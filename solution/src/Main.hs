{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
-- proofcheck, reference version. Reads every job off the proof archive, checks its proof forward
-- and prints one verdict line per job.
--
-- How it stays fast: clauses live in one flat Int32 arena, propagation is two watched literals,
-- and the top-level assignment (what the formula forces with nothing assumed) is kept from line to
-- line instead of being worked out again for every lemma. A lemma is checked by assuming its
-- negation on top of that, propagating, and taking the assumptions back. RAT candidates come off
-- per-literal occurrence lists, and deletions find their clause through a hash of its literal set.
--
-- The one place the kept assignment can go stale is a deletion: if the deleted clause is the
-- reason some literal is true at the top level, the formula may no longer force that literal
-- (or anything that followed from it). Then the whole top-level assignment is rebuilt from the
-- unit clauses still in the formula. A deleted clause that is nobody's reason cannot change what
-- the rest forces, so everything else is left alone.
module Main (main) where

import Control.Monad
import Data.Array.Base (unsafeRead, unsafeWrite)
import Data.Array.IO
import Data.Bits
import Data.Char (isSpace)
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as BC
import Data.Int
import qualified Data.IntMap.Strict as IM
import Data.IORef
import Archive.Conn
import System.Environment (lookupEnv)
import System.Exit
import System.IO

------------------------------------------------------------------------------------------------
-- growable Int32 vectors

data Vec = Vec !(IORef (IOUArray Int Int32)) !(IORef Int)

newVec :: Int -> IO Vec
newVec n = do
  a <- newArray (0, max 1 n - 1) 0
  Vec <$> newIORef a <*> newIORef 0

pushVec :: Vec -> Int32 -> IO ()
pushVec (Vec ra rn) !x = do
  a <- readIORef ra
  n <- readIORef rn
  (_, hi) <- getBounds a
  a' <- if n <= hi then return a else do
          b <- newArray (0, 2 * (hi + 1) - 1) 0
          forM_ [0 .. hi] $ \i -> unsafeRead a i >>= unsafeWrite b i
          writeIORef ra b
          return b
  unsafeWrite a' n x
  writeIORef rn (n + 1)

freezeVec :: Vec -> IO (IOUArray Int Int32, Int)
freezeVec (Vec ra rn) = (,) <$> readIORef ra <*> readIORef rn

------------------------------------------------------------------------------------------------
-- parsing

-- one clause line into the arena; returns (is deletion, length)
parseInto :: Vec -> B.ByteString -> IO (Bool, Int)
parseInto arena ln0 = do
  let ln = BC.dropWhile isSpace ln0
      (isDel, rest) = case BC.uncons ln of
        Just ('d', r) | B.null r || isSpace (BC.head r) -> (True, r)
        _ -> (False, ln)
  n <- go rest 0
  return (isDel, n)
  where
    go !s !k = case BC.readInt (BC.dropWhile isSpace s) of
      Nothing -> return k
      Just (0, _) -> return k
      Just (x, r) -> pushVec arena (fromIntegral x) >> go r (k + 1)

------------------------------------------------------------------------------------------------
-- the checker

data St = St
  { lits     :: !(IOUArray Int Int32)   -- arena
  , cStart   :: !(IOUArray Int Int32)
  , cLen     :: !(IOUArray Int Int32)
  , active   :: !(IOUArray Int Bool)
  , val      :: !(IOUArray Int Int8)    -- per literal code
  , reason   :: !(IOUArray Int Int32)   -- per variable
  , trail    :: !(IOUArray Int Int32)   -- literal codes
  , trailLen :: !(IORef Int)
  , qhead    :: !(IORef Int)
  , wHead    :: !(IOUArray Int Int32)   -- per literal code, watch node
  , wNext    :: !(IOUArray Int Int32)   -- per watch node (2c, 2c+1)
  , oHead    :: !(IOUArray Int Int32)   -- per literal code, arena position
  , oNext    :: !(IOUArray Int Int32)   -- per arena position
  , oClause  :: !(IOUArray Int Int32)   -- per arena position
  , stamp    :: !(IOUArray Int Int32)   -- per literal code
  , stampN   :: !(IORef Int32)
  , units    :: !Vec                    -- unit clause ids ever activated
  , nEmpty   :: !(IORef Int)
  , topConf  :: !(IORef Bool)
  , byHash   :: !(IORef (IM.IntMap [Int]))
  }

code :: Int32 -> Int
code l = if l > 0 then 2 * fromIntegral l else 2 * fromIntegral (negate l) + 1
{-# INLINE code #-}

neg :: Int -> Int
neg c = c `xor` 1
{-# INLINE neg #-}

litAt :: St -> Int -> IO Int
litAt st i = code <$> unsafeRead (lits st) i
{-# INLINE litAt #-}

setTrue :: St -> Int -> Int32 -> IO ()
setTrue st c r = do
  unsafeWrite (val st) c 1
  unsafeWrite (val st) (neg c) (-1)
  unsafeWrite (reason st) (c `shiftR` 1) r
  n <- readIORef (trailLen st)
  unsafeWrite (trail st) n (fromIntegral c)
  writeIORef (trailLen st) (n + 1)

backtrack :: St -> Int -> IO ()
backtrack st to = do
  n <- readIORef (trailLen st)
  let go i | i < to = return ()
           | otherwise = do
               c <- fromIntegral <$> unsafeRead (trail st) i
               unsafeWrite (val st) c 0
               unsafeWrite (val st) (neg c) 0
               unsafeWrite (reason st) (c `shiftR` 1) (-1)
               go (i - 1)
  go (n - 1)
  writeIORef (trailLen st) to
  writeIORef (qhead st) to

-- returns True on conflict
propagate :: St -> IO Bool
propagate st = loop
  where
    loop = do
      q <- readIORef (qhead st)
      n <- readIORef (trailLen st)
      if q >= n then return False else do
        writeIORef (qhead st) (q + 1)
        t <- fromIntegral <$> unsafeRead (trail st) q
        let f = neg t
        h <- unsafeRead (wHead st) f
        conf <- walk f (-1) h
        if conf then return True else loop
    walk :: Int -> Int32 -> Int32 -> IO Bool
    walk !f !prev !node
      | node < 0 = return False
      | otherwise = do
          let ni = fromIntegral node
              c = ni `shiftR` 1
          nxt <- unsafeRead (wNext st) ni
          act <- unsafeRead (active st) c
          if not act then unlink f prev nxt >> walk f prev nxt else do
            s <- fromIntegral <$> unsafeRead (cStart st) c
            len <- fromIntegral <$> unsafeRead (cLen st) c
            l0 <- unsafeRead (lits st) s
            when (code l0 == f) $ do
              l1 <- unsafeRead (lits st) (s + 1)
              unsafeWrite (lits st) s l1
              unsafeWrite (lits st) (s + 1) l0
            other <- litAt st s
            vo <- unsafeRead (val st) other
            if vo == 1 then walk f node nxt else do
              k <- findNew s (s + 2) (s + len)
              if k >= 0 then do
                lk <- unsafeRead (lits st) k
                lf <- unsafeRead (lits st) (s + 1)
                unsafeWrite (lits st) (s + 1) lk
                unsafeWrite (lits st) k lf
                unlink f prev nxt
                let nc = code lk
                hd <- unsafeRead (wHead st) nc
                unsafeWrite (wNext st) ni hd
                unsafeWrite (wHead st) nc node
                walk f prev nxt
              else if vo == -1 then return True
              else do
                setTrue st other (fromIntegral c)
                walk f node nxt
    findNew !_ !k !e
      | k >= e = return (-1)
      | otherwise = do
          lc <- litAt st k
          v <- unsafeRead (val st) lc
          if v /= -1 then return k else findNew 0 (k + 1) e
    unlink f prev nxt =
      if prev < 0 then unsafeWrite (wHead st) f nxt
                  else unsafeWrite (wNext st) (fromIntegral prev) nxt

-- make literal code c false, as part of an assumption; True if it was already true (conflict)
assumeFalse :: St -> Int -> IO Bool
assumeFalse st c = do
  v <- unsafeRead (val st) c
  if v == 1 then return True
  else if v == -1 then return False
  else setTrue st (neg c) (-1) >> return False

clauseHash :: St -> Int -> Int -> IO Int
clauseHash st s len = go s 0
  where
    go !i !h | i >= s + len = return h
             | otherwise = do
                 x <- fromIntegral <$> unsafeRead (lits st) i
                 go (i + 1) (h + mix x)
    mix :: Int -> Int
    mix x = let y = (x * (-7046029254386353131)) `xor` (x `shiftR` 7) in y * (-4658895280553007687) `xor` (y `shiftR` 29)

-- put an active clause (length >= 2) on two watches, under the current top-level assignment
attach :: St -> Int -> IO ()
attach st c = do
  s <- fromIntegral <$> unsafeRead (cStart st) c
  len <- fromIntegral <$> unsafeRead (cLen st) c
  -- move up to two non-false literals to the front
  let pick !pos !k !found
        | k >= s + len || found >= 2 = return found
        | otherwise = do
            lc <- litAt st k
            v <- unsafeRead (val st) lc
            if v /= -1 then do
              a <- unsafeRead (lits st) pos
              b <- unsafeRead (lits st) k
              unsafeWrite (lits st) pos b
              unsafeWrite (lits st) k a
              pick (pos + 1) (k + 1) (found + 1)
            else pick pos (k + 1) found
  found <- pick s s (0 :: Int)
  forM_ [0, 1] $ \w -> do
    lc <- litAt st (s + w)
    hd <- unsafeRead (wHead st) lc
    unsafeWrite (wNext st) (2 * c + w) hd
    unsafeWrite (wHead st) lc (fromIntegral (2 * c + w))
  when (found == 0) $ writeIORef (topConf st) True
  when (found == 1) $ do
    lc <- litAt st s
    v <- unsafeRead (val st) lc
    when (v == 0) $ do
      setTrue st lc (fromIntegral c)
      conf <- propagate st
      when conf $ writeIORef (topConf st) True

-- a clause joins the formula
activate :: St -> Int -> IO ()
activate st c = do
  unsafeWrite (active st) c True
  s <- fromIntegral <$> unsafeRead (cStart st) c
  len <- fromIntegral <$> unsafeRead (cLen st) c
  h <- clauseHash st s len
  modifyIORef' (byHash st) (IM.insertWith (++) h [c])
  forM_ [s .. s + len - 1] $ \i -> do
    lc <- litAt st i
    hd <- unsafeRead (oHead st) lc
    unsafeWrite (oNext st) i hd
    unsafeWrite (oHead st) lc (fromIntegral i)
  tc <- readIORef (topConf st)
  case len of
    0 -> modifyIORef' (nEmpty st) (+ 1) >> writeIORef (topConf st) True
    1 -> do
      pushVec (units st) (fromIntegral c)
      unless tc $ do
        lc <- litAt st s
        v <- unsafeRead (val st) lc
        if v == -1 then writeIORef (topConf st) True
        else when (v == 0) $ do
          setTrue st lc (fromIntegral c)
          conf <- propagate st
          when conf $ writeIORef (topConf st) True
    _ -> if tc then attachBare st c else attach st c

-- watches without regard to the assignment (only while the top level is already in conflict;
-- the next rebuild starts from an empty assignment, where any two literals are fine)
attachBare :: St -> Int -> IO ()
attachBare st c = forM_ [0, 1] $ \w -> do
  s <- fromIntegral <$> unsafeRead (cStart st) c
  lc <- litAt st (s + w)
  hd <- unsafeRead (wHead st) lc
  unsafeWrite (wNext st) (2 * c + w) hd
  unsafeWrite (wHead st) lc (fromIntegral (2 * c + w))

-- rebuild the top-level assignment from nothing
rebuild :: St -> IO ()
rebuild st = do
  backtrack st 0
  ne <- readIORef (nEmpty st)
  writeIORef (topConf st) (ne > 0)
  (ua, un) <- freezeVec (units st)
  let go i | i >= un = return ()
           | otherwise = do
               c <- fromIntegral <$> unsafeRead ua i
               act <- unsafeRead (active st) c
               when act $ do
                 s <- fromIntegral <$> unsafeRead (cStart st) c
                 lc <- litAt st s
                 v <- unsafeRead (val st) lc
                 if v == -1 then writeIORef (topConf st) True
                 else when (v == 0) $ setTrue st lc (fromIntegral c)
               go (i + 1)
  go 0
  conf <- propagate st
  when conf $ writeIORef (topConf st) True

-- a deletion line: find one active copy and remove it
deleteLike :: St -> Int -> IO ()
deleteLike st d = do
  s <- fromIntegral <$> unsafeRead (cStart st) d
  len <- fromIntegral <$> unsafeRead (cLen st) d
  h <- clauseHash st s len
  m <- readIORef (byHash st)
  let cands = IM.findWithDefault [] h m
  sn <- (+ 1) <$> readIORef (stampN st)
  writeIORef (stampN st) sn
  forM_ [s .. s + len - 1] $ \i -> litAt st i >>= \lc -> unsafeWrite (stamp st) lc sn
  let same c = do
        s' <- fromIntegral <$> unsafeRead (cStart st) c
        len' <- fromIntegral <$> unsafeRead (cLen st) c
        if len' /= len then return False else
          allM [s' .. s' + len' - 1] $ \i -> litAt st i >>= \lc -> (== sn) <$> unsafeRead (stamp st) lc
  hit <- findM same cands
  case hit of
    Nothing -> return ()
    Just c -> do
      unsafeWrite (active st) c False
      modifyIORef' (byHash st) (IM.update (\xs -> let ys = filter (/= c) xs in if null ys then Nothing else Just ys) h)
      when (len == 0) $ modifyIORef' (nEmpty st) (subtract 1)
      tc <- readIORef (topConf st)
      isReason <- anyM [s .. s + len - 1] $ \i -> do
        lc <- litAt st i
        v <- unsafeRead (val st) lc
        if v /= 1 then return False else (== fromIntegral c) <$> unsafeRead (reason st) (lc `shiftR` 1)
      when (tc || isReason) $ rebuild st

allM :: [a] -> (a -> IO Bool) -> IO Bool
allM [] _ = return True
allM (x : xs) f = f x >>= \b -> if b then allM xs f else return False

anyM :: [a] -> (a -> IO Bool) -> IO Bool
anyM [] _ = return False
anyM (x : xs) f = f x >>= \b -> if b then return True else anyM xs f

findM :: (a -> IO Bool) -> [a] -> IO (Maybe a)
findM _ [] = return Nothing
findM f (x : xs) = f x >>= \b -> if b then return (Just x) else findM f xs

-- is lemma c (not yet active) RUP, or else RAT on its first literal?
valid :: St -> Int -> IO Bool
valid st c = do
  tc <- readIORef (topConf st)
  if tc then return True else do
    s <- fromIntegral <$> unsafeRead (cStart st) c
    len <- fromIntegral <$> unsafeRead (cLen st) c
    base <- readIORef (trailLen st)
    hit <- anyM [s .. s + len - 1] $ \i -> litAt st i >>= assumeFalse st
    conf <- if hit then return True else propagate st
    if conf then backtrack st base >> return True
    else if len == 0 then backtrack st base >> return False
    else do
      -- the negation of C is assumed and propagated; each resolution candidate adds its own
      -- literals on top of that and is taken back again
      p <- litAt st s
      mid <- readIORef (trailLen st)
      let ratOn q = do
            let nq = neg q
            h0 <- unsafeRead (oHead st) nq
            let walk !prev !pos
                  | pos < 0 = return True
                  | otherwise = do
                      let pi' = fromIntegral pos
                      nxt <- unsafeRead (oNext st) pi'
                      d <- fromIntegral <$> unsafeRead (oClause st) pi'
                      act <- unsafeRead (active st) d
                      if not act then do
                        if prev < 0 then unsafeWrite (oHead st) nq nxt else unsafeWrite (oNext st) (fromIntegral prev) nxt
                        walk prev nxt
                      else do
                        ds <- fromIntegral <$> unsafeRead (cStart st) d
                        dl <- fromIntegral <$> unsafeRead (cLen st) d
                        hit2 <- anyM [ds .. ds + dl - 1] $ \i -> do
                          lc <- litAt st i
                          if lc == nq then return False else assumeFalse st lc
                        conf2 <- if hit2 then return True else propagate st
                        backtrack st mid
                        if conf2 then walk pos nxt else return False
            walk (-1) h0
      ok <- ratOn p
      backtrack st base
      return ok

------------------------------------------------------------------------------------------------

checkJob :: Vec -> Vec -> Vec -> Int -> IO (Maybe Int)
checkJob arenaV startsV opsV nOrig = do
  (arena, nLits) <- freezeVec arenaV
  (starts, nCl) <- freezeVec startsV
  (ops, nOps) <- freezeVec opsV
  -- lengths from starts
  lenA <- newArray (0, max 1 nCl - 1) 0 :: IO (IOUArray Int Int32)
  forM_ [0 .. nCl - 1] $ \i -> do
    a <- unsafeRead starts i
    b <- if i + 1 < nCl then unsafeRead starts (i + 1) else return (fromIntegral nLits)
    unsafeWrite lenA i (b - a)
  maxV <- foldM (\m i -> max m . abs <$> unsafeRead arena i) 0 [0 .. nLits - 1]
  let nCodes = 2 * fromIntegral maxV + 2
  oCl <- newArray (0, max 1 nLits - 1) 0
  forM_ [0 .. nCl - 1] $ \c -> do
    a <- fromIntegral <$> unsafeRead starts c
    l <- fromIntegral <$> unsafeRead lenA c
    forM_ [a .. a + l - 1] $ \i -> unsafeWrite oCl i (fromIntegral c)
  st <- St arena starts lenA
          <$> newArray (0, max 1 nCl - 1) False
          <*> newArray (0, nCodes - 1) 0
          <*> newArray (0, nCodes `div` 2) (-1)
          <*> newArray (0, nCodes `div` 2) 0
          <*> newIORef 0 <*> newIORef 0
          <*> newArray (0, nCodes - 1) (-1)
          <*> newArray (0, 2 * max 1 nCl - 1) (-1)
          <*> newArray (0, nCodes - 1) (-1)
          <*> newArray (0, max 1 nLits - 1) (-1)
          <*> pure oCl
          <*> newArray (0, nCodes - 1) 0
          <*> newIORef 0
          <*> newVec 64
          <*> newIORef 0
          <*> newIORef False
          <*> newIORef IM.empty
  forM_ [0 .. nOrig - 1] $ activate st
  let go i | i >= nOps = return Nothing
           | otherwise = do
               o <- fromIntegral <$> unsafeRead ops i
               if o < 0 then deleteLike st (negate o - 1) >> go (i + 1)
               else do
                 ok <- valid st o
                 if ok then activate st o >> go (i + 1) else return (Just (i + 1))
  go 0

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  host <- maybe "127.0.0.1" id <$> lookupEnv "PROOFS_HOST"
  port <- maybe "7700" id <$> lookupEnv "PROOFS_PORT"
  conn <- openConn host port
  s0 <- request conn "JOBS"
  hdr <- readLineRaw conn s0
  n <- case BC.words hdr of
    ["JOBS", k] | Just (x, _) <- BC.readInt k -> return x
    _ -> die ("unexpected answer to JOBS: " ++ BC.unpack hdr)
  names <- replicateM n (readLineRaw conn s0)
  forM_ names $ \name -> do
    arena <- newVec 4096
    starts <- newVec 1024
    ops <- newVec 1024
    nClauses <- newIORef (0 :: Int)
    let fetch part onLine = loop ("start" :: B.ByteString)
          where
            loop tok = do
              s <- request conn (B.intercalate " " ["READ", name, part, tok])
              h <- readLineRaw conn s
              case BC.words h of
                ["PAGE", m, nxt] | Just (k, _) <- BC.readInt m -> do
                  replicateM_ k (readLineRaw conn s >>= onLine)
                  unless (nxt == "end") (loop nxt)
                _ -> die ("unexpected answer to READ: " ++ BC.unpack h)
        newClause ln = do
          (_, nl) <- freezeVec arena
          pushVec starts (fromIntegral nl)
          modifyIORef' nClauses (+ 1)
          parseInto arena ln
    fetch "cnf" $ \ln -> case BC.uncons ln of
      Just ('p', _) -> return ()
      Just ('c', _) -> return ()
      Nothing -> return ()
      _ -> void (newClause ln)
    nOrig <- readIORef nClauses
    fetch "proof" $ \ln -> unless (B.null (BC.dropWhile isSpace ln)) $ do
      c <- readIORef nClauses
      (isDel, _) <- newClause ln
      pushVec ops (if isDel then negate (fromIntegral c) - 1 else fromIntegral c)
    r <- checkJob arena starts ops nOrig
    BC.putStrLn $ case r of
      Nothing -> B.concat [name, " OK"]
      Just k -> B.concat [name, " FAIL ", BC.pack (show k)]
