{-# LANGUAGE OverloadedStrings #-}
-- The archive connection: one socket at a time, reopened whenever the one before has answered
-- the number of requests its greeting allowed.
module Archive.Conn (Conn, openConn, request, readLineRaw) where

import Control.Exception (IOException, bracketOnError, try)
import Control.Monad (when)
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as BC
import qualified Data.ByteString.Unsafe as BU
import Data.IORef
import Network.Socket
import Network.Socket.ByteString (recv, sendAll)
import System.Exit (die)


data Conn = Conn
  { cHost :: String
  , cPort :: String
  , cSock :: IORef (Maybe Socket)
  , cBuf  :: IORef B.ByteString
  , cLeft :: IORef Int
  }

openConn :: String -> String -> IO Conn
openConn h p = Conn h p <$> newIORef Nothing <*> newIORef B.empty <*> newIORef 0

connectTo :: String -> String -> IO Socket
connectTo host port = do
  let hints = defaultHints { addrSocketType = Stream }
  addrs <- getAddrInfo (Just hints) (Just host) (Just port)
  let try1 [] = die ("cannot reach the archive at " ++ host ++ ":" ++ port)
      try1 (ai : rest) = do
        r <- try (bracketOnError (socket (addrFamily ai) Stream defaultProtocol) close
                    (\s -> connect s (addrAddress ai) >> return s))
        case r of
          Right s -> return s
          Left e -> const (try1 rest) (e :: IOException)
  try1 addrs

-- the socket is fresh for every connection; the greeting says how many requests it answers
ensureConn :: Conn -> IO Socket
ensureConn c = do
  left <- readIORef (cLeft c)
  ms <- readIORef (cSock c)
  case ms of
    Just s | left > 0 -> return s
    _ -> do
      maybe (return ()) close ms
      s <- connectTo (cHost c) (cPort c)
      writeIORef (cSock c) (Just s)
      writeIORef (cBuf c) B.empty
      hello <- readLineRaw c s
      case BC.words hello of
        ["HELLO", _, n] | Just (k, _) <- BC.readInt n -> writeIORef (cLeft c) k
        _ -> die ("unexpected greeting: " ++ BC.unpack hello)
      return s

readLineRaw :: Conn -> Socket -> IO B.ByteString
readLineRaw c s = go
  where
    go = do
      buf <- readIORef (cBuf c)
      case B.elemIndex 10 buf of
        Just i -> do
          writeIORef (cBuf c) (BU.unsafeDrop (i + 1) buf)
          return (BU.unsafeTake i buf)
        Nothing -> do
          chunk <- recv s 262144
          when (B.null chunk) $ die "the archive closed the connection mid-answer"
          writeIORef (cBuf c) (if B.null buf then chunk else B.append buf chunk)
          go

request :: Conn -> B.ByteString -> IO Socket
request c line = do
  s <- ensureConn c
  sendAll s (B.append line "\n")
  modifyIORef' (cLeft c) (subtract 1)
  return s

