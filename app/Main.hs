module Main where

import qualified Pudding (someFunc)

main :: IO ()
main = do
  putStrLn "Hello, Haskell!"
  Pudding.someFunc
