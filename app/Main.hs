module Main where

import qualified Pudding (someFunc)
import qualified Pudding.Surface.Surface as Surface

main :: IO ()
main = do
  putStrLn "Hello, Haskell!"
  Pudding.someFunc
  Surface.demo
