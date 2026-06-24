module Main where

import qualified Pudding (someFunc)
import qualified Pudding.Surface.Lexer as Lexer

main :: IO ()
main = do
  putStrLn "Hello, Haskell!"
  Pudding.someFunc
  Lexer.demo
