module Pudding.Surface.Surface where

import Prelude

import Pudding.Surface.Lexer hiding (demo)
import qualified Pudding.Surface.Happy as Happy

import qualified Data.Text as T
import Pudding.Core.Types (initTable, GlobalDefn (GlobalDefn), GlobalTerm (GlobalTerm), Globals (globalDefns), globalsFrom, Name (nameText))
import Pudding.Types.Stack (pattern Nil)
import qualified Text.Parsec as P
import qualified Data.Text.IO.Utf8 as TIO
import Control.Monad.Identity (Identity (runIdentity))
import Data.Show.Reshow (reshow)
import qualified Pudding.Surface.Elaborator as Elab
import Pudding.Core.Printer (Style (Ansi), formatCore)
import GHC.IO (catch, evaluate)
import GHC.Exception (SomeException)
import qualified Pudding.Core.Unify as U
import qualified Pudding.Core.Eval as E
import Control.DeepSeq (force)
import qualified Pudding.Surface.Delaborator as D
import System.Environment (getArgs)
import qualified Data.Map.Strict as Map
import Data.Foldable (for_)

demo :: IO ()
demo = do
  getArgs >>= \case
    [] -> demoREPL
    [filename] -> demoFile filename
    _ -> error "Unrecognized arguments"

-- cabal run -- pudding test/surface.pudding
demoFile :: String -> IO ()
demoFile filename = do
  contents <- TIO.readFile filename
  let prelexed = runIdentity (P.runPT (prelex <* P.eof) WHITESPACE filename contents)
  catch
    case prelexed of
      Left err -> TIO.putStrLn $ T.pack $ show err
      Right r -> do
        -- TIO.putStrLn $ reshow r
        let tokenized = runIdentity (P.runPT (tokenize <* P.eof) Nothing filename r)
        case tokenized of
          Left err -> TIO.putStrLn $ T.pack $ show err
          Right ts -> do
            -- TIO.putStrLn $ reshow ts
            let parsed = Happy.parseDecls ts
            case parsed of
              Left err -> do
                TIO.putStrLn $ T.pack $ "Error at " <> err
              Right decls -> do
                TIO.putStrLn $ reshow decls
                tbl <- initTable
                (modul, ()) <- Elab.runElabFull tbl (Elab.elaborateModule decls)
                TIO.putStrLn $ reshow $ Map.keys modul
                for_ (Map.toList (globalDefns (globalsFrom modul))) \(name, thingy) -> case thingy of
                  GlobalDefn _ (GlobalTerm ty _) (GlobalTerm tm _) -> do
                    -- TIO.putStrLn $ nameText name <> " : " <> formatCore Ansi ty
                    -- TIO.putStrLn $ nameText name <> " := " <> formatCore Ansi tm
                    TIO.putStrLn $ nameText name <> " : " <> do
                      D.format D.Ansi $ D.printCST (D.runDelab $ D.delab tm) (D.PS 0 0)
                    TIO.putStrLn $ nameText name <> " := " <> do
                      D.format D.Ansi $ D.printCST (D.runDelab $ D.delab ty) (D.PS 0 0)
    \(err :: SomeException) -> TIO.putStrLn $ T.pack $ show err

demoREPL :: IO ()
demoREPL = do
  TIO.putStrLn ""
  line <- TIO.getLine
  let prelexed = runIdentity (P.runPT (prelex <* P.eof) WHITESPACE "<input>" line)
  catch
    case prelexed of
      Left err -> TIO.putStrLn $ T.pack $ show err
      Right r -> do
        TIO.putStrLn $ reshow r
        let tokenized = runIdentity (P.runPT (tokenize <* P.eof) Nothing "<input>" r)
        case tokenized of
          Left err -> TIO.putStrLn $ T.pack $ show err
          Right ts -> do
            TIO.putStrLn $ reshow ts
            let parsed = (Happy.parseExpr ts, Happy.parseDecl ts)
            case parsed of
              (Left err1, Left err2) -> do
                TIO.putStrLn $ T.pack $ "Error at " <> err1
                TIO.putStrLn $ T.pack $ "Error at " <> err2
              (Right cst, _) -> do
                TIO.putStrLn $ reshow cst
                tbl <- initTable
                tm <- Elab.runElabScoped tbl (Elab.elab Nothing cst)
                TIO.putStrLn $ formatCore Ansi tm
                tyE <- evaluate $ force $ U.validate Nil tm
                let tyT = E.quote Nil tyE
                TIO.putStrLn $ formatCore Ansi tyT
                TIO.putStrLn $ D.format D.Ansi $ D.printCST (D.runDelab $ D.delab tm) (D.PS 0 0)
                TIO.putStrLn $ D.format D.Ansi $ D.printCST (D.runDelab $ D.delab tyT) (D.PS 0 0)
              (_, Right decl) -> do
                TIO.putStrLn $ reshow decl
    \(err :: SomeException) -> TIO.putStrLn $ T.pack $ show err
  demo

