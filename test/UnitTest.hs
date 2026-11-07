{-# OPTIONS_GHC -Wno-type-defaults #-}
module UnitTest where

import Testing
import Pudding.Types.Monads.Cont1T
import Pudding.Core.Types (Stack, pattern (:>), pattern Nil)
import Control.Monad.Trans.Class (MonadTrans(lift))
import Data.Foldable (fold)
import Data.Function ((&))
import Data.Functor ((<&>))
import Control.Monad.Reader.Class (MonadReader(local))

type Cont1R = Cont1T String ((->) (Stack String))

into :: (Stack String -> Stack String) -> Cont1R ()
into = localizeCont
snoc :: String -> Cont1R ()
snoc v = into (:> v)

run :: Cont1R t -> (Stack String -> t -> String) -> String
run act cont = runCont1pT act (flip cont) Nil

willBe :: String -> Cont1R String -> String -> Test r ()
willBe val act msg =
  let computed = run act (const id) in
  expect (val == computed) $
    "Expected " <> msg <> " to be " <> show val <> " not " <> show computed

unitTests :: TestSuite
unitTests = TestSuite "UnitTests" do
  testCase "Cont1T" do
    "simplest test" & willBe "01" do
      snoc "0"
      lift \items -> fold items <> "1"
    "double snoc" & willBe "012" do
      snoc "0"
      snoc "1"
      lift \items -> fold items <> "2"
    "associativity test" & willBe "012" do
      snoc "0" *> snoc "1"
      lift \items -> fold items <> "2"
    "full associativity test" & willBe "012345" do
      (snoc "0" *> snoc "1") <* (snoc "2" <* snoc "3")
      snoc "4"
      lift \items -> fold items <> "5"
    "interleaving test" & willBe "->0101234" do
      snoc "0" *> snoc "1"
      onResult \r _ -> "-" <> r
      x <- lift id -- should be "0" "1"
      snoc "2" <* snoc "3"
      onResult \r _ -> ">" <> r
      lift \items -> fold x <> fold items <> "4"
    "awa" & willBe "az" do
      adaptOnResult \c -> local (:> "a") do
        c <&> (, \r l -> fold l <> r)
      lift \items -> fold items <> "z"
    pure ()

