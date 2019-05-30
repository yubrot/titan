module PatternCheckerTest
  ( spec
  ) where

import Test.Hspec
import Titan.PatternChecker
import Titan.Prelude

(==>) :: HasCallStack => [Row] -> CheckResult -> Expectation
ps ==> r = check ps `shouldBe` r

maybeTC :: [(Name, Arity)]
abcTC :: [(Name, Arity)]
justT, nothingT, aT, bT, cT :: Tag
justP :: Pat -> Pat
nothingP :: Pat
aP :: Pat
bP :: Pat -> Pat
cP :: Pat -> Pat -> Pat
integerP :: Integer -> Pat

maybeTC = [("Just", 1), ("Nothing", 0)]
abcTC = [("A", 0), ("B", 1), ("C", 2)]
justT = TagClosed (maybeTC !! 0) maybeTC
nothingT = TagClosed (maybeTC !! 1) maybeTC
aT = TagClosed (abcTC !! 0) abcTC
bT = TagClosed (abcTC !! 1) abcTC
cT = TagClosed (abcTC !! 2) abcTC
justP p = Constructor justT [p]
nothingP = Constructor nothingT []
aP = Constructor aT []
bP p = Constructor bT [p]
cP p q = Constructor cT [p, q]
integerP n = Constructor (TagLit (LInteger n)) []

spec :: Spec
spec = describe "Titan.PatternChecker" $ do
  it "show" $ do
    show Wildcard
      `shouldBe` "_"
    show nothingP
      `shouldBe` "Nothing"
    show (justP Wildcard)
      `shouldBe` "(Just _)"
    show (justP (justP Wildcard))
      `shouldBe` "(Just (Just _))"
    show (integerP 5)
      `shouldBe` "5"
    show (Or (integerP 5) (integerP 6))
      `shouldBe` "(5 | 6)"
    show (cP nothingP Wildcard)
      `shouldBe` "(C Nothing _)"
    show [Wildcard, Wildcard, Wildcard]
      `shouldBe` "_ _ _"
  it "exhaustiveness" $ do
    [[Wildcard]]
      ==> Complete
    [[Wildcard, Wildcard]]
      ==> Complete
    [[justP Wildcard], [nothingP]]
      ==> Complete
    [[justP Wildcard, nothingP], [Wildcard, Wildcard]]
      ==> Complete
    [[justP Wildcard]]
      ==> NonExhaustive [[nothingP]]
    [[nothingP]]
      ==> NonExhaustive [[justP Wildcard]]
    [[justP (justP Wildcard)]]
      ==> NonExhaustive [[nothingP]]
    [[justP (justP Wildcard)], [nothingP]]
      ==> NonExhaustive [[justP nothingP]]
    [[justP (justP Wildcard)], [Wildcard]]
      ==> Complete
    [[justP Wildcard, nothingP], [nothingP, Wildcard]]
      ==> NonExhaustive [[justP Wildcard, justP Wildcard]]
    [[justP Wildcard, nothingP], [nothingP, Wildcard], [justP Wildcard, justP Wildcard]]
      ==> Complete
    [[justP Wildcard, nothingP], [nothingP, Wildcard], [justP Wildcard, Wildcard]]
      ==> Complete
    [[aP]]
      ==> NonExhaustive [[bP Wildcard], [cP Wildcard Wildcard]]
    [[bP nothingP]]
      ==> NonExhaustive [[aP], [cP Wildcard Wildcard]]
    [[integerP 0]]
      ==> NonExhaustive [[Wildcard]]
    [[integerP 0], [integerP 1], [integerP 2]]
      ==> NonExhaustive [[Wildcard]]
    [[integerP 0], [Wildcard]]
      ==> Complete
    [[Or (justP Wildcard) nothingP]]
      ==> Complete
    [[Or (justP (justP Wildcard)) nothingP]]
      ==> NonExhaustive [[justP nothingP]]
    [[Or (justP (justP Wildcard)) (justP Wildcard)]]
      ==> NonExhaustive [[nothingP]]
    [[justP (Or (justP Wildcard) nothingP)]]
      ==> NonExhaustive [[nothingP]]
  it "useless" $ do
    [[nothingP], [nothingP]]
      ==> Useless [nothingP]
    [[justP Wildcard], [justP Wildcard]]
      ==> Useless [justP Wildcard]
    [[justP (justP Wildcard)], [justP Wildcard], [nothingP]]
      ==> Complete
    [[justP (justP Wildcard)], [nothingP], [justP Wildcard]]
      ==> Complete
    [[justP Wildcard], [justP (justP Wildcard)], [nothingP]]
      ==> Useless [justP (justP Wildcard)]
    [[integerP 0], [integerP 0]]
      ==> Useless [integerP 0]
    [[justP Wildcard, Wildcard], [justP (justP nothingP), Wildcard]]
      ==> Useless [justP (justP nothingP), Wildcard]
    [[justP Wildcard, nothingP], [justP (justP Wildcard), Wildcard], [Wildcard, Wildcard]]
      ==> Complete
    [[justP Wildcard, aP], [nothingP, bP Wildcard], [Wildcard, Wildcard]]
      ==> Complete
    [[justP Wildcard, nothingP], [nothingP, justP Wildcard], [Wildcard, Wildcard]]
      ==> Complete
    [[justP Wildcard, Wildcard], [nothingP, nothingP], [Wildcard, Wildcard]]
      ==> Complete
    [[justP Wildcard, nothingP], [nothingP, Wildcard], [Wildcard, Wildcard]]
      ==> Complete
    [[justP Wildcard, Wildcard], [nothingP, Wildcard], [Wildcard, Wildcard]]
      ==> Useless [Wildcard, Wildcard]
  it "useless with Or-pattern" $ do
    [[Or nothingP nothingP]]
      ==> Useless [nothingP]
    [[justP (Or nothingP nothingP)]]
      ==> Useless [nothingP]
    [[nothingP], [Or (justP Wildcard) nothingP]]
      ==> Useless [nothingP]
    [[Or (integerP 0) (integerP 1), Or (integerP 2) (integerP 3)], [Or (integerP 1) (integerP 2), Or (integerP 3) (integerP 4)], [Wildcard, Wildcard]]
      ==> Complete
    [[Or (integerP 0) (integerP 1), Or (integerP 2) (integerP 3)], [integerP 1, Or (integerP 3) (integerP 4)]]
      ==> Useless [integerP 3]
    [[nothingP], [Or nothingP nothingP]]
      ==> Useless [Or nothingP nothingP]
    [[Or (integerP 0) (integerP 1), Or (integerP 2) (integerP 3)], [Or (integerP 0) (integerP 1), Or (integerP 2) (integerP 3)]]
      ==> Useless [Or (integerP 0) (integerP 1), Or (integerP 2) (integerP 3)]
