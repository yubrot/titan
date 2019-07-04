module Titan.Error
  ( Error(..)
  , UnifyFailReason(..)
  ) where

import qualified Data.Text as Text
import Titan.Prelude
import Titan.TT
import Titan.PrettyPrinter

data Error
  = InternalError Text Text
  | ParseError Text
  | MultipleDeclarationsOf Name
  | MultipleDefault
  | CannotResolve Name
  | CannotUnifyKind Kind Kind UnifyFailReason
  | CannotUnifyType Type Type UnifyFailReason
  | ArityMismatch Arity Arity
  | MatchFailed
  | CyclicClasses [Name]
  | FundepsAreWeakerThanSuperclasses ClassCon (Fundep Parameter)
  | OverlappingInstances Instance Instance
  | CoverageConditionUnsatisfied Instance (Fundep Parameter)
  | ConsistencyConditionUnsatisfied Instance Instance (Fundep Parameter)
  | NoMatchingInstances [Constraint] Constraint
  | InstanceResolutionExhausted Constraint
  | CannotResolveAmbiguity (Id Type) [Constraint]
  | UselessPattern Text
  | NonExhaustivePattern [Text]
  deriving (Eq, Ord, Data, Typeable)

data UnifyFailReason
  = Mismatch
  | OccursCheckFailed
  | SignatureTooGeneral
  deriving (Eq, Ord, Data, Typeable)

instance Show Error where
  show = Text.unpack . \case
    InternalError cause s -> "[" <> cause <> "] Internal error: " <> s
    ParseError s -> "Parse error: " <> s
    MultipleDeclarationsOf s -> "Multiple declarations of " <> s
    MultipleDefault -> "Multiple default is not allowed"
    CannotResolve s -> "Cannot resolve " <> s
    CannotUnifyKind a b reason -> "Cannot unify kind " <> pretty a <> " with " <> pretty b <> Text.pack (show reason)
    CannotUnifyType a b reason -> "Cannot unify type " <> pretty a <> " with " <> pretty b <> Text.pack (show reason)
    ArityMismatch expected actual -> "Arity mismatch: expected " <> Text.pack (show expected) <> " arguments but got " <> Text.pack (show actual)
    MatchFailed -> "Cannot match type"
    CyclicClasses classes -> "Cyclic classes: " <> foldr1 (\a b -> a <> ", " <> b) classes
    FundepsAreWeakerThanSuperclasses cls fundep -> "Functional dependencies are weaker than superclasses: " <> pretty cls <> " should have a functional dependency stricter than " <> pretty fundep
    OverlappingInstances a b -> "Overlapping instances: " <> pretty a <> " and " <> pretty b
    CoverageConditionUnsatisfied inst fundep -> "Coverage condition unsatisfied for " <> pretty fundep <> ": " <> pretty inst
    ConsistencyConditionUnsatisfied a b fundep -> "Consistency condition unsatisfied for " <> pretty fundep <> ": " <> pretty a <> " and " <> pretty b
    NoMatchingInstances ps p -> "No matching instances for " <> pretty p <> pretty (PrettyContext ps)
    InstanceResolutionExhausted p -> "Instance resolution exhausted for " <> pretty p
    CannotResolveAmbiguity a ps -> "Cannot resolve ambiguity for _" <> pretty a <> pretty (PrettyContext ps)
    UselessPattern p -> "Useless pattern: " <> p
    NonExhaustivePattern ps -> "Non exhaustive pattern: " <> foldr1 (\a b -> a <> " | " <> b) ps

instance Show UnifyFailReason where
  show = \case
    Mismatch -> ""
    OccursCheckFailed -> ": occurs check failed"
    SignatureTooGeneral -> ": signature too general"
