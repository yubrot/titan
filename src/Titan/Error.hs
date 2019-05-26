module Titan.Error
  ( Error(..)
  , UnifyFailReason(..)
  ) where

import Titan.Prelude
import Titan.TT
import Titan.PrettyPrinter

data Error
  = InternalError String String
  | ParseError String
  | MultipleDeclarationsOf Name
  | MultipleDefault
  | CannotResolve Name
  | CannotUnifyKind Kind Kind UnifyFailReason
  | CannotUnifyType Type Type UnifyFailReason
  | MatchFailed
  | CyclicClasses [Name]
  | OverlappingInstances Instance Instance
  | NoMatchingInstances [Constraint] Constraint
  | CannotResolveAmbiguity Name [Constraint]
  deriving (Eq, Ord, Data, Typeable)

data UnifyFailReason
  = Mismatch
  | OccursCheckFailed
  | SignatureTooGeneral
  deriving (Eq, Ord, Data, Typeable)

instance Show Error where
  show = \case
    InternalError cause s -> "[" ++ cause ++ "] Internal error: " ++ s
    ParseError s -> "Parse error: " ++ s
    MultipleDeclarationsOf s -> "Multiple declarations of " ++ s
    MultipleDefault -> "Multiple default is not allowed"
    CannotResolve s -> "Cannot resolve " ++ s
    CannotUnifyKind a b reason -> "Cannot unify kind " ++ pprint a ++ " with " ++ pprint b ++ show reason
    CannotUnifyType a b reason -> "Cannot unify type " ++ pprint a ++ " with " ++ pprint b ++ show reason
    MatchFailed -> "Cannot match type"
    CyclicClasses classes -> "Cyclic classes: " ++ foldr1 (\a b -> a ++ ", " ++ b) classes
    OverlappingInstances a b -> "Overlapping instances: " ++ pprint a ++ " and " ++ pprint b
    NoMatchingInstances ps p -> "No matching instances for " ++ pprint p ++ pprint (PrettyContext ps)
    CannotResolveAmbiguity a ps -> "Cannot resolve ambiguity for " ++ a ++ pprint (PrettyContext ps)

instance Show UnifyFailReason where
  show = \case
    Mismatch -> ""
    OccursCheckFailed -> ": occurs check failed"
    SignatureTooGeneral -> ": signature too general"
