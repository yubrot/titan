module Titan.Error
  ( Error(..)
  , UnifyFailReason(..)
  ) where

import Data.Text.Prettyprint.Doc
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
  | CoverageConditionUnsatisfied Instance ClassCon (Fundep Parameter)
  | ConsistencyConditionUnsatisfied Instance Instance ClassCon (Fundep Parameter)
  | NoMatchingInstances [Constraint] Constraint
  | InstanceResolutionExhausted Constraint
  | CannotResolveAmbiguity (Id Type) [Constraint]
  | UselessPattern [Doc ()]
  | NonExhaustivePattern [[Doc ()]]
  deriving (Show, Typeable)

data UnifyFailReason
  = Mismatch
  | OccursCheckFailed
  | SignatureTooGeneral
  deriving (Show, Typeable)

instance Pretty Error where
  pretty = \case
    InternalError cause s ->
      brackets (pretty cause) <+> "Internal error:" <+> pretty s
    ParseError s ->
      "Parse error:" <+> pretty s
    MultipleDeclarationsOf s ->
      "Multiple declarations of" <+> pretty s
    MultipleDefault ->
      "Multiple default is not allowed"
    CannotResolve s ->
      "Cannot resolve" <+> pretty s
    CannotUnifyKind a b reason -> sep
      [ hang 2 $ vsep ["Cannot unify kind", prettyInline 0 a]
      , hang 2 $ vsep ["with kind", prettyInline 0 b]
      , pretty reason
      ]
    CannotUnifyType a b reason -> sep
      [ hang 2 $ vsep ["Cannot unify type", prettyInline 0 a]
      , hang 2 $ vsep ["with type", prettyInline 0 b]
      , pretty reason
      ]
    ArityMismatch expected actual ->
      "Arity mismatch: expected" <+> pretty expected <+> "arguments but got" <+> pretty actual
    MatchFailed ->
      "Cannot match type"
    CyclicClasses classes ->
      hang 2 $ sep $ "Cyclic classes:" : punctuate comma (map pretty classes)
    FundepsAreWeakerThanSuperclasses cls fundep -> sep
      [ hang 2 $ vsep ["Functional dependencies are weaker than superclasses:", prettyInline 0 cls]
      , hang 2 $ vsep ["should have a functional dependency stricter than", prettyInline 0 fundep]
      ]
    OverlappingInstances a b -> sep
      [ hang 2 $ vsep ["Overlapping instances:", prettyInline 0 a]
      , hang 2 $ vsep ["conflicts with", prettyInline 0 b]
      ]
    CoverageConditionUnsatisfied inst cls fundep ->
      hang 2 $ sep ["Coverage condition of" <+> prettyInline 0 fundep <+> "on" <+> prettyInline 0 cls' <+> "is unsatisfied:", prettyInline 0 inst]
     where
      cls' = cls & fundeps .~ [] & superclasses .~ []
    ConsistencyConditionUnsatisfied a b cls fundep -> sep
      [ hang 2 $ vsep ["Consistency condition of" <+> prettyInline 0 fundep <+> "on" <+> prettyInline 0 cls' <+> "is unsatisfied:", prettyInline 0 a]
      , hang 2 $ vsep ["conflicts with", prettyInline 0 b]
      ]
     where
      cls' = cls & fundeps .~ [] & superclasses .~ []
    NoMatchingInstances ps p ->
      group $ "No matching instances for" <+> prettyInline 0 p <++ ps
    InstanceResolutionExhausted p ->
      group $ "Instance resolution exhausted for" <+> prettyInline 0 p
    CannotResolveAmbiguity a ps ->
      group $ "Cannot resolve ambiguity for _" <> prettyInline 0 a <++ ps
    UselessPattern p ->
      hang 2 $ sep ["Useless pattern:", (unAnnotate . hsep) p]
    NonExhaustivePattern ps ->
      hang 2 $ sep $ "Non exhaustive pattern:" : punctuate " |" (map (unAnnotate . hsep) ps)

instance Pretty UnifyFailReason where
  pretty = \case
    Mismatch -> mempty
    OccursCheckFailed -> "Occurs check failed"
    SignatureTooGeneral -> "Signature too general"
