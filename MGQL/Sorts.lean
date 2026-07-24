/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Sorts.lean -- Sort universes T0, T1, T2, T3 and coercion relation

  Paper hierarchy (Section 3):
    T0 = Z | S | B
    T1 = T0 | N<G> | E<G> | N<G,zeta_hat> | E<G,xi_hat>
    tau = T1 | Any | bot | ? | tau1 union tau2 | List tau | <tau>_bot

  Changes from v2:
  - Removed NodeSchema/EdgeSchema id wrappers
  - Moved PropSchema, NodeSchemaFull, EdgeSchemaFull here from Schema.lean
  - ExtSort.nodeRefined/edgeRefined now take List NodeSchemaFull/List EdgeSchemaFull
    directly, matching Paper Notation 3.1: N<G, zeta'> = union_{zeta in zeta'} N<G, zeta>
  - No more id-based indirection; schema content is embedded in the type
-/

namespace MGQL

abbrev GraphSite := String
abbrev Name := String

/-! ## T0: Primitive Scalar Sorts -/

inductive BaseSort where
  | int
  | string
  | bool
  deriving DecidableEq, Repr, BEq

/-! ## Property Schema (Paper Definition 3.2): Phi : A partial-> T0
  Moved here from Schema.lean so that NodeSchemaFull/EdgeSchemaFull
  can be used directly in ExtSort without circular imports. -/

abbrev PropSchema := List (Prod Name BaseSort)

/-! ## Schema Definitions (Paper Definition 3.2)
  Moved here from Schema.lean for the same reason.
  These are the full schema structures used throughout the type system. -/

structure NodeSchemaFull where
  labels     : List Name
  propSchema : PropSchema
  deriving DecidableEq, Repr, BEq

structure EdgeSchemaFull where
  labels     : List Name
  srcSchema  : NodeSchemaFull
  dstSchema  : NodeSchemaFull
  propSchema : PropSchema
  isDirected : Bool := true
  deriving DecidableEq, Repr, BEq

/-! ## T1: Extended Base Sorts
  nodeRefined/edgeRefined take List of full schema structures (Paper Notation 3.1).
  The schema content is directly embedded in the type -- no id indirection. -/

inductive ExtSort where
  | scalar      : BaseSort -> ExtSort
  | node        : GraphSite -> ExtSort
  | edge        : GraphSite -> ExtSort
  | nodeRefined : GraphSite -> List NodeSchemaFull -> ExtSort
  | edgeRefined : GraphSite -> List EdgeSchemaFull -> ExtSort
  deriving DecidableEq, Repr, BEq

/-! ## Nullability (Section 3.4)
  val      = t   (definitely non-null)
  nullable = t?  (possibly null, i.e. t union ?)
  null     = ?   (null-singleton, backward compat tag)
-/

inductive NullTag where
  | val       -- t
  | nullable  -- t?
  | null      -- ? (null-singleton)
  deriving DecidableEq, Repr, BEq

/-! ## Sort Shape (Section 4)
  Added: bot, nullType, emptyFormer -/

inductive SortShape where
  | single       : ExtSort -> SortShape
  | any          : SortShape                            -- Any (top type)
  | bot          : SortShape                            -- bot (bottom type)
  | nullType     : SortShape                            -- ? (the null type)
  | union        : List ExtSort -> SortShape
  | list         : SortShape -> NullTag -> SortShape
  | emptyFormer  : SortShape -> NullTag -> SortShape    -- <tau>_bot
  deriving DecidableEq, Repr, BEq

/-! ## GSort: Full GQL sort = (SortShape, NullTag) -/

structure GSort where
  shape : SortShape
  null  : NullTag
  deriving DecidableEq, Repr, BEq

namespace GSort

/-! ### Non-null sorts (t) -/
def int    : GSort := GSort.mk (.single (.scalar .int)) .val
def string : GSort := GSort.mk (.single (.scalar .string)) .val
def bool   : GSort := GSort.mk (.single (.scalar .bool)) .val

/-! ### Nullable sorts (t?) -/
def intN    : GSort := GSort.mk (.single (.scalar .int)) .nullable
def stringN : GSort := GSort.mk (.single (.scalar .string)) .nullable
def boolN   : GSort := GSort.mk (.single (.scalar .bool)) .nullable

/-! ### The null type ? (Paper Section 4.4, E-Null rule) -/
def nullSort : GSort := GSort.mk .nullType .val

/-! ### The bottom type bot (Paper Section 4) -/
def botSort : GSort := GSort.mk .bot .val

/-! ### Graph-scoped sorts (nullable) -/
def nodeOf (G : GraphSite) : GSort := GSort.mk (.single (.node G)) .nullable
def edgeOf (G : GraphSite) : GSort := GSort.mk (.single (.edge G)) .nullable

/-! ### Schema-refined sorts (nullable, List-based, Notation 3.1)
  Now takes List NodeSchemaFull / List EdgeSchemaFull directly.
  The full schema content is embedded in the type. -/
def nodeRefinedOf (G : GraphSite) (ss : List NodeSchemaFull) : GSort :=
  GSort.mk (.single (.nodeRefined G ss)) .nullable
def edgeRefinedOf (G : GraphSite) (ss : List EdgeSchemaFull) : GSort :=
  GSort.mk (.single (.edgeRefined G ss)) .nullable

/-! ### Empty type former <tau>_bot (Paper Section 4.4)
  <N<G>>_bot sits below every schema-refined node type N<G, zeta>. -/
def nodeEmpty (G : GraphSite) : GSort :=
  GSort.mk (.emptyFormer (.single (.node G)) .nullable) .val
def edgeEmpty (G : GraphSite) : GSort :=
  GSort.mk (.emptyFormer (.single (.edge G)) .nullable) .val

/-- Backward compat aliases -/
def nodeNull (G : GraphSite) : GSort := nodeEmpty G
def edgeNull (G : GraphSite) : GSort := edgeEmpty G

/-! ### List sorts (Section 3.3) -/
def listOf (elem : GSort) : GSort :=
  GSort.mk (.list elem.shape elem.null) .val
def listOfN (elem : GSort) : GSort :=
  GSort.mk (.list elem.shape elem.null) .nullable

/-! ### Any type -/
def any : GSort := GSort.mk .any .val

/-! ### Union sorts for open property access: (Z union S union B)? -/
def anyScalarN    : GSort :=
  GSort.mk (.union [.scalar .int, .scalar .string, .scalar .bool]) .nullable
def anyScalarNull : GSort :=
  GSort.mk (.union [.scalar .int, .scalar .string, .scalar .bool]) .null

/-! ### Sort transformers -/
def toNullable (s : GSort) : GSort := { s with null := .nullable }
def toNull     (s : GSort) : GSort := { s with null := .null }
def toVal      (s : GSort) : GSort := { s with null := .val }

/-! ### Predicate helpers -/
def isNullSingleton (s : GSort) : Bool := s.null == .null
def isNullable (s : GSort) : Bool := s.null == .nullable
def isVal (s : GSort) : Bool := s.null == .val

def isEmptyFormer (s : GSort) : Bool :=
  match s.shape with
  | .emptyFormer _ _ => true
  | _ => false

def isBot (s : GSort) : Bool :=
  match s.shape with
  | .bot => true
  | _ => false

/-! ### List introspection -/
def elemSort? (s : GSort) : Option GSort :=
  match s.shape with
  | .list es en => some (GSort.mk es en)
  | _ => none

def isList (s : GSort) : Bool :=
  match s.shape with
  | .list _ _ => true
  | _ => false

def liftToList (s : GSort) : GSort :=
  GSort.mk (.list s.shape s.null) .val

/-! ### Component Type (Paper Definition 3.1) -/
def componentType (s : GSort) : GSort :=
  match s.shape with
  | .list es en => GSort.mk es en
  | _ => s

/-! ### Extract inner type from emptyFormer -/
def emptyInner? (s : GSort) : Option GSort :=
  match s.shape with
  | .emptyFormer es en => some (GSort.mk es en)
  | _ => none

/-! ### Lift-Preserving Type Update (Paper Definition 4.1) -/
def liftPreservingUpdate (s : GSort) (newInner : GSort) : GSort :=
  match s.shape with
  | .list _ _ => GSort.mk (.list newInner.shape newInner.null) s.null
  | _ => newInner

def hasListWrapper (s : GSort) : Bool :=
  match s.shape with
  | .list _ _ => true
  | _ => false

end GSort

/-! ## Coercion Relations (Appendix A) -/

inductive ExtCoercible : ExtSort -> ExtSort -> Prop where
  | refl (t : ExtSort) : ExtCoercible t t
  | refineNode (G : GraphSite) (ss : List NodeSchemaFull) :
      ExtCoercible (.nodeRefined G ss) (.node G)
  | refineEdge (G : GraphSite) (ss : List EdgeSchemaFull) :
      ExtCoercible (.edgeRefined G ss) (.edge G)

inductive ShapeCoercible : SortShape -> SortShape -> Prop where
  | single (t1 t2 : ExtSort) :
      ExtCoercible t1 t2 -> ShapeCoercible (.single t1) (.single t2)
  | unionMember (ts : List ExtSort) (t : ExtSort) :
      (Exists fun ti => And (List.Mem ti ts) (ExtCoercible ti t)) ->
      ShapeCoercible (.union ts) (.single t)
  | listCov (es1 es2 : SortShape) (en1 en2 : NullTag) :
      ShapeCoercible es1 es2 ->
      ShapeCoercible (.list es1 en1) (.list es2 en2)
  | toAny (s : SortShape) : ShapeCoercible s .any
  | fromBot (s : SortShape) : ShapeCoercible .bot s

def Coercible (t1 t2 : GSort) : Prop := ShapeCoercible t1.shape t2.shape

/-! ## Basic Properties -/

theorem ExtCoercible.rfl' (t : ExtSort) : ExtCoercible t t := .refl t

theorem ShapeCoercible.single_refl (t : ExtSort) :
    ShapeCoercible (.single t) (.single t) :=
  .single t t (.refl t)

/-! ## Sort subsumption -/

inductive NullSubsumes : NullTag -> NullTag -> Prop where
  | refl (n : NullTag) : NullSubsumes n n
  | valToNullable : NullSubsumes .val .nullable
  | nullToNullable : NullSubsumes .null .nullable

def Subsumes (t1 t2 : GSort) : Prop :=
  And (ShapeCoercible t1.shape t2.shape) (NullSubsumes t1.null t2.null)

end MGQL
