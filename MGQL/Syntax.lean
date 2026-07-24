/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Syntax.lean -- Core GQL fragment abstract syntax

  Reference: Paper Figure 2

  Changes from v2:
  - Added patternLeadVar (Paper Section 5.2: lead(P))
  - Added Quantifier.lo / Quantifier.hi (Paper Section 5.2: quantifier bounds)
-/
import MGQL.Values

namespace MGQL

/-! ## Operators -/

inductive ArithOp where
  | add | sub | mul | div
  deriving DecidableEq, Repr

inductive RelOp where
  | eq | neq | lt | le | gt | ge
  deriving DecidableEq, Repr

/-! ## Label Expressions (Paper Fig 2: l ::= _l | l & _l | l | _l | !l) -/

inductive LabelExpr where
  | atom     : Name -> LabelExpr
  | wildcard : LabelExpr
  | neg      : LabelExpr -> LabelExpr
  | conj     : LabelExpr -> LabelExpr -> LabelExpr
  | disj     : LabelExpr -> LabelExpr -> LabelExpr
  deriving Repr

/-! ## Literals -/

inductive Literal where
  | int    : Int -> Literal
  | string : String -> Literal
  | bool   : Bool -> Literal
  deriving DecidableEq, Repr

/-! ## Aggregation Qualifier (Paper Fig 2, ISO SS20.9) -/

inductive AggQualifier where
  | default
  | distinct
  | all
  deriving DecidableEq, Repr

/-! ## Aggregation Atoms -/

inductive AggOp where
  | count | sum | max | min
  deriving DecidableEq, Repr

/-! ## Value Expressions (Paper Fig 2: theta) -/

/-! Expressions and predicates are mutually inductive (Paper Fig 2:
    `e ::= ... | phi` embeds predicates as boolean value expressions, and
    predicate atoms take expressions as operands). -/
mutual

inductive Expr where
  | const      : Literal -> Expr
  | null       : Expr
  | var        : Name -> Expr
  | propAccess : Name -> Name -> Expr
  | arithOp    : ArithOp -> Expr -> Expr -> Expr
  | agg        : AggOp -> AggQualifier -> Expr -> Expr
  | pred       : Pred -> Expr

-- ## Predicates (Paper Fig 2: phi)
inductive Pred where
  | true   : Pred
  | false  : Pred
  | relOp  : RelOp -> Expr -> Expr -> Pred
  | not    : Pred -> Pred
  | and    : Pred -> Pred -> Pred
  | or     : Pred -> Pred -> Pred
  | isNull : Expr -> Pred

end

deriving instance Repr for Expr
deriving instance Repr for Pred

/-- Induction over `Expr` treating embedded predicates as opaque atoms.
    The `induction` tactic does not support mutual inductives directly;
    this single-motive eliminator (second motive trivially `True`) restores
    it for the common case where the predicate payload needs no inductive
    hypothesis. -/
def Expr.inductionOpaque {motive : Expr -> Prop}
    (const : ∀ l, motive (.const l))
    (null : motive .null)
    (var : ∀ x, motive (.var x))
    (propAccess : ∀ x k, motive (.propAccess x k))
    (arithOp : ∀ op e1 e2, motive e1 -> motive e2 -> motive (.arithOp op e1 e2))
    (agg : ∀ op qual e, motive e -> motive (.agg op qual e))
    (pred : ∀ φ, motive (.pred φ)) :
    ∀ e, motive e :=
  fun e =>
    Expr.rec (motive_1 := motive) (motive_2 := fun _ => True)
      const null var propAccess arithOp agg (fun φ _ => pred φ)
      trivial trivial
      (fun _ _ _ _ _ => trivial)
      (fun _ _ => trivial)
      (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial)
      (fun _ _ => trivial)
      e

/-! ## Property Map Constraints (Paper Fig 2: _M ::= x:c)
  Changed: val is Literal (constant), not Expr. -/

structure PropConstraint where
  key : Name
  val : Literal
  deriving Repr

/-! ## Quantifiers (Paper Fig 2: K) -/

inductive Quantifier where
  | single
  | star
  | plus
  | question
  | exact    : Nat -> Quantifier
  | range    : Nat -> Nat -> Quantifier
  deriving Repr

/-! ## Node and Edge Atoms -/

structure NodeAtom where
  var    : Name
  labels : Option LabelExpr := none
  props  : List PropConstraint := []
  deriving Repr

structure EdgeAtom where
  var        : Name
  labels     : Option LabelExpr := none
  props      : List PropConstraint := []
  quantifier : Quantifier := .single
  deriving Repr

/-! ## Directions (Paper Figure 2: D)
  7 edge direction patterns per ISO SS16.9:
    right             = ->E->   (right-directed)
    left              = <-E<-   (left-directed)
    anyDirected       = ->E<-   (any directed)
    undirected        = ~E~     (undirected only)
    rightOrUndirected = ->E~    (right-directed or undirected)
    leftOrUndirected  = <-E~    (left-directed or undirected)
    any               = any dir (any direction)
-/

inductive Direction where
  | right
  | left
  | anyDirected
  | undirected
  | rightOrUndirected
  | leftOrUndirected
  | any
  deriving DecidableEq, Repr

/-! ## Patterns (Paper Fig 2: P, p)
  Extended: Pattern.step for general P D^K N composition (Paper Pat-Step). -/

inductive Pattern where
  | node        : NodeAtom -> Pattern
  | edge        : NodeAtom -> EdgeAtom -> Direction -> NodeAtom -> Pattern
  | step        : Pattern -> EdgeAtom -> Direction -> NodeAtom -> Pattern   -- Pat-Step: P D^K N
  | grouped     : Pattern -> Pattern
  | quantified  : Pattern -> Quantifier -> Pattern
  | patternList : Pattern -> Pattern -> Pattern
  deriving Repr

/-! ## Quantifier helpers -/

/-- Is this quantifier a group-reference quantifier (induces List lifting)?
  True for *, +, {i}, {i,j}. False for single (no quantifier) and ? (optional). -/
def Quantifier.isGroupRef : Quantifier -> Bool
  | .star      => true
  | .plus      => true
  | .exact _   => true
  | .range _ _ => true
  | _          => false

/-- lo(K): lower bound of quantifier (Paper Section 5.3) -/
def Quantifier.lo : Quantifier -> Nat
  | .single    => 1
  | .star      => 0
  | .plus      => 1
  | .question  => 0
  | .exact i   => i
  | .range i _ => i

/-- hi(K): upper bound of quantifier (Paper Section 5.3)
  For unbounded quantifiers (*, +), returns none. -/
def Quantifier.hi : Quantifier -> Option Nat
  | .single    => some 1
  | .star      => none   -- infinity
  | .plus      => none   -- infinity
  | .question  => some 1
  | .exact i   => some i
  | .range _ j => some j

/-! ## Pattern Tail Variable (Paper: triangle v)
  Extracts the tail node variable from a pattern.
  Defined here (not in Typing) since it is a pure syntax function
  needed by both Typing and Semantics. -/

def patternTailVar : Pattern -> Option Name
  | .node na          => some na.var
  | .edge _ _ _ n2    => some n2.var
  | .step _ _ _ n2    => some n2.var
  | .grouped P        => patternTailVar P
  | .quantified P _   => patternTailVar P
  | .patternList _ P2 => patternTailVar P2

/-! ## Pattern Lead Variable (Paper Section 5.2: lead(P))
  Extracts the leading (leftmost) node variable from a pattern.
  Used by quantified path pattern evaluation. -/

def patternLeadVar : Pattern -> Option Name
  | .node na          => some na.var
  | .edge n1 _ _ _    => some n1.var
  | .step P _ _ _     => patternLeadVar P
  | .grouped P        => patternLeadVar P
  | .quantified P _   => patternLeadVar P
  | .patternList P1 _ => patternLeadVar P1

/-! ## Pattern Variables (the variables a pattern binds)
  The set (as a list) of all variables a pattern introduces; equals the domain
  of the schema the pattern is typed to. Used by quantified-path evaluation to
  build the per-variable group-reference lists, including the zero-length match
  (which binds every variable to the empty list, so the variable set must be
  available even when the pattern produced no base matches). -/

def patternVars : Pattern -> List Name
  | .node na           => [na.var]
  | .edge n1 rel _ n2  => [n1.var, rel.var, n2.var]
  | .step P rel _ n2   => patternVars P ++ [rel.var, n2.var]
  | .grouped P         => patternVars P
  | .quantified P _    => patternVars P
  | .patternList P1 P2 => patternVars P1 ++ patternVars P2

/-! ## Projections -/

inductive Projection where
  | expr    : Expr -> Projection
  | alias'  : Expr -> Name -> Projection
  | agg     : AggOp -> AggQualifier -> Expr -> Projection
  | aggAs   : AggOp -> AggQualifier -> Expr -> Name -> Projection
  deriving Repr

abbrev ProjectionList := List Projection

/-! ## Set Operations (Paper Fig 2: circledast) -/

inductive SetOp where
  | otherwise
  | union
  | exceptDistinct
  | intersectDistinct
  | exceptAll
  | intersectAll
  deriving DecidableEq, Repr

/-! ## Queries (Paper Fig 2: q, Q) -/

inductive Query where
  | useGraph    : Name -> Query -> Query
  | matchReturn : Pattern -> ProjectionList -> Query
  | matchWhere  : Pattern -> Pred -> ProjectionList -> Query
  | composite   : SetOp -> Query -> Query -> Query
  deriving Repr

/-- Is this a linear (non-composite) query?  The paper's grammar splits
    queries into focused linear queries Q and composite queries q built
    from them (Fig. 2: q ::= Q | q circledast Q); this predicate carves the
    linear class out of the mechanization's single Query type. -/
def Query.isLinear : Query -> Bool
  | .useGraph _ Q      => Q.isLinear
  | .matchReturn _ _   => true
  | .matchWhere _ _ _  => true
  | .composite _ _ _   => false

end MGQL
