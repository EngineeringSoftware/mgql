/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Subtyping.lean -- Subtyping and Dynamic Refinement

  Reference: Paper Section 3.5 (Subtyping)
             Paper Appendix A (Dynamic Refinement)

  Changes from v2:
  - NodeSchema/EdgeSchema replaced with NodeSchemaFull/EdgeSchemaFull
    (schema content is now embedded directly in types)
-/
import MGQL.Sorts

namespace MGQL

-- ============================================================
--  Subtyping (Paper Section 3.5)
-- ============================================================

inductive Subtype : GSort -> GSort -> Prop where

  -- S-Reflexive: tau <: tau
  | refl (t : GSort) :
      Subtype t t

  -- S-Transitive: tau1 <: tau2, tau2 <: tau3 => tau1 <: tau3
  | trans {t1 t2 t3 : GSort} :
      Subtype t1 t2 -> Subtype t2 t3 -> Subtype t1 t3

  -- S-Any: tau <: Any
  | any (t : GSort) :
      Subtype t GSort.any

  -- S-Empty: bot <: tau (Paper Section 3.5)
  | bot (t : GSort) :
      Subtype GSort.botSort t

  -- S-RefineNode: N<G, zeta_hat> <: N<G>
  | refineNode (G : GraphSite) (ss : List NodeSchemaFull) (n : NullTag) :
      Subtype (GSort.mk (.single (.nodeRefined G ss)) n)
              (GSort.mk (.single (.node G)) n)

  -- S-RefineEdge: E<G, xi_hat> <: E<G>
  | refineEdge (G : GraphSite) (ss : List EdgeSchemaFull) (n : NullTag) :
      Subtype (GSort.mk (.single (.edgeRefined G ss)) n)
              (GSort.mk (.single (.edge G)) n)

  -- S-Refine-Widen-Node: N<G, zeta_hat_1> <: N<G, zeta_hat_2> when
  -- zeta_hat_1 is a subset of zeta_hat_2 (S-Union-L under Notation 3.1).
  | refineWidenNode (G : GraphSite) (ss1 ss2 : List NodeSchemaFull) (n : NullTag) :
      (∀ s, s ∈ ss1 → s ∈ ss2) →
      Subtype (GSort.mk (.single (.nodeRefined G ss1)) n)
              (GSort.mk (.single (.nodeRefined G ss2)) n)

  -- S-Refine-Widen-Edge: the edge counterpart
  | refineWidenEdge (G : GraphSite) (ss1 ss2 : List EdgeSchemaFull) (n : NullTag) :
      (∀ s, s ∈ ss1 → s ∈ ss2) →
      Subtype (GSort.mk (.single (.edgeRefined G ss1)) n)
              (GSort.mk (.single (.edgeRefined G ss2)) n)

  -- S-Ref-Node-Empty: tau <: N<G> ==> <N<G>>_bot <: tau
  -- (Paper Section 3.5: makes empty type former a typed bottom
  --  within each element-type hierarchy)
  | refNodeEmpty (G : GraphSite) (t : GSort) :
      Subtype t (GSort.mk (.single (.node G)) t.null) ->
      Subtype (GSort.nodeEmpty G) t

  -- S-Ref-Edge-Empty: tau <: E<G> ==> <E<G>>_bot <: tau
  | refEdgeEmpty (G : GraphSite) (t : GSort) :
      Subtype t (GSort.mk (.single (.edge G)) t.null) ->
      Subtype (GSort.edgeEmpty G) t

  -- S-List-Lift: tau1 <: tau2 => List tau1 <: List tau2
  | listCov (es1 es2 : SortShape) (en1 en2 : NullTag) (n : NullTag) :
      Subtype (GSort.mk es1 en1) (GSort.mk es2 en2) ->
      Subtype (GSort.mk (.list es1 en1) n) (GSort.mk (.list es2 en2) n)

  -- S-Union-L: for t in ts, (single t, n) <: (union ts, n)
  | unionL (ts : List ExtSort) (t : ExtSort) (n : NullTag) :
      List.Mem t ts ->
      Subtype (GSort.mk (.single t) n) (GSort.mk (.union ts) n)

  -- S-Union-R: (symmetric, subsumed by unionL via Mem)

  -- S-Union: if all branches <: tau, then union <: tau
  | unionElim (ts : List ExtSort) (n : NullTag) (target : GSort) :
      (forall t : ExtSort, List.Mem t ts ->
        Subtype (GSort.mk (.single t) n) target) ->
      Subtype (GSort.mk (.union ts) n) target

  -- S-Union-Congruence (Paper Section 3.5):
  --   Derivable from unionElim + unionL + trans.
  --   Cannot be a primitive constructor due to Lean kernel restriction
  --   on nested inductives with Exists containing local variables.
  --   See derived theorem Subtype.unionCong below.

  -- S-Nullable: tau <: tau?
  | nullable (s : SortShape) :
      Subtype (GSort.mk s .val) (GSort.mk s .nullable)

  -- S-NullSingleton: ?tau <: tau?
  | nullSingleton (s : SortShape) :
      Subtype (GSort.mk s .null) (GSort.mk s .nullable)

  -- S-NullCov: tau1 <: tau2 => tau1? <: tau2?
  | nullCov {t1 t2 : GSort} :
      Subtype t1 t2 ->
      Subtype (t1.toNullable) (t2.toNullable)

  -- S-NullSingCov: tau1 <: tau2 => ?tau1 <: ?tau2
  | nullSingCov {t1 t2 : GSort} :
      Subtype t1 t2 ->
      Subtype (t1.toNull) (t2.toNull)

-- ============================================================
--  Dynamic Refinement (Paper Appendix A)
--  R-Sub and R-Union
-- ============================================================

/-- Dynamic refinement (Paper Appendix A): R-Sub and R-Union.  List
    covariance comes through R-Sub via Subtype.listCov, so no separate
    list rule is needed. -/
inductive DynRefine : GSort -> GSort -> Prop where

  -- R-Sub: subtyping implies refinement
  | sub {t1 t2 : GSort} :
      Subtype t1 t2 -> DynRefine t1 t2

  -- R-Union: a union refines to target if some branch does
  | unionBranch (ts : List ExtSort) (t : ExtSort) (n : NullTag) (target : GSort) :
      List.Mem t ts ->
      DynRefine (GSort.mk (.single t) n) target ->
      DynRefine (GSort.mk (.union ts) n) target

-- ============================================================
--  Type Intersection (Paper Definition 3.2)
--  tau1 cap tau2
-- ============================================================

/-- Intersect-L: tau1 <: tau2 ==> tau1 cap tau2 : tau1
    Intersect-R: tau2 <: tau1 ==> tau1 cap tau2 : tau2
    Intersect:   tau <: tau1, tau <: tau2, tau1 </: tau2, tau2 </: tau1
                 ==> tau1 cap tau2 : tau -/
inductive TypeIntersection : GSort -> GSort -> GSort -> Prop where

  | intersectL {t1 t2 : GSort} :
      Subtype t1 t2 ->
      TypeIntersection t1 t2 t1

  | intersectR {t1 t2 : GSort} :
      Subtype t2 t1 ->
      TypeIntersection t1 t2 t2

  | intersect {t t1 t2 : GSort} :
      Subtype t t1 -> Subtype t t2 ->
      TypeIntersection t1 t2 t

-- ============================================================
--  Lemma 3.1 (Absorption Laws for Top and Bottom)
-- ============================================================

/-- (1) tau union Any = Any -/
theorem absorb_union_any (t : GSort) :
    Subtype t GSort.any :=
  .any t

/-- (2) tau union bot = tau (bot is absorbed by anything) -/
theorem absorb_union_bot (t : GSort) :
    Subtype GSort.botSort t :=
  .bot t

/-- (3) tau cap Any = tau (via Intersect-L with S-Any) -/
theorem absorb_inter_any (t : GSort) :
    TypeIntersection t GSort.any t :=
  .intersectL (.any t)

/-- (4) tau cap bot = bot (via Intersect-R with S-Empty) -/
theorem absorb_inter_bot (t : GSort) :
    TypeIntersection t GSort.botSort GSort.botSort :=
  .intersectR (.bot t)

-- ============================================================
--  Basic Theorems
-- ============================================================

theorem Subtype.rfl' (t : GSort) : Subtype t t := .refl t

/-- S-Union-Congruence (Paper Section 3.5): derived from unionElim + unionL + trans.
  For each t1 in ts1, if there exists t2 in ts2 with (single t1, n1) <: (single t2, n2),
  then (union ts1, n1) <: (union ts2, n2).
  Note: Cannot be a primitive inductive constructor due to Lean kernel restriction
  on nested inductives with Exists containing local variables. -/
theorem Subtype.unionCong (ts1 ts2 : List ExtSort) (n1 n2 : NullTag)
    (h : forall t1 : ExtSort, List.Mem t1 ts1 ->
      Exists fun t2 => And (List.Mem t2 ts2)
        (Subtype (GSort.mk (.single t1) n1) (GSort.mk (.single t2) n2))) :
    Subtype (GSort.mk (.union ts1) n1) (GSort.mk (.union ts2) n2) :=
  .unionElim ts1 n1 (GSort.mk (.union ts2) n2) fun t1 hMem =>
    let ⟨t2, hMem2, hSub⟩ := h t1 hMem
    .trans hSub (.unionL ts2 t2 n2 hMem2)

theorem subtypeNullable (s : SortShape) :
    Subtype (GSort.mk s .val) (GSort.mk s .nullable) :=
  .nullable s

theorem nullSingletonSubtypeNullable (s : SortShape) :
    Subtype (GSort.mk s .null) (GSort.mk s .nullable) :=
  .nullSingleton s

theorem botSubtypeAny (t : GSort) : Subtype GSort.botSort t :=
  .bot t

theorem nodeRefineSubtype (G : GraphSite) (ss : List NodeSchemaFull) :
    Subtype (GSort.nodeRefinedOf G ss) (GSort.nodeOf G) :=
  .refineNode G ss .nullable

theorem edgeRefineSubtype (G : GraphSite) (ss : List EdgeSchemaFull) :
    Subtype (GSort.edgeRefinedOf G ss) (GSort.edgeOf G) :=
  .refineEdge G ss .nullable

/-- <N<G>>_bot <: N<G, ss> for any ss (via S-Ref-Node-Empty + S-Ref-Node) -/
theorem nodeEmptySubtypeRefined (G : GraphSite) (ss : List NodeSchemaFull) :
    Subtype (GSort.nodeEmpty G) (GSort.nodeRefinedOf G ss) :=
  .refNodeEmpty G _ (nodeRefineSubtype G ss)

/-- <E<G>>_bot <: E<G, ss> for any ss (via S-Ref-Edge-Empty + S-Ref-Edge) -/
theorem edgeEmptySubtypeRefined (G : GraphSite) (ss : List EdgeSchemaFull) :
    Subtype (GSort.edgeEmpty G) (GSort.edgeRefinedOf G ss) :=
  .refEdgeEmpty G _ (edgeRefineSubtype G ss)

-- ============================================================
--  Lemma 3.2 (Schema-Refined Type Bounds)
--  <N<G>>_bot <: N<G, _> <: N<G> (similarly for edges)
-- ============================================================

/-- Any schema-refined node type is bounded below by <N<G>>_bot
    and above by N<G>. -/
theorem schemaRefinedNodeBounded (G : GraphSite) (ss : List NodeSchemaFull) :
    Subtype (GSort.nodeEmpty G) (GSort.nodeRefinedOf G ss) /\
    Subtype (GSort.nodeRefinedOf G ss) (GSort.nodeOf G) :=
  And.intro
    (nodeEmptySubtypeRefined G ss)
    (nodeRefineSubtype G ss)

theorem schemaRefinedEdgeBounded (G : GraphSite) (ss : List EdgeSchemaFull) :
    Subtype (GSort.edgeEmpty G) (GSort.edgeRefinedOf G ss) /\
    Subtype (GSort.edgeRefinedOf G ss) (GSort.edgeOf G) :=
  And.intro
    (edgeEmptySubtypeRefined G ss)
    (edgeRefineSubtype G ss)

-- ============================================================
--  Graph-Scoped Types (Paper Lemma 3.2, upper bound)
--  N<G> = N<G, zeta_hat> when zeta_hat = zeta (all node schemas)
--  Expressed as mutual subtyping.
-- ============================================================

/-- N<G, zeta_hat> <: N<G> for any zeta_hat (immediate from S-Ref-Node) -/
theorem graphScopedNode_sub (G : GraphSite) (ss : List NodeSchemaFull) :
    Subtype (GSort.nodeRefinedOf G ss) (GSort.nodeOf G) :=
  nodeRefineSubtype G ss

/-- E<G, xi_hat> <: E<G> for any xi_hat (immediate from S-Ref-Edge) -/
theorem graphScopedEdge_sub (G : GraphSite) (ss : List EdgeSchemaFull) :
    Subtype (GSort.edgeRefinedOf G ss) (GSort.edgeOf G) :=
  edgeRefineSubtype G ss

theorem Subtype.toDynRefine {t1 t2 : GSort} (h : Subtype t1 t2) :
    DynRefine t1 t2 :=
  .sub h

theorem DynRefine.rfl' (t : GSort) : DynRefine t t :=
  .sub (.refl t)

theorem boolSubtypeBoolN : Subtype GSort.bool GSort.boolN :=
  .nullable (.single (.scalar .bool))

theorem intSubtypeIntN : Subtype GSort.int GSort.intN :=
  .nullable (.single (.scalar .int))

theorem intRefineIntN : DynRefine GSort.int GSort.intN :=
  .sub intSubtypeIntN

theorem anyScalarRefineIntN : DynRefine GSort.anyScalarN GSort.intN :=
  .unionBranch _ (.scalar .int) _ _
    (List.Mem.head [.scalar .string, .scalar .bool])
    (.sub (.refl _))

theorem nodeRefinedRefineNode (G : GraphSite) (ss : List NodeSchemaFull) :
    DynRefine (GSort.nodeRefinedOf G ss) (GSort.nodeOf G) :=
  .sub (nodeRefineSubtype G ss)

theorem listNodeRefineListNode (G : GraphSite) :
    DynRefine (GSort.listOf (GSort.nodeOf G)) (GSort.listOfN (GSort.nodeOf G)) :=
  .sub (.nullable (.list (.single (.node G)) .nullable))

end MGQL
