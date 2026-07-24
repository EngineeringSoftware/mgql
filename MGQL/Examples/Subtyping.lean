/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Examples/Subtyping.lean -- subtyping and dynamic refinement (Section 3.5, Appendix A)
-/
import MGQL.Examples.Fixtures

namespace MGQL.Examples

open MGQL

-- ============================================================
section SubtypingExamples

-- S-Ref-Node: a schema-refined node type is below its graph-indexed type.
example : Subtype (GSort.nodeRefinedOf "g" [egPersonNS]) (GSort.nodeOf "g") :=
  nodeRefineSubtype _ _

-- S-Refine-Widen (Notation 3.1): refined types widen along schema-set inclusion.
example : Subtype (GSort.nodeRefinedOf "g" [egPersonNS])
    (GSort.nodeRefinedOf "g" [egPersonNS, egProjectNS]) :=
  .refineWidenNode _ _ _ _ (by
    intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact List.mem_cons_self _ _)

-- R-Union: the open property-access union (Z u S u B)? refines to Z?.
example : DynRefine GSort.anyScalarN GSort.intN := anyScalarRefineIntN

end SubtypingExamples

end MGQL.Examples
