/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Examples/PatternTyping.lean -- pattern typing with endpoint refinement (Section 4.1)
-/
import MGQL.Examples.Fixtures

namespace MGQL.Examples

open MGQL

-- ============================================================
section PatternTypingExamples

/-- `(a:Person)-[r:KNOWS]->(b)`: the target is unlabeled. -/
def egPat : Pattern :=
  .edge { var := "a", labels := some (.atom "Person") }
        { var := "r", labels := some (.atom "KNOWS") } .right
        { var := "b" }

-- The pattern is accepted.
example : (inferPattern egClosedCtx .outside egPat).isSome = true := by native_decide

-- Refine-Closed prunes the unlabeled target to the Person schema:
-- a KNOWS edge cannot end at a Project (theta_D endpoint filtering).
example : (inferPattern egClosedCtx .outside egPat).map
    (fun Gv => Gv.1.lookup "b")
    = some (some (GSort.nodeRefinedOf "g" [egPersonNS])) := by native_decide

end PatternTypingExamples

end MGQL.Examples
