/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Examples/AtomTyping.lean -- atom typing (Sch-Node, Prp rules; Section 4)
-/
import MGQL.Examples.Fixtures

namespace MGQL.Examples

open MGQL

-- ============================================================
section AtomTyping

-- Atom-Node-Closed: label filtering refines `(n:Person)` to the Person schema.
example : (inferAtomNode egClosedCtx { var := "n", labels := some (.atom "Person") }).map
    (fun Gamma => Gamma.entries)
    = some [("n", GSort.nodeRefinedOf "g" [egPersonNS])] := by native_decide

-- Atom-Node-Closed-Fail: an unsatisfiable label gets the empty type former.
example : (inferAtomNode egClosedCtx { var := "n", labels := some (.atom "Robot") }).map
    (fun Gamma => Gamma.entries)
    = some [("n", GSort.nodeEmpty "g")] := by native_decide

-- Atom-Node-Open: with no schema, the variable gets the graph-indexed sort.
example : (inferAtomNode egOpenCtx { var := "n", labels := some (.atom "Person") }).map
    (fun Gamma => Gamma.entries)
    = some [("n", GSort.nodeOf "g")] := by native_decide

end AtomTyping

end MGQL.Examples
