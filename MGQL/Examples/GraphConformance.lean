/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Examples/GraphConformance.lean -- graph conformance (Definition 2.3)
-/
import MGQL.Examples.Fixtures

namespace MGQL.Examples

open MGQL

-- ============================================================
section GraphConformance

-- Every node and edge conforms to some schema: the graph conforms.
example : graphConformsSchema egGraph egSchema = true := by native_decide

-- Dropping the Project schema orphans node 2: conformance fails.
example : graphConformsSchema egGraph
    { nodeSchemas := [egPersonNS], edgeSchemas := [egKnowsES, egWorksES] }
    = false := by native_decide

end GraphConformance

end MGQL.Examples
