/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Examples/NodeConformance.lean -- node conformance (Definition 2.3)
-/
import MGQL.Examples.Fixtures

namespace MGQL.Examples

open MGQL

-- ============================================================
section NodeConformance

-- Node 0 (Ada) conforms to the Person schema: labels set-equal, props conform.
example : nodeConformsSchema egGraph (Fin.mk 0 (by native_decide)) egPersonNS = true := by
  native_decide

-- Node 2 (the Atlas project) does not conform to the Person schema.
example : nodeConformsSchema egGraph (Fin.mk 2 (by native_decide)) egPersonNS = false := by
  native_decide

end NodeConformance

end MGQL.Examples
