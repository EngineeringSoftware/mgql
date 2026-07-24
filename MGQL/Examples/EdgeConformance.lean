/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Examples/EdgeConformance.lean -- edge conformance (Definition 2.3)
-/
import MGQL.Examples.Fixtures

namespace MGQL.Examples

open MGQL

-- ============================================================
section EdgeConformance

-- Edge 0 (Ada -KNOWS-> Bo) conforms to the KNOWS schema: label, props,
-- directionality, and both endpoint node schemas.
example : edgeConformsSchema egGraph (Fin.mk 0 (by native_decide)) egKnowsES = true := by
  native_decide

-- Edge 1 (Bo -WORKS_ON-> Atlas) conforms to WORKS_ON but not to KNOWS
-- (label and target endpoint schema both disagree).
example : edgeConformsSchema egGraph (Fin.mk 1 (by native_decide)) egWorksES = true := by
  native_decide
example : edgeConformsSchema egGraph (Fin.mk 1 (by native_decide)) egKnowsES = false := by
  native_decide

end EdgeConformance

end MGQL.Examples
