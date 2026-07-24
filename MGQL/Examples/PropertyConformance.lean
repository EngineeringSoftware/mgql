/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Examples/PropertyConformance.lean -- property conformance (Definition 2.3)
-/
import MGQL.Examples.Fixtures

namespace MGQL.Examples

open MGQL

-- ============================================================
section PropertyConformance

-- Ada's property map conforms to the Person property schema.
example : propMapConformsSchema [("name", .ofString "Ada"), ("age", .ofInt 36)]
    [("name", .string), ("age", .int)] = true := by native_decide

-- A missing key is rejected, since the key sets must agree.
example : propMapConformsSchema [("name", .ofString "Ada")]
    [("name", .string), ("age", .int)] = false := by native_decide

-- So is a value of the wrong scalar sort.
example : propMapConformsSchema [("name", .ofInt 7), ("age", .ofInt 36)]
    [("name", .string), ("age", .int)] = false := by native_decide

end PropertyConformance

end MGQL.Examples
