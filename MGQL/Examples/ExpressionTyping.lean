/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Examples/ExpressionTyping.lean -- expression typing (Appendix B)
-/
import MGQL.Examples.Fixtures

namespace MGQL.Examples

open MGQL

-- ============================================================
section ExpressionTyping

-- E-Const: an integer constant has the non-nullable integer sort.
example : inferExpr egClosedCtx RecordSchema.empty .zero .singleton
    (.const (.int 7)) = some (GSort.int, []) := by native_decide

/-- A record schema binding `n` to the Person-refined node sort. -/
def egRho : RecordSchema :=
  RecordSchema.mk [("n", GSort.nodeRefinedOf "g" [egPersonNS])]

-- E-PropAccess-Schema (closed site): `n.age` gets the precise scalar `Z?`
-- from the Person property schema (H-PropType-Schema).
example : inferExpr egClosedCtx egRho .zero .singleton
    (.propAccess "n" "age") = some (GSort.intN, ["n"]) := by native_decide

-- E-PropAccess (open site): with no schema, `n.age` gets (Z u S u B)?.
example : inferExpr egOpenCtx (RecordSchema.mk [("n", GSort.nodeOf "g")])
    .zero .singleton (.propAccess "n" "age")
    = some (GSort.anyScalarN, ["n"]) := by native_decide

-- The evaluated value is admissible at the inferred sort (Theorem 6.1
-- on this instance).
example : RecordSchema.valueAdmissible
    (evalExpr egGraph "g" [("n", Value.nodeRef "g" 0)] (.propAccess "n" "age"))
    GSort.intN = true := by native_decide

end ExpressionTyping

end MGQL.Examples
