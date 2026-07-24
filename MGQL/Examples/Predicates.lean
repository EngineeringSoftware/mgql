/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Examples/Predicates.lean -- predicate typing and Kleene evaluation (Appendices B, C)
-/
import MGQL.Examples.Fixtures
import MGQL.Examples.ExpressionTyping

namespace MGQL.Examples

open MGQL

-- ============================================================
section PredicateExamples

-- FTy-Rel: a comparison over a property access types at `B?`.
example : inferPred egClosedCtx egRho .one .singleton
    (.relOp .gt (.propAccess "n" "age") (.const (.int 30)))
    = some (GSort.boolN, ["n"]) := by native_decide

-- Kleene three-valued logic: True OR Unknown = True, but
-- True AND Unknown = Unknown (evalPred yields none for Unknown).
example : evalPred egGraph "g" []
    (.or .true (.relOp .lt .null (.const (.int 1)))) = some true := by native_decide
example : evalPred egGraph "g" []
    (.and .true (.relOp .lt .null (.const (.int 1)))) = none := by native_decide

end PredicateExamples

end MGQL.Examples
