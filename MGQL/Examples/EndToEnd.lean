/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Examples/EndToEnd.lean -- a small end-to-end query
-/
import MGQL.Examples.Fixtures
import MGQL.Examples.PatternTyping

namespace MGQL.Examples

open MGQL

-- ============================================================
section EndToEnd

/-- MATCH (a:Person)-[r:KNOWS]->(b) WHERE a.age > 30 RETURN b.name AS friend -/
def egQuery : Query := .matchWhere
  egPat
  (.relOp .gt (.propAccess "a" "age") (.const (.int 30)))
  [.alias' (.propAccess "b" "name") "friend"]

-- The checker accepts the query.
example : (inferQuery egClosedCtx egQuery).isSome = true := by native_decide

-- Evaluation returns a single row, Ada's friend Bo.
example : (evalQuery egCatalog egGraph "g" egQuery).length = 1 := by native_decide
example : (evalQuery egCatalog egGraph "g" egQuery).head!.lookup "friend"
    = .ofString "Bo" := by native_decide

-- The result table conforms to the inferred schema; inferQuery_conforms
-- proves this in general, here it is checked on the instance.
example : RecordSchema.bindingTableConforms (evalQuery egCatalog egGraph "g" egQuery)
    ((inferQuery egClosedCtx egQuery).getD RecordSchema.empty) = true := by
  native_decide

-- The small-step engine agrees with the big-step evaluator.
example : runQuery .smallStep egCatalog egGraph "g" egQuery
    = runQuery .bigStep egCatalog egGraph "g" egQuery := by native_decide

end EndToEnd

end MGQL.Examples
