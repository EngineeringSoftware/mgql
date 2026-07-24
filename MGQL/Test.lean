/-
  MGQL Test Suite — machine-checked assertions.
  Every test is an example proven by native_decide; a wrong assertion fails the build.
-/
import MGQL.Sorts
import MGQL.Values
import MGQL.Syntax
import MGQL.Schema
import MGQL.RecordSchema
import MGQL.Subtyping
import MGQL.Typing
import MGQL.Semantics
import MGQL.SmallStep
import MGQL.TypeChecker

namespace MGQL.Test

open MGQL

-- ============================================================
--  Test schemas (reused throughout)
-- ============================================================

def personSchema : NodeSchemaFull := {
  labels := ["Person"]
  propSchema := []
}

def projectSchema : NodeSchemaFull := {
  labels := ["Project"]
  propSchema := [("name", .string), ("projectID", .int)]
}

def knowsSchema : EdgeSchemaFull := {
  labels := ["KNOWS"]
  srcSchema := personSchema
  dstSchema := personSchema
  propSchema := []
  isDirected := true
}

def leadsSchema : EdgeSchemaFull := {
  labels := ["LEADS"]
  srcSchema := personSchema
  dstSchema := projectSchema
  propSchema := []
  isDirected := true
}

-- ============================================================
--  1. Sorts -- T0, T1, T2, T3 construction, bot, emptyFormer, nullType
-- ============================================================

section SortTests

-- T0
#check BaseSort.int
#check BaseSort.string
#check BaseSort.bool

-- T1 with full schema structures (no more id wrappers)
#check ExtSort.scalar BaseSort.int
#check ExtSort.node "myGraph"
#check ExtSort.nodeRefined "g" [personSchema, projectSchema]
#check ExtSort.edgeRefined "g" [knowsSchema]

-- GSort: non-null, nullable
example : GSort.int = GSort.mk (.single (.scalar .int)) .val := by native_decide
example : GSort.intN = GSort.mk (.single (.scalar .int)) .nullable := by native_decide
example : GSort.nodeOf "g" = GSort.mk (.single (.node "g")) .nullable := by native_decide

-- New: bot type
example : GSort.botSort = GSort.mk .bot .val := by native_decide

-- New: null type
example : GSort.nullSort = GSort.mk .nullType .val := by native_decide

-- New: emptyFormer (replaces old nodeNull)
example : GSort.nodeEmpty "g" = GSort.mk (.emptyFormer (.single (.node "g")) .nullable) .val := by native_decide
example : GSort.edgeEmpty "g" = GSort.mk (.emptyFormer (.single (.edge "g")) .nullable) .val := by native_decide

-- Backward compat: nodeNull = nodeEmpty
example : GSort.nodeNull "g" = GSort.nodeEmpty "g" := by native_decide

-- anyScalarN includes all three scalar sorts
example : GSort.anyScalarN.shape = SortShape.union [.scalar .int, .scalar .string, .scalar .bool] := by native_decide

-- Transformers
example : GSort.int.toNullable = GSort.intN := by native_decide

-- List sort
example : GSort.listOf GSort.intN = GSort.mk (.list (.single (.scalar .int)) .nullable) .val := by native_decide

-- elemSort? introspection
example : (GSort.listOf GSort.intN).elemSort? = some GSort.intN := by native_decide
example : GSort.intN.elemSort? = none := by native_decide

-- isList
example : (GSort.listOf GSort.intN).isList = true := by native_decide
example : GSort.intN.isList = false := by native_decide

-- isEmptyFormer
example : (GSort.nodeEmpty "g").isEmptyFormer = true := by native_decide
example : GSort.intN.isEmptyFormer = false := by native_decide

-- isBot
example : GSort.botSort.isBot = true := by native_decide
example : GSort.intN.isBot = false := by native_decide

-- liftToList
example : GSort.intN.liftToList = GSort.listOf GSort.intN := by native_decide

-- Schema-refined with full schemas
example : GSort.nodeRefinedOf "g" [personSchema] = GSort.mk (.single (.nodeRefined "g" [personSchema])) .nullable := by native_decide

end SortTests

-- ============================================================
--  2. Values
-- ============================================================

section ValueTests

example : Value.ofInt 42 = .prim (.int 42) := by native_decide
example : Value.isNull .null = true := by native_decide
example : Value.isNull (Value.ofInt 3) = false := by native_decide

def testListVal : Value := Value.ofList [.ofInt 1, .ofInt 2, .ofInt 3]
example : testListVal.asList.isSome = true := by native_decide

def r1 : Record := [("m", .nodeRef "g" 0), ("x", .ofInt 42)]
example : r1.lookup "m" = .nodeRef "g" 0 := by native_decide
example : r1.lookup "x" = .ofInt 42 := by native_decide
example : r1.lookup "y" = .null := by native_decide

-- Kleene logic
example : Kleene.and (some true) (some true) = some true := by native_decide
example : Kleene.and (some true) none = none := by native_decide
example : Kleene.and (some false) none = some false := by native_decide
example : Kleene.or (some true) none = some true := by native_decide

end ValueTests

-- ============================================================
--  3. Syntax -- Literal-based PropConstraint
-- ============================================================

section SyntaxTests

-- PropConstraint now uses Literal
def testPropConstraint : PropConstraint := { key := "age", val := .int 25 }

def countExpr : Expr := .agg .count .default (.var "x")
def whereCountGt0 : Pred := .relOp .gt countExpr (.const (.int 0))

#check countExpr
#check whereCountGt0

end SyntaxTests

-- ============================================================
--  4. Schema
-- ============================================================

section SchemaTests

def testGraph : PropertyGraph := {
  numNodes := 4
  numEdges := 4
  src := fun e => match e.val with
    | 0 => Fin.mk 0 (by omega)
    | 1 => Fin.mk 0 (by omega)
    | 2 => Fin.mk 2 (by omega)
    | _ => Fin.mk 1 (by omega)
  dst := fun e => match e.val with
    | 0 => Fin.mk 2 (by omega)
    | 1 => Fin.mk 3 (by omega)
    | 2 => Fin.mk 1 (by omega)
    | _ => Fin.mk 2 (by omega)
  edgeDirected := fun e => match e.val with
    | 1 => false
    | _ => true
  nodeLabels := fun n => match n.val with
    | 0 => ["Person"]
    | 1 => ["Project"]
    | 2 => ["Person"]
    | _ => ["Person"]
  edgeLabels := fun e => match e.val with
    | 0 => ["KNOWS"]
    | 1 => ["KNOWS"]
    | 2 => ["LEADS"]
    | _ => ["KNOWS"]
  nodeProps := fun n => match n.val with
    | 1 => [("name", .ofString "Atlas"), ("projectID", .ofInt 451)]
    | _ => []
  edgeProps := fun _ => []
}

example : testGraph.edgeDirected (Fin.mk 0 (by native_decide)) = true := by native_decide
example : testGraph.edgeDirected (Fin.mk 1 (by native_decide)) = false := by native_decide

example : nodeConformsSchema testGraph (Fin.mk 0 (by native_decide)) personSchema = true := by native_decide
example : nodeConformsSchema testGraph (Fin.mk 1 (by native_decide)) projectSchema = true := by native_decide
example : nodeConformsSchema testGraph (Fin.mk 0 (by native_decide)) projectSchema = false := by native_decide

-- Property constraint typing
example : literalBaseSort (.int 42) = .int := by native_decide
example : literalBaseSort (.string "hello") = .string := by native_decide
example : propConstraintSchema [{ key := "age", val := .int 25 }] = [("age", .int)] := by native_decide

end SchemaTests

-- ============================================================
--  5. RecordSchema -- emptyFormer propagation, sortInter, sortUnion
-- ============================================================

section RecordSchemaTests

def rsBase : RecordSchema := RecordSchema.mk [
  ("m", GSort.nodeOf "g"),
  ("x", GSort.edgeOf "g")
]

-- liftToGroupRef
def rsLifted := rsBase.liftToGroupRef ["x"]
example : rsLifted.lookup "m" = some (GSort.nodeOf "g") := by native_decide
example : rsLifted.lookup "x" = some (GSort.listOf (GSort.edgeOf "g")) := by native_decide

-- sortUnion
example : RecordSchema.sortUnion GSort.int GSort.string = GSort.mk (.union [.scalar .int, .scalar .string]) .nullable := by native_decide

-- sortUnion: emptyFormer union tau = tau (other dominates)
example : RecordSchema.sortUnion (GSort.nodeEmpty "g") GSort.intN = GSort.intN := by native_decide
example : RecordSchema.sortUnion GSort.intN (GSort.nodeEmpty "g") = GSort.intN := by native_decide

-- sortInter
example : RecordSchema.sortInter GSort.int GSort.int = GSort.int := by native_decide

-- sortInter: emptyFormer propagates
example : RecordSchema.sortInter (GSort.nodeEmpty "g") GSort.intN = GSort.nodeEmpty "g" := by native_decide

-- Component type (Definition 3.1)
example : GSort.componentType (GSort.listOf GSort.intN) = GSort.intN := by native_decide
example : GSort.componentType GSort.intN = GSort.intN := by native_decide

-- Type-preserving schema update (Definition 4.1)
example : GSort.liftPreservingUpdate (GSort.listOf GSort.intN) GSort.boolN = GSort.mk (.list (.single (.scalar .bool)) .nullable) .val := by native_decide

-- Compatibility
def rs1 : RecordSchema := RecordSchema.mk [("x", GSort.int)]
def rs2 : RecordSchema := RecordSchema.mk [("x", GSort.intN)]
example : rs1.compatible rs2 = true := by native_decide

-- disjointUnionCompatible
example : RecordSchema.disjointUnionCompatible (RecordSchema.mk [("x", GSort.int)]) (RecordSchema.mk [("y", GSort.bool)]) = true := by native_decide
example : RecordSchema.disjointUnionCompatible (RecordSchema.mk [("x", GSort.int)]) (RecordSchema.mk [("x", GSort.bool)]) = false := by native_decide

-- unionCompatible
example : RecordSchema.unionCompatible (RecordSchema.mk [("x", GSort.int)]) (RecordSchema.mk [("x", GSort.bool)]) = true := by native_decide
example : RecordSchema.unionCompatible (RecordSchema.mk [("x", GSort.int)]) (RecordSchema.mk [("x", GSort.bool), ("y", GSort.int)]) = false := by native_decide

end RecordSchemaTests

-- ============================================================
--  6. Subtyping -- uses full schemas now
-- ============================================================

section SubtypingTests

-- S-Ref-Node: N<G, [personSchema]> <: N<G>
#check nodeRefineSubtype "g" [personSchema]

-- <N<G>>_bot <: N<G, [personSchema]>
#check nodeEmptySubtypeRefined "g" [personSchema]

-- S-Refine-Widen (Notation 3.1 + S-Union-L): a refined type widens along
-- schema-set inclusion.
example : Subtype (GSort.nodeRefinedOf "g" [personSchema])
    (GSort.nodeRefinedOf "g" [personSchema, projectSchema]) :=
  .refineWidenNode "g" _ _ .nullable (by
    intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact List.mem_cons_self _ _)

-- DynRefine: Z union S ~> Z?
#check anyScalarRefineIntN

-- DynRefine reflexivity
#check DynRefine.rfl' GSort.int

-- List refinement
#check listNodeRefineListNode "g"

end SubtypingTests

-- ============================================================
--  7. Semantics -- aggregation evaluation
-- ============================================================

section SemanticsTests

def testVals : List Value := [.ofInt 10, .ofInt 20, .null, .ofInt 30]

example : evalAggOnValues .count .default testVals = .ofInt 3 := by native_decide
example : evalAggOnValues .sum .default testVals = .ofInt 60 := by native_decide
example : evalAggOnValues .max .default testVals = .ofInt 30 := by native_decide
example : evalAggOnValues .min .default testVals = .ofInt 10 := by native_decide

def testValsWithDups : List Value := [.ofInt 1, .ofInt 2, .ofInt 1, .ofInt 3]
example : evalAggOnValues .count .distinct testValsWithDups = .ofInt 3 := by native_decide
example : evalAggOnValues .count .default testValsWithDups = .ofInt 4 := by native_decide
example : evalAggOnValues .sum .distinct testValsWithDups = .ofInt 6 := by native_decide
example : evalAggOnValues .sum .default testValsWithDups = .ofInt 7 := by native_decide

example : evalAggOnValues .count .default [] = .ofInt 0 := by native_decide
example : evalAggOnValues .sum .default [] = .null := by native_decide

end SemanticsTests

-- ============================================================
--  8. Pattern matching
-- ============================================================

section PatternMatchTests

def personPattern : Pattern := .node { var := "m", labels := some (.atom "Person") }
def personResults := evalPattern testGraph "" personPattern
example : personResults.length = 3 := by native_decide

def knowsPattern : Pattern := .edge
  { var := "m" }
  { var := "r", labels := some (.atom "KNOWS") }
  .right
  { var := "n" }
def knowsResults := evalPattern testGraph "" knowsPattern
example : knowsResults.length = 2 := by native_decide

def leadsPattern : Pattern := .edge
  { var := "m" }
  { var := "r", labels := some (.atom "LEADS") }
  .right
  { var := "n" }
def leadsResults := evalPattern testGraph "" leadsPattern
example : leadsResults.length = 1 := by native_decide

end PatternMatchTests

-- ============================================================
--  9. Query evaluation
-- ============================================================

section QueryTests

def catalog : Catalog := [("testG", testGraph)]

def simpleQuery : Query := .matchReturn
  (.node { var := "m", labels := some (.atom "Person") })
  [.expr (.var "m")]

def simpleResult := evalQuery catalog testGraph "" simpleQuery
example : simpleResult.length = 3 := by native_decide

def filteredQuery : Query := .matchWhere
  (.edge
    { var := "m" }
    { var := "r", labels := some (.atom "LEADS") }
    .right
    { var := "n" })
  .true
  [.expr (.var "m")]

def filteredResult := evalQuery catalog testGraph "" filteredQuery
example : filteredResult.length = 1 := by native_decide

end QueryTests

-- ============================================================
--  10. VarSet operations
-- ============================================================

section VarSetTests

def vs1 : VarSet := VarSet.single "x"
def vs2 : VarSet := VarSet.single "y"
def vs3 := VarSet.union vs1 vs2

example : vs3 = ["x", "y"] := by native_decide
example : vs3.mem "x" = true := by native_decide
example : vs3.mem "z" = false := by native_decide
example : vs1.subset vs3 = true := by native_decide

def vs4 := VarSet.union vs3 vs1
example : vs4 = ["x", "y"] := by native_decide

end VarSetTests

-- ============================================================
--  11. Pattern Tail Variable
-- ============================================================

section TailVarTests

def tailNode := patternTailVar (.node { var := "m" })
example : tailNode = some "m" := by native_decide

def tailEdge := patternTailVar (.edge
  { var := "m" } { var := "r" } .right { var := "n" })
example : tailEdge = some "n" := by native_decide

-- New: step pattern tail = destination node
def tailStep := patternTailVar (.step
  (.node { var := "m" }) { var := "r" } .right { var := "n" })
example : tailStep = some "n" := by native_decide

def tailGrouped := patternTailVar (.grouped (.node { var := "m" }))
example : tailGrouped = some "m" := by native_decide

end TailVarTests

-- ============================================================
--  11b. Pattern Lead Variable (Paper Section 5.2: lead(P))
-- ============================================================

section LeadVarTests

def leadNode := patternLeadVar (.node { var := "m" })
example : leadNode = some "m" := by native_decide

def leadEdge := patternLeadVar (.edge
  { var := "m" } { var := "r" } .right { var := "n" })
example : leadEdge = some "m" := by native_decide

def leadStep := patternLeadVar (.step
  (.node { var := "a" }) { var := "r" } .right { var := "b" })
example : leadStep = some "a" := by native_decide

def leadGrouped := patternLeadVar (.grouped (.node { var := "m" }))
example : leadGrouped = some "m" := by native_decide

end LeadVarTests

-- ============================================================
--  11c. Quantifier Bounds (Paper Section 5.2)
-- ============================================================

section QuantBoundsTests

example : Quantifier.lo .star = 0 := by native_decide
example : Quantifier.lo .plus = 1 := by native_decide
example : Quantifier.lo .question = 0 := by native_decide
example : Quantifier.lo (.exact 3) = 3 := by native_decide
example : Quantifier.lo (.range 2 5) = 2 := by native_decide

example : Quantifier.hi .star = none := by native_decide
example : Quantifier.hi .plus = none := by native_decide
example : Quantifier.hi .question = some 1 := by native_decide
example : Quantifier.hi (.exact 3) = some 3 := by native_decide
example : Quantifier.hi (.range 2 5) = some 5 := by native_decide

end QuantBoundsTests

-- ============================================================
--  11d. dist() and applySetOp (Paper Section 5.3)
-- ============================================================

section SetOpTests

def b1 : BindingTable := [
  [("x", .ofInt 1)],
  [("x", .ofInt 2)],
  [("x", .ofInt 1)]
]
def b2 : BindingTable := [
  [("x", .ofInt 1)]
]

-- dist removes duplicates
example : dist b1 = [[("x", .ofInt 1)], [("x", .ofInt 2)]] := by native_decide

-- CQ-Union: bag union
example : applySetOp .union b1 b2 = b1 ++ b2 := by native_decide

-- CQ-Otherwise: non-empty -> left
example : applySetOp .otherwise b1 b2 = b1 := by native_decide
-- CQ-Otherwise-Empty: empty -> right
example : applySetOp .otherwise [] b2 = b2 := by native_decide

-- CQ-ExceptD: dist(B1 \ B2) -- removes [("x", 1)] from b1, then dist
example : (applySetOp .exceptDistinct b1 b2).length = 1 := by native_decide

-- CQ-IntersectD: dist(B1 cap B2)
example : (applySetOp .intersectDistinct b1 b2).length = 1 := by native_decide

-- CQ-ExceptA: bag difference keeps multiplicity. b1 has [("x",1)] twice and b2
-- once, so one copy survives alongside [("x",2)] (a set difference would drop
-- both copies of [("x",1)] and give length 1).
example : (applySetOp .exceptAll b1 b2).length = 2 := by native_decide
-- CQ-IntersectA: bag intersection is min-multiplicity. b1 has [("x",1)] twice,
-- b2 once, so exactly one copy is kept (a filter would keep both, length 2).
example : (applySetOp .intersectAll b1 b2).length = 1 := by native_decide

-- Canonical multiplicity checks: {{a,a}} EXCEPT ALL {{a}} = {{a}}, and
-- {{a,a}} INTERSECT ALL {{a}} = {{a}}.
example : applySetOp .exceptAll [[("x", .ofInt 1)], [("x", .ofInt 1)]] [[("x", .ofInt 1)]]
    = [[("x", .ofInt 1)]] := by native_decide
example : applySetOp .intersectAll [[("x", .ofInt 1)], [("x", .ofInt 1)]] [[("x", .ofInt 1)]]
    = [[("x", .ofInt 1)]] := by native_decide

-- phiD: runtime endpoint condition (Paper Section 5.2)
-- testGraph edge 0: src=0(Person)->dst=2(Person), directed, label KNOWS
-- phiD .right node0 edge0 node2 should be true
example : phiD testGraph .right (Fin.mk 0 (by native_decide)) (Fin.mk 0 (by native_decide)) (Fin.mk 2 (by native_decide)) = true := by native_decide
-- phiD .left node0 edge0 node2 should be false (wrong direction)
example : phiD testGraph .left (Fin.mk 0 (by native_decide)) (Fin.mk 0 (by native_decide)) (Fin.mk 2 (by native_decide)) = false := by native_decide
-- testGraph edge 1: src=0->dst=3, undirected, label KNOWS
-- phiD .undirected should work both ways
example : phiD testGraph .undirected (Fin.mk 0 (by native_decide)) (Fin.mk 1 (by native_decide)) (Fin.mk 3 (by native_decide)) = true := by native_decide
example : phiD testGraph .undirected (Fin.mk 3 (by native_decide)) (Fin.mk 1 (by native_decide)) (Fin.mk 0 (by native_decide)) = true := by native_decide

end SetOpTests

-- ============================================================
--  12. Direction Variants (Paper Figure 2, all 7 edge directions)
-- ============================================================

section DirectionTests

-- All 7 direction constructors exist
#check Direction.right
#check Direction.left
#check Direction.anyDirected
#check Direction.undirected
#check Direction.rightOrUndirected
#check Direction.leftOrUndirected
#check Direction.any

-- reverseDir is involutive for symmetric cases
example : reverseDir .right = .left := by native_decide
example : reverseDir .left = .right := by native_decide
example : reverseDir .anyDirected = .anyDirected := by native_decide
example : reverseDir .undirected = .undirected := by native_decide
example : reverseDir .rightOrUndirected = .leftOrUndirected := by native_decide
example : reverseDir .leftOrUndirected = .rightOrUndirected := by native_decide
example : reverseDir .any = .any := by native_decide

-- thetaD with 3-arg signature (source node, edge, target node)
-- KNOWS: Person -> Person (directed)
-- right: src=Person, dst=Person matches
example : thetaD .right personSchema knowsSchema personSchema = true := by native_decide
-- right: src=Project, dst=Person does not match KNOWS
example : thetaD .right projectSchema knowsSchema personSchema = false := by native_decide
-- LEADS: Person -> Project (directed)
example : thetaD .right personSchema leadsSchema projectSchema = true := by native_decide
-- left reversal: target=Person, src=Project for LEADS
example : thetaD .left projectSchema leadsSchema personSchema = true := by native_decide

end DirectionTests

-- ============================================================
--  13. Quantifier Lift (Paper Definition 4.2)
-- ============================================================

section QuantLiftTests

def liftTestCtx : RecordSchema :=
  RecordSchema.mk [("r", GSort.edgeOf "g"), ("n", GSort.nodeOf "g")]

-- List lift for group-ref quantifiers (*, +, {i}, {i,j})
def liftedList := RecordSchema.liftToGroupRef liftTestCtx ["r"]
example : liftedList.lookup "r" = some (GSort.listOf (GSort.edgeOf "g")) := by native_decide
example : liftedList.lookup "n" = some (GSort.nodeOf "g") := by native_decide

-- Nullable lift for optional quantifier (?)
def liftedNullable := RecordSchema.liftToNullable liftTestCtx ["r"]
example : liftedNullable.lookup "r" = some (GSort.edgeOf "g").toNullable := by native_decide
example : liftedNullable.lookup "n" = some (GSort.nodeOf "g") := by native_decide

end QuantLiftTests

-- ============================================================
--  14. Type Intersection (Paper Definition 3.2)
-- ============================================================

section TypeIntersectionTests

-- Intersect-L: tau <: Any ==> tau cap Any = tau
example : TypeIntersection GSort.int GSort.any GSort.int :=
  .intersectL (.any _)

-- Intersect-R: bot <: tau ==> tau cap bot = bot
example : TypeIntersection GSort.int GSort.botSort GSort.botSort :=
  .intersectR (.bot _)

end TypeIntersectionTests

-- ============================================================
--  15. Lemma 3.1 (Absorption Laws) and Lemma 3.2
-- ============================================================

section AbsorptionTests

-- (1) tau union Any = Any (tau <: Any)
example : Subtype GSort.int GSort.any := absorb_union_any GSort.int

-- (2) bot <: tau
example : Subtype GSort.botSort GSort.int := absorb_union_bot GSort.int

-- (3) tau cap Any = tau
example : TypeIntersection GSort.boolN GSort.any GSort.boolN := absorb_inter_any GSort.boolN

-- (4) tau cap bot = bot
example : TypeIntersection GSort.boolN GSort.botSort GSort.botSort := absorb_inter_bot GSort.boolN

-- Lemma 3.2: <N<G>>_bot <: N<G,ss> <: N<G>
example : Subtype (GSort.nodeEmpty "g") (GSort.nodeRefinedOf "g" [personSchema]) :=
  (schemaRefinedNodeBounded "g" [personSchema]).1

example : Subtype (GSort.nodeRefinedOf "g" [personSchema]) (GSort.nodeOf "g") :=
  (schemaRefinedNodeBounded "g" [personSchema]).2

end AbsorptionTests

-- ============================================================
--  16. Component Type (Paper Definition 3.1)
-- ============================================================

section ComponentTypeTests

-- Non-list: component type is identity
example : GSort.componentType (GSort.nodeOf "g") = GSort.nodeOf "g" := by native_decide
example : GSort.componentType GSort.int = GSort.int := by native_decide

-- List: strips outermost List wrapper
example : GSort.componentType (GSort.listOf (GSort.nodeOf "g")) = GSort.nodeOf "g" := by native_decide
example : GSort.componentType (GSort.listOf GSort.int) = GSort.int := by native_decide

end ComponentTypeTests

-- ============================================================
--  17. Expression Evaluation (evalExpr, evalArith, evalLiteral)
-- ============================================================

section ExprTests

-- testGraph node 1 = Project with name="Atlas", projectID=451
-- Bind m -> nodeRef 1, x -> 42
def exprRho : Record := [("m", .nodeRef "" 1), ("x", .ofInt 42), ("y", .ofString "hello")]

-- const
example : evalExpr testGraph "" exprRho (.const (.int 7)) = .ofInt 7 := by native_decide
example : evalExpr testGraph "" exprRho (.const (.string "hi")) = .ofString "hi" := by native_decide
example : evalExpr testGraph "" exprRho (.const (.bool true)) = .ofBool true := by native_decide

-- null
example : evalExpr testGraph "" exprRho .null = .null := by native_decide

-- var
example : evalExpr testGraph "" exprRho (.var "x") = .ofInt 42 := by native_decide
example : evalExpr testGraph "" exprRho (.var "y") = .ofString "hello" := by native_decide
example : evalExpr testGraph "" exprRho (.var "missing") = .null := by native_decide

-- propAccess: m is nodeRef 1, node 1 has name="Atlas" and projectID=451
example : evalExpr testGraph "" exprRho (.propAccess "m" "name") = .ofString "Atlas" := by native_decide
example : evalExpr testGraph "" exprRho (.propAccess "m" "projectID") = .ofInt 451 := by native_decide
example : evalExpr testGraph "" exprRho (.propAccess "m" "missing") = .null := by native_decide
example : evalExpr testGraph "" exprRho (.propAccess "x" "name") = .null := by native_decide

-- arithOp
example : evalExpr testGraph "" exprRho (.arithOp .add (.var "x") (.const (.int 8))) = .ofInt 50 := by native_decide
example : evalExpr testGraph "" exprRho (.arithOp .sub (.var "x") (.const (.int 2))) = .ofInt 40 := by native_decide
example : evalExpr testGraph "" exprRho (.arithOp .mul (.const (.int 3)) (.const (.int 7))) = .ofInt 21 := by native_decide
example : evalExpr testGraph "" exprRho (.arithOp .div (.var "x") (.const (.int 5))) = .ofInt 8 := by native_decide
example : evalExpr testGraph "" exprRho (.arithOp .div (.var "x") (.const (.int 0))) = .null := by native_decide
example : evalExpr testGraph "" exprRho (.arithOp .add (.var "y") (.const (.int 1))) = .null := by native_decide

end ExprTests

-- ============================================================
--  18. Relational Operators (evalRelOp)
-- ============================================================

section RelOpTests

-- Int comparisons
example : evalRelOp .eq (.ofInt 3) (.ofInt 3) = some true := by native_decide
example : evalRelOp .eq (.ofInt 3) (.ofInt 4) = some false := by native_decide
example : evalRelOp .neq (.ofInt 3) (.ofInt 4) = some true := by native_decide
example : evalRelOp .lt (.ofInt 3) (.ofInt 4) = some true := by native_decide
example : evalRelOp .lt (.ofInt 4) (.ofInt 3) = some false := by native_decide
example : evalRelOp .le (.ofInt 3) (.ofInt 3) = some true := by native_decide
example : evalRelOp .gt (.ofInt 5) (.ofInt 3) = some true := by native_decide
example : evalRelOp .ge (.ofInt 3) (.ofInt 3) = some true := by native_decide
example : evalRelOp .ge (.ofInt 2) (.ofInt 3) = some false := by native_decide

-- Non-integer operands yield Null (paper E-Relational-Null): the comparison is
-- defined only on two integers, so string and bool operands propagate Null.
example : evalRelOp .eq (.ofString "a") (.ofString "a") = none := by native_decide
example : evalRelOp .neq (.ofString "a") (.ofString "b") = none := by native_decide
example : evalRelOp .lt (.ofString "a") (.ofString "b") = none := by native_decide
example : evalRelOp .eq (.ofBool true) (.ofBool true) = none := by native_decide
example : evalRelOp .neq (.ofBool true) (.ofBool false) = none := by native_decide

-- Null propagation (Kleene)
example : evalRelOp .eq .null (.ofInt 3) = none := by native_decide
example : evalRelOp .eq (.ofInt 3) .null = none := by native_decide
example : evalRelOp .eq .null .null = none := by native_decide

-- Cross-type: int vs string
example : evalRelOp .eq (.ofInt 3) (.ofString "3") = none := by native_decide

end RelOpTests

-- ============================================================
--  19. Predicate Evaluation (evalPred, Kleene 3-valued)
-- ============================================================

section PredTests

def predRho : Record := [("x", .ofInt 10), ("y", .ofInt 20), ("z", .null)]

-- true / false
example : evalPred testGraph "" predRho .true = some true := by native_decide
example : evalPred testGraph "" predRho .false = some false := by native_decide

-- relOp
example : evalPred testGraph "" predRho (.relOp .lt (.var "x") (.var "y")) = some true := by native_decide
example : evalPred testGraph "" predRho (.relOp .gt (.var "x") (.var "y")) = some false := by native_decide
example : evalPred testGraph "" predRho (.relOp .eq (.var "x") (.const (.int 10))) = some true := by native_decide

-- not
example : evalPred testGraph "" predRho (.not .true) = some false := by native_decide
example : evalPred testGraph "" predRho (.not .false) = some true := by native_decide

-- and
example : evalPred testGraph "" predRho (.and .true .true) = some true := by native_decide
example : evalPred testGraph "" predRho (.and .true .false) = some false := by native_decide
example : evalPred testGraph "" predRho (.and .false .true) = some false := by native_decide

-- or
example : evalPred testGraph "" predRho (.or .false .true) = some true := by native_decide
example : evalPred testGraph "" predRho (.or .false .false) = some false := by native_decide

-- isNull
example : evalPred testGraph "" predRho (.isNull (.var "z")) = some true := by native_decide
example : evalPred testGraph "" predRho (.isNull (.var "x")) = some false := by native_decide
example : evalPred testGraph "" predRho (.isNull (.var "missing")) = some true := by native_decide

-- Kleene: null propagation through and/or/not
example : evalPred testGraph "" predRho (.relOp .eq (.var "z") (.const (.int 1))) = none := by native_decide
example : evalPred testGraph "" predRho (.and (.relOp .eq (.var "z") (.const (.int 1))) .true) = none := by native_decide
example : evalPred testGraph "" predRho (.and (.relOp .eq (.var "z") (.const (.int 1))) .false) = some false := by native_decide
example : evalPred testGraph "" predRho (.or .true (.relOp .eq (.var "z") (.const (.int 1)))) = some true := by native_decide
example : evalPred testGraph "" predRho (.or .false (.relOp .eq (.var "z") (.const (.int 1)))) = none := by native_decide
example : evalPred testGraph "" predRho (.not (.relOp .eq (.var "z") (.const (.int 1)))) = none := by native_decide

end PredTests

-- ============================================================
--  20. Label Expression Evaluation (evalLabelExpr)
-- ============================================================

section LabelExprTests

-- atom
example : evalLabelExpr ["Person", "Employee"] (.atom "Person") = true := by native_decide
example : evalLabelExpr ["Person"] (.atom "Project") = false := by native_decide
example : evalLabelExpr [] (.atom "Person") = false := by native_decide

-- wildcard
example : evalLabelExpr ["Person"] .wildcard = true := by native_decide
example : evalLabelExpr [] .wildcard = false := by native_decide

-- neg
example : evalLabelExpr ["Person"] (.neg (.atom "Project")) = true := by native_decide
example : evalLabelExpr ["Person"] (.neg (.atom "Person")) = false := by native_decide

-- conj
example : evalLabelExpr ["Person", "Employee"] (.conj (.atom "Person") (.atom "Employee")) = true := by native_decide
example : evalLabelExpr ["Person"] (.conj (.atom "Person") (.atom "Employee")) = false := by native_decide

-- disj
example : evalLabelExpr ["Person"] (.disj (.atom "Person") (.atom "Project")) = true := by native_decide
example : evalLabelExpr ["Other"] (.disj (.atom "Person") (.atom "Project")) = false := by native_decide

end LabelExprTests

-- ============================================================
--  21. Variable-length Path Matching (matchVarLengthPath)
-- ============================================================

section VarLengthPathTests

-- testGraph: 4 nodes, 4 edges
-- e0: n0(Person)->n2(Person) KNOWS directed
-- e1: n0->n3(Person) KNOWS undirected
-- e2: n2(Person)->n1(Project) LEADS directed
-- e3: n1(Project)->n2(Person) KNOWS directed

def vlpSrc : NodeAtom := { var := "a" }
def vlpRel : EdgeAtom := { var := "r", labels := some (.atom "KNOWS") }
def vlpDst : NodeAtom := { var := "b" }

-- k=0: every source node matches itself (no edge traversed)
example : (matchVarLengthPath testGraph "" vlpSrc vlpRel vlpDst .right 0).length = 4 := by native_decide

-- k=1: single KNOWS edges in .right direction (directed only)
-- e0: n0->n2, e3: n1->n2
example : (matchVarLengthPath testGraph "" vlpSrc vlpRel vlpDst .right 1).length = 2 := by native_decide

-- k=2: 2-hop KNOWS paths in .right direction
-- n0->n2 then n2 has no outgoing directed KNOWS, so only via e3: but n1 is Project
-- Let me check: e0 n0->n2, e3 n1->n2. From n0: n0->n2(e0), n2 has no outgoing directed KNOWS. From n1: n1->n2(e3), n2 has no outgoing directed KNOWS. So k=2 = 0.
example : (matchVarLengthPath testGraph "" vlpSrc vlpRel vlpDst .right 2).length = 0 := by native_decide

-- undirected KNOWS: e1 is undirected KNOWS n0~n3
example : (matchVarLengthPath testGraph "" vlpSrc vlpRel vlpDst .undirected 1).length = 2 := by native_decide

end VarLengthPathTests

-- ============================================================
--  22. Schema Operations (edgeConformsSchema, schemaUnion, sortCompatible)
-- ============================================================

section SchemaOpTests

-- edgeConformsSchema
example : edgeConformsSchema testGraph (Fin.mk 0 (by native_decide)) knowsSchema = true := by native_decide
example : edgeConformsSchema testGraph (Fin.mk 2 (by native_decide)) leadsSchema = true := by native_decide
example : edgeConformsSchema testGraph (Fin.mk 0 (by native_decide)) leadsSchema = false := by native_decide

-- schemaUnion: shared keys get sortUnion, disjoint keys appear in both
example : (RecordSchema.schemaUnion
  (RecordSchema.mk [("x", GSort.int)])
  (RecordSchema.mk [("x", GSort.string)])).lookup "x" =
  some (RecordSchema.sortUnion GSort.int GSort.string) := by native_decide

-- schemaUnion only keeps keys from Ctx1; Ctx2-only keys are dropped
example : (RecordSchema.schemaUnion
  (RecordSchema.mk [("x", GSort.int)])
  (RecordSchema.mk [("y", GSort.bool)])).lookup "x" = some GSort.int := by native_decide

example : (RecordSchema.schemaUnion
  (RecordSchema.mk [("x", GSort.int)])
  (RecordSchema.mk [("y", GSort.bool)])).lookup "y" = none := by native_decide

-- sortCompatible: same kind counts as compatible (int/string are both .scalar)
example : RecordSchema.sortCompatible GSort.int GSort.int = true := by native_decide
example : RecordSchema.sortCompatible GSort.int GSort.string = true := by native_decide
example : RecordSchema.sortCompatible GSort.int GSort.intN = true := by native_decide
example : RecordSchema.sortCompatible GSort.int (GSort.nodeOf "g") = false := by native_decide

end SchemaOpTests

-- ============================================================
--  23. Quantifier Normalization
-- ============================================================

section QuantNormTests

example : quantifierNormalize .star 10 = (0, 10) := by native_decide
example : quantifierNormalize .plus 10 = (1, 10) := by native_decide
example : quantifierNormalize .question 10 = (0, 1) := by native_decide
example : quantifierNormalize (.exact 3) 10 = (3, 3) := by native_decide
example : quantifierNormalize (.range 2 5) 10 = (2, 5) := by native_decide
example : quantifierNormalize .single 10 = (1, 1) := by native_decide

end QuantNormTests

-- ============================================================
--  15. Engine flag: small-step interpreter vs big-step evaluator
--  (executable confirmation of runQuery_engine_agnostic)
-- ============================================================

section SmallStepEngineTests

example : runQuery .smallStep catalog testGraph "" simpleQuery
    = runQuery .bigStep catalog testGraph "" simpleQuery := by native_decide

example : runQuery .smallStep catalog testGraph "" filteredQuery
    = runQuery .bigStep catalog testGraph "" filteredQuery := by native_decide

example : (runQuery .smallStep catalog testGraph "" simpleQuery).length = 3 := by
  native_decide

example : (runQuery .smallStep catalog testGraph "" filteredQuery).length = 1 := by
  native_decide

-- Composite query through the small-step engine (Cor 6.1 path).
example : (runQuery .smallStep catalog testGraph ""
    (.composite .union simpleQuery simpleQuery)).length = 6 := by native_decide

-- Graph resolution (FSQueryUse path) through the small-step engine.
example : (runQuery .smallStep catalog testGraph ""
    (.useGraph "testG" simpleQuery)).length = 3 := by native_decide

end SmallStepEngineTests

-- ============================================================
--  16. Predicates as value expressions (Paper Fig 2: e ::= ... | phi)
-- ============================================================

section PredExprTests

-- A comparison used as a value evaluates to its truth value.
example : evalExpr testGraph "" [] (.pred (.relOp .gt (.const (.int 5)) (.const (.int 3))))
    = Value.ofBool true := by native_decide

example : evalExpr testGraph "" [] (.pred (.relOp .lt (.const (.int 5)) (.const (.int 3))))
    = Value.ofBool false := by native_decide

-- Kleene: an undefined comparison surfaces as Null in the value domain.
example : evalExpr testGraph "" [] (.pred (.relOp .eq .null (.const (.int 1))))
    = Value.null := by native_decide

-- Logical structure evaluates under Kleene logic.
example : evalExpr testGraph "" []
    (.pred (.and (.relOp .gt (.const (.int 5)) (.const (.int 3))) .true))
    = Value.ofBool true := by native_decide

-- RETURN (predicate) AS flag: boolean-valued projection through evalQuery.
def predProjQuery : Query := .matchReturn
  (.node { var := "m", labels := some (.atom "Person") })
  [.alias' (.pred (.relOp .gt (.const (.int 2)) (.const (.int 1)))) "flag"]

example : (evalQuery catalog testGraph "" predProjQuery).all
    (fun rho => rho.lookup "flag" == Value.ofBool true) = true := by native_decide

-- Both engines agree on boolean-valued projections.
example : runQuery .smallStep catalog testGraph "" predProjQuery
    = runQuery .bigStep catalog testGraph "" predProjQuery := by native_decide

end PredExprTests

-- ============================================================
--  15. Trail path mode (Paper Section 5.2)
--
--  A single directed self-loop A -e0-> A.  The length-2 walk e0,e0
--  exists (the walk evaluator finds it), but it repeats an edge, so
--  trail mode must reject it while keeping the length-1 match.
-- ============================================================
section TrailTests

def loopGraph : PropertyGraph := {
  numNodes := 1
  numEdges := 1
  src := fun _ => Fin.mk 0 (by omega)
  dst := fun _ => Fin.mk 0 (by omega)
  edgeDirected := fun _ => true
  nodeLabels := fun _ => ["Person"]
  edgeLabels := fun _ => ["KNOWS"]
  nodeProps := fun _ => []
  edgeProps := fun _ => []
}

/-- `(a)-[r*2..2]->(b)`: exactly-two-edges quantified edge pattern. -/
def loopPat2 : Pattern :=
  .edge { var := "a" } { var := "r", quantifier := .exact 2 } .right { var := "b" }

/-- `(a)-[r*1..1]->(b)`: exactly-one-edge pattern. -/
def loopPat1 : Pattern :=
  .edge { var := "a" } { var := "r", quantifier := .exact 1 } .right { var := "b" }

-- The walk evaluator finds the repeated-edge length-2 walk ...
example : (evalPattern loopGraph "" loopPat2).length = 1 := by native_decide

-- Its single row binds edge 0 twice inside the list r, so it is not a trail,
example : (evalPattern loopGraph "" loopPat2).all
    (fun rho => !rho.isTrail) = true := by native_decide

-- and trail mode rejects it.
example : evalPatternTrail loopGraph "" loopPat2 = [] := by native_decide

-- The length-1 match is a trail and survives.
example : (evalPatternTrail loopGraph "" loopPat1).length = 1 := by native_decide

-- Query level: trail semantics is what MATCH ... RETURN uses.
def loopQuery2 : Query := .matchReturn loopPat2 [.expr (.var "r")]
def loopQuery1 : Query := .matchReturn loopPat1 [.expr (.var "r")]

example : evalQuery [] loopGraph "" loopQuery2 = [] := by native_decide
example : (evalQuery [] loopGraph "" loopQuery1).length = 1 := by native_decide

-- Both engines agree under trail mode (repeated-edge walk rejected in both).
example : runQuery .smallStep [] loopGraph "" loopQuery2
    = runQuery .bigStep [] loopGraph "" loopQuery2 := by native_decide
example : runQuery .smallStep [] loopGraph "" loopQuery1
    = runQuery .bigStep [] loopGraph "" loopQuery1 := by native_decide

-- Trail-ness is per comma component: the SAME edge may be reused by two
-- different components of one pattern list.
def loopPatList : Pattern := .patternList loopPat1
  (.edge { var := "c" } { var := "s", quantifier := .exact 1 } .right { var := "d" })

example : (evalPatternTrail loopGraph "" loopPatList).length = 1 := by native_decide

end TrailTests

-- ============================================================
--  16. The ? (zero-or-one) quantifier (Paper Definition 4.2)
--
--  On loopGraph, `(a)-[r?]->(b)` has a zero match (a = b = node 0 with
--  r bound to NULL -- not to an empty list) and a one match (edge 0).
-- ============================================================
section OptQuantTests

def optPat : Pattern :=
  .edge { var := "a" } { var := "r", quantifier := .question } .right { var := "b" }

-- Zero match + one match.
example : (evalPattern loopGraph "" optPat).length = 2 := by native_decide

-- The zero match binds the edge variable to null (the ? lift's nullable
-- reading), and both endpoints to the same node.
example : (evalPattern loopGraph "" optPat).any
    (fun rho => rho.lookup "r" == Value.null
      && rho.lookup "a" == rho.lookup "b") = true := by native_decide

-- The one match binds an edge reference, not a singleton list.
example : (evalPattern loopGraph "" optPat).any
    (fun rho => rho.lookup "r" == Value.edgeRef "" 0) = true := by native_decide

-- Null binds no edges, so both rows are trails.
example : (evalPatternTrail loopGraph "" optPat).length = 2 := by native_decide

-- The ? pattern is TYPABLE (Pat-Opt-Edge), with the edge variable's sort
-- passed through the nullable lift.
example : PatternTyping { catalog := [], schemaMap := [], graphSite := "" }
    .outside optPat
    (((RecordSchema.mk [("a", GSort.nodeOf "")]).join
        (RecordSchema.mk [("r", GSort.edgeOf "")])
        |>.join (RecordSchema.mk [("b", GSort.nodeOf "")])).liftToNullable ["r"]) "b" :=
  PatternTyping.patOptEdge { catalog := [], schemaMap := [], graphSite := "" }
    { var := "a" } { var := "b" } { var := "r" } .right rfl rfl

-- Query level: both engines agree on the optional-edge query.
def optQuery : Query := .matchReturn optPat [.expr (.var "r")]
example : (evalQuery [] loopGraph "" optQuery).length = 2 := by native_decide
example : runQuery .smallStep [] loopGraph "" optQuery
    = runQuery .bigStep [] loopGraph "" optQuery := by native_decide

end OptQuantTests

-- ============================================================
--  17. theta_D faithfulness bridge
--
--  On a well-formed catalog (label-discriminated, endpoint-closed) the
--  typing's label-set triple compatibility IS the paper's theta_D.
-- ============================================================
section ThetaDTests

def testPsi : GraphSchemaFull := {
  nodeSchemas := [personSchema, projectSchema]
  edgeSchemas := [knowsSchema, leadsSchema]
}

-- The test catalog is well-formed (boolean reflections of
-- SchemaLabelUnique / SchemaEndpointClosed).
example : (testPsi.nodeSchemas.all fun z1 => testPsi.nodeSchemas.all fun z2 =>
    !(labelSetEq z1.labels z2.labels) || (z1 == z2)) = true := by native_decide
example : (testPsi.edgeSchemas.all fun es =>
    testPsi.nodeSchemas.contains es.srcSchema
      && testPsi.nodeSchemas.contains es.dstSchema) = true := by native_decide

-- On it, label-set compatibility agrees with theta_D pointwise.
example : tripleCompat personSchema knowsSchema personSchema .right
    = thetaD .right personSchema knowsSchema personSchema := by native_decide
example : tripleCompat projectSchema knowsSchema personSchema .right
    = thetaD .right projectSchema knowsSchema personSchema := by native_decide
example : tripleCompat personSchema leadsSchema projectSchema .right
    = thetaD .right personSchema leadsSchema projectSchema := by native_decide
example : tripleCompat projectSchema leadsSchema personSchema .left
    = thetaD .left projectSchema leadsSchema personSchema := by native_decide

-- And WITHOUT well-formedness the two genuinely differ: a conformant
-- schema with the same labels but a different property schema passes the
-- label-set check yet fails theta_D's schema equality.
def personSchemaAged : NodeSchemaFull := {
  labels := ["Person"]
  propSchema := [("age", .int)]
}
example : tripleCompat personSchemaAged knowsSchema personSchema .right = true := by
  native_decide
example : thetaD .right personSchemaAged knowsSchema personSchema = false := by
  native_decide

end ThetaDTests

-- ============================================================
--  18. Aggregation in WHERE (paper FTy-Match-Where-Ret types the
--  predicate with aggregation budget 1: one root aggregation node,
--  evaluated per row over list-valued group references)
-- ============================================================
section WhereAggTests

def whereAggQuery (n : Int) : Query := .matchWhere
  (.edge { var := "a" } { var := "r", quantifier := .exact 1 } .right { var := "b" })
  (.relOp .gt (.agg .count .default (.var "r")) (.const (.int n)))
  [.expr (.var "a")]

-- Count(r) counts the single-edge list's elements per row.
example : (evalQuery [] loopGraph "" (whereAggQuery 0)).length = 1 := by native_decide
example : evalQuery [] loopGraph "" (whereAggQuery 1) = [] := by native_decide

-- Both engines agree with an aggregate in WHERE.
example : runQuery .smallStep [] loopGraph "" (whereAggQuery 0)
    = runQuery .bigStep [] loopGraph "" (whereAggQuery 0) := by native_decide

end WhereAggTests

-- ============================================================
--  19. Count qualifiers in singleton context; aggregates inside
--      alias expressions at budget one
-- ============================================================
section PaperStrengthTests

/-- Open-site typing context over the loop graph. -/
def loopCtx : TypingCtx :=
  { catalog := [("g", loopGraph)], schemaMap := [], graphSite := "g" }

/-- Count(Distinct r) in a singleton (WHERE) context. -/
def whereCountDistinct : Query := .matchWhere
  (.edge { var := "a" } { var := "r", quantifier := .exact 1 } .right { var := "b" })
  (.relOp .gt (.agg .count .distinct (.var "r")) (.const (.int 0)))
  [.expr (.var "a")]

example : (inferQuery loopCtx whereCountDistinct).isSome = true := by native_decide
example : (evalQuery [("g", loopGraph)] loopGraph "g" whereCountDistinct).length = 1 := by
  native_decide

/-- An aggregate under an operator inside an alias: Count(r) + 1 As cnt1. -/
def aliasAggPlus : Query := .matchReturn
  (.edge { var := "a" } { var := "r", quantifier := .exact 1 } .right { var := "b" })
  [.alias' (.arithOp .add (.agg .count .default (.var "r")) (.const (.int 1))) "cnt1"]

example : (inferQuery loopCtx aliasAggPlus).isSome = true := by native_decide
example : (evalQuery [("g", loopGraph)] loopGraph "g" aliasAggPlus).head!.lookup "cnt1"
    = .ofInt 2 := by native_decide

-- The evaluated table conforms to the inferred schema and both engines
-- agree.
example : RecordSchema.bindingTableConforms
    (evalQuery [("g", loopGraph)] loopGraph "g" aliasAggPlus)
    ((inferQuery loopCtx aliasAggPlus).getD RecordSchema.empty) = true := by native_decide
example : runQuery .smallStep [("g", loopGraph)] loopGraph "g" aliasAggPlus
    = runQuery .bigStep [("g", loopGraph)] loopGraph "g" aliasAggPlus := by native_decide

end PaperStrengthTests

-- ============================================================
--  20. Uniform composite operators (single-operator judgment, ISO 14.2)
-- ============================================================
section CompositeUniformTests

def linQ : Query := .matchReturn (.node { var := "a" }) [.expr (.var "a")]

/-- a UNION a UNION a: one operator throughout the composite. -/
def uniformUnion : Query := .composite .union (.composite .union linQ linQ) linQ

/-- (a UNION a) EXCEPT ALL a: mixes two operator kinds. -/
def mixedOps : Query := .composite .exceptAll (.composite .union linQ linQ) linQ

-- The operator-indexed checker accepts the uniform composite; evaluation
-- is the bag union of three singleton tables and conforms.
example : (inferCompQuery loopCtx .union uniformUnion).isSome = true := by native_decide
example : (evalQuery [("g", loopGraph)] loopGraph "g" uniformUnion).length = 3 := by
  native_decide
example : RecordSchema.bindingTableConforms
    (evalQuery [("g", loopGraph)] loopGraph "g" uniformUnion)
    ((inferCompQuery loopCtx .union uniformUnion).getD RecordSchema.empty) = true := by
  native_decide

-- The mixed composite is rejected at either operator index.
example : (inferCompQuery loopCtx .exceptAll mixedOps).isNone = true := by native_decide
example : (inferCompQuery loopCtx .union mixedOps).isNone = true := by native_decide
-- The generalized per-node judgment still types it.
example : (inferQuery loopCtx mixedOps).isSome = true := by native_decide

end CompositeUniformTests

-- ============================================================
--  21. Schema filtering and conformance units (Sch-Lbl-*, Sch-Prp-Atom,
--      Definition 2.3, Refine-Closed/-Fail/-Empty dispatch)
-- ============================================================
section SchemaFilterTests

def testSchemaFull : GraphSchemaFull :=
  { nodeSchemas := [personSchema, projectSchema]
    edgeSchemas := [knowsSchema, leadsSchema] }

-- Sch-Lbl-Atom: retain schemas whose label set contains the label.
example : labelFilterNodeSchemas testSchemaFull (.atom "Person")
    = [personSchema] := by native_decide
-- Sch-Lbl-Wildcard: retain every schema with at least one label.
example : labelFilterNodeSchemas testSchemaFull .wildcard
    = [personSchema, projectSchema] := by native_decide
-- Sch-Lbl-Negation: set difference against the matched schemas.
example : labelFilterNodeSchemas testSchemaFull (.neg (.atom "Person"))
    = [projectSchema] := by native_decide
-- Sch-Lbl-Conjunction: intersection (Person & Project matches nothing).
example : labelFilterNodeSchemas testSchemaFull (.conj (.atom "Person") (.atom "Project"))
    = [] := by native_decide
-- Sch-Lbl-Disjunction: union of the filtered sets.
example : labelFilterNodeSchemas testSchemaFull (.disj (.atom "Person") (.atom "Project"))
    = [personSchema, projectSchema] := by native_decide
-- Sch-Lbl-Empty: no label expression returns the full schema set.
example : resolveNodeSchemas testSchemaFull none
    = [personSchema, projectSchema] := by native_decide

-- Sch-Prp-Atom: retain schemas whose property signature covers the constraint.
example : filterNodeSchemasByPropCompat [personSchema, projectSchema]
    [("projectID", .int)] = [projectSchema] := by native_decide

-- Definition 2.3: property-map conformance requires agreeing key sets
-- with matching scalar sorts.
example : propMapConformsSchema [("name", .ofString "Atlas"), ("projectID", .ofInt 451)]
    [("name", .string), ("projectID", .int)] = true := by native_decide
example : propMapConformsSchema [("name", .ofString "Atlas")]
    [("name", .string), ("projectID", .int)] = false := by native_decide

/-- A closed typing context over the test graph and full schema set. -/
def filterCtx : TypingCtx :=
  { catalog := [("t", testGraph)], schemaMap := [("t", testSchemaFull)], graphSite := "t" }

-- Refine-Closed: theta_D endpoint filtering prunes the unlabeled target of
-- a KNOWS step down to the Person schema.
example : ((inferPattern filterCtx .outside
    (.edge { var := "a", labels := some (.atom "Person") }
            { var := "r", labels := some (.atom "KNOWS") } .right
            { var := "b" })).map (fun Gv => Gv.1.lookup "b"))
    = some (some (GSort.nodeRefinedOf "t" [personSchema])) := by native_decide

-- Refine-Closed-Fail: KNOWS cannot end at a Project; the endpoint set is
-- empty and all three step variables collapse to empty formers.
example : ((inferPattern filterCtx .outside
    (.edge { var := "a", labels := some (.atom "Person") }
            { var := "r", labels := some (.atom "KNOWS") } .right
            { var := "b", labels := some (.atom "Project") })).map
      (fun Gv => Gv.1.lookup "r"))
    = some (some (GSort.edgeEmpty "t")) := by native_decide

-- Refine-Closed-Empty: an unsatisfiable source atom (no Robot schema)
-- already carries the empty former, and the step propagates it.
example : ((inferPattern filterCtx .outside
    (.edge { var := "a", labels := some (.atom "Robot") }
            { var := "r", labels := some (.atom "KNOWS") } .right
            { var := "b" })).map (fun Gv => Gv.1.lookup "b"))
    = some (some (GSort.nodeEmpty "t")) := by native_decide

end SchemaFilterTests

end MGQL.Test
