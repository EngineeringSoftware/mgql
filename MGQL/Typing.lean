/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Typing.lean -- Complete typing judgments

  Reference: Paper Sections 3.5, 4.1, 4.2, and Appendix B

  Changes from v3:
  - thetaD now takes 3 schemas (source node, edge, target node) per paper theta_D(zeta1, xi2, zeta3)
  - RefinementTyping takes 3 record schemas (Gamma1, Gamma2, Gamma3) and 3 variable names (v1, r2, v3)
    per paper: Sigma; G; Gamma1; Gamma2; Gamma3 |-_REF v1, r2, v3, D : Gamma4
  - PatternTyping.patEdge types all 3 atoms (source node, edge, target node) and passes to 3-way refinement
  - PatternTyping.patStep similarly uses 3-way refinement
-/
import MGQL.Sorts
import MGQL.Syntax
import MGQL.Schema
import MGQL.RecordSchema
import MGQL.Subtyping

namespace MGQL

/- ## Typing Context: Sigma = (C, Upsilon, G) -/

structure TypingCtx where
  catalog   : Catalog
  schemaMap : SchemaMap
  graphSite : GraphSite

/- ## Reference Context and Aggregation Depth (Paper Section 4, Appendix B) -/

inductive RefCtx where
  | singleton  -- 1
  | group      -- star
  deriving DecidableEq, Repr

inductive AggDepth where
  | zero   -- aggregation permitted
  | one    -- inside an aggregate
  deriving DecidableEq, Repr

def AggDepth.incr : AggDepth -> AggDepth
  | .zero => .one
  | .one  => .one

/- ## Reference Mode (Paper Section 4.1: the pattern judgment tracks
  diamond in {1, star})
  outside = singleton reference (1)
  inside = group reference (star) -/

inductive QuantDepth where
  | outside   -- 0: singleton reference
  | inside    -- 1: inside quantifier (star), types lifted to List
  deriving DecidableEq, Repr

/- ## Variable Reference Set (omega) -/

abbrev VarSet := List Name

namespace VarSet

def empty : VarSet := []
def single (x : Name) : VarSet := [x]
def union (s1 s2 : VarSet) : VarSet :=
  s1 ++ s2.filter (fun x => !s1.any (fun y => y == x))
def mem (s : VarSet) (x : Name) : Bool :=
  s.any (fun y => y == x)
def size (s : VarSet) : Nat := s.length
def subset (s1 s2 : VarSet) : Bool :=
  s1.all (fun x => s2.any (fun y => y == x))

end VarSet

/- ============================================================
    Label Expression Typing (Paper Section 4.1, Sch-Lbl-* rules)
    box |-_L l =d> box'
    ============================================================ -/
/- Suppose there are 4 recordingSchemas, label of A:["Person", "Employee"]
B:["Person", "Customer"] C:["Company"] D:["Animal", "Dog"]
if query: MATCH (n:Person) RETURN n.name, then it match with .atom "Person",
so it will filter out C, D, and return [A B]

MATCH (n:Person|Company) RETURN n
.disj "Person" "Company"
return [A,B,C]

MATCH (n:Person&Employee) RETURN n.salary
.conj "Person" "Employee"
return A

MATCH (n:!Person) RETURN n
.neg "Person"
return [C D]

 -/
def labelFilterNodeSchemas (Psi : GraphSchemaFull) : LabelExpr -> List NodeSchemaFull
  | .atom l     => Psi.nodeSchemas.filter (fun ns => ns.labels.any (fun x => x == l))
  | .wildcard   => Psi.nodeSchemas.filter (fun ns => !ns.labels.isEmpty)
  | .neg l      =>
    let matched := labelFilterNodeSchemas Psi l
    Psi.nodeSchemas.filter (fun ns => !matched.any (fun m => m.labels == ns.labels))
  | .conj l1 l2 =>
    let s1 := labelFilterNodeSchemas Psi l1
    let s2 := labelFilterNodeSchemas Psi l2
    s1.filter (fun ns => s2.any (fun ns' => ns.labels == ns'.labels))
  | .disj l1 l2 =>
    let s1 := labelFilterNodeSchemas Psi l1
    let s2 := labelFilterNodeSchemas Psi l2
    s1 ++ s2.filter (fun ns => !s1.any (fun ns' => ns.labels == ns'.labels))

def labelFilterEdgeSchemas (Psi : GraphSchemaFull) : LabelExpr -> List EdgeSchemaFull
  | .atom l     => Psi.edgeSchemas.filter (fun es => es.labels.any (fun x => x == l))
  | .wildcard   => Psi.edgeSchemas.filter (fun es => !es.labels.isEmpty)
  | .neg l      =>
    let matched := labelFilterEdgeSchemas Psi l
    Psi.edgeSchemas.filter (fun es => !matched.any (fun m => m.labels == es.labels))
  | .conj l1 l2 =>
    let s1 := labelFilterEdgeSchemas Psi l1
    let s2 := labelFilterEdgeSchemas Psi l2
    s1.filter (fun es => s2.any (fun es' => es.labels == es'.labels))
  | .disj l1 l2 =>
    let s1 := labelFilterEdgeSchemas Psi l1
    let s2 := labelFilterEdgeSchemas Psi l2
    s1 ++ s2.filter (fun es => !s1.any (fun es' => es.labels == es'.labels))

/-- Sch-Lbl-Empty: no label expression returns all schemas -/

/- MATCH (n) -> labels will be none
MATCH (n:Person) -> labels will be some l, l is person -/
def resolveNodeSchemas (Psi : GraphSchemaFull) (labels : Option LabelExpr) :
    List NodeSchemaFull :=
  match labels with
  | none   => Psi.nodeSchemas
  | some l => labelFilterNodeSchemas Psi l

def resolveEdgeSchemas (Psi : GraphSchemaFull) (labels : Option LabelExpr) :
    List EdgeSchemaFull :=
  match labels with
  | none   => Psi.edgeSchemas
  | some l => labelFilterEdgeSchemas Psi l

/-- Set equality of two label lists (order-insensitive), matching how
    `nodeConformsSchema`/`edgeConformsSchema` compare label sets. -/
def labelSetEq (l1 l2 : List Name) : Bool :=
  l1.length == l2.length &&
  l1.all (fun x => l2.any (fun y => y == x)) &&
  l2.all (fun x => l1.any (fun y => y == x))

/-- Schema-level reflection of the runtime endpoint predicate `phiD`: does some
    edge schema in `sE2` admit an endpoint-compatible triple with a source-position
    schema from `sN1` and a target-position schema from `sN3` under direction
    `dir`? An edge schema is compatible *right* when it is directed and its
    declared src/dst endpoint label sets are realized in `sN1`/`sN3`, *left* when
    reversed, and *undirected* when either pairing is realized -- mirroring
    `phiD`'s seven direction cases. The `Refine-Closed-Fail` rule fires exactly
    when no such triple exists. -/
def endpointCompatTriple (sN1 : List NodeSchemaFull) (sE2 : List EdgeSchemaFull)
    (sN3 : List NodeSchemaFull) (dir : Direction) : Bool :=
  sE2.any fun es =>
    let cR := es.isDirected &&
      sN1.any (fun n => labelSetEq n.labels es.srcSchema.labels) &&
      sN3.any (fun n => labelSetEq n.labels es.dstSchema.labels)
    let cL := es.isDirected &&
      sN1.any (fun n => labelSetEq n.labels es.dstSchema.labels) &&
      sN3.any (fun n => labelSetEq n.labels es.srcSchema.labels)
    let cU := !es.isDirected &&
      ((sN1.any (fun n => labelSetEq n.labels es.srcSchema.labels) &&
        sN3.any (fun n => labelSetEq n.labels es.dstSchema.labels)) ||
       (sN1.any (fun n => labelSetEq n.labels es.dstSchema.labels) &&
        sN3.any (fun n => labelSetEq n.labels es.srcSchema.labels)))
    match dir with
    | .right             => cR
    | .left              => cL
    | .anyDirected       => cR || cL
    | .undirected        => cU
    | .rightOrUndirected => cR || cU
    | .leftOrUndirected  => cL || cU
    | .any               => cR || cL || cU

/-- Endpoint compatibility of a single schema triple `(z1, es, z3)` under
    direction `dir` -- the per-triple kernel of the endpoint-compatible set `S`
    (Paper Section 4.1). `z1`/`z3` are candidate source/target node schemas and
    `es` the candidate edge schema; the triple is compatible when `es`'s declared
    endpoint label sets are realized by `z1`/`z3` consistently with `dir`. -/
def tripleCompat (z1 : NodeSchemaFull) (es : EdgeSchemaFull) (z3 : NodeSchemaFull)
    (dir : Direction) : Bool :=
  let cR := es.isDirected && labelSetEq z1.labels es.srcSchema.labels
              && labelSetEq z3.labels es.dstSchema.labels
  let cL := es.isDirected && labelSetEq z1.labels es.dstSchema.labels
              && labelSetEq z3.labels es.srcSchema.labels
  let cU := !es.isDirected &&
    ((labelSetEq z1.labels es.srcSchema.labels && labelSetEq z3.labels es.dstSchema.labels) ||
     (labelSetEq z1.labels es.dstSchema.labels && labelSetEq z3.labels es.srcSchema.labels))
  match dir with
  | .right             => cR
  | .left              => cL
  | .anyDirected       => cR || cL
  | .undirected        => cU
  | .rightOrUndirected => cR || cU
  | .leftOrUndirected  => cL || cU
  | .any               => cR || cL || cU

/-- `pi_1(S)`: the source-node schemas in `sN1` that participate in a compatible
    triple with some edge in `sE2` and target in `sN3`. The refined source set the
    `Refine-Closed` rule assigns (Paper Section 4.1, `refineType` over `pi_1(S)`). -/
def refineSrcByCompat (sN1 : List NodeSchemaFull) (sE2 : List EdgeSchemaFull)
    (sN3 : List NodeSchemaFull) (dir : Direction) : List NodeSchemaFull :=
  sN1.filter (fun z1 => sE2.any (fun es => sN3.any (fun z3 => tripleCompat z1 es z3 dir)))

/-- `pi_2(S)`: the edge schemas in `sE2` participating in a compatible triple. -/
def refineEdgeByCompat (sN1 : List NodeSchemaFull) (sE2 : List EdgeSchemaFull)
    (sN3 : List NodeSchemaFull) (dir : Direction) : List EdgeSchemaFull :=
  sE2.filter (fun es => sN1.any (fun z1 => sN3.any (fun z3 => tripleCompat z1 es z3 dir)))

/-- `pi_3(S)`: the target-node schemas in `sN3` participating in a compatible triple. -/
def refineDstByCompat (sN1 : List NodeSchemaFull) (sE2 : List EdgeSchemaFull)
    (sN3 : List NodeSchemaFull) (dir : Direction) : List NodeSchemaFull :=
  sN3.filter (fun z3 => sN1.any (fun z1 => sE2.any (fun es => tripleCompat z1 es z3 dir)))

-- ============================================================
--  Property-Type Helper (Paper Appendix B)
-- ============================================================

/- a variable may have multiple identity, how to decide n.age if n is unsure
after the return from above functions, [Person, Company]
 -/
def propTypeOfNodeSchemas (schemas : List NodeSchemaFull) (k : Name) : GSort :=
  match schemas with
  | [] => GSort.anyScalarN  -- H-PropType-Empty
  | [ns] =>
    match ns.propSchema.lookup k with
    | some b => GSort.mk (.single (.scalar b)) .nullable  -- H-PropType-Schema: Phi(k)?
    | none => GSort.mk .nullType .val                      -- H-PropType-Schema-Fail: ?
  | ns :: rest =>
    let t1 := match ns.propSchema.lookup k with
      | some b => GSort.mk (.single (.scalar b)) .nullable
      | none => GSort.mk .nullType .val
    let t2 := propTypeOfNodeSchemas rest k
    RecordSchema.sortUnion t1 t2  -- H-PropType-Schemas

def propTypeOfEdgeSchemas (schemas : List EdgeSchemaFull) (k : Name) : GSort :=
  match schemas with
  | [] => GSort.anyScalarN
  | [es] =>
    match es.propSchema.lookup k with
    | some b => GSort.mk (.single (.scalar b)) .nullable  -- H-PropType-Schema: Phi(k)?
    | none => GSort.mk .nullType .val
  | es :: rest =>
    let t1 := match es.propSchema.lookup k with
      | some b => GSort.mk (.single (.scalar b)) .nullable
      | none => GSort.mk .nullType .val
    let t2 := propTypeOfEdgeSchemas rest k
    RecordSchema.sortUnion t1 t2

/- ============================================================
    Property Constraint Typing (Paper Section 4.1: Prp-Empty, Prp-Atom, Prp-Insert)
    |-_Prp Pi |= Phi_Pi
    Derives a PropSchema from property constraints.
    ============================================================ -/
inductive PropConstraintTyping : List PropConstraint -> PropSchema -> Prop where

  /-- Prp-Empty: empty constraint list produces empty schema -/
  | empty :
      PropConstraintTyping [] []

  /-- Prp-Atom: single constraint {k |-> c} |= [k |-> tau] where c in U_tau -/
  /- {age: 18} -/
  | atom (k : Name) (c : Literal) (tau : BaseSort)
      (hSort : literalBaseSort c = tau) :
      PropConstraintTyping [{ key := k, val := c }] [(k, tau)]

  /-- Prp-Insert: extend with fresh key -/
  /- {name: "Alice"} -/
  | insert (k : Name) (c : Literal) (tau : BaseSort)
      (rest : List PropConstraint) (PhiRest : PropSchema)
      (hSort : literalBaseSort c = tau)
      (hFresh : !PhiRest.keys.any (fun x => x == k))    -- no other "name" appears
      (hRest : PropConstraintTyping rest PhiRest) :
      PropConstraintTyping ({ key := k, val := c } :: rest) ((k, tau) :: PhiRest)

/- ============================================================
    Expression Typing: Sigma; G; Gamma; X |-^box_hat theta : tau -| X'
    ============================================================ -/

/-! Expression and predicate typing are mutually inductive, mirroring the
    mutual grammar: the `pred` rule embeds a well-typed predicate as a
    boolean value expression (Paper Fig 2: `e ::= ... | phi`), and the
    predicate atoms type their expression operands. -/
mutual

inductive ExprTyping :
    TypingCtx -> RecordSchema -> AggDepth -> RefCtx
    -> Expr -> GSort -> VarSet -> Prop where

  /-- E-Const: c : tau, omega' = empty -/
  | constInt (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx)
      (n : Int) :
      ExprTyping ctx Ctx box hat (.const (.int n)) GSort.int VarSet.empty

  | constString (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx)
      (s : String) :
      ExprTyping ctx Ctx box hat (.const (.string s)) GSort.string VarSet.empty

  | constBool (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx)
      (b : Bool) :
      ExprTyping ctx Ctx box hat (.const (.bool b)) GSort.bool VarSet.empty

  /-- E-Null: Null : ? (Paper Appendix B: formal rule assigns null type ?) -/
  | constNull (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx)
      :
      ExprTyping ctx Ctx box hat .null GSort.nullSort VarSet.empty

  /-- E-Variable: x in dom(Gamma) ==> x : Gamma(x), omega' = {x} -/
  | var (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx)
      (x : Name) (tau : GSort)
      (hLookup : Ctx.lookup x = some tau) :
      ExprTyping ctx Ctx box hat (.var x) tau (VarSet.single x)

  /-- E-Arithmetic: theta1 oplus theta2 : Z? -/
  /- n.age + 5 -/
  | arithOp (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx)
      (op : ArithOp) (e1 e2 : Expr) (t1 t2 : GSort)
      (omega1 omega2 : VarSet)
      (h1 : ExprTyping ctx Ctx box hat e1 t1 omega1)
      (h2 : ExprTyping ctx Ctx box hat e2 t2 omega2)
      (hc1 : DynRefine t1 GSort.intN)
      (hc2 : DynRefine t2 GSort.intN) :
      ExprTyping ctx Ctx box hat (.arithOp op e1 e2) GSort.intN
        (VarSet.union omega1 omega2)

  /- ### Property Access (Paper Appendix B) -/

  /-- E-PropAccess: x.k for open graphs: (Z union S union B)? -/
  | propAccessOpen (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx)
      (x k : Name) (tx : GSort)
      (hLookup : Ctx.lookup x = some tx)
      (hRefine : DynRefine (tx.componentType) (GSort.nodeOf ctx.graphSite)
               \/ DynRefine (tx.componentType) (GSort.edgeOf ctx.graphSite))
      (hOpen : ctx.schemaMap.isClosed ctx.graphSite = false) :
      ExprTyping ctx Ctx box hat (.propAccess x k) GSort.anyScalarN
        (VarSet.single x)

  /-- E-PropAccess-Schema: x.k for closed graphs with schema-refined type -/
  | propAccessSchema (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx)
      (x k : Name) (tx resultTy : GSort)
      (nodeSchemas : List NodeSchemaFull) (edgeSchemas : List EdgeSchemaFull)
      (hLookup : Ctx.lookup x = some tx)
      (hClosed : ctx.schemaMap.isClosed ctx.graphSite = true)
      (hRefine : (tx.componentType = GSort.nodeRefinedOf ctx.graphSite nodeSchemas
                   /\ resultTy = propTypeOfNodeSchemas nodeSchemas k)
               \/ (tx.componentType = GSort.edgeRefinedOf ctx.graphSite edgeSchemas
                   /\ resultTy = propTypeOfEdgeSchemas edgeSchemas k)) :
      ExprTyping ctx Ctx box hat (.propAccess x k) resultTy
        (VarSet.single x)

  /-- E-PropAccess-List-Open: x.k for open graphs where x has list type
      (Paper Appendix B: handles grouped variables from quantified patterns) -/
  | propAccessListOpen (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx)
      (x k : Name) (tx : GSort)
      (hLookup : Ctx.lookup x = some tx)
      (hIsList : tx.isList = true)
      (hRefine : DynRefine (tx.componentType) (GSort.nodeOf ctx.graphSite)
               \/ DynRefine (tx.componentType) (GSort.edgeOf ctx.graphSite))
      (hOpen : ctx.schemaMap.isClosed ctx.graphSite = false) :
      ExprTyping ctx Ctx box hat (.propAccess x k) GSort.anyScalarN
        (VarSet.single x)

  /-- E-PropAccess-List-Closed: x.k for closed graphs where x has list type
      (Paper Appendix B: handles grouped variables with schema-refined list types) -/
  | propAccessListClosed (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx)
      (x k : Name) (tx resultTy : GSort)
      (nodeSchemas : List NodeSchemaFull) (edgeSchemas : List EdgeSchemaFull)
      (hLookup : Ctx.lookup x = some tx)
      (hIsList : tx.isList = true)
      (hClosed : ctx.schemaMap.isClosed ctx.graphSite = true)
      (hRefine : (tx.componentType = GSort.nodeRefinedOf ctx.graphSite nodeSchemas
                   /\ resultTy = propTypeOfNodeSchemas nodeSchemas k)
               \/ (tx.componentType = GSort.edgeRefinedOf ctx.graphSite edgeSchemas
                   /\ resultTy = propTypeOfEdgeSchemas edgeSchemas k)) :
      ExprTyping ctx Ctx box hat (.propAccess x k) resultTy
        (VarSet.single x)

  /- ### Aggregation (Paper Appendix B) -/

  /-- E-Count-Singleton, for any aggregate qualifier -/
  | countSingleton (ctx : TypingCtx) (Ctx : RecordSchema)
      (qual : AggQualifier) (e : Expr) (x : Name) (tau1 : GSort) (elemSort : GSort)
      (hExpr : ExprTyping ctx Ctx .zero .singleton e tau1 (VarSet.single x))
      (hListType : Ctx.lookup x = some elemSort)
      (hIsList : elemSort.isList = true) :
      ExprTyping ctx Ctx .one .singleton
        (.agg .count qual e) GSort.int (VarSet.single x)

  /-- E-Agg-Singleton: Sum/Max/Min in singleton context -/
  | aggSingleton (ctx : TypingCtx) (Ctx : RecordSchema)
      (op : AggOp) (qual : AggQualifier) (e : Expr) (x : Name) (tau1 : GSort)
      (elemSort innerTy : GSort)
      (hOp : op = .sum \/ op = .max \/ op = .min)
      (hExpr : ExprTyping ctx Ctx .zero .singleton e tau1 (VarSet.single x))
      (hListType : Ctx.lookup x = some elemSort)
      (hElem : elemSort.elemSort? = some innerTy)
      (hRefine : DynRefine innerTy GSort.intN) :
      ExprTyping ctx Ctx .one .singleton
        (.agg op qual e) GSort.intN (VarSet.single x)

  /-- E-Count-Group -/
  | countGroup (ctx : TypingCtx) (Ctx : RecordSchema)
      (qual : AggQualifier) (e : Expr) (tau1 : GSort) (omega1 : VarSet)
      (hExpr : ExprTyping ctx Ctx .zero .group e tau1 omega1)
      (hSubset : omega1.subset Ctx.dom = true) :
      ExprTyping ctx Ctx .one .group
        (.agg .count qual e) GSort.int omega1

  /-- E-Agg-Group: Sum/Max/Min in group context -/
  | aggGroup (ctx : TypingCtx) (Ctx : RecordSchema)
      (op : AggOp) (qual : AggQualifier) (e : Expr) (tau1 : GSort) (omega1 : VarSet)
      (hOp : op = .sum \/ op = .max \/ op = .min)
      (hExpr : ExprTyping ctx Ctx .zero .group e tau1 omega1)
      (hSubset : omega1.subset Ctx.dom = true) :
      ExprTyping ctx Ctx .one .group
        (.agg op qual e) GSort.intN omega1

  /-- E-Pred: a well-typed predicate is a boolean value expression
      (Paper Fig 2: e ::= ... | phi; the FTy rules give phi its Bool/Bool?
      type, reflected here verbatim). -/
  | pred (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx)
      (phi : Pred) (t : GSort) (omega1 : VarSet)
      (h : PredTyping ctx Ctx box hat phi t omega1) :
      ExprTyping ctx Ctx box hat (.pred phi) t omega1

  /-- Subsumption (Paper: tau1 <: tau2) -/
  | subsume (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx)
      (e : Expr) (ty1 ty2 : GSort) (omega' : VarSet)
      (h : ExprTyping ctx Ctx box hat e ty1 omega')
      (hSub : Subtype ty1 ty2) :
      ExprTyping ctx Ctx box hat e ty2 omega'

/- ============================================================
    Predicate Typing
    ============================================================ -/

inductive PredTyping :
    TypingCtx -> RecordSchema -> AggDepth -> RefCtx
    -> Pred -> GSort -> VarSet -> Prop where

  | true (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx)
      :
      PredTyping ctx Ctx box hat .true GSort.bool VarSet.empty

  | false (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx)
      :
      PredTyping ctx Ctx box hat .false GSort.bool VarSet.empty

  /-- E-Relational: theta1 cmp theta2 : B? -/
  | relOp (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx)
      (op : RelOp) (e1 e2 : Expr) (t1 t2 : GSort)
      (omega1 omega2 : VarSet)
      (h1 : ExprTyping ctx Ctx box hat e1 t1 omega1)
      (h2 : ExprTyping ctx Ctx box hat e2 t2 omega2)
      (hc1 : DynRefine t1 GSort.intN)
      (hc2 : DynRefine t2 GSort.intN) :
      PredTyping ctx Ctx box hat (.relOp op e1 e2) GSort.boolN
        (VarSet.union omega1 omega2)

  /-- E-Negation: the operand dynamically refines to Bool? -/
  | not (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx)
      (phi : Pred) (t : GSort) (omega1 : VarSet)
      (h : PredTyping ctx Ctx box hat phi t omega1)
      (hSub : DynRefine t GSort.boolN) :
      PredTyping ctx Ctx box hat (.not phi) GSort.boolN omega1

  /-- E-Logical-Binary: and -/
  | and (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx)
      (p1 p2 : Pred) (t1 t2 : GSort) (omega1 omega2 : VarSet)
      (h1 : PredTyping ctx Ctx box hat p1 t1 omega1)
      (h2 : PredTyping ctx Ctx box hat p2 t2 omega2)
      (hSub1 : DynRefine t1 GSort.boolN)
      (hSub2 : DynRefine t2 GSort.boolN) :
      PredTyping ctx Ctx box hat (.and p1 p2) GSort.boolN
        (VarSet.union omega1 omega2)

  /-- E-Logical-Binary: or -/
  | or (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx)
      (p1 p2 : Pred) (t1 t2 : GSort) (omega1 omega2 : VarSet)
      (h1 : PredTyping ctx Ctx box hat p1 t1 omega1)
      (h2 : PredTyping ctx Ctx box hat p2 t2 omega2)
      (hSub1 : DynRefine t1 GSort.boolN)
      (hSub2 : DynRefine t2 GSort.boolN) :
      PredTyping ctx Ctx box hat (.or p1 p2) GSort.boolN
        (VarSet.union omega1 omega2)

  /-- E-IsNull: theta isNull : B (non-nullable) -/
  | isNull (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx)
      (e : Expr) (t : GSort) (omega1 : VarSet)
      (h : ExprTyping ctx Ctx box hat e t omega1) :
      PredTyping ctx Ctx box hat (.isNull e) GSort.bool omega1

end

set_option maxHeartbeats 1600000 in
/-- Induction over `ExprTyping` treating the embedded predicate typing as an
    opaque premise (second motive trivially `True`). The `induction` tactic
    does not support mutual inductives; this restores it for the common case
    where the predicate-side derivation needs no inductive hypothesis (all
    soundness obligations for embedded predicates discharge by value shape:
    the result is a boolean or null). `ctx` and `Ctx` are family parameters
    (fixed across every premise), mirroring the underlying recursor. -/
def ExprTyping.inductionOpaque
    {ctx : TypingCtx} {Ctx : RecordSchema}
    {motive : ∀ (box : AggDepth) (hat : RefCtx)
        (e : Expr) (t : GSort) (omega' : VarSet),
        ExprTyping ctx Ctx box hat e t omega' → Prop}
    {box : AggDepth} {hat : RefCtx}
    {e : Expr} {t : GSort} {omega' : VarSet}
    (h : ExprTyping ctx Ctx box hat e t omega')
    (constInt : ∀ box hat (n : Int),
        motive _ _ _ _ _ (.constInt ctx Ctx box hat n))
    (constString : ∀ box hat (s : String),
        motive _ _ _ _ _ (.constString ctx Ctx box hat s))
    (constBool : ∀ box hat (b : Bool),
        motive _ _ _ _ _ (.constBool ctx Ctx box hat b))
    (constNull : ∀ box hat,
        motive _ _ _ _ _ (.constNull ctx Ctx box hat))
    (var : ∀ box hat (x : Name) (tau : GSort)
        (hLookup : RecordSchema.lookup Ctx x = some tau),
        motive _ _ _ _ _ (.var ctx Ctx box hat x tau hLookup))
    (arithOp : ∀ box hat (op : ArithOp) (e1 e2 : Expr) (t1 t2 : GSort)
        (omega1 omega2 : VarSet)
        (h1 : ExprTyping ctx Ctx box hat e1 t1 omega1)
        (h2 : ExprTyping ctx Ctx box hat e2 t2 omega2)
        (hc1 : DynRefine t1 GSort.intN) (hc2 : DynRefine t2 GSort.intN),
        motive _ _ _ _ _ h1 → motive _ _ _ _ _ h2 →
        motive _ _ _ _ _ (.arithOp ctx Ctx box hat op e1 e2 t1 t2 omega1 omega2 h1 h2 hc1 hc2))
    (propAccessOpen : ∀ box hat (x k : Name) (tx : GSort)
        (hLookup : RecordSchema.lookup Ctx x = some tx)
        (hRefine : DynRefine tx.componentType (GSort.nodeOf ctx.graphSite)
                 ∨ DynRefine tx.componentType (GSort.edgeOf ctx.graphSite))
        (hOpen : SchemaMap.isClosed ctx.schemaMap ctx.graphSite = false),
        motive _ _ _ _ _ (.propAccessOpen ctx Ctx box hat x k tx hLookup hRefine hOpen))
    (propAccessSchema : ∀ box hat (x k : Name) (tx resultTy : GSort)
        (nodeSchemas : List NodeSchemaFull) (edgeSchemas : List EdgeSchemaFull)
        (hLookup : RecordSchema.lookup Ctx x = some tx)
        (hClosed : SchemaMap.isClosed ctx.schemaMap ctx.graphSite = true)
        (hRefine : (tx.componentType = GSort.nodeRefinedOf ctx.graphSite nodeSchemas
                     ∧ resultTy = propTypeOfNodeSchemas nodeSchemas k)
                 ∨ (tx.componentType = GSort.edgeRefinedOf ctx.graphSite edgeSchemas
                     ∧ resultTy = propTypeOfEdgeSchemas edgeSchemas k)),
        motive _ _ _ _ _ (.propAccessSchema ctx Ctx box hat x k tx resultTy nodeSchemas edgeSchemas hLookup hClosed hRefine))
    (propAccessListOpen : ∀ box hat (x k : Name) (tx : GSort)
        (hLookup : RecordSchema.lookup Ctx x = some tx)
        (hIsList : tx.isList = true)
        (hRefine : DynRefine tx.componentType (GSort.nodeOf ctx.graphSite)
                 ∨ DynRefine tx.componentType (GSort.edgeOf ctx.graphSite))
        (hOpen : SchemaMap.isClosed ctx.schemaMap ctx.graphSite = false),
        motive _ _ _ _ _ (.propAccessListOpen ctx Ctx box hat x k tx hLookup hIsList hRefine hOpen))
    (propAccessListClosed : ∀ box hat (x k : Name) (tx resultTy : GSort)
        (nodeSchemas : List NodeSchemaFull) (edgeSchemas : List EdgeSchemaFull)
        (hLookup : RecordSchema.lookup Ctx x = some tx)
        (hIsList : tx.isList = true)
        (hClosed : SchemaMap.isClosed ctx.schemaMap ctx.graphSite = true)
        (hRefine : (tx.componentType = GSort.nodeRefinedOf ctx.graphSite nodeSchemas
                     ∧ resultTy = propTypeOfNodeSchemas nodeSchemas k)
                 ∨ (tx.componentType = GSort.edgeRefinedOf ctx.graphSite edgeSchemas
                     ∧ resultTy = propTypeOfEdgeSchemas edgeSchemas k)),
        motive _ _ _ _ _ (.propAccessListClosed ctx Ctx box hat x k tx resultTy nodeSchemas edgeSchemas hLookup hIsList hClosed hRefine))
    (countSingleton : ∀ (qual : AggQualifier) (e : Expr) (x : Name)
        (tau1 : GSort) (elemSort : GSort)
        (hExpr : ExprTyping ctx Ctx .zero .singleton e tau1 (VarSet.single x))
        (hListType : RecordSchema.lookup Ctx x = some elemSort)
        (hIsList : elemSort.isList = true),
        motive _ _ _ _ _ hExpr →
        motive _ _ _ _ _ (.countSingleton ctx Ctx qual e x tau1 elemSort hExpr hListType hIsList))
    (aggSingleton : ∀ (op : AggOp) (qual : AggQualifier) (e : Expr) (x : Name)
        (tau1 : GSort) (elemSort innerTy : GSort)
        (hOp : op = .sum ∨ op = .max ∨ op = .min)
        (hExpr : ExprTyping ctx Ctx .zero .singleton e tau1 (VarSet.single x))
        (hListType : RecordSchema.lookup Ctx x = some elemSort)
        (hElem : elemSort.elemSort? = some innerTy)
        (hRefine : DynRefine innerTy GSort.intN),
        motive _ _ _ _ _ hExpr →
        motive _ _ _ _ _ (.aggSingleton ctx Ctx op qual e x tau1 elemSort innerTy hOp hExpr hListType hElem hRefine))
    (countGroup : ∀ (qual : AggQualifier) (e : Expr) (tau1 : GSort) (omega1 : VarSet)
        (hExpr : ExprTyping ctx Ctx .zero .group e tau1 omega1)
        (hSubset : VarSet.subset omega1 Ctx.dom = true),
        motive _ _ _ _ _ hExpr →
        motive _ _ _ _ _ (.countGroup ctx Ctx qual e tau1 omega1 hExpr hSubset))
    (aggGroup : ∀ (op : AggOp) (qual : AggQualifier) (e : Expr) (tau1 : GSort)
        (omega1 : VarSet)
        (hOp : op = .sum ∨ op = .max ∨ op = .min)
        (hExpr : ExprTyping ctx Ctx .zero .group e tau1 omega1)
        (hSubset : VarSet.subset omega1 Ctx.dom = true),
        motive _ _ _ _ _ hExpr →
        motive _ _ _ _ _ (.aggGroup ctx Ctx op qual e tau1 omega1 hOp hExpr hSubset))
    (pred : ∀ box hat (phi : Pred) (t : GSort) (omega1 : VarSet)
        (h : PredTyping ctx Ctx box hat phi t omega1),
        motive _ _ _ _ _ (.pred ctx Ctx box hat phi t omega1 h))
    (subsume : ∀ box hat (e : Expr) (ty1 ty2 : GSort) (omega' : VarSet)
        (h : ExprTyping ctx Ctx box hat e ty1 omega')
        (hSub : Subtype ty1 ty2),
        motive _ _ _ _ _ h →
        motive _ _ _ _ _ (.subsume ctx Ctx box hat e ty1 ty2 omega' h hSub)) :
    motive box hat e t omega' h :=
  ExprTyping.rec (motive_1 := motive)
    (motive_2 := fun _ _ _ _ _ _ => True)
    constInt constString constBool constNull var arithOp propAccessOpen propAccessSchema
    propAccessListOpen propAccessListClosed countSingleton aggSingleton countGroup aggGroup
    (fun box hat phi t omega1 hp _ => pred box hat phi t omega1 hp)
    subsume
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    h

/- ============================================================
    Direction Helpers (Paper Section 4.1, Figure 4)
    ============================================================ -/

/-- Direction reversal (Paper Section 4.1) -/
def reverseDir : Direction -> Direction
  | .right              => .left
  | .left               => .right
  | .anyDirected        => .anyDirected
  | .undirected         => .undirected
  | .rightOrUndirected  => .leftOrUndirected
  | .leftOrUndirected   => .rightOrUndirected
  | .any                => .any

/-- thetaD(zeta1, xi2, zeta3): endpoint direction predicate (Paper Section 4.1)
  Takes source node schema zeta1, edge schema xi2, target node schema zeta3.
  Handles all 7 direction variants from Figure 2.
  pi3(xi) = srcSchema, pi4(xi) = dstSchema, pi5(xi) = isDirected -/
def thetaD (dir : Direction) (ns1 : NodeSchemaFull) (es : EdgeSchemaFull)
    (ns3 : NodeSchemaFull) : Bool :=
  -- theta_right-arrow: zeta1 = pi3(xi2) /\ zeta3 = pi4(xi2) /\ directed
  let thetaRight :=
    es.isDirected &&
    ns1 == es.srcSchema &&
    ns3 == es.dstSchema
  -- theta_left-arrow: zeta1 = pi4(xi2) /\ zeta3 = pi3(xi2) /\ directed
  let thetaLeft :=
    es.isDirected &&
    ns1 == es.dstSchema &&
    ns3 == es.srcSchema
  -- theta_tilde: {zeta1, zeta3} subset {{pi3(xi2), pi4(xi2)}} /\ undirected
  let thetaUndirected :=
    !es.isDirected &&
    (((ns1 == es.srcSchema && ns3 == es.dstSchema) ||
      (ns1 == es.dstSchema && ns3 == es.srcSchema)))
  match dir with
  | .right              => thetaRight
  | .left               => thetaLeft
  | .anyDirected        => thetaRight || thetaLeft
  | .undirected         => thetaUndirected
  | .rightOrUndirected  => thetaRight || thetaUndirected
  | .leftOrUndirected   => thetaLeft || thetaUndirected
  | .any                => thetaRight || thetaLeft || thetaUndirected

/- ============================================================
    Atom Typing: Sigma; G |-_A N/E : Gamma
    (Paper Section 4.1)
    Now with explicit schema filtering premises (Sch-Node/Sch-Edge).
    ============================================================ -/

inductive AtomInput where
  | node : NodeAtom -> AtomInput
  | edge : EdgeAtom -> AtomInput
  deriving Repr

/-- Note: Atom-Edge-Direction-Lift (Paper Section 4.1) is mechanized by construction:
    AtomInput.edge does not carry a Direction, so atom typing is automatically
    independent of the edge direction wrapper D. The direction is applied at the
    PatternTyping level (Pat-Edge, Pat-Step). -/
inductive AtomTyping : TypingCtx -> AtomInput -> RecordSchema -> Prop where

  /-- Atom-Node-Open: G not-in dom(Upsilon) ==> [v -> N<G>] -/
  | nodeOpen (ctx : TypingCtx)
      (v : Name) (labels : Option LabelExpr) (props : List PropConstraint)
      (hOpen : ctx.schemaMap.isClosed ctx.graphSite = false) :
      AtomTyping ctx
        (.node { var := v, labels := labels, props := props })
        (RecordSchema.mk [(v, GSort.nodeOf ctx.graphSite)])

  /-- Atom-Node-Closed: G in dom(Upsilon), Sch-Node filtering produces non-empty set
      ==> [v -> N<G, zeta_hat>] where zeta_hat = zeta_l intersect zeta_Prp
      The filtering result is used directly as the schema list in the type. -/
  | nodeClosed (ctx : TypingCtx)
      (v : Name) (labels : Option LabelExpr) (props : List PropConstraint)
      (Psi : GraphSchemaFull) (PhiPi : PropSchema)
      (zetaL zetaPrp zetaResult : List NodeSchemaFull)
      (hClosed : ctx.schemaMap.isClosed ctx.graphSite = true)
      (hSchema : ctx.schemaMap.lookup ctx.graphSite = some Psi)
      (hPrpTyping : PropConstraintTyping props PhiPi)
      (hLblFilter : zetaL = resolveNodeSchemas Psi labels)
      (hPrpFilter : zetaPrp = filterNodeSchemasByPropCompat zetaL PhiPi)
      (hResult : zetaResult = zetaPrp)
      (hNonEmpty : zetaResult.length > 0) :
      AtomTyping ctx
        (.node { var := v, labels := labels, props := props })
        (RecordSchema.mk [(v, GSort.nodeRefinedOf ctx.graphSite zetaResult)])

  /-- Atom-Node-Closed-Fail: filtering produces empty set
      ==> [v -> <N<G>>_bot] (empty type former) -/
  | nodeClosedFail (ctx : TypingCtx)
      (v : Name) (labels : Option LabelExpr) (props : List PropConstraint)
      (Psi : GraphSchemaFull) (PhiPi : PropSchema)
      (zetaL zetaPrp : List NodeSchemaFull)
      (hClosed : ctx.schemaMap.isClosed ctx.graphSite = true)
      (hSchema : ctx.schemaMap.lookup ctx.graphSite = some Psi)
      (hPrpTyping : PropConstraintTyping props PhiPi)
      (hLblFilter : zetaL = resolveNodeSchemas Psi labels)
      (hPrpFilter : zetaPrp = filterNodeSchemasByPropCompat zetaL PhiPi)
      (hEmpty : zetaPrp.length = 0) :
      AtomTyping ctx
        (.node { var := v, labels := labels, props := props })
        (RecordSchema.mk [(v, GSort.nodeEmpty ctx.graphSite)])

  /-- Atom-Edge-Open -/
  | edgeOpen (ctx : TypingCtx)
      (r : Name) (labels : Option LabelExpr) (props : List PropConstraint)
      (hOpen : ctx.schemaMap.isClosed ctx.graphSite = false) :
      AtomTyping ctx
        (.edge { var := r, labels := labels, props := props })
        (RecordSchema.mk [(r, GSort.edgeOf ctx.graphSite)])

  /-- Atom-Edge-Closed: schema filtering produces non-empty set
      The filtering result is used directly as the schema list in the type. -/
  | edgeClosed (ctx : TypingCtx)
      (r : Name) (labels : Option LabelExpr) (props : List PropConstraint)
      (Psi : GraphSchemaFull) (PhiPi : PropSchema)
      (xiL xiPrp xiResult : List EdgeSchemaFull)
      (hClosed : ctx.schemaMap.isClosed ctx.graphSite = true)
      (hSchema : ctx.schemaMap.lookup ctx.graphSite = some Psi)
      (hPrpTyping : PropConstraintTyping props PhiPi)
      (hLblFilter : xiL = resolveEdgeSchemas Psi labels)
      (hPrpFilter : xiPrp = filterEdgeSchemasByPropCompat xiL PhiPi)
      (hResult : xiResult = xiPrp)
      (hNonEmpty : xiResult.length > 0) :
      AtomTyping ctx
        (.edge { var := r, labels := labels, props := props })
        (RecordSchema.mk [(r, GSort.edgeRefinedOf ctx.graphSite xiResult)])

  /-- Atom-Edge-Closed-Fail -/
  | edgeClosedFail (ctx : TypingCtx)
      (r : Name) (labels : Option LabelExpr) (props : List PropConstraint)
      (Psi : GraphSchemaFull) (PhiPi : PropSchema)
      (xiL xiPrp : List EdgeSchemaFull)
      (hClosed : ctx.schemaMap.isClosed ctx.graphSite = true)
      (hSchema : ctx.schemaMap.lookup ctx.graphSite = some Psi)
      (hPrpTyping : PropConstraintTyping props PhiPi)
      (hLblFilter : xiL = resolveEdgeSchemas Psi labels)
      (hPrpFilter : xiPrp = filterEdgeSchemasByPropCompat xiL PhiPi)
      (hEmpty : xiPrp.length = 0) :
      AtomTyping ctx
        (.edge { var := r, labels := labels, props := props })
        (RecordSchema.mk [(r, GSort.edgeEmpty ctx.graphSite)])

/- ============================================================
    Refinement Typing (Paper Section 4.1)
    Sigma; G; Gamma1; Gamma2; Gamma3 |-_REF v1, r2, v3, D : Gamma4
    Gamma1 = left node, Gamma2 = edge, Gamma3 = right node
    ============================================================ -/

inductive RefinementTyping :
    TypingCtx -> RecordSchema -> RecordSchema -> RecordSchema
    -> Name -> Name -> Name -> Direction
    -> RecordSchema -> Prop where

  /-- Refine-Closed: endpoint compatibility filtering (Paper Section 4.1)
      S = { (zeta1, xi2, zeta3) in (zeta1_hat x xi2_hat x zeta3_hat) | thetaD(zeta1, xi2, zeta3) }
      zeta1' = pi1(S), xi2' = pi2(S), zeta3' = pi3(S) -/
  | closed (ctx : TypingCtx) (Gamma1 Gamma2 Gamma3 : RecordSchema)
      (v1 r2 v3 : Name) (dir : Direction)
      (sN1 : List NodeSchemaFull) (sE2 : List EdgeSchemaFull) (sN3 : List NodeSchemaFull)
      (sN1' : List NodeSchemaFull) (sE2' : List EdgeSchemaFull) (sN3' : List NodeSchemaFull)
      (hNode1 : Gamma1.lookup v1 = some (GSort.nodeRefinedOf ctx.graphSite sN1))
      (hEdge2 : Gamma2.lookup r2 = some (GSort.edgeRefinedOf ctx.graphSite sE2))
      (hNode3 : Gamma3.lookup v3 = some (GSort.nodeRefinedOf ctx.graphSite sN3))
      (hJoinCompat12 : Gamma1.joinCompatible Gamma2 = true)
      (hJoinCompat23 : Gamma2.joinCompatible Gamma3 = true)
      (hJoinCompat13 : Gamma1.joinCompatible Gamma3 = true)
      (hSrc' : sN1' = refineSrcByCompat sN1 sE2 sN3 dir)
      (hEdge' : sE2' = refineEdgeByCompat sN1 sE2 sN3 dir)
      (hDst' : sN3' = refineDstByCompat sN1 sE2 sN3 dir)
      (hNonEmpty : sN1'.length > 0 /\ sE2'.length > 0 /\ sN3'.length > 0) :
      RefinementTyping ctx Gamma1 Gamma2 Gamma3 v1 r2 v3 dir
        ((Gamma1.join Gamma2 |>.join Gamma3).setMany
          [(v1, GSort.nodeRefinedOf ctx.graphSite sN1'),
           (r2, GSort.edgeRefinedOf ctx.graphSite sE2'),
           (v3, GSort.nodeRefinedOf ctx.graphSite sN3')])

  /-- Refine-Closed-Empty: any one atom is empty -> all become empty
      (Paper Section 4.1: Refine-Closed-Empty) -/
  | closedEmpty (ctx : TypingCtx) (Gamma1 Gamma2 Gamma3 : RecordSchema)
      (v1 r2 v3 : Name) (dir : Direction)
      (hJoinCompat12 : Gamma1.joinCompatible Gamma2 = true)
      (hJoinCompat23 : Gamma2.joinCompatible Gamma3 = true)
      (hJoinCompat13 : Gamma1.joinCompatible Gamma3 = true)
      (hSomeEmpty : (match Gamma1.lookup v1 with
                     | some t => t.isEmptyFormer | none => false) = true
                  \/ (match Gamma2.lookup r2 with
                     | some t => t.isEmptyFormer | none => false) = true
                  \/ (match Gamma3.lookup v3 with
                     | some t => t.isEmptyFormer | none => false) = true) :
      RefinementTyping ctx Gamma1 Gamma2 Gamma3 v1 r2 v3 dir
        ((Gamma1.join Gamma2 |>.join Gamma3).setMany
          [(v1, GSort.nodeEmpty ctx.graphSite),
           (r2, GSort.edgeEmpty ctx.graphSite),
           (v3, GSort.nodeEmpty ctx.graphSite)])

  /-- Refine-Closed-Fail: endpoint schemas incompatible (S = empty).
      The `hFail` premise (`endpointCompatTriple ... = false`) is the static
      witness that the endpoint-compatibility set S is empty: no edge schema in
      `sE2` admits a source/target pairing realized in `sN1`/`sN3` under `dir`.
      Without it the rule would be unsound, since a non-empty S could still
      produce matches; with it `matchSingleEdge` is provably vacuous. -/
  | closedFail (ctx : TypingCtx) (Gamma1 Gamma2 Gamma3 : RecordSchema)
      (v1 r2 v3 : Name) (dir : Direction)
      (sN1 : List NodeSchemaFull) (sE2 : List EdgeSchemaFull) (sN3 : List NodeSchemaFull)
      (hNode1 : Gamma1.lookup v1 = some (GSort.nodeRefinedOf ctx.graphSite sN1))
      (hEdge2 : Gamma2.lookup r2 = some (GSort.edgeRefinedOf ctx.graphSite sE2))
      (hNode3 : Gamma3.lookup v3 = some (GSort.nodeRefinedOf ctx.graphSite sN3))
      (hJoinCompat12 : Gamma1.joinCompatible Gamma2 = true)
      (hJoinCompat23 : Gamma2.joinCompatible Gamma3 = true)
      (hJoinCompat13 : Gamma1.joinCompatible Gamma3 = true)
      (hFail : endpointCompatTriple sN1 sE2 sN3 dir = false) :
      RefinementTyping ctx Gamma1 Gamma2 Gamma3 v1 r2 v3 dir
        ((Gamma1.join Gamma2 |>.join Gamma3).setMany
          [(v1, GSort.nodeEmpty ctx.graphSite),
           (r2, GSort.edgeEmpty ctx.graphSite),
           (v3, GSort.nodeEmpty ctx.graphSite)])

  /-- Refine-Open: no schema info, just join all three -/
  | open_ (ctx : TypingCtx) (Gamma1 Gamma2 Gamma3 : RecordSchema)
      (v1 r2 v3 : Name) (dir : Direction)
      (hNode1 : Gamma1.lookup v1 = some (GSort.nodeOf ctx.graphSite))
      (hEdge2 : Gamma2.lookup r2 = some (GSort.edgeOf ctx.graphSite))
      (hNode3 : Gamma3.lookup v3 = some (GSort.nodeOf ctx.graphSite))
      (hJoinCompat12 : Gamma1.joinCompatible Gamma2 = true)
      (hJoinCompat23 : Gamma2.joinCompatible Gamma3 = true)
      (hJoinCompat13 : Gamma1.joinCompatible Gamma3 = true) :
      RefinementTyping ctx Gamma1 Gamma2 Gamma3 v1 r2 v3 dir
        (Gamma1.join Gamma2 |>.join Gamma3)

/- ============================================================
    Pattern Typing: Sigma; G |-^box_P P : Gamma triangle v
    (Paper Section 4.1)
    Now outputs tail variable (triangle v) as part of judgment.
    ============================================================ -/

/-- PatternTyping now includes tail variable in output.
  Sigma; G |-^box_P P : Gamma triangle tailVar -/

/- PatternTyping connects individual atoms(node/edge) into a path,
 while performing type refinement along the way.
 -/
inductive PatternTyping :
    TypingCtx -> QuantDepth -> Pattern
    -> RecordSchema -> Name -> Prop where

  /-- Pat-Node: atom typing for a node, tail = node var; ex: Pattern: (m :Person) -/
  | patNode (ctx : TypingCtx) (qd : QuantDepth)
      (na : NodeAtom) (GammaA : RecordSchema)
      (hAtom : AtomTyping ctx (.node na) GammaA) :
      PatternTyping ctx qd (.node na) GammaA na.var

  /-- Pat-Edge + Pat-Step (base case): N1 D N2 with 3-way endpoint refinement
      Paper: types source node, edge, target node independently,
      then feeds all three into Sigma;G;Gamma1;Gamma_e;Gamma3 |-_REF v1,r2,v3,D : Gamma4 -/

  | patEdge (ctx : TypingCtx) (qd : QuantDepth)
      (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
      (GammaN1 GammaE GammaN2 GammaRef : RecordSchema)
      (hSingle : rel.quantifier = .single)
      (hAtomN1 : AtomTyping ctx (.node n1) GammaN1)
      (hAtomE : AtomTyping ctx (.edge { var := rel.var, labels := rel.labels, props := rel.props }) GammaE)
      (hAtomN2 : AtomTyping ctx (.node n2) GammaN2)
      (hRef : RefinementTyping ctx GammaN1 GammaE GammaN2 n1.var rel.var n2.var dir GammaRef) :
      PatternTyping ctx qd
        (.edge n1 rel dir n2)
        GammaRef n2.var

  /-- Pat-Step: P D^K N -- compose prefix with edge+destination
      (Paper Section 4.1, Pat-Step rule)
      Types prefix P to get Gamma1 with tail v1,
      types edge atom and target node independently,
      applies 3-way refinement on (v1, r2, v3). -/

  /- ex:Pattern: (m :Person)-[r :KNOWS]->(n :Person) -/
  | patStep (ctx : TypingCtx) (qd : QuantDepth)
      (P : Pattern) (rel : EdgeAtom) (dir : Direction) (n2 : NodeAtom)
      (Gamma1 GammaE GammaN2 GammaRef : RecordSchema) (v1 : Name)
      (hSingle : rel.quantifier = .single)
      (hPrefix : PatternTyping ctx qd P Gamma1 v1)
      (hAtomE : AtomTyping ctx (.edge { var := rel.var, labels := rel.labels, props := rel.props }) GammaE)
      (hAtomN2 : AtomTyping ctx (.node n2) GammaN2)
      (hRef : RefinementTyping ctx Gamma1 GammaE GammaN2 v1 rel.var n2.var dir GammaRef) :
      PatternTyping ctx qd
        (.step P rel dir n2)
        GammaRef n2.var

  /-- Pat-Quant-Edge: for a group-reference quantifier K, variable-length
      paths leave intermediate nodes unconstrained, so single-edge endpoint
      refinement does not extend to multi-hop paths: the ENDPOINTS are typed
      with graph-scoped (unrefined) sorts, sound for every path length.
      The EDGE atom, however, is typed through the atom judgment (as in the
      paper's rule): every edge on the path satisfies the atom's label and
      property constraints, so at a closed site the group reference's
      element sort is the label/property-refined edge sort. -/
  | patQuantEdge (ctx : TypingCtx)
      (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
      (K : Quantifier) (GammaE : RecordSchema)
      (hQuant : K.isGroupRef = true)
      (hAtomE : AtomTyping ctx (.edge { var := rel.var, labels := rel.labels, props := rel.props }) GammaE)
      (hNE12 : (rel.var == n1.var) = false)
      (hNE23 : (rel.var == n2.var) = false) :
      PatternTyping ctx .outside
        (.edge n1 { rel with quantifier := K } dir n2)
        (((RecordSchema.mk [(n1.var, GSort.nodeOf ctx.graphSite)]).join GammaE
            |>.join (RecordSchema.mk [(n2.var, GSort.nodeOf ctx.graphSite)])).liftToGroupRef [rel.var]) n2.var

  /-- Pat-Opt-Edge: the `?` (zero-or-one) quantifier.  Endpoints are typed
      with graph-scoped (unrefined) sorts: in the zero case they bind the
      same node with no edge constraining them, so single-edge endpoint
      refinement is unsound here for the same reason as for the
      group-reference quantifiers.  The edge variable is exposed through
      the `?` Quantifier Lift (Paper Definition 4.2): nullable -- null in
      the zero case, an edge reference in the one case. -/
  | patOptEdge (ctx : TypingCtx)
      (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
      (hNE12 : (rel.var == n1.var) = false)
      (hNE23 : (rel.var == n2.var) = false) :
      PatternTyping ctx .outside
        (.edge n1 { rel with quantifier := .question } dir n2)
        (((RecordSchema.mk [(n1.var, GSort.nodeOf ctx.graphSite)]).join
            (RecordSchema.mk [(rel.var, GSort.edgeOf ctx.graphSite)])
            |>.join (RecordSchema.mk [(n2.var, GSort.nodeOf ctx.graphSite)])).liftToNullable [rel.var]) n2.var

  /-- Pat-Quant-Path: (P)K lifts ALL fresh inner variables to List type
      (Paper Section 4.1, Pat-Quant-Path) for K in {*, +, {i}, {i,j}}
      S = dom(Gamma) \ dom(Ctx_input) -/
  | patQuantPath (ctx : TypingCtx)
      (P : Pattern) (K : Quantifier) (GammaInner : RecordSchema) (v : Name)
      (hInner : PatternTyping ctx .inside P GammaInner v)
      (hQuant : K.isGroupRef = true) :
      PatternTyping ctx .outside
        (.quantified P K)
        (GammaInner.liftToGroupRef GammaInner.dom) v

  /-- Grouped pattern: (P) transparent -/
  | patGrouped (ctx : TypingCtx) (qd : QuantDepth)
      (P : Pattern) (Gamma : RecordSchema) (v : Name)
      (h : PatternTyping ctx qd P Gamma v) :
      PatternTyping ctx qd (.grouped P) Gamma v

/- ============================================================
    Pattern Expression Typing: Sigma; G |-_PE p : Gamma
    (Paper Section 4.1)
    No tail variable (pattern expressions are complete).
    ============================================================ -/
/-
check the pattern query:
single MATCH (a)->(b),

conjunction  MATCH (a)->(b), (b)->(c)
take the two recordSchemas to compare, call joinCompatible to make sure no conflicts, then use join to merge into one recordSchema.
 -/
inductive PatExprTyping :
    TypingCtx -> Pattern -> RecordSchema -> Prop where

  /-- PE-Single: promote path pattern to pattern expression -/
  | single (ctx : TypingCtx)
      (P : Pattern) (Gamma : RecordSchema) (v : Name)
      (h : PatternTyping ctx .outside P Gamma v) :
      PatExprTyping ctx P Gamma

  /-- PE-Conjunction: p, P -- both must match, schemas joined -/
  | conjunction (ctx : TypingCtx)
      (P1 P2 : Pattern) (Gamma1 Gamma2 : RecordSchema) (v : Name)
      (h1 : PatExprTyping ctx P1 Gamma1)
      (h2 : PatternTyping ctx .outside P2 Gamma2 v)
      (hJoinCompat : Gamma1.joinCompatible Gamma2 = true) :
      PatExprTyping ctx (.patternList P1 P2) (Gamma1.join Gamma2)

/- ============================================================
    Projection Typing (Paper Section 4.2)
    ============================================================ -/

inductive ProjectionTyping : TypingCtx -> RecordSchema -> Projection -> RecordSchema -> Prop where

  /-- Prj-Atom: unaliased variable projection (Paper Section 4.2) -/
  | atom (ctx : TypingCtx) (Ctx : RecordSchema)
      (x : Name) (tau : GSort)
      (hLookup : Ctx.lookup x = some tau) :
      ProjectionTyping ctx Ctx (.expr (.var x))
        (RecordSchema.mk [(x, tau)])

  /-- Prj-Alias: theta As x, typed at aggregation budget one, so the alias
      may contain one root aggregate anywhere in its expression tree -/
  | alias' (ctx : TypingCtx) (Ctx : RecordSchema)
      (e : Expr) (x : Name) (tau : GSort) (omega' : VarSet)
      (hType : ExprTyping ctx Ctx .one .group e tau omega') :
      ProjectionTyping ctx Ctx (.alias' e x)
        (RecordSchema.mk [(x, tau)])

  /-- Prj-Agg-Alias: agg(qual e) As y -/
  | aggAs (ctx : TypingCtx) (Ctx : RecordSchema)
      (op : AggOp) (qual : AggQualifier) (e : Expr) (y : Name) (tau : GSort)
      (omega' : VarSet)
      (hType : ExprTyping ctx Ctx .one .group (.agg op qual e) tau omega') :
      ProjectionTyping ctx Ctx (.aggAs op qual e y)
        (RecordSchema.mk [(y, tau)])

/-- Prj-List: type a list of projections -/
inductive ProjectionListTyping :
    TypingCtx -> RecordSchema -> ProjectionList -> RecordSchema -> Prop where

  | nil (ctx : TypingCtx) (Ctx : RecordSchema) :
      ProjectionListTyping ctx Ctx [] RecordSchema.empty

  | cons (ctx : TypingCtx) (Ctx : RecordSchema)
      (pi : Projection) (pis : ProjectionList) (Gpi Ctxrest : RecordSchema)
      (hProj : ProjectionTyping ctx Ctx pi Gpi)
      (hRest : ProjectionListTyping ctx Ctx pis Ctxrest)
      (hDisjoint : RecordSchema.disjointUnionCompatible Gpi Ctxrest = true) :
      ProjectionListTyping ctx Ctx (pi :: pis) (Gpi.disjointUnion Ctxrest)

/- ============================================================
    Operator-Specific Schema Compatibility and Combination
    (Paper Section 4.2: Gamma1 ~_circledast Gamma2 and Gamma1 circledast Gamma2)
    ============================================================ -/

/-- Operator-indexed compatibility condition -/
def opCompatible (op : SetOp) (Ctx1 Ctx2 : RecordSchema) : Bool :=
  match op with
  | .union | .otherwise => RecordSchema.unionCompatible Ctx1 Ctx2
  | .exceptDistinct | .exceptAll => RecordSchema.unionCompatible Ctx1 Ctx2
  | .intersectDistinct | .intersectAll => RecordSchema.unionCompatible Ctx1 Ctx2

/-- Operator-indexed schema combination -/
def opCombine (op : SetOp) (Ctx1 Ctx2 : RecordSchema) : RecordSchema :=
  match op with
  | .union => RecordSchema.schemaUnion Ctx1 Ctx2
  -- OTHERWISE can return the right operand's table (when the left is empty), and
  -- union-compatibility only equates domains, so the result schema must be one
  -- both branches satisfy: the schema union (the same combine as UNION).
  | .otherwise => RecordSchema.schemaUnion Ctx1 Ctx2
  | .exceptDistinct | .exceptAll => Ctx1
  | .intersectDistinct | .intersectAll => Ctx1

/- ============================================================
    Query Typing (Paper Section 4.2)
    ============================================================ -/

inductive QueryTyping : TypingCtx -> Query -> RecordSchema -> Prop where

  /-- Q-Match-Filter (Paper Section 4.2) -/
  | matchFilter (ctx : TypingCtx)
      (P : Pattern) (phi : Pred) (projs : ProjectionList)
      (Gamma1 Gamma2 : RecordSchema) (tPred : GSort) (omegaPred : VarSet)
      (hGraph : (ctx.catalog.lookup ctx.graphSite).isSome = true)
      (hPat : PatExprTyping ctx P Gamma1)
      (hPred : PredTyping ctx Gamma1 .one .singleton phi tPred omegaPred)
      (hPredSub : Subtype tPred GSort.boolN)
      (hProj : ProjectionListTyping ctx Gamma1 projs Gamma2) :
      QueryTyping ctx (.matchWhere P phi projs) Gamma2

  /-- Q-Match (desugars to Q-Match-Filter with True, Paper Section 4.2) -/
  | matchReturn (ctx : TypingCtx)
      (P : Pattern) (projs : ProjectionList)
      (Gamma1 Gamma2 : RecordSchema)
      (hGraph : (ctx.catalog.lookup ctx.graphSite).isSome = true)
      (hPat : PatExprTyping ctx P Gamma1)
      (hProj : ProjectionListTyping ctx Gamma1 projs Gamma2) :
      QueryTyping ctx (.matchReturn P projs) Gamma2

  /-- Use clause: select working graph -/
  | useGraph (ctx : TypingCtx)
      (graphName : Name) (Q : Query) (Gamma : RecordSchema)
      (hResolve : (ctx.catalog.lookup graphName).isSome = true)
      (hBody : QueryTyping { ctx with graphSite := graphName } Q Gamma) :
      QueryTyping ctx (.useGraph graphName Q) Gamma

  /-- CQ-Lift: linear query lifted to composite (Paper Section 4.2) -/
  | cqLift (ctx : TypingCtx) (Q : Query) (Gamma : RecordSchema)
      (h : QueryTyping ctx Q Gamma) :
      QueryTyping ctx Q Gamma

  /-- CQ-Expression: q circledast Q with operator-specific compatibility
      (Paper Section 4.2).  The operator is chosen per node here, so this
      is more general than the paper's judgment; the single-operator form is
      CompQueryTyping below. -/
  | composite (ctx : TypingCtx)
      (op : SetOp) (Q1 Q2 : Query) (Gamma1 Gamma2 : RecordSchema)
      (h1 : QueryTyping ctx Q1 Gamma1)
      (h2 : QueryTyping ctx Q2 Gamma2)
      (hCompat : opCompatible op Gamma1 Gamma2 = true) :
      QueryTyping ctx (.composite op Q1 Q2) (opCombine op Gamma1 Gamma2)

/- ============================================================
    Composite Query Typing, paper-faithful form (Paper Section 4.2)
    Sigma |-_circledast q : Gamma
    ============================================================ -/

/-- The composite-query judgment of the paper: indexed by a single
    operator threaded through the whole derivation (ISO 14.2 permits one
    kind of composite operator per query).  Operands are linear queries
    (Fig. 2: q ::= Q | q circledast Q). -/
inductive CompQueryTyping :
    TypingCtx -> SetOp -> Query -> RecordSchema -> Prop where

  /-- CQ-Lift: a linear query embeds at any operator index. -/
  | lift (ctx : TypingCtx) (op : SetOp) (Q : Query) (Gamma : RecordSchema)
      (hLin : Q.isLinear = true)
      (h : QueryTyping ctx Q Gamma) :
      CompQueryTyping ctx op Q Gamma

  /-- CQ-Expression: q circledast Q, same operator on the left spine,
      linear right operand. -/
  | expression (ctx : TypingCtx) (op : SetOp) (q Q : Query)
      (Gamma1 Gamma2 : RecordSchema)
      (h1 : CompQueryTyping ctx op q Gamma1)
      (hLin2 : Q.isLinear = true)
      (h2 : QueryTyping ctx Q Gamma2)
      (hCompat : opCompatible op Gamma1 Gamma2 = true) :
      CompQueryTyping ctx op (.composite op q Q) (opCombine op Gamma1 Gamma2)

/-- The single-operator judgment is included in the general one. -/
theorem CompQueryTyping.toQueryTyping {ctx : TypingCtx} {op : SetOp}
    {q : Query} {Gamma : RecordSchema}
    (h : CompQueryTyping ctx op q Gamma) : QueryTyping ctx q Gamma := by
  induction h with
  | lift _ _ _hLin hQ => exact hQ
  | expression q' Q' Gamma1 Gamma2 _h1 _hLin2 h2 hCompat ih =>
    exact .composite _ _ q' Q' Gamma1 Gamma2 ih h2 hCompat

end MGQL
