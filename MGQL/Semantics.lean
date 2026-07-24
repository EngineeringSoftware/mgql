/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Semantics.lean -- Big-step denotational semantics (total evaluation functions)

  Reference: Paper Section 5

  Changes from v2:
  - Added dist() for CQ-ExceptD and CQ-IntersectD (Paper Section 5.3)
  - Added phiD: runtime endpoint condition phi_D(n1, e, n2) (Paper Section 5.2)
  - Added bindingTableJoin for PE-And natural join
  - Quantified path pattern (.quantified P K) now respects quantifier bounds
  - Edge quantifiers use Quantifier.lo/hi helpers
-/
import MGQL.Sorts
import MGQL.Values
import MGQL.Syntax
import MGQL.Schema
import MGQL.RecordSchema

namespace MGQL

-- ============================================================
--  Expression Semantics
-- ============================================================

def evalLiteral : Literal -> Value
  | .int n    => .ofInt n
  | .string s => .ofString s
  | .bool b   => .ofBool b

def evalArith (op : ArithOp) (v1 v2 : Value) : Value :=
  match v1.asInt, v2.asInt with
  | some n1, some n2 =>
    match op with
    | .add => .ofInt (n1 + n2)
    | .sub => .ofInt (n1 - n2)
    | .mul => .ofInt (n1 * n2)
    | .div => if n2 == 0 then .null else .ofInt (n1 / n2)
  | _, _ => .null

def evalAggOnValues (op : AggOp) (qual : AggQualifier) (vals : List Value) : Value :=
  let nonNull := vals.filter (fun v => !v.isNull)
  let filtered := match qual with
    | .distinct => nonNull.foldl (fun (acc : List Value) v =>
        if acc.any (fun x => x == v) then acc else acc ++ [v]) []
    | _ => nonNull
  match op with
  | .count => .ofInt (Int.ofNat filtered.length)
  | .sum =>
    let ints := filtered.filterMap Value.asInt
    if ints.isEmpty then .null
    else .ofInt (ints.foldl (· + ·) 0)
  | .max =>
    let ints := filtered.filterMap Value.asInt
    match ints with
    | [] => .null
    | x :: xs => .ofInt (xs.foldl (fun a b => if a >= b then a else b) x)
  | .min =>
    let ints := filtered.filterMap Value.asInt
    match ints with
    | [] => .null
    | x :: xs => .ofInt (xs.foldl (fun a b => if a <= b then a else b) x)

-- ============================================================
--  Relational Operator Semantics
-- ============================================================

def evalRelOp (op : RelOp) (v1 v2 : Value) : Option Bool :=
  -- Paper App. C (E-Relational / E-Relational-Null): the comparison is defined
  -- only on two integers; any non-integer operand (including Null, strings,
  -- and booleans) yields Null. Well-typed operands coerce to Int? (H-PropType
  -- gives open property access the type (Z|S|B)? which refines to Int?), so a
  -- string/bool operand is possible at runtime and must propagate Null here.
  match v1, v2 with
  | .prim (.int n1), .prim (.int n2) =>
    some (match op with
      | .eq  => n1 == n2
      | .neq => n1 != n2
      | .lt  => n1 < n2
      | .le  => n1 <= n2
      | .gt  => n1 > n2
      | .ge  => n1 >= n2)
  | _, _ => none

/-! Expression and predicate evaluation are mutually recursive, mirroring the
    mutual grammar (Paper Fig 2: `e ::= ... | phi`): an embedded predicate
    evaluates under Kleene logic and its truth value is reflected into the
    value domain (`Null` when the predicate is undefined). -/
mutual

def evalExpr (G : PropertyGraph) (site : GraphSite) (rho : Record) : Expr -> Value
  | .const lit => evalLiteral lit
  | .null => .null
  | .var x => rho.lookup x
  | .propAccess x k =>
    let v := rho.lookup x
    match v with
    | .nodeRef _ n =>
      if h : n < G.numNodes
      then (G.nodeProps (Fin.mk n h)).lookup k
      else .null
    | .edgeRef _ e =>
      if h : e < G.numEdges
      then (G.edgeProps (Fin.mk e h)).lookup k
      else .null
    | _ => .null
  | .arithOp op e1 e2 =>
    let v1 := evalExpr G site rho e1
    let v2 := evalExpr G site rho e2
    evalArith op v1 v2
  | .agg op qual inner =>
    let innerVal := evalExpr G site rho inner
    match innerVal with
    | .list vs => evalAggOnValues op qual vs.toList
    | _ =>
      match op with
      | .count => if innerVal.isNull then .ofInt 0 else .ofInt 1
      -- Sum/Max/Min on a non-list (non-collection) operand is undefined; yield
      -- Null so the result inhabits the nullable result type Int? (Thm 6.1).
      | _ => .null
  | .pred phi =>
    match evalPred G site rho phi with
    | some b => .ofBool b
    | none => .null

def evalPred (G : PropertyGraph) (site : GraphSite) (rho : Record) : Pred -> Option Bool
  | .true  => some true
  | .false => some false
  | .relOp op e1 e2 =>
    let v1 := evalExpr G site rho e1
    let v2 := evalExpr G site rho e2
    evalRelOp op v1 v2
  | .not phi => Kleene.neg (evalPred G site rho phi)
  | .and p1 p2 => Kleene.and (evalPred G site rho p1) (evalPred G site rho p2)
  | .or  p1 p2 => Kleene.or  (evalPred G site rho p1) (evalPred G site rho p2)
  | .isNull e =>
    let v := evalExpr G site rho e
    some v.isNull

end

/-- The value of an embedded predicate: its Kleene truth value reflected into
    the value domain (`Null` when undefined). Definitionally the `.pred`
    branch of `evalExpr`. -/
def evalPredValue (G : PropertyGraph) (site : GraphSite) (rho : Record)
    (phi : Pred) : Value :=
  match evalPred G site rho phi with
  | some b => .ofBool b
  | none => .null

-- ============================================================
--  Label Matching (runtime)
-- ============================================================

def evalLabelExpr (labels : List Name) : LabelExpr -> Bool
  | .atom l     => labels.any (fun x => x == l)
  | .wildcard   => !labels.isEmpty
  | .neg l      => !evalLabelExpr labels l
  | .conj l1 l2 => evalLabelExpr labels l1 && evalLabelExpr labels l2
  | .disj l1 l2 => evalLabelExpr labels l1 || evalLabelExpr labels l2

def checkLabels (labels : List Name) : Option LabelExpr -> Bool
  | none => true
  | some l => evalLabelExpr labels l

-- ============================================================
--  Pattern Semantics
-- ============================================================

/-! ## Quantifier Normalization N_K^OG (Paper Section 5.2)
  Normalizes quantifier bounds, capping unbounded quantifiers at |E|
  (Trail mode: each edge may be traversed at most once).
  N_K^OG =
    (0, |E|)  if K = *
    (1, |E|)  if K = +
    (0, 1)    if K = ?
    (i, i)    if K = {i}
    (i, j)    if K = {i, j} -/
def quantifierNormalize (K : Quantifier) (numEdges : Nat) : Prod Nat Nat :=
  match K with
  | .single    => (1, 1)
  | .star      => (0, numEdges)
  | .plus      => (1, numEdges)
  | .question  => (0, 1)
  | .exact i   => (i, i)
  | .range i j => (i, j)

/-- Runtime endpoint condition phi_D(n1, e, n2) (Paper Section 5.2)
  Runtime analog of the static endpoint condition theta_D in the typing rules.
  Checks whether source node n1, edge e, and target node n2 form a valid
  endpoint triple for direction D. -/
def phiD (G : PropertyGraph) (dir : Direction)
    (n1 : Fin G.numNodes) (e : Fin G.numEdges) (n2 : Fin G.numNodes) : Bool :=
  let isDir := G.edgeDirected e
  let eSrc := G.src e
  let eDst := G.dst e
  -- phi_right: Theta(e) = (n1, n2) /\ Delta(e) = directed
  let phiRight := isDir && eSrc == n1 && eDst == n2
  -- phi_left: Theta(e) = (n2, n1) /\ Delta(e) = directed
  let phiLeft := isDir && eSrc == n2 && eDst == n1
  -- phi_tilde: {n1, n2} = Theta(e) /\ Delta(e) = undirected
  let phiUndirected := !isDir &&
    ((eSrc == n1 && eDst == n2) || (eSrc == n2 && eDst == n1))
  match dir with
  | .right              => phiRight
  | .left               => phiLeft
  | .anyDirected        => phiRight || phiLeft
  | .undirected         => phiUndirected
  | .rightOrUndirected  => phiRight || phiUndirected
  | .leftOrUndirected   => phiLeft || phiUndirected
  | .any                => phiRight || phiLeft || phiUndirected

/-- Natural join of binding tables: B1 |><| B2 (Paper Section 5.2, PE-And)
  Joins records that agree on shared variables. -/
def bindingTableJoin (B1 B2 : BindingTable) : BindingTable :=
  B1.flatMap fun rho1 =>
    B2.filterMap fun rho2 =>
      if rho1.agreeOn rho2 then some (rho1.merge rho2)
      else none

/-- Check property constraints (now uses Literal evaluation) -/
def checkNodeProps (G : PropertyGraph) (_site : GraphSite) (n : Fin G.numNodes)
    (props : List PropConstraint) : Bool :=
  props.all fun pc =>
    let expected := evalLiteral pc.val
    let actual := (G.nodeProps n).lookup pc.key
    expected == actual

def checkEdgeProps (G : PropertyGraph) (_site : GraphSite) (e : Fin G.numEdges)
    (props : List PropConstraint) : Bool :=
  props.all fun pc =>
    let expected := evalLiteral pc.val
    let actual := (G.edgeProps e).lookup pc.key
    expected == actual

def matchNode (G : PropertyGraph) (site : GraphSite) (na : NodeAtom) : List Record :=
  (List.range G.numNodes).filterMap fun i =>
    if h : i < G.numNodes then
      let n : Fin G.numNodes := Fin.mk i h
      let labels := G.nodeLabels n
      if checkLabels labels na.labels then
        let rho : Record := [(na.var, Value.nodeRef site i)]
        if checkNodeProps G site n na.props then some rho
        else none
      else none
    else none

def matchSingleEdge (G : PropertyGraph) (site : GraphSite)
    (src : NodeAtom) (rel : EdgeAtom) (dst : NodeAtom) (dir : Direction) :
    List Record :=
  let srcRecords := matchNode G site src
  srcRecords.flatMap fun rho_src =>
    let srcId := match rho_src.lookup src.var with
      | .nodeRef _ n => some n
      | _ => none
    match srcId with
    | none => []
    | some srcN =>
      (List.range G.numEdges).flatMap fun ei =>
        if h : ei < G.numEdges then
          let e : Fin G.numEdges := Fin.mk ei h
          -- Check label and property constraints on the edge
          if checkLabels (G.edgeLabels e) rel.labels &&
             checkEdgeProps G site e rel.props then
            -- Collect all valid (srcNode, dstNode) pairs via phiD
            let eSrc := (G.src e).val
            let eDst := (G.dst e).val
            -- Determine candidate destination node ids based on endpoint condition
            -- Deduplicate to avoid double results on self-loops
            let rawCandidates : List Nat :=
              [eSrc, eDst].filter fun dstN =>
                if h2 : srcN < G.numNodes then
                  if h3 : dstN < G.numNodes then
                    phiD G dir (Fin.mk srcN h2) e (Fin.mk dstN h3)
                  else false
                else false
            let candidates := rawCandidates.foldl (fun acc c =>
              if acc.any (fun x => x == c) then acc else acc ++ [c]) []
            candidates.filterMap fun dstN =>
              if h2 : dstN < G.numNodes then
                let dstFin : Fin G.numNodes := Fin.mk dstN h2
                let dstLabels := G.nodeLabels dstFin
                if checkLabels dstLabels dst.labels &&
                   checkNodeProps G site dstFin dst.props then
                  let rho := rho_src.extend rel.var (.edgeRef site ei)
                  let dstVal := Value.nodeRef site dstN
                  -- Natural-join semantics on shared variables: if the destination
                  -- variable already occurs (e.g. a self-loop (a)-[r]->(a) where the
                  -- source and target share a variable), keep the match only when the
                  -- two bindings agree; otherwise this cross-product row is filtered.
                  if rho.mem dst.var && !(rho.lookup dst.var == dstVal) then none
                  else some (rho.extend dst.var dstVal)
                else none
              else none
          else []
        else []

def matchVarLengthPath (G : PropertyGraph) (site : GraphSite)
    (src : NodeAtom) (rel : EdgeAtom) (dst : NodeAtom) (dir : Direction)
    (k : Nat) : List Record :=
  match k with
  | 0 =>
    let srcRecords := matchNode G site src
    srcRecords.filterMap fun rho =>
      let srcVal := rho.lookup src.var
      some (rho.extend rel.var (.ofList []) |>.extend dst.var srcVal)
  | 1 =>
    let results := matchSingleEdge G site src
      { rel with quantifier := .single } dst dir
    results.map fun rho =>
      match rho.lookup rel.var with
      | .edgeRef g ee => rho.set rel.var (.ofList [.edgeRef g ee])
      | _ => rho
  | n + 2 =>
    let tempVar := "_mid_" ++ toString n
    let tempRel := "_rel_" ++ toString n
    let firstEdge := matchSingleEdge G site src
      { rel with var := tempRel, quantifier := .single }
      { var := tempVar, labels := none, props := [] } dir
    firstEdge.flatMap fun rho1 =>
      let midVal := rho1.lookup tempVar
      let midId := match midVal with
        | .nodeRef _ nn => some nn
        | _ => none
      match midId with
      | none => []
      | some _ =>
        -- Fresh recursive edge variable: `_rest_` prefixed to the destination
        -- variable, so it is provably distinct from `dst.var` (length) and from
        -- the generated `_mid_`/`_rel_` names (prefix). No reserved-name
        -- assumption on user patterns is needed (Paper Rnm-Edge-Fresh).
        let restRel := "_rest_" ++ dst.var
        let restRecords := matchVarLengthPath G site
          { var := tempVar, labels := none, props := [] }
          { rel with var := restRel } dst dir (n + 1)
        restRecords.filterMap fun rho2 =>
          let midVal2 := rho2.lookup tempVar
          if midVal == midVal2 then
            let edges1 := match rho1.lookup tempRel with
              | .edgeRef g ee => [Value.edgeRef g ee]
              | _ => []
            let edges2 := match (rho2.lookup restRel).asList with
              | some es => es
              | none => []
            let combinedEdges := edges1 ++ edges2
            let result : Record := [(src.var, rho1.lookup src.var),
                          (rel.var, .ofList combinedEdges),
                          (dst.var, rho2.lookup dst.var)]
            some result
          else none
termination_by k
decreasing_by simp_wf <;> omega

def matchRangePath (G : PropertyGraph) (site : GraphSite)
    (src : NodeAtom) (rel : EdgeAtom) (dst : NodeAtom) (dir : Direction)
    (lo hi : Nat) : List Record :=
  (List.range (hi - lo + 1)).flatMap fun offset =>
    matchVarLengthPath G site src rel dst dir (lo + offset)

/-- Collapse a path (the per-iteration base records, in order) into one group-
    reference record: each variable in `vars` is bound to the list of its
    per-iteration values (Pat-Quant-Path lifts the inner schema pointwise, so
    every variable inside the quantifier is exposed as such a list). The empty
    path yields one empty list per variable -- the zero-length match. -/
def collapsePath (vars : List Name) (path : List Record) : Record :=
  vars.map fun x => (x, Value.ofList (path.map (fun r => r.lookup x)))

/-- Frontier-based quantified path iteration (Paper Section 5.2: QPath-Iter/Finish).
  Frontier entries are PARTIAL PATHS `(path, endNode)`: the base records traversed
  so far and the current end-node value. Each step extends a partial path with a
  base record whose lead node matches `endNode`; emitting a length-`kappa` path
  (when `kappa >= lo`) collapses it so every variable becomes the list of its
  per-iteration values. Uses fuel for termination. -/
def qpathIterate (baseResults : List Record) (vars : List Name) (lv tv : Name) (lo hi : Nat)
    (kappa : Nat) (frontier : List (List Record × Value))
    (accumulated : List Record) (fuel : Nat) : List Record :=
  match fuel with
  | 0 => accumulated
  | fuel' + 1 =>
    if kappa > hi || frontier.isEmpty then
      accumulated  -- QPath-Finish
    else
      let newAccum :=
        if kappa >= lo then
          accumulated ++ frontier.map (fun pe => collapsePath vars pe.fst)
        else accumulated
      let nextFrontier := frontier.flatMap fun pe =>
        baseResults.filterMap fun rho =>
          if rho.lookup lv == pe.snd then some (pe.fst ++ [rho], rho.lookup tv)
          else none
      qpathIterate baseResults vars lv tv lo hi (kappa + 1) nextFrontier newAccum fuel'

/-- The quantified-path evaluator body `(P)^K`. `vars` is the variable set of the
    inner pattern (`patternVars P`), needed so the zero-length match binds every
    variable to the empty list even when there are no base results. -/
def evalQuantified (vars : List Name) (baseResults : List Record) (lv tv : Name)
    (lo hi : Nat) : List Record :=
  let initFrontier : List (List Record × Value) :=
    baseResults.map fun rho => ([rho], rho.lookup tv)
  let zeroResults : List Record :=
    if lo == 0 then [collapsePath vars []] else []
  zeroResults ++ qpathIterate baseResults vars lv tv lo hi 1 initFrontier [] (hi + 1)

/-- The `?` (zero-or-one) quantifier on an edge (Paper Definition 4.2, the
    `?` Quantifier Lift).  Zero case: the two node atoms match the SAME
    node (a length-zero path) and the edge variable is bound to null --
    not to an empty list, which is what the group-reference quantifiers
    produce.  One case: an ordinary single-edge match binding the edge
    variable to an edge reference. -/
def matchOptionalEdge (G : PropertyGraph) (site : GraphSite)
    (src : NodeAtom) (rel : EdgeAtom) (dst : NodeAtom) (dir : Direction) :
    List Record :=
  ((List.range G.numNodes).filterMap fun i =>
    if h : i < G.numNodes then
      let n : Fin G.numNodes := Fin.mk i h
      if checkLabels (G.nodeLabels n) src.labels &&
         checkNodeProps G site n src.props &&
         (checkLabels (G.nodeLabels n) dst.labels &&
          checkNodeProps G site n dst.props) then
        some [(src.var, Value.nodeRef site i), (rel.var, Value.null),
              (dst.var, Value.nodeRef site i)]
      else none
    else none)
  ++ matchSingleEdge G site src { rel with quantifier := .single } dst dir

def evalPattern (G : PropertyGraph) (site : GraphSite) : Pattern -> List Record
  | .node na => matchNode G site na
  | .edge n1 rel dir n2 =>
    match rel.quantifier with
    | .single => matchSingleEdge G site n1 rel n2 dir
    | .question => matchOptionalEdge G site n1 rel n2 dir
    | q =>
      let lo := q.lo
      let hi := match q.hi with
        | some h => h
        | none => G.numEdges  -- bounded by edge count for unbounded quantifiers
      matchRangePath G site n1 rel n2 dir lo hi
  | .step P rel dir n2 =>
    -- Evaluate prefix, then extend each result with the edge + destination
    let prefixResults := evalPattern G site P
    prefixResults.flatMap fun rho =>
      let tailVar := patternTailVar P
      match tailVar with
      | none => []
      | some tv =>
        let tailVal := rho.lookup tv
        let tailId := match tailVal with
          | .nodeRef _ n => some n
          | _ => none
        match tailId with
        | none => []
        | some _ =>
          let srcAtom : NodeAtom := { var := tv }
          -- Handle quantified vs single edge in step
          let edgeResults := match rel.quantifier with
            | .single =>
              matchSingleEdge G site srcAtom
                { rel with quantifier := .single } n2 dir
            | .question => matchOptionalEdge G site srcAtom rel n2 dir
            | q =>
              let lo := q.lo
              let hi := match q.hi with
                | some h => h
                | none => G.numEdges
              matchRangePath G site srcAtom rel n2 dir lo hi
          -- Natural equijoin: keep edges that agree with the prefix on every
          -- shared variable (the source tail, and any reused edge/endpoint
          -- variable such as a cycle's closing node), then merge.
          edgeResults.filterMap fun rhoEdge =>
            if rho.agreeOn rhoEdge then
              some (rho.merge rhoEdge)
            else none
  | .grouped P => evalPattern G site P
  | .quantified P K =>
    -- Paper Section 5.3: Quantified path pattern (P)^K
    -- Frontier-based iteration: QPath-Init, QPath-Iter, QPath-Finish
    -- N_K^OG: normalize quantifier bounds, unbounded capped at |E|
    let lo := K.lo
    let hi := match K.hi with
      | some h => h
      | none => G.numEdges  -- Trail mode: bounded by |E|
    let baseResults := evalPattern G site P
    match patternLeadVar P, patternTailVar P with
    | some lv, some tv =>
      -- Pat-Quant-Path lifts the inner schema pointwise: every variable of P is
      -- exposed as the list of its per-iteration bindings.
      evalQuantified (patternVars P) baseResults lv tv lo hi
    | _, _ => baseResults  -- fallback if no lead/tail var
  | .patternList P1 P2 =>
    -- PE-And: B1 |><| B2 (natural join on shared variables)
    let rs1 := evalPattern G site P1
    let rs2 := evalPattern G site P2
    bindingTableJoin rs1 rs2

-- ============================================================
--  Trail path mode (Paper Section 5.1)
--
--  The paper's pattern semantics threads a visited-edge set through
--  every judgment and rejects a step that would repeat an edge (the
--  trail product); the set is discarded when a path pattern completes
--  (FS-PatExp-Done), so trail-ness is enforced per comma component and
--  edges may repeat across components.  In this fragment every matched
--  edge is bound in the output record -- single edges under their edge
--  variable, variable-length paths as an edge-reference list,
--  quantified paths as per-iteration lists -- so a record describes a
--  trail exactly when the edge references it binds are pairwise
--  distinct.  Trail mode is therefore the per-component filter below,
--  which agrees with the visited-set semantics on fully-bound patterns.
-- ============================================================

mutual
/-- Collect every edge reference bound in a value (descending into
    lists, the shape group references and variable-length paths use). -/
def Value.edgeRefs : Value -> List (Prod GraphSite Nat)
  | .edgeRef g e => [(g, e)]
  | .list vs => ValueList.edgeRefs vs
  | _ => []

def ValueList.edgeRefs : ValueList -> List (Prod GraphSite Nat)
  | .nil => []
  | .cons v vs => Value.edgeRefs v ++ ValueList.edgeRefs vs
end

/-- No `==`-duplicates. -/
def nodupBy {α : Type} [BEq α] : List α -> Bool
  | [] => true
  | a :: as => !as.contains a && nodupBy as

/-- The record's bound edge references are pairwise distinct: it
    describes a trail. -/
def Record.isTrail (rho : Record) : Bool :=
  nodupBy (rho.flatMap fun e => e.2.edgeRefs)

/-- Trail-mode pattern evaluation: each comma component's rows must bind
    pairwise-distinct edges; the join across components is unrestricted
    (mirroring FS-PatExp-Done / FS-PatExp-And). -/
def evalPatternTrail (G : PropertyGraph) (site : GraphSite) : Pattern -> List Record
  | .patternList P1 P2 =>
    bindingTableJoin (evalPatternTrail G site P1) (evalPatternTrail G site P2)
  | P => (evalPattern G site P).filter Record.isTrail

-- ============================================================
--  Projection Semantics
-- ============================================================

def evalAggOverTable (G : PropertyGraph) (site : GraphSite) (B : BindingTable)
    (op : AggOp) (qual : AggQualifier) (inner : Expr) : Value :=
  let vals := B.map fun rho => evalExpr G site rho inner
  evalAggOnValues op qual vals

def projectItem (G : PropertyGraph) (site : GraphSite) (rho : Record)
    (B : BindingTable) : Projection -> Record
  | .expr e =>
    let v := evalExpr G site rho e
    let name := match e with
      | .var x => x
      | .propAccess x k => x ++ "." ++ k
      | _ => "_expr"
    [(name, v)]
  | .alias' e x =>
    let v := evalExpr G site rho e
    [(x, v)]
  | .agg op qual inner =>
    let v := evalAggOverTable G site B op qual inner
    let opName := match op with
      | .count => "Count" | .sum => "Sum" | .max => "Max" | .min => "Min"
    let name := match inner with
      | .var x => opName ++ "(" ++ x ++ ")"
      | _ => "_agg"
    [(name, v)]
  | .aggAs op qual inner y =>
    let v := evalAggOverTable G site B op qual inner
    [(y, v)]

def projectRecord (G : PropertyGraph) (site : GraphSite) (rho : Record)
    (B : BindingTable) (pis : ProjectionList) : Record :=
  pis.flatMap (projectItem G site rho B)

-- ============================================================
--  Query Semantics
-- ============================================================

def resolveGraph (C : Catalog) (name : Name) : Option PropertyGraph :=
  C.lookup name

/-- dist: remove duplicates from a binding table (Paper Section 5.3) -/
def dist (B : BindingTable) : BindingTable :=
  B.foldl (fun acc rho =>
    if acc.any (fun x => x == rho) then acc else acc ++ [rho]) []

def applySetOp (op : SetOp) (B1 B2 : BindingTable) : BindingTable :=
  match op with
  | .union => B1 ++ B2
  | .otherwise => if B1.isEmpty then B2 else B1
  -- CQ-ExceptD: dist(B1 \ B2)
  | .exceptDistinct =>
    dist (B1.filter fun rho => !B2.any (fun x => x == rho))
  -- CQ-ExceptA: B1 \ B2 as bags (multiplicity-correct). Each row of B2 cancels
  -- at most one occurrence in B1, so the result multiplicity of a row is
  -- max(0, count_B1 - count_B2). Threading the shrinking B2 remainder through the
  -- fold and erasing one occurrence per match is what makes this a bag difference
  -- rather than the set difference the previous `filter` computed.
  | .exceptAll =>
    (B1.foldl (fun (st : BindingTable × BindingTable) rho =>
      let (acc, rem) := st
      if rem.any (fun x => x == rho) then (acc, rem.erase rho)
      else (acc ++ [rho], rem)) ([], B2)).1
  -- CQ-IntersectD: dist(B1 cap B2)
  | .intersectDistinct =>
    dist (B1.filter fun rho => B2.any (fun x => x == rho))
  -- CQ-IntersectA: B1 cap B2 as bags (multiplicity-correct). Result multiplicity
  -- of a row is min(count_B1, count_B2): each kept B1 occurrence consumes one
  -- matching B2 occurrence, and once B2's copies are used up the remaining B1
  -- occurrences are dropped (the previous `filter` kept every B1 copy instead).
  | .intersectAll =>
    (B1.foldl (fun (st : BindingTable × BindingTable) rho =>
      let (acc, rem) := st
      if rem.any (fun x => x == rho) then (acc ++ [rho], rem.erase rho)
      else (acc, rem)) ([], B2)).1

def evalQuery (C : Catalog) (defaultGraph : PropertyGraph)
    (site : GraphSite) (q : Query) : BindingTable :=
  match q with
  | .useGraph graphName inner =>
    match resolveGraph C graphName with
    | some G => evalQuery C G graphName inner
    | none => []
  | .matchReturn P pis =>
    let matched := evalPatternTrail defaultGraph site P
    matched.map fun rho => projectRecord defaultGraph site rho matched pis
  | .matchWhere P phi pis =>
    let matched := (evalPatternTrail defaultGraph site P).filter fun rho =>
      evalPred defaultGraph site rho phi == some true
    matched.map fun rho => projectRecord defaultGraph site rho matched pis
  | .composite op Q1 Q2 =>
    applySetOp op (evalQuery C defaultGraph site Q1) (evalQuery C defaultGraph site Q2)

end MGQL
