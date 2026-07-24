/-
  MGQL: Mechanized GQL Semantics in Lean 4
  RecordSchema.lean -- Record schemas, compatibility, schema operations,
                       record conformance

  Reference: Paper Definitions 3.3-3.4 (record and binding table
             schemas; union/join compatibility, schema union and join)

  Changes from v1:
  - sortInter handles emptyFormer (empty type former propagation)
  - valueAdmissible handles emptyFormer (always false for non-null values)
  - Updated join compatibility for emptyFormer
-/
import MGQL.Sorts
import MGQL.Values

namespace MGQL

/-! ## Sort Kind (for compatibility) -/

inductive SortKind where
  | scalar | node | edge
  deriving DecidableEq, Repr

def ExtSort.kind : ExtSort -> SortKind
  | .scalar _        => .scalar
  | .node _          => .node
  | .edge _          => .edge
  | .nodeRefined _ _ => .node
  | .edgeRefined _ _ => .edge

def SortShape.kind? : SortShape -> Option SortKind
  | .single t       => some t.kind
  | .union _        => none
  | .list _ _       => none
  | .any            => none
  | .bot            => none
  | .nullType       => none
  | .emptyFormer s _ => s.kind?

/-! ## Record Schema: Gamma : A partial-> tau -/

structure RecordSchema where
  entries : List (Prod Name GSort)

instance : BEq RecordSchema where
  beq a b := a.entries == b.entries

namespace RecordSchema

def empty : RecordSchema := RecordSchema.mk []

def dom (Ctx : RecordSchema) : List Name := Ctx.entries.map Prod.fst

def lookup (Ctx : RecordSchema) (x : Name) : Option GSort :=
  match Ctx.entries.find? (fun e => e.1 == x) with
  | some (_, t) => some t
  | none => none

def mem (Ctx : RecordSchema) (x : Name) : Bool :=
  Ctx.entries.any (fun e => e.1 == x)

def extend (Ctx : RecordSchema) (x : Name) (t : GSort) : RecordSchema :=
  RecordSchema.mk (Ctx.entries ++ [(x, t)])

def update (Ctx : RecordSchema) (x : Name) (t : GSort) : RecordSchema :=
  RecordSchema.mk (Ctx.entries.map (fun (k, v) => if k == x then (k, t) else (k, v)))

def set (Ctx : RecordSchema) (x : Name) (t : GSort) : RecordSchema :=
  if Ctx.mem x then Ctx.update x t else Ctx.extend x t

def setMany (Ctx : RecordSchema) (bindings : List (Prod Name GSort)) : RecordSchema :=
  bindings.foldl (fun acc (x, t) => acc.set x t) Ctx

def size (Ctx : RecordSchema) : Nat := Ctx.entries.length

def restrictTo (Ctx : RecordSchema) (xs : List Name) : RecordSchema :=
  RecordSchema.mk (Ctx.entries.filter (fun e => xs.any (fun x => x == e.1)))

def filterKeys (Ctx : RecordSchema) (xs : List Name) : RecordSchema :=
  RecordSchema.mk (Ctx.entries.filter (fun e => !xs.any (fun x => x == e.1)))

/-! ## Compatibility (Paper Definition 3.4) -/

def sortCompatible (t1 t2 : GSort) : Bool :=
  t1 == t2 ||
  match t1.shape.kind?, t2.shape.kind? with
  | some k1, some k2 => k1 == k2
  | _, _ => false

def compatible (Ctx1 Ctx2 : RecordSchema) : Bool :=
  let d1 := Ctx1.dom
  let d2 := Ctx2.dom
  d1.length == d2.length &&
  d1.all (fun x => d2.any (fun y => y == x)) &&
  d2.all (fun x => d1.any (fun y => y == x)) &&
  Ctx1.entries.all fun (x, t1) =>
    match Ctx2.lookup x with
    | some t2 => sortCompatible t1 t2
    | none => false

def compatibleOn (Ctx1 Ctx2 : RecordSchema) (D : List Name) : Bool :=
  D.all fun x =>
    match Ctx1.lookup x, Ctx2.lookup x with
    | some t1, some t2 => sortCompatible t1 t2
    | _, _ => false

/-! ## Sort Union: t1 union t2 (Paper Definition 3.4) -/
/- MATCH (a) UNION MATCH (a, b) -/
/-- Join in the null lattice (least upper bound): nullable if either side is
    nullable, `val`/`null` agree, else they combine up to `nullable`. Used by the
    subsumption arms of `sortUnion` so the union keeps the looser of the two null
    tags (a value null at either side must inhabit the union). -/
def looserNull : NullTag -> NullTag -> NullTag
  | .nullable, _ => .nullable
  | _, .nullable => .nullable
  | .val, .val => .val
  | .null, .null => .null
  | .val, .null => .nullable
  | .null, .val => .nullable

def sortUnion (t1 t2 : GSort) : GSort :=
  if t1 == t2 then t1
  else
    -- If either is an empty type former, the other dominates
    match t1.shape, t2.shape with
    | .emptyFormer _ _, _ => t2
    | _, .emptyFormer _ _ => t1
    | .bot, _ => t2
    | _, .bot => t1
    -- the empty union admits nothing, so it is a bottom and is dominated.
    | .union [], _ => t2
    | _, .union [] => t1
    -- `any` is the top type, so it absorbs the union (least upper bound).
    | .any, _ => GSort.any
    | _, .any => GSort.any
    -- The null type ? unions into the other component, making it nullable.
    | .nullType, _ => t2.toNullable
    | _, .nullType => t1.toNullable
    | .single s1, .single s2 => GSort.mk (.union [s1, s2]) .nullable
    | .union ts1, .single s2 =>
      if ts1.any (fun x => x == s2) then GSort.mk (.union ts1) (looserNull t1.null t2.null)
      else GSort.mk (.union (ts1 ++ [s2])) .nullable
    | .single s1, .union ts2 =>
      if ts2.any (fun x => x == s1) then GSort.mk (.union ts2) (looserNull t1.null t2.null)
      else GSort.mk (.union (s1 :: ts2)) .nullable
    | .union ts1, .union ts2 =>
      let merged := ts1 ++ ts2.filter (fun t => !ts1.any (fun x => x == t))
      GSort.mk (.union merged) .nullable
    -- incompatible kinds (e.g. a list vs a node): the only expressible upper
    -- bound is the top type.
    | _, _ => GSort.any

/-! ## Sort Intersection: t1 inter t2 (Paper Definition 3.2)
  Used in join for shared variables.
  Computes the greatest lower bound without introducing new type constructors.
  Key: emptyFormer inter anything = emptyFormer (propagate emptiness)
  Key: nodeRefined G ss1 inter nodeRefined G ss2 = nodeRefined G (ss1 cap ss2) -/

/-- Pick the tighter null tag (greatest lower bound in the null lattice).
  val <: nullable, null <: nullable. val and null are incomparable.
  (Not `private`: the meet-admissibility lemma for join soundness reasons about
   `sortInter`, whose result null tag is `tighterNull`, so the proof must reduce it.) -/
def tighterNull : NullTag -> NullTag -> NullTag
  | .val, _        => .val
  | _, .val        => .val
  | .null, _       => .null
  | _, .null       => .null
  | .nullable, .nullable => .nullable

/- MATCH (a)-[r1]->(b), (a)-[r2]->(c) -/
def sortInter (t1 t2 : GSort) : GSort :=
  if t1 == t2 then t1
  else
    -- Empty type former propagates (Paper Section 4.4)
    match t1.shape, t2.shape with
    | .emptyFormer _ _, _ => t1
    | _, .emptyFormer _ _ => t2
    | .bot, _ => t1
    | _, .bot => t2
    | _, _ =>
      let n := tighterNull t1.null t2.null
      if t1.shape == t2.shape then
        -- Same shape, different null tags: pick tighter
        GSort.mk t1.shape n
      else
        match t1.shape, t2.shape with
        -- Schema-refined node types: intersect schema lists (Intersect rule)
        | .single (.nodeRefined G ss1), .single (.nodeRefined G' ss2) =>
          if G == G' then
            let common := ss1.filter (fun s => ss2.any (fun s' => s == s'))
            if common.isEmpty then GSort.nodeEmpty G
            else GSort.mk (.single (.nodeRefined G common)) n
          else GSort.botSort
        -- Refined <: unrefined => Intersect-L: result is the refined type
        | .single (.nodeRefined G _), .single (.node G') =>
          if G == G' then GSort.mk t1.shape n else GSort.botSort
        -- Symmetric: Intersect-R
        | .single (.node G), .single (.nodeRefined G' _) =>
          if G == G' then GSort.mk t2.shape n else GSort.botSort
        -- Schema-refined edge types: intersect schema lists
        | .single (.edgeRefined G ss1), .single (.edgeRefined G' ss2) =>
          if G == G' then
            let common := ss1.filter (fun s => ss2.any (fun s' => s == s'))
            if common.isEmpty then GSort.edgeEmpty G
            else GSort.mk (.single (.edgeRefined G common)) n
          else GSort.botSort
        -- Refined <: unrefined => Intersect-L
        | .single (.edgeRefined G _), .single (.edge G') =>
          if G == G' then GSort.mk t1.shape n else GSort.botSort
        -- Symmetric: Intersect-R
        | .single (.edge G), .single (.edgeRefined G' _) =>
          if G == G' then GSort.mk t2.shape n else GSort.botSort
        -- Fallback: no common subtype
        | _, _ => GSort.botSort

/-! ## Schema Union: Gamma1 union Gamma2 (Paper Definition 3.4) -/

def schemaUnion (Ctx1 Ctx2 : RecordSchema) : RecordSchema :=
  RecordSchema.mk (Ctx1.entries.map fun (x, t1) =>
    match Ctx2.lookup x with
    | some t2 => (x, sortUnion t1 t2)
    | none => (x, t1))

/-! ## Disjoint Union: Gamma1 squnion Gamma2 -/

def disjointUnion (Ctx1 Ctx2 : RecordSchema) : RecordSchema :=
  RecordSchema.mk (Ctx1.entries ++ Ctx2.entries)

/-! ## Join: Gamma1 join Gamma2 (Paper Definition 3.4) -/

def join (Ctx1 Ctx2 : RecordSchema) : RecordSchema :=
  let onlyIn1 := Ctx1.entries.filter (fun e => !Ctx2.mem e.1)
  let onlyIn2 := Ctx2.entries.filter (fun e => !Ctx1.mem e.1)
  let shared := Ctx1.entries.filterMap (fun (x, t1) =>
    match Ctx2.lookup x with
    | some t2 => some (x, sortInter t1 t2)
    | none => none)
  RecordSchema.mk (onlyIn1 ++ shared ++ onlyIn2)

/-! ## Quantifier Lifting (Paper Definition 4.2)
  Gamma^uparrow_K(x) = List Gamma(x)   if K in {*, +, {i,j}, {i}}
  Gamma^uparrow_K(x) = Gamma(x)?       if K = ?
-/


/- MATCH (a)-[e*1..3]->(b) the variable will repeat showup -/
def liftToGroupRef (Ctx : RecordSchema) (vars : List Name) : RecordSchema :=
  RecordSchema.mk (Ctx.entries.map fun (x, t) =>
    if vars.any (fun v => v == x) then (x, t.liftToList)
    else (x, t))

/- optional match, if not match, use nullable -/
def liftToNullable (Ctx : RecordSchema) (vars : List Name) : RecordSchema :=
  RecordSchema.mk (Ctx.entries.map fun (x, t) =>
    if vars.any (fun v => v == x) then (x, t.toNullable)
    else (x, t))

/-! ## Record Conformance (Paper Definition 6.2) -/

/- place whre static analysis and dynamic true value coincide. -/
def valueAdmissible (v : Value) (t : GSort) : Bool :=
  -- Empty type former admits nothing (binding is definitely absent)
  match t.shape with
  | .emptyFormer _ _ => false
  | .bot => false
  -- Empty union is the empty type: it admits nothing, not even null.
  -- (For non-null values `ts.any` already yields false on []; this guard
  --  extends that to null so that `∪[]` behaves like ⊥, restoring
  --  monotonicity of admissibility under subtyping.)
  | .union [] => false
  | _ =>
    match v, t.null with
    | .null, .nullable => true
    | .null, .null     => true
    | .null, .val      => match t.shape with
      | .nullType => true   -- ? admits Null
      | .any => true        -- Any admits Null (Paper: ? <: Any)
      | _ => false
    | _, .null         => false
    | v, _  =>
      match t.shape with
      | .single es => v.hasExtSort "" es
      | .union ts  => ts.any (fun es => v.hasExtSort "" es)
      | .list _ _  => match v with
        | .list _ => true
        | _ => false
      | .any       => true
      | .nullType  => false   -- ? only admits Null
      | _ => false

/- check all the elements in BindingTable and check the variable's type -/
def bindingTableConforms (B : BindingTable) (Ctx : RecordSchema) : Bool :=
  B.all fun rho =>
    Ctx.entries.all fun (x, t) =>
      valueAdmissible (rho.lookup x) t

/-! ## Join Compatibility (Paper Definition 3.4) -/

def sortNullPair (t1 t2 : GSort) : Bool :=
  t1.shape == t2.shape && t1 != t2 &&
  ((t1.null == .val && t2.null == .null) ||
   (t1.null == .null && t2.null == .val) ||
   (t1.null == .val && t2.null == .nullable) ||
   (t1.null == .nullable && t2.null == .val))


/- Two schemas may differ on which variables they bind, but on a shared
   variable the paper (Def. Record Schema Join Compatibility, Sec. on subtyping)
   requires the two types to have a NON-EMPTY meet: Gamma1(x) ∩ Gamma2(x) ≠ ∅.
   `sortInter` computes the meet, and it yields a bottom (⊥) or an empty type
   former exactly when the intersection is empty -- incompatible element kinds,
   a mismatched graph site, or DISJOINT schema lists (e.g. N⟨G,{Person}⟩ vs
   N⟨G,{Company}⟩). Rejecting those is what excludes joins on which no value
   could conform; checking only kind-compatibility (the previous behaviour) was
   strictly weaker than the paper and admitted unsatisfiable joins. -/
/-- Underlying element sort of a shape, peeling an empty-type former. -/
def peelExt : SortShape -> Option ExtSort
  | .single es => some es
  | .emptyFormer (.single es) _ => some es
  | _ => none

def isNodeKind (t : GSort) : Bool :=
  match peelExt t.shape with
  | some (.node _) => true
  | some (.nodeRefined _ _) => true
  | _ => false

def isEdgeKind (t : GSort) : Bool :=
  match peelExt t.shape with
  | some (.edge _) => true
  | some (.edgeRefined _ _) => true
  | _ => false

/-- Paper join-compatibility kind condition: both node-kinded or both
    edge-kinded (`Gamma1(x) <: N<-> (or E<->)` and likewise for `Gamma2(x)`). -/
def sameKind (t1 t2 : GSort) : Bool :=
  (isNodeKind t1 && isNodeKind t2) || (isEdgeKind t1 && isEdgeKind t2)

/-- Join compatibility (Paper Def.): for every shared variable the two sorts
    are the same kind and their meet is not bottom. An empty type former is a
    permitted meet -- it is not bottom -- and the joined table is then provably
    empty, since no graph element inhabits an empty former. -/
def joinCompatible (Ctx1 Ctx2 : RecordSchema) : Bool :=
  let shared := Ctx1.dom.filter (fun x => Ctx2.dom.any (fun y => y == x))
  shared.all fun x =>
    match Ctx1.lookup x, Ctx2.lookup x with
    | some t1, some t2 =>
      -- Paper Def 3.4: same-kind subtyping (N<G>/E<G>) with non-bottom meet.
      -- Same-kind empty-former meets are accepted (Example 3.2); the joined table
      -- is then provably empty (soundness via the empty-former-meet vacuity).
      sameKind t1 t2 && !(sortInter t1 t2).isBot
    | _, _ => false

/-! ## Disjoint Union Compatibility (Paper Definition 3.4) -/

def disjointUnionCompatible (Ctx1 Ctx2 : RecordSchema) : Bool :=
  let d1 := Ctx1.dom
  let d2 := Ctx2.dom
  d1.all (fun x => !d2.any (fun y => y == x))

/-! ## Union Compatibility (Paper Definition 3.4) -/

def unionCompatible (Ctx1 Ctx2 : RecordSchema) : Bool :=
  let d1 := Ctx1.dom
  let d2 := Ctx2.dom
  d1.length == d2.length &&
  d1.all (fun x => d2.any (fun y => y == x)) &&
  d2.all (fun x => d1.any (fun y => y == x))

end RecordSchema

end MGQL
