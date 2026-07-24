/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Values.lean -- Multi-sorted value universe, Kleene three-valued logic,
                 records, and binding tables

  Reference: Paper Sections 2.1 and 5.1, Figure 2
-/
import MGQL.Sorts

namespace MGQL

/-! ## Values -/

inductive PrimValue where
  | int    : Int -> PrimValue
  | string : String -> PrimValue
  | bool   : Bool -> PrimValue
  deriving DecidableEq, Repr, BEq



mutual
inductive Value where
  | prim     : PrimValue -> Value
  | nodeRef  : GraphSite -> Nat -> Value
  | edgeRef  : GraphSite -> Nat -> Value
  | null     : Value
  | list     : ValueList -> Value
/-
list is used for:
1. Group-reference bindings from quantified patterns (Paper Section 3.3):
   MATCH (start)-[ (x:Person)-[e:KNOWS]-> ]{1,3} (end)
   e = .list [ .edgeRef "g" 2, .edgeRef "g" 5, .edgeRef "g" 7 ]

2. Variable-length path edge collections:
   MATCH (a)-[r:KNOWS*1..3]->(b)
   r = .list [ .edgeRef "g" 0, .edgeRef "g" 3 ]

Used by aggregation in semantics:
   RETURN COUNT(e)
   op = count, inner value is the list
-/

inductive ValueList where
  | nil  : ValueList
  | cons : Value -> ValueList -> ValueList
end

deriving instance DecidableEq for Value
deriving instance DecidableEq for ValueList
deriving instance Repr for Value
deriving instance Repr for ValueList

-- `Value`/`ValueList` are a *mutual* inductive, so `deriving BEq` would produce an
-- opaque, recursively-defined comparison that proofs cannot relate back to `=`
-- (`LawfulBEq` is unprovable for it). Since both already derive `DecidableEq`, we
-- instead define `==` as the decision of `=`. This computes the identical boolean
-- (true iff structurally equal) but is provably lawful, so `agreeOn`/value-equality
-- reasoning in the metatheory (e.g. the join case of pattern soundness) goes through.
instance : BEq Value := ⟨fun a b => decide (a = b)⟩
instance : BEq ValueList := ⟨fun a b => decide (a = b)⟩

instance : LawfulBEq Value where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true (Eq.refl _)

instance : LawfulBEq ValueList where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true (Eq.refl _)

/-! ## ValueList helpers -/

namespace ValueList

def toList : ValueList -> List Value
  | .nil => []
  | .cons v vs => v :: vs.toList

def ofList : List Value -> ValueList
  | [] => .nil
  | v :: vs => .cons v (ofList vs)

def length : ValueList -> Nat
  | .nil => 0
  | .cons _ vs => 1 + vs.length

def map (f : Value -> Value) : ValueList -> ValueList
  | .nil => .nil
  | .cons v vs => .cons (f v) (vs.map f)

def filter (p : Value -> Bool) : ValueList -> ValueList
  | .nil => .nil
  | .cons v vs =>
    if p v then .cons v (vs.filter p) else vs.filter p

def all (p : Value -> Bool) : ValueList -> Bool
  | .nil => true
  | .cons v vs => p v && vs.all p

def any (p : Value -> Bool) : ValueList -> Bool
  | .nil => false
  | .cons v vs => p v || vs.any p

def append : ValueList -> ValueList -> ValueList
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (xs.append ys)

instance : Append ValueList where
  append := ValueList.append

theorem ofList_toList : (vs : ValueList) -> ofList vs.toList = vs
  | .nil => rfl
  | .cons v vs => by simp [toList, ofList, ofList_toList vs]

theorem toList_ofList : (xs : List Value) -> (ofList xs).toList = xs
  | [] => rfl
  | v :: vs => by simp [ofList, toList, toList_ofList vs]

end ValueList

instance : Coe ValueList (List Value) where
  coe := ValueList.toList

instance : Coe (List Value) ValueList where
  coe := ValueList.ofList

namespace PrimValue

def hasSort : PrimValue -> BaseSort -> Bool
  | .int _,    .int    => true
  | .string _, .string => true
  | .bool _,   .bool   => true
  | _,         _       => false

end PrimValue

namespace Value

def ofInt (n : Int) : Value := .prim (.int n)
def ofString (s : String) : Value := .prim (.string s)
def ofBool (b : Bool) : Value := .prim (.bool b)
def ofList (vs : List Value) : Value := .list (ValueList.ofList vs)

def isNull : Value -> Bool
  | .null => true
  | _     => false

def asInt : Value -> Option Int
  | .prim (.int n) => some n
  | _ => none

def asBool : Value -> Option Bool
  | .prim (.bool b) => some b
  | _ => none

def asString : Value -> Option String
  | .prim (.string s) => some s
  | _ => none

def asList : Value -> Option (List Value)
  | .list vs => some vs.toList
  | _ => none

def asValueList : Value -> Option ValueList
  | .list vs => some vs
  | _ => none

def hasBaseSort : Value -> BaseSort -> Bool
  | .prim (.int _),    .int    => true
  | .prim (.string _), .string => true
  | .prim (.bool _),   .bool   => true
  | _,                 _       => false

def hasExtSort : Value -> GraphSite -> ExtSort -> Bool
  | .prim p,          _, .scalar b          => p.hasSort b
  | .nodeRef G' _,    _, .node G            => G' == G
  | .edgeRef G' _,    _, .edge G            => G' == G
  | .nodeRef G' _,    _, .nodeRefined G _   => G' == G
  | .edgeRef G' _,    _, .edgeRefined G _   => G' == G
  | _,                _, _                  => false

end Value

/-! ## Records (Paper Section 5.1) -/

abbrev Record := List (Prod Name Value)

namespace Record

def empty : Record := []

def lookup (rho : Record) (x : Name) : Value :=
  match rho.find? (fun e => e.1 == x) with
  | some (_, v) => v
  | none => .null

def dom (rho : Record) : List Name := rho.map Prod.fst

def mem (rho : Record) (x : Name) : Bool :=
  rho.any (fun e => e.1 == x)

def extend (rho : Record) (x : Name) (v : Value) : Record :=
  rho ++ [(x, v)]

def set (rho : Record) (x : Name) (v : Value) : Record :=
  if rho.mem x
  then rho.map (fun (k, w) => if k == x then (k, v) else (k, w))
  else rho.extend x v

def disjointUnion (rho1 rho2 : Record) : Record := rho1 ++ rho2

def merge (rho1 rho2 : Record) : Record :=
  let extra := rho2.filter (fun e => !rho1.mem e.1)
  rho1 ++ extra

def agreeOn (rho1 rho2 : Record) : Bool :=
  rho1.all fun (x, v) =>
    if rho2.mem x then rho2.lookup x == v else true

def restrict (rho : Record) (xs : List Name) : Record :=
  rho.filter (fun e => xs.any (fun x => x == e.1))

def project (rho : Record) (keys : List Name) : Record :=
  keys.filterMap fun k =>
    match rho.find? (fun e => e.1 == k) with
    | some entry => some entry
    | none => none

end Record

/-! ## Binding Tables (Paper Section 5.1) -/

abbrev BindingTable := List Record

/-! ## Trail-Annotated Binding Tables (Paper Section 5.1)
  A binding table entry is a pair (rho, W) where rho is a record and
  W is the set of edges traversed along the matched path.
  This supports the Trail path mode where each edge may be traversed at most once. -/

abbrev EdgeSet := List Nat

structure TrailEntry where
  record : Record
  visited : EdgeSet
  deriving DecidableEq, Repr, BEq

abbrev TrailBindingTable := List TrailEntry

namespace TrailEntry

/-- Trail product of two entries (Paper Section 5.1):
  (rho1, W1) tensor (rho2, W2) =
    (rho1 join rho2, W1 union W2) if W1 cap W2 = empty
    bot                           otherwise -/
def trailProduct (e1 e2 : TrailEntry) : Option TrailEntry :=
  let disjoint := e1.visited.all (fun w => !e2.visited.any (fun w' => w == w'))
  if disjoint && e1.record.agreeOn e2.record then
    some { record := e1.record.merge e2.record,
           visited := e1.visited ++ e2.visited.filter
             (fun w => !e1.visited.any (fun w' => w == w')) }
  else none

end TrailEntry

namespace TrailBindingTable

/-- Identity element: 1_B = {{([], empty)}} -/
def identity : TrailBindingTable := [{ record := [], visited := [] }]

/-- Trail-aware join: B1 join B2 (Paper Section 5.1)
  B1 join B2 = {{ b1 tensor b2 | b1 in B1, b2 in B2, b1 tensor b2 != bot }} -/
def trailJoin (B1 B2 : TrailBindingTable) : TrailBindingTable :=
  B1.flatMap fun e1 =>
    B2.filterMap fun e2 =>
      e1.trailProduct e2

/-- Conditioned trail join: B1 join_phi B2 -/
def trailJoinCond (B1 B2 : TrailBindingTable)
    (phi : Record -> Bool) : TrailBindingTable :=
  (trailJoin B1 B2).filter fun e => phi e.record

/-- Trail lift eta(B): embed plain records with empty visited sets -/
def trailLift (B : BindingTable) : TrailBindingTable :=
  B.map fun rho => { record := rho, visited := [] }

/-- Edge-annotated trail lift eta_r(B): marks each entry with the edge bound by r -/
def trailLiftEdge (B : BindingTable) (r : Name) : TrailBindingTable :=
  B.filterMap fun rho =>
    match rho.lookup r with
    | .edgeRef _ eid => some { record := rho, visited := [eid] }
    | _ => some { record := rho, visited := [] }

/-- Selection sigma_phi(B) -/
def trailSelect (B : TrailBindingTable) (phi : Record -> Bool) : TrailBindingTable :=
  B.filter fun e => phi e.record

/-- Bag union -/
def trailUnion (B1 B2 : TrailBindingTable) : TrailBindingTable := B1 ++ B2

/-- Strip trail annotations to get plain binding table -/
def stripTrail (B : TrailBindingTable) : BindingTable :=
  B.map fun e => e.record

end TrailBindingTable

/-! ## Kleene Three-Valued Logic (Paper Figure 2) -/

namespace Kleene

def neg : Option Bool -> Option Bool
  | some b => some (!b)
  | none   => none

def and : Option Bool -> Option Bool -> Option Bool
  | some false, _          => some false
  | _, some false          => some false
  | some true, some true   => some true
  | _, _                   => none

def or : Option Bool -> Option Bool -> Option Bool
  | some true, _           => some true
  | _, some true           => some true
  | some false, some false => some false
  | _, _                   => none

def eq (a b : Option Value) : Option Bool :=
  match a, b with
  | some va, some vb =>
    if va == .null || vb == .null then none
    else some (va == vb)
  | _, _ => none

theorem neg_neg (v : Option Bool) : neg (neg v) = v := by
  cases v with
  | none => rfl
  | some b => cases b <;> rfl

theorem and_comm (a b : Option Bool) : Kleene.and a b = Kleene.and b a := by
  cases a with
  | none => cases b with
    | none => rfl
    | some b => cases b <;> rfl
  | some a => cases b with
    | none => cases a <;> rfl
    | some b => cases a <;> cases b <;> rfl

theorem or_comm (a b : Option Bool) : Kleene.or a b = Kleene.or b a := by
  cases a with
  | none => cases b with
    | none => rfl
    | some b => cases b <;> rfl
  | some a => cases b with
    | none => cases a <;> rfl
    | some b => cases a <;> cases b <;> rfl

end Kleene

def Value.conformsToBase : Value -> BaseSort -> Bool
  | .prim p, t => p.hasSort t
  | _, _       => false

end MGQL
