/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Schema.lean -- Property schemas, graph schemas, property graphs, catalog,
                 schema conformance, label-based filtering

  Reference: Paper Definitions 2.1-2.4, Section 4.1 (Sch-Lbl-*, Prp-*)

  Changes from v2:
  - PropSchema, NodeSchemaFull, EdgeSchemaFull moved to Sorts.lean
    (to avoid circular dependency: types embed schema content directly)
  - PropConstraint now uses Literal (matching paper _M ::= x:c)
  - Added propConstraintSchema (Prp-Empty, Prp-Atom, Prp-Insert rules)
-/
import MGQL.Sorts
import MGQL.Values
import MGQL.Syntax

namespace MGQL

/-! ## PropSchema namespace (operations on PropSchema = List (Prod Name BaseSort))
  The type itself is defined in Sorts.lean. -/

namespace PropSchema

def keys (Phi : PropSchema) : List Name := Phi.map Prod.fst

def lookup (Phi : PropSchema) (p : Name) : Option BaseSort :=
  match Phi.find? (fun e => e.1 == p) with
  | some (_, t) => some t
  | none => none

def dom (Phi : PropSchema) : List Name := Phi.map Prod.fst

def isEmpty (Phi : PropSchema) : Bool := Phi.length == 0

def compatibleWith (Phi1 Phi2 : PropSchema) : Bool :=
  Phi1.all fun (k, t) =>
    match Phi2.lookup k with
    | some t' => t == t'
    | none => true

end PropSchema

/-! ## Graph Schema (Paper Definition 3.2(4))
  NodeSchemaFull and EdgeSchemaFull are defined in Sorts.lean. -/

structure GraphSchemaFull where
  nodeSchemas : List NodeSchemaFull
  edgeSchemas : List EdgeSchemaFull
  deriving Repr

namespace GraphSchemaFull

def allNodeSchemas (Psi : GraphSchemaFull) : List NodeSchemaFull := Psi.nodeSchemas
def allEdgeSchemas (Psi : GraphSchemaFull) : List EdgeSchemaFull := Psi.edgeSchemas

end GraphSchemaFull

/-! ## Property Maps -/

abbrev PropMap := List (Prod Name Value)

namespace PropMap

def lookup (pm : PropMap) (key : Name) : Value :=
  match pm.find? (fun e => e.1 == key) with
  | some (_, v) => v
  | none => .null

def lookupOpt (pm : PropMap) (key : Name) : Option Value :=
  match pm.find? (fun e => e.1 == key) with
  | some (_, v) => some v
  | none => none

def dom (pm : PropMap) : List Name := pm.map Prod.fst

def isEmpty (pm : PropMap) : Bool := pm.length == 0

end PropMap

/-! ## Property Graph (Paper Definition 3.1) -/

structure PropertyGraph where
  numNodes      : Nat
  numEdges      : Nat
  src           : Fin numEdges -> Fin numNodes
  dst           : Fin numEdges -> Fin numNodes
  edgeDirected  : Fin numEdges -> Bool
  nodeLabels    : Fin numNodes -> List Name
  edgeLabels    : Fin numEdges -> List Name
  nodeProps     : Fin numNodes -> PropMap
  edgeProps     : Fin numEdges -> PropMap

namespace PropertyGraph

def nodeLabelSet (G : PropertyGraph) (n : Fin G.numNodes) : List Name :=
  G.nodeLabels n

def edgeLabelSet (G : PropertyGraph) (e : Fin G.numEdges) : List Name :=
  G.edgeLabels e

def nodePropertyMap (G : PropertyGraph) (n : Fin G.numNodes) : PropMap :=
  G.nodeProps n

def edgePropertyMap (G : PropertyGraph) (e : Fin G.numEdges) : PropMap :=
  G.edgeProps e

def isEdgeDirected (G : PropertyGraph) (e : Fin G.numEdges) : Bool :=
  G.edgeDirected e

def undirectedEndpoints (G : PropertyGraph) (e : Fin G.numEdges) :
    Prod (Fin G.numNodes) (Fin G.numNodes) :=
  let s := G.src e
  let d := G.dst e
  if s.val <= d.val then (s, d) else (d, s)

end PropertyGraph

/-! ## Property Schema Conformance (Paper Definition 2.3) -/

/- check the property map of a node is consistant with schema -/
def propMapConformsSchema (pm : PropMap) (Phi : PropSchema) : Bool :=
  let pmKeys := pm.dom
  let schKeys := Phi.dom
  pmKeys.length == schKeys.length &&
  pmKeys.all (fun k => schKeys.any (fun x => x == k)) &&
  schKeys.all (fun k => pmKeys.any (fun x => x == k)) &&
  Phi.all fun (k, t) =>
    match pm.lookupOpt k with
    | some v => v.conformsToBase t
    | none => false

/-! ## Node Conformance (Paper Definition 2.3) -/

def nodeConformsSchema (G : PropertyGraph) (n : Fin G.numNodes)
    (ns : NodeSchemaFull) : Bool :=
  let nodeLabels := G.nodeLabels n
  nodeLabels.length == ns.labels.length &&
  nodeLabels.all (fun l => ns.labels.any (fun x => x == l)) &&
  ns.labels.all (fun l => nodeLabels.any (fun x => x == l)) &&
  propMapConformsSchema (G.nodeProps n) ns.propSchema

/-! ## Edge Conformance (Paper Definition 2.3) -/

def edgeConformsSchema (G : PropertyGraph) (e : Fin G.numEdges)
    (es : EdgeSchemaFull) : Bool :=
  let edgeLabels := G.edgeLabels e
  edgeLabels.length == es.labels.length &&
  edgeLabels.all (fun l => es.labels.any (fun x => x == l)) &&
  es.labels.all (fun l => edgeLabels.any (fun x => x == l)) &&
  propMapConformsSchema (G.edgeProps e) es.propSchema &&
  (G.edgeDirected e == es.isDirected) &&
  (if G.edgeDirected e then
    nodeConformsSchema G (G.src e) es.srcSchema &&
    nodeConformsSchema G (G.dst e) es.dstSchema
  else
    let s := G.src e
    let d := G.dst e
    (nodeConformsSchema G s es.srcSchema && nodeConformsSchema G d es.dstSchema) ||
    (nodeConformsSchema G d es.srcSchema && nodeConformsSchema G s es.dstSchema))

/-! ## Graph Conformance (Paper Definition 2.3) -/

def graphConformsSchema (G : PropertyGraph) (Psi : GraphSchemaFull) : Bool :=
  (List.range G.numNodes).all (fun i =>
    if h : i < G.numNodes then
      let n : Fin G.numNodes := Fin.mk i h
      Psi.nodeSchemas.any (fun ns => nodeConformsSchema G n ns)
    else true) &&
  (List.range G.numEdges).all (fun i =>
    if h : i < G.numEdges then
      let e : Fin G.numEdges := Fin.mk i h
      Psi.edgeSchemas.any (fun es => edgeConformsSchema G e es)
    else true)

/-! ## Property Constraint Typing (Paper Section 4.1: Prp-Empty, Prp-Atom, Prp-Insert)
  |-_Prp Pi |= Phi
  Derives a PropSchema from a list of property constraints. -/

def literalBaseSort : Literal -> BaseSort
  | .int _    => .int
  | .string _ => .string
  | .bool _   => .bool

/-- Derive property schema from property constraints (Prp-Empty, Prp-Atom, Prp-Insert) -/
/- {age: 18, name: "Alice" -/
def propConstraintSchema (pcs : List PropConstraint) : PropSchema :=
  pcs.map fun pc => (pc.key, literalBaseSort pc.val)

/-! ## Schema Filtering (Paper Section 4.1: Sch-L-*, Sch-Prp-*) -/

/-- Sch-Lbl-Atom: filter node schemas whose label set contains label l -/
/- MATCH (n:Person) -/
def filterNodeSchemasByLabel (schemas : List NodeSchemaFull) (l : Name) :
    List NodeSchemaFull :=
  schemas.filter (fun ns => ns.labels.any (fun x => x == l))

def filterEdgeSchemasByLabel (schemas : List EdgeSchemaFull) (l : Name) :
    List EdgeSchemaFull :=
  schemas.filter (fun es => es.labels.any (fun x => x == l))

/-- Sch-Lbl-Wildcard: filter schemas with non-empty label sets -/
def filterNodeSchemasNonEmpty (schemas : List NodeSchemaFull) :
    List NodeSchemaFull :=
  schemas.filter (fun ns => !ns.labels.isEmpty)

def filterEdgeSchemasNonEmpty (schemas : List EdgeSchemaFull) :
    List EdgeSchemaFull :=
  schemas.filter (fun es => !es.labels.isEmpty)

/-- Sch-Prp-Atom: filter schemas whose property schema is compatible with Phi -/
/- MATCH (n:Person {age: 18}) -/
def filterNodeSchemasByPropCompat (schemas : List NodeSchemaFull)
    (propKeys : List (Prod Name BaseSort)) : List NodeSchemaFull :=
  schemas.filter fun ns =>
    propKeys.all fun (k, t) =>
      match ns.propSchema.lookup k with
      | some t' => t == t'
      | none => false

def filterEdgeSchemasByPropCompat (schemas : List EdgeSchemaFull)
    (propKeys : List (Prod Name BaseSort)) : List EdgeSchemaFull :=
  schemas.filter fun es =>
    propKeys.all fun (k, t) =>
      match es.propSchema.lookup k with
      | some t' => t == t'
      | none => false

/-! ## Endpoint Refinement helpers (Paper Section 4.1) -/
/- MATCH (n)-[e:WORKS_AT]->(...) -/
def refineNodeSchemasBySrc (nodeSchemas : List NodeSchemaFull)
    (edgeSchemas : List EdgeSchemaFull) :
    Prod (List NodeSchemaFull) (List EdgeSchemaFull) :=
  let pairs := edgeSchemas.filterMap fun es =>
    if nodeSchemas.any (fun ns =>
      ns.labels == es.srcSchema.labels &&
      ns.propSchema.length == es.srcSchema.propSchema.length)
    then some es
    else none
  let refinedNodes := nodeSchemas.filter fun ns =>
    pairs.any (fun es =>
      ns.labels == es.srcSchema.labels)
  (refinedNodes, pairs)

def refineNodeSchemasByDst (nodeSchemas : List NodeSchemaFull)
    (edgeSchemas : List EdgeSchemaFull) :
    Prod (List NodeSchemaFull) (List EdgeSchemaFull) :=
  let pairs := edgeSchemas.filterMap fun es =>
    if nodeSchemas.any (fun ns =>
      ns.labels == es.dstSchema.labels &&
      ns.propSchema.length == es.dstSchema.propSchema.length)
    then some es
    else none
  let refinedNodes := nodeSchemas.filter fun ns =>
    pairs.any (fun es =>
      ns.labels == es.dstSchema.labels)
  (refinedNodes, pairs)

/-! ## Catalog and Schema Map -/

abbrev Catalog := List (Prod Name PropertyGraph)
abbrev SchemaMap := List (Prod Name GraphSchemaFull)

namespace Catalog

def lookup (C : Catalog) (name : Name) : Option PropertyGraph :=
  match C.find? (fun e => e.1 == name) with
  | some (_, g) => some g
  | none => none

end Catalog

namespace SchemaMap

def lookup (Omega : SchemaMap) (name : Name) : Option GraphSchemaFull :=
  match Omega.find? (fun e => e.1 == name) with
  | some (_, s) => some s
  | none => none

def isClosed (Omega : SchemaMap) (G : GraphSite) : Bool :=
  (Omega.lookup G).isSome

end SchemaMap

/-! ## Label Matching (runtime) -/

def labelSetContains (labels : List Name) (l : Name) : Bool :=
  labels.any (fun x => x == l)

end MGQL
