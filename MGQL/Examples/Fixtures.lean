/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Examples/Fixtures.lean -- the worked graph, schema, and typing contexts
  shared by the kick-the-tires examples
-/
import MGQL.TypeChecker
import MGQL.SmallStep

namespace MGQL.Examples

open MGQL

-- ============================================================
--  A worked property graph: Ada -KNOWS-> Bo -WORKS_ON-> Atlas
-- ============================================================

def egPersonNS : NodeSchemaFull :=
  { labels := ["Person"], propSchema := [("name", .string), ("age", .int)] }

def egProjectNS : NodeSchemaFull :=
  { labels := ["Project"], propSchema := [("title", .string)] }

def egKnowsES : EdgeSchemaFull :=
  { labels := ["KNOWS"], srcSchema := egPersonNS, dstSchema := egPersonNS
    propSchema := [("since", .int)], isDirected := true }

def egWorksES : EdgeSchemaFull :=
  { labels := ["WORKS_ON"], srcSchema := egPersonNS, dstSchema := egProjectNS
    propSchema := [], isDirected := true }

def egSchema : GraphSchemaFull :=
  { nodeSchemas := [egPersonNS, egProjectNS]
    edgeSchemas := [egKnowsES, egWorksES] }

def egGraph : PropertyGraph := {
  numNodes := 3
  numEdges := 2
  src := fun e => match e.val with
    | 0 => Fin.mk 0 (by omega)
    | _ => Fin.mk 1 (by omega)
  dst := fun e => match e.val with
    | 0 => Fin.mk 1 (by omega)
    | _ => Fin.mk 2 (by omega)
  edgeDirected := fun _ => true
  nodeLabels := fun n => match n.val with
    | 0 => ["Person"]
    | 1 => ["Person"]
    | _ => ["Project"]
  edgeLabels := fun e => match e.val with
    | 0 => ["KNOWS"]
    | _ => ["WORKS_ON"]
  nodeProps := fun n => match n.val with
    | 0 => [("name", .ofString "Ada"), ("age", .ofInt 36)]
    | 1 => [("name", .ofString "Bo"), ("age", .ofInt 25)]
    | _ => [("title", .ofString "Atlas")]
  edgeProps := fun e => match e.val with
    | 0 => [("since", .ofInt 2020)]
    | _ => []
}

def egCatalog : Catalog := [("g", egGraph)]

/-- Closed working site: the schema map carries `egSchema` for `g`. -/
def egClosedCtx : TypingCtx :=
  { catalog := egCatalog, schemaMap := [("g", egSchema)], graphSite := "g" }

/-- Open working site: no schema information for `g`. -/
def egOpenCtx : TypingCtx :=
  { catalog := egCatalog, schemaMap := [], graphSite := "g" }

end MGQL.Examples
