# How to Check Your Own GQL Query

This guide walks through type checking and semantically checking a GQL
query of your own with the MGQL mechanization, end to end. Everything
below is plain Lean that you can put in a new file (say `MyQuery.lean`
at the repository root, next to `MGQL.lean`) and check with

```
lake env lean MyQuery.lean
```

after a one-time `lake build`. The guide itself is tested: the complete
file assembled from the snippets below elaborates cleanly and produces
exactly the outputs shown.

The file starts with:

```lean
import MGQL.TypeChecker
import MGQL.SmallStep

open MGQL
```

`MGQL.TypeChecker` brings in the executable checker (and, transitively,
the syntax, typing rules, evaluator, and soundness theorems);
`MGQL.SmallStep` adds the second engine.

## Step 1: encode your graph and its schema

A property graph is a `PropertyGraph`: node/edge counts, endpoint
functions, directionality, labels, and property maps. A schema is a
`GraphSchemaFull`: the admissible node and edge schemas. Here is a
two-person graph, Ada −KNOWS→ Bo:

```lean
def myPersonNS : NodeSchemaFull :=
  { labels := ["Person"], propSchema := [("name", .string), ("age", .int)] }

def myKnowsES : EdgeSchemaFull :=
  { labels := ["KNOWS"], srcSchema := myPersonNS, dstSchema := myPersonNS
    propSchema := [], isDirected := true }

def mySchema : GraphSchemaFull :=
  { nodeSchemas := [myPersonNS], edgeSchemas := [myKnowsES] }

def myGraph : PropertyGraph := {
  numNodes := 2
  numEdges := 1
  src := fun _ => Fin.mk 0 (by omega)
  dst := fun _ => Fin.mk 1 (by omega)
  edgeDirected := fun _ => true
  nodeLabels := fun _ => ["Person"]
  edgeLabels := fun _ => ["KNOWS"]
  nodeProps := fun n => match n.val with
    | 0 => [("name", .ofString "Ada"), ("age", .ofInt 36)]
    | _ => [("name", .ofString "Bo"), ("age", .ofInt 25)]
  edgeProps := fun _ => []
}
```

You can confirm that your graph conforms to your schema
(Definition 2.3 of the paper) before doing anything else:

```lean
#eval graphConformsSchema myGraph mySchema    -- true
```

If this prints `false`, fix the graph or the schema first: the
conformance premise is what the soundness theorems assume about the
data. Conformance requires each node's and edge's label set to be
set-equal to some schema's, property keys to agree exactly, and edge
endpoints to match the declared endpoint schemas.

## Step 2: build the typing context

A `TypingCtx` bundles the catalog (graph names to graphs), the schema
map (graph names to schemas, for closed sites), and the current
working site:

```lean
def myCtx : TypingCtx :=
  { catalog := [("g", myGraph)], schemaMap := [("g", mySchema)], graphSite := "g" }
```

Listing `"g"` in the schema map makes it a *closed* site: the checker
will refine types through the schema (precise property types, endpoint
pruning). Omit the entry to model an *open* site, where property
accesses get the permissive scalar union instead.

## Step 3: write the query

Queries are terms of the `Query` type, mirroring the paper's grammar
(Figure 2). The GQL query

```
USE g
MATCH (a:Person)-[k:KNOWS]->(b:Person)
WHERE a.age > 30
RETURN b.name AS friend
```

is encoded as:

```lean
def myQuery : Query :=
  .useGraph "g" (.matchWhere
    (.edge { var := "a", labels := some (.atom "Person") }
          { var := "k", labels := some (.atom "KNOWS") }
          .right
          { var := "b", labels := some (.atom "Person") })
    (.relOp .gt (.propAccess "a" "age") (.const (.int 30)))
    [.alias' (.propAccess "b" "name") "friend"])
```

The correspondence between GQL surface constructs and constructors:

| GQL | Lean encoding |
|---|---|
| `USE g Q` | `.useGraph "g" Q` |
| `MATCH p RETURN μ` | `.matchReturn p μ` |
| `MATCH p WHERE φ RETURN μ` | `.matchWhere p φ μ` |
| `q UNION Q`, `q OTHERWISE Q`, ... | `.composite .union q Q`, `.composite .otherwise q Q`, ... |
| `(x:l {k: c})` node atom | `{ var := "x", labels := some l, props := [{key := "k", val := c}] }` |
| `-[x:l]->`, `<-[x]-`, `~[x]~`, ... | edge atom + `Direction` (`.right`, `.left`, `.undirected`, `.anyDirected`, `.rightOrUndirected`, `.leftOrUndirected`, `.any`) |
| pattern step `P -[..]-> (n)` | `.step P edgeAtom dir nodeAtom` (or `.edge n1 e dir n2` for a single step) |
| quantifiers `*`, `+`, `?`, `{i}`, `{i,j}` | `quantifier := .star / .plus / .question / .exact i / .range i j` on the edge atom, or `.quantified P K` for `(P)K` |
| pattern conjunction `p, P` | `.patternList p P` (left-nested) |
| labels `l & l`, `l \| l`, `!l`, `%` | `.conj`, `.disj`, `.neg`, `.wildcard` in `LabelExpr` |
| `a.k`, constants, `+ - * /` | `.propAccess "a" "k"`, `.const (.int n / .string s / .bool b)`, `.arithOp` |
| `COUNT(e)`, `SUM/MAX/MIN`, `DISTINCT/ALL` | `.agg .count/.sum/.max/.min .default/.distinct/.all e` |
| predicates `< <= > >= = <>`, `AND OR NOT`, `IS NULL` | `.relOp`, `.and`, `.or`, `.not`, `.isNull` in `Pred` |
| `ϑ AS x` / bare `x` in RETURN | `.alias' ϑ "x"` / `.expr (.var "x")`; `.aggAs op qual e "y"` for a top-level aggregate |

Anonymous variables must be given explicit fresh names (for example
`"_e1"`); the paper's renaming rules are applied at encoding time.

## Step 4: type-check it

`inferQuery` computes the result schema, or `none` if the query is
rejected:

```lean
#eval (inferQuery myCtx myQuery).map (·.entries)
-- some [("friend",
--   { shape := MGQL.SortShape.single (MGQL.ExtSort.scalar (MGQL.BaseSort.string)),
--     null := MGQL.NullTag.nullable })]
```

The result schema says the output has one column `friend` of sort `S?`
(nullable string), the precise type recovered from the Person schema
through the closed site. To make acceptance a machine-checked fact
that fails the build when violated:

```lean
example : (inferQuery myCtx myQuery).isSome = true := by native_decide
```

For a composite query that must use a single set operator throughout
(the paper's single-operator judgment ⊢⊛), use
`inferCompQuery myCtx op q` instead.

What acceptance means: `inferQuery_sound` (`TypeChecker.lean`) proves
that every accepted query is well typed in the declarative system at
the inferred schema. The checker is sound but not complete, so a
`none` result does not prove your query untypable; but for queries in
the fragment written in the style above, the checker follows the same
derivations the typing rules do.

## Step 5: run it and check the semantics

Evaluate with the executable semantics:

```lean
#eval evalQuery myCtx.catalog myGraph "g" myQuery
-- [[("friend", MGQL.Value.prim (MGQL.PrimValue.string "Bo"))]]
```

Check that the result table conforms to the inferred schema. The
theorem `inferQuery_conforms` guarantees this in general (given graph
conformance and value well-formedness); on your concrete query it is
also directly decidable:

```lean
example : RecordSchema.bindingTableConforms
    (evalQuery myCtx.catalog myGraph "g" myQuery)
    ((inferQuery myCtx myQuery).getD RecordSchema.empty) = true := by native_decide
```

And run the same query on the small-step engine, which is proven to
agree with the evaluator (`runQuery_engine_agnostic`):

```lean
example : runQuery .smallStep myCtx.catalog myGraph "g" myQuery
    = runQuery .bigStep myCtx.catalog myGraph "g" myQuery := by native_decide
```

## The supported fragment

Queries built from the constructs in the table above are in the
fragment: `USE`/`MATCH`/`WHERE`/`RETURN` with path patterns (all seven
edge directions, label expressions, property constraints, quantified
edges and paths, pattern conjunction), Kleene three-valued predicates
with aggregates, projections with aliases and aggregation, and
composite queries under `UNION`, `OTHERWISE`, `EXCEPT [ALL]`, and
`INTERSECT [ALL]`. Features outside the fragment include `WITH`
pipelining, `OPTIONAL MATCH`, `ORDER BY`/`LIMIT`, and shortest-path
constructs.
