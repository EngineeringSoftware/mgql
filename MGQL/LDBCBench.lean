/-
  MGQL: Mechanized GQL Semantics in Lean 4
  LDBCBench.lean -- LDBC SNB Interactive v2 benchmark evaluation

  Encodes the subset of LDBC SNB Interactive Cypher queries that fall
  within the formalized GQL fragment (Paper Figure 2) and runs them
  through the executable denotational semantics (evalQuery) to measure
  execution time.

  LDBC SNB schema reference:
    https://github.com/ldbc/ldbc_snb_interactive_v2_impls

  Coverage summary (14 complex + 7 short = 21 read queries):
    Expressible (core MATCH...WHERE...RETURN):
      IS1  -- Profile of a person          (single directed edge + property access)
      IS3  -- Friends of a person          (undirected KNOWS edge)
      IS4  -- Content of a message         (single node match + property access)
      IS5  -- Creator of a message         (single directed edge)
      IC8  -- Recent replies               (multi-hop directed chain, 3 edges)
      IC2  -- Recent messages by friends   (2-hop chain + WHERE filter) [core only]
    Not expressible (require features outside formalized fragment):
      IS2  -- WITH, ORDER BY, LIMIT, variable-length path *0..
      IS6  -- variable-length path *0..
      IS7  -- OPTIONAL MATCH, CASE
      IC1  -- shortestPath, WITH, OPTIONAL MATCH, CASE, COLLECT
      IC3  -- WITH, COLLECT, IN, CASE
      IC4  -- WITH, CASE
      IC5  -- WITH, OPTIONAL MATCH, COLLECT
      IC6  -- WITH, UNWIND, COLLECT
      IC7  -- WITH, head, COLLECT, map projections
      IC9  -- WITH, UNWIND, COLLECT
      IC10 -- WITH, OPTIONAL MATCH, datetime, COLLECT
      IC11 -- WITH DISTINCT (partial: quantified path *1..2 IS supported)
      IC12 -- WITH, COLLECT, IS_SUBCLASS_OF*0.., collect(DISTINCT)
      IC13 -- shortestPath, CASE
      IC14 -- GDS library (not GQL at all)
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

namespace MGQL.LDBCBench

open MGQL

-- ============================================================
--  1. LDBC SNB Graph Schema
--     Node labels: Person, Message, Comment, Post, City, Country,
--                  Forum, Tag, TagClass, University, Company
--     Edge labels: KNOWS, IS_LOCATED_IN, HAS_CREATOR, REPLY_OF,
--                  HAS_TAG, HAS_MEMBER, CONTAINER_OF, HAS_MODERATOR,
--                  LIKES, STUDY_AT, WORK_AT, IS_PART_OF, HAS_TYPE,
--                  IS_SUBCLASS_OF, HAS_INTEREST
-- ============================================================

-- Node schemas (label, property schema)
def personNS : NodeSchemaFull :=
  { labels := ["Person"]
    propSchema := [("id", .int), ("firstName", .string), ("lastName", .string),
                   ("gender", .string), ("birthday", .int),
                   ("locationIP", .string), ("browserUsed", .string)] }

-- Plain messages (only the Message label) carry id/creationDate.
def messageNS : NodeSchemaFull :=
  { labels := ["Message"]
    propSchema := [("id", .int), ("creationDate", .int)] }

-- Comments and posts carry the Message label as well (LDBC SNB: Comment and
-- Post are subtypes of Message); Definition 2.3 compares label sets
-- set-equal, so the schema label sets list both labels.
def commentNS : NodeSchemaFull :=
  { labels := ["Comment", "Message"]
    propSchema := [("id", .int), ("creationDate", .int),
                   ("content", .string), ("length", .int)] }

def postNS : NodeSchemaFull :=
  { labels := ["Post", "Message"]
    propSchema := [("id", .int), ("creationDate", .int),
                   ("content", .string), ("length", .int)] }

def cityNS : NodeSchemaFull :=
  { labels := ["City"]
    propSchema := [("id", .int), ("name", .string)] }

def countryNS : NodeSchemaFull :=
  { labels := ["Country"]
    propSchema := [("id", .int), ("name", .string)] }

def forumNS : NodeSchemaFull :=
  { labels := ["Forum"]
    propSchema := [("id", .int), ("title", .string), ("creationDate", .int)] }

def tagNS : NodeSchemaFull :=
  { labels := ["Tag"]
    propSchema := [("id", .int), ("name", .string)] }

-- Edge schemas (label, src, dst, propSchema, isDirected)
def knowsES : EdgeSchemaFull :=
  { labels := ["KNOWS"]
    srcSchema := personNS, dstSchema := personNS
    propSchema := [("creationDate", .int)]
    isDirected := false }  -- KNOWS is undirected in LDBC SNB

def isLocatedInPersonES : EdgeSchemaFull :=
  { labels := ["IS_LOCATED_IN"]
    srcSchema := personNS, dstSchema := cityNS
    propSchema := [], isDirected := true }

def hasCreatorCommentES : EdgeSchemaFull :=
  { labels := ["HAS_CREATOR"]
    srcSchema := commentNS, dstSchema := personNS
    propSchema := [], isDirected := true }

def hasCreatorPostES : EdgeSchemaFull :=
  { labels := ["HAS_CREATOR"]
    srcSchema := postNS, dstSchema := personNS
    propSchema := [], isDirected := true }

-- Every REPLY_OF edge in the instance targets a Post (comments replying to
-- posts), so the declared destination schema is the post schema.
def replyOfES : EdgeSchemaFull :=
  { labels := ["REPLY_OF"]
    srcSchema := commentNS, dstSchema := postNS
    propSchema := [], isDirected := true }

def ldbcSchema : GraphSchemaFull :=
  { nodeSchemas := [personNS, messageNS, commentNS, postNS, cityNS,
                    countryNS, forumNS, tagNS]
    edgeSchemas := [knowsES, isLocatedInPersonES, hasCreatorCommentES,
                    hasCreatorPostES, replyOfES] }

-- ============================================================
--  2. Small LDBC-like Test Graph Instance
--
--  Nodes (20 total):
--    0-4: Person (Alice, Bob, Charlie, Diana, Eve)
--    5-9: Message/Comment
--    10-11: Post
--    12-14: City (Austin, London, Tokyo)
--    15-17: Person (Frank, Grace, Hank) -- more people for richer results
--    18-19: Comment (more replies)
--
--  Edges (20 total):
--    0: Alice  -[:KNOWS]->  Bob        (undirected)
--    1: Alice  -[:KNOWS]->  Charlie    (undirected)
--    2: Bob    -[:KNOWS]->  Diana      (undirected)
--    3: Charlie-[:KNOWS]->  Eve        (undirected)
--    4: Alice  -[:IS_LOCATED_IN]-> Austin
--    5: Bob    -[:IS_LOCATED_IN]-> London
--    6: Charlie-[:IS_LOCATED_IN]-> Tokyo
--    7: Diana  -[:IS_LOCATED_IN]-> Austin
--    8: Comment5 -[:HAS_CREATOR]-> Alice
--    9: Comment6 -[:HAS_CREATOR]-> Bob
--   10: Comment7 -[:HAS_CREATOR]-> Charlie
--   11: Post10   -[:HAS_CREATOR]-> Alice
--   12: Post11   -[:HAS_CREATOR]-> Bob
--   13: Comment5 -[:REPLY_OF]-> Message(Post10)
--   14: Comment6 -[:REPLY_OF]-> Message(Post11)
--   15: Comment7 -[:REPLY_OF]-> Message(Post10)
--   16: Bob   -[:KNOWS]->  Eve        (undirected)
--   17: Diana -[:KNOWS]->  Frank      (undirected)
--   18: Comment18-[:HAS_CREATOR]-> Diana
--   19: Comment18-[:REPLY_OF]-> Message(Post11)
-- ============================================================

def ldbcGraph : PropertyGraph := {
  numNodes := 20
  numEdges := 20
  src := fun e => match e.val with
    -- KNOWS (undirected, stored both ways)
    | 0 => Fin.mk 0 (by omega)    -- Alice
    | 1 => Fin.mk 0 (by omega)    -- Alice
    | 2 => Fin.mk 1 (by omega)    -- Bob
    | 3 => Fin.mk 2 (by omega)    -- Charlie
    -- IS_LOCATED_IN
    | 4 => Fin.mk 0 (by omega)    -- Alice
    | 5 => Fin.mk 1 (by omega)    -- Bob
    | 6 => Fin.mk 2 (by omega)    -- Charlie
    | 7 => Fin.mk 3 (by omega)    -- Diana
    -- HAS_CREATOR
    | 8  => Fin.mk 5 (by omega)   -- Comment5
    | 9  => Fin.mk 6 (by omega)   -- Comment6
    | 10 => Fin.mk 7 (by omega)   -- Comment7
    | 11 => Fin.mk 10 (by omega)  -- Post10
    | 12 => Fin.mk 11 (by omega)  -- Post11
    -- REPLY_OF
    | 13 => Fin.mk 5 (by omega)   -- Comment5
    | 14 => Fin.mk 6 (by omega)   -- Comment6
    | 15 => Fin.mk 7 (by omega)   -- Comment7
    -- more KNOWS
    | 16 => Fin.mk 1 (by omega)   -- Bob
    | 17 => Fin.mk 3 (by omega)   -- Diana
    -- more HAS_CREATOR + REPLY_OF
    | 18 => Fin.mk 18 (by omega)  -- Comment18
    | _ => Fin.mk 18 (by omega)   -- Comment18
  dst := fun e => match e.val with
    | 0 => Fin.mk 1 (by omega)    -- Bob
    | 1 => Fin.mk 2 (by omega)    -- Charlie
    | 2 => Fin.mk 3 (by omega)    -- Diana
    | 3 => Fin.mk 4 (by omega)    -- Eve
    | 4 => Fin.mk 12 (by omega)   -- Austin
    | 5 => Fin.mk 13 (by omega)   -- London
    | 6 => Fin.mk 14 (by omega)   -- Tokyo
    | 7 => Fin.mk 12 (by omega)   -- Austin
    | 8  => Fin.mk 0 (by omega)   -- Alice
    | 9  => Fin.mk 1 (by omega)   -- Bob
    | 10 => Fin.mk 2 (by omega)   -- Charlie
    | 11 => Fin.mk 0 (by omega)   -- Alice
    | 12 => Fin.mk 1 (by omega)   -- Bob
    | 13 => Fin.mk 10 (by omega)  -- Post10 (as Message)
    | 14 => Fin.mk 11 (by omega)  -- Post11 (as Message)
    | 15 => Fin.mk 10 (by omega)  -- Post10 (as Message)
    | 16 => Fin.mk 4 (by omega)   -- Eve
    | 17 => Fin.mk 15 (by omega)  -- Frank
    | 18 => Fin.mk 3 (by omega)   -- Diana
    | _ => Fin.mk 11 (by omega)   -- Post11
  edgeDirected := fun e => match e.val with
    | 0 | 1 | 2 | 3 | 16 | 17 => false  -- KNOWS = undirected
    | _ => true                            -- all others directed
  nodeLabels := fun n => match n.val with
    | 0 | 1 | 2 | 3 | 4 => ["Person"]
    | 5 | 6 | 7           => ["Comment", "Message"]
    | 8 | 9                => ["Message"]
    | 10 | 11              => ["Post", "Message"]
    | 12 | 13 | 14         => ["City"]
    | 15 | 16 | 17         => ["Person"]
    | 18 | 19              => ["Comment", "Message"]
    | _                    => []
  edgeLabels := fun e => match e.val with
    | 0 | 1 | 2 | 3 | 16 | 17 => ["KNOWS"]
    | 4 | 5 | 6 | 7             => ["IS_LOCATED_IN"]
    | 8 | 9 | 10 | 11 | 12 | 18 => ["HAS_CREATOR"]
    | 13 | 14 | 15 | 19         => ["REPLY_OF"]
    | _                          => []
  nodeProps := fun n => match n.val with
    | 0 => [("id", .ofInt 1), ("firstName", .ofString "Alice"),
            ("lastName", .ofString "Smith"), ("gender", .ofString "female"),
            ("birthday", .ofInt 19900101),
            ("locationIP", .ofString "1.2.3.4"), ("browserUsed", .ofString "Firefox")]
    | 1 => [("id", .ofInt 2), ("firstName", .ofString "Bob"),
            ("lastName", .ofString "Jones"), ("gender", .ofString "male"),
            ("birthday", .ofInt 19880515),
            ("locationIP", .ofString "5.6.7.8"), ("browserUsed", .ofString "Chrome")]
    | 2 => [("id", .ofInt 3), ("firstName", .ofString "Charlie"),
            ("lastName", .ofString "Wang"), ("gender", .ofString "male"),
            ("birthday", .ofInt 19951231),
            ("locationIP", .ofString "10.0.0.1"), ("browserUsed", .ofString "Safari")]
    | 3 => [("id", .ofInt 4), ("firstName", .ofString "Diana"),
            ("lastName", .ofString "Lee"), ("gender", .ofString "female"),
            ("birthday", .ofInt 19920620),
            ("locationIP", .ofString "192.168.1.1"), ("browserUsed", .ofString "Edge")]
    | 4 => [("id", .ofInt 5), ("firstName", .ofString "Eve"),
            ("lastName", .ofString "Chen"), ("gender", .ofString "female"),
            ("birthday", .ofInt 20000101),
            ("locationIP", .ofString "10.0.0.2"), ("browserUsed", .ofString "Firefox")]
    -- Comments (5-7)
    | 5 => [("id", .ofInt 100), ("creationDate", .ofInt 1609459200),
            ("content", .ofString "Great post Alice!"), ("length", .ofInt 17)]
    | 6 => [("id", .ofInt 101), ("creationDate", .ofInt 1609545600),
            ("content", .ofString "I agree with you"), ("length", .ofInt 16)]
    | 7 => [("id", .ofInt 102), ("creationDate", .ofInt 1609632000),
            ("content", .ofString "Interesting perspective"), ("length", .ofInt 23)]
    -- Messages (8-9, plain)
    | 8 => [("id", .ofInt 200), ("creationDate", .ofInt 1609200000)]
    | 9 => [("id", .ofInt 201), ("creationDate", .ofInt 1609300000)]
    -- Posts (10-11)
    | 10 => [("id", .ofInt 300), ("creationDate", .ofInt 1609100000),
             ("content", .ofString "Hello world from Alice"), ("length", .ofInt 22)]
    | 11 => [("id", .ofInt 301), ("creationDate", .ofInt 1609150000),
             ("content", .ofString "Tech news roundup"), ("length", .ofInt 17)]
    -- Cities (12-14)
    | 12 => [("id", .ofInt 400), ("name", .ofString "Austin")]
    | 13 => [("id", .ofInt 401), ("name", .ofString "London")]
    | 14 => [("id", .ofInt 402), ("name", .ofString "Tokyo")]
    -- More Persons (15-17)
    | 15 => [("id", .ofInt 6), ("firstName", .ofString "Frank"),
             ("lastName", .ofString "Garcia"), ("gender", .ofString "male"),
             ("birthday", .ofInt 19870301),
             ("locationIP", .ofString "172.16.0.1"), ("browserUsed", .ofString "Chrome")]
    | 16 => [("id", .ofInt 7), ("firstName", .ofString "Grace"),
             ("lastName", .ofString "Kim"), ("gender", .ofString "female"),
             ("birthday", .ofInt 19930815),
             ("locationIP", .ofString "10.1.1.1"), ("browserUsed", .ofString "Safari")]
    | 17 => [("id", .ofInt 8), ("firstName", .ofString "Hank"),
             ("lastName", .ofString "Brown"), ("gender", .ofString "male"),
             ("birthday", .ofInt 19850712),
             ("locationIP", .ofString "10.2.2.2"), ("browserUsed", .ofString "Edge")]
    -- More Comments (18-19)
    | 18 => [("id", .ofInt 103), ("creationDate", .ofInt 1609700000),
             ("content", .ofString "Thanks for sharing"), ("length", .ofInt 18)]
    | 19 => [("id", .ofInt 104), ("creationDate", .ofInt 1609800000),
             ("content", .ofString "Nice thread"), ("length", .ofInt 11)]
    | _ => []
  edgeProps := fun e => match e.val with
    | 0 => [("creationDate", .ofInt 1600000000)]
    | 1 => [("creationDate", .ofInt 1600100000)]
    | 2 => [("creationDate", .ofInt 1600200000)]
    | 3 => [("creationDate", .ofInt 1600300000)]
    | 16 => [("creationDate", .ofInt 1600400000)]
    | 17 => [("creationDate", .ofInt 1600500000)]
    | _ => []
}

def ldbcSite : GraphSite := "ldbc"
def ldbcCatalog : Catalog := [("ldbc", ldbcGraph)]

-- ============================================================
--  3. LDBC Query Encodings
--     Each encodes the core MATCH...WHERE...RETURN fragment that
--     fits within the Paper Figure 2 grammar.
-- ============================================================

/-- IS1 (simplified): Profile of a person
  Original Cypher:
    MATCH (n:Person {id: $personId})-[:IS_LOCATED_IN]->(p:City)
    RETURN n.firstName AS firstName, n.lastName AS lastName, p.id AS cityId
  Param: personId = 1 (Alice) -/
def queryIS1 : Query :=
  .matchReturn
    (.edge
      { var := "n", labels := some (.atom "Person"),
        props := [{ key := "id", val := .int 1 }] }
      { var := "_e", labels := some (.atom "IS_LOCATED_IN") }
      .right
      { var := "p", labels := some (.atom "City") })
    [.alias' (.propAccess "n" "firstName") "firstName",
     .alias' (.propAccess "n" "lastName") "lastName",
     .alias' (.propAccess "p" "id") "cityId"]

/-- IS3 (simplified): Friends of a person
  Original Cypher:
    MATCH (n:Person {id: $personId})-[r:KNOWS]-(friend)
    RETURN friend.id AS personId, friend.firstName AS firstName,
           friend.lastName AS lastName
  Param: personId = 1 (Alice) -/
def queryIS3 : Query :=
  .matchReturn
    (.edge
      { var := "n", labels := some (.atom "Person"),
        props := [{ key := "id", val := .int 1 }] }
      { var := "r", labels := some (.atom "KNOWS") }
      .undirected
      { var := "friend" })
    [.alias' (.propAccess "friend" "id") "personId",
     .alias' (.propAccess "friend" "firstName") "firstName",
     .alias' (.propAccess "friend" "lastName") "lastName"]

/-- IS4 (simplified): Content of a message
  Original Cypher:
    MATCH (m:Message {id: $messageId})
    RETURN m.creationDate AS messageCreationDate, m.content AS messageContent
  Param: messageId = 300 (Post10) -/
def queryIS4 : Query :=
  .matchReturn
    (.node
      { var := "m", labels := some (.atom "Message"),
        props := [{ key := "id", val := .int 300 }] })
    [.alias' (.propAccess "m" "creationDate") "messageCreationDate",
     .alias' (.propAccess "m" "content") "messageContent"]

/-- IS5: Creator of a message
  Original Cypher:
    MATCH (m:Message {id: $messageId})-[:HAS_CREATOR]->(p:Person)
    RETURN p.id AS personId, p.firstName AS firstName, p.lastName AS lastName
  Param: messageId = 100 (Comment5, created by Alice) -/
def queryIS5 : Query :=
  .matchReturn
    (.edge
      { var := "m", labels := some (.atom "Message"),
        props := [{ key := "id", val := .int 100 }] }
      { var := "_e", labels := some (.atom "HAS_CREATOR") }
      .right
      { var := "p", labels := some (.atom "Person") })
    [.alias' (.propAccess "p" "id") "personId",
     .alias' (.propAccess "p" "firstName") "firstName",
     .alias' (.propAccess "p" "lastName") "lastName"]

/-- IC8 (core, no ORDER BY/LIMIT): Recent replies
  Original Cypher:
    MATCH (start:Person {id: $personId})<-[:HAS_CREATOR]-(:Message)
          <-[:REPLY_OF]-(comment:Comment)-[:HAS_CREATOR]->(person:Person)
    RETURN person.id AS personId, person.firstName AS personFirstName,
           comment.id AS commentId, comment.content AS commentContent

  Encoded as conjunction of 3 edge patterns sharing variables:
    (msg1)-[:HAS_CREATOR]->(start:Person {id:1}),
    (comment:Comment)-[:REPLY_OF]->(msg1),
    (comment)-[:HAS_CREATOR]->(person:Person) [note: reuse is not directly
       encodable in a single pattern; we use a fresh var and rely on
       the conjunction semantics with variable agreement]

  Actually, in our calculus we express the left-arrow direction:
    (start:Person {id:1}) <-[:HAS_CREATOR]- (msg1:Message)
  as edge(start, _e1:HAS_CREATOR, .left, msg1)

  Param: personId = 1 (Alice)
  Expected: comments replying to posts created by Alice -/
def queryIC8 : Query :=
  .matchReturn
    (.patternList
      (.patternList
        (.edge
          { var := "start", labels := some (.atom "Person"),
            props := [{ key := "id", val := .int 1 }] }
          { var := "_e1", labels := some (.atom "HAS_CREATOR") }
          .left
          { var := "msg1", labels := some (.atom "Message") })
        (.edge
          { var := "comment", labels := some (.atom "Comment") }
          { var := "_e2", labels := some (.atom "REPLY_OF") }
          .right
          { var := "msg1" }))
      (.edge
        { var := "comment" }
        { var := "_e3", labels := some (.atom "HAS_CREATOR") }
        .right
        { var := "person", labels := some (.atom "Person") }))
    [.alias' (.propAccess "person" "id") "personId",
     .alias' (.propAccess "person" "firstName") "personFirstName",
     .alias' (.propAccess "person" "lastName") "personLastName",
     .alias' (.propAccess "comment" "id") "commentId",
     .alias' (.propAccess "comment" "content") "commentContent"]

/-- IC2 (core, no ORDER BY/LIMIT/coalesce): Recent messages by friends
  Original Cypher:
    MATCH (:Person {id: $personId})-[:KNOWS]-(friend:Person)
          <-[:HAS_CREATOR]-(message:Message)
    WHERE message.creationDate < $maxDate
    RETURN friend.id AS personId, friend.firstName AS personFirstName,
           message.id AS messageId, message.content AS messageContent

  Encoded as conjunction:
    (p:Person {id:1})-[:KNOWS]~(friend:Person),
    (message:Message)-[:HAS_CREATOR]->(friend)
  Plus WHERE: message.creationDate < 1609600000

  Param: personId = 1 (Alice), maxDate = 1609600000 -/
def queryIC2 : Query :=
  .matchWhere
    (.patternList
      (.edge
        { var := "p", labels := some (.atom "Person"),
          props := [{ key := "id", val := .int 1 }] }
        { var := "_r", labels := some (.atom "KNOWS") }
        .undirected
        { var := "friend", labels := some (.atom "Person") })
      (.edge
        { var := "message", labels := some (.atom "Message") }
        { var := "_e", labels := some (.atom "HAS_CREATOR") }
        .right
        { var := "friend" }))
    (.relOp .lt (.propAccess "message" "creationDate") (.const (.int 1609600000)))
    [.alias' (.propAccess "friend" "id") "personId",
     .alias' (.propAccess "friend" "firstName") "personFirstName",
     .alias' (.propAccess "message" "id") "messageId",
     .alias' (.propAccess "message" "content") "messageContent"]

-- ============================================================
--  4. Query result assertions (golden outputs)
-- ============================================================

section QueryAssertions

def resultIS1 := evalQuery ldbcCatalog ldbcGraph ldbcSite queryIS1
def resultIS3 := evalQuery ldbcCatalog ldbcGraph ldbcSite queryIS3
def resultIS4 := evalQuery ldbcCatalog ldbcGraph ldbcSite queryIS4
def resultIS5 := evalQuery ldbcCatalog ldbcGraph ldbcSite queryIS5
def resultIC8 := evalQuery ldbcCatalog ldbcGraph ldbcSite queryIC8
def resultIC2 := evalQuery ldbcCatalog ldbcGraph ldbcSite queryIC2

-- IS1: Alice (id=1) located in Austin (id=400)
example : resultIS1.length = 1 := by native_decide
example : resultIS1.head!.lookup "firstName" = .ofString "Alice" := by native_decide
example : resultIS1.head!.lookup "lastName" = .ofString "Smith" := by native_decide
example : resultIS1.head!.lookup "cityId" = .ofInt 400 := by native_decide

-- IS3: Alice knows Bob and Charlie (undirected KNOWS)
example : resultIS3.length = 2 := by native_decide
example : resultIS3[0]!.lookup "firstName" = .ofString "Bob" := by native_decide
example : resultIS3[1]!.lookup "firstName" = .ofString "Charlie" := by native_decide

-- IS4: Post10 (id=300) content
example : resultIS4.length = 1 := by native_decide
example : resultIS4.head!.lookup "messageCreationDate" = .ofInt 1609100000 := by native_decide
example : resultIS4.head!.lookup "messageContent" = .ofString "Hello world from Alice" := by native_decide

-- IS5: Comment id=100 created by Alice
example : resultIS5.length = 1 := by native_decide
example : resultIS5.head!.lookup "personId" = .ofInt 1 := by native_decide
example : resultIS5.head!.lookup "firstName" = .ofString "Alice" := by native_decide

-- IC8: 3-hop reply chain — comments replying to posts created by Alice
example : resultIC8.length = 2 := by native_decide
example : resultIC8[0]!.lookup "personFirstName" = .ofString "Alice" := by native_decide
example : resultIC8[0]!.lookup "commentContent" = .ofString "Great post Alice!" := by native_decide
example : resultIC8[1]!.lookup "personFirstName" = .ofString "Charlie" := by native_decide
example : resultIC8[1]!.lookup "commentContent" = .ofString "Interesting perspective" := by native_decide

-- IC2: Friends' messages with creationDate < 1609600000
-- Both results from Bob (Charlie's comment has creationDate > cutoff)
example : resultIC2.length = 2 := by native_decide
example : resultIC2[0]!.lookup "personFirstName" = .ofString "Bob" := by native_decide
example : resultIC2[0]!.lookup "messageContent" = .ofString "I agree with you" := by native_decide
example : resultIC2[1]!.lookup "personFirstName" = .ofString "Bob" := by native_decide
example : resultIC2[1]!.lookup "messageContent" = .ofString "Tech news roundup" := by native_decide

end QueryAssertions

-- ============================================================
--  4b. Type checking and conformance of the benchmark queries
-- ============================================================

section TypeCheckAssertions

/-- Schema map binding the LDBC site to the LDBC schema (a closed site). -/
def ldbcSchemaMap : SchemaMap := [("ldbc", ldbcSchema)]

/-- Typing context for the LDBC catalog. -/
def ldbcCtx : TypingCtx :=
  { catalog := ldbcCatalog, schemaMap := ldbcSchemaMap, graphSite := ldbcSite }

/-- The LDBC data graph conforms to the LDBC schema -- the closed-site
    premise of the soundness theorems. -/
example : graphConformsSchema ldbcGraph ldbcSchema = true := by native_decide

-- inferQuery accepts each benchmark query.
example : (inferQuery ldbcCtx queryIS1).isSome = true := by native_decide
example : (inferQuery ldbcCtx queryIS3).isSome = true := by native_decide
example : (inferQuery ldbcCtx queryIS4).isSome = true := by native_decide
example : (inferQuery ldbcCtx queryIS5).isSome = true := by native_decide
example : (inferQuery ldbcCtx queryIC8).isSome = true := by native_decide
example : (inferQuery ldbcCtx queryIC2).isSome = true := by native_decide

-- Each evaluated binding table conforms to the inferred schema
-- (the concrete instances of inferQuery_conforms).
example : RecordSchema.bindingTableConforms resultIS1
    ((inferQuery ldbcCtx queryIS1).getD RecordSchema.empty) = true := by native_decide
example : RecordSchema.bindingTableConforms resultIS3
    ((inferQuery ldbcCtx queryIS3).getD RecordSchema.empty) = true := by native_decide
example : RecordSchema.bindingTableConforms resultIS4
    ((inferQuery ldbcCtx queryIS4).getD RecordSchema.empty) = true := by native_decide
example : RecordSchema.bindingTableConforms resultIS5
    ((inferQuery ldbcCtx queryIS5).getD RecordSchema.empty) = true := by native_decide
example : RecordSchema.bindingTableConforms resultIC8
    ((inferQuery ldbcCtx queryIC8).getD RecordSchema.empty) = true := by native_decide
example : RecordSchema.bindingTableConforms resultIC2
    ((inferQuery ldbcCtx queryIC2).getD RecordSchema.empty) = true := by native_decide

-- The small-step engine agrees with the big-step evaluator on each
-- benchmark query.
example : runQuery .smallStep ldbcCatalog ldbcGraph ldbcSite queryIS1 =
          runQuery .bigStep ldbcCatalog ldbcGraph ldbcSite queryIS1 := by native_decide
example : runQuery .smallStep ldbcCatalog ldbcGraph ldbcSite queryIS3 =
          runQuery .bigStep ldbcCatalog ldbcGraph ldbcSite queryIS3 := by native_decide
example : runQuery .smallStep ldbcCatalog ldbcGraph ldbcSite queryIS4 =
          runQuery .bigStep ldbcCatalog ldbcGraph ldbcSite queryIS4 := by native_decide
example : runQuery .smallStep ldbcCatalog ldbcGraph ldbcSite queryIS5 =
          runQuery .bigStep ldbcCatalog ldbcGraph ldbcSite queryIS5 := by native_decide
example : runQuery .smallStep ldbcCatalog ldbcGraph ldbcSite queryIC8 =
          runQuery .bigStep ldbcCatalog ldbcGraph ldbcSite queryIC8 := by native_decide
example : runQuery .smallStep ldbcCatalog ldbcGraph ldbcSite queryIC2 =
          runQuery .bigStep ldbcCatalog ldbcGraph ldbcSite queryIC2 := by native_decide

end TypeCheckAssertions

-- ============================================================
--  5. Benchmark Runner
-- ============================================================

/-- Compact display of an extended base sort. -/
private def baseLabel : ExtSort → String
  | .scalar .int => "Z"
  | .scalar .string => "S"
  | .scalar .bool => "B"
  | .node g => s!"N<{g}>"
  | .edge g => s!"E<{g}>"
  | .nodeRefined g ss => s!"N<{g},{ss.length} schemas>"
  | .edgeRefined g ss => s!"E<{g},{ss.length} schemas>"

/-- Compact display of a sort shape. -/
private def shapeLabel : SortShape → String
  | .single es => baseLabel es
  | .any => "Any"
  | .bot => "bot"
  | .nullType => "?"
  | .union ts => "(" ++ String.intercalate " u " (ts.map baseLabel) ++ ")"
  | .list s _ => "List " ++ shapeLabel s
  | .emptyFormer s _ => "<" ++ shapeLabel s ++ ">bot"

/-- Compact display of a GQL sort for the benchmark output. -/
def sortLabel (t : GSort) : String :=
  match t.null with
  | .val => shapeLabel t.shape
  | .nullable => shapeLabel t.shape ++ "?"
  | .null => "?" ++ shapeLabel t.shape

/-- Run a single query and report results + basic timing.
  Uses IO.monoMsNow for wall-clock measurement. -/
def benchQuery (name : String) (q : Query) : IO Unit := do
  let numIter : Nat := 100
  let startTime <- IO.monoMsNow
  let mut lastResult : BindingTable := []
  for _ in List.range numIter do
    lastResult := evalQuery ldbcCatalog ldbcGraph ldbcSite q
  let endTime <- IO.monoMsNow
  let elapsed := endTime - startTime
  IO.println s!"  {name}: {lastResult.length} results, {elapsed}ms / {numIter} iters"
  -- Print first result as sanity check
  match lastResult with
  | first :: _ =>
    let vals := first.map fun (k, v) =>
      match v with
      | .prim (.int n) => s!"{k}={n}"
      | .prim (.string s) => s!"{k}=\"{s}\""
      | .prim (.bool b) => s!"{k}={b}"
      | .nodeRef g n => s!"{k}=nodeRef({g},{n})"
      | .edgeRef g e => s!"{k}=edgeRef({g},{e})"
      | .null => s!"{k}=null"
      | _ => s!"{k}=<other>"
    IO.println s!"    first row: {vals}"
  | [] => IO.println "    (no results)"

/-- Main benchmark entry point. -/
def main : IO Unit := do
  IO.println "======================================================"
  IO.println "  MGQL LDBC SNB Interactive v2 Benchmark"
  IO.println "  Graph: 20 nodes, 20 edges (small LDBC-like instance)"
  IO.println "======================================================"
  IO.println ""

  IO.println "--- LDBC SNB Interactive read queries (executable semantics) ---"
  IO.println ""

  benchQuery "IS1  (Person profile via IS_LOCATED_IN)" queryIS1
  IO.println ""
  benchQuery "IS3  (Friends via undirected KNOWS)" queryIS3
  IO.println ""
  benchQuery "IS4  (Message content by id)" queryIS4
  IO.println ""
  benchQuery "IS5  (Message creator via HAS_CREATOR)" queryIS5
  IO.println ""
  benchQuery "IC8  (3-hop reply chain)" queryIC8
  IO.println ""
  benchQuery "IC2  (Friends' messages with WHERE filter)" queryIC2
  IO.println ""

  IO.println "--- Certified type checker (inferQuery, TypeChecker.lean) ---"
  IO.println ""
  for (name, q) in [("IS1", queryIS1), ("IS3", queryIS3), ("IS4", queryIS4),
                    ("IS5", queryIS5), ("IC8", queryIC8), ("IC2", queryIC2)] do
    match inferQuery ldbcCtx q with
    | some Gamma =>
      let cols := Gamma.entries.map (fun (x, t) => s!"{x}: {sortLabel t}")
      IO.println s!"  {name}: accepted -- schema [{String.intercalate ", " cols}]"
    | none => IO.println s!"  {name}: rejected"
  IO.println ""
  IO.println "  inferQuery_sound certifies every accepted query against the"
  IO.println "  declarative typing judgment; inferQuery_conforms guarantees the"
  IO.println "  evaluated binding table conforms to the inferred schema."
  IO.println ""

end MGQL.LDBCBench

def main : IO Unit := MGQL.LDBCBench.main
