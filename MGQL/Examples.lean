/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Examples.lean -- Kick-the-tires examples for artifact evaluation

  One file per layer, so each group can be checked on its own (see
  run-test.sh, or `lake env lean MGQL/Examples/<Group>.lean`):
  the conformance relations (Definition 2.3), subtyping and dynamic
  refinement, expression and predicate typing, Kleene evaluation, atom
  and pattern typing with endpoint refinement, and a small end-to-end
  query.  All assertions are checked during the build.

  The integration test over the six LDBC SNB queries is in
  LDBCBench.lean.
-/
import MGQL.Examples.Fixtures
import MGQL.Examples.PropertyConformance
import MGQL.Examples.NodeConformance
import MGQL.Examples.EdgeConformance
import MGQL.Examples.GraphConformance
import MGQL.Examples.Subtyping
import MGQL.Examples.ExpressionTyping
import MGQL.Examples.Predicates
import MGQL.Examples.AtomTyping
import MGQL.Examples.PatternTyping
import MGQL.Examples.EndToEnd
