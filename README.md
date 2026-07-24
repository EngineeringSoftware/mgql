# MGQL: An Executable, Small-Step Semantics of GQL

[![CI](https://github.com/EngineeringSoftware/mgql/actions/workflows/ci.yml/badge.svg)](https://github.com/EngineeringSoftware/mgql/actions/workflows/ci.yml)

This is the artifact for the OOPSLA 2026 paper *MGQL: An Executable,
Small-Step Semantics of GQL* (submission #337). It contains the complete
Lean 4 mechanization described in Section 7 of the paper: the MGQL
calculus and its schema-aware type system, a big-step evaluator and a
small-step engine proven equivalent to it, machine-checked proofs of
every theorem the paper names, a certified executable type checker, and
the LDBC SNB case study.

Key properties, each verifiable with the instructions below:

- about 23,700 lines of Lean 4 across fourteen modules, with no
  dependency beyond core Lean (no Mathlib, no Std);
- zero `sorry`, zero user-declared axioms; every named result depends
  only on the standard Lean axioms `propext`, `Classical.choice`, and
  `Quot.sound`;
- 350 executable `native_decide` assertions re-checked on every build
  (276 unit tests, 32 assertions across 30 worked examples, 42 LDBC
  integration assertions).

We apply for the **Available**, **Functional**, **Reusable**, and **Results
Reproduced** badges.

## Contents

1. [Artifact inventory](#1-artifact-inventory)
2. [Requirements](#2-requirements)
3. [Getting started (kick the tires)](#3-getting-started-kick-the-tires)
4. [Evaluation instructions](#4-evaluation-instructions)
5. [List of claims](#5-list-of-claims)
6. [Paper-to-artifact correspondence](#6-paper-to-artifact-correspondence)
7. [Axioms, assumptions, and proof completeness](#7-axioms-assumptions-and-proof-completeness)
8. [Deviations from the paper](#8-deviations-from-the-paper)
9. [Proof structure and organization](#9-proof-structure-and-organization)
10. [Reusability guide](#10-reusability-guide)
11. [Platform notes](#11-platform-notes)

## 1. Artifact inventory

| Path | Purpose |
|---|---|
| `MGQL/*.lean` | The mechanization (fourteen modules, listed in [Section 9](#9-proof-structure-and-organization)) |
| `MGQL/Examples/` | 30 worked kick-the-tires examples, one file per layer of the development |
| `verify-soundness.sh` | One-command audit: clean build, `sorry`/axiom scan, per-theorem axiom report, LDBC benchmark |
| `run-test.sh` | Re-runs one test group at a time (see `./run-test.sh --list`) |
| `HOWTO.md` | Reusability guide: check a GQL query of your own against the mechanization |
| `Dockerfile` | Ubuntu 22.04 image that builds everything and runs `verify-soundness.sh` |
| `LICENSE` | MIT license |
| `lean-toolchain`, `lakefile.lean`, `lake-manifest.json` | Toolchain pin (Lean 4.14.0) and build configuration |

## 2. Requirements

- **Hardware.** Any 64-bit x86 or ARM machine with about 8 GB of RAM
  and 3 GB of free disk. No specialized hardware is needed.
- **Software.** Either Docker (any recent version), or the Lean
  toolchain manager [elan](https://github.com/leanprover/elan) for a
  local build. elan installs the pinned Lean 4.14.0 automatically from
  the `lean-toolchain` file; no other software is required.
- **Time.** The initial build compiles the full development and checks
  all 350 assertions; it takes about one minute on a recent laptop
  (Apple Silicon), and a few minutes on older hardware or under Docker
  QEMU emulation. Everything after that is incremental and fast.

## 3. Getting started (kick the tires)

### Option A: Docker (recommended)

```
docker build -t mgql-artifact .
docker run --rm mgql-artifact
```

`docker build` compiles the full development inside the image (this is
where the build time goes); `docker run` executes
`verify-soundness.sh` and must end with:

```
ALL CHECKS PASSED
```

On Apple Silicon or other ARM hosts, plain `docker build` works; to
force the architecture explicitly use
`docker buildx build --platform linux/arm64 -t mgql-artifact --load .`.

### Option B: Local build

```
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y
export PATH="$HOME/.elan/bin:$PATH"
lake build
```

A clean `lake build` that ends without errors is itself a meaningful
check: it re-elaborates every proof and re-executes every
`native_decide` assertion in the test and example modules.

### Sanity test

After either option, re-check one example group by hand (inside the
container: `docker run --rm -it mgql-artifact bash`, then the same
commands):

```
./run-test.sh --list               # show the twelve targets
./run-test.sh graph-conformance    # expected: PASS (2 examples)
./run-test.sh -v end-to-end        # expected: PASS (5 examples), one line per check
```

Each target re-elaborates its file and re-executes its assertions; a
failing assertion aborts with a compile error at the offending line.

## 4. Evaluation instructions

The full evaluation is four commands and takes well under an hour, of
which most is the one-time build.

**Step 1: build.** `lake build` (or the Docker build from Section 3).

**Step 2: run the audit script.** `./verify-soundness.sh` performs, in
order:

1. a build of the full development;
2. a scan proving there is no live `sorry` in any module;
3. a scan proving there is no user-declared `axiom` in any module;
4. `#print axioms` on every named result from the paper, so you can
   confirm each theorem exists and depends only on the three standard
   Lean axioms (the per-theorem expectation is the Axioms column of the
   [correspondence tables](#6-paper-to-artifact-correspondence));
5. the LDBC SNB benchmark run (Table 2 of the paper);
6. a summary of the test layers.

The expected output is reproduced at the end of this section.

**Step 3: run every test group.** `./run-test.sh all` re-executes the
30 worked examples group by group, then the 276-assertion unit suite,
then the 42-assertion LDBC integration suite. Expected: every line ends
in `PASS (n examples)` followed by `ALL TARGETS PASSED`.

**Step 4: run the benchmark executable.**

```
lake exe ldbcBench
```

This executes the six LDBC SNB Interactive v2 queries (IS1, IS3, IS4,
IS5, IC8, IC2) against a 20-node/20-edge graph through the executable
semantics, then runs the certified type checker on each query and
prints the inferred result schema. Compare the printed queries and
schemas against Table 2 of the paper.

**Step 5 (optional): spot-check individual results.** To inspect any
single theorem, open the file and line from the
[correspondence tables](#6-paper-to-artifact-correspondence); each
headline theorem carries a doc comment naming the paper statement it
mechanizes. To re-check its axioms yourself, elaborate a two-line file:

```
echo 'import MGQL.TypeChecker
#print axioms MGQL.inferQuery_sound' > /tmp/Ax.lean && lake env lean /tmp/Ax.lean
```

To compare the module inventory against Table 1 of the paper:
`wc -l MGQL/*.lean`.

### Expected output of verify-soundness.sh

```
==> 1. Clean build of the full development
Build completed successfully.

==> 2. No live sorry in any module
PASS

==> 3. No user-declared axiom in the proof modules
PASS

==> 4. Axiom dependencies of the paper's named results
'expressionSoundness' depends on axioms: [propext, Quot.sound]
'expressionSoundness_graphConforms' depends on axioms: [propext, Quot.sound]
'patExprSoundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'queryTypeSoundness_composed' depends on axioms: [propext, Classical.choice, Quot.sound]
'queryTypeSoundness_bool' depends on axioms: [propext, Classical.choice, Quot.sound]
'queryTypeSoundness_composed_catalogWide' depends on axioms: [propext, Classical.choice, Quot.sound]
'compositeQuerySoundness_composed' depends on axioms: [propext, Classical.choice, Quot.sound]
'compositeQuerySoundness_bool' depends on axioms: [propext, Classical.choice, Quot.sound]
'exprStep_progress' does not depend on any axioms
'exprStep_preservation' depends on axioms: [propext]
'exprSmallStep_soundness_open' depends on axioms: [propext, Quot.sound]
'patSmallStep_soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'querySmallStep_soundness_catalogWide' depends on axioms: [propext, Classical.choice, Quot.sound]
'compositeSmallStep_soundness_catalogWide' depends on axioms: [propext, Classical.choice, Quot.sound]
'exprStep_correct' depends on axioms: [propext]
'patStep_correct' depends on axioms: [propext]
'qStep_correct' depends on axioms: [propext, Quot.sound]
'runQuery_engine_agnostic' depends on axioms: [propext, Quot.sound]
'patExprSoundness_open' depends on axioms: [propext, Classical.choice, Quot.sound]
'queryTypeSoundness_composed_mixedSites' depends on axioms: [propext, Classical.choice, Quot.sound]
'compositeQuerySoundness_mixedSites' depends on axioms: [propext, Classical.choice, Quot.sound]
'patExprSoundness_inhabits' depends on axioms: [propext, Classical.choice, Quot.sound]
'patExprSoundness_inhabits_open' depends on axioms: [propext, Classical.choice, Quot.sound]
'queryTyping_inhabits' depends on axioms: [propext, Classical.choice, Quot.sound]
'queryTyping_inhabitsS' depends on axioms: [propext, Classical.choice, Quot.sound]
'querySmallStep_inhabits' depends on axioms: [propext, Classical.choice, Quot.sound]
'querySmallStep_inhabitsS' depends on axioms: [propext, Classical.choice, Quot.sound]
'evalPatternTrail_subset' depends on axioms: [propext, Quot.sound]
'patStepT_complete' depends on axioms: [propext]
'tripleCompat_eq_thetaD' depends on axioms: [propext, Quot.sound]
'refineEdgeByCompat_eq_thetaD' depends on axioms: [propext, Quot.sound]
'compQueryTypeSoundness_mixedSites' depends on axioms: [propext, Classical.choice, Quot.sound]
'compQuerySmallStep_soundness_catalogWide' depends on axioms: [propext, Classical.choice, Quot.sound]
'inferQuery_sound' depends on axioms: [propext, Quot.sound]
'inferQuery_conforms' depends on axioms: [propext, Classical.choice, Quot.sound]
'inferCompQuery_sound' depends on axioms: [propext, Quot.sound]
PASS (all results depend only on propext, Classical.choice, Quot.sound)

==> 5. LDBC SNB Interactive benchmark (executable semantics)
  IS1  (Person profile via IS_LOCATED_IN): 1 results, ...
  IS3  (Friends via undirected KNOWS): 2 results, ...
  IS4  (Message content by id): 1 results, ...
  IS5  (Message creator via HAS_CREATOR): 1 results, ...
  IC8  (3-hop reply chain): 2 results, ...
  IC2  (Friends' messages with WHERE filter): 2 results, ...

--- Certified type checker (inferQuery, TypeChecker.lean) ---

  IS1: accepted -- schema [firstName: S?, lastName: S?, cityId: Z?]
  IS3: accepted -- schema [personId: Z?, firstName: S?, lastName: S?]
  IS4: accepted -- schema [messageCreationDate: Z?, messageContent: S?]
  IS5: accepted -- schema [personId: Z?, firstName: S?, lastName: S?]
  IC8: accepted -- schema [personId: Z?, personFirstName: S?, ...]
  IC2: accepted -- schema [personId: Z?, personFirstName: S?, ...]

==> 6. Test summary
  ...

ALL CHECKS PASSED
```

(Lines abbreviated with `...` print additional per-query detail; the
final line must read `ALL CHECKS PASSED`.)

## 5. List of claims

Each claim states where it appears in the paper, where it lives in the
artifact, and which evaluation step checks it. Line numbers refer to
this revision of the artifact; declaration names are stable.

### Section 3 (type system)

- **Lemma 3.1 (absorption laws for top and bottom)** corresponds to
  `absorb_union_any`, `absorb_union_bot`, `absorb_inter_any`,
  `absorb_inter_bot` in `MGQL/Subtyping.lean:163-178` and is checked by
  Step 1 (they are proved, not tested).
- **Lemma 3.2 (schema-refined type bounds)** corresponds to
  `schemaRefinedNodeBounded` and `schemaRefinedEdgeBounded` in
  `MGQL/Subtyping.lean:238,245`, checked by Step 1.

### Section 4 (well-formedness of GQL queries)

- **The typing rules of Section 4 and Appendix B are mechanized** as
  eleven inductive propositions totaling 57 constructors
  (`MGQL/Typing.lean`; per-judgment locations in the
  [definitions table](#definitions)). Checked by Step 1; exercised
  positively and negatively by the worked examples of Step 3
  (`expression-typing`, `atom-typing`, `pattern-typing` targets).
- **The certified type checker** (Section 7) corresponds to
  `inferQuery`/`inferQuery_sound`/`inferQuery_conforms` in
  `MGQL/TypeChecker.lean` and is checked by Steps 2 and 4 (it runs on
  every LDBC query).

### Section 5 (small-step operational semantics)

- **The semantics is executable.** The evaluators
  `evalExpr`/`evalPattern`/`evalQuery` (`MGQL/Semantics.lean`) and the
  step interpreter (`MGQL/SmallStep.lean`) run every test, example, and
  benchmark query in this artifact. Checked by Steps 1 to 4.
- **The step relations mirror the paper's reduction rules.**
  `ExprStep`, `PatStep`, and `QStep` over the paper's 4-tuple/3-tuple/
  final-bag configurations live in `MGQL/SmallStep.lean:71,709,1083`.
  Checked by Step 1 and the `end-to-end` target of Step 3.
- **Both engines agree.** `runQuery_engine_agnostic`
  (`MGQL/SmallStep.lean:2232`) proves the big-step evaluator and the
  small-step engine return the same table on every catalog, graph,
  site, and query, via the equivalence theorems `exprStep_correct`,
  `patStep_correct`, `qStep_correct`. Checked by Steps 1 and 2; also
  asserted per LDBC query in Step 4.

### Section 6 (type soundness)

Theorems 6.1, 6.2, 6.3 and Corollary 6.1, including their small-step,
open-site, mixed-site, and Definition 6.1 variants, correspond to the
Lean theorems in the [theorems table](#theorems) and are checked by
Step 2 (script steps 1 to 4): the script proves they build, contain no
`sorry`, use no user axioms, and depend only on the standard axioms.

### Section 7 (mechanized implementation)

- **Table 1 (module structure and lines of code)** is reproduced by
  `wc -l MGQL/*.lean` (Step 5); the per-module counts match the table.
- **"276 unit assertions, 30 worked examples, LDBC integration, 350
  `native_decide` assertions in total"** is checked by Steps 2 and 3
  (the `unit` and `integration` targets print their assertion counts).
- **Table 2 (LDBC SNB queries)** is reproduced by Step 4: the six
  queries, their pattern shapes, and their inferred schemas are
  printed by `ldbcBench`.
- **"Zero `sorry`, zero user-declared axioms, standard axioms only"**
  is checked by Step 2 (script steps 2 to 4).

## 6. Paper-to-artifact correspondence

### Theorems

Axiom abbreviations: **P** = `propext`, **C** = `Classical.choice`,
**Q** = `Quot.sound`. These are the three standard Lean axioms; see
[Section 7](#7-axioms-assumptions-and-proof-completeness).

| Paper statement | Lean theorem | Location | Axioms |
|---|---|---|---|
| Thm 6.1 Expression Soundness | `expressionSoundness` | `Metatheory.lean:4897` | P, Q |
| Thm 6.1 (graph-conforming form) | `expressionSoundness_graphConforms` | `Metatheory.lean:4991` | P, Q |
| Thm 6.1 (small-step Progress) | `exprStep_progress` | `SmallStep.lean:211` | none |
| Thm 6.1 (small-step Preservation) | `exprStep_preservation` | `SmallStep.lean:480` | P |
| Thm 6.1 (small-step soundness, open sites) | `exprSmallStep_soundness_open` | `SmallStep.lean:582` | P, Q |
| Thm 6.2 Pattern Soundness | `patExprSoundness` | `Metatheory.lean:8760` | P, C, Q |
| Thm 6.2 (open sites) | `patExprSoundness_open` | `Metatheory.lean:9336` | P, C, Q |
| Thm 6.2 (small-step star form) | `patSmallStep_soundness` | `SmallStep.lean:983` | P, C, Q |
| Thm 6.2 (Definition 6.1 conformance) | `patExprSoundness_inhabits`, `patExprSoundness_inhabits_open` | `Metatheory.lean:12689,12722` | P, C, Q |
| Thm 6.3 Query Type Soundness | `queryTypeSoundness_composed` | `Metatheory.lean:11050` | P, C, Q |
| Thm 6.3 (boolean form) | `queryTypeSoundness_bool` | `Metatheory.lean:13753` | P, C, Q |
| Thm 6.3 (catalog-wide) | `queryTypeSoundness_composed_catalogWide` | `Metatheory.lean:11130` | P, C, Q |
| Thm 6.3 (mixed open/closed sites) | `queryTypeSoundness_composed_mixedSites` | `Metatheory.lean:11172` | P, C, Q |
| Thm 6.3 (small-step star form) | `querySmallStep_soundness_catalogWide` | `SmallStep.lean:1298` | P, C, Q |
| Thm 6.3 (Definition 6.1 conformance) | `queryTyping_inhabits`, `queryTyping_inhabitsS` | `Metatheory.lean:13726,13619` | P, C, Q |
| Thm 6.3 (Def 6.1, small-step star form) | `querySmallStep_inhabits`, `querySmallStep_inhabitsS` | `SmallStep.lean:1374,1396` | P, C, Q |
| Cor 6.1 Composite Query Soundness | `compositeQuerySoundness_composed` | `Metatheory.lean:11080` | P, C, Q |
| Cor 6.1 (boolean form) | `compositeQuerySoundness_bool` | `Metatheory.lean:13771` | P, C, Q |
| Cor 6.1 (mixed open/closed sites) | `compositeQuerySoundness_mixedSites` | `Metatheory.lean:11212` | P, C, Q |
| Cor 6.1 (small-step star form) | `compositeSmallStep_soundness_catalogWide` | `SmallStep.lean:1323` | P, C, Q |
| Cor 6.1 (single-operator judgment) | `compQueryTypeSoundness_mixedSites`, `compQuerySmallStep_soundness_catalogWide` | `Metatheory.lean:14042`, `SmallStep.lean:2247` | P, C, Q |
| Lemma 3.1 Absorption | `absorb_union_any`, `absorb_union_bot`, `absorb_inter_any`, `absorb_inter_bot` | `Subtyping.lean:163-178` | none |
| Lemma 3.2 Bounds | `schemaRefinedNodeBounded`, `schemaRefinedEdgeBounded` | `Subtyping.lean:238,245` | none |
| Trail path mode (walk-to-trail transport) | `evalPatternTrail_subset`, `patStepT_complete` | `Metatheory.lean:2203`, `SmallStep.lean:940` | P, Q / P |
| θ_D faithfulness (well-formed catalogs) | `tripleCompat_eq_thetaD`, `refineEdgeByCompat_eq_thetaD` | `Metatheory.lean:13891,13940` | P, Q |
| Engine equivalence | `exprStep_correct`, `patStep_correct`, `qStep_correct` | `SmallStep.lean:195,966,1283` | P / P / P, Q |
| Engine-flag agreement | `runQuery_engine_agnostic` | `SmallStep.lean:2232` | P, Q |
| Certified checker soundness | `inferQuery_sound`, `inferCompQuery_sound` | `TypeChecker.lean:1212,1312` | P, Q |
| Checker semantic guarantee | `inferQuery_conforms` | `TypeChecker.lean:1277` | P, C, Q |

### Definitions

| Paper | Lean name(s) | Location |
|---|---|---|
| Def 2.1 property graph instance | `PropertyGraph` | `Schema.lean:83` |
| Def 2.2 property/node/edge/graph schemas | `PropSchema`, `NodeSchemaFull`, `EdgeSchemaFull`, `GraphSchemaFull` | `Sorts.lean:35,41,46`, `Schema.lean:47` |
| Def 2.3 conformance relations | `propMapConformsSchema`, `nodeConformsSchema`, `edgeConformsSchema`, `graphConformsSchema` | `Schema.lean:122,135,145,164` |
| Def 2.4 closed and open graphs | `SchemaMap.isClosed` | `Schema.lean:280` |
| Fig 2 calculus grammar | `Expr`/`Pred`, `Pattern`, `Query` | `Syntax.lean:64,171,274` |
| Sec 3 sort tiers T0/T1/τ | `BaseSort`, `ExtSort`, `GSort` | `Sorts.lean:25,58,93` |
| Notation 3.1 schema-refined unions | `GSort.nodeRefinedOf`, `GSort.edgeRefinedOf` (the constructor carries the schema set) | `Sorts.lean:123,125` |
| Def 3.1 component type | `GSort.componentType` | `Sorts.lean:189` |
| Sec 3.4 null type and empty formers | `NullTag`, `GSort.nodeEmpty`, `GSort.edgeEmpty` | `Sorts.lean:72,130,132` |
| Sec 3.5 subtyping | `Subtype` | `Subtyping.lean:20` |
| Def 3.2 type intersection | `TypeIntersection` (declarative), `RecordSchema.sortInter` (computable) | `Subtyping.lean:144`, `RecordSchema.lean:174` |
| Def 3.3-3.4 record schemas, union/join compatibility | `RecordSchema` and its operations | `RecordSchema.lean:45` |
| App A dynamic refinement | `DynRefine` | `Subtyping.lean:123` |
| Def 4.2 quantifier lift | `RecordSchema.liftToGroupRef`, `RecordSchema.liftToNullable` | `RecordSchema.lean:250,256` |
| θ_D endpoint condition | `thetaD`; the filters use `tripleCompat`, proven equal on well-formed catalogs | `Typing.lean:629,183`, `Metatheory.lean:13891` |
| Sec 4/App B typing judgments | `ExprTyping`, `PredTyping`, `AtomTyping`, `RefinementTyping`, `PatternTyping`, `PatExprTyping`, `ProjectionTyping`, `ProjectionListTyping`, `QueryTyping`, `CompQueryTyping` | `Typing.lean:289,440,670,760,853,964,985,1011,1051,1105` |
| Sec 5.1 runtime domain | `Value`, `Record`, `BindingTable` | `Values.lean:23,186,233` |
| Def 5.1-5.2 trail-aware tables | `Record.isTrail`, `evalPatternTrail` (per-component filter, equivalent to the visited-set monoid on fully-bound patterns) | `Semantics.lean:531,537` |
| Sec 5/App C evaluation | `evalExpr`, `evalPred`, `evalPattern`, `evalQuery` | `Semantics.lean:91,126,426,621` |
| Sec 5 step relations and configurations | `ExprStep`, `PatStep`, `QStep` over `RQuery` (the 4-tuple/3-tuple/final-bag configurations) | `SmallStep.lean:71,709,1083,1074` |
| Def 6.1 value typing | `ValueInhabits`, `ValueInhabitsS` | `Metatheory.lean:11262,11352` |
| Def 6.2 record/table conformance | `RecordConforms`, `BTConforms` | `Metatheory.lean:40,50` |
| Certified checker | `inferQuery`, `inferCompQuery` | `TypeChecker.lean:1182,1297` |

## 7. Axioms, assumptions, and proof completeness

**Axioms.** No module declares an axiom. Every named result depends
only on `propext` (propositional extensionality), `Classical.choice`,
and `Quot.sound` (quotient soundness), the three standard axioms that
ship with Lean itself and underpin its classical logic. Several results
need fewer (see the Axioms column above); `exprStep_progress` is fully
axiom-free. Step 2 of the evaluation prints the exact dependency set of
every result.

**No unfinished proofs.** There is no `sorry` anywhere in the
development; script step 2 greps for it, and any live `sorry` would
also surface as a build warning in Step 1.

**`native_decide` is confined to tests.** The test and example modules
use `native_decide`, which trusts the Lean compiler, to execute
concrete queries during the build. No soundness proof uses it: if one
did, `Lean.ofReduceBool` would appear in that theorem's `#print axioms`
output in Step 2, and it does not.

**Hypotheses of the soundness theorems.** Mirroring the premises of the
paper's theorems, the mechanized results assume the working graph
conforms to its catalog schema (Definition 2.3), that graph values are
well formed, and, for the closed-site refinement results, that the
schema map supplies a schema for the working site. Each hypothesis is
an explicit named argument of the corresponding theorem, so the full
assumption set of any result is visible in its statement.

## 8. Deviations from the paper

The mechanized judgments match the printed rules one-to-one. The
deliberate differences are listed here; none of them changes which
complete queries are typeable, except where the mechanization is a
proven-sound generalization.

**Generalizations (soundness proven for the general form).**

- `USE` clauses are optional in the mechanized query type, while the
  paper's grammar mandates one per linear query. The mechanization
  therefore types a superset of the paper's queries.
- Composite queries mixing set-operator kinds are typed by the general
  per-node rule (`QueryTyping.composite`) and proven sound. The paper's
  single-operator judgment is mechanized separately as
  `CompQueryTyping`, with its soundness inherited through an axiom-free
  erasure.

**Encoding conventions.**

- The paper's Rnm rules assign fresh names to anonymous pattern
  variables during matching. Mechanized atoms carry explicit names, and
  encodings perform this deterministic renaming up front (for example
  `"_e1"`). The renaming pass itself is not mechanized.
- The paper's two union sugars are represented in normalized form: the
  nullable type τ? (that is, τ ∪ ?) as a nullability component on the
  sort, and the multi-schema refined type of Notation 3.1 (the union of
  its singleton refinements) as one constructor carrying the schema
  set. The union laws are provable over this representation. For
  instance, schema-set widening (the S-Union-L instance under
  Notation 3.1) is a subtyping rule, and the absorption laws of
  Lemma 3.1 are theorems.

**Narrower premises, coinciding on all reachable schemas.**

- Refine-Open's printed premises admit the non-nullable graph-scoped
  operand as well as the nullable one; the mechanized rule takes the
  nullable form, which is the only form the atom and refinement rules
  produce.
- E-PropAccess-Schema's printed premise is a dynamic refinement to the
  schema-refined sort; the mechanized rule matches the variable's
  component type exactly. Multi-schema refined types are covered (the
  schema set lives inside the constructor and the property helper
  unions over it). What is excluded are union types mixing a refined
  branch with branches of other kinds, which no pattern rule produces,
  so typeability of complete queries coincides.

## 9. Proof structure and organization

| Module | Contents |
|---|---|
| `MGQL/Sorts.lean` | Sort tiers T0/T1/τ, `GSort`, empty formers, ⊥ |
| `MGQL/Values.lean` | Runtime values, records, Kleene three-valued logic |
| `MGQL/Syntax.lean` | The calculus AST: expressions, predicates, patterns, queries (Fig. 2) |
| `MGQL/Schema.lean` | Property graphs, graph schemas, conformance (Defs 2.1-2.4) |
| `MGQL/RecordSchema.lean` | Record schemas, compatibility, sort operations |
| `MGQL/Subtyping.lean` | The subtype lattice, absorption laws, refinement bounds |
| `MGQL/Typing.lean` | The eleven typing judgments of Section 4 and Appendix B |
| `MGQL/Semantics.lean` | The big-step evaluator (`evalExpr`, `evalPattern`, `evalQuery`) |
| `MGQL/Metatheory.lean` | The soundness proofs of Section 6 |
| `MGQL/SmallStep.lean` | Step relations, configurations, interpreter, engine equivalence and flag |
| `MGQL/TypeChecker.lean` | The certified executable type checker and its soundness |
| `MGQL/Test.lean` | Unit tests (276 `native_decide` assertions) |
| `MGQL/Examples/` | 30 worked examples, one file per layer, including negative cases |
| `MGQL/LDBCBench.lean` | The six LDBC SNB queries plus 42 integration assertions |

The import chain is linear:

```
Sorts -> Values/Syntax -> Schema -> RecordSchema -> Subtyping
      -> Typing -> Semantics -> Metatheory -> SmallStep -> TypeChecker
```

with the test and example modules on top; each file depends only on the
ones before it. Definitions and theorems carry doc comments naming the
paper rule or statement they mechanize (for example, the doc comment of
`exprStep_progress` reads "Paper Theorem 6.1, small-step form").

## 10. Reusability guide

**License.** The artifact is released under the MIT license (see
`LICENSE`).

**Checking your own queries.** `HOWTO.md` is a complete, tested
walkthrough for using the mechanization on new inputs: encoding a
property graph and its schema, writing a GQL query as a `Query` term
(with a table mapping each GQL surface construct to its Lean
constructor), type checking it with the certified checker, evaluating
it on both engines, and turning each check into a machine-checked
`example` that fails the build if violated. The LDBC module
(`MGQL/LDBCBench.lean`) contains six real queries written in exactly
that style.

**Reusable components.** The development is an ordinary Lean library
with a linear module structure and no external dependencies, so any
prefix of it can be reused in another project: the calculus AST
(`Syntax`), the graph and schema model (`Schema`), the type system
(`Typing`, `Subtyping`, `RecordSchema`), the evaluators (`Semantics`,
`SmallStep`), and the certified checker (`TypeChecker`) all import
cleanly via `import MGQL.<Module>`.

**Interactive exploration.** Opening the folder in VS Code with the
lean4 extension (after `lake build`) gives hover documentation, go to
definition, and live elaboration of the examples.

**Limitations.** The mechanization covers the fragment formalized in
the paper. Features outside it, primarily `WITH` pipelining,
`OPTIONAL MATCH`, `ORDER BY`/`LIMIT`, and shortest-path constructs, are
out of scope; `HOWTO.md` lists the supported fragment precisely.

## 11. Platform notes

The artifact builds on any platform supported by Lean 4.14.0. Tested
configurations:

- **Linux x86-64**: native build and Docker, all checks pass.
- **Linux ARM64**: Docker via `docker buildx build --platform
  linux/arm64` under QEMU emulation, all checks pass, including
  re-execution of every `native_decide` assertion on aarch64.
- **macOS (Apple Silicon)**: Docker works out of the box. For the local
  build, `lake build` succeeds and checks every assertion; on recent
  macOS versions dyld may refuse to launch the standalone benchmark
  executable (an `SG_READ_ONLY` segment-flag issue in the toolchain's
  bundled linker), in which case `verify-soundness.sh` automatically
  re-runs the benchmark through the Lean interpreter instead.

The Docker image is built from `ubuntu:22.04` by the included
`Dockerfile`, which installs elan, copies the sources, and precompiles
the full development; it supports both x86-64 and ARM64.
