/-
  MGQL: Small-Step Operational Semantics (Expressions) -- Paper Theorem 6.1

  Developed ALONGSIDE the big-step evaluator `evalExpr` (Semantics.lean) and
  proven equivalent, so a flag can select either engine and the equivalence
  theorem guarantees they agree. This is the expression layer (Thm 6.1); the
  pattern and query layers extend the same pattern.

  Because `evalExpr` can produce graph elements and lists (via variable lookup)
  that the source `Expr` grammar cannot represent as terminal forms, the step
  relation runs over a runtime-expression type `RExpr` that mirrors `Expr` plus
  a `val : Value` embedding. Terminal form is `val v`.
-/
import MGQL.Metatheory

namespace MGQL

/-! ## Runtime expressions -/

inductive RExpr where
  | val        : Value -> RExpr
  | const      : Literal -> RExpr
  | null       : RExpr
  | var        : Name -> RExpr
  | propAccess : Name -> Name -> RExpr
  | arithOp    : ArithOp -> RExpr -> RExpr -> RExpr
  | agg        : AggOp -> AggQualifier -> RExpr -> RExpr
  | pred       : Pred -> RExpr

/-- Embed a source expression as a (not-yet-reduced) runtime expression. -/
def ofExpr : Expr -> RExpr
  | .const lit        => .const lit
  | .null             => .null
  | .var x            => .var x
  | .propAccess x k   => .propAccess x k
  | .arithOp op e1 e2 => .arithOp op (ofExpr e1) (ofExpr e2)
  | .agg op qual e    => .agg op qual (ofExpr e)
  | .pred phi         => .pred phi

/-- The property-access leaf computation, factored out of `evalExpr` so the
    step rule and the big-step evaluator share it definitionally. -/
def evalPropAccess (G : PropertyGraph) (rho : Record) (x k : Name) : Value :=
  match rho.lookup x with
  | .nodeRef _ n => if h : n < G.numNodes then (G.nodeProps (Fin.mk n h)).lookup k else .null
  | .edgeRef _ e => if h : e < G.numEdges then (G.edgeProps (Fin.mk e h)).lookup k else .null
  | _ => .null

/-- The aggregation leaf computation, factored out of `evalExpr`. -/
def evalAggStep (op : AggOp) (qual : AggQualifier) (v : Value) : Value :=
  match v with
  | .list vs => evalAggOnValues op qual vs.toList
  | _ =>
    match op with
    | .count => if v.isNull then .ofInt 0 else .ofInt 1
    | _ => .null

/-! ## Big-step meaning of a runtime expression (used only in the proofs) -/

def evalR (G : PropertyGraph) (site : GraphSite) (rho : Record) : RExpr -> Value
  | .val v            => v
  | .const lit        => evalLiteral lit
  | .null             => .null
  | .var x            => rho.lookup x
  | .propAccess x k   => evalPropAccess G rho x k
  | .arithOp op e1 e2 => evalArith op (evalR G site rho e1) (evalR G site rho e2)
  | .agg op qual e    => evalAggStep op qual (evalR G site rho e)
  | .pred phi         => evalPredValue G site rho phi

/-! ## The small-step relation (Paper: fEval) -/

inductive ExprStep (G : PropertyGraph) (site : GraphSite) (rho : Record) :
    RExpr -> RExpr -> Prop where
  | constVal (lit) :
      ExprStep G site rho (.const lit) (.val (evalLiteral lit))
  | nullVal :
      ExprStep G site rho .null (.val .null)
  | varVal (x) :
      ExprStep G site rho (.var x) (.val (rho.lookup x))
  | propVal (x k) :
      ExprStep G site rho (.propAccess x k) (.val (evalPropAccess G rho x k))
  | predVal (phi) :
      ExprStep G site rho (.pred phi) (.val (evalPredValue G site rho phi))
  | arith1 {e1 e1'} (op) (e2) :
      ExprStep G site rho e1 e1' ->
      ExprStep G site rho (.arithOp op e1 e2) (.arithOp op e1' e2)
  | arith2 {e2 e2'} (op) (v1) :
      ExprStep G site rho e2 e2' ->
      ExprStep G site rho (.arithOp op (.val v1) e2) (.arithOp op (.val v1) e2')
  | arithVal (op v1 v2) :
      ExprStep G site rho (.arithOp op (.val v1) (.val v2)) (.val (evalArith op v1 v2))
  | agg1 {e e'} (op qual) :
      ExprStep G site rho e e' ->
      ExprStep G site rho (.agg op qual e) (.agg op qual e')
  | aggVal (op qual v) :
      ExprStep G site rho (.agg op qual (.val v)) (.val (evalAggStep op qual v))

/-- Reflexive-transitive closure (hand-rolled: Init-only, no Mathlib). -/
inductive ExprStepStar (G : PropertyGraph) (site : GraphSite) (rho : Record) :
    RExpr -> RExpr -> Prop where
  | refl (a) : ExprStepStar G site rho a a
  | step {a b c} :
      ExprStep G site rho a b -> ExprStepStar G site rho b c -> ExprStepStar G site rho a c

/-! ## Basic closure lemmas -/

theorem ExprStepStar.one {G site rho} {a b : RExpr}
    (h : ExprStep G site rho a b) : ExprStepStar G site rho a b :=
  .step h (.refl b)

theorem ExprStepStar.trans {G site rho} {a b c : RExpr}
    (h1 : ExprStepStar G site rho a b) (h2 : ExprStepStar G site rho b c) :
    ExprStepStar G site rho a c := by
  induction h1 with
  | refl _ => exact h2
  | step hs _ ih => exact .step hs (ih h2)

/-! ## Congruence lemmas: lift single-step congruence to the closure -/

theorem arith_cong1 {G site rho} {e1 e1' : RExpr} (op) (e2 : RExpr)
    (h : ExprStepStar G site rho e1 e1') :
    ExprStepStar G site rho (.arithOp op e1 e2) (.arithOp op e1' e2) := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.arith1 op e2 hs) ih

theorem arith_cong2 {G site rho} {e2 e2' : RExpr} (op) (v1 : Value)
    (h : ExprStepStar G site rho e2 e2') :
    ExprStepStar G site rho (.arithOp op (.val v1) e2) (.arithOp op (.val v1) e2') := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.arith2 op v1 hs) ih

theorem agg_cong {G site rho} {e e' : RExpr} (op qual)
    (h : ExprStepStar G site rho e e') :
    ExprStepStar G site rho (.agg op qual e) (.agg op qual e') := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.agg1 op qual hs) ih

/-! ## Backward direction: each step preserves the big-step meaning -/

theorem evalR_ofExpr (G site rho) (e : Expr) :
    evalR G site rho (ofExpr e) = evalExpr G site rho e := by
  induction e using Expr.inductionOpaque with
  | const lit => rfl
  | null => rfl
  | var x => rfl
  | propAccess x k => rfl
  | arithOp op e1 e2 ih1 ih2 => simp only [ofExpr, evalR, evalExpr, ih1, ih2]
  | agg op qual e ih =>
      simp only [ofExpr, evalR, ih]
      rfl
  | pred phi => rfl

theorem exprStep_preserves_evalR {G site rho} {a b : RExpr}
    (h : ExprStep G site rho a b) : evalR G site rho a = evalR G site rho b := by
  induction h with
  | constVal _ => rfl
  | nullVal => rfl
  | varVal _ => rfl
  | propVal _ _ => rfl
  | predVal _ => rfl
  | arith1 _ _ _ ih => simp only [evalR, ih]
  | arith2 _ _ _ ih => simp only [evalR, ih]
  | arithVal _ _ _ => rfl
  | agg1 _ _ _ ih => simp only [evalR, ih]
  | aggVal _ _ _ => rfl

theorem exprStepStar_preserves_evalR {G site rho} {a b : RExpr}
    (h : ExprStepStar G site rho a b) : evalR G site rho a = evalR G site rho b := by
  induction h with
  | refl _ => rfl
  | step hs _ ih => exact (exprStep_preserves_evalR hs).trans ih

/-! ## Forward direction: the closure reaches the big-step value -/

theorem exprStep_complete (G site rho) (e : Expr) :
    ExprStepStar G site rho (ofExpr e) (.val (evalExpr G site rho e)) := by
  induction e using Expr.inductionOpaque with
  | const lit => exact .one (.constVal lit)
  | null => exact .one .nullVal
  | var x => exact .one (.varVal x)
  | propAccess x k => exact .one (.propVal x k)
  | arithOp op e1 e2 ih1 ih2 =>
      refine .trans (arith_cong1 op (ofExpr e2) ih1) ?_
      refine .trans (arith_cong2 op (evalExpr G site rho e1) ih2) ?_
      exact .one (.arithVal op _ _)
  | agg op qual e ih =>
      refine .trans (agg_cong op qual ih) ?_
      exact .one (.aggVal op qual _)
  | pred phi => exact .one (.predVal phi)

/-! ## Equivalence of the two engines (Paper Theorem 6.1, small-step form) -/

theorem exprStep_correct (G site rho) (e : Expr) (v : Value) :
    ExprStepStar G site rho (ofExpr e) (.val v) <-> evalExpr G site rho e = v := by
  constructor
  · intro h
    have hpres := exprStepStar_preserves_evalR h
    rw [evalR_ofExpr] at hpres
    exact hpres
  · intro h
    subst h
    exact exprStep_complete G site rho e

/-! ## Progress (Paper Theorem 6.1, small-step form)

    Every runtime expression is either a value or can take a step. In the
    open-graph setting this needs no typing hypothesis: the relation is total on
    non-values, so progress is unconditional. -/
theorem exprStep_progress (G site rho) (a : RExpr) :
    (exists v, a = .val v) \/ (exists b, ExprStep G site rho a b) := by
  induction a with
  | val v => exact Or.inl ⟨v, rfl⟩
  | const lit => exact Or.inr ⟨_, .constVal lit⟩
  | null => exact Or.inr ⟨_, .nullVal⟩
  | var x => exact Or.inr ⟨_, .varVal x⟩
  | propAccess x k => exact Or.inr ⟨_, .propVal x k⟩
  | pred phi => exact Or.inr ⟨_, .predVal phi⟩
  | arithOp op e1 e2 ih1 ih2 =>
      rcases ih1 with ⟨v1, rfl⟩ | ⟨b1, hb1⟩
      · rcases ih2 with ⟨v2, rfl⟩ | ⟨b2, hb2⟩
        · exact Or.inr ⟨_, .arithVal op v1 v2⟩
        · exact Or.inr ⟨_, .arith2 op v1 hb2⟩
      · exact Or.inr ⟨_, .arith1 op e2 hb1⟩
  | agg op qual e ih =>
      rcases ih with ⟨v, rfl⟩ | ⟨b, hb⟩
      · exact Or.inr ⟨_, .aggVal op qual v⟩
      · exact Or.inr ⟨_, .agg1 op qual hb⟩

-- ============================================================
--  Preservation (Paper Theorem 6.1, small-step form, open graphs)
--
--  A runtime typing judgment `RExprTyping` types partially-reduced
--  expressions: the `val` rule types embedded values by admissibility, the
--  structural rules mirror the open-graph fragment of `ExprTyping`, and
--  `subsume` mirrors static subsumption. Preservation holds at the same type
--  (the paper's "exists tau1 <: tau" is absorbed by the `subsume` rule), and
--  the closed-graph refined property rules are vacuous under the open-site
--  hypothesis, per the paper's open/closed split.
-- ============================================================

/-! ### Local admissibility lemmas
    (mirrors of `private` lemmas in Metatheory.lean, which are not exported) -/

private theorem ss_null_admissible_intN :
    RecordSchema.valueAdmissible Value.null GSort.intN = true := rfl

private theorem ss_null_admissible_nullSort :
    RecordSchema.valueAdmissible Value.null GSort.nullSort = true := rfl

private theorem ss_null_admissible_anyScalarN :
    RecordSchema.valueAdmissible Value.null GSort.anyScalarN = true := rfl

private theorem ss_int_admissible_int (n : Int) :
    RecordSchema.valueAdmissible (Value.ofInt n) GSort.int = true := by
  unfold RecordSchema.valueAdmissible
  simp [GSort.int, Value.ofInt, Value.hasExtSort, PrimValue.hasSort]

private theorem ss_int_admissible_intN (n : Int) :
    RecordSchema.valueAdmissible (Value.ofInt n) GSort.intN = true := by
  unfold RecordSchema.valueAdmissible
  simp [GSort.intN, Value.ofInt, Value.hasExtSort, PrimValue.hasSort]

private theorem ss_string_admissible_string (s : String) :
    RecordSchema.valueAdmissible (Value.ofString s) GSort.string = true := by
  unfold RecordSchema.valueAdmissible
  simp [GSort.string, Value.ofString, Value.hasExtSort, PrimValue.hasSort]

private theorem ss_bool_admissible_bool (b : Bool) :
    RecordSchema.valueAdmissible (Value.ofBool b) GSort.bool = true := by
  unfold RecordSchema.valueAdmissible
  simp [GSort.bool, Value.ofBool, Value.hasExtSort, PrimValue.hasSort]

private theorem ss_bool_admissible_boolN (b : Bool) :
    RecordSchema.valueAdmissible (Value.ofBool b) GSort.boolN = true := by
  unfold RecordSchema.valueAdmissible
  simp [GSort.boolN, Value.ofBool, Value.hasExtSort, PrimValue.hasSort]

private theorem ss_null_admissible_boolN :
    RecordSchema.valueAdmissible Value.null GSort.boolN = true := rfl

private theorem ss_evalArith_admissible_intN (op : ArithOp) (v1 v2 : Value) :
    RecordSchema.valueAdmissible (evalArith op v1 v2) GSort.intN = true := by
  unfold evalArith
  match h1 : v1.asInt, h2 : v2.asInt with
  | none, _ =>
    simp only [h1]
    exact ss_null_admissible_intN
  | some _, none =>
    simp only [h1, h2]
    exact ss_null_admissible_intN
  | some n1, some n2 =>
    simp only [h1, h2]
    split
    · exact ss_int_admissible_intN _
    · exact ss_int_admissible_intN _
    · exact ss_int_admissible_intN _
    · split
      · exact ss_null_admissible_intN
      · exact ss_int_admissible_intN _

private theorem ss_evalAggOnValues_count_admissible (qual : AggQualifier)
    (vals : List Value) :
    RecordSchema.valueAdmissible (evalAggOnValues .count qual vals) GSort.int = true := by
  simp only [evalAggOnValues]
  exact ss_int_admissible_int _

private theorem ss_evalAggOnValues_admissible_intN (op : AggOp) (qual : AggQualifier)
    (vals : List Value) :
    RecordSchema.valueAdmissible (evalAggOnValues op qual vals) GSort.intN = true := by
  cases op <;> simp only [evalAggOnValues] <;> (try split) <;>
    first | exact ss_int_admissible_intN _ | exact ss_null_admissible_intN

private theorem ss_evalAggStep_count_admissible (qual : AggQualifier) (v : Value) :
    RecordSchema.valueAdmissible (evalAggStep .count qual v) GSort.int = true := by
  cases v with
  | list vs =>
      simp only [evalAggStep]
      exact ss_evalAggOnValues_count_admissible qual vs.toList
  | prim p => simp only [evalAggStep]; split <;> exact ss_int_admissible_int _
  | nodeRef s n => simp only [evalAggStep]; split <;> exact ss_int_admissible_int _
  | edgeRef s e => simp only [evalAggStep]; split <;> exact ss_int_admissible_int _
  | null => simp only [evalAggStep]; split <;> exact ss_int_admissible_int _

private theorem ss_evalAggStep_admissible_intN (op : AggOp) (qual : AggQualifier)
    (v : Value) :
    RecordSchema.valueAdmissible (evalAggStep op qual v) GSort.intN = true := by
  cases v with
  | list vs =>
      simp only [evalAggStep]
      exact ss_evalAggOnValues_admissible_intN op qual vs.toList
  | prim p =>
      simp only [evalAggStep]
      cases op <;> first
        | exact ss_null_admissible_intN
        | (split <;> exact ss_int_admissible_intN _)
  | nodeRef s n =>
      simp only [evalAggStep]
      cases op <;> first
        | exact ss_null_admissible_intN
        | (split <;> exact ss_int_admissible_intN _)
  | edgeRef s e =>
      simp only [evalAggStep]
      cases op <;> first
        | exact ss_null_admissible_intN
        | (split <;> exact ss_int_admissible_intN _)
  | null =>
      simp only [evalAggStep]
      cases op <;> first
        | exact ss_null_admissible_intN
        | (split <;> exact ss_int_admissible_intN _)

private theorem ss_primOrNull_admissible_anyScalarN {v : Value}
    (h : (∃ p, v = Value.prim p) ∨ v = Value.null) :
    RecordSchema.valueAdmissible v GSort.anyScalarN = true := by
  rcases h with ⟨p, rfl⟩ | rfl
  · cases p <;> rfl
  · rfl

private theorem ss_propmap_lookup_wf {pm : PropMap} (hwf : PropMapValuesWF pm)
    (key : Name) :
    (∃ p, pm.lookup key = Value.prim p) ∨ pm.lookup key = Value.null := by
  unfold PropMap.lookup
  cases hf : pm.find? (fun e => e.1 == key) with
  | none => exact Or.inr rfl
  | some e =>
    obtain ⟨k', val⟩ := e
    exact hwf k' val (List.mem_of_find?_eq_some hf)

private theorem ss_evalPropAccess_admissible {G : PropertyGraph}
    (hWF : GraphValuesWF G) (rho : Record) (x k : Name) :
    RecordSchema.valueAdmissible (evalPropAccess G rho x k) GSort.anyScalarN = true := by
  unfold evalPropAccess
  cases hx : rho.lookup x with
  | nodeRef s n =>
      show RecordSchema.valueAdmissible
        (if h : n < G.numNodes then (G.nodeProps ⟨n, h⟩).lookup k else Value.null)
        GSort.anyScalarN = true
      split
      · rename_i h
        exact ss_primOrNull_admissible_anyScalarN
          (ss_propmap_lookup_wf (hWF.1 ⟨n, h⟩) k)
      · exact ss_null_admissible_anyScalarN
  | edgeRef s eid =>
      show RecordSchema.valueAdmissible
        (if h : eid < G.numEdges then (G.edgeProps ⟨eid, h⟩).lookup k else Value.null)
        GSort.anyScalarN = true
      split
      · rename_i h
        exact ss_primOrNull_admissible_anyScalarN
          (ss_propmap_lookup_wf (hWF.2 ⟨eid, h⟩) k)
      · exact ss_null_admissible_anyScalarN
  | prim p => exact ss_null_admissible_anyScalarN
  | null => exact ss_null_admissible_anyScalarN
  | list l => exact ss_null_admissible_anyScalarN

/-! ### Runtime expression typing -/

/-- Typing for partially-reduced expressions. The `val` rule types embedded
    values by admissibility; the structural rules mirror the open-graph
    fragment of `ExprTyping` (the static premises that only constrain the
    SOURCE program, e.g. `DynRefine` side conditions, are dropped: they are
    not needed for the runtime invariant, which makes this judgment a sound
    over-approximation); `subsume` mirrors static subsumption. -/
inductive RExprTyping (Ctx : RecordSchema) : RExpr -> GSort -> Prop where
  | val {v : Value} {t : GSort}
      (hAdm : RecordSchema.valueAdmissible v t = true) :
      RExprTyping Ctx (.val v) t
  | constInt (n : Int) : RExprTyping Ctx (.const (.int n)) GSort.int
  | constString (s : String) : RExprTyping Ctx (.const (.string s)) GSort.string
  | constBool (b : Bool) : RExprTyping Ctx (.const (.bool b)) GSort.bool
  | constNull : RExprTyping Ctx .null GSort.nullSort
  | var {x : Name} {t : GSort} (hLookup : Ctx.lookup x = some t) :
      RExprTyping Ctx (.var x) t
  | propAccess (x k : Name) : RExprTyping Ctx (.propAccess x k) GSort.anyScalarN
  | arith {e1 e2 : RExpr} {t1 t2 : GSort} (op : ArithOp)
      (h1 : RExprTyping Ctx e1 t1) (h2 : RExprTyping Ctx e2 t2) :
      RExprTyping Ctx (.arithOp op e1 e2) GSort.intN
  | aggCount {e : RExpr} {t : GSort} (qual : AggQualifier)
      (h : RExprTyping Ctx e t) :
      RExprTyping Ctx (.agg .count qual e) GSort.int
  | aggOther {e : RExpr} {t : GSort} {op : AggOp} (qual : AggQualifier)
      (hOp : op = .sum ∨ op = .max ∨ op = .min)
      (h : RExprTyping Ctx e t) :
      RExprTyping Ctx (.agg op qual e) GSort.intN
  | predV {phi : Pred}
      (hV : phi = .true ∨ phi = .false ∨ ∃ e, phi = .isNull e) :
      RExprTyping Ctx (.pred phi) GSort.bool
  | predN (phi : Pred) : RExprTyping Ctx (.pred phi) GSort.boolN
  | subsume {e : RExpr} {t1 t2 : GSort}
      (h : RExprTyping Ctx e t1) (hSub : Subtype t1 t2) :
      RExprTyping Ctx e t2

/-- A statically well-typed source expression is runtime-typed at the same
    sort, for open graph sites (the closed refined rules are vacuous). -/
theorem rExprTyping_of_exprTyping
    {ctx : TypingCtx} {Ctx : RecordSchema} {box : AggDepth} {hat : RefCtx}
    {e : Expr} {t : GSort} {omega' : VarSet}
    (hOpen : ctx.schemaMap.isClosed ctx.graphSite = false)
    (hType : ExprTyping ctx Ctx box hat e t omega') :
    RExprTyping Ctx (ofExpr e) t := by
  induction hType using ExprTyping.inductionOpaque with
  | constInt => rename_i n; exact .constInt n
  | constString => rename_i s; exact .constString s
  | constBool => rename_i b; exact .constBool b
  | constNull => exact .constNull
  | var => rename_i hLookup; exact .var hLookup
  | arithOp => rename_i ih1 ih2; exact .arith _ ih1 ih2
  | propAccessOpen => exact .propAccess _ _
  | propAccessSchema =>
      rename_i hClosed _
      rw [hOpen] at hClosed
      exact Bool.noConfusion hClosed
  | propAccessListOpen => exact .propAccess _ _
  | propAccessListClosed =>
      rename_i hClosed _
      rw [hOpen] at hClosed
      exact Bool.noConfusion hClosed
  | countSingleton => rename_i ih; exact .aggCount _ ih
  | aggSingleton => rename_i hOp _ _ _ _ ih; exact .aggOther _ hOp ih
  | countGroup => rename_i ih; exact .aggCount _ ih
  | aggGroup => rename_i hOp _ _ ih; exact .aggOther _ hOp ih
  | pred =>
    rename_i phi tP omega1 hp
    cases hp with
    | true => exact .predV (Or.inl rfl)
    | false => exact .predV (Or.inr (Or.inl rfl))
    | isNull e => exact .predV (Or.inr (Or.inr ⟨_, rfl⟩))
    | relOp => exact .predN _
    | not => exact .predN _
    | and => exact .predN _
    | or => exact .predN _
  | subsume => rename_i hSub ih; exact .subsume ih hSub

/-- Preservation (Paper Theorem 6.1, small-step form).  A single step
    preserves the runtime typing at the same sort; the paper's
    "exists tau1 with tau1 <: tau" conclusion follows because the runtime
    judgment carries subsumption. -/
theorem exprStep_preservation {G : PropertyGraph} {site : GraphSite}
    {rho : Record} {Ctx : RecordSchema}
    (hConf : RecordConforms rho Ctx) (hWF : GraphValuesWF G)
    {a : RExpr} {t : GSort} (hTy : RExprTyping Ctx a t) :
    ∀ {b : RExpr}, ExprStep G site rho a b -> RExprTyping Ctx b t := by
  induction hTy with
  | val hAdm => intro b hStep; cases hStep
  | constInt n => intro b hStep; cases hStep; exact .val (ss_int_admissible_int n)
  | constString s => intro b hStep; cases hStep; exact .val (ss_string_admissible_string s)
  | constBool bb => intro b hStep; cases hStep; exact .val (ss_bool_admissible_bool bb)
  | constNull => intro b hStep; cases hStep; exact .val ss_null_admissible_nullSort
  | var hLookup =>
      intro b hStep; cases hStep
      exact .val (hConf.2 _ _ (RecordSchema.lookup_some_mem hLookup))
  | propAccess x k =>
      intro b hStep; cases hStep
      exact .val (ss_evalPropAccess_admissible hWF rho x k)
  | arith op h1 h2 ih1 ih2 =>
      intro b hStep
      cases hStep with
      | arith1 => rename_i hs; exact .arith op (ih1 hs) h2
      | arith2 => rename_i hs; exact .arith op h1 (ih2 hs)
      | arithVal => exact .val (ss_evalArith_admissible_intN op _ _)
  | aggCount qual h ih =>
      intro b hStep
      cases hStep with
      | agg1 => rename_i hs; exact .aggCount qual (ih hs)
      | aggVal => exact .val (ss_evalAggStep_count_admissible qual _)
  | aggOther qual hOp h ih =>
      intro b hStep
      cases hStep with
      | agg1 => rename_i hs; exact .aggOther qual hOp (ih hs)
      | aggVal => exact .val (ss_evalAggStep_admissible_intN _ qual _)
  | predV hV =>
      intro b hStep
      cases hStep
      rcases hV with rfl | rfl | ⟨e0, rfl⟩
      · exact .val (ss_bool_admissible_bool true)
      · exact .val (ss_bool_admissible_bool false)
      · exact .val (ss_bool_admissible_bool _)
  | predN phi =>
      intro b hStep
      cases hStep
      cases hpv : evalPred G site rho phi with
      | some bb =>
        have hv : evalPredValue G site rho phi = Value.ofBool bb := by
          unfold evalPredValue; rw [hpv]
        rw [hv]
        exact .val (ss_bool_admissible_boolN bb)
      | none =>
        have hv : evalPredValue G site rho phi = Value.null := by
          unfold evalPredValue; rw [hpv]
        rw [hv]
        exact .val ss_null_admissible_boolN
  | subsume h hSub ih =>
      intro b hStep
      exact .subsume (ih hStep) hSub

/-- Preservation along a reduction sequence. -/
theorem exprStepStar_preservation {G : PropertyGraph} {site : GraphSite}
    {rho : Record} {Ctx : RecordSchema}
    (hConf : RecordConforms rho Ctx) (hWF : GraphValuesWF G)
    {a b : RExpr} (hSteps : ExprStepStar G site rho a b) :
    ∀ {t : GSort}, RExprTyping Ctx a t -> RExprTyping Ctx b t := by
  induction hSteps with
  | refl _ => intro t h; exact h
  | step =>
      rename_i hs _ ih
      intro t h
      exact ih (exprStep_preservation hConf hWF h hs)

/-- A runtime-typed value is admissible at its sort (inversion through
    subsumption chains, via `admissible_mono`). -/
theorem rExprTyping_val_admissible {Ctx : RecordSchema} {v : Value} {t : GSort}
    (h : RExprTyping Ctx (.val v) t) :
    RecordSchema.valueAdmissible v t = true := by
  generalize hE : RExpr.val v = a at h
  induction h with
  | val hAdm =>
      injection hE with hv
      rw [hv]; exact hAdm
  | subsume h hSub ih => exact admissible_mono _ _ _ (ih hE) hSub
  | constInt n => exact RExpr.noConfusion hE
  | constString s => exact RExpr.noConfusion hE
  | constBool b => exact RExpr.noConfusion hE
  | constNull => exact RExpr.noConfusion hE
  | var hLookup => exact RExpr.noConfusion hE
  | propAccess x k => exact RExpr.noConfusion hE
  | arith op h1 h2 ih1 ih2 => exact RExpr.noConfusion hE
  | aggCount qual h ih => exact RExpr.noConfusion hE
  | aggOther qual hOp h ih => exact RExpr.noConfusion hE
  | predV hV => exact RExpr.noConfusion hE
  | predN phi => exact RExpr.noConfusion hE

/-- Small-step Expression Soundness for open graphs (Paper Theorem 6.1).
    Together with `exprStep_progress` this is the paper's small-step reading
    of Theorem 6.1: a well-typed expression can always step (progress), every
    step preserves typing (`exprStep_preservation`), and a reduction sequence
    that reaches a value lands in the declared type. Scoped to open graph
    sites; combined with `exprStep_correct` the same conclusion transfers to
    the big-step engine, which is what makes the two engines interchangeable
    behind a flag. -/
theorem exprSmallStep_soundness_open
    {ctx : TypingCtx} {G : PropertyGraph} {site : GraphSite} {rho : Record}
    {Ctx : RecordSchema} {box : AggDepth} {hat : RefCtx}
    {e : Expr} {t : GSort} {omega' : VarSet} {v : Value}
    (hOpen : ctx.schemaMap.isClosed ctx.graphSite = false)
    (hType : ExprTyping ctx Ctx box hat e t omega')
    (hConf : RecordConforms rho Ctx) (hWF : GraphValuesWF G)
    (hSteps : ExprStepStar G site rho (ofExpr e) (.val v)) :
    RecordSchema.valueAdmissible v t = true :=
  rExprTyping_val_admissible
    (exprStepStar_preservation hConf hWF hSteps
      (rExprTyping_of_exprTyping hOpen hType))

-- ============================================================
--  Pattern layer (Paper Theorem 6.2)
--
--  Runtime patterns `RPat` mirror `Pattern` with a `table` embedding for
--  computed binding tables. Because the big-step combination forms consult
--  syntactic data of their sub-pattern (`patternTailVar`, `patternVars`,
--  `patternLeadVar`) that is erased once the sub-pattern reduces to a table,
--  the runtime `step`/`quantified` nodes carry those extracted names -- the
--  same closure-style bookkeeping the paper's configurations keep by leaving
--  the pattern syntax in the configuration.
--
--  Paper Theorem 6.2 is stated in star form (no separate progress /
--  preservation clauses): if |- P : Gamma and P -->* B then B conforms to
--  Gamma. We mechanize exactly that: `PatStep` is the step relation,
--  `patStep_progress` gives progress, `patStep_correct` proves the reduction
--  relation computes precisely `evalPattern` (making the two engines
--  interchangeable), and `patSmallStep_soundness` is the star-form theorem.
-- ============================================================

/-- Runtime patterns: `Pattern` plus an embedded computed table. The
    `step` node carries the original prefix's tail variable, and the
    `quantified` node carries the inner pattern's variable list and
    lead/tail variables. -/
inductive RPat where
  | table       : BindingTable -> RPat
  | node        : NodeAtom -> RPat
  | edge        : NodeAtom -> EdgeAtom -> Direction -> NodeAtom -> RPat
  | step        : RPat -> Option Name -> EdgeAtom -> Direction -> NodeAtom -> RPat
  | grouped     : RPat -> RPat
  | quantified  : RPat -> List Name -> Option Name -> Option Name -> Quantifier -> RPat
  | patternList : RPat -> RPat -> RPat
  | trail       : RPat -> RPat

/-- Embed a source pattern, extracting the syntactic data the combination
    steps will need after sub-patterns reduce to tables. -/
def ofPattern : Pattern -> RPat
  | .node na => .node na
  | .edge n1 rel dir n2 => .edge n1 rel dir n2
  | .step P rel dir n2 => .step (ofPattern P) (patternTailVar P) rel dir n2
  | .grouped P => .grouped (ofPattern P)
  | .quantified P K =>
      .quantified (ofPattern P) (patternVars P) (patternLeadVar P) (patternTailVar P) K
  | .patternList P1 P2 => .patternList (ofPattern P1) (ofPattern P2)

/-- Runtime pattern for trail mode: each comma component is wrapped in a
    `trail` gate whose value rule applies the distinct-edge filter,
    mirroring the paper's FS-PatExp-Done discarding the visited set at a
    path component's completion. -/
def ofPatternT : Pattern -> RPat
  | .patternList P1 P2 => .patternList (ofPatternT P1) (ofPatternT P2)
  | P => .trail (ofPattern P)

/-- The step-extension combination, factored out of `evalPattern`'s `.step`
    branch so the small-step combine rule and the big-step evaluator share it
    definitionally (the prefix table and its tail variable are parameters). -/
def stepCombine (G : PropertyGraph) (site : GraphSite) (B : BindingTable)
    (tv? : Option Name) (rel : EdgeAtom) (dir : Direction) (n2 : NodeAtom) :
    BindingTable :=
  B.flatMap fun rho =>
    match tv? with
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
        edgeResults.filterMap fun rhoEdge =>
          if rho.agreeOn rhoEdge then
            some (rho.merge rhoEdge)
          else none

/-- The quantified-path combination, factored out of `evalPattern`'s
    `.quantified` branch. -/
def quantCombine (G : PropertyGraph) (B : BindingTable) (vars : List Name)
    (lv? tv? : Option Name) (K : Quantifier) : BindingTable :=
  let lo := K.lo
  let hi := match K.hi with
    | some h => h
    | none => G.numEdges
  match lv?, tv? with
  | some lv, some tv => evalQuantified vars B lv tv lo hi
  | _, _ => B

theorem evalPattern_step_eq (G : PropertyGraph) (site : GraphSite)
    (P : Pattern) (rel : EdgeAtom) (dir : Direction) (n2 : NodeAtom) :
    evalPattern G site (.step P rel dir n2)
      = stepCombine G site (evalPattern G site P) (patternTailVar P) rel dir n2 := by
  simp only [evalPattern]; rfl

theorem evalPattern_quantified_eq (G : PropertyGraph) (site : GraphSite)
    (P : Pattern) (K : Quantifier) :
    evalPattern G site (.quantified P K)
      = quantCombine G (evalPattern G site P) (patternVars P)
          (patternLeadVar P) (patternTailVar P) K := by
  simp only [evalPattern, quantCombine]
  rfl

/-! ### The pattern step relation (Paper: FSPat rules) -/

inductive PatStep (G : PropertyGraph) (site : GraphSite) : RPat -> RPat -> Prop where
  -- Atom matching is a single reduction, as in the paper's atom rules.
  | nodeVal (na) :
      PatStep G site (.node na) (.table (matchNode G site na))
  | edgeVal (n1 rel dir n2) :
      PatStep G site (.edge n1 rel dir n2)
        (.table (evalPattern G site (.edge n1 rel dir n2)))
  -- Congruence: reduce inside a combination form.
  | stepCong {P P'} (tv? rel dir n2) :
      PatStep G site P P' ->
      PatStep G site (.step P tv? rel dir n2) (.step P' tv? rel dir n2)
  | groupedCong {P P'} :
      PatStep G site P P' ->
      PatStep G site (.grouped P) (.grouped P')
  | quantCong {P P'} (vars lv? tv? K) :
      PatStep G site P P' ->
      PatStep G site (.quantified P vars lv? tv? K) (.quantified P' vars lv? tv? K)
  | listCong1 {P1 P1'} (P2) :
      PatStep G site P1 P1' ->
      PatStep G site (.patternList P1 P2) (.patternList P1' P2)
  | listCong2 {P2 P2'} (B1) :
      PatStep G site P2 P2' ->
      PatStep G site (.patternList (.table B1) P2) (.patternList (.table B1) P2')
  -- Combination: all sub-results computed, combine the tables.
  | stepVal (B tv? rel dir n2) :
      PatStep G site (.step (.table B) tv? rel dir n2)
        (.table (stepCombine G site B tv? rel dir n2))
  | groupedVal (B) :
      PatStep G site (.grouped (.table B)) (.table B)
  | quantVal (B vars lv? tv? K) :
      PatStep G site (.quantified (.table B) vars lv? tv? K)
        (.table (quantCombine G B vars lv? tv? K))
  | listVal (B1 B2) :
      PatStep G site (.patternList (.table B1) (.table B2))
        (.table (bindingTableJoin B1 B2))
  | trailCong {P P'} :
      PatStep G site P P' ->
      PatStep G site (.trail P) (.trail P')
  | trailVal (B) :
      PatStep G site (.trail (.table B)) (.table (B.filter Record.isTrail))

/-- Reflexive-transitive closure of `PatStep`. -/
inductive PatStepStar (G : PropertyGraph) (site : GraphSite) : RPat -> RPat -> Prop where
  | refl (p) : PatStepStar G site p p
  | step {p q r} :
      PatStep G site p q -> PatStepStar G site q r -> PatStepStar G site p r

theorem PatStepStar.one {G site} {p q : RPat}
    (h : PatStep G site p q) : PatStepStar G site p q :=
  .step h (.refl q)

theorem PatStepStar.trans {G site} {p q r : RPat}
    (h1 : PatStepStar G site p q) (h2 : PatStepStar G site q r) :
    PatStepStar G site p r := by
  induction h1 with
  | refl _ => exact h2
  | step hs _ ih => exact .step hs (ih h2)

/-! ### Progress: every non-table runtime pattern can step -/

theorem patStep_progress (G : PropertyGraph) (site : GraphSite) (p : RPat) :
    (∃ B, p = .table B) ∨ (∃ q, PatStep G site p q) := by
  induction p with
  | table B => exact Or.inl ⟨B, rfl⟩
  | node na => exact Or.inr ⟨_, .nodeVal na⟩
  | edge n1 rel dir n2 => exact Or.inr ⟨_, .edgeVal n1 rel dir n2⟩
  | step P tv? rel dir n2 ih =>
      rcases ih with ⟨B, rfl⟩ | ⟨q, hq⟩
      · exact Or.inr ⟨_, .stepVal B tv? rel dir n2⟩
      · exact Or.inr ⟨_, .stepCong tv? rel dir n2 hq⟩
  | grouped P ih =>
      rcases ih with ⟨B, rfl⟩ | ⟨q, hq⟩
      · exact Or.inr ⟨_, .groupedVal B⟩
      · exact Or.inr ⟨_, .groupedCong hq⟩
  | quantified P vars lv? tv? K ih =>
      rcases ih with ⟨B, rfl⟩ | ⟨q, hq⟩
      · exact Or.inr ⟨_, .quantVal B vars lv? tv? K⟩
      · exact Or.inr ⟨_, .quantCong vars lv? tv? K hq⟩
  | patternList P1 P2 ih1 ih2 =>
      rcases ih1 with ⟨B1, rfl⟩ | ⟨q1, hq1⟩
      · rcases ih2 with ⟨B2, rfl⟩ | ⟨q2, hq2⟩
        · exact Or.inr ⟨_, .listVal B1 B2⟩
        · exact Or.inr ⟨_, .listCong2 B1 hq2⟩
      · exact Or.inr ⟨_, .listCong1 P2 hq1⟩
  | trail P ih =>
      rcases ih with ⟨B, rfl⟩ | ⟨q, hq⟩
      · exact Or.inr ⟨_, .trailVal B⟩
      · exact Or.inr ⟨_, .trailCong hq⟩

/-! ### Equivalence with the big-step evaluator -/

/-- Big-step meaning of a runtime pattern (used only in the proofs). -/
def patEvalR (G : PropertyGraph) (site : GraphSite) : RPat -> BindingTable
  | .table B => B
  | .node na => matchNode G site na
  | .edge n1 rel dir n2 => evalPattern G site (.edge n1 rel dir n2)
  | .step P tv? rel dir n2 => stepCombine G site (patEvalR G site P) tv? rel dir n2
  | .grouped P => patEvalR G site P
  | .quantified P vars lv? tv? K => quantCombine G (patEvalR G site P) vars lv? tv? K
  | .patternList P1 P2 => bindingTableJoin (patEvalR G site P1) (patEvalR G site P2)
  | .trail p => (patEvalR G site p).filter Record.isTrail

theorem patEvalR_ofPattern (G : PropertyGraph) (site : GraphSite) (P : Pattern) :
    patEvalR G site (ofPattern P) = evalPattern G site P := by
  induction P with
  | node na => rfl
  | edge n1 rel dir n2 => rfl
  | step P rel dir n2 ih =>
      simp only [ofPattern, patEvalR, ih, evalPattern_step_eq]
  | grouped P ih => simp only [ofPattern, patEvalR, ih, evalPattern]
  | quantified P K ih =>
      simp only [ofPattern, patEvalR, ih, evalPattern_quantified_eq]
  | patternList P1 P2 ih1 ih2 =>
      simp only [ofPattern, patEvalR, ih1, ih2, evalPattern]

theorem patEvalR_ofPatternT (G : PropertyGraph) (site : GraphSite) (P : Pattern) :
    patEvalR G site (ofPatternT P) = evalPatternTrail G site P := by
  induction P with
  | node na => rfl
  | edge n1 rel dir n2 => rfl
  | step P rel dir n2 _ =>
      show (patEvalR G site (ofPattern (.step P rel dir n2))).filter Record.isTrail
        = evalPatternTrail G site (.step P rel dir n2)
      rw [patEvalR_ofPattern]; rfl
  | grouped P _ =>
      show (patEvalR G site (ofPattern (.grouped P))).filter Record.isTrail
        = evalPatternTrail G site (.grouped P)
      rw [patEvalR_ofPattern]; rfl
  | quantified P K _ =>
      show (patEvalR G site (ofPattern (.quantified P K))).filter Record.isTrail
        = evalPatternTrail G site (.quantified P K)
      rw [patEvalR_ofPattern]; rfl
  | patternList P1 P2 ih1 ih2 =>
      show bindingTableJoin (patEvalR G site (ofPatternT P1))
          (patEvalR G site (ofPatternT P2))
        = evalPatternTrail G site (.patternList P1 P2)
      rw [ih1, ih2]; rfl

theorem patStep_preserves_patEvalR {G site} {p q : RPat}
    (h : PatStep G site p q) : patEvalR G site p = patEvalR G site q := by
  induction h with
  | nodeVal na => rfl
  | edgeVal n1 rel dir n2 => rfl
  | stepCong tv? rel dir n2 _ ih => simp only [patEvalR, ih]
  | groupedCong _ ih => simp only [patEvalR, ih]
  | quantCong vars lv? tv? K _ ih => simp only [patEvalR, ih]
  | listCong1 P2 _ ih => simp only [patEvalR, ih]
  | listCong2 B1 _ ih => simp only [patEvalR, ih]
  | stepVal B tv? rel dir n2 => rfl
  | groupedVal B => rfl
  | quantVal B vars lv? tv? K => rfl
  | listVal B1 B2 => rfl
  | trailCong _ ih => simp only [patEvalR, ih]
  | trailVal B => rfl

theorem patStepStar_preserves_patEvalR {G site} {p q : RPat}
    (h : PatStepStar G site p q) : patEvalR G site p = patEvalR G site q := by
  induction h with
  | refl _ => rfl
  | step hs _ ih => exact (patStep_preserves_patEvalR hs).trans ih

/-! Congruence closure lemmas for completeness -/

private theorem patStar_stepCong {G site} {P P' : RPat} (tv? rel dir n2)
    (h : PatStepStar G site P P') :
    PatStepStar G site (.step P tv? rel dir n2) (.step P' tv? rel dir n2) := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.stepCong tv? rel dir n2 hs) ih

private theorem patStar_groupedCong {G site} {P P' : RPat}
    (h : PatStepStar G site P P') :
    PatStepStar G site (.grouped P) (.grouped P') := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.groupedCong hs) ih

private theorem patStar_quantCong {G site} {P P' : RPat} (vars lv? tv? K)
    (h : PatStepStar G site P P') :
    PatStepStar G site (.quantified P vars lv? tv? K) (.quantified P' vars lv? tv? K) := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.quantCong vars lv? tv? K hs) ih

private theorem patStar_listCong1 {G site} {P1 P1' : RPat} (P2)
    (h : PatStepStar G site P1 P1') :
    PatStepStar G site (.patternList P1 P2) (.patternList P1' P2) := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.listCong1 P2 hs) ih

private theorem patStar_listCong2 {G site} {P2 P2' : RPat} (B1)
    (h : PatStepStar G site P2 P2') :
    PatStepStar G site (.patternList (.table B1) P2) (.patternList (.table B1) P2') := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.listCong2 B1 hs) ih

/-- Completeness: the reduction sequence reaches the big-step table. -/
private theorem patStar_trailCong {G site} {P P' : RPat}
    (h : PatStepStar G site P P') :
    PatStepStar G site (.trail P) (.trail P') := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.trailCong hs) ih

theorem patStep_complete (G : PropertyGraph) (site : GraphSite) (P : Pattern) :
    PatStepStar G site (ofPattern P) (.table (evalPattern G site P)) := by
  induction P with
  | node na => exact .one (.nodeVal na)
  | edge n1 rel dir n2 => exact .one (.edgeVal n1 rel dir n2)
  | step P rel dir n2 ih =>
      refine .trans (patStar_stepCong (patternTailVar P) rel dir n2 ih) ?_
      rw [evalPattern_step_eq]
      exact .one (.stepVal _ _ _ _ _)
  | grouped P ih =>
      refine .trans (patStar_groupedCong ih) ?_
      exact .one (.groupedVal _)
  | quantified P K ih =>
      refine .trans
        (patStar_quantCong (patternVars P) (patternLeadVar P) (patternTailVar P) K ih) ?_
      rw [evalPattern_quantified_eq]
      exact .one (.quantVal _ _ _ _ _)
  | patternList P1 P2 ih1 ih2 =>
      refine .trans (patStar_listCong1 (ofPattern P2) ih1) ?_
      refine .trans (patStar_listCong2 (evalPattern G site P1) ih2) ?_
      show PatStepStar G site _ (.table (bindingTableJoin _ _))
      exact .one (.listVal _ _)

/-- Completeness for trail mode: the trail runtime pattern reaches the
    trail evaluator's table. -/
theorem patStepT_complete (G : PropertyGraph) (site : GraphSite) (P : Pattern) :
    PatStepStar G site (ofPatternT P) (.table (evalPatternTrail G site P)) := by
  induction P with
  | node na =>
      refine .trans (patStar_trailCong (patStep_complete G site (.node na))) ?_
      exact .one (.trailVal _)
  | edge n1 rel dir n2 =>
      refine .trans (patStar_trailCong (patStep_complete G site (.edge n1 rel dir n2))) ?_
      exact .one (.trailVal _)
  | step P rel dir n2 _ =>
      refine .trans (patStar_trailCong (patStep_complete G site (.step P rel dir n2))) ?_
      exact .one (.trailVal _)
  | grouped P _ =>
      refine .trans (patStar_trailCong (patStep_complete G site (.grouped P))) ?_
      exact .one (.trailVal _)
  | quantified P K _ =>
      refine .trans (patStar_trailCong (patStep_complete G site (.quantified P K))) ?_
      exact .one (.trailVal _)
  | patternList P1 P2 ih1 ih2 =>
      refine .trans (patStar_listCong1 (ofPatternT P2) ih1) ?_
      refine .trans (patStar_listCong2 (evalPatternTrail G site P1) ih2) ?_
      show PatStepStar G site _ (.table (bindingTableJoin _ _))
      exact .one (.listVal _ _)

/-- Equivalence of the two pattern engines. A reduction sequence from a
    source pattern reaches table `B` iff the big-step evaluator computes `B`. -/
theorem patStep_correct (G : PropertyGraph) (site : GraphSite)
    (P : Pattern) (B : BindingTable) :
    PatStepStar G site (ofPattern P) (.table B) <-> evalPattern G site P = B := by
  constructor
  · intro h
    have hpres := patStepStar_preserves_patEvalR h
    rw [patEvalR_ofPattern] at hpres
    exact hpres
  · intro h
    subst h
    exact patStep_complete G site P

/-- Small-step Pattern Soundness (Paper Theorem 6.2, star form).
    This is the paper's literal statement: a well-typed pattern expression
    whose reduction sequence terminates in a table yields a table conforming
    to the declared schema. Discharged through the engine equivalence and the
    proven big-step pattern soundness. -/
theorem patSmallStep_soundness
    (ctx : TypingCtx) (G : PropertyGraph)
    (hCat : ∀ Psi', ctx.schemaMap.lookup ctx.graphSite = some Psi' →
              graphConformsSchema G Psi' = true)
    (Psi : GraphSchemaFull) (hPsi : ctx.schemaMap.lookup ctx.graphSite = some Psi)
    (P : Pattern) (GammaOut : RecordSchema)
    (hType : PatExprTyping ctx P GammaOut)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G)
    {B : BindingTable}
    (hSteps : PatStepStar G ctx.graphSite (ofPattern P) (.table B)) :
    BTConforms B GammaOut := by
  have hB : evalPattern G ctx.graphSite P = B :=
    (patStep_correct G ctx.graphSite P B).mp hSteps
  rw [← hB]
  exact patExprSoundness' ctx G hCat Psi hPsi P GammaOut hType hGraph

/-- Small-step pattern soundness at open sites (Theorem 6.2, star form).
    No schema witness, no graph-conformance premise: an open site
    carries neither. Discharged through the engine equivalence and the
    open-graph big-step pattern soundness. -/
theorem patSmallStep_soundness_open
    (ctx : TypingCtx) (G : PropertyGraph)
    (hOpen : ctx.schemaMap.isClosed ctx.graphSite = false)
    (P : Pattern) (GammaOut : RecordSchema)
    (hType : PatExprTyping ctx P GammaOut)
    {B : BindingTable}
    (hSteps : PatStepStar G ctx.graphSite (ofPattern P) (.table B)) :
    BTConforms B GammaOut := by
  have hB : evalPattern G ctx.graphSite P = B :=
    (patStep_correct G ctx.graphSite P B).mp hSteps
  rw [← hB]
  exact patExprSoundness_open ctx G hOpen P GammaOut hType

/-- Definition 6.1-faithful small-step pattern soundness (closed sites):
    the star-form Theorem 6.2 with the strengthened conclusion. -/
theorem patSmallStep_soundness_inhabits
    (ctx : TypingCtx) (G : PropertyGraph)
    (hCat : ∀ Psi', ctx.schemaMap.lookup ctx.graphSite = some Psi' →
              graphConformsSchema G Psi' = true)
    (Psi : GraphSchemaFull) (hPsi : ctx.schemaMap.lookup ctx.graphSite = some Psi)
    (P : Pattern) (GammaOut : RecordSchema)
    (hType : PatExprTyping ctx P GammaOut)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G)
    {B : BindingTable}
    (hSteps : PatStepStar G ctx.graphSite (ofPattern P) (.table B)) :
    BTInhabits G B GammaOut := by
  have hB : evalPattern G ctx.graphSite P = B :=
    (patStep_correct G ctx.graphSite P B).mp hSteps
  rw [← hB]
  exact patExprSoundness_inhabits ctx G hCat Psi hPsi P GammaOut hType hGraph

/-- Definition 6.1-faithful small-step pattern soundness (open sites). -/
theorem patSmallStep_soundness_inhabits_open
    (ctx : TypingCtx) (G : PropertyGraph)
    (hOpen : ctx.schemaMap.isClosed ctx.graphSite = false)
    (P : Pattern) (GammaOut : RecordSchema)
    (hType : PatExprTyping ctx P GammaOut)
    {B : BindingTable}
    (hSteps : PatStepStar G ctx.graphSite (ofPattern P) (.table B)) :
    BTInhabits G B GammaOut := by
  have hB : evalPattern G ctx.graphSite P = B :=
    (patStep_correct G ctx.graphSite P B).mp hSteps
  rw [← hB]
  exact patExprSoundness_inhabits_open ctx G hOpen P GammaOut hType

-- ============================================================
--  Query layer (Paper Theorem 6.3 / Corollary 6.1)
--
--  Runtime queries mirror the paper's query configurations (Definition
--  "Well-Typed Query Configuration"): `matchQ` is the paper's 4-tuple
--  <G, P, phi, pi> (with the WHERE predicate optional), `project` is the
--  3-tuple <G, B, pi>, and `table` is the final bag. Because `use graph`
--  switches the working graph and site mid-reduction, configurations carry
--  the resolved graph and site, exactly as the paper's configurations do.
--
--  Steps mirror the paper's rules: `useResolve` is FSQueryUse, `matchStep`
--  is FSQueryMatch (the pattern layer's `PatStep` runs INSIDE the 4-tuple,
--  giving the fine-grained checkable steps), `matchDone` is FSQueryMatchDone
--  (the WHERE filter selects a sub-bag and the configuration transitions to
--  the 3-tuple), and `projectStep` is FSQueryProject. The composite rules
--  give Corollary 6.1's set-operator layer.
-- ============================================================

/-- The WHERE filter applied at the 4-tuple to 3-tuple transition
    (`none` for `matchReturn`, `some phi` for `matchWhere`). -/
def applyWhere (G : PropertyGraph) (site : GraphSite) (B : BindingTable) :
    Option Pred -> BindingTable
  | none => B
  | some phi => B.filter fun rho => evalPred G site rho phi == some true

/-- Runtime query configurations (paper Definition: query configurations). -/
inductive RQuery where
  | src       : PropertyGraph -> GraphSite -> Query -> RQuery
  | matchQ    : PropertyGraph -> GraphSite -> RPat -> Option Pred -> ProjectionList -> RQuery
  | project   : PropertyGraph -> GraphSite -> BindingTable -> ProjectionList -> RQuery
  | composite : SetOp -> RQuery -> RQuery -> RQuery
  | table     : BindingTable -> RQuery

/-- The query step relation (Paper: FSQuery rules). Parameterized only by
    the catalog; the working graph and site live in the configuration. -/
inductive QStep (C : Catalog) : RQuery -> RQuery -> Prop where
  -- FSQueryUse: resolve the graph switch.
  | useResolve {G site g inner G'} (h : resolveGraph C g = some G') :
      QStep C (.src G site (.useGraph g inner)) (.src G' g inner)
  | useFail {G site g inner} (h : resolveGraph C g = none) :
      QStep C (.src G site (.useGraph g inner)) (.table [])
  -- Enter the 4-tuple configuration.
  | matchInit {G site P pis} :
      QStep C (.src G site (.matchReturn P pis))
        (.matchQ G site (ofPatternT P) none pis)
  | matchWhereInit {G site P phi pis} :
      QStep C (.src G site (.matchWhere P phi pis))
        (.matchQ G site (ofPatternT P) (some phi) pis)
  | compositeInit {G site op Q1 Q2} :
      QStep C (.src G site (.composite op Q1 Q2))
        (.composite op (.src G site Q1) (.src G site Q2))
  -- FSQueryMatch: the pattern steps inside the 4-tuple.
  | matchStep {G site p p' phi? pis} (h : PatStep G site p p') :
      QStep C (.matchQ G site p phi? pis) (.matchQ G site p' phi? pis)
  -- FSQueryMatchDone: filter and transition to the 3-tuple.
  | matchDone {G site B phi? pis} :
      QStep C (.matchQ G site (.table B) phi? pis)
        (.project G site (applyWhere G site B phi?) pis)
  -- FSQueryProject: project the 3-tuple to the final bag.
  | projectStep {G site B pis} :
      QStep C (.project G site B pis)
        (.table (B.map fun rho => projectRecord G site rho B pis))
  -- Corollary 6.1: set-operator congruence and combination.
  | compCong1 {q1 q1'} (op q2) (h : QStep C q1 q1') :
      QStep C (.composite op q1 q2) (.composite op q1' q2)
  | compCong2 {q2 q2'} (op B1) (h : QStep C q2 q2') :
      QStep C (.composite op (.table B1) q2) (.composite op (.table B1) q2')
  | compVal (op B1 B2) :
      QStep C (.composite op (.table B1) (.table B2))
        (.table (applySetOp op B1 B2))

/-- Reflexive-transitive closure of `QStep`. -/
inductive QStepStar (C : Catalog) : RQuery -> RQuery -> Prop where
  | refl (q) : QStepStar C q q
  | step {p q r} : QStep C p q -> QStepStar C q r -> QStepStar C p r

theorem QStepStar.one {C} {p q : RQuery} (h : QStep C p q) : QStepStar C p q :=
  .step h (.refl q)

theorem QStepStar.trans {C} {p q r : RQuery}
    (h1 : QStepStar C p q) (h2 : QStepStar C q r) : QStepStar C p r := by
  induction h1 with
  | refl _ => exact h2
  | step hs _ ih => exact .step hs (ih h2)

/-! ### Progress: every non-table configuration can step -/

theorem qStep_progress (C : Catalog) (q : RQuery) :
    (∃ B, q = .table B) ∨ (∃ q', QStep C q q') := by
  induction q with
  | src G site q0 =>
      cases q0 with
      | useGraph g inner =>
          cases hres : resolveGraph C g with
          | some G' => exact Or.inr ⟨_, .useResolve hres⟩
          | none => exact Or.inr ⟨_, .useFail hres⟩
      | matchReturn P pis => exact Or.inr ⟨_, .matchInit⟩
      | matchWhere P phi pis => exact Or.inr ⟨_, .matchWhereInit⟩
      | composite op Q1 Q2 => exact Or.inr ⟨_, .compositeInit⟩
  | matchQ G site p phi? pis =>
      rcases patStep_progress G site p with ⟨B, rfl⟩ | ⟨p', hp⟩
      · exact Or.inr ⟨_, .matchDone⟩
      · exact Or.inr ⟨_, .matchStep hp⟩
  | project G site B pis => exact Or.inr ⟨_, .projectStep⟩
  | composite op q1 q2 ih1 ih2 =>
      rcases ih1 with ⟨B1, rfl⟩ | ⟨q1', h1⟩
      · rcases ih2 with ⟨B2, rfl⟩ | ⟨q2', h2⟩
        · exact Or.inr ⟨_, .compVal op B1 B2⟩
        · exact Or.inr ⟨_, .compCong2 op B1 h2⟩
      · exact Or.inr ⟨_, .compCong1 op q2 h1⟩
  | table B => exact Or.inl ⟨B, rfl⟩

/-! ### Equivalence with the big-step evaluator -/

/-- Big-step meaning of a query configuration (used only in the proofs). -/
def qEvalR (C : Catalog) : RQuery -> BindingTable
  | .src G site q => evalQuery C G site q
  | .matchQ G site p phi? pis =>
      let B := applyWhere G site (patEvalR G site p) phi?
      B.map fun rho => projectRecord G site rho B pis
  | .project G site B pis => B.map fun rho => projectRecord G site rho B pis
  | .composite op q1 q2 => applySetOp op (qEvalR C q1) (qEvalR C q2)
  | .table B => B

theorem evalQuery_matchReturn_eq (C : Catalog) (G : PropertyGraph)
    (site : GraphSite) (P : Pattern) (pis : ProjectionList) :
    evalQuery C G site (.matchReturn P pis)
      = (applyWhere G site (evalPatternTrail G site P) none).map
          (fun rho =>
            projectRecord G site rho
              (applyWhere G site (evalPatternTrail G site P) none) pis) := rfl

theorem evalQuery_matchWhere_eq (C : Catalog) (G : PropertyGraph)
    (site : GraphSite) (P : Pattern) (phi : Pred) (pis : ProjectionList) :
    evalQuery C G site (.matchWhere P phi pis)
      = (applyWhere G site (evalPatternTrail G site P) (some phi)).map
          (fun rho =>
            projectRecord G site rho
              (applyWhere G site (evalPatternTrail G site P) (some phi)) pis) := rfl

theorem evalQuery_composite_eq (C : Catalog) (G : PropertyGraph)
    (site : GraphSite) (op : SetOp) (Q1 Q2 : Query) :
    evalQuery C G site (.composite op Q1 Q2)
      = applySetOp op (evalQuery C G site Q1) (evalQuery C G site Q2) := rfl

theorem qStep_preserves_qEvalR {C : Catalog} {p q : RQuery}
    (h : QStep C p q) : qEvalR C p = qEvalR C q := by
  induction h with
  | useResolve hres => rename_i G site g inner G'; simp only [qEvalR, evalQuery, hres]
  | useFail hres => rename_i G site g inner; simp only [qEvalR, evalQuery, hres]
  | matchInit =>
      rename_i G site P pis
      simp only [qEvalR, patEvalR_ofPatternT, evalQuery_matchReturn_eq]
  | matchWhereInit =>
      rename_i G site P phi pis
      simp only [qEvalR, patEvalR_ofPatternT, evalQuery_matchWhere_eq]
  | compositeInit => rfl
  | matchStep hp => simp only [qEvalR, patStep_preserves_patEvalR hp]
  | matchDone => rfl
  | projectStep => rfl
  | compCong1 op q2 _ ih => simp only [qEvalR, ih]
  | compCong2 op B1 _ ih => simp only [qEvalR, ih]
  | compVal op B1 B2 => rfl

theorem qStepStar_preserves_qEvalR {C : Catalog} {p q : RQuery}
    (h : QStepStar C p q) : qEvalR C p = qEvalR C q := by
  induction h with
  | refl _ => rfl
  | step hs _ ih => exact (qStep_preserves_qEvalR hs).trans ih

/-! Congruence closure lemmas for completeness -/

private theorem qStar_matchCong {C : Catalog} {G site} {p p' : RPat}
    (phi? : Option Pred) (pis : ProjectionList)
    (h : PatStepStar G site p p') :
    QStepStar C (.matchQ G site p phi? pis) (.matchQ G site p' phi? pis) := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.matchStep hs) ih

private theorem qStar_compCong1 {C : Catalog} {q1 q1' : RQuery} (op) (q2)
    (h : QStepStar C q1 q1') :
    QStepStar C (.composite op q1 q2) (.composite op q1' q2) := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.compCong1 op q2 hs) ih

private theorem qStar_compCong2 {C : Catalog} {q2 q2' : RQuery} (op) (B1)
    (h : QStepStar C q2 q2') :
    QStepStar C (.composite op (.table B1) q2) (.composite op (.table B1) q2') := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.compCong2 op B1 hs) ih

/-- Completeness: the reduction sequence reaches the big-step table. -/
theorem qStep_complete (C : Catalog) (q : Query) :
    ∀ (G : PropertyGraph) (site : GraphSite),
      QStepStar C (.src G site q) (.table (evalQuery C G site q)) := by
  induction q with
  | useGraph g inner ih =>
      intro G site
      cases hres : resolveGraph C g with
      | some G' =>
          have hEq : evalQuery C G site (.useGraph g inner) = evalQuery C G' g inner := by
            simp only [evalQuery, hres]
          rw [hEq]
          exact .step (.useResolve hres) (ih G' g)
      | none =>
          have hEq : evalQuery C G site (.useGraph g inner) = [] := by
            simp only [evalQuery, hres]
          rw [hEq]
          exact .one (.useFail hres)
  | matchReturn P pis =>
      intro G site
      rw [evalQuery_matchReturn_eq]
      refine .step .matchInit ?_
      refine .trans (qStar_matchCong none pis (patStepT_complete G site P)) ?_
      exact .step .matchDone (.one .projectStep)
  | matchWhere P phi pis =>
      intro G site
      rw [evalQuery_matchWhere_eq]
      refine .step .matchWhereInit ?_
      refine .trans (qStar_matchCong (some phi) pis (patStepT_complete G site P)) ?_
      exact .step .matchDone (.one .projectStep)
  | composite op Q1 Q2 ih1 ih2 =>
      intro G site
      rw [evalQuery_composite_eq]
      refine .step .compositeInit ?_
      refine .trans (qStar_compCong1 op _ (ih1 G site)) ?_
      refine .trans (qStar_compCong2 op _ (ih2 G site)) ?_
      exact .one (.compVal op _ _)

/-- Equivalence of the two query engines. A reduction sequence from a
    source query configuration reaches table `B` iff the big-step evaluator
    computes `B`. This is the theorem that makes the engine flag sound. -/
theorem qStep_correct (C : Catalog) (G : PropertyGraph) (site : GraphSite)
    (q : Query) (B : BindingTable) :
    QStepStar C (.src G site q) (.table B) <-> evalQuery C G site q = B := by
  constructor
  · intro h
    exact qStepStar_preserves_qEvalR h
  · intro h
    subst h
    exact qStep_complete C q G site

/-- Small-step query type soundness (Paper Theorem 6.3, star form).
    The paper's literal statement over the configuration step relation: a
    well-typed query whose reduction sequence terminates in a bag yields a
    bag conforming to the declared schema. Catalog-wide premises; no
    `use graph` leaf obligation. -/
theorem querySmallStep_soundness_catalogWide
    (hCat : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' →
        ∀ Psi, ctx'.schemaMap.lookup ctx'.graphSite = some Psi →
          graphConformsSchema G' Psi = true)
    (hWF : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' → GraphValuesWF G')
    (hSchemaCat : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' →
        ∃ Psi, ctx'.schemaMap.lookup ctx'.graphSite = some Psi)
    (ctx : TypingCtx) (G : PropertyGraph) (Q : Query) (Gamma : RecordSchema)
    (hType : QueryTyping ctx Q Gamma)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G)
    {B : BindingTable}
    (hSteps : QStepStar ctx.catalog (.src G ctx.graphSite Q) (.table B)) :
    BTConforms B Gamma := by
  have hB : evalQuery ctx.catalog G ctx.graphSite Q = B :=
    (qStep_correct ctx.catalog G ctx.graphSite Q B).mp hSteps
  rw [← hB]
  exact queryTypeSoundness_composed_catalogWide hCat hWF hSchemaCat
    ctx G Q Gamma hType hGraph

/-- Small-step Composite Query Soundness (Paper Corollary 6.1, star form).
    The set-operator layer: a well-typed composite query whose reduction
    sequence terminates in a bag conforms to the combined schema. -/
theorem compositeSmallStep_soundness_catalogWide
    (hCat : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' →
        ∀ Psi, ctx'.schemaMap.lookup ctx'.graphSite = some Psi →
          graphConformsSchema G' Psi = true)
    (hWF : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' → GraphValuesWF G')
    (hSchemaCat : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' →
        ∃ Psi, ctx'.schemaMap.lookup ctx'.graphSite = some Psi)
    (ctx : TypingCtx) (G : PropertyGraph)
    (op : SetOp) (Q1 Q2 : Query) (Gamma1 Gamma2 : RecordSchema)
    (hType1 : QueryTyping ctx Q1 Gamma1)
    (hType2 : QueryTyping ctx Q2 Gamma2)
    (hCompat : opCompatible op Gamma1 Gamma2 = true)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G)
    {B : BindingTable}
    (hSteps : QStepStar ctx.catalog
      (.src G ctx.graphSite (.composite op Q1 Q2)) (.table B)) :
    BTConforms B (opCombine op Gamma1 Gamma2) := by
  have hB : evalQuery ctx.catalog G ctx.graphSite (.composite op Q1 Q2) = B :=
    (qStep_correct ctx.catalog G ctx.graphSite _ B).mp hSteps
  rw [← hB, evalQuery_composite_eq]
  exact compositeQuerySoundness_catalogWide hCat hWF hSchemaCat
    ctx G op Q1 Q2 Gamma1 Gamma2 hType1 hType2 hCompat hGraph

/-- Small-step query type soundness across mixed open and closed sites
    (Theorem 6.3, star form). No site is required to carry a
    schema: closed sites go through the refinement machinery, open sites
    through the open-graph soundness theorems. -/
theorem querySmallStep_soundness_mixedSites
    (hCat : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' →
        ∀ Psi, ctx'.schemaMap.lookup ctx'.graphSite = some Psi →
          graphConformsSchema G' Psi = true)
    (hWF : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' → GraphValuesWF G')
    (ctx : TypingCtx) (G : PropertyGraph) (Q : Query) (Gamma : RecordSchema)
    (hType : QueryTyping ctx Q Gamma)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G)
    {B : BindingTable}
    (hSteps : QStepStar ctx.catalog (.src G ctx.graphSite Q) (.table B)) :
    BTConforms B Gamma := by
  have hB : evalQuery ctx.catalog G ctx.graphSite Q = B :=
    (qStep_correct ctx.catalog G ctx.graphSite Q B).mp hSteps
  rw [← hB]
  exact queryTypeSoundness_composed_mixedSites hCat hWF ctx G Q Gamma hType hGraph

/-- Definition 6.1-faithful small-step query type soundness (closed
    sites, full query language): the star-form Theorem 6.3 with the
    strengthened conclusion. -/
theorem querySmallStep_inhabits
    (ctx : TypingCtx) (G : PropertyGraph)
    (hCat : ∀ Psi', ctx.schemaMap.lookup ctx.graphSite = some Psi' →
              graphConformsSchema G Psi' = true)
    (Psi : GraphSchemaFull) (hPsi : ctx.schemaMap.lookup ctx.graphSite = some Psi)
    (hWF : GraphValuesWF G)
    (hUse : ∀ (g : Name) (inner : Query) (Gu : RecordSchema),
        (ctx.catalog.lookup g).isSome = true →
        QueryTyping { ctx with graphSite := g } inner Gu →
        BTInhabitsS G (evalQuery ctx.catalog G ctx.graphSite (.useGraph g inner)) Gu)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G)
    {Q : Query} {Gamma : RecordSchema}
    (hType : QueryTyping ctx Q Gamma)
    {B : BindingTable}
    (hSteps : QStepStar ctx.catalog (.src G ctx.graphSite Q) (.table B)) :
    BTInhabits G B Gamma := by
  have hB : evalQuery ctx.catalog G ctx.graphSite Q = B :=
    (qStep_correct ctx.catalog G ctx.graphSite Q B).mp hSteps
  rw [← hB]
  exact queryTyping_inhabits ctx G hCat Psi hPsi hWF hUse hGraph hType

/-- Strong-relation form of `querySmallStep_inhabits`. -/
theorem querySmallStep_inhabitsS
    (ctx : TypingCtx) (G : PropertyGraph)
    (hCat : ∀ Psi', ctx.schemaMap.lookup ctx.graphSite = some Psi' →
              graphConformsSchema G Psi' = true)
    (Psi : GraphSchemaFull) (hPsi : ctx.schemaMap.lookup ctx.graphSite = some Psi)
    (hWF : GraphValuesWF G)
    (hUse : ∀ (g : Name) (inner : Query) (Gu : RecordSchema),
        (ctx.catalog.lookup g).isSome = true →
        QueryTyping { ctx with graphSite := g } inner Gu →
        BTInhabitsS G (evalQuery ctx.catalog G ctx.graphSite (.useGraph g inner)) Gu)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G)
    {Q : Query} {Gamma : RecordSchema}
    (hType : QueryTyping ctx Q Gamma)
    {B : BindingTable}
    (hSteps : QStepStar ctx.catalog (.src G ctx.graphSite Q) (.table B)) :
    BTInhabitsS G B Gamma := by
  have hB : evalQuery ctx.catalog G ctx.graphSite Q = B :=
    (qStep_correct ctx.catalog G ctx.graphSite Q B).mp hSteps
  rw [← hB]
  exact queryTyping_inhabitsS ctx G hCat Psi hPsi hWF hUse hGraph hType

/-- Small-step Composite Query Soundness across mixed sites
    (Corollary 6.1, star form). -/
theorem compositeSmallStep_soundness_mixedSites
    (hCat : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' →
        ∀ Psi, ctx'.schemaMap.lookup ctx'.graphSite = some Psi →
          graphConformsSchema G' Psi = true)
    (hWF : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' → GraphValuesWF G')
    (ctx : TypingCtx) (G : PropertyGraph)
    (op : SetOp) (Q1 Q2 : Query) (Gamma1 Gamma2 : RecordSchema)
    (hType1 : QueryTyping ctx Q1 Gamma1)
    (hType2 : QueryTyping ctx Q2 Gamma2)
    (hCompat : opCompatible op Gamma1 Gamma2 = true)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G)
    {B : BindingTable}
    (hSteps : QStepStar ctx.catalog
      (.src G ctx.graphSite (.composite op Q1 Q2)) (.table B)) :
    BTConforms B (opCombine op Gamma1 Gamma2) := by
  have hB : evalQuery ctx.catalog G ctx.graphSite (.composite op Q1 Q2) = B :=
    (qStep_correct ctx.catalog G ctx.graphSite _ B).mp hSteps
  rw [← hB, evalQuery_composite_eq]
  exact compositeQuerySoundness_mixedSites hCat hWF
    ctx G op Q1 Q2 Gamma1 Gamma2 hType1 hType2 hCompat hGraph

-- ============================================================
--  Executable small-step interpreter and the engine flag
--
--  `patStepInterp` / `qStepInterp` are executable single-step functions
--  implementing a deterministic (leftmost-innermost) strategy of the step
--  relations. Three facts connect them to the metatheory: each emitted step
--  is a `PatStep`/`QStep` (soundness), they return `none` exactly on
--  terminal tables (executable progress), and each step strictly decreases
--  a size measure (so the fuel-based driver provably terminates with the
--  right answer). `runQuery` exposes the user-facing engine flag; the
--  agreement theorem shows the flag cannot change any query's result.
-- ============================================================

def RPat.asTable? : RPat -> Option BindingTable
  | .table B => some B
  | _ => none

private theorem RPat.asTable?_some {p : RPat} {B : BindingTable}
    (h : p.asTable? = some B) : p = .table B := by
  cases p with
  | table B' =>
      simp only [RPat.asTable?, Option.some.injEq] at h
      rw [h]
  | node na => simp [RPat.asTable?] at h
  | edge n1 rel dir n2 => simp [RPat.asTable?] at h
  | step P tv? rel dir n2 => simp [RPat.asTable?] at h
  | grouped P => simp [RPat.asTable?] at h
  | trail P => simp [RPat.asTable?] at h
  | quantified P vars lv? tv? K => simp [RPat.asTable?] at h
  | patternList P1 P2 => simp [RPat.asTable?] at h

def RQuery.asTable? : RQuery -> Option BindingTable
  | .table B => some B
  | _ => none

private theorem RQuery.asTable?_some {q : RQuery} {B : BindingTable}
    (h : q.asTable? = some B) : q = .table B := by
  cases q with
  | table B' =>
      simp only [RQuery.asTable?, Option.some.injEq] at h
      rw [h]
  | src G site q0 => simp [RQuery.asTable?] at h
  | matchQ G site p phi? pis => simp [RQuery.asTable?] at h
  | project G site B0 pis => simp [RQuery.asTable?] at h
  | composite op q1 q2 => simp [RQuery.asTable?] at h

/-- Executable single pattern step (deterministic leftmost-innermost). -/
def patStepInterp (G : PropertyGraph) (site : GraphSite) : RPat -> Option RPat
  | .table _ => none
  | .node na => some (.table (matchNode G site na))
  | .edge n1 rel dir n2 => some (.table (evalPattern G site (.edge n1 rel dir n2)))
  | .step P tv? rel dir n2 =>
      match P.asTable? with
      | some B => some (.table (stepCombine G site B tv? rel dir n2))
      | none =>
        match patStepInterp G site P with
        | some P' => some (.step P' tv? rel dir n2)
        | none => none
  | .grouped P =>
      match P.asTable? with
      | some B => some (.table B)
      | none =>
        match patStepInterp G site P with
        | some P' => some (.grouped P')
        | none => none
  | .trail P =>
      match P.asTable? with
      | some B => some (.table (B.filter Record.isTrail))
      | none =>
        match patStepInterp G site P with
        | some P' => some (.trail P')
        | none => none
  | .quantified P vars lv? tv? K =>
      match P.asTable? with
      | some B => some (.table (quantCombine G B vars lv? tv? K))
      | none =>
        match patStepInterp G site P with
        | some P' => some (.quantified P' vars lv? tv? K)
        | none => none
  | .patternList P1 P2 =>
      match P1.asTable? with
      | some B1 =>
        match P2.asTable? with
        | some B2 => some (.table (bindingTableJoin B1 B2))
        | none =>
          match patStepInterp G site P2 with
          | some P2' => some (.patternList (.table B1) P2')
          | none => none
      | none =>
        match patStepInterp G site P1 with
        | some P1' => some (.patternList P1' P2)
        | none => none

/-- The interpreter is stuck exactly on tables (executable progress). -/
theorem patStepInterp_none_iff (G : PropertyGraph) (site : GraphSite) (p : RPat) :
    patStepInterp G site p = none <-> ∃ B, p = .table B := by
  induction p with
  | table B => simp [patStepInterp]
  | node na => simp [patStepInterp]
  | edge n1 rel dir n2 => simp [patStepInterp]
  | step P tv? rel dir n2 ih =>
      simp only [patStepInterp]
      cases hT : P.asTable? with
      | some B => simp
      | none =>
        cases hI : patStepInterp G site P with
        | some P' => simp
        | none =>
          obtain ⟨B, rfl⟩ := ih.mp hI
          simp [RPat.asTable?] at hT
  | grouped P ih =>
      simp only [patStepInterp]
      cases hT : P.asTable? with
      | some B => simp
      | none =>
        cases hI : patStepInterp G site P with
        | some P' => simp
        | none =>
          obtain ⟨B, rfl⟩ := ih.mp hI
          simp [RPat.asTable?] at hT
  | quantified P vars lv? tv? K ih =>
      simp only [patStepInterp]
      cases hT : P.asTable? with
      | some B => simp
      | none =>
        cases hI : patStepInterp G site P with
        | some P' => simp
        | none =>
          obtain ⟨B, rfl⟩ := ih.mp hI
          simp [RPat.asTable?] at hT
  | trail P ih =>
      simp only [patStepInterp]
      cases hT : P.asTable? with
      | some B => simp
      | none =>
        cases hI : patStepInterp G site P with
        | some P' => simp
        | none =>
          obtain ⟨B, rfl⟩ := ih.mp hI
          simp [RPat.asTable?] at hT
  | patternList P1 P2 ih1 ih2 =>
      simp only [patStepInterp]
      cases hT1 : P1.asTable? with
      | some B1 =>
        cases hT2 : P2.asTable? with
        | some B2 => simp
        | none =>
          cases hI2 : patStepInterp G site P2 with
          | some P2' => simp
          | none =>
            obtain ⟨B, rfl⟩ := ih2.mp hI2
            simp [RPat.asTable?] at hT2
      | none =>
        cases hI1 : patStepInterp G site P1 with
        | some P1' => simp
        | none =>
          obtain ⟨B, rfl⟩ := ih1.mp hI1
          simp [RPat.asTable?] at hT1

/-- Every emitted step is a `PatStep`. -/
theorem patStepInterp_sound {G : PropertyGraph} {site : GraphSite}
    {p p' : RPat} (h : patStepInterp G site p = some p') :
    PatStep G site p p' := by
  induction p generalizing p' with
  | table B => simp [patStepInterp] at h
  | node na =>
      simp only [patStepInterp, Option.some.injEq] at h
      rw [← h]; exact .nodeVal na
  | edge n1 rel dir n2 =>
      simp only [patStepInterp, Option.some.injEq] at h
      rw [← h]; exact .edgeVal n1 rel dir n2
  | step P tv? rel dir n2 ih =>
      simp only [patStepInterp] at h
      cases hT : P.asTable? with
      | some B =>
        rw [hT] at h
        simp only [Option.some.injEq] at h
        rw [RPat.asTable?_some hT, ← h]
        exact .stepVal B tv? rel dir n2
      | none =>
        rw [hT] at h
        cases hI : patStepInterp G site P with
        | some P0 =>
          rw [hI] at h
          simp only [Option.some.injEq] at h
          rw [← h]
          exact .stepCong tv? rel dir n2 (ih hI)
        | none => rw [hI] at h; simp at h
  | grouped P ih =>
      simp only [patStepInterp] at h
      cases hT : P.asTable? with
      | some B =>
        rw [hT] at h
        simp only [Option.some.injEq] at h
        rw [RPat.asTable?_some hT, ← h]
        exact .groupedVal B
      | none =>
        rw [hT] at h
        cases hI : patStepInterp G site P with
        | some P0 =>
          rw [hI] at h
          simp only [Option.some.injEq] at h
          rw [← h]
          exact .groupedCong (ih hI)
        | none => rw [hI] at h; simp at h
  | quantified P vars lv? tv? K ih =>
      simp only [patStepInterp] at h
      cases hT : P.asTable? with
      | some B =>
        rw [hT] at h
        simp only [Option.some.injEq] at h
        rw [RPat.asTable?_some hT, ← h]
        exact .quantVal B vars lv? tv? K
      | none =>
        rw [hT] at h
        cases hI : patStepInterp G site P with
        | some P0 =>
          rw [hI] at h
          simp only [Option.some.injEq] at h
          rw [← h]
          exact .quantCong vars lv? tv? K (ih hI)
        | none => rw [hI] at h; simp at h
  | trail P ih =>
      simp only [patStepInterp] at h
      cases hT : P.asTable? with
      | some B =>
        rw [hT] at h
        simp only [Option.some.injEq] at h
        rw [RPat.asTable?_some hT, ← h]
        exact .trailVal B
      | none =>
        rw [hT] at h
        cases hI : patStepInterp G site P with
        | some P0 =>
          rw [hI] at h
          simp only [Option.some.injEq] at h
          rw [← h]
          exact .trailCong (ih hI)
        | none => rw [hI] at h; simp at h
  | patternList P1 P2 ih1 ih2 =>
      simp only [patStepInterp] at h
      cases hT1 : P1.asTable? with
      | some B1 =>
        rw [hT1] at h
        cases hT2 : P2.asTable? with
        | some B2 =>
          rw [hT2] at h
          simp only [Option.some.injEq] at h
          rw [RPat.asTable?_some hT1, RPat.asTable?_some hT2, ← h]
          exact .listVal B1 B2
        | none =>
          rw [hT2] at h
          cases hI2 : patStepInterp G site P2 with
          | some P2' =>
            rw [hI2] at h
            simp only [Option.some.injEq] at h
            rw [RPat.asTable?_some hT1, ← h]
            exact .listCong2 B1 (ih2 hI2)
          | none => rw [hI2] at h; simp at h
      | none =>
        rw [hT1] at h
        cases hI1 : patStepInterp G site P1 with
        | some P1' =>
          rw [hI1] at h
          simp only [Option.some.injEq] at h
          rw [← h]
          exact .listCong1 P2 (ih1 hI1)
        | none => rw [hI1] at h; simp at h

/-- Executable single query step (deterministic leftmost-innermost). -/
def qStepInterp (C : Catalog) : RQuery -> Option RQuery
  | .table _ => none
  | .src G site q =>
      match q with
      | .useGraph g inner =>
          match resolveGraph C g with
          | some G' => some (.src G' g inner)
          | none => some (.table [])
      | .matchReturn P pis => some (.matchQ G site (ofPatternT P) none pis)
      | .matchWhere P phi pis => some (.matchQ G site (ofPatternT P) (some phi) pis)
      | .composite op Q1 Q2 => some (.composite op (.src G site Q1) (.src G site Q2))
  | .matchQ G site p phi? pis =>
      match p.asTable? with
      | some B => some (.project G site (applyWhere G site B phi?) pis)
      | none =>
        match patStepInterp G site p with
        | some p' => some (.matchQ G site p' phi? pis)
        | none => none
  | .project G site B pis =>
      some (.table (B.map fun rho => projectRecord G site rho B pis))
  | .composite op q1 q2 =>
      match q1.asTable? with
      | some B1 =>
        match q2.asTable? with
        | some B2 => some (.table (applySetOp op B1 B2))
        | none =>
          match qStepInterp C q2 with
          | some q2' => some (.composite op (.table B1) q2')
          | none => none
      | none =>
        match qStepInterp C q1 with
        | some q1' => some (.composite op q1' q2)
        | none => none

/-- The query interpreter is stuck exactly on tables (executable progress). -/
theorem qStepInterp_none_iff (C : Catalog) (q : RQuery) :
    qStepInterp C q = none <-> ∃ B, q = .table B := by
  induction q with
  | table B => simp [qStepInterp]
  | src G site q0 =>
      cases q0 with
      | useGraph g inner =>
          simp only [qStepInterp]
          cases hres : resolveGraph C g <;> simp
      | matchReturn P pis => simp [qStepInterp]
      | matchWhere P phi pis => simp [qStepInterp]
      | composite op Q1 Q2 => simp [qStepInterp]
  | matchQ G site p phi? pis =>
      simp only [qStepInterp]
      cases hT : p.asTable? with
      | some B => simp
      | none =>
        cases hI : patStepInterp G site p with
        | some p' => simp
        | none =>
          obtain ⟨B, rfl⟩ := (patStepInterp_none_iff G site p).mp hI
          simp [RPat.asTable?] at hT
  | project G site B pis => simp [qStepInterp]
  | composite op q1 q2 ih1 ih2 =>
      simp only [qStepInterp]
      cases hT1 : q1.asTable? with
      | some B1 =>
        cases hT2 : q2.asTable? with
        | some B2 => simp
        | none =>
          cases hI2 : qStepInterp C q2 with
          | some q2' => simp
          | none =>
            obtain ⟨B, rfl⟩ := ih2.mp hI2
            simp [RQuery.asTable?] at hT2
      | none =>
        cases hI1 : qStepInterp C q1 with
        | some q1' => simp
        | none =>
          obtain ⟨B, rfl⟩ := ih1.mp hI1
          simp [RQuery.asTable?] at hT1

/-- Every emitted step is a `QStep`. -/
theorem qStepInterp_sound {C : Catalog} {q q' : RQuery}
    (h : qStepInterp C q = some q') : QStep C q q' := by
  induction q generalizing q' with
  | table B => simp [qStepInterp] at h
  | src G site q0 =>
      cases q0 with
      | useGraph g inner =>
          simp only [qStepInterp] at h
          cases hres : resolveGraph C g with
          | some G' =>
            rw [hres] at h
            simp only [Option.some.injEq] at h
            rw [← h]; exact .useResolve hres
          | none =>
            rw [hres] at h
            simp only [Option.some.injEq] at h
            rw [← h]; exact .useFail hres
      | matchReturn P pis =>
          simp only [qStepInterp, Option.some.injEq] at h
          rw [← h]; exact .matchInit
      | matchWhere P phi pis =>
          simp only [qStepInterp, Option.some.injEq] at h
          rw [← h]; exact .matchWhereInit
      | composite op Q1 Q2 =>
          simp only [qStepInterp, Option.some.injEq] at h
          rw [← h]; exact .compositeInit
  | matchQ G site p phi? pis =>
      simp only [qStepInterp] at h
      cases hT : p.asTable? with
      | some B =>
        rw [hT] at h
        simp only [Option.some.injEq] at h
        rw [RPat.asTable?_some hT, ← h]
        exact .matchDone
      | none =>
        rw [hT] at h
        cases hI : patStepInterp G site p with
        | some p0 =>
          rw [hI] at h
          simp only [Option.some.injEq] at h
          rw [← h]
          exact .matchStep (patStepInterp_sound hI)
        | none => rw [hI] at h; simp at h
  | project G site B pis =>
      simp only [qStepInterp, Option.some.injEq] at h
      rw [← h]; exact .projectStep
  | composite op q1 q2 ih1 ih2 =>
      simp only [qStepInterp] at h
      cases hT1 : q1.asTable? with
      | some B1 =>
        rw [hT1] at h
        cases hT2 : q2.asTable? with
        | some B2 =>
          rw [hT2] at h
          simp only [Option.some.injEq] at h
          rw [RQuery.asTable?_some hT1, RQuery.asTable?_some hT2, ← h]
          exact .compVal op B1 B2
        | none =>
          rw [hT2] at h
          cases hI2 : qStepInterp C q2 with
          | some q2' =>
            rw [hI2] at h
            simp only [Option.some.injEq] at h
            rw [RQuery.asTable?_some hT1, ← h]
            exact .compCong2 op B1 (ih2 hI2)
          | none => rw [hI2] at h; simp at h
      | none =>
        rw [hT1] at h
        cases hI1 : qStepInterp C q1 with
        | some q1' =>
          rw [hI1] at h
          simp only [Option.some.injEq] at h
          rw [← h]
          exact .compCong1 op q2 (ih1 hI1)
        | none => rw [hI1] at h; simp at h

/-! ### Termination measure: every interpreter step strictly shrinks -/

def RPat.size : RPat -> Nat
  | .table _ => 0
  | .node _ => 1
  | .edge _ _ _ _ => 1
  | .step P _ _ _ _ => P.size + 1
  | .grouped P => P.size + 1
  | .quantified P _ _ _ _ => P.size + 1
  | .patternList P1 P2 => P1.size + P2.size + 1
  | .trail P => P.size + 1

theorem patStepInterp_decreases {G : PropertyGraph} {site : GraphSite}
    {p p' : RPat} (h : patStepInterp G site p = some p') :
    p'.size < p.size := by
  induction p generalizing p' with
  | table B => simp [patStepInterp] at h
  | node na =>
      simp only [patStepInterp, Option.some.injEq] at h
      rw [← h]; simp [RPat.size]
  | edge n1 rel dir n2 =>
      simp only [patStepInterp, Option.some.injEq] at h
      rw [← h]; simp [RPat.size]
  | step P tv? rel dir n2 ih =>
      simp only [patStepInterp] at h
      cases hT : P.asTable? with
      | some B =>
        rw [hT] at h
        simp only [Option.some.injEq] at h
        rw [← h, RPat.asTable?_some hT]
        simp [RPat.size]
      | none =>
        rw [hT] at h
        cases hI : patStepInterp G site P with
        | some P0 =>
          rw [hI] at h
          simp only [Option.some.injEq] at h
          rw [← h]
          simp only [RPat.size]
          exact Nat.succ_lt_succ (ih hI)
        | none => rw [hI] at h; simp at h
  | grouped P ih =>
      simp only [patStepInterp] at h
      cases hT : P.asTable? with
      | some B =>
        rw [hT] at h
        simp only [Option.some.injEq] at h
        rw [← h, RPat.asTable?_some hT]
        simp [RPat.size]
      | none =>
        rw [hT] at h
        cases hI : patStepInterp G site P with
        | some P0 =>
          rw [hI] at h
          simp only [Option.some.injEq] at h
          rw [← h]
          simp only [RPat.size]
          exact Nat.succ_lt_succ (ih hI)
        | none => rw [hI] at h; simp at h
  | quantified P vars lv? tv? K ih =>
      simp only [patStepInterp] at h
      cases hT : P.asTable? with
      | some B =>
        rw [hT] at h
        simp only [Option.some.injEq] at h
        rw [← h, RPat.asTable?_some hT]
        simp [RPat.size]
      | none =>
        rw [hT] at h
        cases hI : patStepInterp G site P with
        | some P0 =>
          rw [hI] at h
          simp only [Option.some.injEq] at h
          rw [← h]
          simp only [RPat.size]
          exact Nat.succ_lt_succ (ih hI)
        | none => rw [hI] at h; simp at h
  | trail P ih =>
      simp only [patStepInterp] at h
      cases hT : P.asTable? with
      | some B =>
        rw [hT] at h
        simp only [Option.some.injEq] at h
        rw [← h, RPat.asTable?_some hT]
        simp [RPat.size]
      | none =>
        rw [hT] at h
        cases hI : patStepInterp G site P with
        | some P0 =>
          rw [hI] at h
          simp only [Option.some.injEq] at h
          rw [← h]
          simp only [RPat.size]
          exact Nat.succ_lt_succ (ih hI)
        | none => rw [hI] at h; simp at h
  | patternList P1 P2 ih1 ih2 =>
      simp only [patStepInterp] at h
      cases hT1 : P1.asTable? with
      | some B1 =>
        rw [hT1] at h
        cases hT2 : P2.asTable? with
        | some B2 =>
          rw [hT2] at h
          simp only [Option.some.injEq] at h
          rw [← h, RPat.asTable?_some hT1, RPat.asTable?_some hT2]
          simp [RPat.size]
        | none =>
          rw [hT2] at h
          cases hI2 : patStepInterp G site P2 with
          | some P2' =>
            rw [hI2] at h
            simp only [Option.some.injEq] at h
            rw [← h, RPat.asTable?_some hT1]
            simp only [RPat.size, Nat.zero_add]
            exact Nat.succ_lt_succ (ih2 hI2)
          | none => rw [hI2] at h; simp at h
      | none =>
        rw [hT1] at h
        cases hI1 : patStepInterp G site P1 with
        | some P1' =>
          rw [hI1] at h
          simp only [Option.some.injEq] at h
          rw [← h]
          simp only [RPat.size]
          exact Nat.add_lt_add_right (Nat.add_lt_add_right (ih1 hI1) _) 1
        | none => rw [hI1] at h; simp at h

/-- Size of a source query, measured through its runtime embedding. The
    constants account for the init, match-done, and project transitions. -/
def Query.rsize : Query -> Nat
  | .useGraph _ inner => inner.rsize + 1
  | .matchReturn P _ => (ofPatternT P).size + 3
  | .matchWhere P _ _ => (ofPatternT P).size + 3
  | .composite _ Q1 Q2 => Q1.rsize + Q2.rsize + 2

def RQuery.size : RQuery -> Nat
  | .src _ _ q => q.rsize
  | .matchQ _ _ p _ _ => p.size + 2
  | .project _ _ _ _ => 1
  | .composite _ q1 q2 => q1.size + q2.size + 1
  | .table _ => 0

theorem qStepInterp_decreases {C : Catalog} {q q' : RQuery}
    (h : qStepInterp C q = some q') : q'.size < q.size := by
  induction q generalizing q' with
  | table B => simp [qStepInterp] at h
  | src G site q0 =>
      cases q0 with
      | useGraph g inner =>
          simp only [qStepInterp] at h
          cases hres : resolveGraph C g with
          | some G' =>
            rw [hres] at h
            simp only [Option.some.injEq] at h
            rw [← h]
            simp [RQuery.size, Query.rsize]
          | none =>
            rw [hres] at h
            simp only [Option.some.injEq] at h
            rw [← h]
            simp [RQuery.size, Query.rsize]
      | matchReturn P pis =>
          simp only [qStepInterp, Option.some.injEq] at h
          rw [← h]
          simp [RQuery.size, Query.rsize]
      | matchWhere P phi pis =>
          simp only [qStepInterp, Option.some.injEq] at h
          rw [← h]
          simp [RQuery.size, Query.rsize]
      | composite op Q1 Q2 =>
          simp only [qStepInterp, Option.some.injEq] at h
          rw [← h]
          simp [RQuery.size, Query.rsize]
  | matchQ G site p phi? pis =>
      simp only [qStepInterp] at h
      cases hT : p.asTable? with
      | some B =>
        rw [hT] at h
        simp only [Option.some.injEq] at h
        rw [← h, RPat.asTable?_some hT]
        simp [RQuery.size, RPat.size]
      | none =>
        rw [hT] at h
        cases hI : patStepInterp G site p with
        | some p0 =>
          rw [hI] at h
          simp only [Option.some.injEq] at h
          rw [← h]
          simp only [RQuery.size]
          exact Nat.add_lt_add_right (patStepInterp_decreases hI) 2
        | none => rw [hI] at h; simp at h
  | project G site B pis =>
      simp only [qStepInterp, Option.some.injEq] at h
      rw [← h]
      simp [RQuery.size]
  | composite op q1 q2 ih1 ih2 =>
      simp only [qStepInterp] at h
      cases hT1 : q1.asTable? with
      | some B1 =>
        rw [hT1] at h
        cases hT2 : q2.asTable? with
        | some B2 =>
          rw [hT2] at h
          simp only [Option.some.injEq] at h
          rw [← h, RQuery.asTable?_some hT1, RQuery.asTable?_some hT2]
          simp [RQuery.size]
        | none =>
          rw [hT2] at h
          cases hI2 : qStepInterp C q2 with
          | some q2' =>
            rw [hI2] at h
            simp only [Option.some.injEq] at h
            rw [← h, RQuery.asTable?_some hT1]
            simp only [RQuery.size, Nat.zero_add]
            exact Nat.succ_lt_succ (ih2 hI2)
          | none => rw [hI2] at h; simp at h
      | none =>
        rw [hT1] at h
        cases hI1 : qStepInterp C q1 with
        | some q1' =>
          rw [hI1] at h
          simp only [Option.some.injEq] at h
          rw [← h]
          simp only [RQuery.size]
          exact Nat.add_lt_add_right (Nat.add_lt_add_right (ih1 hI1) _) 1
        | none => rw [hI1] at h; simp at h

/-! ### The fuel-based driver and the engine flag -/

/-- Run the executable small-step interpreter to a final table. Fuel-based;
    `RQuery.size` fuel provably suffices (`runSmallStep_complete`). -/
def runSmallStep (C : Catalog) : Nat -> RQuery -> Option BindingTable
  | _, .table B => some B
  | 0, _ => none
  | fuel + 1, q =>
    match qStepInterp C q with
    | some q' => runSmallStep C fuel q'
    | none => none

/-- Partial correctness: whatever fuel is supplied, a produced table is the
    big-step meaning of the starting configuration. -/
theorem runSmallStep_sound {C : Catalog} :
    ∀ {fuel : Nat} {q : RQuery} {B : BindingTable},
      runSmallStep C fuel q = some B -> qEvalR C q = B := by
  intro fuel
  induction fuel with
  | zero =>
      intro q B h
      cases hT : q.asTable? with
      | some B' =>
        rw [RQuery.asTable?_some hT] at h ⊢
        simp only [runSmallStep, Option.some.injEq] at h
        exact h
      | none =>
        cases q with
        | table B' => simp [RQuery.asTable?] at hT
        | src G site q0 => simp [runSmallStep] at h
        | matchQ G site p phi? pis => simp [runSmallStep] at h
        | project G site B0 pis => simp [runSmallStep] at h
        | composite op q1 q2 => simp [runSmallStep] at h
  | succ fuel ih =>
      intro q B h
      cases hT : q.asTable? with
      | some B' =>
        rw [RQuery.asTable?_some hT] at h ⊢
        simp only [runSmallStep, Option.some.injEq] at h
        exact h
      | none =>
        have hne : ∀ B0, q ≠ .table B0 := by
          intro B0 hq
          rw [hq] at hT
          simp [RQuery.asTable?] at hT
        have hrun : runSmallStep C (fuel + 1) q
            = match qStepInterp C q with
              | some q' => runSmallStep C fuel q'
              | none => none := by
          cases q with
          | table B0 => exact absurd rfl (hne B0)
          | src G site q0 => rfl
          | matchQ G site p phi? pis => rfl
          | project G site B0 pis => rfl
          | composite op q1 q2 => rfl
        rw [hrun] at h
        cases hI : qStepInterp C q with
        | some q' =>
          rw [hI] at h
          rw [qStep_preserves_qEvalR (qStepInterp_sound hI)]
          exact ih h
        | none => rw [hI] at h; simp at h

/-- Total correctness: with `RQuery.size` fuel the driver returns exactly
    the big-step meaning. -/
theorem runSmallStep_complete (C : Catalog) :
    ∀ (fuel : Nat) (q : RQuery), q.size ≤ fuel ->
      runSmallStep C fuel q = some (qEvalR C q) := by
  intro fuel
  induction fuel with
  | zero =>
      intro q hq
      cases hT : q.asTable? with
      | some B =>
        rw [RQuery.asTable?_some hT]
        rfl
      | none =>
        exfalso
        have hI : qStepInterp C q ≠ none := by
          intro hnone
          obtain ⟨B, rfl⟩ := (qStepInterp_none_iff C q).mp hnone
          simp [RQuery.asTable?] at hT
        cases hI2 : qStepInterp C q with
        | none => exact hI hI2
        | some q' =>
          have := qStepInterp_decreases hI2
          omega
  | succ fuel ih =>
      intro q hq
      cases hT : q.asTable? with
      | some B =>
        rw [RQuery.asTable?_some hT]
        rfl
      | none =>
        have hne : ∀ B0, q ≠ .table B0 := by
          intro B0 hq0
          rw [hq0] at hT
          simp [RQuery.asTable?] at hT
        have hrun : runSmallStep C (fuel + 1) q
            = match qStepInterp C q with
              | some q' => runSmallStep C fuel q'
              | none => none := by
          cases q with
          | table B0 => exact absurd rfl (hne B0)
          | src G site q0 => rfl
          | matchQ G site p phi? pis => rfl
          | project G site B0 pis => rfl
          | composite op q1 q2 => rfl
        rw [hrun]
        cases hI : qStepInterp C q with
        | some q' =>
          rw [qStep_preserves_qEvalR (qStepInterp_sound hI)]
          exact ih q' (by
            have := qStepInterp_decreases hI
            omega)
        | none =>
          exfalso
          obtain ⟨B, rfl⟩ := (qStepInterp_none_iff C q).mp hI
          simp [RQuery.asTable?] at hT

/-- The user-facing engine selector. -/
inductive Engine where
  | bigStep
  | smallStep
  deriving Repr, DecidableEq

/-- Run a query under the selected engine. The big-step engine is the
    evaluator; the small-step engine drives the executable step interpreter
    with provably sufficient fuel. -/
def runQuery (engine : Engine) (C : Catalog) (G : PropertyGraph)
    (site : GraphSite) (q : Query) : BindingTable :=
  match engine with
  | .bigStep => evalQuery C G site q
  | .smallStep =>
    (runSmallStep C (RQuery.size (.src G site q)) (.src G site q)).getD []

/-- The engine flag does not change any query's result: the small-step
    engine agrees with the big-step evaluator on every catalog, graph,
    site, and query. -/
theorem runQuery_engine_agnostic (C : Catalog) (G : PropertyGraph)
    (site : GraphSite) (q : Query) :
    runQuery .smallStep C G site q = runQuery .bigStep C G site q := by
  simp only [runQuery]
  rw [runSmallStep_complete C _ _ (Nat.le_refl _)]
  rfl

-- ============================================================
--  Paper-faithful composite query soundness, star form
-- ============================================================

/-- Corollary 6.1, paper-faithful single-operator form (star form).
    A composite query well typed in the operator-indexed judgment
    |-_circledast reduces only to binding tables conforming to its
    combined schema. -/
theorem compQuerySmallStep_soundness_catalogWide
    (hCat : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' →
        ∀ Psi, ctx'.schemaMap.lookup ctx'.graphSite = some Psi →
          graphConformsSchema G' Psi = true)
    (hWF : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' → GraphValuesWF G')
    (hSchemaCat : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' →
        ∃ Psi, ctx'.schemaMap.lookup ctx'.graphSite = some Psi)
    (ctx : TypingCtx) (G : PropertyGraph)
    (op : SetOp) (q : Query) (Gamma : RecordSchema)
    (hType : CompQueryTyping ctx op q Gamma)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G)
    {B : BindingTable}
    (hSteps : QStepStar ctx.catalog (.src G ctx.graphSite q) (.table B)) :
    BTConforms B Gamma :=
  querySmallStep_soundness_catalogWide hCat hWF hSchemaCat ctx G q Gamma
    hType.toQueryTyping hGraph hSteps

end MGQL
