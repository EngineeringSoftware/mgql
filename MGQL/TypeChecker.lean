/-
  MGQL: Mechanized GQL Semantics in Lean 4
  TypeChecker.lean -- Executable type checker

  inferQuery : TypingCtx -> Query -> Option RecordSchema computes a result
  schema for a query; inferQuery_sound shows every accepted query is well
  typed in the declarative system (QueryTyping), and composing with query
  type soundness gives inferQuery_conforms: an accepted query evaluates to
  a binding table conforming to the inferred schema.

  The checker is sound but not complete.  The declarative system has
  non-syntax-directed rules (subsumption, free choices of schema lists),
  and the checker commits to one canonical derivation, so rejection of a
  query does not mean it is untypable.
-/
import MGQL.Metatheory

namespace MGQL

/- ============================================================
    Boolean side-condition checkers (sound one-directional reflections)
    ============================================================ -/

/-- Does `t` dynamically refine to `Z?` (`GSort.intN`)?  Sound approximation:
    the int scalar at any null tag, unions containing the int branch, bottom. -/
def chkRefineIntN (t : GSort) : Bool :=
  match t.shape with
  | .single (.scalar .int) => true
  | .union ts => ts.any (fun es => decide (es = ExtSort.scalar .int))
  | .bot => true
  | _ => false

theorem chkRefineIntN_sound (t : GSort) (h : chkRefineIntN t = true) :
    DynRefine t GSort.intN := by
  obtain ⟨sh, n⟩ := t
  simp only [chkRefineIntN] at h
  split at h
  · -- sh = .single (.scalar .int)
    cases n with
    | val => exact .sub intSubtypeIntN
    | nullable => exact .sub (.refl _)
    | null => exact .sub (.nullSingleton _)
  · -- sh = .union ts
    rename_i ts
    rw [List.any_eq_true] at h
    obtain ⟨es, hmem, hdec⟩ := h
    obtain rfl : es = ExtSort.scalar .int := of_decide_eq_true hdec
    refine .unionBranch ts (.scalar .int) n GSort.intN hmem ?_
    cases n with
    | val => exact .sub intSubtypeIntN
    | nullable => exact .sub (.refl _)
    | null => exact .sub (.nullSingleton _)
  · -- sh = .bot
    cases n with
    | val => exact .sub (.bot GSort.intN)
    | nullable => exact .sub (.nullCov (.bot GSort.int))
    | null =>
      exact .sub (.trans (.nullSingCov (.bot GSort.int)) (.nullSingleton _))
  all_goals exact Bool.noConfusion h

/-- Does `t` dynamically refine to `B?` (`GSort.boolN`)?  Sound
    approximation: the bool scalar at any null tag, unions containing the
    bool branch, bottom. -/
def chkRefineBoolN (t : GSort) : Bool :=
  match t.shape with
  | .single (.scalar .bool) => true
  | .union ts => ts.any (fun es => decide (es = ExtSort.scalar .bool))
  | .bot => true
  | _ => false

theorem chkRefineBoolN_sound (t : GSort) (h : chkRefineBoolN t = true) :
    DynRefine t GSort.boolN := by
  obtain ⟨sh, n⟩ := t
  simp only [chkRefineBoolN] at h
  split at h
  · -- sh = .single (.scalar .bool)
    cases n with
    | val => exact .sub boolSubtypeBoolN
    | nullable => exact .sub (.refl _)
    | null => exact .sub (.nullSingleton _)
  · -- sh = .union ts
    rename_i ts
    rw [List.any_eq_true] at h
    obtain ⟨es, hmem, hdec⟩ := h
    obtain rfl : es = ExtSort.scalar .bool := of_decide_eq_true hdec
    refine .unionBranch ts (.scalar .bool) n GSort.boolN hmem ?_
    cases n with
    | val => exact .sub boolSubtypeBoolN
    | nullable => exact .sub (.refl _)
    | null => exact .sub (.nullSingleton _)
  · -- sh = .bot
    cases n with
    | val => exact .sub (.bot GSort.boolN)
    | nullable => exact .sub (.nullCov (.bot GSort.bool))
    | null =>
      exact .sub (.trans (.nullSingCov (.bot GSort.bool)) (.nullSingleton _))
  all_goals exact Bool.noConfusion h

/-- Is `t` a subtype of `B?` (`GSort.boolN`)?  Sound approximation:
    the bool scalar at any null tag, and bottom. -/
def chkSubBoolN (t : GSort) : Bool :=
  match t.shape with
  | .single (.scalar .bool) => true
  | .bot => true
  | _ => false

theorem chkSubBoolN_sound (t : GSort) (h : chkSubBoolN t = true) :
    Subtype t GSort.boolN := by
  obtain ⟨sh, n⟩ := t
  simp only [chkSubBoolN] at h
  split at h
  · -- sh = .single (.scalar .bool)
    cases n with
    | val => exact boolSubtypeBoolN
    | nullable => exact .refl _
    | null => exact .nullSingleton _
  · -- sh = .bot
    cases n with
    | val => exact .bot GSort.boolN
    | nullable => exact .nullCov (.bot GSort.bool)
    | null => exact .trans (.nullSingCov (.bot GSort.bool)) (.nullSingleton _)
  all_goals exact Bool.noConfusion h

/-- Does `t` dynamically refine to `N<site>` or `E<site>`?  Used by the
    open-site property-access rule. -/
def chkNodeOrEdgeOf (site : GraphSite) (t : GSort) : Bool :=
  match t.shape with
  | .single (.node s) => decide (s = site)
  | .single (.edge s) => decide (s = site)
  | .single (.nodeRefined s _) => decide (s = site)
  | .single (.edgeRefined s _) => decide (s = site)
  | _ => false

theorem chkNodeOrEdgeOf_sound (site : GraphSite) (t : GSort)
    (h : chkNodeOrEdgeOf site t = true) :
    DynRefine t (GSort.nodeOf site) ∨ DynRefine t (GSort.edgeOf site) := by
  obtain ⟨sh, n⟩ := t
  simp only [chkNodeOrEdgeOf] at h
  split at h
  · -- sh = .single (.node s)
    obtain rfl := of_decide_eq_true h
    left
    cases n with
    | val => exact .sub (.nullable _)
    | nullable => exact .sub (.refl _)
    | null => exact .sub (.nullSingleton _)
  · -- sh = .single (.edge s)
    obtain rfl := of_decide_eq_true h
    right
    cases n with
    | val => exact .sub (.nullable _)
    | nullable => exact .sub (.refl _)
    | null => exact .sub (.nullSingleton _)
  · -- sh = .single (.nodeRefined s ss)
    obtain rfl := of_decide_eq_true h
    left
    cases n with
    | val => exact .sub (.trans (.refineNode _ _ .val) (.nullable _))
    | nullable => exact .sub (.refineNode _ _ .nullable)
    | null => exact .sub (.trans (.refineNode _ _ .null) (.nullSingleton _))
  · -- sh = .single (.edgeRefined s ss)
    obtain rfl := of_decide_eq_true h
    right
    cases n with
    | val => exact .sub (.trans (.refineEdge _ _ .val) (.nullable _))
    | nullable => exact .sub (.refineEdge _ _ .nullable)
    | null => exact .sub (.trans (.refineEdge _ _ .null) (.nullSingleton _))
  all_goals exact Bool.noConfusion h

/- ============================================================
    Property constraint checking (Prp-Empty / Prp-Insert)
    ============================================================ -/

/-- Pairwise key freshness of a property constraint list: each key does not
    reappear among the later constraints.  This is exactly the `hFresh`
    premise chain of the `Prp-Insert` rule. -/
def chkPropFresh : List PropConstraint → Bool
  | [] => true
  | pc :: rest =>
    !(propConstraintSchema rest).keys.any (fun x => x == pc.key) && chkPropFresh rest

theorem chkPropFresh_sound (props : List PropConstraint)
    (h : chkPropFresh props = true) :
    PropConstraintTyping props (propConstraintSchema props) := by
  induction props with
  | nil => exact .empty
  | cons pc rest ih =>
    simp only [chkPropFresh, Bool.and_eq_true] at h
    exact .insert pc.key pc.val (literalBaseSort pc.val) rest
      (propConstraintSchema rest) rfl h.1 (ih h.2)

/- ============================================================
    Atom inference (Atom-Node-* / Atom-Edge-*)
    ============================================================ -/

/-- Infer the record schema of a node atom.  Open site: graph-scoped sort.
    Closed site: label/property filtering, empty former on empty result. -/
def inferAtomNode (ctx : TypingCtx) (na : NodeAtom) : Option RecordSchema :=
  match ctx.schemaMap.lookup ctx.graphSite with
  | none => some (RecordSchema.mk [(na.var, GSort.nodeOf ctx.graphSite)])
  | some Psi =>
    if chkPropFresh na.props then
      if (filterNodeSchemasByPropCompat (resolveNodeSchemas Psi na.labels)
            (propConstraintSchema na.props)).length > 0 then
        some (RecordSchema.mk [(na.var, GSort.nodeRefinedOf ctx.graphSite
          (filterNodeSchemasByPropCompat (resolveNodeSchemas Psi na.labels)
            (propConstraintSchema na.props)))])
      else
        some (RecordSchema.mk [(na.var, GSort.nodeEmpty ctx.graphSite)])
    else none

theorem inferAtomNode_sound (ctx : TypingCtx) (na : NodeAtom)
    (Gamma : RecordSchema) (h : inferAtomNode ctx na = some Gamma) :
    AtomTyping ctx (.node na) Gamma := by
  unfold inferAtomNode at h
  split at h
  · -- open site
    rename_i hlk
    obtain rfl := Option.some.inj h
    exact .nodeOpen ctx na.var na.labels na.props
      (by unfold SchemaMap.isClosed; rw [hlk]; rfl)
  · -- closed site
    rename_i Psi hlk
    have hClosed : ctx.schemaMap.isClosed ctx.graphSite = true := by
      unfold SchemaMap.isClosed; rw [hlk]; rfl
    split at h
    · rename_i hFresh
      split at h
      · rename_i hNE
        obtain rfl := Option.some.inj h
        exact .nodeClosed ctx na.var na.labels na.props Psi
          (propConstraintSchema na.props) (resolveNodeSchemas Psi na.labels)
          _ _ hClosed hlk (chkPropFresh_sound na.props hFresh) rfl rfl rfl hNE
      · rename_i hNE
        obtain rfl := Option.some.inj h
        exact .nodeClosedFail ctx na.var na.labels na.props Psi
          (propConstraintSchema na.props) (resolveNodeSchemas Psi na.labels)
          _ hClosed hlk (chkPropFresh_sound na.props hFresh) rfl rfl
          (Nat.eq_zero_of_not_pos hNE)
    · exact Option.noConfusion h

/-- Infer the record schema of an edge atom (label/property filtering at a
    closed site, graph-scoped at an open site). -/
def inferAtomEdge (ctx : TypingCtx) (ea : EdgeAtom) : Option RecordSchema :=
  match ctx.schemaMap.lookup ctx.graphSite with
  | none => some (RecordSchema.mk [(ea.var, GSort.edgeOf ctx.graphSite)])
  | some Psi =>
    if chkPropFresh ea.props then
      if (filterEdgeSchemasByPropCompat (resolveEdgeSchemas Psi ea.labels)
            (propConstraintSchema ea.props)).length > 0 then
        some (RecordSchema.mk [(ea.var, GSort.edgeRefinedOf ctx.graphSite
          (filterEdgeSchemasByPropCompat (resolveEdgeSchemas Psi ea.labels)
            (propConstraintSchema ea.props)))])
      else
        some (RecordSchema.mk [(ea.var, GSort.edgeEmpty ctx.graphSite)])
    else none

theorem inferAtomEdge_sound (ctx : TypingCtx) (ea : EdgeAtom)
    (Gamma : RecordSchema) (h : inferAtomEdge ctx ea = some Gamma) :
    AtomTyping ctx (.edge { var := ea.var, labels := ea.labels, props := ea.props })
      Gamma := by
  unfold inferAtomEdge at h
  split at h
  · rename_i hlk
    obtain rfl := Option.some.inj h
    exact .edgeOpen ctx ea.var ea.labels ea.props
      (by unfold SchemaMap.isClosed; rw [hlk]; rfl)
  · rename_i Psi hlk
    have hClosed : ctx.schemaMap.isClosed ctx.graphSite = true := by
      unfold SchemaMap.isClosed; rw [hlk]; rfl
    split at h
    · rename_i hFresh
      split at h
      · rename_i hNE
        obtain rfl := Option.some.inj h
        exact .edgeClosed ctx ea.var ea.labels ea.props Psi
          (propConstraintSchema ea.props) (resolveEdgeSchemas Psi ea.labels)
          _ _ hClosed hlk (chkPropFresh_sound ea.props hFresh) rfl rfl rfl hNE
      · rename_i hNE
        obtain rfl := Option.some.inj h
        exact .edgeClosedFail ctx ea.var ea.labels ea.props Psi
          (propConstraintSchema ea.props) (resolveEdgeSchemas Psi ea.labels)
          _ hClosed hlk (chkPropFresh_sound ea.props hFresh) rfl rfl
          (Nat.eq_zero_of_not_pos hNE)
    · exact Option.noConfusion h

/- ============================================================
    Refinement inference (Refine-Closed / -Empty / -Fail / -Open)
    ============================================================ -/

/-- Recognize a triple of schema-refined sorts at `site`. -/
def refinedTriple? (site : GraphSite) (t1 t2 t3 : GSort) :
    Option (List NodeSchemaFull × List EdgeSchemaFull × List NodeSchemaFull) :=
  match t1, t2, t3 with
  | ⟨.single (.nodeRefined s1 sN1), .nullable⟩,
    ⟨.single (.edgeRefined s2 sE2), .nullable⟩,
    ⟨.single (.nodeRefined s3 sN3), .nullable⟩ =>
    if s1 = site ∧ s2 = site ∧ s3 = site then some (sN1, sE2, sN3) else none
  | _, _, _ => none

theorem refinedTriple?_sound (site : GraphSite) (t1 t2 t3 : GSort)
    (sN1 : List NodeSchemaFull) (sE2 : List EdgeSchemaFull)
    (sN3 : List NodeSchemaFull)
    (h : refinedTriple? site t1 t2 t3 = some (sN1, sE2, sN3)) :
    t1 = GSort.nodeRefinedOf site sN1 ∧ t2 = GSort.edgeRefinedOf site sE2 ∧
    t3 = GSort.nodeRefinedOf site sN3 := by
  unfold refinedTriple? at h
  split at h
  · split at h
    · rename_i hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl, rfl⟩
    · exact Option.noConfusion h
  · exact Option.noConfusion h

/-- Recognize a triple of graph-scoped (open) sorts at `site`. -/
def openTriple? (site : GraphSite) (t1 t2 t3 : GSort) : Bool :=
  match t1, t2, t3 with
  | ⟨.single (.node s1), .nullable⟩, ⟨.single (.edge s2), .nullable⟩,
    ⟨.single (.node s3), .nullable⟩ =>
    decide (s1 = site) && decide (s2 = site) && decide (s3 = site)
  | _, _, _ => false

theorem openTriple?_sound (site : GraphSite) (t1 t2 t3 : GSort)
    (h : openTriple? site t1 t2 t3 = true) :
    t1 = GSort.nodeOf site ∧ t2 = GSort.edgeOf site ∧ t3 = GSort.nodeOf site := by
  unfold openTriple? at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  · exact Bool.noConfusion h

/-- The all-empty output schema shared by `Refine-Closed-Empty` and
    `Refine-Closed-Fail`. -/
def refineEmptySchema (ctx : TypingCtx) (Gamma1 Gamma2 Gamma3 : RecordSchema)
    (v1 r2 v3 : Name) : RecordSchema :=
  (Gamma1.join Gamma2 |>.join Gamma3).setMany
    [(v1, GSort.nodeEmpty ctx.graphSite),
     (r2, GSort.edgeEmpty ctx.graphSite),
     (v3, GSort.nodeEmpty ctx.graphSite)]

/-- Infer the three-way endpoint refinement.  Dispatch: any empty former
    fires `Refine-Closed-Empty`; refined triples go through the endpoint
    compatibility projections (`Refine-Closed` / `Refine-Closed-Fail`);
    graph-scoped triples fire `Refine-Open`. -/
def inferRefinement (ctx : TypingCtx) (Gamma1 Gamma2 Gamma3 : RecordSchema)
    (v1 r2 v3 : Name) (dir : Direction) : Option RecordSchema :=
  if Gamma1.joinCompatible Gamma2 && Gamma2.joinCompatible Gamma3 &&
      Gamma1.joinCompatible Gamma3 then
    match Gamma1.lookup v1, Gamma2.lookup r2, Gamma3.lookup v3 with
    | some t1, some t2, some t3 =>
      if t1.isEmptyFormer || t2.isEmptyFormer || t3.isEmptyFormer then
        some (refineEmptySchema ctx Gamma1 Gamma2 Gamma3 v1 r2 v3)
      else
        match refinedTriple? ctx.graphSite t1 t2 t3 with
        | some (sN1, sE2, sN3) =>
          if (refineSrcByCompat sN1 sE2 sN3 dir).length > 0 ∧
              (refineEdgeByCompat sN1 sE2 sN3 dir).length > 0 ∧
              (refineDstByCompat sN1 sE2 sN3 dir).length > 0 then
            some ((Gamma1.join Gamma2 |>.join Gamma3).setMany
              [(v1, GSort.nodeRefinedOf ctx.graphSite (refineSrcByCompat sN1 sE2 sN3 dir)),
               (r2, GSort.edgeRefinedOf ctx.graphSite (refineEdgeByCompat sN1 sE2 sN3 dir)),
               (v3, GSort.nodeRefinedOf ctx.graphSite (refineDstByCompat sN1 sE2 sN3 dir))])
          else if endpointCompatTriple sN1 sE2 sN3 dir = false then
            some (refineEmptySchema ctx Gamma1 Gamma2 Gamma3 v1 r2 v3)
          else none
        | none =>
          if openTriple? ctx.graphSite t1 t2 t3 then
            some (Gamma1.join Gamma2 |>.join Gamma3)
          else none
    | _, _, _ => none
  else none

theorem inferRefinement_sound (ctx : TypingCtx)
    (Gamma1 Gamma2 Gamma3 : RecordSchema) (v1 r2 v3 : Name) (dir : Direction)
    (Gamma : RecordSchema)
    (h : inferRefinement ctx Gamma1 Gamma2 Gamma3 v1 r2 v3 dir = some Gamma) :
    RefinementTyping ctx Gamma1 Gamma2 Gamma3 v1 r2 v3 dir Gamma := by
  unfold inferRefinement at h
  split at h
  case isFalse => exact Option.noConfusion h
  rename_i hJC
  rw [Bool.and_eq_true, Bool.and_eq_true] at hJC
  obtain ⟨⟨hJC12, hJC23⟩, hJC13⟩ := hJC
  split at h
  · -- main arm: all three lookups succeed
    rename_i t1 t2 t3 heq1 heq2 heq3
    split at h
    · -- some sort is an empty former: Refine-Closed-Empty
      rename_i hEmp
      obtain rfl := Option.some.inj h
      rw [Bool.or_eq_true, Bool.or_eq_true] at hEmp
      refine .closedEmpty ctx Gamma1 Gamma2 Gamma3 v1 r2 v3 dir hJC12 hJC23 hJC13 ?_
      rcases hEmp with (h1 | h2) | h3
      · exact Or.inl (by rw [heq1]; exact h1)
      · exact Or.inr (Or.inl (by rw [heq2]; exact h2))
      · exact Or.inr (Or.inr (by rw [heq3]; exact h3))
    · rename_i hNoEmp
      split at h
      · -- refined triple
        rename_i sN1 sE2 sN3 hTrip
        obtain ⟨rfl, rfl, rfl⟩ :=
          refinedTriple?_sound ctx.graphSite t1 t2 t3 sN1 sE2 sN3 hTrip
        split at h
        · -- all projections non-empty: Refine-Closed
          rename_i hNE
          obtain rfl := Option.some.inj h
          exact .closed ctx Gamma1 Gamma2 Gamma3 v1 r2 v3 dir sN1 sE2 sN3
            _ _ _ heq1 heq2 heq3 hJC12 hJC23 hJC13 rfl rfl rfl hNE
        · split at h
          · -- endpoint-incompatible: Refine-Closed-Fail
            rename_i hFail
            obtain rfl := Option.some.inj h
            exact .closedFail ctx Gamma1 Gamma2 Gamma3 v1 r2 v3 dir sN1 sE2 sN3
              heq1 heq2 heq3 hJC12 hJC23 hJC13 hFail
          · exact Option.noConfusion h
      · -- graph-scoped triple: Refine-Open
        split at h
        · rename_i hOpen
          obtain ⟨rfl, rfl, rfl⟩ := openTriple?_sound ctx.graphSite t1 t2 t3 hOpen
          obtain rfl := Option.some.inj h
          exact .open_ ctx Gamma1 Gamma2 Gamma3 v1 r2 v3 dir
            heq1 heq2 heq3 hJC12 hJC23 hJC13
        · exact Option.noConfusion h
  all_goals exact Option.noConfusion h

/- ============================================================
    Pattern inference (Pat-* rules)
    ============================================================ -/

/-- Shared inference for the group-reference quantifier edge rule
    (`Pat-Quant-Edge`): endpoints at graph-scoped sorts, the edge atom
    through atom typing, the edge variable lifted to a list. -/
def inferQuantEdge (ctx : TypingCtx) (n1 n2 : NodeAtom) (rel : EdgeAtom) :
    Option (RecordSchema × Name) :=
  if (rel.var == n1.var) = false ∧ (rel.var == n2.var) = false then
    match inferAtomEdge ctx { var := rel.var, labels := rel.labels, props := rel.props } with
    | some GammaE =>
      some ((((RecordSchema.mk [(n1.var, GSort.nodeOf ctx.graphSite)]).join GammaE).join
        (RecordSchema.mk [(n2.var, GSort.nodeOf ctx.graphSite)])).liftToGroupRef [rel.var],
        n2.var)
    | none => none
  else none

theorem inferQuantEdge_sound (ctx : TypingCtx)
    (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
    (Gamma : RecordSchema) (v : Name)
    (hQuant : rel.quantifier.isGroupRef = true)
    (h : inferQuantEdge ctx n1 n2 rel = some (Gamma, v)) :
    PatternTyping ctx .outside (.edge n1 rel dir n2) Gamma v := by
  unfold inferQuantEdge at h
  split at h
  · rename_i hNE
    split at h
    · rename_i GammaE hAtomE
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .patQuantEdge ctx n1 n2 rel dir rel.quantifier GammaE hQuant
        (inferAtomEdge_sound ctx _ GammaE hAtomE) hNE.1 hNE.2
    · exact Option.noConfusion h
  · exact Option.noConfusion h

/-- Infer the schema and tail variable of a path pattern (`Pat-*` rules).
    Quantified edges and paths only type at `QuantDepth.outside`, mirroring
    the judgment. -/
def inferPattern (ctx : TypingCtx) (qd : QuantDepth) :
    Pattern → Option (RecordSchema × Name)
  | .node na =>
    match inferAtomNode ctx na with
    | some GammaA => some (GammaA, na.var)
    | none => none
  | .edge n1 rel dir n2 =>
    match rel.quantifier with
    | .single =>
      match inferAtomNode ctx n1,
            inferAtomEdge ctx { var := rel.var, labels := rel.labels, props := rel.props },
            inferAtomNode ctx n2 with
      | some GammaN1, some GammaE, some GammaN2 =>
        match inferRefinement ctx GammaN1 GammaE GammaN2 n1.var rel.var n2.var dir with
        | some GammaRef => some (GammaRef, n2.var)
        | none => none
      | _, _, _ => none
    | .question =>
      match qd with
      | .outside =>
        if (rel.var == n1.var) = false ∧ (rel.var == n2.var) = false then
          some ((((RecordSchema.mk [(n1.var, GSort.nodeOf ctx.graphSite)]).join
            (RecordSchema.mk [(rel.var, GSort.edgeOf ctx.graphSite)])).join
            (RecordSchema.mk [(n2.var, GSort.nodeOf ctx.graphSite)])).liftToNullable [rel.var],
            n2.var)
        else none
      | .inside => none
    | _ =>
      match qd with
      | .outside => inferQuantEdge ctx n1 n2 rel
      | .inside => none
  | .step P rel dir n2 =>
    match rel.quantifier with
    | .single =>
      match inferPattern ctx qd P with
      | some (Gamma1, v1) =>
        match inferAtomEdge ctx { var := rel.var, labels := rel.labels, props := rel.props },
              inferAtomNode ctx n2 with
        | some GammaE, some GammaN2 =>
          match inferRefinement ctx Gamma1 GammaE GammaN2 v1 rel.var n2.var dir with
          | some GammaRef => some (GammaRef, n2.var)
          | none => none
        | _, _ => none
      | none => none
    | _ => none
  | .grouped P => inferPattern ctx qd P
  | .quantified P K =>
    match qd with
    | .outside =>
      if K.isGroupRef then
        match inferPattern ctx .inside P with
        | some (GammaInner, v) =>
          some (GammaInner.liftToGroupRef GammaInner.dom, v)
        | none => none
      else none
    | .inside => none
  | .patternList _ _ => none

theorem inferPattern_sound (ctx : TypingCtx) :
    ∀ (P : Pattern) (qd : QuantDepth) (Gamma : RecordSchema) (v : Name),
    inferPattern ctx qd P = some (Gamma, v) →
    PatternTyping ctx qd P Gamma v := by
  intro P
  induction P with
  | node na =>
    intro qd Gamma v h
    simp only [inferPattern] at h
    split at h
    · rename_i GammaA hAtom
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .patNode ctx qd na GammaA (inferAtomNode_sound ctx na GammaA hAtom)
    · exact Option.noConfusion h
  | edge n1 rel dir n2 =>
    intro qd Gamma v h
    obtain ⟨rv, rl, rp, rq⟩ := rel
    cases rq with
    | single =>
      simp only [inferPattern] at h
      split at h
      · rename_i GammaN1 GammaE GammaN2 heq1 heq2 heq3
        split at h
        · rename_i GammaRef hRef
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .patEdge ctx qd n1 n2 ⟨rv, rl, rp, .single⟩ dir
            GammaN1 GammaE GammaN2 GammaRef rfl
            (inferAtomNode_sound ctx n1 GammaN1 heq1)
            (inferAtomEdge_sound ctx _ GammaE heq2)
            (inferAtomNode_sound ctx n2 GammaN2 heq3)
            (inferRefinement_sound ctx GammaN1 GammaE GammaN2
              n1.var rv n2.var dir GammaRef hRef)
        · exact Option.noConfusion h
      all_goals exact Option.noConfusion h
    | question =>
      cases qd with
      | outside =>
        simp only [inferPattern] at h
        split at h
        · rename_i hNE
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .patOptEdge ctx n1 n2 ⟨rv, rl, rp, .question⟩ dir hNE.1 hNE.2
        · exact Option.noConfusion h
      | inside => simp only [inferPattern] at h; exact Option.noConfusion h
    | star =>
      cases qd with
      | outside =>
        simp only [inferPattern] at h
        exact inferQuantEdge_sound ctx n1 n2 ⟨rv, rl, rp, .star⟩ dir
          Gamma v rfl h
      | inside => simp only [inferPattern] at h; exact Option.noConfusion h
    | plus =>
      cases qd with
      | outside =>
        simp only [inferPattern] at h
        exact inferQuantEdge_sound ctx n1 n2 ⟨rv, rl, rp, .plus⟩ dir
          Gamma v rfl h
      | inside => simp only [inferPattern] at h; exact Option.noConfusion h
    | exact i =>
      cases qd with
      | outside =>
        simp only [inferPattern] at h
        exact inferQuantEdge_sound ctx n1 n2 ⟨rv, rl, rp, .exact i⟩ dir
          Gamma v rfl h
      | inside => simp only [inferPattern] at h; exact Option.noConfusion h
    | range i j =>
      cases qd with
      | outside =>
        simp only [inferPattern] at h
        exact inferQuantEdge_sound ctx n1 n2 ⟨rv, rl, rp, .range i j⟩ dir
          Gamma v rfl h
      | inside => simp only [inferPattern] at h; exact Option.noConfusion h
  | step P rel dir n2 ih =>
    intro qd Gamma v h
    obtain ⟨rv, rl, rp, rq⟩ := rel
    cases rq with
    | single =>
      simp only [inferPattern] at h
      split at h
      · rename_i Gamma1 v1 hPrefix
        split at h
        · rename_i GammaE GammaN2 heqE heqN2
          split at h
          · rename_i GammaRef hRef
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .patStep ctx qd P ⟨rv, rl, rp, .single⟩ dir n2
              Gamma1 GammaE GammaN2 GammaRef v1 rfl
              (ih qd Gamma1 v1 hPrefix)
              (inferAtomEdge_sound ctx _ GammaE heqE)
              (inferAtomNode_sound ctx n2 GammaN2 heqN2)
              (inferRefinement_sound ctx Gamma1 GammaE GammaN2
                v1 rv n2.var dir GammaRef hRef)
          · exact Option.noConfusion h
        all_goals exact Option.noConfusion h
      · exact Option.noConfusion h
    | question => exact Option.noConfusion h
    | star => exact Option.noConfusion h
    | plus => exact Option.noConfusion h
    | exact i => exact Option.noConfusion h
    | range i j => exact Option.noConfusion h
  | grouped P ih =>
    intro qd Gamma v h
    simp only [inferPattern] at h
    exact .patGrouped ctx qd P Gamma v (ih qd Gamma v h)
  | quantified P K ih =>
    intro qd Gamma v h
    cases qd with
    | outside =>
      simp only [inferPattern] at h
      split at h
      · rename_i hQuant
        split at h
        · rename_i GammaInner v' hInner
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .patQuantPath ctx P K GammaInner _
            (ih .inside GammaInner _ hInner) hQuant
        · exact Option.noConfusion h
      · exact Option.noConfusion h
    | inside => simp only [inferPattern] at h; exact Option.noConfusion h
  | patternList P1 P2 ih1 ih2 =>
    intro qd Gamma v h
    simp only [inferPattern] at h
    exact Option.noConfusion h

/- ============================================================
    Pattern expression inference (PE-Single / PE-Conjunction)
    ============================================================ -/

/-- The `PE-Single` arm shared by every non-conjunction pattern. -/
def inferPatSingle (ctx : TypingCtx) (P : Pattern) :
    Option RecordSchema :=
  match inferPattern ctx .outside P with
  | some Gv => some Gv.1
  | none => none

theorem inferPatSingle_sound (ctx : TypingCtx)
    (P : Pattern) (Gamma : RecordSchema)
    (h : inferPatSingle ctx P = some Gamma) :
    PatExprTyping ctx P Gamma := by
  unfold inferPatSingle at h
  split at h
  · rename_i Gv heq
    obtain rfl := Option.some.inj h
    exact .single ctx P Gv.1 Gv.2
      (inferPattern_sound ctx P .outside Gv.1 Gv.2 heq)
  · exact Option.noConfusion h

def inferPatExpr (ctx : TypingCtx) : Pattern → Option RecordSchema
  | .patternList P1 P2 =>
    match inferPatExpr ctx P1, inferPattern ctx .outside P2 with
    | some Gamma1, some (Gamma2, _) =>
      if Gamma1.joinCompatible Gamma2 then some (Gamma1.join Gamma2) else none
    | _, _ => none
  | P => inferPatSingle ctx P

theorem inferPatExpr_sound (ctx : TypingCtx) :
    ∀ (P : Pattern) (Gamma : RecordSchema),
    inferPatExpr ctx P = some Gamma →
    PatExprTyping ctx P Gamma := by
  intro P
  induction P with
  | patternList P1 P2 ih1 ih2 =>
    intro Gamma h
    simp only [inferPatExpr] at h
    split at h
    · rename_i Gamma1 Gamma2 v2 heq1 heq2
      split at h
      · rename_i hJC
        obtain rfl := Option.some.inj h
        exact .conjunction ctx P1 P2 Gamma1 Gamma2 v2 (ih1 Gamma1 heq1)
          (inferPattern_sound ctx P2 .outside Gamma2 v2 heq2) hJC
      · exact Option.noConfusion h
    · exact Option.noConfusion h
  | node na => exact fun Gamma h => inferPatSingle_sound ctx _ Gamma h
  | edge n1 rel dir n2 => exact fun Gamma h => inferPatSingle_sound ctx _ Gamma h
  | step P rel dir n2 ih => exact fun Gamma h => inferPatSingle_sound ctx _ Gamma h
  | grouped P ih => exact fun Gamma h => inferPatSingle_sound ctx _ Gamma h
  | quantified P K ih => exact fun Gamma h => inferPatSingle_sound ctx _ Gamma h

/- ============================================================
    Expression and predicate inference (E-* / FTy rules)
    ============================================================ -/

/-- Closed-site property type: if `tcomp` is the schema-refined node/edge
    sort of `site`, compute the `H-PropType` union for key `k`. -/
def closedPropType (site : GraphSite) (tcomp : GSort) (k : Name) : Option GSort :=
  match tcomp with
  | ⟨.single (.nodeRefined s ns), .nullable⟩ =>
    if s = site then some (propTypeOfNodeSchemas ns k) else none
  | ⟨.single (.edgeRefined s es), .nullable⟩ =>
    if s = site then some (propTypeOfEdgeSchemas es k) else none
  | _ => none

theorem closedPropType_sound (site : GraphSite) (tcomp : GSort) (k : Name)
    (ty : GSort) (h : closedPropType site tcomp k = some ty) :
    (∃ ns, tcomp = GSort.nodeRefinedOf site ns ∧ ty = propTypeOfNodeSchemas ns k) ∨
    (∃ es, tcomp = GSort.edgeRefinedOf site es ∧ ty = propTypeOfEdgeSchemas es k) := by
  unfold closedPropType at h
  split at h
  · rename_i s ns
    split at h
    · rename_i hs
      subst hs
      exact Or.inl ⟨ns, rfl, (Option.some.inj h).symm⟩
    · exact Option.noConfusion h
  · rename_i s es
    split at h
    · rename_i hs
      subst hs
      exact Or.inr ⟨es, rfl, (Option.some.inj h).symm⟩
    · exact Option.noConfusion h
  · exact Option.noConfusion h

mutual

/-- Expression type inference.  Returns the sort and the referenced
    variable set of the judgment's conclusion. -/
def inferExpr (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx) :
    Expr → Option (GSort × VarSet)
  | .const (.int _) => some (GSort.int, VarSet.empty)
  | .const (.string _) => some (GSort.string, VarSet.empty)
  | .const (.bool _) => some (GSort.bool, VarSet.empty)
  | .null => some (GSort.nullSort, VarSet.empty)
  | .var x =>
    match Ctx.lookup x with
    | some tau => some (tau, VarSet.single x)
    | none => none
  | .arithOp _ e1 e2 =>
    match inferExpr ctx Ctx box hat e1, inferExpr ctx Ctx box hat e2 with
    | some (t1, o1), some (t2, o2) =>
      if chkRefineIntN t1 && chkRefineIntN t2 then
        some (GSort.intN, VarSet.union o1 o2)
      else none
    | _, _ => none
  | .propAccess x k =>
    match Ctx.lookup x with
    | some tx =>
      if ctx.schemaMap.isClosed ctx.graphSite then
        match closedPropType ctx.graphSite tx.componentType k with
        | some ty => some (ty, VarSet.single x)
        | none => none
      else
        if chkNodeOrEdgeOf ctx.graphSite tx.componentType then
          some (GSort.anyScalarN, VarSet.single x)
        else none
    | none => none
  | .agg op _qual e =>
    if box = .one then
      if hat = .singleton then
        match inferExpr ctx Ctx .zero .singleton e with
        | some (_tau1, [x]) =>
          match Ctx.lookup x with
          | some elemSort =>
            if op = .count then
              if elemSort.isList then some (GSort.int, VarSet.single x) else none
            else if op = .sum ∨ op = .max ∨ op = .min then
              match elemSort.elemSort? with
              | some innerTy =>
                if chkRefineIntN innerTy then some (GSort.intN, VarSet.single x)
                else none
              | none => none
            else none
          | none => none
        | _ => none
      else if hat = .group then
        match inferExpr ctx Ctx .zero .group e with
        | some (_tau1, o1) =>
          if o1.subset Ctx.dom then
            if op = .count then some (GSort.int, o1)
            else if op = .sum ∨ op = .max ∨ op = .min then some (GSort.intN, o1)
            else none
          else none
        | none => none
      else none
    else none
  | .pred phi => inferPred ctx Ctx box hat phi

/-- Predicate type inference. -/
def inferPred (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth) (hat : RefCtx) :
    Pred → Option (GSort × VarSet)
  | .true => some (GSort.bool, VarSet.empty)
  | .false => some (GSort.bool, VarSet.empty)
  | .relOp _ e1 e2 =>
    match inferExpr ctx Ctx box hat e1, inferExpr ctx Ctx box hat e2 with
    | some (t1, o1), some (t2, o2) =>
      if chkRefineIntN t1 && chkRefineIntN t2 then
        some (GSort.boolN, VarSet.union o1 o2)
      else none
    | _, _ => none
  | .not phi =>
    match inferPred ctx Ctx box hat phi with
    | some (t, o) => if chkRefineBoolN t then some (GSort.boolN, o) else none
    | none => none
  | .and p1 p2 =>
    match inferPred ctx Ctx box hat p1, inferPred ctx Ctx box hat p2 with
    | some (t1, o1), some (t2, o2) =>
      if chkRefineBoolN t1 && chkRefineBoolN t2 then
        some (GSort.boolN, VarSet.union o1 o2)
      else none
    | _, _ => none
  | .or p1 p2 =>
    match inferPred ctx Ctx box hat p1, inferPred ctx Ctx box hat p2 with
    | some (t1, o1), some (t2, o2) =>
      if chkRefineBoolN t1 && chkRefineBoolN t2 then
        some (GSort.boolN, VarSet.union o1 o2)
      else none
    | _, _ => none
  | .isNull e =>
    match inferExpr ctx Ctx box hat e with
    | some (_, o) => some (GSort.bool, o)
    | none => none

end

mutual

theorem inferExpr_sound (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth)
    (hat : RefCtx) (e : Expr) (t : GSort) (o : VarSet)
    (h : inferExpr ctx Ctx box hat e = some (t, o)) :
    ExprTyping ctx Ctx box hat e t o := by
  match e with
  | .const (.int n) =>
    simp only [inferExpr, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .constInt ctx Ctx box hat n
  | .const (.string s) =>
    simp only [inferExpr, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .constString ctx Ctx box hat s
  | .const (.bool b) =>
    simp only [inferExpr, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .constBool ctx Ctx box hat b
  | .null =>
    simp only [inferExpr, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .constNull ctx Ctx box hat
  | .var x =>
    simp only [inferExpr] at h
    split at h
    · rename_i tau hLookup
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .var ctx Ctx box hat x _ hLookup
    · exact Option.noConfusion h
  | .arithOp op e1 e2 =>
    simp only [inferExpr] at h
    split at h
    · rename_i t1 o1 t2 o2 heq1 heq2
      split at h
      · rename_i hchk
        rw [Bool.and_eq_true] at hchk
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .arithOp ctx Ctx box hat op e1 e2 t1 t2 o1 o2
          (inferExpr_sound ctx Ctx box hat e1 t1 o1 heq1)
          (inferExpr_sound ctx Ctx box hat e2 t2 o2 heq2)
          (chkRefineIntN_sound t1 hchk.1) (chkRefineIntN_sound t2 hchk.2)
      · exact Option.noConfusion h
    all_goals exact Option.noConfusion h
  | .propAccess x k =>
    simp only [inferExpr] at h
    split at h
    · rename_i tx hLookup
      split at h
      · -- closed site
        rename_i hClosed
        split at h
        · rename_i ty hPT
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rcases closedPropType_sound ctx.graphSite tx.componentType k ty hPT with
            ⟨ns, hcomp, hty⟩ | ⟨es, hcomp, hty⟩
          · exact .propAccessSchema ctx Ctx box hat x k tx ty ns []
              hLookup hClosed (Or.inl ⟨hcomp, hty⟩)
          · exact .propAccessSchema ctx Ctx box hat x k tx ty [] es
              hLookup hClosed (Or.inr ⟨hcomp, hty⟩)
        · exact Option.noConfusion h
      · -- open site
        rename_i hNotClosed
        have hOpen : ctx.schemaMap.isClosed ctx.graphSite = false := by
          cases hb : ctx.schemaMap.isClosed ctx.graphSite
          · rfl
          · exact absurd hb hNotClosed
        split at h
        · rename_i hchk
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .propAccessOpen ctx Ctx box hat x k tx hLookup
            (chkNodeOrEdgeOf_sound ctx.graphSite tx.componentType hchk) hOpen
        · exact Option.noConfusion h
    · exact Option.noConfusion h
  | .agg op qual e =>
    simp only [inferExpr] at h
    split at h
    · rename_i hbox
      subst hbox
      split at h
      · -- singleton reference context
        rename_i hhat
        subst hhat
        split at h
        · rename_i _tau1 x heqE
          split at h
          · rename_i elemSort hLk
            split at h
            · -- count
              rename_i hop
              subst hop
              split at h
              · rename_i hIsList
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact .countSingleton ctx Ctx qual e x _tau1 elemSort
                  (inferExpr_sound ctx Ctx .zero .singleton e _tau1 [x] heqE)
                  hLk hIsList
              · exact Option.noConfusion h
            · -- sum/max/min
              rename_i hNotCount
              split at h
              · rename_i hOp
                split at h
                · rename_i innerTy hElem
                  split at h
                  · rename_i hchk
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact .aggSingleton ctx Ctx op qual e x _tau1 elemSort
                      innerTy hOp
                      (inferExpr_sound ctx Ctx .zero .singleton e _tau1 [x] heqE)
                      hLk hElem (chkRefineIntN_sound innerTy hchk)
                  · exact Option.noConfusion h
                · exact Option.noConfusion h
              · exact Option.noConfusion h
          · exact Option.noConfusion h
        all_goals exact Option.noConfusion h
      · -- group reference context
        rename_i hNotSingleton
        split at h
        · rename_i hhat
          subst hhat
          split at h
          · rename_i _tau1 o1 heqE
            split at h
            · rename_i hSubset
              split at h
              · -- count
                rename_i hop
                subst hop
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact .countGroup ctx Ctx qual e _tau1 o1
                  (inferExpr_sound ctx Ctx .zero .group e _tau1 o1 heqE) hSubset
              · rename_i hNotCount
                split at h
                · rename_i hOp
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact .aggGroup ctx Ctx op qual e _tau1 o1 hOp
                    (inferExpr_sound ctx Ctx .zero .group e _tau1 o1 heqE) hSubset
                · exact Option.noConfusion h
            · exact Option.noConfusion h
          · exact Option.noConfusion h
        · exact Option.noConfusion h
    · exact Option.noConfusion h
  | .pred phi =>
    simp only [inferExpr] at h
    exact .pred ctx Ctx box hat phi t o
      (inferPred_sound ctx Ctx box hat phi t o h)

theorem inferPred_sound (ctx : TypingCtx) (Ctx : RecordSchema) (box : AggDepth)
    (hat : RefCtx) (phi : Pred) (t : GSort) (o : VarSet)
    (h : inferPred ctx Ctx box hat phi = some (t, o)) :
    PredTyping ctx Ctx box hat phi t o := by
  match phi with
  | .true =>
    simp only [inferPred, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .true ctx Ctx box hat
  | .false =>
    simp only [inferPred, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .false ctx Ctx box hat
  | .relOp op e1 e2 =>
    simp only [inferPred] at h
    split at h
    · rename_i t1 o1 t2 o2 heq1 heq2
      split at h
      · rename_i hchk
        rw [Bool.and_eq_true] at hchk
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .relOp ctx Ctx box hat op e1 e2 t1 t2 o1 o2
          (inferExpr_sound ctx Ctx box hat e1 t1 o1 heq1)
          (inferExpr_sound ctx Ctx box hat e2 t2 o2 heq2)
          (chkRefineIntN_sound t1 hchk.1) (chkRefineIntN_sound t2 hchk.2)
      · exact Option.noConfusion h
    all_goals exact Option.noConfusion h
  | .not p =>
    simp only [inferPred] at h
    split at h
    · rename_i tp op' heq
      split at h
      · rename_i hchk
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .not ctx Ctx box hat p tp op'
          (inferPred_sound ctx Ctx box hat p tp op' heq)
          (chkRefineBoolN_sound tp hchk)
      · exact Option.noConfusion h
    · exact Option.noConfusion h
  | .and p1 p2 =>
    simp only [inferPred] at h
    split at h
    · rename_i t1 o1 t2 o2 heq1 heq2
      split at h
      · rename_i hchk
        rw [Bool.and_eq_true] at hchk
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .and ctx Ctx box hat p1 p2 t1 t2 o1 o2
          (inferPred_sound ctx Ctx box hat p1 t1 o1 heq1)
          (inferPred_sound ctx Ctx box hat p2 t2 o2 heq2)
          (chkRefineBoolN_sound t1 hchk.1) (chkRefineBoolN_sound t2 hchk.2)
      · exact Option.noConfusion h
    all_goals exact Option.noConfusion h
  | .or p1 p2 =>
    simp only [inferPred] at h
    split at h
    · rename_i t1 o1 t2 o2 heq1 heq2
      split at h
      · rename_i hchk
        rw [Bool.and_eq_true] at hchk
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .or ctx Ctx box hat p1 p2 t1 t2 o1 o2
          (inferPred_sound ctx Ctx box hat p1 t1 o1 heq1)
          (inferPred_sound ctx Ctx box hat p2 t2 o2 heq2)
          (chkRefineBoolN_sound t1 hchk.1) (chkRefineBoolN_sound t2 hchk.2)
      · exact Option.noConfusion h
    all_goals exact Option.noConfusion h
  | .isNull e =>
    simp only [inferPred] at h
    split at h
    · rename_i te oe heq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .isNull ctx Ctx box hat e te oe
        (inferExpr_sound ctx Ctx box hat e te oe heq)
    · exact Option.noConfusion h

end

/- ============================================================
    Projection inference (Prj-Atom / Prj-Alias / Prj-Agg-Alias)
    ============================================================ -/

def inferProjection (ctx : TypingCtx) (Ctx : RecordSchema) :
    Projection → Option RecordSchema
  | .expr (.var x) =>
    match Ctx.lookup x with
    | some tau => some (RecordSchema.mk [(x, tau)])
    | none => none
  | .alias' e x =>
    match inferExpr ctx Ctx .one .group e with
    | some (tau, _) => some (RecordSchema.mk [(x, tau)])
    | none => none
  | .aggAs op qual e y =>
    match inferExpr ctx Ctx .one .group (.agg op qual e) with
    | some (tau, _) => some (RecordSchema.mk [(y, tau)])
    | none => none
  | _ => none

theorem inferProjection_sound (ctx : TypingCtx) (Ctx : RecordSchema)
    (pi : Projection) (Gpi : RecordSchema)
    (h : inferProjection ctx Ctx pi = some Gpi) :
    ProjectionTyping ctx Ctx pi Gpi := by
  match pi with
  | .expr (.var x) =>
    simp only [inferProjection] at h
    split at h
    · rename_i tau hLookup
      obtain rfl := Option.some.inj h
      exact .atom ctx Ctx x tau hLookup
    · exact Option.noConfusion h
  | .alias' e x =>
    simp only [inferProjection] at h
    split at h
    · rename_i tau o' heq
      obtain rfl := Option.some.inj h
      exact .alias' ctx Ctx e x tau o'
        (inferExpr_sound ctx Ctx .one .group e tau o' heq)
    · exact Option.noConfusion h
  | .aggAs op qual e y =>
    simp only [inferProjection] at h
    split at h
    · rename_i tau o' heq
      obtain rfl := Option.some.inj h
      exact .aggAs ctx Ctx op qual e y tau o'
        (inferExpr_sound ctx Ctx .one .group (.agg op qual e) tau o' heq)
    · exact Option.noConfusion h
  | .expr (.const _) => exact Option.noConfusion h
  | .expr .null => exact Option.noConfusion h
  | .expr (.propAccess _ _) => exact Option.noConfusion h
  | .expr (.arithOp _ _ _) => exact Option.noConfusion h
  | .expr (.agg _ _ _) => exact Option.noConfusion h
  | .expr (.pred _) => exact Option.noConfusion h
  | .agg _ _ _ => exact Option.noConfusion h

def inferProjectionList (ctx : TypingCtx) (Ctx : RecordSchema) :
    ProjectionList → Option RecordSchema
  | [] => some RecordSchema.empty
  | pi :: pis =>
    match inferProjection ctx Ctx pi, inferProjectionList ctx Ctx pis with
    | some Gpi, some Grest =>
      if RecordSchema.disjointUnionCompatible Gpi Grest then
        some (Gpi.disjointUnion Grest)
      else none
    | _, _ => none

theorem inferProjectionList_sound (ctx : TypingCtx) (Ctx : RecordSchema) :
    ∀ (pis : ProjectionList) (Gamma : RecordSchema),
    inferProjectionList ctx Ctx pis = some Gamma →
    ProjectionListTyping ctx Ctx pis Gamma := by
  intro pis
  induction pis with
  | nil =>
    intro Gamma h
    simp only [inferProjectionList] at h
    obtain rfl := Option.some.inj h
    exact .nil ctx Ctx
  | cons pi pis ih =>
    intro Gamma h
    simp only [inferProjectionList] at h
    split at h
    · rename_i Gpi Grest heq1 heq2
      split at h
      · rename_i hDisj
        obtain rfl := Option.some.inj h
        exact .cons ctx Ctx pi pis Gpi Grest
          (inferProjection_sound ctx Ctx pi Gpi heq1) (ih Grest heq2) hDisj
      · exact Option.noConfusion h
    all_goals exact Option.noConfusion h

/- ============================================================
    Query inference (Q-Match / Q-Match-Filter / Use / CQ-Expression)
    ============================================================ -/

/-- Executable query type inference: computes the result record schema of a
    query, certified sound against `QueryTyping` by `inferQuery_sound`. -/
def inferQuery (ctx : TypingCtx) : Query → Option RecordSchema
  | .matchReturn P projs =>
    if (ctx.catalog.lookup ctx.graphSite).isSome then
      match inferPatExpr ctx P with
      | some Gamma1 => inferProjectionList ctx Gamma1 projs
      | none => none
    else none
  | .matchWhere P phi projs =>
    if (ctx.catalog.lookup ctx.graphSite).isSome then
      match inferPatExpr ctx P with
      | some Gamma1 =>
        match inferPred ctx Gamma1 .one .singleton phi with
        | some (tPred, _) =>
          if chkSubBoolN tPred then inferProjectionList ctx Gamma1 projs
          else none
        | none => none
      | none => none
    else none
  | .useGraph g Q =>
    if (ctx.catalog.lookup g).isSome then
      inferQuery { ctx with graphSite := g } Q
    else none
  | .composite op Q1 Q2 =>
    match inferQuery ctx Q1, inferQuery ctx Q2 with
    | some Gamma1, some Gamma2 =>
      if opCompatible op Gamma1 Gamma2 then some (opCombine op Gamma1 Gamma2)
      else none
    | _, _ => none

/-- Every query the checker accepts is well typed at the inferred schema. -/
theorem inferQuery_sound :
    ∀ (Q : Query) (ctx : TypingCtx) (Gamma : RecordSchema),
    inferQuery ctx Q = some Gamma → QueryTyping ctx Q Gamma := by
  intro Q
  induction Q with
  | useGraph g Q ih =>
    intro ctx Gamma h
    simp only [inferQuery] at h
    split at h
    · rename_i hResolve
      exact .useGraph ctx g Q Gamma hResolve (ih _ Gamma h)
    · exact Option.noConfusion h
  | matchReturn P projs =>
    intro ctx Gamma h
    simp only [inferQuery] at h
    split at h
    · rename_i hGraph
      split at h
      · rename_i Gamma1 heq1
        exact .matchReturn ctx P projs Gamma1 Gamma hGraph
          (inferPatExpr_sound ctx P Gamma1 heq1)
          (inferProjectionList_sound ctx Gamma1 projs Gamma h)
      · exact Option.noConfusion h
    · exact Option.noConfusion h
  | matchWhere P phi projs =>
    intro ctx Gamma h
    simp only [inferQuery] at h
    split at h
    · rename_i hGraph
      split at h
      · rename_i Gamma1 heq1
        split at h
        · rename_i tPred omegaPred heqPred
          split at h
          · rename_i hSub
            exact .matchFilter ctx P phi projs Gamma1 Gamma tPred omegaPred hGraph
              (inferPatExpr_sound ctx P Gamma1 heq1)
              (inferPred_sound ctx Gamma1 .one .singleton phi
                tPred omegaPred heqPred)
              (chkSubBoolN_sound tPred hSub)
              (inferProjectionList_sound ctx Gamma1 projs Gamma h)
          · exact Option.noConfusion h
        · exact Option.noConfusion h
      · exact Option.noConfusion h
    · exact Option.noConfusion h
  | composite op Q1 Q2 ih1 ih2 =>
    intro ctx Gamma h
    simp only [inferQuery] at h
    split at h
    · rename_i Gamma1 Gamma2 heq1 heq2
      split at h
      · rename_i hCompat
        obtain rfl := Option.some.inj h
        exact .composite ctx op Q1 Q2 Gamma1 Gamma2
          (ih1 ctx Gamma1 heq1) (ih2 ctx Gamma2 heq2) hCompat
      · exact Option.noConfusion h
    all_goals exact Option.noConfusion h

/- ============================================================
    End-to-end: checker acceptance implies semantic conformance
    ============================================================ -/

/-- If the checker accepts `Q` with schema `Gamma`, then under the standard
    catalog assumptions the evaluated binding table conforms to `Gamma`
    (composition with Theorem 6.3 across mixed open/closed sites). -/
theorem inferQuery_conforms
    (hCat : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' →
        ∀ Psi, ctx'.schemaMap.lookup ctx'.graphSite = some Psi →
          graphConformsSchema G' Psi = true)
    (hWF : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' → GraphValuesWF G')
    (ctx : TypingCtx) (G : PropertyGraph) (Q : Query) (Gamma : RecordSchema)
    (hInfer : inferQuery ctx Q = some Gamma)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G) :
    BTConforms (evalQuery ctx.catalog G ctx.graphSite Q) Gamma :=
  queryTypeSoundness_composed_mixedSites hCat hWF ctx G Q Gamma
    (inferQuery_sound Q ctx Gamma hInfer) hGraph

/- ============================================================
    Uniform composite inference (the paper judgment |-_circledast)
    ============================================================ -/

/-- Inference for the operator-indexed composite judgment: the left spine
    must use `op` throughout and every operand must be linear. -/
def inferCompQuery (ctx : TypingCtx) (op : SetOp) : Query → Option RecordSchema
  | .composite op' q Q =>
    if op' = op ∧ Q.isLinear = true then
      match inferCompQuery ctx op q, inferQuery ctx Q with
      | some Gamma1, some Gamma2 =>
        if opCompatible op Gamma1 Gamma2 then some (opCombine op Gamma1 Gamma2)
        else none
      | _, _ => none
    else none
  | .useGraph g Q =>
    if (Query.useGraph g Q).isLinear = true then inferQuery ctx (.useGraph g Q)
    else none
  | .matchReturn P projs => inferQuery ctx (.matchReturn P projs)
  | .matchWhere P phi projs => inferQuery ctx (.matchWhere P phi projs)

theorem inferCompQuery_sound (ctx : TypingCtx) (op : SetOp) :
    ∀ (q : Query) (Gamma : RecordSchema),
    inferCompQuery ctx op q = some Gamma → CompQueryTyping ctx op q Gamma := by
  intro q
  induction q with
  | composite op' q1 q2 ih1 _ih2 =>
    intro Gamma h
    simp only [inferCompQuery] at h
    split at h
    · rename_i hcond
      obtain ⟨rfl, hLin2⟩ := hcond
      split at h
      · rename_i Gamma1 Gamma2 heq1 heq2
        split at h
        · rename_i hCompat
          obtain rfl := Option.some.inj h
          exact .expression ctx op' q1 q2 Gamma1 Gamma2 (ih1 Gamma1 heq1) hLin2
            (inferQuery_sound q2 ctx Gamma2 heq2) hCompat
        · exact Option.noConfusion h
      all_goals exact Option.noConfusion h
    · exact Option.noConfusion h
  | useGraph g Q _ih =>
    intro Gamma h
    simp only [inferCompQuery] at h
    split at h
    · rename_i hLin
      exact .lift ctx op _ Gamma hLin (inferQuery_sound _ ctx Gamma h)
    · exact Option.noConfusion h
  | matchReturn P projs =>
    intro Gamma h
    exact .lift ctx op _ Gamma rfl (inferQuery_sound _ ctx Gamma h)
  | matchWhere P phi projs =>
    intro Gamma h
    exact .lift ctx op _ Gamma rfl (inferQuery_sound _ ctx Gamma h)

/-- Acceptance in the single-operator judgment implies semantic
    conformance (Corollary 6.1 through the checker). -/
theorem inferCompQuery_conforms
    (hCat : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' →
        ∀ Psi, ctx'.schemaMap.lookup ctx'.graphSite = some Psi →
          graphConformsSchema G' Psi = true)
    (hWF : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' → GraphValuesWF G')
    (ctx : TypingCtx) (G : PropertyGraph) (op : SetOp) (q : Query)
    (Gamma : RecordSchema)
    (hInfer : inferCompQuery ctx op q = some Gamma)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G) :
    BTConforms (evalQuery ctx.catalog G ctx.graphSite q) Gamma :=
  compQueryTypeSoundness_mixedSites hCat hWF ctx G op q Gamma
    (inferCompQuery_sound ctx op q Gamma hInfer) hGraph

end MGQL
