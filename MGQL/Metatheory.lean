/-
  MGQL: Mechanized GQL Semantics in Lean 4
  Metatheory.lean -- Type Soundness (Paper Section 6)
-/
import MGQL.Sorts
import MGQL.Values
import MGQL.Syntax
import MGQL.Schema
import MGQL.RecordSchema
import MGQL.Subtyping
import MGQL.Typing
import MGQL.Semantics

namespace MGQL

-- ============================================================
--  Value Typing (Paper Definition 6.1)
-- ============================================================

inductive ValueTyping : Value -> GSort -> Prop where
  | intVal (n : Int) : ValueTyping (.prim (.int n)) GSort.int
  | stringVal (s : String) : ValueTyping (.prim (.string s)) GSort.string
  | boolVal (b : Bool) : ValueTyping (.prim (.bool b)) GSort.bool
  | nullType : ValueTyping .null GSort.nullSort
  | nullNullable (s : SortShape) : ValueTyping .null (GSort.mk s .nullable)
  | nodeRef (G : GraphSite) (n : Nat) : ValueTyping (.nodeRef G n) (GSort.nodeOf G)
  | edgeRef (G : GraphSite) (e : Nat) : ValueTyping (.edgeRef G e) (GSort.edgeOf G)
  | nodeRefRefined (G : GraphSite) (n : Nat) (ss : List NodeSchemaFull) :
      ValueTyping (.nodeRef G n) (GSort.nodeRefinedOf G ss)
  | edgeRefRefined (G : GraphSite) (e : Nat) (ss : List EdgeSchemaFull) :
      ValueTyping (.edgeRef G e) (GSort.edgeRefinedOf G ss)
  | anyVal (v : Value) : ValueTyping v GSort.any
  | subsume (v : Value) (t1 t2 : GSort) :
      ValueTyping v t1 -> Subtype t1 t2 -> ValueTyping v t2

-- ============================================================
--  Prop-level Conformance
-- ============================================================

def RecordConforms (rho : Record) (Gamma : RecordSchema) : Prop :=
  -- Paper (Def. Record Schema Conformance): dom(rho) = dom(Gamma), AND every
  -- bound value inhabits its declared type. The domain equality (as sets, via
  -- `mem`) was previously omitted; without it record join is unsound (a record
  -- could carry an extra binding outside Gamma that survives a merge).
  (forall x : Name, rho.mem x = Gamma.mem x) ∧
  (forall (x : Name) (t : GSort),
    (x, t) ∈ Gamma.entries ->
    RecordSchema.valueAdmissible (rho.lookup x) t = true)

def BTConforms (B : BindingTable) (Gamma : RecordSchema) : Prop :=
  forall (rho : Record), rho ∈ B -> RecordConforms rho Gamma

-- ============================================================
--  Filter membership
-- ============================================================

private theorem mem_of_filter {a : Record} {l : List Record}
    {p : Record -> Bool} (h : a ∈ l.filter p) : a ∈ l := by
  induction l with
  | nil => simp [List.filter] at h
  | cons x xs ih =>
    simp only [List.filter] at h
    split at h
    · cases h with
      | head => exact List.Mem.head _
      | tail _ ht => exact List.Mem.tail _ (ih ht)
    · exact List.Mem.tail _ (ih h)

-- ============================================================
--  Conformance Preservation (fully proved)
-- ============================================================

theorem filter_preserves (B : BindingTable) (Gamma : RecordSchema)
    (p : Record -> Bool) (h : BTConforms B Gamma) :
    BTConforms (B.filter p) Gamma :=
  fun rho hmem => h rho (mem_of_filter hmem)

theorem union_preserves (B1 B2 : BindingTable) (Gamma : RecordSchema)
    (h1 : BTConforms B1 Gamma) (h2 : BTConforms B2 Gamma) :
    BTConforms (B1 ++ B2) Gamma := by
  intro rho hmem
  cases List.mem_append.mp hmem with
  | inl hl => exact h1 rho hl
  | inr hr => exact h2 rho hr

theorem dist_preserves (B : BindingTable) (Gamma : RecordSchema)
    (h : BTConforms B Gamma) :
    BTConforms (dist B) Gamma := by
  unfold dist
  suffices hgen : forall (l : BindingTable), BTConforms l Gamma ->
    forall (acc : BindingTable), BTConforms acc Gamma ->
    BTConforms (l.foldl (fun a rr =>
      if a.any (fun xx => xx == rr) then a else a ++ [rr]) acc) Gamma by
    exact hgen B h [] (fun _ habs => absurd habs (List.not_mem_nil _))
  intro l hl acc hacc
  induction l generalizing acc with
  | nil => simpa [List.foldl]
  | cons y ys ih =>
    simp only [List.foldl]
    split
    · exact ih (fun r hr => hl r (List.Mem.tail _ hr)) acc hacc
    · apply ih (fun r hr => hl r (List.Mem.tail _ hr))
      intro r hr
      cases List.mem_append.mp hr with
      | inl ha => exact hacc r ha
      | inr hy =>
        cases hy with
        | head => exact hl y (List.Mem.head _)
        | tail _ hnil => exact absurd hnil (List.not_mem_nil _)

/-- The first component of a pair-threading fold whose step only ever appends
    the current element to the left accumulator preserves conformance. Both the
    bag `EXCEPT ALL` and `INTERSECT ALL` folds have this shape (they differ only
    in which branch appends and how the right remainder shrinks), so a single
    membership argument covers both: every record placed in the result
    accumulator is drawn from the folded table `l`, hence conforms whenever `l`
    does. -/
theorem foldPairFst_preserves (Gamma : RecordSchema)
    (step : BindingTable × BindingTable -> Record -> BindingTable × BindingTable)
    (hstep : forall st rho, (step st rho).1 = st.1 \/ (step st rho).1 = st.1 ++ [rho])
    (l : BindingTable) (hl : BTConforms l Gamma)
    (init : BindingTable × BindingTable) (hinit : BTConforms init.1 Gamma) :
    BTConforms (l.foldl step init).1 Gamma := by
  induction l generalizing init with
  | nil => simpa [List.foldl] using hinit
  | cons y ys ih =>
    simp only [List.foldl]
    apply ih (fun r hr => hl r (List.Mem.tail _ hr)) (step init y)
    cases hstep init y with
    | inl heq => rw [heq]; exact hinit
    | inr heq =>
      rw [heq]
      intro r hr
      cases List.mem_append.mp hr with
      | inl ha => exact hinit r ha
      | inr hy =>
        cases hy with
        | head => exact hl y (List.Mem.head _)
        | tail _ hnil => exact absurd hnil (List.not_mem_nil _)

-- ============================================================
--  Set Op Conformance (same schema) (fully proved)
-- ============================================================

theorem setop_preserves_same (op : SetOp) (B1 B2 : BindingTable)
    (Gamma : RecordSchema)
    (h1 : BTConforms B1 Gamma) (h2 : BTConforms B2 Gamma) :
    BTConforms (applySetOp op B1 B2) Gamma := by
  cases op
  case union =>
    show BTConforms (B1 ++ B2) Gamma
    exact union_preserves B1 B2 Gamma h1 h2
  case otherwise =>
    show BTConforms (if B1.isEmpty then B2 else B1) Gamma
    split
    · exact h2
    · exact h1
  case exceptDistinct =>
    show BTConforms (dist (List.filter _ _)) Gamma
    exact dist_preserves _ Gamma (filter_preserves B1 Gamma _ h1)
  case exceptAll =>
    simp only [applySetOp]
    exact foldPairFst_preserves Gamma _
      (by intro st rho; obtain ⟨acc, rem⟩ := st; split
          · exact Or.inl rfl
          · exact Or.inr rfl)
      B1 h1 ([], B2) (fun _ habs => absurd habs (List.not_mem_nil _))
  case intersectDistinct =>
    show BTConforms (dist (List.filter _ _)) Gamma
    exact dist_preserves _ Gamma (filter_preserves B1 Gamma _ h1)
  case intersectAll =>
    simp only [applySetOp]
    exact foldPairFst_preserves Gamma _
      (by intro st rho; obtain ⟨acc, rem⟩ := st; split
          · exact Or.inr rfl
          · exact Or.inl rfl)
      B1 h1 ([], B2) (fun _ habs => absurd habs (List.not_mem_nil _))

-- ============================================================
--  Bool <-> Prop Bridge (fully proved)
-- ============================================================

-- (Bool ⇒ Prop bridge `btConforms_of_bool` was removed: the Bool check
--  `bindingTableConforms` only verifies per-entry admissibility, so it cannot
--  witness the domain-equality now required by `RecordConforms`. The Prop ⇒ Bool
--  direction still holds, since `BTConforms` is the stronger property.)

theorem bool_of_btConforms (B : BindingTable) (Gamma : RecordSchema)
    (h : BTConforms B Gamma) :
    RecordSchema.bindingTableConforms B Gamma = true := by
  simp [RecordSchema.bindingTableConforms]
  intro rho hmem x t hentry
  exact (h rho hmem).2 x t hentry

-- ============================================================
--  Primitive Admissibility Lemmas (proved by rfl)
--  These close expressions by definitional reduction.
-- ============================================================

/-- null is admissible for any nullable type. Proved via rfl since
  valueAdmissible reduces to true when v = null and t.null = nullable. -/
private theorem null_admissible_intN :
    RecordSchema.valueAdmissible Value.null GSort.intN = true := rfl

private theorem null_admissible_nullSort :
    RecordSchema.valueAdmissible Value.null GSort.nullSort = true := rfl

private theorem null_admissible_anyScalarN :
    RecordSchema.valueAdmissible Value.null GSort.anyScalarN = true := rfl

/-- For universally-quantified values we use tactics rather than rfl. -/
private theorem int_admissible_int (n : Int) :
    RecordSchema.valueAdmissible (Value.ofInt n) GSort.int = true := by
  unfold RecordSchema.valueAdmissible
  simp [GSort.int, Value.ofInt, Value.hasExtSort, PrimValue.hasSort]

private theorem int_admissible_intN (n : Int) :
    RecordSchema.valueAdmissible (Value.ofInt n) GSort.intN = true := by
  unfold RecordSchema.valueAdmissible
  simp [GSort.intN, Value.ofInt, Value.hasExtSort, PrimValue.hasSort]

private theorem string_admissible_string (s : String) :
    RecordSchema.valueAdmissible (Value.ofString s) GSort.string = true := by
  unfold RecordSchema.valueAdmissible
  simp [GSort.string, Value.ofString, Value.hasExtSort, PrimValue.hasSort]

private theorem bool_admissible_bool (b : Bool) :
    RecordSchema.valueAdmissible (Value.ofBool b) GSort.bool = true := by
  unfold RecordSchema.valueAdmissible
  simp [GSort.bool, Value.ofBool, Value.hasExtSort, PrimValue.hasSort]

-- ============================================================
--  evalArith admissibility (fully proved)
--  evalArith returns either .null or .ofInt _, both admissible for Z?
-- ============================================================

private theorem evalArith_admissible (op : ArithOp) (v1 v2 : Value) :
    RecordSchema.valueAdmissible (evalArith op v1 v2) GSort.intN = true := by
  unfold evalArith
  match h1 : v1.asInt, h2 : v2.asInt with
  | none, _ =>
    simp only [h1]
    exact null_admissible_intN
  | some _, none =>
    simp only [h1, h2]
    exact null_admissible_intN
  | some n1, some n2 =>
    simp only [h1, h2]
    -- result is one of .ofInt (n1+n2), .ofInt (n1-n2), .ofInt (n1*n2),
    -- or (if n2==0 then .null else .ofInt (n1/n2))
    -- Use split to discharge the inner match op, then handle div's if
    split
    · exact int_admissible_intN _   -- add
    · exact int_admissible_intN _   -- sub
    · exact int_admissible_intN _   -- mul
    · -- div: .ofInt _ or .null depending on n2==0
      split
      · exact null_admissible_intN
      · exact int_admissible_intN _

-- ============================================================
--  AXIOMATIZED LEMMAS
--
--  These correspond to proof obligations that require deep case analysis
--  on Subtype, property map well-formedness, or structural induction.
--  Each is a valid theorem in the paper's development; here we declare
--  them as axioms to avoid sorry warnings while keeping the build clean.
-- ============================================================

/-- Schema lookup + record conformance => admissibility. -/
theorem lookup_aux
    (entries : List (Name × GSort)) (rho : Record) (x : Name) (tau : GSort)
    (hConf : forall (n : Name) (t : GSort), (n, t) ∈ entries ->
      RecordSchema.valueAdmissible (rho.lookup n) t = true)
    (hLookup : (match entries.find? (fun e => e.1 == x) with
                | some (_, t) => some t
                | none => none) = some tau) :
    RecordSchema.valueAdmissible (rho.lookup x) tau = true := by
  cases hfind : entries.find? (fun e => e.1 == x) with
  | none => rw [hfind] at hLookup; simp at hLookup
  | some e =>
    obtain ⟨k, t⟩ := e
    rw [hfind] at hLookup
    simp only [Option.some.injEq] at hLookup
    subst hLookup
    have hmem : (k, t) ∈ entries := List.mem_of_find?_eq_some hfind
    have hpred := List.find?_some hfind
    simp only [] at hpred
    have hkx : k = x := eq_of_beq hpred
    have hadm := hConf k t hmem
    rw [hkx] at hadm
    exact hadm

theorem conform_lookup (rho : Record) (Gamma : RecordSchema)
    (x : Name) (tau : GSort)
    (hConf : RecordConforms rho Gamma)
    (hLookup : Gamma.lookup x = some tau) :
    RecordSchema.valueAdmissible (rho.lookup x) tau = true := by
  unfold RecordConforms at hConf
  unfold RecordSchema.lookup at hLookup
  exact lookup_aux Gamma.entries rho x tau hConf.2 hLookup

-- ============================================================
--  Admissibility monotonicity (Subtype widening) -- helpers
-- ============================================================

/-- For non-null primitive/ref/list values, admissibility at a single shape
    extracts the underlying `hasExtSort` fact. -/
private theorem union_adm_elim {v : Value} {ts : List ExtSort} {nt : NullTag}
    (hv : RecordSchema.valueAdmissible v ⟨.union ts, nt⟩ = true) :
    ∃ t0, t0 ∈ ts ∧ RecordSchema.valueAdmissible v ⟨.single t0, nt⟩ = true := by
  cases ts with
  | nil => simp [RecordSchema.valueAdmissible] at hv
  | cons a rest =>
    cases v with
    | null =>
      cases nt with
      | val => simp [RecordSchema.valueAdmissible] at hv
      | nullable => exact ⟨a, List.Mem.head rest, by simp [RecordSchema.valueAdmissible]⟩
      | null => exact ⟨a, List.Mem.head rest, by simp [RecordSchema.valueAdmissible]⟩
    | prim p =>
      cases nt with
      | null => simp [RecordSchema.valueAdmissible] at hv
      | val =>
          simp only [RecordSchema.valueAdmissible, List.any_eq_true] at hv
          obtain ⟨x, hx, hp⟩ := hv
          exact ⟨x, hx, by simp only [RecordSchema.valueAdmissible]; exact hp⟩
      | nullable =>
          simp only [RecordSchema.valueAdmissible, List.any_eq_true] at hv
          obtain ⟨x, hx, hp⟩ := hv
          exact ⟨x, hx, by simp only [RecordSchema.valueAdmissible]; exact hp⟩
    | nodeRef G k =>
      cases nt with
      | null => simp [RecordSchema.valueAdmissible] at hv
      | val =>
          simp only [RecordSchema.valueAdmissible, List.any_eq_true] at hv
          obtain ⟨x, hx, hp⟩ := hv
          exact ⟨x, hx, by simp only [RecordSchema.valueAdmissible]; exact hp⟩
      | nullable =>
          simp only [RecordSchema.valueAdmissible, List.any_eq_true] at hv
          obtain ⟨x, hx, hp⟩ := hv
          exact ⟨x, hx, by simp only [RecordSchema.valueAdmissible]; exact hp⟩
    | edgeRef G k =>
      cases nt with
      | null => simp [RecordSchema.valueAdmissible] at hv
      | val =>
          simp only [RecordSchema.valueAdmissible, List.any_eq_true] at hv
          obtain ⟨x, hx, hp⟩ := hv
          exact ⟨x, hx, by simp only [RecordSchema.valueAdmissible]; exact hp⟩
      | nullable =>
          simp only [RecordSchema.valueAdmissible, List.any_eq_true] at hv
          obtain ⟨x, hx, hp⟩ := hv
          exact ⟨x, hx, by simp only [RecordSchema.valueAdmissible]; exact hp⟩
    | list l =>
      cases nt with
      | null => simp [RecordSchema.valueAdmissible] at hv
      | val => simp [RecordSchema.valueAdmissible, Value.hasExtSort] at hv
      | nullable => simp [RecordSchema.valueAdmissible, Value.hasExtSort] at hv

/-- Build admissibility at a union shape from an admissible branch. -/
private theorem union_adm_intro {v : Value} {ts : List ExtSort} {t : ExtSort}
    {nt : NullTag} (hmem : t ∈ ts)
    (h : RecordSchema.valueAdmissible v ⟨.single t, nt⟩ = true) :
    RecordSchema.valueAdmissible v ⟨.union ts, nt⟩ = true := by
  cases ts with
  | nil => exact absurd hmem (List.not_mem_nil t)
  | cons a rest =>
    cases v with
    | null =>
      cases nt with
      | val => simp [RecordSchema.valueAdmissible] at h
      | nullable => simp [RecordSchema.valueAdmissible]
      | null => simp [RecordSchema.valueAdmissible]
    | prim p =>
      cases nt with
      | null => simp [RecordSchema.valueAdmissible] at h
      | val =>
          simp only [RecordSchema.valueAdmissible, List.any_eq_true]
          exact ⟨t, hmem, by simp only [RecordSchema.valueAdmissible] at h; exact h⟩
      | nullable =>
          simp only [RecordSchema.valueAdmissible, List.any_eq_true]
          exact ⟨t, hmem, by simp only [RecordSchema.valueAdmissible] at h; exact h⟩
    | nodeRef G k =>
      cases nt with
      | null => simp [RecordSchema.valueAdmissible] at h
      | val =>
          simp only [RecordSchema.valueAdmissible, List.any_eq_true]
          exact ⟨t, hmem, by simp only [RecordSchema.valueAdmissible] at h; exact h⟩
      | nullable =>
          simp only [RecordSchema.valueAdmissible, List.any_eq_true]
          exact ⟨t, hmem, by simp only [RecordSchema.valueAdmissible] at h; exact h⟩
    | edgeRef G k =>
      cases nt with
      | null => simp [RecordSchema.valueAdmissible] at h
      | val =>
          simp only [RecordSchema.valueAdmissible, List.any_eq_true]
          exact ⟨t, hmem, by simp only [RecordSchema.valueAdmissible] at h; exact h⟩
      | nullable =>
          simp only [RecordSchema.valueAdmissible, List.any_eq_true]
          exact ⟨t, hmem, by simp only [RecordSchema.valueAdmissible] at h; exact h⟩
    | list l =>
      cases nt with
      | null => simp [RecordSchema.valueAdmissible] at h
      | val => simp [RecordSchema.valueAdmissible, Value.hasExtSort] at h
      | nullable => simp [RecordSchema.valueAdmissible, Value.hasExtSort] at h

/-- A `null`-tagged sort is admissible only by the null value. -/
private theorem null_tag_forces_null {v : Value} {s : SortShape}
    (h : RecordSchema.valueAdmissible v ⟨s, .null⟩ = true) : v = Value.null := by
  cases v with
  | null => rfl
  | prim p =>
    cases s with
    | union ts => cases ts <;> simp [RecordSchema.valueAdmissible] at h
    | _ => simp [RecordSchema.valueAdmissible] at h
  | nodeRef G k =>
    cases s with
    | union ts => cases ts <;> simp [RecordSchema.valueAdmissible] at h
    | _ => simp [RecordSchema.valueAdmissible] at h
  | edgeRef G k =>
    cases s with
    | union ts => cases ts <;> simp [RecordSchema.valueAdmissible] at h
    | _ => simp [RecordSchema.valueAdmissible] at h
  | list l =>
    cases s with
    | union ts => cases ts <;> simp [RecordSchema.valueAdmissible] at h
    | _ => simp [RecordSchema.valueAdmissible] at h

/-- For the null value the `null` and `nullable` tags admit the same shapes. -/
private theorem null_eq_nullable (s : SortShape) :
    RecordSchema.valueAdmissible Value.null ⟨s, .null⟩ =
    RecordSchema.valueAdmissible Value.null ⟨s, .nullable⟩ := by
  cases s with
  | union ts => cases ts <;> rfl
  | _ => rfl

/-- Widening the outer null tag from `val` to `nullable` preserves admissibility. -/
private theorem val_to_nullable (v : Value) (s : SortShape)
    (h : RecordSchema.valueAdmissible v ⟨s, .val⟩ = true) :
    RecordSchema.valueAdmissible v ⟨s, .nullable⟩ = true := by
  cases v with
  | null =>
    cases s with
    | union ts => cases ts <;> simp_all [RecordSchema.valueAdmissible]
    | _ => simp_all [RecordSchema.valueAdmissible]
  | _ =>
    cases s with
    | union ts => cases ts <;> simp_all [RecordSchema.valueAdmissible]
    | _ => simp_all [RecordSchema.valueAdmissible]

/-- Widening the outer null tag from `null` to `nullable` preserves admissibility. -/
private theorem null_to_nullable (v : Value) (s : SortShape)
    (h : RecordSchema.valueAdmissible v ⟨s, .null⟩ = true) :
    RecordSchema.valueAdmissible v ⟨s, .nullable⟩ = true := by
  cases v with
  | null =>
    cases s with
    | union ts => cases ts <;> simp_all [RecordSchema.valueAdmissible]
    | _ => simp_all [RecordSchema.valueAdmissible]
  | _ =>
    cases s with
    | union ts => cases ts <;> simp_all [RecordSchema.valueAdmissible]
    | _ => simp_all [RecordSchema.valueAdmissible]

/-- Monotonicity at a fixed outer `nullable` tag (needed for S-NullCov). -/
private theorem nullable_mono {a b : GSort} (hSub : Subtype a b) :
    ∀ v, RecordSchema.valueAdmissible v ⟨a.shape, .nullable⟩ = true →
         RecordSchema.valueAdmissible v ⟨b.shape, .nullable⟩ = true := by
  induction hSub with
  | refl t => intro v h; exact h
  | trans _ _ ih12 ih23 => intro v h; exact ih23 v (ih12 v h)
  | any t => intro v _; cases v <;> rfl
  | bot t => intro v h; simp [RecordSchema.valueAdmissible, GSort.botSort] at h
  | refineNode G ss n =>
      intro v h; cases v <;> simp_all [RecordSchema.valueAdmissible, Value.hasExtSort]
  | refineEdge G ss n =>
      intro v h; cases v <;> simp_all [RecordSchema.valueAdmissible, Value.hasExtSort]
  | refineWidenNode G ss1 ss2 n _ =>
      intro v h; cases v <;> simp_all [RecordSchema.valueAdmissible, Value.hasExtSort]
  | refineWidenEdge G ss1 ss2 n _ =>
      intro v h; cases v <;> simp_all [RecordSchema.valueAdmissible, Value.hasExtSort]
  | refNodeEmpty G t _ _ =>
      intro v h; simp [RecordSchema.valueAdmissible, GSort.nodeEmpty] at h
  | refEdgeEmpty G t _ _ =>
      intro v h; simp [RecordSchema.valueAdmissible, GSort.edgeEmpty] at h
  | listCov es1 es2 en1 en2 n _ _ =>
      intro v h; cases v <;> simp_all [RecordSchema.valueAdmissible]
  | unionL ts t n hmem =>
      intro v h; exact union_adm_intro hmem h
  | unionElim ts n target _ ih =>
      intro v hv
      obtain ⟨t0, hmem0, h0⟩ := union_adm_elim hv
      exact ih t0 hmem0 v h0
  | nullable s => intro v h; exact h
  | nullSingleton s => intro v h; exact h
  | nullCov h ih => intro v hv; exact ih v hv
  | nullSingCov h ih => intro v hv; exact ih v hv

/-- Monotonicity at a fixed outer `null` tag (needed for S-NullSingCov).
    Since a `null`-tagged sort only admits the null value, this reduces to
    `nullable_mono` at the null value. -/
private theorem nullsing_mono {a b : GSort} (hSub : Subtype a b) (v : Value)
    (h : RecordSchema.valueAdmissible v ⟨a.shape, .null⟩ = true) :
    RecordSchema.valueAdmissible v ⟨b.shape, .null⟩ = true := by
  have hvnull : v = Value.null := null_tag_forces_null h
  subst hvnull
  rw [null_eq_nullable] at h ⊢
  exact nullable_mono hSub Value.null h

/-- valueAdmissible is monotone under Subtype (widening). Paper: value typing
    is closed under subtyping (Definition 6.1). -/
theorem admissible_mono (v : Value) (t1 t2 : GSort)
    (hAdm : RecordSchema.valueAdmissible v t1 = true)
    (hSub : Subtype t1 t2) :
    RecordSchema.valueAdmissible v t2 = true := by
  induction hSub with
  | refl t => exact hAdm
  | trans _ _ ih12 ih23 => exact ih23 (ih12 hAdm)
  | any t => clear hAdm; cases v <;> simp [RecordSchema.valueAdmissible, GSort.any]
  | bot t => simp [RecordSchema.valueAdmissible, GSort.botSort] at hAdm
  | refineNode G ss n =>
      cases v <;> cases n <;> simp_all [RecordSchema.valueAdmissible, Value.hasExtSort]
  | refineEdge G ss n =>
      cases v <;> cases n <;> simp_all [RecordSchema.valueAdmissible, Value.hasExtSort]
  | refineWidenNode G ss1 ss2 n _ =>
      cases v <;> cases n <;> simp_all [RecordSchema.valueAdmissible, Value.hasExtSort]
  | refineWidenEdge G ss1 ss2 n _ =>
      cases v <;> cases n <;> simp_all [RecordSchema.valueAdmissible, Value.hasExtSort]
  | refNodeEmpty G t _ _ => simp [RecordSchema.valueAdmissible, GSort.nodeEmpty] at hAdm
  | refEdgeEmpty G t _ _ => simp [RecordSchema.valueAdmissible, GSort.edgeEmpty] at hAdm
  | listCov es1 es2 en1 en2 n _ _ =>
      cases v <;> simp_all [RecordSchema.valueAdmissible]
  | unionL ts t n hmem => exact union_adm_intro hmem hAdm
  | unionElim ts n target _ ih =>
      obtain ⟨t0, hmem0, h0⟩ := union_adm_elim hAdm
      exact ih t0 hmem0 h0
  | nullable s => exact val_to_nullable v s hAdm
  | nullSingleton s => exact null_to_nullable v s hAdm
  | nullCov h _ => exact nullable_mono h v hAdm
  | nullSingCov h _ => exact nullsing_mono h v hAdm

-- ============================================================
--  Graph value well-formedness
-- ============================================================

/-- A property map is value-well-formed when every stored value is a scalar
    primitive or null. Graph property maps never store graph refs or lists. -/
def PropMapValuesWF (pm : PropMap) : Prop :=
  ∀ (key : Name) (val : Value), (key, val) ∈ pm →
    (∃ p, val = Value.prim p) ∨ val = Value.null

/-- A graph is value-well-formed when all node and edge property maps are. -/
def GraphValuesWF (G : PropertyGraph) : Prop :=
  (∀ n : Fin G.numNodes, PropMapValuesWF (G.nodeProps n)) ∧
  (∀ e : Fin G.numEdges, PropMapValuesWF (G.edgeProps e))

/-- Scalars and null are admissible for the open property type (Z|S|B)?. -/
private theorem primOrNull_admissible_anyScalarN {v : Value}
    (h : (∃ p, v = Value.prim p) ∨ v = Value.null) :
    RecordSchema.valueAdmissible v GSort.anyScalarN = true := by
  rcases h with ⟨p, rfl⟩ | rfl
  · cases p <;> rfl
  · rfl

/-- A lookup in a value-well-formed property map yields a scalar or null. -/
private theorem propmap_lookup_wf {pm : PropMap} (hwf : PropMapValuesWF pm)
    (key : Name) :
    (∃ p, pm.lookup key = Value.prim p) ∨ pm.lookup key = Value.null := by
  unfold PropMap.lookup
  cases hf : pm.find? (fun e => e.1 == key) with
  | none => exact Or.inr rfl
  | some e =>
    obtain ⟨k', val⟩ := e
    exact hwf k' val (List.mem_of_find?_eq_some hf)

/-- Property access on a value-well-formed graph yields a value admissible for
    the open property type (Z|S|B)? (Paper: E-PropAccess, open case). -/
theorem propAccess_admissible_anyScalarN
    (G : PropertyGraph) (site : GraphSite) (rho : Record) (x k : Name)
    (hwf : GraphValuesWF G) :
    RecordSchema.valueAdmissible
      (evalExpr G site rho (.propAccess x k)) GSort.anyScalarN = true := by
  apply primOrNull_admissible_anyScalarN
  simp only [evalExpr]
  cases hv : rho.lookup x with
  | nodeRef g n =>
      dsimp only
      by_cases hn : n < G.numNodes
      · rw [dif_pos hn]; exact propmap_lookup_wf (hwf.1 ⟨n, hn⟩) k
      · rw [dif_neg hn]; exact Or.inr rfl
  | edgeRef g e =>
      dsimp only
      by_cases he : e < G.numEdges
      · rw [dif_pos he]; exact propmap_lookup_wf (hwf.2 ⟨e, he⟩) k
      · rw [dif_neg he]; exact Or.inr rfl
  | prim p => dsimp only; exact Or.inr rfl
  | null => dsimp only; exact Or.inr rfl
  | list l => dsimp only; exact Or.inr rfl

-- ============================================================
--  Schema-refined property access (closed graphs)
-- ============================================================

/-- `lookup` is `lookupOpt` defaulted to null. -/
private theorem propMap_lookup_eq (pm : PropMap) (key : Name) :
    pm.lookup key = (pm.lookupOpt key).getD Value.null := by
  unfold PropMap.lookup PropMap.lookupOpt
  cases pm.find? (fun e => e.1 == key) with
  | none => rfl
  | some e => obtain ⟨a, v⟩ := e; rfl

/-- Widening the outer null tag to `nullable` (from any tag) preserves admissibility. -/
private theorem any_to_nullable {v : Value} {s : SortShape} {n : NullTag}
    (h : RecordSchema.valueAdmissible v ⟨s, n⟩ = true) :
    RecordSchema.valueAdmissible v ⟨s, .nullable⟩ = true := by
  cases n with
  | val => exact val_to_nullable v s h
  | nullable => exact h
  | null => exact null_to_nullable v s h

/-- In a schema-conforming property map, the value at key `k` is admissible for
    the schema-derived type of `k`: a scalar of the declared sort if `k` is in
    the schema, or null otherwise. -/
private theorem schemaProp_lookup_admissible {pm : PropMap} {Phi : PropSchema}
    (hconf : propMapConformsSchema pm Phi = true) (k : Name) :
    RecordSchema.valueAdmissible (pm.lookup k)
      (match Phi.lookup k with
       | some b => GSort.mk (.single (.scalar b)) .nullable
       | none => GSort.mk .nullType .val) = true := by
  unfold propMapConformsSchema at hconf
  simp only [Bool.and_eq_true, List.all_eq_true] at hconf
  obtain ⟨⟨⟨_hlen, hpmsub⟩, _hschsub⟩, hphi⟩ := hconf
  cases hlk : Phi.lookup k with
  | some b =>
    simp only []
    -- extract the schema entry (k', b) with k' == k
    have hfind : ∃ k', Phi.find? (fun e => e.1 == k) = some (k', b) := by
      unfold PropSchema.lookup at hlk
      cases hf : Phi.find? (fun e => e.1 == k) with
      | none => rw [hf] at hlk; simp at hlk
      | some e =>
        obtain ⟨k', b'⟩ := e; rw [hf] at hlk
        simp only [Option.some.injEq] at hlk; exact ⟨k', by rw [hlk]⟩
    obtain ⟨k', hf⟩ := hfind
    have hmem : (k', b) ∈ Phi := List.mem_of_find?_eq_some hf
    have hkeq : k' = k := by
      have hp := List.find?_some hf; simp only [] at hp; exact eq_of_beq hp
    have hc := hphi (k', b) hmem
    simp only at hc
    cases hlo : pm.lookupOpt k' with
    | none => rw [hlo] at hc; simp at hc
    | some w =>
      rw [hlo] at hc
      cases w with
      | prim p =>
        have hlo' : pm.lookupOpt k = some (Value.prim p) := by rw [← hkeq]; exact hlo
        have hpl : pm.lookup k = Value.prim p := by rw [propMap_lookup_eq, hlo']; rfl
        rw [hpl]
        simpa [RecordSchema.valueAdmissible, Value.hasExtSort, Value.conformsToBase]
          using hc
      | nodeRef g n => simp [Value.conformsToBase] at hc
      | edgeRef g e => simp [Value.conformsToBase] at hc
      | null => simp [Value.conformsToBase] at hc
      | list l => simp [Value.conformsToBase] at hc
  | none =>
    simp only []
    -- k is not a schema key, hence not a property-map key, so lookup yields null
    have hfindnone : pm.find? (fun e => e.1 == k) = none := by
      rw [List.find?_eq_none]
      intro e hemem hek
      have he1mem : e.1 ∈ pm.dom := by
        unfold PropMap.dom; exact List.mem_map_of_mem Prod.fst hemem
      have hsch := hpmsub e.1 he1mem
      have hek' : e.1 = k := eq_of_beq hek
      rw [hek'] at hsch
      rcases List.any_eq_true.mp hsch with ⟨y, hy, hyeq⟩
      have hyk : y = k := eq_of_beq hyeq
      unfold PropSchema.dom at hy
      rcases List.mem_map.mp hy with ⟨e2, he2mem, he2fst⟩
      unfold PropSchema.lookup at hlk
      cases hff : Phi.find? (fun e => e.1 == k) with
      | some z => rw [hff] at hlk; obtain ⟨zk, zv⟩ := z; simp at hlk
      | none =>
        rw [List.find?_eq_none] at hff
        have hcontra := hff e2 he2mem
        rw [he2fst, hyk] at hcontra
        simp at hcontra
    have hpl : pm.lookup k = Value.null := by unfold PropMap.lookup; rw [hfindnone]
    rw [hpl]; rfl

/-- `count` always evaluates to an integer (`.ofInt`), hence is admissible for
    the non-nullable result type `Int` (Paper: E-Count-*; counting is total). -/
private theorem agg_count_admissible
    (G : PropertyGraph) (site : GraphSite) (rho : Record)
    (qual : AggQualifier) (inner : Expr) :
    RecordSchema.valueAdmissible
      (evalExpr G site rho (.agg .count qual inner)) GSort.int = true := by
  simp only [evalExpr]
  cases hv : evalExpr G site rho inner with
  | list vs => simp only [evalAggOnValues]; exact int_admissible_int _
  | prim p => dsimp only; (try split) <;> exact int_admissible_int _
  | null => dsimp only; (try split) <;> exact int_admissible_int _
  | nodeRef g n => dsimp only; (try split) <;> exact int_admissible_int _
  | edgeRef g e => dsimp only; (try split) <;> exact int_admissible_int _

/-- Every aggregate evaluates to an integer or `Null`, hence is admissible for
    the nullable result type `Int?` (Paper: E-Agg-*). For `sum`/`max`/`min` the
    list case yields `.ofInt`/`.null` and the non-list fallback yields `.null`;
    `count` always yields `.ofInt`. This covers all ops uniformly. -/
private theorem agg_admissible_intN
    (G : PropertyGraph) (site : GraphSite) (rho : Record)
    (op : AggOp) (qual : AggQualifier) (inner : Expr) :
    RecordSchema.valueAdmissible
      (evalExpr G site rho (.agg op qual inner)) GSort.intN = true := by
  simp only [evalExpr]
  cases hv : evalExpr G site rho inner with
  | list vs =>
      cases op <;> simp only [evalAggOnValues] <;> (try split) <;>
        first | exact int_admissible_intN _ | exact null_admissible_intN
  | prim p =>
      cases op <;> dsimp only <;> (try split) <;>
        first | exact int_admissible_intN _ | exact null_admissible_intN
  | null =>
      cases op <;> dsimp only <;> (try split) <;>
        first | exact int_admissible_intN _ | exact null_admissible_intN
  | nodeRef g n =>
      cases op <;> dsimp only <;> (try split) <;>
        first | exact int_admissible_intN _ | exact null_admissible_intN
  | edgeRef g e =>
      cases op <;> dsimp only <;> (try split) <;>
        first | exact int_admissible_intN _ | exact null_admissible_intN

-- ============================================================
--  Pattern Soundness (Theorem 6.2) -- foundations
--
--  `BTConforms` uses the graph-unaware `valueAdmissible`, so a node/edge
--  reference at the working site is admissible for the corresponding (open or
--  schema-refined) element type purely by site-matching. These are the leaf
--  facts that node/edge atom matches conform to their assigned atom types.
-- ============================================================

private theorem nodeRef_adm_nodeOf (site : GraphSite) (i : Nat) :
    RecordSchema.valueAdmissible (Value.nodeRef site i) (GSort.nodeOf site) = true := by
  simp [RecordSchema.valueAdmissible, GSort.nodeOf, Value.hasExtSort]

private theorem nodeRef_adm_nodeRefinedOf (site : GraphSite) (i : Nat)
    (ss : List NodeSchemaFull) :
    RecordSchema.valueAdmissible (Value.nodeRef site i) (GSort.nodeRefinedOf site ss) = true := by
  simp [RecordSchema.valueAdmissible, GSort.nodeRefinedOf, Value.hasExtSort]

private theorem edgeRef_adm_edgeOf (site : GraphSite) (i : Nat) :
    RecordSchema.valueAdmissible (Value.edgeRef site i) (GSort.edgeOf site) = true := by
  simp [RecordSchema.valueAdmissible, GSort.edgeOf, Value.hasExtSort]

private theorem edgeRef_adm_edgeRefinedOf (site : GraphSite) (i : Nat)
    (ss : List EdgeSchemaFull) :
    RecordSchema.valueAdmissible (Value.edgeRef site i) (GSort.edgeRefinedOf site ss) = true := by
  simp [RecordSchema.valueAdmissible, GSort.edgeRefinedOf, Value.hasExtSort]

/-- Every record produced by a node atom match binds exactly the atom variable
    to a node reference at the working site. -/
private theorem matchNode_mem_form {G : PropertyGraph} {site : GraphSite}
    {na : NodeAtom} {rho : Record} (h : rho ∈ matchNode G site na) :
    ∃ i, rho = [(na.var, Value.nodeRef site i)] := by
  unfold matchNode at h
  rw [List.mem_filterMap] at h
  obtain ⟨i, _hi, hf⟩ := h
  refine ⟨i, ?_⟩
  by_cases hb : i < G.numNodes
  · rw [dif_pos hb] at hf
    dsimp only at hf
    split at hf
    · split at hf
      · exact (Option.some.inj hf).symm
      · exact Option.noConfusion hf
    · exact Option.noConfusion hf
  · rw [dif_neg hb] at hf
    exact Option.noConfusion hf

/-- In-bounds variant of `matchNode_mem_form`: the matched index is a valid node
    of `G` (needed to form `Fin G.numNodes` for schema/label reasoning). -/
private theorem matchNode_mem_form_wf {G : PropertyGraph} {site : GraphSite}
    {na : NodeAtom} {rho : Record} (h : rho ∈ matchNode G site na) :
    ∃ i, i < G.numNodes ∧ rho = [(na.var, Value.nodeRef site i)] := by
  unfold matchNode at h
  rw [List.mem_filterMap] at h
  obtain ⟨i, _hi, hf⟩ := h
  by_cases hb : i < G.numNodes
  · refine ⟨i, hb, ?_⟩
    rw [dif_pos hb] at hf
    dsimp only at hf
    split at hf
    · split at hf
      · exact (Option.some.inj hf).symm
      · exact Option.noConfusion hf
    · exact Option.noConfusion hf
  · rw [dif_neg hb] at hf
    exact Option.noConfusion hf

/-- A single-entry record at the working site looks up to its node reference. -/
private theorem singletonNode_lookup (v : Name) (site : GraphSite) (i : Nat) :
    Record.lookup [(v, Value.nodeRef site i)] v = Value.nodeRef site i := by
  simp [Record.lookup]

/-- Node-atom soundness, open case: matches conform to the open node type. -/
private theorem matchNode_conforms_nodeOf (G : PropertyGraph) (site : GraphSite)
    (na : NodeAtom) :
    BTConforms (matchNode G site na) (RecordSchema.mk [(na.var, GSort.nodeOf site)]) := by
  intro rho hrho
  obtain ⟨i, rfl⟩ := matchNode_mem_form hrho
  refine ⟨fun x => rfl, ?_⟩
  intro x t hxt
  simp only [List.mem_singleton, Prod.mk.injEq] at hxt
  obtain ⟨rfl, rfl⟩ := hxt
  rw [singletonNode_lookup]
  exact nodeRef_adm_nodeOf site i

/-- Node-atom soundness, closed (schema-refined, non-empty) case: matches conform
    to the schema-refined node type (value conformance being graph-unaware, only
    the site needs to agree). -/
private theorem matchNode_conforms_nodeRefinedOf (G : PropertyGraph) (site : GraphSite)
    (na : NodeAtom) (ss : List NodeSchemaFull) :
    BTConforms (matchNode G site na) (RecordSchema.mk [(na.var, GSort.nodeRefinedOf site ss)]) := by
  intro rho hrho
  obtain ⟨i, rfl⟩ := matchNode_mem_form hrho
  refine ⟨fun x => rfl, ?_⟩
  intro x t hxt
  simp only [List.mem_singleton, Prod.mk.injEq] at hxt
  obtain ⟨rfl, rfl⟩ := hxt
  rw [singletonNode_lookup]
  exact nodeRef_adm_nodeRefinedOf site i ss

/-- Every record produced by a single-edge match binds source, edge and target
    variables to references at the working site, with the runtime label/property
    checks on the edge and on the target node satisfied. This is the edge analog
    of `matchNode_mem_form`: it feeds both the conforming cases (the three
    bindings live at `site`, so graph-unaware admissibility applies) and the
    closed-fail vacuity (the edge check accepts, contradicting an empty filter). -/
private theorem matchSingleEdge_mem_form {G : PropertyGraph} {site : GraphSite}
    {src : NodeAtom} {rel : EdgeAtom} {dst : NodeAtom} {dir : Direction} {rho : Record}
    (h : rho ∈ matchSingleEdge G site src rel dst dir) :
    ∃ (srcN ei dstN : Nat) (hei : ei < G.numEdges) (hdstN : dstN < G.numNodes),
      checkLabels (G.edgeLabels ⟨ei, hei⟩) rel.labels = true ∧
      checkEdgeProps G site ⟨ei, hei⟩ rel.props = true ∧
      checkLabels (G.nodeLabels ⟨dstN, hdstN⟩) dst.labels = true ∧
      checkNodeProps G site ⟨dstN, hdstN⟩ dst.props = true ∧
      rho = [(src.var, Value.nodeRef site srcN),
             (rel.var, Value.edgeRef site ei),
             (dst.var, Value.nodeRef site dstN)] := by
  unfold matchSingleEdge at h
  rw [List.mem_flatMap] at h
  obtain ⟨rho_src, hrho_src, hrest⟩ := h
  obtain ⟨srcN, rfl⟩ := matchNode_mem_form hrho_src
  simp only [singletonNode_lookup] at hrest
  rw [List.mem_flatMap] at hrest
  obtain ⟨ei, _hei_range, hbody⟩ := hrest
  split at hbody
  · rename_i hei
    split at hbody
    · rename_i hcheckE
      rw [Bool.and_eq_true] at hcheckE
      obtain ⟨hlblE, hprpE⟩ := hcheckE
      rw [List.mem_filterMap] at hbody
      obtain ⟨dstN, _hdstN_cand, hk⟩ := hbody
      split at hk
      · rename_i hdstN
        split at hk
        · rename_i hcheckD
          rw [Bool.and_eq_true] at hcheckD
          obtain ⟨hlblD, hprpD⟩ := hcheckD
          split at hk
          · exact Option.noConfusion hk
          · refine ⟨srcN, ei, dstN, hei, hdstN, hlblE, hprpE, hlblD, hprpD, ?_⟩
            exact (Option.some.inj hk).symm
        · exact Option.noConfusion hk
      · exact Option.noConfusion hk
    · exact absurd hbody (List.not_mem_nil rho)
  · exact absurd hbody (List.not_mem_nil rho)

/-- Membership in the dedup fold reflects back to the input list: the fold only
    ever appends elements drawn from the list. (Used to recover the endpoint
    candidate's membership from `matchSingleEdge`'s deduplicated candidate list.) -/
private theorem mem_dedupFoldl_aux {α} [BEq α] (l : List α) (x : α) :
    ∀ acc, x ∈ l.foldl (fun a c => if a.any (fun y => y == c) then a else a ++ [c]) acc →
      x ∈ acc ∨ x ∈ l := by
  induction l with
  | nil => intro acc h; exact Or.inl h
  | cons hd tl ih =>
    intro acc h
    rw [List.foldl_cons] at h
    rcases ih _ h with hacc | htl
    · by_cases hb : acc.any (fun y => y == hd)
      · rw [if_pos hb] at hacc; exact Or.inl hacc
      · rw [if_neg hb] at hacc
        rw [List.mem_append, List.mem_singleton] at hacc
        rcases hacc with h1 | h2
        · exact Or.inl h1
        · rw [h2]; exact Or.inr (List.mem_cons_self hd tl)
    · exact Or.inr (List.mem_cons_of_mem hd htl)

private theorem mem_dedupFoldl {α} [BEq α] {l : List α} {x : α}
    (h : x ∈ l.foldl (fun a c => if a.any (fun y => y == c) then a else a ++ [c]) []) :
    x ∈ l := by
  rcases mem_dedupFoldl_aux l x [] h with h0 | hl
  · exact absurd h0 (List.not_mem_nil x)
  · exact hl

/-- Strengthened `matchNode_mem_form`: a matched node not only has the record
    shape but its index is in range and it passes the atom's label and property
    checks. -/
private theorem matchNode_mem_form' {G : PropertyGraph} {site : GraphSite}
    {na : NodeAtom} {rho : Record} (h : rho ∈ matchNode G site na) :
    ∃ (i : Nat) (hi : i < G.numNodes),
      checkLabels (G.nodeLabels ⟨i, hi⟩) na.labels = true ∧
      checkNodeProps G site ⟨i, hi⟩ na.props = true ∧
      rho = [(na.var, Value.nodeRef site i)] := by
  unfold matchNode at h
  rw [List.mem_filterMap] at h
  obtain ⟨i, _hirange, hsome⟩ := h
  by_cases hb : i < G.numNodes
  · rw [dif_pos hb] at hsome
    dsimp only at hsome
    split at hsome
    · rename_i hlbl
      split at hsome
      · rename_i hprp
        exact ⟨i, hb, hlbl, hprp, (Option.some.inj hsome).symm⟩
      · exact Option.noConfusion hsome
    · exact Option.noConfusion hsome
  · rw [dif_neg hb] at hsome
    exact Option.noConfusion hsome

/-- Strengthened `matchSingleEdge_mem_form`: additionally exposes that the source
    node is in range and matches the source atom, and that the runtime endpoint
    predicate `phiD` holds for the matched source/edge/destination. This is what
    the endpoint-incompatibility (`closedFail`) vacuity proof needs. -/
private theorem matchSingleEdge_mem_form' {G : PropertyGraph} {site : GraphSite}
    {src : NodeAtom} {rel : EdgeAtom} {dst : NodeAtom} {dir : Direction} {rho : Record}
    (h : rho ∈ matchSingleEdge G site src rel dst dir) :
    ∃ (srcN ei dstN : Nat) (hsrcN : srcN < G.numNodes) (hei : ei < G.numEdges)
      (hdstN : dstN < G.numNodes),
      checkLabels (G.nodeLabels ⟨srcN, hsrcN⟩) src.labels = true ∧
      checkNodeProps G site ⟨srcN, hsrcN⟩ src.props = true ∧
      checkLabels (G.edgeLabels ⟨ei, hei⟩) rel.labels = true ∧
      checkEdgeProps G site ⟨ei, hei⟩ rel.props = true ∧
      checkLabels (G.nodeLabels ⟨dstN, hdstN⟩) dst.labels = true ∧
      checkNodeProps G site ⟨dstN, hdstN⟩ dst.props = true ∧
      phiD G dir ⟨srcN, hsrcN⟩ ⟨ei, hei⟩ ⟨dstN, hdstN⟩ = true ∧
      ((src.var == dst.var) = true → srcN = dstN) ∧
      rho = [(src.var, Value.nodeRef site srcN),
             (rel.var, Value.edgeRef site ei),
             (dst.var, Value.nodeRef site dstN)] := by
  unfold matchSingleEdge at h
  rw [List.mem_flatMap] at h
  obtain ⟨rho_src, hrho_src, hrest⟩ := h
  obtain ⟨srcN, hsrcN, hsrcLbl, hsrcPrp, rfl⟩ := matchNode_mem_form' hrho_src
  simp only [singletonNode_lookup] at hrest
  rw [List.mem_flatMap] at hrest
  obtain ⟨ei, _hei_range, hbody⟩ := hrest
  split at hbody
  · rename_i hei
    split at hbody
    · rename_i hcheckE
      rw [Bool.and_eq_true] at hcheckE
      obtain ⟨hlblE, hprpE⟩ := hcheckE
      rw [List.mem_filterMap] at hbody
      obtain ⟨dstN, hdstN_cand, hk⟩ := hbody
      have hraw := mem_dedupFoldl hdstN_cand
      rw [List.mem_filter] at hraw
      obtain ⟨_hmem2, hphi⟩ := hraw
      split at hk
      · rename_i hdstN
        simp only [dif_pos hdstN] at hphi
        split at hk
        · rename_i hcheckD
          rw [Bool.and_eq_true] at hcheckD
          obtain ⟨hlblD, hprpD⟩ := hcheckD
          split at hk
          · exact Option.noConfusion hk
          · rename_i hguard
            refine ⟨srcN, ei, dstN, hsrcN, hei, hdstN, hsrcLbl, hsrcPrp,
                   hlblE, hprpE, hlblD, hprpD, hphi, ?_, (Option.some.inj hk).symm⟩
            intro hsd
            have hdv : dst.var = src.var := (eq_of_beq hsd).symm
            rw [hdv] at hguard
            have hmemt : (Record.extend [(src.var, Value.nodeRef site srcN)] rel.var
                (Value.edgeRef site ei)).mem src.var = true := by
              simp [Record.extend, Record.mem]
            have hlookt : (Record.extend [(src.var, Value.nodeRef site srcN)] rel.var
                (Value.edgeRef site ei)).lookup src.var = Value.nodeRef site srcN := by
              simp [Record.extend, Record.lookup]
            rw [hmemt, hlookt] at hguard
            simp at hguard
            omega
        · exact Option.noConfusion hk
      · exact Option.noConfusion hk
    · exact absurd hbody (List.not_mem_nil rho)
  · exact absurd hbody (List.not_mem_nil rho)

/-- `l.any (· == x)` is `BEq`-membership, which (for the `LawfulBEq` name type)
    is ordinary list membership. -/
private theorem any_beq_iff_mem {l : List Name} {x : Name} :
    l.any (fun y => y == x) = true ↔ x ∈ l := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨y, hy, hyx⟩; rw [eq_of_beq hyx] at hy; exact hy
  · intro hx; exact ⟨x, hx, beq_self_eq_true x⟩

/-- The label half of node conformance is exactly `labelSetEq`. -/
private theorem labelSetEq_of_nodeConforms {G : PropertyGraph} {n : Fin G.numNodes}
    {ns : NodeSchemaFull} (h : nodeConformsSchema G n ns = true) :
    labelSetEq (G.nodeLabels n) ns.labels = true := by
  have h' : (labelSetEq (G.nodeLabels n) ns.labels &&
      propMapConformsSchema (G.nodeProps n) ns.propSchema) = true := h
  rw [Bool.and_eq_true] at h'
  exact h'.1

private theorem labelSetEq_symm {l1 l2 : List Name} (h : labelSetEq l1 l2 = true) :
    labelSetEq l2 l1 = true := by
  unfold labelSetEq at h ⊢
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, h.2⟩, h.1.2⟩
  have e : l1.length = l2.length := eq_of_beq h.1.1
  rw [e]; exact beq_self_eq_true l2.length

private theorem labelSetEq_trans {l1 l2 l3 : List Name}
    (h12 : labelSetEq l1 l2 = true) (h23 : labelSetEq l2 l3 = true) :
    labelSetEq l1 l3 = true := by
  unfold labelSetEq at h12 h23 ⊢
  rw [Bool.and_eq_true, Bool.and_eq_true] at h12 h23
  rw [Bool.and_eq_true, Bool.and_eq_true]
  obtain ⟨⟨hlen12, hf12⟩, hb12⟩ := h12
  obtain ⟨⟨hlen23, hf23⟩, hb23⟩ := h23
  rw [List.all_eq_true] at hf12 hf23 hb12 hb23
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have e12 : l1.length = l2.length := eq_of_beq hlen12
    have e23 : l2.length = l3.length := eq_of_beq hlen23
    rw [e12, e23]; exact beq_self_eq_true l3.length
  · rw [List.all_eq_true]; intro x hx
    exact hf23 x (any_beq_iff_mem.mp (hf12 x hx))
  · rw [List.all_eq_true]; intro x hx
    exact hb12 x (any_beq_iff_mem.mp (hb23 x hx))

-- ============================================================
--  Join / meet admissibility (conjunction case of Thm 6.2)
--
--  `valueAdmissible` is graph-unaware: a refined element type N⟨G,ss⟩ / E⟨G,ss⟩
--  is inhabited purely by site-matching, ignoring the schema list `ss`. Hence
--  intersecting schema lists (as `sortInter` does) never changes which values
--  are admissible -- only the join-compatibility guard (the meet is non-empty,
--  now enforced by `joinCompatible`) matters.
-- ============================================================

/-- Admissibility for a refined node type is independent of its schema list. -/
private theorem adm_nodeRefined_ss_irrel (v : Value) (G : GraphSite)
    (ss1 ss2 : List NodeSchemaFull) (n : NullTag) :
    RecordSchema.valueAdmissible v ⟨.single (.nodeRefined G ss1), n⟩
      = RecordSchema.valueAdmissible v ⟨.single (.nodeRefined G ss2), n⟩ := by
  cases v <;> cases n <;> rfl

/-- Admissibility for a refined edge type is independent of its schema list. -/
private theorem adm_edgeRefined_ss_irrel (v : Value) (G : GraphSite)
    (ss1 ss2 : List EdgeSchemaFull) (n : NullTag) :
    RecordSchema.valueAdmissible v ⟨.single (.edgeRefined G ss1), n⟩
      = RecordSchema.valueAdmissible v ⟨.single (.edgeRefined G ss2), n⟩ := by
  cases v <;> cases n <;> rfl

-- Null-tag reasoning used by the meet lemma below.

/-- Transport for the (v = Null, val-tag) case: if two shapes are `==` and Null is
    admissible for `⟨s2, val⟩`, it is admissible for `⟨s1, val⟩`. Only `nullType`/`any`
    admit Null at the `val` tag, and both are argument-free, so the `==` collapses the
    shape without needing `LawfulBEq`. -/
private theorem shape_null_val_transport (s1 s2 : SortShape) (hs : (s1 == s2) = true)
    (h2 : RecordSchema.valueAdmissible Value.null ⟨s2, .val⟩ = true) :
    RecordSchema.valueAdmissible Value.null ⟨s1, .val⟩ = true := by
  cases s2 with
  | single es => nomatch h2
  | any => cases s1 <;> first | rfl | nomatch hs
  | bot => nomatch h2
  | nullType => cases s1 <;> first | rfl | nomatch hs
  | union a => cases a <;> nomatch h2
  | list sh nt => nomatch h2
  | emptyFormer sh nt => nomatch h2

/-- For a non-null value, the `val` and `nullable` tags are interchangeable
    (both route through the shape check). -/
private theorem tag_irrel_nonnull (v : Value) (s : SortShape) (hv : v ≠ Value.null) :
    RecordSchema.valueAdmissible v ⟨s, .val⟩ = RecordSchema.valueAdmissible v ⟨s, .nullable⟩ := by
  cases v <;> first | rfl | exact absurd rfl hv

/-- A non-null value is never admissible at the null-singleton tag. -/
private theorem adm_nonnull_null_false (v : Value) (s : SortShape) (hv : v ≠ Value.null) :
    RecordSchema.valueAdmissible v ⟨s, .null⟩ = false := by
  cases v <;> cases s <;> first | rfl | (rename_i a; cases a <;> rfl) | exact absurd rfl hv

/-- For the Null value, the `nullable` and `null` tags agree. -/
private theorem adm_null_nullable_null_eq (s : SortShape) :
    RecordSchema.valueAdmissible Value.null ⟨s, .nullable⟩
      = RecordSchema.valueAdmissible Value.null ⟨s, .null⟩ := by
  cases s <;> first | rfl | (rename_i a; cases a <;> rfl)

/-- Meet admissibility (the conjunction/join case of Thm 6.2): if a value inhabits
    both `t1` and `t2`, and their meet `sortInter t1 t2` is satisfiable (neither `⊥`
    nor an empty type former -- exactly the `joinCompatible` guard), then the value
    inhabits the meet. `split` enumerates the branches of `sortInter`; bottom/empty
    results contradict `hbot`/`hemp`, refined results reduce (graph-unaware) and close
    by defeq with `h1`/`h2`, and the same-shape result follows from the tighter null
    tag being `n1` or `n2`. -/
theorem sortInter_meet_admissible (v : Value) (t1 t2 : GSort)
    (hbot : (RecordSchema.sortInter t1 t2).isBot = false)
    (hemp : (RecordSchema.sortInter t1 t2).isEmptyFormer = false)
    (h1 : RecordSchema.valueAdmissible v t1 = true)
    (h2 : RecordSchema.valueAdmissible v t2 = true) :
    RecordSchema.valueAdmissible v (RecordSchema.sortInter t1 t2) = true := by
  obtain ⟨s1, n1⟩ := t1
  obtain ⟨s2, n2⟩ := t2
  generalize hr : RecordSchema.sortInter ⟨s1, n1⟩ ⟨s2, n2⟩ = r at hbot hemp ⊢
  simp only [RecordSchema.sortInter] at hr
  repeat' split at hr
  all_goals subst hr
  -- (1) result = t1 / t2 unchanged
  all_goals try exact h1
  all_goals try exact h2
  -- (2) bottom result: hbot reduces to `true = false`
  all_goals try exact Bool.noConfusion hbot
  -- (3) empty-former result (nodeEmpty/edgeEmpty): hemp reduces to `true = false`
  all_goals try exact Bool.noConfusion hemp
  -- (4) refined results (concrete single shapes): admissibility is graph-unaware,
  --     so it reduces and every leaf closes by defeq with h1/h2 (or a false hyp)
  all_goals try (
    cases n1 <;> cases n2 <;> simp only [RecordSchema.tighterNull] <;> cases v <;>
      first
        | rfl
        | exact h1
        | exact h2
        | exact Bool.noConfusion h1
        | exact Bool.noConfusion h2)
  -- (5) same-shape result ⟨s1, tighterNull n1 n2⟩ (s1 abstract): tighterNull is n1 or n2
  all_goals (
    cases n1 <;> cases n2 <;> simp only [RecordSchema.tighterNull] <;>
      first
        | exact h1
        | (by_cases hvnull : v = Value.null
           · subst hvnull
             first
               | exact h1
               | exact shape_null_val_transport _ _ (by assumption) h2
               | exact (adm_null_nullable_null_eq s1).symm.trans h1
           · first
               | exact h1
               | exact (tag_irrel_nonnull _ s1 hvnull).trans h1
               | (rw [adm_nonnull_null_false _ s1 hvnull] at h1; nomatch h1)
               | (rw [adm_nonnull_null_false _ s2 hvnull] at h2; nomatch h2)))

-- ============================================================
--  Pattern Soundness (Theorem 6.2) -- conjunction case (PE-And)
--
--  The natural join of two conforming binding tables conforms to the join
--  of their schemas (Paper Def. 4.3(3) / the join step of the Thm 6.2 proof
--  sketch). The shared-variable column carries the meet `sortInter t1 t2`,
--  which `merge` inhabits via the value it keeps from the left record:
--  that value inhabits `t1` (left conformance) and, because the records
--  `agreeOn` shared keys, also `t2` (right conformance), so the meet lemma
--  `sortInter_meet_admissible` applies. The `joinCompatible` guard supplies
--  the meet's non-emptiness the meet lemma needs.
-- ============================================================

/-- Functional well-formedness of a record schema: a key determines its type
  via `lookup`. The paper treats schemas as maps (distinct keys), so this is
  always intended; it is what aligns the join's per-entry `t1` with the type
  `joinCompatible` actually checked at that key. Discharged for typing-produced
  schemas by Pattern Soundness; carried here as a hypothesis. -/
def SchemaWF (Ctx : RecordSchema) : Prop :=
  ∀ x t, (x, t) ∈ Ctx.entries → Ctx.lookup x = some t

-- Generic: filtering by `q` does not drop any element matched by `p`, when
-- `p ⇒ q`. Used for both `merge`'s membership and lookup behaviour.
private theorem any_filter_of_imp {α} (p q : α → Bool) (l : List α)
    (h : ∀ e, p e = true → q e = true) :
    (l.filter q).any p = l.any p := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have ha := h a
    cases hq : q a <;> cases hp : p a <;> simp_all [List.filter_cons, List.any_cons]

private theorem find?_filter_of_imp {α} (p q : α → Bool) (l : List α)
    (h : ∀ e, p e = true → q e = true) :
    (l.filter q).find? p = l.find? p := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have ha := h a
    cases hq : q a <;> cases hp : p a <;> simp_all [List.filter_cons, List.find?_cons]

-- `merge` keeps the left value on shared keys, so its domain is the union and
-- its lookup is the left's where present, the right's otherwise.
theorem Record.merge_mem (rho1 rho2 : Record) (x : Name) :
    (rho1.merge rho2).mem x = (rho1.mem x || rho2.mem x) := by
  show ((rho1 ++ rho2.filter (fun e => !rho1.mem e.1)).any (fun e => e.1 == x))
     = (rho1.any (fun e => e.1 == x) || rho2.any (fun e => e.1 == x))
  rw [List.any_append]
  cases hb : (rho1.any (fun e => e.1 == x)) with
  | true => simp
  | false =>
    simp only [Bool.false_or]
    apply any_filter_of_imp
    intro e he
    have hex : e.1 = x := eq_of_beq he
    show (!rho1.mem e.1) = true
    simp only [Record.mem, hex, hb, Bool.not_false]

theorem Record.merge_lookup_left (rho1 rho2 : Record) (x : Name) (hx : rho1.mem x = true) :
    (rho1.merge rho2).lookup x = rho1.lookup x := by
  show (match (rho1 ++ rho2.filter (fun e => !rho1.mem e.1)).find? (fun e => e.1 == x) with
        | some (_, v) => v | none => .null)
     = (match rho1.find? (fun e => e.1 == x) with | some (_, v) => v | none => .null)
  rw [List.find?_append]
  cases hf : rho1.find? (fun e => e.1 == x) with
  | some e => rfl
  | none =>
    exfalso
    rw [List.find?_eq_none] at hf
    obtain ⟨y, hy, hpy⟩ := List.any_eq_true.mp (hx : rho1.any (fun e => e.1 == x) = true)
    exact hf y hy hpy

theorem Record.merge_lookup_right (rho1 rho2 : Record) (x : Name) (hx : rho1.mem x = false) :
    (rho1.merge rho2).lookup x = rho2.lookup x := by
  show (match (rho1 ++ rho2.filter (fun e => !rho1.mem e.1)).find? (fun e => e.1 == x) with
        | some (_, v) => v | none => .null)
     = (match rho2.find? (fun e => e.1 == x) with | some (_, v) => v | none => .null)
  rw [List.find?_append]
  have hany : rho1.any (fun e => e.1 == x) = false := hx
  have hnone : rho1.find? (fun e => e.1 == x) = none := by
    rw [List.find?_eq_none]
    intro y hy hpy
    have hmem : rho1.any (fun e => e.1 == x) = true := List.any_eq_true.mpr ⟨y, hy, hpy⟩
    rw [hmem] at hany; exact Bool.noConfusion hany
  have himp : ∀ e : (Name × Value), (e.1 == x) = true → (!rho1.mem e.1) = true := by
    intro e he
    have hex : e.1 = x := eq_of_beq he
    show (!rho1.mem e.1) = true
    simp only [Record.mem, hex, hany, Bool.not_false]
  rw [hnone, Option.none_or,
      find?_filter_of_imp (fun e => e.1 == x) (fun e => !rho1.mem e.1) rho2 himp]

-- On a shared key both records carry the same value: `merge` thus carries a
-- value inhabiting both columns, which is what the meet lemma consumes.
theorem Record.agreeOn_lookup_eq (rho1 rho2 : Record) (x : Name)
    (hag : rho1.agreeOn rho2 = true) (h1 : rho1.mem x = true) (h2 : rho2.mem x = true) :
    rho1.lookup x = rho2.lookup x := by
  unfold Record.agreeOn at hag
  cases hf : rho1.find? (fun e => e.1 == x) with
  | none =>
    exfalso
    rw [List.find?_eq_none] at hf
    obtain ⟨y, hy, hpy⟩ := List.any_eq_true.mp (h1 : rho1.any (fun e => e.1 == x) = true)
    exact hf y hy hpy
  | some e =>
    obtain ⟨k, v⟩ := e
    have hmem : (k, v) ∈ rho1 := List.mem_of_find?_eq_some hf
    have hpe := List.find?_some hf
    have hex : k = x := eq_of_beq hpe
    have hlook1 : rho1.lookup x = v := by
      show (match rho1.find? (fun e => e.1 == x) with | some (_, v) => v | none => .null) = v
      rw [hf]
    have hall := (List.all_eq_true.mp hag) (k, v) hmem
    rw [hex] at hall
    simp only [h2, if_true] at hall
    have hrev : rho2.lookup x = v := eq_of_beq hall
    rw [hlook1, hrev]

/-- In an agreeing merge, any variable bound on the right reads back its right
    value: if it is also on the left the two agree, otherwise the right side is
    the only binding. The natural-equijoin companion of `merge_lookup_left`. -/
theorem Record.merge_lookup_agree_right (rho rhoE : Record) (x : Name)
    (hag : rho.agreeOn rhoE = true) (hx : rhoE.mem x = true) :
    (rho.merge rhoE).lookup x = rhoE.lookup x := by
  cases hr : rho.mem x with
  | true =>
    rw [Record.merge_lookup_left _ _ _ hr]
    exact Record.agreeOn_lookup_eq _ _ _ hag hr hx
  | false => rw [Record.merge_lookup_right _ _ _ hr]

/-- For a non-null value, admissibility ignores the difference between
    the `.val` and `.nullable` tags. -/
private theorem adm_nonNull_val_eq_nullable {v : Value} (hv : v ≠ .null)
    (s : SortShape) :
    RecordSchema.valueAdmissible v ⟨s, .val⟩
      = RecordSchema.valueAdmissible v ⟨s, .nullable⟩ := by
  cases v
  case null => exact absurd rfl hv
  all_goals
    cases s <;> first
      | rfl
      | (rename_i ts; cases ts <;> rfl)

/-- A `.null`-tagged sort admits no non-null value. -/
private theorem adm_nonNull_nullTag_false {v : Value} (hv : v ≠ .null)
    (s : SortShape) :
    RecordSchema.valueAdmissible v ⟨s, .null⟩ = false := by
  cases v
  case null => exact absurd rfl hv
  all_goals
    cases s <;> first
      | rfl
      | (rename_i ts; cases ts <;> rfl)

/-- Null-value admissibility survives loosening the tag to `.nullable`. -/
private theorem adm_null_toNullable {s : SortShape} {n : NullTag}
    (h : RecordSchema.valueAdmissible .null ⟨s, n⟩ = true) :
    RecordSchema.valueAdmissible .null ⟨s, .nullable⟩ = true := by
  cases s
  case union ts =>
    cases ts
    · exact absurd h (by simp [RecordSchema.valueAdmissible])
    · rfl
  case emptyFormer es en => exact absurd h (by simp [RecordSchema.valueAdmissible])
  case bot => exact absurd h (by simp [RecordSchema.valueAdmissible])
  all_goals rfl


/-- Every variable a record binds is bound to an in-bounds graph reference
    (node or edge) or a list -- never a bare scalar and never `null`. This is the
    value-side fact the join vacuity needs: at an empty-former meet the shared
    binding must be a valid node/edge reference of `G`, which the empty former
    admits nothing at. Evaluated patterns satisfy it because `matchNode`,
    `matchSingleEdge`, `matchRangePath` and `collapsePath` only ever bind such
    values (`evalPattern_refBoundWF`). -/
def RecordRefBoundWF (G : PropertyGraph) (rho : Record) : Prop :=
  ∀ x, rho.mem x = true →
    (∃ g n, n < G.numNodes ∧ rho.lookup x = Value.nodeRef g n) ∨
    (∃ g e, e < G.numEdges ∧ rho.lookup x = Value.edgeRef g e) ∨
    (∃ l, rho.lookup x = Value.list l) ∨
    rho.lookup x = Value.null

/-- Entry-wise sufficient condition for `RecordRefBoundWF`: if every entry's value
    is an in-bounds ref or a list, the record is ref-bounded. `lookup x` is one of
    the record's entry values whenever `x` is in the domain. -/
theorem RecordRefBoundWF_of_entries {G : PropertyGraph} {rho : Record}
    (h : ∀ e ∈ rho, (∃ g n, n < G.numNodes ∧ e.2 = Value.nodeRef g n) ∨
                    (∃ g ee, ee < G.numEdges ∧ e.2 = Value.edgeRef g ee) ∨
                    (∃ l, e.2 = Value.list l) ∨
                    e.2 = Value.null) :
    RecordRefBoundWF G rho := by
  intro x hx
  have hmem : rho.any (fun e => e.1 == x) = true := hx
  cases hf : rho.find? (fun e => e.1 == x) with
  | none =>
    rw [List.find?_eq_none] at hf
    obtain ⟨y, hy, hpy⟩ := List.any_eq_true.mp hmem
    exact absurd hpy (hf y hy)
  | some e =>
    have hlk : rho.lookup x = e.2 := by
      show (match rho.find? (fun e => e.1 == x) with | some (_, v) => v | none => .null) = e.2
      rw [hf]
    rw [hlk]
    exact h e (List.mem_of_find?_eq_some hf)

/-- `RecordRefBoundWF` is preserved by `Record.merge`: every merged binding comes
    from one of the two operands (left wins on shared keys). -/
theorem RecordRefBoundWF.merge {G : PropertyGraph} {rho1 rho2 : Record}
    (h1 : RecordRefBoundWF G rho1) (h2 : RecordRefBoundWF G rho2) :
    RecordRefBoundWF G (rho1.merge rho2) := by
  intro x hx
  by_cases hm1 : rho1.mem x = true
  · rw [Record.merge_lookup_left rho1 rho2 x hm1]; exact h1 x hm1
  · have hm1f : rho1.mem x = false := by
      cases hh : rho1.mem x with | true => exact absurd hh hm1 | false => rfl
    rw [Record.merge_lookup_right rho1 rho2 x hm1f]
    rw [Record.merge_mem, hm1f, Bool.false_or] at hx
    exact h2 x hx

/-- A `matchNode` record is ref-bounded (binds its variable to an in-bounds node). -/
theorem matchNode_refBoundWF {G : PropertyGraph} {site : GraphSite}
    {na : NodeAtom} {rho : Record} (h : rho ∈ matchNode G site na) :
    RecordRefBoundWF G rho := by
  obtain ⟨i, hi, rfl⟩ := matchNode_mem_form_wf h
  apply RecordRefBoundWF_of_entries
  intro e he
  rw [List.mem_singleton] at he; subst he
  exact Or.inl ⟨site, i, hi, rfl⟩

/-- A `matchSingleEdge` record is ref-bounded (in-bounds endpoints and edge). -/
theorem matchSingleEdge_refBoundWF {G : PropertyGraph} {site : GraphSite}
    {src : NodeAtom} {rel : EdgeAtom} {dst : NodeAtom} {dir : Direction} {rho : Record}
    (h : rho ∈ matchSingleEdge G site src rel dst dir) :
    RecordRefBoundWF G rho := by
  obtain ⟨srcN, ei, dstN, hsrcN, hei, hdstN, _, _, _, _, _, _, _, _, rfl⟩ :=
    matchSingleEdge_mem_form' h
  apply RecordRefBoundWF_of_entries
  intro e he
  obtain ⟨ek, ev⟩ := e
  simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq] at he
  rcases he with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | hnil
  · exact Or.inl ⟨site, srcN, hsrcN, rfl⟩
  · exact Or.inr (Or.inl ⟨site, ei, hei, rfl⟩)
  · exact Or.inl ⟨site, dstN, hdstN, rfl⟩
  · exact absurd hnil (List.not_mem_nil _)

/-- Membership in `matchOptionalEdge`: either the zero-case record (both
    node variables bound to the same in-bounds node, the edge variable
    null) or an ordinary single-edge match. -/
theorem matchOptionalEdge_mem {G : PropertyGraph} {site : GraphSite}
    {src : NodeAtom} {rel : EdgeAtom} {dst : NodeAtom} {dir : Direction}
    {rho : Record} (h : rho ∈ matchOptionalEdge G site src rel dst dir) :
    (∃ i, ∃ _ : i < G.numNodes,
        rho = [(src.var, Value.nodeRef site i), (rel.var, Value.null),
               (dst.var, Value.nodeRef site i)]) ∨
    rho ∈ matchSingleEdge G site src { rel with quantifier := .single } dst dir := by
  rcases List.mem_append.mp h with hz | ho
  · left
    rw [List.mem_filterMap] at hz
    obtain ⟨i, _, hsome⟩ := hz
    by_cases hi : i < G.numNodes
    · rw [dif_pos hi] at hsome
      dsimp only at hsome
      split at hsome
      · exact ⟨i, hi, (Option.some.inj hsome).symm⟩
      · exact Option.noConfusion hsome
    · rw [dif_neg hi] at hsome
      exact Option.noConfusion hsome
  · right
    exact ho

/-- A `matchOptionalEdge` record is ref-bounded: the zero case binds two
    in-bounds node references and a null, the one case is a single-edge
    match. -/
theorem matchOptionalEdge_refBoundWF {G : PropertyGraph} {site : GraphSite}
    {src : NodeAtom} {rel : EdgeAtom} {dst : NodeAtom} {dir : Direction}
    {rho : Record} (h : rho ∈ matchOptionalEdge G site src rel dst dir) :
    RecordRefBoundWF G rho := by
  rcases matchOptionalEdge_mem h with ⟨i, hi, rfl⟩ | ho
  · apply RecordRefBoundWF_of_entries
    intro e he
    obtain ⟨ek, ev⟩ := e
    simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq] at he
    rcases he with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | hnil
    · exact Or.inl ⟨site, i, hi, rfl⟩
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inl ⟨site, i, hi, rfl⟩
    · exact absurd hnil (List.not_mem_nil _)
  · exact matchSingleEdge_refBoundWF ho

-- Schema membership / lookup bridges.
theorem RecordSchema.mem_of_entry {Ctx : RecordSchema} {x : Name} {t : GSort}
    (h : (x, t) ∈ Ctx.entries) : Ctx.mem x = true := by
  show Ctx.entries.any (fun e => e.1 == x) = true
  rw [List.any_eq_true]; exact ⟨(x, t), h, by simp⟩

theorem RecordSchema.lookup_some_mem {Ctx : RecordSchema} {x : Name} {t : GSort}
    (h : Ctx.lookup x = some t) : (x, t) ∈ Ctx.entries := by
  unfold RecordSchema.lookup at h
  cases hf : Ctx.entries.find? (fun e => e.1 == x) with
  | none => rw [hf] at h; simp at h
  | some e =>
    obtain ⟨k, v⟩ := e
    rw [hf] at h
    simp only [Option.some.injEq] at h
    subst h
    have hmem := List.mem_of_find?_eq_some hf
    have hpe := List.find?_some hf
    have hkx : k = x := eq_of_beq hpe
    subst hkx; exact hmem

theorem RecordSchema.mem_iff (Ctx : RecordSchema) (x : Name) :
    Ctx.mem x = true ↔ ∃ t, (x, t) ∈ Ctx.entries := by
  constructor
  · intro h
    obtain ⟨e, hmem, hpe⟩ := List.any_eq_true.mp (h : Ctx.entries.any (fun e => e.1 == x) = true)
    obtain ⟨k, v⟩ := e
    have : k = x := eq_of_beq hpe
    subst this; exact ⟨v, hmem⟩
  · intro ⟨t, ht⟩; exact RecordSchema.mem_of_entry ht

theorem RecordSchema.mem_lookup_some {Ctx : RecordSchema} {x : Name}
    (h : Ctx.mem x = true) : ∃ t, Ctx.lookup x = some t := by
  obtain ⟨t, ht⟩ := (RecordSchema.mem_iff Ctx x).mp h
  cases hf : Ctx.entries.find? (fun e => e.1 == x) with
  | none => exfalso; rw [List.find?_eq_none] at hf; exact hf (x, t) ht (by simp)
  | some e =>
    refine ⟨e.2, ?_⟩
    show (match Ctx.entries.find? (fun e => e.1 == x) with
          | some (_, t) => some t | none => none) = some e.2
    rw [hf]

-- ============================================================
--  `set` / `setMany` domain and entry structure
--
--  Used by the edge/refinement soundness (Pat-Edge / Pat-Step): the
--  refinement output schema is `(...join...).setMany [v1,r2,v3]`, so the
--  conformance proof needs to know how `set`/`setMany` change a schema's
--  domain (`mem`) and which entries they produce.
-- ============================================================

/-- `update` rewrites values but never keys, so it preserves membership. -/
theorem RecordSchema.update_mem (Ctx : RecordSchema) (x : Name) (t : GSort) (y : Name) :
    (Ctx.update x t).mem y = Ctx.mem y := by
  unfold RecordSchema.update RecordSchema.mem
  dsimp only
  generalize Ctx.entries = es
  induction es with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    rw [List.map_cons, List.any_cons, List.any_cons, ih]
    congr 1
    split <;> rfl

/-- `extend` appends `(x, t)`, so it adds exactly the key `x` to the domain. -/
theorem RecordSchema.extend_mem (Ctx : RecordSchema) (x : Name) (t : GSort) (y : Name) :
    (Ctx.extend x t).mem y = (Ctx.mem y || x == y) := by
  show ((Ctx.entries ++ [(x, t)]).any (fun e => e.1 == y))
     = (Ctx.entries.any (fun e => e.1 == y) || x == y)
  rw [List.any_append]
  simp [List.any_cons]

/-- `set x t` makes exactly `x` present, leaving every other key as it was. -/
theorem RecordSchema.set_mem (Ctx : RecordSchema) (x : Name) (t : GSort) (y : Name) :
    (Ctx.set x t).mem y = (Ctx.mem y || x == y) := by
  unfold RecordSchema.set
  split
  · rename_i hm
    rw [RecordSchema.update_mem]
    cases hxy : x == y with
    | false => simp
    | true =>
      rw [Bool.or_true]
      have hxy' : x = y := eq_of_beq hxy
      rw [← hxy']; exact hm
  · rw [RecordSchema.extend_mem]

/-- Looking up the just-`set` key returns the set value. -/
theorem RecordSchema.set_lookup_self (Ctx : RecordSchema) (x : Name) (t : GSort) :
    (Ctx.set x t).lookup x = some t := by
  by_cases hmem : Ctx.mem x = true
  · have hset : Ctx.set x t = Ctx.update x t := by unfold RecordSchema.set; rw [if_pos hmem]
    rw [hset]; unfold RecordSchema.lookup RecordSchema.update; rw [List.find?_map]
    have hpred : ((fun e : Name × GSort => e.1 == x) ∘
        (fun p : Name × GSort => if p.1 == x then (p.1, t) else p))
        = (fun e : Name × GSort => e.1 == x) := by
      funext e; obtain ⟨k, v⟩ := e; simp only [Function.comp]; split <;> rfl
    rw [hpred]
    cases h : Ctx.entries.find? (fun e => e.1 == x) with
    | none =>
      exfalso
      rw [RecordSchema.mem, List.any_eq_true] at hmem
      obtain ⟨e, he, hpe⟩ := hmem
      rw [List.find?_eq_none] at h
      exact absurd hpe (by simpa using h e he)
    | some e0 =>
      obtain ⟨k0, v0⟩ := e0
      have hk0 : (k0 == x) = true := by have hh := List.find?_some h; simpa using hh
      have hk0' : k0 = x := eq_of_beq hk0
      simp [hk0']
  · have hnm : Ctx.mem x = false := by simpa using hmem
    have hset : Ctx.set x t = Ctx.extend x t := by unfold RecordSchema.set; rw [if_neg hmem]
    rw [hset]; unfold RecordSchema.lookup RecordSchema.extend
    have hnone : Ctx.entries.find? (fun e => e.1 == x) = none := by
      rw [List.find?_eq_none]; intro e he
      rw [RecordSchema.mem, List.any_eq_false] at hnm
      simpa using hnm e he
    rw [List.find?_append, hnone]; simp

/-- Looking up a key other than the just-`set` one is unchanged. -/
theorem RecordSchema.set_lookup_other (Ctx : RecordSchema) (x : Name) (t : GSort) (y : Name)
    (hxy : (x == y) = false) :
    (Ctx.set x t).lookup y = Ctx.lookup y := by
  by_cases hmem : Ctx.mem x = true
  · have hset : Ctx.set x t = Ctx.update x t := by unfold RecordSchema.set; rw [if_pos hmem]
    rw [hset]; unfold RecordSchema.lookup RecordSchema.update; rw [List.find?_map]
    have hpred : ((fun e : Name × GSort => e.1 == y) ∘
        (fun p : Name × GSort => if p.1 == x then (p.1, t) else p))
        = (fun e : Name × GSort => e.1 == y) := by
      funext e; obtain ⟨k, v⟩ := e; simp only [Function.comp]; split <;> rfl
    rw [hpred]
    cases h : Ctx.entries.find? (fun e => e.1 == y) with
    | none => simp
    | some e0 =>
      obtain ⟨k0, v0⟩ := e0
      have hk0 : (k0 == y) = true := by have hh := List.find?_some h; simpa using hh
      have hne' : k0 ≠ x := by
        intro hc
        have hxeqy : x = y := hc.symm.trans (eq_of_beq hk0)
        rw [hxeqy, beq_self_eq_true] at hxy
        simp at hxy
      simp [hne']
  · have hset : Ctx.set x t = Ctx.extend x t := by unfold RecordSchema.set; rw [if_neg hmem]
    rw [hset]; unfold RecordSchema.lookup RecordSchema.extend
    rw [List.find?_append]
    cases h : Ctx.entries.find? (fun e => e.1 == y) with
    | none => simp [hxy]
    | some e0 => simp

/-- Lookup of the first of three distinct `setMany` bindings. -/
theorem RecordSchema.setMany3_lookup_fst (base : RecordSchema) (a r b : Name) (t1 t2 t3 : GSort)
    (hra : (r == a) = false) (hba : (b == a) = false) :
    (base.setMany [(a, t1), (r, t2), (b, t3)]).lookup a = some t1 := by
  show (((base.set a t1).set r t2).set b t3).lookup a = some t1
  rw [RecordSchema.set_lookup_other _ b t3 a hba, RecordSchema.set_lookup_other _ r t2 a hra,
      RecordSchema.set_lookup_self]

/-- Lookup of the second of three `setMany` bindings (distinct from the third). -/
theorem RecordSchema.setMany3_lookup_snd (base : RecordSchema) (a r b : Name) (t1 t2 t3 : GSort)
    (hbr : (b == r) = false) :
    (base.setMany [(a, t1), (r, t2), (b, t3)]).lookup r = some t2 := by
  show (((base.set a t1).set r t2).set b t3).lookup r = some t2
  rw [RecordSchema.set_lookup_other _ b t3 r hbr, RecordSchema.set_lookup_self]

/-- Lookup of the last of three `setMany` bindings. -/
theorem RecordSchema.setMany3_lookup_thd (base : RecordSchema) (a r b : Name) (t1 t2 t3 : GSort) :
    (base.setMany [(a, t1), (r, t2), (b, t3)]).lookup b = some t3 := by
  show (((base.set a t1).set r t2).set b t3).lookup b = some t3
  rw [RecordSchema.set_lookup_self]

/-- When the first and third `setMany` keys coincide (a self-loop), the third
    binding wins, so looking up the first key returns the third value. -/
theorem RecordSchema.setMany3_lookup_eq13 (base : RecordSchema) (a r b : Name) (t1 t2 t3 : GSort)
    (hab : (a == b) = true) :
    (base.setMany [(a, t1), (r, t2), (b, t3)]).lookup a = some t3 := by
  show (((base.set a t1).set r t2).set b t3).lookup a = some t3
  rw [eq_of_beq hab, RecordSchema.set_lookup_self]

/-- Lookup of a key distinct from all three `setMany` bindings reads the base. -/
theorem RecordSchema.setMany3_lookup_other (base : RecordSchema) (a r b : Name) (t1 t2 t3 : GSort)
    (x : Name) (ha : (a == x) = false) (hr : (r == x) = false) (hb : (b == x) = false) :
    (base.setMany [(a, t1), (r, t2), (b, t3)]).lookup x = base.lookup x := by
  show (((base.set a t1).set r t2).set b t3).lookup x = base.lookup x
  rw [RecordSchema.set_lookup_other _ b t3 x hb, RecordSchema.set_lookup_other _ r t2 x hr,
      RecordSchema.set_lookup_other _ a t1 x ha]

/-- `setMany` adds exactly the keys of its bindings. -/
theorem RecordSchema.setMany_mem (bindings : List (Name × GSort)) (Ctx : RecordSchema) (y : Name) :
    (Ctx.setMany bindings).mem y = (Ctx.mem y || bindings.any (fun b => b.1 == y)) := by
  induction bindings generalizing Ctx with
  | nil => simp [RecordSchema.setMany]
  | cons hd tl ih =>
    obtain ⟨x, t⟩ := hd
    have hstep : Ctx.setMany ((x, t) :: tl) = (Ctx.set x t).setMany tl := by
      unfold RecordSchema.setMany; rw [List.foldl_cons]
    rw [hstep, ih (Ctx.set x t), RecordSchema.set_mem, List.any_cons]
    simp only [Bool.or_assoc]

/-- Every entry of `set x t` is either the just-set `(x, t)` (under some key
    `==`-equal to `x`) or an old entry under a key distinct from `x`. -/
theorem RecordSchema.mem_set_entries {Ctx : RecordSchema} {x : Name} {t : GSort}
    {k : Name} {v : GSort} (h : (k, v) ∈ (Ctx.set x t).entries) :
    ((k == x) = true ∧ v = t) ∨ ((k == x) = false ∧ (k, v) ∈ Ctx.entries) := by
  unfold RecordSchema.set at h
  split at h
  · rename_i hm
    unfold RecordSchema.update at h
    rw [List.mem_map] at h
    obtain ⟨⟨k0, v0⟩, hmem, heq⟩ := h
    simp only [] at heq
    split at heq
    · rename_i hk0
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hk, hv⟩ := heq
      subst hk; exact Or.inl ⟨hk0, hv.symm⟩
    · rename_i hk0
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hk, hv⟩ := heq
      subst hk; subst hv
      simp only [Bool.not_eq_true] at hk0
      exact Or.inr ⟨hk0, hmem⟩
  · rename_i hm
    unfold RecordSchema.extend at h
    rw [List.mem_append] at h
    rcases h with hl | hr
    · refine Or.inr ⟨?_, hl⟩
      cases hkx : k == x
      · rfl
      · exfalso
        have hke : k = x := eq_of_beq hkx
        subst hke
        exact hm (RecordSchema.mem_of_entry hl)
    · rw [List.mem_singleton, Prod.mk.injEq] at hr
      obtain ⟨hk, hv⟩ := hr
      subst hk; subst hv
      exact Or.inl ⟨by simp, rfl⟩

/-- Every entry of `setMany bindings` is either one of the bindings (under a key
    `==`-equal to some binding's key, with that binding's value) or an old entry
    under a key distinct from every binding key. -/
theorem RecordSchema.mem_setMany_entries {Ctx : RecordSchema} {bindings : List (Name × GSort)}
    {k : Name} {v : GSort} (h : (k, v) ∈ (Ctx.setMany bindings).entries) :
    (∃ b, b ∈ bindings ∧ (k == b.1) = true ∧ v = b.2)
    ∨ ((k, v) ∈ Ctx.entries ∧ ∀ b ∈ bindings, (k == b.1) = false) := by
  induction bindings generalizing Ctx with
  | nil =>
    refine Or.inr ⟨?_, fun b hb => absurd hb (List.not_mem_nil b)⟩
    simpa [RecordSchema.setMany] using h
  | cons hd tl ih =>
    obtain ⟨x, t⟩ := hd
    have hstep : Ctx.setMany ((x, t) :: tl) = (Ctx.set x t).setMany tl := by
      unfold RecordSchema.setMany; rw [List.foldl_cons]
    rw [hstep] at h
    rcases ih h with ⟨b, hb, hkb, hvb⟩ | ⟨hbase, hall⟩
    · exact Or.inl ⟨b, List.mem_cons_of_mem _ hb, hkb, hvb⟩
    · rcases RecordSchema.mem_set_entries hbase with ⟨hkx, hv⟩ | ⟨hkx, hmem⟩
      · exact Or.inl ⟨(x, t), List.mem_cons_self _ _, hkx, hv⟩
      · refine Or.inr ⟨hmem, ?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with hbeq | hbtl
        · subst hbeq; exact hkx
        · exact hall b hbtl

-- Decompose membership in the join schema into the three constituents
-- (only-in-1 / shared / only-in-2) of `RecordSchema.join`.
theorem RecordSchema.join_entry_cases {G1 G2 : RecordSchema} {x : Name} {t : GSort}
    (h : (x, t) ∈ (G1.join G2).entries) :
    (∃ t1, (x, t1) ∈ G1.entries ∧ G2.mem x = false ∧ t = t1)
    ∨ (∃ t1 t2, (x, t1) ∈ G1.entries ∧ G2.lookup x = some t2
          ∧ t = RecordSchema.sortInter t1 t2)
    ∨ (∃ t2, (x, t2) ∈ G2.entries ∧ G1.mem x = false ∧ t = t2) := by
  simp only [RecordSchema.join] at h
  rw [List.mem_append, List.mem_append] at h
  rcases h with (h | h) | h
  · rw [List.mem_filter] at h
    obtain ⟨hmem, hcond⟩ := h
    exact Or.inl ⟨t, hmem, by simpa using hcond, rfl⟩
  · rw [List.mem_filterMap] at h
    obtain ⟨⟨k, t1⟩, hmem, hsome⟩ := h
    cases hlk : G2.lookup k with
    | none => rw [hlk] at hsome; simp at hsome
    | some t2 =>
      rw [hlk] at hsome
      simp only [Option.some.injEq, Prod.mk.injEq] at hsome
      obtain ⟨hk, ht⟩ := hsome
      subst hk; subst ht
      exact Or.inr (Or.inl ⟨t1, t2, hmem, hlk, rfl⟩)
  · rw [List.mem_filter] at h
    obtain ⟨hmem, hcond⟩ := h
    exact Or.inr (Or.inr ⟨t, hmem, by simpa using hcond, rfl⟩)

theorem RecordSchema.mem_join_of_onlyIn1 {G1 G2 : RecordSchema} {x : Name} {t1 : GSort}
    (hg1 : (x, t1) ∈ G1.entries) (hg2 : G2.mem x = false) :
    (x, t1) ∈ (G1.join G2).entries := by
  simp only [RecordSchema.join]
  rw [List.mem_append, List.mem_append]
  exact Or.inl (Or.inl (List.mem_filter.mpr ⟨hg1, by simp [hg2]⟩))

theorem RecordSchema.mem_join_of_shared {G1 G2 : RecordSchema} {x : Name} {t1 t2 : GSort}
    (hg1 : (x, t1) ∈ G1.entries) (hlk : G2.lookup x = some t2) :
    (x, RecordSchema.sortInter t1 t2) ∈ (G1.join G2).entries := by
  simp only [RecordSchema.join]
  rw [List.mem_append, List.mem_append]
  refine Or.inl (Or.inr (List.mem_filterMap.mpr ⟨(x, t1), hg1, ?_⟩))
  show (match G2.lookup x with
        | some t2 => some (x, RecordSchema.sortInter t1 t2) | none => none)
      = some (x, RecordSchema.sortInter t1 t2)
  rw [hlk]

theorem RecordSchema.mem_join_of_onlyIn2 {G1 G2 : RecordSchema} {x : Name} {t2 : GSort}
    (hg2 : (x, t2) ∈ G2.entries) (hg1 : G1.mem x = false) :
    (x, t2) ∈ (G1.join G2).entries := by
  simp only [RecordSchema.join]
  rw [List.mem_append, List.mem_append]
  exact Or.inr (List.mem_filter.mpr ⟨hg2, by simp [hg1]⟩)

theorem RecordSchema.join_mem_true_iff (G1 G2 : RecordSchema) (x : Name) :
    (G1.join G2).mem x = true ↔ (G1.mem x = true ∨ G2.mem x = true) := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := (RecordSchema.mem_iff _ x).mp h
    rcases RecordSchema.join_entry_cases ht with
      ⟨t1, hg1, _, _⟩ | ⟨t1, t2, hg1, _, _⟩ | ⟨t2, hg2, _, _⟩
    · exact Or.inl (RecordSchema.mem_of_entry hg1)
    · exact Or.inl (RecordSchema.mem_of_entry hg1)
    · exact Or.inr (RecordSchema.mem_of_entry hg2)
  · intro h
    rw [RecordSchema.mem_iff]
    rcases h with h1 | h2
    · obtain ⟨t1, hg1⟩ := (RecordSchema.mem_iff _ x).mp h1
      cases hg2 : G2.mem x with
      | true =>
        obtain ⟨t2, hlk⟩ := RecordSchema.mem_lookup_some hg2
        exact ⟨_, RecordSchema.mem_join_of_shared hg1 hlk⟩
      | false => exact ⟨t1, RecordSchema.mem_join_of_onlyIn1 hg1 hg2⟩
    · obtain ⟨t2, hg2⟩ := (RecordSchema.mem_iff _ x).mp h2
      cases hg1 : G1.mem x with
      | true =>
        obtain ⟨t1, hlk1⟩ := RecordSchema.mem_lookup_some hg1
        obtain ⟨t2', hlk2⟩ := RecordSchema.mem_lookup_some h2
        exact ⟨_, RecordSchema.mem_join_of_shared (RecordSchema.lookup_some_mem hlk1) hlk2⟩
      | false => exact ⟨t2, RecordSchema.mem_join_of_onlyIn2 hg2 hg1⟩

theorem RecordSchema.join_mem (G1 G2 : RecordSchema) (x : Name) :
    (G1.join G2).mem x = (G1.mem x || G2.mem x) := by
  have key := RecordSchema.join_mem_true_iff G1 G2 x
  rcases Bool.eq_false_or_eq_true ((G1.join G2).mem x) with hL | hL <;>
    rcases Bool.eq_false_or_eq_true (G1.mem x) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (G2.mem x) with h2 | h2 <;>
    simp_all [Bool.or_eq_true]

-- The `joinCompatible` guard guarantees, for each shared key, that the meet is
-- inhabited (neither ⊥ nor an empty former) -- exactly the meet lemma's premise.
theorem RecordSchema.joinCompatible_meet {G1 G2 : RecordSchema} {x : Name} {t1 t2 : GSort}
    (hjc : RecordSchema.joinCompatible G1 G2 = true)
    (hlk1 : G1.lookup x = some t1) (hlk2 : G2.lookup x = some t2) :
    (RecordSchema.sortInter t1 t2).isBot = false
    ∧ RecordSchema.sameKind t1 t2 = true := by
  simp only [RecordSchema.joinCompatible] at hjc
  have hx1 : x ∈ G1.dom := by
    show x ∈ G1.entries.map Prod.fst
    exact List.mem_map.mpr ⟨(x, t1), RecordSchema.lookup_some_mem hlk1, rfl⟩
  have hx2 : x ∈ G2.dom := by
    show x ∈ G2.entries.map Prod.fst
    exact List.mem_map.mpr ⟨(x, t2), RecordSchema.lookup_some_mem hlk2, rfl⟩
  have hxs : x ∈ G1.dom.filter (fun y => G2.dom.any (fun z => z == y)) :=
    List.mem_filter.mpr ⟨hx1, List.any_eq_true.mpr ⟨x, hx2, by simp⟩⟩
  have hpred := (List.all_eq_true.mp hjc) x hxs
  simp only [hlk1, hlk2] at hpred
  rw [Bool.and_eq_true] at hpred
  obtain ⟨hk, hb⟩ := hpred
  exact ⟨by simpa using hb, hk⟩

-- ============================================================
--  sortInter componentType inversion (for RuntimeConfigWF of join)
-- ============================================================

theorem baseSort_beq_self (b : BaseSort) : (b == b) = true := by cases b <;> rfl

theorem prod_nameBase_beq_self (p : Name × BaseSort) : (p == p) = true := by
  cases p with
  | mk a b => simp only [instBEqProd, beq_self_eq_true, baseSort_beq_self, Bool.and_self]

theorem propSchema_beq_self (ps : PropSchema) : (ps == ps) = true := by
  induction ps with
  | nil => rfl
  | cons hd tl ih =>
      show ((hd == hd) && (tl == tl)) = true
      rw [prod_nameBase_beq_self, ih, Bool.and_self]

theorem nodeSchemaFull_beq_self (ns : NodeSchemaFull) : (ns == ns) = true := by
  cases ns with
  | mk labels ps =>
      show ((labels == labels) && (ps == ps)) = true
      rw [beq_self_eq_true, propSchema_beq_self, Bool.and_self]

theorem edgeSchemaFull_beq_self (es : EdgeSchemaFull) : (es == es) = true := by
  cases es with
  | mk labels src dst ps dir =>
      show (labels == labels && (src == src && (dst == dst && (ps == ps && (dir == dir))))) = true
      simp only [beq_self_eq_true, nodeSchemaFull_beq_self, propSchema_beq_self, Bool.and_self]

theorem tighterNull_eq_nullable {a b : NullTag}
    (h : RecordSchema.tighterNull a b = .nullable) : a = .nullable ∧ b = .nullable := by
  cases a <;> cases b <;> simp_all [RecordSchema.tighterNull]

theorem componentType_eq_nodeRefinedOf (t : GSort) (G : GraphSite) (ssx : List NodeSchemaFull)
    (hsh : t.shape = .single (.nodeRefined G ssx)) (hnl : t.null = .nullable) :
    t.componentType = GSort.nodeRefinedOf G ssx := by
  obtain ⟨sh, nl⟩ := t
  simp only at hsh hnl
  subst hsh; subst hnl; rfl

theorem componentType_mk_shape_nodeRefined (t : GSort) (n : NullTag)
    (site : GraphSite) (ss : List NodeSchemaFull) (ns : NodeSchemaFull)
    (hnnull : n = .nullable → t.null = .nullable)
    (h1 : ∀ ss1, t.componentType = GSort.nodeRefinedOf site ss1 → ns ∈ ss1)
    (h : (GSort.mk t.shape n).componentType = GSort.nodeRefinedOf site ss) : ns ∈ ss := by
  apply h1 ss
  obtain ⟨sh, nl⟩ := t
  simp only [GSort.componentType] at h ⊢
  cases sh with
  | single e =>
      simp only [GSort.nodeRefinedOf, GSort.mk.injEq, SortShape.single.injEq] at h
      obtain ⟨he, hn⟩ := h
      have hnl : nl = .nullable := hnnull hn
      subst he; subst hnl; rfl
  | list es en => exact h
  | any => simp [GSort.nodeRefinedOf] at h
  | bot => simp [GSort.nodeRefinedOf] at h
  | nullType => simp [GSort.nodeRefinedOf] at h
  | union es => simp [GSort.nodeRefinedOf] at h
  | emptyFormer s m => simp [GSort.nodeRefinedOf] at h

-- Crux: sortInter componentType inversion (node version).
theorem sortInter_componentType_nodeRefined_mem
    (t1 t2 : GSort) (site : GraphSite) (ss : List NodeSchemaFull) (ns : NodeSchemaFull)
    (h1 : ∀ ss1, t1.componentType = GSort.nodeRefinedOf site ss1 → ns ∈ ss1)
    (h2 : ∀ ss2, t2.componentType = GSort.nodeRefinedOf site ss2 → ns ∈ ss2)
    (h : (RecordSchema.sortInter t1 t2).componentType = GSort.nodeRefinedOf site ss) :
    ns ∈ ss := by
  unfold RecordSchema.sortInter at h
  split at h
  · exact h1 ss h
  · split at h
    · exact h1 ss h
    · exact h2 ss h
    · exact h1 ss h
    · exact h2 ss h
    · -- catch-all
      split at h
      · -- same shape: result = { shape := t1.shape, null := tighterNull t1.null t2.null }
        exact componentType_mk_shape_nodeRefined t1 _ site ss ns
          (fun hn => (tighterNull_eq_nullable hn).1) h1 h
      · -- refined / unrefined / cross-kind match
        split at h
        · -- nodeRefined / nodeRefined
          rename_i G1 ss1 G2 ss2 heq1 heq2
          split at h
          · -- G == G'
            rename_i hGG
            dsimp only at h
            split at h
            · -- common empty -> nodeEmpty -> contradiction
              simp [GSort.componentType, GSort.nodeRefinedOf, GSort.nodeEmpty] at h
            · -- common nonempty -> the real intersection case
              simp only [GSort.componentType, GSort.nodeRefinedOf, GSort.mk.injEq,
                SortShape.single.injEq, ExtSort.nodeRefined.injEq] at h
              obtain ⟨⟨hG1site, hcommon⟩, hn⟩ := h
              obtain ⟨hnl1, hnl2⟩ := tighterNull_eq_nullable hn
              have hGGeq : G1 = G2 := eq_of_beq hGG
              have hns1 : ns ∈ ss1 := h1 ss1 (by
                rw [← hG1site]; exact componentType_eq_nodeRefinedOf t1 G1 ss1 heq1 hnl1)
              have hns2 : ns ∈ ss2 := h2 ss2 (by
                rw [← hG1site, hGGeq]; exact componentType_eq_nodeRefinedOf t2 G2 ss2 heq2 hnl2)
              rw [← hcommon]
              exact List.mem_filter.mpr
                ⟨hns1, List.any_eq_true.mpr ⟨ns, hns2, nodeSchemaFull_beq_self ns⟩⟩
          · -- G != G' -> botSort
            simp [GSort.componentType, GSort.nodeRefinedOf, GSort.botSort] at h
        · -- nodeRefined / node
          split at h
          · exact componentType_mk_shape_nodeRefined t1 _ site ss ns
              (fun hn => (tighterNull_eq_nullable hn).1) h1 h
          · simp [GSort.componentType, GSort.nodeRefinedOf, GSort.botSort] at h
        · -- node / nodeRefined
          split at h
          · exact componentType_mk_shape_nodeRefined t2 _ site ss ns
              (fun hn => (tighterNull_eq_nullable hn).2) h2 h
          · simp [GSort.componentType, GSort.nodeRefinedOf, GSort.botSort] at h
        · -- edgeRefined / edgeRefined -> edge/bot result, contradiction
          dsimp only at h
          (split at h <;> try split at h) <;>
            simp [GSort.componentType, GSort.nodeRefinedOf, GSort.botSort, GSort.edgeEmpty,
              GSort.mk.injEq, SortShape.single.injEq] at h
        · -- edgeRefined / edge
          split at h <;>
            simp_all [GSort.componentType, GSort.nodeRefinedOf, GSort.botSort,
              GSort.mk.injEq, SortShape.single.injEq]
        · -- edge / edgeRefined
          split at h <;>
            simp_all [GSort.componentType, GSort.nodeRefinedOf, GSort.botSort,
              GSort.mk.injEq, SortShape.single.injEq]
        · -- fallback -> botSort
          simp [GSort.componentType, GSort.nodeRefinedOf, GSort.botSort] at h

-- ===== Edge analog =====

theorem componentType_eq_edgeRefinedOf (t : GSort) (G : GraphSite) (ssx : List EdgeSchemaFull)
    (hsh : t.shape = .single (.edgeRefined G ssx)) (hnl : t.null = .nullable) :
    t.componentType = GSort.edgeRefinedOf G ssx := by
  obtain ⟨sh, nl⟩ := t
  simp only at hsh hnl
  subst hsh; subst hnl; rfl

theorem componentType_mk_shape_edgeRefined (t : GSort) (n : NullTag)
    (site : GraphSite) (ss : List EdgeSchemaFull) (es : EdgeSchemaFull)
    (hnnull : n = .nullable → t.null = .nullable)
    (h1 : ∀ ss1, t.componentType = GSort.edgeRefinedOf site ss1 → es ∈ ss1)
    (h : (GSort.mk t.shape n).componentType = GSort.edgeRefinedOf site ss) : es ∈ ss := by
  apply h1 ss
  obtain ⟨sh, nl⟩ := t
  simp only [GSort.componentType] at h ⊢
  cases sh with
  | single e =>
      simp only [GSort.edgeRefinedOf, GSort.mk.injEq, SortShape.single.injEq] at h
      obtain ⟨he, hn⟩ := h
      have hnl : nl = .nullable := hnnull hn
      subst he; subst hnl; rfl
  | list es en => exact h
  | any => simp [GSort.edgeRefinedOf] at h
  | bot => simp [GSort.edgeRefinedOf] at h
  | nullType => simp [GSort.edgeRefinedOf] at h
  | union es => simp [GSort.edgeRefinedOf] at h
  | emptyFormer s m => simp [GSort.edgeRefinedOf] at h

theorem sortInter_componentType_edgeRefined_mem
    (t1 t2 : GSort) (site : GraphSite) (ss : List EdgeSchemaFull) (es : EdgeSchemaFull)
    (h1 : ∀ ss1, t1.componentType = GSort.edgeRefinedOf site ss1 → es ∈ ss1)
    (h2 : ∀ ss2, t2.componentType = GSort.edgeRefinedOf site ss2 → es ∈ ss2)
    (h : (RecordSchema.sortInter t1 t2).componentType = GSort.edgeRefinedOf site ss) :
    es ∈ ss := by
  unfold RecordSchema.sortInter at h
  split at h
  · exact h1 ss h
  · split at h
    · exact h1 ss h
    · exact h2 ss h
    · exact h1 ss h
    · exact h2 ss h
    · split at h
      · -- same shape
        exact componentType_mk_shape_edgeRefined t1 _ site ss es
          (fun hn => (tighterNull_eq_nullable hn).1) h1 h
      · split at h
        · -- nodeRefined / nodeRefined -> node/bot result, contradiction
          dsimp only at h
          (split at h <;> try split at h) <;>
            simp [GSort.componentType, GSort.edgeRefinedOf, GSort.botSort, GSort.nodeEmpty,
              GSort.mk.injEq, SortShape.single.injEq] at h
        · -- nodeRefined / node
          split at h <;>
            simp_all [GSort.componentType, GSort.edgeRefinedOf, GSort.botSort,
              GSort.mk.injEq, SortShape.single.injEq]
        · -- node / nodeRefined
          split at h <;>
            simp_all [GSort.componentType, GSort.edgeRefinedOf, GSort.botSort,
              GSort.mk.injEq, SortShape.single.injEq]
        · -- edgeRefined / edgeRefined
          rename_i G1 ss1 G2 ss2 heq1 heq2
          split at h
          · rename_i hGG
            dsimp only at h
            split at h
            · simp [GSort.componentType, GSort.edgeRefinedOf, GSort.edgeEmpty] at h
            · simp only [GSort.componentType, GSort.edgeRefinedOf, GSort.mk.injEq,
                SortShape.single.injEq, ExtSort.edgeRefined.injEq] at h
              obtain ⟨⟨hG1site, hcommon⟩, hn⟩ := h
              obtain ⟨hnl1, hnl2⟩ := tighterNull_eq_nullable hn
              have hGGeq : G1 = G2 := eq_of_beq hGG
              have hes1 : es ∈ ss1 := h1 ss1 (by
                rw [← hG1site]; exact componentType_eq_edgeRefinedOf t1 G1 ss1 heq1 hnl1)
              have hes2 : es ∈ ss2 := h2 ss2 (by
                rw [← hG1site, hGGeq]; exact componentType_eq_edgeRefinedOf t2 G2 ss2 heq2 hnl2)
              rw [← hcommon]
              exact List.mem_filter.mpr
                ⟨hes1, List.any_eq_true.mpr ⟨es, hes2, edgeSchemaFull_beq_self es⟩⟩
          · simp [GSort.componentType, GSort.edgeRefinedOf, GSort.botSort] at h
        · -- edgeRefined / edge
          split at h
          · exact componentType_mk_shape_edgeRefined t1 _ site ss es
              (fun hn => (tighterNull_eq_nullable hn).1) h1 h
          · simp [GSort.componentType, GSort.edgeRefinedOf, GSort.botSort] at h
        · -- edge / edgeRefined
          split at h
          · exact componentType_mk_shape_edgeRefined t2 _ site ss es
              (fun hn => (tighterNull_eq_nullable hn).2) h2 h
          · simp [GSort.componentType, GSort.edgeRefinedOf, GSort.botSort] at h
        · -- fallback
          simp [GSort.componentType, GSort.edgeRefinedOf, GSort.botSort] at h


-- ============================================================
--  Schema well-formedness (`SchemaWF`) preservation
--
--  `SchemaWF Gamma` (every entry's key looks up to its own type, i.e. functional
--  / distinct keys) is the hypothesis `bindingTableJoin_conforms` carries. These
--  lemmas discharge it structurally for typing-produced schemas: the atom
--  singletons (base), and the schema operations (`join`/`setMany`/`liftTo*`) that
--  the refinement/quantifier rules apply.
-- ============================================================

/-- A key absent from the domain looks up to `none`. -/
theorem RecordSchema.lookup_eq_none_of_mem_false {Ctx : RecordSchema} {x : Name}
    (h : Ctx.mem x = false) : Ctx.lookup x = none := by
  cases hlk : Ctx.lookup x with
  | none => rfl
  | some t =>
    exfalso
    have hm := RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem hlk)
    rw [h] at hm
    exact Bool.noConfusion hm

/-- A singleton schema is well-formed (the atom-typing base case). -/
theorem RecordSchema.singleton_schemaWF (a : Name) (t : GSort) :
    SchemaWF (RecordSchema.mk [(a, t)]) := by
  intro x t' hxt'
  rw [List.mem_singleton, Prod.mk.injEq] at hxt'
  obtain ⟨hx, ht⟩ := hxt'
  subst hx; subst ht
  simp [RecordSchema.lookup, List.find?_cons, beq_self_eq_true]

/-- `join` preserves well-formedness: each join entry's type is functionally
    determined by the two inputs' lookups (using their `SchemaWF`), so it equals
    what `lookup` returns on the join. -/
theorem RecordSchema.join_schemaWF {G1 G2 : RecordSchema}
    (h1 : SchemaWF G1) (h2 : SchemaWF G2) : SchemaWF (G1.join G2) := by
  have hcanon : ∀ x s, (x, s) ∈ (G1.join G2).entries →
      some s = (match G1.lookup x, G2.lookup x with
                | some t1, some t2 => some (RecordSchema.sortInter t1 t2)
                | some t1, none => some t1
                | none, some t2 => some t2
                | none, none => none) := by
    intro x s hxs
    rcases RecordSchema.join_entry_cases hxs with
      ⟨t1, hg1, hg2, hs⟩ | ⟨t1, t2, hg1, hlk2, hs⟩ | ⟨t2, hg2, hg1, hs⟩
    · rw [hs, h1 x t1 hg1, RecordSchema.lookup_eq_none_of_mem_false hg2]
    · rw [hs, h1 x t1 hg1, hlk2]
    · rw [hs, h2 x t2 hg2, RecordSchema.lookup_eq_none_of_mem_false hg1]
  intro x t hxt
  obtain ⟨t', hlk'⟩ := RecordSchema.mem_lookup_some (RecordSchema.mem_of_entry hxt)
  rw [hlk', hcanon x t' (RecordSchema.lookup_some_mem hlk'), ← hcanon x t hxt]

/-- Canonical `lookup` on a join (both inputs well-formed): shared keys meet, keys
    in only one side keep that side's type. -/
theorem RecordSchema.join_lookup {G1 G2 : RecordSchema}
    (h1 : SchemaWF G1) (h2 : SchemaWF G2) (x : Name) :
    (G1.join G2).lookup x = (match G1.lookup x, G2.lookup x with
      | some t1, some t2 => some (RecordSchema.sortInter t1 t2)
      | some t1, none => some t1
      | none, some t2 => some t2
      | none, none => none) := by
  cases hjlk : (G1.join G2).lookup x with
  | some s =>
    have hmem := RecordSchema.lookup_some_mem hjlk
    rcases RecordSchema.join_entry_cases hmem with
      ⟨t1, hg1, hg2, hs⟩ | ⟨t1, t2, hg1, hlk2, hs⟩ | ⟨t2, hg2, hg1f, hs⟩
    · rw [hs, h1 x t1 hg1, RecordSchema.lookup_eq_none_of_mem_false hg2]
    · rw [hs, h1 x t1 hg1, hlk2]
    · rw [hs, h2 x t2 hg2, RecordSchema.lookup_eq_none_of_mem_false hg1f]
  | none =>
    have hmemf : (G1.join G2).mem x = false := by
      cases hm : (G1.join G2).mem x with
      | false => rfl
      | true =>
        obtain ⟨s, hs⟩ := RecordSchema.mem_lookup_some hm
        rw [hs] at hjlk; exact Option.noConfusion hjlk
    rw [RecordSchema.join_mem] at hmemf
    have hm1 : G1.mem x = false := by
      cases hh : G1.mem x with
      | false => rfl
      | true => rw [hh] at hmemf; exact Bool.noConfusion hmemf
    have hm2 : G2.mem x = false := by
      cases hh : G2.mem x with
      | false => rfl
      | true => rw [hh, Bool.or_true] at hmemf; exact Bool.noConfusion hmemf
    rw [RecordSchema.lookup_eq_none_of_mem_false hm1, RecordSchema.lookup_eq_none_of_mem_false hm2]

/-- Lookup on a join where the key is absent from the right side: reads the left. -/
theorem RecordSchema.join_lookup_of_right_none {G1 G2 : RecordSchema} {x : Name}
    (h1 : SchemaWF G1) (h2 : SchemaWF G2) (hr : G2.lookup x = none) :
    (G1.join G2).lookup x = G1.lookup x := by
  rw [RecordSchema.join_lookup h1 h2, hr]
  cases G1.lookup x <;> rfl

/-- `set` preserves well-formedness: every `set`-entry under key `k` has the same
    type (the just-set `t` if `k == x`, else its original `Ctx` type by `SchemaWF`),
    so it agrees with `lookup`. -/
theorem RecordSchema.set_schemaWF {Ctx : RecordSchema} {x : Name} {t : GSort}
    (h : SchemaWF Ctx) : SchemaWF (Ctx.set x t) := by
  have hfun : ∀ k v v', (k, v) ∈ (Ctx.set x t).entries → (k, v') ∈ (Ctx.set x t).entries →
      v = v' := by
    intro k v v' hv hv'
    rcases RecordSchema.mem_set_entries hv with ⟨hkx, hvt⟩ | ⟨hkx, hmem⟩
    · rcases RecordSchema.mem_set_entries hv' with ⟨hkx', hvt'⟩ | ⟨hkx', hmem'⟩
      · rw [hvt, hvt']
      · rw [hkx] at hkx'; exact Bool.noConfusion hkx'
    · rcases RecordSchema.mem_set_entries hv' with ⟨hkx', hvt'⟩ | ⟨hkx', hmem'⟩
      · rw [hkx'] at hkx; exact Bool.noConfusion hkx
      · exact Option.some.inj ((h k v hmem).symm.trans (h k v' hmem'))
  intro k v hv
  obtain ⟨v', hlk'⟩ := RecordSchema.mem_lookup_some (RecordSchema.mem_of_entry hv)
  rw [hlk', hfun k v' v (RecordSchema.lookup_some_mem hlk') hv]

/-- `setMany` preserves well-formedness (fold of `set`). -/
theorem RecordSchema.setMany_schemaWF (bindings : List (Name × GSort)) :
    ∀ {Ctx : RecordSchema}, SchemaWF Ctx → SchemaWF (Ctx.setMany bindings) := by
  induction bindings with
  | nil => intro Ctx h; simpa [RecordSchema.setMany] using h
  | cons hd tl ih =>
    intro Ctx h
    obtain ⟨x, t⟩ := hd
    have hstep : Ctx.setMany ((x, t) :: tl) = (Ctx.set x t).setMany tl := by
      unfold RecordSchema.setMany; rw [List.foldl_cons]
    rw [hstep]
    exact ih (RecordSchema.set_schemaWF h)

-- Every record produced by the join arises from an agreeing pair.
theorem mem_bindingTableJoin {B1 B2 : BindingTable} {rho : Record}
    (h : rho ∈ bindingTableJoin B1 B2) :
    ∃ rho1, rho1 ∈ B1 ∧ ∃ rho2, rho2 ∈ B2
      ∧ rho1.agreeOn rho2 = true ∧ rho = rho1.merge rho2 := by
  unfold bindingTableJoin at h
  rw [List.mem_flatMap] at h
  obtain ⟨rho1, hrho1, hrho⟩ := h
  rw [List.mem_filterMap] at hrho
  obtain ⟨rho2, hrho2, heq⟩ := hrho
  split at heq
  · rename_i hcond
    simp only [Option.some.injEq] at heq
    exact ⟨rho1, hrho1, rho2, hrho2, hcond, heq.symm⟩
  · simp at heq

/-- Intro form for `bindingTableJoin` membership. -/
theorem mem_bindingTableJoin_intro {B1 B2 : BindingTable} {rho1 rho2 : Record}
    (h1 : rho1 ∈ B1) (h2 : rho2 ∈ B2) (hag : rho1.agreeOn rho2 = true) :
    rho1.merge rho2 ∈ bindingTableJoin B1 B2 := by
  unfold bindingTableJoin
  rw [List.mem_flatMap]
  refine ⟨rho1, h1, ?_⟩
  rw [List.mem_filterMap]
  exact ⟨rho2, h2, by simp [hag]⟩

/-- Trail-mode rows are walk rows: the per-component distinct-edge filter
    only shrinks each comma component, and the join is unchanged. -/
theorem evalPatternTrail_subset (G : PropertyGraph) (site : GraphSite) :
    ∀ (P : Pattern) (rho : Record),
      rho ∈ evalPatternTrail G site P → rho ∈ evalPattern G site P := by
  intro P
  induction P with
  | node na => intro rho h; exact mem_of_filter h
  | edge n1 rel dir n2 => intro rho h; exact mem_of_filter h
  | step P rel dir n2 _ => intro rho h; exact mem_of_filter h
  | grouped P _ => intro rho h; exact mem_of_filter h
  | quantified P K _ => intro rho h; exact mem_of_filter h
  | patternList P1 P2 ih1 ih2 =>
      intro rho h
      have h' : rho ∈ bindingTableJoin (evalPatternTrail G site P1)
          (evalPatternTrail G site P2) := h
      obtain ⟨r1, hr1, r2, hr2, hag, rfl⟩ := mem_bindingTableJoin h'
      exact mem_bindingTableJoin_intro (ih1 r1 hr1) (ih2 r2 hr2) hag

/-- Conformance transports from the walk evaluator to the trail evaluator. -/
theorem btConforms_evalPatternTrail {G : PropertyGraph} {site : GraphSite}
    {P : Pattern} {Gamma : RecordSchema}
    (h : BTConforms (evalPattern G site P) Gamma) :
    BTConforms (evalPatternTrail G site P) Gamma :=
  fun rho hrho => h rho (evalPatternTrail_subset G site P rho hrho)

/-- Pattern Soundness (Theorem 6.2), conjunction case: the natural join of two
  conforming binding tables conforms to the join of their schemas, provided the
  schemas are join-compatible. -/
theorem bindingTableJoin_conforms (B1 B2 : BindingTable) (G1 G2 : RecordSchema)
    (hwf1 : SchemaWF G1)
    (h1 : BTConforms B1 G1) (h2 : BTConforms B2 G2)
    (hjc : RecordSchema.joinCompatible G1 G2 = true)
    (hEmptyVac : ∀ (x : Name) (t1 t2 : GSort),
        G1.lookup x = some t1 → G2.lookup x = some t2 →
        (RecordSchema.sortInter t1 t2).isEmptyFormer = true →
        ∀ rho1 rho2, rho1 ∈ B1 → rho2 ∈ B2 → rho1.agreeOn rho2 = true →
        RecordSchema.valueAdmissible (rho1.lookup x) t1 = true →
        RecordSchema.valueAdmissible (rho1.lookup x) t2 = true → False) :
    BTConforms (bindingTableJoin B1 B2) (G1.join G2) := by
  intro rho hrho
  obtain ⟨rho1, hrho1, rho2, hrho2, hag, rfl⟩ := mem_bindingTableJoin hrho
  obtain ⟨hdom1, hadm1⟩ := h1 rho1 hrho1
  obtain ⟨hdom2, hadm2⟩ := h2 rho2 hrho2
  refine ⟨?_, ?_⟩
  · intro x
    rw [Record.merge_mem, RecordSchema.join_mem, hdom1, hdom2]
  · intro x t hxt
    rcases RecordSchema.join_entry_cases hxt with
      ⟨t1, hg1, _, hte⟩ | ⟨t1, t2, hg1, hg2lk, hte⟩ | ⟨t2, hg2, hg1false, hte⟩
    · have hm1 : rho1.mem x = true := by rw [hdom1]; exact RecordSchema.mem_of_entry hg1
      rw [Record.merge_lookup_left _ _ _ hm1, hte]
      exact hadm1 x t1 hg1
    · have hm1 : rho1.mem x = true := by rw [hdom1]; exact RecordSchema.mem_of_entry hg1
      rw [Record.merge_lookup_left _ _ _ hm1, hte]
      have hadmt1 := hadm1 x t1 hg1
      have hg2mem : (x, t2) ∈ G2.entries := RecordSchema.lookup_some_mem hg2lk
      have hm2 : rho2.mem x = true := by rw [hdom2]; exact RecordSchema.mem_of_entry hg2mem
      have hlkeq : rho1.lookup x = rho2.lookup x := Record.agreeOn_lookup_eq _ _ _ hag hm1 hm2
      have hadmt2 : RecordSchema.valueAdmissible (rho1.lookup x) t2 = true := by
        rw [hlkeq]; exact hadm2 x t2 hg2mem
      have hg1lk : G1.lookup x = some t1 := hwf1 x t1 hg1
      by_cases hemp : (RecordSchema.sortInter t1 t2).isEmptyFormer = true
      · exact (hEmptyVac x t1 t2 hg1lk hg2lk hemp rho1 rho2 hrho1 hrho2 hag hadmt1 hadmt2).elim
      · obtain ⟨hbot, _⟩ := RecordSchema.joinCompatible_meet hjc hg1lk hg2lk
        have hempf : (RecordSchema.sortInter t1 t2).isEmptyFormer = false := by
          cases hh : (RecordSchema.sortInter t1 t2).isEmptyFormer with
          | true => exact absurd hh hemp
          | false => rfl
        exact sortInter_meet_admissible _ _ _ hbot hempf hadmt1 hadmt2
    · have hm1 : rho1.mem x = false := by rw [hdom1]; exact hg1false
      rw [Record.merge_lookup_right _ _ _ hm1, hte]
      exact hadm2 x t2 hg2

-- ============================================================
--  Pattern Soundness (Theorem 6.2) -- atom typing, label resolution
--
--  Toward the node-atom cases of Pattern Soundness: a node `n` that the
--  matcher accepts (its labels satisfy the atom's `LabelExpr`) and that
--  conforms to a catalog schema `ns` has `ns` surviving the static label
--  filter `resolveNodeSchemas`. This is the label half of the matcher↔schema
--  correspondence the closed/closed-fail atom cases rest on (the property
--  half, via `filterNodeSchemasByPropCompat`, is the remaining piece).
--
--  Key facts: `evalLabelExpr` depends only on the label *set* (so the node's
--  labels and the schema's set-equal labels evaluate any `LabelExpr` alike),
--  and for a catalog schema `ns ∈ Psi`, `ns ∈ labelFilterNodeSchemas Psi l`
--  iff `evalLabelExpr ns.labels l` (the static filter realizes the runtime
--  predicate; the neg/conj/disj cases use schema-label-set matching).
-- ============================================================

/-- `evalLabelExpr` only inspects label membership, so set-equal label lists
  satisfy the same label expressions. -/
theorem evalLabelExpr_set_invariant (L1 L2 : List Name)
    (h : ∀ x, L1.any (fun y => y == x) = L2.any (fun y => y == x)) (l : LabelExpr) :
    evalLabelExpr L1 l = evalLabelExpr L2 l := by
  have hemp : L1.isEmpty = L2.isEmpty := by
    cases L1 with
    | nil => cases L2 with
      | nil => rfl
      | cons b bs => have := h b; simp [List.any_cons] at this
    | cons a as => cases L2 with
      | nil => have := h a; simp [List.any_cons] at this
      | cons b bs => rfl
  induction l with
  | atom a => exact h a
  | wildcard => simp only [evalLabelExpr, hemp]
  | neg l ih => simp only [evalLabelExpr, ih]
  | conj l1 l2 ih1 ih2 => simp only [evalLabelExpr, ih1, ih2]
  | disj l1 l2 ih1 ih2 => simp only [evalLabelExpr, ih1, ih2]

theorem mem_labelFilterNodeSchemas_subset (Psi : GraphSchemaFull) (l : LabelExpr) :
    ∀ ns, ns ∈ labelFilterNodeSchemas Psi l → ns ∈ Psi.nodeSchemas := by
  induction l with
  | atom a => intro ns h; exact (List.mem_filter.mp h).1
  | wildcard => intro ns h; exact (List.mem_filter.mp h).1
  | neg l _ => intro ns h; exact (List.mem_filter.mp h).1
  | conj l1 l2 ih1 _ =>
    intro ns h; simp only [labelFilterNodeSchemas] at h
    exact ih1 ns (List.mem_filter.mp h).1
  | disj l1 l2 ih1 ih2 =>
    intro ns h; simp only [labelFilterNodeSchemas] at h
    rcases List.mem_append.mp h with h1 | h2
    · exact ih1 ns h1
    · exact ih2 ns (List.mem_filter.mp h2).1

private theorem any_lab_match {lst : List NodeSchemaFull} {tgt : List Name} :
    (lst.any (fun m => m.labels == tgt) = true) ↔ ∃ m, m ∈ lst ∧ m.labels = tgt := by
  rw [List.any_eq_true]
  exact ⟨fun ⟨m, hm, hq⟩ => ⟨m, hm, eq_of_beq hq⟩,
         fun ⟨m, hm, he⟩ => ⟨m, hm, by rw [he]; simp⟩⟩

private theorem any_lab_match' {lst : List NodeSchemaFull} {tgt : List Name} :
    (lst.any (fun m => tgt == m.labels) = true) ↔ ∃ m, m ∈ lst ∧ m.labels = tgt := by
  rw [List.any_eq_true]
  exact ⟨fun ⟨m, hm, hq⟩ => ⟨m, hm, (eq_of_beq hq).symm⟩,
         fun ⟨m, hm, he⟩ => ⟨m, hm, by rw [he]; simp⟩⟩

/-- For a catalog schema, static label filtering realizes the runtime label
  predicate `evalLabelExpr`. -/
theorem mem_labelFilterNodeSchemas_iff (Psi : GraphSchemaFull) (l : LabelExpr) :
    ∀ ns, ns ∈ Psi.nodeSchemas →
      (ns ∈ labelFilterNodeSchemas Psi l ↔ evalLabelExpr ns.labels l = true) := by
  induction l with
  | atom a =>
    intro ns hns
    simp only [labelFilterNodeSchemas, evalLabelExpr, List.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hns, h⟩⟩
  | wildcard =>
    intro ns hns
    simp only [labelFilterNodeSchemas, evalLabelExpr, List.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hns, h⟩⟩
  | neg l ih =>
    intro ns hns
    have hexists : (∃ m, m ∈ labelFilterNodeSchemas Psi l ∧ m.labels = ns.labels)
        ↔ evalLabelExpr ns.labels l = true := by
      constructor
      · rintro ⟨m, hm, heq⟩
        have := (ih m (mem_labelFilterNodeSchemas_subset Psi l m hm)).mp hm
        rw [heq] at this; exact this
      · intro he; exact ⟨ns, (ih ns hns).mpr he, rfl⟩
    have hmatch : (labelFilterNodeSchemas Psi l).any (fun m => m.labels == ns.labels) = true
        ↔ evalLabelExpr ns.labels l = true := any_lab_match.trans hexists
    simp only [labelFilterNodeSchemas, evalLabelExpr, List.mem_filter]
    rcases Bool.eq_false_or_eq_true ((labelFilterNodeSchemas Psi l).any (fun m => m.labels == ns.labels)) with hx | hx <;>
      rcases Bool.eq_false_or_eq_true (evalLabelExpr ns.labels l) with hy | hy <;> simp_all
  | conj l1 l2 ih1 ih2 =>
    intro ns hns
    have hexists : (∃ m, m ∈ labelFilterNodeSchemas Psi l2 ∧ m.labels = ns.labels)
        ↔ evalLabelExpr ns.labels l2 = true := by
      constructor
      · rintro ⟨m, hm, heq⟩
        have := (ih2 m (mem_labelFilterNodeSchemas_subset Psi l2 m hm)).mp hm
        rw [heq] at this; exact this
      · intro he; exact ⟨ns, (ih2 ns hns).mpr he, rfl⟩
    have hmatch : (labelFilterNodeSchemas Psi l2).any (fun ns' => ns.labels == ns'.labels) = true
        ↔ evalLabelExpr ns.labels l2 = true := any_lab_match'.trans hexists
    have h1 := ih1 ns hns
    simp only [labelFilterNodeSchemas, evalLabelExpr, List.mem_filter, Bool.and_eq_true]
    rcases Bool.eq_false_or_eq_true (evalLabelExpr ns.labels l1) with hy1 | hy1 <;>
      rcases Bool.eq_false_or_eq_true (evalLabelExpr ns.labels l2) with hy2 | hy2 <;> simp_all
  | disj l1 l2 ih1 ih2 =>
    intro ns hns
    have hexists : (∃ m, m ∈ labelFilterNodeSchemas Psi l1 ∧ m.labels = ns.labels)
        ↔ evalLabelExpr ns.labels l1 = true := by
      constructor
      · rintro ⟨m, hm, heq⟩
        have := (ih1 m (mem_labelFilterNodeSchemas_subset Psi l1 m hm)).mp hm
        rw [heq] at this; exact this
      · intro he; exact ⟨ns, (ih1 ns hns).mpr he, rfl⟩
    have hmatch : (labelFilterNodeSchemas Psi l1).any (fun ns' => ns.labels == ns'.labels) = true
        ↔ evalLabelExpr ns.labels l1 = true := any_lab_match'.trans hexists
    have h1 := ih1 ns hns
    have h2 := ih2 ns hns
    simp only [labelFilterNodeSchemas, evalLabelExpr, List.mem_append, List.mem_filter, Bool.or_eq_true]
    rcases Bool.eq_false_or_eq_true (evalLabelExpr ns.labels l1) with hy1 | hy1 <;>
      rcases Bool.eq_false_or_eq_true (evalLabelExpr ns.labels l2) with hy2 | hy2 <;> simp_all

/-- Mutually-included label lists carry the same membership Bool (set equality). -/
theorem mutual_subset_setEq (A B : List Name)
    (hAB : A.all (fun l => B.any (fun x => x == l)) = true)
    (hBA : B.all (fun l => A.any (fun x => x == l)) = true) :
    ∀ x, A.any (fun y => y == x) = B.any (fun y => y == x) := by
  intro x
  rcases Bool.eq_false_or_eq_true (A.any (fun y => y == x)) with ha | ha
  · rcases Bool.eq_false_or_eq_true (B.any (fun y => y == x)) with hb | hb
    · rw [ha, hb]
    · exfalso
      obtain ⟨y, hy, hyx⟩ := List.any_eq_true.mp ha
      have hyx' : y = x := eq_of_beq hyx
      have := (List.all_eq_true.mp hAB) y hy
      rw [hyx'] at this; rw [hb] at this; exact Bool.noConfusion this
  · rcases Bool.eq_false_or_eq_true (B.any (fun y => y == x)) with hb | hb
    · exfalso
      obtain ⟨y, hy, hyx⟩ := List.any_eq_true.mp hb
      have hyx' : y = x := eq_of_beq hyx
      have := (List.all_eq_true.mp hBA) y hy
      rw [hyx'] at this; rw [ha] at this; exact Bool.noConfusion this
    · rw [ha, hb]

/-- The label half of node-atom soundness: a conforming node's catalog schema
  survives label resolution whenever the runtime label check accepts the node. -/
theorem resolveNodeSchemas_mem_of_conforms (G : PropertyGraph) (Psi : GraphSchemaFull)
    (n : Fin G.numNodes) (ns : NodeSchemaFull) (labels : Option LabelExpr)
    (hns : ns ∈ Psi.nodeSchemas)
    (hconf : nodeConformsSchema G n ns = true)
    (hcheck : checkLabels (G.nodeLabels n) labels = true) :
    ns ∈ resolveNodeSchemas Psi labels := by
  cases labels with
  | none => exact hns
  | some l =>
    show ns ∈ labelFilterNodeSchemas Psi l
    rw [mem_labelFilterNodeSchemas_iff Psi l ns hns]
    simp only [nodeConformsSchema] at hconf
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hconf
    obtain ⟨⟨⟨_, hAB⟩, hBA⟩, _⟩ := hconf
    have hsetEq := mutual_subset_setEq (G.nodeLabels n) ns.labels hAB hBA
    have hc : evalLabelExpr (G.nodeLabels n) l = true := hcheck
    rw [evalLabelExpr_set_invariant (G.nodeLabels n) ns.labels hsetEq l] at hc
    exact hc

-- ============================================================
--  Pattern Soundness (Theorem 6.2) -- edge-atom label resolution
--
--  Edge mirror of the node label half above. `evalLabelExpr`,
--  `evalLabelExpr_set_invariant` and `mutual_subset_setEq` are
--  element-agnostic (they speak only of label *lists*) and are reused
--  as-is; only the schema-filtering functions differ (edgeSchemas /
--  labelFilterEdgeSchemas), so these copy the node proofs verbatim with
--  `NodeSchemaFull`/`nodeSchemas` replaced by their edge counterparts.
-- ============================================================

theorem mem_labelFilterEdgeSchemas_subset (Psi : GraphSchemaFull) (l : LabelExpr) :
    ∀ es, es ∈ labelFilterEdgeSchemas Psi l → es ∈ Psi.edgeSchemas := by
  induction l with
  | atom a => intro es h; exact (List.mem_filter.mp h).1
  | wildcard => intro es h; exact (List.mem_filter.mp h).1
  | neg l _ => intro es h; exact (List.mem_filter.mp h).1
  | conj l1 l2 ih1 _ =>
    intro es h; simp only [labelFilterEdgeSchemas] at h
    exact ih1 es (List.mem_filter.mp h).1
  | disj l1 l2 ih1 ih2 =>
    intro es h; simp only [labelFilterEdgeSchemas] at h
    rcases List.mem_append.mp h with h1 | h2
    · exact ih1 es h1
    · exact ih2 es (List.mem_filter.mp h2).1

private theorem any_lab_match_e {lst : List EdgeSchemaFull} {tgt : List Name} :
    (lst.any (fun m => m.labels == tgt) = true) ↔ ∃ m, m ∈ lst ∧ m.labels = tgt := by
  rw [List.any_eq_true]
  exact ⟨fun ⟨m, hm, hq⟩ => ⟨m, hm, eq_of_beq hq⟩,
         fun ⟨m, hm, he⟩ => ⟨m, hm, by rw [he]; simp⟩⟩

private theorem any_lab_match_e' {lst : List EdgeSchemaFull} {tgt : List Name} :
    (lst.any (fun m => tgt == m.labels) = true) ↔ ∃ m, m ∈ lst ∧ m.labels = tgt := by
  rw [List.any_eq_true]
  exact ⟨fun ⟨m, hm, hq⟩ => ⟨m, hm, (eq_of_beq hq).symm⟩,
         fun ⟨m, hm, he⟩ => ⟨m, hm, by rw [he]; simp⟩⟩

theorem mem_labelFilterEdgeSchemas_iff (Psi : GraphSchemaFull) (l : LabelExpr) :
    ∀ es, es ∈ Psi.edgeSchemas →
      (es ∈ labelFilterEdgeSchemas Psi l ↔ evalLabelExpr es.labels l = true) := by
  induction l with
  | atom a =>
    intro es hes
    simp only [labelFilterEdgeSchemas, evalLabelExpr, List.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hes, h⟩⟩
  | wildcard =>
    intro es hes
    simp only [labelFilterEdgeSchemas, evalLabelExpr, List.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hes, h⟩⟩
  | neg l ih =>
    intro es hes
    have hexists : (∃ m, m ∈ labelFilterEdgeSchemas Psi l ∧ m.labels = es.labels)
        ↔ evalLabelExpr es.labels l = true := by
      constructor
      · rintro ⟨m, hm, heq⟩
        have := (ih m (mem_labelFilterEdgeSchemas_subset Psi l m hm)).mp hm
        rw [heq] at this; exact this
      · intro he; exact ⟨es, (ih es hes).mpr he, rfl⟩
    have hmatch : (labelFilterEdgeSchemas Psi l).any (fun m => m.labels == es.labels) = true
        ↔ evalLabelExpr es.labels l = true := any_lab_match_e.trans hexists
    simp only [labelFilterEdgeSchemas, evalLabelExpr, List.mem_filter]
    rcases Bool.eq_false_or_eq_true ((labelFilterEdgeSchemas Psi l).any (fun m => m.labels == es.labels)) with hx | hx <;>
      rcases Bool.eq_false_or_eq_true (evalLabelExpr es.labels l) with hy | hy <;> simp_all
  | conj l1 l2 ih1 ih2 =>
    intro es hes
    have hexists : (∃ m, m ∈ labelFilterEdgeSchemas Psi l2 ∧ m.labels = es.labels)
        ↔ evalLabelExpr es.labels l2 = true := by
      constructor
      · rintro ⟨m, hm, heq⟩
        have := (ih2 m (mem_labelFilterEdgeSchemas_subset Psi l2 m hm)).mp hm
        rw [heq] at this; exact this
      · intro he; exact ⟨es, (ih2 es hes).mpr he, rfl⟩
    have hmatch : (labelFilterEdgeSchemas Psi l2).any (fun es' => es.labels == es'.labels) = true
        ↔ evalLabelExpr es.labels l2 = true := any_lab_match_e'.trans hexists
    have h1 := ih1 es hes
    simp only [labelFilterEdgeSchemas, evalLabelExpr, List.mem_filter, Bool.and_eq_true]
    rcases Bool.eq_false_or_eq_true (evalLabelExpr es.labels l1) with hy1 | hy1 <;>
      rcases Bool.eq_false_or_eq_true (evalLabelExpr es.labels l2) with hy2 | hy2 <;> simp_all
  | disj l1 l2 ih1 ih2 =>
    intro es hes
    have hexists : (∃ m, m ∈ labelFilterEdgeSchemas Psi l1 ∧ m.labels = es.labels)
        ↔ evalLabelExpr es.labels l1 = true := by
      constructor
      · rintro ⟨m, hm, heq⟩
        have := (ih1 m (mem_labelFilterEdgeSchemas_subset Psi l1 m hm)).mp hm
        rw [heq] at this; exact this
      · intro he; exact ⟨es, (ih1 es hes).mpr he, rfl⟩
    have hmatch : (labelFilterEdgeSchemas Psi l1).any (fun es' => es.labels == es'.labels) = true
        ↔ evalLabelExpr es.labels l1 = true := any_lab_match_e'.trans hexists
    have h1 := ih1 es hes
    have h2 := ih2 es hes
    simp only [labelFilterEdgeSchemas, evalLabelExpr, List.mem_append, List.mem_filter, Bool.or_eq_true]
    rcases Bool.eq_false_or_eq_true (evalLabelExpr es.labels l1) with hy1 | hy1 <;>
      rcases Bool.eq_false_or_eq_true (evalLabelExpr es.labels l2) with hy2 | hy2 <;> simp_all

/-- The label half of edge-atom soundness: a conforming edge's catalog schema
  survives label resolution whenever the runtime label check accepts the edge. -/
theorem resolveEdgeSchemas_mem_of_conforms (G : PropertyGraph) (Psi : GraphSchemaFull)
    (e : Fin G.numEdges) (es : EdgeSchemaFull) (labels : Option LabelExpr)
    (hes : es ∈ Psi.edgeSchemas)
    (hconf : edgeConformsSchema G e es = true)
    (hcheck : checkLabels (G.edgeLabels e) labels = true) :
    es ∈ resolveEdgeSchemas Psi labels := by
  cases labels with
  | none => exact hes
  | some l =>
    show es ∈ labelFilterEdgeSchemas Psi l
    rw [mem_labelFilterEdgeSchemas_iff Psi l es hes]
    simp only [edgeConformsSchema] at hconf
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
        Bool.and_eq_true, Bool.and_eq_true] at hconf
    obtain ⟨⟨⟨⟨⟨_, hAB⟩, hBA⟩, _⟩, _⟩, _⟩ := hconf
    have hsetEq := mutual_subset_setEq (G.edgeLabels e) es.labels hAB hBA
    have hc : evalLabelExpr (G.edgeLabels e) l = true := hcheck
    rw [evalLabelExpr_set_invariant (G.edgeLabels e) es.labels hsetEq l] at hc
    exact hc

-- ============================================================
--  Pattern Soundness (Theorem 6.2) -- PROVEN (see `patExprSoundness` below)
--
--  The former `axiom patternSoundness` (which asserted the result
--  unconditionally) has been discharged. Its replacement is the theorem
--  `patExprSoundness` (defined near the end of this file, after the per-pattern
--  workhorses it depends on). That theorem proves exactly the same conclusion
--    BTConforms (evalPattern G ctx.graphSite P) GammaOut
--  for any `PatExprTyping ctx P GammaOut`, but carries the
--  graph-conformance assumption `hCat` plus the explicit obligations for the
--  Lean fidelity defects that are still open (closed-fail, the `?`/optional and
--  quantified edge/step list-vs-nullable/single mismatches, the zero-length
--  group quantifier, and the quantified-path group lists). Those obligations are
--  what the remaining author-side fixes will discharge; until then they are
--  visible in the signature rather than assumed as an axiom.
-- ============================================================

-- ============================================================
--  Query Soundness (Theorem 6.3) -- AXIOM
--
--  This unconditional form is kept only so its `_bool` wrapper still type
--  checks. Its content is now exhibited as a composition of proven results by
--  `queryTypeSoundness_composed` (defined near the end of this file), which
--  derives the same conclusion from `queryTypeSoundness_assembled` with the
--  three workhorses plugged in (`patExprSoundness`, `projectionList_sound`,
--  `setOp_conforms`), carrying only the genuinely-open leaf obligations: the
--  pattern fidelity gaps, the naming-hygiene and graph-conformance
--  well-formedness, the projection well-formedness, the graph-switch clause,
--  and the two non-left-biased set ops. The axiom is removable once those
--  leaves close.
-- ============================================================

-- The flat `queryTypeSoundness` / `compositeQuerySoundness` axioms (Theorem 6.3 /
-- Corollary 6.1) that used to sit here have been REMOVED. They are now proven
-- *theorems* `queryTypeSoundness` / `compositeQuerySoundness` (and their `_bool`
-- wrappers) at the end of this file, defined as `queryTypeSoundness_composed` /
-- `compositeQuerySoundness_composed` -- i.e. their content is exhibited as a
-- composition of proven results (`patExprSoundness`, `projectionList_sound`,
-- `setOp_conforms`, `patExpr_runtimeWF`) carrying only the explicit, named leaf
-- obligations (the author-side pattern/set-op fidelity gaps and the standing
-- well-formedness assumptions), rather than being assumed outright. They live at
-- the end because they reference those workhorses, all defined later in the file.

-- ============================================================
--  Query Soundness (Theorem 6.3), assembled (skeleton)
--
--  `queryTypeSoundness_assembled` reduces Theorem 6.3 to four results, exactly
--  mirroring how `patExprSoundness` reduced Theorem 6.2 to the per-pattern
--  obligation. It is an induction over `QueryTyping`:
--    * `matchReturn` / `matchWhere` -> the matched table conforms (the pattern
--      soundness result `hPatSound`), filtering preserves conformance
--      (`filter_preserves`), and projecting preserves it (`hProjSound`);
--    * `useGraph` -> `hUseGraph` (graph resolution + recursion on the inner query
--      at the switched site; carried for now, like `patStep`);
--    * `cqLift` -> the induction hypothesis;
--    * `composite` -> the two induction hypotheses fed to `hSetOp` (Corollary 6.1).
--  The context is generalised for the induction (it changes under `useGraph`),
--  with `ctx' = ctx` carried so every other case lands back at the fixed `ctx`.
--  The four reduction hypotheses are the open obligations: `hPatSound` is
--  discharged by composing `patExprSoundness` (modulo its pattern obligations);
--  `hProjSound` (projection-list soundness) is the next sub-theorem to build;
--  `hUseGraph` and `hSetOp` remain. The `queryTypeSoundness` axiom above is kept
--  until these are discharged (its `_bool` wrapper still depends on it).
-- ============================================================

/-- Runtime-configuration well-formedness for schema-refined bindings: every
    variable whose `Gamma`-type has a schema-refined node (resp. edge) component
    `N⟨G',ss⟩` / `E⟨G',ss⟩` is bound to a graph element conforming to one of the
    schemas in `ss`. This is the graph-aware reading of Value Typing (Def 6.1)
    for refined element types -- which the graph-unaware `valueAdmissible` cannot
    express -- and is established for pattern-produced records by Pattern
    Soundness (Thm 6.2). -/
def RuntimeConfigWF (G : PropertyGraph) (rho : Record) (Gamma : RecordSchema) : Prop :=
  ∀ (x : Name) (t : GSort), Gamma.lookup x = some t →
    (∀ (site : GraphSite) (ss : List NodeSchemaFull),
        t.componentType = GSort.nodeRefinedOf site ss →
        ∀ (g : GraphSite) (n : Nat) (hn : n < G.numNodes),
          rho.lookup x = Value.nodeRef g n →
          ∃ ns, ns ∈ ss ∧
            propMapConformsSchema (G.nodeProps ⟨n, hn⟩) ns.propSchema = true) ∧
    (∀ (site : GraphSite) (ss : List EdgeSchemaFull),
        t.componentType = GSort.edgeRefinedOf site ss →
        ∀ (g : GraphSite) (ed : Nat) (he : ed < G.numEdges),
          rho.lookup x = Value.edgeRef g ed →
          ∃ es, es ∈ ss ∧
            propMapConformsSchema (G.edgeProps ⟨ed, he⟩) es.propSchema = true)

theorem queryTypeSoundness_assembled
    (ctx : TypingCtx) (G : PropertyGraph)
    (hPatSound : ∀ (P : Pattern) (GammaOut : RecordSchema),
        PatExprTyping ctx P GammaOut →
        BTConforms (evalPattern G ctx.graphSite P) GammaOut)
    (hPatRtWF : ∀ (P : Pattern) (GammaOut : RecordSchema),
        PatExprTyping ctx P GammaOut →
        ∀ rho, rho ∈ evalPattern G ctx.graphSite P → RuntimeConfigWF G rho GammaOut)
    (hProjSound : ∀ (Gamma1 Gamma2 : RecordSchema) (pis : ProjectionList) (matched : BindingTable),
        BTConforms matched Gamma1 →
        (∀ rho, rho ∈ matched → RuntimeConfigWF G rho Gamma1) →
        ProjectionListTyping ctx Gamma1 pis Gamma2 →
        BTConforms (matched.map (fun rho => projectRecord G ctx.graphSite rho matched pis)) Gamma2)
    (hUseGraph : ∀ (graphName : Name) (inner : Query) (GammaU : RecordSchema),
        (ctx.catalog.lookup graphName).isSome = true →
        QueryTyping { ctx with graphSite := graphName } inner GammaU →
        BTConforms (evalQuery ctx.catalog G ctx.graphSite (.useGraph graphName inner)) GammaU)
    (hSetOp : ∀ (op : SetOp) (Q1 Q2 : Query) (Gamma1 Gamma2 : RecordSchema),
        BTConforms (evalQuery ctx.catalog G ctx.graphSite Q1) Gamma1 →
        BTConforms (evalQuery ctx.catalog G ctx.graphSite Q2) Gamma2 →
        opCompatible op Gamma1 Gamma2 = true →
        BTConforms (applySetOp op (evalQuery ctx.catalog G ctx.graphSite Q1)
          (evalQuery ctx.catalog G ctx.graphSite Q2)) (opCombine op Gamma1 Gamma2))
    (Q : Query) (Gamma : RecordSchema) (hType : QueryTyping ctx Q Gamma)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G) :
    BTConforms (evalQuery ctx.catalog G ctx.graphSite Q) Gamma := by
  suffices H : ∀ (ctx' : TypingCtx) (Q : Query) (Gamma : RecordSchema),
      QueryTyping ctx' Q Gamma → ctx' = ctx →
      BTConforms (evalQuery ctx.catalog G ctx.graphSite Q) Gamma by
    exact H ctx Q Gamma hType rfl
  intro ctx' Q Gamma hType'
  induction hType' with
  | matchFilter ctxq P phi projs Gamma1 Gamma2 tPred omegaPred hGr hPat hPred hPredSub hProj =>
      intro hceq; subst hceq
      refine hProjSound Gamma1 Gamma2 projs _ ?_ ?_ hProj
      · exact filter_preserves _ Gamma1 _
          (btConforms_evalPatternTrail (hPatSound P Gamma1 hPat))
      · exact fun rho hrho => hPatRtWF P Gamma1 hPat rho
          (evalPatternTrail_subset _ _ _ _ (mem_of_filter hrho))
  | matchReturn ctxq P projs Gamma1 Gamma2 hGr hPat hProj =>
      intro hceq; subst hceq
      exact hProjSound Gamma1 Gamma2 projs _
        (btConforms_evalPatternTrail (hPatSound P Gamma1 hPat))
        (fun rho hrho => hPatRtWF P Gamma1 hPat rho
          (evalPatternTrail_subset _ _ _ _ hrho)) hProj
  | useGraph ctxq graphName Q0 GammaU hResolve hBody ih =>
      intro hceq; subst hceq
      exact hUseGraph graphName Q0 GammaU hResolve hBody
  | cqLift ctxq Q0 Gamma0 h ih =>
      intro hceq
      exact ih hceq
  | composite ctxq op Q1 Q2 Gamma1 Gamma2 h1 h2 hCompat ih1 ih2 =>
      intro hceq
      exact hSetOp op Q1 Q2 Gamma1 Gamma2 (ih1 hceq) (ih2 hceq) hCompat

-- ============================================================
--  Query Soundness (Theorem 6.3), catalog-wide
--
--  `queryTypeSoundness_assembled` fixes the working graph `G` for the whole
--  derivation, so a `use graph` clause (which switches both the site and the
--  graph) cannot reuse its own induction hypothesis and is carried as the
--  `hUseGraph` obligation. This catalog-wide form removes that obligation: the
--  conclusion tracks the site and graph that `evalQuery` actually uses, so the
--  `useGraph` case is discharged by its induction hypothesis at the switched
--  site. The key facts are that `evalQuery` keeps the same catalog across the
--  switch and that the catalog field is invariant down a `QueryTyping`
--  derivation (only `graphSite` changes), so the resolved graph at `graphName`
--  is exactly what the inner derivation is typed against.
--
--  The pattern and projection obligations are quantified over the working
--  context `ctx'` and its graph (they are used at whichever site the match runs
--  at after any switches); the set-operation obligation is graph-independent and
--  needs no such quantification. This is the skeleton a catalog-wide composed
--  theorem plugs the three workhorses into, exactly as `queryTypeSoundness_composed`
--  does for the fixed-graph skeleton, with `hUseGraph` no longer present.
-- ============================================================

theorem queryTypeSoundness_catalogWide
    (hPatSound : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' →
        ∀ (P : Pattern) (GammaOut : RecordSchema),
          PatExprTyping ctx' P GammaOut →
          BTConforms (evalPattern G' ctx'.graphSite P) GammaOut)
    (hPatRtWF : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' →
        ∀ (P : Pattern) (GammaOut : RecordSchema),
          PatExprTyping ctx' P GammaOut →
          ∀ rho, rho ∈ evalPattern G' ctx'.graphSite P → RuntimeConfigWF G' rho GammaOut)
    (hProjSound : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' →
        ∀ (Gamma1 Gamma2 : RecordSchema) (pis : ProjectionList) (matched : BindingTable),
          BTConforms matched Gamma1 →
          (∀ rho, rho ∈ matched → RuntimeConfigWF G' rho Gamma1) →
          ProjectionListTyping ctx' Gamma1 pis Gamma2 →
          BTConforms (matched.map (fun rho => projectRecord G' ctx'.graphSite rho matched pis)) Gamma2)
    (hSetOp : ∀ (op : SetOp) (_Q1 _Q2 : Query) (Gamma1 Gamma2 : RecordSchema)
        (B1 B2 : BindingTable),
        BTConforms B1 Gamma1 → BTConforms B2 Gamma2 →
        opCompatible op Gamma1 Gamma2 = true →
        BTConforms (applySetOp op B1 B2) (opCombine op Gamma1 Gamma2))
    (ctx : TypingCtx) (G : PropertyGraph) (Q : Query) (Gamma : RecordSchema)
    (hType : QueryTyping ctx Q Gamma)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G) :
    BTConforms (evalQuery ctx.catalog G ctx.graphSite Q) Gamma := by
  suffices H : ∀ (ctx' : TypingCtx) (Q : Query) (Gamma : RecordSchema),
      QueryTyping ctx' Q Gamma →
      ∀ (G' : PropertyGraph), ctx'.catalog.lookup ctx'.graphSite = some G' →
        BTConforms (evalQuery ctx'.catalog G' ctx'.graphSite Q) Gamma by
    exact H ctx Q Gamma hType G hGraph
  intro ctx' Q Gamma hType'
  induction hType' with
  | matchFilter ctxq P phi projs Gamma1 Gamma2 tPred omegaPred hGr hPat hPred hPredSub hProj =>
      intro G' hG'
      refine hProjSound ctxq G' hG' Gamma1 Gamma2 projs _ ?_ ?_ hProj
      · exact filter_preserves _ Gamma1 _
          (btConforms_evalPatternTrail (hPatSound ctxq G' hG' P Gamma1 hPat))
      · exact fun rho hrho => hPatRtWF ctxq G' hG' P Gamma1 hPat rho
          (evalPatternTrail_subset _ _ _ _ (mem_of_filter hrho))
  | matchReturn ctxq P projs Gamma1 Gamma2 hGr hPat hProj =>
      intro G' hG'
      exact hProjSound ctxq G' hG' Gamma1 Gamma2 projs _
        (btConforms_evalPatternTrail (hPatSound ctxq G' hG' P Gamma1 hPat))
        (fun rho hrho => hPatRtWF ctxq G' hG' P Gamma1 hPat rho
          (evalPatternTrail_subset _ _ _ _ hrho)) hProj
  | useGraph ctxq graphName Q0 GammaU hResolve hBody ih =>
      intro G' hG'
      cases hres : ctxq.catalog.lookup graphName with
      | none => simp [hres] at hResolve
      | some G'' =>
          have heq : evalQuery ctxq.catalog G' ctxq.graphSite (.useGraph graphName Q0)
                   = evalQuery ctxq.catalog G'' graphName Q0 := by
            simp only [evalQuery, resolveGraph, hres]
          rw [heq]
          exact ih G'' hres
  | cqLift ctxq Q0 Gamma0 h ih =>
      intro G' hG'
      exact ih G' hG'
  | composite ctxq op Q1 Q2 Gamma1 Gamma2 h1 h2 hCompat ih1 ih2 =>
      intro G' hG'
      exact hSetOp op Q1 Q2 Gamma1 Gamma2 _ _ (ih1 G' hG') (ih2 G' hG') hCompat

private theorem baseSort_eq_of_beq {a b : BaseSort} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> (revert h; decide)

/-- An extsort that `==`-matches a scalar IS that scalar (used to turn
    sortUnion's `ts.any (· == scalar b)` checks into list membership).
    The derived `BEq ExtSort` is not `LawfulBEq`, so we discharge this by
    reducing the scalar case to `baseSort_eq_of_beq` and the constructor
    mismatches via `Bool.noConfusion` (the beq is definitionally `false`). -/
private theorem eq_scalar_of_beq {x : ExtSort} {b : BaseSort}
    (h : (x == ExtSort.scalar b) = true) : x = ExtSort.scalar b := by
  cases x with
  | scalar b' => exact congrArg ExtSort.scalar (baseSort_eq_of_beq h)
  | node g => exact Bool.noConfusion h
  | edge g => exact Bool.noConfusion h
  | nodeRefined g ss => exact Bool.noConfusion h
  | edgeRefined g ss => exact Bool.noConfusion h

-- ============================================================
--  Schema property-type fold admissibility (Step 3)
--
--  Goal: if a node conforms to some schema ns in `schemas`, then the value
--  at key k is admissible for `propTypeOfNodeSchemas schemas k` (the union
--  of each schema's contribution). Proved by folding the single-schema
--  lemma `schemaProp_lookup_admissible` through `sortUnion`.
-- ============================================================

/-- null is admissible for any single-shape nullable sort. -/
private theorem null_adm_nullable_single (es : ExtSort) :
    RecordSchema.valueAdmissible Value.null ⟨.single es, .nullable⟩ = true := rfl

/-- null is admissible for a nonempty union nullable sort. -/
private theorem null_adm_nullable_union {ts : List ExtSort} (h : ts ≠ []) :
    RecordSchema.valueAdmissible Value.null ⟨.union ts, .nullable⟩ = true := by
  cases ts with
  | nil => exact absurd rfl h
  | cons a r => rfl

/-- The `?` (null) type at the `val` tag admits only the null value. -/
private theorem nullTypeVal_forces_null {v : Value}
    (h : RecordSchema.valueAdmissible v ⟨.nullType, .val⟩ = true) : v = Value.null := by
  cases v with
  | null => rfl
  | prim p => simp [RecordSchema.valueAdmissible] at h
  | nodeRef g n => simp [RecordSchema.valueAdmissible] at h
  | edgeRef g e => simp [RecordSchema.valueAdmissible] at h
  | list l => simp [RecordSchema.valueAdmissible] at h

/-- A scalar that `==`-matches some element of `ts` is a member of `ts`. -/
private theorem mem_of_any_scalar {ts : List ExtSort} {b : BaseSort}
    (h : ts.any (fun x => x == ExtSort.scalar b) = true) : ExtSort.scalar b ∈ ts := by
  rcases List.any_eq_true.mp h with ⟨x, hx, hxb⟩
  rw [← eq_scalar_of_beq hxb]; exact hx

/-- Admissibility for a union is preserved when the branch list grows. -/
private theorem union_weaken {v : Value} {ts ts' : List ExtSort}
    (hsub : ∀ t, t ∈ ts → t ∈ ts')
    (h : RecordSchema.valueAdmissible v ⟨.union ts, .nullable⟩ = true) :
    RecordSchema.valueAdmissible v ⟨.union ts', .nullable⟩ = true := by
  obtain ⟨t0, hmem0, h0⟩ := union_adm_elim h
  exact union_adm_intro (hsub t0 hmem0) h0

/-! ### sortUnion computation lemmas for two scalar singletons (Phi(k)? makes
    each schema contribution nullable, so all combos are nullable now). -/

private theorem sortUnion_single_scalar_self_nn (b : BaseSort) :
    RecordSchema.sortUnion (GSort.mk (.single (.scalar b)) .nullable)
                           (GSort.mk (.single (.scalar b)) .nullable)
      = GSort.mk (.single (.scalar b)) .nullable := by
  cases b <;> rfl

private theorem sortUnion_single_scalar_nn_diff {b1 b2 : BaseSort} (hb : b1 ≠ b2) :
    RecordSchema.sortUnion (GSort.mk (.single (.scalar b1)) .nullable)
                           (GSort.mk (.single (.scalar b2)) .nullable)
      = GSort.mk (.union [.scalar b1, .scalar b2]) .nullable := by
  cases b1 <;> cases b2 <;> first | rfl | (exact absurd rfl hb)

private theorem sortUnion_single_scalar_nullType_right (b : BaseSort) :
    RecordSchema.sortUnion (GSort.mk (.single (.scalar b)) .nullable)
                           (GSort.mk .nullType .val)
      = GSort.mk (.single (.scalar b)) .nullable := by
  cases b <;> rfl

/-- The shape of a single schema's contribution to a property type:
    either a nullable scalar (key present, type `Phi(k)?`) or `?` (key absent). -/
private def SchemaPropForm (t : GSort) : Prop :=
  (∃ b : BaseSort, t = GSort.mk (.single (.scalar b)) .nullable) ∨ t = GSort.mk .nullType .val

/-- The shapes a schema-derived property type can take: a nullable scalar,
    `?`, or a nonempty nullable union of scalars. Closed under the
    `sortUnion` folds used by `propTypeOfNodeSchemas`. -/
private def ScalarUnionType (t : GSort) : Prop :=
  (∃ b : BaseSort, t = GSort.mk (.single (.scalar b)) .nullable) ∨
  (t = GSort.mk .nullType .val) ∨
  (∃ ts : List ExtSort, ts ≠ [] ∧ t = GSort.mk (.union ts) .nullable)

/-- `sortUnion` of a scalar single with a NONEMPTY union (the empty-union arm is
    skipped). -/
private theorem sortUnion_single_scalar_union_nn (b : BaseSort) (ts : List ExtSort) (hts : ts ≠ []) :
    RecordSchema.sortUnion (GSort.mk (.single (.scalar b)) .nullable) (GSort.mk (.union ts) .nullable)
    = (if ts.any (fun x => x == ExtSort.scalar b) then GSort.mk (.union ts) .nullable
       else GSort.mk (.union (.scalar b :: ts)) .nullable) := by
  obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hts; rfl

/-- `sortUnion` of the null type with a NONEMPTY union is that union (nullable). -/
private theorem sortUnion_nullType_union_nn (ts : List ExtSort) (hts : ts ≠ []) :
    RecordSchema.sortUnion (GSort.mk .nullType .val) (GSort.mk (.union ts) .nullable)
    = GSort.mk (.union ts) .nullable := by
  obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hts; rfl

/-- The core fold step: unioning a single schema contribution `t1` with an
    accumulated scalar-union type `t2` (a) stays a scalar-union type, and
    (b) is an upper bound for admissibility of both `t1` and `t2`. -/
private theorem sortUnion_schemaProp {t1 t2 : GSort}
    (h1 : SchemaPropForm t1) (h2 : ScalarUnionType t2) :
    ScalarUnionType (RecordSchema.sortUnion t1 t2)
    ∧ (∀ v, RecordSchema.valueAdmissible v t1 = true →
            RecordSchema.valueAdmissible v (RecordSchema.sortUnion t1 t2) = true)
    ∧ (∀ v, RecordSchema.valueAdmissible v t2 = true →
            RecordSchema.valueAdmissible v (RecordSchema.sortUnion t1 t2) = true) := by
  unfold SchemaPropForm at h1
  unfold ScalarUnionType at h2
  rcases h1 with ⟨b1, rfl⟩ | rfl
  · rcases h2 with ⟨b2, rfl⟩ | rfl | ⟨ts2, hts2, rfl⟩
    · -- t1 = scalar b1 (nullable), t2 = scalar b2 (nullable)
      by_cases hb : b1 = b2
      · rw [hb, sortUnion_single_scalar_self_nn b2]
        exact ⟨Or.inl ⟨b2, rfl⟩, fun v h => h, fun v h => h⟩
      · rw [sortUnion_single_scalar_nn_diff hb]
        refine ⟨Or.inr (Or.inr ⟨[.scalar b1, .scalar b2], by simp, rfl⟩), ?_, ?_⟩
        · intro v hv; exact union_adm_intro (List.Mem.head _) hv
        · intro v hv; exact union_adm_intro (List.Mem.tail _ (List.Mem.head _)) hv
    · -- t1 = scalar b1 (nullable), t2 = ? (val)
      rw [sortUnion_single_scalar_nullType_right b1]
      exact ⟨Or.inl ⟨b1, rfl⟩,
             fun v hv => hv,
             fun v hv => by rw [nullTypeVal_forces_null hv]; exact null_adm_nullable_single _⟩
    · -- t1 = scalar b1 (nullable), t2 = union ts2 (nullable)
      rw [sortUnion_single_scalar_union_nn b1 ts2 hts2]
      by_cases hany : ts2.any (fun x => x == ExtSort.scalar b1) = true
      · rw [if_pos hany]
        refine ⟨Or.inr (Or.inr ⟨ts2, hts2, rfl⟩), ?_, ?_⟩
        · intro v hv; exact union_adm_intro (mem_of_any_scalar hany) hv
        · intro v hv; exact hv
      · rw [if_neg hany]
        refine ⟨Or.inr (Or.inr ⟨_, List.cons_ne_nil _ _, rfl⟩), ?_, ?_⟩
        · intro v hv; exact union_adm_intro (List.Mem.head _) hv
        · intro v hv; exact union_weaken (fun t ht => List.Mem.tail _ ht) hv
  · rcases h2 with ⟨b2, rfl⟩ | rfl | ⟨ts2, hts2, rfl⟩
    · -- t1 = ? (val), t2 = scalar b2 (nullable)
      exact ⟨Or.inl ⟨b2, rfl⟩,
             fun v hv => by rw [nullTypeVal_forces_null hv]; exact null_adm_nullable_single _,
             fun v hv => hv⟩
    · -- t1 = ? (val), t2 = ? (val)
      exact ⟨Or.inr (Or.inl rfl), fun v hv => hv, fun v hv => hv⟩
    · -- t1 = ? (val), t2 = union ts2 (nullable)
      rw [sortUnion_nullType_union_nn ts2 hts2]
      exact ⟨Or.inr (Or.inr ⟨ts2, hts2, rfl⟩),
             fun v hv => by rw [nullTypeVal_forces_null hv]; exact null_adm_nullable_union hts2,
             fun v hv => hv⟩

/-- `propTypeOfNodeSchemas` always produces a scalar-union type. -/
private theorem propTypeOfNodeSchemas_scalarUnion (schemas : List NodeSchemaFull) (k : Name) :
    ScalarUnionType (propTypeOfNodeSchemas schemas k) := by
  induction schemas with
  | nil =>
    exact Or.inr (Or.inr ⟨[.scalar .int, .scalar .string, .scalar .bool], by simp, rfl⟩)
  | cons ns rest ih =>
    cases rest with
    | nil =>
      have hsu : propTypeOfNodeSchemas [ns] k
        = (match ns.propSchema.lookup k with
           | some b => GSort.mk (.single (.scalar b)) .nullable
           | none => GSort.mk .nullType .val) := rfl
      rw [hsu]
      cases ns.propSchema.lookup k with
      | some b => exact Or.inl ⟨b, rfl⟩
      | none => exact Or.inr (Or.inl rfl)
    | cons r1 rest1 =>
      have hsu : propTypeOfNodeSchemas (ns :: r1 :: rest1) k
        = RecordSchema.sortUnion
            (match ns.propSchema.lookup k with
             | some b => GSort.mk (.single (.scalar b)) .nullable
             | none => GSort.mk .nullType .val)
            (propTypeOfNodeSchemas (r1 :: rest1) k) := rfl
      rw [hsu]
      have h1 : SchemaPropForm (match ns.propSchema.lookup k with
             | some b => GSort.mk (.single (.scalar b)) .nullable
             | none => GSort.mk .nullType .val) := by
        cases ns.propSchema.lookup k with
        | some b => exact Or.inl ⟨b, rfl⟩
        | none => exact Or.inr rfl
      exact (sortUnion_schemaProp h1 ih).1

/-- Step 3 main lemma: if `pm` conforms to schema `ns ∈ schemas`, then the
    value at key `k` is admissible for the folded property type. -/
private theorem propTypeOfNodeSchemas_mem_admissible {pm : PropMap}
    (schemas : List NodeSchemaFull) {ns : NodeSchemaFull}
    (hconf : propMapConformsSchema pm ns.propSchema = true) (k : Name) :
    ns ∈ schemas →
    RecordSchema.valueAdmissible (pm.lookup k) (propTypeOfNodeSchemas schemas k) = true := by
  induction schemas with
  | nil => intro hmem; exact absurd hmem (List.not_mem_nil _)
  | cons ns0 rest ih =>
    intro hmem
    cases rest with
    | nil =>
      have hns : ns = ns0 := by
        cases hmem with
        | head => rfl
        | tail _ h => exact absurd h (List.not_mem_nil _)
      subst hns
      have hsu : propTypeOfNodeSchemas [ns] k
        = (match ns.propSchema.lookup k with
           | some b => GSort.mk (.single (.scalar b)) .nullable
           | none => GSort.mk .nullType .val) := rfl
      rw [hsu]
      exact schemaProp_lookup_admissible hconf k
    | cons r1 rest1 =>
      have hsu : propTypeOfNodeSchemas (ns0 :: r1 :: rest1) k
        = RecordSchema.sortUnion
            (match ns0.propSchema.lookup k with
             | some b => GSort.mk (.single (.scalar b)) .nullable
             | none => GSort.mk .nullType .val)
            (propTypeOfNodeSchemas (r1 :: rest1) k) := rfl
      rw [hsu]
      have h1 : SchemaPropForm (match ns0.propSchema.lookup k with
             | some b => GSort.mk (.single (.scalar b)) .nullable
             | none => GSort.mk .nullType .val) := by
        cases ns0.propSchema.lookup k with
        | some b => exact Or.inl ⟨b, rfl⟩
        | none => exact Or.inr rfl
      have h2 : ScalarUnionType (propTypeOfNodeSchemas (r1 :: rest1) k) :=
        propTypeOfNodeSchemas_scalarUnion (r1 :: rest1) k
      have hmono := sortUnion_schemaProp h1 h2
      cases hmem with
      | head =>
        exact hmono.2.1 (pm.lookup k) (schemaProp_lookup_admissible hconf k)
      | tail _ hrest =>
        exact hmono.2.2 (pm.lookup k) (ih hrest)

-- ============================================================
--  Step 4: schema-refined property access (de-axiomatization)
-- ============================================================

/-- Every schema-derived property type admits the null value: by the `Phi(k)?`
    fix each contribution is nullable, so the fold is always a nullable scalar,
    `?`, or a nullable union -- all of which inhabit `Null`. This is exactly what
    makes the `Null`-receiver branches of property access sound. -/
private theorem scalarUnionType_admits_null {t : GSort} (h : ScalarUnionType t) :
    RecordSchema.valueAdmissible Value.null t = true := by
  rcases h with ⟨b, rfl⟩ | rfl | ⟨ts, hts, rfl⟩
  · exact null_adm_nullable_single _
  · rfl
  · exact null_adm_nullable_union hts

/-- Edge mirror of `propTypeOfNodeSchemas_scalarUnion`. -/
private theorem propTypeOfEdgeSchemas_scalarUnion (schemas : List EdgeSchemaFull) (k : Name) :
    ScalarUnionType (propTypeOfEdgeSchemas schemas k) := by
  induction schemas with
  | nil =>
    exact Or.inr (Or.inr ⟨[.scalar .int, .scalar .string, .scalar .bool], by simp, rfl⟩)
  | cons es rest ih =>
    cases rest with
    | nil =>
      have hsu : propTypeOfEdgeSchemas [es] k
        = (match es.propSchema.lookup k with
           | some b => GSort.mk (.single (.scalar b)) .nullable
           | none => GSort.mk .nullType .val) := rfl
      rw [hsu]
      cases es.propSchema.lookup k with
      | some b => exact Or.inl ⟨b, rfl⟩
      | none => exact Or.inr (Or.inl rfl)
    | cons r1 rest1 =>
      have hsu : propTypeOfEdgeSchemas (es :: r1 :: rest1) k
        = RecordSchema.sortUnion
            (match es.propSchema.lookup k with
             | some b => GSort.mk (.single (.scalar b)) .nullable
             | none => GSort.mk .nullType .val)
            (propTypeOfEdgeSchemas (r1 :: rest1) k) := rfl
      rw [hsu]
      have h1 : SchemaPropForm (match es.propSchema.lookup k with
             | some b => GSort.mk (.single (.scalar b)) .nullable
             | none => GSort.mk .nullType .val) := by
        cases es.propSchema.lookup k with
        | some b => exact Or.inl ⟨b, rfl⟩
        | none => exact Or.inr rfl
      exact (sortUnion_schemaProp h1 ih).1

/-- Edge mirror of `propTypeOfNodeSchemas_mem_admissible`: if `pm` conforms to
    edge schema `es ∈ schemas`, the value at key `k` is admissible for the
    folded edge property type. -/
private theorem propTypeOfEdgeSchemas_mem_admissible {pm : PropMap}
    (schemas : List EdgeSchemaFull) {es : EdgeSchemaFull}
    (hconf : propMapConformsSchema pm es.propSchema = true) (k : Name) :
    es ∈ schemas →
    RecordSchema.valueAdmissible (pm.lookup k) (propTypeOfEdgeSchemas schemas k) = true := by
  induction schemas with
  | nil => intro hmem; exact absurd hmem (List.not_mem_nil _)
  | cons es0 rest ih =>
    intro hmem
    cases rest with
    | nil =>
      have hes : es = es0 := by
        cases hmem with
        | head => rfl
        | tail _ h => exact absurd h (List.not_mem_nil _)
      subst hes
      have hsu : propTypeOfEdgeSchemas [es] k
        = (match es.propSchema.lookup k with
           | some b => GSort.mk (.single (.scalar b)) .nullable
           | none => GSort.mk .nullType .val) := rfl
      rw [hsu]
      exact schemaProp_lookup_admissible hconf k
    | cons r1 rest1 =>
      have hsu : propTypeOfEdgeSchemas (es0 :: r1 :: rest1) k
        = RecordSchema.sortUnion
            (match es0.propSchema.lookup k with
             | some b => GSort.mk (.single (.scalar b)) .nullable
             | none => GSort.mk .nullType .val)
            (propTypeOfEdgeSchemas (r1 :: rest1) k) := rfl
      rw [hsu]
      have h1 : SchemaPropForm (match es0.propSchema.lookup k with
             | some b => GSort.mk (.single (.scalar b)) .nullable
             | none => GSort.mk .nullType .val) := by
        cases es0.propSchema.lookup k with
        | some b => exact Or.inl ⟨b, rfl⟩
        | none => exact Or.inr rfl
      have h2 : ScalarUnionType (propTypeOfEdgeSchemas (r1 :: rest1) k) :=
        propTypeOfEdgeSchemas_scalarUnion (r1 :: rest1) k
      have hmono := sortUnion_schemaProp h1 h2
      cases hmem with
      | head => exact hmono.2.1 (pm.lookup k) (schemaProp_lookup_admissible hconf k)
      | tail _ hrest => exact hmono.2.2 (pm.lookup k) (ih hrest)

/-- A node-ref value is never admissible for a type whose component is a refined
    EDGE type. Used to rule out kind-mismatched receivers in schema property
    access (such a binding would violate record conformance). -/
private theorem nodeRef_not_edgeComp {tx : GSort} {site : GraphSite}
    {ss : List EdgeSchemaFull} (hcomp : tx.componentType = GSort.edgeRefinedOf site ss)
    {g : GraphSite} {n : Nat}
    (htx : RecordSchema.valueAdmissible (Value.nodeRef g n) tx = true) : False := by
  obtain ⟨shape, ntag⟩ := tx
  cases ntag <;> cases shape <;>
    simp_all [GSort.componentType, GSort.edgeRefinedOf, RecordSchema.valueAdmissible,
              Value.hasExtSort]

/-- An edge-ref value is never admissible for a type whose component is a refined
    NODE type. Symmetric to `nodeRef_not_edgeComp`. -/
private theorem edgeRef_not_nodeComp {tx : GSort} {site : GraphSite}
    {ss : List NodeSchemaFull} (hcomp : tx.componentType = GSort.nodeRefinedOf site ss)
    {g : GraphSite} {ed : Nat}
    (htx : RecordSchema.valueAdmissible (Value.edgeRef g ed) tx = true) : False := by
  obtain ⟨shape, ntag⟩ := tx
  cases ntag <;> cases shape <;>
    simp_all [GSort.componentType, GSort.nodeRefinedOf, RecordSchema.valueAdmissible,
              Value.hasExtSort]

-- ============================================================
--  RuntimeConfigWF is realizable from the paper's graph conformance
--
--  `RuntimeConfigWF` is the hypothesis Thm 6.1 carries for schema-refined
--  property access. To show it is neither vacuous nor ad hoc, we discharge it
--  from the paper's standard Graph Conformance (Def 2.3, `graphConformsSchema`):
--  every node/edge conforms to SOME schema in the catalog, so when a refined
--  type uses the full schema list (the unlabeled/unfiltered atom case) the
--  conformance obligation is met. The general (label/property-filtered) case is
--  what Pattern Soundness (Thm 6.2) establishes.
-- ============================================================

/-- From graph conformance: every node conforms to some catalog node schema. -/
private theorem graphConformsSchema_node {G : PropertyGraph} {Psi : GraphSchemaFull}
    (h : graphConformsSchema G Psi = true) (i : Nat) (hi : i < G.numNodes) :
    ∃ ns, ns ∈ Psi.nodeSchemas ∧ nodeConformsSchema G ⟨i, hi⟩ ns = true := by
  unfold graphConformsSchema at h
  rw [Bool.and_eq_true] at h
  have hnodes := h.1
  rw [List.all_eq_true] at hnodes
  have hi' := hnodes i (List.mem_range.mpr hi)
  rw [dif_pos hi, List.any_eq_true] at hi'
  obtain ⟨ns, hmem, hconf⟩ := hi'
  exact ⟨ns, hmem, hconf⟩

/-- From graph conformance: every edge conforms to some catalog edge schema. -/
private theorem graphConformsSchema_edge {G : PropertyGraph} {Psi : GraphSchemaFull}
    (h : graphConformsSchema G Psi = true) (i : Nat) (hi : i < G.numEdges) :
    ∃ es, es ∈ Psi.edgeSchemas ∧ edgeConformsSchema G ⟨i, hi⟩ es = true := by
  unfold graphConformsSchema at h
  rw [Bool.and_eq_true] at h
  have hedges := h.2
  rw [List.all_eq_true] at hedges
  have hi' := hedges i (List.mem_range.mpr hi)
  rw [dif_pos hi, List.any_eq_true] at hi'
  obtain ⟨es, hmem, hconf⟩ := hi'
  exact ⟨es, hmem, hconf⟩

/-- Node conformance entails property-map conformance (its last conjunct). -/
private theorem nodeConformsSchema_propMap {G : PropertyGraph} {n : Fin G.numNodes}
    {ns : NodeSchemaFull} (h : nodeConformsSchema G n ns = true) :
    propMapConformsSchema (G.nodeProps n) ns.propSchema = true := by
  unfold nodeConformsSchema at h
  dsimp only at h
  rw [Bool.and_eq_true] at h
  exact h.2

/-- Edge conformance entails property-map conformance (the 4th of its conjuncts). -/
private theorem edgeConformsSchema_propMap {G : PropertyGraph} {e : Fin G.numEdges}
    {es : EdgeSchemaFull} (h : edgeConformsSchema G e es = true) :
    propMapConformsSchema (G.edgeProps e) es.propSchema = true := by
  unfold edgeConformsSchema at h
  dsimp only at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.1.2

/-- `RuntimeConfigWF` is discharged by the paper's graph conformance whenever the
    schema-refined component types in `Gamma` use the full catalog schema lists
    (the unlabeled/unfiltered atom case). This demonstrates the hypothesis of
    Thm 6.1 is realizable from standard (Def 2.3) well-formedness, not vacuous. -/
theorem runtimeConfigWF_of_graphConforms
    {G : PropertyGraph} {Psi : GraphSchemaFull} {rho : Record} {Gamma : RecordSchema}
    (hG : graphConformsSchema G Psi = true)
    (hNode : ∀ x t site ss, Gamma.lookup x = some t →
        t.componentType = GSort.nodeRefinedOf site ss → ss = Psi.nodeSchemas)
    (hEdge : ∀ x t site ss, Gamma.lookup x = some t →
        t.componentType = GSort.edgeRefinedOf site ss → ss = Psi.edgeSchemas) :
    RuntimeConfigWF G rho Gamma := by
  intro x t hlk
  refine ⟨?_, ?_⟩
  · intro site ss hcomp _g n hn _hlook
    have hss := hNode x t site ss hlk hcomp
    subst hss
    obtain ⟨ns, hmem, hconf⟩ := graphConformsSchema_node hG n hn
    exact ⟨ns, hmem, nodeConformsSchema_propMap hconf⟩
  · intro site ss hcomp _g ed he _hlook
    have hss := hEdge x t site ss hlk hcomp
    subst hss
    obtain ⟨es, hmem, hconf⟩ := graphConformsSchema_edge hG ed he
    exact ⟨es, hmem, edgeConformsSchema_propMap hconf⟩

-- ============================================================
--  RuntimeConfigWFStrong: strong runtime config WF + the join lemma
-- ============================================================

/-- Strengthened runtime config well-formedness: instead of "the bound element
    conforms to *some* schema in the refined set", it says "*every* catalog schema
    the bound element conforms to lies in the refined set". This stronger statement
    is what is preserved by the natural join (the join intersects refined sets, so
    a single existential witness on each side need not land in the intersection),
    and it implies the plain `RuntimeConfigWF` via graph conformance. -/
def RuntimeConfigWFStrong (G : PropertyGraph) (Psi : GraphSchemaFull)
    (rho : Record) (Gamma : RecordSchema) : Prop :=
  ∀ (x : Name) (t : GSort), Gamma.lookup x = some t →
    (∀ (site : GraphSite) (ss : List NodeSchemaFull),
        t.componentType = GSort.nodeRefinedOf site ss →
        ∀ (g : GraphSite) (n : Nat) (hn : n < G.numNodes),
          rho.lookup x = Value.nodeRef g n →
          ∀ ns, ns ∈ Psi.nodeSchemas → nodeConformsSchema G ⟨n, hn⟩ ns = true → ns ∈ ss) ∧
    (∀ (site : GraphSite) (ss : List EdgeSchemaFull),
        t.componentType = GSort.edgeRefinedOf site ss →
        ∀ (g : GraphSite) (ed : Nat) (he : ed < G.numEdges),
          rho.lookup x = Value.edgeRef g ed →
          ∀ es, es ∈ Psi.edgeSchemas → edgeConformsSchema G ⟨ed, he⟩ es = true → es ∈ ss)

-- ============================================================
--  Empty-former join emptiness (kind-aware joinCompatible support)
--
--  The paper's join-compatibility admits same-kind empty-former meets; the
--  joined table is then provably empty because no graph element inhabits an
--  empty former. A schema shared by both refined lists keeps the meet
--  non-empty, so `RuntimeConfigWFStrong` (which records, per shared node, all
--  catalog schemas the node conforms to) together with graph conformance
--  (every node conforms to some catalog schema) forces a contradiction.
-- ============================================================

/-- A schema common to both refined node lists keeps the meet from being an
    empty former. -/
theorem sortInter_nodeRefinedOf_mem_not_emptyFormer {G : GraphSite}
    {ss1 ss2 : List NodeSchemaFull} {ns : NodeSchemaFull}
    (h1 : ns ∈ ss1) (h2 : ns ∈ ss2) :
    (RecordSchema.sortInter (GSort.nodeRefinedOf G ss1) (GSort.nodeRefinedOf G ss2)).isEmptyFormer
      = false := by
  have hcm : ns ∈ ss1.filter (fun s => ss2.any (fun s' => s == s')) := by
    rw [List.mem_filter]
    exact ⟨h1, List.any_eq_true.mpr ⟨ns, h2, nodeSchemaFull_beq_self ns⟩⟩
  have hnil : (ss1.filter (fun s => ss2.any (fun s' => s == s'))).isEmpty = false := by
    cases hf : (ss1.filter (fun s => ss2.any (fun s' => s == s'))) with
    | nil => rw [hf] at hcm; exact absurd hcm (List.not_mem_nil ns)
    | cons a l => rfl
  unfold RecordSchema.sortInter GSort.nodeRefinedOf
  split
  · rfl
  · simp only [beq_self_eq_true, if_true]
    split
    · rfl
    · rw [hnil]; rfl

theorem sortInter_edgeRefinedOf_mem_not_emptyFormer {G : GraphSite}
    {ss1 ss2 : List EdgeSchemaFull} {es : EdgeSchemaFull}
    (h1 : es ∈ ss1) (h2 : es ∈ ss2) :
    (RecordSchema.sortInter (GSort.edgeRefinedOf G ss1) (GSort.edgeRefinedOf G ss2)).isEmptyFormer
      = false := by
  have hcm : es ∈ ss1.filter (fun s => ss2.any (fun s' => s == s')) := by
    rw [List.mem_filter]
    exact ⟨h1, List.any_eq_true.mpr ⟨es, h2, edgeSchemaFull_beq_self es⟩⟩
  have hnil : (ss1.filter (fun s => ss2.any (fun s' => s == s'))).isEmpty = false := by
    cases hf : (ss1.filter (fun s => ss2.any (fun s' => s == s'))) with
    | nil => rw [hf] at hcm; exact absurd hcm (List.not_mem_nil es)
    | cons a l => rfl
  unfold RecordSchema.sortInter GSort.edgeRefinedOf
  split
  · rfl
  · simp only [beq_self_eq_true, if_true]
    split
    · rfl
    · rw [hnil]; rfl

/-- No value inhabits an empty type former. -/
private theorem adm_emptyFormer_false (v : Value) (t : GSort)
    (hef : t.isEmptyFormer = true) :
    RecordSchema.valueAdmissible v t = false := by
  unfold GSort.isEmptyFormer at hef
  unfold RecordSchema.valueAdmissible
  cases hsh : t.shape <;> rw [hsh] at hef <;>
    first
      | rfl
      | exact Bool.noConfusion hef

/-- A meet of a non-empty-former sort with the open edge sort is never an empty
    former (the empty-former-producing branches need both operands refined and
    same-kind, or an empty-former operand). Used at edge meets in the step join. -/
theorem sortInter_edgeOf_not_emptyFormer {G : GraphSite} {t : GSort}
    (h : t.isEmptyFormer = false) :
    (RecordSchema.sortInter t (GSort.edgeOf G)).isEmptyFormer = false := by
  unfold RecordSchema.sortInter GSort.edgeOf
  repeat' split
  all_goals first
    | exact h
    | rfl
    | (simp only [GSort.isEmptyFormer, GSort.botSort]; done)
    | (exfalso; simp_all; done)
    | simp_all

/-- A meet of a non-empty-former sort with the open node sort is never an empty
    former. Used at node meets in the step join. -/
theorem sortInter_nodeOf_not_emptyFormer {G : GraphSite} {t : GSort}
    (h : t.isEmptyFormer = false) :
    (RecordSchema.sortInter t (GSort.nodeOf G)).isEmptyFormer = false := by
  unfold RecordSchema.sortInter GSort.nodeOf
  repeat' split
  all_goals first
    | exact h
    | rfl
    | (simp only [GSort.isEmptyFormer, GSort.botSort]; done)
    | (exfalso; simp_all; done)
    | simp_all

/-- A sort whose shape is a single node/edge (refined or not) is nullable. Every
    entry of a typed pattern schema satisfies this, which is exactly what the
    closed empty-former-meet vacuity needs: the operand type is then the canonical
    `nodeRefinedOf`/`edgeRefinedOf` (nullable), so strong-WF's `componentType`
    guard fires. -/
def GSort.nodeEdgeNullable (t : GSort) : Prop :=
  match t.shape with
  | .single (.node _) => t.null = .nullable
  | .single (.nodeRefined _ _) => t.null = .nullable
  | .single (.edge _) => t.null = .nullable
  | .single (.edgeRefined _ _) => t.null = .nullable
  | _ => True

-- `sortInter` preserves `nodeEdgeNullable`: any node/edge-single result combines
-- two node/edge-single operands, whose nullable tags meet to nullable.
set_option maxHeartbeats 800000 in
theorem sortInter_nodeEdgeNullable {t1 t2 : GSort}
    (h1 : t1.nodeEdgeNullable) (h2 : t2.nodeEdgeNullable) :
    (RecordSchema.sortInter t1 t2).nodeEdgeNullable := by
  unfold RecordSchema.sortInter
  split
  · exact h1
  · split
    · exact h1
    · exact h2
    · exact h1
    · exact h2
    · -- neither operand is emptyFormer/bot: case shapes concretely; the result's
      -- null is `tighterNull` of two node/edge-single operands (both nullable).
      obtain ⟨sh1, nl1⟩ := t1; obtain ⟨sh2, nl2⟩ := t2
      simp only [GSort.nodeEdgeNullable] at h1 h2
      cases sh1 with
      | single es1 =>
        cases es1 <;>
          (cases sh2 with
           | single es2 =>
             cases es2 <;>
               (simp only [GSort.nodeEdgeNullable] <;> (repeat' split) <;>
                 first
                   | trivial | rfl | contradiction
                   | simp_all [beq_self_eq_true, RecordSchema.tighterNull, GSort.nodeEdgeNullable,
                       GSort.botSort, GSort.nodeEmpty, GSort.edgeEmpty])
           | _ =>
             simp only [GSort.nodeEdgeNullable] <;> (repeat' split) <;>
               first
                 | trivial | rfl | contradiction
                 | simp_all [beq_self_eq_true, GSort.nodeEdgeNullable, GSort.botSort])
      | _ => cases sh2 <;>
          (simp only [GSort.nodeEdgeNullable] <;> (repeat' split) <;>
            first
              | trivial | rfl | contradiction
              | simp_all [beq_self_eq_true, GSort.nodeEdgeNullable, GSort.botSort])

/-- No node strongly-conforms to two disjoint refined-schema sets under a
    conforming graph: the catalog schema it conforms to would have to lie in
    the (empty) intersection. -/
theorem nodeRefined_disjoint_vacuous {G : PropertyGraph} {Psi : GraphSchemaFull}
    (hGconf : graphConformsSchema G Psi = true)
    {site : GraphSite} {n : Nat} (hn : n < G.numNodes) {ss1 ss2 : List NodeSchemaFull}
    (hm1 : ∀ ns, ns ∈ Psi.nodeSchemas → nodeConformsSchema G ⟨n, hn⟩ ns = true → ns ∈ ss1)
    (hm2 : ∀ ns, ns ∈ Psi.nodeSchemas → nodeConformsSchema G ⟨n, hn⟩ ns = true → ns ∈ ss2)
    (hemp : (RecordSchema.sortInter (GSort.nodeRefinedOf site ss1) (GSort.nodeRefinedOf site ss2)).isEmptyFormer = true) :
    False := by
  obtain ⟨ns0, hpsi, hconf⟩ := graphConformsSchema_node hGconf n hn
  rw [sortInter_nodeRefinedOf_mem_not_emptyFormer (hm1 ns0 hpsi hconf) (hm2 ns0 hpsi hconf)] at hemp
  exact Bool.noConfusion hemp

theorem edgeRefined_disjoint_vacuous {G : PropertyGraph} {Psi : GraphSchemaFull}
    (hGconf : graphConformsSchema G Psi = true)
    {site : GraphSite} {ed : Nat} (he : ed < G.numEdges) {ss1 ss2 : List EdgeSchemaFull}
    (hm1 : ∀ es, es ∈ Psi.edgeSchemas → edgeConformsSchema G ⟨ed, he⟩ es = true → es ∈ ss1)
    (hm2 : ∀ es, es ∈ Psi.edgeSchemas → edgeConformsSchema G ⟨ed, he⟩ es = true → es ∈ ss2)
    (hemp : (RecordSchema.sortInter (GSort.edgeRefinedOf site ss1) (GSort.edgeRefinedOf site ss2)).isEmptyFormer = true) :
    False := by
  obtain ⟨es0, hpsi, hconf⟩ := graphConformsSchema_edge hGconf ed he
  rw [sortInter_edgeRefinedOf_mem_not_emptyFormer (hm1 es0 hpsi hconf) (hm2 es0 hpsi hconf)] at hemp
  exact Bool.noConfusion hemp

/-- The join lemma (strong form). If each side is `RuntimeConfigWFStrong`, the
    natural join of the records is `RuntimeConfigWFStrong` for the join of the
    schemas. The shared-variable case is the crux: the join intersects refined
    sets, and the `sortInter` componentType-inversion lemmas place a conforming
    schema (known to be in both sides' sets by the strong hypotheses) in the
    intersection. -/
theorem runtimeConfigWFStrong_join
    (G : PropertyGraph) (Psi : GraphSchemaFull)
    (rho1 rho2 : Record) (G1 G2 : RecordSchema)
    (hwf1 : SchemaWF G1) (hwf2 : SchemaWF G2)
    (hdom1 : ∀ x, rho1.mem x = G1.mem x)
    (hdom2 : ∀ x, rho2.mem x = G2.mem x)
    (hag : rho1.agreeOn rho2 = true)
    (hs1 : RuntimeConfigWFStrong G Psi rho1 G1)
    (hs2 : RuntimeConfigWFStrong G Psi rho2 G2) :
    RuntimeConfigWFStrong G Psi (rho1.merge rho2) (G1.join G2) := by
  intro x t hlk
  have hentry := RecordSchema.lookup_some_mem hlk
  rcases RecordSchema.join_entry_cases hentry with
    ⟨t1, hg1, _hg2false, hte⟩ | ⟨t1, t2, hg1, hg2lk, hte⟩ | ⟨t2, hg2, hg1false, hte⟩
  · -- onlyIn1
    subst hte
    have hm1 : rho1.mem x = true := by rw [hdom1]; exact RecordSchema.mem_of_entry hg1
    have hmerge : (rho1.merge rho2).lookup x = rho1.lookup x := Record.merge_lookup_left _ _ _ hm1
    have hg1lk : G1.lookup x = some t := hwf1 x t hg1
    refine ⟨?_, ?_⟩
    · intro site ss hcomp g n hn hlook ns hnsPsi hconf
      rw [hmerge] at hlook
      exact (hs1 x t hg1lk).1 site ss hcomp g n hn hlook ns hnsPsi hconf
    · intro site ss hcomp g ed he hlook es hesPsi hconf
      rw [hmerge] at hlook
      exact (hs1 x t hg1lk).2 site ss hcomp g ed he hlook es hesPsi hconf
  · -- shared
    subst hte
    have hm1 : rho1.mem x = true := by rw [hdom1]; exact RecordSchema.mem_of_entry hg1
    have hm2 : rho2.mem x = true := by
      rw [hdom2]; exact RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem hg2lk)
    have hmerge : (rho1.merge rho2).lookup x = rho1.lookup x := Record.merge_lookup_left _ _ _ hm1
    have hlkeq : rho1.lookup x = rho2.lookup x := Record.agreeOn_lookup_eq _ _ _ hag hm1 hm2
    have hg1lk : G1.lookup x = some t1 := hwf1 x t1 hg1
    refine ⟨?_, ?_⟩
    · intro site ss hcomp g n hn hlook ns hnsPsi hconf
      rw [hmerge] at hlook
      refine sortInter_componentType_nodeRefined_mem t1 t2 site ss ns ?_ ?_ hcomp
      · intro ss1 heq
        exact (hs1 x t1 hg1lk).1 site ss1 heq g n hn hlook ns hnsPsi hconf
      · intro ss2 heq
        exact (hs2 x t2 hg2lk).1 site ss2 heq g n hn (hlkeq ▸ hlook) ns hnsPsi hconf
    · intro site ss hcomp g ed he hlook es hesPsi hconf
      rw [hmerge] at hlook
      refine sortInter_componentType_edgeRefined_mem t1 t2 site ss es ?_ ?_ hcomp
      · intro ss1 heq
        exact (hs1 x t1 hg1lk).2 site ss1 heq g ed he hlook es hesPsi hconf
      · intro ss2 heq
        exact (hs2 x t2 hg2lk).2 site ss2 heq g ed he (hlkeq ▸ hlook) es hesPsi hconf
  · -- onlyIn2
    subst hte
    have hm1 : rho1.mem x = false := by rw [hdom1]; exact hg1false
    have hmerge : (rho1.merge rho2).lookup x = rho2.lookup x := Record.merge_lookup_right _ _ _ hm1
    have hg2lk : G2.lookup x = some t := hwf2 x t hg2
    refine ⟨?_, ?_⟩
    · intro site ss hcomp g n hn hlook ns hnsPsi hconf
      rw [hmerge] at hlook
      exact (hs2 x t hg2lk).1 site ss hcomp g n hn hlook ns hnsPsi hconf
    · intro site ss hcomp g ed he hlook es hesPsi hconf
      rw [hmerge] at hlook
      exact (hs2 x t hg2lk).2 site ss hcomp g ed he hlook es hesPsi hconf

/-- `RuntimeConfigWFStrong` implies plain `RuntimeConfigWF` whenever the graph
    conforms to the catalog: graph conformance supplies a conforming catalog
    schema for each element, and the strong property places that schema in the
    refined set. -/
theorem runtimeConfigWF_of_strong
    {G : PropertyGraph} {Psi : GraphSchemaFull} {rho : Record} {Gamma : RecordSchema}
    (hG : graphConformsSchema G Psi = true)
    (hs : RuntimeConfigWFStrong G Psi rho Gamma) :
    RuntimeConfigWF G rho Gamma := by
  intro x t hlk
  refine ⟨?_, ?_⟩
  · intro site ss hcomp g n hn hlook
    obtain ⟨ns, hmem, hconf⟩ := graphConformsSchema_node hG n hn
    exact ⟨ns, (hs x t hlk).1 site ss hcomp g n hn hlook ns hmem hconf,
      nodeConformsSchema_propMap hconf⟩
  · intro site ss hcomp g ed he hlook
    obtain ⟨es, hmem, hconf⟩ := graphConformsSchema_edge hG ed he
    exact ⟨es, (hs x t hlk).2 site ss hcomp g ed he hlook es hmem hconf,
      edgeConformsSchema_propMap hconf⟩



-- ============================================================
--  Node-atom soundness: the PROPERTY half + closed-fail vacuity
--  (companion to `resolveNodeSchemas_mem_of_conforms`, the label half)
-- ============================================================

/-- A literal's evaluated value conforms only to its own base sort. -/
private theorem evalLiteral_conformsToBase_eq {c : Literal} {t : BaseSort}
    (h : (evalLiteral c).conformsToBase t = true) : t = literalBaseSort c := by
  cases c <;> cases t <;>
    simp_all [evalLiteral, Value.ofInt, Value.ofString, Value.ofBool,
              Value.conformsToBase, PrimValue.hasSort, literalBaseSort]

/-- `PropConstraintTyping` makes every typed property entry come from an actual
    constraint whose key matches and whose literal has the recorded base sort. -/
private theorem propConstraintTyping_mem {props : List PropConstraint} {PhiPi : PropSchema}
    (h : PropConstraintTyping props PhiPi) :
    ∀ k t, (k, t) ∈ PhiPi →
      ∃ pc, pc ∈ props ∧ pc.key = k ∧ literalBaseSort pc.val = t := by
  induction h with
  | empty => intro k t hmem; cases hmem
  | atom k0 c tau hSort =>
    intro k t hmem
    have heq := List.mem_singleton.mp hmem
    rw [Prod.mk.injEq] at heq
    obtain ⟨hk, ht⟩ := heq
    exact ⟨{ key := k0, val := c }, List.mem_singleton.mpr rfl, hk.symm, hSort.trans ht.symm⟩
  | insert k0 c tau rest PhiRest hSort hFresh hRest ih =>
    intro k t hmem
    rw [List.mem_cons] at hmem
    rcases hmem with heq | hrest
    · rw [Prod.mk.injEq] at heq
      obtain ⟨hk, ht⟩ := heq
      exact ⟨{ key := k0, val := c }, List.mem_cons_self _ _, hk.symm, hSort.trans ht.symm⟩
    · obtain ⟨pc, hpcmem, hpck, hpcv⟩ := ih k t hrest
      exact ⟨pc, List.mem_cons_of_mem _ hpcmem, hpck, hpcv⟩

/-- A nonnull property-map lookup is reflected by `lookupOpt` and witnesses the key. -/
private theorem propMap_lookupOpt_of_lookup_ne_null {pm : PropMap} {k : Name}
    (h : pm.lookup k ≠ Value.null) :
    pm.lookupOpt k = some (pm.lookup k) ∧ k ∈ pm.dom := by
  cases hf : pm.find? (fun e => e.1 == k) with
  | none => exact absurd (by unfold PropMap.lookup; rw [hf]) h
  | some e =>
    obtain ⟨k', v⟩ := e
    have hmem : (k', v) ∈ pm := List.mem_of_find?_eq_some hf
    have hkeq : k' = k := eq_of_beq (by simpa using List.find?_some hf)
    have hlk : pm.lookup k = v := by unfold PropMap.lookup; rw [hf]
    have hlo : pm.lookupOpt k = some v := by unfold PropMap.lookupOpt; rw [hf]
    refine ⟨by rw [hlo, hlk], ?_⟩
    rw [← hkeq]; unfold PropMap.dom; exact List.mem_map_of_mem Prod.fst hmem

/-- If a key lies in a property schema's domain, the schema lookup succeeds. -/
private theorem propSchema_lookup_isSome_of_mem_dom {Phi : PropSchema} {k : Name}
    (h : k ∈ Phi.dom) : ∃ t, Phi.lookup k = some t := by
  unfold PropSchema.dom at h
  rcases List.mem_map.mp h with ⟨e, hemem, hek⟩
  unfold PropSchema.lookup
  cases hf : Phi.find? (fun e => e.1 == k) with
  | some z => obtain ⟨zk, zv⟩ := z; exact ⟨zv, rfl⟩
  | none =>
    exfalso
    have hcontra := (List.find?_eq_none.mp hf) e hemem
    simp [hek] at hcontra

/-- A successful property-schema lookup recovers the underlying entry. -/
private theorem propSchema_lookup_some_mem {Phi : PropSchema} {k : Name} {t : BaseSort}
    (h : Phi.lookup k = some t) : (k, t) ∈ Phi := by
  unfold PropSchema.lookup at h
  cases hf : Phi.find? (fun e => e.1 == k) with
  | none => rw [hf] at h; simp at h
  | some e =>
    obtain ⟨k', t'⟩ := e
    rw [hf] at h
    simp only [Option.some.injEq] at h
    have hmem : (k', t') ∈ Phi := List.mem_of_find?_eq_some hf
    have hkeq : k' = k := eq_of_beq (by simpa using List.find?_some hf)
    rw [hkeq, h] at hmem
    exact hmem

/-- The property half of node-atom soundness: a node that conforms to catalog
    schema `ns` and passes the runtime property check `checkNodeProps` survives
    the static property filter `filterNodeSchemasByPropCompat` for the typed
    property schema `PhiPi`. -/
theorem filterNodeSchemasByPropCompat_mem_of_conforms
    (G : PropertyGraph) (site : GraphSite) (n : Fin G.numNodes) (ns : NodeSchemaFull)
    (zetaL : List NodeSchemaFull) (props : List PropConstraint) (PhiPi : PropSchema)
    (hmem : ns ∈ zetaL)
    (hconf : nodeConformsSchema G n ns = true)
    (hPrp : PropConstraintTyping props PhiPi)
    (hcheck : checkNodeProps G site n props = true) :
    ns ∈ filterNodeSchemasByPropCompat zetaL PhiPi := by
  unfold filterNodeSchemasByPropCompat
  rw [List.mem_filter]
  refine ⟨hmem, ?_⟩
  rw [List.all_eq_true]
  intro e he
  obtain ⟨k, t⟩ := e
  -- find the constraint backing the typed entry (k, t)
  obtain ⟨pc, hpcmem, hpck, hpcv⟩ := propConstraintTyping_mem hPrp k t he
  -- the runtime check forces pm.lookup k = evalLiteral pc.val
  unfold checkNodeProps at hcheck
  rw [List.all_eq_true] at hcheck
  have hpc : (evalLiteral pc.val == (G.nodeProps n).lookup pc.key) = true :=
    hcheck pc hpcmem
  have hlk : (G.nodeProps n).lookup k = evalLiteral pc.val := by
    rw [← hpck]; exact (eq_of_beq hpc).symm
  -- evalLiteral never yields null, so k is a property key
  have hne : (G.nodeProps n).lookup k ≠ Value.null := by
    rw [hlk]; cases pc.val <;>
      simp [evalLiteral, Value.ofInt, Value.ofString, Value.ofBool]
  obtain ⟨hlo, hdom⟩ := propMap_lookupOpt_of_lookup_ne_null hne
  -- bring in property-map conformance
  have hpmconf := nodeConformsSchema_propMap hconf
  unfold propMapConformsSchema at hpmconf
  simp only [Bool.and_eq_true, List.all_eq_true] at hpmconf
  obtain ⟨⟨⟨_hlen, hpmsub⟩, _hschsub⟩, hphi⟩ := hpmconf
  -- k is a property key, hence a schema key, hence schema-lookup succeeds
  rcases List.any_eq_true.mp (hpmsub k hdom) with ⟨y, hy, hyk⟩
  rw [eq_of_beq hyk] at hy
  obtain ⟨t', hlook⟩ := propSchema_lookup_isSome_of_mem_dom hy
  -- the conforming value pins the schema sort: t' = literalBaseSort pc.val = t
  have hlo2 : (G.nodeProps n).lookupOpt k = some (evalLiteral pc.val) := by rw [hlo, hlk]
  have hconfk := hphi (k, t') (propSchema_lookup_some_mem hlook)
  simp only [hlo2] at hconfk
  have ht' : t' = t := (evalLiteral_conformsToBase_eq hconfk).trans hpcv
  -- conclude the filter predicate holds at (k, t)
  have hfin : ns.propSchema.lookup k = some t := by rw [hlook, ht']
  show (match ns.propSchema.lookup k with | some t' => t == t' | none => false) = true
  rw [hfin]
  cases t <;> rfl

/-- The property half of edge-atom soundness (edge mirror of
    `filterNodeSchemasByPropCompat_mem_of_conforms`): an edge that conforms to
    catalog schema `es` and passes `checkEdgeProps` survives the static property
    filter `filterEdgeSchemasByPropCompat`. The literal/propmap/propschema helpers
    are element-agnostic and reused; only `checkEdgeProps`/`G.edgeProps`/
    `es.propSchema`/`edgeConformsSchema_propMap` are edge-specific. -/
theorem filterEdgeSchemasByPropCompat_mem_of_conforms
    (G : PropertyGraph) (site : GraphSite) (e : Fin G.numEdges) (es : EdgeSchemaFull)
    (xiL : List EdgeSchemaFull) (props : List PropConstraint) (PhiPi : PropSchema)
    (hmem : es ∈ xiL)
    (hconf : edgeConformsSchema G e es = true)
    (hPrp : PropConstraintTyping props PhiPi)
    (hcheck : checkEdgeProps G site e props = true) :
    es ∈ filterEdgeSchemasByPropCompat xiL PhiPi := by
  unfold filterEdgeSchemasByPropCompat
  rw [List.mem_filter]
  refine ⟨hmem, ?_⟩
  rw [List.all_eq_true]
  intro ee he
  obtain ⟨k, t⟩ := ee
  obtain ⟨pc, hpcmem, hpck, hpcv⟩ := propConstraintTyping_mem hPrp k t he
  unfold checkEdgeProps at hcheck
  rw [List.all_eq_true] at hcheck
  have hpc : (evalLiteral pc.val == (G.edgeProps e).lookup pc.key) = true :=
    hcheck pc hpcmem
  have hlk : (G.edgeProps e).lookup k = evalLiteral pc.val := by
    rw [← hpck]; exact (eq_of_beq hpc).symm
  have hne : (G.edgeProps e).lookup k ≠ Value.null := by
    rw [hlk]; cases pc.val <;>
      simp [evalLiteral, Value.ofInt, Value.ofString, Value.ofBool]
  obtain ⟨hlo, hdom⟩ := propMap_lookupOpt_of_lookup_ne_null hne
  have hpmconf := edgeConformsSchema_propMap hconf
  unfold propMapConformsSchema at hpmconf
  simp only [Bool.and_eq_true, List.all_eq_true] at hpmconf
  obtain ⟨⟨⟨_hlen, hpmsub⟩, _hschsub⟩, hphi⟩ := hpmconf
  rcases List.any_eq_true.mp (hpmsub k hdom) with ⟨y, hy, hyk⟩
  rw [eq_of_beq hyk] at hy
  obtain ⟨t', hlook⟩ := propSchema_lookup_isSome_of_mem_dom hy
  have hlo2 : (G.edgeProps e).lookupOpt k = some (evalLiteral pc.val) := by rw [hlo, hlk]
  have hconfk := hphi (k, t') (propSchema_lookup_some_mem hlook)
  simp only [hlo2] at hconfk
  have ht' : t' = t := (evalLiteral_conformsToBase_eq hconfk).trans hpcv
  have hfin : es.propSchema.lookup k = some t := by rw [hlook, ht']
  show (match es.propSchema.lookup k with | some t' => t == t' | none => false) = true
  rw [hfin]
  cases t <;> rfl

/-- Closed-fail vacuity (soundness of Atom-Node-Closed-Fail): when the static
    node filter is empty, no node passes the runtime matcher, so `matchNode`
    yields no records. Both correspondence halves feed in here -- a matched node
    conforms to some catalog schema (graph conformance), that schema survives
    label resolution (`resolveNodeSchemas_mem_of_conforms`) and the property
    filter (`filterNodeSchemasByPropCompat_mem_of_conforms`), contradicting
    emptiness. The empty type former the rule assigns is therefore sound: it is
    never asked to admit a value. -/
theorem not_mem_matchNode_of_filter_empty
    (G : PropertyGraph) (Psi : GraphSchemaFull) (site : GraphSite)
    (v : Name) (labels : Option LabelExpr) (props : List PropConstraint)
    (PhiPi : PropSchema) (zetaL : List NodeSchemaFull)
    (hGconf : graphConformsSchema G Psi = true)
    (hPrp : PropConstraintTyping props PhiPi)
    (hLbl : zetaL = resolveNodeSchemas Psi labels)
    (hEmpty : (filterNodeSchemasByPropCompat zetaL PhiPi).length = 0)
    (rho : Record)
    (hrho : rho ∈ matchNode G site { var := v, labels := labels, props := props }) :
    False := by
  unfold matchNode at hrho
  rw [List.mem_filterMap] at hrho
  obtain ⟨i, _hirange, hsome⟩ := hrho
  split at hsome
  · rename_i hlt
    simp only [] at hsome
    split at hsome
    · split at hsome
      · rename_i hlbl hprp
        obtain ⟨ns, hns, hconf⟩ := graphConformsSchema_node hGconf i hlt
        have hlblmem : ns ∈ resolveNodeSchemas Psi labels :=
          resolveNodeSchemas_mem_of_conforms G Psi ⟨i, hlt⟩ ns labels hns hconf hlbl
        rw [← hLbl] at hlblmem
        have hpropmem : ns ∈ filterNodeSchemasByPropCompat zetaL PhiPi :=
          filterNodeSchemasByPropCompat_mem_of_conforms G site ⟨i, hlt⟩ ns zetaL props PhiPi
            hlblmem hconf hPrp hprp
        rw [List.length_eq_zero] at hEmpty
        rw [hEmpty] at hpropmem
        exact List.not_mem_nil ns hpropmem
      · simp at hsome
    · simp at hsome
  · simp at hsome

/-- Edge closed-fail vacuity (soundness of Atom-Edge-Closed-Fail, and the
    edge-empty branch of Refine-Closed-Empty): when the static edge filter is
    empty, no edge passes the runtime matcher, so `matchSingleEdge` yields no
    records. Edge mirror of `not_mem_matchNode_of_filter_empty`: a matched edge
    conforms to some catalog edge schema (graph conformance), which survives
    label resolution (`resolveEdgeSchemas_mem_of_conforms`) and the property
    filter (`filterEdgeSchemasByPropCompat_mem_of_conforms`), contradicting
    emptiness. So the empty type former assigned to the edge variable is never
    asked to admit a value. -/
theorem not_mem_matchSingleEdge_of_edge_filter_empty
    (G : PropertyGraph) (Psi : GraphSchemaFull) (site : GraphSite)
    (src : NodeAtom) (rel : EdgeAtom) (dst : NodeAtom) (dir : Direction)
    (PhiPi : PropSchema) (xiL : List EdgeSchemaFull)
    (hGconf : graphConformsSchema G Psi = true)
    (hPrp : PropConstraintTyping rel.props PhiPi)
    (hLbl : xiL = resolveEdgeSchemas Psi rel.labels)
    (hEmpty : (filterEdgeSchemasByPropCompat xiL PhiPi).length = 0)
    (rho : Record)
    (hrho : rho ∈ matchSingleEdge G site src rel dst dir) :
    False := by
  obtain ⟨srcN, ei, dstN, hei, hdstN, hlblE, hprpE, _hlblD, _hprpD, _hform⟩ :=
    matchSingleEdge_mem_form hrho
  obtain ⟨es, hes, hconf⟩ := graphConformsSchema_edge hGconf ei hei
  have hlblmem : es ∈ resolveEdgeSchemas Psi rel.labels :=
    resolveEdgeSchemas_mem_of_conforms G Psi ⟨ei, hei⟩ es rel.labels hes hconf hlblE
  rw [← hLbl] at hlblmem
  have hpropmem : es ∈ filterEdgeSchemasByPropCompat xiL PhiPi :=
    filterEdgeSchemasByPropCompat_mem_of_conforms G site ⟨ei, hei⟩ es xiL rel.props PhiPi
      hlblmem hconf hPrp hprpE
  rw [List.length_eq_zero] at hEmpty
  rw [hEmpty] at hpropmem
  exact List.not_mem_nil es hpropmem

/-- Bridge: a record produced by `matchSingleEdge` comes from some source-node
    match (`matchSingleEdge` flat-maps over `matchNode G site src`). Used to lift
    source-node vacuity to edge vacuity (the source check is consumed inside
    `matchNode_mem_form`, so it is not exposed by `matchSingleEdge_mem_form`). -/
private theorem matchSingleEdge_src_mem {G : PropertyGraph} {site : GraphSite}
    {src : NodeAtom} {rel : EdgeAtom} {dst : NodeAtom} {dir : Direction} {rho : Record}
    (h : rho ∈ matchSingleEdge G site src rel dst dir) :
    ∃ rho_src, rho_src ∈ matchNode G site src := by
  unfold matchSingleEdge at h
  rw [List.mem_flatMap] at h
  obtain ⟨rho_src, hrho_src, _⟩ := h
  exact ⟨rho_src, hrho_src⟩

/-- Source-node analog of `not_mem_matchSingleEdge_of_edge_filter_empty`: when the
    source atom's static schema filter is empty, no source node matches, so
    `matchSingleEdge` (which flat-maps over the source match) is vacuous. -/
theorem not_mem_matchSingleEdge_of_src_filter_empty
    (G : PropertyGraph) (Psi : GraphSchemaFull) (site : GraphSite)
    (src : NodeAtom) (rel : EdgeAtom) (dst : NodeAtom) (dir : Direction)
    (PhiPi : PropSchema) (zetaL : List NodeSchemaFull)
    (hGconf : graphConformsSchema G Psi = true)
    (hPrp : PropConstraintTyping src.props PhiPi)
    (hLbl : zetaL = resolveNodeSchemas Psi src.labels)
    (hEmpty : (filterNodeSchemasByPropCompat zetaL PhiPi).length = 0)
    (rho : Record)
    (hrho : rho ∈ matchSingleEdge G site src rel dst dir) :
    False := by
  obtain ⟨rho_src, hrho_src⟩ := matchSingleEdge_src_mem hrho
  exact not_mem_matchNode_of_filter_empty G Psi site src.var src.labels src.props PhiPi zetaL
    hGconf hPrp hLbl hEmpty rho_src hrho_src

/-- Destination-node analog: when the destination atom's static schema filter is
    empty, the destination check in `matchSingleEdge` (exposed by
    `matchSingleEdge_mem_form`) can never succeed under graph conformance. -/
theorem not_mem_matchSingleEdge_of_dst_filter_empty
    (G : PropertyGraph) (Psi : GraphSchemaFull) (site : GraphSite)
    (src : NodeAtom) (rel : EdgeAtom) (dst : NodeAtom) (dir : Direction)
    (PhiPi : PropSchema) (zetaL : List NodeSchemaFull)
    (hGconf : graphConformsSchema G Psi = true)
    (hPrp : PropConstraintTyping dst.props PhiPi)
    (hLbl : zetaL = resolveNodeSchemas Psi dst.labels)
    (hEmpty : (filterNodeSchemasByPropCompat zetaL PhiPi).length = 0)
    (rho : Record)
    (hrho : rho ∈ matchSingleEdge G site src rel dst dir) :
    False := by
  obtain ⟨srcN, ei, dstN, hei, hdstN, _hlblE, _hprpE, hlblD, hprpD, _hform⟩ :=
    matchSingleEdge_mem_form hrho
  obtain ⟨ns, hns, hconf⟩ := graphConformsSchema_node hGconf dstN hdstN
  have hlblmem : ns ∈ resolveNodeSchemas Psi dst.labels :=
    resolveNodeSchemas_mem_of_conforms G Psi ⟨dstN, hdstN⟩ ns dst.labels hns hconf hlblD
  rw [← hLbl] at hlblmem
  have hpropmem : ns ∈ filterNodeSchemasByPropCompat zetaL PhiPi :=
    filterNodeSchemasByPropCompat_mem_of_conforms G site ⟨dstN, hdstN⟩ ns zetaL dst.props PhiPi
      hlblmem hconf hPrp hprpD
  rw [List.length_eq_zero] at hEmpty
  rw [hEmpty] at hpropmem
  exact List.not_mem_nil ns hpropmem

/-- `nodeRefinedOf` is injective in its schema-list argument (the graph site is
    fixed): two refined node sorts are equal only if their schema lists are. -/
private theorem nodeRefinedOf_inj {G : GraphSite} {ss1 ss2 : List NodeSchemaFull}
    (h : GSort.nodeRefinedOf G ss1 = GSort.nodeRefinedOf G ss2) : ss1 = ss2 := by
  simpa only [GSort.nodeRefinedOf, GSort.mk.injEq, SortShape.single.injEq,
    ExtSort.nodeRefined.injEq, true_and, and_true] using h

/-- Edge mirror of `nodeRefinedOf_inj`. -/
private theorem edgeRefinedOf_inj {G : GraphSite} {ss1 ss2 : List EdgeSchemaFull}
    (h : GSort.edgeRefinedOf G ss1 = GSort.edgeRefinedOf G ss2) : ss1 = ss2 := by
  simpa only [GSort.edgeRefinedOf, GSort.mk.injEq, SortShape.single.injEq,
    ExtSort.edgeRefined.injEq, true_and, and_true] using h

/-- The endpoint argument of `not_mem_matchSingleEdge_of_no_endpoint_triple`,
    factored over the source-set membership: a matched source/edge/destination
    triple whose conforming schemas lie in the refined endpoint sets realizes the
    static endpoint-compatibility check. Reusable both by the single-edge vacuity
    (source set from the atom) and the step vacuity (source set from the prefix). -/
theorem matched_triple_endpointCompat
    (G : PropertyGraph) (srcN ei dstN : Nat)
    (hsrcN : srcN < G.numNodes) (hei : ei < G.numEdges) (hdstN : dstN < G.numNodes)
    (dir : Direction)
    (sN1 : List NodeSchemaFull) (sE2 : List EdgeSchemaFull) (sN3 : List NodeSchemaFull)
    (nsS nsD : NodeSchemaFull) (es2 : EdgeSchemaFull)
    (hnsS_sN1 : nsS ∈ sN1) (hes2_sE2 : es2 ∈ sE2) (hnsD_sN3 : nsD ∈ sN3)
    (hnsSconf : nodeConformsSchema G ⟨srcN, hsrcN⟩ nsS = true)
    (hes2conf : edgeConformsSchema G ⟨ei, hei⟩ es2 = true)
    (hnsDconf : nodeConformsSchema G ⟨dstN, hdstN⟩ nsD = true)
    (hphi : phiD G dir ⟨srcN, hsrcN⟩ ⟨ei, hei⟩ ⟨dstN, hdstN⟩ = true) :
    endpointCompatTriple sN1 sE2 sN3 dir = true := by
  -- the matched endpoints' actual labels equal their conforming schemas' label sets
  have hLS_src : labelSetEq (G.nodeLabels ⟨srcN, hsrcN⟩) nsS.labels = true :=
    labelSetEq_of_nodeConforms hnsSconf
  have hLS_dst : labelSetEq (G.nodeLabels ⟨dstN, hdstN⟩) nsD.labels = true :=
    labelSetEq_of_nodeConforms hnsDconf
  -- so any node-schema conforming to the matched src (resp. dst) is label-matched
  -- by some member of sN1 (resp. sN3)
  have anySN1 : ∀ (sch : NodeSchemaFull), nodeConformsSchema G ⟨srcN, hsrcN⟩ sch = true →
      sN1.any (fun n => labelSetEq n.labels sch.labels) = true := by
    intro sch hsch
    rw [List.any_eq_true]
    exact ⟨nsS, hnsS_sN1, labelSetEq_trans (labelSetEq_symm hLS_src) (labelSetEq_of_nodeConforms hsch)⟩
  have anySN3 : ∀ (sch : NodeSchemaFull), nodeConformsSchema G ⟨dstN, hdstN⟩ sch = true →
      sN3.any (fun n => labelSetEq n.labels sch.labels) = true := by
    intro sch hsch
    rw [List.any_eq_true]
    exact ⟨nsD, hnsD_sN3, labelSetEq_trans (labelSetEq_symm hLS_dst) (labelSetEq_of_nodeConforms hsch)⟩
  -- extract directedness + endpoint conformance from the matched edge's conformance
  have hecAll : edgeConformsSchema G ⟨ei, hei⟩ es2 = true := hes2conf
  unfold edgeConformsSchema at hecAll
  simp only [Bool.and_eq_true] at hecAll
  obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hDirEq⟩, hEndpoint⟩ := hecAll
  have hdir : G.edgeDirected ⟨ei, hei⟩ = es2.isDirected := eq_of_beq hDirEq
  -- the schema triple (sN1, es2, sN3) is endpoint-compatible for dir, so the
  -- static check is `true`, contradicting `hFail`
  have hgoal : endpointCompatTriple sN1 sE2 sN3 dir = true := by
    unfold endpointCompatTriple
    rw [List.any_eq_true]
    refine ⟨es2, hes2_sE2, ?_⟩
    cases hd : G.edgeDirected ⟨ei, hei⟩ with
    | true =>
      have hesDir : es2.isDirected = true := hdir ▸ hd
      rw [if_pos hd, Bool.and_eq_true] at hEndpoint
      obtain ⟨hsEP0, hdEP0⟩ := hEndpoint
      have cRwin : G.src ⟨ei, hei⟩ = (⟨srcN, hsrcN⟩ : Fin G.numNodes) →
          G.dst ⟨ei, hei⟩ = (⟨dstN, hdstN⟩ : Fin G.numNodes) →
          (es2.isDirected && sN1.any (fun n => labelSetEq n.labels es2.srcSchema.labels)
            && sN3.any (fun n => labelSetEq n.labels es2.dstSchema.labels)) = true := by
        intro hse hde
        have h1 := hsEP0; rw [hse] at h1
        have h2 := hdEP0; rw [hde] at h2
        simp [hesDir, anySN1 _ h1, anySN3 _ h2]
      have cLwin : G.src ⟨ei, hei⟩ = (⟨dstN, hdstN⟩ : Fin G.numNodes) →
          G.dst ⟨ei, hei⟩ = (⟨srcN, hsrcN⟩ : Fin G.numNodes) →
          (es2.isDirected && sN1.any (fun n => labelSetEq n.labels es2.dstSchema.labels)
            && sN3.any (fun n => labelSetEq n.labels es2.srcSchema.labels)) = true := by
        intro hse hde
        have h1 := hsEP0; rw [hse] at h1
        have h2 := hdEP0; rw [hde] at h2
        simp [hesDir, anySN1 _ h2, anySN3 _ h1]
      cases dir with
      | right =>
        dsimp only
        simp only [phiD] at hphi
        rw [Bool.and_eq_true, Bool.and_eq_true] at hphi
        obtain ⟨⟨_, hsq⟩, hdq⟩ := hphi
        exact cRwin (eq_of_beq hsq) (eq_of_beq hdq)
      | left =>
        dsimp only
        simp only [phiD] at hphi
        rw [Bool.and_eq_true, Bool.and_eq_true] at hphi
        obtain ⟨⟨_, hsq⟩, hdq⟩ := hphi
        exact cLwin (eq_of_beq hsq) (eq_of_beq hdq)
      | anyDirected =>
        dsimp only
        simp only [phiD] at hphi
        rw [Bool.or_eq_true] at hphi
        rcases hphi with hr | hl
        · rw [Bool.and_eq_true, Bool.and_eq_true] at hr
          obtain ⟨⟨_, hsq⟩, hdq⟩ := hr
          simp [cRwin (eq_of_beq hsq) (eq_of_beq hdq)]
        · rw [Bool.and_eq_true, Bool.and_eq_true] at hl
          obtain ⟨⟨_, hsq⟩, hdq⟩ := hl
          simp [cLwin (eq_of_beq hsq) (eq_of_beq hdq)]
      | undirected =>
        dsimp only
        simp only [phiD] at hphi
        rw [hd] at hphi
        simp at hphi
      | rightOrUndirected =>
        dsimp only
        simp only [phiD] at hphi
        rw [hd] at hphi
        simp only [Bool.not_true, Bool.false_and, Bool.or_false, Bool.true_and] at hphi
        rw [Bool.and_eq_true] at hphi
        obtain ⟨hsq, hdq⟩ := hphi
        simp [cRwin (eq_of_beq hsq) (eq_of_beq hdq)]
      | leftOrUndirected =>
        dsimp only
        simp only [phiD] at hphi
        rw [hd] at hphi
        simp only [Bool.not_true, Bool.false_and, Bool.or_false, Bool.true_and] at hphi
        rw [Bool.and_eq_true] at hphi
        obtain ⟨hsq, hdq⟩ := hphi
        simp [cLwin (eq_of_beq hsq) (eq_of_beq hdq)]
      | any =>
        dsimp only
        simp only [phiD] at hphi
        rw [hd] at hphi
        simp only [Bool.not_true, Bool.false_and, Bool.or_false, Bool.true_and] at hphi
        rw [Bool.or_eq_true] at hphi
        rcases hphi with hr | hl
        · rw [Bool.and_eq_true] at hr
          obtain ⟨hsq, hdq⟩ := hr
          simp [cRwin (eq_of_beq hsq) (eq_of_beq hdq)]
        · rw [Bool.and_eq_true] at hl
          obtain ⟨hsq, hdq⟩ := hl
          simp [cLwin (eq_of_beq hsq) (eq_of_beq hdq)]
    | false =>
      have hesDir : es2.isDirected = false := hdir ▸ hd
      have hcond : ¬(G.edgeDirected ⟨ei, hei⟩ = true) := by rw [hd]; exact Bool.false_ne_true
      rw [if_neg hcond] at hEndpoint
      have cUwin : ((G.src ⟨ei, hei⟩ == (⟨srcN, hsrcN⟩ : Fin G.numNodes))
              && (G.dst ⟨ei, hei⟩ == (⟨dstN, hdstN⟩ : Fin G.numNodes))
            || (G.src ⟨ei, hei⟩ == (⟨dstN, hdstN⟩ : Fin G.numNodes))
              && (G.dst ⟨ei, hei⟩ == (⟨srcN, hsrcN⟩ : Fin G.numNodes))) = true →
          (!es2.isDirected &&
            ((sN1.any (fun n => labelSetEq n.labels es2.srcSchema.labels)
              && sN3.any (fun n => labelSetEq n.labels es2.dstSchema.labels))
            || (sN1.any (fun n => labelSetEq n.labels es2.dstSchema.labels)
              && sN3.any (fun n => labelSetEq n.labels es2.srcSchema.labels)))) = true := by
        intro hpu
        rw [hesDir]
        simp only [Bool.not_false, Bool.true_and]
        rw [Bool.or_eq_true] at hpu hEndpoint
        rcases hpu with hO1 | hO2
        · rw [Bool.and_eq_true] at hO1
          obtain ⟨hsq, hdq⟩ := hO1
          have hse : G.src ⟨ei, hei⟩ = (⟨srcN, hsrcN⟩ : Fin G.numNodes) := eq_of_beq hsq
          have hde : G.dst ⟨ei, hei⟩ = (⟨dstN, hdstN⟩ : Fin G.numNodes) := eq_of_beq hdq
          rcases hEndpoint with hE1 | hE2
          · rw [Bool.and_eq_true] at hE1
            obtain ⟨hsEP, hdEP⟩ := hE1
            rw [hse] at hsEP; rw [hde] at hdEP
            simp [anySN1 _ hsEP, anySN3 _ hdEP]
          · rw [Bool.and_eq_true] at hE2
            obtain ⟨hdEP, hsEP⟩ := hE2
            rw [hde] at hdEP; rw [hse] at hsEP
            simp [anySN1 _ hsEP, anySN3 _ hdEP]
        · rw [Bool.and_eq_true] at hO2
          obtain ⟨hsq, hdq⟩ := hO2
          have hse : G.src ⟨ei, hei⟩ = (⟨dstN, hdstN⟩ : Fin G.numNodes) := eq_of_beq hsq
          have hde : G.dst ⟨ei, hei⟩ = (⟨srcN, hsrcN⟩ : Fin G.numNodes) := eq_of_beq hdq
          rcases hEndpoint with hE1 | hE2
          · rw [Bool.and_eq_true] at hE1
            obtain ⟨hsEP, hdEP⟩ := hE1
            rw [hse] at hsEP; rw [hde] at hdEP
            simp [anySN1 _ hdEP, anySN3 _ hsEP]
          · rw [Bool.and_eq_true] at hE2
            obtain ⟨hdEP, hsEP⟩ := hE2
            rw [hde] at hdEP; rw [hse] at hsEP
            simp [anySN1 _ hdEP, anySN3 _ hsEP]
      cases dir with
      | right =>
        dsimp only
        simp only [phiD] at hphi
        rw [hd] at hphi
        simp at hphi
      | left =>
        dsimp only
        simp only [phiD] at hphi
        rw [hd] at hphi
        simp at hphi
      | anyDirected =>
        dsimp only
        simp only [phiD] at hphi
        rw [hd] at hphi
        simp at hphi
      | undirected =>
        dsimp only
        simp only [phiD] at hphi
        rw [hd] at hphi
        simp only [Bool.not_false, Bool.true_and] at hphi
        exact cUwin hphi
      | rightOrUndirected =>
        dsimp only
        simp only [phiD] at hphi
        rw [hd] at hphi
        simp only [Bool.not_false, Bool.true_and, Bool.false_and, Bool.false_or] at hphi
        simp [cUwin hphi]
      | leftOrUndirected =>
        dsimp only
        simp only [phiD] at hphi
        rw [hd] at hphi
        simp only [Bool.not_false, Bool.true_and, Bool.false_and, Bool.false_or] at hphi
        simp [cUwin hphi]
      | any =>
        dsimp only
        simp only [phiD] at hphi
        rw [hd] at hphi
        simp only [Bool.not_false, Bool.true_and, Bool.false_and, Bool.false_or] at hphi
        simp [cUwin hphi]
  exact hgoal

/-- Closed-fail vacuity (soundness of Refine-Closed-Fail). When the resolved
    endpoint schema sets carry no compatible triple under direction `dir`
    (`endpointCompatTriple = false`), no graph edge can simultaneously match the
    source/edge/destination atoms and satisfy the runtime endpoint predicate
    `phiD`, so `matchSingleEdge` is vacuous. The matched endpoints conform to
    catalog schemas (graph conformance) that survive label resolution and the
    property filter, landing in `sN1`/`sE2`/`sN3`; the matched edge's own declared
    endpoint label sets (recovered from edge conformance) then coincide -- via the
    matched endpoints' labels -- with members of `sN1`/`sN3`, realizing a
    compatible triple for `dir`, contradicting emptiness. -/
theorem not_mem_matchSingleEdge_of_no_endpoint_triple
    (G : PropertyGraph) (Psi : GraphSchemaFull) (site : GraphSite)
    (src : NodeAtom) (rel : EdgeAtom) (dst : NodeAtom) (dir : Direction)
    (PhiPi1 PhiPiE PhiPi3 : PropSchema)
    (sN1 : List NodeSchemaFull) (sE2 : List EdgeSchemaFull) (sN3 : List NodeSchemaFull)
    (hGconf : graphConformsSchema G Psi = true)
    (hPrp1 : PropConstraintTyping src.props PhiPi1)
    (hPrpE : PropConstraintTyping rel.props PhiPiE)
    (hPrp3 : PropConstraintTyping dst.props PhiPi3)
    (hsN1 : sN1 = filterNodeSchemasByPropCompat (resolveNodeSchemas Psi src.labels) PhiPi1)
    (hsE2 : sE2 = filterEdgeSchemasByPropCompat (resolveEdgeSchemas Psi rel.labels) PhiPiE)
    (hsN3 : sN3 = filterNodeSchemasByPropCompat (resolveNodeSchemas Psi dst.labels) PhiPi3)
    (hFail : endpointCompatTriple sN1 sE2 sN3 dir = false)
    (rho : Record)
    (hrho : rho ∈ matchSingleEdge G site src rel dst dir) :
    False := by
  obtain ⟨srcN, ei, dstN, hsrcN, hei, hdstN,
          hsrcLbl, hsrcPrp, hlblE, hprpE, hlblD, hprpD, hphi, _hform⟩ :=
    matchSingleEdge_mem_form' hrho
  -- the three matched elements conform to some catalog schema (graph conformance)
  obtain ⟨nsS, hnsS_Psi, hnsSconf⟩ := graphConformsSchema_node hGconf srcN hsrcN
  obtain ⟨es2, hes2_Psi, hes2conf⟩ := graphConformsSchema_edge hGconf ei hei
  obtain ⟨nsD, hnsD_Psi, hnsDconf⟩ := graphConformsSchema_node hGconf dstN hdstN
  -- those conforming schemas survive label resolution + the property filter, so
  -- they are members of sN1 / sE2 / sN3
  have hnsS_sN1 : nsS ∈ sN1 := by
    rw [hsN1]
    exact filterNodeSchemasByPropCompat_mem_of_conforms G site ⟨srcN, hsrcN⟩ nsS _ src.props PhiPi1
      (resolveNodeSchemas_mem_of_conforms G Psi ⟨srcN, hsrcN⟩ nsS src.labels hnsS_Psi hnsSconf hsrcLbl)
      hnsSconf hPrp1 hsrcPrp
  have hes2_sE2 : es2 ∈ sE2 := by
    rw [hsE2]
    exact filterEdgeSchemasByPropCompat_mem_of_conforms G site ⟨ei, hei⟩ es2 _ rel.props PhiPiE
      (resolveEdgeSchemas_mem_of_conforms G Psi ⟨ei, hei⟩ es2 rel.labels hes2_Psi hes2conf hlblE)
      hes2conf hPrpE hprpE
  have hnsD_sN3 : nsD ∈ sN3 := by
    rw [hsN3]
    exact filterNodeSchemasByPropCompat_mem_of_conforms G site ⟨dstN, hdstN⟩ nsD _ dst.props PhiPi3
      (resolveNodeSchemas_mem_of_conforms G Psi ⟨dstN, hdstN⟩ nsD dst.labels hnsD_Psi hnsDconf hlblD)
      hnsDconf hPrp3 hprpD
  have hgoalEC := matched_triple_endpointCompat G srcN ei dstN hsrcN hei hdstN dir sN1 sE2 sN3 nsS nsD es2
    hnsS_sN1 hes2_sE2 hnsD_sN3 hnsSconf hes2conf hnsDconf hphi
  rw [hgoalEC] at hFail
  exact Bool.noConfusion hFail

-- ============================================================
--  Edge-pattern (Pat-Edge / Pat-Step) conformance: sound cases
--
--  `matchSingleEdge` binds exactly src/edge/dst at the working site. The
--  refinement output schema's domain is those three variables, and each entry
--  admits the matching reference kind (graph-unaware: site-matching only). The
--  edge variable differs from both node variables (join-compatibility forbids a
--  node/edge meet). The core lemma factors the record-form + per-key lookup
--  reasoning; the open/closed/closed-empty cases discharge its hypotheses.
--
--  (The `closed-fail` case is omitted: as written its rule is missing the
--  `S = empty` premise, so it is unsound; see the artifact note.)
-- ============================================================

/-- Membership in a singleton schema is exactly key equality. -/
private theorem singleton_schema_mem (a : Name) (T : GSort) (z : Name) :
    (RecordSchema.mk [(a, T)]).mem z = (a == z) := by
  simp [RecordSchema.mem]

/-- `==` on names (strings) is symmetric. -/
private theorem name_beq_comm (a b : Name) : (a == b) = (b == a) := by
  cases h : a == b
  · cases h2 : b == a
    · rfl
    · rw [eq_of_beq h2] at h; simp at h
  · rw [eq_of_beq h]; simp

/-- Transport a disequality across a key equality. -/
private theorem beq_false_trans {z a b : Name} (hza : (z == a) = true) (hba : (b == a) = false) :
    (b == z) = false := by
  rw [eq_of_beq hza]; exact hba

/-- A node atom is always typed to a singleton schema keyed by its variable. -/
private theorem atomTyping_node_singleton {ctx : TypingCtx} {na : NodeAtom} {Gamma : RecordSchema}
    (h : AtomTyping ctx (.node na) Gamma) : ∃ T, Gamma = RecordSchema.mk [(na.var, T)] := by
  cases h <;> exact ⟨_, rfl⟩

/-- An edge atom is always typed to a singleton schema keyed by its variable. -/
private theorem atomTyping_edge_singleton {ctx : TypingCtx} {ea : EdgeAtom} {Gamma : RecordSchema}
    (h : AtomTyping ctx (.edge ea) Gamma) : ∃ T, Gamma = RecordSchema.mk [(ea.var, T)] := by
  cases h <;> exact ⟨_, rfl⟩

/-- Core edge-pattern conformance: any schema whose domain is exactly the three
    edge-pattern variables and whose entries admit the matching reference kind at
    `site` is conformed to by every `matchSingleEdge` record. -/
private theorem matchSingleEdge_conforms_core
    (G : PropertyGraph) (site : GraphSite) (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
    (GammaRef : RecordSchema)
    (_hrel1 : (rel.var == n1.var) = false) (_hrel2 : (rel.var == n2.var) = false)
    (hdom : ∀ z, GammaRef.mem z = (n1.var == z || rel.var == z || n2.var == z))
    (hVal : ∀ z t, (z, t) ∈ GammaRef.entries →
              ((n1.var == z) = true → ∀ i, RecordSchema.valueAdmissible (Value.nodeRef site i) t = true)
            ∧ ((rel.var == z) = true → ∀ i, RecordSchema.valueAdmissible (Value.edgeRef site i) t = true)
            ∧ ((n2.var == z) = true → ∀ i, RecordSchema.valueAdmissible (Value.nodeRef site i) t = true)) :
    BTConforms (matchSingleEdge G site n1 rel n2 dir) GammaRef := by
  intro rho hrho
  obtain ⟨srcN, ei, dstN, hei, hdstN, _, _, _, _, hform⟩ := matchSingleEdge_mem_form hrho
  subst hform
  refine ⟨?_, ?_⟩
  · -- domain agreement
    intro z
    rw [hdom z]
    simp [Record.mem, Bool.or_assoc]
  · -- value admissibility per entry
    intro z t hzt
    obtain ⟨hv1, hve, hv2⟩ := hVal z t hzt
    have hmemz : GammaRef.mem z = true := RecordSchema.mem_of_entry hzt
    rw [hdom z] at hmemz
    cases hz1 : n1.var == z with
    | true =>
      have hlk : Record.lookup [(n1.var, Value.nodeRef site srcN),
          (rel.var, Value.edgeRef site ei), (n2.var, Value.nodeRef site dstN)] z
          = Value.nodeRef site srcN := by
        simp [Record.lookup, List.find?_cons, hz1]
      rw [hlk]; exact hv1 hz1 srcN
    | false =>
      cases hze : rel.var == z with
      | true =>
        have hlk : Record.lookup [(n1.var, Value.nodeRef site srcN),
            (rel.var, Value.edgeRef site ei), (n2.var, Value.nodeRef site dstN)] z
            = Value.edgeRef site ei := by
          simp [Record.lookup, List.find?_cons, hz1, hze]
        rw [hlk]; exact hve hze ei
      | false =>
        simp only [hz1, hze, Bool.false_or] at hmemz
        have hlk : Record.lookup [(n1.var, Value.nodeRef site srcN),
            (rel.var, Value.edgeRef site ei), (n2.var, Value.nodeRef site dstN)] z
            = Value.nodeRef site dstN := by
          simp [Record.lookup, List.find?_cons, hz1, hze, hmemz]
        rw [hlk]; exact hv2 hmemz dstN

/-- The per-entry value-admissibility obligation for the `closed` edge join,
    factored out of `matchSingleEdge_conforms_closed` so the variable-length
    (group-ref) lifted case can reuse it. Each entry of
    `join.setMany [v1↦N⟨G,…⟩, r2↦E⟨G,…⟩, v3↦N⟨G,…⟩]` admits the matching shape
    (node ref at the endpoints, edge ref at the edge variable). -/
private theorem closed_join_hVal
    (site : GraphSite) (n1 n2 : NodeAtom) (rel : EdgeAtom)
    (TN1 TE TN2 : GSort)
    (sN1' : List NodeSchemaFull) (sE2' : List EdgeSchemaFull) (sN3' : List NodeSchemaFull)
    (hrel1 : (rel.var == n1.var) = false) (hrel2 : (rel.var == n2.var) = false)
    (z : Name) (t : GSort)
    (hzt : (z, t) ∈ (((RecordSchema.mk [(n1.var, TN1)]).join (RecordSchema.mk [(rel.var, TE)])
          |>.join (RecordSchema.mk [(n2.var, TN2)])).setMany
        [(n1.var, GSort.nodeRefinedOf site sN1'),
         (rel.var, GSort.edgeRefinedOf site sE2'),
         (n2.var, GSort.nodeRefinedOf site sN3')]).entries) :
    ((n1.var == z) = true → ∀ i, RecordSchema.valueAdmissible (Value.nodeRef site i) t = true)
  ∧ ((rel.var == z) = true → ∀ i, RecordSchema.valueAdmissible (Value.edgeRef site i) t = true)
  ∧ ((n2.var == z) = true → ∀ i, RecordSchema.valueAdmissible (Value.nodeRef site i) t = true) := by
  rcases RecordSchema.mem_setMany_entries hzt with ⟨b, hb, hzb, hvb⟩ | ⟨hbase, hnone⟩
  · subst hvb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨fun _ i => nodeRef_adm_nodeRefinedOf site i sN1',
             fun hrel => by rw [beq_false_trans hzb hrel1] at hrel; exact Bool.noConfusion hrel,
             fun _ i => nodeRef_adm_nodeRefinedOf site i sN1'⟩
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨fun hn1 => by rw [beq_false_trans hzb (name_beq_comm rel.var n1.var ▸ hrel1)] at hn1; exact Bool.noConfusion hn1,
               fun _ i => edgeRef_adm_edgeRefinedOf site i sE2',
               fun hn2 => by rw [beq_false_trans hzb (name_beq_comm rel.var n2.var ▸ hrel2)] at hn2; exact Bool.noConfusion hn2⟩
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨fun _ i => nodeRef_adm_nodeRefinedOf site i sN3',
                 fun hrel => by rw [beq_false_trans hzb hrel2] at hrel; exact Bool.noConfusion hrel,
                 fun _ i => nodeRef_adm_nodeRefinedOf site i sN3'⟩
        · exact absurd hb (List.not_mem_nil b)
  · exfalso
    have hmemz := RecordSchema.mem_of_entry hbase
    rw [RecordSchema.join_mem, RecordSchema.join_mem,
        singleton_schema_mem, singleton_schema_mem, singleton_schema_mem] at hmemz
    have h1 := hnone (n1.var, GSort.nodeRefinedOf site sN1') (List.mem_cons_self _ _)
    have h2 := hnone (rel.var, GSort.edgeRefinedOf site sE2')
      (List.mem_cons_of_mem _ (List.mem_cons_self _ _))
    have h3 := hnone (n2.var, GSort.nodeRefinedOf site sN3')
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))
    rw [name_beq_comm n1.var z, name_beq_comm rel.var z, name_beq_comm n2.var z] at hmemz
    rw [h1, h2, h3] at hmemz
    exact Bool.noConfusion hmemz

/-- Edge-pattern conformance, `closed` (Refine-Closed, non-empty) case: the
    refinement output `join.setMany [v1↦N⟨G,…⟩, r2↦E⟨G,…⟩, v3↦N⟨G,…⟩]` is conformed
    to by `matchSingleEdge`. Sound regardless of the (unconstrained) refined
    schema lists, since admissibility is graph-unaware (site-matching only). The
    edge variable's distinctness from the node variables is taken as a hypothesis
    (it follows from the rule's `joinCompatible` premises). -/
private theorem matchSingleEdge_conforms_closed
    (G : PropertyGraph) (site : GraphSite) (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
    (TN1 TE TN2 : GSort)
    (sN1' : List NodeSchemaFull) (sE2' : List EdgeSchemaFull) (sN3' : List NodeSchemaFull)
    (hrel1 : (rel.var == n1.var) = false) (hrel2 : (rel.var == n2.var) = false) :
    BTConforms (matchSingleEdge G site n1 rel n2 dir)
      (((RecordSchema.mk [(n1.var, TN1)]).join (RecordSchema.mk [(rel.var, TE)])
          |>.join (RecordSchema.mk [(n2.var, TN2)])).setMany
        [(n1.var, GSort.nodeRefinedOf site sN1'),
         (rel.var, GSort.edgeRefinedOf site sE2'),
         (n2.var, GSort.nodeRefinedOf site sN3')]) := by
  apply matchSingleEdge_conforms_core G site n1 n2 rel dir _ hrel1 hrel2
  · -- domain
    intro z
    rw [RecordSchema.setMany_mem, RecordSchema.join_mem, RecordSchema.join_mem,
        singleton_schema_mem, singleton_schema_mem, singleton_schema_mem]
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    cases n1.var == z <;> cases rel.var == z <;> cases n2.var == z <;> rfl
  · -- value
    intro z t hzt
    exact closed_join_hVal site n1 n2 rel TN1 TE TN2 sN1' sE2' sN3' hrel1 hrel2 z t hzt

/-- `nodeOf G == nodeOf G` reduces to `true`. GSort derives only a structural
    `BEq` (no `LawfulBEq`), so the self-equality does not close by `rfl`/`simp`;
    we unfold one structure level (GSort's derived `==` is `shape==shape && null==null`)
    and bottom out at the `String`-level `site == site` (which is lawful). -/
private theorem nodeOf_beq_self (site : GraphSite) :
    (GSort.nodeOf site == GSort.nodeOf site) = true := by
  unfold GSort.nodeOf
  show (SortShape.single (ExtSort.node site) == SortShape.single (ExtSort.node site))
        && (NullTag.nullable == NullTag.nullable) = true
  rw [Bool.and_eq_true]
  refine ⟨?_, rfl⟩
  show (site == site) = true
  exact beq_self_eq_true site

/-- The self-intersection of an open node type collapses to itself (fast path of
    `sortInter`, `t == t`). Needed for the self-loop entry of the open edge join. -/
private theorem sortInter_nodeOf_self (site : GraphSite) :
    RecordSchema.sortInter (GSort.nodeOf site) (GSort.nodeOf site) = GSort.nodeOf site := by
  unfold RecordSchema.sortInter
  rw [if_pos (nodeOf_beq_self site)]

/-- Lookup in a singleton schema. -/
private theorem singleton_schema_lookup (a : Name) (t : GSort) (z : Name) :
    (RecordSchema.mk [(a, t)]).lookup z = if a == z then some t else none := by
  unfold RecordSchema.lookup
  cases h : a == z with
  | true => simp [List.find?, h]
  | false => simp [List.find?, h]

/-- The per-entry value-admissibility obligation for the `open` edge join,
    factored out of `matchSingleEdge_conforms_open` so the variable-length
    (group-ref) lifted case can reuse it. Each entry of `N⟨G⟩ ⋈ E⟨G⟩ ⋈ N⟨G⟩`
    admits the matching shape; self-loops collapse `sortInter (N⟨G⟩) (N⟨G⟩)` back
    to `N⟨G⟩` (`sortInter_nodeOf_self`). -/
private theorem open_join_hVal
    (site : GraphSite) (n1 n2 : NodeAtom) (rel : EdgeAtom)
    (hrel1 : (rel.var == n1.var) = false) (hrel2 : (rel.var == n2.var) = false)
    (z : Name) (t : GSort)
    (hzt : (z, t) ∈ ((RecordSchema.mk [(n1.var, GSort.nodeOf site)]).join
          (RecordSchema.mk [(rel.var, GSort.edgeOf site)])
          |>.join (RecordSchema.mk [(n2.var, GSort.nodeOf site)])).entries) :
    ((n1.var == z) = true → ∀ i, RecordSchema.valueAdmissible (Value.nodeRef site i) t = true)
  ∧ ((rel.var == z) = true → ∀ i, RecordSchema.valueAdmissible (Value.edgeRef site i) t = true)
  ∧ ((n2.var == z) = true → ∀ i, RecordSchema.valueAdmissible (Value.nodeRef site i) t = true) := by
  rcases RecordSchema.join_entry_cases hzt with
    ⟨t1, hinner, hCmem, ht⟩ | ⟨t1, t2, hinner, hClk, ht⟩ | ⟨t2, hCent, _, ht⟩
  · -- outer onlyIn1: (z,t1) ∈ (A.join B).entries, C.mem z = false, t = t1
    subst ht
    rcases RecordSchema.join_entry_cases hinner with
      ⟨ta, hAent, _, hta⟩ | ⟨ta, tb, hAent, hBlk, _⟩ | ⟨tb, hBent, _, htb⟩
    · -- inner onlyIn1: z = n1.var, t = nodeOf
      subst hta
      have hpair := List.mem_singleton.mp hAent
      rw [Prod.mk.injEq] at hpair
      obtain ⟨hz, hval⟩ := hpair; subst hz; subst hval
      exact ⟨fun _ i => nodeRef_adm_nodeOf site i,
             fun hr => by rw [hrel1] at hr; exact Bool.noConfusion hr,
             fun _ i => nodeRef_adm_nodeOf site i⟩
    · -- inner shared: impossible (B.lookup n1.var = none)
      exfalso
      have hpair := List.mem_singleton.mp hAent
      rw [Prod.mk.injEq] at hpair
      obtain ⟨hz, _⟩ := hpair; subst hz
      simp [singleton_schema_lookup, hrel1] at hBlk
    · -- inner onlyIn2: z = rel.var, t = edgeOf
      subst htb
      have hpair := List.mem_singleton.mp hBent
      rw [Prod.mk.injEq] at hpair
      obtain ⟨hz, hval⟩ := hpair; subst hz; subst hval
      exact ⟨fun hn1 => by rw [name_beq_comm n1.var rel.var, hrel1] at hn1; exact Bool.noConfusion hn1,
             fun _ i => edgeRef_adm_edgeOf site i,
             fun hn2 => by rw [name_beq_comm n2.var rel.var, hrel2] at hn2; exact Bool.noConfusion hn2⟩
  · -- outer shared: C.lookup z = some t2, t = sortInter t1 t2
    rw [singleton_schema_lookup] at hClk
    cases hnz : n2.var == z with
    | false => rw [hnz] at hClk; exact absurd hClk (by simp)
    | true =>
      rw [hnz] at hClk
      have ht2 : t2 = GSort.nodeOf site := (Option.some.inj hClk).symm
      have hzn2 : z = n2.var := (eq_of_beq hnz).symm
      subst hzn2; subst ht2; subst ht
      rcases RecordSchema.join_entry_cases hinner with
        ⟨ta, hAent, _, hta⟩ | ⟨ta, tb, hAent, hBlk, _⟩ | ⟨tb, hBent, _, _⟩
      · -- inner onlyIn1: z = n2.var = n1.var (self-loop), t1 = nodeOf
        have hpair := List.mem_singleton.mp hAent
        rw [Prod.mk.injEq] at hpair
        obtain ⟨_, hval⟩ := hpair; subst hval; subst hta
        rw [sortInter_nodeOf_self site]
        exact ⟨fun _ i => nodeRef_adm_nodeOf site i,
               fun hr => by rw [hrel2] at hr; exact Bool.noConfusion hr,
               fun _ i => nodeRef_adm_nodeOf site i⟩
      · -- inner shared: impossible (B.lookup n2.var = none)
        exfalso
        simp [singleton_schema_lookup, hrel2] at hBlk
      · -- inner onlyIn2: z = n2.var = rel.var, contradicts hrel2
        exfalso
        have hpair := List.mem_singleton.mp hBent
        rw [Prod.mk.injEq] at hpair
        obtain ⟨hz, _⟩ := hpair
        rw [hz] at hrel2
        rw [beq_self_eq_true] at hrel2
        exact Bool.noConfusion hrel2
  · -- outer onlyIn2: z = n2.var, t = nodeOf
    subst ht
    have hpair := List.mem_singleton.mp hCent
    rw [Prod.mk.injEq] at hpair
    obtain ⟨hz, hval⟩ := hpair; subst hz; subst hval
    exact ⟨fun _ i => nodeRef_adm_nodeOf site i,
           fun hr => by rw [hrel2] at hr; exact Bool.noConfusion hr,
           fun _ i => nodeRef_adm_nodeOf site i⟩

/-- Edge-pattern conformance, `open` (Refine-Open) case: the output is the plain
    join of the three open atom types `N⟨G⟩ ⋈ E⟨G⟩ ⋈ N⟨G⟩`, with no refinement.
    Every produced record conforms by graph-unaware admissibility. Self-loops
    (`n1.var = n2.var`) produce a shared entry `sortInter (N⟨G⟩) (N⟨G⟩)`, which
    collapses back to `N⟨G⟩` (`sortInter_nodeOf_self`) and still admits a node ref.
    The edge variable's distinctness from the node variables (`hrel1`/`hrel2`)
    follows from the rule's `joinCompatible` premises. -/
private theorem matchSingleEdge_conforms_open
    (G : PropertyGraph) (site : GraphSite) (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
    (hrel1 : (rel.var == n1.var) = false) (hrel2 : (rel.var == n2.var) = false) :
    BTConforms (matchSingleEdge G site n1 rel n2 dir)
      ((RecordSchema.mk [(n1.var, GSort.nodeOf site)]).join (RecordSchema.mk [(rel.var, GSort.edgeOf site)])
          |>.join (RecordSchema.mk [(n2.var, GSort.nodeOf site)])) := by
  apply matchSingleEdge_conforms_core G site n1 n2 rel dir _ hrel1 hrel2
  · -- domain
    intro z
    rw [RecordSchema.join_mem, RecordSchema.join_mem,
        singleton_schema_mem, singleton_schema_mem, singleton_schema_mem,
        Bool.or_assoc]
  · -- value
    intro z t hzt
    exact open_join_hVal site n1 n2 rel hrel1 hrel2 z t hzt

/-- Edge-pattern conformance, `closedEmpty` (Refine-Closed-Empty) case: when one
    of the three input atom types is the empty type former, the refinement output
    binds every variable to an empty former (admits nothing), so soundness
    requires `matchSingleEdge` to be vacuous. Only the `*ClosedFail` atom rules
    produce an empty former, and each carries the static-filter-empty premise that
    drives the corresponding vacuity lemma; the open/closed atom rules produce
    `nodeOf`/`edgeOf`/`*RefinedOf`, which are not empty formers (contradicting the
    hypothesis). Needs graph conformance (`hCat`). -/
private theorem matchSingleEdge_conforms_closedEmpty
    (ctx : TypingCtx) (G : PropertyGraph) (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
    (Gamma1 Gamma2 Gamma3 GammaRef : RecordSchema)
    (hA1 : AtomTyping ctx (AtomInput.node n1) Gamma1)
    (hA2 : AtomTyping ctx (AtomInput.edge rel) Gamma2)
    (hA3 : AtomTyping ctx (AtomInput.node n2) Gamma3)
    (hCat : ∀ Psi, ctx.schemaMap.lookup ctx.graphSite = some Psi →
              graphConformsSchema G Psi = true)
    (hSomeEmpty :
        (match Gamma1.lookup n1.var with | some t => t.isEmptyFormer | none => false) = true
      ∨ (match Gamma2.lookup rel.var with | some t => t.isEmptyFormer | none => false) = true
      ∨ (match Gamma3.lookup n2.var with | some t => t.isEmptyFormer | none => false) = true) :
    BTConforms (matchSingleEdge G ctx.graphSite n1 rel n2 dir) GammaRef := by
  intro rho hrho
  exfalso
  rcases hSomeEmpty with h | h | h
  · -- source node empty: only nodeClosedFail produces an empty former
    cases hA1 with
    | nodeOpen v labels props hOpen =>
        simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.nodeOf] at h
    | nodeClosed v labels props Psi PhiPi zetaL zetaPrp zetaResult
        hClosed hSchema hPrpTyping hLblFilter hPrpFilter hResult hNonEmpty =>
        simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.nodeRefinedOf] at h
    | nodeClosedFail v labels props Psi PhiPi zetaL zetaPrp
        hClosed hSchema hPrpTyping hLblFilter hPrpFilter hEmpty =>
        exact not_mem_matchSingleEdge_of_src_filter_empty G Psi ctx.graphSite _ rel n2 dir
          PhiPi zetaL (hCat Psi hSchema) hPrpTyping hLblFilter (hPrpFilter ▸ hEmpty) rho hrho
  · -- edge empty: only edgeClosedFail produces an empty former
    cases hA2 with
    | edgeOpen r labels props hOpen =>
        simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.edgeOf] at h
    | edgeClosed r labels props Psi PhiPi xiL xiPrp xiResult
        hClosed hSchema hPrpTyping hLblFilter hPrpFilter hResult hNonEmpty =>
        simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.edgeRefinedOf] at h
    | edgeClosedFail r labels props Psi PhiPi xiL xiPrp
        hClosed hSchema hPrpTyping hLblFilter hPrpFilter hEmpty =>
        exact not_mem_matchSingleEdge_of_edge_filter_empty G Psi ctx.graphSite n1 _ n2 dir
          PhiPi xiL (hCat Psi hSchema) hPrpTyping hLblFilter (hPrpFilter ▸ hEmpty) rho hrho
  · -- destination node empty: only nodeClosedFail produces an empty former
    cases hA3 with
    | nodeOpen v labels props hOpen =>
        simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.nodeOf] at h
    | nodeClosed v labels props Psi PhiPi zetaL zetaPrp zetaResult
        hClosed hSchema hPrpTyping hLblFilter hPrpFilter hResult hNonEmpty =>
        simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.nodeRefinedOf] at h
    | nodeClosedFail v labels props Psi PhiPi zetaL zetaPrp
        hClosed hSchema hPrpTyping hLblFilter hPrpFilter hEmpty =>
        exact not_mem_matchSingleEdge_of_dst_filter_empty G Psi ctx.graphSite n1 rel _ dir
          PhiPi zetaL (hCat Psi hSchema) hPrpTyping hLblFilter (hPrpFilter ▸ hEmpty) rho hrho

/-- Node-atom soundness (the full Atom-Node-* fragment of Thm 6.2): every record
    produced by `matchNode` conforms to the typed atom schema. The open and
    closed-nonempty cases are graph-unaware admissibility; the closed-fail case
    is vacuous under graph conformance (`not_mem_matchNode_of_filter_empty`). The
    catalog graph `G` is assumed to conform to whatever schema the typing context
    assigns its site (`hCat`) -- the standard catalog/schema-map agreement. -/
theorem matchNode_conforms_atom
    (ctx : TypingCtx) (G : PropertyGraph) (na : NodeAtom) (GammaA : RecordSchema)
    (hType : AtomTyping ctx (AtomInput.node na) GammaA)
    (hCat : ∀ Psi, ctx.schemaMap.lookup ctx.graphSite = some Psi →
              graphConformsSchema G Psi = true) :
    BTConforms (matchNode G ctx.graphSite na) GammaA := by
  cases hType with
  | nodeOpen v labels props hOpen =>
      exact matchNode_conforms_nodeOf G ctx.graphSite _
  | nodeClosed v labels props Psi PhiPi zetaL zetaPrp zetaResult
      hClosed hSchema hPrpTyping hLblFilter hPrpFilter hResult hNonEmpty =>
      exact matchNode_conforms_nodeRefinedOf G ctx.graphSite _ zetaResult
  | nodeClosedFail v labels props Psi PhiPi zetaL zetaPrp
      hClosed hSchema hPrpTyping hLblFilter hPrpFilter hEmpty =>
      intro rho hrho
      exact absurd hrho (fun h =>
        not_mem_matchNode_of_filter_empty G Psi ctx.graphSite v labels props PhiPi zetaL
          (hCat Psi hSchema) hPrpTyping hLblFilter (hPrpFilter ▸ hEmpty) rho h)

/-- Graph-aware node-atom conformance (Theorem 6.2, atom-conformance half).
    Every record `matchNode` produces is `RuntimeConfigWF`: the only non-vacuous
    case is the schema-refined (`nodeClosed`) atom, where the matched node's
    property map conforms some schema in the refined set -- exactly the obligation
    `RuntimeConfigWF` carries for a node-refined component. The open
    (`nodeOf`) and empty-former (`nodeEmpty`) atoms have a component type that is
    not `nodeRefinedOf`/`edgeRefinedOf`, so the obligation is vacuous. -/
theorem matchNode_runtimeWF
    (ctx : TypingCtx) (G : PropertyGraph) (na : NodeAtom) (GammaA : RecordSchema)
    (hType : AtomTyping ctx (AtomInput.node na) GammaA)
    (hCat : ∀ Psi, ctx.schemaMap.lookup ctx.graphSite = some Psi →
              graphConformsSchema G Psi = true)
    (rho : Record) (hrho : rho ∈ matchNode G ctx.graphSite na) :
    RuntimeConfigWF G rho GammaA := by
  cases hType with
  | nodeOpen v labels props hOpen =>
      intro x t hlk
      rw [singleton_schema_lookup] at hlk
      split at hlk
      · simp only [Option.some.injEq] at hlk; subst hlk
        refine ⟨?_, ?_⟩
        · intro site ss hcomp _ _ _ _
          simp [GSort.nodeOf, GSort.componentType, GSort.nodeRefinedOf] at hcomp
        · intro site ss hcomp _ _ _ _
          simp [GSort.nodeOf, GSort.componentType, GSort.edgeRefinedOf] at hcomp
      · exact absurd hlk (by simp)
  | nodeClosed v labels props Psi PhiPi zetaL zetaPrp zetaResult
      hClosed hSchema hPrpTyping hLblFilter hPrpFilter hResult hNonEmpty =>
      intro x t hlk
      rw [singleton_schema_lookup] at hlk
      split at hlk
      · rename_i hxv
        simp only [Option.some.injEq] at hlk; subst hlk
        refine ⟨?_, ?_⟩
        · intro site ss hcomp g n hn hlook
          -- componentType of nodeRefinedOf is itself; pin ss = zetaResult
          simp only [GSort.nodeRefinedOf, GSort.componentType, GSort.mk.injEq,
            SortShape.single.injEq, ExtSort.nodeRefined.injEq, true_and, and_true] at hcomp
          obtain ⟨_hsite, hss⟩ := hcomp
          subst hss
          -- the matched record pins rho.lookup (na.var) = nodeRef ctx.graphSite i
          obtain ⟨i, hi, hlbl, hprp, hrec⟩ := matchNode_mem_form' hrho
          subst hrec
          rw [show x = v from (eq_of_beq hxv).symm] at hlook
          simp only [Record.lookup, List.find?, beq_self_eq_true] at hlook
          -- hlook : Value.nodeRef ctx.graphSite i = Value.nodeRef g n
          rw [Value.nodeRef.injEq] at hlook
          obtain ⟨_hg, hin⟩ := hlook
          subst hin
          obtain ⟨ns, hmem, hconf⟩ := graphConformsSchema_node (hCat Psi hSchema) i hi
          refine ⟨ns, ?_, nodeConformsSchema_propMap hconf⟩
          rw [hResult, hPrpFilter]
          exact filterNodeSchemasByPropCompat_mem_of_conforms G ctx.graphSite ⟨i, hi⟩ ns zetaL props PhiPi
            (hLblFilter ▸ resolveNodeSchemas_mem_of_conforms G Psi ⟨i, hi⟩ ns labels hmem hconf hlbl)
            hconf hPrpTyping hprp
        · intro site ss hcomp _ _ _ _
          simp [GSort.nodeRefinedOf, GSort.componentType, GSort.edgeRefinedOf] at hcomp
      · exact absurd hlk (by simp)
  | nodeClosedFail v labels props Psi PhiPi zetaL zetaPrp
      hClosed hSchema hPrpTyping hLblFilter hPrpFilter hEmpty =>
      intro x t hlk
      rw [singleton_schema_lookup] at hlk
      split at hlk
      · simp only [Option.some.injEq] at hlk; subst hlk
        refine ⟨?_, ?_⟩
        · intro site ss hcomp _ _ _ _
          simp [GSort.nodeEmpty, GSort.componentType, GSort.nodeRefinedOf] at hcomp
        · intro site ss hcomp _ _ _ _
          simp [GSort.nodeEmpty, GSort.componentType, GSort.edgeRefinedOf] at hcomp
      · exact absurd hlk (by simp)

/-- Strong graph-aware node-atom conformance. The `RuntimeConfigWFStrong`
    version of `matchNode_runtimeWF`: for the schema-refined (`nodeClosed`) atom,
    *every* catalog schema the matched node conforms to lands in the refined set
    `zetaResult`, via the same label/property filter membership argument
    (`resolveNodeSchemas_mem_of_conforms` + `filterNodeSchemasByPropCompat_mem_of_conforms`).
    Unlike the plain version this needs no `graphConformsSchema` (the conforming
    schema is given, not produced) and no property-map conformance. The open and
    empty-former atoms are vacuous as before. -/
theorem matchNode_runtimeWFStrong
    (ctx : TypingCtx) (G : PropertyGraph) (na : NodeAtom) (GammaA : RecordSchema)
    (hType : AtomTyping ctx (AtomInput.node na) GammaA)
    (Psi : GraphSchemaFull)
    (hPsi : ctx.schemaMap.lookup ctx.graphSite = some Psi)
    (rho : Record) (hrho : rho ∈ matchNode G ctx.graphSite na) :
    RuntimeConfigWFStrong G Psi rho GammaA := by
  cases hType with
  | nodeOpen v labels props hOpen =>
      intro x t hlk
      rw [singleton_schema_lookup] at hlk
      split at hlk
      · simp only [Option.some.injEq] at hlk; subst hlk
        refine ⟨?_, ?_⟩
        · intro site ss hcomp
          simp [GSort.nodeOf, GSort.componentType, GSort.nodeRefinedOf] at hcomp
        · intro site ss hcomp
          simp [GSort.nodeOf, GSort.componentType, GSort.edgeRefinedOf] at hcomp
      · exact absurd hlk (by simp)
  | nodeClosed v labels props Psi' PhiPi zetaL zetaPrp zetaResult
      hClosed hSchema hPrpTyping hLblFilter hPrpFilter hResult hNonEmpty =>
      have hPsiEq : Psi' = Psi := by rw [hSchema] at hPsi; exact Option.some.inj hPsi
      subst hPsiEq
      intro x t hlk
      rw [singleton_schema_lookup] at hlk
      split at hlk
      · rename_i hxv
        simp only [Option.some.injEq] at hlk; subst hlk
        refine ⟨?_, ?_⟩
        · intro site ss hcomp g n hn hlook ns hmem hconf
          simp only [GSort.nodeRefinedOf, GSort.componentType, GSort.mk.injEq,
            SortShape.single.injEq, ExtSort.nodeRefined.injEq, true_and, and_true] at hcomp
          obtain ⟨_hsite, hss⟩ := hcomp
          subst hss
          obtain ⟨i, hi, hlbl, hprp, hrec⟩ := matchNode_mem_form' hrho
          subst hrec
          rw [show x = v from (eq_of_beq hxv).symm] at hlook
          simp only [Record.lookup, List.find?, beq_self_eq_true] at hlook
          rw [Value.nodeRef.injEq] at hlook
          obtain ⟨_hg, hin⟩ := hlook
          subst hin
          rw [hResult, hPrpFilter]
          exact filterNodeSchemasByPropCompat_mem_of_conforms G ctx.graphSite ⟨i, hi⟩ ns zetaL props PhiPi
            (hLblFilter ▸ resolveNodeSchemas_mem_of_conforms G Psi' ⟨i, hi⟩ ns labels hmem hconf hlbl)
            hconf hPrpTyping hprp
        · intro site ss hcomp
          simp [GSort.nodeRefinedOf, GSort.componentType, GSort.edgeRefinedOf] at hcomp
      · exact absurd hlk (by simp)
  | nodeClosedFail v labels props Psi' PhiPi zetaL zetaPrp
      hClosed hSchema hPrpTyping hLblFilter hPrpFilter hEmpty =>
      intro x t hlk
      rw [singleton_schema_lookup] at hlk
      split at hlk
      · simp only [Option.some.injEq] at hlk; subst hlk
        refine ⟨?_, ?_⟩
        · intro site ss hcomp
          simp [GSort.nodeEmpty, GSort.componentType, GSort.nodeRefinedOf] at hcomp
        · intro site ss hcomp
          simp [GSort.nodeEmpty, GSort.componentType, GSort.edgeRefinedOf] at hcomp
      · exact absurd hlk (by simp)

/-- The matched triple is endpoint-compatible. For a `matchSingleEdge` match
    (source `srcN`, edge `ei`, destination `dstN`, satisfying `phiD`), the matched
    elements' own conforming schemas `(nsS, es2, nsD)` form a compatible triple
    under `dir` (`tripleCompat = true`). This is the positive (per-triple) form of
    the `closedFail` endpoint reasoning: the matched edge's declared endpoint label
    sets coincide -- through the matched nodes' labels -- with `nsS`/`nsD`. It is
    what places a matched node's schema in the endpoint-compatible projection
    `refineSrc/Edge/DstByCompat` that the (pinned) `closed` rule assigns. -/
private theorem tripleCompat_of_matched
    (G : PropertyGraph) (srcN ei dstN : Nat)
    (hsrcN : srcN < G.numNodes) (hei : ei < G.numEdges) (hdstN : dstN < G.numNodes)
    (dir : Direction) (nsS nsD : NodeSchemaFull) (es2 : EdgeSchemaFull)
    (hnsSconf : nodeConformsSchema G ⟨srcN, hsrcN⟩ nsS = true)
    (hnsDconf : nodeConformsSchema G ⟨dstN, hdstN⟩ nsD = true)
    (hes2conf : edgeConformsSchema G ⟨ei, hei⟩ es2 = true)
    (hphi : phiD G dir ⟨srcN, hsrcN⟩ ⟨ei, hei⟩ ⟨dstN, hdstN⟩ = true) :
    tripleCompat nsS es2 nsD dir = true := by
  have hLS_src : labelSetEq (G.nodeLabels ⟨srcN, hsrcN⟩) nsS.labels = true :=
    labelSetEq_of_nodeConforms hnsSconf
  have hLS_dst : labelSetEq (G.nodeLabels ⟨dstN, hdstN⟩) nsD.labels = true :=
    labelSetEq_of_nodeConforms hnsDconf
  have lsSrc : ∀ sch : NodeSchemaFull, nodeConformsSchema G ⟨srcN, hsrcN⟩ sch = true →
      labelSetEq nsS.labels sch.labels = true :=
    fun sch hsch => labelSetEq_trans (labelSetEq_symm hLS_src) (labelSetEq_of_nodeConforms hsch)
  have lsDst : ∀ sch : NodeSchemaFull, nodeConformsSchema G ⟨dstN, hdstN⟩ sch = true →
      labelSetEq nsD.labels sch.labels = true :=
    fun sch hsch => labelSetEq_trans (labelSetEq_symm hLS_dst) (labelSetEq_of_nodeConforms hsch)
  have hecAll : edgeConformsSchema G ⟨ei, hei⟩ es2 = true := hes2conf
  unfold edgeConformsSchema at hecAll
  simp only [Bool.and_eq_true] at hecAll
  obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hDirEq⟩, hEndpoint⟩ := hecAll
  have hdir : G.edgeDirected ⟨ei, hei⟩ = es2.isDirected := eq_of_beq hDirEq
  unfold tripleCompat
  cases hd : G.edgeDirected ⟨ei, hei⟩ with
  | true =>
    have hesDir : es2.isDirected = true := hdir ▸ hd
    rw [if_pos hd, Bool.and_eq_true] at hEndpoint
    obtain ⟨hsEP0, hdEP0⟩ := hEndpoint
    have cRwin : G.src ⟨ei, hei⟩ = (⟨srcN, hsrcN⟩ : Fin G.numNodes) →
        G.dst ⟨ei, hei⟩ = (⟨dstN, hdstN⟩ : Fin G.numNodes) →
        (es2.isDirected && labelSetEq nsS.labels es2.srcSchema.labels
          && labelSetEq nsD.labels es2.dstSchema.labels) = true := by
      intro hse hde
      have h1 := hsEP0; rw [hse] at h1
      have h2 := hdEP0; rw [hde] at h2
      simp [hesDir, lsSrc _ h1, lsDst _ h2]
    have cLwin : G.src ⟨ei, hei⟩ = (⟨dstN, hdstN⟩ : Fin G.numNodes) →
        G.dst ⟨ei, hei⟩ = (⟨srcN, hsrcN⟩ : Fin G.numNodes) →
        (es2.isDirected && labelSetEq nsS.labels es2.dstSchema.labels
          && labelSetEq nsD.labels es2.srcSchema.labels) = true := by
      intro hse hde
      have h1 := hsEP0; rw [hse] at h1
      have h2 := hdEP0; rw [hde] at h2
      simp [hesDir, lsSrc _ h2, lsDst _ h1]
    cases dir with
    | right =>
      simp only [phiD] at hphi
      rw [Bool.and_eq_true, Bool.and_eq_true] at hphi
      obtain ⟨⟨_, hsq⟩, hdq⟩ := hphi
      exact cRwin (eq_of_beq hsq) (eq_of_beq hdq)
    | left =>
      simp only [phiD] at hphi
      rw [Bool.and_eq_true, Bool.and_eq_true] at hphi
      obtain ⟨⟨_, hsq⟩, hdq⟩ := hphi
      exact cLwin (eq_of_beq hsq) (eq_of_beq hdq)
    | anyDirected =>
      simp only [phiD] at hphi
      rw [Bool.or_eq_true] at hphi
      rcases hphi with hr | hl
      · rw [Bool.and_eq_true, Bool.and_eq_true] at hr
        obtain ⟨⟨_, hsq⟩, hdq⟩ := hr
        simp [cRwin (eq_of_beq hsq) (eq_of_beq hdq)]
      · rw [Bool.and_eq_true, Bool.and_eq_true] at hl
        obtain ⟨⟨_, hsq⟩, hdq⟩ := hl
        simp [cLwin (eq_of_beq hsq) (eq_of_beq hdq)]
    | undirected =>
      simp only [phiD] at hphi; rw [hd] at hphi; simp at hphi
    | rightOrUndirected =>
      simp only [phiD] at hphi
      rw [hd] at hphi
      simp only [Bool.not_true, Bool.false_and, Bool.or_false, Bool.true_and] at hphi
      rw [Bool.and_eq_true] at hphi
      obtain ⟨hsq, hdq⟩ := hphi
      simp [cRwin (eq_of_beq hsq) (eq_of_beq hdq)]
    | leftOrUndirected =>
      simp only [phiD] at hphi
      rw [hd] at hphi
      simp only [Bool.not_true, Bool.false_and, Bool.or_false, Bool.true_and] at hphi
      rw [Bool.and_eq_true] at hphi
      obtain ⟨hsq, hdq⟩ := hphi
      simp [cLwin (eq_of_beq hsq) (eq_of_beq hdq)]
    | any =>
      simp only [phiD] at hphi
      rw [hd] at hphi
      simp only [Bool.not_true, Bool.false_and, Bool.or_false, Bool.true_and] at hphi
      rw [Bool.or_eq_true] at hphi
      rcases hphi with hr | hl
      · rw [Bool.and_eq_true] at hr
        obtain ⟨hsq, hdq⟩ := hr
        simp [cRwin (eq_of_beq hsq) (eq_of_beq hdq)]
      · rw [Bool.and_eq_true] at hl
        obtain ⟨hsq, hdq⟩ := hl
        simp [cLwin (eq_of_beq hsq) (eq_of_beq hdq)]
  | false =>
    have hesDir : es2.isDirected = false := hdir ▸ hd
    have hcond : ¬(G.edgeDirected ⟨ei, hei⟩ = true) := by rw [hd]; exact Bool.false_ne_true
    rw [if_neg hcond] at hEndpoint
    have cUwin : ((G.src ⟨ei, hei⟩ == (⟨srcN, hsrcN⟩ : Fin G.numNodes))
            && (G.dst ⟨ei, hei⟩ == (⟨dstN, hdstN⟩ : Fin G.numNodes))
          || (G.src ⟨ei, hei⟩ == (⟨dstN, hdstN⟩ : Fin G.numNodes))
            && (G.dst ⟨ei, hei⟩ == (⟨srcN, hsrcN⟩ : Fin G.numNodes))) = true →
        (!es2.isDirected &&
          ((labelSetEq nsS.labels es2.srcSchema.labels && labelSetEq nsD.labels es2.dstSchema.labels)
          || (labelSetEq nsS.labels es2.dstSchema.labels && labelSetEq nsD.labels es2.srcSchema.labels))) = true := by
      intro hpu
      rw [hesDir]
      simp only [Bool.not_false, Bool.true_and]
      rw [Bool.or_eq_true] at hpu hEndpoint
      rcases hpu with hO1 | hO2
      · rw [Bool.and_eq_true] at hO1
        obtain ⟨hsq, hdq⟩ := hO1
        have hse : G.src ⟨ei, hei⟩ = (⟨srcN, hsrcN⟩ : Fin G.numNodes) := eq_of_beq hsq
        have hde : G.dst ⟨ei, hei⟩ = (⟨dstN, hdstN⟩ : Fin G.numNodes) := eq_of_beq hdq
        rcases hEndpoint with hE1 | hE2
        · rw [Bool.and_eq_true] at hE1
          obtain ⟨hsEP, hdEP⟩ := hE1
          rw [hse] at hsEP; rw [hde] at hdEP
          simp [lsSrc _ hsEP, lsDst _ hdEP]
        · rw [Bool.and_eq_true] at hE2
          obtain ⟨hdEP, hsEP⟩ := hE2
          rw [hde] at hdEP; rw [hse] at hsEP
          simp [lsSrc _ hsEP, lsDst _ hdEP]
      · rw [Bool.and_eq_true] at hO2
        obtain ⟨hsq, hdq⟩ := hO2
        have hse : G.src ⟨ei, hei⟩ = (⟨dstN, hdstN⟩ : Fin G.numNodes) := eq_of_beq hsq
        have hde : G.dst ⟨ei, hei⟩ = (⟨srcN, hsrcN⟩ : Fin G.numNodes) := eq_of_beq hdq
        rcases hEndpoint with hE1 | hE2
        · rw [Bool.and_eq_true] at hE1
          obtain ⟨hsEP, hdEP⟩ := hE1
          rw [hse] at hsEP; rw [hde] at hdEP
          simp [lsSrc _ hdEP, lsDst _ hsEP]
        · rw [Bool.and_eq_true] at hE2
          obtain ⟨hdEP, hsEP⟩ := hE2
          rw [hde] at hdEP; rw [hse] at hsEP
          simp [lsSrc _ hdEP, lsDst _ hsEP]
    cases dir with
    | right => simp only [phiD] at hphi; rw [hd] at hphi; simp at hphi
    | left => simp only [phiD] at hphi; rw [hd] at hphi; simp at hphi
    | anyDirected => simp only [phiD] at hphi; rw [hd] at hphi; simp at hphi
    | undirected =>
      simp only [phiD] at hphi
      rw [hd] at hphi
      simp only [Bool.not_false, Bool.true_and] at hphi
      exact cUwin hphi
    | rightOrUndirected =>
      simp only [phiD] at hphi
      rw [hd] at hphi
      simp only [Bool.not_false, Bool.true_and, Bool.false_and, Bool.false_or] at hphi
      simp [cUwin hphi]
    | leftOrUndirected =>
      simp only [phiD] at hphi
      rw [hd] at hphi
      simp only [Bool.not_false, Bool.true_and, Bool.false_and, Bool.false_or] at hphi
      simp [cUwin hphi]
    | any =>
      simp only [phiD] at hphi
      rw [hd] at hphi
      simp only [Bool.not_false, Bool.true_and, Bool.false_and, Bool.false_or] at hphi
      simp [cUwin hphi]

/-- Property access on closed (schema-refined) graphs yields a value admissible
    for the schema-derived (nullable) property type (Paper: E-PropAccess-Schema,
    H-PropType-Schema). De-axiomatized: the receiver `x` has type `tx`; in either
    the node- or edge-refined mode the result is the corresponding nullable
    schema fold. The `Null`/out-of-bounds/list-receiver branches are immediate
    because the fold is nullable; the conforming-element branch uses the
    fold-admissibility lemmas (with conformance supplied by `RuntimeConfigWF`),
    and a kind-mismatched receiver contradicts `htx`. -/
theorem propAccess_admissible_schema
    (G : PropertyGraph) (site : GraphSite) (rho : Record)
    (x k : Name) (tx resultTy : GSort)
    (nodeSchemas : List NodeSchemaFull) (edgeSchemas : List EdgeSchemaFull)
    (htx : RecordSchema.valueAdmissible (rho.lookup x) tx = true)
    (hcase :
      (tx.componentType = GSort.nodeRefinedOf site nodeSchemas ∧
        resultTy = propTypeOfNodeSchemas nodeSchemas k ∧
        ∀ (g : GraphSite) (n : Nat) (hn : n < G.numNodes),
          rho.lookup x = Value.nodeRef g n →
          ∃ ns, ns ∈ nodeSchemas ∧
            propMapConformsSchema (G.nodeProps ⟨n, hn⟩) ns.propSchema = true)
      ∨
      (tx.componentType = GSort.edgeRefinedOf site edgeSchemas ∧
        resultTy = propTypeOfEdgeSchemas edgeSchemas k ∧
        ∀ (g : GraphSite) (ed : Nat) (he : ed < G.numEdges),
          rho.lookup x = Value.edgeRef g ed →
          ∃ es, es ∈ edgeSchemas ∧
            propMapConformsSchema (G.edgeProps ⟨ed, he⟩) es.propSchema = true)) :
    RecordSchema.valueAdmissible
      (evalExpr G site rho (.propAccess x k)) resultTy = true := by
  have hnull : RecordSchema.valueAdmissible Value.null resultTy = true := by
    rcases hcase with ⟨_, hres, _⟩ | ⟨_, hres, _⟩
    · rw [hres]
      exact scalarUnionType_admits_null (propTypeOfNodeSchemas_scalarUnion nodeSchemas k)
    · rw [hres]
      exact scalarUnionType_admits_null (propTypeOfEdgeSchemas_scalarUnion edgeSchemas k)
  simp only [evalExpr]
  cases hv : rho.lookup x with
  | nodeRef g n =>
      dsimp only
      by_cases hn : n < G.numNodes
      · rw [dif_pos hn]
        rcases hcase with ⟨_, hres, hconf⟩ | ⟨hcomp, _, _⟩
        · rw [hres]
          obtain ⟨ns, hmem, hpm⟩ := hconf g n hn hv
          exact propTypeOfNodeSchemas_mem_admissible nodeSchemas hpm k hmem
        · rw [hv] at htx
          exact absurd htx (nodeRef_not_edgeComp hcomp)
      · rw [dif_neg hn]; exact hnull
  | edgeRef g ed =>
      dsimp only
      by_cases he : ed < G.numEdges
      · rw [dif_pos he]
        rcases hcase with ⟨hcomp, _, _⟩ | ⟨_, hres, hconf⟩
        · rw [hv] at htx
          exact absurd htx (edgeRef_not_nodeComp hcomp)
        · rw [hres]
          obtain ⟨es, hmem, hpm⟩ := hconf g ed he hv
          exact propTypeOfEdgeSchemas_mem_admissible edgeSchemas hpm k hmem
      · rw [dif_neg he]; exact hnull
  | prim p => dsimp only; exact hnull
  | null => dsimp only; exact hnull
  | list l => dsimp only; exact hnull

-- ============================================================
--  Expression Soundness (Theorem 6.1) -- proved via helpers
-- ============================================================

private theorem bool_admissible_boolN (b : Bool) :
    RecordSchema.valueAdmissible (Value.ofBool b) GSort.boolN = true := by
  unfold RecordSchema.valueAdmissible
  simp [GSort.boolN, Value.ofBool, Value.hasExtSort, PrimValue.hasSort]

private theorem null_admissible_boolN :
    RecordSchema.valueAdmissible Value.null GSort.boolN = true := rfl

/-- Predicate typings conclude at the boolean sorts. -/
private theorem predTyping_type_shape {ctx : TypingCtx} {Ctx : RecordSchema}
    {box : AggDepth} {hat : RefCtx}
    {phi : Pred} {t : GSort} {omega1 : VarSet}
    (h : PredTyping ctx Ctx box hat phi t omega1) :
    t = GSort.bool ∨ t = GSort.boolN := by
  cases h with
  | true => exact Or.inl rfl
  | false => exact Or.inl rfl
  | relOp => exact Or.inr rfl
  | not => exact Or.inr rfl
  | and => exact Or.inr rfl
  | or => exact Or.inr rfl
  | isNull => exact Or.inl rfl

/-- Predicates typed at the non-nullable boolean sort always evaluate to a
    truth value (only the Kleene-null-propagating rules type at Bool?). -/
private theorem predTyping_bool_some {ctx : TypingCtx} {Ctx : RecordSchema}
    {box : AggDepth} {hat : RefCtx}
    {phi : Pred} {omega1 : VarSet}
    (h : PredTyping ctx Ctx box hat phi GSort.bool omega1)
    (G : PropertyGraph) (site : GraphSite) (rho : Record) :
    ∃ b, evalPred G site rho phi = some b := by
  cases h with
  | true => exact ⟨true, rfl⟩
  | false => exact ⟨false, rfl⟩
  | isNull e => exact ⟨_, rfl⟩

theorem expressionSoundness
    (ctx : TypingCtx) (Gamma : RecordSchema) (box : AggDepth) (hat : RefCtx)
    (e : Expr) (tau : GSort) (omega' : VarSet)
    (hType : ExprTyping ctx Gamma box hat e tau omega')
    (rho : Record) (G : PropertyGraph)
    (hConf : RecordConforms rho Gamma)
    (hWF : GraphValuesWF G)
    (hRuntimeWF : RuntimeConfigWF G rho Gamma)
    (_hGraph : ctx.catalog.lookup ctx.graphSite = some G) :
    RecordSchema.valueAdmissible (evalExpr G ctx.graphSite rho e) tau = true := by
  induction hType using ExprTyping.inductionOpaque
  case pred =>
    rename_i phi tP omega1 hp
    simp only [evalExpr]
    cases hpv : evalPred G ctx.graphSite rho phi with
    | some b =>
      rcases predTyping_type_shape hp with rfl | rfl
      · exact bool_admissible_bool b
      · exact bool_admissible_boolN b
    | none =>
      rcases predTyping_type_shape hp with rfl | rfl
      · obtain ⟨b, hb⟩ := predTyping_bool_some hp G ctx.graphSite rho
        rw [hb] at hpv
        exact Option.noConfusion hpv
      · exact null_admissible_boolN
  case constInt =>
    rename_i n
    simp only [evalExpr, evalLiteral]
    exact int_admissible_int n
  case constString =>
    rename_i s
    simp only [evalExpr, evalLiteral]
    exact string_admissible_string s
  case constBool =>
    rename_i b
    simp only [evalExpr, evalLiteral]
    exact bool_admissible_bool b
  case constNull =>
    simp only [evalExpr]
    exact null_admissible_nullSort
  case var =>
    rename_i x tau hLookup
    simp only [evalExpr]
    exact conform_lookup rho Gamma x tau hConf hLookup
  case arithOp =>
    simp only [evalExpr]
    exact evalArith_admissible _ _ _
  case propAccessOpen =>
    exact propAccess_admissible_anyScalarN G ctx.graphSite rho _ _ hWF
  case propAccessSchema x k tx resultTy nodeSchemas edgeSchemas hLookup _hClosed hRefine =>
    have htx : RecordSchema.valueAdmissible (rho.lookup x) tx = true :=
      conform_lookup rho Gamma x tx hConf hLookup
    apply propAccess_admissible_schema G ctx.graphSite rho x k tx resultTy
      nodeSchemas edgeSchemas htx
    rcases hRefine with ⟨hcomp, hres⟩ | ⟨hcomp, hres⟩
    · refine Or.inl ⟨hcomp, hres, ?_⟩
      intro g n hn hlk
      exact (hRuntimeWF x tx hLookup).1 ctx.graphSite nodeSchemas hcomp g n hn hlk
    · refine Or.inr ⟨hcomp, hres, ?_⟩
      intro g ed he hlk
      exact (hRuntimeWF x tx hLookup).2 ctx.graphSite edgeSchemas hcomp g ed he hlk
  case propAccessListOpen =>
    exact propAccess_admissible_anyScalarN G ctx.graphSite rho _ _ hWF
  case propAccessListClosed x k tx resultTy nodeSchemas edgeSchemas hLookup _hIsList _hClosed hRefine =>
    have htx : RecordSchema.valueAdmissible (rho.lookup x) tx = true :=
      conform_lookup rho Gamma x tx hConf hLookup
    apply propAccess_admissible_schema G ctx.graphSite rho x k tx resultTy
      nodeSchemas edgeSchemas htx
    rcases hRefine with ⟨hcomp, hres⟩ | ⟨hcomp, hres⟩
    · refine Or.inl ⟨hcomp, hres, ?_⟩
      intro g n hn hlk
      exact (hRuntimeWF x tx hLookup).1 ctx.graphSite nodeSchemas hcomp g n hn hlk
    · refine Or.inr ⟨hcomp, hres, ?_⟩
      intro g ed he hlk
      exact (hRuntimeWF x tx hLookup).2 ctx.graphSite edgeSchemas hcomp g ed he hlk
  case countSingleton =>
    exact agg_count_admissible G ctx.graphSite rho _ _
  case aggSingleton =>
    exact agg_admissible_intN G ctx.graphSite rho _ _ _
  case countGroup =>
    exact agg_count_admissible G ctx.graphSite rho _ _
  case aggGroup =>
    exact agg_admissible_intN G ctx.graphSite rho _ _ _
  case subsume =>
    rename_i _ty1 hSub ih
    exact admissible_mono _ _ _ ih hSub

/-- Expression Soundness (Thm 6.1) with only paper-level well-formedness
    hypotheses: instead of assuming `RuntimeConfigWF` directly, assume the
    paper's Graph Conformance (Def 2.3) and that any schema-refined component
    types in the record schema use the full catalog schema lists (the
    unlabeled/unfiltered atom fragment). This shows Thm 6.1's runtime-config
    hypothesis is realizable from standard conditions, not an ad hoc assumption.
    The general label/property-filtered case is closed by Pattern Soundness. -/
theorem expressionSoundness_graphConforms
    (ctx : TypingCtx) (Gamma : RecordSchema) (box : AggDepth) (hat : RefCtx)
    (e : Expr) (tau : GSort) (omega' : VarSet)
    (hType : ExprTyping ctx Gamma box hat e tau omega')
    (rho : Record) (G : PropertyGraph) (Psi : GraphSchemaFull)
    (hConf : RecordConforms rho Gamma)
    (hWF : GraphValuesWF G)
    (hGraphConf : graphConformsSchema G Psi = true)
    (hNodeFull : ∀ x t site ss, Gamma.lookup x = some t →
        t.componentType = GSort.nodeRefinedOf site ss → ss = Psi.nodeSchemas)
    (hEdgeFull : ∀ x t site ss, Gamma.lookup x = some t →
        t.componentType = GSort.edgeRefinedOf site ss → ss = Psi.edgeSchemas)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G) :
    RecordSchema.valueAdmissible (evalExpr G ctx.graphSite rho e) tau = true :=
  expressionSoundness ctx Gamma box hat e tau omega' hType rho G hConf hWF
    (runtimeConfigWF_of_graphConforms hGraphConf hNodeFull hEdgeFull) hGraph

/-- A node/edge meet is bottom: `sortInter` of an (open or refined) node type and
    an (open or refined) edge type falls through to `botSort` (no common element
    kind). These are exactly the four pairings that arise from the open/closed
    refinement rules; both reduce by `rfl` (cross-constructor `==` is `false`). -/
private theorem sortInter_nodeOf_edgeOf_isBot (site : GraphSite) :
    (RecordSchema.sortInter (GSort.nodeOf site) (GSort.edgeOf site)).isBot = true := rfl

private theorem sortInter_nodeRefinedOf_edgeRefinedOf_isBot
    (site : GraphSite) (sN : List NodeSchemaFull) (sE : List EdgeSchemaFull) :
    (RecordSchema.sortInter (GSort.nodeRefinedOf site sN) (GSort.edgeRefinedOf site sE)).isBot
      = true := rfl

private theorem sortInter_edgeOf_nodeOf_isBot (site : GraphSite) :
    (RecordSchema.sortInter (GSort.edgeOf site) (GSort.nodeOf site)).isBot = true := rfl

private theorem sortInter_edgeRefinedOf_nodeRefinedOf_isBot
    (site : GraphSite) (sE : List EdgeSchemaFull) (sN : List NodeSchemaFull) :
    (RecordSchema.sortInter (GSort.edgeRefinedOf site sE) (GSort.nodeRefinedOf site sN)).isBot
      = true := rfl

/-- Edge-variable distinctness from join-compatibility: if two singleton schemas
    `[a ↦ t1]` and `[b ↦ t2]` are join-compatible but their types have a bottom
    meet, then `a ≠ b` (a shared variable would force the meet to be checked,
    failing the `!isBot` conjunct). This discharges the `rel.var ≠ n1.var/n2.var`
    hypotheses (`hrel1`/`hrel2`) of the edge conformance lemmas from the
    `joinCompatible` premises of the `RefinementTyping` rules: a node type and an
    edge type always have a bottom meet (`sortInter_*_isBot`). -/
private theorem joinCompatible_singleton_distinct
    (a b : Name) (t1 t2 : GSort)
    (hbot : (RecordSchema.sortInter t1 t2).isBot = true)
    (hjc : (RecordSchema.mk [(a, t1)]).joinCompatible (RecordSchema.mk [(b, t2)]) = true) :
    (b == a) = false := by
  cases hba : b == a with
  | false => rfl
  | true =>
    exfalso
    have hashared : a ∈ (RecordSchema.mk [(a, t1)]).dom.filter
        (fun x => (RecordSchema.mk [(b, t2)]).dom.any (fun y => y == x)) := by
      simp [RecordSchema.dom, hba]
    unfold RecordSchema.joinCompatible at hjc
    have hpred := List.all_eq_true.mp hjc a hashared
    rw [singleton_schema_lookup, singleton_schema_lookup] at hpred
    simp [beq_self_eq_true, hba, hbot] at hpred

/-- General-schema version of `joinCompatible_singleton_distinct`: for an
    arbitrary left schema `Gamma1` (not just a singleton), if `Gamma1` and
    `GammaE` are join-compatible and the variable `v1` of `Gamma1` carries a type
    whose meet with `GammaE`'s `r`-type is bottom, then `r ≠ v1`. Used to derive
    `rel.var ≠ v1` for a step, where `v1` is the prefix tail (a node type) and `r`
    is the fresh edge variable (an edge type), so their meet is bottom. -/
private theorem joinCompatible_lookup_distinct {Gamma1 GammaE : RecordSchema}
    {v1 r : Name} {t1 t2 : GSort}
    (hjc : Gamma1.joinCompatible GammaE = true)
    (h1 : Gamma1.lookup v1 = some t1) (h2 : GammaE.lookup r = some t2)
    (hbot : (RecordSchema.sortInter t1 t2).isBot = true) :
    (r == v1) = false := by
  cases hrv : r == v1 with
  | false => rfl
  | true =>
    exfalso
    have hrv' : r = v1 := eq_of_beq hrv
    subst hrv'
    obtain ⟨hbf, _⟩ := RecordSchema.joinCompatible_meet hjc h1 h2
    rw [hbot] at hbf
    exact Bool.noConfusion hbf

-- ============================================================
--  Variable-length / quantified path soundness (Thm 6.2, paths)
--
--  matchVarLengthPath / matchRangePath bind the edge variable to a LIST of edge
--  refs (`.ofList`), and the source/target node variables to node refs -- to be
--  conformed against the `liftToGroupRef` (list) refinement of the base schema.
-- ============================================================

/-- `asList` recovers the underlying list from `ofList` (uses the existing
    `ValueList.toList_ofList` round-trip). -/
theorem Value.asList_ofList (vs : List Value) :
    (Value.ofList vs).asList = some vs := by
  simp [Value.ofList, Value.asList, ValueList.toList_ofList]

/-- Edge-list conformance is trivial: `valueAdmissible` for a `liftToList` (group-ref)
    type only checks that the value is a list -- it ignores the element types
    entirely. So any `ofList _` (which the path semantics always binds the edge
    variable to) conforms to the lifted edge type, regardless of its contents.
    This is what makes the variable-length / quantified edge-variable binding
    sound without tracking the produced edge refs. -/
theorem ofList_adm_liftToList (edges : List Value) (t : GSort) :
    RecordSchema.valueAdmissible (Value.ofList edges) (GSort.liftToList t) = true := by
  simp [RecordSchema.valueAdmissible, GSort.liftToList, Value.ofList]

/-- The fresh recursive edge name `_rest_ ++ x` never equals `x`: it is strictly
    longer. This makes the recursion's edge variable provably distinct from the
    destination variable, with no reserved-name assumption on user patterns. -/
theorem rest_ne_dst (x : Name) : ("_rest_" ++ x == x) = false := by
  cases h : ("_rest_" ++ x == x) with
  | false => rfl
  | true =>
    exfalso
    have heq : ("_rest_" ++ x) = x := eq_of_beq h
    have hd : ("_rest_" ++ x).data = x.data := congrArg String.data heq
    rw [String.data_append] at hd
    have hl := congrArg List.length hd
    rw [List.length_append] at hl
    have h6 : ("_rest_" : String).data.length = 6 := by decide
    omega

/-- The generated mid-node name `_mid_<m>` never equals a fresh recursive edge
    name `_rest_ ++ x`: they differ already at their second character. -/
theorem mid_ne_rest_dst (m : Nat) (x : Name) :
    ("_mid_" ++ toString m == "_rest_" ++ x) = false := by
  cases h : ("_mid_" ++ toString m == "_rest_" ++ x) with
  | false => rfl
  | true =>
    exfalso
    have heq : ("_mid_" ++ toString m) = "_rest_" ++ x := eq_of_beq h
    have hd : ("_mid_" ++ toString m).data = ("_rest_" ++ x).data := congrArg String.data heq
    simp only [String.data_append, List.cons_append, List.nil_append] at hd
    injection hd with h1 hd
    injection hd with h2 _
    exact absurd h2 (by decide)

/-- Record form of `matchVarLengthPath`: every produced record binds the source
    and target node variables to node refs at the working site, and the edge
    variable to a list value. The edge-list contents are irrelevant to
    conformance (`ofList_adm_liftToList`), so the form abstracts them as `edges`.

    Hygiene hypotheses: the source/edge/target variables of the *pattern* must be
    distinct in the ways the semantics relies on (`src.var ≠ rel.var`,
    `dst.var ≠ rel.var` -- from join-compatibility at assembly time) and not
    collide with the recursion's reserved temp name (`dst.var ≠ "_rest_rel"`).
    `hH4` is the generated-name distinctness the recursion needs at every depth;
    it is `True` under a fresh-name semantics and otherwise a benign assumption. -/
theorem matchVarLengthPath_mem_form (G : PropertyGraph) (site : GraphSite) (dir : Direction) :
    ∀ (k : Nat) (src : NodeAtom) (rel : EdgeAtom) (dst : NodeAtom) (rho : Record),
      (src.var == rel.var) = false →
      (dst.var == rel.var) = false →
      rho ∈ matchVarLengthPath G site src rel dst dir k →
      ∃ (srcN dstN : Nat) (edges : List Value),
        rho = [(src.var, Value.nodeRef site srcN),
               (rel.var, Value.ofList edges),
               (dst.var, Value.nodeRef site dstN)] := by
  intro k
  induction k with
  | zero =>
    intro src rel dst rho _ _ hmem
    simp only [matchVarLengthPath, List.mem_filterMap] at hmem
    obtain ⟨rho0, hrho0, heq⟩ := hmem
    obtain ⟨srcN, rfl⟩ := matchNode_mem_form hrho0
    refine ⟨srcN, srcN, [], ?_⟩
    rw [singletonNode_lookup] at heq
    simp only [Record.extend, Option.some.injEq] at heq
    rw [← heq]; rfl
  | succ k ih =>
    cases k with
    | zero =>
      -- k = 1: single edge, edge variable wrapped into a one-element list
      intro src rel dst rho hH1 hH2 hmem
      rw [matchVarLengthPath] at hmem
      simp only [List.mem_map] at hmem
      obtain ⟨rho0, hrho0, heq⟩ := hmem
      obtain ⟨srcN, ei, dstN, hei, hdstN, _, _, _, _, hform⟩ := matchSingleEdge_mem_form hrho0
      subst hform
      have hne1 : src.var ≠ rel.var := fun h => by simp [h] at hH1
      have hne2 : dst.var ≠ rel.var := fun h => by simp [h] at hH2
      have hlk : Record.lookup [(src.var, Value.nodeRef site srcN),
          (rel.var, Value.edgeRef site ei), (dst.var, Value.nodeRef site dstN)] rel.var
          = Value.edgeRef site ei := by
        simp [Record.lookup, List.find?_cons, hH1, beq_self_eq_true]
      rw [hlk] at heq
      refine ⟨srcN, dstN, [Value.edgeRef site ei], ?_⟩
      rw [← heq]
      simp [Record.set, Record.mem, Record.extend, List.find?_cons, hH1, hH2, hne1, hne2,
            beq_self_eq_true]
    | succ n =>
      -- k = n + 2: first edge + recursive rest, edges concatenated into the list
      intro src rel dst rho hH1 hH2 hmem
      rw [matchVarLengthPath] at hmem
      simp only [List.mem_flatMap] at hmem
      obtain ⟨rho1, hrho1, hbody⟩ := hmem
      obtain ⟨srcN, ei, midN, hei, hmidN, _, _, _, _, hform1⟩ := matchSingleEdge_mem_form hrho1
      subst hform1
      -- the source lookup is the first entry of rho1, independent of any collision
      have hsrc : Record.lookup
          [(src.var, Value.nodeRef site srcN),
           (({ rel with var := "_rel_" ++ toString n, quantifier := Quantifier.single } : EdgeAtom).var,
              Value.edgeRef site ei),
           (({ var := "_mid_" ++ toString n, labels := none, props := [] } : NodeAtom).var,
              Value.nodeRef site midN)] src.var = Value.nodeRef site srcN := by
        simp [Record.lookup, List.find?_cons, beq_self_eq_true]
      split at hbody
      · -- midId = none: the some-branch never runs, body is empty
        exact absurd hbody (List.not_mem_nil rho)
      · -- midId = some: a real intermediate node was found
        simp only [List.mem_filterMap] at hbody
        obtain ⟨rho2, hrho2, hfilt⟩ := hbody
        obtain ⟨srcN', dstN', edges', hform2⟩ :=
          ih { var := "_mid_" ++ toString n, labels := none, props := [] }
            { rel with var := "_rest_" ++ dst.var } dst rho2
            (mid_ne_rest_dst n dst.var) (by rw [name_beq_comm]; exact rest_ne_dst dst.var) hrho2
        subst hform2
        split at hfilt
        · -- the agreement check passed: hfilt builds the result record
          obtain rfl := Option.some.inj hfilt
          have hrr : ("_rest_" ++ dst.var == dst.var) = false := rest_ne_dst dst.var
          by_cases hcol : (("_mid_" ++ toString n : Name) == dst.var) = true
          · have hdst : Record.lookup
                [(({ var := "_mid_" ++ toString n, labels := none, props := [] } : NodeAtom).var,
                    Value.nodeRef site srcN'),
                 (({ rel with var := "_rest_" ++ dst.var } : EdgeAtom).var, Value.ofList edges'),
                 (dst.var, Value.nodeRef site dstN')] dst.var = Value.nodeRef site srcN' := by
              simp [Record.lookup, List.find?_cons, hcol]
            exact ⟨srcN, srcN', _, by rw [hsrc, hdst]⟩
          · simp only [Bool.not_eq_true] at hcol
            have hdst : Record.lookup
                [(({ var := "_mid_" ++ toString n, labels := none, props := [] } : NodeAtom).var,
                    Value.nodeRef site srcN'),
                 (({ rel with var := "_rest_" ++ dst.var } : EdgeAtom).var, Value.ofList edges'),
                 (dst.var, Value.nodeRef site dstN')] dst.var = Value.nodeRef site dstN' := by
              simp [Record.lookup, List.find?_cons, hcol, hrr, beq_self_eq_true]
            exact ⟨srcN, dstN', _, by rw [hsrc, hdst]⟩
        · exact absurd hfilt (by simp)

/-- In-bounds variant of `matchVarLengthPath_mem_form`: the matched source and
    destination node indices are additionally valid nodes of `G`. Mirrors the
    original proof, threading `matchNode_mem_form_wf` and
    `matchSingleEdge_mem_form'` through in place of their unbounded
    counterparts. -/
theorem matchVarLengthPath_mem_form_wf (G : PropertyGraph) (site : GraphSite) (dir : Direction) :
    ∀ (k : Nat) (src : NodeAtom) (rel : EdgeAtom) (dst : NodeAtom) (rho : Record),
      (src.var == rel.var) = false →
      (dst.var == rel.var) = false →
      rho ∈ matchVarLengthPath G site src rel dst dir k →
      ∃ (srcN dstN : Nat) (edges : List Value),
        srcN < G.numNodes ∧ dstN < G.numNodes ∧
        rho = [(src.var, Value.nodeRef site srcN),
               (rel.var, Value.ofList edges),
               (dst.var, Value.nodeRef site dstN)] := by
  intro k
  induction k with
  | zero =>
    intro src rel dst rho _ _ hmem
    simp only [matchVarLengthPath, List.mem_filterMap] at hmem
    obtain ⟨rho0, hrho0, heq⟩ := hmem
    obtain ⟨srcN, hsrcN, rfl⟩ := matchNode_mem_form_wf hrho0
    refine ⟨srcN, srcN, [], hsrcN, hsrcN, ?_⟩
    rw [singletonNode_lookup] at heq
    simp only [Record.extend, Option.some.injEq] at heq
    rw [← heq]; rfl
  | succ k ih =>
    cases k with
    | zero =>
      -- k = 1: single edge, edge variable wrapped into a one-element list
      intro src rel dst rho hH1 hH2 hmem
      rw [matchVarLengthPath] at hmem
      simp only [List.mem_map] at hmem
      obtain ⟨rho0, hrho0, heq⟩ := hmem
      obtain ⟨srcN, ei, dstN, hsrcN, hei, hdstN, _, _, _, _, _, _, _, _, hform⟩ :=
        matchSingleEdge_mem_form' hrho0
      subst hform
      have hne1 : src.var ≠ rel.var := fun h => by simp [h] at hH1
      have hne2 : dst.var ≠ rel.var := fun h => by simp [h] at hH2
      have hlk : Record.lookup [(src.var, Value.nodeRef site srcN),
          (rel.var, Value.edgeRef site ei), (dst.var, Value.nodeRef site dstN)] rel.var
          = Value.edgeRef site ei := by
        simp [Record.lookup, List.find?_cons, hH1, beq_self_eq_true]
      rw [hlk] at heq
      refine ⟨srcN, dstN, [Value.edgeRef site ei], hsrcN, hdstN, ?_⟩
      rw [← heq]
      simp [Record.set, Record.mem, Record.extend, List.find?_cons, hH1, hH2, hne1, hne2,
            beq_self_eq_true]
    | succ n =>
      -- k = n + 2: first edge + recursive rest, edges concatenated into the list
      intro src rel dst rho hH1 hH2 hmem
      rw [matchVarLengthPath] at hmem
      simp only [List.mem_flatMap] at hmem
      obtain ⟨rho1, hrho1, hbody⟩ := hmem
      obtain ⟨srcN, ei, midN, hsrcN, hei, hmidN, _, _, _, _, _, _, _, _, hform1⟩ :=
        matchSingleEdge_mem_form' hrho1
      subst hform1
      -- the source lookup is the first entry of rho1, independent of any collision
      have hsrc : Record.lookup
          [(src.var, Value.nodeRef site srcN),
           (({ rel with var := "_rel_" ++ toString n, quantifier := Quantifier.single } : EdgeAtom).var,
              Value.edgeRef site ei),
           (({ var := "_mid_" ++ toString n, labels := none, props := [] } : NodeAtom).var,
              Value.nodeRef site midN)] src.var = Value.nodeRef site srcN := by
        simp [Record.lookup, List.find?_cons, beq_self_eq_true]
      split at hbody
      · -- midId = none: the some-branch never runs, body is empty
        exact absurd hbody (List.not_mem_nil rho)
      · -- midId = some: a real intermediate node was found
        simp only [List.mem_filterMap] at hbody
        obtain ⟨rho2, hrho2, hfilt⟩ := hbody
        obtain ⟨srcN', dstN', edges', hsrcN', hdstN', hform2⟩ :=
          ih { var := "_mid_" ++ toString n, labels := none, props := [] }
            { rel with var := "_rest_" ++ dst.var } dst rho2
            (mid_ne_rest_dst n dst.var) (by rw [name_beq_comm]; exact rest_ne_dst dst.var) hrho2
        subst hform2
        split at hfilt
        · -- the agreement check passed: hfilt builds the result record
          obtain rfl := Option.some.inj hfilt
          have hrr : ("_rest_" ++ dst.var == dst.var) = false := rest_ne_dst dst.var
          by_cases hcol : (("_mid_" ++ toString n : Name) == dst.var) = true
          · have hdst : Record.lookup
                [(({ var := "_mid_" ++ toString n, labels := none, props := [] } : NodeAtom).var,
                    Value.nodeRef site srcN'),
                 (({ rel with var := "_rest_" ++ dst.var } : EdgeAtom).var, Value.ofList edges'),
                 (dst.var, Value.nodeRef site dstN')] dst.var = Value.nodeRef site srcN' := by
              simp [Record.lookup, List.find?_cons, hcol]
            exact ⟨srcN, srcN', _, hsrcN, hsrcN', by rw [hsrc, hdst]⟩
          · simp only [Bool.not_eq_true] at hcol
            have hdst : Record.lookup
                [(({ var := "_mid_" ++ toString n, labels := none, props := [] } : NodeAtom).var,
                    Value.nodeRef site srcN'),
                 (({ rel with var := "_rest_" ++ dst.var } : EdgeAtom).var, Value.ofList edges'),
                 (dst.var, Value.nodeRef site dstN')] dst.var = Value.nodeRef site dstN' := by
              simp [Record.lookup, List.find?_cons, hcol, hrr, beq_self_eq_true]
            exact ⟨srcN, dstN', _, hsrcN, hdstN', by rw [hsrc, hdst]⟩
        · exact absurd hfilt (by simp)

/-- Every record produced by `matchVarLengthPath` is ref-bounded and binds the
    destination variable -- with NO hygiene hypotheses on the pattern's variable
    names. `RecordRefBoundWF` and `Record.mem` only inspect a record entry-wise
    (`RecordRefBoundWF_of_entries` is collision-agnostic, and a variable's own
    key trivially witnesses its own membership), so name collisions between
    `src.var`, `rel.var` and `dst.var` cannot break either fact. -/
theorem matchVarLengthPath_refBoundWF (G : PropertyGraph) (site : GraphSite) (dir : Direction) :
    ∀ (k : Nat) (src : NodeAtom) (rel : EdgeAtom) (dst : NodeAtom) (rho : Record),
      rho ∈ matchVarLengthPath G site src rel dst dir k →
      RecordRefBoundWF G rho ∧ rho.mem dst.var = true := by
  intro k
  induction k with
  | zero =>
    intro src rel dst rho hmem
    simp only [matchVarLengthPath, List.mem_filterMap] at hmem
    obtain ⟨rho0, hrho0, heq⟩ := hmem
    obtain ⟨srcN, hsrcN, rfl⟩ := matchNode_mem_form_wf hrho0
    rw [singletonNode_lookup] at heq
    simp only [Record.extend, Option.some.injEq] at heq
    have hrho : rho = [(src.var, Value.nodeRef site srcN), (rel.var, Value.ofList []),
        (dst.var, Value.nodeRef site srcN)] := by rw [← heq]; rfl
    subst hrho
    refine ⟨?_, ?_⟩
    · apply RecordRefBoundWF_of_entries
      intro e he
      obtain ⟨ek, ev⟩ := e
      simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq] at he
      rcases he with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | hnil
      · exact Or.inl ⟨site, srcN, hsrcN, rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
      · exact Or.inl ⟨site, srcN, hsrcN, rfl⟩
      · exact absurd hnil (List.not_mem_nil _)
    · simp [Record.mem, beq_self_eq_true]
  | succ k ih =>
    cases k with
    | zero =>
      -- k = 1: single edge, edge variable wrapped into a one-element list
      intro src rel dst rho hmem
      rw [matchVarLengthPath] at hmem
      simp only [List.mem_map] at hmem
      obtain ⟨rho0, hrho0, heq⟩ := hmem
      obtain ⟨srcN, ei, dstN, hsrcN, hei, hdstN, _, _, _, _, _, _, _, _, hform⟩ :=
        matchSingleEdge_mem_form' hrho0
      subst hform
      have hrbwf0 := matchSingleEdge_refBoundWF hrho0
      have hmemdst0 : Record.mem [(src.var, Value.nodeRef site srcN), (rel.var, Value.edgeRef site ei),
          (dst.var, Value.nodeRef site dstN)] dst.var = true := by
        simp [Record.mem, beq_self_eq_true]
      have hmemrel0 : Record.mem [(src.var, Value.nodeRef site srcN), (rel.var, Value.edgeRef site ei),
          (dst.var, Value.nodeRef site dstN)] rel.var = true := by
        simp [Record.mem, beq_self_eq_true]
      rw [← heq]
      -- Whichever constructor `rel.var`'s current value happens to be, the
      -- result is either the unchanged record (any constructor but `edgeRef`)
      -- or `Record.set` applied to it (the `edgeRef` constructor); both keep
      -- every value bounded-ref-or-list and keep `dst.var` in the domain.
      cases Record.lookup [(src.var, Value.nodeRef site srcN), (rel.var, Value.edgeRef site ei),
          (dst.var, Value.nodeRef site dstN)] rel.var with
      | prim p => exact ⟨hrbwf0, hmemdst0⟩
      | nodeRef gg nn => exact ⟨hrbwf0, hmemdst0⟩
      | null => exact ⟨hrbwf0, hmemdst0⟩
      | list l => exact ⟨hrbwf0, hmemdst0⟩
      | edgeRef g ee =>
        dsimp only
        constructor
        · unfold Record.set
          split
          · apply RecordRefBoundWF_of_entries
            intro e he
            rw [List.mem_map] at he
            obtain ⟨⟨k, w⟩, hkw, hfe⟩ := he
            simp only [] at hfe
            simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq] at hkw
            by_cases hc : (k == rel.var)
            · rw [if_pos hc] at hfe
              subst hfe
              exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
            · rw [if_neg hc] at hfe
              subst hfe
              rcases hkw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hnil
              · exact Or.inl ⟨site, srcN, hsrcN, rfl⟩
              · exact Or.inr (Or.inl ⟨site, ei, hei, rfl⟩)
              · exact Or.inl ⟨site, dstN, hdstN, rfl⟩
              · exact absurd hnil (List.not_mem_nil _)
          · rename_i hcontra
            exact absurd hmemrel0 hcontra
        · unfold Record.set
          split
          · rw [Record.mem, List.any_eq_true]
            refine ⟨(dst.var, if dst.var == rel.var then Value.ofList [Value.edgeRef g ee]
                else Value.nodeRef site dstN), ?_, ?_⟩
            · rw [List.mem_map]
              refine ⟨(dst.var, Value.nodeRef site dstN), ?_, ?_⟩
              · simp
              · dsimp only; split <;> rfl
            · simp [beq_self_eq_true]
          · rename_i hcontra
            exact absurd hmemrel0 hcontra
    | succ n =>
      -- k = n + 2: first edge + recursive rest, edges concatenated into the list
      intro src rel dst rho hmem
      rw [matchVarLengthPath] at hmem
      simp only [List.mem_flatMap] at hmem
      obtain ⟨rho1, hrho1, hbody⟩ := hmem
      obtain ⟨srcN, ei, midN, hsrcN, hei, hmidN, _, _, _, _, _, _, _, _, hform1⟩ :=
        matchSingleEdge_mem_form' hrho1
      subst hform1
      have hsrc : Record.lookup
          [(src.var, Value.nodeRef site srcN),
           (({ rel with var := "_rel_" ++ toString n, quantifier := Quantifier.single } : EdgeAtom).var,
              Value.edgeRef site ei),
           (({ var := "_mid_" ++ toString n, labels := none, props := [] } : NodeAtom).var,
              Value.nodeRef site midN)] src.var = Value.nodeRef site srcN := by
        simp [Record.lookup, List.find?_cons, beq_self_eq_true]
      split at hbody
      · exact absurd hbody (List.not_mem_nil rho)
      · simp only [List.mem_filterMap] at hbody
        obtain ⟨rho2, hrho2, hfilt⟩ := hbody
        obtain ⟨hrbwf2, hmemdst2⟩ :=
          ih { var := "_mid_" ++ toString n, labels := none, props := [] }
            { rel with var := "_rest_" ++ dst.var } dst rho2 hrho2
        split at hfilt
        · obtain rfl := Option.some.inj hfilt
          refine ⟨?_, ?_⟩
          · apply RecordRefBoundWF_of_entries
            intro e he
            obtain ⟨ek, ev⟩ := e
            simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq] at he
            rcases he with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | hnil
            · rw [hsrc]; exact Or.inl ⟨site, srcN, hsrcN, rfl⟩
            · exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
            · exact hrbwf2 dst.var hmemdst2
            · exact absurd hnil (List.not_mem_nil _)
          · simp [Record.mem, beq_self_eq_true]
        · exact absurd hfilt (by simp)

/-- Zero-length match form (#4 pre-stage). The `k = 0` branch of
    `matchVarLengthPath` -- the only contribution a `lo = 0` quantified edge makes
    beyond the `k >= 1` paths -- binds the source variable to a node matched by
    `src`, the edge variable to the empty list, and the destination variable to
    that same node (source = target, no edge traversed). It exposes the underlying
    `matchNode` witness, so node-atom conformance (`matchNode_conforms_atom`)
    applies to the endpoints. This is the structural handle the open `lo = 0`
    quantified-edge typing question (#4) turns on, and it holds regardless of how
    that typing is ultimately resolved. -/
theorem matchVarLengthPath_zero_form (G : PropertyGraph) (site : GraphSite)
    (src : NodeAtom) (rel : EdgeAtom) (dst : NodeAtom) (dir : Direction) (rho : Record)
    (hmem : rho ∈ matchVarLengthPath G site src rel dst dir 0) :
    ∃ i, [(src.var, Value.nodeRef site i)] ∈ matchNode G site src ∧
      rho = [(src.var, Value.nodeRef site i), (rel.var, Value.ofList []),
             (dst.var, Value.nodeRef site i)] := by
  simp only [matchVarLengthPath, List.mem_filterMap] at hmem
  obtain ⟨rho0, hrho0, heq⟩ := hmem
  obtain ⟨i, rfl⟩ := matchNode_mem_form hrho0
  refine ⟨i, hrho0, ?_⟩
  rw [singletonNode_lookup] at heq
  simp only [Record.extend, Option.some.injEq] at heq
  exact heq.symm

/-- Zero-length endpoint admissibility (#4 pre-stage). Combines the form lemma
    with node-atom conformance: every zero-length record is the explicit
    source/empty-edge/destination triple, and its shared endpoint node is
    admissible to the source atom's type `T` (so the endpoints are properly
    node-typed, not empty-typed). The edge variable's empty list is admissible to
    any list type by `ofList_adm_liftToList`. This is the conformance core the
    `lo = 0` case needs under the node-typed resolution of #4. -/
theorem matchVarLengthPath_zero_adm
    (ctx : TypingCtx) (G : PropertyGraph) (src : NodeAtom) (rel : EdgeAtom) (dst : NodeAtom)
    (dir : Direction) (T : GSort)
    (hAtom : AtomTyping ctx (AtomInput.node src) (RecordSchema.mk [(src.var, T)]))
    (hCat : ∀ Psi, ctx.schemaMap.lookup ctx.graphSite = some Psi →
              graphConformsSchema G Psi = true)
    (rho : Record) (hmem : rho ∈ matchVarLengthPath G ctx.graphSite src rel dst dir 0) :
    ∃ i, rho = [(src.var, Value.nodeRef ctx.graphSite i), (rel.var, Value.ofList []),
                (dst.var, Value.nodeRef ctx.graphSite i)]
         ∧ RecordSchema.valueAdmissible (Value.nodeRef ctx.graphSite i) T = true := by
  obtain ⟨i, hnode, rfl⟩ :=
    matchVarLengthPath_zero_form G ctx.graphSite src rel dst dir rho hmem
  refine ⟨i, rfl, ?_⟩
  have hconf := matchNode_conforms_atom ctx G src _ hAtom hCat _ hnode
  have hadm := hconf.2 src.var T (by simp [RecordSchema.mk])
  simpa [singletonNode_lookup] using hadm

/-- Single-length vacuity under closed-fail (#4 boundary). When the single-edge
    endpoint compatibility fails (`closedFail`, `endpointCompatTriple ... = false`)
    and the graph conforms, no length-one path survives -- this is the single-edge
    vacuity wrapped through the `k = 1` branch of `matchVarLengthPath`.

    This does not extend to `k >= 2`: the `k = n + 2` branch routes its
    first edge through an UNCONSTRAINED intermediate node (`labels := none`,
    `props := []`), so `closedFail` -- which only fails the direct `(src, rel, dst)`
    triple -- says nothing about it. A multi-hop path can exist even when no direct
    edge is schema-compatible: e.g. with `rel = E` admitting `A->B` and `B->C` but
    not `A->C`, the single edge `(A)-[E]->(C)` is `closedFail`, yet the 2-hop
    `(A)-[E]->(B)-[E]->(C)` is produced by `matchVarLengthPath ... 2`. Hence
    `closedFail` lifted to ANY quantifier reaching length 0 (`lo = 0`) or length
    `>= 2` (`+`, `*`, `{i,j}` with `j >= 2`) is NOT vacuous; only the exact-length-one
    quantifier `{1}` is. This broadens fidelity finding #4 beyond the `lo = 0` case. -/
theorem matchVarLengthPath_one_vacuous
    (G : PropertyGraph) (Psi : GraphSchemaFull) (site : GraphSite)
    (src : NodeAtom) (rel : EdgeAtom) (dst : NodeAtom) (dir : Direction)
    (PhiPi1 PhiPiE PhiPi3 : PropSchema)
    (sN1 : List NodeSchemaFull) (sE2 : List EdgeSchemaFull) (sN3 : List NodeSchemaFull)
    (hGconf : graphConformsSchema G Psi = true)
    (hPrp1 : PropConstraintTyping src.props PhiPi1)
    (hPrpE : PropConstraintTyping rel.props PhiPiE)
    (hPrp3 : PropConstraintTyping dst.props PhiPi3)
    (hsN1 : sN1 = filterNodeSchemasByPropCompat (resolveNodeSchemas Psi src.labels) PhiPi1)
    (hsE2 : sE2 = filterEdgeSchemasByPropCompat (resolveEdgeSchemas Psi rel.labels) PhiPiE)
    (hsN3 : sN3 = filterNodeSchemasByPropCompat (resolveNodeSchemas Psi dst.labels) PhiPi3)
    (hFail : endpointCompatTriple sN1 sE2 sN3 dir = false)
    (rho : Record) (hrho : rho ∈ matchVarLengthPath G site src rel dst dir 1) :
    False := by
  rw [matchVarLengthPath] at hrho
  simp only [List.mem_map] at hrho
  obtain ⟨rho0, hrho0, _⟩ := hrho
  exact not_mem_matchSingleEdge_of_no_endpoint_triple G Psi site src
    { rel with quantifier := .single } dst dir PhiPi1 PhiPiE PhiPi3 sN1 sE2 sN3
    hGconf hPrp1 hPrpE hPrp3 hsN1 hsE2 hsN3 hFail rho0 hrho0

/-- Record form of `matchRangePath`: it is a flat-map of `matchVarLengthPath`
    over the length range `[lo, hi]`, so every produced record has the same
    three-binding shape. Carries the same hygiene hypotheses. -/
theorem matchRangePath_mem_form (G : PropertyGraph) (site : GraphSite) (dir : Direction)
    (src : NodeAtom) (rel : EdgeAtom) (dst : NodeAtom) (lo hi : Nat) (rho : Record)
    (hH1 : (src.var == rel.var) = false)
    (hH2 : (dst.var == rel.var) = false)
    (hmem : rho ∈ matchRangePath G site src rel dst dir lo hi) :
    ∃ (srcN dstN : Nat) (edges : List Value),
      rho = [(src.var, Value.nodeRef site srcN),
             (rel.var, Value.ofList edges),
             (dst.var, Value.nodeRef site dstN)] := by
  unfold matchRangePath at hmem
  rw [List.mem_flatMap] at hmem
  obtain ⟨offset, _, hmem'⟩ := hmem
  exact matchVarLengthPath_mem_form G site dir (lo + offset) src rel dst rho hH1 hH2 hmem'

/-- In-bounds variant of `matchRangePath_mem_form`: the matched source and
    destination node indices are additionally valid nodes of `G`. -/
theorem matchRangePath_mem_form_wf (G : PropertyGraph) (site : GraphSite) (dir : Direction)
    (src : NodeAtom) (rel : EdgeAtom) (dst : NodeAtom) (lo hi : Nat) (rho : Record)
    (hH1 : (src.var == rel.var) = false)
    (hH2 : (dst.var == rel.var) = false)
    (hmem : rho ∈ matchRangePath G site src rel dst dir lo hi) :
    ∃ (srcN dstN : Nat) (edges : List Value),
      srcN < G.numNodes ∧ dstN < G.numNodes ∧
      rho = [(src.var, Value.nodeRef site srcN),
             (rel.var, Value.ofList edges),
             (dst.var, Value.nodeRef site dstN)] := by
  unfold matchRangePath at hmem
  rw [List.mem_flatMap] at hmem
  obtain ⟨offset, _, hmem'⟩ := hmem
  exact matchVarLengthPath_mem_form_wf G site dir (lo + offset) src rel dst rho hH1 hH2 hmem'

/-- Every record produced by `matchRangePath` is ref-bounded: it is a flat-map of
    `matchVarLengthPath` over the length range, and `matchVarLengthPath_refBoundWF`
    already covers every length freshness-free. -/
theorem matchRangePath_refBoundWF (G : PropertyGraph) (site : GraphSite) (dir : Direction)
    (src : NodeAtom) (rel : EdgeAtom) (dst : NodeAtom) (lo hi : Nat) (rho : Record)
    (hmem : rho ∈ matchRangePath G site src rel dst dir lo hi) :
    RecordRefBoundWF G rho := by
  unfold matchRangePath at hmem
  rw [List.mem_flatMap] at hmem
  obtain ⟨offset, _, hmem'⟩ := hmem
  exact (matchVarLengthPath_refBoundWF G site dir (lo + offset) src rel dst rho hmem').1

/-- `liftToGroupRef` preserves a schema's domain (it maps entries, keeping each
    key and only possibly lifting its type to a list). -/
theorem RecordSchema.liftToGroupRef_mem (Ctx : RecordSchema) (vars : List Name) (z : Name) :
    (Ctx.liftToGroupRef vars).mem z = Ctx.mem z := by
  unfold RecordSchema.liftToGroupRef RecordSchema.mem
  dsimp only
  generalize Ctx.entries = es
  induction es with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    rw [List.map_cons, List.any_cons, List.any_cons, ih]
    congr 1
    split <;> rfl

/-- The nullable lift preserves the domain (mirror of `liftToGroupRef_mem`). -/
theorem RecordSchema.liftToNullable_mem (Ctx : RecordSchema) (vars : List Name) (z : Name) :
    (Ctx.liftToNullable vars).mem z = Ctx.mem z := by
  unfold RecordSchema.liftToNullable RecordSchema.mem
  dsimp only
  generalize Ctx.entries = es
  induction es with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    rw [List.map_cons, List.any_cons, List.any_cons, ih]
    congr 1
    split <;> rfl

/-- Entry structure of `liftToNullable` (mirror of `mem_liftToGroupRef_entries`). -/
theorem RecordSchema.mem_liftToNullable_entries {Ctx : RecordSchema} {vars : List Name}
    {z : Name} {t : GSort} (h : (z, t) ∈ (Ctx.liftToNullable vars).entries) :
    ∃ t0, (z, t0) ∈ Ctx.entries ∧
      t = (if vars.any (fun v => v == z) then t0.toNullable else t0) := by
  unfold RecordSchema.liftToNullable at h
  simp only [List.mem_map] at h
  obtain ⟨⟨k, v⟩, hmem, heq⟩ := h
  simp only [] at heq
  split at heq
  · rename_i hcond
    obtain ⟨hk, ht⟩ := Prod.mk.injEq .. ▸ heq
    subst hk; subst ht
    exact ⟨v, hmem, by rw [if_pos hcond]⟩
  · rename_i hcond
    obtain ⟨hk, ht⟩ := Prod.mk.injEq .. ▸ heq
    subst hk; subst ht
    exact ⟨v, hmem, by rw [if_neg hcond]⟩

/-- `liftToNullable` preserves well-formedness. -/
theorem RecordSchema.liftToNullable_schemaWF {Ctx : RecordSchema} {vars : List Name}
    (h : SchemaWF Ctx) : SchemaWF (Ctx.liftToNullable vars) := by
  have hfun : ∀ z t t', (z, t) ∈ (Ctx.liftToNullable vars).entries →
      (z, t') ∈ (Ctx.liftToNullable vars).entries → t = t' := by
    intro z t t' hzt hzt'
    obtain ⟨t0, hmem0, heq0⟩ := RecordSchema.mem_liftToNullable_entries hzt
    obtain ⟨t0', hmem0', heq0'⟩ := RecordSchema.mem_liftToNullable_entries hzt'
    have ht0 : t0 = t0' := Option.some.inj ((h z t0 hmem0).symm.trans (h z t0' hmem0'))
    rw [heq0, heq0', ht0]
  intro z t hzt
  obtain ⟨t', hlk'⟩ := RecordSchema.mem_lookup_some (RecordSchema.mem_of_entry hzt)
  rw [hlk', hfun z t' t (RecordSchema.lookup_some_mem hlk') hzt]

/-- The empty schema is well-formed. -/
theorem RecordSchema.schemaWF_empty : SchemaWF RecordSchema.empty := by
  intro x t h; exact absurd h (List.not_mem_nil _)

/-- Atom typing produces a singleton schema, hence well-formed. -/
theorem atomTyping_schemaWF {ctx : TypingCtx} {a : AtomInput} {GammaA : RecordSchema}
    (h : AtomTyping ctx a GammaA) : SchemaWF GammaA := by
  cases h <;> exact RecordSchema.singleton_schemaWF _ _

/-- Refinement typing preserves well-formedness: the output is a join (open) or a
    `setMany` over a join (closed/closed-empty/closed-fail) of the three inputs. -/
theorem refinementTyping_schemaWF {ctx : TypingCtx} {G1 G2 G3 : RecordSchema}
    {v1 r2 v3 : Name} {dir : Direction} {GammaRef : RecordSchema}
    (h : RefinementTyping ctx G1 G2 G3 v1 r2 v3 dir GammaRef)
    (h1 : SchemaWF G1) (h2 : SchemaWF G2) (h3 : SchemaWF G3) : SchemaWF GammaRef := by
  cases h with
  | open_ => exact RecordSchema.join_schemaWF (RecordSchema.join_schemaWF h1 h2) h3
  | closed => exact RecordSchema.setMany_schemaWF _ (RecordSchema.join_schemaWF (RecordSchema.join_schemaWF h1 h2) h3)
  | closedEmpty => exact RecordSchema.setMany_schemaWF _ (RecordSchema.join_schemaWF (RecordSchema.join_schemaWF h1 h2) h3)
  | closedFail => exact RecordSchema.setMany_schemaWF _ (RecordSchema.join_schemaWF (RecordSchema.join_schemaWF h1 h2) h3)

/-- Entry structure of `liftToGroupRef`: every produced entry comes from an
    original entry at the same key, with its type lifted to a list iff the key is
    in `vars`. -/
theorem RecordSchema.mem_liftToGroupRef_entries {Ctx : RecordSchema} {vars : List Name}
    {z : Name} {t : GSort} (h : (z, t) ∈ (Ctx.liftToGroupRef vars).entries) :
    ∃ t0, (z, t0) ∈ Ctx.entries ∧
      t = (if vars.any (fun v => v == z) then t0.liftToList else t0) := by
  unfold RecordSchema.liftToGroupRef at h
  simp only [List.mem_map] at h
  obtain ⟨⟨k, v⟩, hmem, heq⟩ := h
  simp only [] at heq
  split at heq
  · rename_i hcond
    obtain ⟨hk, ht⟩ := Prod.mk.injEq .. ▸ heq
    subst hk; subst ht
    exact ⟨v, hmem, by rw [if_pos hcond]⟩
  · rename_i hcond
    obtain ⟨hk, ht⟩ := Prod.mk.injEq .. ▸ heq
    subst hk; subst ht
    exact ⟨v, hmem, by rw [if_neg hcond]⟩

/-- Conformance workhorse for variable-length / quantified edge paths (the
    group-ref/list case), mirroring `matchSingleEdge_conforms_core`. Every
    `matchRangePath` record binds the node variables to node refs and the edge
    variable to a list, so a schema whose domain is those three variables and
    whose entries admit the matching shape (node ref for the endpoints, ANY list
    for the edge variable -- see `ofList_adm_liftToList`) is conformed to. -/
theorem matchRangePath_conforms_core
    (G : PropertyGraph) (site : GraphSite) (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
    (lo hi : Nat) (GammaPath : RecordSchema)
    (hrel1 : (rel.var == n1.var) = false) (hrel2 : (rel.var == n2.var) = false)
    (hdom : ∀ z, GammaPath.mem z = (n1.var == z || rel.var == z || n2.var == z))
    (hVal : ∀ z t, (z, t) ∈ GammaPath.entries →
              ((n1.var == z) = true → ∀ i, RecordSchema.valueAdmissible (Value.nodeRef site i) t = true)
            ∧ ((rel.var == z) = true → ∀ es, RecordSchema.valueAdmissible (Value.ofList es) t = true)
            ∧ ((n2.var == z) = true → ∀ i, RecordSchema.valueAdmissible (Value.nodeRef site i) t = true)) :
    BTConforms (matchRangePath G site n1 rel n2 dir lo hi) GammaPath := by
  intro rho hrho
  obtain ⟨srcN, dstN, edges, rfl⟩ := matchRangePath_mem_form G site dir n1 rel n2 lo hi rho
    ((name_beq_comm n1.var rel.var).trans hrel1) ((name_beq_comm n2.var rel.var).trans hrel2) hrho
  refine ⟨?_, ?_⟩
  · intro z
    rw [hdom z]
    simp [Record.mem, Bool.or_assoc]
  · intro z t hzt
    obtain ⟨hv1, hve, hv2⟩ := hVal z t hzt
    have hmemz : GammaPath.mem z = true := RecordSchema.mem_of_entry hzt
    rw [hdom z] at hmemz
    cases hz1 : n1.var == z with
    | true =>
      have hlk : Record.lookup [(n1.var, Value.nodeRef site srcN),
          (rel.var, Value.ofList edges), (n2.var, Value.nodeRef site dstN)] z
          = Value.nodeRef site srcN := by
        simp [Record.lookup, List.find?_cons, hz1]
      rw [hlk]; exact hv1 hz1 srcN
    | false =>
      cases hze : rel.var == z with
      | true =>
        have hlk : Record.lookup [(n1.var, Value.nodeRef site srcN),
            (rel.var, Value.ofList edges), (n2.var, Value.nodeRef site dstN)] z
            = Value.ofList edges := by
          simp [Record.lookup, List.find?_cons, hz1, hze]
        rw [hlk]; exact hve hze edges
      | false =>
        simp only [hz1, hze, Bool.false_or] at hmemz
        have hlk : Record.lookup [(n1.var, Value.nodeRef site srcN),
            (rel.var, Value.ofList edges), (n2.var, Value.nodeRef site dstN)] z
            = Value.nodeRef site dstN := by
          simp [Record.lookup, List.find?_cons, hz1, hze, hmemz]
        rw [hlk]; exact hv2 hmemz dstN

/-- Lift a single-edge per-entry value obligation (edge variable bound to an edge
    ref) to the group-ref/list obligation (edge variable bound to a list), for the
    `patQuantEdge` (variable-length / quantified edge) cases. The node-variable
    entries are unchanged; the edge variable's type becomes a list, which every
    `ofList` admits trivially (`ofList_adm_liftToList`), so the base obligation's
    edge-ref clause is not even needed. -/
private theorem liftToGroupRef_hVal
    (site : GraphSite) (n1 n2 : NodeAtom) (rel : EdgeAtom) (Gamma : RecordSchema)
    (hrel1 : (rel.var == n1.var) = false) (hrel2 : (rel.var == n2.var) = false)
    (hbase : ∀ z t, (z, t) ∈ Gamma.entries →
              ((n1.var == z) = true → ∀ i, RecordSchema.valueAdmissible (Value.nodeRef site i) t = true)
            ∧ ((n2.var == z) = true → ∀ i, RecordSchema.valueAdmissible (Value.nodeRef site i) t = true))
    (z : Name) (t : GSort)
    (hzt : (z, t) ∈ (Gamma.liftToGroupRef [rel.var]).entries) :
    ((n1.var == z) = true → ∀ i, RecordSchema.valueAdmissible (Value.nodeRef site i) t = true)
  ∧ ((rel.var == z) = true → ∀ es, RecordSchema.valueAdmissible (Value.ofList es) t = true)
  ∧ ((n2.var == z) = true → ∀ i, RecordSchema.valueAdmissible (Value.nodeRef site i) t = true) := by
  obtain ⟨t0, ht0mem, ht0eq⟩ := RecordSchema.mem_liftToGroupRef_entries hzt
  obtain ⟨hv1, hv2⟩ := hbase z t0 ht0mem
  simp only [List.any_cons, List.any_nil, Bool.or_false] at ht0eq
  split at ht0eq
  · -- edge variable: t = t0.liftToList; node implications vacuous (rel.var ≠ n1/n2)
    rename_i hrz
    subst ht0eq
    refine ⟨fun hn1 => ?_, fun _ es => ofList_adm_liftToList es t0, fun hn2 => ?_⟩
    · exfalso
      have h : rel.var = n1.var := (eq_of_beq hrz).trans (eq_of_beq hn1).symm
      rw [h, beq_self_eq_true n1.var] at hrel1; exact Bool.noConfusion hrel1
    · exfalso
      have h : rel.var = n2.var := (eq_of_beq hrz).trans (eq_of_beq hn2).symm
      rw [h, beq_self_eq_true n2.var] at hrel2; exact Bool.noConfusion hrel2
  · -- node variable: t = t0; edge implication vacuous (rel.var ≠ z)
    rename_i hrz
    subst ht0eq
    exact ⟨hv1, fun hh => absurd hh hrz, hv2⟩

/-- Variable-length / quantified edge conformance, `open` case: the group-ref lift
    of the open edge join `(N⟨G⟩ ⋈ E⟨G⟩ ⋈ N⟨G⟩)↑[rel.var]` is conformed to by
    `matchRangePath`. Endpoints stay node-typed; the edge variable becomes a list,
    admitted by every produced edge list (`ofList_adm_liftToList`). -/
private theorem matchRangePath_conforms_open
    (G : PropertyGraph) (site : GraphSite) (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
    (lo hi : Nat)
    (hrel1 : (rel.var == n1.var) = false) (hrel2 : (rel.var == n2.var) = false) :
    BTConforms (matchRangePath G site n1 rel n2 dir lo hi)
      (((RecordSchema.mk [(n1.var, GSort.nodeOf site)]).join
          (RecordSchema.mk [(rel.var, GSort.edgeOf site)])
          |>.join (RecordSchema.mk [(n2.var, GSort.nodeOf site)])).liftToGroupRef [rel.var]) := by
  apply matchRangePath_conforms_core G site n1 n2 rel dir lo hi _ hrel1 hrel2
  · intro z
    rw [RecordSchema.liftToGroupRef_mem, RecordSchema.join_mem, RecordSchema.join_mem,
        singleton_schema_mem, singleton_schema_mem, singleton_schema_mem, Bool.or_assoc]
  · intro z t hzt
    exact liftToGroupRef_hVal site n1 n2 rel _ hrel1 hrel2
      (fun z' t' h' => ⟨(open_join_hVal site n1 n2 rel hrel1 hrel2 z' t' h').1,
        (open_join_hVal site n1 n2 rel hrel1 hrel2 z' t' h').2.2⟩) z t hzt

private theorem open_join_entry_is_nodeOf_or_edgeOf
    (site : GraphSite) (n1 n2 : NodeAtom) (rel : EdgeAtom) (TE : GSort)
    (hrel1 : (rel.var == n1.var) = false) (hrel2 : (rel.var == n2.var) = false)
    (z : Name) (t0 : GSort)
    (h : (z, t0) ∈ ((RecordSchema.mk [(n1.var, GSort.nodeOf site)]).join
          (RecordSchema.mk [(rel.var, TE)])
          |>.join (RecordSchema.mk [(n2.var, GSort.nodeOf site)])).entries) :
    t0 = GSort.nodeOf site ∨ (z = rel.var ∧ t0 = TE) := by
  rcases RecordSchema.join_entry_cases h with
    ⟨t1, hinner, _, ht⟩ | ⟨t1, t2, hinner, hClk, ht⟩ | ⟨t2, hCent, _, ht⟩
  · subst ht
    rcases RecordSchema.join_entry_cases hinner with
      ⟨ta, hAent, _, hta⟩ | ⟨ta, tb, hAent, hBlk, hta⟩ | ⟨tb, hBent, _, htb⟩
    · subst hta; exact Or.inl (Prod.mk.injEq .. ▸ (List.mem_singleton.mp hAent)).2
    · exfalso
      have := (Prod.mk.injEq .. ▸ (List.mem_singleton.mp hAent)).1
      subst this; simp [singleton_schema_lookup, hrel1] at hBlk
    · subst htb
      exact Or.inr ⟨(Prod.mk.injEq .. ▸ (List.mem_singleton.mp hBent)).1,
        (Prod.mk.injEq .. ▸ (List.mem_singleton.mp hBent)).2⟩
  · subst ht
    rw [singleton_schema_lookup] at hClk
    cases hnz : n2.var == z with
    | false => rw [hnz] at hClk; exact absurd hClk (by simp)
    | true =>
      rw [hnz] at hClk
      have ht2 : t2 = GSort.nodeOf site := (Option.some.inj hClk).symm
      subst ht2
      rcases RecordSchema.join_entry_cases hinner with
        ⟨ta, hAent, _, hta⟩ | ⟨_, _, hAent, hBlk, _⟩ | ⟨tb, hBent, _, _⟩
      · subst hta
        have := (Prod.mk.injEq .. ▸ (List.mem_singleton.mp hAent)).2
        subst this; rw [sortInter_nodeOf_self]; exact Or.inl rfl
      · exfalso
        have := (Prod.mk.injEq .. ▸ (List.mem_singleton.mp hAent)).1
        subst this; simp [singleton_schema_lookup, hrel1] at hBlk
      · exfalso
        have hzrel := (Prod.mk.injEq .. ▸ (List.mem_singleton.mp hBent)).1
        rw [hzrel, name_beq_comm] at hnz
        rw [hnz] at hrel2; exact Bool.noConfusion hrel2
  · subst ht; exact Or.inl (Prod.mk.injEq .. ▸ (List.mem_singleton.mp hCent)).2



/-- Variable-length / quantified edge conformance for an ARBITRARY edge
    atom sort `TE` (open, refined, or empty): the group-ref lift admits the
    edge variable's list regardless of `TE` (list admissibility is
    element-unaware), and the endpoint entries are the open node sorts. -/
private theorem matchRangePath_conforms_edgeSort
    (G : PropertyGraph) (site : GraphSite) (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
    (lo hi : Nat) (TE : GSort)
    (hrel1 : (rel.var == n1.var) = false) (hrel2 : (rel.var == n2.var) = false) :
    BTConforms (matchRangePath G site n1 rel n2 dir lo hi)
      (((RecordSchema.mk [(n1.var, GSort.nodeOf site)]).join
          (RecordSchema.mk [(rel.var, TE)])
          |>.join (RecordSchema.mk [(n2.var, GSort.nodeOf site)])).liftToGroupRef [rel.var]) := by
  apply matchRangePath_conforms_core G site n1 n2 rel dir lo hi _ hrel1 hrel2
  · intro z
    rw [RecordSchema.liftToGroupRef_mem, RecordSchema.join_mem, RecordSchema.join_mem,
        singleton_schema_mem, singleton_schema_mem, singleton_schema_mem, Bool.or_assoc]
  · intro z t hzt
    refine liftToGroupRef_hVal site n1 n2 rel _ hrel1 hrel2 ?_ z t hzt
    intro z' t' h'
    rcases open_join_entry_is_nodeOf_or_edgeOf site n1 n2 rel TE hrel1 hrel2 z' t' h' with
      rfl | ⟨rfl, rfl⟩
    · exact ⟨fun _ i => by simp [RecordSchema.valueAdmissible, GSort.nodeOf, Value.hasExtSort],
        fun _ i => by simp [RecordSchema.valueAdmissible, GSort.nodeOf, Value.hasExtSort]⟩
    · constructor
      · intro hz1 i
        exfalso
        rw [name_beq_comm] at hz1
        rw [hz1] at hrel1
        exact Bool.noConfusion hrel1
      · intro hz2 i
        exfalso
        rw [name_beq_comm] at hz2
        rw [hz2] at hrel2
        exact Bool.noConfusion hrel2

/-- Variable-length / quantified edge conformance, `closed` case: the group-ref
    lift of the refined edge join is conformed to by `matchRangePath`. As in the
    open case the edge variable is admitted as a list regardless of the (graph-
    unaware, hence irrelevant) refined schema lists. -/
private theorem matchRangePath_conforms_closed
    (G : PropertyGraph) (site : GraphSite) (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
    (lo hi : Nat) (TN1 TE TN2 : GSort)
    (sN1' : List NodeSchemaFull) (sE2' : List EdgeSchemaFull) (sN3' : List NodeSchemaFull)
    (hrel1 : (rel.var == n1.var) = false) (hrel2 : (rel.var == n2.var) = false) :
    BTConforms (matchRangePath G site n1 rel n2 dir lo hi)
      ((((RecordSchema.mk [(n1.var, TN1)]).join (RecordSchema.mk [(rel.var, TE)])
          |>.join (RecordSchema.mk [(n2.var, TN2)])).setMany
        [(n1.var, GSort.nodeRefinedOf site sN1'),
         (rel.var, GSort.edgeRefinedOf site sE2'),
         (n2.var, GSort.nodeRefinedOf site sN3')]).liftToGroupRef [rel.var]) := by
  apply matchRangePath_conforms_core G site n1 n2 rel dir lo hi _ hrel1 hrel2
  · intro z
    rw [RecordSchema.liftToGroupRef_mem, RecordSchema.setMany_mem,
        RecordSchema.join_mem, RecordSchema.join_mem,
        singleton_schema_mem, singleton_schema_mem, singleton_schema_mem]
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    cases n1.var == z <;> cases rel.var == z <;> cases n2.var == z <;> rfl
  · intro z t hzt
    exact liftToGroupRef_hVal site n1 n2 rel _ hrel1 hrel2
      (fun z' t' h' => ⟨(closed_join_hVal site n1 n2 rel TN1 TE TN2 sN1' sE2' sN3' hrel1 hrel2 z' t' h').1,
        (closed_join_hVal site n1 n2 rel TN1 TE TN2 sN1' sE2' sN3' hrel1 hrel2 z' t' h').2.2⟩) z t hzt

/-- Semantic reduction for a group-reference quantified edge (`*`, `+`, `{i}`,
    `{i,j}`): `evalPattern` of the edge pattern is `matchRangePath` over the
    quantifier's bounds, with an unbounded upper bound capped at the edge count.
    (The `.single` and `?` quantifiers take the other branches and are excluded by
    `hQuant`.) -/
theorem evalPattern_edge_groupRef (G : PropertyGraph) (site : GraphSite)
    (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
    (hQuant : rel.quantifier.isGroupRef = true) :
    evalPattern G site (.edge n1 rel dir n2)
      = matchRangePath G site n1 rel n2 dir rel.quantifier.lo
          (rel.quantifier.hi.getD G.numEdges) := by
  simp only [evalPattern]
  cases h : rel.quantifier with
  | single => rw [h] at hQuant; exact absurd hQuant (by decide)
  | question => rw [h] at hQuant; exact absurd hQuant (by decide)
  | star => rfl
  | plus => rfl
  | exact i => rfl
  | range i j => rfl

/-- Pattern-level (`evalPattern`) conformance for a group-reference quantified
    edge, `open` case: the pattern evaluates into the group-ref lift of the open
    edge join. Composes `evalPattern_edge_groupRef` with `matchRangePath_conforms_open`.
    The distinctness/hygiene hypotheses are carried forward (discharged at the
    `patQuantEdge` assembly). -/
private theorem evalPattern_quantEdge_conforms_open
    (G : PropertyGraph) (site : GraphSite) (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
    (hQuant : rel.quantifier.isGroupRef = true)
    (hrel1 : (rel.var == n1.var) = false) (hrel2 : (rel.var == n2.var) = false) :
    BTConforms (evalPattern G site (.edge n1 rel dir n2))
      (((RecordSchema.mk [(n1.var, GSort.nodeOf site)]).join
          (RecordSchema.mk [(rel.var, GSort.edgeOf site)])
          |>.join (RecordSchema.mk [(n2.var, GSort.nodeOf site)])).liftToGroupRef [rel.var]) := by
  rw [evalPattern_edge_groupRef G site n1 n2 rel dir hQuant]
  exact matchRangePath_conforms_open G site n1 n2 rel dir _ _ hrel1 hrel2

/-- Pattern-level conformance for a group-reference quantified edge with an
    arbitrary edge atom sort. -/
private theorem evalPattern_quantEdge_conforms_edgeSort
    (G : PropertyGraph) (site : GraphSite) (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
    (TE : GSort)
    (hQuant : rel.quantifier.isGroupRef = true)
    (hrel1 : (rel.var == n1.var) = false) (hrel2 : (rel.var == n2.var) = false) :
    BTConforms (evalPattern G site (.edge n1 rel dir n2))
      (((RecordSchema.mk [(n1.var, GSort.nodeOf site)]).join
          (RecordSchema.mk [(rel.var, TE)])
          |>.join (RecordSchema.mk [(n2.var, GSort.nodeOf site)])).liftToGroupRef [rel.var]) := by
  rw [evalPattern_edge_groupRef G site n1 n2 rel dir hQuant]
  exact matchRangePath_conforms_edgeSort G site n1 n2 rel dir _ _ TE hrel1 hrel2

/-- Pattern-level (`evalPattern`) conformance for a group-reference quantified
    edge, `closed` case: composes the reduction with `matchRangePath_conforms_closed`.
    The refined schema lists are irrelevant (graph-unaware admissibility). -/
private theorem evalPattern_quantEdge_conforms_closed
    (G : PropertyGraph) (site : GraphSite) (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
    (TN1 TE TN2 : GSort)
    (sN1' : List NodeSchemaFull) (sE2' : List EdgeSchemaFull) (sN3' : List NodeSchemaFull)
    (hQuant : rel.quantifier.isGroupRef = true)
    (hrel1 : (rel.var == n1.var) = false) (hrel2 : (rel.var == n2.var) = false) :
    BTConforms (evalPattern G site (.edge n1 rel dir n2))
      ((((RecordSchema.mk [(n1.var, TN1)]).join (RecordSchema.mk [(rel.var, TE)])
          |>.join (RecordSchema.mk [(n2.var, TN2)])).setMany
        [(n1.var, GSort.nodeRefinedOf site sN1'),
         (rel.var, GSort.edgeRefinedOf site sE2'),
         (n2.var, GSort.nodeRefinedOf site sN3')]).liftToGroupRef [rel.var]) := by
  rw [evalPattern_edge_groupRef G site n1 n2 rel dir hQuant]
  exact matchRangePath_conforms_closed G site n1 n2 rel dir _ _
    TN1 TE TN2 sN1' sE2' sN3' hrel1 hrel2

/-- Widening the null tag to `.nullable` preserves admissibility. -/
private theorem adm_toNullable_of_adm {v : Value} {t : GSort}
    (h : RecordSchema.valueAdmissible v t = true) :
    RecordSchema.valueAdmissible v t.toNullable = true := by
  obtain ⟨s, n⟩ := t
  by_cases hv : v = .null
  · subst hv
    exact adm_null_toNullable h
  · cases n with
    | val => exact (adm_nonNull_val_eq_nullable hv s).symm.trans h
    | nullable => exact h
    | null => exact absurd h (by rw [adm_nonNull_nullTag_false hv]; simp)

/-- A sort admitting any value at all admits null once its tag is loosened
    to `.nullable` (the bad shapes admit nothing). -/
private theorem adm_null_toNullable_of_adm {v : Value} {t : GSort}
    (h : RecordSchema.valueAdmissible v t = true) :
    RecordSchema.valueAdmissible .null t.toNullable = true := by
  obtain ⟨s, n⟩ := t
  cases s <;>
    first
      | rfl
      | (rename_i ts
         cases ts
         · exact absurd h (by simp [RecordSchema.valueAdmissible]; done)
         · rfl)
      | (refine absurd h ?_; simp [RecordSchema.valueAdmissible]; done)

/-- Semantic reduction for the `?` quantifier: `evalPattern` of the edge
    pattern is `matchOptionalEdge`. -/
theorem evalPattern_edge_question (G : PropertyGraph) (site : GraphSite)
    (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
    (hQ : rel.quantifier = .question) :
    evalPattern G site (.edge n1 rel dir n2)
      = matchOptionalEdge G site n1 rel n2 dir := by
  simp only [evalPattern]; rw [hQ]

/-- Conformance workhorse for the `?` quantifier, mirroring
    `matchRangePath_conforms_core`: every `matchOptionalEdge` record binds
    the node variables to node refs and the edge variable to null (zero
    case) or an edge ref (one case). -/
theorem matchOptionalEdge_conforms_core
    (G : PropertyGraph) (site : GraphSite) (n1 n2 : NodeAtom) (rel : EdgeAtom)
    (dir : Direction) (GammaOpt : RecordSchema)
    (_hrel1 : (rel.var == n1.var) = false) (_hrel2 : (rel.var == n2.var) = false)
    (hdom : ∀ z, GammaOpt.mem z = (n1.var == z || rel.var == z || n2.var == z))
    (hVal : ∀ z t, (z, t) ∈ GammaOpt.entries →
              ((n1.var == z) = true → ∀ i, RecordSchema.valueAdmissible (Value.nodeRef site i) t = true)
            ∧ ((rel.var == z) = true →
                RecordSchema.valueAdmissible Value.null t = true
                ∧ ∀ i, RecordSchema.valueAdmissible (Value.edgeRef site i) t = true)
            ∧ ((n2.var == z) = true → ∀ i, RecordSchema.valueAdmissible (Value.nodeRef site i) t = true)) :
    BTConforms (matchOptionalEdge G site n1 rel n2 dir) GammaOpt := by
  intro rho hrho
  rcases matchOptionalEdge_mem hrho with ⟨i, hi, rfl⟩ | ho
  · refine ⟨?_, ?_⟩
    · intro z
      rw [hdom z]
      simp [Record.mem, Bool.or_assoc]
    · intro z t hzt
      obtain ⟨hv1, hve, hv2⟩ := hVal z t hzt
      have hmemz : GammaOpt.mem z = true := RecordSchema.mem_of_entry hzt
      rw [hdom z] at hmemz
      cases hz1 : n1.var == z with
      | true =>
        have hlk : Record.lookup [(n1.var, Value.nodeRef site i),
            (rel.var, Value.null), (n2.var, Value.nodeRef site i)] z
            = Value.nodeRef site i := by
          simp [Record.lookup, List.find?_cons, hz1]
        rw [hlk]; exact hv1 hz1 i
      | false =>
        cases hze : rel.var == z with
        | true =>
          have hlk : Record.lookup [(n1.var, Value.nodeRef site i),
              (rel.var, Value.null), (n2.var, Value.nodeRef site i)] z
              = Value.null := by
            simp [Record.lookup, List.find?_cons, hz1, hze]
          rw [hlk]; exact (hve hze).1
        | false =>
          have hz2 : (n2.var == z) = true := by
            rw [hz1, hze] at hmemz; simpa using hmemz
          have hlk : Record.lookup [(n1.var, Value.nodeRef site i),
              (rel.var, Value.null), (n2.var, Value.nodeRef site i)] z
              = Value.nodeRef site i := by
            simp [Record.lookup, List.find?_cons, hz1, hze, hz2]
          rw [hlk]; exact hv2 hz2 i
  · obtain ⟨srcN, ei, dstN, hsrcN, hei, hdstN, _, _, _, _, _, _, _, _, rfl⟩ :=
      matchSingleEdge_mem_form' ho
    refine ⟨?_, ?_⟩
    · intro z
      rw [hdom z]
      simp [Record.mem, Bool.or_assoc]
    · intro z t hzt
      obtain ⟨hv1, hve, hv2⟩ := hVal z t hzt
      have hmemz : GammaOpt.mem z = true := RecordSchema.mem_of_entry hzt
      rw [hdom z] at hmemz
      cases hz1 : n1.var == z with
      | true =>
        have hlk : Record.lookup [(n1.var, Value.nodeRef site srcN),
            (rel.var, Value.edgeRef site ei), (n2.var, Value.nodeRef site dstN)] z
            = Value.nodeRef site srcN := by
          simp [Record.lookup, List.find?_cons, hz1]
        rw [hlk]; exact hv1 hz1 srcN
      | false =>
        cases hze : rel.var == z with
        | true =>
          have hlk : Record.lookup [(n1.var, Value.nodeRef site srcN),
              (rel.var, Value.edgeRef site ei), (n2.var, Value.nodeRef site dstN)] z
              = Value.edgeRef site ei := by
            simp [Record.lookup, List.find?_cons, hz1, hze]
          rw [hlk]; exact (hve hze).2 ei
        | false =>
          have hz2 : (n2.var == z) = true := by
            rw [hz1, hze] at hmemz; simpa using hmemz
          have hlk : Record.lookup [(n1.var, Value.nodeRef site srcN),
              (rel.var, Value.edgeRef site ei), (n2.var, Value.nodeRef site dstN)] z
              = Value.nodeRef site dstN := by
            simp [Record.lookup, List.find?_cons, hz1, hze, hz2]
          rw [hlk]; exact hv2 hz2 dstN

/-- Pattern-level conformance for the `?` quantifier: the pattern
    evaluates into the nullable lift of the open edge join. -/
private theorem evalPattern_optEdge_conforms_open
    (G : PropertyGraph) (site : GraphSite) (n1 n2 : NodeAtom) (rel : EdgeAtom)
    (dir : Direction)
    (hrel1 : (rel.var == n1.var) = false) (hrel2 : (rel.var == n2.var) = false) :
    BTConforms
      (evalPattern G site (.edge n1 { rel with quantifier := .question } dir n2))
      (((RecordSchema.mk [(n1.var, GSort.nodeOf site)]).join
          (RecordSchema.mk [(rel.var, GSort.edgeOf site)])
          |>.join (RecordSchema.mk [(n2.var, GSort.nodeOf site)])).liftToNullable [rel.var]) := by
  rw [evalPattern_edge_question G site n1 n2 { rel with quantifier := .question } dir rfl]
  apply matchOptionalEdge_conforms_core G site n1 n2 _ dir _ hrel1 hrel2
  · intro z
    rw [RecordSchema.liftToNullable_mem, RecordSchema.join_mem, RecordSchema.join_mem,
        singleton_schema_mem, singleton_schema_mem, singleton_schema_mem, Bool.or_assoc]
  · intro z t hzt
    obtain ⟨t0, ht0, ht⟩ := RecordSchema.mem_liftToNullable_entries hzt
    obtain ⟨hv1, hve, hv2⟩ := open_join_hVal site n1 n2 rel hrel1 hrel2 z t0 ht0
    subst ht
    refine ⟨?_, ?_, ?_⟩
    · intro hz1 i
      split
      · rename_i hcond
        exfalso
        simp only [List.any_cons, List.any_nil, Bool.or_false] at hcond
        have : rel.var = n1.var := (eq_of_beq hcond).trans (eq_of_beq hz1).symm
        rw [this, beq_self_eq_true] at hrel1
        exact Bool.noConfusion hrel1
      · exact hv1 hz1 i
    · intro hze
      split
      · exact ⟨adm_null_toNullable_of_adm (hve hze 0),
          fun i => adm_toNullable_of_adm (hve hze i)⟩
      · rename_i hcond
        exfalso
        simp only [List.any_cons, List.any_nil, Bool.or_false] at hcond
        exact absurd hze hcond
    · intro hz2 i
      split
      · rename_i hcond
        exfalso
        simp only [List.any_cons, List.any_nil, Bool.or_false] at hcond
        have : rel.var = n2.var := (eq_of_beq hcond).trans (eq_of_beq hz2).symm
        rw [this, beq_self_eq_true] at hrel2
        exact Bool.noConfusion hrel2
      · exact hv2 hz2 i

-- ============================================================
--  Pattern Soundness (Thm 6.2) -- structural reductions + PE-layer skeleton
-- ============================================================

/-- `evalPattern` of a node pattern is `matchNode`. -/
theorem evalPattern_node (G : PropertyGraph) (site : GraphSite) (na : NodeAtom) :
    evalPattern G site (.node na) = matchNode G site na := rfl

/-- `evalPattern` of a grouped pattern is transparent. -/
theorem evalPattern_grouped (G : PropertyGraph) (site : GraphSite) (P : Pattern) :
    evalPattern G site (.grouped P) = evalPattern G site P := rfl

/-- `evalPattern` of a conjunction (`.patternList`) is the binding-table join of the
    two sub-patterns (the natural join on shared variables). -/
theorem evalPattern_patternList (G : PropertyGraph) (site : GraphSite) (P1 P2 : Pattern) :
    evalPattern G site (.patternList P1 P2)
      = bindingTableJoin (evalPattern G site P1) (evalPattern G site P2) := rfl

/-- `evalPattern` of a single (non-quantified) edge is `matchSingleEdge`. -/
theorem evalPattern_edge_single (G : PropertyGraph) (site : GraphSite)
    (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
    (hSingle : rel.quantifier = .single) :
    evalPattern G site (.edge n1 rel dir n2) = matchSingleEdge G site n1 rel n2 dir := by
  simp only [evalPattern]; rw [hSingle]

-- (Removed dead `patExprSoundness_of_patternSound` -- an abstract PE-layer
--  skeleton with no strong-WF context, superseded by `patExprSoundness'` /
--  `patExprSoundness`. The kind-aware join flip requires the empty-former-meet
--  discharge, which this abstract skeleton could not supply; it and its only
--  consumer `patExprSoundness_of_single` were unused.)

-- ============================================================
--  Typing produces well-formed schemas (discharges the `hWF` obligation)
-- ============================================================

/-- `liftToGroupRef` preserves well-formedness (it relabels each entry's type by a
    key-determined function, so two entries under one key still agree). -/
theorem RecordSchema.liftToGroupRef_schemaWF {Ctx : RecordSchema} {vars : List Name}
    (h : SchemaWF Ctx) : SchemaWF (Ctx.liftToGroupRef vars) := by
  have hfun : ∀ z t t', (z, t) ∈ (Ctx.liftToGroupRef vars).entries →
      (z, t') ∈ (Ctx.liftToGroupRef vars).entries → t = t' := by
    intro z t t' hzt hzt'
    obtain ⟨t0, hmem0, heq0⟩ := RecordSchema.mem_liftToGroupRef_entries hzt
    obtain ⟨t0', hmem0', heq0'⟩ := RecordSchema.mem_liftToGroupRef_entries hzt'
    have ht0 : t0 = t0' := Option.some.inj ((h z t0 hmem0).symm.trans (h z t0' hmem0'))
    rw [heq0, heq0', ht0]
  intro z t hzt
  obtain ⟨t', hlk'⟩ := RecordSchema.mem_lookup_some (RecordSchema.mem_of_entry hzt)
  rw [hlk', hfun z t' t (RecordSchema.lookup_some_mem hlk') hzt]

/-- Pattern typing preserves well-formedness (`SchemaWF Ctx → SchemaWF Gamma`),
    threading WF through the refinement/quantifier/grouping structure. -/
theorem patternTyping_schemaWF {ctx : TypingCtx} {qd : QuantDepth}
    {P : Pattern} {Gamma : RecordSchema} {v : Name}
    (h : PatternTyping ctx qd P Gamma v) : SchemaWF Gamma := by
  induction h with
  | patNode qd na GammaA hAtom =>
    exact atomTyping_schemaWF hAtom
  | patEdge qd n1 n2 rel dir GammaN1 GammaE GammaN2 GammaRef hSingle hAtomN1 hAtomE hAtomN2 hRef =>
    exact refinementTyping_schemaWF hRef (atomTyping_schemaWF hAtomN1)
      (atomTyping_schemaWF hAtomE) (atomTyping_schemaWF hAtomN2)
  | patStep qd P rel dir n2 Gamma1 GammaE GammaN2 GammaRef v1 hSingle hPrefix hAtomE hAtomN2 hRef ihPrefix =>
    exact refinementTyping_schemaWF hRef ihPrefix
      (atomTyping_schemaWF hAtomE) (atomTyping_schemaWF hAtomN2)
  | patQuantEdge n1 n2 rel dir K GammaE hQuant hAtomE hNE12 hNE23 =>
    obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
    exact RecordSchema.liftToGroupRef_schemaWF
      (RecordSchema.join_schemaWF (RecordSchema.join_schemaWF
        (RecordSchema.singleton_schemaWF _ _) (RecordSchema.singleton_schemaWF _ _))
        (RecordSchema.singleton_schemaWF _ _))
  | patOptEdge n1 n2 rel dir hNE12 hNE23 =>
    exact RecordSchema.liftToNullable_schemaWF
      (RecordSchema.join_schemaWF (RecordSchema.join_schemaWF
        (RecordSchema.singleton_schemaWF _ _) (RecordSchema.singleton_schemaWF _ _))
        (RecordSchema.singleton_schemaWF _ _))
  | patQuantPath P K GammaInner v hInner hQuant ihInner =>
    exact RecordSchema.liftToGroupRef_schemaWF ihInner
  | patGrouped qd P Gamma v hP ih =>
    exact ih

/-- Pattern-expression typing produces well-formed schemas:
    PE-Single via `patternTyping_schemaWF`, PE-Conjunction via `join`. -/
theorem patExprTyping_schemaWF {ctx : TypingCtx}
    {P : Pattern} {Gamma : RecordSchema}
    (h : PatExprTyping ctx P Gamma) : SchemaWF Gamma := by
  induction h with
  | single P Gamma v hPat => exact patternTyping_schemaWF hPat
  | conjunction P1 P2 Gamma1 Gamma2 v h1 h2 hjc ih1 =>
    exact RecordSchema.join_schemaWF ih1 (patternTyping_schemaWF h2)

-- (Removed dead `patExprSoundness_of_single` -- see the removed
--  `patExprSoundness_of_patternSound` note above.)

-- ============================================================
--  Per-pattern soundness (the `hSingle` obligation), non-blocked cases
--
--  Each `patternSound_*` lemma discharges one `PatternTyping` constructor at the
--  `evalPattern` level. They are the reusable workhorses for the eventual `hSingle`
--  induction; the blocked constructors (`closedFail`, `closedEmpty`+zero-length
--  quantifier, `?`/optional list-vs-nullable, quantified-path group lists) are
--  excluded by hypothesis and tracked separately (Lean fidelity defects).
-- ============================================================

/-- Joining the empty schema on the left is the identity: `onlyIn1`/`shared` are
    empty and `onlyIn2` keeps every entry (nothing is shared with `∅`). -/
theorem RecordSchema.empty_join (GammaA : RecordSchema) :
    RecordSchema.empty.join GammaA = GammaA := by
  cases GammaA with
  | mk es =>
    show RecordSchema.mk _ = RecordSchema.mk es
    congr 1
    simp [RecordSchema.join, RecordSchema.empty, RecordSchema.mem]

/-- `==` on names is symmetric on the `false` side (names are `String`, `LawfulBEq`). -/
private theorem beq_name_symm_false {a b : Name} (h : (a == b) = false) : (b == a) = false := by
  cases hb : b == a with
  | false => rfl
  | true => have hba : b = a := eq_of_beq hb; subst hba; simp at h

/-- The quantifier-stripped edge atom used by `Pat-Edge`/`Pat-Step` typing equals
    the original edge atom whenever its quantifier is `.single` (the default). This
    bridges the edge *atom typing* (stated on the stripped atom) to the
    `matchSingleEdge` semantics (stated on the original `rel`). -/
private theorem edge_atom_strip {rel : EdgeAtom} (hQ : rel.quantifier = .single) :
    AtomInput.edge { var := rel.var, labels := rel.labels, props := rel.props } = AtomInput.edge rel := by
  cases rel with
  | mk v l p q => cases hQ; rfl

/-- Inversion of a node-atom typing whose output binds the variable to a
    schema-refined node sort: it can only be `Atom-Node-Closed`, which exposes
    the resolved + property-filtered schema set. The `open` (`N⟨G⟩`) and
    `closed-fail` (`⟨N⟨G⟩⟩⊥`) cases produce non-refined sorts, contradicting the
    lookup. -/
private theorem atomTyping_node_refined_inv {ctx : TypingCtx} {na : NodeAtom}
    {Gamma : RecordSchema} {ss : List NodeSchemaFull}
    (hA : AtomTyping ctx (AtomInput.node na) Gamma)
    (hLk : Gamma.lookup na.var = some (GSort.nodeRefinedOf ctx.graphSite ss)) :
    ∃ Psi PhiPi, ctx.schemaMap.lookup ctx.graphSite = some Psi ∧
      PropConstraintTyping na.props PhiPi ∧
      ss = filterNodeSchemasByPropCompat (resolveNodeSchemas Psi na.labels) PhiPi := by
  cases hA with
  | nodeOpen v labels props hOpen =>
      simp [singleton_schema_lookup, GSort.nodeOf, GSort.nodeRefinedOf] at hLk
  | nodeClosed v labels props Psi PhiPi zetaL zetaPrp zetaResult
      hClosed hSchema hPrp hLbl hPrpF hRes hNE =>
      rw [singleton_schema_lookup] at hLk
      simp only [beq_self_eq_true, if_true, Option.some.injEq] at hLk
      refine ⟨Psi, PhiPi, hSchema, hPrp, ?_⟩
      have hz : zetaResult = ss := nodeRefinedOf_inj hLk
      rw [← hz, hRes, hPrpF, hLbl]
  | nodeClosedFail v labels props Psi PhiPi zetaL zetaPrp
      hClosed hSchema hPrp hLbl hPrpF hEmpty =>
      simp [singleton_schema_lookup, GSort.nodeEmpty, GSort.nodeRefinedOf] at hLk

/-- Edge mirror of `atomTyping_node_refined_inv`. -/
private theorem atomTyping_edge_refined_inv {ctx : TypingCtx} {ea : EdgeAtom}
    {Gamma : RecordSchema} {ss : List EdgeSchemaFull}
    (hA : AtomTyping ctx (AtomInput.edge ea) Gamma)
    (hLk : Gamma.lookup ea.var = some (GSort.edgeRefinedOf ctx.graphSite ss)) :
    ∃ Psi PhiPi, ctx.schemaMap.lookup ctx.graphSite = some Psi ∧
      PropConstraintTyping ea.props PhiPi ∧
      ss = filterEdgeSchemasByPropCompat (resolveEdgeSchemas Psi ea.labels) PhiPi := by
  cases hA with
  | edgeOpen r labels props hOpen =>
      simp [singleton_schema_lookup, GSort.edgeOf, GSort.edgeRefinedOf] at hLk
  | edgeClosed r labels props Psi PhiPi xiL xiPrp xiResult
      hClosed hSchema hPrp hLbl hPrpF hRes hNE =>
      rw [singleton_schema_lookup] at hLk
      simp only [beq_self_eq_true, if_true, Option.some.injEq] at hLk
      refine ⟨Psi, PhiPi, hSchema, hPrp, ?_⟩
      have hz : xiResult = ss := edgeRefinedOf_inj hLk
      rw [← hz, hRes, hPrpF, hLbl]
  | edgeClosedFail r labels props Psi PhiPi xiL xiPrp
      hClosed hSchema hPrp hLbl hPrpF hEmpty =>
      simp [singleton_schema_lookup, GSort.edgeEmpty, GSort.edgeRefinedOf] at hLk

/-- Edge-pattern conformance, `closedFail` (Refine-Closed-Fail) case. The three
    refined endpoint sets are recovered from the atom typings (graph site fixed,
    so the schema maps agree); the rule's `hFail` premise then drives the
    `matchSingleEdge` vacuity lemma. So the all-empty refinement output is never
    asked to admit a value. -/
private theorem matchSingleEdge_conforms_closedFail
    (ctx : TypingCtx) (G : PropertyGraph) (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
    (Gamma1 Gamma2 Gamma3 GammaRef : RecordSchema)
    (sN1 : List NodeSchemaFull) (sE2 : List EdgeSchemaFull) (sN3 : List NodeSchemaFull)
    (hA1 : AtomTyping ctx (AtomInput.node n1) Gamma1)
    (hA2 : AtomTyping ctx (AtomInput.edge rel) Gamma2)
    (hA3 : AtomTyping ctx (AtomInput.node n2) Gamma3)
    (hNode1 : Gamma1.lookup n1.var = some (GSort.nodeRefinedOf ctx.graphSite sN1))
    (hEdge2 : Gamma2.lookup rel.var = some (GSort.edgeRefinedOf ctx.graphSite sE2))
    (hNode3 : Gamma3.lookup n2.var = some (GSort.nodeRefinedOf ctx.graphSite sN3))
    (hCat : ∀ Psi, ctx.schemaMap.lookup ctx.graphSite = some Psi →
              graphConformsSchema G Psi = true)
    (hFail : endpointCompatTriple sN1 sE2 sN3 dir = false) :
    BTConforms (matchSingleEdge G ctx.graphSite n1 rel n2 dir) GammaRef := by
  intro rho hrho
  exfalso
  obtain ⟨Psi1, PhiPi1, hSchema1, hPrp1, hsN1eq⟩ := atomTyping_node_refined_inv hA1 hNode1
  obtain ⟨Psi2, PhiPiE, hSchema2, hPrpE, hsE2eq⟩ := atomTyping_edge_refined_inv hA2 hEdge2
  obtain ⟨Psi3, PhiPi3, hSchema3, hPrp3, hsN3eq⟩ := atomTyping_node_refined_inv hA3 hNode3
  have hP12 : Psi1 = Psi2 := Option.some.inj (hSchema1.symm.trans hSchema2)
  have hP13 : Psi1 = Psi3 := Option.some.inj (hSchema1.symm.trans hSchema3)
  rw [← hP12] at hsE2eq
  rw [← hP13] at hsN3eq
  exact not_mem_matchSingleEdge_of_no_endpoint_triple G Psi1 ctx.graphSite n1 rel n2 dir
    PhiPi1 PhiPiE PhiPi3 sN1 sE2 sN3 (hCat Psi1 hSchema1) hPrp1 hPrpE hPrp3
    hsN1eq hsE2eq hsN3eq hFail rho hrho

/-- `Pat-Node` soundness: `evalPattern` of a node pattern is `matchNode`, and the
    typed schema is `∅ ⋈ GammaA = GammaA`, conformed via `matchNode_conforms_atom`. -/
theorem patternSound_node (ctx : TypingCtx) (G : PropertyGraph)
    (na : NodeAtom) (GammaA : RecordSchema)
    (hAtom : AtomTyping ctx (.node na) GammaA)
    (hCat : ∀ Psi, ctx.schemaMap.lookup ctx.graphSite = some Psi →
              graphConformsSchema G Psi = true) :
    BTConforms (evalPattern G ctx.graphSite (.node na)) GammaA := by
  rw [evalPattern_node]
  exact matchNode_conforms_atom ctx G na GammaA hAtom hCat

/-- Every type bound by the open-refinement join (the `open_` rule's output) is one
    of the open sorts `nodeOf`/`edgeOf` or `bot` (cross intersections collapse to
    `bot`). None is schema-refined, so the `RuntimeConfigWF` obligation is vacuous
    in the open case. Proved by reading the looked-up entry back through
    `join_entry_cases` (nested over the two joins) rather than computing the join. -/
private theorem open_join3_lookup_disj {a r b : Name} {site : GraphSite} {x : Name} {t : GSort}
    (h : (((RecordSchema.mk [(a, GSort.nodeOf site)]).join (RecordSchema.mk [(r, GSort.edgeOf site)])).join
        (RecordSchema.mk [(b, GSort.nodeOf site)])).lookup x = some t) :
    t = GSort.nodeOf site ∨ t = GSort.edgeOf site ∨ t = GSort.botSort := by
  have hsie : RecordSchema.sortInter (GSort.nodeOf site) (GSort.edgeOf site) = GSort.botSort := rfl
  have hsen : RecordSchema.sortInter (GSort.edgeOf site) (GSort.nodeOf site) = GSort.botSort := rfl
  have hsbn : RecordSchema.sortInter GSort.botSort (GSort.nodeOf site) = GSort.botSort := rfl
  have hmem := RecordSchema.lookup_some_mem h
  rcases RecordSchema.join_entry_cases hmem with ⟨t1, hm1, _, rfl⟩ | ⟨t1, t2, hm1, hlk2, rfl⟩ | ⟨t2, hm2, _, rfl⟩
  · -- t = t1, an entry of (A.join B)
    rcases RecordSchema.join_entry_cases hm1 with ⟨ta, hma, _, rfl⟩ | ⟨ta, tb, hma, hlkb, rfl⟩ | ⟨tb, hmb, _, rfl⟩
    · simp only [List.mem_singleton, Prod.mk.injEq] at hma; exact Or.inl hma.2
    · simp only [List.mem_singleton, Prod.mk.injEq] at hma; obtain ⟨_, rfl⟩ := hma
      rw [singleton_schema_lookup] at hlkb
      split at hlkb
      · obtain rfl := Option.some.inj hlkb; exact Or.inr (Or.inr hsie)
      · exact Option.noConfusion hlkb
    · simp only [List.mem_singleton, Prod.mk.injEq] at hmb; exact Or.inr (Or.inl hmb.2)
  · -- t = sortInter t1 t2, with t1 an entry of (A.join B) and t2 from C
    rw [singleton_schema_lookup] at hlk2
    split at hlk2
    · obtain rfl := Option.some.inj hlk2
      rcases RecordSchema.join_entry_cases hm1 with ⟨ta, hma, _, rfl⟩ | ⟨ta, tb, hma, hlkb, rfl⟩ | ⟨tb, hmb, _, rfl⟩
      · simp only [List.mem_singleton, Prod.mk.injEq] at hma; obtain ⟨_, rfl⟩ := hma
        rw [sortInter_nodeOf_self]; exact Or.inl rfl
      · simp only [List.mem_singleton, Prod.mk.injEq] at hma; obtain ⟨_, rfl⟩ := hma
        rw [singleton_schema_lookup] at hlkb
        split at hlkb
        · obtain rfl := Option.some.inj hlkb; rw [hsie, hsbn]; exact Or.inr (Or.inr rfl)
        · exact Option.noConfusion hlkb
      · simp only [List.mem_singleton, Prod.mk.injEq] at hmb; obtain ⟨_, rfl⟩ := hmb
        rw [hsen]; exact Or.inr (Or.inr rfl)
    · exact Option.noConfusion hlk2
  · -- t = t2, an entry of C
    simp only [List.mem_singleton, Prod.mk.injEq] at hm2; exact Or.inl hm2.2

/-- Graph-aware edge-pattern conformance (Theorem 6.2, atom-conformance half).
    Every record `matchSingleEdge` produces is `RuntimeConfigWF`. `open` binds the
    variables to non-refined sorts (vacuous, via `open_join3_lookup_disj`);
    `closedEmpty` and `closedFail` make `matchSingleEdge` vacuous (no record). The
    `closed` case is the content: each matched endpoint/edge conforms a catalog
    schema that lands in the endpoint-compatible projection the (pinned) rule
    assigns, and the matched element's property map conforms it. The natural-join
    fix means a self-loop (`n1.var = n2.var`) forces `srcN = dstN`, so the shared
    variable's last-written refined set (`sN3'`) still contains the node's schema. -/
theorem matchSingleEdge_runtimeWF
    (ctx : TypingCtx) (G : PropertyGraph) (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
    (GammaN1 GammaE GammaN2 GammaRef : RecordSchema)
    (hAtomN1 : AtomTyping ctx (AtomInput.node n1) GammaN1)
    (hAtomE : AtomTyping ctx (AtomInput.edge rel) GammaE)
    (hAtomN2 : AtomTyping ctx (AtomInput.node n2) GammaN2)
    (hRef : RefinementTyping ctx GammaN1 GammaE GammaN2 n1.var rel.var n2.var dir GammaRef)
    (hCat : ∀ Psi, ctx.schemaMap.lookup ctx.graphSite = some Psi →
              graphConformsSchema G Psi = true)
    (rho : Record) (hrho : rho ∈ matchSingleEdge G ctx.graphSite n1 rel n2 dir) :
    RuntimeConfigWF G rho GammaRef := by
  obtain ⟨T1, rfl⟩ := atomTyping_node_singleton hAtomN1
  obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
  obtain ⟨T2, rfl⟩ := atomTyping_node_singleton hAtomN2
  obtain ⟨srcN, ei, dstN, hsrcN, hei, hdstN, hsrcLbl, hsrcPrp, hlblE, hprpE,
          hlblD, hprpD, hphi, hagree, hform⟩ := matchSingleEdge_mem_form' hrho
  have hnodekey : ∀ {x : Name} {g : GraphSite} {nn : Nat}, rho.lookup x = Value.nodeRef g nn →
      ((n1.var == x) = true ∧ nn = srcN) ∨
      ((n1.var == x) = false ∧ (n2.var == x) = true ∧ nn = dstN) := by
    intro x g nn hl
    rw [hform] at hl
    cases hx1 : n1.var == x with
    | true =>
        left; refine ⟨rfl, ?_⟩
        simp only [Record.lookup, List.find?_cons, hx1] at hl
        injection hl with _ hnn; exact hnn.symm
    | false =>
        cases hxr : rel.var == x with
        | true => exfalso; simp only [Record.lookup, List.find?_cons, hx1, hxr] at hl; exact Value.noConfusion hl
        | false =>
            cases hx2 : n2.var == x with
            | true =>
                right; refine ⟨rfl, rfl, ?_⟩
                simp only [Record.lookup, List.find?_cons, hx1, hxr, hx2] at hl
                injection hl with _ hnn; exact hnn.symm
            | false => exfalso; simp only [Record.lookup, List.find?_cons, hx1, hxr, hx2] at hl; exact Value.noConfusion hl
  have hedgekey : ∀ {x : Name} {g : GraphSite} {ee : Nat}, rho.lookup x = Value.edgeRef g ee →
      (rel.var == x) = true ∧ ee = ei := by
    intro x g ee hl
    rw [hform] at hl
    cases hx1 : n1.var == x with
    | true => exfalso; simp only [Record.lookup, List.find?_cons, hx1] at hl; exact Value.noConfusion hl
    | false =>
        cases hxr : rel.var == x with
        | true =>
            refine ⟨rfl, ?_⟩
            simp only [Record.lookup, List.find?_cons, hx1, hxr] at hl
            injection hl with _ hee; exact hee.symm
        | false =>
            cases hx2 : n2.var == x with
            | true => exfalso; simp only [Record.lookup, List.find?_cons, hx1, hxr, hx2] at hl; exact Value.noConfusion hl
            | false => exfalso; simp only [Record.lookup, List.find?_cons, hx1, hxr, hx2] at hl; exact Value.noConfusion hl
  cases hRef with
  | open_ hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 =>
      simp only [singleton_schema_lookup, beq_self_eq_true, if_true, Option.some.injEq]
        at hNode1 hEdge2 hNode3
      subst hNode1; subst hEdge2; subst hNode3
      intro x t hlk
      refine ⟨?_, ?_⟩
      · intro site ss hcomp g nn hn hlook
        rcases open_join3_lookup_disj hlk with rfl | rfl | rfl <;>
          simp [GSort.nodeOf, GSort.edgeOf, GSort.botSort, GSort.componentType, GSort.nodeRefinedOf] at hcomp
      · intro site ss hcomp g ee he hlook
        rcases open_join3_lookup_disj hlk with rfl | rfl | rfl <;>
          simp [GSort.nodeOf, GSort.edgeOf, GSort.botSort, GSort.componentType, GSort.edgeRefinedOf] at hcomp
  | closed sN1 sE2 sN3 sN1' sE2' sN3' hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 hSrc' hEdge' hDst' hNonEmpty =>
      obtain ⟨Psi1, PhiPi1, hSchema1, hPrp1, hsN1eq⟩ := atomTyping_node_refined_inv hAtomN1 hNode1
      obtain ⟨Psi2, PhiPiE, hSchema2, hPrpE2, hsE2eq⟩ := atomTyping_edge_refined_inv hAtomE hEdge2
      obtain ⟨Psi3, PhiPi3, hSchema3, hPrp3, hsN3eq⟩ := atomTyping_node_refined_inv hAtomN2 hNode3
      have hP12 : Psi1 = Psi2 := Option.some.inj (hSchema1.symm.trans hSchema2)
      have hP13 : Psi1 = Psi3 := Option.some.inj (hSchema1.symm.trans hSchema3)
      rw [← hP12] at hsE2eq; rw [← hP13] at hsN3eq
      have hGconf : graphConformsSchema G Psi1 = true := hCat Psi1 hSchema1
      have hT1 : T1 = GSort.nodeRefinedOf ctx.graphSite sN1 := by
        have h := hNode1; rw [singleton_schema_lookup] at h; simpa using h
      have hTE : TE = GSort.edgeRefinedOf ctx.graphSite sE2 := by
        have h := hEdge2; rw [singleton_schema_lookup] at h; simpa using h
      have hT2 : T2 = GSort.nodeRefinedOf ctx.graphSite sN3 := by
        have h := hNode3; rw [singleton_schema_lookup] at h; simpa using h
      have d_rn1 : (rel.var == n1.var) = false :=
        joinCompatible_singleton_distinct n1.var rel.var T1 TE
          (by rw [hT1, hTE]; exact sortInter_nodeRefinedOf_edgeRefinedOf_isBot _ _ _) hJC12
      have d_n2r : (n2.var == rel.var) = false :=
        joinCompatible_singleton_distinct rel.var n2.var TE T2
          (by rw [hTE, hT2]; exact sortInter_edgeRefinedOf_nodeRefinedOf_isBot _ _ _) hJC23
      obtain ⟨nsS, hnsS_Psi, hnsSconf⟩ := graphConformsSchema_node hGconf srcN hsrcN
      obtain ⟨es2, hes2_Psi, hes2conf⟩ := graphConformsSchema_edge hGconf ei hei
      obtain ⟨nsD, hnsD_Psi, hnsDconf⟩ := graphConformsSchema_node hGconf dstN hdstN
      have hnsS_sN1 : nsS ∈ sN1 := by
        rw [hsN1eq]
        exact filterNodeSchemasByPropCompat_mem_of_conforms G ctx.graphSite ⟨srcN, hsrcN⟩ nsS _ n1.props PhiPi1
          (resolveNodeSchemas_mem_of_conforms G Psi1 ⟨srcN, hsrcN⟩ nsS n1.labels hnsS_Psi hnsSconf hsrcLbl)
          hnsSconf hPrp1 hsrcPrp
      have hes2_sE2 : es2 ∈ sE2 := by
        rw [hsE2eq]
        exact filterEdgeSchemasByPropCompat_mem_of_conforms G ctx.graphSite ⟨ei, hei⟩ es2 _ rel.props PhiPiE
          (resolveEdgeSchemas_mem_of_conforms G Psi1 ⟨ei, hei⟩ es2 rel.labels hes2_Psi hes2conf hlblE)
          hes2conf hPrpE2 hprpE
      have hnsD_sN3 : nsD ∈ sN3 := by
        rw [hsN3eq]
        exact filterNodeSchemasByPropCompat_mem_of_conforms G ctx.graphSite ⟨dstN, hdstN⟩ nsD _ n2.props PhiPi3
          (resolveNodeSchemas_mem_of_conforms G Psi1 ⟨dstN, hdstN⟩ nsD n2.labels hnsD_Psi hnsDconf hlblD)
          hnsDconf hPrp3 hprpD
      have htc : tripleCompat nsS es2 nsD dir = true :=
        tripleCompat_of_matched G srcN ei dstN hsrcN hei hdstN dir nsS nsD es2
          hnsSconf hnsDconf hes2conf hphi
      have srcMem : nsS ∈ refineSrcByCompat sN1 sE2 sN3 dir := by
        unfold refineSrcByCompat; rw [List.mem_filter]; refine ⟨hnsS_sN1, ?_⟩
        rw [List.any_eq_true]; refine ⟨es2, hes2_sE2, ?_⟩
        rw [List.any_eq_true]; exact ⟨nsD, hnsD_sN3, htc⟩
      have edgeMem : es2 ∈ refineEdgeByCompat sN1 sE2 sN3 dir := by
        unfold refineEdgeByCompat; rw [List.mem_filter]; refine ⟨hes2_sE2, ?_⟩
        rw [List.any_eq_true]; refine ⟨nsS, hnsS_sN1, ?_⟩
        rw [List.any_eq_true]; exact ⟨nsD, hnsD_sN3, htc⟩
      have dstMem : nsD ∈ refineDstByCompat sN1 sE2 sN3 dir := by
        unfold refineDstByCompat; rw [List.mem_filter]; refine ⟨hnsD_sN3, ?_⟩
        rw [List.any_eq_true]; refine ⟨nsS, hnsS_sN1, ?_⟩
        rw [List.any_eq_true]; exact ⟨es2, hes2_sE2, htc⟩
      intro x t hlk
      refine ⟨?_, ?_⟩
      · intro site ss hcomp g nn hn hlook
        rcases hnodekey hlook with ⟨hx1, hnn⟩ | ⟨_, hx2, hnn⟩
        · by_cases hsl : (n1.var == n2.var) = true
          · rw [← eq_of_beq hx1, RecordSchema.setMany3_lookup_eq13 _ n1.var rel.var n2.var _ _ _ hsl] at hlk
            obtain rfl := Option.some.inj hlk
            simp only [GSort.nodeRefinedOf, GSort.componentType, GSort.mk.injEq,
              SortShape.single.injEq, ExtSort.nodeRefined.injEq, true_and, and_true] at hcomp
            obtain ⟨_, rfl⟩ := hcomp
            have hnd : nn = dstN := hnn.trans (hagree hsl)
            subst hnd
            exact ⟨nsD, by rw [hDst']; exact dstMem, nodeConformsSchema_propMap hnsDconf⟩
          · have hd : (n2.var == n1.var) = false := by rw [name_beq_comm]; simpa using hsl
            rw [← eq_of_beq hx1, RecordSchema.setMany3_lookup_fst _ n1.var rel.var n2.var _ _ _ d_rn1 hd] at hlk
            obtain rfl := Option.some.inj hlk
            simp only [GSort.nodeRefinedOf, GSort.componentType, GSort.mk.injEq,
              SortShape.single.injEq, ExtSort.nodeRefined.injEq, true_and, and_true] at hcomp
            obtain ⟨_, rfl⟩ := hcomp
            subst hnn
            exact ⟨nsS, by rw [hSrc']; exact srcMem, nodeConformsSchema_propMap hnsSconf⟩
        · rw [← eq_of_beq hx2, RecordSchema.setMany3_lookup_thd _ n1.var rel.var n2.var _ _ _] at hlk
          obtain rfl := Option.some.inj hlk
          simp only [GSort.nodeRefinedOf, GSort.componentType, GSort.mk.injEq,
            SortShape.single.injEq, ExtSort.nodeRefined.injEq, true_and, and_true] at hcomp
          obtain ⟨_, rfl⟩ := hcomp
          subst hnn
          exact ⟨nsD, by rw [hDst']; exact dstMem, nodeConformsSchema_propMap hnsDconf⟩
      · intro site ss hcomp g ee he hlook
        obtain ⟨hxr, hee⟩ := hedgekey hlook
        rw [← eq_of_beq hxr, RecordSchema.setMany3_lookup_snd _ n1.var rel.var n2.var _ _ _ d_n2r] at hlk
        obtain rfl := Option.some.inj hlk
        simp only [GSort.edgeRefinedOf, GSort.componentType, GSort.mk.injEq,
          SortShape.single.injEq, ExtSort.edgeRefined.injEq, true_and, and_true] at hcomp
        obtain ⟨_, rfl⟩ := hcomp
        subst hee
        exact ⟨es2, by rw [hEdge']; exact edgeMem, edgeConformsSchema_propMap hes2conf⟩
  | closedEmpty hJC12 hJC23 hJC13 hSomeEmpty =>
      exfalso
      rcases hSomeEmpty with h | h | h
      · cases hAtomN1 with
        | nodeOpen v labels props hOpen =>
            simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.nodeOf] at h
        | nodeClosed v labels props Psi PhiPi zetaL zetaPrp zetaResult
            hClosed hSchema hPrpTyping hLblFilter hPrpFilter hResult hNE =>
            simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.nodeRefinedOf] at h
        | nodeClosedFail v labels props Psi PhiPi zetaL zetaPrp
            hClosed hSchema hPrpTyping hLblFilter hPrpFilter hEmpty =>
            exact not_mem_matchSingleEdge_of_src_filter_empty G Psi ctx.graphSite _ rel n2 dir
              PhiPi zetaL (hCat Psi hSchema) hPrpTyping hLblFilter (hPrpFilter ▸ hEmpty) rho hrho
      · cases hAtomE with
        | edgeOpen r labels props hOpen =>
            simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.edgeOf] at h
        | edgeClosed r labels props Psi PhiPi xiL xiPrp xiResult
            hClosed hSchema hPrpTyping hLblFilter hPrpFilter hResult hNE =>
            simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.edgeRefinedOf] at h
        | edgeClosedFail r labels props Psi PhiPi xiL xiPrp
            hClosed hSchema hPrpTyping hLblFilter hPrpFilter hEmpty =>
            exact not_mem_matchSingleEdge_of_edge_filter_empty G Psi ctx.graphSite n1 _ n2 dir
              PhiPi xiL (hCat Psi hSchema) hPrpTyping hLblFilter (hPrpFilter ▸ hEmpty) rho hrho
      · cases hAtomN2 with
        | nodeOpen v labels props hOpen =>
            simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.nodeOf] at h
        | nodeClosed v labels props Psi PhiPi zetaL zetaPrp zetaResult
            hClosed hSchema hPrpTyping hLblFilter hPrpFilter hResult hNE =>
            simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.nodeRefinedOf] at h
        | nodeClosedFail v labels props Psi PhiPi zetaL zetaPrp
            hClosed hSchema hPrpTyping hLblFilter hPrpFilter hEmpty =>
            exact not_mem_matchSingleEdge_of_dst_filter_empty G Psi ctx.graphSite n1 rel _ dir
              PhiPi zetaL (hCat Psi hSchema) hPrpTyping hLblFilter (hPrpFilter ▸ hEmpty) rho hrho
  | closedFail sN1 sE2 sN3 hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 hFail =>
      exfalso
      obtain ⟨Psi1, PhiPi1, hSchema1, hPrp1, hsN1eq⟩ := atomTyping_node_refined_inv hAtomN1 hNode1
      obtain ⟨Psi2, PhiPiE, hSchema2, hPrpE2, hsE2eq⟩ := atomTyping_edge_refined_inv hAtomE hEdge2
      obtain ⟨Psi3, PhiPi3, hSchema3, hPrp3, hsN3eq⟩ := atomTyping_node_refined_inv hAtomN2 hNode3
      have hP12 : Psi1 = Psi2 := Option.some.inj (hSchema1.symm.trans hSchema2)
      have hP13 : Psi1 = Psi3 := Option.some.inj (hSchema1.symm.trans hSchema3)
      rw [← hP12] at hsE2eq; rw [← hP13] at hsN3eq
      exact not_mem_matchSingleEdge_of_no_endpoint_triple G Psi1 ctx.graphSite n1 rel n2 dir
        PhiPi1 PhiPiE PhiPi3 sN1 sE2 sN3 (hCat Psi1 hSchema1) hPrp1 hPrpE2 hPrp3
        hsN1eq hsE2eq hsN3eq hFail rho hrho

/-- Strong graph-aware edge-pattern conformance. The `RuntimeConfigWFStrong`
    version of `matchSingleEdge_runtimeWF`: in the `closed` case, *every* catalog
    schema the matched endpoint/edge conforms to lands in the endpoint-compatible
    projection the (pinned) rule assigns. The current endpoint's membership uses
    the arbitrary conforming schema (via `filter...mem_of_conforms`), while the
    other two endpoints of the compatibility triple are still witnessed by graph
    conformance; `tripleCompat_of_matched` is parametric over all three schemas,
    so the mixed triple is compatible. `open` is vacuous; `closedEmpty`/`closedFail`
    make the matcher empty. -/
theorem matchSingleEdge_runtimeWFStrong
    (ctx : TypingCtx) (G : PropertyGraph) (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
    (GammaN1 GammaE GammaN2 GammaRef : RecordSchema)
    (hAtomN1 : AtomTyping ctx (AtomInput.node n1) GammaN1)
    (hAtomE : AtomTyping ctx (AtomInput.edge rel) GammaE)
    (hAtomN2 : AtomTyping ctx (AtomInput.node n2) GammaN2)
    (hRef : RefinementTyping ctx GammaN1 GammaE GammaN2 n1.var rel.var n2.var dir GammaRef)
    (hCat : ∀ Psi, ctx.schemaMap.lookup ctx.graphSite = some Psi →
              graphConformsSchema G Psi = true)
    (Psi : GraphSchemaFull)
    (hPsi : ctx.schemaMap.lookup ctx.graphSite = some Psi)
    (rho : Record) (hrho : rho ∈ matchSingleEdge G ctx.graphSite n1 rel n2 dir) :
    RuntimeConfigWFStrong G Psi rho GammaRef := by
  obtain ⟨T1, rfl⟩ := atomTyping_node_singleton hAtomN1
  obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
  obtain ⟨T2, rfl⟩ := atomTyping_node_singleton hAtomN2
  obtain ⟨srcN, ei, dstN, hsrcN, hei, hdstN, hsrcLbl, hsrcPrp, hlblE, hprpE,
          hlblD, hprpD, hphi, hagree, hform⟩ := matchSingleEdge_mem_form' hrho
  have hnodekey : ∀ {x : Name} {g : GraphSite} {nn : Nat}, rho.lookup x = Value.nodeRef g nn →
      ((n1.var == x) = true ∧ nn = srcN) ∨
      ((n1.var == x) = false ∧ (n2.var == x) = true ∧ nn = dstN) := by
    intro x g nn hl
    rw [hform] at hl
    cases hx1 : n1.var == x with
    | true =>
        left; refine ⟨rfl, ?_⟩
        simp only [Record.lookup, List.find?_cons, hx1] at hl
        injection hl with _ hnn; exact hnn.symm
    | false =>
        cases hxr : rel.var == x with
        | true => exfalso; simp only [Record.lookup, List.find?_cons, hx1, hxr] at hl; exact Value.noConfusion hl
        | false =>
            cases hx2 : n2.var == x with
            | true =>
                right; refine ⟨rfl, rfl, ?_⟩
                simp only [Record.lookup, List.find?_cons, hx1, hxr, hx2] at hl
                injection hl with _ hnn; exact hnn.symm
            | false => exfalso; simp only [Record.lookup, List.find?_cons, hx1, hxr, hx2] at hl; exact Value.noConfusion hl
  have hedgekey : ∀ {x : Name} {g : GraphSite} {ee : Nat}, rho.lookup x = Value.edgeRef g ee →
      (rel.var == x) = true ∧ ee = ei := by
    intro x g ee hl
    rw [hform] at hl
    cases hx1 : n1.var == x with
    | true => exfalso; simp only [Record.lookup, List.find?_cons, hx1] at hl; exact Value.noConfusion hl
    | false =>
        cases hxr : rel.var == x with
        | true =>
            refine ⟨rfl, ?_⟩
            simp only [Record.lookup, List.find?_cons, hx1, hxr] at hl
            injection hl with _ hee; exact hee.symm
        | false =>
            cases hx2 : n2.var == x with
            | true => exfalso; simp only [Record.lookup, List.find?_cons, hx1, hxr, hx2] at hl; exact Value.noConfusion hl
            | false => exfalso; simp only [Record.lookup, List.find?_cons, hx1, hxr, hx2] at hl; exact Value.noConfusion hl
  cases hRef with
  | open_ hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 =>
      simp only [singleton_schema_lookup, beq_self_eq_true, if_true, Option.some.injEq]
        at hNode1 hEdge2 hNode3
      subst hNode1; subst hEdge2; subst hNode3
      intro x t hlk
      refine ⟨?_, ?_⟩
      · intro site ss hcomp g nn hn hlook ns hmem hconf
        rcases open_join3_lookup_disj hlk with rfl | rfl | rfl <;>
          simp [GSort.nodeOf, GSort.edgeOf, GSort.botSort, GSort.componentType, GSort.nodeRefinedOf] at hcomp
      · intro site ss hcomp g ee he hlook es hmem hconf
        rcases open_join3_lookup_disj hlk with rfl | rfl | rfl <;>
          simp [GSort.nodeOf, GSort.edgeOf, GSort.botSort, GSort.componentType, GSort.edgeRefinedOf] at hcomp
  | closed sN1 sE2 sN3 sN1' sE2' sN3' hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 hSrc' hEdge' hDst' hNonEmpty =>
      obtain ⟨Psi1, PhiPi1, hSchema1, hPrp1, hsN1eq⟩ := atomTyping_node_refined_inv hAtomN1 hNode1
      obtain ⟨Psi2, PhiPiE, hSchema2, hPrpE2, hsE2eq⟩ := atomTyping_edge_refined_inv hAtomE hEdge2
      obtain ⟨Psi3, PhiPi3, hSchema3, hPrp3, hsN3eq⟩ := atomTyping_node_refined_inv hAtomN2 hNode3
      have hP12 : Psi1 = Psi2 := Option.some.inj (hSchema1.symm.trans hSchema2)
      have hP13 : Psi1 = Psi3 := Option.some.inj (hSchema1.symm.trans hSchema3)
      rw [← hP12] at hsE2eq; rw [← hP13] at hsN3eq
      have hPsiEq : Psi1 = Psi := Option.some.inj (hSchema1.symm.trans hPsi)
      subst hPsiEq
      have hGconf : graphConformsSchema G Psi1 = true := hCat Psi1 hSchema1
      obtain ⟨nsS, hnsS_Psi, hnsSconf⟩ := graphConformsSchema_node hGconf srcN hsrcN
      obtain ⟨es2, hes2_Psi, hes2conf⟩ := graphConformsSchema_edge hGconf ei hei
      obtain ⟨nsD, hnsD_Psi, hnsDconf⟩ := graphConformsSchema_node hGconf dstN hdstN
      have hnsS_sN1 : nsS ∈ sN1 := by
        rw [hsN1eq]
        exact filterNodeSchemasByPropCompat_mem_of_conforms G ctx.graphSite ⟨srcN, hsrcN⟩ nsS _ n1.props PhiPi1
          (resolveNodeSchemas_mem_of_conforms G Psi1 ⟨srcN, hsrcN⟩ nsS n1.labels hnsS_Psi hnsSconf hsrcLbl)
          hnsSconf hPrp1 hsrcPrp
      have hes2_sE2 : es2 ∈ sE2 := by
        rw [hsE2eq]
        exact filterEdgeSchemasByPropCompat_mem_of_conforms G ctx.graphSite ⟨ei, hei⟩ es2 _ rel.props PhiPiE
          (resolveEdgeSchemas_mem_of_conforms G Psi1 ⟨ei, hei⟩ es2 rel.labels hes2_Psi hes2conf hlblE)
          hes2conf hPrpE2 hprpE
      have hnsD_sN3 : nsD ∈ sN3 := by
        rw [hsN3eq]
        exact filterNodeSchemasByPropCompat_mem_of_conforms G ctx.graphSite ⟨dstN, hdstN⟩ nsD _ n2.props PhiPi3
          (resolveNodeSchemas_mem_of_conforms G Psi1 ⟨dstN, hdstN⟩ nsD n2.labels hnsD_Psi hnsDconf hlblD)
          hnsDconf hPrp3 hprpD
      have hT1 : T1 = GSort.nodeRefinedOf ctx.graphSite sN1 := by
        have h := hNode1; rw [singleton_schema_lookup] at h; simpa using h
      have hTE : TE = GSort.edgeRefinedOf ctx.graphSite sE2 := by
        have h := hEdge2; rw [singleton_schema_lookup] at h; simpa using h
      have hT2 : T2 = GSort.nodeRefinedOf ctx.graphSite sN3 := by
        have h := hNode3; rw [singleton_schema_lookup] at h; simpa using h
      have d_rn1 : (rel.var == n1.var) = false :=
        joinCompatible_singleton_distinct n1.var rel.var T1 TE
          (by rw [hT1, hTE]; exact sortInter_nodeRefinedOf_edgeRefinedOf_isBot _ _ _) hJC12
      have d_n2r : (n2.var == rel.var) = false :=
        joinCompatible_singleton_distinct rel.var n2.var TE T2
          (by rw [hTE, hT2]; exact sortInter_edgeRefinedOf_nodeRefinedOf_isBot _ _ _) hJC23
      intro x t hlk
      refine ⟨?_, ?_⟩
      · intro site ss hcomp g nn hn hlook ns hmem hconf
        rcases hnodekey hlook with ⟨hx1, hnn⟩ | ⟨_, hx2, hnn⟩
        · by_cases hsl : (n1.var == n2.var) = true
          · rw [← eq_of_beq hx1, RecordSchema.setMany3_lookup_eq13 _ n1.var rel.var n2.var _ _ _ hsl] at hlk
            obtain rfl := Option.some.inj hlk
            simp only [GSort.nodeRefinedOf, GSort.componentType, GSort.mk.injEq,
              SortShape.single.injEq, ExtSort.nodeRefined.injEq, true_and, and_true] at hcomp
            obtain ⟨_, rfl⟩ := hcomp
            have hconf' : nodeConformsSchema G ⟨dstN, hdstN⟩ ns := by
              have hfin : (⟨dstN, hdstN⟩ : Fin G.numNodes) = ⟨nn, hn⟩ :=
                Fin.ext (hnn.trans (hagree hsl)).symm
              rw [hfin]; exact hconf
            rw [hDst']
            unfold refineDstByCompat; rw [List.mem_filter]; refine ⟨?_, ?_⟩
            · rw [hsN3eq]
              exact filterNodeSchemasByPropCompat_mem_of_conforms G ctx.graphSite ⟨dstN, hdstN⟩ ns _ n2.props PhiPi3
                (resolveNodeSchemas_mem_of_conforms G Psi1 ⟨dstN, hdstN⟩ ns n2.labels hmem hconf' hlblD)
                hconf' hPrp3 hprpD
            · rw [List.any_eq_true]; refine ⟨nsS, hnsS_sN1, ?_⟩
              rw [List.any_eq_true]; exact ⟨es2, hes2_sE2,
                tripleCompat_of_matched G srcN ei dstN hsrcN hei hdstN dir nsS ns es2 hnsSconf hconf' hes2conf hphi⟩
          · have hd : (n2.var == n1.var) = false := by rw [name_beq_comm]; simpa using hsl
            rw [← eq_of_beq hx1, RecordSchema.setMany3_lookup_fst _ n1.var rel.var n2.var _ _ _ d_rn1 hd] at hlk
            obtain rfl := Option.some.inj hlk
            simp only [GSort.nodeRefinedOf, GSort.componentType, GSort.mk.injEq,
              SortShape.single.injEq, ExtSort.nodeRefined.injEq, true_and, and_true] at hcomp
            obtain ⟨_, rfl⟩ := hcomp
            have hconf' : nodeConformsSchema G ⟨srcN, hsrcN⟩ ns := by
              have hfin : (⟨srcN, hsrcN⟩ : Fin G.numNodes) = ⟨nn, hn⟩ := Fin.ext hnn.symm
              rw [hfin]; exact hconf
            rw [hSrc']
            unfold refineSrcByCompat; rw [List.mem_filter]; refine ⟨?_, ?_⟩
            · rw [hsN1eq]
              exact filterNodeSchemasByPropCompat_mem_of_conforms G ctx.graphSite ⟨srcN, hsrcN⟩ ns _ n1.props PhiPi1
                (resolveNodeSchemas_mem_of_conforms G Psi1 ⟨srcN, hsrcN⟩ ns n1.labels hmem hconf' hsrcLbl)
                hconf' hPrp1 hsrcPrp
            · rw [List.any_eq_true]; refine ⟨es2, hes2_sE2, ?_⟩
              rw [List.any_eq_true]; exact ⟨nsD, hnsD_sN3,
                tripleCompat_of_matched G srcN ei dstN hsrcN hei hdstN dir ns nsD es2 hconf' hnsDconf hes2conf hphi⟩
        · rw [← eq_of_beq hx2, RecordSchema.setMany3_lookup_thd _ n1.var rel.var n2.var _ _ _] at hlk
          obtain rfl := Option.some.inj hlk
          simp only [GSort.nodeRefinedOf, GSort.componentType, GSort.mk.injEq,
            SortShape.single.injEq, ExtSort.nodeRefined.injEq, true_and, and_true] at hcomp
          obtain ⟨_, rfl⟩ := hcomp
          have hconf' : nodeConformsSchema G ⟨dstN, hdstN⟩ ns := by
            have hfin : (⟨dstN, hdstN⟩ : Fin G.numNodes) = ⟨nn, hn⟩ := Fin.ext hnn.symm
            rw [hfin]; exact hconf
          rw [hDst']
          unfold refineDstByCompat; rw [List.mem_filter]; refine ⟨?_, ?_⟩
          · rw [hsN3eq]
            exact filterNodeSchemasByPropCompat_mem_of_conforms G ctx.graphSite ⟨dstN, hdstN⟩ ns _ n2.props PhiPi3
              (resolveNodeSchemas_mem_of_conforms G Psi1 ⟨dstN, hdstN⟩ ns n2.labels hmem hconf' hlblD)
              hconf' hPrp3 hprpD
          · rw [List.any_eq_true]; refine ⟨nsS, hnsS_sN1, ?_⟩
            rw [List.any_eq_true]; exact ⟨es2, hes2_sE2,
              tripleCompat_of_matched G srcN ei dstN hsrcN hei hdstN dir nsS ns es2 hnsSconf hconf' hes2conf hphi⟩
      · intro site ss hcomp g ee he hlook es hmem hconf
        obtain ⟨hxr, hee⟩ := hedgekey hlook
        rw [← eq_of_beq hxr, RecordSchema.setMany3_lookup_snd _ n1.var rel.var n2.var _ _ _ d_n2r] at hlk
        obtain rfl := Option.some.inj hlk
        simp only [GSort.edgeRefinedOf, GSort.componentType, GSort.mk.injEq,
          SortShape.single.injEq, ExtSort.edgeRefined.injEq, true_and, and_true] at hcomp
        obtain ⟨_, rfl⟩ := hcomp
        have hconf' : edgeConformsSchema G ⟨ei, hei⟩ es := by
          have hfin : (⟨ei, hei⟩ : Fin G.numEdges) = ⟨ee, he⟩ := Fin.ext hee.symm
          rw [hfin]; exact hconf
        rw [hEdge']
        unfold refineEdgeByCompat; rw [List.mem_filter]; refine ⟨?_, ?_⟩
        · rw [hsE2eq]
          exact filterEdgeSchemasByPropCompat_mem_of_conforms G ctx.graphSite ⟨ei, hei⟩ es _ rel.props PhiPiE
            (resolveEdgeSchemas_mem_of_conforms G Psi1 ⟨ei, hei⟩ es rel.labels hmem hconf' hlblE)
            hconf' hPrpE2 hprpE
        · rw [List.any_eq_true]; refine ⟨nsS, hnsS_sN1, ?_⟩
          rw [List.any_eq_true]; exact ⟨nsD, hnsD_sN3,
            tripleCompat_of_matched G srcN ei dstN hsrcN hei hdstN dir nsS nsD es hnsSconf hnsDconf hconf' hphi⟩
  | closedEmpty hJC12 hJC23 hJC13 hSomeEmpty =>
      exfalso
      rcases hSomeEmpty with h | h | h
      · cases hAtomN1 with
        | nodeOpen v labels props hOpen =>
            simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.nodeOf] at h
        | nodeClosed v labels props Psi PhiPi zetaL zetaPrp zetaResult
            hClosed hSchema hPrpTyping hLblFilter hPrpFilter hResult hNE =>
            simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.nodeRefinedOf] at h
        | nodeClosedFail v labels props Psi PhiPi zetaL zetaPrp
            hClosed hSchema hPrpTyping hLblFilter hPrpFilter hEmpty =>
            exact not_mem_matchSingleEdge_of_src_filter_empty G Psi ctx.graphSite _ rel n2 dir
              PhiPi zetaL (hCat Psi hSchema) hPrpTyping hLblFilter (hPrpFilter ▸ hEmpty) rho hrho
      · cases hAtomE with
        | edgeOpen r labels props hOpen =>
            simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.edgeOf] at h
        | edgeClosed r labels props Psi PhiPi xiL xiPrp xiResult
            hClosed hSchema hPrpTyping hLblFilter hPrpFilter hResult hNE =>
            simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.edgeRefinedOf] at h
        | edgeClosedFail r labels props Psi PhiPi xiL xiPrp
            hClosed hSchema hPrpTyping hLblFilter hPrpFilter hEmpty =>
            exact not_mem_matchSingleEdge_of_edge_filter_empty G Psi ctx.graphSite n1 _ n2 dir
              PhiPi xiL (hCat Psi hSchema) hPrpTyping hLblFilter (hPrpFilter ▸ hEmpty) rho hrho
      · cases hAtomN2 with
        | nodeOpen v labels props hOpen =>
            simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.nodeOf] at h
        | nodeClosed v labels props Psi PhiPi zetaL zetaPrp zetaResult
            hClosed hSchema hPrpTyping hLblFilter hPrpFilter hResult hNE =>
            simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.nodeRefinedOf] at h
        | nodeClosedFail v labels props Psi PhiPi zetaL zetaPrp
            hClosed hSchema hPrpTyping hLblFilter hPrpFilter hEmpty =>
            exact not_mem_matchSingleEdge_of_dst_filter_empty G Psi ctx.graphSite n1 rel _ dir
              PhiPi zetaL (hCat Psi hSchema) hPrpTyping hLblFilter (hPrpFilter ▸ hEmpty) rho hrho
  | closedFail sN1 sE2 sN3 hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 hFail =>
      exfalso
      obtain ⟨Psi1, PhiPi1, hSchema1, hPrp1, hsN1eq⟩ := atomTyping_node_refined_inv hAtomN1 hNode1
      obtain ⟨Psi2, PhiPiE, hSchema2, hPrpE2, hsE2eq⟩ := atomTyping_edge_refined_inv hAtomE hEdge2
      obtain ⟨Psi3, PhiPi3, hSchema3, hPrp3, hsN3eq⟩ := atomTyping_node_refined_inv hAtomN2 hNode3
      have hP12 : Psi1 = Psi2 := Option.some.inj (hSchema1.symm.trans hSchema2)
      have hP13 : Psi1 = Psi3 := Option.some.inj (hSchema1.symm.trans hSchema3)
      rw [← hP12] at hsE2eq; rw [← hP13] at hsN3eq
      exact not_mem_matchSingleEdge_of_no_endpoint_triple G Psi1 ctx.graphSite n1 rel n2 dir
        PhiPi1 PhiPiE PhiPi3 sN1 sE2 sN3 (hCat Psi1 hSchema1) hPrp1 hPrpE2 hPrp3
        hsN1eq hsE2eq hsN3eq hFail rho hrho

/-- `Pat-Edge` soundness for a non-quantified edge (`rel.quantifier = .single`).
    `evalPattern` reduces to `matchSingleEdge`; the typed schema is determined by
    the `RefinementTyping` derivation. The `open`/`closed` cases use the graph-
    unaware join/`setMany` conformance lemmas; `closedEmpty` is vacuous under graph
    conformance (`matchSingleEdge_conforms_closedEmpty`, bridged via
    `edge_atom_strip`). The `closedFail` case is vacuous too: its `hFail` premise
    (`endpointCompatTriple ... = false`) drives `matchSingleEdge_conforms_closedFail`. -/
theorem patternSound_edge_single
    (ctx : TypingCtx) (G : PropertyGraph)
    (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction)
    (GammaN1 GammaE GammaN2 GammaRef : RecordSchema)
    (hQ : rel.quantifier = .single)
    (hAtomN1 : AtomTyping ctx (.node n1) GammaN1)
    (hAtomE : AtomTyping ctx (.edge { var := rel.var, labels := rel.labels, props := rel.props }) GammaE)
    (hAtomN2 : AtomTyping ctx (.node n2) GammaN2)
    (hRef : RefinementTyping ctx GammaN1 GammaE GammaN2 n1.var rel.var n2.var dir GammaRef)
    (hCat : ∀ Psi, ctx.schemaMap.lookup ctx.graphSite = some Psi →
              graphConformsSchema G Psi = true) :
    BTConforms (evalPattern G ctx.graphSite (.edge n1 rel dir n2)) GammaRef := by
  obtain ⟨T1, rfl⟩ := atomTyping_node_singleton hAtomN1
  obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
  obtain ⟨T2, rfl⟩ := atomTyping_node_singleton hAtomN2
  rw [evalPattern_edge_single G ctx.graphSite n1 n2 rel dir hQ]
  cases hRef with
  | open_ hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 =>
    simp only [singleton_schema_lookup, beq_self_eq_true, if_true, Option.some.injEq]
      at hNode1 hEdge2 hNode3
    subst hNode1; subst hEdge2; subst hNode3
    exact matchSingleEdge_conforms_open G ctx.graphSite n1 n2 rel dir
      (joinCompatible_singleton_distinct n1.var rel.var _ _
        (sortInter_nodeOf_edgeOf_isBot _) hJC12)
      (beq_name_symm_false (joinCompatible_singleton_distinct rel.var n2.var _ _
        (sortInter_edgeOf_nodeOf_isBot _) hJC23))
  | closed sN1 sE2 sN3 sN1' sE2' sN3' hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 hSrc' hEdge' hDst' hNonEmpty =>
    simp only [singleton_schema_lookup, beq_self_eq_true, if_true, Option.some.injEq]
      at hNode1 hEdge2 hNode3
    subst hNode1; subst hEdge2; subst hNode3
    exact matchSingleEdge_conforms_closed G ctx.graphSite n1 n2 rel dir _ _ _ sN1' sE2' sN3'
      (joinCompatible_singleton_distinct n1.var rel.var _ _
        (sortInter_nodeRefinedOf_edgeRefinedOf_isBot _ _ _) hJC12)
      (beq_name_symm_false (joinCompatible_singleton_distinct rel.var n2.var _ _
        (sortInter_edgeRefinedOf_nodeRefinedOf_isBot _ _ _) hJC23))
  | closedEmpty hJC12 hJC23 hJC13 hSomeEmpty =>
    exact matchSingleEdge_conforms_closedEmpty ctx G n1 n2 rel dir _ _ _ _
      hAtomN1 (edge_atom_strip hQ ▸ hAtomE) hAtomN2 hCat hSomeEmpty
  | closedFail sN1 sE2 sN3 hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 hFail =>
    exact matchSingleEdge_conforms_closedFail ctx G n1 n2 rel dir _ _ _ _ sN1 sE2 sN3
      hAtomN1 (edge_atom_strip hQ ▸ hAtomE) hAtomN2 hNode1 hEdge2 hNode3 hCat hFail

/-- `Pat-Quant-Edge` soundness for a group-reference quantifier (`*`, `+`, `{i}`,
    `{i,j}`). The single-edge base typing `hBase` is in `.inside` mode, so it can
    only have come from `Pat-Edge` (the quantified/optional edge rules are
    `.outside`-only) -- inverting it exposes the three endpoint atoms and the
    refinement. `evalPattern` of the quantified edge is a variable-length path; the
    `open`/`closed` refinements reuse the lifted (group-ref) path conformance
    lemmas. The `closedEmpty`/`closedFail` refinements both produce an all-empty
    `setMany` base, whose lifted form is the zero-length-path defect (blocked on the
    author); both are covered by the single `hEmptyLift` hypothesis. `hH4`/`hfresh`
    are the recursion's hygiene side-conditions (discharged by the fresh-name fix). -/
theorem patternSound_quantEdge
    (ctx : TypingCtx) (G : PropertyGraph)
    (n1 n2 : NodeAtom) (rel : EdgeAtom) (dir : Direction) (K : Quantifier)
    (GammaBase : RecordSchema)
    (hBase : PatternTyping ctx .inside
      (.edge n1 { rel with quantifier := .single } dir n2) GammaBase n2.var)
    (hQuant : K.isGroupRef = true)
    (hEdgeVar : GammaBase.mem rel.var = true)
    (hEmptyLift : ∀ (TN1 TE TN2 : GSort),
       BTConforms (evalPattern G ctx.graphSite (.edge n1 { rel with quantifier := K } dir n2))
         ((((RecordSchema.mk [(n1.var, TN1)]).join (RecordSchema.mk [(rel.var, TE)])
            |>.join (RecordSchema.mk [(n2.var, TN2)])).setMany
           [(n1.var, GSort.nodeEmpty ctx.graphSite),
            (rel.var, GSort.edgeEmpty ctx.graphSite),
            (n2.var, GSort.nodeEmpty ctx.graphSite)]).liftToGroupRef [rel.var])) :
    BTConforms (evalPattern G ctx.graphSite (.edge n1 { rel with quantifier := K } dir n2))
      (GammaBase.liftToGroupRef [rel.var]) := by
  cases hBase
  rename_i hAtomN1 hSingle' hAtomE hAtomN2 hRef
  obtain ⟨T1, rfl⟩ := atomTyping_node_singleton hAtomN1
  obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
  obtain ⟨T2, rfl⟩ := atomTyping_node_singleton hAtomN2
  cases hRef with
    | open_ hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 =>
      simp only [singleton_schema_lookup, beq_self_eq_true, if_true, Option.some.injEq]
        at hNode1 hEdge2 hNode3
      subst hNode1; subst hEdge2; subst hNode3
      exact evalPattern_quantEdge_conforms_open G ctx.graphSite n1 n2
        { rel with quantifier := K } dir hQuant
        (joinCompatible_singleton_distinct n1.var rel.var _ _
          (sortInter_nodeOf_edgeOf_isBot _) hJC12)
        (beq_name_symm_false (joinCompatible_singleton_distinct rel.var n2.var _ _
          (sortInter_edgeOf_nodeOf_isBot _) hJC23))
    | closed sN1 sE2 sN3 sN1' sE2' sN3' hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 hSrc' hEdge' hDst' hNonEmpty =>
      simp only [singleton_schema_lookup, beq_self_eq_true, if_true, Option.some.injEq]
        at hNode1 hEdge2 hNode3
      subst hNode1; subst hEdge2; subst hNode3
      exact evalPattern_quantEdge_conforms_closed G ctx.graphSite n1 n2
        { rel with quantifier := K } dir _ _ _ sN1' sE2' sN3' hQuant
        (joinCompatible_singleton_distinct n1.var rel.var _ _
          (sortInter_nodeRefinedOf_edgeRefinedOf_isBot _ _ _) hJC12)
        (beq_name_symm_false (joinCompatible_singleton_distinct rel.var n2.var _ _
          (sortInter_edgeRefinedOf_nodeRefinedOf_isBot _ _ _) hJC23))
    | closedEmpty hJC12 hJC23 hJC13 hSomeEmpty =>
      exact hEmptyLift T1 TE T2
    | closedFail sN1 sE2 sN3 hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 hFail =>
      exact hEmptyLift T1 TE T2

/-- The tail variable a pattern is typed with is exactly the one the evaluator
    reads off via `patternTailVar`. Needed to connect a step's prefix typing
    (tail `v1`) to the runtime lookup `rho.lookup (patternTailVar P)`. The node /
    edge / step / quantified-edge cases are definitional; the grouped and
    quantified-path cases peel to the inner pattern via the induction hypothesis. -/
theorem patternTyping_tailVar {ctx : TypingCtx} {qd : QuantDepth}
    {P : Pattern} {Gamma : RecordSchema} {v : Name}
    (h : PatternTyping ctx qd P Gamma v) : patternTailVar P = some v := by
  induction h with
  | patNode => rfl
  | patEdge => rfl
  | patStep => rfl
  | patQuantEdge => rfl
  | patOptEdge => rfl
  | patQuantPath _ _ _ _ _ _ ih => exact ih
  | patGrouped _ _ _ _ _ ih => exact ih

-- ============================================================
--  The quantified-path evaluator conforms.
--
--  `evalQuantified` exposes every variable inside a quantifier as the list of its
--  per-iteration bindings (Pat-Quant-Path's pointwise lift). List admissibility
--  is element-unaware (`ofList_adm_liftToList`), so the conformance reduces to one
--  structural fact -- every output record is a `collapsePath` -- with no
--  element-level reasoning. The graph-aware (`RuntimeConfigWFStrong`) version is
--  vacuous: that predicate only constrains node/edge-ref bindings, and every
--  binding here is a list.
-- ============================================================

/-- The group-reference conformance bridge (per record): a record whose every
    lifted variable is a list value, with the right domain, conforms to the
    group-reference lift. -/
theorem liftToGroupRef_conforms_of_listForm
    (rho : Record) (GammaInner : RecordSchema) (innerVars : List Name)
    (hdom : ∀ z, rho.mem z = GammaInner.mem z)
    (hlist : ∀ z, innerVars.any (fun v => v == z) = true →
        ∃ es, rho.lookup z = Value.ofList es)
    (hrest : ∀ z t, (z, t) ∈ GammaInner.entries →
        innerVars.any (fun v => v == z) = false →
        RecordSchema.valueAdmissible (rho.lookup z) t = true) :
    RecordConforms rho (GammaInner.liftToGroupRef innerVars) := by
  refine ⟨fun z => ?_, fun z t' hzt => ?_⟩
  · rw [RecordSchema.liftToGroupRef_mem]; exact hdom z
  · obtain ⟨t0, ht0mem, ht0eq⟩ := RecordSchema.mem_liftToGroupRef_entries hzt
    rw [ht0eq]
    split
    · rename_i hcond
      obtain ⟨es, hes⟩ := hlist z hcond
      rw [hes]; exact ofList_adm_liftToList es t0
    · rename_i hcond
      rw [Bool.not_eq_true] at hcond
      exact hrest z t0 ht0mem hcond

/-- BTConforms form of the bridge (the precise leaf shape against the evaluator). -/
theorem liftToGroupRef_btconforms_of_listForm
    (B : BindingTable) (GammaInner : RecordSchema) (innerVars : List Name)
    (hB : ∀ rho ∈ B,
      (∀ z, rho.mem z = GammaInner.mem z) ∧
      (∀ z, innerVars.any (fun v => v == z) = true → ∃ es, rho.lookup z = Value.ofList es) ∧
      (∀ z t, (z, t) ∈ GammaInner.entries → innerVars.any (fun v => v == z) = false →
          RecordSchema.valueAdmissible (rho.lookup z) t = true)) :
    BTConforms B (GammaInner.liftToGroupRef innerVars) := by
  intro rho hrho
  obtain ⟨hdom, hlist, hrest⟩ := hB rho hrho
  exact liftToGroupRef_conforms_of_listForm rho GammaInner innerVars hdom hlist hrest

/-- `collapsePath` binds exactly the variables in `vars`. -/
theorem collapsePath_mem (vars : List Name) (path : List Record) (z : Name) :
    (collapsePath vars path).mem z = vars.any (fun v => v == z) := by
  unfold collapsePath Record.mem
  induction vars with
  | nil => rfl
  | cons hd tl ih => simp only [List.map_cons, List.any_cons, ih]

/-- Every variable `collapsePath` binds is bound to a list value. -/
theorem collapsePath_lookup_ofList (vars : List Name) (path : List Record) (z : Name)
    (hz : vars.any (fun v => v == z) = true) :
    ∃ es, (collapsePath vars path).lookup z = Value.ofList es := by
  induction vars with
  | nil => simp at hz
  | cons hd tl ih =>
    simp only [List.any_cons, Bool.or_eq_true] at hz
    by_cases hc : (hd == z) = true
    · exact ⟨path.map (fun r => r.lookup hd), by
        simp only [collapsePath, List.map_cons, Record.lookup, List.find?_cons, hc, if_true]⟩
    · have htl : tl.any (fun v => v == z) = true := by
        rcases hz with h | h
        · exact absurd h hc
        · exact h
      obtain ⟨es, hes⟩ := ih htl
      refine ⟨es, ?_⟩
      have hcf : (hd == z) = false := by
        cases hb : (hd == z) with
        | true => exact absurd hb hc
        | false => rfl
      simp only [collapsePath, List.map_cons, Record.lookup, List.find?_cons, hcf, if_false]
      simpa only [collapsePath, Record.lookup] using hes

/-- Every record the iterator accumulates is a `collapsePath` (list form). -/
theorem qpathIterate_listForm
    (baseResults : List Record) (vars : List Name) (lv tv : Name) (lo hi : Nat) :
    ∀ (fuel kappa : Nat) (frontier : List (List Record × Value)) (accumulated : List Record),
      (∀ rho ∈ accumulated, ∃ path, rho = collapsePath vars path) →
      ∀ rho ∈ qpathIterate baseResults vars lv tv lo hi kappa frontier accumulated fuel,
        ∃ path, rho = collapsePath vars path := by
  intro fuel
  induction fuel with
  | zero =>
    intro kappa frontier accumulated hacc rho hrho
    simp only [qpathIterate] at hrho
    exact hacc rho hrho
  | succ fuel' ih =>
    intro kappa frontier accumulated hacc rho hrho
    simp only [qpathIterate] at hrho
    split at hrho
    · exact hacc rho hrho
    · refine ih (kappa + 1) _ _ (fun rho' hrho' => ?_) rho hrho
      split at hrho'
      · rw [List.mem_append] at hrho'
        rcases hrho' with h | h
        · exact hacc rho' h
        · obtain ⟨pe, _, hpe⟩ := List.mem_map.mp h
          exact ⟨pe.fst, hpe.symm⟩
      · exact hacc rho' hrho'

/-- Every output record of the corrected quantified-path evaluator is a
    `collapsePath` over `vars`. -/
theorem evalQuantified_listForm
    (vars : List Name) (baseResults : List Record) (lv tv : Name) (lo hi : Nat)
    (rho : Record) (hrho : rho ∈ evalQuantified vars baseResults lv tv lo hi) :
    ∃ path, rho = collapsePath vars path := by
  simp only [evalQuantified] at hrho
  rw [List.mem_append] at hrho
  rcases hrho with hz | hq
  · split at hz
    · rw [List.mem_singleton] at hz; exact ⟨[], hz⟩
    · exact absurd hz (List.not_mem_nil rho)
  · exact qpathIterate_listForm baseResults vars lv tv lo hi (hi + 1) 1 _ []
      (fun _ h => absurd h (List.not_mem_nil _)) rho hq

/-- `collapsePath` is ref-bounded: every variable it collapses is bound to a list
    (the per-iteration group-reference lift). -/
theorem collapsePath_refBoundWF {G : PropertyGraph} (vars : List Name) (path : List Record) :
    RecordRefBoundWF G (collapsePath vars path) := by
  intro x hx
  rw [collapsePath_mem] at hx
  obtain ⟨es, hes⟩ := collapsePath_lookup_ofList vars path x hx
  exact Or.inr (Or.inr (Or.inl ⟨ValueList.ofList es, hes⟩))

/-- The `.step` case of `evalPattern_refBoundWF`: every step output is a merge of a
    prefix record (ref-bounded by the sub-pattern IH `ihP`) and an edge record
    (ref-bounded by `matchSingleEdge`/`matchRangePath`), for either quantifier. -/
theorem step_refBoundWF (G : PropertyGraph) (site : GraphSite)
    (P : Pattern) (rel : EdgeAtom) (dir : Direction) (n2 : NodeAtom)
    (ihP : ∀ rho, rho ∈ evalPattern G site P → RecordRefBoundWF G rho)
    (rho_out : Record) (h : rho_out ∈ evalPattern G site (.step P rel dir n2)) :
    RecordRefBoundWF G rho_out := by
  simp only [evalPattern] at h
  rw [List.mem_flatMap] at h
  obtain ⟨rho, hrho, hbody⟩ := h
  cases htv : patternTailVar P with
  | none => rw [htv] at hbody; simp at hbody
  | some tv =>
    rw [htv] at hbody
    cases htl : rho.lookup tv with
    | nodeRef g n =>
      simp only [htl] at hbody
      split at hbody
      all_goals (
        rw [List.mem_filterMap] at hbody
        obtain ⟨rhoEdge, hedge, hsome⟩ := hbody
        split at hsome
        · rw [← Option.some.inj hsome]
          exact RecordRefBoundWF.merge (ihP rho hrho)
            (by first
               | exact matchSingleEdge_refBoundWF hedge
               | exact matchOptionalEdge_refBoundWF hedge
               | exact matchRangePath_refBoundWF _ _ _ _ _ _ _ _ _ hedge)
        · exact absurd hsome (by simp))
    | prim _ => simp [htl] at hbody
    | edgeRef _ _ => simp [htl] at hbody
    | list _ => simp [htl] at hbody
    | null => simp [htl] at hbody

/-- Value-side soundness of pattern evaluation: every binding produced is an
    in-bounds node/edge reference or a list -- never a scalar and never `null`.
    This is the fact the join vacuity needs at empty-former meets. -/
theorem evalPattern_refBoundWF (G : PropertyGraph) (site : GraphSite) :
    ∀ (P : Pattern) (rho : Record), rho ∈ evalPattern G site P → RecordRefBoundWF G rho := by
  intro P
  induction P with
  | node na => intro rho h; exact matchNode_refBoundWF h
  | edge n1 rel dir n2 =>
    intro rho h
    simp only [evalPattern] at h
    split at h
    · exact matchSingleEdge_refBoundWF h
    · exact matchOptionalEdge_refBoundWF h
    · exact matchRangePath_refBoundWF _ _ _ _ _ _ _ _ _ h
  | step P rel dir n2 ihP => intro rho h; exact step_refBoundWF G site P rel dir n2 ihP rho h
  | grouped P ihP => intro rho h; rw [evalPattern_grouped] at h; exact ihP rho h
  | quantified P K ihP =>
    intro rho h
    simp only [evalPattern] at h
    split at h
    · obtain ⟨path, rfl⟩ := evalQuantified_listForm (patternVars P) _ _ _ _ _ rho h
      exact collapsePath_refBoundWF (patternVars P) path
    all_goals exact ihP rho h
  | patternList P1 P2 ih1 ih2 =>
    intro rho h
    rw [evalPattern_patternList] at h
    obtain ⟨rho1, hrho1, rho2, hrho2, _, rfl⟩ := mem_bindingTableJoin h
    exact RecordRefBoundWF.merge (ih1 rho1 hrho1) (ih2 rho2 hrho2)

/-- The #5 leaf: the quantified-path output conforms to the group-reference lift,
    given `vars` = `dom(GammaInner)` and (at top level) `innerVars` = `vars`. -/
theorem evalQuantified_btconforms
    (vars : List Name) (baseResults : List Record) (lv tv : Name) (lo hi : Nat)
    (GammaInner : RecordSchema) (innerVars : List Name)
    (hvars : ∀ z, vars.any (fun v => v == z) = GammaInner.mem z)
    (hinner : ∀ z, innerVars.any (fun v => v == z) = vars.any (fun v => v == z)) :
    BTConforms (evalQuantified vars baseResults lv tv lo hi)
      (GammaInner.liftToGroupRef innerVars) := by
  apply liftToGroupRef_btconforms_of_listForm
  intro rho hrho
  obtain ⟨path, rfl⟩ := evalQuantified_listForm vars baseResults lv tv lo hi rho hrho
  refine ⟨fun z => ?_, fun z hz => ?_, fun z t hzt hz => ?_⟩
  · rw [collapsePath_mem]; exact hvars z
  · rw [hinner z] at hz; exact collapsePath_lookup_ofList vars path z hz
  · exfalso
    rw [hinner z] at hz
    have hmem : GammaInner.mem z = true := RecordSchema.mem_of_entry hzt
    rw [← hvars z, hz] at hmem
    exact Bool.noConfusion hmem

/-- The #5 STRONG leaf: `RuntimeConfigWFStrong` is vacuous for the corrected
    evaluator, since every variable is bound to a list (never a node/edge ref). -/
theorem evalQuantified_runtimeWFStrong
    (G : PropertyGraph) (Psi : GraphSchemaFull)
    (vars : List Name) (baseResults : List Record) (lv tv : Name) (lo hi : Nat)
    (GammaInner : RecordSchema) (innerVars : List Name)
    (hvars : ∀ z, vars.any (fun v => v == z) = GammaInner.mem z)
    (_hinner : ∀ z, innerVars.any (fun v => v == z) = vars.any (fun v => v == z)) :
    ∀ rho ∈ evalQuantified vars baseResults lv tv lo hi,
      RuntimeConfigWFStrong G Psi rho (GammaInner.liftToGroupRef innerVars) := by
  intro rho hrho
  obtain ⟨path, rfl⟩ := evalQuantified_listForm vars baseResults lv tv lo hi rho hrho
  intro x t hlk
  have hxv : vars.any (fun v => v == x) = true := by
    have hmem : (GammaInner.liftToGroupRef innerVars).mem x = true :=
      RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem hlk)
    rw [RecordSchema.liftToGroupRef_mem, ← hvars x] at hmem
    exact hmem
  obtain ⟨es, hes⟩ := collapsePath_lookup_ofList vars path x hxv
  refine ⟨fun site ss _ g n hn hnr => ?_, fun site ss _ g ed he her => ?_⟩
  · rw [hes] at hnr; exact Value.noConfusion hnr
  · rw [hes] at her; exact Value.noConfusion her

/-- The refinement output schema's domain is the union of the three input
    domains. The output is `(G1 ⋈ G2 ⋈ G3).setMany [(v1,_),(r2,_),(v3,_)]` (or the
    bare join for `open_`), and `setMany` ADDS those three keys; each is absorbed
    into its input schema via the supplied membership facts. -/
theorem refinementTyping_mem {ctx : TypingCtx} {G1 G2 G3 : RecordSchema}
    {v1 r2 v3 : Name} {dir : Direction} {GammaRef : RecordSchema}
    (h : RefinementTyping ctx G1 G2 G3 v1 r2 v3 dir GammaRef)
    (hv1 : G1.mem v1 = true) (hr2 : G2.mem r2 = true) (hv3 : G3.mem v3 = true) (z : Name) :
    GammaRef.mem z = (G1.mem z || G2.mem z || G3.mem z) := by
  have a1 : (v1 == z) = true → G1.mem z = true := fun hh => by
    have e : v1 = z := eq_of_beq hh; subst e; exact hv1
  have a2 : (r2 == z) = true → G2.mem z = true := fun hh => by
    have e : r2 = z := eq_of_beq hh; subst e; exact hr2
  have a3 : (v3 == z) = true → G3.mem z = true := fun hh => by
    have e : v3 = z := eq_of_beq hh; subst e; exact hv3
  cases h with
  | open_ => rw [RecordSchema.join_mem, RecordSchema.join_mem, Bool.or_assoc]
  | closed =>
      rw [RecordSchema.setMany_mem, RecordSchema.join_mem, RecordSchema.join_mem]
      cases hg1 : G1.mem z <;> cases hg2 : G2.mem z <;> cases hg3 : G3.mem z <;>
        cases hc1 : (v1 == z) <;> cases hc2 : (r2 == z) <;> cases hc3 : (v3 == z) <;>
        simp_all [List.any_cons]
  | closedEmpty =>
      rw [RecordSchema.setMany_mem, RecordSchema.join_mem, RecordSchema.join_mem]
      cases hg1 : G1.mem z <;> cases hg2 : G2.mem z <;> cases hg3 : G3.mem z <;>
        cases hc1 : (v1 == z) <;> cases hc2 : (r2 == z) <;> cases hc3 : (v3 == z) <;>
        simp_all [List.any_cons]
  | closedFail =>
      rw [RecordSchema.setMany_mem, RecordSchema.join_mem, RecordSchema.join_mem]
      cases hg1 : G1.mem z <;> cases hg2 : G2.mem z <;> cases hg3 : G3.mem z <;>
        cases hc1 : (v1 == z) <;> cases hc2 : (r2 == z) <;> cases hc3 : (v3 == z) <;>
        simp_all [List.any_cons]

/-- The third (trailing-node) refinement variable is always in the refinement
    output: it is a `setMany` key in the closed cases, and is in `G3` (via the
    `open_` lookup) otherwise. -/
theorem refinementTyping_tailVar_mem {ctx : TypingCtx} {G1 G2 G3 : RecordSchema}
    {v1 r2 v3 : Name} {dir : Direction} {GammaRef : RecordSchema}
    (h : RefinementTyping ctx G1 G2 G3 v1 r2 v3 dir GammaRef) :
    GammaRef.mem v3 = true := by
  cases h with
  | open_ _ _ hN3 _ _ _ =>
      rw [RecordSchema.join_mem, RecordSchema.join_mem]
      have h3 : G3.mem v3 = true := RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem hN3)
      simp [h3]
  | closed => rw [RecordSchema.setMany_mem]; simp
  | closedEmpty => rw [RecordSchema.setMany_mem]; simp
  | closedFail => rw [RecordSchema.setMany_mem]; simp

/-- A pattern's trailing variable is in the schema it is typed to. -/
theorem patternTyping_tailVar_mem {ctx : TypingCtx} {qd : QuantDepth}
    {P : Pattern} {Gamma : RecordSchema} {v : Name}
    (h : PatternTyping ctx qd P Gamma v) : Gamma.mem v = true := by
  induction h with
  | patNode qd na GammaA hAtom =>
      obtain ⟨T, rfl⟩ := atomTyping_node_singleton hAtom
      simp [RecordSchema.mem]
  | patEdge qd n1 n2 rel dir GammaN1 GammaE GammaN2 GammaRef hSingleD hAtomN1 hAtomE hAtomN2 hRef =>
      exact refinementTyping_tailVar_mem hRef
  | patStep qd P rel dir n2 Gamma1 GammaE GammaN2 GammaRef v1 hSingle hPrefix hAtomE hAtomN2 hRef ihPrefix =>
      exact refinementTyping_tailVar_mem hRef
  | patQuantEdge n1 n2 rel dir K GammaE hQuant hAtomE hNE12 hNE23 =>
      rw [RecordSchema.liftToGroupRef_mem]
      rw [RecordSchema.join_mem]; simp [RecordSchema.mem]
  | patOptEdge n1 n2 rel dir hNE12 hNE23 =>
      rw [RecordSchema.liftToNullable_mem]
      rw [RecordSchema.join_mem]; simp [RecordSchema.mem]
  | patQuantPath P K GammaInner v hInner hQuant ihInner =>
      rw [RecordSchema.liftToGroupRef_mem]; exact ihInner
  | patGrouped qd P Gamma v hP ihP => exact ihP

/-- A pattern's syntactic variable set equals the domain of the schema it is
    typed to (`patternVars P = dom(Gamma)`, as membership). -/
theorem patternTyping_vars_mem {ctx : TypingCtx} {qd : QuantDepth}
    {P : Pattern} {Gamma : RecordSchema} {v : Name}
    (h : PatternTyping ctx qd P Gamma v) :
    ∀ z, (patternVars P).any (fun w => w == z) = Gamma.mem z := by
  induction h with
  | patNode qd na GammaA hAtom =>
      intro z
      obtain ⟨T, rfl⟩ := atomTyping_node_singleton hAtom
      simp [patternVars, RecordSchema.mem]
  | patEdge qd n1 n2 rel dir GammaN1 GammaE GammaN2 GammaRef hSingleD hAtomN1 hAtomE hAtomN2 hRef =>
      intro z
      obtain ⟨T1, rfl⟩ := atomTyping_node_singleton hAtomN1
      obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
      obtain ⟨T2, rfl⟩ := atomTyping_node_singleton hAtomN2
      rw [refinementTyping_mem hRef (by simp [RecordSchema.mem])
            (by simp [RecordSchema.mem]) (by simp [RecordSchema.mem])]
      simp [patternVars, RecordSchema.mem, Bool.or_assoc]
  | patStep qd P rel dir n2 Gamma1 GammaE GammaN2 GammaRef v1 hSingle hPrefix hAtomE hAtomN2 hRef ihPrefix =>
      intro z
      obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
      obtain ⟨T2, rfl⟩ := atomTyping_node_singleton hAtomN2
      rw [refinementTyping_mem hRef (patternTyping_tailVar_mem hPrefix)
            (by simp [RecordSchema.mem]) (by simp [RecordSchema.mem])]
      show (patternVars P ++ [rel.var, n2.var]).any (fun w => w == z) = _
      rw [List.any_append, ihPrefix z]
      simp [RecordSchema.mem, List.any_cons, Bool.or_assoc]
  | patQuantEdge n1 n2 rel dir K GammaE hQuant hAtomE hNE12 hNE23 =>
      intro z
      obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
      rw [RecordSchema.liftToGroupRef_mem]
      simp only [patternVars, List.any_cons, List.any_nil, Bool.or_false]
      rw [RecordSchema.join_mem, RecordSchema.join_mem]
      simp [RecordSchema.mem, Bool.or_assoc]
  | patOptEdge n1 n2 rel dir hNE12 hNE23 =>
      intro z
      rw [RecordSchema.liftToNullable_mem]
      simp only [patternVars, List.any_cons, List.any_nil, Bool.or_false]
      rw [RecordSchema.join_mem, RecordSchema.join_mem]
      simp [RecordSchema.mem, Bool.or_assoc]
  | patQuantPath P K GammaInner v hInner hQuant ihInner =>
      intro z; rw [RecordSchema.liftToGroupRef_mem]; exact ihInner z
  | patGrouped qd P Gamma v hP ihP =>
      intro z; exact ihP z

/-- Every pattern has a leading node variable. -/
theorem patternLeadVar_isSome (P : Pattern) : ∃ lv, patternLeadVar P = some lv := by
  induction P with
  | node na => exact ⟨na.var, rfl⟩
  | edge n1 _ _ _ => exact ⟨n1.var, rfl⟩
  | step _ _ _ _ ih => exact ih
  | grouped _ ih => exact ih
  | quantified _ _ ih => exact ih
  | patternList _ _ ih1 _ => exact ih1

/-- Every pattern has a trailing node variable. -/
theorem patternTailVar_isSome (P : Pattern) : ∃ tv, patternTailVar P = some tv := by
  induction P with
  | node na => exact ⟨na.var, rfl⟩
  | edge _ _ _ n2 => exact ⟨n2.var, rfl⟩
  | step _ _ _ n2 _ => exact ⟨n2.var, rfl⟩
  | grouped _ ih => exact ih
  | quantified _ _ ih => exact ih
  | patternList _ _ _ ih2 => exact ih2

/-- Membership over a schema's domain list agrees with `mem`. -/
theorem RecordSchema.dom_any_mem (Gamma : RecordSchema) (z : Name) :
    Gamma.dom.any (fun w => w == z) = Gamma.mem z := by
  unfold RecordSchema.dom RecordSchema.mem
  induction Gamma.entries with
  | nil => rfl
  | cons hd tl ih => simp only [List.map_cons, List.any_cons, ih]

/-- Membership form for a single-edge step: every record of `evalPattern (.step P
    rel dir n2)` (with `rel` single) is `rho.merge rhoEdge` for a prefix record
    `rho` and a single edge `rhoEdge` out of the prefix tail, where the two agree
    on every shared variable (the natural-equijoin condition). -/
theorem evalPattern_step_single_mem (G : PropertyGraph) (site : GraphSite)
    (P : Pattern) (rel : EdgeAtom) (dir : Direction) (n2 : NodeAtom) (tv : Name)
    (hSingle : rel.quantifier = .single) (htv : patternTailVar P = some tv)
    (rho_out : Record) (h : rho_out ∈ evalPattern G site (.step P rel dir n2)) :
    ∃ rho rhoEdge, rho ∈ evalPattern G site P ∧
      rhoEdge ∈ matchSingleEdge G site { var := tv } { rel with quantifier := .single } n2 dir ∧
      rho.agreeOn rhoEdge = true ∧ (∃ gg nn, rho.lookup tv = Value.nodeRef gg nn) ∧
      rho_out = rho.merge rhoEdge := by
  simp only [evalPattern, htv, hSingle, List.mem_flatMap] at h
  obtain ⟨rho, hrho, hin⟩ := h
  refine ⟨rho, ?_⟩
  cases htail : rho.lookup tv with
  | nodeRef g n =>
    simp only [htail, List.mem_filterMap] at hin
    obtain ⟨rhoEdge, hedge, hsome⟩ := hin
    split at hsome
    · refine ⟨rhoEdge, hrho, hedge, ?_, ⟨g, n, rfl⟩, ?_⟩
      · assumption
      · exact (Option.some.inj hsome).symm
    · exact absurd hsome (by simp)
  | prim _ => simp [htail] at hin
  | edgeRef _ _ => simp [htail] at hin
  | list _ => simp [htail] at hin
  | null => simp [htail] at hin

-- ============================================================
--  The `hSingle` obligation, assembled (per-pattern soundness)
--
--  `patternTyping_sound` is the per-pattern half of Theorem 6.2: every record the
--  evaluator produces for a single (path) pattern fits the type the type-checker
--  assigned. It is proved by induction on `PatternTyping`, dispatching the three
--  proven structural cases to the standalone `patternSound_*` lemmas and the
--  grouping case to the induction hypothesis. (Optional `?` is unsupported, so
--  its rules have been removed from the model; the former `hEdgeQuestion`,
--  `hOptEdge`, and `hOptPath` obligations are gone with them.) The remaining
--  open constructors are isolated as explicit obligation hypotheses, so the
--  proof is `sorry`-free and the open work is visible in the signature.
--  (The `closedFail` refinement is now discharged outright by the rule's `S = ∅`
--  premise via `matchSingleEdge_conforms_closedFail`, so the former `hEdgeFail`
--  obligation is gone. The quantified-path case `hQuantPath` is now discharged
--  too, via `evalQuantified_btconforms` once the evaluator accumulates per-variable
--  group-reference lists.) The plain and strong step obligations are now both
--  proven (`step_conforms` / `step_runtimeWFStrong`), so the former `hStep` is
--  gone. The variable-length-path hygiene side conditions are gone too: the
--  recursion now uses a genuinely fresh edge name (`_rest_` prefixed to the
--  destination variable), so the old `hH4`/`hQuantHygiene` reserved-name
--  assumptions are discharged internally by `rest_ne_dst`/`mid_ne_rest_dst`.
--  The remaining open obligations are:
--    * `hQuantEmpty`      -- a group-quantified edge over an empty-typed atom
--      with a zero-length quantifier (the lifted `closedEmpty`/`closedFail` base);
--    * `hQuantEdgeStrong` -- the graph-aware runtime well-formedness of the records
--      a group-quantified edge produces.
--  `hCat` is the graph-conformance assumption needed by the closed-fail atom
--  vacuity.
-- ============================================================

/-- Plain step soundness (discharges the plain `hStep`). The step record is a
    prefix record merged with a single edge agreeing on shared variables. For the
    productive (`open`/`closed`) refinements every entry is admissible: the three
    endpoint values are node/edge refs at the site (`valueAdmissible` is
    graph-unaware), the rest come from the prefix conformance. The `closedEmpty`
    and `closedFail` refinements bind the endpoints to empty formers, so the step
    must be vacuous; `closedEmpty` follows from the empty atom (prefix or matcher),
    and `closedFail` from the strong prefix well-formedness (the matched source's
    schema lies in the refined set, realizing a compatible triple that contradicts
    the static incompatibility). -/
theorem step_conforms
    (ctx : TypingCtx) (G : PropertyGraph) (Psi : GraphSchemaFull)
    (hPsi : ctx.schemaMap.lookup ctx.graphSite = some Psi)
    (hCat : ∀ Psi', ctx.schemaMap.lookup ctx.graphSite = some Psi' →
              graphConformsSchema G Psi' = true)
    (P : Pattern) (rel : EdgeAtom) (dir : Direction) (n2 : NodeAtom)
    (Gamma1 GammaE GammaN2 GammaRef : RecordSchema) (v1 : Name)
    (hSingle : rel.quantifier = .single)
    (htv : patternTailVar P = some v1)
    (hPrefixConf : BTConforms (evalPattern G ctx.graphSite P) Gamma1)
    (hPrefixStrong : ∀ rho, rho ∈ evalPattern G ctx.graphSite P →
        RuntimeConfigWFStrong G Psi rho Gamma1)
    (hPrefixWF : SchemaWF Gamma1)
    (hAtomE : AtomTyping ctx (.edge { var := rel.var, labels := rel.labels, props := rel.props }) GammaE)
    (hAtomN2 : AtomTyping ctx (.node n2) GammaN2)
    (hRef : RefinementTyping ctx Gamma1 GammaE GammaN2 v1 rel.var n2.var dir GammaRef) :
    BTConforms (evalPattern G ctx.graphSite (.step P rel dir n2)) GammaRef := by
  intro rho_out hmem
  obtain ⟨rho, rhoEdge, hrho, hedge, hStepAgree, ⟨gv, srcN0, hrhov1⟩, rfl⟩ :=
    evalPattern_step_single_mem G ctx.graphSite P rel dir n2 v1 hSingle htv rho_out hmem
  obtain ⟨T2, rfl⟩ := atomTyping_node_singleton hAtomN2
  obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
  have hrelEq : ({ rel with quantifier := .single } : EdgeAtom) = rel := by
    cases rel with | mk v l p q => cases hSingle; rfl
  rw [hrelEq] at hedge
  obtain ⟨srcN, ei, dstN, hsrcN, hei, hdstN, hsrcLbl, hsrcPrp, hlblE, hprpE,
          hlblD, hprpD, hphi, hsd, hform⟩ := matchSingleEdge_mem_form' hedge
  have hv1memE : rhoEdge.mem v1 = true := by rw [hform]; simp [Record.mem]
  have hrhoEdge_v1 : rhoEdge.lookup v1 = Value.nodeRef ctx.graphSite srcN := by
    rw [hform]; simp [Record.lookup, List.find?_cons]
  have hv1memRho : rho.mem v1 = true := by
    cases hm : rho.mem v1 with
    | true => rfl
    | false =>
      exfalso
      have hnone : rho.find? (fun e => e.1 == v1) = none := by
        rw [List.find?_eq_none]; intro y hy hpy
        have hany : rho.any (fun e => e.1 == v1) = true := List.any_eq_true.mpr ⟨y, hy, hpy⟩
        rw [show rho.any (fun e => e.1 == v1) = rho.mem v1 from rfl, hm] at hany
        exact Bool.noConfusion hany
      have hlknull : rho.lookup v1 = Value.null := by
        show (match rho.find? (fun e => e.1 == v1) with | some (_, v) => v | none => Value.null) = Value.null
        rw [hnone]
      rw [hlknull] at hrhov1; exact Value.noConfusion hrhov1
  have hrho_src : rho.lookup v1 = Value.nodeRef ctx.graphSite srcN :=
    (Record.agreeOn_lookup_eq rho rhoEdge v1 hStepAgree hv1memRho hv1memE).trans hrhoEdge_v1
  obtain ⟨hdom_rho, hadm_rho⟩ := hPrefixConf rho hrho
  have hwfGE : SchemaWF (RecordSchema.mk [(rel.var, TE)]) := RecordSchema.singleton_schemaWF _ _
  have hwfGN : SchemaWF (RecordSchema.mk [(n2.var, T2)]) := RecordSchema.singleton_schemaWF _ _
  have hv1G1 : Gamma1.mem v1 = true := by rw [← hdom_rho v1]; exact hv1memRho
  have hGRmem := refinementTyping_mem hRef hv1G1
    (by simp [RecordSchema.mem] : (RecordSchema.mk [(rel.var, TE)]).mem rel.var = true)
    (by simp [RecordSchema.mem] : (RecordSchema.mk [(n2.var, T2)]).mem n2.var = true)
  have hdom_step : ∀ z, (rho.merge rhoEdge).mem z = GammaRef.mem z := by
    intro z
    rw [Record.merge_mem, hdom_rho z, hGRmem z, hform]
    simp only [Record.mem, List.any_cons, List.any_nil, Bool.or_false, singleton_schema_mem]
    cases hvz : v1 == z with
    | true => have h1 : Gamma1.mem z = true := by rw [← eq_of_beq hvz]; exact hv1G1
              simp [h1]
    | false => simp [hvz, Bool.or_assoc]
  cases hRef with
  | open_ hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 =>
    have hTEeq : TE = GSort.edgeOf ctx.graphSite := by
      have h := hEdge2; rw [singleton_schema_lookup] at h; simpa using h
    have hT2eq : T2 = GSort.nodeOf ctx.graphSite := by
      have h := hNode3; rw [singleton_schema_lookup] at h; simpa using h
    subst hTEeq; subst hT2eq
    have d_rv1 : (rel.var == v1) = false :=
      joinCompatible_lookup_distinct hJC12 hNode1 hEdge2 (sortInter_nodeOf_edgeOf_isBot ctx.graphSite)
    have d_n2r : (n2.var == rel.var) = false :=
      joinCompatible_singleton_distinct rel.var n2.var _ _ (sortInter_edgeOf_nodeOf_isBot ctx.graphSite) hJC23
    have hv1rel : (v1 == rel.var) = false := beq_name_symm_false d_rv1
    have hreln2 : (rel.var == n2.var) = false := beq_name_symm_false d_n2r
    have hrelmemE : rhoEdge.mem rel.var = true := by rw [hform]; simp [Record.mem, hv1rel]
    have hn2memE : rhoEdge.mem n2.var = true := by rw [hform]; simp [Record.mem]
    have lookE : (rho.merge rhoEdge).lookup rel.var = Value.edgeRef ctx.graphSite ei := by
      rw [Record.merge_lookup_agree_right rho rhoEdge rel.var hStepAgree hrelmemE, hform]
      simp [Record.lookup, List.find?_cons, hv1rel]
    have lookD : (rho.merge rhoEdge).lookup n2.var = Value.nodeRef ctx.graphSite dstN := by
      rw [Record.merge_lookup_agree_right rho rhoEdge n2.var hStepAgree hn2memE, hform]
      cases hvn : v1 == n2.var with
      | true => simp only [Record.lookup, List.find?_cons, hvn]; rw [hsd hvn]
      | false => simp [Record.lookup, List.find?_cons, hvn, hreln2]
    have hGRrel : ((Gamma1.join (RecordSchema.mk [(rel.var, GSort.edgeOf ctx.graphSite)])).join
          (RecordSchema.mk [(n2.var, GSort.nodeOf ctx.graphSite)])).lookup rel.var
        = (match Gamma1.lookup rel.var with
           | some s => some (RecordSchema.sortInter s (GSort.edgeOf ctx.graphSite))
           | none => some (GSort.edgeOf ctx.graphSite)) := by
      rw [RecordSchema.join_lookup_of_right_none (RecordSchema.join_schemaWF hPrefixWF hwfGE) hwfGN
            (RecordSchema.lookup_eq_none_of_mem_false (by rw [singleton_schema_mem]; exact d_n2r)),
          RecordSchema.join_lookup hPrefixWF hwfGE, singleton_schema_lookup]
      simp only [beq_self_eq_true, if_true]; cases Gamma1.lookup rel.var <;> rfl
    have hGRn2 : ((Gamma1.join (RecordSchema.mk [(rel.var, GSort.edgeOf ctx.graphSite)])).join
          (RecordSchema.mk [(n2.var, GSort.nodeOf ctx.graphSite)])).lookup n2.var
        = (match Gamma1.lookup n2.var with
           | some s => some (RecordSchema.sortInter s (GSort.nodeOf ctx.graphSite))
           | none => some (GSort.nodeOf ctx.graphSite)) := by
      rw [RecordSchema.join_lookup (RecordSchema.join_schemaWF hPrefixWF hwfGE) hwfGN,
          RecordSchema.join_lookup_of_right_none hPrefixWF hwfGE
            (RecordSchema.lookup_eq_none_of_mem_false (by rw [singleton_schema_mem]; exact hreln2)),
          singleton_schema_lookup]
      simp only [beq_self_eq_true, if_true]; cases Gamma1.lookup n2.var <;> rfl
    have hGRother : ∀ x, (x == rel.var) = false → (x == n2.var) = false →
        ((Gamma1.join (RecordSchema.mk [(rel.var, GSort.edgeOf ctx.graphSite)])).join
          (RecordSchema.mk [(n2.var, GSort.nodeOf ctx.graphSite)])).lookup x = Gamma1.lookup x := by
      intro x hxr hxn
      rw [RecordSchema.join_lookup_of_right_none (RecordSchema.join_schemaWF hPrefixWF hwfGE) hwfGN
            (RecordSchema.lookup_eq_none_of_mem_false (by rw [singleton_schema_mem]; exact beq_name_symm_false hxn))]
      exact RecordSchema.join_lookup_of_right_none hPrefixWF hwfGE
        (RecordSchema.lookup_eq_none_of_mem_false (by rw [singleton_schema_mem]; exact beq_name_symm_false hxr))
    refine ⟨hdom_step, ?_⟩
    intro x t hxt
    have hlk : (((Gamma1.join (RecordSchema.mk [(rel.var, GSort.edgeOf ctx.graphSite)])).join
        (RecordSchema.mk [(n2.var, GSort.nodeOf ctx.graphSite)]))).lookup x = some t :=
      (RecordSchema.join_schemaWF (RecordSchema.join_schemaWF hPrefixWF hwfGE) hwfGN) x t hxt
    cases hxr : x == rel.var with
    | true =>
      rw [eq_of_beq hxr, hGRrel] at hlk
      rw [eq_of_beq hxr, lookE]
      cases hg1 : Gamma1.lookup rel.var with
      | none => rw [hg1] at hlk; obtain rfl := Option.some.inj hlk; exact edgeRef_adm_edgeOf ctx.graphSite ei
      | some s =>
        rw [hg1] at hlk; obtain rfl := Option.some.inj hlk
        have hrelrho : rho.mem rel.var = true := by
          rw [hdom_rho rel.var]; exact RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem hg1)
        have hadmS : RecordSchema.valueAdmissible (Value.edgeRef ctx.graphSite ei) s = true := by
          have hl : rho.lookup rel.var = Value.edgeRef ctx.graphSite ei := by
            rw [Record.agreeOn_lookup_eq rho rhoEdge rel.var hStepAgree hrelrho hrelmemE, hform]
            simp [Record.lookup, List.find?_cons, hv1rel]
          rw [← hl]; exact hadm_rho rel.var s (RecordSchema.lookup_some_mem hg1)
        obtain ⟨hbot, _⟩ := RecordSchema.joinCompatible_meet hJC12 hg1 hEdge2
        have hs : s.isEmptyFormer = false := by
          cases hc : s.isEmptyFormer with
          | false => rfl
          | true =>
            rw [adm_emptyFormer_false (Value.edgeRef ctx.graphSite ei) s hc] at hadmS
            exact Bool.noConfusion hadmS
        exact sortInter_meet_admissible _ _ _ hbot
          (sortInter_edgeOf_not_emptyFormer hs) hadmS (edgeRef_adm_edgeOf ctx.graphSite ei)
    | false =>
      cases hxn : x == n2.var with
      | true =>
        rw [eq_of_beq hxn, hGRn2] at hlk
        rw [eq_of_beq hxn, lookD]
        cases hg1 : Gamma1.lookup n2.var with
        | none => rw [hg1] at hlk; obtain rfl := Option.some.inj hlk; exact nodeRef_adm_nodeOf ctx.graphSite dstN
        | some s =>
          rw [hg1] at hlk; obtain rfl := Option.some.inj hlk
          have hn2rho : rho.mem n2.var = true := by
            rw [hdom_rho n2.var]; exact RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem hg1)
          have hadmS : RecordSchema.valueAdmissible (Value.nodeRef ctx.graphSite dstN) s = true := by
            have hl : rho.lookup n2.var = Value.nodeRef ctx.graphSite dstN := by
              rw [Record.agreeOn_lookup_eq rho rhoEdge n2.var hStepAgree hn2rho hn2memE, hform]
              cases hvn : v1 == n2.var with
              | true => simp only [Record.lookup, List.find?_cons, hvn]; rw [hsd hvn]
              | false => simp [Record.lookup, List.find?_cons, hvn, hreln2]
            rw [← hl]; exact hadm_rho n2.var s (RecordSchema.lookup_some_mem hg1)
          obtain ⟨hbot, _⟩ := RecordSchema.joinCompatible_meet hJC13 hg1 hNode3
          have hs : s.isEmptyFormer = false := by
            cases hc : s.isEmptyFormer with
            | false => rfl
            | true =>
              rw [adm_emptyFormer_false (Value.nodeRef ctx.graphSite dstN) s hc] at hadmS
              exact Bool.noConfusion hadmS
          exact sortInter_meet_admissible _ _ _ hbot
            (sortInter_nodeOf_not_emptyFormer hs) hadmS (nodeRef_adm_nodeOf ctx.graphSite dstN)
      | false =>
        rw [hGRother x hxr hxn] at hlk
        rw [Record.merge_lookup_left _ _ _ (by rw [hdom_rho x]; exact RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem hlk))]
        exact hadm_rho x t (RecordSchema.lookup_some_mem hlk)
  | closed sN1 sE2 sN3 sN1' sE2' sN3' hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13
      hSrc' hEdge' hDst' hNonEmpty =>
    have hTEeq : TE = GSort.edgeRefinedOf ctx.graphSite sE2 := by
      have h := hEdge2; rw [singleton_schema_lookup] at h; simpa using h
    have hT2eq : T2 = GSort.nodeRefinedOf ctx.graphSite sN3 := by
      have h := hNode3; rw [singleton_schema_lookup] at h; simpa using h
    subst hTEeq; subst hT2eq
    have d_rv1 : (rel.var == v1) = false :=
      joinCompatible_lookup_distinct hJC12 hNode1 hEdge2
        (sortInter_nodeRefinedOf_edgeRefinedOf_isBot ctx.graphSite sN1 sE2)
    have d_n2r : (n2.var == rel.var) = false :=
      joinCompatible_singleton_distinct rel.var n2.var _ _
        (sortInter_edgeRefinedOf_nodeRefinedOf_isBot ctx.graphSite sE2 sN3) hJC23
    have hv1rel : (v1 == rel.var) = false := beq_name_symm_false d_rv1
    have hreln2 : (rel.var == n2.var) = false := beq_name_symm_false d_n2r
    have hrelmemE : rhoEdge.mem rel.var = true := by rw [hform]; simp [Record.mem, hv1rel]
    have hn2memE : rhoEdge.mem n2.var = true := by rw [hform]; simp [Record.mem]
    have lookE : (rho.merge rhoEdge).lookup rel.var = Value.edgeRef ctx.graphSite ei := by
      rw [Record.merge_lookup_agree_right rho rhoEdge rel.var hStepAgree hrelmemE, hform]
      simp [Record.lookup, List.find?_cons, hv1rel]
    have lookD : (rho.merge rhoEdge).lookup n2.var = Value.nodeRef ctx.graphSite dstN := by
      rw [Record.merge_lookup_agree_right rho rhoEdge n2.var hStepAgree hn2memE, hform]
      cases hvn : v1 == n2.var with
      | true => simp only [Record.lookup, List.find?_cons, hvn]; rw [hsd hvn]
      | false => simp [Record.lookup, List.find?_cons, hvn, hreln2]
    have lookS : (rho.merge rhoEdge).lookup v1 = Value.nodeRef ctx.graphSite srcN := by
      rw [Record.merge_lookup_left rho rhoEdge v1 hv1memRho, hrho_src]
    have hwfRef : SchemaWF (((Gamma1.join (RecordSchema.mk [(rel.var, GSort.edgeRefinedOf ctx.graphSite sE2)])).join
        (RecordSchema.mk [(n2.var, GSort.nodeRefinedOf ctx.graphSite sN3)])).setMany
        [(v1, GSort.nodeRefinedOf ctx.graphSite sN1'),
         (rel.var, GSort.edgeRefinedOf ctx.graphSite sE2'),
         (n2.var, GSort.nodeRefinedOf ctx.graphSite sN3')]) :=
      RecordSchema.setMany_schemaWF _ (RecordSchema.join_schemaWF (RecordSchema.join_schemaWF hPrefixWF hwfGE) hwfGN)
    refine ⟨hdom_step, ?_⟩
    intro x t hxt
    have hlk := hwfRef x t hxt
    cases hxr : x == rel.var with
    | true =>
      rw [eq_of_beq hxr, RecordSchema.setMany3_lookup_snd _ v1 rel.var n2.var _ _ _ d_n2r] at hlk
      obtain rfl := Option.some.inj hlk
      rw [eq_of_beq hxr, lookE]; exact edgeRef_adm_edgeRefinedOf ctx.graphSite ei sE2'
    | false =>
      cases hxn : x == n2.var with
      | true =>
        rw [eq_of_beq hxn, RecordSchema.setMany3_lookup_thd _ v1 rel.var n2.var _ _ _] at hlk
        obtain rfl := Option.some.inj hlk
        rw [eq_of_beq hxn, lookD]; exact nodeRef_adm_nodeRefinedOf ctx.graphSite dstN sN3'
      | false =>
        cases hxv : x == v1 with
        | true =>
          have d_n2v1 : (n2.var == v1) = false := by
            have h := hxn; rw [eq_of_beq hxv] at h; exact beq_name_symm_false h
          rw [eq_of_beq hxv, RecordSchema.setMany3_lookup_fst _ v1 rel.var n2.var _ _ _ d_rv1 d_n2v1] at hlk
          obtain rfl := Option.some.inj hlk
          rw [eq_of_beq hxv, lookS]; exact nodeRef_adm_nodeRefinedOf ctx.graphSite srcN sN1'
        | false =>
          rw [RecordSchema.setMany3_lookup_other _ v1 rel.var n2.var _ _ _ x
                (beq_name_symm_false hxv) (beq_name_symm_false hxr) (beq_name_symm_false hxn),
              RecordSchema.join_lookup_of_right_none (RecordSchema.join_schemaWF hPrefixWF hwfGE) hwfGN
                (RecordSchema.lookup_eq_none_of_mem_false
                  (by rw [singleton_schema_mem]; exact beq_name_symm_false hxn)),
              RecordSchema.join_lookup_of_right_none hPrefixWF hwfGE
                (RecordSchema.lookup_eq_none_of_mem_false
                  (by rw [singleton_schema_mem]; exact beq_name_symm_false hxr))] at hlk
          rw [Record.merge_lookup_left _ _ _ (by rw [hdom_rho x]; exact RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem hlk))]
          exact hadm_rho x t (RecordSchema.lookup_some_mem hlk)
  | closedEmpty hJC12 hJC23 hJC13 hSomeEmpty =>
    exfalso
    rcases hSomeEmpty with h | h | h
    · cases hg1 : Gamma1.lookup v1 with
      | none => rw [hg1] at h; exact Bool.noConfusion h
      | some te =>
        rw [hg1] at h
        have hadm := hadm_rho v1 te (RecordSchema.lookup_some_mem hg1)
        have hfalse : RecordSchema.valueAdmissible (rho.lookup v1) te = false := by
          cases hsh : te.shape with
          | emptyFormer a b => simp [RecordSchema.valueAdmissible, hsh]
          | _ => simp [GSort.isEmptyFormer, hsh] at h
        rw [hfalse] at hadm; exact Bool.noConfusion hadm
    · cases hAtomE with
      | edgeOpen r labels props hOpen =>
          simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.edgeOf] at h
      | edgeClosed r labels props Psi' PhiPi xiL xiPrp xiResult hClosed hSchema hPrpTyping hLblFilter hPrpFilter hResult hNE =>
          simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.edgeRefinedOf] at h
      | edgeClosedFail r labels props Psi' PhiPi xiL xiPrp hClosed hSchema hPrpTyping hLblFilter hPrpFilter hEmpty =>
          exact not_mem_matchSingleEdge_of_edge_filter_empty G Psi' ctx.graphSite { var := v1 } rel n2 dir
            PhiPi xiL (hCat Psi' hSchema) hPrpTyping hLblFilter (hPrpFilter ▸ hEmpty) rhoEdge hedge
    · cases hAtomN2 with
      | nodeOpen v labels props hOpen =>
          simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.nodeOf] at h
      | nodeClosed v labels props Psi' PhiPi zetaL zetaPrp zetaResult hClosed hSchema hPrpTyping hLblFilter hPrpFilter hResult hNE =>
          simp [singleton_schema_lookup, GSort.isEmptyFormer, GSort.nodeRefinedOf] at h
      | nodeClosedFail v labels props Psi' PhiPi zetaL zetaPrp hClosed hSchema hPrpTyping hLblFilter hPrpFilter hEmpty =>
          exact not_mem_matchSingleEdge_of_dst_filter_empty G Psi' ctx.graphSite { var := v1 } rel _ dir
            PhiPi zetaL (hCat Psi' hSchema) hPrpTyping hLblFilter (hPrpFilter ▸ hEmpty) rhoEdge hedge
  | closedFail sN1 sE2 sN3 hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 hFail =>
    exfalso
    have hTEeq : TE = GSort.edgeRefinedOf ctx.graphSite sE2 := by
      have h := hEdge2; rw [singleton_schema_lookup] at h; simpa using h
    have hT2eq : T2 = GSort.nodeRefinedOf ctx.graphSite sN3 := by
      have h := hNode3; rw [singleton_schema_lookup] at h; simpa using h
    subst hTEeq; subst hT2eq
    obtain ⟨Psi2, PhiPiE, hSchema2, hPrpE2, hsE2eq⟩ := atomTyping_edge_refined_inv hAtomE hEdge2
    obtain ⟨Psi3, PhiPi3, hSchema3, hPrp3, hsN3eq⟩ := atomTyping_node_refined_inv hAtomN2 hNode3
    rw [Option.some.inj (hSchema2.symm.trans hPsi)] at hsE2eq
    rw [Option.some.inj (hSchema3.symm.trans hPsi)] at hsN3eq
    have hGconf := hCat Psi hPsi
    obtain ⟨nsS, hnsS_Psi, hnsSconf⟩ := graphConformsSchema_node hGconf srcN hsrcN
    obtain ⟨es2, hes2_Psi, hes2conf⟩ := graphConformsSchema_edge hGconf ei hei
    obtain ⟨nsD, hnsD_Psi, hnsDconf⟩ := graphConformsSchema_node hGconf dstN hdstN
    have hpre := hPrefixStrong rho hrho
    have hnsS_sN1 : nsS ∈ sN1 :=
      (hpre v1 (GSort.nodeRefinedOf ctx.graphSite sN1) hNode1).1 ctx.graphSite sN1 rfl
        ctx.graphSite srcN hsrcN hrho_src nsS hnsS_Psi hnsSconf
    have hes2_sE2 : es2 ∈ sE2 := by
      rw [hsE2eq]
      exact filterEdgeSchemasByPropCompat_mem_of_conforms G ctx.graphSite ⟨ei, hei⟩ es2 _ rel.props PhiPiE
        (resolveEdgeSchemas_mem_of_conforms G Psi ⟨ei, hei⟩ es2 rel.labels hes2_Psi hes2conf hlblE)
        hes2conf hPrpE2 hprpE
    have hnsD_sN3 : nsD ∈ sN3 := by
      rw [hsN3eq]
      exact filterNodeSchemasByPropCompat_mem_of_conforms G ctx.graphSite ⟨dstN, hdstN⟩ nsD _ n2.props PhiPi3
        (resolveNodeSchemas_mem_of_conforms G Psi ⟨dstN, hdstN⟩ nsD n2.labels hnsD_Psi hnsDconf hlblD)
        hnsDconf hPrp3 hprpD
    have hgoal := matched_triple_endpointCompat G srcN ei dstN hsrcN hei hdstN dir sN1 sE2 sN3 nsS nsD es2
      hnsS_sN1 hes2_sE2 hnsD_sN3 hnsSconf hes2conf hnsDconf hphi
    rw [hFail] at hgoal; exact Bool.noConfusion hgoal

/-- Open-graph variant of `step_conforms` (Pat-Step case at an OPEN site).
    With no schema at the site there is nothing to conform to beyond the
    graph-indexed identity types, so the schema witness (`Psi`, `hPsi`) and
    the strong runtime invariant (`hPrefixStrong`) both disappear from the
    premises. The closed refinement cases are refuted: their atom typings
    demand a closed site (`hClosed` contradicts `hOpen`) or a refined/empty
    sort an open atom rule cannot produce; `closedEmpty`'s remaining
    disjunct (an empty-former binding in the prefix schema) contradicts the
    prefix conformance, since the tail variable holds a node reference and
    no value inhabits an empty former. The `open_` case never consults the
    schema. -/
theorem step_conforms_open
    (ctx : TypingCtx) (G : PropertyGraph)
    (hOpen : ctx.schemaMap.isClosed ctx.graphSite = false)
    (P : Pattern) (rel : EdgeAtom) (dir : Direction) (n2 : NodeAtom)
    (Gamma1 GammaE GammaN2 GammaRef : RecordSchema) (v1 : Name)
    (hSingle : rel.quantifier = .single)
    (htv : patternTailVar P = some v1)
    (hPrefixConf : BTConforms (evalPattern G ctx.graphSite P) Gamma1)
    (hPrefixWF : SchemaWF Gamma1)
    (hAtomE : AtomTyping ctx (.edge { var := rel.var, labels := rel.labels, props := rel.props }) GammaE)
    (hAtomN2 : AtomTyping ctx (.node n2) GammaN2)
    (hRef : RefinementTyping ctx Gamma1 GammaE GammaN2 v1 rel.var n2.var dir GammaRef) :
    BTConforms (evalPattern G ctx.graphSite (.step P rel dir n2)) GammaRef := by
  intro rho_out hmem
  obtain ⟨rho, rhoEdge, hrho, hedge, hStepAgree, ⟨gv, srcN0, hrhov1⟩, rfl⟩ :=
    evalPattern_step_single_mem G ctx.graphSite P rel dir n2 v1 hSingle htv rho_out hmem
  obtain ⟨T2, rfl⟩ := atomTyping_node_singleton hAtomN2
  obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
  have hrelEq : ({ rel with quantifier := .single } : EdgeAtom) = rel := by
    cases rel with | mk v l p q => cases hSingle; rfl
  rw [hrelEq] at hedge
  obtain ⟨srcN, ei, dstN, hsrcN, hei, hdstN, hsrcLbl, hsrcPrp, hlblE, hprpE,
          hlblD, hprpD, hphi, hsd, hform⟩ := matchSingleEdge_mem_form' hedge
  have hv1memE : rhoEdge.mem v1 = true := by rw [hform]; simp [Record.mem]
  have hrhoEdge_v1 : rhoEdge.lookup v1 = Value.nodeRef ctx.graphSite srcN := by
    rw [hform]; simp [Record.lookup, List.find?_cons]
  have hv1memRho : rho.mem v1 = true := by
    cases hm : rho.mem v1 with
    | true => rfl
    | false =>
      exfalso
      have hnone : rho.find? (fun e => e.1 == v1) = none := by
        rw [List.find?_eq_none]; intro y hy hpy
        have hany : rho.any (fun e => e.1 == v1) = true := List.any_eq_true.mpr ⟨y, hy, hpy⟩
        rw [show rho.any (fun e => e.1 == v1) = rho.mem v1 from rfl, hm] at hany
        exact Bool.noConfusion hany
      have hlknull : rho.lookup v1 = Value.null := by
        show (match rho.find? (fun e => e.1 == v1) with | some (_, v) => v | none => Value.null) = Value.null
        rw [hnone]
      rw [hlknull] at hrhov1; exact Value.noConfusion hrhov1
  have hrho_src : rho.lookup v1 = Value.nodeRef ctx.graphSite srcN :=
    (Record.agreeOn_lookup_eq rho rhoEdge v1 hStepAgree hv1memRho hv1memE).trans hrhoEdge_v1
  obtain ⟨hdom_rho, hadm_rho⟩ := hPrefixConf rho hrho
  have hwfGE : SchemaWF (RecordSchema.mk [(rel.var, TE)]) := RecordSchema.singleton_schemaWF _ _
  have hwfGN : SchemaWF (RecordSchema.mk [(n2.var, T2)]) := RecordSchema.singleton_schemaWF _ _
  have hv1G1 : Gamma1.mem v1 = true := by rw [← hdom_rho v1]; exact hv1memRho
  have hGRmem := refinementTyping_mem hRef hv1G1
    (by simp [RecordSchema.mem] : (RecordSchema.mk [(rel.var, TE)]).mem rel.var = true)
    (by simp [RecordSchema.mem] : (RecordSchema.mk [(n2.var, T2)]).mem n2.var = true)
  have hdom_step : ∀ z, (rho.merge rhoEdge).mem z = GammaRef.mem z := by
    intro z
    rw [Record.merge_mem, hdom_rho z, hGRmem z, hform]
    simp only [Record.mem, List.any_cons, List.any_nil, Bool.or_false, singleton_schema_mem]
    cases hvz : v1 == z with
    | true => have h1 : Gamma1.mem z = true := by rw [← eq_of_beq hvz]; exact hv1G1
              simp [h1]
    | false => simp [hvz, Bool.or_assoc]
  cases hRef with
  | open_ hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 =>
    have hTEeq : TE = GSort.edgeOf ctx.graphSite := by
      have h := hEdge2; rw [singleton_schema_lookup] at h; simpa using h
    have hT2eq : T2 = GSort.nodeOf ctx.graphSite := by
      have h := hNode3; rw [singleton_schema_lookup] at h; simpa using h
    subst hTEeq; subst hT2eq
    have d_rv1 : (rel.var == v1) = false :=
      joinCompatible_lookup_distinct hJC12 hNode1 hEdge2 (sortInter_nodeOf_edgeOf_isBot ctx.graphSite)
    have d_n2r : (n2.var == rel.var) = false :=
      joinCompatible_singleton_distinct rel.var n2.var _ _ (sortInter_edgeOf_nodeOf_isBot ctx.graphSite) hJC23
    have hv1rel : (v1 == rel.var) = false := beq_name_symm_false d_rv1
    have hreln2 : (rel.var == n2.var) = false := beq_name_symm_false d_n2r
    have hrelmemE : rhoEdge.mem rel.var = true := by rw [hform]; simp [Record.mem, hv1rel]
    have hn2memE : rhoEdge.mem n2.var = true := by rw [hform]; simp [Record.mem]
    have lookE : (rho.merge rhoEdge).lookup rel.var = Value.edgeRef ctx.graphSite ei := by
      rw [Record.merge_lookup_agree_right rho rhoEdge rel.var hStepAgree hrelmemE, hform]
      simp [Record.lookup, List.find?_cons, hv1rel]
    have lookD : (rho.merge rhoEdge).lookup n2.var = Value.nodeRef ctx.graphSite dstN := by
      rw [Record.merge_lookup_agree_right rho rhoEdge n2.var hStepAgree hn2memE, hform]
      cases hvn : v1 == n2.var with
      | true => simp only [Record.lookup, List.find?_cons, hvn]; rw [hsd hvn]
      | false => simp [Record.lookup, List.find?_cons, hvn, hreln2]
    have hGRrel : ((Gamma1.join (RecordSchema.mk [(rel.var, GSort.edgeOf ctx.graphSite)])).join
          (RecordSchema.mk [(n2.var, GSort.nodeOf ctx.graphSite)])).lookup rel.var
        = (match Gamma1.lookup rel.var with
           | some s => some (RecordSchema.sortInter s (GSort.edgeOf ctx.graphSite))
           | none => some (GSort.edgeOf ctx.graphSite)) := by
      rw [RecordSchema.join_lookup_of_right_none (RecordSchema.join_schemaWF hPrefixWF hwfGE) hwfGN
            (RecordSchema.lookup_eq_none_of_mem_false (by rw [singleton_schema_mem]; exact d_n2r)),
          RecordSchema.join_lookup hPrefixWF hwfGE, singleton_schema_lookup]
      simp only [beq_self_eq_true, if_true]; cases Gamma1.lookup rel.var <;> rfl
    have hGRn2 : ((Gamma1.join (RecordSchema.mk [(rel.var, GSort.edgeOf ctx.graphSite)])).join
          (RecordSchema.mk [(n2.var, GSort.nodeOf ctx.graphSite)])).lookup n2.var
        = (match Gamma1.lookup n2.var with
           | some s => some (RecordSchema.sortInter s (GSort.nodeOf ctx.graphSite))
           | none => some (GSort.nodeOf ctx.graphSite)) := by
      rw [RecordSchema.join_lookup (RecordSchema.join_schemaWF hPrefixWF hwfGE) hwfGN,
          RecordSchema.join_lookup_of_right_none hPrefixWF hwfGE
            (RecordSchema.lookup_eq_none_of_mem_false (by rw [singleton_schema_mem]; exact hreln2)),
          singleton_schema_lookup]
      simp only [beq_self_eq_true, if_true]; cases Gamma1.lookup n2.var <;> rfl
    have hGRother : ∀ x, (x == rel.var) = false → (x == n2.var) = false →
        ((Gamma1.join (RecordSchema.mk [(rel.var, GSort.edgeOf ctx.graphSite)])).join
          (RecordSchema.mk [(n2.var, GSort.nodeOf ctx.graphSite)])).lookup x = Gamma1.lookup x := by
      intro x hxr hxn
      rw [RecordSchema.join_lookup_of_right_none (RecordSchema.join_schemaWF hPrefixWF hwfGE) hwfGN
            (RecordSchema.lookup_eq_none_of_mem_false (by rw [singleton_schema_mem]; exact beq_name_symm_false hxn))]
      exact RecordSchema.join_lookup_of_right_none hPrefixWF hwfGE
        (RecordSchema.lookup_eq_none_of_mem_false (by rw [singleton_schema_mem]; exact beq_name_symm_false hxr))
    refine ⟨hdom_step, ?_⟩
    intro x t hxt
    have hlk : (((Gamma1.join (RecordSchema.mk [(rel.var, GSort.edgeOf ctx.graphSite)])).join
        (RecordSchema.mk [(n2.var, GSort.nodeOf ctx.graphSite)]))).lookup x = some t :=
      (RecordSchema.join_schemaWF (RecordSchema.join_schemaWF hPrefixWF hwfGE) hwfGN) x t hxt
    cases hxr : x == rel.var with
    | true =>
      rw [eq_of_beq hxr, hGRrel] at hlk
      rw [eq_of_beq hxr, lookE]
      cases hg1 : Gamma1.lookup rel.var with
      | none => rw [hg1] at hlk; obtain rfl := Option.some.inj hlk; exact edgeRef_adm_edgeOf ctx.graphSite ei
      | some s =>
        rw [hg1] at hlk; obtain rfl := Option.some.inj hlk
        have hrelrho : rho.mem rel.var = true := by
          rw [hdom_rho rel.var]; exact RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem hg1)
        have hadmS : RecordSchema.valueAdmissible (Value.edgeRef ctx.graphSite ei) s = true := by
          have hl : rho.lookup rel.var = Value.edgeRef ctx.graphSite ei := by
            rw [Record.agreeOn_lookup_eq rho rhoEdge rel.var hStepAgree hrelrho hrelmemE, hform]
            simp [Record.lookup, List.find?_cons, hv1rel]
          rw [← hl]; exact hadm_rho rel.var s (RecordSchema.lookup_some_mem hg1)
        obtain ⟨hbot, _⟩ := RecordSchema.joinCompatible_meet hJC12 hg1 hEdge2
        have hs : s.isEmptyFormer = false := by
          cases hc : s.isEmptyFormer with
          | false => rfl
          | true =>
            rw [adm_emptyFormer_false (Value.edgeRef ctx.graphSite ei) s hc] at hadmS
            exact Bool.noConfusion hadmS
        exact sortInter_meet_admissible _ _ _ hbot
          (sortInter_edgeOf_not_emptyFormer hs) hadmS (edgeRef_adm_edgeOf ctx.graphSite ei)
    | false =>
      cases hxn : x == n2.var with
      | true =>
        rw [eq_of_beq hxn, hGRn2] at hlk
        rw [eq_of_beq hxn, lookD]
        cases hg1 : Gamma1.lookup n2.var with
        | none => rw [hg1] at hlk; obtain rfl := Option.some.inj hlk; exact nodeRef_adm_nodeOf ctx.graphSite dstN
        | some s =>
          rw [hg1] at hlk; obtain rfl := Option.some.inj hlk
          have hn2rho : rho.mem n2.var = true := by
            rw [hdom_rho n2.var]; exact RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem hg1)
          have hadmS : RecordSchema.valueAdmissible (Value.nodeRef ctx.graphSite dstN) s = true := by
            have hl : rho.lookup n2.var = Value.nodeRef ctx.graphSite dstN := by
              rw [Record.agreeOn_lookup_eq rho rhoEdge n2.var hStepAgree hn2rho hn2memE, hform]
              cases hvn : v1 == n2.var with
              | true => simp only [Record.lookup, List.find?_cons, hvn]; rw [hsd hvn]
              | false => simp [Record.lookup, List.find?_cons, hvn, hreln2]
            rw [← hl]; exact hadm_rho n2.var s (RecordSchema.lookup_some_mem hg1)
          obtain ⟨hbot, _⟩ := RecordSchema.joinCompatible_meet hJC13 hg1 hNode3
          have hs : s.isEmptyFormer = false := by
            cases hc : s.isEmptyFormer with
            | false => rfl
            | true =>
              rw [adm_emptyFormer_false (Value.nodeRef ctx.graphSite dstN) s hc] at hadmS
              exact Bool.noConfusion hadmS
          exact sortInter_meet_admissible _ _ _ hbot
            (sortInter_nodeOf_not_emptyFormer hs) hadmS (nodeRef_adm_nodeOf ctx.graphSite dstN)
      | false =>
        rw [hGRother x hxr hxn] at hlk
        rw [Record.merge_lookup_left _ _ _ (by rw [hdom_rho x]; exact RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem hlk))]
        exact hadm_rho x t (RecordSchema.lookup_some_mem hlk)
  | closed sN1 sE2 sN3 sN1' sE2' sN3' hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13
      hSrc' hEdge' hDst' hNonEmpty =>
    exfalso
    have hTEeq : TE = GSort.edgeRefinedOf ctx.graphSite sE2 := by
      have h := hEdge2; rw [singleton_schema_lookup] at h; simpa using h
    subst hTEeq
    cases hAtomE with
    | edgeClosed _ _ _ _ _ _ _ _ hClosed _ _ _ _ _ _ =>
      rw [hOpen] at hClosed; exact Bool.noConfusion hClosed
  | closedEmpty hJC12 hJC23 hJC13 hSomeEmpty =>
    exfalso
    rcases hSomeEmpty with h1 | h2 | h3
    · cases hg : Gamma1.lookup v1 with
      | none => rw [hg] at h1; exact Bool.noConfusion h1
      | some t =>
        rw [hg] at h1
        have hadm := hadm_rho v1 t (RecordSchema.lookup_some_mem hg)
        rw [hrho_src, adm_emptyFormer_false _ _ h1] at hadm
        exact Bool.noConfusion hadm
    · rw [singleton_schema_lookup] at h2
      simp only [beq_self_eq_true, if_true] at h2
      cases hAtomE with
      | edgeOpen _ _ _ _ => exact Bool.noConfusion h2
      | edgeClosed _ _ _ _ _ _ _ _ hClosed _ _ _ _ _ _ =>
        rw [hOpen] at hClosed; exact Bool.noConfusion hClosed
      | edgeClosedFail _ _ _ _ _ _ _ hClosed _ _ _ _ =>
        rw [hOpen] at hClosed; exact Bool.noConfusion hClosed
    · rw [singleton_schema_lookup] at h3
      simp only [beq_self_eq_true, if_true] at h3
      cases hAtomN2 with
      | nodeOpen _ _ _ _ => exact Bool.noConfusion h3
      | nodeClosed _ _ _ _ _ _ _ _ hClosed _ _ _ _ _ _ =>
        rw [hOpen] at hClosed; exact Bool.noConfusion hClosed
      | nodeClosedFail _ _ _ _ _ _ _ hClosed _ _ _ _ =>
        rw [hOpen] at hClosed; exact Bool.noConfusion hClosed
  | closedFail sN1 sE2 sN3 hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 hFail =>
    exfalso
    have hTEeq : TE = GSort.edgeRefinedOf ctx.graphSite sE2 := by
      have h := hEdge2; rw [singleton_schema_lookup] at h; simpa using h
    subst hTEeq
    cases hAtomE with
    | edgeClosed _ _ _ _ _ _ _ _ hClosed _ _ _ _ _ _ =>
      rw [hOpen] at hClosed; exact Bool.noConfusion hClosed

theorem patternTyping_sound
    (ctx : TypingCtx) (G : PropertyGraph)
    (hCat : ∀ Psi', ctx.schemaMap.lookup ctx.graphSite = some Psi' →
              graphConformsSchema G Psi' = true)
    (Psi : GraphSchemaFull) (hPsi : ctx.schemaMap.lookup ctx.graphSite = some Psi)
    (hStrongFn : ∀ (qd' : QuantDepth) (P' : Pattern) (Gamma' : RecordSchema) (v' : Name),
        PatternTyping ctx qd' P' Gamma' v' →
        ∀ rho, rho ∈ evalPattern G ctx.graphSite P' → RuntimeConfigWFStrong G Psi rho Gamma') :
    ∀ (qd : QuantDepth) (P : Pattern) (Gamma : RecordSchema) (v : Name),
      PatternTyping ctx qd P Gamma v →
      BTConforms (evalPattern G ctx.graphSite P) Gamma := by
  intro qd P Gamma v h
  induction h with
  | patNode qd na GammaA hAtom =>
      exact patternSound_node ctx G na GammaA hAtom hCat
  | patEdge qd n1 n2 rel dir GammaN1 GammaE GammaN2 GammaRef hSingleD hAtomN1 hAtomE hAtomN2 hRef =>
      exact patternSound_edge_single ctx G n1 n2 rel dir GammaN1 GammaE GammaN2 GammaRef
        hSingleD hAtomN1 hAtomE hAtomN2 hRef hCat
  | patStep qd P rel dir n2 Gamma1 GammaE GammaN2 GammaRef v1 hSingle hPrefix hAtomE hAtomN2 hRef ihPrefix =>
      exact step_conforms ctx G Psi hPsi hCat P rel dir n2 Gamma1 GammaE GammaN2 GammaRef v1
        hSingle (patternTyping_tailVar hPrefix) ihPrefix
        (hStrongFn qd P Gamma1 v1 hPrefix)
        (patternTyping_schemaWF hPrefix)
        hAtomE hAtomN2 hRef
  | patQuantEdge n1 n2 rel dir K GammaE hQuant hAtomE hNE12 hNE23 =>
      obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
      exact evalPattern_quantEdge_conforms_edgeSort G ctx.graphSite n1 n2
        { rel with quantifier := K } dir TE hQuant hNE12 hNE23
  | patOptEdge n1 n2 rel dir hNE12 hNE23 =>
      exact evalPattern_optEdge_conforms_open G ctx.graphSite n1 n2 rel dir hNE12 hNE23
  | patQuantPath P K GammaInner v hInner hQuant ihInner =>
      obtain ⟨lv, hlv⟩ := patternLeadVar_isSome P
      obtain ⟨tv, htv⟩ := patternTailVar_isSome P
      have hvars := patternTyping_vars_mem hInner
      have hinner : ∀ z, GammaInner.dom.any (fun w => w == z)
          = (patternVars P).any (fun w => w == z) := by
        intro z
        rw [hvars z]
        exact RecordSchema.dom_any_mem GammaInner z
      show BTConforms (evalPattern G ctx.graphSite (.quantified P K))
        (GammaInner.liftToGroupRef GammaInner.dom)
      simp only [evalPattern, hlv, htv]
      exact evalQuantified_btconforms (patternVars P) (evalPattern G ctx.graphSite P) lv tv K.lo _
        GammaInner GammaInner.dom hvars hinner
  | patGrouped qd P Gamma v hP ih =>
      rw [evalPattern_grouped]
      exact ih

-- ============================================================
--  Schema `nodeEdgeNullable` invariant: every node/edge-single entry of a typed
--  schema is nullable (so it is the canonical `nodeRefinedOf`/`edgeRefinedOf`).
--  Fed to the closed empty-former-meet vacuity via `componentType_eq_*`.
-- ============================================================

def SchemaNodeEdgeNullable (Gamma : RecordSchema) : Prop :=
  ∀ x t, (x, t) ∈ Gamma.entries → t.nodeEdgeNullable

theorem schemaNEN_empty : SchemaNodeEdgeNullable RecordSchema.empty := by
  intro x t h; simp [RecordSchema.empty] at h

/-- At an empty-former meet whose operands both admit a value (hence neither is
    itself an empty former), the operands are both node-refined or both
    edge-refined single sorts. The only `sortInter` branches producing an empty
    former from non-empty-former operands are the two same-kind refined ones. -/
theorem sortInter_emptyFormer_adm_classify {v : Value} {t1 t2 : GSort}
    (hemp : (RecordSchema.sortInter t1 t2).isEmptyFormer = true)
    (ha1 : RecordSchema.valueAdmissible v t1 = true)
    (ha2 : RecordSchema.valueAdmissible v t2 = true) :
    (∃ G ss1 ss2, t1.shape = .single (.nodeRefined G ss1) ∧ t2.shape = .single (.nodeRefined G ss2)) ∨
    (∃ G ss1 ss2, t1.shape = .single (.edgeRefined G ss1) ∧ t2.shape = .single (.edgeRefined G ss2)) := by
  have ht1ne : t1.isEmptyFormer = false := by
    cases hc : t1.isEmptyFormer with
    | false => rfl
    | true => rw [adm_emptyFormer_false v t1 hc] at ha1; exact Bool.noConfusion ha1
  have ht2ne : t2.isEmptyFormer = false := by
    cases hc : t2.isEmptyFormer with
    | false => rfl
    | true => rw [adm_emptyFormer_false v t2 hc] at ha2; exact Bool.noConfusion ha2
  obtain ⟨sh1, nl1⟩ := t1; obtain ⟨sh2, nl2⟩ := t2
  simp only [GSort.isEmptyFormer] at ht1ne ht2ne
  cases sh1
  case single es1 =>
    cases es1
    case nodeRefined G1 ssa =>
      cases sh2
      case single es2 =>
        cases es2
        case nodeRefined G2 ssb =>
          by_cases hGG : (G1 == G2) = true
          · have hGe : G1 = G2 := eq_of_beq hGG; subst hGe
            exact Or.inl ⟨G1, ssa, ssb, rfl, rfl⟩
          · exfalso; simp only [RecordSchema.sortInter] at hemp
            (repeat' split at hemp) <;>
              simp_all [GSort.isEmptyFormer, GSort.botSort, GSort.nodeEmpty, GSort.edgeEmpty,
                beq_self_eq_true]
        all_goals
          (exfalso; simp only [RecordSchema.sortInter] at hemp
           (repeat' split at hemp) <;>
             simp_all [GSort.isEmptyFormer, GSort.botSort, GSort.nodeEmpty, GSort.edgeEmpty,
               beq_self_eq_true])
      all_goals
        (exfalso; simp only [RecordSchema.sortInter] at hemp
         (repeat' split at hemp) <;>
           simp_all [GSort.isEmptyFormer, GSort.botSort, GSort.nodeEmpty, GSort.edgeEmpty,
             beq_self_eq_true])
    case edgeRefined G1 ssa =>
      cases sh2
      case single es2 =>
        cases es2
        case edgeRefined G2 ssb =>
          by_cases hGG : (G1 == G2) = true
          · have hGe : G1 = G2 := eq_of_beq hGG; subst hGe
            exact Or.inr ⟨G1, ssa, ssb, rfl, rfl⟩
          · exfalso; simp only [RecordSchema.sortInter] at hemp
            (repeat' split at hemp) <;>
              simp_all [GSort.isEmptyFormer, GSort.botSort, GSort.nodeEmpty, GSort.edgeEmpty,
                beq_self_eq_true]
        all_goals
          (exfalso; simp only [RecordSchema.sortInter] at hemp
           (repeat' split at hemp) <;>
             simp_all [GSort.isEmptyFormer, GSort.botSort, GSort.nodeEmpty, GSort.edgeEmpty,
               beq_self_eq_true])
      all_goals
        (exfalso; simp only [RecordSchema.sortInter] at hemp
         (repeat' split at hemp) <;>
           simp_all [GSort.isEmptyFormer, GSort.botSort, GSort.nodeEmpty, GSort.edgeEmpty,
             beq_self_eq_true])
    all_goals
      (exfalso; simp only [RecordSchema.sortInter] at hemp
       (repeat' split at hemp) <;>
         simp_all [GSort.isEmptyFormer, GSort.botSort, GSort.nodeEmpty, GSort.edgeEmpty,
           beq_self_eq_true])
  all_goals
    (exfalso; simp only [RecordSchema.sortInter] at hemp
     (repeat' split at hemp) <;>
       simp_all [GSort.isEmptyFormer, GSort.botSort, GSort.nodeEmpty, GSort.edgeEmpty,
         beq_self_eq_true])

theorem schemaNEN_singleton {x : Name} {t : GSort} (ht : t.nodeEdgeNullable) :
    SchemaNodeEdgeNullable (RecordSchema.mk [(x, t)]) := by
  intro y s hy
  simp only [List.mem_singleton, Prod.mk.injEq] at hy
  obtain ⟨_, rfl⟩ := hy; exact ht

theorem schemaNEN_join {A B : RecordSchema}
    (hA : SchemaNodeEdgeNullable A) (hB : SchemaNodeEdgeNullable B) :
    SchemaNodeEdgeNullable (A.join B) := by
  intro x t hxt
  rcases RecordSchema.join_entry_cases hxt with
    ⟨t1, h1, _, ht⟩ | ⟨t1, t2, h1, h2lk, ht⟩ | ⟨t2, h2, _, ht⟩
  · rw [ht]; exact hA x t1 h1
  · rw [ht]; exact sortInter_nodeEdgeNullable (hA x t1 h1) (hB x t2 (RecordSchema.lookup_some_mem h2lk))
  · rw [ht]; exact hB x t2 h2

theorem schemaNEN_set {Gamma : RecordSchema} {x : Name} {t : GSort}
    (hG : SchemaNodeEdgeNullable Gamma) (ht : t.nodeEdgeNullable) :
    SchemaNodeEdgeNullable (Gamma.set x t) := by
  intro y s hys
  unfold RecordSchema.set at hys
  split at hys
  · simp only [RecordSchema.update, List.mem_map] at hys
    obtain ⟨⟨k, w⟩, hkw, heq⟩ := hys
    split at heq
    · rw [Prod.mk.injEq] at heq; obtain ⟨_, rfl⟩ := heq; exact ht
    · rw [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq; exact hG k w hkw
  · simp only [RecordSchema.extend, List.mem_append, List.mem_singleton] at hys
    rcases hys with h | h
    · exact hG y s h
    · rw [Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact ht

theorem schemaNEN_setMany : ∀ {bindings : List (Name × GSort)} {Gamma : RecordSchema},
    SchemaNodeEdgeNullable Gamma → (∀ p ∈ bindings, (Prod.snd p).nodeEdgeNullable) →
    SchemaNodeEdgeNullable (Gamma.setMany bindings)
  | [], _, hG, _ => hG
  | hd :: _tl, Gamma, hG, hb =>
      schemaNEN_setMany (Gamma := Gamma.set hd.1 hd.2)
        (schemaNEN_set hG (hb hd (List.mem_cons_self _ _)))
        (fun p hp => hb p (List.mem_cons_of_mem _ hp))

theorem schemaNEN_liftToGroupRef {Gamma : RecordSchema} {vars : List Name}
    (h : SchemaNodeEdgeNullable Gamma) : SchemaNodeEdgeNullable (Gamma.liftToGroupRef vars) := by
  intro x t hxt
  obtain ⟨t0, ht0, ht⟩ := RecordSchema.mem_liftToGroupRef_entries hxt
  rw [ht]; split
  · show GSort.nodeEdgeNullable t0.liftToList
    simp [GSort.nodeEdgeNullable, GSort.liftToList]
  · exact h x t0 ht0

theorem schemaNEN_liftToNullable {Gamma : RecordSchema} {vars : List Name}
    (h : SchemaNodeEdgeNullable Gamma) :
    SchemaNodeEdgeNullable (Gamma.liftToNullable vars) := by
  intro x t hxt
  obtain ⟨t0, ht0, ht⟩ := RecordSchema.mem_liftToNullable_entries hxt
  rw [ht]; split
  · show GSort.nodeEdgeNullable t0.toNullable
    obtain ⟨s0, n0⟩ := t0
    cases s0 <;>
      first
        | trivial
        | rfl
        | (rename_i es; cases es <;> first | trivial | rfl)
  · exact h x t0 ht0

theorem atomTyping_NEN {ctx : TypingCtx} {a : AtomInput} {Gamma : RecordSchema}
    (h : AtomTyping ctx a Gamma) : SchemaNodeEdgeNullable Gamma := by
  cases h <;>
    (apply schemaNEN_singleton
     simp [GSort.nodeEdgeNullable, GSort.nodeOf, GSort.edgeOf, GSort.nodeRefinedOf,
       GSort.edgeRefinedOf, GSort.nodeEmpty, GSort.edgeEmpty])

theorem refinementTyping_NEN {ctx : TypingCtx} {G1 G2 G3 : RecordSchema}
    {v1 r2 v3 : Name} {dir : Direction} {GammaRef : RecordSchema}
    (h : RefinementTyping ctx G1 G2 G3 v1 r2 v3 dir GammaRef)
    (h1 : SchemaNodeEdgeNullable G1) (h2 : SchemaNodeEdgeNullable G2)
    (h3 : SchemaNodeEdgeNullable G3) :
    SchemaNodeEdgeNullable GammaRef := by
  cases h with
  | open_ => exact schemaNEN_join (schemaNEN_join h1 h2) h3
  | _ =>
    apply schemaNEN_setMany (schemaNEN_join (schemaNEN_join h1 h2) h3)
    intro p hp
    obtain ⟨pk, pv⟩ := p
    simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq] at hp
    rcases hp with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | hnil <;>
      first
        | (simp [GSort.nodeEdgeNullable, GSort.nodeRefinedOf, GSort.edgeRefinedOf,
            GSort.nodeEmpty, GSort.edgeEmpty]; done)
        | exact absurd hnil (List.not_mem_nil _)

theorem patternTyping_NEN {ctx : TypingCtx} {qd : QuantDepth}
    {P : Pattern} {Gamma : RecordSchema} {v : Name}
    (h : PatternTyping ctx qd P Gamma v) :
    SchemaNodeEdgeNullable Gamma := by
  induction h with
  | patNode _ _ _ hAtom => exact atomTyping_NEN hAtom
  | patEdge _ _ _ _ _ _ _ _ _ _ hAtomN1 hAtomE hAtomN2 hRef =>
      exact refinementTyping_NEN hRef (atomTyping_NEN hAtomN1) (atomTyping_NEN hAtomE)
        (atomTyping_NEN hAtomN2)
  | patStep _ _ _ _ _ _ _ _ _ _ _ _ hAtomE hAtomN2 hRef ihPrefix =>
      exact refinementTyping_NEN hRef ihPrefix (atomTyping_NEN hAtomE)
        (atomTyping_NEN hAtomN2)
  | patQuantEdge _ _ _ _ _ _ _ hAtomE _ _ =>
      exact schemaNEN_liftToGroupRef (schemaNEN_join (schemaNEN_join
        (schemaNEN_singleton (by simp [GSort.nodeEdgeNullable, GSort.nodeOf]))
        (atomTyping_NEN hAtomE))
        (schemaNEN_singleton (by simp [GSort.nodeEdgeNullable, GSort.nodeOf])))
  | patOptEdge _ _ _ _ _ _ =>
      exact schemaNEN_liftToNullable (schemaNEN_join (schemaNEN_join
        (schemaNEN_singleton (by simp [GSort.nodeEdgeNullable, GSort.nodeOf]))
        (schemaNEN_singleton (by simp [GSort.nodeEdgeNullable, GSort.edgeOf])))
        (schemaNEN_singleton (by simp [GSort.nodeEdgeNullable, GSort.nodeOf])))
  | patQuantPath _ _ _ _ _ _ ihInner =>
      exact schemaNEN_liftToGroupRef ihInner
  | patGrouped _ _ _ _ _ ih => exact ih

theorem patExprTyping_NEN {ctx : TypingCtx} {P : Pattern} {Gamma : RecordSchema}
    (h : PatExprTyping ctx P Gamma) :
    SchemaNodeEdgeNullable Gamma := by
  induction h with
  | single _ _ _ hp => exact patternTyping_NEN hp
  | conjunction _ _ _ _ _ _ h2 _ ih1 =>
      exact schemaNEN_join ih1 (patternTyping_NEN h2)

/-- Away from the three step variables, the refined output schema looks up
    like the prefix schema, in every refinement mode. -/
private theorem refinementTyping_lookup_other
    {ctx : TypingCtx} {Gamma1 GammaE GammaN2 GammaRef : RecordSchema}
    {v1 r2 v3 : Name} {dir : Direction}
    (hRef : RefinementTyping ctx Gamma1 GammaE GammaN2 v1 r2 v3 dir GammaRef)
    (hwf1 : SchemaWF Gamma1) (hwfE : SchemaWF GammaE) (hwfN : SchemaWF GammaN2)
    (x : Name)
    (hx1 : (v1 == x) = false)
    (hElk : GammaE.lookup x = none) (hNlk : GammaN2.lookup x = none)
    (hxr : (r2 == x) = false) (hxn : (v3 == x) = false) :
    GammaRef.lookup x = Gamma1.lookup x := by
  cases hRef with
  | open_ hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 =>
    rw [RecordSchema.join_lookup_of_right_none (RecordSchema.join_schemaWF hwf1 hwfE) hwfN hNlk,
        RecordSchema.join_lookup_of_right_none hwf1 hwfE hElk]
  | closed sN1 sE2 sN3 sN1' sE2' sN3' hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13
      hSrc' hEdge' hDst' hNonEmpty =>
    rw [RecordSchema.setMany3_lookup_other _ v1 r2 v3 _ _ _ x hx1 hxr hxn,
        RecordSchema.join_lookup_of_right_none (RecordSchema.join_schemaWF hwf1 hwfE) hwfN hNlk,
        RecordSchema.join_lookup_of_right_none hwf1 hwfE hElk]
  | closedEmpty hJC12 hJC23 hJC13 hSomeEmpty =>
    rw [RecordSchema.setMany3_lookup_other _ v1 r2 v3 _ _ _ x hx1 hxr hxn,
        RecordSchema.join_lookup_of_right_none (RecordSchema.join_schemaWF hwf1 hwfE) hwfN hNlk,
        RecordSchema.join_lookup_of_right_none hwf1 hwfE hElk]
  | closedFail sN1 sE2 sN3 hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 hFail =>
    rw [RecordSchema.setMany3_lookup_other _ v1 r2 v3 _ _ _ x hx1 hxr hxn,
        RecordSchema.join_lookup_of_right_none (RecordSchema.join_schemaWF hwf1 hwfE) hwfN hNlk,
        RecordSchema.join_lookup_of_right_none hwf1 hwfE hElk]


/-- The tail variable of a pattern is one of the variables it binds. -/
theorem patternTailVar_in_vars (P : Pattern) (v : Name) (h : patternTailVar P = some v) :
    (patternVars P).any (fun w => w == v) = true := by
  induction P with
  | node na => simp only [patternTailVar, Option.some.injEq] at h; subst h; simp [patternVars]
  | edge n1 rel dir n2 => simp only [patternTailVar, Option.some.injEq] at h; subst h; simp [patternVars]
  | step P rel dir n2 ih =>
    simp only [patternTailVar, Option.some.injEq] at h; subst h
    simp [patternVars, List.any_append]
  | grouped P ih => exact ih (by simpa [patternTailVar] using h)
  | quantified P K ih => exact ih (by simpa [patternTailVar] using h)
  | patternList P1 P2 ih1 ih2 =>
    have := ih2 (by simpa [patternTailVar] using h)
    simp [patternVars, List.any_append, this]


/-- The evaluator binds exactly the pattern's variables. Every record produced
    by `evalPattern P` has domain `patternVars P`. With `patternTyping_vars_mem`
    (which equates `patternVars P` to the typed schema's domain) this gives the
    record/schema domain agreement the step strong soundness needs. -/
theorem evalBindsPatternVars (ctx : TypingCtx) (G : PropertyGraph) :
    ∀ (qd : QuantDepth) (P : Pattern) (Gamma : RecordSchema) (v : Name),
      PatternTyping ctx qd P Gamma v →
      ∀ rho, rho ∈ evalPattern G ctx.graphSite P →
        ∀ z, rho.mem z = (patternVars P).any (fun w => w == z) := by
  intro qd P Gamma v h
  induction h with
  | patNode qd na GammaA hAtom =>
    intro rho hrho z
    rw [evalPattern_node] at hrho
    obtain ⟨i, rfl⟩ := matchNode_mem_form hrho
    simp [Record.mem, patternVars]
  | patEdge qd n1 n2 rel dir GammaN1 GammaE GammaN2 GammaRef hSingleD hAtomN1 hAtomE hAtomN2 hRef =>
    intro rho hrho z
    rw [evalPattern_edge_single G ctx.graphSite n1 n2 rel dir hSingleD] at hrho
    obtain ⟨srcN, ei, dstN, _, _, _, _, _, _, rfl⟩ := matchSingleEdge_mem_form hrho
    simp [Record.mem, patternVars]
  | patStep qd P rel dir n2 Gamma1 GammaE GammaN2 GammaRef v1 hSingle hPrefix hAtomE hAtomN2 hRef ihPrefix =>
    intro rho hrho z
    have htv : patternTailVar P = some v1 := patternTyping_tailVar hPrefix
    obtain ⟨rho_p, rhoEdge, hrho_p, hedge, _, _, rfl⟩ :=
      evalPattern_step_single_mem G ctx.graphSite P rel dir n2 v1 hSingle htv rho hrho
    obtain ⟨srcN, ei, dstN, _, _, _, _, _, _, rfl⟩ := matchSingleEdge_mem_form hedge
    rw [Record.merge_mem, ihPrefix rho_p hrho_p z]
    have hv1 := patternTailVar_in_vars P v1 htv
    simp only [patternVars, List.any_append, Record.mem, List.any_cons, List.any_nil, Bool.or_false]
    cases hvz : v1 == z with
    | true =>
      have : (patternVars P).any (fun w => w == z) = true := by rw [← eq_of_beq hvz]; exact hv1
      simp [this]
    | false => simp [hvz, Bool.or_assoc]
  | patQuantEdge n1 n2 rel dir K GammaE hQuant hAtomE hNE12 hNE23 =>
    intro rho hrho z
    have hH1 : (n1.var == rel.var) = false := beq_name_symm_false hNE12
    have hH2 : (n2.var == rel.var) = false := beq_name_symm_false hNE23
    have hbody : ∀ lo hi, rho ∈ matchRangePath G ctx.graphSite n1 { rel with quantifier := K } n2 dir lo hi →
        rho.mem z = (patternVars (Pattern.edge n1 { rel with quantifier := K } dir n2)).any (fun w => w == z) := by
      intro lo hi hm
      obtain ⟨srcN, dstN, edges, rfl⟩ :=
        matchRangePath_mem_form G ctx.graphSite dir n1 { rel with quantifier := K } n2 lo hi rho
          hH1 hH2 hm
      simp [Record.mem, patternVars]
    cases K with
    | single => simp [Quantifier.isGroupRef] at hQuant
    | question => simp [Quantifier.isGroupRef] at hQuant
    | star => simp only [evalPattern] at hrho; exact hbody _ _ hrho
    | plus => simp only [evalPattern] at hrho; exact hbody _ _ hrho
    | exact i => simp only [evalPattern] at hrho; exact hbody _ _ hrho
    | range i j => simp only [evalPattern] at hrho; exact hbody _ _ hrho
  | patOptEdge n1 n2 rel dir hNE12 hNE23 =>
    intro rho hrho z
    have hrho' : rho ∈ matchOptionalEdge G ctx.graphSite n1
        { rel with quantifier := .question } n2 dir := hrho
    rcases matchOptionalEdge_mem hrho' with ⟨i, hi, rfl⟩ | ho
    · simp [Record.mem, patternVars]
    · obtain ⟨srcN, ei, dstN, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ :=
        matchSingleEdge_mem_form' ho
      simp [Record.mem, patternVars]
  | patQuantPath P K GammaInner v hInner hQuant ihInner =>
    intro rho hrho z
    obtain ⟨lv, hlv⟩ := patternLeadVar_isSome P
    obtain ⟨tv, htv⟩ := patternTailVar_isSome P
    simp only [evalPattern, hlv, htv] at hrho
    obtain ⟨path, rfl⟩ := evalQuantified_listForm (patternVars P) _ lv tv _ _ rho hrho
    simp only [collapsePath_mem, patternVars]
  | patGrouped qd P Gamma v hP ihP =>
    intro rho hrho z; exact ihP rho hrho z


/-- A record lookup returns one of the record's values, or null. -/
private theorem lookup_mem_or_null (rho : Record) (z : Name) :
    (∃ p, p ∈ rho ∧ rho.lookup z = p.2) ∨ rho.lookup z = Value.null := by
  cases hf : rho.find? (fun e => e.1 == z) with
  | none =>
    right
    show (match rho.find? (fun e => e.1 == z) with
          | some (_, v) => v | none => Value.null) = Value.null
    rw [hf]
  | some p =>
    left
    obtain ⟨a, b⟩ := p
    refine ⟨(a, b), List.mem_of_find?_eq_some hf, ?_⟩
    show (match rho.find? (fun e => e.1 == z) with
          | some (_, v) => v | none => Value.null) = (a, b).2
    rw [hf]


set_option maxHeartbeats 1600000 in
/-- A refined-single meet has a refined-single operand: `sortInter` only
    produces a refined single shape out of an operand that already has
    one (same-shape, refined-refined, or refined-unrefined branches). -/
private theorem sortInter_refined_operand {t1 t2 : GSort}
    (h : (∃ Gs ss, (RecordSchema.sortInter t1 t2).shape = SortShape.single (.nodeRefined Gs ss)) ∨
         (∃ Gs ss, (RecordSchema.sortInter t1 t2).shape = SortShape.single (.edgeRefined Gs ss))) :
    ((∃ Gs ss, t1.shape = SortShape.single (.nodeRefined Gs ss)) ∨
     (∃ Gs ss, t1.shape = SortShape.single (.edgeRefined Gs ss))) ∨
    ((∃ Gs ss, t2.shape = SortShape.single (.nodeRefined Gs ss)) ∨
     (∃ Gs ss, t2.shape = SortShape.single (.edgeRefined Gs ss))) := by
  obtain ⟨s1, n1⟩ := t1
  obtain ⟨s2, n2⟩ := t2
  unfold RecordSchema.sortInter at h
  rcases s1 with es1 | _ | _ | _ | (_ | ⟨e1, ts1⟩) | ⟨ls1, ln1⟩ | ⟨fs1, fn1⟩ <;>
    rcases s2 with es2 | _ | _ | _ | (_ | ⟨e2, ts2⟩) | ⟨ls2, ln2⟩ | ⟨fs2, fn2⟩ <;>
    (try cases es1) <;> (try cases es2) <;>
    dsimp only at h <;> (repeat' split at h) <;>
    rcases h with ⟨Gs, ss, hsh⟩ | ⟨Gs, ss, hsh⟩ <;>
    first
      | exact Or.inl (Or.inl ⟨_, _, rfl⟩)
      | exact Or.inl (Or.inr ⟨_, _, rfl⟩)
      | exact Or.inr (Or.inl ⟨_, _, rfl⟩)
      | exact Or.inr (Or.inr ⟨_, _, rfl⟩)
      | simp [GSort.botSort, GSort.nodeEmpty, GSort.edgeEmpty] at hsh

/-- A variable typed with a refined single sort is never bound to null.
    Refined sorts arise only from the closed single-edge rules, whose
    evaluator binds references; the quantified and optional rules expose
    open (or list-lifted) sorts only.  This is what excludes the `?`
    quantifier's null bindings at the empty-former-meet vacuity. -/
theorem patternTyping_refinedNonNull
    (ctx : TypingCtx) (G : PropertyGraph) :
    ∀ (qd : QuantDepth) (P : Pattern) (Gamma : RecordSchema) (v : Name),
      PatternTyping ctx qd P Gamma v →
      ∀ rho, rho ∈ evalPattern G ctx.graphSite P →
      ∀ x t, (x, t) ∈ Gamma.entries →
      ((∃ Gs ss, t.shape = SortShape.single (.nodeRefined Gs ss)) ∨
       (∃ Gs ss, t.shape = SortShape.single (.edgeRefined Gs ss))) →
      rho.lookup x ≠ Value.null := by
  intro qd P Gamma v h
  induction h with
  | patNode qd na GammaA hAtom =>
    intro rho hrho x t hxt href hnull
    obtain ⟨T, rfl⟩ := atomTyping_node_singleton hAtom
    obtain ⟨hx, -⟩ := Prod.mk.injEq .. ▸ List.mem_singleton.mp hxt
    obtain ⟨i, rfl⟩ := matchNode_mem_form hrho
    subst hx
    simp [Record.lookup, List.find?_cons] at hnull
  | patEdge qd n1 n2 rel dir GammaN1 GammaE GammaN2 GammaRef hSingleD hAtomN1 hAtomE hAtomN2 hRef =>
    intro rho hrho x t hxt href hnull
    have hmem : rho.mem x = true := by
      rw [evalBindsPatternVars ctx G qd _ _ _
            (PatternTyping.patEdge ctx qd n1 n2 rel dir GammaN1 GammaE
              GammaN2 GammaRef hSingleD hAtomN1 hAtomE hAtomN2 hRef) rho hrho x,
          patternTyping_vars_mem
            (PatternTyping.patEdge ctx qd n1 n2 rel dir GammaN1 GammaE
              GammaN2 GammaRef hSingleD hAtomN1 hAtomE hAtomN2 hRef) x]
      exact RecordSchema.mem_of_entry hxt
    have hrho' : rho ∈ matchSingleEdge G ctx.graphSite n1 rel n2 dir := by
      rw [← evalPattern_edge_single G ctx.graphSite n1 n2 rel dir hSingleD]
      exact hrho
    obtain ⟨srcN, ei, dstN, _, _, _, _, _, _, _, _, _, _, _, hform⟩ :=
      matchSingleEdge_mem_form' hrho'
    rcases lookup_mem_or_null rho x with ⟨p, hp, hpv⟩ | hn
    · have hp2 : p.2 = Value.null := hpv.symm.trans hnull
      rw [hform] at hp
      rcases hp with _ | ⟨_, hp⟩
      · exact Value.noConfusion hp2
      · rcases hp with _ | ⟨_, hp⟩
        · exact Value.noConfusion hp2
        · rcases hp with _ | ⟨_, hp⟩
          · exact Value.noConfusion hp2
          · exact absurd hp (List.not_mem_nil p)
    · cases hf : rho.find? (fun e => e.1 == x) with
      | some p =>
        have : (∃ p, p ∈ rho ∧ rho.lookup x = p.2) := by
          refine ⟨p, List.mem_of_find?_eq_some hf, ?_⟩
          show (match rho.find? (fun e => e.1 == x) with
                | some (_, v) => v | none => Value.null) = p.2
          rw [hf]
        obtain ⟨p, hp, hpv⟩ := this
        have hp2 : p.2 = Value.null := hpv.symm.trans hnull
        rw [hform] at hp
        rcases hp with _ | ⟨_, hp⟩
        · exact Value.noConfusion hp2
        · rcases hp with _ | ⟨_, hp⟩
          · exact Value.noConfusion hp2
          · rcases hp with _ | ⟨_, hp⟩
            · exact Value.noConfusion hp2
            · exact absurd hp (List.not_mem_nil p)
      | none =>
        rw [List.find?_eq_none] at hf
        obtain ⟨y, hy, hpy⟩ := List.any_eq_true.mp (hmem : rho.any (fun e => e.1 == x) = true)
        exact absurd hpy (hf y hy)
  | patStep qd P rel dir n2 Gamma1 GammaE GammaN2 GammaRef v1 hSingle hPrefix hAtomE hAtomN2 hRef ihPrefix =>
    intro rho_out hmem x t hxt href hnull
    obtain ⟨rho, rhoEdge, hrho, hedge, hStepAgree, ⟨gv, srcN0, hrhov1⟩, rfl⟩ :=
      evalPattern_step_single_mem G ctx.graphSite P rel dir n2 v1 hSingle
        (patternTyping_tailVar hPrefix) rho_out hmem
    obtain ⟨T2, rfl⟩ := atomTyping_node_singleton hAtomN2
    obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
    have hrelEq : ({ rel with quantifier := .single } : EdgeAtom) = rel := by
      cases rel with | mk v l p q => cases hSingle; rfl
    rw [hrelEq] at hedge
    obtain ⟨srcN, ei, dstN, hsrcN, hei, hdstN, _, _, _, _, _, _, _, hsd, hform⟩ :=
      matchSingleEdge_mem_form' hedge
    cases hxe : rhoEdge.mem x with
    | true =>
      have hlkE := Record.merge_lookup_agree_right rho rhoEdge x hStepAgree hxe
      rw [hlkE] at hnull
      rcases lookup_mem_or_null rhoEdge x with ⟨p, hp, hpv⟩ | hn
      · have hp2 : p.2 = Value.null := hpv.symm.trans hnull
        rw [hform] at hp
        rcases hp with _ | ⟨_, hp⟩
        · exact Value.noConfusion hp2
        · rcases hp with _ | ⟨_, hp⟩
          · exact Value.noConfusion hp2
          · rcases hp with _ | ⟨_, hp⟩
            · exact Value.noConfusion hp2
            · exact absurd hp (List.not_mem_nil p)
      · cases hf : rhoEdge.find? (fun e => e.1 == x) with
        | some p =>
          have hpv : rhoEdge.lookup x = p.2 := by
            show (match rhoEdge.find? (fun e => e.1 == x) with
                  | some (_, v) => v | none => Value.null) = p.2
            rw [hf]
          have hp2 : p.2 = Value.null := hpv.symm.trans hn
          have hp := List.mem_of_find?_eq_some hf
          rw [hform] at hp
          rcases hp with _ | ⟨_, hp⟩
          · exact Value.noConfusion hp2
          · rcases hp with _ | ⟨_, hp⟩
            · exact Value.noConfusion hp2
            · rcases hp with _ | ⟨_, hp⟩
              · exact Value.noConfusion hp2
              · exact absurd hp (List.not_mem_nil p)
        | none =>
          rw [List.find?_eq_none] at hf
          obtain ⟨y, hy, hpy⟩ :=
            List.any_eq_true.mp (hxe : rhoEdge.any (fun e => e.1 == x) = true)
          exact absurd hpy (hf y hy)
    | false =>
      have hb1 : (v1 == x) = false := by
        cases hb : v1 == x with
        | false => rfl
        | true =>
          rw [hform] at hxe
          simp [Record.mem, hb] at hxe
      have hbr : (rel.var == x) = false := by
        cases hb : rel.var == x with
        | false => rfl
        | true =>
          rw [hform] at hxe
          simp [Record.mem, hb] at hxe
      have hbn : (n2.var == x) = false := by
        cases hb : n2.var == x with
        | false => rfl
        | true =>
          rw [hform] at hxe
          simp [Record.mem, hb] at hxe
      have hwf1 : SchemaWF Gamma1 := patternTyping_schemaWF hPrefix
      have hwfRef : SchemaWF GammaRef :=
        patternTyping_schemaWF
          (PatternTyping.patStep ctx qd P rel dir n2 Gamma1 _ _ GammaRef v1
            hSingle hPrefix hAtomE hAtomN2 hRef)
      have hlkRef : GammaRef.lookup x = some t := hwfRef x t hxt
      have hElk : (RecordSchema.mk [(rel.var, TE)]).lookup x = none :=
        RecordSchema.lookup_eq_none_of_mem_false (by rw [singleton_schema_mem]; exact hbr)
      have hNlk : (RecordSchema.mk [(n2.var, T2)]).lookup x = none :=
        RecordSchema.lookup_eq_none_of_mem_false (by rw [singleton_schema_mem]; exact hbn)
      rw [refinementTyping_lookup_other hRef hwf1 (RecordSchema.singleton_schemaWF _ _)
        (RecordSchema.singleton_schemaWF _ _) x hb1 hElk hNlk hbr hbn] at hlkRef
      have hxrho : rho.mem x = true := by
        rw [evalBindsPatternVars ctx G qd P Gamma1 v1 hPrefix rho hrho x,
            patternTyping_vars_mem hPrefix x]
        exact RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem hlkRef)
      have hnL : rho.lookup x = Value.null := by
        rw [← Record.merge_lookup_left rho rhoEdge x hxrho]
        exact hnull
      exact ihPrefix rho hrho x t (RecordSchema.lookup_some_mem hlkRef) href hnL
  | patQuantEdge n1 n2 rel dir K GammaE hQuant hAtomE hNE12 hNE23 =>
    intro rho hrho x t hxt href hnull
    obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
    obtain ⟨t0, ht0, ht⟩ := RecordSchema.mem_liftToGroupRef_entries hxt
    subst ht
    rcases open_join_entry_is_nodeOf_or_edgeOf ctx.graphSite n1 n2 rel
      TE hNE12 hNE23 x t0 ht0 with hn | ⟨hxrel, hn⟩
    · rcases href with ⟨Gs, ss, hsh⟩ | ⟨Gs, ss, hsh⟩ <;>
        (rw [hn] at hsh
         split at hsh <;> simp [GSort.liftToList, GSort.nodeOf] at hsh)
    · subst hxrel
      subst hn
      rcases href with ⟨Gs, ss, hsh⟩ | ⟨Gs, ss, hsh⟩ <;>
        (split at hsh
         · simp [GSort.liftToList] at hsh
         · rename_i hcond
           exact absurd (by simp [beq_self_eq_true] :
             ([rel.var].any (fun v => v == rel.var)) = true) hcond)
  | patOptEdge n1 n2 rel dir hNE12 hNE23 =>
    intro rho hrho x t hxt href hnull
    obtain ⟨t0, ht0, ht⟩ := RecordSchema.mem_liftToNullable_entries hxt
    subst ht
    rcases open_join_entry_is_nodeOf_or_edgeOf ctx.graphSite n1 n2 rel
      (GSort.edgeOf ctx.graphSite) hNE12 hNE23 x t0 ht0 with hn | ⟨_, hn⟩ <;>
      rcases href with ⟨Gs, ss, hsh⟩ | ⟨Gs, ss, hsh⟩ <;>
        (rw [hn] at hsh
         split at hsh <;> simp [GSort.toNullable, GSort.nodeOf, GSort.edgeOf] at hsh)
  | patQuantPath P K GammaInner v hInner hQuant ihInner =>
    intro rho hrho x t hxt href hnull
    obtain ⟨t0, ht0, ht⟩ := RecordSchema.mem_liftToGroupRef_entries hxt
    have hmemI : GammaInner.mem x = true := RecordSchema.mem_of_entry ht0
    have hx_inner : GammaInner.dom.any (fun w => w == x) = true := by
      rw [RecordSchema.dom_any_mem GammaInner x]
      exact hmemI
    rw [hx_inner] at ht
    simp only [if_true] at ht
    subst ht
    rcases href with ⟨Gs, ss, hsh⟩ | ⟨Gs, ss, hsh⟩ <;>
      simp [GSort.liftToList] at hsh
  | patGrouped qd P Gamma v hP ih =>
    intro rho hrho x t hxt href hnull
    rw [evalPattern_grouped] at hrho
    exact ih rho hrho x t hxt href hnull

/-- Domain agreement at the pattern-expression level, from the syntactic
    variable machinery alone (no soundness premises). -/
private theorem patExprTyping_domEq
    (ctx : TypingCtx) (G : PropertyGraph)
    {P : Pattern} {Gamma : RecordSchema}
    (hType : PatExprTyping ctx P Gamma) :
    ∀ rho, rho ∈ evalPattern G ctx.graphSite P →
    ∀ z, rho.mem z = Gamma.mem z := by
  induction hType with
  | single P Gamma v h =>
    intro rho hrho z
    rw [evalBindsPatternVars ctx G _ _ _ _ h rho hrho z,
        patternTyping_vars_mem h z]
  | conjunction P1 P2 Gamma1 Gamma2 v h1 h2 hjc ih1 =>
    intro rho hrho z
    rw [evalPattern_patternList] at hrho
    obtain ⟨rho1, hrho1, rho2, hrho2, hag, rfl⟩ := mem_bindingTableJoin hrho
    rw [Record.merge_mem, RecordSchema.join_mem, ih1 rho1 hrho1 z,
        evalBindsPatternVars ctx G _ _ _ _ h2 rho2 hrho2 z,
        patternTyping_vars_mem h2 z]

/-- Pattern-expression level refined-non-null (joins classified through the
    meet). -/
theorem patExprTyping_refinedNonNull
    (ctx : TypingCtx) (G : PropertyGraph)
    {P : Pattern} {Gamma : RecordSchema}
    (hType : PatExprTyping ctx P Gamma) :
    ∀ rho, rho ∈ evalPattern G ctx.graphSite P →
    ∀ x t, (x, t) ∈ Gamma.entries →
    ((∃ Gs ss, t.shape = SortShape.single (.nodeRefined Gs ss)) ∨
     (∃ Gs ss, t.shape = SortShape.single (.edgeRefined Gs ss))) →
    rho.lookup x ≠ Value.null := by
  induction hType with
  | single P Gamma v h =>
    exact patternTyping_refinedNonNull ctx G
      .outside P Gamma v h
  | conjunction P1 P2 Gamma1 Gamma2 v h1 h2 hjc ih1 =>
    intro rho hrho x t hxt href hnull
    rw [evalPattern_patternList] at hrho
    obtain ⟨rho1, hrho1, rho2, hrho2, hagree, rfl⟩ := mem_bindingTableJoin hrho
    have hdom1 : ∀ z, rho1.mem z = Gamma1.mem z := patExprTyping_domEq ctx G h1 rho1 hrho1
    have hdom2 : ∀ z, rho2.mem z = Gamma2.mem z := fun z => by
      rw [evalBindsPatternVars ctx G _ _ _ _ h2 rho2 hrho2 z,
          patternTyping_vars_mem h2 z]
    rcases RecordSchema.join_entry_cases hxt with
      ⟨t1, h1e, hm2, ht⟩ | ⟨t1, t2, h1e, h2lk, ht⟩ | ⟨t2, h2e, hm1, ht⟩
    · have hmem1 : rho1.mem x = true := by
        rw [hdom1 x]; exact RecordSchema.mem_of_entry h1e
      have hn1 : rho1.lookup x = Value.null := by
        rw [← Record.merge_lookup_left rho1 rho2 x hmem1]
        exact hnull
      exact ih1 rho1 hrho1 x t1 h1e (ht ▸ href) hn1
    · have hmem1 : rho1.mem x = true := by
        rw [hdom1 x]; exact RecordSchema.mem_of_entry h1e
      have hn1 : rho1.lookup x = Value.null := by
        rw [← Record.merge_lookup_left rho1 rho2 x hmem1]
        exact hnull
      subst ht
      rcases sortInter_refined_operand href with hop1 | hop2
      · exact ih1 rho1 hrho1 x t1 h1e hop1 hn1
      · have hmem2 : rho2.mem x = true := by
          rw [hdom2 x]
          exact RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem h2lk)
        have hn2 : rho2.lookup x = Value.null := by
          rw [← Record.agreeOn_lookup_eq rho1 rho2 x hagree hmem1 hmem2]
          exact hn1
        exact patternTyping_refinedNonNull ctx G
          .outside P2 Gamma2 v h2 rho2 hrho2 x t2
          (RecordSchema.lookup_some_mem h2lk) hop2 hn2
    · have hmem2 : rho2.mem x = true := by
        rw [hdom2 x]; exact RecordSchema.mem_of_entry h2e
      have hmem1f : rho1.mem x = false := by
        cases hb : rho1.mem x with
        | false => rfl
        | true =>
          exfalso
          rw [hdom1 x] at hb
          rw [hb] at hm1
          exact Bool.noConfusion hm1
      have hn2 : rho2.lookup x = Value.null := by
        rw [← Record.merge_lookup_right rho1 rho2 x hmem1f]
        exact hnull
      exact patternTyping_refinedNonNull ctx G
        .outside P2 Gamma2 v h2 rho2 hrho2 x t2 h2e
        (ht ▸ href) hn2

/-- The closed-graph empty-former-meet vacuity: a shared variable whose two typed
    refinements meet to an empty former cannot actually occur, because the strong
    runtime invariant makes the matched node/edge conform to a catalog schema in
    both refined lists, whose intersection is empty. -/
theorem emptyFormerMeet_vacuous
    (ctx : TypingCtx) (G : PropertyGraph) (Psi : GraphSchemaFull)
    (hGconf : graphConformsSchema G Psi = true)
    {P1 P2 : Pattern} {Gamma1 Gamma2 : RecordSchema} {v0 : Name}
    (h1 : PatExprTyping ctx P1 Gamma1)
    (h2 : PatternTyping ctx .outside P2 Gamma2 v0)
    (hS1 : ∀ rho, rho ∈ evalPattern G ctx.graphSite P1 → RuntimeConfigWFStrong G Psi rho Gamma1)
    (hS2 : ∀ rho, rho ∈ evalPattern G ctx.graphSite P2 → RuntimeConfigWFStrong G Psi rho Gamma2)
    (hSound1 : BTConforms (evalPattern G ctx.graphSite P1) Gamma1)
    (hSound2 : BTConforms (evalPattern G ctx.graphSite P2) Gamma2)
    (x : Name) (t1 t2 : GSort)
    (hg1lk : Gamma1.lookup x = some t1) (hg2lk : Gamma2.lookup x = some t2)
    (hemp : (RecordSchema.sortInter t1 t2).isEmptyFormer = true)
    (rho1 rho2 : Record) (hrho1 : rho1 ∈ evalPattern G ctx.graphSite P1)
    (hrho2 : rho2 ∈ evalPattern G ctx.graphSite P2)
    (hag : rho1.agreeOn rho2 = true)
    (hadmt1 : RecordSchema.valueAdmissible (rho1.lookup x) t1 = true)
    (hadmt2 : RecordSchema.valueAdmissible (rho1.lookup x) t2 = true) :
    False := by
  have hNEN1 : t1.nodeEdgeNullable :=
    patExprTyping_NEN h1 x t1 (RecordSchema.lookup_some_mem hg1lk)
  have hNEN2 : t2.nodeEdgeNullable :=
    patternTyping_NEN h2 x t2 (RecordSchema.lookup_some_mem hg2lk)
  have hm1mem : rho1.mem x = true := by
    rw [(hSound1 rho1 hrho1).1 x]
    exact RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem hg1lk)
  have hm2mem : rho2.mem x = true := by
    rw [(hSound2 rho2 hrho2).1 x]
    exact RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem hg2lk)
  have hlkeq : rho1.lookup x = rho2.lookup x :=
    Record.agreeOn_lookup_eq _ _ _ hag hm1mem hm2mem
  have hrb := evalPattern_refBoundWF G ctx.graphSite P1 rho1 hrho1 x hm1mem
  rcases sortInter_emptyFormer_adm_classify hemp hadmt1 hadmt2 with
    ⟨Gr, ss1, ss2, hsh1, hsh2⟩ | ⟨Gr, ss1, ss2, hsh1, hsh2⟩
  · have hnl1 : t1.null = NullTag.nullable := by
      have h := hNEN1; unfold GSort.nodeEdgeNullable at h; rw [hsh1] at h; exact h
    have hnl2 : t2.null = NullTag.nullable := by
      have h := hNEN2; unfold GSort.nodeEdgeNullable at h; rw [hsh2] at h; exact h
    have ht1eq : t1 = GSort.nodeRefinedOf Gr ss1 := by rw [GSort.nodeRefinedOf, ← hsh1, ← hnl1]
    have ht2eq : t2 = GSort.nodeRefinedOf Gr ss2 := by rw [GSort.nodeRefinedOf, ← hsh2, ← hnl2]
    obtain ⟨g, n, hn, hveq⟩ : ∃ g n, n < G.numNodes ∧ rho1.lookup x = Value.nodeRef g n := by
      rcases hrb with ⟨gg, nn, hnn, hvv⟩ | ⟨gg, ee, hee, hvv⟩ | ⟨l, hvv⟩ | hvv
      · exact ⟨gg, nn, hnn, hvv⟩
      · exfalso; rw [hvv, ht1eq] at hadmt1
        simp [RecordSchema.valueAdmissible, GSort.nodeRefinedOf, Value.hasExtSort] at hadmt1
      · exfalso; rw [hvv, ht1eq] at hadmt1
        simp [RecordSchema.valueAdmissible, GSort.nodeRefinedOf, Value.hasExtSort] at hadmt1
      · exact absurd hvv (patExprTyping_refinedNonNull ctx G h1 rho1 hrho1 x t1
          (RecordSchema.lookup_some_mem hg1lk) (Or.inl ⟨Gr, ss1, hsh1⟩))
    have hct1 : t1.componentType = GSort.nodeRefinedOf Gr ss1 := componentType_eq_nodeRefinedOf t1 Gr ss1 hsh1 hnl1
    have hct2 : t2.componentType = GSort.nodeRefinedOf Gr ss2 := componentType_eq_nodeRefinedOf t2 Gr ss2 hsh2 hnl2
    have hm1 : ∀ ns, ns ∈ Psi.nodeSchemas → nodeConformsSchema G ⟨n, hn⟩ ns = true → ns ∈ ss1 :=
      ((hS1 rho1 hrho1) x t1 hg1lk).1 Gr ss1 hct1 g n hn hveq
    have hm2 : ∀ ns, ns ∈ Psi.nodeSchemas → nodeConformsSchema G ⟨n, hn⟩ ns = true → ns ∈ ss2 :=
      ((hS2 rho2 hrho2) x t2 hg2lk).1 Gr ss2 hct2 g n hn (hlkeq ▸ hveq)
    rw [ht1eq, ht2eq] at hemp
    exact nodeRefined_disjoint_vacuous hGconf hn hm1 hm2 hemp
  · have hnl1 : t1.null = NullTag.nullable := by
      have h := hNEN1; unfold GSort.nodeEdgeNullable at h; rw [hsh1] at h; exact h
    have hnl2 : t2.null = NullTag.nullable := by
      have h := hNEN2; unfold GSort.nodeEdgeNullable at h; rw [hsh2] at h; exact h
    have ht1eq : t1 = GSort.edgeRefinedOf Gr ss1 := by rw [GSort.edgeRefinedOf, ← hsh1, ← hnl1]
    have ht2eq : t2 = GSort.edgeRefinedOf Gr ss2 := by rw [GSort.edgeRefinedOf, ← hsh2, ← hnl2]
    obtain ⟨g, e, he, hveq⟩ : ∃ g e, e < G.numEdges ∧ rho1.lookup x = Value.edgeRef g e := by
      rcases hrb with ⟨gg, nn, hnn, hvv⟩ | ⟨gg, ee, hee, hvv⟩ | ⟨l, hvv⟩ | hvv
      · exfalso; rw [hvv, ht1eq] at hadmt1
        simp [RecordSchema.valueAdmissible, GSort.edgeRefinedOf, Value.hasExtSort] at hadmt1
      · exact ⟨gg, ee, hee, hvv⟩
      · exfalso; rw [hvv, ht1eq] at hadmt1
        simp [RecordSchema.valueAdmissible, GSort.edgeRefinedOf, Value.hasExtSort] at hadmt1
      · exact absurd hvv (patExprTyping_refinedNonNull ctx G h1 rho1 hrho1 x t1
          (RecordSchema.lookup_some_mem hg1lk) (Or.inr ⟨Gr, ss1, hsh1⟩))
    have hct1 : t1.componentType = GSort.edgeRefinedOf Gr ss1 := componentType_eq_edgeRefinedOf t1 Gr ss1 hsh1 hnl1
    have hct2 : t2.componentType = GSort.edgeRefinedOf Gr ss2 := componentType_eq_edgeRefinedOf t2 Gr ss2 hsh2 hnl2
    have hm1 : ∀ es, es ∈ Psi.edgeSchemas → edgeConformsSchema G ⟨e, he⟩ es = true → es ∈ ss1 :=
      ((hS1 rho1 hrho1) x t1 hg1lk).2 Gr ss1 hct1 g e he hveq
    have hm2 : ∀ es, es ∈ Psi.edgeSchemas → edgeConformsSchema G ⟨e, he⟩ es = true → es ∈ ss2 :=
      ((hS2 rho2 hrho2) x t2 hg2lk).2 Gr ss2 hct2 g e he (hlkeq ▸ hveq)
    rw [ht1eq, ht2eq] at hemp
    exact edgeRefined_disjoint_vacuous hGconf he hm1 hm2 hemp




/-- Pattern-expression soundness (Theorem 6.2, closed sites).  The PE-Single
    layer goes through `patternTyping_sound`; the PE-Conjunction layer joins
    the operand tables via `bindingTableJoin_conforms`, with the empty-former
    meets ruled out by the strong runtime invariant. -/
theorem patExprSoundness
    (ctx : TypingCtx) (G : PropertyGraph)
    (hCat : ∀ Psi', ctx.schemaMap.lookup ctx.graphSite = some Psi' →
              graphConformsSchema G Psi' = true)
    (Psi : GraphSchemaFull) (hPsi : ctx.schemaMap.lookup ctx.graphSite = some Psi)
    (hStrongFn : ∀ (qd' : QuantDepth) (P' : Pattern) (Gamma' : RecordSchema) (v' : Name),
        PatternTyping ctx qd' P' Gamma' v' →
        ∀ rho, rho ∈ evalPattern G ctx.graphSite P' → RuntimeConfigWFStrong G Psi rho Gamma')
    (P : Pattern) (GammaOut : RecordSchema)
    (hType : PatExprTyping ctx P GammaOut)
    (_hGraph : ctx.catalog.lookup ctx.graphSite = some G) :
    BTConforms (evalPattern G ctx.graphSite P) GammaOut := by
  -- Proved together with the strong runtime invariant, so the conjunction case can
  -- feed the left operand's strong invariant into the empty-former-meet vacuity.
  suffices h : BTConforms (evalPattern G ctx.graphSite P) GammaOut ∧
      (∀ rho, rho ∈ evalPattern G ctx.graphSite P → RuntimeConfigWFStrong G Psi rho GammaOut) from h.1
  induction hType with
  | single P Gamma v h =>
      refine ⟨patternTyping_sound ctx G hCat Psi hPsi hStrongFn
        .outside P Gamma v h, ?_⟩
      intro rho hrho
      exact hStrongFn .outside P Gamma v h rho hrho
  | conjunction P1 P2 Gamma1 Gamma2 v h1 h2 hjc ih1 =>
      have hS2 : ∀ rho, rho ∈ evalPattern G ctx.graphSite P2 → RuntimeConfigWFStrong G Psi rho Gamma2 :=
        fun rho hrho => hStrongFn .outside P2 Gamma2 v h2 rho hrho
      have hSound2 : BTConforms (evalPattern G ctx.graphSite P2) Gamma2 :=
        patternTyping_sound ctx G hCat Psi hPsi hStrongFn .outside P2 Gamma2 v h2
      rw [evalPattern_patternList]
      refine ⟨bindingTableJoin_conforms _ _ Gamma1 Gamma2
          (patExprTyping_schemaWF h1) ih1.1 hSound2 hjc
          (fun x t1 t2 hg1lk hg2lk hemp rho1 rho2 hrho1 hrho2 hag hadmt1 hadmt2 =>
            emptyFormerMeet_vacuous ctx G Psi (hCat Psi hPsi) h1 h2 ih1.2 hS2 ih1.1 hSound2
              x t1 t2 hg1lk hg2lk hemp rho1 rho2 hrho1 hrho2 hag hadmt1 hadmt2), ?_⟩
      intro rho hrho
      obtain ⟨rho1, hrho1, rho2, hrho2, hag, rfl⟩ := mem_bindingTableJoin hrho
      exact runtimeConfigWFStrong_join G Psi rho1 rho2 Gamma1 Gamma2
        (patExprTyping_schemaWF h1)
        (patternTyping_schemaWF h2)
        (ih1.1 rho1 hrho1).1 (hSound2 rho2 hrho2).1 hag
        (ih1.2 rho1 hrho1) (hS2 rho2 hrho2)

/-- Open-graph pattern soundness (P2). At an open site the schema-map has
    no entry, so the closed-world premises of `patternTyping_sound` -- the
    schema witness (`Psi`, `hPsi`), the graph-conformance assumption, and the
    strong runtime invariant (`hStrongFn`) -- all disappear. The graph
    conformance hypothesis threaded to the atom lemmas is rebuilt vacuously
    from `hOpen`, and the Pat-Step case goes through `step_conforms_open`. -/
theorem patternTyping_sound_open
    (ctx : TypingCtx) (G : PropertyGraph)
    (hOpen : ctx.schemaMap.isClosed ctx.graphSite = false) :
    ∀ (qd : QuantDepth) (P : Pattern) (Gamma : RecordSchema) (v : Name),
      PatternTyping ctx qd P Gamma v →
      BTConforms (evalPattern G ctx.graphSite P) Gamma := by
  have hCat : ∀ Psi', ctx.schemaMap.lookup ctx.graphSite = some Psi' →
      graphConformsSchema G Psi' = true := by
    intro Psi' hPsi'
    exfalso
    unfold SchemaMap.isClosed at hOpen
    rw [hPsi'] at hOpen
    exact Bool.noConfusion hOpen
  intro qd P Gamma v h
  induction h with
  | patNode qd na GammaA hAtom =>
      exact patternSound_node ctx G na GammaA hAtom hCat
  | patEdge qd n1 n2 rel dir GammaN1 GammaE GammaN2 GammaRef hSingleD hAtomN1 hAtomE hAtomN2 hRef =>
      exact patternSound_edge_single ctx G n1 n2 rel dir GammaN1 GammaE GammaN2 GammaRef
        hSingleD hAtomN1 hAtomE hAtomN2 hRef hCat
  | patStep qd P rel dir n2 Gamma1 GammaE GammaN2 GammaRef v1 hSingle hPrefix hAtomE hAtomN2 hRef ihPrefix =>
      exact step_conforms_open ctx G hOpen P rel dir n2 Gamma1 GammaE GammaN2 GammaRef v1
        hSingle (patternTyping_tailVar hPrefix) ihPrefix
        (patternTyping_schemaWF hPrefix)
        hAtomE hAtomN2 hRef
  | patQuantEdge n1 n2 rel dir K GammaE hQuant hAtomE hNE12 hNE23 =>
      obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
      exact evalPattern_quantEdge_conforms_edgeSort G ctx.graphSite n1 n2
        { rel with quantifier := K } dir TE hQuant hNE12 hNE23
  | patOptEdge n1 n2 rel dir hNE12 hNE23 =>
      exact evalPattern_optEdge_conforms_open G ctx.graphSite n1 n2 rel dir hNE12 hNE23
  | patQuantPath P K GammaInner v hInner hQuant ihInner =>
      obtain ⟨lv, hlv⟩ := patternLeadVar_isSome P
      obtain ⟨tv, htv⟩ := patternTailVar_isSome P
      have hvars := patternTyping_vars_mem hInner
      have hinner : ∀ z, GammaInner.dom.any (fun w => w == z)
          = (patternVars P).any (fun w => w == z) := by
        intro z
        rw [hvars z]
        exact RecordSchema.dom_any_mem GammaInner z
      show BTConforms (evalPattern G ctx.graphSite (.quantified P K))
        (GammaInner.liftToGroupRef GammaInner.dom)
      simp only [evalPattern, hlv, htv]
      exact evalQuantified_btconforms (patternVars P) (evalPattern G ctx.graphSite P) lv tv K.lo _
        GammaInner GammaInner.dom hvars hinner
  | patGrouped qd P Gamma v hP ih =>
      rw [evalPattern_grouped]
      exact ih

/- Open-graph pattern-expression soundness (Theorem 6.2 for open sites,
    The open-site counterpart of `patExprSoundness'`: no
    schema witness, no graph-conformance premise, no strong runtime
    invariant -- an open site carries none of that structure. -/
-- (`patExprSoundness_open` moved below `patExprTyping_openSorts`, since the
--  kind-aware join flip's empty-former-meet discharge needs `SchemaOpen` and
--  `openSort_sortInter_not_emptyFormer`, both defined later.)

-- ============================================================
--  Open sites, runtime invariant (P2, query layer): open pattern outputs
--  carry only graph-indexed identity sorts (possibly list-lifted), never a
--  schema-refined sort, so `RuntimeConfigWF` holds vacuously.
-- ============================================================

/-- The sorts an open-site pattern can assign: the node and edge identity
    sorts of the site, closed under list lifting (quantifier grouping). -/
inductive OpenSort (site : GraphSite) : GSort -> Prop where
  | node : OpenSort site (GSort.nodeOf site)
  | edge : OpenSort site (GSort.edgeOf site)
  | lift {t : GSort} : OpenSort site t -> OpenSort site t.liftToList

/-- Where `sortInter` can land, without computing the branch conditions:
    one of the operands, a same-shape re-tagging, bottom, an empty former,
    or a branch that presupposes a schema-refined operand shape. -/
private theorem sortInter_cases (t1 t2 : GSort) :
    RecordSchema.sortInter t1 t2 = t1 ∨
    RecordSchema.sortInter t1 t2 = t2 ∨
    (RecordSchema.sortInter t1 t2
        = GSort.mk t1.shape (RecordSchema.tighterNull t1.null t2.null)
      ∧ (t1.shape == t2.shape) = true) ∨
    (RecordSchema.sortInter t1 t2).isBot = true ∨
    (RecordSchema.sortInter t1 t2).isEmptyFormer = true ∨
    (∃ s ss, t1.shape = .single (.nodeRefined s ss)) ∨
    (∃ s ss, t1.shape = .single (.edgeRefined s ss)) ∨
    (∃ s ss, t2.shape = .single (.nodeRefined s ss)) ∨
    (∃ s ss, t2.shape = .single (.edgeRefined s ss)) := by
  unfold RecordSchema.sortInter
  split
  · exact Or.inl rfl
  split
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · split
    · rename_i hsb
      exact Or.inr (Or.inr (Or.inl ⟨rfl, hsb⟩))
    · split
      · rename_i heq1 heq2
        repeat' split
        all_goals exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, heq1⟩)))))
      · rename_i heq1 heq2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, heq1⟩)))))
      · rename_i heq1 heq2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, heq2⟩)))))))
      · rename_i heq1 heq2
        repeat' split
        all_goals exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, heq1⟩))))))
      · rename_i heq1 heq2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, heq1⟩))))))
      · rename_i heq1 heq2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, heq2⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

/-- An open sort's meet with another open sort, when neither bottom nor an
    empty former, is again an open sort. -/
private theorem sortInter_openSort {site : GraphSite} {t1 t2 : GSort}
    (h1 : OpenSort site t1) (h2 : OpenSort site t2)
    (hbot : (RecordSchema.sortInter t1 t2).isBot = false)
    (hemp : (RecordSchema.sortInter t1 t2).isEmptyFormer = false) :
    OpenSort site (RecordSchema.sortInter t1 t2) := by
  rcases sortInter_cases t1 t2 with
    h | h | ⟨h, hsb⟩ | h | h | ⟨s, ss, h⟩ | ⟨s, ss, h⟩ | ⟨s, ss, h⟩ | ⟨s, ss, h⟩
  · rw [h]; exact h1
  · rw [h]; exact h2
  · cases h1 with
    | node =>
      cases h2 with
      | node => rw [h]; exact .node
      | edge => exact Bool.noConfusion hsb
      | lift _ => exact Bool.noConfusion hsb
    | edge =>
      cases h2 with
      | node => exact Bool.noConfusion hsb
      | edge => rw [h]; exact .edge
      | lift _ => exact Bool.noConfusion hsb
    | lift ha =>
      cases h2 with
      | node => exact Bool.noConfusion hsb
      | edge => exact Bool.noConfusion hsb
      | lift hb => rw [h]; exact .lift ha
  · exact Bool.noConfusion (h.symm.trans hbot)
  · exact Bool.noConfusion (h.symm.trans hemp)
  · cases h1 with
    | node => injection h with h'; exact ExtSort.noConfusion h'
    | edge => injection h with h'; exact ExtSort.noConfusion h'
    | lift _ => exact SortShape.noConfusion h
  · cases h1 with
    | node => injection h with h'; exact ExtSort.noConfusion h'
    | edge => injection h with h'; exact ExtSort.noConfusion h'
    | lift _ => exact SortShape.noConfusion h
  · cases h2 with
    | node => injection h with h'; exact ExtSort.noConfusion h'
    | edge => injection h with h'; exact ExtSort.noConfusion h'
    | lift _ => exact SortShape.noConfusion h
  · cases h2 with
    | node => injection h with h'; exact ExtSort.noConfusion h'
    | edge => injection h with h'; exact ExtSort.noConfusion h'
    | lift _ => exact SortShape.noConfusion h

/-- Open sorts are never schema-refined, at any component depth. -/
private theorem openSort_component_unrefined {site : GraphSite} {t : GSort}
    (h : OpenSort site t) :
    (∀ s ss, t.componentType ≠ GSort.nodeRefinedOf s ss) ∧
    (∀ s ss, t.componentType ≠ GSort.edgeRefinedOf s ss) := by
  cases h with
  | node =>
    constructor <;> intro s ss heq <;>
      (injection heq with h1 _; injection h1 with h2; exact ExtSort.noConfusion h2)
  | edge =>
    constructor <;> intro s ss heq <;>
      (injection heq with h1 _; injection h1 with h2; exact ExtSort.noConfusion h2)
  | lift ht =>
    rename_i t0
    have hcomp : (t0.liftToList).componentType = t0 := rfl
    rw [hcomp]
    constructor <;> intro s ss heq <;>
      (cases ht with
        | node => injection heq with h1 _; injection h1 with h2; exact ExtSort.noConfusion h2
        | edge => injection heq with h1 _; injection h1 with h2; exact ExtSort.noConfusion h2
        | lift _ => injection heq with h1 _; exact SortShape.noConfusion h1)

/-- Open sorts are not empty formers. -/
private theorem openSort_not_emptyFormer {site : GraphSite} {t : GSort}
    (h : OpenSort site t) : t.isEmptyFormer = false := by
  cases h <;> rfl

private theorem isBot_not_emptyFormer {t : GSort} (h : t.isBot = true) :
    t.isEmptyFormer = false := by
  obtain ⟨sh, nl⟩ := t
  cases sh <;> first | rfl | exact Bool.noConfusion h

/-- The meet of two open sorts is never an empty former: open sorts have node,
    edge, or list shapes, none of which drive `sortInter` into an
    empty-former (which needs a refined or already-empty-former operand). -/
private theorem openSort_sortInter_not_emptyFormer {site : GraphSite} {t1 t2 : GSort}
    (h1 : OpenSort site t1) (h2 : OpenSort site t2) :
    (RecordSchema.sortInter t1 t2).isEmptyFormer = false := by
  -- Every open sort has a node/edge/list shape; classify and compute.
  have shape_of : ∀ {t : GSort}, OpenSort site t →
      (t = GSort.nodeOf site) ∨ (t = GSort.edgeOf site) ∨ (∃ s n, t = GSort.mk (.list s n) .val) := by
    intro t h
    cases h with
    | node => exact Or.inl rfl
    | edge => exact Or.inr (Or.inl rfl)
    | lift ht => exact Or.inr (Or.inr ⟨_, _, rfl⟩)
  rcases shape_of h1 with rfl | rfl | ⟨s1, n1, rfl⟩ <;>
    rcases shape_of h2 with rfl | rfl | ⟨s2, n2, rfl⟩ <;>
    simp only [RecordSchema.sortInter, GSort.nodeOf, GSort.edgeOf] <;>
    repeat' first | rfl | split

/-- All entries of a schema are open sorts. -/
def SchemaOpen (site : GraphSite) (Gamma : RecordSchema) : Prop :=
  ∀ x t, (x, t) ∈ Gamma.entries → OpenSort site t

private theorem schemaOpen_singleton_node (site : GraphSite) (v : Name) :
    SchemaOpen site (RecordSchema.mk [(v, GSort.nodeOf site)]) := by
  intro x t hxt
  cases hxt with
  | head => exact .node
  | tail _ h => exact absurd h (List.not_mem_nil _)

private theorem schemaOpen_singleton_edge (site : GraphSite) (v : Name) :
    SchemaOpen site (RecordSchema.mk [(v, GSort.edgeOf site)]) := by
  intro x t hxt
  cases hxt with
  | head => exact .edge
  | tail _ h => exact absurd h (List.not_mem_nil _)

/-- Join preserves open sorts (meets certified by join compatibility). -/
private theorem schemaOpen_join {site : GraphSite} {A B : RecordSchema}
    (hwfA : SchemaWF A)
    (hA : SchemaOpen site A) (hB : SchemaOpen site B)
    (hjc : A.joinCompatible B = true) :
    SchemaOpen site (A.join B) := by
  intro x t hxt
  rcases RecordSchema.join_entry_cases hxt with
    ⟨t1, hA1, _, rfl⟩ | ⟨t1, t2, hA1, hB2, rfl⟩ | ⟨t2, hB2, _, rfl⟩
  · exact hA _ _ hA1
  · obtain ⟨hbot, _⟩ :=
      RecordSchema.joinCompatible_meet hjc (hwfA x t1 hA1) hB2
    exact sortInter_openSort (hA _ _ hA1)
      (hB _ _ (RecordSchema.lookup_some_mem hB2)) hbot
      (openSort_sortInter_not_emptyFormer (hA _ _ hA1)
        (hB _ _ (RecordSchema.lookup_some_mem hB2)))
  · exact hB _ _ hB2

/-- Group-reference lifting preserves open sorts. -/
private theorem schemaOpen_lift {site : GraphSite} {Gamma : RecordSchema}
    {vars : List Name} (h : SchemaOpen site Gamma) :
    SchemaOpen site (Gamma.liftToGroupRef vars) := by
  intro x t hxt
  obtain ⟨t0, ht0, ht⟩ := RecordSchema.mem_liftToGroupRef_entries hxt
  rw [ht]
  split
  · exact .lift (h _ _ ht0)
  · exact h _ _ ht0

/-- Open-sortedness of the three-way refinement join at an open site: a
    generic open-sorted left schema joined with the edge and target-node
    identity singletons. Meets with the edge singleton are certified by
    `hJC12`, meets with the target singleton by `hJC13`, and the two
    singletons are key-disjoint because their sorts meet at bottom. -/
private theorem schemaOpen_openJoin3 {site : GraphSite} {A : RecordSchema}
    {ev nv : Name}
    (hwfA : SchemaWF A) (hA : SchemaOpen site A)
    (hJC12 : A.joinCompatible (RecordSchema.mk [(ev, GSort.edgeOf site)]) = true)
    (hJC23 : (RecordSchema.mk [(ev, GSort.edgeOf site)]).joinCompatible
        (RecordSchema.mk [(nv, GSort.nodeOf site)]) = true)
    (hJC13 : A.joinCompatible (RecordSchema.mk [(nv, GSort.nodeOf site)]) = true) :
    SchemaOpen site ((A.join (RecordSchema.mk [(ev, GSort.edgeOf site)])).join
      (RecordSchema.mk [(nv, GSort.nodeOf site)])) := by
  have d_ne : (nv == ev) = false :=
    joinCompatible_singleton_distinct ev nv _ _
      (sortInter_edgeOf_nodeOf_isBot site) hJC23
  intro x t hxt
  rcases RecordSchema.join_entry_cases hxt with
    ⟨t1, hin, _, rfl⟩ | ⟨t1, t2, hin, hClk, rfl⟩ | ⟨t2, hent, _, rfl⟩
  · rcases RecordSchema.join_entry_cases hin with
      ⟨tA, hAe, _, rfl⟩ | ⟨tA, tB, hAe, hBlk, rfl⟩ | ⟨tB, hBe, _, rfl⟩
    · exact hA _ _ hAe
    · have hBlk0 := hBlk
      rw [singleton_schema_lookup] at hBlk
      cases hb : ev == x with
      | false => rw [hb] at hBlk; exact absurd hBlk (by simp)
      | true =>
        rw [hb] at hBlk
        have htB : tB = GSort.edgeOf site := (Option.some.inj hBlk).symm
        subst htB
        obtain ⟨hbot, _⟩ :=
          RecordSchema.joinCompatible_meet hJC12 (hwfA _ _ hAe) hBlk0
        exact sortInter_openSort (hA _ _ hAe) .edge hbot
          (openSort_sortInter_not_emptyFormer (hA _ _ hAe) .edge)
    · have := (Prod.mk.injEq .. ▸ (List.mem_singleton.mp hBe)).2
      subst this; exact .edge
  · have hClk0 := hClk
    rw [singleton_schema_lookup] at hClk
    cases hb : nv == x with
    | false => rw [hb] at hClk; exact absurd hClk (by simp)
    | true =>
      rw [hb] at hClk
      have ht2 : t2 = GSort.nodeOf site := (Option.some.inj hClk).symm
      subst ht2
      rcases RecordSchema.join_entry_cases hin with
        ⟨tA, hAe, _, rfl⟩ | ⟨_, _, hAe, hBlk, _⟩ | ⟨tB, hBe, _, rfl⟩
      · obtain ⟨hbot, _⟩ :=
          RecordSchema.joinCompatible_meet hJC13 (hwfA _ _ hAe) hClk0
        exact sortInter_openSort (hA _ _ hAe) .node hbot
          (openSort_sortInter_not_emptyFormer (hA _ _ hAe) .node)
      · exfalso
        -- The inner meet's right component is the edge-singleton lookup at
        -- x, which forces x = ev; combined with nv == x this contradicts
        -- the key-disjointness d_ne.
        rw [singleton_schema_lookup] at hBlk
        cases hbe : ev == x with
        | false => rw [hbe] at hBlk; exact absurd hBlk (by simp)
        | true =>
          have : nv = x := eq_of_beq hb
          subst this
          rw [name_beq_comm] at hbe
          rw [hbe] at d_ne; exact Bool.noConfusion d_ne
      · exfalso
        have hxe := (Prod.mk.injEq .. ▸ (List.mem_singleton.mp hBe)).1
        subst hxe
        rw [hb] at d_ne; exact Bool.noConfusion d_ne
  · have := (Prod.mk.injEq .. ▸ (List.mem_singleton.mp hent)).2
    subst this; exact .node

/-- Open pattern outputs are open-sorted. By induction on the pattern
    typing at an open site: atoms give the identity sorts, refinement joins
    are certified by join compatibility, closed rules contradict openness or
    the induction hypothesis, and quantifiers lift. -/
theorem patternTyping_openSorts
    (ctx : TypingCtx)
    (hOpen : ctx.schemaMap.isClosed ctx.graphSite = false) :
    ∀ (qd : QuantDepth) (P : Pattern) (Gamma : RecordSchema) (v : Name),
      PatternTyping ctx qd P Gamma v →
      SchemaOpen ctx.graphSite Gamma := by
  intro qd P Gamma v h
  induction h with
  | patNode qd na GammaA hAtom =>
    cases hAtom with
    | nodeOpen _ _ _ _ => exact schemaOpen_singleton_node _ _
    | nodeClosed _ _ _ _ _ _ _ _ hClosed _ _ _ _ _ _ =>
      rw [hOpen] at hClosed; exact Bool.noConfusion hClosed
    | nodeClosedFail _ _ _ _ _ _ _ hClosed _ _ _ _ =>
      rw [hOpen] at hClosed; exact Bool.noConfusion hClosed
  | patEdge qd n1 n2 rel dir GammaN1 GammaE GammaN2 GammaRef hSingleD hAtomN1 hAtomE hAtomN2 hRef =>
    have hN1open : SchemaOpen ctx.graphSite GammaN1 := by
      cases hAtomN1 with
      | nodeOpen _ _ _ _ => exact schemaOpen_singleton_node _ _
      | nodeClosed _ _ _ _ _ _ _ _ hClosed _ _ _ _ _ _ =>
        rw [hOpen] at hClosed; exact Bool.noConfusion hClosed
      | nodeClosedFail _ _ _ _ _ _ _ hClosed _ _ _ _ =>
        rw [hOpen] at hClosed; exact Bool.noConfusion hClosed
    have hEopen : SchemaOpen ctx.graphSite GammaE := by
      cases hAtomE with
      | edgeOpen _ _ _ _ => exact schemaOpen_singleton_edge _ _
      | edgeClosed _ _ _ _ _ _ _ _ hClosed _ _ _ _ _ _ =>
        rw [hOpen] at hClosed; exact Bool.noConfusion hClosed
      | edgeClosedFail _ _ _ _ _ _ _ hClosed _ _ _ _ =>
        rw [hOpen] at hClosed; exact Bool.noConfusion hClosed
    have hN2open : SchemaOpen ctx.graphSite GammaN2 := by
      cases hAtomN2 with
      | nodeOpen _ _ _ _ => exact schemaOpen_singleton_node _ _
      | nodeClosed _ _ _ _ _ _ _ _ hClosed _ _ _ _ _ _ =>
        rw [hOpen] at hClosed; exact Bool.noConfusion hClosed
      | nodeClosedFail _ _ _ _ _ _ _ hClosed _ _ _ _ =>
        rw [hOpen] at hClosed; exact Bool.noConfusion hClosed
    cases hRef with
    | open_ hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 =>
      obtain ⟨T1, rfl⟩ := atomTyping_node_singleton hAtomN1
      obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
      obtain ⟨T2, rfl⟩ := atomTyping_node_singleton hAtomN2
      have hTEeq : TE = GSort.edgeOf ctx.graphSite := by
        have h := hEdge2; rw [singleton_schema_lookup] at h; simpa using h
      have hT2eq : T2 = GSort.nodeOf ctx.graphSite := by
        have h := hNode3; rw [singleton_schema_lookup] at h; simpa using h
      subst hTEeq; subst hT2eq
      exact schemaOpen_openJoin3 (RecordSchema.singleton_schemaWF _ _)
        hN1open hJC12 hJC23 hJC13
    | closed sN1 sE2 sN3 _ _ _ hNode1 hEdge2 hNode3 _ _ _ _ _ _ _ =>
      exact absurd (hEopen _ _ (RecordSchema.lookup_some_mem hEdge2))
        (fun hop => by cases hop)
    | closedEmpty hJC12 hJC23 hJC13 hSomeEmpty =>
      exfalso
      rcases hSomeEmpty with h1 | h2 | h3
      · cases hg : GammaN1.lookup n1.var with
        | none => rw [hg] at h1; exact Bool.noConfusion h1
        | some t =>
          rw [hg] at h1
          have h1' : t.isEmptyFormer = true := h1
          rw [openSort_not_emptyFormer
            (hN1open _ _ (RecordSchema.lookup_some_mem hg))] at h1'
          exact Bool.noConfusion h1'
      · cases hg : GammaE.lookup rel.var with
        | none => rw [hg] at h2; exact Bool.noConfusion h2
        | some t =>
          rw [hg] at h2
          have h2' : t.isEmptyFormer = true := h2
          rw [openSort_not_emptyFormer
            (hEopen _ _ (RecordSchema.lookup_some_mem hg))] at h2'
          exact Bool.noConfusion h2'
      · cases hg : GammaN2.lookup n2.var with
        | none => rw [hg] at h3; exact Bool.noConfusion h3
        | some t =>
          rw [hg] at h3
          have h3' : t.isEmptyFormer = true := h3
          rw [openSort_not_emptyFormer
            (hN2open _ _ (RecordSchema.lookup_some_mem hg))] at h3'
          exact Bool.noConfusion h3'
    | closedFail sN1 sE2 sN3 hNode1 hEdge2 hNode3 _ _ _ _ =>
      exact absurd (hEopen _ _ (RecordSchema.lookup_some_mem hEdge2))
        (fun hop => by cases hop)
  | patStep qd P rel dir n2 Gamma1 GammaE GammaN2 GammaRef v1 hSingle hPrefix hAtomE hAtomN2 hRef ihPrefix =>
    have hG1open : SchemaOpen ctx.graphSite Gamma1 := ihPrefix
    have hEopen : SchemaOpen ctx.graphSite GammaE := by
      cases hAtomE with
      | edgeOpen _ _ _ _ => exact schemaOpen_singleton_edge _ _
      | edgeClosed _ _ _ _ _ _ _ _ hClosed _ _ _ _ _ _ =>
        rw [hOpen] at hClosed; exact Bool.noConfusion hClosed
      | edgeClosedFail _ _ _ _ _ _ _ hClosed _ _ _ _ =>
        rw [hOpen] at hClosed; exact Bool.noConfusion hClosed
    have hN2open : SchemaOpen ctx.graphSite GammaN2 := by
      cases hAtomN2 with
      | nodeOpen _ _ _ _ => exact schemaOpen_singleton_node _ _
      | nodeClosed _ _ _ _ _ _ _ _ hClosed _ _ _ _ _ _ =>
        rw [hOpen] at hClosed; exact Bool.noConfusion hClosed
      | nodeClosedFail _ _ _ _ _ _ _ hClosed _ _ _ _ =>
        rw [hOpen] at hClosed; exact Bool.noConfusion hClosed
    have hwfG1 : SchemaWF Gamma1 := patternTyping_schemaWF hPrefix
    cases hRef with
    | open_ hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 =>
      obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
      obtain ⟨T2, rfl⟩ := atomTyping_node_singleton hAtomN2
      have hTEeq : TE = GSort.edgeOf ctx.graphSite := by
        have h := hEdge2; rw [singleton_schema_lookup] at h; simpa using h
      have hT2eq : T2 = GSort.nodeOf ctx.graphSite := by
        have h := hNode3; rw [singleton_schema_lookup] at h; simpa using h
      subst hTEeq; subst hT2eq
      exact schemaOpen_openJoin3 hwfG1 hG1open hJC12 hJC23 hJC13
    | closed sN1 sE2 sN3 _ _ _ hNode1 hEdge2 hNode3 _ _ _ _ _ _ _ =>
      exact absurd (hG1open _ _ (RecordSchema.lookup_some_mem hNode1))
        (fun hop => by cases hop)
    | closedEmpty hJC12 hJC23 hJC13 hSomeEmpty =>
      exfalso
      rcases hSomeEmpty with h1 | h2 | h3
      · cases hg : Gamma1.lookup v1 with
        | none => rw [hg] at h1; exact Bool.noConfusion h1
        | some t =>
          rw [hg] at h1
          have h1' : t.isEmptyFormer = true := h1
          rw [openSort_not_emptyFormer
            (hG1open _ _ (RecordSchema.lookup_some_mem hg))] at h1'
          exact Bool.noConfusion h1'
      · cases hg : GammaE.lookup rel.var with
        | none => rw [hg] at h2; exact Bool.noConfusion h2
        | some t =>
          rw [hg] at h2
          have h2' : t.isEmptyFormer = true := h2
          rw [openSort_not_emptyFormer
            (hEopen _ _ (RecordSchema.lookup_some_mem hg))] at h2'
          exact Bool.noConfusion h2'
      · cases hg : GammaN2.lookup n2.var with
        | none => rw [hg] at h3; exact Bool.noConfusion h3
        | some t =>
          rw [hg] at h3
          have h3' : t.isEmptyFormer = true := h3
          rw [openSort_not_emptyFormer
            (hN2open _ _ (RecordSchema.lookup_some_mem hg))] at h3'
          exact Bool.noConfusion h3'
    | closedFail sN1 sE2 sN3 hNode1 hEdge2 hNode3 _ _ _ _ =>
      exact absurd (hG1open _ _ (RecordSchema.lookup_some_mem hNode1))
        (fun hop => by cases hop)
  | patQuantEdge n1 n2 rel dir K GammaE hQuant hAtomE hNE12 hNE23 =>
    intro x t hxt
    cases hAtomE with
    | edgeClosed _ _ _ _ _ _ _ _ hClosed _ _ _ _ _ =>
        rw [hOpen] at hClosed; exact Bool.noConfusion hClosed
    | edgeClosedFail _ _ _ _ _ _ _ hClosed _ _ _ _ _ =>
        rw [hOpen] at hClosed; exact Bool.noConfusion hClosed
    | edgeOpen _ _ _ _ =>
      obtain ⟨t0, ht0, ht⟩ := RecordSchema.mem_liftToGroupRef_entries hxt
      have hopen0 : OpenSort ctx.graphSite t0 := by
        rcases open_join_entry_is_nodeOf_or_edgeOf ctx.graphSite n1 n2 rel
          (GSort.edgeOf ctx.graphSite) hNE12 hNE23 x t0 ht0 with h | ⟨_, h⟩
        · rw [h]; exact .node
        · rw [h]; exact .edge
      rw [ht]
      split
      · exact .lift hopen0
      · exact hopen0
  | patOptEdge n1 n2 rel dir hNE12 hNE23 =>
    intro x t hxt
    obtain ⟨t0, ht0, ht⟩ := RecordSchema.mem_liftToNullable_entries hxt
    rw [ht]
    split
    · rcases open_join_entry_is_nodeOf_or_edgeOf ctx.graphSite n1 n2 rel
        (GSort.edgeOf ctx.graphSite) hNE12 hNE23 x t0 ht0 with h | ⟨_, h⟩
      · rw [h]; exact .node
      · rw [h]; exact .edge
    · rcases open_join_entry_is_nodeOf_or_edgeOf ctx.graphSite n1 n2 rel
        (GSort.edgeOf ctx.graphSite) hNE12 hNE23 x t0 ht0 with h | ⟨_, h⟩
      · rw [h]; exact .node
      · rw [h]; exact .edge
  | patQuantPath P K GammaInner v hInner hQuant ihInner =>
    exact schemaOpen_lift ihInner
  | patGrouped qd P Gamma v hP ih =>
    exact ih

/-- Open pattern-expression outputs are open-sorted. -/
theorem patExprTyping_openSorts
    (ctx : TypingCtx)
    (hOpen : ctx.schemaMap.isClosed ctx.graphSite = false)
    {P : Pattern} {Gamma : RecordSchema}
    (hType : PatExprTyping ctx P Gamma) :
    SchemaOpen ctx.graphSite Gamma := by
  induction hType with
  | single P Gamma v h =>
    exact patternTyping_openSorts ctx hOpen .outside P Gamma v h
  | conjunction P1 P2 Gamma1 Gamma2 v h1 h2 hjc ih1 =>
    exact schemaOpen_join (patExprTyping_schemaWF h1)
      ih1
      (patternTyping_openSorts ctx hOpen .outside P2 Gamma2 v h2)
      hjc

/-- Pattern-expression soundness at an OPEN site. Placed after the open-sort
    machinery: the kind-aware join flip's empty-former-meet discharge is vacuous
    here because both operand types are open sorts, whose meet is never an empty
    type former (`openSort_sortInter_not_emptyFormer`). -/
theorem patExprSoundness_open
    (ctx : TypingCtx) (G : PropertyGraph)
    (hOpen : ctx.schemaMap.isClosed ctx.graphSite = false)
    (P : Pattern) (GammaOut : RecordSchema)
    (hType : PatExprTyping ctx P GammaOut) :
    BTConforms (evalPattern G ctx.graphSite P) GammaOut := by
  induction hType with
  | single P Gamma v h =>
      exact patternTyping_sound_open ctx G hOpen
        .outside P Gamma v h
  | conjunction P1 P2 Gamma1 Gamma2 v h1 h2 hjc ih1 =>
      rw [evalPattern_patternList]
      have hO1 : SchemaOpen ctx.graphSite Gamma1 := patExprTyping_openSorts ctx hOpen h1
      have hO2 : SchemaOpen ctx.graphSite Gamma2 :=
        patternTyping_openSorts ctx hOpen .outside P2 Gamma2 v h2
      exact bindingTableJoin_conforms _ _ Gamma1 Gamma2
        (patExprTyping_schemaWF h1) ih1
        (patternTyping_sound_open ctx G hOpen
          .outside P2 Gamma2 v h2)
        hjc
        (fun x t1 t2 hg1lk hg2lk hemp _ _ _ _ _ _ _ => by
          rw [openSort_sortInter_not_emptyFormer
              (hO1 x t1 (RecordSchema.lookup_some_mem hg1lk))
              (hO2 x t2 (RecordSchema.lookup_some_mem hg2lk))] at hemp
          exact Bool.noConfusion hemp)

/-- Open runtime well-formedness (P2, query layer). At an open site the
    output schema is open-sorted, so the runtime-configuration invariant --
    which only constrains schema-refined component sorts -- holds vacuously
    for every record. -/
theorem patExpr_runtimeWF_open
    (ctx : TypingCtx) (G : PropertyGraph)
    (hOpen : ctx.schemaMap.isClosed ctx.graphSite = false)
    {P : Pattern} {GammaOut : RecordSchema}
    (hType : PatExprTyping ctx P GammaOut)
    (rho : Record) :
    RuntimeConfigWF G rho GammaOut := by
  intro x t hlk
  have hop := patExprTyping_openSorts ctx hOpen hType x t
    (RecordSchema.lookup_some_mem hlk)
  obtain ⟨hnode, hedge⟩ := openSort_component_unrefined hop
  constructor
  · intro site ss hct
    exact absurd hct (hnode site ss)
  · intro site ss hct
    exact absurd hct (hedge site ss)

-- (Removed: `atomNode_edge_botOrEmpty`/`atomEdge_node_botOrEmpty`/
--  `singleton_atoms_distinct` -- dead scaffolding obsoleted by the kind-aware
--  join-compatibility flip. Same-kind empty-former meets are now accepted, so
--  distinctness no longer follows from a bot-or-empty meet; where needed it
--  follows from `sameKind = false` via `joinCompatible_meet`.)

private theorem refinementTyping_joinCompat12 {ctx : TypingCtx} {G1 G2 G3 : RecordSchema}
    {v1 r2 v3 : Name} {dir : Direction} {GammaRef : RecordSchema}
    (h : RefinementTyping ctx G1 G2 G3 v1 r2 v3 dir GammaRef) : G1.joinCompatible G2 = true := by
  cases h <;> assumption

private theorem refinementTyping_joinCompat23 {ctx : TypingCtx} {G1 G2 G3 : RecordSchema}
    {v1 r2 v3 : Name} {dir : Direction} {GammaRef : RecordSchema}
    (h : RefinementTyping ctx G1 G2 G3 v1 r2 v3 dir GammaRef) : G2.joinCompatible G3 = true := by
  cases h <;> assumption

/-- Record/schema domain agreement. Every record produced by `evalPattern P`
    has exactly the typed schema's domain. Combines `evalBindsPatternVars` (the
    record binds `patternVars P`) with `patternTyping_vars_mem` (the schema's domain
    is `patternVars P`). This is the prefix-domain fact `step_runtimeWFStrong` needs. -/
theorem patternEvalDom (ctx : TypingCtx) (G : PropertyGraph)
    (qd : QuantDepth) (P : Pattern) (Gamma : RecordSchema) (v : Name)
    (h : PatternTyping ctx qd P Gamma v)
    (rho : Record) (hrho : rho ∈ evalPattern G ctx.graphSite P) (z : Name) :
    rho.mem z = Gamma.mem z := by
  rw [evalBindsPatternVars ctx G qd P Gamma v h rho hrho z]
  exact patternTyping_vars_mem h z

/-- Strong graph-aware step soundness (discharges `hStepStrong`). The step's
    source schema set `sN1` comes from the prefix's strong well-formedness (not a
    source atom), the edge/destination sets from the edge/destination atoms;
    combined they discharge the three refined endpoint memberships exactly as
    `matchSingleEdge_runtimeWFStrong` does for a single edge, with the
    natural-equijoin agreement transporting the prefix's tail binding to the
    matched source. -/
theorem step_runtimeWFStrong
    (ctx : TypingCtx) (G : PropertyGraph) (Psi : GraphSchemaFull)
    (hPsi : ctx.schemaMap.lookup ctx.graphSite = some Psi)
    (hCat : ∀ Psi', ctx.schemaMap.lookup ctx.graphSite = some Psi' →
              graphConformsSchema G Psi' = true)
    (P : Pattern) (rel : EdgeAtom) (dir : Direction) (n2 : NodeAtom)
    (Gamma1 GammaE GammaN2 GammaRef : RecordSchema) (v1 : Name)
    (hSingle : rel.quantifier = .single)
    (htv : patternTailVar P = some v1)
    (hPrefixWF : SchemaWF Gamma1)
    (hPrefixDom : ∀ rho, rho ∈ evalPattern G ctx.graphSite P → ∀ x, rho.mem x = Gamma1.mem x)
    (hPrefixStrong : ∀ rho, rho ∈ evalPattern G ctx.graphSite P →
        RuntimeConfigWFStrong G Psi rho Gamma1)
    (hAtomE : AtomTyping ctx (.edge { var := rel.var, labels := rel.labels, props := rel.props }) GammaE)
    (hAtomN2 : AtomTyping ctx (.node n2) GammaN2)
    (hRef : RefinementTyping ctx Gamma1 GammaE GammaN2 v1 rel.var n2.var dir GammaRef) :
    ∀ rho_out, rho_out ∈ evalPattern G ctx.graphSite (.step P rel dir n2) →
      RuntimeConfigWFStrong G Psi rho_out GammaRef := by
  intro rho_out hmem
  obtain ⟨rho, rhoEdge, hrho, hedge, hStepAgree, ⟨gv, srcN0, hrhov1⟩, rfl⟩ :=
    evalPattern_step_single_mem G ctx.graphSite P rel dir n2 v1 hSingle htv rho_out hmem
  obtain ⟨T2, rfl⟩ := atomTyping_node_singleton hAtomN2
  obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
  have hrelEq : ({ rel with quantifier := .single } : EdgeAtom) = rel := by
    cases rel with | mk v l p q => cases hSingle; rfl
  rw [hrelEq] at hedge
  have hpre := hPrefixStrong rho hrho
  obtain ⟨srcN, ei, dstN, hsrcN, hei, hdstN, hsrcLbl, hsrcPrp, hlblE, hprpE,
          hlblD, hprpD, hphi, hsd, hform⟩ := matchSingleEdge_mem_form' hedge
  have hv1memE : rhoEdge.mem v1 = true := by rw [hform]; simp [Record.mem]
  have hrhoEdge_v1 : rhoEdge.lookup v1 = Value.nodeRef ctx.graphSite srcN := by
    rw [hform]; simp [Record.lookup, List.find?_cons]
  have hv1memRho : rho.mem v1 = true := by
    cases hm : rho.mem v1 with
    | true => rfl
    | false =>
      exfalso
      have hnone : rho.find? (fun e => e.1 == v1) = none := by
        rw [List.find?_eq_none]; intro y hy hpy
        have hany : rho.any (fun e => e.1 == v1) = true := List.any_eq_true.mpr ⟨y, hy, hpy⟩
        rw [show rho.any (fun e => e.1 == v1) = rho.mem v1 from rfl, hm] at hany
        exact Bool.noConfusion hany
      have hlknull : rho.lookup v1 = Value.null := by
        show (match rho.find? (fun e => e.1 == v1) with | some (_, v) => v | none => Value.null) = Value.null
        rw [hnone]
      rw [hlknull] at hrhov1; exact Value.noConfusion hrhov1
  have hrho_src : rho.lookup v1 = Value.nodeRef ctx.graphSite srcN :=
    (Record.agreeOn_lookup_eq rho rhoEdge v1 hStepAgree hv1memRho hv1memE).trans hrhoEdge_v1
  have hwfGE : SchemaWF (RecordSchema.mk [(rel.var, TE)]) := RecordSchema.singleton_schemaWF _ _
  have hwfGN : SchemaWF (RecordSchema.mk [(n2.var, T2)]) := RecordSchema.singleton_schemaWF _ _
  cases hRef with
  | open_ hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 =>
    have hpredom := hPrefixDom rho hrho
    have hTEeq : TE = GSort.edgeOf ctx.graphSite := by
      have h := hEdge2; rw [singleton_schema_lookup] at h; simpa using h
    have hT2eq : T2 = GSort.nodeOf ctx.graphSite := by
      have h := hNode3; rw [singleton_schema_lookup] at h; simpa using h
    subst hTEeq; subst hT2eq
    have d_rv1 : (rel.var == v1) = false :=
      joinCompatible_lookup_distinct hJC12 hNode1 hEdge2 (sortInter_nodeOf_edgeOf_isBot ctx.graphSite)
    have d_n2r : (n2.var == rel.var) = false :=
      joinCompatible_singleton_distinct rel.var n2.var _ _ (sortInter_edgeOf_nodeOf_isBot ctx.graphSite) hJC23
    have hv1rel : (v1 == rel.var) = false := beq_name_symm_false d_rv1
    have hreln2 : (rel.var == n2.var) = false := beq_name_symm_false d_n2r
    have hrelmemE : rhoEdge.mem rel.var = true := by rw [hform]; simp [Record.mem, hv1rel]
    have hn2memE : rhoEdge.mem n2.var = true := by rw [hform]; simp [Record.mem]
    have lookE : (rho.merge rhoEdge).lookup rel.var = Value.edgeRef ctx.graphSite ei := by
      rw [Record.merge_lookup_agree_right rho rhoEdge rel.var hStepAgree hrelmemE, hform]
      simp [Record.lookup, List.find?_cons, hv1rel]
    have lookD : (rho.merge rhoEdge).lookup n2.var = Value.nodeRef ctx.graphSite dstN := by
      rw [Record.merge_lookup_agree_right rho rhoEdge n2.var hStepAgree hn2memE, hform]
      cases hvn : v1 == n2.var with
      | true => simp only [Record.lookup, List.find?_cons, hvn]; rw [hsd hvn]
      | false => simp [Record.lookup, List.find?_cons, hvn, hreln2]
    have hGRn2 : ((Gamma1.join (RecordSchema.mk [(rel.var, GSort.edgeOf ctx.graphSite)])).join
          (RecordSchema.mk [(n2.var, GSort.nodeOf ctx.graphSite)])).lookup n2.var
        = (match Gamma1.lookup n2.var with
           | some s => some (RecordSchema.sortInter s (GSort.nodeOf ctx.graphSite))
           | none => some (GSort.nodeOf ctx.graphSite)) := by
      rw [RecordSchema.join_lookup (RecordSchema.join_schemaWF hPrefixWF hwfGE) hwfGN,
          RecordSchema.join_lookup_of_right_none hPrefixWF hwfGE
            (RecordSchema.lookup_eq_none_of_mem_false (by rw [singleton_schema_mem]; exact hreln2)),
          singleton_schema_lookup]
      simp only [beq_self_eq_true, if_true]
      cases Gamma1.lookup n2.var <;> rfl
    have hGRrel : ((Gamma1.join (RecordSchema.mk [(rel.var, GSort.edgeOf ctx.graphSite)])).join
          (RecordSchema.mk [(n2.var, GSort.nodeOf ctx.graphSite)])).lookup rel.var
        = (match Gamma1.lookup rel.var with
           | some s => some (RecordSchema.sortInter s (GSort.edgeOf ctx.graphSite))
           | none => some (GSort.edgeOf ctx.graphSite)) := by
      rw [RecordSchema.join_lookup_of_right_none (RecordSchema.join_schemaWF hPrefixWF hwfGE) hwfGN
            (RecordSchema.lookup_eq_none_of_mem_false (by rw [singleton_schema_mem]; exact d_n2r)),
          RecordSchema.join_lookup hPrefixWF hwfGE, singleton_schema_lookup]
      simp only [beq_self_eq_true, if_true]
      cases Gamma1.lookup rel.var <;> rfl
    have hGRother : ∀ x, (x == rel.var) = false → (x == n2.var) = false →
        ((Gamma1.join (RecordSchema.mk [(rel.var, GSort.edgeOf ctx.graphSite)])).join
          (RecordSchema.mk [(n2.var, GSort.nodeOf ctx.graphSite)])).lookup x = Gamma1.lookup x := by
      intro x hxr hxn
      rw [RecordSchema.join_lookup_of_right_none (RecordSchema.join_schemaWF hPrefixWF hwfGE) hwfGN
            (RecordSchema.lookup_eq_none_of_mem_false (by rw [singleton_schema_mem]; exact beq_name_symm_false hxn))]
      exact RecordSchema.join_lookup_of_right_none hPrefixWF hwfGE
        (RecordSchema.lookup_eq_none_of_mem_false (by rw [singleton_schema_mem]; exact beq_name_symm_false hxr))
    intro x t hlk
    refine ⟨?_, ?_⟩
    · intro site ss hcomp g nn hn hlook ns hmem hconf
      cases hxr : x == rel.var with
      | true => rw [eq_of_beq hxr, lookE] at hlook; exact absurd hlook (by simp)
      | false =>
        cases hxn : x == n2.var with
        | true =>
          rw [eq_of_beq hxn, hGRn2] at hlk
          rw [eq_of_beq hxn, lookD] at hlook
          injection hlook with _ hnn'
          have hconf' : nodeConformsSchema G ⟨dstN, hdstN⟩ ns = true := by
            have hfin : (⟨dstN, hdstN⟩ : Fin G.numNodes) = ⟨nn, hn⟩ := Fin.ext hnn'
            rw [hfin]; exact hconf
          cases hg1n2 : Gamma1.lookup n2.var with
          | none =>
            rw [hg1n2] at hlk; obtain rfl := Option.some.inj hlk
            simp [GSort.componentType, GSort.nodeOf, GSort.nodeRefinedOf] at hcomp
          | some s =>
            rw [hg1n2] at hlk; obtain rfl := Option.some.inj hlk
            have hn2rho : rho.mem n2.var = true := by
              rw [hpredom n2.var]; exact RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem hg1n2)
            have hrhon2 : rho.lookup n2.var = Value.nodeRef ctx.graphSite dstN := by
              rw [Record.agreeOn_lookup_eq rho rhoEdge n2.var hStepAgree hn2rho hn2memE, hform]
              cases hvn : v1 == n2.var with
              | true => simp only [Record.lookup, List.find?_cons, hvn]; rw [hsd hvn]
              | false => simp [Record.lookup, List.find?_cons, hvn, hreln2]
            refine sortInter_componentType_nodeRefined_mem s (GSort.nodeOf ctx.graphSite) site ss ns ?_ ?_ hcomp
            · intro ss1 heq
              exact (hpre n2.var s hg1n2).1 site ss1 heq ctx.graphSite dstN hdstN hrhon2 ns hmem hconf'
            · intro ss2 heq; simp [GSort.componentType, GSort.nodeOf, GSort.nodeRefinedOf] at heq
        | false =>
          rw [hGRother x hxr hxn] at hlk
          have hxrho : rho.mem x = true := by
            rw [hpredom x]; exact RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem hlk)
          rw [Record.merge_lookup_left _ _ _ hxrho] at hlook
          exact (hpre x t hlk).1 site ss hcomp g nn hn hlook ns hmem hconf
    · intro site ss hcomp g ee he hlook es hmem hconf
      cases hxn : x == n2.var with
      | true => rw [eq_of_beq hxn, lookD] at hlook; exact absurd hlook (by simp)
      | false =>
        cases hxr : x == rel.var with
        | true =>
          rw [eq_of_beq hxr, hGRrel] at hlk
          rw [eq_of_beq hxr, lookE] at hlook
          injection hlook with _ hee'
          have hconf' : edgeConformsSchema G ⟨ei, hei⟩ es = true := by
            have hfin : (⟨ei, hei⟩ : Fin G.numEdges) = ⟨ee, he⟩ := Fin.ext hee'
            rw [hfin]; exact hconf
          cases hg1rel : Gamma1.lookup rel.var with
          | none =>
            rw [hg1rel] at hlk; obtain rfl := Option.some.inj hlk
            simp [GSort.componentType, GSort.edgeOf, GSort.edgeRefinedOf] at hcomp
          | some s =>
            rw [hg1rel] at hlk; obtain rfl := Option.some.inj hlk
            have hrelrho : rho.mem rel.var = true := by
              rw [hpredom rel.var]; exact RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem hg1rel)
            have hrhorel : rho.lookup rel.var = Value.edgeRef ctx.graphSite ei := by
              rw [Record.agreeOn_lookup_eq rho rhoEdge rel.var hStepAgree hrelrho hrelmemE, hform]
              simp [Record.lookup, List.find?_cons, hv1rel]
            refine sortInter_componentType_edgeRefined_mem s (GSort.edgeOf ctx.graphSite) site ss es ?_ ?_ hcomp
            · intro ss1 heq
              exact (hpre rel.var s hg1rel).2 site ss1 heq ctx.graphSite ei hei hrhorel es hmem hconf'
            · intro ss2 heq; simp [GSort.componentType, GSort.edgeOf, GSort.edgeRefinedOf] at heq
        | false =>
          rw [hGRother x hxr hxn] at hlk
          have hxrho : rho.mem x = true := by
            rw [hpredom x]; exact RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem hlk)
          rw [Record.merge_lookup_left _ _ _ hxrho] at hlook
          exact (hpre x t hlk).2 site ss hcomp g ee he hlook es hmem hconf
  | closed sN1 sE2 sN3 sN1' sE2' sN3' hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13
      hSrc' hEdge' hDst' hNonEmpty =>
    have hTEeq : TE = GSort.edgeRefinedOf ctx.graphSite sE2 := by
      have h := hEdge2; rw [singleton_schema_lookup] at h; simpa using h
    have hT2eq : T2 = GSort.nodeRefinedOf ctx.graphSite sN3 := by
      have h := hNode3; rw [singleton_schema_lookup] at h; simpa using h
    subst hTEeq; subst hT2eq
    obtain ⟨Psi2, PhiPiE, hSchema2, hPrpE2, hsE2eq⟩ := atomTyping_edge_refined_inv hAtomE hEdge2
    obtain ⟨Psi3, PhiPi3, hSchema3, hPrp3, hsN3eq⟩ := atomTyping_node_refined_inv hAtomN2 hNode3
    rw [Option.some.inj (hSchema2.symm.trans hPsi)] at hsE2eq
    rw [Option.some.inj (hSchema3.symm.trans hPsi)] at hsN3eq
    have hGconf : graphConformsSchema G Psi = true := hCat Psi hPsi
    obtain ⟨nsS, hnsS_Psi, hnsSconf⟩ := graphConformsSchema_node hGconf srcN hsrcN
    obtain ⟨es2, hes2_Psi, hes2conf⟩ := graphConformsSchema_edge hGconf ei hei
    obtain ⟨nsD, hnsD_Psi, hnsDconf⟩ := graphConformsSchema_node hGconf dstN hdstN
    have hnsS_sN1 : nsS ∈ sN1 :=
      (hpre v1 (GSort.nodeRefinedOf ctx.graphSite sN1) hNode1).1 ctx.graphSite sN1 rfl
        ctx.graphSite srcN hsrcN hrho_src nsS hnsS_Psi hnsSconf
    have hes2_sE2 : es2 ∈ sE2 := by
      rw [hsE2eq]
      exact filterEdgeSchemasByPropCompat_mem_of_conforms G ctx.graphSite ⟨ei, hei⟩ es2 _ rel.props PhiPiE
        (resolveEdgeSchemas_mem_of_conforms G Psi ⟨ei, hei⟩ es2 rel.labels hes2_Psi hes2conf hlblE)
        hes2conf hPrpE2 hprpE
    have hnsD_sN3 : nsD ∈ sN3 := by
      rw [hsN3eq]
      exact filterNodeSchemasByPropCompat_mem_of_conforms G ctx.graphSite ⟨dstN, hdstN⟩ nsD _ n2.props PhiPi3
        (resolveNodeSchemas_mem_of_conforms G Psi ⟨dstN, hdstN⟩ nsD n2.labels hnsD_Psi hnsDconf hlblD)
        hnsDconf hPrp3 hprpD
    have d_rv1 : (rel.var == v1) = false :=
      joinCompatible_lookup_distinct hJC12 hNode1 hEdge2
        (sortInter_nodeRefinedOf_edgeRefinedOf_isBot ctx.graphSite sN1 sE2)
    have d_n2r : (n2.var == rel.var) = false :=
      joinCompatible_singleton_distinct rel.var n2.var _ _
        (sortInter_edgeRefinedOf_nodeRefinedOf_isBot ctx.graphSite sE2 sN3) hJC23
    have hv1rel : (v1 == rel.var) = false := beq_name_symm_false d_rv1
    have hreln2 : (rel.var == n2.var) = false := beq_name_symm_false d_n2r
    have hrelmemE : rhoEdge.mem rel.var = true := by rw [hform]; simp [Record.mem, hv1rel]
    have hn2memE : rhoEdge.mem n2.var = true := by rw [hform]; simp [Record.mem]
    have lookE : (rho.merge rhoEdge).lookup rel.var = Value.edgeRef ctx.graphSite ei := by
      rw [Record.merge_lookup_agree_right rho rhoEdge rel.var hStepAgree hrelmemE, hform]
      simp [Record.lookup, List.find?_cons, hv1rel]
    have lookD : (rho.merge rhoEdge).lookup n2.var = Value.nodeRef ctx.graphSite dstN := by
      rw [Record.merge_lookup_agree_right rho rhoEdge n2.var hStepAgree hn2memE, hform]
      cases hvn : v1 == n2.var with
      | true => simp only [Record.lookup, List.find?_cons, hvn]; rw [hsd hvn]
      | false => simp [Record.lookup, List.find?_cons, hvn, hreln2]
    have lookS : (rho.merge rhoEdge).lookup v1 = Value.nodeRef ctx.graphSite srcN := by
      rw [Record.merge_lookup_left rho rhoEdge v1 hv1memRho, hrho_src]
    have hGRother : ∀ x, (x == v1) = false → (x == rel.var) = false → (x == n2.var) = false →
        (((Gamma1.join (RecordSchema.mk [(rel.var, GSort.edgeRefinedOf ctx.graphSite sE2)])).join
            (RecordSchema.mk [(n2.var, GSort.nodeRefinedOf ctx.graphSite sN3)])).setMany
          [(v1, GSort.nodeRefinedOf ctx.graphSite sN1'),
           (rel.var, GSort.edgeRefinedOf ctx.graphSite sE2'),
           (n2.var, GSort.nodeRefinedOf ctx.graphSite sN3')]).lookup x = Gamma1.lookup x := by
      intro x hxv hxr hxn
      rw [RecordSchema.setMany3_lookup_other _ v1 rel.var n2.var _ _ _ x
            (beq_name_symm_false hxv) (beq_name_symm_false hxr) (beq_name_symm_false hxn)]
      rw [RecordSchema.join_lookup_of_right_none (RecordSchema.join_schemaWF hPrefixWF hwfGE) hwfGN
            (RecordSchema.lookup_eq_none_of_mem_false
              (by rw [singleton_schema_mem]; exact beq_name_symm_false hxn))]
      exact RecordSchema.join_lookup_of_right_none hPrefixWF hwfGE
        (RecordSchema.lookup_eq_none_of_mem_false
          (by rw [singleton_schema_mem]; exact beq_name_symm_false hxr))
    intro x t hlk
    refine ⟨?_, ?_⟩
    · intro site ss hcomp g nn hn hlook ns hmem hconf
      cases hxr : x == rel.var with
      | true =>
        rw [eq_of_beq hxr, RecordSchema.setMany3_lookup_snd _ v1 rel.var n2.var _ _ _ d_n2r] at hlk
        obtain rfl := Option.some.inj hlk
        simp [GSort.componentType, GSort.edgeRefinedOf, GSort.nodeRefinedOf] at hcomp
      | false =>
        cases hxn : x == n2.var with
        | true =>
          rw [eq_of_beq hxn, RecordSchema.setMany3_lookup_thd _ v1 rel.var n2.var _ _ _] at hlk
          obtain rfl := Option.some.inj hlk
          simp only [GSort.nodeRefinedOf, GSort.componentType, GSort.mk.injEq, SortShape.single.injEq,
            ExtSort.nodeRefined.injEq, true_and, and_true] at hcomp
          obtain ⟨_, rfl⟩ := hcomp
          rw [eq_of_beq hxn, lookD] at hlook
          injection hlook with _ hnn'
          have hconf' : nodeConformsSchema G ⟨dstN, hdstN⟩ ns = true := by
            have hfin : (⟨dstN, hdstN⟩ : Fin G.numNodes) = ⟨nn, hn⟩ := Fin.ext hnn'
            rw [hfin]; exact hconf
          rw [hDst']; unfold refineDstByCompat; rw [List.mem_filter]
          refine ⟨?_, ?_⟩
          · rw [hsN3eq]
            exact filterNodeSchemasByPropCompat_mem_of_conforms G ctx.graphSite ⟨dstN, hdstN⟩ ns _ n2.props PhiPi3
              (resolveNodeSchemas_mem_of_conforms G Psi ⟨dstN, hdstN⟩ ns n2.labels hmem hconf' hlblD)
              hconf' hPrp3 hprpD
          · rw [List.any_eq_true]; refine ⟨nsS, hnsS_sN1, ?_⟩
            rw [List.any_eq_true]; exact ⟨es2, hes2_sE2,
              tripleCompat_of_matched G srcN ei dstN hsrcN hei hdstN dir nsS ns es2 hnsSconf hconf' hes2conf hphi⟩
        | false =>
          cases hxv : x == v1 with
          | true =>
            have d_n2v1 : (n2.var == v1) = false := by
              have h := hxn; rw [eq_of_beq hxv] at h; exact beq_name_symm_false h
            rw [eq_of_beq hxv, RecordSchema.setMany3_lookup_fst _ v1 rel.var n2.var _ _ _ d_rv1 d_n2v1] at hlk
            obtain rfl := Option.some.inj hlk
            simp only [GSort.nodeRefinedOf, GSort.componentType, GSort.mk.injEq, SortShape.single.injEq,
              ExtSort.nodeRefined.injEq, true_and, and_true] at hcomp
            obtain ⟨_, rfl⟩ := hcomp
            rw [eq_of_beq hxv, lookS] at hlook
            injection hlook with _ hnn'
            have hconf' : nodeConformsSchema G ⟨srcN, hsrcN⟩ ns = true := by
              have hfin : (⟨srcN, hsrcN⟩ : Fin G.numNodes) = ⟨nn, hn⟩ := Fin.ext hnn'
              rw [hfin]; exact hconf
            rw [hSrc']; unfold refineSrcByCompat; rw [List.mem_filter]
            refine ⟨?_, ?_⟩
            · exact (hpre v1 (GSort.nodeRefinedOf ctx.graphSite sN1) hNode1).1 ctx.graphSite sN1 rfl
                ctx.graphSite srcN hsrcN hrho_src ns hmem hconf'
            · rw [List.any_eq_true]; refine ⟨es2, hes2_sE2, ?_⟩
              rw [List.any_eq_true]; exact ⟨nsD, hnsD_sN3,
                tripleCompat_of_matched G srcN ei dstN hsrcN hei hdstN dir ns nsD es2 hconf' hnsDconf hes2conf hphi⟩
          | false =>
            rw [hGRother x hxv hxr hxn] at hlk
            have hxrho : rho.mem x = true := by
              cases hm : rho.mem x with
              | true => rfl
              | false =>
                exfalso
                rw [Record.merge_lookup_right _ _ _ hm, hform] at hlook
                simp only [Record.lookup, List.find?_cons,
                  beq_name_symm_false hxv, beq_name_symm_false hxr, beq_name_symm_false hxn] at hlook
                exact Value.noConfusion hlook
            rw [Record.merge_lookup_left _ _ _ hxrho] at hlook
            exact (hpre x t hlk).1 site ss hcomp g nn hn hlook ns hmem hconf
    · intro site ss hcomp g ee he hlook es hmem hconf
      cases hxr : x == rel.var with
      | true =>
        rw [eq_of_beq hxr, RecordSchema.setMany3_lookup_snd _ v1 rel.var n2.var _ _ _ d_n2r] at hlk
        obtain rfl := Option.some.inj hlk
        simp only [GSort.edgeRefinedOf, GSort.componentType, GSort.mk.injEq, SortShape.single.injEq,
          ExtSort.edgeRefined.injEq, true_and, and_true] at hcomp
        obtain ⟨_, rfl⟩ := hcomp
        rw [eq_of_beq hxr, lookE] at hlook
        injection hlook with _ hee'
        have hconf' : edgeConformsSchema G ⟨ei, hei⟩ es = true := by
          have hfin : (⟨ei, hei⟩ : Fin G.numEdges) = ⟨ee, he⟩ := Fin.ext hee'
          rw [hfin]; exact hconf
        rw [hEdge']; unfold refineEdgeByCompat; rw [List.mem_filter]
        refine ⟨?_, ?_⟩
        · rw [hsE2eq]
          exact filterEdgeSchemasByPropCompat_mem_of_conforms G ctx.graphSite ⟨ei, hei⟩ es _ rel.props PhiPiE
            (resolveEdgeSchemas_mem_of_conforms G Psi ⟨ei, hei⟩ es rel.labels hmem hconf' hlblE)
            hconf' hPrpE2 hprpE
        · rw [List.any_eq_true]; refine ⟨nsS, hnsS_sN1, ?_⟩
          rw [List.any_eq_true]; exact ⟨nsD, hnsD_sN3,
            tripleCompat_of_matched G srcN ei dstN hsrcN hei hdstN dir nsS nsD es hnsSconf hnsDconf hconf' hphi⟩
      | false =>
        cases hxn : x == n2.var with
        | true =>
          rw [eq_of_beq hxn, RecordSchema.setMany3_lookup_thd _ v1 rel.var n2.var _ _ _] at hlk
          obtain rfl := Option.some.inj hlk
          simp [GSort.componentType, GSort.edgeRefinedOf, GSort.nodeRefinedOf] at hcomp
        | false =>
          cases hxv : x == v1 with
          | true =>
            have d_n2v1 : (n2.var == v1) = false := by
              have h := hxn; rw [eq_of_beq hxv] at h; exact beq_name_symm_false h
            rw [eq_of_beq hxv, RecordSchema.setMany3_lookup_fst _ v1 rel.var n2.var _ _ _ d_rv1 d_n2v1] at hlk
            obtain rfl := Option.some.inj hlk
            simp [GSort.componentType, GSort.edgeRefinedOf, GSort.nodeRefinedOf] at hcomp
          | false =>
            rw [hGRother x hxv hxr hxn] at hlk
            have hxrho : rho.mem x = true := by
              cases hm : rho.mem x with
              | true => rfl
              | false =>
                exfalso
                rw [Record.merge_lookup_right _ _ _ hm, hform] at hlook
                simp only [Record.lookup, List.find?_cons,
                  beq_name_symm_false hxv, beq_name_symm_false hxr, beq_name_symm_false hxn] at hlook
                exact Value.noConfusion hlook
            rw [Record.merge_lookup_left _ _ _ hxrho] at hlook
            exact (hpre x t hlk).2 site ss hcomp g ee he hlook es hmem hconf
  | closedEmpty hJC12 hJC23 hJC13 hSomeEmpty =>
    have hGRother : ∀ x, (x == v1) = false → (x == rel.var) = false → (x == n2.var) = false →
        (((Gamma1.join (RecordSchema.mk [(rel.var, TE)])).join
            (RecordSchema.mk [(n2.var, T2)])).setMany
          [(v1, GSort.nodeEmpty ctx.graphSite),
           (rel.var, GSort.edgeEmpty ctx.graphSite),
           (n2.var, GSort.nodeEmpty ctx.graphSite)]).lookup x = Gamma1.lookup x := by
      intro x hxv hxr hxn
      rw [RecordSchema.setMany3_lookup_other _ v1 rel.var n2.var _ _ _ x
            (beq_name_symm_false hxv) (beq_name_symm_false hxr) (beq_name_symm_false hxn)]
      rw [RecordSchema.join_lookup_of_right_none (RecordSchema.join_schemaWF hPrefixWF hwfGE) hwfGN
            (RecordSchema.lookup_eq_none_of_mem_false
              (by rw [singleton_schema_mem]; exact beq_name_symm_false hxn))]
      exact RecordSchema.join_lookup_of_right_none hPrefixWF hwfGE
        (RecordSchema.lookup_eq_none_of_mem_false
          (by rw [singleton_schema_mem]; exact beq_name_symm_false hxr))
    intro x t hlk
    refine ⟨?_, ?_⟩
    · intro site ss hcomp g nn hn hlook ns hmem hconf
      cases hxn : x == n2.var with
      | true =>
        rw [eq_of_beq hxn, RecordSchema.setMany3_lookup_thd _ v1 rel.var n2.var _ _ _] at hlk
        obtain rfl := Option.some.inj hlk
        simp [GSort.componentType, GSort.nodeEmpty, GSort.nodeRefinedOf] at hcomp
      | false =>
        cases hxr : x == rel.var with
        | true =>
          have d_n2r : (n2.var == rel.var) = false := by
            have h := hxn; rw [eq_of_beq hxr] at h; exact beq_name_symm_false h
          rw [eq_of_beq hxr, RecordSchema.setMany3_lookup_snd _ v1 rel.var n2.var _ _ _ d_n2r] at hlk
          obtain rfl := Option.some.inj hlk
          simp [GSort.componentType, GSort.edgeEmpty, GSort.nodeRefinedOf] at hcomp
        | false =>
          cases hxv : x == v1 with
          | true =>
            have d_rv1 : (rel.var == v1) = false := by
              have h := hxr; rw [eq_of_beq hxv] at h; exact beq_name_symm_false h
            have d_n2v1 : (n2.var == v1) = false := by
              have h := hxn; rw [eq_of_beq hxv] at h; exact beq_name_symm_false h
            rw [eq_of_beq hxv, RecordSchema.setMany3_lookup_fst _ v1 rel.var n2.var _ _ _ d_rv1 d_n2v1] at hlk
            obtain rfl := Option.some.inj hlk
            simp [GSort.componentType, GSort.nodeEmpty, GSort.nodeRefinedOf] at hcomp
          | false =>
            rw [hGRother x hxv hxr hxn] at hlk
            have hxrho : rho.mem x = true := by
              cases hm : rho.mem x with
              | true => rfl
              | false =>
                exfalso
                rw [Record.merge_lookup_right _ _ _ hm, hform] at hlook
                simp only [Record.lookup, List.find?_cons,
                  beq_name_symm_false hxv, beq_name_symm_false hxr, beq_name_symm_false hxn] at hlook
                exact Value.noConfusion hlook
            rw [Record.merge_lookup_left _ _ _ hxrho] at hlook
            exact (hpre x t hlk).1 site ss hcomp g nn hn hlook ns hmem hconf
    · intro site ss hcomp g ee he hlook es hmem hconf
      cases hxn : x == n2.var with
      | true =>
        rw [eq_of_beq hxn, RecordSchema.setMany3_lookup_thd _ v1 rel.var n2.var _ _ _] at hlk
        obtain rfl := Option.some.inj hlk
        simp [GSort.componentType, GSort.nodeEmpty, GSort.edgeRefinedOf] at hcomp
      | false =>
        cases hxr : x == rel.var with
        | true =>
          have d_n2r : (n2.var == rel.var) = false := by
            have h := hxn; rw [eq_of_beq hxr] at h; exact beq_name_symm_false h
          rw [eq_of_beq hxr, RecordSchema.setMany3_lookup_snd _ v1 rel.var n2.var _ _ _ d_n2r] at hlk
          obtain rfl := Option.some.inj hlk
          simp [GSort.componentType, GSort.edgeEmpty, GSort.edgeRefinedOf] at hcomp
        | false =>
          cases hxv : x == v1 with
          | true =>
            have d_rv1 : (rel.var == v1) = false := by
              have h := hxr; rw [eq_of_beq hxv] at h; exact beq_name_symm_false h
            have d_n2v1 : (n2.var == v1) = false := by
              have h := hxn; rw [eq_of_beq hxv] at h; exact beq_name_symm_false h
            rw [eq_of_beq hxv, RecordSchema.setMany3_lookup_fst _ v1 rel.var n2.var _ _ _ d_rv1 d_n2v1] at hlk
            obtain rfl := Option.some.inj hlk
            simp [GSort.componentType, GSort.nodeEmpty, GSort.edgeRefinedOf] at hcomp
          | false =>
            rw [hGRother x hxv hxr hxn] at hlk
            have hxrho : rho.mem x = true := by
              cases hm : rho.mem x with
              | true => rfl
              | false =>
                exfalso
                rw [Record.merge_lookup_right _ _ _ hm, hform] at hlook
                simp only [Record.lookup, List.find?_cons,
                  beq_name_symm_false hxv, beq_name_symm_false hxr, beq_name_symm_false hxn] at hlook
                exact Value.noConfusion hlook
            rw [Record.merge_lookup_left _ _ _ hxrho] at hlook
            exact (hpre x t hlk).2 site ss hcomp g ee he hlook es hmem hconf
  | closedFail sN1 sE2 sN3 hNode1 hEdge2 hNode3 hJC12 hJC23 hJC13 hFail =>
    have hTEeq : TE = GSort.edgeRefinedOf ctx.graphSite sE2 := by
      have h := hEdge2; rw [singleton_schema_lookup] at h; simpa using h
    have hT2eq : T2 = GSort.nodeRefinedOf ctx.graphSite sN3 := by
      have h := hNode3; rw [singleton_schema_lookup] at h; simpa using h
    subst hTEeq; subst hT2eq
    have d_rv1 : (rel.var == v1) = false :=
      joinCompatible_lookup_distinct hJC12 hNode1 hEdge2
        (sortInter_nodeRefinedOf_edgeRefinedOf_isBot ctx.graphSite sN1 sE2)
    have d_n2r : (n2.var == rel.var) = false :=
      joinCompatible_singleton_distinct rel.var n2.var _ _
        (sortInter_edgeRefinedOf_nodeRefinedOf_isBot ctx.graphSite sE2 sN3) hJC23
    have hGRother : ∀ x, (x == v1) = false → (x == rel.var) = false → (x == n2.var) = false →
        (((Gamma1.join (RecordSchema.mk [(rel.var, GSort.edgeRefinedOf ctx.graphSite sE2)])).join
            (RecordSchema.mk [(n2.var, GSort.nodeRefinedOf ctx.graphSite sN3)])).setMany
          [(v1, GSort.nodeEmpty ctx.graphSite),
           (rel.var, GSort.edgeEmpty ctx.graphSite),
           (n2.var, GSort.nodeEmpty ctx.graphSite)]).lookup x = Gamma1.lookup x := by
      intro x hxv hxr hxn
      rw [RecordSchema.setMany3_lookup_other _ v1 rel.var n2.var _ _ _ x
            (beq_name_symm_false hxv) (beq_name_symm_false hxr) (beq_name_symm_false hxn)]
      rw [RecordSchema.join_lookup_of_right_none (RecordSchema.join_schemaWF hPrefixWF hwfGE) hwfGN
            (RecordSchema.lookup_eq_none_of_mem_false
              (by rw [singleton_schema_mem]; exact beq_name_symm_false hxn))]
      exact RecordSchema.join_lookup_of_right_none hPrefixWF hwfGE
        (RecordSchema.lookup_eq_none_of_mem_false
          (by rw [singleton_schema_mem]; exact beq_name_symm_false hxr))
    intro x t hlk
    refine ⟨?_, ?_⟩
    · intro site ss hcomp g nn hn hlook ns hmem hconf
      cases hxr : x == rel.var with
      | true =>
        rw [eq_of_beq hxr, RecordSchema.setMany3_lookup_snd _ v1 rel.var n2.var _ _ _ d_n2r] at hlk
        obtain rfl := Option.some.inj hlk
        simp [GSort.componentType, GSort.edgeEmpty, GSort.nodeRefinedOf] at hcomp
      | false =>
        cases hxn : x == n2.var with
        | true =>
          rw [eq_of_beq hxn, RecordSchema.setMany3_lookup_thd _ v1 rel.var n2.var _ _ _] at hlk
          obtain rfl := Option.some.inj hlk
          simp [GSort.componentType, GSort.nodeEmpty, GSort.nodeRefinedOf] at hcomp
        | false =>
          cases hxv : x == v1 with
          | true =>
            have d_n2v1 : (n2.var == v1) = false := by
              have h := hxn; rw [eq_of_beq hxv] at h; exact beq_name_symm_false h
            rw [eq_of_beq hxv, RecordSchema.setMany3_lookup_fst _ v1 rel.var n2.var _ _ _ d_rv1 d_n2v1] at hlk
            obtain rfl := Option.some.inj hlk
            simp [GSort.componentType, GSort.nodeEmpty, GSort.nodeRefinedOf] at hcomp
          | false =>
            rw [hGRother x hxv hxr hxn] at hlk
            have hxrho : rho.mem x = true := by
              cases hm : rho.mem x with
              | true => rfl
              | false =>
                exfalso
                rw [Record.merge_lookup_right _ _ _ hm, hform] at hlook
                simp only [Record.lookup, List.find?_cons,
                  beq_name_symm_false hxv, beq_name_symm_false hxr, beq_name_symm_false hxn] at hlook
                exact Value.noConfusion hlook
            rw [Record.merge_lookup_left _ _ _ hxrho] at hlook
            exact (hpre x t hlk).1 site ss hcomp g nn hn hlook ns hmem hconf
    · intro site ss hcomp g ee he hlook es hmem hconf
      cases hxr : x == rel.var with
      | true =>
        rw [eq_of_beq hxr, RecordSchema.setMany3_lookup_snd _ v1 rel.var n2.var _ _ _ d_n2r] at hlk
        obtain rfl := Option.some.inj hlk
        simp [GSort.componentType, GSort.edgeEmpty, GSort.edgeRefinedOf] at hcomp
      | false =>
        cases hxn : x == n2.var with
        | true =>
          rw [eq_of_beq hxn, RecordSchema.setMany3_lookup_thd _ v1 rel.var n2.var _ _ _] at hlk
          obtain rfl := Option.some.inj hlk
          simp [GSort.componentType, GSort.nodeEmpty, GSort.edgeRefinedOf] at hcomp
        | false =>
          cases hxv : x == v1 with
          | true =>
            have d_n2v1 : (n2.var == v1) = false := by
              have h := hxn; rw [eq_of_beq hxv] at h; exact beq_name_symm_false h
            rw [eq_of_beq hxv, RecordSchema.setMany3_lookup_fst _ v1 rel.var n2.var _ _ _ d_rv1 d_n2v1] at hlk
            obtain rfl := Option.some.inj hlk
            simp [GSort.componentType, GSort.nodeEmpty, GSort.edgeRefinedOf] at hcomp
          | false =>
            rw [hGRother x hxv hxr hxn] at hlk
            have hxrho : rho.mem x = true := by
              cases hm : rho.mem x with
              | true => rfl
              | false =>
                exfalso
                rw [Record.merge_lookup_right _ _ _ hm, hform] at hlook
                simp only [Record.lookup, List.find?_cons,
                  beq_name_symm_false hxv, beq_name_symm_false hxr, beq_name_symm_false hxn] at hlook
                exact Value.noConfusion hlook
            rw [Record.merge_lookup_left _ _ _ hxrho] at hlook
            exact (hpre x t hlk).2 site ss hcomp g ee he hlook es hmem hconf

-- (open_join_entry_is_nodeOf_or_edgeOf moved earlier, before the OpenSort
--  development, which also uses it.)

private theorem componentType_nodeOf (site : GraphSite) :
    (GSort.nodeOf site).componentType = GSort.nodeOf site := rfl

private theorem componentType_edgeOf (site : GraphSite) :
    (GSort.edgeOf site).componentType = GSort.edgeOf site := rfl

private theorem componentType_liftToList_nodeOf (site : GraphSite) :
    (GSort.nodeOf site).liftToList.componentType = GSort.nodeOf site := rfl

private theorem componentType_liftToList_edgeOf (site : GraphSite) :
    (GSort.edgeOf site).liftToList.componentType = GSort.edgeOf site := rfl

private theorem nodeOf_ne_nodeRefinedOf (site site' : GraphSite) (ss : List NodeSchemaFull) :
    GSort.nodeOf site ≠ GSort.nodeRefinedOf site' ss := by
  simp [GSort.nodeOf, GSort.nodeRefinedOf, GSort.mk.injEq, SortShape.single.injEq]

private theorem nodeOf_ne_edgeRefinedOf (site site' : GraphSite) (ss : List EdgeSchemaFull) :
    GSort.nodeOf site ≠ GSort.edgeRefinedOf site' ss := by
  simp [GSort.nodeOf, GSort.edgeRefinedOf, GSort.mk.injEq, SortShape.single.injEq]

private theorem edgeOf_ne_nodeRefinedOf (site site' : GraphSite) (ss : List NodeSchemaFull) :
    GSort.edgeOf site ≠ GSort.nodeRefinedOf site' ss := by
  simp [GSort.edgeOf, GSort.nodeRefinedOf, GSort.mk.injEq, SortShape.single.injEq]

private theorem edgeOf_ne_edgeRefinedOf (site site' : GraphSite) (ss : List EdgeSchemaFull) :
    GSort.edgeOf site ≠ GSort.edgeRefinedOf site' ss := by
  simp [GSort.edgeOf, GSort.edgeRefinedOf, GSort.mk.injEq, SortShape.single.injEq]

-- ============================================================
--  Strong runtime-config WF of pattern expressions (closes hPatRtWF)
-- ============================================================

/-- Per-pattern strong runtime well-formedness, by induction on `PatternTyping`
    (mirrors `patternTyping_sound`). The node/edge atoms discharge via the strong
    atom lemmas; `grouped` via the IH; `step`/`quant-edge`/`quant-path` are carried
    as obligations (the same blocked fidelity items as in `patternTyping_sound`). -/
theorem patternTyping_runtimeWFStrong
    (ctx : TypingCtx) (G : PropertyGraph) (Psi : GraphSchemaFull)
    (hPsi : ctx.schemaMap.lookup ctx.graphSite = some Psi)
    (hCat : ∀ Psi', ctx.schemaMap.lookup ctx.graphSite = some Psi' →
              graphConformsSchema G Psi' = true) :
    ∀ (qd : QuantDepth) (P : Pattern) (Gamma : RecordSchema) (v : Name),
      PatternTyping ctx qd P Gamma v →
      ∀ rho, rho ∈ evalPattern G ctx.graphSite P → RuntimeConfigWFStrong G Psi rho Gamma := by
  intro qd P Gamma v h
  induction h with
  | patNode qd na GammaA hAtom =>
      intro rho hrho
      rw [evalPattern_node] at hrho
      exact matchNode_runtimeWFStrong ctx G na GammaA hAtom Psi hPsi rho hrho
  | patEdge qd n1 n2 rel dir GammaN1 GammaE GammaN2 GammaRef hSingleD hAtomN1 hAtomE hAtomN2 hRef =>
      intro rho hrho
      rw [evalPattern_edge_single G ctx.graphSite n1 n2 rel dir hSingleD] at hrho
      exact matchSingleEdge_runtimeWFStrong ctx G n1 n2 rel dir _ _ _ _
        hAtomN1 (edge_atom_strip hSingleD ▸ hAtomE) hAtomN2 hRef hCat Psi hPsi rho hrho
  | patStep qd P rel dir n2 Gamma1 GammaE GammaN2 GammaRef v1 hSingle hPrefix hAtomE hAtomN2 hRef ihPrefix =>
      intro rho hrho
      exact step_runtimeWFStrong ctx G Psi hPsi hCat P rel dir n2 Gamma1 GammaE GammaN2 GammaRef v1
        hSingle (patternTyping_tailVar hPrefix)
        (patternTyping_schemaWF hPrefix)
        (fun rho' hrho' x =>
          patternEvalDom ctx G qd P Gamma1 v1 hPrefix rho' hrho' x)
        ihPrefix hAtomE hAtomN2 hRef rho hrho
  | patQuantEdge n1 n2 rel dir K GammaE hQuant hAtomE hNE12 hNE23 =>
      intro rho hrho x t hlk
      obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
      have ⟨t0, ht0mem, ht0eq⟩ := RecordSchema.mem_liftToGroupRef_entries
          (RecordSchema.lookup_some_mem hlk)
      rcases open_join_entry_is_nodeOf_or_edgeOf ctx.graphSite n1 n2 rel
          TE hNE12 hNE23 x t0 ht0mem with h | ⟨hxrel, h⟩
      · -- node entry: componentType is the open node sort in both lift branches
        have hct : t.componentType = GSort.nodeOf ctx.graphSite := by
          subst ht0eq
          subst h
          cases hif : List.any [rel.var] fun v => v == x
          · simp [hif, componentType_nodeOf]
          · simp [hif, componentType_liftToList_nodeOf]
        refine ⟨fun site' ss hcomp => ?_, fun site' ss hcomp => ?_⟩ <;>
        intro g idx hidx hlook ns hmem hconf <;> exfalso
        · exact nodeOf_ne_nodeRefinedOf _ _ _ (hct ▸ hcomp)
        · exact nodeOf_ne_edgeRefinedOf _ _ _ (hct ▸ hcomp)
      · -- the group variable: its bound value is an edge LIST, so the
        -- reference-conditional obligations are vacuous whatever TE is
        subst hxrel
        have hH1 : (n1.var == rel.var) = false := beq_name_symm_false hNE12
        have hH2 : (n2.var == rel.var) = false := beq_name_symm_false hNE23
        rw [evalPattern_edge_groupRef G ctx.graphSite n1 n2
          { rel with quantifier := K } dir hQuant] at hrho
        obtain ⟨srcN, dstN, edges, rfl⟩ :=
          matchRangePath_mem_form G ctx.graphSite dir n1 { rel with quantifier := K } n2
            _ _ _ hH1 hH2 hrho
        refine ⟨fun site' ss hcomp => ?_, fun site' ss hcomp => ?_⟩ <;>
        intro g idx hidx hlook ns hmem hconf <;> exfalso <;>
          simp [Record.lookup, List.find?_cons, hH1, hH2, Value.ofList] at hlook
  | patOptEdge n1 n2 rel dir hNE12 hNE23 =>
      intro rho hrho x t hlk
      have ⟨t0, ht0mem, ht0eq⟩ := RecordSchema.mem_liftToNullable_entries
          (RecordSchema.lookup_some_mem hlk)
      have ht0kind := open_join_entry_is_nodeOf_or_edgeOf ctx.graphSite n1 n2 rel
          (GSort.edgeOf ctx.graphSite) hNE12 hNE23 x t0 ht0mem
      have hct : t.componentType = GSort.nodeOf ctx.graphSite ∨
                 t.componentType = GSort.edgeOf ctx.graphSite := by
        subst ht0eq
        cases ht0kind with
        | inl h =>
            subst h; cases hif : List.any [rel.var] fun v => v == x
            · exact Or.inl (by
                simp [hif, GSort.toNullable, GSort.componentType, GSort.nodeOf])
            · exact Or.inl (by
                simp [hif, GSort.toNullable, GSort.componentType, GSort.nodeOf])
        | inr h =>
            obtain ⟨hxrel, h⟩ := h
            subst h; cases hif : List.any [rel.var] fun v => v == x
            · exact Or.inr (by
                simp [hif, GSort.toNullable, GSort.componentType, GSort.edgeOf])
            · exact Or.inr (by
                simp [hif, GSort.toNullable, GSort.componentType, GSort.edgeOf])
      refine ⟨fun site' ss hcomp => ?_, fun site' ss hcomp => ?_⟩ <;>
      intro g idx hidx hlook ns hmem hconf <;> exfalso
      · cases hct with
        | inl h => exact nodeOf_ne_nodeRefinedOf _ _ _ (h ▸ hcomp)
        | inr h => exact edgeOf_ne_nodeRefinedOf _ _ _ (h ▸ hcomp)
      · cases hct with
        | inl h => exact nodeOf_ne_edgeRefinedOf _ _ _ (h ▸ hcomp)
        | inr h => exact edgeOf_ne_edgeRefinedOf _ _ _ (h ▸ hcomp)
  | patQuantPath P K GammaInner v hInner hQuant ihInner =>
      intro rho hrho
      obtain ⟨lv, hlv⟩ := patternLeadVar_isSome P
      obtain ⟨tv, htv⟩ := patternTailVar_isSome P
      have hvars := patternTyping_vars_mem hInner
      have hinner : ∀ z, GammaInner.dom.any (fun w => w == z)
          = (patternVars P).any (fun w => w == z) := by
        intro z
        rw [hvars z]
        exact RecordSchema.dom_any_mem GammaInner z
      simp only [evalPattern, hlv, htv] at hrho
      exact evalQuantified_runtimeWFStrong G Psi (patternVars P) (evalPattern G ctx.graphSite P)
        lv tv K.lo _ GammaInner GammaInner.dom hvars hinner rho hrho
  | patGrouped qd P Gamma v hP ih =>
      intro rho hrho
      rw [evalPattern_grouped] at hrho
      exact ih rho hrho

/-- Strong runtime well-formedness of pattern expressions (closes `hPatRtWF`).
    By induction on `PatExprTyping`: the `single` layer via `patternTyping_runtimeWFStrong`,
    the conjunction (join) layer via `runtimeConfigWFStrong_join`. The domain
    equalities the join lemma needs come from pattern soundness `hSound` (the
    domain half of `BTConforms`); `SchemaWF` via `patExprTyping_schemaWF`. -/
theorem patExpr_runtimeWFStrong
    (ctx : TypingCtx) (G : PropertyGraph) (Psi : GraphSchemaFull)
    (hPsi : ctx.schemaMap.lookup ctx.graphSite = some Psi)
    (hCat : ∀ Psi', ctx.schemaMap.lookup ctx.graphSite = some Psi' →
              graphConformsSchema G Psi' = true)
    (hSound : ∀ (P' : Pattern) (G' : RecordSchema),
        PatExprTyping ctx P' G' → BTConforms (evalPattern G ctx.graphSite P') G')
    (P : Pattern) (GammaOut : RecordSchema)
    (hType : PatExprTyping ctx P GammaOut) :
    ∀ rho, rho ∈ evalPattern G ctx.graphSite P → RuntimeConfigWFStrong G Psi rho GammaOut := by
  induction hType with
  | single P Gamma v h =>
      intro rho hrho
      exact patternTyping_runtimeWFStrong ctx G Psi hPsi hCat
        .outside P Gamma v h rho hrho
  | conjunction P1 P2 Gamma1 Gamma2 v h1 h2 hjc ih1 =>
      intro rho hrho
      rw [evalPattern_patternList] at hrho
      obtain ⟨rho1, hrho1, rho2, hrho2, hag, rfl⟩ := mem_bindingTableJoin hrho
      exact runtimeConfigWFStrong_join G Psi rho1 rho2 Gamma1 Gamma2
        (patExprTyping_schemaWF h1)
        (patExprTyping_schemaWF (PatExprTyping.single ctx P2 Gamma2 v h2))
        (hSound P1 Gamma1 h1 rho1 hrho1).1
        (hSound P2 Gamma2 (PatExprTyping.single ctx P2 Gamma2 v h2) rho2 hrho2).1
        hag
        (ih1 rho1 hrho1)
        (patternTyping_runtimeWFStrong ctx G Psi hPsi hCat
          .outside P2 Gamma2 v h2 rho2 hrho2)

/-- Runtime well-formedness of pattern expressions (`hPatRtWF`). The plain
    `RuntimeConfigWF` form, obtained from `patExpr_runtimeWFStrong` by
    `runtimeConfigWF_of_strong` (graph conformance supplies the existential witness
    the plain property needs). This is exactly the `hPatRtWF` leaf the query and
    composite soundness theorems carry. -/
theorem patExpr_runtimeWF
    (ctx : TypingCtx) (G : PropertyGraph) (Psi : GraphSchemaFull)
    (hPsi : ctx.schemaMap.lookup ctx.graphSite = some Psi)
    (hCat : ∀ Psi', ctx.schemaMap.lookup ctx.graphSite = some Psi' →
              graphConformsSchema G Psi' = true)
    (hSound : ∀ (P' : Pattern) (G' : RecordSchema),
        PatExprTyping ctx P' G' → BTConforms (evalPattern G ctx.graphSite P') G') :
    ∀ (P : Pattern) (GammaOut : RecordSchema),
      PatExprTyping ctx P GammaOut →
      ∀ rho, rho ∈ evalPattern G ctx.graphSite P → RuntimeConfigWF G rho GammaOut := by
  intro P GammaOut hType rho hrho
  exact runtimeConfigWF_of_strong (hCat Psi hPsi)
    (patExpr_runtimeWFStrong ctx G Psi hPsi hCat hSound
      P GammaOut hType rho hrho)

-- ============================================================
--  Projection soundness (Theorem 6.3) -- foundations
--
--  A projection list is evaluated by concatenating the per-item records
--  (`projectRecord = pis.flatMap (projectItem ...)`) and typed by the disjoint
--  union of the per-item schemas. These lemmas give the conformance combinator
--  for that concatenation and the admissibility of table-level aggregates, which
--  the per-item / list-level projection soundness will build on.
-- ============================================================

/-- Looking up a key bound in the left record reads the left value, regardless of
    what is appended on the right (the `find?` hits the left list first). -/
theorem Record.append_lookup_left (rho1 rho2 : Record) (x : Name) (hx : rho1.mem x = true) :
    (rho1 ++ rho2).lookup x = rho1.lookup x := by
  show (match (rho1 ++ rho2).find? (fun e => e.1 == x) with | some (_, v) => v | none => .null)
     = (match rho1.find? (fun e => e.1 == x) with | some (_, v) => v | none => .null)
  rw [List.find?_append]
  cases hf : rho1.find? (fun e => e.1 == x) with
  | some e => rfl
  | none =>
    exfalso
    rw [List.find?_eq_none] at hf
    obtain ⟨y, hy, hpy⟩ := List.any_eq_true.mp (hx : rho1.any (fun e => e.1 == x) = true)
    exact hf y hy hpy

/-- Looking up a key absent from the left record falls through to the right. -/
theorem Record.append_lookup_right (rho1 rho2 : Record) (x : Name) (hx : rho1.mem x = false) :
    (rho1 ++ rho2).lookup x = rho2.lookup x := by
  show (match (rho1 ++ rho2).find? (fun e => e.1 == x) with | some (_, v) => v | none => .null)
     = (match rho2.find? (fun e => e.1 == x) with | some (_, v) => v | none => .null)
  rw [List.find?_append]
  have hany : rho1.any (fun e => e.1 == x) = false := hx
  have hnone : rho1.find? (fun e => e.1 == x) = none := by
    rw [List.find?_eq_none]
    intro y hy hpy
    have hmem : rho1.any (fun e => e.1 == x) = true := List.any_eq_true.mpr ⟨y, hy, hpy⟩
    rw [hmem] at hany; exact Bool.noConfusion hany
  rw [hnone, Option.none_or]

/-- Membership in an appended record is membership in either side. -/
theorem Record.append_mem (rho1 rho2 : Record) (x : Name) :
    (rho1 ++ rho2).mem x = (rho1.mem x || rho2.mem x) := by
  show ((rho1 ++ rho2).any (fun e => e.1 == x))
     = (rho1.any (fun e => e.1 == x) || rho2.any (fun e => e.1 == x))
  rw [List.any_append]

/-- Membership in a disjoint union of schemas is membership in either side. -/
theorem RecordSchema.disjointUnion_mem (G1 G2 : RecordSchema) (x : Name) :
    (G1.disjointUnion G2).mem x = (G1.mem x || G2.mem x) := by
  show ((G1.entries ++ G2.entries).any (fun e => e.1 == x))
     = (G1.entries.any (fun e => e.1 == x) || G2.entries.any (fun e => e.1 == x))
  rw [List.any_append]

/-- Conformance of a disjoint union of records: if `r1 ⊨ G1`, `r2 ⊨ G2`, and the
    schema domains are disjoint, the concatenation `r1 ++ r2` conforms to
    `G1 ⊎ G2`. This is the per-projection-list combinator: each projection's
    record conforms to its schema, and the whole list conforms to their disjoint
    union. Domain disjointness (from `disjointUnionCompatible`) is what lets the
    right-hand entries read through the left record cleanly. -/
theorem disjointUnion_recordConforms (r1 r2 : Record) (G1 G2 : RecordSchema)
    (h1 : RecordConforms r1 G1) (h2 : RecordConforms r2 G2)
    (hcompat : RecordSchema.disjointUnionCompatible G1 G2 = true) :
    RecordConforms (r1 ++ r2) (G1.disjointUnion G2) := by
  obtain ⟨hdom1, hval1⟩ := h1
  obtain ⟨hdom2, hval2⟩ := h2
  refine ⟨?_, ?_⟩
  · -- domain equality
    intro x
    rw [Record.append_mem, RecordSchema.disjointUnion_mem, hdom1 x, hdom2 x]
  · -- value admissibility, by which side the entry came from
    intro x t hxt
    have hmem : (x, t) ∈ G1.entries ++ G2.entries := hxt
    rcases List.mem_append.mp hmem with hin1 | hin2
    · -- entry from G1: x ∈ dom G1 = dom r1, lookup reads r1
      have hxG1 : G1.mem x = true :=
        List.any_eq_true.mpr ⟨(x, t), hin1, beq_self_eq_true x⟩
      have hxr1 : r1.mem x = true := by rw [hdom1 x]; exact hxG1
      rw [Record.append_lookup_left _ _ _ hxr1]
      exact hval1 x t hin1
    · -- entry from G2: disjointness gives x ∉ dom G1 = dom r1, lookup reads r2
      have hxG2 : G2.mem x = true :=
        List.any_eq_true.mpr ⟨(x, t), hin2, beq_self_eq_true x⟩
      have hxG1false : G1.mem x = false := by
        cases hb : G1.mem x with
        | false => rfl
        | true =>
          exfalso
          unfold RecordSchema.disjointUnionCompatible at hcompat
          have hx1 : x ∈ G1.dom := by
            unfold RecordSchema.dom
            rcases List.any_eq_true.mp (hb : G1.entries.any (fun e => e.1 == x) = true)
              with ⟨e, hemem, heq⟩
            have hex : e.1 = x := eq_of_beq heq
            rw [← hex]; exact List.mem_map_of_mem Prod.fst hemem
          have hx2 : G2.dom.any (fun y => y == x) = true := by
            rcases List.any_eq_true.mp (hxG2 : G2.entries.any (fun e => e.1 == x) = true)
              with ⟨e, hemem, heq⟩
            refine List.any_eq_true.mpr ⟨e.1, ?_, heq⟩
            unfold RecordSchema.dom; exact List.mem_map_of_mem Prod.fst hemem
          have hcontra := List.all_eq_true.mp hcompat x hx1
          rw [hx2] at hcontra; exact Bool.noConfusion hcontra
      have hxr1false : r1.mem x = false := by rw [hdom1 x]; exact hxG1false
      rw [Record.append_lookup_right _ _ _ hxr1false]
      exact hval2 x t hin2

/-- A `count` aggregate over any list of values is an integer, hence admissible
    for the non-nullable `Int`. -/
private theorem evalAggOnValues_count_admissible (qual : AggQualifier) (vals : List Value) :
    RecordSchema.valueAdmissible (evalAggOnValues .count qual vals) GSort.int = true := by
  simp only [evalAggOnValues]
  exact int_admissible_int _

/-- Every aggregate over a list of values is an integer or `Null`, hence
    admissible for the nullable `Int?`. (`count` yields `.ofInt`; `sum`/`max`/`min`
    yield `.ofInt` or `.null`.) -/
private theorem evalAggOnValues_admissible_intN (op : AggOp) (qual : AggQualifier)
    (vals : List Value) :
    RecordSchema.valueAdmissible (evalAggOnValues op qual vals) GSort.intN = true := by
  cases op <;> simp only [evalAggOnValues] <;> (try split) <;>
    first | exact int_admissible_intN _ | exact null_admissible_intN

/-- A table-level aggregate is admissible for the type the checker assigns to the
    corresponding `.agg` expression. By induction on the aggregate's typing: the
    four `count`/`agg` rules give `Int`/`Int?` (discharged by the `evalAggOnValues`
    leaves, independent of which record list is aggregated), `subsume` widens via
    `admissible_mono`, and the non-aggregate rules cannot derive an `.agg`
    expression (`Expr.noConfusion` on the generalized term equation). This is what
    discharges the `hAgg` obligation of `projectionList_sound`. -/
private theorem aggTable_admissible
    {ctx : TypingCtx} {Ctx : RecordSchema} {box : AggDepth} {hat : RefCtx}
    {op : AggOp} {qual : AggQualifier} {e : Expr} {tau : GSort} {omega' : VarSet}
    (hType : ExprTyping ctx Ctx box hat (.agg op qual e) tau omega')
    (vals : List Value) :
    RecordSchema.valueAdmissible (evalAggOnValues op qual vals) tau = true := by
  generalize hE : Expr.agg op qual e = E at hType
  induction hType using ExprTyping.inductionOpaque with
  | countSingleton =>
      injection hE with ho hq _; subst ho; subst hq
      exact evalAggOnValues_count_admissible _ _
  | aggSingleton =>
      injection hE with ho hq _; subst ho; subst hq
      exact evalAggOnValues_admissible_intN _ _ _
  | countGroup =>
      injection hE with ho hq _; subst ho; subst hq
      exact evalAggOnValues_count_admissible _ _
  | aggGroup =>
      injection hE with ho hq _; subst ho; subst hq
      exact evalAggOnValues_admissible_intN _ _ _
  | subsume =>
      rename_i _ hSub ih
      exact admissible_mono _ _ _ (ih hE) hSub
  | constInt => exact Expr.noConfusion hE
  | constString => exact Expr.noConfusion hE
  | constBool => exact Expr.noConfusion hE
  | constNull => exact Expr.noConfusion hE
  | var => exact Expr.noConfusion hE
  | arithOp => exact Expr.noConfusion hE
  | propAccessOpen => exact Expr.noConfusion hE
  | propAccessSchema => exact Expr.noConfusion hE
  | propAccessListOpen => exact Expr.noConfusion hE
  | propAccessListClosed => exact Expr.noConfusion hE
  | pred => exact Expr.noConfusion hE

/-- A one-entry record conforms to its one-entry schema exactly when the bound
    value inhabits the declared type. Every projection item produces such a
    singleton (`[(name, v)]` against `[(name, tau)]`), so this is the leaf of the
    per-item conformance. -/
theorem singleton_recordConforms (key : Name) (v : Value) (tau : GSort)
    (hadm : RecordSchema.valueAdmissible v tau = true) :
    RecordConforms [(key, v)] (RecordSchema.mk [(key, tau)]) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro y t hyt
  rw [List.mem_singleton] at hyt
  obtain ⟨hy, ht⟩ := Prod.mk.injEq .. ▸ hyt
  rw [hy, ht]
  show RecordSchema.valueAdmissible (Record.lookup [(key, v)] key) tau = true
  simp only [Record.lookup, List.find?, beq_self_eq_true]
  exact hadm

/-- Projection-list conformance (per record). Given that every projection
    item's record conforms to its schema (`hItem`), the concatenation produced by
    `projectRecord` conforms to the disjoint union the type-checker assigns. The
    `nil` case is the empty record against the empty schema; `cons` glues the head
    item and the tail via `disjointUnion_recordConforms`. `hItem` (atom / alias /
    aggregate item soundness) is the remaining obligation. -/
theorem projectionList_recordConforms
    (G : PropertyGraph) (site : GraphSite) (rho : Record) (matched : BindingTable)
    (ctx : TypingCtx) (Gamma1 : RecordSchema)
    (hItem : ∀ (pi : Projection) (Gpi : RecordSchema),
        ProjectionTyping ctx Gamma1 pi Gpi →
        RecordConforms (projectItem G site rho matched pi) Gpi)
    (pis : ProjectionList) (Gamma2 : RecordSchema)
    (hType : ProjectionListTyping ctx Gamma1 pis Gamma2) :
    RecordConforms (projectRecord G site rho matched pis) Gamma2 := by
  induction hType with
  | nil => exact ⟨fun _ => rfl, fun _ t h => absurd h (List.not_mem_nil _)⟩
  | cons pi pis Gpi Ctxrest hProj hRest hDisjoint ih =>
      show RecordConforms
        (projectItem G site rho matched pi ++ projectRecord G site rho matched pis)
        (Gpi.disjointUnion Ctxrest)
      exact disjointUnion_recordConforms _ _ Gpi Ctxrest (hItem pi Gpi hProj) ih hDisjoint

/-- Projection soundness (discharges `hProjSound`). Mapping the projection
    over a conforming matched table yields a table conforming to the projected
    schema. Per record, `projectionList_recordConforms` reduces to per-item
    soundness; the variable item (`Prj-Atom`) is `conform_lookup`, the aliased
    expression item (`Prj-Alias`) is Expression Soundness (Thm 6.1), and the
    aggregate item (`Prj-Agg-Alias`) is `aggTable_admissible`. `hWF`/`hRtWF` are
    Thm 6.1's well-formedness premises -- `hRtWF` is the graph-aware conformance
    Pattern Soundness establishes for matched records. -/
theorem projectionList_sound
    (ctx : TypingCtx) (G : PropertyGraph)
    (hWF : GraphValuesWF G)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G)
    (Gamma1 Gamma2 : RecordSchema) (pis : ProjectionList) (matched : BindingTable)
    (hMatched : BTConforms matched Gamma1)
    (hRtWF : ∀ rho, rho ∈ matched → RuntimeConfigWF G rho Gamma1)
    (hType : ProjectionListTyping ctx Gamma1 pis Gamma2) :
    BTConforms
      (matched.map (fun rho => projectRecord G ctx.graphSite rho matched pis)) Gamma2 := by
  intro projRho hprojmem
  rw [List.mem_map] at hprojmem
  obtain ⟨rho, hrhomem, rfl⟩ := hprojmem
  refine projectionList_recordConforms G ctx.graphSite rho matched ctx Gamma1 ?_ pis Gamma2 hType
  intro pi Gpi hProj
  cases hProj with
  | atom x tau hLookup =>
      apply singleton_recordConforms
      exact conform_lookup rho Gamma1 x tau (hMatched rho hrhomem) hLookup
  | alias' e x tau omega' hExpr =>
      apply singleton_recordConforms
      exact expressionSoundness ctx Gamma1 .one .group e tau omega' hExpr
        rho G (hMatched rho hrhomem) hWF (hRtWF rho hrhomem) hGraph
  | aggAs op qual e y tau omega' hExpr =>
      apply singleton_recordConforms
      exact aggTable_admissible hExpr _

-- ============================================================
--  Composite query / set-op soundness (Corollary 6.1) -- foundations
--
--  For the left-biased operators (`except`/`intersect`), every output record
--  comes from `B1`, and the combined schema is `Γ1`, so conformance follows
--  directly from `B1 ⊨ Γ1` and the existing filter/dist/bag-difference
--  preservation lemmas (the right table only appears in a membership predicate).
--  The `union` case (output `schemaUnion Γ1 Γ2`) and the `otherwise` case are
--  isolated as hypotheses: `union` needs the `sortUnion` widening (built next),
--  and `otherwise` is the flagged fidelity concern (its left-biased combine `Γ1`
--  does not cover the right bag returned when `B1` is empty).
-- ============================================================

section UnionWidening
open RecordSchema

/-! ## Step 1: `hasExtSort` respects `==` on `ExtSort`.

  `hasExtSort` only reads the value's constructor and the type's graph-site /
  base-sort -- it ignores the schema list -- so two beq-equal `ExtSort`s give the
  same answer even though the schema types are not `LawfulBEq`. This is what lets
  the subsumption arm keep `ts2` (testing membership by `==`). -/
private theorem extGraphSite_beq {T : Type} [BEq T] {G G' : GraphSite} {ss ss' : T}
    (h : ((G == G') && (ss == ss')) = true) : G = G' :=
  eq_of_beq ((Bool.and_eq_true _ _).mp h).1

theorem hasExtSort_beq_congr (v : Value) (g : GraphSite) (x y : ExtSort)
    (h : (x == y) = true) : v.hasExtSort g x = v.hasExtSort g y := by
  cases x <;> cases y <;> (try exact absurd h Bool.false_ne_true)
  case scalar.scalar b b' =>
    cases b <;> cases b' <;>
      first | rfl | exact absurd h Bool.false_ne_true
  case node.node G G' =>
    have : G = G' := eq_of_beq h; subst this; rfl
  case edge.edge G G' =>
    have : G = G' := eq_of_beq h; subst this; rfl
  case nodeRefined.nodeRefined G ss G' ss' =>
    have : G = G' := extGraphSite_beq h; subst this; cases v <;> rfl
  case edgeRefined.edgeRefined G ss G' ss' =>
    have : G = G' := extGraphSite_beq h; subst this; cases v <;> rfl

/-- `List.any (hasExtSort v g ·)` respects `==` on the element list. -/
theorem any_hasExtSort_beq_congr (v : Value) (g : GraphSite) :
    ∀ (ts1 ts2 : List ExtSort), (ts1 == ts2) = true →
      ts1.any (fun es => v.hasExtSort g es) = ts2.any (fun es => v.hasExtSort g es)
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp [List.instBEq, List.beq])
  | _ :: _, [], h => absurd h (by simp [List.instBEq, List.beq])
  | a :: as, b :: bs, h => by
      have h2 : ((a == b) && (as == bs)) = true := h
      obtain ⟨hab, hrest⟩ := (Bool.and_eq_true _ _).mp h2
      simp only [List.any_cons]
      rw [hasExtSort_beq_congr v g a b hab, any_hasExtSort_beq_congr v g as bs hrest]

/-- A beq-membership hit plus a `hasExtSort` witness for the matched element
    gives a genuine `hasExtSort` hit in the list (the subsumption-arm crux). -/
theorem any_hasExtSort_of_any_beq (v : Value) (g : GraphSite) (s : ExtSort) :
    ∀ (ts : List ExtSort), ts.any (fun x => x == s) = true → v.hasExtSort g s = true →
      ts.any (fun es => v.hasExtSort g es) = true
  | [], h, _ => absurd h (by simp)
  | a :: as, h, hs => by
      simp only [List.any_cons] at h ⊢
      rcases Bool.or_eq_true _ _ |>.mp h with hh | ht
      · rw [hasExtSort_beq_congr v g a s hh, hs]; rfl
      · rw [any_hasExtSort_of_any_beq v g s as ht hs]; exact Bool.or_true _

/-- `valueAdmissible` respects `==` on `GSort` (which is not `LawfulBEq` because
    the embedded schema lists are not). Needed for the `t1 == t2` arm of the
    union. -/
theorem valueAdmissible_beq_congr (v : Value) (t1 t2 : GSort)
    (h : (t1 == t2) = true) :
    RecordSchema.valueAdmissible v t1 = RecordSchema.valueAdmissible v t2 := by
  obtain ⟨s1, n1⟩ := t1
  obtain ⟨s2, n2⟩ := t2
  have hsn : ((s1 == s2) && (n1 == n2)) = true := h
  obtain ⟨hs, hn⟩ := (Bool.and_eq_true _ _).mp hsn
  have hnn : n1 = n2 := by
    cases n1 <;> cases n2 <;> first | rfl | exact absurd hn Bool.false_ne_true
  subst hnn
  cases s1 <;> cases s2 <;> (try (exact absurd hs Bool.false_ne_true))
  case single.single e1 e2 =>
    cases v <;> cases n1 <;>
      simp only [RecordSchema.valueAdmissible] <;>
      first | rfl | exact hasExtSort_beq_congr _ _ _ _ hs
  case any.any => rfl
  case bot.bot => rfl
  case nullType.nullType => rfl
  case list.list es1 m1 es2 m2 => cases v <;> cases n1 <;> rfl
  case emptyFormer.emptyFormer a1 b1 a2 b2 => rfl
  case union.union ts1 ts2 =>
    rcases ts1 with _ | ⟨a, as⟩ <;> rcases ts2 with _ | ⟨b, bs⟩
    · cases v <;> cases n1 <;> rfl
    · exact absurd hs Bool.false_ne_true
    · exact absurd hs Bool.false_ne_true
    · have hs' : ((a :: as) == (b :: bs)) = true := hs
      cases v <;> cases n1 <;>
        simp only [RecordSchema.valueAdmissible] <;>
        first | rfl | exact any_hasExtSort_beq_congr _ _ _ _ hs'

/-! ## Step 2: widening helpers. -/

/-- Everything is admissible for the top type `any`. -/
theorem va_any (v : Value) : RecordSchema.valueAdmissible v GSort.any = true := by
  cases v <;> rfl

/-- Widen the null tag to `nullable`. -/
theorem subtype_null_widen (s : SortShape) (n : NullTag) :
    Subtype ⟨s, n⟩ ⟨s, .nullable⟩ := by
  cases n
  · exact .nullable s
  · exact .refl _
  · exact .nullSingleton s

theorem va_toNullable_of_va (v : Value) (t : GSort)
    (h : RecordSchema.valueAdmissible v t = true) :
    RecordSchema.valueAdmissible v t.toNullable = true := by
  obtain ⟨s, n⟩ := t
  exact admissible_mono v _ _ h (subtype_null_widen s n)

/-- A single sort whose element is a genuine member of a list widens into the
    (nullable) union over that list. -/
theorem va_single_into_union_mem (v : Value) (s : ExtSort) (ts : List ExtSort)
    (n : NullTag) (hmem : s ∈ ts)
    (h : RecordSchema.valueAdmissible v ⟨.single s, n⟩ = true) :
    RecordSchema.valueAdmissible v ⟨.union ts, .nullable⟩ = true :=
  admissible_mono v _ _ h
    (.trans (subtype_null_widen (.single s) n) (.unionL ts s .nullable hmem))

/-- A union widens into any (nullable) super-union. -/
theorem va_union_into_superunion (v : Value) (ts1 ts2 : List ExtSort) (n : NullTag)
    (hsubset : ∀ t, t ∈ ts1 → t ∈ ts2)
    (h : RecordSchema.valueAdmissible v ⟨.union ts1, n⟩ = true) :
    RecordSchema.valueAdmissible v ⟨.union ts2, .nullable⟩ = true :=
  admissible_mono v _ _ h
    (.unionElim ts1 n _ fun t ht =>
      .trans (subtype_null_widen (.single t) n) (.unionL ts2 t .nullable (hsubset t ht)))

/-- The subsumption-arm crux (gated on the `sortUnion` fix): when `s1` is
    `==`-subsumed by `ts2`, a `single s1` value widens into the union over `ts2`
    carrying the JOINED null tag `looserNull n1 n2` (not one operand's tag). -/
theorem va_single_into_subsumed_union (v : Value) (s1 : ExtSort) (ts2 : List ExtSort)
    (n1 n2 : NullTag) (hsub : ts2.any (fun x => x == s1) = true)
    (h : RecordSchema.valueAdmissible v ⟨.single s1, n1⟩ = true) :
    RecordSchema.valueAdmissible v ⟨.union ts2, looserNull n1 n2⟩ = true := by
  obtain ⟨a, as, rfl⟩ : ∃ a as, ts2 = a :: as := by
    cases ts2 with
    | nil => simp at hsub
    | cons a as => exact ⟨a, as, rfl⟩
  by_cases hv : v = Value.null
  · subst hv
    have hn1 : n1 = .nullable ∨ n1 = .null := by
      cases n1 <;> simp_all [RecordSchema.valueAdmissible]
    rcases hn1 with rfl | rfl <;> cases n2 <;>
      simp [RecordSchema.valueAdmissible, looserNull]
  · have hhs : v.hasExtSort "" s1 = true ∧ n1 ≠ .null := by
      cases v <;> cases n1 <;> simp_all [RecordSchema.valueAdmissible]
    obtain ⟨hext, hn1⟩ := hhs
    have hany : (a :: as).any (fun es => v.hasExtSort "" es) = true :=
      any_hasExtSort_of_any_beq v "" s1 (a :: as) hsub hext
    cases n1 <;> cases n2 <;>
      simp_all [RecordSchema.valueAdmissible, looserNull]

theorem looserNull_comm (n1 n2 : NullTag) : looserNull n1 n2 = looserNull n2 n1 := by
  cases n1 <;> cases n2 <;> rfl

theorem subtype_looserNull_left (s : SortShape) (n n' : NullTag) :
    Subtype ⟨s, n⟩ ⟨s, looserNull n n'⟩ := by
  cases n <;> cases n' <;>
    first | exact .refl _ | exact .nullable s | exact .nullSingleton s

theorem va_relax_looserNull_left (v : Value) (s : SortShape) (n n' : NullTag)
    (h : RecordSchema.valueAdmissible v ⟨s, n⟩ = true) :
    RecordSchema.valueAdmissible v ⟨s, looserNull n n'⟩ = true :=
  admissible_mono v _ _ h (subtype_looserNull_left s n n')

/-- Arm-8 subsumption for the RIGHT operand: a `single s2` subsumed by `ts1`
    widens into the union over `ts1` with the joined tag. -/
theorem va_single_into_subsumed_union' (v : Value) (s2 : ExtSort) (ts1 : List ExtSort)
    (n1 n2 : NullTag) (hsub : ts1.any (fun x => x == s2) = true)
    (h : RecordSchema.valueAdmissible v ⟨.single s2, n2⟩ = true) :
    RecordSchema.valueAdmissible v ⟨.union ts1, looserNull n1 n2⟩ = true := by
  rw [looserNull_comm]
  exact va_single_into_subsumed_union v s2 ts1 n2 n1 hsub h

/-- `null` is admissible for a nonempty union made nullable. -/
theorem va_null_union_nullable (lst : List ExtSort) (n : NullTag) (h : lst ≠ []) :
    RecordSchema.valueAdmissible Value.null (⟨.union lst, n⟩ : GSort).toNullable = true := by
  cases lst with
  | nil => exact absurd rfl h
  | cons a as => rfl

theorem subtype_looserNull_right (s : SortShape) (n n' : NullTag) :
    Subtype ⟨s, n⟩ ⟨s, looserNull n' n⟩ := by
  rw [looserNull_comm]; exact subtype_looserNull_left s n n'

theorem va_relax_looserNull_right (v : Value) (s : SortShape) (n n' : NullTag)
    (h : RecordSchema.valueAdmissible v ⟨s, n⟩ = true) :
    RecordSchema.valueAdmissible v ⟨s, looserNull n' n⟩ = true :=
  admissible_mono v _ _ h (subtype_looserNull_right s n n')

/-- The union-union RIGHT crux: an element of `ts2` is covered by `merged`
    either directly (it survives the filter) or by a beq-equal element of `ts1`. -/
theorem any_hasExtSort_append_filter (v : Value) (g : GraphSite) (ts1 ts2 : List ExtSort)
    (h : ts2.any (fun es => v.hasExtSort g es) = true) :
    (ts1 ++ ts2.filter (fun t => !ts1.any (fun x => x == t))).any
      (fun es => v.hasExtSort g es) = true := by
  rw [List.any_eq_true] at h
  obtain ⟨t, ht, hpt⟩ := h
  rw [List.any_eq_true]
  by_cases hc : ts1.any (fun x => x == t) = true
  · rw [List.any_eq_true] at hc
    obtain ⟨t', ht', htt'⟩ := hc
    exact ⟨t', List.mem_append_left _ ht', by rw [hasExtSort_beq_congr v g t' t htt']; exact hpt⟩
  · refine ⟨t, List.mem_append_right _ ?_, hpt⟩
    rw [List.mem_filter]
    exact ⟨ht, by simp only [Bool.not_eq_true] at hc; simp [hc]⟩

/-- For a non-null value and non-null tag, union admissibility is exactly
    membership-by-`hasExtSort` (the `union []` guard agrees with `any []`). -/
theorem va_union_nonnull_eq (v : Value) (ts : List ExtSort) (n : NullTag)
    (hv : v ≠ Value.null) (hn : n ≠ .null) :
    RecordSchema.valueAdmissible v ⟨.union ts, n⟩ = ts.any (fun es => v.hasExtSort "" es) := by
  cases ts <;> cases v <;> cases n <;> simp_all [RecordSchema.valueAdmissible]

theorem va_union_into_merged (v : Value) (ts1 ts2 : List ExtSort) (n2 : NullTag)
    (h : RecordSchema.valueAdmissible v ⟨.union ts2, n2⟩ = true) :
    RecordSchema.valueAdmissible v
      ⟨.union (ts1 ++ ts2.filter (fun t => !ts1.any (fun x => x == t))), .nullable⟩ = true := by
  by_cases hv : v = Value.null
  · subst hv
    have hts2 : ts2 ≠ [] := by rintro rfl; simp [RecordSchema.valueAdmissible] at h
    have hmne : ts1 ++ ts2.filter (fun t => !ts1.any (fun x => x == t)) ≠ [] := by
      cases ts1 with
      | cons b bs => simp
      | nil =>
          simp only [List.nil_append, List.any_nil, Bool.not_false]
          cases ts2 with
          | nil => exact absurd rfl hts2
          | cons a as => simp
    cases hm : ts1 ++ ts2.filter (fun t => !ts1.any (fun x => x == t)) with
    | nil => exact absurd hm hmne
    | cons a as => rfl
  · have hn2 : n2 ≠ .null := by
      rintro rfl; cases v <;> cases ts2 <;> simp_all [RecordSchema.valueAdmissible]
    rw [va_union_nonnull_eq v ts2 n2 hv hn2] at h
    rw [va_union_nonnull_eq v _ .nullable hv (by simp)]
    exact any_hasExtSort_append_filter v "" ts1 ts2 h

/-! ## Step 3: the UNION widening, both directions (union [] is treated as
    bottom, so no properness side condition is needed). -/

/-- Close a `v = null` admissibility goal where the result type is `t.toNullable`
    (nullable, shape not an empty union / bottom). -/
private theorem va_null_toNullable_nonbot {v : Value} (hv : v = Value.null)
    (s : SortShape) (n : NullTag) (hs : s ≠ .union [] ∧ (∀ a b, s ≠ .emptyFormer a b) ∧ s ≠ .bot) :
    RecordSchema.valueAdmissible v (⟨s, n⟩ : GSort).toNullable = true := by
  subst hv; obtain ⟨h1, h2, h3⟩ := hs
  cases s with
  | single _ => rfl
  | nullType => rfl
  | list _ _ => rfl
  | any => rfl
  | union ts => cases ts with
                | nil => exact absurd rfl h1
                | cons _ _ => rfl
  | emptyFormer a b => exact absurd rfl (h2 a b)
  | bot => exact absurd rfl h3

theorem sortUnion_adm_left (v : Value) (t1 t2 : GSort)
    (h : RecordSchema.valueAdmissible v t1 = true) :
    RecordSchema.valueAdmissible v (sortUnion t1 t2) = true := by
  unfold sortUnion
  split
  · exact h
  · obtain ⟨s1, n1⟩ := t1
    obtain ⟨s2, n2⟩ := t2
    cases s1 with
    | emptyFormer _ _ => revert h; simp [RecordSchema.valueAdmissible]
    | bot => revert h; simp [RecordSchema.valueAdmissible]
    | any =>
      cases s2 with
      | emptyFormer _ _ => exact h
      | bot => exact h
      | union ts2 => rcases ts2 with _ | ⟨a, as⟩
                     · exact h
                     · exact va_any v
      | _ => exact va_any v
    | nullType =>
      have hvnull : v = Value.null := by cases v <;> cases n1 <;> simp_all [RecordSchema.valueAdmissible]
      cases s2 with
      | emptyFormer _ _ => exact h
      | bot => exact h
      | any => exact va_any v
      | union ts2 => rcases ts2 with _ | ⟨a, as⟩
                     · exact h
                     · subst hvnull; exact va_null_union_nullable _ _ (List.cons_ne_nil _ _)
      | single e2 => exact va_null_toNullable_nonbot hvnull _ n2 (by simp)
      | nullType => exact va_null_toNullable_nonbot hvnull _ n2 (by simp)
      | list _ _ => exact va_null_toNullable_nonbot hvnull _ n2 (by simp)
    | list _ _ =>
      cases s2 with
      | emptyFormer _ _ => exact h
      | bot => exact h
      | any => exact va_any v
      | nullType => exact va_toNullable_of_va v _ h
      | union ts2 => rcases ts2 with _ | ⟨a, as⟩
                     · exact h
                     · exact va_any v
      | _ => exact va_any v
    | single e1 =>
      cases s2 with
      | emptyFormer _ _ => exact h
      | bot => exact h
      | any => exact va_any v
      | nullType => exact va_toNullable_of_va v _ h
      | single e2 => exact va_single_into_union_mem v e1 [e1, e2] n1 (by simp) h
      | list _ _ => exact va_any v
      | union ts2 => rcases ts2 with _ | ⟨a, as⟩
                     · exact h
                     · dsimp only
                       split
                       · exact va_single_into_subsumed_union v e1 (a :: as) n1 n2 (by assumption) h
                       · exact va_single_into_union_mem v e1 (e1 :: a :: as) n1 (by simp) h
    | union ts1 =>
      rcases ts1 with _ | ⟨a1, as1⟩
      · revert h; simp [RecordSchema.valueAdmissible]
      · cases s2 with
        | emptyFormer _ _ => exact h
        | bot => exact h
        | any => exact va_any v
        | nullType => exact va_toNullable_of_va v _ h
        | list _ _ => exact va_any v
        | single e2 => dsimp only
                       split
                       · exact va_relax_looserNull_left v _ _ _ h
                       · refine va_union_into_superunion v (a1 :: as1) _ _ ?_ h
                         intro t ht; exact List.mem_append_left _ ht
        | union ts2 => rcases ts2 with _ | ⟨a2, as2⟩
                       · exact h
                       · refine va_union_into_superunion v (a1 :: as1) _ _ ?_ h
                         intro t ht; exact List.mem_append_left _ ht

/-- `sortUnion` is an upper bound on its RIGHT operand. The
    `t1.shape ≠ union []` side condition mirrors the left version. -/
theorem sortUnion_adm_right (v : Value) (t1 t2 : GSort)
    (h : RecordSchema.valueAdmissible v t2 = true) :
    RecordSchema.valueAdmissible v (sortUnion t1 t2) = true := by
  unfold sortUnion
  split
  case isTrue hc => rw [valueAdmissible_beq_congr v t1 t2 hc]; exact h
  case isFalse _ =>
    obtain ⟨s1, n1⟩ := t1
    obtain ⟨s2, n2⟩ := t2
    cases s1 with
    | emptyFormer _ _ =>
      cases s2 with
      | union ts => cases ts <;> exact h
      | _ => exact h
    | bot =>
      cases s2 with
      | union ts => cases ts <;> exact h
      | _ => exact h
    | any =>
      cases s2 with
      | emptyFormer _ _ => revert h; simp [RecordSchema.valueAdmissible]
      | bot => revert h; simp [RecordSchema.valueAdmissible]
      | union ts2 => rcases ts2 with _ | ⟨a, as⟩
                     · revert h; simp [RecordSchema.valueAdmissible]
                     · exact va_any v
      | _ => exact va_any v
    | nullType =>
      cases s2 with
      | emptyFormer _ _ => revert h; simp [RecordSchema.valueAdmissible]
      | bot => revert h; simp [RecordSchema.valueAdmissible]
      | any => exact va_any v
      | union ts2 => rcases ts2 with _ | ⟨a, as⟩
                     · revert h; simp [RecordSchema.valueAdmissible]
                     · exact va_toNullable_of_va v _ h
      | single _ => exact va_toNullable_of_va v _ h
      | nullType => exact va_toNullable_of_va v _ h
      | list _ _ => exact va_toNullable_of_va v _ h
    | list _ _ =>
      cases s2 with
      | emptyFormer _ _ => revert h; simp [RecordSchema.valueAdmissible]
      | bot => revert h; simp [RecordSchema.valueAdmissible]
      | any => exact va_any v
      | nullType =>
        have hvnull : v = Value.null := by cases v <;> cases n2 <;> simp_all [RecordSchema.valueAdmissible]
        exact va_null_toNullable_nonbot hvnull _ n1 (by simp)
      | union ts2 => rcases ts2 with _ | ⟨a, as⟩
                     · revert h; simp [RecordSchema.valueAdmissible]
                     · exact va_any v
      | single _ => exact va_any v
      | list _ _ => exact va_any v
    | single e1 =>
      cases s2 with
      | emptyFormer _ _ => revert h; simp [RecordSchema.valueAdmissible]
      | bot => revert h; simp [RecordSchema.valueAdmissible]
      | any => exact va_any v
      | nullType =>
        have hvnull : v = Value.null := by cases v <;> cases n2 <;> simp_all [RecordSchema.valueAdmissible]
        exact va_null_toNullable_nonbot hvnull _ n1 (by simp)
      | list _ _ => exact va_any v
      | single e2 => exact va_single_into_union_mem v e2 [e1, e2] n2 (by simp) h
      | union ts2 => rcases ts2 with _ | ⟨a, as⟩
                     · revert h; simp [RecordSchema.valueAdmissible]
                     · dsimp only
                       split
                       · exact va_relax_looserNull_right v _ _ _ h
                       · refine va_union_into_superunion v (a :: as) _ _ ?_ h
                         intro t ht; exact List.mem_cons_of_mem _ ht
    | union ts1 =>
      rcases ts1 with _ | ⟨a1, as1⟩
      · cases s2 with
        | union ts => cases ts <;> exact h
        | _ => exact h
      · cases s2 with
        | emptyFormer _ _ => revert h; simp [RecordSchema.valueAdmissible]
        | bot => revert h; simp [RecordSchema.valueAdmissible]
        | any => exact va_any v
        | list _ _ => exact va_any v
        | nullType =>
          have hvnull : v = Value.null := by cases v <;> cases n2 <;> simp_all [RecordSchema.valueAdmissible]
          subst hvnull; exact va_null_union_nullable _ _ (List.cons_ne_nil _ _)
        | single e2 => dsimp only
                       split
                       · exact va_single_into_subsumed_union' v e2 (a1 :: as1) n1 n2 (by assumption) h
                       · refine va_single_into_union_mem v e2 _ n2 ?_ h; simp
        | union ts2 => rcases ts2 with _ | ⟨a2, as2⟩
                       · revert h; simp [RecordSchema.valueAdmissible]
                       · dsimp only
                         exact va_union_into_merged v (a1 :: as1) (a2 :: as2) n2 h

/-! ## Step 4: schema-level UNION conformance (the `hUnionOp` leaf shape).

  This threads the `unionCompatible` side condition (which the composite-query
  rule already carries) for the domain clause, plus the benign `union []`
  properness invariant on both schemas, and routes the admissibility clause
  through the two widenings above. -/


/-- The union schema's domain is the LEFT schema's domain. -/
theorem schemaUnion_mem (Ctx1 Ctx2 : RecordSchema) (x : Name) :
    (schemaUnion Ctx1 Ctx2).mem x = Ctx1.mem x := by
  unfold schemaUnion RecordSchema.mem
  dsimp only
  generalize Ctx1.entries = es
  induction es with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨k, t1⟩ := hd
      rw [List.map_cons, List.any_cons, List.any_cons, ih]
      congr 1
      cases Ctx2.lookup k <;> rfl

/-- Decompose membership in the union schema's entries. -/
theorem mem_schemaUnion {Ctx1 Ctx2 : RecordSchema} {x : Name} {t : GSort}
    (h : (x, t) ∈ (schemaUnion Ctx1 Ctx2).entries) :
    ∃ t1, (x, t1) ∈ Ctx1.entries ∧
      ((∃ t2, Ctx2.lookup x = some t2 ∧ t = sortUnion t1 t2) ∨
       (Ctx2.lookup x = none ∧ t = t1)) := by
  simp only [schemaUnion, List.mem_map] at h
  obtain ⟨⟨x', t1⟩, hmem, heq⟩ := h
  cases hl : Ctx2.lookup x' with
  | some t2 =>
      rw [hl] at heq; simp only [Prod.mk.injEq] at heq
      obtain ⟨hx, ht⟩ := heq; subst hx
      exact ⟨t1, hmem, Or.inl ⟨t2, hl, ht.symm⟩⟩
  | none =>
      rw [hl] at heq; simp only [Prod.mk.injEq] at heq
      obtain ⟨hx, ht⟩ := heq; subst hx
      exact ⟨t1, hmem, Or.inr ⟨hl, ht.symm⟩⟩

/-- `unionCompatible` equates the two domains (membership), via beq transitivity
    on the `LawfulBEq` name type. -/
theorem unionCompat_mem {Ctx1 Ctx2 : RecordSchema}
    (hc : RecordSchema.unionCompatible Ctx1 Ctx2 = true) (x : Name) :
    Ctx1.mem x = Ctx2.mem x := by
  simp only [RecordSchema.unionCompatible, Bool.and_eq_true] at hc
  obtain ⟨⟨_, hall12⟩, hall21⟩ := hc
  apply Bool.eq_iff_iff.mpr
  show Ctx1.entries.any (fun e => e.1 == x) = true ↔ Ctx2.entries.any (fun e => e.1 == x) = true
  rw [List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨e, hmem, hex⟩
    have hed1 : e.1 ∈ Ctx1.dom := List.mem_map_of_mem _ hmem
    obtain ⟨y, hy2, hye⟩ := List.any_eq_true.mp (List.all_eq_true.mp hall12 e.1 hed1)
    obtain ⟨ey, hey, hey1⟩ := List.mem_map.mp hy2
    refine ⟨ey, hey, ?_⟩
    have h1 : y = e.1 := eq_of_beq hye
    have h2 : e.1 = x := eq_of_beq hex
    show (ey.fst == x) = true
    rw [hey1, h1, h2]; exact beq_self_eq_true x
  · rintro ⟨e, hmem, hex⟩
    have hed2 : e.1 ∈ Ctx2.dom := List.mem_map_of_mem _ hmem
    obtain ⟨y, hy1, hye⟩ := List.any_eq_true.mp (List.all_eq_true.mp hall21 e.1 hed2)
    obtain ⟨ey, hey, hey1⟩ := List.mem_map.mp hy1
    refine ⟨ey, hey, ?_⟩
    have h1 : y = e.1 := eq_of_beq hye
    have h2 : e.1 = x := eq_of_beq hex
    show (ey.fst == x) = true
    rw [hey1, h1, h2]; exact beq_self_eq_true x

/-- The pre-staged `hUnionOp`: UNION set-op soundness against the fixed schema
    union, given union-compatibility and the (benign) properness invariant. -/
theorem schemaUnion_btconforms (B1 B2 : BindingTable) (Ctx1 Ctx2 : RecordSchema)
    (hc : RecordSchema.unionCompatible Ctx1 Ctx2 = true)
    (h1 : BTConforms B1 Ctx1) (h2 : BTConforms B2 Ctx2) :
    BTConforms (B1 ++ B2) (schemaUnion Ctx1 Ctx2) := by
  intro rho hrho
  rw [List.mem_append] at hrho
  refine ⟨fun y => ?_, fun x t hxt => ?_⟩
  · -- domain clause
    rw [schemaUnion_mem]
    rcases hrho with hB1 | hB2
    · exact (h1 rho hB1).1 y
    · rw [unionCompat_mem hc y]; exact (h2 rho hB2).1 y
  · -- admissibility clause
    obtain ⟨t1, ht1, hcase⟩ := mem_schemaUnion hxt
    have hmem2 : Ctx2.mem x = true := by rw [← unionCompat_mem hc]; exact RecordSchema.mem_of_entry ht1
    obtain ⟨t2, hl2⟩ := RecordSchema.mem_lookup_some hmem2
    have ht : t = sortUnion t1 t2 := by
      rcases hcase with ⟨t2', hl2', ht'⟩ | ⟨hnone, _⟩
      · have hee : t2' = t2 := Option.some.injEq _ _ |>.mp (hl2'.symm.trans hl2)
        rw [ht', hee]
      · rw [hl2] at hnone; exact absurd hnone (by simp)
    subst ht
    have ht2mem := RecordSchema.lookup_some_mem hl2
    rcases hrho with hB1 | hB2
    · exact sortUnion_adm_left _ t1 t2 ((h1 rho hB1).2 x t1 ht1)
    · exact sortUnion_adm_right _ t1 t2 ((h2 rho hB2).2 x t2 ht2mem)

/-! ## OTHERWISE combines to the schema union.

  Per CQ-Expression the composite combine is the uniform `Γ1 ⊗ Γ2`, and the
  heterogeneous-union motivation (Section 3.2 / Example 3.1) forces `⊗` to be the
  schema union. Once `opCombine .otherwise` is changed from `Γ1` to the schema
  union, the OTHERWISE leaf becomes provable by the same widening as UNION: the
  evaluator returns `B2` when `B1` is empty and `B1` otherwise, and each side
  widens into the union. We factor the two per-table widenings here. -/

/-- Widen a table conforming to the LEFT operand up to the fixed schema union. -/
theorem btconforms_widen_left (B : BindingTable) (Ctx1 Ctx2 : RecordSchema)
    (hc : RecordSchema.unionCompatible Ctx1 Ctx2 = true)
    (h1 : BTConforms B Ctx1) :
    BTConforms B (schemaUnion Ctx1 Ctx2) := by
  intro rho hrho
  refine ⟨fun y => ?_, fun x t hxt => ?_⟩
  · rw [schemaUnion_mem]; exact (h1 rho hrho).1 y
  · obtain ⟨t1, ht1, hcase⟩ := mem_schemaUnion hxt
    have hmem2 : Ctx2.mem x = true := by
      rw [← unionCompat_mem hc]; exact RecordSchema.mem_of_entry ht1
    obtain ⟨t2, hl2⟩ := RecordSchema.mem_lookup_some hmem2
    have ht : t = sortUnion t1 t2 := by
      rcases hcase with ⟨t2', hl2', ht'⟩ | ⟨hnone, _⟩
      · have hee : t2' = t2 := Option.some.injEq _ _ |>.mp (hl2'.symm.trans hl2)
        rw [ht', hee]
      · rw [hl2] at hnone; exact absurd hnone (by simp)
    subst ht
    have ht2mem := RecordSchema.lookup_some_mem hl2
    exact sortUnion_adm_left _ t1 t2 ((h1 rho hrho).2 x t1 ht1)

/-- Widen a table conforming to the RIGHT operand up to the fixed schema union. -/
theorem btconforms_widen_right (B : BindingTable) (Ctx1 Ctx2 : RecordSchema)
    (hc : RecordSchema.unionCompatible Ctx1 Ctx2 = true)
    (h2 : BTConforms B Ctx2) :
    BTConforms B (schemaUnion Ctx1 Ctx2) := by
  intro rho hrho
  refine ⟨fun y => ?_, fun x t hxt => ?_⟩
  · rw [schemaUnion_mem, unionCompat_mem hc y]; exact (h2 rho hrho).1 y
  · obtain ⟨t1, ht1, hcase⟩ := mem_schemaUnion hxt
    have hmem2 : Ctx2.mem x = true := by
      rw [← unionCompat_mem hc]; exact RecordSchema.mem_of_entry ht1
    obtain ⟨t2, hl2⟩ := RecordSchema.mem_lookup_some hmem2
    have ht : t = sortUnion t1 t2 := by
      rcases hcase with ⟨t2', hl2', ht'⟩ | ⟨hnone, _⟩
      · have hee : t2' = t2 := Option.some.injEq _ _ |>.mp (hl2'.symm.trans hl2)
        rw [ht', hee]
      · rw [hl2] at hnone; exact absurd hnone (by simp)
    subst ht
    have ht2mem := RecordSchema.lookup_some_mem hl2
    exact sortUnion_adm_right _ t1 t2 ((h2 rho hrho).2 x t2 ht2mem)

/-- The pre-staged `hOther` against the FIXED combine `schemaUnion Γ1 Γ2`
    `applySetOp .otherwise` returns `B2` when `B1` is empty and
    `B1` otherwise, so each branch widens into the union — exactly the
    "OTHERWISE introduces no non-conforming records" claim of Corollary 6.1,
    which the left-biased combine `Γ1` did NOT support. -/
theorem schemaUnion_otherwise_btconforms (B1 B2 : BindingTable) (Ctx1 Ctx2 : RecordSchema)
    (hc : RecordSchema.unionCompatible Ctx1 Ctx2 = true)
    (h1 : BTConforms B1 Ctx1) (h2 : BTConforms B2 Ctx2) :
    BTConforms (applySetOp .otherwise B1 B2) (schemaUnion Ctx1 Ctx2) := by
  show BTConforms (if B1.isEmpty then B2 else B1) (schemaUnion Ctx1 Ctx2)
  by_cases hB1 : B1.isEmpty = true
  · rw [if_pos hB1]; exact btconforms_widen_right B2 Ctx1 Ctx2 hc h2
  · rw [if_neg hB1]; exact btconforms_widen_left B1 Ctx1 Ctx2 hc h1

end UnionWidening

theorem setOp_conforms (op : SetOp) (B1 B2 : BindingTable) (Gamma1 Gamma2 : RecordSchema)
    (hCompat : opCompatible op Gamma1 Gamma2 = true)
    (h1 : BTConforms B1 Gamma1) (h2 : BTConforms B2 Gamma2) :
    BTConforms (applySetOp op B1 B2) (opCombine op Gamma1 Gamma2) := by
  cases op
  case union => exact schemaUnion_btconforms B1 B2 Gamma1 Gamma2 hCompat h1 h2
  case otherwise => exact schemaUnion_otherwise_btconforms B1 B2 Gamma1 Gamma2 hCompat h1 h2
  case exceptDistinct =>
    show BTConforms (dist (List.filter _ B1)) Gamma1
    exact dist_preserves _ Gamma1 (filter_preserves B1 Gamma1 _ h1)
  case exceptAll =>
    simp only [applySetOp]
    exact foldPairFst_preserves Gamma1 _
      (by intro st rho; obtain ⟨acc, rem⟩ := st; split
          · exact Or.inl rfl
          · exact Or.inr rfl)
      B1 h1 ([], B2) (fun _ habs => absurd habs (List.not_mem_nil _))
  case intersectDistinct =>
    show BTConforms (dist (List.filter _ B1)) Gamma1
    exact dist_preserves _ Gamma1 (filter_preserves B1 Gamma1 _ h1)
  case intersectAll =>
    simp only [applySetOp]
    exact foldPairFst_preserves Gamma1 _
      (by intro st rho; obtain ⟨acc, rem⟩ := st; split
          · exact Or.inr rfl
          · exact Or.inl rfl)
      B1 h1 ([], B2) (fun _ habs => absurd habs (List.not_mem_nil _))

-- ============================================================
--  Query Soundness (Theorem 6.3) / Composite Query Soundness
--  (Corollary 6.1), composed
--
--  These plug the three proven workhorses into the skeletons:
--    * hPatSound  := patExprSoundness        (Pattern Soundness, Theorem 6.2)
--    * hProjSound := projectionList_sound     (projection soundness)
--    * hSetOp     := setOp_conforms           (left-biased set ops, Corollary 6.1)
--  so the four coarse reductions of `queryTypeSoundness_assembled` are discharged
--  internally and only the genuinely-open LEAF obligations stay in the signature.
--  Relative to the `queryTypeSoundness` axiom (a flat unproven assertion), this is
--  the same conclusion reduced to exactly:
--    - the pattern fidelity gaps (`hQuantEmpty`/`hQuantEdgeStrong`, via
--      Theorem 6.2; the `?`/optional obligations are gone since `?` is unsupported,
--      the plain/strong step obligations are now proven, and the closed-fail
--      obligation is discharged by the rule's `S = ∅` premise),
--    - the graph-conformance well-formedness (`hCat`); the former naming-hygiene
--      side conditions `hH4`/`hQuantHygiene` are gone, discharged internally now
--      that the variable-length-path recursion uses a genuinely fresh edge name,
--    - the projection well-formedness (`hWF` graph values, and `hPatRtWF`, the
--      graph-aware runtime conformance Pattern Soundness gives for the records a
--      pattern actually produces -- not for arbitrary conforming tables, which
--      `BTConforms` being graph-free could not support),
--    - the graph-switch clause (`hUseGraph`, the catalog-wide recursion),
--    - and the two non-left-biased set ops (`hUnionOp` widening, `hOtherOp` the
--      flagged otherwise fidelity concern).
--  The axioms are kept until these close, but their content is now exhibited as a
--  composition of proven results rather than assumed outright.
-- ============================================================

theorem queryTypeSoundness_composed
    (ctx : TypingCtx) (G : PropertyGraph)
    (hCat : ∀ Psi, ctx.schemaMap.lookup ctx.graphSite = some Psi →
              graphConformsSchema G Psi = true)
    (Psi : GraphSchemaFull) (hPsi : ctx.schemaMap.lookup ctx.graphSite = some Psi)
    (hWF : GraphValuesWF G)
    (hUseGraph : ∀ (graphName : Name) (inner : Query) (GammaU : RecordSchema),
        (ctx.catalog.lookup graphName).isSome = true →
        QueryTyping { ctx with graphSite := graphName } inner GammaU →
        BTConforms (evalQuery ctx.catalog G ctx.graphSite (.useGraph graphName inner)) GammaU)
    (Q : Query) (Gamma : RecordSchema) (hType : QueryTyping ctx Q Gamma)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G) :
    BTConforms (evalQuery ctx.catalog G ctx.graphSite Q) Gamma := by
  have hSoundFn : ∀ (P : Pattern) (GammaOut : RecordSchema),
      PatExprTyping ctx P GammaOut →
      BTConforms (evalPattern G ctx.graphSite P) GammaOut :=
    fun P GammaOut hPE =>
      patExprSoundness ctx G hCat Psi hPsi
        (patternTyping_runtimeWFStrong ctx G Psi hPsi hCat)
        P GammaOut hPE hGraph
  exact queryTypeSoundness_assembled ctx G hSoundFn
    (patExpr_runtimeWF ctx G Psi hPsi hCat hSoundFn)
    (fun Gamma1 _Gamma2 _pis matched hMatched hMrt hPType =>
      projectionList_sound ctx G hWF hGraph Gamma1 _Gamma2 _pis matched hMatched
        hMrt hPType)
    hUseGraph
    (fun _op Q1 Q2 Gamma1 Gamma2 h1 h2 hCompat =>
      setOp_conforms _op _ _ Gamma1 Gamma2 hCompat h1 h2)
    Q Gamma hType hGraph

theorem compositeQuerySoundness_composed
    (ctx : TypingCtx) (G : PropertyGraph)
    (hCat : ∀ Psi, ctx.schemaMap.lookup ctx.graphSite = some Psi →
              graphConformsSchema G Psi = true)
    (Psi : GraphSchemaFull) (hPsi : ctx.schemaMap.lookup ctx.graphSite = some Psi)
    (hWF : GraphValuesWF G)
    (hUseGraph : ∀ (graphName : Name) (inner : Query) (GammaU : RecordSchema),
        (ctx.catalog.lookup graphName).isSome = true →
        QueryTyping { ctx with graphSite := graphName } inner GammaU →
        BTConforms (evalQuery ctx.catalog G ctx.graphSite (.useGraph graphName inner)) GammaU)
    (op : SetOp) (Q1 Q2 : Query) (Gamma1 Gamma2 : RecordSchema)
    (hType1 : QueryTyping ctx Q1 Gamma1)
    (hType2 : QueryTyping ctx Q2 Gamma2)
    (_hCompat : opCompatible op Gamma1 Gamma2 = true)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G) :
    BTConforms
      (applySetOp op
        (evalQuery ctx.catalog G ctx.graphSite Q1)
        (evalQuery ctx.catalog G ctx.graphSite Q2))
      (opCombine op Gamma1 Gamma2) := by
  have hQ1 := queryTypeSoundness_composed ctx G hCat
    Psi hPsi
    hWF hUseGraph
    Q1 Gamma1 hType1 hGraph
  have hQ2 := queryTypeSoundness_composed ctx G hCat
    Psi hPsi
    hWF hUseGraph
    Q2 Gamma2 hType2 hGraph
  exact setOp_conforms op _ _ Gamma1 Gamma2 _hCompat hQ1 hQ2

-- ============================================================
--  Query Soundness (Theorem 6.3), composed catalog-wide
--
--  Same composition as `queryTypeSoundness_composed`, but built on the
--  catalog-wide skeleton `queryTypeSoundness_catalogWide`, so the `use graph`
--  clause is discharged internally and there is NO `hUseGraph` obligation. The
--  three skeleton reductions are discharged exactly as in the fixed-graph
--  version: pattern soundness by `patExprSoundness`, projection soundness by
--  `projectionList_sound`, and the set operations by `setOp_conforms`. Because a
--  match runs at whatever site is in effect after any switches, the pattern,
--  projection, and well-formedness leaves are now quantified over the working
--  context and its resolved graph; the two set-operation leaves stay as
--  graph-independent table statements (no `evalQuery` wrapper). What remains is
--  exactly the author-side fidelity gaps plus the union/otherwise/runtime
--  well-formedness work; once those close, the `queryTypeSoundness` axiom can be
--  deleted. The composite (Corollary 6.1) catalog-wide form is the same theorem
--  instantiated at a `.composite` query (the fixed-graph
--  `compositeQuerySoundness_composed` already gives the Corollary 6.1 shape).
-- ============================================================

theorem queryTypeSoundness_composed_catalogWide
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
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G) :
    BTConforms (evalQuery ctx.catalog G ctx.graphSite Q) Gamma :=
  queryTypeSoundness_catalogWide
    (fun ctx' G' hG' P GammaOut hPE => by
      obtain ⟨Psi', hPsi'⟩ := hSchemaCat ctx' G' hG'
      exact patExprSoundness ctx' G' (hCat ctx' G' hG') Psi' hPsi'
        (patternTyping_runtimeWFStrong ctx' G' Psi' hPsi' (hCat ctx' G' hG'))
        P GammaOut hPE hG')
    (by
      intro ctx' G' hG' P GammaOut hPE rho hrho
      obtain ⟨Psi, hPsi⟩ := hSchemaCat ctx' G' hG'
      exact patExpr_runtimeWF ctx' G' Psi hPsi (hCat ctx' G' hG')
        (fun P' G'' hPE' =>
          patExprSoundness ctx' G' (hCat ctx' G' hG') Psi hPsi
            (patternTyping_runtimeWFStrong ctx' G' Psi hPsi (hCat ctx' G' hG'))
            P' G'' hPE' hG')
        P GammaOut hPE rho hrho)
    (fun ctx' G' hG' Gamma1 Gamma2 pis matched hMatched hMrt hPType =>
      projectionList_sound ctx' G' (hWF ctx' G' hG') hG' Gamma1 Gamma2 pis matched hMatched
        hMrt hPType)
    (fun op _Q1 _Q2 Gamma1 Gamma2 B1 B2 h1 h2 hCompat =>
      setOp_conforms op B1 B2 Gamma1 Gamma2 hCompat h1 h2)
    ctx G Q Gamma hType hGraph

/-- Query type soundness across mixed open and closed sites (P2, query
    layer). Strengthens `queryTypeSoundness_composed_catalogWide` by
    dropping the requirement that every resolvable site carries a schema:
    a site with a schema (closed) discharges through the refinement-aware
    machinery, a site without one (open) through the open-graph soundness
    theorems. -/
theorem queryTypeSoundness_composed_mixedSites
    (hCat : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' →
        ∀ Psi, ctx'.schemaMap.lookup ctx'.graphSite = some Psi →
          graphConformsSchema G' Psi = true)
    (hWF : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' → GraphValuesWF G')
    (ctx : TypingCtx) (G : PropertyGraph) (Q : Query) (Gamma : RecordSchema)
    (hType : QueryTyping ctx Q Gamma)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G) :
    BTConforms (evalQuery ctx.catalog G ctx.graphSite Q) Gamma := by
  refine queryTypeSoundness_catalogWide ?_ ?_ ?_ ?_ ctx G Q Gamma hType hGraph
  · intro ctx' G' hG' P GammaOut hPE
    cases hcl : ctx'.schemaMap.lookup ctx'.graphSite with
    | some Psi' =>
      exact patExprSoundness ctx' G' (hCat ctx' G' hG') Psi' hcl
        (patternTyping_runtimeWFStrong ctx' G' Psi' hcl (hCat ctx' G' hG'))
        P GammaOut hPE hG'
    | none =>
      exact patExprSoundness_open ctx' G'
        (by unfold SchemaMap.isClosed; rw [hcl]; rfl) P GammaOut hPE
  · intro ctx' G' hG' P GammaOut hPE rho hrho
    cases hcl : ctx'.schemaMap.lookup ctx'.graphSite with
    | some Psi' =>
      exact patExpr_runtimeWF ctx' G' Psi' hcl (hCat ctx' G' hG')
        (fun P' G'' hPE' =>
          patExprSoundness ctx' G' (hCat ctx' G' hG') Psi' hcl
            (patternTyping_runtimeWFStrong ctx' G' Psi' hcl (hCat ctx' G' hG'))
            P' G'' hPE' hG')
        P GammaOut hPE rho hrho
    | none =>
      exact patExpr_runtimeWF_open ctx' G'
        (by unfold SchemaMap.isClosed; rw [hcl]; rfl) hPE rho
  · intro ctx' G' hG' Gamma1 Gamma2 pis matched hMatched hMrt hPType
    exact projectionList_sound ctx' G' (hWF ctx' G' hG') hG' Gamma1 Gamma2 pis matched
      hMatched hMrt hPType
  · intro op _Q1 _Q2 Gamma1 Gamma2 B1 B2 h1 h2 hCompat
    exact setOp_conforms op B1 B2 Gamma1 Gamma2 hCompat h1 h2

/-- Composite query soundness across mixed sites (Corollary 6.1). -/
theorem compositeQuerySoundness_mixedSites
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
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G) :
    BTConforms
      (applySetOp op
        (evalQuery ctx.catalog G ctx.graphSite Q1)
        (evalQuery ctx.catalog G ctx.graphSite Q2))
      (opCombine op Gamma1 Gamma2) :=
  setOp_conforms op _ _ Gamma1 Gamma2 hCompat
    (queryTypeSoundness_composed_mixedSites hCat hWF ctx G Q1 Gamma1 hType1 hGraph)
    (queryTypeSoundness_composed_mixedSites hCat hWF ctx G Q2 Gamma2 hType2 hGraph)

-- ============================================================
--  Definition 6.1 value inhabitation
--
--  The paper's value typing checks more than `valueAdmissible`: list values
--  must have every ELEMENT inhabit the element type, and a graph element at
--  a schema-refined type must belong to one of the refined schemas (its
--  property map conforms to that schema's property schema). `ValueInhabits`
--  is the graph-indexed, Definition 6.1-faithful relation; `valueAdmissible`
--  stays untouched (it is deliberately graph-free, the whole typing side
--  depends on it). Refined membership is stated conditionally on the
--  reference being in bounds, mirroring `RuntimeConfigWF`; that references
--  denote actual graph elements is part of the ambient data-model
--  assumption, like `GraphValuesWF`.
-- ============================================================

/-- A node reference belongs to one of the refined node schemas. -/
def NodeRefMember (G : PropertyGraph) (n : Nat) (ss : List NodeSchemaFull) : Prop :=
  ∀ hn : n < G.numNodes, ∃ ns, ns ∈ ss ∧
    propMapConformsSchema (G.nodeProps ⟨n, hn⟩) ns.propSchema = true

/-- An edge reference belongs to one of the refined edge schemas. -/
def EdgeRefMember (G : PropertyGraph) (ed : Nat) (ss : List EdgeSchemaFull) : Prop :=
  ∀ he : ed < G.numEdges, ∃ es, es ∈ ss ∧
    propMapConformsSchema (G.edgeProps ⟨ed, he⟩) es.propSchema = true

/-- Definition 6.1 value inhabitation. Admissibility, plus refined-schema
    membership for graph elements at refined component types, plus recursive
    inhabitation of every list element at the element type. -/
inductive ValueInhabits (G : PropertyGraph) : Value -> GSort -> Prop where
  | mk {v : Value} {t : GSort}
      (hAdm : RecordSchema.valueAdmissible v t = true)
      (hNodeMem : ∀ site ss g n, t.componentType = GSort.nodeRefinedOf site ss →
          v = Value.nodeRef g n → NodeRefMember G n ss)
      (hEdgeMem : ∀ site ss g ed, t.componentType = GSort.edgeRefinedOf site ss →
          v = Value.edgeRef g ed → EdgeRefMember G ed ss)
      (hElems : ∀ es en vs, t.shape = .list es en → v = .list vs →
          ∀ w, w ∈ vs.toList → ValueInhabits G w (GSort.mk es en)) :
      ValueInhabits G v t

/-- Definition 6.1 record conformance: domains match and every binding
    inhabits its declared sort. -/
def RecordInhabits (G : PropertyGraph) (rho : Record) (Gamma : RecordSchema) : Prop :=
  (∀ x : Name, rho.mem x = Gamma.mem x) ∧
  ∀ (x : Name) (t : GSort), (x, t) ∈ Gamma.entries →
    ValueInhabits G (rho.lookup x) t

/-- Definition 6.1 binding-table conformance. -/
def BTInhabits (G : PropertyGraph) (B : BindingTable) (Gamma : RecordSchema) : Prop :=
  ∀ rho, rho ∈ B → RecordInhabits G rho Gamma

/-- The list-element obligation, isolated: the only content of Definition
    6.1 that the existing conformance and runtime-invariant theorems do not
    already provide. -/
def ListElemsInhabit (G : PropertyGraph) (rho : Record) (Gamma : RecordSchema) : Prop :=
  ∀ (x : Name) (t : GSort), (x, t) ∈ Gamma.entries →
    ∀ es en, t.shape = .list es en →
    ∀ vs, rho.lookup x = .list vs →
    ∀ w, w ∈ vs.toList → ValueInhabits G w (GSort.mk es en)

/-- The glue. Classical conformance (admissibility) + the runtime
    configuration invariant (refined membership) + the list-element
    obligation assemble into Definition 6.1 conformance. -/
theorem recordInhabits_of_parts {G : PropertyGraph} {rho : Record}
    {Gamma : RecordSchema}
    (hwf : SchemaWF Gamma)
    (hConf : RecordConforms rho Gamma)
    (hWF : RuntimeConfigWF G rho Gamma)
    (hLE : ListElemsInhabit G rho Gamma) :
    RecordInhabits G rho Gamma := by
  refine ⟨hConf.1, ?_⟩
  intro x t hxt
  refine ValueInhabits.mk (hConf.2 x t hxt) ?_ ?_ ?_
  · intro site ss g n hct hv hn
    exact (hWF x t (hwf x t hxt)).1 site ss hct g n hn hv
  · intro site ss g ed hct hv he
    exact (hWF x t (hwf x t hxt)).2 site ss hct g ed he hv
  · intro es en vs hsh hv w hw
    exact hLE x t hxt es en hsh vs hv w hw

theorem btInhabits_of_parts {G : PropertyGraph} {B : BindingTable}
    {Gamma : RecordSchema}
    (hwf : SchemaWF Gamma)
    (hConf : BTConforms B Gamma)
    (hWF : ∀ rho, rho ∈ B → RuntimeConfigWF G rho Gamma)
    (hLE : ∀ rho, rho ∈ B → ListElemsInhabit G rho Gamma) :
    BTInhabits G B Gamma :=
  fun rho hrho =>
    recordInhabits_of_parts hwf (hConf rho hrho) (hWF rho hrho) (hLE rho hrho)

-- ============================================================
--  Strong (branch-witnessing) Definition 6.1 inhabitation
--
--  `ValueInhabits` does not record WHICH branch of a union a value
--  inhabits, so it is not monotone along `Subtype`: a reference that
--  conforms to no schema in `ss` still weakly inhabits
--  `union [nodeRefined ss]` (admissibility checks the site only, and
--  the membership obligation is keyed on a refined componentType,
--  which a union shape never is), yet `unionElim` collapses that union
--  to `nodeRefined ss`, where membership is demanded.  The strong
--  relation `ValueInhabitsS` adds exactly the missing data:
--    * refined-single membership is required at EVERY null tag (the
--      weak relation keys on `componentType`, i.e. nullable only);
--    * at a union shape a non-null value must strongly inhabit some
--      branch -- the witness produced by `unionL` and consumed by
--      `unionElim`.
--  With that strengthening, monotonicity along `Subtype` holds by
--  plain induction on the derivation; no transitivity elimination is
--  needed, since `trans` composes the induction hypotheses directly.
--  The branch witness is stated at the `.val` tag: for non-null values
--  admissibility at `.val` and `.nullable` coincides, and `.null`-
--  tagged sorts admit no non-null value at all.
-- ============================================================

mutual
/-- Strong Definition 6.1 inhabitation.  Admissibility, plus
    refined-schema membership at every null tag, plus recursive
    inhabitation of list elements, plus a strong branch witness at
    union shapes for non-null values. -/
inductive ValueInhabitsS (G : PropertyGraph) : Value -> GSort -> Prop where
  | mk {v : Value} {t : GSort}
      (hAdm : RecordSchema.valueAdmissible v t = true)
      (hNodeMem : ∀ site ss g n, t.shape = .single (.nodeRefined site ss) →
          v = Value.nodeRef g n → NodeRefMember G n ss)
      (hEdgeMem : ∀ site ss g ed, t.shape = .single (.edgeRefined site ss) →
          v = Value.edgeRef g ed → EdgeRefMember G ed ss)
      (hElems : ∀ es en vs, t.shape = .list es en → v = .list vs →
          ∀ w, w ∈ vs.toList → ValueInhabitsS G w (GSort.mk es en))
      (hBranch : ∀ ts, t.shape = .union ts → v ≠ .null →
          StrongBranch G v ts) :
      ValueInhabitsS G v t

/-- A strong branch witness: some member of the union's branch list is
    strongly inhabited (at the `.val` tag) by the value.  A separate
    mutual inductive because the kernel rejects an `Exists` nesting
    whose predicate captures constructor-local variables (the same
    restriction noted for `Subtype.unionCong`). -/
inductive StrongBranch (G : PropertyGraph) : Value -> List ExtSort -> Prop where
  | mk {v : Value} {ts : List ExtSort} (es : ExtSort)
      (hmem : es ∈ ts)
      (h : ValueInhabitsS G v (GSort.mk (.single es) .val)) :
      StrongBranch G v ts
end

theorem ValueInhabitsS.adm {G : PropertyGraph} {v : Value} {t : GSort}
    (h : ValueInhabitsS G v t) :
    RecordSchema.valueAdmissible v t = true := by
  cases h with | mk hAdm _ _ _ _ => exact hAdm

/-- The null value strongly inhabits anything that admits it: every other
    obligation is triggered by a specific non-null value form. -/
private theorem strong_of_null {G : PropertyGraph} {t : GSort}
    (hAdm : RecordSchema.valueAdmissible .null t = true) :
    ValueInhabitsS G .null t :=
  ⟨hAdm,
   fun _ _ _ _ _ hveq => Value.noConfusion hveq,
   fun _ _ _ _ _ hveq => Value.noConfusion hveq,
   fun _ _ _ _ hveq => Value.noConfusion hveq,
   fun _ _ hne => absurd rfl hne⟩

/-- Retag a strong inhabitation of a non-null value to the `.val` tag. -/
private theorem strong_retag_toVal {G : PropertyGraph} {v : Value}
    {s : SortShape} {n : NullTag} (hv : v ≠ .null)
    (h : ValueInhabitsS G v ⟨s, n⟩) : ValueInhabitsS G v ⟨s, .val⟩ := by
  obtain ⟨hAdm, hN, hE, hL, hB⟩ := h
  cases n with
  | val => exact ⟨hAdm, hN, hE, hL, hB⟩
  | nullable => exact ⟨(adm_nonNull_val_eq_nullable hv s).trans hAdm, hN, hE, hL, hB⟩
  | null => exact absurd hAdm (by rw [adm_nonNull_nullTag_false hv s]; simp)

/-- Retag a `.val` strong inhabitation of a non-null value to any
    non-`.null` tag. -/
private theorem strong_retag_ofVal {G : PropertyGraph} {v : Value}
    {s : SortShape} {n : NullTag} (hv : v ≠ .null) (hn : n ≠ .null)
    (h : ValueInhabitsS G v ⟨s, .val⟩) : ValueInhabitsS G v ⟨s, n⟩ := by
  obtain ⟨hAdm, hN, hE, hL, hB⟩ := h
  cases n with
  | val => exact ⟨hAdm, hN, hE, hL, hB⟩
  | nullable => exact ⟨(adm_nonNull_val_eq_nullable hv s).symm.trans hAdm, hN, hE, hL, hB⟩
  | null => exact absurd rfl hn

/-- Every value strongly inhabits the top sort. -/
private theorem strong_any {G : PropertyGraph} (v : Value) :
    ValueInhabitsS G v GSort.any := by
  refine ⟨by cases v <;> rfl, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ _ hsh; exact absurd hsh (by simp [GSort.any])
  · intro _ _ _ _ hsh; exact absurd hsh (by simp [GSort.any])
  · intro _ _ _ hsh; exact absurd hsh (by simp [GSort.any])
  · intro _ hsh; exact absurd hsh (by simp [GSort.any])

/-- Shape-level monotonicity of strong inhabitation along `Subtype`: for
    non-null values, with both tags pinned to `.val`, every subtyping
    rule transports the strong relation.  The four null-tag rules
    collapse to shape identity; the residual tag corners are handled in
    the assembly `valueInhabitsS_mono` via `admissible_mono`. -/
private theorem valueInhabitsS_shape_mono {G : PropertyGraph}
    {t1 t2 : GSort} (hSub : Subtype t1 t2) :
    ∀ v : Value, v ≠ .null →
      ValueInhabitsS G v (GSort.mk t1.shape .val) →
      ValueInhabitsS G v (GSort.mk t2.shape .val) := by
  induction hSub with
  | refl t => exact fun v _ h => h
  | trans _ _ ih12 ih23 => exact fun v hv h => ih23 v hv (ih12 v hv h)
  | any t => exact fun v _ _ => strong_any v
  | bot t =>
      intro v _ h
      exact absurd h.adm
        (by cases v <;> simp [RecordSchema.valueAdmissible, GSort.botSort])
  | refineNode Gs ss n =>
      intro v hv h
      obtain ⟨hAdm, _, _, _, _⟩ := h
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · cases v <;> simp_all [RecordSchema.valueAdmissible, Value.hasExtSort]
      · intro _ _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ hsh; exact absurd hsh (by simp)
  | refineEdge Gs ss n =>
      intro v hv h
      obtain ⟨hAdm, _, _, _, _⟩ := h
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · cases v <;> simp_all [RecordSchema.valueAdmissible, Value.hasExtSort]
      · intro _ _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ hsh; exact absurd hsh (by simp)
  | refineWidenNode Gs ss1 ss2 n hwide =>
      intro v hv h
      obtain ⟨hAdm, hNodeMem, _, _, _⟩ := h
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · cases v <;> simp_all [RecordSchema.valueAdmissible, Value.hasExtSort]
      · intro site ss g nn hsh hveq
        injection hsh with hes
        injection hes with hsite hss
        subst hss
        intro hn
        obtain ⟨ns, hns, hconf⟩ := hNodeMem site ss1 g nn (by rw [hsite]) hveq hn
        exact ⟨ns, hwide ns hns, hconf⟩
      · intro _ _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ hsh; exact absurd hsh (by simp)
  | refineWidenEdge Gs ss1 ss2 n hwide =>
      intro v hv h
      obtain ⟨hAdm, _, hEdgeMem, _, _⟩ := h
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · cases v <;> simp_all [RecordSchema.valueAdmissible, Value.hasExtSort]
      · intro _ _ _ _ hsh; exact absurd hsh (by simp)
      · intro site ss g ed hsh hveq
        injection hsh with hes
        injection hes with hsite hss
        subst hss
        intro he
        obtain ⟨es, hes', hconf⟩ := hEdgeMem site ss1 g ed (by rw [hsite]) hveq he
        exact ⟨es, hwide es hes', hconf⟩
      · intro _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ hsh; exact absurd hsh (by simp)
  | refNodeEmpty Gs t _ _ =>
      intro v _ h
      exact absurd h.adm
        (by cases v <;> simp [RecordSchema.valueAdmissible, GSort.nodeEmpty])
  | refEdgeEmpty Gs t _ _ =>
      intro v _ h
      exact absurd h.adm
        (by cases v <;> simp [RecordSchema.valueAdmissible, GSort.edgeEmpty])
  | listCov es1 es2 en1 en2 n hin ih =>
      intro v hv h
      obtain ⟨hAdm, _, _, hL, _⟩ := h
      cases v with
      | null => exact absurd rfl hv
      | prim p => exact absurd hAdm (by simp [RecordSchema.valueAdmissible])
      | nodeRef a b =>
          exact absurd hAdm
            (by simp [RecordSchema.valueAdmissible, Value.hasExtSort])
      | edgeRef a b =>
          exact absurd hAdm
            (by simp [RecordSchema.valueAdmissible, Value.hasExtSort])
      | list vs =>
          refine ⟨rfl, ?_, ?_, ?_, ?_⟩
          · intro _ _ _ _ hsh; exact absurd hsh (by simp)
          · intro _ _ _ _ hsh; exact absurd hsh (by simp)
          · intro es en vs' hsh hveq w hw
            injection hsh with h1 h2
            injection hveq with h3
            subst h1; subst h2; subst h3
            have hSw := hL es1 en1 vs rfl rfl w hw
            by_cases hwn : w = .null
            · subst hwn
              exact strong_of_null (admissible_mono _ _ _ hSw.adm hin)
            · have h2 := ih w hwn (strong_retag_toVal hwn hSw)
              cases hen2 : en2 with
              | null =>
                  exact absurd (admissible_mono w _ _ hSw.adm (hen2 ▸ hin))
                    (by rw [adm_nonNull_nullTag_false hwn]; simp)
              | val => exact h2
              | nullable => exact strong_retag_ofVal hwn (by simp) h2
          · intro _ hsh; exact absurd hsh (by simp)
  | unionL ts t n hmem =>
      intro v hv h
      refine ⟨union_adm_intro hmem h.adm, ?_, ?_, ?_, ?_⟩
      · intro _ _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ _ _ hsh; exact absurd hsh (by simp)
      · intro ts' hsh _
        injection hsh with h1
        subst h1
        exact ⟨t, hmem, h⟩
  | unionElim ts n target _ ih =>
      intro v hv h
      obtain ⟨_, _, _, _, hB⟩ := h
      obtain ⟨es, hmem, hSb⟩ := hB ts rfl hv
      exact ih es hmem v hv hSb
  | nullable s => exact fun v _ h => h
  | nullSingleton s => exact fun v _ h => h
  | nullCov _ ih => exact ih
  | nullSingCov _ ih => exact ih

/-- Strong inhabitation is monotone along `Subtype`.  This is the
    transport the weak relation cannot satisfy; the strong branch
    witness restores exactly the data `unionElim` consumes, and `trans`
    composes the induction hypotheses directly. -/
theorem valueInhabitsS_mono {G : PropertyGraph} {v : Value} {t1 t2 : GSort}
    (h : ValueInhabitsS G v t1) (hSub : Subtype t1 t2) :
    ValueInhabitsS G v t2 := by
  by_cases hv : v = .null
  · subst hv
    exact strong_of_null (admissible_mono _ _ _ h.adm hSub)
  · obtain ⟨s2, n2⟩ := t2
    have h1 : ValueInhabitsS G v ⟨t1.shape, .val⟩ := strong_retag_toVal hv h
    have h2 := valueInhabitsS_shape_mono hSub v hv h1
    cases n2 with
    | val => exact h2
    | nullable => exact strong_retag_ofVal hv (by simp) h2
    | null =>
        exact absurd (admissible_mono v t1 _ h.adm hSub)
          (by rw [adm_nonNull_nullTag_false hv]; simp)

/-- Strong inhabitation implies the weak (headline) Definition 6.1
    relation: the weak membership obligation is keyed on a nullable
    refined `componentType`, which the tag-blind strong obligation
    covers, and list elements convert recursively. -/
theorem valueInhabitsS_to_inhabits {G : PropertyGraph} :
    ∀ (s : SortShape) (n : NullTag) (v : Value),
      ValueInhabitsS G v ⟨s, n⟩ → ValueInhabits G v ⟨s, n⟩ := by
  intro s
  induction s with
  | single es =>
      intro n v h
      obtain ⟨hAdm, hN, hE, _, _⟩ := h
      refine ValueInhabits.mk hAdm ?_ ?_ ?_
      · intro site ss g m hct hveq
        have hct' : (⟨.single es, n⟩ : GSort) = GSort.nodeRefinedOf site ss := hct
        rw [GSort.nodeRefinedOf] at hct'
        injection hct' with hsh hn
        exact hN site ss g m hsh hveq
      · intro site ss g ed hct hveq
        have hct' : (⟨.single es, n⟩ : GSort) = GSort.edgeRefinedOf site ss := hct
        rw [GSort.edgeRefinedOf] at hct'
        injection hct' with hsh hn
        exact hE site ss g ed hsh hveq
      · intro _ _ _ hsh; exact absurd hsh (by simp)
  | list es en ih =>
      intro n v h
      obtain ⟨hAdm, _, _, hL, _⟩ := h
      refine ValueInhabits.mk hAdm ?_ ?_ ?_
      · intro site ss g m hct hveq
        subst hveq
        cases n <;> simp [RecordSchema.valueAdmissible] at hAdm
      · intro site ss g ed hct hveq
        subst hveq
        cases n <;> simp [RecordSchema.valueAdmissible] at hAdm
      · intro es' en' vs hsh hveq w hw
        injection hsh with h1 h2
        subst h1; subst h2
        exact ih en w (hL es en vs rfl hveq w hw)
  | union ts =>
      intro n v h
      obtain ⟨hAdm, _, _, _, _⟩ := h
      refine ValueInhabits.mk hAdm ?_ ?_ ?_
      · intro site ss g m hct hveq
        exact absurd hct (by simp [GSort.componentType, GSort.nodeRefinedOf])
      · intro site ss g ed hct hveq
        exact absurd hct (by simp [GSort.componentType, GSort.edgeRefinedOf])
      · intro _ _ _ hsh; exact absurd hsh (by simp)
  | any =>
      intro n v h
      obtain ⟨hAdm, _, _, _, _⟩ := h
      refine ValueInhabits.mk hAdm ?_ ?_ ?_
      · intro site ss g m hct hveq
        exact absurd hct (by simp [GSort.componentType, GSort.nodeRefinedOf])
      · intro site ss g ed hct hveq
        exact absurd hct (by simp [GSort.componentType, GSort.edgeRefinedOf])
      · intro _ _ _ hsh; exact absurd hsh (by simp)
  | bot =>
      intro n v h
      obtain ⟨hAdm, _, _, _, _⟩ := h
      refine ValueInhabits.mk hAdm ?_ ?_ ?_
      · intro site ss g m hct hveq
        exact absurd hct (by simp [GSort.componentType, GSort.nodeRefinedOf])
      · intro site ss g ed hct hveq
        exact absurd hct (by simp [GSort.componentType, GSort.edgeRefinedOf])
      · intro _ _ _ hsh; exact absurd hsh (by simp)
  | nullType =>
      intro n v h
      obtain ⟨hAdm, _, _, _, _⟩ := h
      refine ValueInhabits.mk hAdm ?_ ?_ ?_
      · intro site ss g m hct hveq
        exact absurd hct (by simp [GSort.componentType, GSort.nodeRefinedOf])
      · intro site ss g ed hct hveq
        exact absurd hct (by simp [GSort.componentType, GSort.edgeRefinedOf])
      · intro _ _ _ hsh; exact absurd hsh (by simp)
  | emptyFormer es en _ =>
      intro n v h
      obtain ⟨hAdm, _, _, _, _⟩ := h
      refine ValueInhabits.mk hAdm ?_ ?_ ?_
      · intro site ss g m hct hveq
        exact absurd hct (by simp [GSort.componentType, GSort.nodeRefinedOf])
      · intro site ss g ed hct hveq
        exact absurd hct (by simp [GSort.componentType, GSort.edgeRefinedOf])
      · intro _ _ _ hsh; exact absurd hsh (by simp)

/-- The transportable fragment of the sort language: graph-element
    singles (refined or not) carry the `.nullable` tag (for refined ones
    that is exactly where the weak relation's `componentType` obligation
    fires; for unrefined ones it makes `sortInter`'s `tighterNull` stay
    nullable), unions contain no refined branch, and list element sorts
    are recursively transportable.  Pattern-output schemas live in this
    fragment; on it a weak inhabitation upgrades to a strong one. -/
def SortShape.transportableAt : SortShape → NullTag → Prop
  | .single (.node _), n => n = .nullable
  | .single (.edge _), n => n = .nullable
  | .single (.nodeRefined _ _), n => n = .nullable
  | .single (.edgeRefined _ _), n => n = .nullable
  | .list es en, _ => SortShape.transportableAt es en
  | .union ts, _ => ∀ es, es ∈ ts →
      match es with
      | .nodeRefined _ _ => False
      | .edgeRefined _ _ => False
      | _ => True
  | _, _ => True

def GSort.transportable (t : GSort) : Prop :=
  SortShape.transportableAt t.shape t.null

/-- On the transportable fragment, weak Definition 6.1 inhabitation
    upgrades to strong inhabitation: refined singles are nullable so the
    weak membership obligation already fired, and union branches are
    unrefined so the branch witness carries no membership obligation. -/
theorem inhabits_to_strong {G : PropertyGraph} :
    ∀ (s : SortShape) (n : NullTag) (v : Value),
      SortShape.transportableAt s n →
      ValueInhabits G v ⟨s, n⟩ → ValueInhabitsS G v ⟨s, n⟩ := by
  intro s
  induction s with
  | single es =>
      intro n v htr h
      obtain ⟨hAdm, hN, hE, _⟩ := h
      refine ⟨hAdm, ?_, ?_, ?_, ?_⟩
      · intro site ss g m hsh hveq
        injection hsh with he
        subst he
        have hn : n = .nullable := htr
        subst hn
        exact hN site ss g m rfl hveq
      · intro site ss g ed hsh hveq
        injection hsh with he
        subst he
        have hn : n = .nullable := htr
        subst hn
        exact hE site ss g ed rfl hveq
      · intro _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ hsh; exact absurd hsh (by simp)
  | list es en ih =>
      intro n v htr h
      obtain ⟨hAdm, _, _, hL⟩ := h
      refine ⟨hAdm, ?_, ?_, ?_, ?_⟩
      · intro _ _ _ _ hsh hveq
        subst hveq
        cases n <;> simp [RecordSchema.valueAdmissible] at hAdm
      · intro _ _ _ _ hsh hveq
        subst hveq
        cases n <;> simp [RecordSchema.valueAdmissible] at hAdm
      · intro es' en' vs hsh hveq w hw
        injection hsh with h1 h2
        subst h1; subst h2
        exact ih en w htr (hL es en vs rfl hveq w hw)
      · intro _ hsh; exact absurd hsh (by simp)
  | union ts =>
      intro n v htr h
      obtain ⟨hAdm, _, _, _⟩ := h
      refine ⟨hAdm, ?_, ?_, ?_, ?_⟩
      · intro _ _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ _ _ hsh; exact absurd hsh (by simp)
      · intro ts' hsh hne
        injection hsh with h1
        subst h1
        obtain ⟨es0, hmem0, hadm0⟩ := union_adm_elim hAdm
        have hadmv : RecordSchema.valueAdmissible v ⟨.single es0, .val⟩ = true := by
          cases n with
          | val => exact hadm0
          | nullable => exact (adm_nonNull_val_eq_nullable hne _).trans hadm0
          | null =>
              exact absurd hadm0
                (by rw [adm_nonNull_nullTag_false hne]; simp)
        refine ⟨es0, hmem0, hadmv, ?_, ?_, ?_, ?_⟩
        · intro site ss g m hsh2 hveq
          injection hsh2 with he
          subst he
          exact False.elim (htr _ hmem0)
        · intro site ss g ed hsh2 hveq
          injection hsh2 with he
          subst he
          exact False.elim (htr _ hmem0)
        · intro _ _ _ hsh2; exact absurd hsh2 (by simp)
        · intro _ hsh2; exact absurd hsh2 (by simp)
  | any =>
      intro n v _ h
      obtain ⟨hAdm, _, _, _⟩ := h
      refine ⟨hAdm, ?_, ?_, ?_, ?_⟩
      · intro _ _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ hsh; exact absurd hsh (by simp)
  | bot =>
      intro n v _ h
      obtain ⟨hAdm, _, _, _⟩ := h
      refine ⟨hAdm, ?_, ?_, ?_, ?_⟩
      · intro _ _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ hsh; exact absurd hsh (by simp)
  | nullType =>
      intro n v _ h
      obtain ⟨hAdm, _, _, _⟩ := h
      refine ⟨hAdm, ?_, ?_, ?_, ?_⟩
      · intro _ _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ hsh; exact absurd hsh (by simp)
  | emptyFormer es en _ =>
      intro n v _ h
      obtain ⟨hAdm, _, _, _⟩ := h
      refine ⟨hAdm, ?_, ?_, ?_, ?_⟩
      · intro _ _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ _ _ hsh; exact absurd hsh (by simp)
      · intro _ hsh; exact absurd hsh (by simp)

/-- Strong Definition 6.1 record conformance. -/
def RecordInhabitsS (G : PropertyGraph) (rho : Record) (Gamma : RecordSchema) : Prop :=
  (∀ x : Name, rho.mem x = Gamma.mem x) ∧
  ∀ (x : Name) (t : GSort), (x, t) ∈ Gamma.entries →
    ValueInhabitsS G (rho.lookup x) t

/-- Strong Definition 6.1 binding-table conformance. -/
def BTInhabitsS (G : PropertyGraph) (B : BindingTable) (Gamma : RecordSchema) : Prop :=
  ∀ rho, rho ∈ B → RecordInhabitsS G rho Gamma

/-- Every entry sort of the schema is transportable. -/
def SchemaTransportable (Gamma : RecordSchema) : Prop :=
  ∀ x t, (x, t) ∈ Gamma.entries → GSort.transportable t

theorem recordInhabitsS_of_inhabits {G : PropertyGraph} {rho : Record}
    {Gamma : RecordSchema}
    (htr : SchemaTransportable Gamma) (h : RecordInhabits G rho Gamma) :
    RecordInhabitsS G rho Gamma :=
  ⟨h.1, fun x t hxt =>
    inhabits_to_strong t.shape t.null _ (htr x t hxt) (h.2 x t hxt)⟩

theorem recordInhabitsS_to_inhabits {G : PropertyGraph} {rho : Record}
    {Gamma : RecordSchema} (h : RecordInhabitsS G rho Gamma) :
    RecordInhabits G rho Gamma :=
  ⟨h.1, fun x t hxt => valueInhabitsS_to_inhabits t.shape t.null _ (h.2 x t hxt)⟩

theorem btInhabitsS_of_inhabits {G : PropertyGraph} {B : BindingTable}
    {Gamma : RecordSchema}
    (htr : SchemaTransportable Gamma) (h : BTInhabits G B Gamma) :
    BTInhabitsS G B Gamma :=
  fun rho hrho => recordInhabitsS_of_inhabits htr (h rho hrho)

theorem btInhabitsS_to_inhabits {G : PropertyGraph} {B : BindingTable}
    {Gamma : RecordSchema} (h : BTInhabitsS G B Gamma) :
    BTInhabits G B Gamma :=
  fun rho hrho => recordInhabitsS_to_inhabits (h rho hrho)

-- ============================================================
--  Pattern-output schemas are transportable
--
--  Mirrors the `nodeEdgeNullable` chain: every sort a pattern typing
--  can place in its output schema keeps graph-element singles at the
--  `.nullable` tag, keeps unions free of refined branches, and keeps
--  list element sorts inside the fragment.  This is what upgrades the
--  weak pattern-level Definition 6.1 result to the strong relation at
--  the query level.
-- ============================================================

set_option maxHeartbeats 800000 in
/-- `sortInter` preserves transportability: same-shape meets keep the
    shape (list/union content unchanged, graph-element tags stay
    nullable because both operands are), refined meets stay nullable or
    collapse to an empty former, and every fallback is a bottom or an
    empty former, which the fragment does not constrain. -/
theorem sortInter_transportable {t1 t2 : GSort}
    (h1 : t1.transportable) (h2 : t2.transportable) :
    (RecordSchema.sortInter t1 t2).transportable := by
  unfold RecordSchema.sortInter
  split
  · exact h1
  · split
    · exact h1
    · exact h2
    · exact h1
    · exact h2
    · obtain ⟨sh1, nl1⟩ := t1
      obtain ⟨sh2, nl2⟩ := t2
      simp only [GSort.transportable] at h1 h2
      cases sh1 with
      | single es1 =>
          cases es1 <;>
            (cases sh2 with
             | single es2 =>
                 cases es2 <;>
                   (simp only [GSort.transportable] <;> (repeat' split) <;>
                     first
                       | trivial
                       | rfl
                       | assumption
                       | contradiction
                       | simp_all [beq_self_eq_true, RecordSchema.tighterNull,
                           SortShape.transportableAt, GSort.botSort,
                           GSort.nodeEmpty, GSort.edgeEmpty])
             | _ =>
                 simp only [GSort.transportable] <;> (repeat' split) <;>
                   first
                     | trivial
                     | rfl
                     | assumption
                     | contradiction
                     | simp_all [beq_self_eq_true, RecordSchema.tighterNull,
                         SortShape.transportableAt, GSort.botSort,
                         GSort.nodeEmpty, GSort.edgeEmpty])
      | _ =>
          cases sh2 <;>
            (simp only [GSort.transportable] <;> (repeat' split) <;>
              first
                | trivial
                | rfl
                | assumption
                | contradiction
                | simp_all [beq_self_eq_true, RecordSchema.tighterNull,
                    SortShape.transportableAt, GSort.botSort,
                    GSort.nodeEmpty, GSort.edgeEmpty])

theorem schemaTransportable_empty : SchemaTransportable RecordSchema.empty := by
  intro x t h; simp [RecordSchema.empty] at h

theorem schemaTransportable_singleton {x : Name} {t : GSort}
    (ht : t.transportable) :
    SchemaTransportable (RecordSchema.mk [(x, t)]) := by
  intro y s hy
  simp only [List.mem_singleton, Prod.mk.injEq] at hy
  obtain ⟨_, rfl⟩ := hy; exact ht

theorem schemaTransportable_join {A B : RecordSchema}
    (hA : SchemaTransportable A) (hB : SchemaTransportable B) :
    SchemaTransportable (A.join B) := by
  intro x t hxt
  rcases RecordSchema.join_entry_cases hxt with
    ⟨t1, h1, _, ht⟩ | ⟨t1, t2, h1, h2lk, ht⟩ | ⟨t2, h2, _, ht⟩
  · rw [ht]; exact hA x t1 h1
  · rw [ht]
    exact sortInter_transportable (hA x t1 h1)
      (hB x t2 (RecordSchema.lookup_some_mem h2lk))
  · rw [ht]; exact hB x t2 h2

theorem schemaTransportable_set {Gamma : RecordSchema} {x : Name} {t : GSort}
    (hG : SchemaTransportable Gamma) (ht : t.transportable) :
    SchemaTransportable (Gamma.set x t) := by
  intro y s hys
  unfold RecordSchema.set at hys
  split at hys
  · simp only [RecordSchema.update, List.mem_map] at hys
    obtain ⟨⟨k, w⟩, hkw, heq⟩ := hys
    split at heq
    · rw [Prod.mk.injEq] at heq; obtain ⟨_, rfl⟩ := heq; exact ht
    · rw [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq; exact hG k w hkw
  · simp only [RecordSchema.extend, List.mem_append, List.mem_singleton] at hys
    rcases hys with h | h
    · exact hG y s h
    · rw [Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact ht

theorem schemaTransportable_setMany :
    ∀ {bindings : List (Name × GSort)} {Gamma : RecordSchema},
    SchemaTransportable Gamma →
    (∀ p ∈ bindings, GSort.transportable (Prod.snd p)) →
    SchemaTransportable (Gamma.setMany bindings)
  | [], _, hG, _ => hG
  | hd :: _tl, Gamma, hG, hb =>
      schemaTransportable_setMany (Gamma := Gamma.set hd.1 hd.2)
        (schemaTransportable_set hG (hb hd (List.mem_cons_self _ _)))
        (fun p hp => hb p (List.mem_cons_of_mem _ hp))

theorem schemaTransportable_liftToGroupRef {Gamma : RecordSchema}
    {vars : List Name} (h : SchemaTransportable Gamma) :
    SchemaTransportable (Gamma.liftToGroupRef vars) := by
  intro x t hxt
  obtain ⟨t0, ht0, ht⟩ := RecordSchema.mem_liftToGroupRef_entries hxt
  rw [ht]; split
  · show GSort.transportable t0.liftToList
    exact h x t0 ht0
  · exact h x t0 ht0

theorem schemaTransportable_liftToNullable {Gamma : RecordSchema}
    {vars : List Name} (h : SchemaTransportable Gamma) :
    SchemaTransportable (Gamma.liftToNullable vars) := by
  intro x t hxt
  obtain ⟨t0, ht0, ht⟩ := RecordSchema.mem_liftToNullable_entries hxt
  rw [ht]; split
  · show GSort.transportable t0.toNullable
    have h0 := h x t0 ht0
    obtain ⟨s0, n0⟩ := t0
    cases s0 <;>
      first
        | trivial
        | rfl
        | exact h0
        | (rename_i es; cases es <;> first | trivial | rfl)
  · exact h x t0 ht0

theorem atomTyping_transportable {ctx : TypingCtx} {a : AtomInput}
    {Gamma : RecordSchema}
    (h : AtomTyping ctx a Gamma) : SchemaTransportable Gamma := by
  cases h <;>
    (apply schemaTransportable_singleton
     simp [GSort.transportable, SortShape.transportableAt, GSort.nodeOf,
       GSort.edgeOf, GSort.nodeRefinedOf, GSort.edgeRefinedOf,
       GSort.nodeEmpty, GSort.edgeEmpty])

theorem refinementTyping_transportable {ctx : TypingCtx}
    {G1 G2 G3 : RecordSchema} {v1 r2 v3 : Name} {dir : Direction}
    {GammaRef : RecordSchema}
    (h : RefinementTyping ctx G1 G2 G3 v1 r2 v3 dir GammaRef)
    (h1 : SchemaTransportable G1) (h2 : SchemaTransportable G2)
    (h3 : SchemaTransportable G3) :
    SchemaTransportable GammaRef := by
  cases h with
  | open_ => exact schemaTransportable_join (schemaTransportable_join h1 h2) h3
  | _ =>
    apply schemaTransportable_setMany
      (schemaTransportable_join (schemaTransportable_join h1 h2) h3)
    intro p hp
    obtain ⟨pk, pv⟩ := p
    simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq] at hp
    rcases hp with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | hnil <;>
      first
        | (simp [GSort.transportable, SortShape.transportableAt,
            GSort.nodeRefinedOf, GSort.edgeRefinedOf,
            GSort.nodeEmpty, GSort.edgeEmpty]; done)
        | exact absurd hnil (List.not_mem_nil _)

theorem patternTyping_transportable {ctx : TypingCtx} {qd : QuantDepth}
    {P : Pattern} {Gamma : RecordSchema} {v : Name}
    (h : PatternTyping ctx qd P Gamma v) :
    SchemaTransportable Gamma := by
  induction h with
  | patNode _ _ _ hAtom =>
      exact atomTyping_transportable hAtom
  | patEdge _ _ _ _ _ _ _ _ _ _ hAtomN1 hAtomE hAtomN2 hRef =>
      exact refinementTyping_transportable hRef
        (atomTyping_transportable hAtomN1) (atomTyping_transportable hAtomE)
        (atomTyping_transportable hAtomN2)
  | patStep _ _ _ _ _ _ _ _ _ _ _ _ hAtomE hAtomN2 hRef ihPrefix =>
      exact refinementTyping_transportable hRef ihPrefix
        (atomTyping_transportable hAtomE) (atomTyping_transportable hAtomN2)
  | patQuantEdge _ _ _ _ _ _ _ hAtomE _ _ =>
      exact schemaTransportable_liftToGroupRef (schemaTransportable_join
        (schemaTransportable_join
          (schemaTransportable_singleton
            (by simp [GSort.transportable, SortShape.transportableAt, GSort.nodeOf]))
          (atomTyping_transportable hAtomE))
        (schemaTransportable_singleton
          (by simp [GSort.transportable, SortShape.transportableAt, GSort.nodeOf])))
  | patOptEdge _ _ _ _ _ _ =>
      exact schemaTransportable_liftToNullable (schemaTransportable_join
        (schemaTransportable_join
          (schemaTransportable_singleton
            (by simp [GSort.transportable, SortShape.transportableAt, GSort.nodeOf]))
          (schemaTransportable_singleton
            (by simp [GSort.transportable, SortShape.transportableAt, GSort.edgeOf])))
        (schemaTransportable_singleton
          (by simp [GSort.transportable, SortShape.transportableAt, GSort.nodeOf])))
  | patQuantPath _ _ _ _ _ _ ihInner =>
      exact schemaTransportable_liftToGroupRef ihInner
  | patGrouped _ _ _ _ _ ih => exact ih

theorem patExprTyping_transportable {ctx : TypingCtx}
    {P : Pattern} {Gamma : RecordSchema}
    (h : PatExprTyping ctx P Gamma) :
    SchemaTransportable Gamma := by
  induction h with
  | single _ _ _ hp => exact patternTyping_transportable hp
  | conjunction _ _ _ _ _ _ h2 _ ih1 =>
      exact schemaTransportable_join ih1 (patternTyping_transportable h2)

/-- Strengthening of `qpathIterate_listForm`: the collapsed path's members
    all come from the base results. -/
theorem qpathIterate_listForm_mem
    (baseResults : List Record) (vars : List Name) (lv tv : Name) (lo hi : Nat) :
    ∀ (fuel kappa : Nat) (frontier : List (List Record × Value))
      (accumulated : List Record),
      (∀ pe, pe ∈ frontier → ∀ r, r ∈ pe.1 → r ∈ baseResults) →
      (∀ rho, rho ∈ accumulated →
        ∃ path, rho = collapsePath vars path ∧ ∀ r, r ∈ path → r ∈ baseResults) →
      ∀ rho, rho ∈ qpathIterate baseResults vars lv tv lo hi kappa frontier accumulated fuel →
        ∃ path, rho = collapsePath vars path ∧ ∀ r, r ∈ path → r ∈ baseResults := by
  intro fuel
  induction fuel with
  | zero =>
    intro kappa frontier accumulated hfr hacc rho hrho
    simp only [qpathIterate] at hrho
    exact hacc rho hrho
  | succ fuel' ih =>
    intro kappa frontier accumulated hfr hacc rho hrho
    simp only [qpathIterate] at hrho
    split at hrho
    · exact hacc rho hrho
    · refine ih (kappa + 1) _ _ ?_ ?_ rho hrho
      · intro pe hpe r hr
        rw [List.mem_flatMap] at hpe
        obtain ⟨pe0, hpe0, hpe0m⟩ := hpe
        rw [List.mem_filterMap] at hpe0m
        obtain ⟨rho0, hrho0, heq⟩ := hpe0m
        split at heq
        · obtain rfl := Option.some.inj heq
          rw [List.mem_append] at hr
          rcases hr with h | h
          · exact hfr pe0 hpe0 r h
          · rw [List.mem_singleton] at h
            rw [h]; exact hrho0
        · exact Option.noConfusion heq
      · intro rho' hrho'
        split at hrho'
        · rw [List.mem_append] at hrho'
          rcases hrho' with h | h
          · exact hacc rho' h
          · obtain ⟨pe, hpe, hpec⟩ := List.mem_map.mp h
            exact ⟨pe.fst, hpec.symm, fun r hr => hfr pe hpe r hr⟩
        · exact hacc rho' hrho'

/-- Every output of the quantified-path evaluator is a `collapsePath` whose
    members are base-result records. -/
theorem evalQuantified_listForm_mem
    (vars : List Name) (baseResults : List Record) (lv tv : Name) (lo hi : Nat)
    (rho : Record) (hrho : rho ∈ evalQuantified vars baseResults lv tv lo hi) :
    ∃ path, rho = collapsePath vars path ∧ ∀ r, r ∈ path → r ∈ baseResults := by
  simp only [evalQuantified] at hrho
  rw [List.mem_append] at hrho
  rcases hrho with hz | hq
  · split at hz
    · rw [List.mem_singleton] at hz
      exact ⟨[], hz, fun r hr => absurd hr (List.not_mem_nil r)⟩
    · exact absurd hz (List.not_mem_nil rho)
  · refine qpathIterate_listForm_mem baseResults vars lv tv lo hi (hi + 1) 1 _ []
      ?_ (fun _ h => absurd h (List.not_mem_nil _)) rho hq
    intro pe hpe r hr
    rw [List.mem_map] at hpe
    obtain ⟨rho0, hrho0, hpe0⟩ := hpe
    rw [← hpe0] at hr
    rw [List.mem_singleton] at hr
    rw [hr]; exact hrho0

/-- A value at a sort with an unrefined component and a non-list shape
    inhabits it as soon as it is admissible. -/
private theorem valueInhabits_of_adm_simple {G : PropertyGraph} {v : Value} {t : GSort}
    (hAdm : RecordSchema.valueAdmissible v t = true)
    (hNR : ∀ site ss, t.componentType ≠ GSort.nodeRefinedOf site ss)
    (hER : ∀ site ss, t.componentType ≠ GSort.edgeRefinedOf site ss)
    (hNL : ∀ es en, t.shape ≠ .list es en) :
    ValueInhabits G v t :=
  .mk hAdm (fun site ss _ _ hct _ => absurd hct (hNR site ss))
    (fun site ss _ _ hct _ => absurd hct (hER site ss))
    (fun es en _ hsh _ _ _ => absurd hsh (hNL es en))

private theorem valueInhabits_nodeOf {G : PropertyGraph} {v : Value} {site : GraphSite}
    (hAdm : RecordSchema.valueAdmissible v (GSort.nodeOf site) = true) :
    ValueInhabits G v (GSort.nodeOf site) := by
  obtain ⟨hNR, hER⟩ := openSort_component_unrefined (OpenSort.node (site := site))
  exact valueInhabits_of_adm_simple hAdm hNR hER (fun es en h => SortShape.noConfusion h)

private theorem valueInhabits_edgeOf {G : PropertyGraph} {v : Value} {site : GraphSite}
    (hAdm : RecordSchema.valueAdmissible v (GSort.edgeOf site) = true) :
    ValueInhabits G v (GSort.edgeOf site) := by
  obtain ⟨hNR, hER⟩ := openSort_component_unrefined (OpenSort.edge (site := site))
  exact valueInhabits_of_adm_simple hAdm hNR hER (fun es en h => SortShape.noConfusion h)

/-- `collapsePath`'s binding for a collapsed variable, precisely. -/
private theorem collapsePath_lookup_eq (vars : List Name) (path : List Record) (z : Name)
    (hz : vars.any (fun v => v == z) = true) :
    (collapsePath vars path).lookup z
      = Value.ofList (path.map (fun r => r.lookup z)) := by
  induction vars with
  | nil => simp at hz
  | cons v vs ih =>
    simp only [List.any_cons, Bool.or_eq_true] at hz
    show (Record.lookup (((v, Value.ofList (path.map (fun r => r.lookup v)))
        :: vs.map fun x => (x, Value.ofList (path.map (fun r => r.lookup x)))) : Record) z) = _
    unfold Record.lookup
    rw [List.find?_cons]
    cases hv : v == z with
    | true =>
      have : v = z := eq_of_beq hv
      subst this
      simp
    | false =>
      simp only [hv]
      rcases hz with h | h
      · exact absurd h (by rw [hv]; exact Bool.noConfusion)
      · exact ih h

/-- Looking up the middle key of an explicit three-entry record. -/
private theorem lookup_triple_mid {a b c : Name} {va vb vc : Value}
    (hab : (a == b) = false) :
    Record.lookup [(a, va), (b, vb), (c, vc)] b = vb := by
  simp [Record.lookup, List.find?_cons, hab, beq_self_eq_true]

/-- Elements of the edge list a variable-length path binds are edge
    references of the working site. -/
private theorem matchVarLengthPath_lookup_elems (G : PropertyGraph) (site : GraphSite)
    (dir : Direction) :
    ∀ (k : Nat) (src : NodeAtom) (rel : EdgeAtom) (dst : NodeAtom) (rho : Record),
      (src.var == rel.var) = false →
      (dst.var == rel.var) = false →
      rho ∈ matchVarLengthPath G site src rel dst dir k →
      ∃ edges, rho.lookup rel.var = Value.ofList edges ∧
        ∀ e, e ∈ edges → ∃ ei, ∃ hei : ei < G.numEdges, e = Value.edgeRef site ei
          ∧ checkLabels (G.edgeLabels ⟨ei, hei⟩) rel.labels = true
          ∧ checkEdgeProps G site ⟨ei, hei⟩ rel.props = true := by
  intro k
  induction k with
  | zero =>
    intro src rel dst rho hH1 hH2 hmem
    simp only [matchVarLengthPath, List.mem_filterMap] at hmem
    obtain ⟨rho0, hrho0, heq⟩ := hmem
    obtain ⟨srcN, rfl⟩ := matchNode_mem_form hrho0
    obtain rfl := Option.some.inj heq
    refine ⟨[], ?_, fun e he => absurd he (List.not_mem_nil e)⟩
    simp [Record.extend, Record.lookup, List.find?_cons, hH1, singletonNode_lookup]
  | succ k ih =>
    cases k with
    | zero =>
      intro src rel dst rho hH1 hH2 hmem
      rw [matchVarLengthPath] at hmem
      simp only [List.mem_map] at hmem
      obtain ⟨rho0, hrho0, heq⟩ := hmem
      obtain ⟨srcN, ei, dstN, hei, hdstN, hlblE, hprpE, _, _, hform⟩ := matchSingleEdge_mem_form hrho0
      subst hform
      have hlk : Record.lookup [(src.var, Value.nodeRef site srcN),
          (rel.var, Value.edgeRef site ei), (dst.var, Value.nodeRef site dstN)] rel.var
          = Value.edgeRef site ei := lookup_triple_mid hH1
      rw [hlk] at heq
      refine ⟨[Value.edgeRef site ei], ?_, ?_⟩
      · rw [← heq]
        simp [Record.set, Record.mem, Record.lookup, List.map, List.any_cons,
              List.find?_cons, hH1, hH2, beq_self_eq_true]
      · intro e he
        rw [List.mem_singleton] at he
        exact ⟨ei, hei, he, hlblE, hprpE⟩
    | succ n =>
      intro src rel dst rho hH1 hH2 hmem
      rw [matchVarLengthPath] at hmem
      simp only [List.mem_flatMap] at hmem
      obtain ⟨rho1, hrho1, hbody⟩ := hmem
      obtain ⟨srcN, ei, midN, hei, hmidN, hlblE1, hprpE1, _, _, hform1⟩ := matchSingleEdge_mem_form hrho1
      split at hbody
      · exact absurd hbody (List.not_mem_nil rho)
      · simp only [List.mem_filterMap] at hbody
        obtain ⟨rho2, hrho2, hfilt⟩ := hbody
        obtain ⟨edges', hlk', helems'⟩ :=
          ih { var := "_mid_" ++ toString n, labels := none, props := [] }
            { rel with var := "_rest_" ++ dst.var } dst rho2
            (mid_ne_rest_dst n dst.var) (by rw [name_beq_comm]; exact rest_ne_dst dst.var) hrho2
        split at hfilt
        · obtain rfl := Option.some.inj hfilt
          refine ⟨_, lookup_triple_mid hH1, ?_⟩
          intro e he
          rw [List.mem_append] at he
          rcases he with h1 | h2
          · -- first-edge contribution: if the lookup returned an edge
            -- reference at all, it is one of the matched record's values,
            -- all of which are site references
            split at h1
            · rename_i g ee hveq
              rw [List.mem_singleton] at h1
              have hveq' : rho1.lookup ("_rel_" ++ toString n : Name)
                  = Value.edgeRef g ee := hveq
              have hgee : g = site ∧ ee = ei := by
                rcases lookup_mem_or_null rho1 ("_rel_" ++ toString n : Name) with
                  ⟨p, hp, hpv⟩ | hnull
                · rw [hveq'] at hpv
                  rw [hform1] at hp
                  rcases hp with _ | ⟨_, hp⟩
                  · exact absurd hpv.symm (by intro h; exact Value.noConfusion h)
                  · rcases hp with _ | ⟨_, hp⟩
                    · injection hpv.symm with hg he
                      exact ⟨hg.symm, he.symm⟩
                    · rcases hp with _ | ⟨_, hp⟩
                      · exact absurd hpv.symm (by intro h; exact Value.noConfusion h)
                      · exact absurd hp (List.not_mem_nil p)
                · rw [hveq'] at hnull; exact Value.noConfusion hnull
              obtain ⟨hgsite, heei⟩ := hgee
              rw [h1, hgsite, heei]
              exact ⟨ei, hei, rfl, hlblE1, hprpE1⟩
            · exact absurd h1 (List.not_mem_nil e)
          · -- rest contribution: the recursive lookup's list, via the IH
            rw [hlk'] at h2
            simp only [Value.ofList, Value.asList, ValueList.toList_ofList] at h2
            exact helems' e h2
        · exact absurd hfilt (by simp)

/-- A list value is never admissible at a single-sorted type. -/
private theorem list_not_adm_single {vs : ValueList} {t : GSort} {esort : ExtSort}
    (hsh : t.shape = .single esort) :
    RecordSchema.valueAdmissible (Value.list vs) t = false := by
  obtain ⟨tsh, tn⟩ := t
  have h : tsh = .single esort := hsh
  subst h
  cases tn <;> rfl

/-- A quantified edge's collected element at a closed site inhabits the
    label/property-refined edge sort: the element's conformant catalog
    schema survives both atom filters, giving the Definition 6.1
    refined-schema membership. -/
private theorem quantEdge_closed_elem_inhabits
    (G : PropertyGraph) (site : GraphSite)
    (Psi : GraphSchemaFull) (hGconf : graphConformsSchema G Psi = true)
    (rel : EdgeAtom) (PhiPi : PropSchema)
    (xiL xiPrp xiResult : List EdgeSchemaFull)
    (hPrpTyping : PropConstraintTyping rel.props PhiPi)
    (hLblFilter : xiL = resolveEdgeSchemas Psi rel.labels)
    (hPrpFilter : xiPrp = filterEdgeSchemasByPropCompat xiL PhiPi)
    (hResult : xiResult = xiPrp)
    (w : Value) (ei : Nat) (hei : ei < G.numEdges)
    (hwei : w = Value.edgeRef site ei)
    (hchkL : checkLabels (G.edgeLabels ⟨ei, hei⟩) rel.labels = true)
    (hchkP : checkEdgeProps G site ⟨ei, hei⟩ rel.props = true) :
    ValueInhabits G w (GSort.edgeRefinedOf site xiResult) := by
  obtain ⟨es, hes, hconf⟩ := graphConformsSchema_edge hGconf ei hei
  have hlblmem : es ∈ resolveEdgeSchemas Psi rel.labels :=
    resolveEdgeSchemas_mem_of_conforms G Psi ⟨ei, hei⟩ es rel.labels hes hconf hchkL
  rw [← hLblFilter] at hlblmem
  have hpropmem : es ∈ filterEdgeSchemasByPropCompat xiL PhiPi :=
    filterEdgeSchemasByPropCompat_mem_of_conforms G site ⟨ei, hei⟩ es xiL rel.props PhiPi
      hlblmem hconf hPrpTyping hchkP
  have hmemR : es ∈ xiResult := by
    rw [hResult, hPrpFilter]
    exact hpropmem
  have hpm : propMapConformsSchema (G.edgeProps ⟨ei, hei⟩) es.propSchema = true := by
    have hc := hconf
    unfold edgeConformsSchema at hc
    simp only [Bool.and_eq_true] at hc
    exact hc.1.1.2
  subst hwei
  refine ValueInhabits.mk ?_ ?_ ?_ ?_
  · simp [RecordSchema.valueAdmissible, GSort.edgeRefinedOf, Value.hasExtSort]
  · intro site' ss g n hct hveq
    exact Value.noConfusion hveq
  · intro site' ss g ed hct hveq
    have hct' : GSort.edgeRefinedOf site xiResult = GSort.edgeRefinedOf site' ss := hct
    rw [GSort.edgeRefinedOf, GSort.edgeRefinedOf] at hct'
    injection hct' with hsh _
    injection hsh with hes'
    injection hes' with hsite hss
    injection hveq with hg hed
    subst hss
    intro he
    subst hed
    exact ⟨es, hmemR, hpm⟩
  · intro es' en' vs hsh hveq
    exact Value.noConfusion hveq

/-- At a closed site whose atom filters are empty, no edge can be
    collected: any collected element's conformant schema would survive the
    filters, contradicting emptiness. -/
private theorem quantEdge_closedFail_elem_false
    (G : PropertyGraph) (site : GraphSite)
    (Psi : GraphSchemaFull) (hGconf : graphConformsSchema G Psi = true)
    (rel : EdgeAtom) (PhiPi : PropSchema)
    (xiL xiPrp : List EdgeSchemaFull)
    (hPrpTyping : PropConstraintTyping rel.props PhiPi)
    (hLblFilter : xiL = resolveEdgeSchemas Psi rel.labels)
    (hPrpFilter : xiPrp = filterEdgeSchemasByPropCompat xiL PhiPi)
    (hEmpty : xiPrp.length = 0)
    (ei : Nat) (hei : ei < G.numEdges)
    (hchkL : checkLabels (G.edgeLabels ⟨ei, hei⟩) rel.labels = true)
    (hchkP : checkEdgeProps G site ⟨ei, hei⟩ rel.props = true) :
    False := by
  obtain ⟨es, hes, hconf⟩ := graphConformsSchema_edge hGconf ei hei
  have hlblmem : es ∈ resolveEdgeSchemas Psi rel.labels :=
    resolveEdgeSchemas_mem_of_conforms G Psi ⟨ei, hei⟩ es rel.labels hes hconf hchkL
  rw [← hLblFilter] at hlblmem
  have hpropmem : es ∈ filterEdgeSchemasByPropCompat xiL PhiPi :=
    filterEdgeSchemasByPropCompat_mem_of_conforms G site ⟨ei, hei⟩ es xiL rel.props PhiPi
      hlblmem hconf hPrpTyping hchkP
  rw [← hPrpFilter] at hpropmem
  rw [List.length_eq_zero] at hEmpty
  rw [hEmpty] at hpropmem
  exact List.not_mem_nil es hpropmem

/-- List-element inhabitation for pattern outputs.
    The conformance and runtime-invariant facts the quantified case needs
    about inner rows are supplied as function premises, so the closed-site
    and open-site instantiations share this single induction. -/
theorem patternTyping_listElems
    (ctx : TypingCtx) (G : PropertyGraph)
    (hInnerConf : ∀ (qd : QuantDepth) (P : Pattern) (Gamma : RecordSchema) (v : Name),
        PatternTyping ctx qd P Gamma v →
        BTConforms (evalPattern G ctx.graphSite P) Gamma)
    (hInnerWF : ∀ (qd : QuantDepth) (P : Pattern) (Gamma : RecordSchema) (v : Name),
        PatternTyping ctx qd P Gamma v →
        ∀ rho, rho ∈ evalPattern G ctx.graphSite P → RuntimeConfigWF G rho Gamma)
    (hClosedConf : ∀ Psi, ctx.schemaMap.lookup ctx.graphSite = some Psi →
        graphConformsSchema G Psi = true) :
    ∀ (qd : QuantDepth) (P : Pattern) (Gamma : RecordSchema) (v : Name),
      PatternTyping ctx qd P Gamma v →
      ∀ rho, rho ∈ evalPattern G ctx.graphSite P →
        ListElemsInhabit G rho Gamma := by
  intro qd P Gamma v h
  induction h with
  | patNode qd na GammaA hAtom =>
    intro rho hrho x t hxt es en hsh vs hv w hw
    exfalso
    cases hAtom with
    | nodeOpen _ _ _ _ =>
      have ht := (Prod.mk.injEq .. ▸ (List.mem_singleton.mp hxt)).2
      rw [ht] at hsh
      exact SortShape.noConfusion hsh
    | nodeClosed _ _ _ _ _ _ _ _ hClosed _ _ _ _ _ _ =>
      have ht := (Prod.mk.injEq .. ▸ (List.mem_singleton.mp hxt)).2
      rw [ht] at hsh
      exact SortShape.noConfusion hsh
    | nodeClosedFail _ _ _ _ _ _ _ hClosed _ _ _ _ =>
      have ht := (Prod.mk.injEq .. ▸ (List.mem_singleton.mp hxt)).2
      rw [ht] at hsh
      exact SortShape.noConfusion hsh
  | patEdge qd n1 n2 rel dir GammaN1 GammaE GammaN2 GammaRef hSingleD hAtomN1 hAtomE hAtomN2 hRef =>
    intro rho hrho x t hxt es en hsh vs hv w hw
    exfalso
    rw [evalPattern_edge_single G ctx.graphSite n1 n2 rel dir hSingleD] at hrho
    obtain ⟨srcN, ei, dstN, hsrcN, hei, hdstN, _, _, _, _, _, _, _, hsd, hform⟩ :=
      matchSingleEdge_mem_form' hrho
    subst hform
    rcases lookup_mem_or_null _ x with ⟨p, hp, hpv⟩ | hnull
    · have hp2 : p.2 = Value.list vs := hpv.symm.trans hv
      rcases hp with _ | ⟨_, hp⟩
      · exact Value.noConfusion hp2
      · rcases hp with _ | ⟨_, hp⟩
        · exact Value.noConfusion hp2
        · rcases hp with _ | ⟨_, hp⟩
          · exact Value.noConfusion hp2
          · exact absurd hp (List.not_mem_nil p)
    · exact Value.noConfusion (hnull.symm.trans hv)
  | patStep qd P rel dir n2 Gamma1 GammaE GammaN2 GammaRef v1 hSingle hPrefix hAtomE hAtomN2 hRef ihPrefix =>
    intro rho_out hmem x t hxt es en hsh vs hv w hw
    obtain ⟨rho, rhoEdge, hrho, hedge, hStepAgree, ⟨gv, srcN0, hrhov1⟩, rfl⟩ :=
      evalPattern_step_single_mem G ctx.graphSite P rel dir n2 v1 hSingle
        (patternTyping_tailVar hPrefix) rho_out hmem
    obtain ⟨T2, rfl⟩ := atomTyping_node_singleton hAtomN2
    obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
    have hrelEq : ({ rel with quantifier := .single } : EdgeAtom) = rel := by
      cases rel with | mk v l p q => cases hSingle; rfl
    rw [hrelEq] at hedge
    obtain ⟨srcN, ei, dstN, hsrcN, hei, hdstN, _, _, _, _, _, _, _, hsd, hform⟩ :=
      matchSingleEdge_mem_form' hedge
    cases hxe : rhoEdge.mem x with
    | true =>
      exfalso
      have hlkE := Record.merge_lookup_agree_right rho rhoEdge x hStepAgree hxe
      rw [hlkE] at hv
      rcases lookup_mem_or_null rhoEdge x with ⟨p, hp, hpv⟩ | hnull
      · have hp2 : p.2 = Value.list vs := hpv.symm.trans hv
        rw [hform] at hp
        rcases hp with _ | ⟨_, hp⟩
        · exact Value.noConfusion hp2
        · rcases hp with _ | ⟨_, hp⟩
          · exact Value.noConfusion hp2
          · rcases hp with _ | ⟨_, hp⟩
            · exact Value.noConfusion hp2
            · exact absurd hp (List.not_mem_nil p)
      · exact Value.noConfusion (hnull.symm.trans hv)
    | false =>
      have hb1 : (v1 == x) = false := by
        cases hb : v1 == x with
        | false => rfl
        | true =>
          rw [hform] at hxe
          simp [Record.mem, hb] at hxe
      have hbr : (rel.var == x) = false := by
        cases hb : rel.var == x with
        | false => rfl
        | true =>
          rw [hform] at hxe
          simp [Record.mem, hb] at hxe
      have hbn : (n2.var == x) = false := by
        cases hb : n2.var == x with
        | false => rfl
        | true =>
          rw [hform] at hxe
          simp [Record.mem, hb] at hxe
      have hwf1 : SchemaWF Gamma1 := patternTyping_schemaWF hPrefix
      have hwfRef : SchemaWF GammaRef :=
        patternTyping_schemaWF
          (PatternTyping.patStep ctx qd P rel dir n2 Gamma1 _ _ GammaRef v1
            hSingle hPrefix hAtomE hAtomN2 hRef)
      have hlkRef : GammaRef.lookup x = some t := hwfRef x t hxt
      have hElk : (RecordSchema.mk [(rel.var, TE)]).lookup x = none :=
        RecordSchema.lookup_eq_none_of_mem_false (by rw [singleton_schema_mem]; exact hbr)
      have hNlk : (RecordSchema.mk [(n2.var, T2)]).lookup x = none :=
        RecordSchema.lookup_eq_none_of_mem_false (by rw [singleton_schema_mem]; exact hbn)
      rw [refinementTyping_lookup_other hRef hwf1 (RecordSchema.singleton_schemaWF _ _)
        (RecordSchema.singleton_schemaWF _ _) x hb1 hElk hNlk hbr hbn] at hlkRef
      have hxrho : rho.mem x = true := by
        obtain ⟨hdom, _⟩ := hInnerConf qd P Gamma1 v1 hPrefix rho hrho
        rw [hdom x]
        exact RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem hlkRef)
      have hvL : rho.lookup x = Value.list vs := by
        rw [← Record.merge_lookup_left rho rhoEdge x hxrho]
        exact hv
      exact ihPrefix rho hrho x t (RecordSchema.lookup_some_mem hlkRef)
        es en hsh vs hvL w hw
  | patOptEdge n1 n2 rel dir hNE12 hNE23 =>
    intro rho hrho x t hxt es en hsh vs hv w hw
    exfalso
    obtain ⟨t0, ht0, ht⟩ := RecordSchema.mem_liftToNullable_entries hxt
    subst ht
    rcases open_join_entry_is_nodeOf_or_edgeOf ctx.graphSite n1 n2 rel
      (GSort.edgeOf ctx.graphSite) hNE12 hNE23 x t0 ht0 with hn | ⟨_, hn⟩ <;>
      (rw [hn] at hsh
       split at hsh <;> exact SortShape.noConfusion hsh)
  | patQuantEdge n1 n2 rel dir K GammaE hQuant hAtomE hNE12 hNE23 =>
    intro rho hrho x t hxt es en hsh vs hv w hw
    obtain ⟨TE, rfl⟩ := atomTyping_edge_singleton hAtomE
    obtain ⟨t0, ht0, ht⟩ := RecordSchema.mem_liftToGroupRef_entries hxt
    cases hlift : ([rel.var].any (fun v => v == x)) with
    | false =>
      exfalso
      simp only [hlift, if_false] at ht
      subst ht
      rcases open_join_entry_is_nodeOf_or_edgeOf ctx.graphSite n1 n2 rel
        TE hNE12 hNE23 x t ht0 with hn | ⟨hxrel, hn⟩
      · rw [hn] at hsh; exact SortShape.noConfusion hsh
      · subst hxrel
        simp [beq_self_eq_true] at hlift
    | true =>
      have hxrel : rel.var = x := by
        simp only [List.any_cons, List.any_nil, Bool.or_false] at hlift
        exact eq_of_beq hlift
      subst hxrel
      -- the lifted variable's base sort is the edge identity sort
      have ht0edge : t0 = TE := by
        rcases RecordSchema.join_entry_cases ht0 with
          ⟨ta, hin, _, rfl⟩ | ⟨ta, tb, hin, hClk, rfl⟩ | ⟨tb, hent, _, rfl⟩
        · rcases RecordSchema.join_entry_cases hin with
            ⟨tc, hAe, _, rfl⟩ | ⟨tc, td, hAe, hBlk, rfl⟩ | ⟨td, hBe, _, rfl⟩
          · exfalso
            have hkey := (Prod.mk.injEq .. ▸ (List.mem_singleton.mp hAe)).1
            rw [hkey] at hNE12
            rw [beq_self_eq_true] at hNE12
            exact Bool.noConfusion hNE12
          · exfalso
            have hkey := (Prod.mk.injEq .. ▸ (List.mem_singleton.mp hAe)).1
            rw [hkey] at hNE12
            rw [beq_self_eq_true] at hNE12
            exact Bool.noConfusion hNE12
          · exact (Prod.mk.injEq .. ▸ (List.mem_singleton.mp hBe)).2
        · exfalso
          rw [singleton_schema_lookup] at hClk
          rw [beq_name_symm_false hNE23] at hClk
          exact Option.noConfusion hClk
        · exfalso
          have hkey := (Prod.mk.injEq .. ▸ (List.mem_singleton.mp hent)).1
          rw [hkey] at hNE23
          rw [beq_self_eq_true] at hNE23
          exact Bool.noConfusion hNE23
      -- reduce the evaluator and extract the edge list
      rw [evalPattern_edge_groupRef G ctx.graphSite n1 n2
        { rel with quantifier := K } dir hQuant] at hrho
      unfold matchRangePath at hrho
      rw [List.mem_flatMap] at hrho
      obtain ⟨offset, _, hk⟩ := hrho
      obtain ⟨edges, hlkE, helems⟩ :=
        matchVarLengthPath_lookup_elems G ctx.graphSite dir _ n1
          { rel with quantifier := K } n2 rho
          (beq_name_symm_false hNE12) (beq_name_symm_false hNE23) hk
      rw [hlkE] at hv
      unfold Value.ofList at hv
      injection hv with hvl
      -- element type: the lift of the edge sort
      rw [ht0edge] at ht
      simp only [hlift, if_true] at ht
      subst ht
      have hshl : SortShape.list TE.shape TE.null = SortShape.list es en := hsh
      injection hshl with he1 he2
      subst he1
      subst he2
      -- elements are site edge references, admissible at the edge sort
      rw [← hvl] at hw
      rw [ValueList.toList_ofList] at hw
      obtain ⟨ei, hei, hwei, hchkL, hchkP⟩ := helems w hw
      cases hAtomE with
      | edgeOpen _ _ _ _ =>
        have hAdm : RecordSchema.valueAdmissible w (GSort.edgeOf ctx.graphSite) = true := by
          rw [hwei]
          exact edgeRef_adm_edgeOf ctx.graphSite ei
        exact valueInhabits_edgeOf hAdm
      | edgeClosed _ _ _ Psi' PhiPi xiL xiPrp xiResult hClosed hSchema hPrpTyping hLblFilter hPrpFilter hResult hNonEmpty =>
        exact quantEdge_closed_elem_inhabits G ctx.graphSite Psi'
          (hClosedConf Psi' hSchema) rel PhiPi xiL xiPrp xiResult
          hPrpTyping hLblFilter hPrpFilter hResult w ei hei hwei hchkL hchkP
      | edgeClosedFail _ _ _ Psi' PhiPi xiL xiPrp hClosed hSchema hPrpTyping hLblFilter hPrpFilter hEmpty =>
        exact (quantEdge_closedFail_elem_false G ctx.graphSite Psi'
          (hClosedConf Psi' hSchema) rel PhiPi xiL xiPrp
          hPrpTyping hLblFilter hPrpFilter hEmpty ei hei hchkL hchkP).elim
  | patQuantPath P K GammaInner v hInner hQuant ihInner =>
    intro rho hrho x t hxt es en hsh vs hv w hw
    obtain ⟨lv, hlv⟩ := patternLeadVar_isSome P
    obtain ⟨tv, htv⟩ := patternTailVar_isSome P
    have hvars := patternTyping_vars_mem hInner
    simp only [evalPattern, hlv, htv] at hrho
    obtain ⟨path, rfl, hpathmem⟩ :=
      evalQuantified_listForm_mem (patternVars P) (evalPattern G ctx.graphSite P)
        lv tv _ _ rho hrho
    obtain ⟨t0, ht0, ht⟩ := RecordSchema.mem_liftToGroupRef_entries hxt
    have hmemI : GammaInner.mem x = true := RecordSchema.mem_of_entry ht0
    have hx_inner : GammaInner.dom.any (fun w => w == x) = true := by
      rw [RecordSchema.dom_any_mem GammaInner x]
      exact hmemI
    have hx_vars : (patternVars P).any (fun w => w == x) = true := by
      rw [hvars x]
      exact hmemI
    simp only [hx_inner, if_true] at ht
    subst ht
    have hshl : SortShape.list t0.shape t0.null = SortShape.list es en := hsh
    injection hshl with he1 he2
    subst he1
    subst he2
    rw [collapsePath_lookup_eq (patternVars P) path x hx_vars] at hv
    unfold Value.ofList at hv
    injection hv with hvl
    rw [← hvl] at hw
    rw [ValueList.toList_ofList] at hw
    obtain ⟨r, hrpath, hrw⟩ := List.mem_map.mp hw
    have hrbase := hpathmem r hrpath
    have hwfI : SchemaWF GammaInner :=
      patternTyping_schemaWF hInner
    have hrec : RecordInhabits G r GammaInner :=
      recordInhabits_of_parts hwfI
        (hInnerConf .inside P GammaInner v hInner r hrbase)
        (hInnerWF .inside P GammaInner v hInner r hrbase)
        (ihInner r hrbase)
    have hval := hrec.2 x t0 ht0
    rw [← hrw]
    exact hval
  | patGrouped qd P Gamma v hP ih =>
    intro rho hrho
    rw [evalPattern_grouped] at hrho
    exact ih rho hrho

/-- List-element inhabitation for pattern-expression outputs: the conjunction
    (join) layer over `patternTyping_listElems`. -/
theorem patExprTyping_listElems
    (ctx : TypingCtx) (G : PropertyGraph)
    (hInnerConf : ∀ (qd : QuantDepth) (P : Pattern) (Gamma : RecordSchema) (v : Name),
        PatternTyping ctx qd P Gamma v →
        BTConforms (evalPattern G ctx.graphSite P) Gamma)
    (hInnerWF : ∀ (qd : QuantDepth) (P : Pattern) (Gamma : RecordSchema) (v : Name),
        PatternTyping ctx qd P Gamma v →
        ∀ rho, rho ∈ evalPattern G ctx.graphSite P → RuntimeConfigWF G rho Gamma)
    (hExprConf : ∀ (P' : Pattern) (Gamma' : RecordSchema),
        PatExprTyping ctx P' Gamma' →
        BTConforms (evalPattern G ctx.graphSite P') Gamma')
    (hClosedConf : ∀ Psi, ctx.schemaMap.lookup ctx.graphSite = some Psi →
        graphConformsSchema G Psi = true)
    {P : Pattern} {Gamma : RecordSchema}
    (hType : PatExprTyping ctx P Gamma) :
    ∀ rho, rho ∈ evalPattern G ctx.graphSite P → ListElemsInhabit G rho Gamma := by
  induction hType with
  | single P Gamma v h =>
    exact patternTyping_listElems ctx G hInnerConf hInnerWF hClosedConf
      .outside P Gamma v h
  | conjunction P1 P2 Gamma1 Gamma2 v h1 h2 hjc ih1 =>
    intro rho hrho x t hxt es en hsh vs hv w hw
    rw [evalPattern_patternList] at hrho
    obtain ⟨rho1, hrho1, rho2, hrho2, hagree, rfl⟩ := mem_bindingTableJoin hrho
    have hwf1 : SchemaWF Gamma1 := patExprTyping_schemaWF h1
    have hconf1 : RecordConforms rho1 Gamma1 := hExprConf P1 Gamma1 h1 rho1 hrho1
    have hconf2 : RecordConforms rho2 Gamma2 :=
      hInnerConf .outside P2 Gamma2 v h2 rho2 hrho2
    rcases RecordSchema.join_entry_cases hxt with
      ⟨t1, h1e, hm2, rfl⟩ | ⟨t1, t2, h1e, h2lk, rfl⟩ | ⟨t2, h2e, hm1, rfl⟩
    · have hmem1 : rho1.mem x = true := by
        rw [hconf1.1 x]; exact RecordSchema.mem_of_entry h1e
      have hv1 : rho1.lookup x = Value.list vs := by
        rw [← Record.merge_lookup_left rho1 rho2 x hmem1]; exact hv
      exact ih1 rho1 hrho1 x t h1e es en hsh vs hv1 w hw
    · have hmem1 : rho1.mem x = true := by
        rw [hconf1.1 x]; exact RecordSchema.mem_of_entry h1e
      have hmem2 : rho2.mem x = true := by
        rw [hconf2.1 x]
        exact RecordSchema.mem_of_entry (RecordSchema.lookup_some_mem h2lk)
      have hv1 : rho1.lookup x = Value.list vs := by
        rw [← Record.merge_lookup_left rho1 rho2 x hmem1]; exact hv
      have hv2 : rho2.lookup x = Value.list vs := by
        rw [← Record.agreeOn_lookup_eq rho1 rho2 x hagree hmem1 hmem2]; exact hv1
      obtain ⟨hbot, _⟩ := RecordSchema.joinCompatible_meet hjc (hwf1 x t1 h1e) h2lk
      rcases sortInter_cases t1 t2 with
        hc | hc | ⟨hc, hsb⟩ | hc | hc | ⟨s, ss, hc⟩ | ⟨s, ss, hc⟩ | ⟨s, ss, hc⟩ | ⟨s, ss, hc⟩
      · rw [hc] at hsh
        exact ih1 rho1 hrho1 x t1 h1e es en hsh vs hv1 w hw
      · rw [hc] at hsh
        exact patternTyping_listElems ctx G hInnerConf hInnerWF hClosedConf
          .outside P2 Gamma2 v h2 rho2 hrho2
          x t2 (RecordSchema.lookup_some_mem h2lk) es en hsh vs hv2 w hw
      · rw [hc] at hsh
        have hsh1 : t1.shape = SortShape.list es en := hsh
        exact ih1 rho1 hrho1 x t1 h1e es en hsh1 vs hv1 w hw
      · rw [hc] at hbot; exact Bool.noConfusion hbot
      · simp only [GSort.isEmptyFormer, hsh] at hc; exact Bool.noConfusion hc
      · exfalso
        have hadm := hconf1.2 x t1 h1e
        rw [hv1, list_not_adm_single hc] at hadm
        exact Bool.noConfusion hadm
      · exfalso
        have hadm := hconf1.2 x t1 h1e
        rw [hv1, list_not_adm_single hc] at hadm
        exact Bool.noConfusion hadm
      · exfalso
        have hadm := hconf2.2 x t2 (RecordSchema.lookup_some_mem h2lk)
        rw [hv2, list_not_adm_single hc] at hadm
        exact Bool.noConfusion hadm
      · exfalso
        have hadm := hconf2.2 x t2 (RecordSchema.lookup_some_mem h2lk)
        rw [hv2, list_not_adm_single hc] at hadm
        exact Bool.noConfusion hadm
    · have hmem1 : rho1.mem x = false := by
        rw [hconf1.1 x]; exact hm1
      have hv2 : rho2.lookup x = Value.list vs := by
        rw [← Record.merge_lookup_right rho1 rho2 x hmem1]; exact hv
      exact patternTyping_listElems ctx G hInnerConf hInnerWF hClosedConf
        .outside P2 Gamma2 v h2 rho2 hrho2
        x t h2e es en hsh vs hv2 w hw

/-- Definition 6.1-faithful pattern soundness (Theorem 6.2, closed sites).
    A well-typed pattern expression's table inhabits its
    schema in the full Definition 6.1 sense: admissibility, refined-schema
    membership for every graph element, and elementwise inhabitation of every
    list binding. -/
theorem patExprSoundness_inhabits
    (ctx : TypingCtx) (G : PropertyGraph)
    (hCat : ∀ Psi', ctx.schemaMap.lookup ctx.graphSite = some Psi' →
              graphConformsSchema G Psi' = true)
    (Psi : GraphSchemaFull) (hPsi : ctx.schemaMap.lookup ctx.graphSite = some Psi)
    (P : Pattern) (GammaOut : RecordSchema)
    (hType : PatExprTyping ctx P GammaOut)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G) :
    BTInhabits G (evalPattern G ctx.graphSite P) GammaOut := by
  have hStrongFn := patternTyping_runtimeWFStrong ctx G Psi hPsi hCat
  have hInnerConf : ∀ (qd : QuantDepth) (P' : Pattern) (Gamma' : RecordSchema) (v' : Name),
      PatternTyping ctx qd P' Gamma' v' →
      BTConforms (evalPattern G ctx.graphSite P') Gamma' :=
    fun qd P' Gamma' v' h =>
      patternTyping_sound ctx G hCat Psi hPsi hStrongFn qd P' Gamma' v' h
  have hInnerWF : ∀ (qd : QuantDepth) (P' : Pattern) (Gamma' : RecordSchema) (v' : Name),
      PatternTyping ctx qd P' Gamma' v' →
      ∀ rho, rho ∈ evalPattern G ctx.graphSite P' → RuntimeConfigWF G rho Gamma' :=
    fun qd P' Gamma' v' h rho hrho =>
      runtimeConfigWF_of_strong (hCat Psi hPsi)
        (hStrongFn qd P' Gamma' v' h rho hrho)
  have hExprConf : ∀ (P' : Pattern) (Gamma' : RecordSchema),
      PatExprTyping ctx P' Gamma' →
      BTConforms (evalPattern G ctx.graphSite P') Gamma' :=
    fun P' Gamma' h' => patExprSoundness ctx G hCat Psi hPsi hStrongFn P' Gamma' h' hGraph
  exact btInhabits_of_parts
    (patExprTyping_schemaWF hType)
    (hExprConf P GammaOut hType)
    (fun rho hrho => patExpr_runtimeWF ctx G Psi hPsi hCat
      (fun P' G' hPE' => hExprConf P' G' hPE') P GammaOut hType rho hrho)
    (patExprTyping_listElems ctx G hInnerConf hInnerWF hExprConf hCat hType)

/-- Definition 6.1-faithful pattern soundness at open sites. -/
theorem patExprSoundness_inhabits_open
    (ctx : TypingCtx) (G : PropertyGraph)
    (hOpen : ctx.schemaMap.isClosed ctx.graphSite = false)
    (P : Pattern) (GammaOut : RecordSchema)
    (hType : PatExprTyping ctx P GammaOut) :
    BTInhabits G (evalPattern G ctx.graphSite P) GammaOut := by
  have hInnerConf : ∀ (qd : QuantDepth) (P' : Pattern) (Gamma' : RecordSchema) (v' : Name),
      PatternTyping ctx qd P' Gamma' v' →
      BTConforms (evalPattern G ctx.graphSite P') Gamma' :=
    fun qd P' Gamma' v' h =>
      patternTyping_sound_open ctx G hOpen qd P' Gamma' v' h
  have hInnerWF : ∀ (qd : QuantDepth) (P' : Pattern) (Gamma' : RecordSchema) (v' : Name),
      PatternTyping ctx qd P' Gamma' v' →
      ∀ rho, rho ∈ evalPattern G ctx.graphSite P' → RuntimeConfigWF G rho Gamma' := by
    intro qd P' Gamma' v' h rho _
    intro x t hlk
    have hop := patternTyping_openSorts ctx hOpen qd P' Gamma' v' h
      x t (RecordSchema.lookup_some_mem hlk)
    obtain ⟨hnode, hedge⟩ := openSort_component_unrefined hop
    exact ⟨fun site ss hct => absurd hct (hnode site ss),
           fun site ss hct => absurd hct (hedge site ss)⟩
  have hExprConf : ∀ (P' : Pattern) (Gamma' : RecordSchema),
      PatExprTyping ctx P' Gamma' →
      BTConforms (evalPattern G ctx.graphSite P') Gamma' :=
    fun P' Gamma' h' => patExprSoundness_open ctx G hOpen P' Gamma' h'
  exact btInhabits_of_parts
    (patExprTyping_schemaWF hType)
    (hExprConf P GammaOut hType)
    (fun rho _ => patExpr_runtimeWF_open ctx G hOpen hType rho)
    (patExprTyping_listElems ctx G hInnerConf hInnerWF hExprConf
      (fun Psi' hPsi' => by
        unfold SchemaMap.isClosed at hOpen
        rw [hPsi'] at hOpen
        exact Bool.noConfusion hOpen) hType)

-- ============================================================
--  Definition 6.1 at the query level: projections,
--  filtering, and the schema-preserving set operations.
-- ============================================================

/-- Definition 6.1 conformance implies classical conformance. -/
theorem recordConforms_of_inhabits {G : PropertyGraph} {rho : Record}
    {Gamma : RecordSchema} (h : RecordInhabits G rho Gamma) :
    RecordConforms rho Gamma := by
  refine ⟨h.1, ?_⟩
  intro x t hxt
  cases h.2 x t hxt with
  | mk hAdm _ _ _ => exact hAdm

/-- Scalar and null values inhabit any sort they are admissible at: the
    membership and list-element obligations are triggered only by reference
    and list values. -/
theorem valueInhabits_of_prim_or_null {G : PropertyGraph} {v : Value} {t : GSort}
    (hpn : (∃ p, v = Value.prim p) ∨ v = Value.null)
    (hAdm : RecordSchema.valueAdmissible v t = true) :
    ValueInhabits G v t := by
  refine ValueInhabits.mk hAdm ?_ ?_ ?_
  · intro s ss g n _ hv
    exfalso
    rcases hpn with ⟨p, rfl⟩ | rfl <;> exact Value.noConfusion hv
  · intro s ss g ed _ hv
    exfalso
    rcases hpn with ⟨p, rfl⟩ | rfl <;> exact Value.noConfusion hv
  · intro es en vs _ hv w hw
    exfalso
    rcases hpn with ⟨p, rfl⟩ | rfl <;> exact Value.noConfusion hv

/-- Arithmetic always yields an integer or null. -/
private theorem evalArith_prim_or_null (op : ArithOp) (v1 v2 : Value) :
    (∃ p, evalArith op v1 v2 = Value.prim p) ∨ evalArith op v1 v2 = Value.null := by
  unfold evalArith
  match h1 : v1.asInt, h2 : v2.asInt with
  | none, _ =>
    simp only [h1]
    first | exact Or.inr rfl | exact Or.inr trivial
  | some _, none =>
    simp only [h1, h2]
    first | exact Or.inr rfl | exact Or.inr trivial
  | some n1, some n2 =>
    simp only [h1, h2]
    split
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · split
      · first | exact Or.inr rfl | exact Or.inr trivial
      · exact Or.inl ⟨_, rfl⟩

/-- Aggregation over values always yields an integer or null. -/
private theorem evalAggOnValues_prim_or_null (op : AggOp) (qual : AggQualifier)
    (vals : List Value) :
    (∃ p, evalAggOnValues op qual vals = Value.prim p)
      ∨ evalAggOnValues op qual vals = Value.null := by
  cases op <;> simp only [evalAggOnValues] <;> (try split) <;>
    first
      | exact Or.inl ⟨_, rfl⟩
      | exact Or.inr rfl
      | exact Or.inr trivial
      | exact Or.inl ⟨_, trivial⟩

/-- A non-variable expression evaluates to a scalar or null: only variable
    lookup can surface a graph reference or a list. -/
private theorem evalExpr_not_var_prim_or_null
    (G : PropertyGraph) (site : GraphSite) (rho : Record) (e : Expr)
    (hWF : GraphValuesWF G)
    (hne : ∀ y, e ≠ .var y) :
    (∃ p, evalExpr G site rho e = Value.prim p)
      ∨ evalExpr G site rho e = Value.null := by
  cases e with
  | var y => exact absurd rfl (hne y)
  | const lit => cases lit <;> exact Or.inl ⟨_, rfl⟩
  | null => exact Or.inr rfl
  | propAccess x k =>
    simp only [evalExpr]
    cases hx : rho.lookup x with
    | nodeRef s n =>
      simp only [hx]
      split
      · rename_i h
        exact propmap_lookup_wf (hWF.1 ⟨n, h⟩) k
      · exact Or.inr rfl
    | edgeRef s eid =>
      simp only [hx]
      split
      · rename_i h
        exact propmap_lookup_wf (hWF.2 ⟨eid, h⟩) k
      · exact Or.inr rfl
    | prim p =>
      simp only [hx]
      first | exact Or.inr rfl | exact Or.inr trivial
    | null =>
      simp only [hx]
      first | exact Or.inr rfl | exact Or.inr trivial
    | list l =>
      simp only [hx]
      first | exact Or.inr rfl | exact Or.inr trivial
  | arithOp op e1 e2 =>
    simp only [evalExpr]
    exact evalArith_prim_or_null op _ _
  | pred phi =>
    simp only [evalExpr]
    cases hp : evalPred G site rho phi with
    | some b =>
      simp only [hp]
      exact Or.inl ⟨_, rfl⟩
    | none =>
      simp only [hp]
      first | exact Or.inr rfl | exact Or.inr trivial
  | agg op qual inner =>
    simp only [evalExpr]
    cases hi : evalExpr G site rho inner with
    | list vs =>
      simp only [hi]
      exact evalAggOnValues_prim_or_null op qual vs.toList
    | prim p =>
      simp only [hi]
      cases op <;>
        first
          | exact Or.inr rfl
          | (split <;> exact Or.inl ⟨_, rfl⟩)
          | exact Or.inl ⟨_, rfl⟩
    | nodeRef s n =>
      simp only [hi]
      cases op <;>
        first
          | exact Or.inr rfl
          | (split <;> exact Or.inl ⟨_, rfl⟩)
          | exact Or.inl ⟨_, rfl⟩
    | edgeRef s ed =>
      simp only [hi]
      cases op <;>
        first
          | exact Or.inr rfl
          | (split <;> exact Or.inl ⟨_, rfl⟩)
          | exact Or.inl ⟨_, rfl⟩
    | null =>
      simp only [hi]
      cases op <;>
        first
          | exact Or.inr rfl
          | (split <;> exact Or.inl ⟨_, rfl⟩)
          | exact Or.inl ⟨_, rfl⟩

private theorem singleton_recordInhabits {G : PropertyGraph}
    (key : Name) (v : Value) (tau : GSort)
    (hinh : ValueInhabits G v tau) :
    RecordInhabits G [(key, v)] (RecordSchema.mk [(key, tau)]) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro y t hyt
  rw [List.mem_singleton] at hyt
  obtain ⟨hy, ht⟩ := Prod.mk.injEq .. ▸ hyt
  rw [hy, ht]
  show ValueInhabits G (Record.lookup [(key, v)] key) tau
  rw [show Record.lookup [(key, v)] key = v from by
    simp [Record.lookup, List.find?_cons]]
  exact hinh

private theorem disjointUnion_recordInhabits {G : PropertyGraph}
    (r1 r2 : Record) (G1 G2 : RecordSchema)
    (h1 : RecordInhabits G r1 G1) (h2 : RecordInhabits G r2 G2)
    (hcompat : RecordSchema.disjointUnionCompatible G1 G2 = true) :
    RecordInhabits G (r1 ++ r2) (G1.disjointUnion G2) := by
  obtain ⟨hdom1, hval1⟩ := h1
  obtain ⟨hdom2, hval2⟩ := h2
  refine ⟨?_, ?_⟩
  · intro x
    rw [Record.append_mem, RecordSchema.disjointUnion_mem, hdom1 x, hdom2 x]
  · intro x t hxt
    have hmem : (x, t) ∈ G1.entries ++ G2.entries := hxt
    rcases List.mem_append.mp hmem with hin1 | hin2
    · have hxG1 : G1.mem x = true :=
        List.any_eq_true.mpr ⟨(x, t), hin1, beq_self_eq_true x⟩
      have hxr1 : r1.mem x = true := by rw [hdom1 x]; exact hxG1
      rw [Record.append_lookup_left _ _ _ hxr1]
      exact hval1 x t hin1
    · have hxG2 : G2.mem x = true :=
        List.any_eq_true.mpr ⟨(x, t), hin2, beq_self_eq_true x⟩
      have hxG1false : G1.mem x = false := by
        cases hb : G1.mem x with
        | false => rfl
        | true =>
          exfalso
          unfold RecordSchema.disjointUnionCompatible at hcompat
          have hx1 : x ∈ G1.dom := by
            unfold RecordSchema.dom
            rcases List.any_eq_true.mp (hb : G1.entries.any (fun e => e.1 == x) = true)
              with ⟨e, hemem, heq⟩
            have hex : e.1 = x := eq_of_beq heq
            rw [← hex]; exact List.mem_map_of_mem Prod.fst hemem
          have hx2 : G2.dom.any (fun y => y == x) = true := by
            rcases List.any_eq_true.mp (hxG2 : G2.entries.any (fun e => e.1 == x) = true)
              with ⟨e, hemem, heq⟩
            refine List.any_eq_true.mpr ⟨e.1, ?_, heq⟩
            unfold RecordSchema.dom; exact List.mem_map_of_mem Prod.fst hemem
          have hcontra := List.all_eq_true.mp hcompat x hx1
          rw [hx2] at hcontra; exact Bool.noConfusion hcontra
      have hxr1false : r1.mem x = false := by rw [hdom1 x]; exact hxG1false
      rw [Record.append_lookup_right _ _ _ hxr1false]
      exact hval2 x t hin2

/-- Per-record projection assembly at Definition 6.1 conformance. The
    per-item premise carries list membership so syntactic side conditions on
    the projection list can be consumed itemwise. -/
private theorem projectionList_recordInhabits
    (G : PropertyGraph) (site : GraphSite) (rho : Record) (matched : BindingTable)
    (ctx : TypingCtx) (Gamma1 : RecordSchema)
    (pis : ProjectionList) (Gamma2 : RecordSchema)
    (hItem : ∀ (pi : Projection), pi ∈ pis → ∀ (Gpi : RecordSchema),
        ProjectionTyping ctx Gamma1 pi Gpi →
        RecordInhabits G (projectItem G site rho matched pi) Gpi)
    (hType : ProjectionListTyping ctx Gamma1 pis Gamma2) :
    RecordInhabits G (projectRecord G site rho matched pis) Gamma2 := by
  induction hType with
  | nil => exact ⟨fun _ => rfl, fun _ t h => absurd h (List.not_mem_nil _)⟩
  | cons pi pis Gpi Ctxrest hProj hRest hDisjoint ih =>
    show RecordInhabits G
      (projectItem G site rho matched pi ++ projectRecord G site rho matched pis)
      (Gpi.disjointUnion Ctxrest)
    exact disjointUnion_recordInhabits _ _ Gpi Ctxrest
      (hItem pi (List.Mem.head _) Gpi hProj)
      (ih (fun pi' hpi' Gpi' h' => hItem pi' (List.Mem.tail _ hpi') Gpi' h'))
      hDisjoint

/-- Filtering preserves Definition 6.1 conformance. -/
theorem btInhabits_filter {G : PropertyGraph} {B : BindingTable}
    {Gamma : RecordSchema} {p : Record -> Bool}
    (h : BTInhabits G B Gamma) : BTInhabits G (B.filter p) Gamma :=
  fun rho hrho => h rho (mem_of_filter hrho)

/-- Rows of a deduplicated table come from the table. -/
private theorem dist_mem {B : BindingTable} {rho : Record}
    (h : rho ∈ dist B) : rho ∈ B := by
  unfold dist at h
  suffices hgen : ∀ (l acc : BindingTable),
      rho ∈ l.foldl (fun a rr =>
        if a.any (fun xx => xx == rr) then a else a ++ [rr]) acc →
      rho ∈ l ∨ rho ∈ acc by
    rcases hgen B [] h with h' | h'
    · exact h'
    · exact absurd h' (List.not_mem_nil _)
  intro l
  induction l with
  | nil => intro acc h'; exact Or.inr h'
  | cons y ys ih =>
    intro acc h'
    simp only [List.foldl] at h'
    rcases ih _ h' with h'' | h''
    · exact Or.inl (List.Mem.tail _ h'')
    · split at h''
      · exact Or.inr h''
      · rcases List.mem_append.mp h'' with h3 | h3
        · exact Or.inr h3
        · rw [List.mem_singleton] at h3
          rw [h3]; exact Or.inl (List.Mem.head _)

/-- Rows of a pair-threading fold's first component come from the folded
    table (or the initial accumulator). -/
private theorem foldPairFst_mem
    (step : BindingTable × BindingTable -> Record -> BindingTable × BindingTable)
    (hstep : ∀ st rho, (step st rho).1 = st.1 ∨ (step st rho).1 = st.1 ++ [rho]) :
    ∀ (l : BindingTable) (init : BindingTable × BindingTable) (rho : Record),
      rho ∈ (l.foldl step init).1 → rho ∈ l ∨ rho ∈ init.1 := by
  intro l
  induction l with
  | nil => intro init rho h; exact Or.inr h
  | cons y ys ih =>
    intro init rho h
    simp only [List.foldl] at h
    rcases ih (step init y) rho h with h' | h'
    · exact Or.inl (List.Mem.tail _ h')
    · rcases hstep init y with heq | heq
      · rw [heq] at h'; exact Or.inr h'
      · rw [heq] at h'
        rcases List.mem_append.mp h' with h'' | h''
        · exact Or.inr h''
        · rw [List.mem_singleton] at h''
          rw [h'']; exact Or.inl (List.Mem.head _)

/-- Rows of the schema-preserving set operations come from the left table. -/
private theorem applySetOp_mem_left {op : SetOp} {B1 B2 : BindingTable}
    {rho : Record}
    (hop : op = .exceptDistinct ∨ op = .exceptAll
        ∨ op = .intersectDistinct ∨ op = .intersectAll)
    (h : rho ∈ applySetOp op B1 B2) : rho ∈ B1 := by
  rcases hop with rfl | rfl | rfl | rfl
  · exact mem_of_filter (dist_mem h)
  · rcases foldPairFst_mem _
      (by intro st r
          obtain ⟨a, b⟩ := st
          cases hc : b.any (fun x => x == r) with
          | true => simp [hc]
          | false => simp [hc])
      B1 ([], B2) rho h with h' | h'
    · exact h'
    · exact absurd h' (List.not_mem_nil _)
  · exact mem_of_filter (dist_mem h)
  · rcases foldPairFst_mem _
      (by intro st r
          obtain ⟨a, b⟩ := st
          cases hc : b.any (fun x => x == r) with
          | true => simp [hc]
          | false => simp [hc])
      B1 ([], B2) rho h with h' | h'
    · exact h'
    · exact absurd h' (List.not_mem_nil _)

/-- Scalar and null values strongly inhabit any sort they are admissible
    at: the membership and list-element obligations need reference or
    list values, and the union branch witness for a scalar is recovered
    from admissibility (no membership content on a scalar branch). -/
private theorem strong_of_prim_or_null {G : PropertyGraph} {v : Value} {t : GSort}
    (hpn : (∃ p, v = Value.prim p) ∨ v = Value.null)
    (hAdm : RecordSchema.valueAdmissible v t = true) :
    ValueInhabitsS G v t := by
  rcases hpn with ⟨p, rfl⟩ | rfl
  · refine ⟨hAdm, ?_, ?_, ?_, ?_⟩
    · intro _ _ _ _ _ hveq; exact Value.noConfusion hveq
    · intro _ _ _ _ _ hveq; exact Value.noConfusion hveq
    · intro _ _ _ _ hveq; exact Value.noConfusion hveq
    · intro ts hsh _
      have hAdm' : RecordSchema.valueAdmissible (.prim p) ⟨.union ts, t.null⟩ = true := by
        rw [← hsh]; exact hAdm
      obtain ⟨es0, hmem0, hadm0⟩ := union_adm_elim hAdm'
      have hadmv : RecordSchema.valueAdmissible (.prim p) ⟨.single es0, .val⟩ = true := by
        cases hn : t.null with
        | val => rw [hn] at hadm0; exact hadm0
        | nullable =>
            rw [hn] at hadm0
            exact (adm_nonNull_val_eq_nullable (by simp) _).trans hadm0
        | null =>
            rw [hn] at hadm0
            exact absurd hadm0
              (by rw [adm_nonNull_nullTag_false (by simp)]; simp)
      exact ⟨es0, hmem0,
        ⟨hadmv,
         fun _ _ _ _ _ hveq => Value.noConfusion hveq,
         fun _ _ _ _ _ hveq => Value.noConfusion hveq,
         fun _ _ _ _ hveq => Value.noConfusion hveq,
         fun _ hsh2 _ => absurd hsh2 (by simp)⟩⟩
  · exact strong_of_null hAdm

private theorem singleton_recordInhabitsS {G : PropertyGraph}
    (key : Name) (v : Value) (tau : GSort)
    (hinh : ValueInhabitsS G v tau) :
    RecordInhabitsS G [(key, v)] (RecordSchema.mk [(key, tau)]) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro y t hyt
  rw [List.mem_singleton] at hyt
  obtain ⟨hy, ht⟩ := Prod.mk.injEq .. ▸ hyt
  rw [hy, ht]
  show ValueInhabitsS G (Record.lookup [(key, v)] key) tau
  rw [show Record.lookup [(key, v)] key = v from by
    simp [Record.lookup, List.find?_cons]]
  exact hinh

private theorem disjointUnion_recordInhabitsS {G : PropertyGraph}
    (r1 r2 : Record) (G1 G2 : RecordSchema)
    (h1 : RecordInhabitsS G r1 G1) (h2 : RecordInhabitsS G r2 G2)
    (hcompat : RecordSchema.disjointUnionCompatible G1 G2 = true) :
    RecordInhabitsS G (r1 ++ r2) (G1.disjointUnion G2) := by
  obtain ⟨hdom1, hval1⟩ := h1
  obtain ⟨hdom2, hval2⟩ := h2
  refine ⟨?_, ?_⟩
  · intro x
    rw [Record.append_mem, RecordSchema.disjointUnion_mem, hdom1 x, hdom2 x]
  · intro x t hxt
    have hmem : (x, t) ∈ G1.entries ++ G2.entries := hxt
    rcases List.mem_append.mp hmem with hin1 | hin2
    · have hxG1 : G1.mem x = true :=
        List.any_eq_true.mpr ⟨(x, t), hin1, beq_self_eq_true x⟩
      have hxr1 : r1.mem x = true := by rw [hdom1 x]; exact hxG1
      rw [Record.append_lookup_left _ _ _ hxr1]
      exact hval1 x t hin1
    · have hxG2 : G2.mem x = true :=
        List.any_eq_true.mpr ⟨(x, t), hin2, beq_self_eq_true x⟩
      have hxG1false : G1.mem x = false := by
        cases hb : G1.mem x with
        | false => rfl
        | true =>
          exfalso
          unfold RecordSchema.disjointUnionCompatible at hcompat
          have hx1 : x ∈ G1.dom := by
            unfold RecordSchema.dom
            rcases List.any_eq_true.mp (hb : G1.entries.any (fun e => e.1 == x) = true)
              with ⟨e, hemem, heq⟩
            have hex : e.1 = x := eq_of_beq heq
            rw [← hex]; exact List.mem_map_of_mem Prod.fst hemem
          have hx2 : G2.dom.any (fun y => y == x) = true := by
            rcases List.any_eq_true.mp (hxG2 : G2.entries.any (fun e => e.1 == x) = true)
              with ⟨e, hemem, heq⟩
            refine List.any_eq_true.mpr ⟨e.1, ?_, heq⟩
            unfold RecordSchema.dom; exact List.mem_map_of_mem Prod.fst hemem
          have hcontra := List.all_eq_true.mp hcompat x hx1
          rw [hx2] at hcontra; exact Bool.noConfusion hcontra
      have hxr1false : r1.mem x = false := by rw [hdom1 x]; exact hxG1false
      rw [Record.append_lookup_right _ _ _ hxr1false]
      exact hval2 x t hin2

private theorem projectionList_recordInhabitsS
    (G : PropertyGraph) (site : GraphSite) (rho : Record) (matched : BindingTable)
    (ctx : TypingCtx) (Gamma1 : RecordSchema)
    (pis : ProjectionList) (Gamma2 : RecordSchema)
    (hItem : ∀ (pi : Projection), pi ∈ pis → ∀ (Gpi : RecordSchema),
        ProjectionTyping ctx Gamma1 pi Gpi →
        RecordInhabitsS G (projectItem G site rho matched pi) Gpi)
    (hType : ProjectionListTyping ctx Gamma1 pis Gamma2) :
    RecordInhabitsS G (projectRecord G site rho matched pis) Gamma2 := by
  induction hType with
  | nil => exact ⟨fun _ => rfl, fun _ t h => absurd h (List.not_mem_nil _)⟩
  | cons pi pis Gpi Ctxrest hProj hRest hDisjoint ih =>
    show RecordInhabitsS G
      (projectItem G site rho matched pi ++ projectRecord G site rho matched pis)
      (Gpi.disjointUnion Ctxrest)
    exact disjointUnion_recordInhabitsS _ _ Gpi Ctxrest
      (hItem pi (List.Mem.head _) Gpi hProj)
      (ih (fun pi' hpi' Gpi' h' => hItem pi' (List.Mem.tail _ hpi') Gpi' h'))
      hDisjoint

/-- Filtering preserves strong Definition 6.1 conformance. -/
theorem btInhabitsS_filter {G : PropertyGraph} {B : BindingTable}
    {Gamma : RecordSchema} {p : Record -> Bool}
    (h : BTInhabitsS G B Gamma) : BTInhabitsS G (B.filter p) Gamma :=
  fun rho hrho => h rho (mem_of_filter hrho)

-- ============================================================
--  `eq_of_beq` bootstrap for the sort component types
--
--  The derived `BEq` instances are not registered `LawfulBEq`, but the
--  equality is provable by structural descent to the lawful leaves
--  (String, plus the case-bashed BaseSort).  Needed to turn the
--  `ts.any (· == es)` membership checks inside `sortUnion` into
--  propositional list membership.
-- ============================================================

private theorem list_eq_of_beq {α : Type} [BEq α]
    (elem : ∀ a b : α, (a == b) = true → a = b) :
    ∀ l1 l2 : List α, (l1 == l2) = true → l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | a :: t1, b :: t2, h => by
      have h' : ((a == b) && (t1 == t2)) = true := h
      simp only [Bool.and_eq_true] at h'
      rw [elem a b h'.1, list_eq_of_beq elem t1 t2 h'.2]

private theorem prodNB_eq_of_beq (p q : Name × BaseSort)
    (h : (p == q) = true) : p = q := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  have h' : ((a == c) && (b == d)) = true := h
  simp only [Bool.and_eq_true] at h'
  rw [eq_of_beq h'.1, baseSort_eq_of_beq h'.2]

private theorem nodeSchemaFull_eq_of_beq {s1 s2 : NodeSchemaFull}
    (h : (s1 == s2) = true) : s1 = s2 := by
  obtain ⟨l1, p1⟩ := s1
  obtain ⟨l2, p2⟩ := s2
  have h' : ((l1 == l2) && (p1 == p2)) = true := h
  simp only [Bool.and_eq_true] at h'
  rw [list_eq_of_beq (fun a b hab => eq_of_beq hab) l1 l2 h'.1,
      list_eq_of_beq prodNB_eq_of_beq p1 p2 h'.2]

private theorem edgeSchemaFull_eq_of_beq {s1 s2 : EdgeSchemaFull}
    (h : (s1 == s2) = true) : s1 = s2 := by
  obtain ⟨l1, sr1, ds1, p1, d1⟩ := s1
  obtain ⟨l2, sr2, ds2, p2, d2⟩ := s2
  have h' : ((l1 == l2) && ((sr1 == sr2) && ((ds1 == ds2) && ((p1 == p2)
      && (d1 == d2))))) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨h1, h2, h3, h4, h5⟩ := h'
  rw [list_eq_of_beq (fun a b hab => eq_of_beq hab) l1 l2 h1,
      nodeSchemaFull_eq_of_beq h2, nodeSchemaFull_eq_of_beq h3,
      list_eq_of_beq prodNB_eq_of_beq p1 p2 h4, eq_of_beq h5]

private theorem extSort_eq_of_beq : ∀ {x y : ExtSort}, (x == y) = true → x = y := by
  intro x y h
  cases x <;> cases y <;>
    first
      | exact Bool.noConfusion h
      | exact congrArg ExtSort.scalar (baseSort_eq_of_beq h)
      | exact congrArg ExtSort.node (eq_of_beq h)
      | exact congrArg ExtSort.edge (eq_of_beq h)
      | (rename_i G1 ss1 G2 ss2
         have h' : ((G1 == G2) && (ss1 == ss2)) = true := h
         simp only [Bool.and_eq_true] at h'
         rw [eq_of_beq h'.1,
             list_eq_of_beq (fun _ _ hb => nodeSchemaFull_eq_of_beq hb) _ _ h'.2])
      | (rename_i G1 ss1 G2 ss2
         have h' : ((G1 == G2) && (ss1 == ss2)) = true := h
         simp only [Bool.and_eq_true] at h'
         rw [eq_of_beq h'.1,
             list_eq_of_beq (fun _ _ hb => edgeSchemaFull_eq_of_beq hb) _ _ h'.2])

private theorem nullTag_eq_of_beq {a b : NullTag} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact Bool.noConfusion h

private theorem sortShape_eq_of_beq : ∀ (x y : SortShape), (x == y) = true → x = y := by
  intro x
  induction x with
  | single a =>
      intro y h
      cases y <;>
        first
          | exact Bool.noConfusion h
          | (rename_i b
             have h' : (a == b) = true := h
             exact congrArg SortShape.single (extSort_eq_of_beq h'))
  | any => intro y h; cases y <;> first | rfl | exact Bool.noConfusion h
  | bot => intro y h; cases y <;> first | rfl | exact Bool.noConfusion h
  | nullType => intro y h; cases y <;> first | rfl | exact Bool.noConfusion h
  | union ts =>
      intro y h
      cases y <;>
        first
          | exact Bool.noConfusion h
          | (rename_i ts2
             have h' : (ts == ts2) = true := h
             exact congrArg SortShape.union
               (list_eq_of_beq (fun _ _ hb => extSort_eq_of_beq hb) _ _ h'))
  | list s1 m1 ih =>
      intro y h
      cases y <;>
        first
          | exact Bool.noConfusion h
          | (rename_i s2 m2
             have h' : ((s1 == s2) && (m1 == m2)) = true := h
             simp only [Bool.and_eq_true] at h'
             rw [ih s2 h'.1, nullTag_eq_of_beq h'.2])
  | emptyFormer s1 m1 ih =>
      intro y h
      cases y <;>
        first
          | exact Bool.noConfusion h
          | (rename_i s2 m2
             have h' : ((s1 == s2) && (m1 == m2)) = true := h
             simp only [Bool.and_eq_true] at h'
             rw [ih s2 h'.1, nullTag_eq_of_beq h'.2])

private theorem gSort_eq_of_beq {t1 t2 : GSort} (h : (t1 == t2) = true) : t1 = t2 := by
  obtain ⟨s1, n1⟩ := t1
  obtain ⟨s2, n2⟩ := t2
  have h' : ((s1 == s2) && (n1 == n2)) = true := h
  simp only [Bool.and_eq_true] at h'
  rw [sortShape_eq_of_beq s1 s2 h'.1, nullTag_eq_of_beq h'.2]

-- ============================================================
--  Strong transport along `sortUnion` (UNION/OTHERWISE schemas)
-- ============================================================

private theorem looserNull_ne_null_left {n1 n2 : NullTag} (h : n1 ≠ .null) :
    RecordSchema.looserNull n1 n2 ≠ .null := by
  cases n1 <;> cases n2 <;>
    first
      | (simp [RecordSchema.looserNull]; done)
      | exact absurd rfl h

private theorem looserNull_ne_null_right {n1 n2 : NullTag} (h : n2 ≠ .null) :
    RecordSchema.looserNull n1 n2 ≠ .null := by
  cases n1 <;> cases n2 <;>
    first
      | (simp [RecordSchema.looserNull]; done)
      | exact absurd rfl h

private theorem strong_tag_ne_null {G : PropertyGraph} {v : Value}
    {s : SortShape} {n : NullTag} (hv : v ≠ .null)
    (h : ValueInhabitsS G v ⟨s, n⟩) : n ≠ .null := by
  intro hn
  subst hn
  exact absurd h.adm (by rw [adm_nonNull_nullTag_false hv]; simp)

/-- Build a strong union inhabitation from one strong branch. -/
private theorem strong_union_of_branch {G : PropertyGraph} {v : Value}
    {es : ExtSort} {ts : List ExtSort} {n : NullTag} (hv : v ≠ .null)
    (hmem : es ∈ ts) (hn : n ≠ .null)
    (hbr : ValueInhabitsS G v ⟨.single es, .val⟩) :
    ValueInhabitsS G v ⟨.union ts, n⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hadm := hbr.adm
    cases n with
    | val => exact union_adm_intro hmem hadm
    | nullable =>
        exact union_adm_intro hmem
          ((adm_nonNull_val_eq_nullable hv _).symm.trans hadm)
    | null => exact absurd rfl hn
  · intro _ _ _ _ hsh; exact absurd hsh (by simp)
  · intro _ _ _ _ hsh; exact absurd hsh (by simp)
  · intro _ _ _ hsh; exact absurd hsh (by simp)
  · intro ts' hsh _
    injection hsh with h1
    subst h1
    exact ⟨es, hmem, hbr⟩

/-- A member of the right operand survives into `sortUnion`'s merged
    union branch list. -/
private theorem mem_unionMerge {ts1 ts2 : List ExtSort} {es : ExtSort}
    (h : es ∈ ts2) :
    es ∈ ts1 ++ ts2.filter (fun t => !ts1.any (fun x => x == t)) := by
  cases hb : ts1.any (fun x => x == es) with
  | true =>
      obtain ⟨x, hx, hbeq⟩ := List.any_eq_true.mp hb
      rw [extSort_eq_of_beq hbeq] at hx
      exact List.mem_append.mpr (Or.inl hx)
  | false =>
      refine List.mem_append.mpr (Or.inr (List.mem_filter.mpr ⟨h, ?_⟩))
      rw [hb]
      rfl

set_option maxHeartbeats 1600000 in
/-- Strong inhabitation transports into `sortUnion` from the left. -/
private theorem strong_sortUnion_left {G : PropertyGraph} {v : Value}
    {t1 t2 : GSort} (h : ValueInhabitsS G v t1) :
    ValueInhabitsS G v (RecordSchema.sortUnion t1 t2) := by
  unfold RecordSchema.sortUnion
  split
  · exact h
  · obtain ⟨s1, n1⟩ := t1
    obtain ⟨s2, n2⟩ := t2
    have hadm := h.adm
    by_cases hv : v = .null
    · subst hv
      rcases s1 with es1 | _ | _ | _ | (_ | ⟨e1, ts1⟩) | ⟨ls1, ln1⟩ | ⟨fs1, fn1⟩ <;>
        rcases s2 with es2 | _ | _ | _ | (_ | ⟨e2, ts2⟩) | ⟨ls2, ln2⟩ | ⟨fs2, fn2⟩ <;>
        dsimp only <;> (repeat' split) <;>
        first
          | exact h
          | exact strong_any _
          | exact Bool.noConfusion hadm
          | exact strong_of_null (adm_null_toNullable hadm)
          | (refine strong_of_null ?_
             cases n1 <;> cases n2 <;>
               first
                 | rfl
                 | exact Bool.noConfusion hadm)
    · rcases s1 with es1 | _ | _ | _ | (_ | ⟨e1, ts1⟩) | ⟨ls1, ln1⟩ | ⟨fs1, fn1⟩ <;>
        rcases s2 with es2 | _ | _ | _ | (_ | ⟨e2, ts2⟩) | ⟨ls2, ln2⟩ | ⟨fs2, fn2⟩ <;>
        dsimp only <;> (repeat' split) <;>
        first
          | exact h
          | exact strong_any _
          | exact Bool.noConfusion hadm
          | (refine absurd hadm ?_
             cases v <;>
               first
                 | exact absurd rfl hv
                 | (cases n1 <;> exact fun hc => Bool.noConfusion hc))
          | exact strong_retag_ofVal hv (fun hc => NullTag.noConfusion hc)
              (strong_retag_toVal hv h)
          | exact strong_retag_ofVal hv
              (looserNull_ne_null_left (strong_tag_ne_null hv h))
              (strong_retag_toVal hv h)
          | exact strong_union_of_branch hv (List.Mem.head _)
              (fun hc => NullTag.noConfusion hc) (strong_retag_toVal hv h)
          | (rename_i hcond
             obtain ⟨x, hx, hbeq⟩ := List.any_eq_true.mp hcond
             rw [extSort_eq_of_beq hbeq] at hx
             exact strong_union_of_branch hv hx
               (looserNull_ne_null_left (strong_tag_ne_null hv h))
               (strong_retag_toVal hv h))
          | (obtain ⟨_, _, _, _, hB⟩ := h
             obtain ⟨es, hmem, hbr⟩ := hB _ rfl hv
             exact strong_union_of_branch hv (List.mem_append.mpr (Or.inl hmem))
               (fun hc => NullTag.noConfusion hc) hbr)

set_option maxHeartbeats 1600000 in
/-- Strong inhabitation transports into `sortUnion` from the right. -/
private theorem strong_sortUnion_right {G : PropertyGraph} {v : Value}
    {t1 t2 : GSort} (h : ValueInhabitsS G v t2) :
    ValueInhabitsS G v (RecordSchema.sortUnion t1 t2) := by
  unfold RecordSchema.sortUnion
  split
  · rename_i heq
    rw [gSort_eq_of_beq heq]
    exact h
  · obtain ⟨s1, n1⟩ := t1
    obtain ⟨s2, n2⟩ := t2
    have hadm := h.adm
    by_cases hv : v = .null
    · subst hv
      rcases s1 with es1 | _ | _ | _ | (_ | ⟨e1, ts1⟩) | ⟨ls1, ln1⟩ | ⟨fs1, fn1⟩ <;>
        rcases s2 with es2 | _ | _ | _ | (_ | ⟨e2, ts2⟩) | ⟨ls2, ln2⟩ | ⟨fs2, fn2⟩ <;>
        dsimp only <;> (repeat' split) <;>
        first
          | exact h
          | exact strong_any _
          | exact Bool.noConfusion hadm
          | exact strong_of_null (adm_null_toNullable hadm)
          | (refine strong_of_null ?_
             cases n1 <;> cases n2 <;>
               first
                 | rfl
                 | exact Bool.noConfusion hadm)
    · rcases s1 with es1 | _ | _ | _ | (_ | ⟨e1, ts1⟩) | ⟨ls1, ln1⟩ | ⟨fs1, fn1⟩ <;>
        rcases s2 with es2 | _ | _ | _ | (_ | ⟨e2, ts2⟩) | ⟨ls2, ln2⟩ | ⟨fs2, fn2⟩ <;>
        dsimp only <;> (repeat' split) <;>
        first
          | exact h
          | exact strong_any _
          | exact Bool.noConfusion hadm
          | (refine absurd hadm ?_
             cases v <;>
               first
                 | exact absurd rfl hv
                 | (cases n2 <;> exact fun hc => Bool.noConfusion hc))
          | exact strong_retag_ofVal hv (fun hc => NullTag.noConfusion hc)
              (strong_retag_toVal hv h)
          | exact strong_retag_ofVal hv
              (looserNull_ne_null_right (strong_tag_ne_null hv h))
              (strong_retag_toVal hv h)
          | exact strong_union_of_branch hv (List.Mem.tail _ (List.Mem.head _))
              (fun hc => NullTag.noConfusion hc) (strong_retag_toVal hv h)
          | (rename_i hcond
             obtain ⟨x, hx, hbeq⟩ := List.any_eq_true.mp hcond
             rw [extSort_eq_of_beq hbeq] at hx
             exact strong_union_of_branch hv hx
               (looserNull_ne_null_right (strong_tag_ne_null hv h))
               (strong_retag_toVal hv h))
          | exact strong_union_of_branch hv
              (List.mem_append.mpr (Or.inr (List.Mem.head _)))
              (fun hc => NullTag.noConfusion hc) (strong_retag_toVal hv h)
          | (obtain ⟨_, _, _, _, hB⟩ := h
             obtain ⟨es, hmem, hbr⟩ := hB _ rfl hv
             first
               | exact strong_union_of_branch hv (List.Mem.tail _ hmem)
                   (fun hc => NullTag.noConfusion hc) hbr
               | exact strong_union_of_branch hv (mem_unionMerge hmem)
                   (fun hc => NullTag.noConfusion hc) hbr)

/-- An expression-typing derivation for a bare variable is the variable
    rule followed by a (possibly empty) chain of subsumptions: the
    declared sort is reached from the schema sort by `Subtype`. -/
private theorem exprTyping_var_subtype {ctx : TypingCtx} {Ctx : RecordSchema}
    {box : AggDepth} {hat : RefCtx} {y : Name} {tau : GSort}
    {omega' : VarSet}
    (h : ExprTyping ctx Ctx box hat (.var y) tau omega') :
    ∃ tau0, Ctx.lookup y = some tau0 ∧ Subtype tau0 tau := by
  generalize he : Expr.var y = e0 at h
  induction h using ExprTyping.inductionOpaque with
  | var =>
      rename_i x tau1 hLookup
      injection he with hxy
      subst hxy
      exact ⟨tau1, hLookup, .refl tau1⟩
  | subsume =>
      rename_i _ hSub ih
      obtain ⟨tau0, hlk, hsub⟩ := ih he
      exact ⟨tau0, hlk, .trans hsub hSub⟩
  | constInt => exact Expr.noConfusion he
  | constString => exact Expr.noConfusion he
  | constBool => exact Expr.noConfusion he
  | constNull => exact Expr.noConfusion he
  | arithOp => exact Expr.noConfusion he
  | propAccessOpen => exact Expr.noConfusion he
  | propAccessSchema => exact Expr.noConfusion he
  | propAccessListOpen => exact Expr.noConfusion he
  | propAccessListClosed => exact Expr.noConfusion he
  | countSingleton => exact Expr.noConfusion he
  | aggSingleton => exact Expr.noConfusion he
  | countGroup => exact Expr.noConfusion he
  | aggGroup => exact Expr.noConfusion he
  | pred => exact Expr.noConfusion he

/-- Per-item strong Definition 6.1 projection soundness. Unaliased
    variables carry their binding's full strong inhabitation (upgraded
    from the weak pattern-level result on the transportable pattern
    schema); aliased bare variables additionally transport it along the
    subsumption chain via `valueInhabitsS_mono`; aliased non-variable
    expressions and aliased aggregates evaluate to scalars or null,
    where admissibility (Theorem 6.1 / the aggregate lemma) suffices. -/
private theorem projectItem_inhabitsS
    (ctx : TypingCtx) (G : PropertyGraph)
    (hWF : GraphValuesWF G)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G)
    (Gamma1 : RecordSchema) (rho : Record) (matched : BindingTable)
    (hRow : RecordInhabits G rho Gamma1)
    (hRt : RuntimeConfigWF G rho Gamma1)
    (pi : Projection) (Gpi : RecordSchema)
    (htr : SchemaTransportable Gamma1)
    (hProj : ProjectionTyping ctx Gamma1 pi Gpi) :
    RecordInhabitsS G (projectItem G ctx.graphSite rho matched pi) Gpi := by
  have hRowS : RecordInhabitsS G rho Gamma1 := recordInhabitsS_of_inhabits htr hRow
  cases hProj with
  | atom x tau hLookup =>
    apply singleton_recordInhabitsS
    show ValueInhabitsS G (evalExpr G ctx.graphSite rho (.var x)) tau
    exact hRowS.2 x tau (RecordSchema.lookup_some_mem hLookup)
  | alias' e x tau omega' hExpr =>
    apply singleton_recordInhabitsS
    by_cases hv : ∃ y, e = .var y
    · obtain ⟨y, rfl⟩ := hv
      obtain ⟨tau0, hlk, hsub⟩ := exprTyping_var_subtype hExpr
      have hs : ValueInhabitsS G (rho.lookup y) tau0 :=
        hRowS.2 y tau0 (RecordSchema.lookup_some_mem hlk)
      show ValueInhabitsS G (evalExpr G ctx.graphSite rho (.var y)) tau
      exact valueInhabitsS_mono hs hsub
    · have hne : ∀ y, e ≠ .var y := fun y h => hv ⟨y, h⟩
      have hAdm := expressionSoundness ctx Gamma1 .one .group e tau omega' hExpr
        rho G (recordConforms_of_inhabits hRow) hWF hRt hGraph
      exact strong_of_prim_or_null
        (evalExpr_not_var_prim_or_null G ctx.graphSite rho e hWF hne) hAdm
  | aggAs op qual e y tau omega' hExpr =>
    apply singleton_recordInhabitsS
    have hAdm := aggTable_admissible hExpr
      (matched.map fun r => evalExpr G ctx.graphSite r e)
    exact strong_of_prim_or_null (evalAggOnValues_prim_or_null op qual _) hAdm

-- ============================================================
--  Schema-union transport (record level) and the full query-level
--  strong soundness
-- ============================================================

/-- Rows of the left operand strongly inhabit the union schema. -/
private theorem recordInhabitsS_schemaUnion_left {G : PropertyGraph}
    {rho : Record} {G1 G2 : RecordSchema}
    (h : RecordInhabitsS G rho G1) :
    RecordInhabitsS G rho (RecordSchema.schemaUnion G1 G2) := by
  refine ⟨?_, ?_⟩
  · intro x
    rw [schemaUnion_mem]
    exact h.1 x
  · intro x t hxt
    obtain ⟨t1, hmem1, hcase⟩ := mem_schemaUnion hxt
    rcases hcase with ⟨t2, hlk2, ht⟩ | ⟨_, ht⟩
    · rw [ht]; exact strong_sortUnion_left (h.2 x t1 hmem1)
    · rw [ht]; exact h.2 x t1 hmem1

/-- Rows of the right operand strongly inhabit the union schema (using
    union compatibility for the domain agreement). -/
private theorem recordInhabitsS_schemaUnion_right {G : PropertyGraph}
    {rho : Record} {G1 G2 : RecordSchema}
    (hcompat : RecordSchema.unionCompatible G1 G2 = true)
    (h : RecordInhabitsS G rho G2) :
    RecordInhabitsS G rho (RecordSchema.schemaUnion G1 G2) := by
  refine ⟨?_, ?_⟩
  · intro x
    rw [schemaUnion_mem, h.1 x]
    exact (unionCompat_mem hcompat x).symm
  · intro x t hxt
    obtain ⟨t1, hmem1, hcase⟩ := mem_schemaUnion hxt
    rcases hcase with ⟨t2, hlk2, ht⟩ | ⟨hnone, ht⟩
    · rw [ht]; exact strong_sortUnion_right (h.2 x t2 (RecordSchema.lookup_some_mem hlk2))
    · exfalso
      have hx1 : G1.mem x = true := RecordSchema.mem_of_entry hmem1
      have hx2 : G2.mem x = true := by
        rw [← unionCompat_mem hcompat x]
        exact hx1
      obtain ⟨t2, hlk⟩ := RecordSchema.mem_lookup_some hx2
      rw [hlk] at hnone
      exact Option.noConfusion hnone

/-- Strong Definition 6.1 query type soundness (Theorem 6.3, closed
    sites, full query language).  A well-typed
    query's result table strongly inhabits its declared schema.  Every
    projection form is covered (aliased bare variables transport along
    the subsumption chain by `valueInhabitsS_mono`), and every composite
    operator is covered (UNION and OTHERWISE transport along the schema
    union via the strong branch witness).  `useGraph` leaves are
    discharged by the strong leaf premise `hUse`. -/
theorem queryTyping_inhabitsS
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
    (hType : QueryTyping ctx Q Gamma) :
    BTInhabitsS G (evalQuery ctx.catalog G ctx.graphSite Q) Gamma := by
  suffices H : ∀ (ctx' : TypingCtx) (Q' : Query) (Gamma' : RecordSchema),
      QueryTyping ctx' Q' Gamma' → ctx' = ctx →
      BTInhabitsS G (evalQuery ctx.catalog G ctx.graphSite Q') Gamma' by
    exact H ctx Q Gamma hType rfl
  intro ctx' Q' Gamma' hT
  induction hT with
  | matchFilter ctx0 P phi projs Gamma1 Gamma2 tPred omegaPred hG hPat hPred hPredSub hProj =>
    intro hEq
    subst hEq
    intro projRho hmem
    simp only [evalQuery] at hmem
    rw [List.mem_map] at hmem
    obtain ⟨rho, hrho, rfl⟩ := hmem
    have hrho0 : rho ∈ evalPattern G ctx0.graphSite P :=
      evalPatternTrail_subset _ _ _ _ (mem_of_filter hrho)
    have hRow : RecordInhabits G rho Gamma1 :=
      patExprSoundness_inhabits ctx0 G hCat Psi hPsi P Gamma1 hPat hGraph rho hrho0
    have hRt : RuntimeConfigWF G rho Gamma1 :=
      patExpr_runtimeWF ctx0 G Psi hPsi hCat
        (fun P' G' h' =>
          patExprSoundness ctx0 G hCat Psi hPsi
            (patternTyping_runtimeWFStrong ctx0 G Psi hPsi hCat) P' G' h' hGraph)
        P Gamma1 hPat rho hrho0
    exact projectionList_recordInhabitsS G ctx0.graphSite rho _ ctx0 Gamma1
      projs Gamma2
      (fun pi hpi Gpi hP =>
        projectItem_inhabitsS ctx0 G hWF hGraph Gamma1 rho _ hRow hRt pi Gpi
          (patExprTyping_transportable hPat) hP)
      hProj
  | matchReturn ctx0 P projs Gamma1 Gamma2 hG hPat hProj =>
    intro hEq
    subst hEq
    intro projRho hmem
    simp only [evalQuery] at hmem
    rw [List.mem_map] at hmem
    obtain ⟨rho, hrho, rfl⟩ := hmem
    have hrho0 : rho ∈ evalPattern G ctx0.graphSite P :=
      evalPatternTrail_subset _ _ _ _ hrho
    have hRow : RecordInhabits G rho Gamma1 :=
      patExprSoundness_inhabits ctx0 G hCat Psi hPsi P Gamma1 hPat hGraph rho hrho0
    have hRt : RuntimeConfigWF G rho Gamma1 :=
      patExpr_runtimeWF ctx0 G Psi hPsi hCat
        (fun P' G' h' =>
          patExprSoundness ctx0 G hCat Psi hPsi
            (patternTyping_runtimeWFStrong ctx0 G Psi hPsi hCat) P' G' h' hGraph)
        P Gamma1 hPat rho hrho0
    exact projectionList_recordInhabitsS G ctx0.graphSite rho _ ctx0 Gamma1
      projs Gamma2
      (fun pi hpi Gpi hP =>
        projectItem_inhabitsS ctx0 G hWF hGraph Gamma1 rho _ hRow hRt pi Gpi
          (patExprTyping_transportable hPat) hP)
      hProj
  | useGraph ctx0 g inner Gu hResolve hBody ih =>
    intro hEq
    subst hEq
    exact hUse g inner Gu hResolve hBody
  | cqLift ctx0 Q0 Gamma0 h ih =>
    intro hEq
    exact ih hEq
  | composite ctx0 op Q1 Q2 Gamma1 Gamma2 h1 h2 hCompat ih1 ih2 =>
    intro hEq
    subst hEq
    intro rho hmem
    simp only [evalQuery] at hmem
    cases op with
    | union =>
        have hmem' : rho ∈ evalQuery ctx0.catalog G ctx0.graphSite Q1
            ++ evalQuery ctx0.catalog G ctx0.graphSite Q2 := hmem
        rcases List.mem_append.mp hmem' with hL | hR
        · exact recordInhabitsS_schemaUnion_left (ih1 rfl rho hL)
        · exact recordInhabitsS_schemaUnion_right hCompat (ih2 rfl rho hR)
    | otherwise =>
        have hmem' : rho ∈
            (if (evalQuery ctx0.catalog G ctx0.graphSite Q1).isEmpty
              then evalQuery ctx0.catalog G ctx0.graphSite Q2
              else evalQuery ctx0.catalog G ctx0.graphSite Q1) := hmem
        split at hmem'
        · exact recordInhabitsS_schemaUnion_right hCompat (ih2 rfl rho hmem')
        · exact recordInhabitsS_schemaUnion_left (ih1 rfl rho hmem')
    | exceptDistinct =>
        exact ih1 rfl rho (applySetOp_mem_left (Or.inl rfl) hmem)
    | exceptAll =>
        exact ih1 rfl rho (applySetOp_mem_left (Or.inr (Or.inl rfl)) hmem)
    | intersectDistinct =>
        exact ih1 rfl rho (applySetOp_mem_left (Or.inr (Or.inr (Or.inl rfl))) hmem)
    | intersectAll =>
        exact ih1 rfl rho (applySetOp_mem_left (Or.inr (Or.inr (Or.inr rfl))) hmem)

/-- Definition 6.1-faithful query type soundness (Theorem 6.3, closed
    sites, full query language).  Weak-relation form
    of `queryTyping_inhabitsS`: a well-typed query's result table
    inhabits its declared schema in the full Definition 6.1 sense, with
    no fragment restriction. -/
theorem queryTyping_inhabits
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
    (hType : QueryTyping ctx Q Gamma) :
    BTInhabits G (evalQuery ctx.catalog G ctx.graphSite Q) Gamma :=
  btInhabitsS_to_inhabits
    (queryTyping_inhabitsS ctx G hCat Psi hPsi hWF hUse hGraph hType)

-- ============================================================
--  Headline soundness results (formerly axioms, now theorems)
--
--  The Theorem 6.3 / Corollary 6.1 conclusions in `BTConforms` form are
--  `queryTypeSoundness_composed` / `compositeQuerySoundness_composed` above (no
--  longer axioms -- proven, carrying the explicit leaf obligations). The `_bool`
--  wrappers below give the executable (`bindingTableConforms = true`) form by
--  composing `bool_of_btConforms` with them.
-- ============================================================

theorem queryTypeSoundness_bool
    (ctx : TypingCtx) (G : PropertyGraph)
    (hCat : ∀ Psi, ctx.schemaMap.lookup ctx.graphSite = some Psi →
              graphConformsSchema G Psi = true)
    (Psi : GraphSchemaFull) (hPsi : ctx.schemaMap.lookup ctx.graphSite = some Psi)
    (hWF : GraphValuesWF G)
    (hUseGraph : ∀ (graphName : Name) (inner : Query) (GammaU : RecordSchema),
        (ctx.catalog.lookup graphName).isSome = true →
        QueryTyping { ctx with graphSite := graphName } inner GammaU →
        BTConforms (evalQuery ctx.catalog G ctx.graphSite (.useGraph graphName inner)) GammaU)
    (Q : Query) (Gamma : RecordSchema) (hType : QueryTyping ctx Q Gamma)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G) :
    RecordSchema.bindingTableConforms (evalQuery ctx.catalog G ctx.graphSite Q) Gamma = true :=
  bool_of_btConforms _ _
    (queryTypeSoundness_composed ctx G hCat
      Psi hPsi hWF hUseGraph
      Q Gamma hType hGraph)

theorem compositeQuerySoundness_bool
    (ctx : TypingCtx) (G : PropertyGraph)
    (hCat : ∀ Psi, ctx.schemaMap.lookup ctx.graphSite = some Psi →
              graphConformsSchema G Psi = true)
    (Psi : GraphSchemaFull) (hPsi : ctx.schemaMap.lookup ctx.graphSite = some Psi)
    (hWF : GraphValuesWF G)
    (hUseGraph : ∀ (graphName : Name) (inner : Query) (GammaU : RecordSchema),
        (ctx.catalog.lookup graphName).isSome = true →
        QueryTyping { ctx with graphSite := graphName } inner GammaU →
        BTConforms (evalQuery ctx.catalog G ctx.graphSite (.useGraph graphName inner)) GammaU)
    (op : SetOp) (Q1 Q2 : Query) (Gamma1 Gamma2 : RecordSchema)
    (hType1 : QueryTyping ctx Q1 Gamma1)
    (hType2 : QueryTyping ctx Q2 Gamma2)
    (hCompat : opCompatible op Gamma1 Gamma2 = true)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G) :
    RecordSchema.bindingTableConforms
      (applySetOp op
        (evalQuery ctx.catalog G ctx.graphSite Q1)
        (evalQuery ctx.catalog G ctx.graphSite Q2))
      (opCombine op Gamma1 Gamma2) = true :=
  bool_of_btConforms _ _
    (compositeQuerySoundness_composed ctx G hCat
      Psi hPsi hWF hUseGraph
      op Q1 Q2 Gamma1 Gamma2 hType1 hType2 hCompat hGraph)

theorem patExprSoundness'
    (ctx : TypingCtx) (G : PropertyGraph)
    (hCat : ∀ Psi', ctx.schemaMap.lookup ctx.graphSite = some Psi' →
              graphConformsSchema G Psi' = true)
    (Psi : GraphSchemaFull) (hPsi : ctx.schemaMap.lookup ctx.graphSite = some Psi)
    (P : Pattern) (GammaOut : RecordSchema)
    (hType : PatExprTyping ctx P GammaOut)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G) :
    BTConforms (evalPattern G ctx.graphSite P) GammaOut :=
  patExprSoundness ctx G hCat Psi hPsi
    (patternTyping_runtimeWFStrong ctx G Psi hPsi hCat) P GammaOut hType hGraph

theorem compositeQuerySoundness_catalogWide
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
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G) :
    BTConforms
      (applySetOp op
        (evalQuery ctx.catalog G ctx.graphSite Q1)
        (evalQuery ctx.catalog G ctx.graphSite Q2))
      (opCombine op Gamma1 Gamma2) :=
  setOp_conforms op _ _ Gamma1 Gamma2 hCompat
    (queryTypeSoundness_composed_catalogWide hCat hWF hSchemaCat ctx G Q1 Gamma1 hType1 hGraph)
    (queryTypeSoundness_composed_catalogWide hCat hWF hSchemaCat ctx G Q2 Gamma2 hType2 hGraph)

-- ============================================================
--  theta_D faithfulness bridge
--
--  The typing's endpoint filters compare schemas by LABEL SET
--  (`labelSetEq`); the paper's theta_D compares by schema equality.
--  The label-set comparison is deliberately coarser: the strong runtime
--  invariant quantifies over ALL conformant catalog schemas of a matched
--  element, and under full schema equality that universal form fails
--  (a conformant schema with the same labels but a different property
--  schema would escape the refined lists), while the natural theta_D
--  witness -- the edge schema's own endpoint schema -- need not even be
--  a catalog member.  On WELL-FORMED catalogs (endpoint-closed and
--  label-discriminated) the two comparisons coincide, so the
--  mechanization's refinement filters ARE the paper's theta_D filters
--  there.  This section proves that equivalence.
-- ============================================================

/-- Node schemas are discriminated by their label sets. -/
def SchemaLabelUnique (Psi : GraphSchemaFull) : Prop :=
  ∀ z1 ∈ Psi.nodeSchemas, ∀ z2 ∈ Psi.nodeSchemas,
    labelSetEq z1.labels z2.labels = true → z1 = z2

/-- Every edge schema's endpoint schemas are catalog members. -/
def SchemaEndpointClosed (Psi : GraphSchemaFull) : Prop :=
  ∀ es ∈ Psi.edgeSchemas,
    es.srcSchema ∈ Psi.nodeSchemas ∧ es.dstSchema ∈ Psi.nodeSchemas

private theorem labelSetEq_refl (l : List Name) : labelSetEq l l = true := by
  simp only [labelSetEq, Bool.and_eq_true]
  refine ⟨⟨beq_self_eq_true _, ?_⟩, ?_⟩ <;>
    (rw [List.all_eq_true]
     intro x hx
     rw [List.any_eq_true]
     exact ⟨x, hx, beq_self_eq_true x⟩)

/-- On a label-discriminated catalog, the label-set comparison of two
    catalog schemas IS schema equality, as booleans. -/
private theorem labelSetEq_eq_beq {Psi : GraphSchemaFull}
    (hLU : SchemaLabelUnique Psi) {z1 z2 : NodeSchemaFull}
    (h1 : z1 ∈ Psi.nodeSchemas) (h2 : z2 ∈ Psi.nodeSchemas) :
    labelSetEq z1.labels z2.labels = (z1 == z2) := by
  cases hls : labelSetEq z1.labels z2.labels with
  | true =>
      have heq := hLU z1 h1 z2 h2 hls
      subst heq
      exact (nodeSchemaFull_beq_self z1).symm
  | false =>
      cases hbq : z1 == z2 with
      | false => rfl
      | true =>
          exfalso
          have heq := nodeSchemaFull_eq_of_beq hbq
          subst heq
          rw [labelSetEq_refl] at hls
          exact Bool.noConfusion hls

/-- theta_D faithfulness, per triple.  On a well-formed catalog the
    label-set triple compatibility is exactly the paper's theta_D. -/
theorem tripleCompat_eq_thetaD {Psi : GraphSchemaFull}
    (hLU : SchemaLabelUnique Psi) (hEC : SchemaEndpointClosed Psi)
    {z1 z3 : NodeSchemaFull} {es : EdgeSchemaFull} (dir : Direction)
    (h1 : z1 ∈ Psi.nodeSchemas) (h3 : z3 ∈ Psi.nodeSchemas)
    (hes : es ∈ Psi.edgeSchemas) :
    tripleCompat z1 es z3 dir = thetaD dir z1 es z3 := by
  obtain ⟨hsrc, hdst⟩ := hEC es hes
  simp only [tripleCompat, thetaD]
  rw [labelSetEq_eq_beq hLU h1 hsrc, labelSetEq_eq_beq hLU h3 hdst,
      labelSetEq_eq_beq hLU h1 hdst, labelSetEq_eq_beq hLU h3 hsrc]

private theorem list_any_congr {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.any p = l.any q
  | [], _ => rfl
  | a :: t, h => by
      simp only [List.any_cons]
      rw [h a (List.mem_cons_self a t),
          list_any_congr (fun x hx => h x (List.mem_cons_of_mem a hx))]

private theorem list_filter_congr {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.filter p = l.filter q
  | [], _ => rfl
  | a :: t, h => by
      simp only [List.filter]
      rw [h a (List.mem_cons_self a t),
          list_filter_congr (fun x hx => h x (List.mem_cons_of_mem a hx))]

/-- The refined source projection is the theta_D projection pi_1 on a
    well-formed catalog. -/
theorem refineSrcByCompat_eq_thetaD {Psi : GraphSchemaFull}
    (hLU : SchemaLabelUnique Psi) (hEC : SchemaEndpointClosed Psi)
    {sN1 sN3 : List NodeSchemaFull} {sE2 : List EdgeSchemaFull} (dir : Direction)
    (hN1 : ∀ z ∈ sN1, z ∈ Psi.nodeSchemas)
    (hN3 : ∀ z ∈ sN3, z ∈ Psi.nodeSchemas)
    (hE2 : ∀ e ∈ sE2, e ∈ Psi.edgeSchemas) :
    refineSrcByCompat sN1 sE2 sN3 dir
      = sN1.filter (fun z1 => sE2.any fun es => sN3.any fun z3 =>
          thetaD dir z1 es z3) := by
  unfold refineSrcByCompat
  refine list_filter_congr ?_
  intro z1 hz1
  refine list_any_congr ?_
  intro es hes
  refine list_any_congr ?_
  intro z3 hz3
  exact tripleCompat_eq_thetaD hLU hEC dir (hN1 z1 hz1) (hN3 z3 hz3) (hE2 es hes)

/-- The refined edge projection is the theta_D projection pi_2 on a
    well-formed catalog. -/
theorem refineEdgeByCompat_eq_thetaD {Psi : GraphSchemaFull}
    (hLU : SchemaLabelUnique Psi) (hEC : SchemaEndpointClosed Psi)
    {sN1 sN3 : List NodeSchemaFull} {sE2 : List EdgeSchemaFull} (dir : Direction)
    (hN1 : ∀ z ∈ sN1, z ∈ Psi.nodeSchemas)
    (hN3 : ∀ z ∈ sN3, z ∈ Psi.nodeSchemas)
    (hE2 : ∀ e ∈ sE2, e ∈ Psi.edgeSchemas) :
    refineEdgeByCompat sN1 sE2 sN3 dir
      = sE2.filter (fun es => sN1.any fun z1 => sN3.any fun z3 =>
          thetaD dir z1 es z3) := by
  unfold refineEdgeByCompat
  refine list_filter_congr ?_
  intro es hes
  refine list_any_congr ?_
  intro z1 hz1
  refine list_any_congr ?_
  intro z3 hz3
  exact tripleCompat_eq_thetaD hLU hEC dir (hN1 z1 hz1) (hN3 z3 hz3) (hE2 es hes)

/-- The refined target projection is the theta_D projection pi_3 on a
    well-formed catalog. -/
theorem refineDstByCompat_eq_thetaD {Psi : GraphSchemaFull}
    (hLU : SchemaLabelUnique Psi) (hEC : SchemaEndpointClosed Psi)
    {sN1 sN3 : List NodeSchemaFull} {sE2 : List EdgeSchemaFull} (dir : Direction)
    (hN1 : ∀ z ∈ sN1, z ∈ Psi.nodeSchemas)
    (hN3 : ∀ z ∈ sN3, z ∈ Psi.nodeSchemas)
    (hE2 : ∀ e ∈ sE2, e ∈ Psi.edgeSchemas) :
    refineDstByCompat sN1 sE2 sN3 dir
      = sN3.filter (fun z3 => sN1.any fun z1 => sE2.any fun es =>
          thetaD dir z1 es z3) := by
  unfold refineDstByCompat
  refine list_filter_congr ?_
  intro z3 hz3
  refine list_any_congr ?_
  intro z1 hz1
  refine list_any_congr ?_
  intro es hes
  exact tripleCompat_eq_thetaD hLU hEC dir (hN1 z1 hz1) (hN3 z3 hz3) (hE2 es hes)

/-- The atom label filters only select catalog schemas (feeds the
    membership premises of the theta_D bridge at the refinement rules'
    use sites). -/
private theorem labelFilterNodeSchemas_subset (Psi : GraphSchemaFull) :
    ∀ (l : LabelExpr), ∀ z ∈ labelFilterNodeSchemas Psi l, z ∈ Psi.nodeSchemas := by
  intro l
  induction l with
  | atom name => intro z hz; exact (List.mem_filter.mp hz).1
  | wildcard => intro z hz; exact (List.mem_filter.mp hz).1
  | neg l ih => intro z hz; exact (List.mem_filter.mp hz).1
  | conj l1 l2 ih1 ih2 =>
      intro z hz
      exact ih1 z (List.mem_filter.mp hz).1
  | disj l1 l2 ih1 ih2 =>
      intro z hz
      unfold labelFilterNodeSchemas at hz
      rcases List.mem_append.mp hz with h1 | h2
      · exact ih1 z h1
      · exact ih2 z (List.mem_filter.mp h2).1

theorem resolveNodeSchemas_subset (Psi : GraphSchemaFull)
    (labels : Option LabelExpr) :
    ∀ z ∈ resolveNodeSchemas Psi labels, z ∈ Psi.nodeSchemas := by
  intro z hz
  cases labels with
  | none => exact hz
  | some l => exact labelFilterNodeSchemas_subset Psi l z hz

private theorem labelFilterEdgeSchemas_subset (Psi : GraphSchemaFull) :
    ∀ (l : LabelExpr), ∀ e ∈ labelFilterEdgeSchemas Psi l, e ∈ Psi.edgeSchemas := by
  intro l
  induction l with
  | atom name => intro e he; exact (List.mem_filter.mp he).1
  | wildcard => intro e he; exact (List.mem_filter.mp he).1
  | neg l ih => intro e he; exact (List.mem_filter.mp he).1
  | conj l1 l2 ih1 ih2 =>
      intro e he
      exact ih1 e (List.mem_filter.mp he).1
  | disj l1 l2 ih1 ih2 =>
      intro e he
      unfold labelFilterEdgeSchemas at he
      rcases List.mem_append.mp he with h1 | h2
      · exact ih1 e h1
      · exact ih2 e (List.mem_filter.mp h2).1

theorem resolveEdgeSchemas_subset (Psi : GraphSchemaFull)
    (labels : Option LabelExpr) :
    ∀ e ∈ resolveEdgeSchemas Psi labels, e ∈ Psi.edgeSchemas := by
  intro e he
  cases labels with
  | none => exact he
  | some l => exact labelFilterEdgeSchemas_subset Psi l e he

-- ============================================================
--  Paper-faithful composite query soundness (single operator)
--
--  Corollary 6.1 as printed: the composite judgment |-_circledast
--  threads one operator through the derivation (CompQueryTyping).
--  Soundness transports along the erasure into QueryTyping.
-- ============================================================

/-- Corollary 6.1, paper-faithful single-operator form (big-step).
    A composite query well typed in the operator-indexed judgment
    evaluates to a binding table conforming to its combined schema. -/
theorem compQueryTypeSoundness_mixedSites
    (hCat : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' →
        ∀ Psi, ctx'.schemaMap.lookup ctx'.graphSite = some Psi →
          graphConformsSchema G' Psi = true)
    (hWF : ∀ (ctx' : TypingCtx) (G' : PropertyGraph),
        ctx'.catalog.lookup ctx'.graphSite = some G' → GraphValuesWF G')
    (ctx : TypingCtx) (G : PropertyGraph)
    (op : SetOp) (q : Query) (Gamma : RecordSchema)
    (hType : CompQueryTyping ctx op q Gamma)
    (hGraph : ctx.catalog.lookup ctx.graphSite = some G) :
    BTConforms (evalQuery ctx.catalog G ctx.graphSite q) Gamma :=
  queryTypeSoundness_composed_mixedSites hCat hWF ctx G q Gamma
    hType.toQueryTyping hGraph

end MGQL
