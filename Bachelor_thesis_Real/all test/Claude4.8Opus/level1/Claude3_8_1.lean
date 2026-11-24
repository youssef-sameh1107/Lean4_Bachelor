/-
Regular languages are closed under concatenation.

We use Mathlib's own definition of regularity, `Language.IsRegular` (in
`Mathlib/Computability/DFA.lean`):

    def Language.IsRegular {T : Type u} (L : Language T) : Prop :=
      ∃ σ : Type, ∃ _ : Fintype σ, ∃ M : DFA T σ, M.accepts = L

i.e. `L` is regular iff it is recognised by a DFA with finitely many states.

Mathlib already proves closure under complement, union, intersection and
reversal, but NOT under concatenation, so we build it here.

Strategy (the textbook Thompson-style construction).  Given DFAs `M₁`, `M₂`
recognising `L₁`, `L₂`, we build an ε-NFA on the disjoint union of states
`σ₁ ⊕ σ₂`:

  * inside `inl` we run `M₁`, inside `inr` we run `M₂`;
  * from any `M₁`-accepting state there is an ε-transition (`none`) to `M₂`'s
    start state;
  * the start state is `inl M₁.start`; the accepting states are the `inr` of
    `M₂`-accepting states.

We prove this ε-NFA recognises `L₁ * L₂` using Mathlib's path characterisation
`εNFA.mem_accepts_iff_exists_path`, then push it through
`εNFA.toNFA` and `NFA.toDFA` (the subset construction) — both of which preserve
`accepts` — to obtain a *finite-state* DFA, witnessing `IsRegular`.
-/
import Mathlib

open Computability εNFA

namespace Language
#count_heartbeats in --4
/-! ### A `cons` characterisation of ε-NFA paths

`εNFA.IsPath` ships with `isPath_nil`, `isPath_singleton` and `isPath_append`,
but no `cons` lemma.  We derive one from `isPath_append`. -/

theorem isPath_cons_iff {α σ : Type*} {M : εNFA α σ} {s u : σ} {a : Option α}
    {l : List (Option α)} :
    M.IsPath s u (a :: l) ↔ ∃ t ∈ M.step s a, M.IsPath t u l := by
  have h : a :: l = [a] ++ l := rfl
  rw [h, M.isPath_append]
  constructor
  · rintro ⟨t, h1, h2⟩; exact ⟨t, M.isPath_singleton.mp h1, h2⟩
  · rintro ⟨t, h1, h2⟩; exact ⟨t, M.isPath_singleton.mpr h1, h2⟩
#count_heartbeats in --10
/-- Reducing the options of a list that is entirely `some`s gives the list back. -/
theorem reduceOption_map_some {α : Type*} (w : List α) :
    (w.map some).reduceOption = w := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [List.map_cons, List.reduceOption_cons_of_some, ih]

/-! ### The concatenation ε-NFA -/
#count_heartbeats in --128
/-- The ε-NFA recognising the concatenation of the languages of two DFAs. -/
def concatεNFA {α σ₁ σ₂ : Type*} (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    εNFA α (σ₁ ⊕ σ₂) where
  step s a := match s, a with
    | Sum.inl p, some c => {Sum.inl (M₁.step p c)}
    | Sum.inr q, some c => {Sum.inr (M₂.step q c)}
    | Sum.inl p, none   => {x | p ∈ M₁.accept ∧ x = Sum.inr M₂.start}
    | Sum.inr _, none   => ∅
  start := {Sum.inl M₁.start}
  accept := {x | ∃ q ∈ M₂.accept, x = Sum.inr q}

section
variable {α σ₁ σ₂ : Type*} (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
#count_heartbeats in --30
@[simp] theorem concatεNFA_step_inl_some (p : σ₁) (c : α) :
    (concatεNFA M₁ M₂).step (Sum.inl p) (some c) = {Sum.inl (M₁.step p c)} := rfl
#count_heartbeats in --30
@[simp] theorem concatεNFA_step_inr_some (q : σ₂) (c : α) :
    (concatεNFA M₁ M₂).step (Sum.inr q) (some c) = {Sum.inr (M₂.step q c)} := rfl
#count_heartbeats in --36
@[simp] theorem concatεNFA_step_inl_none (p : σ₁) :
    (concatεNFA M₁ M₂).step (Sum.inl p) none
      = {x | p ∈ M₁.accept ∧ x = Sum.inr M₂.start} := rfl
#count_heartbeats in --25
@[simp] theorem concatεNFA_step_inr_none (q : σ₂) :
    (concatεNFA M₁ M₂).step (Sum.inr q) none = ∅ := rfl
#count_heartbeats in --24
@[simp] theorem concatεNFA_start :
    (concatεNFA M₁ M₂).start = {Sum.inl M₁.start} := rfl
#count_heartbeats in --33
@[simp] theorem concatεNFA_accept :
    (concatεNFA M₁ M₂).accept = {x | ∃ q ∈ M₂.accept, x = Sum.inr q} := rfl

/-! ### Structural lemmas about paths in `concatεNFA M₁ M₂` -/
#count_heartbeats in --22
/-- Once on the `inr` side, a path can never leave it. -/
theorem concatεNFA_isPath_inr_trap :
    ∀ (s : σ₂) (u : σ₁ ⊕ σ₂) (l : List (Option α)),
      (concatεNFA M₁ M₂).IsPath (Sum.inr s) u l → ∃ q, u = Sum.inr q := by
  intro s u l
  induction l generalizing s with
  | nil => intro h; rw [isPath_nil] at h; exact ⟨s, h.symm⟩
  | cons a l ih =>
    intro h
    rw [isPath_cons_iff] at h
    obtain ⟨t, ht, hpath⟩ := h
    cases a with
    | none =>
      rw [concatεNFA_step_inr_none] at ht
      exact absurd ht (Set.not_mem_empty _)
    | some c =>
      rw [concatεNFA_step_inr_some, Set.mem_singleton_iff] at ht
      subst ht
      exact ih (M₂.step s c) hpath
#count_heartbeats in --27
/-- A path that stays on the `inl` side just runs `M₁`. -/
theorem concatεNFA_isPath_inl (r : σ₁) :
    ∀ (p : σ₁) (l : List (Option α)),
      (concatεNFA M₁ M₂).IsPath (Sum.inl p) (Sum.inl r) l ↔
        ∃ w : List α, l = w.map some ∧ M₁.evalFrom p w = r := by
  intro p l
  induction l generalizing p with
  | nil =>
    rw [isPath_nil, Sum.inl.injEq]
    constructor
    · rintro rfl; exact ⟨[], rfl, rfl⟩
    · rintro ⟨w, hw, hev⟩
      cases w with
      | nil => rw [DFA.evalFrom_nil] at hev; exact hev
      | cons c w' => simp at hw
  | cons a l ih =>
    constructor
    · intro h
      rw [isPath_cons_iff] at h
      obtain ⟨t, ht, hpath⟩ := h
      cases a with
      | some c =>
        rw [concatεNFA_step_inl_some, Set.mem_singleton_iff] at ht
        subst ht
        obtain ⟨w, hw, hev⟩ := (ih (M₁.step p c)).mp hpath
        exact ⟨c :: w, by rw [List.map_cons, hw], by rw [DFA.evalFrom_cons]; exact hev⟩
      | none =>
        rw [concatεNFA_step_inl_none, Set.mem_setOf_eq] at ht
        obtain ⟨hp, rfl⟩ := ht
        obtain ⟨q', hq'⟩ :=
          concatεNFA_isPath_inr_trap M₁ M₂ M₂.start (Sum.inl r) l hpath
        simp at hq'
    · rintro ⟨w, hw, hev⟩
      cases w with
      | nil => simp at hw
      | cons c w' =>
        rw [List.map_cons] at hw
        injection hw with ha hl
        subst ha; subst hl
        rw [DFA.evalFrom_cons] at hev
        rw [isPath_cons_iff]
        exact ⟨Sum.inl (M₁.step p c), by simp, (ih (M₁.step p c)).mpr ⟨w', rfl, hev⟩⟩
#count_heartbeats in --27
/-- A path that stays on the `inr` side just runs `M₂`. -/
theorem concatεNFA_isPath_inr (q : σ₂) :
    ∀ (s : σ₂) (l : List (Option α)),
      (concatεNFA M₁ M₂).IsPath (Sum.inr s) (Sum.inr q) l ↔
        ∃ w : List α, l = w.map some ∧ M₂.evalFrom s w = q := by
  intro s l
  induction l generalizing s with
  | nil =>
    rw [isPath_nil, Sum.inr.injEq]
    constructor
    · rintro rfl; exact ⟨[], rfl, rfl⟩
    · rintro ⟨w, hw, hev⟩
      cases w with
      | nil => rw [DFA.evalFrom_nil] at hev; exact hev
      | cons c w' => simp at hw
  | cons a l ih =>
    constructor
    · intro h
      rw [isPath_cons_iff] at h
      obtain ⟨t, ht, hpath⟩ := h
      cases a with
      | some c =>
        rw [concatεNFA_step_inr_some, Set.mem_singleton_iff] at ht
        subst ht
        obtain ⟨w, hw, hev⟩ := (ih (M₂.step s c)).mp hpath
        exact ⟨c :: w, by rw [List.map_cons, hw], by rw [DFA.evalFrom_cons]; exact hev⟩
      | none =>
        rw [concatεNFA_step_inr_none] at ht
        exact absurd ht (Set.not_mem_empty _)
    · rintro ⟨w, hw, hev⟩
      cases w with
      | nil => simp at hw
      | cons c w' =>
        rw [List.map_cons] at hw
        injection hw with ha hl
        subst ha; subst hl
        rw [DFA.evalFrom_cons] at hev
        rw [isPath_cons_iff]
        exact ⟨Sum.inr (M₂.step s c), by simp, (ih (M₂.step s c)).mpr ⟨w', rfl, hev⟩⟩
#count_heartbeats in --63
/-- A full accepting-shaped path from `inl p` to `inr q` crosses the boundary
exactly once, at the unique ε-transition. -/
theorem concatεNFA_isPath_cross (q : σ₂) :
    ∀ (p : σ₁) (l : List (Option α)),
      (concatεNFA M₁ M₂).IsPath (Sum.inl p) (Sum.inr q) l ↔
        ∃ (l₁ l₂ : List (Option α)) (r : σ₁),
          l = l₁ ++ none :: l₂ ∧
          (concatεNFA M₁ M₂).IsPath (Sum.inl p) (Sum.inl r) l₁ ∧
          r ∈ M₁.accept ∧
          (concatεNFA M₁ M₂).IsPath (Sum.inr M₂.start) (Sum.inr q) l₂ := by
  intro p l
  constructor
  · induction l generalizing p with
    | nil =>
      intro h
      rw [isPath_nil] at h
      simp at h
    | cons a l ih =>
      intro h
      rw [isPath_cons_iff] at h
      obtain ⟨t, ht, hpath⟩ := h
      cases a with
      | some c =>
        rw [concatεNFA_step_inl_some, Set.mem_singleton_iff] at ht
        subst ht
        obtain ⟨l₁, l₂, r, rfl, hpl, hr, hpr⟩ := ih (M₁.step p c) hpath
        refine ⟨some c :: l₁, l₂, r, rfl, ?_, hr, hpr⟩
        rw [isPath_cons_iff]
        exact ⟨Sum.inl (M₁.step p c), by simp, hpl⟩
      | none =>
        rw [concatεNFA_step_inl_none, Set.mem_setOf_eq] at ht
        obtain ⟨hp, rfl⟩ := ht
        exact ⟨[], l, p, rfl, (concatεNFA M₁ M₂).isPath_nil.mpr rfl, hp, hpath⟩
  · rintro ⟨l₁, l₂, r, rfl, hpl, hr, hpr⟩
    rw [isPath_append]
    refine ⟨Sum.inl r, hpl, ?_⟩
    rw [isPath_cons_iff]
    refine ⟨Sum.inr M₂.start, ?_, hpr⟩
    simp only [concatεNFA_step_inl_none, Set.mem_setOf_eq]
    exact ⟨hr, rfl⟩

/-! ### Correctness of the construction -/
#count_heartbeats in --23
/-- The concatenation ε-NFA recognises exactly `M₁.accepts * M₂.accepts`. -/
theorem concatεNFA_accepts :
    (concatεNFA M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext x
  rw [mem_accepts_iff_exists_path, mem_mul]
  constructor
  · rintro ⟨s₁, s₂, x', hs₁, hs₂, hx', hpath⟩
    rw [concatεNFA_start, Set.mem_singleton_iff] at hs₁
    subst hs₁
    rw [concatεNFA_accept, Set.mem_setOf_eq] at hs₂
    obtain ⟨q₂, hq₂, rfl⟩ := hs₂
    obtain ⟨l₁, l₂, r, rfl, hpl, hr, hpr⟩ :=
      (concatεNFA_isPath_cross M₁ M₂ _ _ _).mp hpath
    obtain ⟨w₁, rfl, hw₁⟩ := (concatεNFA_isPath_inl M₁ M₂ _ _ _).mp hpl
    obtain ⟨w₂, rfl, hw₂⟩ := (concatεNFA_isPath_inr M₁ M₂ _ _ _).mp hpr
    refine ⟨w₁, ?_, w₂, ?_, ?_⟩
    · rw [DFA.mem_accepts]
      show M₁.evalFrom M₁.start w₁ ∈ M₁.accept
      rw [hw₁]; exact hr
    · rw [DFA.mem_accepts]
      show M₂.evalFrom M₂.start w₂ ∈ M₂.accept
      rw [hw₂]; exact hq₂
    · rw [← hx', List.reduceOption_append, reduceOption_map_some,
        List.reduceOption_cons_of_none, reduceOption_map_some]
  · rintro ⟨w₁, hw₁, w₂, hw₂, rfl⟩
    refine ⟨Sum.inl M₁.start, Sum.inr (M₂.evalFrom M₂.start w₂),
      (w₁.map some) ++ none :: (w₂.map some), ?_, ?_, ?_, ?_⟩
    · simp
    · rw [concatεNFA_accept, Set.mem_setOf_eq]
      refine ⟨M₂.evalFrom M₂.start w₂, ?_, rfl⟩
      rw [DFA.mem_accepts] at hw₂; exact hw₂
    · rw [List.reduceOption_append, reduceOption_map_some,
        List.reduceOption_cons_of_none, reduceOption_map_some]
    · rw [concatεNFA_isPath_cross]
      refine ⟨w₁.map some, w₂.map some, M₁.evalFrom M₁.start w₁, rfl, ?_, ?_, ?_⟩
      · rw [concatεNFA_isPath_inl]; exact ⟨w₁, rfl, rfl⟩
      · rw [DFA.mem_accepts] at hw₁; exact hw₁
      · rw [concatεNFA_isPath_inr]; exact ⟨w₂, rfl, rfl⟩

end

/-! ### Closure of regular languages under concatenation -/
#count_heartbeats in --25 heartbeats
/-- **Regular languages are closed under concatenation.** -/
protected theorem IsRegular.mul {T : Type u} {L₁ L₂ : Language T}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) : (L₁ * L₂).IsRegular := by
  obtain ⟨σ₁, fσ₁, M₁, hM₁⟩ := h₁
  obtain ⟨σ₂, fσ₂, M₂, hM₂⟩ := h₂
  haveI := fσ₁
  haveI := fσ₂
  refine ⟨Set (σ₁ ⊕ σ₂), inferInstance, (concatεNFA M₁ M₂).toNFA.toDFA, ?_⟩
  rw [NFA.toDFA_correct, εNFA.toNFA_correct, concatεNFA_accepts, hM₁, hM₂]

end Language

#print axioms Language.IsRegular.mul
--[propext, sorryAx, Classical.choice, Quot.sound]
/-Application type mismatch: The argument
  rfl
has type
  ?m.403 = ?m.403
but is expected to have type
  True
in the application
  ⟨hr, rfl⟩
Unknown constant `Set.not_mem_empty`
Unknown constant `Set.not_mem_empty`
-/
