import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.Language

open Classical

universe u v

namespace DFA

variable {α : Type u} {σ₁ σ₂ : Type v}
#count_heartbeats in --141
def εconcat (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : εNFA α (σ₁ ⊕ σ₂) where
  step s a :=
    match s, a with
    | Sum.inl s₁, some c => {Sum.inl (M₁.step s₁ c)}
    | Sum.inl s₁, none   => if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅
    | Sum.inr s₂, some c => {Sum.inr (M₂.step s₂ c)}
    | Sum.inr _ , none   => ∅
  start :=
    insert (Sum.inl M₁.start)
      (if M₁.start ∈ M₁.accept then ({Sum.inr M₂.start} : Set (σ₁ ⊕ σ₂)) else ∅)
  accept := Sum.inr '' M₂.accept

variable (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
#count_heartbeats in --38
-- Helper for characterizing exactly what the ε-transitions are
lemma step_none_iff (a b : σ₁ ⊕ σ₂) :
    b ∈ (εconcat M₁ M₂).step a none ↔
    ∃ s₁, a = Sum.inl s₁ ∧ s₁ ∈ M₁.accept ∧ b = Sum.inr M₂.start := by
  cases a with
  | inl s₁ =>
    dsimp [εconcat]
    split_ifs with h
    · simp [h]
    · simp [h]
  | inr s₂ =>
    dsimp [εconcat]
    simp
#count_heartbeats in --45
-- The ε-closure in our specific construction can only take at most one step.
lemma εClosure_iff (S : Set (σ₁ ⊕ σ₂)) (b : σ₁ ⊕ σ₂) :
    b ∈ (εconcat M₁ M₂).εClosure S ↔
    b ∈ S ∨ (b = Sum.inr M₂.start ∧ ∃ s₁, Sum.inl s₁ ∈ S ∧ s₁ ∈ M₁.accept) := by
  dsimp [εNFA.εClosure]
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, hab⟩
    induction hab with
    | refl => exact Or.inl ha
    | tail c d _ hcd ih =>
      have hcd' := (step_none_iff M₁ M₂ c d).mp hcd
      rcases hcd' with ⟨s₁, rfl, hs₁, rfl⟩
      cases ih with
      | inl hc => right; exact ⟨rfl, s₁, hc, hs₁⟩
      | inr hc => rcases hc with ⟨-, hc_s₁, -⟩; contradiction
  · rintro (hb | ⟨rfl, s₁, hs₁S, hs₁A⟩)
    · exact ⟨b, hb, Relation.ReflTransGen.refl⟩
    · refine ⟨Sum.inl s₁, hs₁S, Relation.ReflTransGen.tail Relation.ReflTransGen.refl ?_⟩
      exact (step_none_iff M₁ M₂ _ _).mpr ⟨s₁, rfl, hs₁A, rfl⟩
#count_heartbeats in --71
-- Characterization of a single step set over `c`
lemma stepSet_iff (S : Set (σ₁ ⊕ σ₂)) (c : α) (b : σ₁ ⊕ σ₂) :
    b ∈ (εconcat M₁ M₂).stepSet S c ↔
    (∃ s₁, Sum.inl s₁ ∈ S ∧ b = Sum.inl (M₁.step s₁ c)) ∨
    (∃ s₂, Sum.inr s₂ ∈ S ∧ b = Sum.inr (M₂.step s₂ c)) ∨
    (b = Sum.inr M₂.start ∧ ∃ s₁, Sum.inl s₁ ∈ S ∧ M₁.step s₁ c ∈ M₁.accept) := by
  dsimp [εNFA.stepSet]
  rw [εClosure_iff]
  have H : ∀ y, y ∈ (⋃ x ∈ S, (εconcat M₁ M₂).step x (some c)) ↔
      (∃ s₁, Sum.inl s₁ ∈ S ∧ y = Sum.inl (M₁.step s₁ c)) ∨
      (∃ s₂, Sum.inr s₂ ∈ S ∧ y = Sum.inr (M₂.step s₂ c)) := by
    intro y
    simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, hy⟩
      cases x with
      | inl s₁ => left; exact ⟨s₁, hx, hy⟩
      | inr s₂ => right; exact ⟨s₂, hx, hy⟩
    · rintro (⟨s₁, hs₁, rfl⟩ | ⟨s₂, hs₂, rfl⟩)
      · exact ⟨Sum.inl s₁, hs₁, rfl⟩
      · exact ⟨Sum.inr s₂, hs₂, rfl⟩
  have H2 : (∃ s', Sum.inl s' ∈ (⋃ x ∈ S, (εconcat M₁ M₂).step x (some c)) ∧ s' ∈ M₁.accept) ↔
            (∃ s₁, Sum.inl s₁ ∈ S ∧ M₁.step s₁ c ∈ M₁.accept) := by
    constructor
    · rintro ⟨s', hs', hacc⟩
      rw [H] at hs'
      rcases hs' with ⟨s₁, hs₁, eq⟩ | ⟨s₂, hs₂, eq⟩
      · cases eq; exact ⟨s₁, hs₁, hacc⟩
      · contradiction
    · rintro ⟨s₁, hs₁, hacc⟩
      refine ⟨M₁.step s₁ c, ?_, hacc⟩
      rw [H]; left; exact ⟨s₁, hs₁, rfl⟩
  rw [H b, H2]
  tauto
#count_heartbeats in --47
-- Our structurally invariant subset of active states
def myState (s₁ : σ₁) (S₂ : Set σ₂) : Set (σ₁ ⊕ σ₂) :=
  insert (Sum.inl s₁) (Sum.inr '' (S₂ ∪ if s₁ ∈ M₁.accept then {M₂.start} else ∅))
#count_heartbeats in --140
-- How our structurally invariant state steps on a character `c`
lemma stepSet_myState (s₁ : σ₁) (S₂ : Set σ₂) (c : α) :
    (εconcat M₁ M₂).stepSet (myState M₁ M₂ s₁ S₂) c =
    myState M₁ M₂ (M₁.step s₁ c) (M₂.step '' (S₂ ∪ if s₁ ∈ M₁.accept then {M₂.start} else ∅)) := by
  ext b
  rw [stepSet_iff]
  dsimp [myState]
  simp only [Set.mem_insert_iff, Set.mem_image, Set.mem_union]
  constructor
  · rintro (⟨s₁', h1, rfl⟩ | ⟨s₂', h2, rfl⟩ | ⟨rfl, s₁', h1, hacc⟩)
    · rcases h1 with (hk | ⟨x, hx, hk⟩)
      · cases hk; left; rfl
      · contradiction
    · rcases h2 with (hk | ⟨x, hx, hk⟩)
      · contradiction
      · cases hk; right; exact ⟨x, Or.inl hx, rfl⟩
    · rcases h1 with (hk | ⟨x, hx, hk⟩)
      · cases hk; right; exact ⟨M₂.start, Or.inr (by split_ifs; rfl; contradiction), rfl⟩
      · contradiction
  · rintro (rfl | ⟨x, hx, rfl⟩)
    · left; exact ⟨s₁, Or.inl rfl, rfl⟩
    · rcases hx with (hx | hx)
      · right; left; exact ⟨x, Or.inr ⟨x, hx, rfl⟩, rfl⟩
      · split_ifs at hx with hacc
        · rcases hx
          right; right; exact ⟨rfl, s₁, Or.inl rfl, hacc⟩
        · exact False.elim (Set.not_mem_empty _ hx)
#count_heartbeats in --69
-- A generated subset of states tracked in M₂ from reading prefix splits
def S_M2_gen (s₁ : σ₁) (S₂ : Set σ₂) (w : List α) : Set σ₂ :=
  { s₂ | ∃ (u v : List α), u ++ v = w ∧ v ≠ [] ∧ List.foldl M₁.step s₁ u ∈ M₁.accept ∧ s₂ = List.foldl M₂.step M₂.start v } ∪
  { s₂ | ∃ s₂' ∈ S₂, s₂ = List.foldl M₂.step s₂' w }
#count_heartbeats in --141
lemma S_M2_gen_cons (s₁ : σ₁) (S₂ : Set σ₂) (a : α) (w : List α) :
    S_M2_gen M₁ M₂ (M₁.step s₁ a) (M₂.step '' (S₂ ∪ if s₁ ∈ M₁.accept then {M₂.start} else ∅)) w =
    S_M2_gen M₁ M₂ s₁ S₂ (a :: w) := by
  ext s₂
  simp only [S_M2_gen, Set.mem_union, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro (⟨u, v, huv, hv, hu, rfl⟩ | ⟨s₂', hs₂', rfl⟩)
    · left
      refine ⟨a :: u, v, ?_, hv, hu, rfl⟩
      rw [← huv, List.cons_append]
    · rcases hs₂' with ⟨s₂'', hs₂'', rfl⟩
      rcases hs₂'' with (h_in | h_in)
      · right; exact ⟨s₂'', h_in, rfl⟩
      · split_ifs at h_in with h_acc
        · left
          refine ⟨[], a :: w, rfl, by simp, h_acc, ?_⟩
          rcases h_in; rfl
        · exact False.elim (Set.not_mem_empty _ h_in)
  · rintro (⟨u, v, huv, hv, hu, rfl⟩ | ⟨s₂', hs₂', rfl⟩)
    · cases u with
      | nil =>
        right
        simp only [List.nil_append] at huv
        subst huv
        refine ⟨M₂.step M₂.start a, ?_, rfl⟩
        exact ⟨M₂.start, Or.inr (by split_ifs; exact rfl; contradiction), rfl⟩
      | cons a' u' =>
        cases huv
        left
        refine ⟨u', v, rfl, hv, hu, rfl⟩
    · right
      refine ⟨M₂.step s₂' a, ?_, rfl⟩
      exact ⟨s₂', Or.inl hs₂', rfl⟩
#count_heartbeats in --27
-- Generalizing to entire string traversal with foldl
lemma foldl_stepSet_myState (s₁ : σ₁) (S₂ : Set σ₂) (w : List α) :
    List.foldl (εconcat M₁ M₂).stepSet (myState M₁ M₂ s₁ S₂) w =
    myState M₁ M₂ (List.foldl M₁.step s₁ w) (S_M2_gen M₁ M₂ s₁ S₂ w) := by
  induction w generalizing s₁ S₂ with
  | nil =>
    dsimp [S_M2_gen]
    have h_eq : (S_M2_gen M₁ M₂ s₁ S₂ []) = S₂ := by
      ext x
      simp only [Set.mem_union, Set.mem_setOf_eq, List.append_eq_nil_iff]
      constructor
      · rintro (⟨u, v, ⟨rfl, rfl⟩, hv, -⟩ | ⟨s₂', hs₂', rfl⟩)
        · exact False.elim (hv rfl)
        · exact hs₂'
      · intro h
        right; exact ⟨x, h, rfl⟩
    rw [h_eq]
    rfl
  | cons a w ih =>
    rw [List.foldl_cons, stepSet_myState, ih]
    congr 2
    exact S_M2_gen_cons M₁ M₂ s₁ S₂ a w
#count_heartbeats in --29
-- Core execution evaluation characterization mapping
lemma evalFrom_eq (w : List α) :
    (εconcat M₁ M₂).evalFrom (εconcat M₁ M₂).start w =
    myState M₁ M₂ (List.foldl M₁.step M₁.start w) (S_M2_gen M₁ M₂ M₁.start ∅ w) := by
  dsimp [εNFA.evalFrom]
  have h_start : (εconcat M₁ M₂).start = myState M₁ M₂ M₁.start ∅ := by
    ext x
    simp only [myState, Set.mem_insert_iff, Set.mem_union, Set.mem_empty_iff_false, Set.mem_image, false_or]
    rfl
  have h_clos : (εconcat M₁ M₂).εClosure (εconcat M₁ M₂).start = (εconcat M₁ M₂).start := by
    ext x
    rw [εClosure_iff]
    constructor
    · rintro (hx | ⟨rfl, s₁, hs₁, hacc⟩)
      · exact hx
      · rw [h_start] at hs₁
        rcases hs₁ with (hk | ⟨y, hy, hk⟩)
        · cases hk
          rw [h_start]
          right
          split_ifs
          · exact ⟨M₂.start, rfl, rfl⟩
          · contradiction
        · contradiction
    · exact Or.inl
  rw [h_clos, h_start]
  exact foldl_stepSet_myState M₁ M₂ M₁.start ∅ w
#count_heartbeats in --49
-- Showing membership alignment from evaluation behavior
lemma mem_accepts_iff (w : List α) :
    w ∈ (εconcat M₁ M₂).accepts ↔
    ∃ u v, u ++ v = w ∧ List.foldl M₁.step M₁.start u ∈ M₁.accept ∧ List.foldl M₂.step M₂.start v ∈ M₂.accept := by
  rw [εNFA.accepts, Set.mem_setOf_eq, evalFrom_eq]
  simp only [Set.Nonempty, Set.mem_inter_iff]
  constructor
  · rintro ⟨x, hx, hx_acc⟩
    rcases hx_acc with ⟨s₂_acc, hs₂_acc, rfl⟩
    rcases hx with (hk | ⟨s₂, hs₂, hk⟩)
    · contradiction
    · cases hk
      rcases hs₂ with (hs₂ | hs₂)
      · rcases hs₂ with (⟨u, v, huv, hv, hu, rfl⟩ | ⟨s₂', hs₂', rfl⟩)
        · exact ⟨u, v, huv, hu, hs₂_acc⟩
        · exact False.elim (Set.not_mem_empty _ hs₂')
      · split_ifs at hs₂ with hacc
        · rcases hs₂
          exact ⟨w, [], by simp, hacc, hs₂_acc⟩
        · exact False.elim (Set.not_mem_empty _ hs₂)
  · rintro ⟨u, v, huv, hu, hv⟩
    refine ⟨Sum.inr (List.foldl M₂.step M₂.start v), ?_, ⟨_, hv, rfl⟩⟩
    right
    refine ⟨List.foldl M₂.step M₂.start v, ?_, rfl⟩
    cases v with
    | nil =>
      simp only [List.append_nil] at huv
      subst huv
      right
      split_ifs
      · rfl
      · contradiction
    | cons a v' =>
      left; left
      refine ⟨u, a :: v', huv, by simp, hu, rfl⟩
#count_heartbeats in --24 heartbeats
theorem accepts (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (εconcat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext w
  rw [mem_accepts_iff, Language.mem_mul]
  dsimp [DFA.accepts, DFA.eval, DFA.evalFrom]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    exact ⟨u, v, hu, hv, huv⟩
  · rintro ⟨u, v, hu, hv, huv⟩
    exact ⟨u, v, huv, hu, hv⟩

end DFA

#print axioms DFA.accepts
--'DFA.accepts' depends on axioms: [propext, sorryAx, choice, Quot.sound]
