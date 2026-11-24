import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.Language

open Classical

universe u v

namespace DFA

variable {α : Type u} {σ₁ σ₂ : Type v}

def εconcat (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : εNFA α (σ₁ ⊕ σ₂) where
  step s a :=
    match s, a with
    | Sum.inl s₁, some c => {Sum.inl (M₁.step s₁ c)}
    | Sum.inl s₁, none   => if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅
    | Sum.inr s₂, some c => {Sum.inr (M₂.step s₂ c)}
    | Sum.inr _ , none   => ∅
  start := insert (Sum.inl M₁.start)
    (if M₁.start ∈ M₁.accept then ({Sum.inr M₂.start} : Set (σ₁ ⊕ σ₂)) else ∅)
  accept := Sum.inr '' M₂.accept

section
variable (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)

/-! ### Unfolding lemmas for the construction

The alphabet coercion `α → Option α` used by `εNFA.stepSet` is `some`, so stating the
`some`-transitions with an argument `c : α` (letting Lean insert the coercion) makes these
lemmas fire on the terms produced by `mem_stepSet_iff`. -/

@[simp] lemma εconcat_step_inl (s₁ : σ₁) (c : α) :
    (εconcat M₁ M₂).step (Sum.inl s₁) c = {Sum.inl (M₁.step s₁ c)} := rfl

@[simp] lemma εconcat_step_inr (s₂ : σ₂) (c : α) :
    (εconcat M₁ M₂).step (Sum.inr s₂) c = {Sum.inr (M₂.step s₂ c)} := rfl

@[simp] lemma εconcat_step_inl_none (s₁ : σ₁) :
    (εconcat M₁ M₂).step (Sum.inl s₁) none
      = (if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅) := rfl

@[simp] lemma εconcat_step_inr_none (s₂ : σ₂) :
    (εconcat M₁ M₂).step (Sum.inr s₂) none = ∅ := rfl

@[simp] lemma εconcat_start :
    (εconcat M₁ M₂).start
      = insert (Sum.inl M₁.start)
          (if M₁.start ∈ M₁.accept then ({Sum.inr M₂.start} : Set (σ₁ ⊕ σ₂)) else ∅) := rfl

@[simp] lemma εconcat_accept :
    (εconcat M₁ M₂).accept = Sum.inr '' M₂.accept := rfl

/-! ### ε-closures of singletons -/

/-- From a right-hand (`M₂`) state there are no ε-transitions, so the closure is trivial. -/
lemma εcl_inr (s₂ : σ₂) :
    (εconcat M₁ M₂).εClosure {Sum.inr s₂} = {Sum.inr s₂} := by
  apply Set.eq_of_subset_of_subset _ (εNFA.subset_εClosure _ _)
  rintro s hs
  induction hs with
  | base u hu => exact hu
  | step u t hut _ ih =>
    rw [Set.mem_singleton_iff] at ih
    subst ih
    simp only [εconcat_step_inr_none, Set.mem_empty_iff_false] at hut

/-- From a left-hand (`M₁`) state `s₁`, the only ε-move is a single jump to `Sum.inr M₂.start`,
available exactly when `s₁` is accepting. -/
lemma mem_εcl_inl (s₁ : σ₁) (p : σ₁ ⊕ σ₂) :
    p ∈ (εconcat M₁ M₂).εClosure {Sum.inl s₁} ↔
      p = Sum.inl s₁ ∨ (s₁ ∈ M₁.accept ∧ p = Sum.inr M₂.start) := by
  constructor
  · intro h
    induction h with
    | base u hu =>
      rw [Set.mem_singleton_iff] at hu
      exact Or.inl hu
    | step u t hut _ ih =>
      rcases ih with rfl | ⟨-, rfl⟩
      · rw [εconcat_step_inl_none] at hut
        split_ifs at hut with hacc
        · rw [Set.mem_singleton_iff] at hut
          exact Or.inr ⟨hacc, hut⟩
        · exact (Set.notMem_empty _ hut).elim
      · simp only [εconcat_step_inr_none, Set.mem_empty_iff_false] at hut
  · rintro (rfl | ⟨hacc, rfl⟩)
    · exact εNFA.subset_εClosure _ _ rfl
    · refine εNFA.εClosure.step (Sum.inl s₁) (Sum.inr M₂.start) ?_
        (εNFA.subset_εClosure _ _ rfl)
      rw [εconcat_step_inl_none, if_pos hacc]
      rfl

/-! ### Behaviour from a single start state -/

/-- Running the machine from a right state just simulates `M₂`. -/
lemma evalFrom_inr (s₂ : σ₂) (w : List α) :
    (εconcat M₁ M₂).evalFrom {Sum.inr s₂} w = {Sum.inr (M₂.evalFrom s₂ w)} := by
  induction w using List.reverseRecOn with
  | nil => simp [εcl_inr]
  | append_singleton w c ih =>
    rw [εNFA.evalFrom_append_singleton, ih]
    ext p
    simp only [εNFA.mem_stepSet_iff, Set.mem_singleton_iff, exists_eq_left,
      εconcat_step_inr, εcl_inr, DFA.evalFrom_append_singleton]

/-- Running the machine from a left state `Sum.inl s₁`: the reachable states are the current
`M₁`-state `Sum.inl (M₁.evalFrom s₁ w)`, together with, for every way to split `w = x ++ y` at a
point where `M₁` is accepting, the `M₂`-state `Sum.inr (M₂.evalFrom M₂.start y)`. -/
lemma mem_evalFrom_inl (s₁ : σ₁) (w : List α) (p : σ₁ ⊕ σ₂) :
    p ∈ (εconcat M₁ M₂).evalFrom {Sum.inl s₁} w ↔
      p = Sum.inl (M₁.evalFrom s₁ w) ∨
      ∃ x y, x ++ y = w ∧ M₁.evalFrom s₁ x ∈ M₁.accept
        ∧ p = Sum.inr (M₂.evalFrom M₂.start y) := by
  induction w using List.reverseRecOn generalizing p with
  | nil =>
    rw [εNFA.evalFrom_nil, mem_εcl_inl]
    simp only [DFA.evalFrom_nil]
    constructor
    · rintro (rfl | ⟨hacc, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨[], [], rfl, hacc, rfl⟩
    · rintro (rfl | ⟨x, y, hxy, hacc, rfl⟩)
      · exact Or.inl rfl
      · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hxy
        exact Or.inr ⟨hacc, rfl⟩
  | append_singleton w c ih =>
    rw [εNFA.evalFrom_append_singleton]
    rw [εNFA.mem_stepSet_iff]
    -- rewrite the membership in the previous eval-set using the induction hypothesis
    have hmem : ∀ q, q ∈ (εconcat M₁ M₂).evalFrom {Sum.inl s₁} w ↔
        q = Sum.inl (M₁.evalFrom s₁ w) ∨
        ∃ x y, x ++ y = w ∧ M₁.evalFrom s₁ x ∈ M₁.accept
          ∧ q = Sum.inr (M₂.evalFrom M₂.start y) := ih
    constructor
    · rintro ⟨q, hq, hpq⟩
      rw [hmem] at hq
      rcases hq with rfl | ⟨x, y, hxy, hacc, rfl⟩
      · -- came from the left `M₁`-state; step of `M₁`, then possible ε-jump
        rw [εconcat_step_inl, mem_εcl_inl] at hpq
        rcases hpq with rfl | ⟨hacc, rfl⟩
        · left
          rw [DFA.evalFrom_append_singleton]
        · right
          refine ⟨w ++ [c], [], by simp, ?_, rfl⟩
          rwa [DFA.evalFrom_append_singleton] at hacc
      · -- came from a right `M₂`-state; pure `M₂` step, no new ε-jump
        rw [εconcat_step_inr, εcl_inr, Set.mem_singleton_iff] at hpq
        right
        refine ⟨x, y ++ [c], by rw [← List.append_assoc, hxy], hacc, ?_⟩
        rw [hpq, DFA.evalFrom_append_singleton]
    · rintro (rfl | ⟨x, y, hxy, hacc, rfl⟩)
      · -- the current `M₁`-state, reached by stepping the previous `M₁`-state
        refine ⟨Sum.inl (M₁.evalFrom s₁ w), ?_, ?_⟩
        · rw [hmem]; exact Or.inl rfl
        · rw [εconcat_step_inl, mem_εcl_inl]
          left
          rw [DFA.evalFrom_append_singleton]
      · -- a right `M₂`-state from a split `x ++ y = w ++ [c]`
        obtain ⟨rfl, rfl⟩ | ⟨y', rfl, hxy'⟩ := split_last x y w c hxy
        · -- split at the very end: `y = []`, so this is a fresh ε-jump after the last step
          refine ⟨Sum.inl (M₁.evalFrom s₁ w), ?_, ?_⟩
          · rw [hmem]; exact Or.inl rfl
          · rw [εconcat_step_inl, mem_εcl_inl]
            right
            refine ⟨?_, ?_⟩
            · rwa [DFA.evalFrom_append_singleton] at hacc
            · rfl
        · -- split earlier: the `M₂`-state existed before and just took one more step
          refine ⟨Sum.inr (M₂.evalFrom M₂.start y'), ?_, ?_⟩
          · rw [hmem]
            exact Or.inr ⟨x, y', hxy', hacc, rfl⟩
          · rw [εconcat_step_inr, εcl_inr, Set.mem_singleton_iff,
              DFA.evalFrom_append_singleton]

end

/-- Splitting `x ++ y = w ++ [c]`: either `y` is empty (and `x` is the whole thing) or `y` ends in
`c` and the prefixes match up. -/
theorem split_last {α : Type u} (x w : List α) (c : α) :
    ∀ y, x ++ y = w ++ [c] →
      (y = [] ∧ x = w ++ [c]) ∨ (∃ y', y = y' ++ [c] ∧ x ++ y' = w) := by
  intro y
  induction y using List.reverseRecOn with
  | nil =>
    intro h
    simp only [List.append_nil] at h
    exact Or.inl ⟨rfl, h⟩
  | append_singleton y d _ =>
    intro h
    rw [← List.append_assoc] at h
    obtain ⟨hxy, hd⟩ := List.append_inj' h rfl
    have hdc : d = c := by simpa using hd
    subst hdc
    exact Or.inr ⟨y, rfl, hxy⟩

/-! ### Main theorem -/

theorem accepts (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (εconcat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext w
  rw [Language.mem_mul]
  constructor
  · -- accepted word ⇒ it splits as `M₁`-word ++ `M₂`-word
    rintro ⟨S, hSacc, hSeval⟩
    rw [εconcat_accept] at hSacc
    obtain ⟨s₂, hs₂acc, rfl⟩ := hSacc
    -- `hSeval : Sum.inr s₂ ∈ (εconcat M₁ M₂).eval w`
    rw [εNFA.eval, εNFA.mem_evalFrom_iff_exists] at hSeval
    obtain ⟨t, ht, hteval⟩ := hSeval
    rw [εconcat_start, Set.mem_insert_iff] at ht
    rcases ht with rfl | ht
    · -- start in `Sum.inl M₁.start`
      rw [mem_evalFrom_inl] at hteval
      rcases hteval with h | ⟨x, y, hxy, hacc, hinr⟩
      · exact absurd h (by simp)
      · rw [Sum.inr.injEq] at hinr
        subst hinr
        exact ⟨x, hacc, y, hs₂acc, hxy⟩
    · -- start in `Sum.inr M₂.start` (only when `M₁.start` is accepting)
      split_ifs at ht with hstart
      · rw [Set.mem_singleton_iff] at ht
        subst ht
        rw [evalFrom_inr, Set.mem_singleton_iff, Sum.inr.injEq] at hteval
        subst hteval
        exact ⟨[], hstart, w, hs₂acc, by simp⟩
      · exact absurd ht (Set.notMem_empty _)
  · -- a valid split ⇒ the word is accepted
    rintro ⟨x, hxacc, y, hyacc, rfl⟩
    refine ⟨Sum.inr (M₂.evalFrom M₂.start y), ?_, ?_⟩
    · rw [εconcat_accept]
      exact ⟨_, hyacc, rfl⟩
    · rw [εNFA.eval, εNFA.mem_evalFrom_iff_exists]
      refine ⟨Sum.inl M₁.start, ?_, ?_⟩
      · rw [εconcat_start]
        exact Set.mem_insert _ _
      · rw [mem_evalFrom_inl]
        exact Or.inr ⟨x, y, rfl, hxacc, rfl⟩

end DFA

#print axioms DFA.accepts
--[propext, sorryAx, choice, Quot.sound]
