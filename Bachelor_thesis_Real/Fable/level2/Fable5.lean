/-
Closure of regular languages under concatenation, via an explicit ε-NFA.

Given DFAs `M₁ : DFA α σ₁` and `M₂ : DFA α σ₂`, the `εNFA α (σ₁ ⊕ σ₂)` below
simulates `M₁` on the `Sum.inl` states and, whenever `M₁` sits in an accepting
state, may ε-jump to the start state of `M₂`, which it then simulates on the
`Sum.inr` states.

Main results:
* `εconcat_εClosure`  : closed form for the ε-closure of this machine.
* `εconcat_mem_eval`  : the run invariant.  After reading `x` the machine is in
    - the state `Sum.inl (M₁.eval x)` tracking `M₁`'s (deterministic) run, and
    - the state `Sum.inr (M₂.eval z)` for every split `x = y ++ z` whose
      prefix `y` is accepted by `M₁`.
* `εconcat_accepts`   : `(εconcat M₁ M₂).accepts = M₁.accepts * M₂.accepts`.
* `isRegular_concat`  : regular languages are closed under concatenation
                        (determinise `εconcat` with the subset construction).
-/
import Mathlib.Computability.EpsilonNFA
import Mathlib.Data.Fintype.Powerset

set_option profiler true
open Classical

universe u v w

variable {α : Type u} {σ₁ : Type v} {σ₂ : Type w}
variable (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
#count_heartbeats in --134
/-- The ε-NFA that simulates `M₁` and then `M₂`: run `M₁` on the `inl` states,
and whenever `M₁` is in an accepting state allow an ε-move to `M₂.start`. -/

def εconcat : εNFA α (σ₁ ⊕ σ₂) where
  step
    | Sum.inl s₁, some c => {Sum.inl (M₁.step s₁ c)}
    | Sum.inl s₁, none => if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅
    | Sum.inr s₂, some c => {Sum.inr (M₂.step s₂ c)}
    | Sum.inr _, none => ∅
  start := {x | x = Sum.inl M₁.start ∨ (x = Sum.inr M₂.start ∧ M₁.start ∈ M₁.accept)}
  accept := Sum.inr '' M₂.accept

/-! ### Unfolding lemmas for the transition structure -/
#count_heartbeats in --27
theorem εconcat_step_inl_some (s : σ₁) (c : α) :
    (εconcat M₁ M₂).step (Sum.inl s) (some c) = {Sum.inl (M₁.step s c)} := rfl
#count_heartbeats in --27
theorem εconcat_step_inr_some (s : σ₂) (c : α) :
    (εconcat M₁ M₂).step (Sum.inr s) (some c) = {Sum.inr (M₂.step s c)} := rfl
#count_heartbeats in --46
theorem εconcat_step_inl_none (s : σ₁) :
    (εconcat M₁ M₂).step (Sum.inl s) none =
      if s ∈ M₁.accept then {Sum.inr M₂.start} else ∅ := rfl
#count_heartbeats in --22
theorem εconcat_step_inr_none (s : σ₂) :
    (εconcat M₁ M₂).step (Sum.inr s) none = ∅ := rfl
#count_heartbeats in --32
theorem εconcat_start_def :
    (εconcat M₁ M₂).start =
      {x | x = Sum.inl M₁.start ∨ (x = Sum.inr M₂.start ∧ M₁.start ∈ M₁.accept)} := rfl
#count_heartbeats in --19
theorem εconcat_accept_def :
    (εconcat M₁ M₂).accept = Sum.inr '' M₂.accept := rfl
#count_heartbeats in --32
/-- The only ε-moves are `inl s ⟶ inr M₂.start` for accepting `s`. -/
theorem εconcat_mem_step_inl_none {s : σ₁} {p : σ₁ ⊕ σ₂} :
    p ∈ (εconcat M₁ M₂).step (Sum.inl s) none ↔
      p = Sum.inr M₂.start ∧ s ∈ M₁.accept := by
  rw [εconcat_step_inl_none]
  split_ifs with h <;> simp [h]
#count_heartbeats in --44
/-! ### The ε-closure of `εconcat` -/

/-- Closed form for the ε-closure: a set of states is enlarged by `inr M₂.start`
exactly when it contains some accepting `inl` state. -/

theorem εconcat_εClosure (S : Set (σ₁ ⊕ σ₂)) :
    (εconcat M₁ M₂).εClosure S =
      S ∪ {p | p = Sum.inr M₂.start ∧ ∃ s ∈ M₁.accept, Sum.inl s ∈ S} := by
  apply Set.Subset.antisymm
  · intro p hp
    induction hp with
    | base s hs => exact Or.inl hs
    | step s t ht _ ih =>
      cases s with
      | inl s₁ =>
        rw [εconcat_mem_step_inl_none] at ht
        obtain ⟨rfl, h⟩ := ht
        rcases ih with hS | ⟨h', -⟩
        · exact Or.inr ⟨rfl, s₁, h, hS⟩
        · exact absurd h' (by simp)
      | inr s₂ =>
        rw [εconcat_step_inr_none] at ht
        simp at ht
  · rintro p (hp | ⟨rfl, s, hs, hS⟩)
    · exact εNFA.εClosure.base p hp
    · exact εNFA.εClosure.step (Sum.inl s) _
        ((εconcat_mem_step_inl_none M₁ M₂).mpr ⟨rfl, hs⟩)
        (εNFA.εClosure.base _ hS)
#count_heartbeats in --46
theorem εconcat_εClosure_inl (s : σ₁) :
    (εconcat M₁ M₂).εClosure {Sum.inl s} =
      {Sum.inl s} ∪ {p | p = Sum.inr M₂.start ∧ s ∈ M₁.accept} := by
  rw [εconcat_εClosure]
  ext p
  simp
#count_heartbeats in --25
theorem εconcat_εClosure_inr (s : σ₂) :
    (εconcat M₁ M₂).εClosure {Sum.inr s} = {Sum.inr s} := by
  rw [εconcat_εClosure]
  ext p
  simp
#count_heartbeats in --47
/-! ### Two small generic helpers -/

/-- Membership form of `εNFA.stepSet`. -/

theorem mem_stepSet' {σ : Type*} {M : εNFA α σ} {S : Set σ} {a : α} {p : σ} :
    p ∈ M.stepSet S a ↔ ∃ t ∈ S, p ∈ M.εClosure (M.step t a) := by
  simp [εNFA.stepSet]
#count_heartbeats in --34
/-- Every list is `[]` or ends in a single letter. -/

theorem eq_nil_or_append_singleton (z : List α) :
    z = [] ∨ ∃ z' b, z = z' ++ [b] := by
  induction z using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton z' b _ => exact Or.inr ⟨z', b, rfl⟩

/-! ### The run invariant -/
#count_heartbeats in --55
/-- **Key invariant.** After reading `x`, the εNFA occupies exactly
* `Sum.inl (M₁.eval x)` (the deterministic run of `M₁` on `x`), and
* `Sum.inr (M₂.eval z)` for each decomposition `x = y ++ z` with
  `M₁.eval y ∈ M₁.accept` (the run of `M₂` started after an accepted prefix). -/
theorem εconcat_mem_eval (x : List α) (p : σ₁ ⊕ σ₂) :
    p ∈ (εconcat M₁ M₂).eval x ↔
      p = Sum.inl (M₁.eval x) ∨
        ∃ y z, y ++ z = x ∧ M₁.eval y ∈ M₁.accept ∧ p = Sum.inr (M₂.eval z) := by
  induction x using List.reverseRecOn generalizing p with
  | nil =>
    rw [εNFA.eval_nil, εconcat_εClosure]
    simp only [εconcat_start_def, Set.mem_union, Set.mem_setOf_eq, DFA.eval_nil]
    constructor
    · rintro ((rfl | ⟨rfl, h⟩) | ⟨rfl, s, hs, (h | ⟨h, -⟩)⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨[], [], rfl, by simpa using h, by simp⟩
      · obtain rfl := Sum.inl.inj h
        exact Or.inr ⟨[], [], rfl, by simpa using hs, by simp⟩
      · exact absurd h (by simp)
    · rintro (rfl | ⟨y, z, hyz, hy, rfl⟩)
      · exact Or.inl (Or.inl rfl)
      · obtain ⟨rfl, rfl⟩ : y = [] ∧ z = [] := by simpa using hyz
        exact Or.inl (Or.inr ⟨by simp, by simpa using hy⟩)
  | append_singleton x a ih =>
    rw [εNFA.eval_append_singleton, mem_stepSet']
    constructor
    · rintro ⟨t, ht, hpt⟩
      rcases (ih t).mp ht with rfl | ⟨y, z, rfl, hy, rfl⟩
      · -- `t` was the state tracking `M₁`'s run on `x`
        rw [εconcat_step_inl_some, εconcat_εClosure_inl] at hpt
        rcases hpt with hp | ⟨rfl, hacc⟩
        · rw [Set.mem_singleton_iff] at hp
          subst hp
          exact Or.inl (by rw [DFA.eval_append_singleton])
        · -- ε-jump just after reading `a`: this is the split `x ++ [a] = (x ++ [a]) ++ []`
          refine Or.inr ⟨x ++ [a], [], List.append_nil _, ?_, by simp⟩
          rwa [DFA.eval_append_singleton]
      · -- `t` was an `M₂`-state arising from the split `x = y ++ z`
        rw [εconcat_step_inr_some, εconcat_εClosure_inr, Set.mem_singleton_iff] at hpt
        subst hpt
        exact Or.inr ⟨y, z ++ [a], (List.append_assoc y z [a]).symm, hy,
          by rw [DFA.eval_append_singleton]⟩
    · rintro (rfl | ⟨y, z, hyz, hy, rfl⟩)
      · -- the `M₁`-tracking state advances deterministically
        refine ⟨Sum.inl (M₁.eval x), (ih _).mpr (Or.inl rfl), ?_⟩
        rw [εconcat_step_inl_some]
        apply εNFA.subset_εClosure
        rw [Set.mem_singleton_iff, DFA.eval_append_singleton]
      · rcases eq_nil_or_append_singleton z with rfl | ⟨z', b, rfl⟩
        · -- split with `z = []`: the whole word `x ++ [a]` was accepted by `M₁`,
          -- so take the ε-move right after the last letter
          rw [List.append_nil] at hyz
          subst hyz
          refine ⟨Sum.inl (M₁.eval x), (ih _).mpr (Or.inl rfl), ?_⟩
          rw [εconcat_step_inl_some, εconcat_εClosure_inl]
          exact Or.inr ⟨by simp, by rwa [DFA.eval_append_singleton] at hy⟩
        · -- split with `z = z' ++ [b]`: the last letter was read inside `M₂`
          rw [← List.append_assoc] at hyz
          obtain ⟨rfl, hb⟩ := List.append_inj' hyz rfl
          obtain rfl : b = a := by simpa using hb
          refine ⟨Sum.inr (M₂.eval z'), (ih _).mpr (Or.inr ⟨y, z', rfl, hy, rfl⟩), ?_⟩
          rw [εconcat_step_inr_some, εconcat_εClosure_inr, Set.mem_singleton_iff,
            DFA.eval_append_singleton]

/-! ### The main theorem -/
#count_heartbeats in --22
/-- The εNFA recognises exactly the concatenation `M₁.accepts * M₂.accepts`. -/

theorem εconcat_accepts : (εconcat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨p, hp, hx⟩
    rw [εconcat_accept_def, Set.mem_image] at hp
    obtain ⟨s, hs, rfl⟩ := hp
    rcases (εconcat_mem_eval M₁ M₂ x (Sum.inr s)).mp hx with h | ⟨y, z, hyz, hy, h⟩
    · exact absurd h (by simp)
    · obtain rfl : s = M₂.eval z := by simpa using h
      exact ⟨y, hy, z, hs, hyz⟩
  · rintro ⟨y, hy, z, hz, rfl⟩
    refine ⟨Sum.inr (M₂.eval z), ?_, ?_⟩
    · rw [εconcat_accept_def]
      exact Set.mem_image_of_mem _ hz
    · exact (εconcat_mem_eval M₁ M₂ (y ++ z) _).mpr (Or.inr ⟨y, z, rfl, hy, rfl⟩)
#count_heartbeats in --20
/-- **Regular languages are closed under concatenation.**
Determinise `εconcat` via `εNFA.toNFA` and the subset construction `NFA.toDFA`. -/

theorem isRegular_concat {L₁ L₂ : Language α} (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (L₁ * L₂).IsRegular := by
  obtain ⟨τ₁, i₁, N₁, rfl⟩ := h₁
  obtain ⟨τ₂, i₂, N₂, rfl⟩ := h₂
  haveI := i₁
  haveI := i₂
  refine ⟨Set (τ₁ ⊕ τ₂), inferInstance, (εconcat N₁ N₂).toNFA.toDFA, ?_⟩
  rw [NFA.toDFA_correct, εNFA.toNFA_correct, εconcat_accepts]




#print axioms isRegular_concat
--[propext, choice, Quot.sound]
--none
