/-
  Concatenation of two DFAs via an ε-NFA.

  We are given the construction `DFA.εconcat M₁ M₂` (an `εNFA` over `σ₁ ⊕ σ₂`)
  and must prove that the language it accepts is exactly `M₁.accepts * M₂.accepts`.

  The construction below is UNCHANGED from the problem statement.

  ------------------------------------------------------------------------------
  A note on placement of the final theorem.

  `DFA.accepts` already exists in Mathlib (it is the definition of the language
  accepted by a DFA). Declaring a *new* `theorem accepts` inside `namespace DFA`
  therefore collides with that name ("`DFA.accepts` has already been declared").
  For this reason the final theorem is stated at the top level (with `open DFA`),
  where the name `accepts` is free. Its statement is otherwise verbatim.
  ------------------------------------------------------------------------------

  Proof outline.

  The whole argument rests on a single semantic description of the reachable set
  after reading a word `x` (`eval_eq`): a state is reachable iff it is
  `inl (M₁.eval x)` (we are still simulating `M₁`), or it is `inr (M₂.eval y)`
  for some split `x = u ++ y` with `M₁.eval u` accepting (we ε-jumped into `M₂`
  after `M₁` accepted the prefix `u`).

  This in turn rests on a description of the ε-closure for this particular NFA
  (`εclosure_char`): the only ε-transitions go `inl s₁ → inr M₂.start`, and only
  when `s₁ ∈ M₁.accept`; so the closure can add at most `inr M₂.start`.
-/

import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.Language

open Classical

universe u v

namespace DFA

variable {α : Type u} {σ₁ σ₂ : Type v}
#count_heartbeats in --141
/-- The ε-NFA computing the concatenation of `M₁` and `M₂`.  (Verbatim.) -/
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

/-! ### Projection lemmas for the construction (all definitional). -/
#count_heartbeats in --28
@[simp] theorem εconcat_step_inl_some (s₁ : σ₁) (a : α) :
    (εconcat M₁ M₂).step (Sum.inl s₁) (some a) = {Sum.inl (M₁.step s₁ a)} := rfl
#count_heartbeats in --46
@[simp] theorem εconcat_step_inl_none (s₁ : σ₁) :
    (εconcat M₁ M₂).step (Sum.inl s₁) none
      = if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅ := rfl
#count_heartbeats in --28
@[simp] theorem εconcat_step_inr_some (s₂ : σ₂) (a : α) :
    (εconcat M₁ M₂).step (Sum.inr s₂) (some a) = {Sum.inr (M₂.step s₂ a)} := rfl
#count_heartbeats in --24
@[simp] theorem εconcat_step_inr_none (s₂ : σ₂) :
    (εconcat M₁ M₂).step (Sum.inr s₂) none = (∅ : Set (σ₁ ⊕ σ₂)) := rfl
#count_heartbeats in --44
@[simp] theorem εconcat_start_eq :
    (εconcat M₁ M₂).start
      = insert (Sum.inl M₁.start)
          (if M₁.start ∈ M₁.accept then ({Sum.inr M₂.start} : Set (σ₁ ⊕ σ₂)) else ∅) := rfl
#count_heartbeats in --20
@[simp] theorem εconcat_accept_eq :
    (εconcat M₁ M₂).accept = Sum.inr '' M₂.accept := rfl

/-! ### The ε-closure of `εconcat`.

The only ε-move is `inl s₁ → inr M₂.start` (present exactly when `s₁ ∈ M₁.accept`),
so the ε-closure of `S` adds at most the single state `inr M₂.start`. -/
#count_heartbeats in --44
theorem εclosure_char (S : Set (σ₁ ⊕ σ₂)) (z : σ₁ ⊕ σ₂) :
    z ∈ (εconcat M₁ M₂).εClosure S ↔
      z ∈ S ∨ (z = Sum.inr M₂.start ∧ ∃ s₁ : σ₁, Sum.inl s₁ ∈ S ∧ s₁ ∈ M₁.accept) := by
  constructor
  · intro h
    induction h with
    | base s hs => exact Or.inl hs
    | step s t ht hs ih =>
      cases s with
      | inl s₁ =>
        by_cases hacc : s₁ ∈ M₁.accept
        · rw [εconcat_step_inl_none, if_pos hacc, Set.mem_singleton_iff] at ht
          have hin : Sum.inl s₁ ∈ S := by
            rcases ih with h' | ⟨he, _⟩
            · exact h'
            · simp at he
          exact Or.inr ⟨ht, s₁, hin, hacc⟩
        · rw [εconcat_step_inl_none, if_neg hacc] at ht
          simp at ht
      | inr s₂ =>
        rw [εconcat_step_inr_none] at ht
        simp at ht
  · rintro (hz | ⟨hz, s₁, hin, hacc⟩)
    · exact εNFA.εClosure.base z hz
    · subst hz
      have hbase : Sum.inl s₁ ∈ (εconcat M₁ M₂).εClosure S := εNFA.εClosure.base _ hin
      have hstep : Sum.inr M₂.start ∈ (εconcat M₁ M₂).step (Sum.inl s₁) none := by
        rw [εconcat_step_inl_none, if_pos hacc]; exact rfl
      exact εNFA.εClosure.step (Sum.inl s₁) (Sum.inr M₂.start) hstep hbase
#count_heartbeats in --42
/-- Closure of an `inl`-singleton: either you stay, or you ε-jump to `inr M₂.start`
(possible exactly when the state is accepting in `M₁`). -/
theorem mem_εcl_inl (w : σ₁) (z : σ₁ ⊕ σ₂) :
    z ∈ (εconcat M₁ M₂).εClosure {Sum.inl w} ↔
      z = Sum.inl w ∨ (z = Sum.inr M₂.start ∧ w ∈ M₁.accept) := by
  rw [εclosure_char]
  constructor
  · rintro (hz | ⟨hz, s₁, hin, hacc⟩)
    · exact Or.inl (Set.mem_singleton_iff.mp hz)
    · rw [Set.mem_singleton_iff] at hin
      have hs : s₁ = w := Sum.inl.inj hin
      subst hs
      exact Or.inr ⟨hz, hacc⟩
  · rintro (hz | ⟨hz, hacc⟩)
    · exact Or.inl (Set.mem_singleton_iff.mpr hz)
    · exact Or.inr ⟨hz, w, Set.mem_singleton_iff.mpr rfl, hacc⟩
#count_heartbeats in --29
/-- Closure of an `inr`-singleton: no ε-moves are available, so it is just the point. -/
theorem mem_εcl_inr (w : σ₂) (z : σ₁ ⊕ σ₂) :
    z ∈ (εconcat M₁ M₂).εClosure {Sum.inr w} ↔ z = Sum.inr w := by
  rw [εclosure_char]
  constructor
  · rintro (hz | ⟨hz, s₁, hin, hacc⟩)
    · exact Set.mem_singleton_iff.mp hz
    · rw [Set.mem_singleton_iff] at hin; simp at hin
  · intro hz
    exact Or.inl (Set.mem_singleton_iff.mpr hz)
#count_heartbeats in --53
/-- The key semantic characterization of the states reachable after reading `x`. -/
theorem eval_eq (x : List α) (z : σ₁ ⊕ σ₂) :
    z ∈ (εconcat M₁ M₂).eval x ↔
      z = Sum.inl (M₁.eval x) ∨
      ∃ u y, x = u ++ y ∧ M₁.eval u ∈ M₁.accept ∧ z = Sum.inr (M₂.eval y) := by
  induction x using List.reverseRecOn generalizing z with
  | nil =>
    rw [εNFA.eval_nil, εclosure_char]
    constructor
    · rintro (hmem | ⟨hz, s₁, hin, hacc⟩)
      · rw [εconcat_start_eq, Set.mem_insert_iff] at hmem
        rcases hmem with h1 | h2
        · exact Or.inl h1
        · by_cases hacc : M₁.start ∈ M₁.accept
          · rw [if_pos hacc, Set.mem_singleton_iff] at h2
            exact Or.inr ⟨[], [], rfl, hacc, h2⟩
          · rw [if_neg hacc] at h2; simp at h2
      · rw [εconcat_start_eq, Set.mem_insert_iff] at hin
        rcases hin with h1 | h2
        · have hs : s₁ = M₁.start := Sum.inl.inj h1
          subst hs
          exact Or.inr ⟨[], [], rfl, hacc, hz⟩
        · by_cases hacc2 : M₁.start ∈ M₁.accept
          · rw [if_pos hacc2, Set.mem_singleton_iff] at h2; simp at h2
          · rw [if_neg hacc2] at h2; simp at h2
    · rintro (hz | ⟨u, y, he, hu, hz⟩)
      · left
        rw [εconcat_start_eq, Set.mem_insert_iff]
        exact Or.inl hz
      · rw [List.nil_eq_append_iff] at he
        obtain ⟨hu0, hy0⟩ := he; subst hu0; subst hy0
        rw [DFA.eval_nil] at hu hz
        left
        rw [εconcat_start_eq, Set.mem_insert_iff]
        right
        rw [if_pos hu, Set.mem_singleton_iff]
        exact hz
  | append_singleton x a ih =>
    rw [εNFA.eval_append_singleton, εNFA.mem_stepSet_iff]
    constructor
    · rintro ⟨t, ht, hcl⟩
      rw [ih] at ht
      rcases ht with ht1 | ⟨u, y, hxuy, hu, htinr⟩
      · subst ht1
        rw [εconcat_step_inl_some, mem_εcl_inl, ← DFA.eval_append_singleton] at hcl
        rcases hcl with h1 | ⟨hzr, hacc⟩
        · exact Or.inl h1
        · exact Or.inr ⟨x ++ [a], [], (List.append_nil _).symm, hacc, hzr⟩
      · subst htinr
        rw [εconcat_step_inr_some, mem_εcl_inr, ← DFA.eval_append_singleton] at hcl
        exact Or.inr ⟨u, y ++ [a], by rw [hxuy, List.append_assoc], hu, hcl⟩
    · rintro (hz | ⟨u, y, hxuy, hu, hz⟩)
      · rw [DFA.eval_append_singleton] at hz
        refine ⟨Sum.inl (M₁.eval x), (ih _).mpr (Or.inl rfl), ?_⟩
        rw [εconcat_step_inl_some, mem_εcl_inl]
        exact Or.inl hz
      · rcases List.eq_nil_or_concat y with hy | ⟨y₀, b, hy⟩
        · subst hy
          rw [List.append_nil] at hxuy
          refine ⟨Sum.inl (M₁.eval x), (ih _).mpr (Or.inl rfl), ?_⟩
          rw [εconcat_step_inl_some, mem_εcl_inl]
          right
          refine ⟨?_, ?_⟩
          · rw [DFA.eval_nil] at hz; exact hz
          · rw [← DFA.eval_append_singleton, hxuy]; exact hu
        · rw [List.concat_eq_append] at hy
          subst hy
          rw [← List.append_assoc] at hxuy
          have hsplit : x = u ++ y₀ ∧ a = b := by
            have h := congrArg List.reverse hxuy
            simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
              List.nil_append, List.cons_append, List.cons.injEq] at h
            refine ⟨?_, h.1⟩
            have h2 := congrArg List.reverse h.2
            simpa only [List.reverse_reverse, List.reverse_append] using h2
          obtain ⟨hx, hab⟩ := hsplit
          rw [← hab] at hz
          refine ⟨Sum.inr (M₂.eval y₀), (ih _).mpr (Or.inr ⟨u, y₀, hx, hu, rfl⟩), ?_⟩
          rw [εconcat_step_inr_some, mem_εcl_inr, ← DFA.eval_append_singleton]
          exact hz

end DFA
open DFA in
#count_heartbeats in --22
/-- The ε-NFA `εconcat M₁ M₂` accepts exactly `M₁.accepts * M₂.accepts`. -/

theorem accepts {α : Type u} {σ₁ σ₂ : Type v} (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (εconcat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext x
  rw [Language.mem_mul]
  constructor
  · rintro ⟨S, hSacc, hSev⟩
    rw [εconcat_accept_eq, Set.mem_image] at hSacc
    obtain ⟨t, htacc, rfl⟩ := hSacc
    rw [eval_eq] at hSev
    rcases hSev with hfalse | ⟨u, y, hxuy, hu, hz⟩
    · simp at hfalse
    · have hty : t = M₂.eval y := Sum.inr.inj hz
      refine ⟨u, ?_, y, ?_, hxuy.symm⟩
      · rw [DFA.mem_accepts]; exact hu
      · rw [DFA.mem_accepts, ← hty]; exact htacc
  · rintro ⟨u, hu, y, hy, hxuy⟩
    rw [DFA.mem_accepts] at hu hy
    refine ⟨Sum.inr (M₂.eval y), ?_, ?_⟩
    · rw [εconcat_accept_eq, Set.mem_image]; exact ⟨M₂.eval y, hy, rfl⟩
    · rw [eval_eq]; right; exact ⟨u, y, hxuy.symm, hu, rfl⟩
#print axioms accepts
--[propext, choice, Quot.sound]
