import Mathlib.Computability.Language
import Mathlib.Computability.DFA
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

open Set
open List
open Classical

universe u v

variable {α : Type*} [DecidableEq α]

#count_heartbeats in --88
/--
The DFA construction for concatenating M₁ and M₂.
The state space is `σ₁ × Set σ₂`.
A state `(q, S)` tracks the deterministic state `q` of M₁
and the non-deterministic set of possible states `S` in M₂.
-/
def concatDFA {σ₁ σ₂ : Type*} (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : DFA α (σ₁ × Set σ₂) where
  step s a :=
    let q₁' := M₁.step s.1 a
    let S' := (fun q => M₂.step q a) '' s.2
    (q₁', if q₁' ∈ M₁.accept then insert M₂.start S' else S')
  start := (M₁.start, if M₁.start ∈ M₁.accept then {M₂.start} else ∅)
  accept := { s |
(s.2 ∩ M₂.accept).Nonempty }

#count_heartbeats in --65
/--
A helper lemma explicitly characterising the second component of the DFA's state
after evaluating a string `x`.
It proves that the active states in M₂ are exactly
the ones spawned by any prefix of `x` that was accepted by M₁.
-/
lemma concatDFA_evalFrom_snd {σ₁ σ₂ : Type*} (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    (s : σ₁ × Set σ₂) (x : List α) :
    ((concatDFA M₁ M₂).evalFrom s x).2 =
      (fun q => M₂.evalFrom q x) '' s.2 ∪
      { q |
∃ u v, u ≠ [] ∧ x = u ++ v ∧ M₁.evalFrom s.1 u ∈ M₁.accept ∧ q = M₂.evalFrom M₂.start v } := by
  induction x generalizing s with
  |
nil =>
    ext q
    simp only [mem_union, mem_image, mem_setOf_eq]
    constructor
    · intro hq
      left
      exact ⟨q, hq, rfl⟩
    · rintro (⟨q', hq', rfl⟩ | ⟨u, v, hu, h_eq, h_acc, hq⟩)
      · exact hq'
      · exfalso
        cases u with
        |
nil => exact hu rfl
        |
cons _ _ => cases h_eq
  | cons a y ih =>
    have h_step : ((concatDFA M₁ M₂).evalFrom s (a :: y)).2 = ((concatDFA M₁ M₂).evalFrom ((concatDFA M₁ M₂).step s a) y).2 := rfl
    rw [h_step, ih ((concatDFA M₁ M₂).step s a)]
    ext q
    simp only [mem_union, mem_image, mem_setOf_eq]
    have hs' : ((concatDFA M₁ M₂).step s a).2 = if M₁.step s.1 a ∈ M₁.accept then insert M₂.start ((fun q => M₂.step q a) '' s.2) else (fun q => M₂.step q a) '' s.2
:= rfl
    constructor
    · rintro (⟨q', hq', rfl⟩ | ⟨u, v, hu, hy_eq, h_acc, rfl⟩)
      · by_cases h_in : M₁.step s.1 a ∈ M₁.accept
        · rw [hs', if_pos h_in] at hq'
          rcases hq' with (rfl | ⟨q'', hq'', rfl⟩)
          · right
            use [a], y

            constructor
            · exact fun h => by cases h
            · constructor
              · rfl
              · exact ⟨h_in, rfl⟩
          · left
            use q''

            exact ⟨hq'', rfl⟩
        · rw [hs', if_neg h_in] at hq'
          rcases hq' with ⟨q'', hq'', rfl⟩
          left
          use q''
          exact ⟨hq'', rfl⟩
      · right
        use a :: u, v
        constructor

        · exact fun h => by cases h
        · constructor
          · rw [hy_eq, cons_append]
          · exact ⟨h_acc, rfl⟩
    · rintro (⟨q', hq', rfl⟩ |
⟨u, v, hu, h_eq, h_acc, rfl⟩)
      · left
        use M₂.step q' a
        constructor
        · by_cases h_in : M₁.step s.1 a ∈ M₁.accept
          · rw [hs', if_pos h_in]
            exact Or.inr ⟨q', hq', rfl⟩
          · rw [hs', if_neg h_in]

           exact ⟨q', hq', rfl⟩
        · rfl
      · cases u with
        |
nil => contradiction
        |
cons b u_tl =>
          injection h_eq with h_hd h_tl
          subst h_hd
          cases u_tl with
          |
nil =>
            simp only [nil_append] at h_tl
            subst h_tl
            left
            use M₂.start
            constructor
            · rw [hs', if_pos h_acc]
              exact Or.inl rfl

            · rfl
          |
cons c u_tl' =>
            right
            use c :: u_tl', v
            constructor
            · exact fun h => by cases h
            · constructor
              · exact h_tl

              · exact ⟨h_acc, rfl⟩

#count_heartbeats in
/--
The main correctness theorem asserting that the generated DFA accepts exactly
the language derived from the concatenation of the original accepted sets.
-/
lemma concatDFA_accepts {σ₁ σ₂ : Type*} (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (concatDFA M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext x
  simp only [DFA.accepts, mem_setOf_eq]
  constructor
  · rintro ⟨q, hq_in, hq_acc⟩
    rw [concatDFA_evalFrom_snd] at hq_in
    rcases hq_in with ⟨q_base, h_base, rfl⟩ |
⟨u, v, hu, hx, h_acc_u, rfl⟩
    · by_cases h_start : M₁.start ∈ M₁.accept
      · rw [if_pos h_start] at h_base
        rcases h_base with rfl
        apply Set.mem_image2.mpr
        use [], h_start, x, hq_acc
        rfl
      · rw [if_neg h_start] at h_base
        exact False.elim h_base
    · apply Set.mem_image2.mpr
      use
u, h_acc_u, v, hq_acc
      exact hx.symm
  · intro h
    rcases Set.mem_image2.mp h with ⟨u, hu_in, v, hv_in, rfl⟩
    cases u with
    |
nil =>
      use M₂.evalFrom M₂.start v
      constructor
      · rw [concatDFA_evalFrom_snd]
        left
        use M₂.start
        constructor
        · rw [if_pos hu_in]
          rfl
        · rfl
      · exact hv_in
    |
cons a u' =>
      use M₂.evalFrom M₂.start v
      constructor
      · rw [concatDFA_evalFrom_snd]
        right
        use a :: u', v
        constructor
        · exact fun h => by cases h
        · constructor
          · rfl
          ·
exact ⟨hu_in, rfl⟩
      · exact hv_in

/--
Finally, the closure property applied to regular languages.
-/


#count_heartbeats in -- 20 heartbeats
theorem regular_closure_concat {L₁ L₂ : Language α}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) : (L₁ * L₂).IsRegular := by
  obtain ⟨M₁, hM₁⟩ := h₁
  obtain ⟨M₂, hM₂⟩ := h₂
  have h_acc : (concatDFA M₁ M₂).accepts = L₁ * L₂ := by
    rw [concatDFA_accepts, hM₁, hM₂]
  exact ⟨_, _, h_acc⟩

#print axioms regular_closure_concat
--[propext, sorryAx, Quot.sound]
