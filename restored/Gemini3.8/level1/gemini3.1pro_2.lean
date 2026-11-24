import Mathlib.Computability.DFA
import Mathlib.Computability.Language
import Mathlib.Data.Set.Image
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod

open Language
open scoped Classical

namespace DFA

variable {α : Type _}
#count_heartbeats in --101
/-- The DFA recognizing the concatenation of the languages of two DFAs.
The state space tracks the deterministic evaluation of `M1`, and a set of possible
evaluations in `M2` (since the split between the first and second word is non-deterministic). -/
def concatDFA {σ₁ σ₂ : Type _} (M1 : DFA α σ₁) (M2 : DFA α σ₂) : DFA α (σ₁ × Set σ₂) where
  step := fun s a =>
    let q1' := M1.step s.1 a
    let Q2' := (s.2.image (fun q2 => M2.step q2 a)) ∪ (if q1' ∈ M1.accept then {M2.start} else ∅)
    (q1', Q2')
  start := (M1.start, if M1.start ∈ M1.accept then {M2.start} else ∅)
  accept := { s | ∃ q2 ∈ s.2, q2 ∈ M2.accept }
#count_heartbeats in --20
/-- The first component of the state always mirrors the exact evaluation of `M1`. -/
lemma concatDFA_evalFrom_fst {σ₁ σ₂ : Type _} (M1 : DFA α σ₁) (M2 : DFA α σ₂) (q1 : σ₁) (Q2 : Set σ₂) (w : List α) :
    ((concatDFA M1 M2).evalFrom (q1, Q2) w).1 = M1.evalFrom q1 w := by
  induction w generalizing q1 Q2 with
  | nil => rfl
  | cons a w ih =>
    simp only [DFA.evalFrom_cons]
    exact ih (M1.step q1 a) _
#count_heartbeats in --62
/-- The second component of the state contains all active states in `M2`.
These are the states reached by either propagating the existing states in `Q2`,
or by dynamically starting `M2` whenever `M1` reached an accept state in the past. -/
lemma concatDFA_evalFrom_snd {σ₁ σ₂ : Type _} (M1 : DFA α σ₁) (M2 : DFA α σ₂) (q1 : σ₁) (Q2 : Set σ₂) (w : List α) :
    ((concatDFA M1 M2).evalFrom (q1, Q2) w).2 =
      (Q2.image (fun q2 => M2.evalFrom q2 w)) ∪
      { q2_end | ∃ u v, w = u ++ v ∧ u ≠ [] ∧ M1.evalFrom q1 u ∈ M1.accept ∧ q2_end = M2.evalFrom M2.start v } := by
  induction w generalizing q1 Q2 with
  | nil =>
    ext x
    simp only [DFA.evalFrom_nil, List.append_eq_nil_iff, Set.mem_union, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro hx
      left
      exact ⟨x, hx, rfl⟩
    · rintro (⟨y, hy, rfl⟩ | ⟨u, v, ⟨rfl, rfl⟩, hne, _⟩)
      · exact hy
      · contradiction
  | cons a w ih =>
    simp only [DFA.evalFrom_cons]
    rw [ih]
    ext x
    simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq, concatDFA]
    constructor
    · rintro (⟨y, hy, rfl⟩ | ⟨u, v, heq, hne, hacc, rfl⟩)
      · rcases hy with ⟨q2, hq2, rfl⟩ | hy2
        · left
          exact ⟨q2, hq2, rfl⟩
        · by_cases h1 : M1.step q1 a ∈ M1.accept
          · simp only [h1, if_pos, Set.mem_singleton_iff] at hy2
            subst hy2
            right
            use [a], w
            exact ⟨rfl, by simp, h1, rfl⟩
          · simp only [h1, if_neg, Set.mem_empty_iff_false] at hy2
            contradiction
      · right
        use a :: u, v
        exact ⟨by rw [heq]; rfl, by simp, hacc, rfl⟩
    · rintro (⟨q2, hq2, rfl⟩ | ⟨u, v, heq, hne, hacc, rfl⟩)
      · left
        use M2.step q2 a
        constructor
        · left
          exact ⟨q2, hq2, rfl⟩
        · rfl
      · cases u with
        | nil => contradiction
        | cons a' u' =>
          injection heq with heq1 heq2
          subst heq1
          cases u' with
          | nil =>
            left
            use M2.start
            constructor
            · right
              by_cases h1 : M1.step q1 a ∈ M1.accept
              · rw [if_pos h1]
                rfl
              · change M1.step q1 a ∈ M1.accept at hacc
                exact False.elim (h1 hacc)
            · rw [heq2]
          | cons b u'' =>
            right
            use b :: u'', v
            exact ⟨heq2, by simp, hacc, rfl⟩
#count_heartbeats in --21
/-- The composite DFA accepts precisely the concatenation of the two languages. -/
theorem concatDFA_accepts {σ₁ σ₂ : Type _} (M1 : DFA α σ₁) (M2 : DFA α σ₂) :
    (concatDFA M1 M2).accepts = M1.accepts * M2.accepts := by
  ext w
  simp only [DFA.mem_accepts, Language.mem_mul, concatDFA]
  change ∃ q2 ∈ ((concatDFA M1 M2).evalFrom (concatDFA M1 M2).start w).2, q2 ∈ M2.accept ↔ _
  rw [concatDFA_evalFrom_snd]
  constructor
  · rintro ⟨q2, hq2, hacc2⟩
    simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq] at hq2
    rcases hq2 with ⟨q2', hq2', rfl⟩ | ⟨u, v, heq, _, hacc1, rfl⟩
    · change q2' ∈ (if M1.start ∈ M1.accept then ({M2.start} : Set σ₂) else ∅) at hq2'
      by_cases h1 : M1.start ∈ M1.accept
      · simp only [h1, if_pos, Set.mem_singleton_iff] at hq2'
        subst hq2'
        use [], h1, w, hacc2
        rfl
      · simp only [h1, if_neg, Set.mem_empty_iff_false] at hq2'
        contradiction
    · use u, hacc1, v, hacc2, heq
  · rintro ⟨u, hu, v, hv, rfl⟩
    use M2.evalFrom M2.start v
    constructor
    · cases u with
      | nil =>
        left
        use M2.start
        constructor
        · change M2.start ∈ (if M1.start ∈ M1.accept then ({M2.start} : Set σ₂) else ∅)
          rw [if_pos hu]
          rfl
        · rfl
      | cons a u' =>
        right
        use a :: u', v
        exact ⟨rfl, by simp, hu, rfl⟩
    · exact hv

end DFA

#count_heartbeats in --23 heartbeats
/-- Main Theorem: Regular languages are closed under concatenation. -/
theorem Language.IsRegular.mul {α : Type _} {L M : Language α} (hL : L.IsRegular) (hM : M.IsRegular) :
    (L * M).IsRegular := by
  rcases hL with ⟨σ₁, inst₁, M1, rfl⟩
  rcases hM with ⟨σ₂, inst₂, M2, rfl⟩
  -- We provide the Fintype using Mathlib's Fintype instances for `Prod` and `Set`
  use σ₁ × Set σ₂, inferInstance, DFA.concatDFA M1 M2
  exact DFA.concatDFA_accepts M1 M2

#print axioms Language.IsRegular.mul
--[propext, sorryAx, Classical.choice, Quot.sound]
