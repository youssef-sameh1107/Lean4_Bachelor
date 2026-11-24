import Mathlib.Computability.DFA
import Mathlib.Data.List.Basic

open Set
open Computability

namespace Language

universe u v w

variable {α : Type u}

namespace IsRegular
#count_heartbeats in --24
private def concatPost {σ₂ : Type v} (M₂ : DFA α σ₂) (S : Set σ₂) (a : α) : Set σ₂ :=
  { q | ∃ p ∈ S, M₂.step p a = q }
#count_heartbeats in --43
private def concatSuffixStates {σ₁ : Type v} {σ₂ : Type w}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (x : List α) : Set σ₂ :=
  { q | ∃ y z, y ++ z = x ∧ M₁.eval y ∈ M₁.accept ∧ M₂.evalFrom M₂.start z = q }
#count_heartbeats in --70
private lemma mem_concatSuffixStates_append_singleton_iff
    {σ₁ : Type v} {σ₂ : Type w}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (x : List α) (a : α) (q : σ₂) :
    q ∈ concatSuffixStates M₁ M₂ (x ++ [a]) ↔
      (∃ p, p ∈ concatSuffixStates M₁ M₂ x ∧ M₂.step p a = q) ∨
        (M₁.eval (x ++ [a]) ∈ M₁.accept ∧ q = M₂.start) := by
  constructor
  · intro h
    rcases h with ⟨y, z, hyz, hyacc, hzq⟩
    rcases (List.append_eq_append_iff.mp hyz) with ⟨t, hxt, hzt⟩ | ⟨t, hyt, htza⟩
    · left
      refine ⟨M₂.evalFrom M₂.start t, ?_, ?_⟩
      · exact ⟨y, t, hxt.symm, hyacc, rfl⟩
      · rw [hzt] at hzq
        simpa [DFA.evalFrom_append_singleton] using hzq
    · rcases (List.singleton_eq_append_iff.mp htza) with ⟨ht, hz⟩ | ⟨ht, hz⟩
      · left
        refine ⟨M₂.start, ?_, ?_⟩
        · refine ⟨x, [], by simp, ?_, by simp⟩
          simpa [ht] using (hyt ▸ hyacc)
        · rw [hz] at hzq
          simpa [DFA.evalFrom_singleton] using hzq
      · right
        constructor
        · simpa [ht] using (hyt ▸ hyacc)
        · rw [hz] at hzq
          simpa using hzq.symm
  · intro h
    rcases h with ⟨p, hp, hpq⟩ | ⟨hxacc, hq⟩
    · rcases hp with ⟨y, z, hyz, hyacc, hzp⟩
      refine ⟨y, z ++ [a], ?_, hyacc, ?_⟩
      · rw [← hyz, List.append_assoc]
      · simpa [DFA.evalFrom_append_singleton, hzp] using hpq
    · refine ⟨x ++ [a], [], by simp, hxacc, ?_⟩
      simpa [hq]
#count_heartbeats in --69
private lemma concatSuffixStates_append_singleton
    {σ₁ : Type v} {σ₂ : Type w}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (x : List α) (a : α) :
    concatPost M₂ (concatSuffixStates M₁ M₂ x) a ∪
        (if M₁.eval (x ++ [a]) ∈ M₁.accept then {M₂.start} else ∅)
      = concatSuffixStates M₁ M₂ (x ++ [a]) := by
  classical
  ext q
  by_cases h : M₁.eval (x ++ [a]) ∈ M₁.accept
  · simp [concatPost, mem_concatSuffixStates_append_singleton_iff, eq_comm, and_left_comm,
    and_assoc]
  · simp [concatPost, h, mem_concatSuffixStates_append_singleton_iff,
      and_left_comm, and_assoc]
#count_heartbeats in --90
private noncomputable def concatDFA {σ₁ : Type v} {σ₂ : Type w}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : DFA α (σ₁ × Set σ₂) := by
  classical
  exact
    { step := fun s a =>
        let q₁ := M₁.step s.1 a
        (q₁,
          concatPost M₂ s.2 a ∪
            (if q₁ ∈ M₁.accept then ({M₂.start} : Set σ₂) else ∅))
      start := (M₁.start, concatSuffixStates M₁ M₂ [])
      accept := { s | ∃ q ∈ s.2, q ∈ M₂.accept } }
#count_heartbeats in --21
private lemma concatDFA_eval {σ₁ : Type v} {σ₂ : Type w}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (x : List α) :
    (concatDFA M₁ M₂).eval x = (M₁.eval x, concatSuffixStates M₁ M₂ x) := by
  induction x using List.reverseRecOn with
  | nil =>
      simp [concatDFA]
  | append_singleton x a ih =>
      rw [DFA.eval_append_singleton, ih]
      simp [concatDFA, concatSuffixStates_append_singleton, DFA.eval_append_singleton]
#count_heartbeats in --24
private lemma concatDFA_accepts {σ₁ : Type v} {σ₂ : Type w}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (concatDFA M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  apply Language.ext
  intro x
  rw [DFA.mem_accepts, concatDFA_eval]
  change (∃ q ∈ concatSuffixStates M₁ M₂ x, q ∈ M₂.accept) ↔
    x ∈ M₁.accepts * M₂.accepts
  constructor
  · intro hx
    rcases hx with ⟨q, hqsplit, hqacc⟩
    rcases hqsplit with ⟨y, z, hyz, hyacc, hzq⟩
    rw [Language.mem_mul]
    refine ⟨y, ?_, z, ?_, hyz⟩
    · rw [DFA.mem_accepts]
      exact hyacc
    · rw [DFA.mem_accepts]
      simpa [DFA.eval, hzq] using hqacc
  · intro hx
    rw [Language.mem_mul] at hx
    rcases hx with ⟨y, hy, z, hz, hyz⟩
    rw [DFA.mem_accepts] at hy hz
    refine ⟨M₂.eval z, ?_, hz⟩
    exact ⟨y, z, hyz, hy, rfl⟩

#count_heartbeats in --19

theorem mul {L₁ L₂ : Language α} (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (L₁ * L₂).IsRegular := by
  classical
  rcases (Language.isRegular_iff.mp h₁) with ⟨σ₁, fintype₁, M₁, hM₁⟩
  rcases (Language.isRegular_iff.mp h₂) with ⟨σ₂, fintype₂, M₂, hM₂⟩
  letI := fintype₁
  letI := fintype₂
  refine Language.isRegular_iff.mpr ?_
  refine ⟨σ₁ × Set σ₂, inferInstance, concatDFA M₁ M₂, ?_⟩
  rw [concatDFA_accepts, hM₁, hM₂]

end IsRegular

end Language

#print axioms Language.IsRegular.mul
--[propext, sorryAx, Classical.choice, Quot.sound]
--way more issues
-- doesnt compile at all error in the "inferinstance"
/-No info found.
invalid `▸` notation, expected result type of cast is
  M₁.eval x ∈ M₁.accept
however, the equality
  hyt
of type
  y = x ++ t
does not contain the expected result type on either the left or the right hand side
invalid `▸` notation, expected result type of cast is
  M₁.step (M₁.eval x) a ∈ M₁.accept
however, the equality
  hyt
of type
  y = x ++ t
does not contain the expected result type on either the left or the right hand side
try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
Used 69 heartbeats, which is less than the current maximum of 200000.
failed to synthesize instance of type class
  Decidable (M₁.eval (x ++ [a]) ∈ M₁.accept)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Error code: lean.synthInstanceFailed
View explanation
unsolved goals
case pos
α : Type u
σ₁ : Type v
σ₂ : Type w
M₁ : DFA α σ₁
M₂ : DFA α σ₂
x : List α
a : α
q : σ₂
h : M₁.eval (x ++ [a]) ∈ M₁.accept
⊢ (∃ p ∈ concatSuffixStates M₁ M₂ x, q = M₂.step p a) ∨ q ∈ sorry () ↔
  (∃ p ∈ concatSuffixStates M₁ M₂ x, q = M₂.step p a) ∨ M₁.step (M₁.eval x) a ∈ M₁.accept ∧ q = M₂.start
This simp argument is unused:
  and_left_comm

Hint: Omit it from the simp argument list.
  simp [concatPost, mem_concatSuffixStates_append_singleton_iff, eq_comm, and_left_comm,and_assoc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
This simp argument is unused:
  and_assoc

Hint: Omit it from the simp argument list.
  simp [concatPost, mem_concatSuffixStates_append_singleton_iff, eq_comm, and_left_comm,
    and_assoc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
unsolved goals
case neg
α : Type u
σ₁ : Type v
σ₂ : Type w
M₁ : DFA α σ₁
M₂ : DFA α σ₂
x : List α
a : α
q : σ₂
h : M₁.eval (x ++ [a]) ∉ M₁.accept
⊢ (∃ p ∈ concatSuffixStates M₁ M₂ x, M₂.step p a = q) ∨ q ∈ sorry () ↔
  (∃ p ∈ concatSuffixStates M₁ M₂ x, M₂.step p a = q) ∨ M₁.step (M₁.eval x) a ∈ M₁.accept ∧ q = M₂.start
This simp argument is unused:
  h

Hint: Omit it from the simp argument list.
  simp [concatPost, h, mem_concatSuffixStates_append_singleton_iff,
      and_left_comm, and_assoc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
This simp argument is unused:
  and_left_comm

Hint: Omit it from the simp argument list.
  simp [concatPost, h, mem_concatSuffixStates_append_singleton_iff, and_left_comm, and_assoc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
This simp argument is unused:
  and_assoc

Hint: Omit it from the simp argument list.
  simp [concatPost, h, mem_concatSuffixStates_append_singleton_iff, and_left_comm, and_assoc]and_left_comm]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
unsolved goals
case append_singleton
α : Type u
σ₁ : Type v
σ₂ : Type w
M₁ : DFA α σ₁
M₂ : DFA α σ₂
x : List α
a : α
ih : (concatDFA M₁ M₂).eval x = (M₁.eval x, concatSuffixStates M₁ M₂ x)
⊢ (concatPost M₂ (concatSuffixStates M₁ M₂ x) a ∪ if M₁.step (M₁.eval x) a ∈ M₁.accept then {M₂.start} else ∅) =
  concatSuffixStates M₁ M₂ (x ++ [a])
This simp argument is unused:
  concatSuffixStates_append_singleton

Hint: Omit it from the simp argument list.
  simp [concatDFA, concatSuffixStates_append_singleton, DFA.eval_append_singleton]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Used 24 heartbeats, which is less than the current maximum of 200000.
Used 19 heartbeats, which is less than the current maximum of 200000.
failed to synthesize instance of type class
  Fintype (σ₁ × Set σ₂)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Error code: lean.synthInstanceFailed
View explanation
'Language.IsRegular.mul' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]-/
