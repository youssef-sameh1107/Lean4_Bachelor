import Mathlib.Computability.Language
import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset

open Set Classical

universe u

namespace DFA

variable {α : Type u} {σ1 σ2 : Type} (M1 : DFA α σ1) (M2 : DFA α σ2)
#count_heartbeats in --33
-- Provides explicit helper for destructuring List.append = []
private lemma append_eq_nil_iff_both {A B : List α} : A ++ B = [] ↔ A = [] ∧ B = [] := by
  cases A <;> cases B <;> simp
#count_heartbeats in --37
-- Helper for reversing a singleton append to infer equality without heavy List libraries
private lemma append_singleton_inj {A B : List α} {a b : α} (h : A ++ [a] = B ++ [b]) : A = B ∧ a = b := by
  have hrev := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_singleton] at hrev
  have ha : a = b := by
    change a :: A.reverse = b :: B.reverse at hrev
    injection hrev
  have hA_rev : A.reverse = B.reverse := by
    change a :: A.reverse = b :: B.reverse at hrev
    injection hrev
  have hA : A = B := by rw [← List.reverse_reverse A, hA_rev, List.reverse_reverse]
  exact ⟨hA, ha⟩
#count_heartbeats in --71
private lemma append_singleton_eq_append_iff {x w y' : List α} {a : α} :
    x ++ [a] = w ++ y' ↔
    (y' = [] ∧ x ++ [a] = w) ∨ (∃ y, y' = y ++ [a] ∧ x = w ++ y) := by
  constructor
  · intro h
    induction y' using List.reverseRecOn with
    | nil => left; exact ⟨rfl, h.symm⟩
    | append_singleton y b _ih =>
      right
      rw [← List.append_assoc] at h
      have ⟨h1, h2⟩ := append_singleton_inj h
      subst h2
      exact ⟨y, rfl, h1⟩
  · rintro (⟨rfl, rfl⟩ | ⟨y, rfl, rfl⟩)
    · rfl
    · rw [List.append_assoc]
#count_heartbeats in --99
/-- DFA corresponding to the concatenation of two DFAs. -/
def concatDFA : DFA α (σ1 × Set σ2) where
  step p a :=
    let s1' := M1.step p.1 a
    let S2' := (fun s2 => M2.step s2 a) '' p.2 ∪ (if s1' ∈ M1.accept then {M2.start} else ∅)
    (s1', S2')
  start := (M1.start, if M1.start ∈ M1.accept then {M2.start} else ∅)
  accept := { p | ∃ s2 ∈ p.2, s2 ∈ M2.accept }
#count_heartbeats in --44
/-- The key invariant: after evaluating a string `x`, the new DFA is at `M1.eval x`
and tracks exactly the active states in M2 that correspond to a valid split `x = w ++ y`. -/
lemma concatDFA_eval (x : List α) :
    (concatDFA M1 M2).eval x =
      (M1.eval x,
       { s2 | ∃ w y, x = w ++ y ∧ w ∈ M1.accepts ∧ s2 = M2.eval y }) := by
  induction x using List.reverseRecOn with
  | nil =>
    rw [DFA.eval_nil, DFA.eval_nil]
    change (M1.start, if M1.start ∈ M1.accept then {M2.start} else ∅) = (M1.start, _)
    congr 1
    ext s2
    simp only [mem_setOf_eq, mem_singleton_iff, mem_empty_iff_false]
    split_ifs with h
    · constructor
      · rintro rfl
        have h_acc : [] ∈ M1.accepts := by rwa [DFA.mem_accepts, DFA.eval_nil]
        exact ⟨[], [], rfl, h_acc, rfl⟩
      · rintro ⟨w, y, heq, hw, rfl⟩
        have ⟨hw_eq, hy_eq⟩ := append_eq_nil_iff_both.mp heq.symm
        subst hw_eq hy_eq
        rfl
    · simp only [iff_false, not_exists, not_and]
      rintro w y heq hw rfl
      have ⟨hw_eq, hy_eq⟩ := append_eq_nil_iff_both.mp heq.symm
      subst hw_eq hy_eq
      apply h
      rwa [← DFA.eval_nil, ← DFA.mem_accepts]
  | append_singleton x a ih =>
    rw [DFA.eval_append_singleton, ih]
    change (M1.step (M1.eval x) a, _) = (M1.eval (x ++ [a]), _)
    rw [← DFA.eval_append_singleton M1 x a]
    congr 1
    ext s2
    simp only [mem_union, mem_image, mem_setOf_eq, mem_singleton_iff, mem_empty_iff_false]
    constructor
    · rintro (⟨s2_prev, ⟨w, y, hx, hw, rfl⟩, rfl⟩ | h_if)
      · refine ⟨w, y ++ [a], ?_, hw, ?_⟩
        · rw [hx, List.append_assoc]
        · rw [DFA.eval_append_singleton]
      · split_ifs at h_if with h_accept
        · refine ⟨x ++ [a], [], rfl, ?_, ?_⟩
          · rwa [DFA.mem_accepts]
          · rw [DFA.eval_nil]; exact h_if
        · exfalso; exact h_if
    · rintro ⟨w, y', h_eq, hw, rfl⟩
      have h_cases := append_singleton_eq_append_iff.mp h_eq
      rcases h_cases with ⟨rfl, rfl⟩ | ⟨y, rfl, rfl⟩
      · right
        split_ifs with h_accept
        · exact rfl
        · exfalso; apply h_accept
          rwa [← DFA.mem_accepts]
      · left
        refine ⟨M2.eval y, ⟨w, y, rfl, hw, rfl⟩, ?_⟩
        rw [DFA.eval_append_singleton]
#count_heartbeats in --22
/-- Proof that the accepted language matches exactly the language concatenation. -/
lemma concatDFA_accepts :
    (concatDFA M1 M2).accepts = M1.accepts * M2.accepts := by
  ext x
  simp only [DFA.mem_accepts, concatDFA_eval, concatDFA, mem_setOf_eq]
  constructor
  · rintro ⟨s2, ⟨w, y, rfl, hw, rfl⟩, hs2⟩
    rw [Language.mem_mul]
    exact ⟨w, hw, y, hs2, rfl⟩
  · intro h
    rw [Language.mem_mul] at h
    rcases h with ⟨w, hw, y, hy, rfl⟩
    exact ⟨M2.eval y, ⟨w, y, rfl, hw, rfl⟩, hy⟩

end DFA


namespace Language

#count_heartbeats in --23 heartbeats
/-- Regular languages are closed under concatenation. -/
theorem IsRegular.mul1 {α : Type u} {L1 L2 : Language α} (h1 : L1.IsRegular) (h2 : L2.IsRegular) : (L1 * L2).IsRegular := by
  rcases h1 with ⟨σ1, _, M1, rfl⟩
  rcases h2 with ⟨σ2, _, M2, rfl⟩
  -- The state type `σ1 × Set σ2` relies on mathlib finding Fintype for Product and Powerset automatically
  exact ⟨σ1 × Set σ2, inferInstance, DFA.concatDFA M1 M2, DFA.concatDFA_accepts M1 M2⟩

end Language

#print axioms Language.IsRegular.mul1
--[propext, sorryAx, choice, Quot.sound]
/-Invalid `⟨...⟩` notation: The expected type
  ({
            step := fun p a ↦
              (M1.step p.1 a, (fun s2 ↦ M2.step s2 a) '' p.2 ∪ if M1.step p.1 a ∈ M1.accept then {M2.start} else ∅),
            start := (M1.start, if M1.start ∈ M1.accept then {M2.start} else ∅),
            accept := {p | ∃ s2 ∈ p.2, s2 ∈ M2.accept} }.eval
        (w ++ y)).2
    (M2.eval y)
is not an inductive type

Note: This notation can only be used when the expected type is an inductive type with a single constructor
Tactic `rcases` failed: `left✝ : ({
          step := fun p a ↦
            (M1.step p.1 a, (fun s2 ↦ M2.step s2 a) '' p.2 ∪ if M1.step p.1 a ∈ M1.accept then {M2.start} else ∅),
          start := (M1.start, if M1.start ∈ M1.accept then {M2.start} else ∅),
          accept := {p | ∃ s2 ∈ p.2, s2 ∈ M2.accept} }.eval
      x).2
  s2` is not an inductive datatype
This simp argument is unused:
  concatDFA_eval

Hint: Omit it from the simp argument list.
  simp only [DFA.mem_accepts, concatDFA_eval, concatDFA, mem_setOf_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Used 22 heartbeats, which is less than the current maximum of 200000.
Application type mismatch: The argument
  rfl
has type
  ?m.415 = ?m.415
but is expected to have type
  x ++ [a] = x ++ [a] ++ []
in the application
  And.intro rfl
This simp argument is unused:
  mem_empty_iff_false

Hint: Omit it from the simp argument list.
  simp only [mem_union, mem_image, mem_setOf_eq, mem_singleton_iff, mem_empty_iff_false]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
This simp argument is unused:
  mem_singleton_iff

Hint: Omit it from the simp argument list.
  simp only [mem_union, mem_image, mem_setOf_eq, mem_singleton_iff, mem_empty_iff_false]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
`simp` made no progress
This simp argument is unused:
  mem_empty_iff_false

Hint: Omit it from the simp argument list.
  simp only [mem_setOf_eq, mem_singleton_iff, mem_empty_iff_false]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
This simp argument is unused:
  mem_singleton_iff

Hint: Omit it from the simp argument list.
  simp only [mem_setOf_eq, mem_singleton_iff, mem_empty_iff_false]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Used 44 heartbeats, which is less than the current maximum of 200000.
Used 99 heartbeats, which is less than the current maximum of 200000.
Tactic `rfl` failed: The left-hand side
  x ++ [a]
is not definitionally equal to the right-hand side
  x ++ [a] ++ []

case mpr.inl
α : Type u
x : List α
a : α
⊢ x ++ [a] = x ++ [a] ++ []
Application type mismatch: The argument
  Eq.symm h
has type
  w ++ [] = x ++ [a]
but is expected to have type
  x ++ [a] = w
in the application
  ⟨rfl, Eq.symm h⟩-/
