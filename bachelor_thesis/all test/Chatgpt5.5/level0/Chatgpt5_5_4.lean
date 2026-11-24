import Mathlib.Computability.NFA

open Set
open Computability

universe u v w

#count_heartbeats in --21
@[simp] private theorem nfa_mem_acceptsFrom_empty {α : Type u} {σ : Type v}
    (M : NFA α σ) (x : List α) :
    x ∈ M.acceptsFrom (∅ : Set σ) ↔ False := by
  induction x with
  | nil =>
      simp [NFA.mem_acceptsFrom]
  | cons a x ih =>
      rw [NFA.cons_mem_acceptsFrom]
      simpa using ih

#count_heartbeats in --20
@[simp] private theorem dfa_toNFA_acceptsFrom_start {α : Type u} {σ : Type v}
    (M : DFA α σ) :
    M.toNFA.acceptsFrom ({M.start} : Set σ) = M.accepts := by
  rw [← (NFA.accepts_eq_acceptsFrom_start (M := M.toNFA))]
  simp

namespace DFA

#count_heartbeats in --86
/--
Given DFAs `M₁` and `M₂`, `concat M₁ M₂` recognizes the concatenation
of their languages.
 The state is `(s₁, S₂)`, where `s₁` is the current state of `M₁`,
and `S₂` is the set of possible states of `M₂` after choosing a split
point that occurred strictly before the current position.
 -/
def concat {α : Type u} {σ₁ : Type v} {σ₂ : Type w}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    DFA α (σ₁ × Set σ₂) where
  step q a :=
    ( M₁.step q.1 a,
      M₂.toNFA.stepSet
        (q.2 ∪ {s : σ₂ | q.1 ∈ M₁.accept ∧ s = M₂.start}) a )
  start := (M₁.start, ∅)
  accept :=
    {q |
 (∃ s ∈ q.2, s ∈ M₂.accept) ∨
         (q.1 ∈ M₁.accept ∧ M₂.start ∈ M₂.accept)}

#count_heartbeats in --60
/--
The key invariant for the concatenation automaton.
 Starting from state `(s₁, S₂)`, a word `x` is accepted iff either:

* `M₂`, started nondeterministically from `S₂`, accepts `x`;
 or
* there is a split `x = y ++ z` such that `M₁`, started from `s₁`,
  accepts `y`, and `M₂` accepts `z`.
 -/
theorem concat_acceptsFrom_iff {α : Type u} {σ₁ : Type v} {σ₂ : Type w}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    (s₁ : σ₁) (S₂ : Set σ₂) (x : List α) :
    x ∈ (concat M₁ M₂).acceptsFrom (s₁, S₂) ↔
      x ∈ M₂.toNFA.acceptsFrom S₂ ∨
        ∃ y z : List α,
          y ++ z = x ∧

   M₁.evalFrom s₁ y ∈ M₁.accept ∧
              z ∈ M₂.accepts := by
  induction x generalizing s₁ S₂ with
  | nil =>
      simp [concat, DFA.mem_acceptsFrom, NFA.mem_acceptsFrom,
        DFA.mem_accepts, DFA.eval] <;> tauto
  | cons a x ih =>
      change
        x ∈ (concat M₁ M₂).acceptsFrom
          (M₁.step s₁ a,
            M₂.toNFA.stepSet
              (S₂ ∪ {s : σ₂ | s₁ ∈ M₁.accept ∧ s = M₂.start}) a) ↔
          a :: x ∈ M₂.toNFA.acceptsFrom S₂ ∨

   ∃ y z : List α,
              y ++ z = a :: x ∧
                M₁.evalFrom s₁ y ∈ M₁.accept ∧
                  z ∈ M₂.accepts

      have hsplit0 :
          a :: x ∈

     M₂.toNFA.acceptsFrom
                ({s : σ₂ | s₁ ∈ M₁.accept ∧ s = M₂.start}) ↔
            s₁ ∈ M₁.accept ∧ a :: x ∈ M₂.accepts := by
        by_cases hs : s₁ ∈ M₁.accept
        · have hset :
            ({s : σ₂ | s₁ ∈ M₁.accept ∧ s = M₂.start}
 : Set σ₂) =
              ({M₂.start} : Set σ₂) := by
              ext s
              simp [hs]
          rw [hset]
          simp [hs]
        · have hset :
            ({s : σ₂
 | s₁ ∈ M₁.accept ∧ s = M₂.start} : Set σ₂) =
              (∅ : Set σ₂) := by
              ext s
              simp [hs]
          rw [hset]
          simp [hs]

      have hT :

 x ∈
              M₂.toNFA.acceptsFrom
                (M₂.toNFA.stepSet
                  (S₂ ∪ {s : σ₂ |
 s₁ ∈ M₁.accept ∧ s = M₂.start}) a) ↔
            a :: x ∈ M₂.toNFA.acceptsFrom S₂ ∨
              (s₁ ∈ M₁.accept ∧ a :: x ∈ M₂.accepts) := by
        rw [← (NFA.cons_mem_acceptsFrom
          (M := M₂.toNFA)
          (S := S₂ ∪ {s : σ₂ | s₁ ∈ M₁.accept ∧ s = M₂.start})

       (a := a) (x := x))]
        rw [NFA.acceptsFrom_union, Language.mem_add]
        rw [hsplit0]

      have hprefix :
          (∃ y z : List α,
              y ++ z = a :: x ∧
                M₁.evalFrom s₁ y ∈ M₁.accept ∧

              z ∈ M₂.accepts) ↔
            (s₁ ∈ M₁.accept ∧ a :: x ∈ M₂.accepts) ∨
              ∃ y z : List α,
                y ++ z = x ∧
                  M₁.evalFrom (M₁.step s₁ a) y
 ∈ M₁.accept ∧
                    z ∈ M₂.accepts := by
        constructor
        · rintro ⟨y, z, hcat, hy, hz⟩
          cases y with
          | nil =>
              have hz' : z = a :: x := by
                simpa using hcat
              subst z
              left
              exact ⟨by simpa using hy, hz⟩

 | cons b y =>
              right
              injection hcat with hb htail
              subst b
              refine ⟨y, z, htail, ?_, hz⟩
              simpa using hy
        · rintro (⟨hs, hz⟩ | ⟨y,
 z, hcat, hy, hz⟩)
          · refine ⟨[], a :: x, by simp, ?_, hz⟩
            simpa using hs
          · refine ⟨a :: y, z, ?_, ?_, hz⟩
            · simpa [hcat]
            · simpa using hy

      rw [ih, hT, hprefix]
      tauto

#count_heartbeats in --24

/--
 The DFA constructed above accepts exactly the concatenation language. -/
@[simp] theorem accepts_concat {α : Type u} {σ₁ : Type v} {σ₂ : Type w}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (concat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext x
  change
    x ∈ (concat M₁ M₂).acceptsFrom (M₁.start, (∅ : Set σ₂)) ↔
      x ∈ M₁.accepts * M₂.accepts
  rw [concat_acceptsFrom_iff]
  constructor
  · intro h
    rcases h with hEmpty |
 ⟨y, z, hcat, hy, hz⟩
    · exact False.elim ((nfa_mem_acceptsFrom_empty M₂.toNFA x).mp hEmpty)
    · rw [Language.mem_mul]
      exact ⟨y, by simpa [DFA.mem_accepts, DFA.eval] using hy, z, hz, hcat⟩
  · intro h
    rw [Language.mem_mul] at h
    rcases h with ⟨y, hy, z, hz, hcat⟩
    right
    exact ⟨y, z, hcat, by simpa [DFA.mem_accepts, DFA.eval] using hy, hz⟩

end DFA

namespace Language
#count_heartbeats in --23
/-- Regular languages are closed under concatenation.
 -/

theorem IsRegular.mul {α : Type u} {L₁ L₂ : Language α}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (L₁ * L₂).IsRegular := by
  rcases h₁ with ⟨σ₁, _, M₁, hM₁⟩
  rcases h₂ with ⟨σ₂, _, M₂, hM₂⟩
  refine ⟨σ₁ × Set σ₂, inferInstance, DFA.concat M₁ M₂, ?_⟩
  rw [DFA.accepts_concat, hM₁, hM₂]

end Language

#print axioms DFA.accepts_concat --doesnt compile completey
--[propext, sorryAx, Classical.choice, Quot.sound]

/-Used 21 heartbeats, which is less than the current maximum of 200000.
Used 20 heartbeats, which is less than the current maximum of 200000.
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  M.toNFA.acceptsFrom M.toNFA.start
in the target expression
  M.toNFA.acceptsFrom {M.start} = M.accepts

α : Type u
σ : Type v
M : DFA α σ
⊢ M.toNFA.acceptsFrom {M.start} = M.accepts
Used 87 heartbeats, which is less than the current maximum of 200000.
error: doc-strings should end with a single space or newline

Note: This linter can be disabled with `set_option linter.style.docString false`
Used 60 heartbeats, which is less than the current maximum of 200000.
Tactic `tauto` failed

case nil
α : Type u
σ₁ : Type v
σ₂ : Type w
M₁ : DFA α σ₁
M₂ : DFA α σ₂
s₁ : σ₁
S₂ : Set σ₂
⊢ (∃ s ∈ S₂, s ∈ M₂.accept) ∨ s₁ ∈ M₁.accept ∧ M₂.start ∈ M₂.accept ↔
  (∃ s ∈ M₂.accept, s ∈ S₂) ∨ s₁ ∈ M₁.accept ∧ M₂.start ∈ M₂.accept
unsolved goals
case cons
α : Type u
σ₁ : Type v
σ₂ : Type w
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
x : List α
ih : ∀ (s₁ : σ₁) (S₂ : Set σ₂),
  x ∈ (M₁.concat M₂).acceptsFrom (s₁, S₂) ↔
    x ∈ M₂.toNFA.acceptsFrom S₂ ∨ ∃ y z, y ++ z = x ∧ M₁.evalFrom s₁ y ∈ M₁.accept ∧ z ∈ M₂.accepts
s₁ : σ₁
S₂ : Set σ₂
hsplit0 : a :: x ∈ M₂.toNFA.acceptsFrom {s | s₁ ∈ M₁.accept ∧ s = M₂.start} ↔ s₁ ∈ M₁.accept ∧ a :: x ∈ M₂.accepts
hT : x ∈ M₂.toNFA.acceptsFrom (M₂.toNFA.stepSet (S₂ ∪ {s | s₁ ∈ M₁.accept ∧ s = M₂.start}) a) ↔
  a :: x ∈ M₂.toNFA.acceptsFrom S₂ ∨ s₁ ∈ M₁.accept ∧ a :: x ∈ M₂.accepts
hprefix : (∃ y z, y ++ z = a :: x ∧ M₁.evalFrom s₁ y ∈ M₁.accept ∧ z ∈ M₂.accepts) ↔
  s₁ ∈ M₁.accept ∧ a :: x ∈ M₂.accepts ∨ ∃ y z, y ++ z = x ∧ M₁.evalFrom (M₁.step s₁ a) y ∈ M₁.accept ∧ z ∈ M₂.accepts
⊢ x ∈ (M₁.concat M₂).acceptsFrom (M₁.step s₁ a, M₂.toNFA.stepSet (S₂ ∪ {s | s₁ ∈ M₁.accept ∧ s = M₂.start}) a) ↔
  a :: x ∈ M₂.toNFA.acceptsFrom S₂ ∨ ∃ y z, y ++ z = a :: x ∧ M₁.evalFrom s₁ y ∈ M₁.accept ∧ z ∈ M₂.accepts
unsolved goals
case mpr
α : Type u
σ₁ : Type v
σ₂ : Type w
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
x : List α
ih : ∀ (s₁ : σ₁) (S₂ : Set σ₂),
  x ∈ (M₁.concat M₂).acceptsFrom (s₁, S₂) ↔
    x ∈ M₂.toNFA.acceptsFrom S₂ ∨ ∃ y z, y ++ z = x ∧ M₁.evalFrom s₁ y ∈ M₁.accept ∧ z ∈ M₂.accepts
s₁ : σ₁
S₂ : Set σ₂
hsplit0 : a :: x ∈ M₂.toNFA.acceptsFrom {s | s₁ ∈ M₁.accept ∧ s = M₂.start} ↔ s₁ ∈ M₁.accept ∧ a :: x ∈ M₂.accepts
hT : x ∈ M₂.toNFA.acceptsFrom (M₂.toNFA.stepSet (S₂ ∪ {s | s₁ ∈ M₁.accept ∧ s = M₂.start}) a) ↔
  a :: x ∈ M₂.toNFA.acceptsFrom S₂ ∨ s₁ ∈ M₁.accept ∧ a :: x ∈ M₂.accepts
⊢ (s₁ ∈ M₁.accept ∧ a :: x ∈ M₂.accepts ∨ ∃ y z, y ++ z = x ∧ M₁.evalFrom (M₁.step s₁ a) y ∈ M₁.accept ∧ z ∈ M₂.accepts) →
  ∃ y z, y ++ z = a :: x ∧ M₁.evalFrom s₁ y ∈ M₁.accept ∧ z ∈ M₂.accepts
Alternative `cons` has not been provided
unexpected token '|'; expected command
Used 24 heartbeats, which is less than the current maximum of 200000.
error: doc-strings should start with a single space or newline

Note: This linter can be disabled with `set_option linter.style.docString false`
Used 23 heartbeats, which is less than the current maximum of 200000.
error: doc-strings should end with a single space or newline

Note: This linter can be disabled with `set_option linter.style.docString false`
'DFA.accepts_concat' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
