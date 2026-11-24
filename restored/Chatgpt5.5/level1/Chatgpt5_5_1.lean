import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Powerset

open Set

universe u v w

namespace DFA

variable {α : Type u} {σ₁ : Type v} {σ₂ : Type w}
#count_heartbeats in --77
/-- DFA construction recognizing the concatenation of two DFA languages.

The second component is the usual subset-construction state for the second DFA:
it stores all states of `M₂` reachable after a split point at which `M₁` has
accepted the prefix read so far.
-/

def concat (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : DFA α (σ₁ × Set σ₂) where
  step st a :=
    ( M₁.step st.1 a
    , Set.image (fun t => M₂.step t a) st.2 ∪
        {t | M₁.step st.1 a ∈ M₁.accept ∧ t = M₂.start} )
  start :=
    (M₁.start, {t | M₁.start ∈ M₁.accept ∧ t = M₂.start})
  accept :=
    {st | ∃ t ∈ st.2, t ∈ M₂.accept}
#count_heartbeats in --60
/-- The set represented by the second component after reading `x` from
a general concatenation-construction state `(s₁, S₂)`. -/
def concatTargetsFrom
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    (s₁ : σ₁) (S₂ : Set σ₂) (x : List α) : Set σ₂ :=
  {t |
    (∃ u ∈ S₂, M₂.evalFrom u x = t) ∨
      ∃ p q : List α,
        p ++ q = x ∧
        p ≠ [] ∧
        M₁.evalFrom s₁ p ∈ M₁.accept ∧
        M₂.eval q = t}
#count_heartbeats in --18
theorem concat_evalFrom_fst
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    (st : σ₁ × Set σ₂) (x : List α) :
    ((M₁.concat M₂).evalFrom st x).1 = M₁.evalFrom st.1 x := by
  induction x generalizing st with
  | nil =>
      simp
  | cons a x ih =>
      simpa [DFA.concat] using ih ((M₁.concat M₂).step st a)
#count_heartbeats in --42
theorem concatTargetsFrom_step
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    (s₁ : σ₁) (S₂ : Set σ₂) (a : α) (x : List α) :
    concatTargetsFrom M₁ M₂ (M₁.step s₁ a)
      (Set.image (fun t => M₂.step t a) S₂ ∪
        {t | M₁.step s₁ a ∈ M₁.accept ∧ t = M₂.start}) x
      =
    concatTargetsFrom M₁ M₂ s₁ S₂ (a :: x) := by
  ext t
  constructor
  · intro ht
    simp only [concatTargetsFrom, Set.mem_setOf_eq, Set.mem_union, Set.mem_image] at ht ⊢
    rcases ht with ⟨u, hu, hut⟩ | ⟨p, q, hpq, hpne, hpacc, hq⟩
    · rcases hu with ⟨v, hv, rfl⟩ | ⟨hacc, rfl⟩
      · left
        exact ⟨v, hv, by simpa [DFA.evalFrom_cons] using hut⟩
      · right
        refine ⟨[a], x, by simp, by simp, ?_, ?_⟩
        · simpa using hacc
        · simpa [DFA.eval] using hut
    · right
      refine ⟨a :: p, q, by simpa [hpq], by simp, ?_, hq⟩
      simpa [DFA.evalFrom_cons] using hpacc
  · intro ht
    simp only [concatTargetsFrom, Set.mem_setOf_eq, Set.mem_union, Set.mem_image] at ht ⊢
    rcases ht with ⟨u, hu, hut⟩ | ⟨p, q, hpq, hpne, hpacc, hq⟩
    · left
      refine ⟨M₂.step u a, ?_, ?_⟩
      · left
        exact ⟨u, hu, rfl⟩
      · simpa [DFA.evalFrom_cons] using hut
    · cases p with
      | nil =>
          exact (hpne rfl).elim
      | cons b p' =>
          simp only [List.cons_append, List.cons.injEq] at hpq
          rcases hpq with ⟨rfl, hpq⟩
          by_cases hp' : p' = []
          · subst p'
            simp only [List.nil_append] at hpq
            subst x
            left
            refine ⟨M₂.start, ?_, ?_⟩
            · right
              exact ⟨by simpa [DFA.evalFrom_cons] using hpacc, rfl⟩
            · simpa [DFA.eval] using hq
          · right
            exact ⟨p', q, hpq, hp', by simpa [DFA.evalFrom_cons] using hpacc, hq⟩
#count_heartbeats in
theorem concat_evalFrom_snd
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    (st : σ₁ × Set σ₂) (x : List α) :
    ((M₁.concat M₂).evalFrom st x).2 =
      concatTargetsFrom M₁ M₂ st.1 st.2 x := by
  induction x generalizing st with
  | nil =>
      ext t
      simp [concatTargetsFrom]
  | cons a x ih =>
      simp only [DFA.evalFrom_cons]
      rw [ih]
      simpa [DFA.concat] using
        concatTargetsFrom_step M₁ M₂ st.1 st.2 a x
#count_heartbeats in --29
theorem concat_eval_snd
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (x : List α) :
    ((M₁.concat M₂).eval x).2 =
      concatTargetsFrom M₁ M₂ M₁.start
        {t | M₁.start ∈ M₁.accept ∧ t = M₂.start} x := by
  simpa [DFA.eval, DFA.concat] using
    concat_evalFrom_snd M₁ M₂ ((M₁.concat M₂).start) x
#count_heartbeats in --22
/-- The DFA construction accepts exactly the concatenation of the two
accepted languages. -/
theorem accepts_concat
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (M₁.concat M₂).accepts = M₁.accepts * M₂.accepts := by
  ext x
  rw [Language.mem_mul]
  constructor
  · intro hx
    rw [DFA.mem_accepts] at hx
    rcases (by simpa [DFA.concat] using hx) with ⟨t, ht, htacc⟩
    rw [concat_eval_snd] at ht
    rcases ht with ⟨u, hu, hut⟩ | ⟨p, q, hpq, hpne, hpacc, hq⟩
    · rcases hu with ⟨hstart, rfl⟩
      refine ⟨[], ?_, x, ?_, by simp⟩
      · rw [DFA.mem_accepts]
        simpa using hstart
      · rw [DFA.mem_accepts]
        simpa [DFA.eval, hut] using htacc
    · refine ⟨p, ?_, q, ?_, hpq⟩
      · rw [DFA.mem_accepts]
        simpa [DFA.eval] using hpacc
      · rw [DFA.mem_accepts]
        simpa [DFA.eval, hq] using htacc
  · rintro ⟨p, hp, q, hq, hpq⟩
    rw [DFA.mem_accepts]
    change ∃ t ∈ ((M₁.concat M₂).eval x).2, t ∈ M₂.accept
    refine ⟨M₂.eval q, ?_, ?_⟩
    · rw [concat_eval_snd]
      by_cases hpnil : p = []
      · subst p
        simp only [List.nil_append] at hpq
        subst x
        left
        refine ⟨M₂.start, ?_, rfl⟩
        exact ⟨by simpa [DFA.mem_accepts] using hp, rfl⟩
      · right
        exact
          ⟨p, q, hpq, hpnil,
            by simpa [DFA.mem_accepts, DFA.eval] using hp,
            rfl⟩
    · simpa [DFA.mem_accepts] using hq

end DFA

namespace Language

#count_heartbeats in --23 heartbeats
/-- Regular languages are closed under concatenation. -/
theorem IsRegular.mul
    {T : Type u} {L₁ L₂ : Language T}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (L₁ * L₂).IsRegular := by
  classical
  obtain ⟨σ₁, hσ₁, M₁, hM₁⟩ := h₁
  obtain ⟨σ₂, hσ₂, M₂, hM₂⟩ := h₂
  letI : Fintype σ₁ := hσ₁
  letI : Fintype σ₂ := hσ₂
  refine ⟨σ₁ × Set σ₂, inferInstance, M₁.concat M₂, ?_⟩
  simp [DFA.accepts_concat, hM₁, hM₂]

end Language

#print axioms Language.IsRegular.mul
--'Language.IsRegular.mul' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]

--    rw [concat_eval_snd] at ht this line

--unclosed goal which allows for compilation but breaks with axioms]
/-Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ((concat ?M₁ ?M₂).eval ?x).2
in the target expression
  t ∈
    ({
            step := fun st a ↦
              (M₁.step st.1 a, (fun t ↦ M₂.step t a) '' st.2 ∪ {t | M₁.step st.1 a ∈ M₁.accept ∧ t = M₂.start}),
            start := (M₁.start, {t | M₁.start ∈ M₁.accept ∧ t = M₂.start}),
            accept := {st | ∃ t ∈ st.2, t ∈ M₂.accept} }.eval
        x).2

case h.mp
α : Type u
σ₁ : Type v
σ₂ : Type w
M₁ : DFA α σ₁
M₂ : DFA α σ₂
x : List α
hx : (M₁.concat M₂).eval x ∈ (M₁.concat M₂).accept
t : σ₂
ht : t ∈
  ({
          step := fun st a ↦
            (M₁.step st.1 a, (fun t ↦ M₂.step t a) '' st.2 ∪ {t | M₁.step st.1 a ∈ M₁.accept ∧ t = M₂.start}),
          start := (M₁.start, {t | M₁.start ∈ M₁.accept ∧ t = M₂.start}),
          accept := {st | ∃ t ∈ st.2, t ∈ M₂.accept} }.eval
      x).2
htacc : t ∈ M₂.accept
⊢ ∃ a ∈ M₁.accepts, ∃ b ∈ M₂.accepts, a ++ b = x-/
