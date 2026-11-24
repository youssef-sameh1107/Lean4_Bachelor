import Mathlib

universe u v w
#count_heartbeats in --55
private def concatActive {α : Type u} {σ₁ : Type v} {σ₂ : Type w}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    (s₁ : σ₁) (S₂ : Set σ₂) (x : List α) : Set σ₂ :=
  {t |
    (∃ u ∈ S₂, t = M₂.evalFrom u x) ∨
    ∃ y z,
      x = y ++ z ∧
      y ≠ [] ∧
      M₁.evalFrom s₁ y ∈ M₁.accept ∧
      t = M₂.eval z}
#count_heartbeats in --73
private def concatDFA {α : Type u} {σ₁ : Type v} {σ₂ : Type w}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : DFA α (σ₁ × Set σ₂) where
  step s a :=
    let s₁' := M₁.step s.1 a
    (s₁',
      {t |
        (∃ u ∈ s.2, M₂.step u a = t) ∨
        (t = M₂.start ∧ s₁' ∈ M₁.accept)})
  start :=
    (M₁.start, {t | t = M₂.start ∧ M₁.start ∈ M₁.accept})
  accept :=
    {s | ∃ t ∈ s.2, t ∈ M₂.accept}
#count_heartbeats in --42
private theorem concatActive_cons {α : Type u} {σ₁ : Type v} {σ₂ : Type w}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    (s₁ : σ₁) (S₂ : Set σ₂) (a : α) (x : List α) :
    concatActive M₁ M₂ (M₁.step s₁ a)
      {t |
        (∃ u ∈ S₂, M₂.step u a = t) ∨
        (t = M₂.start ∧ M₁.step s₁ a ∈ M₁.accept)}
      x
    =
    concatActive M₁ M₂ s₁ S₂ (a :: x) := by
  ext t
  constructor
  · intro ht
    unfold concatActive at ht ⊢
    simp only [Set.mem_setOf_eq] at ht ⊢
    rcases ht with ⟨u, hu, htu⟩ | ⟨y, z, hy, hyne, hyacc, htz⟩
    · rcases hu with ⟨p, hp, hstep⟩ | ⟨hstart, hacc⟩
      · left
        refine ⟨p, hp, ?_⟩
        rw [htu, ← hstep]
        rfl
      · right
        refine ⟨[a], x, by rfl, by simp, ?_, ?_⟩
        · simpa using hacc
        · simpa [DFA.eval, hstart] using htu
    · right
      refine ⟨a :: y, z, ?_, by simp, ?_, htz⟩
      · simp [hy]
      · simpa using hyacc
  · intro ht
    unfold concatActive at ht ⊢
    simp only [Set.mem_setOf_eq] at ht ⊢
    rcases ht with ⟨p, hp, htp⟩ | ⟨y, z, hy, hyne, hyacc, htz⟩
    · left
      refine ⟨M₂.step p a, ?_, ?_⟩
      · left
        exact ⟨p, hp, rfl⟩
      · rw [htp]
        rfl
    · cases y with
      | nil =>
          exact (hyne rfl).elim
      | cons b y' =>
          simp only [List.cons_append] at hy
          cases hy
          cases y' with
          | nil =>
              left
              refine ⟨M₂.start, ?_, ?_⟩
              · right
                exact ⟨rfl, by simpa using hyacc⟩
              · simpa [DFA.eval] using htz
          | cons c y'' =>
              right
              refine ⟨c :: y'', z, ?_, by simp, ?_, htz⟩
              · rfl
              · simpa using hyacc
#count_heartbeats in --23
private theorem concatDFA_evalFrom {α : Type u} {σ₁ : Type v} {σ₂ : Type w}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    (s₁ : σ₁) (S₂ : Set σ₂) (x : List α) :
    (concatDFA M₁ M₂).evalFrom (s₁, S₂) x =
      (M₁.evalFrom s₁ x, concatActive M₁ M₂ s₁ S₂ x) := by
  induction x generalizing s₁ S₂ with
  | nil =>
      simp [concatActive]
  | cons a x ih =>
      simp [concatDFA, ih, concatActive_cons]
#count_heartbeats in --21
private theorem concatDFA_accepts {α : Type u} {σ₁ : Type v} {σ₂ : Type w}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (concatDFA M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext x
  rw [DFA.mem_accepts, Language.mem_mul]
  let I : Set σ₂ := {t | t = M₂.start ∧ M₁.start ∈ M₁.accept}
  have hEval :
      (concatDFA M₁ M₂).eval x =
        (M₁.eval x, concatActive M₁ M₂ M₁.start I x) := by
    simpa [DFA.eval, concatDFA, I] using
      (concatDFA_evalFrom M₁ M₂ M₁.start I x)
  rw [hEval]
  change
    (∃ t ∈ concatActive M₁ M₂ M₁.start I x, t ∈ M₂.accept) ↔
      ∃ a ∈ M₁.accepts, ∃ b ∈ M₂.accepts, a ++ b = x
  constructor
  · rintro ⟨t, ht, htacc⟩
    unfold concatActive at ht
    simp only [Set.mem_setOf_eq] at ht
    rcases ht with ⟨p, hp, htp⟩ | ⟨y, z, hyz, hyne, hyacc, htz⟩
    · rcases hp with ⟨hpstart, hstartacc⟩
      refine ⟨[], ?_, x, ?_, by simp⟩
      · rw [DFA.mem_accepts]
        simpa [DFA.eval] using hstartacc
      · rw [DFA.mem_accepts]
        simpa [DFA.eval, hpstart, htp] using htacc
    · refine ⟨y, ?_, z, ?_, hyz.symm⟩
      · rw [DFA.mem_accepts]
        simpa [DFA.eval] using hyacc
      · rw [DFA.mem_accepts]
        simpa [DFA.eval, htz] using htacc
  · rintro ⟨y, hy, z, hz, hyz⟩
    rw [DFA.mem_accepts] at hy hz
    cases y with
    | nil =>
        refine ⟨M₂.eval z, ?_, hz⟩
        unfold concatActive
        simp only [Set.mem_setOf_eq]
        left
        refine ⟨M₂.start, ?_, ?_⟩
        · exact ⟨rfl, by simpa [DFA.eval] using hy⟩
        · simp [DFA.eval, ← hyz]
    | cons a y' =>
        refine ⟨M₂.eval z, ?_, hz⟩
        unfold concatActive
        simp only [Set.mem_setOf_eq]
        right
        refine ⟨a :: y', z, hyz.symm, by simp, ?_, rfl⟩
        simpa [DFA.eval] using hy

namespace Language
#count_heartbeats in --23 heartbeats
theorem IsRegular.mul {α : Type u} {L₁ L₂ : Language α}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (L₁ * L₂).IsRegular := by
  rcases h₁ with ⟨σ₁, hσ₁, M₁, rfl⟩
  rcases h₂ with ⟨σ₂, hσ₂, M₂, rfl⟩
  letI := hσ₁
  letI := hσ₂
  exact ⟨σ₁ × Set σ₂, inferInstance, concatDFA M₁ M₂, concatDFA_accepts M₁ M₂⟩

end Language

#print axioms Language.IsRegular.mul

--'Language.IsRegular.mul' depends on axioms:
-- [propext, sorryAx, Classical.choice, Quot.sound]
--unclosed goal which allows for compilation but breaks with axioms
--| cons a x ih =>
--simp [concatDFA, ih, concatActive_cons]
/-unsolved goals
case cons
α : Type u
σ₁ : Type v
σ₂ : Type w
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
x : List α
ih : ∀ (s₁ : σ₁) (S₂ : Set σ₂), (concatDFA M₁ M₂).evalFrom (s₁, S₂) x = (M₁.evalFrom s₁ x, concatActive M₁ M₂ s₁ S₂ x)
s₁ : σ₁
S₂ : Set σ₂
⊢ { step := fun s a ↦ (M₁.step s.1 a, {t | (∃ u ∈ s.2, M₂.step u a = t) ∨ t = M₂.start ∧ M₁.step s.1 a ∈ M₁.accept}),
        start := (M₁.start, {t | t = M₂.start ∧ M₁.start ∈ M₁.accept}),
        accept := {s | ∃ t ∈ s.2, t ∈ M₂.accept} }.evalFrom
    (M₁.step s₁ a, {t | (∃ u ∈ S₂, M₂.step u a = t) ∨ t = M₂.start ∧ M₁.step s₁ a ∈ M₁.accept}) x =
  (M₁.evalFrom (M₁.step s₁ a) x, concatActive M₁ M₂ s₁ S₂ (a :: x))
This simp argument is unused:
  ih

Hint: Omit it from the simp argument list.
  simp [concatDFA, ih, concatActive_cons]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
This simp argument is unused:
  concatActive_cons

Hint: Omit it from the simp argument list.
  simp [concatDFA, ih, concatActive_cons]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
'Language.IsRegular.mul' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]-/
