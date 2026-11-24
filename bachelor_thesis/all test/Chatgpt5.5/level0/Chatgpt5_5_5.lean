import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Powerset

open Set

namespace Language

#count_heartbeats in --14
private def dfaStepSet {α σ : Type*} (M : DFA α σ) (S : Set σ) (a : α) : Set σ :=
  (fun s => M.step s a) '' S

#count_heartbeats in --21
private def restartSet {α σ₁ σ₂ : Type*}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (q : σ₁) : Set σ₂ :=
  {s |
 q ∈ M₁.accept ∧ s = M₂.start}

#count_heartbeats in --58
/--
The product automaton for concatenation.
 After reading a word `x`, the first component is the state of `M₁` after reading `x`.
 The second component is the set of possible states of `M₂` after reading a suffix
which begins immediately after some prefix accepted by `M₁`.
 -/
private def concatDFA {α σ₁ σ₂ : Type*}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : DFA α (σ₁ × Set σ₂) where
  step st a :=
    let q := M₁.step st.1 a
    (q, dfaStepSet M₂ st.2 a ∪ restartSet M₁ M₂ q)
  start := (M₁.start, restartSet M₁ M₂ M₁.start)
  accept := {st |
 ∃ q, q ∈ st.2 ∧ q ∈ M₂.accept}

#count_heartbeats in --40
private def suffixStates {α σ₁ σ₂ : Type*}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (x : List α) : Set σ₂ :=
  {q |
 ∃ u : List α, ∃ v : List α,
      u ++ v = x ∧ M₁.eval u ∈ M₁.accept ∧ M₂.eval v = q}

#count_heartbeats in
private lemma append_eq_append_singleton_iff {α : Type*}
    {u v x : List α} {a : α} :
    u ++ v = x ++ [a] ↔
      (u = x ++ [a] ∧ v = []) ∨
        ∃ v', v = v' ++ [a] ∧ u ++ v' = x := by
  constructor
  ·
 intro h
    induction v using List.reverseRecOn with
    |
 nil =>
        left
        constructor
        · simpa using h
        · rfl
    |
 append_singleton v' b =>
        right
        have hr := congrArg List.reverse h
        have hcons : b :: (v'.reverse ++ u.reverse) = a :: x.reverse := by
          simpa [List.reverse_append, List.append_assoc] using hr
        injection hcons with hb htail
        subst b
        refine ⟨v', rfl, ?_⟩
        apply
 List.reverse_injective
        simpa [List.reverse_append] using htail
  · rintro (⟨rfl, rfl⟩ | ⟨v', rfl, hux⟩)
    · simp
    · simpa [List.append_assoc, hux]

#count_heartbeats in --15
private lemma suffixStates_nil {α σ₁ σ₂ : Type*}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    suffixStates M₁ M₂ [] = restartSet M₁ M₂ M₁.start := by
  ext q
  constructor
  · intro h
    change ∃ u : List α, ∃ v : List α,
      u ++ v =
 [] ∧ M₁.eval u ∈ M₁.accept ∧ M₂.eval v = q at h
    rcases h with ⟨u, v, huv, hu, hq⟩
    rcases List.append_eq_nil.mp huv with ⟨rfl, rfl⟩
    change M₁.start ∈ M₁.accept ∧ q = M₂.start
    exact ⟨by simpa using hu, by simpa using hq.symm⟩
  · intro h
    change M₁.start ∈ M₁.accept ∧ q = M₂.start at h
    rcases h with ⟨hacc, rfl⟩
    change ∃ u : List α, ∃ v : List α,

 u ++ v = [] ∧ M₁.eval u ∈ M₁.accept ∧ M₂.eval v = M₂.start
    exact ⟨[], [], by simp, by simpa using hacc, by simp⟩

#count_heartbeats in --45
private lemma suffixStates_append_singleton {α σ₁ σ₂ : Type*}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (x : List α) (a : α) :
    suffixStates M₁ M₂ (x ++ [a]) =
      dfaStepSet M₂ (suffixStates M₁ M₂ x) a ∪
        restartSet M₁ M₂ (M₁.eval (x ++ [a])) := by
  ext q

 constructor
  · intro h
    change ∃ u : List α, ∃ v : List α,
      u ++ v = x ++ [a] ∧
        M₁.eval u ∈ M₁.accept ∧ M₂.eval v = q at h
    rcases h with ⟨u, v, huv, hu, hq⟩
    rcases (append_eq_append_singleton_iff.mp huv) with hlast |
 hproper
    · rcases hlast with ⟨rfl, rfl⟩
      right
      change M₁.eval (x ++ [a]) ∈ M₁.accept ∧ q = M₂.start
      exact ⟨hu, by simpa using hq.symm⟩
    · rcases hproper with ⟨v', rfl, huv'⟩
      left
      change q ∈ (fun s => M₂.step s a) '' suffixStates M₁ M₂ x
      refine ⟨M₂.eval v', ?_, ?_⟩
      · change ∃ u : List α,
 ∃ v : List α,
          u ++ v = x ∧ M₁.eval u ∈ M₁.accept ∧ M₂.eval v = M₂.eval v'
        exact ⟨u, v', huv', hu, rfl⟩
      · simpa [DFA.eval_append_singleton] using hq
  · intro h
    change q ∈ dfaStepSet M₂ (suffixStates M₁ M₂ x) a ∪
      restartSet M₁ M₂ (M₁.eval (x ++ [a])) at h
    rcases h with hstep |
 hrestart
    · change q ∈ (fun s => M₂.step s a) '' suffixStates M₁ M₂ x at hstep
      rcases hstep with ⟨s, hS, hsq⟩
      change ∃ u : List α, ∃ v : List α,
        u ++ v = x ∧ M₁.eval u ∈ M₁.accept ∧ M₂.eval v = s at hS
      rcases hS with ⟨u, v, huv, hu, hs⟩
      change ∃ u : List α, ∃ v : List
 α,
        u ++ v = x ++ [a] ∧
          M₁.eval u ∈ M₁.accept ∧ M₂.eval v = q
      refine ⟨u, v ++ [a], ?_, hu, ?_⟩
      · simpa [List.append_assoc, huv]
      · simpa [DFA.eval_append_singleton, hs, hsq]
    · change M₁.eval (x ++ [a]) ∈ M₁.accept ∧ q = M₂.start at hrestart
      rcases hrestart with ⟨hacc, rfl⟩
      change ∃
 u : List α, ∃ v : List α,
        u ++ v = x ++ [a] ∧
          M₁.eval u ∈ M₁.accept ∧ M₂.eval v = M₂.start
      exact ⟨x ++ [a], [], by simp, hacc, by simp⟩

#count_heartbeats in --19
private lemma concatDFA_eval {α σ₁ σ₂ : Type*}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (x : List α) :
    (concatDFA M₁ M₂).eval x = (M₁.eval x, suffixStates M₁ M₂ x) := by
  induction
 x using List.reverseRecOn with
  | nil =>
      simp [concatDFA, suffixStates_nil]
  |
 append_singleton x a ih =>
      simp [concatDFA, ih, suffixStates_append_singleton]

#count_heartbeats in --23
private theorem concatDFA_correct {α σ₁ σ₂ : Type*}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (concatDFA M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext x
  constructor
  · intro hx
    have hx' :
        (concatDFA M₁ M₂).eval x ∈ (concatDFA M₁ M₂).accept := by
      simpa [DFA.accepts, DFA.acceptsFrom, DFA.eval] using hx
    rw [concatDFA_eval] at hx'

 have hx'' : ∃ q, q ∈ suffixStates M₁ M₂ x ∧ q ∈ M₂.accept := by
      simpa [concatDFA] using hx'
    rcases hx'' with ⟨q, hqS, hqacc⟩
    change ∃ u : List α, ∃ v : List α,
      u ++ v = x ∧ M₁.eval u ∈ M₁.accept ∧ M₂.eval v = q at hqS
    rcases hqS with ⟨u, v, huv, hu, hq⟩
    rw [Language.mem_mul]
    refine ⟨u, ?_, v, ?_, huv⟩
    ·
 simpa [DFA.accepts, DFA.acceptsFrom, DFA.eval] using hu
    · have hv : M₂.eval v ∈ M₂.accept := by
        simpa [hq] using hqacc
      simpa [DFA.accepts, DFA.acceptsFrom, DFA.eval] using hv
  · intro hx
    rw [Language.mem_mul] at hx
    rcases hx with ⟨u, hu, v, hv, huv⟩
    have hx' :
        (concatDFA M₁ M₂).eval x ∈ (concatDFA M₁ M₂).accept := by
      rw [concatDFA_eval]
      change ∃
 q, q ∈ suffixStates M₁ M₂ x ∧ q ∈ M₂.accept
      refine ⟨M₂.eval v, ?_, ?_⟩
      · change ∃ u' : List α, ∃ v' : List α,
          u' ++ v' = x ∧
            M₁.eval u' ∈ M₁.accept ∧ M₂.eval v' = M₂.eval v
        refine ⟨u, v, huv, ?_, rfl⟩
        simpa [DFA.accepts, DFA.acceptsFrom, DFA.eval] using hu

      · simpa [DFA.accepts, DFA.acceptsFrom, DFA.eval] using hv
    simpa [DFA.accepts, DFA.acceptsFrom, DFA.eval] using hx'

#count_heartbeats in --23
/-- Regular languages are closed under concatenation.
 -/
protected theorem IsRegular.mul {α : Type*} {L₁ L₂ : Language α}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (L₁ * L₂).IsRegular := by
  rcases h₁ with ⟨σ₁, fintype₁, M₁, hM₁⟩
  rcases h₂ with ⟨σ₂, fintype₂, M₂, hM₂⟩
  classical
  letI : Fintype σ₁ := fintype₁
  letI : Fintype σ₂ := fintype₂
  refine ⟨σ₁ × Set σ₂, inferInstance, concatDFA M₁ M₂, ?_⟩
  calc
    (concatDFA M₁ M₂).accepts = M₁.accepts * M₂.accepts :=
      concatDFA_correct M₁ M₂
    _ = L₁ * L₂ := by
      rw [hM₁, hM₂]

#count_heartbeats in --18 heartbeats

/-- Alias in theorem style.
 -/
theorem isRegular_mul {α : Type*} {L₁ L₂ : Language α}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (L₁ * L₂).IsRegular :=
  h₁.mul h₂

end Language
#print axioms Language.isRegular_mul
--[propext, sorryAx, Classical.choice, Quot.sound]

/-Used 14 heartbeats, which is less than the current maximum of 200000.
Used 22 heartbeats, which is less than the current maximum of 200000.
Used 58 heartbeats, which is less than the current maximum of 200000.
error: doc-strings should end with a single space or newline

Note: This linter can be disabled with `set_option linter.style.docString false`
Used 40 heartbeats, which is less than the current maximum of 200000.
unsolved goals
case mpr
α : Type u_1
u v x : List α
a : α
⊢ (u = x ++ [a] ∧ v = [] ∨ ∃ v', v = v' ++ [a] ∧ u ++ v' = x) → u ++ v = x ++ [a]
unsolved goals
case mp
α : Type u_1
u v x : List α
a : α
⊢ u ++ v = x ++ [a] → u = x ++ [a] ∧ v = [] ∨ ∃ v', v = v' ++ [a] ∧ u ++ v' = x
expected '{' or indented tactic sequence
Used 15 heartbeats, which is less than the current maximum of 200000.
Unknown constant `List.append_eq_nil.mp`
Error code: lean.unknownIdentifier
View explanation
Tactic `rcases` failed: `x✝ : ?m.75` is not an inductive datatype
Used 45 heartbeats, which is less than the current maximum of 200000.
unsolved goals
case h
α : Type u_1
σ₁ : Type u_2
σ₂ : Type u_3
M₁ : DFA α σ₁
M₂ : DFA α σ₂
x : List α
a : α
q : σ₂
⊢ q ∈ suffixStates M₁ M₂ (x ++ [a]) ↔ q ∈ dfaStepSet M₂ (suffixStates M₁ M₂ x) a ∪ restartSet M₁ M₂ (M₁.eval (x ++ [a]))
unexpected identifier; expected command
Used 19 heartbeats, which is less than the current maximum of 200000.
unsolved goals
case append_singleton
α : Type u_1
σ₁ : Type u_2
σ₂ : Type u_3
M₁ : DFA α σ₁
M₂ : DFA α σ₂
x : List α
a : α
ih : (concatDFA M₁ M₂).eval x = (M₁.eval x, suffixStates M₁ M₂ x)
⊢ M₁.step
      ({ step := fun st a ↦ (M₁.step st.1 a, dfaStepSet M₂ st.2 a ∪ restartSet M₁ M₂ (M₁.step st.1 a)),
              start := (M₁.start, restartSet M₁ M₂ M₁.start), accept := {st | ∃ q ∈ st.2, q ∈ M₂.accept} }.eval
          x).1
      a =
    M₁.step (M₁.eval x) a ∧
  dfaStepSet M₂
        ({ step := fun st a ↦ (M₁.step st.1 a, dfaStepSet M₂ st.2 a ∪ restartSet M₁ M₂ (M₁.step st.1 a)),
                start := (M₁.start, restartSet M₁ M₂ M₁.start), accept := {st | ∃ q ∈ st.2, q ∈ M₂.accept} }.eval
            x).2
        a ∪
      restartSet M₁ M₂
        (M₁.step
          ({ step := fun st a ↦ (M₁.step st.1 a, dfaStepSet M₂ st.2 a ∪ restartSet M₁ M₂ (M₁.step st.1 a)),
                  start := (M₁.start, restartSet M₁ M₂ M₁.start), accept := {st | ∃ q ∈ st.2, q ∈ M₂.accept} }.eval
              x).1
          a) =
    dfaStepSet M₂ (suffixStates M₁ M₂ x) a ∪ restartSet M₁ M₂ (M₁.step (M₁.eval x) a)
This simp argument is unused:
  ih

Hint: Omit it from the simp argument list.
  simp [concatDFA, ih, suffixStates_append_singleton]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Used 23 heartbeats, which is less than the current maximum of 200000.
unsolved goals
case h.mpr
α : Type u_1
σ₁ : Type u_2
σ₂ : Type u_3
M₁ : DFA α σ₁
M₂ : DFA α σ₂
x : List α
⊢ x ∈ M₁.accepts * M₂.accepts → x ∈ (concatDFA M₁ M₂).accepts
unsolved goals
case h.mp
α : Type u_1
σ₁ : Type u_2
σ₂ : Type u_3
M₁ : DFA α σ₁
M₂ : DFA α σ₂
x : List α
hx : x ∈ (concatDFA M₁ M₂).accepts
hx' : (M₁.eval x, suffixStates M₁ M₂ x) ∈ (concatDFA M₁ M₂).accept
⊢ x ∈ M₁.accepts * M₂.accepts
unexpected token 'have'; expected command
Used 23 heartbeats, which is less than the current maximum of 200000.
error: doc-strings should end with a single space or newline

Note: This linter can be disabled with `set_option linter.style.docString false`
Used 18 heartbeats, which is less than the current maximum of 200000.
error: doc-strings should end with a single space or newline

Note: This linter can be disabled with `set_option linter.style.docString false`
'Language.isRegular_mul' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
