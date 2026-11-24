/-
# Regular languages are closed under concatenation

This file proves from first principles that the concatenation `L₁ * L₂` of two
regular languages is regular, using Mathlib's definition of regularity
(`Language.IsRegular`): a language is regular if it is the language accepted by
a deterministic finite automaton (DFA) with a finite state type.  Note that on
`Language α` the semiring multiplication `*` *is* concatenation
(`Language.mem_mul : x ∈ l * m ↔ ∃ a ∈ l, ∃ b ∈ m, a ++ b = x`), so the
statement proved here, `Language.IsRegular.mul`, is exactly closure under
concatenation.

## The construction

Given DFAs `M₁ : DFA α σ₁` and `M₂ : DFA α σ₂`, we build a *nondeterministic*
automaton `concat M₁ M₂ : NFA α (σ₁ ⊕ σ₂)`:

* On `inl`-states it deterministically simulates `M₁`.  Whenever that
  simulation is *in* an accepting state of `M₁` — at time zero via the start
  set, or after a step via the transition relation — the NFA also
  nondeterministically spawns a copy of `M₂` in its start state (an
  `inr`-state).
* On `inr`-states it simulates `M₂`.
* It accepts exactly in the states `inr q` with `q ∈ M₂.accept`.

The key invariant (`concat_eval`) describes the set of states reachable after
reading `w`: it is

  `{inl (M₁.eval w)}  ∪  { inr (M₂.eval v) | w = u ++ v  and  M₁ accepts u }`.

From this, `(concat M₁ M₂).accepts = M₁.accepts * M₂.accepts` follows
(`concat_accepts`).  Finally, Mathlib's subset construction `NFA.toDFA` — whose
state type `Set (σ₁ ⊕ σ₂)` is finite because `σ₁ ⊕ σ₂` is — converts the NFA
back into a DFA, giving the main theorem `Language.IsRegular.mul`.

Declaration names were checked against Mathlib master (July 2026).
-/
import Mathlib.Computability.NFA
import Mathlib.Data.Fintype.Sum

open Sum

namespace RegularConcatenation

variable {α : Type*} {σ₁ σ₂ : Type*}

/-!
### Two elementary list facts

These are proved from scratch (using only `List.reverseRecOn`, `nil_append`,
`cons_append` and constructor injectivity), so the file does not depend on the
precise names of the corresponding library lemmas.
-/
#count_heartbeats in --31
/-- Every list is empty or has the form `v' ++ [a]`. -/
private theorem eq_nil_or_append_singleton (v : List α) :
    v = [] ∨ ∃ v' a, v = v' ++ [a] := by
  induction v using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton v' a _ => exact Or.inr ⟨v', a, rfl⟩

#count_heartbeats in --32
/-- Decompositions ending in a single element are unique. -/
private theorem append_singleton_inj :
    ∀ (w u : List α) (a b : α), w ++ [a] = u ++ [b] → w = u ∧ a = b := by
  intro w
  induction w with
  | nil =>
    intro u a b h
    cases u with
    | nil =>
      rw [List.nil_append, List.nil_append] at h
      injection h with h1 _
      exact ⟨rfl, h1⟩
    | cons y u =>
      rw [List.nil_append, List.cons_append] at h
      injection h with _ h2
      exact absurd h2.symm (by simp)
  | cons x w ih =>
    intro u a b h
    cases u with
    | nil =>
      rw [List.cons_append, List.nil_append] at h
      injection h with _ h2
      exact absurd h2 (by simp)
    | cons y u =>
      rw [List.cons_append, List.cons_append] at h
      injection h with h1 h2
      obtain ⟨rfl, rfl⟩ := ih u a b h2
      exact ⟨by rw [h1], rfl⟩
#count_heartbeats in --107
/-! ### The concatenation NFA -/

/-- The concatenation automaton of two DFAs `M₁`, `M₂`, an NFA on the state
type `σ₁ ⊕ σ₂`.  The `inl`-component simulates `M₁`; whenever it is in an
accepting state of `M₁`, a copy of `M₂` is nondeterministically started in an
`inr`-state.  Acceptance happens exactly in accepting `inr`-states. -/

def concat (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : NFA α (σ₁ ⊕ σ₂) where
  step p a :=
    match p with
    | inl q => {p' | p' = inl (M₁.step q a) ∨ (M₁.step q a ∈ M₁.accept ∧ p' = inr M₂.start)}
    | inr q => {p' | p' = inr (M₂.step q a)}
  start := {p | p = inl M₁.start ∨ (M₁.start ∈ M₁.accept ∧ p = inr M₂.start)}
  accept := {p | ∃ q ∈ M₂.accept, p = inr q}

variable (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)

/-! Membership in the four components of `concat`, as rewriting lemmas. -/

#count_heartbeats in --41
theorem mem_concat_step_inl {q : σ₁} {a : α} {p : σ₁ ⊕ σ₂} :
    p ∈ (concat M₁ M₂).step (inl q) a ↔
      p = inl (M₁.step q a) ∨ (M₁.step q a ∈ M₁.accept ∧ p = inr M₂.start) :=
  Iff.rfl

#count_heartbeats in --26
theorem mem_concat_step_inr {q : σ₂} {a : α} {p : σ₁ ⊕ σ₂} :
    p ∈ (concat M₁ M₂).step (inr q) a ↔ p = inr (M₂.step q a) :=
  Iff.rfl

#count_heartbeats in --37
theorem mem_concat_start {p : σ₁ ⊕ σ₂} :
    p ∈ (concat M₁ M₂).start ↔
      p = inl M₁.start ∨ (M₁.start ∈ M₁.accept ∧ p = inr M₂.start) :=
  Iff.rfl

#count_heartbeats in --31
theorem mem_concat_accept {p : σ₁ ⊕ σ₂} :
    p ∈ (concat M₁ M₂).accept ↔ ∃ q ∈ M₂.accept, p = inr q :=
  Iff.rfl
#count_heartbeats in --53
/-- **Key invariant.**  After reading `w`, the set of states of the
concatenation NFA is exactly: the `inl`-state tracking `M₁` on all of `w`,
together with one `inr`-state `inr (M₂.eval v)` for every decomposition
`w = u ++ v` whose prefix `u` drives `M₁` into an accepting state. -/

theorem concat_eval (w : List α) :
    (concat M₁ M₂).evalFrom (concat M₁ M₂).start w =
      {p | p = inl (M₁.eval w) ∨
        ∃ u v, w = u ++ v ∧ M₁.eval u ∈ M₁.accept ∧ p = inr (M₂.eval v)} := by
  induction w using List.reverseRecOn with
  | nil =>
    ext p
    rw [NFA.evalFrom_nil, mem_concat_start, Set.mem_setOf_eq]
    constructor
    · rintro (rfl | ⟨h, rfl⟩)
      · exact Or.inl (by rw [DFA.eval_nil])
      · exact Or.inr ⟨[], [], rfl, by rwa [DFA.eval_nil], by rw [DFA.eval_nil]⟩
    · rintro (rfl | ⟨u, v, huv, hacc, rfl⟩)
      · exact Or.inl (by rw [DFA.eval_nil])
      · obtain ⟨rfl, rfl⟩ : u = [] ∧ v = [] := by simpa using huv.symm
        rw [DFA.eval_nil] at hacc
        exact Or.inr ⟨hacc, by rw [DFA.eval_nil]⟩
  | append_singleton w a ih =>
    ext p
    rw [NFA.evalFrom_append, NFA.evalFrom_cons, NFA.evalFrom_nil, ih, NFA.mem_stepSet,
      Set.mem_setOf_eq]
    constructor
    -- Forward inclusion: every state reachable after `w ++ [a]` is of the
    -- claimed form.
    · rintro ⟨s, hs, hp⟩
      rw [Set.mem_setOf_eq] at hs
      rcases hs with rfl | ⟨u, v, rfl, hu, rfl⟩
      · -- the running copy of `M₁` makes a step ...
        rw [mem_concat_step_inl] at hp
        rcases hp with rfl | ⟨hacc, rfl⟩
        · exact Or.inl (by rw [DFA.eval_append_singleton])
        · -- ... and lands in an accepting state, spawning a fresh copy of `M₂`
          refine Or.inr ⟨w ++ [a], [], (List.append_nil _).symm, ?_, by rw [DFA.eval_nil]⟩
          rwa [DFA.eval_append_singleton]
      · -- a running copy of `M₂` makes a step
        rw [mem_concat_step_inr] at hp
        subst hp
        exact Or.inr ⟨u, v ++ [a], by rw [List.append_assoc], hu,
          by rw [DFA.eval_append_singleton]⟩
    -- Backward inclusion: every state of the claimed form is reachable.
    · rintro (rfl | ⟨u, v, huv, hu, rfl⟩)
      · -- the `inl`-state: step the copy of `M₁`
        refine ⟨inl (M₁.eval w), ?_, ?_⟩
        · rw [Set.mem_setOf_eq]
          exact Or.inl rfl
        · rw [mem_concat_step_inl]
          exact Or.inl (by rw [DFA.eval_append_singleton])
      · rcases eq_nil_or_append_singleton v with rfl | ⟨v', b, rfl⟩
        · -- `v = []`, so `u = w ++ [a]`: this is a freshly spawned copy of `M₂`
          obtain rfl : u = w ++ [a] := by simpa using huv.symm
          refine ⟨inl (M₁.eval w), ?_, ?_⟩
          · rw [Set.mem_setOf_eq]
            exact Or.inl rfl
          · rw [mem_concat_step_inl]
            refine Or.inr ⟨?_, by rw [DFA.eval_nil]⟩
            rwa [DFA.eval_append_singleton] at hu
        · -- `v = v' ++ [b]`: a copy of `M₂` that was already running steps
          rw [← List.append_assoc] at huv
          obtain ⟨rfl, rfl⟩ := append_singleton_inj _ _ _ _ huv
          refine ⟨inr (M₂.eval v'), ?_, ?_⟩
          · rw [Set.mem_setOf_eq]
            exact Or.inr ⟨u, v', rfl, hu, rfl⟩
          · rw [mem_concat_step_inr, DFA.eval_append_singleton]
#count_heartbeats in --23
/-- The concatenation NFA accepts exactly the concatenation of the two
languages. -/

theorem concat_accepts :
    (concat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext w
  rw [NFA.mem_accepts, Language.mem_mul]
  constructor
  · rintro ⟨p, hp, hw⟩
    rw [mem_concat_accept] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [concat_eval, Set.mem_setOf_eq] at hw
    rcases hw with h | ⟨u, v, rfl, hu, h⟩
    · -- an accepting state is an `inr`-state, never `inl`
      simp at h
    · obtain rfl : q = M₂.eval v := by simpa using h
      refine ⟨u, ?_, v, ?_, rfl⟩
      · rw [DFA.mem_accepts]
        exact hu
      · rw [DFA.mem_accepts]
        exact hq
  · rintro ⟨u, hu, v, hv, rfl⟩
    refine ⟨inr (M₂.eval v), ?_, ?_⟩
    · rw [mem_concat_accept]
      refine ⟨M₂.eval v, ?_, rfl⟩
      rw [← DFA.mem_accepts]
      exact hv
    · rw [concat_eval, Set.mem_setOf_eq]
      refine Or.inr ⟨u, v, rfl, ?_, rfl⟩
      rw [← DFA.mem_accepts]
      exact hu

end RegularConcatenation

open RegularConcatenation
#count_heartbeats in --28
/-- **Regular languages are closed under concatenation.**

If `L₁` and `L₂` are regular, so is their concatenation `L₁ * L₂`: run the
concatenation NFA on `σ₁ ⊕ σ₂` and determinize it with the subset construction
`NFA.toDFA`; the resulting DFA has the finite state type `Set (σ₁ ⊕ σ₂)`. -/

theorem Language.IsRegular.mul {α : Type*} {L₁ L₂ : Language α}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) : (L₁ * L₂).IsRegular := by
  obtain ⟨σ₁, _, M₁, rfl⟩ := h₁
  obtain ⟨σ₂, _, M₂, rfl⟩ := h₂
  exact ⟨Set (σ₁ ⊕ σ₂), inferInstance, (concat M₁ M₂).toDFA,
    ((concat M₁ M₂).toDFA_correct).trans (concat_accepts M₁ M₂)⟩

-- Sanity check: the theorem is usable with dot notation.
example {α : Type*} {L₁ L₂ : Language α} (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (L₁ * L₂).IsRegular :=
  h₁.mul h₂

#print axioms Language.IsRegular.mul
--'Language.IsRegular.mul' depends on axioms: [propext, Classical.choice, Quot.sound]
--none
