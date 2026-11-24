/-
# Regular languages are closed under concatenation

This file proves `Language.isRegular_mul`: if `L₁` and `L₂` are regular languages
— in the sense of Mathlib's own `Language.IsRegular`, i.e. recognised by *some*
`DFA` with a finite state type — then their concatenation `L₁ * L₂` is regular.

Mathlib provides closure of `Language.IsRegular` under union (`IsRegular.add`),
intersection (`IsRegular.inf`) and complement (`IsRegular.compl`), but *not* under
concatenation, so we build it here from Mathlib's primitives only.

## Strategy

`IsRegular` is defined via `DFA`s, and concatenation is awkward to express
directly on deterministic automata, so we route through an `NFA`.

Given DFAs `M₁ : DFA α σ₁` and `M₂ : DFA α σ₂` we build a nondeterministic
automaton `concatNFA M₁ M₂` on the sum state type `σ₁ ⊕ σ₂`:

* it stays in the *left* copy while running `M₁`;
* on any transition that lands `M₁` in an accepting state it may additionally
  *jump* to `M₂.start` in the *right* copy;
* it then just runs `M₂` in the right copy;
* the start set contains `M₂.start` as well when `[] ∈ L₁`, and the accepting
  states are exactly the accepting states of `M₂` in the right copy.

We prove `(concatNFA M₁ M₂).accepts = M₁.accepts * M₂.accepts`, then transport
the language back to a `DFA` with `NFA.toDFA` (the subset construction), whose
state type `Set (σ₁ ⊕ σ₂)` is again a `Fintype`.
-/
import Mathlib

universe u

namespace RegularConcat

variable {α : Type u} {σ σ1 σ2 : Type}

/-- `evalFrom` starting from the empty set of states stays empty, hence the empty
start set accepts no word. -/
theorem nmem_acceptsFrom_empty (M : NFA α σ) (x : List α) :
    x ∉ M.acceptsFrom (∅ : Set σ) := by
  have hev : ∀ y : List α, M.evalFrom (∅ : Set σ) y = ∅ := by
    intro y
    induction y with
    | nil => rfl
    | cons a y ih => rw [NFA.evalFrom_cons, NFA.stepSet_empty, ih]
  rw [NFA.mem_acceptsFrom, hev]
  rintro ⟨s, -, hs⟩
  exact Set.not_mem_empty s hs

variable (M1 : DFA α σ1) (M2 : DFA α σ2)

/-- The concatenation NFA on the sum state type `σ₁ ⊕ σ₂`. -/
def concatNFA : NFA α (σ1 ⊕ σ2) where
  step p a :=
    p.elim
      (fun s => {Sum.inl (M1.step s a)} ∪
        {q | q = Sum.inr M2.start ∧ M1.step s a ∈ M1.accept})
      (fun t => {Sum.inr (M2.step t a)})
  start := {Sum.inl M1.start} ∪ {q | q = Sum.inr M2.start ∧ M1.start ∈ M1.accept}
  accept := {p | p.elim (fun _ => False) (fun t => t ∈ M2.accept)}

@[simp] theorem concatNFA_step_inl (s : σ1) (a : α) :
    (concatNFA M1 M2).step (Sum.inl s) a =
      {Sum.inl (M1.step s a)} ∪
        {q | q = Sum.inr M2.start ∧ M1.step s a ∈ M1.accept} := rfl

@[simp] theorem concatNFA_step_inr (t : σ2) (a : α) :
    (concatNFA M1 M2).step (Sum.inr t) a = {Sum.inr (M2.step t a)} := rfl

@[simp] theorem concatNFA_accept_inl (s : σ1) :
    (Sum.inl s ∈ (concatNFA M1 M2).accept) ↔ False := Iff.rfl

@[simp] theorem concatNFA_accept_inr (t : σ2) :
    (Sum.inr t ∈ (concatNFA M1 M2).accept) ↔ t ∈ M2.accept := Iff.rfl

theorem concatNFA_start :
    (concatNFA M1 M2).start =
      {Sum.inl M1.start} ∪ {q | q = Sum.inr M2.start ∧ M1.start ∈ M1.accept} := rfl

/-- Running the concatenation NFA from a single *right* state behaves exactly like
running `M₂` from that state. -/
theorem acceptsFrom_inr (t : σ2) (y : List α) :
    y ∈ (concatNFA M1 M2).acceptsFrom {Sum.inr t} ↔ M2.evalFrom t y ∈ M2.accept := by
  induction y generalizing t with
  | nil => simp [concatNFA_accept_inr, DFA.evalFrom_nil]
  | cons a y ih =>
    rw [NFA.cons_mem_acceptsFrom, NFA.stepSet_singleton, concatNFA_step_inr, ih,
      DFA.evalFrom_cons]

/-- Running the concatenation NFA from the guarded singleton
`{p | p = inr M₂.start ∧ Q}`: it accepts `x` iff `Q` holds and `M₂` accepts `x`. -/
theorem acceptsFrom_jump (Q : Prop) (x : List α) :
    x ∈ (concatNFA M1 M2).acceptsFrom {p | p = Sum.inr M2.start ∧ Q} ↔
      Q ∧ M2.evalFrom M2.start x ∈ M2.accept := by
  by_cases hQ : Q
  · have hset : {p : σ1 ⊕ σ2 | p = Sum.inr M2.start ∧ Q} = {Sum.inr M2.start} := by
      ext p; simp [hQ]
    rw [hset, acceptsFrom_inr]
    exact ⟨fun h => ⟨hQ, h⟩, fun h => h.2⟩
  · have hset : {p : σ1 ⊕ σ2 | p = Sum.inr M2.start ∧ Q} = (∅ : Set (σ1 ⊕ σ2)) := by
      ext p; simp [hQ]
    rw [hset]
    exact ⟨fun h => absurd h (nmem_acceptsFrom_empty _ _), fun h => absurd h.1 hQ⟩

/-- Running the concatenation NFA from a single *left* state `inl s`: it accepts
`w` iff `w` splits as a **nonempty** prefix `u` on which `M₁` (started at `s`)
accepts, followed by a suffix `v` on which `M₂` accepts. -/
theorem acceptsFrom_inl (s : σ1) (w : List α) :
    w ∈ (concatNFA M1 M2).acceptsFrom {Sum.inl s} ↔
      ∃ u v, w = u ++ v ∧ u ≠ [] ∧ M1.evalFrom s u ∈ M1.accept ∧
        M2.evalFrom M2.start v ∈ M2.accept := by
  induction w generalizing s with
  | nil =>
    constructor
    · intro h
      rw [NFA.nil_mem_acceptsFrom] at h
      obtain ⟨p, hp, hpacc⟩ := h
      rw [Set.mem_singleton_iff] at hp
      subst hp
      exact ((concatNFA_accept_inl M1 M2 s).mp hpacc).elim
    · rintro ⟨u, v, huv, hu, -, -⟩
      cases u with
      | nil => exact absurd rfl hu
      | cons b u' => simp at huv
  | cons a w ih =>
    rw [NFA.cons_mem_acceptsFrom, NFA.stepSet_singleton, concatNFA_step_inl,
      NFA.acceptsFrom_union, Language.mem_add, ih, acceptsFrom_jump]
    constructor
    · rintro (⟨u, v, huv, -, h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨a :: u, v, by rw [huv, List.cons_append], List.cons_ne_nil a u,
          by rw [DFA.evalFrom_cons]; exact h1, h2⟩
      · exact ⟨[a], w, rfl, List.cons_ne_nil a [],
          by rw [DFA.evalFrom_singleton]; exact h1, h2⟩
    · rintro ⟨u, v, huv, hu, h1, h2⟩
      cases u with
      | nil => exact absurd rfl hu
      | cons b u' =>
        rw [List.cons_append] at huv
        injection huv with hab hw
        subst hab
        cases u' with
        | nil =>
          rw [List.nil_append] at hw
          subst hw
          right
          exact ⟨by rw [DFA.evalFrom_singleton] at h1; exact h1, h2⟩
        | cons c u'' =>
          left
          exact ⟨c :: u'', v, hw, List.cons_ne_nil c u'',
            by rw [DFA.evalFrom_cons] at h1; exact h1, h2⟩

/-- **Correctness of the construction:** the concatenation NFA recognises exactly
the concatenation of the two DFA languages. -/
theorem concatNFA_accepts :
    (concatNFA M1 M2).accepts = M1.accepts * M2.accepts := by
  ext w
  rw [NFA.accepts_eq_acceptsFrom_start, concatNFA_start, NFA.acceptsFrom_union,
    Language.mem_add, acceptsFrom_inl, acceptsFrom_jump, Language.mem_mul]
  have e1 : ∀ x : List α, (M1.evalFrom M1.start x ∈ M1.accept) ↔ x ∈ M1.accepts :=
    fun _ => DFA.mem_accepts.symm
  have e2 : ∀ x : List α, (M2.evalFrom M2.start x ∈ M2.accept) ↔ x ∈ M2.accepts :=
    fun _ => DFA.mem_accepts.symm
  have e0 : (M1.start ∈ M1.accept) ↔ ([] ∈ M1.accepts) := DFA.mem_accepts.symm
  simp only [e0, e1, e2]
  constructor
  · rintro (⟨u, v, huv, -, hu1, hv2⟩ | ⟨h0, hw2⟩)
    · exact ⟨u, hu1, v, hv2, huv.symm⟩
    · exact ⟨[], h0, w, hw2, rfl⟩
  · rintro ⟨p, hp, q, hq, hpq⟩
    rcases eq_or_ne p [] with rfl | hp0
    · right
      rw [List.nil_append] at hpq
      subst hpq
      exact ⟨hp, hq⟩
    · left
      exact ⟨p, q, hpq.symm, hp0, hp, hq⟩

end RegularConcat

/-- **Regular languages are closed under concatenation.**

If `L₁` and `L₂` are regular (`Language.IsRegular`), then so is `L₁ * L₂`. -/
theorem Language.isRegular_mul {α : Type u} {L1 L2 : Language α}
    (h1 : L1.IsRegular) (h2 : L2.IsRegular) : (L1 * L2).IsRegular := by
  obtain ⟨σ1, fin1, M1, rfl⟩ := h1
  obtain ⟨σ2, fin2, M2, rfl⟩ := h2
  haveI := fin1
  haveI := fin2
  exact ⟨Set (σ1 ⊕ σ2), inferInstance, (RegularConcat.concatNFA M1 M2).toDFA, by
    rw [NFA.toDFA_correct, RegularConcat.concatNFA_accepts]⟩
#print axioms Language.isRegular_mul
--[propext, sorryAx, Classical.choice, Quot.sound]
/-Unknown constant `DFA.mem_accepts.symm`
Error code: lean.unknownIdentifier
View explanation
Unknown constant `DFA.mem_accepts.symm`
Error code: lean.unknownIdentifier
View explanation
Unknown constant `DFA.mem_accepts.symm`
Error code: lean.unknownIdentifier
View explanation
Unknown constant `Set.not_mem_empty`
Error code: lean.unknownIdentifier
View explanation-/
