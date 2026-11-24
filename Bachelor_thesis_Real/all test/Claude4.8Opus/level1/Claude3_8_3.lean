import Mathlib

/-!
# Regular languages are closed under concatenation

This file proves that the language product (concatenation) of two **regular**
languages is regular, using Mathlib's *own* notion of regularity,
`Language.IsRegular`, defined in `Mathlib/Computability/DFA.lean` as

    Language.IsRegular L  :=  ∃ σ, ∃ _ : Fintype σ, ∃ M : DFA T σ, M.accepts = L

i.e. a language is regular iff some **finite-state DFA** accepts it.  We do not
introduce or substitute any alternative characterisation.

Mathlib already provides closure under union (`Language.IsRegular.add`),
intersection (`Language.IsRegular.inf`), complement (`Language.IsRegular.compl`)
and reversal (`Language.IsRegular.reverse`), but **not** under the language
product `*`.  We supply it here as `Language.IsRegular.mul`.

## Strategy

Concatenation genuinely needs nondeterminism, so a product-DFA construction (as
used for union/intersection) does not work directly.  From DFAs `M₁`, `M₂` we
build an `NFA` over the state type `σ₁ ⊕ σ₂` that:

* simulates `M₁` on the `inl` side (deterministically);
* every time the `M₁`-component **enters** an accepting state, it additionally
  spawns `M₂`'s start state on the `inr` side (this replaces an ε-transition);
* simulates `M₂` on the `inr` side; the accepting states are the `inr` images of
  `M₂`'s accepting states.

We prove this NFA accepts exactly `M₁.accepts * M₂.accepts`, then push it through
`NFA.toDFA` (whose state type `Set (σ₁ ⊕ σ₂)` is again a `Fintype`).
-/

namespace RegularConcat

variable {T : Type*} {σ1 σ2 : Type*} (M1 : DFA T σ1) (M2 : DFA T σ2)
#count_heartbeats in --94
/-- The concatenation NFA over `σ1 ⊕ σ2`. -/
def cN : NFA T (σ1 ⊕ σ2) where
  step s a :=
    s.elim
      (fun p =>
        insert (Sum.inl (M1.step p a))
          {x | x = Sum.inr M2.start ∧ M1.step p a ∈ M1.accept})
      (fun q => {Sum.inr (M2.step q a)})
  start :=
    insert (Sum.inl M1.start)
      {x | x = Sum.inr M2.start ∧ M1.start ∈ M1.accept}
  accept := {x | ∃ q ∈ M2.accept, x = Sum.inr q}
#count_heartbeats in --35
@[simp] lemma cN_start :
    (cN M1 M2).start =
      insert (Sum.inl M1.start)
        {x | x = Sum.inr M2.start ∧ M1.start ∈ M1.accept} := rfl
#count_heartbeats in --40
@[simp] lemma cN_step_inl (p : σ1) (a : T) :
    (cN M1 M2).step (Sum.inl p) a =
      insert (Sum.inl (M1.step p a))
        {x | x = Sum.inr M2.start ∧ M1.step p a ∈ M1.accept} := rfl
#count_heartbeats in --27
@[simp] lemma cN_step_inr (q : σ2) (a : T) :
    (cN M1 M2).step (Sum.inr q) a = {Sum.inr (M2.step q a)} := rfl
#count_heartbeats in --31
@[simp] lemma cN_accept :
    (cN M1 M2).accept = {x | ∃ q ∈ M2.accept, x = Sum.inr q} := rfl
#count_heartbeats in --59
/-- The exact set of states reachable in `cN` after reading `w`:

* either the unique (deterministic) `M₁`-state `Sum.inl (M₁.eval w)`, or
* a state `Sum.inr (M₂.eval v)` for *every* way to write `w = u ++ v` with the
  prefix `u` accepted by `M₁`.

The statement quantifies over the state `s` (after the colon) so that the
inductive hypothesis is available at every state, not just the one we started
with. -/
lemma mem_evalFrom (w : List T) : ∀ s : σ1 ⊕ σ2,
    s ∈ (cN M1 M2).evalFrom (cN M1 M2).start w ↔
      s = Sum.inl (M1.evalFrom M1.start w) ∨
      ∃ u v, u ++ v = w ∧ M1.evalFrom M1.start u ∈ M1.accept ∧
        s = Sum.inr (M2.evalFrom M2.start v) := by
  induction w using List.reverseRecOn with
  | nil =>
    intro s
    simp only [NFA.evalFrom_nil, cN_start, Set.mem_insert_iff, Set.mem_setOf_eq,
      DFA.evalFrom_nil]
    constructor
    · rintro (h | ⟨h, hacc⟩)
      · exact Or.inl h
      · exact Or.inr ⟨[], [], rfl, hacc, h⟩
    · rintro (h | ⟨u, v, huv, hacc, h⟩)
      · exact Or.inl h
      · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp huv
        exact Or.inr ⟨h, hacc⟩
  | append_singleton xs a ih =>
    intro s
    rw [NFA.evalFrom_append, NFA.evalFrom_singleton, NFA.mem_stepSet]
    constructor
    -- (⇒) read the last symbol `a`, then use the IH on `xs`
    · rintro ⟨t, ht, hs⟩
      rw [ih t] at ht
      rcases ht with rfl | ⟨u, v, huv, hacc, rfl⟩
      · -- the predecessor state is the (unique) `M₁`-state after `xs`
        rw [cN_step_inl, Set.mem_insert_iff, Set.mem_setOf_eq] at hs
        rcases hs with rfl | ⟨rfl, hacc⟩
        · left
          rw [DFA.evalFrom_append_singleton]
        · right
          refine ⟨xs ++ [a], [], by simp, ?_, ?_⟩
          · rw [DFA.evalFrom_append_singleton]; exact hacc
          · rw [DFA.evalFrom_nil]
      · -- the predecessor state is an `M₂`-state `Sum.inr (M₂.eval v)`
        rw [cN_step_inr, Set.mem_singleton_iff] at hs
        right
        refine ⟨u, v ++ [a], ?_, hacc, ?_⟩
        · rw [← List.append_assoc, huv]
        · rw [hs, DFA.evalFrom_append_singleton]
    -- (⇐) build a predecessor state and a final transition
    · rintro (rfl | ⟨u, v, huv, hacc, rfl⟩)
      · -- the `M₁`-state case
        refine ⟨Sum.inl (M1.evalFrom M1.start xs), ?_, ?_⟩
        · rw [ih]; exact Or.inl rfl
        · rw [cN_step_inl, Set.mem_insert_iff]
          left
          rw [DFA.evalFrom_append_singleton]
      · -- split `v` as `[]` or `v0 ++ [b]` to find where `a` was consumed
        rcases List.eq_nil_or_concat v with rfl | ⟨v0, b, rfl⟩
        · -- `v = []`: `u = xs ++ [a]`, and `M₂.start` was just spawned
          rw [List.append_nil] at huv
          subst huv
          refine ⟨Sum.inl (M1.evalFrom M1.start xs), ?_, ?_⟩
          · rw [ih]; exact Or.inl rfl
          · rw [cN_step_inl, Set.mem_insert_iff, Set.mem_setOf_eq]
            right
            refine ⟨?_, ?_⟩
            · rw [DFA.evalFrom_nil]
            · rw [DFA.evalFrom_append_singleton] at hacc; exact hacc
        · -- `v = v0 ++ [b]`: cancel the trailing symbol, so `b = a`
          simp only [List.concat_eq_append] at huv ⊢
          rw [← List.append_assoc] at huv
          obtain ⟨hxs, hb⟩ := List.append_inj' huv rfl
          have hba : b = a := by simpa using hb
          subst hba
          refine ⟨Sum.inr (M2.evalFrom M2.start v0), ?_, ?_⟩
          · rw [ih]; exact Or.inr ⟨u, v0, hxs, hacc, rfl⟩
          · rw [cN_step_inr, Set.mem_singleton_iff, DFA.evalFrom_append_singleton]
#count_heartbeats in --22
/-- `cN` accepts exactly the concatenation `M₁.accepts * M₂.accepts`. -/
lemma accepts_eq : (cN M1 M2).accepts = M1.accepts * M2.accepts := by
  ext w
  rw [NFA.mem_accepts, Language.mem_mul]
  simp only [cN_accept, Set.mem_setOf_eq]
  constructor
  · rintro ⟨s, ⟨q, hq, rfl⟩, hmem⟩
    rw [mem_evalFrom] at hmem
    rcases hmem with h | ⟨u, v, huv, hu, hv⟩
    · simp at h            -- `Sum.inr _ = Sum.inl _` is impossible
    · refine ⟨u, ?_, v, ?_, huv⟩
      · show M1.evalFrom M1.start u ∈ M1.accept
        exact hu
      · show M2.evalFrom M2.start v ∈ M2.accept
        have hqv : q = M2.evalFrom M2.start v := by simpa using hv
        rw [← hqv]; exact hq
  · rintro ⟨u, hu, v, hv, rfl⟩
    refine ⟨Sum.inr (M2.evalFrom M2.start v),
      ⟨M2.evalFrom M2.start v, hv, rfl⟩, ?_⟩
    rw [mem_evalFrom]
    exact Or.inr ⟨u, v, rfl, hu, rfl⟩

end RegularConcat

#count_heartbeats in --26 heartbeats
/-- **Regular languages are closed under concatenation.**

If `L₁` and `L₂` are regular (in Mathlib's sense, `Language.IsRegular`), then so
is their language product `L₁ * L₂`. -/
theorem Language.IsRegular.mul {T : Type*} {L1 L2 : Language T}
    (h1 : L1.IsRegular) (h2 : L2.IsRegular) : (L1 * L2).IsRegular := by
  obtain ⟨σ1, _, M1, rfl⟩ := h1
  obtain ⟨σ2, _, M2, rfl⟩ := h2
  exact ⟨Set (σ1 ⊕ σ2), inferInstance, (RegularConcat.cN M1 M2).toDFA, by
    rw [NFA.toDFA_correct]; exact RegularConcat.accepts_eq M1 M2⟩

#print axioms Language.IsRegular.mul
--[propext, Classical.choice, Quot.sound]
--none
