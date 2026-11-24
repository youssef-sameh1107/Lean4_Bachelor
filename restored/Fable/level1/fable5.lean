/-
Regular languages are closed under concatenation.

This file uses Mathlib's own definition of regularity, `Language.IsRegular`
(from `Mathlib/Computability/DFA.lean`):

  `def IsRegular (L : Language T) : Prop :=`
  `  ∃ σ : Type, ∃ _ : Fintype σ, ∃ M : DFA T σ, M.accepts = L`

and Mathlib's own concatenation of languages, which is the multiplication `*`
of the `Language` semiring: by `Language.mem_mul`,
`x ∈ L1 * L2 ↔ ∃ a ∈ L1, ∃ b ∈ L2, a ++ b = x`.

**Strategy.** Given DFAs `M1 : DFA α σ1` and `M2 : DFA α σ2`, we build the
standard concatenation NFA `M1.concat M2 : NFA α (σ1 ⊕ σ2)`: it simulates `M1`
on the `Sum.inl` states and `M2` on the `Sum.inr` states, and whenever the
simulated `M1`-state is accepting it nondeterministically also activates the
start state of `M2` (this replaces the usual ε-transition from accepting
states of `M1` to the start state of `M2`). We prove

  `(M1.concat M2).accepts = M1.accepts * M2.accepts`

by induction on the input word, using Mathlib's `NFA.acceptsFrom` API, and
finally convert the NFA back into a DFA with the subset construction
`NFA.toDFA` (whose state type `Set (σ1 ⊕ σ2)` is a `Fintype`), which yields
`Language.IsRegular.mul`.
-/
import Mathlib.Computability.NFA
import Mathlib.Data.Fintype.Sum

open Sum

namespace DFA

variable {α : Type*} {σ σ1 σ2 : Type*} {M1 : DFA α σ1} {M2 : DFA α σ2}

/-! ### Auxiliary lemmas about languages and `DFA.acceptsFrom` -/
#count_heartbeats in --36
private theorem nil_mem_mul_iff {P Q : Language α} :
    [] ∈ P * Q ↔ [] ∈ P ∧ [] ∈ Q := by
  constructor
  · intro h
    obtain ⟨u, hu, v, hv, huv⟩ := Language.mem_mul.mp h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp huv
    exact ⟨hu, hv⟩
  · rintro ⟨h1, h2⟩
    exact Language.mem_mul.mpr ⟨[], h1, [], h2, rfl⟩
#count_heartbeats in --25
private theorem cons_mem_acceptsFrom' {M : DFA α σ} {s : σ} {a : α} {x : List α} :
    a :: x ∈ M.acceptsFrom s ↔ x ∈ M.acceptsFrom (M.step s a) := by
  rw [DFA.mem_acceptsFrom, DFA.mem_acceptsFrom, DFA.evalFrom_cons]
#count_heartbeats in --25
private theorem cons_mem_accepts {M : DFA α σ} {a : α} {x : List α} :
    a :: x ∈ M.accepts ↔ x ∈ M.acceptsFrom (M.step M.start a) :=
  cons_mem_acceptsFrom'
#count_heartbeats in --13
private theorem accepts_eq_acceptsFrom_start (M : DFA α σ) :
    M.accepts = M.acceptsFrom M.start :=
  rfl
#count_heartbeats in --51
/-- Peeling one letter off a word of `M.acceptsFrom q * Q`: either the first
letter is consumed by `M` (leaving a word of `M.acceptsFrom (M.step q a) * Q`),
or the `M`-part of the word is empty, which forces `q` to be accepting and the
whole word to lie in `Q`. -/
private theorem cons_mem_acceptsFrom_mul_iff {M : DFA α σ} {Q : Language α}
    {q : σ} {a : α} {x : List α} :
    a :: x ∈ M.acceptsFrom q * Q ↔
      x ∈ M.acceptsFrom (M.step q a) * Q ∨ (q ∈ M.accept ∧ a :: x ∈ Q) := by
  constructor
  · intro h
    obtain ⟨u, hu, v, hv, huv⟩ := Language.mem_mul.mp h
    cases u with
    | nil =>
      rw [List.nil_append] at huv
      subst huv
      exact Or.inr ⟨(mem_acceptsFrom M).mp hu, hv⟩
    | cons b u =>
      rw [List.cons_append, List.cons.injEq] at huv
      obtain ⟨rfl, rfl⟩ := huv
      exact Or.inl (Language.mem_mul.mpr ⟨u, cons_mem_acceptsFrom'.mp hu, v, hv, rfl⟩)
  · rintro (h | ⟨hq, hx⟩)
    · obtain ⟨u, hu, v, hv, huv⟩ := Language.mem_mul.mp h
      refine Language.mem_mul.mpr ⟨a :: u, cons_mem_acceptsFrom'.mpr hu, v, hv, ?_⟩
      rw [List.cons_append, huv]
    · exact Language.mem_mul.mpr
        ⟨[], (mem_acceptsFrom M).mpr hq, a :: x, hx, List.nil_append _⟩
#count_heartbeats in --35
/-! ### The concatenation NFA -/

/-- The set of states of the concatenation automaton that are active when the
simulated run of `M1` is in state `q`: the state `Sum.inl q` itself and, in
case `q` is accepting for `M1`, additionally the start state of `M2`.  The
second part plays the role of the usual ε-transitions from accepting states of
`M1` to the start state of `M2`. -/
def concatFollow (M1 : DFA α σ1) (M2 : DFA α σ2) (q : σ1) : Set (σ1 ⊕ σ2) :=
  insert (inl q) {s | q ∈ M1.accept ∧ s = inr M2.start}
#count_heartbeats in --34
theorem mem_concatFollow {q : σ1} {s : σ1 ⊕ σ2} :
    s ∈ concatFollow M1 M2 q ↔ s = inl q ∨ (q ∈ M1.accept ∧ s = inr M2.start) := by
  simp only [concatFollow, Set.mem_insert_iff, Set.mem_setOf_eq]
#count_heartbeats in --39
theorem concatFollow_of_accept {q : σ1} (hq : q ∈ M1.accept) :
    concatFollow M1 M2 q = {inl q, inr M2.start} := by
  ext s
  rw [mem_concatFollow, Set.mem_insert_iff, Set.mem_singleton_iff]
  simp [hq]
#count_heartbeats in --26
theorem concatFollow_of_not_accept {q : σ1} (hq : q ∉ M1.accept) :
    concatFollow M1 M2 q = {inl q} := by
  ext s
  rw [mem_concatFollow, Set.mem_singleton_iff]
  simp [hq]
#count_heartbeats in --61
/-- The concatenation NFA of two DFAs `M1` and `M2`.  It simulates `M1` on the
`Sum.inl` states and `M2` on the `Sum.inr` states; whenever the simulated
`M1`-state is accepting, it nondeterministically also starts a run of `M2`.
Its accepted language is `M1.accepts * M2.accepts` (see `DFA.concat_accepts`). -/
def concat (M1 : DFA α σ1) (M2 : DFA α σ2) : NFA α (σ1 ⊕ σ2) where
  step
    | inl q, a => concatFollow M1 M2 (M1.step q a)
    | inr q, a => {inr (M2.step q a)}
  start := concatFollow M1 M2 M1.start
  accept := inr '' M2.accept
#count_heartbeats in --22
@[simp]
theorem concat_step_inl (q : σ1) (a : α) :
    (M1.concat M2).step (inl q) a = concatFollow M1 M2 (M1.step q a) :=
  rfl
#count_heartbeats in --27
@[simp]
theorem concat_step_inr (q : σ2) (a : α) :
    (M1.concat M2).step (inr q) a = {inr (M2.step q a)} :=
  rfl
#count_heartbeats in --18
@[simp]
theorem concat_start : (M1.concat M2).start = concatFollow M1 M2 M1.start :=
  rfl
#count_heartbeats in --21
@[simp]
theorem concat_accept : (M1.concat M2).accept = inr '' M2.accept :=
  rfl
#count_heartbeats in --23
theorem inr_mem_concat_accept {q : σ2} :
    inr q ∈ (M1.concat M2).accept ↔ q ∈ M2.accept := by
  rw [concat_accept]
  constructor
  · rintro ⟨t, ht, hts⟩
    obtain rfl : t = q := Sum.inr.inj hts
    exact ht
  · exact fun h => ⟨q, h, rfl⟩
#count_heartbeats in --17
theorem inl_not_mem_concat_accept {q : σ1} :
    inl q ∉ (M1.concat M2).accept := by
  rw [concat_accept]
  rintro ⟨t, -, hts⟩
  exact Sum.inr_ne_inl hts
#count_heartbeats in --29
/-! ### Correctness of the construction -/

/-- Once the concatenation automaton has handed control over to `M2` (i.e. is
in an `inr` state), it behaves exactly like `M2`. -/

theorem mem_concat_acceptsFrom_inr {x : List α} {q : σ2} :
    x ∈ (M1.concat M2).acceptsFrom {inr q} ↔ x ∈ M2.acceptsFrom q := by
  induction x generalizing q with
  | nil =>
    rw [NFA.nil_mem_acceptsFrom, DFA.mem_acceptsFrom, DFA.evalFrom_nil]
    constructor
    · rintro ⟨s, hs, hacc⟩
      rw [Set.mem_singleton_iff] at hs
      subst hs
      rwa [inr_mem_concat_accept] at hacc
    · exact fun h => ⟨inr q, rfl, inr_mem_concat_accept.mpr h⟩
  | cons a x ih =>
    rw [NFA.cons_mem_acceptsFrom, NFA.stepSet_singleton, concat_step_inr, ih,
      cons_mem_acceptsFrom']
#count_heartbeats in --34
/-- Key invariant: started from `concatFollow M1 M2 q`, the concatenation
automaton accepts exactly the concatenations of a word accepted by `M1` from
`q` with a word accepted by `M2`. -/
theorem mem_concat_acceptsFrom_follow {x : List α} {q : σ1} :
    x ∈ (M1.concat M2).acceptsFrom (concatFollow M1 M2 q) ↔
      x ∈ M1.acceptsFrom q * M2.accepts := by
  induction x generalizing q with
  | nil =>
    rw [NFA.nil_mem_acceptsFrom, nil_mem_mul_iff, DFA.mem_acceptsFrom,
      DFA.evalFrom_nil, DFA.mem_accepts, DFA.eval_nil]
    constructor
    · rintro ⟨s, hs, hacc⟩
      rcases mem_concatFollow.mp hs with rfl | ⟨hq, rfl⟩
      · exact absurd hacc inl_not_mem_concat_accept
      · exact ⟨hq, inr_mem_concat_accept.mp hacc⟩
    · rintro ⟨hq, hstart⟩
      exact ⟨inr M2.start, mem_concatFollow.mpr (Or.inr ⟨hq, rfl⟩),
        inr_mem_concat_accept.mpr hstart⟩
  | cons a x ih =>
    rw [NFA.cons_mem_acceptsFrom, cons_mem_acceptsFrom_mul_iff]
    by_cases hq : q ∈ M1.accept
    · rw [concatFollow_of_accept hq, Set.insert_eq, NFA.stepSet_union,
        NFA.stepSet_singleton, NFA.stepSet_singleton, concat_step_inl,
        concat_step_inr, NFA.acceptsFrom_union, Language.mem_add, ih,
        mem_concat_acceptsFrom_inr, cons_mem_accepts]
      simp [hq]
    · rw [concatFollow_of_not_accept hq, NFA.stepSet_singleton, concat_step_inl, ih]
      simp [hq]
#count_heartbeats in --23
/-- The concatenation NFA accepts exactly the concatenation of the languages of
the two DFAs. -/
@[simp]
theorem concat_accepts : (M1.concat M2).accepts = M1.accepts * M2.accepts := by
  ext x
  rw [NFA.accepts_eq_acceptsFrom_start, concat_start, mem_concat_acceptsFrom_follow,
    accepts_eq_acceptsFrom_start M1, accepts_eq_acceptsFrom_start M2]

end DFA
#count_heartbeats in --26
/-- **Regular languages are closed under concatenation.**

Here `Language.IsRegular` is Mathlib's definition of a regular language
(recognisability by a DFA with a `Fintype` of states), and `L1 * L2` is
Mathlib's concatenation of languages: by `Language.mem_mul`,
`x ∈ L1 * L2 ↔ ∃ a ∈ L1, ∃ b ∈ L2, a ++ b = x`. -/
protected theorem Language.IsRegular.mul {α : Type*} {L1 L2 : Language α}
    (h1 : L1.IsRegular) (h2 : L2.IsRegular) : (L1 * L2).IsRegular := by
  obtain ⟨σ1, _, M1, rfl⟩ := h1
  obtain ⟨σ2, _, M2, rfl⟩ := h2
  exact ⟨Set (σ1 ⊕ σ2), inferInstance, (M1.concat M2).toDFA,
    by rw [NFA.toDFA_correct, DFA.concat_accepts]⟩
#print axioms Language.IsRegular.mul
--[propext, Classical.choice, Quot.sound]
--none
