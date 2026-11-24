/-
  Regular languages are closed under concatenation.

  We use Mathlib's own definition `Language.IsRegular` from
  `Mathlib.Computability.DFA`, which says a language is regular iff
  there exists a DFA (with a universe-polymorphic state type) whose
  accepted language is exactly that language.

  Proof outline:
  1. Unpack h₁ : L₁.IsRegular into a DFA M₁ with M₁.accepts = L₁,
     and likewise h₂ into M₂.
  2. Build an NFA N over σ₁ ⊕ σ₂ recognising L₁ * L₂.
  3. Convert N to a DFA via NFA.toDFA (Mathlib proves this preserves
     the language: NFA.toDFA_correct).
  4. Show N.accepts = M₁.accepts * M₂.accepts.
-/

import Mathlib.Computability.NFA

open Set Language

namespace Language

universe u v

variable {α : Type u}

/- The NFA for L₁ * L₂, given DFAs M₁ (for L₁) and M₂ (for L₂).

  States  : σ₁ ⊕ σ₂
  Start   : {inl M₁.start} ∪ (if M₁.start ∈ M₁.accept then {inr M₂.start} else ∅)
              (If M₁ accepts ε, M₂ may start immediately.)
  Step    : inl q --a→ {inl (M₁.step q a)}
                     ∪ (if M₁.step q a ∈ M₁.accept then {inr M₂.start} else ∅)
            inr q --a→ {inr (M₂.step q a)}
  Accept  : inr '' M₂.accept
-/
#count_heartbeats in --116
private def concatNFA {σ₁ σ₂ : Type v}
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : NFA α (σ₁ ⊕ σ₂) where
  step s a := match s with
    | Sum.inl q =>
        {Sum.inl (M₁.step q a)} ∪
        if M₁.step q a ∈ M₁.accept then {Sum.inr M₂.start} else ∅
    | Sum.inr q => {Sum.inr (M₂.step q a)}
  start := {Sum.inl M₁.start} ∪
           if M₁.start ∈ M₁.accept then {Sum.inr M₂.start} else ∅
  accept := Sum.inr '' M₂.accept

/-! ### Supporting lemmas -/

section ConcatNFA

variable {σ₁ σ₂ : Type v} (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
#count_heartbeats in --28
/-- The right component of the NFA exactly simulates M₂. -/
private lemma evalFrom_inr :
    ∀ (t : σ₂) (x : List α),
      (concatNFA M₁ M₂).evalFrom {Sum.inr t} x = {Sum.inr (M₂.evalFrom t x)}
  | _, []     => by simp
  | _, _ :: x => by
      simp only [NFA.evalFrom_cons, NFA.stepSet_singleton, concatNFA]
      exact evalFrom_inr _ x
#count_heartbeats in --61
/-- Crossing lemma: `Sum.inr q ∈ evalFrom {Sum.inl s} x` iff there is a
    *non-empty* prefix `u` (of `x = u ++ v`) such that M₁ reaches an accept
    state from `s` after `u`, and M₂ reaches `q` from its start after `v`. -/
private lemma inr_mem_evalFrom_inl :
    ∀ {s : σ₁} {x : List α} {q : σ₂},
      Sum.inr q ∈ (concatNFA M₁ M₂).evalFrom {Sum.inl s} x ↔
      ∃ u v, x = u ++ v ∧ u ≠ [] ∧
        M₁.evalFrom s u ∈ M₁.accept ∧ M₂.evalFrom M₂.start v = q
  | _, [],     _ => by
      simp only [NFA.evalFrom_nil, mem_singleton_iff]
      exact ⟨fun h => absurd h (by simp),
             fun ⟨u, _, h, hne, _⟩ =>
               absurd (List.append_eq_nil.mp h.symm).1 hne⟩
  | s, a :: x, q => by
      constructor
      · -- Forward direction
        intro hmem
        rw [NFA.evalFrom_cons, NFA.mem_evalFrom_iff_exists] at hmem
        obtain ⟨s_mid, hs_mid, hq⟩ := hmem
        simp only [NFA.stepSet_singleton, concatNFA, mem_union, mem_singleton_iff,
                   mem_ite_empty_right, mem_setOf_eq] at hs_mid
        rcases hs_mid with rfl | ⟨hacc, rfl⟩
        · -- Stayed in left component after reading a
          rw [inr_mem_evalFrom_inl] at hq
          obtain ⟨u, v, hx, hne, hacc', hq'⟩ := hq
          exact ⟨a :: u, v, by simp [hx], List.cons_ne_nil _ _, by simpa, hq'⟩
        · -- Crossed to right on letter a
          rw [evalFrom_inr] at hq
          simp only [mem_singleton_iff, Sum.inr.injEq] at hq
          exact ⟨[a], x, rfl, List.singleton_ne_nil a, by simpa, hq⟩
      · -- Backward direction
        rintro ⟨u, v, hx, hne, hacc, hq⟩
        match u with
        | [] => exact absurd rfl hne
        | b :: u' =>
            -- Decompose: a :: x = b :: u' ++ v gives b = a and u' ++ v = x
            have ⟨rfl, rfl⟩ : b = a ∧ u' ++ v = x := List.cons.inj hx
            rw [NFA.evalFrom_cons, NFA.mem_evalFrom_iff_exists]
            rcases List.eq_or_ne u' [] with rfl | hne'
            · -- u = [a]: cross immediately on a
              simp only [List.nil_append, DFA.evalFrom_singleton] at *
              exact ⟨Sum.inr M₂.start,
                     by simp [NFA.stepSet_singleton, concatNFA, mem_union,
                               mem_ite_empty_right, hacc],
                     by rw [evalFrom_inr]; simp [hq]⟩
            · -- u = a :: u' with u' ≠ []: stay in left component one more step
              exact ⟨Sum.inl (M₁.step s a),
                     by simp [NFA.stepSet_singleton, concatNFA],
                     inr_mem_evalFrom_inl.mpr ⟨u', v, rfl, hne', by simpa, hq⟩⟩
#count_heartbeats in --22
/- `concatNFA M₁ M₂` accepts exactly `M₁.accepts * M₂.accepts`. -/
private theorem concatNFA_accepts :
    (concatNFA M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext z
  simp only [NFA.mem_accepts, NFA.mem_acceptsFrom, mul_def, mem_setOf_eq]
  constructor
  · -- Forward: NFA accepts z → z ∈ L₁ * L₂
    rintro ⟨acc, ⟨q, hq_acc, rfl⟩, hacc⟩
    -- acc = Sum.inr q, q ∈ M₂.accept; hacc : Sum.inr q ∈ evalFrom N.start z
    rw [NFA.mem_evalFrom_iff_exists] at hacc
    obtain ⟨s_init, hs_init, hmem⟩ := hacc
    simp only [concatNFA, mem_union, mem_singleton_iff,
               mem_ite_empty_right, mem_setOf_eq] at hs_init
    rcases hs_init with rfl | ⟨h_eps, rfl⟩
    · -- s_init = Sum.inl M₁.start
      rw [inr_mem_evalFrom_inl] at hmem
      obtain ⟨u, v, hz, _, hu_acc, hv_q⟩ := hmem
      exact ⟨u, DFA.mem_accepts.mpr hu_acc,
             v, DFA.mem_accepts.mpr (hv_q ▸ hq_acc), hz⟩
    · -- s_init = Sum.inr M₂.start (M₁ accepts ε)
      rw [evalFrom_inr] at hmem
      simp only [mem_singleton_iff, Sum.inr.injEq] at hmem
      exact ⟨[], DFA.mem_accepts.mpr (by simpa using h_eps),
             z, DFA.mem_accepts.mpr (hmem ▸ hq_acc), by simp⟩
  · -- Backward: z ∈ L₁ * L₂ → NFA accepts z
    rintro ⟨u, hu, v, hv, rfl⟩
    rw [DFA.mem_accepts] at hu hv
    refine ⟨Sum.inr (M₂.evalFrom M₂.start v),
            ⟨M₂.evalFrom M₂.start v, hv, rfl⟩, ?_⟩
    rw [NFA.mem_evalFrom_iff_exists]
    rcases List.eq_or_ne u [] with rfl | hne
    · -- u = []: M₁ accepts ε, start already includes Sum.inr M₂.start
      simp only [DFA.evalFrom_nil] at hu
      exact ⟨Sum.inr M₂.start,
             by simp [concatNFA, mem_union, mem_ite_empty_right, hu],
             by rw [evalFrom_inr]; simp⟩
    · -- u ≠ []: start from Sum.inl M₁.start, cross after u
      exact ⟨Sum.inl M₁.start,
             by simp [concatNFA],
             inr_mem_evalFrom_inl.mpr ⟨u, v, rfl, hne, hu, rfl⟩⟩

end ConcatNFA

#count_heartbeats in --23

theorem IsRegular.mul {L₁ L₂ : Language α}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) : (L₁ * L₂).IsRegular := by
  -- Extract DFAs M₁, M₂ from the regularity witnesses
  obtain ⟨σ₁, M₁, rfl⟩ := h₁
  obtain ⟨σ₂, M₂, rfl⟩ := h₂
  -- Build the concatenation NFA and convert to a DFA
  exact ⟨Set (σ₁ ⊕ σ₂), (concatNFA M₁ M₂).toDFA,
         by rw [NFA.toDFA_correct, concatNFA_accepts]⟩
end Language

#print axioms Language.IsRegular.mul

/-Error when compliing "unterminated commetn had to remove to be able to measure
the output"-/
