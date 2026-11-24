/-
Concatenation of two DFAs via an εNFA.

The construction `DFA.εconcat` is given verbatim as specified; everything after it
is the proof of `DFA.accepts`.
-/
import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.Language

open Classical

universe u v

namespace DFA

variable {α : Type u} {σ₁ σ₂ : Type v}

def εconcat (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : εNFA α (σ₁ ⊕ σ₂) where
  step s a :=
    match s, a with
    | Sum.inl s₁, some c => {Sum.inl (M₁.step s₁ c)}
    | Sum.inl s₁, none   => if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅
    | Sum.inr s₂, some c => {Sum.inr (M₂.step s₂ c)}
    | Sum.inr _ , none   => ∅
  start :=
    insert (Sum.inl M₁.start)
      (if M₁.start ∈ M₁.accept then ({Sum.inr M₂.start} : Set (σ₁ ⊕ σ₂)) else ∅)
  accept := Sum.inr '' M₂.accept

/-! ### Generic auxiliary lemmas -/

/-- Evaluating a DFA on `x ++ [a]`. -/
theorem eval_snoc {σ : Type*} (M : DFA α σ) (x : List α) (a : α) :
    M.eval (x ++ [a]) = M.step (M.eval x) a := by
  simp [DFA.eval, DFA.evalFrom]

/-- Every list is either empty or a list with an element appended. -/
theorem eq_nil_or_snoc (l : List α) : l = [] ∨ ∃ (l' : List α) (b : α), l = l' ++ [b] := by
  refine List.reverseRecOn l ?_ ?_
  · exact Or.inl rfl
  · intro l' b _
    exact Or.inr ⟨l', b, rfl⟩

section

variable (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)

/-! ### Unfolding lemmas for `εconcat` -/

theorem εconcat_step_inl_some (p : σ₁) (a : α) :
    (εconcat M₁ M₂).step (Sum.inl p) (some a) = {Sum.inl (M₁.step p a)} := rfl

theorem εconcat_step_inr_some (q : σ₂) (a : α) :
    (εconcat M₁ M₂).step (Sum.inr q) (some a) = {Sum.inr (M₂.step q a)} := rfl

theorem εconcat_step_inl_none (p : σ₁) :
    (εconcat M₁ M₂).step (Sum.inl p) none =
      (if p ∈ M₁.accept then {Sum.inr M₂.start} else ∅) := rfl

theorem εconcat_step_inr_none (q : σ₂) :
    (εconcat M₁ M₂).step (Sum.inr q) none = (∅ : Set (σ₁ ⊕ σ₂)) := rfl

theorem εconcat_start :
    (εconcat M₁ M₂).start =
      insert (Sum.inl M₁.start)
        (if M₁.start ∈ M₁.accept then ({Sum.inr M₂.start} : Set (σ₁ ⊕ σ₂)) else ∅) := rfl

theorem εconcat_accept :
    (εconcat M₁ M₂).accept = Sum.inr '' M₂.accept := rfl

/-! ### The ε-closure

The only ε-transitions of `εconcat M₁ M₂` go from an accepting state of `M₁`
(on the left) to the start state of `M₂` (on the right), and states on the right
have no ε-transitions at all.  Hence the ε-closure of a set `S` adds at most the
single state `Sum.inr M₂.start`, and does so exactly when `S` meets the accepting
states of `M₁`. -/

theorem mem_εconcat_εClosure_iff {S : Set (σ₁ ⊕ σ₂)} {s : σ₁ ⊕ σ₂} :
    s ∈ (εconcat M₁ M₂).εClosure S ↔
      s ∈ S ∨ (s = Sum.inr M₂.start ∧ ∃ p, Sum.inl p ∈ S ∧ p ∈ M₁.accept) := by
  constructor
  · intro h
    induction h with
    | base t ht => exact Or.inl ht
    | step t u hu _hclos ih =>
        cases t with
        | inl p =>
            rw [εconcat_step_inl_none] at hu
            by_cases hp : p ∈ M₁.accept
            · rw [if_pos hp, Set.mem_singleton_iff] at hu
              subst hu
              rcases ih with hS | ⟨hbad, -⟩
              · exact Or.inr ⟨rfl, p, hS, hp⟩
              · exact absurd hbad (by simp)
            · rw [if_neg hp] at hu
              exact absurd hu (Set.not_mem_empty _)
        | inr q =>
            rw [εconcat_step_inr_none] at hu
            exact absurd hu (Set.not_mem_empty _)
  · rintro (hS | ⟨rfl, p, hpS, hp⟩)
    · exact εNFA.εClosure.base _ hS
    · refine εNFA.εClosure.step (Sum.inl p) _ ?_ (εNFA.εClosure.base _ hpS)
      rw [εconcat_step_inl_none, if_pos hp]
      rfl

/-! ### Exact description of the reachable set

After reading `x`, the machine is in the (unique) state `M₁` would be in, together
with one `M₂`-state for every way of splitting `x` as `u ++ v` with `u` accepted
by `M₁`. -/

theorem mem_εconcat_eval_iff (x : List α) :
    ∀ s : σ₁ ⊕ σ₂,
      s ∈ (εconcat M₁ M₂).eval x ↔
        s = Sum.inl (M₁.eval x) ∨
        ∃ u v : List α, u ++ v = x ∧ M₁.eval u ∈ M₁.accept ∧ s = Sum.inr (M₂.eval v) := by
  refine List.reverseRecOn x ?_ ?_
  -- Base case: the empty word.
  · intro s
    rw [εNFA.eval_nil, mem_εconcat_εClosure_iff, εconcat_start]
    constructor
    · rintro (hs | ⟨rfl, r, hr, hracc⟩)
      · rw [Set.mem_insert_iff] at hs
        rcases hs with rfl | hs
        · exact Or.inl rfl
        · by_cases hc : M₁.start ∈ M₁.accept
          · rw [if_pos hc, Set.mem_singleton_iff] at hs
            exact Or.inr ⟨[], [], rfl, hc, hs⟩
          · rw [if_neg hc] at hs
            exact absurd hs (Set.not_mem_empty _)
      · have hrs : r = M₁.start := by
          rw [Set.mem_insert_iff] at hr
          rcases hr with h | h
          · exact Sum.inl.inj h
          · by_cases hc : M₁.start ∈ M₁.accept
            · rw [if_pos hc, Set.mem_singleton_iff] at h
              exact absurd h (by simp)
            · rw [if_neg hc] at h
              exact absurd h (Set.not_mem_empty _)
        subst hrs
        exact Or.inr ⟨[], [], rfl, hracc, rfl⟩
    · rintro (rfl | ⟨u, v, huv, hu, rfl⟩)
      · exact Or.inl (Set.mem_insert _ _)
      · obtain ⟨rfl, rfl⟩ : u = [] ∧ v = [] := by simpa using huv
        exact Or.inr ⟨rfl, M₁.start, Set.mem_insert _ _, hu⟩
  -- Inductive step: reading one more letter.
  · intro l a ih s
    rw [εNFA.eval_append_singleton, εNFA.mem_stepSet_iff]
    constructor
    · rintro ⟨t, ht, hs⟩
      rcases (ih t).mp ht with rfl | ⟨u, v, huv, hu, rfl⟩
      · -- we were tracking `M₁`
        rw [εconcat_step_inl_some, mem_εconcat_εClosure_iff] at hs
        rcases hs with hs | ⟨rfl, r, hr, hracc⟩
        · rw [Set.mem_singleton_iff] at hs
          exact Or.inl (by rw [hs, eval_snoc])
        · -- a fresh ε-jump into `M₂`: the whole word is a prefix accepted by `M₁`
          rw [Set.mem_singleton_iff] at hr
          have hreq : r = M₁.eval (l ++ [a]) := by
            rw [eval_snoc]; exact Sum.inl.inj hr
          subst hreq
          exact Or.inr ⟨l ++ [a], [], by simp, hracc, rfl⟩
      · -- we were tracking `M₂` on the suffix `v`
        rw [εconcat_step_inr_some, mem_εconcat_εClosure_iff] at hs
        rcases hs with hs | ⟨-, r, hr, -⟩
        · rw [Set.mem_singleton_iff] at hs
          refine Or.inr ⟨u, v ++ [a], by rw [← List.append_assoc, huv], hu, ?_⟩
          rw [hs, eval_snoc]
        · rw [Set.mem_singleton_iff] at hr
          exact absurd hr (by simp)
    · rintro (rfl | ⟨u, v, huv, hu, rfl⟩)
      · refine ⟨Sum.inl (M₁.eval l), (ih _).mpr (Or.inl rfl), ?_⟩
        rw [εconcat_step_inl_some, mem_εconcat_εClosure_iff]
        left
        rw [Set.mem_singleton_iff, eval_snoc]
      · rcases eq_nil_or_snoc v with rfl | ⟨v', b, rfl⟩
        · -- the split puts the new letter in the `M₁` part: use the ε-jump
          have hu' : u = l ++ [a] := by simpa using huv
          subst hu'
          refine ⟨Sum.inl (M₁.eval l), (ih _).mpr (Or.inl rfl), ?_⟩
          rw [εconcat_step_inl_some, mem_εconcat_εClosure_iff]
          right
          refine ⟨rfl, M₁.step (M₁.eval l) a, rfl, ?_⟩
          rw [← eval_snoc]
          exact hu
        · -- the split puts the new letter in the `M₂` part: use an `inr` step
          have hsplit : u ++ v' = l ∧ b = a := by
            have h1 : (u ++ v') ++ [b] = l ++ [a] := by
              rw [List.append_assoc]; exact huv
            have h2 := List.append_inj' h1 rfl
            exact ⟨h2.1, by simpa using h2.2⟩
          obtain ⟨hl, rfl⟩ := hsplit
          refine ⟨Sum.inr (M₂.eval v'), (ih _).mpr (Or.inr ⟨u, v', hl, hu, rfl⟩), ?_⟩
          rw [εconcat_step_inr_some, mem_εconcat_εClosure_iff]
          left
          rw [Set.mem_singleton_iff, eval_snoc]

end

/-! ### The main theorem -/

theorem accepts1 (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (εconcat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext x
  simp only [εNFA.accepts, Set.mem_setOf_eq]
  constructor
  · rintro ⟨S, hS, hx⟩
    rw [εconcat_accept] at hS
    obtain ⟨t, ht, rfl⟩ := hS
    rcases (mem_εconcat_eval_iff M₁ M₂ x _).mp hx with hbad | ⟨u, v, huv, hu, heq⟩
    · exact absurd hbad (by simp)
    · have htv : t = M₂.eval v := Sum.inr.inj heq
      subst htv
      have hu' : u ∈ M₁.accepts := hu
      have hv' : v ∈ M₂.accepts := ht
      rw [Language.mem_mul]
      exact ⟨u, hu', v, hv', huv⟩
  · intro hx
    rw [Language.mem_mul] at hx
    obtain ⟨u, hu, v, hv, huv⟩ := hx
    refine ⟨Sum.inr (M₂.eval v), ?_, ?_⟩
    · rw [εconcat_accept]
      exact ⟨M₂.eval v, hv, rfl⟩
    · exact (mem_εconcat_eval_iff M₁ M₂ x _).mpr (Or.inr ⟨u, v, huv, hu, rfl⟩)

end DFA
#print axioms DFA.accepts1
/-Unknown constant `Set.not_mem_empty`
Error code: lean.unknownIdentifier
View explanation
Unknown constant `Set.not_mem_empty`
Error code: lean.unknownIdentifier
View explanation
Unknown constant `Set.not_mem_empty`
Error code: lean.unknownIdentifier
View explanation
Unknown constant `Set.not_mem_empty`
Error code: lean.unknownIdentifier
View explanation-/
