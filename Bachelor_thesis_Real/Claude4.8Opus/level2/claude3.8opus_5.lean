/-
  Concatenation of two DFAs via an ε-NFA.

  The construction `DFA.εconcat` is given verbatim as specified; everything below
  it is the proof that it recognises the concatenation of the two languages.

  Note on namespacing: `DFA.accepts` already exists in Mathlib (the acceptance
  language of a DFA), so the final theorem lives in the `DFA.εconcat` namespace
  to avoid a name clash.  Its statement is exactly as requested.
-/

import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.Language

open Classical

universe u v

namespace DFA

variable {α : Type u} {σ₁ σ₂ : Type v}

/-- The ε-NFA obtained by gluing `M₂` onto the accepting states of `M₁`. -/
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

namespace εconcat

variable (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)

/-! ### Unfolding lemmas for the construction -/

@[simp]
lemma step_inl_some (s : σ₁) (c : α) :
    (εconcat M₁ M₂).step (Sum.inl s) (some c) = {Sum.inl (M₁.step s c)} := rfl

@[simp]
lemma step_inr_some (s : σ₂) (c : α) :
    (εconcat M₁ M₂).step (Sum.inr s) (some c) = {Sum.inr (M₂.step s c)} := rfl

@[simp]
lemma step_inl_none (s : σ₁) :
    (εconcat M₁ M₂).step (Sum.inl s) none =
      if s ∈ M₁.accept then {Sum.inr M₂.start} else ∅ := rfl

@[simp]
lemma step_inr_none (s : σ₂) :
    (εconcat M₁ M₂).step (Sum.inr s) none = (∅ : Set (σ₁ ⊕ σ₂)) := rfl

@[simp]
lemma start_def :
    (εconcat M₁ M₂).start =
      insert (Sum.inl M₁.start)
        (if M₁.start ∈ M₁.accept then ({Sum.inr M₂.start} : Set (σ₁ ⊕ σ₂)) else ∅) := rfl

/-! ### The ε-closure

The only ε-transitions available run from an accepting state of `M₁` to the start
state of `M₂`, and no ε-transition leaves the right-hand component.  Hence the
ε-closure of a set `S` adds at most the single state `Sum.inr M₂.start`. -/

lemma mem_εClosure_iff {S : Set (σ₁ ⊕ σ₂)} {s : σ₁ ⊕ σ₂} :
    s ∈ (εconcat M₁ M₂).εClosure S ↔
      s ∈ S ∨ (s = Sum.inr M₂.start ∧ ∃ t ∈ M₁.accept, Sum.inl t ∈ S) := by
  constructor
  · intro h
    induction h with
    | base p hp => exact Or.inl hp
    | step p q hq _ ih =>
        cases p with
        | inl p₁ =>
            rw [step_inl_none] at hq
            split_ifs at hq with hp
            · rw [Set.mem_singleton_iff] at hq
              subst hq
              rcases ih with h' | ⟨h', -⟩
              · exact Or.inr ⟨rfl, p₁, hp, h'⟩
              · simp at h'
            · simp at hq
        | inr p₂ =>
            rw [step_inr_none] at hq
            simp at hq
  · rintro (hs | ⟨rfl, t, ht, hts⟩)
    · exact εNFA.εClosure.base _ hs
    · have h1 : (Sum.inl t : σ₁ ⊕ σ₂) ∈ (εconcat M₁ M₂).εClosure S :=
        εNFA.εClosure.base _ hts
      have h2 : (Sum.inr M₂.start : σ₁ ⊕ σ₂) ∈
          (εconcat M₁ M₂).step (Sum.inl t) none := by
        rw [step_inl_none, if_pos ht]
        rfl
      exact εNFA.εClosure.step _ _ h2 h1

/-! ### One step of the powerset construction -/

lemma mem_stepSet_inl {T : Set (σ₁ ⊕ σ₂)} {s : σ₁} {a : α} :
    Sum.inl s ∈ (εconcat M₁ M₂).stepSet T a ↔ ∃ p, Sum.inl p ∈ T ∧ M₁.step p a = s := by
  rw [εNFA.mem_stepSet_iff]
  constructor
  · rintro ⟨p, hp, hmem⟩
    rw [mem_εClosure_iff] at hmem
    cases p with
    | inl p₁ =>
        rcases hmem with h | ⟨h, -⟩
        · rw [step_inl_some, Set.mem_singleton_iff] at h
          exact ⟨p₁, hp, (Sum.inl.inj h).symm⟩
        · simp at h
    | inr p₂ =>
        rcases hmem with h | ⟨h, -⟩
        · rw [step_inr_some, Set.mem_singleton_iff] at h
          simp at h
        · simp at h
  · rintro ⟨p, hp, rfl⟩
    refine ⟨Sum.inl p, hp, ?_⟩
    rw [mem_εClosure_iff]
    left
    rw [step_inl_some]
    rfl

lemma mem_stepSet_inr {T : Set (σ₁ ⊕ σ₂)} {r : σ₂} {a : α} :
    Sum.inr r ∈ (εconcat M₁ M₂).stepSet T a ↔
      (∃ p, Sum.inr p ∈ T ∧ M₂.step p a = r) ∨
      (∃ p, Sum.inl p ∈ T ∧ M₁.step p a ∈ M₁.accept ∧ r = M₂.start) := by
  rw [εNFA.mem_stepSet_iff]
  constructor
  · rintro ⟨p, hp, hmem⟩
    rw [mem_εClosure_iff] at hmem
    cases p with
    | inl p₁ =>
        rcases hmem with h | ⟨h, q, hq, hq2⟩
        · rw [step_inl_some, Set.mem_singleton_iff] at h
          simp at h
        · rw [step_inl_some, Set.mem_singleton_iff] at hq2
          refine Or.inr ⟨p₁, hp, ?_, Sum.inr.inj h⟩
          rw [← Sum.inl.inj hq2]
          exact hq
    | inr p₂ =>
        rcases hmem with h | ⟨h, q, hq, hq2⟩
        · rw [step_inr_some, Set.mem_singleton_iff] at h
          exact Or.inl ⟨p₂, hp, (Sum.inr.inj h).symm⟩
        · rw [step_inr_some, Set.mem_singleton_iff] at hq2
          simp at hq2
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, hacc, rfl⟩)
    · refine ⟨Sum.inr p, hp, ?_⟩
      rw [mem_εClosure_iff]
      left
      rw [step_inr_some]
      rfl
    · refine ⟨Sum.inl p, hp, ?_⟩
      rw [mem_εClosure_iff]
      right
      refine ⟨rfl, M₁.step p a, hacc, ?_⟩
      rw [step_inl_some]
      rfl

/-! ### Reachability along a word

These are stated about the raw `List.foldl` underlying `εNFA.evalFrom`, so that
the accumulator can be generalised in the induction.  This avoids needing any
idempotence property of the ε-closure. -/

/-- The left-hand component evolves deterministically, exactly as in `M₁`. -/
lemma mem_foldl_inl (x : List α) (t : σ₁) :
    ∀ T : Set (σ₁ ⊕ σ₂),
      (Sum.inl t ∈ List.foldl (εconcat M₁ M₂).stepSet T x ↔
        ∃ s, Sum.inl s ∈ T ∧ M₁.evalFrom s x = t) := by
  induction x with
  | nil =>
      intro T
      simp only [List.foldl_nil]
      constructor
      · intro h
        exact ⟨t, h, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact hs
  | cons a x ih =>
      intro T
      rw [List.foldl_cons, ih]
      constructor
      · rintro ⟨s, hs, hev⟩
        rw [mem_stepSet_inl] at hs
        obtain ⟨p, hp, rfl⟩ := hs
        exact ⟨p, hp, hev⟩
      · rintro ⟨s, hs, hev⟩
        refine ⟨M₁.step s a, ?_, hev⟩
        rw [mem_stepSet_inl]
        exact ⟨s, hs, rfl⟩

/-- A right-hand state is reachable either because we were already on the right
at the start, or because some *nonempty* prefix drove a left state into
`M₁.accept`, triggering the ε-jump to `M₂.start`.

The prefix must be nonempty because `List.foldl` applies the ε-closure after each
letter but not to the initial accumulator. -/
lemma mem_foldl_inr (x : List α) (t : σ₂) :
    ∀ T : Set (σ₁ ⊕ σ₂),
      (Sum.inr t ∈ List.foldl (εconcat M₁ M₂).stepSet T x ↔
        (∃ r, Sum.inr r ∈ T ∧ M₂.evalFrom r x = t) ∨
        (∃ u v, u ++ v = x ∧ u ≠ [] ∧ ∃ s, Sum.inl s ∈ T ∧
          M₁.evalFrom s u ∈ M₁.accept ∧ M₂.evalFrom M₂.start v = t)) := by
  induction x with
  | nil =>
      intro T
      simp only [List.foldl_nil]
      constructor
      · intro h
        exact Or.inl ⟨t, h, rfl⟩
      · rintro (⟨r, hr, hrt⟩ | ⟨u, v, huv, hu, -⟩)
        · rw [← hrt]
          exact hr
        · cases u with
          | nil => exact absurd rfl hu
          | cons b u' => simp at huv
  | cons a x ih =>
      intro T
      rw [List.foldl_cons, ih]
      constructor
      · rintro (⟨r, hr, hev⟩ | ⟨u, v, huv, hu, s, hs, hacc, hev⟩)
        · rw [mem_stepSet_inr] at hr
          rcases hr with ⟨p, hp, rfl⟩ | ⟨p, hp, hacc', rfl⟩
          · exact Or.inl ⟨p, hp, hev⟩
          · exact Or.inr ⟨[a], x, rfl, by simp, p, hp, hacc', hev⟩
        · rw [mem_stepSet_inl] at hs
          obtain ⟨p, hp, rfl⟩ := hs
          refine Or.inr ⟨a :: u, v, ?_, by simp, p, hp, hacc, hev⟩
          rw [List.cons_append, huv]
      · rintro (⟨r, hr, hev⟩ | ⟨u, v, huv, hu, s, hs, hacc, hev⟩)
        · refine Or.inl ⟨M₂.step r a, ?_, hev⟩
          rw [mem_stepSet_inr]
          exact Or.inl ⟨r, hr, rfl⟩
        · cases u with
          | nil => exact absurd rfl hu
          | cons b u' =>
              rw [List.cons_append] at huv
              obtain ⟨rfl, huv'⟩ := List.cons.inj huv
              cases u' with
              | nil =>
                  have hvx : v = x := huv'
                  subst hvx
                  refine Or.inl ⟨M₂.start, ?_, hev⟩
                  rw [mem_stepSet_inr]
                  exact Or.inr ⟨s, hs, hacc, rfl⟩
              | cons c u'' =>
                  refine Or.inr ⟨c :: u'', v, huv', by simp, M₁.step s a, ?_, hacc, hev⟩
                  rw [mem_stepSet_inl]
                  exact ⟨s, hs, rfl⟩

/-! ### The start set and its ε-closure -/

lemma mem_start_inl (s : σ₁) :
    (Sum.inl s : σ₁ ⊕ σ₂) ∈ (εconcat M₁ M₂).start ↔ s = M₁.start := by
  rw [start_def, Set.mem_insert_iff]
  constructor
  · rintro (h | h)
    · exact Sum.inl.inj h
    · split_ifs at h with hs
      · simp at h
      · simp at h
  · rintro rfl
    exact Or.inl rfl

lemma mem_start_inr (r : σ₂) :
    (Sum.inr r : σ₁ ⊕ σ₂) ∈ (εconcat M₁ M₂).start ↔ (r = M₂.start ∧ M₁.start ∈ M₁.accept) := by
  rw [start_def, Set.mem_insert_iff]
  constructor
  · rintro (h | h)
    · simp at h
    · split_ifs at h with hs
      · exact ⟨Sum.inr.inj (Set.mem_singleton_iff.mp h), hs⟩
      · simp at h
  · rintro ⟨rfl, hs⟩
    right
    rw [if_pos hs]
    rfl

lemma mem_εClosure_start_inl (s : σ₁) :
    (Sum.inl s : σ₁ ⊕ σ₂) ∈ (εconcat M₁ M₂).εClosure (εconcat M₁ M₂).start ↔
      s = M₁.start := by
  rw [mem_εClosure_iff, mem_start_inl]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact h
    · simp at h
  · exact fun h => Or.inl h

lemma mem_εClosure_start_inr (r : σ₂) :
    (Sum.inr r : σ₁ ⊕ σ₂) ∈ (εconcat M₁ M₂).εClosure (εconcat M₁ M₂).start ↔
      (r = M₂.start ∧ M₁.start ∈ M₁.accept) := by
  rw [mem_εClosure_iff, mem_start_inr]
  constructor
  · rintro (h | ⟨h, q, hq, hqs⟩)
    · exact h
    · rw [mem_start_inl] at hqs
      subst hqs
      exact ⟨Sum.inr.inj h, hq⟩
  · exact fun h => Or.inl h

/-! ### Reachable right-hand states, from the actual start set

Here the `u = []` case is recovered from the `Sum.inr M₂.start ∈ start` disjunct
built into the construction, so the nonemptiness side condition disappears. -/

lemma mem_eval_inr (x : List α) (t : σ₂) :
    Sum.inr t ∈ (εconcat M₁ M₂).eval x ↔
      ∃ u v, u ++ v = x ∧ M₁.evalFrom M₁.start u ∈ M₁.accept ∧
        M₂.evalFrom M₂.start v = t := by
  have hunfold : Sum.inr t ∈ (εconcat M₁ M₂).eval x ↔
      Sum.inr t ∈ List.foldl (εconcat M₁ M₂).stepSet
        ((εconcat M₁ M₂).εClosure (εconcat M₁ M₂).start) x := Iff.rfl
  rw [hunfold, mem_foldl_inr]
  constructor
  · rintro (⟨r, hr, hev⟩ | ⟨u, v, huv, -, s, hs, hacc, hev⟩)
    · rw [mem_εClosure_start_inr] at hr
      obtain ⟨rfl, hstart⟩ := hr
      exact ⟨[], x, List.nil_append x, hstart, hev⟩
    · rw [mem_εClosure_start_inl] at hs
      subst hs
      exact ⟨u, v, huv, hacc, hev⟩
  · rintro ⟨u, v, huv, hacc, hev⟩
    rcases eq_or_ne u [] with rfl | hune
    · have hvx : v = x := huv
      subst hvx
      refine Or.inl ⟨M₂.start, ?_, hev⟩
      rw [mem_εClosure_start_inr]
      exact ⟨rfl, hacc⟩
    · refine Or.inr ⟨u, v, huv, hune, M₁.start, ?_, hacc, hev⟩
      rw [mem_εClosure_start_inl]

/-! ### The main theorem -/

theorem accepts (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (εconcat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext x
  rw [Language.mem_mul]
  constructor
  · rintro ⟨S, hS, hmem⟩
    obtain ⟨t, ht, rfl⟩ := hS
    rw [mem_eval_inr] at hmem
    obtain ⟨u, v, huv, hacc, hev⟩ := hmem
    refine ⟨u, hacc, v, ?_, huv⟩
    show M₂.evalFrom M₂.start v ∈ M₂.accept
    rw [hev]
    exact ht
  · rintro ⟨u, hu, v, hv, rfl⟩
    show ∃ S ∈ (εconcat M₁ M₂).accept, S ∈ (εconcat M₁ M₂).eval (u ++ v)
    refine ⟨Sum.inr (M₂.evalFrom M₂.start v),
      ⟨M₂.evalFrom M₂.start v, hv, rfl⟩, ?_⟩
    rw [mem_eval_inr]
    exact ⟨u, v, rfl, hu, rfl⟩

end εconcat

end DFA
#print axioms DFA.εconcat.accepts
/-Unknown identifier `a`
Error code: lean.unknownIdentifier line 253-/
