import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.Language

open Classical

universe u v

namespace DFA

variable {α : Type u} {σ₁ σ₂ : Type v}
#count_heartbeats in --141
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
#count_heartbeats in --30
@[simp] theorem step_inl_some (s₁ : σ₁) (c : α) :
    (εconcat M₁ M₂).step (Sum.inl s₁) (some c) = {Sum.inl (M₁.step s₁ c)} := rfl
#count_heartbeats in --49
@[simp] theorem step_inl_none (s₁ : σ₁) :
    (εconcat M₁ M₂).step (Sum.inl s₁) none
      = if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅ := rfl
#count_heartbeats in --29
@[simp] theorem step_inr_some (s₂ : σ₂) (c : α) :
    (εconcat M₁ M₂).step (Sum.inr s₂) (some c) = {Sum.inr (M₂.step s₂ c)} := rfl
#count_heartbeats in --26
@[simp] theorem step_inr_none (s₂ : σ₂) :
    (εconcat M₁ M₂).step (Sum.inr s₂) none = (∅ : Set (σ₁ ⊕ σ₂)) := rfl
#count_heartbeats in --46
theorem start_def :
    (εconcat M₁ M₂).start
      = insert (Sum.inl M₁.start)
          (if M₁.start ∈ M₁.accept then ({Sum.inr M₂.start} : Set (σ₁ ⊕ σ₂)) else ∅) := rfl
#count_heartbeats in --19
theorem accept_def :
    (εconcat M₁ M₂).accept = Sum.inr '' M₂.accept := rfl
#count_heartbeats in --12
theorem reduceOption_map_some (x : List α) : (x.map some).reduceOption = x := by
  induction x with
  | nil => rfl
  | cons a x ih => rw [List.map_cons, List.reduceOption_cons_of_some, ih]
#count_heartbeats in --19
theorem inr_build (x : List α) (s₂ : σ₂) :
    (εconcat M₁ M₂).IsPath (Sum.inr s₂) (Sum.inr (M₂.evalFrom s₂ x)) (x.map some) := by
  induction x generalizing s₂ with
  | nil => exact εNFA.IsPath.nil (Sum.inr s₂)
  | cons c x ih =>
    apply εNFA.IsPath.cons (Sum.inr (M₂.step s₂ c))
    · simp
    · simpa [DFA.evalFrom_cons] using ih (M₂.step s₂ c)
#count_heartbeats in --19
theorem inl_build (x : List α) (s₁ : σ₁) :
    (εconcat M₁ M₂).IsPath (Sum.inl s₁) (Sum.inl (M₁.evalFrom s₁ x)) (x.map some) := by
  induction x generalizing s₁ with
  | nil => exact εNFA.IsPath.nil (Sum.inl s₁)
  | cons c x ih =>
    apply εNFA.IsPath.cons (Sum.inl (M₁.step s₁ c))
    · simp
    · simpa [DFA.evalFrom_cons] using ih (M₁.step s₁ c)
#count_heartbeats in --24
theorem inr_analyze (w : List (Option α)) (s₂ : σ₂) (q : σ₁ ⊕ σ₂)
    (h : (εconcat M₁ M₂).IsPath (Sum.inr s₂) q w) :
    q = Sum.inr (M₂.evalFrom s₂ w.reduceOption) := by
  induction w generalizing s₂ with
  | nil =>
    rw [εNFA.isPath_nil] at h
    subst h; rfl
  | cons a w ih =>
    cases h with
    | cons t _ _ _ _ hmem hrest =>
      cases a with
      | none =>
        simp only [step_inr_none, Set.mem_empty_iff_false] at hmem
      | some c =>
        simp only [step_inr_some, Set.mem_singleton_iff] at hmem
        subst hmem
        rw [List.reduceOption_cons_of_some, DFA.evalFrom_cons]
        exact ih (M₂.step s₂ c) hrest
#count_heartbeats in --47
theorem cross_build (x₁ x₂ : List α) (s₁ : σ₁)
    (h : M₁.evalFrom s₁ x₁ ∈ M₁.accept) :
    (εconcat M₁ M₂).IsPath (Sum.inl s₁) (Sum.inr (M₂.evalFrom M₂.start x₂))
      (x₁.map some ++ none :: x₂.map some) := by
  rw [εNFA.isPath_append]
  refine ⟨Sum.inl (M₁.evalFrom s₁ x₁), inl_build M₁ M₂ x₁ s₁, ?_⟩
  apply εNFA.IsPath.cons (Sum.inr M₂.start)
  · simp only [step_inl_none]
    rw [if_pos h]
    exact Set.mem_singleton _
  · exact inr_build M₁ M₂ x₂ M₂.start
#count_heartbeats in --46
theorem inl_analyze (w : List (Option α)) (s₁ : σ₁) (f : σ₂)
    (h : (εconcat M₁ M₂).IsPath (Sum.inl s₁) (Sum.inr f) w) :
    ∃ x₁ x₂, w.reduceOption = x₁ ++ x₂ ∧ M₁.evalFrom s₁ x₁ ∈ M₁.accept ∧
      M₂.evalFrom M₂.start x₂ = f := by
  induction w generalizing s₁ with
  | nil =>
    rw [εNFA.isPath_nil] at h
    exact absurd h (by simp)
  | cons a w ih =>
    cases h with
    | cons t _ _ _ _ hmem hrest =>
      cases a with
      | some c =>
        simp only [step_inl_some, Set.mem_singleton_iff] at hmem
        subst hmem
        obtain ⟨x₁, x₂, hre, hacc, hev⟩ := ih (M₁.step s₁ c) hrest
        exact ⟨c :: x₁, x₂, by rw [List.reduceOption_cons_of_some, hre]; rfl,
          by rw [DFA.evalFrom_cons]; exact hacc, hev⟩
      | none =>
        simp only [step_inl_none] at hmem
        by_cases hc : s₁ ∈ M₁.accept
        · rw [if_pos hc, Set.mem_singleton_iff] at hmem
          subst hmem
          have hq := inr_analyze M₁ M₂ w M₂.start (Sum.inr f) hrest
          rw [Sum.inr.injEq] at hq
          exact ⟨[], w.reduceOption, by rw [List.reduceOption_cons_of_none]; rfl,
            by simpa using hc, hq.symm⟩
        · rw [if_neg hc] at hmem
          exact absurd hmem (by simp)

end εconcat

end DFA

open DFA

variable {α : Type u} {σ₁ σ₂ : Type v}
#count_heartbeats in -- 22 heartbeats
theorem accepts (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (εconcat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext x
  rw [εNFA.mem_accepts_iff_exists_path, Language.mem_mul]
  constructor
  · rintro ⟨s₁, s₂, w, hstart, haccept, hre, hpath⟩
    rw [DFA.εconcat.accept_def] at haccept
    obtain ⟨f, hf, rfl⟩ := haccept
    rw [DFA.εconcat.start_def] at hstart
    simp only [Set.mem_insert_iff] at hstart
    rcases hstart with hstart | hstart
    · subst hstart
      obtain ⟨x₁, x₂, hre2, hacc, hev⟩ := DFA.εconcat.inl_analyze M₁ M₂ w M₁.start f hpath
      refine ⟨x₁, ?_, x₂, ?_, ?_⟩
      · exact hacc
      · rw [DFA.mem_accepts, DFA.eval, hev]; exact hf
      · rw [← hre, hre2]
    · by_cases hc : M₁.start ∈ M₁.accept
      · rw [if_pos hc, Set.mem_singleton_iff] at hstart
        subst hstart
        have hq := DFA.εconcat.inr_analyze M₁ M₂ w M₂.start (Sum.inr f) hpath
        rw [Sum.inr.injEq] at hq
        refine ⟨[], ?_, x, ?_, ?_⟩
        · rw [DFA.mem_accepts, DFA.eval, DFA.evalFrom_nil]; exact hc
        · rw [DFA.mem_accepts, DFA.eval, ← hre, ← hq]; exact hf
        · simp
      · rw [if_neg hc] at hstart
        exact absurd hstart (by simp)
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨Sum.inl M₁.start, Sum.inr (M₂.evalFrom M₂.start b),
      a.map some ++ none :: b.map some, ?_, ?_, ?_, ?_⟩
    · rw [DFA.εconcat.start_def]; simp
    · rw [DFA.εconcat.accept_def]; exact ⟨M₂.evalFrom M₂.start b, hb, rfl⟩
    · rw [List.reduceOption_append, List.reduceOption_cons_of_none,
        DFA.εconcat.reduceOption_map_some, DFA.εconcat.reduceOption_map_some]
    · apply DFA.εconcat.cross_build M₁ M₂ a b M₁.start
      rw [DFA.mem_accepts, DFA.eval] at ha
      exact ha
#print axioms accepts
--[propext, choice, Quot.sound]
