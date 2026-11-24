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

variable {M₁ : DFA α σ₁} {M₂ : DFA α σ₂}
#count_heartbeats in --48
lemma append_eq_cons_iff {α} (a : α) (as : List α) (w₁ w₂ : List α) :
    w₁ ++ w₂ = a :: as ↔
    (w₁ = [] ∧ w₂ = a :: as) ∨ (∃ w₁', w₁ = a :: w₁' ∧ w₁' ++ w₂ = as) := by
  cases w₁ <;> simp
#count_heartbeats in --78
lemma εClosure_inr_eq (s₂ : σ₂) (x : σ₁ ⊕ σ₂) :
    (εconcat M₁ M₂).εClosure (Sum.inr s₂) x ↔ x = Sum.inr s₂ := by
  constructor
  · intro h
    generalize hy : Sum.inr s₂ = y at h
    induction h with
    | refl s => exact hy.symm
    | step s1 s2 s3 hstep h2 ih =>
      subst hy
      change s2 ∈ (εconcat M₁ M₂).step (Sum.inr s₂) none at hstep
      dsimp [εconcat] at hstep
      cases hstep
  · rintro rfl; exact εNFA.εClosure.refl _
#count_heartbeats in --89
lemma εClosure_inl_eq (s₁ : σ₁) (x : σ₁ ⊕ σ₂) :
    (εconcat M₁ M₂).εClosure (Sum.inl s₁) x ↔
    x = Sum.inl s₁ ∨ (s₁ ∈ M₁.accept ∧ x = Sum.inr M₂.start) := by
  constructor
  · intro h
    generalize hy : Sum.inl s₁ = y at h
    induction h with
    | refl s =>
      subst hy
      exact Or.inl rfl
    | step a b c hstep hc ih =>
      subst hy
      change b ∈ (εconcat M₁ M₂).step (Sum.inl s₁) none at hstep
      dsimp [εconcat] at hstep
      by_cases h_acc : s₁ ∈ M₁.accept
      · rw [if_pos h_acc] at hstep
        have hb : b = Sum.inr M₂.start := hstep
        subst hb
        rw [εClosure_inr_eq] at hc
        exact Or.inr ⟨h_acc, hc⟩
      · rw [if_neg h_acc] at hstep
        cases hstep
  · rintro (rfl | ⟨h1, rfl⟩)
    · exact εNFA.εClosure.refl _
    · apply εNFA.εClosure.step (s₂ := Sum.inr M₂.start)
      · change _ ∈ (εconcat M₁ M₂).step (Sum.inl s₁) none
        dsimp [εconcat]
        rw [if_pos h1]
        exact Set.mem_singleton _
      · exact εNFA.εClosure.refl _
#count_heartbeats in --76
lemma εClosureSet_inl (s₁ : σ₁) :
    (εconcat M₁ M₂).εClosureSet {Sum.inl s₁} =
    if s₁ ∈ M₁.accept then {Sum.inl s₁, Sum.inr M₂.start} else {Sum.inl s₁} := by
  ext x
  by_cases h : s₁ ∈ M₁.accept <;> simp [h, εNFA.εClosureSet, εClosure_inl_eq]
#count_heartbeats in --27
lemma εClosureSet_inr (s₂ : σ₂) :
    (εconcat M₁ M₂).εClosureSet {Sum.inr s₂} = {Sum.inr s₂} := by
  ext x
  simp [εNFA.εClosureSet, εClosure_inr_eq]
#count_heartbeats in --33
lemma εClosureSet_union (S T : Set (σ₁ ⊕ σ₂)) :
    (εconcat M₁ M₂).εClosureSet (S ∪ T) =
    (εconcat M₁ M₂).εClosureSet S ∪ (εconcat M₁ M₂).εClosureSet T := by
  ext x
  simp [εNFA.εClosureSet, or_and_right, exists_or]
#count_heartbeats in --13
lemma start_eq :
    (εconcat M₁ M₂).start = (εconcat M₁ M₂).εClosureSet {Sum.inl M₁.start} := by
  ext x
  by_cases h : M₁.start ∈ M₁.accept <;> simp [h, εconcat, εClosureSet_inl] <;> aesop
#count_heartbeats in --64
lemma stepSet_inl (s₁ : σ₁) (a : α) :
    (εconcat M₁ M₂).stepSet {Sum.inl s₁} a =
    if (M₁.step s₁ a) ∈ M₁.accept then {Sum.inl (M₁.step s₁ a), Sum.inr M₂.start}
    else {Sum.inl (M₁.step s₁ a)} := by
  dsimp [εNFA.stepSet]
  have : (⋃ s ∈ ({Sum.inl s₁} : Set (σ₁ ⊕ σ₂)), (εconcat M₁ M₂).step s (some a)) =
         {Sum.inl (M₁.step s₁ a)} := by ext x; simp [εconcat]
  rw [this]
  apply εClosureSet_inl
#count_heartbeats in --27
lemma stepSet_inr (s₂ : σ₂) (a : α) :
    (εconcat M₁ M₂).stepSet {Sum.inr s₂} a = {Sum.inr (M₂.step s₂ a)} := by
  dsimp [εNFA.stepSet]
  have : (⋃ s ∈ ({Sum.inr s₂} : Set (σ₁ ⊕ σ₂)), (εconcat M₁ M₂).step s (some a)) =
         {Sum.inr (M₂.step s₂ a)} := by ext x; simp [εconcat]
  rw [this]
  apply εClosureSet_inr
#count_heartbeats in --32
lemma stepSet_union (S T : Set (σ₁ ⊕ σ₂)) (a : α) :
    (εconcat M₁ M₂).stepSet (S ∪ T) a =
    (εconcat M₁ M₂).stepSet S a ∪ (εconcat M₁ M₂).stepSet T a := by
  dsimp [εNFA.stepSet]
  have : (⋃ s ∈ S ∪ T, (εconcat M₁ M₂).step s (some a)) =
         (⋃ s ∈ S, (εconcat M₁ M₂).step s (some a)) ∪
         (⋃ s ∈ T, (εconcat M₁ M₂).step s (some a)) := by
    ext x; simp [or_and_right, exists_or]
  rw [this, εClosureSet_union]
#count_heartbeats in --27
lemma εClosureSet_StateSet (s₁ : σ₁) (Q₂ : Set σ₂) :
    (εconcat M₁ M₂).εClosureSet ((εconcat M₁ M₂).εClosureSet {Sum.inl s₁} ∪ Sum.inr '' Q₂) =
    (εconcat M₁ M₂).εClosureSet {Sum.inl s₁} ∪ Sum.inr '' Q₂ := by
  rw [εClosureSet_union]
  have h2 : (εconcat M₁ M₂).εClosureSet (Sum.inr '' Q₂) = Sum.inr '' Q₂ := by
    ext x; simp [εNFA.εClosureSet, εClosure_inr_eq]
  rw [h2]
  have h1 : (εconcat M₁ M₂).εClosureSet ((εconcat M₁ M₂).εClosureSet {Sum.inl s₁}) =
            (εconcat M₁ M₂).εClosureSet {Sum.inl s₁} := by
    rw [εClosureSet_inl]
    by_cases h : s₁ ∈ M₁.accept
    · rw [if_pos h]
      have : ({Sum.inl s₁, Sum.inr M₂.start} : Set (σ₁ ⊕ σ₂)) = {Sum.inl s₁} ∪ {Sum.inr M₂.start} := by ext; simp
      rw [this, εClosureSet_union, εClosureSet_inl, εClosureSet_inr, if_pos h]
      ext; simp
    · rw [if_neg h]
  rw [h1]
#count_heartbeats in --79
lemma stepSet_StateSet_eq (s₁ : σ₁) (Q₂ : Set σ₂) (a : α) :
    (εconcat M₁ M₂).stepSet ((εconcat M₁ M₂).εClosureSet {Sum.inl s₁} ∪ Sum.inr '' Q₂) a =
    (εconcat M₁ M₂).εClosureSet {Sum.inl (M₁.step s₁ a)} ∪
    Sum.inr '' (M₂.step '' Q₂ ∪ if s₁ ∈ M₁.accept then {M₂.step M₂.start a} else ∅) := by
  rw [stepSet_union]
  have h1 : (εconcat M₁ M₂).stepSet ((εconcat M₁ M₂).εClosureSet {Sum.inl s₁}) a =
            (εconcat M₁ M₂).εClosureSet {Sum.inl (M₁.step s₁ a)} ∪
            Sum.inr '' (if s₁ ∈ M₁.accept then {M₂.step M₂.start a} else ∅) := by
    rw [εClosureSet_inl]
    by_cases h : s₁ ∈ M₁.accept
    · rw [if_pos h, if_pos h]
      have : ({Sum.inl s₁, Sum.inr M₂.start} : Set (σ₁ ⊕ σ₂)) = {Sum.inl s₁} ∪ {Sum.inr M₂.start} := by ext; simp
      rw [this, stepSet_union, stepSet_inl, stepSet_inr]
      ext; simp
    · rw [if_neg h, if_neg h]
      have : Sum.inr '' ∅ = (∅ : Set (σ₁ ⊕ σ₂)) := Set.image_empty _
      rw [this, Set.union_empty, stepSet_inl]
  have h2 : (εconcat M₁ M₂).stepSet (Sum.inr '' Q₂) a = Sum.inr '' (M₂.step '' Q₂) := by
    dsimp [εNFA.stepSet]
    have : (⋃ s ∈ Sum.inr '' Q₂, (εconcat M₁ M₂).step s (some a)) = Sum.inr '' (M₂.step '' Q₂) := by
      ext x; simp [εconcat]
    rw [this]
    ext x; simp [εNFA.εClosureSet, εClosure_inr_eq]
  rw [h1, h2, Set.image_union]
  ext; simp; tauto
#count_heartbeats in --202
lemma evalFrom_StateSet_step_eq (s₁ : σ₁) (Q₂ : Set σ₂) (a : α) (as : List α) :
    ((fun q => M₂.evalFrom q as) '' (M₂.step '' Q₂ ∪ if s₁ ∈ M₁.accept then {M₂.step M₂.start a} else ∅)) ∪
    {s₂ | ∃ w₁ w₂, w₁ ++ w₂ = as ∧ M₁.evalFrom (M₁.step s₁ a) w₁ ∈ M₁.accept ∧ M₂.evalFrom M₂.start w₂ = s₂} =
    ((fun q => M₂.evalFrom q (a :: as)) '' Q₂) ∪
    {s₂ | ∃ w₁ w₂, w₁ ++ w₂ = a :: as ∧ M₁.evalFrom s₁ w₁ ∈ M₁.accept ∧ M₂.evalFrom M₂.start w₂ = s₂} := by
  ext x
  simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq, append_eq_cons_iff, Set.mem_ite_empty_right, Set.mem_singleton_iff]
  constructor
  · rintro (⟨q', hq', rfl⟩ | ⟨w₁, w₂, rfl, hacc, rfl⟩)
    · rcases hq' with ⟨q, hq, rfl⟩ | ⟨hacc, rfl⟩
      · left; exact ⟨q, hq, rfl⟩
      · right; right; use [], (a :: as)
        simp [hacc]
    · right; right; use (a :: w₁), w₂
      simp [hacc]
  · rintro (⟨q, hq, rfl⟩ | ⟨w₁, w₂, hw, hacc, rfl⟩)
    · left; left; use M₂.step q a; exact ⟨⟨q, hq, rfl⟩, rfl⟩
    · rcases hw with ⟨rfl, rfl⟩ | ⟨w₁', rfl, rfl⟩
      · left; right; exact ⟨hacc, rfl⟩
      · right; use w₁', w₂; exact ⟨rfl, hacc, rfl⟩
#count_heartbeats in --75
lemma evalFrom_StateSet (s₁ : σ₁) (Q₂ : Set σ₂) (w : List α) :
    (εconcat M₁ M₂).evalFrom ((εconcat M₁ M₂).εClosureSet {Sum.inl s₁} ∪ Sum.inr '' Q₂) w =
    (εconcat M₁ M₂).εClosureSet {Sum.inl (M₁.evalFrom s₁ w)} ∪
    Sum.inr '' (
      ((fun q => M₂.evalFrom q w) '' Q₂) ∪
      {s₂ | ∃ w₁ w₂, w₁ ++ w₂ = w ∧ M₁.evalFrom s₁ w₁ ∈ M₁.accept ∧ M₂.evalFrom M₂.start w₂ = s₂}
    ) := by
  induction w generalizing s₁ Q₂ with
  | nil =>
    simp only [εNFA.evalFrom_nil, DFA.evalFrom, Set.image_id']
    have h_set : {s₂ | ∃ w₁ w₂, w₁ ++ w₂ = [] ∧ M₁.evalFrom s₁ w₁ ∈ M₁.accept ∧ M₂.evalFrom M₂.start w₂ = s₂} =
                 if s₁ ∈ M₁.accept then {M₂.start} else ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_ite_empty_right, Set.mem_singleton_iff]
      constructor
      · rintro ⟨w₁, w₂, hw, h_acc, rfl⟩
        have h_nil := List.append_eq_nil_iff.mp hw
        rcases h_nil with ⟨rfl, rfl⟩
        exact ⟨h_acc, rfl⟩
      · rintro ⟨h_acc, rfl⟩
        exact ⟨[], [], rfl, h_acc, rfl⟩
    rw [h_set]
    have h_eval : (fun q => q) '' Q₂ = Q₂ := Set.image_id
    rw [h_eval]
    have h_union : Q₂ ∪ (if s₁ ∈ M₁.accept then {M₂.start} else ∅) =
                   if s₁ ∈ M₁.accept then (Q₂ ∪ {M₂.start}) else Q₂ := by
      by_cases h : s₁ ∈ M₁.accept <;> simp [h]
    rw [h_union]
    ext x
    by_cases h : s₁ ∈ M₁.accept
    · rw [if_pos h]
      simp only [εClosureSet_inl, if_pos h, Set.image_union, Set.image_singleton]
      have : ({Sum.inl s₁, Sum.inr M₂.start} : Set (σ₁ ⊕ σ₂)) = {Sum.inl s₁} ∪ {Sum.inr M₂.start} := by ext; simp
      rw [this]
      ext y; simp; tauto
    · rw [if_neg h]
      simp only [εClosureSet_inl, if_neg h]
      rw [εClosureSet_StateSet]
  | cons a as ih =>
    rw [εNFA.evalFrom_cons, εClosureSet_StateSet, stepSet_StateSet_eq]
    rw [ih]
    have h_dfa1 : M₁.evalFrom s₁ (a :: as) = M₁.evalFrom (M₁.step s₁ a) as := rfl
    rw [h_dfa1]
    have h_inner := evalFrom_StateSet_step_eq s₁ Q₂ a as
    rw [h_inner]
#count_heartbeats in -- 24 heartbeats
theorem accepts1  (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (εconcat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext w
  simp only [εNFA.accepts, DFA.accepts, Set.mem_mul, Set.mem_image, Set.mem_setOf_eq]
  have h_start : (εconcat M₁ M₂).start = (εconcat M₁ M₂).εClosureSet {Sum.inl M₁.start} ∪ Sum.inr '' ∅ := by
    rw [Set.image_empty, Set.union_empty, start_eq]
  rw [h_start, evalFrom_StateSet]
  constructor
  · rintro ⟨S, hS, h_acc⟩
    rcases h_acc with ⟨s_acc, hs_acc, rfl⟩
    rcases hS with h_inl | h_inr
    · by_cases h : M₁.evalFrom M₁.start w ∈ M₁.accept
      · rw [εClosureSet_inl, if_pos h] at h_inl
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_inl
        rcases h_inl with h_inl | h_inl
        · cases h_inl
        · cases h_inl
          use w, []
          simp [h, hs_acc]
      · rw [εClosureSet_inl, if_neg h] at h_inl
        simp only [Set.mem_singleton_iff] at h_inl
        cases h_inl
    · rcases h_inr with ⟨s₂, hs₂, hs_eq⟩
      cases hs_eq
      cases hs₂
      · contradiction
      · rcases ‹s_acc ∈ {s₂ | _}› with ⟨w₁, w₂, hw, h1, h2⟩
        use w₁, w₂
        exact ⟨hw, h1, h2 ▸ hs_acc⟩
  · rintro ⟨w₁, w₂, hw, h1, h2⟩
    use Sum.inr (M₂.evalFrom M₂.start w₂)
    constructor
    · right
      use M₂.evalFrom M₂.start w₂
      constructor
      · right
        use w₁, w₂
        exact ⟨hw, h1, rfl⟩
      · rfl
    · use M₂.evalFrom M₂.start w₂
      exact ⟨h2, rfl⟩

end DFA

#print axioms DFA.accepts1
--'DFA.accepts1' depends on axioms: [propext, sorryAx, choice, Quot.sound]
