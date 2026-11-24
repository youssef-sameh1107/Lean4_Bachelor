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

lemma εconcat_εClosure_inr (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s₂ : σ₂) :
  (εconcat M₁ M₂).εClosure {Sum.inr s₂} = {Sum.inr s₂} := by
  ext s
  simp only [Set.mem_singleton_iff]
  constructor
  · intro h
    induction h with
    | base s_ h_s =>
      exact h_s
    | step s_ t_ h_step h_closure ih =>
      subst ih
      change t_ ∈ (εconcat M₁ M₂).step (Sum.inr s₂) none at h_step
      dsimp [εconcat] at h_step
      simp at h_step
      contradiction
  · intro h
    subst h
    exact εNFA.εClosure.base _ rfl

lemma εconcat_εClosure_inl (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s₁ : σ₁) :
  (εconcat M₁ M₂).εClosure {Sum.inl s₁} =
    insert (Sum.inl s₁) (if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅) := by
  ext s
  simp only [Set.mem_insert_iff, Set.mem_ite_empty_right, Set.mem_singleton_iff]
  constructor
  · intro h
    induction h with
    | base s_ h_s =>
      simp only [Set.mem_singleton_iff] at h_s
      subst h_s
      exact Or.inl rfl
    | step s_ t_ h_step h_closure ih =>
      rcases ih with rfl | ⟨h_acc, rfl⟩
      · change t_ ∈ (εconcat M₁ M₂).step (Sum.inl s₁) none at h_step
        dsimp [εconcat] at h_step
        split_ifs at h_step with h_acc2
        · simp only [Set.mem_singleton_iff] at h_step
          subst h_step
          exact Or.inr ⟨h_acc2, rfl⟩
        · simp at h_step
          contradiction
      · change t_ ∈ (εconcat M₁ M₂).step (Sum.inr M₂.start) none at h_step
        dsimp [εconcat] at h_step
        simp at h_step
        contradiction
  · intro h
    rcases h with rfl | ⟨h_acc, rfl⟩
    · exact εNFA.εClosure.base _ rfl
    · apply εNFA.εClosure.step (Sum.inl s₁) (Sum.inr M₂.start)
      · change (Sum.inr M₂.start) ∈ (εconcat M₁ M₂).step (Sum.inl s₁) none
        dsimp [εconcat]
        rw [if_pos h_acc]
        exact Set.mem_singleton _
      · apply εNFA.εClosure.base
        exact Set.mem_singleton _

lemma εconcat_εClosure_start (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
  (εconcat M₁ M₂).εClosure (εconcat M₁ M₂).start = (εconcat M₁ M₂).εClosure {Sum.inl M₁.start} := by
  ext s
  constructor
  · intro h
    induction h with
    | base s_ h_s =>
      have h_eq : (εconcat M₁ M₂).start = (εconcat M₁ M₂).εClosure {Sum.inl M₁.start} := by
        rw [εconcat_εClosure_inl]; rfl
      rw [h_eq] at h_s
      exact h_s
    | step s_ t_ h_step h_closure ih =>
      exact εNFA.εClosure.step s_ t_ h_step ih
  · intro h
    induction h with
    | base s_ h_s =>
      apply εNFA.εClosure.base
      have h_eq : (εconcat M₁ M₂).start = (εconcat M₁ M₂).εClosure {Sum.inl M₁.start} := by
        rw [εconcat_εClosure_inl]; rfl
      rw [h_eq]
      exact εNFA.εClosure.base s_ h_s
    | step s_ t_ h_step h_closure ih =>
      exact εNFA.εClosure.step s_ t_ h_step ih

lemma foldl_stepSet_union (M : εNFA α σ) (S T : Set σ) (x : List α) :
  List.foldl M.stepSet (S ∪ T) x = List.foldl M.stepSet S x ∪ List.foldl M.stepSet T x := by
  induction x generalizing S T with
  | nil => rfl
  | cons a x ih =>
    simp only [List.foldl_cons]
    have h_step : M.stepSet (S ∪ T) a = M.stepSet S a ∪ M.stepSet T a := by
      ext s
      simp only [εNFA.mem_stepSet_iff, Set.mem_union]
      constructor
      · rintro ⟨s', hs' | hs', h⟩
        · exact Or.inl ⟨s', hs', h⟩
        · exact Or.inr ⟨s', hs', h⟩
      · rintro (⟨s', hs', h⟩ | ⟨s', hs', h⟩)
        · exact ⟨s', Or.inl hs', h⟩
        · exact ⟨s', Or.inr hs', h⟩
    rw [h_step, ih]

lemma foldl_stepSet_insert (M : εNFA α σ) (s : σ) (T : Set σ) (x : List α) :
  List.foldl M.stepSet (insert s T) x = List.foldl M.stepSet {s} x ∪ List.foldl M.stepSet T x := by
  have h_eq : insert s T = {s} ∪ T := rfl
  rw [h_eq, foldl_stepSet_union]

lemma foldl_stepSet_empty (M : εNFA α σ) (x : List α) :
  List.foldl M.stepSet ∅ x = ∅ := by
  induction x with
  | nil => rfl
  | cons a x ih =>
    simp only [List.foldl_cons]
    have h_step : M.stepSet ∅ a = ∅ := by
      ext s
      simp [εNFA.mem_stepSet_iff]
    rw [h_step, ih]

lemma foldl_stepSet_inr (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s₂ : σ₂) (x : List α) :
  List.foldl (εconcat M₁ M₂).stepSet {Sum.inr s₂} x = {Sum.inr (M₂.evalFrom s₂ x)} := by
  induction x generalizing s₂ with
  | nil => rfl
  | cons a x ih =>
    simp only [List.foldl_cons]
    have h_step : (εconcat M₁ M₂).stepSet {Sum.inr s₂} a = {Sum.inr (M₂.step s₂ a)} := by
      ext s
      simp only [εNFA.mem_stepSet_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨s', rfl, h_clos⟩
        change s ∈ (εconcat M₁ M₂).εClosure ((εconcat M₁ M₂).step (Sum.inr s₂) (some a)) at h_clos
        dsimp [εconcat] at h_clos
        rw [εconcat_εClosure_inr] at h_clos
        exact h_clos
      · intro h
        use Sum.inr s₂
        refine ⟨rfl, ?_⟩
        change s ∈ (εconcat M₁ M₂).εClosure ((εconcat M₁ M₂).step (Sum.inr s₂) (some a))
        dsimp [εconcat]
        rw [εconcat_εClosure_inr]
        exact h
    rw [h_step, ih]

lemma stepSet_inl (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s₁ : σ₁) (a : α) :
  (εconcat M₁ M₂).stepSet {Sum.inl s₁} a = (εconcat M₁ M₂).εClosure {Sum.inl (M₁.step s₁ a)} := by
  ext s
  simp only [εNFA.mem_stepSet_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s', rfl, h_clos⟩
    change s ∈ (εconcat M₁ M₂).εClosure ((εconcat M₁ M₂).step (Sum.inl s₁) (some a)) at h_clos
    dsimp [εconcat] at h_clos
    exact h_clos
  · intro h
    use Sum.inl s₁
    refine ⟨rfl, ?_⟩
    change s ∈ (εconcat M₁ M₂).εClosure ((εconcat M₁ M₂).step (Sum.inl s₁) (some a))
    dsimp [εconcat]
    exact h

lemma foldl_stepSet_inl (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s₁ : σ₁) (x : List α) :
  List.foldl (εconcat M₁ M₂).stepSet ((εconcat M₁ M₂).εClosure {Sum.inl s₁}) x =
    insert (Sum.inl (M₁.evalFrom s₁ x))
      { s | ∃ (u v : List α), x = u ++ v ∧ M₁.evalFrom s₁ u ∈ M₁.accept ∧ s = Sum.inr (M₂.evalFrom M₂.start v) } := by
  induction x generalizing s₁ with
  | nil =>
    rw [εconcat_εClosure_inl]
    dsimp [List.foldl]
    ext s
    simp only [Set.mem_insert_iff, Set.mem_setOf_eq, Set.mem_ite_empty_right, Set.mem_singleton_iff]
    constructor
    · intro h
      rcases h with rfl | ⟨h_acc, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨[], [], rfl, h_acc, rfl⟩
    · intro h
      rcases h with rfl | ⟨u, v, h_eq, h_acc, rfl⟩
      · exact Or.inl rfl
      · cases u with
        | nil =>
          simp only [List.nil_append] at h_eq
          subst h_eq
          exact Or.inr ⟨h_acc, rfl⟩
        | cons a' u' =>
          contradiction
  | cons a x ih =>
    simp only [List.foldl_cons]
    rw [εconcat_εClosure_inl, foldl_stepSet_insert, stepSet_inl]
    rw [ih (M₁.step s₁ a)]
    have h_ite : List.foldl (εconcat M₁ M₂).stepSet (if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅) x =
      if s₁ ∈ M₁.accept then { Sum.inr (M₂.evalFrom M₂.start x) } else ∅ := by
      split_ifs with h_acc
      · exact foldl_stepSet_inr M₁ M₂ M₂.start x
      · exact foldl_stepSet_empty _ x
    rw [h_ite]
    ext s
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_setOf_eq, Set.mem_ite_empty_right, Set.mem_singleton_iff]
    constructor
    · rintro ( (rfl | ⟨u, v, h_eq, h_acc, rfl⟩) | h_ite2 )
      · exact Or.inl rfl
      · exact Or.inr ⟨a :: u, v, by rw [h_eq, List.cons_append], h_acc, rfl⟩
      · rcases h_ite2 with ⟨h_acc2, rfl⟩
        exact Or.inr ⟨[], a :: x, rfl, h_acc2, rfl⟩
    · rintro (rfl | ⟨u, v, h_eq, h_acc, rfl⟩)
      · exact Or.inl (Or.inl rfl)
      · cases u with
        | nil =>
          simp only [List.nil_append] at h_eq
          subst h_eq
          exact Or.inr ⟨h_acc, rfl⟩
        | cons a' u' =>
          rw [List.cons_append] at h_eq
          injection h_eq with h_a h_x
          subst h_a h_x
          exact Or.inl (Or.inr ⟨u', v, rfl, h_acc, rfl⟩)
#count_heartbeats in -- 22 hearbeats
theorem accepts1 (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (εconcat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext x
  simp only [εNFA.accepts, Set.mem_setOf_eq, Language.mem_mul]
  constructor
  · rintro ⟨S, h_acc, h_eval⟩
    dsimp [εconcat, εNFA.accept] at h_acc
    rcases h_acc with ⟨s₂, hs₂, h_eqS⟩
    subst h_eqS
    have h_eval_eq : (εconcat M₁ M₂).eval x = List.foldl (εconcat M₁ M₂).stepSet ((εconcat M₁ M₂).εClosure {Sum.inl M₁.start}) x := by
      dsimp [εNFA.eval, εNFA.evalFrom]
      rw [εconcat_εClosure_start]
    rw [h_eval_eq, foldl_stepSet_inl] at h_eval
    simp only [Set.mem_insert_iff, Set.mem_setOf_eq] at h_eval
    rcases h_eval with h_inl | ⟨u, v, h_eq, h_acc_u, h_inr⟩
    · contradiction
    · injection h_inr with h_inr_eq
      use u, v
      refine ⟨h_acc_u, ?_, h_eq.symm⟩
      rw [← h_inr_eq]
      exact hs₂
  · rintro ⟨u, v, hu, hv, rfl⟩
    use Sum.inr (M₂.evalFrom M₂.start v)
    constructor
    · dsimp [εconcat, εNFA.accept]
      use M₂.evalFrom M₂.start v
      exact ⟨hv, rfl⟩
    · have h_eval_eq : (εconcat M₁ M₂).eval (u ++ v) = List.foldl (εconcat M₁ M₂).stepSet ((εconcat M₁ M₂).εClosure {Sum.inl M₁.start}) (u ++ v) := by
        dsimp [εNFA.eval, εNFA.evalFrom]
        rw [εconcat_εClosure_start]
      rw [h_eval_eq, foldl_stepSet_inl]
      simp only [Set.mem_insert_iff, Set.mem_setOf_eq]
      right
      use u, v
      exact ⟨rfl, hu, rfl⟩

end DFA

#print axioms DFA.accepts1
--'DFA.accepts1' depends on axioms: [propext, sorryAx, choice, Quot.sound]
/-No info found.
'DFA.accepts1' depends on axioms: [propext, sorryAx, choice, Quot.sound]
Application type mismatch: The argument
  v
has type
  u ∈ M₁.accepts
of sort `Prop` but is expected to have type
  List α
of sort `Type u` in the application
  u ++ v
Application type mismatch: The argument
  v
has type
  u ∈ M₁.accepts
of sort `Prop` but is expected to have type
  List α
of sort `Type u` in the application
  M₂.evalFrom M₂.start v
Application type mismatch: The argument
  v
has type
  u ∈ M₁.accepts
of sort `Prop` but is expected to have type
  List α
of sort `Type u` in the application
  M₂.evalFrom M₂.start v
Application type mismatch: The argument
  h_acc_u
has type
  M₁.evalFrom M₁.start u ∈ M₁.accept
of sort `Prop` but is expected to have type
  List α
of sort `Type u` in the application
  Exists.intro h_acc_u
Type mismatch
  v
has type
  List α
of sort `Type u` but is expected to have type
  u ∈ M₁.accepts
of sort `Prop`
This simp argument is unused:
  Set.mem_setOf_eq

Hint: Omit it from the simp argument list.
  simp only [εNFA.accepts, Set.mem_setOf_eq, Language.mem_mul]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Used 22 heartbeats, which is less than the current maximum of 200000.
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  List.foldl (εNFA.stepSet ?M) (insert ?s ?T) ?x
in the target expression
  List.foldl (M₁.εconcat M₂).stepSet
      ((M₁.εconcat M₂).stepSet (insert (Sum.inl s₁) (if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅)) a) x =
    insert (Sum.inl (M₁.evalFrom s₁ (a :: x)))
      {s | ∃ u v, a :: x = u ++ v ∧ M₁.evalFrom s₁ u ∈ M₁.accept ∧ s = Sum.inr (M₂.evalFrom M₂.start v)}

case cons
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
x : List α
ih : ∀ (s₁ : σ₁),
  List.foldl (M₁.εconcat M₂).stepSet ((M₁.εconcat M₂).εClosure {Sum.inl s₁}) x =
    insert (Sum.inl (M₁.evalFrom s₁ x))
      {s | ∃ u v, x = u ++ v ∧ M₁.evalFrom s₁ u ∈ M₁.accept ∧ s = Sum.inr (M₂.evalFrom M₂.start v)}
s₁ : σ₁
⊢ List.foldl (M₁.εconcat M₂).stepSet
    ((M₁.εconcat M₂).stepSet (insert (Sum.inl s₁) (if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅)) a) x =
  insert (Sum.inl (M₁.evalFrom s₁ (a :: x)))
    {s | ∃ u v, a :: x = u ++ v ∧ M₁.evalFrom s₁ u ∈ M₁.accept ∧ s = Sum.inr (M₂.evalFrom M₂.start v)}
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (εconcat ?M₁ ?M₂).εClosure {Sum.inr ?s₂}
in the target expression
  s ∈
    {
          step := fun s a ↦
            match s, a with
            | Sum.inl s₁, some c => {Sum.inl (M₁.step s₁ c)}
            | Sum.inl s₁, none => if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅
            | Sum.inr s₂, some c => {Sum.inr (M₂.step s₂ c)}
            | Sum.inr val, none => ∅,
          start := insert (Sum.inl M₁.start) (if M₁.start ∈ M₁.accept then {Sum.inr M₂.start} else ∅),
          accept := Sum.inr '' M₂.accept }.εClosure
      {Sum.inr (M₂.step s₂ a)}

case h
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
x : List α
ih : ∀ (s₂ : σ₂), List.foldl (M₁.εconcat M₂).stepSet {Sum.inr s₂} x = {Sum.inr (M₂.evalFrom s₂ x)}
s₂ : σ₂
s : σ₁ ⊕ σ₂
h : s = Sum.inr (M₂.step s₂ a)
⊢ s ∈
  {
        step := fun s a ↦
          match s, a with
          | Sum.inl s₁, some c => {Sum.inl (M₁.step s₁ c)}
          | Sum.inl s₁, none => if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅
          | Sum.inr s₂, some c => {Sum.inr (M₂.step s₂ c)}
          | Sum.inr val, none => ∅,
        start := insert (Sum.inl M₁.start) (if M₁.start ∈ M₁.accept then {Sum.inr M₂.start} else ∅),
        accept := Sum.inr '' M₂.accept }.εClosure
    {Sum.inr (M₂.step s₂ a)}
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (εconcat ?M₁ ?M₂).εClosure {Sum.inr ?s₂}
in the target expression
  s ∈
    {
          step := fun s a ↦
            match s, a with
            | Sum.inl s₁, some c => {Sum.inl (M₁.step s₁ c)}
            | Sum.inl s₁, none => if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅
            | Sum.inr s₂, some c => {Sum.inr (M₂.step s₂ c)}
            | Sum.inr val, none => ∅,
          start := insert (Sum.inl M₁.start) (if M₁.start ∈ M₁.accept then {Sum.inr M₂.start} else ∅),
          accept := Sum.inr '' M₂.accept }.εClosure
      {Sum.inr (M₂.step s₂ a)}

case h.mp
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
x : List α
ih : ∀ (s₂ : σ₂), List.foldl (M₁.εconcat M₂).stepSet {Sum.inr s₂} x = {Sum.inr (M₂.evalFrom s₂ x)}
s₂ : σ₂
s : σ₁ ⊕ σ₂
h_clos : s ∈
  {
        step := fun s a ↦
          match s, a with
          | Sum.inl s₁, some c => {Sum.inl (M₁.step s₁ c)}
          | Sum.inl s₁, none => if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅
          | Sum.inr s₂, some c => {Sum.inr (M₂.step s₂ c)}
          | Sum.inr val, none => ∅,
        start := insert (Sum.inl M₁.start) (if M₁.start ∈ M₁.accept then {Sum.inr M₂.start} else ∅),
        accept := Sum.inr '' M₂.accept }.εClosure
    {Sum.inr (M₂.step s₂ a)}
⊢ s = Sum.inr (M₂.step s₂ a)
unsolved goals
case cons
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
x : List α
ih : ∀ (s₂ : σ₂), List.foldl (M₁.εconcat M₂).stepSet {Sum.inr s₂} x = {Sum.inr (M₂.evalFrom s₂ x)}
s₂ : σ₂
h_step : (M₁.εconcat M₂).stepSet {Sum.inr s₂} a = {Sum.inr (M₂.step s₂ a)}
⊢ {Sum.inr (M₂.evalFrom (M₂.step s₂ a) x)} = {Sum.inr (M₂.evalFrom s₂ (a :: x))}
This simp argument is unused:
  εNFA.mem_stepSet_iff

Hint: Omit it from the simp argument list.
  simp [εNFA.mem_stepSet_iff]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
No goals to be solved
No goals to be solved
No goals to be solved
please avoid 'open (scoped) Classical' statements: this can hide theorem statements which would be better stated with explicit decidability statements.
Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
For theorem statements, either add missing decidability assumptions or use `open Classical in`.

Note: This linter can be disabled with `set_option linter.style.openClassical false`-/
