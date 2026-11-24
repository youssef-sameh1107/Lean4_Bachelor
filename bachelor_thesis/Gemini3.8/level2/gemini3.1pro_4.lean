import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.Language
import Mathlib.Tactic

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

-- Supporting lemmas for the structure of epsilon-closures

lemma rtg_of_false {X : Type*} {r : X → X → Prop} {a : X} (h_false : ∀ b, ¬ r a b) (b : X) :
    Relation.ReflTransGen r a b ↔ b = a := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hcd ih =>
      subst ih
      exact (h_false _ hcd).elim
  · rintro rfl
    exact Relation.ReflTransGen.refl

lemma rtg_inl (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s : σ₁) (b : σ₁ ⊕ σ₂) :
    Relation.ReflTransGen (fun x y => y ∈ (εconcat M₁ M₂).step x none) (Sum.inl s) b ↔
    b = Sum.inl s ∨ (s ∈ M₁.accept ∧ b = Sum.inr M₂.start) := by
  constructor
  · intro h
    induction h with
    | refl => left; rfl
    | tail c d hac hcd ih =>
      rcases ih with rfl | ⟨hacc, rfl⟩
      · right
        dsimp [εconcat] at hcd
        split_ifs at hcd with h
        · exact ⟨h, hcd⟩
        · contradiction
      · exfalso
        dsimp [εconcat] at hcd
        contradiction
  · rintro (rfl | ⟨hacc, rfl⟩)
    · exact Relation.ReflTransGen.refl
    · apply Relation.ReflTransGen.tail Relation.ReflTransGen.refl
      dsimp [εconcat]
      rw [if_pos hacc]
      rfl

lemma εClosure_inr (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s : σ₂) :
    (εconcat M₁ M₂).εClosure {Sum.inr s} = {Sum.inr s} := by
  ext x
  simp only [εNFA.εClosure, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy, hrtg⟩
    rw [hy] at hrtg
    have h_false : ∀ b, ¬ (b ∈ (εconcat M₁ M₂).step (Sum.inr s) none) := by
      intro b; dsimp [εconcat]; exact Set.not_mem_empty b
    exact (rtg_of_false h_false x).mp hrtg
  · rintro rfl
    exact ⟨Sum.inr s, rfl, Relation.ReflTransGen.refl⟩

lemma εClosure_inl (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s : σ₁) :
    (εconcat M₁ M₂).εClosure {Sum.inl s} =
    insert (Sum.inl s) (if s ∈ M₁.accept then {Sum.inr M₂.start} else ∅) := by
  ext x
  simp only [εNFA.εClosure, Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_insert_iff]
  constructor
  · rintro ⟨y, hy, hrtg⟩
    rw [hy] at hrtg
    rw [rtg_inl] at hrtg
    rcases hrtg with rfl | ⟨hacc, rfl⟩
    · left; rfl
    · right
      split_ifs with h
      · rfl
      · contradiction
  · rintro (rfl | hx)
    · exact ⟨Sum.inl s, rfl, Relation.ReflTransGen.refl⟩
    · split_ifs at hx with h
      · rcases hx with rfl
        refine ⟨Sum.inl s, rfl, ?_⟩
        rw [rtg_inl]
        right; exact ⟨h, rfl⟩
      · contradiction

-- Structural lemmas for `stepSet` and `evalFrom`

lemma stepSet_empty (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (a : α) :
    (εconcat M₁ M₂).stepSet ∅ a = ∅ := by
  ext x
  simp only [εNFA.stepSet, Set.mem_empty_iff_false, false_and, exists_false, Set.mem_iUnion]

lemma εClosure_empty (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (εconcat M₁ M₂).εClosure ∅ = ∅ := by
  ext x
  simp only [εNFA.εClosure, Set.mem_setOf_eq, Set.mem_empty_iff_false, false_and, exists_false]

lemma stepSet_union (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (S T : Set (σ₁ ⊕ σ₂)) (a : α) :
    (εconcat M₁ M₂).stepSet (S ∪ T) a = (εconcat M₁ M₂).stepSet S a ∪ (εconcat M₁ M₂).stepSet T a := by
  ext x
  simp only [εNFA.stepSet, Set.mem_union, Set.mem_iUnion]
  constructor
  · rintro ⟨y, hy | hy, hx⟩
    · left; exact ⟨y, hy, hx⟩
    · right; exact ⟨y, hy, hx⟩
  · rintro (⟨y, hy, hx⟩ | ⟨y, hy, hx⟩)
    · exact ⟨y, Or.inl hy, hx⟩
    · exact ⟨y, Or.inr hy, hx⟩

lemma εClosure_union (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (S T : Set (σ₁ ⊕ σ₂)) :
    (εconcat M₁ M₂).εClosure (S ∪ T) = (εconcat M₁ M₂).εClosure S ∪ (εconcat M₁ M₂).εClosure T := by
  ext x
  simp only [εNFA.εClosure, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨y, hy | hy, hrtg⟩
    · left; exact ⟨y, hy, hrtg⟩
    · right; exact ⟨y, hy, hrtg⟩
  · rintro (⟨y, hy, hrtg⟩ | ⟨y, hy, hrtg⟩)
    · exact ⟨y, Or.inl hy, hrtg⟩
    · exact ⟨y, Or.inr hy, hrtg⟩

lemma εClosure_idem (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (S : Set (σ₁ ⊕ σ₂)) :
    (εconcat M₁ M₂).εClosure ((εconcat M₁ M₂).εClosure S) = (εconcat M₁ M₂).εClosure S := by
  ext x
  simp only [εNFA.εClosure, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, ⟨z, hz, hrtg1⟩, hrtg2⟩
    exact ⟨z, hz, Relation.ReflTransGen.trans hrtg1 hrtg2⟩
  · intro h
    rcases h with ⟨y, hy, hrtg⟩
    exact ⟨y, ⟨y, hy, Relation.ReflTransGen.refl⟩, hrtg⟩

lemma foldl_union (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (S T : Set (σ₁ ⊕ σ₂)) (w : List α) :
    List.foldl (fun s a => (εconcat M₁ M₂).εClosure ((εconcat M₁ M₂).stepSet s a)) (S ∪ T) w =
    List.foldl (fun s a => (εconcat M₁ M₂).εClosure ((εconcat M₁ M₂).stepSet s a)) S w ∪
    List.foldl (fun s a => (εconcat M₁ M₂).εClosure ((εconcat M₁ M₂).stepSet s a)) T w := by
  induction w generalizing S T with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.foldl_cons]
    have H : (εconcat M₁ M₂).εClosure ((εconcat M₁ M₂).stepSet (S ∪ T) a) =
             (εconcat M₁ M₂).εClosure ((εconcat M₁ M₂).stepSet S a) ∪
             (εconcat M₁ M₂).εClosure ((εconcat M₁ M₂).stepSet T a) := by
      rw [stepSet_union, εClosure_union]
    rw [H]
    exact ih _ _

lemma evalFrom_union (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (S T : Set (σ₁ ⊕ σ₂)) (w : List α) :
    (εconcat M₁ M₂).evalFrom (S ∪ T) w = (εconcat M₁ M₂).evalFrom S w ∪ (εconcat M₁ M₂).evalFrom T w := by
  unfold εNFA.evalFrom
  rw [εClosure_union, foldl_union]

lemma foldl_empty (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (w : List α) :
    List.foldl (fun s a => (εconcat M₁ M₂).εClosure ((εconcat M₁ M₂).stepSet s a)) ∅ w = ∅ := by
  induction w with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.foldl_cons]
    have H : (εconcat M₁ M₂).εClosure ((εconcat M₁ M₂).stepSet ∅ a) = ∅ := by
      rw [stepSet_empty, εClosure_empty]
    rw [H, ih]

lemma evalFrom_empty (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (w : List α) :
    (εconcat M₁ M₂).evalFrom ∅ w = ∅ := by
  unfold εNFA.evalFrom
  rw [εClosure_empty, foldl_empty]

lemma evalFrom_cons (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (S : Set (σ₁ ⊕ σ₂)) (a : α) (xs : List α) :
    (εconcat M₁ M₂).evalFrom S (a :: xs) =
    (εconcat M₁ M₂).evalFrom ((εconcat M₁ M₂).stepSet ((εconcat M₁ M₂).εClosure S) a) xs := by
  rfl

lemma foldl_inr (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s : σ₂) (w : List α) :
    List.foldl (fun s a => (εconcat M₁ M₂).εClosure ((εconcat M₁ M₂).stepSet s a)) {Sum.inr s} w =
    {Sum.inr (DFA.evalFrom s w)} := by
  induction w generalizing s with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.foldl_cons]
    have H1 : (εconcat M₁ M₂).stepSet {Sum.inr s} a = {Sum.inr (M₂.step s a)} := by
      ext x
      simp only [εNFA.stepSet, Set.mem_singleton_iff, Set.mem_iUnion]
      constructor
      · rintro ⟨y, rfl, hx⟩
        exact hx
      · intro hx
        exact ⟨Sum.inr s, rfl, hx⟩
    have H : (εconcat M₁ M₂).εClosure ((εconcat M₁ M₂).stepSet {Sum.inr s} a) = {Sum.inr (M₂.step s a)} := by
      rw [H1, εClosure_inr]
    rw [H]
    exact ih (M₂.step s a)

lemma evalFrom_inr (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s : σ₂) (w : List α) :
    (εconcat M₁ M₂).evalFrom {Sum.inr s} w = {Sum.inr (DFA.evalFrom s w)} := by
  unfold εNFA.evalFrom
  rw [εClosure_inr]
  exact foldl_inr M₁ M₂ _ _

lemma stepSet_inl_εClosure (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s : σ₁) (a : α) :
    (εconcat M₁ M₂).stepSet ((εconcat M₁ M₂).εClosure {Sum.inl s}) a =
    {Sum.inl (M₁.step s a)} ∪ if s ∈ M₁.accept then {Sum.inr (M₂.step M₂.start a)} else ∅ := by
  rw [εClosure_inl]
  ext x
  simp only [εNFA.stepSet, Set.mem_insert_iff, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨y, (rfl | hy), hx⟩
    · left
      exact hx
    · right
      split_ifs at hy with hacc
      · rw [hy] at hx
        exact hx
      · contradiction
  · rintro (hx | hx)
    · refine ⟨Sum.inl s, Or.inl rfl, hx⟩
    · split_ifs at hx with hacc
      · refine ⟨Sum.inr M₂.start, Or.inr ?_, hx⟩
        rw [if_pos hacc]
        rfl
      · contradiction

lemma mem_evalFrom_inl_inr (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s : σ₁) (w : List α) (t : σ₂) :
    Sum.inr t ∈ (εconcat M₁ M₂).evalFrom {Sum.inl s} w ↔
    ∃ w₁ w₂, w = w₁ ++ w₂ ∧ DFA.evalFrom s w₁ ∈ M₁.accept ∧ t = DFA.evalFrom M₂.start w₂ := by
  induction w generalizing s with
  | nil =>
    unfold εNFA.evalFrom
    simp only [List.foldl_nil, εClosure_inl, Set.mem_insert_iff, Sum.inr.injEq]
    constructor
    · intro h
      have h' : Sum.inr t ∈ (if s ∈ M₁.accept then {Sum.inr M₂.start} else ∅) := by
        rcases h with h | h
        · contradiction
        · exact h
      split_ifs at h' with hacc
      · exact ⟨[], [], rfl, hacc, (Set.mem_singleton_iff.mp h').symm⟩
      · contradiction
    · rintro ⟨w₁, w₂, h_eq, hacc, rfl⟩
      have h_nil : w₁ = [] ∧ w₂ = [] := List.append_eq_nil_iff.mp h_eq
      rcases h_nil with ⟨rfl, rfl⟩
      right
      split_ifs with h
      · rfl
      · contradiction
  | cons a xs ih =>
    rw [evalFrom_cons]
    rw [stepSet_inl_εClosure]
    rw [evalFrom_union]
    simp only [Set.mem_union]
    rw [ih]
    constructor
    · rintro (⟨w₁', w₂, h_eq, hacc, rfl⟩ | h2)
      · exact ⟨a :: w₁', w₂, congrArg (List.cons a) h_eq, hacc, rfl⟩
      · split_ifs at h2 with hacc
        · rw [evalFrom_inr, Set.mem_singleton_iff, Sum.inr.injEq] at h2
          exact ⟨[], a :: xs, rfl, hacc, h2⟩
        · rw [evalFrom_empty] at h2
          exact False.elim h2
    · rintro ⟨w₁, w₂, h_eq, hacc, rfl⟩
      cases w₁ with
      | nil =>
        simp only [List.nil_append] at h_eq
        subst h_eq
        right
        split_ifs with h
        · rw [evalFrom_inr, Set.mem_singleton_iff, Sum.inr.injEq]
          rfl
        · exact False.elim (h hacc)
      | cons b w₁' =>
        simp only [List.cons_append] at h_eq
        injection h_eq with h_a h_xs
        subst h_a
        subst h_xs
        left
        exact ⟨w₁', w₂, rfl, hacc, rfl⟩

lemma evalFrom_εClosure (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (S : Set (σ₁ ⊕ σ₂)) (w : List α) :
    (εconcat M₁ M₂).evalFrom ((εconcat M₁ M₂).εClosure S) w = (εconcat M₁ M₂).evalFrom S w := by
  unfold εNFA.evalFrom
  rw [εClosure_idem]

-- Main theorem
#count_heartbeats in
theorem accepts1 (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (εconcat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext w
  constructor
  · rintro ⟨x, hx_eval, hx_acc⟩
    rcases hx_acc with ⟨t, ht_acc, rfl⟩
    have h_start : (εconcat M₁ M₂).start = (εconcat M₁ M₂).εClosure {Sum.inl M₁.start} := by
      rw [εClosure_inl]; rfl
    rw [h_start] at hx_eval
    rw [evalFrom_εClosure] at hx_eval
    rw [mem_evalFrom_inl_inr] at hx_eval
    rcases hx_eval with ⟨w₁, w₂, h_eq, hacc₁, rfl⟩
    exact ⟨w₁, w₂, h_eq, hacc₁, ht_acc⟩
  · rintro ⟨w₁, w₂, h_eq, hacc₁, hacc₂⟩
    have h_start : (εconcat M₁ M₂).start = (εconcat M₁ M₂).εClosure {Sum.inl M₁.start} := by
      rw [εClosure_inl]; rfl
    refine ⟨Sum.inr (DFA.evalFrom M₂.start w₂), ?_, ⟨DFA.evalFrom M₂.start w₂, hacc₂, rfl⟩⟩
    rw [h_start]
    rw [evalFrom_εClosure]
    rw [mem_evalFrom_inl_inr]
    exact ⟨w₁, w₂, h_eq, hacc₁, rfl⟩

end DFA

#print axioms DFA.accepts1
--[propext, sorryAx, choice, Quot.sound]
--22 heartbeats
/-Application type mismatch: The argument
  M₂.start
has type
  σ₂
but is expected to have type
  DFA ?m.105 ?m.106
in the application
  evalFrom M₂.start
Tactic `rcases` failed: `hx_acc : List.foldl (M₁.εconcat M₂).stepSet ((M₁.εconcat M₂).εClosure (M₁.εconcat M₂).start) w
  x` is not an inductive datatype
Used 22 heartbeats, which is less than the current maximum of 200000.
This simp argument is unused:
  Sum.inr.injEq

Hint: Omit it from the simp argument list.
  simp only [List.foldl_nil, εClosure_inl, Set.mem_insert_iff, Sum.inr.injEq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Application type mismatch: The argument
  M₂.start
has type
  σ₂
but is expected to have type
  DFA ?m.32 ?m.33
in the application
  evalFrom M₂.start
failed to synthesize instance of type class
  Membership (List ?m.30 → List α) (Set σ₁)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Error code: lean.synthInstanceFailed
View explanation
Application type mismatch: The argument
  s
has type
  σ₁
but is expected to have type
  DFA ?m.30 ?m.31
in the application
  evalFrom s
Application type mismatch: The argument
  hx
has type
  x ∈ {Sum.inr (M₂.step M₂.start a)}
but is expected to have type
  x ∈ (M₁.εconcat M₂).εClosure ((M₁.εconcat M₂).step (Sum.inr M₂.start) (some a))
in the application
  Exists.intro (Or.inr ?m.185) hx
Application type mismatch: The argument
  hx
has type
  x = Sum.inl (M₁.step s a)
but is expected to have type
  x ∈ (M₁.εconcat M₂).εClosure ((M₁.εconcat M₂).step (Sum.inl s) (some a))
in the application
  Exists.intro (Or.inl rfl) hx
Type mismatch
  hx
has type
  x ∈ (M₁.εconcat M₂).εClosure ((M₁.εconcat M₂).step (Sum.inr M₂.start) (some a))
but is expected to have type
  x ∈ if s ∈ M₁.accept then {Sum.inr (M₂.step M₂.start a)} else ∅
Type mismatch
  hx
has type
  x ∈ (M₁.εconcat M₂).εClosure ((M₁.εconcat M₂).step (Sum.inl s) (some a))
but is expected to have type
  x = Sum.inl (M₁.step s a)
This simp argument is unused:
  Set.mem_setOf_eq

Hint: Omit it from the simp argument list.
  simp only [εNFA.stepSet, Set.mem_insert_iff, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_iUnion]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Unknown identifier `foldl_inr`
Error code: lean.unknownIdentifier
View explanation
failed to synthesize instance of type class
  Singleton (?m.14 ⊕ (List ?m.16 → List α)) (Set (σ₁ ⊕ σ₂))

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Error code: lean.synthInstanceFailed
View explanation
Application type mismatch: The argument
  s
has type
  σ₂
but is expected to have type
  DFA ?m.16 ?m.17
in the application
  evalFrom s
Application type mismatch: The argument
  hx
has type
  x = Sum.inr (M₂.step s a)
but is expected to have type
  x ∈ (M₁.εconcat M₂).εClosure ((M₁.εconcat M₂).step (Sum.inr s) (some a))
in the application
  Exists.intro rfl hx
Type mismatch
  hx
has type
  x ∈ (M₁.εconcat M₂).εClosure ((M₁.εconcat M₂).step (Sum.inr s) (some a))
but is expected to have type
  x = Sum.inr (M₂.step s a)
failed to synthesize instance of type class
  Singleton (?m.23 ⊕ (List ?m.25 → List α)) (Set (σ₁ ⊕ σ₂))

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Error code: lean.synthInstanceFailed
View explanation
Application type mismatch: The argument
  s
has type
  σ₂
but is expected to have type
  DFA ?m.25 ?m.26
in the application
  evalFrom s
`DFA.evalFrom_cons` has already been declared
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  List.foldl (fun s a ↦ (εconcat ?M₁ ?M₂).εClosure ((εconcat ?M₁ ?M₂).stepSet s a)) ∅ ?w
in the target expression
  List.foldl (M₁.εconcat M₂).stepSet ∅ w = ∅

α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
w : List α
⊢ List.foldl (M₁.εconcat M₂).stepSet ∅ w = ∅
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  List.foldl (fun s a ↦ (εconcat ?M₁ ?M₂).εClosure ((εconcat ?M₁ ?M₂).stepSet s a)) (?S ∪ ?T) ?w
in the target expression
  List.foldl (M₁.εconcat M₂).stepSet ((M₁.εconcat M₂).εClosure S ∪ (M₁.εconcat M₂).εClosure T) w =
    List.foldl (M₁.εconcat M₂).stepSet ((M₁.εconcat M₂).εClosure S) w ∪
      List.foldl (M₁.εconcat M₂).stepSet ((M₁.εconcat M₂).εClosure T) w

α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
S T : Set (σ₁ ⊕ σ₂)
w : List α
⊢ List.foldl (M₁.εconcat M₂).stepSet ((M₁.εconcat M₂).εClosure S ∪ (M₁.εconcat M₂).εClosure T) w =
  List.foldl (M₁.εconcat M₂).stepSet ((M₁.εconcat M₂).εClosure S) w ∪
    List.foldl (M₁.εconcat M₂).stepSet ((M₁.εconcat M₂).εClosure T) w
`simp` made no progress
Tactic `rcases` failed: `a✝ : S x` is not an inductive datatype
Tactic `rcases` failed: `h✝ : S x` is not an inductive datatype
This simp argument is unused:
  Set.mem_setOf_eq

Hint: Omit it from the simp argument list.
  simp only [εNFA.εClosure, Set.mem_setOf_eq, Set.mem_union]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
This simp argument is unused:
  εNFA.εClosure

Hint: Omit it from the simp argument list.
  simp only [εNFA.εClosure, Set.mem_setOf_eq, Set.mem_union]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
This simp argument is unused:
  exists_false

Hint: Omit it from the simp argument list.
  simp only [εNFA.εClosure, Set.mem_setOf_eq, Set.mem_empty_iff_false, false_and, exists_false]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
This simp argument is unused:
  false_and

Hint: Omit it from the simp argument list.
  simp only [εNFA.εClosure, Set.mem_setOf_eq, Set.mem_empty_iff_false, false_and, exists_false]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
This simp argument is unused:
  Set.mem_setOf_eq

Hint: Omit it from the simp argument list.
  simp only [εNFA.εClosure, Set.mem_setOf_eq, Set.mem_empty_iff_false, false_and, exists_false]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
This simp argument is unused:
  εNFA.εClosure

Hint: Omit it from the simp argument list.
  simp only [εNFA.εClosure, Set.mem_setOf_eq, Set.mem_empty_iff_false, false_and, exists_false]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
unsolved goals
case h
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
x : σ₁ ⊕ σ₂
⊢ x ∈ (M₁.εconcat M₂).εClosure ∅ ↔ False
This simp argument is unused:
  exists_false

Hint: Omit it from the simp argument list.
  simp only [εNFA.stepSet, Set.mem_empty_iff_false, false_and, exists_false, Set.mem_iUnion]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
This simp argument is unused:
  false_and

Hint: Omit it from the simp argument list.
  simp only [εNFA.stepSet, Set.mem_empty_iff_false, false_and, exists_false, Set.mem_iUnion]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
unsolved goals
case h
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
x : σ₁ ⊕ σ₂
⊢ (∃ i, ∃ (_ : False), x ∈ (M₁.εconcat M₂).εClosure ((M₁.εconcat M₂).step i (some a))) ↔ False
No goals to be solved
Invalid `⟨...⟩` notation: The expected type
  (M₁.εconcat M₂).εClosure {Sum.inl s} (Sum.inr M₂.start)
has more than one constructor

Note: This notation can only be used when the expected type is an inductive type with a single constructor
Invalid `⟨...⟩` notation: The expected type
  (M₁.εconcat M₂).εClosure {Sum.inl s} (Sum.inl s)
has more than one constructor

Note: This notation can only be used when the expected type is an inductive type with a single constructor
Unknown identifier `hrtg`
Error code: lean.unknownIdentifier
View explanation
This simp argument is unused:
  Set.mem_singleton_iff

Hint: Omit it from the simp argument list.
  simp only [εNFA.εClosure, Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_insert_iff]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
This simp argument is unused:
  Set.mem_setOf_eq

Hint: Omit it from the simp argument list.
  simp only [εNFA.εClosure, Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_insert_iff]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
This simp argument is unused:
  εNFA.εClosure

Hint: Omit it from the simp argument list.
  simp only [εNFA.εClosure, Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_insert_iff]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Invalid `⟨...⟩` notation: The expected type
  (M₁.εconcat M₂).εClosure {Sum.inr s} (Sum.inr s)
has more than one constructor

Note: This notation can only be used when the expected type is an inductive type with a single constructor
Unknown identifier `hrtg`
Error code: lean.unknownIdentifier
View explanation
This simp argument is unused:
  Set.mem_setOf_eq

Hint: Omit it from the simp argument list.
  simp only [εNFA.εClosure, Set.mem_setOf_eq, Set.mem_singleton_iff]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
This simp argument is unused:
  εNFA.εClosure

Hint: Omit it from the simp argument list.
  simp only [εNFA.εClosure, Set.mem_setOf_eq, Set.mem_singleton_iff]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Tactic `rcases` failed: `x✝ : ?m.55` is not an inductive datatype
Unknown identifier `ih`
Error code: lean.unknownIdentifier
View explanation
Too many variable names provided at alternative `tail`: 5 provided, but 3 expected
please avoid 'open (scoped) Classical' statements: this can hide theorem statements which would be better stated with explicit decidability statements.
Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
For theorem statements, either add missing decidability assumptions or use `open 
-/
