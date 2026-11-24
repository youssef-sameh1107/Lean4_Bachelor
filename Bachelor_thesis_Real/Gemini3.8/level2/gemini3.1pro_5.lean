import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.Language

open Classical Set

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

-- Helper simplification lemmas to unfold the construction's step function
@[simp]
lemma εconcat_step_inl_some (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s₁ : σ₁) (c : α) :
    (εconcat M₁ M₂).step (Sum.inl s₁) (some c) = {Sum.inl (M₁.step s₁ c)} := rfl

@[simp]
lemma εconcat_step_inl_none (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s₁ : σ₁) :
    (εconcat M₁ M₂).step (Sum.inl s₁) none = if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅ := rfl

@[simp]
lemma εconcat_step_inr_some (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s₂ : σ₂) (c : α) :
    (εconcat M₁ M₂).step (Sum.inr s₂) (some c) = {Sum.inr (M₂.step s₂ c)} := rfl

@[simp]
lemma εconcat_step_inr_none (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s₂ : σ₂) :
    (εconcat M₁ M₂).step (Sum.inr s₂) none = ∅ := rfl

@[simp]
lemma εconcat_start (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (εconcat M₁ M₂).start = insert (Sum.inl M₁.start) (if M₁.start ∈ M₁.accept then {Sum.inr M₂.start} else ∅) := rfl

@[simp]
lemma εconcat_accept (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (εconcat M₁ M₂).accept = Sum.inr '' M₂.accept := rfl

/-- An auxiliary lemma characterizing the exact subset of states reachable in the concatenated εNFA
    after processing a string `w`. It precisely maintains the deterministic state of M₁ on the left,
    and spawns a deterministic M₂ state on the right for every accepted prefix of `w`. -/
lemma εconcat_eval_eq (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (w : List α) :
    (εconcat M₁ M₂).eval w =
    insert (Sum.inl (M₁.eval w)) (Sum.inr '' { s | ∃ x y, w = x ++ y ∧ M₁.eval x ∈ M₁.accept ∧ s = M₂.eval y }) := by
  induction w with
  | nil =>
    ext s
    simp only [DFA.eval, εNFA.eval, List.append_eq_nil_iff, Set.mem_insert_iff, Set.mem_image, Set.mem_setOf_eq,
               εconcat_start]
    aesop
  | cons a w ih =>
    ext s
    -- By utilizing the inductive hypothesis alongside our helper `simp` lemmas,
    -- we push the evaluation step through the epsilon closure and union sets.
    simp only [DFA.eval, εNFA.eval, ih, List.append_eq_nil_iff, Set.mem_insert_iff, Set.mem_image, Set.mem_setOf_eq,
               εconcat_step_inl_some, εconcat_step_inl_none, εconcat_step_inr_some, εconcat_step_inr_none]
    aesop

theorem accepts1 (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (εconcat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext w
  -- We unfold the definitions of language acceptance and language multiplication (concatenation).
  simp only [DFA.accepts, εNFA.accepts, Language.mul_def, Set.mem_mul, Set.mem_setOf_eq]

  -- Rewrite the εNFA evaluation into our explicit reachable-state characterization.
  rw [εconcat_eval_eq M₁ M₂ w]

  -- The acceptance condition is that the intersection of the reachable states and the accept states is nonempty.
  -- We simplify this intersection strictly using the disjoint nature of Sum.inl and Sum.inr.
  simp only [εconcat_accept, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_image, Set.mem_setOf_eq,
             Sum.inr.injEq, Sum.inl_inr_eq, false_and, false_or, Set.Nonempty]

  constructor
  · -- Forward direction: If the εconcat machine accepts `w`, there exists a valid partition `x ++ y`.
    rintro ⟨s, ⟨⟨x, y, h_append, h_accept_x, rfl⟩, h_accept_y⟩⟩
    exact ⟨x, y, h_append, h_accept_x, h_accept_y⟩
  · -- Backward direction: If `w = x ++ y` where `x` is accepted by M₁ and `y` by M₂, the εconcat machine accepts it.
    rintro ⟨x, y, h_append, h_accept_x, h_accept_y⟩
    exact ⟨Sum.inr (M₂.eval y), ⟨x, y, h_append, h_accept_x, rfl⟩, h_accept_y⟩

end DFA

/-Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (M₁.εconcat M₂).eval w
in the target expression
  w ∈ {x | ∃ S ∈ (M₁.εconcat M₂).accept, S ∈ (M₁.εconcat M₂).eval x} ↔
    w ∈ image2 (fun x1 x2 ↦ x1 ++ x2) (M₁.acceptsFrom M₁.start) (M₂.acceptsFrom M₂.start)

case h
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
w : List α
⊢ w ∈ {x | ∃ S ∈ (M₁.εconcat M₂).accept, S ∈ (M₁.εconcat M₂).eval x} ↔
  w ∈ image2 (fun x1 x2 ↦ x1 ++ x2) (M₁.acceptsFrom M₁.start) (M₂.acceptsFrom M₂.start)
unsolved goals
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
w : List α
ih : (M₁.εconcat M₂).eval w =
  insert (Sum.inl (M₁.eval w)) (Sum.inr '' {s | ∃ x y, w = x ++ y ∧ M₁.eval x ∈ M₁.accept ∧ s = M₂.eval y})
val : σ₁
h : M₁.start ∈ M₁.accept
a_1 : Sum.inl val ∈ (M₁.εconcat M₂).evalFrom {Sum.inl M₁.start, Sum.inr M₂.start} (a :: w)
⊢ val = M₁.evalFrom (M₁.step M₁.start a) w


α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
w : List α
ih : (M₁.εconcat M₂).eval w =
  insert (Sum.inl (M₁.eval w)) (Sum.inr '' {s | ∃ x y, w = x ++ y ∧ M₁.eval x ∈ M₁.accept ∧ s = M₂.eval y})
val : σ₁
h : M₁.start ∉ M₁.accept
a_1 : Sum.inl val ∈ (M₁.εconcat M₂).evalFrom {Sum.inl M₁.start} (a :: w)
⊢ val = M₁.evalFrom (M₁.step M₁.start a) w


α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
w : List α
ih : (M₁.εconcat M₂).eval w =
  insert (Sum.inl (M₁.eval w)) (Sum.inr '' {s | ∃ x y, w = x ++ y ∧ M₁.eval x ∈ M₁.accept ∧ s = M₂.eval y})
h : M₁.start ∈ M₁.accept
⊢ Sum.inl (M₁.evalFrom (M₁.step M₁.start a) w) ∈ (M₁.εconcat M₂).evalFrom {Sum.inl M₁.start, Sum.inr M₂.start} (a :: w)


α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
w : List α
ih : (M₁.εconcat M₂).eval w =
  insert (Sum.inl (M₁.eval w)) (Sum.inr '' {s | ∃ x y, w = x ++ y ∧ M₁.eval x ∈ M₁.accept ∧ s = M₂.eval y})
h : M₁.start ∉ M₁.accept
⊢ Sum.inl (M₁.evalFrom (M₁.step M₁.start a) w) ∈ (M₁.εconcat M₂).evalFrom {Sum.inl M₁.start} (a :: w)


α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
w : List α
ih : (M₁.εconcat M₂).eval w =
  insert (Sum.inl (M₁.eval w)) (Sum.inr '' {s | ∃ x y, w = x ++ y ∧ M₁.eval x ∈ M₁.accept ∧ s = M₂.eval y})
val_1 : σ₂
h : M₁.start ∈ M₁.accept
a_1 : Sum.inr val_1 ∈ (M₁.εconcat M₂).evalFrom {Sum.inl M₁.start, Sum.inr M₂.start} (a :: w)
⊢ ∃ x y, (a :: w = x ++ y ∧ M₁.evalFrom M₁.start x ∈ M₁.accept) ∧ M₂.evalFrom M₂.start y = val_1


α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
w : List α
ih : (M₁.εconcat M₂).eval w =
  insert (Sum.inl (M₁.eval w)) (Sum.inr '' {s | ∃ x y, w = x ++ y ∧ M₁.eval x ∈ M₁.accept ∧ s = M₂.eval y})
val_1 : σ₂
h : M₁.start ∉ M₁.accept
a_1 : Sum.inr val_1 ∈ (M₁.εconcat M₂).evalFrom {Sum.inl M₁.start} (a :: w)
⊢ ∃ x y, (a :: w = x ++ y ∧ M₁.evalFrom M₁.start x ∈ M₁.accept) ∧ M₂.evalFrom M₂.start y = val_1


α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
w : List α
ih : (M₁.εconcat M₂).eval w =
  insert (Sum.inl (M₁.eval w)) (Sum.inr '' {s | ∃ x y, w = x ++ y ∧ M₁.eval x ∈ M₁.accept ∧ s = M₂.eval y})
w_1 w_2 : List α
left : a :: w = w_1 ++ w_2
right_1 : M₁.evalFrom M₁.start w_1 ∈ M₁.accept
h : M₁.start ∈ M₁.accept
⊢ Sum.inr (M₂.evalFrom M₂.start w_2) ∈ (M₁.εconcat M₂).evalFrom {Sum.inl M₁.start, Sum.inr M₂.start} (w_1 ++ w_2)


α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
w : List α
ih : (M₁.εconcat M₂).eval w =
  insert (Sum.inl (M₁.eval w)) (Sum.inr '' {s | ∃ x y, w = x ++ y ∧ M₁.eval x ∈ M₁.accept ∧ s = M₂.eval y})
w_1 w_2 : List α
left : a :: w = w_1 ++ w_2
right_1 : M₁.evalFrom M₁.start w_1 ∈ M₁.accept
h : M₁.start ∉ M₁.accept
⊢ Sum.inr (M₂.evalFrom M₂.start w_2) ∈ (M₁.εconcat M₂).evalFrom {Sum.inl M₁.start} (w_1 ++ w_2)
  -/
