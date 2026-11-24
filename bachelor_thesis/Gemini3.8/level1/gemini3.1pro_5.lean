import Mathlib.Computability.Language
import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset

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

theorem accepts (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
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
/-'' starts on column 4, but all commands should start at the beginning of the line.

Note: This linter can be disabled with `set_option linter.style.whitespace false`
unterminated comment
'' starts on column 4, but all commands should start at the beginning of the line.

Note: This linter can be disabled with `set_option linter.style.whitespace false`
`DFA.accepts` has already been declared
aesop: failed to prove the goal after exhaustive search.
Unknown identifier `εconcat_step_inr_none`
Error code: lean.unknownIdentifier
View explanation
Unknown identifier `εconcat_step_inr_some`
Error code: lean.unknownIdentifier
View explanation
Unknown identifier `εconcat_step_inl_none`
Error code: lean.unknownIdentifier
View explanation
Unknown identifier `εconcat_step_inl_some`
Error code: lean.unknownIdentifier
View explanation
This simp argument is unused:
  List.append_eq_nil_iff

Hint: Omit it from the simp argument list.
  simp only [DFA.eval, εNFA.eval, ih, List.append_eq_nil_iff, Set.mem_insert_iff, Set.mem_image, Set.mem_setOf_eq,
               εconcat_step_inl_some, εconcat_step_inl_none, εconcat_step_inr_some, εconcat_step_inr_none]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Unknown identifier `εNFA.eval`
Error code: lean.unknownIdentifier
View explanation
unsolved goals
case cons.h.inl.mp
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
w : List α
ih : sorry () = insert (Sum.inl (M₁.eval w)) (Sum.inr '' {s | ∃ x y, w = x ++ y ∧ M₁.eval x ∈ M₁.accept ∧ s = M₂.eval y})
⊢ M₁.evalFrom M₁.start w = M₁.evalFrom (M₁.step M₁.start a) w


case cons.h.inl.mpr
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
w : List α
ih : sorry () = insert (Sum.inl (M₁.eval w)) (Sum.inr '' {s | ∃ x y, w = x ++ y ∧ M₁.eval x ∈ M₁.accept ∧ s = M₂.eval y})
⊢ M₁.evalFrom (M₁.step M₁.start a) w = M₁.evalFrom M₁.start w


case cons.h.inr.mp
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
w_1 w_2 : List α
right_1 : M₁.evalFrom M₁.start w_1 ∈ M₁.accept
ih : sorry () =
  insert (Sum.inl (M₁.eval (w_1 ++ w_2)))
    (Sum.inr '' {s | ∃ x y, w_1 ++ w_2 = x ++ y ∧ M₁.eval x ∈ M₁.accept ∧ s = M₂.eval y})
⊢ ∃ x y,
  (a :: (w_1 ++ w_2) = x ++ y ∧ M₁.evalFrom M₁.start x ∈ M₁.accept) ∧ M₂.evalFrom M₂.start y = M₂.evalFrom M₂.start w_2


case cons.h.inr.mpr
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
w : List α
ih : sorry () = insert (Sum.inl (M₁.eval w)) (Sum.inr '' {s | ∃ x y, w = x ++ y ∧ M₁.eval x ∈ M₁.accept ∧ s = M₂.eval y})
w_1 w_2 : List α
left : a :: w = w_1 ++ w_2
right_1 : M₁.evalFrom M₁.start w_1 ∈ M₁.accept
⊢ ∃ x y, (w = x ++ y ∧ M₁.evalFrom M₁.start x ∈ M₁.accept) ∧ M₂.evalFrom M₂.start y = M₂.evalFrom M₂.start w_2
aesop: failed to prove the goal after exhaustive search.
Unknown identifier `εconcat_start`
Error code: lean.unknownIdentifier
View explanation
This simp argument is unused:
  List.append_eq_nil_iff

Hint: Omit it from the simp argument list.
  simp only [DFA.eval, εNFA.eval, List.append_eq_nil_iff, Set.mem_insert_iff, Set.mem_image, Set.mem_setOf_eq,
      εconcat_start]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Unknown identifier `εNFA.eval`
Error code: lean.unknownIdentifier
View explanation
unsolved goals
case nil.h.inl.mp
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
val : σ₁
a : Sum.inl val ∈ sorry ()
⊢ val = M₁.start


case nil.h.inl.mpr
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
⊢ Sum.inl M₁.start ∈ sorry ()


case nil.h.inr.mp.left
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
val_1 : σ₂
a : Sum.inr val_1 ∈ sorry ()
⊢ M₁.start ∈ M₁.accept


case nil.h.inr.mp.right
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
val_1 : σ₂
a : Sum.inr val_1 ∈ sorry ()
⊢ M₂.start = val_1


case nil.h.inr.mpr
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
left : M₁.start ∈ M₁.accept
⊢ Sum.inr M₂.start ∈ sorry ()
don't know how to synthesize implicit argument `β`
  @image σ₂ (?m.12 M₁ M₂ ⊕ σ₂) Sum.inr M₂.accept
context:
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
⊢ Type (max v ?u.3493)


Note: All parameter types and holes (e.g., `_`) in the header of a theorem are resolved before the proof is processed; information from the proof cannot be used to infer what these values should be
don't know how to synthesize implicit argument `α`
  @Sum.inr (?m.12 M₁ M₂) σ₂
context:
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
⊢ Type ?u.3493


Note: All parameter types and holes (e.g., `_`) in the header of a theorem are resolved before the proof is processed; information from the proof cannot be used to infer what these values should be
typeclass instance problem is stuck
  EmptyCollection ?m.31

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `EmptyCollection` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
typeclass instance problem is stuck
  EmptyCollection ?m.7

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `EmptyCollection` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
typeclass instance problem is stuck
  Singleton (?m.8 ⊕ σ₂) ?m.12

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to `Singleton` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
typeclass instance problem is stuck
  EmptyCollection ?m.22

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `EmptyCollection` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
typeclass instance problem is stuck
  Singleton (σ₁ ⊕ ?m.9) ?m.12

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to `Singleton` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
Unknown identifier `εNFA`

Note: It is not possible to treat `εNFA` as an implicitly bound variable here because it has multiple characters while the `relaxedAutoImplicit` option is set to `false`.
Error code: lean.unknownIdentifier
View explanation-/
