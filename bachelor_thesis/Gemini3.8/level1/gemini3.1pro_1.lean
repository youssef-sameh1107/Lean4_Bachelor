import Mathlib.Computability.NFA
import Mathlib.Computability.DFA
import Mathlib.Computability.Language
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Powerset

open Set Computability NFA DFA

universe u

variable {α : Type u}

namespace Language.IsRegular.ConcatNFA
#count_heartbeats in --143
/-- An NFA constructed to recognize the concatenation of two DFA languages. -/
def concatNFA {σ₁ σ₂ : Type*} (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : NFA α (σ₁ ⊕ σ₂) where
  step q a := match q with
    | Sum.inl q₁ =>
      let nxt := M₁.step q₁ a
      if nxt ∈ M₁.accept then {Sum.inl nxt, Sum.inr M₂.start}
      else {Sum.inl nxt}
    | Sum.inr q₂ => {Sum.inr (M₂.step q₂ a)}
  start := if M₁.start ∈ M₁.accept then {Sum.inl M₁.start, Sum.inr M₂.start} else {Sum.inl M₁.start}
  accept := {q | ∃ q₂, q = Sum.inr q₂ ∧ q₂ ∈ M₂.accept}
#count_heartbeats in --101
/-- The exact characterization of states reachable in `concatNFA` upon reading a string `x`. -/
lemma concatNFA_evalFrom {σ₁ σ₂ : Type*} (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (x : List α) (q₁ : σ₁) (S₂ : Set σ₂) :
  (concatNFA M₁ M₂).evalFrom (insert (Sum.inl q₁) (Sum.inr '' S₂)) x =
  insert (Sum.inl (M₁.evalFrom q₁ x))
    (Sum.inr '' ((fun q₂ => M₂.evalFrom q₂ x) '' S₂ ∪
      {q | ∃ y z, x = y ++ z ∧ y ≠ [] ∧ M₁.evalFrom q₁ y ∈ M₁.accept ∧ q = M₂.evalFrom M₂.start z})) := by
  induction x generalizing q₁ S₂ with
  | nil =>
    simp only [NFA.evalFrom_nil, DFA.evalFrom_nil, List.append_eq_nil_iff, true_and]
    ext s
    simp only [mem_insert_iff, mem_image, mem_union, mem_setOf_eq]
    constructor
    · rintro (rfl | ⟨q₂, hq₂, rfl⟩)
      · left; rfl
      · right; left; exact ⟨q₂, hq₂, rfl⟩
    · rintro (rfl | ⟨q₂, (⟨q₂', hq₂', rfl⟩ | ⟨y, z, hyz, hy, hacc, rfl⟩), rfl⟩)
      · left; rfl
      · right; exact ⟨q₂', hq₂', rfl⟩
      · apply (hy (List.append_eq_nil_iff.mp hyz.symm).1).elim
  | cons a x ih =>
    have h_step : (concatNFA M₁ M₂).stepSet (insert (Sum.inl q₁) (Sum.inr '' S₂)) a =
      insert (Sum.inl (M₁.step q₁ a))
        (Sum.inr '' ((fun q₂ => M₂.step q₂ a) '' S₂ ∪ if M₁.step q₁ a ∈ M₁.accept then {M₂.start} else ∅)) := by
      ext s
      simp only [NFA.mem_stepSet, mem_insert_iff, mem_image, mem_union, concatNFA]
      constructor
      · rintro ⟨s', hs', h_step⟩
        rcases hs' with (rfl | ⟨q₂, hq₂, rfl⟩)
        · dsimp at h_step
          split_ifs at h_step with hacc
          · simp only [mem_insert_iff, mem_singleton_iff] at h_step
            rcases h_step with rfl | rfl
            · left; rfl
            · right; right; rw [if_pos hacc]; exact Set.mem_singleton _
          · simp only [mem_singleton_iff] at h_step
            left; exact h_step
        · dsimp at h_step
          simp only [mem_singleton_iff] at h_step
          right; left; exact ⟨M₂.step q₂ a, ⟨q₂, hq₂, rfl⟩, h_step⟩
      · rintro (rfl | ⟨q₂', (⟨q₂, hq₂, rfl⟩ | h_start), rfl⟩)
        · exact ⟨Sum.inl q₁, Or.inl rfl, by dsimp; split_ifs; exact Or.inl rfl; rfl⟩
        · exact ⟨Sum.inr q₂, Or.inr ⟨q₂, hq₂, rfl⟩, rfl⟩
        · split_ifs at h_start with hacc
          · simp only [mem_singleton_iff] at h_start
            subst h_start
            exact ⟨Sum.inl q₁, Or.inl rfl, by dsimp; rw [if_pos hacc]; exact Or.inr rfl⟩
          · contradiction
    rw [NFA.evalFrom_cons, h_step, ih]
    ext s
    simp only [DFA.evalFrom_cons, mem_insert_iff, mem_image, mem_union, mem_setOf_eq]
    constructor
    · rintro (rfl | ⟨q₂, (⟨q₂', (⟨q₂'', hq₂'', rfl⟩ | h_start), rfl⟩ | ⟨y, z, hyz, hy, hacc, rfl⟩), rfl⟩)
      · left; rfl
      · right; exact ⟨M₂.evalFrom (M₂.step q₂'' a) x, Or.inl ⟨q₂'', hq₂'', rfl⟩, rfl⟩
      · split_ifs at h_start with hacc2
        · simp only [mem_singleton_iff] at h_start
          subst h_start
          right; exact ⟨M₂.evalFrom M₂.start x, Or.inr ⟨[a], x, rfl, by simp, hacc2, rfl⟩, rfl⟩
        · contradiction
      · right; exact ⟨M₂.evalFrom M₂.start z, Or.inr ⟨a :: y, z, by simp [hyz], by simp, hacc, rfl⟩, rfl⟩
    · rintro (rfl | ⟨q₂, (⟨q₂', hq₂', rfl⟩ | ⟨y, z, hyz, hy, hacc, rfl⟩), rfl⟩)
      · left; rfl
      · right; exact ⟨M₂.evalFrom (M₂.step q₂' a) x, Or.inl ⟨M₂.step q₂' a, Or.inl ⟨q₂', hq₂', rfl⟩, rfl⟩, rfl⟩
      · rcases y with _ | ⟨y_hd, y_tl⟩
        · contradiction
        · simp only [List.cons_append, List.cons_eq_cons] at hyz
          rcases hyz with ⟨rfl, rfl⟩
          rcases y_tl with _ | ⟨y₂_hd, y₂_tl⟩
          · have hacc2 : M₁.step q₁ a ∈ M₁.accept := hacc
            right
            refine ⟨M₂.evalFrom M₂.start x, Or.inl ⟨M₂.start, Or.inr ?_, rfl⟩, rfl⟩
            rw [if_pos hacc2]; exact Set.mem_singleton _
          · right
            refine ⟨M₂.evalFrom M₂.start z, Or.inr ⟨y₂_hd :: y₂_tl, z, rfl, by simp, hacc, rfl⟩, rfl⟩
#count_heartbeats in --26
/-- The equivalence between the accepted set of `concatNFA` and Mathlib's Language concatenation. -/
theorem concatNFA_accepts {σ₁ σ₂ : Type*} (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
  (concatNFA M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext x
  simp only [NFA.mem_accepts, concatNFA, mem_image, mem_union, mem_setOf_eq, Language.mem_mul]
  constructor
  · rintro ⟨S, ⟨q₂, hq₂, rfl⟩, h_eval⟩
    have h_start : (concatNFA M₁ M₂).start = insert (Sum.inl M₁.start) (Sum.inr '' (if M₁.start ∈ M₁.accept then {M₂.start} else ∅)) := by
      ext s; dsimp [concatNFA]; split_ifs with hacc
      · simp only [mem_insert_iff, image_singleton, mem_singleton_iff]
      · simp only [image_empty, mem_insert_iff, not_mem_empty, or_false]
    rw [NFA.eval, h_start, concatNFA_evalFrom] at h_eval
    simp only [mem_insert_iff, mem_image, mem_union, mem_setOf_eq] at h_eval
    rcases h_eval with h_inl | ⟨q₂', h_or, h_eq⟩
    · contradiction
    · injection h_eq with h_eq'
      subst h_eq'
      rcases h_or with hq₂'_1 | ⟨y, z, hyz, hy, hacc, rfl⟩
      · split_ifs at hq₂'_1 with hacc2
        · simp only [mem_singleton_iff] at hq₂'_1
          subst hq₂'_1
          exact ⟨[], hacc2, x, hq₂, rfl⟩
        · contradiction
      · exact ⟨y, hacc, z, hq₂, hyz⟩
  · rintro ⟨y, hy, z, hz, rfl⟩
    use Sum.inr (M₂.evalFrom M₂.start z)
    constructor
    · exact ⟨M₂.evalFrom M₂.start z, hz, rfl⟩
    · have h_start : (concatNFA M₁ M₂).start = insert (Sum.inl M₁.start) (Sum.inr '' (if M₁.start ∈ M₁.accept then {M₂.start} else ∅)) := by
        ext s; dsimp [concatNFA]; split_ifs with hacc
        · simp only [mem_insert_iff, image_singleton, mem_singleton_iff]
        · simp only [image_empty, mem_insert_iff, not_mem_empty, or_false]
      rw [NFA.eval, h_start, concatNFA_evalFrom]
      simp only [mem_insert_iff, mem_image, mem_union, mem_setOf_eq]
      rcases y with _ | ⟨y_hd, y_tl⟩
      · right
        have hacc : M₁.start ∈ M₁.accept := hy
        refine ⟨M₂.evalFrom M₂.start z, Or.inl ⟨M₂.start, ?_, rfl⟩, rfl⟩
        rw [if_pos hacc]; exact Set.mem_singleton _
      · right
        refine ⟨M₂.evalFrom M₂.start z, Or.inr ⟨y_hd :: y_tl, z, rfl, by simp, hy, rfl⟩, rfl⟩

end Language.IsRegular.ConcatNFA

open Language.IsRegular.ConcatNFA

#count_heartbeats in --28 heartbeats
/-- Regular languages are closed under concatenation. -/
theorem Language.IsRegular.mul1 {L₁ L₂ : Language α} (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
  (L₁ * L₂).IsRegular := by
  obtain ⟨σ₁, _, M₁, hM₁⟩ := Language.isRegular_iff.mp h₁
  obtain ⟨σ₂, _, M₂, hM₂⟩ := Language.isRegular_iff.mp h₂
  apply Language.isRegular_iff.mpr
  use σ₁ ⊕ σ₂
  use inferInstance
  use (concatNFA M₁ M₂).toDFA
  rw [NFA.toDFA_correct, concatNFA_accepts, hM₁, hM₂]

#print axioms Language.IsRegular.mul1
--[propext, sorryAx, Classical.choice, Quot.sound]
/-Failed to rewrite using equation theorems for `NFA.eval`
Tactic `split_ifs` failed: no if-then-else conditions to split

case h
α : Type u
σ₁ : Type u_1
σ₂ : Type u_2
M₁ : DFA α σ₁
M₂ : DFA α σ₂
y : List α
hy : y ∈ M₁.accepts
z : List α
hz : z ∈ M₂.accepts
s : σ₁ ⊕ σ₂
⊢ s ∈ sorry () ↔ s ∈ insert (Sum.inl M₁.start) (Sum.inr '' sorry ())
failed to synthesize instance of type class
  Decidable (M₁.start ∈ M₁.accept)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Error code: lean.synthInstanceFailed
View explanation
Application type mismatch: The argument
  hz
has type
  z ∈ M₂.accepts
but is expected to have type
  Sum.inr (M₂.evalFrom M₂.start z) = Sum.inr (M₂.evalFrom M₂.start z)
in the application
  And.intro hz
Tactic `subst` failed: invalid equality proof, it is not of the form (x = t) or (t = x)
  q₂ ∈ M₂.accept

case h.mp
α : Type u
σ₁ : Type u_1
σ₂ : Type u_2
M₁ : DFA α σ₁
M₂ : DFA α σ₂
x : List α
S : σ₁ ⊕ σ₂
h_eval : S ∈
  {
        step := fun q a ↦
          match q with
          | Sum.inl q₁ => sorry
          | Sum.inr q₂ => {Sum.inr (M₂.step q₂ a)},
        start := sorry, accept := {q | ∃ q₂, q = Sum.inr q₂ ∧ q₂ ∈ M₂.accept} }.evalFrom
    sorry x
q₂ : σ₂
hq₂ : S = Sum.inr q₂
right✝ : q₂ ∈ M₂.accept
⊢ ∃ a ∈ M₁.accepts, ∃ b ∈ M₂.accepts, a ++ b = x
This simp argument is unused:
  mem_union

Hint: Omit it from the simp argument list.
  simp only [NFA.mem_accepts, concatNFA, mem_image, mem_union, mem_setOf_eq, Language.mem_mul]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
This simp argument is unused:
  mem_image

Hint: Omit it from the simp argument list.
  simp only [NFA.mem_accepts, concatNFA, mem_image, mem_union, mem_setOf_eq, Language.mem_mul]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
declaration uses `sorry`
Used 26 heartbeats, which is less than the current maximum of 200000.
Unknown identifier `x`
Error code: lean.unknownIdentifier
View explanation
Tactic `split_ifs` failed: no if-then-else conditions to split

case cons.h.mp.inr.inl.inr
α : Type u
σ₁ : Type u_1
σ₂ : Type u_2
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
x : List α
ih : ∀ (q₁ : σ₁) (S₂ : Set σ₂),
  (concatNFA M₁ M₂).evalFrom (insert (Sum.inl q₁) (Sum.inr '' S₂)) x =
    insert (Sum.inl (M₁.evalFrom q₁ x))
      (Sum.inr ''
        ((fun q₂ ↦ M₂.evalFrom q₂ x) '' S₂ ∪
          {q | ∃ y z, x = y ++ z ∧ y ≠ [] ∧ M₁.evalFrom q₁ y ∈ M₁.accept ∧ q = M₂.evalFrom M₂.start z}))
q₁ : σ₁
S₂ : Set σ₂
h_step : (concatNFA M₁ M₂).stepSet (insert (Sum.inl q₁) (Sum.inr '' S₂)) a =
  insert (Sum.inl (M₁.step q₁ a)) (Sum.inr '' ((fun q₂ ↦ M₂.step q₂ a) '' S₂ ∪ sorry))
q₂' : σ₂
h_start : q₂' ∈ sorry
⊢ Sum.inr (M₂.evalFrom q₂' x) = Sum.inl (M₁.evalFrom (M₁.step q₁ a) x) ∨
  ∃ x_1,
    ((∃ x_2 ∈ S₂, M₂.evalFrom (M₂.step x_2 a) x = x_1) ∨
        ∃ y z, a :: x = y ++ z ∧ y ≠ [] ∧ M₁.evalFrom q₁ y ∈ M₁.accept ∧ x_1 = M₂.evalFrom M₂.start z) ∧
      Sum.inr x_1 = Sum.inr (M₂.evalFrom q₂' x)
Tactic `split_ifs` failed: no if-then-else conditions to split

case h.mpr.inr.inr
α : Type u
σ₁ : Type u_1
σ₂ : Type u_2
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
x : List α
ih : ∀ (q₁ : σ₁) (S₂ : Set σ₂),
  (concatNFA M₁ M₂).evalFrom (insert (Sum.inl q₁) (Sum.inr '' S₂)) x =
    insert (Sum.inl (M₁.evalFrom q₁ x))
      (Sum.inr ''
        ((fun q₂ ↦ M₂.evalFrom q₂ x) '' S₂ ∪
          {q | ∃ y z, x = y ++ z ∧ y ≠ [] ∧ M₁.evalFrom q₁ y ∈ M₁.accept ∧ q = M₂.evalFrom M₂.start z}))
q₁ : σ₁
S₂ : Set σ₂
q₂' : σ₂
h_start : q₂' ∈ sorry
⊢ ∃ t,
  (t = Sum.inl q₁ ∨ ∃ x ∈ S₂, Sum.inr x = t) ∧
    Sum.inr q₂' ∈
      match t with
      | Sum.inl q₁ => sorry
      | Sum.inr q₂ => {Sum.inr (M₂.step q₂ a)}
Tactic `split_ifs` failed: no if-then-else conditions to split

α : Type u
σ₁ : Type u_1
σ₂ : Type u_2
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
x : List α
ih : ∀ (q₁ : σ₁) (S₂ : Set σ₂),
  (concatNFA M₁ M₂).evalFrom (insert (Sum.inl q₁) (Sum.inr '' S₂)) x =
    insert (Sum.inl (M₁.evalFrom q₁ x))
      (Sum.inr ''
        ((fun q₂ ↦ M₂.evalFrom q₂ x) '' S₂ ∪
          {q | ∃ y z, x = y ++ z ∧ y ≠ [] ∧ M₁.evalFrom q₁ y ∈ M₁.accept ∧ q = M₂.evalFrom M₂.start z}))
q₁ : σ₁
S₂ : Set σ₂
⊢ Sum.inl (M₁.step q₁ a) ∈ sorry ()
Tactic `left` failed: left tactic works for inductive types with exactly 2 constructors

case h.mp.inr.h
α : Type u
σ₁ : Type u_1
σ₂ : Type u_2
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
x : List α
ih : ∀ (q₁ : σ₁) (S₂ : Set σ₂),
  (concatNFA M₁ M₂).evalFrom (insert (Sum.inl q₁) (Sum.inr '' S₂)) x =
    insert (Sum.inl (M₁.evalFrom q₁ x))
      (Sum.inr ''
        ((fun q₂ ↦ M₂.evalFrom q₂ x) '' S₂ ∪
          {q | ∃ y z, x = y ++ z ∧ y ≠ [] ∧ M₁.evalFrom q₁ y ∈ M₁.accept ∧ q = M₂.evalFrom M₂.start z}))
q₁ : σ₁
S₂ : Set σ₂
s : σ₁ ⊕ σ₂
q₂ : σ₂
hq₂ : q₂ ∈ S₂
h_step : s = Sum.inr (M₂.step q₂ a)
⊢ ∃ x, ((∃ x_1 ∈ S₂, M₂.step x_1 a = x) ∨ x ∈ sorry) ∧ Sum.inr x = s
Tactic `split_ifs` failed: no if-then-else conditions to split

case h.mp.inl
α : Type u
σ₁ : Type u_1
σ₂ : Type u_2
M₁ : DFA α σ₁
M₂ : DFA α σ₂
a : α
x : List α
ih : ∀ (q₁ : σ₁) (S₂ : Set σ₂),
  (concatNFA M₁ M₂).evalFrom (insert (Sum.inl q₁) (Sum.inr '' S₂)) x =
    insert (Sum.inl (M₁.evalFrom q₁ x))
      (Sum.inr ''
        ((fun q₂ ↦ M₂.evalFrom q₂ x) '' S₂ ∪
          {q | ∃ y z, x = y ++ z ∧ y ≠ [] ∧ M₁.evalFrom q₁ y ∈ M₁.accept ∧ q = M₂.evalFrom M₂.start z}))
q₁ : σ₁
S₂ : Set σ₂
s : σ₁ ⊕ σ₂
h_step : s ∈ sorry ()
⊢ s = Sum.inl (M₁.step q₁ a) ∨ ∃ x, ((∃ x_1 ∈ S₂, M₂.step x_1 a = x) ∨ x ∈ sorry) ∧ Sum.inr x = s
declaration uses `sorry`
failed to synthesize instance of type class
  Decidable (M₁.step q₁ a ∈ M₁.accept)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Error code: lean.synthInstanceFailed
View explanation
Tactic `left` failed: left tactic works for inductive types with exactly 2 constructors

case nil.h.mp.inr.h
α : Type u
σ₁ : Type u_1
σ₂ : Type u_2
M₁ : DFA α σ₁
M₂ : DFA α σ₂
q₁ : σ₁
S₂ : Set σ₂
q₂ : σ₂
hq₂ : q₂ ∈ S₂
⊢ ∃ x,
  ((∃ x_1 ∈ S₂, x_1 = x) ∨ ∃ y z, [] = y ++ z ∧ y ≠ [] ∧ M₁.evalFrom q₁ y ∈ M₁.accept ∧ x = M₂.evalFrom M₂.start z) ∧
    Sum.inr x = Sum.inr q₂
This simp argument is unused:
  true_and

Hint: Omit it from the simp argument list.
  simp only [NFA.evalFrom_nil, DFA.evalFrom_nil, List.append_eq_nil_iff, true_and]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
This simp argument is unused:
  List.append_eq_nil_iff

Hint: Omit it from the simp argument list.
  simp only [NFA.evalFrom_nil, DFA.evalFrom_nil, List.append_eq_nil_iff, true_and]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Used 101 heartbeats, which is less than the current maximum of 200000.
failed to synthesize instance of type class
  Decidable (M₁.start ∈ M₁.accept)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Error code: lean.synthInstanceFailed
View explanation
failed to synthesize instance of type class
  Decidable (nxt ∈ M₁.accept)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Error code: lean.synthInstanceFailed-/
