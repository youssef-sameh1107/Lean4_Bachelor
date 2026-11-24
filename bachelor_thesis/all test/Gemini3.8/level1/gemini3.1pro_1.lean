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
