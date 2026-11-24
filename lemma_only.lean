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

namespace εconcat
variable (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)

def init (q : σ₁) : Set (σ₁ ⊕ σ₂) :=
  insert (Sum.inl q)
    (if q ∈ M₁.accept then ({Sum.inr M₂.start} : Set (σ₁ ⊕ σ₂)) else ∅)

@[simp] lemma step_inl_some (s : σ₁) (c : α) :
    (εconcat M₁ M₂).step (Sum.inl s) (some c) = {Sum.inl (M₁.step s c)} := sorry

@[simp] lemma step_inl_none (s : σ₁) :
    (εconcat M₁ M₂).step (Sum.inl s) none =
      (if s ∈ M₁.accept then ({Sum.inr M₂.start} : Set (σ₁ ⊕ σ₂)) else ∅) := sorry

@[simp] lemma step_inr_some (s : σ₂) (c : α) :
    (εconcat M₁ M₂).step (Sum.inr s) (some c) = {Sum.inr (M₂.step s c)} := sorry

@[simp] lemma step_inr_none (s : σ₂) :
    (εconcat M₁ M₂).step (Sum.inr s) none = (∅ : Set (σ₁ ⊕ σ₂)) := sorry

lemma εClosure_singleton_inr (s : σ₂) (x : σ₁ ⊕ σ₂) :
    x ∈ (εconcat M₁ M₂).εClosure {Sum.inr s} ↔ x = Sum.inr s := sorry

lemma εClosure_singleton_inl (q : σ₁) (x : σ₁ ⊕ σ₂) :
    x ∈ (εconcat M₁ M₂).εClosure {Sum.inl q} ↔
      x = Sum.inl q ∨ (x = Sum.inr M₂.start ∧ q ∈ M₁.accept) := sorry

lemma εClosure_init (q : σ₁) (x : σ₁ ⊕ σ₂) :
    x ∈ (εconcat M₁ M₂).εClosure (init M₁ M₂ q) ↔
      x = Sum.inl q ∨ (x = Sum.inr M₂.start ∧ q ∈ M₁.accept) := sorry

lemma mem_evalFrom_inl (q : σ₁) (xs : List α) (s : σ₁) :
    Sum.inl s ∈ (εconcat M₁ M₂).evalFrom (init M₁ M₂ q) xs ↔
      s = M₁.evalFrom q xs := sorry

lemma mem_evalFrom_inr (q : σ₁) (xs : List α) (r : σ₂) :
    Sum.inr r ∈ (εconcat M₁ M₂).evalFrom (init M₁ M₂ q) xs ↔
      ∃ u v, u ++ v = xs ∧ M₁.evalFrom q u ∈ M₁.accept ∧
        r = M₂.evalFrom M₂.start v := sorry

theorem accepts (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (εconcat M₁ M₂).accepts = M₁.accepts * M₂.accepts := sorry

end εconcat
end DFA
