import Mathlib.Computability.RegularExpressions
/-!
# Regular Languages Are Closed Under Concatenation

**Theorem**: If `L₁` and `L₂` are regular languages over an alphabet `α`,
then their concatenation `L₁ * L₂` is also a regular language.
 ## Formalization

We use Mathlib's `RegularExpression` and `Language` APIs:

* `Language α = Set (List α)` — a language is a set of strings over `α`.
 * Concatenation `L₁ * L₂ = { u ++ v |
 u ∈ L₁, v ∈ L₂ }` is the `Mul` instance.
 * `RegularExpression α` — the inductive type of regular expressions with
  constructors `zero`, `epsilon`, `char`, `plus`, `comp`, `star` and
  numeric notation `0, 1, +, *`.
 * `r.matches' : Language α` — the language denoted by regular expression `r`,
  defined by structural recursion:
  - `(0 : RegularExpression α).matches' = 0`          (empty language)
  - `(1 : RegularExpression α).matches' = 1`          (language {ε})
  - `(char a).matches' = {[a]}`                        (singleton)
  - `(r₁ + r₂).matches' = r₁.matches' + r₂.matches'` (union)
  - `(r₁ * r₂).matches' = r₁.matches' * r₂.matches'` (concatenation)
  - `r.star.matches'   = r.matches'.kstar`             (Kleene star)

## Definition of Regularity

`Language.IsRegular L` holds when `L` equals `r.matches'` for some regular
expression `r`.
 This captures exactly the languages describable by regular
expressions, which (by the classical Kleene theorem) equals the class accepted
by finite automata.
 ## Proof of Closure Under Concatenation

Given `r₁` with `r₁.matches' = L₁` and `r₂` with `r₂.matches' = L₂`, the
regular expression `r₁ * r₂` witnesses `L₁ * L₂`:

    (r₁ * r₂).matches'
        = r₁.matches' * r₂.matches'    -- by RegularExpression.matches'_mul
        = L₁ * L₂.
 -- by hypothesis

The companion closure results (for `∅`, `{ε}`, `{[a]}`, union, and Kleene
star) are proved identically.
-/


/-!
 ### Definition -/

#count_heartbeats in --14
/-- A language `L : Language α` is **regular** if it is the language of some
    regular expression, i.e., `∃ r : RegularExpression α, r.matches' = L`.
 -/
def Language.IsRegular {α : Type*} (L : Language α) : Prop :=
  ∃ r : RegularExpression α, r.matches' = L

namespace Language.IsRegular

variable {α : Type*}

/-!
 ### Primitive regular languages -/

#count_heartbeats in --8
/-- The empty language `0 = ∅` is regular (witnessed by `0 : RegularExpression α`).
 -/
theorem zero : (0 : Language α).IsRegular :=
  ⟨0, RegularExpression.matches'_zero⟩

#count_heartbeats in --8
/-- The trivial language `1 = {ε}` (the empty word alone) is regular
    (witnessed by `1 : RegularExpression α`).
 -/
theorem one : (1 : Language α).IsRegular :=
  ⟨1, RegularExpression.matches'_epsilon⟩

#count_heartbeats in --17
/-- For each letter `a : α`, the singleton language `{[a]}` is regular
    (witnessed by `RegularExpression.char a`).
 -/
theorem ofChar (a : α) : ({[a]} : Language α).IsRegular :=
  ⟨.char a, RegularExpression.matches'_char a⟩

/-!
 ### Closure properties -/

#count_heartbeats in --18
/-- Regular languages are closed under union: if `L₁` and `L₂` are regular
    then `L₁ + L₂` is regular.
 -/
theorem add {L₁ L₂ : Language α}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) : (L₁ + L₂).IsRegular := by
  obtain ⟨r₁, rfl⟩ := h₁   -- substitute L₁ = r₁.matches' in the goal
  obtain ⟨r₂, rfl⟩ := h₂   -- substitute L₂ = r₂.matches' in the goal
  -- Witness: r₁ + r₂;
 proof obligation: (r₁ + r₂).matches' = r₁.matches' + r₂.matches'
  exact ⟨r₁ + r₂, RegularExpression.matches'_add r₁ r₂⟩

/-!
 ### Main theorem -/


#count_heartbeats in


/-- **Regular languages are closed under concatenation.**

If `L₁` and `L₂` are regular then `L₁ * L₂` is regular.
 *Proof.* Let `r₁`, `r₂` be regular expressions for `L₁`, `L₂`.
 The regular expression `r₁ * r₂` is a witness for `L₁ * L₂`:
 (r₁ * r₂).matches'
= r₁.matches' * r₂.matches'   [RegularExpression.matches'_mul]
= L₁ * L₂.
[by hypothesis]
-/


theorem mul {L₁ L₂ : Language α}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) : (L₁ * L₂).IsRegular := by
  -- Extract a regular expression r₁ with r₁.matches' = L₁,
  -- rewriting L₁ ↦ r₁.matches' throughout the goal.
 obtain ⟨r₁, rfl⟩ := h₁
  -- Extract a regular expression r₂ with r₂.matches' = L₂,
  -- rewriting L₂ ↦ r₂.matches' throughout the goal.
 obtain ⟨r₂, rfl⟩ := h₂
  -- Goal is now: ∃ r, r.matches' = r₁.matches' * r₂.matches'
  -- Witness r := r₁ * r₂;
 the equation holds by matches'_mul.
  exact ⟨r₁ * r₂, RegularExpression.matches'_mul r₁ r₂⟩

#count_heartbeats in --8
/-- Regular languages are closed under Kleene star: if `L` is regular
    then `L.kstar` is regular.
 -/
theorem kstar {L : Language α} (h : L.IsRegular) : L.kstar.IsRegular := by
  obtain ⟨r, rfl⟩ := h   -- substitute L = r.matches' in the goal
  -- Witness: r.star;
 proof: r.star.matches' = r.matches'.kstar
  exact ⟨r.star, RegularExpression.matches'_star r⟩

end Language.IsRegular

#print axioms Language.IsRegular.mul
--[sorryAx]
