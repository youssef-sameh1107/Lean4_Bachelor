import Mathlib.Computability.RegularExpressions

/-!
# Regular languages are closed under concatenation

A language `L : Language α` (i.e. a set of words, `Set (List α)`) is **regular**
when it is the language *denoted* by some regular expression: there is an
`r : RegularExpression α` with `r.matches' = L`.
This is the standard
formalization of regularity available in Mathlib, and by Kleene's theorem it
coincides with recognizability by a (deterministic) finite automaton.
The **concatenation** of two languages is the product `L₁ * L₂` coming from the
semiring structure on `Language α`;
concretely

    `L₁ * L₂ = { x ++ y | x ∈ L₁, y ∈ L₂ }`.
We prove that the concatenation of two regular languages is regular.
The proof is short because `RegularExpression` already has a concatenation
constructor `comp` (notation `*`) whose denotation is exactly the product of
denotations:

    `(r₁ * r₂).matches' = r₁.matches' * r₂.matches'`.
-/

open RegularExpression

universe u
variable {α : Type u}

#count_heartbeats in --10
/-- A language is **regular** if some regular expression denotes it.
-/
def IsRegular (L : Language α) : Prop :=
  ∃ r : RegularExpression α, r.matches' = L

#count_heartbeats in --26
/-- **Regular languages are closed under concatenation.**

If `L₁` and `L₂` are regular, witnessed by regular expressions `r₁` and `r₂`,
then the regular expression `r₁ * r₂` (the `comp` constructor) denotes the
concatenation `L₁ * L₂`, because
`(r₁ * r₂).matches' = r₁.matches' * r₂.matches'`.
-/
theorem IsRegular.mul {L₁ L₂ : Language α}
    (h₁ : IsRegular L₁) (h₂ : IsRegular L₂) : IsRegular (L₁ * L₂) := by
  obtain ⟨r₁, hr₁⟩ := h₁
  obtain ⟨r₂, hr₂⟩ := h₂
  exact ⟨r₁ * r₂, by rw [matches'_mul, hr₁, hr₂]⟩

/-!
### Bonus: the remaining Kleene closure properties

Not required by the statement, but they confirm that `IsRegular` behaves as it
should and that the concatenation result sits in a coherent framework.
Each one
follows the same one-line pattern. -/

#count_heartbeats in --26 heartbeats
/-- Regular languages are closed under union.
-/
theorem IsRegular.add {L₁ L₂ : Language α}
    (h₁ : IsRegular L₁) (h₂ : IsRegular L₂) : IsRegular (L₁ + L₂) := by
  obtain ⟨r₁, hr₁⟩ := h₁
  obtain ⟨r₂, hr₂⟩ := h₂
  exact ⟨r₁ + r₂, by rw [matches'_add, hr₁, hr₂]⟩

/-- Regular languages are closed under Kleene star.
-/

theorem IsRegular.star {L : Language α} (h : IsRegular L) : IsRegular L∗ := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r.star, by rw [matches'_star, hr]⟩

#count_heartbeats in
/-- The empty language `0` and the empty-word language `1` are regular,
so the concatenation theorem is non-vacuous.
-/
example : IsRegular (0 : Language α) := ⟨0, matches'_zero⟩
#count_heartbeats in --51
example : IsRegular (1 : Language α) := ⟨1, matches'_epsilon⟩

#print axioms IsRegular.add
--[sorryAx]
/-numerals are data in Lean, but the expected type is a proposition
  IsLeftRegular 1 : Prop
Used 51 heartbeats, which is less than the current maximum of 200000.
numerals are data in Lean, but the expected type is a proposition
  IsLeftRegular 0 : Prop
Used 51 heartbeats, which is less than the current maximum of 200000.
expected token
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (?P + ?Q).matches'
in the target expression
  IsRightRegular (L₁ + L₂)

α : Type u
L₁ L₂ : Language α
r₁ : IsLeftRegular L₁
hr₁ : IsRightRegular L₁
r₂ : IsLeftRegular L₂
hr₂ : IsRightRegular L₂
⊢ IsRightRegular (L₁ + L₂)
Type mismatch
  ?m.35 + ?m.36
has type
  ?m.33
of sort `outParam (Type ?u.411.90)` but is expected to have type
  IsLeftRegular (L₁ + L₂)
of sort `Prop`
Used 26 heartbeats, which is less than the current maximum of 200000.
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (?P * ?Q).matches'
in the target expression
  IsRightRegular (L₁ * L₂)

α : Type u
L₁ L₂ : Language α
r₁ : IsLeftRegular L₁
hr₁ : IsRightRegular L₁
r₂ : IsLeftRegular L₂
hr₂ : IsRightRegular L₂
⊢ IsRightRegular (L₁ * L₂)
Type mismatch
  ?m.35 * ?m.36
has type
  ?m.33
of sort `outParam (Type ?u.222.90)` but is expected to have type
  IsLeftRegular (L₁ * L₂)
of sort `Prop`
-/
