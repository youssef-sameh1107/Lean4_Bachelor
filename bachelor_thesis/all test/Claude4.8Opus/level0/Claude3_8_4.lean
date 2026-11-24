/-
  Regular languages are closed under concatenation.

  We model a *regular language* over an alphabet `α` as a language that is
  matched by some regular expression (`RegularExpression α`), which is the
  standard characterisation available in Mathlib.
* Concatenation of languages is the monoid multiplication `*` on `Language α`
    (i.e. `L₁ * L₂ = { x ++ y | x ∈ L₁, y ∈ L₂ }`).
* Concatenation of regular expressions is the multiplication `*` on
    `RegularExpression α` (the `comp` constructor).
The key fact `RegularExpression.matches'_mul` says these two are compatible:

      (r₁ * r₂).matches' = r₁.matches' * r₂.matches'

  so a witnessing regular expression for `L₁ * L₂` is simply `r₁ * r₂`.
-/
import Mathlib.Computability.RegularExpressions

open RegularExpression

#count_heartbeats in --10
/-- A language `L` over an alphabet `α` is **regular** when it is the language
matched by some regular expression.
-/
def IsRegularLanguage {α : Type*} (L : Language α) : Prop :=
  ∃ r : RegularExpression α, r.matches' = L

#count_heartbeats in --22 heartbeats
/-- **Regular languages are closed under concatenation.**
If `L₁` and `L₂` are regular, then so is their concatenation `L₁ * L₂`.
-/
theorem IsRegularLanguage.mul {α : Type*} {L₁ L₂ : Language α}
    (h₁ : IsRegularLanguage L₁) (h₂ : IsRegularLanguage L₂) :
    IsRegularLanguage (L₁ * L₂) := by
  -- Extract regular expressions matching `L₁` and `L₂`.
 obtain ⟨r₁, hr₁⟩ := h₁
  obtain ⟨r₂, hr₂⟩ := h₂
  -- The regex `r₁ * r₂` (concatenation of regexes) witnesses regularity of `L₁ * L₂`.
 refine ⟨r₁ * r₂, ?_⟩
  rw [matches'_mul, hr₁, hr₂]

#print axioms IsRegularLanguage.mul
--[sorryAx]
/-unexpected token ':='; expected command
Function expected at
  h₁
but this term has type
  IsRegularLanguage L₁

Note: Expected a function because this term is being applied to the argument
  obtain
Tactic `rcases` failed: `x✝ : ?m.10` is not an inductive datatype-/
