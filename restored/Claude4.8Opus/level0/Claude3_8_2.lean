import Mathlib.Computability.RegularExpressions

/-!
# Regular languages are closed under concatenation

We model a language over an alphabet `α` as a `Language α` (a set of lists),
and call it *regular* when it is the language `matches'` of some
`RegularExpression α`.
 Concatenation of languages is the monoid
multiplication `*` on `Language α`, and concatenation of regular
expressions is the constructor `comp`, also written `*`.
 The key fact `matches'_mul` says that `matches'` turns the `*` of regular
expressions into the `*` of languages, which makes the closure proof a
one-liner: given expressions for `L₁` and `L₂`, the expression `r₁ * r₂`
matches exactly `L₁ * L₂`.
 -/

namespace RegLang

open RegularExpression

variable {α : Type*}

#count_heartbeats in --10
/-- A language is *regular* when some regular expression matches exactly it.
 -/
def IsRegular (L : Language α) : Prop :=
  ∃ r : RegularExpression α, r.matches' = L

#count_heartbeats in --23 heartbeats
/-- Regular languages are closed under concatenation.
 -/

theorem IsRegular.mul {L₁ L₂ : Language α}
    (h₁ : IsRegular L₁) (h₂ : IsRegular L₂) : IsRegular (L₁ * L₂) := by
  obtain ⟨r₁, hr₁⟩ := h₁
  obtain ⟨r₂, hr₂⟩ := h₂
  -- The expression `r₁ * r₂` (i.e. `comp r₁ r₂`) matches `L₁ * L₂`.
  exact ⟨r₁ * r₂, by rw [matches'_mul, hr₁, hr₂]⟩

end RegLang

#print axioms RegLang.IsRegular.mul
--doesnt depend on anything [sorryAx]
/-Type mismatch
  ?m.35 * ?m.36
has type
  ?m.33
of sort `outParam (Type ?u.222.90)` but is expected to have type
  IsLeftRegular (L₁ * L₂)
of sort `Prop`
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (?P * ?Q).matches'
in the target expression
  IsRightRegular (L₁ * L₂)

α : Type u_1
L₁ L₂ : Language α
r₁ : IsLeftRegular L₁
hr₁ : IsRightRegular L₁
r₂ : IsLeftRegular L₂
hr₂ : IsRightRegular L₂
⊢ IsRightRegular (L₁ * L₂)-/
