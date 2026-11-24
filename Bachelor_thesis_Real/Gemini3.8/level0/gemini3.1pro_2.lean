import Mathlib.Computability.RegularExpressions
import Mathlib.Computability.Language

/-!
# Closure Properties of Regular Languages
This file demonstrates that regular languages are closed under concatenation
using Mathlib's computability and formal language libraries.
 -/

-- We define `α` to represent our arbitrary alphabet.
variable {α : Type*}

#count_heartbeats in --11
/--
A language `L` over an alphabet `α` is regular if there
exists a regular expression `r` whose language matches `L`.
 -/
def IsRegularLanguage (L : Language α) : Prop :=
  ∃ r : RegularExpression α, r.matches = L

#count_heartbeats in--17
/--
Theorem: Regular languages are closed under concatenation.
 Proof: If `L₁` and `L₂` are regular, there exist regular expressions `r₁` and `r₂`
that generate them.
 The concatenation of these regular expressions,
represented by `RegularExpression.comp r₁ r₂`, exactly matches the language `L₁ * L₂`.
 -/
theorem regular_concat {L₁ L₂ : Language α}
    (h₁ : IsRegularLanguage L₁) (h₂ : IsRegularLanguage L₂) :
    IsRegularLanguage (L₁ * L₂) := by

  -- Extract the underlying regular expressions r₁ and r₂ from our hypotheses.
 -- Using `rfl` in the rcases pattern automatically substitutes `L₁` with `r₁.matches`
  -- and `L₂` with `r₂.matches` in the goal state.
 rcases h₁ with ⟨r₁, rfl⟩
 rcases h₂ with ⟨r₂, rfl⟩

  -- We provide the composed regular expression as our existential witness.
 use RegularExpression.comp r₁ r₂

  -- In Mathlib, the language matched by `RegularExpression.comp r₁ r₂` is
  -- definitionally equal to `r₁.matches * r₂.matches`.
 -- Therefore, reflexivity gracefully closes the goal.
  rfl

/-!
### Bonus: Union and Kleene Star
Using the exact same structural logic, we can easily prove closure under
Union (`+`) and Kleene Star (`star`) to complete the standard closure properties.
 -/

#count_heartbeats in --17 heartsbeats
theorem regular_union {L₁ L₂ : Language α}
    (h₁ : IsRegularLanguage L₁) (h₂ : IsRegularLanguage L₂) :
    IsRegularLanguage (L₁ + L₂) := by
  rcases h₁ with ⟨r₁, rfl⟩
  rcases h₂ with ⟨r₂, rfl⟩
  use RegularExpression.plus r₁ r₂
  rfl

#count_heartbeats in --33
theorem regular_star {L : Language α}
    (h : IsRegularLanguage L) :
    IsRegularLanguage L.star := by
  rcases h with ⟨r, rfl⟩
  use RegularExpression.star r
  rfl

#print axioms regular_union
--[sorryAx]

/-Function expected at
  r₁.comp r₂
but this term has type
  RegularExpression α

Note: Expected a function because this term is being applied to the argument
  rfl
unsolved goals
case h
α : Type u_1
r₁ r₂ : RegularExpression α
⊢ sorry = sorry * sorry

Invalid field `matches`: The environment does not contain `RegularExpression.matches`, so it is not possible to project the field `matches` from an expression
  r
of type `RegularExpression α`
-/
