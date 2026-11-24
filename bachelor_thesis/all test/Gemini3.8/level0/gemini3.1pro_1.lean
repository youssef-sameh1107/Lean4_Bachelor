import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Computability.Language

/-!
# Closure of Regular Languages Under Concatenation

This file provides a self-contained formalization proving that regular languages
are closed under concatenation.
 We define regular expressions over an alphabet `α`,
define their semantics as formal languages (`Language α := Set (List α)`), define
regularity, and establish closure under concatenation.
 -/

namespace FormalLanguages

variable {α : Type*}

/--
Inductive definition of Regular Expressions over an alphabet `α`.
-/
inductive RegEx (α : Type*)
  |
 empty : RegEx α
  | epsilon : RegEx α
  |
 char (a : α) : RegEx α
  | plus (r₁ r₂ : RegEx α) : RegEx α
  |
 comp (r₁ r₂ : RegEx α) : RegEx α
  |
 star (r : RegEx α) : RegEx α

#count_heartbeats in --118
/--
Semantics of regular expressions: mapping a `RegEx α` to a `Language α`.
 In Mathlib, `Language α` is defined as `Set (List α)`, which forms a semiring
where multiplication `*` corresponds to language concatenation.
 -/
def RegEx.toLanguage : RegEx α → Language α
  |
 .empty       => ∅
  | .epsilon     => {[]}
  |
 .char a      => {[a]}
  |
 .plus r₁ r₂  => r₁.toLanguage ∪ r₂.toLanguage
  | .comp r₁ r₂  => r₁.toLanguage * r₂.toLanguage
  |
 .star r      => r.toLanguage∗

#count_heartbeats in --10
/--
A formal language `L` over `α` is defined to be **Regular** if there exists
a regular expression `r` whose language is precisely `L`.
 -/
def IsRegular (L : Language α) : Prop :=
  ∃ r : RegEx α, r.toLanguage = L

/-!
 ### Main Theorems
-/

#count_heartbeats in --24
/--
The concatenation of two regular expressions yields the concatenation of their languages.
 By definition of `toLanguage`, this is an immediate structural equality.
 -/
lemma RegEx.toLanguage_comp (r₁ r₂ : RegEx α) :
    (RegEx.comp r₁ r₂).toLanguage = r₁.toLanguage * r₂.toLanguage := by
  rfl

/--
**Theorem**: Regular languages are closed under concatenation.
 Given two regular languages `L₁` and `L₂`, their concatenation `L₁ * L₂` is regular.
 -/

#count_heartbeats in --18 heartbeats
theorem isRegular_mul {L₁ L₂ : Language α} (h₁ : IsRegular L₁) (h₂ : IsRegular L₂) :
    IsRegular (L₁ * L₂) := by
  -- Obtain the witness regular expressions r₁ and r₂ for L₁ and L₂
  rcases h₁ with ⟨r₁, hr₁⟩
  rcases h₂ with ⟨r₂, hr₂⟩

  -- Construct the candidate regular expression for the concatenation
  use RegEx.comp r₁ r₂

  -- Rewrite using the definition of `toLanguage` for `comp` and our hypotheses
  rw [RegEx.toLanguage_comp, hr₁, hr₂]

end FormalLanguages

#print axioms FormalLanguages.isRegular_mul --fails to compile
--[sorryAx]
