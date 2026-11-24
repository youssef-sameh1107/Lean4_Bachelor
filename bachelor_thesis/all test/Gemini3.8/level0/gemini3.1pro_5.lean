import Mathlib.Computability.Language
import Mathlib.Tactic

-- Let α be our alphabet
variable {α : Type*}

/--
We define a standard regular expression over the alphabet α.
This provides the algebraic structure for regular languages.
-/
inductive Regex (α : Type*)
  |
empty : Regex α
  | epsilon : Regex α
  | char : α → Regex α
  |
plus : Regex α → Regex α → Regex α
  |
comp : Regex α → Regex α → Regex α
  |
star : Regex α → Regex α

#count_heartbeats in --399
/--
Evaluation of a Regex into Mathlib's built-in `Language α`.
Mathlib provides instances for `0` (empty), `1` (epsilon), `+` (union),
`*` (concatenation), and `star` (Kleene star) on `Language α`.
-/
@[simp]
def Regex.toLanguage : Regex α → Language α
  | empty => 0
  | epsilon => 1
  |
char a => {[a]}
  | plus r s => r.toLanguage + s.toLanguage
  |
comp r s => r.toLanguage * s.toLanguage
  | star r => star (r.toLanguage)

#count_heartbeats in
/--
A language is defined as regular if there exists some regular expression
that perfectly denotes it.
-/
def IsRegular (L : Language α) : Prop :=
  ∃ r : Regex α, r.toLanguage = L

/--
Theorem: The concatenation of two regular languages is regular.
-/


#count_heartbeats in --25 heartbeats
theorem isRegular_concat {L₁ L₂ : Language α} (h₁ : IsRegular L₁) (h₂ : IsRegular L₂) :
    IsRegular (L₁ * L₂) := by
  -- Extract the underlying regular expressions (r₁ and r₂) and their equivalences
  -- from our hypotheses.
obtain ⟨r₁, hr₁⟩ := h₁
  obtain ⟨r₂, hr₂⟩ := h₂

  -- To show the concatenated language is regular, we provide the `comp` constructor
  -- wrapped around our extracted regexes.
use Regex.comp r₁ r₂

  -- Simplify the goal using our `@[simp]` definition of `Regex.toLanguage`.
-- This reduces `(Regex.comp r₁ r₂).toLanguage` to `r₁.toLanguage * r₂.toLanguage`.
simp only [Regex.toLanguage]

  -- Substitute the definitions of the languages back in to close the goal.
rw [hr₁, hr₂]


#print axioms isRegular_concat

--[sorryAx]
