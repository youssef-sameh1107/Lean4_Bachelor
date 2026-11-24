import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

universe u

namespace RegularLang

variable {α : Type u}

/-- A simple inductive definition of regular expressions over an alphabet `α`.
-/
inductive Regex (α : Type u) : Type u
| empty : Regex α                     -- ∅
| eps   : Regex α                     -- ε
| char  : α → Regex α                -- single character
| alt   : Regex α → Regex α → Regex α -- alternation (r | s)
| seq   : Regex α → Regex α → Regex α -- concatenation (r · s)
| star  : Regex α → Regex α           -- Kleene star (r*)
  deriving DecidableEq

namespace Regex

#count_heartbeats in
/-- Semantic interpretation of a regular expression as a predicate on strings.
-/
def matches {α : Type u} : Regex α → List α → Prop
| empty, _ => False
| eps,   l => l = []
| char c, l => l = [c]
| alt r s, l => matches r l ∨ matches s l
| seq r s, l => ∃ l₁ l₂, l = l₁ ++ l₂ ∧ matches r l₁ ∧ matches s l₂
| star r, l =>
    (l = []) ∨
    ∃ ls : List (List α), ls ≠ [] ∧ l = ls.join ∧ (∀ l', l' ∈ ls → matches r l')

end Regex

open Regex

#count_heartbeats in --13
/-- The language recognised by a regular expression.
-/
def langOf {α : Type u} (r : Regex α) : Set (List α) := {l |
Regex.matches r l}

#count_heartbeats in --11
/-- A language is *regular* if it is accepted by some regular expression.
-/
def Regular {α : Type u} (L : Set (List α)) : Prop := ∃ r : Regex α, langOf r = L

#count_heartbeats in--30
/-- Language concatenation.
-/
def concat {α : Type u} (L₁ L₂ : Set (List α)) : Set (List α) :=
  {l |
∃ l₁ l₂, l = l₁ ++ l₂ ∧ L₁ l₁ ∧ L₂ l₂}

#count_heartbeats in--14

/-- Regular languages are closed under concatenation.
-/
lemma regular_concat {α : Type u} {L₁ L₂ : Set (List α)}
    (h₁ : Regular (α := α) L₁) (h₂ : Regular (α := α) L₂) :
    Regular (concat L₁ L₂) := by
  rcases h₁ with ⟨r₁, hr₁⟩
  rcases h₂ with ⟨r₂, hr₂⟩
  refine ⟨Regex.seq r₁ r₂, ?_⟩
  ext l
  constructor
  · -- `→` direction
    intro h
    rcases h with ⟨l₁, l₂, hl, h₁m, h₂m⟩
    -- translate `matches` to membership using `hr₁` and `hr₂`
    have :
L₁ l₁ := by
      have : langOf r₁ l₁ := by
        simpa [langOf] using h₁m
      simpa [hr₁] using this
    have : L₂ l₂ := by
      have : langOf r₂ l₂ := by
        simpa [langOf] using h₂m
      simpa [hr₂] using this
    exact ⟨l₁, l₂, hl, ‹L₁ l₁›, ‹L₂ l₂›⟩
  · -- `←` direction
    intro h

     rcases h with ⟨l₁, l₂, hl, hL₁, hL₂⟩
    -- translate membership back to `matches`
    have h₁m : Regex.matches r₁ l₁ := by
      have : langOf r₁ l₁ := by
        simpa [hr₁] using hL₁
      simpa [langOf] using this
    have h₂m : Regex.matches r₂ l₂ := by
      have : langOf r₂ l₂ := by
        simpa [hr₂] using hL₂

simpa [langOf] using this
    exact ⟨l₁, l₂, hl, h₁m, h₂m⟩

end RegularLang

#print axioms RegularLang.concat --fails to compile
----no axioms
/-unexpected token 'matches'; expected identifier
unexpected token 'matches'; expected term
Used 14 heartbeats, which is less than the current maximum of 200000.
Unknown constant `RegularLang.Regex.matches`
Error code: lean.unknownIdentifier
View explanation
unsolved goals
case h.mpr
α : Type u
L₁ L₂ : Set (List α)
r₁ : Regex α
hr₁ : langOf r₁ = L₁
r₂ : Regex α
hr₂ : langOf r₂ = L₂
l : List α
⊢ l ∈ concat L₁ L₂ → l ∈ langOf (r₁.seq r₂)
unexpected identifier; expected command
'RegularLang.concat' does not depend on any axioms-/
