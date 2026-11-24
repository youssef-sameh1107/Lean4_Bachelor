import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Basic

open Set

universe u

/-- Regular expressions over an alphabet `α`. -/
inductive Regex (α : Type u) : Type u
| emptySet : Regex α
| epsilon  : Regex α
| char     : α → Regex α
| union    : Regex α → Regex α → Regex α
| concat   : Regex α → Regex α → Regex α
| star     : Regex α → Regex α
deriving DecidableEq, Repr

namespace Regex

variable {α : Type u}

#count_heartbeats in --162
/-- The language denoted by a regular expression.
-/
def language : Regex α → Set (List α)
| emptySet      => ∅
| epsilon       => {[]}
| char a        => {[a]}
| union r₁ r₂   => language r₁ ∪ language r₂
| concat r₁ r₂  => {w |
∃ u v, u ∈ language r₁ ∧ v ∈ language r₂ ∧ w = u ++ v}
| star r        => {w |
∃ l : List (List α), (∀ s, s ∈ l → s ∈ language r) ∧ w = l.join}

end Regex

#count_heartbeats in --10
/-- A language is *regular* if some regular expression denotes it.
-/
def Regular {α : Type u} (L : Set (List α)) : Prop :=
  ∃ r : Regex α, Regex.language r = L

namespace Regular

variable {α : Type u}

#count_heartbeats in --36
/-- Concatenation of two languages.
-/
def concat (L₁ L₂ : Set (List α)) : Set (List α) :=
  {w |
∃ u v, u ∈ L₁ ∧ v ∈ L₂ ∧ w = u ++ v}

#count_heartbeats in --13
/-- Regular languages are closed under concatenation.
-/
theorem concat_closed {L₁ L₂ : Set (List α)}
    (h₁ : Regular L₁) (h₂ : Regular L₂) : Regular (concat L₁ L₂) := by
  rcases h₁ with ⟨r₁, hr₁⟩
  rcases h₂ with ⟨r₂, hr₂⟩
  refine ⟨Regex.concat r₁ r₂, ?_⟩
  -- Prove languages coincide
  ext w
  constructor
  · intro h
    rcases h with ⟨u, v, hu, hv, hw⟩
    have hu' : u ∈ L₁ := by
      simpa [hr₁] using hu
    have hv' : v ∈ L₂ := by

      simpa [hr₂] using hv
    exact ⟨u, v, hu', hv', hw⟩
  · intro h
    rcases h with ⟨u, v, hu, hv, hw⟩
    have hu' : u ∈ Regex.language r₁ := by
      simpa [hr₁] using hu
    have hv' : v ∈ Regex.language r₂ := by
      simpa [hr₂] using hv
    exact ⟨u, v, hu', hv', hw⟩

end Regular

#print axioms Regular.concat_closed
--[propext, sorryAx, Quot.sound]
--Invalid field `join`: The environment does not contain `List.join`,
--so it is not possible to project the field `join` from an expression
--  l
--of type `List (List α)`
--Error code: lean.invalidField
