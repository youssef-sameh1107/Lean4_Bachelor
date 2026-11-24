import Mathlib.Computability.RegularExpressions

/-!
# Regular languages are closed under concatenation

In Mathlib a *language* over an alphabet `α` is a set of strings:
`Language α := Set (List α)`.
 This type carries a semiring structure whose
multiplication is exactly the *concatenation* of languages:

    L * M = { u ++ v |
 u ∈ L, v ∈ M }.

We say a language is **regular** when it is the denotation `matches'` of some
regular expression `RegularExpression α`.
 Closure under concatenation is then
immediate, because the `comp` constructor of regular expressions (written `*`)
denotes language concatenation:

    (r * s).matches' = r.matches' * s.matches'.
 -/

variable {α : Type*}

#count_heartbeats in --14
/-- A language is **regular** when some regular expression matches exactly it.
 -/
def Language.IsRegular (L : Language α) : Prop :=
  ∃ r : RegularExpression α, r.matches' = L

#count_heartbeats in --24 heartbeats
/-- **Regular languages are closed under concatenation.**

If `L` and `M` are regular, then so is their concatenation `L * M`.
 -/
theorem Language.IsRegular.mul {L M : Language α}
    (hL : L.IsRegular) (hM : M.IsRegular) : (L * M).IsRegular := by
  -- Obtain regular expressions `r`, `s` matching `L`, `M` respectively.
 obtain ⟨r, hr⟩ := hL
  obtain ⟨s, hs⟩ := hM
  -- Their composition `r * s` matches the concatenation `L * M`.
 refine ⟨r * s, ?_⟩
  -- `(r * s).matches' = r.matches' * s.matches' = L * M`.
 simp [RegularExpression.matches', hr, hs]

#print axioms Language.IsRegular.mul
--[sorryAx]
/-Function expected at
  hL
but this term has type
  L.IsRegular

Note: Expected a function because this term is being applied to the argument
  obtain
Tactic `rcases` failed: `x✝ : ?m.10` is not an inductive datatype-/
