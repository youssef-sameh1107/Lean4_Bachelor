/-
  Regular languages are closed under concatenation
  ================================================

  Mathlib models regular expressions as `RegularExpression α`, together with the
  language they match, `RegularExpression.matches' : RegularExpression α → Language α`.
 Here `Language α := Set (List α)`, and concatenation of languages is the monoid
  multiplication `*`:

      L * M = { x |
 ∃ u ∈ L, ∃ v ∈ M, u ++ v = x }.
 We call a language *regular* when some regular expression matches it.
 The regex
  constructor `comp` — written `*` on `RegularExpression` — matches exactly the
  concatenation of the matched languages (the simp lemma
  `RegularExpression.matches'_mul`, which is true by `rfl`).
 Closure under
  concatenation is therefore immediate.
-/
import Mathlib.Computability.RegularExpressions

variable {α : Type*}

namespace Language

#count_heartbeats in --10
/-- A language is **regular** if it is the set of words matched by some
regular expression.
 -/
def IsRegular (L : Language α) : Prop :=
  ∃ r : RegularExpression α, r.matches' = L

#count_heartbeats in
/-- **Regular languages are closed under concatenation.**

If `L` and `M` are regular, witnessed by regular expressions `r` and `s`, then the
composite regular expression `r * s` matches `L * M`, so `L * M` is regular.
 -/
theorem IsRegular.mul {L M : Language α} (hL : IsRegular L) (hM : IsRegular M) :
    IsRegular (L * M) := by
  -- Unpack regular expressions matching `L` and `M`;
  substitute them for `L`, `M`.
  obtain ⟨r, rfl⟩ := hL
  obtain ⟨s, rfl⟩ := hM
  -- `(r * s).matches' = r.matches' * s.matches'` holds definitionally
  -- (`RegularExpression.matches'_mul`).
 exact ⟨r * s, rfl⟩

end Language

#count_heartbeats in --50 heartbeats
/-- A small sanity check: the concatenation of two single-character languages is
regular.
 (`(RegularExpression.char a).matches' = {[a]}` holds by `rfl` via
`RegularExpression.matches'_char`.) -/
example (a b : α) : Language.IsRegular ({[a]} * {[b]} : Language α) :=
  Language.IsRegular.mul ⟨RegularExpression.char a, rfl⟩ ⟨RegularExpression.char b, rfl⟩


#print axioms Language.IsRegular.mul
--d[sorryAx] ONLY
/-unknown tactic
unsolved goals
α : Type u_1
L M : Language α
hL : L.IsRegular
hM : M.IsRegular
⊢ (L * M).IsRegular-/
