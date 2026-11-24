import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.Language

open Classical
open Computability

universe u v

namespace DFA

variable {α : Type u} {σ : Type v}

/-- Kleene-star construction on a DFA.

We add one fresh "hub" state `none`.  From the hub an ε-transition enters a fresh
copy of `M` at `M.start`; inside the copy `M` runs deterministically on letters; and
from any accepting state of `M` an ε-transition returns to the hub.  The hub is both
the (unique) start state and the (unique) accept state, so the empty word is accepted
and each return to the hub closes off one factor of the star. -/
def εstar (M : DFA α σ) : εNFA α (Option σ) where
  step s a :=
    match s, a with
    | none,    some _ => ∅
    | none,    none   => {some M.start}
    | some s,  some c => {some (M.step s c)}
    | some s,  none   => if s ∈ M.accept then {none} else ∅
  start := {none}
  accept := {none}

namespace εstar

variable (M : DFA α σ)

@[simp] theorem step_none_some (c : α) :
    (εstar M).step none (some c) = (∅ : Set (Option σ)) := rfl

@[simp] theorem step_none_none :
    (εstar M).step none none = {some M.start} := rfl

@[simp] theorem step_some_some (s : σ) (c : α) :
    (εstar M).step (some s) (some c) = {some (M.step s c)} := rfl

@[simp] theorem step_some_none (s : σ) :
    (εstar M).step (some s) none = if s ∈ M.accept then {none} else ∅ := rfl

theorem start_def : (εstar M).start = {none} := rfl
theorem accept_def : (εstar M).accept = {none} := rfl

theorem reduceOption_map_some (x : List α) : (x.map some).reduceOption = x := by
  induction x with
  | nil => rfl
  | cons a x ih => rw [List.map_cons, List.reduceOption_cons_of_some, ih]

/-- Running `M` on a word `u` inside the `some`-region, from `some s`. -/
theorem run_some (u : List α) (s : σ) :
    (εstar M).IsPath (some s) (some (M.evalFrom s u)) (u.map some) := by
  induction u generalizing s with
  | nil => exact εNFA.IsPath.nil (some s)
  | cons c u ih =>
    apply εNFA.IsPath.cons (some (M.step s c))
    · simp
    · simpa [DFA.evalFrom_cons] using ih (M.step s c)

/-- Analyse a path that starts inside the `some`-region and ends back at the hub:
it reads a word `u` (accepted by `M` from `s`), takes the ε-transition back to the
hub, and then continues from the hub. -/
theorem excursion (w : List (Option α)) (s : σ)
    (h : (εstar M).IsPath (some s) none w) :
    ∃ u rest, w = u.map some ++ none :: rest ∧ M.evalFrom s u ∈ M.accept ∧
      (εstar M).IsPath none none rest := by
  induction w generalizing s with
  | nil =>
    rw [εNFA.isPath_nil] at h
    exact absurd h (by simp)
  | cons a w ih =>
    cases h with
    | cons t _ _ _ _ hmem hrest =>
      cases a with
      | some c =>
        simp only [step_some_some, Set.mem_singleton_iff] at hmem
        subst hmem
        obtain ⟨u, rest, hw, hacc, hpath⟩ := ih (M.step s c) hrest
        refine ⟨c :: u, rest, ?_, ?_, hpath⟩
        · rw [hw]; simp [List.map_cons]
        · rw [DFA.evalFrom_cons]; exact hacc
      | none =>
        simp only [step_some_none] at hmem
        by_cases hc : s ∈ M.accept
        · rw [if_pos hc, Set.mem_singleton_iff] at hmem
          subst hmem
          exact ⟨[], w, by simp, by simpa using hc, hrest⟩
        · rw [if_neg hc] at hmem
          exact absurd hmem (by simp)

/-- Every hub-to-hub path spells out a word in `M.accepts∗`. -/
theorem forward (n : ℕ) : ∀ (w : List (Option α)), w.length ≤ n →
    (εstar M).IsPath none none w → w.reduceOption ∈ (M.accepts)∗ := by
  induction n with
  | zero =>
    intro w hlen _
    cases w with
    | nil => exact Language.mem_kstar.mpr ⟨[], by simp, by simp⟩
    | cons a w' => simp only [List.length_cons] at hlen; omega
  | succ n ih =>
    intro w hlen h
    cases w with
    | nil => exact Language.mem_kstar.mpr ⟨[], by simp, by simp⟩
    | cons a w' =>
      cases h with
      | cons t _ _ _ _ hmem hrest =>
        cases a with
        | some c =>
          simp only [step_none_some, Set.mem_empty_iff_false] at hmem
        | none =>
          simp only [step_none_none, Set.mem_singleton_iff] at hmem
          subst hmem
          obtain ⟨u, rest, hw', hacc, hpath⟩ := excursion M w' M.start hrest
          have hlen_rest : rest.length ≤ n := by
            have hw : w'.length ≤ n := by simpa using hlen
            rw [hw'] at hw
            simp only [List.length_append, List.length_map, List.length_cons] at hw
            omega
          have hstar := ih rest hlen_rest hpath
          have hu : u ∈ M.accepts := by rw [DFA.mem_accepts, DFA.eval]; exact hacc
          rw [List.reduceOption_cons_of_none, hw', List.reduceOption_append,
            List.reduceOption_cons_of_none, reduceOption_map_some]
          obtain ⟨L', hflat, hL'⟩ := Language.mem_kstar.mp hstar
          refine Language.mem_kstar.mpr ⟨u :: L', ?_, ?_⟩
          · rw [List.flatten_cons, ← hflat]
          · intro z hz
            rw [List.mem_cons] at hz
            rcases hz with rfl | hz
            · exact hu
            · exact hL' z hz

/-- Conversely, every word in `M.accepts∗` is spelled out by some hub-to-hub path. -/
theorem build (L' : List (List α)) (hL' : ∀ y ∈ L', y ∈ M.accepts) :
    ∃ w, w.reduceOption = L'.flatten ∧ (εstar M).IsPath none none w := by
  induction L' with
  | nil => exact ⟨[], by simp, εNFA.IsPath.nil none⟩
  | cons y L'' ih =>
    obtain ⟨w, hre, hpath⟩ := ih (fun z hz => hL' z (List.mem_cons_of_mem y hz))
    have hy : M.evalFrom M.start y ∈ M.accept := by
      have := hL' y (by simp)
      rwa [DFA.mem_accepts, DFA.eval] at this
    refine ⟨none :: (y.map some ++ none :: w), ?_, ?_⟩
    · rw [List.reduceOption_cons_of_none, List.reduceOption_append,
        List.reduceOption_cons_of_none, reduceOption_map_some, hre, List.flatten_cons]
    · apply εNFA.IsPath.cons (some M.start)
      · simp
      · rw [εNFA.isPath_append]
        refine ⟨some (M.evalFrom M.start y), run_some M y M.start, ?_⟩
        apply εNFA.IsPath.cons none
        · simp only [step_some_none]; rw [if_pos hy]; exact Set.mem_singleton _
        · exact hpath

end εstar

/-- **Regular languages are closed under Kleene star.**
The ε-NFA `εstar M` recognises exactly the Kleene star of the language of `M`. -/
theorem star_accepts (M : DFA α σ) : (εstar M).accepts = (M.accepts)∗ := by
  ext x
  constructor
  · intro hx
    rw [εNFA.mem_accepts_iff_exists_path] at hx
    obtain ⟨s₁, s₂, w, hs₁, hs₂, hre, hpath⟩ := hx
    rw [εstar.start_def, Set.mem_singleton_iff] at hs₁
    rw [εstar.accept_def, Set.mem_singleton_iff] at hs₂
    subst hs₁; subst hs₂
    rw [← hre]
    exact εstar.forward M w.length w le_rfl hpath
  · intro hx
    rw [Language.mem_kstar] at hx
    obtain ⟨L', rfl, hL'⟩ := hx
    obtain ⟨w, hre, hpath⟩ := εstar.build M L' hL'
    rw [εNFA.mem_accepts_iff_exists_path]
    exact ⟨none, none, w, by rw [εstar.start_def]; exact Set.mem_singleton _,
      by rw [εstar.accept_def]; exact Set.mem_singleton _, hre, hpath⟩

end DFA
