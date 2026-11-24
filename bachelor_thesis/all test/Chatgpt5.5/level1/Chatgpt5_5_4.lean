import Mathlib.Computability.EpsilonNFA

open Set

universe u v w

namespace List
#count_heartbeats in --11
@[simp]
theorem reduceOption_map_some {α : Type u} (x : List α) :
    (x.map (fun a => some a)).reduceOption = x := by
  induction x with
  | nil =>
      simp
  | cons a x ih =>
      simp [ih]

end List

namespace DFA

variable {α : Type u} {σ₁ : Type v} {σ₂ : Type w}
#count_heartbeats in --110
/-- The ε-NFA obtained by running `M₁`, then taking an ε-transition to the
start of `M₂` whenever `M₁` is in an accepting state, and then running `M₂`. -/
def concatENFA (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : εNFA α (σ₁ ⊕ σ₂) where
  step q a :=
    match q, a with
    | Sum.inl s, none =>
        {q | s ∈ M₁.accept ∧ q = Sum.inr M₂.start}
    | Sum.inl s, some x =>
        {Sum.inl (M₁.step s x)}
    | Sum.inr _, none =>
        ∅
    | Sum.inr s, some x =>
        {Sum.inr (M₂.step s x)}
  start := {Sum.inl M₁.start}
  accept := Sum.inr '' M₂.accept
#count_heartbeats in --19
lemma concatENFA_leftPath (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    (s : σ₁) (x : List α) :
    (concatENFA M₁ M₂).IsPath
      (Sum.inl s) (Sum.inl (M₁.evalFrom s x)) (x.map (fun a => some a)) := by
  induction x generalizing s with
  | nil =>
      simp
  | cons a x ih =>
      change (concatENFA M₁ M₂).IsPath
        (Sum.inl s)
        (Sum.inl (M₁.evalFrom (M₁.step s a) x))
        (some a :: x.map (fun a => some a))
      exact εNFA.IsPath.cons
        (Sum.inl (M₁.step s a))
        (Sum.inl s)
        (Sum.inl (M₁.evalFrom (M₁.step s a) x))
        (some a)
        (x.map (fun a => some a))
        (by simp [concatENFA])
        (ih (M₁.step s a))
#count_heartbeats in --19
lemma concatENFA_rightPath (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    (s : σ₂) (x : List α) :
    (concatENFA M₁ M₂).IsPath
      (Sum.inr s) (Sum.inr (M₂.evalFrom s x)) (x.map (fun a => some a)) := by
  induction x generalizing s with
  | nil =>
      simp
  | cons a x ih =>
      change (concatENFA M₁ M₂).IsPath
        (Sum.inr s)
        (Sum.inr (M₂.evalFrom (M₂.step s a) x))
        (some a :: x.map (fun a => some a))
      exact εNFA.IsPath.cons
        (Sum.inr (M₂.step s a))
        (Sum.inr s)
        (Sum.inr (M₂.evalFrom (M₂.step s a) x))
        (some a)
        (x.map (fun a => some a))
        (by simp [concatENFA])
        (ih (M₂.step s a))
#count_heartbeats in --26
lemma concatENFA_midPath (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    {s : σ₁} (hs : s ∈ M₁.accept) :
    (concatENFA M₁ M₂).IsPath (Sum.inl s) (Sum.inr M₂.start) [none] := by
  apply εNFA.IsPath.singleton
  simp [concatENFA, hs]
#count_heartbeats in --85
lemma concatENFA_path_spec (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    {q : σ₁ ⊕ σ₂} {t : σ₂} {xs : List (Option α)}
    (p : (concatENFA M₁ M₂).IsPath q (Sum.inr t) xs) :
    match q with
    | Sum.inl s =>
        ∃ u v : List α,
          xs.reduceOption = u ++ v ∧
            M₁.evalFrom s u ∈ M₁.accept ∧
              M₂.eval v = t
    | Sum.inr s =>
        M₂.evalFrom s xs.reduceOption = t := by
  induction p with
  | nil q =>
      simp [DFA.eval]
  | cons q q₀ qf a xs hq hp ih =>
      cases q₀ with
      | inl s =>
          cases a with
          | none =>
              have hqmem : s ∈ M₁.accept ∧ q = Sum.inr M₂.start := by
                simpa [concatENFA] using hq
              have hs : s ∈ M₁.accept := hqmem.1
              have hq' : q = Sum.inr M₂.start := hqmem.2
              subst q
              refine ⟨[], xs.reduceOption, by simp, hs, ?_⟩
              simpa [DFA.eval] using ih
          | some a =>
              have hq' : q = Sum.inl (M₁.step s a) := by
                simpa [concatENFA] using hq
              subst q
              obtain ⟨u, v, hxs, hu, hv⟩ := ih
              refine ⟨a :: u, v, ?_, ?_, hv⟩
              · simp [hxs]
              · simpa [DFA.evalFrom_cons] using hu
      | inr s =>
          cases a with
          | none =>
              exfalso
              simpa [concatENFA] using hq
          | some a =>
              have hq' : q = Sum.inr (M₂.step s a) := by
                simpa [concatENFA] using hq
              subst q
              simpa [DFA.evalFrom_cons] using ih
#count_heartbeats in --22
theorem concatENFA_accepts (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (concatENFA M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext x
  constructor
  · intro hx
    rw [εNFA.mem_accepts_iff_exists_path] at hx
    rcases hx with ⟨s₀, sF, xs, hs₀, hsF, hred, hp⟩
    have hs₀' : s₀ = Sum.inl M₁.start := by
      simpa [concatENFA] using hs₀
    subst s₀
    rcases hsF with ⟨t, ht, rfl⟩
    obtain ⟨u, v, huv, hu, hv⟩ :=
      concatENFA_path_spec M₁ M₂ hp
    rw [Language.mem_mul]
    refine ⟨u, ?_, v, ?_, ?_⟩
    · simpa [DFA.mem_accepts, DFA.eval] using hu
    · simpa [DFA.mem_accepts, DFA.eval, hv] using ht
    · rw [← hred, huv]
  · intro hx
    rw [Language.mem_mul] at hx
    rcases hx with ⟨u, hu, v, hv, huv⟩
    rw [εNFA.mem_accepts_iff_exists_path]
    have hu' : M₁.eval u ∈ M₁.accept := by
      simpa [DFA.mem_accepts] using hu
    have hv' : M₂.eval v ∈ M₂.accept := by
      simpa [DFA.mem_accepts] using hv
    have p₁ :
        (concatENFA M₁ M₂).IsPath
          (Sum.inl M₁.start) (Sum.inl (M₁.eval u))
          (u.map (fun a => some a)) := by
      simpa [DFA.eval] using concatENFA_leftPath M₁ M₂ M₁.start u
    have pε :
        (concatENFA M₁ M₂).IsPath
          (Sum.inl (M₁.eval u)) (Sum.inr M₂.start) [none] :=
      concatENFA_midPath M₁ M₂ hu'
    have p₁ε :
        (concatENFA M₁ M₂).IsPath
          (Sum.inl M₁.start) (Sum.inr M₂.start)
          (u.map (fun a => some a) ++ [none]) := by
      exact (εNFA.isPath_append (M := concatENFA M₁ M₂)).2
        ⟨Sum.inl (M₁.eval u), p₁, pε⟩
    have p₂ :
        (concatENFA M₁ M₂).IsPath
          (Sum.inr M₂.start) (Sum.inr (M₂.eval v))
          (v.map (fun a => some a)) := by
      simpa [DFA.eval] using concatENFA_rightPath M₁ M₂ M₂.start v
    have p :
        (concatENFA M₁ M₂).IsPath
          (Sum.inl M₁.start) (Sum.inr (M₂.eval v))
          ((u.map (fun a => some a) ++ [none]) ++
            v.map (fun a => some a)) := by
      exact (εNFA.isPath_append (M := concatENFA M₁ M₂)).2
        ⟨Sum.inr M₂.start, p₁ε, p₂⟩
    refine ⟨
      Sum.inl M₁.start,
      Sum.inr (M₂.eval v),
      (u.map (fun a => some a) ++ [none]) ++
        v.map (fun a => some a),
      ?_, ?_, ?_, p⟩
    · simp [concatENFA]
    · exact ⟨M₂.eval v, hv', rfl⟩
    · simp [List.reduceOption_append, huv]

end DFA

namespace Language

#count_heartbeats in --23 heartbeats

/-- Regular languages are closed under concatenation. -/
theorem IsRegular.mul {α : Type u} {L₁ L₂ : Language α}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (L₁ * L₂).IsRegular := by
  rcases h₁ with ⟨σ₁, inst₁, M₁, hM₁⟩
  rcases h₂ with ⟨σ₂, inst₂, M₂, hM₂⟩
  letI : Fintype σ₁ := inst₁
  letI : Fintype σ₂ := inst₂
  refine ⟨Set (σ₁ ⊕ σ₂), inferInstance,
    (DFA.concatENFA M₁ M₂).toNFA.toDFA, ?_⟩
  calc
    (DFA.concatENFA M₁ M₂).toNFA.toDFA.accepts
        = (DFA.concatENFA M₁ M₂).toNFA.accepts := by
          exact NFA.toDFA_correct (M := (DFA.concatENFA M₁ M₂).toNFA)
    _ = (DFA.concatENFA M₁ M₂).accepts := by
          exact εNFA.toNFA_correct (DFA.concatENFA M₁ M₂)
    _ = M₁.accepts * M₂.accepts := DFA.concatENFA_accepts M₁ M₂
    _ = L₁ * L₂ := by rw [hM₁, hM₂]

end Language

#print axioms Language.IsRegular.mul
--[propext, sorryAx, Classical.choice, Quot.sound]

--unclosed goal which allows for compilation but breaks with axioms
--type mismatch error too

/-Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)
  Sum.inr t
Type mismatch: After simplification, term
  ht
 has type
  t ∈ M₂.accept
but is expected to have type
  M₂.evalFrom M₂.start v ∈ M₂.accept-/
