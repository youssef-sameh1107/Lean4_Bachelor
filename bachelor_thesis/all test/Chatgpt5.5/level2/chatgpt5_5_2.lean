import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.Language

open Classical

universe u v

variable {α : Type u} {σ₁ σ₂ : Type v}
#count_heartbeats in --134
def εconcat (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : εNFA α (σ₁ ⊕ σ₂) where
  step s a := match s, a with
  | Sum.inl s₁, some c => {Sum.inl (M₁.step s₁ c)}
  | Sum.inl s₁, none => if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅
  | Sum.inr s₂, some c => {Sum.inr (M₂.step s₂ c)}
  | Sum.inr _ , none => ∅
  start := insert (Sum.inl M₁.start) (if M₁.start ∈ M₁.accept then ({Sum.inr M₂.start} : Set (σ₁ ⊕ σ₂)) else ∅)
  accept := Sum.inr '' M₂.accept
#count_heartbeats in --10
private lemma reduceOption_map_some {α : Type u} (x : List α) :
    (x.map fun a => some a).reduceOption = x := by
  induction x with
  | nil =>
      simp
  | cons a x ih =>
      simp [ih]
#count_heartbeats in --34
private lemma reduceOption_map_some_append_none {α : Type u} (x y : List α) :
    ((x.map fun a => some a) ++ none :: (y.map fun a => some a)).reduceOption = x ++ y := by
  induction x with
  | nil =>
      simp [reduceOption_map_some]
  | cons a x ih =>
      simp [ih]
#count_heartbeats in --19
private lemma εconcat_left_path
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s : σ₁) (x : List α) :
    (εconcat M₁ M₂).IsPath
      (Sum.inl s)
      (Sum.inl (M₁.evalFrom s x))
      (x.map fun a => some a) := by
  induction x generalizing s with
  | nil =>
      simpa using εNFA.IsPath.nil (M := εconcat M₁ M₂) (Sum.inl s)
  | cons a x ih =>
      simpa [DFA.evalFrom_cons] using
        εNFA.IsPath.cons
          (M := εconcat M₁ M₂)
          (t := Sum.inl (M₁.step s a))
          (s := Sum.inl s)
          (u := Sum.inl (M₁.evalFrom (M₁.step s a) x))
          (a := some a)
          (x := x.map fun a => some a)
          (by simp [εconcat])
          (ih (M₁.step s a))
#count_heartbeats in --19
private lemma εconcat_right_path
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s : σ₂) (x : List α) :
    (εconcat M₁ M₂).IsPath
      (Sum.inr s)
      (Sum.inr (M₂.evalFrom s x))
      (x.map fun a => some a) := by
  induction x generalizing s with
  | nil =>
      simpa using εNFA.IsPath.nil (M := εconcat M₁ M₂) (Sum.inr s)
  | cons a x ih =>
      simpa [DFA.evalFrom_cons] using
        εNFA.IsPath.cons
          (M := εconcat M₁ M₂)
          (t := Sum.inr (M₂.step s a))
          (s := Sum.inr s)
          (u := Sum.inr (M₂.evalFrom (M₂.step s a) x))
          (a := some a)
          (x := x.map fun a => some a)
          (by simp [εconcat])
          (ih (M₂.step s a))
#count_heartbeats in --19
private lemma εconcat_right_path_eval
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    {s t : σ₂} {x : List (Option α)}
    (h : (εconcat M₁ M₂).IsPath (Sum.inr s) (Sum.inr t) x) :
    M₂.evalFrom s x.reduceOption = t := by
  induction x generalizing s t with
  | nil =>
      have hst : Sum.inr s = Sum.inr t :=
        (εNFA.isPath_nil (M := εconcat M₁ M₂)).mp h
      injection hst with hst'
      simpa [hst'] -- <-- the only error in the entire code
      -- the model thought that injection would
      --result in a goal not realizing that injection automatically closes in this case
  | cons a x ih =>
      rw [εNFA.isPath_iff] at h
      rcases h with hnil | ⟨r, a', x', hstep, htail, hlist⟩
      · cases hnil.2
      · cases hlist
        cases a with
        | none =>
            simp [εconcat] at hstep
        | some c =>
            simp [εconcat] at hstep
            subst r
            have hrec := ih (s := M₂.step s c) (t := t) htail
            simpa [DFA.evalFrom_cons] using hrec
#count_heartbeats in --42
private lemma εconcat_left_to_right_split
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    {s : σ₁} {t : σ₂} {x : List (Option α)}
    (h : (εconcat M₁ M₂).IsPath (Sum.inl s) (Sum.inr t) x) :
    ∃ a b : List α,
      x.reduceOption = a ++ b ∧
      M₁.evalFrom s a ∈ M₁.accept ∧
      M₂.evalFrom M₂.start b = t := by
  induction x generalizing s t with
  | nil =>
      have hbad : Sum.inl s = Sum.inr t :=
        (εNFA.isPath_nil (M := εconcat M₁ M₂)).mp h
      cases hbad
  | cons oa x ih =>
      rw [εNFA.isPath_iff] at h
      rcases h with hnil | ⟨r, oa', x', hstep, htail, hlist⟩
      · cases hnil.2
      · cases hlist
        cases oa with
        | none =>
            by_cases hs : s ∈ M₁.accept
            · simp [εconcat, hs] at hstep
              subst r
              have hright :=
                εconcat_right_path_eval M₁ M₂
                  (s := M₂.start) (t := t) htail
              refine ⟨[], x.reduceOption, ?_, ?_, hright⟩
              · simp
              · simpa using hs
            · simp [εconcat, hs] at hstep
        | some c =>
            simp [εconcat] at hstep
            subst r
            obtain ⟨a, b, hred, ha, hb⟩ :=
              ih (s := M₁.step s c) (t := t) htail
            refine ⟨c :: a, b, ?_, ?_, hb⟩
            · simp [hred]
            · simpa [DFA.evalFrom_cons] using ha
#count_heartbeats in --42
private lemma εconcat_path_of_split
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    {a b : List α}
    (ha : a ∈ M₁.accepts) :
    (εconcat M₁ M₂).IsPath
      (Sum.inl M₁.start)
      (Sum.inr (M₂.eval b))
      ((a.map fun c => some c) ++ none :: (b.map fun c => some c)) := by
  have hleft :
      (εconcat M₁ M₂).IsPath
        (Sum.inl M₁.start)
        (Sum.inl (M₁.eval a))
        (a.map fun c => some c) := by
    simpa [DFA.eval] using εconcat_left_path M₁ M₂ M₁.start a

  have hcross :
      (εconcat M₁ M₂).IsPath
        (Sum.inl (M₁.eval a))
        (Sum.inr M₂.start)
        [none] := by
    apply εNFA.IsPath.singleton
    have ha' : M₁.eval a ∈ M₁.accept := (DFA.mem_accepts M₁).mp ha
    simpa [εconcat, ha']

  have hright :
      (εconcat M₁ M₂).IsPath
        (Sum.inr M₂.start)
        (Sum.inr (M₂.eval b))
        (b.map fun c => some c) := by
    simpa [DFA.eval] using εconcat_right_path M₁ M₂ M₂.start b

  have hleft_cross :
      (εconcat M₁ M₂).IsPath
        (Sum.inl M₁.start)
        (Sum.inr M₂.start)
        ((a.map fun c => some c) ++ [none]) := by
    rw [εNFA.isPath_append]
    exact ⟨Sum.inl (M₁.eval a), hleft, hcross⟩

  have hall :
      (εconcat M₁ M₂).IsPath
        (Sum.inl M₁.start)
        (Sum.inr (M₂.eval b))
        (((a.map fun c => some c) ++ [none]) ++ (b.map fun c => some c)) := by
    rw [εNFA.isPath_append]
    exact ⟨Sum.inr M₂.start, hleft_cross, hright⟩

  simpa [List.append_assoc] using hall

#count_heartbeats in -- 21 heartbeats
theorem εconcat_accepts (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (εconcat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext x
  constructor
  · intro hx
    rw [εNFA.mem_accepts_iff_exists_path] at hx
    rcases hx with ⟨q₀, qf, x', hq₀, hqf, hred, hpath⟩

    change qf ∈ Sum.inr '' M₂.accept at hqf
    rcases hqf with ⟨q₂, hq₂, rfl⟩

    change
      q₀ ∈ insert (Sum.inl M₁.start)
        (if M₁.start ∈ M₁.accept then
          ({Sum.inr M₂.start} : Set (σ₁ ⊕ σ₂))
        else
          ∅) at hq₀
    rw [Set.mem_insert_iff] at hq₀

    rw [Language.mem_mul]

    rcases hq₀ with rfl | hq₀
    · obtain ⟨a, b, hsplit, ha, hb⟩ :=
        εconcat_left_to_right_split M₁ M₂ hpath

      have ha' : a ∈ M₁.accepts := by
        rw [DFA.mem_accepts, DFA.eval]
        exact ha

      have hb' : b ∈ M₂.accepts := by
        rw [DFA.mem_accepts, DFA.eval, hb]
        exact hq₂

      exact ⟨a, ha', b, hb', hsplit.symm.trans hred⟩

    · by_cases hstart : M₁.start ∈ M₁.accept
      · simp [hstart] at hq₀
        subst q₀

        have hb_eval :
            M₂.evalFrom M₂.start x'.reduceOption = q₂ :=
          εconcat_right_path_eval M₁ M₂ hpath

        have hnil : ([] : List α) ∈ M₁.accepts := by
          rw [DFA.mem_accepts, DFA.eval]
          simpa using hstart

        have hxM₂ : x ∈ M₂.accepts := by
          rw [DFA.mem_accepts, DFA.eval, ← hred, hb_eval]
          exact hq₂

        exact ⟨[], hnil, x, hxM₂, by simp⟩

      · simp [hstart] at hq₀

  · intro hx
    rw [Language.mem_mul] at hx
    rcases hx with ⟨a, ha, b, hb, hxab⟩

    rw [εNFA.mem_accepts_iff_exists_path]

    refine
      ⟨Sum.inl M₁.start,
       Sum.inr (M₂.eval b),
       (a.map fun c => some c) ++ none :: (b.map fun c => some c),
       ?_, ?_, ?_, ?_⟩

    · simp [εconcat]

    · exact ⟨M₂.eval b, (DFA.mem_accepts M₂).mp hb, rfl⟩

    · exact (reduceOption_map_some_append_none a b).trans hxab

    · exact εconcat_path_of_split M₁ M₂ ha


#print axioms εconcat_accepts
--'εconcat_accepts' depends on axioms: [propext, sorryAx, choice, Quot.sound]
--line 90
