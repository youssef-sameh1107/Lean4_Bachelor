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
@[simp]
lemma reduceOption_map_some' (x : List α) :
    (x.map some).reduceOption = x := by
  induction x with
  | nil =>
      simp
  | cons a x ih =>
      simp [ih]
#count_heartbeats in --115
@[simp]
lemma reduceOption_map_some_none_map_some (x y : List α) :
    (x.map some ++ [none] ++ y.map some).reduceOption = x ++ y := by
  simp [List.reduceOption_append]
#count_heartbeats in --18
lemma εconcat_path_inl (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    (s : σ₁) (x : List α) :
    (εconcat M₁ M₂).IsPath
      (Sum.inl s)
      (Sum.inl (M₁.evalFrom s x))
      (x.map some) := by
  induction x generalizing s with
  | nil =>
      simpa using
        (εNFA.IsPath.nil (M := εconcat M₁ M₂) (Sum.inl s))
  | cons a x ih =>
      simpa using
        (εNFA.IsPath.cons (M := εconcat M₁ M₂)
          (Sum.inl (M₁.step s a))
          (Sum.inl s)
          (Sum.inl (M₁.evalFrom (M₁.step s a) x))
          (some a)
          (x.map some)
          (by simp [εconcat])
          (ih (M₁.step s a)))
#count_heartbeats in --18
lemma εconcat_path_inr (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    (s : σ₂) (x : List α) :
    (εconcat M₁ M₂).IsPath
      (Sum.inr s)
      (Sum.inr (M₂.evalFrom s x))
      (x.map some) := by
  induction x generalizing s with
  | nil =>
      simpa using
        (εNFA.IsPath.nil (M := εconcat M₁ M₂) (Sum.inr s))
  | cons a x ih =>
      simpa using
        (εNFA.IsPath.cons (M := εconcat M₁ M₂)
          (Sum.inr (M₂.step s a))
          (Sum.inr s)
          (Sum.inr (M₂.evalFrom (M₂.step s a) x))
          (some a)
          (x.map some)
          (by simp [εconcat])
          (ih (M₂.step s a)))
#count_heartbeats in --27
lemma εconcat_path_from_inr_eq_aux (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    {p q : σ₁ ⊕ σ₂} {w : List (Option α)}
    (h : (εconcat M₁ M₂).IsPath p q w) :
    ∀ s₂ : σ₂, p = Sum.inr s₂ →
      q = Sum.inr (M₂.evalFrom s₂ w.reduceOption) := by
  induction h with
  | nil p =>
      intro s₂ hp
      subst p
      simp
  | cons t p q a w ht hp ih =>
      intro s₂ hp0
      subst p
      cases a with
      | none =>
          have hnone : t ∈ (∅ : Set (σ₁ ⊕ σ₂)) := by
            simpa [εconcat] using ht
          cases hnone
      | some c =>
          have ht' : t = Sum.inr (M₂.step s₂ c) := by
            simpa [εconcat] using ht
          have hq := ih (M₂.step s₂ c) ht'
          simpa using hq
#count_heartbeats in --22
lemma εconcat_path_from_inr_eq (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    {s₂ : σ₂} {q : σ₁ ⊕ σ₂} {w : List (Option α)}
    (h : (εconcat M₁ M₂).IsPath (Sum.inr s₂) q w) :
    q = Sum.inr (M₂.evalFrom s₂ w.reduceOption) :=
  εconcat_path_from_inr_eq_aux M₁ M₂ h s₂ rfl
#count_heartbeats in --52
lemma εconcat_left_to_right_decomp_aux (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    {p q : σ₁ ⊕ σ₂} {w : List (Option α)}
    (h : (εconcat M₁ M₂).IsPath p q w) :
    ∀ s₁ : σ₁, ∀ s₂ : σ₂, p = Sum.inl s₁ → q = Sum.inr s₂ →
      ∃ y z : List α,
        w.reduceOption = y ++ z ∧
        M₁.evalFrom s₁ y ∈ M₁.accept ∧
        M₂.evalFrom M₂.start z = s₂ := by
  induction h with
  | nil p =>
      intro s₁ s₂ hp hq
      rw [hp] at hq
      cases hq
  | cons t p q a w ht hp ih =>
      intro s₁ s₂ hp0 hq
      subst p
      cases a with
      | some c =>
          have ht' : t = Sum.inl (M₁.step s₁ c) := by
            simpa [εconcat] using ht
          obtain ⟨y, z, hred, hy, hz⟩ :=
            ih (M₁.step s₁ c) s₂ ht' hq
          refine ⟨c :: y, z, ?_, ?_, hz⟩
          · simpa [hred]
          · simpa using hy
      | none =>
          by_cases hacc : s₁ ∈ M₁.accept
          · have ht' : t = Sum.inr M₂.start := by
              simpa [εconcat, hacc] using ht
            have hqeval :
                q = Sum.inr (M₂.evalFrom M₂.start w.reduceOption) :=
              εconcat_path_from_inr_eq_aux M₁ M₂ hp M₂.start ht'
            have hz : M₂.evalFrom M₂.start w.reduceOption = s₂ := by
              have hs :
                  Sum.inr s₂ =
                    Sum.inr (M₂.evalFrom M₂.start w.reduceOption) := by
                simpa [hq] using hqeval
              injection hs with hs'
              exact hs'.symm
            refine ⟨[], w.reduceOption, ?_, ?_, hz⟩
            · simp
            · simpa using hacc
          · have hfalse : t ∈ (∅ : Set (σ₁ ⊕ σ₂)) := by
              simpa [εconcat, hacc] using ht
            cases hfalse
#count_heartbeats in --42
lemma εconcat_left_to_right_decomp (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    {s₁ : σ₁} {s₂ : σ₂} {w : List (Option α)}
    (h : (εconcat M₁ M₂).IsPath (Sum.inl s₁) (Sum.inr s₂) w) :
    ∃ y z : List α,
      w.reduceOption = y ++ z ∧
      M₁.evalFrom s₁ y ∈ M₁.accept ∧
      M₂.evalFrom M₂.start z = s₂ :=
  εconcat_left_to_right_decomp_aux M₁ M₂ h s₁ s₂ rfl rfl
#count_heartbeats in--34
lemma εconcat_start_cases (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    {q : σ₁ ⊕ σ₂}
    (h : q ∈ (εconcat M₁ M₂).start) :
    q = Sum.inl M₁.start ∨
      (M₁.start ∈ M₁.accept ∧ q = Sum.inr M₂.start) := by
  by_cases hacc : M₁.start ∈ M₁.accept
  · simp [εconcat, hacc] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hacc, h⟩
  · simp [εconcat, hacc] at h
    exact Or.inl h
#count_heartbeats in --21 heartbeats
theorem εconcat_accepts (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (εconcat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  apply Language.ext
  intro x
  constructor
  · intro hx
    rw [εNFA.mem_accepts_iff_exists_path] at hx
    rcases hx with ⟨p, q, w, hp, hq, hw, hpath⟩
    rcases hq with ⟨q₂, hq₂, hqeq⟩
    subst q
    rcases εconcat_start_cases M₁ M₂ hp with hp' | hp'
    · subst p
      obtain ⟨y, z, hred, hyacc, hzeq⟩ :=
        εconcat_left_to_right_decomp M₁ M₂ hpath
      have hy : y ∈ M₁.accepts := by
        rw [DFA.mem_accepts]
        simpa [DFA.eval] using hyacc
      have hz : z ∈ M₂.accepts := by
        rw [DFA.mem_accepts]
        simpa [DFA.eval, hzeq] using hq₂
      rw [Language.mem_mul]
      exact ⟨y, hy, z, hz, hred.symm.trans hw⟩
    · rcases hp' with ⟨hstartacc, hp''⟩
      subst p
      have hqeval := εconcat_path_from_inr_eq M₁ M₂ hpath
      have hzeq : M₂.evalFrom M₂.start w.reduceOption = q₂ := by
        injection hqeval with hqeval'
        exact hqeval'.symm
      have hy : [] ∈ M₁.accepts := by
        rw [DFA.mem_accepts]
        simpa using hstartacc
      have hz : w.reduceOption ∈ M₂.accepts := by
        rw [DFA.mem_accepts]
        simpa [DFA.eval, hzeq] using hq₂
      rw [Language.mem_mul]
      exact ⟨[], hy, w.reduceOption, hz, by simpa using hw⟩
  · intro hx
    rw [Language.mem_mul] at hx
    rcases hx with ⟨y, hy, z, hz, hxyz⟩
    rw [εNFA.mem_accepts_iff_exists_path]
    let w : List (Option α) := y.map some ++ [none] ++ z.map some
    refine ⟨Sum.inl M₁.start, Sum.inr (M₂.eval z), w, ?_, ?_, ?_, ?_⟩
    · simp [εconcat]
    · exact ⟨M₂.eval z, (DFA.mem_accepts M₂).mp hz, rfl⟩
    · change (y.map some ++ [none] ++ z.map some).reduceOption = x
      simpa [hxyz]
    · change
        (εconcat M₁ M₂).IsPath
          (Sum.inl M₁.start)
          (Sum.inr (M₂.eval z))
          (y.map some ++ [none] ++ z.map some)
      rw [εNFA.isPath_append]
      refine ⟨Sum.inl (M₁.eval y), ?_, ?_⟩
      · simpa [DFA.eval] using
          εconcat_path_inl M₁ M₂ M₁.start y
      · rw [εNFA.isPath_append]
        refine ⟨Sum.inr M₂.start, ?_, ?_⟩
        · have hyacc : M₁.eval y ∈ M₁.accept :=
            (DFA.mem_accepts M₁).mp hy
          exact
            εNFA.IsPath.singleton (M := εconcat M₁ M₂)
              (by simpa [εconcat, hyacc])
        · simpa [DFA.eval] using
            εconcat_path_inr M₁ M₂ M₂.start z
#count_heartbeats in --21
theorem econcat_accepts (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (εconcat M₁ M₂).accepts = M₁.accepts * M₂.accepts :=
  εconcat_accepts M₁ M₂

#print axioms econcat_accepts
--'econcat_accepts' depends on axioms: [propext, sorryAx, choice, Quot.sound]
/-Tactic `rewrite` failed: Did not find an occurrence of the pattern
  εNFA.IsPath ?M ?s ?u (?x ++ ?y)
in the target expression
  (εconcat M₁ M₂).IsPath (Sum.inl (M₁.eval y)) (Sum.inr (M₂.eval z)) (List.map some z)

case h.mpr.refine_4.refine_2
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
x y : List α
hy : y ∈ M₁.accepts
z : List α
hz : z ∈ M₂.accepts
hxyz : y ++ z = x
w : List (Option α) := List.map some y ++ [none] ++ List.map some z
⊢ (εconcat M₁ M₂).IsPath (Sum.inl (M₁.eval y)) (Sum.inr (M₂.eval z)) (List.map some z)
Type mismatch: After simplification, term
  εconcat_path_inl M₁ M₂ M₁.start y
 has type
  (εconcat M₁ M₂).IsPath (Sum.inl M₁.start) (Sum.inl (M₁.evalFrom M₁.start y)) (List.map some y)
but is expected to have type
  (εconcat M₁ M₂).IsPath (Sum.inl M₁.start) (Sum.inl (M₁.evalFrom M₁.start y)) (List.map some y ++ [none])
  Tactic `assumption` faileddon't know how to synthesize implicit argument `α`
  @Sum.inr ?m.254 σ₂ (M₂.evalFrom M₂.start w.reduceOption)
context:
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
p q✝ : σ₁ ⊕ σ₂
w✝ : List (Option α)
t q : σ₁ ⊕ σ₂
w : List (Option α)
hp : (εconcat M₁ M₂).IsPath t q w
ih : ∀ (s₁ : σ₁) (s₂ : σ₂),
  t = Sum.inl s₁ →
    q = Sum.inr s₂ → ∃ y z, w.reduceOption = y ++ z ∧ M₁.evalFrom s₁ y ∈ M₁.accept ∧ M₂.evalFrom M₂.start z = s₂
s₁ : σ₁
s₂ : σ₂
hq : q = Sum.inr s₂
ht : t ∈ (εconcat M₁ M₂).step (Sum.inl s₁) none
hacc : s₁ ∈ M₁.accept
ht' : t = Sum.inr M₂.start
hqeval : q = Sum.inr (M₂.evalFrom M₂.start w.reduceOption)
⊢ Type ?u.2257.1997
don't know how to synthesize implicit argument `α`
  @Eq (?m.254 ⊕ σ₂) (Sum.inr s₂) (Sum.inr (M₂.evalFrom M₂.start w.reduceOption))
context:
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
p q✝ : σ₁ ⊕ σ₂
w✝ : List (Option α)
t q : σ₁ ⊕ σ₂
w : List (Option α)
hp : (εconcat M₁ M₂).IsPath t q w
ih : ∀ (s₁ : σ₁) (s₂ : σ₂),
  t = Sum.inl s₁ →
    q = Sum.inr s₂ → ∃ y z, w.reduceOption = y ++ z ∧ M₁.evalFrom s₁ y ∈ M₁.accept ∧ M₂.evalFrom M₂.start z = s₂
s₁ : σ₁
s₂ : σ₂
hq : q = Sum.inr s₂
ht : t ∈ (εconcat M₁ M₂).step (Sum.inl s₁) none
hacc : s₁ ∈ M₁.accept
ht' : t = Sum.inr M₂.start
hqeval : q = Sum.inr (M₂.evalFrom M₂.start w.reduceOption)
⊢ Type (max v ?u.2257.1997)
don't know how to synthesize implicit argument `α`
  @Sum.inr ?m.254 σ₂ s₂
context:
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
p q✝ : σ₁ ⊕ σ₂
w✝ : List (Option α)
t q : σ₁ ⊕ σ₂
w : List (Option α)
hp : (εconcat M₁ M₂).IsPath t q w
ih : ∀ (s₁ : σ₁) (s₂ : σ₂),
  t = Sum.inl s₁ →
    q = Sum.inr s₂ → ∃ y z, w.reduceOption = y ++ z ∧ M₁.evalFrom s₁ y ∈ M₁.accept ∧ M₂.evalFrom M₂.start z = s₂
s₁ : σ₁
s₂ : σ₂
hq : q = Sum.inr s₂
ht : t ∈ (εconcat M₁ M₂).step (Sum.inl s₁) none
hacc : s₁ ∈ M₁.accept
ht' : t = Sum.inr M₂.start
hqeval : q = Sum.inr (M₂.evalFrom M₂.start w.reduceOption)
⊢ Type ?u.2257.1997
-/
