import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.Language
import Lean.Util.Heartbeats


open Classical

noncomputable section

universe u v

variable {α : Type u} {σ₁ σ₂ : Type v}
#count_heartbeats in --134
def εconcat (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : εNFA α (σ₁ ⊕ σ₂) where
  step s a :=
    match s, a with
    | Sum.inl s₁, some c => {Sum.inl (M₁.step s₁ c)}
    | Sum.inl s₁, none => if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅
    | Sum.inr s₂, some c => {Sum.inr (M₂.step s₂ c)}
    | Sum.inr _ , none => ∅
  start :=
    insert (Sum.inl M₁.start)
      (if M₁.start ∈ M₁.accept then ({Sum.inr M₂.start} : Set (σ₁ ⊕ σ₂)) else ∅)
  accept := Sum.inr '' M₂.accept
#count_heartbeats in --24
lemma εconcat_inl_mem_εClosure_iff
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    {S : Set (σ₁ ⊕ σ₂)} {q : σ₁} :
    Sum.inl q ∈ (εconcat M₁ M₂).εClosure S ↔ Sum.inl q ∈ S := by
  constructor
  · intro h
    have hgen :
        ∀ z : σ₁ ⊕ σ₂,
          z ∈ (εconcat M₁ M₂).εClosure S →
            ∀ q : σ₁, z = Sum.inl q → Sum.inl q ∈ S := by
      intro z hz
      induction hz with
      | base z hz =>
          intro q hzq
          simpa [hzq] using hz
      | step s t ht hs ih =>
          intro q htq
          cases s with
          | inl p =>
              by_cases hp : p ∈ M₁.accept
              · have ht' : t = Sum.inr M₂.start := by
                  simpa [εconcat, hp] using ht
                rw [ht'] at htq
                cases htq
              · have hfalse : False := by
                  simpa [εconcat, hp] using ht
                exact False.elim hfalse
          | inr p =>
              have hfalse : False := by
                simpa [εconcat] using ht
              exact False.elim hfalse
    exact hgen (Sum.inl q) h q rfl
  · intro h
    exact εNFA.εClosure.base (Sum.inl q) h
#count_heartbeats in --39
lemma εconcat_inr_mem_εClosure_iff
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    {S : Set (σ₁ ⊕ σ₂)} {r : σ₂} :
    Sum.inr r ∈ (εconcat M₁ M₂).εClosure S ↔
      Sum.inr r ∈ S ∨
        r = M₂.start ∧ ∃ q : σ₁, q ∈ M₁.accept ∧ Sum.inl q ∈ S := by
  constructor
  · intro h
    have hgen :
        ∀ z : σ₁ ⊕ σ₂,
          z ∈ (εconcat M₁ M₂).εClosure S →
            z ∈ S ∨
              ∃ q : σ₁,
                q ∈ M₁.accept ∧ Sum.inl q ∈ S ∧ z = Sum.inr M₂.start := by
      intro z hz
      induction hz with
      | base z hz =>
          exact Or.inl hz
      | step s t ht hs ih =>
          cases s with
          | inl p =>
              by_cases hp : p ∈ M₁.accept
              · have ht' : t = Sum.inr M₂.start := by
                  simpa [εconcat, hp] using ht
                have hsS : Sum.inl p ∈ S :=
                  (εconcat_inl_mem_εClosure_iff M₁ M₂).mp hs
                exact Or.inr ⟨p, hp, hsS, ht'⟩
              · have hfalse : False := by
                  simpa [εconcat, hp] using ht
                exact False.elim hfalse
          | inr p =>
              have hfalse : False := by
                simpa [εconcat] using ht
              exact False.elim hfalse
    rcases hgen (Sum.inr r) h with hS | ⟨q, hq, hqS, hz⟩
    · exact Or.inl hS
    · cases hz
      exact Or.inr ⟨rfl, q, hq, hqS⟩
  · rintro (hS | ⟨hr, q, hq, hqS⟩)
    · exact εNFA.εClosure.base (Sum.inr r) hS
    · subst r
      exact
        εNFA.εClosure.step
          (Sum.inl q)
          (Sum.inr M₂.start)
          (by simp [εconcat, hq])
          (εNFA.εClosure.base (Sum.inl q) hqS)
#count_heartbeats in --21
lemma εconcat_eval_inl_iff
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    {x : List α} {q : σ₁} :
    Sum.inl q ∈ (εconcat M₁ M₂).eval x ↔ q = M₁.eval x := by
  induction x using List.reverseRecOn generalizing q with
  | nil =>
      simp [εconcat, εconcat_inl_mem_εClosure_iff]
  | append_singleton x a ih =>
      rw [εNFA.eval_append_singleton, DFA.eval_append_singleton]
      constructor
      · intro h
        rw [εNFA.mem_stepSet_iff] at h
        rcases h with ⟨s, hs, hcl⟩
        cases s with
        | inl q₀ =>
            rw [εconcat_inl_mem_εClosure_iff] at hcl
            have hstep : q = M₁.step q₀ a := by
              simpa [εconcat] using hcl
            have hq₀ : q₀ = M₁.eval x := (ih (q := q₀)).mp hs
            simpa [hstep, hq₀]
        | inr r₀ =>
            rw [εconcat_inl_mem_εClosure_iff] at hcl
            have hfalse : False := by
              simpa [εconcat] using hcl
            exact False.elim hfalse
      · intro hq
        subst q
        rw [εNFA.mem_stepSet_iff]
        refine ⟨Sum.inl (M₁.eval x), ?_, ?_⟩
        · exact (ih (q := M₁.eval x)).mpr rfl
        · rw [εconcat_inl_mem_εClosure_iff]
          simp [εconcat]
#count_heartbeats in --42
lemma εconcat_eval_inr_sound
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    {x : List α} {r : σ₂}
    (h : Sum.inr r ∈ (εconcat M₁ M₂).eval x) :
    ∃ a : List α, a ∈ M₁.accepts ∧
      ∃ b : List α, M₂.eval b = r ∧ a ++ b = x := by
  induction x using List.reverseRecOn generalizing r with
  | nil =>
      rw [εNFA.eval_nil] at h
      rw [εconcat_inr_mem_εClosure_iff] at h
      rcases h with hstart | ⟨hr, q, hq, hqstart⟩
      · by_cases hacc : M₁.start ∈ M₁.accept
        · have hr' : r = M₂.start := by
            simpa [εconcat, hacc] using hstart
          refine ⟨[], ?_, [], ?_, by simp⟩
          · exact (DFA.mem_accepts M₁).mpr (by simpa [DFA.eval] using hacc)
          · simp [DFA.eval, hr']
        · have hfalse : False := by
            simpa [εconcat, hacc] using hstart
          exact False.elim hfalse
      · have hqeq : q = M₁.start := by
          simpa [εconcat] using hqstart
        have hacc : M₁.start ∈ M₁.accept := by
          simpa [hqeq] using hq
        refine ⟨[], ?_, [], ?_, by simp⟩
        · exact (DFA.mem_accepts M₁).mpr (by simpa [DFA.eval] using hacc)
        · simp [DFA.eval, hr]
  | append_singleton x a ih =>
      rw [εNFA.eval_append_singleton] at h
      rw [εNFA.mem_stepSet_iff] at h
      rcases h with ⟨s, hs, hcl⟩
      cases s with
      | inl q =>
          rw [εconcat_inr_mem_εClosure_iff] at hcl
          rcases hcl with hstep | ⟨hr, q', hqacc, hqstep⟩
          · have hfalse : False := by
              simpa [εconcat] using hstep
            exact False.elim hfalse
          · have hqstep' : q' = M₁.step q a := by
              simpa [εconcat] using hqstep
            have hqeval : q = M₁.eval x :=
              (εconcat_eval_inl_iff M₁ M₂ (x := x) (q := q)).mp hs
            refine ⟨x ++ [a], ?_, [], ?_, by simp⟩
            · exact (DFA.mem_accepts M₁).mpr (by
                rw [DFA.eval_append_singleton]
                simpa [hqeval, hqstep'] using hqacc)
            · simp [DFA.eval, hr]
      | inr p =>
          rw [εconcat_inr_mem_εClosure_iff] at hcl
          rcases hcl with hstep | ⟨hr, q, hqacc, hqstep⟩
          · have hrstep : r = M₂.step p a := by
              simpa [εconcat] using hstep
            obtain ⟨pref, hpref, suf, hsuf, hcat⟩ := ih hs
            refine ⟨pref, hpref, suf ++ [a], ?_, ?_⟩
            · rw [DFA.eval_append_singleton, hsuf, hrstep]
            · rw [← List.append_assoc, hcat]
          · have hfalse : False := by
              simpa [εconcat] using hqstep
            exact False.elim hfalse
#count_heartbeats in --26
lemma εconcat_eval_inr_start_of_accept
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    {x : List α} (hx : x ∈ M₁.accepts) :
    Sum.inr M₂.start ∈ (εconcat M₁ M₂).eval x := by
  induction x using List.reverseRecOn with
  | nil =>
      have hacc : M₁.start ∈ M₁.accept := by
        simpa [DFA.eval] using (DFA.mem_accepts M₁).mp hx
      rw [εNFA.eval_nil]
      rw [εconcat_inr_mem_εClosure_iff]
      left
      simp [εconcat, hacc]
  | append_singleton x a _ =>
      have hacc : M₁.step (M₁.eval x) a ∈ M₁.accept := by
        simpa [DFA.eval_append_singleton] using (DFA.mem_accepts M₁).mp hx
      rw [εNFA.eval_append_singleton]
      rw [εNFA.mem_stepSet_iff]
      refine ⟨Sum.inl (M₁.eval x), ?_, ?_⟩
      · exact (εconcat_eval_inl_iff M₁ M₂ (x := x) (q := M₁.eval x)).mpr rfl
      · rw [εconcat_inr_mem_εClosure_iff]
        right
        refine ⟨rfl, M₁.step (M₁.eval x) a, hacc, ?_⟩
        simp [εconcat]
#count_heartbeats in --39
lemma εconcat_eval_inr_run
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    {x : List α} {p : σ₂}
    (hp : Sum.inr p ∈ (εconcat M₁ M₂).eval x)
    (y : List α) :
    Sum.inr (M₂.evalFrom p y) ∈ (εconcat M₁ M₂).eval (x ++ y) := by
  induction y using List.reverseRecOn with
  | nil =>
      simpa using hp
  | append_singleton y a ih =>
      rw [← List.append_assoc]
      rw [εNFA.eval_append_singleton, DFA.evalFrom_append_singleton]
      rw [εNFA.mem_stepSet_iff]
      refine ⟨Sum.inr (M₂.evalFrom p y), ih, ?_⟩
      rw [εconcat_inr_mem_εClosure_iff]
      left
      simp [εconcat]
#count_heartbeats in --36
lemma εconcat_eval_inr_complete
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    {a b : List α} (ha : a ∈ M₁.accepts) :
    Sum.inr (M₂.eval b) ∈ (εconcat M₁ M₂).eval (a ++ b) := by
  simpa [DFA.eval] using
    (εconcat_eval_inr_run M₁ M₂
      (x := a)
      (p := M₂.start)
      (εconcat_eval_inr_start_of_accept M₁ M₂ ha)
      b)

#count_heartbeats in --21 heartbeats
theorem εconcat_accepts (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (εconcat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext x
  constructor
  · intro hx
    change ∃ s : σ₁ ⊕ σ₂,
      s ∈ (εconcat M₁ M₂).accept ∧
        s ∈ (εconcat M₁ M₂).eval x at hx
    rcases hx with ⟨s, hsacc, hs⟩
    change s ∈ Sum.inr '' M₂.accept at hsacc
    rcases hsacc with ⟨r, hr, rfl⟩
    obtain ⟨a, ha, b, hb, hcat⟩ :=
      εconcat_eval_inr_sound M₁ M₂ hs
    rw [Language.mem_mul]
    refine ⟨a, ha, b, ?_, hcat⟩
    exact (DFA.mem_accepts M₂).mpr (by simpa [hb] using hr)
  · intro hx
    rw [Language.mem_mul] at hx
    rcases hx with ⟨a, ha, b, hb, hcat⟩
    change ∃ s : σ₁ ⊕ σ₂,
      s ∈ (εconcat M₁ M₂).accept ∧
        s ∈ (εconcat M₁ M₂).eval x
    refine ⟨Sum.inr (M₂.eval b), ?_, ?_⟩
    · change Sum.inr (M₂.eval b) ∈ Sum.inr '' M₂.accept
      exact ⟨M₂.eval b, (DFA.mem_accepts M₂).mp hb, rfl⟩
    · simpa [hcat] using
        (εconcat_eval_inr_complete M₁ M₂ (a := a) (b := b) ha)

end

#print axioms εconcat_accepts
--'econcat_accepts' depends on axioms: [propext, sorryAx, choice, Quot.sound]
/-unsolved goals
case nil
α : Type u
σ₁ σ₂ : Type v
M₁ : DFA α σ₁
M₂ : DFA α σ₂
q : σ₁
⊢ Sum.inl q ∈
    {
          step := fun s a ↦
            match s, a with
            | Sum.inl s₁, some c => {Sum.inl (M₁.step s₁ c)}
            | Sum.inl s₁, none => if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅
            | Sum.inr s₂, some c => {Sum.inr (M₂.step s₂ c)}
            | Sum.inr val, none => ∅,
          start := insert (Sum.inl M₁.start) (if M₁.start ∈ M₁.accept then {Sum.inr M₂.start} else ∅),
          accept := Sum.inr '' M₂.accept }.εClosure
      (insert (Sum.inl M₁.start) (if M₁.start ∈ M₁.accept then {Sum.inr M₂.start} else ∅)) ↔
  q = M₁.start-/
