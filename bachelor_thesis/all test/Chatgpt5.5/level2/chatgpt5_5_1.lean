import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.Language

open Classical
open Set

universe u v

noncomputable section

variable {α : Type u} {σ₁ σ₂ : Type v}
#count_heartbeats in --139
def εconcat (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : εNFA α (σ₁ ⊕ σ₂) where
  step s a :=
    match s, a with
    | Sum.inl s₁, some c => {Sum.inl (M₁.step s₁ c)}
    | Sum.inl s₁, none => if s₁ ∈ M₁.accept then {Sum.inr M₂.start} else ∅
    | Sum.inr s₂, some c => {Sum.inr (M₂.step s₂ c)}
    | Sum.inr _ , none => ∅
  start :=
    insert (Sum.inl M₁.start)
      (if M₁.start ∈ M₁.accept then
        ({Sum.inr M₂.start} : Set (σ₁ ⊕ σ₂))
      else
        ∅)
  accept := Sum.inr '' M₂.accept
#count_heartbeats in --44
private lemma εconcat_mem_εClosure_singleton_left
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s₁ : σ₁) (q : σ₁ ⊕ σ₂) :
    q ∈ (εconcat M₁ M₂).εClosure ({Sum.inl s₁} : Set (σ₁ ⊕ σ₂)) ↔
      q = Sum.inl s₁ ∨ s₁ ∈ M₁.accept ∧ q = Sum.inr M₂.start := by
  constructor
  · intro h
    induction h with
    | base q hq =>
        left
        simpa using hq
    | step s t hst hs ih =>
        rcases ih with rfl | ⟨hsacc, rfl⟩
        · by_cases hsacc : s₁ ∈ M₁.accept
          · right
            refine ⟨hsacc, ?_⟩
            simpa [εconcat, hsacc] using hst
          · exfalso
            simpa [εconcat, hsacc] using hst
        · exfalso
          simpa [εconcat] using hst
  · rintro (rfl | ⟨hsacc, rfl⟩)
    · exact εNFA.εClosure.base _ (by simp)
    · exact
        εNFA.εClosure.step
          (Sum.inl s₁)
          (Sum.inr M₂.start)
          (by simp [εconcat, hsacc])
          (εNFA.εClosure.base _ (by simp))
#count_heartbeats in --31
private lemma εconcat_mem_εClosure_singleton_right
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (s₂ : σ₂) (q : σ₁ ⊕ σ₂) :
    q ∈ (εconcat M₁ M₂).εClosure ({Sum.inr s₂} : Set (σ₁ ⊕ σ₂)) ↔
      q = Sum.inr s₂ := by
  constructor
  · intro h
    induction h with
    | base q hq =>
        simpa using hq
    | step s t hst hs ih =>
        cases ih
        exfalso
        simpa [εconcat] using hst
  · intro h
    subst q
    exact εNFA.εClosure.base _ (by simp)
#count_heartbeats in --39
private lemma εconcat_mem_εClosure_start
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (q : σ₁ ⊕ σ₂) :
    q ∈ (εconcat M₁ M₂).εClosure (εconcat M₁ M₂).start ↔
      q = Sum.inl M₁.start ∨
        M₁.start ∈ M₁.accept ∧ q = Sum.inr M₂.start := by
  constructor
  · intro h
    induction h with
    | base q hq =>
        by_cases hstart : M₁.start ∈ M₁.accept
        · simp [εconcat, hstart] at hq ⊢
          exact hq
        · simp [εconcat, hstart] at hq ⊢
          exact hq
    | step s t hst hs ih =>
        rcases ih with rfl | ⟨hstart, rfl⟩
        · by_cases hstart : M₁.start ∈ M₁.accept
          · right
            refine ⟨hstart, ?_⟩
            simpa [εconcat, hstart] using hst
          · exfalso
            simpa [εconcat, hstart] using hst
        · exfalso
          simpa [εconcat] using hst
  · rintro (rfl | ⟨hstart, rfl⟩)
    · exact εNFA.εClosure.base _ (by simp [εconcat])
    · exact εNFA.εClosure.base _ (by simp [εconcat, hstart])
#count_heartbeats in --53
private lemma εconcat_eval_iff
    (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    ∀ (x : List α) (q : σ₁ ⊕ σ₂),
      q ∈ (εconcat M₁ M₂).eval x ↔
        q = Sum.inl (M₁.eval x) ∨
          ∃ y z,
            x = y ++ z ∧
              M₁.eval y ∈ M₁.accept ∧
                q = Sum.inr (M₂.eval z) := by
  intro x
  induction x using List.reverseRecOn with
  | nil =>
      intro q
      rw [εNFA.eval_nil, εconcat_mem_εClosure_start]
      constructor
      · rintro (hq | ⟨hacc, hq⟩)
        · left
          simpa using hq
        · right
          refine ⟨[], [], by simp, ?_, ?_⟩
          · simpa using hacc
          · simpa using hq
      · rintro (hq | ⟨y, z, hxz, hacc, hq⟩)
        · left
          simpa using hq
        · have hyz : y = [] ∧ z = [] := by
            simpa using (List.nil_eq_append_iff.mp hxz)
          rcases hyz with ⟨rfl, rfl⟩
          right
          exact ⟨by simpa using hacc, by simpa using hq⟩
  | append_singleton x a ih =>
      intro q
      rw [εNFA.eval_append_singleton]
      constructor
      · intro hq
        rw [εNFA.mem_stepSet_iff] at hq
        rcases hq with ⟨t, ht, hcl⟩
        rcases (ih t).mp ht with htleft | ⟨y, z, hxz, hacc, htinr⟩
        · subst t
          have hcl' :
              q ∈ (εconcat M₁ M₂).εClosure
                ({Sum.inl (M₁.step (M₁.eval x) a)} : Set (σ₁ ⊕ σ₂)) := by
            simpa [εconcat] using hcl
          rcases
              (εconcat_mem_εClosure_singleton_left M₁ M₂
                (M₁.step (M₁.eval x) a) q).mp hcl'
            with hqleft | ⟨hacc', hqright⟩
          · left
            simpa [DFA.eval_append_singleton] using hqleft
          · right
            refine ⟨x ++ [a], [], by simp, ?_, ?_⟩
            · simpa [DFA.eval_append_singleton] using hacc'
            · simpa using hqright
        · subst t
          have hcl' :
              q ∈ (εconcat M₁ M₂).εClosure
                ({Sum.inr (M₂.step (M₂.eval z) a)} : Set (σ₁ ⊕ σ₂)) := by
            simpa [εconcat] using hcl
          have hqstep :=
            (εconcat_mem_εClosure_singleton_right M₁ M₂
              (M₂.step (M₂.eval z) a) q).mp hcl'
          right
          refine ⟨y, z ++ [a], ?_, hacc, ?_⟩
          · rw [hxz]
            simp [List.append_assoc]
          · simpa [DFA.eval_append_singleton] using hqstep
      · intro hq
        rw [εNFA.mem_stepSet_iff]
        rcases hq with hqleft | ⟨y, z, hxz, hacc, hqright⟩
        · subst q
          refine ⟨Sum.inl (M₁.eval x), ?_, ?_⟩
          · exact (ih _).mpr (Or.inl rfl)
          · have hcl' :
              Sum.inl (M₁.eval (x ++ [a])) ∈
                (εconcat M₁ M₂).εClosure
                  ({Sum.inl (M₁.step (M₁.eval x) a)} : Set (σ₁ ⊕ σ₂)) := by
              apply
                (εconcat_mem_εClosure_singleton_left M₁ M₂
                  (M₁.step (M₁.eval x) a)
                  (Sum.inl (M₁.eval (x ++ [a])))).mpr
              left
              simp [DFA.eval_append_singleton]
            simpa [εconcat] using hcl'
        · have hsplit :
              (z = [] ∧ y = x ++ [a]) ∨
                ∃ z', z = z' ++ [a] ∧ x = y ++ z' := by
            rcases (List.append_eq_append_iff.mp hxz) with
              ⟨as, hy, ha⟩ | ⟨bs, hx, hz⟩
            · rcases (List.singleton_eq_append_iff.mp ha) with
                ⟨has, hz⟩ | ⟨has, hz⟩
              · right
                refine ⟨[], ?_, ?_⟩
                · simpa [hz]
                · simpa [hy, has]
              · left
                constructor
                · exact hz
                · simpa [hy, has]
            · right
              exact ⟨bs, hz, hx⟩
          rcases hsplit with ⟨hz, hy⟩ | ⟨z', hz, hx⟩
          · subst z
            subst y
            refine ⟨Sum.inl (M₁.eval x), ?_, ?_⟩
            · exact (ih _).mpr (Or.inl rfl)
            · have hcl' :
                q ∈ (εconcat M₁ M₂).εClosure
                  ({Sum.inl (M₁.step (M₁.eval x) a)} : Set (σ₁ ⊕ σ₂)) := by
                apply
                  (εconcat_mem_εClosure_singleton_left M₁ M₂
                    (M₁.step (M₁.eval x) a) q).mpr
                right
                constructor
                · simpa [DFA.eval_append_singleton] using hacc
                · simpa using hqright
              simpa [εconcat] using hcl'
          · subst z
            refine ⟨Sum.inr (M₂.eval z'), ?_, ?_⟩
            · exact (ih _).mpr (Or.inr ⟨y, z', hx, hacc, rfl⟩)
            · have hcl' :
                q ∈ (εconcat M₁ M₂).εClosure
                  ({Sum.inr (M₂.step (M₂.eval z') a)} : Set (σ₁ ⊕ σ₂)) := by
                apply
                  (εconcat_mem_εClosure_singleton_right M₁ M₂
                    (M₂.step (M₂.eval z') a) q).mpr
                simpa [DFA.eval_append_singleton] using hqright
              simpa [εconcat] using hcl'

#count_heartbeats in -- 22 heartbeats
theorem εconcat_accepts (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (εconcat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext x
  constructor
  · intro hx
    rw [εNFA.accepts] at hx
    rcases hx with ⟨q, hqacc, hqeval⟩
    simp [εconcat] at hqacc
    rcases hqacc with ⟨s₂, hs₂, hq⟩
    subst q
    rcases
        (εconcat_eval_iff M₁ M₂ x (Sum.inr s₂)).mp hqeval
      with hbad | ⟨y, z, hxz, hacc₁, hqz⟩
    · cases hbad
    · cases hqz
      rw [Language.mul_def]
      refine ⟨y, ?_, z, ?_, ?_⟩
      · exact (DFA.mem_accepts M₁).mpr hacc₁
      · exact (DFA.mem_accepts M₂).mpr (by simpa using hs₂)
      · exact hxz.symm
  · intro hx
    rw [Language.mul_def] at hx
    rcases hx with ⟨y, hy, z, hz, hconcat⟩
    subst x
    rw [εNFA.accepts]
    refine ⟨Sum.inr (M₂.eval z), ?_, ?_⟩
    · change Sum.inr (M₂.eval z) ∈ Sum.inr '' M₂.accept
      exact ⟨M₂.eval z, (DFA.mem_accepts M₂).mp hz, rfl⟩
    · exact
        (εconcat_eval_iff M₁ M₂ (y ++ z) (Sum.inr (M₂.eval z))).mpr
          (Or.inr ⟨y, z, rfl, (DFA.mem_accepts M₁).mp hy, rfl⟩)

#print axioms εconcat_accepts
--'εconcat_accepts' depends on axioms: [propext, choice, Quot.sound]
--none all of them are regular liner warnings about using simp only and simp at hst
--instead of simpa using hst
