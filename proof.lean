import Mathlib.Computability.DFA
import Mathlib.Computability.NFA
import Mathlib.Computability.EpsilonNFA

set_option profiler true
open Classical Set

variable {α : Type*}

/-- Sipser-style concatenation of two εNFAs. -/
@[simps]
def εconcat (M1 : DFA α σ1) (M2 : DFA α σ2) : εNFA α (σ1 ⊕ σ2) where
step (s : σ1 ⊕ σ2) (a : Option α) :=
by match s, a with
|Sum.inl s1, some as => exact {Sum.inl (M1.step s1 as)}
|Sum.inl s1, none => exact if s1 ∈ M1.accept then {Sum.inr M2.start} else ∅
|Sum.inr s2, some as => exact {Sum.inr (M2.step s2 as)}
|Sum.inr s2, none => exact ∅
start := {Sum.inl M1.start} ∪ if M1.start ∈ M1.accept then {Sum.inr M2.start} else ∅
accept := Sum.inr '' M2.accept
--have h : ∃ r : σ2, t = Sum.inr r :=  right_stays_right q mid string
-- (εconcat M1 M2).IsPath (Sum.inr q) (Sum.inl a) ox

variable {α : Type u} {σ1 σ2 : Type v} (M1 : DFA α σ1) (M2 : DFA α σ2)

@[simp] lemma step_inl_some (q : σ1) (a : α) :
    (εconcat M1 M2).step (Sum.inl q) (some a) = {Sum.inl (M1.step q a)} := by
  rfl  -- fallback: `show {Sum.inl (M1.step q a)} = _; rfl`

@[simp] lemma step_inr_some (q : σ2) (a : α) :
    (εconcat M1 M2).step (Sum.inr q) (some a) = {Sum.inr (M2.step q a)} := by
  rfl

@[simp] lemma step_inr_none (q : σ2) :
    (εconcat M1 M2).step (Sum.inr q) none = ∅ := by
  rfl

lemma step_inl_none_of_accept {q : σ1} (hq : q ∈ M1.accept) :
    (εconcat M1 M2).step (Sum.inl q) none = {Sum.inr M2.start} := by
  change (if q ∈ M1.accept then ({Sum.inr M2.start} : Set _) else ∅) = _
  rw [if_pos hq]

lemma isPath_inl (q : σ1) (x : List α) :
    (εconcat M1 M2).IsPath (Sum.inl q) (Sum.inl (x.foldl M1.step q)) (x.map some) := by
  induction x generalizing q with
  | nil => exact εNFA.IsPath.nil _
  | cons a x ih =>
      -- After definitional unfolding the goal is
      --   IsPath (inl q) (inl (x.foldl M1.step (M1.step q a))) (some a :: x.map some)
      refine εNFA.IsPath.cons
        (Sum.inl (M1.step q a)) _ _ _ _ ?_ (ih (M1.step q a))
      -- Remaining goal: inl (M1.step q a) ∈ (εconcat M1 M2).step (inl q) (some a)
      rw [step_inl_some]
      rfl
lemma isPath_inr (q : σ2) (y : List α) :
    (εconcat M1 M2).IsPath (Sum.inr q) (Sum.inr (y.foldl M2.step q)) (y.map some) := by
  induction y generalizing q with
  | nil => exact εNFA.IsPath.nil _
  | cons a y ih =>
      refine εNFA.IsPath.cons
        (Sum.inr (M2.step q a)) _ _ _ _ ?_ (ih (M2.step q a))
      rw [step_inr_some]
      rfl
lemma isPath_jump {q : σ1} (hq : q ∈ M1.accept) :
    (εconcat M1 M2).IsPath (Sum.inl q) (Sum.inr M2.start) [none] := by
  apply εNFA.IsPath.singleton
  rw [step_inl_none_of_accept _ _ hq]
  rfl

lemma no_right_to_left_path {q : σ2} {r : σ1} {x : List (Option α)} :
    (εconcat M1 M2).IsPath (Sum.inr q) (Sum.inl r) x → False := by
  induction x generalizing q r with
  | nil =>
      intro h
      cases h
  | cons hd xs ih =>
      intro h
      cases h with
      | cons t s u hlabel xs' hstep hpath =>
        cases hd with
          | none =>
              simp [εconcat] at hstep
          | some b =>
              have ht := hstep
              simp only [εconcat] at ht
              rcases ht with rfl
              exact ih hpath

lemma left_path_evalFrom {q r : σ1} {x : List (Option α)} :
    (εconcat M1 M2).IsPath (Sum.inl q) (Sum.inl r) x →
    M1.evalFrom q x.reduceOption = r := by
  induction x generalizing q r with
  | nil =>
      intro h
      cases h
      rfl
  | cons hd xs ih =>
      intro h
      cases h with
      | cons t s u lbl xs' hstep hpath =>
        cases hd with
          | none =>
              have ht : q ∈ M1.accept ∧ t = Sum.inr M2.start := by
                simpa [εconcat] using hstep
              rcases ht with ⟨hacc, rfl⟩
              have hcontra : (εconcat M1 M2).IsPath (Sum.inr M2.start) (Sum.inl r) xs := by
                simpa [εconcat] using hpath
              exact False.elim (no_right_to_left_path (M1 := M1) (M2 := M2) hcontra)
          | some b =>
              have ht : t = Sum.inl (M1.step q b) := by
                simpa [step_inl_some] using hstep
              subst ht
              simpa [DFA.evalFrom, List.reduceOption_cons_of_some] using ih hpath

lemma right_path_evalFrom {q r : σ2} {x : List (Option α)} :
    (εconcat M1 M2).IsPath (Sum.inr q) (Sum.inr r) x →
    M2.evalFrom q x.reduceOption = r := by
  induction x generalizing q r with
  | nil =>
      intro h
      cases h
      rfl
  | cons hd xs ih =>
      intro h
      cases h with
      | cons t s u lbl xs' hstep hpath =>
        cases hd with
          | none =>
          simp [εconcat] at hstep
          | some b =>
              have ht : t = Sum.inr (M2.step q b) := by
                simpa [step_inr_some] using hstep
              subst ht
              simpa [DFA.evalFrom, List.reduceOption_cons_of_some] using ih hpath

lemma cross_path_split {q : σ1} {r : σ2} {x : List (Option α)} :
    (εconcat M1 M2).IsPath (Sum.inl q) (Sum.inr r) x →
    ∃ u v q',
      x = u ++ [none] ++ v ∧
        (εconcat M1 M2).IsPath (Sum.inl q) (Sum.inl q') u ∧
        q' ∈ M1.accept ∧
        (εconcat M1 M2).IsPath (Sum.inr M2.start) (Sum.inr r) v := by
  induction x generalizing q r with
  | nil =>
      intro h
      cases h
  | cons hd xs ih =>
      intro h
      cases h with
      | cons t s u lbl xs' hstep hpath =>
        cases hd with
          | none =>
              have ht : q ∈ M1.accept ∧ t = Sum.inr M2.start := by
                simpa [εconcat] using hstep
              rcases ht with ⟨hacc, rfl⟩
              refine ⟨[], xs, q, by simp, ?_, hacc, ?_⟩
              · exact εNFA.IsPath.nil _
              · simpa using hpath
          | some b =>
              have ht : t = Sum.inl (M1.step q b) := by
                simpa [step_inl_some] using hstep
              subst ht
              rcases ih hpath with ⟨u, v, q', hx, hleft, hacc, hright⟩
              refine ⟨some b :: u, v, q', ?_, ?_, hacc, hright⟩
              · simp [hx]
              · exact εNFA.IsPath.cons _ _ _ _ _ hstep hleft

theorem accepts_mpr {w : List α}
    (hw : w ∈ M1.accepts * M2.accepts) : w ∈ (εconcat M1 M2).accepts := by
  -- Unpack w = x ++ y with hx, hy.  If `Language.mem_mul` lives under a different
  -- name in your snapshot, replace this `rw` accordingly (`Set.mem_mul`, etc.).
  rw [Language.mem_mul] at hw
  obtain ⟨x, hx, y, hy, rfl⟩ := hw
  -- hx : x ∈ M1.accepts  ≡  M1.eval x ∈ M1.accept     (defeq)
  -- hy : y ∈ M2.accepts  ≡  M2.eval y ∈ M2.accept     (defeq)
  rw [εNFA.mem_accepts_iff_exists_path]
  refine ⟨Sum.inl M1.start, Sum.inr (M2.eval y),
          x.map some ++ [none] ++ y.map some,
          ?_, ?_, ?_, ?_⟩
  · -- start membership
    change Sum.inl M1.start ∈ ({Sum.inl M1.start} ∪
        (if M1.start ∈ M1.accept then {Sum.inr M2.start} else ∅) : Set _)
    exact Set.mem_union_left _ rfl
  · -- accept membership
    exact ⟨M2.eval y, hy, rfl⟩
  · -- reduceOption (x.map some ++ [none] ++ y.map some) = x ++ y
    simp [List.reduceOption_append,List.reduceOption_cons_of_none]
    congr
    simp [List.reduceOption, List.filterMap_map]
    simp [List.reduceOption, List.filterMap_map]
  · -- IsPath glue
    rw [εNFA.isPath_append]
    refine ⟨Sum.inr M2.start, ?_, isPath_inr M1 M2 M2.start y⟩
    rw [εNFA.isPath_append]
    refine ⟨Sum.inl (M1.eval x),
            isPath_inl M1 M2 M1.start x,
            isPath_jump M1 M2 hx⟩

theorem εNFA.concat_accepts
    (M1 : DFA α σ1) (M2 : DFA α σ2) :
    (εconcat M1 M2).accepts = M1.accepts * M2.accepts := by
  ext w
  constructor
  · -- (⊆) If N accepts w, split the run at the ε-jump and recover x ∈ L(M₁), y ∈ L(M₂).
    intro hw
    rw [εNFA.mem_accepts_iff_exists_path] at hw
    rcases hw with ⟨s₁, s₂, x', hs₁, hs₂, hx', hpath⟩
    rw [Language.mem_mul]
    have hs₁' : s₁ = Sum.inl M1.start ∨ (M1.start ∈ M1.accept ∧ s₁ = Sum.inr M2.start) := by
      simpa using hs₁
    rcases hs₁' with rfl | ⟨hstartacc, rfl⟩
    · rcases hs₂ with ⟨a, ha, rfl⟩
      rcases cross_path_split (M1 := M1) (M2 := M2) hpath with
        ⟨u, v, q', hxsplit, hleft, hacc, hright⟩
      refine ⟨u.reduceOption, ?_, v.reduceOption, ?_, ?_⟩
      · have heval : M1.eval u.reduceOption = q' := by
          simpa [DFA.eval] using (left_path_evalFrom (M1 := M1) (M2 := M2) hleft)
        rw [DFA.mem_accepts, heval]
        exact hacc
      · have heval : M2.eval v.reduceOption = a := by
          simpa [DFA.eval] using (right_path_evalFrom (M1 := M1) (M2 := M2) hright)
        rw [DFA.mem_accepts, heval]
        exact ha
      · calc
          u.reduceOption ++ v.reduceOption = (u ++ [none] ++ v).reduceOption := by
            simp [List.reduceOption_append, List.reduceOption_cons_of_none]
          _ = x'.reduceOption := by rw [hxsplit]
          _ = w := hx'
    · rcases hs₂ with ⟨a, ha, rfl⟩
      refine ⟨[], ?_, w, ?_, ?_⟩
      · rw [DFA.mem_accepts]
        simpa [DFA.eval] using hstartacc
      · have heval : M2.eval w = a := by
          rw [← hx']
          simpa [DFA.eval] using (right_path_evalFrom (M1 := M1) (M2 := M2) hpath)
        rw [DFA.mem_accepts, heval]
        exact ha
      · simp
  · -- (⊇) If w = x ++ y with x ∈ L(M₁), y ∈ L(M₂), stitch runs together via the ε-jump.
    exact fun a => accepts_mpr M1 M2 a

#print axioms εNFA.concat_accepts
--elaboration took 121ms
--'εNFA.concat_accepts' depends on axioms: [propext, choice, Quot.sound]
