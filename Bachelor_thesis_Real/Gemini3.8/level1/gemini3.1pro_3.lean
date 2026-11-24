import Mathlib.Computability.Language
import Mathlib.Computability.DFA
import Mathlib.Computability.NFA
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Powerset

open Set Language
open Classical

universe u

variable {T : Type u}
#count_heartbeats in --119
/-- An NFA that represents the concatenation of two DFAs. -/
def concatNFA {σ1 σ2 : Type*} (M1 : DFA T σ1) (M2 : DFA T σ2) : NFA T (σ1 ⊕ σ2) where
  step s a := match s with
    | Sum.inl s1 => if M1.step s1 a ∈ M1.accept then {Sum.inl (M1.step s1 a)} ∪ {Sum.inr M2.start} else {Sum.inl (M1.step s1 a)}
    | Sum.inr s2 => {Sum.inr (M2.step s2 a)}
  start := if M1.start ∈ M1.accept then {Sum.inl M1.start} ∪ {Sum.inr M2.start} else {Sum.inl M1.start}
  accept := Sum.inr '' M2.accept
#count_heartbeats in --29
/-- The evaluation of the concatenation NFA from a state in `Sum.inr` behaves exactly like `M2`. -/
theorem evalFrom_inr {σ1 σ2 : Type*} (M1 : DFA T σ1) (M2 : DFA T σ2) (s2 : σ2) (x : List T) :
    (concatNFA M1 M2).evalFrom {Sum.inr s2} x = {Sum.inr (M2.evalFrom s2 x)} := by
  induction x generalizing s2 with
  | nil => rfl
  | cons a x ih => simp [NFA.evalFrom_cons, NFA.stepSet_singleton, concatNFA, ih]
#count_heartbeats in --64
/-- Characterization of the states reachable in the concatenation NFA when starting from `Sum.inl`. -/
theorem mem_evalFrom_inl {σ1 σ2 : Type*} [Fintype σ1] [Fintype σ2]
    (M1 : DFA T σ1) (M2 : DFA T σ2) (s1 : σ1) (t2 : σ2) (x : List T) :
    Sum.inr t2 ∈ (concatNFA M1 M2).evalFrom {Sum.inl s1} x ↔
    ∃ u v, x = u ++ v ∧ u ≠ [] ∧ M1.evalFrom s1 u ∈ M1.accept ∧ t2 = M2.evalFrom M2.start v := by
  induction x generalizing s1 with
  | nil =>
    simp [NFA.evalFrom_nil]
    constructor
    · intro h; simp at h
    · rintro ⟨u, v, h, hu, _, _⟩
      cases u with
      | nil => exact hu rfl
      | cons _ _ => contradiction
  | cons a x ih =>
    simp [NFA.evalFrom_cons, NFA.stepSet_singleton, concatNFA]
    split_ifs with h_accept
    · rw [NFA.evalFrom_union, Set.mem_union, ih, evalFrom_inr, Set.mem_singleton_iff]
      constructor
      · rintro (⟨u, v, rfl, hu, h1, rfl⟩ | rfl)
        · refine ⟨a :: u, v, rfl, by simp, ?_, rfl⟩
          rwa [DFA.evalFrom_cons]
        · refine ⟨[a], x, rfl, by simp, ?_, rfl⟩
          simp [DFA.evalFrom_nil, DFA.evalFrom_cons, h_accept]
      · rintro ⟨u, v, h, hu, h1, rfl⟩
        cases u with
        | nil => exact (hu rfl).elim
        | cons b u =>
          simp only [List.cons_append, List.cons_eq_cons] at h
          rcases h with ⟨rfl, rfl⟩
          cases u with
          | nil =>
            right
            simp only [DFA.evalFrom_nil, DFA.evalFrom_cons] at h1
            rfl
          | cons c u =>
            left
            refine ⟨c :: u, v, rfl, by simp, ?_, rfl⟩
            rwa [DFA.evalFrom_cons] at h1
    · rw [ih]
      constructor
      · rintro ⟨u, v, rfl, hu, h1, rfl⟩
        refine ⟨a :: u, v, rfl, by simp, ?_, rfl⟩
        rwa [DFA.evalFrom_cons]
      · rintro ⟨u, v, h, hu, h1, rfl⟩
        cases u with
        | nil => exact (hu rfl).elim
        | cons b u =>
          simp only [List.cons_append, List.cons_eq_cons] at h
          rcases h with ⟨rfl, rfl⟩
          cases u with
          | nil =>
            simp only [DFA.evalFrom_nil, DFA.evalFrom_cons] at h1
            exact (h_accept h1).elim
          | cons c u =>
            refine ⟨c :: u, v, rfl, by simp, ?_, rfl⟩
            rwa [DFA.evalFrom_cons] at h1
#count_heartbeats in --25
/-- The language accepted by `concatNFA M1 M2` is exactly `M1.accepts * M2.accepts`. -/
theorem concatNFA_correct {σ1 σ2 : Type*} [Fintype σ1] [Fintype σ2] (M1 : DFA T σ1) (M2 : DFA T σ2) :
    (concatNFA M1 M2).accepts = M1.accepts * M2.accepts := by
  ext x
  simp only [NFA.mem_accepts, concatNFA, Set.mem_image, NFA.eval, Language.mem_mul, DFA.mem_accepts, DFA.eval]
  constructor
  · rintro ⟨t2, ht2, h_eval⟩
    split_ifs at h_eval with h_start
    · rw [NFA.evalFrom_union, Set.mem_union] at h_eval
      rcases h_eval with h_inl | h_inr
      · rw [mem_evalFrom_inl M1 M2] at h_inl
        rcases h_inl with ⟨u, v, rfl, hu, h1, rfl⟩
        exact ⟨u, h1, v, ht2, rfl⟩
      · rw [evalFrom_inr M1 M2, Set.mem_singleton_iff] at h_inr
        subst h_inr
        exact ⟨[], h_start, x, ht2, rfl⟩
    · rw [mem_evalFrom_inl M1 M2] at h_eval
      rcases h_eval with ⟨u, v, rfl, hu, h1, rfl⟩
      exact ⟨u, h1, v, ht2, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    split_ifs with h_start
    · refine ⟨M2.evalFrom M2.start v, hv, ?_⟩
      rw [NFA.evalFrom_union, Set.mem_union]
      cases u with
      | nil =>
        right
        rw [evalFrom_inr M1 M2, Set.mem_singleton_iff]
      | cons a u =>
        left
        rw [mem_evalFrom_inl M1 M2]
        refine ⟨a :: u, v, rfl, by simp, hu, rfl⟩
    · refine ⟨M2.evalFrom M2.start v, hv, ?_⟩
      rw [mem_evalFrom_inl M1 M2]
      cases u with
      | nil =>
        simp only [DFA.evalFrom_nil] at hu
        exact (h_start hu).elim
      | cons a u =>
        refine ⟨a :: u, v, rfl, by simp, hu, rfl⟩

#count_heartbeats in --23 heartbeats
/-- Regular languages are closed under concatenation. -/
theorem IsRegular.mul1 {L1 L2 : Language T} (h1 : L1.IsRegular) (h2 : L2.IsRegular) :
    (L1 * L2).IsRegular := by
  rcases h1 with ⟨σ1, inst1, M1, rfl⟩
  rcases h2 with ⟨σ2, inst2, M2, rfl⟩
  rw [← concatNFA_correct M1 M2]
  rw [Language.isRegular_iff]
  refine ⟨Set (σ1 ⊕ σ2), inferInstance, (concatNFA M1 M2).toDFA, ?_⟩
  exact NFA.toDFA_correct (concatNFA M1 M2)


#print axioms IsRegular.mul1
--[propext, sorryAx, choice, Quot.sound]
/-Function expected at
  NFA.toDFA_correct
but this term has type
  (NFA.toDFA ?m.90).accepts = NFA.accepts ?m.90

Note: Expected a function because this term is being applied to the argument
  (concatNFA M1 M2)
Used 23 heartbeats, which is less than the current maximum of 200000.
Application type mismatch: The argument
  M2.evalFrom M2.start v
has type
  σ2
of sort `Type u_2` but is expected to have type
  σ1 ⊕ σ2
of sort `Type (max u_1 u_2)` in the application
  Exists.intro (M2.evalFrom M2.start v)
Application type mismatch: The argument
  M2.evalFrom M2.start v
has type
  σ2
of sort `Type u_2` but is expected to have type
  σ1 ⊕ σ2
of sort `Type (max u_1 u_2)` in the application
  Exists.intro (M2.evalFrom M2.start v)
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  Sum.inr ?t2 ∈ (concatNFA M1 M2).evalFrom {Sum.inl ?s1} ?x
in the target expression
  t2 ∈
    {
          step := fun s a ↦
            match s with
            | Sum.inl s1 =>
              if M1.step s1 a ∈ M1.accept then {Sum.inl (M1.step s1 a)} ∪ {Sum.inr M2.start}
              else {Sum.inl (M1.step s1 a)}
            | Sum.inr s2 => {Sum.inr (M2.step s2 a)},
          start := {Sum.inl M1.start}, accept := Sum.inr '' M2.accept }.evalFrom
      {Sum.inl M1.start} x

case neg
T : Type u
σ1 : Type u_1
σ2 : Type u_2
inst✝¹ : Fintype σ1
inst✝ : Fintype σ2
M1 : DFA T σ1
M2 : DFA T σ2
x : List T
t2 : σ1 ⊕ σ2
ht2 : ∃ x ∈ M2.accept, Sum.inr x = t2
h_start : M1.start ∉ M1.accept
h_eval : t2 ∈
  {
        step := fun s a ↦
          match s with
          | Sum.inl s1 =>
            if M1.step s1 a ∈ M1.accept then {Sum.inl (M1.step s1 a)} ∪ {Sum.inr M2.start} else {Sum.inl (M1.step s1 a)}
          | Sum.inr s2 => {Sum.inr (M2.step s2 a)},
        start := {Sum.inl M1.start}, accept := Sum.inr '' M2.accept }.evalFrom
    {Sum.inl M1.start} x
⊢ ∃ a, M1.evalFrom M1.start a ∈ M1.accept ∧ ∃ b, M2.evalFrom M2.start b ∈ M2.accept ∧ a ++ b = x
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (concatNFA M1 M2).evalFrom {Sum.inr ?s2} ?x
in the target expression
  t2 ∈
    {
          step := fun s a ↦
            match s with
            | Sum.inl s1 =>
              if M1.step s1 a ∈ M1.accept then {Sum.inl (M1.step s1 a)} ∪ {Sum.inr M2.start}
              else {Sum.inl (M1.step s1 a)}
            | Sum.inr s2 => {Sum.inr (M2.step s2 a)},
          start := {Sum.inl M1.start} ∪ {Sum.inr M2.start}, accept := Sum.inr '' M2.accept }.evalFrom
      {Sum.inr M2.start} x

case pos.inr
T : Type u
σ1 : Type u_1
σ2 : Type u_2
inst✝¹ : Fintype σ1
inst✝ : Fintype σ2
M1 : DFA T σ1
M2 : DFA T σ2
x : List T
t2 : σ1 ⊕ σ2
ht2 : ∃ x ∈ M2.accept, Sum.inr x = t2
h_start : M1.start ∈ M1.accept
h_inr : t2 ∈
  {
        step := fun s a ↦
          match s with
          | Sum.inl s1 =>
            if M1.step s1 a ∈ M1.accept then {Sum.inl (M1.step s1 a)} ∪ {Sum.inr M2.start} else {Sum.inl (M1.step s1 a)}
          | Sum.inr s2 => {Sum.inr (M2.step s2 a)},
        start := {Sum.inl M1.start} ∪ {Sum.inr M2.start}, accept := Sum.inr '' M2.accept }.evalFrom
    {Sum.inr M2.start} x
⊢ ∃ a, M1.evalFrom M1.start a ∈ M1.accept ∧ ∃ b, M2.evalFrom M2.start b ∈ M2.accept ∧ a ++ b = x
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  Sum.inr ?t2 ∈ (concatNFA M1 M2).evalFrom {Sum.inl ?s1} ?x
in the target expression
  t2 ∈
    {
          step := fun s a ↦
            match s with
            | Sum.inl s1 =>
              if M1.step s1 a ∈ M1.accept then {Sum.inl (M1.step s1 a)} ∪ {Sum.inr M2.start}
              else {Sum.inl (M1.step s1 a)}
            | Sum.inr s2 => {Sum.inr (M2.step s2 a)},
          start := {Sum.inl M1.start} ∪ {Sum.inr M2.start}, accept := Sum.inr '' M2.accept }.evalFrom
      {Sum.inl M1.start} x

case pos.inl
T : Type u
σ1 : Type u_1
σ2 : Type u_2
inst✝¹ : Fintype σ1
inst✝ : Fintype σ2
M1 : DFA T σ1
M2 : DFA T σ2
x : List T
t2 : σ1 ⊕ σ2
ht2 : ∃ x ∈ M2.accept, Sum.inr x = t2
h_start : M1.start ∈ M1.accept
h_inl : t2 ∈
  {
        step := fun s a ↦
          match s with
          | Sum.inl s1 =>
            if M1.step s1 a ∈ M1.accept then {Sum.inl (M1.step s1 a)} ∪ {Sum.inr M2.start} else {Sum.inl (M1.step s1 a)}
          | Sum.inr s2 => {Sum.inr (M2.step s2 a)},
        start := {Sum.inl M1.start} ∪ {Sum.inr M2.start}, accept := Sum.inr '' M2.accept }.evalFrom
    {Sum.inl M1.start} x
⊢ ∃ a, M1.evalFrom M1.start a ∈ M1.accept ∧ ∃ b, M2.evalFrom M2.start b ∈ M2.accept ∧ a ++ b = x
This simp argument is unused:
  NFA.eval

Hint: Omit it from the simp argument list.
  simp only [NFA.mem_accepts, concatNFA, Set.mem_image, NFA.eval, Language.mem_mul, DFA.mem_accepts, DFA.eval]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Used 25 heartbeats, which is less than the current maximum of 200000.
`concatNFA_correct` does not use the following hypotheses in its type:
  • [Fintype σ1] (#4)
  • [Fintype σ2] (#5)

Consider replacing these hypotheses with the corresponding instances of `Finite` and using `Fintype.ofFinite` in the proof, or removing them entirely.

Note: This linter can be disabled with `set_option linter.unusedFintypeInType false`
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  Sum.inr t2 ∈ (concatNFA M1 M2).evalFrom {Sum.inl ?s1} x
in the target expression
  Sum.inr t2 ∈
      {
            step := fun s a ↦
              match s with
              | Sum.inl s1 =>
                if M1.step s1 a ∈ M1.accept then {Sum.inr M2.start, Sum.inl (M1.step s1 a)}
                else {Sum.inl (M1.step s1 a)}
              | Sum.inr s2 => {Sum.inr (M2.step s2 a)},
            start := {Sum.inr M2.start, Sum.inl M1.start}, accept := Sum.inr '' M2.accept }.evalFrom
        {Sum.inl (M1.step s1 a)} x ↔
    ∃ u v, a :: x = u ++ v ∧ ¬u = [] ∧ M1.evalFrom s1 u ∈ M1.accept ∧ t2 = M2.evalFrom M2.start v

case neg
T : Type u
σ1 : Type u_1
σ2 : Type u_2
inst✝¹ : Fintype σ1
inst✝ : Fintype σ2
M1 : DFA T σ1
M2 : DFA T σ2
t2 : σ2
a : T
x : List T
ih : ∀ (s1 : σ1),
  Sum.inr t2 ∈ (concatNFA M1 M2).evalFrom {Sum.inl s1} x ↔
    ∃ u v, x = u ++ v ∧ u ≠ [] ∧ M1.evalFrom s1 u ∈ M1.accept ∧ t2 = M2.evalFrom M2.start v
s1 : σ1
h_accept : M1.start ∈ M1.accept
h✝ : M1.step s1 a ∉ M1.accept
⊢ Sum.inr t2 ∈
    {
          step := fun s a ↦
            match s with
            | Sum.inl s1 =>
              if M1.step s1 a ∈ M1.accept then {Sum.inr M2.start, Sum.inl (M1.step s1 a)} else {Sum.inl (M1.step s1 a)}
            | Sum.inr s2 => {Sum.inr (M2.step s2 a)},
          start := {Sum.inr M2.start, Sum.inl M1.start}, accept := Sum.inr '' M2.accept }.evalFrom
      {Sum.inl (M1.step s1 a)} x ↔
  ∃ u v, a :: x = u ++ v ∧ ¬u = [] ∧ M1.evalFrom s1 u ∈ M1.accept ∧ t2 = M2.evalFrom M2.start v
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  NFA.evalFrom ?M (?S ∪ ?T) ?x
in the target expression
  Sum.inr t2 ∈
      {
            step := fun s a ↦
              match s with
              | Sum.inl s1 =>
                if M1.step s1 a ∈ M1.accept then {Sum.inr M2.start, Sum.inl (M1.step s1 a)}
                else {Sum.inl (M1.step s1 a)}
              | Sum.inr s2 => {Sum.inr (M2.step s2 a)},
            start := {Sum.inr M2.start, Sum.inl M1.start}, accept := Sum.inr '' M2.accept }.evalFrom
        {Sum.inr M2.start, Sum.inl (M1.step s1 a)} x ↔
    ∃ u v, a :: x = u ++ v ∧ ¬u = [] ∧ M1.evalFrom s1 u ∈ M1.accept ∧ t2 = M2.evalFrom M2.start v

case pos
T : Type u
σ1 : Type u_1
σ2 : Type u_2
inst✝¹ : Fintype σ1
inst✝ : Fintype σ2
M1 : DFA T σ1
M2 : DFA T σ2
t2 : σ2
a : T
x : List T
ih : ∀ (s1 : σ1),
  Sum.inr t2 ∈ (concatNFA M1 M2).evalFrom {Sum.inl s1} x ↔
    ∃ u v, x = u ++ v ∧ u ≠ [] ∧ M1.evalFrom s1 u ∈ M1.accept ∧ t2 = M2.evalFrom M2.start v
s1 : σ1
h_accept : M1.start ∈ M1.accept
h✝ : M1.step s1 a ∈ M1.accept
⊢ Sum.inr t2 ∈
    {
          step := fun s a ↦
            match s with
            | Sum.inl s1 =>
              if M1.step s1 a ∈ M1.accept then {Sum.inr M2.start, Sum.inl (M1.step s1 a)} else {Sum.inl (M1.step s1 a)}
            | Sum.inr s2 => {Sum.inr (M2.step s2 a)},
          start := {Sum.inr M2.start, Sum.inl M1.start}, accept := Sum.inr '' M2.accept }.evalFrom
      {Sum.inr M2.start, Sum.inl (M1.step s1 a)} x ↔
  ∃ u v, a :: x = u ++ v ∧ ¬u = [] ∧ M1.evalFrom s1 u ∈ M1.accept ∧ t2 = M2.evalFrom M2.start v
unsolved goals
case pos
T : Type u
σ1 : Type u_1
σ2 : Type u_2
inst✝¹ : Fintype σ1
inst✝ : Fintype σ2
M1 : DFA T σ1
M2 : DFA T σ2
t2 : σ2
a : T
x : List T
ih : ∀ (s1 : σ1),
  Sum.inr t2 ∈ (concatNFA M1 M2).evalFrom {Sum.inl s1} x ↔
    ∃ u v, x = u ++ v ∧ u ≠ [] ∧ M1.evalFrom s1 u ∈ M1.accept ∧ t2 = M2.evalFrom M2.start v
s1 : σ1
h_accept : M1.start ∉ M1.accept
h✝ : M1.step s1 a ∈ M1.accept
⊢ Sum.inr t2 ∈
    {
          step := fun s a ↦
            match s with
            | Sum.inl s1 =>
              if M1.step s1 a ∈ M1.accept then {Sum.inr M2.start, Sum.inl (M1.step s1 a)} else {Sum.inl (M1.step s1 a)}
            | Sum.inr s2 => {Sum.inr (M2.step s2 a)},
          start := {Sum.inl M1.start}, accept := Sum.inr '' M2.accept }.evalFrom
      {Sum.inr M2.start, Sum.inl (M1.step s1 a)} x ↔
  ∃ u v, a :: x = u ++ v ∧ ¬u = [] ∧ M1.evalFrom s1 u ∈ M1.accept ∧ t2 = M2.evalFrom M2.start v


case neg
T : Type u
σ1 : Type u_1
σ2 : Type u_2
inst✝¹ : Fintype σ1
inst✝ : Fintype σ2
M1 : DFA T σ1
M2 : DFA T σ2
t2 : σ2
a : T
x : List T
ih : ∀ (s1 : σ1),
  Sum.inr t2 ∈ (concatNFA M1 M2).evalFrom {Sum.inl s1} x ↔
    ∃ u v, x = u ++ v ∧ u ≠ [] ∧ M1.evalFrom s1 u ∈ M1.accept ∧ t2 = M2.evalFrom M2.start v
s1 : σ1
h_accept : M1.start ∉ M1.accept
h✝ : M1.step s1 a ∉ M1.accept
⊢ Sum.inr t2 ∈
    {
          step := fun s a ↦
            match s with
            | Sum.inl s1 =>
              if M1.step s1 a ∈ M1.accept then {Sum.inr M2.start, Sum.inl (M1.step s1 a)} else {Sum.inl (M1.step s1 a)}
            | Sum.inr s2 => {Sum.inr (M2.step s2 a)},
          start := {Sum.inl M1.start}, accept := Sum.inr '' M2.accept }.evalFrom
      {Sum.inl (M1.step s1 a)} x ↔
  ∃ u v, a :: x = u ++ v ∧ ¬u = [] ∧ M1.evalFrom s1 u ∈ M1.accept ∧ t2 = M2.evalFrom M2.start v
No goals to be solved
Used 64 heartbeats, which is less than the current maximum of 200000.
`mem_evalFrom_inl` does not use the following hypotheses in its type:
  • [Fintype σ1] (#4)
  • [Fintype σ2] (#5)

Consider replacing these hypotheses with the corresponding instances of `Finite` and using `Fintype.ofFinite` in the proof, or removing them entirely.

Note: This linter can be disabled with `set_option linter.unusedFintypeInType false`
unsolved goals
case cons
T : Type u
σ1 : Type u_1
σ2 : Type u_2
M1 : DFA T σ1
M2 : DFA T σ2
a : T
x : List T
ih : ∀ (s2 : σ2), (concatNFA M1 M2).evalFrom {Sum.inr s2} x = {Sum.inr (M2.evalFrom s2 x)}
s2 : σ2
⊢ {
        step := fun s a ↦
          match s with
          | Sum.inl s1 =>
            if M1.step s1 a ∈ M1.accept then {Sum.inr M2.start, Sum.inl (M1.step s1 a)} else {Sum.inl (M1.step s1 a)}
          | Sum.inr s2 => {Sum.inr (M2.step s2 a)},
        start := if M1.start ∈ M1.accept then {Sum.inr M2.start, Sum.inl M1.start} else {Sum.inl M1.start},
        accept := Sum.inr '' M2.accept }.evalFrom
    {Sum.inr (M2.step s2 a)} x =
  {Sum.inr (M2.evalFrom (M2.step s2 a) x)}-/
