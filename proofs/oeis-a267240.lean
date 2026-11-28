import OMAStatements.S_oeis_a267240

namespace A267240Proof
open OMA.S_oeis_a267240

abbrev Row := Fin 3 → Fin 2
def rows : List Row :=
  [![0,0,0], ![0,0,1], ![0,1,0], ![0,1,1],
   ![1,0,0], ![1,0,1], ![1,1,0], ![1,1,1]]

def wt (r : Row) : ℕ := (r 0).val + (r 1).val + (r 2).val
def col (l : List Row) (i : Fin 3) := l.map (fun r => r i)
def sorted (m : ℕ) (l : List Row) := (m :: l.map wt).IsChain (· ≤ ·)
def P (m : ℕ) (b c : Bool) (l : List Row) :=
  sorted m l ∧ (b = true → col l 0 ≤ col l 1) ∧ (c = true → col l 1 ≤ col l 2)

lemma initial (l : List Row) : IsSolution l ↔ P 0 true true l := by
  simp only [IsSolution, P, sorted, true_implies, Fin.forall_fin_succ, Fin.forall_fin_zero,
    and_true, Fin.sum_univ_three]
  change (l.IsChain (fun r s => wt r ≤ wt s) ∧ _) ↔
    ((0 :: l.map wt).IsChain (· ≤ ·) ∧ _)
  cases l <;> simp [List.isChain_cons_cons, col]
  intro _ _
  exact (List.isChain_map wt).symm

def opts (m : ℕ) (b c : Bool) := rows.filter fun r =>
  decide (m ≤ wt r ∧ (b = true → r 0 ≤ r 1) ∧ (c = true → r 1 ≤ r 2))
def flag (b : Bool) (x y : Fin 2) := b && decide (x = y)

lemma lexStep (b : Bool) (x y : Fin 2) (u v : List (Fin 2)) :
    (b = true → x :: u ≤ y :: v) ↔
    (b = true → x ≤ y) ∧ (flag b x y = true → u ≤ v) := by
  cases b
  · simp [flag]
  · rcases lt_trichotomy x y with h | rfl | h
    · have hh : x :: u < y :: v := List.Lex.rel h
      simp [flag, h.ne, h.le, hh.le]
    · have hh : x :: u ≤ x :: v ↔ u ≤ v := by
        rw [← not_lt, ← not_lt]
        exact not_congr List.lex_cons_iff
      simp [flag, hh]
    · have hh : y :: v < x :: u := List.Lex.rel h
      simp [flag, h.ne', h.not_ge, hh.not_ge]

lemma step (m : ℕ) (b c : Bool) (r : Row) (l : List Row) :
    P m b c (r :: l) ↔ r ∈ opts m b c ∧
      P (wt r) (flag b (r 0) (r 1)) (flag c (r 1) (r 2)) l := by
  have allRows : ∀ s : Row, s ∈ rows := by decide
  simp only [P, sorted, col, List.map_cons, List.isChain_cons_cons, lexStep,
    opts, List.mem_filter, allRows, true_and, decide_eq_true_eq]
  tauto

def words : ℕ → ℕ → Bool → Bool → List (List Row)
  | 0, _, _, _ => [[]]
  | n+1, m, b, c => (opts m b c).flatMap fun r =>
      (words n (wt r) (flag b (r 0) (r 1)) (flag c (r 1) (r 2))).map (r :: ·)

lemma mem_words (n m b c l) : l ∈ words n m b c ↔ l.length = n ∧ P m b c l := by
  induction n generalizing m b c l with
  | zero => cases l <;> simp [words, P, sorted, col]
  | succ n ih => cases l <;> simp [words, ih, step, and_assoc, and_left_comm, and_comm]

lemma unique_words (n m b c) : (words n m b c).Nodup := by
  induction n generalizing m b c with
  | zero => simp [words]
  | succ n ih =>
    have h : rows.Nodup := by decide
    apply List.nodup_flatMap.mpr
    refine ⟨fun r _ => (ih ..).map List.cons_injective, (h.filter _).imp ?_⟩
    intro r s hrs l hl hl'
    rcases List.mem_map.mp hl with ⟨u, _, rfl⟩
    rcases List.mem_map.mp hl' with ⟨v, _, he⟩
    exact hrs (List.cons.inj he).1.symm

abbrev count (n m b c) := (words n m b c).length

lemma count_eq (n) : a n = count n 0 true true := by
  let s := (words n 0 true true).toFinset
  have h := Nat.card_congr (Equiv.subtypeEquivProp (p := fun l : List Row =>
    l.length = n ∧ IsSolution l) (q := fun l => l ∈ s) (by
      funext l
      apply propext
      simp [s, mem_words, initial]))
  exact h.trans ((Nat.card_eq_fintype_card.trans (Fintype.card_coe s)).trans
    (List.toFinset_card_of_nodup (unique_words ..)))

private lemma count_succ (n m b c) : count (n+1) m b c =
    ((opts m b c).map fun r => count n (wt r)
      (flag b (r 0) (r 1)) (flag c (r 1) (r 2))).sum := by
  simp only [count, words, List.length_flatMap, List.length_map]

private lemma rec0 (n) : count (n+1) 0 true true = count n 0 true true + (count n 1 true false + (count n 2 false true + (count n 3 true true + 0))) := by
  rw [count_succ]
  rfl

private lemma rec1 (n) : count (n+1) 1 false false = count n 1 false false + (count n 1 false false + (count n 2 false false + (count n 1 false false + (count n 2 false false + (count n 2 false false + (count n 3 false false + 0)))))) := by
  rw [count_succ]
  rfl

private lemma rec2 (n) : count (n+1) 1 true false = count n 1 true false + (count n 1 false false + (count n 2 false false + (count n 2 true false + (count n 3 true false + 0)))) := by
  rw [count_succ]
  rfl

private lemma rec3 (n) : count (n+1) 2 false false = count n 2 false false + (count n 2 false false + (count n 2 false false + (count n 3 false false + 0))) := by
  rw [count_succ]
  rfl

private lemma rec4 (n) : count (n+1) 2 false true = count n 2 false true + (count n 2 false false + (count n 3 false true + 0)) := by
  rw [count_succ]
  rfl

private lemma rec5 (n) : count (n+1) 2 true false = count n 2 false false + (count n 2 true false + (count n 3 true false + 0)) := by
  rw [count_succ]
  rfl

private lemma rec6 (n) : count (n+1) 3 false false = count n 3 false false + 0 := by
  rw [count_succ]
  rfl

private lemma rec7 (n) : count (n+1) 3 false true = count n 3 false true + 0 := by
  rw [count_succ]
  rfl

private lemma rec8 (n) : count (n+1) 3 true false = count n 3 true false + 0 := by
  rw [count_succ]
  rfl

private lemma rec9 (n) : count (n+1) 3 true true = count n 3 true true + 0 := by
  rw [count_succ]
  rfl

lemma formulas (n : ℕ) :
    ((count n 0 true true : ℚ) = 3*3^n*(n:ℚ)/8 + (n:ℚ)^3/12 + (n:ℚ)^2/2 + 31*(n:ℚ)/24 + 1) ∧
    ((count n 1 false false : ℚ) = 3*3^n*(n:ℚ)/2 + 3*3^n/4 + 1/4) ∧
    ((count n 1 true false : ℚ) = 3*3^n*(n:ℚ)/4 + 3*3^n/8 + (n:ℚ)^2/4 + 3*(n:ℚ)/4 + 5/8) ∧
    ((count n 2 false false : ℚ) = 3*3^n/2 - 1/2) ∧
    ((count n 2 false true : ℚ) = 3*3^n/4 + (n:ℚ)/2 + 1/4) ∧
    ((count n 2 true false : ℚ) = 3*3^n/4 + (n:ℚ)/2 + 1/4) ∧
    ((count n 3 false false : ℚ) = 1) ∧
    ((count n 3 false true : ℚ) = 1) ∧
    ((count n 3 true false : ℚ) = 1) ∧
    ((count n 3 true true : ℚ) = 1) := by
  induction n with
  | zero => norm_num [count, words]
  | succ n ih =>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ih
    simp only [rec0, rec1, rec2, rec3, rec4, rec5, rec6, rec7, rec8, rec9, Nat.cast_add, Nat.cast_zero, Nat.cast_succ, pow_succ, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
    repeat' apply And.intro
    all_goals first | trivial | ring

lemma closedForm (n : ℕ) : (a n : ℚ) =
    (24 + (31 + 3 ^ (2+n)) * n + 12*n^2 + 2*n^3)/24 := by
  rw [count_eq, (formulas n).1, pow_add]
  ring

lemma recurrence (k : ℕ) : (a (k+7) : ℚ) = 10*a (k+6) - 39*a (k+5) +
    76*a (k+4) - 79*a (k+3) + 42*a (k+2) - 9*a (k+1) := by
  simp only [closedForm, pow_add, Nat.cast_add, Nat.cast_ofNat]
  ring

open PowerSeries

lemma series : PowerSeries.mk (fun n => (a (n+1) : ℚ)) * ((1-X)^4*(1-3*X)^2) =
    4 - 27*X + 68*X^2 - 76*X^3 + 42*X^4 - 9*X^5 := by
  let f := PowerSeries.mk (fun n => (a (n+1) : ℚ))
  change f * _ = _
  have expand : f * ((1-X)^4*(1-3*X)^2) =
      f - 10 • (f*X^1) + 39 • (f*X^2) - 76 • (f*X^3) +
      79 • (f*X^4) - 42 • (f*X^5) + 9 • (f*X^6) := by simp only [nsmul_eq_mul]; ring
  rw [expand]
  have num : (4 - 27*X + 68*X^2 - 76*X^3 + 42*X^4 - 9*X^5 : ℚ⟦X⟧) =
      4 • (X^0) - 27 • (X^1) + 68 • (X^2) - 76 • (X^3) + 42 • (X^4) - 9 • (X^5) := by
    simp only [nsmul_eq_mul]; ring
  rw [num]
  ext n
  simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_X_pow, f, coeff_mk]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  by_cases hn : n < 6
  · interval_cases n <;> norm_num [closedForm]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n-6, by omega⟩
    simp (disch := omega) only [if_pos, if_neg, Nat.add_sub_cancel, Nat.add_sub_assoc]
    linarith [recurrence k]

end A267240Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a267240.main := by
  refine ⟨?_, A267240Proof.series, fun n _ => A267240Proof.closedForm n⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k+7 := ⟨n-7, by omega⟩
  exact_mod_cast A267240Proof.recurrence k
