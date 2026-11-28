import OMAStatements.S_oeis_a125370

-- Credit: @Aryan-Poonacha
-- The finite path-to-trace argument adapts the base-six formalization for OEIS
-- A125316 in https://github.com/lefttosolve2/open-math-agents/pull/25779.
-- The transfer-matrix method is given by Rafał Wiktorowicz, Proposition 2,
-- https://oeis.org/A126371/a126371_1.pdf (2026). Formulas: Colin Barker (2017).
namespace CircularDigitWords

open OMA.S_oeis_a125370 Finset PowerSeries

section Walks

variable {Digit : Type*} (Edge : Digit → Digit → Prop)

private abbrev cons {n : ℕ} (u : Digit) (w : Fin n → Digit) : Fin (n + 1) → Digit :=
  @Fin.cons n (fun _ ↦ Digit) u w

private abbrev snoc {n : ℕ} (w : Fin n → Digit) (v : Digit) : Fin (n + 1) → Digit :=
  @Fin.snoc n (fun _ ↦ Digit) w v

def walkMatrix [DecidableRel Edge] : Matrix Digit Digit ℚ := fun u v ↦ if Edge u v then 1 else 0

private def Path {n : ℕ} (u v : Digit) (w : Fin n → Digit) : Prop :=
  ∀ i : Fin (n + 1),
    Edge (snoc (cons u w) v i.castSucc) (snoc (cons u w) v i.succ)

private instance [DecidableRel Edge] {n : ℕ} (u v : Digit) (w : Fin n → Digit) : Decidable (Path Edge u v w) := by
  unfold Path
  infer_instance

private lemma path_empty (u v : Digit) (w : Fin 0 → Digit) : Path Edge u v w ↔ Edge u v := by
  have h0 : Edge (snoc (cons u w) v (0 : Fin 1).castSucc)
      (snoc (cons u w) v (Fin.last 1)) ↔ Edge u v := by
    rw [show snoc (cons u w) v (Fin.last 1) = v from Fin.snoc_last ..,
      show snoc (cons u w) v (0 : Fin 1).castSucc = u from
        (Fin.snoc_castSucc ..).trans (Fin.cons_zero ..)]
  constructor
  · intro h
    exact h0.1 (h 0)
  · intro h i
    have hi : i = 0 := Fin.ext (by have hi := i.isLt; simp at hi; omega)
    subst i
    exact h0.2 h

private lemma path_cons {n : ℕ} (u v x : Digit) (w : Fin n → Digit) :
    Path Edge u v (cons x w) ↔ Edge u x ∧ Path Edge x v w := by
  unfold Path
  have hs : snoc (cons u (cons x w)) v = cons u (snoc (cons x w) v) :=
    (Fin.cons_snoc_eq_snoc_cons u (cons x w) v).symm
  rw [hs, Fin.forall_fin_succ]
  have hcast (i : Fin (n + 1)) : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
  have hzero : snoc (cons x w) v 0 = x := by
    change snoc (cons x w) v (0 : Fin (n + 1)).castSucc = x
    simp [snoc, cons]
  simp only [Fin.castSucc_zero, cons, Fin.cons_zero, Fin.cons_succ, hcast]
  change (Edge u (snoc (cons x w) v 0) ∧ _) ↔ _
  rw [hzero]

private lemma path_sum [Fintype Digit] [DecidableEq Digit] [DecidableRel Edge] (n : ℕ) (u v : Digit) :
    (∑ w : Fin n → Digit, (if Path Edge u v w then 1 else 0 : ℚ)) = ((walkMatrix Edge) ^ (n + 1)) u v := by
  induction n generalizing u v with
  | zero =>
    simp only [path_empty, Fintype.sum_unique, Nat.zero_add, pow_one, walkMatrix]
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n + 1) ↦ Digit)
    have hs :
        (∑ w : Fin (n + 1) → Digit, (if Path Edge u v w then 1 else 0 : ℚ)) =
          ∑ p : Digit × (Fin n → Digit), (if Path Edge u v (cons p.1 p.2) then 1 else 0 : ℚ) := by
      exact (Fintype.sum_equiv e _ _ fun p ↦ rfl).symm
    rw [hs, Fintype.sum_prod_type, pow_succ', Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro x _
    simp only [path_cons]
    by_cases hx : Edge u x
    · simp only [hx, true_and, walkMatrix, if_true, one_mul]
      exact ih x v
    · simp only [hx, false_and, if_false, sum_const_zero, walkMatrix, zero_mul]

private lemma snoc_next {n : ℕ} (w : Fin (n + 1) → Digit) (i : Fin (n + 1)) :
    snoc w (w 0) i.succ = w ⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩ := by
  by_cases h : i.val + 1 < n + 1
  · have heq : i.succ = (⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩ : Fin (n + 1)).castSucc :=
      Fin.ext (by simp [Nat.mod_eq_of_lt h])
    rw [heq]
    exact Fin.snoc_castSucc ..
  · have hv : i.val + 1 = n + 1 := by omega
    have heq : i.succ = Fin.last (n + 1) := Fin.ext hv
    rw [heq, show snoc w (w 0) (Fin.last (n + 1)) = w 0 from Fin.snoc_last ..]
    congr 1
    exact Fin.ext (by simp [hv])

private lemma path_cycle {n : ℕ} (u : Digit) (w : Fin n → Digit) :
    Path Edge u u w ↔ ∀ i : Fin (n + 1),
      Edge ((cons u w) i)
        ((cons u w) ⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩) := by
  unfold Path
  apply forall_congr'
  intro i
  have h0 : snoc (cons u w) u i.castSucc = (cons u w) i := Fin.snoc_castSucc ..
  have hn : snoc (cons u w) u i.succ =
      (cons u w) ⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩ := by
    simpa only [cons, Fin.cons_zero] using snoc_next (cons u w) i
  rw [h0, hn]

theorem walks_as_trace [Fintype Digit] [DecidableEq Digit] [DecidableRel Edge] (n : ℕ) :
    ((Finset.univ.filter (fun w : Fin (n+1) → Digit => ∀ i,
      Edge (w i) (w ⟨(i.val+1) % (n+1), Nat.mod_lt _ (by omega)⟩))).card : ℚ) = Matrix.trace ((walkMatrix Edge) ^ (n + 1)) := by
  classical
  let e := Fin.consEquiv (fun _ : Fin (n + 1) ↦ Digit)
  have hs :
      (∑ w : Fin (n + 1) → Digit, (if ∀ i : Fin (n + 1),
        Edge (w i) (w ⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩) then 1 else 0 : ℚ)) =
      ∑ p : Digit × (Fin n → Digit), (if Path Edge p.1 p.1 p.2 then 1 else 0 : ℚ) := by
    symm
    apply Fintype.sum_equiv e
    intro p
    simp only [path_cycle]
    rfl
  rw [Fintype.sum_prod_type] at hs
  simp_rw [path_sum] at hs
  rw [Matrix.trace]
  change _ = ∑ x, ((walkMatrix Edge) ^ (n + 1)) x x
  rw [← hs]
  exact (Finset.sum_boole _ _).symm

end Walks


/-- Quotient adjacency matrix for two forbidden extreme digits and m interior digits. -/
def quotient (m : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, m, 0; 1, m, 1; 0, m, 1]

lemma class_relation (m : ℚ) :
    (quotient m)^3 = (m+2) • (quotient m)^2 - quotient m - m • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quotient, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private lemma swap_power {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I (Fin 3) ℚ) (V : Matrix (Fin 3) I ℚ) (n : ℕ) :
    (U*V)^(n+1) = U * (V*U)^n * V := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (U*V) (n+1), ih, pow_succ]
    simp only [Matrix.mul_assoc]

/-- Lift the three-class polynomial identity through any adjacency factorization. -/
lemma lifted_relation {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I (Fin 3) ℚ) (V : Matrix (Fin 3) I ℚ) (m : ℚ)
    (H : V*U = quotient m) :
    (U*V)^4 = (m+2) • (U*V)^3 - (U*V)^2 - m • (U*V) := by
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℚ => U * A * V) (class_relation m)
  rw [← H] at h
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at h
  simpa only [swap_power U V 3, swap_power U V 2, swap_power U V 1, pow_one] using h

/-- Class 0 is the low endpoint, class 2 the high endpoint; the remaining m digits form class 1. -/
def digitClass (m : ℕ) (x : Fin (m+2)) : Fin 3 :=
  if x = 0 then 0 else if x = Fin.last (m+1) then 2 else 1

def indicator (m : ℕ) : Matrix (Fin (m+2)) (Fin 3) ℚ :=
  fun x i => if digitClass m x = i then 1 else 0

def allowed (m : ℕ) : Matrix (Fin 3) (Fin (m+2)) ℚ :=
  fun i y => if (i = 0 ∧ digitClass m y = 2) ∨ (i = 2 ∧ digitClass m y = 0) then 0 else 1

/-- All steps are allowed except a step from either endpoint to the opposite endpoint. -/
def circularMatrix (m : ℕ) : Matrix (Fin (m+2)) (Fin (m+2)) ℚ :=
  fun x y => allowed m (digitClass m x) y

private lemma factorMatrix (m : ℕ) : indicator m * allowed m = circularMatrix m := by
  ext x y
  simp [Matrix.mul_apply, indicator, circularMatrix]

private lemma classCounts (m : ℕ) : allowed m * indicator m = quotient m := by
  have hlast : Fin.last (m+1) ≠ 0 := by intro h; have := congrArg Fin.val h; simp at this
  have hzero : digitClass m 0 = 0 := by simp [digitClass]
  have hlast' : digitClass m (Fin.last (m+1)) = 2 := by simp [digitClass, hlast]
  have hmid' (x : Fin m) : digitClass m x.castSucc.succ = 1 := by
    change digitClass m x.succ.castSucc = 1
    simp [digitClass, Fin.castSucc_ne_last]
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  fin_cases i <;> fin_cases j <;>
    simp [allowed, indicator, hzero, hlast', hmid', quotient]

theorem circularMatrix_relation (m : ℕ) :
    circularMatrix m ^ 4 = ((m:ℚ)+2) • circularMatrix m ^ 3 -
      circularMatrix m ^ 2 - (m:ℚ) • circularMatrix m := by
  simpa only [factorMatrix] using lifted_relation (indicator m) (allowed m) m (classCounts m)

def boundedEdge (m : ℕ) (x y : Fin (m+2)) : Prop :=
  ((x.val : ℤ) - y.val).natAbs ≤ m

instance (m : ℕ) : DecidableRel (boundedEdge m) := fun _ _ => inferInstanceAs (Decidable (_ ≤ _))

private lemma distanceMatrix (m : ℕ) : walkMatrix (boundedEdge m) = circularMatrix m := by
  ext x y
  have hx := x.isLt
  have hy := y.isLt
  have habs : ((x.val : ℤ) - y.val).natAbs ≤ m ↔
      ¬ (x.val = 0 ∧ y.val = m+1 ∨ x.val = m+1 ∧ y.val = 0) := by
    by_cases h : x.val ≤ y.val
    · rw [Int.natAbs_natCast_sub_natCast_of_le h]
      omega
    · rw [← Int.natAbs_neg, neg_sub, Int.natAbs_natCast_sub_natCast_of_le (by omega : y.val ≤ x.val)]
      omega
  simp only [walkMatrix, boundedEdge, circularMatrix, allowed, digitClass, habs]
  simp only [Fin.ext_iff, Fin.val_zero, Fin.val_last]
  split_ifs <;> first | rfl | omega

def circularCount (m n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin n → Fin (m+2) => ∀ i,
    boundedEdge m (w i) (w ⟨(i.val+1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩))).card

private lemma count_trace (m n : ℕ) :
    (circularCount m (n+1) : ℚ) = Matrix.trace (circularMatrix m ^ (n+1)) := by
  rw [← distanceMatrix]
  exact walks_as_trace (boundedEdge m) n

/-- For every alphabet of size m+2, count circular words whose adjacent digits differ by at most m. -/
theorem circular_recurrence (m k : ℕ) :
    (circularCount m (k+4) : ℚ) = ((m:ℚ)+2)*circularCount m (k+3) -
      circularCount m (k+2) - (m:ℚ)*circularCount m (k+1) := by
  have h := congrArg (fun A : Matrix (Fin (m+2)) (Fin (m+2)) ℚ =>
    Matrix.trace (circularMatrix m ^ k * A)) (circularMatrix_relation m)
  simp only [mul_sub, mul_smul_comm, ← pow_add, ← pow_succ,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at h
  simpa only [count_trace m (k+3), count_trace m (k+2), count_trace m (k+1),
    count_trace m k] using h

private lemma count_quotient (m n : ℕ) :
    (circularCount m (n+1) : ℚ) = Matrix.trace ((quotient m)^(n+1)) := by
  rw [count_trace, ← factorMatrix, swap_power, Matrix.trace_mul_cycle,
    classCounts, ← pow_succ']

private lemma init0 (m : ℕ) : (circularCount m 0 : ℚ) = 1 := by
  simp [circularCount]

private lemma init1 (m : ℕ) : (circularCount m 1 : ℚ) = m+2 := by
  rw [count_quotient m 0]
  simp [quotient, Matrix.trace, Fin.sum_univ_succ]
  ring

private lemma init2 (m : ℕ) : (circularCount m 2 : ℚ) = (m+2)^2-2 := by
  rw [count_quotient m 1]
  simp [quotient, Matrix.trace, pow_succ, Fin.sum_univ_succ]
  ring

private lemma init3 (m : ℕ) : (circularCount m 3 : ℚ) = (m+2)^3-6*(m+2)+6 := by
  rw [count_quotient m 2]
  simp [quotient, Matrix.trace, pow_succ, Fin.sum_univ_succ]
  ring

theorem circular_gf (m : ℕ) :
    PowerSeries.mk (fun n => (circularCount m n : ℚ)) *
      ((1-X)*(1-C ((m:ℚ)+1)*X-C (m:ℚ)*X^2)) = 1-X^2-C (2*(m:ℚ))*X^3 := by
  let F : PowerSeries ℚ := PowerSeries.mk (fun n => (circularCount m n : ℚ))
  let w : ℚ := (m:ℚ)+2
  change F * _ = _
  have he : F * ((1-X)*(1-C ((m:ℚ)+1)*X-C (m:ℚ)*X^2)) =
      F - C w * (X^1 * F) + X^2 * F + C (m:ℚ) * (X^3 * F) := by
    simp only [w, map_add, map_one, map_ofNat]
    ring
  rw [he]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, coeff_one, F, coeff_mk]
  dsimp only [w]
  by_cases hn : 4 ≤ n
  · obtain ⟨k, rfl⟩ : ∃ k, n = k+4 := ⟨n-4, by omega⟩
    simp only [if_pos (show 1 ≤ k+4 by omega), if_pos (show 2 ≤ k+4 by omega),
      if_pos (show 3 ≤ k+4 by omega), if_neg (show k+4 ≠ 0 by omega),
      if_neg (show k+4 ≠ 2 by omega), if_neg (show k+4 ≠ 3 by omega), mul_zero, sub_zero]
    rw [show k+4-1 = k+3 by omega, show k+4-2 = k+2 by omega,
      show k+4-3 = k+1 by omega, circular_recurrence]
    ring
  · interval_cases n <;> norm_num [init0, init1, init2, init3] <;> ring

private lemma root_step (t x : ℝ) (hx : x^2 = (t+1)*x+t) (k : ℕ) :
    x^(k+3) = (t+2)*x^(k+2) - x^(k+1) - t*x^k := by
  have h3 : x^3 = (t+2)*x^2-x-t := by linear_combination (x-1)*hx
  simp only [pow_add]
  rw [h3]
  ring

theorem circular_closed (m : ℕ) (x y : ℝ)
    (hsum : x+y = (m:ℝ)+1) (hprod : x*y = -(m:ℝ)) (n : ℕ) (hn : 1 ≤ n) :
    (circularCount m n : ℝ) = 1+x^n+y^n := by
  have hx : x^2 = ((m:ℝ)+1)*x+m := by linear_combination x*hsum - hprod
  have hy : y^2 = ((m:ℝ)+1)*y+m := by linear_combination y*hsum - hprod
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n ≤ 3
    · interval_cases n
      · have h : (circularCount m 1 : ℝ) = (m:ℝ)+2 := by exact_mod_cast init1 m
        simp only [pow_one]
        linarith
      · have h : (circularCount m 2 : ℝ) = ((m:ℝ)+2)^2-2 := by exact_mod_cast init2 m
        have H : x^2+y^2 = (x+y)^2-2*(x*y) := by ring
        rw [hsum,hprod] at H
        linarith
      · have h : (circularCount m 3 : ℝ) = ((m:ℝ)+2)^3-6*((m:ℝ)+2)+6 := by exact_mod_cast init3 m
        have H : x^3+y^3 = (x+y)^3-3*(x*y)*(x+y) := by ring
        rw [hsum,hprod] at H
        linarith
    · obtain ⟨k, rfl⟩ : ∃ k, n = k+4 := ⟨n-4, by omega⟩
      have h : (circularCount m (k+4) : ℝ) =
          ((m:ℝ)+2)*circularCount m (k+3)-circularCount m (k+2)-(m:ℝ)*circularCount m (k+1) := by
        exact_mod_cast circular_recurrence m k
      rw [h, ih (k+3) (by omega) (by omega), ih (k+2) (by omega) (by omega),
        ih (k+1) (by omega) (by omega), root_step _ x hx (k+1), root_step _ y hy (k+1)]
      ring

end CircularDigitWords

theorem OMA.solution : type_of% @OMA.S_oeis_a125370.main := by
  have hg := CircularDigitWords.circular_gf 5
  norm_num only [Nat.cast_ofNat, map_ofNat, show (5:ℚ)+1=6 by norm_num,
    show (2:ℚ)*5=10 by norm_num] at hg
  refine ⟨hg, ?_, ?_⟩
  · intro n hn
    apply CircularDigitWords.circular_closed 5 _ _ _ _ n hn
    · norm_num
    · have h := Real.sq_sqrt (show (0:ℝ) ≤ 14 by norm_num)
      norm_num
      nlinarith
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k+4 := ⟨n-4, by omega⟩
    have h := CircularDigitWords.circular_recurrence 5 k
    norm_num only [Nat.cast_ofNat, show (5:ℚ)+2=7 by norm_num] at h
    exact_mod_cast h
