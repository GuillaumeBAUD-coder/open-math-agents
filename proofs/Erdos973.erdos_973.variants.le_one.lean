import FormalConjectures.ErdosProblems.«973»

/- Formalization of the known unit-disc construction for Erdős problem 973.
For large n, a corrected Taylor polynomial forces the middle power sums to vanish.
The remaining two sums are controlled by a scalar exponential estimate.
The finite range uses a separate unit-disc construction and continuity.
-/

open Polynomial Finset

namespace OMA973

lemma reflected_factors_tuple (s : Multiset ℂ) :
    ∃ z : Fin s.card → ℂ, (∏ i, (1 - C (z i) * X)) =
      (((s.map fun a => (X : ℂ[X]) - C a).prod).reflect s.card) := by
  classical
  induction s using Multiset.induction_on with
  | empty => exact ⟨fun i => Fin.elim0 i, by simp⟩
  | cons a s ih =>
    obtain ⟨z, hz⟩ := ih
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons]
    refine ⟨Fin.cons a z, ?_⟩
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hz]
    have h₁ : ((X : ℂ[X]) - C a).natDegree ≤ 1 := natDegree_X_sub_C_le a
    have h₂ : ((s.map fun b => (X : ℂ[X]) - C b).prod).natDegree ≤ s.card :=
      (natDegree_multiset_prod_X_sub_C_eq_card s).le
    simpa [Nat.add_comm] using
      (reflect_mul ((X : ℂ[X]) - C a) ((s.map fun b => X - C b).prod) h₁ h₂).symm

lemma exists_factor_tuple (n : ℕ) (P : ℂ[X]) (h₀ : P.coeff 0 = 1)
    (hd : P.natDegree ≤ n) (h₁ : P.eval 1 = 0) :
    ∃ z : Fin n → ℂ, (∃ i, z i = 1) ∧ (∏ i, (1 - C (z i) * X)) = P := by
  classical
  let q := P.reflect n
  have hcoeff : q.coeff n = 1 := by simp [q, h₀]
  have hdeg : q.natDegree = n := le_antisymm
    ((Polynomial.natDegree_reflect_le (p := P) (N := n)).trans (max_eq_left hd).le)
    (Polynomial.le_natDegree_of_ne_zero (hcoeff.trans_ne one_ne_zero))
  have hmonic : q.Monic := by
    change q.coeff q.natDegree = 1
    rwa [hdeg]
  have hcard : q.roots.card = q.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hcount : q.roots.card = n := hcard.trans hdeg
  obtain ⟨z, hz⟩ := reflected_factors_tuple q.roots
  have hp : (∏ i, (1 - C (z i) * X)) = P := calc
    _ = _ := hz
    _ = q.reflect q.roots.card := by
      rw [Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard]
    _ = P := by rw [hcount]; exact Polynomial.reflect_reflect
  have heval : (∏ i, (1 - z i)) = 0 := by
    simpa [Polynomial.eval_prod, h₁] using congrArg (Polynomial.eval 1) hp
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp heval
  rw [← hcount]
  exact ⟨z, ⟨i, (sub_eq_zero.mp hi).symm⟩, hp⟩

end OMA973

open Polynomial Finset

namespace OMA.E973

lemma factorTelescoping (r : ℂ) (q : ℂ[X]) (k : ℕ) :
    (∑ j ∈ range (k + 1), (q * (1 - C r * X)).coeff j * r ^ (k + 1 - j)) =
      q.coeff k * r := by
  let p := q * (1 - C r * X)
  change (∑ j ∈ range (k + 1), p.coeff j * r ^ (k + 1 - j)) = q.coeff k * r
  have h0 : p.coeff 0 = q.coeff 0 := by
    simp [p, mul_sub, ← mul_assoc, coeff_mul_X_zero]
  have hs (m : ℕ) : p.coeff (m + 1) = q.coeff (m + 1) - q.coeff m * r := by
    simp [p, mul_sub, ← mul_assoc]
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    have liftSum :
        (∑ j ∈ range (k + 1), p.coeff j * r ^ (k + 1 + 1 - j)) =
          (∑ j ∈ range (k + 1), p.coeff j * r ^ (k + 1 - j)) * r := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [show k + 1 + 1 - j = (k + 1 - j) + 1 by omega, pow_succ, mul_assoc]
    change (∑ j ∈ range (k + 1 + 1), p.coeff j * r ^ (k + 1 + 1 - j)) = _
    rw [Finset.sum_range_succ, liftSum, ih, hs,
      show k + 1 + 1 - (k + 1) = 1 by omega, pow_one]
    ring

lemma factorPowerSumNewton {n : ℕ} (z : Fin n → ℂ) (k : ℕ) (hk : 1 ≤ k) :
    let q : ℂ[X] := ∏ i, (1 - C (z i) * X)
    (k : ℂ) * q.coeff k +
      ∑ j ∈ range k, q.coeff j * ∑ i, z i ^ (k - j) = 0 := by
  classical
  cases k with
  | zero => omega
  | succ m =>
    let f : Fin n → ℂ[X] := fun i => 1 - C (z i) * X
    let q := ∏ i, f i
    let rem (i : Fin n) := ∏ b ∈ (univ : Finset (Fin n)).erase i, f b
    change ((m + 1 : ℕ) : ℂ) * q.coeff (m + 1) +
      ∑ j ∈ range (m + 1), q.coeff j * ∑ i, z i ^ (m + 1 - j) = 0
    have hsplit (i : Fin n) : rem i * f i = q :=
      Finset.prod_erase_mul univ f (Finset.mem_univ i)
    have hsum : (∑ j ∈ range (m + 1), q.coeff j * ∑ i, z i ^ (m + 1 - j)) =
        ∑ i, (rem i).coeff m * z i := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [← hsplit i]
      exact factorTelescoping (z i) (rem i) m
    have hderiv : derivative q = ∑ i, rem i * (-C (z i)) := by
      dsimp [q, rem]
      rw [derivative_prod_finset]
      simp [f, derivative_C_mul_X]
    have hc := congrArg (fun t : ℂ[X] => t.coeff m) hderiv
    simp only [coeff_derivative, finsetSum_coeff, mul_neg, coeff_neg, coeff_mul_C,
      Finset.sum_neg_distrib] at hc
    rw [hsum, Nat.cast_add, Nat.cast_one, mul_comm]
    exact eq_neg_iff_add_eq_zero.mp hc

end OMA.E973

open Finset Polynomial

namespace OMA973

noncomputable def expCoeff (a : ℂ) (k : ℕ) : ℂ := (-a) ^ k / (k.factorial : ℂ)

noncomputable def expPartial (a : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ range (n+1), expCoeff a j

noncomputable def correctedExp (a : ℂ) (n : ℕ) : ℂ[X] :=
  (∑ j ∈ range (n+1), monomial j (expCoeff a j)) - monomial n (expPartial a n)

lemma expCoeff_zero (a : ℂ) : expCoeff a 0 = 1 := by
  simp [expCoeff]

lemma expCoeff_one (a : ℂ) : expCoeff a 1 = -a := by
  simp [expCoeff]

lemma expCoeff_step (a : ℂ) (j : ℕ) :
    ((j+1 : ℕ) : ℂ) * expCoeff a (j+1) = -a * expCoeff a j := by
  simp only [expCoeff, Nat.factorial_succ, pow_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hj : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  field_simp
  <;> ring

lemma correctedExp_coeff (a : ℂ) (n j : ℕ) :
    (correctedExp a n).coeff j =
      (if j ≤ n then expCoeff a j else 0) - (if j = n then expPartial a n else 0) := by
  classical
  simp [correctedExp, Polynomial.finsetSum_coeff, coeff_monomial, eq_comm, Nat.lt_succ_iff]

lemma correctedExp_eval_one (a : ℂ) (n : ℕ) : (correctedExp a n).eval 1 = 0 := by
  classical
  simp [correctedExp, expPartial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

lemma correctedExp_natDegree (a : ℂ) (n : ℕ) : (correctedExp a n).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  simp [correctedExp_coeff, Nat.not_le.mpr hi, Nat.ne_of_gt hi]

lemma newton_middle_sum (c s : ℕ → ℂ) {k : ℕ} (hk : 2 ≤ k)
    (hs : ∀ i, 2 ≤ i → i < k → s i = 0) :
    ∑ j ∈ range k, c j * s (k-j) = c 0 * s k + c (k-1) * s 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k-2, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have hz : ∑ j ∈ range m, c (j+1) * s (m+2-(j+1)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [hs _ (by omega) (by omega), mul_zero]
  simp [hz, show m + 2 - (m + 1) = 1 by omega]

lemma newton_last_sum (c s : ℕ → ℂ) {n : ℕ} (hn : 2 ≤ n)
    (hs : ∀ i, 2 ≤ i → i < n → s i = 0) :
    ∑ j ∈ range (n+1), c j * s (n+1-j) =
      c 0 * s (n+1) + c 1 * s n + c n * s 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m+2 := ⟨n-2, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∑ j ∈ range m, c (j+1+1) * s (m+2+1-(j+1+1)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [hs _ (by omega) (by omega), mul_zero]
  simp [hz, show m+2+1-(m+2) = 1 by omega, add_comm, add_left_comm, add_assoc]

lemma correctedExp_moments (a : ℂ) (n : ℕ) (hn : 2 ≤ n) (s : ℕ → ℂ)
    (hN : ∀ k, 1 ≤ k → (k : ℂ) * (correctedExp a n).coeff k +
        ∑ j ∈ range k, (correctedExp a n).coeff j * s (k-j) = 0) :
    s 1 = a ∧ (∀ k, 2 ≤ k → k < n → s k = 0) ∧
      s n = n * expPartial a n ∧
      s (n+1) = ((n+1 : ℕ) : ℂ) * a * expPartial a n +
        (-a)^(n+1)/(n.factorial : ℂ) := by
  have hsmall (j : ℕ) (hj : j < n) :
      (correctedExp a n).coeff j = expCoeff a j := by
    simp [correctedExp_coeff, hj.le, hj.ne]
  have hzero : (correctedExp a n).coeff 0 = 1 := by
    rw [hsmall 0 (by omega), expCoeff_zero]
  have hone : (correctedExp a n).coeff 1 = -a := by
    rw [hsmall 1 (by omega), expCoeff_one]
  have htop : (correctedExp a n).coeff n = expCoeff a n - expPartial a n := by
    simp [correctedExp_coeff]
  have habove : (correctedExp a n).coeff (n+1) = 0 := by
    simp [correctedExp_coeff]
  have hs1 : s 1 = a := by
    have h := hN 1 (by decide)
    simp [hone, hzero] at h
    linear_combination h
  have hz : ∀ k, 2 ≤ k → k < n → s k = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk hkn
      have h := hN k (by omega)
      rw [newton_middle_sum _ _ hk (fun i hi hik => ih i hik hi (by omega)),
        hzero, one_mul, hs1, hsmall k hkn, hsmall (k-1) (by omega)] at h
      have hr := expCoeff_step a (k-1)
      rw [show k-1+1=k by omega] at hr
      linear_combination h - hr
  have hsn : s n = n * expPartial a n := by
    have h := hN n (by omega)
    rw [newton_middle_sum _ _ hn hz, hzero, one_mul, hs1, htop, hsmall (n-1) (by omega)] at h
    have hr := expCoeff_step a (n-1)
    rw [show n-1+1=n by omega] at hr
    linear_combination h - hr
  refine ⟨hs1, hz, hsn, ?_⟩
  have h := hN (n+1) (by omega)
  rw [newton_last_sum _ _ hn hz, habove, hzero, hone, htop, hs1, hsn] at h
  simp only [expCoeff, pow_succ, Nat.cast_add, Nat.cast_one, mul_zero, zero_add, one_mul] at h ⊢
  linear_combination h

end OMA973

open Polynomial Finset

namespace OMA973

lemma tuple_on_interval (n : ℕ) (hn : 2 ≤ n) (z : Fin n → ℂ)
    (hz : ∃ i, z i = 1) :
    ∃ w : ℕ → ℂ, (∃ r ∈ Icc 1 n, w r = 1) ∧ 1 ≤ ‖w 1‖ ∧ (∀ i ∈ Icc 1 n, ‖w i‖ ≤ ‖w 1‖) ∧
      ∀ k : ℕ, ∑ i ∈ Icc 1 n, w i ^ k = ∑ i, z i ^ k := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  letI : Nonempty (Fin n) := ⟨i0⟩
  obtain ⟨imax, hm⟩ := Finite.exists_max (fun j => ‖z j‖)
  let e := Equiv.swap i0 imax
  let idx (i : ℕ) : Fin n := if h : i-1 < n then ⟨i-1, h⟩ else i0
  let w (i : ℕ) := z (e (idx i))
  have h1 : w 1 = z imax := by
    have h : 0 < n := by omega
    have he : idx 1 = i0 := by simp [idx, i0, h]
    simp [w, he, e]
  obtain ⟨i, hi⟩ := hz
  refine ⟨w, ?_, ?_, fun j _ => ?_, ?_⟩
  · let t := e.symm i
    refine ⟨t.val+1, mem_Icc.mpr ⟨by omega, by have := t.isLt; omega⟩, ?_⟩
    have ht : idx (t.val+1) = t := by simp [idx, t.isLt]
    simpa [w, ht, t] using hi
  · rw [h1]
    simpa [hi] using hm i
  · rw [h1]
    exact hm _
  · intro k
    have hi : Icc 1 n = Ico 1 (n+1) := by
      ext j
      simp only [mem_Icc, mem_Ico]
      omega
    rw [hi, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    rw [← Fin.sum_univ_eq_sum_range (fun j => w (1+j)^k) n]
    calc
      ∑ j : Fin n, w (1 + (j : ℕ)) ^ k = ∑ j : Fin n, z (e j) ^ k := by
        apply Finset.sum_congr rfl
        intro j _
        have he : idx (1 + (j : ℕ)) = j := by
          simp [idx, Nat.add_comm 1, j.isLt]
        simp [w, he]
      _ = ∑ j, z j ^ k := e.sum_comp (fun j => z j ^ k)

lemma raw_complex_moments_with_one (n : ℕ) (hn : 2 ≤ n) (a : ℂ) :
    ∃ w : ℕ → ℂ, (∃ r ∈ Icc 1 n, w r = 1) ∧ 1 ≤ ‖w 1‖ ∧ (∀ i ∈ Icc 1 n, ‖w i‖ ≤ ‖w 1‖) ∧
      (∀ k ∈ Ico 2 n, ∑ i ∈ Icc 1 n, w i ^ k = 0) ∧
      (∑ i ∈ Icc 1 n, w i ^ n) = n * expPartial a n ∧
      (∑ i ∈ Icc 1 n, w i ^ (n + 1)) =
        ((n+1 : ℕ) : ℂ) * a * expPartial a n + (-a)^(n+1)/(n.factorial : ℂ) := by
  classical
  have hp : (correctedExp a n).coeff 0 = 1 := by
    simp [correctedExp_coeff, show 0 ≠ n by omega, expCoeff_zero]
  obtain ⟨z, hone, hprod⟩ :=
    exists_factor_tuple n (correctedExp a n) hp (correctedExp_natDegree a n) (correctedExp_eval_one a n)
  have hN (k : ℕ) (hk : 1 ≤ k) := OMA.E973.factorPowerSumNewton z k hk
  have hrule (k : ℕ) (hk : 1 ≤ k) :
      (k : ℂ) * (correctedExp a n).coeff k +
        ∑ j ∈ range k, (correctedExp a n).coeff j * ∑ i, z i ^ (k-j) = 0 := by
    simpa only [hprod] using hN k hk
  obtain ⟨_, hmid, hl, hr⟩ := correctedExp_moments a n hn (fun k => ∑ i, z i ^ k) hrule
  obtain ⟨w, hroot, hw, hwmax, hwk⟩ := tuple_on_interval n hn z hone
  refine ⟨w, hroot, hw, hwmax, fun k hk => (hwk k).trans (hmid k (mem_Ico.mp hk).1 (mem_Ico.mp hk).2), ?_, ?_⟩
  · exact (hwk n).trans hl
  · exact (hwk (n+1)).trans hr

lemma raw_complex_moments (n : ℕ) (hn : 2 ≤ n) (a : ℂ) :
    ∃ w : ℕ → ℂ, 1 ≤ ‖w 1‖ ∧ (∀ i ∈ Icc 1 n, ‖w i‖ ≤ ‖w 1‖) ∧
      (∀ k ∈ Ico 2 n, ∑ i ∈ Icc 1 n, w i ^ k = 0) ∧
      (∑ i ∈ Icc 1 n, w i ^ n) = n * expPartial a n ∧
      (∑ i ∈ Icc 1 n, w i ^ (n + 1)) =
        ((n+1 : ℕ) : ℂ) * a * expPartial a n + (-a)^(n+1)/(n.factorial : ℂ) := by
  obtain ⟨w, _, hrest⟩ := raw_complex_moments_with_one n hn a
  exact ⟨w, hrest⟩

lemma raw_exp_moments (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    let t := ∑ j ∈ range (n+1), (-a)^j / (j.factorial : ℝ)
    ∃ w : ℕ → ℂ, (∃ r ∈ Icc 1 n, w r = 1) ∧
      (∀ k ∈ Ico 2 n, ∑ i ∈ Icc 1 n, w i ^ k = 0) ∧
      (∑ i ∈ Icc 1 n, w i ^ n) = (((n : ℝ) * t : ℝ) : ℂ) ∧
      (∑ i ∈ Icc 1 n, w i ^ (n + 1)) =
        ((((n : ℝ) + 1) * a * t + (-a) ^ (n + 1) / (n.factorial : ℝ) : ℝ) : ℂ) := by
  classical
  dsimp only
  obtain ⟨w, hroot, _, _, hmid, hl, hr⟩ := raw_complex_moments_with_one n hn (a : ℂ)
  refine ⟨w, hroot, hmid, ?_, ?_⟩
  · rw [hl]
    simp [expPartial, expCoeff, Complex.ofReal_sum]
  · rw [hr]
    simp [expPartial, expCoeff, Complex.ofReal_sum]

end OMA973

open Finset

namespace OMA.Erdos973Bounds

private lemma exp_tail_bound {x : ℝ} {k : ℕ} (h : |x| / (k + 1 : ℝ) ≤ 1 / 2) :
    |Real.exp x - ∑ j ∈ range k, x ^ j / j.factorial| ≤ |x| ^ k / k.factorial * 2 := by
  have h' : ‖(x : ℂ)‖ / (k.succ : ℝ) ≤ 1 / 2 := by simpa using h
  convert Complex.exp_bound' h' using 1 <;> norm_cast

private lemma exp_neg_fifth : Real.exp (-(1 / 5 : ℝ)) ≤ 5 / 6 := by
  rw [Real.exp_neg, ← one_div, div_le_iff₀ (Real.exp_pos _)]
  linarith [Real.add_one_le_exp (1 / 5 : ℝ)]

private lemma exp_two_fifths : Real.exp (2 / 5 : ℝ) ≤ 5 / 3 := by
  have h := Real.one_sub_le_exp_neg (2 / 5 : ℝ)
  rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos _)] at h
  linarith

private lemma poly_geom_bound (n : ℕ) (hn : 64 ≤ n) :
    ((n : ℝ) + 1)^2 * (101/120 : ℝ)^n < 1 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h64 : (64 : ℝ) ≤ n := by exact_mod_cast hn
    have hratio : ((n : ℝ) + 2)^2 * (101/120) ≤ ((n : ℝ) + 1)^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h64) (Nat.cast_nonneg (α := ℝ) n)]
    calc
      _ = (((n : ℝ) + 2)^2 * (101/120)) * (101/120 : ℝ)^n := by
        rw [Nat.cast_succ, pow_succ (101/120 : ℝ)]
        ring
      _ ≤ ((n : ℝ) + 1)^2 * (101/120 : ℝ)^n :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ < 1 := ih

lemma erdos973_large_bounds (n : ℕ) (hn : 64 ≤ n) :
    let a : ℝ := n / 5
    let T : ℝ := ∑ j ∈ range (n+1), (-a)^j / j.factorial
    |n * T| < (101/100 : ℝ)^(-(n : ℝ)) ∧
      |((n : ℝ)+1) * a * T + (-a)^(n+1) / n.factorial| <
        (101/100 : ℝ)^(-(n : ℝ)) := by
  let a : ℝ := n / 5
  let T : ℝ := ∑ j ∈ range (n+1), (-a)^j / j.factorial
  let R : ℝ := (5/6 : ℝ)^n
  change |(n : ℝ)*T| < _ ∧ |((n : ℝ)+1)*a*T + (-a)^(n+1) / n.factorial| < _
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcoeff : a^n / n.factorial ≤ R := by
    calc
      _ = ((2*a)^n / n.factorial)/(2 : ℝ)^n := by
        rw [mul_pow]
        field_simp <;> ring
      _ ≤ Real.exp (2*a)/(2 : ℝ)^n :=
        div_le_div_of_nonneg_right (Real.pow_div_factorial_le_exp (by positivity) n) (by positivity)
      _ = (Real.exp (2/5)/2)^n := by
        rw [div_pow, ← Real.exp_nat_mul]
        congr 2
        dsimp [a]
        ring
      _ ≤ R := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [exp_two_fifths]
  have he : Real.exp (-a) ≤ R := by
    calc
      _ = (Real.exp (-(1/5 : ℝ)))^n := by
        rw [← Real.exp_nat_mul]
        congr 1
        dsimp [a]
        ring
      _ ≤ R := pow_le_pow_left₀ (Real.exp_nonneg _) exp_neg_fifth n
  have hcoeff' : a^(n+1)/(n+1).factorial ≤ a^n / n.factorial := by
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    have hfac : (0 : ℝ) < n.factorial := by positivity
    have hnext : a ≤ (n : ℝ)+1 := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) n]
    apply (div_le_div_iff₀ (by positivity) hfac).mpr
    calc
      _ = (a^n * (n.factorial : ℝ)) * a := by ring
      _ ≤ (a^n * (n.factorial : ℝ)) * ((n : ℝ) + 1) := by gcongr
      _ = _ := by ring
  have herr : |Real.exp (-a) - T| ≤ 2*R := by
    have hh : |-a| / ((n+1 : ℕ) + 1 : ℝ) ≤ 1/2 := by
      rw [abs_neg, abs_of_nonneg ha, div_le_iff₀ (by positivity)]
      push_cast
      dsimp [a]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hx := exp_tail_bound hh
    rw [abs_neg, abs_of_nonneg ha] at hx
    exact hx.trans (by linarith [hcoeff'.trans hcoeff])
  have hT : |T| ≤ 3 * R := by
    obtain ⟨hl, hu⟩ := abs_le.mp herr
    rw [abs_le]
    constructor <;> linarith [Real.exp_pos (-a)]
  have hsmall : ((n : ℝ)+1)^2 * R < (101/100 : ℝ)^(-(n : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ← one_div, lt_div_iff₀ (by positivity)]
    calc
      _ = ((n : ℝ)+1)^2 * (101/120 : ℝ)^n := by
        dsimp [R]
        rw [mul_assoc, ← mul_pow]
        norm_num
      _ < 1 := poly_geom_bound n hn
  constructor
  · apply lt_of_le_of_lt _ hsmall
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
    calc
      _ ≤ (n : ℝ) * (3*R) := mul_le_mul_of_nonneg_left hT (by positivity)
      _ = (3*n : ℝ)*R := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hR
        nlinarith [sq_nonneg ((n : ℝ)-1), Nat.cast_nonneg (α := ℝ) n]
  · apply lt_of_le_of_lt _ hsmall
    calc
      _ ≤ |((n : ℝ)+1)*a*T| + |(-a)^(n+1)/(n.factorial : ℝ)| := abs_add_le _ _
      _ = ((n : ℝ)+1)*a*|T| + a*(a^n/(n.factorial : ℝ)) := by
        rw [abs_mul, abs_of_nonneg (show 0 ≤ ((n : ℝ)+1)*a by positivity), abs_div,
          abs_pow, abs_neg, abs_of_nonneg ha, abs_of_nonneg (by positivity : 0 ≤ (n.factorial : ℝ)),
          pow_succ]
        ring
      _ ≤ ((n : ℝ)+1)*a*(3*R) + a*R :=
        add_le_add (mul_le_mul_of_nonneg_left hT (by positivity)) (mul_le_mul_of_nonneg_left hcoeff ha)
      _ = ((3*((n : ℝ)+1)+1)*a)*R := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hR
        dsimp [a]
        nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]

end OMA.Erdos973Bounds

open Finset

namespace OMA.DiskFinite

lemma split_sum (f : ℕ → ℂ) (m : ℕ) :
    (∑ i ∈ Icc 1 (m + 1), f i) = f 1 + ∑ j ∈ range m, f (j + 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (a := 1) (b := m + 1) (by omega) f, ih, sum_range_succ]
    simp [Nat.add_assoc, add_assoc]

lemma half_sum (m : ℕ) (v : ℂ) (hq : v ^ (2 * m + 1) = 1)
    (hv : v ≠ 1) (hn : ‖v‖ = 1) :
    (v * ∑ j ∈ range m, v ^ j).re = -(1/2 : ℝ) := by
  let S := v * ∑ j ∈ range m, v ^ j
  let u := v ^ (m + 1)
  have hu : u ^ 2 = v := by
    dsimp [u]
    rw [← pow_mul, show (m + 1) * 2 = (2 * m + 1) + 1 by omega, pow_succ, hq, one_mul]
  have hune : u ≠ 1 := by
    intro hh
    exact hv (by simpa [hh] using hu.symm)
  have hgeom : S * (v - 1) = u - v := by
    dsimp [S, u]
    rw [pow_succ]
    linear_combination v * geom_sum_mul v m
  have hprod : (u - 1) * (S + u * (1 + S)) = 0 := by
    rw [← hu] at hgeom
    linear_combination hgeom
  have hsum := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hune)
  have heq : S = -(u * (1 + S)) := eq_neg_of_add_eq_zero_left hsum
  have hun : ‖u‖ = 1 := by simp [u, norm_pow, hn]
  have habs : ‖S‖ = ‖1 + S‖ := calc
    ‖S‖ = ‖-(u * (1 + S))‖ := congrArg norm heq
    _ = ‖1 + S‖ := by rw [norm_neg, norm_mul, hun, one_mul]
  have hs := congrArg (fun x : ℝ => x ^ 2) habs
  change S.re = _
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, zero_add] at hs
  nlinarith

lemma scale_lt (S : ℂ) (t : ℝ) (hRe : S.re = -(1/2 : ℝ))
    (ht : 0 < t) (hs : t * ‖S‖ ^ 2 < 1) : ‖1 + (t : ℂ) * S‖ < 1 := by
  have hid : ‖1 + (t : ℂ) * S‖ ^ 2 = 1 + 2*t*S.re + t^2*‖S‖^2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im]
    ring
  rw [hRe] at hid
  have hneg : t * (t * ‖S‖^2 - 1) < 0 := mul_neg_of_pos_of_neg ht (by linarith)
  nlinarith [sq_nonneg (‖1 + (t : ℂ) * S‖ - 1)]

lemma finite_general (m : ℕ) (hm : 2 ≤ m) :
    ∃ z : ℕ → ℂ, z 1 = 1 ∧ (∀ i ∈ Icc 1 (m + 1), ‖z i‖ ≤ 1) ∧
      ∀ k ∈ Icc 2 (m + 1 + 1), ‖∑ i ∈ Icc 1 (m + 1), z i ^ k‖ < 1 := by
  let q := 2 * m + 1
  have hq : q ≠ 0 := by dsimp [q]; omega
  let w := Complex.exp (2 * Real.pi * Complex.I / q)
  have hw : IsPrimitiveRoot w q := Complex.isPrimitiveRoot_exp q hq
  have hwn : ‖w‖ = 1 := hw.norm'_eq_one hq
  let r : ℝ := 1 / ((m : ℝ)^2 + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [sq_nonneg (m : ℝ)]
  let z : ℕ → ℂ := fun i => if i = 1 then 1 else (r : ℂ) * w ^ (i - 1)
  have hz1 : z 1 = 1 := by simp [z]
  refine ⟨z, hz1, ?_, ?_⟩
  · intro i _
    by_cases hi : i = 1
    · simp [hi, hz1]
    · simpa [z, hi, norm_mul, norm_pow, hwn, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr] using hr1
  · intro k hk
    obtain ⟨hk0, hkm⟩ := Finset.mem_Icc.mp hk
    let v := w ^ k
    have hv : v ≠ 1 := hw.pow_ne_one_of_pos_of_lt (by omega) (by dsimp [q]; omega)
    have hvn : ‖v‖ = 1 := by simp [v, norm_pow, hwn]
    have hvq : v ^ (2 * m + 1) = 1 := by
      change (w ^ k) ^ q = 1
      rw [← pow_mul, Nat.mul_comm k q, pow_mul, hw.pow_eq_one, one_pow]
    let S := v * ∑ j ∈ range m, v ^ j
    have hRe : S.re = -(1/2 : ℝ) := half_sum m v hvq hv hvn
    have hS : ‖S‖ ≤ m := calc
      ‖S‖ = ‖∑ j ∈ range m, v ^ j‖ := by simp [S, norm_mul, hvn]
      _ ≤ ∑ j ∈ range m, ‖v ^ j‖ := norm_sum_le _ _
      _ = (m : ℝ) := by simp [norm_pow, hvn]
    have ht : 0 < r^k := pow_pos hr _
    have htr : r^k ≤ r := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [pow_succ]
      exact mul_le_of_le_one_left hr.le (pow_le_one₀ hr.le hr1)
    have hbound : r^k * ‖S‖^2 < 1 := calc
      r^k * ‖S‖^2 ≤ r * (m : ℝ)^2 := by gcongr
      _ < 1 := by
        dsimp [r]
        rw [one_div_mul_eq_div]
        apply (div_lt_iff₀ (by positivity)).2
        linarith
    have hterm (j : ℕ) : z (j+2) ^ k = ((r^k : ℝ) : ℂ) * (v ^ j * v) := by
      have hj : j + 2 ≠ 1 := by omega
      simp only [z, if_neg hj, show j + 2 - 1 = j + 1 by omega,
        mul_pow, Complex.ofReal_pow, v]
      rw [← pow_mul, Nat.mul_comm (j + 1) k, pow_mul, pow_succ]
    have hid : (∑ i ∈ Icc 1 (m+1), z i ^ k) = 1 + ((r^k : ℝ) : ℂ) * S := by
      rw [split_sum _ m]
      simp only [hz1, one_pow, hterm, ← Finset.mul_sum, ← Finset.sum_mul, S]
      ring
    rw [hid]
    exact scale_lt S _ hRe ht hbound

lemma finite_two :
    ∃ z : ℕ → ℂ, z 1 = 1 ∧ (∀ i ∈ Icc 1 2, ‖z i‖ ≤ 1) ∧
      ∀ k ∈ Icc 2 3, ‖∑ i ∈ Icc 1 2, z i ^ k‖ < 1 := by
  let b : ℂ := ⟨1/4, 1/2⟩
  let z : ℕ → ℂ := fun i => if i = 1 then 1 else b
  have hz1 : z 1 = 1 := by simp [z]
  have hb : ‖b‖ ^ 2 = 5/16 := by norm_num [b, Complex.sq_norm, Complex.normSq_apply]
  refine ⟨z, hz1, ?_, ?_⟩
  · intro i _
    by_cases hi : i = 1
    · simp [hi, hz1]
    · simp [z, hi]
      nlinarith [sq_nonneg (‖b‖ - 1)]
  · intro k hk
    obtain ⟨hk2,hk3⟩ := Finset.mem_Icc.mp hk
    rw [split_sum _ 1]
    simp only [sum_range_one, hz1, one_pow, Nat.zero_add]
    have hzb : z 2 = b := by norm_num [z]
    rw [hzb]
    interval_cases k
    · have h : ‖1 + b^2‖^2 = 185/256 := by
        norm_num [b, Complex.sq_norm, Complex.normSq_apply, pow_succ,
          Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      nlinarith [sq_nonneg (‖1+b^2‖ - 1)]
    · have h : ‖1 + b^3‖^2 = 2813/4096 := by
        norm_num [b, Complex.sq_norm, Complex.normSq_apply, pow_succ,
          Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      nlinarith [sq_nonneg (‖1+b^3‖ - 1)]

lemma finite_witness (n : ℕ) (hn : 2 ≤ n) :
    ∃ z : ℕ → ℂ, z 1 = 1 ∧ (∀ i ∈ Icc 1 n, ‖z i‖ ≤ 1) ∧
      ∀ k ∈ Icc 2 (n + 1), ‖∑ i ∈ Icc 1 n, z i ^ k‖ < 1 := by
  cases n with
  | zero => omega
  | succ m =>
    by_cases hm : 2 ≤ m
    · exact finite_general m hm
    · obtain rfl : m = 1 := by omega
      exact finite_two

end OMA.DiskFinite

namespace OMA.R_Erdos973_erdos_973_variants_le_one_R1

open Finset Filter
open scoped Topology

-- The reversed truncated exponential, corrected in degree n to have a root
-- at 1, gives these power sums by Newton's identities.
def H1 : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ a : ℝ,
    let t := ∑ j ∈ range (n + 1), (-a) ^ j / (j.factorial : ℝ)
    ∃ z : ℕ → ℂ, (∃ r ∈ Icc 1 n, z r = 1) ∧
      (∀ k ∈ Ico 2 n, ∑ i ∈ Icc 1 n, z i ^ k = 0) ∧
      (∑ i ∈ Icc 1 n, z i ^ n) = (((n : ℝ) * t : ℝ) : ℂ) ∧
      (∑ i ∈ Icc 1 n, z i ^ (n + 1)) =
        ((((n : ℝ) + 1) * a * t + (-a) ^ (n + 1) / (n.factorial : ℝ) : ℝ) : ℂ)

-- This is a scalar Taylor remainder estimate. It does not quantify over roots.
def H2 : Prop :=
  ∀ n : ℕ, 64 ≤ n →
    let a := (n : ℝ) / 5
    let t := ∑ j ∈ range (n + 1), (-a) ^ j / (j.factorial : ℝ)
    |(n : ℝ) * t| < (101 / 100 : ℝ) ^ (-(n : ℝ)) ∧
      |((n : ℝ) + 1) * a * t + (-a) ^ (n + 1) / (n.factorial : ℝ)| <
        (101 / 100 : ℝ) ^ (-(n : ℝ))

-- The initial range requires only a qualitative bound for each power sum.
def H3 : Prop :=
  ∀ n ∈ Ico 2 64, ∃ z : ℕ → ℂ,
    z 1 = 1 ∧ (∀ i ∈ Icc 1 n, ‖z i‖ ≤ 1) ∧
      ∀ k ∈ Icc 2 (n + 1), ‖∑ i ∈ Icc 1 n, z i ^ k‖ < 1

-- Continuity at 1 and finiteness make the exponential base uniform.
lemma finite_uniform (h : H3) :
    ∃ c : ℝ, 1 < c ∧ ∀ n ∈ Ico 2 64, ∃ z : ℕ → ℂ,
      z 1 = 1 ∧ (∀ i ∈ Icc 1 n, ‖z i‖ ≤ 1) ∧
        ∀ k ∈ Icc 2 (n + 1), ‖∑ i ∈ Icc 1 n, z i ^ k‖ < c ^ (-(n : ℝ)) := by
  have he : ∀ᶠ c : ℝ in 𝓝[>] (1 : ℝ), ∀ n ∈ Ico 2 64, ∃ z : ℕ → ℂ,
      z 1 = 1 ∧ (∀ i ∈ Icc 1 n, ‖z i‖ ≤ 1) ∧
        ∀ k ∈ Icc 2 (n + 1), ‖∑ i ∈ Icc 1 n, z i ^ k‖ < c ^ (-(n : ℝ)) := by
    apply (eventually_all_finset _).2
    intro n hn
    obtain ⟨z, hz, hdisk, hs⟩ := h n hn
    have hpow : ∀ᶠ c : ℝ in 𝓝[>] (1 : ℝ), ∀ k ∈ Icc 2 (n + 1),
        ‖∑ i ∈ Icc 1 n, z i ^ k‖ < c ^ (-(n : ℝ)) := by
      apply (eventually_all_finset _).2
      intro k hk
      have hlim := Real.continuousAt_rpow_const 1 (-(n : ℝ)) (Or.inl one_ne_zero)
      have hlt : ‖∑ i ∈ Icc 1 n, z i ^ k‖ < (1 : ℝ) ^ (-(n : ℝ)) := by
        simpa using hs k hk
      exact hlim.continuousWithinAt.tendsto.eventually (lt_mem_nhds hlt)
    filter_upwards [hpow] with c hc
    exact ⟨z, hz, hdisk, hc⟩
  have hgt : ∀ᶠ c : ℝ in 𝓝[>] (1 : ℝ), 1 < c := self_mem_nhdsWithin
  exact (hgt.and he).exists

lemma put_largest_first (n : ℕ) (hn : 2 ≤ n) (z : ℕ → ℂ)
    (hroot : ∃ r ∈ Icc 1 n, z r = 1) :
    ∃ y : ℕ → ℂ, 1 ≤ ‖y 1‖ ∧ (∀ i ∈ Icc 1 n, ‖y i‖ ≤ ‖y 1‖) ∧
      ∀ k : ℕ, (∑ i ∈ Icc 1 n, y i ^ k) = ∑ i ∈ Icc 1 n, z i ^ k := by
  obtain ⟨r, hr, hroot⟩ := hroot
  have hone : 1 ∈ Icc 1 n := mem_Icc.mpr ⟨le_rfl, by omega⟩
  obtain ⟨j, hj, hm⟩ := exists_max_image (Icc 1 n) (fun i => ‖z i‖) ⟨1, hone⟩
  have hmem : ∀ i, i ∈ Icc 1 n ↔ Equiv.swap 1 j i ∈ Icc 1 n := by
    intro i
    by_cases h : i = 1
    · subst i
      simp [hone, hj]
    by_cases h' : i = j
    · subst i
      simp [hone, hj]
    rw [Equiv.swap_apply_of_ne_of_ne h h']
  refine ⟨fun i => z (Equiv.swap 1 j i), ?_, ?_, ?_⟩
  · simpa [hroot] using hm r hr
  · intro i hi
    simpa using hm (Equiv.swap 1 j i) ((hmem i).mp hi)
  · intro k
    exact Finset.sum_equiv (Equiv.swap 1 j) hmem (fun _ _ => rfl)

lemma normalize_sum_le (n k : ℕ) (z : ℕ → ℂ) (hz : 1 ≤ ‖z 1‖) :
    ‖∑ i ∈ Icc 1 n, (z i / z 1) ^ k‖ ≤ ‖∑ i ∈ Icc 1 n, z i ^ k‖ := by
  simp only [div_pow, ← Finset.sum_div, norm_div, norm_pow]
  exact div_le_self (norm_nonneg _) (one_le_pow₀ hz)

theorem main : H1 → H2 → H3 → type_of% @Erdos973.erdos_973.variants.le_one := by
  intro h1 h2 h3
  obtain ⟨c, hc, hsmall⟩ := finite_uniform h3
  let b : ℝ := 101 / 100
  have hb : 1 < b := by norm_num [b]
  have hmin : 1 < min c b := lt_min hc hb
  refine ⟨min c b, hmin, ?_⟩
  intro n hn
  have hneg : -(n : ℝ) ≤ 0 := by positivity
  have hpos : 0 < min c b := zero_lt_one.trans hmin
  by_cases hlarge : 64 ≤ n
  · obtain ⟨w, hw, hzero, hlast, hnext⟩ := h1 n hn ((n : ℝ) / 5)
    obtain ⟨z, hz, hmax, hsum⟩ := put_largest_first n hn w hw
    obtain ⟨en, enext⟩ := h2 n hlarge
    have hzpos : 0 < ‖z 1‖ := zero_lt_one.trans_le hz
    have hne : z 1 ≠ 0 := norm_pos_iff.mp hzpos
    refine ⟨fun i => z i / z 1, div_self hne, ?_, ?_⟩
    · intro i hi
      rw [norm_div]
      exact (div_le_one hzpos).mpr (hmax i hi)
    · intro k hk
      have hraw : ‖∑ i ∈ Icc 1 n, z i ^ k‖ < b ^ (-(n : ℝ)) := by
        rw [hsum k]
        obtain ⟨hklo, hkhi⟩ := mem_Icc.mp hk
        rcases lt_trichotomy k n with h | h | h
        · rw [hzero k (mem_Ico.mpr ⟨hklo, h⟩), norm_zero]
          exact Real.rpow_pos_of_pos (zero_lt_one.trans hb) _
        · subst k
          rw [hlast, Complex.norm_real, Real.norm_eq_abs]
          exact en
        · have heq : k = n + 1 := by omega
          subst k
          rw [hnext, Complex.norm_real, Real.norm_eq_abs]
          exact enext
      exact ((normalize_sum_le n k z hz).trans_lt hraw).trans_le
        (Real.rpow_le_rpow_of_nonpos hpos (min_le_right c b) hneg)
  · obtain ⟨z, hz, hdisk, hs⟩ := hsmall n (mem_Ico.mpr ⟨hn, by omega⟩)
    exact ⟨z, hz, hdisk, fun k hk => (hs k hk).trans_le
      (Real.rpow_le_rpow_of_nonpos hpos (min_le_left c b) hneg)⟩

end OMA.R_Erdos973_erdos_973_variants_le_one_R1

theorem OMA.solution : type_of% @Erdos973.erdos_973.variants.le_one := by
  apply OMA.R_Erdos973_erdos_973_variants_le_one_R1.main
  · exact OMA973.raw_exp_moments
  · exact OMA.Erdos973Bounds.erdos973_large_bounds
  · intro n hn
    exact OMA.DiskFinite.finite_witness n (Finset.mem_Ico.mp hn).1
