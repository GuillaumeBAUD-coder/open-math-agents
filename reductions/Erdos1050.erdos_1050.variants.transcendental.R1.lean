import FormalConjectures.ErdosProblems.«1050»

/-! A finite rational certificate per nonlinear polynomial for all admissible integer shifts. -/

namespace OMA.R_Erdos1050_erdos_1050_variants_transcendental_R1

open Finset

/-- The degree-one case, a specialization of Borwein's published irrationality theorem. -/
def H1 : Prop :=
  ∀ t : ℤ, t ≠ 0 → (∀ n : ℕ, 1 ≤ n → t ≠ -(2 : ℤ) ^ n) →
    Irrational (∑' n : ℕ, 1 / ((2 : ℝ) ^ (n + 1) + t))

/-- For each remaining possible minimal polynomial, find one pair of cutoffs for all shifts.
The first finite rational test covers the reciprocals that approximate large shifts.
The second tests finite partial sums for the bounded shifts. -/
def H2 : Prop :=
  ∀ p : Polynomial ℚ, p.Monic → Irreducible p → 2 ≤ p.natDegree →
    (∀ m : ℕ, 2 ≤ m → p ≠ Polynomial.X ^ 2 - Polynomial.C (m : ℚ)) →
    let passes (a r : ℚ) := r *
      (∑ i ∈ range (p.natDegree + 1), |p.coeff i| * i * (|a| + r) ^ (i - 1)) < |p.eval a|
    ∃ K L : ℕ, K + 2 ≤ L ∧
      (∀ d ∈ Icc (-(2 : ℤ) ^ K) (2 ^ K), passes (1 / (d : ℚ)) ((K + 3) / (2 : ℚ) ^ K)) ∧
      (∀ t ∈ Ioo (-(2 : ℤ) ^ (K + 1)) (2 ^ (K + 1)), t ≠ 0 →
        (∀ j ∈ range (K + 1), t ≠ -(2 : ℤ) ^ (j + 1)) →
        passes (∑ n ∈ range L, 1 / ((2 : ℚ) ^ (n + 1) + t)) (2 / (2 : ℚ) ^ L))

/-- Only the two powers neighboring the shift need special treatment. At least one of
their denominators has magnitude at least 2^k. -/
theorem locate_in_annulus (t : ℤ) (k : ℕ)
    (hlo : (2 : ℝ) ^ (k + 1) ≤ |(t : ℝ)|)
    (hhi : |(t : ℝ)| ≤ 2 ^ (k + 2)) :
    ∃ d : ℤ, |(∑' n : ℕ, 1 / ((2 : ℝ) ^ (n + 1) + t)) - 1 / d| ≤
      (k + 2 : ℝ) / 2 ^ k := by
  let f := fun n : ℕ => 1 / ((2 : ℝ) ^ (n + 1) + t)
  have lower (a : ℝ) (ha : 0 ≤ a) : |(t : ℝ)| - a ≤ |a + t| := by
    have h := abs_sub_le (t : ℝ) (-a) 0
    rw [sub_zero, sub_zero, abs_neg, sub_neg_eq_add, add_comm (t : ℝ), abs_of_nonneg ha] at h
    linarith
  have upper (a : ℝ) (ha : 0 ≤ a) : a - |(t : ℝ)| ≤ |a + t| := by
    have h := abs_sub_le a (-(t : ℝ)) 0
    rw [sub_zero, sub_zero, abs_neg, sub_neg_eq_add, abs_of_nonneg ha] at h
    linarith
  have habs (n : ℕ) {u : ℝ} (hu : 0 < u) (h : u ≤ |(2 : ℝ) ^ (n + 1) + t|) :
      |f n| ≤ 1 / u := by
    dsimp [f]; rw [abs_div, abs_one]
    exact one_div_le_one_div_of_le hu h
  have head : |∑ n ∈ range k, f n| ≤ (k : ℝ) / 2 ^ k := by
    calc
      _ ≤ ∑ n ∈ range k, |f n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ range k, 1 / (2 : ℝ) ^ k := by
        apply sum_le_sum
        intro n hn
        apply habs _ (by positivity)
        apply le_trans _ (lower _ (by positivity))
        have hnk : (2 : ℝ) ^ (n + 1) ≤ 2 ^ k :=
          pow_le_pow_right₀ (by norm_num) (mem_range.mp hn)
        rw [pow_succ] at hlo
        linarith
      _ = _ := by simp [div_eq_mul_inv]
  have late (n : ℕ) : |f (n + (k + 2))| ≤ (1 / (2 : ℝ) ^ (k + 2)) * (1 / 2 : ℝ) ^ n := by
    have he : (1 / (2 : ℝ) ^ (k + 2)) * (1 / 2 : ℝ) ^ n = 1 / 2 ^ (n + (k + 2)) := by
      rw [pow_add (2 : ℝ) n (k + 2)]; simp [div_eq_mul_inv, mul_comm]
    rw [he]; apply habs _ (by positivity)
    apply le_trans _ (upper _ (by positivity))
    have hnk : (2 : ℝ) ^ (k + 2) ≤ 2 ^ (n + (k + 2)) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    rw [pow_succ (2 : ℝ) (n + (k + 2))]
    linarith
  have hg := (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
    (1 / (2 : ℝ) ^ (k + 2))
  have ht : Summable (fun n => f (n + (k + 2))) :=
    hg.summable.of_norm_bounded (fun n => by simpa only [Real.norm_eq_abs] using late n)
  have tail := ht.hasSum.norm_le_of_bounded hg (fun n => by simpa only [Real.norm_eq_abs] using late n)
  have htail : |∑' n : ℕ, f (n + (k + 2))| ≤ 1 / 2 ^ k := by
    rw [Real.norm_eq_abs] at tail
    apply tail.trans
    rw [pow_add (2 : ℝ) k 2]
    norm_num
    field_simp
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]
  have hf := (summable_nat_add_iff (k + 2)).mp ht
  have hsplit := hf.sum_add_tsum_nat_add (k + 2)
  rw [sum_range_succ, sum_range_succ] at hsplit
  let a := (2 : ℝ) ^ (k + 1) + t
  let b := (2 : ℝ) ^ (k + 2) + t
  have hmax : (2 : ℝ) ^ k ≤ |a| ∨ (2 : ℝ) ^ k ≤ |b| := by
    have h := abs_sub_le b 0 a
    have hdiff : b - a = (2 : ℝ) ^ (k + 1) := by dsimp [a,b]; ring
    rw [hdiff, abs_of_pos (by positivity), sub_zero, zero_sub, abs_neg, pow_succ] at h
    by_contra! hh
    linarith
  have bound (u : ℝ) (hu : |u| ≤ 1 / (2 : ℝ) ^ k) :
      |(∑ n ∈ range k, f n) + u + ∑' n : ℕ, f (n + (k + 2))| ≤ (k + 2 : ℝ) / 2 ^ k := by
    calc
      _ ≤ (|(∑ n ∈ range k, f n)| + |u|) + |∑' n : ℕ, f (n + (k + 2))| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
      _ ≤ (k : ℝ) / 2 ^ k + 1 / 2 ^ k + 1 / 2 ^ k := add_le_add (add_le_add head hu) htail
      _ = _ := by ring
  rcases hmax with ha | hb
  · refine ⟨(2 : ℤ) ^ (k + 2) + t, ?_⟩
    change |(∑' n, f n) - _| ≤ _
    have e : (1 : ℝ) / ↑((2 : ℤ) ^ (k + 2) + t) = f (k + 1) := by simp [f]
    rw [e, ← hsplit]
    convert bound (f k) (habs _ (by positivity) ha) using 2
    ring
  · refine ⟨(2 : ℤ) ^ (k + 1) + t, ?_⟩
    change |(∑' n, f n) - _| ≤ _
    have e : (1 : ℝ) / ↑((2 : ℤ) ^ (k + 1) + t) = f k := by simp [f]
    rw [e, ← hsplit]
    convert bound (f (k + 1)) (habs _ (by positivity) hb) using 2
    ring

/-- A polynomial with a root within δ of a satisfies this rational evaluation bound. -/
theorem polynomial_root_bound (p : Polynomial ℚ) (a : ℚ) (s : ℝ) (δ : ℚ) (hδ : 0 ≤ δ)
    (hs : Polynomial.aeval s p = 0) (hsa : |s - a| ≤ δ) :
    |(↑(p.eval a) : ℝ)| ≤ δ *
      (↑(∑ i ∈ range (p.natDegree + 1), |p.coeff i| * i * (|a| + δ) ^ (i - 1) : ℚ) : ℝ) := by
  have he : (↑(p.eval a) : ℝ) = ∑ i ∈ range (p.natDegree + 1), (p.coeff i : ℝ) * (a : ℝ) ^ i := by
    rw [Polynomial.eval_eq_sum_range]
    push_cast
    rfl
  rw [he, ← sub_zero (∑ i ∈ _, _), ← hs, Polynomial.aeval_eq_sum_range, ← sum_sub_distrib]
  simp_rw [Rat.smul_def, ← mul_sub]
  push_cast
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have hpow := abs_pow_sub_pow_le (a : ℝ) s i
  rw [abs_sub_comm (a : ℝ) s] at hpow
  calc
    _ ≤ |(p.coeff i : ℝ)| * (((δ : ℝ) * i) * (|(a : ℝ)| + δ) ^ (i - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply hpow.trans
      have hδr : 0 ≤ (δ : ℝ) := by exact_mod_cast hδ
      have hsbound : |s| ≤ |(a : ℝ)| + δ := by
        have h := abs_sub_le s (a : ℝ) 0
        rw [sub_zero, sub_zero] at h
        linarith
      gcongr
      exact max_le (by linarith) hsbound
    _ = _ := by ring

/-- At a bounded shift the dyadic tail beyond L is uniformly small. -/
theorem prefix_error (t : ℤ) (L : ℕ) (ht : |(t : ℝ)| ≤ 2 ^ L) :
    |(∑' n : ℕ, 1 / ((2 : ℝ) ^ (n + 1) + t)) -
      ↑(∑ n ∈ range L, 1 / ((2 : ℚ) ^ (n + 1) + t) : ℚ)| ≤ 2 / (2 : ℝ) ^ L := by
  let f := fun n : ℕ => 1 / ((2 : ℝ) ^ (n + 1) + t)
  have late (n : ℕ) : |f (n + L)| ≤ (1 / (2 : ℝ) ^ L) * (1 / 2 : ℝ) ^ n := by
    have hnl : (2 : ℝ) ^ L ≤ 2 ^ (n + L) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hden : (2 : ℝ) ^ (n + L) ≤ 2 ^ ((n + L) + 1) + t := by
      rw [pow_succ]; linarith [neg_abs_le (t : ℝ)]
    dsimp [f]
    rw [abs_div, abs_one, abs_of_pos ((by positivity : (0 : ℝ) < 2 ^ (n + L)).trans_le hden)]
    calc
      _ ≤ 1 / (2 : ℝ) ^ (n + L) := one_div_le_one_div_of_le (by positivity) hden
      _ = _ := by rw [pow_add]; simp [div_eq_mul_inv, mul_comm]
  have hg := (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
    (1 / (2 : ℝ) ^ L)
  have hs : Summable (fun n => f (n + L)) :=
    hg.summable.of_norm_bounded (fun n => by simpa only [Real.norm_eq_abs] using late n)
  have herr := hs.hasSum.norm_le_of_bounded hg (fun n => by simpa only [Real.norm_eq_abs] using late n)
  have hsplit := ((summable_nat_add_iff L).mp hs).sum_add_tsum_nat_add L
  have he : (↑(∑ n ∈ range L, 1 / ((2 : ℚ) ^ (n + 1) + t) : ℚ) : ℝ) = ∑ n ∈ range L, f n := by
    simp [f]
  change |(∑' n, f n) - _| ≤ _
  rw [he, ← hsplit, add_sub_cancel_left]
  norm_num [Real.norm_eq_abs, div_eq_mul_inv, mul_comm] at herr ⊢
  exact herr

theorem annulus_error_decreasing : Antitone (fun k : ℕ => (k + 2 : ℝ) / 2 ^ k) := by
  apply antitone_nat_of_succ_le
  intro k
  simp only [Nat.cast_succ, pow_succ]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k)]

/-- All shifts beyond the cutoff lie in the finite grid of rational intervals. -/
theorem finite_outer_cover (t : ℤ) (K : ℕ) (ht : 2 ^ (K + 1) ≤ t.natAbs) :
    ∃ d : ℤ, d.natAbs ≤ 2 ^ K ∧
      |(∑' n : ℕ, 1 / ((2 : ℝ) ^ (n + 1) + t)) - 1 / d| ≤ (K + 3 : ℝ) / 2 ^ K := by
  have hm : t.natAbs ≠ 0 := by
    have hp : 0 < (2 : ℕ) ^ (K + 1) := by positivity
    omega
  have hk := (Nat.le_log_iff_pow_le (by decide : 1 < 2) hm).mpr ht
  let k := Nat.log 2 t.natAbs - 1
  have he : k + 1 = Nat.log 2 t.natAbs := by dsimp [k]; omega
  have hKk : K ≤ k := by omega
  have hcast : (t.natAbs : ℝ) = |(t : ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs]; simp
  have hlo : (2 : ℝ) ^ (k + 1) ≤ |(t : ℝ)| := by
    rw [he, ← hcast]; exact_mod_cast Nat.pow_log_le_self 2 hm
  have hhi : |(t : ℝ)| ≤ 2 ^ (k + 2) := by
    rw [show k + 2 = (k + 1) + 1 by omega, he, ← hcast]
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < 2) t.natAbs).le
  obtain ⟨d, hd⟩ := locate_in_annulus t k hlo hhi
  have h := hd.trans (annulus_error_decreasing hKk)
  by_cases hcut : d.natAbs ≤ 2 ^ K
  · exact ⟨d, hcut, h.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))⟩
  · refine ⟨0, by simp, ?_⟩
    simp only [Int.cast_zero, div_zero, sub_zero]
    have hcastd : (d.natAbs : ℝ) = |(d : ℝ)| := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs]; simp
    have hden : (2 : ℝ) ^ K ≤ |(d : ℝ)| := by
      rw [← hcastd]; exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hcut))
    have hrec : |(1 : ℝ) / d| ≤ 1 / 2 ^ K := by
      rw [abs_div, abs_one]
      exact one_div_le_one_div_of_le (by positivity) hden
    have htri := abs_sub_le (∑' n : ℕ, 1 / ((2 : ℝ) ^ (n + 1) + t)) (1 / (d : ℝ)) 0
    rw [sub_zero, sub_zero] at htri
    calc
      _ ≤ _ := htri
      _ ≤ _ := add_le_add h hrec
      _ = _ := by ring

/-- Every shift belongs to an interval from one of two finite rational tables. -/
theorem finite_cover (K L : ℕ) (hKL : K + 2 ≤ L) (t : ℤ) :
    (∃ d ∈ Icc (-(2 : ℤ) ^ K) (2 ^ K),
      |(∑' n : ℕ, 1 / ((2 : ℝ) ^ (n + 1) + t)) - ↑(1 / (d : ℚ) : ℚ)| ≤
        ↑(((K + 3) / (2 : ℚ) ^ K) : ℚ)) ∨
    (t ∈ Ioo (-(2 : ℤ) ^ (K + 1)) (2 ^ (K + 1)) ∧
      |(∑' n : ℕ, 1 / ((2 : ℝ) ^ (n + 1) + t)) -
        ↑(∑ n ∈ range L, 1 / ((2 : ℚ) ^ (n + 1) + t) : ℚ)| ≤ ↑(2 / (2 : ℚ) ^ L : ℚ)) := by
  by_cases hsmall : t.natAbs < 2 ^ (K + 1)
  · have hcast : (t.natAbs : ℝ) = |(t : ℝ)| := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs]; simp
    have habs : |(t : ℝ)| ≤ 2 ^ L := by
      rw [← hcast]
      exact_mod_cast hsmall.le.trans (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : K + 1 ≤ L))
    have hmem : t ∈ Ioo (-(2 : ℤ) ^ (K + 1)) (2 ^ (K + 1)) := by
      rw [mem_Ioo, ← abs_lt, ← Int.natCast_natAbs]; exact_mod_cast hsmall
    exact Or.inr ⟨hmem, by simpa using prefix_error t L habs⟩
  · obtain ⟨d, hd, he⟩ := finite_outer_cover t K (le_of_not_gt hsmall)
    have hmem : d ∈ Icc (-(2 : ℤ) ^ K) (2 ^ K) := by
      rw [mem_Icc, ← abs_le, ← Int.natCast_natAbs]; exact_mod_cast hd
    exact Or.inl ⟨d, hmem, by simpa using he⟩

/-- The two finite tables exclude the specified polynomial at every admissible shift. -/
theorem excludes_of_certificate (p : Polynomial ℚ) (K L : ℕ) :
    let passes (a r : ℚ) := r *
      (∑ i ∈ range (p.natDegree + 1), |p.coeff i| * i * (|a| + r) ^ (i - 1)) < |p.eval a|
    K + 2 ≤ L →
      (∀ d ∈ Icc (-(2 : ℤ) ^ K) (2 ^ K), passes (1 / (d : ℚ)) ((K + 3) / (2 : ℚ) ^ K)) →
      (∀ t ∈ Ioo (-(2 : ℤ) ^ (K + 1)) (2 ^ (K + 1)), t ≠ 0 →
        (∀ j ∈ range (K + 1), t ≠ -(2 : ℤ) ^ (j + 1)) →
        passes (∑ n ∈ range L, 1 / ((2 : ℚ) ^ (n + 1) + t)) (2 / (2 : ℚ) ^ L)) →
      ∀ t : ℤ, t ≠ 0 → (∀ n : ℕ, 1 ≤ n → t ≠ -(2 : ℤ) ^ n) →
        Polynomial.aeval (∑' n : ℕ, 1 / ((2 : ℝ) ^ (n + 1) + t)) p ≠ 0 := by
  dsimp only
  intro hKL houter hinner t ht hnp hroot
  let s := ∑' n : ℕ, 1 / ((2 : ℝ) ^ (n + 1) + t)
  have exclude (a r : ℚ) (hr : 0 ≤ r) (he : |s - a| ≤ (r : ℝ))
      (test : r * (∑ i ∈ range (p.natDegree + 1),
        |p.coeff i| * i * (|a| + r) ^ (i - 1)) < |p.eval a|) : False := by
    have bound := polynomial_root_bound p a s r hr hroot he
    exact (not_lt_of_ge bound) (by
      simpa only [Rat.cast_mul, Rat.cast_abs] using (Rat.cast_lt (K := ℝ)).mpr test)
  rcases finite_cover K L hKL t with ⟨d, hd, he⟩ | ⟨ht', he⟩
  · exact exclude _ _ (by positivity) he (houter d hd)
  · exact exclude _ _ (by positivity) he (hinner t ht' ht (fun j _ => hnp (j+1) (by omega)))

open Polynomial in
/-- A concrete certificate with K = 5 and L = 7. -/
theorem square_ne_two (t : ℤ) (ht : t ≠ 0) (hnp : ∀ n : ℕ, 1 ≤ n → t ≠ -(2 : ℤ) ^ n) :
    (∑' n : ℕ, (1 : ℝ) / (2 ^ (n + 1) + t)) ^ 2 ≠ 2 := by
  let p : Polynomial ℚ := X ^ 2 - C 2
  have hdeg : p.natDegree = 2 := by simp [p]
  have hslope (a r : ℚ) :
      (∑ i ∈ range (p.natDegree + 1), |p.coeff i| * i * (|a| + r) ^ (i - 1)) =
      2 * (|a| + r) := by
    rw [hdeg]
    norm_num [sum_range_succ, p, coeff_X_pow, coeff_C]
  have heval (a : ℚ) : p.eval a = a ^ 2 - 2 := by simp [p]
  have h := excludes_of_certificate p 5 7
  dsimp only at h
  simp_rw [hslope, heval] at h
  have ho : ∀ d ∈ Icc (-32 : ℤ) 32,
      (1/4 : ℚ) * (2 * (|1 / (d : ℚ)| + 1/4)) < |(1 / (d : ℚ)) ^ 2 - 2| := by decide +kernel
  have hi : ∀ t ∈ Ioo (-64 : ℤ) 64, t ≠ 0 →
      (∀ j ∈ range 6, t ≠ -(2 : ℤ) ^ (j + 1)) →
      let a := ∑ n ∈ range 7, 1 / ((2 : ℚ) ^ (n+1) + t)
      (1/64 : ℚ) * (2 * (|a| + 1/64)) < |a ^ 2 - 2| := by decide +kernel
  have hx := h (by decide) (by norm_num at ho ⊢; exact ho) (by norm_num at hi ⊢; exact hi) t ht hnp
  simpa [p, sub_ne_zero] using hx

/-- All admissible shifts have absolute sum strictly below 5/3. -/
theorem uniform_abs_lt (t : ℤ) (ht : t ≠ 0) (hnp : ∀ n : ℕ, 1 ≤ n → t ≠ -(2 : ℤ) ^ n) :
    |∑' n : ℕ, (1 : ℝ) / (2 ^ (n + 1) + t)| < 5 / 3 := by
  let s := ∑' n : ℕ, (1 : ℝ) / (2 ^ (n + 1) + t)
  have near (a r : ℚ) (he : |s - a| ≤ (r : ℝ)) (hb : |a| + r < 5 / 3) : |s| < 5 / 3 := by
    have h := abs_sub_le s (a : ℝ) 0
    rw [sub_zero, sub_zero] at h
    have hc : |(a : ℝ)| + (r : ℝ) < 5 / 3 := by
      simpa only [Rat.cast_add, Rat.cast_abs, Rat.cast_div, Rat.cast_ofNat] using
        (Rat.cast_lt (K := ℝ)).mpr hb
    linarith
  have ho : ∀ d ∈ Icc (-32 : ℤ) 32, |1 / (d : ℚ)| + 1/4 < 5/3 := by decide +kernel
  have hi : ∀ t ∈ Ioo (-64 : ℤ) 64, t ≠ 0 → (∀ j ∈ range 6, t ≠ -(2 : ℤ) ^ (j+1)) →
      |∑ n ∈ range 7, 1 / ((2 : ℚ) ^ (n+1) + t)| + 1/64 < 5/3 := by decide +kernel
  rcases finite_cover 5 7 (by decide) t with ⟨d, hd, he⟩ | ⟨hd, he⟩
  · apply near _ _ he
    convert ho d hd using 1
    norm_num
  · apply near _ _ he
    convert hi t hd ht (fun j _ => hnp (j+1) (by omega)) using 1
    norm_num

/-- An unconditional exclusion of an infinite family of quadratic equations. -/
theorem square_ne_large_integer (t : ℤ) (ht : t ≠ 0) (hnp : ∀ n : ℕ, 1 ≤ n → t ≠ -(2 : ℤ) ^ n)
    (m : ℕ) (hm : 2 ≤ m) : (∑' n : ℕ, (1 : ℝ) / (2 ^ (n + 1) + t)) ^ 2 ≠ m := by
  rcases eq_or_lt_of_le hm with rfl | hlt
  · exact square_ne_two t ht hnp
  · have h := abs_lt.mp (uniform_abs_lt t ht hnp)
    have hc : (3 : ℝ) ≤ m := by exact_mod_cast hlt
    nlinarith [mul_pos (sub_pos.mpr h.2) (by linarith only [h.1] :
      0 < (∑' n : ℕ, (1 : ℝ) / (2 ^ (n + 1) + t)) + 5/3)]

theorem main : H1 → H2 → type_of% @Erdos1050.erdos_1050.variants.transcendental := by
  intro irrationality certificates t ht hnp halg
  let s := ∑' n : ℕ, 1 / ((2 : ℝ) ^ (n + 1) + t)
  have hi : IsIntegral ℚ s := halg.isIntegral
  let p := minpoly ℚ s
  have deg : 2 ≤ p.natDegree :=
    (minpoly.two_le_natDegree_iff hi).mpr (irrationality t ht hnp)
  have outside : ∀ m : ℕ, 2 ≤ m → p ≠ Polynomial.X ^ 2 - Polynomial.C (m : ℚ) := by
    intro m hm he
    have hr : Polynomial.aeval s p = 0 := minpoly.aeval _ _
    rw [he] at hr
    apply square_ne_large_integer t ht hnp m hm
    simpa [s, sub_eq_zero] using hr
  obtain ⟨K, L, hKL, houter, hinner⟩ :=
    certificates p (minpoly.monic hi) (minpoly.irreducible hi) deg outside
  exact excludes_of_certificate p K L hKL houter hinner t ht hnp (minpoly.aeval _ _)

end OMA.R_Erdos1050_erdos_1050_variants_transcendental_R1
