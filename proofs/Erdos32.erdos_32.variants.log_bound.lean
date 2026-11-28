/-
Disproof of Erdős Problem 32 (`Erdos32.erdos_32.variants.log_bound`).

The sieve and truncated divisor-sum core (namespace `LongGapsBetweenPrimes`) is
adapted from OpenAI's Apache-2.0 formalization `openai/LongGapsBetweenPrimes`
(https://github.com/openai/LongGapsBetweenPrimes, SPDX-License-Identifier: Apache-2.0).

The extension to large shifts and the disproof of O(log N) additive complements
to the primes follow Artyom Radomskii (arXiv:2610.14127, Oct 2026).
-/

-- Credit: @LiJiaHua1024

import FormalConjectures.ErdosProblems.«32»

/-!
# Disproof of Erdős Problem 32 (`log_bound`)
-/

namespace LongGapsBetweenPrimes
noncomputable section

/-- The j-fold natural logarithm used in the statement of Theorem 1.1. -/
def iteratedLog (j : ℕ) (x : ℝ) : ℝ := (Real.log^[j]) x

/-- The function on the right hand side of Theorem 1.1, without its constant. -/
def gapScale (x : ℝ) : ℝ :=
  Real.log x * (iteratedLog 2 x) ^ 2 * iteratedLog 4 x / (iteratedLog 3 x) ^ 2

/-- Consecutive primes, specified without choosing an enumeration. -/
def ConsecutivePrimes (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ ∀ r : ℕ, p < r → r < q → ¬r.Prime

/-- The precise conclusion to be proved. -/
def LongGapTheorem : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in Filter.atTop,
    ∃ p q : ℕ, ConsecutivePrimes p q ∧ (q : ℝ) ≤ X ∧ c * gapScale X ≤ (q - p : ℕ)

/-- The short-translate assertion of Proposition 1.2. -/
def ShortTranslates : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ᶠ x : ℝ in Filter.atTop,
    ∀ H : ℕ, x < H → (H : ℝ) ≤ x * (Real.log x) ^ 2 →
    ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 H → (S.card : ℝ) ≤ δ * x →
    ∀ b : ℕ, b < primorial ⌊x⌋₊ →
    ∃ t : ℕ, 1 ≤ t ∧ (t : ℝ) ≤ Real.exp x ∧
      ∀ s ∈ S, ¬Nat.Prime (b + primorial ⌊x⌋₊ * t + s)

/-- The normalization B in (3.1). -/
def normalizer (P : ℕ) : ℝ :=
  ∑ d ∈ P.divisors.erase 1, 1 / ((d.totient : ℝ) * Real.log d)

/-- The coefficient a(d) in (3.1). -/
def coefficient (P d : ℕ) : ℝ :=
  if d = 1 then 1 else -1 / (normalizer P * Real.log d)

/-- A divisor other than one is greater than one. -/
lemma one_lt_of_mem_divisors_erase_one {P d : ℕ}
    (hd : d ∈ P.divisors.erase 1) : 1 < d := by
  exact lt_of_le_of_ne (Nat.pos_of_mem_divisors (Finset.mem_of_mem_erase hd))
    (Finset.ne_of_mem_erase hd).symm

/-- The normalizer is positive when `P > 1`. -/
lemma normalizer_pos {P : ℕ} (hP : 1 < P) : 0 < normalizer P := by
  unfold normalizer
  apply Finset.sum_pos
  · intro d hd
    have hd' := one_lt_of_mem_divisors_erase_one hd
    have ht : 0 < (d.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d)
    exact one_div_pos.mpr (mul_pos ht (Real.log_pos (by exact_mod_cast hd')))
  · exact ⟨P, Finset.mem_erase.mpr ⟨ne_of_gt hP, Nat.mem_divisors_self P (by omega)⟩⟩

/-- For `P > 1`, coefficients at `d > 1` are negative. -/
lemma coefficient_neg {P d : ℕ} (hP : 1 < P) (hd : 1 < d) :
    coefficient P d < 0 := by
  rw [coefficient, if_neg (ne_of_gt hd)]
  exact div_neg_of_neg_of_pos (by norm_num)
    (mul_pos (normalizer_pos hP) (Real.log_pos (by exact_mod_cast hd)))

/-- Exact cancellation, equations (3.2) and (3.5). -/
theorem coefficient_cancellation {P : ℕ} (hP : 1 < P) :
    ∑ d ∈ P.divisors, coefficient P d / d.totient = 0 := by
  have hB : normalizer P ≠ 0 := ne_of_gt (normalizer_pos hP)
  have hsum : ∑ d ∈ P.divisors.erase 1, coefficient P d / d.totient =
      -(normalizer P)⁻¹ * normalizer P := by
    change _ = -(normalizer P)⁻¹ *
      ∑ d ∈ P.divisors.erase 1, 1 / ((d.totient : ℝ) * Real.log d)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [coefficient, if_neg (Finset.ne_of_mem_erase hd)]
    ring
  rw [← Finset.sum_erase_add _ _ (Nat.one_mem_divisors.mpr (by omega : P ≠ 0)),
    hsum]
  simp [coefficient, hB]

/-- The omitted terms in (3.11) have positive total mass. -/
theorem partial_cancellation {P : ℕ} (hP : 1 < P)
    (E : Finset ℕ) (hE : E ⊆ P.divisors) (h1 : 1 ∈ E) :
    ∑ d ∈ E, coefficient P d / d.totient =
      ∑ d ∈ P.divisors \ E, |coefficient P d| / d.totient := by
  have hsum := Finset.sum_sdiff hE (f := fun d => coefficient P d / d.totient)
  rw [coefficient_cancellation hP] at hsum
  rw [eq_neg_of_add_eq_zero_right hsum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rcases Finset.mem_sdiff.mp hd with ⟨hd, hdE⟩
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hdE h1
  rw [abs_of_neg (coefficient_neg hP
    (one_lt_of_mem_divisors_erase_one (Finset.mem_erase.mpr ⟨hd1, hd⟩))), neg_div]

/-- A divisor subsum containing one has nonnegative weighted coefficient sum. -/
lemma partial_cancellation_nonneg {P : ℕ} (hP : 1 < P)
    (E : Finset ℕ) (hE : E ⊆ P.divisors) (h1 : 1 ∈ E) :
    0 ≤ ∑ d ∈ E, coefficient P d / d.totient := by
  rw [partial_cancellation hP E hE h1]
  positivity

/-- The local factor as a function of a residue class with specified root. -/
def residueFactor {p : ℕ} (a t : Fin p) : ℝ :=
  if t = a then -1 else 1 / ((p : ℝ) - 1)

/-- Sum a constant function with one exceptional value. -/
lemma sum_one_exception {p : ℕ} (a : Fin p) (c d : ℝ) :
    (∑ t : Fin p, if t = a then c else d) = c + ((p : ℝ) - 1) * d := by
  simp [Finset.sum_ite, Finset.filter_eq', Finset.filter_ne',
    Nat.cast_sub (Nat.succ_le_of_lt (Fin.pos a))]

/-- The local mean is zero (Section 3.1). -/
theorem sum_residueFactor {p : ℕ} (hp : 1 < p) (a : Fin p) :
    ∑ t : Fin p, residueFactor a t = 0 := by
  have hp' : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ne_of_gt hp)
  simp [residueFactor, sum_one_exception, hp']

/-- The local square mean is 1/(p-1), before dividing the sum by p. -/
theorem sum_residueFactor_sq {p : ℕ} (hp : 1 < p) (a : Fin p) :
    (∑ t : Fin p, (residueFactor a t) ^ 2) = (p : ℝ) / ((p : ℝ) - 1) := by
  have hp' : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ne_of_gt hp)
  simp only [residueFactor, ite_pow, neg_one_sq, sum_one_exception]
  field_simp
  ring

/-- Distinct roots have negative covariance, as used in (3.9). -/
theorem sum_residueFactor_mul {p : ℕ} (hp : 1 < p) (a b : Fin p) (hab : a ≠ b) :
    (∑ t : Fin p, residueFactor a t * residueFactor b t) =
      -(p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
  have hmul (t : Fin p) :
      residueFactor a t * residueFactor b t =
        (1 / ((p : ℝ) - 1)) * (residueFactor a t + residueFactor b t) -
          (1 / ((p : ℝ) - 1)) ^ 2 := by
    unfold residueFactor
    split_ifs with ha hb
    · exact (hab (ha.symm.trans hb)).elim
    all_goals ring
  simp_rw [hmul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
    sum_residueFactor hp a, sum_residueFactor hp b]
  simp
  ring

/-- For squarefree `d`, its totient is the product of `p - 1` over its prime factors. -/
lemma totient_eq_prod_sub_one_of_squarefree {d : ℕ} (hd : Squarefree d) :
    d.totient = ∏ p ∈ d.primeFactors, (p - 1) := by
  have h := Nat.totient_mul_prod_primeFactors d
  rw [Nat.prod_primeFactors_of_squarefree hd] at h
  exact mul_right_cancel₀ hd.ne_zero (h.trans (mul_comm _ _))

/-- A_gamma in Lemma 3.1; A is its value at gamma = 0. -/
def coefficientMoment (P : ℕ) (γ : ℝ) : ℝ :=
  ∑ d ∈ P.divisors, coefficient P d ^ 2 * (d : ℝ) ^ γ / d.totient

/-- The absolute coefficient moment over nontrivial divisors. -/
def coefficientAbsMoment (P : ℕ) (γ : ℝ) : ℝ :=
  ∑ d ∈ P.divisors.erase 1, |coefficient P d| * (d : ℝ) ^ γ / d.totient

/-- Expand the coefficient moment at exponent zero. -/
lemma coefficientMoment_zero (P : ℕ) :
    coefficientMoment P 0 = ∑ d ∈ P.divisors, coefficient P d ^ 2 / d.totient := by
  simp [coefficientMoment]

/-- The divisor one gives a lower bound of one for the coefficient moment. -/
lemma coefficientMoment_ge_one {P : ℕ} (hP : P ≠ 0) (γ : ℝ) :
    1 ≤ coefficientMoment P γ := by
  have h := Finset.single_le_sum
    (f := fun d => coefficient P d ^ 2 * (d : ℝ) ^ γ / d.totient)
    (fun d _ => div_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Nat.cast_nonneg _)) (Nat.one_mem_divisors.mpr hP)
  simpa [coefficientMoment, coefficient] using h

/-- The exponential increment is at most `x * exp x`. -/
lemma exp_sub_one_le_mul_exp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_nonneg x)
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  linarith

/-- The power increment is at most `γ * v ^ γ * log v`. -/
lemma rpow_sub_one_le {v γ : ℝ} (hv : 0 < v) :
    v ^ γ - 1 ≤ γ * v ^ γ * Real.log v := by
  rw [Real.rpow_def_of_pos hv]
  nlinarith [exp_sub_one_le_mul_exp (Real.log v * γ)]

/-- A squared coefficient times `log d` equals its normalized absolute value. -/
lemma coefficient_sq_mul_log {P d : ℕ} (hP : 1 < P) (hd : 1 < d) :
    coefficient P d ^ 2 * Real.log d = |coefficient P d| / normalizer P := by
  rw [abs_of_neg (coefficient_neg hP hd), coefficient, if_neg (ne_of_gt hd)]
  have hB := ne_of_gt (normalizer_pos hP)
  have hlog := ne_of_gt (Real.log_pos (by exact_mod_cast hd : (1 : ℝ) < d))
  field_simp

/-- Control the change in the squared moment by the absolute moment. -/
lemma coefficientMoment_sub_le {P : ℕ} (hP : 1 < P) (γ : ℝ) :
    coefficientMoment P γ - coefficientMoment P 0 ≤
      (γ / normalizer P) * coefficientAbsMoment P γ := by
  rw [coefficientMoment, coefficientMoment_zero, ← Finset.sum_sub_distrib,
    ← Finset.sum_erase_add _ _ (Nat.one_mem_divisors.mpr (by omega : P ≠ 0))]
  simp only [Nat.cast_one, Real.one_rpow, Nat.totient_one, mul_one, div_one,
    sub_self, add_zero]
  unfold coefficientAbsMoment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hd' := one_lt_of_mem_divisors_erase_one hd
  calc
    coefficient P d ^ 2 * (d : ℝ) ^ γ / d.totient -
        coefficient P d ^ 2 / d.totient =
        coefficient P d ^ 2 * ((d : ℝ) ^ γ - 1) / d.totient := by ring
    _ ≤ coefficient P d ^ 2 * (γ * (d : ℝ) ^ γ * Real.log d) / d.totient :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (rpow_sub_one_le (by exact_mod_cast (zero_lt_one.trans hd'))) (sq_nonneg _))
        (Nat.cast_nonneg _)
    _ = (coefficient P d ^ 2 * Real.log d) * (γ * (d : ℝ) ^ γ) / d.totient := by ring
    _ = (γ / normalizer P) * (|coefficient P d| * (d : ℝ) ^ γ / d.totient) := by
      rw [coefficient_sq_mul_log hP hd']
      ring

/-- Rankin's tail estimate, in the finite form needed for (3.10). -/
theorem moment_tail_le {α : Type*} (s : Finset α) (f v : α → ℝ) (D β : ℝ)
    (hD : 0 < D) (hβ : 0 ≤ β) (hf : ∀ a ∈ s, 0 ≤ f a)
    (hv : ∀ a ∈ s, 0 ≤ v a) :
    (∑ a ∈ s.filter (fun a => D < v a), f a) ≤
      D ^ (-β) * ∑ a ∈ s, f a * (v a) ^ β := by
  rw [Real.rpow_neg hD.le, ← div_eq_inv_mul]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hD β)).mpr
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ a ∈ s.filter (fun a => D < v a), f a * (v a) ^ β := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨has, hav⟩ := Finset.mem_filter.mp ha
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hD.le hav.le hβ) (hf a has)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun a ha _ => mul_nonneg (hf a ha) (Real.rpow_nonneg (hv a ha) _))

/-- Divisors regarded as a finite index type. -/
abbrev DivisorIndex (P : ℕ) := {d : ℕ // d ∈ P.divisors}

/-- Tuples of `k` divisors of `P`. -/
abbrev DivisorTuple (P k : ℕ) := Fin k → DivisorIndex P

/-- The product of the divisors in a tuple. -/
def tupleProduct {P k : ℕ} (r : DivisorTuple P k) : ℕ := ∏ i, (r i).val

/-- The common truncated region R_k of (3.3). -/
def tupleRegion (P k : ℕ) (D : ℝ) : Finset (DivisorTuple P k) := by
  classical
  exact Finset.univ.filter fun r =>
    (∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) ∧ (tupleProduct r : ℝ) ≤ D

/-- The diagonal mass attached to one tuple in (3.9). -/
def tupleMass {P k : ℕ} (r : DivisorTuple P k) : ℝ :=
  ∏ i, coefficient P (r i).val ^ 2 / ((r i).val.totient : ℝ)

/-- The diagonal mass of a divisor tuple is nonnegative. -/
lemma tupleMass_nonneg {P k : ℕ} (r : DivisorTuple P k) : 0 ≤ tupleMass r := by
  unfold tupleMass
  positivity

/-- Rewrite a sum over divisor indices as a sum over the divisor finset. -/
lemma sum_divisorIndex (P : ℕ) (f : ℕ → ℝ) :
    (∑ d : DivisorIndex P, f d.val) = ∑ d ∈ P.divisors, f d := by
  exact Finset.sum_attach P.divisors f

/-- The total tuple mass is the `k`th power of the zero coefficient moment. -/
lemma sum_tupleMass (P k : ℕ) :
    (∑ r : DivisorTuple P k, tupleMass r) = coefficientMoment P 0 ^ k := by
  classical
  unfold tupleMass
  rw [← Fintype.prod_sum (fun (_ : Fin k) (d : DivisorIndex P) =>
    coefficient P d.val ^ 2 / (d.val.totient : ℝ))]
  rw [sum_divisorIndex P (fun d => coefficient P d ^ 2 / (d.totient : ℝ)),
    ← coefficientMoment_zero]
  simp

/-- The tilted tuple mass factors as a power of the coefficient moment. -/
lemma sum_tupleMass_mul_rpow (P k : ℕ) (γ : ℝ) :
    (∑ r : DivisorTuple P k, tupleMass r * (tupleProduct r : ℝ) ^ γ) =
      coefficientMoment P γ ^ k := by
  classical
  unfold tupleMass tupleProduct
  simp_rw [Nat.cast_prod,
    ← Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _),
    ← Finset.prod_mul_distrib, div_mul_eq_mul_div]
  rw [← Fintype.prod_sum (fun (_ : Fin k) (d : DivisorIndex P) =>
    coefficient P d.val ^ 2 * (d.val : ℝ) ^ γ / (d.val.totient : ℝ))]
  rw [sum_divisorIndex P (fun d => coefficient P d ^ 2 * (d : ℝ) ^ γ / d.totient)]
  simp [coefficientMoment]

/-- The first inequality in (3.10), with no asymptotic assumptions. -/
theorem diagonal_tail_le (P k : ℕ) {D β : ℝ} (hD : 0 < D) (hβ : 0 ≤ β) :
    (∑ r ∈ (Finset.univ : Finset (DivisorTuple P k)).filter
        (fun r => D < (tupleProduct r : ℝ)), tupleMass r) ≤
      D ^ (-β) * coefficientMoment P β ^ k := by
  classical
  simpa only [sum_tupleMass_mul_rpow] using
    moment_tail_le Finset.univ tupleMass (fun r : DivisorTuple P k => (tupleProduct r : ℝ))
      D β hD hβ (fun r _ => tupleMass_nonneg r) (fun r _ => Nat.cast_nonneg _)

/-- Convert an additive bound into an exponential bound on powers. -/
lemma pow_le_mul_exp {A B t : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B)
    (ht : 0 ≤ t) (hBA : B ≤ A + t) (k : ℕ) :
    B ^ k ≤ A ^ k * Real.exp ((k : ℝ) * t) := by
  have hbase : B ≤ A * Real.exp t := by
    have he := Real.add_one_le_exp t
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) ht,
      mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ A)]
  calc
    B ^ k ≤ (A * Real.exp t) ^ k := pow_le_pow_left₀ hB hbase k
    _ = A ^ k * Real.exp ((k : ℝ) * t) := by rw [mul_pow, Real.exp_nat_mul]

/-- Bound powers of a tilted coefficient moment relative to the zero moment. -/
lemma coefficientMoment_pow_le {P : ℕ} (hP : 1 < P) {C γ : ℝ}
    (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hM : coefficientAbsMoment P γ ≤ C * normalizer P) (k : ℕ) :
    coefficientMoment P γ ^ k ≤
      coefficientMoment P 0 ^ k * Real.exp ((k : ℝ) * C * γ) := by
  have hP0 : P ≠ 0 := by omega
  have hB := normalizer_pos hP
  have hbound : coefficientMoment P γ - coefficientMoment P 0 ≤ C * γ := by
    calc
      _ ≤ γ / normalizer P * coefficientAbsMoment P γ := coefficientMoment_sub_le hP γ
      _ ≤ γ / normalizer P * (C * normalizer P) :=
        mul_le_mul_of_nonneg_left hM (div_nonneg hγ hB.le)
      _ = C * γ := by field_simp
  simpa [mul_assoc] using pow_le_mul_exp (coefficientMoment_ge_one hP0 0)
    (zero_le_one.trans (coefficientMoment_ge_one hP0 γ)) (mul_nonneg hC hγ)
    (by linarith : coefficientMoment P γ ≤ coefficientMoment P 0 + C * γ) k

/-- The elementary passage from a prime-free interval to consecutive primes.
Bertrand's postulate supplies the upper endpoint bound used in Section 2. -/
theorem consecutivePrimes_of_composite_interval {N H : ℕ} (hN : 2 ≤ N)
    (hcomposite : ∀ n : ℕ, N < n → n ≤ N + H → ¬n.Prime) :
    ∃ p q : ℕ, ConsecutivePrimes p q ∧ p ≤ N ∧ N + H < q ∧ q ≤ 2 * N ∧ H < q - p := by
  have hex := Nat.exists_prime_lt_and_le_two_mul N (by omega)
  let q := Nat.find hex
  obtain ⟨hq, hNq, hqN⟩ : q.Prime ∧ N < q ∧ q ≤ 2 * N := Nat.find_spec hex
  let p := Nat.findGreatest Nat.Prime N
  have hp : p.Prime := Nat.findGreatest_spec hN Nat.prime_two
  have hpN : p ≤ N := Nat.findGreatest_le N
  have hNHq : N + H < q := by
    by_contra! h
    exact hcomposite q hNq h hq
  refine ⟨p, q, ⟨hp, hq, hpN.trans_lt hNq, ?_⟩, hpN, hNHq, hqN, by omega⟩
  intro r hpr hrq hr
  by_cases hrN : r ≤ N
  · exact Nat.findGreatest_is_greatest hpr hrN hr
  · exact Nat.find_min hex hrq ⟨hr, by omega, by omega⟩

/-- The initial zero-residue sieve leaves only primes and z-smooth integers. -/
theorem prime_or_smooth_of_survives {n H : ℕ} {x w z : ℝ}
    (hn : 1 ≤ n) (hnH : n ≤ H) (hx : 0 < x) (hsmall : 2 * (H : ℝ) < x * w)
    (hsurvives : ∀ p : ℕ, p.Prime → ((p : ℝ) ≤ w ∨ (z < p ∧ (p : ℝ) ≤ x / 2)) → ¬p ∣ n) :
    n.Prime ∨ ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ z := by
  by_cases hprime : n.Prime
  · exact Or.inl hprime
  right
  intro p hp hpn
  by_contra! hpz
  have hpbig : x / 2 < (p : ℝ) := by
    by_contra! hpx
    exact hsurvives p hp (Or.inr ⟨hpz, hpx⟩) hpn
  obtain ⟨k, rfl⟩ := hpn
  have hk1 : k ≠ 1 := by
    intro hk
    simp [hk, hp] at hprime
  obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd hk1
  have hqn : q ∣ p * k := dvd_mul_of_dvd_right hqk p
  have hqbig : w < (q : ℝ) := by
    by_contra! hqw
    exact hsurvives q hq (Or.inl hqw) hqn
  have hkn : q ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero (by rintro rfl; simp at hn)) hqk
  have hpkH : (p : ℝ) * k ≤ H := by exact_mod_cast hnH
  have hqk' : (q : ℝ) ≤ k := by exact_mod_cast hkn
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  nlinarith [mul_le_mul_of_nonneg_left hqk' hp0,
    mul_lt_mul_of_pos_right hpbig hq0,
    mul_lt_mul_of_pos_left hqbig hx]

/-- Elements of `S` avoiding the selected residue classes. -/
def survivors (S ps : Finset ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  S.filter fun n => ∀ p ∈ ps, n % p ≠ a p

/-- The greedy product bound in (2.1), before applying Mertens' estimate. -/
theorem greedy_residue_classes (S ps : Finset ℕ) (hpos : ∀ p ∈ ps, 0 < p) :
    ∃ a : ℕ → ℕ, (∀ p ∈ ps, a p < p) ∧
      ((survivors S ps a).card : ℝ) ≤ (S.card : ℝ) * ∏ p ∈ ps, (1 - 1 / (p : ℝ)) := by
  classical
  induction ps using Finset.induction_on with
  | empty =>
      exact ⟨fun _ => 0, by simp, by simp [survivors]⟩
  | @insert p ps hp ih =>
      have hp0 : 0 < p := hpos p (Finset.mem_insert_self p ps)
      have hpR : 0 < (p : ℝ) := by exact_mod_cast hp0
      obtain ⟨a, ha, hcard⟩ := ih (fun q hq => hpos q (Finset.mem_insert_of_mem hq))
      let T := survivors S ps a
      have hsum : (∑ r ∈ Finset.range p,
          ((T.filter fun n => n % p = r).card : ℝ)) = T.card := by
        exact_mod_cast (Finset.card_eq_sum_card_fiberwise
          (f := fun n => n % p) (s := T) (t := Finset.range p)
          (by intro n _; exact Finset.mem_range.mpr (Nat.mod_lt n hp0))).symm
      obtain ⟨r, hr, hlarge⟩ : ∃ r ∈ Finset.range p,
          (T.card : ℝ) / p ≤ ((T.filter fun n => n % p = r).card : ℝ) := by
        apply Finset.exists_le_of_sum_le (Finset.nonempty_range_iff.mpr hp0.ne')
        rw [hsum]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact le_of_eq (by field_simp)
      have hsplit : ((T.filter fun n => n % p = r).card : ℝ) +
          ((T.filter fun n => n % p ≠ r).card : ℝ) = T.card := by
        exact_mod_cast T.card_filter_add_card_filter_not (fun n => n % p = r)
      have hstep : ((T.filter fun n => n % p ≠ r).card : ℝ) ≤
          (T.card : ℝ) * (1 - 1 / (p : ℝ)) := by
        rw [div_eq_mul_inv] at hlarge
        simp only [one_div]
        nlinarith
      refine ⟨Function.update a p r, ?_, ?_⟩
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · simpa using Finset.mem_range.mp hr
        · simpa [Function.update_of_ne (ne_of_mem_of_not_mem hq hp)] using ha q hq
      · have hsurvivors : survivors S (insert p ps) (Function.update a p r) =
            T.filter (fun n => n % p ≠ r) := by
          have hupdate : ∀ q ∈ ps, Function.update a p r q = a q := by
            intro q hq
            exact Function.update_of_ne (ne_of_mem_of_not_mem hq hp) r a
          ext n
          simp (config := { contextual := true }) only [survivors, Finset.mem_filter,
            Finset.mem_insert, forall_eq_or_imp, Function.update_self, T, hupdate]
          tauto
        rw [hsurvivors, Finset.prod_insert hp]
        calc
          _ ≤ (T.card : ℝ) * (1 - 1 / (p : ℝ)) := hstep
          _ ≤ ((S.card : ℝ) * ∏ q ∈ ps, (1 - 1 / (q : ℝ))) *
              (1 - 1 / (p : ℝ)) :=
            mul_le_mul_of_nonneg_right hcard (by
              have : (1 : ℝ) ≤ p := by exact_mod_cast hp0
              exact sub_nonneg.mpr ((div_le_one hpR).mpr this))
          _ = _ := by ring

/-- A symmetric matrix is controlled by its absolute row sums. This is the
2|ab| ≤ a²+b² argument invoked in the proof of (3.9). -/
theorem abs_quadratic_form_le_rows {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (K : ι → ι → ℝ) (hK : ∀ i j, |K i j| = |K j i|) :
    |∑ i, ∑ j, c i * c j * K i j| ≤ ∑ i, c i ^ 2 * ∑ j, |K i j| := by
  calc
    |∑ i, ∑ j, c i * c j * K i j| ≤ ∑ i, ∑ j, |c i * c j * K i j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, (c i ^ 2 + c j ^ 2) / 2 * |K i j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      nlinarith [sq_nonneg (|c i| - |c j|), sq_abs (c i), sq_abs (c j)]
    _ = ∑ i, c i ^ 2 * ∑ j, |K i j| := by
      simp_rw [add_div, add_mul, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => c j ^ 2 / 2 * |K i j|)]
      simp_rw [← hK, ← Finset.mul_sum, ← Finset.sum_add_distrib, ← add_mul, add_halves]

/-- Row sums away from the diagonal bound the quadratic error from the identity. -/
lemma quadratic_form_near_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) (K : ι → ι → ℝ) (ε : ℝ)
    (hsym : ∀ i j, K i j = K j i) (hdiag : ∀ i, K i i = 1)
    (hrow : ∀ i, (∑ j, if j = i then 0 else |K i j|) ≤ ε) :
    |(∑ i, ∑ j, c i * c j * K i j) - ∑ i, c i ^ 2| ≤ ε * ∑ i, c i ^ 2 := by
  let L : ι → ι → ℝ := fun i j => if j = i then 0 else K i j
  have hL (i j : ι) : c i * c j * L i j =
      c i * c j * K i j - if j = i then c i ^ 2 else 0 := by
    by_cases hij : j = i <;> simp [L, hij, hdiag, pow_two]
  calc
    _ = |∑ i, ∑ j, c i * c j * L i j| := by
      simp_rw [hL, Finset.sum_sub_distrib]
      simp
    _ ≤ ∑ i, c i ^ 2 * ∑ j, |L i j| :=
      abs_quadratic_form_le_rows c L (by
        intro i j
        simp only [L, eq_comm, hsym i j])
    _ ≤ ∑ i, c i ^ 2 * ε := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      simpa only [L, apply_ite abs, abs_zero] using hrow i
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- The product of selected local basis functions over all coordinates. -/
def productBasis {α : Type*} [Fintype α] {Ω J : α → Type*}
    (f : (p : α) → J p → Ω p → ℝ) (σ : (p : α) → J p) (t : (p : α) → Ω p) : ℝ :=
  ∏ p, f p (σ p) (t p)

/-- The residue factor has mean zero. -/
lemma average_residueFactor {p : ℕ} (hp : 1 < p) (a : Fin p) :
    Finset.expect Finset.univ (residueFactor a) = 0 := by
  simp [Finset.expect, sum_residueFactor hp]

/-- The residue factor has second moment `1 / (p - 1)`. -/
lemma average_residueFactor_sq {p : ℕ} (hp : 1 < p) (a : Fin p) :
    Finset.expect Finset.univ (fun t => residueFactor a t ^ 2) = 1 / ((p : ℝ) - 1) := by
  have hp0 : p ≠ 0 := by omega
  simp [Finset.expect_eq_sum_div_card, sum_residueFactor_sq hp, div_eq_mul_inv,
    mul_right_comm, hp0]

/-- Distinct residue factors have covariance `-1 / (p - 1)^2`. -/
lemma average_residueFactor_mul {p : ℕ} (hp : 1 < p) (a b : Fin p) (hab : a ≠ b) :
    Finset.expect Finset.univ (fun t => residueFactor a t * residueFactor b t) =
      -1 / ((p : ℝ) - 1) ^ 2 := by
  have hp0 : p ≠ 0 := by omega
  simp [Finset.expect_eq_sum_div_card, sum_residueFactor_mul hp a b hab,
    div_eq_mul_inv, mul_right_comm, hp0]

/-- The constant function and residue factors scaled to have variance one. -/
def localBasis {p k : ℕ} (root : Fin k → Fin p) (i : Option (Fin k)) (t : Fin p) : ℝ :=
  match i with
  | none => 1
  | some j => Real.sqrt ((p : ℝ) - 1) * residueFactor (root j) t

/-- The Gram kernel for the normalized local basis. -/
def localKernel (p : ℕ) {k : ℕ} (i j : Option (Fin k)) : ℝ :=
  match i, j with
  | none, none => 1
  | none, some _ => 0
  | some _, none => 0
  | some a, some b => if a = b then 1 else -1 / ((p : ℝ) - 1)

/-- The local Gram matrix, with the nonconstant factors normalized to variance one. -/
theorem average_localBasis_mul {p k : ℕ} (hp : 1 < p) (root : Fin k → Fin p)
    (hroot : Function.Injective root) (i j : Option (Fin k)) :
    Finset.expect Finset.univ (fun t => localBasis root i t * localBasis root j t) =
      localKernel p i j := by
  classical
  have hpR : 0 < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hp)
  have : NeZero p := ⟨by omega⟩
  cases i with
  | none =>
      cases j <;>
        simp [localBasis, localKernel, ← Finset.mul_expect, average_residueFactor hp,
          Finset.expect_const Finset.univ_nonempty]
  | some a =>
      cases j with
      | none =>
          simp [localBasis, localKernel, ← Finset.mul_expect, average_residueFactor hp]
      | some b =>
          simp_rw [localBasis, mul_mul_mul_comm (Real.sqrt _) _ (Real.sqrt _) _]
          rw [← Finset.mul_expect, ← pow_two, Real.sq_sqrt hpR.le]
          by_cases hab : a = b
          · subst b
            simp only [localKernel, ← pow_two, average_residueFactor_sq hp]
            exact mul_one_div_cancel (ne_of_gt hpR)
          · rw [average_residueFactor_mul hp _ _ (hroot.ne hab)]
            simp only [localKernel, if_neg hab]
            field_simp

/-- The absolute row sum of the local Gram kernel. -/
def localRow (p k : ℕ) (i : Option (Fin k)) : ℝ :=
  match i with
  | none => 1
  | some _ => 1 + ((k : ℝ) - 1) / ((p : ℝ) - 1)

/-- The local Gram kernel is symmetric. -/
lemma localKernel_symm (p : ℕ) {k : ℕ} (i j : Option (Fin k)) :
    localKernel p i j = localKernel p j i := by
  cases i <;> cases j <;> simp [localKernel, eq_comm]

/-- The local Gram kernel has diagonal entries equal to one. -/
lemma localKernel_diag (p : ℕ) {k : ℕ} (i : Option (Fin k)) :
    localKernel p i i = 1 := by cases i <;> simp [localKernel]

/-- Summing the absolute local kernel entries gives `localRow`. -/
lemma sum_abs_localKernel {p k : ℕ} (hp : 1 < p) (i : Option (Fin k)) :
    (∑ j, |localKernel p i j|) = localRow p k i := by
  have hpR : 0 ≤ (p : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hp.le)
  cases i with
  | none => simp [localKernel, localRow, Fintype.sum_option]
  | some a =>
      simp only [Fintype.sum_option, localKernel, abs_zero, zero_add, apply_ite abs,
        abs_one, abs_div, abs_neg, abs_of_nonneg hpR]
      simpa [localRow, eq_comm, div_eq_mul_inv] using
        sum_one_exception a 1 (1 / ((p : ℝ) - 1))

/-- The product of local Gram kernels over all coordinates. -/
def productKernel {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ τ : α → Option (Fin k)) : ℝ := ∏ p, localKernel (size p) (σ p) (τ p)

/-- The product Gram kernel is symmetric. -/
lemma productKernel_symm {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ τ : α → Option (Fin k)) : productKernel size σ τ = productKernel size τ σ := by
  exact Finset.prod_congr rfl fun p _ => localKernel_symm (size p) (σ p) (τ p)

/-- The product Gram kernel has diagonal entries equal to one. -/
lemma productKernel_diag {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ : α → Option (Fin k)) : productKernel size σ σ = 1 := by
  simp [productKernel, localKernel_diag]

/-- The product of local row sums from the proof of (3.9). -/
theorem sum_abs_productKernel {α : Type*} [Fintype α] [DecidableEq α]
    (size : α → ℕ) (hsize : ∀ p, 1 < size p) {k : ℕ} (σ : α → Option (Fin k)) :
    (∑ τ, |productKernel size σ τ|) = ∏ p, localRow (size p) k (σ p) := by
  simp only [productKernel, Finset.abs_prod]
  rw [← Fintype.prod_sum (fun p (j : Option (Fin k)) =>
    |localKernel (size p) (σ p) j|)]
  simp_rw [sum_abs_localKernel (hsize _)]

/-- Products of local basis functions have Gram kernel `productKernel`. -/
lemma average_productBasis_localBasis {α : Type*} [Fintype α] [DecidableEq α]
    (size : α → ℕ) (hsize : ∀ p, 1 < size p) {k : ℕ}
    (root : (p : α) → Fin k → Fin (size p)) (hroot : ∀ p, Function.Injective (root p))
    (σ τ : α → Option (Fin k)) :
    Finset.expect Finset.univ (fun t => productBasis (fun p => localBasis (root p)) σ t *
      productBasis (fun p => localBasis (root p)) τ t) = productKernel size σ τ := by
  classical
  simp only [productBasis, ← Finset.prod_mul_distrib]
  rw [Finset.expect_eq_sum_div_card, Finset.card_univ, Fintype.card_pi,
    Nat.cast_prod, ← Fintype.prod_sum (fun p t =>
      localBasis (root p) (σ p) t * localBasis (root p) (τ p) t),
    ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun p _ =>
    (Finset.expect_eq_sum_div_card _ _).symm.trans
      (average_localBasis_mul (hsize p) (root p) (hroot p) (σ p) (τ p))

/-- Coordinates assigned to a nonconstant local basis function. -/
def assignmentSupport {α : Type*} [Fintype α] {k : ℕ}
    (σ : α → Option (Fin k)) : Finset α := Finset.univ.filter fun p => (σ p).isSome

/-- The product of coordinate sizes on an assignment's support. -/
def assignmentProduct {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ : α → Option (Fin k)) : ℕ := ∏ p ∈ assignmentSupport σ, size p

/-- The cutoff controls the row sums uniformly, independently of the
number of auxiliary primes in P. -/
theorem assignment_row_bound {α : Type*} [Fintype α]
    (size : α → ℕ) {k : ℕ} (hk : 1 ≤ k) (σ : α → Option (Fin k))
    {z D : ℝ} (hz : 1 < z) (hsize : ∀ p, z ≤ (size p : ℝ))
    (hcut : (assignmentProduct size σ : ℝ) ≤ D) :
    (∏ p, localRow (size p) k (σ p)) ≤
      Real.exp ((k : ℝ) * Real.log D / ((z - 1) * Real.log z)) := by
  classical
  have hz0 : 0 < z := zero_lt_one.trans hz
  have hz1 : 0 < z - 1 := sub_pos.mpr hz
  have hk1 : 0 ≤ (k : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hk)
  have hpos (p : α) : 0 < (size p : ℝ) := hz0.trans_le (hsize p)
  have hlog : ((assignmentSupport σ).card : ℝ) * Real.log z ≤ Real.log D := by
    calc
      _ = ∑ p ∈ assignmentSupport σ, Real.log z := by simp
      _ ≤ ∑ p ∈ assignmentSupport σ, Real.log (size p) :=
        Finset.sum_le_sum fun p _ => Real.log_le_log hz0 (hsize p)
      _ = Real.log (assignmentProduct size σ) := by
        rw [assignmentProduct, Nat.cast_prod, Real.log_prod (fun p _ => (hpos p).ne')]
      _ ≤ Real.log D := Real.log_le_log (by
        rw [assignmentProduct, Nat.cast_prod]
        exact Finset.prod_pos fun p _ => hpos p) hcut
  calc
    (∏ p, localRow (size p) k (σ p)) =
        ∏ p ∈ assignmentSupport σ, (1 + ((k : ℝ) - 1) / ((size p : ℝ) - 1)) := by
      simp only [assignmentSupport, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro p _
      cases σ p <;> simp [localRow]
    _ ≤ ∏ _ ∈ assignmentSupport σ, Real.exp ((k : ℝ) / (z - 1)) := by
      apply Finset.prod_le_prod
      · intro p _
        exact add_nonneg zero_le_one
          (div_nonneg hk1 (hz1.le.trans (sub_le_sub_right (hsize p) 1)))
      · intro p _
        calc
          _ ≤ 1 + (k : ℝ) / (z - 1) := add_le_add (le_refl 1)
            (div_le_div₀ (Nat.cast_nonneg k) (sub_le_self _ zero_le_one) hz1
              (sub_le_sub_right (hsize p) 1))
          _ ≤ Real.exp ((k : ℝ) / (z - 1)) := by
            simpa [add_comm] using Real.add_one_le_exp ((k : ℝ) / (z - 1))
    _ = Real.exp (((assignmentSupport σ).card : ℝ) * ((k : ℝ) / (z - 1))) := by
      simp [Real.exp_nat_mul]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hcount := (le_div_iff₀ (Real.log_pos hz)).mpr hlog
      have hbound := mul_le_mul_of_nonneg_right hcount
        (div_nonneg (Nat.cast_nonneg k) hz1.le)
      calc
        _ ≤ Real.log D / Real.log z * ((k : ℝ) / (z - 1)) := hbound
        _ = _ := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring

/-- The indicator of the residue class `a` modulo `m`. -/
def residueIndicator (m a n : ℕ) : ℝ := if n % m = a then 1 else 0

/-- The error of counting one congruence class is at most one. -/
theorem residue_count_error_le_one {m a : ℕ} (ha : a < m) (T : ℕ) :
    |(∑ n ∈ Finset.range T, residueIndicator m a n) - (T : ℝ) / m| ≤ 1 := by
  have hlo : ((T / m : ℕ) : ℝ) ≤ (T : ℝ) / m := Nat.cast_div_le
  have hhi : (T : ℝ) / m < ((T / m : ℕ) : ℝ) + 1 := by
    simpa only [Nat.floor_div_natCast, Nat.floor_natCast] using Nat.lt_floor_add_one ((T : ℝ) / m)
  have hcount := congrArg (fun n : ℕ => (n : ℝ))
    (Nat.count_modEq_card T (by omega : 0 < m) a)
  simp only [Nat.count_eq_card_filter_range, Nat.ModEq, Nat.mod_eq_of_lt ha,
    Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hcount
  simp only [residueIndicator, Finset.sum_boole]
  rw [hcount]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- A residue class has frequency error at most `1 / T` on an interval of length `T`. -/
lemma residue_average_error {m a T : ℕ} (ha : a < m) (hT : 0 < T) :
    |(∑ n ∈ Finset.range T, residueIndicator m a n) / (T : ℝ) - 1 / (m : ℝ)| ≤
      1 / (T : ℝ) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have he : (∑ n ∈ Finset.range T, residueIndicator m a n) / (T : ℝ) - 1 / (m : ℝ) =
      ((∑ n ∈ Finset.range T, residueIndicator m a n) - (T : ℝ) / m) / T := by
    field_simp [ne_of_gt hTr]
  rw [he, abs_div, abs_of_pos hTr]
  exact div_le_div_of_nonneg_right (residue_count_error_le_one ha T) hTr.le

/-- A weighted union bound, stated without a probability-space interface. -/
theorem weighted_union_bound {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (w : Ω → ℝ) (event : ι → Ω → Prop) [∀ i, DecidablePred (event i)]
    (hw : ∀ t, 0 ≤ w t) :
    (∑ t, w t * if ∃ i, event i t then 1 else 0) ≤
      ∑ i, ∑ t, w t * if event i t then 1 else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro t _
  by_cases h : ∃ i, event i t
  · obtain ⟨i, hi⟩ := h
    simpa [show ∃ j, event j t from ⟨i, hi⟩, hi] using
      (Finset.single_le_sum (s := Finset.univ)
        (f := fun j => w t * if event j t then 1 else 0)
        (fun j _ => by split_ifs <;> simp [hw]) (Finset.mem_univ i))
  · simp [not_exists.mp h]

/-- Independence of two marked coordinates under a product of normalized masses. -/
theorem sum_pair_marked_product {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] (w : Ω → ℝ) (hw : ∑ d, w d = 1)
    (mark : Ω → Prop) [DecidablePred mark] (i j : ι) (hij : i ≠ j) :
    (∑ r : ι → Ω, (∏ ℓ, w (r ℓ)) * if mark (r i) ∧ mark (r j) then 1 else 0) =
      (∑ d, w d * if mark d then 1 else 0) ^ 2 := by
  classical
  calc
    _ = ∏ ℓ, ∑ d, w d * if (ℓ = i ∨ ℓ = j) → mark d then 1 else 0 := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.prod_mul_distrib, Finset.prod_boole]
      congr 1
      simp only [Finset.mem_univ, forall_true_left, or_imp, forall_and, forall_eq]
    _ = ∏ ℓ ∈ ({i, j} : Finset ι), ∑ d, w d * if mark d then 1 else 0 := by
      rw [← Finset.prod_subset (Finset.subset_univ ({i, j} : Finset ι))]
      · simp [hij, Finset.prod_pair hij]
      · intro ℓ _ hℓ
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hℓ
        simp [hℓ.1, hℓ.2, hw]
    _ = _ := by simp [Finset.prod_pair hij, pow_two]

/-- The collision estimate for independently chosen divisors: a common mark
in two coordinates costs at most the square of its one-coordinate mass. -/
theorem product_collision_bound {α Ω : Type*} [Fintype α] [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ d, 0 ≤ w d) (hsum : ∑ d, w d = 1)
    (mark : α → Ω → Prop) [∀ p, DecidablePred (mark p)] (k : ℕ) :
    (∑ r : Fin k → Ω, (∏ i, w (r i)) *
      if ∃ p i j, i ≠ j ∧ mark p (r i) ∧ mark p (r j) then 1 else 0) ≤
        (k : ℝ) ^ 2 * ∑ p, (∑ d, w d * if mark p d then 1 else 0) ^ 2 := by
  classical
  have h := weighted_union_bound
    (fun r : Fin k → Ω => ∏ i, w (r i))
    (fun (x : α × Fin k × Fin k) r =>
      x.2.1 ≠ x.2.2 ∧ mark x.1 (r x.2.1) ∧ mark x.1 (r x.2.2))
    (fun r => Finset.prod_nonneg fun i _ => hw (r i))
  calc
    _ ≤ ∑ p, ∑ i : Fin k, ∑ j : Fin k,
        ∑ r : Fin k → Ω, (∏ ℓ, w (r ℓ)) *
          if i ≠ j ∧ mark p (r i) ∧ mark p (r j) then 1 else 0 := by
      simpa only [Prod.exists, Fintype.sum_prod_type] using h
    _ ≤ ∑ p, ∑ _i : Fin k, ∑ _j : Fin k,
        (∑ d, w d * if mark p d then 1 else 0) ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i = j
      · simp [hij, sq_nonneg]
      · simpa only [hij, ne_eq, not_false_eq_true, true_and] using
          (sum_pair_marked_product w hsum (mark p) i j hij).le
    _ = _ := by simp [Finset.mul_sum, pow_two, mul_assoc]

/-- Divisors divisible by p are parametrized by the divisors of P/p. -/
theorem sum_divisors_dvd_eq {P p : ℕ} (hP : P ≠ 0) (hp : 0 < p) (hpP : p ∣ P)
    (f : ℕ → ℝ) :
    (∑ d ∈ P.divisors.filter (fun d => p ∣ d), f d) =
      ∑ e ∈ (P / p).divisors, f (p * e) := by
  symm
  refine Finset.sum_bij (fun e _ => p * e) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro e he
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr
        ⟨(Nat.dvd_div_iff_mul_dvd hpP).mp (Nat.dvd_of_mem_divisors he), hP⟩,
        dvd_mul_right p e⟩
  · intro e₁ _ e₂ _ h
    exact Nat.mul_left_cancel hp h
  · intro d hd
    obtain ⟨hd, hpd⟩ := Finset.mem_filter.mp hd
    refine ⟨d / p, Nat.mem_divisors.mpr ⟨?_, ?_⟩, Nat.mul_div_cancel' hpd⟩
    · exact Nat.div_dvd_div hpd (Nat.dvd_of_mem_divisors hd)
    · intro h
      apply hP
      rw [← Nat.mul_div_cancel' hpP, h, mul_zero]

/-- Multiplying a nontrivial divisor by a prime decreases the absolute coefficient. -/
theorem abs_coefficient_mul_le {P p e : ℕ} (hP : 1 < P) (hp : 1 ≤ p) (he : 1 < e) :
    |coefficient P (p * e)| ≤ |coefficient P e| := by
  have hpe : e ≤ p * e := by simpa using Nat.mul_le_mul_right e hp
  have hpe1 : 1 < p * e := he.trans_le hpe
  rw [abs_of_neg (coefficient_neg hP hpe1), abs_of_neg (coefficient_neg hP he)]
  simp only [coefficient, if_neg (ne_of_gt hpe1), if_neg (ne_of_gt he),
    neg_div, neg_neg]
  apply one_div_le_one_div_of_le
  · exact mul_pos (normalizer_pos hP) (Real.log_pos (by exact_mod_cast he))
  · exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (by exact_mod_cast (zero_lt_one.trans he))
        (by exact_mod_cast hpe)) (normalizer_pos hP).le

/-- The absolute coefficient moment at exponent zero equals one. -/
lemma coefficientAbsMoment_zero {P : ℕ} (hP : 1 < P) : coefficientAbsMoment P 0 = 1 := by
  have h := partial_cancellation hP {1}
    (by simpa using Nat.one_mem_divisors.mpr (by omega : P ≠ 0)) (by simp)
  simpa [coefficientAbsMoment, coefficient, Finset.sdiff_singleton_eq_erase] using h.symm

/-- The sum of absolute coefficients divided by totients equals two. -/
lemma sum_abs_coefficient_div_totient {P : ℕ} (hP : 1 < P) :
    (∑ d ∈ P.divisors, |coefficient P d| / d.totient) = 2 := by
  rw [← Finset.sum_erase_add _ _ (Nat.one_mem_divisors.mpr (by omega : P ≠ 0))]
  have h := coefficientAbsMoment_zero hP
  simp only [coefficientAbsMoment, Real.rpow_zero, mul_one] at h
  rw [h]
  norm_num [coefficient]

/-- The incidence bound (3.7), with an explicit constant once |a(p)| ≤ 1. -/
theorem coefficient_prime_incidence {P p : ℕ} (hP : 1 < P) (hsq : Squarefree P)
    (hp : p.Prime) (hpP : p ∣ P) (hcoeff : |coefficient P p| ≤ 1) :
    (∑ d ∈ P.divisors.filter (fun d => p ∣ d), |coefficient P d| / d.totient) ≤
      4 / (p : ℝ) := by
  have hP0 : P ≠ 0 := by omega
  have hpR : 0 < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hp.one_lt)
  rw [sum_divisors_dvd_eq hP0 hp.pos hpP]
  calc
    _ ≤ ∑ e ∈ (P / p).divisors,
        (|coefficient P e| / e.totient) / ((p : ℝ) - 1) := by
      apply Finset.sum_le_sum
      intro e he
      have hcop : p.Coprime e := by
        apply hp.coprime_iff_not_dvd.mpr
        intro hpe
        have hpeP := (Nat.dvd_div_iff_mul_dvd hpP).mp (Nat.dvd_of_mem_divisors he)
        exact hp.ne_one (Nat.isUnit_iff.mp (hsq p ((mul_dvd_mul_left p hpe).trans hpeP)))
      have hcoeff' : |coefficient P (p * e)| ≤ |coefficient P e| := by
        by_cases he1 : e = 1
        · simpa [he1, coefficient] using hcoeff
        · exact abs_coefficient_mul_le hP hp.one_le
            (by have := Nat.pos_of_mem_divisors he; omega)
      rw [Nat.totient_mul hcop, Nat.totient_prime hp, Nat.cast_mul,
        Nat.cast_sub hp.one_le, Nat.cast_one]
      calc
        _ ≤ |coefficient P e| / (((p : ℝ) - 1) * e.totient) :=
          div_le_div_of_nonneg_right hcoeff' (mul_nonneg hpR.le (Nat.cast_nonneg _))
        _ = _ := by rw [mul_comm, div_mul_eq_div_div]
    _ = (∑ e ∈ (P / p).divisors, |coefficient P e| / e.totient) /
        ((p : ℝ) - 1) := by rw [Finset.sum_div]
    _ ≤ 2 / ((p : ℝ) - 1) := by
      apply div_le_div_of_nonneg_right _ hpR.le
      calc
        _ ≤ ∑ e ∈ P.divisors, |coefficient P e| / e.totient :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Nat.divisors_subset_of_dvd hP0 (Nat.div_dvd_of_dvd hpP))
            (fun _ _ _ => by positivity)
        _ = 2 := sum_abs_coefficient_div_totient hP
    _ ≤ 4 / (p : ℝ) := by
      apply (div_le_div_iff₀ hpR (by exact_mod_cast hp.pos)).mpr
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith

/-- The logarithms of distinct prime divisors sum to at most `log n`. -/
lemma sum_log_prime_divisors_le_log {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (∑ p ∈ N.primesLE, if p ∣ n then Real.log p else 0) ≤ Real.log n := by
  have hfilter : N.primesLE.filter (fun p => p ∣ n) = n.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
    exact ⟨fun h => ⟨h.1.2, h.2, hn.ne'⟩,
      fun h => ⟨⟨(Nat.le_of_dvd hn h.2.1).trans hnN, h.1⟩, h.2.1⟩⟩
  rw [← Finset.sum_filter, hfilter, ← Real.log_prod (fun p hp =>
    Nat.cast_ne_zero.mpr (Nat.mem_primeFactors.mp hp).1.ne_zero)]
  apply Real.log_le_log
  · exact Finset.prod_pos fun p hp =>
      Nat.cast_pos.mpr (Nat.mem_primeFactors.mp hp).1.pos
  · rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

/-- An elementary upper bound for the logarithmically weighted prime harmonic sum. -/
theorem sum_prime_log_div_le {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ N.primesLE, Real.log p / p) ≤ Real.log N + Real.log 4 := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcount (p : ℕ) (_hp : p ∈ N.primesLE) :
      (N : ℝ) / p - 1 ≤ (N / p : ℕ) := by
    simpa only [Nat.floor_div_natCast, Nat.floor_natCast] using
      (Nat.sub_one_lt_floor ((N : ℝ) / p)).le
  have hsum : (∑ p ∈ N.primesLE, ((N / p : ℕ) : ℝ) * Real.log p) ≤
      (N : ℝ) * Real.log N := by
    calc
      _ = ∑ p ∈ N.primesLE, ∑ n ∈ Finset.range N,
          if p ∣ n + 1 then Real.log p else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        rw [← Nat.card_multiples N p, ← Finset.sum_boole]
        simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
      _ = ∑ n ∈ Finset.range N, ∑ p ∈ N.primesLE,
          if p ∣ n + 1 then Real.log p else 0 := Finset.sum_comm
      _ ≤ ∑ n ∈ Finset.range N, Real.log N := by
        apply Finset.sum_le_sum
        intro n hn
        have hnN : n + 1 ≤ N := by simpa using Finset.mem_range.mp hn
        exact (sum_log_prime_divisors_le_log (by omega : 0 < n + 1) hnN).trans
          (Real.log_le_log (by positivity) (by exact_mod_cast hnN))
      _ = (N : ℝ) * Real.log N := by simp
  have hlower : (N : ℝ) * (∑ p ∈ N.primesLE, Real.log p / p) -
      Chebyshev.theta N ≤ (N : ℝ) * Real.log N := by
    apply le_trans _ hsum
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have h := mul_le_mul_of_nonneg_right (hcount p hp)
      (Nat.mem_primesLE.mp hp).2.log_pos.le
    calc
      (N : ℝ) * (Real.log p / p) - Real.log p =
        ((N : ℝ) / p - 1) * Real.log p := by ring
      _ ≤ _ := h
  have htheta := Chebyshev.theta_le_log4_mul_x hNr.le
  apply (mul_le_mul_iff_right₀ hNr).mp
  nlinarith

/-- The finite Euler product over primes at most N. -/
def eulerProduct (N : ℕ) (σ : ℝ) : ℝ :=
  ∏ p ∈ N.primesLE, (1 - (p : ℝ) ^ (-σ))⁻¹

/-- The multiplicative weight `n ↦ n ^ (-σ)`. -/
def natPowerHom (σ : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-σ)
  map_one' := by simp
  map_mul' a b := by
    simp only [Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The weighted sum over smooth numbers is bounded by the finite Euler product. -/
lemma sum_smooth_le_eulerProduct {N : ℕ} {σ : ℝ} (hσ : 0 < σ)
    (S : Finset ℕ) (hS : ∀ n ∈ S, n ∈ (N + 1).smoothNumbers) :
    (∑ n ∈ S, (n : ℝ) ^ (-σ)) ≤ eulerProduct N σ := by
  classical
  have hprime {p : ℕ} (hp : p.Prime) : ‖natPowerHom σ p‖ < 1 := by
    change ‖(p : ℝ) ^ (-σ)‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hσ)
  have hsum :=
    (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := natPowerHom σ) hprime (N + 1)).2
  rw [← Finset.sum_subtype_of_mem _ hS]
  exact sum_le_hasSum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hsum

/-- The lower half of the weak Mertens product estimate. -/
theorem log_le_eulerProduct_one (N : ℕ) : Real.log N ≤ eulerProduct N 1 := by
  have h := sum_smooth_le_eulerProduct (N := N) (by norm_num : (0 : ℝ) < 1)
    (Finset.Icc 1 N) (fun n hn => Nat.mem_smoothNumbers_of_lt
      (by have := Finset.mem_Icc.mp hn; omega)
      (by have := Finset.mem_Icc.mp hn; omega))
  have hlog := log_le_harmonic_floor (N : ℝ) (Nat.cast_nonneg _)
  rw [Nat.floor_natCast, harmonic_eq_sum_Icc] at hlog
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hlog
  simp only [Real.rpow_neg_one] at h
  exact hlog.trans h

/-- The elementary zeta-function bound obtained by integrating t^(-σ). -/
theorem tsum_succ_rpow_le {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hexp : -σ < -1 := neg_lt_neg hσ
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Ici 1) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx) hxy (by linarith)
  have htail := AntitoneOn.tsum_comp_add_le_integral 1 (by simpa using hanti)
    (integrableOn_Ioi_rpow_of_lt hexp (by norm_num))
    (fun x hx => Real.rpow_nonneg (le_of_lt (lt_trans (by norm_num) hx)) _)
  rw [integral_Ioi_rpow_of_lt hexp (by norm_num), Nat.cast_one, Real.one_rpow,
    show -σ + 1 = -(σ - 1) by ring, neg_div_neg_eq] at htail
  have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-σ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hexp)
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_add, Real.one_rpow]
  apply add_le_add le_rfl
  simpa only [Nat.cast_add, Nat.cast_one] using htail

/-- For `σ > 1`, the finite Euler product is at most `1 + 1 / (σ - 1)`. -/
lemma eulerProduct_le_zeta_bound {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    eulerProduct N σ ≤ 1 + 1 / (σ - 1) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have ht := Summable.tsum_subtype_le (fun n : ℕ => (n : ℝ) ^ (-σ))
    ((N + 1).smoothNumbers) (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) hs
  have hseries := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := natPowerHom σ) (fun {p} hp => by
      change ‖(p : ℝ) ^ (-σ)‖ < 1
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt)
        (by linarith)) (N + 1)).2
  change HasSum (fun n : (N + 1).smoothNumbers => (n.val : ℝ) ^ (-σ))
    (eulerProduct N σ) at hseries
  rw [hseries.tsum_eq] at ht
  rw [hs.tsum_eq_zero_add, Nat.cast_zero, Real.zero_rpow (by linarith : -σ ≠ 0), zero_add] at ht
  simp only [Nat.cast_add, Nat.cast_one] at ht
  exact ht.trans (tsum_succ_rpow_le hσ)

/-- Compare an Euler factor at exponent one with its shift by `r`. -/
lemma euler_factor_comparison {p r : ℝ} (hp : 2 ≤ p) (hr : 0 ≤ r) :
    (1 - p ^ (-(1 : ℝ)))⁻¹ ≤
      (1 - p ^ (-(1 + r)))⁻¹ * Real.exp (2 * r * Real.log p / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num) hp
  have hden : 0 < 1 - p ^ (-(1 + r)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith))
  have hpm : 0 < p - 1 := sub_pos.mpr hp1
  have hlog : 0 ≤ r * Real.log p := mul_nonneg hr (Real.log_pos hp1).le
  have hpow : 1 - p ^ (-r) ≤ r * Real.log p := by
    rw [Real.rpow_def_of_pos hp0]
    have h := Real.add_one_le_exp (Real.log p * -r)
    nlinarith
  rw [Real.rpow_neg_one, ← div_eq_inv_mul]
  apply (le_div_iff₀ hden).mpr
  rw [← div_eq_inv_mul]
  calc
    (1 - p ^ (-(1 + r))) / (1 - p⁻¹) =
        1 + (1 - p ^ (-r)) / (p - 1) := by
      rw [neg_add, Real.rpow_add hp0, Real.rpow_neg_one]
      field_simp
      ring
    _ ≤ 1 + (r * Real.log p) / (p - 1) :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hpow hpm.le)
    _ ≤ 1 + 2 * r * Real.log p / p := by
      apply add_le_add le_rfl
      apply (div_le_div_iff₀ hpm hp0).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) hlog]
    _ ≤ Real.exp (2 * r * Real.log p / p) := by
      simpa [add_comm] using Real.add_one_le_exp (2 * r * Real.log p / p)

/-- Moving the Euler product to the right of its pole has bounded cost. -/
theorem eulerProduct_comparison (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    eulerProduct N 1 ≤ eulerProduct N (1 + r) *
      Real.exp (2 * r * ∑ p ∈ N.primesLE, Real.log p / p) := by
  unfold eulerProduct
  calc
    _ ≤ ∏ p ∈ N.primesLE,
        (1 - (p : ℝ) ^ (-(1 + r)))⁻¹ * Real.exp (2 * r * Real.log p / p) := by
      apply Finset.prod_le_prod
      · intro p hp
        apply inv_nonneg.mpr
        apply sub_nonneg.mpr
        exact (Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt)
          (by norm_num : -(1 : ℝ) < 0)).le
      · intro p hp
        exact euler_factor_comparison
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le) hr
    _ = _ := by
      simp_rw [mul_div_assoc]
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]

/-- An explicit weak Mertens upper bound, sufficient throughout the proof. -/
theorem eulerProduct_one_le {N : ℕ} (hN : 2 ≤ N) :
    eulerProduct N 1 ≤ Real.exp 6 * (1 + Real.log N) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog4 : Real.log 4 ≤ 2 * Real.log N := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by norm_num : (0 : ℝ) < 4)
        (show (4 : ℝ) ≤ (N : ℝ) ^ 2 by nlinarith)
  have hsum : (∑ p ∈ N.primesLE, Real.log p / p) ≤ 3 * Real.log N := by
    linarith [sum_prime_log_div_le (by omega : 1 ≤ N)]
  have hcost : 2 * (Real.log N)⁻¹ * (∑ p ∈ N.primesLE, Real.log p / p) ≤ 6 := by
    calc
      _ ≤ 2 * (Real.log N)⁻¹ * (3 * Real.log N) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 6 := by field_simp; norm_num
  have hzeta : eulerProduct N (1 + (Real.log N)⁻¹) ≤ 1 + Real.log N := by
    simpa using eulerProduct_le_zeta_bound
      (lt_add_of_pos_right 1 (inv_pos.mpr hlog)) N
  calc
    _ ≤ eulerProduct N (1 + (Real.log N)⁻¹) *
        Real.exp (2 * (Real.log N)⁻¹ * ∑ p ∈ N.primesLE, Real.log p / p) :=
      eulerProduct_comparison N (inv_nonneg.mpr hlog.le)
    _ ≤ (1 + Real.log N) * Real.exp 6 :=
      mul_le_mul hzeta (Real.exp_le_exp.mpr hcost) (Real.exp_nonneg _) (by positivity)
    _ = _ := mul_comm _ _

/-- The power moment of divisors weighted by reciprocal totients. -/
def divisorEulerMoment (P : ℕ) (γ : ℝ) : ℝ :=
  ∑ d ∈ P.divisors, (d : ℝ) ^ γ / d.totient

/-- Factor the divisor Euler moment of a product of distinct primes. -/
lemma divisorEulerMoment_primeProduct (ps : Finset ℕ) (hps : ∀ p ∈ ps, p.Prime) (γ : ℝ) :
    divisorEulerMoment (∏ p ∈ ps, p) γ =
      ∏ p ∈ ps, (1 + (p : ℝ) ^ γ / ((p : ℝ) - 1)) := by
  let f : ArithmeticFunction ℝ :=
    ⟨fun n => (n : ℝ) ^ γ / n.totient, by simp⟩
  have hf : f.IsMultiplicative := by
    constructor
    · simp [f]
    · intro a b hab
      change ((a * b : ℕ) : ℝ) ^ γ / ((a * b).totient : ℝ) =
        ((a : ℝ) ^ γ / a.totient) * ((b : ℝ) ^ γ / b.totient)
      rw [Nat.totient_mul hab, Nat.cast_mul, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      exact (div_mul_div_comm _ _ _ _).symm
  have hsq : Squarefree (∏ p ∈ ps, p) :=
    Finset.squarefree_prod_of_pairwise_isCoprime
      (fun p hp q hq hpq => Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hps p hp) (hps q hq)).mpr hpq))
      (fun p hp => (hps p hp).squarefree)
  have h := hf.prodPrimeFactors_one_add_of_squarefree hsq
  rw [Nat.primeFactors_prod hps] at h
  calc
    _ = ∏ p ∈ ps, (1 + f p) := h.symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      change 1 + (p : ℝ) ^ γ / p.totient = _
      rw [Nat.totient_prime (hps p hp), Nat.cast_sub (hps p hp).one_le, Nat.cast_one]

/-- The finite Euler product is positive at every positive exponent. -/
lemma eulerProduct_pos (N : ℕ) {σ : ℝ} (hσ : 0 < σ) : 0 < eulerProduct N σ := by
  apply Finset.prod_pos
  intro p hp
  exact inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt) (by linarith)))

/-- The finite Euler product decreases as its positive exponent increases. -/
lemma eulerProduct_antitone (N : ℕ) {σ τ : ℝ} (hσ : 0 < σ) (hστ : σ ≤ τ) :
    eulerProduct N τ ≤ eulerProduct N σ := by
  apply Finset.prod_le_prod
  · intro p hp
    exact inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt) (by linarith)).le)
  · intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt
    have hden : 0 < 1 - (p : ℝ) ^ (-σ) :=
      sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith))
    rw [← one_div, ← one_div]
    apply one_div_le_one_div_of_le hden
    have h := Real.rpow_le_rpow_of_exponent_le hp1.le (show -τ ≤ -σ by linarith)
    linarith

/-- Primes in the interval `(Z, Y]`. -/
def auxiliaryPrimes (Z Y : ℕ) : Finset ℕ := Y.primesLE \ Z.primesLE

/-- The product of primes in the interval `(Z, Y]`. -/
def auxiliaryProduct (Z Y : ℕ) : ℕ := ∏ p ∈ auxiliaryPrimes Z Y, p

/-- Every auxiliary prime is prime. -/
lemma auxiliaryPrimes_prime {Z Y p : ℕ} (hp : p ∈ auxiliaryPrimes Z Y) : p.Prime :=
  (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2

/-- Membership in the auxiliary primes means primality and `Z < p ≤ Y`. -/
lemma mem_auxiliaryPrimes {Z Y p : ℕ} :
    p ∈ auxiliaryPrimes Z Y ↔ p.Prime ∧ Z < p ∧ p ≤ Y := by
  simp only [auxiliaryPrimes, Finset.mem_sdiff, Nat.mem_primesLE, not_and_or, not_le]
  tauto

/-- The auxiliary prime product is squarefree. -/
lemma auxiliaryProduct_squarefree (Z Y : ℕ) : Squarefree (auxiliaryProduct Z Y) := by
  exact Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (auxiliaryPrimes_prime hp) (auxiliaryPrimes_prime hq)).mpr hpq))
    (fun p hp => (auxiliaryPrimes_prime hp).squarefree)

/-- The auxiliary prime product is positive. -/
lemma auxiliaryProduct_pos (Z Y : ℕ) : 0 < auxiliaryProduct Z Y :=
  Finset.prod_pos (fun _ hp => (auxiliaryPrimes_prime hp).pos)

/-- Split the Euler product at the lower cutoff `Z`. -/
lemma auxiliary_euler_factorization {Z Y : ℕ} (hZY : Z ≤ Y) (σ : ℝ) :
    (∏ p ∈ auxiliaryPrimes Z Y, (1 - (p : ℝ) ^ (-σ))⁻¹) * eulerProduct Z σ =
      eulerProduct Y σ := Finset.prod_sdiff (Nat.primesLE_mono hZY)

/-- A squarefree Euler factor dominates the corresponding shifted geometric factor. -/
lemma squarefree_euler_factor_ge {p t : ℝ} (hp : 1 < p) (ht : 0 < t) :
    (1 - p ^ (-(1 + t)))⁻¹ ≤ 1 + p ^ (-t) / (p - 1) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpow : p ^ (-t) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos ht)
  have hden : 0 < 1 - p ^ (-(1 + t)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith))
  rw [← one_div, div_le_iff₀ hden, neg_add, Real.rpow_add hp0, Real.rpow_neg_one]
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  field_simp
  nlinarith [mul_nonneg (Real.rpow_nonneg hp0.le (-t)) (sub_nonneg.mpr hpow.le)]

/-- A lower bound for the squarefree-divisor Euler product by a usual Euler product. -/
theorem divisorEulerMoment_ge_eulerProduct {Z Y : ℕ} (hZY : Z ≤ Y) {t : ℝ} (ht : 0 < t) :
    eulerProduct Y (1 + t) ≤
      divisorEulerMoment (auxiliaryProduct Z Y) (-t) * eulerProduct Z (1 + t) := by
  classical
  rw [← auxiliary_euler_factorization hZY (1 + t)]
  apply mul_le_mul_of_nonneg_right _ (eulerProduct_pos Z (by linarith)).le
  rw [auxiliaryProduct, divisorEulerMoment_primeProduct _
    (fun _ hp => auxiliaryPrimes_prime hp)]
  apply Finset.prod_le_prod
  · intro p hp
    exact (inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast (auxiliaryPrimes_prime hp).one_lt) (by linarith)))).le
  · intro p hp
    exact squarefree_euler_factor_ge
      (by exact_mod_cast (auxiliaryPrimes_prime hp).one_lt) ht

/-- Bound the Euler product below by an integral of a negative power. -/
lemma eulerProduct_ge_power_integral (Y : ℕ) {t : ℝ} (ht : 0 < t) :
    (1 - ((Y : ℝ) + 1) ^ (-t)) / t ≤ eulerProduct Y (1 + t) := by
  calc
    _ = ∫ x : ℝ in 1..(Y : ℝ) + 1, x ^ (-(1 + t)) := by
      rw [integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
      · rw [show -(1 + t) + 1 = -t by ring, Real.one_rpow]
        ring
      · rw [Set.uIcc_of_le (le_add_of_nonneg_left (Nat.cast_nonneg Y))]
        norm_num
    _ ≤ ∑ n ∈ Finset.Ico 1 (Y + 1), (n : ℝ) ^ (-(1 + t)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        AntitoneOn.integral_le_sum_Ico (a := 1) (b := Y + 1)
          (f := fun x : ℝ => x ^ (-(1 + t))) (by omega) (by
            intro x hx y _ hxy
            exact Real.rpow_le_rpow_of_nonpos
              (lt_of_lt_of_le (by norm_num) hx.1) hxy (by linarith))
    _ ≤ _ := sum_smooth_le_eulerProduct (by linarith)
      (Finset.Ico 1 (Y + 1)) (fun n hn => Nat.mem_smoothNumbers_of_lt
        (by have := Finset.mem_Ico.mp hn; omega) (Finset.mem_Ico.mp hn).2)

/-- The Euler product at `1 + t` is at least `1 / (2 * t)` when `t * log (Y + 1) ≥ 1`. -/
lemma eulerProduct_ge_one_div_two_mul (Y : ℕ) {t : ℝ} (ht : 0 < t)
    (hscale : 1 ≤ t * Real.log ((Y : ℝ) + 1)) :
    1 / (2 * t) ≤ eulerProduct Y (1 + t) := by
  have hpow : ((Y : ℝ) + 1) ^ (-t) ≤ 1 / 2 := by
    rw [Real.rpow_def_of_pos (by positivity),
      show Real.log ((Y : ℝ) + 1) * -t = -(t * Real.log ((Y : ℝ) + 1)) by ring,
      Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num)
      (by linarith [Real.add_one_le_exp (t * Real.log ((Y : ℝ) + 1))])
  calc
    1 / (2 * t) = (1 / 2) / t := by ring
    _ ≤ (1 - ((Y : ℝ) + 1) ^ (-t)) / t :=
      div_le_div_of_nonneg_right (by linarith) ht.le
    _ ≤ eulerProduct Y (1 + t) := eulerProduct_ge_power_integral Y ht

/-- The divisor Euler moment is nonnegative. -/
lemma divisorEulerMoment_nonneg (P : ℕ) (γ : ℝ) : 0 ≤ divisorEulerMoment P γ :=
  Finset.sum_nonneg (fun _d _ => div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Nat.cast_nonneg _))

/-- The lower bound whose integral supplies a positive normalization B. -/
theorem divisorEulerMoment_lower {Z Y : ℕ} (hZY : Z ≤ Y) {t A : ℝ}
    (ht : 0 < t) (hA : 0 < A) (hZA : eulerProduct Z 1 ≤ A)
    (hscale : 1 ≤ t * Real.log ((Y : ℝ) + 1)) :
    1 / (2 * t * A) ≤ divisorEulerMoment (auxiliaryProduct Z Y) (-t) := by
  have hZ := (eulerProduct_antitone Z (by norm_num : (0 : ℝ) < 1)
    (by linarith : 1 ≤ 1 + t)).trans hZA
  have h := (eulerProduct_ge_one_div_two_mul Y ht hscale).trans
    ((divisorEulerMoment_ge_eulerProduct hZY ht).trans
      (mul_le_mul_of_nonneg_left hZ (divisorEulerMoment_nonneg _ _)))
  calc
    1 / (2 * t * A) = (1 / (2 * t)) / A := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ divisorEulerMoment (auxiliaryProduct Z Y) (-t) := (div_le_iff₀ hA).mpr h

/-- The negatively tilted divisor Euler moment is continuous. -/
lemma continuous_divisorEulerMoment (P : ℕ) :
    Continuous (fun t : ℝ => divisorEulerMoment P (-t)) := by
  unfold divisorEulerMoment
  apply continuous_finsetSum
  intro d hd
  have hdpos : 0 < (d : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_mem_divisors hd)
  simp only [Real.rpow_def_of_pos hdpos]
  fun_prop

/-- An exponential decay integral starting at a nonnegative point is at most `1 / L`. -/
lemma integral_exp_decay_le {L a : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (b : ℝ) :
    (∫ t : ℝ in a..b, Real.exp (-L * t)) ≤ 1 / L := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hL.ne'),
    integral_exp, smul_eq_mul, inv_neg, neg_mul, ← mul_neg, neg_sub, ← div_eq_inv_mul]
  exact div_le_div_of_nonneg_right
    ((sub_le_self _ (Real.exp_nonneg _)).trans
      (Real.exp_le_one_iff.mpr (by nlinarith))) hL.le

/-- The normalizer dominates every positive-half-line integral of U_(-t)-1. -/
theorem normalizer_integral_le {P : ℕ} (hP : P ≠ 0) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    (∫ t : ℝ in a..b, divisorEulerMoment P (-t) - 1) ≤ normalizer P := by
  have hsum (t : ℝ) : divisorEulerMoment P (-t) - 1 =
      ∑ d ∈ P.divisors.erase 1, (d : ℝ) ^ (-t) / d.totient := by
    rw [divisorEulerMoment,
      ← Finset.sum_erase_add _ _ (Nat.one_mem_divisors.mpr hP)]
    simp
  simp_rw [hsum]
  rw [intervalIntegral.integral_finsetSum]
  · unfold normalizer
    apply Finset.sum_le_sum
    intro d hd
    have hd1 : (1 : ℝ) < d := by
      exact_mod_cast one_lt_of_mem_divisors_erase_one hd
    have hlog : 0 < Real.log d := Real.log_pos hd1
    simp_rw [Real.rpow_def_of_pos (zero_lt_one.trans hd1), mul_neg,
      ← neg_mul]
    rw [intervalIntegral.integral_div]
    calc
      (∫ t : ℝ in a..b, Real.exp (-Real.log d * t)) / (d.totient : ℝ) ≤
          (1 / Real.log d) / (d.totient : ℝ) :=
        div_le_div_of_nonneg_right (integral_exp_decay_le hlog ha b) (Nat.cast_nonneg _)
      _ = 1 / ((d.totient : ℝ) * Real.log d) := by ring
  · intro d hd
    have hdpos : 0 < (d : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_mem_divisors (Finset.mem_of_mem_erase hd))
    apply Continuous.intervalIntegrable
    simp_rw [Real.rpow_def_of_pos hdpos]
    fun_prop

/-- Integrating the lower Euler-product bound gives a completely finite
lower bound for B; no sieve asymptotic is assumed. -/
theorem normalizer_lower_integral {Z Y : ℕ} (hZY : Z ≤ Y) {A a b : ℝ}
    (hA : 0 < A) (ha : 0 < a) (hab : a ≤ b) (hZA : eulerProduct Z 1 ≤ A)
    (hscale : 1 ≤ a * Real.log ((Y : ℝ) + 1)) :
    (Real.log b - Real.log a) / (2 * A) - (b - a) ≤ normalizer (auxiliaryProduct Z Y) := by
  have hpos : ∀ t ∈ Set.uIcc a b, 0 < t := by
    rw [Set.uIcc_of_le hab]
    exact fun t ht => ha.trans_le ht.1
  have hinv : IntervalIntegrable (fun t : ℝ => 1 / t) MeasureTheory.volume a b :=
    (continuousOn_const.div continuousOn_id (fun t ht => (hpos t ht).ne')).intervalIntegrable
  calc
    _ = ∫ t : ℝ in a..b, (1 / t) / (2 * A) - 1 := by
      rw [intervalIntegral.integral_sub (hinv.div_const _) intervalIntegrable_const,
        intervalIntegral.integral_div, integral_one_div (by
          intro ht
          exact (hpos 0 ht).false),
        Real.log_div (ha.trans_le hab).ne' ha.ne']
      simp
    _ ≤ ∫ t : ℝ in a..b, divisorEulerMoment (auxiliaryProduct Z Y) (-t) - 1 := by
      apply intervalIntegral.integral_mono_on hab
        ((hinv.div_const _).sub intervalIntegrable_const)
        (((continuous_divisorEulerMoment _).sub continuous_const).intervalIntegrable a b)
      intro t ht
      have htpos := ha.trans_le ht.1
      have htscale : 1 ≤ t * Real.log ((Y : ℝ) + 1) :=
        hscale.trans (mul_le_mul_of_nonneg_right ht.1
          (Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg Y))))
      calc
        (1 / t) / (2 * A) - 1 = 1 / (2 * t * A) - 1 := by ring
        _ ≤ _ := sub_le_sub_right (divisorEulerMoment_lower hZY htpos hA hZA htscale) 1
    _ ≤ normalizer (auxiliaryProduct Z Y) :=
      normalizer_integral_le (auxiliaryProduct_pos Z Y).ne' ha.le b

/-- A logarithmic lower bound for the auxiliary normalizer. -/
lemma normalizer_lower_bound {Z Y : ℕ} (hZY : Z ≤ Y) {A : ℝ}
    (hA : 0 < A) (hZA : eulerProduct Z 1 ≤ A)
    (hAY : A ≤ Real.log ((Y : ℝ) + 1)) :
    Real.log (Real.log ((Y : ℝ) + 1)) - Real.log A - 2 ≤
      2 * A * normalizer (auxiliaryProduct Z Y) := by
  have hlog : 0 < Real.log ((Y : ℝ) + 1) := hA.trans_le hAY
  have h := normalizer_lower_integral hZY hA (one_div_pos.mpr hlog)
    (one_div_le_one_div_of_le hA hAY) hZA
    (by rw [one_div_mul_cancel hlog.ne'])
  simp only [one_div, Real.log_inv] at h
  have hmul := (div_le_iff₀ (show 0 < 2 * A by positivity)).mp
    (sub_le_iff_le_add.mp h)
  nlinarith [mul_inv_cancel₀ hA.ne',
    mul_nonneg hA.le (inv_nonneg.mpr hlog.le)]

/-- A nontrivial coefficient has absolute value `1 / (normalizer P * log d)`. -/
lemma abs_coefficient_eq {P d : ℕ} (hP : 1 < P) (hd : 1 < d) :
    |coefficient P d| = 1 / (normalizer P * Real.log d) := by
  rw [abs_of_neg (coefficient_neg hP hd), coefficient, if_neg (ne_of_gt hd)]
  ring

/-- Splitting at Y gives the tilted absolute-moment bound in (3.6). -/
theorem coefficientAbsMoment_le {P Y : ℕ} (hP : 1 < P) (hY : 1 < Y)
    {γ E : ℝ} (hγ : 0 ≤ γ) (hYE : (Y : ℝ) ^ γ ≤ E) :
    coefficientAbsMoment P γ ≤ E + divisorEulerMoment P γ / (normalizer P * Real.log Y) := by
  have hB : 0 < normalizer P := normalizer_pos hP
  have hlogY : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast hY)
  have hden : 0 < normalizer P * Real.log Y := mul_pos hB hlogY
  have hE : 0 ≤ E := (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hYE
  have hpoint (d : ℕ) (hd : d ∈ P.divisors.erase 1) :
      |coefficient P d| * (d : ℝ) ^ γ / d.totient ≤
        E * (|coefficient P d| / d.totient) +
          (1 / (normalizer P * Real.log Y)) * ((d : ℝ) ^ γ / d.totient) := by
    have hd1 := one_lt_of_mem_divisors_erase_one hd
    have hf : 0 ≤ |coefficient P d| / (d.totient : ℝ) :=
      div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
    have hg : 0 ≤ (d : ℝ) ^ γ / d.totient :=
      div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
    by_cases hdY : d ≤ Y
    · have hpow : (d : ℝ) ^ γ ≤ E :=
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hdY) hγ).trans hYE
      calc
        _ = (|coefficient P d| / d.totient) * (d : ℝ) ^ γ := by ring
        _ ≤ (|coefficient P d| / d.totient) * E := mul_le_mul_of_nonneg_left hpow hf
        _ ≤ _ := by nlinarith [mul_nonneg (one_div_nonneg.mpr hden.le) hg]
    · have hac : |coefficient P d| ≤ 1 / (normalizer P * Real.log Y) := by
        rw [abs_coefficient_eq hP hd1]
        apply one_div_le_one_div_of_le hden
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_log (by exact_mod_cast (by omega : 0 < Y))
            (by exact_mod_cast (by omega : Y ≤ d))) hB.le
      calc
        _ = |coefficient P d| * ((d : ℝ) ^ γ / d.totient) := by ring
        _ ≤ (1 / (normalizer P * Real.log Y)) * ((d : ℝ) ^ γ / d.totient) :=
          mul_le_mul_of_nonneg_right hac hg
        _ ≤ _ := by nlinarith [mul_nonneg hE hf]
  have hsmall : (∑ d ∈ P.divisors.erase 1, |coefficient P d| / d.totient) = 1 := by
    simpa [coefficientAbsMoment] using coefficientAbsMoment_zero hP
  have hlarge : (∑ d ∈ P.divisors.erase 1, (d : ℝ) ^ γ / d.totient) ≤ divisorEulerMoment P γ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun d _ _ => div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _))
  calc
    coefficientAbsMoment P γ ≤ ∑ d ∈ P.divisors.erase 1,
        (E * (|coefficient P d| / d.totient) +
          (1 / (normalizer P * Real.log Y)) * ((d : ℝ) ^ γ / d.totient)) :=
      Finset.sum_le_sum hpoint
    _ = E + (1 / (normalizer P * Real.log Y)) *
        ∑ d ∈ P.divisors.erase 1, (d : ℝ) ^ γ / d.totient := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsmall, mul_one]
    _ ≤ E + (1 / (normalizer P * Real.log Y)) * divisorEulerMoment P γ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hlarge (one_div_nonneg.mpr hden.le))
    _ = E + divisorEulerMoment P γ / (normalizer P * Real.log Y) := by ring

/-- At exponent zero, the auxiliary divisor moment is an Euler-product ratio. -/
lemma divisorEulerMoment_zero_factorization {Z Y : ℕ} (hZY : Z ≤ Y) :
    divisorEulerMoment (auxiliaryProduct Z Y) 0 * eulerProduct Z 1 = eulerProduct Y 1 := by
  rw [auxiliaryProduct, divisorEulerMoment_primeProduct _
    (fun _ hp => auxiliaryPrimes_prime hp)]
  convert auxiliary_euler_factorization hZY (1 : ℝ) using 2
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (auxiliaryPrimes_prime hp).ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by
    exact_mod_cast (auxiliaryPrimes_prime hp).ne_one)
  simp only [Real.rpow_zero, Real.rpow_neg_one]
  field_simp
  ring

/-- Bound the auxiliary zero moment by a ratio of logarithms. -/
lemma divisorEulerMoment_zero_le {Z Y : ℕ} (hZY : Z ≤ Y) (hZ : 2 ≤ Z) :
    divisorEulerMoment (auxiliaryProduct Z Y) 0 ≤
      Real.exp 6 * (1 + Real.log Y) / Real.log Z := by
  have hlog : 0 < Real.log (Z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
  apply (le_div_iff₀ hlog).mpr
  calc
    _ ≤ divisorEulerMoment (auxiliaryProduct Z Y) 0 * eulerProduct Z 1 :=
      mul_le_mul_of_nonneg_left (log_le_eulerProduct_one Z) (divisorEulerMoment_nonneg _ _)
    _ = eulerProduct Y 1 := divisorEulerMoment_zero_factorization hZY
    _ ≤ Real.exp 6 * (1 + Real.log Y) := eulerProduct_one_le (hZ.trans hZY)

/-- An exponential bound for tilting a squarefree Euler factor. -/
lemma squarefree_euler_factor_tilt {p γ E : ℝ} (hp : 1 < p)
    (hγ : 0 ≤ γ) (hpE : p ^ γ ≤ E) :
    1 + p ^ γ / (p - 1) ≤
      (1 + 1 / (p - 1)) * Real.exp (E * γ * Real.log p / p) := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  have hlog : 0 ≤ Real.log p := (Real.log_pos hp).le
  have hdiff : p ^ γ - 1 ≤ E * γ * Real.log p := by
    have h := rpow_sub_one_le (γ := γ) hp0
    have hmul := mul_le_mul_of_nonneg_right hpE (mul_nonneg hγ hlog)
    nlinarith
  have hexp : 1 + (p ^ γ - 1) / p ≤ Real.exp (E * γ * Real.log p / p) := by
    calc
      _ ≤ 1 + E * γ * Real.log p / p :=
        add_le_add le_rfl (div_le_div_of_nonneg_right hdiff hp0.le)
      _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (E * γ * Real.log p / p)
  have he : 1 + p ^ γ / (p - 1) = (1 + 1 / (p - 1)) * (1 + (p ^ γ - 1) / p) := by
    field_simp [ne_of_gt hp0, ne_of_gt hpm]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- Tilting a squarefree divisor moment costs an exponential factor. -/
lemma divisorEulerMoment_tilt (ps : Finset ℕ) (hps : ∀ p ∈ ps, p.Prime)
    {γ E : ℝ} (hγ : 0 ≤ γ) (hE : ∀ p ∈ ps, (p : ℝ) ^ γ ≤ E) :
    divisorEulerMoment (∏ p ∈ ps, p) γ ≤
      divisorEulerMoment (∏ p ∈ ps, p) 0 *
        Real.exp (E * γ * ∑ p ∈ ps, Real.log p / p) := by
  have h := Finset.prod_le_prod (s := ps)
    (f := fun p : ℕ => 1 + (p : ℝ) ^ γ / ((p : ℝ) - 1))
    (g := fun p : ℕ => (1 + 1 / ((p : ℝ) - 1)) * Real.exp (E * γ * Real.log p / p))
    (fun p hp => by
      have hpm : 0 < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (hps p hp).one_lt)
      positivity)
    (fun p hp => squarefree_euler_factor_tilt (by exact_mod_cast (hps p hp).one_lt) hγ (hE p hp))
  rw [Finset.prod_mul_distrib, ← Real.exp_sum] at h
  have he : (∑ p ∈ ps, E * γ * Real.log p / p) = E * γ * ∑ p ∈ ps, Real.log p / p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  simpa only [divisorEulerMoment_primeProduct ps hps, Real.rpow_zero, he] using h

/-- Uniformly bound the cost of tilting the auxiliary divisor moment. -/
lemma auxiliary_divisorEulerMoment_tilt {Z Y : ℕ} (hY : 2 ≤ Y)
    {γ : ℝ} (hγ : 0 ≤ γ) (hscale : γ * Real.log Y ≤ 2) :
    divisorEulerMoment (auxiliaryProduct Z Y) γ ≤
      divisorEulerMoment (auxiliaryProduct Z Y) 0 * Real.exp (6 * Real.exp 2) := by
  have hYr : (2 : ℝ) ≤ Y := by exact_mod_cast hY
  have hYE : (Y : ℝ) ^ γ ≤ Real.exp 2 := by
    rw [Real.rpow_def_of_pos (by linarith)]
    exact Real.exp_le_exp.mpr (by linarith [hscale])
  have hlog4 : Real.log 4 ≤ 2 * Real.log Y := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by norm_num : (0 : ℝ) < 4)
        (show (4 : ℝ) ≤ (Y : ℝ) ^ 2 by nlinarith)
  have hsum : (∑ p ∈ auxiliaryPrimes Z Y, Real.log p / p) ≤ 3 * Real.log Y := by
    calc
      _ ≤ ∑ p ∈ Y.primesLE, Real.log p / p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
          (fun p hp _ => div_nonneg (Nat.mem_primesLE.mp hp).2.log_pos.le
            (Nat.cast_nonneg p))
      _ ≤ 3 * Real.log Y := by
        linarith [sum_prime_log_div_le (by omega : 1 ≤ Y)]
  have hcost : γ * (∑ p ∈ auxiliaryPrimes Z Y, Real.log p / p) ≤ 6 := by
    nlinarith [mul_le_mul_of_nonneg_left hsum hγ]
  calc
    _ ≤ divisorEulerMoment (auxiliaryProduct Z Y) 0 *
        Real.exp (Real.exp 2 * γ * ∑ p ∈ auxiliaryPrimes Z Y, Real.log p / p) :=
      divisorEulerMoment_tilt (auxiliaryPrimes Z Y) (fun _ hp => auxiliaryPrimes_prime hp)
        hγ (fun p hp => (Real.rpow_le_rpow (Nat.cast_nonneg p)
          (by exact_mod_cast (mem_auxiliaryPrimes.mp hp).2.2) hγ).trans hYE)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_left hcost (Real.exp_nonneg 2)]))
      (divisorEulerMoment_nonneg _ _)

/-- Every prime divisor of the auxiliary product is an auxiliary prime. -/
lemma prime_dvd_auxiliaryProduct {Z Y p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ auxiliaryProduct Z Y) : p ∈ auxiliaryPrimes Z Y := by
  obtain ⟨q, hq, hpq⟩ := ((Nat.prime_iff.mp hp).dvd_finsetProd_iff id).mp hdvd
  exact ((Nat.prime_dvd_prime_iff_eq hp (auxiliaryPrimes_prime hq)).mp hpq).symm ▸ hq

/-- Every nontrivial auxiliary divisor exceeds the lower cutoff `Z`. -/
lemma auxiliary_divisor_gt {Z Y d : ℕ} (hd : d ∈ (auxiliaryProduct Z Y).divisors.erase 1) :
    Z < d := by
  obtain ⟨hd1, hd⟩ := Finset.mem_erase.mp hd
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
  have hpP := prime_dvd_auxiliaryProduct hp (hpd.trans (Nat.mem_divisors.mp hd).1)
  exact (mem_auxiliaryPrimes.mp hpP).2.1.trans_le
    (Nat.le_of_dvd (Nat.pos_of_mem_divisors hd) hpd)

/-- A normalizer lower bound makes every auxiliary coefficient at most one in magnitude. -/
lemma auxiliary_coefficient_le_one {Z Y : ℕ} (hP : 1 < auxiliaryProduct Z Y)
    (hZ : 1 < Z) (hB : 1 ≤ normalizer (auxiliaryProduct Z Y) * Real.log Z)
    {d : ℕ} (hd : d ∈ (auxiliaryProduct Z Y).divisors) :
    |coefficient (auxiliaryProduct Z Y) d| ≤ 1 := by
  by_cases hd1 : d = 1
  · simp [hd1, coefficient]
  have hZd := auxiliary_divisor_gt (Finset.mem_erase.mpr ⟨hd1, hd⟩)
  rw [abs_coefficient_eq hP (hZ.trans hZd)]
  have hden : 1 ≤ normalizer (auxiliaryProduct Z Y) * Real.log d :=
    hB.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by exact_mod_cast (zero_lt_one.trans hZ))
        (by exact_mod_cast hZd.le)) (normalizer_pos hP).le)
  simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden

/-- An explicit absolute moment bound from a lower bound on the normalizer. -/
def absoluteMomentBound (b : ℝ) : ℝ :=
  Real.exp 2 + 2 * Real.exp 6 * Real.exp (6 * Real.exp 2) / b

/-- The absolute moment bound divided by the normalizer lower bound. -/
def coefficientControl (b : ℝ) : ℝ := absoluteMomentBound b / b

/-- The absolute moment bound is positive for positive `b`. -/
lemma absoluteMomentBound_pos {b : ℝ} (hb : 0 < b) : 0 < absoluteMomentBound b := by
  unfold absoluteMomentBound
  positivity

/-- The coefficient control constant is positive for positive `b`. -/
lemma coefficientControl_pos {b : ℝ} (hb : 0 < b) : 0 < coefficientControl b :=
  div_pos (absoluteMomentBound_pos hb) hb

/-- Bound the auxiliary absolute moment by `absoluteMomentBound`. -/
lemma auxiliary_coefficientAbsMoment_le {Z Y : ℕ} (hZY : Z ≤ Y) (hZ : 2 ≤ Z)
    (hlogZ : 1 ≤ Real.log Z) (hP : 1 < auxiliaryProduct Z Y)
    {b γ : ℝ} (hb : 0 < b) (hB : b ≤ normalizer (auxiliaryProduct Z Y))
    (hγ : 0 ≤ γ) (hscale : γ * Real.log Y ≤ 2) :
    coefficientAbsMoment (auxiliaryProduct Z Y) γ ≤ absoluteMomentBound b := by
  have hY : 1 < Y := by omega
  have hlogY : 1 ≤ Real.log (Y : ℝ) :=
    hlogZ.trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < Z))
      (by exact_mod_cast hZY))
  have hlogYpos : 0 < Real.log (Y : ℝ) := zero_lt_one.trans_le hlogY
  have hYE : (Y : ℝ) ^ γ ≤ Real.exp 2 := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast (by omega : 0 < Y))]
    exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hscale)
  have hzero : divisorEulerMoment (auxiliaryProduct Z Y) 0 ≤
      2 * Real.exp 6 * Real.log Y := by
    calc
      _ ≤ Real.exp 6 * (1 + Real.log Y) / Real.log Z :=
        divisorEulerMoment_zero_le hZY hZ
      _ ≤ Real.exp 6 * (1 + Real.log Y) := div_le_self (by positivity) hlogZ
      _ ≤ 2 * Real.exp 6 * Real.log Y := by nlinarith [Real.exp_pos 6]
  have hmoment : divisorEulerMoment (auxiliaryProduct Z Y) γ ≤
      (2 * Real.exp 6 * Real.exp (6 * Real.exp 2)) * Real.log Y := by
    calc
      _ ≤ divisorEulerMoment (auxiliaryProduct Z Y) 0 * Real.exp (6 * Real.exp 2) :=
        auxiliary_divisorEulerMoment_tilt (hZ.trans hZY) hγ hscale
      _ ≤ (2 * Real.exp 6 * Real.log Y) * Real.exp (6 * Real.exp 2) :=
        mul_le_mul_of_nonneg_right hzero (Real.exp_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ Real.exp 2 + divisorEulerMoment (auxiliaryProduct Z Y) γ /
        (normalizer (auxiliaryProduct Z Y) * Real.log Y) :=
      coefficientAbsMoment_le hP hY hγ hYE
    _ ≤ Real.exp 2 +
        ((2 * Real.exp 6 * Real.exp (6 * Real.exp 2)) * Real.log Y) /
          (b * Real.log Y) := by
      gcongr
    _ = absoluteMomentBound b := by
      unfold absoluteMomentBound
      rw [mul_div_mul_right _ _ hlogYpos.ne']

/-- Bound the auxiliary absolute moment by a constant times the normalizer. -/
lemma auxiliary_coefficientAbsMoment_control {Z Y : ℕ} (hZY : Z ≤ Y) (hZ : 2 ≤ Z)
    (hlogZ : 1 ≤ Real.log Z) (hP : 1 < auxiliaryProduct Z Y)
    {b γ : ℝ} (hb : 0 < b) (hB : b ≤ normalizer (auxiliaryProduct Z Y))
    (hγ : 0 ≤ γ) (hscale : γ * Real.log Y ≤ 2) :
    coefficientAbsMoment (auxiliaryProduct Z Y) γ ≤
      coefficientControl b * normalizer (auxiliaryProduct Z Y) := by
  calc
    _ ≤ absoluteMomentBound b := auxiliary_coefficientAbsMoment_le hZY hZ hlogZ hP hb hB hγ hscale
    _ = coefficientControl b * b := by
      rw [coefficientControl, div_mul_cancel₀ _ (ne_of_gt hb)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (coefficientControl_pos hb).le

/-- The auxiliary prime ranges of Section 3.1, with integral endpoints. -/
def sieveZ (x : ℝ) : ℕ := ⌊x ^ 6⌋₊

/-- The logarithmic upper cutoff `x / (log x)^5` for the sieve primes. -/
def sieveUpperLog (x : ℝ) : ℝ := x / (Real.log x) ^ 5

/-- The upper sieve cutoff, rounded down to an integer. -/
def sieveY (x : ℝ) : ℕ := ⌊Real.exp (sieveUpperLog x)⌋₊

/-- The product of primes between the two sieve cutoffs. -/
def sieveP (x : ℝ) : ℕ := auxiliaryProduct (sieveZ x) (sieveY x)

/-- A fixed positive lower bound used for the sieve normalizer. -/
def normalizerLower : ℝ := 1 / (100 * Real.exp 6)

/-- The fixed normalizer lower bound is positive. -/
lemma normalizerLower_pos : 0 < normalizerLower := by
  unfold normalizerLower
  positivity

/-- Explicit size bounds ensure ordered cutoffs and a uniform normalizer lower bound. -/
lemma sieve_normalizer_lower_of_bounds {x : ℝ} (hx : 0 < x)
    (hlx : 1 ≤ Real.log x) (hZ : 2 ≤ sieveZ x)
    (hlarge : 7 * Real.exp 6 * (Real.log x) ^ 6 ≤ x)
    (hsmall : 6 * Real.log (Real.log x) + Real.log 7 + 8 ≤ Real.log x / 2) :
    sieveZ x ≤ sieveY x ∧ normalizerLower ≤ normalizer (sieveP x) := by
  have hlxpos : 0 < Real.log x := zero_lt_one.trans_le hlx
  have hexp : 1 ≤ Real.exp 6 := Real.one_le_exp (by norm_num)
  have hscale : 7 * Real.exp 6 * Real.log x ≤ sieveUpperLog x := by
    apply (le_div_iff₀ (pow_pos hlxpos 5)).mpr
    nlinarith [hlarge]
  have hZY : sieveZ x ≤ sieveY x := by
    apply Nat.floor_le_floor
    calc
      x ^ 6 = Real.exp (6 * Real.log x) := by
        simpa only [Nat.cast_ofNat, Real.exp_log hx] using
          (Real.exp_nat_mul (Real.log x) 6).symm
      _ ≤ Real.exp (sieveUpperLog x) := Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_right hexp hlxpos.le])
  refine ⟨hZY, ?_⟩
  have hlogZ : Real.log (sieveZ x) ≤ 6 * Real.log x := by
    calc
      _ ≤ Real.log (x ^ 6) := Real.log_le_log
        (by exact_mod_cast (by omega : 0 < sieveZ x)) (Nat.floor_le (by positivity))
      _ = _ := by rw [Real.log_pow]; norm_num
  have hZA : eulerProduct (sieveZ x) 1 ≤ 7 * Real.exp 6 * Real.log x := by
    calc
      _ ≤ Real.exp 6 * (1 + Real.log (sieveZ x)) := eulerProduct_one_le hZ
      _ ≤ Real.exp 6 * (7 * Real.log x) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg 6)
      _ = _ := by ring
  have hYlog : sieveUpperLog x ≤ Real.log ((sieveY x : ℝ) + 1) := by
    calc
      _ = Real.log (Real.exp (sieveUpperLog x)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (Nat.lt_floor_add_one _).le
  have hApos : 0 < 7 * Real.exp 6 * Real.log x := by positivity
  have hbound := normalizer_lower_bound hZY hApos hZA (hscale.trans hYlog)
  have hloglog : Real.log x - 5 * Real.log (Real.log x) ≤
      Real.log (Real.log ((sieveY x : ℝ) + 1)) := by
    calc
      _ = Real.log (sieveUpperLog x) := by
        rw [sieveUpperLog, Real.log_div hx.ne' (pow_pos hlxpos 5).ne', Real.log_pow]
        norm_num
      _ ≤ _ := Real.log_le_log (hApos.trans_le hscale) hYlog
  have hlogA : Real.log (7 * Real.exp 6 * Real.log x) =
      Real.log 7 + 6 + Real.log (Real.log x) := by
    rw [Real.log_mul (by positivity : (7 * Real.exp 6 : ℝ) ≠ 0) hlxpos.ne',
      Real.log_mul (by norm_num : (7 : ℝ) ≠ 0) (Real.exp_ne_zero 6), Real.log_exp]
  rw [hlogA] at hbound
  have hlower : Real.log x / 2 ≤
      2 * (7 * Real.exp 6 * Real.log x) * normalizer (sieveP x) := by
    change _ ≤ 2 * (7 * Real.exp 6 * Real.log x) *
      normalizer (auxiliaryProduct (sieveZ x) (sieveY x))
    linarith
  unfold normalizerLower
  apply (div_le_iff₀ (by positivity : 0 < 100 * Real.exp 6)).mpr
  nlinarith

/-- The lower sieve cutoff tends to infinity. -/
lemma tendsto_sieveZ : Filter.Tendsto sieveZ Filter.atTop Filter.atTop :=
  tendsto_nat_floor_atTop.comp (Filter.tendsto_pow_atTop (by decide : (6 : ℕ) ≠ 0))

/-- The logarithm of the lower sieve cutoff tends to infinity. -/
lemma tendsto_log_sieveZ :
    Filter.Tendsto (fun x : ℝ => Real.log (sieveZ x)) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp tendsto_sieveZ)

/-- The unconditional positive lower bound for B for the paper's parameters. -/
theorem eventually_sieve_normalizer_lower : ∀ᶠ x : ℝ in Filter.atTop,
    sieveZ x ≤ sieveY x ∧ normalizerLower ≤ normalizer (sieveP x) := by
  have hpow : Filter.Tendsto (fun x : ℝ => (Real.log x) ^ 6 / x)
      Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 6 one_ne_zero
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x)
      Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      Real.tendsto_log_atTop
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    tendsto_sieveZ.eventually_ge_atTop 2,
    hpow.eventually_le_const (by positivity : (0 : ℝ) < 1 / (7 * Real.exp 6)),
    hlog.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 24),
    Real.tendsto_log_atTop.eventually_ge_atTop (4 * (Real.log 7 + 8))]
    with x hx hlx hZ hpow hlog hconst
  apply sieve_normalizer_lower_of_bounds hx hlx hZ
  · simpa [mul_comm] using
      (div_le_div_iff₀ hx (by positivity : 0 < 7 * Real.exp 6)).mp hpow
  · have h := (div_le_iff₀ (zero_lt_one.trans_le hlx)).mp hlog
    linarith

/-- The tilt scale reciprocal to the logarithmic upper sieve cutoff. -/
def sieveBeta (x : ℝ) : ℝ := 1 / sieveUpperLog x

/-- A common constant controlling the coefficient moments. -/
def weightConstant : ℝ :=
  1 + absoluteMomentBound normalizerLower + coefficientControl normalizerLower

/-- The common coefficient constant exceeds one. -/
lemma weightConstant_gt_one : 1 < weightConstant := by
  unfold weightConstant
  linarith [absoluteMomentBound_pos normalizerLower_pos,
    coefficientControl_pos normalizerLower_pos]

/-- The coefficient estimates needed by the finite weighted sieve argument. -/
structure CoefficientEstimates (P : ℕ) (β C : ℝ) : Prop where
  /-- The sieve modulus exceeds one. -/
  one_lt : 1 < P
  /-- The sieve modulus is squarefree. -/
  squarefree : Squarefree P
  /-- Every divisor coefficient has absolute value at most one. -/
  abs_le_one : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1
  /-- The absolute moment is uniformly bounded for tilts up to `2 * β`. -/
  absMoment_le : ∀ γ : ℝ, 0 ≤ γ → γ ≤ 2 * β → coefficientAbsMoment P γ ≤ C
  /-- The absolute moment is also controlled relative to the normalizer. -/
  moment_control : ∀ γ : ℝ, 0 ≤ γ → γ ≤ 2 * β →
    coefficientAbsMoment P γ ≤ C * normalizer P

/-- The sieve coefficients eventually satisfy all required uniform estimates. -/
lemma eventually_sieve_coefficient_estimates : ∀ᶠ x : ℝ in Filter.atTop,
    0 < sieveBeta x ∧ CoefficientEstimates (sieveP x) (sieveBeta x) weightConstant := by
  have hunit := (Filter.Tendsto.const_mul_atTop normalizerLower_pos tendsto_log_sieveZ).eventually
    (Filter.eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_sieve_normalizer_lower,
    tendsto_sieveZ.eventually (Filter.eventually_ge_atTop 2),
    tendsto_log_sieveZ.eventually (Filter.eventually_ge_atTop (1 : ℝ)),
    Filter.eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ)), hunit]
    with x hB hZ hlogZ hx hlx hunit'
  obtain ⟨hZY, hB⟩ := hB
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 < Real.log x := by linarith
  have hupper : 0 < sieveUpperLog x := div_pos hx0 (pow_pos hlx0 5)
  have hP : 1 < sieveP x := by
    have hp0 : 0 < sieveP x := auxiliaryProduct_pos _ _
    by_contra h
    have he : sieveP x = 1 := by omega
    have hb0 : normalizer (sieveP x) = 0 := by simp [he, normalizer]
    rw [hb0] at hB
    exact (not_le_of_gt normalizerLower_pos) hB
  have hY : 2 ≤ sieveY x := hZ.trans hZY
  have hY0 : (0 : ℝ) < sieveY x := by exact_mod_cast (by omega : 0 < sieveY x)
  have hYlog : Real.log (sieveY x : ℝ) ≤ sieveUpperLog x := by
    have h := Real.log_le_log hY0 (Nat.floor_le (Real.exp_pos (sieveUpperLog x)).le)
    simpa only [Real.log_exp] using h
  have hscale (γ : ℝ) (hγ : 0 ≤ γ) (hγβ : γ ≤ 2 * sieveBeta x) :
      γ * Real.log (sieveY x : ℝ) ≤ 2 := by
    calc
      _ ≤ γ * sieveUpperLog x := mul_le_mul_of_nonneg_left hYlog hγ
      _ ≤ (2 * sieveBeta x) * sieveUpperLog x := mul_le_mul_of_nonneg_right hγβ hupper.le
      _ = 2 := by unfold sieveBeta; field_simp
  have hC1 : absoluteMomentBound normalizerLower ≤ weightConstant := by
    unfold weightConstant
    have h := coefficientControl_pos normalizerLower_pos
    linarith
  have hC2 : coefficientControl normalizerLower ≤ weightConstant := by
    unfold weightConstant
    have h := absoluteMomentBound_pos normalizerLower_pos
    linarith
  refine ⟨one_div_pos.mpr hupper, ⟨hP, auxiliaryProduct_squarefree _ _, ?_, ?_, ?_⟩⟩
  · intro d hd
    exact auxiliary_coefficient_le_one hP (by omega : 1 < sieveZ x)
      (hunit'.trans (mul_le_mul_of_nonneg_right hB (by linarith : 0 ≤ Real.log (sieveZ x : ℝ)))) hd
  · intro γ hγ hγβ
    exact (auxiliary_coefficientAbsMoment_le hZY hZ hlogZ hP normalizerLower_pos hB hγ
      (hscale γ hγ hγβ)).trans hC1
  · intro γ hγ hγβ
    exact (auxiliary_coefficientAbsMoment_control hZY hZ hlogZ hP normalizerLower_pos hB hγ
      (hscale γ hγ hγβ)).trans (mul_le_mul_of_nonneg_right hC2 (normalizer_pos hP).le)

/-- Squared coefficient mass normalized to a probability on divisors. -/
def divisorProbability (P : ℕ) (d : DivisorIndex P) : ℝ :=
  (coefficient P d.val ^ 2 / d.val.totient) / coefficientMoment P 0

/-- The normalized divisor mass is nonnegative. -/
lemma divisorProbability_nonneg {P : ℕ} (hP : P ≠ 0) (d : DivisorIndex P) :
    0 ≤ divisorProbability P d := by
  exact div_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    (zero_le_one.trans (coefficientMoment_ge_one hP 0))

/-- The normalized divisor masses sum to one. -/
lemma sum_divisorProbability {P : ℕ} (hP : P ≠ 0) :
    (∑ d : DivisorIndex P, divisorProbability P d) = 1 := by
  unfold divisorProbability
  rw [← Finset.sum_div,
    sum_divisorIndex P (fun d => coefficient P d ^ 2 / (d.totient : ℝ)),
    ← coefficientMoment_zero]
  exact div_self (ne_of_gt (zero_lt_one.trans_le (coefficientMoment_ge_one hP 0)))

/-- Tuple mass is a fixed scale times the product of the divisor probabilities. -/
lemma tupleMass_eq_probability {P k : ℕ} (hP : P ≠ 0) (r : DivisorTuple P k) :
    tupleMass r = coefficientMoment P 0 ^ k * ∏ i, divisorProbability P (r i) := by
  have hA : coefficientMoment P 0 ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (coefficientMoment_ge_one hP 0))
  rw [mul_comm, ← div_eq_iff (pow_ne_zero k hA)]
  simp [tupleMass, divisorProbability, Finset.prod_div_distrib]

/-- A prime divides a random divisor with probability at most `4 / p`. -/
lemma divisorProbability_prime_incidence {P p : ℕ} {β C : ℝ}
    (h : CoefficientEstimates P β C) (hp : p.Prime) (hpP : p ∣ P) :
    (∑ d : DivisorIndex P, divisorProbability P d * if p ∣ d.val then 1 else 0) ≤ 4 / (p : ℝ) := by
  classical
  have hP : P ≠ 0 := h.squarefree.ne_zero
  have hA : 1 ≤ coefficientMoment P 0 := coefficientMoment_ge_one hP 0
  simp only [divisorProbability]
  rw [sum_divisorIndex P (fun d =>
    (coefficient P d ^ 2 / d.totient) / coefficientMoment P 0 *
      if p ∣ d then 1 else 0)]
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  calc
    _ ≤ ∑ d ∈ P.divisors.filter (fun d => p ∣ d),
        |coefficient P d| / d.totient := by
      apply Finset.sum_le_sum
      intro d hd
      have hc := h.abs_le_one d (Finset.mem_filter.mp hd).1
      have hs : coefficient P d ^ 2 ≤ |coefficient P d| := by
        nlinarith [sq_abs (coefficient P d), abs_nonneg (coefficient P d)]
      exact (div_le_self
        (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) hA).trans
        (div_le_div_of_nonneg_right hs (Nat.cast_nonneg _))
    _ ≤ 4 / (p : ℝ) := coefficient_prime_incidence h.one_lt h.squarefree hp hpP
      (h.abs_le_one p (Nat.mem_divisors.mpr ⟨hpP, hP⟩))

/-- Failure of pairwise coprimality is witnessed by a shared prime factor. -/
lemma noncoprime_pair_iff_common_prime {P k : ℕ} (hP : P ≠ 0) (r : DivisorTuple P k) :
    (¬∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) ↔
      ∃ p : P.primeFactors, ∃ i j, i ≠ j ∧ p.val ∣ (r i).val ∧ p.val ∣ (r j).val := by
  classical
  simp only [not_forall, Nat.Prime.not_coprime_iff_dvd]
  constructor
  · rintro ⟨i, j, hij, p, hp, hpi, hpj⟩
    exact ⟨⟨p, hp.mem_primeFactors (hpi.trans (Nat.dvd_of_mem_divisors (r i).property)) hP⟩,
      i, j, hij, hpi, hpj⟩
  · rintro ⟨p, i, j, hij, hpi, hpj⟩
    exact ⟨i, j, hij, p, Nat.prime_of_mem_primeFactors p.property, hpi, hpj⟩

/-- The discarded mass from tuples sharing a prime, with an explicit constant. -/
theorem diagonal_collision_le {P M k : ℕ} {β C : ℝ}
    (h : CoefficientEstimates P β C) (hM : 0 < M)
    (hmin : ∀ p ∈ P.primeFactors, M < p) :
    (∑ r : DivisorTuple P k, tupleMass r *
      if ¬∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val then 1 else 0) ≤
        (16 * (k : ℝ) ^ 2 / M) * coefficientMoment P 0 ^ k := by
  classical
  have hP : P ≠ 0 := h.squarefree.ne_zero
  have hA : 0 ≤ coefficientMoment P 0 ^ k :=
    pow_nonneg (zero_le_one.trans (coefficientMoment_ge_one hP 0)) k
  have hcollision := product_collision_bound (divisorProbability P)
    (divisorProbability_nonneg hP) (sum_divisorProbability hP)
    (fun (p : P.primeFactors) (d : DivisorIndex P) => p.val ∣ d.val) k
  have hincidence :
      (∑ p : P.primeFactors,
        (∑ d : DivisorIndex P, divisorProbability P d *
          if p.val ∣ d.val then 1 else 0) ^ 2) ≤ 16 / (M : ℝ) := by
    calc
      _ ≤ ∑ p : P.primeFactors, (4 / (p.val : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro p _
        have hnonneg : 0 ≤ ∑ d : DivisorIndex P, divisorProbability P d *
            if p.val ∣ d.val then 1 else 0 := by
          apply Finset.sum_nonneg
          intro d _
          exact mul_nonneg (divisorProbability_nonneg hP d) (by split_ifs <;> norm_num)
        exact pow_le_pow_left₀ hnonneg
          (divisorProbability_prime_incidence h
            (Nat.prime_of_mem_primeFactors p.property)
            (Nat.dvd_of_mem_primeFactors p.property)) 2
      _ = 16 * ∑ p ∈ P.primeFactors, 1 / (p : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        change (∑ p ∈ P.primeFactors.attach, (4 / (p.val : ℝ)) ^ 2) = _
        rw [Finset.sum_attach P.primeFactors (fun p : ℕ => (4 / (p : ℝ)) ^ 2)]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ 16 * (1 / (M : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc
          _ ≤ ∑ p ∈ Finset.Ioc M (max M P), 1 / (p : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (fun p hp => Finset.mem_Ioc.mpr ⟨hmin p hp,
                (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) (Nat.dvd_of_mem_primeFactors hp)).trans
                  (le_max_right _ _)⟩) (fun _ _ _ => by positivity)
          _ ≤ 1 / (M : ℝ) - 1 / ((max M P : ℕ) : ℝ) := by
            simpa only [one_div] using
              (sum_Ioc_inv_sq_le_sub (α := ℝ) hM.ne' (le_max_left M P))
          _ ≤ _ := sub_le_self _ (by positivity)
      _ = 16 / (M : ℝ) := by ring
  calc
    _ = coefficientMoment P 0 ^ k *
        ∑ r : DivisorTuple P k, (∏ i, divisorProbability P (r i)) *
          if ∃ p : P.primeFactors, ∃ i j,
            i ≠ j ∧ p.val ∣ (r i).val ∧ p.val ∣ (r j).val then 1 else 0 := by
      simp_rw [tupleMass_eq_probability hP, noncoprime_pair_iff_common_prime hP,
        mul_assoc]
      rw [Finset.mul_sum]
    _ ≤ coefficientMoment P 0 ^ k * ((k : ℝ) ^ 2 * (16 / (M : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact hcollision.trans (mul_le_mul_of_nonneg_left hincidence (sq_nonneg _))
    _ = _ := by ring

/-- The total diagonal mass over the truncated tuple region. -/
def diagonalMass (P k : ℕ) (D : ℝ) : ℝ := ∑ r ∈ tupleRegion P k D, tupleMass r

/-- The total diagonal mass is nonnegative. -/
lemma diagonalMass_nonneg (P k : ℕ) (D : ℝ) : 0 ≤ diagonalMass P k D :=
  Finset.sum_nonneg (fun r _ => tupleMass_nonneg r)

/-- The only losses in the diagonal are the product cutoff and shared primes. -/
theorem diagonalMass_tail_collision {P M k : ℕ} {β C D : ℝ}
    (h : CoefficientEstimates P β C) (hM : 0 < M)
    (hmin : ∀ p ∈ P.primeFactors, M < p) (hD : 0 < D) (hβ : 0 ≤ β) :
    coefficientMoment P 0 ^ k - diagonalMass P k D ≤
      D ^ (-β) * coefficientMoment P β ^ k +
        (16 * (k : ℝ) ^ 2 / M) * coefficientMoment P 0 ^ k := by
  classical
  calc
    _ ≤ (∑ r ∈ (Finset.univ : Finset (DivisorTuple P k)).filter
          (fun r => D < (tupleProduct r : ℝ)), tupleMass r) +
        ∑ r : DivisorTuple P k, tupleMass r *
          if ¬∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val then 1 else 0 := by
      rw [← sum_tupleMass, diagonalMass, tupleRegion]
      simp only [Finset.sum_filter]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro r _
      have hmass := tupleMass_nonneg r
      split_ifs <;> grind
    _ ≤ _ := add_le_add (diagonal_tail_le P k hD hβ) (diagonal_collision_le h hM hmin)

/-- Injective indexing bounds the row sum away from the diagonal by the full sum minus one. -/
lemma indexed_offdiag_sum_le {ι Λ : Type*} [Fintype ι] [Fintype Λ]
    [DecidableEq ι] (σ : ι → Λ) (hσ : Function.Injective σ)
    (K : Λ → Λ → ℝ) (hdiag : ∀ j, K j j = 1) (i : ι) :
    (∑ j : ι, if j = i then 0 else |K (σ i) (σ j)|) ≤
      (∑ τ : Λ, |K (σ i) τ|) - 1 := by
  classical
  rw [le_sub_iff_add_le]
  calc
    _ = ∑ j : ι, |K (σ i) (σ j)| := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      simp [hdiag, Finset.sum_ite, Finset.filter_ne']
    _ = ∑ τ ∈ Finset.univ.image σ, |K (σ i) τ| := by
      rw [Finset.sum_image hσ.injOn]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun τ _ _ => abs_nonneg (K (σ i) τ))

/-- Row bounds control the second moment of an indexed sum of product basis functions. -/
lemma indexed_product_second_moment {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] (size : α → ℕ) (hsize : ∀ p, 1 < size p) {k : ℕ}
    (root : (p : α) → Fin k → Fin (size p)) (hroot : ∀ p, Function.Injective (root p))
    (σ : ι → α → Option (Fin k)) (hσ : Function.Injective σ) (c : ι → ℝ) (ε : ℝ)
    (hbound : ∀ i, (∏ p, localRow (size p) k (σ i p)) - 1 ≤ ε) :
    |Finset.expect Finset.univ (fun t =>
        (∑ i, c i * productBasis (fun p => localBasis (root p)) (σ i) t) ^ 2) -
      ∑ i, c i ^ 2| ≤ ε * ∑ i, c i ^ 2 := by
  classical
  have hmoment : Finset.expect Finset.univ (fun t =>
      (∑ i, c i * productBasis (fun p => localBasis (root p)) (σ i) t) ^ 2) =
      ∑ i, ∑ j, c i * c j * productKernel size (σ i) (σ j) := by
    simp_rw [pow_two, Finset.sum_mul_sum]
    simp_rw [Finset.expect_sum_comm]
    simp_rw [mul_mul_mul_comm (c _) _ (c _) _, ← Finset.mul_expect,
      average_productBasis_localBasis size hsize root hroot]
  rw [hmoment]
  apply quadratic_form_near_diagonal c (fun i j => productKernel size (σ i) (σ j)) ε
    (fun i j => productKernel_symm size (σ i) (σ j))
    (fun i => productKernel_diag size (σ i))
  intro i
  exact (indexed_offdiag_sum_le σ hσ (productKernel size)
    (productKernel_diag size) i).trans (by simpa [sum_abs_productKernel size hsize] using hbound i)

/-- Prime divisors of `P` regarded as a finite index type. -/
abbrev PrimeIndex (P : ℕ) := {p : ℕ // p ∈ P.primeFactors}

/-- Assign each used prime to a tuple coordinate containing it. -/
def tupleAssignment {P k : ℕ} (r : DivisorTuple P k) : PrimeIndex P → Option (Fin k) := by
  classical
  exact fun p => if h : ∃ i, p.val ∣ (r i).val then some (Classical.choose h) else none

/-- A prime divides at most one coordinate of a pairwise coprime tuple. -/
lemma prime_coordinate_unique {P k p : ℕ} (hp : p.Prime) (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val)
    {i j : Fin k} (hi : p ∣ (r i).val) (hj : p ∣ (r j).val) : i = j := by
  by_contra hij
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hi, hj⟩) (hpair i j hij)

/-- In a pairwise coprime tuple, a prime is assigned exactly to the coordinate it divides. -/
lemma tupleAssignment_eq_some {P k : ℕ} (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val)
    (p : PrimeIndex P) (i : Fin k) : tupleAssignment r p = some i ↔ p.val ∣ (r i).val := by
  classical
  unfold tupleAssignment
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact Classical.choose_spec h
    · exact prime_coordinate_unique (Nat.prime_of_mem_primeFactors p.property) r hpair
        (Classical.choose_spec h)
  · simp only [false_iff]
    exact fun hi => h ⟨i, hi⟩

/-- A truncated tuple is determined by its prime assignment when `P` is squarefree. -/
lemma tupleAssignment_injective {P k : ℕ} (hP : Squarefree P) (D : ℝ) :
    Function.Injective (fun r : tupleRegion P k D => tupleAssignment r.val) := by
  classical
  intro r s hrs
  dsimp only at hrs
  apply Subtype.ext
  funext i
  apply Subtype.ext
  apply (Nat.Squarefree.ext_iff
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors (r.val i).property))
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors (s.val i).property))).mpr
  intro p hp
  by_cases hpP : p ∣ P
  · let p' : PrimeIndex P := ⟨p, hp.mem_primeFactors hpP hP.ne_zero⟩
    rw [← tupleAssignment_eq_some r.val (Finset.mem_filter.mp r.property).2.1 p' i,
      ← tupleAssignment_eq_some s.val (Finset.mem_filter.mp s.property).2.1 p' i, hrs]
  · constructor <;> intro h
    · exact (hpP (h.trans (Nat.dvd_of_mem_divisors (r.val i).property))).elim
    · exact (hpP (h.trans (Nat.dvd_of_mem_divisors (s.val i).property))).elim

/-- Regroup a product over assigned primes by tuple coordinates. -/
lemma tupleAssignment_prod {P k : ℕ} {M : Type*} [CommMonoid M]
    (r : DivisorTuple P k) (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val)
    (f : PrimeIndex P → Fin k → M) :
    (∏ p : PrimeIndex P, match tupleAssignment r p with | none => 1 | some i => f p i) =
      ∏ i, ∏ p : PrimeIndex P, if p.val ∣ (r i).val then f p i else 1 := by
  classical
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p _
  simp_rw [← tupleAssignment_eq_some r hpair p]
  cases tupleAssignment r p <;> simp

/-- Restrict a product over primes dividing `P` to those dividing `d`. -/
lemma prod_primeIndex_dvd {P d : ℕ} (hP : P ≠ 0) (hd : d ∣ P)
    {M : Type*} [CommMonoid M] (f : ℕ → M) :
    (∏ p : PrimeIndex P, if p.val ∣ d then f p.val else 1) = ∏ p ∈ d.primeFactors, f p := by
  classical
  have h := Finset.prod_attach P.primeFactors (fun p => if p ∣ d then f p else 1)
  simp only [Finset.attach_eq_univ] at h
  rw [h, ← Finset.prod_filter, Nat.primeFactors_filter_dvd_of_dvd hP hd]

/-- The product of pairwise coprime divisors of `P` divides `P`. -/
lemma tupleProduct_dvd {P k : ℕ} (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) : tupleProduct r ∣ P := by
  exact Fintype.prod_dvd_of_isRelPrime
    (fun i j hij => Nat.coprime_iff_isRelPrime.mp (hpair i j hij))
    (fun i => Nat.dvd_of_mem_divisors (r i).property)

/-- A prime is assigned precisely when it divides the tuple product. -/
lemma tupleAssignment_isSome {P k : ℕ} (r : DivisorTuple P k) (p : PrimeIndex P) :
    (tupleAssignment r p).isSome ↔ p.val ∣ tupleProduct r := by
  classical
  simp [tupleAssignment, tupleProduct,
    (Nat.prime_of_mem_primeFactors p.property).prime.dvd_finsetProd_iff]

/-- The product of assigned primes equals the tuple product for squarefree `P`. -/
lemma assignmentProduct_tupleAssignment {P k : ℕ} (hP : Squarefree P) (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) :
    assignmentProduct (fun p : PrimeIndex P => p.val) (tupleAssignment r) = tupleProduct r := by
  classical
  unfold assignmentProduct assignmentSupport
  simp_rw [Finset.prod_filter, tupleAssignment_isSome]
  rw [prod_primeIndex_dvd hP.ne_zero (tupleProduct_dvd r hpair) (fun p => p),
    Nat.prod_primeFactors_of_squarefree
      (hP.squarefree_of_dvd (tupleProduct_dvd r hpair))]

/-- The constant function and unnormalized residue factors. -/
def rawLocalBasis {p k : ℕ} (root : Fin k → Fin p) (i : Option (Fin k)) (t : Fin p) : ℝ :=
  match i with
  | none => 1
  | some j => residueFactor (root j) t

/-- The factor converting normalized product basis functions to unnormalized ones. -/
def assignmentNormalizer {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ : α → Option (Fin k)) : ℝ :=
  ∏ p, match σ p with | none => 1 | some _ => (Real.sqrt ((size p : ℝ) - 1))⁻¹

/-- The product of local variances on an assignment's support. -/
def assignmentVariance {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ : α → Option (Fin k)) : ℝ :=
  ∏ p, match σ p with | none => 1 | some _ => 1 / ((size p : ℝ) - 1)

/-- The square of the assignment normalizer equals the assignment variance. -/
lemma assignmentNormalizer_sq {α : Type*} [Fintype α] (size : α → ℕ)
    (hsize : ∀ p, 1 < size p) {k : ℕ} (σ : α → Option (Fin k)) :
    assignmentNormalizer size σ ^ 2 = assignmentVariance size σ := by
  unfold assignmentNormalizer assignmentVariance
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p _
  have hp : (1 : ℝ) ≤ size p := by exact_mod_cast (hsize p).le
  cases σ p <;> simp [inv_pow, Real.sq_sqrt (sub_nonneg.mpr hp), one_div]

/-- Multiplying by the assignment normalizer removes the local basis normalization. -/
lemma assignmentNormalizer_mul_basis {α : Type*} [Fintype α] (size : α → ℕ)
    (hsize : ∀ p, 1 < size p) {k : ℕ} (root : (p : α) → Fin k → Fin (size p))
    (σ : α → Option (Fin k)) (t : (p : α) → Fin (size p)) :
    assignmentNormalizer size σ * productBasis (fun p => localBasis (root p)) σ t =
      productBasis (fun p => rawLocalBasis (root p)) σ t := by
  unfold assignmentNormalizer productBasis
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  have hp : Real.sqrt ((size p : ℝ) - 1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr (by exact_mod_cast hsize p)))
  cases σ p <;> simp [localBasis, rawLocalBasis, hp]

/-- For squarefree `d`, the product of `1 / (p - 1)` equals `1 / φ(d)`. -/
lemma prod_primeFactors_inv_sub_one {d : ℕ} (hd : Squarefree d) :
    (∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 1)) = 1 / (d.totient : ℝ) := by
  rw [Finset.prod_div_distrib, Finset.prod_const_one,
    totient_eq_prod_sub_one_of_squarefree hd, Nat.cast_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]

/-- A tuple's assignment variance is the product of its reciprocal totients. -/
lemma assignmentVariance_tuple {P k : ℕ} (hP : Squarefree P) (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) :
    assignmentVariance (fun p : PrimeIndex P => p.val) (tupleAssignment r) =
      ∏ i, 1 / ((r i).val.totient : ℝ) := by
  rw [assignmentVariance, tupleAssignment_prod r hpair (fun p _ => 1 / ((p.val : ℝ) - 1))]
  apply Finset.prod_congr rfl
  intro i _
  have hd := (Nat.mem_divisors.mp (r i).property).1
  have hsq : Squarefree (r i).val := fun q hq => hP q (hq.trans hd)
  rw [prod_primeIndex_dvd hP.ne_zero hd (fun p : ℕ => 1 / ((p : ℝ) - 1)),
    prod_primeFactors_inv_sub_one hsq]

/-- The product of coefficients attached to a divisor tuple. -/
def tupleAmplitude {P k : ℕ} (r : DivisorTuple P k) : ℝ := ∏ i, coefficient P (r i).val

/-- The tuple amplitude rescaled for expansion in the normalized basis. -/
def tupleNormalizedCoefficient {P k : ℕ} (r : DivisorTuple P k) : ℝ :=
  tupleAmplitude r * assignmentNormalizer (fun p : PrimeIndex P => p.val) (tupleAssignment r)

/-- A normalized tuple coefficient has square equal to its diagonal mass. -/
lemma tupleNormalizedCoefficient_sq {P k : ℕ} (hP : Squarefree P) (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) :
    tupleNormalizedCoefficient r ^ 2 = tupleMass r := by
  rw [tupleNormalizedCoefficient, mul_pow,
    assignmentNormalizer_sq _ (fun p => (Nat.prime_of_mem_primeFactors p.property).one_lt),
    assignmentVariance_tuple hP r hpair]
  simp only [tupleAmplitude, tupleMass, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, mul_one_div]

/-- The truncated divisor sum weighted by coefficients and local residue factors. -/
def residueWeight (P k : ℕ) (D : ℝ) (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (t : (p : PrimeIndex P) → Fin p.val) : ℝ :=
  ∑ r : tupleRegion P k D,
    tupleAmplitude r.val * productBasis (fun p => rawLocalBasis (root p)) (tupleAssignment r.val) t

/-- The tuple weight has the diagonal second moment claimed in (3.9). -/
theorem residueWeight_second_moment {P k : ℕ} (hP : Squarefree P) (D : ℝ)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (ε : ℝ) (hbound : ∀ r : tupleRegion P k D,
      (∏ p : PrimeIndex P, localRow p.val k (tupleAssignment r.val p)) - 1 ≤ ε) :
    |Finset.expect Finset.univ (fun t => residueWeight P k D root t ^ 2) - diagonalMass P k D| ≤
      ε * diagonalMass P k D := by
  classical
  have hsize (p : PrimeIndex P) : 1 < p.val :=
    (Nat.prime_of_mem_primeFactors p.property).one_lt
  have hmass : (∑ r : tupleRegion P k D, tupleNormalizedCoefficient r.val ^ 2) =
      diagonalMass P k D := by
    rw [diagonalMass, ← Finset.sum_attach (tupleRegion P k D) tupleMass]
    apply Finset.sum_congr rfl
    intro r _
    exact tupleNormalizedCoefficient_sq hP r.val (Finset.mem_filter.mp r.property).2.1
  have hweight (t : (p : PrimeIndex P) → Fin p.val) :
      (∑ r : tupleRegion P k D, tupleNormalizedCoefficient r.val *
        productBasis (fun p => localBasis (root p)) (tupleAssignment r.val) t) =
      residueWeight P k D root t := by
    simp only [tupleNormalizedCoefficient, mul_assoc,
      assignmentNormalizer_mul_basis _ hsize, residueWeight]
  simpa only [hweight, hmass] using
    indexed_product_second_moment (fun p : PrimeIndex P => p.val) hsize root hroot
      (fun r : tupleRegion P k D => tupleAssignment r.val) (tupleAssignment_injective hP D)
      (fun r => tupleNormalizedCoefficient r.val) ε hbound

/-- An explicit exponential bound for the second moment's deviation from the diagonal mass. -/
lemma residueWeight_second_moment_bound {P k : ℕ} (hP : Squarefree P) (hk : 1 ≤ k)
    {M D : ℝ} (hM : 1 < M) (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ))
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p)) :
    |Finset.expect Finset.univ (fun t => residueWeight P k D root t ^ 2) - diagonalMass P k D| ≤
      (Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) - 1) * diagonalMass P k D := by
  apply residueWeight_second_moment hP D root hroot
  intro r
  apply sub_le_sub_right _ 1
  apply assignment_row_bound (fun p : PrimeIndex P => p.val) hk (tupleAssignment r.val) hM
    (fun p => hmin p.val p.property)
  rw [assignmentProduct_tupleAssignment hP r.val (Finset.mem_filter.mp r.property).2.1]
  exact (Finset.mem_filter.mp r.property).2.2

/-- The average of `f` over the integers in `[0, T)`. -/
def integerAverage (T : ℕ) (f : ℕ → ℝ) : ℝ := (∑ n ∈ Finset.range T, f n) / T

/-- Expand a function of residues as a sum of residue indicators. -/
lemma residue_expansion {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ) (n : ℕ) :
    g ⟨n % m, Nat.mod_lt n hm⟩ = ∑ a : Fin m, g a * residueIndicator m a.val n := by
  simpa [residueIndicator, Fin.ext_iff, mul_ite] using
    (Fintype.sum_ite_eq (⟨n % m, Nat.mod_lt n hm⟩ : Fin m) g).symm

/-- Express a periodic average using the frequencies of its residue classes. -/
lemma integerAverage_residue_expansion {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ) (T : ℕ) :
    integerAverage T (fun n => g ⟨n % m, Nat.mod_lt n hm⟩) =
      ∑ a : Fin m, g a * ((∑ n ∈ Finset.range T, residueIndicator m a.val n) / T) := by
  classical
  unfold integerAverage
  simp_rw [residue_expansion hm g]
  rw [Finset.sum_comm, Finset.sum_div]
  simp_rw [← Finset.mul_sum, mul_div_assoc]

/-- A bounded function of one residue class has interval-average error at most m/T. -/
theorem residue_average_bounded_error {m T : ℕ} (hm : 0 < m) (hT : 0 < T)
    (g : Fin m → ℝ) (hg : ∀ a, |g a| ≤ 1) :
    |integerAverage T (fun n => g ⟨n % m, Nat.mod_lt n hm⟩) - Finset.expect Finset.univ g| ≤
      (m : ℝ) / T := by
  rw [integerAverage_residue_expansion hm, Fintype.expect_eq_sum_div_card,
    Fintype.card_fin, div_eq_mul_one_div, Finset.sum_mul, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a : Fin m, |g a * ((∑ n ∈ Finset.range T, residueIndicator m a.val n) / T) -
        g a * (1 / (m : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin m, 1 / (T : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      rw [← mul_sub, abs_mul]
      have h := mul_le_mul (hg a) (residue_average_error a.isLt hT)
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simpa only [one_mul] using h
    _ = (m : ℝ) / T := by simp; ring

/-- Averaging over complete periods equals the uniform average over residues. -/
lemma integerAverage_complete_residues {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (hmq : m ∣ q) (g : Fin m → ℝ) :
    integerAverage q (fun n => g ⟨n % m, Nat.mod_lt n hm⟩) = Finset.expect Finset.univ g := by
  rw [integerAverage_residue_expansion hm, Fintype.expect_eq_sum_div_card,
    Fintype.card_fin, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  have hcount : ((Finset.range q).filter fun n => n % m = a.val).card = q / m := by
    simpa [Nat.count_eq_card_filter_range, Nat.ModEq, Nat.mod_eq_of_lt a.isLt,
      Nat.mod_eq_zero_of_dvd hmq] using Nat.count_modEq_card q hm a.val
  simp only [residueIndicator, Finset.sum_boole, hcount,
    Nat.cast_div hmq (by positivity : (m : ℝ) ≠ 0)]
  field_simp

/-- The interval average of a bounded periodic function has error at most `m / T`. -/
lemma integerAverage_period_error {m q T : ℕ} (hm : 0 < m) (hq : 0 < q) (hT : 0 < T)
    (hmq : m ∣ q) (f : ℕ → ℝ) (hperiod : ∀ n, f (n % m) = f n) (hf : ∀ n, |f n| ≤ 1) :
    |integerAverage T f - integerAverage q f| ≤ (m : ℝ) / T := by
  simpa only [← integerAverage_complete_residues hm hq hmq, hperiod] using
    residue_average_bounded_error hm hT (fun a => f a) (fun a => hf a)

/-- Expand the average of a squared weighted sum into pairwise averages. -/
lemma integerAverage_weight_sq {ι : Type*} [Fintype ι] (T : ℕ) (c : ι → ℝ) (f : ι → ℕ → ℝ) :
    integerAverage T (fun n => (∑ i, c i * f i n) ^ 2) =
      ∑ i, ∑ j, c i * c j * integerAverage T (fun n => f i n * f j n) := by
  simp only [integerAverage, pow_two, Finset.sum_mul_sum, mul_mul_mul_comm]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.range T), ← Finset.mul_sum]
  simp only [Finset.sum_div, mul_div_assoc]

/-- Pairwise average errors give a quadratic error bound for a squared weighted sum. -/
lemma integerAverage_weight_error {ι : Type*} [Fintype ι] (q T : ℕ)
    (c : ι → ℝ) (hc : ∀ i, |c i| ≤ 1) (f : ι → ℕ → ℝ) (E : ℝ)
    (hpair : ∀ i j, |integerAverage T (fun n => f i n * f j n) -
      integerAverage q (fun n => f i n * f j n)| ≤ E) :
    |integerAverage T (fun n => (∑ i, c i * f i n) ^ 2) -
      integerAverage q (fun n => (∑ i, c i * f i n) ^ 2)| ≤ (Fintype.card ι : ℝ) ^ 2 * E := by
  simp only [integerAverage_weight_sq, ← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ i, ∑ j, E := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro i _
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      calc
        _ ≤ 1 * 1 * |integerAverage T (fun n => f i n * f j n) -
            integerAverage q (fun n => f i n * f j n)| := by
          gcongr <;> apply hc
        _ ≤ E := by simpa using hpair i j
    _ = _ := by simp [pow_two, mul_assoc]

/-- The primes in the support of an assignment. -/
def assignmentPrimes {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) : Finset ℕ :=
  (assignmentSupport σ).image Subtype.val

/-- Every assigned prime divides `P`. -/
lemma assignmentPrimes_subset {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    assignmentPrimes σ ⊆ P.primeFactors := by
  intro p hp
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
  exact q.property

/-- A prime belongs to the assigned set exactly when its assignment is nonempty. -/
lemma mem_assignmentPrimes {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) (p : PrimeIndex P) :
    p.val ∈ assignmentPrimes σ ↔ (σ p).isSome := by
  classical
  simp [assignmentPrimes, assignmentSupport]

/-- Every element of the assigned prime set is prime. -/
lemma assignmentPrimes_prime {P k : ℕ} (σ : PrimeIndex P → Option (Fin k))
    {p : ℕ} (hp : p ∈ assignmentPrimes σ) : p.Prime :=
  (Nat.mem_primeFactors.mp (assignmentPrimes_subset σ hp)).1

/-- The product of the assigned primes equals the assignment product. -/
lemma assignmentPrimes_product {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    (∏ p ∈ assignmentPrimes σ, p) = assignmentProduct (fun p : PrimeIndex P => p.val) σ := by
  classical
  exact Finset.prod_image Subtype.val_injective.injOn

/-- The product of the assigned primes is positive. -/
lemma assignmentProduct_pos {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    0 < assignmentProduct (fun p : PrimeIndex P => p.val) σ := by
  exact Finset.prod_pos fun p _ => (Nat.prime_of_mem_primeFactors p.property).pos

/-- The product of the assigned primes divides `P`. -/
lemma assignmentProduct_dvd {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    assignmentProduct (fun p : PrimeIndex P => p.val) σ ∣ P := by
  rw [← assignmentPrimes_product]
  exact (Finset.prod_dvd_prod_of_subset _ _ _ (assignmentPrimes_subset σ)).trans
    (Nat.prod_primeFactors_dvd P)

/-- The prime factors of the assignment product are exactly the assigned primes. -/
lemma assignmentProduct_primeFactors {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    (assignmentProduct (fun p : PrimeIndex P => p.val) σ).primeFactors = assignmentPrimes σ := by
  rw [← assignmentPrimes_product]
  exact Nat.primeFactors_prod (fun p hp => assignmentPrimes_prime σ hp)

/-- The root selected by an assignment, with zero at unused primes. -/
def assignedRoot {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (σ : PrimeIndex P → Option (Fin k)) (p : PrimeIndex P) : Fin p.val :=
  match σ p with
  | none => ⟨0, (Nat.mem_primeFactors.mp p.property).1.pos⟩
  | some i => root p i

/-- The Chinese remainder theorem realizes all assigned roots in one residue. -/
lemma exists_assignment_residue {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (σ : PrimeIndex P → Option (Fin k)) :
    ∃ a : ℕ, a < assignmentProduct (fun p : PrimeIndex P => p.val) σ ∧
      ∀ p : PrimeIndex P, (σ p).isSome → a % p.val = (assignedRoot root σ p).val := by
  classical
  have hcop : (↑(assignmentSupport σ) : Set (PrimeIndex P)).Pairwise
      (fun p q => Nat.Coprime p.val q.val) := by
    intro p _ q _ hpq
    exact (Nat.coprime_primes (Nat.mem_primeFactors.mp p.property).1
      (Nat.mem_primeFactors.mp q.property).1).mpr (fun h => hpq (Subtype.ext h))
  let a := Nat.chineseRemainderOfFinset (fun p => (assignedRoot root σ p).val)
    (fun p : PrimeIndex P => p.val) (assignmentSupport σ)
    (fun p _ => (Nat.mem_primeFactors.mp p.property).1.ne_zero) hcop
  refine ⟨a.val, Nat.chineseRemainderOfFinset_lt_prod _ _ _ _, ?_⟩
  intro p hp
  have h := a.property p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt (assignedRoot root σ p).isLt] using h

/-- A residue encoding the roots selected by an assignment. -/
def assignmentCode {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (σ : PrimeIndex P → Option (Fin k)) : ℕ := Classical.choose (exists_assignment_residue root σ)

/-- The assignment code is smaller than its modulus. -/
lemma assignmentCode_lt {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (σ : PrimeIndex P → Option (Fin k)) :
    assignmentCode root σ < assignmentProduct (fun p : PrimeIndex P => p.val) σ :=
  (Classical.choose_spec (exists_assignment_residue root σ)).1

/-- The assignment code has the prescribed residue at each assigned prime. -/
lemma assignmentCode_mod {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (σ : PrimeIndex P → Option (Fin k)) (p : PrimeIndex P) (hp : (σ p).isSome) :
    assignmentCode root σ % p.val = (assignedRoot root σ p).val :=
  (Classical.choose_spec (exists_assignment_residue root σ)).2 p hp

/-- Distinct local roots make the modulus and residue code determine the assignment. -/
lemma assignmentCode_determines {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (hroot : ∀ p, Function.Injective (root p)) (σ τ : PrimeIndex P → Option (Fin k))
    (hn : assignmentProduct (fun p : PrimeIndex P => p.val) σ =
      assignmentProduct (fun p : PrimeIndex P => p.val) τ)
    (ha : assignmentCode root σ = assignmentCode root τ) : σ = τ := by
  funext p
  have hsupp : assignmentPrimes σ = assignmentPrimes τ := by
    rw [← assignmentProduct_primeFactors σ, hn, assignmentProduct_primeFactors]
  have hp : (σ p).isSome ↔ (τ p).isSome := by
    rw [← mem_assignmentPrimes, ← mem_assignmentPrimes, hsupp]
  cases hσ : σ p <;> cases hτ : τ p
  · rfl
  · simp [hσ, hτ] at hp
  · simp [hσ, hτ] at hp
  · congr 1
    apply hroot p
    apply Fin.ext
    have hs := assignmentCode_mod root σ p (by simp [hσ])
    have ht := assignmentCode_mod root τ p (by simp [hτ])
    simpa [assignedRoot, hσ, hτ] using
      hs.symm.trans ((congrArg (· % p.val) ha).trans ht)

/-- Encoding an assignment by its modulus and one CRT residue bounds its count. -/
theorem card_assignment_family_le {P k : ℕ} {ι : Type*} [Fintype ι]
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (σ : ι → PrimeIndex P → Option (Fin k)) (hσ : Function.Injective σ)
    {D : ℝ} (hD : 1 ≤ D)
    (hcut : ∀ i, (assignmentProduct (fun p : PrimeIndex P => p.val) (σ i) : ℝ) ≤ D) :
    (Fintype.card ι : ℝ) ≤ 4 * D ^ 2 := by
  let f (i : ι) : Fin (⌊D⌋₊ + 1) × Fin (⌊D⌋₊ + 1) :=
    (⟨assignmentProduct (fun p : PrimeIndex P => p.val) (σ i),
      Nat.lt_succ_of_le (Nat.le_floor (hcut i))⟩,
     ⟨assignmentCode root (σ i), (assignmentCode_lt root (σ i)).trans
      (Nat.lt_succ_of_le (Nat.le_floor (hcut i)))⟩)
  have hf : Function.Injective f := by
    intro i j hij
    apply hσ
    exact assignmentCode_determines root hroot (σ i) (σ j)
      (congrArg (fun x => x.1.val) hij) (congrArg (fun x => x.2.val) hij)
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_prod, Fintype.card_fin, ← pow_two] at hcard
  calc
    (Fintype.card ι : ℝ) ≤ ((⌊D⌋₊ : ℝ) + 1) ^ 2 := by
      exact_mod_cast hcard
    _ ≤ (2 * D) ^ 2 := by
      gcongr
      linarith [Nat.floor_le (show 0 ≤ D by linarith)]
    _ = 4 * D ^ 2 := by ring

/-- The truncated tuple region has at most `4 * D ^ 2` elements. -/
lemma tupleRegion_card_le {P k : ℕ} (hP : Squarefree P) {D : ℝ} (hD : 1 ≤ D)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p)) :
    (Fintype.card (tupleRegion P k D) : ℝ) ≤ 4 * D ^ 2 := by
  apply card_assignment_family_le root hroot
    (fun r : tupleRegion P k D => tupleAssignment r.val) (tupleAssignment_injective hP D) hD
  intro r
  rw [assignmentProduct_tupleAssignment hP r.val (Finset.mem_filter.mp r.property).2.1]
  exact (Finset.mem_filter.mp r.property).2.2

/-- Invariance modulo `m` implies invariance modulo every multiple of `m`. -/
lemma mod_invariant_of_dvd {m n : ℕ} (hmn : m ∣ n) (f : ℕ → ℝ)
    (hf : ∀ a, f (a % m) = f a) : ∀ a, f (a % n) = f a := by
  intro a
  rw [← hf (a % n), Nat.mod_mod_of_dvd a hmn, hf]

/-- Bound the second-moment averaging error using the periods and number of summands. -/
lemma integerAverage_bounded_periodic_weight {ι : Type*} [Fintype ι]
    {q T : ℕ} (hq : 0 < q) (hT : 0 < T) {D : ℝ} (hD : 0 ≤ D)
    (period : ι → ℕ) (hperiod_pos : ∀ i, 0 < period i) (hperiod_q : ∀ i, period i ∣ q)
    (hperiod_D : ∀ i, (period i : ℝ) ≤ D)
    (c : ι → ℝ) (hc : ∀ i, |c i| ≤ 1) (f : ι → ℕ → ℝ)
    (hf : ∀ i n, |f i n| ≤ 1) (hmod : ∀ i n, f i (n % period i) = f i n) :
    |integerAverage T (fun n => (∑ i, c i * f i n) ^ 2) -
      integerAverage q (fun n => (∑ i, c i * f i n) ^ 2)| ≤
        (Fintype.card ι : ℝ) ^ 2 * (D ^ 2 / T) := by
  apply integerAverage_weight_error q T c hc
  intro i j
  have hbound : (Nat.lcm (period i) (period j) : ℝ) ≤ D ^ 2 := by
    calc
      _ ≤ (period i : ℝ) * period j := by
        exact_mod_cast Nat.lcm_le_mul (hperiod_pos i) (hperiod_pos j)
      _ ≤ D * D := mul_le_mul (hperiod_D i) (hperiod_D j) (Nat.cast_nonneg _) hD
      _ = D ^ 2 := (pow_two D).symm
  refine (integerAverage_period_error
    (Nat.lcm_pos (hperiod_pos i) (hperiod_pos j)) hq hT
    (Nat.lcm_dvd (hperiod_q i) (hperiod_q j))
    (fun n => f i n * f j n) ?_ ?_).trans
      (div_le_div_of_nonneg_right hbound (Nat.cast_nonneg T))
  · intro n
    rw [mod_invariant_of_dvd (Nat.dvd_lcm_left _ _) (f i) (hmod i),
      mod_invariant_of_dvd (Nat.dvd_lcm_right _ _) (f j) (hmod j)]
  · intro n
    rw [abs_mul]
    exact mul_le_one₀ (hf i n) (abs_nonneg _) (hf j n)

/-- The residues of `n` modulo the prime divisors of `P`. -/
def residueVector (P n : ℕ) : (p : PrimeIndex P) → Fin p.val :=
  fun p => ⟨n % p.val, Nat.mod_lt n (Nat.mem_primeFactors.mp p.property).1.pos⟩

open scoped Fin.CommRing in
/-- The Chinese remainder theorem identifies a full-period average with a product average. -/
lemma integerAverage_residues {P : ℕ} (hP : Squarefree P)
    (f : ((p : PrimeIndex P) → Fin p.val) → ℝ) :
    integerAverage P (fun n => f (residueVector P n)) = Finset.expect Finset.univ f := by
  classical
  let : NeZero P := ⟨hP.ne_zero⟩
  let (p : PrimeIndex P) : NeZero p.val := ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
  have hcop : Pairwise (fun p q : PrimeIndex P => Nat.Coprime p.val q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.property)
      (Nat.prime_of_mem_primeFactors q.property)).mpr (fun h => hpq (Subtype.ext h))
  have hprod : (∏ p : PrimeIndex P, p.val) = P :=
    (Finset.prod_subtype (F := inferInstanceAs (Fintype (PrimeIndex P)))
      P.primeFactors (fun _ => Iff.rfl) id).symm.trans (Nat.prod_primeFactors_of_squarefree hP)
  let e : Fin P ≃+* ((p : PrimeIndex P) → Fin p.val) :=
    (ZMod.finEquiv P).trans <| (ZMod.ringEquivCongr hprod.symm).trans <|
      (ZMod.prodEquivPi (fun p : PrimeIndex P => p.val) hcop).trans <|
        RingEquiv.piCongrRight (fun p => (ZMod.finEquiv p.val).symm)
  have he (n : Fin P) : e n = residueVector P n.val := by
    calc
      e n = e (Nat.cast n.val : Fin P) := congrArg e (Fin.cast_val_eq_self n).symm
      _ = (Nat.cast n.val : (p : PrimeIndex P) → Fin p.val) := map_natCast e n.val
      _ = residueVector P n.val := rfl
  have h := Fintype.expect_equiv e.toEquiv
    (fun n : Fin P => f (residueVector P n.val)) f (fun n => congrArg f (he n).symm)
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fin] at h
  rw [Fin.sum_univ_eq_sum_range (fun n => f (residueVector P n)) P] at h
  simpa only [integerAverage, Fintype.expect_eq_sum_div_card] using h

/-- Every residue factor has absolute value at most one. -/
lemma abs_residueFactor_le_one {p : ℕ} (hp : 1 < p) (a t : Fin p) :
    |residueFactor a t| ≤ 1 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast Nat.succ_le_of_lt hp
  unfold residueFactor
  split_ifs
  · norm_num
  · rw [abs_of_nonneg (div_nonneg zero_le_one (by linarith))]
    exact (div_le_one (by linarith)).mpr (by linarith)

/-- Every unnormalized local basis value has absolute value at most one. -/
lemma abs_rawLocalBasis_le_one {p k : ℕ} (hp : 1 < p) (root : Fin k → Fin p)
    (i : Option (Fin k)) (t : Fin p) : |rawLocalBasis root i t| ≤ 1 := by
  cases i with
  | none => simp [rawLocalBasis]
  | some j => exact abs_residueFactor_le_one hp _ _

/-- A product of local basis values bounded by one is bounded by one. -/
lemma abs_productBasis_le_one {α : Type*} [Fintype α] {Ω J : α → Type*}
    (f : (p : α) → J p → Ω p → ℝ) (hf : ∀ p i t, |f p i t| ≤ 1)
    (σ : (p : α) → J p) (t : (p : α) → Ω p) : |productBasis f σ t| ≤ 1 := by
  rw [productBasis, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun p _ => hf p _ _)

/-- Coefficients bounded by one give tuple amplitudes bounded by one. -/
lemma tupleAmplitude_abs_le {P k : ℕ}
    (h : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1) (r : DivisorTuple P k) :
    |tupleAmplitude r| ≤ 1 := by
  rw [tupleAmplitude, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
    (fun i _ => h _ (r i).property)

/-- Every assigned prime divides the assignment product. -/
lemma prime_dvd_assignmentProduct {P k : ℕ} (σ : PrimeIndex P → Option (Fin k))
    (p : PrimeIndex P) (hp : (σ p).isSome) :
    p.val ∣ assignmentProduct (fun p : PrimeIndex P => p.val) σ := by
  exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)

/-- A product basis function depends only on the residue modulo its assignment product. -/
lemma basisProduct_mod_invariant {P k : ℕ}
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (hf : ∀ p t, f p none t = 1) (σ : PrimeIndex P → Option (Fin k)) (n : ℕ) :
    productBasis f σ (residueVector P (n % assignmentProduct (fun p : PrimeIndex P => p.val) σ)) =
      productBasis f σ (residueVector P n) := by
  unfold productBasis
  apply Finset.prod_congr rfl
  intro p _
  cases hσ : σ p with
  | none => simp only [hf]
  | some i =>
      congr 1
      exact Fin.ext (Nat.mod_mod_of_dvd n
        (prime_dvd_assignmentProduct σ p (by simp [hσ])))

/-- The truncated tuple sum formed from an arbitrary family of local basis functions. -/
def basisWeight (P k : ℕ) (D : ℝ)
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (t : (p : PrimeIndex P) → Fin p.val) : ℝ :=
  ∑ r : tupleRegion P k D, tupleAmplitude r.val * productBasis f (tupleAssignment r.val) t

/-- A D^6/T error is sufficient after taking κ = 1/8 in the final parameter choice. -/
theorem basisWeight_interval_error {P k T : ℕ} (hP : Squarefree P) (hT : 0 < T)
    {D : ℝ} (hD : 1 ≤ D)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (hcoeff : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1)
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (hfnone : ∀ p t, f p none t = 1) (hf : ∀ p i t, |f p i t| ≤ 1) :
    |integerAverage T (fun n => basisWeight P k D f (residueVector P n) ^ 2) -
      Finset.expect Finset.univ (fun t => basisWeight P k D f t ^ 2)| ≤ 16 * D ^ 6 / T := by
  rw [← integerAverage_residues hP (fun t => basisWeight P k D f t ^ 2)]
  have hcut (r : tupleRegion P k D) :
      (assignmentProduct (fun p : PrimeIndex P => p.val) (tupleAssignment r.val) : ℝ) ≤ D := by
    rw [assignmentProduct_tupleAssignment hP r.val (Finset.mem_filter.mp r.property).2.1]
    exact (Finset.mem_filter.mp r.property).2.2
  calc
    _ ≤ (Fintype.card (tupleRegion P k D) : ℝ) ^ 2 * (D ^ 2 / T) :=
      integerAverage_bounded_periodic_weight (Nat.pos_of_ne_zero hP.ne_zero) hT
        (zero_le_one.trans hD)
        (fun r : tupleRegion P k D =>
          assignmentProduct (fun p : PrimeIndex P => p.val) (tupleAssignment r.val))
        (fun r => assignmentProduct_pos _) (fun r => assignmentProduct_dvd _) hcut
        (fun r => tupleAmplitude r.val) (fun r => tupleAmplitude_abs_le hcoeff r.val)
        (fun r n => productBasis f (tupleAssignment r.val) (residueVector P n))
        (fun r n => abs_productBasis_le_one f hf _ _)
        (fun r n => basisProduct_mod_invariant f hfnone _ _)
    _ ≤ (4 * D ^ 2) ^ 2 * (D ^ 2 / T) := by
      gcongr
      exact tupleRegion_card_le hP hD root hroot
    _ = 16 * D ^ 6 / T := by ring

/-- The residue weight's second-moment averaging error is at most `16 * D ^ 6 / T`. -/
lemma residueWeight_interval_error {P k T : ℕ} (hP : Squarefree P) (hT : 0 < T)
    {D : ℝ} (hD : 1 ≤ D)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (hcoeff : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1) :
    |integerAverage T (fun n => residueWeight P k D root (residueVector P n) ^ 2) -
      Finset.expect Finset.univ (fun t => residueWeight P k D root t ^ 2)| ≤ 16 * D ^ 6 / T :=
  basisWeight_interval_error hP hT hD root hroot hcoeff (fun p => rawLocalBasis (root p))
    (fun _ _ => rfl) (fun p i t =>
      abs_rawLocalBasis_le_one (Nat.mem_primeFactors.mp p.property).1.one_lt _ i t)


/-- Every divisor tuple has positive product. -/
lemma tupleProduct_pos {P k : ℕ} (r : DivisorTuple P k) : 0 < tupleProduct r := by
  exact Finset.prod_pos fun i _ => Nat.pos_of_mem_divisors (r i).property

/-- Inserting a divisor multiplies the tuple product by that divisor. -/
lemma tupleProduct_insertNth {P k : ℕ} (i : Fin (k + 1)) (d : DivisorIndex P)
    (r : DivisorTuple P k) : tupleProduct (i.insertNth d r) = d.val * tupleProduct r := by
  unfold tupleProduct
  rw [Fin.prod_univ_succAbove _ i]
  simp

/-- Insertion preserves pairwise coprimality iff the new divisor is coprime to the rest. -/
lemma tuplePairwise_insertNth {P k : ℕ} (i : Fin (k + 1)) (d : DivisorIndex P)
    (r : DivisorTuple P k) :
    (∀ j l, j ≠ l →
      Nat.Coprime (i.insertNth (α := fun _ => DivisorIndex P) d r j).val
        (i.insertNth (α := fun _ => DivisorIndex P) d r l).val) ↔
      (∀ j l, j ≠ l → Nat.Coprime (r j).val (r l).val) ∧ d.val.Coprime (tupleProduct r) := by
  simp [Fin.forall_iff_succAbove i, tupleProduct, Nat.coprime_prod_right_iff,
    Nat.coprime_comm, forall_and, and_comm]

/-- Characterize truncated-region membership after inserting one divisor. -/
lemma tupleRegion_insertNth {P k : ℕ} (i : Fin (k + 1)) (d : DivisorIndex P)
    (r : DivisorTuple P k) (D : ℝ) :
    i.insertNth d r ∈ tupleRegion P (k + 1) D ↔
      r ∈ tupleRegion P k D ∧ (d.val : ℝ) ≤ D / tupleProduct r ∧
        d.val.Coprime (tupleProduct r) := by
  classical
  have hr : 0 < (tupleProduct r : ℝ) := by exact_mod_cast tupleProduct_pos r
  have hd : (1 : ℝ) ≤ d.val := by exact_mod_cast Nat.pos_of_mem_divisors d.property
  simp only [tupleRegion, Finset.mem_filter, Finset.mem_univ, true_and,
    tuplePairwise_insertNth, tupleProduct_insertNth, Nat.cast_mul, le_div_iff₀ hr]
  constructor
  · rintro ⟨⟨hpair, hcop⟩, hD⟩
    exact ⟨⟨hpair, (le_mul_of_one_le_left hr.le hd).trans hD⟩, hD, hcop⟩
  · rintro ⟨⟨hpair, _⟩, hD, hcop⟩
    exact ⟨⟨hpair, hcop⟩, hD⟩

/-- Split a truncated tuple sum by one coordinate. -/
lemma tupleSum_split {P k : ℕ} (i : Fin (k + 1)) (D : ℝ)
    (G : Fin (k + 1) → DivisorIndex P → ℝ) :
    (∑ r ∈ tupleRegion P (k + 1) D, ∏ j, G j (r j)) =
      ∑ r ∈ tupleRegion P k D,
        (∑ d : DivisorIndex P,
          if (d.val : ℝ) ≤ D / tupleProduct r ∧ d.val.Coprime (tupleProduct r) then G i d else 0) *
          ∏ j, G (i.succAbove j) (r j) := by
  classical
  let f (r : DivisorTuple P (k + 1)) : ℝ :=
    if r ∈ tupleRegion P (k + 1) D then ∏ j, G j (r j) else 0
  have h := Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => DivisorIndex P) i)
    (fun dr => f (i.insertNth dr.1 dr.2)) f (fun _ => rfl)
  rw [Fintype.sum_prod_type, Finset.sum_comm] at h
  simpa [f, tupleRegion_insertNth, Fin.prod_univ_succAbove _ i,
    ite_and, Finset.sum_mul, ite_mul] using h.symm

/-- The partial coefficient sum over small divisors coprime to `m`. -/
def coefficientRemainder (P m : ℕ) (D : ℝ) : ℝ :=
  ∑ d ∈ P.divisors.filter (fun d : ℕ => (d : ℝ) ≤ D / m ∧ d.Coprime m), coefficient P d / d.totient

/-- Express the coefficient remainder as a sum over divisor indices. -/
lemma coefficientRemainder_eq_sum (P m : ℕ) (D : ℝ) :
    coefficientRemainder P m D =
      ∑ d : DivisorIndex P,
        if (d.val : ℝ) ≤ D / m ∧ d.val.Coprime m then
          coefficient P d.val / d.val.totient else 0 := by
  rw [coefficientRemainder, Finset.sum_filter]
  exact (sum_divisorIndex P _).symm

/-- The local basis product for one divisor and tuple coordinate. -/
def coordinateBasis {P k : ℕ}
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (d : DivisorIndex P) (i : Fin k) (t : (p : PrimeIndex P) → Fin p.val) : ℝ :=
  ∏ p : PrimeIndex P, if p.val ∣ d.val then f p (some i) (t p) else 1

/-- Factor a tuple's product basis function over its coordinates. -/
lemma productBasis_tupleAssignment {P k : ℕ}
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (hf : ∀ p t, f p none t = 1) (r : DivisorTuple P k)
    (hr : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val)
    (t : (p : PrimeIndex P) → Fin p.val) :
    productBasis f (tupleAssignment r) t = ∏ i, coordinateBasis f (r i) i t := by
  classical
  unfold productBasis coordinateBasis
  rw [← tupleAssignment_prod r hr]
  apply Finset.prod_congr rfl
  intro p _
  cases tupleAssignment r p <;> simp [hf]

/-- Expand a basis weight as a sum of products over tuple coordinates. -/
lemma basisWeight_eq_tupleSum {P k : ℕ} (D : ℝ)
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (hf : ∀ p t, f p none t = 1) (t : (p : PrimeIndex P) → Fin p.val) :
    basisWeight P k D f t =
      ∑ r ∈ tupleRegion P k D, ∏ i, coefficient P (r i).val * coordinateBasis f (r i) i t := by
  rw [basisWeight, Finset.sum_coe_sort (tupleRegion P k D)
    (fun r => tupleAmplitude r * productBasis f (tupleAssignment r) t)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [productBasis_tupleAssignment f hf r (Finset.mem_filter.mp hr).2.1 t,
    tupleAmplitude, Finset.prod_mul_distrib]

/-- The local basis with coordinate `i` replaced by the constant `1 / (p - 1)`. -/
def replacedLocalBasis {p k : ℕ} (root : Fin k → Fin p) (i : Fin k)
    (j : Option (Fin k)) (t : Fin p) : ℝ :=
  match j with
  | none => 1
  | some j => if j = i then 1 / ((p : ℝ) - 1) else residueFactor (root j) t

/-- Replacing a coordinate reduces its divisor basis factor to the reciprocal totient. -/
lemma coordinateBasis_replaced {P k : ℕ} (hP : Squarefree P)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (i j : Fin k)
    (d : DivisorIndex P) (t : (p : PrimeIndex P) → Fin p.val) :
    coordinateBasis (fun p => replacedLocalBasis (root p) i) d j t =
      if j = i then 1 / (d.val.totient : ℝ) else
        coordinateBasis (fun p => rawLocalBasis (root p)) d j t := by
  classical
  by_cases h : j = i
  · simp only [coordinateBasis, replacedLocalBasis, if_pos h]
    rw [prod_primeIndex_dvd hP.ne_zero (Nat.dvd_of_mem_divisors d.property)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)),
      prod_primeFactors_inv_sub_one
        (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors d.property))]
  · simp [coordinateBasis, replacedLocalBasis, rawLocalBasis, h]

/-- The residue weight with one marked coordinate replaced by constants. -/
def replacedResidueWeight (P k : ℕ) (D : ℝ)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (i : Fin k)
    (t : (p : PrimeIndex P) → Fin p.val) : ℝ :=
  basisWeight P k D (fun p => replacedLocalBasis (root p) i) t

/-- Split the replaced weight into smaller tuples and coefficient remainders. -/
lemma replacedResidueWeight_split {P k : ℕ} (hP : Squarefree P) (D : ℝ)
    (root : (p : PrimeIndex P) → Fin (k + 1) → Fin p.val) (i : Fin (k + 1))
    (t : (p : PrimeIndex P) → Fin p.val) :
    replacedResidueWeight P (k + 1) D root i t =
      ∑ r ∈ tupleRegion P k D, coefficientRemainder P (tupleProduct r) D *
        ∏ j, coefficient P (r j).val *
          coordinateBasis (fun p => rawLocalBasis (fun j => root p (i.succAbove j))) (r j) j t := by
  classical
  rw [replacedResidueWeight, basisWeight_eq_tupleSum D _ (fun _ _ => rfl),
    tupleSum_split i D (fun j d => coefficient P d.val *
      coordinateBasis (fun p => replacedLocalBasis (root p) i) d j t)]
  simp_rw [coordinateBasis_replaced hP]
  simp [coefficientRemainder_eq_sum, coordinateBasis, rawLocalBasis, div_eq_mul_inv]

/-- Bound the coefficient mass of divisors sharing a prime with `m` by a prime sum. -/
lemma coefficient_noncoprime_le {P m : ℕ} (hP : 1 < P) (hsq : Squarefree P)
    (hm : m ∣ P) (hcoeff : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1) :
    (∑ d ∈ P.divisors.filter (fun d => ¬d.Coprime m), |coefficient P d| / d.totient) ≤
      ∑ p ∈ m.primeFactors, 4 / (p : ℝ) := by
  classical
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hsq.ne_zero (by simpa using hm)
  calc
    _ ≤ ∑ d ∈ P.divisors, ∑ p ∈ m.primeFactors,
        if p ∣ d then |coefficient P d| / d.totient else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro d _
      by_cases hdm : ¬d.Coprime m
      · rw [if_pos hdm]
        obtain ⟨p, hp, hpd, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hdm
        have h := Finset.single_le_sum
          (f := fun p => if p ∣ d then |coefficient P d| / d.totient else 0)
          (fun p _ => by split_ifs <;> positivity) (hp.mem_primeFactors hpm hm0)
        simpa only [if_pos hpd] using h
      · rw [if_neg hdm]
        positivity
    _ = ∑ p ∈ m.primeFactors,
        ∑ d ∈ P.divisors.filter (fun d => p ∣ d), |coefficient P d| / d.totient := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      have hpP := (Nat.dvd_of_mem_primeFactors hp).trans hm
      exact coefficient_prime_incidence hP hsq (Nat.prime_of_mem_primeFactors hp) hpP
        (hcoeff p (Nat.mem_divisors.mpr ⟨hpP, hsq.ne_zero⟩))

/-- A lower bound on prime factors controls their reciprocal sum using `log m`. -/
lemma sum_primeFactors_inv_le {P m : ℕ} (hP : Squarefree P) (hm : m ∣ P)
    {M : ℝ} (hM : 0 < M) (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ)) :
    (∑ p ∈ m.primeFactors, 4 / (p : ℝ)) ≤ 4 * Real.log m / (M * Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (m.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log m := by
    calc
      _ = ∑ p ∈ m.primeFactors, Real.log 2 := by simp
      _ ≤ ∑ p ∈ m.primeFactors, Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        exact Real.log_le_log (by norm_num)
          (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le)
      _ = Real.log m := by
        rw [← Real.log_prod (fun p hp =>
          Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero),
          ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree (hP.squarefree_of_dvd hm)]
  calc
    _ ≤ ∑ p ∈ m.primeFactors, 4 / M := by
      apply Finset.sum_le_sum
      intro p hp
      apply div_le_div_of_nonneg_left (by norm_num) hM
      exact hmin p ((Nat.prime_of_mem_primeFactors hp).mem_primeFactors
        ((Nat.dvd_of_mem_primeFactors hp).trans hm) hP.ne_zero)
    _ = (4 / M) * (m.primeFactors.card : ℝ) := by simp [mul_comm]
    _ ≤ (4 / M) * (Real.log m / Real.log 2) :=
      mul_le_mul_of_nonneg_left ((le_div_iff₀ hlog2).mpr hcard) (by positivity)
    _ = _ := by ring

/-- The coefficient remainder is nonnegative when its cutoff includes one. -/
lemma coefficientRemainder_nonneg {P m : ℕ} (hP : 1 < P) (hm : 0 < m)
    {D : ℝ} (hcut : (m : ℝ) ≤ D) : 0 ≤ coefficientRemainder P m D := by
  apply partial_cancellation_nonneg hP _ (Finset.filter_subset _ _)
  refine Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (by omega), ?_, by simp⟩
  exact (le_div_iff₀ (by exact_mod_cast hm : (0 : ℝ) < m)).mpr (by simpa using hcut)

/-- Rankin's bound for the absolute coefficient tail. -/
lemma coefficient_tail_le {P : ℕ} {v β : ℝ} (hv : 1 ≤ v) (hβ : 0 ≤ β) :
    (∑ d ∈ P.divisors.filter (fun d : ℕ => v < (d : ℝ)), |coefficient P d| / d.totient) ≤
      v ^ (-β) * coefficientAbsMoment P β := by
  classical
  have h1 : (1 : ℕ) ∉ P.divisors.filter (fun d : ℕ => v < (d : ℝ)) := by
    simp only [Finset.mem_filter, Nat.cast_one, not_and]
    exact fun _ => not_lt_of_ge hv
  simpa only [Finset.filter_erase, Finset.erase_eq_of_notMem h1,
    coefficientAbsMoment, div_mul_eq_mul_div] using
    moment_tail_le (P.divisors.erase 1) (fun d => |coefficient P d| / d.totient)
      (fun d => (d : ℝ)) v β (zero_lt_one.trans_le hv) hβ
      (fun d _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
      (fun d _ => Nat.cast_nonneg _)

/-- Bound the coefficient remainder by the discarded tail and noncoprime mass. -/
lemma coefficientRemainder_le_tail_add_overlap {P m : ℕ} (hP : 1 < P)
    (hm : 0 < m) {D : ℝ} (hcut : (m : ℝ) ≤ D) :
    coefficientRemainder P m D ≤
      (∑ d ∈ P.divisors.filter (fun d : ℕ => D / m < (d : ℝ)), |coefficient P d| / d.totient) +
      ∑ d ∈ P.divisors.filter (fun d => ¬d.Coprime m), |coefficient P d| / d.totient := by
  classical
  have h1 : (1 : ℕ) ∈ P.divisors.filter
      (fun d : ℕ => (d : ℝ) ≤ D / m ∧ d.Coprime m) := by
    refine Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (by omega), ?_, by simp⟩
    exact (le_div_iff₀ (by exact_mod_cast hm : (0 : ℝ) < m)).mpr (by simpa using hcut)
  rw [coefficientRemainder, partial_cancellation hP _ (Finset.filter_subset _ _) h1,
    ← Finset.filter_not]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d _
  have hnonneg : 0 ≤ |coefficient P d| / (d.totient : ℝ) := by positivity
  by_cases hd : (d : ℝ) ≤ D / m <;> by_cases hdm : d.Coprime m <;>
    simp [← not_le, hd, hdm, hnonneg]

/-- Bound the coefficient remainder by a power tail and an error from shared primes. -/
lemma coefficientRemainder_le {P m : ℕ} {β C D M : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hm : m ∣ P)
    (hcut : (m : ℝ) ≤ D) (hM : 0 < M)
    (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ)) :
    coefficientRemainder P m D ≤ C * ((m : ℝ) / D) ^ β +
      4 * Real.log D / (M * Real.log 2) := by
  have hm0 : 0 < m := Nat.pos_of_mem_divisors
    (Nat.mem_divisors.mpr ⟨hm, h.squarefree.ne_zero⟩)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  have hv : 1 ≤ D / m := (le_div_iff₀ hmR).mpr (by simpa using hcut)
  apply (coefficientRemainder_le_tail_add_overlap h.one_lt hm0 hcut).trans
  apply add_le_add
  · calc
      _ ≤ (D / m) ^ (-β) * coefficientAbsMoment P β := coefficient_tail_le hv hβ
      _ ≤ (D / m) ^ (-β) * C := mul_le_mul_of_nonneg_left
        (h.absMoment_le β hβ (by linarith)) (Real.rpow_nonneg (by positivity) _)
      _ = C * ((m : ℝ) / D) ^ β := by
        rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]
        exact mul_comm _ _
  · apply (coefficient_noncoprime_le h.one_lt h.squarefree hm h.abs_le_one).trans
    apply (sum_primeFactors_inv_le h.squarefree hm hM hmin).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.log_le_log hmR hcut) (by norm_num)) (by positivity)

/-- An exponential assignment row bound valid for every tuple length. -/
lemma assignment_row_bound_all {α : Type*} [Fintype α]
    (size : α → ℕ) {k : ℕ} (σ : α → Option (Fin k))
    {M D : ℝ} (hM : 1 < M) (hsize : ∀ p, M ≤ (size p : ℝ))
    (hcut : (assignmentProduct size σ : ℝ) ≤ D) :
    (∏ p, localRow (size p) k (σ p)) ≤
      Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) := by
  cases k with
  | zero =>
      have hσ (p : α) : σ p = none := Subsingleton.elim _ _
      simp [hσ, localRow]
  | succ k =>
      exact assignment_row_bound size (Nat.succ_pos k) σ hM hsize hcut

/-- The residue weight with an additional weight on each divisor tuple. -/
def weightedResidueWeight (P k : ℕ) (D : ℝ)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (b : DivisorTuple P k → ℝ)
    (t : (p : PrimeIndex P) → Fin p.val) : ℝ :=
  ∑ r : tupleRegion P k D, b r.val * tupleAmplitude r.val *
    productBasis (fun p => rawLocalBasis (root p)) (tupleAssignment r.val) t

/-- Expand the weighted residue sum as a product over tuple coordinates. -/
lemma weightedResidueWeight_eq_sum {P k : ℕ} (D : ℝ)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (b : DivisorTuple P k → ℝ)
    (t : (p : PrimeIndex P) → Fin p.val) :
    weightedResidueWeight P k D root b t =
      ∑ r ∈ tupleRegion P k D, b r *
        ∏ i, coefficient P (r i).val *
          coordinateBasis (fun p => rawLocalBasis (root p)) (r i) i t := by
  rw [weightedResidueWeight, Finset.sum_coe_sort (tupleRegion P k D)
    (fun r => b r * tupleAmplitude r *
      productBasis (fun p => rawLocalBasis (root p)) (tupleAssignment r) t)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [productBasis_tupleAssignment _ (fun _ _ => rfl) r (Finset.mem_filter.mp hr).2.1 t,
    tupleAmplitude, Finset.prod_mul_distrib, mul_assoc]

/-- Bound the weighted second moment by the Gram factor times its diagonal mass. -/
lemma weightedResidueWeight_second_moment_le {P k : ℕ} (hP : Squarefree P)
    {D M : ℝ} (hM : 1 < M) (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ))
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (b : DivisorTuple P k → ℝ) :
    Finset.expect Finset.univ (fun t => weightedResidueWeight P k D root b t ^ 2) ≤
      Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) *
        ∑ r ∈ tupleRegion P k D, tupleMass r * b r ^ 2 := by
  classical
  have hsize (p : PrimeIndex P) : 1 < p.val :=
    (Nat.prime_of_mem_primeFactors p.property).one_lt
  have hmass :
      (∑ r : tupleRegion P k D, (b r.val * tupleNormalizedCoefficient r.val) ^ 2) =
        ∑ r ∈ tupleRegion P k D, tupleMass r * b r ^ 2 := by
    rw [← Finset.sum_attach (tupleRegion P k D) (fun r => tupleMass r * b r ^ 2)]
    apply Finset.sum_congr rfl
    intro r _
    rw [mul_pow, tupleNormalizedCoefficient_sq hP r.val
      (Finset.mem_filter.mp r.property).2.1, mul_comm]
  have hweight (t : (p : PrimeIndex P) → Fin p.val) :
      (∑ r : tupleRegion P k D, (b r.val * tupleNormalizedCoefficient r.val) *
        productBasis (fun p => localBasis (root p)) (tupleAssignment r.val) t) =
      weightedResidueWeight P k D root b t := by
    simp only [tupleNormalizedCoefficient, mul_assoc,
      assignmentNormalizer_mul_basis _ hsize, weightedResidueWeight]
  have hbound (r : tupleRegion P k D) :
      (∏ p : PrimeIndex P, localRow p.val k (tupleAssignment r.val p)) - 1 ≤
        Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) - 1 := by
    apply sub_le_sub_right _ 1
    apply assignment_row_bound_all (fun p : PrimeIndex P => p.val)
      (tupleAssignment r.val) hM (fun p => hmin p.val p.property)
    rw [assignmentProduct_tupleAssignment hP r.val (Finset.mem_filter.mp r.property).2.1]
    exact (Finset.mem_filter.mp r.property).2.2
  have h := indexed_product_second_moment (fun p : PrimeIndex P => p.val) hsize root hroot
    (fun r : tupleRegion P k D => tupleAssignment r.val) (tupleAssignment_injective hP D)
    (fun r => b r.val * tupleNormalizedCoefficient r.val) _ hbound
  simp only [hweight, hmass] at h
  linarith [(abs_le.mp h).2]

/-- A replaced weight is a weight on smaller tuples with coefficient-remainder factors. -/
lemma replacedResidueWeight_eq_weighted {P k : ℕ} (hP : Squarefree P) (D : ℝ)
    (root : (p : PrimeIndex P) → Fin (k + 1) → Fin p.val) (i : Fin (k + 1))
    (t : (p : PrimeIndex P) → Fin p.val) :
    replacedResidueWeight P (k + 1) D root i t =
      weightedResidueWeight P k D (fun p j => root p (i.succAbove j))
        (fun r => coefficientRemainder P (tupleProduct r) D) t := by
  rw [replacedResidueWeight_split hP, weightedResidueWeight_eq_sum]

/-- Control weighted diagonal mass by tilted and zero coefficient moments. -/
lemma weighted_diagonal_le {P k : ℕ} {D a b γ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (v : DivisorTuple P k → ℝ)
    (hv : ∀ r ∈ tupleRegion P k D, v r ^ 2 ≤ a * (tupleProduct r : ℝ) ^ γ + b) :
    (∑ r ∈ tupleRegion P k D, tupleMass r * v r ^ 2) ≤
      a * coefficientMoment P γ ^ k + b * coefficientMoment P 0 ^ k := by
  classical
  calc
    _ ≤ ∑ r ∈ tupleRegion P k D,
        tupleMass r * (a * (tupleProduct r : ℝ) ^ γ + b) := by
      exact Finset.sum_le_sum fun r hr =>
        mul_le_mul_of_nonneg_left (hv r hr) (tupleMass_nonneg r)
    _ ≤ ∑ r : DivisorTuple P k,
        tupleMass r * (a * (tupleProduct r : ℝ) ^ γ + b) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro r _ _
      exact mul_nonneg (tupleMass_nonneg r)
        (add_nonneg (mul_nonneg ha (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hb)
    _ = a * (∑ r : DivisorTuple P k, tupleMass r * (tupleProduct r : ℝ) ^ γ) +
        b * (∑ r : DivisorTuple P k, tupleMass r) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by rw [sum_tupleMass_mul_rpow, sum_tupleMass]

/-- Bound the squared coefficient remainder by its tail and overlap contributions. -/
lemma coefficientRemainder_square_le {P m : ℕ} {β C D M : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hm : m ∣ P)
    (hcut : (m : ℝ) ≤ D) (hM : 0 < M)
    (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ)) :
    coefficientRemainder P m D ^ 2 ≤
      (2 * C ^ 2 * D ^ (-(2 * β))) * (m : ℝ) ^ (2 * β) +
        2 * (4 * Real.log D / (M * Real.log 2)) ^ 2 := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero h.squarefree.ne_zero hm)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hD : 0 < D := hm'.trans_le hcut
  have hs := pow_le_pow_left₀ (coefficientRemainder_nonneg h.one_lt hm0 hcut)
    (coefficientRemainder_le h hβ hm hcut hM hmin) 2
  have hp : (((m : ℝ) / D) ^ β) ^ 2 = D ^ (-(2 * β)) * (m : ℝ) ^ (2 * β) := by
    rw [← Real.rpow_mul_natCast (div_nonneg hm'.le hD.le), Real.rpow_neg hD.le,
      Real.div_rpow hm'.le hD.le]
    norm_num
    rw [mul_comm β 2]
    ring
  have hsq := sq_nonneg (C * ((m : ℝ) / D) ^ β - 4 * Real.log D / (M * Real.log 2))
  nlinarith [hp]

/-- Bound a replaced weight's second moment using tilted and zero coefficient moments. -/
lemma replacedResidueWeight_second_moment_le {P k : ℕ} {β C D M : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hD : 0 < D)
    (hM : 1 < M) (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ))
    (root : (p : PrimeIndex P) → Fin (k + 1) → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (i : Fin (k + 1)) :
    Finset.expect Finset.univ (fun t => replacedResidueWeight P (k + 1) D root i t ^ 2) ≤
      Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) *
        ((2 * C ^ 2 * D ^ (-(2 * β))) * coefficientMoment P (2 * β) ^ k +
          2 * (4 * Real.log D / (M * Real.log 2)) ^ 2 * coefficientMoment P 0 ^ k) := by
  classical
  simp_rw [replacedResidueWeight_eq_weighted h.squarefree]
  apply (weightedResidueWeight_second_moment_le h.squarefree hM hmin
    (fun p j => root p (i.succAbove j))
    (fun p a b hab => by simpa using hroot p hab)
    (fun r => coefficientRemainder P (tupleProduct r) D)).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  apply weighted_diagonal_le (by positivity) (by positivity)
  intro r hr
  obtain ⟨hpair, hcut⟩ := (Finset.mem_filter.mp hr).2
  exact coefficientRemainder_square_le h hβ (tupleProduct_dvd r hpair) hcut
    (zero_lt_one.trans hM) hmin

/-- Avoiding one coordinate's roots makes the original and replaced weights equal. -/
lemma residueWeight_eq_replaced_of_uncovered {P k : ℕ} (D : ℝ)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (i : Fin k)
    (t : (p : PrimeIndex P) → Fin p.val) (hi : ∀ p, t p ≠ root p i) :
    residueWeight P k D root t = replacedResidueWeight P k D root i t := by
  have hlocal (p : PrimeIndex P) (j : Option (Fin k)) :
      rawLocalBasis (root p) j (t p) = replacedLocalBasis (root p) i j (t p) := by
    cases j with
    | none => rfl
    | some j =>
        by_cases h : j = i <;>
          simp [rawLocalBasis, replacedLocalBasis, h, residueFactor, hi]
  simp only [residueWeight, replacedResidueWeight, basisWeight, productBasis, hlocal]

/-- Every replaced local basis value has absolute value at most one. -/
lemma abs_replacedLocalBasis_le_one {p k : ℕ} (hp : 1 < p)
    (root : Fin k → Fin p) (i : Fin k) (j : Option (Fin k)) (t : Fin p) :
    |replacedLocalBasis root i j t| ≤ 1 := by
  cases j with
  | none => simp [replacedLocalBasis]
  | some j =>
      simp only [replacedLocalBasis]
      split_ifs
      · have hp' : (2 : ℝ) ≤ p := by exact_mod_cast Nat.succ_le_of_lt hp
        rw [abs_of_nonneg (div_nonneg zero_le_one (by linarith))]
        exact (div_le_one (by linarith)).mpr (by linarith)
      · exact abs_residueFactor_le_one hp _ _

/-- The replaced weight's second-moment averaging error is at most `16 * D ^ 6 / T`. -/
lemma replacedResidueWeight_interval_error {P k T : ℕ} (hP : Squarefree P) (hT : 0 < T)
    {D : ℝ} (hD : 1 ≤ D)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (hcoeff : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1) (i : Fin k) :
    |integerAverage T (fun n => replacedResidueWeight P k D root i (residueVector P n) ^ 2) -
      Finset.expect Finset.univ (fun t => replacedResidueWeight P k D root i t ^ 2)| ≤
        16 * D ^ 6 / T :=
  basisWeight_interval_error hP hT hD root hroot hcoeff (fun p => replacedLocalBasis (root p) i)
    (fun _ _ => rfl)
    (fun p j t => abs_replacedLocalBasis_le_one
      (Nat.mem_primeFactors.mp p.property).1.one_lt _ i j t)

/-- A second-moment gap yields an integer meeting a root in every coordinate. -/
lemma exists_simultaneous_root_of_moments {P k T : ℕ} {D L U : ℝ}
    (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (hlower : L ≤ integerAverage T (fun n => residueWeight P k D root (residueVector P n) ^ 2))
    (hupper : ∀ i,
      integerAverage T (fun n => replacedResidueWeight P k D root i (residueVector P n) ^ 2) ≤ U)
    (hgap : (k : ℝ) * U < L) :
    ∃ n < T, ∀ i : Fin k, ∃ p : PrimeIndex P, residueVector P n p = root p i := by
  classical
  by_contra! h
  have hpointwise (n : ℕ) (hn : n ∈ Finset.range T) :
      residueWeight P k D root (residueVector P n) ^ 2 ≤
        ∑ i, replacedResidueWeight P k D root i (residueVector P n) ^ 2 := by
    obtain ⟨i, hi⟩ := h n (Finset.mem_range.mp hn)
    rw [residueWeight_eq_replaced_of_uncovered D root i (residueVector P n) hi]
    apply Finset.single_le_sum ?_ (Finset.mem_univ i)
    intro j _
    exact sq_nonneg _
  apply (not_le_of_gt hgap)
  calc
    L ≤ integerAverage T (fun n => residueWeight P k D root (residueVector P n) ^ 2) := hlower
    _ ≤ ∑ i, integerAverage T
        (fun n => replacedResidueWeight P k D root i (residueVector P n) ^ 2) := by
      unfold integerAverage
      rw [← Finset.sum_div, Finset.sum_comm]
      exact div_le_div_of_nonneg_right (Finset.sum_le_sum hpointwise) (Nat.cast_nonneg T)
    _ ≤ ∑ _i : Fin k, U := Finset.sum_le_sum (fun i _ => hupper i)
    _ = (k : ℝ) * U := by simp

/-- Any coefficient-estimate constant is at least one. -/
lemma CoefficientEstimates.one_le_constant {P : ℕ} {β C : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) : 1 ≤ C := by
  simpa [coefficientAbsMoment_zero h.one_lt] using h.absMoment_le 0 le_rfl (by positivity)

/-- The exponential factor controlling Gram matrix row sums. -/
def gramBound (k : ℕ) (M D : ℝ) : ℝ :=
  Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M))

/-- A normalized second-moment bound for a replaced residue weight. -/
def uncoveredBound (k : ℕ) (β C M D : ℝ) : ℝ :=
  gramBound k M D * (2 * C ^ 2 * D ^ (-(2 * β)) * Real.exp ((k : ℝ) * C * (2 * β)) +
    2 * (4 * Real.log D / (M * Real.log 2)) ^ 2)

/-- The normalized uncovered bound is nonnegative. -/
lemma uncoveredBound_nonneg (k : ℕ) (β C M : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ uncoveredBound k β C M D := by unfold uncoveredBound gramBound; positivity

/-- Bound a replaced weight's second moment by `uncoveredBound` times the zero moment. -/
lemma replacedResidueWeight_normalized_bound {P k : ℕ} {β C D M : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hD : 0 < D)
    (hM : 1 < M) (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ))
    (root : (p : PrimeIndex P) → Fin (k + 1) → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (i : Fin (k + 1)) :
    Finset.expect Finset.univ (fun t => replacedResidueWeight P (k + 1) D root i t ^ 2) ≤
      uncoveredBound k β C M D * coefficientMoment P 0 ^ k := by
  have hγ : 0 ≤ 2 * β := mul_nonneg (by norm_num) hβ
  have hmoment := coefficientMoment_pow_le h.one_lt
    (zero_le_one.trans (h.one_le_constant hβ)) hγ
    (h.moment_control (2 * β) hγ le_rfl) k
  apply (replacedResidueWeight_second_moment_le h hβ hD hM hmin root hroot i).trans
  unfold uncoveredBound gramBound
  calc
    _ ≤ Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) *
        ((2 * C ^ 2 * D ^ (-(2 * β))) *
            (coefficientMoment P 0 ^ k * Real.exp ((k : ℝ) * C * (2 * β))) +
          2 * (4 * Real.log D / (M * Real.log 2)) ^ 2 * coefficientMoment P 0 ^ k) := by
      gcongr
    _ = _ := by ring

/-- The normalized diagonal mass loses only a power tail and prime collisions. -/
lemma diagonalMass_normalized_lower {P M k : ℕ} {β C D : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hD : 0 < D)
    (hM : 0 < M) (hmin : ∀ p ∈ P.primeFactors, M < p) :
    (1 - (D ^ (-β) * Real.exp ((k : ℝ) * C * β) + 16 * (k : ℝ) ^ 2 / M)) *
      coefficientMoment P 0 ^ k ≤ diagonalMass P k D := by
  have hmoment := coefficientMoment_pow_le h.one_lt
    (zero_le_one.trans (h.one_le_constant hβ)) hβ
    (h.moment_control β hβ (by linarith)) k
  have hloss := diagonalMass_tail_collision (k := k) h hM hmin hD hβ
  have htail := mul_le_mul_of_nonneg_left hmoment (Real.rpow_nonneg hD.le (-β))
  nlinarith

/-- The finite weighted sieve, with every numerical loss displayed explicitly. -/
theorem finite_simultaneous_roots {P M k T : ℕ} {β C D : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hD : 1 ≤ D)
    (hM : 1 < M) (hT : 0 < T) (hmin : ∀ p ∈ P.primeFactors, M < p)
    (root : (p : PrimeIndex P) → Fin (k + 1) → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (htail : D ^ (-β) * Real.exp (((k + 1 : ℕ) : ℝ) * C * β) +
      16 * (((k + 1 : ℕ) : ℝ)) ^ 2 / M ≤ 1 / 2)
    (hgram : gramBound (k + 1) M D ≤ 5 / 4)
    (herr : 16 * D ^ 6 / T ≤ 1 / 8)
    (hbad : (((k + 1 : ℕ) : ℝ)) * (uncoveredBound k β C M D + 16 * D ^ 6 / T) < 1 / 4) :
    ∃ n < T, ∀ i : Fin (k + 1), ∃ p : PrimeIndex P, residueVector P n p = root p i := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hM' : (1 : ℝ) < M := by exact_mod_cast hM
  have hmin' : ∀ p ∈ P.primeFactors, (M : ℝ) ≤ p := by
    intro p hp
    exact_mod_cast (hmin p hp).le
  let A := coefficientMoment P 0 ^ (k + 1)
  have hbase := coefficientMoment_ge_one h.squarefree.ne_zero 0
  have hA : 1 ≤ A := one_le_pow₀ hbase
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hdiag : A / 2 ≤ diagonalMass P (k + 1) D := by
    have hlower := diagonalMass_normalized_lower (k := k + 1) h hβ hD0 (by omega) hmin
    change (1 - _) * A ≤ _ at hlower
    nlinarith only [hlower, mul_le_mul_of_nonneg_right htail hA0.le]
  apply exists_simultaneous_root_of_moments (D := D) root
    (L := A / 4) (U := (uncoveredBound k β C M D + 16 * D ^ 6 / T) * A)
  · have hmoment := (abs_le.mp (residueWeight_second_moment_bound (D := D) h.squarefree
      (Nat.succ_pos k) hM' hmin' root hroot)).1
    have herror := (abs_le.mp
      (residueWeight_interval_error h.squarefree hT hD root hroot h.abs_le_one)).1
    have hgram' := mul_le_mul_of_nonneg_right hgram (diagonalMass_nonneg P (k + 1) D)
    unfold gramBound at hgram'
    nlinarith only [hmoment, herror, hgram', hdiag, herr, hA]
  · intro i
    have hscale : coefficientMoment P 0 ^ k ≤ A := by
      simpa only [A, pow_succ] using
        le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans hbase) k) hbase
    have hmoment := (replacedResidueWeight_normalized_bound h hβ hD0 hM' hmin' root hroot i).trans
      (mul_le_mul_of_nonneg_left hscale (uncoveredBound_nonneg k β C M hD0.le))
    have herror := (abs_le.mp
      (replacedResidueWeight_interval_error h.squarefree hT hD root hroot h.abs_le_one i)).2
    have he0 : 0 ≤ 16 * D ^ 6 / (T : ℝ) := by positivity
    nlinarith only [hmoment, herror, mul_le_mul_of_nonneg_left hA he0]
  · nlinarith only [mul_lt_mul_of_pos_right hbad hA0]

/-- The divisor-product cutoff `exp (x / 8)`. -/
def sieveD (x : ℝ) : ℝ := Real.exp (x / 8)

/-- The averaging interval length, given by the integer part of `exp x`. -/
def sieveT (x : ℝ) : ℕ := ⌊Real.exp x⌋₊

/-- Rewrite `exp (-n * log x)` as `1 / x ^ n`. -/
lemma exp_neg_nat_mul_log {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.exp (-(n : ℝ) * Real.log x) = 1 / x ^ n := by
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hx, one_div]

/-- The truncation tail is at most `1 / x ^ 3` under the sieve size bounds. -/
lemma truncated_exponential_le {n : ℕ} {x β C : ℝ} (hx : 0 < x) (hβ : 0 ≤ β)
    (hsize : (n : ℝ) * C ≤ x / 16) (hlog : 48 * Real.log x ≤ x * β) :
    sieveD x ^ (-β) * Real.exp ((n : ℝ) * C * β) ≤ 1 / x ^ 3 := by
  rw [sieveD, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add,
    ← exp_neg_nat_mul_log hx 3]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hsize hβ]

/-- The truncation tail with doubled exponent is at most `1 / x ^ 6`. -/
lemma truncated_double_exponential_le {n : ℕ} {x β C : ℝ} (hx : 0 < x) (hβ : 0 ≤ β)
    (hsize : (n : ℝ) * C ≤ x / 16) (hlog : 48 * Real.log x ≤ x * β) :
    sieveD x ^ (-(2 * β)) * Real.exp ((n : ℝ) * C * (2 * β)) ≤ 1 / x ^ 6 := by
  rw [sieveD, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add,
    ← exp_neg_nat_mul_log hx 6]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hsize hβ]

/-- Bound the Gram factor by `exp (1 / x ^ 2)`. -/
lemma gramBound_le_simple {n : ℕ} {M x : ℝ} (hx : 1 ≤ x) (hn : (n : ℝ) ≤ x)
    (hM : x ^ 4 ≤ M - 1) (hlog : 1 ≤ Real.log M) :
    gramBound n M (sieveD x) ≤ Real.exp (1 / x ^ 2) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M - 1 := (pow_pos hx0 4).trans_le hM
  unfold gramBound sieveD
  rw [Real.log_exp]
  apply Real.exp_le_exp.mpr
  calc
    (n : ℝ) * (x / 8) / ((M - 1) * Real.log M) ≤ x * x / (x ^ 4 * 1) := by
      gcongr
      linarith
    _ = 1 / x ^ 2 := by field_simp

/-- The collision contribution is at most `16 / x ^ 2`. -/
lemma collisionBound_le_simple {n : ℕ} {M x : ℝ} (hx : 0 < x)
    (hn : (n : ℝ) ≤ x) (hM : x ^ 4 ≤ M) :
    16 * (n : ℝ) ^ 2 / M ≤ 16 / x ^ 2 := by
  calc
    16 * (n : ℝ) ^ 2 / M ≤ 16 * x ^ 2 / x ^ 4 := by gcongr
    _ = 16 / x ^ 2 := by field_simp

/-- The overlap contribution is at most `1 / (log 2 * x ^ 3)`. -/
lemma overlapBound_le_simple {M x : ℝ} (hx : 0 < x) (hM : x ^ 4 ≤ M) :
    4 * Real.log (sieveD x) / (M * Real.log 2) ≤ 1 / (Real.log 2 * x ^ 3) := by
  rw [sieveD, Real.log_exp]
  calc
    4 * (x / 8) / (M * Real.log 2) ≤ x / (x ^ 4 * Real.log 2) := by
      gcongr
      linarith
    _ = 1 / (Real.log 2 * x ^ 3) := by field_simp

/-- Bound the normalized uncovered contribution by an explicit multiple of `1 / x ^ 6`. -/
lemma uncoveredBound_le_simple {n : ℕ} {M x β C : ℝ} (hx : 1 ≤ x)
    (hβ : 0 ≤ β) (hn : (n : ℝ) ≤ x) (hsize : (n : ℝ) * C ≤ x / 16)
    (hlog : 48 * Real.log x ≤ x * β) (hM : x ^ 4 ≤ M - 1) (hlogM : 1 ≤ Real.log M)
    (hgram : Real.exp (1 / x ^ 2) ≤ 5 / 4) :
    uncoveredBound n β C M (sieveD x) ≤ (5 / 4) * (2 * C ^ 2 + 2 / (Real.log 2) ^ 2) / x ^ 6 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM' : x ^ 4 ≤ M := hM.trans (sub_le_self _ zero_le_one)
  have hM0 : 0 < M := (pow_pos hx0 4).trans_le hM'
  have hgram' := (gramBound_le_simple hx hn hM hlogM).trans hgram
  have hexp := truncated_double_exponential_le hx0 hβ hsize hlog
  have hover := overlapBound_le_simple hx0 hM'
  have hover0 : 0 ≤ 4 * Real.log (sieveD x) / (M * Real.log 2) := by
    rw [sieveD, Real.log_exp]
    positivity
  calc
    uncoveredBound n β C M (sieveD x) ≤
        (5 / 4) * (2 * C ^ 2 * (1 / x ^ 6) +
          2 * (1 / (Real.log 2 * x ^ 3)) ^ 2) := by
      unfold uncoveredBound
      rw [mul_assoc (2 * C ^ 2)]
      gcongr
      unfold sieveD
      positivity
    _ = _ := by ring

/-- For `x ≥ 2`, the lower sieve cutoff exceeds `x ^ 4` by at least one. -/
lemma sieveZ_lower {x : ℝ} (hx : 2 ≤ x) : x ^ 4 ≤ (sieveZ x : ℝ) - 1 := by
  have hx2 : 4 ≤ x ^ 2 := by nlinarith
  have hx4 : 16 ≤ x ^ 4 := by nlinarith [sq_nonneg (x ^ 2 - 4)]
  have hx6 : 4 * x ^ 4 ≤ x ^ 6 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx2) (sq_nonneg (x ^ 2))]
  unfold sieveZ
  nlinarith [Nat.lt_floor_add_one (x ^ 6)]

/-- The integer averaging length is at least half of `exp x`. -/
lemma sieveT_lower {x : ℝ} (hx : 2 ≤ x) : Real.exp x / 2 ≤ (sieveT x : ℝ) := by
  unfold sieveT
  linarith [Real.add_one_le_exp x, Nat.lt_floor_add_one (Real.exp x)]

/-- The interval averaging error is at most `32 / x ^ 3`. -/
lemma intervalError_le_simple {x : ℝ} (hx : 2 ≤ x) (hlog : 12 * Real.log x ≤ x) :
    16 * sieveD x ^ 6 / sieveT x ≤ 32 / x ^ 3 := by
  have hx0 : 0 < x := by linarith
  calc
    16 * sieveD x ^ 6 / sieveT x ≤ 16 * sieveD x ^ 6 / (Real.exp x / 2) := by
      gcongr
      exact sieveT_lower hx
    _ = 32 * Real.exp (-x / 4) := by
      rw [sieveD, ← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      calc
        _ = 32 * (Real.exp (6 * (x / 8)) / Real.exp x) := by ring
        _ = _ := by rw [← Real.exp_sub]; congr 1; congr 1; ring
    _ ≤ 32 * Real.exp (-(3 : ℝ) * Real.log x) := by
      gcongr
      linarith
    _ = 32 / x ^ 3 := by
      have he : Real.exp (-(3 : ℝ) * Real.log x) = 1 / x ^ 3 := by
        simpa only [Nat.cast_ofNat] using exp_neg_nat_mul_log hx0 3
      rw [he]
      ring

/-- The sieve tilt eventually satisfies `48 * log x ≤ x * sieveBeta x`. -/
lemma eventually_sieve_beta_scale : ∀ᶠ x : ℝ in Filter.atTop,
    48 * Real.log x ≤ x * sieveBeta x := by
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 3] with x hx hlog
  have hpow : (48 : ℝ) ≤ (Real.log x) ^ 4 := by
    calc
      (48 : ℝ) ≤ 3 ^ 4 := by norm_num
      _ ≤ (Real.log x) ^ 4 := pow_le_pow_left₀ (by norm_num) hlog 4
  calc
    48 * Real.log x ≤ (Real.log x) ^ 4 * Real.log x :=
      mul_le_mul_of_nonneg_right hpow (by linarith)
    _ = x * sieveBeta x := by
      unfold sieveBeta sieveUpperLog
      field_simp

/-- The numerical sieve error bounds hold for all sufficiently large `x`. -/
lemma eventually_simple_sieve_bounds (C : ℝ) : ∀ᶠ x : ℝ in Filter.atTop,
    Real.exp (1 / x ^ 2) ≤ 5 / 4 ∧
    1 / x ^ 3 + 16 / x ^ 2 ≤ 1 / 2 ∧
    32 / x ^ 3 ≤ 1 / 8 ∧
    ((5 / 4) * (2 * C ^ 2 + 2 / (Real.log 2) ^ 2)) / x ^ 5 + 32 / x ^ 2 < 1 / 4 := by
  have h (n : ℕ) (hn : n ≠ 0) :
      Filter.Tendsto (fun x : ℝ => 1 / x ^ n) Filter.atTop (nhds 0) := by
    simpa [one_div, hn] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).pow n
  have h₂ := h 2 (by decide)
  have h₃ := h 3 (by decide)
  have h₅ := h 5 (by decide)
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp h₂
  have htail := h₃.add (h₂.const_mul 16)
  have herr := h₃.const_mul 32
  have hbad := (h₅.const_mul ((5 / 4) * (2 * C ^ 2 + 2 / (Real.log 2) ^ 2))).add
    (h₂.const_mul 32)
  filter_upwards [hexp.eventually (gt_mem_nhds (by norm_num : Real.exp 0 < 5 / 4)),
    htail.eventually (gt_mem_nhds (by norm_num : 0 + 16 * 0 < (1 : ℝ) / 2)),
    herr.eventually (gt_mem_nhds (by norm_num : 32 * 0 < (1 : ℝ) / 8)),
    hbad.eventually (gt_mem_nhds (by simp :
      ((5 / 4) * (2 * C ^ 2 + 2 / (Real.log 2) ^ 2)) * 0 + 32 * 0 < (1 : ℝ) / 4))]
    with x hexp htail herr hbad
  exact ⟨hexp.le, by simpa only [mul_one_div] using htail.le,
    by simpa only [mul_one_div] using herr.le,
    by simpa only [mul_one_div] using hbad⟩

/-- The density threshold for simultaneously hitting all root families. -/
def sieveDelta : ℝ := 1 / (64 * weightConstant)

/-- The simultaneous-root density threshold is positive. -/
lemma sieveDelta_pos : 0 < sieveDelta := by
  exact one_div_pos.mpr (mul_pos (by norm_num) (zero_lt_one.trans weightConstant_gt_one))

/-- The simultaneous-root density threshold is less than one half. -/
lemma sieveDelta_lt_half : sieveDelta < 1 / 2 := by
  unfold sieveDelta
  apply one_div_lt_one_div_of_lt (by norm_num)
  linarith [weightConstant_gt_one]

/-- For large `x`, sufficiently small families of distinct roots can be hit simultaneously. -/
lemma eventually_simultaneous_roots : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ k : ℕ, (((k + 1 : ℕ) : ℝ)) ≤ sieveDelta * x →
    ∀ root : (p : PrimeIndex (sieveP x)) → Fin (k + 1) → Fin p.val,
    (∀ p, Function.Injective (root p)) →
    ∃ n < sieveT x, ∀ i : Fin (k + 1), ∃ p : PrimeIndex (sieveP x),
      residueVector (sieveP x) n p = root p i := by
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log x / x)
      Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  filter_upwards [eventually_sieve_coefficient_estimates, eventually_sieve_beta_scale,
    eventually_simple_sieve_bounds weightConstant, Filter.eventually_ge_atTop (2 : ℝ),
    tendsto_sieveZ.eventually_ge_atTop 2, tendsto_log_sieveZ.eventually_ge_atTop 1,
    hlog.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 12)]
    with x hcoeff hbeta ⟨hgram, htail, herr, hbad⟩ hx hZ hlogZ hlog
  intro k hk root hroot
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hC : 0 < weightConstant := zero_lt_one.trans weightConstant_gt_one
  have hn : ((k + 1 : ℕ) : ℝ) ≤ x := by
    have := mul_le_mul_of_nonneg_right sieveDelta_lt_half.le hx0.le
    linarith
  have hsize : ((k + 1 : ℕ) : ℝ) * weightConstant ≤ x / 16 := by
    calc
      _ ≤ (sieveDelta * x) * weightConstant := mul_le_mul_of_nonneg_right hk hC.le
      _ = x / 64 := by unfold sieveDelta; field_simp
      _ ≤ x / 16 := by linarith
  have hkn : (k : ℝ) ≤ x := by
    norm_num only [Nat.cast_add, Nat.cast_one] at hn
    linarith
  have hksize : (k : ℝ) * weightConstant ≤ x / 16 := by
    have : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
    exact (mul_le_mul_of_nonneg_right this hC.le).trans hsize
  have hM := sieveZ_lower hx
  have hM' : x ^ 4 ≤ (sieveZ x : ℝ) := hM.trans (sub_le_self _ zero_le_one)
  have hmin : ∀ p ∈ (sieveP x).primeFactors, sieveZ x < p := by
    intro p hp
    obtain ⟨hp, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact (mem_auxiliaryPrimes.mp (prime_dvd_auxiliaryProduct hp hdvd)).2.1
  have hT : 0 < sieveT x := by
    exact_mod_cast (half_pos (Real.exp_pos x)).trans_le (sieveT_lower hx)
  have herror := intervalError_le_simple hx (by
    have := (div_le_iff₀ hx0).mp hlog
    linarith)
  apply finite_simultaneous_roots hcoeff.2 hcoeff.1.le
    (show 1 ≤ sieveD x by unfold sieveD; exact Real.one_le_exp (by linarith))
    (by omega : 1 < sieveZ x) hT hmin root hroot
  · exact (add_le_add (truncated_exponential_le hx0 hcoeff.1.le hsize hbeta)
      (collisionBound_le_simple hx0 hn hM')).trans htail
  · exact (gramBound_le_simple hx1 hn hM hlogZ).trans hgram
  · exact herror.trans herr
  · have huncovered := uncoveredBound_le_simple hx1 hcoeff.1.le hkn hksize hbeta
      hM hlogZ hgram
    calc
      _ ≤ x * (((5 / 4) * (2 * weightConstant ^ 2 + 2 / (Real.log 2) ^ 2)) / x ^ 6 +
          32 / x ^ 3) := by
        gcongr
        exact add_nonneg
          (uncoveredBound_nonneg k (sieveBeta x) weightConstant (sieveZ x) (Real.exp_nonneg _))
          (by positivity)
      _ = ((5 / 4) * (2 * weightConstant ^ 2 + 2 / (Real.log 2) ^ 2)) / x ^ 5 +
          32 / x ^ 2 := by field_simp
      _ < 1 / 4 := hbad

/-- The upper sieve cutoff is eventually below the primorial up to `x`. -/
lemma eventually_sieveY_lt_primorial : ∀ᶠ x : ℝ in Filter.atTop,
    sieveY x < primorial ⌊x⌋₊ := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hpower : Filter.Tendsto (fun x : ℝ => 1 / (Real.log x) ^ 5)
      Filter.atTop (nhds 0) := by
    simpa [one_div] using
      ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp Real.tendsto_log_atTop).pow 5
  have hconstant : Filter.Tendsto (fun x : ℝ => Real.log 2 / x)
      Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop Filter.tendsto_id
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log (x + 2) / x)
      Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp
        (Filter.tendsto_atTop_add_const_right Filter.atTop 2 Filter.tendsto_id)
  have hsqrt : Filter.Tendsto (fun x : ℝ => C / Real.sqrt x)
      Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hsmall := ((hpower.add hconstant).add hlog).add hsqrt
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
    hsmall.eventually_lt_const (by simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    with x hx hsmall
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hpower_eq : 1 / (Real.log x) ^ 5 = sieveUpperLog x / x := by
    rw [sieveUpperLog, div_right_comm, div_self hx0.ne']
  have hsqrt_eq : C / Real.sqrt x = C * Real.sqrt x / x := by
    apply (div_eq_div_iff (Real.sqrt_pos.mpr hx0).ne' hx0.ne').mpr
    rw [mul_assoc, Real.mul_self_sqrt hx0.le]
  rw [hpower_eq, hsqrt_eq, ← add_div, ← add_div, ← add_div] at hsmall
  have htheta : sieveUpperLog x < Chebyshev.theta x := by
    have hbound := (div_lt_iff₀ hx0).mp hsmall
    linarith [Chebyshev.psi_ge' hx0.le, hC x]
  unfold sieveY
  apply (Nat.floor_lt (Real.exp_pos _).le).mpr
  calc
    Real.exp (sieveUpperLog x) < Real.exp (Chebyshev.theta x) :=
      Real.exp_lt_exp.mpr htheta
    _ = (primorial ⌊x⌋₊ : ℝ) := by
      rw [Chebyshev.theta_eq_log_primorial, Real.exp_log (by
        exact_mod_cast primorial_pos ⌊x⌋₊)]

/-- Construct distinct modular roots forcing divisibility of the translated linear forms. -/
lemma exists_linear_roots {p k Q b : ℕ} (hp : p.Prime) (hQ : Q.Coprime p)
    (s : Fin k → ℕ) (hs : Function.Injective s) (hsmall : ∀ i, s i < p) :
    ∃ root : Fin k → Fin p, Function.Injective root ∧
      ∀ n i, n % p = (root i).val → p ∣ b + Q * (n + 1) + s i := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hQ' : (Q : ZMod p) ≠ 0 := ((ZMod.isUnit_iff_coprime Q p).mpr hQ).ne_zero
  let root (i : Fin k) : Fin p :=
    ⟨(-(b + Q + s i : ZMod p) / Q).val, ZMod.val_lt _⟩
  refine ⟨root, ?_, ?_⟩
  · intro i j hij
    have h := congrArg (fun a : Fin p => (a.val : ZMod p) * Q) hij
    simp only [root, ZMod.natCast_zmod_val, div_mul_cancel₀ _ hQ', neg_inj,
      add_right_inj] at h
    apply hs
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hsmall i), Nat.mod_eq_of_lt (hsmall j)]
      using (ZMod.natCast_eq_natCast_iff (s i) (s j) p).mp h
  · intro n i hn
    have hn' : (n : ZMod p) = -(b + Q + s i : ZMod p) / Q := by
      have h := congrArg (fun a : ℕ => (a : ZMod p)) hn
      simpa only [root, ZMod.natCast_mod, ZMod.natCast_zmod_val] using h
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    push_cast
    rw [hn']
    field_simp
    ring


/- ## Extension to large shifts (Radomskii, arXiv:2610.14127) and disproof of Erdős #32 (`log_bound`) -/

/-- The subset of auxiliary primes in `(Z, Y]` after discarding a finite set `bad`. -/
def goodPrimes (Z Y : ℕ) (bad : Finset ℕ) : Finset ℕ :=
  auxiliaryPrimes Z Y \ bad

/-- The product of all non-discarded auxiliary primes in `(Z, Y]`. -/
def goodP (Z Y : ℕ) (bad : Finset ℕ) : ℕ :=
  ∏ p ∈ goodPrimes Z Y bad, p

lemma goodPrimes_subset (Z Y : ℕ) (bad : Finset ℕ) :
    goodPrimes Z Y bad ⊆ auxiliaryPrimes Z Y :=
  Finset.sdiff_subset

lemma goodPrimes_prime {Z Y : ℕ} {bad : Finset ℕ} {p : ℕ} (hp : p ∈ goodPrimes Z Y bad) :
    p.Prime :=
  auxiliaryPrimes_prime (goodPrimes_subset Z Y bad hp)

lemma goodP_squarefree (Z Y : ℕ) (bad : Finset ℕ) : Squarefree (goodP Z Y bad) := by
  unfold goodP
  exact Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (goodPrimes_prime hp) (goodPrimes_prime hq)).mpr hpq))
    (fun p hp => (goodPrimes_prime hp).squarefree)

lemma goodP_pos (Z Y : ℕ) (bad : Finset ℕ) : 0 < goodP Z Y bad := by
  unfold goodP
  exact Finset.prod_pos (fun p hp => (goodPrimes_prime hp).pos)

lemma goodP_dvd_auxiliaryProduct (Z Y : ℕ) (bad : Finset ℕ) :
    goodP Z Y bad ∣ auxiliaryProduct Z Y := by
  unfold goodP auxiliaryProduct
  exact Finset.prod_dvd_prod_of_subset _ _ _ (goodPrimes_subset Z Y bad)

lemma prime_dvd_goodP {Z Y : ℕ} {bad : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ goodP Z Y bad) : p ∈ goodPrimes Z Y bad := by
  have hpf : (goodP Z Y bad).primeFactors = goodPrimes Z Y bad := Nat.primeFactors_prod (fun q hq => goodPrimes_prime hq)
  have hmem : p ∈ (goodP Z Y bad).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hdvd, (goodP_pos Z Y bad).ne'⟩
  rwa [hpf] at hmem

lemma goodP_divisor_gt {Z Y : ℕ} {bad : Finset ℕ} {d : ℕ}
    (hd : d ∈ (goodP Z Y bad).divisors.erase 1) : Z < d :=
  auxiliary_divisor_gt (Finset.mem_erase.mpr
    ⟨(Finset.mem_erase.mp hd).1,
      Nat.mem_divisors.mpr ⟨dvd_trans (Nat.mem_divisors.mp (Finset.mem_erase.mp hd).2).1
        (goodP_dvd_auxiliaryProduct Z Y bad), (auxiliaryProduct_pos Z Y).ne'⟩⟩)

lemma goodP_coefficient_le_one {Z Y : ℕ} {bad : Finset ℕ}
    (hP : 1 < goodP Z Y bad) (hZ : 1 < Z) (hB : 1 ≤ normalizer (goodP Z Y bad) * Real.log Z)
    {d : ℕ} (hd : d ∈ (goodP Z Y bad).divisors) :
    |coefficient (goodP Z Y bad) d| ≤ 1 := by
  by_cases hd1 : d = 1
  · subst hd1; simp [coefficient]
  · have hde : d ∈ (goodP Z Y bad).divisors.erase 1 := Finset.mem_erase.mpr ⟨hd1, hd⟩
    have hdZ : Z < d := goodP_divisor_gt hde
    have hdgt : 1 < d := by omega
    rw [abs_coefficient_eq hP hdgt]
    have hlog : Real.log (Z : ℝ) ≤ Real.log (d : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < Z)) (by exact_mod_cast hdZ.le)
    have hmul : 1 ≤ normalizer (goodP Z Y bad) * Real.log (d : ℝ) :=
      hB.trans (mul_le_mul_of_nonneg_left hlog (normalizer_pos hP).le)
    exact div_le_one_of_le₀ hmul (by linarith)

lemma divisorEulerMoment_goodP_le (Z Y : ℕ) (bad : Finset ℕ) (γ : ℝ) :
    divisorEulerMoment (goodP Z Y bad) γ ≤ divisorEulerMoment (auxiliaryProduct Z Y) γ := by
  unfold divisorEulerMoment
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    exact Nat.mem_divisors.mpr
      ⟨dvd_trans (Nat.mem_divisors.mp hd).1 (goodP_dvd_auxiliaryProduct Z Y bad),
        (auxiliaryProduct_pos Z Y).ne'⟩
  · intro d _ _
    positivity

lemma divisorEulerMoment_goodP_mul_bad {Z Y : ℕ} {bad : Finset ℕ}
    (hbad : bad ⊆ auxiliaryPrimes Z Y) (γ : ℝ) :
    divisorEulerMoment (goodP Z Y bad) γ * divisorEulerMoment (∏ p ∈ bad, p) γ =
      divisorEulerMoment (auxiliaryProduct Z Y) γ := by
  have hbad_p : ∀ p ∈ bad, p.Prime := fun p hp => auxiliaryPrimes_prime (hbad hp)
  rw [goodP, auxiliaryProduct,
    divisorEulerMoment_primeProduct _ (fun p hp => goodPrimes_prime hp),
    divisorEulerMoment_primeProduct _ hbad_p,
    divisorEulerMoment_primeProduct _ (fun p hp => auxiliaryPrimes_prime hp)]
  exact Finset.prod_sdiff hbad

lemma bad_product_euler_le {Z Y : ℕ} {bad : Finset ℕ}
    (hbad : bad ⊆ auxiliaryPrimes Z Y) (hZ : 1 ≤ Z) {t : ℝ} (ht : 0 ≤ t) :
    divisorEulerMoment (∏ p ∈ bad, p) (-t) ≤ Real.exp ((bad.card : ℝ) / (Z : ℝ)) := by
  have hbad_p : ∀ p ∈ bad, p.Prime := fun p hp => auxiliaryPrimes_prime (hbad hp)
  rw [divisorEulerMoment_primeProduct _ hbad_p]
  have hZpos : (0 : ℝ) < Z := by exact_mod_cast (by omega : 0 < Z)
  calc
    ∏ p ∈ bad, (1 + (p : ℝ) ^ (-t) / ((p : ℝ) - 1))
      ≤ ∏ _p ∈ bad, Real.exp (1 / (Z : ℝ)) := by
        apply Finset.prod_le_prod
        · intro p hp
          have hp2 : 2 ≤ p := (hbad_p p hp).two_le
          have : (0 : ℝ) < (p : ℝ) - 1 := by
            have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
            linarith
          positivity
        · intro p hp
          have hpZ : Z < p := (mem_auxiliaryPrimes.mp (hbad hp)).2.1
          have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
          have hpow : (p : ℝ) ^ (-t) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
          have hsub : (Z : ℝ) ≤ (p : ℝ) - 1 := by
            have : (Z : ℝ) + 1 ≤ p := by exact_mod_cast (by omega : Z + 1 ≤ p)
            linarith
          have hdiv : (p : ℝ) ^ (-t) / ((p : ℝ) - 1) ≤ 1 / (Z : ℝ) :=
            div_le_div₀ zero_le_one hpow hZpos hsub
          calc
            1 + (p : ℝ) ^ (-t) / ((p : ℝ) - 1) ≤ 1 + 1 / (Z : ℝ) := by linarith
            _ ≤ Real.exp (1 / (Z : ℝ)) := by linarith [Real.add_one_le_exp (1 / (Z : ℝ))]
    _ = Real.exp (1 / (Z : ℝ)) ^ bad.card := by simp
    _ = Real.exp ((bad.card : ℝ) / (Z : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

lemma goodP_normalizer_lower {Z Y : ℕ} {bad : Finset ℕ}
    (hZY : Z ≤ Y) (hZ : 1 ≤ Z) (hbad : bad ⊆ auxiliaryPrimes Z Y)
    (hbad_card : (bad.card : ℝ) / (Z : ℝ) ≤ Real.log 2)
    {A : ℝ} (hA : 0 < A) (hZA : eulerProduct Z 1 ≤ A)
    (hAY : 2 * A ≤ Real.log ((Y : ℝ) + 1)) :
    Real.log (Real.log ((Y : ℝ) + 1)) - Real.log (2 * A) - 2 ≤
      4 * A * normalizer (goodP Z Y bad) := by
  have hlog : 0 < Real.log ((Y : ℝ) + 1) := (by linarith : 0 < 2 * A).trans_le hAY
  set a : ℝ := 1 / Real.log ((Y : ℝ) + 1)
  set b : ℝ := 1 / (2 * A)
  have ha : 0 < a := one_div_pos.mpr hlog
  have hab : a ≤ b := one_div_le_one_div_of_le (by positivity) hAY
  have hlow : ∀ t ∈ Set.Icc a b, 1 / (4 * t * A) - 1 ≤ divisorEulerMoment (goodP Z Y bad) (-t) - 1 := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have hscale : 1 ≤ t * Real.log ((Y : ℝ) + 1) := by
      have h1 := mul_le_mul_of_nonneg_right ht.1 hlog.le
      have h2 : a * Real.log ((Y : ℝ) + 1) = 1 := one_div_mul_cancel hlog.ne'
      linarith
    have haux := divisorEulerMoment_lower hZY ht0 hA hZA hscale
    have hbad_le : divisorEulerMoment (∏ p ∈ bad, p) (-t) ≤ 2 := by
      calc
        _ ≤ Real.exp ((bad.card : ℝ) / (Z : ℝ)) := bad_product_euler_le hbad hZ ht0.le
        _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hbad_card
        _ = 2 := Real.exp_log (by norm_num)
    have hbad_pos : 0 < divisorEulerMoment (∏ p ∈ bad, p) (-t) := by
      have hbad_p : ∀ p ∈ bad, p.Prime := fun p hp => auxiliaryPrimes_prime (hbad hp)
      rw [divisorEulerMoment_primeProduct _ hbad_p]
      apply Finset.prod_pos
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hbad_p p hp).two_le
      have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
    have hmul := divisorEulerMoment_goodP_mul_bad hbad (-t)
    have hgp : 1 / (4 * t * A) ≤ divisorEulerMoment (goodP Z Y bad) (-t) := by
      have h1 : 1 / (2 * t * A) ≤ divisorEulerMoment (goodP Z Y bad) (-t) * 2 := by
        calc
          1 / (2 * t * A) ≤ divisorEulerMoment (auxiliaryProduct Z Y) (-t) := haux
          _ = divisorEulerMoment (goodP Z Y bad) (-t) * divisorEulerMoment (∏ p ∈ bad, p) (-t) := hmul.symm
          _ ≤ divisorEulerMoment (goodP Z Y bad) (-t) * 2 :=
              mul_le_mul_of_nonneg_left hbad_le (divisorEulerMoment_nonneg _ _)
      have h2 : 1 / (4 * t * A) * 2 = 1 / (2 * t * A) := by field_simp; ring
      linarith
    linarith
  have hint_lhs : IntervalIntegrable (fun t : ℝ => 1 / (4 * t * A) - 1) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    exact ((continuousAt_const.div
      ((continuousAt_const.mul continuousAt_id).mul continuousAt_const)
      (mul_ne_zero (mul_ne_zero (by norm_num) ht0.ne') hA.ne')).sub continuousAt_const).continuousWithinAt
  have hint_rhs : IntervalIntegrable (fun t : ℝ => divisorEulerMoment (goodP Z Y bad) (-t) - 1)
      MeasureTheory.volume a b :=
    ((continuous_divisorEulerMoment _).sub continuous_const).intervalIntegrable a b
  have hmono : (∫ t in a..b, (1 / (4 * t * A) - 1)) ≤
      ∫ t in a..b, (divisorEulerMoment (goodP Z Y bad) (-t) - 1) :=
    intervalIntegral.integral_mono_on hab hint_lhs hint_rhs hlow
  have hcalc : (∫ t in a..b, (1 / (4 * t * A) - 1)) = (Real.log b - Real.log a) / (4 * A) - (b - a) := by
    have h1 : ∀ t ∈ Set.uIcc a b, (1 / (4 * t * A) - 1) = (1 / (4 * A)) * t⁻¹ - 1 := by
      intro t _; ring
    have hint_inv : IntervalIntegrable (fun t : ℝ => (1 / (4 * A)) * t⁻¹) MeasureTheory.volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hab]
      intro t ht
      have ht0 : 0 < t := ha.trans_le ht.1
      exact (continuousAt_const.mul (continuousAt_id.inv₀ ht0.ne')).continuousWithinAt
    rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_sub hint_inv intervalIntegrable_const,
      intervalIntegral.integral_const_mul,
      integral_inv_of_pos ha (ha.trans_le hab),
      intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_one, Real.log_div (ha.trans_le hab).ne' ha.ne']
    ring
  have hnorm := normalizer_integral_le (goodP_pos Z Y bad).ne' ha.le b
  have hcomb : (Real.log b - Real.log a) / (4 * A) - (b - a) ≤ normalizer (goodP Z Y bad) := by
    linarith
  have hlog_ba : Real.log b - Real.log a = Real.log (Real.log ((Y : ℝ) + 1)) - Real.log (2 * A) := by
    simp only [a, b, one_div, Real.log_inv]
    ring
  rw [hlog_ba] at hcomb
  have hmul := (div_le_iff₀ (show 0 < 4 * A by positivity)).mp (sub_le_iff_le_add.mp hcomb)
  have hba : (b - a) * (4 * A) ≤ 2 := by
    have ha0 : 0 ≤ a * (4 * A) := by positivity
    have hb4 : b * (4 * A) = 2 := by
      simp only [b]
      field_simp
      ring
    linarith
  linarith

def normalizerLower' : ℝ := 1 / (400 * Real.exp 6)

lemma normalizerLower'_pos : 0 < normalizerLower' := by
  unfold normalizerLower'
  positivity

def weightConstant' : ℝ :=
  1 + absoluteMomentBound normalizerLower' + coefficientControl normalizerLower'

lemma weightConstant'_gt_one : 1 < weightConstant' := by
  unfold weightConstant'
  linarith [absoluteMomentBound_pos normalizerLower'_pos,
    coefficientControl_pos normalizerLower'_pos]

def sieveDelta' : ℝ := 1 / (64 * weightConstant')

lemma sieveDelta'_pos : 0 < sieveDelta' := by
  unfold sieveDelta'
  have := zero_lt_one.trans weightConstant'_gt_one
  positivity

lemma sieveDelta'_lt_half : sieveDelta' < 1 / 2 := by
  unfold sieveDelta'
  have h := weightConstant'_gt_one
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  linarith

lemma goodP_coefficientAbsMoment_le {Z Y : ℕ} {bad : Finset ℕ}
    (hZY : Z ≤ Y) (hZ : 2 ≤ Z) (hlogZ : 1 ≤ Real.log Z)
    (hP : 1 < goodP Z Y bad)
    {b γ : ℝ} (hb : 0 < b) (hB : b ≤ normalizer (goodP Z Y bad))
    (hγ : 0 ≤ γ) (hscale : γ * Real.log Y ≤ 2) :
    coefficientAbsMoment (goodP Z Y bad) γ ≤ absoluteMomentBound b := by
  have hY : 1 < Y := by omega
  have hlogY : 1 ≤ Real.log (Y : ℝ) :=
    hlogZ.trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < Z))
      (by exact_mod_cast hZY))
  have hlogYpos : 0 < Real.log (Y : ℝ) := zero_lt_one.trans_le hlogY
  have hYE : (Y : ℝ) ^ γ ≤ Real.exp 2 := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast (by omega : 0 < Y))]
    exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hscale)
  have hzero : divisorEulerMoment (auxiliaryProduct Z Y) 0 ≤
      2 * Real.exp 6 * Real.log Y := by
    calc
      _ ≤ Real.exp 6 * (1 + Real.log Y) / Real.log Z := divisorEulerMoment_zero_le hZY hZ
      _ ≤ Real.exp 6 * (1 + Real.log Y) := div_le_self (by positivity) hlogZ
      _ ≤ 2 * Real.exp 6 * Real.log Y := by nlinarith [Real.exp_pos 6]
  have hmoment : divisorEulerMoment (goodP Z Y bad) γ ≤
      (2 * Real.exp 6 * Real.exp (6 * Real.exp 2)) * Real.log Y := by
    calc
      _ ≤ divisorEulerMoment (auxiliaryProduct Z Y) γ := divisorEulerMoment_goodP_le Z Y bad γ
      _ ≤ divisorEulerMoment (auxiliaryProduct Z Y) 0 * Real.exp (6 * Real.exp 2) :=
          auxiliary_divisorEulerMoment_tilt (hZ.trans hZY) hγ hscale
      _ ≤ (2 * Real.exp 6 * Real.log Y) * Real.exp (6 * Real.exp 2) :=
          mul_le_mul_of_nonneg_right hzero (Real.exp_pos _).le
      _ = _ := by ring
  calc
    coefficientAbsMoment (goodP Z Y bad) γ
      ≤ Real.exp 2 + divisorEulerMoment (goodP Z Y bad) γ /
          (normalizer (goodP Z Y bad) * Real.log Y) :=
        coefficientAbsMoment_le hP hY hγ hYE
    _ ≤ Real.exp 2 + ((2 * Real.exp 6 * Real.exp (6 * Real.exp 2)) * Real.log Y) /
          (b * Real.log Y) := by
        gcongr
    _ = absoluteMomentBound b := by
        unfold absoluteMomentBound
        rw [mul_div_mul_right _ _ hlogYpos.ne']

lemma goodP_coefficientAbsMoment_control {Z Y : ℕ} {bad : Finset ℕ}
    (hZY : Z ≤ Y) (hZ : 2 ≤ Z) (hlogZ : 1 ≤ Real.log Z)
    (hP : 1 < goodP Z Y bad)
    {b γ : ℝ} (hb : 0 < b) (hB : b ≤ normalizer (goodP Z Y bad))
    (hγ : 0 ≤ γ) (hscale : γ * Real.log Y ≤ 2) :
    coefficientAbsMoment (goodP Z Y bad) γ ≤
      coefficientControl b * normalizer (goodP Z Y bad) := by
  have h1 := goodP_coefficientAbsMoment_le hZY hZ hlogZ hP hb hB hγ hscale
  unfold coefficientControl
  calc
    coefficientAbsMoment (goodP Z Y bad) γ ≤ absoluteMomentBound b := h1
    _ = (absoluteMomentBound b / b) * b := by field_simp
    _ ≤ (absoluteMomentBound b / b) * normalizer (goodP Z Y bad) :=
        mul_le_mul_of_nonneg_left hB (div_nonneg (absoluteMomentBound_pos hb).le hb.le)

lemma eventually_filtered_coefficient_estimates : ∀ᶠ x : ℝ in Filter.atTop,
    0 < sieveBeta x ∧
    ∀ bad : Finset ℕ, bad ⊆ auxiliaryPrimes (sieveZ x) (sieveY x) →
      (bad.card : ℝ) ≤ x ^ 4 →
      CoefficientEstimates (goodP (sieveZ x) (sieveY x) bad) (sieveBeta x) weightConstant' := by
  have hpow : Filter.Tendsto (fun x : ℝ => (Real.log x) ^ 6 / x) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 6 one_ne_zero
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x)
      Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp Real.tendsto_log_atTop
  have hunit := (Filter.Tendsto.const_mul_atTop normalizerLower'_pos tendsto_log_sieveZ).eventually
    (Filter.eventually_ge_atTop (1 : ℝ))
  filter_upwards [Filter.eventually_gt_atTop (10 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    tendsto_sieveZ.eventually_ge_atTop 2,
    tendsto_log_sieveZ.eventually_ge_atTop 1,
    hpow.eventually_le_const (by positivity : (0 : ℝ) < 1 / (14 * Real.exp 6)),
    hlog.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 24),
    Real.tendsto_log_atTop.eventually_ge_atTop (4 * (Real.log 14 + 8)),
    hunit]
    with x hx hlx hZ hlogZ hpow hlog hconst hunit'
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 < Real.log x := by linarith
  have hupper : 0 < sieveUpperLog x := div_pos hx0 (pow_pos hlx0 5)
  have hexp : 1 ≤ Real.exp 6 := Real.one_le_exp (by norm_num)
  have hlarge : 14 * Real.exp 6 * (Real.log x) ^ 6 ≤ x := by
    simpa [mul_comm] using (div_le_div_iff₀ hx0 (by positivity : 0 < 14 * Real.exp 6)).mp hpow
  have hscale_u : 14 * Real.exp 6 * Real.log x ≤ sieveUpperLog x := by
    apply (le_div_iff₀ (pow_pos hlx0 5)).mpr
    nlinarith [hlarge]
  have hZY : sieveZ x ≤ sieveY x := by
    apply Nat.floor_le_floor
    calc
      x ^ 6 = Real.exp (6 * Real.log x) := by
        simpa only [Nat.cast_ofNat, Real.exp_log hx0] using
          (Real.exp_nat_mul (Real.log x) 6).symm
      _ ≤ Real.exp (sieveUpperLog x) := Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_right hexp hlx0.le])
  have hY : 2 ≤ sieveY x := hZ.trans hZY
  have hY0 : (0 : ℝ) < sieveY x := by exact_mod_cast (by omega : 0 < sieveY x)
  have hYlog_le : Real.log (sieveY x : ℝ) ≤ sieveUpperLog x := by
    have h := Real.log_le_log hY0 (Nat.floor_le (Real.exp_pos (sieveUpperLog x)).le)
    simpa only [Real.log_exp] using h
  have hYlog_ge : sieveUpperLog x ≤ Real.log ((sieveY x : ℝ) + 1) := by
    have h := Real.log_le_log (Real.exp_pos (sieveUpperLog x))
      (Nat.lt_floor_add_one (Real.exp (sieveUpperLog x))).le
    rw [Real.log_exp] at h
    exact h
  have hlogZ_le : Real.log (sieveZ x : ℝ) ≤ 6 * Real.log x := by
    calc
      _ ≤ Real.log (x ^ 6) := Real.log_le_log
        (by exact_mod_cast (by omega : 0 < sieveZ x)) (Nat.floor_le (by positivity))
      _ = _ := by rw [Real.log_pow]; norm_num
  have hZA : eulerProduct (sieveZ x) 1 ≤ 7 * Real.exp 6 * Real.log x := by
    calc
      eulerProduct (sieveZ x) 1 ≤ Real.exp 6 * (1 + Real.log (sieveZ x : ℝ)) :=
        eulerProduct_one_le hZ
      _ ≤ Real.exp 6 * (1 + 6 * Real.log x) := by gcongr
      _ ≤ 7 * Real.exp 6 * Real.log x := by nlinarith [Real.exp_pos 6]
  have hsmall : 6 * Real.log (Real.log x) + Real.log 14 + 8 ≤ Real.log x / 2 := by
    have h := (div_le_iff₀ hlx0).mp hlog
    linarith
  have hZ_ge : x ^ 6 / 2 ≤ (sieveZ x : ℝ) := by
    have hlt := Nat.lt_floor_add_one (x ^ 6)
    have h1 : (2 : ℝ) ≤ x ^ 6 := by
      have : (2 : ℝ) ≤ x := by linarith
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) this 6]
    change x ^ 6 / 2 ≤ (⌊x ^ 6⌋₊ : ℝ)
    linarith
  refine ⟨one_div_pos.mpr hupper, ?_⟩
  intro bad hbad hbad_card
  have hbad_div : (bad.card : ℝ) / (sieveZ x : ℝ) ≤ Real.log 2 := by
    have hZpos : (0 : ℝ) < sieveZ x := by exact_mod_cast (by omega : 0 < sieveZ x)
    have h2 : (bad.card : ℝ) / (sieveZ x : ℝ) ≤ 2 / x ^ 2 := by
      rw [div_le_div_iff₀ hZpos (by positivity)]
      have : x ^ 4 * x ^ 2 = x ^ 6 := by ring
      nlinarith [hbad_card, hZ_ge]
    have h3 : 2 / x ^ 2 ≤ 2 / 100 := by
      gcongr
      nlinarith
    have hlog2 : (2 : ℝ) / 100 ≤ Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    linarith
  set A : ℝ := 7 * Real.exp 6 * Real.log x
  have hA : 0 < A := by positivity
  have hAY : 2 * A ≤ Real.log ((sieveY x : ℝ) + 1) := by
    calc
      2 * A = 14 * Real.exp 6 * Real.log x := by ring
      _ ≤ sieveUpperLog x := hscale_u
      _ ≤ Real.log ((sieveY x : ℝ) + 1) := hYlog_ge
  have hnorm_raw := goodP_normalizer_lower hZY (by omega) hbad hbad_div hA hZA hAY
  have hlog2A : Real.log (2 * A) = Real.log 14 + 6 + Real.log (Real.log x) := by
    have : 2 * A = (14 * Real.exp 6) * Real.log x := by ring
    rw [this, Real.log_mul (by positivity) hlx0.ne',
      Real.log_mul (by norm_num) (Real.exp_pos 6).ne', Real.log_exp]
  have hlog_upper : Real.log x - 5 * Real.log (Real.log x) ≤
      Real.log (Real.log ((sieveY x : ℝ) + 1)) := by
    calc
      Real.log x - 5 * Real.log (Real.log x) = Real.log (sieveUpperLog x) := by
        unfold sieveUpperLog
        rw [Real.log_div hx0.ne' (pow_pos hlx0 5).ne', Real.log_pow]
        norm_num
      _ ≤ Real.log (Real.log ((sieveY x : ℝ) + 1)) := Real.log_le_log hupper hYlog_ge
  have hB : normalizerLower' ≤ normalizer (goodP (sieveZ x) (sieveY x) bad) := by
    have hstep : Real.log x / 2 ≤ 4 * A * normalizer (goodP (sieveZ x) (sieveY x) bad) := by
      linarith
    have h4A : 4 * A = 28 * Real.exp 6 * Real.log x := by ring
    rw [h4A] at hstep
    have hdiv : 1 / (56 * Real.exp 6) ≤ normalizer (goodP (sieveZ x) (sieveY x) bad) := by
      rw [div_le_iff₀ (by positivity)]
      have hmul : (1 : ℝ) * Real.log x ≤
          (normalizer (goodP (sieveZ x) (sieveY x) bad) * (56 * Real.exp 6)) * Real.log x := by
        linarith
      exact le_of_mul_le_mul_right hmul hlx0
    have hcmp : normalizerLower' ≤ 1 / (56 * Real.exp 6) := by
      unfold normalizerLower'
      gcongr
      norm_num
    exact hcmp.trans hdiv
  have hP : 1 < goodP (sieveZ x) (sieveY x) bad := by
    have hp0 : 0 < goodP (sieveZ x) (sieveY x) bad := goodP_pos _ _ _
    by_contra h
    have he : goodP (sieveZ x) (sieveY x) bad = 1 := by omega
    have hb0 : normalizer (goodP (sieveZ x) (sieveY x) bad) = 0 := by simp [he, normalizer]
    rw [hb0] at hB
    exact (not_le_of_gt normalizerLower'_pos) hB
  have hscale (γ : ℝ) (hγ : 0 ≤ γ) (hγβ : γ ≤ 2 * sieveBeta x) :
      γ * Real.log (sieveY x : ℝ) ≤ 2 := by
    calc
      _ ≤ γ * sieveUpperLog x := mul_le_mul_of_nonneg_left hYlog_le hγ
      _ ≤ (2 * sieveBeta x) * sieveUpperLog x := mul_le_mul_of_nonneg_right hγβ hupper.le
      _ = 2 := by unfold sieveBeta; field_simp
  have hC1 : absoluteMomentBound normalizerLower' ≤ weightConstant' := by
    unfold weightConstant'
    linarith [coefficientControl_pos normalizerLower'_pos]
  have hC2 : coefficientControl normalizerLower' ≤ weightConstant' := by
    unfold weightConstant'
    linarith [absoluteMomentBound_pos normalizerLower'_pos]
  refine ⟨hP, goodP_squarefree _ _ _, ?_, ?_, ?_⟩
  · intro d hd
    exact goodP_coefficient_le_one hP (by omega)
      (hunit'.trans (mul_le_mul_of_nonneg_right hB (by linarith : 0 ≤ Real.log (sieveZ x : ℝ)))) hd
  · intro γ hγ hγβ
    exact (goodP_coefficientAbsMoment_le hZY hZ hlogZ hP normalizerLower'_pos hB hγ
      (hscale γ hγ hγβ)).trans hC1
  · intro γ hγ hγβ
    exact (goodP_coefficientAbsMoment_control hZY hZ hlogZ hP normalizerLower'_pos hB hγ
      (hscale γ hγ hγβ)).trans (mul_le_mul_of_nonneg_right hC2 (normalizer_pos hP).le)

lemma eventually_filtered_simultaneous_roots : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ bad : Finset ℕ, bad ⊆ auxiliaryPrimes (sieveZ x) (sieveY x) →
      (bad.card : ℝ) ≤ x ^ 4 →
      ∀ k : ℕ, (((k + 1 : ℕ) : ℝ)) ≤ sieveDelta' * x →
      ∀ root : (p : PrimeIndex (goodP (sieveZ x) (sieveY x) bad)) → Fin (k + 1) → Fin p.val,
      (∀ p, Function.Injective (root p)) →
      ∃ n < sieveT x, ∀ i : Fin (k + 1),
        ∃ p : PrimeIndex (goodP (sieveZ x) (sieveY x) bad),
          residueVector (goodP (sieveZ x) (sieveY x) bad) n p = root p i := by
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  filter_upwards [eventually_filtered_coefficient_estimates, eventually_sieve_beta_scale,
    eventually_simple_sieve_bounds weightConstant', Filter.eventually_ge_atTop (2 : ℝ),
    tendsto_sieveZ.eventually_ge_atTop 2, tendsto_log_sieveZ.eventually_ge_atTop 1,
    hlog.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 12)]
    with x ⟨hbeta_pos, hcoeff_all⟩ hbeta ⟨hgram, htail, herr, hbad_b⟩ hx hZ hlogZ hlog
  intro bad hbad hbad_card k hk root hroot
  have hcoeff := hcoeff_all bad hbad hbad_card
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hC : 0 < weightConstant' := zero_lt_one.trans weightConstant'_gt_one
  have hn : ((k + 1 : ℕ) : ℝ) ≤ x := by
    have := mul_le_mul_of_nonneg_right sieveDelta'_lt_half.le hx0.le
    linarith
  have hsize : ((k + 1 : ℕ) : ℝ) * weightConstant' ≤ x / 16 := by
    calc
      _ ≤ (sieveDelta' * x) * weightConstant' := mul_le_mul_of_nonneg_right hk hC.le
      _ = x / 64 := by unfold sieveDelta'; field_simp
      _ ≤ x / 16 := by linarith
  have hkn : (k : ℝ) ≤ x := by
    norm_num only [Nat.cast_add, Nat.cast_one] at hn
    linarith
  have hksize : (k : ℝ) * weightConstant' ≤ x / 16 := by
    have : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
    exact (mul_le_mul_of_nonneg_right this hC.le).trans hsize
  have hM := sieveZ_lower hx
  have hM' : x ^ 4 ≤ (sieveZ x : ℝ) := hM.trans (sub_le_self _ zero_le_one)
  have hmin : ∀ p ∈ (goodP (sieveZ x) (sieveY x) bad).primeFactors, sieveZ x < p := by
    intro p hp
    obtain ⟨hp, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact (mem_auxiliaryPrimes.mp (goodPrimes_subset _ _ _ (prime_dvd_goodP hp hdvd))).2.1
  have hT : 0 < sieveT x := by
    exact_mod_cast (half_pos (Real.exp_pos x)).trans_le (sieveT_lower hx)
  have herror := intervalError_le_simple hx (by
    have := (div_le_iff₀ hx0).mp hlog
    linarith)
  apply finite_simultaneous_roots hcoeff hbeta_pos.le
    (show 1 ≤ sieveD x by unfold sieveD; exact Real.one_le_exp (by linarith))
    (by omega : 1 < sieveZ x) hT hmin root hroot
  · exact (add_le_add
      (truncated_exponential_le hx0 hbeta_pos.le hsize hbeta)
      (collisionBound_le_simple hx0 hn hM')).trans htail
  · exact (gramBound_le_simple hx1 hn hM hlogZ).trans hgram
  · exact herror.trans herr
  · have hunc := uncoveredBound_le_simple hx1 hbeta_pos.le hkn hksize hbeta hM hlogZ hgram
    have hmul : ((k + 1 : ℕ) : ℝ) * (uncoveredBound k (sieveBeta x) weightConstant'
        (sieveZ x) (sieveD x) + 16 * sieveD x ^ 6 / sieveT x) ≤
        x * ((5 / 4) * (2 * weightConstant' ^ 2 + 2 / (Real.log 2) ^ 2) / x ^ 6 + 32 / x ^ 3) := by
      have hunc0 : 0 ≤ uncoveredBound k (sieveBeta x) weightConstant' (sieveZ x) (sieveD x) :=
        uncoveredBound_nonneg _ _ _ _ (by unfold sieveD; positivity)
      have herr0 : 0 ≤ 16 * sieveD x ^ 6 / sieveT x := by unfold sieveD; positivity
      apply mul_le_mul hn (add_le_add hunc herror) (add_nonneg hunc0 herr0) hx0.le
    have hsimp : x * ((5 / 4) * (2 * weightConstant' ^ 2 + 2 / (Real.log 2) ^ 2) / x ^ 6 +
        32 / x ^ 3) =
        ((5 / 4) * (2 * weightConstant' ^ 2 + 2 / (Real.log 2) ^ 2)) / x ^ 5 + 32 / x ^ 2 := by
      field_simp
    linarith

lemma exists_linear_roots_sub {p k Q b : ℕ} (hp : p.Prime) (hQ : Q.Coprime p)
    (s : Fin k → ℕ) (hdist : ∀ i j, i ≠ j → (s i : ZMod p) ≠ (s j : ZMod p)) :
    ∃ root : Fin k → Fin p, Function.Injective root ∧
      ∀ n i, n % p = (root i).val → (p : ℤ) ∣ (b + Q * (n + 1) : ℤ) - (s i : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hQ' : (Q : ZMod p) ≠ 0 := ((ZMod.isUnit_iff_coprime Q p).mpr hQ).ne_zero
  let root (i : Fin k) : Fin p :=
    ⟨(((s i : ZMod p) - (b + Q : ZMod p)) / (Q : ZMod p)).val, ZMod.val_lt _⟩
  refine ⟨root, ?_, ?_⟩
  · intro i j hij
    by_contra hne
    have h := congrArg (fun a : Fin p => (a.val : ZMod p) * (Q : ZMod p)) hij
    simp only [root, ZMod.natCast_zmod_val, div_mul_cancel₀ _ hQ', sub_left_inj] at h
    exact hdist i j hne h
  · intro n i hn
    have hn' : (n : ZMod p) = ((s i : ZMod p) - (b + Q : ZMod p)) / (Q : ZMod p) := by
      have h := congrArg (fun a : ℕ => (a : ZMod p)) hn
      simpa only [root, ZMod.natCast_mod, ZMod.natCast_zmod_val] using h
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    rw [hn']
    field_simp
    ring

lemma card_prime_divisors_gt_le {Z d : ℕ} (hZ : 2 ≤ Z) (hd : 0 < d) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Z < p ∧ p ∣ d) :
    (P.card : ℝ) * Real.log (Z : ℝ) ≤ Real.log (d : ℝ) := by
  have hprod_dvd : (∏ p ∈ P, p) ∣ d := by
    apply Finset.prod_primes_dvd d (fun p hp => (hP p hp).1.prime)
    intro p hp
    exact (hP p hp).2.2
  have hprod_le : (∏ p ∈ P, p) ≤ d := Nat.le_of_dvd hd hprod_dvd
  have hZpow : Z ^ P.card ≤ ∏ p ∈ P, p := by
    calc
      Z ^ P.card = ∏ _p ∈ P, Z := by simp
      _ ≤ ∏ p ∈ P, p := Finset.prod_le_prod' (fun p hp => (hP p hp).2.1.le)
  have hle : (Z : ℝ) ^ P.card ≤ (d : ℝ) := by exact_mod_cast hZpow.trans hprod_le
  have hZpos : (0 : ℝ) < Z := by exact_mod_cast (by omega : 0 < Z)
  have hlog := Real.log_le_log (pow_pos hZpos _) hle
  simpa only [Real.log_pow] using hlog

lemma large_shift_divisors : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ k : ℕ, (((k + 1 : ℕ) : ℝ)) ≤ sieveDelta' * x →
    ∀ s : Fin (k + 1) → ℕ, Function.Injective s →
    (∀ i, (s i : ℝ) ≤ Real.exp (4 * x)) →
    ∀ b : ℕ, ∃ t : ℕ, 1 ≤ t ∧ t ≤ sieveT x ∧
      ∀ i : Fin (k + 1), ∃ p : ℕ, p.Prime ∧ sieveZ x < p ∧ p ≤ sieveY x ∧
        (p : ℤ) ∣ (b + primorial ⌊x⌋₊ * t : ℤ) - (s i : ℤ) := by
  classical
  filter_upwards [eventually_filtered_simultaneous_roots,
    Filter.eventually_ge_atTop (4 : ℝ),
    tendsto_sieveZ.eventually_ge_atTop 2,
    tendsto_log_sieveZ.eventually_ge_atTop 4]
    with x hroots hx hZ hlogZ
  intro k hk s hs hsb b
  have hx0 : 0 < x := by linarith
  have hkn : ((k + 1 : ℕ) : ℝ) ≤ x := by
    have := mul_le_mul_of_nonneg_right sieveDelta'_lt_half.le hx0.le
    linarith
  let pairBad (ij : Fin (k + 1) × Fin (k + 1)) : Finset ℕ :=
    (auxiliaryPrimes (sieveZ x) (sieveY x)).filter
      (fun p => ij.1 ≠ ij.2 ∧ s ij.1 < s ij.2 ∧ p ∣ (s ij.2 - s ij.1))
  let bad : Finset ℕ := Finset.univ.biUnion pairBad
  have hbad_sub : bad ⊆ auxiliaryPrimes (sieveZ x) (sieveY x) := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨ij, _, hpij⟩
    exact (Finset.mem_filter.mp hpij).1
  have hpair_card (ij : Fin (k + 1) × Fin (k + 1)) : ((pairBad ij).card : ℝ) ≤ x := by
    by_cases hlt : ij.1 ≠ ij.2 ∧ s ij.1 < s ij.2
    · have hd_pos : 0 < s ij.2 - s ij.1 := Nat.sub_pos_of_lt hlt.2
      have hlog_le := card_prime_divisors_gt_le hZ hd_pos (pairBad ij) (by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpA, _, _, hdvd⟩
        obtain ⟨hpP, hpZ, _⟩ := mem_auxiliaryPrimes.mp hpA
        exact ⟨hpP, hpZ, hdvd⟩)
      have hd_le : ((s ij.2 - s ij.1 : ℕ) : ℝ) ≤ Real.exp (4 * x) := by
        have h1 : (s ij.2 - s ij.1 : ℕ) ≤ s ij.2 := Nat.sub_le _ _
        exact (by exact_mod_cast h1 : ((s ij.2 - s ij.1 : ℕ) : ℝ) ≤ s ij.2).trans (hsb ij.2)
      have hlog_d : Real.log ((s ij.2 - s ij.1 : ℕ) : ℝ) ≤ 4 * x := by
        have := Real.log_le_log (by exact_mod_cast hd_pos) hd_le
        simpa only [Real.log_exp] using this
      nlinarith [hlog_le, hlog_d, hlogZ]
    · have hemp : pairBad ij = ∅ := by
        ext p
        simp only [pairBad, Finset.mem_filter, Finset.notMem_empty, iff_false]
        rintro ⟨_, h1, h2, _⟩
        exact hlt ⟨h1, h2⟩
      simp [hemp, hx0.le]
  have hbad_card : (bad.card : ℝ) ≤ x ^ 4 := by
    have h1 : bad.card ≤ ∑ ij : Fin (k + 1) × Fin (k + 1), (pairBad ij).card :=
      Finset.card_biUnion_le
    have h2 : (bad.card : ℝ) ≤ ∑ ij : Fin (k + 1) × Fin (k + 1), ((pairBad ij).card : ℝ) := by
      exact_mod_cast h1
    have h3 : (∑ ij : Fin (k + 1) × Fin (k + 1), ((pairBad ij).card : ℝ)) ≤
        (Fintype.card (Fin (k + 1) × Fin (k + 1)) : ℝ) * x := by
      calc
        _ ≤ ∑ _ij : Fin (k + 1) × Fin (k + 1), x := Finset.sum_le_sum (fun ij _ => hpair_card ij)
        _ = _ := by simp
    have hcard_prod : (Fintype.card (Fin (k + 1) × Fin (k + 1)) : ℝ) = ((k + 1 : ℕ) : ℝ) ^ 2 := by
      simp [sq]
    rw [hcard_prod] at h3
    calc
      (bad.card : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 2 * x := h2.trans h3
      _ ≤ x ^ 2 * x := by gcongr
      _ = x ^ 3 := by ring
      _ ≤ x ^ 4 := by
        have : (1 : ℝ) ≤ x := by linarith
        nlinarith [pow_nonneg hx0.le 3]
  have hlinear (p : PrimeIndex (goodP (sieveZ x) (sieveY x) bad)) :
      ∃ root : Fin (k + 1) → Fin p.val, Function.Injective root ∧
        ∀ n i, n % p.val = (root i).val →
          (p.val : ℤ) ∣ (b + primorial ⌊x⌋₊ * (n + 1) : ℤ) - (s i : ℤ) := by
    obtain ⟨hp, hdvd, _⟩ := Nat.mem_primeFactors.mp p.property
    have hpG := prime_dvd_goodP hp hdvd
    have hpA := goodPrimes_subset _ _ _ hpG
    have hpNotBad : p.val ∉ bad := (Finset.mem_sdiff.mp hpG).2
    have hpZ : sieveZ x < p.val := (mem_auxiliaryPrimes.mp hpA).2.1
    have hpx : ⌊x⌋₊ < p.val := by
      have h1 : x ≤ x ^ 6 := by
        have : (1 : ℝ) ≤ x := by linarith
        nlinarith [pow_le_pow_right₀ this (show 1 ≤ 6 by decide)]
      exact (Nat.floor_mono h1).trans_lt hpZ
    have hcop : (primorial ⌊x⌋₊).Coprime p.val :=
      (hp.coprime_iff_not_dvd.mpr (hp.dvd_primorial_iff.not.mpr hpx.not_ge)).symm
    apply exists_linear_roots_sub hp hcop s
    intro i j hij heq
    have hne : s i ≠ s j := fun h => hij (hs h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · apply hpNotBad
      refine Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _, Finset.mem_filter.mpr ⟨hpA, hij, hlt, ?_⟩⟩
      have hmod := (ZMod.natCast_eq_natCast_iff (s i) (s j) p.val).mp heq
      exact (Nat.modEq_iff_dvd' hlt.le).mp hmod
    · apply hpNotBad
      refine Finset.mem_biUnion.mpr ⟨(j, i), Finset.mem_univ _, Finset.mem_filter.mpr ⟨hpA, hij.symm, hgt, ?_⟩⟩
      have hmod := (ZMod.natCast_eq_natCast_iff (s j) (s i) p.val).mp heq.symm
      exact (Nat.modEq_iff_dvd' hgt.le).mp hmod
  choose root hinj hdiv using hlinear
  obtain ⟨n, hn, hhit⟩ := hroots bad hbad_sub hbad_card k hk root hinj
  refine ⟨n + 1, Nat.succ_le_succ (Nat.zero_le _), Nat.succ_le_of_lt hn, ?_⟩
  intro i
  obtain ⟨p, hp_eq⟩ := hhit i
  obtain ⟨hp, hdvd, _⟩ := Nat.mem_primeFactors.mp p.property
  obtain ⟨_, hpZ, hpY⟩ := mem_auxiliaryPrimes.mp (goodPrimes_subset _ _ _ (prime_dvd_goodP hp hdvd))
  exact ⟨p.val, hp, hpZ, hpY, hdiv p n i (congrArg Fin.val hp_eq)⟩

/-- Chinese Remainder Theorem over a finite set of primes. -/
lemma exists_crt_primes (ps : Finset ℕ) (hps : ∀ p ∈ ps, p.Prime) (a : ℕ → ℕ) :
    ∃ r : ℕ, r < ∏ p ∈ ps, p ∧ ∀ p ∈ ps, r % p = a p % p := by
  classical
  induction ps using Finset.induction with
  | empty => exact ⟨0, by simp, by simp⟩
  | @insert p s hp ih =>
    have hpp : p.Prime := hps p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hps q (Finset.mem_insert_of_mem hq)
    obtain ⟨r₀, hr₀, hmod₀⟩ := ih hs
    have hcop : p.Coprime (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      exact (Nat.coprime_primes hpp (hs q hq)).mpr (fun heq => hp (heq ▸ hq))
    let c := Nat.chineseRemainder hcop (a p) r₀
    have hPpos : 0 < p * ∏ q ∈ s, q :=
      mul_pos hpp.pos (Finset.prod_pos fun q hq => (hs q hq).pos)
    refine ⟨c.val % (p * ∏ q ∈ s, q), ?_, ?_⟩
    · rw [Finset.prod_insert hp]
      exact Nat.mod_lt _ hPpos
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hqs
      · rw [Nat.mod_mod_of_dvd _ (dvd_mul_right q _)]
        exact c.property.1
      · have hq_dvd : q ∣ p * ∏ x ∈ s, x :=
          dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hqs) p
        rw [Nat.mod_mod_of_dvd _ hq_dvd]
        have h1 : c.val % q = r₀ % q := by
          have := Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem _ hqs) c.property.2
          exact this
        exact h1.trans (hmod₀ q hqs)

/-- Pigeonhole gap lemma: a finite set `B` leaves an empty open interval of length
at least `(b - a) / (B.card + 1)` inside `[a, b]`. -/
lemma exists_empty_gap (B : Finset ℕ) :
    ∀ a b : ℕ, a < b →
      ∃ u v : ℕ, a ≤ u ∧ u < v ∧ v ≤ b ∧
        (∀ x ∈ B, ¬ (u < x ∧ x < v)) ∧
        b - a ≤ (B.card + 1) * (v - u) := by
  classical
  intro a b hab
  let E := B.filter (fun x => a < x ∧ x < b)
  suffices h : ∀ n : ℕ, ∀ (F : Finset ℕ) (a₀ b₀ : ℕ), F.card = n → a₀ < b₀ →
      (∀ x ∈ F, a₀ < x ∧ x < b₀) →
      ∃ u v : ℕ, a₀ ≤ u ∧ u < v ∧ v ≤ b₀ ∧
        (∀ x ∈ F, ¬ (u < x ∧ x < v)) ∧
        b₀ - a₀ ≤ (F.card + 1) * (v - u) by
    obtain ⟨u, v, hau, huv, hvb, hempty, hlen⟩ := h E.card E a b rfl hab (fun x hx => (Finset.mem_filter.mp hx).2)
    refine ⟨u, v, hau, huv, hvb, ?_, ?_⟩
    · intro x hx hxv
      exact hempty x (Finset.mem_filter.mpr ⟨hx, by omega, by omega⟩) hxv
    · have hcard : E.card ≤ B.card := Finset.card_filter_le _ _
      exact hlen.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hcard 1))
  intro n
  induction n with
  | zero =>
    intro F a₀ b₀ hcard hab₀ _
    have hF : F = ∅ := Finset.card_eq_zero.mp hcard
    subst hF
    exact ⟨a₀, b₀, le_rfl, hab₀, le_rfl, by simp, by simp⟩
  | succ n ih =>
    intro F a₀ b₀ hcard hab₀ hF
    have hne : F.Nonempty := Finset.card_pos.mp (by omega)
    let m := F.min' hne
    have hm_mem : m ∈ F := Finset.min'_mem F hne
    have hm_bounds := hF m hm_mem
    have hF'card : (F.erase m).card = n := by
      rw [Finset.card_erase_of_mem hm_mem, hcard]
      omega
    have hF'bounds : ∀ x ∈ F.erase m, m < x ∧ x < b₀ := by
      intro x hx
      have hxm : x ≠ m := (Finset.mem_erase.mp hx).1
      have hxF : x ∈ F := (Finset.mem_erase.mp hx).2
      have hle : m ≤ x := Finset.min'_le F x hxF
      exact ⟨lt_of_le_of_ne hle hxm.symm, (hF x hxF).2⟩
    obtain ⟨u', v', hmu', hu'v', hv'b, hempty', hlen'⟩ := ih (F.erase m) m b₀ hF'card hm_bounds.2 hF'bounds
    rw [hF'card] at hlen'
    by_cases hcmp : v' - u' ≤ m - a₀
    · refine ⟨a₀, m, le_rfl, hm_bounds.1, hm_bounds.2.le, ?_, ?_⟩
      · intro x hx hxm
        exact (not_lt.mpr (Finset.min'_le F x hx)) hxm.2
      · rw [hcard]
        have hsum : b₀ - a₀ = (m - a₀) + (b₀ - m) := by omega
        have hmul : (n + 1) * (v' - u') ≤ (n + 1) * (m - a₀) := Nat.mul_le_mul_left _ hcmp
        have hring : (n + 1 + 1) * (m - a₀) = (m - a₀) + (n + 1) * (m - a₀) := by ring
        omega
    · refine ⟨u', v', hm_bounds.1.le.trans hmu', hu'v', hv'b, ?_, ?_⟩
      · intro x hx hxv
        by_cases hxm : x = m
        · omega
        · exact hempty' x (Finset.mem_erase.mpr ⟨hxm, hx⟩) hxv
      · rw [hcard]
        have hsum : b₀ - a₀ = (m - a₀) + (b₀ - m) := by omega
        have hring : (n + 1 + 1) * (v' - u') = (v' - u') + (n + 1) * (v' - u') := by ring
        omega

lemma prod_one_sub_inv_primesLE_le (m : ℕ) (hm : 2 ≤ m) :
    (∏ p ∈ m.primesLE, (1 - 1 / (p : ℝ))) ≤ 1 / Real.log (m : ℝ) := by
  have hprod : (∏ p ∈ m.primesLE, (1 - 1 / (p : ℝ))) * eulerProduct m 1 = 1 := by
    unfold eulerProduct
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
    have hne : (1 : ℝ) - 1 / (p : ℝ) ≠ 0 := by
      have : 1 / (p : ℝ) ≤ 1 / 2 := by gcongr
      linarith
    have hrpow : (p : ℝ) ^ (-(1 : ℝ)) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg_one, one_div]
    rw [hrpow]
    exact mul_inv_cancel₀ hne
  have hlog_pos : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hlog_le := log_le_eulerProduct_one m
  have heul_pos : 0 < eulerProduct m 1 := hlog_pos.trans_le hlog_le
  have h1 : ∏ p ∈ m.primesLE, (1 - 1 / (p : ℝ)) = 1 / eulerProduct m 1 := by
    field_simp [heul_pos.ne']
    linarith
  rw [h1]
  exact one_div_le_one_div_of_le hlog_pos hlog_le

lemma primorial_le_exp_two (x : ℝ) (hx : 0 ≤ x) :
    (primorial ⌊x⌋₊ : ℝ) ≤ Real.exp (2 * x) := by
  have h1 : (primorial ⌊x⌋₊ : ℝ) ≤ (4 : ℝ) ^ ⌊x⌋₊ := by
    exact_mod_cast primorial_le_four_pow ⌊x⌋₊
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := by gcongr
      _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  calc
    (primorial ⌊x⌋₊ : ℝ) ≤ (4 : ℝ) ^ ⌊x⌋₊ := h1
    _ ≤ (Real.exp 2) ^ ⌊x⌋₊ := pow_le_pow_left₀ (by norm_num) h4 _
    _ = Real.exp (2 * (⌊x⌋₊ : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (2 * x) := Real.exp_le_exp.mpr (by nlinarith [Nat.floor_le hx])

end
end LongGapsBetweenPrimes

open scoped Nat
open Filter Set Asymptotics LongGapsBetweenPrimes

theorem OMA.disproof : ¬ (type_of% @Erdos32.erdos_32.variants.log_bound) := by
  classical
  rintro ⟨A, hcomp, hbigO⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hcomp
  obtain ⟨C₀, hC₀_ev⟩ := hbigO.bound
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hC₀_ev
  set C : ℝ := max C₀ 1
  have hC : 1 ≤ C := le_max_right _ _
  have hC0 : 0 < C := by linarith
  have hcount : ∀ N : ℕ, max N₁ 2 ≤ N →
      (((Finset.Icc 0 N).filter (· ∈ A)).card : ℝ) ≤ C * Real.log (N : ℝ) + 1 := by
    intro N hN
    have h1 := hN₁ N ((le_max_left _ _).trans hN)
    have hlogN : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg hlogN] at h1
    have hsub : (Finset.Icc 0 N).filter (· ∈ A) ⊆ insert 0 ((Finset.Icc 1 N).filter (· ∈ A)) := by
      intro a ha
      rcases Finset.mem_filter.mp ha with ⟨haI, haA⟩
      rcases Finset.mem_Icc.mp haI with ⟨_, haN⟩
      by_cases h0 : a = 0
      · subst h0; exact Finset.mem_insert_self 0 _
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, haN⟩, haA⟩)
    have hcard : ((Finset.Icc 0 N).filter (· ∈ A)).card ≤ ((Finset.Icc 1 N).filter (· ∈ A)).card + 1 :=
      (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    have hcardR : (((Finset.Icc 0 N).filter (· ∈ A)).card : ℝ) ≤
        (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) + 1 := by exact_mod_cast hcard
    have hC1 : C₀ * Real.log (N : ℝ) ≤ C * Real.log (N : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hlogN
    linarith
  have hfloor : Filter.Tendsto (fun x : ℝ => ⌊x⌋₊) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr (fun n => ⟨(n : ℝ), fun x hx => Nat.le_floor hx⟩)
  have hlog_floor : Filter.Tendsto (fun x : ℝ => Real.log (⌊x⌋₊ : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hfloor)
  have hexp_gap : Filter.Tendsto (fun x : ℝ => x * Real.exp (-x)) Filter.atTop (nhds 0) := by
    have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    simpa using h
  have hsmall_ratio : ∀ᶠ x : ℝ in Filter.atTop,
      (5 * C * x + 1) / Real.log (⌊x⌋₊ : ℝ) ≤ sieveDelta' * x := by
    have h1 := hlog_floor.eventually_ge_atTop (12 * C / sieveDelta')
    filter_upwards [h1, Filter.eventually_ge_atTop (1 : ℝ)] with x hlogx hx
    have hδ := sieveDelta'_pos
    have hlog_pos : 0 < Real.log (⌊x⌋₊ : ℝ) := (by positivity : 0 < 12 * C / sieveDelta').trans_le hlogx
    rw [div_le_iff₀ hlog_pos]
    have h6 : 6 * C * x ≤ (sieveDelta' * x) * (12 * C / sieveDelta') := by
      have : (sieveDelta' * x) * (12 * C / sieveDelta') = 12 * C * x := by field_simp
      nlinarith
    have h7 : (sieveDelta' * x) * (12 * C / sieveDelta') ≤ (sieveDelta' * x) * Real.log (⌊x⌋₊ : ℝ) :=
      mul_le_mul_of_nonneg_left hlogx (by positivity)
    nlinarith
  have hgap_dom : ∀ᶠ x : ℝ in Filter.atTop,
      100 * (5 * C * x + 2) * Real.exp (3 * x) ≤ Real.exp (4 * x) := by
    have h1 := hexp_gap.eventually_le_const (by positivity : (0 : ℝ) < 1 / (700 * C))
    filter_upwards [h1, Filter.eventually_ge_atTop (1 : ℝ)] with x hx_e hx
    have hmul : 700 * C * x * Real.exp (-x) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hx_e (by positivity : (0 : ℝ) ≤ 700 * C)
      have hsimp : 700 * C * (1 / (700 * C)) = 1 := by field_simp
      linarith
    have hle : 100 * (5 * C * x + 2) ≤ 700 * C * x := by nlinarith
    have hmul2 : 100 * (5 * C * x + 2) * Real.exp (-x) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hle (Real.exp_pos (-x)).le
      linarith
    have hexp4 := mul_le_mul_of_nonneg_right hmul2 (Real.exp_pos (4 * x)).le
    have hcombine : Real.exp (-x) * Real.exp (4 * x) = Real.exp (3 * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    linarith [show 100 * (5 * C * x + 2) * Real.exp (-x) * Real.exp (4 * x) =
      100 * (5 * C * x + 2) * Real.exp (3 * x) by rw [mul_assoc, hcombine]]
  have hev_all : ∀ᶠ x : ℝ in Filter.atTop,
      2 ≤ x ∧ 2 ≤ ⌊x⌋₊ ∧
      Real.log x ≥ 1 ∧
      max N₁ 2 ≤ ⌊Real.exp (4 * x)⌋₊ ∧
      2 * N₀ + 10 ≤ ⌊Real.exp (4 * x)⌋₊ ∧
      (5 * C * x + 1) / Real.log (⌊x⌋₊ : ℝ) ≤ sieveDelta' * x ∧
      100 * (5 * C * x + 2) * Real.exp (3 * x) ≤ Real.exp (4 * x) ∧
      (∀ k : ℕ, (((k + 1 : ℕ) : ℝ)) ≤ sieveDelta' * x →
        ∀ s : Fin (k + 1) → ℕ, Function.Injective s →
        (∀ i, (s i : ℝ) ≤ Real.exp (4 * x)) →
        ∀ b : ℕ, ∃ t : ℕ, 1 ≤ t ∧ t ≤ sieveT x ∧
          ∀ i : Fin (k + 1), ∃ p : ℕ, p.Prime ∧ sieveZ x < p ∧ p ≤ sieveY x ∧
            (p : ℤ) ∣ (b + primorial ⌊x⌋₊ * t : ℤ) - (s i : ℤ)) := by
    have hexp4 : Filter.Tendsto (fun x : ℝ => ⌊Real.exp (4 * x)⌋₊) Filter.atTop Filter.atTop :=
      hfloor.comp
        (Real.tendsto_exp_atTop.comp (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_id))
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ),
      hfloor.eventually_ge_atTop 2,
      Real.tendsto_log_atTop.eventually_ge_atTop 1,
      hexp4.eventually_ge_atTop (max N₁ 2),
      hexp4.eventually_ge_atTop (2 * N₀ + 10),
      hsmall_ratio, hgap_dom, large_shift_divisors]
      with x h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  obtain ⟨x, hx2, hfx2, hlx1, hX_N1, hX_N0, hsmall, hdom, hshift⟩ := hev_all.exists
  have hx0 : 0 < x := by linarith
  set X : ℕ := ⌊Real.exp (4 * x)⌋₊
  set m : ℕ := ⌊x⌋₊
  set Q : ℕ := primorial m
  set B : Finset ℕ := (Finset.Icc 0 X).filter (· ∈ A)
  have hX_le : (X : ℝ) ≤ Real.exp (4 * x) := Nat.floor_le (Real.exp_pos _).le
  have hX_gt : Real.exp (4 * x) - 1 < (X : ℝ) := by
    have := Nat.lt_floor_add_one (Real.exp (4 * x))
    linarith
  have hB_card : (B.card : ℝ) ≤ 5 * C * x + 1 := by
    have h1 := hcount X hX_N1
    have hlogX : Real.log (X : ℝ) ≤ 4 * x := by
      have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
      simpa only [Real.log_exp] using Real.log_le_log hXpos hX_le
    nlinarith
  -- Step 1: Find a large empty gap `(u, v)` in `[X / 2, X]` avoiding `A`.
  obtain ⟨u, v, hXu, huv, hvX, hempty, hgap_len⟩ :=
    exists_empty_gap B (X / 2) X (by omega)
  set L : ℕ := v - u
  have hL_ge : Real.exp (4 * x) / (4 * (5 * C * x + 2)) ≤ (L : ℝ) := by
    have h1 : ((X - X / 2 : ℕ) : ℝ) ≤ ((B.card + 1 : ℕ) : ℝ) * (L : ℝ) := by
      exact_mod_cast hgap_len
    have h2 : (X : ℝ) / 2 ≤ ((X - X / 2 : ℕ) : ℝ) := by
      have : X ≤ 2 * (X - X / 2) := by omega
      have : (X : ℝ) ≤ 2 * ((X - X / 2 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    have h3 : Real.exp (4 * x) / 4 ≤ (X : ℝ) / 2 := by
      have hexp_ge : (2 : ℝ) ≤ Real.exp (4 * x) := by
        have : (1 : ℝ) ≤ 4 * x := by linarith
        linarith [Real.add_one_le_exp (4 * x)]
      linarith
    have h4 : ((B.card + 1 : ℕ) : ℝ) ≤ 5 * C * x + 2 := by
      push_cast; linarith
    have hden : 0 < 5 * C * x + 2 := by positivity
    rw [div_le_iff₀ (by positivity)]
    have h5 : ((B.card + 1 : ℕ) : ℝ) * (L : ℝ) ≤ (5 * C * x + 2) * (L : ℝ) :=
      mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg _)
    nlinarith
  -- Step 2: Average / greedy choice of residue `r mod Q` leaving `≤ sieveDelta' * x` survivors.
  obtain ⟨a_res, ha_lt, hsurv_le⟩ :=
    greedy_residue_classes B m.primesLE (fun p hp => (Nat.prime_of_mem_primesLE hp).pos)
  obtain ⟨r, hrQ, hr_mod⟩ :=
    exists_crt_primes m.primesLE (fun p hp => Nat.prime_of_mem_primesLE hp) a_res
  set S : Finset ℕ := survivors B m.primesLE a_res
  have hS_card : (S.card : ℝ) ≤ sieveDelta' * x := by
    have h1 := prod_one_sub_inv_primesLE_le m hfx2
    have h2 : (S.card : ℝ) ≤ (B.card : ℝ) * (1 / Real.log (m : ℝ)) :=
      hsurv_le.trans (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _))
    have hlogm_pos : 0 < Real.log (m : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    have h3 : (B.card : ℝ) / Real.log (m : ℝ) ≤ (5 * C * x + 1) / Real.log (m : ℝ) :=
      div_le_div_of_nonneg_right hB_card hlogm_pos.le
    calc
      (S.card : ℝ) ≤ (B.card : ℝ) * (1 / Real.log (m : ℝ)) := h2
      _ = (B.card : ℝ) / Real.log (m : ℝ) := by ring
      _ ≤ (5 * C * x + 1) / Real.log (m : ℝ) := h3
      _ ≤ sieveDelta' * x := hsmall
  -- Step 3: Place baseline `b ≡ r (mod Q)` in `(u + L / 3, u + L / 3 + Q]`.
  set b : ℕ := r + Q * ((u + L / 3) / Q + 1)
  have hQ_pos : 0 < Q := primorial_pos m
  have hb_gt : u + L / 3 < b := by
    have hdiv := Nat.lt_mul_div_succ (u + L / 3) hQ_pos
    have : Q * ((u + L / 3) / Q + 1) = Q * ((u + L / 3) / Q + 1) := rfl
    omega
  have hb_le : b ≤ u + L / 3 + 2 * Q := by
    have hdiv := Nat.mul_div_le (u + L / 3) Q
    have hprim : ∏ p ∈ m.primesLE, p = Q := by
      unfold Q primorial
      apply Finset.prod_congr _ (fun _ _ => rfl)
      ext p
      simp [Nat.mem_primesLE, Nat.lt_succ_iff]
    have hrQ' : r < Q := hprim ▸ hrQ
    have hmul_eq : Q * ((u + L / 3) / Q + 1) = Q * ((u + L / 3) / Q) + Q := by ring
    dsimp only [b]
    omega
  -- Step 4: Apply large-shift lemma to `S` and `b`.
  have hex_t : ∃ t : ℕ, 1 ≤ t ∧ t ≤ sieveT x ∧
      ∀ a ∈ S, ∃ p : ℕ, p.Prime ∧ p ≤ sieveY x ∧ (p : ℤ) ∣ (b + Q * t : ℤ) - (a : ℤ) := by
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · have hTpos : 1 ≤ sieveT x := by
        have h1 := sieveT_lower hx2
        have h2 : (2 : ℝ) ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
        have h3 : (1 : ℝ) ≤ (sieveT x : ℝ) := by linarith
        exact_mod_cast h3
      exact ⟨1, le_rfl, hTpos, by simp [hSe]⟩
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hSne.card_pos.ne'
      let e : Fin (k + 1) ≃ S :=
        (Fintype.equivFinOfCardEq (by simpa using hk : Fintype.card S = k + 1)).symm
      let s : Fin (k + 1) → ℕ := fun i => (e i).val
      have hs_inj : Function.Injective s := Subtype.val_injective.comp e.injective
      have hs_le : ∀ i, (s i : ℝ) ≤ Real.exp (4 * x) := by
        intro i
        have hiB : s i ∈ B := (Finset.mem_filter.mp (e i).property).1
        have hiX : s i ≤ X := (Finset.mem_Icc.mp (Finset.mem_filter.mp hiB).1).2
        exact (by exact_mod_cast hiX : (s i : ℝ) ≤ X).trans hX_le
      obtain ⟨t, ht1, htT, hdiv⟩ := hshift k (by simpa [hk] using hS_card) s hs_inj hs_le b
      refine ⟨t, ht1, htT, ?_⟩
      intro a ha
      obtain ⟨p, hp, _, hpY, hpdvd⟩ := hdiv (e.symm ⟨a, ha⟩)
      refine ⟨p, hp, hpY, ?_⟩
      simpa [s] using hpdvd
  obtain ⟨t, ht1, htT, hS_div⟩ := hex_t
  -- Step 5: Set `N = b + Q * t` and show `N ∉ P + A`, contradicting `hN₀`.
  set N : ℕ := b + Q * t
  have hQ_le : (Q : ℝ) ≤ Real.exp (2 * x) := primorial_le_exp_two x hx0.le
  have hT_le : (sieveT x : ℝ) ≤ Real.exp x := Nat.floor_le (Real.exp_pos x).le
  have hY_le : (sieveY x : ℝ) ≤ Real.exp x := by
    have h1 : (sieveY x : ℝ) ≤ Real.exp (sieveUpperLog x) := Nat.floor_le (Real.exp_pos _).le
    have h2 : sieveUpperLog x ≤ x := by
      unfold sieveUpperLog
      have : (1 : ℝ) ≤ (Real.log x) ^ 5 := one_le_pow₀ hlx1
      exact div_le_self hx0.le this
    exact h1.trans (Real.exp_le_exp.mpr h2)
  have hL3_ge : Real.exp (4 * x) / (12 * (5 * C * x + 2)) ≤ (L : ℝ) / 3 := by
    have hdiv3 : Real.exp (4 * x) / (12 * (5 * C * x + 2)) = (Real.exp (4 * x) / (4 * (5 * C * x + 2))) / 3 := by
      have : (5 * C * x + 2 : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    linarith [hL_ge]
  have hQt_small : ((2 * Q + Q * sieveT x : ℕ) : ℝ) < (L : ℝ) / 3 := by
    have h1 : ((2 * Q + Q * sieveT x : ℕ) : ℝ) ≤ 3 * Real.exp (3 * x) := by
      push_cast
      have hqt : (Q : ℝ) * (sieveT x : ℝ) ≤ Real.exp (2 * x) * Real.exp x :=
        mul_le_mul hQ_le hT_le (Nat.cast_nonneg _) (Real.exp_pos _).le
      have hcomb : Real.exp (2 * x) * Real.exp x = Real.exp (3 * x) := by
        rw [← Real.exp_add]; congr 1; ring
      have h2q : (Q : ℝ) ≤ Real.exp (3 * x) :=
        hQ_le.trans (Real.exp_le_exp.mpr (by linarith))
      linarith
    have h2 : 3 * Real.exp (3 * x) < Real.exp (4 * x) / (12 * (5 * C * x + 2)) := by
      rw [lt_div_iff₀ (by positivity)]
      have : (36 : ℝ) * (5 * C * x + 2) * Real.exp (3 * x) <
          100 * (5 * C * x + 2) * Real.exp (3 * x) := by
        have : 0 < (5 * C * x + 2) * Real.exp (3 * x) := by positivity
        linarith
      linarith [hdom]
    linarith [hL3_ge]
  have hY_small : (sieveY x : ℝ) < (L : ℝ) / 3 := by
    have h1 : (sieveY x : ℝ) ≤ Real.exp (3 * x) :=
      hY_le.trans (Real.exp_le_exp.mpr (by linarith))
    have h2 : Real.exp (3 * x) < Real.exp (4 * x) / (12 * (5 * C * x + 2)) := by
      rw [lt_div_iff₀ (by positivity)]
      have : (12 : ℝ) * (5 * C * x + 2) * Real.exp (3 * x) <
          100 * (5 * C * x + 2) * Real.exp (3 * x) := by
        have : 0 < (5 * C * x + 2) * Real.exp (3 * x) := by positivity
        linarith
      linarith [hdom]
    linarith [hL3_ge]
  have hm_small : (m : ℝ) < (L : ℝ) / 3 := by
    have hm_le : (m : ℝ) ≤ Real.exp (3 * x) := by
      calc
        (m : ℝ) ≤ x := Nat.floor_le hx0.le
        _ ≤ Real.exp (3 * x) := by linarith [Real.add_one_le_exp (3 * x)]
    have h2 : Real.exp (3 * x) < Real.exp (4 * x) / (12 * (5 * C * x + 2)) := by
      rw [lt_div_iff₀ (by positivity)]
      have : (12 : ℝ) * (5 * C * x + 2) * Real.exp (3 * x) <
          100 * (5 * C * x + 2) * Real.exp (3 * x) := by
        have : 0 < (5 * C * x + 2) * Real.exp (3 * x) := by positivity
        linarith
      linarith [hdom]
    linarith [hL3_ge]
  have hN_gt : u + L / 3 < N := by omega
  have hN_lt : N < v := by
    have hQt_nat : 2 * Q + Q * sieveT x < L / 3 + 1 := by
      have hcast : ((2 * Q + Q * sieveT x : ℕ) : ℝ) < ((L / 3 + 1 : ℕ) : ℝ) := by
        have hL3 : (L : ℝ) / 3 ≤ ((L / 3 + 1 : ℕ) : ℝ) := by
          have : L ≤ 3 * (L / 3 + 1) := by omega
          have : (L : ℝ) ≤ 3 * ((L / 3 + 1 : ℕ) : ℝ) := by exact_mod_cast this
          linarith
        exact hQt_small.trans_le hL3
      exact_mod_cast hcast
    have hQtle : Q * t ≤ Q * sieveT x := Nat.mul_le_mul_left Q htT
    omega
  have hN_ge_N0 : N₀ ≤ N := by omega
  obtain ⟨p, hp_prime, a, haA, hN_eq⟩ := hN₀ N hN_ge_N0
  have ha_lt_v : a < v := by omega
  have ha_le_u : a ≤ u := by
    by_contra hgt
    have h1 : u < a := by omega
    have haB : a ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩, haA⟩
    exact hempty a haB ⟨h1, ha_lt_v⟩
  have haB : a ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩, haA⟩
  have hp_gt_L3 : L / 3 < p := by omega
  have hp_gt_Y : sieveY x < p := by
    have : (sieveY x : ℝ) < (p : ℝ) := by
      have hL3p : (L : ℝ) / 3 ≤ (p : ℝ) := by
        have : L ≤ 3 * p := by omega
        have : (L : ℝ) ≤ 3 * (p : ℝ) := by exact_mod_cast this
        linarith
      exact hY_small.trans_le hL3p
    exact_mod_cast this
  have hp_gt_m : m < p := by
    have : (m : ℝ) < (p : ℝ) := by
      have hL3p : (L : ℝ) / 3 ≤ (p : ℝ) := by
        have : L ≤ 3 * p := by omega
        have : (L : ℝ) ≤ 3 * (p : ℝ) := by exact_mod_cast this
        linarith
      exact hm_small.trans_le hL3p
    exact_mod_cast this
  by_cases haS : a ∈ S
  · obtain ⟨q, hq_prime, hqY, hqdvd⟩ := hS_div a haS
    have hqdvd_p : (q : ℤ) ∣ (p : ℤ) := by
      have hp_int : (p : ℤ) = (b + Q * t : ℤ) - (a : ℤ) := by
        have : p + a = b + Q * t := by omega
        omega
      rwa [← hp_int] at hqdvd
    have hq_nat : q ∣ p := Int.ofNat_dvd.mp hqdvd_p
    rcases (Nat.dvd_prime hp_prime).mp hq_nat with hq1 | hqp
    · exact hq_prime.ne_one hq1
    · omega
  · have hnot_all : ¬ ∀ q ∈ m.primesLE, a % q ≠ a_res q := by
      intro hall
      exact haS (Finset.mem_filter.mpr ⟨haB, hall⟩)
    push Not at hnot_all
    obtain ⟨q, hqm, ha_eq⟩ := hnot_all
    have hq_prime : q.Prime := Nat.prime_of_mem_primesLE hqm
    have hq_le_m : q ≤ m := (Nat.mem_primesLE.mp hqm).1
    have hq_dvd_Q : q ∣ Q := hq_prime.dvd_primorial_iff.mpr hq_le_m
    have hN_mod_q : N % q = r % q := by
      obtain ⟨k, hk⟩ := hq_dvd_Q
      have h1 : N = r + q * (k * ((u + L / 3) / Q + 1 + t)) := by
        dsimp only [N, b]
        rw [hk]
        ring
      rw [h1, Nat.add_mul_mod_self_left]
    have ha_mod_q : a % q = r % q := by
      have h1 := hr_mod q hqm
      have h2 := Nat.mod_eq_of_lt (ha_lt q hqm)
      omega
    have hq_dvd_p : q ∣ p := by
      have h1 : p + a ≡ 0 + a [MOD q] := by
        change (p + a) % q = (0 + a) % q
        rw [zero_add, ← hN_eq, hN_mod_q, ha_mod_q]
      have h2 : p % q = 0 := by
        simpa [Nat.ModEq] using Nat.ModEq.add_right_cancel' a h1
      exact Nat.dvd_of_mod_eq_zero h2
    rcases (Nat.dvd_prime hp_prime).mp hq_dvd_p with hq1 | hqp
    · exact hq_prime.ne_one hq1
    · omega
