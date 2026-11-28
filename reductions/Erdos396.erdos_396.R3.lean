import FormalConjectures.ErdosProblems.«396»
import Mathlib

/-!
# Small-prime congruence reduction for Erdos Problem 396

Splits divisibility of the central binomial coefficient by a descending factorial into:
- `H1`: a prime power dividing `n + 1` bounds the prime valuation of the central binomial.
- `H2`: existence of `n > k` with `n + 1` divisible by `(k + 1)`-th powers of all primes
  up to `k + 1`, while primes larger than `k + 1` satisfy single-shift valuation bounds.
-/

namespace OMA.R_Erdos396_erdos_396_R3

private lemma lt_two_pow_self_aux (m : ℕ) : m < 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Nat.pow_succ]
    omega

private lemma descFactorial_ne_zero_of_le {n m : ℕ} (h : m ≤ n) :
    n.descFactorial m ≠ 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.descFactorial_succ]
    exact mul_ne_zero (by omega) (ih (by omega))

private lemma descFactorial_factorization_eq_sum {n m : ℕ} (h : m ≤ n) (p : ℕ) :
    (n.descFactorial m).factorization p = ∑ i ∈ Finset.range m, (n - i).factorization p := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.descFactorial_succ, Finset.sum_range_succ, ← ih (by omega),
      Nat.factorization_mul (by omega) (descFactorial_ne_zero_of_le (by omega)),
      Finsupp.coe_add, Pi.add_apply, Nat.add_comm]

private lemma factorial_factorization_eq_sum (m p : ℕ) :
    (Nat.factorial m).factorization p = ∑ i ∈ Finset.range m, (i + 1).factorization p := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.factorial_succ, Finset.sum_range_succ, ← ih,
      Nat.factorization_mul (by omega) (Nat.factorial_ne_zero m),
      Finsupp.coe_add, Pi.add_apply, Nat.add_comm]

private lemma valuation_sub_eq_of_pow_dvd {p k n i : ℕ} (hp : p.Prime)
    (hik : i ≤ k) (hkn : k < n) (hdvd : p ^ (k + 1) ∣ n + 1) :
    (n - i).factorization p = (i + 1).factorization p := by
  have hilt : i + 1 < p ^ (k + 1) := by
    have h1 : k + 1 < 2 ^ (k + 1) := lt_two_pow_self_aux (k + 1)
    have h2 : 2 ^ (k + 1) ≤ p ^ (k + 1) := Nat.pow_le_pow_left hp.two_le (k + 1)
    omega
  have hb_lt : (i + 1).factorization p < k + 1 := by
    by_contra hge
    have hd : p ^ (k + 1) ∣ i + 1 :=
      (hp.pow_dvd_iff_le_factorization (by omega)).mpr (by omega)
    have hle : p ^ (k + 1) ≤ i + 1 := Nat.le_of_dvd (by omega) hd
    omega
  have hsum : (n - i) + (i + 1) = n + 1 := by omega
  have hdvd_b : p ^ ((i + 1).factorization p) ∣ (n - i) + (i + 1) := by
    rw [hsum]
    exact (pow_dvd_pow p (by omega)).trans hdvd
  have hdvd_b1 : p ^ ((i + 1).factorization p + 1) ∣ (n - i) + (i + 1) := by
    rw [hsum]
    exact (pow_dvd_pow p (by omega)).trans hdvd
  have hi_b : p ^ ((i + 1).factorization p) ∣ i + 1 :=
    (hp.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl
  have hni_b : p ^ ((i + 1).factorization p) ∣ n - i :=
    (Nat.dvd_add_iff_left hi_b).mpr hdvd_b
  have hle1 : (i + 1).factorization p ≤ (n - i).factorization p :=
    (hp.pow_dvd_iff_le_factorization (by omega)).mp hni_b
  have hle2 : (n - i).factorization p ≤ (i + 1).factorization p := by
    by_contra hgt
    have hni_b1 : p ^ ((i + 1).factorization p + 1) ∣ n - i :=
      (hp.pow_dvd_iff_le_factorization (by omega)).mpr (by omega)
    have hi_b1 : p ^ ((i + 1).factorization p + 1) ∣ i + 1 :=
      (Nat.dvd_add_iff_right hni_b1).mpr hdvd_b1
    have hbad : (i + 1).factorization p + 1 ≤ (i + 1).factorization p :=
      (hp.pow_dvd_iff_le_factorization (by omega)).mp hi_b1
    omega
  exact le_antisymm hle2 hle1

private lemma large_prime_sum_le {p k n B : ℕ} (hp : p.Prime)
    (hpk : k + 1 < p) (hkn : k < n)
    (hB : ∀ i : ℕ, i ≤ k → (n - i).factorization p ≤ B) :
    (∑ i ∈ Finset.range (k + 1), (n - i).factorization p) ≤ B := by
  by_cases hex : ∃ i ∈ Finset.range (k + 1), (n - i).factorization p ≠ 0
  · rcases hex with ⟨i0, hi0_mem, hi0_ne⟩
    have hi0_lt : i0 < k + 1 := Finset.mem_range.mp hi0_mem
    have hsingle : (∑ i ∈ Finset.range (k + 1), (n - i).factorization p) =
        (n - i0).factorization p := by
      refine Finset.sum_eq_single i0 ?_ ?_
      · intro j hj_mem hj_ne
        have hj_lt : j < k + 1 := Finset.mem_range.mp hj_mem
        by_contra hj_nz
        have hd_i0 : p ^ 1 ∣ n - i0 :=
          (hp.pow_dvd_iff_le_factorization (show n - i0 ≠ 0 by omega)).mpr (by omega)
        rw [pow_one] at hd_i0
        have hd_j : p ^ 1 ∣ n - j :=
          (hp.pow_dvd_iff_le_factorization (show n - j ≠ 0 by omega)).mpr (by omega)
        rw [pow_one] at hd_j
        by_cases hlt : i0 < j
        · have hdiff : (n - j) + (j - i0) = n - i0 := by omega
          rw [← hdiff] at hd_i0
          have hd_sub : p ∣ j - i0 := (Nat.dvd_add_iff_right hd_j).mpr hd_i0
          have hple : p ≤ j - i0 := Nat.le_of_dvd (by omega) hd_sub
          omega
        · have hdiff : (n - i0) + (i0 - j) = n - j := by omega
          rw [← hdiff] at hd_j
          have hd_sub : p ∣ i0 - j := (Nat.dvd_add_iff_right hd_i0).mpr hd_j
          have hple : p ≤ i0 - j := Nat.le_of_dvd (by omega) hd_sub
          omega
      · intro hnot
        exact absurd hi0_mem hnot
    rw [hsingle]
    exact hB i0 (by omega)
  · have hzero : ∀ i ∈ Finset.range (k + 1), (n - i).factorization p = 0 := by
      intro i hi
      by_contra hnz
      exact hex ⟨i, hi, hnz⟩
    rw [Finset.sum_eq_zero hzero]
    exact Nat.zero_le B

/-- Prime-power divisibility of `n + 1` lower-bounds the central binomial valuation. -/
def H1 : Prop :=
  ∀ (p a n : ℕ), p.Prime → p ^ a ∣ n + 1 → a ≤ (Nat.centralBinom n).factorization p

/-- Existence of `n > k` eliminating small primes via `n + 1` and bounding large primes. -/
def H2 : Prop :=
  ∀ k : ℕ, ∃ n : ℕ, k < n ∧
    (∀ p : ℕ, p.Prime → p ≤ k + 1 → p ^ (k + 1) ∣ n + 1) ∧
    (∀ p : ℕ, p.Prime → k + 1 < p → ∀ i : ℕ, i ≤ k →
      (n - i).factorization p ≤ (Nat.centralBinom n).factorization p)

/-- Combining `H1` and `H2` yields divisibility of the central binomial coefficient. -/
theorem main : H1 → H2 → type_of% @Erdos396.erdos_396 := by
  intro h1 h2 k
  obtain ⟨n, hkn, hsmall, hlarge⟩ := h2 k
  refine ⟨n, ?_⟩
  rw [← Nat.factorization_le_iff_dvd (descFactorial_ne_zero_of_le (by omega))
    (Nat.ne_of_gt (Nat.centralBinom_pos n))]
  intro p
  by_cases hp : p.Prime
  · rw [descFactorial_factorization_eq_sum (by omega) p]
    by_cases hpk : p ≤ k + 1
    · have hsum_eq :
          (∑ i ∈ Finset.range (k + 1), (n - i).factorization p) =
            ∑ i ∈ Finset.range (k + 1), (i + 1).factorization p := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hik : i ≤ k := by
          rw [Finset.mem_range] at hi
          omega
        exact valuation_sub_eq_of_pow_dvd hp hik hkn (hsmall p hp hpk)
      rw [hsum_eq, ← factorial_factorization_eq_sum (k + 1) p]
      exact ((Nat.factorization_factorial_le_div_pred hp (k + 1)).trans
        (Nat.div_le_self (k + 1) (p - 1))).trans (h1 p (k + 1) n hp (hsmall p hp hpk))
    · exact large_prime_sum_le hp (by omega) hkn (hlarge p hp (by omega))
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

end OMA.R_Erdos396_erdos_396_R3
