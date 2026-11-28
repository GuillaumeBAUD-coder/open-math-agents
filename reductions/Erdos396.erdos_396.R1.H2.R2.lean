import OMAReductions.R_Erdos396_erdos_396_R1
import Mathlib

/-!
Kummer base-p carry reduction for Erdos problem 396 on k >= 5.
-/

namespace OMA.R_Erdos396_erdos_396_R1_H2_R2

lemma descFactorial_ne_zero_of_le {n m : ℕ} (h : m ≤ n) : Nat.descFactorial n m ≠ 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.descFactorial_succ]
    exact mul_ne_zero (by omega) (ih (by omega))

lemma factorization_descFactorial_eq_sum {n m : ℕ} (h : m ≤ n) (p : ℕ) :
    (Nat.descFactorial n m).factorization p =
      ∑ i ∈ Finset.range m, (n - i).factorization p := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.descFactorial_succ,
      Nat.factorization_mul (by omega) (descFactorial_ne_zero_of_le (by omega)),
      Finsupp.coe_add, Pi.add_apply, Finset.sum_range_succ, ih (by omega), add_comm]

lemma not_dvd_other_shift {n k p i j : ℕ} (hnk : k + 1 ≤ n) (hpk : k + 1 < p)
    (hi : i < k + 1) (hj : j < k + 1) (hne : i ≠ j) (hdiv : p ∣ n - i) :
    ¬ p ∣ n - j := by
  rintro ⟨b, hb⟩
  obtain ⟨a, ha⟩ := hdiv
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hd : p ∣ j - i := ⟨a - b, by rw [Nat.mul_sub]; omega⟩
    have hle : p ≤ j - i := Nat.le_of_dvd (by omega) hd
    omega
  · have hd : p ∣ i - j := ⟨b - a, by rw [Nat.mul_sub]; omega⟩
    have hle : p ≤ i - j := Nat.le_of_dvd (by omega) hd
    omega

/-- Kummer carry lower bound for the p-adic valuation of the central binomial coefficient. -/
def H1 : Prop :=
  ∀ (p n : ℕ), p.Prime →
    ((Finset.Icc 1 (Nat.log p (2 * n))).filter (fun j => p ^ j ≤ 2 * (n % p ^ j))).card ≤
      (Nat.centralBinom n).factorization p

/-- Existence of n >= k + 1 meeting the Kummer carry bounds for small and large primes. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ n : ℕ, k + 1 ≤ n ∧
    (∀ p : ℕ, p.Prime → p ≤ k + 1 →
      (Nat.factorial (k + 1)).factorization p + (Nat.choose n (k + 1)).factorization p ≤
        ((Finset.Icc 1 (Nat.log p (2 * n))).filter (fun j => p ^ j ≤ 2 * (n % p ^ j))).card) ∧
    (∀ p : ℕ, p.Prime → k + 1 < p → ∀ i : ℕ, i ≤ k →
      (n - i).factorization p ≤
        ((Finset.Icc 1 (Nat.log p (2 * n))).filter (fun j => p ^ j ≤ 2 * (n % p ^ j))).card)

/-- Deduction of the k >= 5 divisibility statement from the Kummer carry hypotheses. -/
theorem main : H1 → H2 → OMA.R_Erdos396_erdos_396_R1.H2 := by
  intro h1 h2 k hk5
  obtain ⟨n, hnk, hsmall, hlarge⟩ := h2 k hk5
  refine ⟨n, ?_⟩
  rw [← Nat.factorization_le_iff_dvd (descFactorial_ne_zero_of_le hnk)
    (ne_of_gt (Nat.centralBinom_pos n))]
  intro p
  by_cases hp : p.Prime
  · by_cases hpk : p ≤ k + 1
    · rw [Nat.descFactorial_eq_factorial_mul_choose,
        Nat.factorization_mul (Nat.factorial_ne_zero _) (ne_of_gt (Nat.choose_pos hnk)),
        Finsupp.coe_add, Pi.add_apply]
      exact (hsmall p hp hpk).trans (h1 p n hp)
    · have hpk' : k + 1 < p := by omega
      rw [factorization_descFactorial_eq_sum hnk p]
      by_cases hex : ∃ i ∈ Finset.range (k + 1), p ∣ n - i
      · obtain ⟨i₀, hi₀, hdiv₀⟩ := hex
        rw [Finset.sum_eq_single i₀]
        · rw [Finset.mem_range] at hi₀
          exact (hlarge p hp hpk' i₀ (by omega)).trans (h1 p n hp)
        · intro j hj hne
          rw [Finset.mem_range] at hi₀ hj
          exact Nat.factorization_eq_zero_of_not_dvd
            (not_dvd_other_shift hnk hpk' hi₀ hj hne.symm hdiv₀)
        · intro hnot
          exact absurd hi₀ hnot
      · have hzero : ∑ i ∈ Finset.range (k + 1), (n - i).factorization p = 0 :=
          Finset.sum_eq_zero fun i hi =>
            Nat.factorization_eq_zero_of_not_dvd fun hdiv => hex ⟨i, hi, hdiv⟩
        rw [hzero]
        exact Nat.zero_le _
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

end OMA.R_Erdos396_erdos_396_R1_H2_R2
