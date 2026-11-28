import OMAStatements.S_oeis_a060693
import Mathlib

namespace OMA.P_oeis_a060693

-- Key binomial cancellation: (n + 1 - k) ∣ C(n, k) * C(2n - k, n) for k ≤ n!
private lemma dvd_choose_mul_choose (n k : ℕ) (hk : k ≤ n) :
    (n + 1 - k) ∣ Nat.choose n k * Nat.choose (2 * n - k) n := by
  -- Note: C(2n - k, n) = C(2n - k, n - k), and C(n, k) * C(2n - k, n - k) = C(2n - k, k) * C(2n - 2k, n - k)!
  -- Even simpler: (n - k + 1) * C(n, k) * C(2n - k, n) = ...
  -- Use Catalan divisibility: (m + 1) ∣ C(2m, m) with m = n - k!
  -- Wait: C(n, k) * C(2n - k, n) = C(2n - k, k) * C(2*(n - k), n - k)!
  have hident : Nat.choose n k * Nat.choose (2 * n - k) n =
      Nat.choose (2 * n - k) k * Nat.choose (2 * (n - k)) (n - k) := by
    have h1 := Nat.choose_mul (n := 2 * n - k) (k := n) (s := k) hk
    have h3 : 2 * n - k - k = 2 * (n - k) := by omega
    rw [mul_comm (Nat.choose n k), h1, h3]
  rw [hident, show n + 1 - k = (n - k) + 1 by omega]
  have hcat : (n - k + 1) ∣ Nat.choose (2 * (n - k)) (n - k) := by
    rw [← Nat.centralBinom_eq_two_mul_choose]
    exact Nat.succ_dvd_centralBinom (n - k)
  exact dvd_mul_of_dvd_right hcat _

-- Core alternating binomial sum via Polynomial ℤ:
-- ∑_{k=0}^n (-1)^k * C(n, k) * C(M - k, r) = C(M - n, r - n) for n ≤ M, n ≤ r!
private lemma alt_choose_sum (n M r : ℕ) (hnM : n ≤ M) (hnr : n ≤ r) :
    ∑ k ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ k * (Nat.choose n k : ℤ) * (Nat.choose (M - k) r : ℤ) =
    (Nat.choose (M - n) (r - n) : ℤ) := by
  have hpoly : ∑ k ∈ Finset.range (n + 1),
      Polynomial.C ((-1 : ℤ) ^ k * (Nat.choose n k : ℤ)) * (1 + Polynomial.X) ^ (M - k) =
      (1 + Polynomial.X) ^ (M - n) * Polynomial.X ^ n := by
    have hfac : ∀ k ∈ Finset.range (n + 1),
        Polynomial.C ((-1 : ℤ) ^ k * (Nat.choose n k : ℤ)) * (1 + Polynomial.X) ^ (M - k) =
        (1 + Polynomial.X) ^ (M - n) *
          ((1 + Polynomial.X) ^ (n - k) * ((-1 : Polynomial ℤ) ^ k * (Nat.choose n k : Polynomial ℤ))) := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hpow : (1 + Polynomial.X : Polynomial ℤ) ^ (M - k) =
          (1 + Polynomial.X) ^ (M - n) * (1 + Polynomial.X) ^ (n - k) := by
        rw [← pow_add, show M - n + (n - k) = M - k by omega]
      rw [hpow, map_mul, map_pow, map_neg, map_one, map_natCast]
      ring
    rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum]
    congr 1
    have hbin := add_pow (-1 : Polynomial ℤ) (1 + Polynomial.X) n
    have hsum_eq : (-1 + (1 + Polynomial.X) : Polynomial ℤ) ^ n = Polynomial.X ^ n := by
      congr 1; ring
    rw [hsum_eq] at hbin
    rw [hbin]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hc := congr_arg (fun P => Polynomial.coeff P r) hpoly
  rw [Polynomial.finsetSum_coeff] at hc
  have hlhs : ∀ k ∈ Finset.range (n + 1),
      Polynomial.coeff (Polynomial.C ((-1 : ℤ) ^ k * (Nat.choose n k : ℤ)) * (1 + Polynomial.X) ^ (M - k)) r =
      (-1 : ℤ) ^ k * (Nat.choose n k : ℤ) * (Nat.choose (M - k) r : ℤ) := by
    intro k _
    rw [Polynomial.coeff_C_mul, add_comm (1 : Polynomial ℤ), Polynomial.coeff_X_add_one_pow]
  have hrhs : Polynomial.coeff ((1 + Polynomial.X : Polynomial ℤ) ^ (M - n) * Polynomial.X ^ n) r =
      (Nat.choose (M - n) (r - n) : ℤ) := by
    rw [mul_comm, Polynomial.coeff_X_pow_mul', if_pos hnr, add_comm (1 : Polynomial ℤ),
      Polynomial.coeff_X_add_one_pow]
  rw [Finset.sum_congr rfl hlhs, hrhs] at hc
  exact hc

private theorem main_proved :
    ∀ n : ℕ,
      ∑ k ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ k *
          ((Nat.choose n k * Nat.choose (2 * n - k) n / (n + 1 - k) : ℕ) : ℤ) *
          ((n + 1 - k : ℕ) : ℤ) ^ 2 =
        1 + (n : ℤ) + (n : ℤ) ^ 2 := by
  intro n
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ k *
        ((Nat.choose n k * Nat.choose (2 * n - k) n / (n + 1 - k) : ℕ) : ℤ) *
        ((n + 1 - k : ℕ) : ℤ) ^ 2 =
      ((n : ℤ) + 1) * ((-1 : ℤ) ^ k * (Nat.choose n k : ℤ) * (Nat.choose (2 * n + 1 - k) (n + 1) : ℤ)) -
      (n : ℤ) * ((-1 : ℤ) ^ k * (Nat.choose n k : ℤ) * (Nat.choose (2 * n - k) n : ℤ)) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hdvd := dvd_choose_mul_choose n k hkn
    have hdiv : ((Nat.choose n k * Nat.choose (2 * n - k) n / (n + 1 - k) : ℕ) : ℤ) * ((n + 1 - k : ℕ) : ℤ) =
        (Nat.choose n k : ℤ) * (Nat.choose (2 * n - k) n : ℤ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    have hstep : ((2 * n + 1 - k : ℕ) : ℤ) * (Nat.choose (2 * n - k) n : ℤ) =
        ((n : ℤ) + 1) * (Nat.choose (2 * n + 1 - k) (n + 1) : ℤ) := by
      have hnat : (2 * n - k + 1) * Nat.choose (2 * n - k) n =
          (n + 1) * Nat.choose (2 * n - k + 1) (n + 1) := by
        have h1 := Nat.choose_mul (n := 2 * n - k + 1) (k := n + 1) (s := 1) (by omega)
        simp only [Nat.choose_one_right, Nat.add_sub_cancel] at h1
        linarith
      have heq : 2 * n + 1 - k = 2 * n - k + 1 := by omega
      rw [heq]
      exact_mod_cast hnat
    have hsub : ((n + 1 - k : ℕ) : ℤ) = ((2 * n + 1 - k : ℕ) : ℤ) - (n : ℤ) := by
      omega
    calc (-1 : ℤ) ^ k *
            ((Nat.choose n k * Nat.choose (2 * n - k) n / (n + 1 - k) : ℕ) : ℤ) *
            ((n + 1 - k : ℕ) : ℤ) ^ 2
        = (-1 : ℤ) ^ k *
            (((Nat.choose n k * Nat.choose (2 * n - k) n / (n + 1 - k) : ℕ) : ℤ) * ((n + 1 - k : ℕ) : ℤ)) *
            ((n + 1 - k : ℕ) : ℤ) := by ring
      _ = (-1 : ℤ) ^ k * ((Nat.choose n k : ℤ) * (Nat.choose (2 * n - k) n : ℤ)) *
            (((2 * n + 1 - k : ℕ) : ℤ) - (n : ℤ)) := by rw [hdiv, hsub]
      _ = (-1 : ℤ) ^ k * (Nat.choose n k : ℤ) *
            (((2 * n + 1 - k : ℕ) : ℤ) * (Nat.choose (2 * n - k) n : ℤ)) -
          (n : ℤ) * ((-1 : ℤ) ^ k * (Nat.choose n k : ℤ) * (Nat.choose (2 * n - k) n : ℤ)) := by ring
      _ = (-1 : ℤ) ^ k * (Nat.choose n k : ℤ) *
            (((n : ℤ) + 1) * (Nat.choose (2 * n + 1 - k) (n + 1) : ℤ)) -
          (n : ℤ) * ((-1 : ℤ) ^ k * (Nat.choose n k : ℤ) * (Nat.choose (2 * n - k) n : ℤ)) := by rw [hstep]
      _ = ((n : ℤ) + 1) * ((-1 : ℤ) ^ k * (Nat.choose n k : ℤ) * (Nat.choose (2 * n + 1 - k) (n + 1) : ℤ)) -
          (n : ℤ) * ((-1 : ℤ) ^ k * (Nat.choose n k : ℤ) * (Nat.choose (2 * n - k) n : ℤ)) := by ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [alt_choose_sum n (2 * n + 1) (n + 1) (by omega) (by omega),
      alt_choose_sum n (2 * n) n (by omega) (le_refl n)]
  have h1 : 2 * n + 1 - n = n + 1 := by omega
  have h2 : n + 1 - n = 1 := by omega
  have h3 : 2 * n - n = n := by omega
  have h4 : n - n = 0 := Nat.sub_self n
  rw [h1, h2, h3, h4, Nat.choose_one_right, Nat.choose_zero_right]
  push_cast
  ring

end OMA.P_oeis_a060693

theorem OMA.solution : type_of% @OMA.S_oeis_a060693.main :=
  OMA.P_oeis_a060693.main_proved
