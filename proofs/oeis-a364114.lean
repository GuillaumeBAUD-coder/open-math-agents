import OMAStatements.S_oeis_a364114
import Mathlib

/-!
# Proof of the four supercongruences for row 3 of Bala's Legendre array (OEIS A364114)

Credit: Daniel Whorlow (@draonbioetl)

Proof overview:
1. Binomial convolution triple-sum identities (`OMA_A364114_Part1`):
   - `a(N) = ∑_{i+j+l ≤ N} C(4N - i - j - l, 3N) C(N, i)^2 C(N, j)^2 C(N, l)^2`
   - `a(N - 1) = ∑_{i+j+l < N} (-1)^(N-1-i-j-l) C(3N - 1, N - 1 - i - j - l) C(N + i - 1, i)^2 C(N + j - 1, j)^2 C(N + l - 1, l)^2`
2. Kazandzidis's theorem (`OMA_A364114_Part2`) for all primes `p ≥ 5`:
   `p^(3 + v_p(a) + v_p(b) + v_p(a-b) + v_p(C(a,b))) ∣ (C(ap, bp) - C(a, b))`.
3. Block-constancy 1D sum cancellation (`OMA_A364114_Part3`) via `(ZMod (p^d))ˣ` unit-square vanishing.
4. Prime-level `mod p^5` harmonic sum relations (`OMA_A364114_Part4`) for all primes `p ≥ 7`,
   showing `a(p) ≡ 7 + 33 p H_1 (mod p^5)` and `a(p - 1) ≡ 1 + 9 p H_1 (mod p^5)`,
   which uniformly implies both `3 a(p) ≡ 10 + 11 a(p - 1) (mod p^5)` and
   `a(p)^21 ≡ 7^21 a(p - 1)^11 (mod p^5)`.
-/

namespace OMA_A364114_Part1

open Finset Polynomial

noncomputable def a_def (n : ℕ) : ℕ :=
  let L : Polynomial ℕ := ∑ j ∈ Finset.range (n + 1),
    Polynomial.monomial j (n.choose j * (n + j).choose j)
  ∑ j ∈ Finset.range (n + 1), n.choose j * (L ^ 3).coeff j

lemma choose_mul_choose_eq (n k j : ℕ) (hjk : j ≤ k) :
    n.choose j * (n - j).choose (k - j) = n.choose k * k.choose j := by
  exact (Nat.choose_mul (n := n) hjk).symm

lemma sum_choose_sq_mul_choose (n k : ℕ) :
    ∑ j ∈ range (k + 1), (n.choose j) ^ 2 * (n - j).choose (k - j) =
      n.choose k * (n + k).choose k := by
  have hterm : ∀ j ∈ range (k + 1),
      (n.choose j) ^ 2 * (n - j).choose (k - j) =
        n.choose k * (n.choose j * k.choose (k - j)) := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [sq, mul_assoc, choose_mul_choose_eq n k j hjk, Nat.choose_symm hjk]
    ring
  rw [sum_congr rfl hterm, ← mul_sum]
  congr 1
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => n.choose i * k.choose j) k,
      ← Nat.add_choose_eq n k k]

lemma L_eq_sum_sq (n : ℕ) :
    (∑ j ∈ range (n + 1), monomial j (n.choose j * (n + j).choose j)) =
      ∑ j ∈ range (n + 1), C ((n.choose j) ^ 2) * X ^ j * (1 + X) ^ (n - j) := by
  ext k
  rw [Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  have hL : (∑ j ∈ range (n + 1), (monomial j (n.choose j * (n + j).choose j)).coeff k) =
      if k ≤ n then n.choose k * (n + k).choose k else 0 := by
    simp only [coeff_monomial]
    by_cases hkn : k ≤ n
    · rw [if_pos hkn, sum_ite_eq' (range (n + 1)) k]
      simp [Nat.lt_succ_iff.mpr hkn]
    · rw [if_neg hkn, sum_eq_zero]
      intro j hj
      rw [if_neg]
      intro hjk
      exact hkn (hjk ▸ Nat.lt_succ_iff.mp (mem_range.mp hj))
  rw [hL]
  have hcoeff : ∀ j ∈ range (n + 1),
      (C ((n.choose j) ^ 2) * X ^ j * (1 + X) ^ (n - j)).coeff k =
        if j ≤ k then (n.choose j) ^ 2 * (n - j).choose (k - j) else 0 := by
    intro j _
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
    by_cases hjk : j ≤ k
    · rw [if_pos hjk, if_pos hjk]
      have h1 : (1 + X : Polynomial ℕ) ^ (n - j) = (X + 1) ^ (n - j) := by rw [add_comm]
      rw [h1, coeff_X_add_one_pow]
      simp
    · rw [if_neg hjk, if_neg hjk, mul_zero]
  rw [sum_congr rfl hcoeff]
  by_cases hkn : k ≤ n
  · rw [if_pos hkn, ← sum_filter]
    have hfilt : (range (n + 1)).filter (· ≤ k) = range (k + 1) := by
      ext j; simp only [mem_filter, mem_range]; omega
    rw [hfilt, sum_choose_sq_mul_choose n k]
  · rw [if_neg hkn]
    symm
    apply sum_eq_zero
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hjk : j ≤ k := by omega
    rw [if_pos hjk]
    have hgt : n - j < k - j := by omega
    rw [Nat.choose_eq_zero_of_lt hgt, mul_zero]

lemma a_eq_coeff_pow_mul (n : ℕ) :
    let L : Polynomial ℕ := ∑ j ∈ range (n + 1),
      monomial j (n.choose j * (n + j).choose j)
    a_def n = (L ^ 3 * (1 + X) ^ n).coeff n := by
  intro L
  dsimp only [a_def]
  rw [coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => (L ^ 3).coeff i * ((1 + X : Polynomial ℕ) ^ n).coeff j) n]
  apply sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have h1 : ((1 + X : Polynomial ℕ) ^ n).coeff (n - j) = n.choose (n - j) := by
    rw [add_comm, coeff_X_add_one_pow]; simp
  rw [h1, Nat.choose_symm hjn, mul_comm]

lemma a_eq_triple_sum (n : ℕ) :
    a_def n =
      ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i), ∑ l ∈ range (n + 1 - i - j),
        (4 * n - i - j - l).choose (3 * n) *
          (n.choose i) ^ 2 * (n.choose j) ^ 2 * (n.choose l) ^ 2 := by
  rw [a_eq_coeff_pow_mul, L_eq_sum_sq]
  set f : ℕ → Polynomial ℕ := fun i => C ((n.choose i) ^ 2) * X ^ i * (1 + X) ^ (n - i)
  have hcube : (∑ i ∈ range (n + 1), f i) ^ 3 * (1 + X) ^ n =
      ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), ∑ l ∈ range (n + 1),
        C ((n.choose i) ^ 2 * (n.choose j) ^ 2 * (n.choose l) ^ 2) *
          X ^ (i + j + l) * (1 + X) ^ (4 * n - i - j - l) := by
    rw [pow_succ', pow_two]
    simp_rw [sum_mul, mul_sum]
    apply sum_congr rfl; intro i hi
    rw [sum_mul]
    apply sum_congr rfl; intro j hj
    rw [sum_mul]
    apply sum_congr rfl; intro l hl
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hl' : l ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hl)
    have hexp : (n - i) + (n - j) + (n - l) + n = 4 * n - i - j - l := by omega
    dsimp only [f]
    rw [map_mul, map_mul, pow_add, pow_add, ← hexp, pow_add, pow_add, pow_add]
    ring
  rw [hcube]
  simp only [Polynomial.finsetSum_coeff]
  apply sum_congr rfl; intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have h1 : ∀ j ∈ range (n + 1),
      (∑ l ∈ range (n + 1),
        (C ((n.choose i) ^ 2 * (n.choose j) ^ 2 * (n.choose l) ^ 2) *
          X ^ (i + j + l) * (1 + X) ^ (4 * n - i - j - l)).coeff n) =
      if j ∈ range (n + 1 - i) then
        ∑ l ∈ range (n + 1 - i - j),
          (4 * n - i - j - l).choose (3 * n) *
            (n.choose i) ^ 2 * (n.choose j) ^ 2 * (n.choose l) ^ 2
      else 0 := by
    intro j _
    by_cases hji : j ∈ range (n + 1 - i)
    · rw [if_pos hji]
      have hji' : j < n + 1 - i := mem_range.mp hji
      rw [← sum_subset (range_mono (by omega : n + 1 - i - j ≤ n + 1))]
      · apply sum_congr rfl; intro l hl
        have hle : i + j + l ≤ n := by
          have := mem_range.mp hl; omega
        rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos hle]
        have hpow : ((1 + X : Polynomial ℕ) ^ (4 * n - i - j - l)).coeff (n - (i + j + l)) =
            (4 * n - i - j - l).choose (n - (i + j + l)) := by
          rw [add_comm, coeff_X_add_one_pow]; simp
        rw [hpow, ← Nat.choose_symm (by omega : n - (i + j + l) ≤ 4 * n - i - j - l)]
        have hsub : 4 * n - i - j - l - (n - (i + j + l)) = 3 * n := by omega
        rw [hsub]; ring
      · intro l _ hl
        have hgt : ¬ (i + j + l ≤ n) := by
          simp only [mem_range] at hl; omega
        rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_neg hgt, mul_zero]
    · rw [if_neg hji]
      apply sum_eq_zero; intro l _
      have hgt : ¬ (i + j + l ≤ n) := by
        simp only [mem_range] at hji; omega
      rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_neg hgt, mul_zero]
  rw [sum_congr rfl h1, sum_ite_mem, inter_eq_right.mpr (range_mono (by omega : n + 1 - i ≤ n + 1))]

-- Part 1B: Formula for a(N - 1) via formal power series
noncomputable def negOneAddPow (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun k => (-1 : ℤ) ^ k * ((m + k - 1).choose k : ℤ)

lemma coeff_negOneAddPow (m k : ℕ) :
    PowerSeries.coeff k (negOneAddPow m) = (-1 : ℤ) ^ k * ((m + k - 1).choose k : ℤ) := by
  simp [negOneAddPow]

lemma one_add_X_mul_negOneAddPow (m : ℕ) (hm : 0 < m) :
    (1 + PowerSeries.X : PowerSeries ℤ) * negOneAddPow (m + 1) = negOneAddPow m := by
  ext k
  rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (1 + PowerSeries.X : PowerSeries ℤ) *
          PowerSeries.coeff j (negOneAddPow (m + 1))) k]
  cases k with
  | zero =>
    simp [coeff_negOneAddPow]
  | succ k =>
    have hcoeff1 : ∀ i ∈ range (k + 2),
        PowerSeries.coeff i (1 + PowerSeries.X : PowerSeries ℤ) *
          PowerSeries.coeff (k + 1 - i) (negOneAddPow (m + 1)) =
        if i = 0 then PowerSeries.coeff (k + 1) (negOneAddPow (m + 1))
        else if i = 1 then PowerSeries.coeff k (negOneAddPow (m + 1))
        else 0 := by
      intro i _
      rcases i with _ | _ | i
      · simp
      · simp
      · simp [PowerSeries.coeff_X]
    rw [sum_congr rfl hcoeff1]
    have hsum : (∑ i ∈ range (k + 2),
        if i = 0 then PowerSeries.coeff (k + 1) (negOneAddPow (m + 1))
        else if i = 1 then PowerSeries.coeff k (negOneAddPow (m + 1))
        else 0) =
        PowerSeries.coeff (k + 1) (negOneAddPow (m + 1)) +
          PowerSeries.coeff k (negOneAddPow (m + 1)) := by
      rw [sum_range_succ', sum_range_succ']
      simp [add_comm]
    rw [hsum, coeff_negOneAddPow, coeff_negOneAddPow, coeff_negOneAddPow]
    have h1 : m + 1 + (k + 1) - 1 = (m + k) + 1 := by omega
    have h2 : m + 1 + k - 1 = m + k := by omega
    have h3 : m + (k + 1) - 1 = m + k := by omega
    rw [h1, h2, h3, Nat.choose_succ_succ (m + k) k]
    push_cast
    ring

lemma one_add_X_mul_negOneAddPow_one :
    (1 + PowerSeries.X : PowerSeries ℤ) * negOneAddPow 1 = 1 := by
  ext k
  rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (1 + PowerSeries.X : PowerSeries ℤ) *
          PowerSeries.coeff j (negOneAddPow 1)) k]
  cases k with
  | zero => simp [coeff_negOneAddPow]
  | succ k =>
    have hcoeff1 : ∀ i ∈ range (k + 2),
        PowerSeries.coeff i (1 + PowerSeries.X : PowerSeries ℤ) *
          PowerSeries.coeff (k + 1 - i) (negOneAddPow 1) =
        if i = 0 then (-1 : ℤ) ^ (k + 1)
        else if i = 1 then (-1 : ℤ) ^ k
        else 0 := by
      intro i _
      rcases i with _ | _ | i
      · simp [coeff_negOneAddPow]
      · simp [coeff_negOneAddPow]
      · simp [PowerSeries.coeff_X]
    rw [sum_congr rfl hcoeff1, sum_range_succ', sum_range_succ']
    simp [pow_succ]

lemma one_add_X_pow_mul_negOneAddPow (m : ℕ) (hm : 0 < m) :
    (1 + PowerSeries.X : PowerSeries ℤ) ^ m * negOneAddPow m = 1 := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => simpa using one_add_X_mul_negOneAddPow_one
    | succ m =>
      rw [pow_succ, mul_assoc, one_add_X_mul_negOneAddPow (m + 1) (by omega)]
      exact ih (by omega)

lemma negOneAddPow_mul (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    negOneAddPow a * negOneAddPow b = negOneAddPow (a + b) := by
  have h1 : (1 + PowerSeries.X : PowerSeries ℤ) ^ (a + b) * (negOneAddPow a * negOneAddPow b) = 1 := by
    rw [pow_add]
    calc (1 + PowerSeries.X : PowerSeries ℤ) ^ a * (1 + PowerSeries.X) ^ b *
            (negOneAddPow a * negOneAddPow b)
        = ((1 + PowerSeries.X) ^ a * negOneAddPow a) *
            ((1 + PowerSeries.X) ^ b * negOneAddPow b) := by ring
      _ = 1 * 1 := by rw [one_add_X_pow_mul_negOneAddPow a ha, one_add_X_pow_mul_negOneAddPow b hb]
      _ = 1 := one_mul 1
  calc negOneAddPow a * negOneAddPow b
      = 1 * (negOneAddPow a * negOneAddPow b) := (one_mul _).symm
    _ = (negOneAddPow (a + b) * (1 + PowerSeries.X) ^ (a + b)) *
          (negOneAddPow a * negOneAddPow b) := by
            rw [mul_comm (negOneAddPow (a + b)), one_add_X_pow_mul_negOneAddPow (a + b) (by omega)]
    _ = negOneAddPow (a + b) *
          ((1 + PowerSeries.X) ^ (a + b) * (negOneAddPow a * negOneAddPow b)) := by ring
    _ = negOneAddPow (a + b) := by rw [h1, mul_one]

lemma choose_mul_choose_pred (N k j : ℕ) (hN : 0 < N) (hjk : j ≤ k) :
    (N + j - 1).choose j * (N + k - 1).choose (k - j) =
      (N + k - 1).choose k * k.choose j := by
  have h1 : (N + k - 1).choose k * k.choose (k - j) =
      (N + k - 1).choose (k - j) * (N + k - 1 - (k - j)).choose (k - (k - j)) :=
    Nat.choose_mul (n := N + k - 1) (Nat.sub_le k j)
  have hsub1 : N + k - 1 - (k - j) = N + j - 1 := by omega
  have hsub2 : k - (k - j) = j := by omega
  rw [hsub1, hsub2, Nat.choose_symm hjk] at h1
  linarith [h1]

lemma alt_vandermonde_choose (N k : ℕ) (hN : 0 < N) :
    ∑ j ∈ range (k + 1), (-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) * ((N + j - 1).choose j : ℤ) =
      ((N - 1).choose k : ℤ) := by
  have hkey : PowerSeries.coeff k (negOneAddPow N * (1 + PowerSeries.X : PowerSeries ℤ) ^ k) =
      (-1 : ℤ) ^ k * ((N - 1).choose k : ℤ) := by
    rw [mul_comm]
    by_cases hlt : k < N
    · have hprod : (1 + PowerSeries.X : PowerSeries ℤ) ^ k * negOneAddPow N =
          negOneAddPow (N - k) := by
        have hN' : N = (N - k) + k := by omega
        have hcancel : (1 + PowerSeries.X : PowerSeries ℤ) ^ (N - k) *
            ((1 + PowerSeries.X) ^ k * negOneAddPow N) = 1 := by
          rw [← mul_assoc, ← pow_add, ← hN', one_add_X_pow_mul_negOneAddPow N hN]
        calc (1 + PowerSeries.X : PowerSeries ℤ) ^ k * negOneAddPow N
            = (negOneAddPow (N - k) * (1 + PowerSeries.X) ^ (N - k)) *
                ((1 + PowerSeries.X) ^ k * negOneAddPow N) := by
                  rw [mul_comm (negOneAddPow (N - k)),
                      one_add_X_pow_mul_negOneAddPow (N - k) (by omega), one_mul]
          _ = negOneAddPow (N - k) * ((1 + PowerSeries.X) ^ (N - k) *
                ((1 + PowerSeries.X) ^ k * negOneAddPow N)) := by ring
          _ = negOneAddPow (N - k) := by rw [hcancel, mul_one]
      rw [hprod, coeff_negOneAddPow]
      have hsub : N - k + k - 1 = N - 1 := by omega
      rw [hsub]
    · have hge : N ≤ k := by omega
      have hprod : (1 + PowerSeries.X : PowerSeries ℤ) ^ k * negOneAddPow N =
          (1 + PowerSeries.X : PowerSeries ℤ) ^ (k - N) := by
        have hk' : k = (k - N) + N := by omega
        conv_lhs => rw [hk', pow_add, mul_assoc, one_add_X_pow_mul_negOneAddPow N hN, mul_one]
      rw [hprod]
      have hzero : PowerSeries.coeff k ((1 + PowerSeries.X : PowerSeries ℤ) ^ (k - N)) = 0 := by
        have hcast : ((1 + PowerSeries.X : PowerSeries ℤ) ^ (k - N)) =
            ↑((1 + Polynomial.X : Polynomial ℤ) ^ (k - N)) := by simp
        rw [hcast, Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt]
        calc ((1 + Polynomial.X : Polynomial ℤ) ^ (k - N)).natDegree
            ≤ (k - N) * (1 + Polynomial.X : Polynomial ℤ).natDegree :=
              Polynomial.natDegree_pow_le
          _ ≤ (k - N) * 1 := by
              apply Nat.mul_le_mul_left
              have : (1 + Polynomial.X : Polynomial ℤ) = Polynomial.X + Polynomial.C 1 := by
                rw [add_comm, map_one]
              rw [this, Polynomial.natDegree_X_add_C]
          _ < k := by omega
      rw [hzero, Nat.choose_eq_zero_of_lt (by omega : N - 1 < k)]
      simp
  rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (negOneAddPow N) *
          PowerSeries.coeff j ((1 + PowerSeries.X : PowerSeries ℤ) ^ k)) k] at hkey
  have h1 : ∀ j ∈ range (k + 1),
      PowerSeries.coeff j (negOneAddPow N) *
        PowerSeries.coeff (k - j) ((1 + PowerSeries.X : PowerSeries ℤ) ^ k) =
      (-1 : ℤ) ^ k * ((-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) * ((N + j - 1).choose j : ℤ)) := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [coeff_negOneAddPow]
    have hc : PowerSeries.coeff (k - j) ((1 + PowerSeries.X : PowerSeries ℤ) ^ k) =
        (k.choose (k - j) : ℤ) := by
      have hcast : ((1 + PowerSeries.X : PowerSeries ℤ) ^ k) =
          ↑((1 + Polynomial.X : Polynomial ℤ) ^ k) := by simp
      rw [hcast, Polynomial.coeff_coe, add_comm, coeff_X_add_one_pow]
    rw [hc, Nat.choose_symm hjk]
    have hsign : (-1 : ℤ) ^ j = (-1 : ℤ) ^ k * (-1 : ℤ) ^ (k - j) := by
      rw [← pow_add]
      have hev : k + (k - j) = j + 2 * (k - j) := by omega
      rw [hev, pow_add, pow_mul]
      norm_num
    rw [hsign]
    ring
  rw [sum_congr rfl h1, ← mul_sum] at hkey
  exact mul_left_cancel₀ (pow_ne_zero k (by norm_num : (-1 : ℤ) ≠ 0)) hkey

lemma L_pred_powerSeries (N : ℕ) (hN : 0 < N) :
    let L : Polynomial ℕ := ∑ j ∈ range N,
      monomial j ((N - 1).choose j * (N - 1 + j).choose j)
    let Q : PowerSeries ℤ := ∑ j ∈ range N,
      PowerSeries.C (((N + j - 1).choose j : ℤ) ^ 2) * PowerSeries.X ^ j * negOneAddPow (N + j)
    ∀ k < N, PowerSeries.coeff k (L.map (Nat.castRingHom ℤ) : PowerSeries ℤ) =
      PowerSeries.coeff k Q := by
  intro L Q k hk
  rw [Polynomial.coeff_coe, Polynomial.coeff_map]
  have hL : L.coeff k = (N - 1).choose k * (N - 1 + k).choose k := by
    dsimp only [L]
    rw [Polynomial.finsetSum_coeff]
    simp only [coeff_monomial]
    rw [sum_ite_eq' (range N) k, if_pos (mem_range.mpr hk)]
  rw [hL]
  push_cast
  dsimp only [Q]
  rw [map_sum]
  have hterm : ∀ j ∈ range N,
      PowerSeries.coeff k
        (PowerSeries.C (((N + j - 1).choose j : ℤ) ^ 2) * PowerSeries.X ^ j *
          negOneAddPow (N + j)) =
      if j ≤ k then
        (-1 : ℤ) ^ (k - j) * ((N + j - 1).choose j : ℤ) ^ 2 *
          ((N + k - 1).choose (k - j) : ℤ)
      else 0 := by
    intro j _
    rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    by_cases hjk : j ≤ k
    · rw [if_pos hjk, if_pos hjk, coeff_negOneAddPow]
      have hsub : N + j + (k - j) - 1 = N + k - 1 := by omega
      rw [hsub]; ring
    · rw [if_neg hjk, if_neg hjk, mul_zero]
  rw [sum_congr rfl hterm, ← sum_filter]
  have hfilt : (range N).filter (· ≤ k) = range (k + 1) := by
    ext j; simp only [mem_filter, mem_range]; omega
  rw [hfilt]
  have hrew : ∀ j ∈ range (k + 1),
      (-1 : ℤ) ^ (k - j) * ((N + j - 1).choose j : ℤ) ^ 2 *
        ((N + k - 1).choose (k - j) : ℤ) =
      ((N + k - 1).choose k : ℤ) *
        ((-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) * ((N + j - 1).choose j : ℤ)) := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hcc := choose_mul_choose_pred N k j hN hjk
    have hccZ : ((N + j - 1).choose j : ℤ) * ((N + k - 1).choose (k - j) : ℤ) =
        ((N + k - 1).choose k : ℤ) * (k.choose j : ℤ) := by exact_mod_cast hcc
    calc (-1 : ℤ) ^ (k - j) * ((N + j - 1).choose j : ℤ) ^ 2 *
            ((N + k - 1).choose (k - j) : ℤ)
        = (-1 : ℤ) ^ (k - j) * ((N + j - 1).choose j : ℤ) *
            (((N + j - 1).choose j : ℤ) * ((N + k - 1).choose (k - j) : ℤ)) := by ring
      _ = (-1 : ℤ) ^ (k - j) * ((N + j - 1).choose j : ℤ) *
            (((N + k - 1).choose k : ℤ) * (k.choose j : ℤ)) := by rw [hccZ]
      _ = _ := by ring
  rw [sum_congr rfl hrew, ← mul_sum, alt_vandermonde_choose N k hN]
  have hNk : N - 1 + k = N + k - 1 := by omega
  rw [hNk, mul_comm]

lemma powerSeries_coeff_mul_eq_of_eq_lt (f₁ f₂ g₁ g₂ : PowerSeries ℤ) (N : ℕ)
    (hf : ∀ k < N, PowerSeries.coeff k f₁ = PowerSeries.coeff k f₂)
    (hg : ∀ k < N, PowerSeries.coeff k g₁ = PowerSeries.coeff k g₂) :
    ∀ k < N, PowerSeries.coeff k (f₁ * g₁) = PowerSeries.coeff k (f₂ * g₂) := by
  intro k hk
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i f₁ * PowerSeries.coeff j g₁) k,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i f₂ * PowerSeries.coeff j g₂) k]
  apply sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [hf j (by omega), hg (k - j) (by omega)]

lemma a_pred_eq_triple_sum (N : ℕ) (hN : 0 < N) :
    (a_def (N - 1) : ℤ) =
      ∑ i ∈ range N, ∑ j ∈ range (N - i), ∑ l ∈ range (N - i - j),
        (-1 : ℤ) ^ (N - 1 - i - j - l) *
          ((3 * N - 1).choose (N - 1 - i - j - l) : ℤ) *
          ((N + i - 1).choose i : ℤ) ^ 2 *
          ((N + j - 1).choose j : ℤ) ^ 2 *
          ((N + l - 1).choose l : ℤ) ^ 2 := by
  have ha := a_eq_coeff_pow_mul (N - 1)
  have hN1 : N - 1 + 1 = N := by omega
  dsimp only at ha
  rw [hN1] at ha
  set L : Polynomial ℕ := ∑ j ∈ range N,
    monomial j ((N - 1).choose j * (N - 1 + j).choose j)
  set Lp : PowerSeries ℤ := (L.map (Nat.castRingHom ℤ) : PowerSeries ℤ)
  set Q : PowerSeries ℤ := ∑ j ∈ range N,
    PowerSeries.C (((N + j - 1).choose j : ℤ) ^ 2) * PowerSeries.X ^ j * negOneAddPow (N + j)
  have hLQ : ∀ k < N, PowerSeries.coeff k Lp = PowerSeries.coeff k Q :=
    L_pred_powerSeries N hN
  have hLQ2 : ∀ k < N, PowerSeries.coeff k (Lp * Lp) = PowerSeries.coeff k (Q * Q) :=
    powerSeries_coeff_mul_eq_of_eq_lt Lp Q Lp Q N hLQ hLQ
  have hLQ3 : ∀ k < N, PowerSeries.coeff k (Lp ^ 3) = PowerSeries.coeff k (Q ^ 3) := by
    intro k hk
    rw [pow_succ, pow_two, pow_succ, pow_two]
    exact powerSeries_coeff_mul_eq_of_eq_lt _ _ _ _ N hLQ2 hLQ k hk
  have hmul : PowerSeries.coeff (N - 1) (Lp ^ 3 * (1 + PowerSeries.X : PowerSeries ℤ) ^ (N - 1)) =
      PowerSeries.coeff (N - 1) (Q ^ 3 * (1 + PowerSeries.X : PowerSeries ℤ) ^ (N - 1)) :=
    powerSeries_coeff_mul_eq_of_eq_lt _ _ _ _ N hLQ3 (fun _ _ => rfl) (N - 1) (by omega)
  have hlhs : (a_def (N - 1) : ℤ) =
      PowerSeries.coeff (N - 1) (Lp ^ 3 * (1 + PowerSeries.X : PowerSeries ℤ) ^ (N - 1)) := by
    rw [ha]
    have hcast : Lp ^ 3 * (1 + PowerSeries.X : PowerSeries ℤ) ^ (N - 1) =
        (((L ^ 3 * (1 + Polynomial.X) ^ (N - 1)).map (Nat.castRingHom ℤ) : Polynomial ℤ) :
          PowerSeries ℤ) := by
      simp [Lp, Polynomial.map_mul, Polynomial.map_pow]
    rw [hcast, Polynomial.coeff_coe, Polynomial.coeff_map]
    simp
  rw [hlhs, hmul]
  have hQ3 : Q ^ 3 * (1 + PowerSeries.X : PowerSeries ℤ) ^ (N - 1) =
      ∑ i ∈ range N, ∑ j ∈ range N, ∑ l ∈ range N,
        PowerSeries.C (((N + i - 1).choose i : ℤ) ^ 2 * ((N + j - 1).choose j : ℤ) ^ 2 *
          ((N + l - 1).choose l : ℤ) ^ 2) *
          PowerSeries.X ^ (i + j + l) * negOneAddPow (2 * N + 1 + i + j + l) := by
    dsimp only [Q]
    rw [pow_succ', pow_two]
    simp_rw [sum_mul, mul_sum]
    apply sum_congr rfl; intro i _
    rw [sum_mul]
    apply sum_congr rfl; intro j _
    rw [sum_mul]
    apply sum_congr rfl; intro l _
    have hneg : negOneAddPow (N + i) * negOneAddPow (N + j) * negOneAddPow (N + l) *
        (1 + PowerSeries.X : PowerSeries ℤ) ^ (N - 1) =
        negOneAddPow (2 * N + 1 + i + j + l) := by
      rw [negOneAddPow_mul (N + i) (N + j) (by omega) (by omega),
          negOneAddPow_mul (N + i + (N + j)) (N + l) (by omega) (by omega)]
      have hsplit : N + i + (N + j) + (N + l) = (2 * N + 1 + i + j + l) + (N - 1) := by omega
      rw [hsplit]
      cases hN_eq : N - 1 with
      | zero => simp
      | succ m =>
        rw [← negOneAddPow_mul (2 * N + 1 + i + j + l) (m + 1) (by omega) (by omega),
            mul_assoc, mul_comm (negOneAddPow (m + 1)),
            one_add_X_pow_mul_negOneAddPow (m + 1) (by omega), mul_one]
    have hC : PowerSeries.C (((N + i - 1).choose i : ℤ) ^ 2) *
        PowerSeries.C (((N + j - 1).choose j : ℤ) ^ 2) *
        PowerSeries.C (((N + l - 1).choose l : ℤ) ^ 2) =
        PowerSeries.C (((N + i - 1).choose i : ℤ) ^ 2 * ((N + j - 1).choose j : ℤ) ^ 2 *
          ((N + l - 1).choose l : ℤ) ^ 2) := by
      simp [map_mul]
    calc (PowerSeries.C (((N + i - 1).choose i : ℤ) ^ 2) * PowerSeries.X ^ i * negOneAddPow (N + i)) *
          ((PowerSeries.C (((N + j - 1).choose j : ℤ) ^ 2) * PowerSeries.X ^ j * negOneAddPow (N + j)) *
          (PowerSeries.C (((N + l - 1).choose l : ℤ) ^ 2) * PowerSeries.X ^ l * negOneAddPow (N + l))) *
          (1 + PowerSeries.X) ^ (N - 1)
        = (PowerSeries.C (((N + i - 1).choose i : ℤ) ^ 2) *
            PowerSeries.C (((N + j - 1).choose j : ℤ) ^ 2) *
            PowerSeries.C (((N + l - 1).choose l : ℤ) ^ 2)) *
          (PowerSeries.X ^ i * PowerSeries.X ^ j * PowerSeries.X ^ l) *
          (negOneAddPow (N + i) * negOneAddPow (N + j) * negOneAddPow (N + l) *
            (1 + PowerSeries.X) ^ (N - 1)) := by ring
      _ = _ := by rw [hC, ← pow_add, ← pow_add, hneg]
  rw [hQ3]
  simp only [map_sum]
  apply sum_congr rfl; intro i hi
  have hi' : i < N := mem_range.mp hi
  have h1 : ∀ j ∈ range N,
      (∑ l ∈ range N,
        PowerSeries.coeff (N - 1)
          (PowerSeries.C (((N + i - 1).choose i : ℤ) ^ 2 * ((N + j - 1).choose j : ℤ) ^ 2 *
            ((N + l - 1).choose l : ℤ) ^ 2) *
            PowerSeries.X ^ (i + j + l) * negOneAddPow (2 * N + 1 + i + j + l))) =
      if j ∈ range (N - i) then
        ∑ l ∈ range (N - i - j),
          (-1 : ℤ) ^ (N - 1 - i - j - l) *
            ((3 * N - 1).choose (N - 1 - i - j - l) : ℤ) *
            ((N + i - 1).choose i : ℤ) ^ 2 *
            ((N + j - 1).choose j : ℤ) ^ 2 *
            ((N + l - 1).choose l : ℤ) ^ 2
      else 0 := by
    intro j _
    by_cases hji : j ∈ range (N - i)
    · rw [if_pos hji]
      have hji' : j < N - i := mem_range.mp hji
      rw [← sum_subset (range_mono (by omega : N - i - j ≤ N))]
      · apply sum_congr rfl; intro l hl
        have hle : i + j + l ≤ N - 1 := by
          have := mem_range.mp hl; omega
        rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
            if_pos hle, coeff_negOneAddPow]
        have hsub1 : N - 1 - (i + j + l) = N - 1 - i - j - l := by omega
        have hsub2 : 2 * N + 1 + i + j + l + (N - 1 - (i + j + l)) - 1 = 3 * N - 1 := by omega
        rw [hsub2, hsub1]; ring
      · intro l _ hl
        have hgt : ¬ (i + j + l ≤ N - 1) := by
          simp only [mem_range] at hl; omega
        rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
            if_neg hgt, mul_zero]
    · rw [if_neg hji]
      apply sum_eq_zero; intro l _
      have hgt : ¬ (i + j + l ≤ N - 1) := by
        simp only [mem_range] at hji; omega
      rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
          if_neg hgt, mul_zero]
  rw [sum_congr rfl h1, sum_ite_mem, inter_eq_right.mpr (range_mono (by omega : N - i ≤ N))]

end OMA_A364114_Part1

namespace OMA_A364114_Part2

open Finset

-- Clean p-adic divisibility predicate on ℚ:
-- pDiv p k q means q = p^k * (a / b) with a : ℤ, b : ℕ, ¬ p ∣ b.
def pDiv (p k : ℕ) (q : ℚ) : Prop :=
  ∃ (a : ℤ) (b : ℕ), ¬ (p ∣ b) ∧ q = ((p : ℚ) ^ k * (a : ℚ)) / (b : ℚ)

lemma pDiv_zero (p k : ℕ) (hp : p.Prime) : pDiv p k 0 := by
  refine ⟨0, 1, hp.not_dvd_one, ?_⟩
  simp

lemma pDiv_mono {p k₁ k₂ : ℕ} {q : ℚ} (h : k₁ ≤ k₂) (hq : pDiv p k₂ q) : pDiv p k₁ q := by
  rcases hq with ⟨a, b, hb, rfl⟩
  refine ⟨a * (p : ℤ) ^ (k₂ - k₁), b, hb, ?_⟩
  have hadd : k₁ + (k₂ - k₁) = k₂ := Nat.add_sub_of_le h
  push_cast
  conv_lhs => rw [← hadd, pow_add]
  ring

lemma pDiv_add {p k : ℕ} {q₁ q₂ : ℚ} (hp : p.Prime) (h1 : pDiv p k q₁) (h2 : pDiv p k q₂) :
    pDiv p k (q₁ + q₂) := by
  rcases h1 with ⟨a₁, b₁, hb₁, rfl⟩
  rcases h2 with ⟨a₂, b₂, hb₂, rfl⟩
  have hb₁0 : (b₁ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h => hb₁ (h ▸ dvd_zero p))
  have hb₂0 : (b₂ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h => hb₂ (h ▸ dvd_zero p))
  refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, hp.not_dvd_mul hb₁ hb₂, ?_⟩
  push_cast
  field_simp [hb₁0, hb₂0]

lemma pDiv_neg {p k : ℕ} {q : ℚ} (h : pDiv p k q) : pDiv p k (-q) := by
  rcases h with ⟨a, b, hb, rfl⟩
  refine ⟨-a, b, hb, ?_⟩
  push_cast; ring

lemma pDiv_sub {p k : ℕ} {q₁ q₂ : ℚ} (hp : p.Prime) (h1 : pDiv p k q₁) (h2 : pDiv p k q₂) :
    pDiv p k (q₁ - q₂) := by
  rw [sub_eq_add_neg]
  exact pDiv_add hp h1 (pDiv_neg h2)

lemma pDiv_mul {p k₁ k₂ : ℕ} {q₁ q₂ : ℚ} (hp : p.Prime)
    (h1 : pDiv p k₁ q₁) (h2 : pDiv p k₂ q₂) : pDiv p (k₁ + k₂) (q₁ * q₂) := by
  rcases h1 with ⟨a₁, b₁, hb₁, rfl⟩
  rcases h2 with ⟨a₂, b₂, hb₂, rfl⟩
  refine ⟨a₁ * a₂, b₁ * b₂, hp.not_dvd_mul hb₁ hb₂, ?_⟩
  push_cast
  rw [pow_add]
  ring

lemma pDiv_sum {ι : Type*} {p k : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, pDiv p k (f i)) : pDiv p k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [pDiv_zero p k hp]
  | @insert x s hx ih =>
    rw [sum_insert hx]
    exact pDiv_add hp (hf x (mem_insert_self x s))
      (ih (fun y hy => hf y (mem_insert_of_mem hy)))

lemma pDiv_int {p k : ℕ} {z : ℤ} (hp : p.Prime) (h : (p : ℤ) ^ k ∣ z) : pDiv p k (z : ℚ) := by
  rcases h with ⟨c, rfl⟩
  refine ⟨c, 1, hp.not_dvd_one, ?_⟩
  push_cast; ring

lemma pDiv_int_zero {p : ℕ} (hp : p.Prime) (z : ℤ) : pDiv p 0 (z : ℚ) := by
  refine ⟨z, 1, hp.not_dvd_one, ?_⟩
  simp

lemma pDiv_nat_zero {p : ℕ} (hp : p.Prime) (n : ℕ) : pDiv p 0 (n : ℚ) := by
  refine ⟨n, 1, hp.not_dvd_one, ?_⟩
  simp

lemma pDiv_of_dvd_nat {p k n : ℕ} (hp : p.Prime) (h : p ^ k ∣ n) : pDiv p k (n : ℚ) := by
  rcases h with ⟨c, rfl⟩
  refine ⟨c, 1, hp.not_dvd_one, ?_⟩
  push_cast; ring

lemma pDiv_div_nat_unit {p k m : ℕ} {q : ℚ} (hp : p.Prime) (hm : ¬ p ∣ m)
    (hq : pDiv p k q) : pDiv p k (q / (m : ℚ)) := by
  rcases hq with ⟨a, b, hb, rfl⟩
  refine ⟨a, b * m, hp.not_dvd_mul hb hm, ?_⟩
  push_cast; ring

lemma pDiv_div_nat {p k m : ℕ} {q : ℚ} (hp : p.Prime) (hm0 : m ≠ 0)
    (hq : pDiv p (k + padicValNat p m) q) : pDiv p k (q / (m : ℚ)) := by
  have : Fact p.Prime := ⟨hp⟩
  set v := padicValNat p m
  have hdvd : p ^ v ∣ m := pow_padicValNat_dvd
  rcases hdvd with ⟨u, hu⟩
  have hu_ndvd : ¬ p ∣ u := by
    intro hpu
    have h1 : p ^ (v + 1) ∣ m := by
      rw [hu, pow_succ]
      exact mul_dvd_mul_left (p ^ v) hpu
    have h2 := padicValNat_dvd_iff_le hm0 |>.mp h1
    omega
  rcases hq with ⟨a, b, hb, rfl⟩
  refine ⟨a, b * u, hp.not_dvd_mul hb hu_ndvd, ?_⟩
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hu0 : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h => hu_ndvd (h ▸ dvd_zero p))
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h => hb (h ▸ dvd_zero p))
  have hm_cast : (m : ℚ) = (p : ℚ) ^ v * (u : ℚ) := by rw [hu]; push_cast; rfl
  rw [hm_cast]
  push_cast
  rw [pow_add]
  field_simp [hp0, hu0, hb0]

lemma int_dvd_of_pDiv {p k : ℕ} {z : ℤ} (hp : p.Prime) (h : pDiv p k (z : ℚ)) :
    (p : ℤ) ^ k ∣ z := by
  rcases h with ⟨a, b, hb, heq⟩
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h0 => hb (h0 ▸ dvd_zero p))
  have h1 : (z : ℚ) * (b : ℚ) = (p : ℚ) ^ k * (a : ℚ) := by
    rw [heq]; field_simp [hb0]
  have h2 : z * (b : ℤ) = (p : ℤ) ^ k * a := by exact_mod_cast h1
  have hdvd : (p : ℤ) ^ k ∣ z * (b : ℤ) := ⟨a, h2⟩
  have hcop : IsCoprime ((p : ℤ) ^ k) (b : ℤ) := by
    apply IsCoprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hb |>.isCoprime
  exact hcop.dvd_of_dvd_mul_right hdvd

lemma pDiv_prod {ι : Type*} {p : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, pDiv p 0 (f i)) : pDiv p 0 (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using pDiv_nat_zero hp 1
  | @insert x s hx ih =>
    rw [prod_insert hx]
    simpa using pDiv_mul hp (hf x (mem_insert_self x s))
      (ih (fun y hy => hf y (mem_insert_of_mem hy)))

lemma pDiv_pow {p k n : ℕ} {q : ℚ} (hp : p.Prime) (hq : pDiv p k q) :
    pDiv p (k * n) (q ^ n) := by
  induction n with
  | zero => simpa using pDiv_nat_zero hp 1
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact pDiv_mul hp ih hq

lemma pDiv_cancel_unit {p k : ℕ} {u q : ℚ} (hp : p.Prime)
    (hu : pDiv p 1 (u - 1)) (_hq : pDiv p 0 q) (hprod : pDiv p k (u * q)) :
    pDiv p k q := by
  rcases hu with ⟨c, d, hd, huc⟩
  have hu_eq : u = ((d : ℤ) + (p : ℤ) * c : ℤ) / (d : ℚ) := by
    have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h0 => hd (h0 ▸ dvd_zero p))
    have : u = 1 + ((p : ℚ) ^ 1 * (c : ℚ)) / (d : ℚ) := by linarith
    rw [this]; push_cast; field_simp [hd0]
  set num : ℤ := (d : ℤ) + (p : ℤ) * c
  have hnum_ndvd : ¬ ((p : ℤ) ∣ num) := by
    intro hdiv
    have hd_dvd : (p : ℤ) ∣ (d : ℤ) := by
      have : (d : ℤ) = num - (p : ℤ) * c := by omega
      rw [this]
      exact dvd_sub hdiv (dvd_mul_right _ _)
    exact hd (Int.ofNat_dvd.mp hd_dvd)
  have hnum_ne : num ≠ 0 := fun h0 => hnum_ndvd (h0 ▸ dvd_zero _)
  rcases hprod with ⟨ap, bp, hbp, hprod_eq⟩
  have hbp0 : (bp : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h0 => hbp (h0 ▸ dvd_zero p))
  have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h0 => hd (h0 ▸ dvd_zero p))
  have hnum0 : (num : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hnum_ne
  have hq_eq : q = ((p : ℚ) ^ k * ((ap * (d : ℤ) : ℤ) : ℚ)) / ((bp : ℚ) * (num : ℚ)) := by
    have : u * q = ((p : ℚ) ^ k * (ap : ℚ)) / (bp : ℚ) := hprod_eq
    rw [hu_eq] at this
    push_cast
    field_simp [hbp0, hd0, hnum0] at this ⊢
    linarith
  have hnat_ndvd : ¬ (p ∣ num.natAbs) := by
    intro hdiv
    exact hnum_ndvd (Int.ofNat_dvd_left.mpr hdiv)
  rcases Int.natAbs_eq num with hpos | hneg
  · refine ⟨ap * (d : ℤ), bp * num.natAbs, hp.not_dvd_mul hbp hnat_ndvd, ?_⟩
    rw [hq_eq]
    have hnum_cast : (num : ℚ) = (num.natAbs : ℚ) := by
      simpa using congrArg (Int.cast (R := ℚ)) hpos
    rw [hnum_cast]; push_cast; ring
  · refine ⟨-(ap * (d : ℤ)), bp * num.natAbs, hp.not_dvd_mul hbp hnat_ndvd, ?_⟩
    rw [hq_eq]
    have hnum_cast : (num : ℚ) = -(num.natAbs : ℚ) := by
      simpa using congrArg (Int.cast (R := ℚ)) hneg
    rw [hnum_cast]; push_cast; ring

-- ============================================================================
-- Section 1: Wolstenholme's theorem (p ≥ 5): pDiv p 1 (∑_{u=1}^{p-1} 1/(u*(p-u)))
-- ============================================================================

-- First: ∑_{u=1}^{p-1} 1/u^2 ≡ 0 (mod p) for p ≥ 5!
lemma zmod_inv_sq_sum_zero (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∑ u ∈ Ico 1 p, ((u : ZMod p)⁻¹) ^ 2 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h3ne : (3 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp (by simpa using h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hfull : ∑ u ∈ Ico 1 p, ((u : ZMod p)⁻¹) ^ 2 = ∑ x : ZMod p, (x⁻¹) ^ 2 := by
    have hrange : ∑ u ∈ range p, ((u : ZMod p)⁻¹) ^ 2 = ∑ x : ZMod p, (x⁻¹) ^ 2 := by
      refine Finset.sum_bij (fun u _ => (u : ZMod p)) ?_ ?_ ?_ ?_
      · intro _ _; exact mem_univ _
      · intro u₁ hu₁ u₂ hu₂ heq
        have hv := congrArg ZMod.val heq
        rw [ZMod.val_natCast_of_lt (mem_range.mp hu₁),
            ZMod.val_natCast_of_lt (mem_range.mp hu₂)] at hv
        exact hv
      · intro x _
        exact ⟨x.val, mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
      · intro _ _; rfl
    rw [← hrange, show range p = insert 0 (Ico 1 p) by ext x; simp; omega, sum_insert (by simp)]
    simp
  rw [hfull]
  have hbij : ∑ x : ZMod p, (((2 : ZMod p) * x)⁻¹) ^ 2 = ∑ x : ZMod p, (x⁻¹) ^ 2 := by
    refine Fintype.sum_equiv (Equiv.mulLeft₀ (2 : ZMod p) h2ne) _ _ (fun x => rfl)
  have h4 : ((2 : ZMod p)⁻¹) ^ 2 * ∑ x : ZMod p, (x⁻¹) ^ 2 = ∑ x : ZMod p, (x⁻¹) ^ 2 := by
    rw [mul_sum]
    convert hbij using 2 with x
    rw [mul_inv, mul_pow]
  have hmul4 : (4 : ZMod p) * (((2 : ZMod p)⁻¹) ^ 2 * ∑ x : ZMod p, (x⁻¹) ^ 2) =
      (4 : ZMod p) * ∑ x : ZMod p, (x⁻¹) ^ 2 := congrArg ((4 : ZMod p) * ·) h4
  have h4inv : (4 : ZMod p) * ((2 : ZMod p)⁻¹) ^ 2 = 1 := by
    have : (4 : ZMod p) = (2 : ZMod p) ^ 2 := by norm_num
    rw [this, ← mul_pow, mul_inv_cancel₀ h2ne, one_pow]
  rw [← mul_assoc, h4inv, one_mul] at hmul4
  have h3 : (3 : ZMod p) * ∑ x : ZMod p, (x⁻¹) ^ 2 = 0 := by
    have : (3 : ZMod p) = 4 - 1 := by norm_num
    rw [this, sub_mul, one_mul, ← hmul4, sub_self]
  exact (mul_eq_zero.mp h3).resolve_left h3ne

lemma sum_inv_mul_sub_pDiv_one (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    pDiv p 1 (∑ u ∈ Ico 1 p, (1 : ℚ) / ((u : ℚ) * ((p - u : ℕ) : ℚ))) := by
  have hfac_ndvd : ¬ p ∣ (p - 1).factorial := by
    have haux : ∀ k, k < p → ¬ p ∣ k.factorial := by
      intro k
      induction k with
      | zero => intro _; exact hp.not_dvd_one
      | succ k ih =>
        intro hk hdiv
        rw [Nat.factorial_succ] at hdiv
        rcases hp.dvd_mul.mp hdiv with h1 | h2
        · have := Nat.le_of_dvd (by omega) h1; omega
        · exact ih (by omega) h2
    exact haux (p - 1) (by omega)
  set F : ℕ := (p - 1).factorial
  have hF0 : (F : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hu_dvd : ∀ u ∈ Ico 1 p, u ∣ F := fun u hu =>
    Nat.dvd_factorial (mem_Ico.mp hu).1 (by have := (mem_Ico.mp hu).2; omega)
  have hpu_dvd : ∀ u ∈ Ico 1 p, (p - u) ∣ F := fun u hu =>
    Nat.dvd_factorial (by have := (mem_Ico.mp hu).2; omega)
      (by have := (mem_Ico.mp hu).1; omega)
  set A : ℕ := ∑ u ∈ Ico 1 p, (F / u) * (F / (p - u))
  have hsum_eq : (∑ u ∈ Ico 1 p, (1 : ℚ) / ((u : ℚ) * ((p - u : ℕ) : ℚ))) =
      (A : ℚ) / ((F * F : ℕ) : ℚ) := by
    rw [Nat.cast_sum, sum_div]
    apply sum_congr rfl
    intro u hu
    have hu0 : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (mem_Ico.mp hu).1; omega)
    have hpu0 : ((p - u : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (mem_Ico.mp hu).2; omega)
    have hq1 : ((F / u : ℕ) : ℚ) = (F : ℚ) / (u : ℚ) := by
      have hm : ((F / u : ℕ) : ℚ) * (u : ℚ) = (F : ℚ) := by
        have := congrArg (Nat.cast (R := ℚ)) (Nat.div_mul_cancel (hu_dvd u hu))
        simpa using this
      field_simp [hu0]; linarith
    have hq2 : ((F / (p - u) : ℕ) : ℚ) = (F : ℚ) / ((p - u : ℕ) : ℚ) := by
      have hm : ((F / (p - u) : ℕ) : ℚ) * ((p - u : ℕ) : ℚ) = (F : ℚ) := by
        have := congrArg (Nat.cast (R := ℚ)) (Nat.div_mul_cancel (hpu_dvd u hu))
        simpa using this
      field_simp [hpu0]; linarith
    push_cast
    rw [hq1, hq2]
    field_simp [hF0, hu0, hpu0]
  have hA_dvd : p ∣ A := by
    rw [← ZMod.natCast_eq_zero_iff]
    have : Fact p.Prime := ⟨hp⟩
    have hA_cast : (A : ZMod p) =
        -((F : ZMod p) ^ 2 * ∑ u ∈ Ico 1 p, ((u : ZMod p)⁻¹) ^ 2) := by
      rw [mul_sum, ← sum_neg_distrib]
      dsimp only [A]
      push_cast
      apply sum_congr rfl
      intro u hu
      have hu1 := (mem_Ico.mp hu).1
      have hu2 := (mem_Ico.mp hu).2
      have hu_ne : (u : ZMod p) ≠ 0 := by
        intro h
        have : p ∣ u := (ZMod.natCast_eq_zero_iff u p).mp h
        have := Nat.le_of_dvd (by omega) this
        omega
      have hpu_cast : ((p - u : ℕ) : ZMod p) = -(u : ZMod p) := by
        rw [Nat.cast_sub (by omega : u ≤ p), ZMod.natCast_self, zero_sub]
      have hq1 : ((F / u : ℕ) : ZMod p) = (F : ZMod p) * (u : ZMod p)⁻¹ := by
        have hmulZ : ((F / u : ℕ) : ZMod p) * (u : ZMod p) = (F : ZMod p) := by
          have := congrArg (Nat.cast (R := ZMod p)) (Nat.div_mul_cancel (hu_dvd u hu))
          simpa using this
        calc ((F / u : ℕ) : ZMod p) = ((F / u : ℕ) : ZMod p) * (u : ZMod p) * (u : ZMod p)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ hu_ne, mul_one]
          _ = (F : ZMod p) * (u : ZMod p)⁻¹ := by rw [hmulZ]
      have hq2 : ((F / (p - u) : ℕ) : ZMod p) = -(F : ZMod p) * (u : ZMod p)⁻¹ := by
        have hmulZ : ((F / (p - u) : ℕ) : ZMod p) * ((p - u : ℕ) : ZMod p) = (F : ZMod p) := by
          have := congrArg (Nat.cast (R := ZMod p)) (Nat.div_mul_cancel (hpu_dvd u hu))
          simpa using this
        rw [hpu_cast] at hmulZ
        have hmulZ' : ((F / (p - u) : ℕ) : ZMod p) * (u : ZMod p) = -(F : ZMod p) := by
          linear_combination -hmulZ
        calc ((F / (p - u) : ℕ) : ZMod p) =
              ((F / (p - u) : ℕ) : ZMod p) * (u : ZMod p) * (u : ZMod p)⁻¹ := by
                rw [mul_assoc, mul_inv_cancel₀ hu_ne, mul_one]
          _ = -(F : ZMod p) * (u : ZMod p)⁻¹ := by rw [hmulZ']
      rw [hq1, hq2]
      ring
    rw [hA_cast, zmod_inv_sq_sum_zero p hp hp5, mul_zero, neg_zero]
  rw [hsum_eq]
  rcases hA_dvd with ⟨c, hc⟩
  refine ⟨c, F * F, hp.not_dvd_mul hfac_ndvd hfac_ndvd, ?_⟩
  rw [hc]; push_cast; ring

-- ============================================================================
-- Section 2: Central falling factorials & S_d(b + c) - S_d(b) - S_d(c)
-- ============================================================================

def centralP (k : ℕ) (m : ℤ) : ℤ :=
  ∏ j ∈ range k, (m * (m + 1) - (j : ℤ) * ((j : ℤ) + 1))

def centralQ (k : ℕ) (n : ℤ) : ℤ :=
  n * ∏ j ∈ Icc 1 k, (n ^ 2 - (j : ℤ) ^ 2)

lemma centralQ_eq_mul_P (k : ℕ) (m : ℤ) :
    centralQ k m = (m - (k : ℤ)) * centralP k m ∧
    centralQ k (m + 1) = (m + (k : ℤ) + 1) * centralP k m := by
  induction k with
  | zero =>
    simp [centralQ, centralP]
  | succ k ih =>
    have hP : centralP (k + 1) m = centralP k m * (m * (m + 1) - (k : ℤ) * ((k : ℤ) + 1)) := by
      simp [centralP, prod_range_succ]
    have hQ : ∀ n : ℤ, centralQ (k + 1) n = centralQ k n * (n ^ 2 - ((k + 1 : ℕ) : ℤ) ^ 2) := by
      intro n
      simp only [centralQ]
      have hIcc : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
        ext x; simp only [mem_Icc, mem_insert]; omega
      rw [hIcc, prod_insert (by simp)]
      ring
    constructor
    · rw [hQ m, ih.1, hP]
      push_cast; ring
    · rw [hQ (m + 1), ih.2, hP]
      push_cast; ring

lemma centralQ_sub' (k : ℕ) (m : ℤ) :
    centralQ k (m + 1) - centralQ k m = (2 * (k : ℤ) + 1) * centralP k m := by
  rw [(centralQ_eq_mul_P k m).2, (centralQ_eq_mul_P k m).1]
  ring

lemma sum_centralP (k n : ℕ) :
    (2 * (k : ℤ) + 1) * ∑ m ∈ range n, centralP k (m : ℤ) = centralQ k (n : ℤ) := by
  induction n with
  | zero => simp [centralQ]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, ← centralQ_sub' k (n : ℤ)]
    push_cast; ring

lemma dvd_odd_pow_sub (j : ℕ) (b c : ℤ) :
    (b + c) * b * c ∣ ((b + c) ^ (2 * j + 3) - b ^ (2 * j + 3) - c ^ (2 * j + 3)) := by
  -- Prove by induction on j!
  -- Wait: for j = 0: (b+c)^3 - b^3 - c^3 = 3*(b+c)*b*c!
  -- Step j -> j+1:
  --   (b+c)^(2j+5) - b^(2j+5) - c^(2j+5)
  --   = (b^2 + c^2) * ((b+c)^(2j+3) - b^(2j+3) - c^(2j+3))
  --     + 2*b*c * (b+c)^(2j+3) + b^2 * c^(2j+3) + c^2 * b^(2j+3)
  --   Wait: b^2 c^(2j+3) + c^2 b^(2j+3) = b^2 c^2 (c^(2j+1) + b^(2j+1)), and (b+c) ∣ (b^(2j+1) + c^(2j+1))!
  induction j with
  | zero =>
    refine ⟨3, ?_⟩
    ring
  | succ j ih =>
    have hodd : (b + c) ∣ (b ^ (2 * j + 1) + c ^ (2 * j + 1)) := by
      have h1 := sub_dvd_pow_sub_pow b (-c) (2 * j + 1)
      rw [sub_neg_eq_add] at h1
      have hneg : (-c) ^ (2 * j + 1) = -(c ^ (2 * j + 1)) := by
        rw [neg_pow, pow_add, pow_mul]; norm_num
      rw [hneg, sub_neg_eq_add] at h1
      exact h1
    rcases ih with ⟨q₁, hq₁⟩
    rcases hodd with ⟨q₂, hq₂⟩
    refine ⟨(b ^ 2 + c ^ 2) * q₁ + 2 * (b + c) ^ (2 * j + 2) + b * c * q₂, ?_⟩
    have hpow1 : (b + c) ^ (2 * (j + 1) + 3) = (b + c) ^ 2 * (b + c) ^ (2 * j + 3) := by
      rw [← pow_add]; congr 1; omega
    have hpow2 : b ^ (2 * (j + 1) + 3) = b ^ 2 * b ^ (2 * j + 3) := by
      rw [← pow_add]; congr 1; omega
    have hpow3 : c ^ (2 * (j + 1) + 3) = c ^ 2 * c ^ (2 * j + 3) := by
      rw [← pow_add]; congr 1; omega
    have hpow4 : (b + c) ^ (2 * j + 3) = (b + c) * (b + c) ^ (2 * j + 2) := by
      rw [pow_succ']
    have hpow5 : b ^ (2 * j + 3) = b ^ 2 * b ^ (2 * j + 1) := by
      rw [← pow_add]; congr 1; omega
    have hpow6 : c ^ (2 * j + 3) = c ^ 2 * c ^ (2 * j + 1) := by
      rw [← pow_add]; congr 1; omega
    calc (b + c) ^ (2 * (j + 1) + 3) - b ^ (2 * (j + 1) + 3) - c ^ (2 * (j + 1) + 3)
        = (b ^ 2 + c ^ 2) * ((b + c) ^ (2 * j + 3) - b ^ (2 * j + 3) - c ^ (2 * j + 3)) +
            2 * b * c * (b + c) ^ (2 * j + 3) +
            b ^ 2 * c ^ 2 * (b ^ (2 * j + 1) + c ^ (2 * j + 1)) := by
              rw [hpow1, hpow2, hpow3, hpow5, hpow6]; ring
      _ = (b ^ 2 + c ^ 2) * ((b + c) * b * c * q₁) +
            2 * b * c * ((b + c) * (b + c) ^ (2 * j + 2)) +
            b ^ 2 * c ^ 2 * ((b + c) * q₂) := by rw [hq₁, hpow4, hq₂]
      _ = (b + c) * b * c * ((b ^ 2 + c ^ 2) * q₁ + 2 * (b + c) ^ (2 * j + 2) + b * c * q₂) := by
            ring

lemma centralQ_sub_dvd (k : ℕ) (b c : ℤ) :
    (b + c) * b * c ∣ (centralQ k (b + c) - centralQ k b - centralQ k c) := by
  -- Expand ∏_{j=1}^k (X^2 - j^2) as ∑_{i=0}^k coeff_i * X^(2*i), so centralQ k n = ∑ coeff_i * n^(2i+1)!
  -- Prove by induction on k that ∃ P : Polynomial ℤ, ∀ n : ℤ, centralQ k n = n * P.eval (n^2)
  have hex : ∃ P : Polynomial ℤ, ∀ n : ℤ, centralQ k n = n * P.eval (n ^ 2) := by
    refine ⟨∏ j ∈ Icc 1 k, (Polynomial.X - Polynomial.C ((j : ℤ) ^ 2)), ?_⟩
    intro n
    simp [centralQ, Polynomial.eval_prod]
  rcases hex with ⟨P, hP⟩
  rw [hP (b + c), hP b, hP c]
  clear hP
  induction P using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp only [Polynomial.eval_add]
    have hrew : (b + c) * (p.eval ((b + c) ^ 2) + q.eval ((b + c) ^ 2)) -
        b * (p.eval (b ^ 2) + q.eval (b ^ 2)) - c * (p.eval (c ^ 2) + q.eval (c ^ 2)) =
        ((b + c) * p.eval ((b + c) ^ 2) - b * p.eval (b ^ 2) - c * p.eval (c ^ 2)) +
        ((b + c) * q.eval ((b + c) ^ 2) - b * q.eval (b ^ 2) - c * q.eval (c ^ 2)) := by ring
    rw [hrew]
    exact dvd_add ihp ihq
  | monomial i a =>
    simp only [Polynomial.eval_monomial]
    cases i with
    | zero =>
      simp only [pow_zero, mul_one]
      have : (b + c) * a - b * a - c * a = 0 := by ring
      rw [this]
      exact dvd_zero _
    | succ j =>
      have hrew : (b + c) * (a * ((b + c) ^ 2) ^ (j + 1)) -
          b * (a * (b ^ 2) ^ (j + 1)) - c * (a * (c ^ 2) ^ (j + 1)) =
          a * ((b + c) ^ (2 * j + 3) - b ^ (2 * j + 3) - c ^ (2 * j + 3)) := by
        simp only [← pow_mul]
        have he : 2 * (j + 1) + 1 = 2 * j + 3 := by omega
        calc (b + c) * (a * (b + c) ^ (2 * (j + 1))) - b * (a * b ^ (2 * (j + 1))) -
              c * (a * c ^ (2 * (j + 1)))
            = a * ((b + c) ^ (2 * (j + 1) + 1) - b ^ (2 * (j + 1) + 1) - c ^ (2 * (j + 1) + 1)) := by
                simp only [pow_succ]; ring
          _ = _ := by rw [he]
      rw [hrew]
      exact dvd_mul_of_dvd_right (dvd_odd_pow_sub j b c) a

noncomputable def centralPoly (k : ℕ) : Polynomial ℤ :=
  ∏ j ∈ range k, (Polynomial.X - Polynomial.C ((j : ℤ) * ((j : ℤ) + 1)))

lemma centralPoly_monic (k : ℕ) : (centralPoly k).Monic := by
  unfold centralPoly
  apply Polynomial.monic_prod_of_monic
  intro j _
  exact Polynomial.monic_X_sub_C _

lemma centralPoly_natDegree (k : ℕ) : (centralPoly k).natDegree = k := by
  unfold centralPoly
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)]
  simp only [Polynomial.natDegree_X_sub_C, sum_const, card_range, smul_eq_mul, mul_one]

lemma centralPoly_coeff_zero (k : ℕ) (hk : 1 ≤ k) : (centralPoly k).coeff 0 = 0 := by
  have h0 : Polynomial.eval 0 (centralPoly k) = (centralPoly k).coeff 0 := by
    rw [Polynomial.eval_eq_sum_range]
    rcases h : (centralPoly k).natDegree with _ | d
    · simp
    · rw [Finset.sum_range_succ']
      simp [zero_pow (Nat.succ_ne_zero _)]
  rw [← h0]
  unfold centralPoly
  rw [Polynomial.eval_prod]
  apply prod_eq_zero (i := 0) (mem_range.mpr hk)
  simp

lemma poly_zero_const_eq_sum_centralPoly (n : ℕ) :
    ∀ R : Polynomial ℤ, R.coeff 0 = 0 → R.natDegree ≤ n →
      ∃ coeff : ℕ → ℤ, R = ∑ k ∈ Icc 1 n, Polynomial.C (coeff k) * centralPoly k := by
  induction n with
  | zero =>
    intro R h0 hdeg
    refine ⟨fun _ => 0, ?_⟩
    ext m
    cases m with
    | zero => simpa using h0
    | succ m =>
      simp only [show Icc 1 0 = ∅ by decide, sum_empty, Polynomial.coeff_zero]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  | succ n ih =>
    intro R h0 hdeg
    set a : ℤ := R.coeff (n + 1)
    set R' : Polynomial ℤ := R - Polynomial.C a * centralPoly (n + 1)
    have hR'0 : R'.coeff 0 = 0 := by
      simp [R', h0, centralPoly_coeff_zero (n + 1) (by omega)]
    have hR'deg : R'.natDegree ≤ n := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      simp only [R', Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      by_cases hmeq : m = n + 1
      · subst hmeq
        have hlc : (centralPoly (n + 1)).coeff (n + 1) = 1 := by
          have := (centralPoly_monic (n + 1)).leadingCoeff
          rw [Polynomial.leadingCoeff, centralPoly_natDegree] at this
          exact this
        rw [hlc, mul_one, sub_self]
      · have hgt : n + 1 < m := by omega
        have hR0 : R.coeff m = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        have hP0 : (centralPoly (n + 1)).coeff m = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [centralPoly_natDegree]; omega)
        rw [hR0, hP0, mul_zero, sub_zero]
    rcases ih R' hR'0 hR'deg with ⟨c', hc'⟩
    refine ⟨fun k => if k = n + 1 then a else c' k, ?_⟩
    have hIcc : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    rw [hIcc, sum_insert (by simp)]
    dsimp only
    rw [if_pos rfl]
    have hcongr : ∑ k ∈ Icc 1 n, Polynomial.C (if k = n + 1 then a else c' k) * centralPoly k =
        ∑ k ∈ Icc 1 n, Polynomial.C (c' k) * centralPoly k := by
      apply sum_congr rfl
      intro k hk
      rw [if_neg (by have := (mem_Icc.mp hk).2; omega)]
    rw [hcongr, ← hc']
    simp [R']

lemma pow_eq_sum_centralP (d : ℕ) (hd : 1 ≤ d) :
    ∃ coeff : ℕ → ℤ, ∀ m : ℤ,
      (m * (m + 1)) ^ d = ∑ k ∈ Icc 1 d, coeff k * centralP k m := by
  have hX0 : ((Polynomial.X : Polynomial ℤ) ^ d).coeff 0 = 0 := by
    rw [Polynomial.coeff_X_pow, if_neg (by omega)]
  have hXdeg : ((Polynomial.X : Polynomial ℤ) ^ d).natDegree ≤ d := by
    simp
  rcases poly_zero_const_eq_sum_centralPoly d (Polynomial.X ^ d) hX0 hXdeg with ⟨c, hc⟩
  refine ⟨c, fun m => ?_⟩
  have hev := congrArg (Polynomial.eval (m * (m + 1))) hc
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C] at hev
  rw [hev]
  apply sum_congr rfl
  intro k _
  congr 1
  simp [centralPoly, centralP, Polynomial.eval_prod]

-- Valuation inequality for d ≥ 2: 2 * d ≥ 3 + v_p(d) + v_p(2 * k + 1)
lemma mul_lt_five_pow (d : ℕ) (hd : 4 ≤ d) : d * (2 * d + 1) < 5 ^ (2 * d - 3) := by
  induction d with
  | zero => omega
  | succ d ih =>
    by_cases h4 : d < 4
    · have : d = 3 := by omega
      subst this; norm_num
    · have hih := ih (by omega)
      have hexp : 2 * (d + 1) - 3 = (2 * d - 3) + 2 := by omega
      rw [hexp, pow_add]
      have h5 : (5 : ℕ) ^ 2 = 25 := by norm_num
      rw [h5]
      nlinarith

lemma kazandzidis_exp_bound (p d k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hd : 2 ≤ d) (hk : k ≤ d) :
    3 + padicValNat p d + padicValNat p (2 * k + 1) ≤ 2 * d := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpow_d : p ^ padicValNat p d ≤ d :=
    Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  have hpow_k : p ^ padicValNat p (2 * k + 1) ≤ 2 * k + 1 :=
    Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  by_cases hd2 : d = 2
  · subst hd2
    have hvd : padicValNat p 2 = 0 := padicValNat.eq_zero_of_not_dvd (by
      intro h; have := Nat.le_of_dvd (by norm_num) h; omega)
    have hvk : padicValNat p (2 * k + 1) ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ padicValNat p (2 * k + 1) := by omega
      have hle : p ^ 2 ≤ 2 * k + 1 := le_trans (Nat.pow_le_pow_right hp.pos h2) hpow_k
      nlinarith
    omega
  · by_cases hd3 : d = 3
    · subst hd3
      have hvd : padicValNat p 3 = 0 := padicValNat.eq_zero_of_not_dvd (by
        intro h; have := Nat.le_of_dvd (by norm_num) h; omega)
      have hvk : padicValNat p (2 * k + 1) ≤ 1 := by
        by_contra h
        have h2 : 2 ≤ padicValNat p (2 * k + 1) := by omega
        have hle : p ^ 2 ≤ 2 * k + 1 := le_trans (Nat.pow_le_pow_right hp.pos h2) hpow_k
        nlinarith
      omega
    · have hd4 : 4 ≤ d := by omega
      have hprod : p ^ (padicValNat p d + padicValNat p (2 * k + 1)) < p ^ (2 * d - 3) := by
        calc p ^ (padicValNat p d + padicValNat p (2 * k + 1))
            = p ^ padicValNat p d * p ^ padicValNat p (2 * k + 1) := pow_add _ _ _
          _ ≤ d * (2 * k + 1) := Nat.mul_le_mul hpow_d hpow_k
          _ ≤ d * (2 * d + 1) := Nat.mul_le_mul_left d (by omega)
          _ < 5 ^ (2 * d - 3) := mul_lt_five_pow d hd4
          _ ≤ p ^ (2 * d - 3) := Nat.pow_le_pow_left hp5 _
      have hlt : padicValNat p d + padicValNat p (2 * k + 1) < 2 * d - 3 :=
        (Nat.pow_lt_pow_iff_right hp.one_lt).mp hprod
      omega

-- ============================================================================
-- Section 3: Δ_d valuation bound and Newton's identity in PowerSeries ℚ
-- ============================================================================

def sumS (n d : ℕ) : ℚ :=
  ∑ m ∈ range n, ((m : ℚ) * ((m : ℚ) + 1)) ^ d

def sumU (p d : ℕ) : ℚ :=
  ∑ u ∈ Ico 1 p, ((1 : ℚ) / ((u : ℚ) * ((p - u : ℕ) : ℚ))) ^ d

def deltaD (p b c d : ℕ) : ℚ :=
  (p : ℚ) ^ (2 * d) * sumU p d * (sumS (b + c) d - sumS b d - sumS c d)

lemma sumU_pDiv_zero (p d : ℕ) (hp : p.Prime) : pDiv p 0 (sumU p d) := by
  unfold sumU
  apply pDiv_sum hp
  intro u hu
  have hu1 := (mem_Ico.mp hu).1
  have hu2 := (mem_Ico.mp hu).2
  have hndvd_u : ¬ p ∣ u := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hndvd_pu : ¬ p ∣ (p - u) := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have h1 : pDiv p 0 ((1 : ℚ) / ((u : ℚ) * ((p - u : ℕ) : ℚ))) := by
    refine ⟨1, u * (p - u), hp.not_dvd_mul hndvd_u hndvd_pu, ?_⟩
    push_cast; ring
  simpa using pDiv_pow hp h1

lemma deltaD_div_pDiv (p b c d : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hb : 0 < b) (hc : 0 < c) (hd : 1 ≤ d) :
    pDiv p (3 + padicValNat p (b + c) + padicValNat p b + padicValNat p c)
      (deltaD p b c d / (d : ℚ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set vabc : ℕ := padicValNat p (b + c) + padicValNat p b + padicValNat p c
  have habc_dvd : p ^ vabc ∣ ((b + c) * b * c) := by
    have h1 : p ^ padicValNat p (b + c) ∣ (b + c) := pow_padicValNat_dvd
    have h2 : p ^ padicValNat p b ∣ b := pow_padicValNat_dvd
    have h3 : p ^ padicValNat p c ∣ c := pow_padicValNat_dvd
    simpa [vabc, pow_add, mul_assoc] using mul_dvd_mul (mul_dvd_mul h1 h2) h3
  have habc_dvdZ : (p : ℤ) ^ vabc ∣ (((b + c : ℤ) * (b : ℤ) * (c : ℤ))) := by
    exact_mod_cast habc_dvd
  by_cases hd1 : d = 1
  · subst hd1
    have hS1 : ∀ n : ℕ, sumS n 1 = (centralQ 1 (n : ℤ) : ℚ) / 3 := by
      intro n
      have h := sum_centralP 1 n
      have hP1 : ∀ m ∈ range n, centralP 1 (m : ℤ) = (m : ℤ) * ((m : ℤ) + 1) := by
        intro m _; simp [centralP]
      rw [sum_congr rfl hP1] at h
      have hQ : (3 : ℚ) * sumS n 1 = (centralQ 1 (n : ℤ) : ℚ) := by
        have h' : (3 : ℤ) * ∑ m ∈ range n, (m : ℤ) * ((m : ℤ) + 1) = centralQ 1 (n : ℤ) := by
          simpa using h
        have h'' : ((3 : ℤ) * ∑ m ∈ range n, (m : ℤ) * ((m : ℤ) + 1) : ℤ) = (centralQ 1 (n : ℤ) : ℚ) := by
          exact_mod_cast h'
        simpa [sumS] using h''
      linarith
    have hdiff : sumS (b + c) 1 - sumS b 1 - sumS c 1 =
        (((b + c : ℕ) * b * c : ℕ) : ℚ) := by
      rw [hS1, hS1, hS1]
      have hQ1 : ∀ x : ℤ, centralQ 1 x = x ^ 3 - x := by
        intro x; simp [centralQ]; ring
      rw [hQ1, hQ1, hQ1]
      push_cast; ring
    unfold deltaD
    push_cast
    rw [div_one, hdiff]
    have hU1 : pDiv p 1 (sumU p 1) := by
      simpa [sumU] using sum_inv_mul_sub_pDiv_one p hp hp5
    have hp2 : pDiv p 2 ((p : ℚ) ^ (2 * 1)) := by
      simpa using pDiv_of_dvd_nat (p := p) (k := 2) (n := p ^ 2) hp dvd_rfl
    have habc_pDiv : pDiv p vabc ((((b + c : ℕ) * b * c : ℕ) : ℚ)) :=
      pDiv_of_dvd_nat hp habc_dvd
    have htot := pDiv_mul hp (pDiv_mul hp hp2 hU1) habc_pDiv
    have hexp : 2 + 1 + vabc = 3 + padicValNat p (b + c) + padicValNat p b + padicValNat p c := by
      dsimp only [vabc]; omega
    rwa [hexp] at htot
  · have hd2 : 2 ≤ d := by omega
    rcases pow_eq_sum_centralP d hd with ⟨coeff, hcoeff⟩
    have hS_eq : ∀ n : ℕ, sumS n d =
        ∑ k ∈ Icc 1 d, (coeff k : ℚ) * (centralQ k (n : ℤ) : ℚ) / ((2 * k + 1 : ℕ) : ℚ) := by
      intro n
      have hstep : sumS n d = ∑ m ∈ range n, ∑ k ∈ Icc 1 d, (coeff k : ℚ) * (centralP k (m : ℤ) : ℚ) := by
        unfold sumS
        apply sum_congr rfl; intro m _
        have hm := hcoeff (m : ℤ)
        have hmQ : (((m : ℤ) * ((m : ℤ) + 1)) ^ d : ℤ) =
            ∑ k ∈ Icc 1 d, (coeff k : ℚ) * (centralP k (m : ℤ) : ℚ) := by
          exact_mod_cast hm
        simpa using hmQ
      rw [hstep, sum_comm]
      apply sum_congr rfl; intro k _
      rw [← mul_sum]
      have hsum := sum_centralP k n
      have hsumQ : ((2 * k + 1 : ℕ) : ℚ) * ∑ m ∈ range n, (centralP k (m : ℤ) : ℚ) =
          (centralQ k (n : ℤ) : ℚ) := by
        have h' : (((2 * (k : ℤ) + 1) * ∑ m ∈ range n, centralP k (m : ℤ) : ℤ) : ℚ) =
            (centralQ k (n : ℤ) : ℚ) := by exact_mod_cast hsum
        push_cast at h' ⊢
        simpa [add_comm, mul_comm] using h'
      have hne : ((2 * k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp [hne]
      linear_combination (coeff k : ℚ) * hsumQ
    have hdiff_eq : sumS (b + c) d - sumS b d - sumS c d =
        ∑ k ∈ Icc 1 d, (coeff k : ℚ) *
          ((centralQ k ((b + c : ℕ) : ℤ) - centralQ k (b : ℤ) - centralQ k (c : ℤ) : ℤ) : ℚ) /
            ((2 * k + 1 : ℕ) : ℚ) := by
      rw [hS_eq, hS_eq, hS_eq, ← sum_sub_distrib, ← sum_sub_distrib]
      apply sum_congr rfl; intro k _
      push_cast; ring
    unfold deltaD
    rw [hdiff_eq, mul_sum, sum_div]
    apply pDiv_sum hp
    intro k hk
    have hkd : k ≤ d := (mem_Icc.mp hk).2
    have hbound := kazandzidis_exp_bound p d k hp hp5 hd2 hkd
    have hQdvd : (p : ℤ) ^ vabc ∣
        (centralQ k ((b + c : ℕ) : ℤ) - centralQ k (b : ℤ) - centralQ k (c : ℤ)) := by
      have h1 := centralQ_sub_dvd k (b : ℤ) (c : ℤ)
      have hcast : ((b + c : ℕ) : ℤ) = (b : ℤ) + (c : ℤ) := by push_cast; rfl
      rw [hcast]
      exact dvd_trans habc_dvdZ h1
    have hQ_pDiv : pDiv p vabc
        (((centralQ k ((b + c : ℕ) : ℤ) - centralQ k (b : ℤ) - centralQ k (c : ℤ) : ℤ) : ℚ)) :=
      pDiv_int hp hQdvd
    have hnum_pDiv : pDiv p (2 * d + vabc)
        ((p : ℚ) ^ (2 * d) * sumU p d *
          ((coeff k : ℚ) *
            ((centralQ k ((b + c : ℕ) : ℤ) - centralQ k (b : ℤ) - centralQ k (c : ℤ) : ℤ) : ℚ))) := by
      have hp2d : pDiv p (2 * d) ((p : ℚ) ^ (2 * d)) := by
        simpa using pDiv_of_dvd_nat (p := p) (k := 2 * d) (n := p ^ (2 * d)) hp dvd_rfl
      have hU := sumU_pDiv_zero p d hp
      have hc0 := pDiv_int_zero hp (coeff k)
      have h1 := pDiv_mul hp hp2d hU
      have h2 := pDiv_mul hp hc0 hQ_pDiv
      simpa using pDiv_mul hp h1 h2
    have hrew : (p : ℚ) ^ (2 * d) * sumU p d *
        ((coeff k : ℚ) *
          ((centralQ k ((b + c : ℕ) : ℤ) - centralQ k (b : ℤ) - centralQ k (c : ℤ) : ℤ) : ℚ) /
            ((2 * k + 1 : ℕ) : ℚ)) / (d : ℚ) =
        ((p : ℚ) ^ (2 * d) * sumU p d *
          ((coeff k : ℚ) *
            ((centralQ k ((b + c : ℕ) : ℤ) - centralQ k (b : ℤ) - centralQ k (c : ℤ) : ℤ) : ℚ))) /
          ((2 * k + 1 : ℕ) : ℚ) / (d : ℚ) := by ring
    rw [hrew]
    apply pDiv_div_nat hp (by omega : d ≠ 0)
    apply pDiv_div_nat hp (by omega : 2 * k + 1 ≠ 0)
    apply pDiv_mono _ hnum_pDiv
    dsimp only [vabc]; omega

-- Formal derivative on PowerSeries ℚ (self-contained, avoids API quirks)
noncomputable def psDeriv (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((n + 1 : ℕ) : ℚ) * PowerSeries.coeff (n + 1) f

lemma coeff_psDeriv (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (psDeriv f) = ((n + 1 : ℕ) : ℚ) * PowerSeries.coeff (n + 1) f := by
  simp [psDeriv]

lemma psDeriv_zero : psDeriv 0 = 0 := by ext n; simp [coeff_psDeriv]
lemma psDeriv_one : psDeriv 1 = 0 := by ext n; simp [coeff_psDeriv, PowerSeries.coeff_one]
lemma psDeriv_C (r : ℚ) : psDeriv (PowerSeries.C r) = 0 := by ext n; simp [coeff_psDeriv]
lemma psDeriv_X : psDeriv PowerSeries.X = 1 := by
  ext n; cases n <;> simp [coeff_psDeriv, PowerSeries.coeff_X, PowerSeries.coeff_one]
lemma psDeriv_add (f g : PowerSeries ℚ) : psDeriv (f + g) = psDeriv f + psDeriv g := by
  ext n; simp [coeff_psDeriv]; ring
lemma psDeriv_sub (f g : PowerSeries ℚ) : psDeriv (f - g) = psDeriv f - psDeriv g := by
  ext n; simp [coeff_psDeriv]; ring

lemma psDeriv_mul (f g : PowerSeries ℚ) :
    psDeriv (f * g) = psDeriv f * g + f * psDeriv g := by
  ext n
  rw [coeff_psDeriv, map_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j g) (n + 1),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (psDeriv f) * PowerSeries.coeff j g) n,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j (psDeriv g)) n]
  simp only [coeff_psDeriv]
  -- Expand LHS: ∑_{i=0}^{n+1} (n + 1) * f_i * g_{n+1-i}
  -- = ∑_{i=0}^{n+1} i * f_i * g_{n+1-i} + ∑_{i=0}^{n+1} (n + 1 - i) * f_i * g_{n+1-i}
  have h1 : ((n + 1 : ℕ) : ℚ) * ∑ i ∈ range (n + 2), PowerSeries.coeff i f * PowerSeries.coeff (n + 1 - i) g =
      (∑ i ∈ range (n + 2), (i : ℚ) * PowerSeries.coeff i f * PowerSeries.coeff (n + 1 - i) g) +
      (∑ i ∈ range (n + 2), ((n + 1 - i : ℕ) : ℚ) * PowerSeries.coeff i f * PowerSeries.coeff (n + 1 - i) g) := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro i hi
    have hle : i ≤ n + 1 := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hcast : ((n + 1 - i : ℕ) : ℚ) = ((n + 1 : ℕ) : ℚ) - (i : ℚ) := Nat.cast_sub hle
    rw [hcast]; ring
  rw [h1]
  congr 1
  · rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    apply sum_congr rfl; intro i _
    have : n + 1 - (i + 1) = n - i := by omega
    rw [this]
  · rw [sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
    apply sum_congr rfl; intro i hi
    have hle : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have : n + 1 - i = (n - i) + 1 := by omega
    rw [this]; ring

noncomputable def geomPS (r : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => r ^ n

lemma coeff_geomPS (r : ℚ) (n : ℕ) : PowerSeries.coeff n (geomPS r) = r ^ n := by
  simp [geomPS]

lemma one_add_C_mul_X_mul_geomPS (r : ℚ) :
    (1 + PowerSeries.C r * PowerSeries.X) * geomPS (-r) = 1 := by
  ext n
  rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (1 + PowerSeries.C r * PowerSeries.X) *
          PowerSeries.coeff j (geomPS (-r))) n]
  cases n with
  | zero => simp [coeff_geomPS]
  | succ n =>
    have h1 : ∀ i ∈ range (n + 2),
        PowerSeries.coeff i (1 + PowerSeries.C r * PowerSeries.X) *
          PowerSeries.coeff (n + 1 - i) (geomPS (-r)) =
        if i = 0 then (-r) ^ (n + 1)
        else if i = 1 then r * (-r) ^ n
        else 0 := by
      intro i _
      rcases i with _ | _ | i
      · simp [coeff_geomPS]
      · simp [coeff_geomPS, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
      · simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
    rw [sum_congr rfl h1, sum_range_succ', sum_range_succ']
    simp [pow_succ']

lemma derivative_prod_one_add_X {ι : Type*} (s : Finset ι) (c : ι → ℚ) :
    psDeriv (∏ i ∈ s, (1 + PowerSeries.C (c i) * PowerSeries.X)) =
      (∏ i ∈ s, (1 + PowerSeries.C (c i) * PowerSeries.X)) *
        (∑ i ∈ s, PowerSeries.C (c i) * geomPS (-c i)) := by
  classical
  induction s using Finset.induction with
  | empty => simp [psDeriv_one]
  | @insert x s hx ih =>
    rw [prod_insert hx, sum_insert hx, psDeriv_mul, ih]
    have hdx : psDeriv (1 + PowerSeries.C (c x) * PowerSeries.X) = PowerSeries.C (c x) := by
      rw [psDeriv_add, psDeriv_one, psDeriv_mul, psDeriv_C, psDeriv_X]; simp
    rw [hdx]
    set P := ∏ i ∈ s, (1 + PowerSeries.C (c i) * PowerSeries.X)
    set L := ∑ i ∈ s, PowerSeries.C (c i) * geomPS (-c i)
    have hinv : (1 + PowerSeries.C (c x) * PowerSeries.X) * geomPS (-c x) = 1 :=
      one_add_C_mul_X_mul_geomPS (c x)
    calc PowerSeries.C (c x) * P + (1 + PowerSeries.C (c x) * PowerSeries.X) * (P * L)
        = P * (PowerSeries.C (c x) * ((1 + PowerSeries.C (c x) * PowerSeries.X) * geomPS (-c x))) +
            (1 + PowerSeries.C (c x) * PowerSeries.X) * P * L := by rw [hinv, mul_one]; ring
      _ = (1 + PowerSeries.C (c x) * PowerSeries.X) * P *
            (PowerSeries.C (c x) * geomPS (-c x) + L) := by ring

-- Recursive sequence h via well-founded recursion using Finset.attach!
noncomputable def newtonH (Δ : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 =>
    (∑ j ∈ (range (k + 1)).attach,
      (-1 : ℚ) ^ (k - j.1) * Δ (k + 1 - j.1) * newtonH Δ j.1) / ((k + 1 : ℕ) : ℚ)
termination_by k => k
decreasing_by
  exact mem_range.mp j.2

lemma newtonH_zero (Δ : ℕ → ℚ) : newtonH Δ 0 = 1 := by rw [newtonH]

lemma newtonH_succ (Δ : ℕ → ℚ) (k : ℕ) :
    newtonH Δ (k + 1) =
      (∑ d ∈ Icc 1 (k + 1), (-1 : ℚ) ^ (d - 1) * Δ d * newtonH Δ (k + 1 - d)) /
        ((k + 1 : ℕ) : ℚ) := by
  rw [newtonH]
  congr 1
  have h1 : (∑ j ∈ (range (k + 1)).attach, (-1 : ℚ) ^ (k - j.1) * Δ (k + 1 - j.1) * newtonH Δ j.1) =
      ∑ j ∈ range (k + 1), (-1 : ℚ) ^ (k - j) * Δ (k + 1 - j) * newtonH Δ j :=
    Finset.sum_attach (range (k + 1)) (fun j => (-1 : ℚ) ^ (k - j) * Δ (k + 1 - j) * newtonH Δ j)
  rw [h1]
  refine Finset.sum_bij (fun j _ => k + 1 - j) ?_ ?_ ?_ ?_
  · intro j hj; simp only [mem_range, mem_Icc] at hj ⊢; omega
  · intro j₁ hj₁ j₂ hj₂ h; simp only [mem_range] at hj₁ hj₂; omega
  · intro d hd
    refine ⟨k + 1 - d, ?_, ?_⟩
    · simp only [mem_Icc, mem_range] at hd ⊢; omega
    · simp only [mem_Icc] at hd; omega
  · intro j hj
    have hjk : j < k + 1 := mem_range.mp hj
    have e1 : k + 1 - j - 1 = k - j := by omega
    have e2 : k + 1 - (k + 1 - j) = j := by omega
    rw [e1, e2]

lemma newtonH_derivative (Δ : ℕ → ℚ) :
    psDeriv (PowerSeries.mk (newtonH Δ)) =
      PowerSeries.mk (newtonH Δ) * PowerSeries.mk (fun n => (-1 : ℚ) ^ n * Δ (n + 1)) := by
  ext k
  rw [coeff_psDeriv, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (PowerSeries.mk (newtonH Δ)) *
          PowerSeries.coeff j (PowerSeries.mk (fun n => (-1 : ℚ) ^ n * Δ (n + 1)))) k]
  rw [newtonH_succ]
  have hk0 : ((k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [mul_div_cancel₀ _ hk0]
  refine Finset.sum_bij (fun d _ => k + 1 - d) ?_ ?_ ?_ ?_
  · intro d hd; simp only [mem_Icc, mem_range] at hd ⊢; omega
  · intro d₁ hd₁ d₂ hd₂ h; simp only [mem_Icc] at hd₁ hd₂; omega
  · intro j hj
    refine ⟨k + 1 - j, ?_, ?_⟩
    · simp only [mem_range, mem_Icc] at hj ⊢; omega
    · simp only [mem_range] at hj; omega
  · intro d hd
    have hd1 := (mem_Icc.mp hd).1
    have hd2 := (mem_Icc.mp hd).2
    simp only [PowerSeries.coeff_mk]
    have h1 : k - (k + 1 - d) = d - 1 := by omega
    have h2 : d - 1 + 1 = d := by omega
    rw [h1, h2]; ring

lemma powerSeries_eq_of_derivative_mul {D L : PowerSeries ℚ}
    (h0 : PowerSeries.coeff 0 D = 0)
    (hderiv : psDeriv D = D * L) : D = 0 := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa using h0
    | succ k =>
      have hk := congrArg (PowerSeries.coeff k) hderiv
      rw [coeff_psDeriv, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => PowerSeries.coeff i D * PowerSeries.coeff j L) k] at hk
      have hzero : (∑ i ∈ range (k + 1), PowerSeries.coeff i D * PowerSeries.coeff (k - i) L) = 0 := by
        apply sum_eq_zero; intro i hi
        have hik : i < k + 1 := mem_range.mp hi
        rw [ih i hik, map_zero, zero_mul]
      rw [hzero] at hk
      have hne : ((k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      simpa using (mul_eq_zero.mp hk).resolve_left hne

lemma prod_eq_prod_mul_newtonH {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (c : ι → ℚ) (d : κ → ℚ) :
    let F : PowerSeries ℚ := ∏ i ∈ s, (1 + PowerSeries.C (c i) * PowerSeries.X)
    let G : PowerSeries ℚ := ∏ j ∈ t, (1 + PowerSeries.C (d j) * PowerSeries.X)
    let Δ : ℕ → ℚ := fun k => (∑ i ∈ s, (c i) ^ k) - (∑ j ∈ t, (d j) ^ k)
    F = G * PowerSeries.mk (newtonH Δ) := by
  intro F G Δ
  set H : PowerSeries ℚ := PowerSeries.mk (newtonH Δ)
  set LF : PowerSeries ℚ := ∑ i ∈ s, PowerSeries.C (c i) * geomPS (-c i)
  set LG : PowerSeries ℚ := ∑ j ∈ t, PowerSeries.C (d j) * geomPS (-d j)
  have hLFG : LF - LG = PowerSeries.mk (fun n => (-1 : ℚ) ^ n * Δ (n + 1)) := by
    ext n
    simp only [LF, LG, Δ, map_sub, map_sum, PowerSeries.coeff_C_mul, coeff_geomPS,
      PowerSeries.coeff_mk]
    have hpow : ∀ r : ℚ, r * (-r) ^ n = (-1 : ℚ) ^ n * r ^ (n + 1) := by
      intro r; rw [neg_eq_neg_one_mul, mul_pow, pow_succ']; ring
    simp only [hpow, ← mul_sum, ← mul_sub]
  have hF' : psDeriv F = F * LF := derivative_prod_one_add_X s c
  have hG' : psDeriv G = G * LG := derivative_prod_one_add_X t d
  have hH' : psDeriv H = H * (LF - LG) := by
    rw [hLFG]; exact newtonH_derivative Δ
  have hD0 : PowerSeries.coeff 0 (F - G * H) = 0 := by
    have hF0 : PowerSeries.constantCoeff F = 1 := by simp [F, map_prod]
    have hG0 : PowerSeries.constantCoeff G = 1 := by simp [G, map_prod]
    have hH0 : PowerSeries.constantCoeff H = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff]; simp [H, newtonH_zero]
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_sub, map_mul, hF0, hG0, hH0]; ring
  have hD' : psDeriv (F - G * H) = (F - G * H) * LF := by
    rw [psDeriv_sub, psDeriv_mul, hF', hG', hH']
    ring
  exact sub_eq_zero.mp (powerSeries_eq_of_derivative_mul hD0 hD')

lemma newtonH_pDiv {p V : ℕ} {Δ : ℕ → ℚ} (hp : p.Prime)
    (hΔ : ∀ d, 1 ≤ d → pDiv p V (Δ d / (d : ℚ))) :
    ∀ k, 1 ≤ k → k < V → pDiv p V (newtonH Δ k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk1 hkV
    cases k with
    | zero => omega
    | succ m =>
      rw [newtonH_succ, sum_div]
      apply pDiv_sum hp
      intro d hd
      have hd1 := (mem_Icc.mp hd).1
      have hd2 := (mem_Icc.mp hd).2
      by_cases hdeq : d = m + 1
      · subst hdeq
        have hsub : m + 1 - (m + 1) = 0 := by omega
        rw [hsub, newtonH_zero, mul_one, mul_div_assoc]
        have hsign : pDiv p 0 ((-1 : ℚ) ^ (m + 1 - 1)) := by
          simpa using pDiv_int_zero hp ((-1 : ℤ) ^ (m + 1 - 1))
        simpa using pDiv_mul hp hsign (hΔ (m + 1) (by omega))
      · have hlt : 1 ≤ m + 1 - d := by omega
        have hlt2 : m + 1 - d < m + 1 := by omega
        have hih := ih (m + 1 - d) hlt2 hlt (by omega)
        have hΔd : pDiv p V (Δ d) := by
          have h1 := hΔ d hd1
          have h2 := pDiv_nat_zero hp d
          have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have h3 := pDiv_mul hp h1 h2
          rw [div_mul_cancel₀ _ hd0] at h3
          simpa using h3
        have hsign : pDiv p 0 ((-1 : ℚ) ^ (d - 1)) := by
          simpa using pDiv_int_zero hp ((-1 : ℤ) ^ (d - 1))
        have hprod := pDiv_mul hp (pDiv_mul hp hsign hΔd) hih
        have : Fact p.Prime := ⟨hp⟩
        have hv_lt : padicValNat p (m + 1) < V := by
          have hpow : p ^ padicValNat p (m + 1) ≤ m + 1 :=
            Nat.le_of_dvd (by omega) pow_padicValNat_dvd
          have hlt2 : padicValNat p (m + 1) < p ^ padicValNat p (m + 1) :=
            Nat.lt_pow_self hp.one_lt
          omega
        apply pDiv_div_nat hp (by omega : m + 1 ≠ 0)
        exact pDiv_mono (by omega) hprod

lemma prod_one_add_coeff_pDiv {ι : Type*} {p : ℕ} (hp : p.Prime)
    (s : Finset ι) (c : ι → ℚ) (hc : ∀ i ∈ s, pDiv p 2 (c i)) :
    ∀ k, pDiv p (2 * k) (PowerSeries.coeff k (∏ i ∈ s, (1 + PowerSeries.C (c i) * PowerSeries.X))) := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro k
    cases k with
    | zero => simpa using pDiv_nat_zero hp 1
    | succ k => simp [pDiv_zero p _ hp]
  | @insert x s hx ih =>
    intro k
    rw [prod_insert hx, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i (1 + PowerSeries.C (c x) * PowerSeries.X) *
            PowerSeries.coeff j (∏ y ∈ s, (1 + PowerSeries.C (c y) * PowerSeries.X))) k]
    apply pDiv_sum hp
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rcases j with _ | _ | j
    · simp only [map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_X,
        Nat.sub_zero]
      simpa using ih (fun y hy => hc y (mem_insert_of_mem hy)) k
    · have h1 := hc x (mem_insert_self x s)
      have h2 := ih (fun y hy => hc y (mem_insert_of_mem hy)) (k - 1)
      have hmul := pDiv_mul hp h1 h2
      have hexp : 2 + 2 * (k - 1) = 2 * k := by omega
      rw [hexp] at hmul
      simpa [map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_X] using hmul
    · simp [pDiv_zero p _ hp]

lemma prod_one_add_natDegree_le {ι : Type*} (s : Finset ι) (c : ι → ℚ) :
    (∏ i ∈ s, (1 + Polynomial.C (c i) * Polynomial.X)).natDegree ≤ s.card := by
  calc (∏ i ∈ s, (1 + Polynomial.C (c i) * Polynomial.X)).natDegree
      ≤ ∑ i ∈ s, (1 + Polynomial.C (c i) * Polynomial.X).natDegree :=
        Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i ∈ s, 1 := by
        apply sum_le_sum; intro i _
        calc (1 + Polynomial.C (c i) * Polynomial.X).natDegree
            ≤ max (1 : Polynomial ℚ).natDegree (Polynomial.C (c i) * Polynomial.X).natDegree :=
              Polynomial.natDegree_add_le _ _
          _ ≤ 1 := by
              simp only [Polynomial.natDegree_one, max_le_iff, zero_le, true_and]
              exact le_trans Polynomial.natDegree_mul_le (by simp)
    _ = s.card := by simp

lemma coe_prod_one_add_X {ι : Type*} (s : Finset ι) (c : ι → ℚ) :
    ((∏ i ∈ s, (1 + Polynomial.C (c i) * Polynomial.X) : Polynomial ℚ) : PowerSeries ℚ) =
      ∏ i ∈ s, (1 + PowerSeries.C (c i) * PowerSeries.X) := by
  classical
  induction s using Finset.induction with
  | empty => simp [Polynomial.coe_one]
  | @insert x s hx ih =>
    rw [prod_insert hx, prod_insert hx, Polynomial.coe_mul, ih,
        Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X]

lemma prod_one_add_eq_sum_coeff {ι : Type*} (s : Finset ι) (c : ι → ℚ) :
    ∏ i ∈ s, (1 + c i) =
      ∑ k ∈ range (s.card + 1),
        PowerSeries.coeff k (∏ i ∈ s, (1 + PowerSeries.C (c i) * PowerSeries.X)) := by
  set P : Polynomial ℚ := ∏ i ∈ s, (1 + Polynomial.C (c i) * Polynomial.X)
  have hP_ps : (P : PowerSeries ℚ) = ∏ i ∈ s, (1 + PowerSeries.C (c i) * PowerSeries.X) :=
    coe_prod_one_add_X s c
  have hdeg : P.natDegree ≤ s.card := prod_one_add_natDegree_le s c
  have heval : P.eval 1 = ∏ i ∈ s, (1 + c i) := by
    simp [P, Polynomial.eval_prod]
  rw [← heval, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg)]
  apply sum_congr rfl
  intro k _
  rw [one_pow, mul_one, ← Polynomial.coeff_coe, hP_ps]

lemma prod_sub_prod_pDiv {ι κ : Type*} {p V : ℕ} (hp : p.Prime)
    (s : Finset ι) (t : Finset κ) (c : ι → ℚ) (d : κ → ℚ)
    (hc : ∀ i ∈ s, pDiv p 2 (c i)) (hd : ∀ j ∈ t, pDiv p 2 (d j))
    (hΔ : ∀ (k : ℕ), 1 ≤ k → pDiv p V (((∑ i ∈ s, (c i) ^ k) - (∑ j ∈ t, (d j) ^ k)) / (k : ℚ))) :
    pDiv p V ((∏ i ∈ s, (1 + c i)) - (∏ j ∈ t, (1 + d j))) := by
  set F : PowerSeries ℚ := ∏ i ∈ s, (1 + PowerSeries.C (c i) * PowerSeries.X)
  set G : PowerSeries ℚ := ∏ j ∈ t, (1 + PowerSeries.C (d j) * PowerSeries.X)
  set Δ : ℕ → ℚ := fun k => (∑ i ∈ s, (c i) ^ k) - (∑ j ∈ t, (d j) ^ k)
  have hFG : F = G * PowerSeries.mk (newtonH Δ) := prod_eq_prod_mul_newtonH s t c d
  set D : ℕ := max s.card t.card
  have hF_eval : ∏ i ∈ s, (1 + c i) = ∑ k ∈ range (D + 1), PowerSeries.coeff k F := by
    rw [prod_one_add_eq_sum_coeff]
    apply sum_subset (range_mono (by omega : s.card + 1 ≤ D + 1))
    intro k _ hk
    have hgt : s.card < k := by simp only [mem_range] at hk; omega
    set P : Polynomial ℚ := ∏ i ∈ s, (1 + Polynomial.C (c i) * Polynomial.X)
    have hP_ps : (P : PowerSeries ℚ) = ∏ i ∈ s, (1 + PowerSeries.C (c i) * PowerSeries.X) :=
      coe_prod_one_add_X s c
    rw [← hP_ps, Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (prod_one_add_natDegree_le s c) hgt)
  have hG_eval : ∏ j ∈ t, (1 + d j) = ∑ k ∈ range (D + 1), PowerSeries.coeff k G := by
    rw [prod_one_add_eq_sum_coeff]
    apply sum_subset (range_mono (by omega : t.card + 1 ≤ D + 1))
    intro k _ hk
    have hgt : t.card < k := by simp only [mem_range] at hk; omega
    set P : Polynomial ℚ := ∏ j ∈ t, (1 + Polynomial.C (d j) * Polynomial.X)
    have hP_ps : (P : PowerSeries ℚ) = ∏ j ∈ t, (1 + PowerSeries.C (d j) * PowerSeries.X) :=
      coe_prod_one_add_X t d
    rw [← hP_ps, Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (prod_one_add_natDegree_le t d) hgt)
  rw [hF_eval, hG_eval, ← sum_sub_distrib]
  apply pDiv_sum hp
  intro k _
  by_cases hkV : k < V
  · rw [hFG, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i G * PowerSeries.coeff j (PowerSeries.mk (newtonH Δ))) k]
    cases k with
    | zero =>
      simp [newtonH_zero, pDiv_zero p V hp]
    | succ m =>
      rw [sum_range_succ, Nat.sub_self]
      have hH0 : PowerSeries.coeff 0 (PowerSeries.mk (newtonH Δ)) = 1 := by
        simp [newtonH_zero]
      rw [hH0, mul_one, add_sub_cancel_right]
      apply pDiv_sum hp
      intro i hi
      have him : i < m + 1 := mem_range.mp hi
      have hG_pDiv : pDiv p 0 (PowerSeries.coeff i G) :=
        pDiv_mono (Nat.zero_le _) (prod_one_add_coeff_pDiv hp t d hd i)
      have hH_pDiv : pDiv p V (PowerSeries.coeff (m + 1 - i) (PowerSeries.mk (newtonH Δ))) := by
        rw [PowerSeries.coeff_mk]
        exact newtonH_pDiv hp hΔ (m + 1 - i) (by omega) (by omega)
      simpa using pDiv_mul hp hG_pDiv hH_pDiv
  · have hFk : pDiv p V (PowerSeries.coeff k F) :=
      pDiv_mono (by omega) (prod_one_add_coeff_pDiv hp s c hc k)
    have hGk : pDiv p V (PowerSeries.coeff k G) :=
      pDiv_mono (by omega) (prod_one_add_coeff_pDiv hp t d hd k)
    exact pDiv_sub hp hFk hGk

-- ============================================================================
-- Section 4: Connect to C(a * p, b * p) / C(a, b) — Kazandzidis's Theorem!
-- ============================================================================

lemma factorial_mul_p_eq (n p : ℕ) (hp : 0 < p) :
    ((n * p).factorial : ℚ) =
      (p : ℚ) ^ n * (n.factorial : ℚ) *
        ∏ m ∈ range n, ∏ u ∈ Ico 1 p, ((m * p + u : ℕ) : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : ((n + 1) * p).factorial =
        (n * p).factorial * ∏ j ∈ Icc 1 p, (n * p + j) := by
      have hstep : ∀ k : ℕ, (n * p + k).factorial =
          (n * p).factorial * ∏ j ∈ Icc 1 k, (n * p + j) := by
        intro k
        induction k with
        | zero => simp
        | succ k ihk =>
          rw [show n * p + (k + 1) = (n * p + k) + 1 by omega, Nat.factorial_succ, ihk]
          have hIcc : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
            ext x; simp only [mem_Icc, mem_insert]; omega
          rw [hIcc, prod_insert (by simp)]
          ring
      simpa [Nat.succ_mul] using hstep p
    have hIcc_split : (∏ j ∈ Icc 1 p, (n * p + j)) =
        ((n + 1) * p) * ∏ u ∈ Ico 1 p, (n * p + u) := by
      have hI : Icc 1 p = insert p (Ico 1 p) := by
        ext x; simp only [mem_Icc, mem_Ico, mem_insert]; omega
      rw [hI, prod_insert (by simp)]
      have : n * p + p = (n + 1) * p := by ring
      rw [this]
    rw [hsplit, hIcc_split]
    push_cast
    rw [ih, prod_range_succ, Nat.factorial_succ]
    push_cast
    ring

lemma choose_mul_p_ratio (b c p : ℕ) (hp : p.Prime) :
    (((b + c) * p).choose (b * p) : ℚ) / ((b + c).choose b : ℚ) =
      (∏ m ∈ range (b + c), ∏ u ∈ Ico 1 p, (((m * p + u : ℕ) : ℚ) / (u : ℚ))) /
        ((∏ m ∈ range b, ∏ u ∈ Ico 1 p, (((m * p + u : ℕ) : ℚ) / (u : ℚ))) *
         (∏ m ∈ range c, ∏ u ∈ Ico 1 p, (((m * p + u : ℕ) : ℚ) / (u : ℚ)))) := by
  have hch1 : (((b + c) * p).choose (b * p) : ℚ) =
      (((b + c) * p).factorial : ℚ) / (((b * p).factorial : ℚ) * ((c * p).factorial : ℚ)) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show b * p ≤ (b + c) * p by nlinarith)
    have hsub : (b + c) * p - b * p = c * p := by
      rw [add_mul, Nat.add_sub_cancel_left]
    rw [hsub] at h
    have hQ : (((b + c) * p).choose (b * p) : ℚ) * ((b * p).factorial : ℚ) * ((c * p).factorial : ℚ) =
        (((b + c) * p).factorial : ℚ) := by exact_mod_cast h
    have hb0 : ((b * p).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hc0 : ((c * p).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp [hb0, hc0]; linarith
  have hch2 : ((b + c).choose b : ℚ) =
      ((b + c).factorial : ℚ) / ((b.factorial : ℚ) * (c.factorial : ℚ)) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right b c)
    rw [Nat.add_sub_cancel_left] at h
    have hQ : ((b + c).choose b : ℚ) * (b.factorial : ℚ) * (c.factorial : ℚ) =
        ((b + c).factorial : ℚ) := by exact_mod_cast h
    have hb0 : (b.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hc0 : (c.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp [hb0, hc0]; linarith
  rw [hch1, hch2, factorial_mul_p_eq (b + c) p hp.pos, factorial_mul_p_eq b p hp.pos,
      factorial_mul_p_eq c p hp.pos]
  -- Cancel (p^(b+c) * (b+c)!) / (p^b * b! * p^c * c!) and divide numerator and denominator by (∏ u)^(b+c)!
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hbc0 : ((b + c).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hb0 : (b.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hc0 : (c.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hU0 : (∏ u ∈ Ico 1 p, (u : ℚ)) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro u hu; exact Nat.cast_ne_zero.mpr (by have := (mem_Ico.mp hu).1; omega)
  have hdiv_prod : ∀ n : ℕ,
      ∏ m ∈ range n, ∏ u ∈ Ico 1 p, (((m * p + u : ℕ) : ℚ) / (u : ℚ)) =
        (∏ m ∈ range n, ∏ u ∈ Ico 1 p, ((m * p + u : ℕ) : ℚ)) / (∏ u ∈ Ico 1 p, (u : ℚ)) ^ n := by
    intro n
    simp only [prod_div_distrib, prod_const, card_range]
  rw [hdiv_prod (b + c), hdiv_prod b, hdiv_prod c, pow_add, pow_add]
  have hPne : ∀ n : ℕ, (∏ m ∈ range n, ∏ u ∈ Ico 1 p, ((m * p + u : ℕ) : ℚ)) ≠ 0 := by
    intro n; apply prod_ne_zero_iff.mpr; intro m _
    apply prod_ne_zero_iff.mpr; intro u hu
    exact Nat.cast_ne_zero.mpr (by have := (mem_Ico.mp hu).1; omega)
  field_simp [hp0, hbc0, hb0, hc0, hU0, hPne b, hPne c]

lemma prod_block_sq (m p : ℕ) :
    (∏ u ∈ Ico 1 p, (((m * p + u : ℕ) : ℚ) / (u : ℚ))) ^ 2 =
      ∏ u ∈ Ico 1 p, (1 + ((m : ℚ) * ((m : ℚ) + 1) * (p : ℚ) ^ 2) / ((u : ℚ) * ((p - u : ℕ) : ℚ))) := by
  rw [sq]
  have hrev : ∏ u ∈ Ico 1 p, (((m * p + u : ℕ) : ℚ) / (u : ℚ)) =
      ∏ u ∈ Ico 1 p, (((m * p + (p - u) : ℕ) : ℚ) / ((p - u : ℕ) : ℚ)) := by
    refine Finset.prod_bij (fun u _ => p - u) ?_ ?_ ?_ ?_
    · intro u hu; simp only [mem_Ico] at hu ⊢; omega
    · intro u₁ hu₁ u₂ hu₂ h; simp only [mem_Ico] at hu₁ hu₂; omega
    · intro v hv
      refine ⟨p - v, ?_, ?_⟩
      · simp only [mem_Ico] at hv ⊢; omega
      · simp only [mem_Ico] at hv; omega
    · intro u hu
      have hu2 := (mem_Ico.mp hu).2
      rw [Nat.sub_sub_self (by omega)]
  conv_lhs => rhs; rw [hrev]
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro u hu
  have hu1 := (mem_Ico.mp hu).1
  have hu2 := (mem_Ico.mp hu).2
  have hu0 : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsub : ((p - u : ℕ) : ℚ) = (p : ℚ) - (u : ℚ) := Nat.cast_sub (by omega)
  have hpu0' : (p : ℚ) - (u : ℚ) ≠ 0 := by
    rw [← hsub]; exact Nat.cast_ne_zero.mpr (by omega)
  push_cast
  rw [hsub]
  field_simp [hu0, hpu0']
  ring

-- Main Kazandzidis theorem (ratio form and integer divisibility form)!
theorem kazandzidis_ratio_pDiv (p b c : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hb : 0 < b) (hc : 0 < c) :
    pDiv p (3 + padicValNat p (b + c) + padicValNat p b + padicValNat p c)
      ((((b + c) * p).choose (b * p) : ℚ) / ((b + c).choose b : ℚ) - 1) := by
  set V := 3 + padicValNat p (b + c) + padicValNat p b + padicValNat p c
  set r : ℚ := (((b + c) * p).choose (b * p) : ℚ) / ((b + c).choose b : ℚ)
  set P : ℕ → ℚ := fun n =>
    ∏ m ∈ range n, ∏ u ∈ Ico 1 p, (((m * p + u : ℕ) : ℚ) / (u : ℚ))
  set Q : ℕ → ℚ := fun n =>
    ∏ m ∈ range n, ∏ u ∈ Ico 1 p,
      (1 + ((m : ℚ) * ((m : ℚ) + 1) * (p : ℚ) ^ 2) / ((u : ℚ) * ((p - u : ℕ) : ℚ)))
  have hPQ : ∀ n : ℕ, (P n) ^ 2 = Q n := by
    intro n
    dsimp only [P, Q]
    rw [← prod_pow]
    apply prod_congr rfl; intro m _
    exact prod_block_sq m p
  have hr : r = P (b + c) / (P b * P c) := choose_mul_p_ratio b c p hp
  have hP_mod1 : ∀ n : ℕ, pDiv p 1 (P n - 1) := by
    intro n
    have hfactor : ∀ m ∈ range n, ∀ u ∈ Ico 1 p,
        pDiv p 1 ((((m * p + u : ℕ) : ℚ) / (u : ℚ)) - 1) := by
      intro m _ u hu
      have hu1 := (mem_Ico.mp hu).1
      have hu2 := (mem_Ico.mp hu).2
      have hndvd : ¬ p ∣ u := fun h => by have := Nat.le_of_dvd (by omega) h; omega
      have hu0 : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      refine ⟨m, u, hndvd, ?_⟩
      push_cast; field_simp [hu0]; ring
    have hprod_sub : ∀ (s : Finset ℕ) (f : ℕ → ℚ),
        (∀ i ∈ s, pDiv p 1 (f i - 1)) → pDiv p 1 ((∏ i ∈ s, f i) - 1) := by
      classical
      intro s f hf
      induction s using Finset.induction with
      | empty => simp [pDiv_zero p 1 hp]
      | @insert x s hx ih =>
        rw [prod_insert hx]
        have hfx := hf x (mem_insert_self x s)
        have hfs := ih (fun y hy => hf y (mem_insert_of_mem hy))
        have hfx0 : pDiv p 0 (f x) := by
          have : f x = (f x - 1) + 1 := by ring
          rw [this]
          exact pDiv_add hp (pDiv_mono (by omega) hfx) (pDiv_nat_zero hp 1)
        have hrew : f x * (∏ i ∈ s, f i) - 1 = f x * ((∏ i ∈ s, f i) - 1) + (f x - 1) := by ring
        rw [hrew]
        exact pDiv_add hp (by simpa using pDiv_mul hp hfx0 hfs) hfx
    dsimp only [P]
    exact hprod_sub (range n) (fun m => ∏ u ∈ Ico 1 p, (((m * p + u : ℕ) : ℚ) / (u : ℚ)))
      (fun m hm => hprod_sub (Ico 1 p) (fun u => (((m * p + u : ℕ) : ℚ) / (u : ℚ))) (hfactor m hm))
  have hP_pDiv0 : ∀ n : ℕ, pDiv p 0 (P n) := by
    intro n
    have : P n = (P n - 1) + 1 := by ring
    rw [this]
    exact pDiv_add hp (pDiv_mono (by omega) (hP_mod1 n)) (pDiv_nat_zero hp 1)
  -- Apply prod_sub_prod_pDiv to Q (b + c) - Q b * Q c!
  set cfn : ℕ × ℕ → ℚ := fun x =>
    ((x.1 : ℚ) * ((x.1 : ℚ) + 1) * (p : ℚ) ^ 2) / ((x.2 : ℚ) * ((p - x.2 : ℕ) : ℚ))
  set s : Finset (ℕ × ℕ) := range (b + c) ×ˢ Ico 1 p
  set t : Finset ((ℕ × ℕ) ⊕ (ℕ × ℕ)) :=
    (range b ×ˢ Ico 1 p).disjSum (range c ×ˢ Ico 1 p)
  set dfn : (ℕ × ℕ) ⊕ (ℕ × ℕ) → ℚ := Sum.elim cfn cfn
  have hcfn_pDiv2 : ∀ x ∈ s, pDiv p 2 (cfn x) := by
    intro x hx
    have hu := (mem_product.mp hx).2
    have hu1 := (mem_Ico.mp hu).1
    have hu2 := (mem_Ico.mp hu).2
    have hndvd_u : ¬ p ∣ x.2 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
    have hndvd_pu : ¬ p ∣ (p - x.2) := fun h => by have := Nat.le_of_dvd (by omega) h; omega
    refine ⟨(x.1 : ℤ) * ((x.1 : ℤ) + 1), x.2 * (p - x.2), hp.not_dvd_mul hndvd_u hndvd_pu, ?_⟩
    simp only [cfn]; push_cast; ring
  have hdfn_pDiv2 : ∀ y ∈ t, pDiv p 2 (dfn y) := by
    intro y hy
    rcases y with x | x
    · have hx : x ∈ range b ×ˢ Ico 1 p := by simpa [t] using hy
      have hu := (mem_product.mp hx).2
      have hu1 := (mem_Ico.mp hu).1
      have hu2 := (mem_Ico.mp hu).2
      have hndvd_u : ¬ p ∣ x.2 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
      have hndvd_pu : ¬ p ∣ (p - x.2) := fun h => by have := Nat.le_of_dvd (by omega) h; omega
      refine ⟨(x.1 : ℤ) * ((x.1 : ℤ) + 1), x.2 * (p - x.2), hp.not_dvd_mul hndvd_u hndvd_pu, ?_⟩
      simp only [dfn, Sum.elim_inl, cfn]; push_cast; ring
    · have hx : x ∈ range c ×ˢ Ico 1 p := by simpa [t] using hy
      have hu := (mem_product.mp hx).2
      have hu1 := (mem_Ico.mp hu).1
      have hu2 := (mem_Ico.mp hu).2
      have hndvd_u : ¬ p ∣ x.2 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
      have hndvd_pu : ¬ p ∣ (p - x.2) := fun h => by have := Nat.le_of_dvd (by omega) h; omega
      refine ⟨(x.1 : ℤ) * ((x.1 : ℤ) + 1), x.2 * (p - x.2), hp.not_dvd_mul hndvd_u hndvd_pu, ?_⟩
      simp only [dfn, Sum.elim_inr, cfn]; push_cast; ring
  have hΔ_eq : ∀ d : ℕ,
      (∑ x ∈ s, (cfn x) ^ d) - (∑ y ∈ t, (dfn y) ^ d) = deltaD p b c d := by
    intro d
    have hsum_prod : ∀ n : ℕ, ∑ x ∈ range n ×ˢ Ico 1 p, (cfn x) ^ d =
        (p : ℚ) ^ (2 * d) * sumU p d * sumS n d := by
      intro n
      rw [sum_product]
      have hinner : ∀ m ∈ range n,
          ∑ u ∈ Ico 1 p, (cfn (m, u)) ^ d =
            (p : ℚ) ^ (2 * d) * sumU p d * ((m : ℚ) * ((m : ℚ) + 1)) ^ d := by
        intro m _
        simp only [cfn, sumU, mul_sum, sum_mul]
        apply sum_congr rfl; intro u _
        rw [div_pow, mul_pow, ← pow_mul, div_pow, one_pow]
        ring
      rw [sum_congr rfl hinner, ← mul_sum]
      rfl
    have ht_sum : ∑ y ∈ t, (dfn y) ^ d =
        (∑ x ∈ range b ×ˢ Ico 1 p, (cfn x) ^ d) + (∑ x ∈ range c ×ˢ Ico 1 p, (cfn x) ^ d) := by
      simp [t, dfn, sum_disjSum]
    rw [ht_sum, hsum_prod (b + c), hsum_prod b, hsum_prod c]
    unfold deltaD; ring
  have hQ_sub : pDiv p V (Q (b + c) - Q b * Q c) := by
    have h1 := prod_sub_prod_pDiv (V := V) hp s t cfn dfn hcfn_pDiv2 hdfn_pDiv2 (fun d hd => by
      rw [hΔ_eq d]; exact deltaD_div_pDiv p b c d hp hp5 hb hc hd)
    have hQeq : ∀ n : ℕ, ∏ x ∈ range n ×ˢ Ico 1 p, (1 + cfn x) = Q n := by
      intro n; exact prod_product (range n) (Ico 1 p) (fun x => 1 + cfn x)
    have ht_prod : ∏ y ∈ t, (1 + dfn y) = Q b * Q c := by
      simp only [t, dfn, prod_disjSum, Sum.elim_inl, Sum.elim_inr, hQeq]
    rw [hQeq (b + c), ht_prod] at h1
    exact h1
  -- Now Q(b+c) - Q(b)*Q(c) = P(b+c)^2 - (P(b)*P(c))^2 = (P(b)*P(c))^2 * (r + 1) * (r - 1)
  have hPb_ne : P b ≠ 0 := by
    apply prod_ne_zero_iff.mpr; intro m _
    apply prod_ne_zero_iff.mpr; intro u hu
    have hu1 := (mem_Ico.mp hu).1
    exact div_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))
  have hPc_ne : P c ≠ 0 := by
    apply prod_ne_zero_iff.mpr; intro m _
    apply prod_ne_zero_iff.mpr; intro u hu
    have hu1 := (mem_Ico.mp hu).1
    exact div_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))
  have hfac_eq : Q (b + c) - Q b * Q c = (P b * P c) * (P (b + c) + P b * P c) * (r - 1) := by
    rw [← hPQ (b + c), ← hPQ b, ← hPQ c, hr]
    field_simp [hPb_ne, hPc_ne]
    ring
  -- Factor 1: u₁ = P b * P c has pDiv p 1 (u₁ - 1)
  have hu1 : pDiv p 1 (P b * P c - 1) := by
    have hrew : P b * P c - 1 = P b * (P c - 1) + (P b - 1) := by ring
    rw [hrew]
    exact pDiv_add hp (by simpa using pDiv_mul hp (hP_pDiv0 b) (hP_mod1 c)) (hP_mod1 b)
  -- Factor 2: u₂ = (P (b + c) + P b * P c) / 2 has pDiv p 1 (u₂ - 1)
  have hu2 : pDiv p 1 ((P (b + c) + P b * P c) / 2 - 1) := by
    have hrew : (P (b + c) + P b * P c) / 2 - 1 = ((P (b + c) - 1) + (P b * P c - 1)) / (2 : ℕ) := by
      push_cast; ring
    rw [hrew]
    have hndvd2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
    exact pDiv_div_nat_unit hp hndvd2 (pDiv_add hp (hP_mod1 (b + c)) hu1)
  -- r - 1 has pDiv p 0 (in fact pDiv p 1!)
  have hr_pDiv0 : pDiv p 0 (r - 1) := by
    have hrm : (P b * P c) * (r - 1) = P (b + c) - P b * P c := by
      rw [hr]; field_simp [hPb_ne, hPc_ne]
    have hrhs : pDiv p 0 (P (b + c) - P b * P c) :=
      pDiv_sub hp (hP_pDiv0 (b + c)) (by simpa using pDiv_mul hp (hP_pDiv0 b) (hP_pDiv0 c))
    -- Actually prove pDiv p 0 directly from r - 1 = (P(b+c) - P(b)P(c)) / (P(b)P(c))!
    -- Wait: pDiv_cancel_unit needs hq : pDiv p 0 q! Let's show pDiv p 0 (r - 1) directly via denom!
    rcases hu1 with ⟨a₁, b₁, hb₁, h1⟩
    rcases hrhs with ⟨a₂, b₂, hb₂, h2⟩
    have hbc_eq : P b * P c = (((b₁ : ℤ) + (p : ℤ) * a₁ : ℤ) : ℚ) / (b₁ : ℚ) := by
      have hb₁0 : (b₁ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h0 => hb₁ (h0 ▸ dvd_zero p))
      have : P b * P c = 1 + ((p : ℚ) ^ 1 * (a₁ : ℚ)) / (b₁ : ℚ) := by linarith
      rw [this]; push_cast; field_simp [hb₁0]
    set num : ℤ := (b₁ : ℤ) + (p : ℤ) * a₁
    have hnum_ndvd : ¬ (p : ℤ) ∣ num := by
      intro hdiv
      have : (p : ℤ) ∣ (b₁ : ℤ) := by
        have heq : (b₁ : ℤ) = num - (p : ℤ) * a₁ := by omega
        rw [heq]; exact dvd_sub hdiv (dvd_mul_right _ _)
      exact hb₁ (Int.ofNat_dvd.mp this)
    have hnum_ne : num ≠ 0 := fun h0 => hnum_ndvd (h0 ▸ dvd_zero _)
    have hnat_ndvd : ¬ p ∣ num.natAbs := fun h => hnum_ndvd (Int.ofNat_dvd_left.mpr h)
    have hb₁0 : (b₁ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h0 => hb₁ (h0 ▸ dvd_zero p))
    have hb₂0 : (b₂ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h0 => hb₂ (h0 ▸ dvd_zero p))
    have hnum0 : (num : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hnum_ne
    have hreq : r - 1 = ((a₂ * (b₁ : ℤ) : ℤ) : ℚ) / ((b₂ : ℚ) * (num : ℚ)) := by
      rw [h2, hbc_eq] at hrm
      simp only [pow_zero, one_mul] at hrm
      push_cast
      field_simp [hb₁0, hb₂0, hnum0] at hrm ⊢
      linarith
    rcases Int.natAbs_eq num with hpos | hneg
    · refine ⟨a₂ * (b₁ : ℤ), b₂ * num.natAbs, hp.not_dvd_mul hb₂ hnat_ndvd, ?_⟩
      rw [hreq]
      have hnc : (num : ℚ) = (num.natAbs : ℚ) := by
        simpa using congrArg (Int.cast (R := ℚ)) hpos
      rw [hnc]; push_cast; ring
    · refine ⟨-(a₂ * (b₁ : ℤ)), b₂ * num.natAbs, hp.not_dvd_mul hb₂ hnat_ndvd, ?_⟩
      rw [hreq]
      have hnc : (num : ℚ) = -(num.natAbs : ℚ) := by
        simpa using congrArg (Int.cast (R := ℚ)) hneg
      rw [hnc]; push_cast; ring
  -- Now cancel 2, then u₁, then u₂!
  have hQ_div2 : pDiv p V ((P b * P c) * ((P (b + c) + P b * P c) / 2) * (r - 1)) := by
    have hndvd2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
    have h2 := pDiv_div_nat_unit hp hndvd2 hQ_sub
    rw [hfac_eq] at h2
    have hrew : (P b * P c) * (P (b + c) + P b * P c) * (r - 1) / (2 : ℕ) =
        (P b * P c) * ((P (b + c) + P b * P c) / 2) * (r - 1) := by push_cast; ring
    rwa [hrew] at h2
  have hstep1 : pDiv p V (((P (b + c) + P b * P c) / 2) * (r - 1)) := by
    have hq0 : pDiv p 0 (((P (b + c) + P b * P c) / 2) * (r - 1)) := by
      have hu2_0 : pDiv p 0 ((P (b + c) + P b * P c) / 2) := by
        have : (P (b + c) + P b * P c) / 2 = ((P (b + c) + P b * P c) / 2 - 1) + 1 := by ring
        rw [this]; exact pDiv_add hp (pDiv_mono (by omega) hu2) (pDiv_nat_zero hp 1)
      simpa using pDiv_mul hp hu2_0 hr_pDiv0
    rw [mul_assoc] at hQ_div2
    exact pDiv_cancel_unit hp hu1 hq0 hQ_div2
  exact pDiv_cancel_unit hp hu2 hr_pDiv0 hstep1

-- Integer corollary: p ^ (3 + v_p(a) + v_p(b) + v_p(a-b) + v_p(C(a,b))) ∣ (C(ap, bp) - C(a, b))
theorem kazandzidis_dvd (p a b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hb : 0 < b) (hba : b < a) :
    (p : ℤ) ^ (3 + padicValNat p a + padicValNat p b + padicValNat p (a - b) +
        padicValNat p (a.choose b)) ∣
      (((a * p).choose (b * p) : ℤ) - (a.choose b : ℤ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set c := a - b
  have hc : 0 < c := by omega
  have hbc : b + c = a := by omega
  have hratio := kazandzidis_ratio_pDiv p b c hp hp5 hb hc
  rw [hbc] at hratio
  have hch_ne : (a.choose b : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  have hch_pDiv : pDiv p (padicValNat p (a.choose b)) (a.choose b : ℚ) :=
    pDiv_of_dvd_nat hp pow_padicValNat_dvd
  have hmul := pDiv_mul hp hratio hch_pDiv
  have hrew : ((((a * p).choose (b * p) : ℚ) / (a.choose b : ℚ) - 1) * (a.choose b : ℚ)) =
      ((((a * p).choose (b * p) : ℤ) - (a.choose b : ℤ) : ℤ) : ℚ) := by
    push_cast; field_simp [hch_ne]
  rw [hrew] at hmul
  exact int_dvd_of_pDiv hp hmul

end OMA_A364114_Part2

namespace OMA_A364114_Part3

open Finset

-- Local copy of pDiv for standalone compilation (shared in final assembled file)
def pDiv (p k : ℕ) (q : ℚ) : Prop :=
  ∃ (a : ℤ) (b : ℕ), ¬ (p ∣ b) ∧ q = ((p : ℚ) ^ k * (a : ℚ)) / (b : ℚ)

lemma pDiv_zero (p k : ℕ) (hp : p.Prime) : pDiv p k 0 := ⟨0, 1, hp.not_dvd_one, by simp⟩

lemma pDiv_mono {p k₁ k₂ : ℕ} {q : ℚ} (h : k₁ ≤ k₂) (hq : pDiv p k₂ q) : pDiv p k₁ q := by
  rcases hq with ⟨a, b, hb, rfl⟩
  refine ⟨a * (p : ℤ) ^ (k₂ - k₁), b, hb, ?_⟩
  have hadd : k₁ + (k₂ - k₁) = k₂ := Nat.add_sub_of_le h
  push_cast; conv_lhs => rw [← hadd, pow_add]
  ring

lemma pDiv_add {p k : ℕ} {q₁ q₂ : ℚ} (hp : p.Prime) (h1 : pDiv p k q₁) (h2 : pDiv p k q₂) :
    pDiv p k (q₁ + q₂) := by
  rcases h1 with ⟨a₁, b₁, hb₁, rfl⟩
  rcases h2 with ⟨a₂, b₂, hb₂, rfl⟩
  have hb₁0 : (b₁ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h => hb₁ (h ▸ dvd_zero p))
  have hb₂0 : (b₂ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h => hb₂ (h ▸ dvd_zero p))
  refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, hp.not_dvd_mul hb₁ hb₂, ?_⟩
  push_cast; field_simp [hb₁0, hb₂0]

lemma pDiv_neg {p k : ℕ} {q : ℚ} (h : pDiv p k q) : pDiv p k (-q) := by
  rcases h with ⟨a, b, hb, rfl⟩
  exact ⟨-a, b, hb, by push_cast; ring⟩

lemma pDiv_sub {p k : ℕ} {q₁ q₂ : ℚ} (hp : p.Prime) (h1 : pDiv p k q₁) (h2 : pDiv p k q₂) :
    pDiv p k (q₁ - q₂) := by
  rw [sub_eq_add_neg]; exact pDiv_add hp h1 (pDiv_neg h2)

lemma pDiv_mul {p k₁ k₂ : ℕ} {q₁ q₂ : ℚ} (hp : p.Prime)
    (h1 : pDiv p k₁ q₁) (h2 : pDiv p k₂ q₂) : pDiv p (k₁ + k₂) (q₁ * q₂) := by
  rcases h1 with ⟨a₁, b₁, hb₁, rfl⟩
  rcases h2 with ⟨a₂, b₂, hb₂, rfl⟩
  refine ⟨a₁ * a₂, b₁ * b₂, hp.not_dvd_mul hb₁ hb₂, ?_⟩
  push_cast; rw [pow_add]; ring

lemma pDiv_sum {ι : Type*} {p k : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, pDiv p k (f i)) : pDiv p k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [pDiv_zero p k hp]
  | @insert x s hx ih =>
    rw [sum_insert hx]
    exact pDiv_add hp (hf x (mem_insert_self x s))
      (ih (fun y hy => hf y (mem_insert_of_mem hy)))

lemma pDiv_int {p k : ℕ} {z : ℤ} (hp : p.Prime) (h : (p : ℤ) ^ k ∣ z) : pDiv p k (z : ℚ) := by
  rcases h with ⟨c, rfl⟩
  exact ⟨c, 1, hp.not_dvd_one, by push_cast; ring⟩

lemma pDiv_int_zero {p : ℕ} (hp : p.Prime) (z : ℤ) : pDiv p 0 (z : ℚ) :=
  ⟨z, 1, hp.not_dvd_one, by simp⟩

lemma pDiv_nat_zero {p : ℕ} (hp : p.Prime) (n : ℕ) : pDiv p 0 (n : ℚ) :=
  ⟨n, 1, hp.not_dvd_one, by simp⟩

lemma int_dvd_of_pDiv {p k : ℕ} {z : ℤ} (hp : p.Prime) (h : pDiv p k (z : ℚ)) :
    (p : ℤ) ^ k ∣ z := by
  rcases h with ⟨a, b, hb, heq⟩
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h0 => hb (h0 ▸ dvd_zero p))
  have h1 : (z : ℚ) * (b : ℚ) = (p : ℚ) ^ k * (a : ℚ) := by rw [heq]; field_simp [hb0]
  have h2 : z * (b : ℤ) = (p : ℤ) ^ k * a := by exact_mod_cast h1
  have hcop : IsCoprime ((p : ℤ) ^ k) (b : ℤ) :=
    IsCoprime.pow_left ((Nat.Prime.coprime_iff_not_dvd hp).mpr hb).isCoprime
  exact hcop.dvd_of_dvd_mul_right ⟨a, h2⟩

-- Helper: product of factors ≡ 1 (mod p^k) is ≡ 1 (mod p^k)
lemma pDiv_prod_sub_one {ι : Type*} {p k : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, pDiv p k (f i - 1)) : pDiv p k ((∏ i ∈ s, f i) - 1) := by
  classical
  induction s using Finset.induction with
  | empty => simp [pDiv_zero p k hp]
  | @insert x s hx ih =>
    rw [prod_insert hx]
    have hfx := hf x (mem_insert_self x s)
    have hfs := ih (fun y hy => hf y (mem_insert_of_mem hy))
    have hfx0 : pDiv p 0 (f x) := by
      have : f x = (f x - 1) + 1 := by ring
      rw [this]; exact pDiv_add hp (pDiv_mono (Nat.zero_le _) hfx) (pDiv_nat_zero hp 1)
    have hrew : f x * (∏ i ∈ s, f i) - 1 = f x * ((∏ i ∈ s, f i) - 1) + (f x - 1) := by ring
    rw [hrew]
    exact pDiv_add hp (by simpa using pDiv_mul hp hfx0 hfs) hfx

-- ============================================================================
-- Section 1: Unit inverse-square sum mod p^d (for p ≥ 5, d ≥ 1)
-- ============================================================================

lemma zmod_units_inv_sq_sum_zero (p d : ℕ) [NeZero (p ^ d)] (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∑ u : (ZMod (p ^ d))ˣ, (((u⁻¹ : (ZMod (p ^ d))ˣ) : ZMod (p ^ d))) ^ 2 = 0 := by
  have hcop2 : Nat.Coprime 2 (p ^ d) := by
    apply Nat.Coprime.pow_right
    exact (hp.coprime_iff_not_dvd.mpr (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)).symm
  have hcop3 : Nat.Coprime 3 (p ^ d) := by
    apply Nat.Coprime.pow_right
    exact (hp.coprime_iff_not_dvd.mpr (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)).symm
  let u2 : (ZMod (p ^ d))ˣ := ZMod.unitOfCoprime 2 hcop2
  let u3 : (ZMod (p ^ d))ˣ := ZMod.unitOfCoprime 3 hcop3
  have hu2_val : (u2 : ZMod (p ^ d)) = 2 := by simp [u2]
  have hu3_val : (u3 : ZMod (p ^ d)) = 3 := by simp [u3]
  set S : ZMod (p ^ d) := ∑ u : (ZMod (p ^ d))ˣ, (((u⁻¹ : (ZMod (p ^ d))ˣ) : ZMod (p ^ d))) ^ 2
  have hbij : ∑ u : (ZMod (p ^ d))ˣ, ((((u2 * u)⁻¹ : (ZMod (p ^ d))ˣ) : ZMod (p ^ d))) ^ 2 = S :=
    Fintype.sum_equiv (Equiv.mulLeft u2) _ _ (fun _ => rfl)
  have h4S : (4 : ZMod (p ^ d)) * S = S := by
    have hstep : ((u2 : ZMod (p ^ d)) ^ 2) *
        ∑ u : (ZMod (p ^ d))ˣ, ((((u2 * u)⁻¹ : (ZMod (p ^ d))ˣ) : ZMod (p ^ d))) ^ 2 = S := by
      rw [mul_sum]
      apply sum_congr rfl; intro u _
      rw [mul_inv_rev, Units.val_mul, mul_pow]
      have hcancel : (u2 : ZMod (p ^ d)) ^ 2 * ((u2⁻¹ : (ZMod (p ^ d))ˣ) : ZMod (p ^ d)) ^ 2 = 1 := by
        rw [← mul_pow, Units.mul_inv, one_pow]
      calc (u2 : ZMod (p ^ d)) ^ 2 * (((u⁻¹ : (ZMod (p ^ d))ˣ) : ZMod (p ^ d)) ^ 2 *
              ((u2⁻¹ : (ZMod (p ^ d))ˣ) : ZMod (p ^ d)) ^ 2)
          = ((u2 : ZMod (p ^ d)) ^ 2 * ((u2⁻¹ : (ZMod (p ^ d))ˣ) : ZMod (p ^ d)) ^ 2) *
              ((u⁻¹ : (ZMod (p ^ d))ˣ) : ZMod (p ^ d)) ^ 2 := by ring
        _ = ((u⁻¹ : (ZMod (p ^ d))ˣ) : ZMod (p ^ d)) ^ 2 := by rw [hcancel, one_mul]
    rw [hbij, hu2_val] at hstep
    simpa [show (2 : ZMod (p ^ d)) ^ 2 = 4 by norm_num] using hstep
  have h3S : (u3 : ZMod (p ^ d)) * S = 0 := by
    rw [hu3_val]
    have : (3 : ZMod (p ^ d)) = 4 - 1 := by norm_num
    rw [this, sub_mul, one_mul, h4S, sub_self]
  calc S = ((u3⁻¹ : (ZMod (p ^ d))ˣ) : ZMod (p ^ d)) * ((u3 : ZMod (p ^ d)) * S) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = 0 := by rw [h3S, mul_zero]

lemma unit_inv_sq_sum_pDiv (p d m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hd : 1 ≤ d) :
    pDiv p d (∑ j ∈ (range (p ^ d)).filter (fun j => ¬ p ∣ j),
      (1 : ℚ) / (((m * p ^ d + j : ℕ) : ℚ) ^ 2)) := by
  set Sfin := (range (p ^ d)).filter (fun j => ¬ p ∣ j)
  set F : ℕ := ∏ j ∈ Sfin, (m * p ^ d + j)
  have hF_ndvd : ¬ p ∣ F := by
    intro hdvd
    rw [hp.prime.dvd_finsetProd_iff] at hdvd
    rcases hdvd with ⟨j, hj, hdiv⟩
    have hj_ndvd : ¬ p ∣ j := (mem_filter.mp hj).2
    have hmp : p ∣ m * p ^ d := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) m
    have hj_dvd : p ∣ j := (Nat.dvd_add_right hmp).mp hdiv
    exact hj_ndvd hj_dvd
  have hF0 : (F : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h => hF_ndvd (h ▸ dvd_zero p))
  have hj_dvd_F : ∀ j ∈ Sfin, (m * p ^ d + j) ∣ F := fun j hj => dvd_prod_of_mem _ hj
  set A : ℕ := ∑ j ∈ Sfin, (F / (m * p ^ d + j)) ^ 2
  have hsum_eq : (∑ j ∈ Sfin, (1 : ℚ) / (((m * p ^ d + j : ℕ) : ℚ) ^ 2)) =
      (A : ℚ) / ((F * F : ℕ) : ℚ) := by
    rw [Nat.cast_sum, sum_div]
    apply sum_congr rfl; intro j hj
    have hj_ndvd : ¬ p ∣ j := (mem_filter.mp hj).2
    have hj_pos : 0 < j := Nat.pos_of_ne_zero (fun h0 => hj_ndvd (h0 ▸ dvd_zero p))
    have hmj0 : ((m * p ^ d + j : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hq : ((F / (m * p ^ d + j) : ℕ) : ℚ) = (F : ℚ) / ((m * p ^ d + j : ℕ) : ℚ) := by
      have hm : ((F / (m * p ^ d + j) : ℕ) : ℚ) * ((m * p ^ d + j : ℕ) : ℚ) = (F : ℚ) := by
        have := congrArg (Nat.cast (R := ℚ)) (Nat.div_mul_cancel (hj_dvd_F j hj))
        simpa using this
      field_simp [hmj0]; linarith
    rw [Nat.cast_pow, hq, Nat.cast_mul]; field_simp [hF0, hmj0]
  have hA_dvd : p ^ d ∣ A := by
    rw [← ZMod.natCast_eq_zero_iff]
    have : NeZero (p ^ d) := ⟨pow_ne_zero d hp.ne_zero⟩
    have hA_cast : (A : ZMod (p ^ d)) =
        (F : ZMod (p ^ d)) ^ 2 *
          ∑ u : (ZMod (p ^ d))ˣ, (((u⁻¹ : (ZMod (p ^ d))ˣ) : ZMod (p ^ d))) ^ 2 := by
      rw [mul_sum]
      dsimp only [A]
      push_cast
      refine Finset.sum_bij
        (fun j hj => ZMod.unitOfCoprime j
          (Nat.Coprime.pow_right d ((hp.coprime_iff_not_dvd.mpr (mem_filter.mp hj).2).symm)))
        ?_ ?_ ?_ ?_
      · intro _ _; exact mem_univ _
      · intro j₁ hj₁ j₂ hj₂ heq
        have hval := congrArg (fun u : (ZMod (p ^ d))ˣ => (u : ZMod (p ^ d)).val) heq
        simp only [ZMod.coe_unitOfCoprime] at hval
        have h1 : j₁ < p ^ d := mem_range.mp (mem_filter.mp hj₁).1
        have h2 : j₂ < p ^ d := mem_range.mp (mem_filter.mp hj₂).1
        rw [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at hval
        exact hval
      · intro u _
        have hcop : Nat.Coprime (u : ZMod (p ^ d)).val (p ^ d) := by
          have h1 : IsUnit ((u : ZMod (p ^ d)).val : ZMod (p ^ d)) := by
            rw [ZMod.natCast_zmod_val]; exact u.isUnit
          exact (ZMod.isUnit_iff_coprime _ _).mp h1
        have hndvd : ¬ p ∣ (u : ZMod (p ^ d)).val := by
          intro hdiv
          have hd1 : p ∣ Nat.gcd (u : ZMod (p ^ d)).val (p ^ d) :=
            Nat.dvd_gcd hdiv (dvd_pow_self p (by omega))
          rw [hcop.gcd_eq_one] at hd1
          exact hp.not_dvd_one hd1
        refine ⟨(u : ZMod (p ^ d)).val, mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _), hndvd⟩, ?_⟩
        ext
        simp only [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]
      · intro j hj
        set u : (ZMod (p ^ d))ˣ := ZMod.unitOfCoprime j
          (Nat.Coprime.pow_right d ((hp.coprime_iff_not_dvd.mpr (mem_filter.mp hj).2).symm))
        have hu_val : (u : ZMod (p ^ d)) = (j : ZMod (p ^ d)) := by simp [u]
        have hmj_cast : ((m * p ^ d + j : ℕ) : ZMod (p ^ d)) = (u : ZMod (p ^ d)) := by
          have hp0 : ((p ^ d : ℕ) : ZMod (p ^ d)) = 0 := ZMod.natCast_self (p ^ d)
          rw [hu_val, Nat.cast_add, Nat.cast_mul, hp0, mul_zero, zero_add]
        have hmulZ : ((F / (m * p ^ d + j) : ℕ) : ZMod (p ^ d)) * (u : ZMod (p ^ d)) =
            (F : ZMod (p ^ d)) := by
          rw [← hmj_cast]
          have := congrArg (Nat.cast (R := ZMod (p ^ d))) (Nat.div_mul_cancel (hj_dvd_F j hj))
          simpa using this
        have hqZ : ((F / (m * p ^ d + j) : ℕ) : ZMod (p ^ d)) =
            (F : ZMod (p ^ d)) * ((u⁻¹ : (ZMod (p ^ d))ˣ) : ZMod (p ^ d)) := by
          calc ((F / (m * p ^ d + j) : ℕ) : ZMod (p ^ d))
              = ((F / (m * p ^ d + j) : ℕ) : ZMod (p ^ d)) * (u : ZMod (p ^ d)) *
                  ((u⁻¹ : (ZMod (p ^ d))ˣ) : ZMod (p ^ d)) := by
                    rw [mul_assoc, Units.mul_inv, mul_one]
            _ = (F : ZMod (p ^ d)) * ((u⁻¹ : (ZMod (p ^ d))ˣ) : ZMod (p ^ d)) := by rw [hmulZ]
        rw [hqZ, mul_pow]
    rw [hA_cast, zmod_units_inv_sq_sum_zero p d hp hp5, mul_zero]
  rw [hsum_eq]
  rcases hA_dvd with ⟨c, hc⟩
  refine ⟨c, F * F, hp.not_dvd_mul hF_ndvd hF_ndvd, ?_⟩
  rw [hc]; push_cast; ring

-- ============================================================================
-- Section 2: Binomial block-constancy lemmas for w1 and w2
-- ============================================================================

-- Exact stepping identity: C(N, k + L) * ∏_{j=1}^L (k + j) = C(N, k) * ∏_{j=1}^L (N - k - j + 1)
lemma choose_shift_identity (N k L : ℕ) (h : k + L ≤ N) :
    N.choose (k + L) * ∏ j ∈ Icc 1 L, (k + j) =
      N.choose k * ∏ j ∈ Icc 1 L, (N + 1 - k - j) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hIcc : Icc 1 (L + 1) = insert (L + 1) (Icc 1 L) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    rw [hIcc, prod_insert (by simp), prod_insert (by simp)]
    have hstep := Nat.add_one_mul_choose_eq N (k + L)
    -- (k + L + 1) * C(N, k + L + 1) = (N - (k + L)) * C(N, k + L)
    have h1 : N.choose (k + (L + 1)) * (k + (L + 1)) = (N - (k + L)) * N.choose (k + L) := by
      have hsucc : k + (L + 1) = (k + L) + 1 := by omega
      rw [hsucc, mul_comm]
      have h2 := Nat.choose_succ_right_eq N (k + L)
      -- C(N, k+L+1) * (k+L+1) = C(N, k+L) * (N - (k+L))
      linarith
    have hsub : N + 1 - k - (L + 1) = N - (k + L) := by omega
    rw [hsub]
    calc N.choose (k + (L + 1)) * ((k + (L + 1)) * ∏ j ∈ Icc 1 L, (k + j))
        = (N.choose (k + (L + 1)) * (k + (L + 1))) * ∏ j ∈ Icc 1 L, (k + j) := by ring
      _ = (N - (k + L)) * (N.choose (k + L) * ∏ j ∈ Icc 1 L, (k + j)) := by rw [h1]; ring
      _ = (N - (k + L)) * (N.choose k * ∏ j ∈ Icc 1 L, (N + 1 - k - j)) := by
            rw [ih (by omega)]
      _ = N.choose k * ((N - (k + L)) * ∏ j ∈ Icc 1 L, (N + 1 - k - j)) := by ring

-- Helper: for p^s ∣ M, p^(d+1) ∣ K, d < s, 1 ≤ j < p^(d+1):
--   pDiv p (s - d) ((M - K - j) / (K + j) + 1)  (when K + j ≤ M)
lemma ratio_neg_one_pDiv (p s d M K j : ℕ) (hp : p.Prime)
    (hds : d < s) (hM : p ^ s ∣ M) (hK : p ^ (d + 1) ∣ K)
    (hj1 : 1 ≤ j) (hj2 : j < p ^ (d + 1)) (hle : K + j ≤ M) :
    pDiv p (s - d) ((((M - K - j : ℕ) : ℚ) / ((K + j : ℕ) : ℚ)) + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  set t := padicValNat p j
  have ht_le : t ≤ d := by
    by_contra h
    have hd1 : d + 1 ≤ t := by omega
    have hpow : p ^ (d + 1) ≤ j :=
      le_trans (Nat.pow_le_pow_right hp.pos hd1) (Nat.le_of_dvd (by omega) pow_padicValNat_dvd)
    omega
  rcases pow_padicValNat_dvd (p := p) (n := j) with ⟨u, hu⟩
  have hu_ndvd : ¬ p ∣ u := by
    intro hpu
    have h1 : p ^ (t + 1) ∣ j := by rw [hu, pow_succ]; exact mul_dvd_mul_left _ hpu
    have h2 := (padicValNat_dvd_iff_le (by omega : j ≠ 0)).mp h1
    omega
  rcases hK with ⟨k', hk'⟩
  rcases hM with ⟨m', hm'⟩
  -- K + j = p^t * (p^(d+1-t) * k' + u), and p ∤ (p^(d+1-t) * k' + u) since d+1-t ≥ 1!
  set den := p ^ (d + 1 - t) * k' + u
  have hden_ndvd : ¬ p ∣ den := by
    intro hdiv
    have h1 : p ∣ p ^ (d + 1 - t) * k' := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) k'
    exact hu_ndvd ((Nat.dvd_add_right h1).mp hdiv)
  have hKj_eq : K + j = p ^ t * den := by
    rw [hk', hu]; dsimp only [den]
    have hexp : t + (d + 1 - t) = d + 1 := by omega
    calc p ^ (d + 1) * k' + p ^ t * u
        = p ^ t * p ^ (d + 1 - t) * k' + p ^ t * u := by rw [← pow_add, hexp]
      _ = p ^ t * (p ^ (d + 1 - t) * k' + u) := by ring
  have hpt0 : (p : ℚ) ^ t ≠ 0 := pow_ne_zero t (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hden0 : (den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h0 => hden_ndvd (h0 ▸ dvd_zero p))
  have hKj0 : ((K + j : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnum_eq : ((M - K - j : ℕ) : ℚ) / ((K + j : ℕ) : ℚ) + 1 = (M : ℚ) / ((K + j : ℕ) : ℚ) := by
    have hsub : ((M - K - j : ℕ) : ℚ) = (M : ℚ) - ((K + j : ℕ) : ℚ) := by
      have : M - K - j = M - (K + j) := by omega
      rw [this, Nat.cast_sub hle]
    rw [hsub]; field_simp [hKj0]; ring
  rw [hnum_eq, hKj_eq, hm']
  refine ⟨(p : ℤ) ^ (d - t) * (m' : ℤ), den, hden_ndvd, ?_⟩
  have hexp : s = t + (s - d) + (d - t) := by omega
  push_cast
  conv_lhs => rw [hexp, pow_add, pow_add]
  field_simp [hpt0, hden0]

-- Helper 2: for p^s ∣ C, p^(d+1) ∣ (B - K), d < s, 1 ≤ j < p^(d+1):
--   pDiv p (s - d) ((B - K - j) / (C + B - K - j) - 1)
lemma ratio_pos_one_pDiv (p s d C BK j : ℕ) (hp : p.Prime)
    (hds : d < s) (hC : p ^ s ∣ C) (hBK : p ^ (d + 1) ∣ BK)
    (hj1 : 1 ≤ j) (hj2 : j < p ^ (d + 1)) (hle : j ≤ BK) :
    pDiv p (s - d) ((((BK - j : ℕ) : ℚ) / ((C + BK - j : ℕ) : ℚ)) - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  set t := padicValNat p j
  have ht_le : t ≤ d := by
    by_contra h
    have hd1 : d + 1 ≤ t := by omega
    have hpow : p ^ (d + 1) ≤ j :=
      le_trans (Nat.pow_le_pow_right hp.pos hd1) (Nat.le_of_dvd (by omega) pow_padicValNat_dvd)
    omega
  rcases pow_padicValNat_dvd (p := p) (n := j) with ⟨u, hu⟩
  have hu_ndvd : ¬ p ∣ u := by
    intro hpu
    have h1 : p ^ (t + 1) ∣ j := by rw [hu, pow_succ]; exact mul_dvd_mul_left _ hpu
    have h2 := (padicValNat_dvd_iff_le (by omega : j ≠ 0)).mp h1
    omega
  rcases hC with ⟨c', hc'⟩
  rcases hBK with ⟨b', hb'⟩
  have hden_eq : C + BK - j = p ^ t * (p ^ (s - t) * c' + p ^ (d + 1 - t) * b' - u) := by
    have hCBK : C + BK = p ^ t * (p ^ (s - t) * c' + p ^ (d + 1 - t) * b') := by
      rw [hc', hb']
      have e1 : t + (s - t) = s := by omega
      have e2 : t + (d + 1 - t) = d + 1 := by omega
      calc p ^ s * c' + p ^ (d + 1) * b'
          = p ^ t * p ^ (s - t) * c' + p ^ t * p ^ (d + 1 - t) * b' := by
              rw [← pow_add, e1, ← pow_add, e2]
        _ = p ^ t * (p ^ (s - t) * c' + p ^ (d + 1 - t) * b') := by ring
    rw [hCBK, hu, ← Nat.mul_sub_left_distrib]
  set den := p ^ (s - t) * c' + p ^ (d + 1 - t) * b' - u
  have hge_u : u ≤ p ^ (s - t) * c' + p ^ (d + 1 - t) * b' := by
    have h1 : p ^ t * u ≤ p ^ t * (p ^ (s - t) * c' + p ^ (d + 1 - t) * b') := by
      have : p ^ t * (p ^ (s - t) * c' + p ^ (d + 1 - t) * b') = C + BK := by
        rw [hc', hb']
        have e1 : t + (s - t) = s := by omega
        have e2 : t + (d + 1 - t) = d + 1 := by omega
        calc p ^ t * (p ^ (s - t) * c' + p ^ (d + 1 - t) * b')
            = p ^ t * p ^ (s - t) * c' + p ^ t * p ^ (d + 1 - t) * b' := by ring
          _ = p ^ s * c' + p ^ (d + 1) * b' := by rw [← pow_add, e1, ← pow_add, e2]
      rw [this, ← hu]; omega
    exact Nat.le_of_mul_le_mul_left h1 (pow_pos hp.pos t)
  have hden_ndvd : ¬ p ∣ den := by
    intro hdiv
    have hsum_dvd : p ∣ (p ^ (s - t) * c' + p ^ (d + 1 - t) * b') :=
      dvd_add (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) c')
        (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) b')
    have hu_eq : u = (p ^ (s - t) * c' + p ^ (d + 1 - t) * b') - den := by omega
    rw [hu_eq] at hu_ndvd
    exact hu_ndvd (Nat.dvd_sub hsum_dvd hdiv)
  have hCBKj0 : ((C + BK - j : ℕ) : ℚ) ≠ 0 := by
    rw [hden_eq]
    exact Nat.cast_ne_zero.mpr (mul_ne_zero (pow_ne_zero t hp.ne_zero)
      (fun h0 => hden_ndvd (h0 ▸ dvd_zero p)))
  have hpt0 : (p : ℚ) ^ t ≠ 0 := pow_ne_zero t (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hden0 : (den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h0 => hden_ndvd (h0 ▸ dvd_zero p))
  have hdiff : ((BK - j : ℕ) : ℚ) / ((C + BK - j : ℕ) : ℚ) - 1 =
      -(C : ℚ) / ((C + BK - j : ℕ) : ℚ) := by
    have h1 : ((BK - j : ℕ) : ℚ) = (BK : ℚ) - (j : ℚ) := Nat.cast_sub hle
    have h2 : ((C + BK - j : ℕ) : ℚ) = (C : ℚ) + (BK : ℚ) - (j : ℚ) := by
      have : C + BK - j = C + (BK - j) := by omega
      rw [this, Nat.cast_add, h1]; ring
    rw [h1, h2]; field_simp [h2 ▸ hCBKj0]; ring
  rw [hdiff, hden_eq, hc']
  refine ⟨-((p : ℤ) ^ (d - t) * (c' : ℤ)), den, hden_ndvd, ?_⟩
  have hexp : s = t + (s - d) + (d - t) := by omega
  push_cast
  conv_lhs => rw [hexp, pow_add, pow_add]
  field_simp [hpt0, hden0]

-- Helper 3 (for a(N-1)): for p^s ∣ A, p^(d+1) ∣ K, d < s, 1 ≤ j < p^(d+1):
--   pDiv p (s - d) ((A + K + j) / (K + j) - 1)
lemma ratio_add_one_pDiv (p s d A K j : ℕ) (hp : p.Prime)
    (hds : d < s) (hA : p ^ s ∣ A) (hK : p ^ (d + 1) ∣ K)
    (hj1 : 1 ≤ j) (hj2 : j < p ^ (d + 1)) :
    pDiv p (s - d) ((((A + K + j : ℕ) : ℚ) / ((K + j : ℕ) : ℚ)) - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  set t := padicValNat p j
  have ht_le : t ≤ d := by
    by_contra h
    have hd1 : d + 1 ≤ t := by omega
    have hpow : p ^ (d + 1) ≤ j :=
      le_trans (Nat.pow_le_pow_right hp.pos hd1) (Nat.le_of_dvd (by omega) pow_padicValNat_dvd)
    omega
  rcases pow_padicValNat_dvd (p := p) (n := j) with ⟨u, hu⟩
  have hu_ndvd : ¬ p ∣ u := by
    intro hpu
    have h1 : p ^ (t + 1) ∣ j := by rw [hu, pow_succ]; exact mul_dvd_mul_left _ hpu
    have h2 := (padicValNat_dvd_iff_le (by omega : j ≠ 0)).mp h1
    omega
  rcases hK with ⟨k', hk'⟩
  rcases hA with ⟨a', ha'⟩
  set den := p ^ (d + 1 - t) * k' + u
  have hden_ndvd : ¬ p ∣ den := by
    intro hdiv
    have h1 : p ∣ p ^ (d + 1 - t) * k' := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) k'
    exact hu_ndvd ((Nat.dvd_add_right h1).mp hdiv)
  have hKj_eq : K + j = p ^ t * den := by
    rw [hk', hu]; dsimp only [den]
    have hexp : t + (d + 1 - t) = d + 1 := by omega
    calc p ^ (d + 1) * k' + p ^ t * u
        = p ^ t * p ^ (d + 1 - t) * k' + p ^ t * u := by rw [← pow_add, hexp]
      _ = p ^ t * (p ^ (d + 1 - t) * k' + u) := by ring
  have hpt0 : (p : ℚ) ^ t ≠ 0 := pow_ne_zero t (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hden0 : (den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h0 => hden_ndvd (h0 ▸ dvd_zero p))
  have hKj0 : ((K + j : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdiff : ((A + K + j : ℕ) : ℚ) / ((K + j : ℕ) : ℚ) - 1 = (A : ℚ) / ((K + j : ℕ) : ℚ) := by
    push_cast; field_simp [hKj0]; ring
  rw [hdiff, hKj_eq, ha']
  refine ⟨(p : ℤ) ^ (d - t) * (a' : ℤ), den, hden_ndvd, ?_⟩
  have hexp : s = t + (s - d) + (d - t) := by omega
  push_cast
  conv_lhs => rw [hexp, pow_add, pow_add]
  field_simp [hpt0, hden0]

-- Helper 4 (for a(N-1)): for p^s ∣ C, p^s ∣ B, p^(d+1) ∣ K, d < s, 1 ≤ j < p^(d+1), j ≤ B - K, B ≤ C:
--   pDiv p (s - d) (((B - K - j) / (C - B + K + j)) + 1)
lemma ratio_sub_neg_one_pDiv (p s d C B K j : ℕ) (hp : p.Prime)
    (hds : d < s) (hC : p ^ s ∣ C) (hB : p ^ s ∣ B) (hK : p ^ (d + 1) ∣ K)
    (hBC : B ≤ C) (hj1 : 1 ≤ j) (hj2 : j < p ^ (d + 1)) (hle : K + j ≤ B) :
    pDiv p (s - d) ((((B - K - j : ℕ) : ℚ) / ((C - B + K + j : ℕ) : ℚ)) + 1) := by
  have hCB : p ^ (d + 1) ∣ (C - B + K) := by
    have h1 : p ^ (d + 1) ∣ C := dvd_trans (pow_dvd_pow p (by omega)) hC
    have h2 : p ^ (d + 1) ∣ B := dvd_trans (pow_dvd_pow p (by omega)) hB
    exact dvd_add (Nat.dvd_sub h1 h2) hK
  have h := ratio_neg_one_pDiv p s d C (C - B + K) j hp hds hC hCB hj1 hj2 (by omega)
  have hsub : C - (C - B + K) - j = B - K - j := by omega
  have hadd : C - B + K + j = (C - B + K) + j := by omega
  rwa [hsub, hadd] at h

-- Now assemble w1 and w2 block-constancy!
def w1 (A B C k : ℕ) : ℤ :=
  ((C + B - 1 - k).choose C : ℤ) * ((A - 1).choose k : ℤ) ^ 2

def w2 (A B C k : ℕ) : ℤ :=
  (-1 : ℤ) ^ (B - 2 - k) * ((C - 1).choose (B - 2 - k) : ℤ) * ((A + k).choose k : ℤ) ^ 2

lemma w1_block_const (p s d A B C k₀ L : ℕ) (hp : p.Prime)
    (hds : d < s) (hA : p ^ s ∣ A) (hB : p ^ s ∣ B) (hC : p ^ s ∣ C)
    (hk₀ : p ^ (d + 1) ∣ k₀) (hL : L < p ^ (d + 1)) (hBA : B ≤ A) (hkL : k₀ + L < B) :
    pDiv p (s - d) ((w1 A B C (k₀ + L) : ℚ) - (w1 A B C k₀ : ℚ)) := by
  -- Step 1: ((A - 1).choose (k₀ + L)) ≡ (-1)^L * ((A - 1).choose k₀) (mod p^(s - d))
  have hfacA : pDiv p (s - d)
      ((((A - 1).choose (k₀ + L) : ℚ) ^ 2) - (((A - 1).choose k₀ : ℚ) ^ 2)) := by
    have hid := choose_shift_identity (A - 1) k₀ L (by omega)
    have hidQ : (((A - 1).choose (k₀ + L) : ℚ) * ∏ j ∈ Icc 1 L, ((k₀ + j : ℕ) : ℚ)) =
        (((A - 1).choose k₀ : ℚ) * ∏ j ∈ Icc 1 L, ((A - k₀ - j : ℕ) : ℚ)) := by
      have h1 : ∀ j ∈ Icc 1 L, A - 1 + 1 - k₀ - j = A - k₀ - j := fun j _ => by omega
      rw [prod_congr rfl h1] at hid
      exact_mod_cast hid
    have hden_ne : (∏ j ∈ Icc 1 L, ((k₀ + j : ℕ) : ℚ)) ≠ 0 := by
      apply prod_ne_zero_iff.mpr; intro j hj
      exact Nat.cast_ne_zero.mpr (by have := (mem_Icc.mp hj).1; omega)
    have hrat : ((A - 1).choose (k₀ + L) : ℚ) =
        (-1 : ℚ) ^ L * ((A - 1).choose k₀ : ℚ) *
          ∏ j ∈ Icc 1 L, (-(((A - k₀ - j : ℕ) : ℚ) / ((k₀ + j : ℕ) : ℚ))) := by
      rw [prod_neg, Nat.card_Icc, Nat.add_sub_cancel, prod_div_distrib]
      have hsq : (-1 : ℚ) ^ L * (-1 : ℚ) ^ L = 1 := by rw [← mul_pow]; norm_num
      field_simp [hden_ne] at hidQ ⊢
      calc ((A - 1).choose (k₀ + L) : ℚ) * ∏ j ∈ Icc 1 L, ((k₀ + j : ℕ) : ℚ)
          = ((A - 1).choose k₀ : ℚ) * ∏ j ∈ Icc 1 L, ((A - k₀ - j : ℕ) : ℚ) := hidQ
        _ = ((-1 : ℚ) ^ L * (-1 : ℚ) ^ L) * (((A - 1).choose k₀ : ℚ) *
              ∏ j ∈ Icc 1 L, ((A - k₀ - j : ℕ) : ℚ)) := by rw [hsq, one_mul]
        _ = _ := by ring
    set R := ∏ j ∈ Icc 1 L, (-(((A - k₀ - j : ℕ) : ℚ) / ((k₀ + j : ℕ) : ℚ)))
    have hR1 : pDiv p (s - d) (R - 1) := by
      apply pDiv_prod_sub_one hp
      intro j hj
      have hj1 := (mem_Icc.mp hj).1
      have hj2 := (mem_Icc.mp hj).2
      have h1 := ratio_neg_one_pDiv p s d A k₀ j hp hds hA hk₀ hj1 (by omega) (by omega)
      have hrew : -(((A - k₀ - j : ℕ) : ℚ) / ((k₀ + j : ℕ) : ℚ)) - 1 =
          -((((A - k₀ - j : ℕ) : ℚ) / ((k₀ + j : ℕ) : ℚ)) + 1) := by ring
      rw [hrew]
      exact pDiv_neg h1
    have hR0 : pDiv p 0 R := by
      have : R = (R - 1) + 1 := by ring
      rw [this]; exact pDiv_add hp (pDiv_mono (Nat.zero_le _) hR1) (pDiv_nat_zero hp 1)
    have hRsq : pDiv p (s - d) (R ^ 2 - 1) := by
      have : R ^ 2 - 1 = (R + 1) * (R - 1) := by ring
      rw [this]
      simpa using pDiv_mul hp (pDiv_add hp hR0 (pDiv_nat_zero hp 1)) hR1
    have hsq_eq : ((A - 1).choose (k₀ + L) : ℚ) ^ 2 - ((A - 1).choose k₀ : ℚ) ^ 2 =
        ((A - 1).choose k₀ : ℚ) ^ 2 * (R ^ 2 - 1) := by
      rw [hrat, mul_pow, mul_pow]
      have : ((-1 : ℚ) ^ L) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [this, one_mul]; ring
    rw [hsq_eq]
    have h := pDiv_mul hp (pDiv_nat_zero hp (((A - 1).choose k₀) ^ 2)) hRsq
    push_cast at h; simpa using h
  -- Step 2: C(C + B - 1 - (k₀ + L), C) ≡ C(C + B - 1 - k₀, C) (mod p^(s - d))
  have hfacC : pDiv p (s - d)
      (((C + B - 1 - (k₀ + L)).choose C : ℚ) - ((C + B - 1 - k₀).choose C : ℚ)) := by
    -- By symmetry: C(C + m, C) = C(C + m, m). Stepping m down by L from m₀ = B - 1 - k₀:
    -- C(C + m₀ - L, C) * ∏_{j=1}^L (C + m₀ + 1 - j) = C(C + m₀, C) * ∏_{j=1}^L (m₀ + 1 - j)
    have hstepC : ∀ l : ℕ, l ≤ B - 1 - k₀ →
        (C + B - 1 - (k₀ + l)).choose C * ∏ j ∈ Icc 1 l, (C + (B - k₀) - j) =
          (C + B - 1 - k₀).choose C * ∏ j ∈ Icc 1 l, ((B - k₀) - j) := by
      intro l
      induction l with
      | zero => intro _; simp
      | succ l ihl =>
        intro hl
        have hIcc : Icc 1 (l + 1) = insert (l + 1) (Icc 1 l) := by
          ext x; simp only [mem_Icc, mem_insert]; omega
        rw [hIcc, prod_insert (by simp), prod_insert (by simp)]
        have hch := Nat.choose_symm (show C ≤ C + B - 1 - (k₀ + l) by omega)
        -- Use (N + 1) * C(N, C) = (N + 1 - C) * C(N + 1, C)!
        -- Let N = C + B - 1 - (k₀ + l + 1). Then N + 1 = C + B - 1 - (k₀ + l) = C + (B - k₀) - (l + 1)!
        -- Wait: C(N + 1, C) * (N + 1 - C) = C(N, C) * (N + 1)!
        have hN : (C + B - 1 - (k₀ + (l + 1))).choose C * (C + (B - k₀) - (l + 1)) =
            (C + B - 1 - (k₀ + l)).choose C * ((B - k₀) - (l + 1)) := by
          set N := C + B - 1 - (k₀ + (l + 1))
          have hN1 : N + 1 = C + (B - k₀) - (l + 1) := by omega
          have hN1' : N + 1 = C + B - 1 - (k₀ + l) := by omega
          have hNC : N + 1 - C = (B - k₀) - (l + 1) := by omega
          rw [← hN1, ← hN1', ← hNC]
          -- Prove C(N, C) * (N + 1) = C(N + 1, C) * (N + 1 - C)!
          -- Since C(N, C) = C(N, N - C) and C(N + 1, C) = C(N + 1, N + 1 - C):
          have hsym1 := Nat.choose_symm (show C ≤ N by omega)
          have hsym2 := Nat.choose_symm (show C ≤ N + 1 by omega)
          have hrec := Nat.add_one_mul_choose_eq N (N - C)
          -- (N + 1) * C(N, N - C) = (N - C + 1) * C(N + 1, N - C + 1)
          have hsub : N - C + 1 = N + 1 - C := by omega
          rw [hsub, hsym1, hsym2] at hrec
          linarith
        calc (C + B - 1 - (k₀ + (l + 1))).choose C *
              ((C + (B - k₀) - (l + 1)) * ∏ j ∈ Icc 1 l, (C + (B - k₀) - j))
            = ((C + B - 1 - (k₀ + (l + 1))).choose C * (C + (B - k₀) - (l + 1))) *
                ∏ j ∈ Icc 1 l, (C + (B - k₀) - j) := by ring
          _ = ((B - k₀) - (l + 1)) * ((C + B - 1 - (k₀ + l)).choose C *
                ∏ j ∈ Icc 1 l, (C + (B - k₀) - j)) := by rw [hN]; ring
          _ = ((B - k₀) - (l + 1)) * ((C + B - 1 - k₀).choose C *
                ∏ j ∈ Icc 1 l, ((B - k₀) - j)) := by rw [ihl (by omega)]
          _ = _ := by ring
    have hid := hstepC L (by omega)
    have hidQ : (((C + B - 1 - (k₀ + L)).choose C : ℚ) *
          ∏ j ∈ Icc 1 L, ((C + (B - k₀) - j : ℕ) : ℚ)) =
        (((C + B - 1 - k₀).choose C : ℚ) * ∏ j ∈ Icc 1 L, (((B - k₀) - j : ℕ) : ℚ)) := by
      exact_mod_cast hid
    have hden_ne : (∏ j ∈ Icc 1 L, ((C + (B - k₀) - j : ℕ) : ℚ)) ≠ 0 := by
      apply prod_ne_zero_iff.mpr; intro j hj
      have hj2 := (mem_Icc.mp hj).2
      exact Nat.cast_ne_zero.mpr (by omega)
    set R := ∏ j ∈ Icc 1 L, ((((B - k₀) - j : ℕ) : ℚ) / ((C + (B - k₀) - j : ℕ) : ℚ))
    have hrat : ((C + B - 1 - (k₀ + L)).choose C : ℚ) = ((C + B - 1 - k₀).choose C : ℚ) * R := by
      dsimp only [R]; rw [prod_div_distrib]
      field_simp [hden_ne] at hidQ ⊢; linarith
    have hR1 : pDiv p (s - d) (R - 1) := by
      apply pDiv_prod_sub_one hp
      intro j hj
      have hj1 := (mem_Icc.mp hj).1
      have hj2 := (mem_Icc.mp hj).2
      have hBK : p ^ (d + 1) ∣ (B - k₀) :=
        Nat.dvd_sub (dvd_trans (pow_dvd_pow p (by omega)) hB) hk₀
      exact ratio_pos_one_pDiv p s d C (B - k₀) j hp hds hC hBK hj1 (by omega) (by omega)
    rw [hrat]
    have hrew : ((C + B - 1 - k₀).choose C : ℚ) * R - ((C + B - 1 - k₀).choose C : ℚ) =
        ((C + B - 1 - k₀).choose C : ℚ) * (R - 1) := by ring
    rw [hrew]
    simpa using pDiv_mul hp (pDiv_nat_zero hp _) hR1
  -- Combine Step 1 and Step 2: x1*y1 - x0*y0 = (x1 - x0)*y1 + x0*(y1 - y0)
  simp only [w1]; push_cast
  have hrew : ((C + B - 1 - (k₀ + L)).choose C : ℚ) * ((A - 1).choose (k₀ + L) : ℚ) ^ 2 -
      ((C + B - 1 - k₀).choose C : ℚ) * ((A - 1).choose k₀ : ℚ) ^ 2 =
      (((C + B - 1 - (k₀ + L)).choose C : ℚ) - ((C + B - 1 - k₀).choose C : ℚ)) *
        ((A - 1).choose (k₀ + L) : ℚ) ^ 2 +
      ((C + B - 1 - k₀).choose C : ℚ) *
        (((A - 1).choose (k₀ + L) : ℚ) ^ 2 - ((A - 1).choose k₀ : ℚ) ^ 2) := by ring
  rw [hrew]
  have h1 := pDiv_mul hp hfacC (pDiv_nat_zero hp (((A - 1).choose (k₀ + L)) ^ 2))
  push_cast at h1
  exact pDiv_add hp (by simpa using h1)
    (by simpa using pDiv_mul hp (pDiv_nat_zero hp _) hfacA)

lemma w2_block_const (p s d A B C k₀ L : ℕ) (hp : p.Prime)
    (hds : d < s) (hA : p ^ s ∣ A) (hB : p ^ s ∣ B) (hC : p ^ s ∣ C)
    (hk₀ : p ^ (d + 1) ∣ k₀) (hL : L + 1 < p ^ (d + 1)) (hBC : B ≤ C) (hkL : k₀ + L + 1 < B) :
    pDiv p (s - d) ((w2 A B C (k₀ + L) : ℚ) - (w2 A B C k₀ : ℚ)) := by
  -- Step 1: C(A + k₀ + L, k₀ + L)^2 ≡ C(A + k₀, k₀)^2 (mod p^(s - d))
  have hfacA : pDiv p (s - d)
      ((((A + (k₀ + L)).choose (k₀ + L) : ℚ) ^ 2) - (((A + k₀).choose k₀ : ℚ) ^ 2)) := by
    have hstepA : ∀ l : ℕ,
        (A + k₀ + l).choose (k₀ + l) * ∏ j ∈ Icc 1 l, (k₀ + j) =
          (A + k₀).choose k₀ * ∏ j ∈ Icc 1 l, (A + k₀ + j) := by
      intro l
      induction l with
      | zero => simp
      | succ l ihl =>
        have hIcc : Icc 1 (l + 1) = insert (l + 1) (Icc 1 l) := by
          ext x; simp only [mem_Icc, mem_insert]; omega
        rw [hIcc, prod_insert (by simp), prod_insert (by simp)]
        have hrec := Nat.add_one_mul_choose_eq (A + k₀ + l) (k₀ + l)
        -- (A + k₀ + l + 1) * C(A + k₀ + l, k₀ + l) = (k₀ + l + 1) * C(A + k₀ + l + 1, k₀ + l + 1)
        have h1 : (A + k₀ + (l + 1)).choose (k₀ + (l + 1)) * (k₀ + (l + 1)) =
            (A + k₀ + (l + 1)) * (A + k₀ + l).choose (k₀ + l) := by
          have e1 : A + k₀ + (l + 1) = A + k₀ + l + 1 := by omega
          have e2 : k₀ + (l + 1) = k₀ + l + 1 := by omega
          rw [e1, e2]; linarith
        calc (A + k₀ + (l + 1)).choose (k₀ + (l + 1)) *
              ((k₀ + (l + 1)) * ∏ j ∈ Icc 1 l, (k₀ + j))
            = ((A + k₀ + (l + 1)).choose (k₀ + (l + 1)) * (k₀ + (l + 1))) *
                ∏ j ∈ Icc 1 l, (k₀ + j) := by ring
          _ = (A + k₀ + (l + 1)) * ((A + k₀ + l).choose (k₀ + l) *
                ∏ j ∈ Icc 1 l, (k₀ + j)) := by rw [h1]; ring
          _ = (A + k₀ + (l + 1)) * ((A + k₀).choose k₀ *
                ∏ j ∈ Icc 1 l, (A + k₀ + j)) := by rw [ihl]
          _ = _ := by ring
    have hid := hstepA L
    have hadd : A + (k₀ + L) = A + k₀ + L := by omega
    rw [hadd]
    have hidQ : (((A + k₀ + L).choose (k₀ + L) : ℚ) * ∏ j ∈ Icc 1 L, ((k₀ + j : ℕ) : ℚ)) =
        (((A + k₀).choose k₀ : ℚ) * ∏ j ∈ Icc 1 L, ((A + k₀ + j : ℕ) : ℚ)) := by
      exact_mod_cast hid
    have hden_ne : (∏ j ∈ Icc 1 L, ((k₀ + j : ℕ) : ℚ)) ≠ 0 := by
      apply prod_ne_zero_iff.mpr; intro j hj
      exact Nat.cast_ne_zero.mpr (by have := (mem_Icc.mp hj).1; omega)
    set R := ∏ j ∈ Icc 1 L, (((A + k₀ + j : ℕ) : ℚ) / ((k₀ + j : ℕ) : ℚ))
    have hrat : ((A + k₀ + L).choose (k₀ + L) : ℚ) = ((A + k₀).choose k₀ : ℚ) * R := by
      dsimp only [R]; rw [prod_div_distrib]
      field_simp [hden_ne] at hidQ ⊢; linarith
    have hR1 : pDiv p (s - d) (R - 1) := by
      apply pDiv_prod_sub_one hp
      intro j hj
      have hj1 := (mem_Icc.mp hj).1
      have hj2 := (mem_Icc.mp hj).2
      exact ratio_add_one_pDiv p s d A k₀ j hp hds hA hk₀ hj1 (by omega)
    have hR0 : pDiv p 0 R := by
      have : R = (R - 1) + 1 := by ring
      rw [this]; exact pDiv_add hp (pDiv_mono (Nat.zero_le _) hR1) (pDiv_nat_zero hp 1)
    have hRsq : pDiv p (s - d) (R ^ 2 - 1) := by
      have : R ^ 2 - 1 = (R + 1) * (R - 1) := by ring
      rw [this]
      simpa using pDiv_mul hp (pDiv_add hp hR0 (pDiv_nat_zero hp 1)) hR1
    rw [hrat, mul_pow]
    have hrew : ((A + k₀).choose k₀ : ℚ) ^ 2 * R ^ 2 - ((A + k₀).choose k₀ : ℚ) ^ 2 =
        ((A + k₀).choose k₀ : ℚ) ^ 2 * (R ^ 2 - 1) := by ring
    rw [hrew]
    have h := pDiv_mul hp (pDiv_nat_zero hp (((A + k₀).choose k₀) ^ 2)) hRsq
    push_cast at h; simpa using h
  -- Step 2: (-1)^(B-2-(k₀+L)) * C(C-1, B-2-(k₀+L)) ≡ (-1)^(B-2-k₀) * C(C-1, B-2-k₀) (mod p^(s-d))
  have hfacC : pDiv p (s - d)
      ((-1 : ℚ) ^ (B - 2 - (k₀ + L)) * ((C - 1).choose (B - 2 - (k₀ + L)) : ℚ) -
       (-1 : ℚ) ^ (B - 2 - k₀) * ((C - 1).choose (B - 2 - k₀) : ℚ)) := by
    have hstepC : ∀ l : ℕ, k₀ + l + 1 < B →
        (C - 1).choose (B - 2 - (k₀ + l)) * ∏ j ∈ Icc 1 l, (C - B + k₀ + (j + 1)) =
          (C - 1).choose (B - 2 - k₀) * ∏ j ∈ Icc 1 l, (B - k₀ - (j + 1)) := by
      intro l
      induction l with
      | zero => intro _; simp
      | succ l ihl =>
        intro hl
        have hIcc : Icc 1 (l + 1) = insert (l + 1) (Icc 1 l) := by
          ext x; simp only [mem_Icc, mem_insert]; omega
        rw [hIcc, prod_insert (by simp), prod_insert (by simp)]
        have h1 : (C - 1).choose (B - 2 - (k₀ + (l + 1))) * (C - B + k₀ + (l + 1 + 1)) =
            (C - 1).choose (B - 2 - (k₀ + l)) * (B - k₀ - (l + 1 + 1)) := by
          set r := B - 2 - (k₀ + (l + 1))
          have hr1 : r + 1 = B - 2 - (k₀ + l) := by omega
          have hr2 : C - 1 - r = C - B + k₀ + (l + 1 + 1) := by omega
          have hr3 : r + 1 = B - k₀ - (l + 1 + 1) := by omega
          rw [← hr1, ← hr2, ← hr3]
          exact (Nat.choose_succ_right_eq (C - 1) r).symm
        calc (C - 1).choose (B - 2 - (k₀ + (l + 1))) *
              ((C - B + k₀ + (l + 1 + 1)) * ∏ j ∈ Icc 1 l, (C - B + k₀ + (j + 1)))
            = ((C - 1).choose (B - 2 - (k₀ + (l + 1))) * (C - B + k₀ + (l + 1 + 1))) *
                ∏ j ∈ Icc 1 l, (C - B + k₀ + (j + 1)) := by ring
          _ = (B - k₀ - (l + 1 + 1)) * ((C - 1).choose (B - 2 - (k₀ + l)) *
                ∏ j ∈ Icc 1 l, (C - B + k₀ + (j + 1))) := by rw [h1]; ring
          _ = (B - k₀ - (l + 1 + 1)) * ((C - 1).choose (B - 2 - k₀) *
                ∏ j ∈ Icc 1 l, (B - k₀ - (j + 1))) := by rw [ihl (by omega)]
          _ = _ := by ring
    have hid := hstepC L hkL
    have hidQ : (((C - 1).choose (B - 2 - (k₀ + L)) : ℚ) *
          ∏ j ∈ Icc 1 L, ((C - B + k₀ + (j + 1) : ℕ) : ℚ)) =
        (((C - 1).choose (B - 2 - k₀) : ℚ) * ∏ j ∈ Icc 1 L, ((B - k₀ - (j + 1) : ℕ) : ℚ)) := by
      exact_mod_cast hid
    have hden_ne : (∏ j ∈ Icc 1 L, ((C - B + k₀ + (j + 1) : ℕ) : ℚ)) ≠ 0 := by
      apply prod_ne_zero_iff.mpr; intro j hj
      exact Nat.cast_ne_zero.mpr (by have := (mem_Icc.mp hj).1; omega)
    set R := ∏ j ∈ Icc 1 L, (-(((B - k₀ - (j + 1) : ℕ) : ℚ) / ((C - B + k₀ + (j + 1) : ℕ) : ℚ)))
    have hrat : (-1 : ℚ) ^ (B - 2 - (k₀ + L)) * ((C - 1).choose (B - 2 - (k₀ + L)) : ℚ) =
        (-1 : ℚ) ^ (B - 2 - k₀) * ((C - 1).choose (B - 2 - k₀) : ℚ) * R := by
      dsimp only [R]; rw [prod_neg, Nat.card_Icc, Nat.add_sub_cancel, prod_div_distrib]
      have hsign : (-1 : ℚ) ^ (B - 2 - k₀) * (-1 : ℚ) ^ L = (-1 : ℚ) ^ (B - 2 - (k₀ + L)) := by
        rw [← pow_add]
        have hev : (B - 2 - k₀) + L = (B - 2 - (k₀ + L)) + 2 * L := by omega
        rw [hev, pow_add, pow_mul]; norm_num
      field_simp [hden_ne] at hidQ ⊢
      calc (((C - 1).choose (B - 2 - (k₀ + L)) : ℚ) *
              ∏ j ∈ Icc 1 L, ((C - B + k₀ + (j + 1) : ℕ) : ℚ)) * (-1 : ℚ) ^ (B - 2 - (k₀ + L))
          = (-1 : ℚ) ^ (B - 2 - (k₀ + L)) *
              (((C - 1).choose (B - 2 - k₀) : ℚ) *
                ∏ j ∈ Icc 1 L, ((B - k₀ - (j + 1) : ℕ) : ℚ)) := by rw [hidQ]; ring
        _ = ((-1 : ℚ) ^ (B - 2 - k₀) * (-1 : ℚ) ^ L) *
              (((C - 1).choose (B - 2 - k₀) : ℚ) *
                ∏ j ∈ Icc 1 L, ((B - k₀ - (j + 1) : ℕ) : ℚ)) := by rw [hsign]
        _ = _ := by ring
    have hR1 : pDiv p (s - d) (R - 1) := by
      apply pDiv_prod_sub_one hp
      intro j hj
      have hj1 := (mem_Icc.mp hj).1
      have hj2 := (mem_Icc.mp hj).2
      have h1 := ratio_sub_neg_one_pDiv p s d C B k₀ (j + 1) hp hds hC hB hk₀ hBC (by omega) (by omega) (by omega)
      have hrew : -(((B - k₀ - (j + 1) : ℕ) : ℚ) / ((C - B + k₀ + (j + 1) : ℕ) : ℚ)) - 1 =
          -((((B - k₀ - (j + 1) : ℕ) : ℚ) / ((C - B + k₀ + (j + 1) : ℕ) : ℚ)) + 1) := by ring
      rw [hrew]
      exact pDiv_neg h1
    rw [hrat]
    have hrew : (-1 : ℚ) ^ (B - 2 - k₀) * ((C - 1).choose (B - 2 - k₀) : ℚ) * R -
        (-1 : ℚ) ^ (B - 2 - k₀) * ((C - 1).choose (B - 2 - k₀) : ℚ) =
        ((-1 : ℚ) ^ (B - 2 - k₀) * ((C - 1).choose (B - 2 - k₀) : ℚ)) * (R - 1) := by ring
    rw [hrew]
    have hpre : pDiv p 0 ((-1 : ℚ) ^ (B - 2 - k₀) * ((C - 1).choose (B - 2 - k₀) : ℚ)) := by
      simpa using pDiv_int_zero hp ((-1 : ℤ) ^ (B - 2 - k₀) * ((C - 1).choose (B - 2 - k₀) : ℤ))
    simpa using pDiv_mul hp hpre hR1
  -- Combine Step 1 and Step 2
  simp only [w2]; push_cast
  have hrew : (-1 : ℚ) ^ (B - 2 - (k₀ + L)) * ((C - 1).choose (B - 2 - (k₀ + L)) : ℚ) *
        ((A + (k₀ + L)).choose (k₀ + L) : ℚ) ^ 2 -
      (-1 : ℚ) ^ (B - 2 - k₀) * ((C - 1).choose (B - 2 - k₀) : ℚ) * ((A + k₀).choose k₀ : ℚ) ^ 2 =
      ((-1 : ℚ) ^ (B - 2 - (k₀ + L)) * ((C - 1).choose (B - 2 - (k₀ + L)) : ℚ) -
       (-1 : ℚ) ^ (B - 2 - k₀) * ((C - 1).choose (B - 2 - k₀) : ℚ)) *
        ((A + (k₀ + L)).choose (k₀ + L) : ℚ) ^ 2 +
      ((-1 : ℚ) ^ (B - 2 - k₀) * ((C - 1).choose (B - 2 - k₀) : ℚ)) *
        (((A + (k₀ + L)).choose (k₀ + L) : ℚ) ^ 2 - ((A + k₀).choose k₀ : ℚ) ^ 2) := by ring
  rw [hrew]
  have hpre : pDiv p 0 ((-1 : ℚ) ^ (B - 2 - k₀) * ((C - 1).choose (B - 2 - k₀) : ℚ)) := by
    simpa using pDiv_int_zero hp ((-1 : ℤ) ^ (B - 2 - k₀) * ((C - 1).choose (B - 2 - k₀) : ℤ))
  have h1 := pDiv_mul hp hfacC (pDiv_nat_zero hp (((A + (k₀ + L)).choose (k₀ + L)) ^ 2))
  push_cast at h1
  exact pDiv_add hp (by simpa using h1)
    (by simpa using pDiv_mul hp hpre hfacA)

-- ============================================================================
-- Section 3: Abstract block-constancy 1D sum vanishing theorem!
-- ============================================================================

-- If w : ℕ → ℤ satisfies w((m*p + u)*p^d) ≡ w(m*p^(d+1)) (mod p^(s-d)) for all d < s,
-- and w(k*p + u - 1) ≡ w(k*p) (mod p^s) for 1 ≤ u < p,
-- then ∑_{1 ≤ i < B, p ∤ i} w(i - 1) / i^2 ≡ 0 (mod p^s)!!
theorem block_const_sum_pDiv (p s B : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hs : 1 ≤ s)
    (hB : p ^ s ∣ B) (w : ℕ → ℤ)
    (hw : ∀ d < s, ∀ k₀ L, p ^ (d + 1) ∣ k₀ → L + 1 < p ^ (d + 1) → k₀ + L + 1 < B →
      pDiv p (s - d) ((w (k₀ + L) : ℚ) - (w k₀ : ℚ))) :
    pDiv p s (∑ i ∈ (range B).filter (fun i => ¬ p ∣ i), (w (i - 1) : ℚ) / ((i : ℚ) ^ 2)) := by
  -- Define stage sum T(d) = ∑_{m < B / p^d} w(m * p^d) * H(d, m)
  -- where H(d, m) = ∑_{j ∈ (range (p^d)).filter (¬ p ∣ ·)} 1 / (m * p^d + j)^2.
  let H : ℕ → ℕ → ℚ := fun d m =>
    ∑ j ∈ (range (p ^ d)).filter (fun j => ¬ p ∣ j),
      (1 : ℚ) / (((m * p ^ d + j : ℕ) : ℚ) ^ 2)
  let T : ℕ → ℚ := fun d => ∑ m ∈ range (B / p ^ d), (w (m * p ^ d) : ℚ) * H d m
  -- Step A: original sum - T(1) has pDiv p s!
  have hbase : pDiv p s
      ((∑ i ∈ (range B).filter (fun i => ¬ p ∣ i), (w (i - 1) : ℚ) / ((i : ℚ) ^ 2)) - T 1) := by
    rcases hB with ⟨q, hq⟩
    have hBp : B / p = q * p ^ (s - 1) := by
      have : B = (q * p ^ (s - 1)) * p := by
        rw [hq, mul_comm, mul_assoc, ← pow_succ, Nat.sub_add_cancel hs]
      rw [this, Nat.mul_div_cancel _ hp.pos]
    have hB_eq : B = (B / p) * p := by
      rw [hBp, hq, mul_comm, mul_assoc, ← pow_succ, Nat.sub_add_cancel hs]
    -- Partition (range B).filter (¬ p ∣ ·) into blocks m ∈ range (B / p), u ∈ (range p).filter (¬ p ∣ ·)
    have hpart : (∑ i ∈ (range B).filter (fun i => ¬ p ∣ i), (w (i - 1) : ℚ) / ((i : ℚ) ^ 2)) =
        ∑ m ∈ range (B / p), ∑ u ∈ (range p).filter (fun u => ¬ p ∣ u),
          (w (m * p + u - 1) : ℚ) / (((m * p + u : ℕ) : ℚ) ^ 2) := by
      rw [← sum_product']
      refine Finset.sum_bij (fun i _ => (i / p, i % p)) ?_ ?_ ?_ ?_
      · intro i hi
        have hiB := mem_range.mp (mem_filter.mp hi).1
        have hind := (mem_filter.mp hi).2
        refine mem_product.mpr ⟨mem_range.mpr ?_, mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt i hp.pos), ?_⟩⟩
        · exact (Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega)
        · intro hdiv
          have : i % p = 0 := Nat.eq_zero_of_dvd_of_lt hdiv (Nat.mod_lt i hp.pos)
          exact hind (Nat.dvd_of_mod_eq_zero this)
      · intro i₁ _ i₂ _ h
        have h1 : i₁ / p = i₂ / p := congrArg Prod.fst h
        have h2 : i₁ % p = i₂ % p := congrArg Prod.snd h
        rw [← Nat.div_add_mod i₁ p, ← Nat.div_add_mod i₂ p, h1, h2]
      · intro ⟨m, u⟩ hmu
        have hm := mem_range.mp (mem_product.mp hmu).1
        have hu := mem_range.mp (mem_filter.mp (mem_product.mp hmu).2).1
        have hund := (mem_filter.mp (mem_product.mp hmu).2).2
        refine ⟨m * p + u, mem_filter.mpr ⟨mem_range.mpr (by nlinarith), ?_⟩, ?_⟩
        · intro hdiv
          have : p ∣ u := (Nat.dvd_add_right (dvd_mul_left p m)).mp hdiv
          exact hund this
        · ext
          · dsimp only; rw [mul_comm m p, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hu, add_zero]
          · dsimp only; rw [mul_comm m p, Nat.mul_add_mod, Nat.mod_eq_of_lt hu]
      · intro i _
        have hdiv : i / p * p + i % p = i := by rw [mul_comm]; exact Nat.div_add_mod i p
        simp [hdiv]
    rw [hpart]
    dsimp only [T, H]
    simp only [pow_one, mul_sum, ← sum_sub_distrib]
    apply pDiv_sum hp; intro m hm
    apply pDiv_sum hp; intro u hu
    have hm' := mem_range.mp hm
    have hu' := mem_range.mp (mem_filter.mp hu).1
    have hund := (mem_filter.mp hu).2
    have hu_pos : 1 ≤ u := Nat.pos_of_ne_zero (fun h0 => hund (h0 ▸ dvd_zero p))
    have hdiff : (w (m * p + u - 1) : ℚ) / (((m * p + u : ℕ) : ℚ) ^ 2) -
        (w (m * p) : ℚ) * ((1 : ℚ) / (((m * p + u : ℕ) : ℚ) ^ 2)) =
        ((w (m * p + (u - 1)) : ℚ) - (w (m * p) : ℚ)) *
          ((1 : ℚ) / (((m * p + u : ℕ) : ℚ) ^ 2)) := by
      have hsub : m * p + u - 1 = m * p + (u - 1) := by omega
      rw [hsub]; ring
    rw [hdiff]
    have hmp_lt : m * p + (u - 1) + 1 < B := by
      have h1 : (m + 1) * p ≤ (B / p) * p := Nat.mul_le_mul_right p hm'
      rw [← hB_eq] at h1
      have hu1 : u - 1 + 1 = u := by omega
      nlinarith
    have hw0 := hw 0 hs (m * p) (u - 1) (by simp only [zero_add, pow_one]; exact dvd_mul_left p m)
      (by simp only [zero_add, pow_one]; omega) hmp_lt
    have hinv : pDiv p 0 ((1 : ℚ) / (((m * p + u : ℕ) : ℚ) ^ 2)) := by
      have hndvd : ¬ p ∣ (m * p + u) := fun h => hund ((Nat.dvd_add_right (dvd_mul_left p m)).mp h)
      refine ⟨1, (m * p + u) * (m * p + u), hp.not_dvd_mul hndvd hndvd, ?_⟩
      push_cast; ring
    simpa using pDiv_mul hp hw0 hinv
  -- Step B: for 1 ≤ d < s, T(d) - T(d + 1) has pDiv p s!
  have hstep : ∀ d, 1 ≤ d → d < s → pDiv p s (T d - T (d + 1)) := by
    intro d hd1 hds
    have hpd1_dvd : p ^ (d + 1) ∣ B := dvd_trans (pow_dvd_pow p (by omega)) hB
    have hdiv_eq : B / p ^ d = (B / p ^ (d + 1)) * p := by
      rcases hpd1_dvd with ⟨q, hq⟩
      have h1 : B / p ^ (d + 1) = q := by rw [hq, mul_comm, Nat.mul_div_cancel _ (pow_pos hp.pos _)]
      have h2 : B / p ^ d = q * p := by
        have heq : B = (q * p) * p ^ d := by rw [hq, pow_succ]; ring
        rw [heq, Nat.mul_div_cancel _ (pow_pos hp.pos _)]
      rw [h1, h2]
    have hsplit : T d = ∑ m' ∈ range (B / p ^ (d + 1)), ∑ v ∈ range p,
        (w ((m' * p + v) * p ^ d) : ℚ) * H d (m' * p + v) := by
      dsimp only [T]
      rw [← sum_product']
      refine Finset.sum_bij (fun m _ => (m / p, m % p)) ?_ ?_ ?_ ?_
      · intro m hm
        have hm' := mem_range.mp hm
        refine mem_product.mpr ⟨mem_range.mpr ?_, mem_range.mpr (Nat.mod_lt m hp.pos)⟩
        exact (Nat.div_lt_iff_lt_mul hp.pos).mpr (by rw [← hdiv_eq]; exact hm')
      · intro m₁ _ m₂ _ h
        have h1 : m₁ / p = m₂ / p := congrArg Prod.fst h
        have h2 : m₁ % p = m₂ % p := congrArg Prod.snd h
        rw [← Nat.div_add_mod m₁ p, ← Nat.div_add_mod m₂ p, h1, h2]
      · intro ⟨m', v⟩ hmv
        have hm' := mem_range.mp (mem_product.mp hmv).1
        have hv := mem_range.mp (mem_product.mp hmv).2
        refine ⟨m' * p + v, mem_range.mpr (by rw [hdiv_eq]; nlinarith), ?_⟩
        ext
        · dsimp only; rw [mul_comm m' p, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hv, add_zero]
        · dsimp only; rw [mul_comm m' p, Nat.mul_add_mod, Nat.mod_eq_of_lt hv]
      · intro m _
        have hm : m / p * p + m % p = m := by rw [mul_comm]; exact Nat.div_add_mod m p
        simp [hm]
    have hH_split : ∀ m', H (d + 1) m' = ∑ v ∈ range p, H d (m' * p + v) := by
      intro m'
      dsimp only [H]
      rw [← sum_product']
      refine Finset.sum_bij (fun j _ => (j / p ^ d, j % p ^ d)) ?_ ?_ ?_ ?_
      · intro j hj
        have hj1 := mem_range.mp (mem_filter.mp hj).1
        have hjnd := (mem_filter.mp hj).2
        refine mem_product.mpr ⟨mem_range.mpr ?_, mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt j (pow_pos hp.pos d)), ?_⟩⟩
        · exact (Nat.div_lt_iff_lt_mul (pow_pos hp.pos d)).mpr (by rw [mul_comm, ← pow_succ]; exact hj1)
        · intro hdiv
          have hpd : p ∣ p ^ d := dvd_pow_self p (by omega)
          have : p ∣ j := by
            have := Nat.div_add_mod j (p ^ d)
            rw [← this]
            exact dvd_add (dvd_mul_of_dvd_left hpd _) hdiv
          exact hjnd this
      · intro j₁ _ j₂ _ h
        have h1 : j₁ / p ^ d = j₂ / p ^ d := congrArg Prod.fst h
        have h2 : j₁ % p ^ d = j₂ % p ^ d := congrArg Prod.snd h
        rw [← Nat.div_add_mod j₁ (p ^ d), ← Nat.div_add_mod j₂ (p ^ d), h1, h2]
      · intro ⟨v, u⟩ hvu
        have hv := mem_range.mp (mem_product.mp hvu).1
        have hu := mem_range.mp (mem_filter.mp (mem_product.mp hvu).2).1
        have hund := (mem_filter.mp (mem_product.mp hvu).2).2
        refine ⟨v * p ^ d + u, mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩, ?_⟩
        · rw [pow_succ]; nlinarith
        · intro hdiv
          have hpd : p ∣ v * p ^ d := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) v
          exact hund ((Nat.dvd_add_right hpd).mp hdiv)
        · ext
          · dsimp only
            rw [mul_comm v (p ^ d), Nat.mul_add_div (pow_pos hp.pos d), Nat.div_eq_of_lt hu, add_zero]
          · dsimp only
            rw [mul_comm v (p ^ d), Nat.mul_add_mod, Nat.mod_eq_of_lt hu]
      · intro j _
        have h1 : (m' * p + j / p ^ d) * p ^ d + j % p ^ d = m' * p ^ (d + 1) + j := by
          have hdm := Nat.div_add_mod j (p ^ d)
          rw [pow_succ]; nlinarith
        simp [h1]
    rw [hsplit]
    have hT1 : T (d + 1) = ∑ m' ∈ range (B / p ^ (d + 1)), ∑ v ∈ range p,
        (w (m' * p ^ (d + 1)) : ℚ) * H d (m' * p + v) := by
      dsimp only [T]
      apply sum_congr rfl; intro m' _
      rw [hH_split m', mul_sum]
    rw [hT1, ← sum_sub_distrib]
    apply pDiv_sum hp; intro m' hm'
    rw [← sum_sub_distrib]
    apply pDiv_sum hp; intro v hv
    have hm'' := mem_range.mp hm'
    have hv' := mem_range.mp hv
    have hrew : (w ((m' * p + v) * p ^ d) : ℚ) * H d (m' * p + v) -
        (w (m' * p ^ (d + 1)) : ℚ) * H d (m' * p + v) =
        ((w (m' * p ^ (d + 1) + v * p ^ d) : ℚ) - (w (m' * p ^ (d + 1)) : ℚ)) *
          H d (m' * p + v) := by
      have : (m' * p + v) * p ^ d = m' * p ^ (d + 1) + v * p ^ d := by rw [pow_succ]; ring
      rw [this]; ring
    rw [hrew]
    have hpd_gt1 : 1 < p ^ d := by
      calc 1 < p := by omega
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ d := Nat.pow_le_pow_right hp.pos hd1
    have hlt_B : m' * p ^ (d + 1) + v * p ^ d + 1 < B := by
      have hB1 : (B / p ^ (d + 1)) * p ^ (d + 1) = B := Nat.div_mul_cancel hpd1_dvd
      have h1 : (m' * p + v + 1) * p ^ d ≤ (B / p ^ (d + 1)) * p ^ (d + 1) := by
        have hm1 : m' * p + v + 1 ≤ (B / p ^ (d + 1)) * p := by nlinarith
        calc (m' * p + v + 1) * p ^ d
            ≤ ((B / p ^ (d + 1)) * p) * p ^ d := Nat.mul_le_mul_right _ hm1
          _ = (B / p ^ (d + 1)) * p ^ (d + 1) := by rw [pow_succ]; ring
      have h2 : m' * p ^ (d + 1) + v * p ^ d + p ^ d = (m' * p + v + 1) * p ^ d := by
        rw [pow_succ]; ring
      omega
    have hw_diff := hw d hds (m' * p ^ (d + 1)) (v * p ^ d)
      (dvd_mul_left _ _) (by rw [pow_succ]; nlinarith [hpd_gt1]) hlt_B
    have hHd : pDiv p d (H d (m' * p + v)) := unit_inv_sq_sum_pDiv p d (m' * p + v) hp hp5 hd1
    have hprod := pDiv_mul hp hw_diff hHd
    have hexp : s - d + d = s := by omega
    rwa [hexp] at hprod
  -- Step C: T(s) has pDiv p s!
  have hTs : pDiv p s (T s) := by
    dsimp only [T]
    apply pDiv_sum hp; intro m _
    have h1 := pDiv_mul hp (pDiv_int_zero hp (w (m * p ^ s))) (unit_inv_sq_sum_pDiv p s m hp hp5 hs)
    simpa only [zero_add] using h1
  -- Step D: Chain T(1) - T(s) by induction on s!
  have hT1_s : ∀ k, 1 ≤ k → k ≤ s → pDiv p s (T k - T s) := by
    intro k hk1 hks
    have hrec : ∀ t, t ≤ s - 1 → pDiv p s (T (s - t) - T s) := by
      intro t
      induction t with
      | zero =>
        intro _
        simp [pDiv_zero p s hp]
      | succ t iht =>
        intro ht
        have h1 : T (s - (t + 1)) - T s =
            (T (s - (t + 1)) - T (s - t)) + (T (s - t) - T s) := by ring
        rw [h1]
        have hstep' := hstep (s - (t + 1)) (by omega) (by omega)
        have heq : s - (t + 1) + 1 = s - t := by omega
        rw [heq] at hstep'
        exact pDiv_add hp hstep' (iht (by omega))
    have h := hrec (s - k) (by omega)
    have heq : s - (s - k) = k := by omega
    rwa [heq] at h
  have hT1 : pDiv p s (T 1) := by
    have : T 1 = (T 1 - T s) + T s := by ring
    rw [this]
    exact pDiv_add hp (hT1_s 1 le_rfl hs) hTs
  have hfinal : (∑ i ∈ (range B).filter (fun i => ¬ p ∣ i), (w (i - 1) : ℚ) / ((i : ℚ) ^ 2)) =
      ((∑ i ∈ (range B).filter (fun i => ¬ p ∣ i), (w (i - 1) : ℚ) / ((i : ℚ) ^ 2)) - T 1) + T 1 := by
    ring
  rw [hfinal]
  exact pDiv_add hp hbase hT1

-- Concrete corollaries for S1 and S2!
lemma S1_vanish_dvd (p r s n m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hsr : s ≤ r)
    (hm_dvd : p ^ (s - 1) ∣ m) (hm_le : m ≤ n * p ^ (r - 1)) :
    (p : ℤ) ^ (2 * r + s) ∣
      ∑ i ∈ (range (n * p ^ r + 1 - m * p)).filter (fun i => ¬ p ∣ i),
        (((4 * (n * p ^ r) - m * p - i).choose (3 * (n * p ^ r)) : ℤ) *
          (((n * p ^ r).choose i : ℤ) ^ 2)) := by
  set N := n * p ^ r
  set B := N - m * p
  have hB_le : B ≤ N := Nat.sub_le _ _
  have hN_dvd : p ^ s ∣ N := dvd_mul_of_dvd_right (pow_dvd_pow p hsr) n
  have hmp_dvd : p ^ s ∣ (m * p) := by
    have : p ^ s = p ^ (s - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hs]
    rw [this]; exact mul_dvd_mul_right hm_dvd p
  have hB_dvd : p ^ s ∣ B := Nat.dvd_sub hN_dvd hmp_dvd
  have h3N_dvd : p ^ s ∣ (3 * N) := dvd_mul_of_dvd_right hN_dvd 3
  -- Notice B + 1 has B as top element, and p ∣ B so B is filtered out!
  have hfilt : (range (N + 1 - m * p)).filter (fun i => ¬ p ∣ i) =
      (range B).filter (fun i => ¬ p ∣ i) := by
    ext i
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hi, hnd⟩
      refine ⟨?_, hnd⟩
      by_contra hge
      have hieq : i = B := by
        have hmp_le : m * p ≤ N := by
          calc m * p ≤ (n * p ^ (r - 1)) * p := Nat.mul_le_mul_right p hm_le
            _ = n * (p ^ (r - 1) * p) := by ring
            _ = N := by rw [← pow_succ, Nat.sub_add_cancel hr]
        omega
      rw [hieq] at hnd
      exact hnd (dvd_trans (dvd_pow_self p (by omega)) hB_dvd)
    · rintro ⟨hi, hnd⟩
      exact ⟨by omega, hnd⟩
  rw [hfilt]
  apply int_dvd_of_pDiv hp
  -- Rewrite each term using C(N, i) = (N / i) * C(N - 1, i - 1)!
  have hrew : (∑ i ∈ (range B).filter (fun i => ¬ p ∣ i),
      (((4 * N - m * p - i).choose (3 * N) : ℤ) * ((N.choose i : ℤ) ^ 2)) : ℚ) =
      ((N : ℚ) ^ 2) * ∑ i ∈ (range B).filter (fun i => ¬ p ∣ i),
        (w1 N B (3 * N) (i - 1) : ℚ) / ((i : ℚ) ^ 2) := by
    rw [mul_sum]
    push_cast
    apply sum_congr rfl; intro i hi
    have hiB := mem_range.mp (mem_filter.mp hi).1
    have hind := (mem_filter.mp hi).2
    have hi_pos : 1 ≤ i := Nat.pos_of_ne_zero (fun h0 => hind (h0 ▸ dvd_zero p))
    have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hN_pos : 1 ≤ N := by omega
    have hchoose : (N.choose i : ℚ) * (i : ℚ) = (N : ℚ) * ((N - 1).choose (i - 1) : ℚ) := by
      have h1 := Nat.add_one_mul_choose_eq (N - 1) (i - 1)
      have e1 : N - 1 + 1 = N := by omega
      have e2 : i - 1 + 1 = i := by omega
      rw [e1, e2] at h1
      have h1Q : (N : ℚ) * ((N - 1).choose (i - 1) : ℚ) = (N.choose i : ℚ) * (i : ℚ) := by
        exact_mod_cast h1
      linarith
    have hch_div : (N.choose i : ℚ) = (N : ℚ) * ((N - 1).choose (i - 1) : ℚ) / (i : ℚ) := by
      field_simp [hi0]; linarith
    have hsub1 : 3 * N + B - 1 - (i - 1) = 4 * N - m * p - i := by
      have hmp_le : m * p ≤ N := by
        calc m * p ≤ (n * p ^ (r - 1)) * p := Nat.mul_le_mul_right p hm_le
          _ = n * (p ^ (r - 1) * p) := by ring
          _ = N := by rw [← pow_succ, Nat.sub_add_cancel hr]
      omega
    simp only [w1]
    push_cast
    rw [hsub1, hch_div]
    ring
  have hcast : ((∑ i ∈ (range B).filter (fun i => ¬ p ∣ i),
      (((4 * N - m * p - i).choose (3 * N) : ℤ) * ((N.choose i : ℤ) ^ 2)) : ℤ) : ℚ) =
      ((N : ℚ) ^ 2) * ∑ i ∈ (range B).filter (fun i => ¬ p ∣ i),
        (w1 N B (3 * N) (i - 1) : ℚ) / ((i : ℚ) ^ 2) := by
    simpa using hrew
  rw [hcast]
  have hN2 : pDiv p (2 * r) ((N : ℚ) ^ 2) := by
    have h1 : p ^ (2 * r) ∣ N ^ 2 := by
      have : p ^ (2 * r) = (p ^ r) ^ 2 := by rw [← pow_mul, mul_comm]
      rw [this]; exact pow_dvd_pow_of_dvd (dvd_mul_left _ _) 2
    rcases h1 with ⟨c, hc⟩
    exact ⟨c, 1, hp.not_dvd_one, by have : (N : ℚ) ^ 2 = ((N ^ 2 : ℕ) : ℚ) := by push_cast; rfl
                                    rw [this, hc]; push_cast; ring⟩
  have hsum := block_const_sum_pDiv p s B hp hp5 hs hB_dvd (w1 N B (3 * N))
    (fun d hds k₀ L hk₀ hL hkL => w1_block_const p s d N B (3 * N) k₀ L hp hds hN_dvd hB_dvd h3N_dvd hk₀ (by omega) hB_le (by omega))
  exact pDiv_mul hp hN2 hsum

lemma S2_vanish_dvd (p r s n m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hsr : s ≤ r)
    (hm_dvd : p ^ (s - 1) ∣ m) (hm_lt : m < n * p ^ (r - 1)) :
    (p : ℤ) ^ (2 * r + s) ∣
      ∑ i ∈ (range (n * p ^ r - m * p)).filter (fun i => ¬ p ∣ i),
        ((-1 : ℤ) ^ (n * p ^ r - 1 - m * p - i) *
          ((3 * (n * p ^ r) - 1).choose (n * p ^ r - 1 - m * p - i) : ℤ) *
          (((n * p ^ r + i - 1).choose i : ℤ) ^ 2)) := by
  set N := n * p ^ r
  set B := N - m * p
  have hmp_lt : m * p < N := by
    calc m * p < (n * p ^ (r - 1)) * p := Nat.mul_lt_mul_of_pos_right hm_lt hp.pos
      _ = n * (p ^ (r - 1) * p) := by ring
      _ = N := by rw [← pow_succ, Nat.sub_add_cancel hr]
  have hN_dvd : p ^ s ∣ N := dvd_mul_of_dvd_right (pow_dvd_pow p hsr) n
  have hmp_dvd : p ^ s ∣ (m * p) := by
    have : p ^ s = p ^ (s - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hs]
    rw [this]; exact mul_dvd_mul_right hm_dvd p
  have hB_dvd : p ^ s ∣ B := Nat.dvd_sub hN_dvd hmp_dvd
  have h3N_dvd : p ^ s ∣ (3 * N) := dvd_mul_of_dvd_right hN_dvd 3
  apply int_dvd_of_pDiv hp
  have hcast : ((∑ i ∈ (range B).filter (fun i => ¬ p ∣ i),
      ((-1 : ℤ) ^ (N - 1 - m * p - i) *
        ((3 * N - 1).choose (N - 1 - m * p - i) : ℤ) *
        (((N + i - 1).choose i : ℤ) ^ 2)) : ℤ) : ℚ) =
      ((N : ℚ) ^ 2) * ∑ i ∈ (range B).filter (fun i => ¬ p ∣ i),
        (w2 N B (3 * N) (i - 1) : ℚ) / ((i : ℚ) ^ 2) := by
    rw [mul_sum]
    push_cast
    apply sum_congr rfl; intro i hi
    have hiB := mem_range.mp (mem_filter.mp hi).1
    have hind := (mem_filter.mp hi).2
    have hi_pos : 1 ≤ i := Nat.pos_of_ne_zero (fun h0 => hind (h0 ▸ dvd_zero p))
    have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    -- C(N + i - 1, i) * i = N * C(N + i - 1, i - 1)!
    have hchoose : ((N + i - 1).choose i : ℚ) * (i : ℚ) = (N : ℚ) * ((N + (i - 1)).choose (i - 1) : ℚ) := by
      have h1 := Nat.choose_succ_right_eq (N + i - 1) (i - 1)
      have e1 : i - 1 + 1 = i := by omega
      have e2 : N + i - 1 - (i - 1) = N := by omega
      have e3 : N + i - 1 = N + (i - 1) := by omega
      rw [e1, e2, e3] at h1
      have h1Q : ((N + (i - 1)).choose i : ℚ) * (i : ℚ) =
          ((N + (i - 1)).choose (i - 1) : ℚ) * (N : ℚ) := by exact_mod_cast h1
      rw [e3]; linarith
    have hch_div : ((N + i - 1).choose i : ℚ) =
        (N : ℚ) * ((N + (i - 1)).choose (i - 1) : ℚ) / (i : ℚ) := by
      field_simp [hi0]; linarith
    have hsub1 : B - 2 - (i - 1) = N - 1 - m * p - i := by
      have hiB : i < N - m * p := mem_range.mp (mem_filter.mp hi).1
      change (N - m * p) - 2 - (i - 1) = N - 1 - m * p - i
      omega
    simp only [w2]
    push_cast
    rw [hsub1, hch_div]
    ring
  rw [hcast]
  have hN2 : pDiv p (2 * r) ((N : ℚ) ^ 2) := by
    have h1 : p ^ (2 * r) ∣ N ^ 2 := by
      have : p ^ (2 * r) = (p ^ r) ^ 2 := by rw [← pow_mul, mul_comm]
      rw [this]; exact pow_dvd_pow_of_dvd (dvd_mul_left _ _) 2
    rcases h1 with ⟨c, hc⟩
    exact ⟨c, 1, hp.not_dvd_one, by have : (N : ℚ) ^ 2 = ((N ^ 2 : ℕ) : ℚ) := by push_cast; rfl
                                    rw [this, hc]; push_cast; ring⟩
  have hsum := block_const_sum_pDiv p s B hp hp5 hs hB_dvd (w2 N B (3 * N))
    (fun d hds k₀ L hk₀ hL hkL => w2_block_const p s d N B (3 * N) k₀ L hp hds hN_dvd hB_dvd h3N_dvd hk₀ hL (by omega) hkL)
  exact pDiv_mul hp hN2 hsum

end OMA_A364114_Part3

namespace OMA_A364114_Part4

open Finset

-- Local copies of pDiv helpers for standalone compilation (deduplicated on assembly)
def pDiv (p k : ℕ) (q : ℚ) : Prop :=
  ∃ (a : ℤ) (b : ℕ), ¬ (p ∣ b) ∧ q = ((p : ℚ) ^ k * (a : ℚ)) / (b : ℚ)

lemma pDiv_zero (p k : ℕ) (hp : p.Prime) : pDiv p k 0 := ⟨0, 1, hp.not_dvd_one, by simp⟩

lemma pDiv_mono {p k₁ k₂ : ℕ} {q : ℚ} (h : k₁ ≤ k₂) (hq : pDiv p k₂ q) : pDiv p k₁ q := by
  rcases hq with ⟨a, b, hb, rfl⟩
  refine ⟨a * (p : ℤ) ^ (k₂ - k₁), b, hb, ?_⟩
  have hadd : k₁ + (k₂ - k₁) = k₂ := Nat.add_sub_of_le h
  push_cast; conv_lhs => rw [← hadd, pow_add]
  ring

lemma pDiv_add {p k : ℕ} {q₁ q₂ : ℚ} (hp : p.Prime) (h1 : pDiv p k q₁) (h2 : pDiv p k q₂) :
    pDiv p k (q₁ + q₂) := by
  rcases h1 with ⟨a₁, b₁, hb₁, rfl⟩
  rcases h2 with ⟨a₂, b₂, hb₂, rfl⟩
  have hb₁0 : (b₁ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h => hb₁ (h ▸ dvd_zero p))
  have hb₂0 : (b₂ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h => hb₂ (h ▸ dvd_zero p))
  refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, hp.not_dvd_mul hb₁ hb₂, ?_⟩
  push_cast; field_simp [hb₁0, hb₂0]

lemma pDiv_neg {p k : ℕ} {q : ℚ} (h : pDiv p k q) : pDiv p k (-q) := by
  rcases h with ⟨a, b, hb, rfl⟩
  exact ⟨-a, b, hb, by push_cast; ring⟩

lemma pDiv_sub {p k : ℕ} {q₁ q₂ : ℚ} (hp : p.Prime) (h1 : pDiv p k q₁) (h2 : pDiv p k q₂) :
    pDiv p k (q₁ - q₂) := by
  rw [sub_eq_add_neg]; exact pDiv_add hp h1 (pDiv_neg h2)

lemma pDiv_mul {p k₁ k₂ : ℕ} {q₁ q₂ : ℚ} (hp : p.Prime)
    (h1 : pDiv p k₁ q₁) (h2 : pDiv p k₂ q₂) : pDiv p (k₁ + k₂) (q₁ * q₂) := by
  rcases h1 with ⟨a₁, b₁, hb₁, rfl⟩
  rcases h2 with ⟨a₂, b₂, hb₂, rfl⟩
  refine ⟨a₁ * a₂, b₁ * b₂, hp.not_dvd_mul hb₁ hb₂, ?_⟩
  push_cast; rw [pow_add]; ring

lemma pDiv_sum {ι : Type*} {p k : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, pDiv p k (f i)) : pDiv p k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [pDiv_zero p k hp]
  | @insert x s hx ih =>
    rw [sum_insert hx]
    exact pDiv_add hp (hf x (mem_insert_self x s))
      (ih (fun y hy => hf y (mem_insert_of_mem hy)))

lemma pDiv_int_zero {p : ℕ} (hp : p.Prime) (z : ℤ) : pDiv p 0 (z : ℚ) :=
  ⟨z, 1, hp.not_dvd_one, by simp⟩

lemma pDiv_nat_zero {p : ℕ} (hp : p.Prime) (n : ℕ) : pDiv p 0 (n : ℚ) :=
  ⟨n, 1, hp.not_dvd_one, by simp⟩

lemma pDiv_p_pow (p k : ℕ) (hp : p.Prime) : pDiv p k ((p : ℚ) ^ k) :=
  ⟨1, 1, hp.not_dvd_one, by simp⟩

lemma pDiv_p_one (p : ℕ) (hp : p.Prime) : pDiv p 1 (p : ℚ) :=
  ⟨1, 1, hp.not_dvd_one, by simp⟩

lemma pDiv_div_nat_unit {p k m : ℕ} {q : ℚ} (hp : p.Prime) (hm : ¬ p ∣ m)
    (hq : pDiv p k q) : pDiv p k (q / (m : ℚ)) := by
  rcases hq with ⟨a, b, hb, rfl⟩
  refine ⟨a, b * m, hp.not_dvd_mul hb hm, ?_⟩
  push_cast; ring

lemma pDiv_pow {p k n : ℕ} {q : ℚ} (hp : p.Prime) (hq : pDiv p k q) :
    pDiv p (k * n) (q ^ n) := by
  induction n with
  | zero => simpa using pDiv_nat_zero hp 1
  | succ n ih => rw [pow_succ, Nat.mul_succ]; exact pDiv_mul hp ih hq

lemma pDiv_cancel_nat_unit {p k m : ℕ} {q : ℚ} (hp : p.Prime) (hm : ¬ p ∣ m)
    (hq : pDiv p k ((m : ℚ) * q)) : pDiv p k q := by
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h0 => hm (h0 ▸ dvd_zero p))
  have h := pDiv_div_nat_unit hp hm hq
  rwa [mul_div_cancel_left₀ _ hm0] at h

lemma pDiv_cancel_p_pow {p k r : ℕ} {q : ℚ} (hp : p.Prime)
    (hq : pDiv p (k + r) ((p : ℚ) ^ r * q)) : pDiv p k q := by
  rcases hq with ⟨a, b, hb, heq⟩
  have hp0 : (p : ℚ) ^ r ≠ 0 := pow_ne_zero r (Nat.cast_ne_zero.mpr hp.ne_zero)
  refine ⟨a, b, hb, ?_⟩
  have h1 : (p : ℚ) ^ r * q = (p : ℚ) ^ r * (((p : ℚ) ^ k * (a : ℚ)) / (b : ℚ)) := by
    rw [heq, pow_add]; ring
  exact mul_left_cancel₀ hp0 h1

lemma int_dvd_of_pDiv {p k : ℕ} {z : ℤ} (hp : p.Prime) (h : pDiv p k (z : ℚ)) :
    (p : ℤ) ^ k ∣ z := by
  rcases h with ⟨a, b, hb, heq⟩
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h0 => hb (h0 ▸ dvd_zero p))
  have h1 : (z : ℚ) * (b : ℚ) = (p : ℚ) ^ k * (a : ℚ) := by rw [heq]; field_simp [hb0]
  have h2 : z * (b : ℤ) = (p : ℤ) ^ k * a := by exact_mod_cast h1
  have hcop : IsCoprime ((p : ℤ) ^ k) (b : ℤ) :=
    IsCoprime.pow_left ((Nat.Prime.coprime_iff_not_dvd hp).mpr hb).isCoprime
  exact hcop.dvd_of_dvd_mul_right ⟨a, h2⟩

-- ============================================================================
-- Section 1: Harmonic sums H_k and partial harmonic sums h(m), h2(m)
-- ============================================================================

def harmH (p k : ℕ) : ℚ := ∑ j ∈ Ico 1 p, (1 : ℚ) / ((j : ℚ) ^ k)
def harmh (m : ℕ) : ℚ := ∑ j ∈ Icc 1 m, (1 : ℚ) / (j : ℚ)
def harmh2 (m : ℕ) : ℚ := ∑ j ∈ Icc 1 m, (1 : ℚ) / ((j : ℚ) ^ 2)

lemma inv_lt_p_pDiv0 {p j : ℕ} (hp : p.Prime) (hj1 : 1 ≤ j) (hj2 : j < p) :
    pDiv p 0 ((1 : ℚ) / (j : ℚ)) := by
  have hnd : ¬ p ∣ j := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  exact ⟨1, j, hnd, by simp⟩

lemma inv_pow_lt_p_pDiv0 {p j k : ℕ} (hp : p.Prime) (hj1 : 1 ≤ j) (hj2 : j < p) :
    pDiv p 0 ((1 : ℚ) / ((j : ℚ) ^ k)) := by
  have h := pDiv_pow (n := k) hp (inv_lt_p_pDiv0 hp hj1 hj2)
  simpa [div_pow, one_pow] using h

lemma harmh_pDiv0 {p m : ℕ} (hp : p.Prime) (hm : m < p) : pDiv p 0 (harmh m) := by
  apply pDiv_sum hp; intro j hj
  exact inv_lt_p_pDiv0 hp (mem_Icc.mp hj).1 (by have := (mem_Icc.mp hj).2; omega)

lemma harmh2_pDiv0 {p m : ℕ} (hp : p.Prime) (hm : m < p) : pDiv p 0 (harmh2 m) := by
  apply pDiv_sum hp; intro j hj
  exact inv_pow_lt_p_pDiv0 hp (mem_Icc.mp hj).1 (by have := (mem_Icc.mp hj).2; omega)

lemma harmH_pDiv0 {p k : ℕ} (hp : p.Prime) : pDiv p 0 (harmH p k) := by
  apply pDiv_sum hp; intro j hj
  exact inv_pow_lt_p_pDiv0 hp (mem_Ico.mp hj).1 (mem_Ico.mp hj).2

-- Generic ZMod p vanishing for ∑_{j=1}^{p-1} j^(-k) when p ∤ (2^k - 1) and p ∤ 2!
lemma zmod_inv_pow_sum_zero (p k : ℕ) (hp : p.Prime) (h2 : ¬ p ∣ 2) (h2k : ¬ p ∣ (2 ^ k - 1)) :
    ∑ j ∈ Ico 1 p, ((j : ZMod p)⁻¹) ^ k = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h; exact h2 ((ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h))
  have h2kne : ((2 : ZMod p) ^ k - 1) ≠ 0 := by
    intro h
    have h1 : ((2 ^ k - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub (Nat.one_le_pow k 2 (by norm_num))]; push_cast; exact h
    exact h2k ((ZMod.natCast_eq_zero_iff _ p).mp h1)
  have hfull : ∑ j ∈ Ico 1 p, ((j : ZMod p)⁻¹) ^ k = ∑ x : ZMod p, (x⁻¹) ^ k := by
    have hrange : ∑ u ∈ range p, ((u : ZMod p)⁻¹) ^ k = ∑ x : ZMod p, (x⁻¹) ^ k := by
      refine Finset.sum_bij (fun u _ => (u : ZMod p)) ?_ ?_ ?_ ?_
      · intro _ _; exact mem_univ _
      · intro u₁ hu₁ u₂ hu₂ heq
        have hv := congrArg ZMod.val heq
        rw [ZMod.val_natCast_of_lt (mem_range.mp hu₁),
            ZMod.val_natCast_of_lt (mem_range.mp hu₂)] at hv
        exact hv
      · intro x _
        exact ⟨x.val, mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
      · intro _ _; rfl
    rw [← hrange, show range p = insert 0 (Ico 1 p) by ext x; simp; have := hp.pos; omega, sum_insert (by simp)]
    cases k with
    | zero => exfalso; exact h2k (by simp)
    | succ k => simp
  rw [hfull]
  have hbij : ∑ x : ZMod p, (((2 : ZMod p) * x)⁻¹) ^ k = ∑ x : ZMod p, (x⁻¹) ^ k :=
    Fintype.sum_equiv (Equiv.mulLeft₀ (2 : ZMod p) h2ne) _ _ (fun _ => rfl)
  have hmul : ((2 : ZMod p)⁻¹) ^ k * ∑ x : ZMod p, (x⁻¹) ^ k = ∑ x : ZMod p, (x⁻¹) ^ k := by
    rw [mul_sum]
    convert hbij using 2 with x
    rw [mul_inv, mul_pow]
  have hmul2 : (2 : ZMod p) ^ k * (((2 : ZMod p)⁻¹) ^ k * ∑ x : ZMod p, (x⁻¹) ^ k) =
      (2 : ZMod p) ^ k * ∑ x : ZMod p, (x⁻¹) ^ k := congrArg ((2 : ZMod p) ^ k * ·) hmul
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ h2ne, one_pow, one_mul] at hmul2
  have hsub : ((2 : ZMod p) ^ k - 1) * ∑ x : ZMod p, (x⁻¹) ^ k = 0 := by
    rw [sub_mul, one_mul, ← hmul2, sub_self]
  exact (mul_eq_zero.mp hsub).resolve_left h2kne

lemma harmH_pDiv_one (p k : ℕ) (hp : p.Prime) (h2 : ¬ p ∣ 2) (h2k : ¬ p ∣ (2 ^ k - 1)) :
    pDiv p 1 (harmH p k) := by
  set F : ℕ := (p - 1).factorial
  have hF_ndvd : ¬ p ∣ F := by
    have haux : ∀ m, m < p → ¬ p ∣ m.factorial := by
      intro m
      induction m with
      | zero => intro _; exact hp.not_dvd_one
      | succ m ih =>
        intro hm hdiv
        rw [Nat.factorial_succ] at hdiv
        rcases hp.dvd_mul.mp hdiv with h1 | h2
        · have := Nat.le_of_dvd (by omega) h1; omega
        · exact ih (by omega) h2
    exact haux (p - 1) (by have := hp.pos; omega)
  have hF0 : (F : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hj_dvd : ∀ j ∈ Ico 1 p, j ∣ F := fun j hj =>
    Nat.dvd_factorial (mem_Ico.mp hj).1 (by have := (mem_Ico.mp hj).2; omega)
  set A : ℕ := ∑ j ∈ Ico 1 p, (F / j) ^ k
  have hsum_eq : harmH p k = (A : ℚ) / ((F ^ k : ℕ) : ℚ) := by
    unfold harmH
    rw [Nat.cast_sum, sum_div]
    apply sum_congr rfl; intro j hj
    have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (mem_Ico.mp hj).1; omega)
    have hq : ((F / j : ℕ) : ℚ) = (F : ℚ) / (j : ℚ) := by
      have hm : ((F / j : ℕ) : ℚ) * (j : ℚ) = (F : ℚ) := by
        have := congrArg (Nat.cast (R := ℚ)) (Nat.div_mul_cancel (hj_dvd j hj))
        simpa using this
      field_simp [hj0]; linarith
    push_cast; rw [hq, div_pow]; field_simp [hF0, hj0]
  have hA_dvd : p ∣ A := by
    rw [← ZMod.natCast_eq_zero_iff]
    have : Fact p.Prime := ⟨hp⟩
    have hA_cast : (A : ZMod p) = (F : ZMod p) ^ k * ∑ j ∈ Ico 1 p, ((j : ZMod p)⁻¹) ^ k := by
      rw [mul_sum]; dsimp only [A]; push_cast
      apply sum_congr rfl; intro j hj
      have hj1 := (mem_Ico.mp hj).1
      have hj2 := (mem_Ico.mp hj).2
      have hj_ne : (j : ZMod p) ≠ 0 := fun h => by
        have := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff j p).mp h); omega
      have hmulZ : ((F / j : ℕ) : ZMod p) * (j : ZMod p) = (F : ZMod p) := by
        have := congrArg (Nat.cast (R := ZMod p)) (Nat.div_mul_cancel (hj_dvd j hj))
        simpa using this
      have hq : ((F / j : ℕ) : ZMod p) = (F : ZMod p) * (j : ZMod p)⁻¹ := by
        calc ((F / j : ℕ) : ZMod p) = ((F / j : ℕ) : ZMod p) * (j : ZMod p) * (j : ZMod p)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ hj_ne, mul_one]
          _ = (F : ZMod p) * (j : ZMod p)⁻¹ := by rw [hmulZ]
      rw [hq, mul_pow]
    rw [hA_cast, zmod_inv_pow_sum_zero p k hp h2 h2k, mul_zero]
  rw [hsum_eq]
  rcases hA_dvd with ⟨c, hc⟩
  have hFk_ndvd : ¬ p ∣ F ^ k := fun h => hF_ndvd (hp.dvd_of_dvd_pow h)
  refine ⟨c, F ^ k, hFk_ndvd, ?_⟩
  rw [hc]; push_cast; ring

lemma harmH2_pDiv_one (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : pDiv p 1 (harmH p 2) :=
  harmH_pDiv_one p 2 hp
    (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)

lemma harmH4_pDiv_one (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : pDiv p 1 (harmH p 4) := by
  apply harmH_pDiv_one p 4 hp
    (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  intro h
  -- 2^4 - 1 = 15 = 3 * 5; prime p ≥ 7 cannot divide 15
  have h15 : p ∣ 3 * 5 := by simpa using h
  rcases hp.dvd_mul.mp h15 with h3 | h5
  · have := Nat.le_of_dvd (by norm_num) h3; omega
  · have := Nat.le_of_dvd (by norm_num) h5; omega

-- Exact rational identity: 2 * H_1 + p * H_2 + p^2 * H_3 + p^3 * H_4 = p^4 * ∑ 1/(j^4 * (p-j))
lemma harmH_exact_rel (p : ℕ) :
    2 * harmH p 1 + (p : ℚ) * harmH p 2 + (p : ℚ) ^ 2 * harmH p 3 + (p : ℚ) ^ 3 * harmH p 4 =
      (p : ℚ) ^ 4 * ∑ j ∈ Ico 1 p, (1 : ℚ) / (((j : ℚ) ^ 4) * ((p - j : ℕ) : ℚ)) := by
  have hrev : harmH p 1 = ∑ j ∈ Ico 1 p, (1 : ℚ) / ((p - j : ℕ) : ℚ) := by
    unfold harmH
    refine Finset.sum_bij (fun j _ => p - j) ?_ ?_ ?_ ?_
    · intro j hj; simp only [mem_Ico] at hj ⊢; omega
    · intro j₁ hj₁ j₂ hj₂ h; simp only [mem_Ico] at hj₁ hj₂; omega
    · intro v hv; exact ⟨p - v, by simp only [mem_Ico] at hv ⊢; omega, by simp only [mem_Ico] at hv; omega⟩
    · intro j hj; simp only [pow_one]; rw [Nat.sub_sub_self (by have := (mem_Ico.mp hj).2; omega)]
  have h2H : 2 * harmH p 1 =
      ∑ j ∈ Ico 1 p, ((1 : ℚ) / (j : ℚ) + (1 : ℚ) / ((p - j : ℕ) : ℚ)) := by
    rw [two_mul, sum_add_distrib]
    conv_lhs => rhs; rw [hrev]
    simp [harmH]
  rw [h2H]
  unfold harmH
  simp only [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl; intro j hj
  have hj1 := (mem_Ico.mp hj).1
  have hj2 := (mem_Ico.mp hj).2
  have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsub : ((p - j : ℕ) : ℚ) = (p : ℚ) - (j : ℚ) := Nat.cast_sub (by omega)
  have hpj0 : (p : ℚ) - (j : ℚ) ≠ 0 := by
    rw [← hsub]; exact Nat.cast_ne_zero.mpr (by omega)
  rw [hsub]
  field_simp [hj0, hpj0]
  ring

-- Exact rational identity for H_3: 2 * H_3 + 3 * p * H_4 = p^2 * ∑ (6*j^2 - 8*p*j + 3*p^2) / (j^4 * (p-j)^3)
lemma harmH3_pDiv_two (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : pDiv p 2 (harmH p 3) := by
  have hrev : harmH p 3 = ∑ j ∈ Ico 1 p, (1 : ℚ) / (((p - j : ℕ) : ℚ) ^ 3) := by
    unfold harmH
    refine Finset.sum_bij (fun j _ => p - j) ?_ ?_ ?_ ?_
    · intro j hj; simp only [mem_Ico] at hj ⊢; omega
    · intro j₁ hj₁ j₂ hj₂ h; simp only [mem_Ico] at hj₁ hj₂; omega
    · intro v hv; exact ⟨p - v, by simp only [mem_Ico] at hv ⊢; omega, by simp only [mem_Ico] at hv; omega⟩
    · intro j hj; rw [Nat.sub_sub_self (by have := (mem_Ico.mp hj).2; omega)]
  have hid : 2 * harmH p 3 + 3 * (p : ℚ) * harmH p 4 =
      (p : ℚ) ^ 2 * ∑ j ∈ Ico 1 p,
        ((6 * (j : ℚ) ^ 2 - 8 * (p : ℚ) * (j : ℚ) + 3 * (p : ℚ) ^ 2) /
          ((j : ℚ) ^ 4 * ((p - j : ℕ) : ℚ) ^ 3)) := by
    have h2 : 2 * harmH p 3 =
        ∑ j ∈ Ico 1 p, ((1 : ℚ) / ((j : ℚ) ^ 3) + (1 : ℚ) / (((p - j : ℕ) : ℚ) ^ 3)) := by
      rw [two_mul, sum_add_distrib]
      conv_lhs => rhs; rw [hrev]
      rfl
    rw [h2]
    unfold harmH
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro j hj
    have hj1 := (mem_Ico.mp hj).1
    have hj2 := (mem_Ico.mp hj).2
    have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hsub : ((p - j : ℕ) : ℚ) = (p : ℚ) - (j : ℚ) := Nat.cast_sub (by omega)
    have hpj0 : (p : ℚ) - (j : ℚ) ≠ 0 := by rw [← hsub]; exact Nat.cast_ne_zero.mpr (by omega)
    rw [hsub]
    field_simp [hj0, hpj0]
    ring
  have hrhs : pDiv p 2 (2 * harmH p 3 + 3 * (p : ℚ) * harmH p 4) := by
    rw [hid]
    have hsum0 : pDiv p 0 (∑ j ∈ Ico 1 p,
        ((6 * (j : ℚ) ^ 2 - 8 * (p : ℚ) * (j : ℚ) + 3 * (p : ℚ) ^ 2) /
          ((j : ℚ) ^ 4 * ((p - j : ℕ) : ℚ) ^ 3))) := by
      apply pDiv_sum hp; intro j hj
      have hj1 := (mem_Ico.mp hj).1
      have hj2 := (mem_Ico.mp hj).2
      have h1 := inv_pow_lt_p_pDiv0 (k := 4) hp hj1 hj2
      have h2 := inv_pow_lt_p_pDiv0 (k := 3) hp (by omega : 1 ≤ p - j) (by omega : p - j < p)
      have hnum : pDiv p 0 (6 * (j : ℚ) ^ 2 - 8 * (p : ℚ) * (j : ℚ) + 3 * (p : ℚ) ^ 2) := by
        convert pDiv_int_zero hp (6 * (j : ℤ) ^ 2 - 8 * (p : ℤ) * (j : ℤ) + 3 * (p : ℤ) ^ 2)
        push_cast; ring
      have hrew : (6 * (j : ℚ) ^ 2 - 8 * (p : ℚ) * (j : ℚ) + 3 * (p : ℚ) ^ 2) /
            ((j : ℚ) ^ 4 * ((p - j : ℕ) : ℚ) ^ 3) =
          (6 * (j : ℚ) ^ 2 - 8 * (p : ℚ) * (j : ℚ) + 3 * (p : ℚ) ^ 2) *
            ((1 : ℚ) / (j : ℚ) ^ 4) * ((1 : ℚ) / ((p - j : ℕ) : ℚ) ^ 3) := by ring
      rw [hrew]
      simpa using pDiv_mul hp (pDiv_mul hp hnum h1) h2
    simpa using pDiv_mul hp (pDiv_p_pow p 2 hp) hsum0
  have h3pH4 : pDiv p 2 (3 * (p : ℚ) * harmH p 4) := by
    have h1 := pDiv_mul hp (pDiv_nat_zero hp 3) (pDiv_p_one p hp)
    simpa [mul_assoc] using pDiv_mul hp h1 (harmH4_pDiv_one p hp hp7)
  have h2H3 : pDiv p 2 ((2 : ℕ) * harmH p 3) := by
    have hrew : ((2 : ℕ) : ℚ) * harmH p 3 =
        (2 * harmH p 3 + 3 * (p : ℚ) * harmH p 4) - 3 * (p : ℚ) * harmH p 4 := by
      push_cast; ring
    rw [hrew]
    exact pDiv_sub hp hrhs h3pH4
  exact pDiv_cancel_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega) h2H3

lemma harmH1_H2_pDiv_five (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    pDiv p 5 (2 * (p : ℚ) * harmH p 1 + (p : ℚ) ^ 2 * harmH p 2) := by
  have hid := congrArg ((p : ℚ) * ·) (harmH_exact_rel p)
  have hrhs : pDiv p 5 ((p : ℚ) * ((p : ℚ) ^ 4 *
      ∑ j ∈ Ico 1 p, (1 : ℚ) / (((j : ℚ) ^ 4) * ((p - j : ℕ) : ℚ)))) := by
    have hsum0 : pDiv p 0 (∑ j ∈ Ico 1 p, (1 : ℚ) / (((j : ℚ) ^ 4) * ((p - j : ℕ) : ℚ))) := by
      apply pDiv_sum hp; intro j hj
      have hj1 := (mem_Ico.mp hj).1
      have hj2 := (mem_Ico.mp hj).2
      have h1 := inv_pow_lt_p_pDiv0 (k := 4) hp hj1 hj2
      have h2 := inv_lt_p_pDiv0 hp (by omega : 1 ≤ p - j) (by omega : p - j < p)
      have hrew : (1 : ℚ) / (((j : ℚ) ^ 4) * ((p - j : ℕ) : ℚ)) =
          ((1 : ℚ) / (j : ℚ) ^ 4) * ((1 : ℚ) / ((p - j : ℕ) : ℚ)) := by ring
      rw [hrew]; simpa using pDiv_mul hp h1 h2
    have hp5 : pDiv p 5 ((p : ℚ) ^ 5) := pDiv_p_pow p 5 hp
    have hrew : (p : ℚ) * ((p : ℚ) ^ 4 *
        ∑ j ∈ Ico 1 p, (1 : ℚ) / (((j : ℚ) ^ 4) * ((p - j : ℕ) : ℚ))) =
        (p : ℚ) ^ 5 * ∑ j ∈ Ico 1 p, (1 : ℚ) / (((j : ℚ) ^ 4) * ((p - j : ℕ) : ℚ)) := by ring
    rw [hrew]; simpa using pDiv_mul hp hp5 hsum0
  rw [← hid] at hrhs
  have h3 : pDiv p 5 ((p : ℚ) ^ 3 * harmH p 3) :=
    pDiv_mul hp (pDiv_p_pow p 3 hp) (harmH3_pDiv_two p hp hp7)
  have h4 : pDiv p 5 ((p : ℚ) ^ 4 * harmH p 4) :=
    pDiv_mul hp (pDiv_p_pow p 4 hp) (harmH4_pDiv_one p hp hp7)
  have hrew : 2 * (p : ℚ) * harmH p 1 + (p : ℚ) ^ 2 * harmH p 2 =
      (p : ℚ) * (2 * harmH p 1 + (p : ℚ) * harmH p 2 +
        (p : ℚ) ^ 2 * harmH p 3 + (p : ℚ) ^ 3 * harmH p 4) -
      (p : ℚ) ^ 3 * harmH p 3 - (p : ℚ) ^ 4 * harmH p 4 := by ring
  rw [hrew]
  exact pDiv_sub hp (pDiv_sub hp hrhs h3) h4

lemma harmH1_pDiv_two (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : pDiv p 2 (harmH p 1) := by
  have h5 := harmH1_H2_pDiv_five p hp hp7
  have h3 : pDiv p 3 ((p : ℚ) ^ 2 * harmH p 2) :=
    pDiv_mul hp (pDiv_p_pow p 2 hp) (harmH2_pDiv_one p hp (by omega))
  have h2pH1 : pDiv p 3 ((p : ℚ) ^ 1 * (2 * harmH p 1)) := by
    have hrew : (p : ℚ) ^ 1 * (2 * harmH p 1) =
        (2 * (p : ℚ) * harmH p 1 + (p : ℚ) ^ 2 * harmH p 2) - (p : ℚ) ^ 2 * harmH p 2 := by ring
    rw [hrew]
    exact pDiv_sub hp (pDiv_mono (by omega) h5) h3
  have h2H1 : pDiv p 2 ((2 : ℕ) * harmH p 1) := by
    have := pDiv_cancel_p_pow (k := 2) (r := 1) hp h2pH1
    simpa using this
  exact pDiv_cancel_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega) h2H1

-- ============================================================================
-- Section 2: Elementary symmetric expansion of ∏_{j=1}^m (1 + c / j)
-- ============================================================================

-- Helper: elementary symmetric polynomial e_k of a finite set s with function f : ι → ℚ
-- Extract directly as coeff k of ∏_{j ∈ s} (1 + C (f j) * X) in PowerSeries ℚ!
noncomputable def prodPS {ι : Type*} (s : Finset ι) (f : ι → ℚ) : PowerSeries ℚ :=
  ∏ j ∈ s, (1 + PowerSeries.C (f j) * PowerSeries.X)

-- Newton's identities for e_0, e_1, e_2, e_3, e_4!
-- Even simpler: direct induction on s proves e_1, e_2, e_3, e_4 formulas in terms of p_1, p_2, p_3, p_4!
lemma prodPS_coeff_small {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    let e := fun k => PowerSeries.coeff k (prodPS s f)
    let p1 := ∑ j ∈ s, f j
    let p2 := ∑ j ∈ s, (f j) ^ 2
    let p3 := ∑ j ∈ s, (f j) ^ 3
    let p4 := ∑ j ∈ s, (f j) ^ 4
    e 0 = 1 ∧
    e 1 = p1 ∧
    2 * e 2 = p1 ^ 2 - p2 ∧
    6 * e 3 = p1 ^ 3 - 3 * p1 * p2 + 2 * p3 ∧
    24 * e 4 = p1 ^ 4 - 6 * p1 ^ 2 * p2 + 3 * p2 ^ 2 + 8 * p1 * p3 - 6 * p4 := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp [prodPS]
  | @insert x s hx ih =>
    rcases ih with ⟨h0, h1, h2, h3, h4⟩
    have hstep : ∀ k : ℕ, PowerSeries.coeff (k + 1) (prodPS (insert x s) f) =
        PowerSeries.coeff (k + 1) (prodPS s f) + f x * PowerSeries.coeff k (prodPS s f) := by
      intro k
      unfold prodPS
      rw [prod_insert hx, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => PowerSeries.coeff i (1 + PowerSeries.C (f x) * PowerSeries.X) *
              PowerSeries.coeff j (∏ y ∈ s, (1 + PowerSeries.C (f y) * PowerSeries.X))) (k + 1)]
      have hterm : ∀ i ∈ range (k + 2),
          PowerSeries.coeff i (1 + PowerSeries.C (f x) * PowerSeries.X) *
            PowerSeries.coeff (k + 1 - i) (∏ j ∈ s, (1 + PowerSeries.C (f j) * PowerSeries.X)) =
          if i = 0 then PowerSeries.coeff (k + 1) (prodPS s f)
          else if i = 1 then f x * PowerSeries.coeff k (prodPS s f)
          else 0 := by
        intro i _
        rcases i with _ | _ | i
        · simp [prodPS]
        · simp [prodPS, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
        · simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
      rw [sum_congr rfl hterm, sum_range_succ', sum_range_succ']
      simp [prodPS, add_comm]
    have h0' : PowerSeries.coeff 0 (prodPS (insert x s) f) = 1 := by
      unfold prodPS; rw [prod_insert hx]
      simp [PowerSeries.coeff_zero_eq_constantCoeff]
    have h1' := hstep 0
    have h2' := hstep 1
    have h3' := hstep 2
    have h4' := hstep 3
    simp only [sum_insert hx]
    dsimp only at h0 h1 h2 h3 h4 ⊢
    refine ⟨h0', ?_, ?_, ?_, ?_⟩
    · rw [h1', h0, h1]; ring
    · rw [h2']; linear_combination h2 + 2 * f x * h1
    · rw [h3']; linear_combination h3 + 3 * f x * h2
    · rw [h4']; linear_combination h4 + 4 * f x * h3

lemma prodPS_poly_natDegree_le {ι : Type*} (s : Finset ι) (g : ι → ℚ) :
    (∏ j ∈ s, (1 + Polynomial.C (g j) * Polynomial.X)).natDegree ≤ s.card := by
  calc (∏ j ∈ s, (1 + Polynomial.C (g j) * Polynomial.X)).natDegree
      ≤ ∑ j ∈ s, (1 + Polynomial.C (g j) * Polynomial.X).natDegree :=
        Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _j ∈ s, 1 := by
        apply sum_le_sum; intro j _
        calc (1 + Polynomial.C (g j) * Polynomial.X).natDegree
            ≤ max (1 : Polynomial ℚ).natDegree (Polynomial.C (g j) * Polynomial.X).natDegree :=
              Polynomial.natDegree_add_le _ _
          _ ≤ 1 := by
              simp only [Polynomial.natDegree_one, max_le_iff, zero_le, true_and]
              exact le_trans Polynomial.natDegree_mul_le (by simp)
    _ = s.card := by simp

lemma prodPS_scale {ι : Type*} (s : Finset ι) (f : ι → ℚ) (c : ℚ) :
    ∀ k : ℕ, PowerSeries.coeff k (prodPS s (fun j => c * f j)) =
      c ^ k * PowerSeries.coeff k (prodPS s f) := by
  classical
  induction s using Finset.induction with
  | empty => intro k; cases k <;> simp [prodPS]
  | @insert x s hx ih =>
    intro k
    unfold prodPS
    rw [prod_insert hx, prod_insert hx, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i (1 + PowerSeries.C (c * f x) * PowerSeries.X) *
            PowerSeries.coeff j (∏ y ∈ s, (1 + PowerSeries.C (c * f y) * PowerSeries.X))) k,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i (1 + PowerSeries.C (f x) * PowerSeries.X) *
            PowerSeries.coeff j (∏ y ∈ s, (1 + PowerSeries.C (f y) * PowerSeries.X))) k,
        mul_sum]
    apply sum_congr rfl; intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have ihi := ih (k - i)
    unfold prodPS at ihi
    rcases i with _ | _ | i
    · have h0 := ih k; unfold prodPS at h0
      simp only [Nat.sub_zero, map_add, PowerSeries.coeff_one, if_true,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_X, show (0 : ℕ) ≠ 1 by decide, if_false,
        mul_zero, add_zero, one_mul]
      exact h0
    · have h1 := ih (k - 1); unfold prodPS at h1
      have he : k = (k - 1) + 1 := by omega
      have hpow : c ^ k = c ^ (k - 1) * c := by conv_lhs => rw [he]; rw [pow_succ]
      have hsub : k - (0 + 1) = k - 1 := by omega
      rw [hsub]
      simp only [map_add, PowerSeries.coeff_one, show (1 : ℕ) ≠ 0 by decide, if_false,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_X, if_true, mul_one, zero_add]
      rw [h1, hpow]
      ring
    · simp

lemma prodPS_coeff_pDiv0 {ι : Type*} {p : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ j ∈ s, pDiv p 0 (f j)) :
    ∀ k : ℕ, pDiv p 0 (PowerSeries.coeff k (prodPS s f)) := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro k; cases k
    · simpa [prodPS] using pDiv_nat_zero hp 1
    · simp [prodPS, pDiv_zero p 0 hp]
  | @insert x s hx ih =>
    intro k
    unfold prodPS
    rw [prod_insert hx, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i (1 + PowerSeries.C (f x) * PowerSeries.X) *
            PowerSeries.coeff j (∏ y ∈ s, (1 + PowerSeries.C (f y) * PowerSeries.X))) k]
    apply pDiv_sum hp; intro i _
    rcases i with _ | _ | i
    · simpa [prodPS, PowerSeries.coeff_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_X] using
        ih (fun y hy => hf y (mem_insert_of_mem hy)) k
    · simpa [prodPS, PowerSeries.coeff_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_X] using
        pDiv_mul hp (hf x (mem_insert_self x s))
          (ih (fun y hy => hf y (mem_insert_of_mem hy)) (k - 1))
    · simp [pDiv_zero p 0 hp]

lemma coe_prod_one_add_X_p4 {ι : Type*} (s : Finset ι) (g : ι → ℚ) :
    ((∏ j ∈ s, (1 + Polynomial.C (g j) * Polynomial.X) : Polynomial ℚ) : PowerSeries ℚ) =
      prodPS s g := by
  classical
  unfold prodPS
  induction s using Finset.induction with
  | empty => simp [Polynomial.coe_one]
  | @insert x s hx ih =>
    rw [prod_insert hx, prod_insert hx, Polynomial.coe_mul, ih,
        Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X]

lemma prod_one_add_trunc2 {ι : Type*} {p : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → ℚ) (c : ℚ)
    (hc : pDiv p 1 c) (hf : ∀ j ∈ s, pDiv p 0 (f j)) :
    pDiv p 3 ((∏ j ∈ s, (1 + c * f j)) -
      (1 + c * (∑ j ∈ s, f j) + c ^ 2 * PowerSeries.coeff 2 (prodPS s f))) := by
  have heval : ∏ j ∈ s, (1 + c * f j) =
      ∑ k ∈ range (max (s.card + 1) 3), PowerSeries.coeff k (prodPS s (fun j => c * f j)) := by
    set P : Polynomial ℚ := ∏ j ∈ s, (1 + Polynomial.C (c * f j) * Polynomial.X)
    have hP_ps : (P : PowerSeries ℚ) = prodPS s (fun j => c * f j) :=
      coe_prod_one_add_X_p4 s (fun j => c * f j)
    have hdeg : P.natDegree ≤ s.card := prodPS_poly_natDegree_le s (fun j => c * f j)
    have h1 : P.eval 1 = ∏ j ∈ s, (1 + c * f j) := by simp [P, Polynomial.eval_prod]
    rw [← h1, Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hdeg (by omega : s.card < max (s.card + 1) 3))]
    apply sum_congr rfl; intro k _
    rw [one_pow, mul_one, ← Polynomial.coeff_coe, hP_ps]
  rw [heval]
  have hsplit : range (max (s.card + 1) 3) = {0, 1, 2} ∪ Ico 3 (max (s.card + 1) 3) := by
    ext k; simp only [mem_range, mem_union, mem_insert, mem_singleton, mem_Ico]; omega
  rw [hsplit, sum_union (by simp [Finset.disjoint_left])]
  have h012 : ∑ k ∈ ({0, 1, 2} : Finset ℕ), PowerSeries.coeff k (prodPS s (fun j => c * f j)) =
      1 + c * (∑ j ∈ s, f j) + c ^ 2 * PowerSeries.coeff 2 (prodPS s f) := by
    have hsm := prodPS_coeff_small s f
    dsimp only at hsm
    simp [prodPS_scale, hsm.1, hsm.2.1]; ring
  rw [h012, add_sub_cancel_left]
  apply pDiv_sum hp; intro k hk
  rw [prodPS_scale]
  have hk3 : 3 ≤ k := (mem_Ico.mp hk).1
  have hck : pDiv p k (c ^ k) := by simpa using pDiv_pow (n := k) hp hc
  exact pDiv_mono hk3 (by simpa using pDiv_mul hp hck (prodPS_coeff_pDiv0 hp s f hf k))

lemma prod_one_add_trunc4 {ι : Type*} {p : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → ℚ) (c : ℚ)
    (hc : pDiv p 1 c) (hf : ∀ j ∈ s, pDiv p 0 (f j)) :
    pDiv p 5 ((∏ j ∈ s, (1 + c * f j)) -
      (1 + c * PowerSeries.coeff 1 (prodPS s f) +
       c ^ 2 * PowerSeries.coeff 2 (prodPS s f) +
       c ^ 3 * PowerSeries.coeff 3 (prodPS s f) +
       c ^ 4 * PowerSeries.coeff 4 (prodPS s f))) := by
  have heval : ∏ j ∈ s, (1 + c * f j) =
      ∑ k ∈ range (max (s.card + 1) 5), PowerSeries.coeff k (prodPS s (fun j => c * f j)) := by
    set P : Polynomial ℚ := ∏ j ∈ s, (1 + Polynomial.C (c * f j) * Polynomial.X)
    have hP_ps : (P : PowerSeries ℚ) = prodPS s (fun j => c * f j) :=
      coe_prod_one_add_X_p4 s (fun j => c * f j)
    have hdeg : P.natDegree ≤ s.card := prodPS_poly_natDegree_le s (fun j => c * f j)
    have h1 : P.eval 1 = ∏ j ∈ s, (1 + c * f j) := by simp [P, Polynomial.eval_prod]
    rw [← h1, Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hdeg (by omega : s.card < max (s.card + 1) 5))]
    apply sum_congr rfl; intro k _
    rw [one_pow, mul_one, ← Polynomial.coeff_coe, hP_ps]
  rw [heval]
  have hsplit : range (max (s.card + 1) 5) = {0, 1, 2, 3, 4} ∪ Ico 5 (max (s.card + 1) 5) := by
    ext k; simp only [mem_range, mem_union, mem_insert, mem_singleton, mem_Ico]; omega
  rw [hsplit, sum_union (by simp [Finset.disjoint_left])]
  have h04 : ∑ k ∈ ({0, 1, 2, 3, 4} : Finset ℕ), PowerSeries.coeff k (prodPS s (fun j => c * f j)) =
      1 + c * PowerSeries.coeff 1 (prodPS s f) +
       c ^ 2 * PowerSeries.coeff 2 (prodPS s f) +
       c ^ 3 * PowerSeries.coeff 3 (prodPS s f) +
       c ^ 4 * PowerSeries.coeff 4 (prodPS s f) := by
    have hsm := prodPS_coeff_small s f
    dsimp only at hsm
    simp [prodPS_scale, hsm.1]; ring
  rw [h04, add_sub_cancel_left]
  apply pDiv_sum hp; intro k hk
  rw [prodPS_scale]
  have hk5 : 5 ≤ k := (mem_Ico.mp hk).1
  have hck : pDiv p k (c ^ k) := by simpa using pDiv_pow (n := k) hp hc
  exact pDiv_mono hk5 (by simpa using pDiv_mul hp hck (prodPS_coeff_pDiv0 hp s f hf k))

-- Helper: C(A + m, m) = ∏_{j=1}^m (1 + A / j)
lemma choose_add_eq_prod (A m : ℕ) :
    ((A + m).choose m : ℚ) = ∏ j ∈ Icc 1 m, (1 + (A : ℚ) * ((1 : ℚ) / (j : ℚ))) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hIcc : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    rw [hIcc, prod_insert (by simp), ← ih]
    have hrec := Nat.add_one_mul_choose_eq (A + m) m
    have hQ : ((A + (m + 1) : ℕ) : ℚ) * ((A + m).choose m : ℚ) =
        ((A + (m + 1)).choose (m + 1) : ℚ) * ((m + 1 : ℕ) : ℚ) := by
      have e1 : A + (m + 1) = A + m + 1 := by omega
      rw [e1]; exact_mod_cast hrec
    have hm0 : ((m + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hm0] at hQ ⊢
    push_cast at hQ ⊢
    linarith

-- Helper: C(A - 1, m) = (-1)^m * ∏_{j=1}^m (1 - A / j)  (for m < A)
lemma choose_sub_one_eq_prod (A m : ℕ) (hm : m < A) :
    ((A - 1).choose m : ℚ) =
      (-1 : ℚ) ^ m * ∏ j ∈ Icc 1 m, (1 + (-(A : ℚ)) * ((1 : ℚ) / (j : ℚ))) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hIcc : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    rw [hIcc, prod_insert (by simp), pow_succ']
    have hih := ih (by omega)
    have hrec := Nat.choose_succ_right_eq (A - 1) m
    have hsub : A - 1 - m = A - (m + 1) := by omega
    rw [hsub] at hrec
    have hQ : ((A - 1).choose (m + 1) : ℚ) * ((m + 1 : ℕ) : ℚ) =
        ((A - 1).choose m : ℚ) * ((A - (m + 1) : ℕ) : ℚ) := by exact_mod_cast hrec
    have hsubQ : ((A - (m + 1) : ℕ) : ℚ) = (A : ℚ) - ((m + 1 : ℕ) : ℚ) := Nat.cast_sub (by omega)
    rw [hsubQ] at hQ
    have hm0 : ((m + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hrew : (-1 : ℚ) * (-1 : ℚ) ^ m * ((1 + -(A : ℚ) * (1 / ((m + 1 : ℕ) : ℚ))) *
          ∏ j ∈ Icc 1 m, (1 + -(A : ℚ) * (1 / (j : ℚ)))) =
        (-1 : ℚ) * (1 + -(A : ℚ) * (1 / ((m + 1 : ℕ) : ℚ))) *
          ((-1 : ℚ) ^ m * ∏ j ∈ Icc 1 m, (1 + -(A : ℚ) * (1 / (j : ℚ)))) := by ring
    rw [hrew, ← hih]
    field_simp [hm0] at hQ ⊢
    linarith

-- C(k*p - 1, p - 1) ≡ 1 + k*(k - 1)*p*H_1 (mod p^5) for p ≥ 7, k ≥ 1!
lemma choose_kp_sub_one_pDiv5 (p k : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hk : 1 ≤ k) :
    pDiv p 5 (((k * p - 1).choose (p - 1) : ℚ) -
      (1 + ((k * (k - 1) : ℕ) : ℚ) * (p : ℚ) * harmH p 1)) := by
  have hkp : k * p - 1 = (k - 1) * p + (p - 1) := by
    have : k * p = (k - 1) * p + p := by
      calc k * p = ((k - 1) + 1) * p := by rw [Nat.sub_add_cancel hk]
        _ = (k - 1) * p + p := by ring
    omega
  have hIcc_eq : Icc 1 (p - 1) = Ico 1 p := by
    ext j; simp only [mem_Icc, mem_Ico]; omega
  have hprod : ((k * p - 1).choose (p - 1) : ℚ) =
      ∏ j ∈ Ico 1 p, (1 + (((k - 1 : ℕ) : ℚ) * (p : ℚ)) * ((1 : ℚ) / (j : ℚ))) := by
    rw [hkp, choose_add_eq_prod, hIcc_eq]; push_cast; rfl
  rw [hprod]
  set c : ℚ := ((k - 1 : ℕ) : ℚ) * (p : ℚ)
  set f : ℕ → ℚ := fun j => (1 : ℚ) / (j : ℚ)
  have hc : pDiv p 1 c := by
    simpa [c] using pDiv_mul hp (pDiv_nat_zero hp (k - 1)) (pDiv_p_one p hp)
  have hf : ∀ j ∈ Ico 1 p, pDiv p 0 (f j) := fun j hj =>
    inv_lt_p_pDiv0 hp (mem_Ico.mp hj).1 (mem_Ico.mp hj).2
  have htrunc := prod_one_add_trunc4 hp (Ico 1 p) f c hc hf
  have hsm := prodPS_coeff_small (Ico 1 p) f
  dsimp only at hsm
  have hp1 : ∑ j ∈ Ico 1 p, f j = harmH p 1 := by simp [harmH, f]
  have hp2 : ∑ j ∈ Ico 1 p, (f j) ^ 2 = harmH p 2 := by simp [harmH, f]
  have hp3 : ∑ j ∈ Ico 1 p, (f j) ^ 3 = harmH p 3 := by simp [harmH, f]
  have hp4 : ∑ j ∈ Ico 1 p, (f j) ^ 4 = harmH p 4 := by simp [harmH, f]
  have hH1 := harmH1_pDiv_two p hp hp7
  have hH2 := harmH2_pDiv_one p hp (by omega)
  have hH3 := harmH3_pDiv_two p hp hp7
  have hH4 := harmH4_pDiv_one p hp hp7
  have h12 := harmH1_H2_pDiv_five p hp hp7
  have he2 : pDiv p 5 (c ^ 2 * PowerSeries.coeff 2 (prodPS (Ico 1 p) f) -
      (((k - 1 : ℕ) : ℚ) ^ 2) * (p : ℚ) * harmH p 1) := by
    have heq : PowerSeries.coeff 2 (prodPS (Ico 1 p) f) = (harmH p 1 ^ 2 - harmH p 2) / 2 := by
      have := hsm.2.2.1; rw [hp1, hp2] at this; linarith
    rw [heq]
    have hrew : c ^ 2 * ((harmH p 1 ^ 2 - harmH p 2) / 2) -
        ((k - 1 : ℕ) : ℚ) ^ 2 * (p : ℚ) * harmH p 1 =
        (((k - 1 : ℕ) : ℚ) ^ 2 * ((p : ℚ) ^ 2 * harmH p 1 ^ 2 -
          (2 * (p : ℚ) * harmH p 1 + (p : ℚ) ^ 2 * harmH p 2))) / (2 : ℕ) := by
      dsimp only [c]; push_cast; ring
    rw [hrew]
    apply pDiv_div_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    have hp2H12 : pDiv p 5 ((p : ℚ) ^ 2 * harmH p 1 ^ 2) := by
      have h6 := pDiv_mul hp (pDiv_p_pow p 2 hp) (pDiv_pow (n := 2) hp hH1)
      exact pDiv_mono (by omega) h6
    have hsub := pDiv_sub hp hp2H12 h12
    have hmul := pDiv_mul hp (pDiv_nat_zero hp ((k - 1) ^ 2)) hsub
    push_cast at hmul; simpa using hmul
  have he3 : pDiv p 5 (c ^ 3 * PowerSeries.coeff 3 (prodPS (Ico 1 p) f)) := by
    have heq : PowerSeries.coeff 3 (prodPS (Ico 1 p) f) =
        (harmH p 1 ^ 3 - 3 * harmH p 1 * harmH p 2 + 2 * harmH p 3) / (6 : ℕ) := by
      have := hsm.2.2.2.1; rw [hp1, hp2, hp3] at this; push_cast; linarith
    rw [heq, ← mul_div_assoc]
    apply pDiv_div_nat_unit hp (fun h => by
      have h6 : p ∣ 2 * 3 := by simpa using h
      rcases hp.dvd_mul.mp h6 with h2 | h3
      · have := Nat.le_of_dvd (by norm_num) h2; omega
      · have := Nat.le_of_dvd (by norm_num) h3; omega)
    have hc3 : pDiv p 3 (c ^ 3) := by simpa using pDiv_pow (n := 3) hp hc
    have ht1 : pDiv p 2 (harmH p 1 ^ 3) := pDiv_mono (by omega) (pDiv_pow (n := 3) hp hH1)
    have ht2 : pDiv p 2 (3 * harmH p 1 * harmH p 2) := by
      have h3 := pDiv_mul hp (pDiv_mul hp (pDiv_nat_zero hp 3) hH1) hH2
      exact pDiv_mono (by omega) h3
    have ht3 : pDiv p 2 (2 * harmH p 3) := by
      simpa using pDiv_mul hp (pDiv_nat_zero hp 2) hH3
    exact pDiv_mul hp hc3 (pDiv_add hp (pDiv_sub hp ht1 ht2) ht3)
  have he4 : pDiv p 5 (c ^ 4 * PowerSeries.coeff 4 (prodPS (Ico 1 p) f)) := by
    have heq : PowerSeries.coeff 4 (prodPS (Ico 1 p) f) =
        (harmH p 1 ^ 4 - 6 * harmH p 1 ^ 2 * harmH p 2 + 3 * harmH p 2 ^ 2 +
          8 * harmH p 1 * harmH p 3 - 6 * harmH p 4) / (24 : ℕ) := by
      have := hsm.2.2.2.2; rw [hp1, hp2, hp3, hp4] at this; push_cast; linarith
    rw [heq, ← mul_div_assoc]
    apply pDiv_div_nat_unit hp (fun h => by
      have h24 : p ∣ 8 * 3 := by simpa using h
      rcases hp.dvd_mul.mp h24 with h8 | h3
      · have h2 : p ∣ 2 ^ 3 := by simpa using h8
        have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
      · have := Nat.le_of_dvd (by norm_num) h3; omega)
    have hc4 : pDiv p 4 (c ^ 4) := by simpa using pDiv_pow (n := 4) hp hc
    have ht1 : pDiv p 1 (harmH p 1 ^ 4) := pDiv_mono (by omega) (pDiv_pow (n := 4) hp hH1)
    have ht2 : pDiv p 1 (6 * harmH p 1 ^ 2 * harmH p 2) :=
      pDiv_mono (by omega) (pDiv_mul hp (pDiv_mul hp (pDiv_nat_zero hp 6) (pDiv_pow (n := 2) hp hH1)) hH2)
    have ht3 : pDiv p 1 (3 * harmH p 2 ^ 2) :=
      pDiv_mono (by omega) (pDiv_mul hp (pDiv_nat_zero hp 3) (pDiv_pow (n := 2) hp hH2))
    have ht4 : pDiv p 1 (8 * harmH p 1 * harmH p 3) :=
      pDiv_mono (by omega) (pDiv_mul hp (pDiv_mul hp (pDiv_nat_zero hp 8) hH1) hH3)
    have ht5 : pDiv p 1 (6 * harmH p 4) := by simpa using pDiv_mul hp (pDiv_nat_zero hp 6) hH4
    exact pDiv_mul hp hc4 (pDiv_sub hp (pDiv_add hp (pDiv_add hp (pDiv_sub hp ht1 ht2) ht3) ht4) ht5)
  have hk_id : ((k * (k - 1) : ℕ) : ℚ) = ((k - 1 : ℕ) : ℚ) + ((k - 1 : ℕ) : ℚ) ^ 2 := by
    have : k * (k - 1) = (k - 1) + (k - 1) ^ 2 := by
      calc k * (k - 1) = ((k - 1) + 1) * (k - 1) := by rw [Nat.sub_add_cancel hk]
        _ = (k - 1) + (k - 1) ^ 2 := by ring
    exact_mod_cast this
  have hrew : (∏ j ∈ Ico 1 p, (1 + c * f j)) - (1 + ((k * (k - 1) : ℕ) : ℚ) * (p : ℚ) * harmH p 1) =
      ((∏ j ∈ Ico 1 p, (1 + c * f j)) -
        (1 + c * PowerSeries.coeff 1 (prodPS (Ico 1 p) f) +
         c ^ 2 * PowerSeries.coeff 2 (prodPS (Ico 1 p) f) +
         c ^ 3 * PowerSeries.coeff 3 (prodPS (Ico 1 p) f) +
         c ^ 4 * PowerSeries.coeff 4 (prodPS (Ico 1 p) f))) +
      (c ^ 2 * PowerSeries.coeff 2 (prodPS (Ico 1 p) f) -
        ((k - 1 : ℕ) : ℚ) ^ 2 * (p : ℚ) * harmH p 1) +
      c ^ 3 * PowerSeries.coeff 3 (prodPS (Ico 1 p) f) +
      c ^ 4 * PowerSeries.coeff 4 (prodPS (Ico 1 p) f) := by
    rw [hsm.2.1, hp1, hk_id]; dsimp only [c]; ring
  rw [hrew]
  exact pDiv_add hp (pDiv_add hp (pDiv_add hp htrunc he2) he3) he4

lemma choose_mp_sub_one_trunc2 (p m i : ℕ) (hp : p.Prime) (hm : 1 ≤ m)
    (hi1 : 1 ≤ i) (hi2 : i < p) :
    pDiv p 3 ((-1 : ℚ) ^ (i - 1) * ((m * p - 1).choose (i - 1) : ℚ) -
      (1 - (m : ℚ) * (p : ℚ) * harmh (i - 1) +
        ((m : ℚ) * (p : ℚ)) ^ 2 * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) / 2)) := by
  have hlt : i - 1 < m * p := by
    have : 1 * p ≤ m * p := Nat.mul_le_mul_right p hm
    omega
  have hprod := choose_sub_one_eq_prod (m * p) (i - 1) hlt
  have hsign : (-1 : ℚ) ^ (i - 1) * ((m * p - 1).choose (i - 1) : ℚ) =
      ∏ j ∈ Icc 1 (i - 1), (1 + (-(m : ℚ) * (p : ℚ)) * ((1 : ℚ) / (j : ℚ))) := by
    rw [hprod, ← mul_assoc]
    have h1 : (-1 : ℚ) ^ (i - 1) * (-1 : ℚ) ^ (i - 1) = 1 := by rw [← mul_pow]; norm_num
    rw [h1, one_mul]; apply prod_congr rfl; intro j _; push_cast; ring
  rw [hsign]
  set c : ℚ := -(m : ℚ) * (p : ℚ)
  set f : ℕ → ℚ := fun j => (1 : ℚ) / (j : ℚ)
  have hc : pDiv p 1 c := by
    have : c = (-(m : ℤ) : ℚ) * (p : ℚ) := by dsimp only [c]; push_cast; ring
    rw [this]; simpa using pDiv_mul hp (pDiv_int_zero hp (-(m : ℤ))) (pDiv_p_one p hp)
  have hf : ∀ j ∈ Icc 1 (i - 1), pDiv p 0 (f j) := fun j hj =>
    inv_lt_p_pDiv0 hp (mem_Icc.mp hj).1 (by have := (mem_Icc.mp hj).2; omega)
  have htr := prod_one_add_trunc2 hp (Icc 1 (i - 1)) f c hc hf
  have hsm := prodPS_coeff_small (Icc 1 (i - 1)) f
  have hp1 : ∑ j ∈ Icc 1 (i - 1), f j = harmh (i - 1) := rfl
  have hp2 : ∑ j ∈ Icc 1 (i - 1), (f j) ^ 2 = harmh2 (i - 1) := by simp [harmh2, f]
  have he2 : PowerSeries.coeff 2 (prodPS (Icc 1 (i - 1)) f) =
      (harmh (i - 1) ^ 2 - harmh2 (i - 1)) / 2 := by
    have := hsm.2.2.1; rw [hp1, hp2] at this; linarith
  rw [hp1, he2] at htr
  have hrew : (1 + c * harmh (i - 1) + c ^ 2 * ((harmh (i - 1) ^ 2 - harmh2 (i - 1)) / 2)) =
      (1 - (m : ℚ) * (p : ℚ) * harmh (i - 1) +
        ((m : ℚ) * (p : ℚ)) ^ 2 * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) / 2) := by
    dsimp only [c]; ring
  rwa [hrew] at htr

lemma choose_mp_add_trunc2 (p m k : ℕ) (hp : p.Prime) (hk : k < p) :
    pDiv p 3 (((m * p + k).choose k : ℚ) -
      (1 + (m : ℚ) * (p : ℚ) * harmh k +
        ((m : ℚ) * (p : ℚ)) ^ 2 * (harmh k ^ 2 - harmh2 k) / 2)) := by
  have hprod := choose_add_eq_prod (m * p) k
  rw [hprod]
  set c : ℚ := (m : ℚ) * (p : ℚ)
  set f : ℕ → ℚ := fun j => (1 : ℚ) / (j : ℚ)
  have hc : pDiv p 1 c := by
    simpa [c] using pDiv_mul hp (pDiv_nat_zero hp m) (pDiv_p_one p hp)
  have hf : ∀ j ∈ Icc 1 k, pDiv p 0 (f j) := fun j hj =>
    inv_lt_p_pDiv0 hp (mem_Icc.mp hj).1 (by have := (mem_Icc.mp hj).2; omega)
  have htr := prod_one_add_trunc2 hp (Icc 1 k) f c hc hf
  have hsm := prodPS_coeff_small (Icc 1 k) f
  have hp1 : ∑ j ∈ Icc 1 k, f j = harmh k := rfl
  have hp2 : ∑ j ∈ Icc 1 k, (f j) ^ 2 = harmh2 k := by simp [harmh2, f, div_pow]
  have he2 : PowerSeries.coeff 2 (prodPS (Icc 1 k) f) = (harmh k ^ 2 - harmh2 k) / 2 := by
    have := hsm.2.2.1; rw [hp1, hp2] at this; linarith
  rw [hp1, he2] at htr
  have hrew : (1 + c * harmh k + c ^ 2 * ((harmh k ^ 2 - harmh2 k) / 2)) =
      (1 + (m : ℚ) * (p : ℚ) * harmh k +
        ((m : ℚ) * (p : ℚ)) ^ 2 * (harmh k ^ 2 - harmh2 k) / 2) := by
    dsimp only [c]; ring
  have hcast : ((m * p : ℕ) : ℚ) = c := by dsimp only [c]; push_cast; rfl
  rw [hcast]
  rwa [hrew] at htr

-- Harmonic reflection: h(p - 1 - k) ≡ h(k) + p * h2(k) (mod p^2) and h2(p - 1 - k) ≡ -h2(k) (mod p)
lemma harmh_reflect_pDiv2 (p k : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hk : k < p) :
    pDiv p 2 (harmh (p - 1 - k) - (harmh k + (p : ℚ) * harmh2 k)) := by
  -- H_1 = h(p - 1 - k) + ∑_{j=1}^k 1/(p - j)
  have hsplit : harmH p 1 = harmh (p - 1 - k) + ∑ j ∈ Icc 1 k, (1 : ℚ) / ((p - j : ℕ) : ℚ) := by
    have hdisj : Ico 1 p = Icc 1 (p - 1 - k) ∪ Icc (p - k) (p - 1) := by
      ext x; simp only [mem_Ico, mem_union, mem_Icc]; omega
    unfold harmH harmh
    rw [hdisj, sum_union (by simp only [Finset.disjoint_left, mem_Icc]; omega)]
    simp only [pow_one]
    congr 1
    refine Finset.sum_bij (fun x _ => p - x) ?_ ?_ ?_ ?_
    · intro x hx; simp only [mem_Icc] at hx ⊢; omega
    · intro x₁ hx₁ x₂ hx₂ h; simp only [mem_Icc] at hx₁ hx₂; omega
    · intro j hj; exact ⟨p - j, by simp only [mem_Icc] at hj ⊢; omega, by simp only [mem_Icc] at hj; omega⟩
    · intro x hx; simp only [mem_Icc] at hx; rw [Nat.sub_sub_self (by omega)]
  have hdiff : harmh (p - 1 - k) - (harmh k + (p : ℚ) * harmh2 k) =
      harmH p 1 - (p : ℚ) ^ 2 * ∑ j ∈ Icc 1 k, (1 : ℚ) / ((j : ℚ) ^ 2 * ((p - j : ℕ) : ℚ)) := by
    have hsum : ∑ j ∈ Icc 1 k, (1 : ℚ) / ((p - j : ℕ) : ℚ) + harmh k + (p : ℚ) * harmh2 k =
        (p : ℚ) ^ 2 * ∑ j ∈ Icc 1 k, (1 : ℚ) / ((j : ℚ) ^ 2 * ((p - j : ℕ) : ℚ)) := by
      unfold harmh harmh2
      simp only [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl; intro j hj
      have hj1 := (mem_Icc.mp hj).1
      have hj2 := (mem_Icc.mp hj).2
      have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hsub : ((p - j : ℕ) : ℚ) = (p : ℚ) - (j : ℚ) := Nat.cast_sub (by omega)
      have hpj0 : (p : ℚ) - (j : ℚ) ≠ 0 := by rw [← hsub]; exact Nat.cast_ne_zero.mpr (by omega)
      rw [hsub]; field_simp [hj0, hpj0]; ring
    linarith
  rw [hdiff]
  have hsum0 : pDiv p 0 (∑ j ∈ Icc 1 k, (1 : ℚ) / ((j : ℚ) ^ 2 * ((p - j : ℕ) : ℚ))) := by
    apply pDiv_sum hp; intro j hj
    have hj1 := (mem_Icc.mp hj).1
    have hj2 := (mem_Icc.mp hj).2
    have h1 := inv_pow_lt_p_pDiv0 (k := 2) hp hj1 (by omega)
    have h2 := inv_lt_p_pDiv0 hp (by omega : 1 ≤ p - j) (by omega : p - j < p)
    have hrew : (1 : ℚ) / ((j : ℚ) ^ 2 * ((p - j : ℕ) : ℚ)) =
        ((1 : ℚ) / (j : ℚ) ^ 2) * ((1 : ℚ) / ((p - j : ℕ) : ℚ)) := by ring
    rw [hrew]; simpa using pDiv_mul hp h1 h2
  exact pDiv_sub hp (harmH1_pDiv_two p hp hp7) (by simpa using pDiv_mul hp (pDiv_p_pow p 2 hp) hsum0)

lemma harmh2_reflect_pDiv1 (p k : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hk : k < p) :
    pDiv p 1 (harmh2 (p - 1 - k) + harmh2 k) := by
  have hsplit : harmH p 2 = harmh2 (p - 1 - k) + ∑ j ∈ Icc 1 k, (1 : ℚ) / (((p - j : ℕ) : ℚ) ^ 2) := by
    have hdisj : Ico 1 p = Icc 1 (p - 1 - k) ∪ Icc (p - k) (p - 1) := by
      ext x; simp only [mem_Ico, mem_union, mem_Icc]; omega
    unfold harmH harmh2
    rw [hdisj, sum_union (by simp only [Finset.disjoint_left, mem_Icc]; omega)]
    congr 1
    refine Finset.sum_bij (fun x _ => p - x) ?_ ?_ ?_ ?_
    · intro x hx; simp only [mem_Icc] at hx ⊢; omega
    · intro x₁ hx₁ x₂ hx₂ h; simp only [mem_Icc] at hx₁ hx₂; omega
    · intro j hj; exact ⟨p - j, by simp only [mem_Icc] at hj ⊢; omega, by simp only [mem_Icc] at hj; omega⟩
    · intro x hx; simp only [mem_Icc] at hx; rw [Nat.sub_sub_self (by omega)]
  have hdiff : harmh2 (p - 1 - k) + harmh2 k =
      harmH p 2 - (p : ℚ) * ∑ j ∈ Icc 1 k, (2 * (j : ℚ) - (p : ℚ)) / ((j : ℚ) ^ 2 * ((p - j : ℕ) : ℚ) ^ 2) := by
    have hsum : ∑ j ∈ Icc 1 k, (1 : ℚ) / (((p - j : ℕ) : ℚ) ^ 2) - harmh2 k =
        (p : ℚ) * ∑ j ∈ Icc 1 k, (2 * (j : ℚ) - (p : ℚ)) / ((j : ℚ) ^ 2 * ((p - j : ℕ) : ℚ) ^ 2) := by
      unfold harmh2
      rw [mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl; intro j hj
      have hj1 := (mem_Icc.mp hj).1
      have hj2 := (mem_Icc.mp hj).2
      have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hsub : ((p - j : ℕ) : ℚ) = (p : ℚ) - (j : ℚ) := Nat.cast_sub (by omega)
      have hpj0 : (p : ℚ) - (j : ℚ) ≠ 0 := by rw [← hsub]; exact Nat.cast_ne_zero.mpr (by omega)
      rw [hsub]; field_simp [hj0, hpj0]; ring
    linarith
  rw [hdiff]
  have hsum0 : pDiv p 0 (∑ j ∈ Icc 1 k, (2 * (j : ℚ) - (p : ℚ)) / ((j : ℚ) ^ 2 * ((p - j : ℕ) : ℚ) ^ 2)) := by
    apply pDiv_sum hp; intro j hj
    have hj1 := (mem_Icc.mp hj).1
    have hj2 := (mem_Icc.mp hj).2
    have h1 := inv_pow_lt_p_pDiv0 (k := 2) hp hj1 (by omega)
    have h2 := inv_pow_lt_p_pDiv0 (k := 2) hp (by omega : 1 ≤ p - j) (by omega : p - j < p)
    have hnum : pDiv p 0 (2 * (j : ℚ) - (p : ℚ)) := by
      simpa using pDiv_int_zero hp (2 * (j : ℤ) - (p : ℤ))
    have hrew : (2 * (j : ℚ) - (p : ℚ)) / ((j : ℚ) ^ 2 * ((p - j : ℕ) : ℚ) ^ 2) =
        (2 * (j : ℚ) - (p : ℚ)) * ((1 : ℚ) / (j : ℚ) ^ 2) * ((1 : ℚ) / ((p - j : ℕ) : ℚ) ^ 2) := by ring
    rw [hrew]; simpa using pDiv_mul hp (pDiv_mul hp hnum h1) h2
  exact pDiv_sub hp (harmH2_pDiv_one p hp (by omega)) (by simpa using pDiv_mul hp (pDiv_p_one p hp) hsum0)

-- ============================================================================
-- Section 4: Multiple harmonic sums U1, U2, U3, U4 via Chu-Vandermonde #1 & #2
-- ============================================================================

def harmU1 (p : ℕ) : ℚ := ∑ i ∈ Ico 1 p, harmh (i - 1) / ((i : ℚ) ^ 2)
def harmU2 (p : ℕ) : ℚ := ∑ i ∈ Ico 1 p, (harmh (i - 1)) ^ 2 / ((i : ℚ) ^ 2)
def harmU3 (p : ℕ) : ℚ := ∑ i ∈ Ico 1 p, harmh2 (i - 1) / ((i : ℚ) ^ 2)
def harmU4 (p : ℕ) : ℚ := ∑ i ∈ Ico 1 p, harmh (i - 1) / ((i : ℚ) ^ 3)

lemma harmU3_pDiv1 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : pDiv p 1 (harmU3 p) := by
  have hid : 2 * harmU3 p = harmH p 2 ^ 2 - harmH p 4 := by
    have hsq : harmH p 2 ^ 2 =
        ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p, (1 : ℚ) / ((i : ℚ) ^ 2) * ((1 : ℚ) / ((j : ℚ) ^ 2)) := by
      unfold harmH; rw [sq, sum_mul_sum]
    have hlt_eq : (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
        if j < i then (1 : ℚ) / ((i : ℚ) ^ 2) * ((1 : ℚ) / ((j : ℚ) ^ 2)) else 0) = harmU3 p := by
      unfold harmU3 harmh2
      apply sum_congr rfl; intro i hi
      have hi1 := (mem_Ico.mp hi).1
      have hi2 := (mem_Ico.mp hi).2
      rw [← sum_filter]
      have hfilt : (Ico 1 p).filter (· < i) = Icc 1 (i - 1) := by
        ext j; simp only [mem_filter, mem_Ico, mem_Icc]; omega
      rw [hfilt, sum_div]
      apply sum_congr rfl; intro j _; ring
    have hgt_eq : (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
        if i < j then (1 : ℚ) / ((i : ℚ) ^ 2) * ((1 : ℚ) / ((j : ℚ) ^ 2)) else 0) = harmU3 p := by
      rw [← hlt_eq, sum_comm]
      apply sum_congr rfl; intro i _
      apply sum_congr rfl; intro j _
      by_cases h : j < i <;> simp [h, mul_comm]
    have hsplit : (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p, (1 : ℚ) / ((i : ℚ) ^ 2) * ((1 : ℚ) / ((j : ℚ) ^ 2))) =
        harmH p 4 +
        (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
          if j < i then (1 : ℚ) / ((i : ℚ) ^ 2) * ((1 : ℚ) / ((j : ℚ) ^ 2)) else 0) +
        (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
          if i < j then (1 : ℚ) / ((i : ℚ) ^ 2) * ((1 : ℚ) / ((j : ℚ) ^ 2)) else 0) := by
      unfold harmH
      rw [← sum_add_distrib, ← sum_add_distrib]
      apply sum_congr rfl; intro i hi
      have hdiag : (1 : ℚ) / (i : ℚ) ^ 4 =
          ∑ j ∈ Ico 1 p, if j = i then (1 : ℚ) / ((i : ℚ) ^ 2) * ((1 : ℚ) / ((j : ℚ) ^ 2)) else 0 := by
        rw [sum_ite_eq' (Ico 1 p) i, if_pos hi]; ring
      rw [hdiag, ← sum_add_distrib, ← sum_add_distrib]
      apply sum_congr rfl; intro j _
      rcases lt_trichotomy j i with hlt | rfl | hgt
      · simp [hlt, ne_of_lt hlt, not_lt.mpr (le_of_lt hlt)]
      · simp
      · simp [hgt, ne_of_gt hgt, not_lt.mpr (le_of_lt hgt)]
    linarith [hsq, hsplit, hlt_eq, hgt_eq]
  have h2U3 : pDiv p 1 ((2 : ℕ) * harmU3 p) := by
    have hrew : ((2 : ℕ) : ℚ) * harmU3 p = harmH p 2 ^ 2 - harmH p 4 := by push_cast; exact hid
    rw [hrew]
    have h22 : pDiv p 1 (harmH p 2 ^ 2) :=
      pDiv_mono (by omega) (pDiv_pow (n := 2) hp (harmH2_pDiv_one p hp (by omega)))
    exact pDiv_sub hp h22 (harmH4_pDiv_one p hp hp7)
  exact pDiv_cancel_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega) h2U3

lemma harmU4_pDiv1 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : pDiv p 1 (harmU4 p) := by
  -- Reindex (j, i) ↦ (p - i, p - j) to get U4 ≡ ∑_{i < j} 1/(i^3 * j) (mod p),
  -- then 2 * U4 ≡ H_1 * H_3 - H_4 ≡ 0 (mod p)!
  have hlt_eq : harmU4 p = ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
      if j < i then (1 : ℚ) / ((j : ℚ) * ((i : ℚ) ^ 3)) else 0 := by
    unfold harmU4 harmh
    apply sum_congr rfl; intro i hi
    have hi1 := (mem_Ico.mp hi).1
    have hi2 := (mem_Ico.mp hi).2
    rw [← sum_filter]
    have hfilt : (Ico 1 p).filter (· < i) = Icc 1 (i - 1) := by
      ext j; simp only [mem_filter, mem_Ico, mem_Icc]; omega
    rw [hfilt, sum_div]
    apply sum_congr rfl; intro j _; ring
  set U4' : ℚ := ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
      if i < j then (1 : ℚ) / ((j : ℚ) * ((i : ℚ) ^ 3)) else 0
  have hdiff : pDiv p 1 (harmU4 p - U4') := by
    have hrev : harmU4 p = ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
        if i < j then (1 : ℚ) / (((p - j : ℕ) : ℚ) * (((p - i : ℕ) : ℚ) ^ 3)) else 0 := by
      rw [hlt_eq]
      -- First swap order i, j -> (p - i, p - j)
      have h1 : ∀ f : ℕ → ℕ → ℚ,
          (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p, f i j) =
            ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p, f (p - i) (p - j) := by
        intro f
        refine Finset.sum_bij (fun i _ => p - i) ?_ ?_ ?_ ?_
        · intro i hi; simp only [mem_Ico] at hi ⊢; omega
        · intro i₁ hi₁ i₂ hi₂ h; simp only [mem_Ico] at hi₁ hi₂; omega
        · intro v hv; exact ⟨p - v, by simp only [mem_Ico] at hv ⊢; omega, by simp only [mem_Ico] at hv; omega⟩
        · intro i hi
          refine Finset.sum_bij (fun j _ => p - j) ?_ ?_ ?_ ?_
          · intro j hj; simp only [mem_Ico] at hj ⊢; omega
          · intro j₁ hj₁ j₂ hj₂ h; simp only [mem_Ico] at hj₁ hj₂; omega
          · intro w hw; exact ⟨p - w, by simp only [mem_Ico] at hw ⊢; omega, by simp only [mem_Ico] at hw; omega⟩
          · intro j hj
            simp only [mem_Ico] at hi hj
            rw [Nat.sub_sub_self (by omega), Nat.sub_sub_self (by omega)]
      rw [h1]
      apply sum_congr rfl; intro i hi
      apply sum_congr rfl; intro j hj
      have hi1 := (mem_Ico.mp hi).1; have hi2 := (mem_Ico.mp hi).2
      have hj1 := (mem_Ico.mp hj).1; have hj2 := (mem_Ico.mp hj).2
      have hiff : p - j < p - i ↔ i < j := by omega
      simp only [hiff]
    rw [hrev]
    dsimp only [U4']
    rw [← sum_sub_distrib]
    apply pDiv_sum hp; intro i hi
    rw [← sum_sub_distrib]
    apply pDiv_sum hp; intro j hj
    by_cases hij : i < j
    · rw [if_pos hij, if_pos hij]
      have hi1 := (mem_Ico.mp hi).1; have hi2 := (mem_Ico.mp hi).2
      have hj1 := (mem_Ico.mp hj).1; have hj2 := (mem_Ico.mp hj).2
      have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hsi : ((p - i : ℕ) : ℚ) = (p : ℚ) - (i : ℚ) := Nat.cast_sub (by omega)
      have hsj : ((p - j : ℕ) : ℚ) = (p : ℚ) - (j : ℚ) := Nat.cast_sub (by omega)
      have hpi0 : (p : ℚ) - (i : ℚ) ≠ 0 := by rw [← hsi]; exact Nat.cast_ne_zero.mpr (by omega)
      have hpj0 : (p : ℚ) - (j : ℚ) ≠ 0 := by rw [← hsj]; exact Nat.cast_ne_zero.mpr (by omega)
      have hrew : (1 : ℚ) / (((p - j : ℕ) : ℚ) * (((p - i : ℕ) : ℚ) ^ 3)) -
          (1 : ℚ) / ((j : ℚ) * ((i : ℚ) ^ 3)) =
          (p : ℚ) * (-(p : ℚ) ^ 3 + (3 * (i : ℚ) + (j : ℚ)) * (p : ℚ) ^ 2 -
            (3 * (i : ℚ) ^ 2 + 3 * (i : ℚ) * (j : ℚ)) * (p : ℚ) +
            ((i : ℚ) ^ 3 + 3 * (i : ℚ) ^ 2 * (j : ℚ))) *
          ((1 : ℚ) / ((p - j : ℕ) : ℚ)) * ((1 : ℚ) / (((p - i : ℕ) : ℚ) ^ 3)) *
          ((1 : ℚ) / (j : ℚ)) * ((1 : ℚ) / ((i : ℚ) ^ 3)) := by
        rw [hsi, hsj]; field_simp [hi0, hj0, hpi0, hpj0]; ring
      rw [hrew]
      have hnum : pDiv p 0 (-(p : ℚ) ^ 3 + (3 * (i : ℚ) + (j : ℚ)) * (p : ℚ) ^ 2 -
          (3 * (i : ℚ) ^ 2 + 3 * (i : ℚ) * (j : ℚ)) * (p : ℚ) +
          ((i : ℚ) ^ 3 + 3 * (i : ℚ) ^ 2 * (j : ℚ))) := by
        convert pDiv_int_zero hp (-(p : ℤ) ^ 3 + (3 * (i : ℤ) + (j : ℤ)) * (p : ℤ) ^ 2 -
          (3 * (i : ℤ) ^ 2 + 3 * (i : ℤ) * (j : ℤ)) * (p : ℤ) +
          ((i : ℤ) ^ 3 + 3 * (i : ℤ) ^ 2 * (j : ℤ)))
        push_cast; ring
      have h1 := inv_lt_p_pDiv0 hp (by omega : 1 ≤ p - j) (by omega : p - j < p)
      have h2 := inv_pow_lt_p_pDiv0 (k := 3) hp (by omega : 1 ≤ p - i) (by omega : p - i < p)
      have h3 := inv_lt_p_pDiv0 hp hj1 hj2
      have h4 := inv_pow_lt_p_pDiv0 (k := 3) hp hi1 hi2
      simpa using pDiv_mul hp (pDiv_mul hp (pDiv_mul hp (pDiv_mul hp
        (pDiv_mul hp (pDiv_p_one p hp) hnum) h1) h2) h3) h4
    · simp [hij, pDiv_zero p 1 hp]
  have hsum_id : harmU4 p + U4' = harmH p 1 * harmH p 3 - harmH p 4 := by
    have hprod : harmH p 1 * harmH p 3 =
        ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p, (1 : ℚ) / ((j : ℚ) * ((i : ℚ) ^ 3)) := by
      unfold harmH
      rw [mul_comm, sum_mul_sum]
      apply sum_congr rfl; intro i _
      apply sum_congr rfl; intro j _
      ring
    rw [hlt_eq]
    dsimp only [U4']
    have hsplit : (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p, (1 : ℚ) / ((j : ℚ) * ((i : ℚ) ^ 3))) =
        harmH p 4 +
        (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p, if j < i then (1 : ℚ) / ((j : ℚ) * ((i : ℚ) ^ 3)) else 0) +
        (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p, if i < j then (1 : ℚ) / ((j : ℚ) * ((i : ℚ) ^ 3)) else 0) := by
      unfold harmH
      rw [← sum_add_distrib, ← sum_add_distrib]
      apply sum_congr rfl; intro i hi
      have hdiag : (1 : ℚ) / (i : ℚ) ^ 4 =
          ∑ j ∈ Ico 1 p, if j = i then (1 : ℚ) / ((j : ℚ) * ((i : ℚ) ^ 3)) else 0 := by
        rw [sum_ite_eq' (Ico 1 p) i, if_pos hi]; ring
      rw [hdiag, ← sum_add_distrib, ← sum_add_distrib]
      apply sum_congr rfl; intro j _
      rcases lt_trichotomy j i with hlt | rfl | hgt
      · simp [hlt, ne_of_lt hlt, not_lt.mpr (le_of_lt hlt)]
      · simp
      · simp [hgt, ne_of_gt hgt, not_lt.mpr (le_of_lt hgt)]
    linarith
  have h2U4 : pDiv p 1 ((2 : ℕ) * harmU4 p) := by
    have hrew : ((2 : ℕ) : ℚ) * harmU4 p =
        (harmU4 p - U4') + (harmH p 1 * harmH p 3 - harmH p 4) := by
      push_cast; linarith
    rw [hrew]
    have h13 : pDiv p 1 (harmH p 1 * harmH p 3) :=
      pDiv_mono (by omega) (pDiv_mul hp (harmH1_pDiv_two p hp hp7) (harmH3_pDiv_two p hp hp7))
    exact pDiv_add hp hdiff (pDiv_sub hp h13 (harmH4_pDiv_one p hp hp7))
  exact pDiv_cancel_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega) h2U4

-- Helper: C(m*p, i) = (m*p / i) * C(m*p - 1, i - 1)
lemma choose_mp_eq (p m i : ℕ) (hm : 1 ≤ m) (hi1 : 1 ≤ i) (hi2 : i < p) :
    ((m * p).choose i : ℚ) = ((m : ℚ) * (p : ℚ) / (i : ℚ)) * ((m * p - 1).choose (i - 1) : ℚ) := by
  have h1 := Nat.add_one_mul_choose_eq (m * p - 1) (i - 1)
  have hmp1 : 0 < m * p := Nat.mul_pos hm (by omega)
  have e1 : m * p - 1 + 1 = m * p := by omega
  have e2 : i - 1 + 1 = i := by omega
  rw [e1, e2] at h1
  have hQ : ((m * p : ℕ) : ℚ) * ((m * p - 1).choose (i - 1) : ℚ) =
      ((m * p).choose i : ℚ) * (i : ℚ) := by exact_mod_cast h1
  have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast at hQ
  field_simp [hi0] at hQ ⊢
  linarith

-- Helper: C(k*p, p) = k * C(k*p - 1, p - 1)
lemma choose_kp_p_eq (p k : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k) :
    ((k * p).choose p : ℚ) = (k : ℚ) * ((k * p - 1).choose (p - 1) : ℚ) := by
  have h1 := Nat.add_one_mul_choose_eq (k * p - 1) (p - 1)
  have hkp1 : 0 < k * p := Nat.mul_pos hk hp
  have e1 : k * p - 1 + 1 = k * p := by omega
  have e2 : p - 1 + 1 = p := by omega
  rw [e1, e2] at h1
  have hQ : ((k * p : ℕ) : ℚ) * ((k * p - 1).choose (p - 1) : ℚ) =
      ((k * p).choose p : ℚ) * (p : ℚ) := by exact_mod_cast h1
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast at hQ
  have : (p : ℚ) * ((k * p).choose p : ℚ) = (p : ℚ) * ((k : ℚ) * ((k * p - 1).choose (p - 1) : ℚ)) := by
    linarith
  exact mul_left_cancel₀ hp0 this

-- Chu-Vandermonde #1 & #2 -> p^4 * U2 ≡ 0 (mod p^5) and p^3 * U1 ≡ -3 * p * H1 (mod p^5)!
lemma harmU1_U2_pDiv5 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    pDiv p 5 ((p : ℚ) ^ 4 * harmU2 p) ∧
    pDiv p 5 ((p : ℚ) ^ 3 * harmU1 p + 3 * (p : ℚ) * harmH p 1) := by
  have hH12 := harmH1_H2_pDiv_five p hp hp7
  have hU3 := harmU3_pDiv1 p hp hp7
  have hU3_5 : pDiv p 5 ((p : ℚ) ^ 4 * harmU3 p) := pDiv_mul hp (pDiv_p_pow p 4 hp) hU3
  -- Vandermonde #1: ∑_{i=1}^{p-1} C(p, i)^2 = C(2p, p) - 2
  have hvand1 : (∑ i ∈ Ico 1 p, ((p.choose i : ℚ) ^ 2)) = ((2 * p).choose p : ℚ) - 2 := by
    have hnat : (2 * p).choose p = ∑ i ∈ range (p + 1), p.choose i ^ 2 := by
      rw [two_mul, Nat.add_choose_eq p p p,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.choose i * p.choose j) p]
      apply sum_congr rfl; intro i hi
      rw [Nat.choose_symm (Nat.lt_succ_iff.mp (mem_range.mp hi)), sq]
    have hsplit : range (p + 1) = insert 0 (insert p (Ico 1 p)) := by
      ext i; simp only [mem_range, mem_insert, mem_Ico]; omega
    rw [hsplit, sum_insert (by simp; omega), sum_insert (by simp)] at hnat
    simp only [Nat.choose_zero_right, Nat.choose_self, one_pow] at hnat
    have hQ : ((2 * p).choose p : ℚ) = 1 + (1 + ∑ i ∈ Ico 1 p, ((p.choose i : ℚ) ^ 2)) := by
      exact_mod_cast hnat
    linarith
  -- Vandermonde #2: ∑_{i=1}^{p-1} C(p, i) * C(2p, i) = C(3p, p) - 1 - C(2p, p)
  have hvand2 : (∑ i ∈ Ico 1 p, (p.choose i : ℚ) * ((2 * p).choose i : ℚ)) =
      ((3 * p).choose p : ℚ) - 1 - ((2 * p).choose p : ℚ) := by
    have hnat : (3 * p).choose p = ∑ i ∈ range (p + 1), p.choose i * (2 * p).choose i := by
      have h3 : 3 * p = p + 2 * p := by ring
      rw [h3, Nat.add_choose_eq p (2 * p) p,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.choose i * (2 * p).choose j) p]
      -- Swap i -> p - i using Nat.choose_symm
      refine Finset.sum_bij (fun i _ => p - i) ?_ ?_ ?_ ?_
      · intro i hi; simp only [mem_range] at hi ⊢; omega
      · intro i₁ hi₁ i₂ hi₂ h; simp only [mem_range] at hi₁ hi₂; omega
      · intro v hv; exact ⟨p - v, by simp only [mem_range] at hv ⊢; omega, by simp only [mem_range] at hv; omega⟩
      · intro i hi
        have hip : i ≤ p := Nat.lt_succ_iff.mp (mem_range.mp hi)
        rw [Nat.choose_symm hip]
    have hsplit : range (p + 1) = insert 0 (insert p (Ico 1 p)) := by
      ext i; simp only [mem_range, mem_insert, mem_Ico]; omega
    rw [hsplit, sum_insert (by simp; omega), sum_insert (by simp)] at hnat
    simp only [Nat.choose_zero_right, Nat.choose_self, one_mul] at hnat
    have hQ : ((3 * p).choose p : ℚ) =
        1 + (((2 * p).choose p : ℚ) + ∑ i ∈ Ico 1 p, (p.choose i : ℚ) * ((2 * p).choose i : ℚ)) := by
      exact_mod_cast hnat
    linarith
  -- C(2p, p) - 2 ≡ 4 * p * H1 and C(3p, p) - 1 - C(2p, p) ≡ 14 * p * H1 (mod p^5)
  have hC2p : pDiv p 5 (((2 * p).choose p : ℚ) - 2 - 4 * (p : ℚ) * harmH p 1) := by
    rw [choose_kp_p_eq p 2 hp.one_le (by norm_num)]
    have h := choose_kp_sub_one_pDiv5 p 2 hp hp7 (by norm_num)
    have hrew : (2 : ℚ) * ((2 * p - 1).choose (p - 1) : ℚ) - 2 - 4 * (p : ℚ) * harmH p 1 =
        (2 : ℚ) * (((2 * p - 1).choose (p - 1) : ℚ) -
          (1 + ((2 * (2 - 1) : ℕ) : ℚ) * (p : ℚ) * harmH p 1)) := by norm_num; ring
    push_cast; rw [hrew]; simpa using pDiv_mul hp (pDiv_nat_zero hp 2) h
  have hC3p : pDiv p 5 (((3 * p).choose p : ℚ) - 3 - 18 * (p : ℚ) * harmH p 1) := by
    rw [choose_kp_p_eq p 3 hp.one_le (by norm_num)]
    have h := choose_kp_sub_one_pDiv5 p 3 hp hp7 (by norm_num)
    have hrew : (3 : ℚ) * ((3 * p - 1).choose (p - 1) : ℚ) - 3 - 18 * (p : ℚ) * harmH p 1 =
        (3 : ℚ) * (((3 * p - 1).choose (p - 1) : ℚ) -
          (1 + ((3 * (3 - 1) : ℕ) : ℚ) * (p : ℚ) * harmH p 1)) := by norm_num; ring
    push_cast; rw [hrew]; simpa using pDiv_mul hp (pDiv_nat_zero hp 3) h
  -- Expand LHS of Vandermonde #1 mod p^5:
  have hL1 : pDiv p 5 ((∑ i ∈ Ico 1 p, ((p.choose i : ℚ) ^ 2)) -
      ((p : ℚ) ^ 2 * harmH p 2 - 2 * (p : ℚ) ^ 3 * harmU1 p +
        2 * (p : ℚ) ^ 4 * harmU2 p - (p : ℚ) ^ 4 * harmU3 p)) := by
    have hsum_rhs : (p : ℚ) ^ 2 * harmH p 2 - 2 * (p : ℚ) ^ 3 * harmU1 p +
        2 * (p : ℚ) ^ 4 * harmU2 p - (p : ℚ) ^ 4 * harmU3 p =
        ∑ i ∈ Ico 1 p, ((p : ℚ) ^ 2 / ((i : ℚ) ^ 2)) *
          (1 - 2 * (p : ℚ) * harmh (i - 1) +
            (p : ℚ) ^ 2 * (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1))) := by
      unfold harmH harmU1 harmU2 harmU3
      simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      apply sum_congr rfl; intro i _; ring
    rw [hsum_rhs, ← sum_sub_distrib]
    apply pDiv_sum hp; intro i hi
    have hi1 := (mem_Ico.mp hi).1; have hi2 := (mem_Ico.mp hi).2
    have hch := choose_mp_eq p 1 i le_rfl hi1 hi2
    simp only [one_mul, Nat.cast_one] at hch
    rw [hch, mul_pow]
    have hrew : ((p : ℚ) / (i : ℚ)) ^ 2 * ((p - 1).choose (i - 1) : ℚ) ^ 2 -
        (p : ℚ) ^ 2 / (i : ℚ) ^ 2 *
          (1 - 2 * (p : ℚ) * harmh (i - 1) +
            (p : ℚ) ^ 2 * (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1))) =
        (p : ℚ) ^ 2 * ((1 : ℚ) / (i : ℚ) ^ 2) *
          (((-1 : ℚ) ^ (i - 1) * ((p - 1).choose (i - 1) : ℚ)) ^ 2 -
            (1 - 2 * (p : ℚ) * harmh (i - 1) +
              (p : ℚ) ^ 2 * (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1)))) := by
      rw [div_pow, mul_pow]
      have hsq : ((-1 : ℚ) ^ (i - 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [hsq, one_mul]; ring
    rw [hrew]
    have htr := choose_mp_sub_one_trunc2 p 1 i hp le_rfl hi1 hi2
    simp only [one_mul, Nat.cast_one] at htr
    set X := (-1 : ℚ) ^ (i - 1) * ((p - 1).choose (i - 1) : ℚ)
    set Y := 1 - (p : ℚ) * harmh (i - 1) + (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) / 2
    have hhh := harmh_pDiv0 (p := p) hp (by omega : i - 1 < p)
    have hhh2 := harmh2_pDiv0 (p := p) hp (by omega : i - 1 < p)
    have hY0 : pDiv p 0 Y := by
      have h1 : pDiv p 0 ((p : ℚ) * harmh (i - 1)) :=
        pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_one p hp) hhh)
      have h2 : pDiv p 0 ((p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) / (2 : ℕ)) := by
        apply pDiv_div_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
        exact pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_pow p 2 hp)
          (pDiv_sub hp (by simpa using pDiv_pow (n := 2) hp hhh) hhh2))
      have hYrew : Y = 1 - (p : ℚ) * harmh (i - 1) +
          (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) / (2 : ℕ) := by push_cast; rfl
      rw [hYrew]; exact pDiv_add hp (pDiv_sub hp (pDiv_nat_zero hp 1) h1) h2
    have hX0 : pDiv p 0 X := by
      have : X = (X - Y) + Y := by ring
      rw [this]; exact pDiv_add hp (pDiv_mono (by omega) htr) hY0
    have hXY_sq : pDiv p 3 (X ^ 2 - Y ^ 2) := by
      have : X ^ 2 - Y ^ 2 = (X + Y) * (X - Y) := by ring
      rw [this]; simpa using pDiv_mul hp (pDiv_add hp hX0 hY0) htr
    have hY_sq : pDiv p 3 (Y ^ 2 -
        (1 - 2 * (p : ℚ) * harmh (i - 1) + (p : ℚ) ^ 2 * (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1)))) := by
      have hrewY : Y ^ 2 -
          (1 - 2 * (p : ℚ) * harmh (i - 1) + (p : ℚ) ^ 2 * (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1))) =
          (p : ℚ) ^ 3 * (-harmh (i - 1) * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) +
            (p : ℚ) * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) ^ 2 / (4 : ℕ)) := by
        dsimp only [Y]; push_cast; ring
      rw [hrewY]
      have hdiff0 : pDiv p 0 (harmh (i - 1) ^ 2 - harmh2 (i - 1)) :=
        pDiv_sub hp (by simpa using pDiv_pow (n := 2) hp hhh) hhh2
      have ht1 : pDiv p 0 (-harmh (i - 1) * (harmh (i - 1) ^ 2 - harmh2 (i - 1))) := by
        simpa using pDiv_mul hp (pDiv_neg hhh) hdiff0
      have ht2 : pDiv p 0 ((p : ℚ) * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) ^ 2 / (4 : ℕ)) := by
        apply pDiv_div_nat_unit hp (fun h => by
          have : p ∣ 2 ^ 2 := by simpa using h
          have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow this); omega)
        exact pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_one p hp)
          (by simpa using pDiv_pow (n := 2) hp hdiff0))
      simpa using pDiv_mul hp (pDiv_p_pow p 3 hp) (pDiv_add hp ht1 ht2)
    have hdiff3 : pDiv p 3 (X ^ 2 -
        (1 - 2 * (p : ℚ) * harmh (i - 1) + (p : ℚ) ^ 2 * (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1)))) := by
      have : X ^ 2 - (1 - 2 * (p : ℚ) * harmh (i - 1) +
            (p : ℚ) ^ 2 * (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1))) =
          (X ^ 2 - Y ^ 2) + (Y ^ 2 - (1 - 2 * (p : ℚ) * harmh (i - 1) +
            (p : ℚ) ^ 2 * (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1)))) := by ring
      rw [this]; exact pDiv_add hp hXY_sq hY_sq
    have hinv := inv_pow_lt_p_pDiv0 (k := 2) hp hi1 hi2
    simpa using pDiv_mul hp (pDiv_mul hp (pDiv_p_pow p 2 hp) hinv) hdiff3
  -- Expand LHS of Vandermonde #2 mod p^5:
  have hL2 : pDiv p 5 ((∑ i ∈ Ico 1 p, (p.choose i : ℚ) * ((2 * p).choose i : ℚ)) -
      (2 * (p : ℚ) ^ 2 * harmH p 2 - 6 * (p : ℚ) ^ 3 * harmU1 p +
        9 * (p : ℚ) ^ 4 * harmU2 p - 5 * (p : ℚ) ^ 4 * harmU3 p)) := by
    have hsum_rhs : 2 * (p : ℚ) ^ 2 * harmH p 2 - 6 * (p : ℚ) ^ 3 * harmU1 p +
        9 * (p : ℚ) ^ 4 * harmU2 p - 5 * (p : ℚ) ^ 4 * harmU3 p =
        ∑ i ∈ Ico 1 p, (2 * (p : ℚ) ^ 2 / ((i : ℚ) ^ 2)) *
          (1 - 3 * (p : ℚ) * harmh (i - 1) +
            (p : ℚ) ^ 2 * (9 * harmh (i - 1) ^ 2 - 5 * harmh2 (i - 1)) / 2) := by
      unfold harmH harmU1 harmU2 harmU3
      simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      apply sum_congr rfl; intro i _; ring
    rw [hsum_rhs, ← sum_sub_distrib]
    apply pDiv_sum hp; intro i hi
    have hi1 := (mem_Ico.mp hi).1; have hi2 := (mem_Ico.mp hi).2
    have hch1 := choose_mp_eq p 1 i le_rfl hi1 hi2
    have hch2 := choose_mp_eq p 2 i (by norm_num) hi1 hi2
    simp only [one_mul, Nat.cast_one] at hch1
    rw [hch1, hch2]
    set X1 := (-1 : ℚ) ^ (i - 1) * ((p - 1).choose (i - 1) : ℚ)
    set X2 := (-1 : ℚ) ^ (i - 1) * ((2 * p - 1).choose (i - 1) : ℚ)
    have hrew : (p : ℚ) / (i : ℚ) * ((p - 1).choose (i - 1) : ℚ) *
          ((2 : ℕ) * (p : ℚ) / (i : ℚ) * ((2 * p - 1).choose (i - 1) : ℚ)) -
        2 * (p : ℚ) ^ 2 / (i : ℚ) ^ 2 *
          (1 - 3 * (p : ℚ) * harmh (i - 1) +
            (p : ℚ) ^ 2 * (9 * harmh (i - 1) ^ 2 - 5 * harmh2 (i - 1)) / 2) =
        2 * (p : ℚ) ^ 2 * ((1 : ℚ) / (i : ℚ) ^ 2) *
          (X1 * X2 - (1 - 3 * (p : ℚ) * harmh (i - 1) +
            (p : ℚ) ^ 2 * (9 * harmh (i - 1) ^ 2 - 5 * harmh2 (i - 1)) / 2)) := by
      dsimp only [X1, X2]
      have hsq : (-1 : ℚ) ^ (i - 1) * (-1 : ℚ) ^ (i - 1) = 1 := by rw [← mul_pow]; norm_num
      push_cast
      calc (p : ℚ) / (i : ℚ) * ((p - 1).choose (i - 1) : ℚ) *
              (2 * (p : ℚ) / (i : ℚ) * ((2 * p - 1).choose (i - 1) : ℚ)) -
            2 * (p : ℚ) ^ 2 / (i : ℚ) ^ 2 *
              (1 - 3 * (p : ℚ) * harmh (i - 1) +
                (p : ℚ) ^ 2 * (9 * harmh (i - 1) ^ 2 - 5 * harmh2 (i - 1)) / 2)
          = 2 * (p : ℚ) ^ 2 * ((1 : ℚ) / (i : ℚ) ^ 2) *
              (((-1 : ℚ) ^ (i - 1) * (-1 : ℚ) ^ (i - 1)) *
                (((p - 1).choose (i - 1) : ℚ) * ((2 * p - 1).choose (i - 1) : ℚ)) -
                (1 - 3 * (p : ℚ) * harmh (i - 1) +
                  (p : ℚ) ^ 2 * (9 * harmh (i - 1) ^ 2 - 5 * harmh2 (i - 1)) / 2)) := by
                rw [hsq, one_mul]; ring
        _ = _ := by ring
    push_cast at hrew ⊢
    rw [hrew]
    have htr1 := choose_mp_sub_one_trunc2 p 1 i hp le_rfl hi1 hi2
    have htr2 := choose_mp_sub_one_trunc2 p 2 i hp (by norm_num) hi1 hi2
    simp only [one_mul, Nat.cast_one] at htr1
    set Y1 := 1 - (p : ℚ) * harmh (i - 1) + (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) / 2
    set Y2 := 1 - 2 * (p : ℚ) * harmh (i - 1) + (2 * (p : ℚ)) ^ 2 * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) / 2
    have hhh := harmh_pDiv0 (p := p) hp (by omega : i - 1 < p)
    have hhh2 := harmh2_pDiv0 (p := p) hp (by omega : i - 1 < p)
    have hdiff0 : pDiv p 0 (harmh (i - 1) ^ 2 - harmh2 (i - 1)) :=
      pDiv_sub hp (by simpa using pDiv_pow (n := 2) hp hhh) hhh2
    have hY1_0 : pDiv p 0 Y1 := by
      have h1 : pDiv p 0 ((p : ℚ) * harmh (i - 1)) := pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_one p hp) hhh)
      have h2 : pDiv p 0 ((p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) / (2 : ℕ)) :=
        pDiv_div_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
          (pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_pow p 2 hp) hdiff0))
      have : Y1 = 1 - (p : ℚ) * harmh (i - 1) + (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) / (2 : ℕ) := by
        push_cast; rfl
      rw [this]; exact pDiv_add hp (pDiv_sub hp (pDiv_nat_zero hp 1) h1) h2
    have hY2_0 : pDiv p 0 Y2 := by
      have h1 : pDiv p 0 (2 * (p : ℚ) * harmh (i - 1)) :=
        pDiv_mono (by omega) (pDiv_mul hp (pDiv_mul hp (pDiv_nat_zero hp 2) (pDiv_p_one p hp)) hhh)
      have h2 : pDiv p 0 (2 * (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 - harmh2 (i - 1))) :=
        pDiv_mono (by omega) (pDiv_mul hp (pDiv_mul hp (pDiv_nat_zero hp 2) (pDiv_p_pow p 2 hp)) hdiff0)
      have : Y2 = 1 - 2 * (p : ℚ) * harmh (i - 1) + 2 * (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) := by
        dsimp only [Y2]; ring
      rw [this]; exact pDiv_add hp (pDiv_sub hp (pDiv_nat_zero hp 1) h1) h2
    have hX1_0 : pDiv p 0 X1 := by
      have : X1 = (X1 - Y1) + Y1 := by ring
      rw [this]; exact pDiv_add hp (pDiv_mono (by omega) htr1) hY1_0
    have hprod_diff : pDiv p 3 (X1 * X2 - Y1 * Y2) := by
      have : X1 * X2 - Y1 * Y2 = X1 * (X2 - Y2) + (X1 - Y1) * Y2 := by ring
      rw [this]
      have htr2' : pDiv p 3 (X2 - Y2) := by simpa [X2, Y2] using htr2
      exact pDiv_add hp (by simpa using pDiv_mul hp hX1_0 htr2') (by simpa using pDiv_mul hp htr1 hY2_0)
    have hY1Y2 : pDiv p 3 (Y1 * Y2 -
        (1 - 3 * (p : ℚ) * harmh (i - 1) +
          (p : ℚ) ^ 2 * (9 * harmh (i - 1) ^ 2 - 5 * harmh2 (i - 1)) / 2)) := by
      have hrewY : Y1 * Y2 -
          (1 - 3 * (p : ℚ) * harmh (i - 1) +
            (p : ℚ) ^ 2 * (9 * harmh (i - 1) ^ 2 - 5 * harmh2 (i - 1)) / 2) =
          (p : ℚ) ^ 3 * (-3 * harmh (i - 1) * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) +
            (p : ℚ) * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) ^ 2) := by
        dsimp only [Y1, Y2]; ring
      rw [hrewY]
      have ht1 : pDiv p 0 (-3 * harmh (i - 1) * (harmh (i - 1) ^ 2 - harmh2 (i - 1))) := by
        simpa using pDiv_mul hp (pDiv_mul hp (pDiv_int_zero hp (-3)) hhh) hdiff0
      have ht2 : pDiv p 0 ((p : ℚ) * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) ^ 2) :=
        pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_one p hp) (by simpa using pDiv_pow (n := 2) hp hdiff0))
      simpa using pDiv_mul hp (pDiv_p_pow p 3 hp) (pDiv_add hp ht1 ht2)
    have hdiff3 : pDiv p 3 (X1 * X2 -
        (1 - 3 * (p : ℚ) * harmh (i - 1) +
          (p : ℚ) ^ 2 * (9 * harmh (i - 1) ^ 2 - 5 * harmh2 (i - 1)) / 2)) := by
      have : X1 * X2 - (1 - 3 * (p : ℚ) * harmh (i - 1) +
            (p : ℚ) ^ 2 * (9 * harmh (i - 1) ^ 2 - 5 * harmh2 (i - 1)) / 2) =
          (X1 * X2 - Y1 * Y2) + (Y1 * Y2 - (1 - 3 * (p : ℚ) * harmh (i - 1) +
            (p : ℚ) ^ 2 * (9 * harmh (i - 1) ^ 2 - 5 * harmh2 (i - 1)) / 2)) := by ring
      rw [this]; exact pDiv_add hp hprod_diff hY1Y2
    have hinv := inv_pow_lt_p_pDiv0 (k := 2) hp hi1 hi2
    simpa using pDiv_mul hp (pDiv_mul hp (pDiv_mul hp (pDiv_nat_zero hp 2) (pDiv_p_pow p 2 hp)) hinv) hdiff3
  -- Combine to get Eq1 and Eq2!
  rw [hvand1] at hL1
  rw [hvand2] at hL2
  have hEq1 : pDiv p 5 ((p : ℚ) ^ 3 * harmU1 p - (p : ℚ) ^ 4 * harmU2 p + 3 * (p : ℚ) * harmH p 1) := by
    have h2Eq1 : pDiv p 5 ((2 : ℕ) * ((p : ℚ) ^ 3 * harmU1 p - (p : ℚ) ^ 4 * harmU2 p + 3 * (p : ℚ) * harmH p 1)) := by
      have hrew : ((2 : ℕ) : ℚ) * ((p : ℚ) ^ 3 * harmU1 p - (p : ℚ) ^ 4 * harmU2 p + 3 * (p : ℚ) * harmH p 1) =
          ((((2 * p).choose p : ℚ) - 2) - ((p : ℚ) ^ 2 * harmH p 2 - 2 * (p : ℚ) ^ 3 * harmU1 p +
            2 * (p : ℚ) ^ 4 * harmU2 p - (p : ℚ) ^ 4 * harmU3 p)) -
          (((2 * p).choose p : ℚ) - 2 - 4 * (p : ℚ) * harmH p 1) +
          (2 * (p : ℚ) * harmH p 1 + (p : ℚ) ^ 2 * harmH p 2) - (p : ℚ) ^ 4 * harmU3 p := by
        push_cast; ring
      rw [hrew]
      exact pDiv_sub hp (pDiv_add hp (pDiv_sub hp hL1 hC2p) hH12) hU3_5
    exact pDiv_cancel_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega) h2Eq1
  have hEq2 : pDiv p 5 (2 * (p : ℚ) ^ 3 * harmU1 p - 3 * (p : ℚ) ^ 4 * harmU2 p + 6 * (p : ℚ) * harmH p 1) := by
    have h3Eq2 : pDiv p 5 ((3 : ℕ) * (2 * (p : ℚ) ^ 3 * harmU1 p - 3 * (p : ℚ) ^ 4 * harmU2 p + 6 * (p : ℚ) * harmH p 1)) := by
      have hrew : ((3 : ℕ) : ℚ) * (2 * (p : ℚ) ^ 3 * harmU1 p - 3 * (p : ℚ) ^ 4 * harmU2 p + 6 * (p : ℚ) * harmH p 1) =
          ((((3 * p).choose p : ℚ) - 1 - ((2 * p).choose p : ℚ)) -
            (2 * (p : ℚ) ^ 2 * harmH p 2 - 6 * (p : ℚ) ^ 3 * harmU1 p +
              9 * (p : ℚ) ^ 4 * harmU2 p - 5 * (p : ℚ) ^ 4 * harmU3 p)) -
          ((((3 * p).choose p : ℚ) - 3 - 18 * (p : ℚ) * harmH p 1) -
            (((2 * p).choose p : ℚ) - 2 - 4 * (p : ℚ) * harmH p 1)) +
          2 * (2 * (p : ℚ) * harmH p 1 + (p : ℚ) ^ 2 * harmH p 2) - 5 * ((p : ℚ) ^ 4 * harmU3 p) := by
        push_cast; ring
      rw [hrew]
      have h2H12 : pDiv p 5 (2 * (2 * (p : ℚ) * harmH p 1 + (p : ℚ) ^ 2 * harmH p 2)) := by
        simpa using pDiv_mul hp (pDiv_nat_zero hp 2) hH12
      have h5U3 : pDiv p 5 (5 * ((p : ℚ) ^ 4 * harmU3 p)) := by
        simpa using pDiv_mul hp (pDiv_nat_zero hp 5) hU3_5
      exact pDiv_sub hp (pDiv_add hp (pDiv_sub hp hL2 (pDiv_sub hp hC3p hC2p)) h2H12) h5U3
    exact pDiv_cancel_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega) h3Eq2
  have hU2 : pDiv p 5 ((p : ℚ) ^ 4 * harmU2 p) := by
    have hrew : (p : ℚ) ^ 4 * harmU2 p =
        2 * ((p : ℚ) ^ 3 * harmU1 p - (p : ℚ) ^ 4 * harmU2 p + 3 * (p : ℚ) * harmH p 1) -
        (2 * (p : ℚ) ^ 3 * harmU1 p - 3 * (p : ℚ) ^ 4 * harmU2 p + 6 * (p : ℚ) * harmH p 1) := by ring
    rw [hrew]
    exact pDiv_sub hp (by simpa using pDiv_mul hp (pDiv_nat_zero hp 2) hEq1) hEq2
  have hU1 : pDiv p 5 ((p : ℚ) ^ 3 * harmU1 p + 3 * (p : ℚ) * harmH p 1) := by
    have hrew : (p : ℚ) ^ 3 * harmU1 p + 3 * (p : ℚ) * harmH p 1 =
        ((p : ℚ) ^ 3 * harmU1 p - (p : ℚ) ^ 4 * harmU2 p + 3 * (p : ℚ) * harmH p 1) +
        (p : ℚ) ^ 4 * harmU2 p := by ring
    rw [hrew]
    exact pDiv_add hp hEq1 hU2
  exact ⟨hU2, hU1⟩

-- ============================================================================
-- Section 5: 1D sums t1 and s1 mod p^5, 2D sums t2 and s2 mod p^5,
--            and final prime-level congruences (parts 3 and 4 of main!)
-- ============================================================================

-- Double sum ∑_{i, j ∈ Ico 1 p, i + j < p} 1/(i^2 * j^2) ≡ 0 (mod p)
lemma double_inv_sq_sum_lt_pDiv1 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    pDiv p 1 (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
      if i + j < p then (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) else 0) := by
  set Slt := ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
      if i + j < p then (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) else 0
  set Sgt := ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
      if p < i + j then (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) else 0
  set Seq := ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
      if i + j = p then (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) else 0
  have hdiff : pDiv p 1 (Slt - Sgt) := by
    have hrev : Slt = ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
        if p < i + j then (1 : ℚ) / (((p - i : ℕ) : ℚ) ^ 2 * ((p - j : ℕ) : ℚ) ^ 2) else 0 := by
      dsimp only [Slt]
      refine Finset.sum_bij (fun i _ => p - i) ?_ ?_ ?_ ?_
      · intro i hi; simp only [mem_Ico] at hi ⊢; omega
      · intro i₁ hi₁ i₂ hi₂ h; simp only [mem_Ico] at hi₁ hi₂; omega
      · intro v hv; exact ⟨p - v, by simp only [mem_Ico] at hv ⊢; omega, by simp only [mem_Ico] at hv; omega⟩
      · intro i hi
        refine Finset.sum_bij (fun j _ => p - j) ?_ ?_ ?_ ?_
        · intro j hj; simp only [mem_Ico] at hj ⊢; omega
        · intro j₁ hj₁ j₂ hj₂ h; simp only [mem_Ico] at hj₁ hj₂; omega
        · intro w hw; exact ⟨p - w, by simp only [mem_Ico] at hw ⊢; omega, by simp only [mem_Ico] at hw; omega⟩
        · intro j hj
          simp only [mem_Ico] at hi hj
          have hiff : i + j < p ↔ p < (p - i) + (p - j) := by omega
          simp only [Nat.sub_sub_self (by omega : i ≤ p), Nat.sub_sub_self (by omega : j ≤ p), hiff]
    rw [hrev]
    dsimp only [Sgt]
    rw [← sum_sub_distrib]
    apply pDiv_sum hp; intro i hi
    rw [← sum_sub_distrib]
    apply pDiv_sum hp; intro j hj
    by_cases hgt : p < i + j
    · rw [if_pos hgt, if_pos hgt]
      have hi1 := (mem_Ico.mp hi).1; have hi2 := (mem_Ico.mp hi).2
      have hj1 := (mem_Ico.mp hj).1; have hj2 := (mem_Ico.mp hj).2
      have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hsi : ((p - i : ℕ) : ℚ) = (p : ℚ) - (i : ℚ) := Nat.cast_sub (by omega)
      have hsj : ((p - j : ℕ) : ℚ) = (p : ℚ) - (j : ℚ) := Nat.cast_sub (by omega)
      have hpi0 : (p : ℚ) - (i : ℚ) ≠ 0 := by rw [← hsi]; exact Nat.cast_ne_zero.mpr (by omega)
      have hpj0 : (p : ℚ) - (j : ℚ) ≠ 0 := by rw [← hsj]; exact Nat.cast_ne_zero.mpr (by omega)
      have hrew : (1 : ℚ) / (((p - i : ℕ) : ℚ) ^ 2 * ((p - j : ℕ) : ℚ) ^ 2) -
          (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) =
          (p : ℚ) * (-(p : ℚ) ^ 3 + 2 * ((i : ℚ) + (j : ℚ)) * (p : ℚ) ^ 2 -
            ((i : ℚ) ^ 2 + 4 * (i : ℚ) * (j : ℚ) + (j : ℚ) ^ 2) * (p : ℚ) +
            2 * (i : ℚ) * (j : ℚ) * ((i : ℚ) + (j : ℚ))) *
          ((1 : ℚ) / ((p - i : ℕ) : ℚ) ^ 2) * ((1 : ℚ) / ((p - j : ℕ) : ℚ) ^ 2) *
          ((1 : ℚ) / (i : ℚ) ^ 2) * ((1 : ℚ) / (j : ℚ) ^ 2) := by
        rw [hsi, hsj]; field_simp [hi0, hj0, hpi0, hpj0]; ring
      rw [hrew]
      have hnum : pDiv p 0 (-(p : ℚ) ^ 3 + 2 * ((i : ℚ) + (j : ℚ)) * (p : ℚ) ^ 2 -
          ((i : ℚ) ^ 2 + 4 * (i : ℚ) * (j : ℚ) + (j : ℚ) ^ 2) * (p : ℚ) +
          2 * (i : ℚ) * (j : ℚ) * ((i : ℚ) + (j : ℚ))) := by
        convert pDiv_int_zero hp (-(p : ℤ) ^ 3 + 2 * ((i : ℤ) + (j : ℤ)) * (p : ℤ) ^ 2 -
          ((i : ℤ) ^ 2 + 4 * (i : ℤ) * (j : ℤ) + (j : ℤ) ^ 2) * (p : ℤ) +
          2 * (i : ℤ) * (j : ℤ) * ((i : ℤ) + (j : ℤ))) using 1
        push_cast; ring
      have h1 := inv_pow_lt_p_pDiv0 (k := 2) hp (by omega : 1 ≤ p - i) (by omega : p - i < p)
      have h2 := inv_pow_lt_p_pDiv0 (k := 2) hp (by omega : 1 ≤ p - j) (by omega : p - j < p)
      have h3 := inv_pow_lt_p_pDiv0 (k := 2) hp hi1 hi2
      have h4 := inv_pow_lt_p_pDiv0 (k := 2) hp hj1 hj2
      simpa using pDiv_mul hp (pDiv_mul hp (pDiv_mul hp (pDiv_mul hp
        (pDiv_mul hp (pDiv_p_one p hp) hnum) h1) h2) h3) h4
    · simp [hgt, pDiv_zero p 1 hp]
  have hSeq : pDiv p 1 Seq := by
    have hSeq_eq : Seq = ∑ i ∈ Ico 1 p, (1 : ℚ) / ((i : ℚ) ^ 2 * ((p - i : ℕ) : ℚ) ^ 2) := by
      dsimp only [Seq]
      apply sum_congr rfl; intro i hi
      have hi1 := (mem_Ico.mp hi).1; have hi2 := (mem_Ico.mp hi).2
      have hcond : ∀ j ∈ Ico 1 p,
          (if i + j = p then (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) else 0) =
          (if j = p - i then (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) else 0) := by
        intro j _; by_cases h : i + j = p <;> by_cases h' : j = p - i <;> simp [h, h'] <;> omega
      rw [sum_congr rfl hcond, sum_ite_eq' (Ico 1 p) (p - i), if_pos (mem_Ico.mpr ⟨by omega, by omega⟩)]
    rw [hSeq_eq]
    have hsub : pDiv p 1 ((∑ i ∈ Ico 1 p, (1 : ℚ) / ((i : ℚ) ^ 2 * ((p - i : ℕ) : ℚ) ^ 2)) - harmH p 4) := by
      unfold harmH
      rw [← sum_sub_distrib]
      apply pDiv_sum hp; intro i hi
      have hi1 := (mem_Ico.mp hi).1; have hi2 := (mem_Ico.mp hi).2
      have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hsi : ((p - i : ℕ) : ℚ) = (p : ℚ) - (i : ℚ) := Nat.cast_sub (by omega)
      have hpi0 : (p : ℚ) - (i : ℚ) ≠ 0 := by rw [← hsi]; exact Nat.cast_ne_zero.mpr (by omega)
      have hrew : (1 : ℚ) / ((i : ℚ) ^ 2 * ((p - i : ℕ) : ℚ) ^ 2) - (1 : ℚ) / (i : ℚ) ^ 4 =
          (p : ℚ) * (2 * (i : ℚ) - (p : ℚ)) * ((1 : ℚ) / ((p - i : ℕ) : ℚ) ^ 2) * ((1 : ℚ) / (i : ℚ) ^ 4) := by
        rw [hsi]; field_simp [hi0, hpi0]; ring
      rw [hrew]
      have hnum : pDiv p 0 (2 * (i : ℚ) - (p : ℚ)) := by
        simpa using pDiv_int_zero hp (2 * (i : ℤ) - (p : ℤ))
      have h1 := inv_pow_lt_p_pDiv0 (k := 2) hp (by omega : 1 ≤ p - i) (by omega : p - i < p)
      have h2 := inv_pow_lt_p_pDiv0 (k := 4) hp hi1 hi2
      simpa using pDiv_mul hp (pDiv_mul hp (pDiv_mul hp (pDiv_p_one p hp) hnum) h1) h2
    have : (∑ i ∈ Ico 1 p, (1 : ℚ) / ((i : ℚ) ^ 2 * ((p - i : ℕ) : ℚ) ^ 2)) =
        ((∑ i ∈ Ico 1 p, (1 : ℚ) / ((i : ℚ) ^ 2 * ((p - i : ℕ) : ℚ) ^ 2)) - harmH p 4) + harmH p 4 := by ring
    rw [this]; exact pDiv_add hp hsub (harmH4_pDiv_one p hp hp7)
  have htot : Slt + Sgt + Seq = harmH p 2 ^ 2 := by
    have hsq : harmH p 2 ^ 2 =
        ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p, (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) := by
      unfold harmH; rw [sq, sum_mul_sum]
      apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring
    rw [hsq]
    dsimp only [Slt, Sgt, Seq]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro i _
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro j _
    rcases lt_trichotomy (i + j) p with hlt | heq | hgt
    · simp [hlt, ne_of_lt hlt, not_lt.mpr (le_of_lt hlt)]
    · simp [heq]
    · simp [hgt, ne_of_gt hgt, not_lt.mpr (le_of_lt hgt)]
  have h2Slt : pDiv p 1 ((2 : ℕ) * Slt) := by
    have hrew : ((2 : ℕ) : ℚ) * Slt = (Slt - Sgt) + (harmH p 2 ^ 2 - Seq) := by
      push_cast; linarith
    rw [hrew]
    have hH2sq : pDiv p 1 (harmH p 2 ^ 2) :=
      pDiv_mono (by omega) (pDiv_pow (n := 2) hp (harmH2_pDiv_one p hp (by omega)))
    exact pDiv_add hp hdiff (pDiv_sub hp hH2sq hSeq)
  exact pDiv_cancel_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega) h2Slt

-- t1: 3 * ∑_{i=1}^{p-1} C(4p - i, 3p) * C(p, i)^2 ≡ -15 * p * H1 (mod p^5)
lemma t1_pDiv5 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    pDiv p 5 (3 * (∑ i ∈ Ico 1 p, (((4 * p - i).choose (3 * p) : ℚ) * ((p.choose i : ℚ) ^ 2))) +
      15 * (p : ℚ) * harmH p 1) := by
  -- Show ∑_{i=1}^{p-1} C(4p - i, 3p) * C(p, i)^2 ≡ p^2 * H2 + p^3 * U1 + p^4 * (U2 / 2 + 13/2 * U3) (mod p^5)
  have hsum : pDiv p 5 ((∑ i ∈ Ico 1 p, (((4 * p - i).choose (3 * p) : ℚ) * ((p.choose i : ℚ) ^ 2))) -
      ((p : ℚ) ^ 2 * harmH p 2 + (p : ℚ) ^ 3 * harmU1 p +
        (p : ℚ) ^ 4 * harmU2 p / 2 + 13 * (p : ℚ) ^ 4 * harmU3 p / 2)) := by
    have hrhs_eq : (p : ℚ) ^ 2 * harmH p 2 + (p : ℚ) ^ 3 * harmU1 p +
        (p : ℚ) ^ 4 * harmU2 p / 2 + 13 * (p : ℚ) ^ 4 * harmU3 p / 2 =
        ∑ i ∈ Ico 1 p, (p : ℚ) ^ 2 * ((1 : ℚ) / (i : ℚ) ^ 2) *
          (1 + (p : ℚ) * harmh (i - 1) +
            (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 + 13 * harmh2 (i - 1)) / 2) := by
      unfold harmH harmU1 harmU2 harmU3
      simp only [mul_sum, sum_div, ← sum_add_distrib]
      apply sum_congr rfl; intro i _; ring
    rw [hrhs_eq, ← sum_sub_distrib]
    apply pDiv_sum hp; intro i hi
    have hi1 := (mem_Ico.mp hi).1; have hi2 := (mem_Ico.mp hi).2
    have hch := choose_mp_eq p 1 i le_rfl hi1 hi2
    simp only [one_mul, Nat.cast_one] at hch
    have hsym : (4 * p - i).choose (3 * p) = (3 * p + (p - i)).choose (p - i) := by
      rw [← Nat.choose_symm (by omega : 3 * p ≤ 4 * p - i)]
      have e1 : 4 * p - i - 3 * p = p - i := by omega
      have e2 : 4 * p - i = 3 * p + (p - i) := by omega
      rw [e1, e2]
    rw [hsym, hch, mul_pow]
    set X := ((3 * p + (p - i)).choose (p - i) : ℚ)
    set Z := (-1 : ℚ) ^ (i - 1) * ((p - 1).choose (i - 1) : ℚ)
    have hrew : X * (((p : ℚ) / (i : ℚ)) ^ 2 * ((p - 1).choose (i - 1) : ℚ) ^ 2) -
        (p : ℚ) ^ 2 * ((1 : ℚ) / (i : ℚ) ^ 2) *
          (1 + (p : ℚ) * harmh (i - 1) + (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 + 13 * harmh2 (i - 1)) / 2) =
        (p : ℚ) ^ 2 * ((1 : ℚ) / (i : ℚ) ^ 2) *
          (X * Z ^ 2 - (1 + (p : ℚ) * harmh (i - 1) +
            (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 + 13 * harmh2 (i - 1)) / 2)) := by
      dsimp only [Z]
      have hsq : ((-1 : ℚ) ^ (i - 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [div_pow, mul_pow, hsq, one_mul]; ring
    rw [hrew]
    -- Expand X mod p^3 using choose_mp_add_trunc2 + harmonic reflection!
    have hXtr := choose_mp_add_trunc2 p 3 (p - i) hp (by omega)
    have hZtr := choose_mp_sub_one_trunc2 p 1 i hp le_rfl hi1 hi2
    simp only [one_mul, Nat.cast_one] at hZtr
    have hhref := harmh_reflect_pDiv2 p (i - 1) hp hp7 (by omega)
    have hh2ref := harmh2_reflect_pDiv1 p (i - 1) hp hp7 (by omega)
    have hsub_idx : p - 1 - (i - 1) = p - i := by omega
    rw [hsub_idx] at hhref hh2ref
    have hhh := harmh_pDiv0 (p := p) hp (by omega : i - 1 < p)
    have hhh2 := harmh2_pDiv0 (p := p) hp (by omega : i - 1 < p)
    have hhp := harmh_pDiv0 (p := p) hp (by omega : p - i < p)
    set YX := 1 + 3 * (p : ℚ) * harmh (i - 1) +
        (p : ℚ) ^ 2 * (9 * harmh (i - 1) ^ 2 + 15 * harmh2 (i - 1)) / 2
    set YZ := 1 - 2 * (p : ℚ) * harmh (i - 1) +
        (p : ℚ) ^ 2 * (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1))
    -- Show pDiv p 3 (X - YX)
    have hX_YX : pDiv p 3 (X - YX) := by
      set X0 := 1 + (3 : ℚ) * (p : ℚ) * harmh (p - i) +
          ((3 : ℚ) * (p : ℚ)) ^ 2 * (harmh (p - i) ^ 2 - harmh2 (p - i)) / 2
      have hX0_YX : pDiv p 3 (X0 - YX) := by
        have h1 : pDiv p 3 (3 * (p : ℚ) * (harmh (p - i) - (harmh (i - 1) + (p : ℚ) * harmh2 (i - 1)))) := by
          simpa [mul_assoc] using pDiv_mul hp (pDiv_mul hp (pDiv_nat_zero hp 3) (pDiv_p_one p hp)) hhref
        have hsq_diff : pDiv p 1 (harmh (p - i) ^ 2 - harmh (i - 1) ^ 2) := by
          have : harmh (p - i) ^ 2 - harmh (i - 1) ^ 2 =
              (harmh (p - i) + harmh (i - 1)) *
                ((harmh (p - i) - (harmh (i - 1) + (p : ℚ) * harmh2 (i - 1))) + (p : ℚ) * harmh2 (i - 1)) := by
            ring
          rw [this]
          have hfac1 : pDiv p 1 ((harmh (p - i) - (harmh (i - 1) + (p : ℚ) * harmh2 (i - 1))) +
              (p : ℚ) * harmh2 (i - 1)) :=
            pDiv_add hp (pDiv_mono (by omega) hhref) (by simpa using pDiv_mul hp (pDiv_p_one p hp) hhh2)
          simpa using pDiv_mul hp (pDiv_add hp hhp hhh) hfac1
        have h2 : pDiv p 3 (9 * (p : ℚ) ^ 2 * ((harmh (p - i) ^ 2 - harmh (i - 1) ^ 2) -
            (harmh2 (p - i) + harmh2 (i - 1))) / (2 : ℕ)) := by
          apply pDiv_div_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
          have hsub := pDiv_sub hp hsq_diff hh2ref
          simpa [mul_assoc] using pDiv_mul hp (pDiv_mul hp (pDiv_nat_zero hp 9) (pDiv_p_pow p 2 hp)) hsub
        have hrew2 : X0 - YX =
            3 * (p : ℚ) * (harmh (p - i) - (harmh (i - 1) + (p : ℚ) * harmh2 (i - 1))) +
            9 * (p : ℚ) ^ 2 * ((harmh (p - i) ^ 2 - harmh (i - 1) ^ 2) -
              (harmh2 (p - i) + harmh2 (i - 1))) / (2 : ℕ) := by
          dsimp only [X0, YX]; push_cast; ring
        rw [hrew2]; exact pDiv_add hp h1 h2
      have : X - YX = (X - X0) + (X0 - YX) := by ring
      rw [this]; exact pDiv_add hp (by simpa [X, X0] using hXtr) hX0_YX
    -- Show pDiv p 3 (Z^2 - YZ)
    have hZ_YZ : pDiv p 3 (Z ^ 2 - YZ) := by
      set Z0 := 1 - (p : ℚ) * harmh (i - 1) + (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) / 2
      have hdiff0 : pDiv p 0 (harmh (i - 1) ^ 2 - harmh2 (i - 1)) :=
        pDiv_sub hp (by simpa using pDiv_pow (n := 2) hp hhh) hhh2
      have hZ0_0 : pDiv p 0 Z0 := by
        have h1 : pDiv p 0 ((p : ℚ) * harmh (i - 1)) := pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_one p hp) hhh)
        have h2 : pDiv p 0 ((p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) / (2 : ℕ)) :=
          pDiv_div_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
            (pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_pow p 2 hp) hdiff0))
        have : Z0 = 1 - (p : ℚ) * harmh (i - 1) + (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) / (2 : ℕ) := by
          push_cast; rfl
        rw [this]; exact pDiv_add hp (pDiv_sub hp (pDiv_nat_zero hp 1) h1) h2
      have hZ_0 : pDiv p 0 Z := by
        have : Z = (Z - Z0) + Z0 := by ring
        rw [this]; exact pDiv_add hp (pDiv_mono (by omega) hZtr) hZ0_0
      have h1 : pDiv p 3 (Z ^ 2 - Z0 ^ 2) := by
        have : Z ^ 2 - Z0 ^ 2 = (Z + Z0) * (Z - Z0) := by ring
        rw [this]; simpa using pDiv_mul hp (pDiv_add hp hZ_0 hZ0_0) hZtr
      have h2 : pDiv p 3 (Z0 ^ 2 - YZ) := by
        have hrew2 : Z0 ^ 2 - YZ = (p : ℚ) ^ 3 * (-harmh (i - 1) * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) +
            (p : ℚ) * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) ^ 2 / (4 : ℕ)) := by
          dsimp only [Z0, YZ]; push_cast; ring
        rw [hrew2]
        have ht1 : pDiv p 0 (-harmh (i - 1) * (harmh (i - 1) ^ 2 - harmh2 (i - 1))) := by
          simpa using pDiv_mul hp (pDiv_neg hhh) hdiff0
        have ht2 : pDiv p 0 ((p : ℚ) * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) ^ 2 / (4 : ℕ)) :=
          pDiv_div_nat_unit hp (fun h => by
            have : p ∣ 2 ^ 2 := by simpa using h
            have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow this); omega)
            (pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_one p hp) (by simpa using pDiv_pow (n := 2) hp hdiff0)))
        simpa using pDiv_mul hp (pDiv_p_pow p 3 hp) (pDiv_add hp ht1 ht2)
      have : Z ^ 2 - YZ = (Z ^ 2 - Z0 ^ 2) + (Z0 ^ 2 - YZ) := by ring
      rw [this]; exact pDiv_add hp h1 h2
    -- Combine X * Z^2 ≡ YX * YZ ≡ 1 + p*h + p^2*(h^2 + 13*h2)/2 (mod p^3)!
    have hYX0 : pDiv p 0 YX := by
      have h1 : pDiv p 0 (3 * (p : ℚ) * harmh (i - 1)) :=
        pDiv_mono (by omega) (pDiv_mul hp (pDiv_mul hp (pDiv_nat_zero hp 3) (pDiv_p_one p hp)) hhh)
      have h2 : pDiv p 0 ((p : ℚ) ^ 2 * (9 * harmh (i - 1) ^ 2 + 15 * harmh2 (i - 1)) / (2 : ℕ)) :=
        pDiv_div_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
          (pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_pow p 2 hp)
            (pDiv_add hp (by simpa using pDiv_mul hp (pDiv_nat_zero hp 9) (pDiv_pow (n := 2) hp hhh))
              (by simpa using pDiv_mul hp (pDiv_nat_zero hp 15) hhh2))))
      have : YX = 1 + 3 * (p : ℚ) * harmh (i - 1) +
          (p : ℚ) ^ 2 * (9 * harmh (i - 1) ^ 2 + 15 * harmh2 (i - 1)) / (2 : ℕ) := by push_cast; rfl
      rw [this]; exact pDiv_add hp (pDiv_add hp (pDiv_nat_zero hp 1) h1) h2
    have hYZ0 : pDiv p 0 YZ := by
      have h1 : pDiv p 0 (2 * (p : ℚ) * harmh (i - 1)) :=
        pDiv_mono (by omega) (pDiv_mul hp (pDiv_mul hp (pDiv_nat_zero hp 2) (pDiv_p_one p hp)) hhh)
      have h2 : pDiv p 0 ((p : ℚ) ^ 2 * (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1))) :=
        pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_pow p 2 hp)
          (pDiv_sub hp (by simpa using pDiv_mul hp (pDiv_nat_zero hp 2) (pDiv_pow (n := 2) hp hhh)) hhh2))
      exact pDiv_add hp (pDiv_sub hp (pDiv_nat_zero hp 1) h1) h2
    have hX0 : pDiv p 0 X := by
      have : X = (X - YX) + YX := by ring
      rw [this]; exact pDiv_add hp (pDiv_mono (by omega) hX_YX) hYX0
    have hprod1 : pDiv p 3 (X * Z ^ 2 - YX * YZ) := by
      have : X * Z ^ 2 - YX * YZ = X * (Z ^ 2 - YZ) + (X - YX) * YZ := by ring
      rw [this]; exact pDiv_add hp (by simpa using pDiv_mul hp hX0 hZ_YZ) (by simpa using pDiv_mul hp hX_YX hYZ0)
    have hprod2 : pDiv p 3 (YX * YZ - (1 + (p : ℚ) * harmh (i - 1) +
        (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 + 13 * harmh2 (i - 1)) / 2)) := by
      have hrew2 : YX * YZ - (1 + (p : ℚ) * harmh (i - 1) +
          (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 + 13 * harmh2 (i - 1)) / 2) =
          (p : ℚ) ^ 3 * ((-3 * harmh (i - 1) ^ 3 - 18 * harmh (i - 1) * harmh2 (i - 1)) +
            (p : ℚ) * ((9 * harmh (i - 1) ^ 2 + 15 * harmh2 (i - 1)) *
              (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1))) / (2 : ℕ)) := by
        dsimp only [YX, YZ]; push_cast; ring
      rw [hrew2]
      have ha : pDiv p 0 (-3 * harmh (i - 1) ^ 3 - 18 * harmh (i - 1) * harmh2 (i - 1)) :=
        pDiv_sub hp
          (by simpa using pDiv_mul hp (pDiv_int_zero hp (-3)) (pDiv_pow (n := 3) hp hhh))
          (by simpa using pDiv_mul hp (pDiv_mul hp (pDiv_nat_zero hp 18) hhh) hhh2)
      have hb : pDiv p 0 ((p : ℚ) * ((9 * harmh (i - 1) ^ 2 + 15 * harmh2 (i - 1)) *
            (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1))) / (2 : ℕ)) := by
        have hf1 : pDiv p 0 (9 * harmh (i - 1) ^ 2 + 15 * harmh2 (i - 1)) :=
          pDiv_add hp
            (by simpa using pDiv_mul hp (pDiv_nat_zero hp 9) (pDiv_pow (n := 2) hp hhh))
            (by simpa using pDiv_mul hp (pDiv_nat_zero hp 15) hhh2)
        have hf2 : pDiv p 0 (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1)) :=
          pDiv_sub hp
            (by simpa using pDiv_mul hp (pDiv_nat_zero hp 2) (pDiv_pow (n := 2) hp hhh))
            hhh2
        have hprod0 : pDiv p 0 ((9 * harmh (i - 1) ^ 2 + 15 * harmh2 (i - 1)) *
            (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1))) := by
          simpa using pDiv_mul hp hf1 hf2
        exact pDiv_div_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
          (pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_one p hp) hprod0))
      simpa using pDiv_mul hp (pDiv_p_pow p 3 hp) (pDiv_add hp ha hb)
    have htot3 : pDiv p 3 (X * Z ^ 2 - (1 + (p : ℚ) * harmh (i - 1) +
        (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 + 13 * harmh2 (i - 1)) / 2)) := by
      have : X * Z ^ 2 - (1 + (p : ℚ) * harmh (i - 1) +
            (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 + 13 * harmh2 (i - 1)) / 2) =
          (X * Z ^ 2 - YX * YZ) + (YX * YZ - (1 + (p : ℚ) * harmh (i - 1) +
            (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 + 13 * harmh2 (i - 1)) / 2)) := by ring
      rw [this]; exact pDiv_add hp hprod1 hprod2
    have hinv := inv_pow_lt_p_pDiv0 (k := 2) hp hi1 hi2
    simpa using pDiv_mul hp (pDiv_mul hp (pDiv_p_pow p 2 hp) hinv) htot3
  -- Plug in H2, U1, U2, U3!
  have h12 := harmH1_H2_pDiv_five p hp hp7
  have ⟨hU2, hU1⟩ := harmU1_U2_pDiv5 p hp hp7
  have hU3 := pDiv_mul hp (pDiv_p_pow p 4 hp) (harmU3_pDiv1 p hp hp7)
  have hU2d : pDiv p 5 ((p : ℚ) ^ 4 * harmU2 p / (2 : ℕ)) :=
    pDiv_div_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega) hU2
  have hU3d : pDiv p 5 (13 * ((p : ℚ) ^ 4 * harmU3 p) / (2 : ℕ)) :=
    pDiv_div_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
      (by simpa using pDiv_mul hp (pDiv_nat_zero hp 13) hU3)
  have hinner : pDiv p 5 ((∑ i ∈ Ico 1 p, (((4 * p - i).choose (3 * p) : ℚ) * ((p.choose i : ℚ) ^ 2))) +
      5 * (p : ℚ) * harmH p 1) := by
    have hrew : (∑ i ∈ Ico 1 p, (((4 * p - i).choose (3 * p) : ℚ) * ((p.choose i : ℚ) ^ 2))) +
        5 * (p : ℚ) * harmH p 1 =
        ((∑ i ∈ Ico 1 p, (((4 * p - i).choose (3 * p) : ℚ) * ((p.choose i : ℚ) ^ 2))) -
          ((p : ℚ) ^ 2 * harmH p 2 + (p : ℚ) ^ 3 * harmU1 p +
            (p : ℚ) ^ 4 * harmU2 p / 2 + 13 * (p : ℚ) ^ 4 * harmU3 p / 2)) +
        (2 * (p : ℚ) * harmH p 1 + (p : ℚ) ^ 2 * harmH p 2) +
        ((p : ℚ) ^ 3 * harmU1 p + 3 * (p : ℚ) * harmH p 1) +
        (p : ℚ) ^ 4 * harmU2 p / (2 : ℕ) +
        13 * ((p : ℚ) ^ 4 * harmU3 p) / (2 : ℕ) := by push_cast; ring
    rw [hrew]
    exact pDiv_add hp (pDiv_add hp (pDiv_add hp (pDiv_add hp hsum h12) hU1) hU2d) hU3d
  have h3 : 3 * (∑ i ∈ Ico 1 p, (((4 * p - i).choose (3 * p) : ℚ) * ((p.choose i : ℚ) ^ 2))) +
      15 * (p : ℚ) * harmH p 1 =
      3 * ((∑ i ∈ Ico 1 p, (((4 * p - i).choose (3 * p) : ℚ) * ((p.choose i : ℚ) ^ 2))) +
        5 * (p : ℚ) * harmH p 1) := by ring
  rw [h3]; simpa using pDiv_mul hp (pDiv_nat_zero hp 3) hinner

-- s1: 3 * ∑_{i=1}^{p-1} (-1)^(p-1-i) * C(3p - 1, p - 1 - i) * C(p + i - 1, i)^2 ≡ 3 * p * H1 (mod p^5)
lemma s1_pDiv5 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    pDiv p 5 (3 * (∑ i ∈ Ico 1 p, ((-1 : ℚ) ^ (p - 1 - i) *
      ((3 * p - 1).choose (p - 1 - i) : ℚ) * (((p + i - 1).choose i : ℚ) ^ 2))) -
      3 * (p : ℚ) * harmH p 1) := by
  -- Use C(p + i - 1, i) = (p / i) * C(p + i - 1, i - 1)
  have hsum : pDiv p 5 ((∑ i ∈ Ico 1 p, ((-1 : ℚ) ^ (p - 1 - i) *
      ((3 * p - 1).choose (p - 1 - i) : ℚ) * (((p + i - 1).choose i : ℚ) ^ 2))) -
      ((p : ℚ) ^ 2 * harmH p 2 - (p : ℚ) ^ 3 * harmU1 p - 3 * (p : ℚ) ^ 3 * harmH p 3 +
        (p : ℚ) ^ 4 * harmU2 p / 2 + (p : ℚ) ^ 4 * harmU3 p / 2 +
        3 * (p : ℚ) ^ 4 * harmU4 p + 6 * (p : ℚ) ^ 4 * harmH p 4)) := by
    have hrhs_eq : (p : ℚ) ^ 2 * harmH p 2 - (p : ℚ) ^ 3 * harmU1 p - 3 * (p : ℚ) ^ 3 * harmH p 3 +
        (p : ℚ) ^ 4 * harmU2 p / 2 + (p : ℚ) ^ 4 * harmU3 p / 2 +
        3 * (p : ℚ) ^ 4 * harmU4 p + 6 * (p : ℚ) ^ 4 * harmH p 4 =
        ∑ i ∈ Ico 1 p, (p : ℚ) ^ 2 * ((1 : ℚ) / (i : ℚ) ^ 2) *
          (1 - (p : ℚ) * (harmh (i - 1) + 3 / (i : ℚ)) +
            (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 + harmh2 (i - 1) +
              6 * harmh (i - 1) / (i : ℚ) + 12 / (i : ℚ) ^ 2) / 2) := by
      unfold harmH harmU1 harmU2 harmU3 harmU4
      simp only [mul_sum, sum_div, ← sum_sub_distrib, ← sum_add_distrib]
      apply sum_congr rfl; intro i _; ring
    rw [hrhs_eq, ← sum_sub_distrib]
    apply pDiv_sum hp; intro i hi
    have hi1 := (mem_Ico.mp hi).1; have hi2 := (mem_Ico.mp hi).2
    have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hch : ((p + i - 1).choose i : ℚ) = ((p : ℚ) / (i : ℚ)) * ((p + (i - 1)).choose (i - 1) : ℚ) := by
      have h1 := Nat.choose_succ_right_eq (p + i - 1) (i - 1)
      have e1 : i - 1 + 1 = i := by omega
      have e2 : p + i - 1 - (i - 1) = p := by omega
      have e3 : p + i - 1 = p + (i - 1) := by omega
      rw [e1, e2, e3] at h1
      have hQ : ((p + (i - 1)).choose i : ℚ) * (i : ℚ) =
          ((p + (i - 1)).choose (i - 1) : ℚ) * (p : ℚ) := by exact_mod_cast h1
      rw [e3]; field_simp [hi0] at hQ ⊢; linarith
    rw [hch, mul_pow]
    set X := (-1 : ℚ) ^ (p - 1 - i) * ((3 * p - 1).choose (p - 1 - i) : ℚ)
    set Z := ((p + (i - 1)).choose (i - 1) : ℚ)
    have hrew : X * (((p : ℚ) / (i : ℚ)) ^ 2 * Z ^ 2) -
        (p : ℚ) ^ 2 * ((1 : ℚ) / (i : ℚ) ^ 2) *
          (1 - (p : ℚ) * (harmh (i - 1) + 3 / (i : ℚ)) +
            (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 + harmh2 (i - 1) +
              6 * harmh (i - 1) / (i : ℚ) + 12 / (i : ℚ) ^ 2) / 2) =
        (p : ℚ) ^ 2 * ((1 : ℚ) / (i : ℚ) ^ 2) *
          (X * Z ^ 2 - (1 - (p : ℚ) * (harmh (i - 1) + 3 / (i : ℚ)) +
            (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 + harmh2 (i - 1) +
              6 * harmh (i - 1) / (i : ℚ) + 12 / (i : ℚ) ^ 2) / 2)) := by
      rw [div_pow]; ring
    rw [hrew]
    -- Expand X = (-1)^(p - 1 - i) * C(3p - 1, p - 1 - i) using choose_mp_sub_one_trunc2 (with index p - i)
    -- and Z = C(p + (i - 1), i - 1) using choose_mp_add_trunc2!
    have hXtr : pDiv p 3 (X - (1 - 3 * (p : ℚ) * harmh (p - 1 - i) +
        (3 * (p : ℚ)) ^ 2 * (harmh (p - 1 - i) ^ 2 - harmh2 (p - 1 - i)) / 2)) := by
      by_cases hip : i = p - 1
      · subst hip
        simp [X, harmh, harmh2, pDiv_zero p 3 hp]
      · have htr := choose_mp_sub_one_trunc2 p 3 (p - i) hp (by norm_num) (by omega) (by omega)
        have e1 : p - i - 1 = p - 1 - i := by omega
        rw [e1] at htr
        simpa [X] using htr
    have hZtr := choose_mp_add_trunc2 p 1 (i - 1) hp (by omega)
    simp only [one_mul, Nat.cast_one] at hZtr
    have hhref := harmh_reflect_pDiv2 p i hp hp7 hi2
    have hh2ref := harmh2_reflect_pDiv1 p i hp hp7 hi2
    have hh_step : harmh i = harmh (i - 1) + (1 : ℚ) / (i : ℚ) := by
      unfold harmh
      have hIcc : Icc 1 i = insert i (Icc 1 (i - 1)) := by
        ext x; simp only [mem_Icc, mem_insert]; omega
      rw [hIcc, sum_insert (by simp; omega), add_comm]
    have hh2_step : harmh2 i = harmh2 (i - 1) + (1 : ℚ) / ((i : ℚ) ^ 2) := by
      unfold harmh2
      have hIcc : Icc 1 i = insert i (Icc 1 (i - 1)) := by
        ext x; simp only [mem_Icc, mem_insert]; omega
      rw [hIcc, sum_insert (by simp; omega), add_comm]
    have hhh := harmh_pDiv0 (p := p) hp (by omega : i - 1 < p)
    have hhh2 := harmh2_pDiv0 (p := p) hp (by omega : i - 1 < p)
    have hhi := harmh_pDiv0 (p := p) hp hi2
    have hhi2 := harmh2_pDiv0 (p := p) hp hi2
    have hhp := harmh_pDiv0 (p := p) hp (by omega : p - 1 - i < p)
    have hinv1 := inv_lt_p_pDiv0 hp hi1 hi2
    have hinv2 := inv_pow_lt_p_pDiv0 (k := 2) hp hi1 hi2
    set YX := 1 - 3 * (p : ℚ) * harmh i +
        (p : ℚ) ^ 2 * (9 * harmh i ^ 2 + 3 * harmh2 i) / 2
    set YZ := 1 + 2 * (p : ℚ) * harmh (i - 1) +
        (p : ℚ) ^ 2 * (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1))
    -- Show pDiv p 3 (X - YX)
    have hX_YX : pDiv p 3 (X - YX) := by
      set X0 := 1 - 3 * (p : ℚ) * harmh (p - 1 - i) +
          (3 * (p : ℚ)) ^ 2 * (harmh (p - 1 - i) ^ 2 - harmh2 (p - 1 - i)) / 2
      have hX0_YX : pDiv p 3 (X0 - YX) := by
        have h1 : pDiv p 3 (-3 * (p : ℚ) * (harmh (p - 1 - i) - (harmh i + (p : ℚ) * harmh2 i))) := by
          simpa [mul_assoc] using pDiv_mul hp (pDiv_mul hp (pDiv_int_zero hp (-3)) (pDiv_p_one p hp)) hhref
        have hsq_diff : pDiv p 1 (harmh (p - 1 - i) ^ 2 - harmh i ^ 2) := by
          have : harmh (p - 1 - i) ^ 2 - harmh i ^ 2 =
              (harmh (p - 1 - i) + harmh i) *
                ((harmh (p - 1 - i) - (harmh i + (p : ℚ) * harmh2 i)) + (p : ℚ) * harmh2 i) := by ring
          rw [this]
          have hfac1 : pDiv p 1 ((harmh (p - 1 - i) - (harmh i + (p : ℚ) * harmh2 i)) + (p : ℚ) * harmh2 i) :=
            pDiv_add hp (pDiv_mono (by omega) hhref) (by simpa using pDiv_mul hp (pDiv_p_one p hp) hhi2)
          simpa using pDiv_mul hp (pDiv_add hp hhp hhi) hfac1
        have h2 : pDiv p 3 (9 * (p : ℚ) ^ 2 * ((harmh (p - 1 - i) ^ 2 - harmh i ^ 2) -
            (harmh2 (p - 1 - i) + harmh2 i)) / (2 : ℕ)) := by
          apply pDiv_div_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
          have hsub := pDiv_sub hp hsq_diff hh2ref
          simpa [mul_assoc] using pDiv_mul hp (pDiv_mul hp (pDiv_nat_zero hp 9) (pDiv_p_pow p 2 hp)) hsub
        have hrew2 : X0 - YX =
            -3 * (p : ℚ) * (harmh (p - 1 - i) - (harmh i + (p : ℚ) * harmh2 i)) +
            9 * (p : ℚ) ^ 2 * ((harmh (p - 1 - i) ^ 2 - harmh i ^ 2) -
              (harmh2 (p - 1 - i) + harmh2 i)) / (2 : ℕ) := by
          dsimp only [X0, YX]; push_cast; ring
        rw [hrew2]; exact pDiv_add hp h1 h2
      have : X - YX = (X - X0) + (X0 - YX) := by ring
      rw [this]; exact pDiv_add hp hXtr hX0_YX
    -- Show pDiv p 3 (Z^2 - YZ)
    have hZ_YZ : pDiv p 3 (Z ^ 2 - YZ) := by
      set Z0 := 1 + (p : ℚ) * harmh (i - 1) + (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) / 2
      have hdiff0 : pDiv p 0 (harmh (i - 1) ^ 2 - harmh2 (i - 1)) :=
        pDiv_sub hp (by simpa using pDiv_pow (n := 2) hp hhh) hhh2
      have hZ0_0 : pDiv p 0 Z0 := by
        have h1 : pDiv p 0 ((p : ℚ) * harmh (i - 1)) := pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_one p hp) hhh)
        have h2 : pDiv p 0 ((p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) / (2 : ℕ)) :=
          pDiv_div_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
            (pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_pow p 2 hp) hdiff0))
        have : Z0 = 1 + (p : ℚ) * harmh (i - 1) + (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) / (2 : ℕ) := by
          push_cast; rfl
        rw [this]; exact pDiv_add hp (pDiv_add hp (pDiv_nat_zero hp 1) h1) h2
      have hZ_0 : pDiv p 0 Z := by
        have : Z = (Z - Z0) + Z0 := by ring
        rw [this]; exact pDiv_add hp (pDiv_mono (by omega) hZtr) hZ0_0
      have h1 : pDiv p 3 (Z ^ 2 - Z0 ^ 2) := by
        have : Z ^ 2 - Z0 ^ 2 = (Z + Z0) * (Z - Z0) := by ring
        rw [this]; simpa using pDiv_mul hp (pDiv_add hp hZ_0 hZ0_0) hZtr
      have h2 : pDiv p 3 (Z0 ^ 2 - YZ) := by
        have hrew2 : Z0 ^ 2 - YZ = (p : ℚ) ^ 3 * (harmh (i - 1) * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) +
            (p : ℚ) * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) ^ 2 / (4 : ℕ)) := by
          dsimp only [Z0, YZ]; push_cast; ring
        rw [hrew2]
        have ht1 : pDiv p 0 (harmh (i - 1) * (harmh (i - 1) ^ 2 - harmh2 (i - 1))) := by
          simpa using pDiv_mul hp hhh hdiff0
        have ht2 : pDiv p 0 ((p : ℚ) * (harmh (i - 1) ^ 2 - harmh2 (i - 1)) ^ 2 / (4 : ℕ)) :=
          pDiv_div_nat_unit hp (fun h => by
            have : p ∣ 2 ^ 2 := by simpa using h
            have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow this); omega)
            (pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_one p hp) (by simpa using pDiv_pow (n := 2) hp hdiff0)))
        simpa using pDiv_mul hp (pDiv_p_pow p 3 hp) (pDiv_add hp ht1 ht2)
      have : Z ^ 2 - YZ = (Z ^ 2 - Z0 ^ 2) + (Z0 ^ 2 - YZ) := by ring
      rw [this]; exact pDiv_add hp h1 h2
    -- Combine X * Z^2 ≡ YX * YZ ≡ target (mod p^3)
    have hYX0 : pDiv p 0 YX := by
      have h1 : pDiv p 0 (3 * (p : ℚ) * harmh i) :=
        pDiv_mono (by omega) (pDiv_mul hp (pDiv_mul hp (pDiv_nat_zero hp 3) (pDiv_p_one p hp)) hhi)
      have h2 : pDiv p 0 ((p : ℚ) ^ 2 * (9 * harmh i ^ 2 + 3 * harmh2 i) / (2 : ℕ)) :=
        pDiv_div_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
          (pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_pow p 2 hp)
            (pDiv_add hp (by simpa using pDiv_mul hp (pDiv_nat_zero hp 9) (pDiv_pow (n := 2) hp hhi))
              (by simpa using pDiv_mul hp (pDiv_nat_zero hp 3) hhi2))))
      have : YX = 1 - 3 * (p : ℚ) * harmh i +
          (p : ℚ) ^ 2 * (9 * harmh i ^ 2 + 3 * harmh2 i) / (2 : ℕ) := by push_cast; rfl
      rw [this]; exact pDiv_add hp (pDiv_sub hp (pDiv_nat_zero hp 1) h1) h2
    have hYZ0 : pDiv p 0 YZ := by
      have h1 : pDiv p 0 (2 * (p : ℚ) * harmh (i - 1)) :=
        pDiv_mono (by omega) (pDiv_mul hp (pDiv_mul hp (pDiv_nat_zero hp 2) (pDiv_p_one p hp)) hhh)
      have h2 : pDiv p 0 ((p : ℚ) ^ 2 * (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1))) :=
        pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_pow p 2 hp)
          (pDiv_sub hp (by simpa using pDiv_mul hp (pDiv_nat_zero hp 2) (pDiv_pow (n := 2) hp hhh)) hhh2))
      exact pDiv_add hp (pDiv_add hp (pDiv_nat_zero hp 1) h1) h2
    have hX0 : pDiv p 0 X := by
      have : X = (X - YX) + YX := by ring
      rw [this]; exact pDiv_add hp (pDiv_mono (by omega) hX_YX) hYX0
    have hprod1 : pDiv p 3 (X * Z ^ 2 - YX * YZ) := by
      have : X * Z ^ 2 - YX * YZ = X * (Z ^ 2 - YZ) + (X - YX) * YZ := by ring
      rw [this]; exact pDiv_add hp (by simpa using pDiv_mul hp hX0 hZ_YZ) (by simpa using pDiv_mul hp hX_YX hYZ0)
    have hprod2 : pDiv p 3 (YX * YZ - (1 - (p : ℚ) * (harmh (i - 1) + 3 / (i : ℚ)) +
        (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 + harmh2 (i - 1) +
          6 * harmh (i - 1) / (i : ℚ) + 12 / (i : ℚ) ^ 2) / 2)) := by
      have hrew2 : YX * YZ - (1 - (p : ℚ) * (harmh (i - 1) + 3 / (i : ℚ)) +
          (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 + harmh2 (i - 1) +
            6 * harmh (i - 1) / (i : ℚ) + 12 / (i : ℚ) ^ 2) / 2) =
          (p : ℚ) ^ 3 * ((-3 * harmh i * (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1)) +
              harmh (i - 1) * (9 * harmh i ^ 2 + 3 * harmh2 i)) +
            (p : ℚ) * ((9 * harmh i ^ 2 + 3 * harmh2 i) *
              (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1))) / (2 : ℕ)) := by
        dsimp only [YX, YZ]; rw [hh_step, hh2_step]; push_cast; ring
      rw [hrew2]
      have hf1 : pDiv p 0 (9 * harmh i ^ 2 + 3 * harmh2 i) :=
        pDiv_add hp
          (by simpa using pDiv_mul hp (pDiv_nat_zero hp 9) (pDiv_pow (n := 2) hp hhi))
          (by simpa using pDiv_mul hp (pDiv_nat_zero hp 3) hhi2)
      have hf2 : pDiv p 0 (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1)) :=
        pDiv_sub hp
          (by simpa using pDiv_mul hp (pDiv_nat_zero hp 2) (pDiv_pow (n := 2) hp hhh))
          hhh2
      have ha : pDiv p 0 (-3 * harmh i * (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1)) +
            harmh (i - 1) * (9 * harmh i ^ 2 + 3 * harmh2 i)) :=
        pDiv_add hp
          (by simpa using pDiv_mul hp (pDiv_mul hp (pDiv_int_zero hp (-3)) hhi) hf2)
          (by simpa using pDiv_mul hp hhh hf1)
      have hb : pDiv p 0 ((p : ℚ) * ((9 * harmh i ^ 2 + 3 * harmh2 i) *
            (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1))) / (2 : ℕ)) := by
        have hprod0 : pDiv p 0 ((9 * harmh i ^ 2 + 3 * harmh2 i) *
            (2 * harmh (i - 1) ^ 2 - harmh2 (i - 1))) := by
          simpa using pDiv_mul hp hf1 hf2
        exact pDiv_div_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
          (pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_one p hp) hprod0))
      simpa using pDiv_mul hp (pDiv_p_pow p 3 hp) (pDiv_add hp ha hb)
    have htot3 : pDiv p 3 (X * Z ^ 2 - (1 - (p : ℚ) * (harmh (i - 1) + 3 / (i : ℚ)) +
        (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 + harmh2 (i - 1) +
          6 * harmh (i - 1) / (i : ℚ) + 12 / (i : ℚ) ^ 2) / 2)) := by
      have : X * Z ^ 2 - (1 - (p : ℚ) * (harmh (i - 1) + 3 / (i : ℚ)) +
            (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 + harmh2 (i - 1) +
              6 * harmh (i - 1) / (i : ℚ) + 12 / (i : ℚ) ^ 2) / 2) =
          (X * Z ^ 2 - YX * YZ) + (YX * YZ - (1 - (p : ℚ) * (harmh (i - 1) + 3 / (i : ℚ)) +
            (p : ℚ) ^ 2 * (harmh (i - 1) ^ 2 + harmh2 (i - 1) +
              6 * harmh (i - 1) / (i : ℚ) + 12 / (i : ℚ) ^ 2) / 2)) := by ring
      rw [this]; exact pDiv_add hp hprod1 hprod2
    simpa using pDiv_mul hp (pDiv_mul hp (pDiv_p_pow p 2 hp) hinv2) htot3
  -- Plug in H2, U1, H3, U2, U3, U4, H4!
  have h12 := harmH1_H2_pDiv_five p hp hp7
  have ⟨hU2, hU1⟩ := harmU1_U2_pDiv5 p hp hp7
  have hH3 := pDiv_mul hp (pDiv_p_pow p 3 hp) (harmH3_pDiv_two p hp hp7)
  have hH4 := pDiv_mul hp (pDiv_p_pow p 4 hp) (harmH4_pDiv_one p hp hp7)
  have hU3 := pDiv_mul hp (pDiv_p_pow p 4 hp) (harmU3_pDiv1 p hp hp7)
  have hU4 := pDiv_mul hp (pDiv_p_pow p 4 hp) (harmU4_pDiv1 p hp hp7)
  have hU2d : pDiv p 5 ((p : ℚ) ^ 4 * harmU2 p / (2 : ℕ)) :=
    pDiv_div_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega) hU2
  have hU3d : pDiv p 5 ((p : ℚ) ^ 4 * harmU3 p / (2 : ℕ)) :=
    pDiv_div_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega) hU3
  have hinner : pDiv p 5 ((∑ i ∈ Ico 1 p, ((-1 : ℚ) ^ (p - 1 - i) *
      ((3 * p - 1).choose (p - 1 - i) : ℚ) * (((p + i - 1).choose i : ℚ) ^ 2))) -
      (p : ℚ) * harmH p 1) := by
    have hrew : (∑ i ∈ Ico 1 p, ((-1 : ℚ) ^ (p - 1 - i) *
        ((3 * p - 1).choose (p - 1 - i) : ℚ) * (((p + i - 1).choose i : ℚ) ^ 2))) -
        (p : ℚ) * harmH p 1 =
        ((∑ i ∈ Ico 1 p, ((-1 : ℚ) ^ (p - 1 - i) *
          ((3 * p - 1).choose (p - 1 - i) : ℚ) * (((p + i - 1).choose i : ℚ) ^ 2))) -
          ((p : ℚ) ^ 2 * harmH p 2 - (p : ℚ) ^ 3 * harmU1 p - 3 * (p : ℚ) ^ 3 * harmH p 3 +
            (p : ℚ) ^ 4 * harmU2 p / 2 + (p : ℚ) ^ 4 * harmU3 p / 2 +
            3 * (p : ℚ) ^ 4 * harmU4 p + 6 * (p : ℚ) ^ 4 * harmH p 4)) +
        (2 * (p : ℚ) * harmH p 1 + (p : ℚ) ^ 2 * harmH p 2) -
        ((p : ℚ) ^ 3 * harmU1 p + 3 * (p : ℚ) * harmH p 1) -
        3 * ((p : ℚ) ^ 3 * harmH p 3) +
        (p : ℚ) ^ 4 * harmU2 p / (2 : ℕ) +
        (p : ℚ) ^ 4 * harmU3 p / (2 : ℕ) +
        3 * ((p : ℚ) ^ 4 * harmU4 p) +
        6 * ((p : ℚ) ^ 4 * harmH p 4) := by push_cast; ring
    rw [hrew]
    exact pDiv_add hp (pDiv_add hp (pDiv_add hp (pDiv_add hp (pDiv_sub hp (pDiv_sub hp
      (pDiv_add hp hsum h12) hU1)
      (by simpa using pDiv_mul hp (pDiv_nat_zero hp 3) hH3))
      hU2d) hU3d)
      (by simpa using pDiv_mul hp (pDiv_nat_zero hp 3) hU4))
      (by simpa using pDiv_mul hp (pDiv_nat_zero hp 6) hH4)
  have h3 : 3 * (∑ i ∈ Ico 1 p, ((-1 : ℚ) ^ (p - 1 - i) *
      ((3 * p - 1).choose (p - 1 - i) : ℚ) * (((p + i - 1).choose i : ℚ) ^ 2))) -
      3 * (p : ℚ) * harmH p 1 =
      3 * ((∑ i ∈ Ico 1 p, ((-1 : ℚ) ^ (p - 1 - i) *
        ((3 * p - 1).choose (p - 1 - i) : ℚ) * (((p + i - 1).choose i : ℚ) ^ 2))) -
        (p : ℚ) * harmH p 1) := by ring
  rw [h3]; simpa using pDiv_mul hp (pDiv_nat_zero hp 3) hinner

-- t2: ∑_{i, j ∈ Ico 1 p, i + j ≤ p} C(4p - i - j, 3p) * C(p, i)^2 * C(p, j)^2 ≡ 0 (mod p^5)
lemma t2_pDiv5 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    pDiv p 5 (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
      if i + j ≤ p then (((4 * p - i - j).choose (3 * p) : ℚ) *
        ((p.choose i : ℚ) ^ 2) * ((p.choose j : ℚ) ^ 2)) else 0) := by
  -- Show each term ≡ p^4 / (i^2 * j^2) (mod p^5)!
  have hdiff : pDiv p 5 ((∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
      if i + j ≤ p then (((4 * p - i - j).choose (3 * p) : ℚ) *
        ((p.choose i : ℚ) ^ 2) * ((p.choose j : ℚ) ^ 2)) else 0) -
      (p : ℚ) ^ 4 * (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
        if i + j ≤ p then (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) else 0)) := by
    simp only [mul_sum, ← sum_sub_distrib]
    apply pDiv_sum hp; intro i hi
    apply pDiv_sum hp; intro j hj
    by_cases hij : i + j ≤ p
    · rw [if_pos hij, if_pos hij]
      have hi1 := (mem_Ico.mp hi).1; have hi2 := (mem_Ico.mp hi).2
      have hj1 := (mem_Ico.mp hj).1; have hj2 := (mem_Ico.mp hj).2
      have hchi := choose_mp_eq p 1 i le_rfl hi1 hi2
      have hchj := choose_mp_eq p 1 j le_rfl hj1 hj2
      simp only [one_mul, Nat.cast_one] at hchi hchj
      have hsym : (4 * p - i - j).choose (3 * p) = (3 * p + (p - (i + j))).choose (p - (i + j)) := by
        rw [← Nat.choose_symm (by omega : 3 * p ≤ 4 * p - i - j)]
        have e1 : 4 * p - i - j - 3 * p = p - (i + j) := by omega
        have e2 : 4 * p - i - j = 3 * p + (p - (i + j)) := by omega
        rw [e1, e2]
      rw [hsym, hchi, hchj, mul_pow, mul_pow]
      set C0 := ((3 * p + (p - (i + j))).choose (p - (i + j)) : ℚ)
      set Ci := ((p - 1).choose (i - 1) : ℚ) ^ 2
      set Cj := ((p - 1).choose (j - 1) : ℚ) ^ 2
      have hC0_1 : pDiv p 1 (C0 - 1) := by
        have htr := choose_mp_add_trunc2 p 3 (p - (i + j)) hp (by omega)
        have hhh := harmh_pDiv0 (p := p) hp (by omega : p - (i + j) < p)
        have hhh2 := harmh2_pDiv0 (p := p) hp (by omega : p - (i + j) < p)
        have hrest : pDiv p 1 ((3 : ℚ) * (p : ℚ) * harmh (p - (i + j)) +
            ((3 : ℚ) * (p : ℚ)) ^ 2 * (harmh (p - (i + j)) ^ 2 - harmh2 (p - (i + j))) / 2) := by
          have ha : pDiv p 1 ((3 : ℚ) * (p : ℚ) * harmh (p - (i + j))) := by
            simpa [mul_assoc] using pDiv_mul hp (pDiv_mul hp (pDiv_nat_zero hp 3) (pDiv_p_one p hp)) hhh
          have hb : pDiv p 1 (9 * (p : ℚ) ^ 2 * (harmh (p - (i + j)) ^ 2 - harmh2 (p - (i + j))) / (2 : ℕ)) :=
            pDiv_div_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
              (pDiv_mono (by omega) (pDiv_mul hp (pDiv_mul hp (pDiv_nat_zero hp 9) (pDiv_p_pow p 2 hp))
                (pDiv_sub hp (by simpa using pDiv_pow (n := 2) hp hhh) hhh2)))
          have hrew : (3 : ℚ) * (p : ℚ) * harmh (p - (i + j)) +
              ((3 : ℚ) * (p : ℚ)) ^ 2 * (harmh (p - (i + j)) ^ 2 - harmh2 (p - (i + j))) / 2 =
              (3 : ℚ) * (p : ℚ) * harmh (p - (i + j)) +
              9 * (p : ℚ) ^ 2 * (harmh (p - (i + j)) ^ 2 - harmh2 (p - (i + j))) / (2 : ℕ) := by
            push_cast; ring
          rw [hrew]; exact pDiv_add hp ha hb
        have : C0 - 1 = (C0 - (1 + (3 : ℚ) * (p : ℚ) * harmh (p - (i + j)) +
            ((3 : ℚ) * (p : ℚ)) ^ 2 * (harmh (p - (i + j)) ^ 2 - harmh2 (p - (i + j))) / 2)) +
            ((3 : ℚ) * (p : ℚ) * harmh (p - (i + j)) +
            ((3 : ℚ) * (p : ℚ)) ^ 2 * (harmh (p - (i + j)) ^ 2 - harmh2 (p - (i + j))) / 2) := by ring
        rw [this]; exact pDiv_add hp (pDiv_mono (by omega) htr) hrest
      have hC_sq1 : ∀ m, 1 ≤ m → m < p → pDiv p 1 (((p - 1).choose (m - 1) : ℚ) ^ 2 - 1) := by
        intro m hm1 hm2
        have htr := choose_mp_sub_one_trunc2 p 1 m hp le_rfl hm1 hm2
        simp only [one_mul, Nat.cast_one] at htr
        have hhh := harmh_pDiv0 (p := p) hp (by omega : m - 1 < p)
        have hhh2 := harmh2_pDiv0 (p := p) hp (by omega : m - 1 < p)
        have hrest : pDiv p 1 (-(p : ℚ) * harmh (m - 1) +
            (p : ℚ) ^ 2 * (harmh (m - 1) ^ 2 - harmh2 (m - 1)) / (2 : ℕ)) :=
          pDiv_add hp
            (by simpa [mul_assoc] using pDiv_mul hp (pDiv_mul hp (pDiv_int_zero hp (-1)) (pDiv_p_one p hp)) hhh)
            (pDiv_div_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
              (pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_pow p 2 hp)
                (pDiv_sub hp (by simpa using pDiv_pow (n := 2) hp hhh) hhh2))))
        set Z := (-1 : ℚ) ^ (m - 1) * ((p - 1).choose (m - 1) : ℚ)
        have hZ1 : pDiv p 1 (Z - 1) := by
          have : Z - 1 = (Z - (1 - (p : ℚ) * harmh (m - 1) +
              (p : ℚ) ^ 2 * (harmh (m - 1) ^ 2 - harmh2 (m - 1)) / 2)) +
              (-(p : ℚ) * harmh (m - 1) +
              (p : ℚ) ^ 2 * (harmh (m - 1) ^ 2 - harmh2 (m - 1)) / (2 : ℕ)) := by push_cast; ring
          rw [this]; exact pDiv_add hp (pDiv_mono (by omega) htr) hrest
        have hZ0 : pDiv p 0 Z := by
          have : Z = (Z - 1) + 1 := by ring
          rw [this]; exact pDiv_add hp (pDiv_mono (by omega) hZ1) (pDiv_nat_zero hp 1)
        have hsq : ((p - 1).choose (m - 1) : ℚ) ^ 2 - 1 = (Z + 1) * (Z - 1) := by
          dsimp only [Z]
          have : ((-1 : ℚ) ^ (m - 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
          calc ((p - 1).choose (m - 1) : ℚ) ^ 2 - 1
              = ((-1 : ℚ) ^ (m - 1)) ^ 2 * ((p - 1).choose (m - 1) : ℚ) ^ 2 - 1 := by rw [this, one_mul]
            _ = _ := by ring
        rw [hsq]; simpa using pDiv_mul hp (pDiv_add hp hZ0 (pDiv_nat_zero hp 1)) hZ1
      have hCi1 := hC_sq1 i hi1 hi2
      have hCj1 := hC_sq1 j hj1 hj2
      have hC00 : pDiv p 0 C0 := pDiv_nat_zero hp _
      have hCi0 : pDiv p 0 Ci := pDiv_nat_zero hp _
      have hprod1 : pDiv p 1 (C0 * Ci * Cj - 1) := by
        have : C0 * Ci * Cj - 1 = C0 * Ci * (Cj - 1) + C0 * (Ci - 1) + (C0 - 1) := by ring
        rw [this]
        exact pDiv_add hp (pDiv_add hp
          (by simpa using pDiv_mul hp (pDiv_mul hp hC00 hCi0) hCj1)
          (by simpa using pDiv_mul hp hC00 hCi1)) hC0_1
      have hrew : C0 * (((p : ℚ) / (i : ℚ)) ^ 2 * ((p - 1).choose (i - 1) : ℚ) ^ 2) *
            (((p : ℚ) / (j : ℚ)) ^ 2 * ((p - 1).choose (j - 1) : ℚ) ^ 2) -
          (p : ℚ) ^ 4 * ((1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2)) =
          (p : ℚ) ^ 4 * ((1 : ℚ) / (i : ℚ) ^ 2) * ((1 : ℚ) / (j : ℚ) ^ 2) * (C0 * Ci * Cj - 1) := by
        dsimp only [Ci, Cj]; rw [div_pow, div_pow]; ring
      rw [hrew]
      have h1 := inv_pow_lt_p_pDiv0 (k := 2) hp hi1 hi2
      have h2 := inv_pow_lt_p_pDiv0 (k := 2) hp hj1 hj2
      simpa using pDiv_mul hp (pDiv_mul hp (pDiv_mul hp (pDiv_p_pow p 4 hp) h1) h2) hprod1
    · rw [if_neg hij, if_neg hij, mul_zero, sub_self]; exact pDiv_zero p 5 hp
  -- Now show ∑_{i+j ≤ p} 1/(i^2*j^2) = ∑_{i+j < p} + ∑_{i+j = p} ≡ 0 (mod p)!
  have hle_pDiv1 : pDiv p 1 (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
      if i + j ≤ p then (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) else 0) := by
    have hsplit : (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
        if i + j ≤ p then (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) else 0) =
        (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
          if i + j < p then (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) else 0) +
        (∑ i ∈ Ico 1 p, (1 : ℚ) / ((i : ℚ) ^ 2 * ((p - i : ℕ) : ℚ) ^ 2)) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl; intro i hi
      have hi1 := (mem_Ico.mp hi).1; have hi2 := (mem_Ico.mp hi).2
      have heq_sum : (1 : ℚ) / ((i : ℚ) ^ 2 * ((p - i : ℕ) : ℚ) ^ 2) =
          ∑ j ∈ Ico 1 p, if i + j = p then (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) else 0 := by
        have hcond : ∀ j ∈ Ico 1 p,
            (if i + j = p then (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) else 0) =
            (if j = p - i then (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) else 0) := by
          intro j _; by_cases h : i + j = p <;> by_cases h' : j = p - i <;> simp [h, h'] <;> omega
        rw [sum_congr rfl hcond, sum_ite_eq' (Ico 1 p) (p - i), if_pos (mem_Ico.mpr ⟨by omega, by omega⟩)]
      rw [heq_sum, ← sum_add_distrib]
      apply sum_congr rfl; intro j _
      by_cases hlt : i + j < p
      · have hle : i + j ≤ p := le_of_lt hlt
        have hne : i + j ≠ p := ne_of_lt hlt
        simp [hlt, hle, hne]
      · by_cases heq : i + j = p
        · simp [hlt, heq]
        · have hnle : ¬ i + j ≤ p := by omega
          simp [hlt, heq, hnle]
    rw [hsplit]
    have hdiag : pDiv p 1 (∑ i ∈ Ico 1 p, (1 : ℚ) / ((i : ℚ) ^ 2 * ((p - i : ℕ) : ℚ) ^ 2)) := by
      have hsub : pDiv p 1 ((∑ i ∈ Ico 1 p, (1 : ℚ) / ((i : ℚ) ^ 2 * ((p - i : ℕ) : ℚ) ^ 2)) - harmH p 4) := by
        unfold harmH; rw [← sum_sub_distrib]
        apply pDiv_sum hp; intro i hi
        have hi1 := (mem_Ico.mp hi).1; have hi2 := (mem_Ico.mp hi).2
        have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hsi : ((p - i : ℕ) : ℚ) = (p : ℚ) - (i : ℚ) := Nat.cast_sub (by omega)
        have hpi0 : (p : ℚ) - (i : ℚ) ≠ 0 := by rw [← hsi]; exact Nat.cast_ne_zero.mpr (by omega)
        have hrew : (1 : ℚ) / ((i : ℚ) ^ 2 * ((p - i : ℕ) : ℚ) ^ 2) - (1 : ℚ) / (i : ℚ) ^ 4 =
            (p : ℚ) * (2 * (i : ℚ) - (p : ℚ)) * ((1 : ℚ) / ((p - i : ℕ) : ℚ) ^ 2) * ((1 : ℚ) / (i : ℚ) ^ 4) := by
          rw [hsi]; field_simp [hi0, hpi0]; ring
        rw [hrew]
        simpa using pDiv_mul hp (pDiv_mul hp (pDiv_mul hp (pDiv_p_one p hp)
          (by simpa using pDiv_int_zero hp (2 * (i : ℤ) - (p : ℤ))))
          (inv_pow_lt_p_pDiv0 (k := 2) hp (by omega : 1 ≤ p - i) (by omega : p - i < p)))
          (inv_pow_lt_p_pDiv0 (k := 4) hp hi1 hi2)
      have : (∑ i ∈ Ico 1 p, (1 : ℚ) / ((i : ℚ) ^ 2 * ((p - i : ℕ) : ℚ) ^ 2)) =
          ((∑ i ∈ Ico 1 p, (1 : ℚ) / ((i : ℚ) ^ 2 * ((p - i : ℕ) : ℚ) ^ 2)) - harmH p 4) + harmH p 4 := by ring
      rw [this]; exact pDiv_add hp hsub (harmH4_pDiv_one p hp hp7)
    exact pDiv_add hp (double_inv_sq_sum_lt_pDiv1 p hp hp7) hdiag
  have hmain := pDiv_mul hp (pDiv_p_pow p 4 hp) hle_pDiv1
  have : (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
      if i + j ≤ p then (((4 * p - i - j).choose (3 * p) : ℚ) *
        ((p.choose i : ℚ) ^ 2) * ((p.choose j : ℚ) ^ 2)) else 0) =
      ((∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
        if i + j ≤ p then (((4 * p - i - j).choose (3 * p) : ℚ) *
          ((p.choose i : ℚ) ^ 2) * ((p.choose j : ℚ) ^ 2)) else 0) -
        (p : ℚ) ^ 4 * (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
          if i + j ≤ p then (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) else 0)) +
      (p : ℚ) ^ 4 * (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
        if i + j ≤ p then (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) else 0) := by ring
  rw [this]; exact pDiv_add hp hdiff hmain

-- s2: ∑_{i, j ∈ Ico 1 p, i + j < p} (-1)^(p-1-i-j) * C(3p-1, p-1-i-j) * C(p+i-1, i)^2 * C(p+j-1, j)^2 ≡ 0 (mod p^5)
lemma s2_pDiv5 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    pDiv p 5 (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
      if i + j < p then ((-1 : ℚ) ^ (p - 1 - i - j) * ((3 * p - 1).choose (p - 1 - i - j) : ℚ) *
        (((p + i - 1).choose i : ℚ) ^ 2) * (((p + j - 1).choose j : ℚ) ^ 2)) else 0) := by
  have hdiff : pDiv p 5 ((∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
      if i + j < p then ((-1 : ℚ) ^ (p - 1 - i - j) * ((3 * p - 1).choose (p - 1 - i - j) : ℚ) *
        (((p + i - 1).choose i : ℚ) ^ 2) * (((p + j - 1).choose j : ℚ) ^ 2)) else 0) -
      (p : ℚ) ^ 4 * (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
        if i + j < p then (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) else 0)) := by
    simp only [mul_sum, ← sum_sub_distrib]
    apply pDiv_sum hp; intro i hi
    apply pDiv_sum hp; intro j hj
    by_cases hij : i + j < p
    · rw [if_pos hij, if_pos hij]
      have hi1 := (mem_Ico.mp hi).1; have hi2 := (mem_Ico.mp hi).2
      have hj1 := (mem_Ico.mp hj).1; have hj2 := (mem_Ico.mp hj).2
      have hch : ∀ m, 1 ≤ m → m < p →
          ((p + m - 1).choose m : ℚ) = ((p : ℚ) / (m : ℚ)) * ((p + (m - 1)).choose (m - 1) : ℚ) := by
        intro m hm1 hm2
        have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have h1 := Nat.choose_succ_right_eq (p + m - 1) (m - 1)
        have e1 : m - 1 + 1 = m := by omega
        have e2 : p + m - 1 - (m - 1) = p := by omega
        have e3 : p + m - 1 = p + (m - 1) := by omega
        rw [e1, e2, e3] at h1
        have hQ : ((p + (m - 1)).choose m : ℚ) * (m : ℚ) =
            ((p + (m - 1)).choose (m - 1) : ℚ) * (p : ℚ) := by exact_mod_cast h1
        rw [e3]; field_simp [hm0] at hQ ⊢; linarith
      rw [hch i hi1 hi2, hch j hj1 hj2, mul_pow, mul_pow]
      set C0 := (-1 : ℚ) ^ (p - 1 - i - j) * ((3 * p - 1).choose (p - 1 - i - j) : ℚ)
      set Ci := ((p + (i - 1)).choose (i - 1) : ℚ) ^ 2
      set Cj := ((p + (j - 1)).choose (j - 1) : ℚ) ^ 2
      have hC0_1 : pDiv p 1 (C0 - 1) := by
        by_cases h0 : p - 1 - i - j = 0
        · simp [C0, h0, pDiv_zero p 1 hp]
        · have htr := choose_mp_sub_one_trunc2 p 3 (p - i - j) hp (by norm_num) (by omega) (by omega)
          have e1 : p - i - j - 1 = p - 1 - i - j := by omega
          rw [e1] at htr
          have hhh := harmh_pDiv0 (p := p) hp (by omega : p - 1 - i - j < p)
          have hhh2 := harmh2_pDiv0 (p := p) hp (by omega : p - 1 - i - j < p)
          have hrest : pDiv p 1 (-(3 : ℚ) * (p : ℚ) * harmh (p - 1 - i - j) +
              9 * (p : ℚ) ^ 2 * (harmh (p - 1 - i - j) ^ 2 - harmh2 (p - 1 - i - j)) / (2 : ℕ)) :=
            pDiv_add hp
              (by simpa [mul_assoc] using pDiv_mul hp (pDiv_mul hp (pDiv_int_zero hp (-3)) (pDiv_p_one p hp)) hhh)
              (pDiv_div_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
                (pDiv_mono (by omega) (pDiv_mul hp (pDiv_mul hp (pDiv_nat_zero hp 9) (pDiv_p_pow p 2 hp))
                  (pDiv_sub hp (by simpa using pDiv_pow (n := 2) hp hhh) hhh2))))
          have : C0 - 1 = (C0 - (1 - (3 : ℚ) * (p : ℚ) * harmh (p - 1 - i - j) +
              ((3 : ℚ) * (p : ℚ)) ^ 2 * (harmh (p - 1 - i - j) ^ 2 - harmh2 (p - 1 - i - j)) / 2)) +
              (-(3 : ℚ) * (p : ℚ) * harmh (p - 1 - i - j) +
              9 * (p : ℚ) ^ 2 * (harmh (p - 1 - i - j) ^ 2 - harmh2 (p - 1 - i - j)) / (2 : ℕ)) := by
            push_cast; ring
          rw [this]; exact pDiv_add hp (pDiv_mono (by omega : 1 ≤ 3) (by simpa [C0] using htr)) hrest
      have hC_sq1 : ∀ m, 1 ≤ m → m < p → pDiv p 1 (((p + (m - 1)).choose (m - 1) : ℚ) ^ 2 - 1) := by
        intro m hm1 hm2
        have htr := choose_mp_add_trunc2 p 1 (m - 1) hp (by omega)
        simp only [one_mul, Nat.cast_one] at htr
        have hhh := harmh_pDiv0 (p := p) hp (by omega : m - 1 < p)
        have hhh2 := harmh2_pDiv0 (p := p) hp (by omega : m - 1 < p)
        have hrest : pDiv p 1 ((p : ℚ) * harmh (m - 1) +
            (p : ℚ) ^ 2 * (harmh (m - 1) ^ 2 - harmh2 (m - 1)) / (2 : ℕ)) :=
          pDiv_add hp (by simpa using pDiv_mul hp (pDiv_p_one p hp) hhh)
            (pDiv_div_nat_unit hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
              (pDiv_mono (by omega) (pDiv_mul hp (pDiv_p_pow p 2 hp)
                (pDiv_sub hp (by simpa using pDiv_pow (n := 2) hp hhh) hhh2))))
        set Z := ((p + (m - 1)).choose (m - 1) : ℚ)
        have hZ1 : pDiv p 1 (Z - 1) := by
          have : Z - 1 = (Z - (1 + (p : ℚ) * harmh (m - 1) +
              (p : ℚ) ^ 2 * (harmh (m - 1) ^ 2 - harmh2 (m - 1)) / 2)) +
              ((p : ℚ) * harmh (m - 1) +
              (p : ℚ) ^ 2 * (harmh (m - 1) ^ 2 - harmh2 (m - 1)) / (2 : ℕ)) := by push_cast; ring
          rw [this]; exact pDiv_add hp (pDiv_mono (by omega) htr) hrest
        have hsq : Z ^ 2 - 1 = (Z + 1) * (Z - 1) := by ring
        rw [hsq]; simpa using pDiv_mul hp (pDiv_add hp (pDiv_nat_zero hp _) (pDiv_nat_zero hp 1)) hZ1
      have hCi1 := hC_sq1 i hi1 hi2
      have hCj1 := hC_sq1 j hj1 hj2
      have hC00 : pDiv p 0 C0 := by
        simpa [C0] using pDiv_int_zero hp ((-1 : ℤ) ^ (p - 1 - i - j) * ((3 * p - 1).choose (p - 1 - i - j) : ℤ))
      have hCi0 : pDiv p 0 Ci := pDiv_nat_zero hp _
      have hprod1 : pDiv p 1 (C0 * Ci * Cj - 1) := by
        have : C0 * Ci * Cj - 1 = C0 * Ci * (Cj - 1) + C0 * (Ci - 1) + (C0 - 1) := by ring
        rw [this]
        exact pDiv_add hp (pDiv_add hp
          (by simpa using pDiv_mul hp (pDiv_mul hp hC00 hCi0) hCj1)
          (by simpa using pDiv_mul hp hC00 hCi1)) hC0_1
      have hrew : C0 * (((p : ℚ) / (i : ℚ)) ^ 2 * ((p + (i - 1)).choose (i - 1) : ℚ) ^ 2) *
            (((p : ℚ) / (j : ℚ)) ^ 2 * ((p + (j - 1)).choose (j - 1) : ℚ) ^ 2) -
          (p : ℚ) ^ 4 * ((1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2)) =
          (p : ℚ) ^ 4 * ((1 : ℚ) / (i : ℚ) ^ 2) * ((1 : ℚ) / (j : ℚ) ^ 2) * (C0 * Ci * Cj - 1) := by
        dsimp only [Ci, Cj]; rw [div_pow, div_pow]; ring
      rw [hrew]
      have h1 := inv_pow_lt_p_pDiv0 (k := 2) hp hi1 hi2
      have h2 := inv_pow_lt_p_pDiv0 (k := 2) hp hj1 hj2
      simpa using pDiv_mul hp (pDiv_mul hp (pDiv_mul hp (pDiv_p_pow p 4 hp) h1) h2) hprod1
    · rw [if_neg hij, if_neg hij, mul_zero, sub_self]; exact pDiv_zero p 5 hp
  have hmain := pDiv_mul hp (pDiv_p_pow p 4 hp) (double_inv_sq_sum_lt_pDiv1 p hp hp7)
  have : (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
      if i + j < p then ((-1 : ℚ) ^ (p - 1 - i - j) * ((3 * p - 1).choose (p - 1 - i - j) : ℚ) *
        (((p + i - 1).choose i : ℚ) ^ 2) * (((p + j - 1).choose j : ℚ) ^ 2)) else 0) =
      ((∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
        if i + j < p then ((-1 : ℚ) ^ (p - 1 - i - j) * ((3 * p - 1).choose (p - 1 - i - j) : ℚ) *
          (((p + i - 1).choose i : ℚ) ^ 2) * (((p + j - 1).choose j : ℚ) ^ 2)) else 0) -
        (p : ℚ) ^ 4 * (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
          if i + j < p then (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) else 0)) +
      (p : ℚ) ^ 4 * (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
        if i + j < p then (1 : ℚ) / ((i : ℚ) ^ 2 * (j : ℚ) ^ 2) else 0) := by ring
  rw [this]; exact pDiv_add hp hdiff hmain

-- Helper: linearizing (7 + 33x)^21 - 7^21 * (1 + 9x)^11 when pDiv p 3 x!
lemma pow21_eq_pow11_of_linear {p a_p a_pm1 : ℕ} {x : ℚ} (hp : p.Prime)
    (hx : pDiv p 3 x)
    (hap : pDiv p 5 ((a_p : ℚ) - (7 + 33 * x)))
    (hapm : pDiv p 5 ((a_pm1 : ℚ) - (1 + 9 * x))) :
    Nat.ModEq (p ^ 5) (3 * a_p) (10 + 11 * a_pm1) ∧
    Nat.ModEq (p ^ 5) (a_p ^ 21) (7 ^ 21 * a_pm1 ^ 11) := by
  have hx0 : pDiv p 0 x := pDiv_mono (by omega) hx
  have hx2 : pDiv p 5 (x ^ 2) := pDiv_mono (by omega) (pDiv_pow (n := 2) hp hx)
  -- Helper: (u + v*x)^n ≡ u^n + n * u^(n-1) * v * x (mod p^5)
  have hbinom_lin : ∀ (u v : ℚ) (n : ℕ), pDiv p 0 u → pDiv p 0 v →
      pDiv p 5 ((u + v * x) ^ n - (u ^ n + (n : ℚ) * u ^ (n - 1) * v * x)) := by
    intro u v n hu hv
    induction n with
    | zero => simp [pDiv_zero p 5 hp]
    | succ m ih =>
      cases m with
      | zero => simp [pDiv_zero p 5 hp]
      | succ k =>
        have hstep : (u + v * x) ^ (k + 2) -
            (u ^ (k + 2) + ((k + 2 : ℕ) : ℚ) * u ^ (k + 1) * v * x) =
            (u + v * x) * ((u + v * x) ^ (k + 1) -
              (u ^ (k + 1) + ((k + 1 : ℕ) : ℚ) * u ^ k * v * x)) +
            ((k + 1 : ℕ) : ℚ) * u ^ k * v ^ 2 * x ^ 2 := by
          push_cast; ring
        change pDiv p 5 ((u + v * x) ^ (k + 2) -
          (u ^ (k + 2) + ((k + 2 : ℕ) : ℚ) * u ^ (k + 1) * v * x))
        rw [hstep]
        have huvx : pDiv p 0 (u + v * x) := pDiv_add hp hu (by simpa using pDiv_mul hp hv hx0)
        have h1 : pDiv p 5 ((u + v * x) * ((u + v * x) ^ (k + 1) -
            (u ^ (k + 1) + ((k + 1 : ℕ) : ℚ) * u ^ k * v * x))) := by
          simpa using pDiv_mul hp huvx ih
        have h2 : pDiv p 5 (((k + 1 : ℕ) : ℚ) * u ^ k * v ^ 2 * x ^ 2) := by
          have hk0 := pDiv_nat_zero hp (k + 1)
          have huk : pDiv p 0 (u ^ k) := by simpa using pDiv_pow (n := k) hp hu
          have hv2 : pDiv p 0 (v ^ 2) := by simpa using pDiv_pow (n := 2) hp hv
          simpa using pDiv_mul hp (pDiv_mul hp (pDiv_mul hp hk0 huk) hv2) hx2
        exact pDiv_add hp h1 h2
  -- Helper: if pDiv p 5 (a - b) and pDiv p 0 a, b, then pDiv p 5 (a^n - b^n)
  have hpow_cong : ∀ (a b : ℚ) (n : ℕ), pDiv p 0 a → pDiv p 0 b → pDiv p 5 (a - b) →
      pDiv p 5 (a ^ n - b ^ n) := by
    intro a b n ha hb hab
    induction n with
    | zero => simp [pDiv_zero p 5 hp]
    | succ m ih =>
      have : a ^ (m + 1) - b ^ (m + 1) = a * (a ^ m - b ^ m) + (a - b) * b ^ m := by ring
      rw [this]
      exact pDiv_add hp (by simpa using pDiv_mul hp ha ih)
        (by
          have hmul := pDiv_mul hp hab (by simpa using pDiv_pow (n := m) hp hb)
          simpa using hmul)
  -- Part 3: 3 * a_p ≡ 10 + 11 * a_pm1 (mod p^5)
  have h3 : Nat.ModEq (p ^ 5) (3 * a_p) (10 + 11 * a_pm1) := by
    have hd : pDiv p 5 ((((3 * a_p : ℕ) : ℤ) - ((10 + 11 * a_pm1 : ℕ) : ℤ) : ℤ) : ℚ) := by
      have hrew : ((((3 * a_p : ℕ) : ℤ) - ((10 + 11 * a_pm1 : ℕ) : ℤ) : ℤ) : ℚ) =
          3 * ((a_p : ℚ) - (7 + 33 * x)) - 11 * ((a_pm1 : ℚ) - (1 + 9 * x)) := by
        push_cast; ring
      rw [hrew]
      exact pDiv_sub hp (by simpa using pDiv_mul hp (pDiv_nat_zero hp 3) hap)
        (by simpa using pDiv_mul hp (pDiv_nat_zero hp 11) hapm)
    have hdvd := int_dvd_of_pDiv hp hd
    exact (Int.natCast_modEq_iff).mp (Int.modEq_iff_dvd.mpr (by simpa [neg_sub] using dvd_neg.mpr hdvd))
  -- Part 4: a_p ^ 21 ≡ 7 ^ 21 * a_pm1 ^ 11 (mod p^5)
  have h4 : Nat.ModEq (p ^ 5) (a_p ^ 21) (7 ^ 21 * a_pm1 ^ 11) := by
    have h733 : pDiv p 0 (7 + 33 * x) :=
      pDiv_add hp (pDiv_nat_zero hp 7) (by simpa using pDiv_mul hp (pDiv_nat_zero hp 33) hx0)
    have h19 : pDiv p 0 (1 + 9 * x) :=
      pDiv_add hp (pDiv_nat_zero hp 1) (by simpa using pDiv_mul hp (pDiv_nat_zero hp 9) hx0)
    have hp1 := hpow_cong (a_p : ℚ) (7 + 33 * x) 21 (pDiv_nat_zero hp a_p) h733 hap
    have hp2 := hpow_cong (a_pm1 : ℚ) (1 + 9 * x) 11 (pDiv_nat_zero hp a_pm1) h19 hapm
    have hl1 := hbinom_lin 7 33 21 (pDiv_nat_zero hp 7) (pDiv_nat_zero hp 33)
    have hl2 := hbinom_lin 1 9 11 (pDiv_nat_zero hp 1) (pDiv_nat_zero hp 9)
    have hd : pDiv p 5 ((((a_p ^ 21 : ℕ) : ℤ) - ((7 ^ 21 * a_pm1 ^ 11 : ℕ) : ℤ) : ℤ) : ℚ) := by
      have hrew : ((((a_p ^ 21 : ℕ) : ℤ) - ((7 ^ 21 * a_pm1 ^ 11 : ℕ) : ℤ) : ℤ) : ℚ) =
          ((a_p : ℚ) ^ 21 - (7 + 33 * x) ^ 21) +
          ((7 + 33 * x) ^ 21 - (7 ^ 21 + (21 : ℚ) * 7 ^ (21 - 1) * 33 * x)) -
          (7 : ℚ) ^ 21 * ((a_pm1 : ℚ) ^ 11 - (1 + 9 * x) ^ 11) -
          (7 : ℚ) ^ 21 * ((1 + 9 * x) ^ 11 - (1 ^ 11 + (11 : ℚ) * 1 ^ (11 - 1) * 9 * x)) := by
        push_cast; norm_num; ring
      rw [hrew]
      have h721 : pDiv p 0 ((7 : ℚ) ^ 21) := by simpa using pDiv_pow (n := 21) hp (pDiv_nat_zero hp 7)
      exact pDiv_sub hp (pDiv_sub hp (pDiv_add hp hp1 hl1)
        (by simpa using pDiv_mul hp h721 hp2))
        (by simpa using pDiv_mul hp h721 hl2)
    have hdvd := int_dvd_of_pDiv hp hd
    exact (Int.natCast_modEq_iff).mp (Int.modEq_iff_dvd.mpr (by simpa [neg_sub] using dvd_neg.mpr hdvd))
  exact ⟨h3, h4⟩

end OMA_A364114_Part4

namespace OMA_A364114_Glue

open Finset

-- Local pDiv copy (will be deduplicated on assembly)
def pDiv (p k : ℕ) (q : ℚ) : Prop :=
  ∃ (a : ℤ) (b : ℕ), ¬ (p ∣ b) ∧ q = ((p : ℚ) ^ k * (a : ℚ)) / (b : ℚ)

lemma pDiv_zero (p k : ℕ) (hp : p.Prime) : pDiv p k 0 :=
  ⟨0, 1, hp.not_dvd_one, by simp⟩

lemma pDiv_mono {p k₁ k₂ : ℕ} {q : ℚ} (hle : k₁ ≤ k₂) (h : pDiv p k₂ q) : pDiv p k₁ q := by
  rcases h with ⟨a, b, hb, rfl⟩
  refine ⟨(p : ℤ) ^ (k₂ - k₁) * a, b, hb, ?_⟩
  push_cast
  have : (p : ℚ) ^ k₂ = (p : ℚ) ^ k₁ * (p : ℚ) ^ (k₂ - k₁) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  rw [this]; ring

lemma pDiv_add {p k : ℕ} {q₁ q₂ : ℚ} (hp : p.Prime)
    (h1 : pDiv p k q₁) (h2 : pDiv p k q₂) : pDiv p k (q₁ + q₂) := by
  rcases h1 with ⟨a₁, b₁, hb₁, rfl⟩
  rcases h2 with ⟨a₂, b₂, hb₂, rfl⟩
  have hb₁0 : (b₁ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h0 => hb₁ (h0 ▸ dvd_zero p))
  have hb₂0 : (b₂ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h0 => hb₂ (h0 ▸ dvd_zero p))
  refine ⟨a₁ * (b₂ : ℤ) + a₂ * (b₁ : ℤ), b₁ * b₂, hp.not_dvd_mul hb₁ hb₂, ?_⟩
  push_cast; field_simp [hb₁0, hb₂0]

lemma pDiv_neg {p k : ℕ} {q : ℚ} (h : pDiv p k q) : pDiv p k (-q) := by
  rcases h with ⟨a, b, hb, rfl⟩
  refine ⟨-a, b, hb, ?_⟩; push_cast; ring

lemma pDiv_sub {p k : ℕ} {q₁ q₂ : ℚ} (hp : p.Prime)
    (h1 : pDiv p k q₁) (h2 : pDiv p k q₂) : pDiv p k (q₁ - q₂) := by
  rw [sub_eq_add_neg]; exact pDiv_add hp h1 (pDiv_neg h2)

lemma pDiv_mul {p k₁ k₂ : ℕ} {q₁ q₂ : ℚ} (hp : p.Prime)
    (h1 : pDiv p k₁ q₁) (h2 : pDiv p k₂ q₂) : pDiv p (k₁ + k₂) (q₁ * q₂) := by
  rcases h1 with ⟨a₁, b₁, hb₁, rfl⟩
  rcases h2 with ⟨a₂, b₂, hb₂, rfl⟩
  refine ⟨a₁ * a₂, b₁ * b₂, hp.not_dvd_mul hb₁ hb₂, ?_⟩
  push_cast; rw [pow_add]; ring

lemma pDiv_sum {ι : Type*} {p k : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, pDiv p k (f i)) : pDiv p k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [pDiv_zero p k hp]
  | @insert x s hx ih =>
    rw [sum_insert hx]
    exact pDiv_add hp (hf x (mem_insert_self x s))
      (ih (fun y hy => hf y (mem_insert_of_mem hy)))

lemma pDiv_nat_zero {p : ℕ} (hp : p.Prime) (n : ℕ) : pDiv p 0 (n : ℚ) :=
  ⟨n, 1, hp.not_dvd_one, by simp⟩

lemma pDiv_int_zero {p : ℕ} (hp : p.Prime) (z : ℤ) : pDiv p 0 (z : ℚ) :=
  ⟨z, 1, hp.not_dvd_one, by simp⟩

lemma pDiv_p_one (p : ℕ) (hp : p.Prime) : pDiv p 1 (p : ℚ) :=
  ⟨1, 1, hp.not_dvd_one, by simp⟩

lemma pDiv_of_dvd_int {p k : ℕ} {z : ℤ} (hp : p.Prime) (h : (p : ℤ) ^ k ∣ z) :
    pDiv p k (z : ℚ) := by
  rcases h with ⟨c, rfl⟩
  refine ⟨c, 1, hp.not_dvd_one, ?_⟩
  push_cast; ring

-- ============================================================================
-- Section 1: Binomial p-adic divisibility helpers
-- ============================================================================

lemma dvd_choose_of_pow_dvd {p r N k e : ℕ} (hp : p.Prime)
    (hN : p ^ r ∣ N) (hN_pos : 0 < N) (hk_pos : 0 < k) (hkN : k ≤ N)
    (her : e ≤ r) (hvk : padicValNat p k ≤ e) :
    p ^ (r - e) ∣ N.choose k := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 := Nat.add_one_mul_choose_eq (N - 1) (k - 1)
  have e1 : N - 1 + 1 = N := by omega
  have e2 : k - 1 + 1 = k := by omega
  rw [e1, e2] at h1
  have hch_ne : N.choose k ≠ 0 := (Nat.choose_pos hkN).ne'
  have hch1_ne : (N - 1).choose (k - 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hv := congrArg (padicValNat p) h1
  rw [padicValNat.mul (by omega) hch1_ne, padicValNat.mul hch_ne (by omega)] at hv
  have hvN : r ≤ padicValNat p N := by
    rw [padicValNat_dvd_iff_le (by omega)] at hN; exact hN
  have hv_ch : r - e ≤ padicValNat p (N.choose k) := by omega
  exact (padicValNat_dvd_iff_le hch_ne).mpr hv_ch

lemma dvd_choose_pred_of_pow_dvd {p r N k e : ℕ} (hp : p.Prime)
    (hN : p ^ r ∣ N) (hN_pos : 0 < N) (hk_pos : 0 < k)
    (her : e ≤ r) (hvk : padicValNat p k ≤ e) :
    p ^ (r - e) ∣ (N + k - 1).choose k := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 := Nat.choose_succ_right_eq (N + k - 1) (k - 1)
  have e1 : k - 1 + 1 = k := by omega
  have e2 : N + k - 1 - (k - 1) = N := by omega
  rw [e1, e2] at h1
  have hch_ne : (N + k - 1).choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hch1_ne : (N + k - 1).choose (k - 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hv := congrArg (padicValNat p) h1
  rw [padicValNat.mul hch_ne (by omega), padicValNat.mul hch1_ne (by omega)] at hv
  have hvN : r ≤ padicValNat p N := by
    rw [padicValNat_dvd_iff_le (by omega)] at hN; exact hN
  have hv_ch : r - e ≤ padicValNat p ((N + k - 1).choose k) := by omega
  exact (padicValNat_dvd_iff_le hch_ne).mpr hv_ch

lemma padicValNat_eq_zero_of_not_dvd {p k : ℕ} (h : ¬ p ∣ k) : padicValNat p k = 0 :=
  padicValNat.eq_zero_of_not_dvd h

lemma pow_dvd_of_padicValNat_ge {p e n : ℕ} (hp : p.Prime) (h : n ≠ 0 → e ≤ padicValNat p n) :
    p ^ e ∣ n := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hn : n = 0
  · subst hn; exact dvd_zero _
  · exact (padicValNat_dvd_iff_le hn).mpr (h hn)

lemma not_pow_succ_dvd_of_sum_not_dvd {p e a b : ℕ} (h : ¬ p ^ (e + 1) ∣ (a + b)) :
    ¬ p ^ (e + 1) ∣ a ∨ ¬ p ^ (e + 1) ∣ b := by
  by_contra hboth
  push_neg at hboth
  exact h (dvd_add hboth.1 hboth.2)

lemma padicValNat_le_of_not_pow_succ_dvd {p e n : ℕ} (hp : p.Prime) (h : ¬ p ^ (e + 1) ∣ n) :
    padicValNat p n ≤ e := by
  have : Fact p.Prime := ⟨hp⟩
  have hn : n ≠ 0 := fun h0 => h (h0 ▸ dvd_zero _)
  by_contra hgt
  push_neg at hgt
  exact h ((padicValNat_dvd_iff_le hn).mpr hgt)

-- ============================================================================
-- Section 2: Flat triple sums and 4-way partition by p-divisibility
-- ============================================================================

def Tle (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range (N + 1) ×ˢ (range (N + 1) ×ˢ range (N + 1))).filter
    (fun x => x.1 + x.2.1 + x.2.2 ≤ N)

def Tlt (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range N ×ˢ (range N ×ˢ range N)).filter
    (fun x => x.1 + x.2.1 + x.2.2 < N)

lemma triple_sum_le_eq_flat {α : Type*} [AddCommMonoid α] (N : ℕ) (f : ℕ → ℕ → ℕ → α) :
    ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1 - i), ∑ l ∈ range (N + 1 - i - j), f i j l =
      ∑ x ∈ Tle N, f x.1 x.2.1 x.2.2 := by
  unfold Tle
  rw [sum_filter, sum_product]
  simp_rw [sum_product]
  apply sum_congr rfl; intro i hi
  have hi' : i ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have h1 : ∀ j ∈ range (N + 1),
      (∑ l ∈ range (N + 1), if i + j + l ≤ N then f i j l else 0) =
      if j ∈ range (N + 1 - i) then ∑ l ∈ range (N + 1 - i - j), f i j l else 0 := by
    intro j _
    by_cases hj : j ∈ range (N + 1 - i)
    · rw [if_pos hj, ← sum_filter]
      have hfilt : (range (N + 1)).filter (fun l => i + j + l ≤ N) = range (N + 1 - i - j) := by
        ext l; simp only [mem_filter, mem_range] at hj ⊢; omega
      rw [hfilt]
    · rw [if_neg hj]
      apply sum_eq_zero; intro l _
      have hgt : ¬ (i + j + l ≤ N) := by simp only [mem_range] at hj; omega
      rw [if_neg hgt]
  rw [sum_congr rfl h1, sum_ite_mem, inter_eq_right.mpr (range_mono (by omega : N + 1 - i ≤ N + 1))]

lemma triple_sum_lt_eq_flat {α : Type*} [AddCommMonoid α] (N : ℕ) (f : ℕ → ℕ → ℕ → α) :
    ∑ i ∈ range N, ∑ j ∈ range (N - i), ∑ l ∈ range (N - i - j), f i j l =
      ∑ x ∈ Tlt N, f x.1 x.2.1 x.2.2 := by
  unfold Tlt
  rw [sum_filter, sum_product]
  simp_rw [sum_product]
  apply sum_congr rfl; intro i hi
  have hi' : i < N := mem_range.mp hi
  have h1 : ∀ j ∈ range N,
      (∑ l ∈ range N, if i + j + l < N then f i j l else 0) =
      if j ∈ range (N - i) then ∑ l ∈ range (N - i - j), f i j l else 0 := by
    intro j _
    by_cases hj : j ∈ range (N - i)
    · rw [if_pos hj, ← sum_filter]
      have hfilt : (range N).filter (fun l => i + j + l < N) = range (N - i - j) := by
        ext l; simp only [mem_filter, mem_range] at hj ⊢; omega
      rw [hfilt]
    · rw [if_neg hj]
      apply sum_eq_zero; intro l _
      have hgt : ¬ (i + j + l < N) := by simp only [mem_range] at hj; omega
      rw [if_neg hgt]
  rw [sum_congr rfl h1, sum_ite_mem, inter_eq_right.mpr (range_mono (by omega : N - i ≤ N))]

-- Partition any Finset S of triples into:
--   S0 : p ∣ i ∧ p ∣ j ∧ p ∣ l
--   S1a : ¬ p ∣ i ∧ p ∣ j ∧ p ∣ l
--   S1b : p ∣ i ∧ ¬ p ∣ j ∧ p ∣ l
--   S1c : p ∣ i ∧ p ∣ j ∧ ¬ p ∣ l
--   S23 : at least two of i, j, l not divisible by p
lemma sum_partition_p {α : Type*} [AddCommMonoid α] (p : ℕ) (S : Finset (ℕ × ℕ × ℕ))
    (g : ℕ × ℕ × ℕ → α) :
    ∑ x ∈ S, g x =
      (∑ x ∈ S.filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g x) +
      (∑ x ∈ S.filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g x) +
      (∑ x ∈ S.filter (fun x => p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ p ∣ x.2.2), g x) +
      (∑ x ∈ S.filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2), g x) +
      (∑ x ∈ S.filter (fun x =>
        (¬ p ∣ x.1 ∧ ¬ p ∣ x.2.1) ∨ (¬ p ∣ x.1 ∧ ¬ p ∣ x.2.2) ∨ (¬ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2)), g x) := by
  simp only [sum_filter, ← sum_add_distrib]
  apply sum_congr rfl; intro x _
  by_cases h1 : p ∣ x.1 <;> by_cases h2 : p ∣ x.2.1 <;> by_cases h3 : p ∣ x.2.2 <;>
    simp [h1, h2, h3]

-- Finer 8-way / 4-way partition (separating cnt=2 and cnt=3) for prime-level p^5 proof
lemma sum_partition_p_fine {α : Type*} [AddCommMonoid α] (p : ℕ) (S : Finset (ℕ × ℕ × ℕ))
    (g : ℕ × ℕ × ℕ → α) :
    ∑ x ∈ S, g x =
      (∑ x ∈ S.filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g x) +
      ((∑ x ∈ S.filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g x) +
       (∑ x ∈ S.filter (fun x => p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ p ∣ x.2.2), g x) +
       (∑ x ∈ S.filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2), g x)) +
      ((∑ x ∈ S.filter (fun x => ¬ p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ p ∣ x.2.2), g x) +
       (∑ x ∈ S.filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2), g x) +
       (∑ x ∈ S.filter (fun x => p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2), g x)) +
      (∑ x ∈ S.filter (fun x => ¬ p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2), g x) := by
  simp only [sum_filter, ← sum_add_distrib]
  apply sum_congr rfl; intro x _
  by_cases h1 : p ∣ x.1 <;> by_cases h2 : p ∣ x.2.1 <;> by_cases h3 : p ∣ x.2.2 <;>
    simp [h1, h2, h3]

-- Symmetry helpers on Tle and Tlt
lemma Tle_swap12_sum {α : Type*} [AddCommMonoid α] (N : ℕ)
    (P Q : ℕ × ℕ × ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (g : ℕ × ℕ × ℕ → α)
    (hPQ : ∀ x, P x ↔ Q (x.2.1, x.1, x.2.2))
    (hg : ∀ x, g x = g (x.2.1, x.1, x.2.2)) :
    ∑ x ∈ (Tle N).filter P, g x = ∑ x ∈ (Tle N).filter Q, g x := by
  refine Finset.sum_bij (fun x _ => (x.2.1, x.1, x.2.2)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, Tle, mem_product, mem_range] at hx ⊢
    refine ⟨⟨⟨hx.1.1.2.1, hx.1.1.1, hx.1.1.2.2⟩, by omega⟩, (hPQ x).mp hx.2⟩
  · intro x₁ _ x₂ _ h
    rcases x₁ with ⟨a₁, b₁, c₁⟩; rcases x₂ with ⟨a₂, b₂, c₂⟩
    simp only [Prod.mk.injEq] at h ⊢; exact ⟨h.2.1, h.1, h.2.2⟩
  · intro y hy
    refine ⟨(y.2.1, y.1, y.2.2), ?_, by rcases y with ⟨a, b, c⟩; rfl⟩
    simp only [mem_filter, Tle, mem_product, mem_range] at hy ⊢
    refine ⟨⟨⟨hy.1.1.2.1, hy.1.1.1, hy.1.1.2.2⟩, by omega⟩, (hPQ (y.2.1, y.1, y.2.2)).mpr hy.2⟩
  · intro x _; exact hg x

lemma Tle_swap13_sum {α : Type*} [AddCommMonoid α] (N : ℕ)
    (P Q : ℕ × ℕ × ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (g : ℕ × ℕ × ℕ → α)
    (hPQ : ∀ x, P x ↔ Q (x.2.2, x.2.1, x.1))
    (hg : ∀ x, g x = g (x.2.2, x.2.1, x.1)) :
    ∑ x ∈ (Tle N).filter P, g x = ∑ x ∈ (Tle N).filter Q, g x := by
  refine Finset.sum_bij (fun x _ => (x.2.2, x.2.1, x.1)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, Tle, mem_product, mem_range] at hx ⊢
    refine ⟨⟨⟨hx.1.1.2.2, hx.1.1.2.1, hx.1.1.1⟩, by omega⟩, (hPQ x).mp hx.2⟩
  · intro x₁ _ x₂ _ h
    rcases x₁ with ⟨a₁, b₁, c₁⟩; rcases x₂ with ⟨a₂, b₂, c₂⟩
    simp only [Prod.mk.injEq] at h ⊢; exact ⟨h.2.2, h.2.1, h.1⟩
  · intro y hy
    refine ⟨(y.2.2, y.2.1, y.1), ?_, by rcases y with ⟨a, b, c⟩; rfl⟩
    simp only [mem_filter, Tle, mem_product, mem_range] at hy ⊢
    refine ⟨⟨⟨hy.1.1.2.2, hy.1.1.2.1, hy.1.1.1⟩, by omega⟩, (hPQ (y.2.2, y.2.1, y.1)).mpr hy.2⟩
  · intro x _; exact hg x

lemma Tlt_swap12_sum {α : Type*} [AddCommMonoid α] (N : ℕ)
    (P Q : ℕ × ℕ × ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (g : ℕ × ℕ × ℕ → α)
    (hPQ : ∀ x, P x ↔ Q (x.2.1, x.1, x.2.2))
    (hg : ∀ x, g x = g (x.2.1, x.1, x.2.2)) :
    ∑ x ∈ (Tlt N).filter P, g x = ∑ x ∈ (Tlt N).filter Q, g x := by
  refine Finset.sum_bij (fun x _ => (x.2.1, x.1, x.2.2)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, Tlt, mem_product, mem_range] at hx ⊢
    refine ⟨⟨⟨hx.1.1.2.1, hx.1.1.1, hx.1.1.2.2⟩, by omega⟩, (hPQ x).mp hx.2⟩
  · intro x₁ _ x₂ _ h
    rcases x₁ with ⟨a₁, b₁, c₁⟩; rcases x₂ with ⟨a₂, b₂, c₂⟩
    simp only [Prod.mk.injEq] at h ⊢; exact ⟨h.2.1, h.1, h.2.2⟩
  · intro y hy
    refine ⟨(y.2.1, y.1, y.2.2), ?_, by rcases y with ⟨a, b, c⟩; rfl⟩
    simp only [mem_filter, Tlt, mem_product, mem_range] at hy ⊢
    refine ⟨⟨⟨hy.1.1.2.1, hy.1.1.1, hy.1.1.2.2⟩, by omega⟩, (hPQ (y.2.1, y.1, y.2.2)).mpr hy.2⟩
  · intro x _; exact hg x

lemma Tlt_swap13_sum {α : Type*} [AddCommMonoid α] (N : ℕ)
    (P Q : ℕ × ℕ × ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (g : ℕ × ℕ × ℕ → α)
    (hPQ : ∀ x, P x ↔ Q (x.2.2, x.2.1, x.1))
    (hg : ∀ x, g x = g (x.2.2, x.2.1, x.1)) :
    ∑ x ∈ (Tlt N).filter P, g x = ∑ x ∈ (Tlt N).filter Q, g x := by
  refine Finset.sum_bij (fun x _ => (x.2.2, x.2.1, x.1)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, Tlt, mem_product, mem_range] at hx ⊢
    refine ⟨⟨⟨hx.1.1.2.2, hx.1.1.2.1, hx.1.1.1⟩, by omega⟩, (hPQ x).mp hx.2⟩
  · intro x₁ _ x₂ _ h
    rcases x₁ with ⟨a₁, b₁, c₁⟩; rcases x₂ with ⟨a₂, b₂, c₂⟩
    simp only [Prod.mk.injEq] at h ⊢; exact ⟨h.2.2, h.2.1, h.1⟩
  · intro y hy
    refine ⟨(y.2.2, y.2.1, y.1), ?_, by rcases y with ⟨a, b, c⟩; rfl⟩
    simp only [mem_filter, Tlt, mem_product, mem_range] at hy ⊢
    refine ⟨⟨⟨hy.1.1.2.2, hy.1.1.2.1, hy.1.1.1⟩, by omega⟩, (hPQ (y.2.2, y.2.1, y.1)).mpr hy.2⟩
  · intro x _; exact hg x

-- ============================================================================
-- Section 3: Part 1 Glue — a(n * p^r) ≡ a(n * p^(r-1)) (mod p^(3*r))
-- ============================================================================

lemma part1_glue (a_fn : ℕ → ℕ)
    (ha : ∀ N : ℕ, a_fn N = ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1 - i), ∑ l ∈ range (N + 1 - i - j),
      (4 * N - i - j - l).choose (3 * N) *
        (N.choose i) ^ 2 * (N.choose j) ^ 2 * (N.choose l) ^ 2)
    (hkaz : ∀ (p a b : ℕ), p.Prime → 5 ≤ p → 0 < b → b < a →
      (p : ℤ) ^ (3 + padicValNat p a + padicValNat p b + padicValNat p (a - b) +
          padicValNat p (a.choose b)) ∣ (((a * p).choose (b * p) : ℤ) - (a.choose b : ℤ)))
    (hS1 : ∀ (p r s n m : ℕ), p.Prime → 5 ≤ p → 1 ≤ r → 1 ≤ s → s ≤ r →
      p ^ (s - 1) ∣ m → m ≤ n * p ^ (r - 1) →
      (p : ℤ) ^ (2 * r + s) ∣
        ∑ i ∈ (range (n * p ^ r + 1 - m * p)).filter (fun i => ¬ p ∣ i),
          (((4 * (n * p ^ r) - m * p - i).choose (3 * (n * p ^ r)) : ℤ) *
            (((n * p ^ r).choose i : ℤ) ^ 2)))
    (p n r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    Nat.ModEq (p ^ (3 * r)) (a_fn (n * p ^ r)) (a_fn (n * p ^ (r - 1))) := by
  have : Fact p.Prime := ⟨hp⟩
  set M := n * p ^ (r - 1)
  set N := n * p ^ r
  have hMp : M * p = N := by
    dsimp only [M, N]; rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hr]
  have hM_pos : 0 < M := Nat.mul_pos hn (pow_pos hp.pos _)
  have hN_pos : 0 < N := Nat.mul_pos hn (pow_pos hp.pos _)
  have hM_dvd : p ^ (r - 1) ∣ M := dvd_mul_left _ _
  have hN_dvd : p ^ r ∣ N := dvd_mul_left _ _
  let f : ℕ → ℕ × ℕ × ℕ → ℤ := fun K x =>
    ((4 * K - x.1 - x.2.1 - x.2.2).choose (3 * K) : ℤ) *
      ((K.choose x.1 : ℤ) ^ 2) * ((K.choose x.2.1 : ℤ) ^ 2) * ((K.choose x.2.2 : ℤ) ^ 2)
  have haN : (a_fn N : ℤ) = ∑ x ∈ Tle N, f N x := by
    rw [ha N, triple_sum_le_eq_flat]; push_cast; rfl
  have haM : (a_fn M : ℤ) = ∑ x ∈ Tle M, f M x := by
    rw [ha M, triple_sum_le_eq_flat]; push_cast; rfl
  -- Enough to show (p : ℤ) ^ (3 * r) ∣ (a_fn N : ℤ) - (a_fn M : ℤ)
  suffices hdvd : (p : ℤ) ^ (3 * r) ∣ ((a_fn N : ℤ) - (a_fn M : ℤ)) by
    exact (Int.natCast_modEq_iff).mp (Int.modEq_iff_dvd.mpr (by simpa [neg_sub] using dvd_neg.mpr hdvd))
  rw [haN, haM, sum_partition_p p (Tle N) (f N)]
  -- Piece 0: S0 matches ∑_{x ∈ Tle M} f M x term-by-term mod p^(3*r)!
  have hS0_bij : ∑ x ∈ (Tle N).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), f N x =
      ∑ x ∈ Tle M, f N (x.1 * p, x.2.1 * p, x.2.2 * p) := by
    symm
    refine Finset.sum_bij (fun x _ => (x.1 * p, x.2.1 * p, x.2.2 * p)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Tle, mem_filter, mem_product, mem_range] at hx ⊢
      refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, dvd_mul_left p x.1, dvd_mul_left p x.2.1, dvd_mul_left p x.2.2⟩
      · have : x.1 * p ≤ M * p := Nat.mul_le_mul_right p (by omega); omega
      · have : x.2.1 * p ≤ M * p := Nat.mul_le_mul_right p (by omega); omega
      · have : x.2.2 * p ≤ M * p := Nat.mul_le_mul_right p (by omega); omega
      · have : (x.1 + x.2.1 + x.2.2) * p ≤ M * p := Nat.mul_le_mul_right p hx.2
        linarith [hMp]
    · intro x₁ _ x₂ _ h
      rcases x₁ with ⟨a₁, b₁, c₁⟩; rcases x₂ with ⟨a₂, b₂, c₂⟩
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨Nat.eq_of_mul_eq_mul_right hp.pos h.1,
             Nat.eq_of_mul_eq_mul_right hp.pos h.2.1,
             Nat.eq_of_mul_eq_mul_right hp.pos h.2.2⟩
    · intro y hy
      simp only [Tle, mem_filter, mem_product, mem_range] at hy
      rcases hy.2.1 with ⟨a, ha'⟩
      rcases hy.2.2.1 with ⟨b, hb'⟩
      rcases hy.2.2.2 with ⟨c, hc'⟩
      refine ⟨(a, b, c), ?_, by ext <;> dsimp only <;> linarith⟩
      simp only [Tle, mem_filter, mem_product, mem_range]
      have hsum : (a + b + c) * p ≤ M * p := by linarith [hy.1.2, hMp]
      have hsum' : a + b + c ≤ M := Nat.le_of_mul_le_mul_right hsum hp.pos
      exact ⟨⟨by omega, by omega, by omega⟩, hsum'⟩
    · intro _ _; rfl
  have hS0_dvd : (p : ℤ) ^ (3 * r) ∣
      ((∑ x ∈ (Tle N).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), f N x) -
        ∑ x ∈ Tle M, f M x) := by
    rw [hS0_bij, ← sum_sub_distrib]
    apply Finset.dvd_sum; intro x hx
    have hx_le : x.1 + x.2.1 + x.2.2 ≤ M := (mem_filter.mp hx).2
    -- Helper: p^(3*r) ∣ (C(N, k*p)^2 - C(M, k)^2) for any k ≤ M!
    have hsq_dvd : ∀ k, k ≤ M → (p : ℤ) ^ (3 * r) ∣ (((N.choose (k * p) : ℤ) ^ 2) - ((M.choose k : ℤ) ^ 2)) := by
      intro k hkM
      by_cases hk0 : k = 0
      · subst hk0; simp
      by_cases hkM_eq : k = M
      · subst hkM_eq; rw [hMp]; simp
      have hk_pos : 0 < k := by omega
      have hk_lt : k < M := by omega
      set e := min (r - 1) (padicValNat p k)
      have he_r : e ≤ r - 1 := Nat.min_le_left _ _
      have he_k : e ≤ padicValNat p k := Nat.min_le_right _ _
      have hkaz_k := hkaz p M k hp hp5 hk_pos hk_lt
      rw [hMp] at hkaz_k
      have hvM : r - 1 ≤ padicValNat p M := (padicValNat_dvd_iff_le hM_pos.ne').mp hM_dvd
      have hvk_dvd : p ^ e ∣ k := (padicValNat_dvd_iff_le hk_pos.ne').mpr he_k
      have hvMk : e ≤ padicValNat p (M - k) := by
        have hsub : p ^ e ∣ M - k := Nat.dvd_sub (dvd_trans (pow_dvd_pow p he_r) hM_dvd) hvk_dvd
        exact (padicValNat_dvd_iff_le (by omega)).mp hsub
      have hchM_dvd : p ^ (r - 1 - e) ∣ M.choose k := by
        by_cases her_eq : e = r - 1
        · rw [her_eq, Nat.sub_self, pow_zero]; exact one_dvd _
        · have hveq : padicValNat p k = e := by omega
          exact dvd_choose_of_pow_dvd hp hM_dvd hM_pos hk_pos hkM he_r (by omega)
      have hchN_dvd : p ^ (r - 1 - e) ∣ N.choose (k * p) := by
        by_cases her_eq : e = r - 1
        · rw [her_eq, Nat.sub_self, pow_zero]; exact one_dvd _
        · have hveq : padicValNat p k = e := by omega
          have hvkp : padicValNat p (k * p) ≤ e + 1 := by
            rw [padicValNat.mul hk_pos.ne' hp.ne_zero, padicValNat.self hp.one_lt]; omega
          have h1 := dvd_choose_of_pow_dvd hp hN_dvd hN_pos (Nat.mul_pos hk_pos hp.pos)
            (by rw [← hMp]; exact Nat.mul_le_mul_right p hkM) (by omega : e + 1 ≤ r) hvkp
          have hsub_eq : r - (e + 1) = r - 1 - e := by omega
          rwa [hsub_eq] at h1
      have hvchM : r - 1 - e ≤ padicValNat p (M.choose k) :=
        (padicValNat_dvd_iff_le (Nat.choose_pos hkM).ne').mp hchM_dvd
      have hexp1 : 3 + (r - 1) + e + e + (r - 1 - e) ≤
          3 + padicValNat p M + padicValNat p k + padicValNat p (M - k) + padicValNat p (M.choose k) := by
        omega
      have hdiff_dvd : (p : ℤ) ^ (3 + (r - 1) + e + e + (r - 1 - e)) ∣
          ((N.choose (k * p) : ℤ) - (M.choose k : ℤ)) :=
        dvd_trans (pow_dvd_pow (p : ℤ) hexp1) hkaz_k
      have hsum_dvd : (p : ℤ) ^ (r - 1 - e) ∣ ((N.choose (k * p) : ℤ) + (M.choose k : ℤ)) :=
        dvd_add (by exact_mod_cast hchN_dvd) (by exact_mod_cast hchM_dvd)
      have hprod := mul_dvd_mul hdiff_dvd hsum_dvd
      rw [← pow_add] at hprod
      have hfac : ((N.choose (k * p) : ℤ) ^ 2) - ((M.choose k : ℤ) ^ 2) =
          ((N.choose (k * p) : ℤ) - (M.choose k : ℤ)) * ((N.choose (k * p) : ℤ) + (M.choose k : ℤ)) := by ring
      rw [hfac]
      exact dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hprod
    -- Also show p^(3*r) ∣ (C(4N - s*p, 3N) - C(4M - s, 3M)) * B1 * B2 * B3
    set s := x.1 + x.2.1 + x.2.2
    have hA0_dvd : (p : ℤ) ^ (3 * r) ∣
        (((4 * N - x.1 * p - x.2.1 * p - x.2.2 * p).choose (3 * N) : ℤ) -
          ((4 * M - x.1 - x.2.1 - x.2.2).choose (3 * M) : ℤ)) *
        ((M.choose x.1 : ℤ) ^ 2) * ((M.choose x.2.1 : ℤ) ^ 2) * ((M.choose x.2.2 : ℤ) ^ 2) := by
      have hsubN : 4 * N - x.1 * p - x.2.1 * p - x.2.2 * p = (4 * M - s) * p := by
        have h1 : x.1 * p + x.2.1 * p + x.2.2 * p = s * p := by dsimp only [s]; ring
        have h2 : (4 * M - s) * p = 4 * N - s * p := by rw [Nat.sub_mul, ← hMp]; ring
        omega
      have hsubM : 4 * M - x.1 - x.2.1 - x.2.2 = 4 * M - s := by dsimp only [s]; omega
      have h3N : 3 * N = (3 * M) * p := by rw [← hMp]; ring
      rw [hsubN, hsubM, h3N]
      by_cases hsM : s = M
      · have h1 : 4 * M - s = 3 * M := by omega
        rw [h1, Nat.choose_self, Nat.choose_self]; simp
      have hkaz_s := hkaz p (4 * M - s) (3 * M) hp hp5 (by omega) (by omega)
      have hv3M : r - 1 ≤ padicValNat p (3 * M) :=
        (padicValNat_dvd_iff_le (by omega)).mp (dvd_mul_of_dvd_right hM_dvd 3)
      by_cases hs0 : s = 0
      · rw [hs0] at hkaz_s ⊢
        have hv4M : r - 1 ≤ padicValNat p (4 * M - 0) :=
          (padicValNat_dvd_iff_le (by omega)).mp (by simpa using dvd_mul_of_dvd_right hM_dvd 4)
        have hv1M : r - 1 ≤ padicValNat p (4 * M - 0 - 3 * M) :=
          (padicValNat_dvd_iff_le (by omega)).mp (by
            have : 4 * M - 0 - 3 * M = M := by omega
            rw [this]; exact hM_dvd)
        have hd0 : (p : ℤ) ^ (3 * r) ∣ (((4 * M - 0) * p).choose (3 * M * p) - ((4 * M - 0).choose (3 * M) : ℤ)) :=
          dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hkaz_s
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd0 _) _) _
      set e := min (r - 1) (padicValNat p s)
      have he_r : e ≤ r - 1 := Nat.min_le_left _ _
      have he_s : e ≤ padicValNat p s := Nat.min_le_right _ _
      have hps : p ^ e ∣ s := (padicValNat_dvd_iff_le hs0).mpr he_s
      have hpM : p ^ e ∣ M := dvd_trans (pow_dvd_pow p he_r) hM_dvd
      have hv4 : e ≤ padicValNat p (4 * M - s) :=
        (padicValNat_dvd_iff_le (by omega)).mp (Nat.dvd_sub (dvd_mul_of_dvd_right hpM 4) hps)
      have hv1 : e ≤ padicValNat p (4 * M - s - 3 * M) :=
        (padicValNat_dvd_iff_le (by omega)).mp (by
          have : 4 * M - s - 3 * M = M - s := by omega
          rw [this]; exact Nat.dvd_sub hpM hps)
      have hdiff0 : (p : ℤ) ^ (3 + (r - 1) + 2 * e) ∣
          (((4 * M - s) * p).choose (3 * M * p) - ((4 * M - s).choose (3 * M) : ℤ)) :=
        dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hkaz_s
      by_cases her_eq : e = r - 1
      · have hd0 : (p : ℤ) ^ (3 * r) ∣
            (((4 * M - s) * p).choose (3 * M * p) - ((4 * M - s).choose (3 * M) : ℤ)) :=
          dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hdiff0
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd0 _) _) _
      have hndvd_s : ¬ p ^ (e + 1) ∣ s := by
        intro hdiv
        have := (padicValNat_dvd_iff_le hs0).mp hdiv
        omega
      have hB_dvd : (p : ℤ) ^ (2 * (r - 1 - e)) ∣
          ((M.choose x.1 : ℤ) ^ 2) * ((M.choose x.2.1 : ℤ) ^ 2) * ((M.choose x.2.2 : ℤ) ^ 2) := by
        have hch : ∀ k, k ≤ M → ¬ p ^ (e + 1) ∣ k → (p : ℤ) ^ (2 * (r - 1 - e)) ∣ ((M.choose k : ℤ) ^ 2) := by
          intro k hkM hknd
          have hk_pos : 0 < k := Nat.pos_of_ne_zero (fun h0 => hknd (h0 ▸ dvd_zero _))
          have hvk := padicValNat_le_of_not_pow_succ_dvd hp hknd
          have h1 := dvd_choose_of_pow_dvd hp hM_dvd hM_pos hk_pos hkM he_r hvk
          have h2 : (p : ℤ) ^ (2 * (r - 1 - e)) = ((p : ℤ) ^ (r - 1 - e)) ^ 2 := by rw [← pow_mul, mul_comm]
          rw [h2]; exact pow_dvd_pow_of_dvd (by exact_mod_cast h1) 2
        rcases not_pow_succ_dvd_of_sum_not_dvd hndvd_s with h12 | h3
        · rcases not_pow_succ_dvd_of_sum_not_dvd h12 with h1 | h2
          · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (hch x.1 (by omega) h1) _) _
          · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hch x.2.1 (by omega) h2) _) _
        · exact dvd_mul_of_dvd_right (hch x.2.2 (by omega) h3) _
      have hprod := mul_dvd_mul hdiff0 hB_dvd
      rw [← pow_add] at hprod
      have hassoc : (((4 * M - s) * p).choose (3 * M * p) - ((4 * M - s).choose (3 * M) : ℤ)) *
            ((M.choose x.1 : ℤ) ^ 2) * ((M.choose x.2.1 : ℤ) ^ 2) * ((M.choose x.2.2 : ℤ) ^ 2) =
          (((4 * M - s) * p).choose (3 * M * p) - ((4 * M - s).choose (3 * M) : ℤ)) *
            (((M.choose x.1 : ℤ) ^ 2) * ((M.choose x.2.1 : ℤ) ^ 2) * ((M.choose x.2.2 : ℤ) ^ 2)) := by ring
      rw [hassoc]
      exact dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hprod
    -- Telescope f N (x.1*p, x.2.1*p, x.2.2*p) - f M x!
    dsimp only [f]
    set A0 : ℤ := ((4 * N - x.1 * p - x.2.1 * p - x.2.2 * p).choose (3 * N) : ℤ)
    set B0 : ℤ := ((4 * M - x.1 - x.2.1 - x.2.2).choose (3 * M) : ℤ)
    set A1 : ℤ := (N.choose (x.1 * p) : ℤ) ^ 2
    set B1 : ℤ := (M.choose x.1 : ℤ) ^ 2
    set A2 : ℤ := (N.choose (x.2.1 * p) : ℤ) ^ 2
    set B2 : ℤ := (M.choose x.2.1 : ℤ) ^ 2
    set A3 : ℤ := (N.choose (x.2.2 * p) : ℤ) ^ 2
    set B3 : ℤ := (M.choose x.2.2 : ℤ) ^ 2
    have htele : A0 * A1 * A2 * A3 - B0 * B1 * B2 * B3 =
        (A0 - B0) * B1 * B2 * B3 +
        A0 * (A1 - B1) * B2 * B3 +
        A0 * A1 * (A2 - B2) * B3 +
        A0 * A1 * A2 * (A3 - B3) := by ring
    rw [htele]
    exact dvd_add (dvd_add (dvd_add hA0_dvd
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hsq_dvd x.1 (by omega)) _) _) _))
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hsq_dvd x.2.1 (by omega)) _) _))
      (dvd_mul_of_dvd_right (hsq_dvd x.2.2 (by omega)) _)
  -- Piece 1: S1a = S1b = S1c by symmetry, and p^(3*r) ∣ S1a by S1_vanish_dvd!
  have hS1a_dvd : (p : ℤ) ^ (3 * r) ∣
      ∑ x ∈ (Tle N).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), f N x := by
    -- Reindex by j' ∈ range (M + 1), l' ∈ range (M + 1 - j'), i ∈ (range (N + 1 - (j' + l')*p)).filter (¬ p ∣ ·)
    have hreidx : ∑ x ∈ (Tle N).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), f N x =
        ∑ j' ∈ range (M + 1), ∑ l' ∈ range (M + 1 - j'),
          ((N.choose (j' * p) : ℤ) ^ 2) * ((N.choose (l' * p) : ℤ) ^ 2) *
          ∑ i ∈ (range (N + 1 - (j' + l') * p)).filter (fun i => ¬ p ∣ i),
            (((4 * N - (j' + l') * p - i).choose (3 * N) : ℤ) * ((N.choose i : ℤ) ^ 2)) := by
      have hflat : ∑ j' ∈ range (M + 1), ∑ l' ∈ range (M + 1 - j'),
            ((N.choose (j' * p) : ℤ) ^ 2) * ((N.choose (l' * p) : ℤ) ^ 2) *
            ∑ i ∈ (range (N + 1 - (j' + l') * p)).filter (fun i => ¬ p ∣ i),
              (((4 * N - (j' + l') * p - i).choose (3 * N) : ℤ) * ((N.choose i : ℤ) ^ 2)) =
          ∑ x ∈ (range (N + 1) ×ˢ (range (M + 1) ×ˢ range (M + 1))).filter
              (fun x => ¬ p ∣ x.1 ∧ x.1 + (x.2.1 + x.2.2) * p ≤ N),
            f N (x.1, x.2.1 * p, x.2.2 * p) := by
        rw [sum_filter, sum_product, sum_comm]
        have hswap : ∑ y ∈ range (M + 1) ×ˢ range (M + 1), ∑ i ∈ range (N + 1),
              (if ¬ p ∣ i ∧ i + (y.1 + y.2) * p ≤ N then f N (i, y.1 * p, y.2 * p) else 0) =
            ∑ j' ∈ range (M + 1), ∑ l' ∈ range (M + 1), ∑ i ∈ range (N + 1),
              (if ¬ p ∣ i ∧ i + (j' + l') * p ≤ N then f N (i, j' * p, l' * p) else 0) := by
          rw [sum_product]
        rw [hswap]
        apply sum_congr rfl; intro j' hj'
        have hj'M : j' ≤ M := Nat.lt_succ_iff.mp (mem_range.mp hj')
        have hinner : ∀ l' ∈ range (M + 1),
            (∑ i ∈ range (N + 1),
              if ¬ p ∣ i ∧ i + (j' + l') * p ≤ N then f N (i, j' * p, l' * p) else 0) =
            if l' ∈ range (M + 1 - j') then
              ((N.choose (j' * p) : ℤ) ^ 2) * ((N.choose (l' * p) : ℤ) ^ 2) *
              ∑ i ∈ (range (N + 1 - (j' + l') * p)).filter (fun i => ¬ p ∣ i),
                (((4 * N - (j' + l') * p - i).choose (3 * N) : ℤ) * ((N.choose i : ℤ) ^ 2))
            else 0 := by
          intro l' _
          by_cases hl' : l' ∈ range (M + 1 - j')
          · rw [if_pos hl', mul_sum, sum_filter]
            have hl'M : j' + l' ≤ M := by simp only [mem_range] at hl'; omega
            have hjp_le : (j' + l') * p ≤ N := by rw [← hMp]; exact Nat.mul_le_mul_right p hl'M
            rw [← sum_subset (range_mono (by omega : N + 1 - (j' + l') * p ≤ N + 1))]
            · apply sum_congr rfl; intro i hi
              have hi' : i + (j' + l') * p ≤ N := by simp only [mem_range] at hi; omega
              by_cases hind : ¬ p ∣ i
              · rw [if_pos ⟨hind, hi'⟩, if_pos hind]
                dsimp only [f]
                have hsub : 4 * N - i - j' * p - l' * p = 4 * N - (j' + l') * p - i := by
                  have : (j' + l') * p = j' * p + l' * p := by ring
                  omega
                rw [hsub]; ring
              · rw [if_neg (by tauto), if_neg hind]
            · intro i _ hi_not
              have hgt : ¬ (i + (j' + l') * p ≤ N) := by simp only [mem_range] at hi_not; omega
              rw [if_neg (by tauto)]
          · rw [if_neg hl']
            apply sum_eq_zero; intro i _
            have hl'gt : M < j' + l' := by simp only [mem_range] at hl'; omega
            have hgt : N < (j' + l') * p := by rw [← hMp]; exact Nat.mul_lt_mul_of_pos_right hl'gt hp.pos
            rw [if_neg (by omega)]
        rw [sum_congr rfl hinner, sum_ite_mem, inter_eq_right.mpr (range_mono (by omega : M + 1 - j' ≤ M + 1))]
      rw [hflat]
      symm
      refine Finset.sum_bij (fun x _ => (x.1, x.2.1 * p, x.2.2 * p)) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [mem_filter, Tle, mem_product, mem_range] at hx ⊢
        have h1 : x.2.1 * p ≤ N := by rw [← hMp]; exact Nat.mul_le_mul_right p (by omega)
        have h2 : x.2.2 * p ≤ N := by rw [← hMp]; exact Nat.mul_le_mul_right p (by omega)
        have hsum : x.1 + x.2.1 * p + x.2.2 * p ≤ N := by linarith [hx.2.2]
        exact ⟨⟨⟨hx.1.1, by omega, by omega⟩, hsum⟩, hx.2.1, dvd_mul_left p _, dvd_mul_left p _⟩
      · intro x₁ _ x₂ _ h
        rcases x₁ with ⟨a₁, b₁, c₁⟩; rcases x₂ with ⟨a₂, b₂, c₂⟩
        simp only [Prod.mk.injEq] at h ⊢
        exact ⟨h.1, Nat.eq_of_mul_eq_mul_right hp.pos h.2.1, Nat.eq_of_mul_eq_mul_right hp.pos h.2.2⟩
      · intro y hy
        simp only [mem_filter, Tle, mem_product, mem_range] at hy
        rcases hy.2.2.1 with ⟨b, hb'⟩
        rcases hy.2.2.2 with ⟨c, hc'⟩
        have hbc_p : (b + c) * p ≤ M * p := by linarith [hy.1.2, hMp]
        have hbc : b + c ≤ M := Nat.le_of_mul_le_mul_right hbc_p hp.pos
        refine ⟨(y.1, b, c), ?_, by ext <;> dsimp only <;> linarith⟩
        simp only [mem_filter, mem_product, mem_range]
        exact ⟨⟨hy.1.1.1, by omega, by omega⟩, hy.2.1, by linarith [hy.1.2]⟩
      · intro _ _; rfl
    rw [hreidx]
    apply Finset.dvd_sum; intro j' hj'
    apply Finset.dvd_sum; intro l' hl'
    have hjlM : j' + l' ≤ M := by simp only [mem_range] at hj' hl'; omega
    set m := j' + l'
    by_cases hm0 : m = 0
    · have hS := hS1 p r r n m hp hp5 hr hr le_rfl (by rw [hm0]; exact dvd_zero _) hjlM
      have h3r : 2 * r + r = 3 * r := by omega
      rw [h3r] at hS
      exact dvd_mul_of_dvd_right hS _
    set e := min (r - 1) (padicValNat p m)
    have he_r : e ≤ r - 1 := Nat.min_le_left _ _
    have he_m : e ≤ padicValNat p m := Nat.min_le_right _ _
    have hS := hS1 p r (e + 1) n m hp hp5 hr (by omega) (by omega)
      (by simpa using (padicValNat_dvd_iff_le hm0).mpr he_m) hjlM
    by_cases her_eq : e = r - 1
    · have h3r : 2 * r + (e + 1) = 3 * r := by omega
      rw [h3r] at hS
      exact dvd_mul_of_dvd_right hS _
    have hndvd_m : ¬ p ^ (e + 1) ∣ m := fun hdiv => by
      have := (padicValNat_dvd_iff_le hm0).mp hdiv; omega
    have hpre_dvd : (p : ℤ) ^ (2 * (r - 1 - e)) ∣
        ((N.choose (j' * p) : ℤ) ^ 2) * ((N.choose (l' * p) : ℤ) ^ 2) := by
      have hch : ∀ k, k ≤ M → ¬ p ^ (e + 1) ∣ k → (p : ℤ) ^ (2 * (r - 1 - e)) ∣ ((N.choose (k * p) : ℤ) ^ 2) := by
        intro k hkM hknd
        have hk_pos : 0 < k := Nat.pos_of_ne_zero (fun h0 => hknd (h0 ▸ dvd_zero _))
        have hvk := padicValNat_le_of_not_pow_succ_dvd hp hknd
        have hvkp : padicValNat p (k * p) ≤ e + 1 := by
          rw [padicValNat.mul hk_pos.ne' hp.ne_zero, padicValNat.self hp.one_lt]; omega
        have h1 := dvd_choose_of_pow_dvd hp hN_dvd hN_pos (Nat.mul_pos hk_pos hp.pos)
          (by rw [← hMp]; exact Nat.mul_le_mul_right p hkM) (by omega : e + 1 ≤ r) hvkp
        have hsub : r - (e + 1) = r - 1 - e := by omega
        rw [hsub] at h1
        have h2 : (p : ℤ) ^ (2 * (r - 1 - e)) = ((p : ℤ) ^ (r - 1 - e)) ^ 2 := by rw [← pow_mul, mul_comm]
        rw [h2]; exact pow_dvd_pow_of_dvd (by exact_mod_cast h1) 2
      rcases not_pow_succ_dvd_of_sum_not_dvd hndvd_m with hj_nd | hl_nd
      · exact dvd_mul_of_dvd_left (hch j' (by omega) hj_nd) _
      · exact dvd_mul_of_dvd_right (hch l' (by omega) hl_nd) _
    have hprod := mul_dvd_mul hpre_dvd hS
    rw [← pow_add] at hprod
    exact dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hprod
  have hS1b_eq : ∑ x ∈ (Tle N).filter (fun x => p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ p ∣ x.2.2), f N x =
      ∑ x ∈ (Tle N).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), f N x := by
    apply Tle_swap12_sum N _ _ (f N) (fun x => by dsimp only; tauto)
    intro x; dsimp only [f]
    have hsub : 4 * N - x.1 - x.2.1 - x.2.2 = 4 * N - x.2.1 - x.1 - x.2.2 := by omega
    rw [hsub]; ring
  have hS1c_eq : ∑ x ∈ (Tle N).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2), f N x =
      ∑ x ∈ (Tle N).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), f N x := by
    apply Tle_swap13_sum N _ _ (f N) (fun x => by dsimp only; tauto)
    intro x; dsimp only [f]
    have hsub : 4 * N - x.1 - x.2.1 - x.2.2 = 4 * N - x.2.2 - x.2.1 - x.1 := by omega
    rw [hsub]; ring
  -- Piece 23: at least two of i, j, l not divisible by p -> p^(4*r) ∣ f N x term-by-term!
  have hS23_dvd : (p : ℤ) ^ (3 * r) ∣
      ∑ x ∈ (Tle N).filter (fun x =>
        (¬ p ∣ x.1 ∧ ¬ p ∣ x.2.1) ∨ (¬ p ∣ x.1 ∧ ¬ p ∣ x.2.2) ∨ (¬ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2)), f N x := by
    apply Finset.dvd_sum; intro x hx
    have hx_le : x.1 + x.2.1 + x.2.2 ≤ N := (mem_filter.mp (mem_filter.mp hx).1).2
    have hch_nd : ∀ k, k ≤ N → ¬ p ∣ k → (p : ℤ) ^ (2 * r) ∣ ((N.choose k : ℤ) ^ 2) := by
      intro k hkN hknd
      have hk_pos : 0 < k := Nat.pos_of_ne_zero (fun h0 => hknd (h0 ▸ dvd_zero _))
      have h1 := dvd_choose_of_pow_dvd hp hN_dvd hN_pos hk_pos hkN (Nat.zero_le r)
        (by rw [padicValNat_eq_zero_of_not_dvd hknd])
      rw [Nat.sub_zero] at h1
      have h2 : (p : ℤ) ^ (2 * r) = ((p : ℤ) ^ r) ^ 2 := by rw [← pow_mul, mul_comm]
      rw [h2]; exact pow_dvd_pow_of_dvd (by exact_mod_cast h1) 2
    have h4r_3r : (p : ℤ) ^ (3 * r) ∣ (p : ℤ) ^ (2 * r + 2 * r) := pow_dvd_pow (p : ℤ) (by omega)
    dsimp only [f]
    rcases (mem_filter.mp hx).2 with ⟨h1, h2⟩ | ⟨h1, h3⟩ | ⟨h2, h3⟩
    · have hm := mul_dvd_mul (hch_nd x.1 (by omega) h1) (hch_nd x.2.1 (by omega) h2)
      rw [← pow_add] at hm
      have hrew : ((4 * N - x.1 - x.2.1 - x.2.2).choose (3 * N) : ℤ) *
            ((N.choose x.1 : ℤ) ^ 2) * ((N.choose x.2.1 : ℤ) ^ 2) * ((N.choose x.2.2 : ℤ) ^ 2) =
          (((N.choose x.1 : ℤ) ^ 2) * ((N.choose x.2.1 : ℤ) ^ 2)) *
            (((4 * N - x.1 - x.2.1 - x.2.2).choose (3 * N) : ℤ) * ((N.choose x.2.2 : ℤ) ^ 2)) := by ring
      rw [hrew]; exact dvd_mul_of_dvd_left (dvd_trans h4r_3r hm) _
    · have hm := mul_dvd_mul (hch_nd x.1 (by omega) h1) (hch_nd x.2.2 (by omega) h3)
      rw [← pow_add] at hm
      have hrew : ((4 * N - x.1 - x.2.1 - x.2.2).choose (3 * N) : ℤ) *
            ((N.choose x.1 : ℤ) ^ 2) * ((N.choose x.2.1 : ℤ) ^ 2) * ((N.choose x.2.2 : ℤ) ^ 2) =
          (((N.choose x.1 : ℤ) ^ 2) * ((N.choose x.2.2 : ℤ) ^ 2)) *
            (((4 * N - x.1 - x.2.1 - x.2.2).choose (3 * N) : ℤ) * ((N.choose x.2.1 : ℤ) ^ 2)) := by ring
      rw [hrew]; exact dvd_mul_of_dvd_left (dvd_trans h4r_3r hm) _
    · have hm := mul_dvd_mul (hch_nd x.2.1 (by omega) h2) (hch_nd x.2.2 (by omega) h3)
      rw [← pow_add] at hm
      have hrew : ((4 * N - x.1 - x.2.1 - x.2.2).choose (3 * N) : ℤ) *
            ((N.choose x.1 : ℤ) ^ 2) * ((N.choose x.2.1 : ℤ) ^ 2) * ((N.choose x.2.2 : ℤ) ^ 2) =
          (((N.choose x.2.1 : ℤ) ^ 2) * ((N.choose x.2.2 : ℤ) ^ 2)) *
            (((4 * N - x.1 - x.2.1 - x.2.2).choose (3 * N) : ℤ) * ((N.choose x.1 : ℤ) ^ 2)) := by ring
      rw [hrew]; exact dvd_mul_of_dvd_left (dvd_trans h4r_3r hm) _
  -- Combine all 5 pieces!
  rw [hS1b_eq, hS1c_eq]
  have hcomb :
      (∑ x ∈ (Tle N).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), f N x) +
        (∑ x ∈ (Tle N).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), f N x) +
        (∑ x ∈ (Tle N).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), f N x) +
        (∑ x ∈ (Tle N).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), f N x) +
        (∑ x ∈ (Tle N).filter (fun x =>
          (¬ p ∣ x.1 ∧ ¬ p ∣ x.2.1) ∨ (¬ p ∣ x.1 ∧ ¬ p ∣ x.2.2) ∨ (¬ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2)), f N x) -
      ∑ x ∈ Tle M, f M x =
      ((∑ x ∈ (Tle N).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), f N x) -
        ∑ x ∈ Tle M, f M x) +
      3 * (∑ x ∈ (Tle N).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), f N x) +
      (∑ x ∈ (Tle N).filter (fun x =>
        (¬ p ∣ x.1 ∧ ¬ p ∣ x.2.1) ∨ (¬ p ∣ x.1 ∧ ¬ p ∣ x.2.2) ∨ (¬ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2)), f N x) := by
    ring
  rw [hcomb]
  exact dvd_add (dvd_add hS0_dvd (dvd_mul_of_dvd_right hS1a_dvd 3)) hS23_dvd

-- ============================================================================
-- Section 4: Part 2 Glue — a(n * p^r - 1) ≡ a(n * p^(r-1) - 1) (mod p^(3*r))
-- ============================================================================

-- Helper: (A - 1).choose B * A = A.choose B * (A - B) for B < A
lemma choose_sub_one_mul (A B : ℕ) (hBA : B < A) :
    (A - 1).choose B * A = A.choose B * (A - B) := by
  have h1 := Nat.add_one_mul_choose_eq (A - 1) (A - 1 - B)
  have e1 : A - 1 + 1 = A := by omega
  have e2 : A - 1 - B + 1 = A - B := by omega
  rw [e1, e2, Nat.choose_symm (by omega : B ≤ A - 1),
      Nat.choose_symm (by omega : B ≤ A)] at h1
  linarith

-- Helper: (p : ℤ) ^ e ∣ z when z * c is divisible by (p : ℤ) ^ (e + v_p(c))
lemma int_dvd_of_mul_dvd_pow {p e c : ℕ} {z : ℤ} (hp : p.Prime) (hc : c ≠ 0)
    (h : (p : ℤ) ^ (e + padicValNat p c) ∣ z * (c : ℤ)) :
    (p : ℤ) ^ e ∣ z := by
  have : Fact p.Prime := ⟨hp⟩
  set v := padicValNat p c
  have hcv : p ^ v ∣ c := pow_padicValNat_dvd
  rcases hcv with ⟨u, hu⟩
  have hu_ndvd : ¬ p ∣ u := by
    intro hdiv
    have hpow : p ^ (v + 1) ∣ c := by
      rw [hu, pow_succ]
      rcases hdiv with ⟨w, rfl⟩; exact ⟨w, by ring⟩
    have := (padicValNat_dvd_iff_le hc).mp hpow
    omega
  rw [hu, pow_add] at h
  have hcast : z * ((p ^ v * u : ℕ) : ℤ) = (p : ℤ) ^ v * (z * (u : ℤ)) := by push_cast; ring
  rw [hcast] at h
  have h1 : (p : ℤ) ^ e ∣ z * (u : ℤ) := by
    rcases h with ⟨q, hq⟩
    have hpv0 : (p : ℤ) ^ v ≠ 0 := pow_ne_zero v (Nat.cast_ne_zero.mpr hp.ne_zero)
    have hq' : (p : ℤ) ^ v * (z * (u : ℤ)) = (p : ℤ) ^ v * ((p : ℤ) ^ e * q) := by
      rw [hq]; ring
    exact ⟨q, mul_left_cancel₀ hpv0 hq'⟩
  have hcop : IsCoprime ((p : ℤ) ^ e) (u : ℤ) :=
    IsCoprime.pow_left ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu_ndvd).isCoprime
  exact hcop.dvd_of_dvd_mul_right h1

lemma part2_glue (a_fn : ℕ → ℕ)
    (hapred : ∀ N : ℕ, 0 < N → (a_fn (N - 1) : ℤ) =
      ∑ i ∈ range N, ∑ j ∈ range (N - i), ∑ l ∈ range (N - i - j),
        (-1 : ℤ) ^ (N - 1 - i - j - l) *
          ((3 * N - 1).choose (N - 1 - i - j - l) : ℤ) *
          ((N + i - 1).choose i : ℤ) ^ 2 *
          ((N + j - 1).choose j : ℤ) ^ 2 *
          ((N + l - 1).choose l : ℤ) ^ 2)
    (hkaz : ∀ (p a b : ℕ), p.Prime → 5 ≤ p → 0 < b → b < a →
      (p : ℤ) ^ (3 + padicValNat p a + padicValNat p b + padicValNat p (a - b) +
          padicValNat p (a.choose b)) ∣ (((a * p).choose (b * p) : ℤ) - (a.choose b : ℤ)))
    (hS2 : ∀ (p r s n m : ℕ), p.Prime → 5 ≤ p → 1 ≤ r → 1 ≤ s → s ≤ r →
      p ^ (s - 1) ∣ m → m < n * p ^ (r - 1) →
      (p : ℤ) ^ (2 * r + s) ∣
        ∑ i ∈ (range (n * p ^ r - m * p)).filter (fun i => ¬ p ∣ i),
          ((-1 : ℤ) ^ (n * p ^ r - 1 - m * p - i) *
            ((3 * (n * p ^ r) - 1).choose (n * p ^ r - 1 - m * p - i) : ℤ) *
            (((n * p ^ r + i - 1).choose i : ℤ) ^ 2)))
    (p n r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    Nat.ModEq (p ^ (3 * r)) (a_fn (n * p ^ r - 1)) (a_fn (n * p ^ (r - 1) - 1)) := by
  have : Fact p.Prime := ⟨hp⟩
  set M := n * p ^ (r - 1)
  set N := n * p ^ r
  have hMp : M * p = N := by
    dsimp only [M, N]; rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hr]
  have hM_pos : 0 < M := Nat.mul_pos hn (pow_pos hp.pos _)
  have hN_pos : 0 < N := Nat.mul_pos hn (pow_pos hp.pos _)
  have hM_dvd : p ^ (r - 1) ∣ M := dvd_mul_left _ _
  have hN_dvd : p ^ r ∣ N := dvd_mul_left _ _
  let g : ℕ → ℕ × ℕ × ℕ → ℤ := fun K x =>
    (-1 : ℤ) ^ (K - 1 - x.1 - x.2.1 - x.2.2) *
      ((3 * K - 1).choose (K - 1 - x.1 - x.2.1 - x.2.2) : ℤ) *
      ((K + x.1 - 1).choose x.1 : ℤ) ^ 2 *
      ((K + x.2.1 - 1).choose x.2.1 : ℤ) ^ 2 *
      ((K + x.2.2 - 1).choose x.2.2 : ℤ) ^ 2
  have haN : (a_fn (N - 1) : ℤ) = ∑ x ∈ Tlt N, g N x := by
    rw [hapred N hN_pos, triple_sum_lt_eq_flat]
  have haM : (a_fn (M - 1) : ℤ) = ∑ x ∈ Tlt M, g M x := by
    rw [hapred M hM_pos, triple_sum_lt_eq_flat]
  suffices hdvd : (p : ℤ) ^ (3 * r) ∣ ((a_fn (N - 1) : ℤ) - (a_fn (M - 1) : ℤ)) by
    exact (Int.natCast_modEq_iff).mp (Int.modEq_iff_dvd.mpr (by simpa [neg_sub] using dvd_neg.mpr hdvd))
  rw [haN, haM, sum_partition_p p (Tlt N) (g N)]
  -- Piece 0: S0 matches Tlt M term-by-term!
  have hS0_bij : ∑ x ∈ (Tlt N).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g N x =
      ∑ x ∈ Tlt M, g N (x.1 * p, x.2.1 * p, x.2.2 * p) := by
    symm
    refine Finset.sum_bij (fun x _ => (x.1 * p, x.2.1 * p, x.2.2 * p)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Tlt, mem_filter, mem_product, mem_range] at hx ⊢
      refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, dvd_mul_left p x.1, dvd_mul_left p x.2.1, dvd_mul_left p x.2.2⟩
      · rw [← hMp]; exact Nat.mul_lt_mul_of_pos_right hx.1.1 hp.pos
      · rw [← hMp]; exact Nat.mul_lt_mul_of_pos_right hx.1.2.1 hp.pos
      · rw [← hMp]; exact Nat.mul_lt_mul_of_pos_right hx.1.2.2 hp.pos
      · have : (x.1 + x.2.1 + x.2.2) * p < M * p := Nat.mul_lt_mul_of_pos_right hx.2 hp.pos
        linarith [hMp]
    · intro x₁ _ x₂ _ h
      rcases x₁ with ⟨a₁, b₁, c₁⟩; rcases x₂ with ⟨a₂, b₂, c₂⟩
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨Nat.eq_of_mul_eq_mul_right hp.pos h.1,
             Nat.eq_of_mul_eq_mul_right hp.pos h.2.1,
             Nat.eq_of_mul_eq_mul_right hp.pos h.2.2⟩
    · intro y hy
      simp only [Tlt, mem_filter, mem_product, mem_range] at hy
      rcases hy.2.1 with ⟨a, ha'⟩
      rcases hy.2.2.1 with ⟨b, hb'⟩
      rcases hy.2.2.2 with ⟨c, hc'⟩
      have hsum : (a + b + c) * p < M * p := by linarith [hy.1.2, hMp]
      have hsum' : a + b + c < M := Nat.lt_of_mul_lt_mul_right hsum
      refine ⟨(a, b, c), ?_, by ext <;> dsimp only <;> linarith⟩
      simp only [Tlt, mem_filter, mem_product, mem_range]
      exact ⟨⟨by omega, by omega, by omega⟩, hsum'⟩
    · intro _ _; rfl
  have hS0_dvd : (p : ℤ) ^ (3 * r) ∣
      ((∑ x ∈ (Tlt N).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g N x) -
        ∑ x ∈ Tlt M, g M x) := by
    rw [hS0_bij, ← sum_sub_distrib]
    apply Finset.dvd_sum; intro x hx
    have hx_lt : x.1 + x.2.1 + x.2.2 < M := (mem_filter.mp hx).2
    -- Helper 1: p^(3*r) ∣ (C(N + k*p - 1, k*p)^2 - C(M + k - 1, k)^2) for any k!
    have hsq_dvd : ∀ k, (p : ℤ) ^ (3 * r) ∣
        (((N + k * p - 1).choose (k * p) : ℤ) ^ 2 - ((M + k - 1).choose k : ℤ) ^ 2) := by
      intro k
      by_cases hk0 : k = 0
      · subst hk0; simp
      have hk_pos : 0 < k := by omega
      set e := min (r - 1) (padicValNat p k)
      have he_r : e ≤ r - 1 := Nat.min_le_left _ _
      have he_k : e ≤ padicValNat p k := Nat.min_le_right _ _
      -- Identity: (C(N + k*p - 1, k*p) - C(M + k - 1, k)) * (M + k) =
      --   (C((M + k) * p, k * p) - C(M + k, k)) * M!
      have hid1 : (N + k * p - 1).choose (k * p) * (M + k) = ((M + k) * p).choose (k * p) * M := by
        have h1 := choose_sub_one_mul ((M + k) * p) (k * p)
          (Nat.mul_lt_mul_of_pos_right (by omega : k < M + k) hp.pos)
        have e1 : (M + k) * p = N + k * p := by rw [← hMp]; ring
        have e2 : (M + k) * p - k * p = M * p := by rw [← Nat.sub_mul, Nat.add_sub_cancel]
        rw [e2, e1] at h1
        have h2 : ((N + k * p - 1).choose (k * p) * (M + k)) * p =
            (((M + k) * p).choose (k * p) * M) * p := by
          calc ((N + k * p - 1).choose (k * p) * (M + k)) * p
              = (N + k * p - 1).choose (k * p) * (N + k * p) := by rw [← e1]; ring
            _ = (N + k * p).choose (k * p) * (M * p) := h1
            _ = (((M + k) * p).choose (k * p) * M) * p := by rw [← e1]; ring
        exact Nat.eq_of_mul_eq_mul_right hp.pos h2
      have hid2 : (M + k - 1).choose k * (M + k) = (M + k).choose k * M := by
        have h1 := choose_sub_one_mul (M + k) k (by omega)
        rwa [Nat.add_sub_cancel] at h1
      have hdiff_mul : (((N + k * p - 1).choose (k * p) : ℤ) - ((M + k - 1).choose k : ℤ)) * ((M + k : ℕ) : ℤ) =
          ((((M + k) * p).choose (k * p) : ℤ) - ((M + k).choose k : ℤ)) * (M : ℤ) := by
        have h1Z : ((N + k * p - 1).choose (k * p) : ℤ) * ((M + k : ℕ) : ℤ) =
            (((M + k) * p).choose (k * p) : ℤ) * (M : ℤ) := by exact_mod_cast hid1
        have h2Z : ((M + k - 1).choose k : ℤ) * ((M + k : ℕ) : ℤ) =
            ((M + k).choose k : ℤ) * (M : ℤ) := by exact_mod_cast hid2
        linarith
      have hkaz_k := hkaz p (M + k) k hp hp5 hk_pos (by omega)
      have hvM : r - 1 ≤ padicValNat p M := (padicValNat_dvd_iff_le hM_pos.ne').mp hM_dvd
      have hsub_eq : M + k - k = M := Nat.add_sub_cancel M k
      rw [hsub_eq] at hkaz_k
      have hmul_dvd : (p : ℤ) ^ ((3 + 2 * (r - 1) + e) + padicValNat p (M + k)) ∣
          (((N + k * p - 1).choose (k * p) : ℤ) - ((M + k - 1).choose k : ℤ)) * ((M + k : ℕ) : ℤ) := by
        rw [hdiff_mul]
        have hM_dvdZ : (p : ℤ) ^ (r - 1) ∣ (M : ℤ) := by exact_mod_cast hM_dvd
        have hprod := mul_dvd_mul hkaz_k hM_dvdZ
        rw [← pow_add] at hprod
        exact dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hprod
      have hdiff_dvd : (p : ℤ) ^ (3 + 2 * (r - 1) + e) ∣
          (((N + k * p - 1).choose (k * p) : ℤ) - ((M + k - 1).choose k : ℤ)) :=
        int_dvd_of_mul_dvd_pow hp (by omega) hmul_dvd
      have hchM_dvd : p ^ (r - 1 - e) ∣ (M + k - 1).choose k := by
        by_cases her_eq : e = r - 1
        · rw [her_eq, Nat.sub_self, pow_zero]; exact one_dvd _
        · exact dvd_choose_pred_of_pow_dvd hp hM_dvd hM_pos hk_pos he_r (by omega)
      have hchN_dvd : p ^ (r - 1 - e) ∣ (N + k * p - 1).choose (k * p) := by
        by_cases her_eq : e = r - 1
        · rw [her_eq, Nat.sub_self, pow_zero]; exact one_dvd _
        · have hvkp : padicValNat p (k * p) ≤ e + 1 := by
            rw [padicValNat.mul hk_pos.ne' hp.ne_zero, padicValNat.self hp.one_lt]; omega
          have h1 := dvd_choose_pred_of_pow_dvd hp hN_dvd hN_pos (Nat.mul_pos hk_pos hp.pos)
            (by omega : e + 1 ≤ r) hvkp
          have hsub : r - (e + 1) = r - 1 - e := by omega
          rwa [hsub] at h1
      have hsum_dvd : (p : ℤ) ^ (r - 1 - e) ∣
          (((N + k * p - 1).choose (k * p) : ℤ) + ((M + k - 1).choose k : ℤ)) :=
        dvd_add (by exact_mod_cast hchN_dvd) (by exact_mod_cast hchM_dvd)
      have hprod := mul_dvd_mul hdiff_dvd hsum_dvd
      rw [← pow_add] at hprod
      have hfac : ((N + k * p - 1).choose (k * p) : ℤ) ^ 2 - ((M + k - 1).choose k : ℤ) ^ 2 =
          (((N + k * p - 1).choose (k * p) : ℤ) - ((M + k - 1).choose k : ℤ)) *
          (((N + k * p - 1).choose (k * p) : ℤ) + ((M + k - 1).choose k : ℤ)) := by ring
      rw [hfac]
      exact dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hprod
    -- Helper 2: sign equality (-1)^(N - 1 - s*p) = (-1)^(M - 1 - s)
    set s := x.1 + x.2.1 + x.2.2
    have hsign_eq : (-1 : ℤ) ^ (N - 1 - x.1 * p - x.2.1 * p - x.2.2 * p) =
        (-1 : ℤ) ^ (M - 1 - x.1 - x.2.1 - x.2.2) := by
      have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
      rcases hp_odd with ⟨q, hq⟩
      have hev : N - 1 - x.1 * p - x.2.1 * p - x.2.2 * p =
          (M - 1 - x.1 - x.2.1 - x.2.2) + 2 * ((M - s) * q) := by
        have h1 : N = M * (2 * q + 1) := by rw [← hMp, hq]
        have h2 : x.1 * p + x.2.1 * p + x.2.2 * p = s * (2 * q + 1) := by dsimp only [s]; rw [hq]; ring
        have h3 : s ≤ M - 1 := by omega
        have h4 : (M - s) * (2 * q + 1) = (M - s) + 2 * ((M - s) * q) := by ring
        have h5 : M * (2 * q + 1) - s * (2 * q + 1) = (M - s) * (2 * q + 1) := by rw [Nat.sub_mul]
        omega
      rw [hev, pow_add, pow_mul]; norm_num
    -- Helper 3: p^(3*r) ∣ (C(3N - 1, N - 1 - s*p) - C(3M - 1, M - 1 - s)) * B1 * B2 * B3
    have hA0_dvd : (p : ℤ) ^ (3 * r) ∣
        (((3 * N - 1).choose (N - 1 - x.1 * p - x.2.1 * p - x.2.2 * p) : ℤ) -
          ((3 * M - 1).choose (M - 1 - x.1 - x.2.1 - x.2.2) : ℤ)) *
        ((M + x.1 - 1).choose x.1 : ℤ) ^ 2 *
        ((M + x.2.1 - 1).choose x.2.1 : ℤ) ^ 2 *
        ((M + x.2.2 - 1).choose x.2.2 : ℤ) ^ 2 := by
      have hsubN : N - 1 - x.1 * p - x.2.1 * p - x.2.2 * p = (M - s) * p - 1 := by
        have h1 : x.1 * p + x.2.1 * p + x.2.2 * p = s * p := by dsimp only [s]; ring
        have h2 : (M - s) * p = N - s * p := by rw [Nat.sub_mul, hMp]
        have h3 : 1 ≤ (M - s) * p := Nat.mul_pos (by omega) hp.pos
        omega
      have hsubM : M - 1 - x.1 - x.2.1 - x.2.2 = (M - s) - 1 := by dsimp only [s]; omega
      rw [hsubN, hsubM]
      -- Identity: (C(3N - 1, (M - s)*p - 1) - C(3M - 1, M - s - 1)) * (3 * M) =
      --   (C(3M * p, (M - s) * p) - C(3M, M - s)) * (M - s)!
      have hid1 : (3 * N - 1).choose ((M - s) * p - 1) * (3 * M) =
          ((3 * M) * p).choose ((M - s) * p) * (M - s) := by
        have h1 := Nat.add_one_mul_choose_eq (3 * N - 1) ((M - s) * p - 1)
        have e1 : 3 * N - 1 + 1 = 3 * N := by omega
        have e2 : (M - s) * p - 1 + 1 = (M - s) * p := by
          have : 0 < (M - s) * p := Nat.mul_pos (by omega) hp.pos; omega
        rw [e1, e2] at h1
        have h3N : 3 * N = (3 * M) * p := by rw [← hMp]; ring
        have h2 : ((3 * N - 1).choose ((M - s) * p - 1) * (3 * M)) * p =
            (((3 * M) * p).choose ((M - s) * p) * (M - s)) * p := by
          calc ((3 * N - 1).choose ((M - s) * p - 1) * (3 * M)) * p
              = (3 * N) * (3 * N - 1).choose ((M - s) * p - 1) := by rw [h3N]; ring
            _ = (3 * N).choose ((M - s) * p) * ((M - s) * p) := h1
            _ = (((3 * M) * p).choose ((M - s) * p) * (M - s)) * p := by rw [h3N]; ring
        exact Nat.eq_of_mul_eq_mul_right hp.pos h2
      have hid2 : (3 * M - 1).choose (M - s - 1) * (3 * M) = (3 * M).choose (M - s) * (M - s) := by
        have h1 := Nat.add_one_mul_choose_eq (3 * M - 1) (M - s - 1)
        have e1 : 3 * M - 1 + 1 = 3 * M := by omega
        have e2 : M - s - 1 + 1 = M - s := by omega
        rw [e1, e2] at h1; linarith
      have hdiff_mul : (((3 * N - 1).choose ((M - s) * p - 1) : ℤ) -
            ((3 * M - 1).choose (M - s - 1) : ℤ)) * ((3 * M : ℕ) : ℤ) =
          ((((3 * M) * p).choose ((M - s) * p) : ℤ) - ((3 * M).choose (M - s) : ℤ)) * ((M - s : ℕ) : ℤ) := by
        have h1Z : ((3 * N - 1).choose ((M - s) * p - 1) : ℤ) * ((3 * M : ℕ) : ℤ) =
            (((3 * M) * p).choose ((M - s) * p) : ℤ) * ((M - s : ℕ) : ℤ) := by exact_mod_cast hid1
        have h2Z : ((3 * M - 1).choose (M - s - 1) : ℤ) * ((3 * M : ℕ) : ℤ) =
            ((3 * M).choose (M - s) : ℤ) * ((M - s : ℕ) : ℤ) := by exact_mod_cast hid2
        linarith
      have hkaz_s := hkaz p (3 * M) (M - s) hp hp5 (by omega) (by omega)
      have hMs_ne : M - s ≠ 0 := by omega
      have h3M_sub : 3 * M - (M - s) = 2 * M + s := by omega
      rw [h3M_sub] at hkaz_s
      -- Cancel padicValNat p (3 * M)!
      have hdiff_gen : (p : ℤ) ^ (3 + 2 * padicValNat p (M - s) + padicValNat p (2 * M + s) +
            padicValNat p ((3 * M).choose (M - s))) ∣
          (((3 * N - 1).choose ((M - s) * p - 1) : ℤ) - ((3 * M - 1).choose (M - s - 1) : ℤ)) := by
        apply int_dvd_of_mul_dvd_pow hp (by omega : 3 * M ≠ 0)
        rw [hdiff_mul]
        have hMs_dvd : (p : ℤ) ^ (padicValNat p (M - s)) ∣ ((M - s : ℕ) : ℤ) := by
          exact_mod_cast (pow_padicValNat_dvd (p := p) (n := M - s))
        have hprod := mul_dvd_mul hkaz_s hMs_dvd
        rw [← pow_add] at hprod
        exact dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hprod
      by_cases hs0 : s = 0
      · rw [hs0] at hdiff_gen hMs_ne ⊢
        have hv1 : r - 1 ≤ padicValNat p (M - 0) :=
          (padicValNat_dvd_iff_le hMs_ne).mp (by simpa using hM_dvd)
        have hv2 : r - 1 ≤ padicValNat p (2 * M + 0) :=
          (padicValNat_dvd_iff_le (by omega)).mp (by simpa using dvd_mul_of_dvd_right hM_dvd 2)
        have hd0 : (p : ℤ) ^ (3 * r) ∣
            (((3 * N - 1).choose ((M - 0) * p - 1) : ℤ) - ((3 * M - 1).choose (M - 0 - 1) : ℤ)) :=
          dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hdiff_gen
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd0 _) _) _
      set e := min (r - 1) (padicValNat p s)
      have he_r : e ≤ r - 1 := Nat.min_le_left _ _
      have he_s : e ≤ padicValNat p s := Nat.min_le_right _ _
      have hps : p ^ e ∣ s := (padicValNat_dvd_iff_le hs0).mpr he_s
      have hpM : p ^ e ∣ M := dvd_trans (pow_dvd_pow p he_r) hM_dvd
      have hv1 : e ≤ padicValNat p (M - s) :=
        (padicValNat_dvd_iff_le hMs_ne).mp (Nat.dvd_sub hpM hps)
      have hv2 : e ≤ padicValNat p (2 * M + s) :=
        (padicValNat_dvd_iff_le (by omega)).mp (dvd_add (dvd_mul_of_dvd_right hpM 2) hps)
      by_cases her_eq : e = r - 1
      · have hd0 : (p : ℤ) ^ (3 * r) ∣
            (((3 * N - 1).choose ((M - s) * p - 1) : ℤ) - ((3 * M - 1).choose (M - s - 1) : ℤ)) :=
          dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hdiff_gen
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd0 _) _) _
      have hndvd_s : ¬ p ^ (e + 1) ∣ s := fun hdiv => by
        have := (padicValNat_dvd_iff_le hs0).mp hdiv; omega
      have hndvd_Ms : ¬ p ^ (e + 1) ∣ (M - s) := by
        intro hdiv
        have hpM1 : p ^ (e + 1) ∣ M := dvd_trans (pow_dvd_pow p (by omega)) hM_dvd
        have hsub : M - (M - s) = s := by omega
        exact hndvd_s (hsub ▸ Nat.dvd_sub hpM1 hdiv)
      have hvch : r - 1 - e ≤ padicValNat p ((3 * M).choose (M - s)) := by
        have h1 := dvd_choose_of_pow_dvd hp (dvd_mul_of_dvd_right hM_dvd 3) (by omega) (by omega)
          (by omega) he_r (padicValNat_le_of_not_pow_succ_dvd hp hndvd_Ms)
        exact (padicValNat_dvd_iff_le (Nat.choose_pos (by omega)).ne').mp h1
      have hdiff0 : (p : ℤ) ^ (3 + (r - 1) + 2 * e) ∣
          (((3 * N - 1).choose ((M - s) * p - 1) : ℤ) - ((3 * M - 1).choose (M - s - 1) : ℤ)) :=
        dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hdiff_gen
      have hB_dvd : (p : ℤ) ^ (2 * (r - 1 - e)) ∣
          ((M + x.1 - 1).choose x.1 : ℤ) ^ 2 *
          ((M + x.2.1 - 1).choose x.2.1 : ℤ) ^ 2 *
          ((M + x.2.2 - 1).choose x.2.2 : ℤ) ^ 2 := by
        have hch : ∀ k, ¬ p ^ (e + 1) ∣ k → (p : ℤ) ^ (2 * (r - 1 - e)) ∣ ((M + k - 1).choose k : ℤ) ^ 2 := by
          intro k hknd
          have hk_pos : 0 < k := Nat.pos_of_ne_zero (fun h0 => hknd (h0 ▸ dvd_zero _))
          have h1 := dvd_choose_pred_of_pow_dvd hp hM_dvd hM_pos hk_pos he_r
            (padicValNat_le_of_not_pow_succ_dvd hp hknd)
          have h2 : (p : ℤ) ^ (2 * (r - 1 - e)) = ((p : ℤ) ^ (r - 1 - e)) ^ 2 := by rw [← pow_mul, mul_comm]
          rw [h2]; exact pow_dvd_pow_of_dvd (by exact_mod_cast h1) 2
        rcases not_pow_succ_dvd_of_sum_not_dvd hndvd_s with h12 | h3
        · rcases not_pow_succ_dvd_of_sum_not_dvd h12 with h1 | h2
          · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (hch x.1 h1) _) _
          · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hch x.2.1 h2) _) _
        · exact dvd_mul_of_dvd_right (hch x.2.2 h3) _
      have hprod := mul_dvd_mul hdiff0 hB_dvd
      rw [← pow_add] at hprod
      have hassoc : (((3 * N - 1).choose ((M - s) * p - 1) : ℤ) -
            ((3 * M - 1).choose (M - s - 1) : ℤ)) *
          ((M + x.1 - 1).choose x.1 : ℤ) ^ 2 *
          ((M + x.2.1 - 1).choose x.2.1 : ℤ) ^ 2 *
          ((M + x.2.2 - 1).choose x.2.2 : ℤ) ^ 2 =
          (((3 * N - 1).choose ((M - s) * p - 1) : ℤ) -
            ((3 * M - 1).choose (M - s - 1) : ℤ)) *
          (((M + x.1 - 1).choose x.1 : ℤ) ^ 2 *
            ((M + x.2.1 - 1).choose x.2.1 : ℤ) ^ 2 *
            ((M + x.2.2 - 1).choose x.2.2 : ℤ) ^ 2) := by ring
      rw [hassoc]
      exact dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hprod
    -- Telescope g N (x.1*p, x.2.1*p, x.2.2*p) - g M x!
    dsimp only [g]
    rw [hsign_eq]
    set sg : ℤ := (-1 : ℤ) ^ (M - 1 - x.1 - x.2.1 - x.2.2)
    set A0 : ℤ := ((3 * N - 1).choose (N - 1 - x.1 * p - x.2.1 * p - x.2.2 * p) : ℤ)
    set B0 : ℤ := ((3 * M - 1).choose (M - 1 - x.1 - x.2.1 - x.2.2) : ℤ)
    set A1 : ℤ := ((N + x.1 * p - 1).choose (x.1 * p) : ℤ) ^ 2
    set B1 : ℤ := ((M + x.1 - 1).choose x.1 : ℤ) ^ 2
    set A2 : ℤ := ((N + x.2.1 * p - 1).choose (x.2.1 * p) : ℤ) ^ 2
    set B2 : ℤ := ((M + x.2.1 - 1).choose x.2.1 : ℤ) ^ 2
    set A3 : ℤ := ((N + x.2.2 * p - 1).choose (x.2.2 * p) : ℤ) ^ 2
    set B3 : ℤ := ((M + x.2.2 - 1).choose x.2.2 : ℤ) ^ 2
    have htele : sg * A0 * A1 * A2 * A3 - sg * B0 * B1 * B2 * B3 =
        sg * ((A0 - B0) * B1 * B2 * B3 +
              A0 * (A1 - B1) * B2 * B3 +
              A0 * A1 * (A2 - B2) * B3 +
              A0 * A1 * A2 * (A3 - B3)) := by ring
    rw [htele]
    exact dvd_mul_of_dvd_right (dvd_add (dvd_add (dvd_add hA0_dvd
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hsq_dvd x.1) _) _) _))
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hsq_dvd x.2.1) _) _))
      (dvd_mul_of_dvd_right (hsq_dvd x.2.2) _)) _
  -- Piece 1: S1a = S1b = S1c by symmetry, and p^(3*r) ∣ S1a by S2_vanish_dvd!
  have hS1a_dvd : (p : ℤ) ^ (3 * r) ∣
      ∑ x ∈ (Tlt N).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g N x := by
    have hreidx : ∑ x ∈ (Tlt N).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g N x =
        ∑ j' ∈ range M, ∑ l' ∈ range (M - j'),
          ((N + j' * p - 1).choose (j' * p) : ℤ) ^ 2 *
          ((N + l' * p - 1).choose (l' * p) : ℤ) ^ 2 *
          ∑ i ∈ (range (N - (j' + l') * p)).filter (fun i => ¬ p ∣ i),
            ((-1 : ℤ) ^ (N - 1 - (j' + l') * p - i) *
              ((3 * N - 1).choose (N - 1 - (j' + l') * p - i) : ℤ) *
              ((N + i - 1).choose i : ℤ) ^ 2) := by
      have hflat : ∑ j' ∈ range M, ∑ l' ∈ range (M - j'),
            ((N + j' * p - 1).choose (j' * p) : ℤ) ^ 2 *
            ((N + l' * p - 1).choose (l' * p) : ℤ) ^ 2 *
            ∑ i ∈ (range (N - (j' + l') * p)).filter (fun i => ¬ p ∣ i),
              ((-1 : ℤ) ^ (N - 1 - (j' + l') * p - i) *
                ((3 * N - 1).choose (N - 1 - (j' + l') * p - i) : ℤ) *
                ((N + i - 1).choose i : ℤ) ^ 2) =
          ∑ x ∈ (range N ×ˢ (range M ×ˢ range M)).filter
              (fun x => ¬ p ∣ x.1 ∧ x.1 + (x.2.1 + x.2.2) * p < N),
            g N (x.1, x.2.1 * p, x.2.2 * p) := by
        rw [sum_filter, sum_product, sum_comm]
        have hswap : ∑ y ∈ range M ×ˢ range M, ∑ i ∈ range N,
              (if ¬ p ∣ i ∧ i + (y.1 + y.2) * p < N then g N (i, y.1 * p, y.2 * p) else 0) =
            ∑ j' ∈ range M, ∑ l' ∈ range M, ∑ i ∈ range N,
              (if ¬ p ∣ i ∧ i + (j' + l') * p < N then g N (i, j' * p, l' * p) else 0) := by
          rw [sum_product]
        rw [hswap]
        apply sum_congr rfl; intro j' hj'
        have hj'M : j' < M := mem_range.mp hj'
        have hinner : ∀ l' ∈ range M,
            (∑ i ∈ range N,
              if ¬ p ∣ i ∧ i + (j' + l') * p < N then g N (i, j' * p, l' * p) else 0) =
            if l' ∈ range (M - j') then
              ((N + j' * p - 1).choose (j' * p) : ℤ) ^ 2 *
              ((N + l' * p - 1).choose (l' * p) : ℤ) ^ 2 *
              ∑ i ∈ (range (N - (j' + l') * p)).filter (fun i => ¬ p ∣ i),
                ((-1 : ℤ) ^ (N - 1 - (j' + l') * p - i) *
                  ((3 * N - 1).choose (N - 1 - (j' + l') * p - i) : ℤ) *
                  ((N + i - 1).choose i : ℤ) ^ 2)
            else 0 := by
          intro l' _
          by_cases hl' : l' ∈ range (M - j')
          · rw [if_pos hl', mul_sum, sum_filter]
            have hl'M : j' + l' < M := by simp only [mem_range] at hl'; omega
            have hjp_lt : (j' + l') * p < N := by rw [← hMp]; exact Nat.mul_lt_mul_of_pos_right hl'M hp.pos
            rw [← sum_subset (range_mono (by omega : N - (j' + l') * p ≤ N))]
            · apply sum_congr rfl; intro i hi
              have hi' : i + (j' + l') * p < N := by simp only [mem_range] at hi; omega
              by_cases hind : ¬ p ∣ i
              · rw [if_pos ⟨hind, hi'⟩, if_pos hind]
                dsimp only [g]
                have hsub : N - 1 - i - j' * p - l' * p = N - 1 - (j' + l') * p - i := by
                  have : (j' + l') * p = j' * p + l' * p := by ring
                  omega
                rw [hsub]; ring
              · rw [if_neg (by tauto), if_neg hind]
            · intro i _ hi_not
              have hgt : ¬ (i + (j' + l') * p < N) := by simp only [mem_range] at hi_not; omega
              rw [if_neg (by tauto)]
          · rw [if_neg hl']
            apply sum_eq_zero; intro i _
            have hl'ge : M ≤ j' + l' := by simp only [mem_range] at hl'; omega
            have hge : N ≤ (j' + l') * p := by rw [← hMp]; exact Nat.mul_le_mul_right p hl'ge
            rw [if_neg (by omega)]
        rw [sum_congr rfl hinner, sum_ite_mem, inter_eq_right.mpr (range_mono (by omega : M - j' ≤ M))]
      rw [hflat]
      symm
      refine Finset.sum_bij (fun x _ => (x.1, x.2.1 * p, x.2.2 * p)) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [mem_filter, Tlt, mem_product, mem_range] at hx ⊢
        have h1 : x.2.1 * p < N := by rw [← hMp]; exact Nat.mul_lt_mul_of_pos_right hx.1.2.1 hp.pos
        have h2 : x.2.2 * p < N := by rw [← hMp]; exact Nat.mul_lt_mul_of_pos_right hx.1.2.2 hp.pos
        have hsum : x.1 + x.2.1 * p + x.2.2 * p < N := by linarith [hx.2.2]
        exact ⟨⟨⟨hx.1.1, h1, h2⟩, hsum⟩, hx.2.1, dvd_mul_left p _, dvd_mul_left p _⟩
      · intro x₁ _ x₂ _ h
        rcases x₁ with ⟨a₁, b₁, c₁⟩; rcases x₂ with ⟨a₂, b₂, c₂⟩
        simp only [Prod.mk.injEq] at h ⊢
        exact ⟨h.1, Nat.eq_of_mul_eq_mul_right hp.pos h.2.1, Nat.eq_of_mul_eq_mul_right hp.pos h.2.2⟩
      · intro y hy
        simp only [mem_filter, Tlt, mem_product, mem_range] at hy
        rcases hy.2.2.1 with ⟨b, hb'⟩
        rcases hy.2.2.2 with ⟨c, hc'⟩
        have hbc_p : (b + c) * p < M * p := by linarith [hy.1.2, hMp]
        have hbc : b + c < M := Nat.lt_of_mul_lt_mul_right hbc_p
        refine ⟨(y.1, b, c), ?_, by ext <;> dsimp only <;> linarith⟩
        simp only [mem_filter, mem_product, mem_range]
        exact ⟨⟨hy.1.1.1, by omega, by omega⟩, hy.2.1, by linarith [hy.1.2]⟩
      · intro _ _; rfl
    rw [hreidx]
    apply Finset.dvd_sum; intro j' hj'
    apply Finset.dvd_sum; intro l' hl'
    have hjlM : j' + l' < M := by simp only [mem_range] at hj' hl'; omega
    set m := j' + l'
    by_cases hm0 : m = 0
    · have hS := hS2 p r r n m hp hp5 hr hr le_rfl (by rw [hm0]; exact dvd_zero _) hjlM
      have h3r : 2 * r + r = 3 * r := by omega
      rw [h3r] at hS
      exact dvd_mul_of_dvd_right hS _
    set e := min (r - 1) (padicValNat p m)
    have he_r : e ≤ r - 1 := Nat.min_le_left _ _
    have he_m : e ≤ padicValNat p m := Nat.min_le_right _ _
    have hS := hS2 p r (e + 1) n m hp hp5 hr (by omega) (by omega)
      (by simpa using (padicValNat_dvd_iff_le hm0).mpr he_m) hjlM
    by_cases her_eq : e = r - 1
    · have h3r : 2 * r + (e + 1) = 3 * r := by omega
      rw [h3r] at hS
      exact dvd_mul_of_dvd_right hS _
    have hndvd_m : ¬ p ^ (e + 1) ∣ m := fun hdiv => by
      have := (padicValNat_dvd_iff_le hm0).mp hdiv; omega
    have hpre_dvd : (p : ℤ) ^ (2 * (r - 1 - e)) ∣
        ((N + j' * p - 1).choose (j' * p) : ℤ) ^ 2 *
        ((N + l' * p - 1).choose (l' * p) : ℤ) ^ 2 := by
      have hch : ∀ k, ¬ p ^ (e + 1) ∣ k →
          (p : ℤ) ^ (2 * (r - 1 - e)) ∣ ((N + k * p - 1).choose (k * p) : ℤ) ^ 2 := by
        intro k hknd
        have hk_pos : 0 < k := Nat.pos_of_ne_zero (fun h0 => hknd (h0 ▸ dvd_zero _))
        have hvk := padicValNat_le_of_not_pow_succ_dvd hp hknd
        have hvkp : padicValNat p (k * p) ≤ e + 1 := by
          rw [padicValNat.mul hk_pos.ne' hp.ne_zero, padicValNat.self hp.one_lt]; omega
        have h1 := dvd_choose_pred_of_pow_dvd hp hN_dvd hN_pos (Nat.mul_pos hk_pos hp.pos)
          (by omega : e + 1 ≤ r) hvkp
        have hsub : r - (e + 1) = r - 1 - e := by omega
        rw [hsub] at h1
        have h2 : (p : ℤ) ^ (2 * (r - 1 - e)) = ((p : ℤ) ^ (r - 1 - e)) ^ 2 := by rw [← pow_mul, mul_comm]
        rw [h2]; exact pow_dvd_pow_of_dvd (by exact_mod_cast h1) 2
      rcases not_pow_succ_dvd_of_sum_not_dvd hndvd_m with hj_nd | hl_nd
      · exact dvd_mul_of_dvd_left (hch j' hj_nd) _
      · exact dvd_mul_of_dvd_right (hch l' hl_nd) _
    have hprod := mul_dvd_mul hpre_dvd hS
    rw [← pow_add] at hprod
    exact dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hprod
  have hS1b_eq : ∑ x ∈ (Tlt N).filter (fun x => p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ p ∣ x.2.2), g N x =
      ∑ x ∈ (Tlt N).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g N x := by
    apply Tlt_swap12_sum N _ _ (g N) (fun x => by dsimp only; tauto)
    intro x; dsimp only [g]
    have hsub : N - 1 - x.1 - x.2.1 - x.2.2 = N - 1 - x.2.1 - x.1 - x.2.2 := by omega
    rw [hsub]; ring
  have hS1c_eq : ∑ x ∈ (Tlt N).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2), g N x =
      ∑ x ∈ (Tlt N).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g N x := by
    apply Tlt_swap13_sum N _ _ (g N) (fun x => by dsimp only; tauto)
    intro x; dsimp only [g]
    have hsub : N - 1 - x.1 - x.2.1 - x.2.2 = N - 1 - x.2.2 - x.2.1 - x.1 := by omega
    rw [hsub]; ring
  -- Piece 23: at least two of i, j, l not divisible by p -> p^(4*r) ∣ g N x term-by-term!
  have hS23_dvd : (p : ℤ) ^ (3 * r) ∣
      ∑ x ∈ (Tlt N).filter (fun x =>
        (¬ p ∣ x.1 ∧ ¬ p ∣ x.2.1) ∨ (¬ p ∣ x.1 ∧ ¬ p ∣ x.2.2) ∨ (¬ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2)), g N x := by
    apply Finset.dvd_sum; intro x hx
    have hch_nd : ∀ k, ¬ p ∣ k → (p : ℤ) ^ (2 * r) ∣ ((N + k - 1).choose k : ℤ) ^ 2 := by
      intro k hknd
      have hk_pos : 0 < k := Nat.pos_of_ne_zero (fun h0 => hknd (h0 ▸ dvd_zero _))
      have h1 := dvd_choose_pred_of_pow_dvd hp hN_dvd hN_pos hk_pos (Nat.zero_le r)
        (by rw [padicValNat_eq_zero_of_not_dvd hknd])
      rw [Nat.sub_zero] at h1
      have h2 : (p : ℤ) ^ (2 * r) = ((p : ℤ) ^ r) ^ 2 := by rw [← pow_mul, mul_comm]
      rw [h2]; exact pow_dvd_pow_of_dvd (by exact_mod_cast h1) 2
    have h4r_3r : (p : ℤ) ^ (3 * r) ∣ (p : ℤ) ^ (2 * r + 2 * r) := pow_dvd_pow (p : ℤ) (by omega)
    dsimp only [g]
    rcases (mem_filter.mp hx).2 with ⟨h1, h2⟩ | ⟨h1, h3⟩ | ⟨h2, h3⟩
    · have hm := mul_dvd_mul (hch_nd x.1 h1) (hch_nd x.2.1 h2)
      rw [← pow_add] at hm
      have hrew : (-1 : ℤ) ^ (N - 1 - x.1 - x.2.1 - x.2.2) *
            ((3 * N - 1).choose (N - 1 - x.1 - x.2.1 - x.2.2) : ℤ) *
            ((N + x.1 - 1).choose x.1 : ℤ) ^ 2 *
            ((N + x.2.1 - 1).choose x.2.1 : ℤ) ^ 2 *
            ((N + x.2.2 - 1).choose x.2.2 : ℤ) ^ 2 =
          (((N + x.1 - 1).choose x.1 : ℤ) ^ 2 * ((N + x.2.1 - 1).choose x.2.1 : ℤ) ^ 2) *
            ((-1 : ℤ) ^ (N - 1 - x.1 - x.2.1 - x.2.2) *
              ((3 * N - 1).choose (N - 1 - x.1 - x.2.1 - x.2.2) : ℤ) *
              ((N + x.2.2 - 1).choose x.2.2 : ℤ) ^ 2) := by ring
      rw [hrew]; exact dvd_mul_of_dvd_left (dvd_trans h4r_3r hm) _
    · have hm := mul_dvd_mul (hch_nd x.1 h1) (hch_nd x.2.2 h3)
      rw [← pow_add] at hm
      have hrew : (-1 : ℤ) ^ (N - 1 - x.1 - x.2.1 - x.2.2) *
            ((3 * N - 1).choose (N - 1 - x.1 - x.2.1 - x.2.2) : ℤ) *
            ((N + x.1 - 1).choose x.1 : ℤ) ^ 2 *
            ((N + x.2.1 - 1).choose x.2.1 : ℤ) ^ 2 *
            ((N + x.2.2 - 1).choose x.2.2 : ℤ) ^ 2 =
          (((N + x.1 - 1).choose x.1 : ℤ) ^ 2 * ((N + x.2.2 - 1).choose x.2.2 : ℤ) ^ 2) *
            ((-1 : ℤ) ^ (N - 1 - x.1 - x.2.1 - x.2.2) *
              ((3 * N - 1).choose (N - 1 - x.1 - x.2.1 - x.2.2) : ℤ) *
              ((N + x.2.1 - 1).choose x.2.1 : ℤ) ^ 2) := by ring
      rw [hrew]; exact dvd_mul_of_dvd_left (dvd_trans h4r_3r hm) _
    · have hm := mul_dvd_mul (hch_nd x.2.1 h2) (hch_nd x.2.2 h3)
      rw [← pow_add] at hm
      have hrew : (-1 : ℤ) ^ (N - 1 - x.1 - x.2.1 - x.2.2) *
            ((3 * N - 1).choose (N - 1 - x.1 - x.2.1 - x.2.2) : ℤ) *
            ((N + x.1 - 1).choose x.1 : ℤ) ^ 2 *
            ((N + x.2.1 - 1).choose x.2.1 : ℤ) ^ 2 *
            ((N + x.2.2 - 1).choose x.2.2 : ℤ) ^ 2 =
          (((N + x.2.1 - 1).choose x.2.1 : ℤ) ^ 2 * ((N + x.2.2 - 1).choose x.2.2 : ℤ) ^ 2) *
            ((-1 : ℤ) ^ (N - 1 - x.1 - x.2.1 - x.2.2) *
              ((3 * N - 1).choose (N - 1 - x.1 - x.2.1 - x.2.2) : ℤ) *
              ((N + x.1 - 1).choose x.1 : ℤ) ^ 2) := by ring
      rw [hrew]; exact dvd_mul_of_dvd_left (dvd_trans h4r_3r hm) _
  -- Combine all 5 pieces!
  rw [hS1b_eq, hS1c_eq]
  have hcomb :
      (∑ x ∈ (Tlt N).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g N x) +
        (∑ x ∈ (Tlt N).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g N x) +
        (∑ x ∈ (Tlt N).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g N x) +
        (∑ x ∈ (Tlt N).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g N x) +
        (∑ x ∈ (Tlt N).filter (fun x =>
          (¬ p ∣ x.1 ∧ ¬ p ∣ x.2.1) ∨ (¬ p ∣ x.1 ∧ ¬ p ∣ x.2.2) ∨ (¬ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2)), g N x) -
      ∑ x ∈ Tlt M, g M x =
      ((∑ x ∈ (Tlt N).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g N x) -
        ∑ x ∈ Tlt M, g M x) +
      3 * (∑ x ∈ (Tlt N).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g N x) +
      (∑ x ∈ (Tlt N).filter (fun x =>
        (¬ p ∣ x.1 ∧ ¬ p ∣ x.2.1) ∨ (¬ p ∣ x.1 ∧ ¬ p ∣ x.2.2) ∨ (¬ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2)), g N x) := by
    ring
  rw [hcomb]
  exact dvd_add (dvd_add hS0_dvd (dvd_mul_of_dvd_right hS1a_dvd 3)) hS23_dvd

-- ============================================================================
-- Section 5: Parts 3 & 4 Glue — prime-level mod p^5 congruences (p ≥ 7)
-- ============================================================================

lemma part34_glue (a_fn : ℕ → ℕ) (H1 : ℕ → ℚ)
    (ha : ∀ N : ℕ, a_fn N = ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1 - i), ∑ l ∈ range (N + 1 - i - j),
      (4 * N - i - j - l).choose (3 * N) *
        (N.choose i) ^ 2 * (N.choose j) ^ 2 * (N.choose l) ^ 2)
    (hapred : ∀ N : ℕ, 0 < N → (a_fn (N - 1) : ℤ) =
      ∑ i ∈ range N, ∑ j ∈ range (N - i), ∑ l ∈ range (N - i - j),
        (-1 : ℤ) ^ (N - 1 - i - j - l) *
          ((3 * N - 1).choose (N - 1 - i - j - l) : ℤ) *
          ((N + i - 1).choose i : ℤ) ^ 2 *
          ((N + j - 1).choose j : ℤ) ^ 2 *
          ((N + l - 1).choose l : ℤ) ^ 2)
    (hH1 : ∀ p : ℕ, p.Prime → 7 ≤ p → pDiv p 2 (H1 p))
    (hCkp : ∀ p k : ℕ, p.Prime → 7 ≤ p → 1 ≤ k →
      pDiv p 5 (((k * p - 1).choose (p - 1) : ℚ) -
        (1 + ((k * (k - 1) : ℕ) : ℚ) * (p : ℚ) * H1 p)))
    (hCkp_eq : ∀ p k : ℕ, 1 ≤ p → 1 ≤ k →
      ((k * p).choose p : ℚ) = (k : ℚ) * ((k * p - 1).choose (p - 1) : ℚ))
    (ht1 : ∀ p : ℕ, p.Prime → 7 ≤ p →
      pDiv p 5 (3 * (∑ i ∈ Ico 1 p, (((4 * p - i).choose (3 * p) : ℚ) * ((p.choose i : ℚ) ^ 2))) +
        15 * (p : ℚ) * H1 p))
    (hs1 : ∀ p : ℕ, p.Prime → 7 ≤ p →
      pDiv p 5 (3 * (∑ i ∈ Ico 1 p, ((-1 : ℚ) ^ (p - 1 - i) *
        ((3 * p - 1).choose (p - 1 - i) : ℚ) * (((p + i - 1).choose i : ℚ) ^ 2))) -
        3 * (p : ℚ) * H1 p))
    (ht2 : ∀ p : ℕ, p.Prime → 7 ≤ p →
      pDiv p 5 (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
        if i + j ≤ p then (((4 * p - i - j).choose (3 * p) : ℚ) *
          ((p.choose i : ℚ) ^ 2) * ((p.choose j : ℚ) ^ 2)) else 0))
    (hs2 : ∀ p : ℕ, p.Prime → 7 ≤ p →
      pDiv p 5 (∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
        if i + j < p then ((-1 : ℚ) ^ (p - 1 - i - j) * ((3 * p - 1).choose (p - 1 - i - j) : ℚ) *
          (((p + i - 1).choose i : ℚ) ^ 2) * (((p + j - 1).choose j : ℚ) ^ 2)) else 0))
    (hPow : ∀ {p a_p a_pm1 : ℕ} {x : ℚ}, p.Prime → pDiv p 3 x →
      pDiv p 5 ((a_p : ℚ) - (7 + 33 * x)) →
      pDiv p 5 ((a_pm1 : ℚ) - (1 + 9 * x)) →
      Nat.ModEq (p ^ 5) (3 * a_p) (10 + 11 * a_pm1) ∧
      Nat.ModEq (p ^ 5) (a_p ^ 21) (7 ^ 21 * a_pm1 ^ 11))
    (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    Nat.ModEq (p ^ 5) (3 * a_fn p) (10 + 11 * a_fn (p - 1)) ∧
    Nat.ModEq (p ^ 5) (a_fn p ^ 21) (7 ^ 21 * a_fn (p - 1) ^ 11) := by
  have hp_pos : 0 < p := hp.pos
  have hx : pDiv p 3 ((p : ℚ) * H1 p) := pDiv_mul hp (pDiv_p_one p hp) (hH1 p hp hp7)
  -- Step A: pDiv p 5 ((a_fn p : ℚ) - (7 + 33 * ((p : ℚ) * H1 p)))
  have hap : pDiv p 5 ((a_fn p : ℚ) - (7 + 33 * ((p : ℚ) * H1 p))) := by
    let f : ℕ × ℕ × ℕ → ℚ := fun x =>
      ((4 * p - x.1 - x.2.1 - x.2.2).choose (3 * p) : ℚ) *
        ((p.choose x.1 : ℚ) ^ 2) * ((p.choose x.2.1 : ℚ) ^ 2) * ((p.choose x.2.2 : ℚ) ^ 2)
    have haQ : (a_fn p : ℚ) = ∑ x ∈ Tle p, f x := by
      rw [ha p, triple_sum_le_eq_flat]; push_cast; rfl
    rw [haQ, sum_partition_p_fine p (Tle p) f]
    -- t0: only (0,0,0), (p,0,0), (0,p,0), (0,0,p)!
    have hT0_eq : (Tle p).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2) =
        {(0, 0, 0), (p, 0, 0), (0, p, 0), (0, 0, p)} := by
      ext ⟨a, b, c⟩
      simp only [mem_filter, Tle, mem_product, mem_range, mem_insert, mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨ha', hb', hc'⟩, hsum⟩, hda, hdb, hdc⟩
        have hcase : ∀ m, m ≤ p → p ∣ m → m = 0 ∨ m = p := fun m hmp hdm => by
          rcases hdm with ⟨q, rfl⟩
          rcases q with _ | _ | q
          · left; ring
          · right; ring
          · exfalso; nlinarith
        rcases hcase a (by omega) hda with rfl | rfl
        · rcases hcase b (by omega) hdb with rfl | rfl
          · rcases hcase c (by omega) hdc with rfl | rfl
            · left; exact ⟨rfl, rfl, rfl⟩
            · right; right; right; exact ⟨rfl, rfl, rfl⟩
          · have hc0 : c = 0 := by omega
            subst hc0; right; right; left; exact ⟨rfl, rfl, rfl⟩
        · have hb0 : b = 0 := by omega
          have hc0 : c = 0 := by omega
          subst hb0; subst hc0; right; left; exact ⟨rfl, rfl, rfl⟩
      · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;>
          exact ⟨⟨⟨by omega, by omega, by omega⟩, by omega⟩, by simp, by simp, by simp⟩
    have ht0_val : ∑ x ∈ (Tle p).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), f x =
        ((4 * p).choose p : ℚ) + 3 := by
      rw [hT0_eq]
      have hne1 : (0, 0, 0) ∉ ({(p, 0, 0), (0, p, 0), (0, 0, p)} : Finset (ℕ × ℕ × ℕ)) := by simp; omega
      have hne2 : (p, 0, 0) ∉ ({(0, p, 0), (0, 0, p)} : Finset (ℕ × ℕ × ℕ)) := by simp; omega
      have hne3 : (0, p, 0) ∉ ({(0, 0, p)} : Finset (ℕ × ℕ × ℕ)) := by simp; omega
      rw [sum_insert hne1, sum_insert hne2, sum_insert hne3, sum_singleton]
      have h4p : (4 * p).choose (3 * p) = (4 * p).choose p := by
        rw [← Nat.choose_symm (by omega : 3 * p ≤ 4 * p)]
        have : 4 * p - 3 * p = p := by omega
        rw [this]
      have h3p : 4 * p - p = 3 * p := by omega
      have hf0 : f (0, 0, 0) = ((4 * p).choose p : ℚ) := by
        dsimp only [f]; simp only [Nat.sub_zero]; rw [h4p, Nat.choose_zero_right]; push_cast; ring
      have hf1 : f (p, 0, 0) = 1 := by
        dsimp only [f]; simp only [Nat.sub_zero]; rw [h3p, Nat.choose_self, Nat.choose_self, Nat.choose_zero_right]; push_cast; ring
      have hf2 : f (0, p, 0) = 1 := by
        dsimp only [f]; simp only [Nat.sub_zero]; rw [h3p, Nat.choose_self, Nat.choose_self, Nat.choose_zero_right]; push_cast; ring
      have hf3 : f (0, 0, p) = 1 := by
        dsimp only [f]; simp only [Nat.sub_zero]; rw [h3p, Nat.choose_self, Nat.choose_self, Nat.choose_zero_right]; push_cast; ring
      rw [hf0, hf1, hf2, hf3]; ring
    have ht0_pDiv : pDiv p 5 ((∑ x ∈ (Tle p).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), f x) -
        (7 + 48 * (p : ℚ) * H1 p)) := by
      rw [ht0_val, hCkp_eq p 4 hp.one_le (by norm_num)]
      have h4 := hCkp p 4 hp hp7 (by norm_num)
      have hrew : (4 : ℚ) * ((4 * p - 1).choose (p - 1) : ℚ) + 3 - (7 + 48 * (p : ℚ) * H1 p) =
          (4 : ℚ) * (((4 * p - 1).choose (p - 1) : ℚ) -
            (1 + ((4 * (4 - 1) : ℕ) : ℚ) * (p : ℚ) * H1 p)) := by norm_num; ring
      push_cast; rw [hrew]; simpa using pDiv_mul hp (pDiv_nat_zero hp 4) h4
    -- t1: 3 equal sums, each matching ∑ i ∈ Ico 1 p, C(4p - i, 3p) * C(p, i)^2!
    have ht1a_eq : ∑ x ∈ (Tle p).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), f x =
        ∑ i ∈ Ico 1 p, (((4 * p - i).choose (3 * p) : ℚ) * ((p.choose i : ℚ) ^ 2)) := by
      symm
      refine Finset.sum_bij (fun i _ => (i, 0, 0)) ?_ ?_ ?_ ?_
      · intro i hi
        have hi1 := (mem_Ico.mp hi).1; have hi2 := (mem_Ico.mp hi).2
        simp only [mem_filter, Tle, mem_product, mem_range]
        exact ⟨⟨⟨by omega, by omega, by omega⟩, by omega⟩,
               fun h => by have := Nat.le_of_dvd (by omega) h; omega, dvd_zero p, dvd_zero p⟩
      · intro i₁ _ i₂ _ h; exact congrArg Prod.fst h
      · intro ⟨a, b, c⟩ hy
        simp only [mem_filter, Tle, mem_product, mem_range] at hy
        have ha1 : 1 ≤ a := Nat.pos_of_ne_zero (fun h0 => hy.2.1 (h0 ▸ dvd_zero p))
        have ha2 : a < p := by
          by_contra hge
          have : a = p := by omega
          exact hy.2.1 (this ▸ dvd_refl p)
        have hb0 : b = 0 := by
          rcases hy.2.2.1 with ⟨q, rfl⟩
          rcases q with _ | q
          · ring
          · exfalso; nlinarith
        have hc0 : c = 0 := by
          rcases hy.2.2.2 with ⟨q, rfl⟩
          rcases q with _ | q
          · ring
          · exfalso; nlinarith
        exact ⟨a, mem_Ico.mpr ⟨ha1, ha2⟩, by ext <;> dsimp only <;> omega⟩
      · intro i _; dsimp only [f]; simp
    have ht1b_eq : ∑ x ∈ (Tle p).filter (fun x => p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ p ∣ x.2.2), f x =
        ∑ x ∈ (Tle p).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), f x := by
      apply Tle_swap12_sum p _ _ f (fun x => by dsimp only; tauto)
      intro x; dsimp only [f]
      have : 4 * p - x.1 - x.2.1 - x.2.2 = 4 * p - x.2.1 - x.1 - x.2.2 := by omega
      rw [this]; ring
    have ht1c_eq : ∑ x ∈ (Tle p).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2), f x =
        ∑ x ∈ (Tle p).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), f x := by
      apply Tle_swap13_sum p _ _ f (fun x => by dsimp only; tauto)
      intro x; dsimp only [f]
      have : 4 * p - x.1 - x.2.1 - x.2.2 = 4 * p - x.2.2 - x.2.1 - x.1 := by omega
      rw [this]; ring
    -- t2: 3 equal sums, each matching ht2!
    have ht2a_eq : ∑ x ∈ (Tle p).filter (fun x => ¬ p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ p ∣ x.2.2), f x =
        ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
          if i + j ≤ p then (((4 * p - i - j).choose (3 * p) : ℚ) *
            ((p.choose i : ℚ) ^ 2) * ((p.choose j : ℚ) ^ 2)) else 0 := by
      rw [← sum_product', ← sum_filter]
      symm
      refine Finset.sum_bij (fun y _ => (y.1, y.2, 0)) ?_ ?_ ?_ ?_
      · intro ⟨i, j⟩ hy
        simp only [mem_filter, mem_product, mem_Ico, Tle, mem_range] at hy ⊢
        refine ⟨⟨⟨by omega, by omega, by omega⟩, by omega⟩, ?_, ?_, dvd_zero p⟩
        · intro h; have := Nat.le_of_dvd (by omega) h; omega
        · intro h; have := Nat.le_of_dvd (by omega) h; omega
      · intro y₁ _ y₂ _ h
        rcases y₁ with ⟨a₁, b₁⟩; rcases y₂ with ⟨a₂, b₂⟩
        simp only [Prod.mk.injEq] at h ⊢; exact ⟨h.1, h.2.1⟩
      · intro ⟨a, b, c⟩ hy
        simp only [mem_filter, Tle, mem_product, mem_range] at hy
        have ha1 : 1 ≤ a := Nat.pos_of_ne_zero (fun h0 => hy.2.1 (h0 ▸ dvd_zero p))
        have hb1 : 1 ≤ b := Nat.pos_of_ne_zero (fun h0 => hy.2.2.1 (h0 ▸ dvd_zero p))
        have ha2 : a < p := by by_contra h; exact hy.2.1 ((by omega : a = p) ▸ dvd_refl p)
        have hb2 : b < p := by by_contra h; exact hy.2.2.1 ((by omega : b = p) ▸ dvd_refl p)
        have hc0 : c = 0 := by
          rcases hy.2.2.2 with ⟨q, rfl⟩
          rcases q with _ | q
          · ring
          · exfalso; nlinarith
        refine ⟨(a, b), ?_, by ext <;> dsimp only <;> omega⟩
        simp only [mem_filter, mem_product, mem_Ico]
        exact ⟨⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩, by omega⟩
      · intro ⟨i, j⟩ _; dsimp only [f]; simp
    have ht2b_eq : ∑ x ∈ (Tle p).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2), f x =
        ∑ x ∈ (Tle p).filter (fun x => ¬ p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ p ∣ x.2.2), f x := by
      -- swap coordinates 2 and 3
      refine Finset.sum_bij (fun x _ => (x.1, x.2.2, x.2.1)) ?_ ?_ ?_ ?_
      · intro x hx; simp only [mem_filter, Tle, mem_product, mem_range] at hx ⊢
        exact ⟨⟨⟨hx.1.1.1, hx.1.1.2.2, hx.1.1.2.1⟩, by omega⟩, hx.2.1, hx.2.2.2, hx.2.2.1⟩
      · intro x₁ _ x₂ _ h
        rcases x₁ with ⟨a₁, b₁, c₁⟩; rcases x₂ with ⟨a₂, b₂, c₂⟩
        simp only [Prod.mk.injEq] at h ⊢; exact ⟨h.1, h.2.2, h.2.1⟩
      · intro y hy; refine ⟨(y.1, y.2.2, y.2.1), ?_, by rcases y with ⟨a, b, c⟩; rfl⟩
        simp only [mem_filter, Tle, mem_product, mem_range] at hy ⊢
        exact ⟨⟨⟨hy.1.1.1, hy.1.1.2.2, hy.1.1.2.1⟩, by omega⟩, hy.2.1, hy.2.2.2, hy.2.2.1⟩
      · intro x _; dsimp only [f]
        have : 4 * p - x.1 - x.2.1 - x.2.2 = 4 * p - x.1 - x.2.2 - x.2.1 := by omega
        rw [this]; ring
    have ht2c_eq : ∑ x ∈ (Tle p).filter (fun x => p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2), f x =
        ∑ x ∈ (Tle p).filter (fun x => ¬ p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ p ∣ x.2.2), f x := by
      apply Tle_swap13_sum p _ _ f (fun x => by dsimp only; tauto)
      intro x; dsimp only [f]
      have : 4 * p - x.1 - x.2.1 - x.2.2 = 4 * p - x.2.2 - x.2.1 - x.1 := by omega
      rw [this]; ring
    -- t3: each term has p^6 ∣ C(p, i)^2 * C(p, j)^2 * C(p, l)^2!
    have ht3_pDiv : pDiv p 5 (∑ x ∈ (Tle p).filter (fun x => ¬ p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2), f x) := by
      apply pDiv_sum hp; intro x hx
      have hx_le : x.1 + x.2.1 + x.2.2 ≤ p := (mem_filter.mp (mem_filter.mp hx).1).2
      have hnd := (mem_filter.mp hx).2
      have hch_p : ∀ k, k ≤ p → ¬ p ∣ k → (p : ℤ) ^ 2 ∣ ((p.choose k : ℤ) ^ 2) := fun k hk hndk => by
        have hk_pos : 0 < k := Nat.pos_of_ne_zero (fun h0 => hndk (h0 ▸ dvd_zero p))
        have h1 := dvd_choose_of_pow_dvd hp (by simp : p ^ 1 ∣ p) hp_pos hk_pos hk (Nat.zero_le 1)
          (by rw [padicValNat_eq_zero_of_not_dvd hndk])
        simp only [Nat.sub_zero, pow_one] at h1
        exact pow_dvd_pow_of_dvd (by exact_mod_cast h1) 2
      have h6 : (p : ℤ) ^ 6 ∣
          ((4 * p - x.1 - x.2.1 - x.2.2).choose (3 * p) : ℤ) *
            ((p.choose x.1 : ℤ) ^ 2) * ((p.choose x.2.1 : ℤ) ^ 2) * ((p.choose x.2.2 : ℤ) ^ 2) := by
        have hm := mul_dvd_mul (mul_dvd_mul (hch_p x.1 (by omega) hnd.1) (hch_p x.2.1 (by omega) hnd.2.1))
          (hch_p x.2.2 (by omega) hnd.2.2)
        have hrew : ((4 * p - x.1 - x.2.1 - x.2.2).choose (3 * p) : ℤ) *
              ((p.choose x.1 : ℤ) ^ 2) * ((p.choose x.2.1 : ℤ) ^ 2) * ((p.choose x.2.2 : ℤ) ^ 2) =
            (((p.choose x.1 : ℤ) ^ 2) * ((p.choose x.2.1 : ℤ) ^ 2) * ((p.choose x.2.2 : ℤ) ^ 2)) *
              ((4 * p - x.1 - x.2.1 - x.2.2).choose (3 * p) : ℤ) := by ring
        rw [hrew]; exact dvd_mul_of_dvd_left (by simpa [← pow_add] using hm) _
      have h5 := pDiv_of_dvd_int hp (dvd_trans (pow_dvd_pow (p : ℤ) (by norm_num : 5 ≤ 6)) h6)
      dsimp only [f]; push_cast at h5; exact h5
    -- Combine t0 + 3*t1 + 3*t2 + t3 - (7 + 33 * p * H1)!
    rw [ht1b_eq, ht1c_eq, ht1a_eq, ht2b_eq, ht2c_eq, ht2a_eq]
    set S0 := ∑ x ∈ (Tle p).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), f x
    set S1 := ∑ i ∈ Ico 1 p, (((4 * p - i).choose (3 * p) : ℚ) * ((p.choose i : ℚ) ^ 2))
    set S2 := ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
      if i + j ≤ p then (((4 * p - i - j).choose (3 * p) : ℚ) *
        ((p.choose i : ℚ) ^ 2) * ((p.choose j : ℚ) ^ 2)) else 0
    set S3 := ∑ x ∈ (Tle p).filter (fun x => ¬ p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2), f x
    have hrew : S0 + (S1 + S1 + S1) + (S2 + S2 + S2) + S3 - (7 + 33 * ((p : ℚ) * H1 p)) =
        (S0 - (7 + 48 * (p : ℚ) * H1 p)) +
        (3 * S1 + 15 * (p : ℚ) * H1 p) +
        3 * S2 + S3 := by ring
    rw [hrew]
    exact pDiv_add hp (pDiv_add hp (pDiv_add hp ht0_pDiv (ht1 p hp hp7))
      (by simpa using pDiv_mul hp (pDiv_nat_zero hp 3) (ht2 p hp hp7))) ht3_pDiv
  -- Step B: pDiv p 5 ((a_fn (p - 1) : ℚ) - (1 + 9 * ((p : ℚ) * H1 p)))
  have hapm : pDiv p 5 ((a_fn (p - 1) : ℚ) - (1 + 9 * ((p : ℚ) * H1 p))) := by
    let g : ℕ × ℕ × ℕ → ℚ := fun x =>
      (-1 : ℚ) ^ (p - 1 - x.1 - x.2.1 - x.2.2) *
        ((3 * p - 1).choose (p - 1 - x.1 - x.2.1 - x.2.2) : ℚ) *
        ((p + x.1 - 1).choose x.1 : ℚ) ^ 2 *
        ((p + x.2.1 - 1).choose x.2.1 : ℚ) ^ 2 *
        ((p + x.2.2 - 1).choose x.2.2 : ℚ) ^ 2
    have haQ : (a_fn (p - 1) : ℚ) = ∑ x ∈ Tlt p, g x := by
      have hZ := hapred p hp_pos
      rw [triple_sum_lt_eq_flat] at hZ
      have hQ : ((a_fn (p - 1) : ℤ) : ℚ) =
          ((∑ x ∈ Tlt p,
            (-1 : ℤ) ^ (p - 1 - x.1 - x.2.1 - x.2.2) *
              ((3 * p - 1).choose (p - 1 - x.1 - x.2.1 - x.2.2) : ℤ) *
              ((p + x.1 - 1).choose x.1 : ℤ) ^ 2 *
              ((p + x.2.1 - 1).choose x.2.1 : ℤ) ^ 2 *
              ((p + x.2.2 - 1).choose x.2.2 : ℤ) ^ 2 : ℤ) : ℚ) := congrArg Int.cast hZ
      push_cast at hQ; exact hQ
    rw [haQ, sum_partition_p_fine p (Tlt p) g]
    -- s0: only (0,0,0)!
    have hT0_eq : (Tlt p).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2) = {(0, 0, 0)} := by
      ext ⟨a, b, c⟩
      simp only [mem_filter, Tlt, mem_product, mem_range, mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨ha', hb', hc'⟩, _⟩, hda, hdb, hdc⟩
        exact ⟨Nat.eq_zero_of_dvd_of_lt hda ha',
               Nat.eq_zero_of_dvd_of_lt hdb hb',
               Nat.eq_zero_of_dvd_of_lt hdc hc'⟩
      · rintro ⟨rfl, rfl, rfl⟩
        exact ⟨⟨⟨hp_pos, hp_pos, hp_pos⟩, hp_pos⟩, dvd_zero p, dvd_zero p, dvd_zero p⟩
    have hs0_val : ∑ x ∈ (Tlt p).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g x =
        ((3 * p - 1).choose (p - 1) : ℚ) := by
      rw [hT0_eq, sum_singleton]
      dsimp only [g]
      have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
      rcases hp_odd with ⟨q, hq⟩
      have hev : p - 1 = 2 * q := by omega
      simp only [Nat.sub_zero, Nat.add_zero, Nat.choose_zero_right, hev, pow_mul]
      norm_num
    have hs0_pDiv : pDiv p 5 ((∑ x ∈ (Tlt p).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g x) -
        (1 + 6 * (p : ℚ) * H1 p)) := by
      rw [hs0_val]
      have h3 := hCkp p 3 hp hp7 (by norm_num)
      have hrew : ((3 * p - 1).choose (p - 1) : ℚ) - (1 + 6 * (p : ℚ) * H1 p) =
          ((3 * p - 1).choose (p - 1) : ℚ) - (1 + ((3 * (3 - 1) : ℕ) : ℚ) * (p : ℚ) * H1 p) := by
        norm_num
      rw [hrew]; exact h3
    -- s1: 3 equal sums, matching hs1!
    have hs1a_eq : ∑ x ∈ (Tlt p).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g x =
        ∑ i ∈ Ico 1 p, ((-1 : ℚ) ^ (p - 1 - i) *
          ((3 * p - 1).choose (p - 1 - i) : ℚ) * (((p + i - 1).choose i : ℚ) ^ 2)) := by
      symm
      refine Finset.sum_bij (fun i _ => (i, 0, 0)) ?_ ?_ ?_ ?_
      · intro i hi
        have hi1 := (mem_Ico.mp hi).1; have hi2 := (mem_Ico.mp hi).2
        simp only [mem_filter, Tlt, mem_product, mem_range]
        exact ⟨⟨⟨hi2, hp_pos, hp_pos⟩, by omega⟩,
               fun h => by have := Nat.le_of_dvd (by omega) h; omega, dvd_zero p, dvd_zero p⟩
      · intro i₁ _ i₂ _ h; exact congrArg Prod.fst h
      · intro ⟨a, b, c⟩ hy
        simp only [mem_filter, Tlt, mem_product, mem_range] at hy
        have ha1 : 1 ≤ a := Nat.pos_of_ne_zero (fun h0 => hy.2.1 (h0 ▸ dvd_zero p))
        have hb0 : b = 0 := Nat.eq_zero_of_dvd_of_lt hy.2.2.1 hy.1.1.2.1
        have hc0 : c = 0 := Nat.eq_zero_of_dvd_of_lt hy.2.2.2 hy.1.1.2.2
        exact ⟨a, mem_Ico.mpr ⟨ha1, hy.1.1.1⟩, by ext <;> dsimp only <;> omega⟩
      · intro i _; dsimp only [g]; simp
    have hs1b_eq : ∑ x ∈ (Tlt p).filter (fun x => p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ p ∣ x.2.2), g x =
        ∑ x ∈ (Tlt p).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g x := by
      apply Tlt_swap12_sum p _ _ g (fun x => by dsimp only; tauto)
      intro x; dsimp only [g]
      have : p - 1 - x.1 - x.2.1 - x.2.2 = p - 1 - x.2.1 - x.1 - x.2.2 := by omega
      rw [this]; ring
    have hs1c_eq : ∑ x ∈ (Tlt p).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2), g x =
        ∑ x ∈ (Tlt p).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g x := by
      apply Tlt_swap13_sum p _ _ g (fun x => by dsimp only; tauto)
      intro x; dsimp only [g]
      have : p - 1 - x.1 - x.2.1 - x.2.2 = p - 1 - x.2.2 - x.2.1 - x.1 := by omega
      rw [this]; ring
    -- s2: 3 equal sums, matching hs2!
    have hs2a_eq : ∑ x ∈ (Tlt p).filter (fun x => ¬ p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ p ∣ x.2.2), g x =
        ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
          if i + j < p then ((-1 : ℚ) ^ (p - 1 - i - j) * ((3 * p - 1).choose (p - 1 - i - j) : ℚ) *
            (((p + i - 1).choose i : ℚ) ^ 2) * (((p + j - 1).choose j : ℚ) ^ 2)) else 0 := by
      rw [← sum_product', ← sum_filter]
      symm
      refine Finset.sum_bij (fun y _ => (y.1, y.2, 0)) ?_ ?_ ?_ ?_
      · intro ⟨i, j⟩ hy
        simp only [mem_filter, mem_product, mem_Ico, Tlt, mem_range] at hy ⊢
        refine ⟨⟨⟨hy.1.1.2, hy.1.2.2, hp_pos⟩, by omega⟩, ?_, ?_, dvd_zero p⟩
        · intro h; have := Nat.le_of_dvd (by omega) h; omega
        · intro h; have := Nat.le_of_dvd (by omega) h; omega
      · intro y₁ _ y₂ _ h
        rcases y₁ with ⟨a₁, b₁⟩; rcases y₂ with ⟨a₂, b₂⟩
        simp only [Prod.mk.injEq] at h ⊢; exact ⟨h.1, h.2.1⟩
      · intro ⟨a, b, c⟩ hy
        simp only [mem_filter, Tlt, mem_product, mem_range] at hy
        have ha1 : 1 ≤ a := Nat.pos_of_ne_zero (fun h0 => hy.2.1 (h0 ▸ dvd_zero p))
        have hb1 : 1 ≤ b := Nat.pos_of_ne_zero (fun h0 => hy.2.2.1 (h0 ▸ dvd_zero p))
        have hc0 : c = 0 := Nat.eq_zero_of_dvd_of_lt hy.2.2.2 hy.1.1.2.2
        refine ⟨(a, b), ?_, by ext <;> dsimp only <;> omega⟩
        simp only [mem_filter, mem_product, mem_Ico]
        exact ⟨⟨⟨ha1, hy.1.1.1⟩, ⟨hb1, hy.1.1.2.1⟩⟩, by omega⟩
      · intro ⟨i, j⟩ _; dsimp only [g]; simp
    have hs2b_eq : ∑ x ∈ (Tlt p).filter (fun x => ¬ p ∣ x.1 ∧ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2), g x =
        ∑ x ∈ (Tlt p).filter (fun x => ¬ p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ p ∣ x.2.2), g x := by
      refine Finset.sum_bij (fun x _ => (x.1, x.2.2, x.2.1)) ?_ ?_ ?_ ?_
      · intro x hx; simp only [mem_filter, Tlt, mem_product, mem_range] at hx ⊢
        exact ⟨⟨⟨hx.1.1.1, hx.1.1.2.2, hx.1.1.2.1⟩, by omega⟩, hx.2.1, hx.2.2.2, hx.2.2.1⟩
      · intro x₁ _ x₂ _ h
        rcases x₁ with ⟨a₁, b₁, c₁⟩; rcases x₂ with ⟨a₂, b₂, c₂⟩
        simp only [Prod.mk.injEq] at h ⊢; exact ⟨h.1, h.2.2, h.2.1⟩
      · intro y hy; refine ⟨(y.1, y.2.2, y.2.1), ?_, by rcases y with ⟨a, b, c⟩; rfl⟩
        simp only [mem_filter, Tlt, mem_product, mem_range] at hy ⊢
        exact ⟨⟨⟨hy.1.1.1, hy.1.1.2.2, hy.1.1.2.1⟩, by omega⟩, hy.2.1, hy.2.2.2, hy.2.2.1⟩
      · intro x _; dsimp only [g]
        have : p - 1 - x.1 - x.2.1 - x.2.2 = p - 1 - x.1 - x.2.2 - x.2.1 := by omega
        rw [this]; ring
    have hs2c_eq : ∑ x ∈ (Tlt p).filter (fun x => p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2), g x =
        ∑ x ∈ (Tlt p).filter (fun x => ¬ p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ p ∣ x.2.2), g x := by
      apply Tlt_swap13_sum p _ _ g (fun x => by dsimp only; tauto)
      intro x; dsimp only [g]
      have : p - 1 - x.1 - x.2.1 - x.2.2 = p - 1 - x.2.2 - x.2.1 - x.1 := by omega
      rw [this]; ring
    -- s3: each term has p^6 ∣ C(p + i - 1, i)^2 * C(p + j - 1, j)^2 * C(p + l - 1, l)^2!
    have hs3_pDiv : pDiv p 5 (∑ x ∈ (Tlt p).filter (fun x => ¬ p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2), g x) := by
      apply pDiv_sum hp; intro x hx
      have hnd := (mem_filter.mp hx).2
      have hch_p : ∀ k, ¬ p ∣ k → (p : ℤ) ^ 2 ∣ ((p + k - 1).choose k : ℤ) ^ 2 := fun k hndk => by
        have hk_pos : 0 < k := Nat.pos_of_ne_zero (fun h0 => hndk (h0 ▸ dvd_zero p))
        have h1 := dvd_choose_pred_of_pow_dvd hp (by simp : p ^ 1 ∣ p) hp_pos hk_pos (Nat.zero_le 1)
          (by rw [padicValNat_eq_zero_of_not_dvd hndk])
        simp only [Nat.sub_zero, pow_one] at h1
        exact pow_dvd_pow_of_dvd (by exact_mod_cast h1) 2
      have h6 : (p : ℤ) ^ 6 ∣
          (-1 : ℤ) ^ (p - 1 - x.1 - x.2.1 - x.2.2) *
            ((3 * p - 1).choose (p - 1 - x.1 - x.2.1 - x.2.2) : ℤ) *
            ((p + x.1 - 1).choose x.1 : ℤ) ^ 2 *
            ((p + x.2.1 - 1).choose x.2.1 : ℤ) ^ 2 *
            ((p + x.2.2 - 1).choose x.2.2 : ℤ) ^ 2 := by
        have hm := mul_dvd_mul (mul_dvd_mul (hch_p x.1 hnd.1) (hch_p x.2.1 hnd.2.1))
          (hch_p x.2.2 hnd.2.2)
        have hrew : (-1 : ℤ) ^ (p - 1 - x.1 - x.2.1 - x.2.2) *
              ((3 * p - 1).choose (p - 1 - x.1 - x.2.1 - x.2.2) : ℤ) *
              ((p + x.1 - 1).choose x.1 : ℤ) ^ 2 *
              ((p + x.2.1 - 1).choose x.2.1 : ℤ) ^ 2 *
              ((p + x.2.2 - 1).choose x.2.2 : ℤ) ^ 2 =
            (((p + x.1 - 1).choose x.1 : ℤ) ^ 2 *
              ((p + x.2.1 - 1).choose x.2.1 : ℤ) ^ 2 *
              ((p + x.2.2 - 1).choose x.2.2 : ℤ) ^ 2) *
            ((-1 : ℤ) ^ (p - 1 - x.1 - x.2.1 - x.2.2) *
              ((3 * p - 1).choose (p - 1 - x.1 - x.2.1 - x.2.2) : ℤ)) := by ring
        rw [hrew]; exact dvd_mul_of_dvd_left (by simpa [← pow_add] using hm) _
      have h5 := pDiv_of_dvd_int hp (dvd_trans (pow_dvd_pow (p : ℤ) (by norm_num : 5 ≤ 6)) h6)
      dsimp only [g]; push_cast at h5; exact h5
    -- Combine s0 + 3*s1 + 3*s2 + s3 - (1 + 9 * p * H1)!
    rw [hs1b_eq, hs1c_eq, hs1a_eq, hs2b_eq, hs2c_eq, hs2a_eq]
    set S0 := ∑ x ∈ (Tlt p).filter (fun x => p ∣ x.1 ∧ p ∣ x.2.1 ∧ p ∣ x.2.2), g x
    set S1 := ∑ i ∈ Ico 1 p, ((-1 : ℚ) ^ (p - 1 - i) *
      ((3 * p - 1).choose (p - 1 - i) : ℚ) * (((p + i - 1).choose i : ℚ) ^ 2))
    set S2 := ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 p,
      if i + j < p then ((-1 : ℚ) ^ (p - 1 - i - j) * ((3 * p - 1).choose (p - 1 - i - j) : ℚ) *
        (((p + i - 1).choose i : ℚ) ^ 2) * (((p + j - 1).choose j : ℚ) ^ 2)) else 0
    set S3 := ∑ x ∈ (Tlt p).filter (fun x => ¬ p ∣ x.1 ∧ ¬ p ∣ x.2.1 ∧ ¬ p ∣ x.2.2), g x
    have hrew : S0 + (S1 + S1 + S1) + (S2 + S2 + S2) + S3 - (1 + 9 * ((p : ℚ) * H1 p)) =
        (S0 - (1 + 6 * (p : ℚ) * H1 p)) +
        (3 * S1 - 3 * (p : ℚ) * H1 p) +
        3 * S2 + S3 := by ring
    rw [hrew]
    exact pDiv_add hp (pDiv_add hp (pDiv_add hp hs0_pDiv (hs1 p hp hp7))
      (by simpa using pDiv_mul hp (pDiv_nat_zero hp 3) (hs2 p hp hp7))) hs3_pDiv
  exact hPow hp hx hap hapm

end OMA_A364114_Glue

theorem OMA.solution : type_of% @OMA.S_oeis_a364114.main := by
  have ha : ∀ N : ℕ, OMA.S_oeis_a364114.a N =
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1 - i), ∑ l ∈ Finset.range (N + 1 - i - j),
        (4 * N - i - j - l).choose (3 * N) *
          (N.choose i) ^ 2 * (N.choose j) ^ 2 * (N.choose l) ^ 2 :=
    fun N => OMA_A364114_Part1.a_eq_triple_sum N
  have hapred : ∀ N : ℕ, 0 < N → (OMA.S_oeis_a364114.a (N - 1) : ℤ) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range (N - i), ∑ l ∈ Finset.range (N - i - j),
        (-1 : ℤ) ^ (N - 1 - i - j - l) *
          ((3 * N - 1).choose (N - 1 - i - j - l) : ℤ) *
          ((N + i - 1).choose i : ℤ) ^ 2 *
          ((N + j - 1).choose j : ℤ) ^ 2 *
          ((N + l - 1).choose l : ℤ) ^ 2 :=
    fun N hN => OMA_A364114_Part1.a_pred_eq_triple_sum N hN
  refine ⟨fun p n r hp hp5 hn hr => ⟨?_, ?_⟩, fun p hp hp7 => ?_⟩
  · exact OMA_A364114_Glue.part1_glue OMA.S_oeis_a364114.a ha
      OMA_A364114_Part2.kazandzidis_dvd
      OMA_A364114_Part3.S1_vanish_dvd
      p n r hp hp5 hn hr
  · exact OMA_A364114_Glue.part2_glue OMA.S_oeis_a364114.a hapred
      OMA_A364114_Part2.kazandzidis_dvd
      OMA_A364114_Part3.S2_vanish_dvd
      p n r hp hp5 hn hr
  · exact OMA_A364114_Glue.part34_glue OMA.S_oeis_a364114.a (fun q => OMA_A364114_Part4.harmH q 1)
      ha hapred
      OMA_A364114_Part4.harmH1_pDiv_two
      OMA_A364114_Part4.choose_kp_sub_one_pDiv5
      OMA_A364114_Part4.choose_kp_p_eq
      OMA_A364114_Part4.t1_pDiv5
      OMA_A364114_Part4.s1_pDiv5
      OMA_A364114_Part4.t2_pDiv5
      OMA_A364114_Part4.s2_pDiv5
      (fun hp' hx hap hapm => OMA_A364114_Part4.pow21_eq_pow11_of_linear hp' hx hap hapm)
      p hp hp7
