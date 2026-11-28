import OMAStatements.S_oeis_a096121
import Mathlib

namespace OMA.A096121

open OMA.S_oeis_a096121
open Finset

/-! ## Binomial series for the crossing decomposition -/

/-- `T N k = ((N - k)!)^2 / (k!^2 (N - 2k)!)` when `2k ≤ N`, else `0`. -/
def T (N k : ℕ) : ℕ :=
  if 2 * k ≤ N then Nat.choose (N - k) k * ((N - k).factorial / k.factorial) else 0

/-- Even-crossing weight. `evenTerm n j` vanishes unless `1 ≤ j` and `2j ≤ n`. -/
def evenTerm (n j : ℕ) : ℕ :=
  if 1 ≤ j ∧ 2 * j ≤ n then
    (n - 2 * j).factorial * Nat.choose (n - j) j * Nat.choose (n - j - 1) (j - 1)
  else 0

/-- Weight of walks with exactly `r` vertical steps, up to the `2 n!` symmetry. -/
def piece (n r : ℕ) : ℕ :=
  if r % 2 = 0 then evenTerm n (r / 2) else if 1 ≤ n then T (n - 1) (r / 2) else 0

def B (N : ℕ) : ℕ := ∑ k ∈ range (N + 1), T N k

def C (n : ℕ) : ℕ := ∑ j ∈ range (n + 1), evenTerm n j

theorem T_of_le {N k : ℕ} (h : 2 * k ≤ N) :
    T N k = Nat.choose (N - k) k * ((N - k).factorial / k.factorial) := by
  simp [T, h]

theorem T_of_gt {N k : ℕ} (h : N < 2 * k) : T N k = 0 := by
  simp [T, Nat.not_le.mpr h]

theorem T_zero_right (N : ℕ) : T N 0 = N.factorial := by
  simp [T, Nat.choose_zero_right, Nat.factorial_zero]

theorem T_num_dvd {N k : ℕ} (h : 2 * k ≤ N) :
    k.factorial * k.factorial * (N - 2 * k).factorial ∣
      (N - k).factorial * (N - k).factorial := by
  have hk : k ≤ N - k := by omega
  have hsub : (N - k) - k = N - 2 * k := by omega
  have hd1 : k.factorial * (N - 2 * k).factorial ∣ (N - k).factorial := by
    simpa [hsub] using Nat.factorial_mul_factorial_dvd_factorial hk
  have hd2 : k.factorial ∣ (N - k).factorial := Nat.factorial_dvd_factorial hk
  have hord :
      (k.factorial * (N - 2 * k).factorial) * k.factorial =
        k.factorial * k.factorial * (N - 2 * k).factorial := by
    ring
  rw [← hord]
  exact Nat.mul_dvd_mul hd1 hd2

theorem T_eq_div {N k : ℕ} (h : 2 * k ≤ N) :
    T N k =
      (N - k).factorial * (N - k).factorial /
        (k.factorial * k.factorial * (N - 2 * k).factorial) := by
  have hk : k ≤ N - k := by omega
  have hsub : (N - k) - k = N - 2 * k := by omega
  have hd1 : k.factorial * (N - 2 * k).factorial ∣ (N - k).factorial := by
    simpa [hsub] using Nat.factorial_mul_factorial_dvd_factorial hk
  have hd2 : k.factorial ∣ (N - k).factorial := Nat.factorial_dvd_factorial hk
  rw [T_of_le h, Nat.choose_eq_factorial_div_factorial hk, hsub]
  have hmul := Nat.div_mul_div_comm hd1 hd2
  rw [hmul]
  apply congrArg (fun d => (N - k).factorial * (N - k).factorial / d)
  ring

theorem T_cast {N k : ℕ} (h : 2 * k ≤ N) :
    (T N k : ℚ) =
      ((N - k).factorial : ℚ) * (N - k).factorial /
        ((k.factorial : ℚ) * k.factorial * (N - 2 * k).factorial) := by
  rw [T_eq_div h, Nat.cast_div_charZero (T_num_dvd h)]
  push_cast
  rfl

theorem T_div_one (num den : ℕ) (hpos : 0 < den) (h : num = den) : num / den = 1 := by
  exact Nat.div_eq_of_eq_mul_left hpos (by rw [one_mul, h])

theorem T_rec_zero (N : ℕ) (hN : 1 ≤ N) :
    T N 0 = N * T (N - 1) 0 := by
  rw [T_zero_right, T_zero_right]
  have : N = (N - 1) + 1 := by omega
  rw [this, Nat.factorial_succ]
  simp

theorem T_rec_out {N k : ℕ} (hN : 2 ≤ N) (hk : N < 2 * k) :
    T N k = N * T (N - 1) k + (if k = 0 then 0 else T (N - 2) (k - 1)) := by
  have hk0 : k ≠ 0 := by omega
  have h1 : N - 1 < 2 * k := by omega
  have h2 : N - 2 < 2 * (k - 1) := by omega
  simp [T_of_gt hk, T_of_gt h1, T_of_gt h2, hk0]

theorem T_rec_diag {N k : ℕ} (hN : 2 ≤ N) (_hk : 1 ≤ k) (heq : 2 * k = N) :
    T N k = N * T (N - 1) k + T (N - 2) (k - 1) := by
  have hle : 2 * k ≤ N := by omega
  have hgt : N - 1 < 2 * k := by omega
  have h2 : 2 * (k - 1) ≤ N - 2 := by omega
  have hT : T N k = 1 := by
    rw [T_eq_div hle]
    have hnum :
        (N - k).factorial * (N - k).factorial =
          k.factorial * k.factorial * (N - 2 * k).factorial := by
      simp [show N - k = k by omega, show N - 2 * k = 0 by omega]
    exact T_div_one _ _ (by positivity) hnum
  have hS : T (N - 2) (k - 1) = 1 := by
    rw [T_eq_div h2]
    have hnum :
        (N - 2 - (k - 1)).factorial * (N - 2 - (k - 1)).factorial =
          (k - 1).factorial * (k - 1).factorial *
            (N - 2 - 2 * (k - 1)).factorial := by
      simp [show N - 2 - (k - 1) = k - 1 by omega,
        show N - 2 - 2 * (k - 1) = 0 by omega]
    exact T_div_one _ _ (by positivity) hnum
  simp [hT, T_of_gt hgt, hS]

theorem T_rec_near {N k : ℕ} (hN : 2 ≤ N) (hk : 1 ≤ k) (heq : 2 * k = N - 1) :
    T N k = N * T (N - 1) k + T (N - 2) (k - 1) := by
  have hNle : 2 * k ≤ N := by omega
  have h1 : 2 * k ≤ N - 1 := by omega
  have h2 : 2 * (k - 1) ≤ N - 2 := by omega
  have hTN : T N k = (k + 1) * (k + 1) := by
    rw [T_eq_div hNle]
    have hNk : N - k = k + 1 := by omega
    have hN2 : N - 2 * k = 1 := by omega
    rw [hNk, hN2, Nat.factorial_one]
    have hfac : (k + 1).factorial = (k + 1) * k.factorial := by
      simpa [Nat.succ_eq_add_one] using Nat.factorial_succ k
    have hnum :
        (k + 1).factorial * (k + 1).factorial =
          ((k + 1) * (k + 1)) * (k.factorial * k.factorial * 1) := by
      rw [hfac]
      ring
    exact Nat.div_eq_of_eq_mul_left (by positivity) hnum
  have hT1 : T (N - 1) k = 1 := by
    rw [T_eq_div h1]
    have hnum :
        (N - 1 - k).factorial * (N - 1 - k).factorial =
          k.factorial * k.factorial * (N - 1 - 2 * k).factorial := by
      simp [show N - 1 - k = k by omega, show N - 1 - 2 * k = 0 by omega]
    exact T_div_one _ _ (by positivity) hnum
  have hT2 : T (N - 2) (k - 1) = k * k := by
    by_cases hk1 : k = 1
    · subst hk1
      have hN3 : N = 3 := by omega
      simp [hN3, T_zero_right]
    · have hk2 : 2 ≤ k := by omega
      rw [T_eq_div h2]
      have hL : N - 2 - (k - 1) = k := by omega
      have hR : N - 2 - 2 * (k - 1) = 1 := by omega
      rw [hL, hR, Nat.factorial_one]
      have hfac : k.factorial = k * (k - 1).factorial := by
        rw [show k = (k - 1) + 1 by omega, Nat.factorial_succ]
        simp
      have hnum :
          k.factorial * k.factorial =
            (k * k) * ((k - 1).factorial * (k - 1).factorial * 1) := by
        rw [hfac]
        ring
      exact Nat.div_eq_of_eq_mul_left (by positivity) hnum
  have hNeq : N = 2 * k + 1 := by omega
  calc
    T N k = (k + 1) * (k + 1) := hTN
    _ = N + k * k := by rw [hNeq]; ring
    _ = N * T (N - 1) k + T (N - 2) (k - 1) := by rw [hT1, hT2, mul_one]

theorem T_rec_room (N k : ℕ) (hN : 2 ≤ N) (hk : 1 ≤ k) (hkN : 2 * k ≤ N - 2) :
    T N k = N * T (N - 1) k + T (N - 2) (k - 1) := by
  have h1 : 2 * k ≤ N := by omega
  have h2 : 2 * k ≤ N - 1 := by omega
  have h3 : 2 * (k - 1) ≤ N - 2 := by omega
  apply (Nat.cast_inj (R := ℚ)).mp
  rw [Nat.cast_add, Nat.cast_mul, T_cast h1, T_cast h2, T_cast h3]
  have e1 : N - 1 - k = N - k - 1 := by omega
  have e2 : N - 1 - 2 * k = N - 2 * k - 1 := by omega
  have e3 : N - 2 - (k - 1) = N - k - 1 := by omega
  have e4 : N - 2 - 2 * (k - 1) = N - 2 * k := by omega
  simp only [e1, e2, e3, e4]
  have hfk : (k.factorial : ℚ) = (k : ℚ) * ↑((k - 1).factorial) := by
    have hk' : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk']
    rw [Nat.factorial_succ]
    have hcast : (k : ℚ) = ↑(k - 1) + 1 := by
      conv_lhs => rw [hk']
      simp [Nat.cast_add, Nat.cast_one]
    rw [hcast]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hfNk : ((N - k).factorial : ℚ) = ↑(N - k) * ↑((N - k - 1).factorial) := by
    have h' : N - k = (N - k - 1) + 1 := by omega
    conv_lhs => rw [h']
    rw [Nat.factorial_succ]
    have hcast : (↑(N - k) : ℚ) = ↑(N - k - 1) + 1 := by
      conv_lhs => rw [h']
      simp [Nat.cast_add, Nat.cast_one]
    rw [hcast]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf2 : ((N - 2 * k).factorial : ℚ) =
      ↑(N - 2 * k) * ↑((N - 2 * k - 1).factorial) := by
    have h' : N - 2 * k = (N - 2 * k - 1) + 1 := by omega
    conv_lhs => rw [h']
    rw [Nat.factorial_succ]
    have hcast : (↑(N - 2 * k) : ℚ) = ↑(N - 2 * k - 1) + 1 := by
      conv_lhs => rw [h']
      simp [Nat.cast_add, Nat.cast_one]
    rw [hcast]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hD : (↑N - ↑k * 2 : ℚ) ≠ 0 := by
    have hcast : (↑(N - 2 * k) : ℚ) = ↑N - ↑k * 2 := by
      rw [Nat.cast_sub (by omega : 2 * k ≤ N), Nat.cast_mul]
      push_cast
      ring
    rw [← hcast]
    exact Nat.cast_ne_zero.mpr (by omega : N - 2 * k ≠ 0)
  rw [hfk, hfNk, hf2, Nat.cast_sub (show k ≤ N by omega),
    Nat.cast_sub (show 2 * k ≤ N by omega), Nat.cast_mul]
  push_cast
  field_simp [hD]
  ring

theorem T_rec (N k : ℕ) (hN : 2 ≤ N) :
    T N k = N * T (N - 1) k + (if k = 0 then 0 else T (N - 2) (k - 1)) := by
  by_cases hk0 : k = 0
  · subst hk0
    simp [T_rec_zero N (by omega)]
  · by_cases hout : N < 2 * k
    · exact T_rec_out hN hout
    · have hle : 2 * k ≤ N := by omega
      have hk : 1 ≤ k := by omega
      by_cases hdiag : 2 * k = N
      · simp [hk0, T_rec_diag hN hk hdiag]
      · by_cases hnear : 2 * k = N - 1
        · simp [hk0, T_rec_near hN hk hnear]
        · have hroom : 2 * k ≤ N - 2 := by omega
          simp [hk0, T_rec_room N k hN hk hroom]

theorem B_zero : B 0 = 1 := by
  decide

theorem B_one : B 1 = 1 := by
  decide

theorem B_rec (N : ℕ) (hN : 2 ≤ N) : B N = N * B (N - 1) + B (N - 2) := by
  conv_lhs => unfold B
  have hpoint : ∀ k ∈ range (N + 1),
      T N k = N * T (N - 1) k + (if k = 0 then 0 else T (N - 2) (k - 1)) := by
    intro k _
    exact T_rec N k hN
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hfirst : ∑ k ∈ range (N + 1), T (N - 1) k = B (N - 1) := by
    rw [Finset.sum_range_succ, T_of_gt (by omega : N - 1 < 2 * N), add_zero]
    have hN : (N - 1) + 1 = N := by omega
    conv_lhs => rw [← hN]
    rfl
  have hsecond :
      ∑ k ∈ range (N + 1), (if k = 0 then 0 else T (N - 2) (k - 1)) = B (N - 2) := by
    rw [Finset.sum_range_succ']
    have hhead : (if (0 : ℕ) = 0 then 0 else T (N - 2) (0 - 1)) = 0 := by rw [if_pos rfl]
    rw [hhead, add_zero]
    have hbody : ∀ x ∈ range N,
        (if x + 1 = 0 then 0 else T (N - 2) (x + 1 - 1)) = T (N - 2) x := by
      intro x _
      rw [if_neg (by omega : x + 1 ≠ 0), show x + 1 - 1 = x by omega]
    rw [Finset.sum_congr rfl hbody]
    have hsplit : ∑ i ∈ range N, T (N - 2) i =
        ∑ i ∈ range (N - 1), T (N - 2) i + T (N - 2) (N - 1) := by
      have hN1 : (N - 1) + 1 = N := by omega
      conv_lhs => rw [← hN1]
      exact Finset.sum_range_succ (fun i => T (N - 2) i) (N - 1)
    rw [hsplit, T_of_gt (by omega : N - 2 < 2 * (N - 1)), add_zero]
    have hN2 : (N - 2) + 1 = N - 1 := by omega
    conv_lhs => rw [← hN2]
    rfl
  rw [hfirst, hsecond]

theorem evenTerm_zero (n : ℕ) : evenTerm n 0 = 0 := by
  simp [evenTerm]

theorem even_num_dvd {n j : ℕ} (hj : 1 ≤ j) (hn : 2 * j ≤ n) :
    j.factorial * (j - 1).factorial * (n - 2 * j).factorial ∣
      (n - j).factorial * (n - j - 1).factorial := by
  have hj1 : j ≤ n - j := by omega
  have s1 : (n - j) - j = n - 2 * j := by omega
  have hd1 : j.factorial * (n - 2 * j).factorial ∣ (n - j).factorial := by
    simpa [s1] using Nat.factorial_mul_factorial_dvd_factorial hj1
  have hd2 : (j - 1).factorial ∣ (n - j - 1).factorial :=
    Nat.factorial_dvd_factorial (by omega)
  have hmul := Nat.mul_dvd_mul hd1 hd2
  have hord :
      (j.factorial * (n - 2 * j).factorial) * (j - 1).factorial =
        j.factorial * (j - 1).factorial * (n - 2 * j).factorial := by
    ring
  rw [← hord]
  exact hmul

theorem evenTerm_cast {n j : ℕ} (hj : 1 ≤ j) (hn : 2 * j ≤ n) :
    (evenTerm n j : ℚ) =
      ((n - j).factorial : ℚ) * ↑((n - j - 1).factorial) /
        (↑(j.factorial) * ↑((j - 1).factorial) * ↑((n - 2 * j).factorial)) := by
  have hj1 : j ≤ n - j := by omega
  have hj2 : j - 1 ≤ n - j - 1 := by omega
  have s1 : (n - j) - j = n - 2 * j := by omega
  have s2 : (n - j - 1) - (j - 1) = n - 2 * j := by omega
  have hdB : j.factorial * (n - 2 * j).factorial ∣ (n - j).factorial := by
    simpa [s1] using Nat.factorial_mul_factorial_dvd_factorial hj1
  have hdE : (j - 1).factorial * (n - 2 * j).factorial ∣ (n - j - 1).factorial := by
    simpa [s2] using Nat.factorial_mul_factorial_dvd_factorial hj2
  unfold evenTerm
  rw [if_pos ⟨hj, hn⟩, Nat.choose_eq_factorial_div_factorial hj1,
    Nat.choose_eq_factorial_div_factorial hj2, s1, s2]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_div_charZero hdB, Nat.cast_div_charZero hdE]
  push_cast
  field_simp

theorem evenTerm_one {n : ℕ} (hn : 2 ≤ n) : evenTerm n 1 = (n - 1).factorial := by
  unfold evenTerm
  rw [if_pos (show 1 ≤ 1 ∧ 2 * 1 ≤ n by omega)]
  have hsub : n - 2 * 1 = n - 2 := by omega
  rw [hsub, Nat.choose_one_right, Nat.choose_zero_right, Nat.mul_one]
  have hfac : (n - 1).factorial = (n - 1) * (n - 2).factorial := by
    conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega]
    rw [Nat.factorial_succ]
    have h : n - 2 + 1 = n - 1 := by omega
    rw [h]
  rw [← Nat.mul_comm]
  exact hfac.symm

theorem evenTerm_rec_one {n : ℕ} (hn : 3 ≤ n) :
    evenTerm n 1 = (n - 1) * evenTerm (n - 1) 1 + evenTerm (n - 2) 0 := by
  rw [evenTerm_one (by omega), evenTerm_one (by omega : 2 ≤ n - 1), evenTerm_zero]
  have h1 : (n - 1).factorial = (n - 1) * (n - 2).factorial := by
    conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega]
    rw [Nat.factorial_succ]
    have h : n - 2 + 1 = n - 1 := by omega
    rw [h]
  have h2 : (n - 1 - 1).factorial = (n - 2).factorial := by
    have h : n - 1 - 1 = n - 2 := by omega
    rw [h]
  rw [h1, h2]
  ring

theorem evenTerm_value_one {n j : ℕ} (hj : 1 ≤ j) (hn : 2 * j = n) :
    evenTerm n j = 1 := by
  apply (Nat.cast_inj (R := ℚ)).mp
  rw [evenTerm_cast hj (by omega), Nat.cast_one]
  simp only [show n - j = j by omega, show n - 2 * j = 0 by omega,
    Nat.factorial_zero, Nat.cast_one]
  field_simp

theorem evenTerm_rec_diag {n j : ℕ} (hn : 3 ≤ n) (hj : 1 ≤ j) (heq : 2 * j = n) :
    evenTerm n j = (n - 1) * evenTerm (n - 1) j + evenTerm (n - 2) (j - 1) := by
  have hj2 : 2 ≤ j := by omega
  have hzero : evenTerm (n - 1) j = 0 := by
    unfold evenTerm
    rw [if_neg (by omega : ¬ (1 ≤ j ∧ 2 * j ≤ n - 1))]
  have hv : evenTerm (n - 2) (j - 1) = 1 :=
    evenTerm_value_one (by omega : 1 ≤ j - 1) (by omega : 2 * (j - 1) = n - 2)
  rw [evenTerm_value_one hj (by omega), hzero, hv]
  simp

theorem evenTerm_rec_near {n j : ℕ} (hn : 3 ≤ n) (hj : 2 ≤ j) (heq : 2 * j = n - 1) :
    evenTerm n j = (n - 1) * evenTerm (n - 1) j + evenTerm (n - 2) (j - 1) := by
  have hleft : evenTerm n j = j * (j + 1) := by
    unfold evenTerm
    rw [if_pos (show 1 ≤ j ∧ 2 * j ≤ n by omega)]
    have h1 : n - 2 * j = 1 := by omega
    have h2 : n - j = j + 1 := by omega
    rw [h1, h2, Nat.factorial_one]
    have h4 : j + 1 - 1 = j := by omega
    rw [h4]
    have hc1 : Nat.choose (j + 1) j = j + 1 := by
      rw [Nat.choose_symm_add, Nat.choose_one_right]
    have hc2 : Nat.choose j (j - 1) = j := by
      have hj' : j = (j - 1) + 1 := by omega
      conv_lhs => arg 1; rw [hj']
      rw [Nat.choose_symm_add, Nat.choose_one_right, ← hj']
    rw [hc1, hc2]
    ring
  have hmid : evenTerm (n - 1) j = 1 :=
    evenTerm_value_one (by omega) (by omega : 2 * j = n - 1)
  have htail : evenTerm (n - 2) (j - 1) = j * (j - 1) := by
    unfold evenTerm
    rw [if_pos (show 1 ≤ j - 1 ∧ 2 * (j - 1) ≤ n - 2 by omega)]
    have h1 : n - 2 - 2 * (j - 1) = 1 := by omega
    have h2 : n - 2 - (j - 1) = j := by omega
    rw [h1, h2, Nat.factorial_one]
    have h4 : j - 1 - 1 = j - 2 := by omega
    rw [h4]
    have hc1 : Nat.choose j (j - 1) = j := by
      have hj' : j = (j - 1) + 1 := by omega
      conv_lhs => arg 1; rw [hj']
      rw [Nat.choose_symm_add, Nat.choose_one_right, ← hj']
    have hc2 : Nat.choose (j - 1) (j - 2) = j - 1 := by
      have hj' : j - 1 = (j - 2) + 1 := by omega
      conv_lhs => arg 1; rw [hj']
      rw [Nat.choose_symm_add, Nat.choose_one_right, ← hj']
    rw [hc1, hc2, Nat.one_mul]
  have hN : n - 1 = 2 * j := by omega
  calc
    evenTerm n j = j * (j + 1) := hleft
    _ = 2 * j + j * (j - 1) := by
      have hk : j = (j - 1) + 1 := by omega
      have h1 : j * (j + 1) = ((j - 1) + 1) * ((j - 1) + 2) := by
        conv_lhs => rw [hk]
      have h2 : 2 * j + j * (j - 1) =
          2 * ((j - 1) + 1) + ((j - 1) + 1) * (j - 1) := by
        have ha : 2 * j = 2 * ((j - 1) + 1) := by
          conv_lhs => rw [hk]
        have hb : j * (j - 1) = ((j - 1) + 1) * (j - 1) := by
          conv_lhs => arg 1; rw [hk]
        rw [ha, hb]
      rw [h1, h2]
      ring
    _ = (n - 1) + j * (j - 1) := by rw [← hN]
    _ = (n - 1) * evenTerm (n - 1) j + evenTerm (n - 2) (j - 1) := by
      rw [hmid, htail, mul_one]

theorem evenTerm_rec_room (n j : ℕ) (hn : 3 ≤ n) (hj : 2 ≤ j) (hjn : 2 * j ≤ n - 2) :
    evenTerm n j = (n - 1) * evenTerm (n - 1) j + evenTerm (n - 2) (j - 1) := by
  have h1a : 1 ≤ j := by omega
  have h1b : 2 * j ≤ n := by omega
  have h2b : 2 * j ≤ n - 1 := by omega
  have h3a : 1 ≤ j - 1 := by omega
  have h3b : 2 * (j - 1) ≤ n - 2 := by omega
  apply (Nat.cast_inj (R := ℚ)).mp
  rw [Nat.cast_add, Nat.cast_mul, evenTerm_cast h1a h1b, evenTerm_cast h1a h2b,
    evenTerm_cast h3a h3b]
  have e1 : n - 1 - j = n - j - 1 := by omega
  have e3 : n - 1 - 2 * j = n - 2 * j - 1 := by omega
  have e4 : n - 2 - (j - 1) = n - j - 1 := by omega
  have e6 : n - 2 - 2 * (j - 1) = n - 2 * j := by omega
  simp only [e1, e3, e4, e6]
  have e7 : n - j - 1 - 1 = n - j - 2 := by omega
  have e8 : j - 1 - 1 = j - 2 := by omega
  simp only [e7, e8]
  have hfj : (j.factorial : ℚ) = (j : ℚ) * ↑((j - 1).factorial) := by
    have hj' : j = (j - 1) + 1 := by omega
    conv_lhs => rw [hj']
    rw [Nat.factorial_succ]
    have hcast : (j : ℚ) = ↑(j - 1) + 1 := by
      conv_lhs => rw [hj']
      simp [Nat.cast_add, Nat.cast_one]
    rw [hcast]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hfj1 : ((j - 1).factorial : ℚ) = ↑(j - 1) * ↑((j - 2).factorial) := by
    have hj' : j - 1 = (j - 2) + 1 := by omega
    conv_lhs => rw [hj']
    rw [Nat.factorial_succ]
    have hcast : (↑(j - 1) : ℚ) = ↑(j - 2) + 1 := by
      conv_lhs => rw [hj']
      simp [Nat.cast_add, Nat.cast_one]
    rw [hcast]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hfnj : ((n - j).factorial : ℚ) = ↑(n - j) * ↑((n - j - 1).factorial) := by
    have h' : n - j = (n - j - 1) + 1 := by omega
    conv_lhs => rw [h']
    rw [Nat.factorial_succ]
    have hcast : (↑(n - j) : ℚ) = ↑(n - j - 1) + 1 := by
      conv_lhs => rw [h']
      simp [Nat.cast_add, Nat.cast_one]
    rw [hcast]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hfnj1 : ((n - j - 1).factorial : ℚ) = ↑(n - j - 1) * ↑((n - j - 2).factorial) := by
    have h' : n - j - 1 = (n - j - 2) + 1 := by omega
    conv_lhs => rw [h']
    rw [Nat.factorial_succ]
    have hcast : (↑(n - j - 1) : ℚ) = ↑(n - j - 2) + 1 := by
      conv_lhs => rw [h']
      simp [Nat.cast_add, Nat.cast_one]
    rw [hcast]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hfn2 : ((n - 2 * j).factorial : ℚ) =
      ↑(n - 2 * j) * ↑((n - 2 * j - 1).factorial) := by
    have h' : n - 2 * j = (n - 2 * j - 1) + 1 := by omega
    conv_lhs => rw [h']
    rw [Nat.factorial_succ]
    have hcast : (↑(n - 2 * j) : ℚ) = ↑(n - 2 * j - 1) + 1 := by
      conv_lhs => rw [h']
      simp [Nat.cast_add, Nat.cast_one]
    rw [hcast]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hD : (↑n - ↑j * 2 : ℚ) ≠ 0 := by
    have hcast : (↑(n - 2 * j) : ℚ) = ↑n - ↑j * 2 := by
      rw [Nat.cast_sub (by omega : 2 * j ≤ n), Nat.cast_mul]
      push_cast
      ring
    rw [← hcast]
    exact Nat.cast_ne_zero.mpr (by omega : n - 2 * j ≠ 0)
  rw [hfj, hfj1, hfnj, hfnj1, hfn2]
  rw [Nat.cast_sub (show 1 ≤ n - j by omega)]
  rw [Nat.cast_sub (show j ≤ n by omega)]
  rw [Nat.cast_sub (show 1 ≤ j by omega)]
  rw [Nat.cast_sub (show 1 ≤ n by omega)]
  rw [Nat.cast_sub (show 2 * j ≤ n by omega), Nat.cast_mul]
  push_cast
  field_simp [hD]
  ring

theorem evenTerm_rec (n j : ℕ) (hn : 3 ≤ n) :
    evenTerm n j =
      (n - 1) * evenTerm (n - 1) j + (if j = 0 then 0 else evenTerm (n - 2) (j - 1)) := by
  by_cases hj0 : j = 0
  · subst hj0
    simp [evenTerm_zero]
  · by_cases hout : n < 2 * j
    · have h1 : n - 1 < 2 * j := by omega
      have h2 : n - 2 < 2 * (j - 1) := by omega
      unfold evenTerm
      rw [if_neg (by omega : ¬ (1 ≤ j ∧ 2 * j ≤ n)),
        if_neg (by omega : ¬ (1 ≤ j ∧ 2 * j ≤ n - 1)),
        if_neg (by omega : ¬ (1 ≤ j - 1 ∧ 2 * (j - 1) ≤ n - 2))]
      simp [hj0]
    · have hle : 2 * j ≤ n := by omega
      have hj : 1 ≤ j := by omega
      by_cases hone : j = 1
      · subst hone
        simp [evenTerm_rec_one hn, evenTerm_zero]
      · have hj2 : 2 ≤ j := by omega
        by_cases hdiag : 2 * j = n
        · simp [hj0, evenTerm_rec_diag hn hj hdiag]
        · by_cases hnear : 2 * j = n - 1
          · simp [hj0, evenTerm_rec_near hn hj2 hnear]
          · have hroom : 2 * j ≤ n - 2 := by omega
            simp [hj0, evenTerm_rec_room n j hn hj2 hroom]

theorem C_one : C 1 = 0 := by
  decide

theorem C_two : C 2 = 1 := by
  decide

theorem C_rec (n : ℕ) (hn : 3 ≤ n) : C n = (n - 1) * C (n - 1) + C (n - 2) := by
  conv_lhs => unfold C
  have hpoint : ∀ j ∈ range (n + 1),
      evenTerm n j =
        (n - 1) * evenTerm (n - 1) j + (if j = 0 then 0 else evenTerm (n - 2) (j - 1)) := by
    intro j _
    exact evenTerm_rec n j hn
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hfirst : ∑ j ∈ range (n + 1), evenTerm (n - 1) j = C (n - 1) := by
    rw [Finset.sum_range_succ]
    have hz : evenTerm (n - 1) n = 0 := by
      unfold evenTerm
      rw [if_neg (by omega : ¬ (1 ≤ n ∧ 2 * n ≤ n - 1))]
    rw [hz, add_zero]
    have hN : (n - 1) + 1 = n := by omega
    conv_lhs => rw [← hN]
    rfl
  have hsecond :
      ∑ j ∈ range (n + 1), (if j = 0 then 0 else evenTerm (n - 2) (j - 1)) = C (n - 2) := by
    rw [Finset.sum_range_succ']
    have hhead : (if (0 : ℕ) = 0 then 0 else evenTerm (n - 2) (0 - 1)) = 0 := by rw [if_pos rfl]
    rw [hhead, add_zero]
    have hbody : ∀ x ∈ range n,
        (if x + 1 = 0 then 0 else evenTerm (n - 2) (x + 1 - 1)) = evenTerm (n - 2) x := by
      intro x _
      rw [if_neg (by omega : x + 1 ≠ 0), show x + 1 - 1 = x by omega]
    rw [Finset.sum_congr rfl hbody]
    have hsplit : ∑ i ∈ range n, evenTerm (n - 2) i =
        ∑ i ∈ range (n - 1), evenTerm (n - 2) i + evenTerm (n - 2) (n - 1) := by
      have hN1 : (n - 1) + 1 = n := by omega
      conv_lhs => rw [← hN1]
      exact Finset.sum_range_succ (fun i => evenTerm (n - 2) i) (n - 1)
    rw [hsplit]
    have hz : evenTerm (n - 2) (n - 1) = 0 := by
      unfold evenTerm
      rw [if_neg (by omega : ¬ (1 ≤ n - 1 ∧ 2 * (n - 1) ≤ n - 2))]
    rw [hz, add_zero]
    have hN2 : (n - 2) + 1 = n - 1 := by omega
    conv_lhs => rw [← hN2]
    rfl
  rw [hfirst, hsecond]

theorem continuant_rec (n : ℕ) (hn : 2 ≤ n) :
    continuant n = (n - 1) * continuant (n - 1) + continuant (n - 2) := by
  have h2 : n - 2 + 2 = n := by omega
  have h1 : n - 2 + 1 = n - 1 := by omega
  conv_lhs => rw [← h2]
  simp [continuant, h1]

theorem continuant_eq (n : ℕ) (hn : 1 ≤ n) : continuant n = B (n - 1) + C n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => omega
    | 1 => decide
    | 2 => decide
    | n + 3 =>
      have hA : continuant (n + 3) = (n + 2) * continuant (n + 2) + continuant (n + 1) := by
        simpa using continuant_rec (n + 3) (by omega)
      have hB : B (n + 2) = (n + 2) * B (n + 1) + B n := B_rec (n + 2) (by omega)
      have hC : C (n + 3) = (n + 2) * C (n + 2) + C (n + 1) := by
        simpa [show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega] using
          C_rec (n + 3) (by omega)
      have h1 := ih (n + 2) (by omega) (by omega)
      have h2 := ih (n + 1) (by omega) (by omega)
      calc
        continuant (n + 3) = (n + 2) * continuant (n + 2) + continuant (n + 1) := hA
        _ = (n + 2) * (B (n + 1) + C (n + 2)) + (B n + C (n + 1)) := by
          rw [h1, h2]
          simp only [show n + 2 - 1 = n + 1 by omega, show n + 1 - 1 = n by omega]
        _ = B (n + 2) + C (n + 3) := by rw [hB, hC]; ring

theorem piece_zero (n : ℕ) : piece n 0 = 0 := by
  simp [piece, evenTerm]

theorem piece_even (n j : ℕ) : piece n (2 * j) = evenTerm n j := by
  unfold piece
  have hmod : (2 * j) % 2 = 0 := Nat.mul_mod_right 2 j
  rw [if_pos hmod, Nat.mul_div_cancel_left j (by decide : 0 < 2)]

theorem piece_odd (n k : ℕ) (hn : 1 ≤ n) : piece n (2 * k + 1) = T (n - 1) k := by
  unfold piece
  have hmod : (2 * k + 1) % 2 = 1 := by
    rw [Nat.add_mod, Nat.mul_mod_right]
  rw [if_neg (by omega : (2 * k + 1) % 2 ≠ 0), if_pos hn]
  have hdiv : (2 * k + 1) / 2 = k := by
    rw [Nat.mul_add_div (by decide : 0 < 2), Nat.div_eq_of_lt (by decide : 1 < 2)]
    simp
  rw [hdiv]

theorem even_step (n : ℕ) (f : ℕ → ℕ) :
    ∑ j ∈ range (n + 2), (if 2 * j ≤ n + 1 then f (2 * j) else 0) =
      ∑ j ∈ range (n + 1), (if 2 * j ≤ n then f (2 * j) else 0) +
        (if (n + 1) % 2 = 0 then f (n + 1) else 0) := by
  rw [Finset.sum_range_succ]
  have hlast : ¬ 2 * (n + 1) ≤ n + 1 := by omega
  rw [if_neg hlast, add_zero]
  by_cases hpar : (n + 1) % 2 = 0
  · set j0 : ℕ := (n + 1) / 2
    have h2 : 2 * j0 = n + 1 := by
      have h := Nat.div_add_mod (n + 1) 2
      omega
    have hj0 : j0 ∈ range (n + 1) := by rw [Finset.mem_range]; omega
    have hfun : ∀ j ∈ range (n + 1),
        (if 2 * j ≤ n + 1 then f (2 * j) else 0) =
          (if 2 * j ≤ n then f (2 * j) else 0) + (if j = j0 then f (n + 1) else 0) := by
      intro j _
      by_cases hje : j = j0
      · subst hje
        simp [h2]
      · have hne : 2 * j ≠ n + 1 := by
          intro heq
          apply hje
          omega
        by_cases hle : 2 * j ≤ n
        · simp [hje, hle, show 2 * j ≤ n + 1 by omega]
        · have hgt : ¬ 2 * j ≤ n + 1 := by
            intro h
            exact hne (by omega)
          simp [hje, hle, hgt]
    rw [Finset.sum_congr rfl hfun, Finset.sum_add_distrib, Finset.sum_ite_eq', hpar]
    simp [hj0]
  · have hodd : (n + 1) % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (n + 1) with h0 | h1
      · exact absurd h0 hpar
      · exact h1
    have hfun : ∀ j ∈ range (n + 1),
        (if 2 * j ≤ n + 1 then f (2 * j) else 0) =
          (if 2 * j ≤ n then f (2 * j) else 0) := by
      intro j _
      have hne : 2 * j ≠ n + 1 := by
        intro heq
        have : (n + 1) % 2 = 0 := by rw [← heq, Nat.mul_mod_right]
        exact hpar this
      by_cases hle : 2 * j ≤ n
      · simp [hle, show 2 * j ≤ n + 1 by omega]
      · have hgt : ¬ 2 * j ≤ n + 1 := by
          intro h
          exact hne (by omega)
        simp [hle, hgt]
    rw [Finset.sum_congr rfl hfun, hodd]
    simp

theorem odd_step (n : ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ range (n + 2), (if 2 * k + 1 ≤ n + 1 then f (2 * k + 1) else 0) =
      ∑ k ∈ range (n + 1), (if 2 * k + 1 ≤ n then f (2 * k + 1) else 0) +
        (if (n + 1) % 2 = 1 then f (n + 1) else 0) := by
  rw [Finset.sum_range_succ]
  have hlast : ¬ 2 * (n + 1) + 1 ≤ n + 1 := by omega
  rw [if_neg hlast, add_zero]
  by_cases hpar : (n + 1) % 2 = 1
  · set k0 : ℕ := (n + 1) / 2
    have h2 : 2 * k0 + 1 = n + 1 := by
      have h := Nat.div_add_mod (n + 1) 2
      omega
    have hk0 : k0 ∈ range (n + 1) := by rw [Finset.mem_range]; omega
    have hfun : ∀ k ∈ range (n + 1),
        (if 2 * k + 1 ≤ n + 1 then f (2 * k + 1) else 0) =
          (if 2 * k + 1 ≤ n then f (2 * k + 1) else 0) +
            (if k = k0 then f (n + 1) else 0) := by
      intro k _
      by_cases hke : k = k0
      · subst hke
        simp [h2]
      · have hne : 2 * k + 1 ≠ n + 1 := by
          intro heq
          apply hke
          omega
        by_cases hle : 2 * k + 1 ≤ n
        · simp [hke, hle, show 2 * k + 1 ≤ n + 1 by omega]
        · have hgt : ¬ 2 * k + 1 ≤ n + 1 := by
            intro h
            exact hne (by omega)
          simp [hke, hle, hgt]
    rw [Finset.sum_congr rfl hfun, Finset.sum_add_distrib, Finset.sum_ite_eq', hpar]
    simp [hk0]
  · have heven : (n + 1) % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (n + 1) with h0 | h1
      · exact h0
      · exact absurd h1 hpar
    have hfun : ∀ k ∈ range (n + 1),
        (if 2 * k + 1 ≤ n + 1 then f (2 * k + 1) else 0) =
          (if 2 * k + 1 ≤ n then f (2 * k + 1) else 0) := by
      intro k _
      have hne : 2 * k + 1 ≠ n + 1 := by
        intro heq
        have : (n + 1) % 2 = 1 := by
          rw [← heq, Nat.add_mod, Nat.mul_mod_right]
        exact hpar this
      by_cases hle : 2 * k + 1 ≤ n
      · simp [hle, show 2 * k + 1 ≤ n + 1 by omega]
      · have hgt : ¬ 2 * k + 1 ≤ n + 1 := by
          intro h
          exact hne (by omega)
        simp [hle, hgt]
    rw [Finset.sum_congr rfl hfun, heven]
    simp

theorem sum_even_odd (n : ℕ) (f : ℕ → ℕ) :
    ∑ r ∈ range (n + 1), f r =
      ∑ j ∈ range (n + 1), (if 2 * j ≤ n then f (2 * j) else 0) +
        ∑ k ∈ range (n + 1), (if 2 * k + 1 ≤ n then f (2 * k + 1) else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, even_step n f, odd_step n f]
    rcases Nat.mod_two_eq_zero_or_one (n + 1) with h | h
    · simp [h, add_assoc, add_comm]
    · simp [h, add_left_comm, add_comm]

theorem pieces_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ r ∈ range (n + 1), piece n r = continuant n := by
  rw [continuant_eq n hn, sum_even_odd]
  have heven : ∑ j ∈ range (n + 1), (if 2 * j ≤ n then piece n (2 * j) else 0) = C n := by
    have hfun : ∀ j ∈ range (n + 1),
        (if 2 * j ≤ n then piece n (2 * j) else 0) = evenTerm n j := by
      intro j _
      by_cases hle : 2 * j ≤ n
      · simp [hle, piece_even]
      · simp [hle, evenTerm]
    rw [Finset.sum_congr rfl hfun]
    rfl
  have hodd : ∑ k ∈ range (n + 1), (if 2 * k + 1 ≤ n then piece n (2 * k + 1) else 0) =
      B (n - 1) := by
    have hfun : ∀ k ∈ range (n + 1),
        (if 2 * k + 1 ≤ n then piece n (2 * k + 1) else 0) = T (n - 1) k := by
      intro k _
      by_cases hle : 2 * k + 1 ≤ n
      · simp [hle, piece_odd n k hn]
      · have hgt : n - 1 < 2 * k := by omega
        simp [hle, T_of_gt hgt]
    rw [Finset.sum_congr rfl hfun]
    rw [Finset.sum_range_succ, T_of_gt (by omega : n - 1 < 2 * n), add_zero]
    conv_rhs => unfold B
    have hN : (n - 1) + 1 = n := by omega
    conv_lhs => rw [← hN]
    rfl
  rw [heven, hodd]
  exact Nat.add_comm _ _


/-! ## The counting identity -/

def tm (m k : ℕ) : ℕ :=
  k.factorial * Nat.choose ((m + k + 1) / 2) k * Nat.choose ((m + k) / 2) k

lemma fact_choose (a j : ℕ) (h : j ≤ a) :
    (a - j).factorial * Nat.choose a j = a.factorial / j.factorial := by
  have h1 := Nat.choose_mul_factorial_mul_factorial h
  symm
  apply Nat.div_eq_of_eq_mul_left (Nat.factorial_pos j)
  rw [← h1]; ring

lemma piece_eq_tm (m k : ℕ) (hk : k ≤ m) : piece (m + 1) (m + 1 - k) = tm m k := by
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' (m + 1 - k)
  · rw [hj, piece_even]
    have hj1 : 1 ≤ j := by omega
    obtain rfl : k = m + 1 - 2 * j := by omega
    unfold evenTerm tm
    rw [if_pos ⟨hj1, by omega⟩]
    have e0 : (m + (m + 1 - 2 * j) + 1) / 2 = m + 1 - j := by omega
    have e0' : (m + (m + 1 - 2 * j)) / 2 = m - j := by omega
    have e1 : Nat.choose (m + 1 - j) (m + 1 - 2 * j) = Nat.choose (m + 1 - j) j := by
      rw [← Nat.choose_symm (n := m + 1 - j) (k := j) (by omega)]
      congr 1; omega
    have e2 : Nat.choose (m - j) (m + 1 - 2 * j) = Nat.choose (m - j) (j - 1) := by
      rw [← Nat.choose_symm (n := m - j) (k := j - 1) (by omega)]
      congr 1; omega
    have e3 : m + 1 - j - 1 = m - j := by omega
    rw [e0, e0', e1, e2, e3]
  · rw [hj, piece_odd _ _ (by omega)]
    obtain rfl : k = m - 2 * j := by omega
    rw [Nat.add_sub_cancel, T_of_le (by omega)]
    unfold tm
    have e0 : (m + (m - 2 * j) + 1) / 2 = m - j := by omega
    have e0' : (m + (m - 2 * j)) / 2 = m - j := by omega
    have e1 : Nat.choose (m - j) (m - 2 * j) = Nat.choose (m - j) j := by
      rw [← Nat.choose_symm (n := m - j) (k := j) (by omega)]
      congr 1; omega
    rw [e0, e0', e1]
    have := fact_choose (m - j) j (by omega)
    have e4 : m - j - j = m - 2 * j := by omega
    rw [e4] at this
    rw [mul_assoc, ← this]; ring

theorem sum_tm (m : ℕ) : ∑ k ∈ range (m + 1), tm m k = continuant (m + 1) := by
  rw [← pieces_sum (m + 1) (by omega), sum_range_succ' _ (m + 1), piece_zero, add_zero]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < m + 1 := Finset.mem_range.mp hk
  have := piece_eq_tm m (m - k) (by omega)
  rw [show m + 1 - (m - k) = k + 1 by omega] at this
  rw [this]
  simp

theorem card_rw (m : ℕ) :
    Fintype.card (RookWalk m) = 2 * (m + 1).factorial * ∑ k ∈ range (m + 1), tm m k := by
  rw [Fintype.card_sigma, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun k => 2 * (m + 1).factorial * tm m k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_perm, Fintype.card_fin,
    Fintype.card_finset_len]
  unfold tm
  ring

end OMA.A096121

open OMA.A096121 OMA.S_oeis_a096121 in
theorem OMA.solution : type_of% @OMA.S_oeis_a096121.main := by
  intro m
  rw [card_rw, sum_tm]
