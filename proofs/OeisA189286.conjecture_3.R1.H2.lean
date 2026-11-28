import OMAReductions.R_OeisA189286_conjecture_3_R1
import Mathlib

/-!
# Power-of-two parity step for OEIS A189286 (`H2`)

Proves `OeisA189286.conjecture_3.R1.H2`: whenever `n = 2 ^ k` (`0 < n`) and `a n = 8 * m`,
`m` is odd, by showing `¬ 16 ∣ sNat (2 ^ k)` via Legendre's formula and reflection symmetry
in the defining binomial convolution.
-/

namespace OeisA189286

private def tNat (k : ℕ) : ℕ := (6 * k).choose (3 * k) * (3 * k).choose k

private def sNat (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), tNat k * tNat (n - k)

private lemma tNat_zero : tNat 0 = 1 := by decide

private lemma tNat_pos (k : ℕ) : 0 < tNat k :=
  Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))

private lemma sNat_pos (n : ℕ) : 0 < sNat n :=
  Finset.sum_pos (fun k _ => Nat.mul_pos (tNat_pos k) (tNat_pos (n - k)))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩

private lemma denom_pos {n : ℕ} (hn : 0 < n) : 0 < (2 * n - 1) * (3 * n).choose n :=
  Nat.mul_pos (by omega) (Nat.choose_pos (by omega))

private lemma a_eq_div_nat {n : ℕ} (hn : 0 < n) :
    a n = (sNat n : ℚ) / (((2 * n - 1) * (3 * n).choose n : ℕ) : ℚ) := by
  unfold a sNat tTerm
  have hsub : ((2 * n - 1 : ℕ) : ℚ) = 2 * (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  simp only [tNat, Nat.cast_sum, Nat.cast_mul, hsub]

private lemma tNat_mul_factorials (k : ℕ) :
    tNat k * (3 * k).factorial * (2 * k).factorial * k.factorial = (6 * k).factorial := by
  have h1 : (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial = (6 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 6 * k) (k := 3 * k) (by omega)
    rwa [show 6 * k - 3 * k = 3 * k by omega] at this
  have h2 : (3 * k).choose k * k.factorial * (2 * k).factorial = (3 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 3 * k) (k := k) (by omega)
    rwa [show 3 * k - k = 2 * k by omega] at this
  calc
    tNat k * (3 * k).factorial * (2 * k).factorial * k.factorial
        = (6 * k).choose (3 * k) * (3 * k).factorial *
            ((3 * k).choose k * k.factorial * (2 * k).factorial) := by
            unfold tNat; ring
    _ = (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial := by rw [h2]
    _ = (6 * k).factorial := h1

private def s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

private lemma padicValNat_two_fac (n : ℕ) : padicValNat 2 n.factorial = n - s2 n := by
  have := sub_one_mul_padicValNat_factorial (p := 2) n
  simpa [s2] using this

private lemma s2_le_self (n : ℕ) : s2 n ≤ n :=
  Nat.digit_sum_le 2 n

private lemma s2_mul_two (n : ℕ) : s2 (2 * n) = s2 n := by
  by_cases hn : n = 0
  · subst hn; simp [s2]
  · unfold s2
    rw [Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2 * n)]
    have h1 : (2 * n) % 2 = 0 := by omega
    have h2 : (2 * n) / 2 = n := by omega
    simp [h1, h2]

private lemma s2_pow_two (k : ℕ) : s2 (2 ^ k) = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ', s2_mul_two, ih]

private lemma s2_pos_of_pos {n : ℕ} (hn : 0 < n) : 1 ≤ s2 n := by
  have hne : n ≠ 0 := hn.ne'
  have hnil : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hne
  have hlast : (Nat.digits 2 n).getLast hnil ≠ 0 := Nat.getLast_digit_ne_zero 2 hne
  have hmem : (Nat.digits 2 n).getLast hnil ∈ Nat.digits 2 n := List.getLast_mem hnil
  exact List.sum_pos_iff_exists_pos_nat.mpr ⟨_, hmem, Nat.pos_of_ne_zero hlast⟩

private lemma padicValNat_two_tNat (k : ℕ) : padicValNat 2 (tNat k) = 2 * s2 k := by
  have hfac := tNat_mul_factorials k
  have hT_pos : 0 < tNat k := tNat_pos k
  have hv := congrArg (padicValNat 2) hfac
  simp only [padicValNat.mul, hT_pos.ne', Nat.factorial_ne_zero, mul_ne_zero_iff, ne_eq,
    not_false_eq_true, and_self, padicValNat_two_fac] at hv
  have h6 : s2 (6 * k) = s2 (3 * k) := by rw [show 6 * k = 2 * (3 * k) by ring, s2_mul_two]
  have h2 : s2 (2 * k) = s2 k := s2_mul_two k
  have hle6 := s2_le_self (6 * k)
  have hle3 := s2_le_self (3 * k)
  have hle2 := s2_le_self (2 * k)
  have hle1 := s2_le_self k
  omega

private lemma sum_sym_decomp (h : ℕ) (hh : 0 < h) (f : ℕ → ℕ)
    (hsym : ∀ j ≤ 2 * h, f (2 * h - j) = f j) :
    ∑ j ∈ Finset.range (2 * h + 1), f j =
      2 * f 0 + f h + 2 * ∑ j ∈ Finset.Ico 1 h, f j := by
  have hsplit : ∑ j ∈ Finset.range (2 * h + 1), f j =
      (∑ j ∈ Finset.range h, f j) + (∑ j ∈ Finset.range h, f (h + j)) + f (2 * h) := by
    rw [Finset.sum_range_succ, show 2 * h = h + h by ring, Finset.sum_range_add]
  have hleft : ∑ j ∈ Finset.range h, f j = f 0 + ∑ j ∈ Finset.Ico 1 h, f j := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hh]
  have hright : ∑ j ∈ Finset.range h, f (h + j) = f h + ∑ j ∈ Finset.Ico 1 h, f (h + j) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hh]
    simp
  have hpair : ∑ j ∈ Finset.Ico 1 h, f (h + j) = ∑ j ∈ Finset.Ico 1 h, f j := by
    apply Finset.sum_nbij (fun j => h - j)
    · intro a ha
      simp only [Finset.mem_Ico] at ha ⊢
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb
      dsimp only at hab
      omega
    · intro b hb
      simp only [Finset.mem_coe, Finset.mem_Ico] at hb
      exact ⟨h - b, Finset.mem_coe.mpr (Finset.mem_Ico.mpr ⟨by omega, by omega⟩), by dsimp only; omega⟩
    · intro a ha
      simp only [Finset.mem_Ico] at ha
      rw [show h + a = 2 * h - (h - a) by omega]
      exact hsym (h - a) (by omega)
  have hf2h : f (2 * h) = f 0 := by
    have := hsym 0 (by omega)
    simpa using this
  rw [hsplit, hleft, hright, hpair, hf2h]
  ring

private lemma not_dvd_16_sNat_pow_two (k : ℕ) : ¬ 16 ∣ sNat (2 ^ k) := by
  cases k with
  | zero =>
    show ¬ 16 ∣ sNat 1
    decide
  | succ r =>
    let h : ℕ := 2 ^ r
    have hh : 0 < h := by positivity
    have hpow : 2 ^ (r + 1) = 2 * h := by dsimp [h]; rw [pow_succ']
    let f : ℕ → ℕ := fun j => tNat j * tNat (2 * h - j)
    have hsym : ∀ j ≤ 2 * h, f (2 * h - j) = f j := by
      intro j hj
      dsimp [f]
      rw [Nat.sub_sub_self hj, mul_comm]
    have hdecomp : sNat (2 ^ (r + 1)) = 2 * f 0 + f h + 2 * ∑ j ∈ Finset.Ico 1 h, f j := by
      unfold sNat
      rw [hpow]
      exact sum_sym_decomp h hh f hsym
    have hfh : 16 ∣ f h := by
      have hne : f h ≠ 0 := mul_ne_zero (tNat_pos h).ne' (tNat_pos _).ne'
      rw [show (16 : ℕ) = 2 ^ 4 by decide]
      apply (padicValNat_dvd_iff_le (p := 2) hne).2
      dsimp [f]
      rw [show 2 * h - h = h by omega, padicValNat.mul (tNat_pos h).ne' (tNat_pos h).ne',
        padicValNat_two_tNat]
      have hs : s2 h = 1 := s2_pow_two r
      omega
    have hsum16 : 16 ∣ 2 * ∑ j ∈ Finset.Ico 1 h, f j := by
      apply dvd_mul_of_dvd_right
      apply Finset.dvd_sum
      intro j hj
      simp only [Finset.mem_Ico] at hj
      have hj1 : 0 < j := by omega
      have hj2 : 0 < 2 * h - j := by omega
      have hne : f j ≠ 0 := mul_ne_zero (tNat_pos j).ne' (tNat_pos _).ne'
      rw [show (16 : ℕ) = 2 ^ 4 by decide]
      apply (padicValNat_dvd_iff_le (p := 2) hne).2
      dsimp [f]
      rw [padicValNat.mul (tNat_pos j).ne' (tNat_pos _).ne', padicValNat_two_tNat,
        padicValNat_two_tNat]
      have hs1 := s2_pos_of_pos hj1
      have hs2 := s2_pos_of_pos hj2
      omega
    have hf0 : ¬ 16 ∣ 2 * f 0 := by
      have hf0_eq : 2 * f 0 = 2 * tNat (2 * h) := by
        dsimp [f]
        simp [tNat_zero]
      rw [hf0_eq, show (16 : ℕ) = 2 ^ 4 by decide]
      have hne : 2 * tNat (2 * h) ≠ 0 := mul_ne_zero (by decide) (tNat_pos _).ne'
      rw [padicValNat_dvd_iff_le (p := 2) hne]
      rw [padicValNat.mul (by decide) (tNat_pos _).ne', padicValNat_two_tNat,
        show padicValNat 2 2 = 1 from padicValNat.self (by decide), ← hpow,
        s2_pow_two]
      omega
    intro hdvd
    rw [hdecomp, add_assoc] at hdvd
    exact hf0 ((Nat.dvd_add_left (dvd_add hfh hsum16)).mp hdvd)

end OeisA189286

open OeisA189286 in
theorem OMA.solution : OMA.R_OeisA189286_conjecture_3_R1.H2 := by
  rintro n hn m hm ⟨k, rfl⟩
  let D := (2 * 2 ^ k - 1) * (3 * 2 ^ k).choose (2 ^ k)
  have hd : D ≠ 0 := (denom_pos hn).ne'
  rw [a_eq_div_nat hn] at hm
  have heq := (div_eq_iff (Nat.cast_ne_zero.mpr hd)).1 hm
  have heq' : (sNat (2 ^ k) : ℤ) = 8 * m * (D : ℕ) := by exact_mod_cast heq
  have habs : sNat (2 ^ k) = 8 * m.natAbs * D := by
    simpa [Int.natAbs_mul] using congrArg Int.natAbs heq'
  by_contra hnot
  obtain ⟨t, ht⟩ := Int.not_odd_iff_even.mp hnot
  have h2m : (2 : ℤ) ∣ m := ⟨t, by omega⟩
  have h2abs : 2 ∣ m.natAbs := by exact_mod_cast Int.dvd_natAbs.mpr h2m
  obtain ⟨q, hq⟩ := h2abs
  have h16 : 16 ∣ sNat (2 ^ k) := by
    rw [habs, hq]
    exact ⟨q * D, by ring⟩
  exact not_dvd_16_sNat_pow_two k h16
