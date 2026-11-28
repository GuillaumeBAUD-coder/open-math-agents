import OMAStatements.S_mo_380394

/-!
# MathOverflow 380394: the 2-adic valuation formula for the modified Catalan sequence

MathOverflow question 380394 (T. Amdeberhan) asks whether, for `w 0 = 1` and
`w (n + 1) = sum_{i = 0}^{n} w i ^ 2 * w (n - i) ^ 2`, the identity
`nu_2 (w n) = (C n mod 2) + 2 * s(n + 1) - 3` holds, where `nu_2` is the 2-adic valuation, `s`
the binary digit sum and `C n` the Catalan number. The answer on the page says that it does not:
the smallest failure is `n = 30`.

We refute `main` at `n = 30`. The residues of the sequence modulo `2048` are computed below, one
from the recurrence at a time; the value at `30` is `1024`, so `nu_2 (w 30) = 10`. On the other
hand `s(31) = 5` and `C 30 mod 2` is `0` or `1`, so the right hand side is `7` or `8`, and the
identity fails.
-/

namespace OMA.P380394

open OMA.S_mo_380394

set_option maxHeartbeats 1000000 in
theorem disproof_core : ¬ (type_of% @OMA.S_mo_380394.main) := by
  intro h
  have h0 : (w 0 : ZMod 2048) = 1 := by rw [w]; simp
  have h1 : (w 1 : ZMod 2048) = 1 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0]
    decide
  have h2 : (w 2 : ZMod 2048) = 2 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1]
    decide
  have h3 : (w 3 : ZMod 2048) = 9 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2]
    decide
  have h4 : (w 4 : ZMod 2048) = 170 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3]
    decide
  have h5 : (w 5 : ZMod 2048) = 634 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4]
    decide
  have h6 : (w 6 : ZMod 2048) = 152 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5]
    decide
  have h7 : (w 7 : ZMod 2048) = 393 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6]
    decide
  have h8 : (w 8 : ZMod 2048) = 1162 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7]
    decide
  have h9 : (w 9 : ZMod 2048) = 834 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8]
    decide
  have h10 : (w 10 : ZMod 2048) = 1528 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
    decide
  have h11 : (w 11 : ZMod 2048) = 1530 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
    decide
  have h12 : (w 12 : ZMod 2048) = 1656 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    decide
  have h13 : (w 13 : ZMod 2048) = 1080 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
    decide
  have h14 : (w 14 : ZMod 2048) = 608 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
    decide
  have h15 : (w 15 : ZMod 2048) = 1545 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
    decide
  have h16 : (w 16 : ZMod 2048) = 650 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
    decide
  have h17 : (w 17 : ZMod 2048) = 1442 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
    decide
  have h18 : (w 18 : ZMod 2048) = 1528 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
    decide
  have h19 : (w 19 : ZMod 2048) = 1730 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
    decide
  have h20 : (w 20 : ZMod 2048) = 1240 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
    decide
  have h21 : (w 21 : ZMod 2048) = 1176 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
    decide
  have h22 : (w 22 : ZMod 2048) = 864 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
    decide
  have h23 : (w 23 : ZMod 2048) = 122 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
    decide
  have h24 : (w 24 : ZMod 2048) = 1656 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
    decide
  have h25 : (w 25 : ZMod 2048) = 152 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
    decide
  have h26 : (w 26 : ZMod 2048) = 1888 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
    decide
  have h27 : (w 27 : ZMod 2048) = 696 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26]
    decide
  have h28 : (w 28 : ZMod 2048) = 864 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
    decide
  have h29 : (w 29 : ZMod 2048) = 1888 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
    decide
  have h30 : (w 30 : ZMod 2048) = 1024 := by
    rw [w]
    push_cast
    repeat rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Fin.isValue, Nat.reduceSub]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
    decide
  have hmod : w 30 % 2048 = 1024 := by
    have h1 : ((w 30 : ℕ) : ZMod 2048) = ((1024 : ℕ) : ZMod 2048) := h30
    rw [ZMod.natCast_eq_natCast_iff'] at h1
    simpa using h1
  have hdvd : 2 ^ 10 ∣ w 30 := by
    have h1024 : (2 : ℕ) ^ 10 = 1024 := by norm_num
    rw [h1024, Nat.dvd_iff_mod_eq_zero]
    calc w 30 % 1024 = w 30 % 2048 % 1024 := (Nat.mod_mod_of_dvd (w 30) (by norm_num)).symm
      _ = 1024 % 1024 := by rw [hmod]
      _ = 0 := by norm_num
  have hndvd : ¬ ((2 : ℕ) ^ 11 ∣ w 30) := by
    have h2048 : (2 : ℕ) ^ 11 = 2048 := by norm_num
    rw [h2048, Nat.dvd_iff_mod_eq_zero, hmod]
    norm_num
  have hne : w 30 ≠ 0 := by
    intro hzero
    rw [hzero] at hmod
    norm_num at hmod
  have hval : padicValNat 2 (w 30) = 10 := by
    have h1 : 10 ≤ padicValNat 2 (w 30) := (padicValNat_dvd_iff_le hne).1 hdvd
    have h2 : ¬ (11 ≤ padicValNat 2 (w 30)) :=
      fun hle => hndvd ((padicValNat_dvd_iff_le hne).2 hle)
    omega
  have hdig : (Nat.digits 2 31).sum = 5 := by decide
  have h30eq := h 30
  rw [hval] at h30eq
  rw [show Nat.digits 2 (30 + 1) = Nat.digits 2 31 from rfl, hdig] at h30eq
  have hlt : ((catalan 30 % 2 : ℕ) : ℤ) < 2 := by
    have h2 : catalan 30 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega
  omega

end OMA.P380394

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_380394.main) := OMA.P380394.disproof_core
