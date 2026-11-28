import OMAReductions.R_mse_1416221_R1
import Mathlib

/-! Step mse-1416221.R1.H1: if 2^q - 1 is prime then Reix's sequence returns to its seed:
S i = 9^(2^i) + 9^(-2^i) and Fermat for the base 3 gives 9^(2^(q-1)) = 3^(M+1) = 9. -/

namespace OMA.P1416

theorem closed_form (q : ℕ) [Fact (mersenne q).Prime] (h9 : (9 : ZMod (mersenne q)) ≠ 0) (i : ℕ) :
    OMA.S_mse_1416221.S q i = (9 : ZMod (mersenne q)) ^ (2 ^ i) + ((9 : ZMod (mersenne q))⁻¹) ^ (2 ^ i) := by
  induction i with
  | zero => simp [OMA.S_mse_1416221.S]
  | succ m ih =>
    rw [OMA.S_mse_1416221.S, ih]
    have hab : (9 : ZMod (mersenne q)) ^ (2 ^ m) * ((9 : ZMod (mersenne q))⁻¹) ^ (2 ^ m) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ h9, one_pow]
    have e1 : (9 : ZMod (mersenne q)) ^ (2 ^ (m + 1)) = ((9 : ZMod (mersenne q)) ^ (2 ^ m)) ^ 2 := by
      rw [← pow_mul, pow_succ]
    have e2 : ((9 : ZMod (mersenne q))⁻¹) ^ (2 ^ (m + 1)) = (((9 : ZMod (mersenne q))⁻¹) ^ (2 ^ m)) ^ 2 := by
      rw [← pow_mul, pow_succ]
    rw [e1, e2]
    linear_combination (2 : ZMod (mersenne q)) * hab

theorem solution_aux : ∀ q : ℕ, q.Prime → 2 < q → (mersenne q).Prime →
    OMA.S_mse_1416221.S q (q - 1) = OMA.S_mse_1416221.S q 0 := by
  intro q hq hq2 hM
  have : Fact (mersenne q).Prime := ⟨hM⟩
  have hq8 : 8 ≤ 2 ^ q := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq2
  have hMge : 7 ≤ mersenne q := by unfold mersenne; omega
  have h3 : (3 : ZMod (mersenne q)) ≠ 0 := by
    intro h
    have : mersenne q ∣ 3 := by
      have := (ZMod.natCast_eq_zero_iff 3 (mersenne q)).mp (by exact_mod_cast h)
      exact this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h9 : (9 : ZMod (mersenne q)) ≠ 0 := by
    have : (9 : ZMod (mersenne q)) = 3 * 3 := by norm_num
    rw [this]; exact mul_ne_zero h3 h3
  have hferm : (3 : ZMod (mersenne q)) ^ (mersenne q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h3
  have hpow : (9 : ZMod (mersenne q)) ^ (2 ^ (q - 1)) = 9 := by
    have e : (9 : ZMod (mersenne q)) = 3 ^ 2 := by norm_num
    have hq1 : 2 * 2 ^ (q - 1) = (mersenne q - 1) + 2 := by
      have : 2 * 2 ^ (q - 1) = 2 ^ q := by
        rw [← pow_succ']; congr 1; omega
      unfold mersenne at hMge ⊢; omega
    rw [e, ← pow_mul, hq1, pow_add, hferm, one_mul]
  rw [closed_form q h9, closed_form q h9, inv_pow, hpow]
  simp

end OMA.P1416

theorem OMA.solution : OMA.R_mse_1416221_R1.H1 := OMA.P1416.solution_aux
