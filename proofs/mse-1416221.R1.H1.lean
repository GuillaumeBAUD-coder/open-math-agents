import OMAReductions.R_mse_1416221_R1
import Mathlib

open OMA.S_mse_1416221

theorem OMA.solution : OMA.R_mse_1416221_R1.H1 := by
  intro q _ hq hp
  let _ : Fact (mersenne q).Prime := ⟨hp⟩
  have hp3 : 3 < mersenne q := by
    calc
      3 = mersenne 2 := by decide +kernel
      _ < mersenne q := strictMono_mersenne hq
  have h3 : (3 : ZMod (mersenne q)) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 3 (mersenne q)).mp h
    exact (not_le_of_gt hp3) (Nat.le_of_dvd (by decide) hd)
  let u : ZMod (mersenne q) := 9
  have hu3 : u = (3 : ZMod (mersenne q)) ^ 2 := by norm_num [u]
  have hu : u ≠ 0 := hu3.symm ▸ pow_ne_zero _ h3
  have hS (i : ℕ) : S q i = u ^ (2 ^ i) + (u⁻¹) ^ (2 ^ i) := by
    induction i with
    | zero => simp [S, u]
    | succ i hi =>
      rw [S, hi, pow_succ 2 i, pow_mul, pow_mul]
      have hprod : u ^ (2 ^ i) * (u⁻¹) ^ (2 ^ i) = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hu, one_pow]
      linear_combination 2 * hprod
  let e : ℕ := 2 ^ (q - 1) - 1
  have hE : 2 ^ (q - 1) = e + 1 := by
    have : 0 < (2 : ℕ) ^ (q - 1) := by positivity
    dsimp [e]
    omega
  have hq' : q - 1 + 1 = q := by omega
  have hqpow : 2 ^ q = 2 ^ (q - 1) * 2 := by
    rw [← pow_succ, hq']
  have he : 2 * e = mersenne q - 1 := by
    have hs := succ_mersenne q
    omega
  have hunit : u ^ e = 1 := by
    rw [hu3, ← pow_mul, he]
    exact ZMod.pow_card_sub_one_eq_one h3
  have hinv : (u⁻¹) ^ e = 1 := by rw [inv_pow, hunit, inv_one]
  rw [hS, hS, hE, pow_succ, pow_succ, hunit, hinv]
  simp