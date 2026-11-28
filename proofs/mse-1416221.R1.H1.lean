import OMAReductions.R_mse_1416221_R1
import Mathlib

/-! The proved direction of Reix's test for Mersenne numbers: if `2 ^ q - 1` is prime then the
sequence `S` returns to its seed at step `q - 1`. -/

namespace OMA.ReixMersenne

open OMA.S_mse_1416221

/-- The second-order identity behind the recurrence. -/
private lemma sq_add_inv_sq {K : Type*} [Field K] {x : K} (hx : x ≠ 0) :
    (x + x⁻¹) ^ 2 - 2 = x ^ 2 + (x ^ 2)⁻¹ := by
  have h2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  field_simp
  ring

/-- `9` is invertible modulo a Mersenne prime with odd prime exponent. -/
private lemma nine_ne_zero (q : ℕ) (hq2 : 2 < q) [Fact (mersenne q).Prime] :
    (9 : ZMod (mersenne q)) ≠ 0 := by
  have hM7 : 7 ≤ mersenne q := by
    have h1 : 2 ^ 3 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [mersenne]; omega
  have h3 : (3 : ZMod (mersenne q)) ≠ 0 := by
    intro h
    have hdvd : mersenne q ∣ 3 := (ZMod.natCast_eq_zero_iff 3 (mersenne q)).mp h
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have h9 : (9 : ZMod (mersenne q)) = 3 ^ 2 := by norm_num
  rw [h9]
  exact pow_ne_zero 2 h3

/-- The closed form of the sequence: `S q i = 9 ^ 2 ^ i + (9 ^ 2 ^ i)⁻¹`. -/
private lemma S_closed (q : ℕ) (hq2 : 2 < q) [Fact (mersenne q).Prime] (i : ℕ) :
    S q i = (9 : ZMod (mersenne q)) ^ 2 ^ i + ((9 : ZMod (mersenne q)) ^ 2 ^ i)⁻¹ := by
  induction i with
  | zero => simp [S]
  | succ n ih =>
    rw [S, ih]
    have hx : (9 : ZMod (mersenne q)) ^ 2 ^ n ≠ 0 := pow_ne_zero _ (nine_ne_zero q hq2)
    have hpow : (9 : ZMod (mersenne q)) ^ 2 ^ (n + 1) =
        ((9 : ZMod (mersenne q)) ^ 2 ^ n) ^ 2 := by
      rw [← pow_mul]
      congr 1
    rw [hpow, sq_add_inv_sq hx]

/-- The key power: `9 ^ 2 ^ (q - 1) = 9` modulo a Mersenne prime. -/
private lemma nine_pow (q : ℕ) (hq2 : 2 < q) [Fact (mersenne q).Prime] :
    (9 : ZMod (mersenne q)) ^ 2 ^ (q - 1) = 9 := by
  have hq3 : 3 ≤ q := by omega
  have h2q : 2 ^ q = 2 * 2 ^ (q - 1) := by
    conv_lhs => rw [show q = q - 1 + 1 by omega]
    rw [pow_succ']
  have hM : mersenne q = 2 ^ q - 1 := rfl
  have hpos : 0 < 2 ^ (q - 1) := pow_pos (by norm_num) _
  have hMeq : mersenne q - 1 = 2 * (2 ^ (q - 1) - 1) := by
    rw [hM, h2q]; omega
  have hexp : 2 ^ (q - 1) - 1 = (mersenne q - 1) / 2 := by
    rw [hMeq]; omega
  have hodd : mersenne q % 2 = 1 := by
    rw [hM, h2q]; omega
  have htwo : 2 * ((mersenne q - 1) / 2) = mersenne q - 1 := by omega
  have h3 : (3 : ZMod (mersenne q)) ≠ 0 := by
    have hM7 : 7 ≤ mersenne q := by
      have h1 : 2 ^ 3 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [mersenne]; omega
    intro h
    have hdvd : mersenne q ∣ 3 := (ZMod.natCast_eq_zero_iff 3 (mersenne q)).mp h
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  calc (9 : ZMod (mersenne q)) ^ 2 ^ (q - 1)
      = (9 : ZMod (mersenne q)) ^ (2 ^ (q - 1) - 1 + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 ^ (q - 1))]
    _ = (9 : ZMod (mersenne q)) ^ (2 ^ (q - 1) - 1) * (9 : ZMod (mersenne q)) ^ 1 := by
        rw [pow_add]
    _ = (3 : ZMod (mersenne q)) ^ (mersenne q - 1) * 9 := by
        rw [hexp]
        have h9 : (9 : ZMod (mersenne q)) = 3 ^ 2 := by norm_num
        rw [h9, ← pow_mul, htwo, pow_one]
    _ = 1 * 9 := by rw [ZMod.pow_card_sub_one_eq_one h3]
    _ = 9 := by ring

end OMA.ReixMersenne

theorem OMA.solution : OMA.R_mse_1416221_R1.H1 := by
  intro q hq hq2 hprim
  haveI : Fact (mersenne q).Prime := ⟨hprim⟩
  rw [OMA.ReixMersenne.S_closed q hq2 (q - 1), OMA.ReixMersenne.nine_pow q hq2]
  simp [OMA.S_mse_1416221.S]
