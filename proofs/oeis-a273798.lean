import OMAStatements.S_oeis_a273798
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a273798.main := by
  rintro x ⟨m, p, hp, hlt, rfl⟩
  have hx0 : 2 ^ m * p ≠ 0 := mul_ne_zero (pow_ne_zero m (by norm_num)) hp.ne_zero
  refine ⟨Nat.one_le_iff_ne_zero.mpr hx0, ?_⟩
  have hm : m ≤ (2 ^ m * p).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hx0).1 (dvd_mul_right _ _)
  have hpow : 2 ^ m ≤ 2 ^ (2 ^ m * p).factorization 2 := Nat.pow_le_pow_right (by norm_num) hm
  have hle : OMA.S_oeis_a273798.oddPart (2 ^ m * p) ≤ p := by
    unfold OMA.S_oeis_a273798.oddPart
    calc 2 ^ m * p / 2 ^ (2 ^ m * p).factorization 2
        ≤ 2 ^ m * p / 2 ^ m := Nat.div_le_div_left hpow (by positivity)
      _ = p := Nat.mul_div_cancel_left p (by positivity)
  calc OMA.S_oeis_a273798.oddPart (2 ^ m * p) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hle 2
    _ = p * p := by ring
    _ ≤ 2 ^ m * p := Nat.mul_le_mul_right p hlt.le
