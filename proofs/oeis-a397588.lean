import OMAStatements.S_oeis_a397588
import Mathlib

namespace OMA.A397588Proof

open PowerSeries

theorem coeff_sq_zmod2 (B : PowerSeries (ZMod 2)) (n : ℕ) :
    coeff n (B ^ 2) = if 2 ∣ n then coeff (n / 2) B else 0 := by
  rw [sq, coeff_mul_eq_coeff_trunc_mul_trunc B B (Nat.lt_succ_self n), ← Polynomial.coe_mul,
    ← sq, ← ZMod.expand_card, Polynomial.coeff_coe, Polynomial.coeff_expand (by norm_num)]
  split_ifs with h
  · rw [coeff_trunc, if_pos (by omega)]
  · rfl

theorem key (A : PowerSeries ℤ)
    (hA : A = PowerSeries.X + PowerSeries.derivative ℤ (PowerSeries.X * A ^ 2)) (n : ℕ) :
    ((A.coeff n : ℤ) : ZMod 2) = (if n = 1 then 1 else 0) +
      ((n : ZMod 2) + 1) * coeff n ((PowerSeries.map (Int.castRingHom (ZMod 2)) A) ^ 2) := by
  have h := congrArg (coeff n) hA
  rw [map_add, coeff_derivative, coeff_succ_X_mul, coeff_X] at h
  rw [← map_pow, coeff_map]
  conv_lhs => rw [h]
  push_cast
  simp
  ring

theorem rec (A : PowerSeries ℤ)
    (hA : A = PowerSeries.X + PowerSeries.derivative ℤ (PowerSeries.X * A ^ 2)) (n : ℕ) :
    ((A.coeff n : ℤ) : ZMod 2) = (if n = 1 then 1 else 0) +
      ((n : ZMod 2) + 1) * (if 2 ∣ n then ((A.coeff (n / 2) : ℤ) : ZMod 2) else 0) := by
  rw [key A hA n, coeff_sq_zmod2, coeff_map]
  rfl

theorem pow2_odd {n : ℕ} (hn : n % 2 = 1) (h1 : n ≠ 1) : ¬ ∃ k : ℕ, n = 2 ^ k := by
  rintro ⟨k, rfl⟩
  rcases k with _ | k
  · simp at h1
  · rw [pow_succ] at hn; omega

theorem pow2_even {m : ℕ} : (∃ k : ℕ, 2 * m = 2 ^ k) ↔ (1 ≤ m ∧ ∃ k : ℕ, m = 2 ^ k) := by
  constructor
  · rintro ⟨k, hk⟩
    rcases k with _ | k
    · omega
    · refine ⟨?_, k, ?_⟩
      · have := Nat.one_le_two_pow (n := k); rw [pow_succ] at hk; omega
      · rw [pow_succ] at hk; omega
  · rintro ⟨_, k, rfl⟩
    exact ⟨k + 1, by rw [pow_succ]; ring⟩

theorem main_proof : type_of% @OMA.S_oeis_a397588.main := by
  intro A _ hA n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [rec A hA n]
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have hm : 1 ≤ m := by omega
      have h2 : ((2 * m : ℕ) : ZMod 2) = 0 := by
        push_cast; rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]
      rw [h2, if_neg (by omega), if_pos (dvd_mul_right 2 m), Nat.mul_div_cancel_left m two_pos,
        zero_add, zero_add, one_mul, ih m (by omega) hm, pow2_even]
      simp [hm]
    · have h2 : ((2 * m + 1 : ℕ) : ZMod 2) + 1 = 0 := by
        push_cast; rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]; rfl
      rw [h2, zero_mul, add_zero]
      by_cases h1 : 2 * m + 1 = 1
      · rw [if_pos h1, h1]; exact ⟨fun _ => ⟨0, rfl⟩, fun _ => rfl⟩
      · rw [if_neg h1]
        exact ⟨fun h => absurd h (by decide), fun h => absurd h (pow2_odd (by omega) h1)⟩

end OMA.A397588Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a397588.main :=
  OMA.A397588Proof.main_proof
