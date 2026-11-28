import OMAReductions.R_oeis_a246914_R1
import Mathlib

open Finset

private theorem no_square {p : ℕ} (hp : p.Prime) (d : ℕ) :
    d * d ≠ 2 * p + 1 := by
  intro h
  have odd : Odd (2 * p + 1) := ⟨p, rfl⟩
  obtain ⟨k, hk⟩ := Odd.of_dvd_nat odd (show d ∣ 2 * p + 1 from ⟨d, h.symm⟩)
  have hd : d * d = 2 * (2 * (k * (k + 1))) + 1 := by
    rw [hk]
    ring
  have he : p = 2 * (k * (k + 1)) := by omega
  rcases hp.eq_two_or_odd with htwo | hodd
  · have hk0 : k ≠ 0 := by
      intro hk0
      simp [htwo, hk0] at he
    have hk1 : 1 ≤ k := by omega
    have hlarge : 2 ≤ k * (k + 1) := by
      simpa using (Nat.mul_le_mul hk1 (show 2 ≤ k + 1 by omega))
    omega
  · omega

private theorem odd_cast {m d : ℕ} (hm : Odd m) (hd : d ∣ m) :
    (d : ZMod 2) = 1 := by
  obtain ⟨k, hk⟩ := Odd.of_dvd_nat hm hd
  rw [hk]
  push_cast
  simp [show (2 : ZMod 2) = 0 by decide]

theorem OMA.solution : OMA.R_oeis_a246914_R1.H1 := by
  intro p hp h
  let m := 2 * p + 1
  have hm : Odd m := ⟨p, rfl⟩
  have hm0 : m ≠ 0 := by dsimp [m]; omega
  have mem (d : ℕ) (hd : d ∈ m.divisors) : m / d ∈ m.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hm0⟩
  have hz : (∑ d ∈ m.divisors, (d : ZMod 2)) = 0 := by
    apply Finset.sum_involution (fun d _ => m / d)
    · intro d hd
      rw [odd_cast hm (Nat.dvd_of_mem_divisors hd),
        odd_cast hm (Nat.dvd_of_mem_divisors (mem d hd))]
      decide
    · intro d hd _ heq
      have hmul := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
      rw [heq] at hmul
      exact no_square hp d hmul
    · exact mem
    · intro d hd
      exact Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hm0
  have hcast : (ArithmeticFunction.sigma 1 m : ZMod 2) = 0 := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum]
    exact hz
  change ArithmeticFunction.sigma 1 m = p * 4 + 3 at h
  rw [h] at hcast
  push_cast at hcast
  have zeroFour : (4 : ZMod 2) = 0 := by decide
  have oneThree : (3 : ZMod 2) = 1 := by decide
  simpa only [zeroFour, oneThree, mul_zero, zero_add, one_ne_zero] using hcast