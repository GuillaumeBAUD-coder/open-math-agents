import OMAReductions.R_oeis_a246914_R1
import Mathlib

theorem OMA.a246914_even (m : ℕ) (hm : Odd m) (hsq : ∀ s : ℕ, s * s ≠ m) :
    Even (ArithmeticFunction.sigma 1 m) := by
  rw [← ZMod.natCast_eq_zero_iff_even, ArithmeticFunction.sigma_one_apply, Nat.cast_sum]
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hodd : ∀ d, d ∈ m.divisors → ((d : ℕ) : ZMod 2) = 1 := by
    intro d hd
    rw [ZMod.natCast_eq_one_iff_odd]
    exact hm.of_dvd_nat (Nat.dvd_of_mem_divisors hd)
  have hmem : ∀ d, d ∈ m.divisors → m / d ∈ m.divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hm0⟩
  refine Finset.sum_involution (fun d _ => m / d) ?_ ?_ hmem ?_
  · intro d hd
    rw [hodd d hd, hodd _ (hmem d hd)]
    decide
  · intro d hd _ he
    have := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
    rw [he] at this
    exact hsq d this
  · intro d hd
    exact Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hm0

theorem OMA.solution : OMA.R_oeis_a246914_R1.H1 := by
  intro p hp h
  by_cases hsq : ∀ s : ℕ, s * s ≠ 2 * p + 1
  · have he := OMA.a246914_even (2 * p + 1) ⟨p, rfl⟩ hsq
    rw [h] at he
    obtain ⟨c, hc⟩ := he
    omega
  · push_neg at hsq
    obtain ⟨s, hs⟩ := hsq
    have hmod := Nat.mul_mod s s 4
    rcases hp.eq_two_or_odd with h2 | h2
    · subst h2
      have : s ≤ 2 := by nlinarith
      interval_cases s <;> omega
    · have h4 : s % 4 = 0 ∨ s % 4 = 1 ∨ s % 4 = 2 ∨ s % 4 = 3 := by omega
      rcases h4 with h4 | h4 | h4 | h4 <;> rw [h4, hs] at hmod <;> omega
