import OMAReductions.R_oeis_a246914_R1
import Mathlib

open ArithmeticFunction

private lemma odd_natCast_zmod_two {n : ℕ} (h : Odd n) : (n : ZMod 2) = 1 := by
  obtain ⟨k, rfl⟩ := h
  push_cast
  simp [show (2 : ZMod 2) = 0 by decide]

theorem OMA.solution : OMA.R_oeis_a246914_R1.H1 := by
  intro p hp he
  rcases hp.eq_two_or_odd with rfl | hpodd
  · exact (show sigma 1 5 ≠ 11 by decide +kernel) he
  let n := 2 * p + 1
  have hn : Odd n := ⟨p, rfl⟩
  have hne : n ≠ 0 := by dsimp [n]; omega
  have hsum : ∑ d ∈ n.divisors, (d : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun d _ => n / d) ?_ ?_ ?_ ?_
    · intro d hd
      have hdvd := (Nat.mem_divisors.mp hd).1
      rw [odd_natCast_zmod_two (hn.of_dvd_nat hdvd),
        odd_natCast_zmod_two (hn.of_dvd_nat (Nat.div_dvd_of_dvd hdvd))]
      decide
    · intro d hd _ hfix
      have hdvd := (Nat.mem_divisors.mp hd).1
      have heq := Nat.div_mul_cancel hdvd
      rw [hfix] at heq
      obtain ⟨k, hk⟩ := hn.of_dvd_nat hdvd
      rw [hk, show (2*k+1)*(2*k+1) = 4*(k*k+k)+1 by ring] at heq
      dsimp [n] at heq
      omega
    · intro d hd
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hd).1, hne⟩
    · intro d hd
      exact Nat.div_div_self (Nat.mem_divisors.mp hd).1 hne
  have hcast : (sigma 1 n : ZMod 2) = 0 := by
    rw [sigma_one_apply, Nat.cast_sum]
    exact hsum
  change sigma 1 n = p * 4 + 3 at he
  rw [he] at hcast
  push_cast at hcast
  simp [show (4 : ZMod 2) = 0 by decide, show (3 : ZMod 2) = 1 by decide] at hcast
