import OMAStatements.S_oeis_a191150
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a191150.main := by
  intro a g H ⟨ha1, ha⟩ hg ⟨hH1, hH⟩ n
  have hg1 : g 1 = 1 := by
    have := hg 1 le_rfl
    simpa using this
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have h1 : 1 ∈ n.properDivisors := by
      rw [Nat.mem_properDivisors]
      exact ⟨one_dvd _, by omega⟩
    have hsig : (ArithmeticFunction.sigma 1 n : ℤ) = ∑ d ∈ n.properDivisors, (d : ℤ) + n := by
      rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
      push_cast
      rfl
    have hih : ∀ d ∈ n.properDivisors.erase 1, a d = g d - H d := by
      intro d hd
      rw [Finset.mem_erase, Nat.mem_properDivisors] at hd
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd.2.1 (by omega)
      exact ih d hd.2.2 (by omega)
    have e1 := Finset.add_sum_erase n.properDivisors (fun d => a d + (d : ℤ)) h1
    have e2 := Finset.add_sum_erase n.properDivisors (fun d => g d) h1
    have e3 := Finset.add_sum_erase n.properDivisors (fun d => H d) h1
    have e4 := Finset.add_sum_erase n.properDivisors (fun d => (d : ℤ)) h1
    have e5 : ∑ d ∈ n.properDivisors.erase 1, (a d + (d : ℤ))
        = ∑ d ∈ n.properDivisors.erase 1, g d - ∑ d ∈ n.properDivisors.erase 1, H d
          + ∑ d ∈ n.properDivisors.erase 1, (d : ℤ) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun d hd => ?_)
      rw [hih d hd]
    rw [ha n hn, hg n (by omega), hH n hn, hsig]
    simp only [Nat.cast_one] at e1 e2 e3 e4
    linarith
