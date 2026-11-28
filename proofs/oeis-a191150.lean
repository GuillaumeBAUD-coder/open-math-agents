import OMAStatements.S_oeis_a191150
import Mathlib

namespace OMA.Helpers

theorem a191150_split (n : ℕ) (hn : 2 ≤ n) (f : ℕ → ℤ) :
    ∑ d ∈ n.properDivisors, f d = f 1 + ∑ d ∈ n.properDivisors.erase 1, f d := by
  have h1 : 1 ∈ n.properDivisors := Nat.mem_properDivisors.mpr ⟨one_dvd n, by omega⟩
  rw [Finset.add_sum_erase _ _ h1]

theorem a191150_sol :
    ∀ a g H : ℕ → ℤ,
      (a 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n →
        a n = (n : ℤ) - 1 + ∑ d ∈ n.properDivisors, (a d + d)) →
      (∀ n : ℕ, 1 ≤ n →
        g n = (ArithmeticFunction.sigma 1 n : ℤ) + ∑ d ∈ n.properDivisors, g d) →
      (H 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n → H n = ∑ d ∈ n.properDivisors, H d) →
      ∀ n : ℕ, 2 ≤ n → a n = g n - H n := by
  intro a g H ha hg hH n
  obtain ⟨ha1, ha⟩ := ha
  obtain ⟨hH1, hH⟩ := hH
  have g1 : g 1 = 1 := by rw [hg 1 le_rfl]; simp
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hsum : ∑ d ∈ n.properDivisors.erase 1, a d =
        ∑ d ∈ n.properDivisors.erase 1, g d - ∑ d ∈ n.properDivisors.erase 1, H d := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨hd1, hd⟩ := Finset.mem_erase.mp hd
      obtain ⟨hdv, hlt⟩ := Nat.mem_properDivisors.mp hd
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [zero_dvd_iff] at hdv
        omega
      exact ih d hlt (by omega)
    have hsig : (ArithmeticFunction.sigma 1 n : ℤ) = ∑ d ∈ n.properDivisors, (d : ℤ) + n := by
      rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
      push_cast
      rfl
    rw [ha n hn, hg n (by omega), hH n hn, Finset.sum_add_distrib, a191150_split n hn a,
      a191150_split n hn g, a191150_split n hn H, ha1, g1, hH1, hsig, hsum]
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a191150.main :=
  OMA.Helpers.a191150_sol
