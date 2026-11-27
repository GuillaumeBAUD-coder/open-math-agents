import OMAStatements.S_oeis_a129439
import Mathlib

/-! Each divisor d occurs once for each positive multiple of d.
After interchanging the two finite products its exponent is floor(n/d).
These exponents are superadditive. -/
namespace Deldor14.DivisorProduct
open Finset OMA.S_oeis_a129439
private theorem formula {n N : ℕ} (h : n≤N) :
    D n = ∏ d ∈ range (N+1), d^(n/d) := by
  have factors (m : ℕ) (hm : m ∈ range (n+1)) :
      (∏ d ∈ m.divisors, d) = ∏ d ∈ range (N+1), if m≠0 ∧ d∣m then d else 1 := by
    have bounded : m.divisors = (range (N+1)).filter (fun d => m≠0 ∧ d∣m) := by
      ext d
      rw [Nat.mem_divisors,mem_filter,mem_range]
      constructor
      · rintro ⟨dvd,nz⟩
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero nz) dvd
        have := mem_range.mp hm
        exact ⟨by omega,nz,dvd⟩
      · rintro ⟨_,nz,dvd⟩
        exact ⟨dvd,nz⟩
    rw [bounded,prod_filter]
  unfold D
  rw [prod_congr rfl factors,prod_comm]
  apply prod_congr rfl
  intro d _
  rw [← prod_filter,prod_const,Nat.card_multiples']

theorem result : type_of% @OMA.S_oeis_a129439.main := by
  intro n k hk
  rw [formula (N:=n) (Nat.sub_le n k), formula hk, formula (n:=n) le_rfl,
    ← prod_mul_distrib]
  apply prod_dvd_prod_of_dvd
  intro d _
  rw [←pow_add]
  apply Nat.pow_dvd_pow
  simpa only [Nat.sub_add_cancel hk] using Nat.div_add_div_le_add_div (x:=n-k) (y:=k) (z:=d)
end Deldor14.DivisorProduct
theorem OMA.solution : type_of% @OMA.S_oeis_a129439.main := Deldor14.DivisorProduct.result
