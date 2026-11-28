import OMAStatements.S_oeis_a007857
import Mathlib

open OMA.S_oeis_a007857 in
theorem OMA.solution : type_of% @OMA.S_oeis_a007857.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have B (n : ℕ) : (2*(n+1)*(2*n+1) * (3*n+3).choose (n+1) : ℚ) = 3*(3*n+1)*(3*n+2) * (3*n).choose n := by
    rw [Nat.cast_choose ℚ (show n+1 ≤ 3*n+3 by omega), Nat.cast_choose ℚ (show n ≤ 3*n by omega),
      show 3*n+3-(n+1) = 2*n+2 by omega, show 3*n-n = 2*n by omega]
    simp [Nat.factorial_succ]
    field_simp
    ring
  have D (t : ℕ) : (((t:ℚ)+1) * (2*t+2).choose (t+1)) = 2*(2*t+1) * (2*t).choose t := by
    have h := t.succ_mul_centralBinom_succ
    simp only [Nat.centralBinom, mul_add, mul_one] at h
    qify at h
    linear_combination h
  have E (m : ℕ) : ((m:ℚ)+1) * a (m+1) = 2*(3*m).choose m - (2*m).choose m := by
    rw [a, Nat.add_sub_cancel]
    push_cast
    field_simp
  have E3 := E (k+3)
  have E2 := E (k+2)
  have E1 := E (k+1)
  have E0 := E k
  have B0 := B k
  have B1 := B (k+1)
  have B2 := B (k+2)
  have D0 := D k
  have D1 := D (k+1)
  have D2 := D (k+2)
  simp [mul_add, add_assoc] at *
  refine mul_left_cancel₀ (show ((k:ℚ)+4)*(k+3)*(k+2)*(k+1) ≠ 0 by positivity) ?_
  linear_combination 2*(k+4)*(k+3)*(2*(k+4)-3)*(44*(k+4)-69)*((k+3)*(k+2)*(k+1:ℚ))*E3
    + (k+3)*(176*(k+4)^3-9591*(k+4)^2+38703*(k+4)-40640)*((k+4)*(k+2)*(k+1:ℚ))*E2
    + (-17479*(k+4)^4+218005*(k+4)^3-959616*(k+4)^2+1797890*(k+4)-1221920)*((k+4)*(k+3)*(k+1:ℚ))*E1
    + 6*(3*(k+4)-10)*(2*(k+4)-7)*(3*(k+4)-11)*(517*(k+4)-1198)*((k+4)*(k+3)*(k+2:ℚ))*E0
    + (-4136*k^5-46252*k^4-192268*k^3-365312*k^2-307152*k-83520)*B0
    + (682*k^5+5108*k^4+6826*k^3-25212*k^2-67788*k-40176)*B1
    + (88*k^5+1094*k^4+5220*k^3+11890*k^2+12812*k+5136)*B2
    + (13959*k^6+163080*k^5+726567*k^4+1553238*k^3+1637148*k^2+773928*k+125280)*D0
    + (-880*k^6-4793*k^5+17873*k^4+182389*k^3+481247*k^2+528484*k+207840)*D1
    + (-176*k^6-2628*k^5-15910*k^4-49880*k^3-85074*k^2-74332*k-25680)*D2
