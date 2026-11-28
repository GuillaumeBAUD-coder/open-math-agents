import OMAStatements.S_oeis_a081204

open OMA.S_oeis_a081204 in
theorem OMA.solution : type_of% @OMA.S_oeis_a081204.main := by
  have e (s c : ℕ) : a (2*s+c) = (3*s+((c+1)/2+c)).choose (2*s+c) := by
    unfold a
    congr 1
    omega
  have p (s : ℕ) : ((3*s+1) * (3*s).choose (2*s) : ℤ) = (3*s+1).choose (2*s+1) * (2*s+1) :=
    mod_cast Nat.add_one_mul_choose_eq (3*s) (2*s)
  have g (s : ℕ) : ((3*s+1).choose (2*s+1) * (3*s+2) : ℤ) = (3*s+2).choose (2*s+1) * (s+1) := by
    have := Nat.choose_mul_succ_eq (3*s+1) (2*s+1)
    rw [show 3*s+1+1-(2*s+1) = s+1 by omega] at this
    exact_mod_cast this
  have h (s : ℕ) : ((3*s+3) * (3*s+2).choose (2*s+1) : ℤ) = (3*s+3).choose (2*s+2) * (2*s+2) :=
    mod_cast Nat.add_one_mul_choose_eq (3*s+2) (2*s+1)
  constructor <;> intro n hn <;> obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn <;>
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k <;>
    have p0 := p i <;> have g0 := g i <;> have h0 := h i <;>
    have p1 := p (i+1) <;> have g1 := g (i+1) <;> have h1 := h (i+1) <;>
    simp [e, mul_add, add_assoc, show a (2*i) = (3*i).choose (2*i) by simpa using e i 0] at * <;>
    refine mul_left_cancel₀ i.cast_add_one_ne_zero ?_
  · linear_combination (i+1)*(-(864*i^3+2088*i^2+1620*i+408)*p0 -(576*i^3+1296*i^2+912*i+204)*g0 -(192*i^3+432*i^2+232*i+24)*h0)
  · linear_combination -(864*i^4+4104*i^3+7176*i^2+5478*i+1540)*h0 -(576*i^4+2544*i^3+4056*i^2+2768*i+680)*p1 -(384*i^4+1632*i^3+2528*i^2+1688*i+408)*g1
  · linear_combination -(-17928*i^3-49860*i^2-45252*i-13320)*p0 -(-11952*i^3-31248*i^2-25956*i-6660)*g0 -(-3840*i^3-9768*i^2-6172*i-240)*h0 -(96*i^3+400*i^2+544*i+240)*p1 -(64*i^3+256*i^2+336*i+144)*g1
  · linear_combination -(-17928*i^3-64800*i^2-75318*i-28140)*h0 -(-11808*i^3-38400*i^2-38112*i-11520)*p1 -(-7872*i^3-24288*i^2-23328*i-6912)*g1 -(32*i^3+176*i^2+304*i+160)*h1
