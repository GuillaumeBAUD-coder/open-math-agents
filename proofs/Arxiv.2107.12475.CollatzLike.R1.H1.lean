import OMAReductions.R_Arxiv_2107_12475_CollatzLike_R1

-- The digit 2 occurs in the base-three expansion of 2^n for every n outside sixteen residue classes mod 162.
-- 2 has order 162 modulo 243 = 3^5, so 2^n mod 243, hence the five lowest ternary digits of 2^n, depends only
-- on n mod 162 (pow_period). The kernel checks the 162 residues (table): one of the five digits is 2 except
-- for the sixteen listed classes. The j-th digit is read off with Mathlib's Nat.getD_digits (two_mem).
-- An elementary sieve on low digits; it does not touch the open classes, and is not progress on the conjecture.

namespace OMA.Ternary

theorem two_mem (m j : ℕ) (h : m / 3 ^ j % 3 = 2) : 2 ∈ Nat.digits 3 m := by
  have hg : (Nat.digits 3 m).getD j 0 = 2 := by
    rw [Nat.getD_digits m j (by norm_num)]
    exact h
  by_cases hj : j < (Nat.digits 3 m).length
  · rw [List.getD_eq_getElem _ _ hj] at hg
    exact hg ▸ List.getElem_mem hj
  · rw [List.getD_eq_default _ _ (by omega)] at hg
    omega

/-- One of the five lowest ternary digits of `c` is `2`. -/
def hasTwo (c : ℕ) : Bool :=
  decide (c % 3 = 2) || decide (c / 3 % 3 = 2) || decide (c / 9 % 3 = 2) ||
    decide (c / 27 % 3 = 2) || decide (c / 81 % 3 = 2)

theorem hasTwo_spec (m : ℕ) (h : hasTwo (m % 243) = true) : 2 ∈ Nat.digits 3 m := by
  simp only [hasTwo, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (((h | h) | h) | h) | h
  · exact two_mem m 0 (by norm_num; omega)
  · exact two_mem m 1 (by norm_num; omega)
  · exact two_mem m 2 (by norm_num; omega)
  · exact two_mem m 3 (by norm_num; omega)
  · exact two_mem m 4 (by norm_num; omega)

theorem pow_period (n : ℕ) : 2 ^ n % 243 = 2 ^ (n % 162) % 243 := by
  have e : 2 ^ n = (2 ^ 162) ^ (n / 162) * 2 ^ (n % 162) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have h1 : (2 ^ 162) ^ (n / 162) % 243 = 1 := by
    rw [Nat.pow_mod]
    have h0 : 2 ^ 162 % 243 = 1 := by norm_num
    rw [h0, one_pow]
    norm_num
  rw [e, Nat.mul_mod, h1, one_mul, Nat.mod_mod]

set_option maxRecDepth 100000 in
theorem table : ∀ r < 162, r ∉ ({0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150} : Finset ℕ) → hasTwo (2 ^ r % 243) = true := by
  decide +kernel

theorem classes (n : ℕ) (h : n % 162 ∉ ({0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150} : Finset ℕ)) : 2 ∈ Nat.digits 3 (2 ^ n) := by
  apply hasTwo_spec
  rw [pow_period]
  exact table (n % 162) (Nat.mod_lt _ (by norm_num)) h

end OMA.Ternary

theorem OMA.solution : OMA.R_Arxiv_2107_12475_CollatzLike_R1.H1 := by
  intro n _ h
  exact OMA.Ternary.classes n h
