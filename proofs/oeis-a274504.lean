import OMAStatements.S_oeis_a274504

private theorem kronecker_fourteen (a : ℤ) :
    OMA.S_oeis_a274504.kronecker a 14 = ZMod.χ₈ (a : ZMod 8) * jacobiSym a 7 := by
  have hfactor : (14 : ℕ).factorization 2 = 1 := by
    rw [show (14 : ℕ) = 2 * 7 by decide, Nat.factorization_mul (by decide) (by decide)]
    rw [Finsupp.add_apply, Nat.prime_two.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ (2 : ℕ) ∣ 7), add_zero]
  simp only [OMA.S_oeis_a274504.kronecker, hfactor, pow_one]

private theorem kronecker_mod_56 (a : ℤ) :
    OMA.S_oeis_a274504.kronecker a 14 =
      OMA.S_oeis_a274504.kronecker (a % 56) 14 := by
  have hchar : ZMod.χ₈ (a : ZMod 8) = ZMod.χ₈ (↑(a % 56) : ZMod 8) := by
    rw [ZMod.χ₈_int_mod_eight a, ZMod.χ₈_int_mod_eight (a % 56)]
    rw [Int.emod_emod_of_dvd a (by norm_num : (8 : ℤ) ∣ 56)]
  have hjacobi : jacobiSym a 7 = jacobiSym (a % 56) 7 :=
    jacobiSym.mod_left' (Int.emod_emod_of_dvd a (by norm_num : (7 : ℤ) ∣ 56)).symm
  rw [kronecker_fourteen, kronecker_fourteen, hchar, hjacobi]

-- The predicate is periodic, so check each of the 56 residues once.
private theorem residue_table (r : ℕ) (hr : r < 56) :
    OMA.S_oeis_a274504.kronecker (r : ℤ) 14 ≠ 1 ↔
      r ∉ ({1, 3, 5, 9, 13, 15, 19, 23, 25, 27, 39, 45} : Finset ℕ) := by
  interval_cases r <;>
    norm_num [kronecker_fourteen, ZMod.χ₈_int_eq_if_mod_eight,
      Finset.mem_insert, Finset.mem_singleton]

theorem OMA.solution : type_of% @OMA.S_oeis_a274504.main := by
  intro p _
  rw [kronecker_mod_56]
  change OMA.S_oeis_a274504.kronecker ((p : ℤ) % ((56 : ℕ) : ℤ)) 14 ≠ 1 ↔ _
  rw [← Int.natCast_emod]
  exact residue_table (p % 56) (Nat.mod_lt _ (by decide))
