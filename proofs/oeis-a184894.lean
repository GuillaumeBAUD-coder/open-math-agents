import OMAStatements.S_oeis_a184894

-- Complete proof of OEIS A184894 via Frobenius endomorphism in (ZMod 3)[X]
-- Author: Paul Roulleau (@Solfanbtc) via Antigravity NEON-SWARM FACTORY v3

open OMA.S_oeis_a184894 Polynomial

private lemma zmod3_cube (a : ZMod 3) : a ^ 3 = a := by
  fin_cases a <;> rfl

private lemma poly_zmod3_add_cube (p q : Polynomial (ZMod 3)) :
    (p + q) ^ 3 = p ^ 3 + q ^ 3 := by
  have h : (p + q) ^ 3 = p ^ 3 + 3 * p ^ 2 * q + 3 * p * q ^ 2 + q ^ 3 := by ring
  rw [h]
  have h3z : (3 : ZMod 3) = 0 := rfl
  have h3 : (3 : Polynomial (ZMod 3)) = 0 := by
    rw [← Polynomial.C_ofNat, h3z, map_zero]
  rw [h3]
  ring

private lemma poly_zmod3_sum_cube {ι : Type*} (s : Finset ι) (f : ι → Polynomial (ZMod 3)) :
    (∑ i ∈ s, f i) ^ 3 = ∑ i ∈ s, (f i) ^ 3 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, poly_zmod3_add_cube, ih, Finset.sum_insert ha]

private lemma iteratePoly_map_zmod3 :
    ∀ m : ℕ,
      (iteratePoly m).map (Nat.castRingHom (ZMod 3)) =
        ∑ j ∈ Finset.range (m + 1),
          Polynomial.C ((m.choose j : ℕ) : ZMod 3) * Polynomial.X ^ (3 ^ j)
  | 0 => by
    simp [iteratePoly]
  | m + 1 => by
    have ih := iteratePoly_map_zmod3 m
    simp only [iteratePoly, Polynomial.map_add, Polynomial.map_pow, ih]
    rw [poly_zmod3_sum_cube]
    have hterm : ∀ j : ℕ,
        (Polynomial.C ((m.choose j : ℕ) : ZMod 3) * Polynomial.X ^ (3 ^ j)) ^ 3 =
          Polynomial.C ((m.choose j : ℕ) : ZMod 3) * Polynomial.X ^ (3 ^ (j + 1)) := by
      intro j
      rw [mul_pow, ← Polynomial.C_pow, zmod3_cube, ← pow_mul, pow_succ]
    simp_rw [hterm]
    have hL1 :
        (∑ j ∈ Finset.range (m + 1), Polynomial.C ((m.choose j : ℕ) : ZMod 3) * X ^ (3 ^ j)) =
        (∑ k ∈ Finset.range m, Polynomial.C ((m.choose (k + 1) : ℕ) : ZMod 3) * X ^ (3 ^ (k + 1))) + X := by
      rw [Finset.sum_range_succ']
      simp
    have hL2 :
        (∑ j ∈ Finset.range (m + 1), Polynomial.C ((m.choose j : ℕ) : ZMod 3) * X ^ (3 ^ (j + 1))) =
        (∑ k ∈ Finset.range m, Polynomial.C ((m.choose k : ℕ) : ZMod 3) * X ^ (3 ^ (k + 1))) + X ^ (3 ^ (m + 1)) := by
      rw [Finset.sum_range_succ]
      simp
    have hR :
        (∑ j ∈ Finset.range (m + 1 + 1), Polynomial.C (((m + 1).choose j : ℕ) : ZMod 3) * X ^ (3 ^ j)) =
        (∑ k ∈ Finset.range m, Polynomial.C (((m + 1).choose (k + 1) : ℕ) : ZMod 3) * X ^ (3 ^ (k + 1))) +
          X ^ (3 ^ (m + 1)) + X := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      simp
    have hcomb :
        (∑ k ∈ Finset.range m, Polynomial.C ((m.choose (k + 1) : ℕ) : ZMod 3) * X ^ (3 ^ (k + 1))) +
        (∑ k ∈ Finset.range m, Polynomial.C ((m.choose k : ℕ) : ZMod 3) * X ^ (3 ^ (k + 1))) =
        ∑ k ∈ Finset.range m, Polynomial.C (((m + 1).choose (k + 1) : ℕ) : ZMod 3) * X ^ (3 ^ (k + 1)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [Nat.choose_succ_succ, add_comm (m.choose k), Nat.cast_add, map_add, add_mul]
    rw [hL1, hL2, hR, ← hcomb, add_add_add_comm, add_comm (X : Polynomial (ZMod 3)), ← add_assoc]

private lemma coeff_iteratePoly_zmod3 (m k : ℕ) :
    ((iteratePoly m).coeff k : ZMod 3) =
      ∑ j ∈ Finset.range (m + 1), if k = 3 ^ j then ((m.choose j : ℕ) : ZMod 3) else 0 := by
  have h1 : ((iteratePoly m).coeff k : ZMod 3) =
      ((iteratePoly m).map (Nat.castRingHom (ZMod 3))).coeff k := by
    rw [Polynomial.coeff_map]
    rfl
  rw [h1, iteratePoly_map_zmod3, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs <;> simp

private lemma two_mul_le_three_pow_add_one : ∀ j : ℕ, 2 * j ≤ 3 ^ j + 1
  | 0 => by decide
  | j + 1 => by
    have ih := two_mul_le_three_pow_add_one j
    have h1 : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by omega)
    have h3 : 3 ^ (j + 1) = 3 * 3 ^ j := by rw [pow_succ']
    omega

private lemma odd_three_pow (j : ℕ) : 3 ^ j % 2 = 1 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [pow_succ']
    omega

private lemma choose_365_6_mod3 : ((365 : ℕ).choose 6 : ZMod 3) = 0 := by
  have hval : (365 : ℕ).choose 6 = 3151277509380 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial_succ, Nat.factorial_succ]
  rw [hval]
  decide

theorem OMA.solution : type_of% @OMA.S_oeis_a184894.main := by
  have hpart2 : ∀ j : ℕ,
      (term ((3 ^ j + 1) / 2) : ZMod 3) = (((3 ^ j + 1) / 2 : ℕ).choose j : ZMod 3) := by
    intro j
    unfold term
    have hodd := odd_three_pow j
    have h1 : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by omega)
    have hdeg : 2 * ((3 ^ j + 1) / 2) - 1 = 3 ^ j := by omega
    rw [hdeg, coeff_iteratePoly_zmod3]
    have hjmem : j ∈ Finset.range ((3 ^ j + 1) / 2 + 1) := by
      rw [Finset.mem_range]
      have := two_mul_le_three_pow_add_one j
      omega
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hne
      have hpne : 3 ^ j ≠ 3 ^ b := fun heq =>
        hne (Nat.pow_right_injective (by norm_num : 1 < 3) heq).symm
      simp [hpne]
    · intro hnot; exact absurd hjmem hnot
  refine ⟨?_, hpart2, ?_⟩
  · intro m hm hndvd
    have hnz : (term m : ZMod 3) ≠ 0 := by
      intro hz
      exact hndvd ((ZMod.natCast_eq_zero_iff (term m) 3).mp hz)
    unfold term at hnz
    rw [coeff_iteratePoly_zmod3] at hnz
    by_contra hnone
    push Not at hnone
    apply hnz
    refine Finset.sum_eq_zero ?_
    intro j _
    split_ifs with heq
    · exfalso
      have hodd := odd_three_pow j
      have hm_eq : m = (3 ^ j + 1) / 2 := by omega
      exact hnone j hm_eq
    · rfl
  · rw [← ZMod.natCast_eq_zero_iff]
    have h6 := hpart2 6
    have h365 : (3 ^ 6 + 1) / 2 = 365 := by decide
    rw [h365] at h6
    rw [h6]
    exact choose_365_6_mod3
