import OMAStatements.S_oeis_a069548

/-!
# Parity of the divisor sum in OEIS A069548

Removing a factor of two preserves parity. On the odd part of the index,
Möbius cancellation reduces the sum modulo two to the number of divisors,
except at the odd part one. This gives an exact parity criterion.
-/

namespace A069548Proof

open ArithmeticFunction OMA.S_oeis_a069548

/-- Modulo two the three possible Möbius values give a single formula. -/
private theorem summand_mod_two (d : ℕ) :
    (summand d : ZMod 2) = (d : ZMod 2) * (1 + (moebius d : ZMod 2)) := by
  have h : summand d ≡ (d : ℤ) * (1 + moebius d) [ZMOD 2] := by
    rcases moebius_eq_or d with h | h | h <;>
      norm_num [summand, h, Int.ModEq] <;> omega
  simpa using (ZMod.intCast_eq_intCast_iff _ _ 2).2 h

/-- Any divisor introduced by doubling the index is even. -/
private theorem sum_divisors_double {n : ℕ} (hn : n ≠ 0) (f : ℕ → ZMod 2)
    (hf : ∀ d, Even d → f d = 0) :
    ∑ d ∈ (2 * n).divisors, f d = ∑ d ∈ n.divisors, f d := by
  symm
  apply Finset.sum_subset
  · intro d hd
    exact Nat.mem_divisors.mpr
      ⟨dvd_mul_of_dvd_right (Nat.dvd_of_mem_divisors hd) 2, mul_ne_zero (by decide) hn⟩
  · intro d hd hnew
    have heven : Even d := by
      apply Nat.not_odd_iff_even.mp
      intro hodd
      exact hnew <| Nat.mem_divisors.mpr
        ⟨(Nat.coprime_two_right.mpr hodd).dvd_of_dvd_mul_left (Nat.dvd_of_mem_divisors hd), hn⟩
    exact hf d heven

private theorem sum_on_odd_part (e m : ℕ) (hm : m ≠ 0) (f : ℕ → ZMod 2)
    (hf : ∀ d, Even d → f d = 0) :
    ∑ d ∈ (2 ^ e * m).divisors, f d = ∑ d ∈ m.divisors, f d := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', mul_assoc, sum_divisors_double (mul_ne_zero (pow_ne_zero _ (by decide)) hm) f hf, ih]

private theorem divisorSum_on_odd_part (e m : ℕ) (hm : m ≠ 0) :
    (divisorSum (2 ^ e * m) : ZMod 2) = (divisorSum m : ZMod 2) := by
  simp only [divisorSum, Int.cast_sum]
  apply sum_on_odd_part e m hm
  intro d hd
  rw [summand_mod_two, hd.natCast_zmod_two, zero_mul]

/-- For odd n greater than one, the Möbius values sum to zero over its divisors. -/
private theorem odd_index_mod_two {n : ℕ} (hn : Odd n) (hne : n ≠ 1) :
    (divisorSum n : ZMod 2) = (n.divisors.card : ZMod 2) := by
  have hmu : ∑ d ∈ n.divisors, moebius d = 0 := by
    rw [← coe_zeta_mul_apply, coe_zeta_mul_moebius, one_apply_ne hne]
  calc
    (divisorSum n : ZMod 2) = ∑ d ∈ n.divisors, (1 + (moebius d : ZMod 2)) := by
      simp only [divisorSum, Int.cast_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [summand_mod_two, (hn.of_dvd_nat (Nat.dvd_of_mem_divisors hd)).natCast_zmod_two, one_mul]
    _ = _ := by rw [Finset.sum_add_distrib, ← Int.cast_sum, hmu]; simp

private theorem odd_card_divisors_iff_square {n : ℕ} (hn : n ≠ 0) :
    Odd n.divisors.card ↔ IsSquare n := by
  constructor
  · intro h
    rw [Nat.card_divisors hn] at h
    rw [Nat.prod_primeFactors_pow_factorization hn]
    apply Finset.isSquare_prod
    intro p hp
    have hodd := h.of_dvd_nat (Finset.dvd_prod_of_mem (fun p => n.factorization p + 1) hp)
    obtain ⟨k, hk⟩ := hodd
    have hev : Even (n.factorization p) := ⟨k, by omega⟩
    exact hev.isSquare_pow p
  · rintro ⟨r, rfl⟩
    have hr : r ≠ 0 := fun hr => hn (by simp [hr])
    rw [Nat.card_divisors hn]
    apply Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) (by decide)
    intro p _
    rw [Nat.factorization_mul hr hr, Finsupp.add_apply]
    exact ⟨r.factorization p, by omega⟩

/-- An index has an odd sum exactly when its odd part is a square greater than one. -/
theorem odd_divisorSum_iff (e m : ℕ) (hm : Odd m) :
    Odd (divisorSum (2 ^ e * m)) ↔ m ≠ 1 ∧ IsSquare m := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [← ZMod.intCast_eq_one_iff_odd, divisorSum_on_odd_part e m hm0]
  by_cases h1 : m = 1
  · subst m
    norm_num [divisorSum, summand, moebius_apply_one]
    decide
  · rw [odd_index_mod_two hm h1, ZMod.natCast_eq_one_iff_odd, odd_card_divisors_iff_square hm0]
    simp [h1]

/-- The squarefree correction is odd exactly at powers of two. -/
theorem odd_correction_iff (e m : ℕ) (hm : Odd m) :
    Odd (divisorSum (2 ^ e * m) - 3 * ∑ d ∈ (2 ^ e * m).divisors, (d : ℤ)) ↔ m = 1 := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hsigma : (((∑ d ∈ (2 ^ e * m).divisors, (d : ℤ)) : ℤ) : ZMod 2) =
      (m.divisors.card : ZMod 2) := by
    simp only [Int.cast_sum, Int.cast_natCast]
    rw [sum_on_odd_part e m hm0 (fun d => (d : ZMod 2)) (fun _ hd => hd.natCast_zmod_two)]
    calc
      _ = ∑ _d ∈ m.divisors, (1 : ZMod 2) := Finset.sum_congr rfl fun d hd =>
        (hm.of_dvd_nat (Nat.dvd_of_mem_divisors hd)).natCast_zmod_two
      _ = _ := by simp
  rw [← ZMod.intCast_eq_one_iff_odd, Int.cast_sub, Int.cast_mul, hsigma,
    divisorSum_on_odd_part e m hm0, show ((3 : ℤ) : ZMod 2) = 1 by decide, one_mul]
  by_cases h1 : m = 1
  · subst m
    norm_num [divisorSum, summand, moebius_apply_one]
  · simp [odd_index_mod_two hm h1, h1]

/-- At index two, the squarefree correction in the OEIS comment is five. -/
theorem correction_at_two :
    divisorSum 2 - 3 * (∑ d ∈ (2 : ℕ).divisors, (d : ℤ)) = 5 := by
  norm_num [divisorSum, Nat.prime_two.divisors, summand, moebius_apply_one,
    moebius_apply_prime Nat.prime_two]

end A069548Proof

open OMA.S_oeis_a069548 A069548Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a069548.main := by
  intro n hn hodd
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
  have hs := ((odd_divisorSum_iff e m hm).mp hodd).2
  rcases Nat.even_or_odd e with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact Or.inl ((Even.isSquare_pow ⟨j, hj⟩ 2).mul hs)
  · obtain ⟨r, hr⟩ := hs.exists_sq
    right
    refine ⟨2 ^ j * r, ?_⟩
    have he : e = j + j + 1 := by omega
    rw [he, pow_succ, pow_add, hr]
    ring
