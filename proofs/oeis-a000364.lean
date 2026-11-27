import OMAStatements.S_oeis_a000364
import Mathlib

-- Disproof of Peter Bala's periodicity conjecture for the secant numbers (OEIS A000364).
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
--
-- Proof sketch: take k = 27, so totient 27 = 18 and a period p must divide 18.
-- Compute the secant numbers E 1, ..., E 19 exactly from the defining recurrence
-- (binomials are evaluated through descFactorial and factorial). Modulo 27 the sequence
-- from n = 1 reads 1, 5, 7, 8, 4, 11, 1, 14, 25, 17, 22, 20, 19, 23, 16, 26, 13, 2, 10, so
-- for p = 1, 2, 3, 9, 18 the congruence fails at n = 1 and for p = 6 it fails at n = 2.

namespace OMA.A000364Disproof

open OMA.S_oeis_a000364

theorem rec_eq (n : ℕ) : secantNumber (n + 1) = ∑ j ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ (j + 2) * ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) * secantNumber (n - j) := by
  rw [secantNumber, ← Fin.sum_univ_eq_sum_range (fun j =>
    (-1 : ℤ) ^ (j + 2) * ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) * secantNumber (n - j))]

theorem v0 : secantNumber 0 = 1 := by rw [secantNumber]
theorem v1 : secantNumber 1 = 1 := by
  rw [rec_eq 0]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_eq_descFactorial_div_factorial,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, v0]
  norm_num [Nat.descFactorial, Nat.factorial]
theorem v2 : secantNumber 2 = 5 := by
  rw [rec_eq 1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_eq_descFactorial_div_factorial,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, v0, v1]
  norm_num [Nat.descFactorial, Nat.factorial]
theorem v3 : secantNumber 3 = 61 := by
  rw [rec_eq 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_eq_descFactorial_div_factorial,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, v0, v1, v2]
  norm_num [Nat.descFactorial, Nat.factorial]
theorem v4 : secantNumber 4 = 1385 := by
  rw [rec_eq 3]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_eq_descFactorial_div_factorial,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, v0, v1, v2, v3]
  norm_num [Nat.descFactorial, Nat.factorial]
theorem v5 : secantNumber 5 = 50521 := by
  rw [rec_eq 4]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_eq_descFactorial_div_factorial,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, v0, v1, v2, v3, v4]
  norm_num [Nat.descFactorial, Nat.factorial]
theorem v6 : secantNumber 6 = 2702765 := by
  rw [rec_eq 5]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_eq_descFactorial_div_factorial,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, v0, v1, v2, v3, v4, v5]
  norm_num [Nat.descFactorial, Nat.factorial]
theorem v7 : secantNumber 7 = 199360981 := by
  rw [rec_eq 6]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_eq_descFactorial_div_factorial,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, v0, v1, v2, v3, v4, v5, v6]
  norm_num [Nat.descFactorial, Nat.factorial]
theorem v8 : secantNumber 8 = 19391512145 := by
  rw [rec_eq 7]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_eq_descFactorial_div_factorial,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, v0, v1, v2, v3, v4, v5, v6, v7]
  norm_num [Nat.descFactorial, Nat.factorial]
theorem v9 : secantNumber 9 = 2404879675441 := by
  rw [rec_eq 8]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_eq_descFactorial_div_factorial,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, v0, v1, v2, v3, v4, v5, v6, v7, v8]
  norm_num [Nat.descFactorial, Nat.factorial]
theorem v10 : secantNumber 10 = 370371188237525 := by
  rw [rec_eq 9]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_eq_descFactorial_div_factorial,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9]
  norm_num [Nat.descFactorial, Nat.factorial]
theorem v11 : secantNumber 11 = 69348874393137901 := by
  rw [rec_eq 10]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_eq_descFactorial_div_factorial,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
  norm_num [Nat.descFactorial, Nat.factorial]
theorem v12 : secantNumber 12 = 15514534163557086905 := by
  rw [rec_eq 11]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_eq_descFactorial_div_factorial,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
  norm_num [Nat.descFactorial, Nat.factorial]
theorem v13 : secantNumber 13 = 4087072509293123892361 := by
  rw [rec_eq 12]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_eq_descFactorial_div_factorial,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12]
  norm_num [Nat.descFactorial, Nat.factorial]
theorem v14 : secantNumber 14 = 1252259641403629865468285 := by
  rw [rec_eq 13]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_eq_descFactorial_div_factorial,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13]
  norm_num [Nat.descFactorial, Nat.factorial]
theorem v15 : secantNumber 15 = 441543893249023104553682821 := by
  rw [rec_eq 14]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_eq_descFactorial_div_factorial,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
  norm_num [Nat.descFactorial, Nat.factorial]
theorem v16 : secantNumber 16 = 177519391579539289436664789665 := by
  rw [rec_eq 15]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_eq_descFactorial_div_factorial,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
  norm_num [Nat.descFactorial, Nat.factorial]
theorem v17 : secantNumber 17 = 80723299235887898062168247453281 := by
  rw [rec_eq 16]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_eq_descFactorial_div_factorial,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16]
  norm_num [Nat.descFactorial, Nat.factorial]
theorem v18 : secantNumber 18 = 41222060339517702122347079671259045 := by
  rw [rec_eq 17]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_eq_descFactorial_div_factorial,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17]
  norm_num [Nat.descFactorial, Nat.factorial]
theorem v19 : secantNumber 19 = 23489580527043108252017828576198947741 := by
  rw [rec_eq 18]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_eq_descFactorial_div_factorial,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18]
  norm_num [Nat.descFactorial, Nat.factorial]

end OMA.A000364Disproof

open OMA.S_oeis_a000364 OMA.A000364Disproof in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a000364.main) := by
  intro h
  obtain ⟨p, hp0, hpd, hp⟩ := h 27 (by norm_num)
  have ht : Nat.totient 27 = 18 := by decide
  rw [ht] at hpd
  have hmem : p ∈ Nat.divisors 18 := Nat.mem_divisors.2 ⟨hpd, by norm_num⟩
  have hd : Nat.divisors 18 = {1, 2, 3, 6, 9, 18} := by decide
  rw [hd] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · have h1 := hp 1 (by norm_num)
    norm_num [Int.ModEq, v1, v2] at h1
  · have h1 := hp 1 (by norm_num)
    norm_num [Int.ModEq, v1, v3] at h1
  · have h1 := hp 1 (by norm_num)
    norm_num [Int.ModEq, v1, v4] at h1
  · have h1 := hp 2 (by norm_num)
    norm_num [Int.ModEq, v2, v8] at h1
  · have h1 := hp 1 (by norm_num)
    norm_num [Int.ModEq, v1, v10] at h1
  · have h1 := hp 1 (by norm_num)
    norm_num [Int.ModEq, v1, v19] at h1
