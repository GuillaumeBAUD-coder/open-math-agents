import OMAStatements.S_oeis_a266516
import Mathlib

-- Credit: @wtho704

/-!
Keller's closed forms for OEIS A266516. The two-step orbit below is the
single-cell specialization of the Rule 29 solution in Henryk Fukś,
Solvable Cellular Automata (Springer, 2023), doi:10.1007/978-3-031-38700-5.
-/

namespace OMA.Rule29

open OMA.S_oeis_a266516

private def seed (x : ℤ) : Bool := decide (x = 0)

private def nextRow (x : ℤ) : Bool := decide (x ≠ -1)

private lemma step_seed : step 29 seed = nextRow := by
  funext x
  by_cases hm : x = -1
  · subst x
    decide
  by_cases hz : x = 0
  · subst x
    decide
  by_cases hp : x = 1
  · subst x
    decide
  have hleft : x - 1 ≠ 0 := by omega
  have hright : x + 1 ≠ 0 := by omega
  simp [step, seed, nextRow, hleft, hright, hz, hm]

private lemma step_nextRow : step 29 nextRow = seed := by
  funext x
  by_cases hm : x = -2
  · subst x
    decide
  by_cases hp : x = -1
  · subst x
    decide
  by_cases hz : x = 0
  · subst x
    decide
  have hleft : x - 1 ≠ -1 := by omega
  have hright : x + 1 ≠ -1 := by omega
  simp [step, seed, nextRow, hleft, hright, hz, hp]
  decide

private lemma state_by_parity (n : ℕ) :
    state 29 n = if Even n then seed else nextRow := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [state, ih]
    by_cases h : Even n
    · have hn : ¬ Even (n + 1) := fun he => (Nat.even_add_one.mp he) h
      rw [if_pos h, if_neg hn, step_seed]
    · have hn : Even (n + 1) := Nat.even_add_one.mpr h
      rw [if_neg h, if_pos hn, step_nextRow]

private lemma seed_value (n : ℕ) : rowValue seed n = 2 ^ n := by
  unfold rowValue
  rw [Finset.sum_eq_single n]
  · simp [seed]
  · intro i _ hi
    have h : (n : ℤ) - (i : ℤ) ≠ 0 := by omega
    simp [seed, h]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

private lemma nextRow_value_add (n : ℕ) (hn : 0 < n) :
    rowValue nextRow n + 2 ^ (n + 1) = ∑ i ∈ Finset.range (2 * n + 1), 2 ^ i := by
  have hmem : n + 1 ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (by omega)
  have hs : (∑ i ∈ Finset.range (2 * n + 1), if i = n + 1 then 2 ^ i else 0) =
      2 ^ (n + 1) := by rw [Finset.sum_ite_eq', if_pos hmem]
  unfold rowValue
  rw [← hs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases hi : i = n + 1
  · subst i
    simp [nextRow]
  · have h : (n : ℤ) - (i : ℤ) ≠ -1 := by omega
    simp [nextRow, h, hi]

private lemma sum_powers_two (m : ℕ) :
    (∑ i ∈ Finset.range m, (2 : ℚ) ^ i) + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith

private lemma a_of_even (n : ℕ) (hn : Even n) : (a n : ℚ) = 2 ^ n := by
  rw [a, state_by_parity, if_pos hn, seed_value]
  norm_cast

private lemma a_of_odd (n : ℕ) (hn : Odd n) : (a n : ℚ) = 2 * (4 ^ n - 2 ^ n) - 1 := by
  have he : ¬ Even n := Nat.not_even_iff_odd.mpr hn
  have hcast : (rowValue nextRow n : ℚ) + 2 ^ (n + 1) =
      ∑ i ∈ Finset.range (2 * n + 1), (2 : ℚ) ^ i := by
    exact_mod_cast nextRow_value_add n hn.pos
  have hsum := sum_powers_two (2 * n + 1)
  have hpow : (2 : ℚ) ^ (2 * n + 1) = 2 * 4 ^ n := by
    rw [pow_succ, pow_mul, mul_comm]
    norm_num
  rw [hpow] at hsum
  rw [pow_succ] at hcast
  rw [a, state_by_parity, if_neg he]
  linarith

end OMA.Rule29

theorem OMA.solution : type_of% @OMA.S_oeis_a266516.main :=
  ⟨OMA.Rule29.a_of_odd, OMA.Rule29.a_of_even⟩
