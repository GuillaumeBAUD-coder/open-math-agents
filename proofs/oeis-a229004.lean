import OMAStatements.S_oeis_a229004

open scoped BigOperators

namespace OMA.A229004

open OMA.S_oeis_a229004 (a)
open PowerSeries

private def bellMod (n : ℕ) : ZMod 3 := Nat.bell n

private def binomialSum (n : ℕ) (f : ℕ → ZMod 3) : ZMod 3 :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 3) * f k

private theorem bellMod_succ (n : ℕ) : bellMod (n + 1) = binomialSum n bellMod := by
  unfold bellMod binomialSum
  rw [Nat.bell_succ', ← Finset.Nat.sum_antidiagonal_swap
    (f := fun ij => n.choose ij.1 * ij.2.bell),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change ((n.choose (n - k) * k.bell : ℕ) : ZMod 3) = (n.choose k : ZMod 3) * k.bell
  rw [Nat.cast_mul, Nat.choose_symm (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]

private theorem binomialSum_add (n : ℕ) (f g : ℕ → ZMod 3) :
    binomialSum n (fun k => f k + g k) = binomialSum n f + binomialSum n g := by
  simp only [binomialSum, mul_add, Finset.sum_add_distrib]

private theorem binomialSum_succ (n : ℕ) (f : ℕ → ZMod 3) :
    binomialSum (n + 1) f = binomialSum n (fun k => f k + f (k + 1)) := by
  rw [binomialSum_add]
  exact Finset.sum_choose_succ_mul (fun k _ => f k) n

-- Three Pascal steps leave only the two outer terms in characteristic three.
private theorem binomialSum_add_three (n : ℕ) (f : ℕ → ZMod 3) :
    binomialSum (n + 3) f = binomialSum n (fun k => f k + f (k + 3)) := by
  rw [binomialSum_succ (n + 2), binomialSum_succ (n + 1), binomialSum_succ n]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only
  have h : (3 : ZMod 3) = 0 := by decide
  calc
    _ = (n.choose k : ZMod 3) *
        ((f k + f (k + 3)) + 3 * (f (k + 1) + f (k + 2))) := by ring
    _ = _ := by rw [h, zero_mul, add_zero]

private theorem touchard (n : ℕ) :
    bellMod (n + 3) = bellMod n + bellMod (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · rw [bellMod_succ 2]
      simp only [binomialSum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        bellMod, Nat.bell_zero, Nat.bell_one, Nat.bell_two]
      decide
    change bellMod ((n + 3) + 1) = bellMod (n + 1) + bellMod ((n + 1) + 1)
    rw [bellMod_succ (n + 3), binomialSum_add_three, bellMod_succ n,
      bellMod_succ (n + 1), binomialSum_succ n, ← binomialSum_add]
    apply Finset.sum_congr rfl
    intro k hk
    have h := ih k (Finset.mem_range.mp hk)
    dsimp only
    rw [h]

private def residue : ℕ → ZMod 3
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | n + 3 => residue n + residue (n + 1)

private theorem residue_step (n : ℕ) : residue (n + 3) = residue n + residue (n + 1) := by
  rw [residue]

private theorem bellMod_eq_residue (n : ℕ) : bellMod n = residue n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | n
    · simp [bellMod, residue]
    · simp [bellMod, residue]
    · simp [bellMod, residue]
    · change bellMod (n + 3) = residue (n + 3)
      rw [touchard, residue_step, ih n (by omega), ih (n + 1) (by omega)]

private theorem residue_period (n : ℕ) : residue (n + 13) = residue n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | n
    · decide
    · decide
    · decide
    · change residue (n + 3 + 13) = residue (n + 3)
      rw [show n + 3 + 13 = (n + 13) + 3 by omega, residue_step (n + 13), residue_step n,
        show n + 13 + 1 = n + 1 + 13 by omega, ih n (by omega), ih (n + 1) (by omega)]

private theorem residue_mod (n : ℕ) : residue n = residue (n % 13) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 13
    · rw [Nat.mod_eq_of_lt hn]
    · have he : n - 13 + 13 = n := by omega
      rw [← he, residue_period, Nat.add_mod_right]
      exact ih _ (by omega)

private theorem zero_residue (r : ℕ) (hr : r < 13) :
    residue r = 0 ↔ r = 4 ∨ r = 8 ∨ r = 9 ∨ r = 11 := by
  interval_cases r <;> decide

private theorem bell_dvd_iff (m : ℕ) :
    3 ∣ Nat.bell m ↔ m % 13 = 4 ∨ m % 13 = 8 ∨ m % 13 = 9 ∨ m % 13 = 11 := by
  rw [← ZMod.natCast_eq_zero_iff]
  change bellMod m = 0 ↔ _
  rw [bellMod_eq_residue, residue_mod]
  exact zero_residue _ (Nat.mod_lt _ (by decide))

private def offset (r : ℕ) : ℕ :=
  if r = 0 then 4 else if r = 1 then 8 else if r = 2 then 9 else 11

private def enumeration (k : ℕ) : ℕ := 13 * (k / 4) + offset (k % 4)

private theorem enumeration_block (q r : ℕ) (hr : r < 4) :
    enumeration (4 * q + r) = 13 * q + offset r := by
  unfold enumeration
  rw [show (4 * q + r) / 4 = q by omega, show (4 * q + r) % 4 = r by omega]

private theorem enumeration_strictMono : StrictMono enumeration := by
  apply strictMono_nat_of_lt_succ
  intro k
  unfold enumeration offset
  split_ifs <;> omega

private theorem enumeration_range : Set.range enumeration = Set.ofPred (fun m => 3 ∣ Nat.bell m) := by
  ext m
  change (∃ k, enumeration k = m) ↔ 3 ∣ Nat.bell m
  rw [bell_dvd_iff]
  constructor
  · rintro ⟨k, rfl⟩
    unfold enumeration offset
    split_ifs <;> omega
  · rintro (h | h | h | h)
    · use 4 * (m / 13) + 0
      rw [enumeration_block _ _ (by decide)]
      norm_num [offset]
      omega
    · use 4 * (m / 13) + 1
      rw [enumeration_block _ _ (by decide)]
      norm_num [offset]
      omega
    · use 4 * (m / 13) + 2
      rw [enumeration_block _ _ (by decide)]
      norm_num [offset]
      omega
    · use 4 * (m / 13) + 3
      rw [enumeration_block _ _ (by decide)]
      norm_num [offset]
      omega

private theorem nth_formula : Nat.nth (fun m => 3 ∣ Nat.bell m) = enumeration := by
  have hi : (Set.ofPred (fun m => 3 ∣ Nat.bell m)).Infinite := by
    rw [← enumeration_range]
    exact Set.infinite_range_of_injective enumeration_strictMono.injective
  exact ((Nat.nth_strictMono hi).range_inj enumeration_strictMono).mp
    ((Nat.range_nth_of_infinite hi).trans enumeration_range.symm)

private theorem a_add_four (n : ℕ) (hn : 1 ≤ n) : a (n + 4) = a n + 13 := by
  simp only [a, nth_formula, enumeration]
  rw [show (n + 4 - 1) / 4 = (n - 1) / 4 + 1 by omega,
    show (n + 4 - 1) % 4 = (n - 1) % 4 by omega]
  omega

private theorem a_recurrence (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℤ) = a (n - 1) + a (n - 4) - a (n - 5) := by
  have h₁ := a_add_four (n - 4) (by omega)
  have h₂ := a_add_four (n - 5) (by omega)
  rw [show n - 4 + 4 = n by omega] at h₁
  rw [show n - 5 + 4 = n - 1 by omega] at h₂
  omega

end OMA.A229004

open OMA.A229004 OMA.S_oeis_a229004 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a229004.main := by
  constructor
  · exact a_recurrence
  · have hden : ((X : PowerSeries ℤ) - 1) ^ 2 * (X + 1) * (X ^ 2 + 1) =
        X ^ 5 - X ^ 4 - X ^ 1 + 1 := by ring
    have hnum : (X : PowerSeries ℤ) * (2 * X ^ 4 + 2 * X ^ 3 + X ^ 2 + 4 * X + 4) =
        C 2 * X ^ 5 + C 2 * X ^ 4 + X ^ 3 + C 4 * X ^ 2 + C 4 * X ^ 1 := by
      simp only [map_ofNat]
      ring
    apply PowerSeries.ext
    intro n
    rw [hden, hnum]
    simp only [mul_add, mul_sub, mul_one, map_add, map_sub, coeff_C_mul_X_pow]
    simp only [coeff_mul_X_pow', coeff_mk, coeff_X_pow]
    by_cases hn : 6 ≤ n
    · have h₁ : 1 ≤ n := by omega
      have h₄ : 4 ≤ n := by omega
      have h₅ : 5 ≤ n := by omega
      have hne : ∀ k ≤ 5, n ≠ k := fun _ _ => by omega
      simp only [if_pos h₁, if_pos h₄, if_pos h₅,
        if_neg (hne 0 (by decide)), if_neg (hne 1 (by decide)), if_neg (hne 2 (by decide)),
        if_neg (hne 3 (by decide)), if_neg (hne 4 (by decide)), if_neg (hne 5 (by decide)),
        if_neg (show n - 1 ≠ 0 by omega), if_neg (show n - 4 ≠ 0 by omega),
        if_neg (show n - 5 ≠ 0 by omega)]
      linarith only [a_recurrence n hn]
    · interval_cases n <;> norm_num [a, nth_formula, enumeration, offset]
