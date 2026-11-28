import OMAReductions.R_mo_315770_R1

/-!
# Proof of `mo-315770.R1.H1`

Proves that for every prime `p`, every `k : ℕ`, and every `z : ℤ`,
`∑ d ∈ (p ^ k).divisors, (1 : ℚ) / (d + 1) ≠ z`.

Since `(p ^ k).divisors = (Finset.range (k + 1)).image (p ^ ·)`, the sum equals
`∑ i ∈ Finset.range (k + 1), (1 : ℚ) / (p ^ i + 1)`.
- For `p = 2`: clearing denominators by the odd integer `M = ∏ i ∈ Finset.Icc 1 k, (2 ^ i + 1)`
  yields `2 * (M * z - N) = M` for an integer `N`, contradicting that `M` is odd.
- For `p ≥ 3`: induction on `k` proves `∑ i ∈ Finset.range (k + 1), 1 / (p ^ i + 1) ≤ 1 - 1 / (2 * p ^ k) < 1`,
  and the sum is strictly positive (at least `1 / 2`), so it lies in `(0, 1)` and cannot be an integer.
-/

namespace Mo315770R1H1Proof

open Finset

private lemma sum_divisors_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∑ d ∈ (p ^ k).divisors, (1 : ℚ) / ((d : ℚ) + 1) =
      ∑ i ∈ range (k + 1), (1 : ℚ) / (((p ^ i : ℕ) : ℚ) + 1) := by
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  rfl

private lemma bound_odd_prime {p : ℕ} (hp : 3 ≤ p) (k : ℕ) :
    ∑ i ∈ range (k + 1), (1 : ℚ) / (((p ^ i : ℕ) : ℚ) + 1) ≤
      1 - (1 : ℚ) / (2 * ((p ^ k : ℕ) : ℚ)) := by
  induction k with
  | zero =>
    simp
    norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hpq : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    have hpk_pos : (0 : ℚ) < ((p ^ k : ℕ) : ℚ) := by
      exact_mod_cast pow_pos (by omega : 0 < p) k
    have hpk1_pos : (0 : ℚ) < ((p ^ (k + 1) : ℕ) : ℚ) := by
      exact_mod_cast pow_pos (by omega : 0 < p) (k + 1)
    have hpk1_eq : ((p ^ (k + 1) : ℕ) : ℚ) = (p : ℚ) * ((p ^ k : ℕ) : ℚ) := by
      rw [pow_succ']
      push_cast
      rfl
    have hstep : (1 : ℚ) / (((p ^ (k + 1) : ℕ) : ℚ) + 1) ≤
        (1 : ℚ) / (2 * ((p ^ k : ℕ) : ℚ)) - (1 : ℚ) / (2 * ((p ^ (k + 1) : ℕ) : ℚ)) := by
      rw [hpk1_eq]
      have hden1 : (0 : ℚ) < (p : ℚ) * ((p ^ k : ℕ) : ℚ) + 1 := by positivity
      have hden2 : (0 : ℚ) < 2 * ((p : ℚ) * ((p ^ k : ℕ) : ℚ)) := by positivity
      have hdiff : (1 : ℚ) / (2 * ((p ^ k : ℕ) : ℚ)) -
          (1 : ℚ) / (2 * ((p : ℚ) * ((p ^ k : ℕ) : ℚ))) =
          ((p : ℚ) - 1) / (2 * ((p : ℚ) * ((p ^ k : ℕ) : ℚ))) := by
        field_simp
      rw [hdiff, div_le_div_iff₀ hden1 hden2]
      nlinarith
    linarith

private lemma prod_two_pow_add_one_odd (k : ℕ) :
    Odd (∏ i ∈ Icc 1 k, (2 ^ i + 1)) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hIcc : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    rw [hIcc, Finset.prod_insert (by simp)]
    have hodd : Odd (2 ^ (k + 1) + 1) := by
      refine ⟨2 ^ k, ?_⟩
      rw [pow_succ']
    exact hodd.mul ih

private lemma sum_Icc_mul_prod_int (k : ℕ) :
    ∃ N : ℕ, ((∏ i ∈ Icc 1 k, (2 ^ i + 1) : ℕ) : ℚ) *
      (∑ i ∈ Icc 1 k, (1 : ℚ) / (((2 ^ i : ℕ) : ℚ) + 1)) = (N : ℚ) := by
  refine ⟨∑ i ∈ Icc 1 k, ∏ j ∈ (Icc 1 k).erase i, (2 ^ j + 1), ?_⟩
  rw [Finset.mul_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hprod : ∏ j ∈ Icc 1 k, (2 ^ j + 1) = (2 ^ i + 1) * ∏ j ∈ (Icc 1 k).erase i, (2 ^ j + 1) :=
    (Finset.mul_prod_erase (Icc 1 k) (fun j => 2 ^ j + 1) hi).symm
  rw [hprod]
  push_cast
  have hne : ((2 ^ i : ℕ) : ℚ) + 1 ≠ 0 := by positivity
  field_simp [hne]

end Mo315770R1H1Proof

theorem OMA.solution : OMA.R_mo_315770_R1.H1 := by
  intro p k hp z hz
  rw [Mo315770R1H1Proof.sum_divisors_prime_pow hp k] at hz
  by_cases hp2 : p = 2
  · subst hp2
    have hsplit : ∑ i ∈ Finset.range (k + 1), (1 : ℚ) / (((2 ^ i : ℕ) : ℚ) + 1) =
        (1 : ℚ) / 2 + ∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / (((2 ^ i : ℕ) : ℚ) + 1) := by
      have hset : Finset.range (k + 1) = insert 0 (Finset.Icc 1 k) := by
        ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hset, Finset.sum_insert (by simp)]
      norm_num
    rw [hsplit] at hz
    set M : ℕ := ∏ i ∈ Finset.Icc 1 k, (2 ^ i + 1)
    obtain ⟨N, hN⟩ := Mo315770R1H1Proof.sum_Icc_mul_prod_int k
    have hmul : (2 : ℚ) * ((M : ℚ) * (z : ℚ) - (N : ℚ)) = (M : ℚ) := by
      have h1 := congrArg (fun x : ℚ => (M : ℚ) * x) hz
      rw [mul_add, hN] at h1
      linarith
    have hint : (2 : ℤ) * ((M : ℤ) * z - (N : ℤ)) = (M : ℤ) := by
      exact_mod_cast hmul
    have heven : Even M := by
      have h2dvd : (2 : ℤ) ∣ (M : ℤ) := ⟨(M : ℤ) * z - (N : ℤ), hint.symm⟩
      have h2nat : 2 ∣ M := Int.ofNat_dvd.mp h2dvd
      exact even_iff_two_dvd.mpr h2nat
    exact Nat.not_even_iff_odd.mpr (Mo315770R1H1Proof.prod_two_pow_add_one_odd k) heven
  · have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hle := Mo315770R1H1Proof.bound_odd_prime hp3 k
    have hpk_pos : (0 : ℚ) < 2 * ((p ^ k : ℕ) : ℚ) := by
      have : 0 < p ^ k := pow_pos hp.pos k
      positivity
    have hlt1 : ∑ i ∈ Finset.range (k + 1), (1 : ℚ) / (((p ^ i : ℕ) : ℚ) + 1) < 1 := by
      have hpos_inv : (0 : ℚ) < (1 : ℚ) / (2 * ((p ^ k : ℕ) : ℚ)) := div_pos one_pos hpk_pos
      linarith
    have hgt0 : (0 : ℚ) < ∑ i ∈ Finset.range (k + 1), (1 : ℚ) / (((p ^ i : ℕ) : ℚ) + 1) := by
      refine Finset.sum_pos (fun i _ => ?_) ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
      positivity
    rw [hz] at hgt0 hlt1
    have hz0 : (0 : ℤ) < z := by exact_mod_cast hgt0
    have hz1 : z < 1 := by exact_mod_cast hlt1
    omega
