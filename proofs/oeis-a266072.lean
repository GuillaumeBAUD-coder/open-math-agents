import OMAStatements.S_oeis_a266072

-- Complete proof of OEIS A266072 (Rule 3 CA) via exact period-2 shift invariant
-- Author: Paul Roulleau (@Solfanbtc) via Antigravity NEON-SWARM FACTORY v3

open OMA.S_oeis_a266072 PowerSeries

private lemma update_eq (l c r : Bool) : update l c r = (!l && !c) := by
  cases l <;> cases c <;> cases r <;> decide

private lemma cell_even_odd :
    ∀ k : ℕ,
      (∀ i : ℤ, cell (2 * k) i = decide (i = (k : ℤ))) ∧
      (∀ i : ℤ, cell (2 * k + 1) i = decide (i ≠ (k : ℤ) ∧ i ≠ (k : ℤ) + 1))
  | 0 => by
    constructor
    · intro i; simp [cell]
    · intro i
      simp only [cell, update_eq, Nat.cast_zero, zero_add]
      by_cases h0 : i = 0
      · subst h0; decide
      · by_cases h1 : i = 1
        · subst h1; decide
        · have h1' : i - 1 ≠ 0 := by omega
          simp [h0, h1, h1']
  | k + 1 => by
    obtain ⟨_, hodd⟩ := cell_even_odd k
    have heven : ∀ i : ℤ, cell (2 * (k + 1)) i = decide (i = ((k + 1 : ℕ) : ℤ)) := by
      intro i
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, cell, update_eq, hodd, hodd]
      by_cases hi : i = (k : ℤ) + 1
      · subst hi
        have h1 : ((k : ℤ) + 1) - 1 = (k : ℤ) := by omega
        simp [h1]
      · by_cases hi0 : i = (k : ℤ)
        · subst hi0
          have h1 : (k : ℤ) - 1 ≠ (k : ℤ) := by omega
          have h2 : (k : ℤ) - 1 ≠ (k : ℤ) + 1 := by omega
          simp [h1, h2]
        · by_cases hi2 : i = (k : ℤ) + 2
          · subst hi2
            have h1 : ((k : ℤ) + 2) ≠ (k : ℤ) := by omega
            have h2 : ((k : ℤ) + 2) ≠ (k : ℤ) + 1 := by omega
            simp [h1, h2]
          · have h1 : i - 1 ≠ (k : ℤ) := by omega
            have h2 : i - 1 ≠ (k : ℤ) + 1 := by omega
            simp [h1, h2, hi0, hi]
    refine ⟨heven, ?_⟩
    intro i
    rw [cell, update_eq, heven, heven]
    by_cases h1 : i = (k : ℤ) + 1
    · subst h1; simp
    · by_cases h2 : i = (k : ℤ) + 2
      · subst h2
        have : ((k : ℤ) + 2) - 1 = (k : ℤ) + 1 := by omega
        simp [this]; omega
      · have h3 : i - 1 ≠ (k : ℤ) + 1 := by omega
        have h2' : i ≠ (k : ℤ) + 1 + 1 := by omega
        simp [h1, h2', h3]

private lemma a_even (k : ℕ) : a (2 * k) = 1 := by
  unfold a
  have hcell := (cell_even_odd k).1
  simp_rw [hcell]
  have hmem : 3 * k ∈ Finset.range (2 * (2 * k) + 1) := by
    rw [Finset.mem_range]; omega
  rw [Finset.sum_eq_single (3 * k)]
  · have hEq : ((3 * k : ℕ) : ℤ) - ((2 * k : ℕ) : ℤ) = (k : ℤ) := by omega
    rw [hEq]; simp
  · intro j _ hne
    simp; omega
  · intro hnot; exact absurd hmem hnot

private lemma a_odd (k : ℕ) : a (2 * k + 1) = 4 * (k : ℤ) + 1 := by
  unfold a
  have hcell := (cell_even_odd k).2
  simp_rw [hcell]
  have hmem1 : 3 * k + 1 ∈ Finset.range (2 * (2 * k + 1) + 1) := by
    rw [Finset.mem_range]; omega
  have hmem2 : 3 * k + 2 ∈ Finset.range (2 * (2 * k + 1) + 1) := by
    rw [Finset.mem_range]; omega
  have hpoint : ∀ j : ℕ,
      (if decide ((j : ℤ) - ((2 * k + 1 : ℕ) : ℤ) ≠ (k : ℤ) ∧
                  (j : ℤ) - ((2 * k + 1 : ℕ) : ℤ) ≠ (k : ℤ) + 1) then (1 : ℤ) else 0) +
      ((if j = 3 * k + 1 then (1 : ℤ) else 0) + (if j = 3 * k + 2 then (1 : ℤ) else 0)) = 1 := by
    intro j
    by_cases h1 : j = 3 * k + 1
    · subst h1
      have heq : ((3 * k + 1 : ℕ) : ℤ) - ((2 * k + 1 : ℕ) : ℤ) = (k : ℤ) := by omega
      rw [heq]; simp
    · by_cases h2 : j = 3 * k + 2
      · subst h2
        have heq : ((3 * k + 2 : ℕ) : ℤ) - ((2 * k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by omega
        rw [heq]; simp
      · simp [h1, h2]; omega
  have hsum :
      (∑ j ∈ Finset.range (2 * (2 * k + 1) + 1),
        if decide ((j : ℤ) - ((2 * k + 1 : ℕ) : ℤ) ≠ (k : ℤ) ∧
                   (j : ℤ) - ((2 * k + 1 : ℕ) : ℤ) ≠ (k : ℤ) + 1) then (1 : ℤ) else 0) +
      ((∑ j ∈ Finset.range (2 * (2 * k + 1) + 1), if j = 3 * k + 1 then (1 : ℤ) else 0) +
       (∑ j ∈ Finset.range (2 * (2 * k + 1) + 1), if j = 3 * k + 2 then (1 : ℤ) else 0)) =
      ∑ _j ∈ Finset.range (2 * (2 * k + 1) + 1), (1 : ℤ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => hpoint j)
  have hrhs : (∑ _j ∈ Finset.range (2 * (2 * k + 1) + 1), (1 : ℤ)) = 4 * (k : ℤ) + 3 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast; ring
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq', hrhs] at hsum
  simp only [hmem1, hmem2, ↓reduceIte] at hsum
  linarith

private lemma a_closed (n : ℕ) : a n = (n : ℤ) - (-1 : ℤ) ^ n * ((n : ℤ) - 1) := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h2k : k + k = 2 * k := by omega
    rw [h2k, a_even]
    have hpow : (-1 : ℤ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
    rw [hpow]; ring
  · rw [a_odd]
    have hpow : (-1 : ℤ) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [hpow]; push_cast; ring

theorem OMA.solution : type_of% @OMA.S_oeis_a266072.main := by
  have hrec : ∀ n : ℕ, 3 < n → a n = 2 * a (n - 2) - a (n - 4) := by
    intro n hn
    rw [a_closed n, a_closed (n - 2), a_closed (n - 4)]
    have h2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
    have h4 : ((n - 4 : ℕ) : ℤ) = (n : ℤ) - 4 := by omega
    have hp2 : (-1 : ℤ) ^ n = (-1 : ℤ) ^ (n - 2) := by
      have : n = (n - 2) + 2 := by omega
      conv_lhs => rw [this, pow_add]
      norm_num
    have hp4 : (-1 : ℤ) ^ n = (-1 : ℤ) ^ (n - 4) := by
      have : n = (n - 4) + 4 := by omega
      conv_lhs => rw [this, pow_add]
      norm_num
    rw [h2, h4, ← hp2, ← hp4]
    ring
  refine ⟨a_closed, hrec, ?_⟩
  ext n
  have hfac : (-1 + X ^ 2 : PowerSeries ℚ) ^ 2 = 1 - 2 * X ^ 2 + X ^ 4 := by ring
  rw [hfac, mul_add, mul_sub, mul_one, map_add, map_sub]
  have hmul_pow : ∀ (f : PowerSeries ℚ) (d : ℕ) (k : ℕ),
      PowerSeries.coeff k (f * X ^ d) = if d ≤ k then PowerSeries.coeff (k - d) f else 0 := by
    intro f d k
    rw [mul_comm, PowerSeries.coeff_X_pow_mul']
  have hmul_c : ∀ (f : PowerSeries ℚ) (c : ℚ) (d : ℕ) (k : ℕ),
      PowerSeries.coeff k (f * (PowerSeries.C c * X ^ d)) =
        if d ≤ k then c * PowerSeries.coeff (k - d) f else 0 := by
    intro f c d k
    rw [← mul_assoc, mul_comm f (PowerSeries.C c), mul_assoc, PowerSeries.coeff_C_mul, hmul_pow]
    split_ifs <;> ring
  have h2 : (2 : PowerSeries ℚ) * X ^ 2 = PowerSeries.C 2 * X ^ 2 := by
    rw [map_ofNat]
  rw [h2, hmul_c, hmul_pow]
  have hcoeff : ∀ k : ℕ, PowerSeries.coeff k (PowerSeries.mk fun m => (a m : ℚ)) = (a k : ℚ) :=
    fun k => PowerSeries.coeff_mk k _
  simp only [hcoeff]
  have hrhs : PowerSeries.coeff n (1 + X - X ^ 2 + 3 * X ^ 3 : PowerSeries ℚ) =
      (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0) -
      (if n = 2 then 1 else 0) + 3 * (if n = 3 then 1 else 0) := by
    have h3 : (3 : PowerSeries ℚ) * X ^ 3 = PowerSeries.C 3 * X ^ 3 := by
      rw [map_ofNat]
    rw [h3]
    simp [PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow,
          PowerSeries.coeff_C_mul]
  rw [hrhs]
  by_cases hn : n ≤ 3
  · interval_cases n <;> simp [a_closed] <;> norm_num
  · have hn4 : 4 ≤ n := by omega
    have hn2 : 2 ≤ n := by omega
    have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    have h2' : n ≠ 2 := by omega
    have h3' : n ≠ 3 := by omega
    simp only [hn2, hn4, h0, h1, h2', h3', ↓reduceIte]
    have hrec_q : (a n : ℚ) = 2 * (a (n - 2) : ℚ) - (a (n - 4) : ℚ) := by
      exact_mod_cast hrec n (by omega)
    linarith
