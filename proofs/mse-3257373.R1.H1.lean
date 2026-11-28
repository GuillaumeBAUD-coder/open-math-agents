import OMAReductions.R_mse_3257373_R1

/-!
# Proof of `mse-3257373.R1.H1`

Proves the three classical facts about `floorZetaNeg n = ⌊(riemannZeta (-(n : ℂ))).re⌋`:
1. `floorZetaNeg (2 * k) = 0` for all `k ≥ 1`, from `riemannZeta_neg_nat_eq_bernoulli` and
   `bernoulli_eq_zero_of_odd`.
2. `floorZetaNeg (4 * j + 1) < 0` for all `j : ℕ`, from Euler's formula `hasSum_zeta_nat` showing
   `bernoulli (4 * j + 2) > 0`, whence `(riemannZeta (-(4 * j + 1 : ℂ))).re < 0`.
3. `floorZetaNeg 23 = 3607`, by verifying `bernoulli 24 = -236364091 / 2730` via the defining
   recurrence `sum_bernoulli` and evaluating `⌊236364091 / 65520⌋ = 3607`.
-/

namespace Mse3257373R1H1Proof

open Finset

private lemma re_riemannZeta_neg_nat (n : ℕ) :
    (riemannZeta (-(n : ℂ))).re = (-1 : ℝ) ^ n * (bernoulli (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  rw [riemannZeta_neg_nat_eq_bernoulli n]
  have h : (-1 : ℂ) ^ n * (bernoulli (n + 1) : ℂ) / ((n : ℂ) + 1) =
      (((-1 : ℝ) ^ n * (bernoulli (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h, Complex.ofReal_re]

private lemma bernoulli_pos_of_four_mul_add_two (j : ℕ) :
    (0 : ℝ) < (bernoulli (4 * j + 2) : ℝ) := by
  set k := 2 * j + 1
  have hk : k ≠ 0 := by dsimp [k]; omega
  have hsum := hasSum_zeta_nat hk
  have htsum_pos : (0 : ℝ) < ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k) := by
    have hnn : ∀ n : ℕ, 0 ≤ 1 / (n : ℝ) ^ (2 * k) := fun n => by positivity
    have h1 : (0 : ℝ) < 1 / ((1 : ℕ) : ℝ) ^ (2 * k) := by norm_num
    exact lt_of_lt_of_le h1 (hsum.summable.le_tsum 1 (fun n _ => hnn n))
  rw [hsum.tsum_eq] at htsum_pos
  have hsign : (-1 : ℝ) ^ (k + 1) = 1 := by
    have hev : Even (k + 1) := ⟨j + 1, by dsimp [k]; omega⟩
    exact hev.neg_one_pow
  rw [hsign, one_mul] at htsum_pos
  have hcoeff_pos : (0 : ℝ) < 2 ^ (2 * k - 1) * Real.pi ^ (2 * k) / ((2 * k).factorial : ℝ) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hfac : (0 : ℝ) < ((2 * k).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    positivity
  have hmul : 2 ^ (2 * k - 1) * Real.pi ^ (2 * k) * (bernoulli (2 * k) : ℝ) / ((2 * k).factorial : ℝ) =
      (2 ^ (2 * k - 1) * Real.pi ^ (2 * k) / ((2 * k).factorial : ℝ)) * (bernoulli (2 * k) : ℝ) := by
    ring
  rw [hmul] at htsum_pos
  have hb_pos : 0 < (bernoulli (2 * k) : ℝ) := by
    by_contra hle
    push Not at hle
    have : (2 ^ (2 * k - 1) * Real.pi ^ (2 * k) / ((2 * k).factorial : ℝ)) * (bernoulli (2 * k) : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcoeff_pos.le hle
    linarith
  have h2k : 2 * k = 4 * j + 2 := by dsimp [k]; omega
  rwa [h2k] at hb_pos

-- Precomputed table of bernoulli 0 .. bernoulli 24, verified via `sum_bernoulli`.
private def bernTable : List ℚ :=
  [1, -1/2, 1/6, 0, -1/30, 0, 1/42, 0, -1/30, 0, 5/66, 0, -691/2730, 0,
   7/6, 0, -3617/510, 0, 43867/798, 0, -174611/330, 0, 854513/138, 0, -236364091/2730]

private def checkBernStep (m : ℕ) : Bool :=
  let s : ℚ := ((List.range (m + 1)).map fun k =>
    (((m + 1).choose k : ℕ) : ℚ) * bernTable.getD k 0).sum
  s == 0

private lemma checkBernAll :
    ((List.range 24).map (fun m => checkBernStep (m + 1))).all id = true := by
  decide +kernel

private lemma bernTable_eq_bernoulli : ∀ n : ℕ, n ≤ 24 → bernTable.getD n 0 = bernoulli n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hle
    cases n with
    | zero =>
      simp [bernTable, bernoulli_zero]
    | succ m =>
      have hstep : checkBernStep (m + 1) = true := by
        have h := checkBernAll
        simp only [List.all_eq_true, List.mem_map, List.mem_range, id_eq] at h
        exact h (checkBernStep (m + 1)) ⟨m, by omega, rfl⟩
      unfold checkBernStep at hstep
      rw [beq_iff_eq] at hstep
      have hsum_eq : ∑ k ∈ range (m + 2), (((m + 2).choose k : ℕ) : ℚ) * bernTable.getD k 0 = 0 := by
        have hlist : (∑ k ∈ range (m + 2), (((m + 2).choose k : ℕ) : ℚ) * bernTable.getD k 0) =
            ((List.range (m + 2)).map fun k => (((m + 2).choose k : ℕ) : ℚ) * bernTable.getD k 0).sum := by
          rw [← List.sum_toFinset _ (List.nodup_range)]
          simp [List.toFinset_range]
        rw [hlist]
        exact hstep
      have hbern := sum_bernoulli (m + 2)
      have hne : m + 2 ≠ 1 := by omega
      rw [if_neg hne] at hbern
      rw [Finset.sum_range_succ] at hsum_eq hbern
      have hprev : ∑ k ∈ range (m + 1), (((m + 2).choose k : ℕ) : ℚ) * bernTable.getD k 0 =
          ∑ k ∈ range (m + 1), (((m + 2).choose k : ℕ) : ℚ) * bernoulli k := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_range] at hk
        rw [ih k (by omega) (by omega)]
      rw [hprev] at hsum_eq
      have hcoeff : (((m + 2).choose (m + 1) : ℕ) : ℚ) ≠ 0 := by
        rw [Nat.choose_succ_self_right]
        exact Nat.cast_ne_zero.mpr (by omega)
      have hdiff : (((m + 2).choose (m + 1) : ℕ) : ℚ) * bernTable.getD (m + 1) 0 =
          (((m + 2).choose (m + 1) : ℕ) : ℚ) * bernoulli (m + 1) := by
        linarith
      exact mul_left_cancel₀ hcoeff hdiff

private lemma bernoulli_24 : bernoulli 24 = -236364091 / 2730 := by
  rw [← bernTable_eq_bernoulli 24 (le_refl 24)]
  rfl

end Mse3257373R1H1Proof

theorem OMA.solution : OMA.R_mse_3257373_R1.H1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    unfold OMA.S_mse_3257373.floorZetaNeg
    rw [Mse3257373R1H1Proof.re_riemannZeta_neg_nat (2 * k)]
    have hzero : bernoulli (2 * k + 1) = 0 := bernoulli_eq_zero_of_odd ⟨k, rfl⟩ (by omega)
    rw [hzero]
    simp
  · intro j
    unfold OMA.S_mse_3257373.floorZetaNeg
    rw [Mse3257373R1H1Proof.re_riemannZeta_neg_nat (4 * j + 1)]
    have hodd : Odd (4 * j + 1) := ⟨2 * j, by omega⟩
    rw [hodd.neg_one_pow]
    have hbpos : (0 : ℝ) < (bernoulli (4 * j + 2) : ℝ) :=
      Mse3257373R1H1Proof.bernoulli_pos_of_four_mul_add_two j
    have hden : (0 : ℝ) < ((4 * j + 1 + 1 : ℕ) : ℝ) := by positivity
    have hneg : (-1 : ℝ) * (bernoulli (4 * j + 1 + 1) : ℝ) / ((4 * j + 1 + 1 : ℕ) : ℝ) < 0 := by
      have : 4 * j + 1 + 1 = 4 * j + 2 := by omega
      rw [this]
      exact div_neg_of_neg_of_pos (by linarith) (by positivity)
    exact Int.floor_lt.mpr (by simpa using hneg)
  · unfold OMA.S_mse_3257373.floorZetaNeg
    rw [Mse3257373R1H1Proof.re_riemannZeta_neg_nat 23, Mse3257373R1H1Proof.bernoulli_24]
    rw [Int.floor_eq_iff]
    norm_num
