import FormalConjectures.ErdosProblems.«422»
import Mathlib

-- Credit: @Iraeeee

open Filter

namespace HofstadterGrowth

/-- Looking one step ahead bounds the current value by its index. -/
theorem le_index (f : ℕ+ → ℕ+) (hf : Erdos422.IsHofstadterQ f) (n : ℕ+) : f n ≤ n := by
  by_cases hn : n = 1
  · simp [hn, hf.1]
  have h : (2 : ℕ+) < n + 1 := by
    change 2 < (n : ℕ) + 1
    have := n.pos
    have hn' : (n : ℕ) ≠ 1 := fun e => hn (PNat.eq e)
    omega
  have hprev := (hf.2.2 (n + 1) h).1
  rw [PNat.add_sub] at hprev
  change (f n : ℕ) < (n : ℕ) + 1 at hprev
  exact Nat.le_of_lt_succ hprev

/-- Every slope above one half also bounds arbitrarily late terms from above. -/
theorem below_slope (f : ℕ+ → ℕ+) (hf : Erdos422.IsHofstadterQ f)
    (c : ℝ) (hc : 1/2 < c) (M : ℕ+) :
    ∃ n ≥ M, (f n : ℝ) < c * (n : ℝ) := by
  by_contra! h
  have pos (n : ℕ+) : 0 < (n : ℝ) := by exact_mod_cast n.pos
  have upper (n : ℕ+) : (f n : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_index f hf n
  have hc1 : c ≤ 1 := by
    by_contra! hh
    nlinarith [h M le_rfl, upper M, mul_pos (sub_pos.mpr hh) (pos M)]
  let N : ℕ+ := M + 2
  let r : ℝ := 2*(1-c)
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have sumIndices (n : ℕ+) (hn : N ≤ n) :
      ∃ i j : ℕ+, f n = f i + f j ∧ (i : ℝ) + (j : ℝ) ≤ r*(n : ℝ) + 3*c := by
    have hn2 : (2 : ℕ+) < n := (PNat.lt_add_left 2 M).trans_le hn
    obtain ⟨h1,h2,he⟩ := hf.2.2 n hn2
    have child (d : ℕ+) (hd : d ≤ 2) (hfd : f (n-d) < n) :
        ((n-f (n-d) : ℕ+) : ℝ) ≤ (1-c)*(n : ℝ) + c*(d : ℝ) := by
      have heNat : ((n-d : ℕ+) : ℕ) + (d : ℕ) = (n : ℕ) := by
        exact_mod_cast PNat.sub_add_of_lt (hd.trans_lt hn2)
      have hM : M ≤ n-d := by
        change (M : ℕ) + 2 ≤ (n : ℕ) at hn
        change (d : ℕ) ≤ 2 at hd
        change (M : ℕ) ≤ ((n-d : ℕ+) : ℕ)
        omega
      have heReal : ((n-d : ℕ+) : ℝ) + (d : ℝ) = (n : ℝ) := by exact_mod_cast heNat
      have hfReal : ((n-f (n-d) : ℕ+) : ℝ) + (f (n-d) : ℝ) = (n : ℝ) := by
        exact_mod_cast PNat.sub_add_of_lt hfd
      linarith [h (n-d) hM, congrArg (c * ·) heReal]
    refine ⟨_, _, he, ?_⟩
    have hsum := add_le_add (child 1 (by decide) h1) (child 2 le_rfl h2)
    norm_num at hsum
    dsimp [r]
    linarith
  have shrink (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ+, (f n : ℝ) ≤ r^k*(n : ℝ) + C := by
    induction k with
    | zero => exact ⟨0, le_rfl, fun n => by simpa using upper n⟩
    | succ k IH =>
      obtain ⟨C,hC,hB⟩ := IH
      have hpow := pow_nonneg hr0 k
      have hc0 : 0 ≤ c := by linarith
      refine ⟨(N : ℝ) + 3*c*r^k + 2*C, by positivity, fun n => ?_⟩
      by_cases hn : N ≤ n
      · obtain ⟨i,j,he,hs⟩ := sumIndices n hn
        have hfr : (f n : ℝ) = (f i : ℝ) + (f j : ℝ) := by exact_mod_cast he
        rw [hfr, pow_succ]
        nlinarith [add_le_add (hB i) (hB j), mul_le_mul_of_nonneg_left hs hpow, pos N]
      · have hsmall : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_of_not_ge hn)
        have hz : 0 ≤ r^(k+1)*(n : ℝ) + 3*c*r^k + 2*C := by positivity
        linarith [upper n]
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (by linarith : 0 < c) hr1
  obtain ⟨C,_,hC⟩ := shrink k
  obtain ⟨t,ht⟩ := exists_nat_gt (C / (c-r^k))
  let n : ℕ+ := M + ⟨t+1, by omega⟩
  have hMn : M ≤ n := (PNat.lt_add_right ..).le
  have htn : (t : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show t ≤ (M : ℕ) + (t+1) by omega)
  have hbig := (div_lt_iff₀ (sub_pos.mpr hk)).mp (ht.trans_le htn)
  nlinarith [h n hMn, hC n]

end HofstadterGrowth

noncomputable def OMA.answer : ℕ+ → ℝ := fun n => n

theorem OMA.solution : Erdos422.erdos_422.variants.growth_rate.answer = OMA.answer → type_of% @Erdos422.erdos_422.variants.growth_rate := by
  intro h f hf
  rw [h]
  apply Asymptotics.IsBigO.of_bound 1
  exact Filter.Eventually.of_forall fun n => by
    have hl : (f n : ℝ) ≤ (n : ℝ) := by exact_mod_cast HofstadterGrowth.le_index f hf n
    simpa [OMA.answer, Real.norm_eq_abs] using hl
