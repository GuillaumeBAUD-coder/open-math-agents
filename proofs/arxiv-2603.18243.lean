import OMAStatements.S_arxiv_2603_18243
import Mathlib

/-!
# Refutation of Hyman's Conjecture 3.17

Credit: @rleshner
Source: https://arxiv.org/abs/2603.18243

At every fixed positive sample depth, there are intervals of bases directly
above powers of ten on which the next continued-fraction digit is large
enough for persistence. The intervals have a fixed positive relative length.
If the natural density were 1/12, subtracting the two endpoint counts would
give asymptotic density 1/12 inside these intervals, although every base
in them is persistent.
-/

open OMA.S_arxiv_2603_18243 Filter
open scoped Topology

/-- Immediately to the right of every sufficiently large power of ten the
first partial quotient already exceeds the persistence threshold. -/
private theorem persistentBlocks (N : ℕ) (hN : 1 ≤ N) :
    ∃ A : ℕ, 0 < A ∧ ∀ k b : ℕ, A * 10 ^ k < b → b ≤ (A + 2) * 10 ^ k →
      persistent N b := by
  obtain ⟨T, hT⟩ := exists_nat_gt (max 1 ((N : ℝ) * Real.log N))
  have hT1 : (1 : ℝ) < T := lt_of_le_of_lt (le_max_left _ _) hT
  have hTN : (N : ℝ) * Real.log N < T := lt_of_le_of_lt (le_max_right _ _) hT
  have hT0 : (0 : ℝ) < T := by linarith
  let v : ℝ := (10 : ℝ) ^ (1 / (T : ℝ))
  have hv : 1 < v := Real.one_lt_rpow (by norm_num) (by positivity)
  obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt (2 / (v - 1)) (by norm_num : (1 : ℝ) < 10)
  have hwidth := (div_lt_iff₀ (by linarith : 0 < v - 1)).mp hs
  refine ⟨10 ^ s, by positivity, ?_⟩
  intro k b hlo hhi
  have hl : (10 : ℝ) ^ s * 10 ^ k < b := by exact_mod_cast hlo
  have hu : (b : ℝ) ≤ ((10 : ℝ) ^ s + 2) * 10 ^ k := by exact_mod_cast hhi
  let x : ℝ := b / (10 : ℝ) ^ (s + k)
  have hp : (0 : ℝ) < 10 ^ (s + k) := by positivity
  have hx : 1 < x := by
    change 1 < (b : ℝ) / 10 ^ (s + k)
    rw [lt_div_iff₀ hp, one_mul, pow_add]
    exact hl
  have hxv : x < v := by
    apply (div_lt_iff₀ hp).mpr
    rw [pow_add, ← mul_assoc]
    apply lt_of_le_of_lt hu (mul_lt_mul_of_pos_right _ (by positivity))
    linarith
  let f := Real.logb 10 x
  have hf : 0 < f := Real.logb_pos (by norm_num) hx
  have hft : f < 1 / (T : ℝ) :=
    (Real.logb_lt_iff_lt_rpow (by norm_num) (by linarith : 0 < x)).mpr hxv
  have hf1 : f < 1 := hft.trans ((div_lt_one hT0).mpr hT1)
  have hfrac : Int.fract (Real.logb 10 (b : ℝ)) = f := by
    have hb : (0 : ℝ) < b := lt_trans (by positivity) hl
    have he : Real.logb 10 (b : ℝ) = f + ((s + k : ℕ) : ℝ) := by
      dsimp [f, x]
      rw [Real.logb_div hb.ne' hp.ne', Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      ring
    rw [he, Int.fract_add_natCast, Int.fract_eq_self.mpr ⟨hf.le, hf1⟩]
  have hprod : (T : ℝ) * f < 1 := by
    have := (lt_div_iff₀ hT0).mp hft
    linarith
  have hd : T ≤ digit (Real.logb 10 (b : ℝ)) 1 := by
    apply Nat.le_floor
    change (T : ℝ) ≤ (Int.fract (Real.logb 10 (b : ℝ)))⁻¹
    rw [hfrac, ← one_div, le_div_iff₀ hf]
    exact hprod.le
  refine ⟨0, ?_, hN, ?_⟩
  · intro j hj
    obtain rfl : j = 0 := by omega
    simpa [completeQuotient, hfrac] using hf.ne'
  · simpa [denominatorPair] using hTN.trans_le (Nat.cast_le.mpr hd)

private theorem persistentBlocksNotTwelfth (F : ℕ → ℕ) (q : ℕ) (hq : 0 < q)
    (blocks : ∀ K : ℕ, ∃ C : ℕ, K ≤ C ∧ F (q*C) + C ≤ F ((q+1)*C)) :
    ¬ Tendsto (fun B : ℕ => (F B : ℝ) / (B : ℝ)) atTop (𝓝 (1/12 : ℝ)) := by
  intro h
  let ε : ℝ := 1 / (24 * (2*(q:ℝ)+1))
  have he : 0 < ε := by dsimp [ε]; positivity
  have hmul : ε*(2*(q:ℝ)+1) = 1/24 := by
    dsimp [ε]
    field_simp
  obtain ⟨K,hK⟩ := Metric.tendsto_atTop.mp h ε he
  obtain ⟨C,hC,hi⟩ := blocks (K+2)
  have hA : C ≤ q*C := Nat.le_mul_of_pos_left _ hq
  have hB : C ≤ (q+1)*C := Nat.le_mul_of_pos_left _ (by omega)
  have bounds (x : ℕ) (hx : C ≤ x) :
      (1/12 - ε)*(x:ℝ) < F x ∧ (F x:ℝ) < (1/12 + ε)*(x:ℝ) := by
    have hh := hK x (by omega)
    rw [Real.dist_eq, abs_lt] at hh
    have xpos : 0 < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
    exact ⟨(lt_div_iff₀ xpos).mp (by linarith [hh.1] : 1/12 - ε < (F x:ℝ) / (x:ℝ)),
      (div_lt_iff₀ xpos).mp (by linarith [hh.2] : (F x:ℝ) / (x:ℝ) < 1/12 + ε)⟩
  have lo := (bounds _ hA).1
  have up := (bounds _ hB).2
  push_cast at lo up
  have comp : (F (q*C) : ℝ) + (C:ℝ) ≤ (F ((q+1)*C) : ℝ) := by exact_mod_cast hi
  have cpos : (0:ℝ) < C := by exact_mod_cast (by omega : 0 < C)
  nlinarith [congrArg (fun x : ℝ => x*(C:ℝ)) hmul]

private theorem persistentBlockObstruction (P : ℕ → Prop) (A : ℕ) (hA : 0 < A)
    (hb : ∀ k b : ℕ, A*10^k < b → b ≤ (A+2)*10^k → P b) :
    ¬ Tendsto (fun n : ℕ => (blockCount P n : ℝ) / (n : ℝ)) atTop (𝓝 (1/12 : ℝ)) := by
  classical
  apply persistentBlocksNotTwelfth (blockCount P) A hA
  intro K
  let C : ℕ := 10^K
  have hC : 0 < C := pow_pos (by decide) _
  refine ⟨C, (Nat.lt_pow_self (by decide : 1 < 10)).le, ?_⟩
  have hp (i : ℕ) (hi : i ∈ Finset.range C) : P (A*C+i+2) := by
    have h := Finset.mem_range.mp hi
    apply hb K
    · change A*C < A*C+i+2; omega
    · change A*C+i+2 ≤ (A+2)*C
      rw [Nat.add_mul]; omega
  rw [Nat.add_mul, Nat.one_mul]
  simp only [blockCount, Finset.sum_range_add]
  have : (∑ i ∈ Finset.range C, if P (A*C+i+2) then 1 else 0) = C := by
    calc
      _ = ∑ _i ∈ Finset.range C, 1 := Finset.sum_congr rfl fun i hi => if_pos (hp i hi)
      _ = _ := by simp
  omega

private theorem noTwelfthAtFixedDepth (N : ℕ) (hN : 1 ≤ N) :
    ¬ Tendsto (fun n : ℕ => (blockCount (persistent N) n : ℝ) / (n : ℝ))
      atTop (𝓝 (1/12 : ℝ)) := by
  obtain ⟨A, hA, hb⟩ := persistentBlocks N hN
  exact persistentBlockObstruction (persistent N) A hA hb

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2603_18243.main) := by
  exact noTwelfthAtFixedDepth 10000 (by decide)
