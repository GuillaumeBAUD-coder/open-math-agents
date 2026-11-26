import FormalConjectures.OEIS.«189286»

-- Problem: Normalized convolution of $\binom{6k}{3k}\binom{3k}{k}$ — conjecture 2
-- Upstream: formal-conjectures FormalConjectures/OEIS/189286.lean (declaration OeisA189286.conjecture_2)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Topology

namespace OMAProof

/-- The integer term `C(6k,3k) C(3k,k)`. -/
def T (k : ℕ) : ℕ := (6 * k).choose (3 * k) * (3 * k).choose k

/-- The convolution sum. -/
def S (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), T k * T (n - k)

lemma a_eq (n : ℕ) :
    (OeisA189286.a n : ℝ) = (S n : ℝ) / ((2 * (n : ℝ) - 1) * ((3 * n).choose n : ℝ)) := by
  have : OeisA189286.a n = (S n : ℚ) / ((2 * (n : ℚ) - 1) * ((3 * n).choose n : ℚ)) := by
    simp [OeisA189286.a, OeisA189286.tTerm, S, T]
  rw [this]
  push_cast
  rfl

lemma vand (n k : ℕ) (hk : k ≤ n) :
    (3 * k).choose k * (3 * (n - k)).choose (n - k) ≤ (3 * n).choose n := by
  have h3 : 3 * n = 3 * k + 3 * (n - k) := by omega
  rw [h3, Nat.add_choose_eq]
  refine Finset.single_le_sum
    (f := fun ij : ℕ × ℕ => (3 * k).choose ij.1 * (3 * (n - k)).choose ij.2)
    (fun _ _ => Nat.zero_le _)
    (show (k, n - k) ∈ Finset.HasAntidiagonal.antidiagonal n from
      Finset.HasAntidiagonal.mem_antidiagonal.mpr (by show k + (n - k) = n; omega))

lemma S_upper (n : ℕ) : S n ≤ (n + 1) * (64 ^ n * (3 * n).choose n) := by
  have : ∀ k ∈ Finset.range (n + 1), T k * T (n - k) ≤ 64 ^ n * (3 * n).choose n := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 : (6 * k).choose (3 * k) * (6 * (n - k)).choose (3 * (n - k)) ≤ 64 ^ n := by
      calc _ ≤ 2 ^ (6 * k) * 2 ^ (6 * (n - k)) :=
            Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (Nat.choose_le_two_pow _ _)
        _ = 64 ^ n := by
          rw [← pow_add, show 6 * k + 6 * (n - k) = 6 * n by omega, pow_mul]; norm_num
    calc T k * T (n - k)
        = ((6 * k).choose (3 * k) * (6 * (n - k)).choose (3 * (n - k))) *
          ((3 * k).choose k * (3 * (n - k)).choose (n - k)) := by unfold T; ring
      _ ≤ 64 ^ n * (3 * n).choose n := Nat.mul_le_mul h1 (vand n k hk')
  calc S n ≤ ∑ k ∈ Finset.range (n + 1), 64 ^ n * (3 * n).choose n := Finset.sum_le_sum this
    _ = _ := by simp

lemma S_lower (n : ℕ) : T n ≤ S n := by
  have hmem : n ∈ Finset.range (n + 1) := Finset.self_mem_range_succ n
  calc T n = T n * T (n - n) := by simp [T]
    _ ≤ S n := Finset.single_le_sum (f := fun k => T k * T (n - k))
      (fun _ _ => Nat.zero_le _) hmem

lemma central (n : ℕ) : 64 ^ n ≤ (6 * n + 1) * (6 * n).choose (3 * n) := by
  have := Nat.four_pow_le_two_mul_add_one_mul_central_binom (3 * n)
  have e1 : (4 : ℕ) ^ (3 * n) = 64 ^ n := by rw [pow_mul]; norm_num
  rw [e1] at this
  calc 64 ^ n ≤ (2 * (3 * n) + 1) * (2 * (3 * n)).choose (3 * n) := this
    _ = (6 * n + 1) * (6 * n).choose (3 * n) := by ring_nf

lemma a_upper (n : ℕ) (hn : 1 ≤ n) : (OeisA189286.a n : ℝ) ≤ 2 * 64 ^ n := by
  rw [a_eq]
  have hc : (0 : ℝ) < (3 * n).choose n := by exact_mod_cast Nat.choose_pos (by omega)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (0 : ℝ) < (2 * (n : ℝ) - 1) * ((3 * n).choose n : ℝ) := by
    apply mul_pos <;> linarith
  rw [div_le_iff₀ hd]
  have hS : (S n : ℝ) ≤ (n + 1) * (64 ^ n * (3 * n).choose n) := by exact_mod_cast S_upper n
  have h64 : (0 : ℝ) ≤ 64 ^ n * (3 * n).choose n := by positivity
  nlinarith

lemma a_lower (n : ℕ) (hn : 1 ≤ n) :
    (64 : ℝ) ^ n / (14 * (n : ℝ) ^ 2) ≤ OeisA189286.a n := by
  rw [a_eq]
  have hc : (0 : ℝ) < (3 * n).choose n := by exact_mod_cast Nat.choose_pos (by omega)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (0 : ℝ) < (2 * (n : ℝ) - 1) * ((3 * n).choose n : ℝ) := by
    apply mul_pos <;> linarith
  rw [le_div_iff₀ hd, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have hS : ((6 * n).choose (3 * n) : ℝ) * (3 * n).choose n ≤ S n := by
    exact_mod_cast S_lower n
  have hC : (64 : ℝ) ^ n ≤ (6 * n + 1) * (6 * n).choose (3 * n) := by
    exact_mod_cast central n
  have hB : (0 : ℝ) ≤ (6 * n).choose (3 * n) := by positivity
  have k1 : (64 : ℝ) ^ n * ((2 * n - 1) * (3 * n).choose n) ≤
      (6 * n + 1) * (6 * n).choose (3 * n) * ((2 * n - 1) * (3 * n).choose n) :=
    mul_le_mul_of_nonneg_right hC hd.le
  have k2 : (6 * (n : ℝ) + 1) * (2 * n - 1) ≤ 14 * n ^ 2 := by nlinarith
  have k3 : (6 * (n : ℝ) + 1) * (6 * n).choose (3 * n) * ((2 * n - 1) * (3 * n).choose n) ≤
      14 * n ^ 2 * ((6 * n).choose (3 * n) * (3 * n).choose n) := by
    have := mul_le_mul_of_nonneg_right k2 (mul_nonneg hB hc.le)
    nlinarith
  have k4 : 14 * (n : ℝ) ^ 2 * ((6 * n).choose (3 * n) * (3 * n).choose n) ≤
      14 * n ^ 2 * S n :=
    mul_le_mul_of_nonneg_left hS (by positivity)
  nlinarith

lemma root_tendsto (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => c ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hcont : Tendsto (fun x : ℝ => c ^ x) (𝓝 0) (𝓝 (c ^ (0 : ℝ))) :=
    (Real.continuous_const_rpow hc.ne').tendsto 0
  rw [Real.rpow_zero] at hcont
  exact hcont.comp h

lemma nroot_tendsto : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 1) :=
  tendsto_rpow_div.comp tendsto_natCast_atTop_atTop

end OMAProof

open OMAProof in
theorem OMA.solution : type_of% @OeisA189286.conjecture_2 := by
  have hpow : ∀ n : ℕ, 1 ≤ n → ((64 : ℝ) ^ n) ^ (1 / (n : ℝ)) = 64 := by
    intro n hn
    rw [one_div]
    exact Real.pow_rpow_inv_natCast (by norm_num) (by omega)
  have hL : Tendsto (fun n : ℕ => 64 / ((14 : ℝ) ^ (1 / (n : ℝ)) *
      ((n : ℝ) ^ (1 / (n : ℝ))) ^ 2)) atTop (𝓝 64) := by
    have := ((root_tendsto 14 (by norm_num)).mul (nroot_tendsto.pow 2))
    have h2 := (tendsto_const_nhds (x := (64 : ℝ))).div this (by norm_num)
    rw [show (64 : ℝ) / (1 * 1 ^ 2) = 64 by norm_num] at h2
    exact h2
  have hU : Tendsto (fun n : ℕ => (2 : ℝ) ^ (1 / (n : ℝ)) * 64) atTop (𝓝 64) := by
    simpa using (root_tendsto 2 (by norm_num)).mul_const (64 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hlo := a_lower n hn
    have hpos : (0 : ℝ) ≤ (64 : ℝ) ^ n / (14 * (n : ℝ) ^ 2) := by positivity
    calc 64 / ((14 : ℝ) ^ (1 / (n : ℝ)) * ((n : ℝ) ^ (1 / (n : ℝ))) ^ 2)
        = ((64 : ℝ) ^ n / (14 * (n : ℝ) ^ 2)) ^ (1 / (n : ℝ)) := by
          rw [Real.div_rpow (by positivity) (by positivity), hpow n hn,
            Real.mul_rpow (by norm_num) (by positivity)]
          congr 2
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hn'.le,
            ← Real.rpow_mul hn'.le, mul_comm]
      _ ≤ (OeisA189286.a n : ℝ) ^ (1 / (n : ℝ)) :=
          Real.rpow_le_rpow hpos hlo (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hlo := a_lower n hn
    have hpos : (0 : ℝ) ≤ (64 : ℝ) ^ n / (14 * (n : ℝ) ^ 2) := by positivity
    calc (OeisA189286.a n : ℝ) ^ (1 / (n : ℝ)) ≤ (2 * (64 : ℝ) ^ n) ^ (1 / (n : ℝ)) :=
          Real.rpow_le_rpow (hpos.trans hlo) (a_upper n hn) (by positivity)
      _ = (2 : ℝ) ^ (1 / (n : ℝ)) * 64 := by
          rw [Real.mul_rpow (by norm_num) (by positivity), hpow n hn]
