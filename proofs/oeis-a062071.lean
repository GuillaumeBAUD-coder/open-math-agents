import OMAStatements.S_oeis_a062071
import Mathlib

namespace A062071aux

open OMA.S_oeis_a062071 in
lemma two_pow_le (k : ℕ) : 2 ^ k ≤ denominator k := by
  unfold denominator
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num
  · calc 2 ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ (k + 1) ^ (k + 1) := Nat.pow_le_pow_left (by omega) _

open OMA.S_oeis_a062071 in
lemma den_pos (k : ℕ) : 0 < denominator k :=
  lt_of_lt_of_le (by positivity) (two_pow_le k)

open OMA.S_oeis_a062071 in
lemma den_pos' (k : ℕ) : (0 : ℝ) < (denominator k : ℝ) := by
  exact_mod_cast den_pos k

open OMA.S_oeis_a062071 in
lemma inv_le (k : ℕ) : 1 / (denominator k : ℝ) ≤ (1 / 2 : ℝ) ^ k := by
  rw [one_div_pow]
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast two_pow_le k

open OMA.S_oeis_a062071 in
lemma inv_nonneg (k : ℕ) : 0 ≤ 1 / (denominator k : ℝ) := by
  have := den_pos' k
  positivity

open OMA.S_oeis_a062071 in
lemma summ : Summable (fun k : ℕ => 1 / (denominator k : ℝ)) :=
  Summable.of_nonneg_of_le inv_nonneg inv_le summable_geometric_two

open OMA.S_oeis_a062071 in
lemma const_ge : 1 ≤ constantValue := by
  unfold constantValue
  have h := summ.le_tsum 0 (fun j _ => inv_nonneg j)
  have h0 : 1 / ((denominator 0 : ℕ) : ℝ) = 1 := by
    unfold denominator
    norm_num
  rw [h0] at h
  exact h

open OMA.S_oeis_a062071 in
lemma floor_le (n k : ℕ) :
    ((n / denominator k : ℕ) : ℝ) ≤ (n : ℝ) * (1 / (denominator k : ℝ)) := by
  rw [mul_one_div]
  exact Nat.cast_div_le

open OMA.S_oeis_a062071 in
lemma summ_floor (n : ℕ) : Summable (fun k : ℕ => ((n / denominator k : ℕ) : ℝ)) :=
  Summable.of_nonneg_of_le (fun _ => Nat.cast_nonneg _) (floor_le n) (summ.mul_left _)

open OMA.S_oeis_a062071 in
lemma upper (n : ℕ) : floorSum n ≤ (n : ℝ) * constantValue := by
  unfold floorSum constantValue
  rw [← tsum_mul_left]
  exact (summ_floor n).tsum_le_tsum (floor_le n) (summ.mul_left _)

open OMA.S_oeis_a062071 in
lemma floor_ge (n k : ℕ) :
    (n : ℝ) * (1 / (denominator k : ℝ)) - 1 ≤ ((n / denominator k : ℕ) : ℝ) := by
  have hd := den_pos' k
  have h1 : n < denominator k * (n / denominator k) + denominator k := by
    have e1 := Nat.div_add_mod n (denominator k)
    have e2 := Nat.mod_lt n (den_pos k)
    omega
  have h2 : (n : ℝ) < (denominator k : ℝ) * ((n / denominator k : ℕ) : ℝ)
      + (denominator k : ℝ) := by
    exact_mod_cast h1
  rw [mul_one_div, sub_le_iff_le_add, div_le_iff₀ hd]
  nlinarith

open OMA.S_oeis_a062071 in
lemma lower (n K : ℕ) :
    (n : ℝ) * (∑ k ∈ Finset.range K, 1 / (denominator k : ℝ)) - (K : ℝ) ≤ floorSum n := by
  have h1 : ∑ k ∈ Finset.range K, ((n / denominator k : ℕ) : ℝ) ≤ floorSum n :=
    (summ_floor n).sum_le_tsum (Finset.range K) (fun k _ => Nat.cast_nonneg _)
  have h2 : ∑ k ∈ Finset.range K, ((n : ℝ) * (1 / (denominator k : ℝ)) - 1)
      ≤ ∑ k ∈ Finset.range K, ((n / denominator k : ℕ) : ℝ) :=
    Finset.sum_le_sum (fun k _ => floor_ge n k)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at h2
  linarith

end A062071aux

theorem OMA.solution : type_of% @OMA.S_oeis_a062071.main := by
  have hc : (1 : ℝ) ≤ OMA.S_oeis_a062071.constantValue := A062071aux.const_ge
  rw [tendsto_order]
  constructor
  · intro a ha
    have hlim : Filter.Tendsto
        (fun K : ℕ => ∑ k ∈ Finset.range K, 1 / (OMA.S_oeis_a062071.denominator k : ℝ))
        Filter.atTop (nhds OMA.S_oeis_a062071.constantValue) :=
      A062071aux.summ.hasSum.tendsto_sum_nat
    have hlt : OMA.S_oeis_a062071.constantValue * ((1 + a) / 2)
        < OMA.S_oeis_a062071.constantValue := by nlinarith
    obtain ⟨K, hK⟩ := ((tendsto_order.1 hlim).1 _ hlt).exists
    rw [Filter.eventually_atTop]
    have hpos : 0 < OMA.S_oeis_a062071.constantValue * (1 - a) := by nlinarith
    refine ⟨⌈2 * (K : ℝ) / (OMA.S_oeis_a062071.constantValue * (1 - a))⌉₊ + 1, fun n hn => ?_⟩
    have hn1 : ((⌈2 * (K : ℝ) / (OMA.S_oeis_a062071.constantValue * (1 - a))⌉₊ : ℕ) : ℝ) + 1
        ≤ (n : ℝ) := by exact_mod_cast hn
    have hn2 := Nat.le_ceil (2 * (K : ℝ) / (OMA.S_oeis_a062071.constantValue * (1 - a)))
    have hn4 : 2 * (K : ℝ) / (OMA.S_oeis_a062071.constantValue * (1 - a)) ≤ (n : ℝ) := by
      linarith
    have hn3 : 2 * (K : ℝ) ≤ (n : ℝ) * (OMA.S_oeis_a062071.constantValue * (1 - a)) :=
      (div_le_iff₀ hpos).1 hn4
    have hceil : (0 : ℝ) ≤
        ((⌈2 * (K : ℝ) / (OMA.S_oeis_a062071.constantValue * (1 - a))⌉₊ : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlow := A062071aux.lower n K
    have hK' := mul_lt_mul_of_pos_left hK hnpos
    have hcn : 0 < OMA.S_oeis_a062071.constantValue * (n : ℝ) := by positivity
    rw [lt_div_iff₀ hcn]
    nlinarith
  · intro b hb
    rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcn : 0 < OMA.S_oeis_a062071.constantValue * (n : ℝ) := by positivity
    rw [div_lt_iff₀ hcn]
    have hup := A062071aux.upper n
    nlinarith
