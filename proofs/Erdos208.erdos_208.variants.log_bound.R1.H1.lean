import OMAReductions.R_Erdos208_erdos_208_variants_log_bound_R1
import Mathlib.Data.Int.CardIntervalMod

/-! Combining counts of multiples over the small square divisors gives
a uniform bound by seven eighths of the interval length. -/

open Finset

namespace OMA.SquarefreeSmallSquareSieve

private theorem inv_square_sum (L : ℕ) :
    ∑ k ∈ Finset.Icc 2 L, (1 : ℚ) / ((k : ℚ) * k) ≤ 3 / 4 := by
  by_cases hL : L < 2
  · rw [Finset.Icc_eq_empty_of_lt hL, Finset.sum_empty]
    norm_num
  have hstrong (N : ℕ) (hN : 2 ≤ N) :
      ∑ k ∈ Finset.Icc 2 N, (1 : ℚ) / ((k : ℚ) * k) ≤ 3 / 4 - 1 / (N : ℚ) := by
    induction N with
    | zero => omega
    | succ N ih =>
      by_cases hn : N < 2
      · have hN' : N = 1 := by omega
        subst N
        norm_num
      have hIcc : Finset.Icc 2 (N + 1) = insert (N + 1) (Finset.Icc 2 N) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hIcc, Finset.sum_insert (by simp)]
      have hrec := ih (by omega)
      have hq : 0 < (N : ℚ) := by exact_mod_cast (by omega : 0 < N)
      have hinv : (1 : ℚ) / ((N + 1 : ℕ) * ((N + 1 : ℕ) : ℚ)) ≤
          1 / (N : ℚ) - 1 / ((N + 1 : ℕ) : ℚ) := by
        push_cast
        field_simp
        nlinarith
      linarith
  refine (hstrong L (by omega)).trans ?_
  have hnonneg : (0 : ℚ) ≤ 1 / L := by positivity
  linarith

private theorem count_multiples (x H d : ℕ) (hd : 0 < d) :
    ((#{y ∈ Finset.Ioc x (x + H) | d ∣ y} : ℕ) : ℚ) ≤ (H : ℚ) / d + 1 := by
  have he : {y ∈ Finset.Ioc x (x + H) | d ∣ y} =
      {y ∈ Finset.Ioc x (x + H) | y ≡ 0 [MOD d]} := by
    ext y
    simp [Nat.modEq_zero_iff_dvd]
  have hcard := Nat.Ioc_filter_modEq_card x (x + H) hd 0
  rw [← he] at hcard
  simp only [Nat.cast_zero, sub_zero] at hcard
  have hupper := Int.floor_le (((x + H : ℕ) : ℚ) / (d : ℚ))
  have hlower := Int.lt_floor_add_one ((x : ℚ) / (d : ℚ))
  have hnonneg : (0 : ℚ) ≤ (H : ℚ) / (d : ℚ) := by positivity
  rcases max_cases
      (⌊((x + H : ℕ) : ℚ) / (d : ℚ)⌋ - ⌊(x : ℚ) / (d : ℚ)⌋) (0 : ℤ)
      with h | h
  · rw [h.1] at hcard
    have hc := congrArg (fun z : ℤ => (z : ℚ)) hcard
    push_cast at hc hupper
    rw [add_div] at hc hupper
    linarith
  · rw [h.1] at hcard
    have hz : (#{y ∈ Finset.Ioc x (x + H) | d ∣ y} : ℕ) = 0 := by exact_mod_cast hcard
    rw [hz, Nat.cast_zero]
    linarith

theorem small_square_count (x L : ℕ) :
    #{y ∈ Finset.Ioc x (x + 8 * L) |
      ∃ d ∈ Finset.Icc 2 L, d * d ∣ y} ≤ 7 * L := by
  let I := Finset.Ioc x (x + 8 * L)
  have hEq : {y ∈ I | ∃ d ∈ Finset.Icc 2 L, d * d ∣ y} =
      (Finset.Icc 2 L).biUnion (fun d => I.filter (fun y => d * d ∣ y)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    aesop
  change #({y ∈ I | ∃ d ∈ Finset.Icc 2 L, d * d ∣ y}) ≤ 7 * L
  rw [hEq]
  apply Finset.card_biUnion_le.trans
  suffices h : (∑ d ∈ Finset.Icc 2 L, ((I.filter (fun y => d * d ∣ y)).card : ℚ)) ≤
      7 * (L : ℚ) by exact_mod_cast h
  have hb : (∑ d ∈ Finset.Icc 2 L, ((I.filter (fun y => d * d ∣ y)).card : ℚ)) ≤
      ∑ d ∈ Finset.Icc 2 L, ((8 * (L : ℚ)) * (1 / ((d : ℚ) * d)) + 1) := by
    apply Finset.sum_le_sum
    intro d hd
    have hd2 := (Finset.mem_Icc.mp hd).1
    have h := count_multiples x (8 * L) (d * d) (by positivity)
    simpa [I, Nat.cast_mul, div_eq_mul_inv] using h
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one] at hb
  have hcard : (Finset.Icc 2 L).card ≤ L := by rw [Nat.card_Icc]; omega
  have hcardq : ((Finset.Icc 2 L).card : ℚ) ≤ L := by exact_mod_cast hcard
  have hs := mul_le_mul_of_nonneg_left (inv_square_sum L) (by positivity : 0 ≤ 8 * (L : ℚ))
  linarith

end OMA.SquarefreeSmallSquareSieve

theorem OMA.solution : OMA.R_Erdos208_erdos_208_variants_log_bound_R1.H1 :=
  OMA.SquarefreeSmallSquareSieve.small_square_count
