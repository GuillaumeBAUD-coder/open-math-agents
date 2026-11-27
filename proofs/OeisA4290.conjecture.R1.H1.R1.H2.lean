import OMAReductions.R_OeisA4290_conjecture_R1_H1_R1

-- Short repunits: if 9n divides 10^t - 1 with t below 9k, the repunit with t digits is a 0/1 multiple of n.
-- Original proof (no external source). A slice of the open question on OEIS A004290, not the question itself.

namespace OMA.A4290slice
open Finset

lemma digits01 : ∀ (L : ℕ) (f : ℕ → ℕ), (∀ i, f i ≤ 1) →
    ∀ d ∈ Nat.digits 10 (∑ i ∈ range L, f i * 10 ^ i), d = 0 ∨ d = 1 := by
  intro L
  induction L with
  | zero => intro f hf d hd; simp at hd
  | succ L ih =>
    intro f hf d hd
    rw [sum_range_succ'] at hd
    have e : ∑ i ∈ range L, f (i + 1) * 10 ^ (i + 1)
        = 10 * ∑ i ∈ range L, f (i + 1) * 10 ^ i := by
      rw [mul_sum]; apply sum_congr rfl; intro i _; ring
    rw [e, pow_zero, mul_one] at hd
    by_cases h0 : 10 * ∑ i ∈ range L, f (i + 1) * 10 ^ i + f 0 = 0
    · rw [h0] at hd; simp at hd
    · rw [Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero h0)] at hd
      have hf0 := hf 0
      have e1 : (10 * ∑ i ∈ range L, f (i + 1) * 10 ^ i + f 0) % 10 = f 0 := by omega
      have e2 : (10 * ∑ i ∈ range L, f (i + 1) * 10 ^ i + f 0) / 10
          = ∑ i ∈ range L, f (i + 1) * 10 ^ i := by omega
      rw [e1, e2] at hd
      rcases List.mem_cons.mp hd with h | h
      · omega
      · exact ih (fun i => f (i + 1)) (fun i => hf (i + 1)) d h

lemma geom10 (L : ℕ) : ∑ i ∈ range L, 10 ^ i = (10 ^ L - 1) / 9 := by
  have := Nat.geomSum_eq (m := 10) (by norm_num) L
  simpa using this

lemma nine_mul_geom10 (L : ℕ) : 9 * ∑ i ∈ range L, 10 ^ i = 10 ^ L - 1 := by
  rw [geom10]
  exact Nat.mul_div_cancel' (by simpa using Nat.sub_one_dvd_pow_sub_one 10 L)

theorem slice2 (k n t : ℕ) (_hn : 0 < n) (_hlt : n < 10 ^ k - 1) (ht0 : 0 < t) (htk : t < 9 * k)
    (hdvd : 9 * n ∣ 10 ^ t - 1) :
    ∃ m < (10 ^ (9 * k) - 1) / 9, 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 := by
  refine ⟨∑ i ∈ range t, 10 ^ i, ?_, ?_, ?_, ?_⟩
  · rw [← geom10]
    exact sum_lt_sum_of_subset (range_mono htk.le) (i := t) (mem_range.mpr htk) (by simp)
      (by positivity) (fun _ _ _ => Nat.zero_le _)
  · exact sum_pos (fun i _ => by positivity) ⟨0, mem_range.mpr ht0⟩
  · exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 9) (by rw [nine_mul_geom10]; exact hdvd)
  · have := digits01 t (fun _ => 1) (fun _ => le_rfl)
    simpa using this


end OMA.A4290slice

theorem OMA.solution : OMA.R_OeisA4290_conjecture_R1_H1_R1.H2 := by
  intro k n t hn hlt ht0 htk hdvd
  exact OMA.A4290slice.slice2 k n t hn hlt ht0 htk hdvd
