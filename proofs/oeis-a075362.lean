import OMAStatements.S_oeis_a075362
import Mathlib

namespace OMA.A075362proof

open OMA.S_oeis_a075362

lemma antidiag_eq (m : ℕ) (hm : 1 ≤ m) :
    (antidiag m : ℤ) = ∑ k ∈ Finset.range (m / 2 + 1), ((m : ℤ) - k) * k := by
  unfold antidiag tri
  rw [← Finset.sum_filter]
  have hf : (Finset.range m).filter (fun k => 2 * k ≤ m) = Finset.range (m / 2 + 1) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hf]; push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [Nat.cast_sub (by omega)]

lemma sum_eq (m : ℤ) (q : ℕ) :
    6 * ∑ k ∈ Finset.range (q + 1), (m - k) * k =
      3 * m * q * (q + 1) - q * (q + 1) * (2 * q + 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, mul_add, ih]; push_cast; ring

theorem a075362 : type_of% @OMA.S_oeis_a075362.main := by
  intro n hn
  unfold a023855
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [if_neg (by omega)]
    have h := antidiag_eq (2 * t + 1) (by omega)
    rw [show (2 * t + 1) / 2 = t by omega] at h
    have hs := sum_eq ((2 * t + 1 : ℕ) : ℤ) t
    rw [← h] at hs
    symm; apply Nat.div_eq_of_eq_mul_left (by norm_num)
    have : ((2 * t * (2 * t + 1) * (2 * t + 2) : ℕ) : ℤ) = ((antidiag (2 * t + 1) * 12 : ℕ) : ℤ) := by
      push_cast at hs ⊢; linear_combination (-2) * hs
    exact_mod_cast this
  · rw [if_pos (by omega)]
    have h := antidiag_eq (2 * t + 1 + 1) (by omega)
    rw [show (2 * t + 1 + 1) / 2 = t + 1 by omega] at h
    have hs := sum_eq ((2 * t + 1 + 1 : ℕ) : ℤ) (t + 1)
    rw [← h] at hs
    symm; apply Nat.div_eq_of_eq_mul_left (by norm_num)
    have : (((2 * t + 1 + 1) * (2 * t + 1 + 3) * (2 * (2 * t + 1) + 1) : ℕ) : ℤ) =
        ((antidiag (2 * t + 1 + 1) * 24 : ℕ) : ℤ) := by
      push_cast at hs ⊢; linear_combination (-4) * hs
    exact_mod_cast this

end OMA.A075362proof

theorem OMA.solution : type_of% @OMA.S_oeis_a075362.main := OMA.A075362proof.a075362
