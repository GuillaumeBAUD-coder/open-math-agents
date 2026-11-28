import OMAStatements.S_oeis_a376360
import Mathlib

open OMA.S_oeis_a376360

namespace P376360

lemma sq579 (a : ℕ) (h : a ≤ 1158) : Nat.sqrt (335241 + a) = 579 := by
  have := Nat.sqrt_add_eq' 579 h
  rwa [show (579 : ℕ) ^ 2 = 335241 by norm_num] at this

lemma sq580 (a : ℕ) (h : a ≤ 1160) : Nat.sqrt (336400 + a) = 580 := by
  have := Nat.sqrt_add_eq' 580 h
  rwa [show (580 : ℕ) ^ 2 = 336400 by norm_num] at this

def p (m : ℕ) : Prop := 1 ≤ m ∧ A007961 m % 10 = 3

instance : DecidablePred p := fun m => by unfold p; infer_instance

lemma window (i : ℕ) (hi : i < 12) : p (336391 + i) ↔ i = 0 := by
  unfold p A007961
  interval_cases i
  · rw [show 336391 + 0 = 335241 + 1150 by norm_num, sq579 _ (by norm_num)]; decide +kernel
  · rw [show 336391 + 1 = 335241 + 1151 by norm_num, sq579 _ (by norm_num)]; decide +kernel
  · rw [show 336391 + 2 = 335241 + 1152 by norm_num, sq579 _ (by norm_num)]; decide +kernel
  · rw [show 336391 + 3 = 335241 + 1153 by norm_num, sq579 _ (by norm_num)]; decide +kernel
  · rw [show 336391 + 4 = 335241 + 1154 by norm_num, sq579 _ (by norm_num)]; decide +kernel
  · rw [show 336391 + 5 = 335241 + 1155 by norm_num, sq579 _ (by norm_num)]; decide +kernel
  · rw [show 336391 + 6 = 335241 + 1156 by norm_num, sq579 _ (by norm_num)]; decide +kernel
  · rw [show 336391 + 7 = 335241 + 1157 by norm_num, sq579 _ (by norm_num)]; decide +kernel
  · rw [show 336391 + 8 = 335241 + 1158 by norm_num, sq579 _ (by norm_num)]; decide +kernel
  · rw [show 336391 + 9 = 336400 + 0 by norm_num, sq580 _ (by norm_num)]; decide +kernel
  · rw [show 336391 + 10 = 336400 + 1 by norm_num, sq580 _ (by norm_num)]; decide +kernel
  · rw [show 336391 + 11 = 336400 + 2 by norm_num, sq580 _ (by norm_num)]; decide +kernel

lemma p_end : p 336403 := by
  unfold p A007961
  rw [show 336403 = 336400 + 3 by norm_num, sq580 _ (by norm_num)]
  decide +kernel

end P376360

open P376360 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a376360.main) := by
  intro h
  have hp0 : p 336391 := (window 0 (by norm_num)).mpr rfl
  have hc : Nat.count p 336403 = Nat.count p 336391 + 1 := by
    rw [show 336403 = 336391 + 12 by norm_num, Nat.count_add]
    congr 1
    rw [Nat.count_eq_card_filter_range]
    have : (Finset.range 12).filter (fun k => p (336391 + k)) = {0} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hk, hpk⟩; exact (window k hk).mp hpk
      · rintro rfl; exact ⟨by norm_num, hp0⟩
    rw [this, Finset.card_singleton]
  have ha1 : a (Nat.count p 336391 + 1) = 336391 := by
    unfold a
    rw [Nat.add_sub_cancel]
    exact Nat.nth_count hp0
  have ha2 : a (Nat.count p 336391 + 1 + 1) = 336403 := by
    unfold a
    rw [Nat.add_sub_cancel, ← hc]
    exact Nat.nth_count p_end
  have h12 : (12 : ℕ) ∈ {d : ℕ | ∃ n : ℕ, 1 ≤ n ∧ a (n + 1) - a n = d} :=
    ⟨Nat.count p 336391 + 1, by omega, by rw [ha1, ha2]⟩
  rw [h] at h12
  simp at h12
