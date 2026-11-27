import OMAReductions.R_OeisA7406_conjecture_R1
import Mathlib

-- Credit: @jagong-cmu

open Finset

namespace A7406H1

lemma sum_zmod_pow (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) :
    ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)) ^ (p - 3) = 0 := by
  have h1 : ∑ x : ZMod p, x ^ (p - 3) = 0 := by
    apply FiniteField.sum_pow_lt_card_sub_one
    rw [ZMod.card]; omega
  have h2 : ∑ k ∈ range p, ((k : ZMod p)) ^ (p - 3) = ∑ x : ZMod p, x ^ (p - 3) := by
    apply Finset.sum_nbij (fun k : ℕ => (k : ZMod p))
    · intro k _; simp
    · intro k hk l hl hkl
      simp only [coe_range, Set.mem_Iio] at hk hl
      have := (ZMod.natCast_eq_natCast_iff' k l p).mp hkl
      rwa [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hl] at this
    · intro x _
      refine ⟨x.val, ?_, ?_⟩
      · simp [ZMod.val_lt]
      · simp
    · intro k _; rfl
  have h3 : ∑ k ∈ range p, ((k : ZMod p)) ^ (p - 3)
      = ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)) ^ (p - 3) := by
    have : range p = insert 0 (Icc 1 (p - 1)) := by
      ext k; simp only [mem_range, mem_insert, mem_Icc]; omega
    rw [this, sum_insert (by simp), Nat.cast_zero, zero_pow (by omega), zero_add]
  rw [← h3, h2, h1]

lemma dvd_T (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    p ∣ ∑ k ∈ Icc 1 (p - 1), ((p - 1).factorial) ^ 2 / k ^ 2 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
  have key : ∀ k ∈ Icc 1 (p - 1), (((p - 1).factorial ^ 2 / k ^ 2 : ℕ) : ZMod p)
      = (((p - 1).factorial ^ 2 : ℕ) : ZMod p) * (k : ZMod p) ^ (p - 3) := by
    intro k hk
    rw [mem_Icc] at hk
    have hdvd : k ^ 2 ∣ (p - 1).factorial ^ 2 :=
      pow_dvd_pow_of_dvd (Nat.dvd_factorial (by omega) hk.2) 2
    have hk0 : (k : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h; have := Nat.le_of_dvd (by omega) h; omega
    have hferm : (k : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hk0
    have hinv : (k : ZMod p) ^ 2 * (k : ZMod p) ^ (p - 3) = 1 := by
      rw [← pow_add]; convert hferm using 2; omega
    obtain ⟨m, hm⟩ := hdvd
    rw [hm, Nat.mul_div_cancel_left _ (pow_pos (by omega) 2)]
    push_cast
    linear_combination (-(m : ZMod p)) * hinv
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, sum_zmod_pow p h5, mul_zero]

theorem h1 : ∀ n : ℕ, 3 < n → n.Prime →
    Nat.gcd n (OeisA7406.a (n - 1)) = OeisA89026.a n := by
  intro p hp3 hp
  have := Fact.mk hp
  have h5 : 5 ≤ p := by
    by_contra h
    have : p = 4 := by omega
    subst this; norm_num at hp
  rw [OeisA89026.a, if_pos hp]
  apply Nat.gcd_eq_left
  unfold OeisA7406.a
  set S : ℚ := ∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / (k : ℚ) ^ 2 with hS
  set D : ℕ := (p - 1).factorial ^ 2 with hD
  set T : ℕ := ∑ k ∈ Icc 1 (p - 1), D / k ^ 2 with hT
  have hST : S * D = T := by
    rw [hS, hT, Finset.sum_mul, Nat.cast_sum]
    apply sum_congr rfl
    intro k hk
    rw [mem_Icc] at hk
    have hdvd : k ^ 2 ∣ D := pow_dvd_pow_of_dvd (Nat.dvd_factorial (by omega) hk.2) 2
    have hk0 : (k : ℚ) ≠ 0 := by norm_cast; omega
    rw [Nat.cast_div hdvd (by exact_mod_cast pow_ne_zero 2 (by omega : k ≠ 0))]
    push_cast
    field_simp
  have hnumQ : (S.num : ℚ) * D = T * S.den := by
    rw [← hST, ← Rat.mul_den_eq_num]; ring
  have hnumZ : S.num * (D : ℤ) = (T : ℤ) * S.den := by exact_mod_cast hnumQ
  have hnumN : S.num.natAbs * D = T * S.den := by
    have := congrArg Int.natAbs hnumZ
    rw [Int.natAbs_mul, Int.natAbs_mul] at this
    simpa using this
  have hpT : p ∣ T := dvd_T p h5
  have hpD : ¬ p ∣ D := by
    intro h
    have := hp.dvd_of_dvd_pow h
    rw [hp.dvd_factorial] at this
    omega
  have : p ∣ S.num.natAbs * D := by
    rw [hnumN]; exact Dvd.dvd.mul_right hpT _
  rcases hp.dvd_mul.mp this with h | h
  · exact h
  · exact absurd h hpD

end A7406H1

theorem OMA.solution : OMA.R_OeisA7406_conjecture_R1.H1 := A7406H1.h1
