import OMAReductions.R_OeisA1146_conjecture_R1
import Mathlib

/-! Divisibility for the power-of-two subfamily via the gcd of two Mersenne numbers. -/

namespace A1146PowersOfTwo

private theorem mersenne_dvd (a b : ℕ) : (2^a - 1 : ℕ) ∣ 2^b - 1 ↔ a ∣ b := by
  constructor
  · intro h
    have hmono : StrictMono (fun n : ℕ => (2^n - 1 : ℕ)) := by
      intro i j hij
      have hlt := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hij
      have hpos := Nat.two_pow_pos i
      change 2^i - 1 < 2^j - 1
      omega
    have hgcd : (2^(a.gcd b) - 1 : ℕ) = 2^a - 1 :=
      (Nat.pow_sub_one_gcd_pow_sub_one 2 a b).symm.trans (Nat.gcd_eq_left h)
    exact Nat.gcd_eq_left_iff_dvd.mp (hmono.injective hgcd)
  · exact Nat.pow_sub_one_dvd_pow_sub_one 2

private theorem enough (t : ℕ) (ht : 2 ≤ t) : t+2 ≤ 2^t := by
  have h : ∀ i : ℕ, i+2+2 ≤ 2^(i+2) := by
    intro i
    induction i with
    | zero => decide
    | succ i ih =>
      have he : i+1+2 = i+2+1 := by omega
      rw [show i.succ+2 = i+1+2 by rfl, he, pow_succ]
      omega
  have ht' : t-2+2 = t := Nat.sub_add_cancel ht
  simpa only [ht'] using h (t-2)

theorem main : ∀ m : ℕ, (2^m)^4-1 ∣ 2^(2^m)-1 ↔ ∃ t : ℕ, 2≤t ∧ m=2^t := by
  intro m
  rw [← pow_mul, Nat.mul_comm m 4, mersenne_dvd]
  have hef (t : ℕ) : 4 * 2^t = 2^(t+2) := by rw [pow_add]; ring
  constructor
  · intro h
    have hm : m ∣ 2^m := (show m ∣ 4*m from ⟨4, Nat.mul_comm 4 m⟩).trans h
    obtain ⟨t,_,ht⟩ := Nat.dvd_prime_pow Nat.prime_two |>.mp hm
    subst m
    rw [hef, Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (2 : ℕ))] at h
    refine ⟨t,?_,rfl⟩
    by_contra! ht
    interval_cases t <;> norm_num at h
  · rintro ⟨t,ht,rfl⟩
    rw [hef, Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (2 : ℕ))]
    exact enough t ht

end A1146PowersOfTwo

theorem OMA.solution : OMA.R_OeisA1146_conjecture_R1.H1 :=
  A1146PowersOfTwo.main