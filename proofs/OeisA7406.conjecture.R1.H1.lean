import OMAReductions.R_OeisA7406_conjecture_R1
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Prime.Factorial

namespace OMA.Wolstenholme
open Finset

lemma clear_denominators (n : ℕ) :
    (∑ k ∈ Icc 1 n, (1 : ℚ) / (k : ℚ) ^ 2) * (n.factorial : ℚ)^2 =
      ∑ k ∈ Icc 1 n, ((n.factorial / k : ℕ) : ℚ)^2 := by
  rw [sum_mul]
  apply sum_congr rfl
  intro k hk
  obtain ⟨hk0, hkn⟩ := mem_Icc.mp hk
  have hd := Nat.div_mul_cancel (Nat.dvd_factorial (by omega) hkn)
  have he : (n.factorial : ℚ) = (n.factorial / k : ℕ) * (k : ℚ) := by
    exact_mod_cast hd.symm
  rw [he]
  field_simp

lemma inverse_square_sum (p : ℕ) [Fact p.Prime] (hp : p.Prime) (hlarge : 3 < p) :
    ∑ k ∈ Icc 1 (p-1), (1 : ZMod p) / (k : ZMod p)^2 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hsum : ∑ x : ZMod p, (1 : ZMod p) / x^2 = 0 := by
    calc
      _ = ∑ x : ZMod p, x^2 := Fintype.sum_equiv (Equiv.inv (ZMod p))
        (fun x => 1 / x^2) (fun x => x^2) (by intro x; simp [inv_pow])
      _ = 0 := FiniteField.sum_pow_lt_card_sub_one _ _ (by rw [ZMod.card]; omega)
  have hr : (∑ k ∈ range p, (1 : ZMod p) / (k : ZMod p)^2) =
      ∑ x : ZMod p, (1 : ZMod p) / x^2 := by
    apply sum_bij (fun (k : ℕ) _ => (k : ZMod p)) (by simp)
    · intro a ha b hb he
      have hv := congrArg ZMod.val he
      simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp ha),
        Nat.mod_eq_of_lt (mem_range.mp hb)] using hv
    · intro x _
      exact ⟨x.val, mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
    · intro k hk
      rfl
  rw [← hr] at hsum
  rw [← hsum]
  apply sum_subset
  · intro k hk
    simp only [mem_Icc] at hk
    simp only [mem_range]
    omega
  · intro k hk hnot
    have : k = 0 := by simp only [mem_range] at hk; simp only [mem_Icc] at hnot; omega
    subst k
    simp

end OMA.Wolstenholme

-- Step OeisA7406.conjecture.R1.H1: hypothesis H1 of reduction OeisA7406.conjecture.R1
-- Credit: @DeepDuke
-- H1 := ∀ n : ℕ, 3 < n → n.Prime → Nat.gcd n (OeisA7406.a (n - 1)) = OeisA89026.a n

theorem OMA.solution : OMA.R_OeisA7406_conjecture_R1.H1 := by
  intro p hlarge hp
  have : Fact p.Prime := ⟨hp⟩
  let D := (p-1).factorial
  let r : ℚ := ∑ k ∈ Finset.Icc 1 (p-1), (1 : ℚ) / (k : ℚ)^2
  let T : ℕ := ∑ k ∈ Finset.Icc 1 (p-1), (D / k)^2
  have heq : r * (D : ℚ)^2 = T := by
    simpa only [r, D, T, Nat.cast_sum, Nat.cast_pow] using
      OMA.Wolstenholme.clear_denominators (p-1)
  have heQ : (r.num : ℚ) * (D : ℚ)^2 = (T : ℚ) * r.den := by
    rw [← Rat.mul_den_eq_num]
    calc
      _ = (r * (D : ℚ)^2) * r.den := by ring
      _ = _ := by rw [heq]
  have heZ : (r.num : ℤ) * (D : ℤ)^2 = (T : ℤ) * r.den := by
    exact_mod_cast heQ
  have hD : (D : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff D p).mp hz
    rw [hp.dvd_factorial] at hd
    omega
  have hT : (T : ZMod p) = 0 := by
    have hterm (k : ℕ) (hk : k ∈ Finset.Icc 1 (p-1)) :
        (((D / k)^2 : ℕ) : ZMod p) = (D : ZMod p)^2 * (1 / (k : ZMod p)^2) := by
      obtain ⟨hk0, hkp⟩ := Finset.mem_Icc.mp hk
      have hkz : (k : ZMod p) ≠ 0 := by
        intro hz
        have hd := (ZMod.natCast_eq_zero_iff k p).mp hz
        have := Nat.le_of_dvd (by omega : 0 < k) hd
        omega
      have hd := Nat.div_mul_cancel (Nat.dvd_factorial (by omega) hkp)
      have hdZ : ((D / k : ℕ) : ZMod p) * k = D := by
        simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : ZMod p)) hd
      rw [Nat.cast_pow, (eq_div_iff hkz).mpr hdZ, div_pow]
      ring
    change (↑(∑ k ∈ Finset.Icc 1 (p-1), (D / k)^2) : ZMod p) = 0
    rw [Nat.cast_sum]
    rw [Finset.sum_congr rfl hterm]
    rw [← Finset.mul_sum, OMA.Wolstenholme.inverse_square_sum p hp hlarge, mul_zero]
  have hz : (r.num : ZMod p) * (D : ZMod p)^2 = (T : ZMod p) * r.den := by
    have hh := congrArg (fun z : ℤ => (z : ZMod p)) heZ
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast] using hh
  rw [hT, zero_mul] at hz
  have hnum : (r.num : ZMod p) = 0 :=
    (mul_eq_zero.mp hz).resolve_right (pow_ne_zero _ hD)
  have hdvd : p ∣ r.num.natAbs := Int.natCast_dvd.mp
    ((ZMod.intCast_zmod_eq_zero_iff_dvd r.num p).mp hnum)
  simpa only [OeisA89026.a, if_pos hp] using
    (Nat.gcd_eq_left_iff_dvd.mpr hdvd : Nat.gcd p (OeisA7406.a (p-1)) = p)

