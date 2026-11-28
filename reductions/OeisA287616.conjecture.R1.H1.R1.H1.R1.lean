import OMAReductions.R_OeisA287616_conjecture_R1_H1_R1
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The primitive seed for 120n + 23 is reduced to two independent classical steps.
The first gives a rational representation from local ones. The second transfers a
rational point and primitive local representations to an integral point in one
of the two genus classes. Over all finite places the local inputs are supplied
here by Hensel lifting, and over the reals by a square root.
See Cao, Guo, Qiu, Feng and Gao, arXiv:2606.26035, Section 3.2.
-/

namespace OMA.R_OeisA287616_conjecture_R1_H1_R1_H1_R1

open Polynomial

private theorem square_lift {p : ℕ} [Fact p.Prime] (a b : ℤ_[p])
    (h : ‖a + b‖ < ‖2 * a‖ ^ 2) :
    ∃ x : ℤ_[p], a * x ^ 2 + b = 0 ∧ ‖x - 1‖ < ‖2 * a‖ := by
  let f : Polynomial ℤ_[p] := C a * X ^ 2 + C b
  have ev (x : ℤ_[p]) : f.aeval x = a * x ^ 2 + b := by
    simp [f]
  have fder : f.derivative = C a * (C (2 : ℤ_[p]) * X) := by
    dsimp [f]
    rw [derivative_add, derivative_C_mul, derivative_X_pow, derivative_C, add_zero]
    norm_num
  have der : f.derivative.aeval (1 : ℤ_[p]) = 2 * a := by
    rw [fder]
    simp; ring
  have hf : ‖f.aeval (1 : ℤ_[p])‖ < ‖f.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    rw [ev, der, one_pow, mul_one]
    exact h
  obtain ⟨x, hx, hclose, _, _⟩ := hensels_lemma (F := f) (a := 1) hf
  exact ⟨x, ev x ▸ hx, der ▸ hclose⟩

private theorem norm_one_if_not_dvd {p : ℕ} [Fact p.Prime] {a : ℤ}
    (h : ¬ (p : ℤ) ∣ a) : ‖(a : ℤ_[p])‖ = 1 := by
  exact PadicInt.norm_intCast_eq_one_iff.mpr
    (((Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).coprime_iff_not_dvd.mpr h).symm)

private theorem prime_not_dvd_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ¬ (p : ℤ) ∣ (q : ℤ) := by
  intro hd
  exact hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp (by exact_mod_cast hd))

private theorem unit_square_lift {p : ℕ} [Fact p.Prime] {a b : ℤ}
    (hunit : ¬ (p : ℤ) ∣ 2 * a) (hdiv : (p : ℤ) ∣ a + b) :
    ∃ x : ℤ_[p], (a : ℤ_[p]) * x ^ 2 + b = 0 ∧ IsUnit x := by
  have hder : ‖2 * (a : ℤ_[p])‖ = 1 := by exact_mod_cast norm_one_if_not_dvd hunit
  have hres : ‖(a : ℤ_[p]) + (b : ℤ_[p])‖ < 1 := by
    exact_mod_cast (PadicInt.norm_intCast_lt_one_iff (p := p)).mpr hdiv
  obtain ⟨x, hx, hc⟩ := square_lift (a : ℤ_[p]) (b : ℤ_[p]) (by simpa [hder] using hres)
  have hc' : ‖x - 1‖ < 1 := hder ▸ hc
  have hn : ‖x - 1‖ ≠ ‖(1 : ℤ_[p])‖ := by simpa using ne_of_lt hc'
  have hnorm := PadicInt.norm_add_eq_max_of_ne hn
  rw [sub_add_cancel, norm_one, max_eq_right (le_of_lt hc')] at hnorm
  exact ⟨x, hx, PadicInt.isUnit_iff.mpr hnorm⟩

private theorem binary_mod {p : ℕ} [Fact p.Prime] {a b c : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) (hp2 : p ≠ 2) :
    ∃ u v : ZMod p, a * u ^ 2 + b * v ^ 2 = c := by
  let f : Polynomial (ZMod p) := C a * X ^ 2
  let g : Polynomial (ZMod p) := C b * X ^ 2 - C c
  have hf : f.degree = 2 := by
    simp [f, degree_C_mul ha]
  have hg : g.degree = 2 := by
    have hd : (C b * X ^ 2).degree = 2 := by simp [degree_C_mul hb]
    dsimp [g]
    rw [degree_sub_eq_left_of_degree_lt, hd]
    rw [hd]
    exact lt_of_le_of_lt degree_C_le (by decide)
  have hodd : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]
    exact ((Fact.out : p.Prime).eq_two_or_odd.resolve_left hp2)
  obtain ⟨u, v, huv⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
  simp [f, g] at huv
  exact ⟨u, v, by linear_combination huv⟩

private theorem local_outside_30 {p : ℕ} [Fact p.Prime] (m : ℤ)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    ∃ u v w : ℤ_[p], 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = (m : ℤ_[p]) ∧
      (IsUnit u ∨ IsUnit v ∨ IsUnit w) := by
  have hp : p.Prime := Fact.out
  have pPrime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h2 : ¬ (p : ℤ) ∣ 2 := by exact_mod_cast prime_not_dvd_prime hp Nat.prime_two hp2
  have h3 : ¬ (p : ℤ) ∣ 3 := by exact_mod_cast prime_not_dvd_prime hp Nat.prime_three hp3
  have h5 : ¬ (p : ℤ) ∣ 5 := by exact_mod_cast prime_not_dvd_prime hp (by decide : Nat.Prime 5) hp5
  have p15 : ¬ (p : ℤ) ∣ 15 := by
    intro hc
    exact (pPrime.dvd_mul.mp (show (p : ℤ) ∣ 3 * 5 from hc)).elim h3 h5
  have a : (15 : ZMod p) ≠ 0 := by
    simpa using (mt (ZMod.intCast_zmod_eq_zero_iff_dvd 15 p).mp p15 : ((15 : ℤ) : ZMod p) ≠ 0)
  have b : (5 : ZMod p) ≠ 0 := by
    simpa using (mt (ZMod.intCast_zmod_eq_zero_iff_dvd 5 p).mp h5 : ((5 : ℤ) : ZMod p) ≠ 0)
  obtain ⟨u, v, huv⟩ := binary_mod a b hp2 (c := (m : ZMod p) - 3)
  let r : ℤ := 15 * (u.val : ℤ) ^ 2 + 5 * (v.val : ℤ) ^ 2 - m
  have hdiv : (p : ℤ) ∣ 3 + r := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    dsimp [r]
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id]
    linear_combination huv
  have hunit : ¬ (p : ℤ) ∣ 2 * 3 := fun h => (pPrime.dvd_mul.mp h).elim h2 h3
  obtain ⟨w, hw, hwu⟩ := unit_square_lift hunit hdiv
  refine ⟨(u.val : ℤ_[p]), (v.val : ℤ_[p]), w, ?_, Or.inr (Or.inr hwu)⟩
  dsimp [r] at hw
  push_cast at hw
  linear_combination hw

private theorem local_at_two (n : ℕ) :
    ∃ u v w : ℤ_[2], 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = ((120 * (n : ℤ) + 23 : ℤ) : ℤ_[2]) ∧
      (IsUnit u ∨ IsUnit v ∨ IsUnit w) := by
  let b : ℤ := -(120 * (n : ℤ) + 3)
  have hres : ‖(3 : ℤ_[2]) + (b : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by
    have hc : (3 : ℤ_[2]) + b = ((3 + b : ℤ) : ℤ_[2]) := by push_cast; rfl
    rw [hc]
    exact (PadicInt.norm_int_le_pow_iff_dvd (n := 3)).mpr
      ⟨-15 * (n : ℤ), by dsimp [b]; ring⟩
  have h6 : ‖(2 : ℤ_[2]) * 3‖ = (2 : ℝ) ^ (-1 : ℤ) := by
    have h2 : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := PadicInt.norm_p (p := 2)
    have h3 : ‖(3 : ℤ_[2])‖ = 1 := by
      exact_mod_cast norm_one_if_not_dvd (p := 2) (a := 3) (by decide)
    rw [norm_mul, h2, h3, mul_one, zpow_neg_one]
  have hsmall : ‖(3 : ℤ_[2]) + (b : ℤ_[2])‖ < ‖(2 : ℤ_[2]) * 3‖ ^ 2 := by
    rw [h6]
    exact hres.trans_lt (by norm_num)
  obtain ⟨w, hw, _⟩ := square_lift (3 : ℤ_[2]) b hsmall
  refine ⟨1, 1, w, ?_, Or.inl isUnit_one⟩
  dsimp [b] at hw
  push_cast at hw ⊢
  linear_combination hw

private theorem local_padic (n p : ℕ) [Fact p.Prime] :
    ∃ u v w : ℤ_[p], 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = ((120 * (n : ℤ) + 23 : ℤ) : ℤ_[p]) ∧
      (IsUnit u ∨ IsUnit v ∨ IsUnit w) := by
  by_cases hp2 : p = 2
  · subst p
    exact local_at_two n
  by_cases hp3 : p = 3
  · subst p
    obtain ⟨v, hv, hvu⟩ := unit_square_lift (p := 3) (a := 5) (b := -(120 * (n : ℤ) + 23))
      (by decide) ⟨-40 * (n : ℤ) - 6, by ring⟩
    refine ⟨0, v, 0, ?_, Or.inr (Or.inl hvu)⟩
    push_cast at hv ⊢
    linear_combination hv
  by_cases hp5 : p = 5
  · subst p
    obtain ⟨w, hw, hwu⟩ := unit_square_lift (p := 5) (a := 3) (b := -(120 * (n : ℤ) + 23))
      (by decide) ⟨-24 * (n : ℤ) - 4, by ring⟩
    refine ⟨0, 0, w, ?_, Or.inr (Or.inr hwu)⟩
    push_cast at hw ⊢
    linear_combination hw
  exact local_outside_30 _ hp2 hp3 hp5

private theorem local_real (n : ℕ) :
    ∃ u v w : ℝ, 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = ((120 * (n : ℤ) + 23 : ℤ) : ℝ) := by
  let m : ℝ := 120 * (n : ℝ) + 23
  refine ⟨Real.sqrt (m / 15), 0, 0, ?_⟩
  rw [Real.sq_sqrt (show 0 ≤ m / 15 by dsimp [m]; positivity)]
  push_cast
  dsimp [m]
  ring


def H1 : Prop :=
  ∀ m : ℤ,
    (∃ u v w : ℝ, 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = (m : ℝ)) →
    (∀ (p : ℕ) [Fact p.Prime], ∃ u v w : ℤ_[p],
      15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = (m : ℤ_[p])) →
    ∃ u v w : ℚ, 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = (m : ℚ)

def H2 : Prop :=
  ∀ m : ℤ, 0 < m →
    (∃ u v w : ℚ, 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = (m : ℚ)) →
    (∀ (p : ℕ) [Fact p.Prime], ∃ u v w : ℤ_[p],
      15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = (m : ℤ_[p]) ∧
        (IsUnit u ∨ IsUnit v ∨ IsUnit w)) →
    (∃ u v w : ℤ, 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = m ∧
      Int.gcd u (Int.gcd v w) = 1) ∨
    (∃ x y z : ℤ, 2 * x ^ 2 - 2 * x * y + 8 * y ^ 2 + 15 * z ^ 2 = m ∧
      Int.gcd x (Int.gcd y z) = 1)

theorem main : H1 → H2 → OMA.R_OeisA287616_conjecture_R1_H1_R1.H1 := by
  intro hrational hgenus n
  let m : ℤ := 120 * (n : ℤ) + 23
  have hrat := hrational m (local_real n) (fun p _ => by
    obtain ⟨u, v, w, heq, _⟩ := local_padic n p
    exact ⟨u, v, w, heq⟩)
  exact hgenus m (by dsimp [m]; positivity) hrat (local_padic n)

end OMA.R_OeisA287616_conjecture_R1_H1_R1_H1_R1
