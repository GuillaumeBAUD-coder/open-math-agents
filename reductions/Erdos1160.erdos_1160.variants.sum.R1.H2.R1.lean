import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R1
import Mathlib.Tactic.Ring

/-!
Reduction of the adjacent-order growth estimate to lower and upper bounds for
groups of order 2^m. The powers of 27 express both bounds using integers.
The lower bound follows from explicit families of central extensions. The
upper bound would follow from Li and Qiao, arXiv:2610.14509v3, Theorem 1.1.
-/

open Filter Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1

def H1 : Prop :=
  ∀ᶠ m : ℕ in atTop, 2 ^ (2 * m^3) ≤ g (2^m)^27 * 2 ^ (13 * m^2)

def H2 : Prop :=
  ∀ᶠ m : ℕ in atTop, g (2^m)^27 * 2 ^ (9 * m^2) ≤ 2 ^ (2 * m^3)

lemma rearrange_four_factors (p q r s : ℕ) :
    (p*q)*r*s = (q*s)*(p*r) := by ring

lemma exponent_gap (m : ℕ) (hm : 64 ≤ m) :
    2*m^3 + 54 + 13*(m+1)^2 < 2*(m+1)^3 + 9*m^2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  apply Nat.lt_iff_add_one_le.mpr
  apply Nat.le.intro (k := 2*k^2+236*k+6846)
  ring

lemma compare_bounds (a b m : ℕ) (hm : 64 ≤ m)
    (hup : a^27 * 2^(9*m^2) ≤ 2^(2*m^3))
    (hlo : 2^(2*(m+1)^3) ≤ b^27 * 2^(13*(m+1)^2)) : 3*a < b := by
  apply lt_of_not_ge
  intro bad
  have three : (3:ℕ)^27 ≤ 2^54 := calc
    (3:ℕ)^27 ≤ (2^2)^27 := Nat.pow_le_pow_left (by decide) _
    _ = 2^54 := (Nat.pow_mul 2 2 27).symm
  have bound : (2:ℕ) ^ (2*(m+1)^3 + 9*m^2) ≤ 2 ^ (2*m^3 + 54 + 13*(m+1)^2) := calc
    _ = 2^(2*(m+1)^3) * 2^(9*m^2) := Nat.pow_add _ _ _
    _ ≤ (b^27 * 2^(13*(m+1)^2)) * 2^(9*m^2) := Nat.mul_le_mul_right _ hlo
    _ ≤ ((3*a)^27 * 2^(13*(m+1)^2)) * 2^(9*m^2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left bad _))
    _ = (a^27 * 2^(9*m^2)) * (3^27 * 2^(13*(m+1)^2)) := by
      rw [Nat.mul_pow]
      exact rearrange_four_factors _ _ _ _
    _ ≤ 2^(2*m^3) * (2^54 * 2^(13*(m+1)^2)) :=
      Nat.mul_le_mul hup (Nat.mul_le_mul_right _ three)
    _ = (2^(2*m^3) * 2^54) * 2^(13*(m+1)^2) := (Nat.mul_assoc _ _ _).symm
    _ = _ := by rw [← Nat.pow_add, ← Nat.pow_add]
  exact (Nat.not_le_of_gt (exponent_gap m hm))
    ((Nat.pow_le_pow_iff_right (a := 2) (by decide)).mp bound)

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R1.H2 := by
  intro lower upper
  unfold H1 at lower
  unfold H2 at upper
  unfold OMA.R_Erdos1160_erdos_1160_variants_sum_R1.H2
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp lower
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp upper
  refine Filter.eventually_atTop.mpr ⟨max 64 (max N M), ?_⟩
  intro m hm
  have hm' : 64 ≤ m := by omega
  have hlo := hN (m+1) (by omega)
  have hup := hM m (by omega)
  exact compare_bounds _ _ m hm' hup hlo

end OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1
