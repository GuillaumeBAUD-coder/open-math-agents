import OMAReductions.R_Erdos242_erdos_242_variants_schinzel_generalization_R1
import Mathlib

/-!
For the Schinzel variant of the Erdős–Straus question, denominators in
residue classes zero, minus one or minus two modulo the numerator
have a three-term expansion by a direct division.
-/

open Nat

namespace OMA.SchinzelEasyResidues

private theorem split_unit {x m : ℕ} (hx : 2 ≤ x) (hm : 2*x ≤ m) :
    ∃ y z : ℕ, x < y ∧ y < z ∧ (1 : ℚ)/m = 1/y+1/z := by
  refine ⟨m+1,m*(m+1),by omega,?_⟩
  constructor
  · simpa only [one_mul] using
      Nat.mul_lt_mul_of_pos_right (by omega : 1 < m) (by omega : 0 < m+1)
  · push_cast
    have hm0 : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
    have hm1 : (0 : ℚ) < (m : ℚ)+1 := by linarith
    field_simp [hm0.ne',hm1.ne']

private theorem split_two {x m : ℕ} (hx : 2 ≤ x) (hm : 2*x ≤ m) :
    ∃ y z : ℕ, x < y ∧ y < z ∧ (2 : ℚ)/m = 1/y+1/z := by
  let k := m/2
  have hk : x ≤ k := by omega
  by_cases hEven : m%2 = 0
  · have hM : m = 2*k := by omega
    refine ⟨k+1,k*(k+1),by omega,?_⟩
    constructor
    · simpa only [one_mul] using
        Nat.mul_lt_mul_of_pos_right (by omega : 1 < k) (by omega : 0 < k+1)
    · rw [hM]
      push_cast
      have hk0 : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
      have hk1 : (0 : ℚ) < (k : ℚ)+1 := by linarith
      field_simp [hk0.ne',hk1.ne']
  · have hM : m = 2*k+1 := by omega
    refine ⟨k+1,m*(k+1),by omega,?_⟩
    constructor
    · simpa only [one_mul] using
        Nat.mul_lt_mul_of_pos_right (by omega : 1 < m) (by omega : 0 < k+1)
    · rw [hM]
      push_cast
      have hk0 : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
      have hk1 : (0 : ℚ) < (k : ℚ)+1 := by linarith
      have hk2 : (0 : ℚ) < 2*(k : ℚ)+1 := by linarith
      field_simp [hk1.ne',hk2.ne']
      ring

theorem easy_residues (a n : ℕ) (ha : 0 < a) (hn : 2*a ≤ n)
    (hRes : n%a = 0 ∨ a ≤ n%a+2) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (a / n : ℚ) = 1/x+1/y+1/z := by
  let q := n/a
  let r := n%a
  have hq : 2 ≤ q := (Nat.le_div_iff_mul_le ha).mpr hn
  have hr : r < a := Nat.mod_lt _ ha
  have hD : n = a*q+r := (Nat.mod_add_div n a).symm.trans (by ring)
  let x := q+1
  have hx : 2 ≤ x := by omega
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  have hN : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hX : (0 : ℚ) < x := by exact_mod_cast (show 0 < x by omega)
  by_cases hr0 : r = 0
  · have hN0 : n = a*q := by simpa only [hr0,add_zero] using hD
    have heq : (a/n : ℚ) = 1/x + 1/(q*x : ℕ) := by
      rw [hN0]
      push_cast
      have hq0 : (0 : ℚ) < q := by exact_mod_cast (show 0 < q by omega)
      have hx' : (x : ℚ) = (q : ℚ)+1 := by dsimp [x]; push_cast; rfl
      field_simp [haq.ne',hq0.ne',hX.ne']
      linarith
    obtain ⟨y,z,hxy,hyz,hy⟩ := split_unit hx (Nat.mul_le_mul_right x hq)
    refine ⟨x,y,z,by omega,hxy,hyz,?_⟩
    rw [heq,hy]
    ring
  · have hR : a ≤ r+2 := hRes.resolve_left hr0
    let t := a-r
    have hT : t = 1 ∨ t = 2 := by omega
    have ht : (t : ℚ) = (a : ℚ)-(r : ℚ) := Nat.cast_sub hr.le
    have heq : (a/n : ℚ) = 1/x + (t : ℚ)/(n*x : ℕ) := by
      push_cast
      have hdQ : (n : ℚ) = (a : ℚ)*(q : ℚ)+(r : ℚ) := by exact_mod_cast hD
      have hxQ : (x : ℚ) = (q : ℚ)+1 := by dsimp [x]; push_cast; rfl
      field_simp [hN.ne',hX.ne']
      rw [hdQ,hxQ,ht]
      ring
    have hm : 2*x ≤ n*x := Nat.mul_le_mul_right _ (by omega)
    have hSplit : ∃ y z : ℕ, x < y ∧ y < z ∧ (t : ℚ)/(n*x : ℕ) = 1/y+1/z := by
      rcases hT with h|h
      · simpa only [h,Nat.cast_one] using split_unit hx hm
      · simpa only [h,Nat.cast_ofNat] using split_two hx hm
    obtain ⟨y,z,hxy,hyz,hy⟩ := hSplit
    refine ⟨x,y,z,by omega,hxy,hyz,?_⟩
    rw [heq,hy]
    ring

end OMA.SchinzelEasyResidues

theorem OMA.solution : OMA.R_Erdos242_erdos_242_variants_schinzel_generalization_R1.H2 :=
  OMA.SchinzelEasyResidues.easy_residues
