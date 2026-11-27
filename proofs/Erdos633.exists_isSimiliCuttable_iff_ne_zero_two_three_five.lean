import FormalConjectures.ErdosProblems.«633»
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
import Mathlib.Geometry.Euclidean.Similarity
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-
Soifer's triangle dissection theorem. Formalization for LeftToSolve by @LDJAI.
The witness has angles 1°, 6°, and 173°, as in Alexander Soifer's How Does One Cut a Triangle?, chapter I.
The angular obstruction and the incidence arguments for two, three, and five tiles are developed below.
The allowed-count construction is from @TheWaler's independently verified LeftToSolve submission:
https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/main/proofs/Erdos633.IsSimiliCuttable.of_ne_zero_two_three_five.lean
The supporting geometric measure and boundary lemmas are adapted from Vico Bonfioli's triangle-tiling formalization:
https://github.com/ElVec1o/formalizing-triangle-tiling-in-lean/tree/b56f1589a32a23e71bd4604d540826a2ff320f2f
-/

/-
Adapted from Vico Bonfioli, formalizing-triangle-tiling-in-lean, commit
b56f1589a32a23e71bd4604d540826a2ff320f2f. MIT License.
Copyright (c) 2026 Vico Bonfioli

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

section
namespace Soifer.Obstruction

/-- Four objects assigned to three sides have a pair on the same side. -/
private theorem four_three : ∀ a b c d : Fin 3,
    a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d := by decide

/-- If five triangles form a dissection with three different unsplit corner
tiles, take four distinct vertices of the two remaining tiles. Each vertex
has at least three incident tiles. Two distinct vertices on the same outer
side have at most two incident corner tiles in total. Distinct tiles cannot
share a nontrivial segment along an outer side. These three incidence
conditions are incompatible. -/
theorem no_five
    (side : Fin 4 → Fin 3) (cornerOwners : Fin 4 → Nat)
    (left right : Fin 4 → Bool)
    (degree : ∀ i, 3 ≤ cornerOwners i + (left i).toNat + (right i).toNat)
    (capacity : ∀ i j, i ≠ j → side i = side j → cornerOwners i + cornerOwners j ≤ 2)
    (edge : ∀ i j, i ≠ j → side i = side j →
      left i = true → right i = true → left j = true → right j = true → False) :
    False := by
  have apart {i j : Fin 4} (h : i ≠ j) : side i ≠ side j := by
    intro hs
    have ci := degree i
    have cj := degree j
    have cap := capacity i j h hs
    have bit_bound (u : Bool) : u.toNat ≤ 1 := by cases u <;> decide
    have cli := bit_bound (left i)
    have cri := bit_bound (right i)
    have clj := bit_bound (left j)
    have crj := bit_bound (right j)
    have li : (left i).toNat = 1 := by omega
    have ri : (right i).toNat = 1 := by omega
    have lj : (left j).toNat = 1 := by omega
    have rj : (right j).toNat = 1 := by omega
    have bit_one (u : Bool) (e : u.toNat = 1) : u = true := by
      cases u <;> simp_all [Bool.toNat]
    exact edge i j h hs (bit_one _ li) (bit_one _ ri) (bit_one _ lj) (bit_one _ rj)
  rcases four_three (side 0) (side 1) (side 2) (side 3) with h | h | h | h | h | h
  all_goals exact apart (by decide) h

/-- Every nonempty set of at most five tile corners with angles 1, 6 and
173 degrees that contributes an integer multiple of 180 degrees has one of
each angle. -/
theorem vertex_balance (a b c k : Nat) (h : a + b + c ≤ 5)
    (hne : 0 < a + b + c) (hsum : a + 6*b + 173*c = 180*k) :
    a = 1 ∧ b = 1 ∧ c = 1 := by
  have hkc : k = c := by
    have ha : a ≤ 5 := by omega
    have hb : b ≤ 5 := by omega
    have hc : c ≤ 5 := by omega
    omega
  subst k
  have hbc : b = c := by omega
  omega

end Soifer.Obstruction
end

section
namespace Soifer

open Finset

private theorem angle_in_band (w : Fin 3 → ℝ) (m : Fin 3 → ℕ)
    (hw : ∀ j, 0 < w j) {lo hi : ℝ} (hlo : 0 ≤ lo)
    (hgap : 5 * lo < hi) (hcount : ∑ j, m j ≤ 5)
    (heq : ∑ j, (m j : ℝ) * w j = hi) :
    ∃ j, 0 < m j ∧ lo < w j ∧ w j ≤ hi := by
  have ex : ∃ j, 0 < m j ∧ lo < w j := by
    by_contra! h
    have H : ∑ j, (m j : ℝ) * w j ≤ ∑ j, (m j : ℝ) * lo := by
      apply sum_le_sum
      intro j _
      by_cases hz : m j = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (h j (Nat.pos_of_ne_zero hz)) (Nat.cast_nonneg _)
    rw [← sum_mul, ← Nat.cast_sum] at H
    have hc : ((∑ j, m j : ℕ) : ℝ) ≤ 5 := by exact_mod_cast hcount
    linarith [mul_le_mul_of_nonneg_right hc hlo]
  obtain ⟨j, hm, hl⟩ := ex
  refine ⟨j, hm, hl, ?_⟩
  have h1 : (1 : ℝ) ≤ (m j : ℝ) := by exact_mod_cast (show 1 ≤ m j from hm)
  calc
    w j = 1 * w j := (one_mul _).symm
    _ ≤ (m j : ℝ) * w j := mul_le_mul_of_nonneg_right h1 (hw j).le
    _ ≤ ∑ k, (m k : ℝ) * w k :=
      single_le_sum (f := fun k => (m k : ℝ) * w k)
        (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hw k).le) (mem_univ j)
    _ = hi := heq

/-- For up to five tiles, the three largest angle types used at the three corners
are distinct. Angle-sum equality then forces every corner to remain unsplit. -/
theorem corners_unsplit (A w : Fin 3 → ℝ) (m : Fin 3 → Fin 3 → ℕ)
    (hA : 0 < A 0) (hAB : 5 * A 0 < A 1) (hBC : 5 * A 1 < A 2)
    (hw : ∀ j, 0 < w j) (htotal : ∑ j, w j = ∑ i, A i)
    (hcount : ∀ i, ∑ j, m i j ≤ 5)
    (hangle : ∀ i, ∑ j, (m i j : ℝ) * w j = A i) :
    ∃ e : Fin 3 ≃ Fin 3, (∀ i, w (e i) = A i) ∧
      ∀ i j, m i j = if j = e i then 1 else 0 := by
  obtain ⟨j₀,h₀,_,u₀⟩ := angle_in_band w (m 0) hw (lo := 0) le_rfl
    (by linarith) (hcount 0) (hangle 0)
  obtain ⟨j₁,h₁,l₁,u₁⟩ := angle_in_band w (m 1) hw hA.le hAB (hcount 1) (hangle 1)
  obtain ⟨j₂,h₂,l₂,u₂⟩ := angle_in_band w (m 2) hw (by linarith : 0 ≤ A 1) hBC
    (hcount 2) (hangle 2)
  have d01 : j₀ ≠ j₁ := fun h => by rw [h] at u₀; linarith
  have d02 : j₀ ≠ j₂ := fun h => by rw [h] at u₀; linarith
  have d12 : j₁ ≠ j₂ := fun h => by rw [h] at u₁; linarith
  let f : Fin 3 → Fin 3 := ![j₀,j₁,j₂]
  have inj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  let e := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp inj)
  have e0 : e 0 = j₀ := rfl
  have e1 : e 1 = j₁ := rfl
  have e2 : e 2 = j₂ := rfl
  have hs := (Equiv.sum_comp e w).trans htotal
  rw [Fin.sum_univ_three, Fin.sum_univ_three, e0, e1, e2] at hs
  have he : ∀ i, w (e i) = A i := by
    intro i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.reduceFinMk, e0, e1, e2] <;> linarith
  refine ⟨e, he, ?_⟩
  intro i
  have hp : 0 < m i (e i) := by
    fin_cases i <;> assumption
  have h1 : (1 : ℝ) ≤ (m i (e i) : ℝ) := by exact_mod_cast (show 1 ≤ m i (e i) from hp)
  have hz : ∀ j, (0 : ℝ) ≤ (m i j : ℝ) * w j :=
    fun j => mul_nonneg (Nat.cast_nonneg _) (hw j).le
  have hle : (m i (e i) : ℝ) * w (e i) ≤ A i := by
    rw [← hangle i]
    exact single_le_sum (fun j _ => hz j) (mem_univ _)
  have hone : m i (e i) = 1 := by
    have hup : (m i (e i) : ℝ) ≤ 1 := by
      apply (mul_le_mul_iff_left₀ (hw (e i))).mp
      simpa only [one_mul, he i] using hle
    exact_mod_cast (le_antisymm hup h1)
  intro j
  split_ifs with hij
  · simpa [hij] using hone
  · by_contra hn
    have hpj : 0 < (m i j : ℝ) * w j := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) (hw j)
    have htwo := sum_le_sum_of_subset_of_nonneg (f := fun k => (m i k : ℝ) * w k)
      (show ({j,e i} : Finset (Fin 3)) ⊆ univ from subset_univ _) (fun k _ _ => hz k)
    rw [sum_pair hij, hangle i, hone, Nat.cast_one, one_mul, he i] at htwo
    linarith

end Soifer
end

section
namespace Soifer

open Finset

/-- A row of local angle contributions. A tile either contributes its angle
at a unique labelled vertex or contributes zero. -/
theorem corner_rows {n : ℕ} (hn : n ≤ 5) (A w : Fin 3 → ℝ)
    (inc : Fin 3 → Fin n → Fin 3 → Prop) [∀ s i j, Decidable (inc s i j)]
    (single : ∀ s i j k, inc s i j → inc s i k → j = k)
    (hA : 0 < A 0) (hAB : 5 * A 0 < A 1) (hBC : 5 * A 1 < A 2)
    (hw : ∀ j, 0 < w j) (htotal : ∑ j, w j = ∑ s, A s)
    (hpartition : ∀ s, (∑ i, ∑ j, if inc s i j then w j else 0) = A s) :
    (∃ e : Fin 3 ≃ Fin 3, ∀ s, w (e s) = A s) ∧
      ∀ s, ∃! i : Fin n, ∃ j, inc s i j := by
  classical
  let m (s j : Fin 3) := (univ.filter (fun i => inc s i j)).card
  have msum s j : m s j = ∑ i, if inc s i j then 1 else 0 := by simp [m]
  have hc (s) : ∑ j, m s j ≤ 5 := by
    simp_rw [msum]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _i : Fin n, 1 := by
        apply sum_le_sum
        intro i _
        by_cases h : ∃ j, inc s i j
        · obtain ⟨j,hj⟩ := h
          have hi : ∀ k, inc s i k ↔ k = j :=
            fun k => ⟨fun hk => single s i k j hk hj, fun e => e ▸ hj⟩
          simp [hi]
        · push_neg at h
          simp [h]
      _ ≤ 5 := by simpa using hn
  have he (s) : ∑ j, (m s j : ℝ) * w j = A s := by
    rw [← hpartition s, Finset.sum_comm (f := fun i j => if inc s i j then w j else 0)]
    apply sum_congr rfl
    intro j _
    simp [m, ← Finset.sum_filter, nsmul_eq_mul]
  obtain ⟨e, hwe, heq⟩ := corners_unsplit A w m hA hAB hBC hw htotal hc he
  refine ⟨⟨e,hwe⟩, fun s => ?_⟩
  have hone : (univ.filter (fun i => inc s i (e s))).card = 1 := by
    simpa [m] using heq s (e s)
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
  have iff_eq (t : Fin n) : inc s t (e s) ↔ t = i := by
    have := Finset.ext_iff.mp hi t
    simpa using this
  refine ⟨i, ⟨e s, (iff_eq i).mpr rfl⟩, ?_⟩
  rintro t ⟨j, hj⟩
  have hj' : j = e s := by
    by_contra h
    have hpos : 0 < m s j := Finset.card_pos.mpr ⟨t, by simp [hj]⟩
    rw [heq, if_neg h] at hpos
    omega
  exact (iff_eq t).mp (hj' ▸ hj)

end Soifer
end

section
namespace Soifer
open Affine EuclideanGeometry
open scoped Real EuclideanGeometry Similar
abbrev Plane := EuclideanSpace ℝ (Fin 2)
noncomputable def triAngle (T : Triangle ℝ Plane) (i : Fin 3) : ℝ :=
  ∠ (T.points (i + 1)) (T.points i) (T.points (i + 2))

theorem triAngle_bounds (T : Triangle ℝ Plane) (i : Fin 3) :
    0 < triAngle T i ∧ triAngle T i < π := by
  have h : ¬Collinear ℝ {T.points (i+1), T.points i, T.points (i+2)} :=
    (affineIndependent_iff_not_collinear_of_ne (by decide +revert : i+1 ≠ i)
      (by decide +revert : i+1 ≠ i+2) (by decide +revert : i ≠ i+2)).mp T.independent
  exact ⟨angle_pos_of_not_collinear h, angle_lt_pi_of_not_collinear h⟩

theorem sum_triAngle (T : Triangle ℝ Plane) : ∑ j, triAngle T j = π := by
  rw [Fin.sum_univ_three]
  change ∠ (T.points 1) (T.points 0) (T.points 2) + ∠ (T.points 2) (T.points 1) (T.points 0) +
    ∠ (T.points 0) (T.points 2) (T.points 1) = π
  have h := angle_add_angle_add_angle_eq_pi (T.points 2) (T.independent.injective.ne (by decide : (1 : Fin 3) ≠ 0))
  rw [angle_comm (T.points 0) (T.points 1) (T.points 2),
      angle_comm (T.points 1) (T.points 2) (T.points 0),
      angle_comm (T.points 2) (T.points 0) (T.points 1)] at h
  linarith

theorem triAngle_eq_of_similar {S T : Triangle ℝ Plane} (h : S.points ∼ T.points) :
    ∀ j, triAngle S j = triAngle T j := by
  have v (p : Fin 3 → Plane) : ![p 0,p 1,p 2] = p := by
    funext j
    fin_cases j <;> rfl
  have hv : ![S.points 0, S.points 1, S.points 2] ∼ ![T.points 0,T.points 1,T.points 2] := by
    simpa only [v] using h
  obtain ⟨a,b,c⟩ := hv.angle_eq_all
  intro j
  fin_cases j
  · change ∠ (S.points 1) (S.points 0) (S.points 2) = ∠ (T.points 1) (T.points 0) (T.points 2)
    simpa only [angle_comm (S.points 2) (S.points 0), angle_comm (T.points 2) (T.points 0)] using c
  · change ∠ (S.points 2) (S.points 1) (S.points 0) = ∠ (T.points 2) (T.points 1) (T.points 0)
    simpa only [angle_comm (S.points 0) (S.points 1), angle_comm (T.points 0) (T.points 1)] using a
  · change ∠ (S.points 0) (S.points 2) (S.points 1) = ∠ (T.points 0) (T.points 2) (T.points 1)
    simpa only [angle_comm (S.points 1) (S.points 2), angle_comm (T.points 1) (T.points 2)] using b
end Soifer
end

section
namespace Soifer

open InnerProductGeometry Affine
open scoped Real EuclideanGeometry RealInnerProductSpace

private lemma real_left_angle {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (z : ℂ) :
    InnerProductGeometry.angle (u : ℂ) z = InnerProductGeometry.angle (v : ℂ) z := by
  have e (x : ℝ) : x • (1 : ℂ) = (x : ℂ) := by simp [Complex.real_smul]
  rw [← e u, ← e v, angle_smul_left_of_pos _ _ hu, angle_smul_left_of_pos _ _ hv]

private lemma first_angle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∠ (b : ℂ) (-(a : ℂ)) Complex.I = Real.arctan (1 / a) := by
  change InnerProductGeometry.angle ((b : ℂ) - -a) (Complex.I - -a) = _
  rw [sub_neg_eq_add, sub_neg_eq_add, add_comm Complex.I, ← Complex.ofReal_add,
    real_left_angle (add_pos hb ha) ha]
  have ho : inner ℝ (a : ℂ) Complex.I = 0 := by simp [RCLike.inner_apply]
  rw [angle_add_eq_arctan_of_inner_eq_zero ho (by exact_mod_cast ha.ne')]
  simp [Real.norm_eq_abs, abs_of_pos ha]

private lemma second_angle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∠ (-(a : ℂ)) (b : ℂ) Complex.I = Real.arctan (1 / b) := by
  change InnerProductGeometry.angle (-(a : ℂ) - b) (Complex.I - b) = _
  rw [← angle_neg_neg, neg_sub, neg_sub, sub_neg_eq_add, ← Complex.ofReal_add,
    real_left_angle (add_pos hb ha) hb]
  have ho : inner ℝ (b : ℂ) Complex.I = 0 := by simp [RCLike.inner_apply]
  rw [angle_sub_eq_arctan_of_inner_eq_zero ho (by exact_mod_cast hb.ne')]
  simp [Real.norm_eq_abs, abs_of_pos hb]

/-- A triangle with angles 1, 6, and 173 degrees in the Euclidean plane. -/
theorem exists_witness :
    ∃ T : Triangle ℝ (EuclideanSpace ℝ (Fin 2)),
      ∠ (T.points 1) (T.points 0) (T.points 2) = π / 180 ∧
      ∠ (T.points 0) (T.points 1) (T.points 2) = π / 30 ∧
      ∠ (T.points 0) (T.points 2) (T.points 1) = 173 * π / 180 := by
  let a := (Real.tan (π / 180))⁻¹
  let b := (Real.tan (π / 30))⁻¹
  have hp := Real.pi_pos
  have ha : 0 < a := inv_pos.mpr (Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith))
  have hb : 0 < b := inv_pos.mpr (Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith))
  let p : ℂ := -(a : ℂ)
  let q : ℂ := b
  let r : ℂ := Complex.I
  have h₀ : ∠ q p r = π / 180 := by
    rw [show ∠ q p r = _ from first_angle ha hb]
    simp [a, one_div, Real.arctan_tan (by linarith : -(π/2) < π/180) (by linarith : π/180 < π/2)]
  have h₁ : ∠ p q r = π / 30 := by
    rw [show ∠ p q r = _ from second_angle ha hb]
    simp [b, one_div, Real.arctan_tan (by linarith : -(π/2) < π/30) (by linarith : π/30 < π/2)]
  have hqp : q ≠ p := by
    intro h
    have hh := congrArg Complex.re h
    simp [p,q] at hh
    linarith
  have hrq : r ≠ q := by
    intro h
    simpa [q,r] using congrArg Complex.im h
  have h₂ : ∠ p r q = 173 * π / 180 := by
    have sum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi r hqp
    rw [EuclideanGeometry.angle_comm q r p, EuclideanGeometry.angle_comm r p q] at sum
    linarith
  have hind : AffineIndependent ℝ ![p,q,r] := by
    apply affineIndependent_iff_not_collinear_set.mpr
    rw [EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi]
    simp [Ne.symm hqp, hrq, h₁, show π / 30 ≠ 0 by linarith, show π / 30 ≠ π by linarith]
  let S : Triangle ℝ ℂ := ⟨![p,q,r],hind⟩
  let f := Complex.orthonormalBasisOneI.repr.toAffineIsometryEquiv
  refine ⟨S.map f.toAffineEquiv.toAffineMap f.injective, ?_, ?_, ?_⟩
  · exact (f.toAffineIsometry.angle_map q p r).trans h₀
  · exact (f.toAffineIsometry.angle_map p q r).trans h₁
  · exact (f.toAffineIsometry.angle_map p r q).trans h₂

end Soifer
end

section
namespace Erdos634.Geometry
open Set
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

structure Tri where
  pts : Fin 3 → Plane
  indep : AffineIndependent ℝ pts
namespace Tri

def carrier (T : Tri) : Set Plane := convexHull ℝ (Set.range T.pts)

theorem convex (T : Tri) : Convex ℝ T.carrier := convex_convexHull ℝ _

theorem affineSpan_eq_top (T : Tri) : affineSpan ℝ T.carrier = ⊤ := by
  have h : affineSpan ℝ T.carrier = affineSpan ℝ (Set.range T.pts) :=
    affineSpan_convexHull _
  rw [h]
  exact T.indep.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)
end Tri
structure Dissection (N : ℕ) where
  target : Tri
  tile : Fin N → Tri
  covers : (⋃ i, (tile i).carrier) = target.carrier
  interiors_disjoint :
    Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier)
noncomputable def cornerAngle (p q r : Plane) : ℝ :=
  EuclideanGeometry.angle (V := Plane) p q r

theorem tile_subset_target (D : Dissection N) (j : Fin N) :
    (D.tile j).carrier ⊆ D.target.carrier := by
  rw [← D.covers]; exact Set.subset_iUnion (fun i => (D.tile i).carrier) j

noncomputable def Tri.basis (T : Tri) : AffineBasis (Fin 3) ℝ Plane :=
  AffineBasis.mk T.pts T.indep (by
    have := T.affineSpan_eq_top
    rwa [Tri.carrier, affineSpan_convexHull] at this)

theorem Tri.carrier_eq_nonneg_coord (T : Tri) :
    T.carrier = {y | ∀ i, 0 ≤ T.basis.coord i y} := by
  have h : Set.range T.pts = Set.range (T.basis : Fin 3 → Plane) := rfl
  rw [Tri.carrier, h]
  exact T.basis.convexHull_eq_nonneg_coord
open Classical in
noncomputable def Tri.localAngle (T : Tri) (p : Plane) : ℝ :=
  if h : ∃ j, p = T.pts j then
    cornerAngle (T.pts (h.choose + 1)) (T.pts h.choose) (T.pts (h.choose + 2))
  else if ∀ j, 0 < T.basis.coord j p then 2 * Real.pi
  else if ∃ k, T.basis.coord k p = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord j p then Real.pi
  else 0

theorem Tri.localAngle_nonneg (T : Tri) (p : Plane) : 0 ≤ T.localAngle p := by
  classical
  rw [Tri.localAngle]
  split
  · exact EuclideanGeometry.angle_nonneg _ _ _
  · split
    · positivity
    · split
      · exact Real.pi_pos.le
      · exact le_refl 0
theorem Tri.localAngle_vertex (T : Tri) (k : Fin 3) :
    T.localAngle (T.pts k)
      = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by
  classical
  have hv : ∃ j, T.pts k = T.pts j := ⟨k, rfl⟩
  rw [Tri.localAngle, dif_pos hv]
  have hk : hv.choose = k := T.indep.injective hv.choose_spec.symm
  rw [hk]

theorem Tri.mem_interior_iff_coord_pos (T : Tri) (p : Plane) :
    p ∈ interior T.carrier ↔ ∀ j, 0 < T.basis.coord j p := by
  change p ∈ interior (convexHull ℝ (Set.range (T.basis : Fin 3 → Plane))) ↔ _
  rw [T.basis.interior_convexHull]
  rfl

theorem Dissection.nonempty_idx {n : ℕ} (D : Dissection n) : 0 < n := by
  cases n with
  | zero =>
    have hv : D.target.pts 0 ∈ D.target.carrier := subset_convexHull ℝ _ (Set.mem_range_self 0)
    rw [← D.covers] at hv
    simpa using hv
  | succ n => exact Nat.succ_pos n
end Erdos634.Geometry
end

section
namespace Erdos634.Geometry
open Set
open MeasureTheory Metric
open scoped ENNReal
namespace Tri
theorem isCompact (T : Tri) : IsCompact T.carrier :=
  (Set.finite_range _).isCompact_convexHull ℝ

theorem measurableSet (T : Tri) : MeasurableSet T.carrier := T.isCompact.measurableSet

theorem nullMeasurableSet (T : Tri) : NullMeasurableSet T.carrier volume :=
  T.measurableSet.nullMeasurableSet

theorem volume_frontier (T : Tri) : volume (frontier T.carrier) = 0 :=
  T.convex.addHaar_frontier volume
theorem interior_nonempty (T : Tri) : (interior T.carrier).Nonempty :=
  T.convex.interior_nonempty_iff_affineSpan_eq_top.mpr T.affineSpan_eq_top

theorem volume_pos (T : Tri) : 0 < volume T.carrier :=
  (isOpen_interior.measure_pos volume T.interior_nonempty).trans_le
    (measure_mono interior_subset)
end Tri
namespace Dissection
variable {N : ℕ}

theorem aedisjoint (D : Dissection N) {i j : Fin N} (hij : i ≠ j) :
    AEDisjoint volume (D.tile i).carrier (D.tile j).carrier := by
  have hsub : (D.tile i).carrier ∩ (D.tile j).carrier ⊆
      frontier (D.tile i).carrier ∪ frontier (D.tile j).carrier := by
    rintro x ⟨hxi, hxj⟩
    by_cases h1 : x ∈ interior (D.tile i).carrier
    · by_cases h2 : x ∈ interior (D.tile j).carrier
      · exfalso
        have hd : Disjoint (interior (D.tile i).carrier) (interior (D.tile j).carrier) :=
          D.interiors_disjoint hij
        exact Set.disjoint_left.mp hd h1 h2
      · exact Or.inr ⟨subset_closure hxj, h2⟩
    · exact Or.inl ⟨subset_closure hxi, h1⟩
  refine measure_mono_null hsub ?_
  exact measure_union_null (D.tile i).volume_frontier (D.tile j).volume_frontier

theorem volume_target (D : Dissection N) :
    volume D.target.carrier = ∑ i, volume (D.tile i).carrier := by
  have h := measure_biUnion_finset₀ (μ := volume)
    (s := (Finset.univ : Finset (Fin N))) (f := fun i => (D.tile i).carrier)
    (fun _ _ _ _ hij => D.aedisjoint hij)
    (fun i _ => (D.tile i).nullMeasurableSet)
  have hU : (⋃ i ∈ (Finset.univ : Finset (Fin N)), (D.tile i).carrier) = D.target.carrier := by
    rw [← D.covers]; simp
  rw [hU] at h
  exact h

theorem pos (D : Dissection N) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    have hz := D.volume_target
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hz
    exact absurd hz D.target.volume_pos.ne'
  · exact h
end Dissection
theorem Tri.inter_ball_eq_halfplane (T : Tri) (k : Fin 3) {x : Plane}
    (h1 : 0 < T.basis.coord (k + 1) x) (h2 : 0 < T.basis.coord (k + 2) x) :
    ∃ r > 0, T.carrier ∩ Metric.ball x r
           = {y | 0 ≤ T.basis.coord k y} ∩ Metric.ball x r := by
  have hfin : ∀ j i : Fin 3, i = j ∨ i = j + 1 ∨ i = j + 2 := by decide
  have hc1 : Continuous (T.basis.coord (k + 1)) := AffineMap.continuous_of_finiteDimensional _
  have hc2 : Continuous (T.basis.coord (k + 2)) := AffineMap.continuous_of_finiteDimensional _
  have hopen : IsOpen {y | 0 < T.basis.coord (k + 1) y ∧ 0 < T.basis.coord (k + 2) y} :=
    (isOpen_lt continuous_const hc1).inter (isOpen_lt continuous_const hc2)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x ⟨h1, h2⟩
  refine ⟨r, hr, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, T.carrier_eq_nonneg_coord]
  constructor
  · rintro ⟨hy, hyb⟩; exact ⟨hy k, hyb⟩
  · rintro ⟨hyk, hyb⟩
    refine ⟨fun i => ?_, hyb⟩
    obtain ⟨hp1, hp2⟩ := hball hyb
    rcases hfin k i with rfl | rfl | rfl
    · exact hyk
    · exact hp1.le
    · exact hp2.le

theorem Tri.ball_subset_of_pos (T : Tri) {x : Plane}
    (hpos : ∀ i, 0 < T.basis.coord i x) :
    ∃ r > 0, Metric.ball x r ⊆ T.carrier := by
  have hopen : IsOpen {y : Plane | ∀ i, 0 < T.basis.coord i y} := by
    have : {y : Plane | ∀ i, 0 < T.basis.coord i y} = ⋂ i, {y | 0 < T.basis.coord i y} := by
      ext y; simp [Set.mem_iInter]
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (AffineMap.continuous_of_finiteDimensional _)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x hpos
  refine ⟨r, hr, fun y hy => ?_⟩
  rw [T.carrier_eq_nonneg_coord]
  exact fun i => (hball hy i).le

theorem Tri.ball_disjoint_of_neg (T : Tri) {x : Plane} {k : Fin 3}
    (hneg : T.basis.coord k x < 0) :
    ∃ r > 0, Metric.ball x r ∩ T.carrier = ∅ := by
  have hopen : IsOpen {y : Plane | T.basis.coord k y < 0} :=
    isOpen_lt (AffineMap.continuous_of_finiteDimensional _) continuous_const
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x hneg
  refine ⟨r, hr, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro y ⟨hy1, hy2⟩
  rw [T.carrier_eq_nonneg_coord] at hy2
  exact absurd (hy2 k) (not_le.mpr (hball hy1))

theorem volume_halfspace_inter_ball (L : Plane →ₗ[ℝ] ℝ) (hL : L ≠ 0) (r : ℝ) :
    2 * volume ({v : Plane | 0 ≤ L v} ∩ Metric.ball 0 r) = volume (Metric.ball (0 : Plane) r) := by
  classical
  have hcont : Continuous L := L.continuous_of_finiteDimensional
  set A : Set Plane := {v | 0 ≤ L v} ∩ Metric.ball 0 r with hAdef
  set B : Set Plane := {v | L v ≤ 0} ∩ Metric.ball 0 r with hBdef
  have hBmeas : MeasurableSet B :=
    ((isClosed_le hcont continuous_const).measurableSet).inter Metric.isOpen_ball.measurableSet
  have hBA : B = (fun v : Plane => (-1 : ℝ) • v) ⁻¹' A := by
    ext v
    simp only [hAdef, hBdef, Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq,
      Metric.mem_ball, dist_zero_right, neg_one_smul, map_neg, norm_neg, neg_nonneg]
  have hvolB : volume B = volume A := by
    rw [hBA, Measure.addHaar_preimage_smul volume (by norm_num : (-1 : ℝ) ≠ 0)]
    simp
  have hunion : A ∪ B = Metric.ball (0 : Plane) r := by
    ext v
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
    · intro hv
      rcases le_total (0 : ℝ) (L v) with h | h
      · exact Or.inl ⟨h, hv⟩
      · exact Or.inr ⟨h, hv⟩
  have hker : LinearMap.ker L ≠ ⊤ := fun h => hL (LinearMap.ker_eq_top.mp h)
  have hinter : volume (A ∩ B) = 0 := by
    refine measure_mono_null (fun v hv => ?_) (Measure.addHaar_submodule volume _ hker)
    exact le_antisymm hv.2.1 hv.1.1
  have hie := measure_union_add_inter (μ := volume) A hBmeas
  rw [hunion, hinter, hvolB, add_zero] at hie
  rw [hie, two_mul]

theorem volume_halfplane_inter_ball_at (g : Plane →ᵃ[ℝ] ℝ) (hL : g.linear ≠ 0)
    {x : Plane} (hx : g x = 0) (r : ℝ) :
    2 * volume ({y : Plane | 0 ≤ g y} ∩ Metric.ball x r) = volume (Metric.ball x r) := by
  have hg : ∀ v : Plane, g (x + v) = g.linear v := by
    intro v
    have h := g.map_vadd x v
    simpa [add_comm, hx] using h
  have hballpre : (fun v : Plane => x + v) ⁻¹' Metric.ball x r = Metric.ball 0 r := by
    ext v; simp [Metric.mem_ball, dist_eq_norm, dist_zero_right]
  have hpre : (fun v : Plane => x + v) ⁻¹' ({y : Plane | 0 ≤ g y} ∩ Metric.ball x r)
            = {v : Plane | 0 ≤ g.linear v} ∩ Metric.ball 0 r := by
    rw [Set.preimage_inter, hballpre]
    congr 1
    ext v; simp only [Set.mem_preimage, Set.mem_setOf_eq, hg]
  calc 2 * volume ({y : Plane | 0 ≤ g y} ∩ Metric.ball x r)
      = 2 * volume ((fun v : Plane => x + v) ⁻¹' ({y : Plane | 0 ≤ g y} ∩ Metric.ball x r)) := by
        rw [measure_preimage_add]
    _ = 2 * volume ({v : Plane | 0 ≤ g.linear v} ∩ Metric.ball 0 r) := by rw [hpre]
    _ = volume (Metric.ball (0 : Plane) r) := volume_halfspace_inter_ball _ hL r
    _ = volume (Metric.ball x r) := by rw [← hballpre, measure_preimage_add]

theorem Tri.coord_linear_ne_zero (T : Tri) (k : Fin 3) : (T.basis.coord k).linear ≠ 0 := by
  intro h
  have hne : ∀ j : Fin 3, j ≠ j + 1 := by decide
  have e1 : T.basis.coord k (T.pts k) = 1 := T.basis.coord_apply_eq k
  have e2 : T.basis.coord k (T.pts (k + 1)) = 0 := T.basis.coord_apply_ne (hne k)
  have hdiff : T.basis.coord k (T.pts k) - T.basis.coord k (T.pts (k + 1)) = 0 := by
    have hv := (T.basis.coord k).linearMap_vsub (T.pts k) (T.pts (k + 1))
    rw [h] at hv
    simpa using hv.symm
  rw [e1, e2] at hdiff
  norm_num at hdiff

theorem inter_ball_mono {A B : Set Plane} {x : Plane} {r : ℝ}
    (h : A ∩ Metric.ball x r = B ∩ Metric.ball x r) {r' : ℝ} (hr' : r' ≤ r) :
    A ∩ Metric.ball x r' = B ∩ Metric.ball x r' := by
  have hsub : Metric.ball x r' ⊆ Metric.ball x r := Metric.ball_subset_ball hr'
  ext y
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨hy, hb⟩; exact ⟨((Set.ext_iff.mp h y).mp ⟨hy, hsub hb⟩).1, hb⟩
  · rintro ⟨hy, hb⟩; exact ⟨((Set.ext_iff.mp h y).mpr ⟨hy, hsub hb⟩).1, hb⟩

theorem Tri.volume_inter_ball_edge (T : Tri) (k : Fin 3) {x : Plane}
    (h0 : T.basis.coord k x = 0)
    (h1 : 0 < T.basis.coord (k + 1) x) (h2 : 0 < T.basis.coord (k + 2) x) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      2 * volume (T.carrier ∩ Metric.ball x r') = volume (Metric.ball x r') := by
  obtain ⟨r, hr, hEq⟩ := T.inter_ball_eq_halfplane k h1 h2
  refine ⟨r, hr, fun r' _ hle => ?_⟩
  rw [inter_ball_mono hEq hle]
  exact volume_halfplane_inter_ball_at (T.basis.coord k) (T.coord_linear_ne_zero k) h0 r'

theorem Tri.volume_inter_ball_interior (T : Tri) {x : Plane}
    (hpos : ∀ i, 0 < T.basis.coord i x) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      volume (T.carrier ∩ Metric.ball x r') = volume (Metric.ball x r') := by
  obtain ⟨r, hr, hsub⟩ := T.ball_subset_of_pos hpos
  refine ⟨r, hr, fun r' _ hle => ?_⟩
  congr 1
  exact Set.inter_eq_self_of_subset_right
    (fun y hy => hsub (Metric.ball_subset_ball hle hy))

theorem Tri.volume_inter_ball_exterior (T : Tri) {x : Plane} {k : Fin 3}
    (hneg : T.basis.coord k x < 0) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      volume (T.carrier ∩ Metric.ball x r') = 0 := by
  obtain ⟨r, hr, hemp⟩ := T.ball_disjoint_of_neg hneg
  refine ⟨r, hr, fun r' _ hle => ?_⟩
  have : T.carrier ∩ Metric.ball x r' = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hy1, hy2⟩
    have : y ∈ Metric.ball x r ∩ T.carrier := ⟨Metric.ball_subset_ball hle hy2, hy1⟩
    rw [hemp] at this
    exact this
  rw [this, measure_empty]

theorem Tri.eq_vertex_of_two_coords_zero (T : Tri) {x : Plane} {j k : Fin 3} (hjk : j ≠ k)
    (hj : T.basis.coord j x = 0) (hk : T.basis.coord k x = 0) :
    ∃ m, x = T.pts m := by
  classical
  have key : ∀ u v : Fin 3, u ≠ v →
      ∃ m : Fin 3, m ≠ u ∧ m ≠ v ∧ ∀ b : Fin 3, b ≠ m → b = u ∨ b = v := by decide
  obtain ⟨m, hmj, hmk, hall⟩ := key j k hjk
  have hzero : ∀ b : Fin 3, b ≠ m → T.basis.coord b x = 0 := by
    intro b hb; rcases hall b hb with rfl | rfl
    · exact hj
    · exact hk
  have hm : T.basis.coord m x = 1 := by
    rw [← T.basis.sum_coord_apply_eq_one x]
    exact (Finset.sum_eq_single_of_mem m (Finset.mem_univ m)
      (fun b _ hb => hzero b hb)).symm
  refine ⟨m, T.basis.ext_elem (fun i => ?_)⟩
  by_cases hi : i = m
  · rw [hi, hm]; exact (T.basis.coord_apply_eq m).symm
  · rw [hzero i hi]; exact (T.basis.coord_apply_ne hi).symm

theorem Tri.classify (T : Tri) {x : Plane} (hx : ∀ k, x ≠ T.pts k) :
    (∀ i, 0 < T.basis.coord i x)
  ∨ (∃ k, T.basis.coord k x = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord j x)
  ∨ (∃ k, T.basis.coord k x < 0) := by
  classical
  by_cases hneg : ∃ k, T.basis.coord k x < 0
  · exact Or.inr (Or.inr hneg)
  push_neg at hneg
  by_cases hpos : ∀ i, 0 < T.basis.coord i x
  · exact Or.inl hpos
  push_neg at hpos
  obtain ⟨k, hk⟩ := hpos
  have hk0 : T.basis.coord k x = 0 := le_antisymm hk (hneg k)
  refine Or.inr (Or.inl ⟨k, hk0, fun j hj => ?_⟩)
  rcases (hneg j).lt_or_eq with h | h
  · exact h
  · 
    exact absurd (T.eq_vertex_of_two_coords_zero hj h.symm hk0) (by
      rintro ⟨m, rfl⟩; exact hx m rfl)

theorem exists_common_radius {N : ℕ} (hN : 0 < N) (f : Fin N → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ r > 0, ∀ i, r ≤ f i := by
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne f, ?_, fun i => Finset.inf'_le _ (Finset.mem_univ i)⟩
  rw [gt_iff_lt, Finset.lt_inf'_iff]
  exact fun i _ => hf i

noncomputable def Tri.det (T : Tri) : ℝ :=
  (T.pts 1 - T.pts 0) 0 * (T.pts 2 - T.pts 0) 1 - (T.pts 1 - T.pts 0) 1 * (T.pts 2 - T.pts 0) 0

def cross (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0

@[simp] theorem cross_neg_left (u v : Plane) : cross (-u) v = - cross u v := by
  simp only [cross]; simp; ring
@[simp] theorem cross_self (u : Plane) : cross u u = 0 := by simp only [cross]; ring
@[simp] theorem cross_zero_right (u : Plane) : cross u 0 = 0 := by simp only [cross]; simp
theorem cross_add_right (u v w : Plane) : cross u (v + w) = cross u v + cross u w := by
  simp only [cross]; simp; ring

theorem cross_smul_right (t : ℝ) (u v : Plane) : cross u (t • v) = t * cross u v := by
  simp only [cross]; simp; ring

theorem cross_sum_right {n : ℕ} (u : Plane) (g : Fin n → Plane) :
    cross u (∑ i, g i) = ∑ i, cross u (g i) := by
  classical
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Fin.sum_univ_castSucc, cross_add_right, ih, Fin.sum_univ_castSucc]

theorem Tri.det_cyclic (T : Tri) (k : Fin 3) :
    cross (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts k) = T.det := by
  fin_cases k <;> simp [cross, Tri.det] <;> ring

theorem Tri.coord_mul_det (T : Tri) (k : Fin 3) (y : Plane) :
    T.basis.coord (k + 2) y * T.det = cross (T.pts (k + 1) - T.pts k) (y - T.pts k) := by
  have hsum : ∑ i, T.basis.coord i y = 1 := T.basis.sum_coord_apply_eq_one y
  have hy : ∑ i, T.basis.coord i y • T.pts i = y := T.basis.linear_combination_coord_eq_self y
  have hdec : y - T.pts k = ∑ i, T.basis.coord i y • (T.pts i - T.pts k) := by
    simp only [smul_sub, Finset.sum_sub_distrib, hy, ← Finset.sum_smul, hsum, one_smul]
  rw [hdec, cross_sum_right]
  have hk   : cross (T.pts (k + 1) - T.pts k) (T.pts k - T.pts k) = 0 := by simp
  have hk1  : cross (T.pts (k + 1) - T.pts k) (T.pts (k + 1) - T.pts k) = 0 := cross_self _
  have hk2  := T.det_cyclic k
  have hfin : ∀ j : Fin 3, j = k ∨ j = k + 1 ∨ j = k + 2 := by
    have : ∀ u v : Fin 3, v = u ∨ v = u + 1 ∨ v = u + 2 := by decide
    exact fun j => this k j
  rw [Finset.sum_eq_single (k + 2)]
  · rw [cross_smul_right, hk2]
  · intro j _ hj
    rcases hfin j with rfl | rfl | rfl
    · rw [cross_smul_right, hk, mul_zero]
    · rw [cross_smul_right, hk1, mul_zero]
    · exact absurd rfl hj
  · intro h; exact absurd (Finset.mem_univ _) h

theorem Tri.det_ne_zero (T : Tri) : T.det ≠ 0 := by
  intro h
  have hall : ∀ w : Plane, cross (T.pts 1 - T.pts 0) w = 0 := by
    intro w
    have hid := T.coord_mul_det 0 (T.pts 0 + w)
    simp only [h, mul_zero, add_sub_cancel_left] at hid
    exact hid.symm
  have h0 : (T.pts 1 - T.pts 0) 0 = 0 := by
    have hw := hall (EuclideanSpace.single 1 (1 : ℝ))
    simpa [cross] using hw
  have h1 : (T.pts 1 - T.pts 0) 1 = 0 := by
    have hw := hall (EuclideanSpace.single 0 (1 : ℝ))
    simp [cross] at hw
    simp only [PiLp.sub_apply]
    linarith
  have hzero : T.pts 1 - T.pts 0 = 0 := by
    ext i; fin_cases i
    · simpa using h0
    · simpa using h1
  have hne : (0 : Fin 3) ≠ 1 := by decide
  exact hne (T.indep.injective (sub_eq_zero.mp hzero).symm)
end Erdos634.Geometry
end

section
-- EdgeChain

namespace Erdos634.Geometry
open MeasureTheory Set

theorem cross_sub_right (u a b : Plane) : cross u (a - b) = cross u a - cross u b := by
  simp only [cross, PiLp.sub_apply]; ring

theorem cross_smul_left (t : ℝ) (u v : Plane) : cross (t • u) v = t * cross u v := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]; ring

theorem parallel_of_cross_eq_zero {a b : Plane} (ha : a ≠ 0) (h : cross a b = 0) :
    ∃ τ : ℝ, b = τ • a := by
  have hcomp : a 0 ≠ 0 ∨ a 1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact ha (by ext i; fin_cases i <;> simp [hc.1, hc.2])
  simp only [cross] at h
  rcases hcomp with h0 | h1
  · refine ⟨b 0 / a 0, ?_⟩
    have key0 : b 0 = b 0 / a 0 * a 0 := by field_simp
    have key1 : b 1 = b 0 / a 0 * a 1 := by field_simp; linear_combination h
    ext i
    fin_cases i
    · simpa [smul_eq_mul] using key0
    · simpa [smul_eq_mul] using key1
  · refine ⟨b 1 / a 1, ?_⟩
    have key0 : b 0 = b 1 / a 1 * a 0 := by field_simp; linear_combination -h
    have key1 : b 1 = b 1 / a 1 * a 1 := by field_simp
    ext i
    fin_cases i
    · simpa [smul_eq_mul] using key0
    · simpa [smul_eq_mul] using key1

theorem move_in_ball {x v : Plane} (hv : v ≠ 0) {r : ℝ} (hr : 0 < r) :
    x + (r / (2 * ‖v‖)) • v ∈ Metric.ball x r ∧ 0 < r / (2 * ‖v‖) := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have htpos : 0 < r / (2 * ‖v‖) := by positivity
  refine ⟨?_, htpos⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have hxy : x + (r / (2 * ‖v‖)) • v - x = (r / (2 * ‖v‖)) • v := by abel
  rw [hxy, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
  have hval : r / (2 * ‖v‖) * ‖v‖ = r / 2 := by field_simp
  rw [hval]; linarith

theorem Tri.interior_coord_pos (T : Tri) {y : Plane} (hy : y ∈ interior T.carrier) :
    ∀ j, 0 < T.basis.coord j y := by
  intro j
  have hnn : 0 ≤ T.basis.coord j y := by
    have hmem := interior_subset hy
    rw [T.carrier_eq_nonneg_coord] at hmem
    exact hmem j
  rcases hnn.lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hy
    obtain ⟨w, hw⟩ : ∃ w, (T.basis.coord j).linear w ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact T.coord_linear_ne_zero j (LinearMap.ext fun w => by simpa using hc w)
    obtain ⟨v, hv⟩ : ∃ v, (T.basis.coord j).linear v < 0 := by
      rcases lt_or_gt_of_ne hw with h' | h'
      · exact ⟨w, h'⟩
      · exact ⟨-w, by rw [map_neg]; linarith⟩
    have hvne : v ≠ 0 := by
      rintro rfl
      rw [map_zero] at hv
      exact absurd hv (lt_irrefl 0)
    obtain ⟨hmem, htpos⟩ := move_in_ball (x := y) hvne hr
    have hin : y + (r / (2 * ‖v‖)) • v ∈ T.carrier := interior_subset (hball hmem)
    rw [T.carrier_eq_nonneg_coord] at hin
    have hcoord : T.basis.coord j (y + (r / (2 * ‖v‖)) • v)
        = (T.basis.coord j).linear ((r / (2 * ‖v‖)) • v) + T.basis.coord j y := by
      have h1 := (T.basis.coord j).map_vadd y ((r / (2 * ‖v‖)) • v)
      simp only [vadd_eq_add] at h1
      rw [add_comm ((r / (2 * ‖v‖)) • v) y] at h1
      exact h1
    have hneg : T.basis.coord j (y + (r / (2 * ‖v‖)) • v) < 0 := by
      rw [hcoord, map_smul, smul_eq_mul, h.symm, add_zero]
      exact mul_neg_of_pos_of_neg htpos hv
    exact absurd (hin j) (not_le.mpr hneg)
end Erdos634.Geometry
end

section
namespace Erdos634.SupportFace
open Finset
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_convexHull_max (f : E →ₗ[ℝ] ℝ) (c : ℝ) (s : Finset E)
    (hle : ∀ v ∈ s, f v ≤ c) {x : E} (hx : x ∈ convexHull ℝ (s : Set E)) (hfx : f x = c) :
    x ∈ convexHull ℝ ((s.filter (fun v => f v = c) : Finset E) : Set E) := by
  classical
  rw [Finset.convexHull_eq] at hx
  obtain ⟨w, hw0, hw1, hcm⟩ := hx
  have hcomb : ∑ v ∈ s, w v • v = x := by
    rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hw1]; rfl
  have hdef : ∑ v ∈ s, w v * (c - f v) = 0 := by
    have hfsum : ∑ v ∈ s, w v * f v = c := by
      have : f (∑ v ∈ s, w v • v) = ∑ v ∈ s, w v * f v := by
        rw [map_sum]; simp [map_smul, smul_eq_mul]
      rw [hcomb] at this; rw [← this, hfx]
    calc ∑ v ∈ s, w v * (c - f v)
        = (∑ v ∈ s, w v) * c - ∑ v ∈ s, w v * f v := by
          rw [Finset.sum_mul]; rw [← Finset.sum_sub_distrib]; ring_nf
          exact Finset.sum_congr rfl (fun v _ => by ring)
      _ = 0 := by rw [hw1, hfsum]; ring
  have hterm : ∀ v ∈ s, w v * (c - f v) = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hdef
    intro v hv
    exact mul_nonneg (hw0 v hv) (by linarith [hle v hv])
  have hsupp : ∀ v ∈ s, w v ≠ 0 → f v = c := by
    intro v hv hne
    rcases mul_eq_zero.mp (hterm v hv) with h | h
    · exact absurd h hne
    · linarith
  have hzero : ∀ v ∈ s, v ∉ s.filter (fun v => f v = c) → w v = 0 := by
    intro v hv hnot
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hv, hsupp v hv hne⟩)
  have hsub : s.filter (fun v => f v = c) ⊆ s := Finset.filter_subset _ _
  have hsum1 : ∑ v ∈ s.filter (fun v => f v = c), w v = 1 := by
    rw [Finset.sum_subset hsub hzero]; exact hw1
  rw [Finset.convexHull_eq]
  refine ⟨w, ?_, hsum1, ?_⟩
  · intro v hv; exact hw0 v (Finset.mem_filter.mp hv).1
  · rw [Finset.centerMass_eq_of_sum_1 _ _ hsum1]
    have : ∑ v ∈ s.filter (fun v => f v = c), w v • id v = ∑ v ∈ s, w v • v := by
      refine Finset.sum_subset hsub ?_
      intro v hv hnot; simp [hzero v hv hnot]
    rw [this]; exact hcomb

theorem contact_eq_face (f : E →ₗ[ℝ] ℝ) (c : ℝ) (s : Finset E)
    (hle : ∀ v ∈ s, f v ≤ c) :
    {x ∈ convexHull ℝ (s : Set E) | f x = c}
      = convexHull ℝ ((s.filter (fun v => f v = c) : Finset E) : Set E) := by
  classical
  ext x
  constructor
  · rintro ⟨hx, hfx⟩
    exact mem_convexHull_max f c s hle hx hfx
  · intro hx
    have hsub : ((s.filter (fun v => f v = c) : Finset E) : Set E) ⊆ (s : Set E) := by
      intro v hv; exact (Finset.mem_filter.mp hv).1
    refine ⟨convexHull_mono hsub hx, ?_⟩
    have : convexHull ℝ ((s.filter (fun v => f v = c) : Finset E) : Set E) ⊆ {y | f y = c} := by
      refine convexHull_min ?_ ?_
      · intro v hv; exact (Finset.mem_filter.mp hv).2
      · intro a ha b hb ta tb hta htb htab
        simp only [Set.mem_setOf_eq] at *
        rw [map_add, map_smul, map_smul, ha, hb, smul_eq_mul, smul_eq_mul]
        linear_combination c * htab
    exact this hx
end Erdos634.SupportFace
namespace Erdos634.SegmentDense
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private noncomputable def par (x b : E) (t : ℝ) : E := (1 - t) • x + t • b

private theorem par_mem_segment {x b : E} {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    par x b t ∈ segment ℝ x b := by
  rw [segment_eq_image]
  exact ⟨t, ht, rfl⟩

private theorem par_dist {x b : E} (t : ℝ) : ‖par x b t - x‖ = |t| * ‖b - x‖ := by
  have : par x b t - x = t • (b - x) := by
    simp only [par, smul_sub, sub_smul, one_smul]; abel
  rw [this, norm_smul, Real.norm_eq_abs]

private theorem par_injOn {x b : E} (hxb : x ≠ b) : Function.Injective (par x b) := by
  intro s t hst
  have h : (s - t) • (b - x) = 0 := by
    have : par x b s - par x b t = (s - t) • (b - x) := by
      simp only [par, smul_sub, sub_smul, one_smul]; abel
    rw [← this, hst, sub_self]
  rcases smul_eq_zero.mp h with h1 | h2
  · linarith [sub_eq_zero.mp (by linarith [h1] : s - t = 0)]
  · exact absurd (sub_eq_zero.mp h2).symm hxb

theorem subset_closure_diff_finite {a b : E} (hab : a ≠ b) {F : Set E} (hF : F.Finite) :
    segment ℝ a b ⊆ closure (segment ℝ a b \ F) := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨p, hp, hxp⟩ : ∃ p, p ∈ ({a, b} : Set E) ∧ x ≠ p := by
    by_cases h : x = a
    · exact ⟨b, by simp, by rw [h]; exact hab⟩
    · exact ⟨a, by simp, h⟩
  have hpmem : p ∈ segment ℝ a b := by
    rcases hp with h | h
    · rw [h]; exact left_mem_segment ℝ a b
    · rw [h]; exact right_mem_segment ℝ a b
  have hseg : segment ℝ x p ⊆ segment ℝ a b :=
    (convex_segment a b).segment_subset hx hpmem
  have hnorm : 0 < ‖p - x‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr (Ne.symm hxp)
  set δ : ℝ := min 1 (ε / (2 * ‖p - x‖)) with hδdef
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hinf : (Set.Ioo (0:ℝ) δ).Infinite := Set.Ioo_infinite hδ
  have himg : ((par x p) '' Set.Ioo (0:ℝ) δ).Infinite :=
    hinf.image ((par_injOn hxp).injOn)
  obtain ⟨y, hy, hyF⟩ := (himg.diff hF).nonempty
  obtain ⟨t, ht, rfl⟩ := hy
  refine ⟨par x p t, ⟨hseg (par_mem_segment ⟨le_of_lt ht.1, le_trans (le_of_lt ht.2) (min_le_left _ _)⟩), hyF⟩, ?_⟩
  rw [dist_comm, dist_eq_norm, par_dist, abs_of_pos ht.1]
  have h1 : t < ε / (2 * ‖p - x‖) := lt_of_lt_of_le ht.2 (min_le_right _ _)
  calc t * ‖p - x‖ < (ε / (2 * ‖p - x‖)) * ‖p - x‖ := by
        exact mul_lt_mul_of_pos_right h1 hnorm
    _ = ε / 2 := by field_simp
    _ < ε := by linarith
end Erdos634.SegmentDense
open scoped ENNReal
namespace Erdos634.Geometry
open MeasureTheory Set
namespace Tri
end Tri
namespace Dissection
variable {N : ℕ}
end Dissection

def HasEdgeChains {N : ℕ} (D : Dissection N) (edgeOf : Fin N → Fin 3 → Set Plane) : Prop :=
  ∀ i : Fin 3, ∃ (part : Finset (Fin N × Fin 3)),
    (⋃ e ∈ part, edgeOf e.1 e.2) = segment ℝ (D.target.pts i) (D.target.pts (i + 1))

def Tri.edge (T : Tri) (i : Fin 3) : Set Plane := segment ℝ (T.pts i) (T.pts (i + 1))

theorem tile_contact_face (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hle : ∀ x ∈ T.carrier, f x ≤ c) :
    {x ∈ T.carrier | f x = c}
      = convexHull ℝ (((Finset.univ.image T.pts).filter (fun v => f v = c) : Finset Plane) :
          Set Plane) := by
  classical
  have hmem : ∀ v ∈ (Finset.univ.image T.pts), f v ≤ c := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact hle _ (subset_convexHull ℝ _ ⟨i, rfl⟩)
  have hcar : T.carrier = convexHull ℝ ((Finset.univ.image T.pts : Finset Plane) : Set Plane) := by
    rw [Tri.carrier]; congr 1
    ext x; constructor
    · rintro ⟨i, rfl⟩; exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact ⟨i, rfl⟩
  rw [hcar]
  exact Erdos634.SupportFace.contact_eq_face f c _ hmem

theorem two_vertices_on_line (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hall : ∀ i, f (T.pts i) = c) : False := by
  have hsub : T.carrier ⊆ {x | f x = c} := by
    rw [Tri.carrier]
    refine convexHull_min ?_ ?_
    · rintro x ⟨i, rfl⟩; exact hall i
    · intro a ha b hb ta tb hta htb htab
      simp only [Set.mem_setOf_eq] at *
      rw [map_add, map_smul, map_smul, ha, hb, smul_eq_mul, smul_eq_mul]
      linear_combination c * htab
  obtain ⟨x, hx⟩ := T.interior_nonempty
  have hxc : f x = c := hsub (interior_subset hx)
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (LinearMap.ext fun z => by simp [h z])
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  set t : ℝ := ε / (2 * ‖y‖) with ht
  have hynorm : 0 < ‖y‖ := by
    rcases eq_or_ne y 0 with rfl | hy0
    · simp at hy
    · exact norm_pos_iff.mpr hy0
  have htpos : 0 < t := by positivity
  have hdist : dist (x + t • y) x = t * ‖y‖ := by
    rw [dist_eq_norm]
    have hxy : x + t • y - x = t • y := by abel
    rw [hxy, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
  have hmemball : x + t • y ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, hdist]
    have hhalf : t * ‖y‖ = ε / 2 := by rw [ht]; field_simp
    rw [hhalf]; linarith
  have : f (x + t • y) = c := hsub (interior_subset (hball hmemball))
  rw [map_add, map_smul, hxc, smul_eq_mul] at this
  have : t * f y = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (ne_of_gt htpos)
  · exact hy h

theorem Tri.isClosed_edge (T : Tri) (k : Fin 3) : IsClosed (T.edge k) := by
  have hc : IsCompact (T.edge k) := by
    rw [Tri.edge, segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  exact hc.isClosed

theorem Tri.pair_eq_edge (T : Tri) {p q : Fin 3} (hpq : p ≠ q) :
    ∃ k, segment ℝ (T.pts p) (T.pts q) = T.edge k := by
  simp only [Tri.edge]
  fin_cases p <;> fin_cases q <;> simp_all <;>
    [ exact ⟨0, rfl⟩;
      exact ⟨2, segment_symm ℝ _ _⟩;
      exact ⟨0, segment_symm ℝ _ _⟩;
      exact ⟨1, rfl⟩;
      exact ⟨2, rfl⟩;
      exact ⟨1, segment_symm ℝ _ _⟩ ]

theorem exists_supporting (T : Tri) (i : Fin 3) :
    ∃ (f : Plane →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ (∀ x ∈ T.carrier, f x ≤ c) ∧
      f (T.pts i) = c ∧ f (T.pts (i + 1)) = c ∧ f (T.pts (i + 2)) < c := by
  classical
  set g : Plane →ᵃ[ℝ] ℝ := T.basis.coord (i + 2) with hg
  have hdecomp : ∀ x, g x = g.linear x + g 0 := by
    intro x; simpa using congrFun (AffineMap.decomp g) x
  have hb : ∀ j, g (T.pts j) = if i + 2 = j then 1 else 0 := by
    intro j; exact AffineBasis.coord_apply T.basis (i + 2) j
  have hne1 : i + 2 ≠ i := by fin_cases i <;> decide
  have hne2 : i + 2 ≠ i + 1 := by fin_cases i <;> decide
  have h0 : g (T.pts i) = 0 := by rw [hb]; simp [hne1]
  have h1 : g (T.pts (i + 1)) = 0 := by rw [hb]; simp [hne2]
  have h2 : g (T.pts (i + 2)) = 1 := by rw [hb]; simp
  have hnonneg : ∀ j, (0:ℝ) ≤ g (T.pts j) := by
    intro j; rw [hb]; split <;> norm_num
  refine ⟨-g.linear, g 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro hzero
    have hlin0 : g.linear = 0 := by
      have := congrArg Neg.neg hzero; simpa using this
    have ha := hdecomp (T.pts i)
    have hc := hdecomp (T.pts (i + 2))
    rw [hlin0] at ha hc
    simp only [LinearMap.zero_apply, zero_add] at ha hc
    rw [h0] at ha; rw [h2] at hc
    linarith
  · intro x hx
    rw [Tri.carrier] at hx
    show x ∈ {y : Plane | (-g.linear) y ≤ g 0}
    refine convexHull_min ?_ ?_ hx
    · rintro y ⟨j, rfl⟩
      simp only [Set.mem_setOf_eq, LinearMap.neg_apply]
      linarith [hdecomp (T.pts j), hnonneg j]
    · intro a ha b hb ta tb hta htb htab
      simp only [Set.mem_setOf_eq, LinearMap.neg_apply] at ha hb ⊢
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      have key : -(ta * g.linear a + tb * g.linear b)
               = ta * (-g.linear a) + tb * (-g.linear b) := by ring
      rw [key]
      calc ta * (-g.linear a) + tb * (-g.linear b)
          ≤ ta * g 0 + tb * g 0 :=
            add_le_add (mul_le_mul_of_nonneg_left ha hta) (mul_le_mul_of_nonneg_left hb htb)
        _ = g 0 := by rw [← add_mul, htab, one_mul]
  · simp only [LinearMap.neg_apply]; linarith [hdecomp (T.pts i), h0]
  · simp only [LinearMap.neg_apply]; linarith [hdecomp (T.pts (i + 1)), h1]
  · simp only [LinearMap.neg_apply]; linarith [hdecomp (T.pts (i + 2)), h2]

theorem contact_is_edge (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hle : ∀ x ∈ T.carrier, f x ≤ c) {x : Plane} (hx : x ∈ T.carrier) (hfx : f x = c)
    (hxv : ∀ k, x ≠ T.pts k) :
    ∃ k, {y ∈ T.carrier | f y = c} = T.edge k := by
  classical
  set V : Finset (Fin 3) := Finset.univ.filter (fun k => f (T.pts k) = c) with hV
  have himg : (((Finset.univ.image T.pts).filter (fun v => f v = c) : Finset Plane) : Set Plane)
            = T.pts '' (V : Set (Fin 3)) := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_image] at hv
      obtain ⟨⟨k, _, hk⟩, hfv⟩ := hv
      refine ⟨k, ?_, hk⟩
      rw [Finset.mem_coe, hV, Finset.mem_filter]
      exact ⟨Finset.mem_univ k, by rw [hk]; exact hfv⟩
    · rintro ⟨k, hkV, rfl⟩
      rw [Finset.mem_coe, hV, Finset.mem_filter] at hkV
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_image]
      exact ⟨⟨k, Finset.mem_univ k, rfl⟩, hkV.2⟩
  have hcontact : {y ∈ T.carrier | f y = c} = convexHull ℝ (T.pts '' (V : Set (Fin 3))) := by
    rw [tile_contact_face T f c hle, himg]
  have hxc : x ∈ convexHull ℝ (T.pts '' (V : Set (Fin 3))) := by
    rw [← hcontact]; exact ⟨hx, hfx⟩
  have hcard3 : V.card ≤ 3 := by
    have := Finset.card_le_card (Finset.subset_univ V)
    simpa using this
  interval_cases h : V.card
  · 
    rw [Finset.card_eq_zero] at h
    rw [h] at hxc; simp at hxc
  · 
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h
    rw [hk] at hxc
    simp only [Finset.coe_singleton, Set.image_singleton, convexHull_singleton,
      Set.mem_singleton_iff] at hxc
    exact absurd hxc (hxv k)
  · 
    obtain ⟨p, q, hpq, hV2⟩ := Finset.card_eq_two.mp h
    obtain ⟨k, hk⟩ := T.pair_eq_edge hpq
    refine ⟨k, ?_⟩
    rw [hcontact, hV2]
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]
    rw [convexHull_pair, hk]
  · 
    exfalso
    have hall : ∀ k, f (T.pts k) = c := by
      intro k
      have hmem : k ∈ V := by
        have : V = Finset.univ := Finset.eq_univ_of_card V (by simpa using h)
        rw [this]; exact Finset.mem_univ k
      simpa [hV, Finset.mem_filter] using hmem
    exact two_vertices_on_line T f c hf hall

theorem target_contact_side (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) {i : Fin 3}
    (hle : ∀ x ∈ T.carrier, f x ≤ c) (hi : f (T.pts i) = c) (hi1 : f (T.pts (i + 1)) = c)
    (hi2 : f (T.pts (i + 2)) < c) :
    {x ∈ T.carrier | f x = c} = segment ℝ (T.pts i) (T.pts (i + 1)) := by
  classical
  set V : Finset (Fin 3) := Finset.univ.filter (fun k => f (T.pts k) = c) with hV
  have hexh : ∀ k : Fin 3, k = i ∨ k = i + 1 ∨ k = i + 2 := by
    intro k; fin_cases i <;> fin_cases k <;> decide
  have hVeq : V = {i, i + 1} := by
    apply Finset.Subset.antisymm
    · intro k hk
      rw [hV, Finset.mem_filter] at hk
      rcases hexh k with rfl | rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · exact absurd hk.2 (by linarith)
    · intro k hk
      rw [hV, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_insert.mp hk with rfl | hk'
      · exact hi
      · rw [Finset.mem_singleton.mp hk']; exact hi1
  have himg : (((Finset.univ.image T.pts).filter (fun v => f v = c) : Finset Plane) : Set Plane)
            = T.pts '' (V : Set (Fin 3)) := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_image] at hv
      obtain ⟨⟨k, _, hk⟩, hfv⟩ := hv
      refine ⟨k, ?_, hk⟩
      rw [Finset.mem_coe, hV, Finset.mem_filter]
      exact ⟨Finset.mem_univ k, by rw [hk]; exact hfv⟩
    · rintro ⟨k, hkV, rfl⟩
      rw [Finset.mem_coe, hV, Finset.mem_filter] at hkV
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_image]
      exact ⟨⟨k, Finset.mem_univ k, rfl⟩, hkV.2⟩
  rw [tile_contact_face T f c hle, himg, hVeq]
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]
  rw [convexHull_pair]

theorem hasEdgeChains_edge (D : Dissection N) :
    HasEdgeChains D (fun j k => (D.tile j).edge k) := by
  classical
  intro i
  obtain ⟨f, c, hf, hle, hi, hi1, hi2⟩ := exists_supporting D.target i
  set S : Set Plane := segment ℝ (D.target.pts i) (D.target.pts (i + 1)) with hSdef
  have hS : {x ∈ D.target.carrier | f x = c} = S :=
    target_contact_side D.target f c hle hi hi1 hi2
  set part : Finset (Fin N × Fin 3) :=
    Finset.univ.filter (fun e : Fin N × Fin 3 => (D.tile e.1).edge e.2 ⊆ S) with hpart
  refine ⟨part, ?_⟩
  apply Set.Subset.antisymm
  · 
    intro x hx
    obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.mp hx
    have : (D.tile e.1).edge e.2 ⊆ S := by
      rw [hpart, Finset.mem_filter] at he; exact he.2
    exact this hxe
  · 
    have hFfin : (Set.range fun (jk : Fin N × Fin 3) => (D.tile jk.1).pts jk.2).Finite :=
      Set.finite_range _
    have hUclosed : IsClosed (⋃ e ∈ part, (D.tile e.1).edge e.2) :=
      Set.Finite.isClosed_biUnion (Finset.finite_toSet part)
        (fun e _ => (D.tile e.1).isClosed_edge e.2)
    have hnd : D.target.pts i ≠ D.target.pts (i + 1) := by
      intro h
      have hij : i = i + 1 := D.target.indep.injective h
      fin_cases i <;> exact absurd hij (by decide)
    have hkey : S \ (Set.range fun (jk : Fin N × Fin 3) => (D.tile jk.1).pts jk.2)
              ⊆ ⋃ e ∈ part, (D.tile e.1).edge e.2 := by
      rintro x ⟨hxS, hxF⟩
      have hxt : x ∈ D.target.carrier ∧ f x = c := by rw [← hS] at hxS; exact hxS
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (by rw [D.covers]; exact hxt.1)
      have hlej : ∀ y ∈ (D.tile j).carrier, f y ≤ c :=
        fun y hy => hle y (tile_subset_target D j hy)
      have hxv : ∀ k, x ≠ (D.tile j).pts k := by
        intro k hk; exact hxF ⟨(j, k), hk.symm⟩
      obtain ⟨k, hk⟩ := contact_is_edge (D.tile j) f c hf hlej hxj hxt.2 hxv
      have hsub : (D.tile j).edge k ⊆ S := by
        rw [← hk, ← hS]
        rintro y ⟨hy1, hy2⟩
        exact ⟨tile_subset_target D j hy1, hy2⟩
      refine Set.mem_iUnion₂.mpr ⟨(j, k), ?_, ?_⟩
      · rw [hpart, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hsub⟩
      · rw [← hk]; exact ⟨hxj, hxt.2⟩
    calc S ⊆ closure (S \ (Set.range fun (jk : Fin N × Fin 3) => (D.tile jk.1).pts jk.2)) :=
          Erdos634.SegmentDense.subset_closure_diff_finite hnd hFfin
      _ ⊆ closure (⋃ e ∈ part, (D.tile e.1).edge e.2) := closure_mono hkey
      _ = _ := hUclosed.closure_eq

def Dir : Type := {v : Plane // ‖v‖ = 1}

def Dir.neg (d : Dir) : Dir := ⟨-d.1, by rw [norm_neg]; exact d.2⟩

theorem Tri.edge_subset_carrier (T : Tri) (k : Fin 3) : T.edge k ⊆ T.carrier := by
  refine (convex_convexHull ℝ _).segment_subset ?_ ?_ <;>
    exact subset_convexHull ℝ _ ⟨_, rfl⟩

theorem Tri.coord_eq_zero_of_mem_edge (T : Tri) (k : Fin 3) {x : Plane} (hx : x ∈ T.edge k) :
    T.basis.coord (k + 2) x = 0 := by
  have hne1 : (k + 2) ≠ k := by fin_cases k <;> decide
  have hne2 : (k + 2) ≠ (k + 1) := by fin_cases k <;> decide
  have hconv : Convex ℝ ((T.basis.coord (k + 2)) ⁻¹' {(0 : ℝ)}) :=
    (convex_singleton (0 : ℝ)).affine_preimage _
  have hb : ∀ i : Fin 3, T.pts i = (T.basis : Fin 3 → Plane) i := fun _ => rfl
  refine hconv.segment_subset ?_ ?_ hx
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, hb, AffineBasis.coord_apply]
    simp [hne1]
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, hb, AffineBasis.coord_apply]
    simp [hne2]
end Erdos634.Geometry
end

section

open MeasureTheory Set
namespace Erdos634.SectorArea

def polarBox (θ : ℝ) : Set (ℝ × ℝ) := Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) θ

def sector (θ : ℝ) : Set (ℝ × ℝ) := polarCoord.symm '' polarBox θ

theorem polarBox_subset_target {θ : ℝ} (hθ' : θ < Real.pi) :
    polarBox θ ⊆ polarCoord.target := by
  rintro ⟨r, φ⟩ ⟨⟨hr0, hr1⟩, hφ0, hφθ⟩
  exact ⟨hr0, by linarith [Real.pi_pos], by linarith⟩

theorem lintegral_id_Ioo : ∫⁻ r in Ioo (0:ℝ) 1, ENNReal.ofReal r = ENNReal.ofReal (1/2) := by
  have hmeas : MeasurableSet (Ioo (0:ℝ) 1) := measurableSet_Ioo
  have hint : IntegrableOn (fun r : ℝ => r) (Ioo (0:ℝ) 1) :=
    (continuous_id.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0:ℝ) 1)] fun r : ℝ => r := by
    filter_upwards [ae_restrict_mem hmeas] with r hr using le_of_lt hr.1
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_id]
  norm_num

theorem lintegral_jacobian {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫⁻ p in polarBox θ, ENNReal.ofReal p.1 = ENNReal.ofReal (θ / 2) := by
  have hprod : (volume : Measure (ℝ × ℝ)).restrict (polarBox θ)
      = ((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioo (0:ℝ) θ))) := by
    rw [Measure.prod_restrict, polarBox, ← Measure.volume_eq_prod]
  rw [hprod, MeasureTheory.lintegral_prod _ (by fun_prop)]
  have hinner : ∀ r : ℝ, ∫⁻ _ in Ioo (0:ℝ) θ, ENNReal.ofReal r
      = ENNReal.ofReal r * ENNReal.ofReal θ := by
    intro r
    rw [MeasureTheory.setLIntegral_const, Real.volume_Ioo]
    congr 1
    rw [ENNReal.ofReal_eq_ofReal_iff (by linarith) hθ]
    ring
  simp_rw [hinner]
  rw [MeasureTheory.lintegral_mul_const _ (by fun_prop), lintegral_id_Ioo,
      ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

theorem volume_sector {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ < Real.pi) :
    volume (sector θ) = ENNReal.ofReal (θ / 2) := by
  have hsub := polarBox_subset_target hθ'
  have hboxOpen : IsOpen (polarBox θ) := isOpen_Ioo.prod isOpen_Ioo
  have hbox : MeasurableSet (polarBox θ) := hboxOpen.measurableSet
  have hsec : MeasurableSet (sector θ) :=
    (OpenPartialHomeomorph.isOpen_image_symm_of_subset_target polarCoord hboxOpen hsub).measurableSet
  have key := lintegral_comp_polarCoord_symm ((sector θ).indicator (fun _ => (1 : ENNReal)))
  rw [lintegral_indicator hsec, setLIntegral_one] at key
  have hpt : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • (sector θ).indicator (fun _ => (1 : ENNReal)) (polarCoord.symm p)
        = (polarBox θ).indicator (fun q => ENNReal.ofReal q.1) p := by
    intro p hp
    by_cases hpb : p ∈ polarBox θ
    · have hmem : polarCoord.symm p ∈ sector θ := mem_image_of_mem _ hpb
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hpb, smul_eq_mul, mul_one]
    · have hnot : polarCoord.symm p ∉ sector θ := by
        rintro ⟨q, hq, hqp⟩
        exact hpb (polarCoord.symm.injOn (hsub hq) hp hqp ▸ hq)
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hpb, smul_zero]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hpt,
    setLIntegral_indicator hbox, Set.inter_eq_self_of_subset_left hsub,
    lintegral_jacobian hθ] at key
  exact key.symm
end Erdos634.SectorArea
end

section

open Set Real
namespace Erdos634.Wedge

def polarBox (θ : ℝ) : Set (ℝ × ℝ) := Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) θ

def sector (θ : ℝ) : Set (ℝ × ℝ) := polarCoord.symm '' polarBox θ

theorem symm_apply (r φ : ℝ) : polarCoord.symm (r, φ) = (r * Real.cos φ, r * Real.sin φ) := rfl

theorem sector_subset_halfplanes {θ : ℝ} (hπ : θ < Real.pi) :
    sector θ ⊆ {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
             ∩ {p : ℝ × ℝ | 0 < p.2}
             ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2} := by
  rintro _ ⟨⟨r, φ⟩, ⟨hr, hφ⟩, rfl⟩
  obtain ⟨hr0, hr1⟩ := hr
  obtain ⟨hφ0, hφθ⟩ := hφ
  have hφπ : φ < Real.pi := lt_trans hφθ hπ
  have hsinφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 hφπ
  rw [symm_apply]
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · 
    have : (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 = r ^ 2 := by
      have := Real.sin_sq_add_cos_sq φ
      nlinarith [this]
    rw [this]
    nlinarith
  · 
    exact mul_pos hr0 hsinφ
  · 
    have hexp : Real.sin θ * (r * Real.cos φ) - Real.cos θ * (r * Real.sin φ)
        = r * Real.sin (θ - φ) := by
      rw [Real.sin_sub]; ring
    rw [hexp]
    have : 0 < Real.sin (θ - φ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    exact mul_pos hr0 this

theorem pos_of_sin_pos {x : ℝ} (hlo : -Real.pi < x) (hs : 0 < Real.sin x) : 0 < x := by
  by_contra h
  simp only [not_lt] at h
  have : Real.sin x ≤ 0 := by
    rcases eq_or_lt_of_le h with rfl | hneg
    · simp
    · have h1 : 0 < -x := by linarith
      have h2 : -x < Real.pi := by linarith
      have := Real.sin_pos_of_pos_of_lt_pi h1 h2
      rw [Real.sin_neg] at this; linarith
  linarith

theorem halfplanes_subset_sector {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
      ∩ {p : ℝ × ℝ | 0 < p.2}
      ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2} ⊆ sector θ := by
  rintro p ⟨⟨hball, hy⟩, hwedge⟩
  simp only [Set.mem_setOf_eq] at hball hy hwedge
  have hsrc : p ∈ polarCoord.source := Or.inr (by simpa using ne_of_gt hy)
  set q := polarCoord p with hq
  have hinv : polarCoord.symm q = p := polarCoord.left_inv hsrc
  have hqt : q ∈ polarCoord.target := polarCoord.map_source hsrc
  obtain ⟨hr, hφ⟩ := hqt
  simp only [Set.mem_Ioi] at hr
  simp only [Set.mem_Ioo] at hφ
  have hp1 : p.1 = q.1 * Real.cos q.2 := by rw [← hinv]; rfl
  have hp2 : p.2 = q.1 * Real.sin q.2 := by rw [← hinv]; rfl
  have hsinφ : 0 < Real.sin q.2 := by
    by_contra h
    simp only [not_lt] at h
    rw [hp2] at hy
    nlinarith
  have hφpos : 0 < q.2 := pos_of_sin_pos hφ.1 hsinφ
  have hkey : Real.sin θ * p.1 - Real.cos θ * p.2 = q.1 * Real.sin (θ - q.2) := by
    rw [hp1, hp2, Real.sin_sub]; ring
  have hsinsub : 0 < Real.sin (θ - q.2) := by
    by_contra h
    simp only [not_lt] at h
    rw [hkey] at hwedge
    nlinarith
  have hφθ : q.2 < θ := by
    have := pos_of_sin_pos (by linarith [hφ.2]) hsinsub
    linarith
  have hrad : q.1 < 1 := by
    have hsq : q.1 ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
      rw [hp1, hp2]; nlinarith [Real.sin_sq_add_cos_sq q.2]
    nlinarith
  exact ⟨q, ⟨⟨hr, hrad⟩, ⟨hφpos, hφθ⟩⟩, hinv⟩

theorem sector_eq_halfplanes {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    sector θ = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
             ∩ {p : ℝ × ℝ | 0 < p.2}
             ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2} :=
  Set.Subset.antisymm (sector_subset_halfplanes hπ) (halfplanes_subset_sector h0 hπ)
end Erdos634.Wedge
end

section

open MeasureTheory Set
namespace Erdos634.E2Join

theorem sector_agree (θ : ℝ) : Wedge.sector θ = SectorArea.sector θ := rfl

theorem volume_halfplane_wedge {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    volume ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
          ∩ {p : ℝ × ℝ | 0 < p.2}
          ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2})
      = ENNReal.ofReal (θ / 2) := by
  rw [← Wedge.sector_eq_halfplanes h0 hπ, sector_agree]
  exact SectorArea.volume_sector (le_of_lt h0) hπ

def toPair (p : EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ :=
  MeasurableEquiv.finTwoArrow (WithLp.ofLp p)

theorem measurePreserving_toPair : MeasurePreserving toPair :=
  (MeasureTheory.volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

def wedge (θ : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  toPair ⁻¹' ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
            ∩ {p : ℝ × ℝ | 0 < p.2}
            ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2})

theorem volume_wedge {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    volume (wedge θ) = ENNReal.ofReal (θ / 2) := by
  have hopen : IsOpen ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
      ∩ {p : ℝ × ℝ | 0 < p.2} ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2}) := by
    refine IsOpen.inter (IsOpen.inter ?_ ?_) ?_
    · exact isOpen_lt (by fun_prop) continuous_const
    · exact isOpen_lt continuous_const (by fun_prop)
    · exact isOpen_lt continuous_const (by fun_prop)
  rw [wedge, measurePreserving_toPair.measure_preimage hopen.measurableSet.nullMeasurableSet]
  exact volume_halfplane_wedge h0 hπ
end Erdos634.E2Join
end

section
-- VertexSector

namespace Erdos634.Geometry
open MeasureTheory Set Metric InnerProductGeometry
open scoped RealInnerProductSpace Pointwise

theorem inner_coords (x y : Plane) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial,
    Fin.sum_univ_two]
  ring

theorem norm_sq_coords (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coords]
  ring

theorem cross_swap (u v : Plane) : cross u v = - cross v u := by
  simp only [cross]; ring

theorem mem_ball_sq (y : Plane) : y ∈ Metric.ball (0 : Plane) 1 ↔ y 0 ^ 2 + y 1 ^ 2 < 1 := by
  rw [Metric.mem_ball, dist_zero_right, ← norm_sq_coords]
  constructor
  · intro h
    nlinarith [norm_nonneg y]
  · intro h
    nlinarith [norm_nonneg y]

noncomputable def rot90 (u : Plane) : Plane :=
  EuclideanSpace.single 0 (-(u 1)) + EuclideanSpace.single 1 (u 0)

@[simp] theorem rot90_apply0 (u : Plane) : rot90 u 0 = -(u 1) := by
  simp [rot90]
@[simp] theorem rot90_apply1 (u : Plane) : rot90 u 1 = u 0 := by
  simp [rot90]
noncomputable def frame (u n : Plane) : Plane →ₗ[ℝ] Plane where
  toFun q := q 0 • u + q 1 • n
  map_add' a b := by
    show ((a + b) 0) • u + ((a + b) 1) • n = (a 0 • u + a 1 • n) + (b 0 • u + b 1 • n)
    simp only [PiLp.add_apply]
    module
  map_smul' c a := by
    show ((c • a) 0) • u + ((c • a) 1) • n = c • (a 0 • u + a 1 • n)
    simp only [PiLp.smul_apply, smul_eq_mul]
    module

theorem frame_apply (u n q : Plane) (i : Fin 2) :
    frame u n q i = q 0 * u i + q 1 * n i := by
  show (q 0 • u + q 1 • n) i = _
  simp [PiLp.add_apply, PiLp.smul_apply]

theorem frame_det (u n : Plane) : LinearMap.det (frame u n) = u 0 * n 1 - n 0 * u 1 := by
  classical
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (frame u n),
    Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, frame_apply, PiLp.single_apply]
  norm_num

theorem inner_sq_add_cross_sq (u v : Plane) :
    ⟪u, v⟫ ^ 2 + cross u v ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [inner_coords, norm_sq_coords, norm_sq_coords]
  simp only [cross]
  ring

theorem cos_angle_eq_inner (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    Real.cos (angle u v) = ⟪u, v⟫ := by
  rw [cos_angle, hu, hv]
  norm_num

theorem sin_angle_eq_cross (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < cross u v) : Real.sin (angle u v) = cross u v := by
  have h := sin_angle_mul_norm_mul_norm u v
  rw [hu, hv] at h
  have hlag : ⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ * ⟪u, v⟫ = cross u v ^ 2 := by
    have hl := inner_sq_add_cross_sq u v
    rw [hu, hv] at hl
    have huu : ⟪u, u⟫ = (1:ℝ) := by
      rw [real_inner_self_eq_norm_sq, hu]; norm_num
    have hvv : ⟪v, v⟫ = (1:ℝ) := by
      rw [real_inner_self_eq_norm_sq, hv]; norm_num
    rw [huu, hvv]
    linear_combination - hl
  rw [hlag] at h
  rw [Real.sqrt_sq hpos.le] at h
  simpa using h

theorem angle_mem_Ioo (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < cross u v) : 0 < angle u v ∧ angle u v < Real.pi := by
  have hsin : 0 < Real.sin (angle u v) := by
    rw [sin_angle_eq_cross u v hu hv hpos]; exact hpos
  constructor
  · rcases (angle_nonneg u v).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, Real.sin_zero] at hsin
      exact lt_irrefl 0 hsin
  · rcases (angle_le_pi u v).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [h, Real.sin_pi] at hsin
      exact lt_irrefl 0 hsin

theorem mem_wedge_iff (θ : ℝ) (q : Plane) :
    q ∈ Erdos634.E2Join.wedge θ ↔
      q 0 ^ 2 + q 1 ^ 2 < 1 ∧ 0 < q 1 ∧ 0 < Real.sin θ * q 0 - Real.cos θ * q 1 := by
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨by simpa only [Set.mem_ofPred_eq, show (Erdos634.E2Join.toPair q).1 = q 0 from rfl, show (Erdos634.E2Join.toPair q).2 = q 1 from rfl, pow_two] using h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨by simpa only [Set.mem_ofPred_eq, show (Erdos634.E2Join.toPair q).1 = q 0 from rfl, show (Erdos634.E2Join.toPair q).2 = q 1 from rfl, pow_two] using h1, h2⟩, h3⟩

theorem frame_image_wedge (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < cross u v) :
    frame u (rot90 u) '' Erdos634.E2Join.wedge (angle u v)
      = {y : Plane | 0 < cross u y} ∩ {y : Plane | 0 < cross y v}
          ∩ Metric.ball (0 : Plane) 1 := by
  have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by rw [← norm_sq_coords, hu]; norm_num
  have hsin := sin_angle_eq_cross u v hu hv hpos
  have hcos := cos_angle_eq_inner u v hu hv
  have hF0 : ∀ q : Plane, frame u (rot90 u) q 0 = q 0 * u 0 - q 1 * u 1 := by
    intro q; rw [frame_apply, rot90_apply0]; ring
  have hF1 : ∀ q : Plane, frame u (rot90 u) q 1 = q 0 * u 1 + q 1 * u 0 := by
    intro q; rw [frame_apply, rot90_apply1]
  have hnorm : ∀ q : Plane,
      (frame u (rot90 u) q) 0 ^ 2 + (frame u (rot90 u) q) 1 ^ 2 = q 0 ^ 2 + q 1 ^ 2 := by
    intro q
    rw [hF0, hF1]
    linear_combination (q 0 ^ 2 + q 1 ^ 2) * hu2
  have hcru : ∀ q : Plane, cross u (frame u (rot90 u) q) = q 1 := by
    intro q
    simp only [cross]
    rw [hF0, hF1]
    linear_combination (q 1) * hu2
  have hcrv : ∀ q : Plane, cross (frame u (rot90 u) q) v
      = Real.sin (angle u v) * q 0 - Real.cos (angle u v) * q 1 := by
    intro q
    rw [hsin, hcos, inner_coords]
    simp only [cross]
    rw [hF0, hF1]
    ring
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [mem_wedge_iff] at hq
    obtain ⟨h1, h2, h3⟩ := hq
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show 0 < cross u (frame u (rot90 u) q)
      rw [hcru]; exact h2
    · show 0 < cross (frame u (rot90 u) q) v
      rw [hcrv]; exact h3
    · rw [mem_ball_sq, hnorm]; exact h1
  · rintro ⟨⟨hy1, hy2⟩, hy3⟩
    set q : Plane := EuclideanSpace.single (0 : Fin 2) (u 0 * y 0 + u 1 * y 1)
      + EuclideanSpace.single (1 : Fin 2) (cross u y) with hqdef
    have hq0 : q 0 = u 0 * y 0 + u 1 * y 1 := by
      rw [hqdef]; simp
    have hq1 : q 1 = cross u y := by
      rw [hqdef]; simp
    have hcuy : cross u y = u 0 * y 1 - u 1 * y 0 := rfl
    have hy2' : 0 < y 0 * v 1 - y 1 * v 0 := hy2
    have hy1' : 0 < cross u y := hy1
    refine ⟨q, ?_, ?_⟩
    · rw [mem_wedge_iff]
      rw [mem_ball_sq] at hy3
      refine ⟨?_, ?_, ?_⟩
      · rw [hq0, hq1, hcuy]
        have hid : (u 0 * y 0 + u 1 * y 1) ^ 2 + (u 0 * y 1 - u 1 * y 0) ^ 2
            = y 0 ^ 2 + y 1 ^ 2 := by
          linear_combination (y 0 ^ 2 + y 1 ^ 2) * hu2
        rw [hid]
        exact hy3
      · rw [hq1]; exact hy1'
      · rw [hq0, hq1, hsin, hcos, inner_coords, hcuy]
        have hid : cross u v * (u 0 * y 0 + u 1 * y 1)
            - (u 0 * v 0 + u 1 * v 1) * (u 0 * y 1 - u 1 * y 0)
            = y 0 * v 1 - y 1 * v 0 := by
          simp only [cross]
          linear_combination (y 0 * v 1 - y 1 * v 0) * hu2
        rw [hid]
        exact hy2'
    · ext i
      fin_cases i
      · show frame u (rot90 u) q 0 = y 0
        rw [hF0, hq0, hq1, hcuy]
        linear_combination (y 0) * hu2
      · show frame u (rot90 u) q 1 = y 1
        rw [hF1, hq0, hq1, hcuy]
        linear_combination (y 1) * hu2

def vertexCone (u v : Plane) : Set Plane :=
  {y | 0 ≤ cross u y * cross u v ∧ 0 ≤ cross y v * cross u v}

theorem vertexCone_swap (u v : Plane) : vertexCone v u = vertexCone u v := by
  ext y
  simp only [vertexCone, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · calc (0:ℝ) ≤ cross y u * cross v u := h2
        _ = cross u y * cross u v := by rw [cross_swap y u, cross_swap v u]; ring
    · calc (0:ℝ) ≤ cross v y * cross v u := h1
        _ = cross y v * cross u v := by rw [cross_swap v y, cross_swap v u]; ring
  · rintro ⟨h1, h2⟩
    constructor
    · calc (0:ℝ) ≤ cross y v * cross u v := h2
        _ = cross v y * cross v u := by rw [cross_swap v y, cross_swap v u]; ring
    · calc (0:ℝ) ≤ cross u y * cross u v := h1
        _ = cross y u * cross v u := by rw [cross_swap y u, cross_swap v u]; ring

theorem nonneg_of_mul_nonneg_left' {a c : ℝ} (h : 0 ≤ c * a) (hc : 0 < c) : 0 ≤ a := by
  nlinarith

theorem vertexCone_smul (u v : Plane) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    vertexCone (s • u) (t • v) = vertexCone u v := by
  have e1 : ∀ y : Plane, cross (s • u) y * cross (s • u) (t • v)
      = (s * s * t) * (cross u y * cross u v) := by
    intro y
    rw [cross_smul_left, cross_smul_left, cross_smul_right]
    ring
  have e2 : ∀ y : Plane, cross y (t • v) * cross (s • u) (t • v)
      = (s * t * t) * (cross y v * cross u v) := by
    intro y
    rw [cross_smul_right, cross_smul_left, cross_smul_right]
    ring
  have h1 : (0:ℝ) < s * s * t := by positivity
  have h2 : (0:ℝ) < s * t * t := by positivity
  ext y
  simp only [vertexCone, Set.mem_setOf_eq, e1, e2]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨nonneg_of_mul_nonneg_left' ha h1, nonneg_of_mul_nonneg_left' hb h2⟩
  · rintro ⟨ha, hb⟩
    exact ⟨mul_nonneg h1.le ha, mul_nonneg h2.le hb⟩

theorem volume_cross_zero (u v : Plane) (hne : cross u v ≠ 0) :
    volume {y : Plane | cross u y = 0} = 0 := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hne
    show (0:Plane) 0 * v 1 - (0:Plane) 1 * v 0 = 0
    simp
  have hsub : {y : Plane | cross u y = 0} ⊆ (Submodule.span ℝ {u} : Submodule ℝ Plane) := by
    intro y hy
    obtain ⟨τ, hτ⟩ := parallel_of_cross_eq_zero hu0 hy
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    exact ⟨τ, hτ.symm⟩
  have htop : (Submodule.span ℝ ({u} : Set Plane)) ≠ ⊤ := by
    intro htop
    have hv : v ∈ Submodule.span ℝ ({u} : Set Plane) := by
      rw [htop]; trivial
    obtain ⟨τ, hτ⟩ := Submodule.mem_span_singleton.mp hv
    apply hne
    rw [← hτ, cross_smul_right, cross_self, mul_zero]
  have hnull := MeasureTheory.Measure.addHaar_submodule (volume : Measure Plane) _ htop
  have hle : volume {y : Plane | cross u y = 0}
      ≤ volume ((Submodule.span ℝ ({u} : Set Plane) : Submodule ℝ Plane) : Set Plane) :=
    measure_mono hsub
  rw [hnull] at hle
  exact nonpos_iff_eq_zero.mp hle

theorem volume_vertexCone_unit_pos (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < cross u v) :
    volume (vertexCone u v ∩ Metric.ball (0 : Plane) 1)
      = ENNReal.ofReal (angle u v / 2) := by
  set θ := angle u v with hθ
  obtain ⟨hθ0, hθπ⟩ := angle_mem_Ioo u v hu hv hpos
  have hopen : volume ({y : Plane | 0 < cross u y} ∩ {y : Plane | 0 < cross y v}
      ∩ Metric.ball (0 : Plane) 1) = ENNReal.ofReal (θ / 2) := by
    rw [← frame_image_wedge u v hu hv hpos,
      Measure.addHaar_image_linearMap volume (frame u (rot90 u))]
    have hdet : LinearMap.det (frame u (rot90 u)) = 1 := by
      rw [frame_det, rot90_apply0, rot90_apply1]
      have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by rw [← norm_sq_coords, hu]; norm_num
      linear_combination hu2
    rw [hdet]
    simp only [abs_one, ENNReal.ofReal_one, one_mul]
    exact Erdos634.E2Join.volume_wedge hθ0 hθπ
  have hCpos : vertexCone u v = {y : Plane | 0 ≤ cross u y ∧ 0 ≤ cross y v} := by
    ext y
    simp only [vertexCone, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · nlinarith [h1, hpos]
      · nlinarith [h2, hpos]
    · rintro ⟨h1, h2⟩
      exact ⟨mul_nonneg h1 hpos.le, mul_nonneg h2 hpos.le⟩
  have hsplit : vertexCone u v ∩ Metric.ball (0 : Plane) 1
      ⊆ ({y : Plane | 0 < cross u y} ∩ {y : Plane | 0 < cross y v}
          ∩ Metric.ball (0 : Plane) 1)
        ∪ ({y : Plane | cross u y = 0} ∪ {y : Plane | cross y v = 0}) := by
    rintro y ⟨hy, hyb⟩
    rw [hCpos] at hy
    obtain ⟨h1, h2⟩ := hy
    rcases h1.lt_or_eq with h1' | h1'
    · rcases h2.lt_or_eq with h2' | h2'
      · exact Or.inl ⟨⟨h1', h2'⟩, hyb⟩
      · exact Or.inr (Or.inr h2'.symm)
    · exact Or.inr (Or.inl h1'.symm)
  have hnull1 : volume {y : Plane | cross u y = 0} = 0 :=
    volume_cross_zero u v hpos.ne'
  have hnull2 : volume {y : Plane | cross y v = 0} = 0 := by
    have hvu : cross v u ≠ 0 := by
      rw [cross_swap v u]
      simpa using hpos.ne'
    have h := volume_cross_zero v u hvu
    have hEq : {y : Plane | cross y v = 0} = {y : Plane | cross v y = 0} := by
      ext y
      simp only [Set.mem_setOf_eq]
      rw [cross_swap y v]
      constructor <;> intro h' <;> linarith
    rw [hEq]
    exact h
  have hle1 : volume (vertexCone u v ∩ Metric.ball (0 : Plane) 1)
      ≤ ENNReal.ofReal (θ / 2) := by
    calc volume (vertexCone u v ∩ Metric.ball (0 : Plane) 1)
        ≤ volume (({y : Plane | 0 < cross u y} ∩ {y : Plane | 0 < cross y v}
            ∩ Metric.ball (0 : Plane) 1)
          ∪ ({y : Plane | cross u y = 0} ∪ {y : Plane | cross y v = 0})) :=
          measure_mono hsplit
      _ ≤ volume ({y : Plane | 0 < cross u y} ∩ {y : Plane | 0 < cross y v}
            ∩ Metric.ball (0 : Plane) 1)
          + volume ({y : Plane | cross u y = 0} ∪ {y : Plane | cross y v = 0}) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (θ / 2) + (volume {y : Plane | cross u y = 0}
          + volume {y : Plane | cross y v = 0}) := by
          rw [hopen]
          have hun : volume ({y : Plane | cross u y = 0} ∪ {y : Plane | cross y v = 0})
              ≤ volume {y : Plane | cross u y = 0} + volume {y : Plane | cross y v = 0} :=
            measure_union_le _ _
          exact add_le_add le_rfl hun
      _ = ENNReal.ofReal (θ / 2) := by rw [hnull1, hnull2, add_zero, add_zero]
  have hle2 : ENNReal.ofReal (θ / 2)
      ≤ volume (vertexCone u v ∩ Metric.ball (0 : Plane) 1) := by
    rw [← hopen]
    refine measure_mono ?_
    rintro y ⟨⟨h1, h2⟩, hyb⟩
    refine ⟨?_, hyb⟩
    rw [hCpos]
    exact ⟨h1.le, h2.le⟩
  exact le_antisymm hle1 hle2

theorem volume_vertexCone_unit (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hne : cross u v ≠ 0) :
    volume (vertexCone u v ∩ Metric.ball (0 : Plane) 1)
      = ENNReal.ofReal (angle u v / 2) := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hpos' : 0 < cross v u := by
      rw [cross_swap v u]; linarith
    rw [← vertexCone_swap, angle_comm]
    exact volume_vertexCone_unit_pos v u hv hu hpos'
  · exact volume_vertexCone_unit_pos u v hu hv hpos

theorem vertexCone_ball_smul (u v : Plane) {r : ℝ} (hr : 0 < r) :
    vertexCone u v ∩ Metric.ball (0 : Plane) r
      = r • (vertexCone u v ∩ Metric.ball (0 : Plane) 1) := by
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne']
  simp only [vertexCone, Set.mem_inter_iff, Set.mem_setOf_eq, Metric.mem_ball,
    dist_zero_right, cross_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hrinv]
  have hcl : ∀ z : Plane, cross (r⁻¹ • y) z = r⁻¹ * cross y z := fun z =>
    cross_smul_left r⁻¹ y z
  rw [hcl]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · calc (0:ℝ) ≤ r⁻¹ * (cross u y * cross u v) := by positivity
        _ = r⁻¹ * cross u y * cross u v := by ring
    · calc (0:ℝ) ≤ r⁻¹ * (cross y v * cross u v) := by positivity
        _ = r⁻¹ * cross y v * cross u v := by ring
    · calc r⁻¹ * ‖y‖ < r⁻¹ * r := mul_lt_mul_of_pos_left h3 hrinv
        _ = 1 := inv_mul_cancel₀ hr.ne'
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have h1' : 0 ≤ r * (r⁻¹ * cross u y * cross u v) := by positivity
      calc (0:ℝ) ≤ r * (r⁻¹ * cross u y * cross u v) := h1'
        _ = cross u y * cross u v := by
            field_simp
    · have h2' : 0 ≤ r * (r⁻¹ * cross y v * cross u v) := by positivity
      calc (0:ℝ) ≤ r * (r⁻¹ * cross y v * cross u v) := h2'
        _ = cross y v * cross u v := by
            field_simp
    · have := mul_lt_mul_of_pos_left h3 hr
      rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul, mul_one] at this
      exact this

theorem volume_vertexCone_ball (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hne : cross u v ≠ 0) {r : ℝ} (hr : 0 < r) :
    volume (vertexCone u v ∩ Metric.ball (0 : Plane) r)
      = ENNReal.ofReal (angle u v / 2 * r ^ 2) := by
  rw [vertexCone_ball_smul u v hr, Measure.addHaar_smul,
    volume_vertexCone_unit u v hu hv hne]
  have hfr : Module.finrank ℝ Plane = 2 := finrank_euclideanSpace_fin
  rw [hfr]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ 2)]
  ring

noncomputable def Tri.edgeVec (T : Tri) (j : Fin 3) : Plane := T.pts (j + 1) - T.pts j

theorem Tri.edgeVec_ne_zero (T : Tri) (j : Fin 3) : T.edgeVec j ≠ 0 := by
  rw [Tri.edgeVec, sub_ne_zero]
  intro h
  have h1 : j + 1 = j := T.indep.injective h
  have h2 : ∀ m : Fin 3, m + 1 ≠ m := by decide
  exact h2 j h1

noncomputable def Tri.edgeVec' (T : Tri) (j : Fin 3) : Plane := T.pts (j + 2) - T.pts j

theorem Tri.edgeVec'_ne_zero (T : Tri) (j : Fin 3) : T.edgeVec' j ≠ 0 := by
  rw [Tri.edgeVec', sub_ne_zero]
  intro h
  have h1 : j + 2 = j := T.indep.injective h
  have h2 : ∀ m : Fin 3, m + 2 ≠ m := by decide
  exact h2 j h1

theorem Tri.cross_edgeVec (T : Tri) (j : Fin 3) :
    cross (T.edgeVec j) (T.edgeVec' j) = T.det := T.det_cyclic j

theorem Tri.inter_ball_eq_vertexCone (T : Tri) (j : Fin 3) :
    ∃ r > 0, T.carrier ∩ Metric.ball (T.pts j) r
      = {y : Plane | y - T.pts j ∈ vertexCone (T.edgeVec j) (T.edgeVec' j)}
        ∩ Metric.ball (T.pts j) r := by
  have hcont : Continuous (T.basis.coord j) := AffineMap.continuous_of_finiteDimensional _
  have hj1 : T.basis.coord j (T.pts j) = 1 := T.basis.coord_apply_eq j
  have hopen : IsOpen {y : Plane | 0 < T.basis.coord j y} :=
    isOpen_lt continuous_const hcont
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen (T.pts j) (by
    rw [Set.mem_setOf_eq, hj1]; norm_num)
  refine ⟨r, hr, ?_⟩
  have hfin : ∀ m : Fin 3, (m + 2) + 2 = m + 1 ∧ (m + 2) + 1 = m := by decide
  have hc2 : ∀ y : Plane, T.basis.coord (j + 2) y * T.det
      = cross (T.edgeVec j) (y - T.pts j) := fun y => T.coord_mul_det j y
  have hc1 : ∀ y : Plane, T.basis.coord (j + 1) y * T.det
      = cross (y - T.pts j) (T.edgeVec' j) := by
    intro y
    have h := T.coord_mul_det (j + 2) y
    rw [(hfin j).1, (hfin j).2] at h
    rw [h]
    have hsplit : y - T.pts (j + 2) = (y - T.pts j) - T.edgeVec' j := by
      rw [Tri.edgeVec']; abel
    have h1 : T.pts j - T.pts (j + 2) = -(T.edgeVec' j) := by
      rw [Tri.edgeVec']; abel
    rw [hsplit, cross_sub_right, h1, cross_neg_left, cross_neg_left, cross_self,
      neg_zero, sub_zero]
    rw [cross_swap (T.edgeVec' j) ((y - T.pts j))]
    ring
  have hsq : (0:ℝ) < T.det ^ 2 := by
    have := T.det_ne_zero
    positivity
  ext y
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, T.carrier_eq_nonneg_coord, vertexCone]
  constructor
  · rintro ⟨hy, hyb⟩
    refine ⟨⟨?_, ?_⟩, hyb⟩
    · rw [T.cross_edgeVec j]
      have h := hc2 y
      have hcd : cross (T.edgeVec j) (y - T.pts j) * T.det
          = T.basis.coord (j + 2) y * T.det ^ 2 := by rw [← h]; ring
      rw [hcd]
      exact mul_nonneg (hy (j + 2)) hsq.le
    · rw [T.cross_edgeVec j]
      have h := hc1 y
      have hcd : cross (y - T.pts j) (T.edgeVec' j) * T.det
          = T.basis.coord (j + 1) y * T.det ^ 2 := by rw [← h]; ring
      rw [hcd]
      exact mul_nonneg (hy (j + 1)) hsq.le
  · rintro ⟨⟨h1, h2⟩, hyb⟩
    rw [T.cross_edgeVec j] at h1 h2
    refine ⟨fun i => ?_, hyb⟩
    have hexh : ∀ m i : Fin 3, i = m ∨ i = m + 1 ∨ i = m + 2 := by decide
    rcases hexh j i with rfl | rfl | rfl
    · exact (hball hyb).le
    · have h := hc1 y
      have hcd : cross (y - T.pts j) (T.edgeVec' j) * T.det
          = T.basis.coord (j + 1) y * T.det ^ 2 := by rw [← h]; ring
      rw [hcd] at h2
      nlinarith [h2, hsq]
    · have h := hc2 y
      have hcd : cross (T.edgeVec j) (y - T.pts j) * T.det
          = T.basis.coord (j + 2) y * T.det ^ 2 := by rw [← h]; ring
      rw [hcd] at h1
      nlinarith [h1, hsq]

theorem Tri.cornerAngle_eq_angle (T : Tri) (j : Fin 3) :
    cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))
      = angle (T.edgeVec j) (T.edgeVec' j) := by
  rw [cornerAngle, EuclideanGeometry.angle, Tri.edgeVec, Tri.edgeVec']
  simp [vsub_eq_sub]

theorem Tri.volume_inter_ball_vertex (T : Tri) (j : Fin 3) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      volume (T.carrier ∩ Metric.ball (T.pts j) r')
        = ENNReal.ofReal
            (cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) / 2 * r' ^ 2) := by
  obtain ⟨r, hr, hEq⟩ := T.inter_ball_eq_vertexCone j
  refine ⟨r, hr, fun r' hr' hle => ?_⟩
  rw [inter_ball_mono hEq hle]
  set u := T.edgeVec j with hudef
  set v := T.edgeVec' j with hvdef
  have hu0 : u ≠ 0 := T.edgeVec_ne_zero j
  have hv0 : v ≠ 0 := T.edgeVec'_ne_zero j
  have hun : (0:ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
  have hvn : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
  have hsupos : 0 < ‖u‖⁻¹ := inv_pos.mpr hun
  have hsvpos : 0 < ‖v‖⁻¹ := inv_pos.mpr hvn
  have hunorm : ‖‖u‖⁻¹ • u‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsupos, inv_mul_cancel₀ hun.ne']
  have hvnorm : ‖‖v‖⁻¹ • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsvpos, inv_mul_cancel₀ hvn.ne']
  have hcone : vertexCone u v = vertexCone (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) :=
    (vertexCone_smul u v hsupos hsvpos).symm
  have hangle : angle (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) = angle u v := by
    rw [angle_smul_left_of_pos _ _ hsupos, angle_smul_right_of_pos _ _ hsvpos]
  have hcross : cross (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) ≠ 0 := by
    rw [cross_smul_left, cross_smul_right, T.cross_edgeVec j]
    have hd := T.det_ne_zero
    positivity
  have htrans : (fun z : Plane => T.pts j + z) ⁻¹'
      ({y : Plane | y - T.pts j ∈ vertexCone u v} ∩ Metric.ball (T.pts j) r')
      = vertexCone u v ∩ Metric.ball (0 : Plane) r' := by
    ext z
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, Metric.mem_ball]
    rw [add_sub_cancel_left, dist_eq_norm, add_sub_cancel_left, dist_zero_right]
  calc volume ({y : Plane | y - T.pts j ∈ vertexCone u v} ∩ Metric.ball (T.pts j) r')
      = volume ((fun z : Plane => T.pts j + z) ⁻¹'
          ({y : Plane | y - T.pts j ∈ vertexCone u v} ∩ Metric.ball (T.pts j) r')) := by
        rw [measure_preimage_add]
    _ = volume (vertexCone u v ∩ Metric.ball (0 : Plane) r') := by rw [htrans]
    _ = volume (vertexCone (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) ∩ Metric.ball (0 : Plane) r') := by
        rw [← hcone]
    _ = ENNReal.ofReal (angle (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) / 2 * r' ^ 2) :=
        volume_vertexCone_ball _ _ hunorm hvnorm hcross hr'
    _ = ENNReal.ofReal
          (cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) / 2 * r' ^ 2) := by
        rw [hangle, hudef, hvdef, ← T.cornerAngle_eq_angle j]

theorem volume_ball_plane (x : Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball x r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [EuclideanSpace.volume_ball]
  have hcard : Fintype.card (Fin 2) = 2 := by simp
  rw [hcard]
  have hg : Real.Gamma (1 + 1) = 1 := by
    have h := Real.Gamma_add_one (s := 1) one_ne_zero
    rw [Real.Gamma_one] at h
    simpa using h
  rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  push_cast
  rw [show (2 : ℝ) / 2 + 1 = 1 + 1 by norm_num, hg, Real.sq_sqrt Real.pi_pos.le]
  ring
end Erdos634.Geometry
end

section
-- AngleSumDissection

namespace Erdos634.Geometry
open MeasureTheory Set Metric
open scoped ENNReal

theorem Tri.volume_inter_ball_localAngle (T : Tri) (p : Plane) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      volume (T.carrier ∩ Metric.ball p r')
        = ENNReal.ofReal (T.localAngle p / 2 * r' ^ 2) := by
  classical
  by_cases hv : ∃ j, p = T.pts j
  · 
    obtain ⟨r, hr, h⟩ := T.volume_inter_ball_vertex hv.choose
    refine ⟨r, hr, fun r' h1 h2 => ?_⟩
    rw [Tri.localAngle, dif_pos hv]
    have hspec := hv.choose_spec
    set j0 := hv.choose with hj0
    rw [hspec]
    exact h r' h1 h2
  · push_neg at hv
    rcases T.classify hv with hpos | ⟨k, hk0, hkpos⟩ | ⟨k, hkneg⟩
    · 
      obtain ⟨r, hr, h⟩ := T.volume_inter_ball_interior hpos
      refine ⟨r, hr, fun r' h1 h2 => ?_⟩
      rw [Tri.localAngle, dif_neg (not_exists.mpr hv), if_pos hpos,
        h r' h1 h2, volume_ball_plane p h1.le]
      congr 1
      ring
    · 
      have hne : ∀ j : Fin 3, j + 1 ≠ j ∧ j + 2 ≠ j := by decide
      obtain ⟨r, hr, h⟩ := T.volume_inter_ball_edge k hk0
        (hkpos _ (hne k).1) (hkpos _ (hne k).2)
      refine ⟨r, hr, fun r' h1 h2 => ?_⟩
      have hIn : ¬ ∀ j, 0 < T.basis.coord j p := fun hI => absurd hk0 (ne_of_gt (hI k))
      rw [Tri.localAngle, dif_neg (not_exists.mpr hv), if_neg hIn,
        if_pos ⟨k, hk0, hkpos⟩]
      have h2v := h r' h1 h2
      rw [volume_ball_plane p h1.le] at h2v
      have hhalf : (2 : ℝ≥0∞) * ENNReal.ofReal (Real.pi / 2 * r' ^ 2)
          = ENNReal.ofReal (Real.pi * r' ^ 2) := by
        rw [show ((2 : ℝ≥0∞)) = ENNReal.ofReal (2 : ℝ) by simp,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        ring
      rw [← hhalf] at h2v
      exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp h2v
    · 
      obtain ⟨r, hr, h⟩ := T.volume_inter_ball_exterior hkneg
      refine ⟨r, hr, fun r' h1 h2 => ?_⟩
      have hIn : ¬ ∀ j, 0 < T.basis.coord j p := fun hI =>
        absurd (hI k) (not_lt.mpr hkneg.le)
      have hOn : ¬ ∃ m, T.basis.coord m p = 0 ∧ ∀ j, j ≠ m → 0 < T.basis.coord j p := by
        rintro ⟨m, hm, hrest⟩
        by_cases hmk : k = m
        · rw [hmk] at hkneg; exact absurd hm (ne_of_lt hkneg)
        · exact absurd (hrest k hmk) (not_lt.mpr hkneg.le)
      rw [Tri.localAngle, dif_neg (not_exists.mpr hv), if_neg hIn, if_neg hOn,
        h r' h1 h2]
      simp

theorem Tri.localAngle_interior (T : Tri) {p : Plane} (hp : p ∈ interior T.carrier) :
    T.localAngle p = 2 * Real.pi := by
  classical
  have hpos := T.interior_coord_pos hp
  have hv : ¬ ∃ j, p = T.pts j := by
    rintro ⟨j, rfl⟩
    have hne : ∀ m : Fin 3, m + 1 ≠ m := by decide
    have h0 : T.basis.coord (j + 1) (T.pts j) = 0 := T.basis.coord_apply_ne (hne j)
    exact absurd h0 (ne_of_gt (hpos (j + 1)))
  rw [Tri.localAngle, dif_neg hv, if_pos hpos]

theorem Tri.localAngle_frontier (T : Tri) {p : Plane} (hp : p ∈ frontier T.carrier)
    (hv : p ∉ Set.range T.pts) : T.localAngle p = Real.pi := by
  classical
  have hv' : ∀ k, p ≠ T.pts k := fun k h => hv ⟨k, h.symm⟩
  have hcar : p ∈ T.carrier := by
    have h1 : p ∈ closure T.carrier := frontier_subset_closure hp
    rwa [T.isCompact.isClosed.closure_eq] at h1
  have hnint : p ∉ interior T.carrier := fun h => hp.2 h
  rcases T.classify hv' with hpos | ⟨k, hk0, hkpos⟩ | ⟨k, hkneg⟩
  · exact absurd ((T.mem_interior_iff_coord_pos p).mpr hpos) hnint
  · have hIn : ¬ ∀ j, 0 < T.basis.coord j p := fun hI => absurd hk0 (ne_of_gt (hI k))
    rw [Tri.localAngle, dif_neg (not_exists.mpr hv'), if_neg hIn,
      if_pos ⟨k, hk0, hkpos⟩]
  · rw [T.carrier_eq_nonneg_coord] at hcar
    exact absurd (hcar k) (not_le.mpr hkneg)

theorem Dissection.volume_inter_ball_eq_sum {N : ℕ} (D : Dissection N) (x : Plane) (r : ℝ) :
    volume (D.target.carrier ∩ Metric.ball x r)
      = ∑ i, volume ((D.tile i).carrier ∩ Metric.ball x r) := by
  have h := measure_biUnion_finset₀ (μ := volume)
    (s := (Finset.univ : Finset (Fin N)))
    (f := fun i => (D.tile i).carrier ∩ Metric.ball x r)
    (fun i _ j _ hij => measure_mono_null
      (Set.inter_subset_inter Set.inter_subset_left Set.inter_subset_left) (D.aedisjoint hij))
    (fun i _ => ((D.tile i).nullMeasurableSet).inter
      Metric.isOpen_ball.measurableSet.nullMeasurableSet)
  have hU : (⋃ i ∈ (Finset.univ : Finset (Fin N)), ((D.tile i).carrier ∩ Metric.ball x r))
          = D.target.carrier ∩ Metric.ball x r := by
    simp only [Finset.mem_univ, Set.iUnion_true]
    rw [← Set.iUnion_inter, D.covers]
  rw [hU] at h
  exact h

theorem Dissection.sum_localAngle_eq {N : ℕ} (D : Dissection N) (p : Plane) :
    ∑ i, (D.tile i).localAngle p = D.target.localAngle p := by
  classical
  obtain ⟨rT, hrT, hT⟩ := D.target.volume_inter_ball_localAngle p
  choose ri hri hcontrib using fun i => (D.tile i).volume_inter_ball_localAngle p
  obtain ⟨r0, hr0, hr0le⟩ := exists_common_radius D.pos ri hri
  set r : ℝ := min rT r0 with hrdef
  have hrpos : 0 < r := lt_min hrT hr0
  have hsum := D.volume_inter_ball_eq_sum p r
  rw [hT r hrpos (min_le_left _ _)] at hsum
  have htiles : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      volume ((D.tile i).carrier ∩ Metric.ball p r)
        = ENNReal.ofReal ((D.tile i).localAngle p / 2 * r ^ 2) := fun i _ =>
    hcontrib i r hrpos ((min_le_right _ _).trans (hr0le i))
  rw [Finset.sum_congr rfl htiles,
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
      have := (D.tile i).localAngle_nonneg p
      positivity)] at hsum
  have hreal := (ENNReal.ofReal_eq_ofReal_iff
    (by have := D.target.localAngle_nonneg p; positivity)
    (Finset.sum_nonneg fun i _ => by
      have := (D.tile i).localAngle_nonneg p
      positivity)).mp hsum
  have hfact : ∑ i, (D.tile i).localAngle p / 2 * r ^ 2
      = (∑ i, (D.tile i).localAngle p) * (r ^ 2 / 2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfact] at hreal
  have hr2 : (0:ℝ) < r ^ 2 / 2 := by positivity
  have hkey : (∑ i, (D.tile i).localAngle p) * (r ^ 2 / 2)
      = D.target.localAngle p * (r ^ 2 / 2) := by
    rw [← hreal]; ring
  exact mul_right_cancel₀ hr2.ne' hkey
end Erdos634.Geometry
end

section
namespace Soifer
open Affine EuclideanGeometry Finset
open Erdos634.Geometry
open scoped Real EuclideanGeometry Similar Classical

abbrev asTile (S : Triangle ℝ Soifer.Plane) : Tri := ⟨S.points,S.independent⟩
abbrev nativeTile (S : Tri) : Triangle ℝ Soifer.Plane := ⟨S.pts,S.indep⟩

private theorem interior_bridge (S : Triangle ℝ Soifer.Plane) :
    interior (asTile S).carrier = S.interior := by
  ext x
  let B := (asTile S).basis
  have hs : ∑ i, B.coord i x = 1 := B.sum_coord_apply_eq_one x
  have hc : Finset.univ.affineCombination ℝ S.points (fun i => B.coord i x) = x := B.affineCombination_coord_eq_self x
  rw [(asTile S).mem_interior_iff_coord_pos x]
  change (∀ i, 0 < B.coord i x) ↔ x ∈ S.interior
  conv_rhs => rw [← hc, S.affineCombination_mem_interior_iff hs]
  refine ⟨fun h i => ⟨h i, ?_⟩, fun h i => (h i).1⟩
  rw [Fin.sum_univ_three] at hs
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  rcases (show ∀ t : Fin 3, t = 0 ∨ t = 1 ∨ t = 2 by decide) i with rfl | rfl | rfl <;> linarith

def ofCover {n : ℕ} (T : Triangle ℝ Soifer.Plane) (P : Fin n → Triangle ℝ Soifer.Plane)
    (hd : Pairwise fun i j => Disjoint (P i).interior (P j).interior)
    (hc : ⋃ i, (P i).closedInterior = T.closedInterior) : Dissection n where
  target := asTile T
  tile i := asTile (P i)
  covers := by simpa only [Tri.carrier,Affine.Simplex.convexHull_eq_closedInterior] using hc
  interiors_disjoint := by simpa only [interior_bridge] using hd

theorem loc_off_vertices (S : Tri) (p : Soifer.Plane) (hv : ¬ ∃ j, p = S.pts j) :
    S.localAngle p = 0 ∨ S.localAngle p = π ∨ S.localAngle p = 2 * π := by
  classical
  rw [Tri.localAngle, dif_neg hv]
  split <;> simp_all
  split <;> simp_all

def AngleAdditive {n : ℕ} (D : Dissection n) : Prop :=
  ∀ x, ∑ i, (D.tile i).localAngle x = D.target.localAngle x

/-- The angle identity at the corners of the target counts genuine tile vertices only. -/
theorem corner_partition {n : ℕ} (D : Dissection n) (hadd : AngleAdditive D) (s : Fin 3) :
    (∑ i, ∑ j, if D.target.pts s = (D.tile i).pts j then triAngle (nativeTile (D.tile i)) j else 0)
      = triAngle (nativeTile D.target) s := by
  classical
  let p := D.target.pts s
  have hsum := hadd p
  have ht : D.target.localAngle p = triAngle (nativeTile D.target) s := D.target.localAngle_vertex s
  rw [ht] at hsum
  rw [← hsum]
  apply sum_congr rfl
  intro i _
  change (∑ j, if p = (D.tile i).pts j then _ else 0) = _
  by_cases hv : ∃ j, p = (D.tile i).pts j
  · obtain ⟨v,hv⟩ := hv
    have iff (j : Fin 3) : p = (D.tile i).pts j ↔ j = v :=
      ⟨fun hj => (D.tile i).indep.injective (hj.symm.trans hv), fun h => h ▸ hv⟩
    simp only [iff, sum_ite_eq', mem_univ, if_true]
    rw [hv, (D.tile i).localAngle_vertex]
    rfl
  · have none : ∀ j, p ≠ (D.tile i).pts j := not_exists.mp hv
    simp only [none, if_false, sum_const_zero]
    have hle : (D.tile i).localAngle p ≤ triAngle (nativeTile D.target) s := by
      rw [← hsum]
      exact single_le_sum (fun j _ => (D.tile j).localAngle_nonneg p) (mem_univ i)
    have hlt := (triAngle_bounds (nativeTile D.target) s).2
    rcases loc_off_vertices (D.tile i) p hv with h | h | h
    · exact h.symm
    · linarith
    · linarith [Real.pi_pos]

/-- Geometric corner uniqueness for a dissection into at most five similar tiles. -/
theorem dissection_corners {n : ℕ} (hn : n ≤ 5) (D : Dissection n) (hadd : AngleAdditive D)
    (hsim : ∀ i j, (D.tile i).pts ∼ (D.tile j).pts)
    (hAB : 5 * triAngle (nativeTile D.target) 0 < triAngle (nativeTile D.target) 1)
    (hBC : 5 * triAngle (nativeTile D.target) 1 < triAngle (nativeTile D.target) 2) :
    (∃ e : Fin 3 ≃ Fin 3, ∀ s i, triAngle (nativeTile (D.tile i)) (e s) = triAngle (nativeTile D.target) s) ∧
      ∀ s, ∃! i : Fin n, ∃ j, D.target.pts s = (D.tile i).pts j := by
  classical
  let i₀ : Fin n := ⟨0,D.nonempty_idx⟩
  let w := triAngle (nativeTile (D.tile i₀))
  have hw (i j) : triAngle (nativeTile (D.tile i)) j = w j :=
    triAngle_eq_of_similar (S:=nativeTile (D.tile i)) (T:=nativeTile (D.tile i₀)) (hsim i i₀) j
  have hp (s : Fin 3) := corner_partition D hadd s
  simp_rw [hw] at hp
  obtain ⟨⟨e,he⟩,hu⟩ := corner_rows hn (triAngle (nativeTile D.target)) w
    (fun s i j => D.target.pts s = (D.tile i).pts j)
    (fun _ i _ _ h₁ h₂ => (D.tile i).indep.injective (h₁.symm.trans h₂))
    (triAngle_bounds _ _).1 hAB hBC (fun j => (triAngle_bounds _ j).1)
    ((sum_triAngle _).trans (sum_triAngle _).symm) hp
  exact ⟨⟨e,fun s i => (hw i (e s)).trans (he s)⟩,hu⟩
end Soifer
end

section
namespace Soifer
open Erdos634.Geometry Finset
open scoped Real Classical

theorem localAngle_le_full (T : Tri) (p : Plane) : T.localAngle p ≤ 2*π := by
  classical
  by_cases h : ∃ j, p = T.pts j
  · obtain ⟨j,rfl⟩ := h
    rw [T.localAngle_vertex]
    have h := EuclideanGeometry.angle_le_pi (T.pts (j+1)) (T.pts j) (T.pts (j+2))
    unfold cornerAngle
    linarith [Real.pi_pos]
  · rw [Tri.localAngle, dif_neg h]
    split <;> first | rfl | split <;> linarith [Real.pi_pos]

theorem localAngle_open_edge (T : Tri) (p : Plane) (m : Fin 3)
    (hz : T.basis.coord m p = 0) (hp : ∀ j, j ≠ m → 0 < T.basis.coord j p) : T.localAngle p = π := by
  classical
  have no : ¬∃ j, p = T.pts j := by
    rintro ⟨j,rfl⟩
    obtain ⟨k,hm,hj⟩ := (show ∀ a b : Fin 3, ∃ k : Fin 3, k ≠ a ∧ k ≠ b by decide) m j
    have h := hp k hm
    have he : T.basis.coord k (T.pts j) = 0 := T.basis.coord_apply_ne hj
    linarith
  have hi : ¬∀ j, 0 < T.basis.coord j p := fun h => (ne_of_gt (h m)) hz
  rw [Tri.localAngle, dif_neg no, if_neg hi, if_pos ⟨m,hz,hp⟩]

theorem vertex_midpoint_localAngle (T : Tri) {a b : Fin 3} (hab : a ≠ b) :
    T.localAngle (midpoint ℝ (T.pts a) (T.pts b)) = π := by
  have hc (j : Fin 3) : T.basis.coord j (midpoint ℝ (T.pts a) (T.pts b)) =
      ((if j = a then 1 else 0) + (if j = b then 1 else 0))/2 := by
    change T.basis.coord j (midpoint ℝ (T.basis a) (T.basis b)) = _
    rw [AffineMap.map_midpoint, midpoint_eq_smul_add, T.basis.coord_apply, T.basis.coord_apply]
    simp [smul_eq_mul,div_eq_inv_mul]
  obtain ⟨m,hma,hmb,hrest⟩ :=
    (show ∀ a b : Fin 3, a ≠ b → ∃ m : Fin 3, m ≠ a ∧ m ≠ b ∧ ∀ j : Fin 3, j ≠ m → j=a ∨ j=b by decide) a b hab
  apply localAngle_open_edge T _ m
  · simp [hc,hma,hmb]
  · intro j hj
    rcases hrest j hj with rfl | rfl <;> norm_num [hc,hab,Ne.symm hab]

theorem midpoint_localAngle_of_vertices (T : Tri) {p q : Plane} (hpq : p ≠ q)
    (hp : ∃ j, p = T.pts j) (hq : ∃ j, q = T.pts j) :
    T.localAngle (midpoint ℝ p q) = π := by
  obtain ⟨a,rfl⟩ := hp
  obtain ⟨b,rfl⟩ := hq
  exact vertex_midpoint_localAngle T (fun h => hpq (congrArg T.pts h))
end Soifer
end

section
namespace Soifer
open Erdos634.Geometry Finset
open scoped Real Classical

def onSide (T : Tri) (s : Fin 3) (p : Plane) : Prop := T.basis.coord s p = 0

theorem outer_on_side (T : Tri) (s v : Fin 3) : onSide T s (T.pts v) ↔ s ≠ v := by
  change T.basis.coord s (T.basis v) = 0 ↔ _
  rw [T.basis.coord_apply]
  by_cases h : s=v <;> simp [h]

theorem side_unique_outside_corners (T : Tri) {s t : Fin 3} {p : Plane}
    (hp : ¬∃ j, p=T.pts j) (hs : onSide T s p) (ht : onSide T t p) : s=t := by
  by_contra h
  exact hp (T.eq_vertex_of_two_coords_zero h hs ht)

theorem corner_is_tile_vertex {n : ℕ} (D : Dissection n) (hadd : AngleAdditive D) {i : Fin n}
    {v : Fin 3} (hmem : D.target.pts v ∈ (D.tile i).carrier) : ∃ j, D.target.pts v = (D.tile i).pts j := by
  by_contra no
  let p := D.target.pts v
  have hbound : (D.tile i).localAngle p < π := by
    have ht : D.target.localAngle p = triAngle (nativeTile D.target) v := D.target.localAngle_vertex v
    have hsum := hadd p
    have hle := single_le_sum (f := fun j => (D.tile j).localAngle p)
      (fun j _ => (D.tile j).localAngle_nonneg p) (mem_univ i)
    rw [hsum,ht] at hle
    exact hle.trans_lt (triAngle_bounds _ _).2
  rcases (D.tile i).classify (not_exists.mp no) with hpos | ⟨m,hz,hpos⟩ | ⟨m,hm⟩
  · have loc : (D.tile i).localAngle p = 2*π := by
      rw [Tri.localAngle, dif_neg no, if_pos hpos]
    linarith [Real.pi_pos]
  · have loc := localAngle_open_edge (D.tile i) p m hz hpos
    linarith
  · rw [(D.tile i).carrier_eq_nonneg_coord] at hmem
    exact (not_lt_of_ge (hmem m)) hm

theorem corner_side_vertex {n : ℕ} (D : Dissection n) (hadd : AngleAdditive D)
    (o : Fin 3 → Fin n) (unique : ∀ v i, (∃ j, D.target.pts v = (D.tile i).pts j) → i=o v)
    {v s : Fin 3} (hvs : v ≠ s) :
    ∃ j, (D.tile (o v)).pts j ≠ D.target.pts v ∧ onSide D.target s ((D.tile (o v)).pts j) := by
  classical
  let a := s+1
  have ham : a+2=s := (by decide : ∀ s : Fin 3, (s+1)+2=s) s
  have hends : v = a ∨ v = a+1 :=
    (by decide : ∀ s v : Fin 3, v ≠ s → v=s+1 ∨ v=(s+1)+1) s v hvs
  have mem : D.target.pts v ∈ D.target.edge a := by
    rcases hends with h | h
    · rw [h]; exact left_mem_segment ℝ _ _
    · rw [h]; exact right_mem_segment ℝ _ _
  obtain ⟨part, hp⟩ := hasEdgeChains_edge D a
  change D.target.pts v ∈ segment ℝ (D.target.pts a) (D.target.pts (a+1)) at mem
  rw [←hp] at mem
  obtain ⟨⟨i,k⟩, hik, hmem⟩ := Set.mem_iUnion₂.mp mem
  have hio : i=o v := unique v i (corner_is_tile_vertex D hadd ((D.tile i).edge_subset_carrier k hmem))
  subst i
  have subset : (D.tile (o v)).edge k ⊆ D.target.edge a := by
    intro p h
    change p ∈ segment ℝ (D.target.pts a) (D.target.pts (a+1))
    rw [←hp]
    exact Set.mem_iUnion₂.mpr ⟨(o v,k),hik,h⟩
  have sid {j : Fin 3} (hj : (D.tile (o v)).pts j ∈ (D.tile (o v)).edge k) : onSide D.target s ((D.tile (o v)).pts j) := by
    have h := D.target.coord_eq_zero_of_mem_edge a (subset hj)
    rwa [ham] at h
  by_cases hx : (D.tile (o v)).pts k = D.target.pts v
  · refine ⟨k+1, ?_,sid (right_mem_segment ℝ _ _)⟩
    rw [←hx]
    exact (D.tile (o v)).indep.injective.ne ((by decide : ∀ k : Fin 3, k+1 ≠ k) k)
  · exact ⟨k,hx,sid (left_mem_segment ℝ _ _)⟩

theorem side_midpoint_localAngle (T : Tri) {p q : Plane} {s : Fin 3}
    (hin : p ∈ T.carrier) (hqin : q ∈ T.carrier) (hp : ¬∃ j, p=T.pts j)
    (hsp : onSide T s p) (hsq : onSide T s q) : T.localAngle (midpoint ℝ p q) = π := by
  rw [T.carrier_eq_nonneg_coord] at hin hqin
  have midpoint_coord (j) : T.basis.coord j (midpoint ℝ p q) = (T.basis.coord j p + T.basis.coord j q)/2 := by
    rw [AffineMap.map_midpoint, midpoint_eq_smul_add]
    simp [smul_eq_mul,div_eq_inv_mul]
  apply localAngle_open_edge T _ s
  · simp [midpoint_coord,show T.basis.coord s p = 0 from hsp,show T.basis.coord s q = 0 from hsq]
  · intro j hj
    have hpos : 0 < T.basis.coord j p := lt_of_le_of_ne (hin j) fun h =>
      hj (side_unique_outside_corners T hp h.symm hsp)
    rw [midpoint_coord]
    linarith [hqin j]
end Soifer
end

section
namespace Soifer
open Finset
open scoped Classical

/-- Integer angle balance, with the flat and full-angle contributions from tiles at
whose vertex the given point does not lie. Each of the three labels occurs once. -/
theorem point_balance {n : ℕ} (hn : n ≤ 5) (V : Fin 3 → Fin n → Prop)
    (single : ∀ i a b, V a i → V b i → a = b) (hv : ∃ j i, V j i)
    (flat : Fin n → ℕ) (turns : ℕ)
    (hsum : ∑ i, ((if V 0 i then 1 else 0) + (if V 1 i then 6 else 0) +
      (if V 2 i then 173 else 0) + 180 * flat i) = 180 * turns) :
    ∀ j, (univ.filter (V j)).card = 1 := by
  classical
  let c (j : Fin 3) := (univ.filter (V j)).card
  have count (j : Fin 3) (a : ℕ) : (∑ i, if V j i then a else 0) = c j * a := by
    simp [c, ← sum_filter]
  have total : c 0 + c 1 + c 2 ≤ 5 := by
    calc
      _ = ∑ i, ((if V 0 i then 1 else 0) + (if V 1 i then 1 else 0) + (if V 2 i then 1 else 0)) := by
        simp only [sum_add_distrib, count, Nat.mul_one]
      _ ≤ ∑ _i : Fin n, (1 : ℕ) := by
        apply sum_le_sum
        intro i _
        have d01 : V 0 i → ¬V 1 i := fun a b => (by decide : (0 : Fin 3) ≠ 1) (single i _ _ a b)
        have d02 : V 0 i → ¬V 2 i := fun a b => (by decide : (0 : Fin 3) ≠ 2) (single i _ _ a b)
        have d12 : V 1 i → ¬V 2 i := fun a b => (by decide : (1 : Fin 3) ≠ 2) (single i _ _ a b)
        by_cases h₀ : V 0 i <;> by_cases h₁ : V 1 i <;> by_cases h₂ : V 2 i <;> simp_all
      _ ≤ 5 := by simpa using hn
  have hne : 0 < c 0 + c 1 + c 2 := by
    obtain ⟨j,i,h⟩ := hv
    have hc : 0 < c j := card_pos.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,h⟩⟩
    rcases ((show ∀ t : Fin 3, t = 0 ∨ t = 1 ∨ t = 2 by decide) j) with rfl | rfl | rfl <;> omega
  simp only [sum_add_distrib, count, Nat.mul_one, ← mul_sum] at hsum
  have eq : c 0 + 6 * c 1 + 173 * c 2 = 180 * (turns - ∑ i, flat i) := by omega
  obtain ⟨h0,h1,h2⟩ := Obstruction.vertex_balance _ _ _ _ total hne eq
  intro j
  fin_cases j <;> assumption
end Soifer
end

section
namespace Soifer
open Affine EuclideanGeometry Finset
open Erdos634.Geometry
open scoped Real Classical EuclideanGeometry Similar

def degrees : Fin 3 → ℕ := ![1,6,173]
@[simp] theorem degrees_zero : degrees 0 = 1 := rfl
@[simp] theorem degrees_one : degrees 1 = 6 := rfl
@[simp] theorem degrees_two : degrees 2 = 173 := rfl

def HasSoiferShape (T : Tri) : Prop :=
  ∀ j, triAngle (nativeTile T) j = (degrees j : ℝ) * (π/180)

theorem shape_corner_data {n : ℕ} (D : Dissection n) (hn : n ≤ 5) (hadd : AngleAdditive D)
    (hsim : ∀ i j, (D.tile i).pts ∼ (D.tile j).pts) (hs : HasSoiferShape D.target) :
    (∃ e : Fin 3 ≃ Fin 3, ∀ s i, triAngle (nativeTile (D.tile i)) (e s) = (degrees s : ℝ)*(π/180)) ∧
      ∀ s, ∃! i : Fin n, ∃ j, D.target.pts s = (D.tile i).pts j := by
  obtain ⟨⟨e,he⟩,hu⟩ := dissection_corners hn D hadd hsim
    (by rw [hs,hs]; norm_num <;> linarith [Real.pi_pos])
    (by rw [hs,hs]; norm_num <;> linarith [Real.pi_pos])
  exact ⟨⟨e,fun s i => (he s i).trans (hs s)⟩, hu⟩

/-- At a tile vertex distinct from the three target corners, precisely one tile
has each of the three corner types at that point. -/
theorem noncorner_counts {n : ℕ} (D : Dissection n) (hn : n ≤ 5) (hadd : AngleAdditive D)
    (e : Fin 3 ≃ Fin 3)
    (he : ∀ s i, triAngle (nativeTile (D.tile i)) (e s) = (degrees s : ℝ)*(π/180))
    {p : Soifer.Plane} (ht : ¬ ∃ j, p = D.target.pts j) (hv : ∃ i j, p = (D.tile i).pts j) :
    ∀ s, (univ.filter (fun i => p = (D.tile i).pts (e s))).card = 1 := by
  classical
  let V (j : Fin 3) (i : Fin n) := p = (D.tile i).pts (e j)
  letI (a : Fin 3) (i : Fin n) : Decidable (V a i) := Classical.propDecidable _
  have row (i : Fin n) : ∃ k : ℕ, (D.tile i).localAngle p =
      ((((if V 0 i then 1 else 0) + (if V 1 i then 6 else 0) + (if V 2 i then 173 else 0) + 180*k : ℕ) : ℝ) * (π/180)) := by
    by_cases h : ∃ j, V j i
    · obtain ⟨j,hj⟩ := h
      have hall (a) : V a i ↔ a = j :=
        ⟨fun ha => e.injective ((D.tile i).indep.injective (ha.symm.trans hj)), fun h => h ▸ hj⟩
      have ht := (D.tile i).localAngle_vertex (e j)
      change (D.tile i).localAngle ((D.tile i).pts (e j)) = triAngle (nativeTile (D.tile i)) (e j) at ht
      change p = (D.tile i).pts (e j) at hj
      rw [← hj, he] at ht
      refine ⟨0, ?_⟩
      rw [ht]
      rcases (show ∀ t : Fin 3, t = 0 ∨ t = 1 ∨ t = 2 by decide) j with rfl | rfl | rfl <;> norm_num [hall]
    · have none (j : Fin 3) : ¬ V j i := not_exists.mp h j
      have no : ¬∃ j, p = (D.tile i).pts j := by
        rintro ⟨j,hj⟩
        exact none (e.symm j) (by simpa [V] using hj)
      rcases loc_off_vertices (D.tile i) p no with h0 | h1 | h2
      · exact ⟨0,by simp [none,h0]⟩
      · exact ⟨1,by simp [none,h1] <;> ring⟩
      · exact ⟨2,by simp [none,h2] <;> ring⟩
  choose flat hflat using row
  have target : ∃ k : ℕ, D.target.localAngle p = ((180*k : ℕ):ℝ) * (π/180) := by
    rcases loc_off_vertices D.target p ht with h0 | h1 | h2
    · exact ⟨0,by simp [h0]⟩
    · exact ⟨1,by rw [h1]; norm_num <;> ring⟩
    · exact ⟨2,by rw [h2]; norm_num <;> ring⟩
  obtain ⟨k,hk⟩ := target
  have hsum := hadd p
  simp_rw [hflat] at hsum
  rw [← sum_mul,← Nat.cast_sum,hk] at hsum
  have hh := (mul_right_cancel₀ (by positivity : (π/180 : ℝ) ≠ 0)) hsum
  have hV : ∃ j i, V j i := by
    obtain ⟨i,j,hj⟩ := hv
    exact ⟨e.symm j,i,by simpa [V] using hj⟩
  have result := point_balance hn V (fun _ _ _ ha hb => e.injective ((D.tile _).indep.injective (ha.symm.trans hb))) hV flat k (by exact_mod_cast hh)
  intro j
  rw [← result j]
  congr 1
  ext i
  simp [V]

/-- A two-piece dissection would need a noncorner vertex with three distinct
incident tiles. -/
theorem no_two_of_angle_additive (D : Dissection 2) (hadd : AngleAdditive D)
    (hsim : ∀ i j, (D.tile i).pts ∼ (D.tile j).pts) (hs : HasSoiferShape D.target) : False := by
  classical
  obtain ⟨⟨e,he⟩,hu⟩ := shape_corner_data D (by decide) hadd hsim hs
  have all_outer (i : Fin 2) (j : Fin 3) : ∃ v, (D.tile i).pts j = D.target.pts v := by
    by_contra h
    have hc := noncorner_counts D (by decide) hadd e he h ⟨i,j,rfl⟩
    have every (s : Fin 3) : ∃ i', (D.tile i).pts j = (D.tile i').pts (e s) := by
      obtain ⟨t,ht⟩ := card_pos.mp (by rw [hc s]; decide)
      exact ⟨t,(mem_filter.mp ht).2⟩
    choose f hf using every
    have inj : Function.Injective f := by
      intro a b h
      have h1 := hf a
      rw [h] at h1
      exact e.injective ((D.tile _).indep.injective (h1.symm.trans (hf b)))
    have := Fintype.card_le_of_injective _ inj
    norm_num at this
  have each (i : Fin 2) : ∃ j, D.target.pts 0 = (D.tile i).pts j := by
    choose f hf using all_outer i
    have hinj : Function.Injective f := by
      intro a b hab
      apply (D.tile i).indep.injective
      rw [hf a,hf b,hab]
    obtain ⟨j,hj⟩ := (Finite.injective_iff_surjective.mp hinj) 0
    exact ⟨j,by rw [hf,hj]⟩
  exact (by decide : (0 : Fin 2) ≠ 1) ((hu 0).unique (each 0) (each 1))
end Soifer
end

section
namespace Soifer
open Erdos634.Geometry Finset
open scoped Real Classical Similar

theorem no_three_of_angle_additive (D : Dissection 3) (hadd : AngleAdditive D)
    (hsim : ∀ i j, (D.tile i).pts ∼ (D.tile j).pts) (hs : HasSoiferShape D.target) : False := by
  classical
  obtain ⟨⟨e,he⟩,hu⟩ := shape_corner_data D (by decide) hadd hsim hs
  have all_contain {p : Plane} (ht : ¬∃ j, p = D.target.pts j) (hv : ∃ i j, p = (D.tile i).pts j)
      (i : Fin 3) : ∃ j, p = (D.tile i).pts j := by
    have hc := noncorner_counts D (by decide) hadd e he ht hv
    have every (s : Fin 3) : ∃ t, p = (D.tile t).pts (e s) := by
      obtain ⟨t,ht⟩ := card_pos.mp (by rw [hc s]; decide)
      exact ⟨t,(mem_filter.mp ht).2⟩
    choose f hf using every
    have inj : Function.Injective f := by
      intro a b h
      have h1 := hf a
      rw [h] at h1
      exact e.injective ((D.tile _).indep.injective (h1.symm.trans (hf b)))
    obtain ⟨s,hs⟩ := (Finite.injective_iff_surjective.mp inj) i
    exact ⟨e s,hs ▸ hf s⟩
  choose owner owned uniq using hu
  obtain ⟨i,h0,h1⟩ := (show ∀ a b : Fin 3, ∃ c : Fin 3, c ≠ a ∧ c ≠ b by decide) (owner 0) (owner 1)
  have avoid (j : Fin 3) : (D.tile i).pts j ≠ D.target.pts 0 ∧ (D.tile i).pts j ≠ D.target.pts 1 :=
    ⟨fun h => h0 (uniq 0 i ⟨j,h.symm⟩),fun h => h1 (uniq 1 i ⟨j,h.symm⟩)⟩
  have onlyone : ∃ c : Fin 3, ∀ j, j ≠ c → (D.tile i).pts j ≠ D.target.pts 2 := by
    by_cases h : ∃ j, (D.tile i).pts j = D.target.pts 2
    · obtain ⟨c,hc⟩ := h
      exact ⟨c,fun j hj heq => hj ((D.tile i).indep.injective (heq.trans hc.symm))⟩
    · exact ⟨0,fun j _ => not_exists.mp h j⟩
  obtain ⟨c,hc⟩ := onlyone
  obtain ⟨a,b,hac,hbc,hab⟩ := (show ∀ c : Fin 3, ∃ a b : Fin 3, a ≠ c ∧ b ≠ c ∧ a ≠ b by decide) c
  have hnon {u : Fin 3} (hu : u ≠ c) : ¬∃ v, (D.tile i).pts u = D.target.pts v := by
    rintro ⟨v,hv⟩
    rcases (show ∀ v : Fin 3, v=0 ∨ v=1 ∨ v=2 by decide) v with rfl | rfl | rfl
    · exact (avoid u).1 hv
    · exact (avoid u).2 hv
    · exact hc u hu hv
  let p := (D.tile i).pts a
  let q := (D.tile i).pts b
  have hpq : p ≠ q := (D.tile i).indep.injective.ne hab
  have mid (t : Fin 3) : (D.tile t).localAngle (midpoint ℝ p q) = π :=
    midpoint_localAngle_of_vertices _ hpq (all_contain (hnon hac) ⟨i,a,rfl⟩ t)
      (all_contain (hnon hbc) ⟨i,b,rfl⟩ t)
  have sum := hadd (midpoint ℝ p q)
  rw [Fin.sum_univ_three,mid,mid,mid] at sum
  linarith [localAngle_le_full D.target (midpoint ℝ p q),Real.pi_pos]
end Soifer
end

section
namespace Soifer
open Erdos634.Geometry Finset
open scoped Classical

theorem three_labels (a b c : Fin 3) (hab : a≠b) (hac : a≠c) (hbc : b≠c) (t : Fin 3) :
    t=a ∨ t=b ∨ t=c :=
  (by decide : ∀ a b c : Fin 3, a≠b → a≠c → b≠c → ∀ t, t=a ∨ t=b ∨ t=c) a b c hab hac hbc t

theorem corner_frame {n : ℕ} (D : Dissection n) (hadd : AngleAdditive D) (o : Fin 3 → Fin n)
    (owns : ∀ v, ∃ k, D.target.pts v = (D.tile (o v)).pts k)
    (unique : ∀ v i, (∃ j, D.target.pts v = (D.tile i).pts j) → i=o v) (v : Fin 3) :
    ∃ f : Fin 3 ≃ Fin 3, (D.tile (o v)).pts (f v) = D.target.pts v ∧
      ∀ s, s≠v → (D.tile (o v)).pts (f s) ≠ D.target.pts v ∧ onSide D.target s ((D.tile (o v)).pts (f s)) := by
  classical
  obtain ⟨j,hj⟩ := owns v
  have side (s : Fin 3) (h : s≠v) := corner_side_vertex D hadd o unique h.symm
  let f (s : Fin 3) := if h : s=v then j else (side s h).choose
  have hv : (D.tile (o v)).pts (f v) = D.target.pts v := by simpa [f] using hj.symm
  have hs s (h : s≠v) : (D.tile (o v)).pts (f s) ≠ D.target.pts v ∧ onSide D.target s ((D.tile (o v)).pts (f s)) := by
    simpa [f,h] using (side s h).choose_spec
  have inj : Function.Injective f := by
    intro a b hab
    by_contra hne
    by_cases ha : a=v
    · subst a
      exact (hs b (Ne.symm hne)).1 ((congrArg (D.tile (o v)).pts hab).symm.trans hv)
    by_cases hb : b=v
    · subst b
      exact (hs a hne).1 ((congrArg (D.tile (o v)).pts hab).trans hv)
    have hsa := (hs a ha).2
    rw [hab] at hsa
    obtain ⟨w,hw⟩ := D.target.eq_vertex_of_two_coords_zero hne hsa (hs b hb).2
    have hsb := (hs b hb).2
    rw [hw] at hsa hsb
    have ha' := (outer_on_side _ _ _).mp hsa
    have hb' := (outer_on_side _ _ _).mp hsb
    rcases three_labels a b v hne ha hb w with h | h | h
    · exact ha' h.symm
    · exact hb' h.symm
    · exact (hs b hb).1 (hw.trans (congrArg D.target.pts h))
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp inj),hv,hs⟩

/-- A tile containing all three original vertices contains the whole triangle. -/
theorem not_all_outer (D : Dissection 5) (i : Fin 5) (h : ∀ s, ∃ j, D.target.pts s = (D.tile i).pts j) : False := by
  have hsub : D.target.carrier ⊆ (D.tile i).carrier := by
    apply convexHull_min _ (D.tile i).convex
    rintro _ ⟨s,rfl⟩
    obtain ⟨j,hj⟩ := h s
    rw [hj]
    exact subset_convexHull ℝ _ (Set.mem_range_self j)
  obtain ⟨j,hji⟩ := (by decide : ∀ i : Fin 5, ∃ j : Fin 5, j≠i) i
  obtain ⟨p,hp⟩ := (D.tile j).interior_nonempty
  exact Set.disjoint_left.mp (D.interiors_disjoint hji) hp
    (interior_mono ((tile_subset_target D j).trans hsub) hp)

/-- The three unsplit corners have different owners in a five-tile dissection. -/
theorem five_distinct_owners (D : Dissection 5) (o : Fin 3 → Fin 5)
    (owns : ∀ v, ∃ k, D.target.pts v = (D.tile (o v)).pts k)
    (f : Fin 3 → Fin 3 ≃ Fin 3)
    (atCorner : ∀ v, (D.tile (o v)).pts (f v v) = D.target.pts v)
    (onEdge : ∀ v s, s≠v → (D.tile (o v)).pts (f v s) ≠ D.target.pts v ∧ onSide D.target s ((D.tile (o v)).pts (f v s))) : Function.Injective o := by
  intro v w hsame
  by_contra hvw
  let j := f v w
  let p := (D.tile (o v)).pts j
  have hsp : onSide D.target w p := (onEdge v w (Ne.symm hvw)).2
  have hpv : p ≠ D.target.pts v := (onEdge v w (Ne.symm hvw)).1
  have hpw : p ≠ D.target.pts w := fun h => ((outer_on_side _ _ _).mp (h ▸ hsp)) rfl
  obtain ⟨s,hs⟩ := (f w).surjective j
  have he : (D.tile (o w)).pts (f w s) = p := by simp only [hs, ←hsame, p]
  have hsw : s ≠ w := by
    intro h
    subst s
    exact hpw (he.symm.trans (atCorner w))
  have hss := (onEdge w s hsw).2
  rw [he] at hss
  obtain ⟨u,hu⟩ := D.target.eq_vertex_of_two_coords_zero hsw hss hsp
  have huv : u ≠ v := fun h => hpv (hu.trans (congrArg D.target.pts h))
  have huw : u ≠ w := fun h => hpw (hu.trans (congrArg D.target.pts h))
  apply not_all_outer D (o v)
  intro k
  rcases three_labels u v w huv huw hvw k with h | h | h
  · rw [h]; exact ⟨j,hu.symm⟩
  · rw [h]; exact owns _
  · rw [h,hsame]; exact owns w

/-- A noncorner vertex of a corner tile is identified by its outer side. -/
theorem frame_incidence {n : ℕ} (D : Dissection n) {v : Fin 3} {i : Fin n}
    (f : Fin 3 ≃ Fin 3) (hv : (D.tile i).pts (f v) = D.target.pts v)
    (hs : ∀ s, s ≠ v → onSide D.target s ((D.tile i).pts (f s)))
    {p : Plane} (hp : ¬∃ t,p=D.target.pts t) (hi : ∃ j,p=(D.tile i).pts j) :
    ∃ s, s≠v ∧ onSide D.target s p ∧ p=(D.tile i).pts (f s) := by
  obtain ⟨j,hj⟩ := hi
  obtain ⟨s,rfl⟩ := f.surjective j
  have hn : s≠v := fun h => hp ⟨v, hj.trans ((congrArg (D.tile i).pts (congrArg f h)).trans hv)⟩
  exact ⟨s,hn,hj ▸ hs s hn,hj⟩
end Soifer
end

section
namespace Soifer
open Finset Erdos634.Geometry
open scoped Classical Real

theorem three_incident (D : Dissection 5) (hadd : AngleAdditive D) (e : Fin 3 ≃ Fin 3)
    (he : ∀ s i, triAngle (nativeTile (D.tile i)) (e s) = (degrees s : ℝ)*(π/180))
    {p : Plane} (ht : ¬∃ s,p=D.target.pts s) (hv : ∃ i j,p=(D.tile i).pts j) :
    ∃ f : Fin 3 → Fin 5, Function.Injective f ∧ ∀ s, ∃ j, p=(D.tile (f s)).pts j := by
  classical
  have counts := noncorner_counts D (by decide) hadd e he ht hv
  have every (s : Fin 3) : ∃ i, p=(D.tile i).pts (e s) := by
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (by rw [counts s]; decide)
    exact ⟨i,(Finset.mem_filter.mp hi).2⟩
  choose f hf using every
  refine ⟨f,?_, fun s => ⟨e s,hf s⟩⟩
  intro a b h
  have ha := hf a
  rw [h] at ha
  exact e.injective ((D.tile _).indep.injective (ha.symm.trans (hf b)))

set_option maxRecDepth 4000 in
private theorem remaining_slots : ∀ a b c : Fin 5, a≠b → a≠c → b≠c → ∃ l r : Fin 5,
    l≠r ∧ l≠a ∧ l≠b ∧ l≠c ∧ r≠a ∧ r≠b ∧ r≠c ∧ ∀ t, t=a ∨ t=b ∨ t=c ∨ t=l ∨ t=r := by decide

theorem remaining_pair (o : Fin 3 → Fin 5) (hinj : Function.Injective o) :
    ∃ l r : Fin 5, l≠r ∧ (∀ v, l ≠ o v) ∧ (∀ v, r ≠ o v) ∧ ∀ t, (∃ v, t=o v) ∨ t=l ∨ t=r := by
  obtain ⟨l,r,hlr,la,lb,lc,ra,rb,rc,hcover⟩ := remaining_slots (o 0) (o 1) (o 2)
    (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
  refine ⟨l,r,hlr,?_,?_,?_⟩
  · intro v; rcases (by decide : ∀ s : Fin 3, s=0 ∨ s=1 ∨ s=2) v with h | h | h <;> rw [h] <;> assumption
  · intro v; rcases (by decide : ∀ s : Fin 3, s=0 ∨ s=1 ∨ s=2) v with h | h | h <;> rw [h] <;> assumption
  · intro t
    rcases hcover t with h | h | h | h | h
    · exact Or.inl ⟨0,h⟩
    · exact Or.inl ⟨1,h⟩
    · exact Or.inl ⟨2,h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem cover_count (o : Fin 3 → Fin 5) {l r : Fin 5}
    (cover : ∀ t, (∃ v, t=o v) ∨ t=l ∨ t=r) (I : Fin 5 → Prop) [DecidablePred I]
    (degree : ∃ f : Fin 3 → Fin 5, Function.Injective f ∧ ∀ s, I (f s)) :
    3 ≤ (univ.filter (fun v => I (o v))).card + (if I l then 1 else 0) + (if I r then 1 else 0) := by
  classical
  obtain ⟨f,hf,hi⟩ := degree
  let C := (univ.filter (fun v => I (o v))).image o
  let L : Finset (Fin 5) := if I l then {l} else ∅
  let R : Finset (Fin 5) := if I r then {r} else ∅
  have hsub : univ.image f ⊆ C ∪ L ∪ R := by
    intro t ht
    obtain ⟨s,_,rfl⟩ := mem_image.mp ht
    rcases cover (f s) with ⟨v,hv⟩ | h | h
    · exact mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨v,mem_filter.mpr ⟨mem_univ _,hv ▸ hi s⟩,hv.symm⟩))
    · exact mem_union_left _ (mem_union_right _ (by simp [L,h ▸ hi s,h]))
    · exact mem_union_right _ (by simp [R,h ▸ hi s,h])
  have HC : C.card ≤ (univ.filter (fun v => I (o v))).card := card_image_le
  have HL : L.card = if I l then 1 else 0 := by by_cases h : I l <;> simp [L,h]
  have HR : R.card = if I r then 1 else 0 := by by_cases h : I r <;> simp [R,h]
  calc
    3 = (univ.image f).card := by rw [card_image_of_injective _ hf]; decide
    _ ≤ (C∪L∪R).card := card_le_card hsub
    _ ≤ (C∪L).card + R.card := card_union_le _ _
    _ ≤ C.card + L.card + R.card := Nat.add_le_add_right (card_union_le _ _) _
    _ ≤ _ := by rw [HL,HR]; omega
end Soifer
end

section
namespace Soifer

/-- In units of one degree, side and interior points have angle sums divisible
by 180. With at most five tile corners, the only nonempty possible collection
of the three angles 1, 6, 173 contains exactly one of each. -/
theorem vertex_multiplicities (a b c k : ℕ) (h : a + b + c ≤ 5)
    (hne : 0 < a + b + c) (hsum : a + 6*b + 173*c = 180*k) :
    a = 1 ∧ b = 1 ∧ c = 1 := by
  have hkc : k = c := by
    have ha : a ≤ 5 := by omega
    have hb : b ≤ 5 := by omega
    have hc : c ≤ 5 := by omega
    omega
  subst k
  have hbc : b = c := by omega
  omega

/-- At most five tiles can contribute positive corners. Counting straight
angles separately leaves the same divisibility condition. -/
theorem vertex_multiplicities_with_flat (a b c flat turns : ℕ)
    (h : a + b + c ≤ 5) (hne : 0 < a + b + c)
    (hsum : a + 6*b + 173*c + 180*flat = 180*turns) :
    a = 1 ∧ b = 1 ∧ c = 1 := by
  apply vertex_multiplicities a b c (turns-flat) h hne
  omega

/-- The final incidence obstruction for five tiles. Three tiles have one
outer corner each. The other two have vertex sets l and r. Each outer side
can contain at most two corner-tile vertex incidences away from its ends. -/
theorem five_tile_obstruction {P : Type*} [DecidableEq P]
    (l r : Finset P) (side : P → Fin 3) (corners : P → ℕ)
    (hl : l.card = 3) (hr : r.card = 3) (hd : l ≠ r)
    (deg : ∀ p ∈ l ∪ r, 3 ≤ corners p +
      (if p ∈ l then 1 else 0) + (if p ∈ r then 1 else 0))
    (bound : ∀ p ∈ l ∪ r, ∀ q ∈ l ∪ r, p ≠ q →
      side p = side q → corners p + corners q ≤ 2)
    (separate : ∀ p ∈ l ∩ r, ∀ q ∈ l ∩ r, p ≠ q → side p ≠ side q) : False := by
  have inj : Set.InjOn side (↑(l ∪ r) : Set P) := by
    intro p hp q hq hs
    by_contra hne
    have h := bound p hp q hq hne hs
    have dp := deg p hp
    have dq := deg q hq
    have both : p ∈ l ∧ p ∈ r ∧ q ∈ l ∧ q ∈ r := by
      by_cases hpl : p ∈ l <;> by_cases hpr : p ∈ r <;>
        by_cases hql : q ∈ l <;> by_cases hqr : q ∈ r <;>
        simp only [hpl,hpr,hql,hqr,if_true,if_false] at dp dq <;> simp [hpl,hpr,hql,hqr] <;> omega
    exact separate p (Finset.mem_inter.mpr ⟨both.1, both.2.1⟩) q
      (Finset.mem_inter.mpr both.2.2) hne hs
  have card : (l ∪ r).card ≤ 3 := by
    rw [← Finset.card_image_of_injOn inj]
    simpa using ((l ∪ r).image side).card_le_univ
  have el : l = l ∪ r := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
  have er : r = l ∪ r := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
  exact hd (el.trans er.symm)

end Soifer
end

section
namespace Soifer
open Erdos634.Geometry Finset
open scoped Real Classical Similar

theorem no_five_of_angle_additive (D : Dissection 5) (hadd : AngleAdditive D)
    (hsim : ∀ i j, (D.tile i).pts ∼ (D.tile j).pts) (hs : HasSoiferShape D.target) : False := by
  classical
  obtain ⟨⟨e,he⟩,hu⟩ := shape_corner_data D (by decide) hadd hsim hs
  choose o owns unique using hu
  choose f atCorner frame using corner_frame D hadd o owns unique
  have inj := five_distinct_owners D o owns f atCorner frame
  obtain ⟨l,r,hlr,hl,hr,cover⟩ := remaining_pair o inj
  let vertices (i : Fin 5) : Finset Plane := univ.image (D.tile i).pts
  have vmem (i : Fin 5) (p : Plane) : p ∈ vertices i ↔ ∃ j, p=(D.tile i).pts j := by
    simp only [vertices,mem_image,mem_univ,true_and]
    exact exists_congr fun j => eq_comm
  have card (i : Fin 5) : (vertices i).card = 3 := by
    rw [show vertices i = univ.image (D.tile i).pts from rfl,card_image_of_injective _ (D.tile i).indep.injective]
    decide
  have diff : vertices l ≠ vertices r := by
    intro h
    have sub : (D.tile l).carrier ⊆ (D.tile r).carrier := by
      apply convexHull_min _ (D.tile r).convex
      rintro _ ⟨j,rfl⟩
      have hp : (D.tile l).pts j ∈ vertices r := h ▸ (vmem _ _).mpr ⟨j,rfl⟩
      obtain ⟨k,hk⟩ := (vmem _ _).mp hp
      rw [hk]
      exact subset_convexHull ℝ _ (Set.mem_range_self k)
    obtain ⟨p,hp⟩ := (D.tile l).interior_nonempty
    exact Set.disjoint_left.mp (D.interiors_disjoint hlr) hp (interior_mono sub hp)
  let U := vertices l ∪ vertices r
  have nonouter {p : Plane} (h : p ∈ U) : ¬∃ s,p=D.target.pts s := by
    rintro ⟨s,rfl⟩
    rcases mem_union.mp h with ha | ha
    · exact hl s (unique s l ((vmem _ _).mp ha))
    · exact hr s (unique s r ((vmem _ _).mp ha))
  let C (p : Plane) := univ.filter (fun v => p ∈ vertices (o v))
  have degree (p : Plane) (hp : p ∈ U) :
      3 ≤ (C p).card + (if p ∈ vertices l then 1 else 0) + (if p ∈ vertices r then 1 else 0) := by
    have hv : ∃ i j,p=(D.tile i).pts j := by
      rcases mem_union.mp hp with a | a
      · exact ⟨l,(vmem _ _).mp a⟩
      · exact ⟨r,(vmem _ _).mp a⟩
    obtain ⟨g,hg,hv⟩ := three_incident D hadd e he (nonouter hp) hv
    exact cover_count o cover (fun t => p ∈ vertices t) ⟨g,hg,fun s => (vmem _ _).mpr (hv s)⟩
  have incident {p : Plane} (hp : p ∈ U) (v : Fin 3) (hv : v ∈ C p) :
      ∃ s, s≠v ∧ onSide D.target s p ∧ p=(D.tile (o v)).pts (f v s) :=
    frame_incidence D (f v) (atCorner v) (fun s h => (frame v s h).2) (nonouter hp)
      ((vmem _ _).mp (mem_filter.mp hv).2)
  have has_side (p : Plane) (hp : p ∈ U) : ∃ s,onSide D.target s p := by
    have positive : 0 < (C p).card := by
      have h := degree p hp
      split_ifs at h <;> omega
    obtain ⟨v,hv⟩ := card_pos.mp positive
    obtain ⟨s,_,h,_⟩ := incident hp v hv
    exact ⟨s,h⟩
  let side (p : Plane) : Fin 3 := if h : p ∈ U then (has_side p h).choose else 0
  have correct {p : Plane} (hp : p ∈ U) : onSide D.target (side p) p := by
    simpa [side,hp] using (has_side p hp).choose_spec
  have tag {p : Plane} (hp : p ∈ U) {v : Fin 3} (hv : v ∈ C p) :
      side p ≠ v ∧ p=(D.tile (o v)).pts (f v (side p)) := by
    obtain ⟨s,hn,hsp,eq⟩ := incident hp v hv
    have h := side_unique_outside_corners D.target (nonouter hp) (correct hp) hsp
    simpa only [h] using And.intro hn eq
  apply five_tile_obstruction (vertices l) (vertices r) side (fun p => (C p).card)
    (card l) (card r) diff degree
  · intro p hp q hq hpq hside
    have dis : Disjoint (C p) (C q) := by
      apply Finset.disjoint_left.mpr
      intro v vp vq
      have h := (tag hp vp).2
      rw [hside] at h
      exact hpq (h.trans (tag hq vq).2.symm)
    have sub : C p ∪ C q ⊆ univ.erase (side p) := by
      intro v hv
      apply mem_erase.mpr
      refine ⟨?_,mem_univ _⟩
      rcases mem_union.mp hv with a | a
      · exact Ne.symm (tag hp a).1
      · rw [hside]; exact Ne.symm (tag hq a).1
    rw [← card_union_of_disjoint dis]
    simpa using card_le_card sub
  · intro p hp q hq hpq hside
    obtain ⟨pl,pr⟩ := mem_inter.mp hp
    obtain ⟨ql,qr⟩ := mem_inter.mp hq
    have pU : p∈U := mem_union_left _ pl
    have qU : q∈U := mem_union_left _ ql
    have inside {x : Plane} (hx : x ∈ vertices l) : x ∈ D.target.carrier := by
      obtain ⟨j,rfl⟩ := (vmem _ _).mp hx
      exact tile_subset_target D l (subset_convexHull ℝ _ (Set.mem_range_self j))
    have hs := side_midpoint_localAngle D.target (inside pl) (inside ql) (nonouter pU) (correct pU)
      (show onSide D.target (side p) q by rw [hside]; exact correct qU)
    have ml := midpoint_localAngle_of_vertices (D.tile l) hpq ((vmem _ _).mp pl) ((vmem _ _).mp ql)
    have mr := midpoint_localAngle_of_vertices (D.tile r) hpq ((vmem _ _).mp pr) ((vmem _ _).mp qr)
    have le := sum_le_sum_of_subset_of_nonneg (f := fun i => (D.tile i).localAngle (midpoint ℝ p q))
      (show ({l,r} : Finset (Fin 5)) ⊆ univ from subset_univ _)
      (fun i _ _ => (D.tile i).localAngle_nonneg _)
    rw [sum_pair hlr,ml,mr,hadd,hs] at le
    linarith [Real.pi_pos]
end Soifer
end

section
/- The allowed-count construction below is the verified LeftToSolve proof by @TheWaler. -/
namespace Erdos633SimiliCuttableProof

open Affine
open scoped EuclideanGeometry Similar NNReal

private def vec3 (x y z : ℝ) : Fin 3 → ℝ
  | 0 => x
  | 1 => y
  | 2 => z

private lemma affineCombination_eq_imp (T : Triangle ℝ ℝ²) {w₁ w₂ : Fin 3 → ℝ}
    (hw₁ : ∑ i, w₁ i = 1) (hw₂ : ∑ i, w₂ i = 1)
    (h : Finset.univ.affineCombination ℝ T.points w₁ =
      Finset.univ.affineCombination ℝ T.points w₂) : w₁ = w₂ := by
  have hind := T.independent.indicator_eq_of_affineCombination_eq
    Finset.univ Finset.univ w₁ w₂ hw₁ hw₂ h
  simpa using hind

private noncomputable def homothetyMap (s : ℝ) (c : ℝ²) : ℝ² →ᵃ[ℝ] ℝ² where
  toFun x := s • x + c
  linear := s • LinearMap.id
  map_vadd' p v := by
    change s • (v + p) + c = s • v + (s • p + c)
    rw [smul_add, add_assoc]

private lemma homothetyMap_injective {s : ℝ} (hs : s ≠ 0) (c : ℝ²) :
    Function.Injective (homothetyMap s c) := by
  intro x y h
  change s • x + c = s • y + c at h
  exact smul_right_injective ℝ² hs (add_right_cancel h)

private noncomputable def subTri (T : Triangle ℝ ℝ²) (s : ℝ) (hs : s ≠ 0)
    (a : Fin 3 → ℝ) : Triangle ℝ ℝ² :=
  T.map (homothetyMap s (∑ i : Fin 3, a i • T.points i)) (homothetyMap_injective hs _)

private lemma subTri_similar (T : Triangle ℝ ℝ²) {s : ℝ} (hs : s ≠ 0) (a : Fin 3 → ℝ) :
    (subTri T s hs a).points ∼ T.points := by
  refine ⟨⟨|s|, abs_nonneg s⟩, ?_, fun i j => ?_⟩
  · intro h
    have h0 : |s| = 0 := congrArg NNReal.toReal h
    exact hs (abs_eq_zero.mp h0)
  · simp only [subTri, Simplex.map_points, Function.comp_apply, homothetyMap, AffineMap.coe_mk]
    rw [edist_dist, edist_dist]
    have hd : dist (s • T.points i + ∑ k : Fin 3, a k • T.points k)
        (s • T.points j + ∑ k : Fin 3, a k • T.points k) =
        |s| * dist (T.points i) (T.points j) := by
      rw [dist_add_right, dist_smul₀, Real.norm_eq_abs]
    rw [hd, ENNReal.ofReal_mul (abs_nonneg s), ENNReal.ofReal_eq_coe_nnreal (abs_nonneg s)]
    rfl

private lemma subTri_affineCombination (T : Triangle ℝ ℝ²) {s : ℝ} (hs : s ≠ 0)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {u : Fin 3 → ℝ} (hu : ∑ i, u i = 1) :
    Finset.univ.affineCombination ℝ (subTri T s hs a).points u =
      Finset.univ.affineCombination ℝ T.points (fun i => a i + s * u i) := by
  have hw : ∑ i : Fin 3, (a i + s * u i) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ha, hu]
    ring
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hu,
    Finset.affineCombination_eq_linear_combination _ _ _ hw]
  simp only [subTri, Simplex.map_points, Function.comp_apply, homothetyMap, AffineMap.coe_mk,
    smul_add, add_smul, Finset.sum_add_distrib]
  have hsmul : ∑ i : Fin 3, u i • ∑ k : Fin 3, a k • T.points k =
      (∑ i : Fin 3, u i) • ∑ k : Fin 3, a k • T.points k :=
    Finset.sum_smul.symm
  rw [hsmul, hu, one_smul, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, mul_comm]

private lemma mem_subTri_setInterior_iff (I : Set ℝ) (T : Triangle ℝ ℝ²)
    {s : ℝ} (hs : s ≠ 0) {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s hs a).setInterior I ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, (w i - a i) / s ∈ I) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  constructor
  · rintro ⟨u, hu, huI, rfl⟩
    refine ⟨fun i => a i + s * u i, ?_, ?_, (subTri_affineCombination T hs ha hu).symm⟩
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ha, hu]
      ring
    · intro i
      have hdiv : (a i + s * u i - a i) / s = u i := by
        field_simp [hs]
        ring
      rw [hdiv]
      exact huI i
  · rintro ⟨w, hw, hwI, rfl⟩
    let u : Fin 3 → ℝ := fun i => (w i - a i) / s
    have hu : ∑ i : Fin 3, u i = 1 := by
      simp only [u, ← Finset.sum_div, Finset.sum_sub_distrib, hw, ha]
      field_simp [hs]
      ring
    refine ⟨u, hu, hwI, ?_⟩
    rw [subTri_affineCombination T hs ha hu]
    congr 1
    funext i
    simp only [u]
    field_simp [hs]
    ring

private lemma mem_subTri_closedInterior_pos (T : Triangle ℝ ℝ²) {s : ℝ} (hs : 0 < s)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s (ne_of_gt hs) a).closedInterior ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, a i ≤ w i) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  change x ∈ (subTri T s (ne_of_gt hs) a).setInterior (Set.Icc 0 1) ↔ _
  rw [mem_subTri_setInterior_iff (Set.Icc 0 1) T (ne_of_gt hs) ha]
  refine exists_congr fun w => and_congr_right fun hw => and_congr_left fun _ => ?_
  constructor
  · intro h i
    have h0 : 0 ≤ (w i - a i) / s := (h i).1
    have h1 : 0 ≤ w i - a i := (div_nonneg_iff.mp h0).elim (fun h' => h'.1) (fun h' => by linarith)
    linarith
  · intro h i
    have hsum : (w 0 - a 0) + (w 1 - a 1) + (w 2 - a 2) = s := by
      rw [Fin.sum_univ_three] at hw ha
      linarith
    have h0 : 0 ≤ w 0 - a 0 := sub_nonneg.mpr (h 0)
    have h1 : 0 ≤ w 1 - a 1 := sub_nonneg.mpr (h 1)
    have h2 : 0 ≤ w 2 - a 2 := sub_nonneg.mpr (h 2)
    have hle : w i - a i ≤ s := match i with
      | 0 => by linarith
      | 1 => by linarith
      | 2 => by linarith
    exact ⟨div_nonneg (sub_nonneg.mpr (h i)) (le_of_lt hs), (div_le_one hs).mpr hle⟩

private lemma mem_subTri_interior_pos (T : Triangle ℝ ℝ²) {s : ℝ} (hs : 0 < s)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s (ne_of_gt hs) a).interior ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, a i < w i) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  change x ∈ (subTri T s (ne_of_gt hs) a).setInterior (Set.Ioo 0 1) ↔ _
  rw [mem_subTri_setInterior_iff (Set.Ioo 0 1) T (ne_of_gt hs) ha]
  refine exists_congr fun w => and_congr_right fun hw => and_congr_left fun _ => ?_
  constructor
  · intro h i
    have h0 : 0 < (w i - a i) / s := (h i).1
    have h1 : 0 < w i - a i := (div_pos_iff.mp h0).elim (fun h' => h'.1) (fun h' => by linarith)
    linarith
  · intro h i
    have hsum : (w 0 - a 0) + (w 1 - a 1) + (w 2 - a 2) = s := by
      rw [Fin.sum_univ_three] at hw ha
      linarith
    have h0 : 0 < w 0 - a 0 := sub_pos.mpr (h 0)
    have h1 : 0 < w 1 - a 1 := sub_pos.mpr (h 1)
    have h2 : 0 < w 2 - a 2 := sub_pos.mpr (h 2)
    have hlt : w i - a i < s := match i with
      | 0 => by linarith
      | 1 => by linarith
      | 2 => by linarith
    exact ⟨div_pos (sub_pos.mpr (h i)) hs, (div_lt_one hs).mpr hlt⟩

private lemma mem_subTri_closedInterior_neg (T : Triangle ℝ ℝ²) {s : ℝ} (hs : s < 0)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s (ne_of_lt hs) a).closedInterior ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, w i ≤ a i) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  change x ∈ (subTri T s (ne_of_lt hs) a).setInterior (Set.Icc 0 1) ↔ _
  rw [mem_subTri_setInterior_iff (Set.Icc 0 1) T (ne_of_lt hs) ha]
  refine exists_congr fun w => and_congr_right fun hw => and_congr_left fun _ => ?_
  have ht : 0 < -s := neg_pos.mpr hs
  constructor
  · intro h i
    have h0 : 0 ≤ (a i - w i) / (-s) := by
      have : (a i - w i) / (-s) = (w i - a i) / s := by field_simp [ne_of_lt hs]; ring
      rw [this]
      exact (h i).1
    have h1 : 0 ≤ a i - w i := (div_nonneg_iff.mp h0).elim (fun h' => h'.1) (fun h' => by linarith)
    linarith
  · intro h i
    have hsum : (a 0 - w 0) + (a 1 - w 1) + (a 2 - w 2) = -s := by
      rw [Fin.sum_univ_three] at hw ha
      linarith
    have h0 : 0 ≤ a 0 - w 0 := sub_nonneg.mpr (h 0)
    have h1 : 0 ≤ a 1 - w 1 := sub_nonneg.mpr (h 1)
    have h2 : 0 ≤ a 2 - w 2 := sub_nonneg.mpr (h 2)
    have hle : a i - w i ≤ -s := match i with
      | 0 => by linarith
      | 1 => by linarith
      | 2 => by linarith
    have heq : (w i - a i) / s = (a i - w i) / (-s) := by field_simp [ne_of_lt hs]; ring
    rw [heq]
    exact ⟨div_nonneg (sub_nonneg.mpr (h i)) (le_of_lt ht), (div_le_one ht).mpr hle⟩

private lemma mem_subTri_interior_neg (T : Triangle ℝ ℝ²) {s : ℝ} (hs : s < 0)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s (ne_of_lt hs) a).interior ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, w i < a i) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  change x ∈ (subTri T s (ne_of_lt hs) a).setInterior (Set.Ioo 0 1) ↔ _
  rw [mem_subTri_setInterior_iff (Set.Ioo 0 1) T (ne_of_lt hs) ha]
  refine exists_congr fun w => and_congr_right fun hw => and_congr_left fun _ => ?_
  have ht : 0 < -s := neg_pos.mpr hs
  constructor
  · intro h i
    have h0 : 0 < (a i - w i) / (-s) := by
      have : (a i - w i) / (-s) = (w i - a i) / s := by field_simp [ne_of_lt hs]; ring
      rw [this]
      exact (h i).1
    have h1 : 0 < a i - w i := (div_pos_iff.mp h0).elim (fun h' => h'.1) (fun h' => by linarith)
    linarith
  · intro h i
    have hsum : (a 0 - w 0) + (a 1 - w 1) + (a 2 - w 2) = -s := by
      rw [Fin.sum_univ_three] at hw ha
      linarith
    have h0 : 0 < a 0 - w 0 := sub_pos.mpr (h 0)
    have h1 : 0 < a 1 - w 1 := sub_pos.mpr (h 1)
    have h2 : 0 < a 2 - w 2 := sub_pos.mpr (h 2)
    have hlt : a i - w i < -s := match i with
      | 0 => by linarith
      | 1 => by linarith
      | 2 => by linarith
    have heq : (w i - a i) / s = (a i - w i) / (-s) := by field_simp [ne_of_lt hs]; ring
    rw [heq]
    exact ⟨div_pos (sub_pos.mpr (h i)) ht, (div_lt_one ht).mpr hlt⟩

private lemma mem_closedInterior_of_nonneg (T : Triangle ℝ ℝ²) {w : Fin 3 → ℝ}
    (hw : ∑ i, w i = 1) (hnn : ∀ i, 0 ≤ w i) :
    Finset.univ.affineCombination ℝ T.points w ∈ T.closedInterior := by
  rw [T.affineCombination_mem_closedInterior_iff hw]
  intro i
  rw [Fin.sum_univ_three] at hw
  have h0 := hnn 0
  have h1 := hnn 1
  have h2 := hnn 2
  refine ⟨hnn i, ?_⟩
  match i with
  | 0 => linarith
  | 1 => linarith
  | 2 => linarith

private lemma mem_interior_of_pos (T : Triangle ℝ ℝ²) {w : Fin 3 → ℝ}
    (hw : ∑ i, w i = 1) (hpos : ∀ i, 0 < w i) :
    Finset.univ.affineCombination ℝ T.points w ∈ T.interior := by
  rw [T.affineCombination_mem_interior_iff hw]
  intro i
  rw [Fin.sum_univ_three] at hw
  have h0 := hpos 0
  have h1 := hpos 1
  have h2 := hpos 2
  refine ⟨hpos i, ?_⟩
  match i with
  | 0 => linarith
  | 1 => linarith
  | 2 => linarith

private def StrongSimiliCuttable (n : ℕ) (T : Triangle ℝ ℝ²) : Prop :=
  ∃ Ts : Fin n → Triangle ℝ ℝ²,
    (∀ i, (Ts i).points ∼ T.points) ∧
    (∀ i, (Ts i).interior ⊆ T.interior) ∧
    Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) ∧
    ⋃ i, (Ts i).closedInterior = T.closedInterior

private lemma StrongSimiliCuttable.toIsSimiliCuttable {n : ℕ} {T : Triangle ℝ ℝ²}
    (h : StrongSimiliCuttable n T) : Erdos633.IsSimiliCuttable n T := by
  rcases h with ⟨Ts, hsim, -, hdisj, hunion⟩
  exact ⟨Ts, fun i j => (hsim i).trans (hsim j).symm, hdisj, hunion⟩

private lemma strongSimiliCuttable_one (T : Triangle ℝ ℝ²) : StrongSimiliCuttable 1 T := by
  refine ⟨fun _ => T, fun _ => Similar.refl _, fun _ => Set.Subset.rfl, ?_, ?_⟩
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  · ext x
    simp

private lemma strongSimiliCuttable_two_mul (m : ℕ) (hm : 2 ≤ m) (T : Triangle ℝ ℝ²) :
    StrongSimiliCuttable (2 * m) T := by
  let mr : ℝ := (m : ℝ)
  have hmr_pos : 0 < mr := by
    dsimp only [mr]
    exact_mod_cast (by omega : 0 < m)
  have hmr_ge2 : (2 : ℝ) ≤ mr := by
    dsimp only [mr]
    exact_mod_cast hm
  have hs_big_pos : 0 < (mr - 1) / mr := div_pos (by linarith) hmr_pos
  have hs_up_pos : 0 < 1 / mr := div_pos one_pos hmr_pos
  have hs_inv_neg : -1 / mr < 0 := div_neg_of_neg_of_pos (by norm_num) hmr_pos
  let aBig : Fin 3 → ℝ := vec3 (1 / mr) 0 0
  have haBig : ∑ i : Fin 3, aBig i = 1 - (mr - 1) / mr := by
    rw [Fin.sum_univ_three]
    change 1 / mr + 0 + 0 = 1 - (mr - 1) / mr
    field_simp [ne_of_gt hmr_pos]
    ring
  let aUp (j : Fin m) : Fin 3 → ℝ := vec3 0 ((j.1 : ℝ) / mr) ((mr - 1 - (j.1 : ℝ)) / mr)
  have haUp (j : Fin m) : ∑ i : Fin 3, aUp j i = 1 - 1 / mr := by
    rw [Fin.sum_univ_three]
    change 0 + (j.1 : ℝ) / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 - 1 / mr
    field_simp [ne_of_gt hmr_pos]
    ring
  let aInv (j : Fin (m - 1)) : Fin 3 → ℝ :=
    vec3 (1 / mr) (((j.1 : ℝ) + 1) / mr) ((mr - 1 - (j.1 : ℝ)) / mr)
  have haInv (j : Fin (m - 1)) : ∑ i : Fin 3, aInv j i = 1 - (-1 / mr) := by
    rw [Fin.sum_univ_three]
    change 1 / mr + ((j.1 : ℝ) + 1) / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 - (-1 / mr)
    field_simp [ne_of_gt hmr_pos]
    ring
  let idx := Unit ⊕ Fin m ⊕ Fin (m - 1)
  let tile : idx → Triangle ℝ ℝ²
    | Sum.inl () => subTri T ((mr - 1) / mr) (ne_of_gt hs_big_pos) aBig
    | Sum.inr (Sum.inl j) => subTri T (1 / mr) (ne_of_gt hs_up_pos) (aUp j)
    | Sum.inr (Sum.inr j) => subTri T (-1 / mr) (ne_of_lt hs_inv_neg) (aInv j)
  have hcard : Fintype.card idx = 2 * m := by
    dsimp only [idx]
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Fintype.card_fin]
    omega
  let e : Fin (2 * m) ≃ idx := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => tile (e i), ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    generalize e i = p
    rcases p with ⟨⟩ | j | j
    · exact subTri_similar T (ne_of_gt hs_big_pos) aBig
    · exact subTri_similar T (ne_of_gt hs_up_pos) (aUp j)
    · exact subTri_similar T (ne_of_lt hs_inv_neg) (aInv j)
  · intro i x hx
    dsimp only at hx
    generalize e i = p at hx
    rcases p with ⟨⟩ | j | j
    · rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx
      rcases hx with ⟨w, hw, hlt, rfl⟩
      refine mem_interior_of_pos T hw fun k => ?_
      have hk := hlt k
      match k with
      | 0 =>
        change 1 / mr < w 0 at hk
        linarith [div_pos one_pos hmr_pos]
      | 1 => exact hk
      | 2 => exact hk
    · rw [mem_subTri_interior_pos T hs_up_pos (haUp j)] at hx
      rcases hx with ⟨w, hw, hlt, rfl⟩
      have hj_le : (j.1 : ℝ) ≤ mr - 1 := by
        have h1 : j.1 + 1 ≤ m := j.2
        have h2 : (j.1 : ℝ) + 1 ≤ mr := by dsimp only [mr]; exact_mod_cast h1
        linarith
      refine mem_interior_of_pos T hw fun k => ?_
      have hk := hlt k
      match k with
      | 0 => exact hk
      | 1 =>
        change (j.1 : ℝ) / mr < w 1 at hk
        have hnn : (0 : ℝ) ≤ (j.1 : ℝ) / mr := div_nonneg (Nat.cast_nonneg _) (le_of_lt hmr_pos)
        linarith
      | 2 =>
        change (mr - 1 - (j.1 : ℝ)) / mr < w 2 at hk
        have hnn : (0 : ℝ) ≤ (mr - 1 - (j.1 : ℝ)) / mr :=
          div_nonneg (by linarith) (le_of_lt hmr_pos)
        linarith
    · rw [mem_subTri_interior_neg T hs_inv_neg (haInv j)] at hx
      rcases hx with ⟨w, hw, hlt, rfl⟩
      have hj_le : (j.1 : ℝ) + 2 ≤ mr := by
        have h1 : j.1 + 2 ≤ m := by omega
        dsimp only [mr]
        exact_mod_cast h1
      rw [Fin.sum_univ_three] at hw
      have h0 : w 0 < 1 / mr := hlt 0
      have h1 : w 1 < ((j.1 : ℝ) + 1) / mr := hlt 1
      have h2 : w 2 < (mr - 1 - (j.1 : ℝ)) / mr := hlt 2
      have hsum12 : ((j.1 : ℝ) + 1) / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 := by
        field_simp [ne_of_gt hmr_pos]; ring
      have hsum02 : 1 / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 - (j.1 : ℝ) / mr := by
        field_simp [ne_of_gt hmr_pos]; ring
      have hsum01 : 1 / mr + ((j.1 : ℝ) + 1) / mr = 1 - (mr - 2 - (j.1 : ℝ)) / mr := by
        field_simp [ne_of_gt hmr_pos]; ring
      have hnn1 : (0 : ℝ) ≤ (j.1 : ℝ) / mr := div_nonneg (Nat.cast_nonneg _) (le_of_lt hmr_pos)
      have hnn2 : (0 : ℝ) ≤ (mr - 2 - (j.1 : ℝ)) / mr :=
        div_nonneg (by linarith) (le_of_lt hmr_pos)
      refine mem_interior_of_pos T (by rw [Fin.sum_univ_three]; exact hw) fun k => ?_
      match k with
      | 0 => linarith
      | 1 => linarith
      | 2 => linarith
  · intro i₁ i₂ hne
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    have he_ne : e i₁ ≠ e i₂ := fun h => hne (e.injective h)
    have hdisj_idx : ∀ p₁ p₂ : idx, p₁ ≠ p₂ →
        x ∈ (tile p₁).interior → x ∈ (tile p₂).interior → False := by
      intro p₁ p₂ hp hx1 hx2
      rcases p₁ with ⟨⟩ | j₁ | j₁ <;> rcases p₂ with ⟨⟩ | j₂ | j₂
      · exact hp rfl
      · rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx1
        rw [mem_subTri_interior_pos T hs_up_pos (haUp j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        rw [Fin.sum_univ_three] at hw₁
        have hb0 : 1 / mr < w₁ 0 := h1 0
        have hu1 : (j₂.1 : ℝ) / mr < w₁ 1 := h2 1
        have hu2 : (mr - 1 - (j₂.1 : ℝ)) / mr < w₁ 2 := h2 2
        have hsum : 1 / mr + (j₂.1 : ℝ) / mr + (mr - 1 - (j₂.1 : ℝ)) / mr = 1 := by
          field_simp [ne_of_gt hmr_pos]; ring
        linarith
      · rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx1
        rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        have hb0 : 1 / mr < w₁ 0 := h1 0
        have hi0 : w₁ 0 < 1 / mr := h2 0
        linarith
      · rw [mem_subTri_interior_pos T hs_up_pos (haUp j₁)] at hx1
        rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        rw [Fin.sum_univ_three] at hw₁
        have hb0 : 1 / mr < w₁ 0 := h2 0
        have hu1 : (j₁.1 : ℝ) / mr < w₁ 1 := h1 1
        have hu2 : (mr - 1 - (j₁.1 : ℝ)) / mr < w₁ 2 := h1 2
        have hsum : 1 / mr + (j₁.1 : ℝ) / mr + (mr - 1 - (j₁.1 : ℝ)) / mr = 1 := by
          field_simp [ne_of_gt hmr_pos]; ring
        linarith
      · rw [mem_subTri_interior_pos T hs_up_pos (haUp j₁)] at hx1
        rw [mem_subTri_interior_pos T hs_up_pos (haUp j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        rw [Fin.sum_univ_three] at hw₁
        have hjne : j₁.1 ≠ j₂.1 := fun h => hp (by rw [Fin.ext h])
        have h0_1 : 0 < w₁ 0 := h1 0
        have h1_1 : (j₁.1 : ℝ) / mr < w₁ 1 := h1 1
        have h2_1 : (mr - 1 - (j₁.1 : ℝ)) / mr < w₁ 2 := h1 2
        have h1_2 : (j₂.1 : ℝ) / mr < w₁ 1 := h2 1
        have h2_2 : (mr - 1 - (j₂.1 : ℝ)) / mr < w₁ 2 := h2 2
        rcases lt_or_gt_of_ne hjne with hlt | hgt
        · have hle : (j₁.1 : ℝ) + 1 ≤ (j₂.1 : ℝ) := by exact_mod_cast hlt
          have hdiv : ((j₁.1 : ℝ) + 1) / mr ≤ (j₂.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle (le_of_lt hmr_pos)
          have hsum : ((j₁.1 : ℝ) + 1) / mr + (mr - 1 - (j₁.1 : ℝ)) / mr = 1 := by
            field_simp [ne_of_gt hmr_pos]; ring
          linarith
        · have hle : (j₂.1 : ℝ) + 1 ≤ (j₁.1 : ℝ) := by exact_mod_cast hgt
          have hdiv : ((j₂.1 : ℝ) + 1) / mr ≤ (j₁.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle (le_of_lt hmr_pos)
          have hsum : ((j₂.1 : ℝ) + 1) / mr + (mr - 1 - (j₂.1 : ℝ)) / mr = 1 := by
            field_simp [ne_of_gt hmr_pos]; ring
          linarith
      · rw [mem_subTri_interior_pos T hs_up_pos (haUp j₁)] at hx1
        rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        have hu1 : (j₁.1 : ℝ) / mr < w₁ 1 := h1 1
        have hu2 : (mr - 1 - (j₁.1 : ℝ)) / mr < w₁ 2 := h1 2
        have hi1 : w₁ 1 < ((j₂.1 : ℝ) + 1) / mr := h2 1
        have hi2 : w₁ 2 < (mr - 1 - (j₂.1 : ℝ)) / mr := h2 2
        rcases le_or_gt j₁.1 j₂.1 with hle | hgt
        · have hle' : (j₁.1 : ℝ) ≤ (j₂.1 : ℝ) := by exact_mod_cast hle
          have hdiv : (mr - 1 - (j₂.1 : ℝ)) / mr ≤ (mr - 1 - (j₁.1 : ℝ)) / mr :=
            div_le_div_of_nonneg_right (by linarith) (le_of_lt hmr_pos)
          linarith
        · have hle' : (j₂.1 : ℝ) + 1 ≤ (j₁.1 : ℝ) := by exact_mod_cast hgt
          have hdiv : ((j₂.1 : ℝ) + 1) / mr ≤ (j₁.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle' (le_of_lt hmr_pos)
          linarith
      · rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₁)] at hx1
        rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        have hi0 : w₁ 0 < 1 / mr := h1 0
        have hb0 : 1 / mr < w₁ 0 := h2 0
        linarith
      · rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₁)] at hx1
        rw [mem_subTri_interior_pos T hs_up_pos (haUp j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        have hi1 : w₁ 1 < ((j₁.1 : ℝ) + 1) / mr := h1 1
        have hi2 : w₁ 2 < (mr - 1 - (j₁.1 : ℝ)) / mr := h1 2
        have hu1 : (j₂.1 : ℝ) / mr < w₁ 1 := h2 1
        have hu2 : (mr - 1 - (j₂.1 : ℝ)) / mr < w₁ 2 := h2 2
        rcases le_or_gt j₂.1 j₁.1 with hle | hgt
        · have hle' : (j₂.1 : ℝ) ≤ (j₁.1 : ℝ) := by exact_mod_cast hle
          have hdiv : (mr - 1 - (j₁.1 : ℝ)) / mr ≤ (mr - 1 - (j₂.1 : ℝ)) / mr :=
            div_le_div_of_nonneg_right (by linarith) (le_of_lt hmr_pos)
          linarith
        · have hle' : (j₁.1 : ℝ) + 1 ≤ (j₂.1 : ℝ) := by exact_mod_cast hgt
          have hdiv : ((j₁.1 : ℝ) + 1) / mr ≤ (j₂.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle' (le_of_lt hmr_pos)
          linarith
      · rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₁)] at hx1
        rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        rw [Fin.sum_univ_three] at hw₁
        have hjne : j₁.1 ≠ j₂.1 := fun h => hp (by rw [Fin.ext h])
        have h0_1 : w₁ 0 < 1 / mr := h1 0
        have h1_1 : w₁ 1 < ((j₁.1 : ℝ) + 1) / mr := h1 1
        have h2_1 : w₁ 2 < (mr - 1 - (j₁.1 : ℝ)) / mr := h1 2
        have h1_2 : w₁ 1 < ((j₂.1 : ℝ) + 1) / mr := h2 1
        have h2_2 : w₁ 2 < (mr - 1 - (j₂.1 : ℝ)) / mr := h2 2
        rcases lt_or_gt_of_ne hjne with hlt | hgt
        · have hle : (j₁.1 : ℝ) + 1 ≤ (j₂.1 : ℝ) := by exact_mod_cast hlt
          have hdiv : ((j₁.1 : ℝ) + 1) / mr ≤ (j₂.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle (le_of_lt hmr_pos)
          have hsum : 1 / mr + (j₂.1 : ℝ) / mr + (mr - 1 - (j₂.1 : ℝ)) / mr = 1 := by
            field_simp [ne_of_gt hmr_pos]; ring
          linarith
        · have hle : (j₂.1 : ℝ) + 1 ≤ (j₁.1 : ℝ) := by exact_mod_cast hgt
          have hdiv : ((j₂.1 : ℝ) + 1) / mr ≤ (j₁.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle (le_of_lt hmr_pos)
          have hsum : 1 / mr + (j₁.1 : ℝ) / mr + (mr - 1 - (j₁.1 : ℝ)) / mr = 1 := by
            field_simp [ne_of_gt hmr_pos]; ring
          linarith
    exact hdisj_idx (e i₁) (e i₂) he_ne hx₁ hx₂
  · ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hx⟩
      generalize e i = p at hx
      rcases p with ⟨⟩ | j | j
      · rw [mem_subTri_closedInterior_pos T hs_big_pos haBig] at hx
        rcases hx with ⟨w, hw, hle, rfl⟩
        refine mem_closedInterior_of_nonneg T hw fun k => ?_
        have hk := hle k
        match k with
        | 0 =>
          change 1 / mr ≤ w 0 at hk
          linarith [div_pos one_pos hmr_pos]
        | 1 => exact hk
        | 2 => exact hk
      · rw [mem_subTri_closedInterior_pos T hs_up_pos (haUp j)] at hx
        rcases hx with ⟨w, hw, hle, rfl⟩
        have hj_le : (j.1 : ℝ) ≤ mr - 1 := by
          have h1 : j.1 + 1 ≤ m := j.2
          have h2 : (j.1 : ℝ) + 1 ≤ mr := by dsimp only [mr]; exact_mod_cast h1
          linarith
        refine mem_closedInterior_of_nonneg T hw fun k => ?_
        have hk := hle k
        match k with
        | 0 => exact hk
        | 1 =>
          change (j.1 : ℝ) / mr ≤ w 1 at hk
          have hnn : (0 : ℝ) ≤ (j.1 : ℝ) / mr := div_nonneg (Nat.cast_nonneg _) (le_of_lt hmr_pos)
          linarith
        | 2 =>
          change (mr - 1 - (j.1 : ℝ)) / mr ≤ w 2 at hk
          have hnn : (0 : ℝ) ≤ (mr - 1 - (j.1 : ℝ)) / mr :=
            div_nonneg (by linarith) (le_of_lt hmr_pos)
          linarith
      · rw [mem_subTri_closedInterior_neg T hs_inv_neg (haInv j)] at hx
        rcases hx with ⟨w, hw, hle, rfl⟩
        have hj_le : (j.1 : ℝ) + 2 ≤ mr := by
          have h1 : j.1 + 2 ≤ m := by omega
          dsimp only [mr]
          exact_mod_cast h1
        rw [Fin.sum_univ_three] at hw
        have h0 : w 0 ≤ 1 / mr := hle 0
        have h1 : w 1 ≤ ((j.1 : ℝ) + 1) / mr := hle 1
        have h2 : w 2 ≤ (mr - 1 - (j.1 : ℝ)) / mr := hle 2
        have hsum12 : ((j.1 : ℝ) + 1) / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 := by
          field_simp [ne_of_gt hmr_pos]; ring
        have hsum02 : 1 / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 - (j.1 : ℝ) / mr := by
          field_simp [ne_of_gt hmr_pos]; ring
        have hsum01 : 1 / mr + ((j.1 : ℝ) + 1) / mr = 1 - (mr - 2 - (j.1 : ℝ)) / mr := by
          field_simp [ne_of_gt hmr_pos]; ring
        have hnn1 : (0 : ℝ) ≤ (j.1 : ℝ) / mr := div_nonneg (Nat.cast_nonneg _) (le_of_lt hmr_pos)
        have hnn2 : (0 : ℝ) ≤ (mr - 2 - (j.1 : ℝ)) / mr :=
          div_nonneg (by linarith) (le_of_lt hmr_pos)
        refine mem_closedInterior_of_nonneg T (by rw [Fin.sum_univ_three]; exact hw) fun k => ?_
        match k with
        | 0 => linarith
        | 1 => linarith
        | 2 => linarith
    · rintro ⟨w, hw, hwI, rfl⟩
      have hw0 : 0 ≤ w 0 := (hwI 0).1
      have hw1 : 0 ≤ w 1 := (hwI 1).1
      have hw2 : 0 ≤ w 2 := (hwI 2).1
      have hw1_le : w 1 ≤ 1 := (hwI 1).2
      have hcover : ∃ p : idx, Finset.univ.affineCombination ℝ T.points w ∈ (tile p).closedInterior := by
        by_cases hbig : 1 / mr ≤ w 0
        · refine ⟨Sum.inl (), ?_⟩
          rw [mem_subTri_closedInterior_pos T hs_big_pos haBig]
          refine ⟨w, hw, fun k => ?_, rfl⟩
          match k with
          | 0 => exact hbig
          | 1 => exact hw1
          | 2 => exact hw2
        · push Not at hbig
          by_cases hw1_eq : w 1 = 1
          · let jlast : Fin m := ⟨m - 1, by omega⟩
            refine ⟨Sum.inr (Sum.inl jlast), ?_⟩
            rw [mem_subTri_closedInterior_pos T hs_up_pos (haUp jlast)]
            have hjlast : (jlast.1 : ℝ) = mr - 1 := by
              dsimp only [jlast, mr]
              rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
            refine ⟨w, hw, fun k => ?_, rfl⟩
            match k with
            | 0 => exact hw0
            | 1 =>
              change (jlast.1 : ℝ) / mr ≤ w 1
              rw [hjlast, hw1_eq]
              exact (div_le_one hmr_pos).mpr (by linarith)
            | 2 =>
              change (mr - 1 - (jlast.1 : ℝ)) / mr ≤ w 2
              rw [hjlast]
              have hzero : (mr - 1 - (mr - 1)) / mr = 0 := by ring
              rw [hzero]
              exact hw2
          · have hw1_lt : w 1 < 1 := lt_of_le_of_ne hw1_le hw1_eq
            let jnat : ℕ := Nat.floor (mr * w 1)
            have hjnat_lt : jnat < m := by
              have hlt : mr * w 1 < mr := by nlinarith
              have hlt' : mr * w 1 < (m : ℝ) := hlt
              exact (Nat.floor_lt (mul_nonneg (le_of_lt hmr_pos) hw1)).mpr hlt'
            have hjnat_le : (jnat : ℝ) ≤ mr * w 1 :=
              Nat.floor_le (mul_nonneg (le_of_lt hmr_pos) hw1)
            have hjnat_gt : mr * w 1 < (jnat : ℝ) + 1 := Nat.lt_floor_add_one (mr * w 1)
            have hw1_lo : (jnat : ℝ) / mr ≤ w 1 := (div_le_iff₀ hmr_pos).mpr (by linarith)
            have hw1_hi : w 1 ≤ ((jnat : ℝ) + 1) / mr := (le_div_iff₀ hmr_pos).mpr (by linarith)
            by_cases hup : (mr - 1 - (jnat : ℝ)) / mr ≤ w 2
            · refine ⟨Sum.inr (Sum.inl ⟨jnat, hjnat_lt⟩), ?_⟩
              rw [mem_subTri_closedInterior_pos T hs_up_pos (haUp ⟨jnat, hjnat_lt⟩)]
              refine ⟨w, hw, fun k => ?_, rfl⟩
              match k with
              | 0 => exact hw0
              | 1 => exact hw1_lo
              | 2 => exact hup
            · push Not at hup
              have hjnat_lt' : jnat < m - 1 := by
                by_contra hge
                have hjeq : jnat = m - 1 := by omega
                have hjr : (jnat : ℝ) = mr - 1 := by
                  rw [hjeq, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
                rw [hjr] at hup
                have hzero : (mr - 1 - (mr - 1)) / mr = 0 := by ring
                linarith
              refine ⟨Sum.inr (Sum.inr ⟨jnat, hjnat_lt'⟩), ?_⟩
              rw [mem_subTri_closedInterior_neg T hs_inv_neg (haInv ⟨jnat, hjnat_lt'⟩)]
              refine ⟨w, hw, fun k => ?_, rfl⟩
              match k with
              | 0 => exact le_of_lt hbig
              | 1 => exact hw1_hi
              | 2 => exact le_of_lt hup
      rcases hcover with ⟨p, hp⟩
      exact ⟨e.symm p, by simpa using hp⟩

private lemma strongSimiliCuttable_add_three {n : ℕ} (hn : 1 ≤ n) {T : Triangle ℝ ℝ²}
    (h : StrongSimiliCuttable n T) : StrongSimiliCuttable (n + 3) T := by
  rcases h with ⟨Ts, hsim, hint, hdisj, hunion⟩
  let i0 : Fin n := ⟨0, by omega⟩
  obtain ⟨Us, hUsim, hUint, hUdisj, hUunion⟩ := strongSimiliCuttable_two_mul 2 (le_refl 2) (Ts i0)
  let idx := Fin 4 ⊕ Fin (n - 1)
  let tile : idx → Triangle ℝ ℝ²
    | Sum.inl k => Us k
    | Sum.inr j => Ts ⟨j.1 + 1, by omega⟩
  have hcard : Fintype.card idx = n + 3 := by
    dsimp only [idx]
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    omega
  let e : Fin (n + 3) ≃ idx := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => tile (e i), ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    generalize e i = p
    rcases p with k | j
    · exact (hUsim k).trans (hsim i0)
    · exact hsim ⟨j.1 + 1, by omega⟩
  · intro i
    dsimp only
    generalize e i = p
    rcases p with k | j
    · exact (hUint k).trans (hint i0)
    · exact hint ⟨j.1 + 1, by omega⟩
  · intro i₁ i₂ hne
    dsimp only
    have he_ne : e i₁ ≠ e i₂ := fun h => hne (e.injective h)
    generalize e i₁ = p₁ at he_ne ⊢
    generalize e i₂ = p₂ at he_ne ⊢
    rcases p₁ with k₁ | j₁ <;> rcases p₂ with k₂ | j₂
    · have hk : k₁ ≠ k₂ := fun h => he_ne (by rw [h])
      exact hUdisj hk
    · have hne' : i0 ≠ ⟨j₂.1 + 1, by omega⟩ := by
        intro heq
        have : (0 : ℕ) = j₂.1 + 1 := congrArg Fin.val heq
        omega
      exact (hdisj hne').mono_left (hUint k₁)
    · have hne' : (⟨j₁.1 + 1, by omega⟩ : Fin n) ≠ i0 := by
        intro heq
        have : j₁.1 + 1 = 0 := congrArg Fin.val heq
        omega
      exact (hdisj hne').mono_right (hUint k₂)
    · have hj : (⟨j₁.1 + 1, by omega⟩ : Fin n) ≠ ⟨j₂.1 + 1, by omega⟩ := by
        intro heq
        have hval : j₁.1 = j₂.1 := by
          have : j₁.1 + 1 = j₂.1 + 1 := congrArg Fin.val heq
          omega
        exact he_ne (by rw [Fin.ext hval])
      exact hdisj hj
  · rw [← hunion]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hx⟩
      generalize e i = p at hx
      rcases p with k | j
      · refine ⟨i0, ?_⟩
        rw [← hUunion]
        exact Set.mem_iUnion.mpr ⟨k, hx⟩
      · exact ⟨⟨j.1 + 1, by omega⟩, hx⟩
    · rintro ⟨j, hx⟩
      by_cases hj : j.1 = 0
      · have hjeq : j = i0 := Fin.ext hj
        rw [hjeq, ← hUunion] at hx
        rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
        exact ⟨e.symm (Sum.inl k), by simpa [tile] using hk⟩
      · let j' : Fin (n - 1) := ⟨j.1 - 1, by omega⟩
        have hjeq : (⟨j'.1 + 1, by omega⟩ : Fin n) = j := Fin.ext (by dsimp [j']; omega)
        refine ⟨e.symm (Sum.inr j'), ?_⟩
        simpa [tile, hjeq] using hx

end Erdos633SimiliCuttableProof

open scoped EuclideanGeometry in
theorem Soifer.allowed : ∀ {n : ℕ} {T : Affine.Triangle ℝ ℝ²}, n ≠ 0 → n ≠ 2 → n ≠ 3 → n ≠ 5 → Erdos633.IsSimiliCuttable n T := by
  intro n T hn₀ hn₂ hn₃ hn₅
  by_cases hn1 : n = 1
  · subst hn1
    exact (Erdos633SimiliCuttableProof.strongSimiliCuttable_one T).toIsSimiliCuttable
  · by_cases heven : n % 2 = 0
    · have hm : 2 ≤ n / 2 := by omega
      have heq : 2 * (n / 2) = n := by omega
      rw [← heq]
      exact (Erdos633SimiliCuttableProof.strongSimiliCuttable_two_mul (n / 2) hm T).toIsSimiliCuttable
    · have hge7 : 7 ≤ n := by omega
      have hsub_even : (n - 3) % 2 = 0 := by omega
      have hm : 2 ≤ (n - 3) / 2 := by omega
      have heq1 : 2 * ((n - 3) / 2) = n - 3 := by omega
      have heq2 : (n - 3) + 3 = n := by omega
      have hbase : Erdos633SimiliCuttableProof.StrongSimiliCuttable (n - 3) T := by
        rw [← heq1]
        exact Erdos633SimiliCuttableProof.strongSimiliCuttable_two_mul ((n - 3) / 2) hm T
      rw [← heq2]
      exact (Erdos633SimiliCuttableProof.strongSimiliCuttable_add_three (by omega) hbase).toIsSimiliCuttable

end

section
namespace Soifer
open Affine EuclideanGeometry Erdos634.Geometry
open scoped Real EuclideanGeometry Similar

theorem exceptional_witness : ∃ T : Triangle ℝ Soifer.Plane,
    ¬Erdos633.IsSimiliCuttable 2 T ∧ ¬Erdos633.IsSimiliCuttable 3 T ∧ ¬Erdos633.IsSimiliCuttable 5 T := by
  obtain ⟨T,h0,h1,h2⟩ := exists_witness
  have shape : HasSoiferShape (asTile T) := by
    intro s
    rcases (by decide : ∀ j : Fin 3, j=0 ∨ j=1 ∨ j=2) s with h | h | h
    · subst s
      change ∠ (T.points 1) (T.points 0) (T.points 2) = (degrees 0 : ℝ)*(π/180)
      rw [h0,degrees_zero]; norm_num
    · subst s
      change ∠ (T.points 2) (T.points 1) (T.points 0) = (degrees 1 : ℝ)*(π/180)
      rw [angle_comm,h1,degrees_one]; push_cast; ring
    · subst s
      change ∠ (T.points 0) (T.points 2) (T.points 1) = (degrees 2 : ℝ)*(π/180)
      rw [h2,degrees_two]; push_cast; ring
  have lift {n : ℕ} (bad : ∀ D : Dissection n, AngleAdditive D →
        (∀ i j, (D.tile i).pts ∼ (D.tile j).pts) → HasSoiferShape D.target → False) :
      ¬ Erdos633.IsSimiliCuttable n T := by
    rintro ⟨P,hs,hd,hc⟩
    let D := ofCover T P hd hc
    exact bad D D.sum_localAngle_eq hs shape
  exact ⟨T,lift no_two_of_angle_additive,lift no_three_of_angle_additive,lift no_five_of_angle_additive⟩
end Soifer
end

theorem OMA.solution : type_of% @Erdos633.exists_isSimiliCuttable_iff_ne_zero_two_three_five := by
  obtain ⟨T,h₂,h₃,h₅⟩ := Soifer.exceptional_witness
  refine ⟨T,fun n => ⟨fun h => ⟨h.ne_zero, ?_, ?_, ?_⟩, ?_⟩⟩
  · rintro rfl; exact h₂ h
  · rintro rfl; exact h₃ h
  · rintro rfl; exact h₅ h
  · rintro ⟨h₀,h₂,h₃,h₅⟩
    exact Soifer.allowed h₀ h₂ h₃ h₅
