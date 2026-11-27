import OMAReductions.R_Erdos757_erdos_757_variants_lowerBound_R1
import Mathlib.Algebra.Ring.Rat
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
Freiman transfer: a finite set of reals is the image of an additive map into the integers,
injective on differences. The map is a rational linear form on a Hamel basis, scaled to clear
denominators. The argument is the standard one; the write-up here is independent.
-/

open scoped Pointwise
open Module

namespace Erdos757Transfer

lemma exists_dual_eq_one {V : Type*} [AddCommGroup V] [Module ℚ V] {v : V} (hv : v ≠ 0) :
    ∃ f : Dual ℚ V, f v = 1 := by
  classical
  have hli : LinearIndepOn ℚ (fun _ : Unit => v) Set.univ := by
    rw [linearIndepOn_univ_iff]
    exact (linearIndependent_unique_iff (R := ℚ) (v := fun _ : Unit => v)).2 hv
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_eq_one hli
  exact ⟨f, hf () ⟨⟩⟩

/-- A rational linear form that avoids zero on a finite set of nonzero vectors. -/
lemma exists_dual_ne_zero_on {V : Type*} [AddCommGroup V] [Module ℚ V] (s : Finset V)
    (hs : ∀ x ∈ s, x ≠ 0) : ∃ f : Dual ℚ V, ∀ x ∈ s, f x ≠ 0 := by
  classical
  induction s using Finset.induction with
  | empty =>
    exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨f, hf⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
    have ha0 : a ≠ 0 := hs a (Finset.mem_insert_self a s)
    obtain ⟨g, hg⟩ := exists_dual_eq_one (V := V) ha0
    let bad : Finset ℚ :=
      insert (-(f a)) ((s.filter fun x => g x ≠ 0).image fun x => -(f x) / g x)
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (insert (0 : ℚ) bad)
    have hc0 : c ≠ 0 := fun h => hc (by simp [h])
    have hcbad : c ∉ bad := fun h => hc (by simp [h])
    refine ⟨f + c • g, ?_⟩
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with hxa | hx
    · subst hxa
      rw [LinearMap.add_apply, LinearMap.smul_apply, hg, smul_eq_mul, mul_one]
      intro hzero
      apply hcbad
      have hcneg : c = -(f x) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hzero
      rw [hcneg]
      exact Finset.mem_insert_self _ _
    · rw [LinearMap.add_apply, LinearMap.smul_apply]
      by_cases hgx : g x = 0
      · simpa [hgx] using hf x hx
      · intro hsum
        apply hcbad
        refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hgx⟩, ?_⟩)
        have hsum' : c * g x = -(f x) := by
          rw [← sub_eq_zero]
          linear_combination hsum
        exact (eq_div_of_mul_eq hgx hsum').symm

/-- Clear denominators of a finite set of rationals. -/
lemma exists_clear_denoms (s : Finset ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ q ∈ s, ∃ z : ℤ, (N : ℚ) * q = z := by
  classical
  refine ⟨∏ q ∈ s, q.den, ?_, ?_⟩
  · rw [Nat.pos_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun q _ => q.den_ne_zero
  · intro q hq
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun q : ℚ => q.den) hq
    refine ⟨q.num * k, ?_⟩
    calc
      ((∏ r ∈ s, r.den : ℕ) : ℚ) * q = ((q.den * k : ℕ) : ℚ) * q := by rw [hk]
      _ = (q.den : ℚ) * (k : ℚ) * q := by push_cast; ring
      _ = (k : ℚ) * (q.den * q) := by ring
      _ = (k : ℚ) * q.num := by rw [Rat.den_mul_eq_num]
      _ = (q.num * k : ℤ) := by push_cast; ring

end Erdos757Transfer

theorem OMA.solution : OMA.R_Erdos757_erdos_757_variants_lowerBound_R1.H2 := by
  intro A hA
  classical
  have hdiff : ((A - A) - (A - A)).Finite := (hA.sub hA).sub (hA.sub hA)
  let D : Finset ℝ := hdiff.toFinset.erase 0
  have hD : ∀ x ∈ D, x ≠ 0 := fun x hx => (Finset.mem_erase.mp hx).1
  obtain ⟨φ, hφ⟩ := Erdos757Transfer.exists_dual_ne_zero_on D hD
  obtain ⟨N, hN, hclear⟩ :=
    Erdos757Transfer.exists_clear_denoms (hA.toFinset.image fun a => φ a)
  let scale : ℝ → ℚ := fun x => (N : ℚ) * φ x
  let f : ℝ →+ ℝ :=
    { toFun := fun x => (scale x : ℝ)
      map_zero' := by simp [scale]
      map_add' := fun x y => by
        simp only [scale, map_add, mul_add, Rat.cast_add] }
  refine ⟨f, ?_, ?_⟩
  · intro x hx y hy hfeq
    have hqe : scale x = scale y := Rat.cast_injective hfeq
    have hφeq : φ x = φ y := by
      simpa [scale] using mul_left_cancel₀ (by exact_mod_cast hN.ne') hqe
    by_contra hne
    have hd : x - y ∈ D := by
      rw [Finset.mem_erase, Set.Finite.mem_toFinset]
      refine ⟨sub_ne_zero.mpr hne, ?_⟩
      exact ⟨x, hx, y, hy, rfl⟩
    have hnz : φ (x - y) ≠ 0 := hφ _ hd
    rw [map_sub, hφeq, sub_self] at hnz
    exact hnz rfl
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨z, hz⟩ := hclear (φ a)
      (Finset.mem_image.mpr ⟨a, hA.mem_toFinset.mpr ha, rfl⟩)
    refine ⟨z, ?_⟩
    have hscale : scale a = (z : ℚ) := by simpa [scale] using hz
    rw [show f a = (scale a : ℝ) from rfl, hscale]
    exact (Rat.cast_intCast z).symm
