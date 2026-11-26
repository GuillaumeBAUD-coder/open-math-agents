import FormalConjectures.ErdosProblems.«494»
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! Multiplying every element by a nontrivial cube root of unity preserves triple products. -/

open Erdos494

theorem OMA.solution : type_of% @Erdos494.erdos_494.variants.product := by
  classical
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
  have hω : IsPrimitiveRoot ω 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
  have hpow : ω ^ 3 = 1 := hω.pow_eq_one
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h] at hpow
    norm_num at hpow
  let e : ℂ ↪ ℂ := ⟨fun z => ω * z, fun _ _ h => mul_left_cancel₀ hω0 h⟩
  let A : Finset ℂ := {1, 2, 3, 4}
  let B := A.map e
  have hA0 : (0 : ℂ) ∉ A := by norm_num [A]
  refine ⟨A, B, by norm_num [A, Finset.card_insert_of_notMem], by simp [B], hA0, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨a, ha, he⟩ := Finset.mem_map.mp h
    change ω * a = 0 at he
    exact hA0 ((mul_eq_zero.mp he).resolve_left hω0 ▸ ha)
  · unfold prodMultiset
    rw [show B = A.map e from rfl, Finset.powersetCard_map, Finset.map_val, Multiset.map_map]
    refine Multiset.map_congr rfl fun s hs => ?_
    have hs' : s ∈ A.powersetCard 3 := hs
    have hcard : s.card = 3 := (Finset.mem_powersetCard.mp hs').2
    change s.prod id = (s.map e).prod id
    rw [Finset.prod_map]
    change (∏ x ∈ s, x) = ∏ x ∈ s, ω * x
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, hpow, one_mul]
  · intro heq
    have hB : ω ∈ B :=
      Finset.mem_map.mpr ⟨1, by simp [A], by change ω * 1 = ω; exact mul_one ω⟩
    have hA : ω ∈ A := heq.symm ▸ hB
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with h | h | h | h
    · exact hω.ne_one (by decide) h
    all_goals rw [h] at hpow; norm_num at hpow