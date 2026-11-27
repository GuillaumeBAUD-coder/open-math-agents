import OMAReductions.R_mse_2615963_R1
import Mathlib

-- Step mse-2615963.R1.H1: hypothesis H1 of reduction mse-2615963.R1
-- Credit: @stochastic-parrot-ftw

open Polynomial Finset

namespace OMA.Mse2615963H1

/-- `C n` has degree at most `n` and is monic of degree `n` for `n ≥ 1`. -/
theorem cheb_C_props (R : Type*) [CommRing R] : ∀ n : ℕ,
    (Chebyshev.C R (n : ℤ)).natDegree ≤ n ∧ (1 ≤ n → (Chebyshev.C R (n : ℤ)).coeff n = 1)
  | 0 => by
    refine ⟨?_, fun h => absurd h (by omega)⟩
    simp only [Nat.cast_zero, Chebyshev.C_zero]
    rw [natDegree_ofNat]
  | 1 => by simpa [Chebyshev.C_one] using natDegree_X_le (R := R)
  | (n + 2) => by
    obtain ⟨h1d, h1c⟩ := cheb_C_props R (n + 1)
    obtain ⟨h0d, -⟩ := cheb_C_props R n
    have e : Chebyshev.C R ((n + 2 : ℕ) : ℤ) =
        X * Chebyshev.C R ((n + 1 : ℕ) : ℤ) - Chebyshev.C R (n : ℤ) := by
      have := Chebyshev.C_add_two (R := R) (n : ℤ)
      push_cast
      exact this
    rw [e]
    constructor
    · refine (natDegree_sub_le _ _).trans (max_le ?_ (by omega))
      refine natDegree_mul_le.trans ?_
      have := natDegree_X_le (R := R)
      omega
    · intro _
      rw [coeff_sub, coeff_X_mul, h1c (by omega),
        coeff_eq_zero_of_natDegree_lt (by omega : (Chebyshev.C R (n : ℤ)).natDegree < n + 2)]
      simp

theorem sum_pow_card_sub_one (p : ℕ) [hp : Fact p.Prime] :
    ∑ x : ZMod p, x ^ (p - 1) = -1 := by
  classical
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, Units.val_injective⟩
  have hmap : univ.map φ = univ \ {0} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton, φ] using! isUnit_iff_ne_zero
  have hq : Fintype.card (ZMod p) = p := ZMod.card p
  calc ∑ x : ZMod p, x ^ (p - 1) = ∑ x ∈ univ \ {(0 : ZMod p)}, x ^ (p - 1) := by
        rw [← sum_sdiff ({0} : Finset (ZMod p)).subset_univ, sum_singleton, zero_pow hp1,
          add_zero]
    _ = ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ (p - 1)) := by simp [φ, ← hmap, univ.sum_map φ]
    _ = -1 := by
        rw [FiniteField.sum_pow_units (ZMod p) (p - 1), if_pos]
        rw [hq]

theorem sum_eval_zmod (p : ℕ) [hp : Fact p.Prime] (P : (ZMod p)[X]) (hP : P.natDegree < p) :
    ∑ x : ZMod p, P.eval x = - P.coeff (p - 1) := by
  have h2 := hp.out.two_le
  simp_rw [eval_eq_sum_range' hP]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hsplit : Finset.range p = insert (p - 1) (Finset.range (p - 1)) := by
    rw [← Finset.range_add_one]; congr 1; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have h0 : ∑ j ∈ Finset.range (p - 1), P.coeff j * ∑ x : ZMod p, x ^ j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) j (by
      rw [ZMod.card]; exact Finset.mem_range.mp hj), mul_zero]
  rw [h0, add_zero, sum_pow_card_sub_one p, mul_neg_one]

end OMA.Mse2615963H1

open OMA.Mse2615963H1 in
theorem OMA.solution : OMA.R_mse_2615963_R1.H1 := by
  intro p hp
  have := Fact.mk hp
  have h2 := hp.two_le
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  -- move the evaluation into `ZMod p`
  have hcast : ∀ k : ℕ, (((Chebyshev.C ℤ ((p : ℤ) - 1)).eval (k : ℤ) : ℤ) : ZMod p) =
      (Chebyshev.C (ZMod p) ((p : ℤ) - 1)).eval (k : ZMod p) := by
    intro k
    have := Chebyshev.algebraMap_eval_C (R := ℤ) (R' := ZMod p) (k : ℤ) ((p : ℤ) - 1)
    simpa using this
  simp_rw [hcast]
  -- reindex the sum over `range p` as a sum over `ZMod p`
  have hre : ∑ k ∈ Finset.range p, (Chebyshev.C (ZMod p) ((p : ℤ) - 1)).eval (k : ZMod p) =
      ∑ x : ZMod p, (Chebyshev.C (ZMod p) ((p : ℤ) - 1)).eval x := by
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
    rw [← Fin.sum_univ_eq_sum_range (fun k => (Chebyshev.C (ZMod (m + 1)) (((m + 1 : ℕ) : ℤ) - 1)).eval
      (k : ZMod (m + 1))) (m + 1)]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact ZMod.natCast_zmod_val (n := m + 1) i
  rw [hre]
  have hpm : ((p : ℤ) - 1) = ((p - 1 : ℕ) : ℤ) := by omega
  rw [hpm]
  obtain ⟨hd, hc⟩ := cheb_C_props (ZMod p) (p - 1)
  rw [sum_eval_zmod p _ (by omega), hc (by omega)]
