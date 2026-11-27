import OMAReductions.R_Erdos1204_erdos_1204_variants_A_lower_R1
import Mathlib

-- Step Erdos1204.erdos_1204.variants.A_lower.R1.H2: hypothesis H2 of reduction Erdos1204.erdos_1204.variants.A_lower.R1
-- Credit: @ivillar
--
-- Proof. log (z + 1) is at most the harmonic number H_z (Mathlib). Group n in [1, z] by its
-- radical d = prod of the primes of n: d is squarefree and d <= n <= z. Inside a fiber,
-- n = d * m with every prime of m dividing d, and n -> m is injective, so the fiber sum of 1/n
-- is at most (1/d) * sum over all such m of 1/m = (1/d) * prod_{p | d} (1 - 1/p)^(-1)
-- (Euler product over d-factored numbers, Mathlib), which equals 1/phi(d).

open Finset

namespace OMA.Erdos1204H2

noncomputable def invHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' a b := by
    push_cast
    exact mul_inv (a : ℝ) (b : ℝ)

theorem hasSum_factored (d : ℕ) :
    HasSum (fun m : Nat.factoredNumbers d.primeFactors => ((m : ℕ) : ℝ)⁻¹)
      (∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹) := by
  have hb : ∀ {p : ℕ}, p.Prime → ‖invHom p‖ < 1 := by
    intro p hp
    have e : invHom p = (p : ℝ)⁻¹ := rfl
    rw [e, norm_inv, Real.norm_natCast]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := invHom) hb d.primeFactors).2
  rw [Finset.filter_true_of_mem (fun p hp => Nat.prime_of_mem_primeFactors hp)] at h
  exact h

theorem totient_real (d : ℕ) :
    (d.totient : ℝ) = d * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors d)
  push_cast at h
  exact h

theorem fiber_bound (d z : ℕ) :
    ∑ n ∈ (Icc 1 z).filter (fun n => ∏ p ∈ n.primeFactors, p = d), (n : ℝ)⁻¹ ≤
      1 / (d.totient : ℝ) := by
  classical
  set T := (Icc 1 z).filter (fun n => ∏ p ∈ n.primeFactors, p = d) with hT
  have hmem : ∀ n ∈ T, n ≠ 0 ∧ d ∣ n ∧ (n / d).primeFactors ⊆ d.primeFactors := by
    intro n hn
    rw [hT, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨h1, -⟩, h2⟩ := hn
    have hdn : d ∣ n := h2 ▸ Nat.prod_primeFactors_dvd n
    refine ⟨by omega, hdn, ?_⟩
    rw [← h2, Nat.primeFactors_prod_primeFactors]
    exact Nat.primeFactors_mono (Nat.div_dvd_of_dvd (Nat.prod_primeFactors_dvd n)) (by omega)
  have hsplit : ∀ n ∈ T, (n : ℝ)⁻¹ = (d : ℝ)⁻¹ * ((n / d : ℕ) : ℝ)⁻¹ := by
    intro n hn
    obtain ⟨-, hdn, -⟩ := hmem n hn
    rw [← mul_inv]
    congr 1
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hdn]
  rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
  have hinj : Set.InjOn (fun n => n / d) (T : Set ℕ) := by
    intro a ha b hb hab
    exact (Nat.div_left_inj (hmem a ha).2.1 (hmem b hb).2.1).mp hab
  rw [← Finset.sum_image (f := fun m : ℕ => ((m : ℝ))⁻¹) hinj]
  have hU : ∀ m ∈ T.image (fun n => n / d), m ∈ Nat.factoredNumbers d.primeFactors := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hn0, hdn, hsub⟩ := hmem n hn
    refine Nat.mem_factoredNumbers_of_primeFactors_subset ?_ hsub
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn (by omega)
    exact (Nat.div_pos (Nat.le_of_dvd (by omega) hdn) hdpos).ne'
  have hle : ∑ m ∈ T.image (fun n => n / d), ((m : ℝ))⁻¹ ≤
      ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
    rw [← Finset.sum_subtype_of_mem (fun m : ℕ => ((m : ℝ))⁻¹) hU]
    exact sum_le_hasSum _ (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg _)) (hasSum_factored d)
  rw [totient_real, one_div, mul_inv, ← Finset.prod_inv_distrib]
  exact mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (Nat.cast_nonneg _))

end OMA.Erdos1204H2

theorem OMA.solution : OMA.R_Erdos1204_erdos_1204_variants_A_lower_R1.H2 := by
  unfold OMA.R_Erdos1204_erdos_1204_variants_A_lower_R1.H2
  intro z hz
  have hlog : Real.log ((z : ℝ) + 1) ≤ ∑ n ∈ Icc 1 z, (n : ℝ)⁻¹ := by
    have h := log_add_one_le_harmonic z
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    exact h
  refine hlog.trans ?_
  have hmaps : ∀ n ∈ Icc 1 z, (∏ p ∈ n.primeFactors, p) ∈ (Icc 1 z).filter Squarefree := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hpos : 0 < ∏ p ∈ n.primeFactors, p :=
      Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    have hle : ∏ p ∈ n.primeFactors, p ≤ n := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
    refine ⟨⟨hpos, by omega⟩, ?_⟩
    rw [← Nat.radical_eq_prod_primeFactors]
    exact UniqueFactorizationMonoid.squarefree_radical
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum (fun d _ => ?_)
  exact OMA.Erdos1204H2.fiber_bound d z
