import FormalConjectures.Wikipedia.RamanujanTau

-- Problem: Ramanujan τ-function — τ two
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/RamanujanTau.lean:59 (declaration RamanujanTau.τ_two)
-- Credit: @eitanteperman (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open PowerSeries PowerSeries.WithPiTopology

lemma OMA.coeff_one_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℤ)
    (hf : ∀ i, constantCoeff (f i) = 1) :
    constantCoeff (∏ i ∈ s, f i) = 1 ∧ coeff 1 (∏ i ∈ s, f i) = ∑ i ∈ s, coeff 1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeff_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    refine ⟨by rw [map_mul, hf a, ih.1, one_mul], ?_⟩
    rw [coeff_mul, Finset.Nat.antidiagonal_succ]
    simp [ih.1, ih.2, hf a, coeff_zero_eq_constantCoeff_apply]
    ring

lemma OMA.coeff_one_factor (n : ℕ+) :
    constantCoeff ((1 - X ^ (n : ℕ)) ^ 24 : PowerSeries ℤ) = 1 ∧
      coeff 1 ((1 - X ^ (n : ℕ)) ^ 24 : PowerSeries ℤ) = if (n : ℕ) = 1 then -24 else 0 := by
  have h := OMA.coeff_one_prod (Finset.range 24) (fun _ => (1 - X ^ (n : ℕ) : PowerSeries ℤ))
    (fun _ => by simp [n.ne_zero])
  simp only [Finset.prod_const, Finset.card_range, Finset.sum_const, nsmul_eq_mul] at h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  split_ifs with h1
  · simp [h1, coeff_one]
  · simp [coeff_one, coeff_X_pow, Ne.symm h1]

theorem OMA.solution : type_of% @RamanujanTau.τ_two := by
  obtain ⟨t, ht⟩ := by
    simpa using ((continuous_coeff ℤ 1).tendsto _).comp RamanujanTau.multipliable.hasProd
  have key := ht (insert 1 t) (Finset.subset_insert _ _)
  unfold RamanujanTau.τ RamanujanTau.Δ
  rw [show (2 : ℕ) = 1 + 1 from rfl, coeff_succ_X_mul, ← key]
  have h := OMA.coeff_one_prod (insert 1 t) (fun n : ℕ+ => ((1 - X ^ (n : ℕ)) ^ 24 : PowerSeries ℤ))
    (fun n => (OMA.coeff_one_factor n).1)
  rw [h.2]
  simp only [fun n => (OMA.coeff_one_factor n).2]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  have : Finset.filter (fun x : ℕ+ => (x : ℕ) = 1) (insert 1 t) = {1} := by
    ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, PNat.coe_eq_one_iff]; tauto
  rw [this]
  simp
