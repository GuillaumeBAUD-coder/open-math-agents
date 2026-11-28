import OMAReductions.R_Erdos910_erdos_910_variants_rudin_CH_R1

namespace OMA.H2Proof910

open scoped Cardinal

open Cardinal Set TopologicalSpace

abbrev E := EuclideanSpace ℝ (Fin 2)

theorem mk_E_le : #E ≤ 𝔠 := by
  have : #E = #(Fin 2 → ℝ) := Cardinal.mk_congr (WithLp.equiv 2 (Fin 2 → ℝ))
  rw [this, mk_arrow, lift_id, Cardinal.mk_real, mk_fintype, Fintype.card_fin]
  have h := power_nat_le (c := 𝔠) (n := 2) aleph0_le_continuum
  rw [lift_natCast, power_natCast]
  exact h

theorem mk_countable_le : #{B : Set E // B.Countable} ≤ 𝔠 := by
  have h1 : #{B : Set E // B.Countable} ≤ #{t : Set E // #t ≤ ℵ₀} :=
    mk_le_of_injective (f := fun B => ⟨B.1, (le_aleph0_iff_set_countable).2 B.2⟩)
      (by intro a b h; simp only [Subtype.mk.injEq] at h; exact Subtype.ext h)
  refine h1.trans ((mk_bounded_set_le E ℵ₀).trans ?_)
  calc max #E ℵ₀ ^ ℵ₀ ≤ 𝔠 ^ ℵ₀ :=
        power_le_power_right (max_le mk_E_le aleph0_le_continuum)
    _ = 𝔠 := continuum_power_aleph0

theorem mk_closeds_le : #(Closeds E) ≤ #{B : Set E // B.Countable} := by
  classical
  have key : ∀ C : Closeds E, ∃ t : Set E, t.Countable ∧ closure t = (C : Set E) := by
    intro C
    obtain ⟨t, hts, htc, hst⟩ :=
      (IsSeparable.of_separableSpace (C : Set E)).exists_countable_dense_subset
    refine ⟨t, htc, le_antisymm ?_ hst⟩
    exact closure_minimal hts C.isClosed
  choose f hfc hf using key
  refine mk_le_of_injective (f := fun C => ⟨f C, hfc C⟩) ?_
  intro a b h
  have : f a = f b := congrArg Subtype.val h
  apply Closeds.ext
  rw [← hf a, ← hf b, this]

end OMA.H2Proof910

open Cardinal Set TopologicalSpace OMA.H2Proof910 in
theorem OMA.solution : OMA.R_Erdos910_erdos_910_variants_rudin_CH_R1.H2 := by
  intro hch
  have hJ : #(Closeds E ⊕ {B : Set E // B.Countable}) ≤ ℵ₁ := by
    rw [hch, ← add_def]
    exact add_le_of_le aleph0_le_continuum (mk_closeds_le.trans mk_countable_le) mk_countable_le
  obtain ⟨r, hr, hord⟩ := exists_ord_eq (Closeds E ⊕ {B : Set E // B.Countable})
  refine ⟨r, hr, fun i => ?_⟩
  rw [← le_aleph0_iff_set_countable, ← lt_aleph_one_iff]
  have := card_typein_lt (r := r) i hord
  rw [Ordinal.card_typein] at this
  exact this.trans_le hJ

