import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R1

/-! # From conjugacy representatives to all subgroups

Every subgroup is a conjugate `K.map (conj g)` of some representative `K ∈ R`, so the map
`(K, g) ↦ K.map (conj g)` from `R × Perm (Fin n)` onto the subgroups is surjective, and the
number of subgroups is at most `R.card * n!`. -/

theorem OMA.solution : OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R1.H1 := by
  intro n R hR
  classical
  let φ : R × Equiv.Perm (Fin n) → Subgroup (Equiv.Perm (Fin n)) :=
    fun p => (p.1 : Subgroup (Equiv.Perm (Fin n))).map (MulAut.conj p.2).toMonoidHom
  have hφ : Function.Surjective φ := by
    intro H
    obtain ⟨K, hK, g, rfl⟩ := hR H
    exact ⟨(⟨K, hK⟩, g), rfl⟩
  have h := Nat.card_le_card_of_surjective φ hφ
  unfold Erdos1162.f
  rw [Nat.card_prod] at h
  simpa [Nat.card_eq_fintype_card, Fintype.card_perm] using h
