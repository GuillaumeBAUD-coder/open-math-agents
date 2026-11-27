import OMAReductions.R_Erdos59_erdos_59_variants_erdos_frankl_rodl_R1
open SimpleGraph Filter
open scoped Classical

theorem bip59 {k : ℕ} (H : SimpleGraph (Fin k)) (hH : ¬ H.IsBipartite) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)^2 ≤ 8 * extremalNumber n H := by
  classical
  filter_upwards [eventually_ge_atTop 2] with n hn
  let a := n / 2
  let b := n - a
  let B := completeBipartiteGraph (Fin a) (Fin b)
  have hab : a + b = n := by dsimp [a,b]; omega
  have hB : B.IsBipartite := by
    refine ⟨Coloring.mk (Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1)) ?_⟩
    rintro (v | v) (w | w) hadj <;> simp_all [B, completeBipartiteGraph]
  have hfree : H.Free B := fun ⟨f⟩ => hH (hB.of_hom f.toHom)
  have edges : B.edgeFinset.card = a * b := by
    have h := encard_edgeSet_completeBipartiteGraph (W₁ := Fin a) (W₂ := Fin b)
    change B.edgeSet.encard = _ at h
    rw [← coe_edgeFinset, Set.encard_coe_eq_coe_finsetCard] at h
    simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin] at h
    exact_mod_cast h
  have hle := card_edgeFinset_le_extremalNumber hfree
  rw [edges, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hab] at hle
  have h₁ : n ≤ 3*a := by dsimp [a]; omega
  have h₂ : n ≤ 2*b := by dsimp [a,b]; omega
  have hprod := Nat.mul_le_mul h₁ h₂
  have : n^2 ≤ 8 * extremalNumber n H := by nlinarith
  exact_mod_cast this


theorem OMA.solution : OMA.R_Erdos59_erdos_59_variants_erdos_frankl_rodl_R1.H3 := @bip59
