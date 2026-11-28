import OMAReductions.R_ReedOmegaDeltaChi_reed_omega_delta_chi_conjecture_R1

/-!
# Proof of `ReedOmegaDeltaChi.reed_omega_delta_chi_conjecture.R1.H1`

Proves Reed's bound `2 * G.chromaticNumber ≤ G.ecliqueNum + G.emaxDegree + 2` for every simple
graph `G` on an arbitrary (possibly infinite) vertex type `V` satisfying
`G.emaxDegree ≤ G.ecliqueNum`.

- If `G.emaxDegree = ⊤`, the right-hand side is `⊤` and the inequality is trivial.
- If `G.emaxDegree = (d : ℕ)`, then every vertex `v` has `(G.neighborSet v).encard ≤ d`.
  Using `WellOrderingRel` on `V`, transfinite greedy coloring assigns each vertex `v` a color
  in `Fin (d + 1)` not used by any earlier neighbor (at most `d` forbidden colors out of
  `d + 1` available). This yields `G.Colorable (d + 1)`, so `G.chromaticNumber ≤ d + 1` and
  `2 * G.chromaticNumber ≤ 2 * (d + 1) = d + d + 2 ≤ G.ecliqueNum + d + 2`.
-/

namespace ReedOmegaDeltaChiInfR1H1Proof

open SimpleGraph

private lemma exists_unused_color {V : Type} {G : SimpleGraph V} {d : ℕ}
    (hdeg : ∀ v : V, (G.neighborSet v).encard ≤ (d : ℕ∞))
    (v : V) (prev : ∀ w : V, WellOrderingRel w v → Fin (d + 1)) :
    ∃ c : Fin (d + 1), ∀ w : V, ∀ hw : WellOrderingRel w v, G.Adj v w → prev w hw ≠ c := by
  classical
  let S : Set V := {w : V | G.Adj v w ∧ WellOrderingRel w v}
  let g : V → Fin (d + 1) := fun w =>
    if h : WellOrderingRel w v then prev w h else ⟨0, Nat.succ_pos d⟩
  have hS_sub : S ⊆ G.neighborSet v := fun _ hw => hw.1
  have hS_le : S.encard ≤ (d : ℕ∞) := (Set.encard_le_encard hS_sub).trans (hdeg v)
  have himg_le : (g '' S).encard ≤ (d : ℕ∞) := (Set.encard_image_le g S).trans hS_le
  have huniv : (Set.univ : Set (Fin (d + 1))).encard = ((d + 1 : ℕ) : ℕ∞) := by
    rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.card_fin]
  have hne : g '' S ≠ Set.univ := by
    intro heq
    rw [heq, huniv] at himg_le
    have hle_nat : d + 1 ≤ d := by exact_mod_cast himg_le
    omega
  have hss : ¬ (Set.univ ⊆ g '' S) := fun hsub => hne (Set.Subset.antisymm (Set.subset_univ _) hsub)
  rw [Set.not_subset] at hss
  obtain ⟨c, -, hc⟩ := hss
  refine ⟨c, fun w hw hadj heq => hc ?_⟩
  refine ⟨w, ⟨hadj, hw⟩, ?_⟩
  simp only [g, dif_pos hw, heq]

private noncomputable def greedyColor {V : Type} (G : SimpleGraph V) (d : ℕ)
    (hdeg : ∀ v : V, (G.neighborSet v).encard ≤ (d : ℕ∞)) : V → Fin (d + 1) :=
  (WellOrderingRel.isWellOrder (α := V)).wf.fix fun v prev =>
    Classical.choose (exists_unused_color hdeg v prev)

private lemma greedyColor_spec {V : Type} (G : SimpleGraph V) (d : ℕ)
    (hdeg : ∀ v : V, (G.neighborSet v).encard ≤ (d : ℕ∞))
    {u v : V} (huv : WellOrderingRel u v) (hadj : G.Adj v u) :
    greedyColor G d hdeg u ≠ greedyColor G d hdeg v := by
  have hfix : greedyColor G d hdeg v =
      Classical.choose (exists_unused_color hdeg v (fun w _ => greedyColor G d hdeg w)) :=
    WellFounded.fix_eq (WellOrderingRel.isWellOrder (α := V)).wf _ v
  rw [hfix]
  exact Classical.choose_spec
    (exists_unused_color hdeg v (fun w _ => greedyColor G d hdeg w)) u huv hadj

private lemma colorable_of_edegree_le {V : Type} (G : SimpleGraph V) (d : ℕ)
    (hdeg : ∀ v : V, (G.neighborSet v).encard ≤ (d : ℕ∞)) :
    G.Colorable (d + 1) := by
  refine ⟨SimpleGraph.Coloring.mk (greedyColor G d hdeg) ?_⟩
  intro u v hadj
  have hne : u ≠ v := G.ne_of_adj hadj
  rcases trichotomous_of WellOrderingRel u v with huv | rfl | hvu
  · exact greedyColor_spec G d hdeg huv hadj.symm
  · exact absurd rfl hne
  · exact (greedyColor_spec G d hdeg hvu hadj).symm

end ReedOmegaDeltaChiInfR1H1Proof

theorem OMA.solution : OMA.R_ReedOmegaDeltaChi_reed_omega_delta_chi_conjecture_R1.H1 := by
  intro V G hle
  cases hΔ : G.emaxDegree with
  | top => simp
  | coe d =>
    rw [hΔ] at hle
    have hdeg : ∀ v : V, (G.neighborSet v).encard ≤ (d : ℕ∞) := fun v => by
      have hv : G.edegree v ≤ G.emaxDegree := le_iSup G.edegree v
      simpa [SimpleGraph.edegree, hΔ] using hv
    have hcol : G.Colorable (d + 1) := ReedOmegaDeltaChiInfR1H1Proof.colorable_of_edegree_le G d hdeg
    have hχ : G.chromaticNumber ≤ ((d + 1 : ℕ) : ℕ∞) := hcol.chromaticNumber_le
    calc
      2 * G.chromaticNumber ≤ 2 * ((d + 1 : ℕ) : ℕ∞) := by gcongr
      _ = (d : ℕ∞) + (d : ℕ∞) + 2 := by
        norm_cast
        ring
      _ ≤ G.ecliqueNum + (d : ℕ∞) + 2 := by gcongr
