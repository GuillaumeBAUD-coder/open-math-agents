import OMAReductions.R_Erdos1119_erdos_1119_R1

open Cardinal Order
open scoped Cardinal

namespace E1119H1

theorem zeros_countable (h : ℂ → ℂ) (hd : Differentiable ℂ h) (x : ℂ) (hx : h x ≠ 0) :
    (h ⁻¹' {0}).Countable := by
  have han : AnalyticOnNhd ℂ h Set.univ := fun z _ => hd.analyticAt z
  have hc := han.preimage_zero_mem_codiscrete hx
  have hdisc : IsDiscrete (h ⁻¹' {0}) := by
    have := isDiscrete_of_codiscreteWithin (s := h ⁻¹' {0}) (U := Set.univ) hc
    simpa using this
  exact (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc

end E1119H1

theorem OMA.solution : OMA.R_Erdos1119_erdos_1119_R1.H1 := by
  intro m hm hsucc F hF hval
  by_contra hlt
  push Not at hlt
  have hsle : succ m ≤ #F := Order.succ_le_of_lt hlt
  obtain ⟨G, hGF, hG⟩ := Cardinal.le_mk_iff_exists_subset.mp hsle
  let ι := {p : G × G // p.1 ≠ p.2}
  let A : ι → Set ℂ := fun p => (fun z => p.1.1.1 z - p.1.2.1 z) ⁻¹' {0}
  have hA : ∀ p, (A p).Countable := by
    intro p
    have hne : p.1.1.1 ≠ p.1.2.1 := fun h => p.2 (Subtype.ext h)
    obtain ⟨x, hx⟩ : ∃ x, p.1.1.1 x - p.1.2.1 x ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (funext fun x => sub_eq_zero.mp (hall x))
    exact E1119H1.zeros_countable _ ((hF _ (hGF p.1.1.2)).sub (hF _ (hGF p.1.2.2))) x hx
  have hinf : ℵ₀ ≤ succ m := (hm.le.trans (Order.le_succ m))
  have hB : #(⋃ p, A p) < 𝔠 := by
    calc #(⋃ p, A p) ≤ #ι * ⨆ p, #(A p) := Cardinal.mk_iUnion_le A
      _ ≤ succ m * ℵ₀ := by
        gcongr
        · calc #ι ≤ #(G × G) := Cardinal.mk_subtype_le _
            _ = succ m := by rw [Cardinal.mk_prod, Cardinal.lift_id, hG, Cardinal.mul_eq_self hinf]
        · exact ciSup_le' fun p => (hA p).le_aleph0
      _ = succ m := Cardinal.mul_eq_left hinf hinf aleph0_ne_zero
      _ < 𝔠 := hsucc
  obtain ⟨z₀, hz₀⟩ : ∃ z, z ∉ ⋃ p, A p := by
    by_contra hall
    push Not at hall
    have : (⋃ p, A p) = Set.univ := Set.eq_univ_of_forall hall
    rw [this, Cardinal.mk_univ, Cardinal.mk_complex] at hB
    exact lt_irrefl _ hB
  have hinj : #G ≤ #{y : ℂ | ∃ f ∈ F, f z₀ = y} := by
    refine Cardinal.mk_le_of_injective (f := fun g : G => (⟨g.1 z₀, g.1, hGF g.2, rfl⟩ : {y : ℂ | ∃ f ∈ F, f z₀ = y})) ?_
    intro g g' hgg
    by_contra hne
    apply hz₀
    refine Set.mem_iUnion.mpr ⟨⟨(g, g'), hne⟩, ?_⟩
    have := congrArg Subtype.val hgg
    simp only [A, Set.mem_preimage, Set.mem_singleton_iff]
    simpa [sub_eq_zero] using this
  have := (hG ▸ hinj).trans (hval z₀)
  exact absurd this (not_le.mpr (Order.lt_succ_of_not_isMax (not_isMax m)))
