import OMAReductions.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1
import Mathlib

/-! Sample a uniform finite vertex measurably from the unit interval. Independent
samples over the vertices of the source graph give uniform random maps. The
graphon integrand is exactly the indicator that this map is a homomorphism.
The two-coordinate integral uses the argument of @TheWaler's merged graphon
proofs and the cycle-graph calculation in the catalogue. -/

open MeasureTheory SimpleGraph LimitObjects Set
namespace OMA.FiniteGraphon

private lemma edge_density (S : Graphon) :
    graphonHomDensity (completeGraph (Fin 2)) S = graphonEdgeDensity S := by
  classical
  have he : (completeGraph (Fin 2)).edgeFinset = {s((0 : Fin 2),(1 : Fin 2))} := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mem_edgeFinset,mem_edgeSet,Finset.mem_singleton]
      fin_cases a <;> fin_cases b <;> decide
  unfold graphonHomDensity graphonHomIntegrand graphonEdgeDensity
  simp_rw [he,Finset.prod_singleton]
  exact (measurePreserving_finTwoArrow (volume : Measure UnitInterval)).integral_comp'
    (fun t => (S t : ℝ))

private def acceptable {V W : Type} (H : SimpleGraph V) (G : SimpleGraph W) :
    Set (V → W) := {f | ∀ a b, H.Adj a b → G.Adj (f a) (f b)}

private def equivHom {V W : Type} (H : SimpleGraph V) (G : SimpleGraph W) :
    acceptable H G ≃ (H →g G) where
  toFun f := ⟨f.val,fun {a b} => f.property a b⟩
  invFun f := ⟨f,fun _ _ h => f.map_rel' h⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem realize {W : Type} [Fintype W] [Nonempty W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] :
    ∃ S : Graphon, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (H : SimpleGraph V) [DecidableRel H.Adj], graphonHomDensity H S = homDensity H G := by
  classical
  letI : MeasurableSpace W := ⊤
  let μ := (PMF.uniformOfFintype W).toMeasure
  obtain ⟨f,hf,hμ⟩ := μ.exists_measurable_map_eq
  let χ (w : W × W) : UnitInterval := if G.Adj w.1 w.2 then 1 else 0
  let S : Graphon := {
    toFun := fun u => χ (f u.1,f u.2)
    measurable := (measurable_of_countable χ).comp
      ((hf.comp measurable_fst).prodMk (hf.comp measurable_snd))
    symmetric := by
      intro x y
      by_cases h : G.Adj (f x) (f y)
      · simp [χ,h,h.symm]
      · have hr : ¬ G.Adj (f y) (f x) := fun he => h he.symm
        simp [χ,h,hr] }
  refine ⟨S,?_⟩
  intro V instV decV H decH
  let F (u : V → UnitInterval) (v : V) := f (u v)
  let ν : Measure (V → UnitInterval) := Measure.pi (fun _ => volume)
  have hmp : MeasurePreserving F ν (Measure.pi (fun _ : V => μ)) :=
    measurePreserving_pi _ _ (fun _ => (⟨hf,hμ⟩ : MeasurePreserving f volume μ))
  let T := acceptable H G
  have hm : MeasurableSet T := T.toFinite.measurableSet
  have representation : graphonHomIntegrand H S =
      (F ⁻¹' T).indicator (1 : (V → UnitInterval) → ℝ) := by
    funext u
    unfold graphonHomIntegrand
    by_cases good : F u ∈ T
    · rw [Set.indicator_of_mem (show u ∈ F ⁻¹' T from good)]
      apply Finset.prod_eq_one
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        have hadj : H.Adj a b := mem_edgeFinset.mp he
        have hG := good a b hadj
        change (χ (F u a,F u b)).val = 1
        simp [χ,hG]
    · rw [Set.indicator_of_notMem (show u ∉ F ⁻¹' T from good)]
      change ¬ ∀ a b, H.Adj a b → G.Adj (F u a) (F u b) at good
      push Not at good
      obtain ⟨a,b,hab,bad⟩ := good
      apply Finset.prod_eq_zero (i := s(a,b)) (mem_edgeFinset.mpr hab)
      change (χ (F u a,F u b)).val = 0
      simp [χ,bad]
  have hprod : Measure.pi (fun _ : V => μ) = (PMF.uniformOfFintype (V → W)).toMeasure := by
    apply Measure.ext_of_singleton
    intro a
    simp [μ,Measure.pi_singleton,ENNReal.inv_pow]
  have final := PMF.toMeasure_uniformOfFintype_apply (α := V → W) T hm
  unfold graphonHomDensity
  rw [representation,integral_indicator_one (hmp.measurable hm)]
  change (ν (F ⁻¹' T)).toReal = _
  rw [← Measure.map_apply hmp.measurable hm,hmp.map_eq,hprod,final]
  change _ = (Fintype.card (H →g G) : ℝ) / (Fintype.card W : ℝ)^Fintype.card V
  rw [Fintype.card_congr (equivHom H G),Fintype.card_fun]
  simp

end OMA.FiniteGraphon

theorem OMA.solution : OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1.H2 := by
  intro V W _ _ _ _ _ H _ G _
  obtain ⟨S,h⟩ := OMA.FiniteGraphon.realize G
  exact ⟨S,(OMA.FiniteGraphon.edge_density S).symm.trans (h _),h H⟩
