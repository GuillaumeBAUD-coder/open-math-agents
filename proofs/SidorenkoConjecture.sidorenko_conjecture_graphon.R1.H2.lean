import OMAReductions.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1
import Mathlib

/-! # Finite uniform hosts as graphons
A uniform sample of the vertices of a finite graph from the unit interval
pulls its adjacency matrix back to a symmetric measurable graphon. Each
test graph has exactly the original homomorphism density. -/

namespace OMA.SidorenkoTransfer
open LimitObjects SimpleGraph MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

private abbrev U := LimitObjects.UnitInterval

private def good {V W : Type*} (H : SimpleGraph V) (G : SimpleGraph W) (f : V → W) : Prop :=
  ∀ v w : V, H.Adj v w → G.Adj (f v) (f w)

private def homEquiv {V W : Type*} (H : SimpleGraph V) (G : SimpleGraph W) :
    {f : V → W // good H G f} ≃ (H →g G) where
  toFun f := ⟨f.val, fun h => f.property _ _ h⟩
  invFun f := ⟨f, fun _ _ h => f.map_adj h⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def step {W : Type*} [Fintype W] [MeasurableSpace W]
    [DiscreteMeasurableSpace W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (f : U → W) (hf : Measurable f) : Graphon where
  toFun ab := if G.Adj (f ab.1) (f ab.2) then 1 else 0
  measurable := (show Measurable (fun ab : W × W =>
    (if G.Adj ab.1 ab.2 then 1 else 0 : U)) from Measurable.of_discrete).comp
      ((hf.comp measurable_fst).prodMk (hf.comp measurable_snd))
  symmetric a b := by simp only [G.adj_comm (f b) (f a)]

private theorem integrand {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [MeasurableSpace W] [DiscreteMeasurableSpace W]
    (H : SimpleGraph V) [DecidableRel H.Adj] (G : SimpleGraph W) [DecidableRel G.Adj]
    (f : U → W) (hf : Measurable f) (x : V → U) :
    graphonHomIntegrand H (step G f hf) x =
      (Set.indicator {y | good H G y} (fun _ => (1:ℝ))) (f ∘ x) := by
  classical
  unfold graphonHomIntegrand
  by_cases h : good H G (f ∘ x)
  · rw [Set.indicator_of_mem h]
    apply Finset.prod_eq_one
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have adj : H.Adj a b := by simpa using he
      have hg := h a b adj
      simpa [Graphon.evalEdge,step,Function.comp_def] using
        (show ((if G.Adj (f (x a)) (f (x b)) then 1 else 0 : U) : ℝ) = 1 by
          simp [show G.Adj (f (x a)) (f (x b)) from hg])
  · rw [Set.indicator_of_notMem h]
    simp only [good, not_forall] at h
    obtain ⟨a,b,hab,hn⟩ := h
    apply Finset.prod_eq_zero (i := s(a,b)) (by simpa using hab)
    have ng : ¬G.Adj (f (x a)) (f (x b)) := hn
    simp [Graphon.evalEdge,step,ng]

private theorem finiteIntegral {V W : Type*} [Fintype V] [Fintype W] [Nonempty W]
    [DecidableEq V] [DecidableEq W] [MeasurableSpace W] [DiscreteMeasurableSpace W]
    (H : SimpleGraph V) [DecidableRel H.Adj] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (∫ y, (Set.indicator {z | good H G z} (fun _ => (1:ℝ))) y
      ∂(uniformOn (Set.univ : Set (V → W)))) = homDensity H G := by
  classical
  let t := Finset.univ.filter (good H G)
  have ht : (t : Set (V → W)) = {z | good H G z} := by ext; simp [t]
  have hcard : t.card = homCount H G := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr ((Equiv.setCongr ht).trans (homEquiv H G))
  rw [integral_indicator_const (1:ℝ) (s := {z | good H G z}) MeasurableSet.of_discrete,
    smul_eq_mul, mul_one, ← ht, measureReal_def]
  have hm := uniformOn_apply_finset (s := (Finset.univ : Finset (V → W))) (t := t)
  simp only [Finset.coe_univ, Finset.univ_inter, Finset.card_univ, Fintype.card_fun] at hm
  rw [hm, ENNReal.toReal_div]
  simp [hcard, homDensity]

private theorem hom_transfer {V W : Type*} [Fintype V] [Fintype W] [Nonempty W]
    [DecidableEq V] [DecidableEq W] [MeasurableSpace W] [DiscreteMeasurableSpace W]
    (H : SimpleGraph V) [DecidableRel H.Adj] (G : SimpleGraph W) [DecidableRel G.Adj]
    (f : U → W) (hf : MeasurePreserving f volume (uniformOn (Set.univ : Set W))) :
    graphonHomDensity H (step G f hf.measurable) = homDensity H G := by
  have hp := measurePreserving_pi (ι := V) (fun _ => (volume : Measure U))
    (fun _ => uniformOn (Set.univ : Set W)) (fun _ => hf)
  have hm : Measure.pi (fun _ : V => uniformOn (Set.univ : Set W)) =
      uniformOn (Set.univ : Set (V → W)) := by
    simpa using (uniformOn_pi (ι := V) (f := fun _ => (Set.univ : Set W))).symm
  rw [hm] at hp
  let val := Set.indicator {z | good H G z} (fun _ => (1:ℝ))
  have meas : Measurable val := Measurable.of_discrete
  rw [← finiteIntegral H G, graphonHomDensity, ← hp.map_eq,
    integral_map hp.measurable.aemeasurable (meas.aestronglyMeasurable)]
  exact integral_congr_ae (Filter.Eventually.of_forall (integrand H G f hf.measurable))

private theorem edge_eq_hom_two (S : Graphon) :
    graphonEdgeDensity S = graphonHomDensity (completeGraph (Fin 2)) S := by
  have hpair := measurePreserving_finTwoArrow (volume : Measure U)
  have hEdge : (completeGraph (Fin 2)).edgeFinset = {s((0:Fin 2),1)} := by decide +kernel
  have meas : Measurable (fun x : U × U => (S x : ℝ)) := measurable_subtype_coe.comp S.measurable
  rw [graphonEdgeDensity, graphonHomDensity, ← hpair.map_eq,
    integral_map hpair.measurable.aemeasurable meas.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with x
  simp [graphonHomIntegrand, hEdge, Graphon.evalEdge, MeasurableEquiv.finTwoArrow]

theorem realize {V W : Type*} [Fintype V] [Fintype W] [Nonempty W]
    [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph V) [DecidableRel H.Adj] (G : SimpleGraph W) [DecidableRel G.Adj] :
    ∃ S : Graphon, graphonEdgeDensity S = homDensity (completeGraph (Fin 2)) G ∧
      graphonHomDensity H S = homDensity H G := by
  let : MeasurableSpace W := ⊤
  obtain ⟨f,hf,law⟩ := (uniformOn (Set.univ : Set W)).exists_measurable_map_eq
  have rng : MeasurePreserving f volume (uniformOn (Set.univ : Set W)) := ⟨hf,law⟩
  let S := step G f hf
  exact ⟨S, (edge_eq_hom_two S).trans (hom_transfer _ G f rng), hom_transfer H G f rng⟩
end OMA.SidorenkoTransfer

theorem OMA.solution : OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1.H2 :=
  @OMA.SidorenkoTransfer.realize
