import FormalConjectures.ErdosProblems.«94»
import Mathlib.Geometry.Euclidean.PerpBisector

/-! Equal-distance triples bound the second moment of the distance multiplicities. -/

open Finset EuclideanGeometry
open scoped BigOperators

namespace ErdosDistanceMoment

abbrev Point := EuclideanSpace ℝ (Fin 2)

noncomputable def incident (P : Finset Point) (p : Point) (u : ℝ) : ℕ :=
  open Classical in (P.filter fun q => dist p q = u).card

noncomputable def centers (P : Finset Point) (q r : Point) : ℕ :=
  open Classical in (P.filter fun p => dist p q = dist p r).card

theorem centers_le_two {P : Finset Point} (hP : NonTrilinear (P : Set Point))
    {q r : Point} (hqr : q ≠ r) : centers P q r ≤ 2 := by
  classical
  have hcol : Collinear ℝ (AffineSubspace.perpBisector q r : Set Point) := by
    rw [collinear_iff_finrank_le_one, ← AffineSubspace.direction_eq_vectorSpan,
      AffineSubspace.direction_perpBisector]
    have h := (ℝ ∙ (r -ᵥ q)).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton (vsub_ne_zero.mpr hqr.symm), finrank_euclideanSpace_fin] at h
    omega
  by_contra! hn
  rw [centers] at hn
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hn
  simp only [Finset.mem_filter] at ha hb hc
  refine hP ha.1 hb.1 hc.1 hab hbc hac (hcol.subset ?_)
  simp [Set.insert_subset_iff, Set.singleton_subset_iff,
    AffineSubspace.mem_perpBisector_iff_dist_eq, ha.2, hb.2, hc.2]

theorem multiplicity_le_incident (P : Finset Point) (u : ℝ) :
    distanceMultiplicity P u ≤ ∑ p ∈ P, incident P p u := by
  classical
  have hsub : P.offDiag ⊆ P ×ˢ P := by simp [← Finset.diag_union_offDiag]
  refine (Nat.div_le_self _ 2).trans ?_
  refine (Finset.card_le_card (Finset.filter_subset_filter (p := fun x : Point × Point =>
    dist x.1 x.2 = u) hsub)).trans_eq ?_
  simp only [incident, Finset.card_filter, Finset.sum_product]

theorem incident_sq (P : Finset Point) (p : Point) (u : ℝ) :
    incident P p u ^ 2 = ∑ q ∈ P, ∑ r ∈ P,
      if dist p q = u ∧ dist p r = u then 1 else 0 := by
  unfold incident
  rw [pow_two, ← Finset.card_product, ← Finset.filter_product, Finset.card_filter,
    Finset.sum_product]

theorem point_moment_le (P : Finset Point) (p : Point) :
    (∑ u ∈ distanceSet P, incident P p u ^ 2) ≤
      ∑ q ∈ P, ∑ r ∈ P, if dist p q = dist p r then 1 else 0 := by
  classical
  simp_rw [incident_sq]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun r _ => ?_
  by_cases heq : dist p q = dist p r
  · simp [← heq]
    split_ifs <;> omega
  · have himp (u : ℝ) : ¬ (dist p q = u ∧ dist p r = u) :=
      fun h => heq (h.1.trans h.2.symm)
    simp [heq, himp]

theorem sum_centers_le (P : Finset Point) (hP : NonTrilinear (P : Set Point))
    {q : Point} (hq : q ∈ P) : (∑ r ∈ P, centers P q r) ≤ 3 * P.card := by
  classical
  rw [← Finset.sum_erase_add P _ hq]
  have hdiag : centers P q q = P.card := by simp [centers]
  rw [hdiag]
  have hoff : (∑ r ∈ P.erase q, centers P q r) ≤ ∑ _r ∈ P.erase q, (2 : ℕ) := by
    refine Finset.sum_le_sum fun r hr => ?_
    exact centers_le_two hP (Finset.ne_of_mem_erase hr).symm
  simp only [Finset.sum_const, Nat.nsmul_eq_mul] at hoff
  have hcard := Finset.card_erase_add_one hq
  omega

theorem second_incidence_le (P : Finset Point) (hP : NonTrilinear (P : Set Point)) :
    (∑ u ∈ distanceSet P, ∑ p ∈ P, incident P p u ^ 2) ≤ 3 * P.card ^ 2 := by
  classical
  rw [Finset.sum_comm]
  calc
    (∑ p ∈ P, ∑ u ∈ distanceSet P, incident P p u ^ 2) ≤
        ∑ p ∈ P, ∑ q ∈ P, ∑ r ∈ P, if dist p q = dist p r then 1 else 0 :=
      Finset.sum_le_sum fun p _ => point_moment_le P p
    _ = ∑ q ∈ P, ∑ r ∈ P, centers P q r := by
      simp only [centers, Finset.card_filter]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ ≤ ∑ _q ∈ P, 3 * P.card := Finset.sum_le_sum fun q hq => sum_centers_le P hP hq
    _ = 3 * P.card ^ 2 := by simp only [Finset.sum_const, Nat.nsmul_eq_mul]; ring

theorem distance_moment_le (P : Finset Point) (hP : NonTrilinear (P : Set Point)) :
    (∑ u ∈ distanceSet P, distanceMultiplicity P u ^ 2) ≤ 3 * P.card ^ 3 := by
  classical
  calc
    (∑ u ∈ distanceSet P, distanceMultiplicity P u ^ 2) ≤
        ∑ u ∈ distanceSet P, P.card * ∑ p ∈ P, incident P p u ^ 2 := by
      refine Finset.sum_le_sum fun u _ => ?_
      exact (Nat.pow_le_pow_left (multiplicity_le_incident P u) 2).trans
        (by simpa [Finset.sum_const, nsmul_eq_mul] using
          Finset.sum_mul_sq_le_sq_mul_sq P (fun _ => (1 : ℕ)) fun p => incident P p u)
    _ ≤ P.card * (3 * P.card ^ 2) := by
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _ (second_incidence_le P hP)
    _ = 3 * P.card ^ 3 := by ring

end ErdosDistanceMoment

theorem OMA.solution : type_of% @Erdos94.erdos_94.variants.no_three_on_a_line := by
  refine ⟨3, by norm_num, fun P hP => ?_⟩
  exact_mod_cast ErdosDistanceMoment.distance_moment_le P hP
