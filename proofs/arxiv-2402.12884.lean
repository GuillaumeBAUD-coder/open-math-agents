import OMAStatements.S_arxiv_2402_12884
import Mathlib

open OMA.S_arxiv_2402_12884 Finset
open scoped Classical

namespace MatchingIndex

noncomputable section

variable {n : ℕ}

private def degree (G : SimpleGraph (Fin n)) (v : Fin n) : ℝ :=
  (G.degree v : ℝ)

private def weight (G : SimpleGraph (Fin n)) (e : Fin n × Fin n) : ℝ :=
  Real.sqrt (degree G e.1 * degree G e.2)

private theorem degree_nonneg (G : SimpleGraph (Fin n)) (v : Fin n) :
    0 ≤ degree G v := by unfold degree; positivity

private theorem weight_nonneg (G : SimpleGraph (Fin n)) (e : Fin n × Fin n) :
    0 ≤ weight G e := Real.sqrt_nonneg _

private theorem weight_pos {G : SimpleGraph (Fin n)} {e : Fin n × Fin n}
    (he : e ∈ darts G) : 0 < weight G e := by
  have ha : G.Adj e.1 e.2 := (mem_filter.mp he).2
  have hp {v w : Fin n} (h : G.Adj v w) : 0 < degree G v := by
    unfold degree
    exact_mod_cast ((G.degree_pos_iff_exists_adj v).mpr ⟨w, h⟩)
  exact Real.sqrt_pos_of_pos (mul_pos (hp ha) (hp ha.symm))

private theorem degree_sum (G : SimpleGraph (Fin n)) :
    ∑ v, degree G v = ((darts G).card : ℝ) := by
  unfold degree
  norm_cast
  rw [G.sum_degrees_eq_twice_card_edges, G.two_mul_card_edgeFinset]
  rfl

private theorem weighted_cauchy {G : SimpleGraph (Fin n)} {S : Finset (Fin n × Fin n)}
    (hS : S ⊆ darts G) :
    (S.card : ℝ)^2 ≤ (∑ e ∈ S, (weight G e)⁻¹) * ∑ e ∈ S, weight G e := by
  simpa using sum_sq_le_sum_mul_sum_of_sq_le_mul S (r := fun _ => (1:ℝ))
    (f := fun e => (weight G e)⁻¹) (g := weight G)
    (fun e _ => inv_nonneg.mpr (weight_nonneg G e))
    (fun e _ => weight_nonneg G e)
    (fun e he => by rw [one_pow, inv_mul_cancel₀ (weight_pos (hS he)).ne'])

private theorem squared_weight (G : SimpleGraph (Fin n)) (e : Fin n × Fin n) :
    weight G e ^ 2 = degree G e.1 * degree G e.2 :=
  Real.sq_sqrt (mul_nonneg (degree_nonneg G _) (degree_nonneg G _))

private theorem square_sum_darts (G : SimpleGraph (Fin n)) :
    (∑ e ∈ darts G, weight G e)^2 ≤ ((darts G).card : ℝ)^3 := by
  have hsq := sum_sq_le_sum_mul_sum_of_sq_le_mul (darts G) (r := weight G)
    (f := fun _ => (1:ℝ)) (g := fun e => weight G e ^ 2)
    (fun _ _ => zero_le_one) (fun e _ => sq_nonneg (weight G e)) (by simp)
  have hprod : ∑ e ∈ darts G, weight G e ^ 2 ≤ ((darts G).card : ℝ)^2 := by
    calc
      ∑ e ∈ darts G, weight G e ^ 2 ≤ ∑ e : Fin n × Fin n, weight G e ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun e _ _ => sq_nonneg (weight G e))
      _ = ((darts G).card : ℝ)^2 := by
        simp only [squared_weight]
        rw [← univ_product_univ, sum_product]
        simp_rw [← mul_sum]
        rw [← sum_mul, degree_sum, pow_two]
  simp only [sum_const, nsmul_eq_mul, mul_one] at hsq
  calc
    _ ≤ ((darts G).card : ℝ) * ∑ e ∈ darts G, weight G e ^ 2 := hsq
    _ ≤ ((darts G).card : ℝ) * ((darts G).card : ℝ)^2 :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by ring

private theorem randic_nonneg (G : SimpleGraph (Fin n)) : 0 ≤ randic G := by
  change 0 ≤ (∑ e ∈ darts G, (weight G e)⁻¹)/2
  exact div_nonneg (sum_nonneg fun e _ => inv_nonneg.mpr (weight_nonneg G e)) (by norm_num)

private theorem mass_bound (G : SimpleGraph (Fin n)) :
    ((darts G).card : ℝ) ≤ (2*randic G)^2 := by
  let D : ℝ := (darts G).card
  let W : ℝ := ∑ e ∈ darts G, weight G e
  let Q : ℝ := ∑ e ∈ darts G, (weight G e)⁻¹
  have hQ : Q = 2 * randic G := by
    change Q = 2*(Q/2)
    ring
  rw [← hQ]
  change D ≤ Q^2
  have hD : 0 ≤ D := by unfold D; positivity
  by_cases h : D=0
  · rw [h]
    positivity
  have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm h)
  have h₁ : D^2 ≤ Q*W := weighted_cauchy Subset.rfl
  have h₂ : W^2 ≤ D^3 := square_sum_darts G
  have hp : D^4 ≤ Q^2*W^2 := by
    simpa only [mul_pow, ← pow_mul, show (2 : ℕ) * 2 = 4 by decide] using
      pow_le_pow_left₀ (sq_nonneg D) h₁ 2
  have hq := mul_le_mul_of_nonneg_left h₂ (sq_nonneg Q)
  apply le_of_mul_le_mul_right (a := D^3) _ (pow_pos hDpos 3)
  nlinarith

private theorem matching_weight_sum {G : SimpleGraph (Fin n)} {M : Finset (Fin n × Fin n)}
    (hM : isMatching G M) : ∑ e ∈ M, weight G e ≤ ((darts G).card : ℝ) := by
  classical
  have hfst : Set.InjOn Prod.fst (M : Set (Fin n × Fin n)) := hM.2.2
  have hsnd : Set.InjOn Prod.snd (M : Set (Fin n × Fin n)) := by
    intro e he f hf h
    have he' : e.swap ∈ (M : Set _) := hM.2.1 e he
    have hf' : f.swap ∈ (M : Set _) := hM.2.1 f hf
    have hh : e.swap = f.swap := hfst he' hf' h
    exact Prod.swap_injective hh
  have hcoord (f : Fin n × Fin n → Fin n) (hf : Set.InjOn f (M : Set _)) :
      ∑ e ∈ M, degree G (f e) ≤ ((darts G).card : ℝ) := by
    rw [← sum_image hf, ← degree_sum]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => degree_nonneg G i)
  have hroot (e : Fin n × Fin n) :
      weight G e ≤ (degree G e.1+degree G e.2)/2 := by
    unfold weight
    apply (Real.sqrt_le_iff).mpr
    constructor
    · exact div_nonneg (add_nonneg (degree_nonneg G _) (degree_nonneg G _)) (by norm_num)
    · nlinarith [sq_nonneg (degree G e.1-degree G e.2)]
  calc
    _ ≤ ∑ e ∈ M, (degree G e.1 + degree G e.2)/2 := sum_le_sum fun e _ => hroot e
    _ = ((∑ e ∈ M, degree G e.1) + ∑ e ∈ M, degree G e.2)/2 := by
      rw [← sum_div, sum_add_distrib]
    _ ≤ _ := by linarith [hcoord Prod.fst hfst, hcoord Prod.snd hsnd]

private theorem cubic_bound (G : SimpleGraph (Fin n)) :
    (matchingNumber G : ℝ)^2 ≤ 2 * randic G ^ 3 := by
  classical
  let S := (darts G).powerset.filter (isMatching G)
  have hnon : S.Nonempty := ⟨∅, by simp [S, isMatching]⟩
  obtain ⟨M, hM, hME⟩ := exists_mem_eq_sup S hnon (fun M => M.card/2)
  have hnum : matchingNumber G = M.card/2 := hME
  have hmatch : isMatching G M := (mem_filter.mp hM).2
  have hm : 2*(matchingNumber G : ℝ) ≤ M.card := by
    rw [hnum]
    exact_mod_cast Nat.mul_div_le M.card 2
  have hQ : (∑ e ∈ M, (weight G e)⁻¹) ≤ 2*randic G := by
    have hc : (∑ e ∈ darts G, (weight G e)⁻¹) = 2*randic G := by
      change _ = 2*((∑ e ∈ darts G, (weight G e)⁻¹)/2)
      ring
    rw [← hc]
    exact sum_le_sum_of_subset_of_nonneg hmatch.1
      (fun e _ _ => inv_nonneg.mpr (weight_nonneg G e))
  have hW : (∑ e ∈ M, weight G e) ≤ (2*randic G)^2 :=
    (matching_weight_sum hmatch).trans (mass_bound G)
  have hsum := (weighted_cauchy hmatch.1).trans <|
    mul_le_mul hQ hW (sum_nonneg fun e _ => weight_nonneg G e)
      (mul_nonneg (by norm_num) (randic_nonneg G))
  have hm' := pow_le_pow_left₀ (by positivity) hm 2
  nlinarith [hm'.trans hsum]

theorem result (G : SimpleGraph (Fin n)) :
    (1/2 : ℝ) * (matchingNumber G : ℝ) ^ (2/3 : ℝ) ≤ randic G := by
  let x : ℝ := (matchingNumber G : ℝ)
  have hx : 0 ≤ x := by unfold x; positivity
  have he : (x ^ (2/3 : ℝ))^3 = x^2 := by
    rw [← Real.rpow_mul_natCast hx, show (2/3 : ℝ) * (3:ℕ) = (2:ℕ) by norm_num,
      Real.rpow_natCast]
  have hr := randic_nonneg G
  have h := cubic_bound G
  change x^2 ≤ 2*randic G^3 at h
  apply le_of_pow_le_pow_left₀ (n := 3) (by decide) hr
  rw [mul_pow, he]
  nlinarith [pow_nonneg hr 3]

end

end MatchingIndex

namespace OMA

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      c * (matchingNumber G : ℝ) ^ (2 / 3 : ℝ) ≤ randic G :=
  ⟨1/2, by norm_num, fun _ G => MatchingIndex.result G⟩

end OMA