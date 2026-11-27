import FormalConjectures.ErdosProblems.«22»

/-! A single finite Bollobás–Erdős graph for each pair of error tolerances suffices.
Replace every vertex by the same number of independent twins and add isolated
vertices to reach the requested order. -/

open Filter SimpleGraph
open scoped Classical

namespace OMA.R_Erdos22_erdos_22_variants_bollobas_erdos_lower_R1

def H1 : Prop :=
  ∀ η δ : ℝ, 0 < η → 0 < δ → ∃ m : ℕ, 0 < m ∧ ∃ G : SimpleGraph (Fin m),
    G.CliqueFree 4 ∧ (G.indepNum : ℝ) ≤ δ * m ∧
      (1 / 8 - η) * (m : ℝ) ^ 2 ≤ G.edgeFinset.card

def H2 : Prop :=
  ∀ (m t r : ℕ) (G : SimpleGraph (Fin m)), G.CliqueFree 4 →
    ∃ H : SimpleGraph (Fin (m*t+r)), H.CliqueFree 4 ∧
      H.indepNum ≤ t * G.indepNum + r ∧ t^2 * G.edgeFinset.card ≤ H.edgeFinset.card

theorem main : H1 → H2 → type_of% @Erdos22.erdos_22.variants.bollobas_erdos_lower := by
  intro seed expand ε δ hε hδ
  let η := min (ε/2) (1/16)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηε : η ≤ ε/2 := min_le_left _ _
  have hηsmall : η ≤ 1/16 := min_le_right _ _
  obtain ⟨m,hm,G,hcl,ha,he⟩ := seed η (δ/2) hη (by positivity)
  obtain ⟨K,hK⟩ := exists_nat_ge (max (2*(m:ℝ)/δ) (4*(m:ℝ)/ε))
  filter_upwards [eventually_ge_atTop K] with n hn
  have hKn : (K:ℝ) ≤ n := by exact_mod_cast hn
  have hδn := (div_le_iff₀ hδ).mp ((le_max_left _ _).trans (hK.trans hKn))
  have hεn := (div_le_iff₀ hε).mp ((le_max_right _ _).trans (hK.trans hKn))
  let t := n / m
  let r := n % m
  have eqn : m*t+r = n := Nat.div_add_mod n m
  have hn' : (m:ℝ)*t+r = n := by exact_mod_cast eqn
  have hr : (r:ℝ) ≤ m := by exact_mod_cast (Nat.mod_lt n hm).le
  obtain ⟨H,hH,hA,hE⟩ := expand m t r G hcl
  suffices goal : ∃ J : SimpleGraph (Fin (m*t+r)), J.CliqueFree 4 ∧
        (J.indepNum:ℝ) ≤ δ*n ∧ (1/8-ε)*(n:ℝ)^2 ≤ J.edgeFinset.card by
    exact (congrArg (fun k : ℕ => ∃ J : SimpleGraph (Fin k), J.CliqueFree 4 ∧
      (J.indepNum:ℝ) ≤ δ*n ∧ (1/8-ε)*(n:ℝ)^2 ≤ J.edgeFinset.card) eqn).mp goal
  refine ⟨H,hH,?_,?_⟩
  · have ha' : (H.indepNum:ℝ) ≤ t*(G.indepNum:ℝ)+r := by exact_mod_cast hA
    have hmul := mul_le_mul_of_nonneg_left ha (show 0 ≤ (t:ℝ) by positivity)
    have hmt : (m:ℝ)*t ≤ n := by linarith [show 0 ≤ (r:ℝ) by positivity]
    have hd := mul_le_mul_of_nonneg_left hmt (show 0 ≤ δ/2 by positivity)
    nlinarith
  · let c := 1/8-η
    have hc : 0 ≤ c := by dsimp [c]; linarith
    have hc1 : c ≤ 1 := by dsimp [c]; linarith
    have hE' : (t:ℝ)^2 * G.edgeFinset.card ≤ H.edgeFinset.card := by exact_mod_cast hE
    have lifted := mul_le_mul_of_nonneg_left he (sq_nonneg (t:ℝ))
    have hsq : c*((m:ℝ)*t)^2 ≤ H.edgeFinset.card := by
      dsimp [c]
      nlinarith
    have hdif : (n:ℝ)^2 - ((m:ℝ)*t)^2 ≤ 2*r*n := by
      rw [← hn']
      nlinarith [sq_nonneg (r:ℝ)]
    have hdiff := mul_le_mul_of_nonneg_left hdif hc
    have hcap := mul_le_mul_of_nonneg_right hc1 (show 0 ≤ 2*(r:ℝ)*n by positivity)
    have hrem := mul_le_mul_of_nonneg_right hr (show 0 ≤ (n:ℝ) by positivity)
    have heps := mul_le_mul_of_nonneg_right hεn (show 0 ≤ (n:ℝ) by positivity)
    have herr := mul_le_mul_of_nonneg_right hηε (sq_nonneg (n:ℝ))
    dsimp [c] at hsq hdiff hcap
    nlinarith

end OMA.R_Erdos22_erdos_22_variants_bollobas_erdos_lower_R1
