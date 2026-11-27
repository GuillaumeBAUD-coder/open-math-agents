import FormalConjectures.ErdosProblems.«713»

-- Credit: @kcd1011
namespace OMA.R_Erdos713_erdos_713_parts_ii_R1

open Filter Asymptotics SimpleGraph
open scoped Classical

/-- Removing an isolated vertex or leaf either leaves a smaller admissible
forbidden graph within a linear error, or the extremal number is already linear-bounded. -/
def H1 : Prop :=
  ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.IsBipartite → 2 ≤ G.edgeFinset.card →
    (∃ v, G.degree v < 2) →
    (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) ∨
      ∃ (r : ℕ) (J : SimpleGraph (Fin r)), r < q ∧ J.IsBipartite ∧ 2 ≤ J.edgeFinset.card ∧
        (fun n : ℕ => (extremalNumber n J : ℝ) - (extremalNumber n G : ℝ))
          =O[atTop] (fun n : ℕ => (n : ℝ))

/-- Superlinear rationality for a graph of minimum degree at least two with the
fewest vertices realizing its exponent, allowing any positive leading constant. -/
def H2 : Prop :=
  ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.IsBipartite → 2 ≤ G.edgeFinset.card →
    (∀ v, 2 ≤ G.degree v) →
    ∀ α c : ℝ, α ∈ Set.Ioo 1 2 → 0 < c →
      (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop] (fun n : ℕ => c * (n : ℝ) ^ α) →
      (∀ (r : ℕ) (J : SimpleGraph (Fin r)), r < q → J.IsBipartite → 2 ≤ J.edgeFinset.card →
        ∀ d : ℝ, 0 < d → ¬ (fun n : ℕ => (extremalNumber n J : ℝ))
            ~[atTop] (fun n : ℕ => d * (n : ℝ) ^ α)) →
      α ∈ Set.range ((↑) : ℚ → ℝ)

theorem linear_isLittleO_power {α c : ℝ} (hα : 1 < α) (hc : 0 < c) :
    (fun n : ℕ => (n : ℝ)) =o[atTop] (fun n : ℕ => c * (n : ℝ) ^ α) := by
  apply IsLittleO.const_mul_right hc.ne'
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact_mod_cast hn
  apply (isLittleO_iff_tendsto' (hpos.mono fun n hn hzero =>
    ((Real.rpow_pos_of_pos hn α).ne' hzero).elim)).2
  apply ((tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp tendsto_natCast_atTop_atTop).congr'
  filter_upwards [hpos] with n hn
  change (n : ℝ) ^ (-(α - 1)) = (n : ℝ) / (n : ℝ) ^ α
  rw [neg_sub, Real.rpow_sub hn, Real.rpow_one]

theorem main : H1 → H2 → type_of% @Erdos713.erdos_713.parts.ii := by
  intro peel terminal q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro G hb he α c hα hc hG
    rcases eq_or_lt_of_le hα.1 with h | h
    · exact ⟨1, by simpa using h⟩
    have hlin := linear_isLittleO_power h hc
    by_cases smaller : ∃ (r : ℕ) (J : SimpleGraph (Fin r)), r < q ∧ J.IsBipartite ∧
        2 ≤ J.edgeFinset.card ∧ ∃ d : ℝ, 0 < d ∧
        (fun n : ℕ => (extremalNumber n J : ℝ)) ~[atTop] (fun n : ℕ => d * (n : ℝ) ^ α)
    · obtain ⟨r, J, hr, hJb, hJe, d, hd, hJ⟩ := smaller
      exact ih r hr J hJb hJe α d hα hd hJ
    · refine terminal q G hb he ?_ α c ⟨h, hα.2⟩ hc hG ?_
      · intro v
        by_contra! hv
        rcases peel q G hb he ⟨v, hv⟩ with hbound | hj
        · have hn : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≠ 0 := by
            filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
            exact_mod_cast hn.ne'
          exact hlin.not_isBigO hn.frequently (hG.isBigO_symm.trans hbound)
        · obtain ⟨r, J, hr, hJb, hJe, hdiff⟩ := hj
          apply smaller
          refine ⟨r, J, hr, hJb, hJe, c, hc, ?_⟩
          apply (hG.add_isLittleO (hdiff.trans_isLittleO hlin)).congr_left
          exact Eventually.of_forall fun n => by
            dsimp
            ring
      · intro r J hr hJb hJe d hd hJ
        exact smaller ⟨r, J, hr, hJb, hJe, d, hd, hJ⟩

end OMA.R_Erdos713_erdos_713_parts_ii_R1
