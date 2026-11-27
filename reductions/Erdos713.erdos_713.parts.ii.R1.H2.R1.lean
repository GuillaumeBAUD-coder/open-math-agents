import OMAReductions.R_Erdos713_erdos_713_parts_ii_R1

/-! Split step H2 of the Erdős 713(ii) reduction into a combinatorial component bound (H1)
and the connected case (H2).

For a graph of minimum degree at least two with connected pieces `G₁`, `G₂`, a copy of `G₁`
can be found in any host with more than `ex(n, G₁) + ex(n, G₂) + q n` edges, its vertices'
incident edges deleted, and a copy of `G₂` found in what remains (all vertices of `G₂` have
positive degree, so they avoid the deleted vertices). Hence some piece has extremal number of
exact order `n ^ α`, and induction on the number of vertices reaches a connected graph.
Since pieces need not inherit an asymptotic `~ c n ^ α`, the connected case is stated with
the order condition `O(n ^ α)` and not `o(n ^ α)`, which is what the Erdős–Simonovits
rationality conjecture predicts. -/

-- Credit: @kcd1011
namespace OMA.R_Erdos713_erdos_713_parts_ii_R1_H2_R1

open Filter Asymptotics SimpleGraph
open scoped Classical

/-- A disconnected graph of minimum degree at least two splits into two smaller nonempty
pieces of minimum degree at least two, both contained in it, whose extremal numbers bound
its own up to a linear error. -/
def H1 : Prop :=
  ∀ (q : ℕ) (G : SimpleGraph (Fin q)), 0 < q → (∀ v, 2 ≤ G.degree v) → ¬ G.Connected →
    ∃ (r₁ r₂ : ℕ) (G₁ : SimpleGraph (Fin r₁)) (G₂ : SimpleGraph (Fin r₂)),
      0 < r₁ ∧ r₁ < q ∧ 0 < r₂ ∧ r₂ < q ∧ G₁ ⊑ G ∧ G₂ ⊑ G ∧
      (∀ v, 2 ≤ G₁.degree v) ∧ (∀ v, 2 ≤ G₂.degree v) ∧
      ∀ n : ℕ, extremalNumber n G ≤ extremalNumber n G₁ + extremalNumber n G₂ + q * n

/-- Connected case: a connected bipartite graph of minimum degree at least two whose
extremal number has exact order `n ^ α` (big-O but not little-o), `1 < α < 2`, has
rational `α`. -/
def H2 : Prop :=
  ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.Connected → G.IsBipartite →
    (∀ v, 2 ≤ G.degree v) → ∀ α : ℝ, α ∈ Set.Ioo 1 2 →
      (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) →
      ¬ (fun n : ℕ => (extremalNumber n G : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) →
      α ∈ Set.range ((↑) : ℚ → ℝ)

theorem lin_littleO {α : ℝ} (hα : 1 < α) :
    (fun n : ℕ => (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact_mod_cast hn
  apply (isLittleO_iff_tendsto' (hpos.mono fun n hn hzero =>
    ((Real.rpow_pos_of_pos hn α).ne' hzero).elim)).2
  apply ((tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp tendsto_natCast_atTop_atTop).congr'
  filter_upwards [hpos] with n hn
  change (n : ℝ) ^ (-(α - 1)) = (n : ℝ) / (n : ℝ) ^ α
  rw [neg_sub, Real.rpow_sub hn, Real.rpow_one]

theorem bigO_of_le {f g : ℕ → ℕ} (h : ∀ n, f n ≤ g n) :
    (fun n => (f n : ℝ)) =O[atTop] (fun n => (g n : ℝ)) :=
  IsBigO.of_bound 1 (Eventually.of_forall fun n => by
    simp only [Real.norm_natCast, one_mul]
    exact_mod_cast h n)

theorem aux (hA : H1) (hB : H2) {α : ℝ} (hα : α ∈ Set.Ioo 1 2) (q : ℕ) :
    ∀ G : SimpleGraph (Fin q), 0 < q → G.IsBipartite → (∀ v, 2 ≤ G.degree v) →
      (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) →
      ¬ (fun n : ℕ => (extremalNumber n G : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) →
      α ∈ Set.range ((↑) : ℚ → ℝ) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
  intro G hq hb hd hO hno
  by_cases hc : G.Connected
  · exact hB q G hc hb hd α hα hO hno
  obtain ⟨r₁, r₂, G₁, G₂, h1, h1q, h2, h2q, c1, c2, d1, d2, hle⟩ := hA q G hq hd hc
  have hb1 : G₁.IsBipartite := Colorable.of_hom c1.some.toHom hb
  have hb2 : G₂.IsBipartite := Colorable.of_hom c2.some.toHom hb
  have hO1 := (bigO_of_le (fun n => c1.extremalNumber_le (n := n))).trans hO
  have hO2 := (bigO_of_le (fun n => c2.extremalNumber_le (n := n))).trans hO
  by_cases ho1 : (fun n : ℕ => (extremalNumber n G₁ : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α)
  · by_cases ho2 : (fun n : ℕ => (extremalNumber n G₂ : ℝ)) =o[atTop]
        (fun n : ℕ => (n : ℝ) ^ α)
    · exfalso
      apply hno
      have hsum := (ho1.add ho2).add ((lin_littleO hα.1).const_mul_left (q : ℝ))
      refine IsBigO.trans_isLittleO ?_ hsum
      refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
      have h := hle n
      have h' : (extremalNumber n G : ℝ) ≤
          (extremalNumber n G₁ : ℝ) + extremalNumber n G₂ + q * n := by exact_mod_cast h
      simp only [Real.norm_natCast, one_mul]
      rw [Real.norm_of_nonneg (by positivity)]
      exact h'
    · exact ih r₂ h2q G₂ h2 hb2 d2 hO2 ho2
  · exact ih r₁ h1q G₁ h1 hb1 d1 hO1 ho1

theorem main : H1 → H2 → OMA.R_Erdos713_erdos_713_parts_ii_R1.H2 := by
  intro hA hB q G hb he hd α c hα hc hG _
  have hq : 0 < q := by
    obtain ⟨e, he'⟩ := Finset.card_pos.mp (by omega : 0 < G.edgeFinset.card)
    induction e using Sym2.ind with
    | h x y => exact Fin.pos x
  have hO : (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) :=
    hG.isBigO.trans (isBigO_const_mul_self c _ _)
  have hno : ¬ (fun n : ℕ => (extremalNumber n G : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ α) := by
    intro ho
    have h1 : (fun n : ℕ => c * (n : ℝ) ^ α) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) :=
      hG.symm.isBigO.trans_isLittleO ho
    have h2 : (fun n : ℕ => (n : ℝ) ^ α) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) :=
      (h1.const_mul_left c⁻¹).congr_left fun n => by field_simp
    have hne : ∃ᶠ n : ℕ in atTop, (n : ℝ) ^ α ≠ 0 :=
      ((eventually_gt_atTop (0 : ℕ)).mono fun n hn =>
        (Real.rpow_pos_of_pos (by exact_mod_cast hn) α).ne').frequently
    exact isLittleO_irrefl hne h2
  exact aux hA hB hα q G hq hb hd hO hno

end OMA.R_Erdos713_erdos_713_parts_ii_R1_H2_R1
