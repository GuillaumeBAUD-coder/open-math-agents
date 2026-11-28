import OMAReductions.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_tournamenton_R1

/-!
Step `SidorenkoConjecture.tournament_anti_sidorenko_trees_conjecture_tournamenton.R1.H1`:
every star satisfies the tournamenton anti-Sidorenko inequality.

For the star `K_{1,k}` relabel the vertices as `Fin (k+1)` with centre `0`, orient the first
`⌈k/2⌉` leaves out of the centre and the others into it. Splitting off the centre coordinate
(`measurePreserving_piFinSuccAbove`) and integrating each leaf separately
(`integral_fintype_prod_eq_prod`) turns the density into
`∫ d(x)^{⌈k/2⌉} (1 - d(x))^{⌊k/2⌋} dx`, where `d(x) = ∫ W(x, y) dy` and
`W(y, x) = 1 - W(x, y)`. Since `d (1 - d) ≤ 1/4` pointwise and `∫ d = 1/2`
(swap the order of integration and use `W(x, y) + W(y, x) = 1`), the density is at most `2^{-k}`.
-/

open MeasureTheory LimitObjects

namespace OMA.SidStarH1

open scoped Classical

open scoped Classical

/-- In- or out-orientation of leaf `t`. -/
def out (n : ℕ) (t : Fin n) : Prop := (t : ℕ) < (n + 1) / 2

/-- The balanced star orientation on `Fin (n+1)` with centre `0`. -/
def Dstar (n : ℕ) : Digraph (Fin (n + 1)) where
  Adj i j := (i = 0 ∧ ∃ t : Fin n, j = t.succ ∧ out n t) ∨ (j = 0 ∧ ∃ t : Fin n, i = t.succ ∧ ¬ out n t)

/-- The factor of leaf `t`. -/
noncomputable def g (n : ℕ) (W : Tournamenton) (t : Fin n) (s u : unitInterval) : ℝ :=
  if out n t then (W (s, u) : ℝ) else (W (u, s) : ℝ)

lemma integrand_eq (n : ℕ) (W : Tournamenton) (y : Fin (n + 1) → unitInterval) :
    tournamentonHomIntegrand (Dstar n) W y = ∏ t : Fin n, g n W t (y 0) (y t.succ) := by
  unfold tournamentonHomIntegrand
  symm
  refine Finset.prod_nbij (fun t => if out n t then ((0 : Fin (n+1)), t.succ) else (t.succ, 0))
    ?_ ?_ ?_ ?_
  · intro t _
    simp only [digraphEdgeFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h
    · exact Or.inl ⟨rfl, t, rfl, h⟩
    · exact Or.inr ⟨rfl, t, rfl, h⟩
  · intro a _ b _ hab
    simp only at hab
    split_ifs at hab with h1 h2 h2 <;> simp_all [Prod.ext_iff, Fin.succ_ne_zero]
  · intro p hp
    have hp' : (Dstar n).Adj p.1 p.2 := by
      simpa [digraphEdgeFinset] using hp
    simp only [Dstar] at hp'
    rcases hp' with ⟨h0, t, ht, ho⟩ | ⟨h0, t, ht, ho⟩
    · exact ⟨t, by simp, by simp [ho, Prod.ext_iff, h0, ht]⟩
    · exact ⟨t, by simp, by simp [ho, Prod.ext_iff, h0, ht]⟩
  · intro t _
    unfold g
    split_ifs <;> rfl


lemma W_meas (W : Tournamenton) : Measurable (fun p : unitInterval × unitInterval => (W p : ℝ)) :=
  measurable_subtype_coe.comp W.measurable

lemma g_meas (n : ℕ) (W : Tournamenton) (t : Fin n) :
    Measurable (fun p : unitInterval × unitInterval => g n W t p.1 p.2) := by
  unfold g
  split_ifs
  · exact W_meas W
  · exact (W_meas W).comp measurable_swap

lemma g_nonneg (n : ℕ) (W : Tournamenton) (t : Fin n) (s u : unitInterval) : 0 ≤ g n W t s u := by
  unfold g; split_ifs <;> exact unitInterval.nonneg _

lemma g_le_one (n : ℕ) (W : Tournamenton) (t : Fin n) (s u : unitInterval) : g n W t s u ≤ 1 := by
  unfold g; split_ifs <;> exact unitInterval.le_one _

lemma integral_split (n : ℕ) (W : Tournamenton) :
    ∫ y : Fin (n + 1) → unitInterval, ∏ t : Fin n, g n W t (y 0) (y t.succ)
        ∂(Measure.pi fun _ => volume) =
      ∫ s : unitInterval, ∏ t : Fin n, ∫ u : unitInterval, g n W t s u := by
  have hmp := measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => (volume : Measure unitInterval)) 0
  let G : unitInterval × (Fin n → unitInterval) → ℝ := fun p => ∏ t, g n W t p.1 (p.2 t)
  have hG : ∀ y : Fin (n + 1) → unitInterval, ∏ t : Fin n, g n W t (y 0) (y t.succ) =
      G (MeasurableEquiv.piFinSuccAbove (fun _ => unitInterval) 0 y) := by
    intro y
    simp [G, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.tail]
  have hGm : Measurable G := by
    refine Finset.measurable_prod _ (fun t _ => ?_)
    exact (g_meas n W t).comp (measurable_fst.prodMk ((measurable_pi_apply t).comp measurable_snd))
  have hGi : Integrable G ((volume : Measure unitInterval).prod
      (Measure.pi fun j : Fin n => (volume : Measure unitInterval))) := by
    refine Integrable.of_bound hGm.aestronglyMeasurable 1 (ae_of_all _ (fun p => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun t _ => g_nonneg n W t _ _)]
    exact Finset.prod_le_one (fun t _ => g_nonneg n W t _ _) (fun t _ => g_le_one n W t _ _)
  simp_rw [hG]
  rw [hmp.integral_comp' G]
  rw [integral_prod G hGi]
  congr 1
  funext s
  exact integral_fintype_prod_eq_prod (fun t u => g n W t s u)


/-- Out-degree function of a tournamenton. -/
noncomputable def d (W : Tournamenton) (s : unitInterval) : ℝ := ∫ u : unitInterval, (W (s, u) : ℝ)

lemma W_int_right (W : Tournamenton) (s : unitInterval) :
    Integrable (fun u : unitInterval => (W (s, u) : ℝ)) := by
  refine Integrable.of_bound ((W_meas W).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    1 (ae_of_all _ (fun u => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (unitInterval.nonneg _)]
  exact unitInterval.le_one _

lemma W_int_prod (W : Tournamenton) :
    Integrable (fun p : unitInterval × unitInterval => (W p : ℝ))
      ((volume : Measure unitInterval).prod volume) := by
  refine Integrable.of_bound (W_meas W).aestronglyMeasurable 1 (ae_of_all _ (fun u => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (unitInterval.nonneg _)]
  exact unitInterval.le_one _

lemma d_nonneg (W : Tournamenton) (s : unitInterval) : 0 ≤ d W s :=
  integral_nonneg (fun u => unitInterval.nonneg _)

lemma d_le_one (W : Tournamenton) (s : unitInterval) : d W s ≤ 1 := by
  have h : d W s ≤ ∫ _u : unitInterval, (1 : ℝ) :=
    integral_mono (W_int_right W s) (integrable_const 1) (fun u => unitInterval.le_one _)
  simpa using h

lemma inner_eq (n : ℕ) (W : Tournamenton) (t : Fin n) (s : unitInterval) :
    ∫ u : unitInterval, g n W t s u = if out n t then d W s else 1 - d W s := by
  unfold g d
  split_ifs
  · rfl
  · have h : ∀ u : unitInterval, (W (u, s) : ℝ) = 1 - (W (s, u) : ℝ) := fun u => by
      have := W.tournament s u; change (W (s, u) : ℝ) + (W (u, s) : ℝ) = 1 at this; linarith
    simp_rw [h]
    rw [integral_sub (integrable_const 1) (W_int_right W s)]
    simp

lemma integral_d (W : Tournamenton) : ∫ s : unitInterval, d W s = 1 / 2 := by
  have hint : Integrable (Function.uncurry fun s u : unitInterval => (W (u, s) : ℝ))
      ((volume : Measure unitInterval).prod volume) := by
    have := (W_int_prod W).swap
    exact this
  have hswap := integral_integral_swap hint
  have hsum : ∫ s : unitInterval, (d W s + ∫ u : unitInterval, (W (u, s) : ℝ)) = 1 := by
    have : ∀ s : unitInterval, d W s + ∫ u : unitInterval, (W (u, s) : ℝ) = 1 := by
      intro s
      unfold d
      rw [← integral_add (W_int_right W s)]
      · have : ∀ u : unitInterval, (W (s, u) : ℝ) + (W (u, s) : ℝ) = 1 := fun u => W.tournament s u
        simp [this]
      · refine Integrable.of_bound ((W_meas W).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
          1 (ae_of_all _ (fun u => ?_))
        rw [Real.norm_eq_abs, abs_of_nonneg (unitInterval.nonneg _)]
        exact unitInterval.le_one _
    simp [this]
  have hd_int : Integrable (fun s => d W s) := (W_int_prod W).integral_prod_left
  have h2_int : Integrable (fun s : unitInterval => ∫ u : unitInterval, (W (u, s) : ℝ)) :=
    hint.integral_prod_left
  rw [integral_add hd_int h2_int, hswap] at hsum
  unfold d at hsum ⊢
  linarith


lemma d_int (W : Tournamenton) : Integrable (fun s => d W s) := (W_int_prod W).integral_prod_left

lemma quarter (x : ℝ) (k : ℕ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ^ k * (1 - x) ^ k ≤ (1 / 4) ^ k := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg h0 (by linarith)) (by nlinarith [sq_nonneg (x - 1 / 2)]) k

theorem star_core (n : ℕ) (W : Tournamenton) :
    tournamentonHomDensity (Dstar n) W ≤ (1 / 2 : ℝ) ^ n := by
  unfold tournamentonHomDensity
  simp_rw [integrand_eq]
  rw [integral_split]
  simp_rw [inner_eq]
  have hprod : ∀ s, ∏ t : Fin n, (if out n t then d W s else 1 - d W s) =
      d W s ^ ((n + 1) / 2) * (1 - d W s) ^ (n / 2) := by
    intro s
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have ha : (Finset.univ.filter (fun t : Fin n => out n t)).card = (n + 1) / 2 := by
      calc _ = min n ((n + 1) / 2) := by unfold out; convert Fin.card_filter_val_lt (n := n)
        _ = _ := by omega
    have hb : (Finset.univ.filter (fun t : Fin n => ¬ out n t)).card = n / 2 := by
      have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun t : Fin n => out n t)
      rw [ha, Finset.card_univ, Fintype.card_fin] at this
      omega
    rw [ha, hb]
  simp_rw [hprod]
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have h1 : (n + 1) / 2 = k := by omega
    have h2 : n / 2 = k := by omega
    simp_rw [h1, h2]
    calc ∫ s : unitInterval, d W s ^ k * (1 - d W s) ^ k
        ≤ ∫ _ : unitInterval, ((1 : ℝ) / 4) ^ k :=
          integral_mono_of_nonneg
            (ae_of_all _ (fun s => mul_nonneg (pow_nonneg (d_nonneg W s) k)
              (pow_nonneg (by linarith [d_le_one W s]) k)))
            (integrable_const _)
            (ae_of_all _ (fun s => quarter _ k (d_nonneg W s) (d_le_one W s)))
      _ = (1 / 2 : ℝ) ^ n := by
          simp only [integral_const, probReal_univ, one_smul]
          rw [hk, pow_add, ← mul_pow]; norm_num
  · have h1 : (n + 1) / 2 = k + 1 := by omega
    have h2 : n / 2 = k := by omega
    simp_rw [h1, h2]
    calc ∫ s : unitInterval, d W s ^ (k + 1) * (1 - d W s) ^ k
        ≤ ∫ s : unitInterval, ((1 : ℝ) / 4) ^ k * d W s :=
          integral_mono_of_nonneg
            (ae_of_all _ (fun s => mul_nonneg (pow_nonneg (d_nonneg W s) _)
              (pow_nonneg (by linarith [d_le_one W s]) k)))
            ((d_int W).const_mul _)
            (ae_of_all _ (fun s => by
              have := quarter _ k (d_nonneg W s) (d_le_one W s)
              have h0 := d_nonneg W s
              calc d W s ^ (k + 1) * (1 - d W s) ^ k = (d W s ^ k * (1 - d W s) ^ k) * d W s := by
                    ring
                _ ≤ ((1 : ℝ) / 4) ^ k * d W s := mul_le_mul_of_nonneg_right this h0))
      _ = (1 / 2 : ℝ) ^ n := by
          rw [integral_const_mul, integral_d, hk, pow_succ, pow_mul]; norm_num


lemma Dstar_zero_succ (n : ℕ) (t : Fin n) : (Dstar n).Adj 0 t.succ ↔ out n t := by
  simp only [Dstar, Fin.succ_ne_zero, false_and, or_false, true_and, Fin.succ_inj,
    exists_eq_left']

lemma Dstar_succ_zero (n : ℕ) (t : Fin n) : (Dstar n).Adj t.succ 0 ↔ ¬ out n t := by
  simp only [Dstar, Fin.succ_ne_zero, false_and, false_or, true_and, Fin.succ_inj,
    exists_eq_left']

lemma Dstar_ne (n : ℕ) (i j : Fin (n + 1)) (h : (Dstar n).Adj i j) :
    (i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0) := by
  rcases h with ⟨h0, t, ht, _⟩ | ⟨h0, t, ht, _⟩
  · exact Or.inl ⟨h0, ht ▸ Fin.succ_ne_zero t⟩
  · exact Or.inr ⟨h0, ht ▸ Fin.succ_ne_zero t⟩

/-- The tournamenton density is invariant under relabelling the vertices. -/
lemma density_comap {V : Type*} {V' : Type*} [Fintype V] [DecidableEq V] [Fintype V']
    [DecidableEq V'] (e : V ≃ V') (D' : Digraph V') (D : Digraph V)
    (hD : ∀ u v, D.Adj u v ↔ D'.Adj (e u) (e v)) [DecidableRel D.Adj] [DecidableRel D'.Adj]
    (W : Tournamenton) : tournamentonHomDensity D W = tournamentonHomDensity D' W := by
  unfold tournamentonHomDensity
  have hmp := measurePreserving_piCongrLeft (fun _ : V' => (volume : Measure unitInterval)) e
  rw [← hmp.integral_comp' (tournamentonHomIntegrand D' W)]
  congr 1
  funext x
  unfold tournamentonHomIntegrand
  refine Finset.prod_nbij (fun p => (e p.1, e p.2)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [digraphEdgeFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact (hD _ _).1 hp
  · intro a _ b _ h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    exact Prod.ext h.1 h.2
  · intro q hq
    refine ⟨(e.symm q.1, e.symm q.2), ?_, by simp⟩
    simp only [digraphEdgeFinset, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hq ⊢
    rw [hD]
    simpa using hq
  · intro p _
    simp only [MeasurableEquiv.coe_piCongrLeft]
    rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]

theorem stars : OMA.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_tournamenton_R1.H1 := by
  intro V _ _ T _ hT hstar
  obtain ⟨c, hc⟩ := hstar
  have leaf : ∀ v, v ≠ c → T.Adj v c := by
    intro v hv
    obtain ⟨p⟩ := hT.connected.preconnected v c
    cases p with
    | nil => exact absurd rfl hv
    | cons h _ =>
      rcases hc _ _ h with h1 | h1
      · exact absurd h1 hv
      · exact h1 ▸ h
  have hadj : ∀ u v, T.Adj u v ↔ (u = c ∧ v ≠ c) ∨ (v = c ∧ u ≠ c) := by
    intro u v
    constructor
    · intro h
      rcases hc u v h with rfl | rfl
      · exact Or.inl ⟨rfl, (T.ne_of_adj h).symm⟩
      · exact Or.inr ⟨rfl, T.ne_of_adj h⟩
    · rintro (⟨rfl, hv⟩ | ⟨rfl, hu⟩)
      · exact (leaf v hv).symm
      · exact leaf u hu
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨c⟩
  set n := Fintype.card V - 1 with hn
  let e0 : V ≃ Fin (n + 1) := Fintype.equivFinOfCardEq (by omega)
  let e : V ≃ Fin (n + 1) := e0.trans (Equiv.swap (e0 c) 0)
  have hec : e c = 0 := by simp [e]
  have he0 : ∀ u, e u = 0 ↔ u = c := fun u => by rw [← hec]; exact e.injective.eq_iff
  refine ⟨⟨fun u v => (Dstar n).Adj (e u) (e v)⟩, ⟨?_, ?_⟩, ?_⟩
  · intro u v h
    rw [hadj]
    rcases Dstar_ne n _ _ h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨(he0 u).1 h1, fun h => h2 ((he0 v).2 h)⟩
    · exact Or.inr ⟨(he0 v).1 h1, fun h => h2 ((he0 u).2 h)⟩
  · intro u v h
    show (Dstar n).Adj (e u) (e v) ↔ ¬ (Dstar n).Adj (e v) (e u)
    rcases (hadj u v).1 h with ⟨rfl, hv⟩ | ⟨rfl, hu⟩
    · obtain ⟨t, ht⟩ := Fin.exists_succ_eq.2 (fun h => hv ((he0 v).1 h))
      rw [hec, ← ht, Dstar_zero_succ, Dstar_succ_zero, not_not]
    · obtain ⟨t, ht⟩ := Fin.exists_succ_eq.2 (fun h => hu ((he0 u).1 h))
      rw [hec, ← ht, Dstar_zero_succ, Dstar_succ_zero]
  · intro W
    rw [density_comap e (Dstar n) _ (fun _ _ => Iff.rfl) W]
    have hcard : T.edgeFinset.card = n := by have := hT.card_edgeFinset; omega
    rw [hcard]
    exact star_core n W

end OMA.SidStarH1

theorem OMA.solution :
    OMA.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_tournamenton_R1.H1 :=
  OMA.SidStarH1.stars
