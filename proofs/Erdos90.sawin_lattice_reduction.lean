import FormalConjectures.ErdosProblems.«90»
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Proof of Sawin Lemma 2: lattice geometry of unit distances
-/

open MeasureTheory
open scoped EuclideanGeometry

section OMASawin

lemma oma_nontrivial_euclid {d : ℕ} (hd : 1 ≤ d) :
    Nontrivial (EuclideanSpace ℝ (Fin (2 * d))) := by
  refine ⟨⟨0, WithLp.toLp 2 (fun _ => (1 : ℝ)), fun h => ?_⟩⟩
  have hi : (0 : ℝ) = 1 := congr_fun (congrArg WithLp.ofLp h) ⟨0, by omega⟩
  norm_num at hi

lemma oma_vol_ball {d : ℕ} (hd : 1 ≤ d) (x : EuclideanSpace ℝ (Fin (2 * d)))
    {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.ball x r) =
      r ^ (2 * d) * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * d))) 1) := by
  have := oma_nontrivial_euclid hd
  rw [← Measure.addHaar_real_closedBall_eq_addHaar_real_ball volume x r,
    Measure.addHaar_real_closedBall volume x hr, finrank_euclideanSpace_fin]

lemma oma_vol_unit_ball_pos (d : ℕ) :
    0 < volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * d))) 1) := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos
    (ne_of_gt (Metric.measure_ball_pos volume 0 zero_lt_one))
    (ne_of_lt measure_ball_lt_top)

lemma oma_lattice_finset_card_bound {d : ℕ} (hd : 1 ≤ d)
    {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * d)))}
    {ρ : ℝ} (hρ : 0 < ρ)
    (hΛ : ∀ v : Λ, v ≠ 0 → ρ ≤ ‖(v : EuclideanSpace ℝ (Fin (2 * d)))‖)
    (w : EuclideanSpace ℝ (Fin (2 * d))) {r : ℝ} (hr : 0 < r)
    (T : Finset Λ)
    (hT : ∀ v ∈ T, (v : EuclideanSpace ℝ (Fin (2 * d))) ∈ Metric.ball w r) :
    (T.card : ℝ) ≤ (2 * r / ρ + 1) ^ (2 * d) := by
  let E := EuclideanSpace ℝ (Fin (2 * d))
  have hV1 : 0 < volume.real (Metric.ball (0 : E) 1) := oma_vol_unit_ball_pos d
  have hρ2 : 0 < ρ / 2 := by linarith
  have hdisj : (T : Set Λ).PairwiseDisjoint
      (fun v : Λ => Metric.ball (v : E) (ρ / 2)) := by
    intro v₁ _ v₂ _ hne
    dsimp [Function.onFun]
    apply Metric.ball_disjoint_ball
    have hsub_ne : v₁ - v₂ ≠ 0 := sub_ne_zero.2 hne
    have hnorm := hΛ (v₁ - v₂) hsub_ne
    rw [dist_eq_norm]
    have hcoe : ((v₁ - v₂ : Λ) : E) = (v₁ : E) - (v₂ : E) := rfl
    linarith [hcoe ▸ hnorm]
  have hsub_big : (⋃ v ∈ T, Metric.ball (v : E) (ρ / 2)) ⊆ Metric.ball w (r + ρ / 2) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    rcases hz with ⟨v, hvT, hzv⟩
    have hvw : dist (v : E) w < r := Metric.mem_ball.1 (hT v hvT)
    have hzv' : dist z (v : E) < ρ / 2 := Metric.mem_ball.1 hzv
    rw [Metric.mem_ball]
    linarith [dist_triangle z (v : E) w]
  have hmeas_union : volume.real (⋃ v ∈ T, Metric.ball (v : E) (ρ / 2)) =
      ∑ v ∈ T, volume.real (Metric.ball (v : E) (ρ / 2)) := by
    refine measureReal_biUnion_finset hdisj (fun _ _ => measurableSet_ball) ?_
    intro _ _; exact ne_of_lt measure_ball_lt_top
  have hmono : volume.real (⋃ v ∈ T, Metric.ball (v : E) (ρ / 2)) ≤
      volume.real (Metric.ball w (r + ρ / 2)) :=
    measureReal_mono hsub_big (ne_of_lt measure_ball_lt_top)
  rw [hmeas_union, oma_vol_ball hd w (by positivity)] at hmono
  have hsum_eq : (∑ v ∈ T, volume.real (Metric.ball (v : E) (ρ / 2))) =
      (T.card : ℝ) * ((ρ / 2) ^ (2 * d) * volume.real (Metric.ball (0 : E) 1)) := by
    have hconst : ∀ v ∈ T, volume.real (Metric.ball (v : E) (ρ / 2)) =
        (ρ / 2) ^ (2 * d) * volume.real (Metric.ball (0 : E) 1) :=
      fun v _ => oma_vol_ball hd (v : E) (by positivity)
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  rw [hsum_eq] at hmono
  have hpos_denom : 0 < (ρ / 2) ^ (2 * d) * volume.real (Metric.ball (0 : E) 1) := by positivity
  have hle1 : (T.card : ℝ) * ((ρ / 2) ^ (2 * d) * volume.real (Metric.ball (0 : E) 1)) ≤
      (2 * r / ρ + 1) ^ (2 * d) * ((ρ / 2) ^ (2 * d) * volume.real (Metric.ball (0 : E) 1)) := by
    have hbase : r + ρ / 2 = (2 * r / ρ + 1) * (ρ / 2) := by field_simp
    rw [hbase, mul_pow] at hmono
    linarith
  exact le_of_mul_le_mul_right hle1 hpos_denom

lemma oma_lattice_ball_finite {d : ℕ} (hd : 1 ≤ d)
    {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * d)))}
    {ρ : ℝ} (hρ : 0 < ρ)
    (hΛ : ∀ v : Λ, v ≠ 0 → ρ ≤ ‖(v : EuclideanSpace ℝ (Fin (2 * d)))‖)
    (w : EuclideanSpace ℝ (Fin (2 * d))) {r : ℝ} (hr : 0 < r) :
    {v : Λ | (v : EuclideanSpace ℝ (Fin (2 * d))) ∈ Metric.ball w r}.Finite := by
  by_contra hinf
  have hinf' : {v : Λ | (v : EuclideanSpace ℝ (Fin (2 * d))) ∈ Metric.ball w r}.Infinite := hinf
  set B := (2 * r / ρ + 1) ^ (2 * d)
  have hB_nonneg : 0 ≤ B := by positivity
  obtain ⟨T, hTsub, hTcard⟩ := hinf'.exists_subset_card_eq (Nat.floor B + 1)
  have hle := oma_lattice_finset_card_bound hd hρ hΛ w hr T (fun v hv => hTsub hv)
  have hgt : B < (T.card : ℝ) := by
    rw [hTcard]
    push_cast
    exact Nat.lt_floor_add_one B
  linarith

noncomputable def omaLatBall {d : ℕ} (hd : 1 ≤ d)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * d))))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hΛ : ∀ v : Λ, v ≠ 0 → ρ ≤ ‖(v : EuclideanSpace ℝ (Fin (2 * d)))‖)
    (w : EuclideanSpace ℝ (Fin (2 * d))) {r : ℝ} (hr : 0 < r) : Finset Λ :=
  (oma_lattice_ball_finite hd hρ hΛ w hr).toFinset

lemma mem_omaLatBall {d : ℕ} (hd : 1 ≤ d)
    {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * d)))}
    {ρ : ℝ} (hρ : 0 < ρ)
    (hΛ : ∀ v : Λ, v ≠ 0 → ρ ≤ ‖(v : EuclideanSpace ℝ (Fin (2 * d)))‖)
    {w : EuclideanSpace ℝ (Fin (2 * d))} {r : ℝ} (hr : 0 < r) {v : Λ} :
    v ∈ omaLatBall hd Λ hρ hΛ w hr ↔
      (v : EuclideanSpace ℝ (Fin (2 * d))) ∈ Metric.ball w r := by
  simp [omaLatBall]

lemma oma_ordered_unit_le_two_unitDistNum (U : Finset ℝ²) :
    (U.offDiag.filter (fun p : ℝ² × ℝ² => dist p.1 p.2 = 1)).card ≤
      2 * unitDistNum U := by
  classical
  let F_ord := U.offDiag.filter (fun p : ℝ² × ℝ² => dist p.1 p.2 = 1)
  let F_sym := U.sym2.filter (fun q : Sym2 ℝ² => dist q.out.1 q.out.2 = 1)
  have hsub : F_ord ⊆ F_sym.biUnion (fun q => ({q.out, q.out.swap} : Finset (ℝ² × ℝ²))) := by
    intro p hp
    rcases Finset.mem_filter.1 hp with ⟨hp_off, hp_dist⟩
    rcases Finset.mem_offDiag.1 hp_off with ⟨hp1, hp2, _⟩
    let q : Sym2 ℝ² := s(p.1, p.2)
    have hq_sym2 : q ∈ U.sym2 := by
      rw [Finset.mem_sym2_iff]
      intro a ha
      rcases Sym2.mem_iff.1 ha with rfl | rfl <;> assumption
    have hq_out_eq : s(q.out.1, q.out.2) = s(p.1, p.2) := Quot.out_eq q
    have hcases := Sym2.eq_iff.1 hq_out_eq
    have hq_dist : dist q.out.1 q.out.2 = 1 := by
      rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hp_dist
      · rw [h1, h2, dist_comm]; exact hp_dist
    have hqF : q ∈ F_sym := Finset.mem_filter.2 ⟨hq_sym2, hq_dist⟩
    refine Finset.mem_biUnion.2 ⟨q, hqF, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact Prod.ext h1.symm h2.symm
    · right; exact Prod.ext h2.symm h1.symm
  have hcard1 : F_ord.card ≤ (F_sym.biUnion (fun q => ({q.out, q.out.swap} : Finset (ℝ² × ℝ²)))).card :=
    Finset.card_le_card hsub
  have hcard2 : (F_sym.biUnion (fun q => ({q.out, q.out.swap} : Finset (ℝ² × ℝ²)))).card ≤
      ∑ q ∈ F_sym, ({q.out, q.out.swap} : Finset (ℝ² × ℝ²)).card :=
    Finset.card_biUnion_le
  have hcard3 : ∑ q ∈ F_sym, ({q.out, q.out.swap} : Finset (ℝ² × ℝ²)).card ≤ ∑ _q ∈ F_sym, 2 := by
    refine Finset.sum_le_sum fun q _ => ?_
    exact le_trans (Finset.card_insert_le _ _) (by simp)
  have hsym_eq : F_sym.card = unitDistNum U := rfl
  simp only [Finset.sum_const, smul_eq_mul] at hcard3
  dsimp [F_ord] at hcard1
  rw [hsym_eq] at hcard3
  linarith

lemma oma_integrableOn_ind {n : ℕ} {s t : Set (EuclideanSpace ℝ (Fin n))}
    (hs : volume s ≠ ⊤) (ht : MeasurableSet t) :
    IntegrableOn (t.indicator (fun _ => (1 : ℝ))) s volume :=
  (integrableOn_const (C := (1 : ℝ)) hs (by simp)).indicator ht

lemma oma_setIntegral_ball_indicator {n : ℕ} (s t : Set (EuclideanSpace ℝ (Fin n)))
    (ht : MeasurableSet t) :
    ∫ x in s, t.indicator (fun _ => (1 : ℝ)) x = volume.real (s ∩ t) := by
  rw [setIntegral_indicator ht, setIntegral_const, smul_eq_mul, mul_one]

lemma oma_exp_beats_poly {α A B : ℝ} (hα : 0 < α) (hA : 0 ≤ A) (hB : 0 ≤ B) (D : ℕ)
    (hle : ∀ k : ℕ, (1 + α) ^ k ≤ (A * (k : ℝ) + B) ^ D) : False := by
  set C := A * ((D + 1 : ℕ) : ℝ) + B + 1
  have hC_pos : 0 < C := by positivity
  obtain ⟨m_nat, hm_nat⟩ := exists_nat_gt (max 1 ((C / α) ^ D / α))
  have hm_ge1 : (1 : ℝ) < (m_nat : ℝ) := lt_of_le_of_lt (le_max_left _ _) hm_nat
  have hm_pos : 0 < (m_nat : ℝ) := by linarith
  have hm_thresh : (C / α) ^ D / α < (m_nat : ℝ) := lt_of_le_of_lt (le_max_right _ _) hm_nat
  set k := (D + 1) * m_nat
  have hk_cast : (k : ℝ) = ((D + 1 : ℕ) : ℝ) * (m_nat : ℝ) := by dsimp [k]; push_cast; ring
  have h1 := hle k
  have hbern : ((m_nat : ℝ) * α) ^ (D + 1) ≤ (1 + α) ^ k := by
    have hb0 : 1 + (m_nat : ℝ) * α ≤ (1 + α) ^ m_nat :=
      one_add_mul_le_pow (by linarith) m_nat
    have hb1 : (m_nat : ℝ) * α ≤ (1 + α) ^ m_nat := by linarith
    have hpow := pow_le_pow_left₀ (by positivity) hb1 (D + 1)
    rwa [← pow_mul, mul_comm m_nat (D + 1)] at hpow
  have hupper : (A * (k : ℝ) + B) ^ D ≤ (C * (m_nat : ℝ)) ^ D := by
    refine pow_le_pow_left₀ (by positivity) ?_ D
    rw [hk_cast]
    dsimp [C]
    nlinarith
  have hcomb : ((m_nat : ℝ) * α) ^ (D + 1) ≤ (C * (m_nat : ℝ)) ^ D :=
    le_trans hbern (le_trans h1 hupper)
  have hpos_mD : 0 < (m_nat : ℝ) ^ D := by positivity
  have hpos_αD : 0 < α ^ D := by positivity
  have hlhs : ((m_nat : ℝ) * α) ^ (D + 1) = ((m_nat : ℝ) * α) * (α ^ D * (m_nat : ℝ) ^ D) := by
    rw [pow_succ]; ring
  have hrhs : (C * (m_nat : ℝ)) ^ D = C ^ D * (m_nat : ℝ) ^ D := by ring
  rw [hlhs, hrhs] at hcomb
  have hcancel_m : ((m_nat : ℝ) * α) * α ^ D ≤ C ^ D :=
    le_of_mul_le_mul_right (by linarith) hpos_mD
  have hstrict : C ^ D < ((m_nat : ℝ) * α) * α ^ D := by
    have hmul1 : (C / α) ^ D < (m_nat : ℝ) * α := (div_lt_iff₀ hα).1 hm_thresh
    have hmul2 := mul_lt_mul_of_pos_right hmul1 hpos_αD
    rwa [div_pow, div_mul_cancel₀ _ (ne_of_gt hpos_αD)] at hmul2
  linarith

end OMASawin

theorem OMA.solution : type_of% @Erdos90.sawin_lattice_reduction := by
  intro d hd R hR Λ ρ hρ hΛ π hπ S hS_norm hS_proj
  classical
  let E := EuclideanSpace ℝ (Fin (2 * d))
  have hRm1 : 0 < R - 1 := by linarith
  have hR_pos : 0 < R := by linarith
  set c := ((1 : ℝ) - 1 / R) ^ (2 * d)
  have hc_eq : c = ((R - 1) / R) ^ (2 * d) := by
    dsimp [c]; congr 1; field_simp
  have hc_pos : 0 < c := by rw [hc_eq]; positivity
  have hexists_w : ∃ w : E,
      1 ≤ (omaLatBall hd Λ hρ hΛ w hR_pos).card ∧
      c * ((omaLatBall hd Λ hρ hΛ w hR_pos).card : ℝ) ≤
        ((omaLatBall hd Λ hρ hΛ w hRm1).card : ℝ) := by
    by_contra hno
    push Not at hno
    set K := Nat.floor ((2 * R / ρ + 1) ^ (2 * d))
    have hcard_le_K : ∀ w : E, (omaLatBall hd Λ hρ hΛ w hR_pos).card ≤ K := by
      intro w
      exact Nat.le_floor (oma_lattice_finset_card_bound hd hρ hΛ w hR_pos _
        (fun v hv => (mem_omaLatBall hd hρ hΛ hR_pos).1 hv))
    have hsub_in : ∀ w : E, omaLatBall hd Λ hρ hΛ w hRm1 ⊆ omaLatBall hd Λ hρ hΛ w hR_pos := by
      intro w v hv
      rw [mem_omaLatBall hd hρ hΛ hRm1] at hv
      rw [mem_omaLatBall hd hρ hΛ hR_pos]
      exact Metric.ball_subset_ball (by linarith) hv
    let P : Finset (ℕ × ℕ) :=
      ((Finset.range (K + 1)) ×ˢ (Finset.Icc 1 K)).filter
        (fun ab : ℕ × ℕ => (ab.1 : ℝ) < c * (ab.2 : ℝ))
    have h0_mem_R : (0 : Λ) ∈ omaLatBall hd Λ hρ hΛ 0 hR_pos := by
      rw [mem_omaLatBall hd hρ hΛ hR_pos]; simp [hR_pos]
    have h0_card_ge1 : 1 ≤ (omaLatBall hd Λ hρ hΛ 0 hR_pos).card :=
      Finset.card_pos.2 ⟨0, h0_mem_R⟩
    have hP_nonempty : P.Nonempty := by
      refine ⟨((omaLatBall hd Λ hρ hΛ 0 hRm1).card, (omaLatBall hd Λ hρ hΛ 0 hR_pos).card), ?_⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨?_, ?_⟩, hno 0 h0_card_ge1⟩
      · have hle := le_trans (Finset.card_le_card (hsub_in 0)) (hcard_le_K 0)
        exact Finset.mem_range.2 (by omega)
      · exact Finset.mem_Icc.2 ⟨h0_card_ge1, hcard_le_K 0⟩
    let gaps : Finset ℝ := P.image (fun ab : ℕ × ℕ => c * (ab.2 : ℝ) - (ab.1 : ℝ))
    have hgaps_ne : gaps.Nonempty := hP_nonempty.image _
    set ε := gaps.min' hgaps_ne
    have hε_pos : 0 < ε := by
      have hmem_min : ε ∈ gaps := Finset.min'_mem gaps hgaps_ne
      obtain ⟨ab, habP, heq⟩ := Finset.mem_image.1 hmem_min
      have hlt := (Finset.mem_filter.1 habP).2
      linarith
    have hgap_all : ∀ w : E,
        ((omaLatBall hd Λ hρ hΛ w hRm1).card : ℝ) -
          c * ((omaLatBall hd Λ hρ hΛ w hR_pos).card : ℝ) ≤ 0 := by
      intro w
      by_cases h1 : 1 ≤ (omaLatBall hd Λ hρ hΛ w hR_pos).card
      · linarith [hno w h1]
      · have h0b : (omaLatBall hd Λ hρ hΛ w hR_pos).card = 0 := by omega
        have h0a : (omaLatBall hd Λ hρ hΛ w hRm1).card = 0 := by
          have := Finset.card_le_card (hsub_in w); omega
        simp [h0a, h0b]
    have hgap_neg : ∀ w : E, 1 ≤ (omaLatBall hd Λ hρ hΛ w hR_pos).card →
        ((omaLatBall hd Λ hρ hΛ w hRm1).card : ℝ) -
          c * ((omaLatBall hd Λ hρ hΛ w hR_pos).card : ℝ) ≤ -ε := by
      intro w h1
      have habP : ((omaLatBall hd Λ hρ hΛ w hRm1).card, (omaLatBall hd Λ hρ hΛ w hR_pos).card) ∈ P := by
        refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨?_, ?_⟩, hno w h1⟩
        · have hle := le_trans (Finset.card_le_card (hsub_in w)) (hcard_le_K w)
          exact Finset.mem_range.2 (by omega)
        · exact Finset.mem_Icc.2 ⟨h1, hcard_le_K w⟩
      have hmem_g : c * ((omaLatBall hd Λ hρ hΛ w hR_pos).card : ℝ) -
          ((omaLatBall hd Λ hρ hΛ w hRm1).card : ℝ) ∈ gaps :=
        Finset.mem_image.2 ⟨_, habP, rfl⟩
      have hle_min := Finset.min'_le gaps _ hmem_g
      linarith
    set δ := min (R / 2) (ρ / 2)
    have hδ_pos : 0 < δ := by positivity
    have hV1 : 0 < volume.real (Metric.ball (0 : E) 1) := oma_vol_unit_ball_pos d
    set α := ε * δ ^ (2 * d) / (R - 1) ^ (2 * d)
    have hα_pos : 0 < α := by positivity
    have hstep : ∀ {r_in : ℝ} (hr_in : 0 < r_in),
        (1 + α) * ((omaLatBall hd Λ hρ hΛ 0 hr_in).card : ℝ) ≤
          ((omaLatBall hd Λ hρ hΛ 0 (by linarith : 0 < r_in + 2 * R)).card : ℝ) := by
      intro r_in hr_in
      set M := r_in + R
      have hM_pos : 0 < M := by linarith
      have hr_out : 0 < r_in + 2 * R := by linarith
      let G_in := omaLatBall hd Λ hρ hΛ 0 hr_in
      let G_out := omaLatBall hd Λ hρ hΛ 0 hr_out
      have hGin_sub : G_in ⊆ G_out := by
        intro v hv
        rw [mem_omaLatBall hd hρ hΛ hr_in] at hv
        rw [mem_omaLatBall hd hρ hΛ hr_out]
        exact Metric.ball_subset_ball (by linarith) hv
      let BM : Set E := Metric.ball 0 M
      have hBM_meas : MeasurableSet BM := measurableSet_ball
      have hBM_fin : volume BM ≠ ⊤ := ne_of_lt measure_ball_lt_top
      let term : Λ → E → ℝ := fun v w =>
        (Metric.ball (v : E) (R - 1)).indicator (fun _ => (1 : ℝ)) w -
          c * (Metric.ball (v : E) R).indicator (fun _ => (1 : ℝ)) w
      have hterm_int : ∀ v ∈ G_out, IntegrableOn (term v) BM volume := by
        intro v _
        exact (oma_integrableOn_ind hBM_fin measurableSet_ball).sub
          ((oma_integrableOn_ind hBM_fin measurableSet_ball).const_mul c)
      have hpointwise_eq : ∀ w ∈ BM,
          (∑ v ∈ G_out, term v w) =
            ((omaLatBall hd Λ hρ hΛ w hRm1).card : ℝ) -
              c * ((omaLatBall hd Λ hρ hΛ w hR_pos).card : ℝ) := by
        intro w hw
        have hcount : ∀ (r : ℝ) (hr : 0 < r), r ≤ R →
            (∑ v ∈ G_out, (Metric.ball (v : E) r).indicator (fun _ => (1 : ℝ)) w) =
              ((omaLatBall hd Λ hρ hΛ w hr).card : ℝ) := by
          intro r hr hrR
          have hsub_w : omaLatBall hd Λ hρ hΛ w hr ⊆ G_out := by
            intro v hv
            rw [mem_omaLatBall hd hρ hΛ hr] at hv
            rw [mem_omaLatBall hd hρ hΛ hr_out]
            have hvw : dist (v : E) w < r := Metric.mem_ball.1 hv
            have hw0 : dist w 0 < M := Metric.mem_ball.1 hw
            rw [Metric.mem_ball]
            linarith [dist_triangle (v : E) w 0]
          rw [← Finset.sum_subset hsub_w]
          · have h1 : ∀ v ∈ omaLatBall hd Λ hρ hΛ w hr,
                (Metric.ball (v : E) r).indicator (fun _ => (1 : ℝ)) w = 1 := by
              intro v hv
              have hv_ball : w ∈ Metric.ball (v : E) r := by
                rw [Metric.mem_ball, dist_comm]
                exact Metric.mem_ball.1 ((mem_omaLatBall hd hρ hΛ hr).1 hv)
              exact Set.indicator_of_mem hv_ball _
            rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
          · intro v _ hv_not
            have hw_not : w ∉ Metric.ball (v : E) r := by
              intro hw_in
              apply hv_not
              rw [mem_omaLatBall hd hρ hΛ hr, Metric.mem_ball, dist_comm]
              exact Metric.mem_ball.1 hw_in
            exact Set.indicator_of_notMem hw_not _
        dsimp [term]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
          hcount (R - 1) hRm1 (by linarith), hcount R hR_pos (le_refl R)]
      let Uδ : Set E := ⋃ v ∈ G_in, Metric.ball (v : E) δ
      have hUδ_meas : MeasurableSet Uδ :=
        Finset.measurableSet_biUnion G_in (fun _ _ => measurableSet_ball)
      have hUδ_sub : Uδ ⊆ BM := by
        intro w hw
        simp only [Uδ, Set.mem_iUnion] at hw
        rcases hw with ⟨v, hv_in, hw_v⟩
        have hv0 : dist (v : E) 0 < r_in :=
          Metric.mem_ball.1 ((mem_omaLatBall hd hρ hΛ hr_in).1 hv_in)
        have hwv : dist w (v : E) < δ := Metric.mem_ball.1 hw_v
        have hδR : δ ≤ R / 2 := min_le_left _ _
        rw [Metric.mem_ball]
        linarith [dist_triangle w (v : E) 0]
      have hpointwise_upper : ∀ w ∈ BM,
          (∑ v ∈ G_out, term v w) ≤ -ε * Uδ.indicator (fun _ => (1 : ℝ)) w := by
        intro w hw
        rw [hpointwise_eq w hw]
        by_cases hwU : w ∈ Uδ
        · rw [Set.indicator_of_mem hwU, mul_one]
          simp only [Uδ, Set.mem_iUnion] at hwU
          rcases hwU with ⟨v, _, hw_v⟩
          have hv_mem : v ∈ omaLatBall hd Λ hρ hΛ w hR_pos := by
            rw [mem_omaLatBall hd hρ hΛ hR_pos, Metric.mem_ball, dist_comm]
            have hwv : dist w (v : E) < δ := Metric.mem_ball.1 hw_v
            have hδR : δ ≤ R / 2 := min_le_left _ _
            linarith
          exact hgap_neg w (Finset.card_pos.2 ⟨v, hv_mem⟩)
        · rw [Set.indicator_of_notMem hwU, mul_zero]
          exact hgap_all w
      have hint_lhs : IntegrableOn (fun w => ∑ v ∈ G_out, term v w) BM volume :=
        integrable_finsetSum G_out hterm_int
      have hint_rhs : IntegrableOn (fun w => -ε * Uδ.indicator (fun _ => (1 : ℝ)) w) BM volume :=
        (oma_integrableOn_ind hBM_fin hUδ_meas).const_mul (-ε)
      have hint_le := setIntegral_mono_on hint_lhs hint_rhs hBM_meas hpointwise_upper
      have hint_rhs_eval : (∫ w in BM, -ε * Uδ.indicator (fun _ => (1 : ℝ)) w) =
          -(ε * δ ^ (2 * d) * volume.real (Metric.ball (0 : E) 1)) * (G_in.card : ℝ) := by
        rw [MeasureTheory.integral_const_mul, oma_setIntegral_ball_indicator BM Uδ hUδ_meas,
          Set.inter_eq_right.2 hUδ_sub]
        have hdisj : (G_in : Set Λ).PairwiseDisjoint (fun v : Λ => Metric.ball (v : E) δ) := by
          intro v₁ _ v₂ _ hne
          dsimp [Function.onFun]
          apply Metric.ball_disjoint_ball
          have hnorm := hΛ (v₁ - v₂) (sub_ne_zero.2 hne)
          have hδρ : δ ≤ ρ / 2 := min_le_right _ _
          rw [dist_eq_norm]
          have hcoe : ((v₁ - v₂ : Λ) : E) = (v₁ : E) - (v₂ : E) := rfl
          linarith [hcoe ▸ hnorm]
        have hvol_Uδ : volume.real Uδ =
            (G_in.card : ℝ) * (δ ^ (2 * d) * volume.real (Metric.ball (0 : E) 1)) := by
          rw [measureReal_biUnion_finset hdisj (fun _ _ => measurableSet_ball)
            (fun _ _ => ne_of_lt measure_ball_lt_top)]
          have hc_vol : ∀ v ∈ G_in, volume.real (Metric.ball (v : E) δ) =
              δ ^ (2 * d) * volume.real (Metric.ball (0 : E) 1) :=
            fun v _ => oma_vol_ball hd (v : E) (le_of_lt hδ_pos)
          rw [Finset.sum_congr rfl hc_vol, Finset.sum_const, nsmul_eq_mul]
        rw [hvol_Uδ]; ring
      have hint_lhs_eval : -((R - 1) ^ (2 * d) * volume.real (Metric.ball (0 : E) 1)) *
            ((G_out.card : ℝ) - (G_in.card : ℝ)) ≤
          (∫ w in BM, ∑ v ∈ G_out, term v w) := by
        rw [MeasureTheory.integral_finsetSum G_out hterm_int]
        have hterm_val : ∀ v ∈ G_out,
            (∫ w in BM, term v w) =
              volume.real (BM ∩ Metric.ball (v : E) (R - 1)) -
                c * volume.real (BM ∩ Metric.ball (v : E) R) := by
          intro v _
          dsimp [term]
          have hi1 : Integrable ((Metric.ball (v : E) (R - 1)).indicator (fun _ => (1 : ℝ)))
              (volume.restrict BM) := oma_integrableOn_ind hBM_fin measurableSet_ball
          have hi2 : Integrable (fun w => c * (Metric.ball (v : E) R).indicator (fun _ => (1 : ℝ)) w)
              (volume.restrict BM) := (oma_integrableOn_ind hBM_fin measurableSet_ball).const_mul c
          rw [MeasureTheory.integral_sub hi1 hi2,
            MeasureTheory.integral_const_mul,
            oma_setIntegral_ball_indicator BM _ measurableSet_ball,
            oma_setIntegral_ball_indicator BM _ measurableSet_ball]
        rw [Finset.sum_congr rfl hterm_val, ← Finset.sum_sdiff hGin_sub]
        have h_in_zero : ∀ v ∈ G_in,
            volume.real (BM ∩ Metric.ball (v : E) (R - 1)) -
              c * volume.real (BM ∩ Metric.ball (v : E) R) = 0 := by
          intro v hv
          have hv0 : dist (v : E) 0 < r_in :=
            Metric.mem_ball.1 ((mem_omaLatBall hd hρ hΛ hr_in).1 hv)
          have hsubR : Metric.ball (v : E) R ⊆ BM := by
            intro z hz
            have hzv : dist z (v : E) < R := Metric.mem_ball.1 hz
            rw [Metric.mem_ball]
            linarith [dist_triangle z (v : E) 0]
          have hsubRm1 : Metric.ball (v : E) (R - 1) ⊆ BM :=
            Set.Subset.trans (Metric.ball_subset_ball (by linarith)) hsubR
          have hne_Rpow : R ^ (2 * d) ≠ 0 := ne_of_gt (pow_pos hR_pos (2 * d))
          rw [Set.inter_eq_right.2 hsubRm1, Set.inter_eq_right.2 hsubR,
            oma_vol_ball hd (v : E) (le_of_lt hRm1), oma_vol_ball hd (v : E) (le_of_lt hR_pos),
            hc_eq, div_pow]
          calc (R - 1) ^ (2 * d) * volume.real (Metric.ball (0 : E) 1) -
                (R - 1) ^ (2 * d) / R ^ (2 * d) * (R ^ (2 * d) * volume.real (Metric.ball (0 : E) 1))
            _ = (R - 1) ^ (2 * d) * volume.real (Metric.ball (0 : E) 1) -
                ((R - 1) ^ (2 * d) / R ^ (2 * d) * R ^ (2 * d)) * volume.real (Metric.ball (0 : E) 1) := by ring
            _ = 0 := by rw [div_mul_cancel₀ _ hne_Rpow, sub_self]
        rw [Finset.sum_congr rfl h_in_zero, Finset.sum_const_zero, add_zero]
        have h_bd_low : ∀ v ∈ G_out \ G_in,
            -((R - 1) ^ (2 * d) * volume.real (Metric.ball (0 : E) 1)) ≤
              volume.real (BM ∩ Metric.ball (v : E) (R - 1)) -
                c * volume.real (BM ∩ Metric.ball (v : E) R) := by
          intro v _
          have hnonneg : 0 ≤ volume.real (BM ∩ Metric.ball (v : E) (R - 1)) := measureReal_nonneg
          have hle_R : volume.real (BM ∩ Metric.ball (v : E) R) ≤
              (R ^ (2 * d)) * volume.real (Metric.ball (0 : E) 1) := by
            rw [← oma_vol_ball hd (v : E) (le_of_lt hR_pos)]
            exact measureReal_mono Set.inter_subset_right (ne_of_lt measure_ball_lt_top)
          have hcR : c * ((R ^ (2 * d)) * volume.real (Metric.ball (0 : E) 1)) =
              (R - 1) ^ (2 * d) * volume.real (Metric.ball (0 : E) 1) := by
            rw [hc_eq, div_pow]
            field_simp [ne_of_gt (pow_pos hR_pos (2 * d))]
          nlinarith [mul_le_mul_of_nonneg_left hle_R (le_of_lt hc_pos)]
        have hsum_low := Finset.sum_le_sum h_bd_low
        simp only [Finset.sum_const, nsmul_eq_mul] at hsum_low
        have hsdiff_card : ((G_out \ G_in).card : ℝ) = (G_out.card : ℝ) - (G_in.card : ℝ) := by
          have hsd : (G_out \ G_in).card = G_out.card - G_in.card := by
            rw [Finset.card_sdiff, Finset.inter_eq_left.2 hGin_sub]
          rw [hsd, Nat.cast_sub (Finset.card_le_card hGin_sub)]
        rw [hsdiff_card, mul_comm] at hsum_low
        exact hsum_low
      rw [hint_rhs_eval] at hint_le
      have hcomb := le_trans hint_lhs_eval hint_le
      have hdiv : ε * δ ^ (2 * d) * (G_in.card : ℝ) ≤
          (R - 1) ^ (2 * d) * ((G_out.card : ℝ) - (G_in.card : ℝ)) := by
        nlinarith
      have hRm1_pow : 0 < (R - 1) ^ (2 * d) := by positivity
      have hα_mul : α * (G_in.card : ℝ) ≤ (G_out.card : ℝ) - (G_in.card : ℝ) := by
        dsimp [α]
        rw [div_mul_eq_mul_div, div_le_iff₀ hRm1_pow]
        linarith
      linarith
    have hrk_pos : ∀ k : ℕ, 0 < ((2 * k + 1 : ℕ) : ℝ) * R := fun _ => by positivity
    have hpow_growth : ∀ k : ℕ,
        (1 + α) ^ k ≤ ((omaLatBall hd Λ hρ hΛ 0 (hrk_pos k)).card : ℝ) := by
      intro k
      induction k with
      | zero =>
        simp only [pow_zero, Nat.mul_zero, zero_add, Nat.cast_one, one_mul]
        exact_mod_cast h0_card_ge1
      | succ k ih =>
        have hst := hstep (hrk_pos k)
        have hrad_eq : ((2 * k + 1 : ℕ) : ℝ) * R + 2 * R = ((2 * (k + 1) + 1 : ℕ) : ℝ) * R := by
          push_cast; ring
        have hcard_eq : (omaLatBall hd Λ hρ hΛ 0 (by linarith [hrk_pos k] :
              0 < ((2 * k + 1 : ℕ) : ℝ) * R + 2 * R)).card =
            (omaLatBall hd Λ hρ hΛ 0 (hrk_pos (k + 1))).card := by
          congr 1
          ext v
          rw [mem_omaLatBall, mem_omaLatBall, hrad_eq]
        rw [hcard_eq] at hst
        rw [pow_succ, mul_comm ((1 + α) ^ k) (1 + α)]
        exact le_trans (mul_le_mul_of_nonneg_left ih (by positivity)) hst
    refine oma_exp_beats_poly hα_pos (A := 4 * R / ρ) (B := 2 * R / ρ + 1)
      (by positivity) (by positivity) (2 * d) (fun k => ?_)
    have h1 := hpow_growth k
    have h2 := oma_lattice_finset_card_bound hd hρ hΛ 0 (hrk_pos k) _
      (fun v hv => (mem_omaLatBall hd hρ hΛ (hrk_pos k)).1 hv)
    have h3 : (2 * (((2 * k + 1 : ℕ) : ℝ) * R) / ρ + 1) ^ (2 * d) =
        (4 * R / ρ * (k : ℝ) + (2 * R / ρ + 1)) ^ (2 * d) := by
      congr 1; push_cast; field_simp; ring
    linarith [h3]
  obtain ⟨w, hw_pos, hw_ratio⟩ := hexists_w
  let A := omaLatBall hd Λ hρ hΛ w hR_pos
  let A_in := omaLatBall hd Λ hρ hΛ w hRm1
  let U : Finset ℝ² := A.image (fun v : Λ => π v)
  have hU_card : U.card = A.card := Finset.card_image_of_injective A hπ
  refine ⟨U, by rw [hU_card]; exact hw_pos, ?_, ?_⟩
  · rw [hU_card]
    exact oma_lattice_finset_card_bound hd hρ hΛ w hR_pos A
      (fun v hv => (mem_omaLatBall hd hρ hΛ hR_pos).1 hv)
  · have hpairs : A_in.card * S.card ≤
        (U.offDiag.filter (fun p : ℝ² × ℝ² => dist p.1 p.2 = 1)).card := by
      let pairMap : Λ × Λ → ℝ² × ℝ² := fun vs => (π (vs.1 + vs.2), π vs.1)
      have hmaps : ∀ vs ∈ A_in ×ˢ S,
          pairMap vs ∈ U.offDiag.filter (fun p : ℝ² × ℝ² => dist p.1 p.2 = 1) := by
        intro vs hvs
        rcases Finset.mem_product.1 hvs with ⟨hv1_in, hsS⟩
        have hv1_ball : dist (vs.1 : E) w < R - 1 :=
          Metric.mem_ball.1 ((mem_omaLatBall hd hρ hΛ hRm1).1 hv1_in)
        have hs_norm : ‖(vs.2 : E)‖ ≤ 1 := hS_norm vs.2 hsS
        have hv1_A : vs.1 ∈ A := by
          rw [mem_omaLatBall hd hρ hΛ hR_pos, Metric.mem_ball]
          linarith
        have hv2_A : vs.1 + vs.2 ∈ A := by
          rw [mem_omaLatBall hd hρ hΛ hR_pos, Metric.mem_ball, dist_eq_norm]
          have hadd : (((vs.1 + vs.2 : Λ) : E) - w) = ((vs.1 : E) - w) + (vs.2 : E) := by
            push_cast; abel
          rw [hadd]
          have htri := norm_add_le ((vs.1 : E) - w) (vs.2 : E)
          rw [dist_eq_norm] at hv1_ball
          linarith
        have hdist1 : dist (π (vs.1 + vs.2)) (π vs.1) = 1 := by
          rw [dist_eq_norm, map_add, add_sub_cancel_left]
          exact hS_proj vs.2 hsS
        have hne_u : π (vs.1 + vs.2) ≠ π vs.1 := by
          intro heq
          rw [heq, dist_self] at hdist1
          norm_num at hdist1
        refine Finset.mem_filter.2 ⟨Finset.mem_offDiag.2 ⟨?_, ?_, hne_u⟩, hdist1⟩
        · exact Finset.mem_image.2 ⟨vs.1 + vs.2, hv2_A, rfl⟩
        · exact Finset.mem_image.2 ⟨vs.1, hv1_A, rfl⟩
      have hinj_pair : Set.InjOn pairMap ((A_in ×ˢ S : Finset (Λ × Λ)) : Set (Λ × Λ)) := by
        intro vs1 _ vs2 _ heq
        have heq2 : π vs1.1 = π vs2.1 := congrArg Prod.snd heq
        have hv1 : vs1.1 = vs2.1 := hπ heq2
        have heq1 : π (vs1.1 + vs1.2) = π (vs2.1 + vs2.2) := congrArg Prod.fst heq
        have hv12 : vs1.1 + vs1.2 = vs2.1 + vs2.2 := hπ heq1
        have hv2 : vs1.2 = vs2.2 := add_left_cancel (hv1 ▸ hv12)
        exact Prod.ext hv1 hv2
      have hcard_prod : (A_in ×ˢ S).card = A_in.card * S.card := Finset.card_product A_in S
      rw [← hcard_prod, ← Finset.card_image_of_injOn hinj_pair]
      refine Finset.card_le_card (fun p hp => ?_)
      obtain ⟨vs, hvs, rfl⟩ := Finset.mem_image.1 hp
      exact hmaps vs hvs
    have hord_le := oma_ordered_unit_le_two_unitDistNum U
    have hnat_le : A_in.card * S.card ≤ 2 * unitDistNum U := le_trans hpairs hord_le
    have hreal_le : (A_in.card : ℝ) * (S.card : ℝ) ≤ 2 * (unitDistNum U : ℝ) := by
      exact_mod_cast hnat_le
    rw [hU_card]
    calc c * (S.card : ℝ) * (A.card : ℝ)
      _ = (c * (A.card : ℝ)) * (S.card : ℝ) := by ring
      _ ≤ (A_in.card : ℝ) * (S.card : ℝ) :=
          mul_le_mul_of_nonneg_right hw_ratio (Nat.cast_nonneg _)
      _ ≤ 2 * (unitDistNum U : ℝ) := hreal_le
