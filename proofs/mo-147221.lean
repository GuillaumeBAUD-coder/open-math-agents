import OMAStatements.S_mo_147221

-- Problem: Distance function from the origin to the boundary of a convex polytope
-- Upstream: formal-conjectures statements/mo-147221.lean:0 (declaration OMA.S_mo_147221.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)


open Metric Set InnerProductGeometry

namespace OMA.Aux147221

open OMA.S_mo_147221

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma mem_of_lt {K : Set E} {r : ℝ} (hrK : ball 0 r ⊆ K) {u : E} (hu : ‖u‖ = 1) {t : ℝ}
    (ht0 : 0 < t) (ht : t < r) : t • u ∈ K := by
  apply hrK
  rw [mem_ball_zero_iff, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos ht0]
  exact ht

lemma bdd {K : Set E} {R : ℝ} (hKR : K ⊆ closedBall 0 R) {u : E} (hu : ‖u‖ = 1) :
    ∀ t ∈ {t : ℝ | 0 < t ∧ t • u ∈ K}, t ≤ R := by
  rintro t ⟨ht0, ht⟩
  have := hKR ht
  rw [mem_closedBall_zero_iff, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos ht0] at this
  exact this

lemma basic {K : Set E} (hK : IsClosed K) {r R : ℝ} (hr : 0 < r) (hrK : ball 0 r ⊆ K)
    (hKR : K ⊆ closedBall 0 R) {u : E} (hu : ‖u‖ = 1) :
    r ≤ radial K u ∧ radial K u ≤ R ∧ radial K u • u ∈ K := by
  have hne : ({t : ℝ | 0 < t ∧ t • u ∈ K}).Nonempty :=
    ⟨r / 2, by positivity, mem_of_lt hrK hu (by positivity) (by linarith)⟩
  have hbdd : BddAbove {t : ℝ | 0 < t ∧ t • u ∈ K} := ⟨R, bdd hKR hu⟩
  refine ⟨?_, csSup_le hne (bdd hKR hu), ?_⟩
  · apply le_of_forall_lt
    intro c hc
    have hm : max c 0 < r := max_lt hc hr
    have hm0 : 0 ≤ max c 0 := le_max_right _ _
    have hmc : c ≤ max c 0 := le_max_left _ _
    have hmem : (max c 0 + r) / 2 ∈ {t : ℝ | 0 < t ∧ t • u ∈ K} :=
      ⟨by linarith, mem_of_lt hrK hu (by linarith) (by linarith)⟩
    have := le_csSup hbdd hmem
    unfold radial
    linarith
  · have hcl : IsClosed {t : ℝ | t • u ∈ K} := hK.preimage (continuous_id.smul continuous_const)
    have h1 : sSup {t : ℝ | 0 < t ∧ t • u ∈ K} ∈ closure {t : ℝ | 0 < t ∧ t • u ∈ K} :=
      csSup_mem_closure hne hbdd
    exact closure_minimal (fun t ht => ht.2) hcl h1

lemma key {K : Set E} (hK : IsClosed K) (hconv : Convex ℝ K) {r R : ℝ} (hr : 0 < r)
    (hrK : ball 0 r ⊆ K) (hKR : K ⊆ closedBall 0 R) {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    radial K v - radial K u ≤ R ^ 2 / r * dist u v := by
  obtain ⟨hs1, hs2, hsK⟩ := basic hK hr hrK hKR hv
  have hbddu : BddAbove {t : ℝ | 0 < t ∧ t • u ∈ K} := ⟨R, bdd hKR hu⟩
  have hR : 0 < R := by linarith
  by_cases hd0 : dist u v = 0
  · have huv : u = v := dist_eq_zero.mp hd0
    subst huv
    rw [sub_self]
    exact mul_nonneg (by positivity) dist_nonneg
  have hd : 0 < dist u v := lt_of_le_of_ne dist_nonneg (Ne.symm hd0)
  generalize hsdef : radial K v = s at hs1 hs2 hsK
  generalize hddef : dist u v = d at hd
  have hs0 : 0 < s := by linarith
  have hcb : closedBall (0 : E) r ⊆ K := by
    rw [← closure_ball (0 : E) hr.ne']
    exact closure_minimal hrK hK
  have hw : (r / d) • (u - v) ∈ K := by
    apply hcb
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hd),
      ← dist_eq_norm, hddef, div_mul_cancel₀ _ hd.ne']
  have hden : 0 < s * d + r := by positivity
  have hmem := hconv hsK hw (a := r / (s * d + r)) (b := s * d / (s * d + r))
    (by positivity) (by positivity) (by field_simp; ring)
  have h1 : r / (s * d + r) * s = r * s / (s * d + r) := by ring
  have h2 : s * d / (s * d + r) * (r / d) = r * s / (s * d + r) := by field_simp
  have heq : (r / (s * d + r)) • (s • v) + (s * d / (s * d + r)) • ((r / d) • (u - v))
      = (r * s / (s * d + r)) • u := by
    rw [smul_smul, smul_smul, h1, h2, smul_sub]
    abel
  rw [heq] at hmem
  have ht0 : 0 < r * s / (s * d + r) := by positivity
  have hle : r * s / (s * d + r) ≤ radial K u := le_csSup hbddu ⟨ht0, hmem⟩
  have e1 : s - r * s / (s * d + r) = s ^ 2 * d / (s * d + r) := by field_simp; ring
  have e2 : s ^ 2 * d / (s * d + r) ≤ R ^ 2 * d / r := by
    apply div_le_div₀ (by positivity)
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs0.le hs2 2) hd.le
    · exact hr
    · nlinarith
  have e3 : R ^ 2 * d / r = R ^ 2 / r * d := by ring
  linarith

lemma absb {K : Set E} (hK : IsClosed K) (hconv : Convex ℝ K) {r R : ℝ} (hr : 0 < r)
    (hrK : ball 0 r ⊆ K) (hKR : K ⊆ closedBall 0 R) {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |radial K u - radial K v| ≤ R ^ 2 / r * dist u v := by
  rw [abs_sub_le_iff]
  refine ⟨?_, key hK hconv hr hrK hKR hu hv⟩
  have := key hK hconv hr hrK hKR hv hu
  rwa [dist_comm] at this

lemma dist_le_angle {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) : dist u v ≤ angle u v := by
  have h0 : 0 ≤ angle u v := angle_nonneg u v
  have hc : Real.cos (angle u v) = inner ℝ u v := by
    rw [cos_angle, hu, hv]; simp
  have h1 : dist u v ^ 2 = 2 - 2 * Real.cos (angle u v) := by
    rw [dist_eq_norm, norm_sub_sq_real, hu, hv, hc]; ring
  have h2 : 1 - angle u v ^ 2 / 2 ≤ Real.cos (angle u v) := Real.one_sub_sq_div_two_le_cos
  by_contra h
  push_neg at h
  have h3 : angle u v ^ 2 < dist u v ^ 2 := pow_lt_pow_left₀ h h0 two_ne_zero
  linarith

end OMA.Aux147221

open OMA.Aux147221 OMA.S_mo_147221 in
theorem OMA.solution : type_of% @OMA.S_mo_147221.main := by
  intro E _ _ K hK hconv
  refine ⟨fun r R hr hR hrK hKR =>
    ⟨fun u hu => basic hK hr hrK hKR hu, fun u v hu hv => ?_⟩, ?_⟩
  · have h1 := absb hK hconv hr hrK hKR hu hv
    refine ⟨h1, h1.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (dist_le_angle hu hv) (by positivity)
  · intro h0 hb
    obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
    obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : E)
    have hKR : K ⊆ closedBall 0 (max R 1) :=
      hR.trans (closedBall_subset_closedBall (le_max_left _ _))
    have hR1 : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hC : 0 < (max R 1) ^ 2 / r := by positivity
    refine ⟨?_, (max R 1) ^ 2 / r, hC, fun u v hu hv =>
      (absb hK hconv hr hrK hKR hu hv).trans
        (mul_le_mul_of_nonneg_left (dist_le_angle hu hv) hC.le)⟩
    have hL : LipschitzOnWith (Real.toNNReal ((max R 1) ^ 2 / r)) (radial K) (sphere 0 1) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro u hu v hv
      rw [Real.dist_eq, Real.coe_toNNReal _ hC.le]
      exact absb hK hconv hr hrK hKR (mem_sphere_zero_iff_norm.mp hu)
        (mem_sphere_zero_iff_norm.mp hv)
    exact hL.continuousOn
