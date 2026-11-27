import OMAReductions.R_Erdos504_erdos_504_R1

-- Step Erdos504.erdos_504.R1.H1: hypothesis H1 of reduction Erdos504.erdos_504.R1
-- Credit: @senamakel
-- Szekeres (1941) construction, by induction: double a shrunken copy of the previous set along the direction exp(i m pi / t).


open Real

namespace OMA.Erdos504Szekeres

lemma dir_angle_le (t : ℕ) (ht : 0 < t) (d : ℤ) (hd : ¬ (t : ℤ) ∣ d) (x y : ℝ)
    (hxy : x - y = (d : ℝ) * π / t) :
    |toIocMod Real.two_pi_pos (-π) (x - y)| ≤ (1 - 1 / (t : ℝ)) * π := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  set k := toIocDiv Real.two_pi_pos (-π) (x - y) with hk
  have hmem := toIocMod_mem_Ioc Real.two_pi_pos (-π) (x - y)
  have hval : toIocMod Real.two_pi_pos (-π) (x - y) = ((d - 2 * k * t : ℤ) : ℝ) * π / t := by
    rw [toIocMod, ← hk, hxy]
    push_cast
    field_simp
    simp [zsmul_eq_mul]
    ring
  rw [hval] at hmem ⊢
  set e : ℤ := d - 2 * k * t with he
  obtain ⟨h1, h2⟩ := hmem
  have h1' : -(t : ℝ) < e := by
    rw [lt_div_iff₀ htR] at h1
    have : -(t : ℝ) * π < e * π := by linarith
    exact lt_of_mul_lt_mul_right this pi_pos.le
  have h2' : (e : ℝ) ≤ t := by
    rw [div_le_iff₀ htR] at h2
    have : (e : ℝ) * π ≤ t * π := by linarith
    exact le_of_mul_le_mul_right this pi_pos
  have h1z : -(t : ℤ) < e := by exact_mod_cast h1'
  have h2z : e ≤ (t : ℤ) := by exact_mod_cast h2'
  have hne0 : e ≠ 0 := by
    intro h0; apply hd; refine ⟨2 * k, ?_⟩; rw [he] at h0; linarith
  have hnet : e ≠ t := by
    intro h0; apply hd; refine ⟨2 * k + 1, ?_⟩; rw [he] at h0; linarith
  have habs : |e| ≤ (t : ℤ) - 1 := by
    rw [abs_le]; constructor <;> omega
  have habsR : |(e : ℝ)| ≤ (t : ℝ) - 1 := by exact_mod_cast habs
  rw [abs_div, abs_mul, abs_of_pos pi_pos, abs_of_pos htR]
  rw [div_le_iff₀ htR]
  have : (1 - 1 / (t : ℝ)) * π * t = ((t : ℝ) - 1) * π := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_right habsR pi_pos.le

lemma angle_dirs (t : ℕ) (ht : 0 < t) (a b : ℤ) (hd : ¬ (t : ℤ) ∣ (a - b)) :
    InnerProductGeometry.angle (Complex.exp (((a : ℝ) * π / t : ℝ) * Complex.I))
      (Complex.exp (((b : ℝ) * π / t : ℝ) * Complex.I)) ≤ (1 - 1 / (t : ℝ)) * π := by
  rw [Complex.angle_exp_exp]
  apply dir_angle_le t ht (a - b) hd
  push_cast; ring


open InnerProductGeometry in
lemma mixed_bound {x y d v : ℂ} {β δ : ℝ} (h1 : angle x d < δ) (h2 : angle y v < δ)
    (h3 : angle d v ≤ β) : angle x y < β + 2 * δ := by
  have a := angle_le_angle_add_angle x d y
  have b := angle_le_angle_add_angle d v y
  rw [angle_comm y v] at h2
  linarith

open InnerProductGeometry in
lemma both_bound {x y v : ℂ} {β δ : ℝ} (h1 : angle x v < δ) (h2 : angle y v < δ)
    (h3 : 0 ≤ β) : angle x y < β + 2 * δ := by
  have a := angle_le_angle_add_angle x v y
  rw [angle_comm y v] at h2
  linarith

lemma exp_add_t (t : ℕ) (ht : 0 < t) (m : ℕ) :
    Complex.exp (((((m : ℤ) + t : ℤ) : ℝ) * π / t : ℝ) * Complex.I) =
      -Complex.exp (((((m : ℤ)) : ℝ) * π / t : ℝ) * Complex.I) := by
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have : (((((m : ℤ) + t : ℤ) : ℝ) * π / t : ℝ) : ℂ) * Complex.I =
      (((((m : ℤ)) : ℝ) * π / t : ℝ) : ℂ) * Complex.I + π * Complex.I := by
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    push_cast; field_simp
  rw [this, Complex.exp_add, Complex.exp_pi_mul_I]; ring

open InnerProductGeometry in
lemma step (t m : ℕ) (ht : 0 < t) (hm : m < t) {δ : ℝ} (hδ : 0 < δ) (S : Finset ℂ)
    (hcard : S.card = 2 ^ m)
    (hdir : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∃ j : ℤ, 0 ≤ j % t ∧ j % t < m ∧
      angle (p - q) (Complex.exp (((j : ℝ) * π / t : ℝ) * Complex.I)) < δ)
    (hang : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      angle (p - q) (r - q) < (1 - 1 / (t : ℝ)) * π + 2 * δ) :
    ∃ S' : Finset ℂ, S'.card = 2 ^ (m + 1) ∧
    (∀ p ∈ S', ∀ q ∈ S', p ≠ q → ∃ j : ℤ, 0 ≤ j % t ∧ j % t < m + 1 ∧
      angle (p - q) (Complex.exp (((j : ℝ) * π / t : ℝ) * Complex.I)) < δ) ∧
    (∀ p ∈ S', ∀ q ∈ S', ∀ r ∈ S', p ≠ q → r ≠ q →
      angle (p - q) (r - q) < (1 - 1 / (t : ℝ)) * π + 2 * δ) := by
  set β := (1 - 1 / (t : ℝ)) * π with hβ
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hβ0 : 0 ≤ β := by
    have : 1 / (t : ℝ) ≤ 1 := by
      rw [div_le_one htR]; exact_mod_cast (by omega : 1 ≤ t)
    exact mul_nonneg (by linarith) pi_pos.le
  set u : ℂ := Complex.exp ((((m : ℤ) : ℝ) * π / t : ℝ) * Complex.I) with hu
  have hun : ‖u‖ = 1 := by rw [hu, Complex.norm_exp_ofReal_mul_I]
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hnu : -u = Complex.exp (((((m : ℤ) + t : ℤ) : ℝ) * π / t : ℝ) * Complex.I) :=
    (exp_add_t t ht m).symm
  -- continuity of the angle at (u, u)
  obtain ⟨ρ, hρ, hcont⟩ : ∃ ρ > 0, ∀ e : ℂ, ‖e‖ < ρ → angle (u + e) u < δ := by
    have hc : ContinuousAt (fun e : ℂ => angle (u + e) u) 0 := by
      have h := continuousAt_angle (x := (u + 0, u)) (by simpa using hu0) hu0
      exact h.comp (f := fun e : ℂ => (u + e, u)) (by fun_prop)
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨ρ, hρ, h⟩ := hc δ hδ
    refine ⟨ρ, hρ, fun e he => ?_⟩
    have := h (x := e) (by simpa using he)
    simp only [add_zero, angle_self hu0, dist_zero_right, Real.norm_eq_abs] at this
    exact lt_of_abs_lt this
  have hcross : ∀ e : ℂ, ‖e‖ < ρ → angle (-(u + e)) (-u) < δ := by
    intro e he; rw [angle_neg_neg]; exact hcont e he
  -- bound on S
  set R : ℝ := ∑ s ∈ S, ‖s‖ with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg (fun s _ => norm_nonneg s)
  have hsR : ∀ s ∈ S, ‖s‖ ≤ R := fun s hs =>
    Finset.single_le_sum (f := fun s => ‖s‖) (fun s _ => norm_nonneg s) hs
  set c : ℝ := min ρ 1 / (2 * R + 1) with hc
  have hmin : 0 < min ρ 1 := lt_min hρ one_pos
  have hc0 : 0 < c := by positivity
  have hsmall : ∀ s ∈ S, ∀ s' ∈ S, ‖c • (s - s')‖ < min ρ 1 := by
    intro s hs s' hs'
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
    have h1 : ‖s - s'‖ ≤ 2 * R := by
      have := norm_sub_le s s'; linarith [hsR s hs, hsR s' hs']
    calc c * ‖s - s'‖ ≤ c * (2 * R) := mul_le_mul_of_nonneg_left h1 hc0.le
      _ < c * (2 * R + 1) := by nlinarith
      _ = min ρ 1 := by rw [hc]; field_simp
  have hsmallρ : ∀ s ∈ S, ∀ s' ∈ S, ‖c • (s - s')‖ < ρ := fun s hs s' hs' =>
    lt_of_lt_of_le (hsmall s hs s' hs') (min_le_left _ _)
  set A := S.image (fun s => c • s) with hA
  set B := S.image (fun s => c • s + u) with hB
  have hinjA : Function.Injective (fun s : ℂ => c • s) := smul_right_injective ℂ hc0.ne'
  have hinjB : Function.Injective (fun s : ℂ => c • s + u) := fun a b h =>
    hinjA (add_right_cancel h)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hxA
    obtain ⟨s', hs', hss⟩ := Finset.mem_image.mp hxB
    have : u = c • (s - s') := by rw [smul_sub, ← hss]; ring
    have h := hsmall s hs s' hs'
    rw [← this, hun] at h
    exact absurd (min_le_right ρ 1) (not_le.mpr h)
  refine ⟨A ∪ B, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinjA,
      Finset.card_image_of_injective _ hinjB, hcard, pow_succ]; ring
  · intro p hp q hq hpq
    rcases Finset.mem_union.mp hp with hp | hp <;>
    rcases Finset.mem_union.mp hq with hq | hq <;>
    obtain ⟨sp, hsp, rfl⟩ := Finset.mem_image.mp hp <;>
    obtain ⟨sq, hsq, rfl⟩ := Finset.mem_image.mp hq
    · have hne : sp ≠ sq := fun h => hpq (by rw [h])
      obtain ⟨j, hj0, hj, hjd⟩ := hdir sp hsp sq hsq hne
      refine ⟨j, hj0, by omega, ?_⟩
      rw [← smul_sub, angle_smul_left_of_pos _ _ hc0]; exact hjd
    · refine ⟨(m : ℤ) + t, ?_, ?_, ?_⟩
      · exact Int.emod_nonneg _ (by exact_mod_cast ht.ne')
      · rw [Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]; omega
      · rw [← hnu]
        have : c • sp - (c • sq + u) = -(u + c • (sq - sp)) := by rw [smul_sub]; ring
        rw [this]; exact hcross _ (hsmallρ sq hsq sp hsp)
    · refine ⟨(m : ℤ), by omega, ?_, ?_⟩
      · rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
      · have : c • sp + u - c • sq = u + c • (sp - sq) := by rw [smul_sub]; ring
        rw [this]; exact hcont _ (hsmallρ sp hsp sq hsq)
    · have hne : sp ≠ sq := fun h => hpq (by rw [h])
      obtain ⟨j, hj0, hj, hjd⟩ := hdir sp hsp sq hsq hne
      refine ⟨j, hj0, by omega, ?_⟩
      have : c • sp + u - (c • sq + u) = c • (sp - sq) := by rw [smul_sub]; ring
      rw [this, angle_smul_left_of_pos _ _ hc0]; exact hjd
  · have gu : ∀ j : ℤ, 0 ≤ j % t → j % t < m →
        angle (Complex.exp (((j : ℝ) * π / t : ℝ) * Complex.I)) u ≤ β := by
      intro j hj0 hj
      apply angle_dirs t ht j m
      intro hdv
      have h := (Int.modEq_iff_dvd.mpr hdv)
      unfold Int.ModEq at h
      rw [Int.emod_eq_of_lt (by omega) (by omega)] at h
      omega
    have gnu : ∀ j : ℤ, 0 ≤ j % t → j % t < m →
        angle (Complex.exp (((j : ℝ) * π / t : ℝ) * Complex.I)) (-u) ≤ β := by
      intro j hj0 hj
      rw [hnu]
      apply angle_dirs t ht j ((m : ℤ) + t)
      intro hdv
      have h := (Int.modEq_iff_dvd.mpr hdv)
      unfold Int.ModEq at h
      rw [Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)] at h
      omega
    intro p hp q hq r hr hpq hrq
    rcases Finset.mem_union.mp hp with hp | hp <;>
    rcases Finset.mem_union.mp hq with hq | hq <;>
    rcases Finset.mem_union.mp hr with hr | hr <;>
    obtain ⟨sp, hsp, rfl⟩ := Finset.mem_image.mp hp <;>
    obtain ⟨sq, hsq, rfl⟩ := Finset.mem_image.mp hq <;>
    obtain ⟨sr, hsr, rfl⟩ := Finset.mem_image.mp hr
    · -- A A A
      have hne1 : sp ≠ sq := fun h => hpq (by rw [h])
      have hne2 : sr ≠ sq := fun h => hrq (by rw [h])
      rw [← smul_sub, ← smul_sub, angle_smul_left_of_pos _ _ hc0,
        angle_smul_right_of_pos _ _ hc0]
      exact hang sp hsp sq hsq sr hsr hne1 hne2
    · -- A A B
      have hne1 : sp ≠ sq := fun h => hpq (by rw [h])
      obtain ⟨j, hj0, hj, hjd⟩ := hdir sp hsp sq hsq hne1
      have e1 : c • sp - c • sq = c • (sp - sq) := by rw [smul_sub]
      have e2 : c • sr + u - c • sq = u + c • (sr - sq) := by rw [smul_sub]; ring
      rw [e1, e2]
      refine mixed_bound (d := Complex.exp (((j : ℝ) * π / t : ℝ) * Complex.I)) (v := u) ?_
        (hcont _ (hsmallρ sr hsr sq hsq)) (gu j hj0 hj)
      rw [angle_smul_left_of_pos _ _ hc0]; exact hjd
    · -- A B A
      have e1 : c • sp - (c • sq + u) = -(u + c • (sq - sp)) := by rw [smul_sub]; ring
      have e2 : c • sr - (c • sq + u) = -(u + c • (sq - sr)) := by rw [smul_sub]; ring
      rw [e1, e2]
      exact both_bound (hcross _ (hsmallρ sq hsq sp hsp)) (hcross _ (hsmallρ sq hsq sr hsr)) hβ0
    · -- A B B
      have hne2 : sr ≠ sq := fun h => hrq (by rw [h])
      obtain ⟨j, hj0, hj, hjd⟩ := hdir sr hsr sq hsq hne2
      have e1 : c • sp - (c • sq + u) = -(u + c • (sq - sp)) := by rw [smul_sub]; ring
      have e2 : c • sr + u - (c • sq + u) = c • (sr - sq) := by rw [smul_sub]; ring
      rw [e1, e2, angle_comm]
      refine mixed_bound (d := Complex.exp (((j : ℝ) * π / t : ℝ) * Complex.I)) (v := -u) ?_
        (hcross _ (hsmallρ sq hsq sp hsp)) (gnu j hj0 hj)
      rw [angle_smul_left_of_pos _ _ hc0]; exact hjd
    · -- B A A
      have hne2 : sr ≠ sq := fun h => hrq (by rw [h])
      obtain ⟨j, hj0, hj, hjd⟩ := hdir sr hsr sq hsq hne2
      have e1 : c • sp + u - c • sq = u + c • (sp - sq) := by rw [smul_sub]; ring
      have e2 : c • sr - c • sq = c • (sr - sq) := by rw [smul_sub]
      rw [e1, e2, angle_comm]
      refine mixed_bound (d := Complex.exp (((j : ℝ) * π / t : ℝ) * Complex.I)) (v := u) ?_
        (hcont _ (hsmallρ sp hsp sq hsq)) (gu j hj0 hj)
      rw [angle_smul_left_of_pos _ _ hc0]; exact hjd
    · -- B A B
      have e1 : c • sp + u - c • sq = u + c • (sp - sq) := by rw [smul_sub]; ring
      have e2 : c • sr + u - c • sq = u + c • (sr - sq) := by rw [smul_sub]; ring
      rw [e1, e2]
      exact both_bound (hcont _ (hsmallρ sp hsp sq hsq)) (hcont _ (hsmallρ sr hsr sq hsq)) hβ0
    · -- B B A
      have hne1 : sp ≠ sq := fun h => hpq (by rw [h])
      obtain ⟨j, hj0, hj, hjd⟩ := hdir sp hsp sq hsq hne1
      have e1 : c • sp + u - (c • sq + u) = c • (sp - sq) := by rw [smul_sub]; ring
      have e2 : c • sr - (c • sq + u) = -(u + c • (sq - sr)) := by rw [smul_sub]; ring
      rw [e1, e2]
      refine mixed_bound (d := Complex.exp (((j : ℝ) * π / t : ℝ) * Complex.I)) (v := -u) ?_
        (hcross _ (hsmallρ sq hsq sr hsr)) (gnu j hj0 hj)
      rw [angle_smul_left_of_pos _ _ hc0]; exact hjd
    · -- B B B
      have hne1 : sp ≠ sq := fun h => hpq (by rw [h])
      have hne2 : sr ≠ sq := fun h => hrq (by rw [h])
      have e1 : c • sp + u - (c • sq + u) = c • (sp - sq) := by rw [smul_sub]; ring
      have e2 : c • sr + u - (c • sq + u) = c • (sr - sq) := by rw [smul_sub]; ring
      rw [e1, e2, angle_smul_left_of_pos _ _ hc0, angle_smul_right_of_pos _ _ hc0]
      exact hang sp hsp sq hsq sr hsr hne1 hne2

lemma build (t : ℕ) (ht : 0 < t) {δ : ℝ} (hδ : 0 < δ) : ∀ m : ℕ, m ≤ t →
    ∃ S : Finset ℂ, S.card = 2 ^ m ∧
    (∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∃ j : ℤ, 0 ≤ j % t ∧ j % t < m ∧
      InnerProductGeometry.angle (p - q) (Complex.exp (((j : ℝ) * π / t : ℝ) * Complex.I)) < δ) ∧
    (∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      InnerProductGeometry.angle (p - q) (r - q) < (1 - 1 / (t : ℝ)) * π + 2 * δ) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨{0}, by simp, ?_, ?_⟩
    · intro p hp q hq hpq
      simp only [Finset.mem_singleton] at hp hq
      exact absurd (hp.trans hq.symm) hpq
    · intro p hp q hq r hr hpq
      simp only [Finset.mem_singleton] at hp hq
      exact absurd (hp.trans hq.symm) hpq
  | succ k ih =>
    intro hk
    obtain ⟨S, h1, h2, h3⟩ := ih (by omega)
    exact step t k ht (by omega) hδ S h1 h2 h3

theorem szekeres_upper {t : ℕ} (ht : 0 < t) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℂ, S.card = 2 ^ t ∧
      ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
        EuclideanGeometry.angle p q r < (1 - 1 / (t : ℝ)) * π + ε := by
  obtain ⟨S, h1, _, h3⟩ := build t ht (δ := ε / 2) (by positivity) t le_rfl
  refine ⟨S, h1, fun p hp q hq r hr hpq hrq => ?_⟩
  have := h3 p hp q hq r hr hpq hrq
  rw [EuclideanGeometry.angle]
  simp only [vsub_eq_sub]
  linarith

end OMA.Erdos504Szekeres

theorem OMA.solution : OMA.R_Erdos504_erdos_504_R1.H1 := by
  intro t ht ε hε
  exact OMA.Erdos504Szekeres.szekeres_upper ht hε
