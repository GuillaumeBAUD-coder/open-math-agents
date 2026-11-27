import OMAReductions.R_Erdos504_erdos_504_R1

/-! # Szekeres' construction

The points are `∑ j, x j * δ ^ j * u j` for `x : Fin t → Bool`, where `u j` is the unit vector of
argument `π j / t`. The difference of two points is `δ ^ m` times a vector that tends to `± u m`
as `δ → 0`, where `m` is the first coordinate in which the points differ. So every angle tends to
an angle between two of the vectors `± u j`, which is `0` or at most `π - π / t`.
-/

namespace OMA504

open Filter Topology

/-- The unit vector of argument `a`. -/
noncomputable def u (a : ℝ) : ℂ := (Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I

lemma u_re (a : ℝ) : (u a).re = Real.cos a := by simp [u, Complex.cos_ofReal_re]

lemma u_im (a : ℝ) : (u a).im = Real.sin a := by simp [u, Complex.sin_ofReal_re]

lemma norm_u (a : ℝ) : ‖u a‖ = 1 := by
  have h : u a = Complex.exp (a * Complex.I) := by
    rw [Complex.exp_mul_I, u, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma u_ne_zero (a : ℝ) : u a ≠ 0 := by
  intro h
  have := norm_u a
  rw [h, norm_zero] at this
  exact zero_ne_one this

lemma inner_cu (c c' a b : ℝ) :
    inner ℝ ((c : ℂ) * u a) ((c' : ℂ) * u b) = c * c' * Real.cos (a - b) := by
  rw [Complex.inner, Real.cos_sub]
  simp [Complex.mul_re, u_re, u_im]
  ring

/-- Two of the vectors `± u (π j / t)` make an angle `0` or at most `π - π / t`. -/
lemma ang_le (t : ℕ) (ht : 0 < t) (j k : Fin t) (c c' : ℝ) (hc : c = 1 ∨ c = -1)
    (hc' : c' = 1 ∨ c' = -1) (h : j = k → c = c') :
    InnerProductGeometry.angle ((c : ℂ) * u (Real.pi * (j : ℕ) / t))
      ((c' : ℂ) * u (Real.pi * (k : ℕ) / t)) ≤ (1 - 1 / (t : ℝ)) * Real.pi := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hpi := Real.pi_pos
  have hdiv : 0 < Real.pi / t := div_pos hpi htR
  have hdivle : Real.pi / t ≤ Real.pi := div_le_self hpi.le (by exact_mod_cast ht)
  have hbound : (1 - 1 / (t : ℝ)) * Real.pi = Real.pi - Real.pi / t := by ring
  have hcne : (c : ℂ) ≠ 0 := by
    rcases hc with rfl | rfl <;> norm_num
  have hc'ne : (c' : ℂ) ≠ 0 := by
    rcases hc' with rfl | rfl <;> norm_num
  by_cases hjk : j = k
  · subst hjk
    rw [h rfl, InnerProductGeometry.angle_self (mul_ne_zero hc'ne (u_ne_zero _)), hbound]
    linarith
  · have hn1 : ‖(c : ℂ) * u (Real.pi * (j : ℕ) / t)‖ = 1 := by
      rw [norm_mul, norm_u, mul_one, Complex.norm_real]
      rcases hc with rfl | rfl <;> norm_num
    have hn2 : ‖(c' : ℂ) * u (Real.pi * (k : ℕ) / t)‖ = 1 := by
      rw [norm_mul, norm_u, mul_one, Complex.norm_real]
      rcases hc' with rfl | rfl <;> norm_num
    unfold InnerProductGeometry.angle
    rw [inner_cu, hn1, hn2, mul_one, div_one, hbound]
    -- the difference of the arguments
    set φ : ℝ := |Real.pi * (j : ℕ) / t - Real.pi * (k : ℕ) / t| with hφ
    have hcosφ : Real.cos (Real.pi * (j : ℕ) / t - Real.pi * (k : ℕ) / t) = Real.cos φ := by
      rw [hφ, Real.cos_abs]
    have hjkv : (j : ℕ) ≠ (k : ℕ) := fun hv => hjk (Fin.ext hv)
    have hφeq : φ = |((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)| * (Real.pi / t) := by
      rw [hφ, ← abs_of_pos hdiv, ← abs_mul]
      congr 1
      ring
    have habs1 : 1 ≤ |((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)| := by
      rcases Nat.lt_or_gt_of_ne hjkv with hlt | hgt
      · have : ((j : ℕ) : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hlt
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have : ((k : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hgt
        rw [abs_of_nonneg (by linarith)]
        linarith
    have habs2 : |((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)| ≤ (t : ℝ) - 1 := by
      have hj : ((j : ℕ) : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast j.isLt
      have hk : ((k : ℕ) : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast k.isLt
      have hj0 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
      have hk0 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [abs_le]
      constructor <;> linarith
    have hφ1 : Real.pi / t ≤ φ := by
      rw [hφeq]
      nlinarith
    have hφ2 : φ ≤ Real.pi - Real.pi / t := by
      rw [hφeq]
      have : ((t : ℝ) - 1) * (Real.pi / t) = Real.pi - Real.pi / t := by
        field_simp
      nlinarith
    have hcos1 : Real.cos φ ≤ Real.cos (Real.pi / t) :=
      Real.cos_le_cos_of_nonneg_of_le_pi hdiv.le (by linarith) hφ1
    have hcos2 : -Real.cos (Real.pi / t) ≤ Real.cos φ := by
      rw [← Real.cos_pi_sub]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hφ2
    have hval : -Real.cos (Real.pi / t) ≤
        c * c' * Real.cos (Real.pi * (j : ℕ) / t - Real.pi * (k : ℕ) / t) := by
      rw [hcosφ]
      rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl <;> norm_num <;> linarith
    calc Real.arccos (c * c' * Real.cos (Real.pi * (j : ℕ) / t - Real.pi * (k : ℕ) / t))
        ≤ Real.arccos (-Real.cos (Real.pi / t)) := Real.arccos_le_arccos hval
      _ = Real.arccos (Real.cos (Real.pi - Real.pi / t)) := by rw [Real.cos_pi_sub]
      _ = Real.pi - Real.pi / t := Real.arccos_cos (by linarith) (by linarith)

/-- The coordinate of a vertex of the cube. -/
def b {t : ℕ} (x : Fin t → Bool) (j : Fin t) : ℝ := if x j then 1 else 0

/-- The points of the construction. -/
noncomputable def P (t : ℕ) (δ : ℝ) (x : Fin t → Bool) : ℂ :=
  ∑ j : Fin t, ((b x j * δ ^ (j : ℕ) : ℝ) : ℂ) * u (Real.pi * (j : ℕ) / t)

/-- The difference of two points, divided by `δ ^ m`. -/
noncomputable def G (t : ℕ) (δ : ℝ) (m : Fin t) (x y : Fin t → Bool) : ℂ :=
  ∑ j : Fin t, (((b x j - b y j) * δ ^ ((j : ℕ) - (m : ℕ)) : ℝ) : ℂ) * u (Real.pi * (j : ℕ) / t)

lemma exists_first_diff {t : ℕ} (x y : Fin t → Bool) (h : x ≠ y) :
    ∃ m, x m ≠ y m ∧ ∀ j, j < m → x j = y j := by
  classical
  have hne : (Finset.univ.filter fun j => x j ≠ y j).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    apply h
    funext j
    by_contra hj
    have : j ∈ Finset.univ.filter fun j => x j ≠ y j := Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩
    rw [hcon] at this
    exact absurd this (Finset.notMem_empty j)
  refine ⟨(Finset.univ.filter fun j => x j ≠ y j).min' hne, ?_, ?_⟩
  · exact (Finset.mem_filter.1 (Finset.min'_mem _ hne)).2
  · intro j hj
    by_contra hxy
    have hmem : j ∈ Finset.univ.filter fun j => x j ≠ y j :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hxy⟩
    exact absurd (Finset.min'_le _ j hmem) (not_le.2 hj)

lemma sub_eq {t : ℕ} (δ : ℝ) (m : Fin t) (x y : Fin t → Bool) (hm : ∀ j, j < m → x j = y j) :
    P t δ x - P t δ y = ((δ ^ (m : ℕ) : ℝ) : ℂ) * G t δ m x y := by
  unfold P G
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j < m
  · have : b x j = b y j := by unfold b; rw [hm j hj]
    rw [this]
    simp
  · have hle : (m : ℕ) ≤ (j : ℕ) := by
      have := not_lt.1 hj
      exact this
    have hpow : δ ^ (j : ℕ) = δ ^ (m : ℕ) * δ ^ ((j : ℕ) - (m : ℕ)) := by
      rw [← pow_add, Nat.add_sub_cancel' hle]
    rw [hpow]
    push_cast
    ring

lemma G_zero {t : ℕ} (m : Fin t) (x y : Fin t → Bool) (hm : ∀ j, j < m → x j = y j) :
    G t 0 m x y = ((b x m - b y m : ℝ) : ℂ) * u (Real.pi * (m : ℕ) / t) := by
  unfold G
  rw [Finset.sum_eq_single m]
  · simp
  · intro j _ hjm
    by_cases hj : j < m
    · have : b x j = b y j := by unfold b; rw [hm j hj]
      rw [this]
      simp
    · have hlt : (m : ℕ) < (j : ℕ) := by
        have h1 := not_lt.1 hj
        exact lt_of_le_of_ne h1 (fun h => hjm (Fin.ext h.symm))
      have hpos : (j : ℕ) - (m : ℕ) ≠ 0 := by omega
      rw [zero_pow hpos]
      simp
  · intro h
    exact absurd (Finset.mem_univ m) h

lemma continuous_G {t : ℕ} (m : Fin t) (x y : Fin t → Bool) :
    Continuous (fun δ : ℝ => G t δ m x y) := by
  unfold G
  fun_prop

lemma coeff_pm {t : ℕ} (x y : Fin t → Bool) (m : Fin t) (h : x m ≠ y m) :
    b x m - b y m = 1 ∨ b x m - b y m = -1 := by
  unfold b
  cases hx : x m <;> cases hy : y m <;> simp_all

lemma G_zero_ne {t : ℕ} (m : Fin t) (x y : Fin t → Bool) (hm : ∀ j, j < m → x j = y j)
    (h : x m ≠ y m) : G t 0 m x y ≠ 0 := by
  rw [G_zero m x y hm]
  refine mul_ne_zero ?_ (u_ne_zero _)
  rcases coeff_pm x y m h with h1 | h1 <;> rw [h1] <;> norm_num

lemma eventually_ne {t : ℕ} (x y : Fin t → Bool) (h : x ≠ y) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), P t δ x ≠ P t δ y := by
  obtain ⟨m, hm, hlt⟩ := exists_first_diff x y h
  have hcont : ContinuousAt (fun δ : ℝ => G t δ m x y) 0 := (continuous_G m x y).continuousAt
  have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), G t δ m x y ≠ 0 := hcont.eventually_ne (G_zero_ne m x y hlt hm)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with δ hδ hpos
  intro heq
  have hsub := sub_eq δ m x y hlt
  rw [heq, sub_self] at hsub
  have hpow : ((δ ^ (m : ℕ) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < δ := hpos
    exact_mod_cast (pow_pos this _).ne'
  exact (mul_ne_zero hpow hδ) hsub.symm

lemma eventually_angle {t : ℕ} (ht : 0 < t) (ε : ℝ) (hε : 0 < ε) (x y z : Fin t → Bool)
    (hxy : x ≠ y) (hzy : z ≠ y) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      EuclideanGeometry.angle (P t δ x) (P t δ y) (P t δ z) < (1 - 1 / (t : ℝ)) * Real.pi + ε := by
  obtain ⟨m, hm, hlt⟩ := exists_first_diff x y hxy
  obtain ⟨m', hm', hlt'⟩ := exists_first_diff z y hzy
  have h1 := G_zero_ne m x y hlt hm
  have h2 := G_zero_ne m' z y hlt' hm'
  have hpair : Tendsto (fun δ : ℝ => (G t δ m x y, G t δ m' z y)) (𝓝 0)
      (𝓝 (G t 0 m x y, G t 0 m' z y)) :=
    ((continuous_G m x y).prodMk (continuous_G m' z y)).tendsto 0
  have hang : Tendsto (fun p : ℂ × ℂ => InnerProductGeometry.angle p.1 p.2)
      (𝓝 (G t 0 m x y, G t 0 m' z y))
      (𝓝 (InnerProductGeometry.angle (G t 0 m x y) (G t 0 m' z y))) :=
    InnerProductGeometry.continuousAt_angle (x := (G t 0 m x y, G t 0 m' z y)) h1 h2
  have hcont : Tendsto
      ((fun p : ℂ × ℂ => InnerProductGeometry.angle p.1 p.2) ∘
        (fun δ : ℝ => (G t δ m x y, G t δ m' z y))) (𝓝 0)
      (𝓝 (InnerProductGeometry.angle (G t 0 m x y) (G t 0 m' z y))) :=
    hang.comp hpair
  have hlim : InnerProductGeometry.angle (G t 0 m x y) (G t 0 m' z y) <
      (1 - 1 / (t : ℝ)) * Real.pi + ε := by
    rw [G_zero m x y hlt, G_zero m' z y hlt']
    have hle := ang_le t ht m m' (b x m - b y m) (b z m' - b y m') (coeff_pm x y m hm)
      (coeff_pm z y m' hm') (by
        intro hmm
        subst hmm
        unfold b
        cases hx : x m <;> cases hy : y m <;> cases hz : z m <;> simp_all)
    linarith
  have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), ((fun p : ℂ × ℂ => InnerProductGeometry.angle p.1 p.2) ∘
        (fun δ : ℝ => (G t δ m x y, G t δ m' z y))) δ <
      (1 - 1 / (t : ℝ)) * Real.pi + ε := hcont.eventually (Iio_mem_nhds hlim)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with δ hδ hpos
  have hpos' : (0 : ℝ) < δ := hpos
  unfold EuclideanGeometry.angle
  rw [vsub_eq_sub, vsub_eq_sub, sub_eq δ m x y hlt, sub_eq δ m' z y hlt',
    ← Complex.real_smul, ← Complex.real_smul,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (pow_pos hpos' _),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (pow_pos hpos' _)]
  exact hδ

theorem main {t : ℕ} (ht : 0 < t) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℂ, S.card = 2 ^ t ∧
      ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
        EuclideanGeometry.angle p q r < (1 - 1 / (t : ℝ)) * Real.pi + ε := by
  classical
  have hall : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∀ x y : Fin t → Bool, x ≠ y → P t δ x ≠ P t δ y) ∧
      (∀ x y z : Fin t → Bool, x ≠ y → z ≠ y →
        EuclideanGeometry.angle (P t δ x) (P t δ y) (P t δ z) <
          (1 - 1 / (t : ℝ)) * Real.pi + ε) := by
    refine Filter.Eventually.and ?_ ?_
    · rw [Filter.eventually_all]
      intro x
      rw [Filter.eventually_all]
      intro y
      by_cases h : x = y
      · exact Filter.Eventually.of_forall fun δ hne => absurd h hne
      · exact (eventually_ne x y h).mono fun δ hδ _ => hδ
    · rw [Filter.eventually_all]
      intro x
      rw [Filter.eventually_all]
      intro y
      rw [Filter.eventually_all]
      intro z
      by_cases h : x = y
      · exact Filter.Eventually.of_forall fun δ hne => absurd h hne
      · by_cases h' : z = y
        · exact Filter.Eventually.of_forall fun δ _ hne => absurd h' hne
        · exact (eventually_angle ht ε hε x y z h h').mono fun δ hδ _ _ => hδ
  obtain ⟨δ, hinj, hang⟩ := hall.exists
  have hinj' : Function.Injective (P t δ) := by
    intro x y hxy
    by_contra hne
    exact hinj x y hne hxy
  refine ⟨Finset.univ.image (P t δ), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj', Finset.card_univ]
    simp
  · intro p hp q hq r hr hpq hrq
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hr
    exact hang x y z (fun h => hpq (by rw [h])) (fun h => hrq (by rw [h]))

end OMA504

theorem OMA.solution : OMA.R_Erdos504_erdos_504_R1.H1 := by
  intro t ht ε hε
  exact OMA504.main ht hε
