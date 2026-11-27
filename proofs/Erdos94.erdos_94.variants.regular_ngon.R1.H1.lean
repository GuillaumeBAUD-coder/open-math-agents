import OMAReductions.R_Erdos94_erdos_94_variants_regular_ngon_R1

/-!
# Proof of `Erdos94.erdos_94.variants.regular_ngon.R1.H1`

The regular `n`-gon attains `∑ u, f(u)^2 ≥ B(n)`, where
`B(n) = n^2 (n - 1) / 2` for odd `n` and `B(n) = n^3 / 2 - 3 n^2 / 4` for even `n`.
-/

open EuclideanGeometry Erdos94

namespace Erdos94R1H1Proof

private noncomputable def regPt (n k : ℕ) : ℝ² :=
  !₂[Real.cos (2 * Real.pi * k / n), Real.sin (2 * Real.pi * k / n)]

private lemma regPt_dist (n j k : ℕ) (hn : 0 < n) (hj : j < n) (hk : k < n) :
    dist (regPt n j) (regPt n k) =
      2 * Real.sin (Real.pi * (((j + n - k) % n : ℕ) : ℝ) / n) := by
  set r := (j + n - k) % n
  have hr_lt : r < n := Nat.mod_lt _ hn
  have hcos_eq : Real.cos (2 * Real.pi * j / n - 2 * Real.pi * k / n) =
      Real.cos (2 * Real.pi * r / n) := by
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    by_cases hkj : k ≤ j
    · have hr_val : r = j - k := by
        dsimp [r]
        have h1 : j + n - k = (j - k) + n := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hr_val, Nat.cast_sub hkj]
      congr 1; field_simp
    · have hr_val : r = j + n - k := by
        dsimp [r]
        exact Nat.mod_eq_of_lt (by omega)
      have harg : 2 * Real.pi * (r : ℝ) / n =
          (2 * Real.pi * j / n - 2 * Real.pi * k / n) + 2 * Real.pi := by
        have hr_real : (r : ℝ) = (j : ℝ) + (n : ℝ) - (k : ℝ) := by
          rw [hr_val]; zify [show k ≤ j + n by omega]
        rw [hr_real]; field_simp; ring
      rw [harg, Real.cos_add_two_pi]
  have hdist_sq : dist (regPt n j) (regPt n k) ^ 2 =
      (2 * Real.sin (Real.pi * (r : ℝ) / n)) ^ 2 := by
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Fin.sum_univ_two]
    have h0 : dist (regPt n j 0) (regPt n k 0) =
        |Real.cos (2 * Real.pi * j / n) - Real.cos (2 * Real.pi * k / n)| := by
      simp [regPt, Real.dist_eq]
    have h1 : dist (regPt n j 1) (regPt n k 1) =
        |Real.sin (2 * Real.pi * j / n) - Real.sin (2 * Real.pi * k / n)| := by
      simp [regPt, Real.dist_eq]
    rw [h0, h1, sq_abs, sq_abs]
    have htrig :
        (Real.cos (2 * Real.pi * j / n) - Real.cos (2 * Real.pi * k / n)) ^ 2 +
        (Real.sin (2 * Real.pi * j / n) - Real.sin (2 * Real.pi * k / n)) ^ 2 =
        2 - 2 * Real.cos (2 * Real.pi * j / n - 2 * Real.pi * k / n) := by
      rw [Real.cos_sub]
      have hsc1 := Real.sin_sq_add_cos_sq (2 * Real.pi * j / n)
      have hsc2 := Real.sin_sq_add_cos_sq (2 * Real.pi * k / n)
      nlinarith
    rw [htrig, hcos_eq]
    have hhalf : 2 * Real.pi * (r : ℝ) / n = 2 * (Real.pi * (r : ℝ) / n) := by ring
    rw [hhalf, Real.cos_two_mul']
    have hsc := Real.sin_sq_add_cos_sq (Real.pi * (r : ℝ) / n)
    linarith
  have hsin_nonneg : 0 ≤ Real.sin (Real.pi * (r : ℝ) / n) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · have hr_le : (r : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (le_of_lt hr_lt)
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      rw [div_le_iff₀ hn_pos]
      nlinarith [Real.pi_pos]
  exact (sq_eq_sq₀ dist_nonneg (by positivity)).mp hdist_sq

private lemma regPt_inj {n j k : ℕ} (hn : 0 < n) (hj : j < n) (hk : k < n)
    (heq : regPt n j = regPt n k) : j = k := by
  by_contra hne
  have hdist : dist (regPt n j) (regPt n k) = 0 := by rw [heq, dist_self]
  rw [regPt_dist n j k hn hj hk] at hdist
  set r := (j + n - k) % n
  have hr_pos : 0 < r := by
    dsimp [r]
    by_contra h0
    have h0' : (j + n - k) % n = 0 := by omega
    by_cases hkj : k ≤ j
    · have h1 : j + n - k = (j - k) + n := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h0'
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at h0'
      omega
  have hr_lt : r < n := Nat.mod_lt _ hn
  have hsin_pos : 0 < Real.sin (Real.pi * (r : ℝ) / n) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr_pos
      have : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      positivity
    · have hr_lt_r : (r : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hr_lt
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      rw [div_lt_iff₀ hn_pos]
      nlinarith [Real.pi_pos]
  linarith

private lemma sin_chord_inj {n d₁ d₂ : ℕ} (hn : 0 < n)
    (hd1 : d₁ ∈ Finset.Icc 1 (n / 2)) (hd2 : d₂ ∈ Finset.Icc 1 (n / 2))
    (heq : 2 * Real.sin (Real.pi * (d₁ : ℝ) / n) = 2 * Real.sin (Real.pi * (d₂ : ℝ) / n)) :
    d₁ = d₂ := by
  have hsin : Real.sin (Real.pi * (d₁ : ℝ) / n) = Real.sin (Real.pi * (d₂ : ℝ) / n) := by linarith
  have hmem : ∀ d ∈ Finset.Icc 1 (n / 2),
      Real.pi * (d : ℝ) / n ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    constructor
    · have : (0 : ℝ) ≤ Real.pi * (d : ℝ) / n := by positivity
      linarith [Real.pi_pos]
    · have hd_le : 2 * (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 2 * d ≤ n by omega)
      rw [div_le_div_iff₀ hn_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [Real.pi_pos]
  have harg := Real.strictMonoOn_sin.injOn (hmem d₁ hd1) (hmem d₂ hd2) hsin
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  have hd_eq : (d₁ : ℝ) = (d₂ : ℝ) := by
    have := congrArg (fun x => x * (n : ℝ) / Real.pi) harg
    field_simp at this
    linarith
  exact_mod_cast hd_eq

private lemma chord_mem_distanceSet (n d : ℕ) (hd1 : 1 ≤ d) (hd2 : 2 * d ≤ n) :
    2 * Real.sin (Real.pi * (d : ℝ) / n) ∈ distanceSet (regularNGon n) := by
  have hn : 0 < n := by omega
  rw [distanceSet, Finset.mem_image]
  refine ⟨(regPt n d, regPt n 0), ?_, ?_⟩
  · rw [Finset.mem_offDiag]
    refine ⟨?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨d, Finset.mem_range.mpr (by omega), rfl⟩
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hn, rfl⟩
    · intro h
      have := regPt_inj hn (by omega) hn h
      omega
  · rw [regPt_dist n d 0 hn (by omega) hn]
    have hmod : (d + n - 0) % n = d := by
      have h1 : d + n - 0 = d + n := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]

private lemma mult_ge_n_of_two_mul_lt (n d : ℕ) (hd1 : 1 ≤ d) (hd2 : 2 * d < n) :
    n ≤ distanceMultiplicity (regularNGon n) (2 * Real.sin (Real.pi * (d : ℝ) / n)) := by
  have hn : 0 < n := by omega
  unfold distanceMultiplicity
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  set F := (regularNGon n).offDiag.filter fun pair =>
    dist pair.1 pair.2 = 2 * Real.sin (Real.pi * (d : ℝ) / n)
  let f1 : ℕ → ℝ² × ℝ² := fun j => (regPt n ((j + d) % n), regPt n j)
  let f2 : ℕ → ℝ² × ℝ² := fun j => (regPt n j, regPt n ((j + d) % n))
  let S1 := (Finset.range n).image f1
  let S2 := (Finset.range n).image f2
  have hS1_sub : S1 ⊆ F := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨j, hj, rfl⟩
    have hjlt : j < n := Finset.mem_range.mp hj
    have hjd_lt : (j + d) % n < n := Nat.mod_lt _ hn
    have hne_idx : (j + d) % n ≠ j := by
      intro heq
      by_cases hlt : j + d < n
      · rw [Nat.mod_eq_of_lt hlt] at heq; omega
      · have h1 : (j + d) % n = j + d - n := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [h1] at heq; omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨(j + d) % n, Finset.mem_range.mpr hjd_lt, rfl⟩
    · exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
    · intro h; exact hne_idx (regPt_inj hn hjd_lt hjlt h)
    · rw [regPt_dist n ((j + d) % n) j hn hjd_lt hjlt]
      have hmod : ((j + d) % n + n - j) % n = d := by
        by_cases hlt : j + d < n
        · rw [Nat.mod_eq_of_lt hlt]
          have h1 : j + d + n - j = d + n := by omega
          rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        · have h1 : (j + d) % n = j + d - n := by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          rw [h1]
          have h2 : j + d - n + n - j = d := by omega
          rw [h2, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
  have hS2_sub : S2 ⊆ F := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨j, hj, rfl⟩
    have h1 := hS1_sub (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    rw [Finset.mem_filter, Finset.mem_offDiag] at h1 ⊢
    exact ⟨⟨h1.1.2.1, h1.1.1, h1.1.2.2.symm⟩, by rw [dist_comm]; exact h1.2⟩
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rcases Finset.mem_image.mp hp1 with ⟨j1, hj1, rfl⟩
    rcases Finset.mem_image.mp hp2 with ⟨j2, hj2, hpair⟩
    have hj1lt : j1 < n := Finset.mem_range.mp hj1
    have hj2lt : j2 < n := Finset.mem_range.mp hj2
    have hfst : regPt n ((j1 + d) % n) = regPt n j2 := congrArg Prod.fst hpair.symm
    have hsnd : regPt n j1 = regPt n ((j2 + d) % n) := congrArg Prod.snd hpair.symm
    have he1 : (j1 + d) % n = j2 := regPt_inj hn (Nat.mod_lt _ hn) hj2lt hfst
    have he2 : j1 = (j2 + d) % n := regPt_inj hn hj1lt (Nat.mod_lt _ hn) hsnd
    have h2d : (j1 + 2 * d) % n = j1 % n := by
      calc (j1 + 2 * d) % n = ((j1 + d) + d) % n := by ring_nf
        _ = ((j1 + d) % n + d) % n := (Nat.mod_add_mod (j1 + d) n d).symm
        _ = (j2 + d) % n := by rw [he1]
        _ = j1 := he2.symm
        _ = j1 % n := (Nat.mod_eq_of_lt hj1lt).symm
    have h0 : 2 * d % n = 0 := by
      have hsub : (j1 + 2 * d) % n = (j1 % n + 2 * d % n) % n := Nat.add_mod _ _ _
      rw [h2d, Nat.mod_eq_of_lt hj1lt, Nat.mod_eq_of_lt hd2] at hsub
      by_cases hlt : j1 + 2 * d < n
      · rw [Nat.mod_eq_of_lt hlt] at hsub; omega
      · have h1 : (j1 + 2 * d) % n = j1 + 2 * d - n := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [h1] at hsub; omega
    rw [Nat.mod_eq_of_lt hd2] at h0
    omega
  have hcard1 : S1.card = n := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    have h2 : regPt n a = regPt n b := congrArg Prod.snd hab
    exact regPt_inj hn (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) h2
  have hcard2 : S2.card = n := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    have h1 : regPt n a = regPt n b := congrArg Prod.fst hab
    exact regPt_inj hn (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) h1
  calc n * 2 = S1.card + S2.card := by omega
    _ = (S1 ∪ S2).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ F.card := Finset.card_le_card (Finset.union_subset hS1_sub hS2_sub)

private lemma mult_ge_half_of_even (m : ℕ) (hm : 1 ≤ m) :
    m ≤ distanceMultiplicity (regularNGon (2 * m))
      (2 * Real.sin (Real.pi * (m : ℝ) / (2 * m : ℕ))) := by
  have hn : 0 < 2 * m := by omega
  unfold distanceMultiplicity
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  set F := (regularNGon (2 * m)).offDiag.filter fun pair =>
    dist pair.1 pair.2 = 2 * Real.sin (Real.pi * (m : ℝ) / (2 * m : ℕ))
  let f : ℕ → ℝ² × ℝ² := fun j => (regPt (2 * m) ((j + m) % (2 * m)), regPt (2 * m) j)
  let S := (Finset.range (2 * m)).image f
  have hS_sub : S ⊆ F := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨j, hj, rfl⟩
    have hjlt : j < 2 * m := Finset.mem_range.mp hj
    have hjm_lt : (j + m) % (2 * m) < 2 * m := Nat.mod_lt _ hn
    have hne_idx : (j + m) % (2 * m) ≠ j := by
      intro heq
      by_cases hlt : j + m < 2 * m
      · rw [Nat.mod_eq_of_lt hlt] at heq; omega
      · have h1 : (j + m) % (2 * m) = j + m - 2 * m := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [h1] at heq; omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨(j + m) % (2 * m), Finset.mem_range.mpr hjm_lt, rfl⟩
    · exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
    · intro h; exact hne_idx (regPt_inj hn hjm_lt hjlt h)
    · rw [regPt_dist (2 * m) ((j + m) % (2 * m)) j hn hjm_lt hjlt]
      have hmod : ((j + m) % (2 * m) + 2 * m - j) % (2 * m) = m := by
        by_cases hlt : j + m < 2 * m
        · rw [Nat.mod_eq_of_lt hlt]
          have h1 : j + m + 2 * m - j = m + 2 * m := by omega
          rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        · have h1 : (j + m) % (2 * m) = j + m - 2 * m := by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          rw [h1]
          have h2 : j + m - 2 * m + 2 * m - j = m := by omega
          rw [h2, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
  have hcard : S.card = 2 * m := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    have h2 : regPt (2 * m) a = regPt (2 * m) b := congrArg Prod.snd hab
    exact regPt_inj hn (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) h2
  calc m * 2 = S.card := by omega
    _ ≤ F.card := Finset.card_le_card hS_sub

end Erdos94R1H1Proof

open Erdos94R1H1Proof in
theorem OMA.solution : OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1.H1 := by
  intro n
  have hsum_nonneg : ∀ s : Finset ℝ,
      0 ≤ ∑ u ∈ s, (distanceMultiplicity (regularNGon n) u : ℝ) ^ 2 :=
    fun s => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hsum_nonneg]
  · let u : ℕ → ℝ := fun d => 2 * Real.sin (Real.pi * (d : ℝ) / n)
    have hu_sub : (Finset.Icc 1 (n / 2)).image u ⊆ distanceSet (regularNGon n) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨d, hd, rfl⟩
      rw [Finset.mem_Icc] at hd
      exact chord_mem_distanceSet n d hd.1 (by omega)
    have hu_inj : Set.InjOn u (Finset.Icc 1 (n / 2) : Set ℕ) := by
      intro d₁ hd1 d₂ hd2 heq
      exact sin_chord_inj hn hd1 hd2 heq
    have hstep1 :
        ∑ d ∈ Finset.Icc 1 (n / 2), (distanceMultiplicity (regularNGon n) (u d) : ℝ) ^ 2 ≤
          ∑ x ∈ distanceSet (regularNGon n), (distanceMultiplicity (regularNGon n) x : ℝ) ^ 2 := by
      rw [← Finset.sum_image (f := fun x => (distanceMultiplicity (regularNGon n) x : ℝ) ^ 2) hu_inj]
      exact Finset.sum_le_sum_of_subset_of_nonneg hu_sub (fun _ _ _ => sq_nonneg _)
    split_ifs with hodd
    · have hge : (n : ℝ) ^ 2 * ((n : ℝ) - 1) / 2 ≤
          ∑ d ∈ Finset.Icc 1 (n / 2), (distanceMultiplicity (regularNGon n) (u d) : ℝ) ^ 2 := by
        calc
          (n : ℝ) ^ 2 * ((n : ℝ) - 1) / 2
              = ∑ _d ∈ Finset.Icc 1 (n / 2), (n : ℝ) ^ 2 := by
                rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
                have hdiv : ((n / 2 + 1 - 1 : ℕ) : ℝ) = ((n : ℝ) - 1) / 2 := by
                  have h1 : 2 * (n / 2) + 1 = n := by omega
                  have h1r : 2 * ((n / 2 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast h1
                  have h2 : n / 2 + 1 - 1 = n / 2 := by omega
                  rw [h2]; linarith
                rw [hdiv]; ring
          _ ≤ ∑ d ∈ Finset.Icc 1 (n / 2),
                (distanceMultiplicity (regularNGon n) (u d) : ℝ) ^ 2 := by
                refine Finset.sum_le_sum fun d hd => ?_
                rw [Finset.mem_Icc] at hd
                have h2d : 2 * d < n := by omega
                have hmult : (n : ℝ) ≤ (distanceMultiplicity (regularNGon n) (u d) : ℝ) :=
                  Nat.cast_le.mpr (mult_ge_n_of_two_mul_lt n d hd.1 h2d)
                nlinarith
      exact hge.trans hstep1
    · have heven : n % 2 = 0 := by omega
      obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
      have hm : 1 ≤ m := by omega
      have hsplit : Finset.Icc 1 (2 * m / 2) = insert m (Finset.Icc 1 (m - 1)) := by
        have h1 : 2 * m / 2 = m := by omega
        rw [h1]
        ext d
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hm_not_mem : m ∉ Finset.Icc 1 (m - 1) := by
        simp only [Finset.mem_Icc]; omega
      have hge : ((2 * m : ℕ) : ℝ) ^ 3 / 2 - 3 * ((2 * m : ℕ) : ℝ) ^ 2 / 4 ≤
          ∑ d ∈ Finset.Icc 1 (2 * m / 2),
            (distanceMultiplicity (regularNGon (2 * m)) (u d) : ℝ) ^ 2 := by
        rw [hsplit, Finset.sum_insert hm_not_mem]
        have hterm_m : (m : ℝ) ^ 2 ≤
            (distanceMultiplicity (regularNGon (2 * m)) (u m) : ℝ) ^ 2 := by
          have h1 : (m : ℝ) ≤ (distanceMultiplicity (regularNGon (2 * m)) (u m) : ℝ) :=
            Nat.cast_le.mpr (mult_ge_half_of_even m hm)
          nlinarith
        have hsum_rest : ((m - 1 : ℕ) : ℝ) * ((2 * m : ℕ) : ℝ) ^ 2 ≤
            ∑ d ∈ Finset.Icc 1 (m - 1),
              (distanceMultiplicity (regularNGon (2 * m)) (u d) : ℝ) ^ 2 := by
          calc
            ((m - 1 : ℕ) : ℝ) * ((2 * m : ℕ) : ℝ) ^ 2
                = ∑ _d ∈ Finset.Icc 1 (m - 1), ((2 * m : ℕ) : ℝ) ^ 2 := by
                  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
                  have h1 : m - 1 + 1 - 1 = m - 1 := by omega
                  rw [h1]
            _ ≤ ∑ d ∈ Finset.Icc 1 (m - 1),
                  (distanceMultiplicity (regularNGon (2 * m)) (u d) : ℝ) ^ 2 := by
                  refine Finset.sum_le_sum fun d hd => ?_
                  rw [Finset.mem_Icc] at hd
                  have h2d : 2 * d < 2 * m := by omega
                  have hmult : ((2 * m : ℕ) : ℝ) ≤
                      (distanceMultiplicity (regularNGon (2 * m)) (u d) : ℝ) :=
                    Nat.cast_le.mpr (mult_ge_n_of_two_mul_lt (2 * m) d hd.1 h2d)
                  nlinarith
        have halg : ((2 * m : ℕ) : ℝ) ^ 3 / 2 - 3 * ((2 * m : ℕ) : ℝ) ^ 2 / 4 =
            (m : ℝ) ^ 2 + ((m - 1 : ℕ) : ℝ) * ((2 * m : ℕ) : ℝ) ^ 2 := by
          rw [Nat.cast_sub hm]
          push_cast
          ring
        linarith
      exact hge.trans hstep1
