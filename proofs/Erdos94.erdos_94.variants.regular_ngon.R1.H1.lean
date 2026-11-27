import OMAReductions.R_Erdos94_erdos_94_variants_regular_ngon_R1

-- Step Erdos94.erdos_94.variants.regular_ngon.R1.H1: hypothesis H1 of reduction Erdos94.erdos_94.variants.regular_ngon.R1
-- Credit: @tatashbar
-- H1 := ∀ n : ℕ,     (if n % 2 = 1 then (n : ℝ) ^ 2 * ((n : ℝ) - 1) / 2       else (n : ℝ) ^ 3 / 2 - 3 * (n : ℝ) ^ 2 / 4) ≤       ∑ u ∈ distanceSet (regularNGon n), (distanceMultiplicity (regularNGon n) u : ℝ) ^ 2  -- If no distance occurs more than n times, the bound B(n) holds (no convexity needed).

open Real Finset

namespace OMA_Erdos94_H1

noncomputable def pt (n k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.cos (2 * Real.pi * k / n), Real.sin (2 * Real.pi * k / n)]

noncomputable def g (n k : ℕ) : ℝ := √(2 - 2 * Real.cos (2 * π * k / n))

lemma dist_pt (n i j : ℕ) :
    dist (pt n i) (pt n j) = √(2 - 2 * Real.cos (2 * π * ((i : ℝ) - j) / n)) := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  simp [pt, Fin.sum_univ_two]
  have : 2 * π * ((i:ℝ) - j) / n = 2 * π * i / n - 2 * π * j / n := by ring
  rw [this, Real.cos_sub]
  simp only [Real.dist_eq, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq (2 * π * i / n), Real.sin_sq_add_cos_sq (2 * π * j / n)]

lemma norm_pt (n k : ℕ) : ‖pt n k‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [pt, Fin.sum_univ_two]

lemma cos_sym (n e : ℕ) (he : e ≤ n) :
    Real.cos (2 * π * ((n - e : ℕ) : ℝ) / n) = Real.cos (2 * π * (e : ℝ) / n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [Nat.cast_sub he]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have : 2 * π * ((n : ℝ) - e) / n = -(2 * π * (e : ℝ) / n) + 2 * π := by
    field_simp; ring
  rw [this, Real.cos_add_two_pi, Real.cos_neg]

lemma dist_eq_g (n i j : ℕ) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    ∃ k ∈ Icc 1 (n / 2), dist (pt n i) (pt n j) = g n k := by
  -- reduce to e = |i - j|
  obtain ⟨e, he1, he2, hce⟩ : ∃ e : ℕ, 1 ≤ e ∧ e < n ∧
      Real.cos (2 * π * ((i : ℝ) - j) / n) = Real.cos (2 * π * (e : ℝ) / n) := by
    rcases lt_or_gt_of_ne hij with h | h
    · refine ⟨j - i, by omega, by omega, ?_⟩
      rw [Nat.cast_sub h.le, ← Real.cos_neg]
      congr 1; ring
    · refine ⟨i - j, by omega, by omega, ?_⟩
      rw [Nat.cast_sub h.le]
  rw [dist_pt, hce]
  by_cases hle : e ≤ n / 2
  · exact ⟨e, mem_Icc.2 ⟨he1, hle⟩, rfl⟩
  · refine ⟨n - e, mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
    rw [g, cos_sym n e he2.le]

lemma g_pos (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n / 2) : 0 < g n k := by
  have hn : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : 0 < 2 * π * k / n := by
    have : (0:ℝ) < k := by exact_mod_cast hk
    positivity
  have h2 : 2 * π * k / n ≤ π := by
    rw [div_le_iff₀ hn']
    have : (2 * k : ℝ) ≤ n := by exact_mod_cast (by omega : 2 * k ≤ n)
    nlinarith [Real.pi_pos]
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) h2 h1
  rw [Real.cos_zero] at this
  exact Real.sqrt_pos.2 (by linarith)

lemma g_ne_two (m k : ℕ) (hk : 1 ≤ k) (hkm : k < m) : g (2 * m) k ≠ 2 := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h1 : 0 ≤ 2 * π * k / ((2 * m : ℕ) : ℝ) := by positivity
  have h2 : 2 * π * k / ((2 * m : ℕ) : ℝ) < π := by
    push_cast
    rw [div_lt_iff₀ (by positivity)]
    have : (k : ℝ) < m := by exact_mod_cast hkm
    nlinarith [Real.pi_pos]
  have := Real.cos_lt_cos_of_nonneg_of_le_pi h1 le_rfl h2
  rw [Real.cos_pi] at this
  intro h
  rw [g] at h
  have h4 : 2 - 2 * Real.cos (2 * π * k / ((2 * m : ℕ) : ℝ)) = 4 := by
    have h0 : 0 ≤ 2 - 2 * Real.cos (2 * π * k / ((2 * m : ℕ) : ℝ)) := by
      nlinarith [Real.cos_le_one (2 * π * k / ((2 * m : ℕ) : ℝ))]
    have := Real.sq_sqrt h0
    rw [h] at this; linarith
  linarith

lemma g_half (m : ℕ) (hm : 0 < m) : g (2 * m) m = 2 := by
  have : 2 * π * (m : ℝ) / ((2 * m : ℕ) : ℝ) = π := by
    have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast; field_simp
  rw [g, this, Real.cos_pi]
  rw [show (2 : ℝ) - 2 * -1 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

noncomputable def Pn (n : ℕ) : Finset (EuclideanSpace ℝ (Fin 2)) := (range n).image (pt n)

lemma pt_inj (n i j : ℕ) (hi : i < n) (hj : j < n) (h : pt n i = pt n j) : i = j := by
  by_contra hij
  obtain ⟨k, hk, hd⟩ := dist_eq_g n i j hi hj hij
  rw [mem_Icc] at hk
  have := g_pos n k hk.1 hk.2
  rw [← hd, h, dist_self] at this
  exact lt_irrefl _ this

lemma card_Pn (n : ℕ) : (Pn n).card = n := by
  rw [Pn, card_image_of_injOn, card_range]
  intro i hi j hj h
  exact pt_inj n i j (mem_range.1 hi) (mem_range.1 hj) h

lemma distanceSet_sub (n : ℕ) : distanceSet (Pn n) ⊆ (Icc 1 (n / 2)).image (g n) := by
  intro u hu
  rw [distanceSet, mem_image] at hu
  obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hu
  obtain ⟨hx, hy, hne⟩ := mem_offDiag.1 hxy
  obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hy
  have hij : i ≠ j := fun h => hne (h ▸ rfl)
  obtain ⟨k, hk, hd⟩ := dist_eq_g n i j (mem_range.1 hi) (mem_range.1 hj) hij
  exact mem_image.2 ⟨k, hk, hd.symm⟩

lemma card_D (n : ℕ) : (distanceSet (Pn n)).card ≤ n / 2 :=
  (card_le_card (distanceSet_sub n)).trans (card_image_le.trans (by simp))

lemma card_D_ne_two (m : ℕ) :
    ((distanceSet (Pn (2 * m))).filter (fun u => u ≠ 2)).card ≤ m - 1 := by
  have hsub : (distanceSet (Pn (2 * m))).filter (fun u => u ≠ 2) ⊆
      (Icc 1 (m - 1)).image (g (2 * m)) := by
    intro u hu
    obtain ⟨hu, hu2⟩ := mem_filter.1 hu
    obtain ⟨k, hk, rfl⟩ := mem_image.1 (distanceSet_sub _ hu)
    rw [mem_Icc] at hk
    have hkm : k ≤ m := by omega
    rcases lt_or_eq_of_le hkm with hlt | rfl
    · exact mem_image.2 ⟨k, mem_Icc.2 ⟨hk.1, by omega⟩, rfl⟩
    · exact absurd (g_half k (by omega)) hu2
  exact (card_le_card hsub).trans (card_image_le.trans (by simp))

lemma norm_of_mem (n : ℕ) {x} (hx : x ∈ Pn n) : ‖x‖ = 1 := by
  obtain ⟨k, -, rfl⟩ := mem_image.1 hx
  exact norm_pt n k

lemma antipode {x y : EuclideanSpace ℝ (Fin 2)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (h : dist x y = 2) : y = -x := by
  rw [dist_eq_norm] at h
  have h1 := norm_sub_sq_real x y
  have h2 := norm_add_sq_real x y
  rw [h, hx, hy] at h1
  rw [hx, hy] at h2
  have : ‖x + y‖ ^ 2 = 0 := by linarith
  have : x + y = 0 := by simpa using this
  exact (neg_eq_of_add_eq_zero_right this).symm

lemma mult_two (n : ℕ) : distanceMultiplicity (Pn n) 2 ≤ n / 2 := by
  unfold distanceMultiplicity
  apply Nat.div_le_div_right
  refine le_trans ?_ (card_Pn n).le
  apply card_le_card_of_injOn Prod.fst
  · intro p hp
    exact (mem_offDiag.1 (mem_filter.1 hp).1).1
  · intro p hp q hq hpq
    obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
    obtain ⟨hq1, hq2⟩ := mem_filter.1 hq
    obtain ⟨hpx, hpy, -⟩ := mem_offDiag.1 hp1
    obtain ⟨hqx, hqy, -⟩ := mem_offDiag.1 hq1
    have e1 := antipode (norm_of_mem n hpx) (norm_of_mem n hpy) hp2
    have e2 := antipode (norm_of_mem n hqx) (norm_of_mem n hqy) hq2
    have hpq' : p.1 = q.1 := hpq
    exact Prod.ext hpq' (by rw [e1, e2, hpq'])

lemma sum_M (n : ℕ) :
    ∑ u ∈ distanceSet (Pn n), (distanceMultiplicity (Pn n) u : ℝ) = n * (n - 1) / 2 := by
  have := sum_distanceMultiplicity (Pn n)
  rw [card_Pn] at this
  rw [← Nat.cast_sum, this, Nat.cast_choose_two ℝ n]

theorem bound (n : ℕ) :
    (if n % 2 = 1 then (n : ℝ) ^ 2 * ((n : ℝ) - 1) / 2
      else (n : ℝ) ^ 3 / 2 - 3 * (n : ℝ) ^ 2 / 4) ≤
      ∑ u ∈ distanceSet (Pn n), (distanceMultiplicity (Pn n) u : ℝ) ^ 2 := by
  set D := distanceSet (Pn n) with hD
  set M : ℝ → ℝ := fun u => (distanceMultiplicity (Pn n) u : ℝ) with hM
  have hS : ∑ u ∈ D, M u = n * (n - 1) / 2 := sum_M n
  have hX0 : 0 ≤ ∑ u ∈ D, M u ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  change _ ≤ ∑ u ∈ D, M u ^ 2
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · -- even case n = 2m
    have hif : ¬ (2 * m % 2 = 1) := by omega
    rw [if_neg hif]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa using hX0
    have hsplit := sum_filter_add_sum_filter_not D (fun u => u = 2) M
    have hsplit2 := sum_filter_add_sum_filter_not D (fun u => u = 2) (fun u => M u ^ 2)
    set F2 := D.filter (fun u => u = 2)
    set Fn := D.filter (fun u => ¬ u = 2)
    have hF2 : F2 ⊆ {2} := fun u hu => by simpa using (mem_filter.1 hu).2
    have hMnn : ∀ u, 0 ≤ M u := fun u => Nat.cast_nonneg _
    set b := ∑ u ∈ F2, M u
    set a := ∑ u ∈ Fn, M u
    set Y := ∑ u ∈ F2, M u ^ 2
    set X := ∑ u ∈ Fn, M u ^ 2
    have hb0 : 0 ≤ b := sum_nonneg (fun u _ => hMnn u)
    have hX0' : 0 ≤ X := sum_nonneg (fun _ _ => sq_nonneg _)
    have hY0 : 0 ≤ Y := sum_nonneg (fun _ _ => sq_nonneg _)
    have hbm : b ≤ m := by
      have h1 : b ≤ ∑ u ∈ ({2} : Finset ℝ), M u :=
        sum_le_sum_of_subset_of_nonneg hF2 (fun u _ _ => hMnn u)
      rw [sum_singleton] at h1
      have h2 := mult_two (2 * m)
      have h3 : M 2 ≤ m := by
        simp only [hM]; exact_mod_cast (h2.trans (by omega))
      linarith
    have hYb : b ^ 2 ≤ Y := by
      have h1 := sq_sum_le_card_mul_sum_sq (s := F2) (f := M)
      have h2 : (F2.card : ℝ) ≤ 1 := by
        have := card_le_card hF2; rw [card_singleton] at this; exact_mod_cast this
      nlinarith
    have hXa : a ^ 2 ≤ ((m : ℝ) - 1) * X := by
      have h1 := sq_sum_le_card_mul_sum_sq (s := Fn) (f := M)
      have h2 : (Fn.card : ℝ) ≤ (m : ℝ) - 1 := by
        have := card_D_ne_two m
        have h3 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [← h3]; exact_mod_cast this
      nlinarith
    have hab : b + a = m * (2 * m - 1) := by
      rw [hsplit, hS]; push_cast; ring
    rw [← hsplit2]
    push_cast
    rcases Nat.lt_or_ge m 2 with hm1 | hm2
    · have hm1' : m = 1 := by omega
      subst hm1'
      simp at hXa hab ⊢
      have ha : a = 0 := by nlinarith [sq_nonneg a]
      have hb : b = 1 := by linarith
      rw [hb] at hYb
      norm_num at hYb ⊢
      linarith
    · have hm2' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
      have hc : 0 < (m : ℝ) - 1 := by linarith
      have hident : a = m * (2 * m - 1) - b := by linarith
      have hpos : 0 ≤ ((m : ℝ) - b) * (3 * m ^ 2 - 2 * m - m * b) := by
        apply mul_nonneg <;> nlinarith
      have hcY : ((m : ℝ) - 1) * b ^ 2 ≤ ((m : ℝ) - 1) * Y :=
        mul_le_mul_of_nonneg_left hYb hc.le
      have key : ((m : ℝ) - 1) * (4 * m ^ 3 - 3 * m ^ 2) ≤ ((m : ℝ) - 1) * (Y + X) := by
        rw [hident] at hXa
        nlinarith
      have := le_of_mul_le_mul_left key hc
      nlinarith
  · -- odd case n = 2m+1
    have hif : (2 * m + 1) % 2 = 1 := by omega
    rw [if_pos hif]
    have h1 := sq_sum_le_card_mul_sum_sq (s := D) (f := M)
    have h2 : (D.card : ℝ) ≤ m := by
      have := card_D (2 * m + 1)
      exact_mod_cast this.trans (by omega)
    rw [hS] at h1
    push_cast at h1 ⊢
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa using hX0
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have h3 : (m : ℝ) * ((2 * m + 1) ^ 2 * m) ≤ m * ∑ u ∈ D, M u ^ 2 := by
      nlinarith
    have := le_of_mul_le_mul_left h3 hm'
    nlinarith

end OMA_Erdos94_H1

theorem OMA.solution : OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1.H1 := by
  intro n
  exact OMA_Erdos94_H1.bound n
