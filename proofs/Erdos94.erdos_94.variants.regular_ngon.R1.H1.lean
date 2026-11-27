import OMAReductions.R_Erdos94_erdos_94_variants_regular_ngon_R1

-- Step Erdos94.erdos_94.variants.regular_ngon.R1.H1: hypothesis H1 of reduction Erdos94.erdos_94.variants.regular_ngon.R1
-- Credit: @OrangeHeadz

/-! # The regular n-gon reaches the value B(n)

Write f(u) for the multiplicity of the distance u in the regular n-gon, S for the sum of the
f(u)^2 and T for the sum of the f(u), so T = n (n - 1) / 2.
The vertices are n distinct points of the unit circle, and the distance between vertices k and l
is sqrt (2 - 2 cos (2 pi (k - l) / n)), which only depends on min(|k - l|, n - |k - l|).
So there are at most n / 2 distinct distances.
* Odd n = 2 m + 1: Cauchy-Schwarz gives T^2 <= m S, hence S >= n^2 (n - 1) / 2.
* Even n = 2 m: the distance 2 (diameters) occurs x <= m times, because the only unit vector at
  distance 2 from a unit vector p is -p. The other distances take at most m - 1 values, so
  Cauchy-Schwarz gives (T - x)^2 <= (m - 1) (S - x^2), hence S >= n^3 / 2 - 3 n^2 / 4. -/

namespace OMA94H1

open EuclideanGeometry Erdos94

theorem dist_pt (a b : ℝ) :
    dist (!₂[Real.cos a, Real.sin a] : ℝ²) !₂[Real.cos b, Real.sin b]
      = Real.sqrt (2 - 2 * Real.cos (a - b)) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  congr 1
  simp only [Real.dist_eq, sq_abs]
  simp
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b]

theorem norm_pt (a : ℝ) : ‖(!₂[Real.cos a, Real.sin a] : ℝ²)‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp

theorem pt_inj (n k l : ℕ) (hk : k < n) (hl : l < n)
    (h : (!₂[Real.cos (2 * Real.pi * k / n), Real.sin (2 * Real.pi * k / n)] : ℝ²)
      = !₂[Real.cos (2 * Real.pi * l / n), Real.sin (2 * Real.pi * l / n)]) : k = l := by
  have hd := dist_pt (2 * Real.pi * k / n) (2 * Real.pi * l / n)
  rw [h, dist_self] at hd
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
  have hkr : (k : ℝ) < n := by exact_mod_cast hk
  have hlr : (l : ℝ) < n := by exact_mod_cast hl
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hpi := Real.pi_pos
  have hcos : Real.cos (2 * Real.pi * k / n - 2 * Real.pi * l / n) = 1 := by
    have h2 : 2 - 2 * Real.cos (2 * Real.pi * k / n - 2 * Real.pi * l / n) ≤ 0 :=
      Real.sqrt_eq_zero'.mp hd.symm
    linarith [Real.cos_le_one (2 * Real.pi * k / n - 2 * Real.pi * l / n)]
  have ha1 : 2 * Real.pi * k / n < 2 * Real.pi := by
    rw [div_lt_iff₀ hn]; nlinarith
  have ha0 : 0 ≤ 2 * Real.pi * k / n := by positivity
  have hb1 : 2 * Real.pi * l / n < 2 * Real.pi := by
    rw [div_lt_iff₀ hn]; nlinarith
  have hb0 : 0 ≤ 2 * Real.pi * l / n := by positivity
  have hx : 2 * Real.pi * k / n - 2 * Real.pi * l / n = 0 :=
    (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) (by linarith)).mp hcos
  have h3 := sub_eq_zero.mp hx
  rw [div_left_inj' hn.ne'] at h3
  have h4 : (k : ℝ) = l := mul_left_cancel₀ (by positivity) h3
  exact_mod_cast h4

theorem card_ngon (n : ℕ) : (regularNGon n).card = n := by
  unfold regularNGon
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro k hk l hl h
  exact pt_inj n k l (Finset.mem_range.mp (Finset.mem_coe.mp hk))
    (Finset.mem_range.mp (Finset.mem_coe.mp hl)) h

theorem cos_fold (n t : ℕ) (h1 : 1 ≤ t) (h2 : t < n) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ n / 2 ∧
      Real.cos (2 * Real.pi * t / n) = Real.cos (2 * Real.pi * j / n) := by
  by_cases h : t ≤ n / 2
  · exact ⟨t, h1, h, rfl⟩
  · refine ⟨n - t, by omega, by omega, ?_⟩
    have hn : (n : ℝ) ≠ 0 := by
      have : 0 < n := by omega
      positivity
    rw [Nat.cast_sub h2.le]
    have h3 : 2 * Real.pi * ((n : ℝ) - t) / n = 2 * Real.pi - 2 * Real.pi * t / n := by
      field_simp
    rw [h3, Real.cos_two_pi_sub]

theorem cos_pair (n k l : ℕ) (hk : k < n) (hl : l < n) (hkl : k ≠ l) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ n / 2 ∧
      Real.cos (2 * Real.pi * k / n - 2 * Real.pi * l / n) = Real.cos (2 * Real.pi * j / n) := by
  rcases Nat.lt_or_gt_of_ne hkl with h | h
  · obtain ⟨j, h1, h2, h3⟩ := cos_fold n (l - k) (by omega) (by omega)
    refine ⟨j, h1, h2, ?_⟩
    rw [← h3, Nat.cast_sub h.le, ← Real.cos_neg]
    congr 1
    ring
  · obtain ⟨j, h1, h2, h3⟩ := cos_fold n (k - l) (by omega) (by omega)
    refine ⟨j, h1, h2, ?_⟩
    rw [← h3, Nat.cast_sub h.le]
    congr 1
    ring

theorem distSet_sub (n : ℕ) :
    distanceSet (regularNGon n) ⊆
      (Finset.Icc 1 (n / 2)).image
        (fun j : ℕ => Real.sqrt (2 - 2 * Real.cos (2 * Real.pi * j / n))) := by
  intro u hu
  unfold distanceSet at hu
  obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨hp, hq, hne⟩ := Finset.mem_offDiag.mp hpq
  unfold regularNGon at hp hq
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq
  have hkl : k ≠ l := fun h => hne (by rw [h])
  obtain ⟨j, h1, h2, h3⟩ :=
    cos_pair n k l (Finset.mem_range.mp hk) (Finset.mem_range.mp hl) hkl
  refine Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨h1, h2⟩, ?_⟩
  show Real.sqrt (2 - 2 * Real.cos (2 * Real.pi * j / n)) = _
  rw [← h3]
  exact (dist_pt _ _).symm

theorem card_distSet_le (n : ℕ) : (distanceSet (regularNGon n)).card ≤ n / 2 := by
  refine le_trans (Finset.card_le_card (distSet_sub n)) ?_
  refine le_trans Finset.card_image_le ?_
  simp

theorem d_half (n : ℕ) (hn : 0 < n) (he : n % 2 = 0) :
    Real.sqrt (2 - 2 * Real.cos (2 * Real.pi * ((n / 2 : ℕ) : ℝ) / n)) = 2 := by
  have h2 : ((n / 2 : ℕ) : ℝ) = (n : ℝ) / 2 := by
    have h3 : n = 2 * (n / 2) := by omega
    have h4 : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast h3
    linarith
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have h5 : 2 * Real.pi * ((n / 2 : ℕ) : ℝ) / n = Real.pi := by
    rw [h2]; field_simp
  rw [h5, Real.cos_pi]
  rw [show (2 : ℝ) - 2 * -1 = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem card_erase_le (n : ℕ) (hpos : 0 < n) (he : n % 2 = 0) :
    ((distanceSet (regularNGon n)).erase 2).card ≤ n / 2 - 1 := by
  have hsub : (distanceSet (regularNGon n)).erase 2 ⊆
      (Finset.Icc 1 (n / 2 - 1)).image
        (fun j : ℕ => Real.sqrt (2 - 2 * Real.cos (2 * Real.pi * j / n))) := by
    intro u hu
    obtain ⟨hne, hu'⟩ := Finset.mem_erase.mp hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (distSet_sub n hu')
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
    have hj2 : j ≠ n / 2 := by
      intro hj2
      apply hne
      rw [hj2]
      exact d_half n hpos he
    exact Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨h1, by omega⟩, rfl⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans Finset.card_image_le ?_
  simp

theorem norm_mem (n : ℕ) (p : ℝ²) (hp : p ∈ regularNGon n) : ‖p‖ = 1 := by
  unfold regularNGon at hp
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hp
  exact norm_pt _

theorem antipode (p q : ℝ²) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (h : dist p q = 2) : q = -p := by
  have h1 := parallelogram_law_with_norm ℝ p q
  rw [dist_eq_norm] at h
  rw [hp, hq, h] at h1
  have h2 : ‖p + q‖ = 0 := mul_self_eq_zero.mp (by linarith)
  have h3 : p + q = 0 := norm_eq_zero.mp h2
  exact (neg_eq_of_add_eq_zero_right h3).symm

theorem mult_two_le (n : ℕ) : distanceMultiplicity (regularNGon n) 2 ≤ n / 2 := by
  unfold distanceMultiplicity
  apply Nat.div_le_div_right
  have hle : ((regularNGon n).offDiag.filter
      fun (pair : ℝ² × ℝ²) => dist pair.1 pair.2 = 2).card ≤ (regularNGon n).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro a ha
      exact Finset.mem_coe.mpr
        (Finset.mem_offDiag.mp (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).1).1
    · intro a ha b hb hab
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
      obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
      obtain ⟨hap, haq, -⟩ := Finset.mem_offDiag.mp ha1
      obtain ⟨hbp, hbq, -⟩ := Finset.mem_offDiag.mp hb1
      have e1 := antipode a.1 a.2 (norm_mem n _ hap) (norm_mem n _ haq) ha2
      have e2 := antipode b.1 b.2 (norm_mem n _ hbp) (norm_mem n _ hbq) hb2
      exact Prod.ext hab (by rw [e1, e2, hab])
  rw [card_ngon] at hle
  exact hle

theorem mult_eq_zero (P : Finset ℝ²) (u : ℝ) (h : u ∉ distanceSet P) :
    distanceMultiplicity P u = 0 := by
  unfold distanceMultiplicity
  have h1 : (P.offDiag.filter fun (pair : ℝ² × ℝ²) => dist pair.1 pair.2 = u) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro pair hpair hd
    exact h (Finset.mem_image.mpr ⟨pair, hpair, hd⟩)
  rw [h1]
  simp

theorem sum_split (D : Finset ℝ) (g : ℝ → ℝ) (h : (2 : ℝ) ∉ D → g 2 = 0) :
    ∑ u ∈ D, g u = g 2 + ∑ u ∈ D.erase 2, g u := by
  by_cases h2 : (2 : ℝ) ∈ D
  · exact (Finset.add_sum_erase D g h2).symm
  · rw [Finset.erase_eq_of_notMem h2, h h2, zero_add]

theorem odd_ineq (m c S T : ℝ) (hm : 0 ≤ m) (hc : c ≤ m) (hS : 0 ≤ S)
    (hT : T = (2 * m + 1) * m) (hCS : T ^ 2 ≤ c * S) : (2 * m + 1) ^ 2 * m ≤ S := by
  rcases hm.eq_or_lt with h0 | hpos
  · rw [← h0]
    simpa using hS
  · have h1 : T ^ 2 ≤ m * S := le_trans hCS (mul_le_mul_of_nonneg_right hc hS)
    rw [hT] at h1
    have h2 : m * ((2 * m + 1) ^ 2 * m) ≤ m * S := by
      have h3 : ((2 * m + 1) * m) ^ 2 = m * ((2 * m + 1) ^ 2 * m) := by ring
      linarith
    exact le_of_mul_le_mul_left h2 hpos

theorem even_ineq (m c x S' T : ℝ) (hm : m = 1 ∨ 2 ≤ m) (hc : c ≤ m - 1)
    (hx : x ≤ m) (hS : 0 ≤ S') (hT : T = m * (2 * m - 1))
    (hCS : (T - x) ^ 2 ≤ c * S') :
    4 * m ^ 3 - 3 * m ^ 2 ≤ x ^ 2 + S' := by
  have h1 : (T - x) ^ 2 ≤ (m - 1) * S' := le_trans hCS (mul_le_mul_of_nonneg_right hc hS)
  rcases hm with hm1 | hm2
  · subst hm1
    have h2 : (T - x) ^ 2 ≤ 0 := by simpa using h1
    have h3 : T - x = 0 := by
      have h4 : (T - x) ^ 2 = 0 := le_antisymm h2 (sq_nonneg _)
      exact pow_eq_zero_iff (two_ne_zero) |>.mp h4
    have h5 : x = 1 := by rw [hT] at h3; linarith
    rw [h5]
    linarith
  · have hpos : 0 < m - 1 := by linarith
    have h3 : (m - 1) * (4 * m ^ 2 * (m - 1) + 4 * m * (m - x)) ≤ (m - 1) * S' := by
      refine le_trans ?_ h1
      rw [hT]
      nlinarith [sq_nonneg (m - x)]
    have h4 := le_of_mul_le_mul_left h3 hpos
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (by linarith : (0 : ℝ) ≤ 3 * m - x)]

theorem sum_real (n : ℕ) :
    ∑ u ∈ distanceSet (regularNGon n), (distanceMultiplicity (regularNGon n) u : ℝ)
      = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  have h := sum_distanceMultiplicity (regularNGon n)
  rw [card_ngon] at h
  have h' := congrArg (Nat.cast : ℕ → ℝ) h
  rw [Nat.cast_sum, Nat.cast_choose_two] at h'
  exact h'

theorem odd_case (n : ℕ) (h : n % 2 = 1) :
    (n : ℝ) ^ 2 * ((n : ℝ) - 1) / 2 ≤
      ∑ u ∈ distanceSet (regularNGon n), (distanceMultiplicity (regularNGon n) u : ℝ) ^ 2 := by
  have hn2 : n = 2 * (n / 2) + 1 := by omega
  have hn : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hn2
  have hCS := sq_sum_le_card_mul_sum_sq (s := distanceSet (regularNGon n))
    (f := fun u => (distanceMultiplicity (regularNGon n) u : ℝ))
  rw [sum_real] at hCS
  have hc : ((distanceSet (regularNGon n)).card : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by
    exact_mod_cast card_distSet_le n
  have hT : (n : ℝ) * ((n : ℝ) - 1) / 2
      = (2 * ((n / 2 : ℕ) : ℝ) + 1) * ((n / 2 : ℕ) : ℝ) := by
    rw [hn]; ring
  have key := odd_ineq ((n / 2 : ℕ) : ℝ) _ _ ((n : ℝ) * ((n : ℝ) - 1) / 2)
    (Nat.cast_nonneg _) hc (Finset.sum_nonneg fun u _ => sq_nonneg _) hT hCS
  have hgoal : (n : ℝ) ^ 2 * ((n : ℝ) - 1) / 2
      = (2 * ((n / 2 : ℕ) : ℝ) + 1) ^ 2 * ((n / 2 : ℕ) : ℝ) := by
    rw [hn]; ring
  rw [hgoal]
  exact key

theorem even_case (n : ℕ) (h : ¬ n % 2 = 1) :
    (n : ℝ) ^ 3 / 2 - 3 * (n : ℝ) ^ 2 / 4 ≤
      ∑ u ∈ distanceSet (regularNGon n), (distanceMultiplicity (regularNGon n) u : ℝ) ^ 2 := by
  have hS0 : 0 ≤ ∑ u ∈ distanceSet (regularNGon n),
      (distanceMultiplicity (regularNGon n) u : ℝ) ^ 2 :=
    Finset.sum_nonneg fun u _ => sq_nonneg _
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · have hz : (n : ℝ) = 0 := by exact_mod_cast h0
    rw [hz]
    norm_num
    exact hS0
  · have he : n % 2 = 0 := by omega
    have hn2 : n = 2 * (n / 2) := by omega
    have hn : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hn2
    have hm1 : 1 ≤ n / 2 := by omega
    have hsplit1 := sum_split (distanceSet (regularNGon n))
      (fun u => (distanceMultiplicity (regularNGon n) u : ℝ))
      (fun h2 => by simp [mult_eq_zero _ _ h2])
    have hsplit2 := sum_split (distanceSet (regularNGon n))
      (fun u => (distanceMultiplicity (regularNGon n) u : ℝ) ^ 2)
      (fun h2 => by simp [mult_eq_zero _ _ h2])
    rw [sum_real] at hsplit1
    have hCS := sq_sum_le_card_mul_sum_sq (s := (distanceSet (regularNGon n)).erase 2)
      (f := fun u => (distanceMultiplicity (regularNGon n) u : ℝ))
    have hc : (((distanceSet (regularNGon n)).erase 2).card : ℝ) ≤ ((n / 2 : ℕ) : ℝ) - 1 := by
      have h1 := card_erase_le n hpos he
      have h2 : (((distanceSet (regularNGon n)).erase 2).card : ℝ) ≤ ((n / 2 - 1 : ℕ) : ℝ) := by
        exact_mod_cast h1
      rw [Nat.cast_sub hm1] at h2
      simpa using h2
    have hx : (distanceMultiplicity (regularNGon n) 2 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by
      exact_mod_cast mult_two_le n
    have hm : ((n / 2 : ℕ) : ℝ) = 1 ∨ 2 ≤ ((n / 2 : ℕ) : ℝ) := by
      rcases hm1.eq_or_lt with h1 | h1
      · left
        rw [← h1]
        simp
      · right
        exact_mod_cast h1
    have hT : (n : ℝ) * ((n : ℝ) - 1) / 2
        = ((n / 2 : ℕ) : ℝ) * (2 * ((n / 2 : ℕ) : ℝ) - 1) := by
      rw [hn]; ring
    have hCS' : ((n : ℝ) * ((n : ℝ) - 1) / 2 - (distanceMultiplicity (regularNGon n) 2 : ℝ)) ^ 2
        ≤ (((distanceSet (regularNGon n)).erase 2).card : ℝ) *
          ∑ u ∈ (distanceSet (regularNGon n)).erase 2,
            (distanceMultiplicity (regularNGon n) u : ℝ) ^ 2 := by
      have h1 : (n : ℝ) * ((n : ℝ) - 1) / 2 - (distanceMultiplicity (regularNGon n) 2 : ℝ)
          = ∑ u ∈ (distanceSet (regularNGon n)).erase 2,
            (distanceMultiplicity (regularNGon n) u : ℝ) := by
        linarith
      rw [h1]
      exact hCS
    have key := even_ineq ((n / 2 : ℕ) : ℝ) _ (distanceMultiplicity (regularNGon n) 2 : ℝ)
      _ ((n : ℝ) * ((n : ℝ) - 1) / 2) hm hc hx
      (Finset.sum_nonneg fun u _ => sq_nonneg _) hT hCS'
    have hgoal : (n : ℝ) ^ 3 / 2 - 3 * (n : ℝ) ^ 2 / 4
        = 4 * ((n / 2 : ℕ) : ℝ) ^ 3 - 3 * ((n / 2 : ℕ) : ℝ) ^ 2 := by
      rw [hn]; ring
    rw [hgoal, hsplit2]
    exact key

end OMA94H1

theorem OMA.solution : OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1.H1 := by
  intro n
  split_ifs with h
  · exact OMA94H1.odd_case n h
  · exact OMA94H1.even_case n h
