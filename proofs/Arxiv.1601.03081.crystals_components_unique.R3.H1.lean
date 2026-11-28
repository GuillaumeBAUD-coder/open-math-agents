import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R3

/-!
# Classification of sorted crystal decompositions via Vieta jumping

For odd `1 < a ≤ b` with `(a + 1)(b + 1) ∣ (a + b)²`, writing `a = 2u - 1`, `b = 2v - 1` gives
`(u + v - 1)² = q u v` with `2 ≤ u ≤ v`. Values `q ∈ {0, 1, 2}` are impossible; `q = 3` yields
`(5, 7)`; `q = 4` gives the parabolic family `a = 2j² + 4j + 1, b = 2j² + 8j + 7`; and for `q ≥ 5`,
Vieta jumping forces `q ≤ u`, yielding either the cubic family (`u = q`) or the sparse regime
`2q < a` (`q < u`).
-/

-- Step Arxiv.1601.03081.crystals_components_unique.R3.H1: hypothesis H1 of reduction Arxiv.1601.03081.crystals_components_unique.R3
-- Credit: @lettucrisp

open Arxiv.«1601.03081»

private lemma vieta_ge (q : ℕ) :
    ∀ u : ℕ, ∀ v : ℕ, 2 ≤ u → u ≤ v → (u + v - 1) ^ 2 = q * u * v → q ≤ u := by
  intro u
  induction u using Nat.strong_induction_on with
  | h u ih =>
    intro v hu huv heq
    by_contra hlt
    have huq : u < q := by omega
    have hZ : ((u : ℤ) + (v : ℤ) - 1) ^ 2 = (q : ℤ) * (u : ℤ) * (v : ℤ) := by
      have h1 : 1 ≤ u + v := by omega
      zify [h1] at heq
      exact heq
    let wZ : ℤ := ((q : ℤ) - 2) * (u : ℤ) + 2 - (v : ℤ)
    have hvw : (v : ℤ) * wZ = ((u : ℤ) - 1) ^ 2 := by
      dsimp [wZ]; nlinarith
    have hw_pos : 0 < wZ := by nlinarith
    have hw_lt : wZ < (u : ℤ) := by nlinarith
    have hw_ne1 : wZ ≠ 1 := by
      intro hw1
      have hv_eq : (v : ℤ) = ((u : ℤ) - 1) ^ 2 := by nlinarith
      have hqeq : ((q : ℤ) - 2) * (u : ℤ) = (u : ℤ) ^ 2 - 2 * (u : ℤ) := by
        dsimp [wZ] at hw1; nlinarith
      have : (u : ℤ) = (q : ℤ) := by nlinarith
      omega
    let w : ℕ := wZ.toNat
    have hw_cast : (w : ℤ) = wZ := Int.toNat_of_nonneg (by omega)
    have hw2 : 2 ≤ w := by omega
    have hwu : w < u := by omega
    have hweqZ : ((w : ℤ) + (u : ℤ) - 1) ^ 2 = (q : ℤ) * (w : ℤ) * (u : ℤ) := by
      rw [hw_cast]
      have hsum : (v : ℤ) + wZ = ((q : ℤ) - 2) * (u : ℤ) + 2 := by dsimp [wZ]; ring
      nlinarith
    have hweq : (w + u - 1) ^ 2 = q * w * u := by
      have h1 : 1 ≤ w + u := by omega
      zify [h1]
      exact hweqZ
    have hqlew : q ≤ w := ih w hwu u hw2 (by omega) hweq
    omega

theorem OMA.solution : OMA.R_Arxiv_1601_03081_crystals_components_unique_R3.H1 := by
  intro n a b hcr hab
  rw [isCrystalWithComponents_iff_sum_sq_dvd] at hcr
  obtain ⟨hodd, ha1, hb1, rfl, hdvd⟩ := hcr
  have ha_odd : Odd a := Nat.Odd.of_mul_left hodd
  have hb_odd : Odd b := Nat.Odd.of_mul_right hodd
  obtain ⟨u', rfl⟩ := ha_odd
  obtain ⟨v', rfl⟩ := hb_odd
  let u := u' + 1
  let v := v' + 1
  have hu2 : 2 ≤ u := by omega
  have huv : u ≤ v := by omega
  obtain ⟨q, hqeq⟩ := hdvd
  have hmain : (u + v - 1) ^ 2 = q * u * v := by
    have h1 : (2 * u' + 1 + (2 * v' + 1)) = 2 * (u + v - 1) := by omega
    have h2 : (2 * u' + 1 + 1) * (2 * v' + 1 + 1) = 4 * (u * v) := by
      dsimp [u, v]; ring
    rw [h1, h2] at hqeq
    nlinarith only [hqeq]
  have hZ : ((u : ℤ) + (v : ℤ) - 1) ^ 2 = (q : ℤ) * (u : ℤ) * (v : ℤ) := by
    zify [show 1 ≤ u + v by omega] at hmain
    exact hmain
  have hq0 : q ≠ 0 := by rintro rfl; push_cast at hZ; nlinarith only [hZ, hu2, huv]
  have hq1 : q ≠ 1 := by rintro rfl; push_cast at hZ; nlinarith only [hZ, hu2, huv]
  have hq2 : q ≠ 2 := by rintro rfl; push_cast at hZ; nlinarith only [hZ, hu2, huv]
  by_cases hq3 : q = 3
  · left
    subst hq3
    push_cast at hZ
    have hdisc : (2 * (v : ℤ) - (u : ℤ) - 2) ^ 2 = 3 * (u : ℤ) * (4 - (u : ℤ)) := by
      nlinarith only [hZ]
    have hu4 : u ≤ 4 := by
      by_contra hgt
      have : 3 * (u : ℤ) * (4 - (u : ℤ)) < 0 := by nlinarith
      nlinarith only [hdisc, this, sq_nonneg (2 * (v : ℤ) - (u : ℤ) - 2)]
    have hucase : u = 2 ∨ u = 3 ∨ u = 4 := by omega
    rcases hucase with hu | hu | hu
    · rw [hu] at hdisc
      norm_num at hdisc
      have hv_le : v ≤ 4 := by nlinarith only [hdisc]
      have hv_case : v = 2 ∨ v = 3 ∨ v = 4 := by omega
      rcases hv_case with hv | hv | hv <;> rw [hv] at hdisc <;> norm_num at hdisc
    · rw [hu] at hZ
      norm_num at hZ
      have hv_fac : ((v : ℤ) - 1) * ((v : ℤ) - 4) = 0 := by nlinarith only [hZ]
      rcases mul_eq_zero.mp hv_fac with h1 | h4
      · omega
      · have hv4 : v = 4 := by omega
        omega
    · rw [hu] at hdisc
      norm_num at hdisc
      have : (v : ℤ) = 3 := by nlinarith only [hdisc]
      omega
  by_cases hq4 : q = 4
  · right; right; left
    subst hq4
    push_cast at hZ
    have hodd_diff : Odd (v - u) := by
      have hsq : ((v - u : ℕ) : ℤ) ^ 2 = 2 * ((u : ℤ) + (v : ℤ)) - 1 := by
        zify [huv]; nlinarith only [hZ]
      rcases Nat.even_or_odd (v - u) with ⟨m, hm⟩ | hodd_vu
      · exfalso
        have h2m : ((v - u : ℕ) : ℤ) = 2 * (m : ℤ) := by omega
        rw [h2m] at hsq
        have hsq2 : 2 * (2 * (m : ℤ) ^ 2) = 2 * ((u : ℤ) + (v : ℤ)) - 1 := by
          nlinarith only [hsq]
        omega
      · exact hodd_vu
    obtain ⟨m, hm⟩ := hodd_diff
    have hum : u = m ^ 2 := by
      have hv_eq : (v : ℤ) = (u : ℤ) + 2 * (m : ℤ) + 1 := by omega
      rw [hv_eq] at hZ
      have : (u : ℤ) = (m : ℤ) ^ 2 := by nlinarith only [hZ]
      exact_mod_cast this
    have hm2 : 2 ≤ m := by
      by_contra hlt
      have : m = 0 ∨ m = 1 := by omega
      rcases this with rfl | rfl <;> norm_num at hum <;> omega
    let j := m - 1
    have hmeq : m = j + 1 := by omega
    refine ⟨j, ?_, ?_⟩
    · have hu_eq : u' + 1 = (j + 1) ^ 2 := by rw [← hmeq]; exact hum
      linarith only [hu_eq]
    · have hv_eq : v' + 1 = (j + 2) ^ 2 := by
        have hv1 : v' + 1 = u + 2 * m + 1 := by omega
        rw [hv1, hum, hmeq]; ring
      linarith only [hv_eq]
  -- Now q ≥ 5
  have hq5 : 5 ≤ q := by omega
  have hqu : q ≤ u := vieta_ge q u v hu2 huv hmain
  by_cases heq_qu : u = q
  · right; left
    rw [heq_qu] at hZ
    have hfac : ((v : ℤ) - 1) * ((v : ℤ) - ((q : ℤ) - 1) ^ 2) = 0 := by nlinarith only [hZ]
    rcases mul_eq_zero.mp hfac with hv1 | hvq
    · omega
    · let d := q - 4
      refine ⟨d, ?_, ?_⟩
      · omega
      · have hv_nat : v = (q - 1) ^ 2 := by
          zify [show 1 ≤ q by omega]; linarith only [hvq]
        have hv_d : v' + 1 = (d + 3) ^ 2 := by
          have : q - 1 = d + 3 := by omega
          rw [← this]; exact hv_nat
        linarith only [hv_d]
  · right; right; right
    refine ⟨q, hq5, by omega, ?_⟩
    rw [hqeq]
    ring
