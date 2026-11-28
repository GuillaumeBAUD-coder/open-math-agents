import OMAReductions.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1

/-!
# Proof of `Erdos103.erdos_103.variants.two_le.R1.H2.R1.H1`

For all `n ≥ 1200`, the first `n` points of a `(⌊√n⌋ + 1) × (⌊√n⌋ + 1)` integer grid form a
1-separated set `C` of diameter at most `2(⌊√n⌋ + 1)`, whereas any 1-separated `n`-point set `B`
lying on a circle of radius `R` centered at its centroid satisfies `(n - 4) / 16 ≤ R ≤ diam(B)`.
-/

-- Step Erdos103.erdos_103.variants.two_le.R1.H2.R1.H1: hypothesis H1 of reduction Erdos103.erdos_103.variants.two_le.R1.H2.R1
-- Credit: @LiJiaHua1024

namespace OMA.Erdos103H1

open EuclideanGeometry Filter Finset
open Erdos103 OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1

private noncomputable def mkPt (x y : ℝ) : ℝ² := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x, y]

private lemma mkPt_zero (x y : ℝ) : mkPt x y 0 = x := rfl
private lemma mkPt_one (x y : ℝ) : mkPt x y 1 = y := rfl

private lemma dist_sq_eq (p q : ℝ²) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

/-- If a finite set `S : Finset ℝ` is `δ`-separated (`δ > 0`) and lies in `[a, b]`,
then `(S.card - 1) * δ ≤ b - a`. -/
private lemma card_separated_interval {S : Finset ℝ} {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b)
    (hin : ∀ x ∈ S, a ≤ x ∧ x ≤ b)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    ((S.card : ℝ) - 1) * δ ≤ b - a := by
  by_cases h0 : S.card = 0
  · rw [h0]; simp; linarith
  · let L := S.sort (· ≤ ·)
    have hLlen : L.length = S.card := Finset.length_sort (· ≤ ·)
    have hLnd : L.Nodup := S.sort_nodup (· ≤ ·)
    have hLpw : L.Pairwise (· ≤ ·) := S.pairwise_sort (· ≤ ·)
    have hLmem : ∀ x, x ∈ L ↔ x ∈ S := fun _ => Finset.mem_sort (· ≤ ·)
    have hstep : ∀ (i : ℕ) (hi : i + 1 < L.length), L[i] + δ ≤ L[i + 1] := by
      intro i hi
      have hle : L[i] ≤ L[i + 1] :=
        List.pairwise_iff_getElem.mp hLpw i (i + 1) (by omega) hi (Nat.lt_succ_self i)
      have hne : L[i] ≠ L[i + 1] := fun h => by
        have := (List.Nodup.getElem_inj_iff hLnd).mp h; omega
      have hs := hsep _ ((hLmem _).mp (List.getElem_mem (by omega)))
        _ ((hLmem _).mp (List.getElem_mem hi)) hne
      rw [abs_of_nonpos (by linarith)] at hs
      linarith
    have htele : ∀ (k : ℕ) (hk : k < L.length), L[0]'(by omega) + (k : ℝ) * δ ≤ L[k]'hk := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have h1 := ih (by omega)
        have h2 := hstep k hk
        push_cast
        linarith
    have hlast_lt : L.length - 1 < L.length := by omega
    have hlast := htele (L.length - 1) hlast_lt
    have ha : a ≤ L[0]'(by omega) := (hin _ ((hLmem _).mp (List.getElem_mem (by omega)))).1
    have hb : L[L.length - 1]'hlast_lt ≤ b := (hin _ ((hLmem _).mp (List.getElem_mem hlast_lt))).2
    have hsub : ((L.length - 1 : ℕ) : ℝ) = (S.card : ℝ) - 1 := by
      rw [hLlen, Nat.cast_sub (by omega : 1 ≤ S.card), Nat.cast_one]
    rw [hsub] at hlast
    linarith

/-- Any 1-separated subset `U` of a circle `dist x c = R` lying in one of the four 90-degree
sectors (`|x 0 - c 0| ≤ x 1 - c 1`) satisfies `(U.card - 1) / 2 ≤ 2 * R`. -/
private lemma sector_card_bound {U : Finset ℝ²} {c : ℝ²} {R : ℝ} (hR : 0 ≤ R)
    (hon : ∀ x ∈ U, dist x c = R)
    (hsep : ∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ dist x y)
    (hsec : ∀ x ∈ U, |x 0 - c 0| ≤ x 1 - c 1) :
    ((U.card : ℝ) - 1) * (1 / 2) ≤ 2 * R := by
  by_cases hU0 : U.card = 0
  · rw [hU0]; linarith
  have hinj : Set.InjOn (fun x : ℝ² => x 0) (U : Set ℝ²) := by
    intro x hx y hy hxeq
    dsimp only at hxeq
    by_contra hne
    have h1 : 1 ≤ dist x y ^ 2 := by
      have := hsep x hx y hy hne; nlinarith [dist_nonneg (x := x) (y := y)]
    rw [dist_sq_eq, hxeq, sub_self, zero_pow two_ne_zero, zero_add] at h1
    have hxsq : (x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2 = R ^ 2 := by
      rw [← dist_sq_eq, hon x hx]
    have hysq : (y 0 - c 0) ^ 2 + (y 1 - c 1) ^ 2 = R ^ 2 := by
      rw [← dist_sq_eq, hon y hy]
    rw [hxeq] at hxsq
    have h1pos : 0 ≤ x 1 - c 1 := (abs_nonneg _).trans (hsec x hx)
    have h2pos : 0 ≤ y 1 - c 1 := (abs_nonneg _).trans (hsec y hy)
    have heq1 : x 1 - c 1 = y 1 - c 1 := by nlinarith
    nlinarith
  have hcard : (U.image (fun x : ℝ² => x 0)).card = U.card := Finset.card_image_of_injOn hinj
  rw [← hcard]
  have hgoal := card_separated_interval (S := U.image (fun x : ℝ² => x 0)) (a := c 0 - R) (b := c 0 + R)
    (δ := 1 / 2) (by norm_num) (by linarith) ?_ ?_
  · linarith
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    have hxsq : (x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2 = R ^ 2 := by rw [← dist_sq_eq, hon x hx]
    have hle : (x 0 - c 0) ^ 2 ≤ R ^ 2 := by nlinarith [sq_nonneg (x 1 - c 1)]
    have habs : |x 0 - c 0| ≤ R := by nlinarith [abs_nonneg (x 0 - c 0), sq_abs (x 0 - c 0)]
    rw [abs_le] at habs
    constructor <;> linarith
  · intro t₁ ht₁ t₂ ht₂ hne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht₁
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht₂
    have hxy : x ≠ y := fun h => hne (congrArg (fun p : ℝ² => p 0) h)
    have h1 : 1 ≤ (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
      rw [← dist_sq_eq]; have := hsep x hx y hy hxy; nlinarith [dist_nonneg (x := x) (y := y)]
    have hxsq : (x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2 = R ^ 2 := by rw [← dist_sq_eq, hon x hx]
    have hysq : (y 0 - c 0) ^ 2 + (y 1 - c 1) ^ 2 = R ^ 2 := by rw [← dist_sq_eq, hon y hy]
    have hdiff : (x 1 - y 1) * ((x 1 - c 1) + (y 1 - c 1)) =
        -(x 0 - y 0) * ((x 0 - c 0) + (y 0 - c 0)) := by linarith
    have hsum_y : 0 ≤ (x 1 - c 1) + (y 1 - c 1) := by
      linarith [abs_nonneg (x 0 - c 0), hsec x hx, abs_nonneg (y 0 - c 0), hsec y hy]
    have hsum_x_le : |(x 0 - c 0) + (y 0 - c 0)| ≤ (x 1 - c 1) + (y 1 - c 1) :=
      (abs_add_le _ _).trans (add_le_add (hsec x hx) (hsec y hy))
    have hy_le_x : |x 1 - y 1| ≤ |x 0 - y 0| := by
      by_cases h0 : (x 1 - c 1) + (y 1 - c 1) = 0
      · have h0x : |(x 0 - c 0) + (y 0 - c 0)| ≤ 0 := h0 ▸ hsum_x_le
        have hx0 : x 0 = c 0 := by linarith [abs_nonneg (x 0 - c 0), hsec x hx, abs_nonneg (y 0 - c 0), hsec y hy, abs_nonpos_iff.mp (show |x 0 - c 0| ≤ 0 by linarith [hsec x hx, hsec y hy, abs_nonneg (y 0 - c 0)])]
        have hy0 : y 0 = c 0 := by linarith [abs_nonpos_iff.mp (show |y 0 - c 0| ≤ 0 by linarith [hsec x hx, hsec y hy, abs_nonneg (x 0 - c 0)])]
        exact absurd (hx0.trans hy0.symm) hne
      · have hpos : 0 < (x 1 - c 1) + (y 1 - c 1) := lt_of_le_of_ne hsum_y (Ne.symm h0)
        have hmul : |x 1 - y 1| * ((x 1 - c 1) + (y 1 - c 1)) ≤ |x 0 - y 0| * ((x 1 - c 1) + (y 1 - c 1)) := by
          calc |x 1 - y 1| * ((x 1 - c 1) + (y 1 - c 1))
              = |(x 1 - y 1) * ((x 1 - c 1) + (y 1 - c 1))| := by rw [abs_mul, abs_of_pos hpos]
            _ = |-(x 0 - y 0) * ((x 0 - c 0) + (y 0 - c 0))| := by rw [hdiff]
            _ = |x 0 - y 0| * |(x 0 - c 0) + (y 0 - c 0)| := by rw [abs_mul, abs_neg]
            _ ≤ |x 0 - y 0| * ((x 1 - c 1) + (y 1 - c 1)) :=
                mul_le_mul_of_nonneg_left hsum_x_le (abs_nonneg _)
        exact le_of_mul_le_mul_right hmul hpos
    have hsq_le : (x 1 - y 1) ^ 2 ≤ (x 0 - y 0) ^ 2 := by
      rw [← sq_abs (x 1 - y 1), ← sq_abs (x 0 - y 0)]
      exact pow_le_pow_left₀ (abs_nonneg _) hy_le_x 2
    nlinarith [sq_abs (x 0 - y 0), abs_nonneg (x 0 - y 0)]

/-- Any 1-separated `n`-point set on a circle of radius `R` satisfies `(n : ℝ) ≤ 16 * R + 4`. -/
private lemma circle_radius_lower {n : ℕ} (hn : 1 ≤ n) {B : Finset ℝ²} (hB : B ∈ separatedSets n)
    {c : ℝ²} {R : ℝ} (hon : ∀ x ∈ B, dist x c = R) :
    (n : ℝ) ≤ 16 * R + 4 := by
  have hBne : B.Nonempty := Finset.card_pos.mp (by rw [hB.1]; omega)
  obtain ⟨x₀, hx₀⟩ := hBne
  have hR : 0 ≤ R := (hon x₀ hx₀) ▸ dist_nonneg
  let U1 := B.filter fun x => |x 0 - c 0| ≤ x 1 - c 1
  let U2 := B.filter fun x => |x 0 - c 0| ≤ -(x 1 - c 1)
  let U3 := B.filter fun x => |x 1 - c 1| ≤ x 0 - c 0
  let U4 := B.filter fun x => |x 1 - c 1| ≤ -(x 0 - c 0)
  have hcov : B ⊆ U1 ∪ U2 ∪ U3 ∪ U4 := by
    intro x hx
    simp only [U1, U2, U3, U4, Finset.mem_union, Finset.mem_filter]
    by_cases hle : |x 0 - c 0| ≤ |x 1 - c 1|
    · rcases le_total 0 (x 1 - c 1) with h | h
      · left; left; left; exact ⟨hx, by rwa [abs_of_nonneg h] at hle⟩
      · left; left; right; exact ⟨hx, by rwa [abs_of_nonpos h] at hle⟩
    · have hle' : |x 1 - c 1| ≤ |x 0 - c 0| := le_of_lt (not_le.mp hle)
      rcases le_total 0 (x 0 - c 0) with h | h
      · left; right; exact ⟨hx, by rwa [abs_of_nonneg h] at hle'⟩
      · right; exact ⟨hx, by rwa [abs_of_nonpos h] at hle'⟩
  have hsum : n ≤ U1.card + U2.card + U3.card + U4.card := by
    rw [← hB.1]
    calc B.card ≤ (U1 ∪ U2 ∪ U3 ∪ U4).card := Finset.card_le_card hcov
      _ ≤ (U1 ∪ U2 ∪ U3).card + U4.card := Finset.card_union_le _ _
      _ ≤ (U1 ∪ U2).card + U3.card + U4.card := by have := Finset.card_union_le (U1 ∪ U2) U3; omega
      _ ≤ U1.card + U2.card + U3.card + U4.card := by have := Finset.card_union_le U1 U2; omega
  have h1 : ((U1.card : ℝ) - 1) * (1 / 2) ≤ 2 * R :=
    sector_card_bound hR (fun x hx => hon x (Finset.mem_filter.mp hx).1)
      (fun x hx y hy hne => sep_dist hB (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hne)
      (fun x hx => (Finset.mem_filter.mp hx).2)
  -- Apply linear isometries (x ↦ (x 0, -x 1), x ↦ (x 1, x 0), x ↦ (x 1, -x 0)) for U2, U3, U4
  let flipY : ℝ² → ℝ² := fun x => mkPt (x 0) (-x 1)
  have hflipY_dist : ∀ p q, dist (flipY p) (flipY q) = dist p q := fun p q => by
    have hsq : dist (flipY p) (flipY q) ^ 2 = dist p q ^ 2 := by
      rw [dist_sq_eq, dist_sq_eq]; simp [flipY, mkPt_zero, mkPt_one]; ring
    nlinarith [dist_nonneg (x := flipY p) (y := flipY q), dist_nonneg (x := p) (y := q)]
  have hflipY_inj : Function.Injective flipY := fun p q h => by
    rw [← dist_eq_zero, ← hflipY_dist, h, dist_self]
  let swapXY : ℝ² → ℝ² := fun x => mkPt (x 1) (x 0)
  have hswap_dist : ∀ p q, dist (swapXY p) (swapXY q) = dist p q := fun p q => by
    have hsq : dist (swapXY p) (swapXY q) ^ 2 = dist p q ^ 2 := by
      rw [dist_sq_eq, dist_sq_eq]; simp [swapXY, mkPt_zero, mkPt_one]; ring
    nlinarith [dist_nonneg (x := swapXY p) (y := swapXY q), dist_nonneg (x := p) (y := q)]
  have hswap_inj : Function.Injective swapXY := fun p q h => by
    rw [← dist_eq_zero, ← hswap_dist, h, dist_self]
  let rot90 : ℝ² → ℝ² := fun x => mkPt (x 1) (-x 0)
  have hrot_dist : ∀ p q, dist (rot90 p) (rot90 q) = dist p q := fun p q => by
    have hsq : dist (rot90 p) (rot90 q) ^ 2 = dist p q ^ 2 := by
      rw [dist_sq_eq, dist_sq_eq]; simp [rot90, mkPt_zero, mkPt_one]; ring
    nlinarith [dist_nonneg (x := rot90 p) (y := rot90 q), dist_nonneg (x := p) (y := q)]
  have hrot_inj : Function.Injective rot90 := fun p q h => by
    rw [← dist_eq_zero, ← hrot_dist, h, dist_self]
  have h2 : ((U2.card : ℝ) - 1) * (1 / 2) ≤ 2 * R := by
    rw [← Finset.card_image_of_injective U2 hflipY_inj]
    refine sector_card_bound (c := flipY c) hR ?_ ?_ ?_
    · intro x hx; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      rw [hflipY_dist]; exact hon p (Finset.mem_filter.mp hp).1
    · intro x hx y hy hne; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      rw [hflipY_dist]
      exact sep_dist hB (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 (fun h => hne (congrArg flipY h))
    · intro x hx; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      have hp' := (Finset.mem_filter.mp hp).2
      simp only [flipY, mkPt_zero, mkPt_one]; linarith
  have h3 : ((U3.card : ℝ) - 1) * (1 / 2) ≤ 2 * R := by
    rw [← Finset.card_image_of_injective U3 hswap_inj]
    refine sector_card_bound (c := swapXY c) hR ?_ ?_ ?_
    · intro x hx; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      rw [hswap_dist]; exact hon p (Finset.mem_filter.mp hp).1
    · intro x hx y hy hne; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      rw [hswap_dist]
      exact sep_dist hB (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 (fun h => hne (congrArg swapXY h))
    · intro x hx; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      have hp' := (Finset.mem_filter.mp hp).2
      simp only [swapXY, mkPt_zero, mkPt_one]; exact hp'
  have h4 : ((U4.card : ℝ) - 1) * (1 / 2) ≤ 2 * R := by
    rw [← Finset.card_image_of_injective U4 hrot_inj]
    refine sector_card_bound (c := rot90 c) hR ?_ ?_ ?_
    · intro x hx; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      rw [hrot_dist]; exact hon p (Finset.mem_filter.mp hp).1
    · intro x hx y hy hne; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      rw [hrot_dist]
      exact sep_dist hB (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 (fun h => hne (congrArg rot90 h))
    · intro x hx; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      have hp' := (Finset.mem_filter.mp hp).2
      simp only [rot90, mkPt_zero, mkPt_one]; linarith
  have hsumr : (n : ℝ) ≤ (U1.card : ℝ) + (U2.card : ℝ) + (U3.card : ℝ) + (U4.card : ℝ) := by
    exact_mod_cast hsum
  linarith

/-- Variance identity gives `R ≤ Metric.diam B` when `B` lies on a circle of radius `R` around its centroid. -/
private lemma radius_le_diam {n : ℕ} (hn : 1 ≤ n) {B : Finset ℝ²} (hB : B ∈ separatedSets n)
    {c : ℝ²} {R : ℝ} (hon : ∀ x ∈ B, dist x c = R) (hcent : ∑ x ∈ B, (x - c) = 0) :
    R ≤ Metric.diam (B : Set ℝ²) := by
  have hvar : ∑ x ∈ B, ∑ y ∈ B, dist x y ^ 2 = 2 * (B.card : ℝ) ^ 2 * R ^ 2 := by
    have hinner : ∀ x ∈ B, ∑ y ∈ B, dist x y ^ 2 = 2 * (B.card : ℝ) * R ^ 2 := by
      intro x hx
      have h1 : ∀ y ∈ B, dist x y ^ 2 = R ^ 2 - 2 * inner ℝ (x - c) (y - c) + R ^ 2 := by
        intro y hy
        rw [dist_eq_norm, show x - y = (x - c) - (y - c) by abel, norm_sub_sq_real,
          ← dist_eq_norm, ← dist_eq_norm, hon x hx, hon y hy]
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, ← Finset.mul_sum, ← inner_sum, hcent, inner_zero_right]
      simp; ring
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
    ring
  have hle : ∑ x ∈ B, ∑ y ∈ B, dist x y ^ 2 ≤ (B.card : ℝ) ^ 2 * Metric.diam (B : Set ℝ²) ^ 2 := by
    calc ∑ x ∈ B, ∑ y ∈ B, dist x y ^ 2
        ≤ ∑ _x ∈ B, ∑ _y ∈ B, Metric.diam (B : Set ℝ²) ^ 2 := by
          refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_
          exact pow_le_pow_left₀ dist_nonneg
            (Metric.dist_le_diam_of_mem B.finite_toSet.isBounded hx hy) 2
      _ = (B.card : ℝ) ^ 2 * Metric.diam (B : Set ℝ²) ^ 2 := by
          simp [Finset.sum_const, nsmul_eq_mul]; ring
  have hBpos : (0 : ℝ) < (B.card : ℝ) ^ 2 := by
    rw [hB.1]; positivity
  have hR2 : R ^ 2 ≤ Metric.diam (B : Set ℝ²) ^ 2 := by nlinarith
  exact le_of_sq_le Metric.diam_nonneg hR2

/-- The first `n` integer lattice points in `[0, k) × [0, k)` (`k = ⌊√n⌋ + 1`) form a 1-separated
set of diameter at most `2 * k`. -/
private lemma grid_competitor (n : ℕ) :
    ∃ C ∈ separatedSets n, Metric.diam (C : Set ℝ²) ≤ 2 * ((Nat.sqrt n + 1 : ℕ) : ℝ) := by
  let k := Nat.sqrt n + 1
  have hkpos : 0 < k := Nat.succ_pos _
  let f : ℕ → ℝ² := fun t => mkPt ((t / k : ℕ) : ℝ) ((t % k : ℕ) : ℝ)
  have hfinj : Function.Injective f := by
    intro a b hab
    have h0 : ((a / k : ℕ) : ℝ) = ((b / k : ℕ) : ℝ) := by
      have := congrArg (fun p : ℝ² => p 0) hab; simpa [f, mkPt_zero] using this
    have h1 : ((a % k : ℕ) : ℝ) = ((b % k : ℕ) : ℝ) := by
      have := congrArg (fun p : ℝ² => p 1) hab; simpa [f, mkPt_one] using this
    have hd : a / k = b / k := Nat.cast_injective h0
    have hm : a % k = b % k := Nat.cast_injective h1
    have ha := Nat.div_add_mod a k
    have hb := Nat.div_add_mod b k
    rw [hd, hm] at ha; omega
  let C : Finset ℝ² := (Finset.range n).image f
  have hCcard : C.card = n := by rw [Finset.card_image_of_injective _ hfinj, Finset.card_range]
  have hnat_sq : ∀ u v : ℕ, u ≠ v → (1 : ℝ) ≤ ((u : ℝ) - (v : ℝ)) ^ 2 := by
    intro u v huv
    rcases lt_or_gt_of_ne huv with h | h
    · have h1 : (u : ℝ) + 1 ≤ (v : ℝ) := by exact_mod_cast (show u + 1 ≤ v by omega)
      nlinarith
    · have h1 : (v : ℝ) + 1 ≤ (u : ℝ) := by exact_mod_cast (show v + 1 ≤ u by omega)
      nlinarith
  have hCsep : C ∈ separatedSets n := by
    refine mk_sep hCcard ?_
    intro x hx y hy hne
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hy
    have hab : a ≠ b := fun h => hne (congrArg f h)
    have hsq : 1 ≤ dist (f a) (f b) ^ 2 := by
      rw [dist_sq_eq]; simp only [f, mkPt_zero, mkPt_one]
      by_cases hd : a / k = b / k
      · have hm : a % k ≠ b % k := fun h => hab (by
          have ha := Nat.div_add_mod a k; have hb := Nat.div_add_mod b k; rw [hd, h] at ha; omega)
        linarith [hnat_sq (a % k) (b % k) hm, sq_nonneg (((a / k : ℕ) : ℝ) - ((b / k : ℕ) : ℝ))]
      · linarith [hnat_sq (a / k) (b / k) hd, sq_nonneg (((a % k : ℕ) : ℝ) - ((b % k : ℕ) : ℝ))]
    exact le_of_sq_le dist_nonneg (by simpa using hsq)
  refine ⟨C, hCsep, ?_⟩
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
  have hlt_k2 : n < k * k := by dsimp [k]; exact Nat.lt_succ_sqrt n
  have ha_lt : a < k * k := (Finset.mem_range.mp ha).trans hlt_k2
  have hb_lt : b < k * k := (Finset.mem_range.mp hb).trans hlt_k2
  have had : a / k < k := Nat.div_lt_of_lt_mul ha_lt
  have hbd : b / k < k := Nat.div_lt_of_lt_mul hb_lt
  have ham : a % k < k := Nat.mod_lt a hkpos
  have hbm : b % k < k := Nat.mod_lt b hkpos
  have hsq : dist (f a) (f b) ^ 2 ≤ (2 * (k : ℝ)) ^ 2 := by
    rw [dist_sq_eq]; simp only [f, mkPt_zero, mkPt_one]
    have h1 : ((a / k : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast had.le
    have h2 : ((b / k : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hbd.le
    have h3 : ((a % k : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast ham.le
    have h4 : ((b % k : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hbm.le
    have hnn1 : (0 : ℝ) ≤ ((a / k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hnn2 : (0 : ℝ) ≤ ((b / k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hnn3 : (0 : ℝ) ≤ ((a % k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hnn4 : (0 : ℝ) ≤ ((b % k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hd1 : (((a / k : ℕ) : ℝ) - ((b / k : ℕ) : ℝ)) ^ 2 ≤ (k : ℝ) ^ 2 := by nlinarith
    have hd2 : (((a % k : ℕ) : ℝ) - ((b % k : ℕ) : ℝ)) ^ 2 ≤ (k : ℝ) ^ 2 := by nlinarith
    nlinarith
  exact le_of_sq_le (by positivity) hsq

end OMA.Erdos103H1

theorem OMA.solution : OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1.H1 := by
  filter_upwards [Filter.eventually_ge_atTop 2000] with n hn
  obtain ⟨C, hCsep, hCdiam⟩ := OMA.Erdos103H1.grid_competitor n
  refine ⟨C, hCsep, fun B hB ⟨c, R, hon, hcent⟩ => ?_⟩
  have hR_lo := OMA.Erdos103H1.circle_radius_lower (by omega) hB hon
  have hR_diam := OMA.Erdos103H1.radius_le_diam (by omega) hB hon hcent
  have hs_le : (Nat.sqrt n : ℝ) ^ 2 ≤ (n : ℝ) := by
    exact_mod_cast (by simpa [sq] using Nat.sqrt_le n)
  have hnr : (2000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs_lt : 2 * ((Nat.sqrt n + 1 : ℕ) : ℝ) < ((n : ℝ) - 4) / 16 := by
    push_cast
    have hsnn : (0 : ℝ) ≤ (Nat.sqrt n : ℝ) := Nat.cast_nonneg _
    have h40 : 40 * (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by
      have hsq : (40 * (Nat.sqrt n : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
      nlinarith
    linarith
  linarith
