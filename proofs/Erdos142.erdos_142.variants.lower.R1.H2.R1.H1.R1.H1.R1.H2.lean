import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R1
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1.R1.H2
-- Credit: @mijuny

open scoped BigOperators

namespace Pre36740

lemma abs_mul_le_one {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |x * y| ≤ 1 := by
  rw [abs_mul]
  exact mul_le_one₀ hx (abs_nonneg y) hy

lemma cs_bounded {ι : Type*} [Fintype ι] (u v : ι → ℝ) (hu : ∀ i, |u i| ≤ 1) :
    (∑ i : ι, u i * v i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i : ι, (v i) ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) u v
  have hsq : ∑ i : ι, (u i) ^ 2 ≤ (Fintype.card ι : ℝ) := by
    calc ∑ i : ι, (u i) ^ 2
        ≤ ∑ _i : ι, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          rw [← sq_abs]
          nlinarith [hu i, abs_nonneg (u i)]
      _ = (Fintype.card ι : ℝ) := by simp
  have hv0 : 0 ≤ ∑ i : ι, (v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  exact hcs.trans (mul_le_mul_of_nonneg_right hsq hv0)

lemma sq_sum_shift {G : Type*} [AddCommGroup G] [Fintype G] (F : G → ℝ) :
    (∑ d : G, F d) ^ 2 = ∑ d : G, ∑ t : G, F d * F (d + t) := by
  rw [sq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  exact (Fintype.sum_equiv (Equiv.addLeft d) (fun t => F d * F (d + t))
    (fun d' => F d * F d') (fun _ => rfl)).symm

theorem prove_H2 :
    OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R1.H2 := by
  intro p hp c₀ c₁ c₂ c₃ _hc01 _hc02 hc03 _hc12 hc13 hc23 f₀ f₁ f₂ f₃ hf₀ hf₁ hf₂
  let a₁ : ZMod p := c₁ - c₀
  let a₂ : ZMod p := c₂ - c₀
  let a₃ : ZMod p := c₃ - c₀
  let b₂ : ZMod p := c₂ - c₁
  let b₃ : ZMod p := c₃ - c₁
  let e₃ : ZMod p := c₃ - c₂
  have ha₃ : a₃ ≠ 0 := sub_ne_zero.mpr hc03.symm
  have hb₃ : b₃ ≠ 0 := sub_ne_zero.mpr hc13.symm
  have he₃ : e₃ ≠ 0 := sub_ne_zero.mpr hc23.symm
  let V₁ (y : ZMod p) : ℝ := ∑ d : ZMod p, f₁ (y + a₁ * d) * f₂ (y + a₂ * d) * f₃ (y + a₃ * d)
  let S₀ : ℝ := ∑ x : ZMod p, ∑ d : ZMod p,
    f₀ (x + c₀ * d) * f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d)
  have hS₀_eq : S₀ = ∑ y : ZMod p, f₀ y * V₁ y := by
    dsimp [S₀, V₁]
    rw [Finset.sum_comm]
    have hshift : ∀ d : ZMod p,
        (∑ x : ZMod p, f₀ (x + c₀ * d) * f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d)) =
        ∑ y : ZMod p, f₀ y * (f₁ (y + a₁ * d) * f₂ (y + a₂ * d) * f₃ (y + a₃ * d)) := by
      intro d
      refine (Fintype.sum_equiv (Equiv.subRight (c₀ * d)) _ _ ?_).symm
      intro y
      have h0 : y - c₀ * d + c₀ * d = y := by ring
      have h1 : y - c₀ * d + c₁ * d = y + a₁ * d := by dsimp [a₁]; ring
      have h2 : y - c₀ * d + c₂ * d = y + a₂ * d := by dsimp [a₂]; ring
      have h3 : y - c₀ * d + c₃ * d = y + a₃ * d := by dsimp [a₃]; ring
      simp only [Equiv.subRight_apply, h0, h1, h2, h3]
      ring
    simp_rw [hshift]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm
  let S₁_sq : ℝ := ∑ y : ZMod p, (V₁ y) ^ 2
  have hcs1 : S₀ ^ 2 ≤ (p : ℝ) * S₁_sq := by
    rw [hS₀_eq]
    simpa [ZMod.card, S₁_sq] using cs_bounded f₀ V₁ hf₀
  let g₁ (t z : ZMod p) : ℝ := f₁ z * f₁ (z + a₁ * t)
  let g₂ (t z : ZMod p) : ℝ := f₂ z * f₂ (z + a₂ * t)
  let g₃ (t z : ZMod p) : ℝ := f₃ z * f₃ (z + a₃ * t)
  have hg₁ : ∀ q : ZMod p × ZMod p, |g₁ q.2 q.1| ≤ 1 := fun _ => abs_mul_le_one (hf₁ _) (hf₁ _)
  have hg₂ : ∀ t z : ZMod p, |g₂ t z| ≤ 1 := fun _ _ => abs_mul_le_one (hf₂ _) (hf₂ _)
  let V₂ (q : ZMod p × ZMod p) : ℝ :=
    ∑ d : ZMod p, g₂ q.2 (q.1 + b₂ * d) * g₃ q.2 (q.1 + b₃ * d)
  have hS₁_eq : S₁_sq = ∑ q : ZMod p × ZMod p, g₁ q.2 q.1 * V₂ q := by
    dsimp [S₁_sq, V₁]
    simp_rw [sq_sum_shift]
    rw [Finset.sum_comm]
    have hshift2 : ∀ d : ZMod p,
        (∑ y : ZMod p, ∑ t : ZMod p,
          (f₁ (y + a₁ * d) * f₂ (y + a₂ * d) * f₃ (y + a₃ * d)) *
          (f₁ (y + a₁ * (d + t)) * f₂ (y + a₂ * (d + t)) * f₃ (y + a₃ * (d + t)))) =
        ∑ z : ZMod p, ∑ t : ZMod p,
          g₁ t z * (g₂ t (z + b₂ * d) * g₃ t (z + b₃ * d)) := by
      intro d
      refine (Fintype.sum_equiv (Equiv.subRight (a₁ * d)) _ _ ?_).symm
      intro z
      refine Finset.sum_congr rfl fun t _ => ?_
      have h1a : z - a₁ * d + a₁ * d = z := by ring
      have h1b : z - a₁ * d + a₁ * (d + t) = z + a₁ * t := by ring
      have h2a : z - a₁ * d + a₂ * d = z + b₂ * d := by dsimp [a₁, a₂, b₂]; ring
      have h2b : z - a₁ * d + a₂ * (d + t) = z + b₂ * d + a₂ * t := by dsimp [a₁, a₂, b₂]; ring
      have h3a : z - a₁ * d + a₃ * d = z + b₃ * d := by dsimp [a₁, a₃, b₃]; ring
      have h3b : z - a₁ * d + a₃ * (d + t) = z + b₃ * d + a₃ * t := by dsimp [a₁, a₃, b₃]; ring
      simp only [Equiv.subRight_apply, h1a, h1b, h2a, h2b, h3a, h3b, g₁, g₂, g₃]
      ring
    simp_rw [hshift2]
    rw [Finset.sum_comm]
    trans ∑ z : ZMod p, ∑ t : ZMod p, g₁ t z * V₂ (z, t)
    · refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => (Finset.mul_sum _ _ _).symm
    · exact (Fintype.sum_prod_type' _).symm
  let S₂_sq : ℝ := ∑ q : ZMod p × ZMod p, (V₂ q) ^ 2
  have hcs2 : S₁_sq ^ 2 ≤ (p : ℝ) ^ 2 * S₂_sq := by
    rw [hS₁_eq]
    have h := cs_bounded (fun q : ZMod p × ZMod p => g₁ q.2 q.1) V₂ hg₁
    have hcard : (Fintype.card (ZMod p × ZMod p) : ℝ) = (p : ℝ) ^ 2 := by
      simp [Fintype.card_prod, ZMod.card, sq]
    rwa [hcard] at h
  let k₂ (t s w : ZMod p) : ℝ := g₂ t w * g₂ t (w + b₂ * s)
  let k₃ (t s w : ZMod p) : ℝ := g₃ t w * g₃ t (w + b₃ * s)
  have hk₂ : ∀ r : ZMod p × ZMod p × ZMod p, |k₂ r.2.1 r.2.2 r.1| ≤ 1 :=
    fun _ => abs_mul_le_one (hg₂ _ _) (hg₂ _ _)
  let V₃ (r : ZMod p × ZMod p × ZMod p) : ℝ :=
    ∑ d : ZMod p, k₃ r.2.1 r.2.2 (r.1 + e₃ * d)
  have hS₂_eq : S₂_sq = ∑ r : ZMod p × ZMod p × ZMod p, k₂ r.2.1 r.2.2 r.1 * V₃ r := by
    dsimp [S₂_sq, V₂]
    rw [Fintype.sum_prod_type]
    simp_rw [sq_sum_shift]
    trans ∑ d : ZMod p, ∑ z : ZMod p, ∑ t : ZMod p, ∑ s : ZMod p,
        (g₂ t (z + b₂ * d) * g₃ t (z + b₃ * d)) *
        (g₂ t (z + b₂ * (d + s)) * g₃ t (z + b₃ * (d + s)))
    · trans ∑ z : ZMod p, ∑ d : ZMod p, ∑ t : ZMod p, ∑ s : ZMod p,
          (g₂ t (z + b₂ * d) * g₃ t (z + b₃ * d)) *
          (g₂ t (z + b₂ * (d + s)) * g₃ t (z + b₃ * (d + s)))
      · refine Finset.sum_congr rfl fun z _ => Finset.sum_comm
      · exact Finset.sum_comm
    have hshift3 : ∀ d : ZMod p,
        (∑ z : ZMod p, ∑ t : ZMod p, ∑ s : ZMod p,
          (g₂ t (z + b₂ * d) * g₃ t (z + b₃ * d)) *
          (g₂ t (z + b₂ * (d + s)) * g₃ t (z + b₃ * (d + s)))) =
        ∑ w : ZMod p, ∑ t : ZMod p, ∑ s : ZMod p,
          k₂ t s w * k₃ t s (w + e₃ * d) := by
      intro d
      refine (Fintype.sum_equiv (Equiv.subRight (b₂ * d)) _ _ ?_).symm
      intro w
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
      have h2a : w - b₂ * d + b₂ * d = w := by ring
      have h2b : w - b₂ * d + b₂ * (d + s) = w + b₂ * s := by ring
      have h3a : w - b₂ * d + b₃ * d = w + e₃ * d := by dsimp [b₂, b₃, e₃]; ring
      have h3b : w - b₂ * d + b₃ * (d + s) = w + e₃ * d + b₃ * s := by dsimp [b₂, b₃, e₃]; ring
      simp only [Equiv.subRight_apply, h2a, h2b, h3a, h3b, k₂, k₃]
      ring
    simp_rw [hshift3]
    rw [Finset.sum_comm]
    trans ∑ w : ZMod p, ∑ t : ZMod p, ∑ s : ZMod p, k₂ t s w * V₃ (w, t, s)
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => (Finset.mul_sum _ _ _).symm
    · symm
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun w _ => Fintype.sum_prod_type _
  let S₃_sq : ℝ := ∑ r : ZMod p × ZMod p × ZMod p, (V₃ r) ^ 2
  have hcs3 : S₂_sq ^ 2 ≤ (p : ℝ) ^ 3 * S₃_sq := by
    rw [hS₂_eq]
    have h := cs_bounded (fun r : ZMod p × ZMod p × ZMod p => k₂ r.2.1 r.2.2 r.1) V₃ hk₂
    have hcard : (Fintype.card (ZMod p × ZMod p × ZMod p) : ℝ) = (p : ℝ) ^ 3 := by
      simp [Fintype.card_prod, ZMod.card]
      ring
    rwa [hcard] at h
  let U₃ : ℝ := ∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
    f₃ x * f₃ (x + h₁) * f₃ (x + h₂) * f₃ (x + h₁ + h₂) *
    f₃ (x + h₃) * f₃ (x + h₁ + h₃) * f₃ (x + h₂ + h₃) * f₃ (x + h₁ + h₂ + h₃)
  have hS₃_eq : S₃_sq = (p : ℝ) * U₃ := by
    dsimp [S₃_sq, V₃]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type, sq_sum_shift]
    trans ∑ d : ZMod p, ∑ w : ZMod p, ∑ t : ZMod p, ∑ s : ZMod p, ∑ u : ZMod p,
        k₃ t s (w + e₃ * d) * k₃ t s (w + e₃ * (d + u))
    · trans ∑ w : ZMod p, ∑ d : ZMod p, ∑ t : ZMod p, ∑ s : ZMod p, ∑ u : ZMod p,
          k₃ t s (w + e₃ * d) * k₃ t s (w + e₃ * (d + u))
      · trans ∑ w : ZMod p, ∑ t : ZMod p, ∑ d : ZMod p, ∑ s : ZMod p, ∑ u : ZMod p,
            k₃ t s (w + e₃ * d) * k₃ t s (w + e₃ * (d + u))
        · refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun t _ => Finset.sum_comm
        · refine Finset.sum_congr rfl fun w _ => Finset.sum_comm
      · exact Finset.sum_comm
    have hshift4 : ∀ d : ZMod p,
        (∑ w : ZMod p, ∑ t : ZMod p, ∑ s : ZMod p, ∑ u : ZMod p,
          k₃ t s (w + e₃ * d) * k₃ t s (w + e₃ * (d + u))) = U₃ := by
      intro d
      trans ∑ x : ZMod p, ∑ t : ZMod p, ∑ s : ZMod p, ∑ u : ZMod p,
          k₃ t s x * k₃ t s (x + e₃ * u)
      · refine (Fintype.sum_equiv (Equiv.subRight (e₃ * d)) _ _ ?_).symm
        intro x
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ =>
          Finset.sum_congr rfl fun u _ => ?_
        have hxa : x - e₃ * d + e₃ * d = x := by ring
        have hxb : x - e₃ * d + e₃ * (d + u) = x + e₃ * u := by ring
        simp only [Equiv.subRight_apply, hxa, hxb]
      · dsimp [U₃]
        refine Finset.sum_congr rfl fun x _ => ?_
        refine Fintype.sum_equiv (Equiv.mulLeft₀ a₃ ha₃) _ _ fun t => ?_
        refine Fintype.sum_equiv (Equiv.mulLeft₀ b₃ hb₃) _ _ fun s => ?_
        refine Fintype.sum_equiv (Equiv.mulLeft₀ e₃ he₃) _ _ fun u => ?_
        simp only [Equiv.mulLeft₀_apply, k₃, g₃]
        have ha : x + b₃ * s + a₃ * t = x + a₃ * t + b₃ * s := by ring
        have hb : x + e₃ * u + a₃ * t = x + a₃ * t + e₃ * u := by ring
        have hc : x + e₃ * u + b₃ * s = x + b₃ * s + e₃ * u := by ring
        have hd : x + b₃ * s + e₃ * u + a₃ * t = x + a₃ * t + b₃ * s + e₃ * u := by ring
        rw [ha, hb, hc, hd]
        ring
    simp_rw [hshift4]
    simp [ZMod.card]
  have hS₀_4 : S₀ ^ 4 ≤ (p : ℝ) ^ 4 * S₂_sq := by
    have hsq1 : (S₀ ^ 2) ^ 2 ≤ ((p : ℝ) * S₁_sq) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg S₀) hcs1 2
    calc S₀ ^ 4 = (S₀ ^ 2) ^ 2 := by ring
      _ ≤ ((p : ℝ) * S₁_sq) ^ 2 := hsq1
      _ = (p : ℝ) ^ 2 * S₁_sq ^ 2 := by ring
      _ ≤ (p : ℝ) ^ 2 * ((p : ℝ) ^ 2 * S₂_sq) :=
            mul_le_mul_of_nonneg_left hcs2 (sq_nonneg (p : ℝ))
      _ = (p : ℝ) ^ 4 * S₂_sq := by ring
  have hsq2 : (S₀ ^ 4) ^ 2 ≤ ((p : ℝ) ^ 4 * S₂_sq) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hS₀_4 2
  calc S₀ ^ 8 = (S₀ ^ 4) ^ 2 := by ring
    _ ≤ ((p : ℝ) ^ 4 * S₂_sq) ^ 2 := hsq2
    _ = (p : ℝ) ^ 8 * S₂_sq ^ 2 := by ring
    _ ≤ (p : ℝ) ^ 8 * ((p : ℝ) ^ 3 * S₃_sq) :=
          mul_le_mul_of_nonneg_left hcs3 (by positivity)
    _ = (p : ℝ) ^ 12 * U₃ := by rw [hS₃_eq]; ring

end Pre36740

theorem OMA.solution :
    OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R1.H2 :=
  Pre36740.prove_H2
