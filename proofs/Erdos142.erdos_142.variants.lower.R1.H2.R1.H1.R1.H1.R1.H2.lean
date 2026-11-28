import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R1

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1.R1.H2:
-- Gowers U^3 generalized von Neumann inequality on ZMod p.
-- Credit: @jktcv2kz4f-cyber

open Finset

namespace OMA.Helpers

def diff {p : ℕ} (t : ZMod p) (f : ZMod p → ℝ) (y : ZMod p) : ℝ :=
  f y * f (y + t)

lemma abs_diff_le_one {p : ℕ} {f : ZMod p → ℝ} (hf : ∀ x, |f x| ≤ 1)
    (t y : ZMod p) : |diff t f y| ≤ 1 := by
  dsimp [diff]
  rw [abs_mul]
  have h1 := hf y
  have h2 := hf (y + t)
  nlinarith [abs_nonneg (f y), abs_nonneg (f (y + t))]

lemma cs_elim {p : ℕ} [NeZero p] (g : ZMod p → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (c : ZMod p) (K : ZMod p → ZMod p → ℝ) :
    (∑ x : ZMod p, ∑ d : ZMod p, g (x + c * d) * K x d) ^ 2 ≤
      (p : ℝ) * ∑ h : ZMod p, ∑ x : ZMod p, ∑ d : ZMod p,
        K x d * K (x - c * h) (d + h) := by
  have hshift :
      (∑ x : ZMod p, ∑ d : ZMod p, g (x + c * d) * K x d) =
        ∑ u : ZMod p, g u * ∑ d : ZMod p, K (u - c * d) d := by
    rw [Finset.sum_comm]
    have h1 : ∀ d : ZMod p,
        (∑ x : ZMod p, g (x + c * d) * K x d) =
          ∑ u : ZMod p, g u * K (u - c * d) d := by
      intro d
      refine Fintype.sum_equiv (Equiv.addRight (c * d)) _ _ fun x => ?_
      simp [add_sub_cancel_right]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => by rw [Finset.mul_sum]
  rw [hshift]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod p))
    g (fun u => ∑ d : ZMod p, K (u - c * d) d)
  have hg2 : (∑ u : ZMod p, g u ^ 2) ≤ (p : ℝ) := by
    calc (∑ u : ZMod p, g u ^ 2)
        ≤ ∑ _u : ZMod p, (1 : ℝ) := by
            refine Finset.sum_le_sum fun u _ => ?_
            have := hg u
            nlinarith [sq_abs (g u), abs_nonneg (g u)]
      _ = (p : ℝ) := by simp [ZMod.card]
  have hsq_nonneg : 0 ≤ ∑ u : ZMod p, (∑ d : ZMod p, K (u - c * d) d) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbound : (∑ u : ZMod p, g u * ∑ d : ZMod p, K (u - c * d) d) ^ 2 ≤
      (p : ℝ) * ∑ u : ZMod p, (∑ d : ZMod p, K (u - c * d) d) ^ 2 :=
    hcs.trans (mul_le_mul_of_nonneg_right hg2 hsq_nonneg)
  suffices hexp :
      (∑ u : ZMod p, (∑ d : ZMod p, K (u - c * d) d) ^ 2) =
        ∑ h : ZMod p, ∑ x : ZMod p, ∑ d : ZMod p, K x d * K (x - c * h) (d + h) by
    rwa [hexp] at hbound
  have hstep1 :
      (∑ u : ZMod p, (∑ d : ZMod p, K (u - c * d) d) ^ 2) =
        ∑ u : ZMod p, ∑ d : ZMod p, ∑ h : ZMod p,
          K (u - c * d) d * K (u - c * (d + h)) (d + h) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine (Fintype.sum_equiv (Equiv.addLeft d) _ _ fun h => ?_).symm
    simp
  rw [hstep1]
  trans (∑ d : ZMod p, ∑ h : ZMod p, ∑ u : ZMod p,
      K (u - c * d) d * K (u - c * (d + h)) (d + h))
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_comm
  trans (∑ d : ZMod p, ∑ h : ZMod p, ∑ x : ZMod p,
      K x d * K (x - c * h) (d + h))
  · refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun h _ => ?_
    refine (Fintype.sum_equiv (Equiv.addRight (c * d)) _ _ fun x => ?_).symm
    have he1 : x + c * d - c * d = x := by ring
    have he2 : x + c * d - c * (d + h) = x - c * h := by ring
    simp [he1, he2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_comm

lemma sum_sq_le_p {p : ℕ} [NeZero p] (F : ZMod p → ℝ) :
    (∑ h : ZMod p, F h) ^ 2 ≤ (p : ℝ) * ∑ h : ZMod p, F h ^ 2 := by
  simpa [ZMod.card] using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (ZMod p))) (f := F)

lemma diff_shift {p : ℕ} (f : ZMod p → ℝ) (b c x d h : ZMod p) :
    f (x + b * d) * f ((x - c * h) + b * (d + h)) = diff ((b - c) * h) f (x + b * d) := by
  dsimp [diff]
  congr 2
  ring

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R1.H2 := by
  intro p hp c₀ c₁ c₂ c₃ _ _ h03 _ h13 h23 f₀ f₁ f₂ f₃ hf₀ hf₁ hf₂
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  -- Step 1: eliminate f₀
  set L : ℝ := ∑ x : ZMod p, ∑ d : ZMod p,
    f₀ (x + c₀ * d) * f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d)
  have h1 : L ^ 2 ≤ (p : ℝ) * ∑ h₁ : ZMod p, ∑ x : ZMod p, ∑ d : ZMod p,
      OMA.Helpers.diff ((c₁ - c₀) * h₁) f₁ (x + c₁ * d) *
      OMA.Helpers.diff ((c₂ - c₀) * h₁) f₂ (x + c₂ * d) *
      OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃ (x + c₃ * d) := by
    have hcs := OMA.Helpers.cs_elim f₀ hf₀ c₀
      (fun x d => f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d))
    have hL : L = ∑ x : ZMod p, ∑ d : ZMod p,
        f₀ (x + c₀ * d) * (f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d)) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => by ring
    rw [hL]
    refine hcs.trans_eq ?_
    congr 1
    refine Finset.sum_congr rfl fun h₁ _ => Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun d _ => ?_
    rw [← OMA.Helpers.diff_shift f₁ c₁ c₀ x d h₁,
      ← OMA.Helpers.diff_shift f₂ c₂ c₀ x d h₁,
      ← OMA.Helpers.diff_shift f₃ c₃ c₀ x d h₁]
    ring
  -- Step 2: square and eliminate f₁
  set A : ZMod p → ℝ := fun h₁ => ∑ x : ZMod p, ∑ d : ZMod p,
    OMA.Helpers.diff ((c₁ - c₀) * h₁) f₁ (x + c₁ * d) *
    OMA.Helpers.diff ((c₂ - c₀) * h₁) f₂ (x + c₂ * d) *
    OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃ (x + c₃ * d)
  have hA_step : ∀ h₁ : ZMod p, A h₁ ^ 2 ≤ (p : ℝ) * ∑ h₂ : ZMod p, ∑ x : ZMod p, ∑ d : ZMod p,
      OMA.Helpers.diff ((c₂ - c₁) * h₂) (OMA.Helpers.diff ((c₂ - c₀) * h₁) f₂) (x + c₂ * d) *
      OMA.Helpers.diff ((c₃ - c₁) * h₂) (OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃) (x + c₃ * d) := by
    intro h₁
    have hcs := OMA.Helpers.cs_elim (OMA.Helpers.diff ((c₁ - c₀) * h₁) f₁)
      (OMA.Helpers.abs_diff_le_one hf₁ _) c₁
      (fun x d => OMA.Helpers.diff ((c₂ - c₀) * h₁) f₂ (x + c₂ * d) *
        OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃ (x + c₃ * d))
    have hA : A h₁ = ∑ x : ZMod p, ∑ d : ZMod p,
        OMA.Helpers.diff ((c₁ - c₀) * h₁) f₁ (x + c₁ * d) *
        (OMA.Helpers.diff ((c₂ - c₀) * h₁) f₂ (x + c₂ * d) *
         OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃ (x + c₃ * d)) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => by ring
    rw [hA]
    refine hcs.trans_eq ?_
    congr 1
    refine Finset.sum_congr rfl fun h₂ _ => Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun d _ => ?_
    rw [← OMA.Helpers.diff_shift (OMA.Helpers.diff ((c₂ - c₀) * h₁) f₂) c₂ c₁ x d h₂,
      ← OMA.Helpers.diff_shift (OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃) c₃ c₁ x d h₂]
    ring
  set B : ZMod p → ZMod p → ℝ := fun h₁ h₂ => ∑ x : ZMod p, ∑ d : ZMod p,
    OMA.Helpers.diff ((c₂ - c₁) * h₂) (OMA.Helpers.diff ((c₂ - c₀) * h₁) f₂) (x + c₂ * d) *
    OMA.Helpers.diff ((c₃ - c₁) * h₂) (OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃) (x + c₃ * d)
  have h2 : L ^ 4 ≤ (p : ℝ) ^ 4 * ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, B h₁ h₂ := by
    have hsq := pow_le_pow_left₀ (sq_nonneg L) h1 2
    have hpow4 : (L ^ 2) ^ 2 = L ^ 4 := by ring
    rw [hpow4, mul_pow] at hsq
    have hsum1 := OMA.Helpers.sum_sq_le_p A
    have hsum2 : (∑ h₁ : ZMod p, A h₁ ^ 2) ≤ (p : ℝ) * ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, B h₁ h₂ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun h₁ _ => hA_step h₁
    calc L ^ 4 ≤ (p : ℝ) ^ 2 * (∑ h₁ : ZMod p, A h₁) ^ 2 := hsq
      _ ≤ (p : ℝ) ^ 2 * ((p : ℝ) * ∑ h₁ : ZMod p, A h₁ ^ 2) :=
          mul_le_mul_of_nonneg_left hsum1 (sq_nonneg _)
      _ ≤ (p : ℝ) ^ 2 * ((p : ℝ) * ((p : ℝ) * ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, B h₁ h₂)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum2 hp0) (sq_nonneg _)
      _ = (p : ℝ) ^ 4 * ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, B h₁ h₂ := by ring
  -- Step 3: square and eliminate f₂
  have hB_step : ∀ h₁ h₂ : ZMod p, B h₁ h₂ ^ 2 ≤ (p : ℝ) ^ 2 * ∑ h₃ : ZMod p, ∑ x : ZMod p,
      OMA.Helpers.diff ((c₃ - c₂) * h₃)
        (OMA.Helpers.diff ((c₃ - c₁) * h₂) (OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃)) x := by
    intro h₁ h₂
    have hf2' : ∀ x : ZMod p,
        |OMA.Helpers.diff ((c₂ - c₁) * h₂) (OMA.Helpers.diff ((c₂ - c₀) * h₁) f₂) x| ≤ 1 :=
      OMA.Helpers.abs_diff_le_one (OMA.Helpers.abs_diff_le_one hf₂ _) _
    have hcs := OMA.Helpers.cs_elim _ hf2' c₂
      (fun x d => OMA.Helpers.diff ((c₃ - c₁) * h₂) (OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃) (x + c₃ * d))
    refine hcs.trans_eq ?_
    have hinner : ∀ h₃ : ZMod p,
        (∑ x : ZMod p, ∑ d : ZMod p,
          OMA.Helpers.diff ((c₃ - c₁) * h₂) (OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃) (x + c₃ * d) *
          OMA.Helpers.diff ((c₃ - c₁) * h₂) (OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃)
            ((x - c₂ * h₃) + c₃ * (d + h₃))) =
        (p : ℝ) * ∑ x : ZMod p,
          OMA.Helpers.diff ((c₃ - c₂) * h₃)
            (OMA.Helpers.diff ((c₃ - c₁) * h₂) (OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃)) x := by
      intro h₃
      set F : ZMod p → ℝ :=
        OMA.Helpers.diff ((c₃ - c₂) * h₃)
          (OMA.Helpers.diff ((c₃ - c₁) * h₂) (OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃))
      have heq1 : ∀ x d : ZMod p,
          OMA.Helpers.diff ((c₃ - c₁) * h₂) (OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃) (x + c₃ * d) *
          OMA.Helpers.diff ((c₃ - c₁) * h₂) (OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃)
            ((x - c₂ * h₃) + c₃ * (d + h₃)) = F (x + c₃ * d) := fun x d =>
        OMA.Helpers.diff_shift _ c₃ c₂ x d h₃
      simp_rw [heq1]
      rw [Finset.sum_comm]
      have hre : ∀ d : ZMod p, (∑ x : ZMod p, F (x + c₃ * d)) = ∑ y : ZMod p, F y := fun d =>
        Fintype.sum_equiv (Equiv.addRight (c₃ * d)) _ _ (fun _ => rfl)
      simp_rw [hre]
      simp [ZMod.card]
    simp_rw [hinner, ← Finset.mul_sum]
    ring
  have h3 : L ^ 8 ≤ (p : ℝ) ^ 12 * ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p, ∑ x : ZMod p,
      OMA.Helpers.diff ((c₃ - c₂) * h₃)
        (OMA.Helpers.diff ((c₃ - c₁) * h₂) (OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃)) x := by
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ L ^ 4) h2 2
    have hpow8 : (L ^ 4) ^ 2 = L ^ 8 := by ring
    rw [hpow8, mul_pow] at hsq
    have hsum1 := OMA.Helpers.sum_sq_le_p (fun h₁ => ∑ h₂ : ZMod p, B h₁ h₂)
    have hsum2 : (∑ h₁ : ZMod p, (∑ h₂ : ZMod p, B h₁ h₂) ^ 2) ≤
        (p : ℝ) * ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, B h₁ h₂ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun h₁ _ => OMA.Helpers.sum_sq_le_p (B h₁)
    have hsum3 : (∑ h₁ : ZMod p, ∑ h₂ : ZMod p, B h₁ h₂ ^ 2) ≤
        (p : ℝ) ^ 2 * ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p, ∑ x : ZMod p,
          OMA.Helpers.diff ((c₃ - c₂) * h₃)
            (OMA.Helpers.diff ((c₃ - c₁) * h₂) (OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃)) x := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun h₁ _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun h₂ _ => hB_step h₁ h₂
    calc L ^ 8 ≤ ((p : ℝ) ^ 4) ^ 2 * (∑ h₁ : ZMod p, ∑ h₂ : ZMod p, B h₁ h₂) ^ 2 := hsq
      _ ≤ ((p : ℝ) ^ 4) ^ 2 * ((p : ℝ) * ∑ h₁ : ZMod p, (∑ h₂ : ZMod p, B h₁ h₂) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum1 (by positivity)
      _ ≤ ((p : ℝ) ^ 4) ^ 2 * ((p : ℝ) * ((p : ℝ) * ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, B h₁ h₂ ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum2 hp0) (by positivity)
      _ ≤ ((p : ℝ) ^ 4) ^ 2 * ((p : ℝ) * ((p : ℝ) * ((p : ℝ) ^ 2 *
            ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p, ∑ x : ZMod p,
              OMA.Helpers.diff ((c₃ - c₂) * h₃)
                (OMA.Helpers.diff ((c₃ - c₁) * h₂) (OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃)) x))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum3 hp0) hp0) (by positivity)
      _ = (p : ℝ) ^ 12 * ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p, ∑ x : ZMod p,
            OMA.Helpers.diff ((c₃ - c₂) * h₃)
              (OMA.Helpers.diff ((c₃ - c₁) * h₂) (OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃)) x := by ring
  -- Step 4: reindex h₁, h₂, h₃ via nonzero multipliers in the field ZMod p and move x outermost
  refine h3.trans_eq ?_
  congr 1
  have hne0 : c₃ - c₀ ≠ 0 := sub_ne_zero.mpr h03.symm
  have hne1 : c₃ - c₁ ≠ 0 := sub_ne_zero.mpr h13.symm
  have hne2 : c₃ - c₂ ≠ 0 := sub_ne_zero.mpr h23.symm
  have hre :
      (∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p, ∑ x : ZMod p,
        OMA.Helpers.diff ((c₃ - c₂) * h₃)
          (OMA.Helpers.diff ((c₃ - c₁) * h₂) (OMA.Helpers.diff ((c₃ - c₀) * h₁) f₃)) x) =
      ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p, ∑ x : ZMod p,
        OMA.Helpers.diff h₃ (OMA.Helpers.diff h₂ (OMA.Helpers.diff h₁ f₃)) x := by
    refine Fintype.sum_equiv (Equiv.mulLeft₀ (c₃ - c₀) hne0) _ _ fun h₁ => ?_
    refine Fintype.sum_equiv (Equiv.mulLeft₀ (c₃ - c₁) hne1) _ _ fun h₂ => ?_
    refine Fintype.sum_equiv (Equiv.mulLeft₀ (c₃ - c₂) hne2) _ _ fun h₃ => ?_
    rfl
  rw [hre]
  have hcomm :
      (∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p, ∑ x : ZMod p,
        OMA.Helpers.diff h₃ (OMA.Helpers.diff h₂ (OMA.Helpers.diff h₁ f₃)) x) =
      ∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
        OMA.Helpers.diff h₃ (OMA.Helpers.diff h₂ (OMA.Helpers.diff h₁ f₃)) x := by
    trans (∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ x : ZMod p, ∑ h₃ : ZMod p,
        OMA.Helpers.diff h₃ (OMA.Helpers.diff h₂ (OMA.Helpers.diff h₁ f₃)) x)
    · refine Finset.sum_congr rfl fun h₁ _ => Finset.sum_congr rfl fun h₂ _ => Finset.sum_comm
    trans (∑ h₁ : ZMod p, ∑ x : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
        OMA.Helpers.diff h₃ (OMA.Helpers.diff h₂ (OMA.Helpers.diff h₁ f₃)) x)
    · refine Finset.sum_congr rfl fun h₁ _ => Finset.sum_comm
    exact Finset.sum_comm
  rw [hcomm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun h₁ _ =>
    Finset.sum_congr rfl fun h₂ _ => Finset.sum_congr rfl fun h₃ _ => ?_
  dsimp [OMA.Helpers.diff]
  have e1 : x + h₂ + h₁ = x + h₁ + h₂ := by ring
  have e2 : x + h₃ + h₁ = x + h₁ + h₃ := by ring
  have e3 : x + h₃ + h₂ = x + h₂ + h₃ := by ring
  have e4 : x + h₂ + h₃ + h₁ = x + h₁ + h₂ + h₃ := by ring
  rw [e1, e2, e3, e4]
  ring
