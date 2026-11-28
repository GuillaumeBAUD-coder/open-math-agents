import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R1
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1.R1.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1.R1
-- Credit: @LAPRAI
-- Generalized von Neumann inequality for four distinct linear forms, by three Cauchy–Schwarz steps.

namespace OMA.Erdos142_U3_vonNeumann

/-- Multiplicative derivative of a function on `ZMod p`. -/
def D {p : ℕ} (f : ZMod p → ℝ) (s y : ZMod p) : ℝ := f y * f (y + s)

lemma absD {p : ℕ} (f : ZMod p → ℝ) (hf : ∀ x, |f x| ≤ 1) (s : ZMod p) :
    ∀ y, |D f s y| ≤ 1 := by
  intro y
  simp only [D, abs_mul]
  have h1 := hf y
  have h2 := hf (y + s)
  nlinarith [abs_nonneg (f y), abs_nonneg (f (y + s))]

/-- One Cauchy–Schwarz step removing the function on the form `x + c d`. -/
lemma cs_step {p : ℕ} [Fact p.Prime] (f : ZMod p → ℝ) (hf : ∀ x, |f x| ≤ 1) (c : ZMod p)
    (G : ZMod p → ZMod p → ℝ) :
    (∑ x : ZMod p, ∑ d : ZMod p, f (x + c * d) * G x d) ^ 2 ≤
      (p : ℝ) * ∑ h : ZMod p, ∑ x : ZMod p, ∑ d : ZMod p, G x d * G (x - c * h) (d + h) := by
  have e1 : ∑ x : ZMod p, ∑ d : ZMod p, f (x + c * d) * G x d
      = ∑ u : ZMod p, f u * ∑ d : ZMod p, G (u - c * d) d := by
    simp_rw [Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    exact Fintype.sum_equiv (Equiv.addRight (c * d)) _ _ (fun x => by simp)
  rw [e1]
  have hf2 : ∑ u : ZMod p, f u ^ 2 ≤ p := by
    calc ∑ u : ZMod p, f u ^ 2 ≤ ∑ _u : ZMod p, (1 : ℝ) :=
          Finset.sum_le_sum fun u _ => by
            have := abs_le.mp (hf u)
            nlinarith
      _ = p := by simp [ZMod.card]
  have s1 : ∀ u : ZMod p, (∑ d : ZMod p, G (u - c * d) d) ^ 2
      = ∑ d : ZMod p, ∑ h : ZMod p, G (u - c * d) d * G (u - c * d - c * h) (d + h) := by
    intro u
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    refine Fintype.sum_equiv (Equiv.subRight d) _ _ (fun d' => ?_)
    simp only [Equiv.subRight_apply]
    rw [show u - c * d - c * (d' - d) = u - c * d' by ring, show d + (d' - d) = d' by ring]
  have e2 : ∑ u : ZMod p, (∑ d : ZMod p, G (u - c * d) d) ^ 2
      = ∑ h : ZMod p, ∑ x : ZMod p, ∑ d : ZMod p, G x d * G (x - c * h) (d + h) := by
    rw [Finset.sum_congr rfl fun u _ => s1 u]
    calc ∑ u : ZMod p, ∑ d : ZMod p, ∑ h : ZMod p,
          G (u - c * d) d * G (u - c * d - c * h) (d + h)
        = ∑ d : ZMod p, ∑ u : ZMod p, ∑ h : ZMod p,
          G (u - c * d) d * G (u - c * d - c * h) (d + h) := Finset.sum_comm
      _ = ∑ d : ZMod p, ∑ h : ZMod p, ∑ u : ZMod p,
          G (u - c * d) d * G (u - c * d - c * h) (d + h) :=
          Finset.sum_congr rfl fun d _ => Finset.sum_comm
      _ = ∑ h : ZMod p, ∑ d : ZMod p, ∑ u : ZMod p,
          G (u - c * d) d * G (u - c * d - c * h) (d + h) := Finset.sum_comm
      _ = ∑ h : ZMod p, ∑ d : ZMod p, ∑ x : ZMod p, G x d * G (x - c * h) (d + h) :=
          Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun d _ =>
            Fintype.sum_equiv (Equiv.subRight (c * d)) _ _ (fun u => rfl)
      _ = ∑ h : ZMod p, ∑ x : ZMod p, ∑ d : ZMod p, G x d * G (x - c * h) (d + h) :=
          Finset.sum_congr rfl fun h _ => Finset.sum_comm
  calc (∑ u : ZMod p, f u * ∑ d : ZMod p, G (u - c * d) d) ^ 2
      ≤ (∑ u : ZMod p, f u ^ 2) * ∑ u : ZMod p, (∑ d : ZMod p, G (u - c * d) d) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (p : ℝ) * ∑ u : ZMod p, (∑ d : ZMod p, G (u - c * d) d) ^ 2 :=
        mul_le_mul_of_nonneg_right hf2 (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by rw [e2]

lemma step4 {p : ℕ} [Fact p.Prime] (c₀ c₁ c₂ c₃ : ZMod p) (f₀ f₁ f₂ f₃ : ZMod p → ℝ)
    (hf : ∀ x, |f₀ x| ≤ 1) :
    (∑ x : ZMod p, ∑ d : ZMod p,
      f₀ (x + c₀ * d) * f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d)) ^ 2 ≤
    (p : ℝ) * ∑ h : ZMod p, ∑ x : ZMod p, ∑ d : ZMod p,
      D f₁ ((c₁ - c₀) * h) (x + c₁ * d) * D f₂ ((c₂ - c₀) * h) (x + c₂ * d) *
        D f₃ ((c₃ - c₀) * h) (x + c₃ * d) := by
  have e : (∑ x : ZMod p, ∑ d : ZMod p,
      f₀ (x + c₀ * d) * f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d)) =
      ∑ x : ZMod p, ∑ d : ZMod p,
      f₀ (x + c₀ * d) * (f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d)) := by
    simp only [mul_assoc]
  rw [e]
  refine (cs_step f₀ hf c₀
    (fun x d => f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d))).trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun d _ => ?_
  simp only [D]
  rw [show x - c₀ * h + c₁ * (d + h) = x + c₁ * d + (c₁ - c₀) * h by ring,
    show x - c₀ * h + c₂ * (d + h) = x + c₂ * d + (c₂ - c₀) * h by ring,
    show x - c₀ * h + c₃ * (d + h) = x + c₃ * d + (c₃ - c₀) * h by ring]
  ring

lemma step3 {p : ℕ} [Fact p.Prime] (c₁ c₂ c₃ : ZMod p) (g₁ g₂ g₃ : ZMod p → ℝ)
    (hg : ∀ x, |g₁ x| ≤ 1) :
    (∑ x : ZMod p, ∑ d : ZMod p, g₁ (x + c₁ * d) * g₂ (x + c₂ * d) * g₃ (x + c₃ * d)) ^ 2 ≤
    (p : ℝ) * ∑ h : ZMod p, ∑ x : ZMod p, ∑ d : ZMod p,
      D g₂ ((c₂ - c₁) * h) (x + c₂ * d) * D g₃ ((c₃ - c₁) * h) (x + c₃ * d) := by
  have e : (∑ x : ZMod p, ∑ d : ZMod p, g₁ (x + c₁ * d) * g₂ (x + c₂ * d) * g₃ (x + c₃ * d)) =
      ∑ x : ZMod p, ∑ d : ZMod p, g₁ (x + c₁ * d) * (g₂ (x + c₂ * d) * g₃ (x + c₃ * d)) := by
    simp only [mul_assoc]
  rw [e]
  refine (cs_step g₁ hg c₁ (fun x d => g₂ (x + c₂ * d) * g₃ (x + c₃ * d))).trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun d _ => ?_
  simp only [D]
  rw [show x - c₁ * h + c₂ * (d + h) = x + c₂ * d + (c₂ - c₁) * h by ring,
    show x - c₁ * h + c₃ * (d + h) = x + c₃ * d + (c₃ - c₁) * h by ring]
  ring

lemma step2 {p : ℕ} [Fact p.Prime] (c₂ c₃ : ZMod p) (k₂ k₃ : ZMod p → ℝ)
    (hk : ∀ x, |k₂ x| ≤ 1) :
    (∑ x : ZMod p, ∑ d : ZMod p, k₂ (x + c₂ * d) * k₃ (x + c₃ * d)) ^ 2 ≤
    (p : ℝ) * ∑ h : ZMod p, ∑ x : ZMod p, ∑ d : ZMod p, D k₃ ((c₃ - c₂) * h) (x + c₃ * d) := by
  refine (cs_step k₂ hk c₂ (fun x d => k₃ (x + c₃ * d))).trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun d _ => ?_
  simp only [D]
  rw [show x - c₂ * h + c₃ * (d + h) = x + c₃ * d + (c₃ - c₂) * h by ring]

lemma step1 {p : ℕ} [Fact p.Prime] (c : ZMod p) (m : ZMod p → ℝ) :
    ∑ x : ZMod p, ∑ d : ZMod p, m (x + c * d) = (p : ℝ) * ∑ y : ZMod p, m y := by
  rw [Finset.sum_comm]
  have hx : ∀ d : ZMod p, ∑ x : ZMod p, m (x + c * d) = ∑ y : ZMod p, m y := fun d =>
    Fintype.sum_equiv (Equiv.addRight (c * d)) _ _ (fun x => rfl)
  simp only [hx, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

lemma chain {p : ℕ} [Fact p.Prime] {Λ W : ℝ} {A : ZMod p → ℝ} {B : ZMod p → ZMod p → ℝ}
    {Cc M : ZMod p → ZMod p → ZMod p → ℝ}
    (hA : Λ ^ 2 ≤ (p : ℝ) * ∑ h : ZMod p, A h)
    (hB : ∀ h, A h ^ 2 ≤ (p : ℝ) * ∑ h' : ZMod p, B h h')
    (hC : ∀ h h', B h h' ^ 2 ≤ (p : ℝ) * ∑ h'' : ZMod p, Cc h h' h'')
    (hCe : ∀ h h' h'', Cc h h' h'' = (p : ℝ) * M h h' h'')
    (hU : ∑ h : ZMod p, ∑ h' : ZMod p, ∑ h'' : ZMod p, M h h' h'' = W) :
    Λ ^ 8 ≤ (p : ℝ) ^ 12 * W := by
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have cs : ∀ a : ZMod p → ℝ, (∑ h : ZMod p, a h) ^ 2 ≤ (p : ℝ) * ∑ h : ZMod p, a h ^ 2 := by
    intro a
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul] at this
    linarith
  have h1 : (∑ h : ZMod p, A h) ^ 2 ≤ (p : ℝ) ^ 2 * ∑ h : ZMod p, ∑ h' : ZMod p, B h h' := by
    calc (∑ h : ZMod p, A h) ^ 2 ≤ (p : ℝ) * ∑ h : ZMod p, A h ^ 2 := cs A
      _ ≤ (p : ℝ) * ∑ h : ZMod p, ((p : ℝ) * ∑ h' : ZMod p, B h h') :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ => hB h) hp
      _ = (p : ℝ) ^ 2 * ∑ h : ZMod p, ∑ h' : ZMod p, B h h' := by
          rw [← Finset.mul_sum]; ring
  have h2 : (∑ h : ZMod p, ∑ h' : ZMod p, B h h') ^ 2 ≤ (p : ℝ) ^ 4 * W := by
    calc (∑ h : ZMod p, ∑ h' : ZMod p, B h h') ^ 2
        ≤ (p : ℝ) * ∑ h : ZMod p, (∑ h' : ZMod p, B h h') ^ 2 := cs _
      _ ≤ (p : ℝ) * ∑ h : ZMod p, ((p : ℝ) * ∑ h' : ZMod p, B h h' ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ => cs _) hp
      _ ≤ (p : ℝ) * ∑ h : ZMod p, ((p : ℝ) * ∑ h' : ZMod p,
            ((p : ℝ) * ∑ h'' : ZMod p, Cc h h' h'')) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ =>
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h' _ => hC h h') hp) hp
      _ = (p : ℝ) ^ 4 * W := by
          rw [← hU]
          simp only [hCe, ← Finset.mul_sum]
          ring
  calc Λ ^ 8 = (Λ ^ 2) ^ 4 := by ring
    _ ≤ ((p : ℝ) * ∑ h : ZMod p, A h) ^ 4 := by gcongr
    _ = (p : ℝ) ^ 4 * ((∑ h : ZMod p, A h) ^ 2) ^ 2 := by ring
    _ ≤ (p : ℝ) ^ 4 * ((p : ℝ) ^ 2 * ∑ h : ZMod p, ∑ h' : ZMod p, B h h') ^ 2 := by gcongr
    _ = (p : ℝ) ^ 8 * (∑ h : ZMod p, ∑ h' : ZMod p, B h h') ^ 2 := by ring
    _ ≤ (p : ℝ) ^ 8 * ((p : ℝ) ^ 4 * W) := by gcongr
    _ = (p : ℝ) ^ 12 * W := by ring

lemma subst {p : ℕ} [Fact p.Prime] (k : ZMod p) (hk : k ≠ 0) (F : ZMod p → ℝ) :
    ∑ h : ZMod p, F (k * h) = ∑ u : ZMod p, F u :=
  (mulLeft_bijective₀ k hk).sum_comp F

end OMA.Erdos142_U3_vonNeumann

open OMA.Erdos142_U3_vonNeumann in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R1.H2 := by
  intro p _ c₀ c₁ c₂ c₃ h01 h02 h03 h12 h13 h23 f₀ f₁ f₂ f₃ hf0 hf1 hf2
  have ha : c₃ - c₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm h03)
  have hb : c₃ - c₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h13)
  have he : c₃ - c₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm h23)
  have hA := step4 c₀ c₁ c₂ c₃ f₀ f₁ f₂ f₃ hf0
  have hB := fun h : ZMod p => step3 c₁ c₂ c₃ (D f₁ ((c₁ - c₀) * h)) (D f₂ ((c₂ - c₀) * h))
    (D f₃ ((c₃ - c₀) * h)) (absD f₁ hf1 _)
  have hC := fun (h h' : ZMod p) => step2 c₂ c₃ (D (D f₂ ((c₂ - c₀) * h)) ((c₂ - c₁) * h'))
    (D (D f₃ ((c₃ - c₀) * h)) ((c₃ - c₁) * h')) (absD _ (absD f₂ hf2 _) _)
  have hCe := fun (h h' h'' : ZMod p) =>
    step1 c₃ (D (D (D f₃ ((c₃ - c₀) * h)) ((c₃ - c₁) * h')) ((c₃ - c₂) * h''))
  have expand : ∀ y s t u : ZMod p, D (D (D f₃ s) t) u y =
      f₃ y * f₃ (y + s) * f₃ (y + t) * f₃ (y + s + t) *
        f₃ (y + u) * f₃ (y + s + u) * f₃ (y + t + u) * f₃ (y + s + t + u) := by
    intro y s t u
    simp only [D]
    rw [show y + u + t + s = y + s + t + u by ring, show y + u + t = y + t + u by ring,
      show y + u + s = y + s + u by ring, show y + t + s = y + s + t by ring]
    ring
  have hU : ∑ h : ZMod p, ∑ h' : ZMod p, ∑ h'' : ZMod p, ∑ y : ZMod p,
      D (D (D f₃ ((c₃ - c₀) * h)) ((c₃ - c₁) * h')) ((c₃ - c₂) * h'') y =
      ∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
        f₃ x * f₃ (x + h₁) * f₃ (x + h₂) * f₃ (x + h₁ + h₂) *
        f₃ (x + h₃) * f₃ (x + h₁ + h₃) * f₃ (x + h₂ + h₃) * f₃ (x + h₁ + h₂ + h₃) := by
    simp only [expand]
    let T : ZMod p → ZMod p → ZMod p → ZMod p → ℝ := fun x h₁ h₂ h₃ =>
      f₃ x * f₃ (x + h₁) * f₃ (x + h₂) * f₃ (x + h₁ + h₂) *
        f₃ (x + h₃) * f₃ (x + h₁ + h₃) * f₃ (x + h₂ + h₃) * f₃ (x + h₁ + h₂ + h₃)
    show ∑ h : ZMod p, ∑ h' : ZMod p, ∑ h'' : ZMod p, ∑ y : ZMod p,
          T y ((c₃ - c₀) * h) ((c₃ - c₁) * h') ((c₃ - c₂) * h'') =
        ∑ y : ZMod p, ∑ s : ZMod p, ∑ t : ZMod p, ∑ u : ZMod p, T y s t u
    calc ∑ h : ZMod p, ∑ h' : ZMod p, ∑ h'' : ZMod p, ∑ y : ZMod p,
          T y ((c₃ - c₀) * h) ((c₃ - c₁) * h') ((c₃ - c₂) * h'')
        = ∑ h : ZMod p, ∑ h' : ZMod p, ∑ u : ZMod p, ∑ y : ZMod p,
          T y ((c₃ - c₀) * h) ((c₃ - c₁) * h') u :=
          Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ =>
            subst _ he (fun u => ∑ y : ZMod p, T y ((c₃ - c₀) * h) ((c₃ - c₁) * h') u)
      _ = ∑ h : ZMod p, ∑ t : ZMod p, ∑ u : ZMod p, ∑ y : ZMod p,
          T y ((c₃ - c₀) * h) t u :=
          Finset.sum_congr rfl fun h _ =>
            subst _ hb (fun t => ∑ u : ZMod p, ∑ y : ZMod p, T y ((c₃ - c₀) * h) t u)
      _ = ∑ s : ZMod p, ∑ t : ZMod p, ∑ u : ZMod p, ∑ y : ZMod p, T y s t u :=
          subst _ ha (fun s => ∑ t : ZMod p, ∑ u : ZMod p, ∑ y : ZMod p, T y s t u)
      _ = ∑ s : ZMod p, ∑ t : ZMod p, ∑ y : ZMod p, ∑ u : ZMod p, T y s t u :=
          Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => Finset.sum_comm
      _ = ∑ s : ZMod p, ∑ y : ZMod p, ∑ t : ZMod p, ∑ u : ZMod p, T y s t u :=
          Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = ∑ y : ZMod p, ∑ s : ZMod p, ∑ t : ZMod p, ∑ u : ZMod p, T y s t u :=
          Finset.sum_comm
  exact chain hA hB hC hCe hU
