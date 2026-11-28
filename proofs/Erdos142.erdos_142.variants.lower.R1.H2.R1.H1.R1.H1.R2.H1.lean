import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R2
import Mathlib

/-!
# Step H1 of the reduction Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1.R2

Fourier extraction for the Gowers U^3 cube sum on ZMod p. Writing g_h (x) = f x * f (x + h),
the cube sum of f is the sum over h of the U^2 sum of g_h. For a real function g bounded by 1,
with Fourier coefficients G(xi) = sum_x g(x) e(xi x) and autocorrelation C(h) = sum_x g(x) g(x+h):

* |G(xi)|^2 = sum_h C(h) e(xi h) = sum_h C(h) e(-xi h)   (two changes of variables),
* sum_xi |G(xi)|^4 = p sum_h C(h)^2 = p U^2(g)            (orthogonality of characters),
* sum_xi |G(xi)|^2 = p C(0) <= p^2,

so U^2(g) <= p max_xi |G(xi)|^2. Choosing a maximizing frequency for each h gives the claim.
-/

namespace U2F

open Finset

variable {p : ℕ} [Fact p.Prime]

/-- The standard additive character of `ZMod p`. -/
noncomputable def e : AddChar (ZMod p) ℂ := ZMod.stdAddChar

lemma e_add (a b : ZMod p) : e (a + b) = e a * e b := AddChar.map_add_eq_mul _ a b

lemma orth (b : ZMod p) : ∑ ξ : ZMod p, e (ξ * b) = if b = 0 then (p : ℂ) else 0 := by
  have h := AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar p)
  simpa [ZMod.card, e] using h

lemma conj_e (a : ZMod p) : (starRingEnd ℂ) (e a) = e (-a) := by
  have h1 : e (-a) = (e a)⁻¹ := AddChar.map_neg_eq_inv _ a
  have h2 : ‖e a‖ = 1 := Circle.norm_coe (ZMod.toCircle a)
  rw [h1, Complex.inv_eq_conj h2]

lemma parseval (c : ZMod p → ℂ) :
    ∑ ξ, (∑ h, c h * e (ξ * h)) * (∑ k, c k * e (ξ * (-k))) = p * ∑ h, c h * c h := by
  calc ∑ ξ, (∑ h, c h * e (ξ * h)) * (∑ k, c k * e (ξ * (-k)))
      = ∑ ξ, ∑ h, ∑ k, c h * c k * e (ξ * (h - k)) := by
        refine sum_congr rfl fun ξ _ => ?_
        rw [sum_mul_sum]
        refine sum_congr rfl fun h _ => sum_congr rfl fun k _ => ?_
        rw [show ξ * (h - k) = ξ * h + ξ * (-k) by ring, e_add]
        ring
    _ = ∑ h, ∑ k, c h * c k * ∑ ξ, e (ξ * (h - k)) := by
        rw [sum_comm]
        refine sum_congr rfl fun h _ => ?_
        rw [sum_comm]
        exact sum_congr rfl fun k _ => (mul_sum _ _ _).symm
    _ = ∑ h, c h * c h * p := by
        refine sum_congr rfl fun h _ => ?_
        simp [orth, sub_eq_zero]
    _ = p * ∑ h, c h * c h := by
        rw [mul_sum]
        exact sum_congr rfl fun h _ => mul_comm _ _

lemma prod_formA (g : ZMod p → ℂ) (ξ : ZMod p) :
    (∑ x, g x * e (ξ * x)) * (∑ y, g y * e (ξ * (-y))) =
      ∑ h, (∑ x, g x * g (x + h)) * e (ξ * (-h)) := by
  calc (∑ x, g x * e (ξ * x)) * (∑ y, g y * e (ξ * (-y)))
      = ∑ x, ∑ h, g x * g (x + h) * e (ξ * (-h)) := by
        rw [sum_mul_sum]
        refine sum_congr rfl fun x _ => ?_
        refine (Fintype.sum_equiv (Equiv.addLeft x)
          (fun h => g x * g (x + h) * e (ξ * (-h)))
          (fun y => g x * e (ξ * x) * (g y * e (ξ * (-y)))) fun h => ?_).symm
        show g x * g (x + h) * e (ξ * (-h)) =
          g x * e (ξ * x) * (g (x + h) * e (ξ * (-(x + h))))
        have he : e (ξ * (-h)) = e (ξ * x) * e (ξ * (-(x + h))) := by
          rw [← e_add]
          congr 1
          ring
        rw [he]
        ring
    _ = ∑ h, (∑ x, g x * g (x + h)) * e (ξ * (-h)) := by
        rw [sum_comm]
        exact sum_congr rfl fun h _ => (sum_mul _ _ _).symm

lemma prod_formB (g : ZMod p → ℂ) (ξ : ZMod p) :
    (∑ x, g x * e (ξ * x)) * (∑ y, g y * e (ξ * (-y))) =
      ∑ h, (∑ x, g x * g (x + h)) * e (ξ * h) := by
  calc (∑ x, g x * e (ξ * x)) * (∑ y, g y * e (ξ * (-y)))
      = ∑ y, ∑ h, g y * g (y + h) * e (ξ * h) := by
        rw [mul_comm, sum_mul_sum]
        refine sum_congr rfl fun y _ => ?_
        refine (Fintype.sum_equiv (Equiv.addLeft y)
          (fun h => g y * g (y + h) * e (ξ * h))
          (fun x => g y * e (ξ * (-y)) * (g x * e (ξ * x))) fun h => ?_).symm
        show g y * g (y + h) * e (ξ * h) =
          g y * e (ξ * (-y)) * (g (y + h) * e (ξ * (y + h)))
        have he : e (ξ * h) = e (ξ * (-y)) * e (ξ * (y + h)) := by
          rw [← e_add]
          congr 1
          ring
        rw [he]
        ring
    _ = ∑ h, (∑ x, g x * g (x + h)) * e (ξ * h) := by
        rw [sum_comm]
        exact sum_congr rfl fun h _ => (sum_mul _ _ _).symm

lemma sum_T_sq (g : ZMod p → ℂ) :
    ∑ ξ, ((∑ x, g x * e (ξ * x)) * (∑ y, g y * e (ξ * (-y)))) ^ 2 =
      p * ∑ h, (∑ x, g x * g (x + h)) ^ 2 := by
  calc ∑ ξ, ((∑ x, g x * e (ξ * x)) * (∑ y, g y * e (ξ * (-y)))) ^ 2
      = ∑ ξ, (∑ h, (∑ x, g x * g (x + h)) * e (ξ * h)) *
          (∑ k, (∑ x, g x * g (x + k)) * e (ξ * (-k))) := by
        refine sum_congr rfl fun ξ _ => ?_
        rw [sq]
        exact congrArg₂ (· * ·) (prod_formB g ξ) (prod_formA g ξ)
    _ = p * ∑ h, (∑ x, g x * g (x + h)) * (∑ x, g x * g (x + h)) :=
        parseval fun h => ∑ x, g x * g (x + h)
    _ = p * ∑ h, (∑ x, g x * g (x + h)) ^ 2 := by simp only [sq]

lemma sum_T (g : ZMod p → ℂ) :
    ∑ ξ, (∑ x, g x * e (ξ * x)) * (∑ y, g y * e (ξ * (-y))) = p * ∑ x, g x * g x := by
  calc ∑ ξ, (∑ x, g x * e (ξ * x)) * (∑ y, g y * e (ξ * (-y)))
      = ∑ ξ, ∑ h, (∑ x, g x * g (x + h)) * e (ξ * h) :=
        sum_congr rfl fun ξ _ => prod_formB g ξ
    _ = ∑ h, (∑ x, g x * g (x + h)) * ∑ ξ, e (ξ * h) := by
        rw [sum_comm]
        exact sum_congr rfl fun h _ => (mul_sum _ _ _).symm
    _ = ∑ h, (∑ x, g x * g (x + h)) * (if h = 0 then (p : ℂ) else 0) := by simp_rw [orth]
    _ = p * ∑ x, g x * g x := by
        simp [mul_comm]

/-- The Fourier coefficient at frequency `ξ`. -/
noncomputable def G (g : ZMod p → ℝ) (ξ : ZMod p) : ℂ := ∑ x, (g x : ℂ) * e (ξ * x)

/-- The autocorrelation. -/
def Cr (g : ZMod p → ℝ) (h : ZMod p) : ℝ := ∑ x, g x * g (x + h)

lemma normSq_G (g : ZMod p → ℝ) (ξ : ZMod p) :
    ((‖G g ξ‖ ^ 2 : ℝ) : ℂ) =
      (∑ x, (g x : ℂ) * e (ξ * x)) * (∑ y, (g y : ℂ) * e (ξ * (-y))) := by
  have hc : (starRingEnd ℂ) (G g ξ) = ∑ y, (g y : ℂ) * e (ξ * (-y)) := by
    simp only [G, map_sum, map_mul, Complex.conj_ofReal, conj_e, mul_neg]
  rw [← hc]
  change ((‖G g ξ‖ ^ 2 : ℝ) : ℂ) = G g ξ * (starRingEnd ℂ) (G g ξ)
  rw [Complex.mul_conj']
  push_cast
  rfl

lemma sum_M_sq (g : ZMod p → ℝ) :
    ∑ ξ, (‖G g ξ‖ ^ 2) ^ 2 = p * ∑ h, Cr g h ^ 2 := by
  have h := sum_T_sq (p := p) (fun x => (g x : ℂ))
  apply Complex.ofReal_injective
  have hl : ((∑ ξ, (‖G g ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) =
      ∑ ξ, ((∑ x, (g x : ℂ) * e (ξ * x)) * (∑ y, (g y : ℂ) * e (ξ * (-y)))) ^ 2 := by
    rw [Complex.ofReal_sum]
    refine sum_congr rfl fun ξ _ => ?_
    rw [← normSq_G]
    push_cast
    rfl
  rw [hl, h]
  simp only [Cr]
  push_cast
  rfl

lemma sum_M (g : ZMod p → ℝ) :
    ∑ ξ, ‖G g ξ‖ ^ 2 = p * ∑ x, g x * g x := by
  have h := sum_T (p := p) (fun x => (g x : ℂ))
  apply Complex.ofReal_injective
  have hl : ((∑ ξ, ‖G g ξ‖ ^ 2 : ℝ) : ℂ) =
      ∑ ξ, (∑ x, (g x : ℂ) * e (ξ * x)) * (∑ y, (g y : ℂ) * e (ξ * (-y))) := by
    rw [Complex.ofReal_sum]
    exact sum_congr rfl fun ξ _ => normSq_G g ξ
  rw [hl, h]
  push_cast
  rfl

lemma U2_eq (g : ZMod p → ℝ) :
    ∑ x, ∑ h₂, ∑ h₃, g x * g (x + h₂) * g (x + h₃) * g (x + h₂ + h₃) = ∑ h, Cr g h ^ 2 := by
  rw [sum_comm]
  refine sum_congr rfl fun h _ => ?_
  rw [sq, Cr, sum_mul_sum]
  refine sum_congr rfl fun x _ => ?_
  refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun h₃ => ?_
  show g x * g (x + h) * g (x + h₃) * g (x + h + h₃) =
    g x * g (x + h) * (g (x + h₃) * g (x + h₃ + h))
  rw [add_right_comm x h h₃]
  ring

lemma exists_large_coeff (g : ZMod p → ℝ) (hg : ∀ x, |g x| ≤ 1) :
    ∃ ξ₀ : ZMod p, ∑ x, ∑ h₂, ∑ h₃, g x * g (x + h₂) * g (x + h₃) * g (x + h₂ + h₃) ≤
      (p : ℝ) * ‖G g ξ₀‖ ^ 2 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  obtain ⟨ξ₀, -, hmax⟩ := Finset.exists_max_image (univ : Finset (ZMod p))
    (fun ξ => ‖G g ξ‖ ^ 2) ⟨0, mem_univ _⟩
  refine ⟨ξ₀, ?_⟩
  rw [U2_eq]
  have h2 : ∑ x, g x * g x ≤ (p : ℝ) := by
    calc ∑ x, g x * g x ≤ ∑ _x : ZMod p, (1 : ℝ) := sum_le_sum fun x _ => by
          have := abs_le.mp (hg x)
          nlinarith
      _ = p := by simp [ZMod.card]
  have h4 : (p : ℝ) * ∑ h, Cr g h ^ 2 ≤ ‖G g ξ₀‖ ^ 2 * ((p : ℝ) * p) := by
    calc (p : ℝ) * ∑ h, Cr g h ^ 2 = ∑ ξ, (‖G g ξ‖ ^ 2) ^ 2 := (sum_M_sq g).symm
      _ ≤ ∑ ξ, ‖G g ξ₀‖ ^ 2 * ‖G g ξ‖ ^ 2 := sum_le_sum fun ξ _ => by
          rw [sq (‖G g ξ‖ ^ 2)]
          exact mul_le_mul_of_nonneg_right (hmax ξ (mem_univ _)) (sq_nonneg _)
      _ = ‖G g ξ₀‖ ^ 2 * ((p : ℝ) * ∑ x, g x * g x) := by rw [← mul_sum, sum_M]
      _ ≤ ‖G g ξ₀‖ ^ 2 * ((p : ℝ) * p) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hp.le) (sq_nonneg _)
  have h5 : (p : ℝ) * ∑ h, Cr g h ^ 2 ≤ (p : ℝ) * ((p : ℝ) * ‖G g ξ₀‖ ^ 2) := by
    calc _ ≤ ‖G g ξ₀‖ ^ 2 * ((p : ℝ) * p) := h4
      _ = _ := by ring
  exact le_of_mul_le_mul_left h5 hp

lemma e_eq (j : ZMod p) :
    (e j : ℂ) = Complex.exp (2 * Real.pi * Complex.I * ((j.val : ℕ) : ℂ) / (p : ℂ)) :=
  ZMod.toCircle_apply j

theorem fourier_extraction (f : ZMod p → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    ∃ ξ : ZMod p → ZMod p,
      ∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
        f x * f (x + h₁) * f (x + h₂) * f (x + h₁ + h₂) *
        f (x + h₃) * f (x + h₁ + h₃) * f (x + h₂ + h₃) * f (x + h₁ + h₂ + h₃) ≤
      (p : ℝ) * ∑ h : ZMod p,
        ‖∑ x : ZMod p, ((f x * f (x + h) : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (((x * ξ h).val : ℕ) : ℂ) / (p : ℂ))‖ ^ 2 := by
  have hb : ∀ h x, |f x * f (x + h)| ≤ 1 := fun h x => by
    rw [abs_mul]
    exact mul_le_one₀ (hf x) (abs_nonneg _) (hf _)
  choose ξ hξ using fun h => exists_large_coeff (fun z => f z * f (z + h)) (hb h)
  refine ⟨ξ, ?_⟩
  have hG : ∀ h, G (fun z => f z * f (z + h)) (ξ h) =
      ∑ x : ZMod p, ((f x * f (x + h) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (((x * ξ h).val : ℕ) : ℂ) / (p : ℂ)) := fun h => by
    unfold G
    refine sum_congr rfl fun x _ => ?_
    rw [e_eq, mul_comm (ξ h) x]
  calc ∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
        f x * f (x + h₁) * f (x + h₂) * f (x + h₁ + h₂) *
        f (x + h₃) * f (x + h₁ + h₃) * f (x + h₂ + h₃) * f (x + h₁ + h₂ + h₃)
      = ∑ h₁ : ZMod p, ∑ x : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
          (f x * f (x + h₁)) * (f (x + h₂) * f (x + h₂ + h₁)) *
          (f (x + h₃) * f (x + h₃ + h₁)) * (f (x + h₂ + h₃) * f (x + h₂ + h₃ + h₁)) := by
        rw [sum_comm]
        refine sum_congr rfl fun h₁ _ => sum_congr rfl fun x _ => sum_congr rfl fun h₂ _ =>
          sum_congr rfl fun h₃ _ => ?_
        have a1 : x + h₂ + h₁ = x + h₁ + h₂ := by ring
        have a2 : x + h₃ + h₁ = x + h₁ + h₃ := by ring
        have a3 : x + h₂ + h₃ + h₁ = x + h₁ + h₂ + h₃ := by ring
        rw [a1, a2, a3]
        ring
    _ ≤ ∑ h₁ : ZMod p, (p : ℝ) * ‖G (fun z => f z * f (z + h₁)) (ξ h₁)‖ ^ 2 :=
        sum_le_sum fun h₁ _ => hξ h₁
    _ = _ := by
        rw [mul_sum]
        exact sum_congr rfl fun h _ => by rw [hG]

end U2F

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R2.H1 :=
  fun _ _ f hf => U2F.fourier_extraction f hf
