import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R1
import Mathlib

/-!
# The U^3 generalized von Neumann inequality on a finite field

Step H2 of reduction R1.H2.R1.H1.R1.H1.R1 of Erdős 142 (reduction by @yhay81). For pairwise
distinct c₀, c₁, c₂, c₃ in ZMod p and real functions f₀, f₁, f₂ bounded by 1,

  (∑ x d, f₀ (x + c₀ d) f₁ (x + c₁ d) f₂ (x + c₂ d) f₃ (x + c₃ d)) ^ 8 ≤ p ^ 12 * ‖f₃‖_{U^3}^8,

where the last factor is the unnormalised sum over three-dimensional cubes. This is a
classical inequality (Gowers); the proof is three applications of Cauchy–Schwarz.

One step (`cs_step`): if |g| ≤ 1 then (∑ y d, g y Φ y d)^2 ≤ |F| ∑ y d h, Φ y d Φ y (d + h).
After the substitution y = x + c d that turns one function into g y, each step removes a
function and replaces every other f by its multiplicative derivative D t f x = f x f (x + t).
`lemA` handles two functions, `lemB` three, `gvn` four; the exponents of |F| are 2, 5, 12.
The statements are over an arbitrary finite field and are specialised to ZMod p at the end.
-/

namespace OMAGvN

open Finset

variable {F : Type*} [Field F] [Fintype F]

/-- Multiplicative derivative. -/
def D (t : F) (f : F → ℝ) : F → ℝ := fun x => f x * f (x + t)

lemma D_abs {f : F → ℝ} (hf : ∀ x, |f x| ≤ 1) (t : F) : ∀ x, |D t f x| ≤ 1 := by
  intro x
  unfold D
  rw [abs_mul]
  exact mul_le_one₀ (hf x) (abs_nonneg _) (hf _)

lemma cs_step (g : F → ℝ) (hg : ∀ x, |g x| ≤ 1) (Φ : F → F → ℝ) :
    (∑ y, ∑ d, g y * Φ y d) ^ 2
      ≤ (Fintype.card F : ℝ) * ∑ y, ∑ d, ∑ h, Φ y d * Φ y (d + h) := by
  have h1 : ∑ y, ∑ d, g y * Φ y d = ∑ y, g y * ∑ d, Φ y d := by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
  have h2 : ∀ y, (∑ d, Φ y d) ^ 2 = ∑ d, ∑ h, Φ y d * Φ y (d + h) := by
    intro y
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    exact (Fintype.sum_equiv (Equiv.addLeft d) (fun h => Φ y d * Φ y (d + h))
      (fun d' => Φ y d * Φ y d') (fun h => rfl)).symm
  have h3 : ∑ y, g y ^ 2 ≤ (Fintype.card F : ℝ) := by
    calc ∑ y, g y ^ 2 ≤ ∑ _y : F, (1 : ℝ) := Finset.sum_le_sum fun y _ => by
          have h := abs_le.mp (hg y)
          nlinarith [h.1, h.2]
      _ = Fintype.card F := by simp
  have h4 : 0 ≤ ∑ y, (∑ d, Φ y d) ^ 2 := Finset.sum_nonneg fun y _ => sq_nonneg _
  calc (∑ y, ∑ d, g y * Φ y d) ^ 2 = (∑ y, g y * ∑ d, Φ y d) ^ 2 := by rw [h1]
    _ ≤ (∑ y, g y ^ 2) * ∑ y, (∑ d, Φ y d) ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (Fintype.card F : ℝ) * ∑ y, (∑ d, Φ y d) ^ 2 := mul_le_mul_of_nonneg_right h3 h4
    _ = _ := by
      congr 1
      exact Finset.sum_congr rfl fun y _ => h2 y

lemma shift (c : F) (Ψ : F → F → ℝ) : ∑ x, ∑ d, Ψ (x + c * d) d = ∑ y, ∑ d, Ψ y d := by
  calc ∑ x, ∑ d, Ψ (x + c * d) d = ∑ d, ∑ x, Ψ (x + c * d) d := Finset.sum_comm
    _ = ∑ d, ∑ y, Ψ y d := Finset.sum_congr rfl fun d _ =>
        Fintype.sum_equiv (Equiv.addRight (c * d)) (fun x => Ψ (x + c * d) d)
          (fun y => Ψ y d) (fun x => rfl)
    _ = ∑ y, ∑ d, Ψ y d := Finset.sum_comm

lemma sum3 (T : F → F → F → ℝ) :
    ∑ y, ∑ d, ∑ h, T y d h = ∑ h, ∑ y, ∑ d, T y d h := by
  calc ∑ y, ∑ d, ∑ h, T y d h = ∑ y, ∑ h, ∑ d, T y d h :=
        Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma sq_sum_le (Y : F → ℝ) : (∑ h, Y h) ^ 2 ≤ (Fintype.card F : ℝ) * ∑ h, Y h ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset F)) (f := Y)
  simpa using h

lemma lemA (u2 u3 : F → ℝ) (hu : ∀ x, |u2 x| ≤ 1) (b2 b3 : F) (hb : b2 ≠ b3) :
    (∑ y, ∑ d, u2 (y + b2 * d) * u3 (y + b3 * d)) ^ 2
      ≤ (Fintype.card F : ℝ) ^ 2 * ∑ l, ∑ z, D l u3 z := by
  have he : b3 - b2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have h1 : ∑ y, ∑ d, u2 (y + b2 * d) * u3 (y + b3 * d)
      = ∑ y, ∑ d, u2 y * u3 (y + (b3 - b2) * d) := by
    rw [← shift b2 (fun y d => u2 y * u3 (y + (b3 - b2) * d))]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => ?_
    have e : x + b2 * d + (b3 - b2) * d = x + b3 * d := by ring
    simp only [e]
  have h2 : ∑ y, ∑ d, ∑ h, u3 (y + (b3 - b2) * d) * u3 (y + (b3 - b2) * (d + h))
      = (Fintype.card F : ℝ) * ∑ l, ∑ z, D l u3 z := by
    have hs := shift (b3 - b2) (fun z _d => ∑ h, u3 z * u3 (z + (b3 - b2) * h))
    calc ∑ y, ∑ d, ∑ h, u3 (y + (b3 - b2) * d) * u3 (y + (b3 - b2) * (d + h))
        = ∑ x, ∑ d, ∑ h, u3 (x + (b3 - b2) * d)
            * u3 (x + (b3 - b2) * d + (b3 - b2) * h) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ =>
            Finset.sum_congr rfl fun h _ => ?_
          have e : x + (b3 - b2) * (d + h) = x + (b3 - b2) * d + (b3 - b2) * h := by ring
          rw [e]
      _ = ∑ z, ∑ _d : F, ∑ h, u3 z * u3 (z + (b3 - b2) * h) := hs
      _ = ∑ z, (Fintype.card F : ℝ) * ∑ h, u3 z * u3 (z + (b3 - b2) * h) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (Fintype.card F : ℝ) * ∑ z, ∑ l, u3 z * u3 (z + l) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          congr 1
          exact Fintype.sum_equiv (Equiv.mulLeft₀ (b3 - b2) he)
            (fun h => u3 z * u3 (z + (b3 - b2) * h)) (fun l => u3 z * u3 (z + l))
            (fun h => rfl)
      _ = (Fintype.card F : ℝ) * ∑ l, ∑ z, D l u3 z := by
          congr 1
          exact Finset.sum_comm
  rw [h1]
  refine (cs_step u2 hu (fun y d => u3 (y + (b3 - b2) * d))).trans ?_
  rw [h2]
  exact le_of_eq (by ring)

lemma lemB (g1 g2 g3 : F → ℝ) (h1 : ∀ x, |g1 x| ≤ 1) (h2 : ∀ x, |g2 x| ≤ 1)
    (a1 a2 a3 : F) (h13 : a1 ≠ a3) (h23 : a2 ≠ a3) :
    (∑ y, ∑ d, g1 (y + a1 * d) * g2 (y + a2 * d) * g3 (y + a3 * d)) ^ 4
      ≤ (Fintype.card F : ℝ) ^ 5 * ∑ k, ∑ l, ∑ z, D l (D k g3) z := by
  have hN : (0 : ℝ) ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
  have hb3 : a3 - a1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h13)
  have hb : a2 - a1 ≠ a3 - a1 := fun h => h23 (sub_left_injective h)
  have e1 : ∑ y, ∑ d, g1 (y + a1 * d) * g2 (y + a2 * d) * g3 (y + a3 * d)
      = ∑ y, ∑ d, g1 y * (g2 (y + (a2 - a1) * d) * g3 (y + (a3 - a1) * d)) := by
    rw [← shift a1 (fun y d => g1 y * (g2 (y + (a2 - a1) * d) * g3 (y + (a3 - a1) * d)))]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => ?_
    have e2 : x + a1 * d + (a2 - a1) * d = x + a2 * d := by ring
    have e3 : x + a1 * d + (a3 - a1) * d = x + a3 * d := by ring
    simp only [e2, e3]
    ring
  have s1 : (∑ y, ∑ d, g1 (y + a1 * d) * g2 (y + a2 * d) * g3 (y + a3 * d)) ^ 2
      ≤ (Fintype.card F : ℝ) * ∑ h, ∑ y, ∑ d,
          D ((a2 - a1) * h) g2 (y + (a2 - a1) * d)
            * D ((a3 - a1) * h) g3 (y + (a3 - a1) * d) := by
    rw [e1]
    refine (cs_step g1 h1 (fun y d => g2 (y + (a2 - a1) * d) * g3 (y + (a3 - a1) * d))).trans
      (le_of_eq ?_)
    congr 1
    rw [sum3]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [D, mul_add, ← add_assoc]
    ring
  have s2 : ∀ h, (∑ y, ∑ d, D ((a2 - a1) * h) g2 (y + (a2 - a1) * d)
            * D ((a3 - a1) * h) g3 (y + (a3 - a1) * d)) ^ 2
      ≤ (Fintype.card F : ℝ) ^ 2 * ∑ l, ∑ z, D l (D ((a3 - a1) * h) g3) z := fun h =>
    lemA (D ((a2 - a1) * h) g2) (D ((a3 - a1) * h) g3) (D_abs h2 _) _ _ hb
  have s4 : ∑ h, (∑ y, ∑ d, D ((a2 - a1) * h) g2 (y + (a2 - a1) * d)
            * D ((a3 - a1) * h) g3 (y + (a3 - a1) * d)) ^ 2
      ≤ (Fintype.card F : ℝ) ^ 2 * ∑ k, ∑ l, ∑ z, D l (D k g3) z := by
    calc _ ≤ ∑ h, (Fintype.card F : ℝ) ^ 2 * ∑ l, ∑ z, D l (D ((a3 - a1) * h) g3) z :=
          Finset.sum_le_sum fun h _ => s2 h
      _ = (Fintype.card F : ℝ) ^ 2 * ∑ h, ∑ l, ∑ z, D l (D ((a3 - a1) * h) g3) z := by
          rw [Finset.mul_sum]
      _ = _ := by
          congr 1
          exact Fintype.sum_equiv (Equiv.mulLeft₀ (a3 - a1) hb3)
            (fun h => ∑ l, ∑ z, D l (D ((a3 - a1) * h) g3) z)
            (fun k => ∑ l, ∑ z, D l (D k g3) z) (fun h => rfl)
  have s3 := sq_sum_le (fun h => ∑ y, ∑ d, D ((a2 - a1) * h) g2 (y + (a2 - a1) * d)
            * D ((a3 - a1) * h) g3 (y + (a3 - a1) * d))
  calc (∑ y, ∑ d, g1 (y + a1 * d) * g2 (y + a2 * d) * g3 (y + a3 * d)) ^ 4
      = ((∑ y, ∑ d, g1 (y + a1 * d) * g2 (y + a2 * d) * g3 (y + a3 * d)) ^ 2) ^ 2 := by ring
    _ ≤ ((Fintype.card F : ℝ) * ∑ h, ∑ y, ∑ d,
          D ((a2 - a1) * h) g2 (y + (a2 - a1) * d)
            * D ((a3 - a1) * h) g3 (y + (a3 - a1) * d)) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) s1 2
    _ = (Fintype.card F : ℝ) ^ 2 * (∑ h, ∑ y, ∑ d,
          D ((a2 - a1) * h) g2 (y + (a2 - a1) * d)
            * D ((a3 - a1) * h) g3 (y + (a3 - a1) * d)) ^ 2 := by ring
    _ ≤ (Fintype.card F : ℝ) ^ 2 * ((Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ) ^ 2 * ∑ k, ∑ l, ∑ z, D l (D k g3) z)) :=
        mul_le_mul_of_nonneg_left (s3.trans (mul_le_mul_of_nonneg_left s4 hN)) (sq_nonneg _)
    _ = _ := by ring

theorem gvn (c0 c1 c2 c3 : F) (h03 : c0 ≠ c3) (h13 : c1 ≠ c3) (h23 : c2 ≠ c3)
    (f0 f1 f2 f3 : F → ℝ) (hf0 : ∀ x, |f0 x| ≤ 1) (hf1 : ∀ x, |f1 x| ≤ 1)
    (hf2 : ∀ x, |f2 x| ≤ 1) :
    (∑ x, ∑ d, f0 (x + c0 * d) * f1 (x + c1 * d) * f2 (x + c2 * d) * f3 (x + c3 * d)) ^ 8
      ≤ (Fintype.card F : ℝ) ^ 12 * ∑ h, ∑ k, ∑ l, ∑ z, D l (D k (D h f3)) z := by
  have hN : (0 : ℝ) ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
  have ha3 : c3 - c0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h03)
  have h13' : c1 - c0 ≠ c3 - c0 := fun h => h13 (sub_left_injective h)
  have h23' : c2 - c0 ≠ c3 - c0 := fun h => h23 (sub_left_injective h)
  have e1 : ∑ x, ∑ d, f0 (x + c0 * d) * f1 (x + c1 * d) * f2 (x + c2 * d) * f3 (x + c3 * d)
      = ∑ y, ∑ d, f0 y * (f1 (y + (c1 - c0) * d) * f2 (y + (c2 - c0) * d)
          * f3 (y + (c3 - c0) * d)) := by
    rw [← shift c0 (fun y d => f0 y * (f1 (y + (c1 - c0) * d) * f2 (y + (c2 - c0) * d)
          * f3 (y + (c3 - c0) * d)))]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => ?_
    have e2 : x + c0 * d + (c1 - c0) * d = x + c1 * d := by ring
    have e3 : x + c0 * d + (c2 - c0) * d = x + c2 * d := by ring
    have e4 : x + c0 * d + (c3 - c0) * d = x + c3 * d := by ring
    simp only [e2, e3, e4]
    ring
  have s1 : (∑ x, ∑ d, f0 (x + c0 * d) * f1 (x + c1 * d) * f2 (x + c2 * d)
        * f3 (x + c3 * d)) ^ 2
      ≤ (Fintype.card F : ℝ) * ∑ h, ∑ y, ∑ d,
          D ((c1 - c0) * h) f1 (y + (c1 - c0) * d) * D ((c2 - c0) * h) f2 (y + (c2 - c0) * d)
            * D ((c3 - c0) * h) f3 (y + (c3 - c0) * d) := by
    rw [e1]
    refine (cs_step f0 hf0 (fun y d => f1 (y + (c1 - c0) * d) * f2 (y + (c2 - c0) * d)
          * f3 (y + (c3 - c0) * d))).trans (le_of_eq ?_)
    congr 1
    rw [sum3]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [D, mul_add, ← add_assoc]
    ring
  have s2 : ∀ h, (∑ y, ∑ d,
          D ((c1 - c0) * h) f1 (y + (c1 - c0) * d) * D ((c2 - c0) * h) f2 (y + (c2 - c0) * d)
            * D ((c3 - c0) * h) f3 (y + (c3 - c0) * d)) ^ 4
      ≤ (Fintype.card F : ℝ) ^ 5 * ∑ k, ∑ l, ∑ z, D l (D k (D ((c3 - c0) * h) f3)) z :=
    fun h => lemB _ _ _ (D_abs hf1 _) (D_abs hf2 _) _ _ _ h13' h23'
  have s4 : ∑ h, (∑ y, ∑ d,
          D ((c1 - c0) * h) f1 (y + (c1 - c0) * d) * D ((c2 - c0) * h) f2 (y + (c2 - c0) * d)
            * D ((c3 - c0) * h) f3 (y + (c3 - c0) * d)) ^ 4
      ≤ (Fintype.card F : ℝ) ^ 5 * ∑ h, ∑ k, ∑ l, ∑ z, D l (D k (D h f3)) z := by
    calc _ ≤ ∑ h, (Fintype.card F : ℝ) ^ 5
            * ∑ k, ∑ l, ∑ z, D l (D k (D ((c3 - c0) * h) f3)) z :=
          Finset.sum_le_sum fun h _ => s2 h
      _ = (Fintype.card F : ℝ) ^ 5
            * ∑ h, ∑ k, ∑ l, ∑ z, D l (D k (D ((c3 - c0) * h) f3)) z := by
          rw [Finset.mul_sum]
      _ = _ := by
          congr 1
          exact Fintype.sum_equiv (Equiv.mulLeft₀ (c3 - c0) ha3)
            (fun h => ∑ k, ∑ l, ∑ z, D l (D k (D ((c3 - c0) * h) f3)) z)
            (fun h => ∑ k, ∑ l, ∑ z, D l (D k (D h f3)) z) (fun h => rfl)
  -- power mean: (∑ Y)^4 ≤ |F|^3 ∑ Y^4
  have pm : ∀ Y : F → ℝ, (∑ h, Y h) ^ 4 ≤ (Fintype.card F : ℝ) ^ 3 * ∑ h, Y h ^ 4 := by
    intro Y
    have p1 := sq_sum_le Y
    have p2 := sq_sum_le (fun h => Y h ^ 2)
    have p3 : 0 ≤ ∑ h, Y h ^ 2 := Finset.sum_nonneg fun h _ => sq_nonneg _
    calc (∑ h, Y h) ^ 4 = ((∑ h, Y h) ^ 2) ^ 2 := by ring
      _ ≤ ((Fintype.card F : ℝ) * ∑ h, Y h ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) p1 2
      _ = (Fintype.card F : ℝ) ^ 2 * (∑ h, Y h ^ 2) ^ 2 := by ring
      _ ≤ (Fintype.card F : ℝ) ^ 2 * ((Fintype.card F : ℝ) * ∑ h, (Y h ^ 2) ^ 2) :=
          mul_le_mul_of_nonneg_left p2 (sq_nonneg _)
      _ = (Fintype.card F : ℝ) ^ 3 * ∑ h, Y h ^ 4 := by
          have e : ∀ h, (Y h ^ 2) ^ 2 = Y h ^ 4 := fun h => by ring
          simp only [e]
          ring
  have s3 := pm (fun h => ∑ y, ∑ d,
          D ((c1 - c0) * h) f1 (y + (c1 - c0) * d) * D ((c2 - c0) * h) f2 (y + (c2 - c0) * d)
            * D ((c3 - c0) * h) f3 (y + (c3 - c0) * d))
  calc (∑ x, ∑ d, f0 (x + c0 * d) * f1 (x + c1 * d) * f2 (x + c2 * d) * f3 (x + c3 * d)) ^ 8
      = ((∑ x, ∑ d, f0 (x + c0 * d) * f1 (x + c1 * d) * f2 (x + c2 * d)
          * f3 (x + c3 * d)) ^ 2) ^ 4 := by ring
    _ ≤ ((Fintype.card F : ℝ) * ∑ h, ∑ y, ∑ d,
          D ((c1 - c0) * h) f1 (y + (c1 - c0) * d) * D ((c2 - c0) * h) f2 (y + (c2 - c0) * d)
            * D ((c3 - c0) * h) f3 (y + (c3 - c0) * d)) ^ 4 :=
        pow_le_pow_left₀ (sq_nonneg _) s1 4
    _ = (Fintype.card F : ℝ) ^ 4 * (∑ h, ∑ y, ∑ d,
          D ((c1 - c0) * h) f1 (y + (c1 - c0) * d) * D ((c2 - c0) * h) f2 (y + (c2 - c0) * d)
            * D ((c3 - c0) * h) f3 (y + (c3 - c0) * d)) ^ 4 := by ring
    _ ≤ (Fintype.card F : ℝ) ^ 4 * ((Fintype.card F : ℝ) ^ 3
          * ((Fintype.card F : ℝ) ^ 5 * ∑ h, ∑ k, ∑ l, ∑ z, D l (D k (D h f3)) z)) :=
        mul_le_mul_of_nonneg_left
          (s3.trans (mul_le_mul_of_nonneg_left s4 (pow_nonneg hN 3))) (pow_nonneg hN 4)
    _ = _ := by ring

lemma cube_sum (f : F → ℝ) :
    ∑ h, ∑ k, ∑ l, ∑ z, D l (D k (D h f)) z
      = ∑ x, ∑ h₁, ∑ h₂, ∑ h₃, f x * f (x + h₁) * f (x + h₂) * f (x + h₁ + h₂) *
          f (x + h₃) * f (x + h₁ + h₃) * f (x + h₂ + h₃) * f (x + h₁ + h₂ + h₃) := by
  calc ∑ h, ∑ k, ∑ l, ∑ z, D l (D k (D h f)) z
      = ∑ h, ∑ k, ∑ z, ∑ l, D l (D k (D h f)) z :=
        Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ h, ∑ z, ∑ k, ∑ l, D l (D k (D h f)) z :=
        Finset.sum_congr rfl fun h _ => Finset.sum_comm
    _ = ∑ z, ∑ h, ∑ k, ∑ l, D l (D k (D h f)) z := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun h _ =>
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        have e4 : z + l + k + h = z + h + k + l := by ring
        have e1 : z + k + h = z + h + k := by ring
        have e2 : z + l + h = z + h + l := by ring
        have e3 : z + l + k = z + k + l := by ring
        simp only [D]
        rw [e4, e1, e2, e3]
        ring

end OMAGvN

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R1.H2 := by
  intro p _ c₀ c₁ c₂ c₃ _ _ h03 _ h13 h23 f₀ f₁ f₂ f₃ hf0 hf1 hf2
  have h := OMAGvN.gvn c₀ c₁ c₂ c₃ h03 h13 h23 f₀ f₁ f₂ f₃ hf0 hf1 hf2
  rw [ZMod.card, OMAGvN.cube_sum] at h
  exact h
