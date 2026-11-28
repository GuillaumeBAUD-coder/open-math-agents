import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R1
import Mathlib

/-!
# Step H2 of the reduction Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1.R1

The Gowers U^3 generalized von Neumann inequality on a finite field: the 4-term linear form
with distinct coefficients is controlled by the U^3 cube sum of its last function.

Proof: three applications of the Cauchy-Schwarz (van der Corput) step
  (sum_{x,d} g(x + a d) K(x,d))^2 <= |F| sum_h sum_{x,d} K(x,d) K(x - a h, d + h),
valid for |g| <= 1. Each application removes one bounded function and replaces the remaining
ones by multiplicative derivatives D_t f (z) = f z * f (z + t). After three steps only f3 is
left, differentiated three times; rescaling the three shifts (the coefficient of f3 differs
from the other three) gives the cube sum. Only f0, f1, f2 need to be bounded.
-/

namespace U3GvN

open Finset

variable {F : Type*} [Field F] [Fintype F]

/-- Multiplicative derivative. -/
def D (t : F) (f : F → ℝ) : F → ℝ := fun z => f z * f (z + t)

lemma D_bound {f : F → ℝ} (hf : ∀ x, |f x| ≤ 1) (t z : F) : |D t f z| ≤ 1 := by
  unfold D
  rw [abs_mul]
  exact mul_le_one₀ (hf z) (abs_nonneg _) (hf _)

lemma shift_mul (a c : F) (g : F → ℝ) (x d h : F) :
    g (x + c * d) * g (x - a * h + c * (d + h)) = D ((c - a) * h) g (x + c * d) := by
  have e : x - a * h + c * (d + h) = x + c * d + (c - a) * h := by ring
  rw [e]
  rfl

lemma sum_scale (c : F) (hc : c ≠ 0) (G : F → ℝ) : ∑ h, G (c * h) = ∑ h, G h :=
  Fintype.sum_equiv (Equiv.mulLeft₀ c hc) _ _ fun _ => rfl

lemma sq_sum_eq (a : F) (K : F → F → ℝ) :
    ∑ y, (∑ d, K (y - a * d) d) ^ 2 = ∑ h, ∑ x, ∑ d, K x d * K (x - a * h) (d + h) := by
  calc ∑ y, (∑ d, K (y - a * d) d) ^ 2
      = ∑ y, ∑ d, ∑ h, K (y - a * d) d * K (y - a * (d + h)) (d + h) := by
        refine sum_congr rfl fun y _ => ?_
        rw [sq, sum_mul_sum]
        refine sum_congr rfl fun d _ => ?_
        exact (Fintype.sum_equiv (Equiv.addLeft d) _ _ fun h => rfl).symm
    _ = ∑ h, ∑ d, ∑ y, K (y - a * d) d * K (y - a * (d + h)) (d + h) := by
        rw [sum_comm]
        refine (sum_congr rfl fun d _ => sum_comm).trans ?_
        exact sum_comm
    _ = ∑ h, ∑ d, ∑ x, K x d * K (x - a * h) (d + h) := by
        refine sum_congr rfl fun h _ => sum_congr rfl fun d _ => ?_
        refine Fintype.sum_equiv (Equiv.subRight (a * d)) _ _ fun y => ?_
        have e : y - a * (d + h) = y - a * d - a * h := by ring
        rw [e]
        rfl
    _ = _ := sum_congr rfl fun h _ => sum_comm

lemma step (g : F → ℝ) (hg : ∀ x, |g x| ≤ 1) (a : F) (K : F → F → ℝ) :
    (∑ x, ∑ d, g (x + a * d) * K x d) ^ 2 ≤
      (Fintype.card F : ℝ) * ∑ h, ∑ x, ∑ d, K x d * K (x - a * h) (d + h) := by
  have e1 : ∑ x, ∑ d, g (x + a * d) * K x d = ∑ y, g y * ∑ d, K (y - a * d) d := by
    calc ∑ x, ∑ d, g (x + a * d) * K x d
        = ∑ d, ∑ x, g (x + a * d) * K x d := sum_comm
      _ = ∑ d, ∑ y, g y * K (y - a * d) d := sum_congr rfl fun d _ =>
            Fintype.sum_equiv (Equiv.addRight (a * d)) _ _ fun x => by simp
      _ = ∑ y, ∑ d, g y * K (y - a * d) d := sum_comm
      _ = ∑ y, g y * ∑ d, K (y - a * d) d := by simp_rw [mul_sum]
  rw [e1, ← sq_sum_eq]
  calc (∑ y, g y * ∑ d, K (y - a * d) d) ^ 2
      ≤ (∑ y, g y ^ 2) * ∑ y, (∑ d, K (y - a * d) d) ^ 2 := sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (Fintype.card F : ℝ) * ∑ y, (∑ d, K (y - a * d) d) ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun _ _ => sq_nonneg _)
        calc ∑ y, g y ^ 2 ≤ ∑ _y : F, (1 : ℝ) := sum_le_sum fun y _ => by
              have := abs_le.mp (hg y)
              nlinarith
          _ = Fintype.card F := by simp

theorem gvn (c0 c1 c2 c3 : F) (h03 : c3 ≠ c0) (h13 : c3 ≠ c1) (h23 : c3 ≠ c2)
    (f0 f1 f2 f3 : F → ℝ) (b0 : ∀ x, |f0 x| ≤ 1) (b1 : ∀ x, |f1 x| ≤ 1)
    (b2 : ∀ x, |f2 x| ≤ 1) :
    (∑ x, ∑ d, f0 (x + c0 * d) * f1 (x + c1 * d) * f2 (x + c2 * d) * f3 (x + c3 * d)) ^ 8 ≤
      (Fintype.card F : ℝ) ^ 12 * ∑ x, ∑ h1, ∑ h2, ∑ h3,
        f3 x * f3 (x + h1) * f3 (x + h2) * f3 (x + h1 + h2) *
        f3 (x + h3) * f3 (x + h1 + h3) * f3 (x + h2 + h3) * f3 (x + h1 + h2 + h3) := by
  set n : ℝ := (Fintype.card F : ℝ) with hn
  have n0 : 0 ≤ n := Nat.cast_nonneg _
  have cs : ∀ u : F → ℝ, (∑ h, u h) ^ 2 ≤ n * ∑ h, u h ^ 2 := fun u => by
    simpa [hn] using sq_sum_le_card_mul_sum_sq (s := (univ : Finset F)) (f := u)
  set L : ℝ := ∑ x, ∑ d, f0 (x + c0 * d) * f1 (x + c1 * d) * f2 (x + c2 * d) * f3 (x + c3 * d)
    with hL
  let T1 : F → ℝ := fun h => ∑ x, ∑ d, D ((c1 - c0) * h) f1 (x + c1 * d) *
    (D ((c2 - c0) * h) f2 (x + c2 * d) * D ((c3 - c0) * h) f3 (x + c3 * d))
  let T2 : F → F → ℝ := fun h h' => ∑ x, ∑ d,
    D ((c2 - c1) * h') (D ((c2 - c0) * h) f2) (x + c2 * d) *
      D ((c3 - c1) * h') (D ((c3 - c0) * h) f3) (x + c3 * d)
  let T3 : F → F → F → ℝ := fun h h' h'' => ∑ x,
    D ((c3 - c2) * h'') (D ((c3 - c1) * h') (D ((c3 - c0) * h) f3)) x
  have s1 : L ^ 2 ≤ n * ∑ h, T1 h := by
    have key := step f0 b0 c0 (fun x d => f1 (x + c1 * d) * f2 (x + c2 * d) * f3 (x + c3 * d))
    have eL : L = ∑ x, ∑ d, f0 (x + c0 * d) *
        (f1 (x + c1 * d) * f2 (x + c2 * d) * f3 (x + c3 * d)) := by
      simp only [hL, mul_assoc]
    rw [eL]
    refine key.trans_eq ?_
    congr 1
    refine sum_congr rfl fun h _ => sum_congr rfl fun x _ => sum_congr rfl fun d _ => ?_
    rw [← shift_mul c0 c1 f1, ← shift_mul c0 c2 f2, ← shift_mul c0 c3 f3]
    ring
  have s2 : ∀ h, T1 h ^ 2 ≤ n * ∑ h', T2 h h' := fun h => by
    have key := step (D ((c1 - c0) * h) f1) (D_bound b1 _) c1
      (fun x d => D ((c2 - c0) * h) f2 (x + c2 * d) * D ((c3 - c0) * h) f3 (x + c3 * d))
    refine key.trans_eq ?_
    congr 1
    refine sum_congr rfl fun h' _ => sum_congr rfl fun x _ => sum_congr rfl fun d _ => ?_
    rw [← shift_mul c1 c2 (D ((c2 - c0) * h) f2), ← shift_mul c1 c3 (D ((c3 - c0) * h) f3)]
    ring
  have s3 : ∀ h h', T2 h h' ^ 2 ≤ n ^ 2 * ∑ h'', T3 h h' h'' := fun h h' => by
    have key := step (D ((c2 - c1) * h') (D ((c2 - c0) * h) f2)) (D_bound (D_bound b2 _) _) c2
      (fun x d => D ((c3 - c1) * h') (D ((c3 - c0) * h) f3) (x + c3 * d))
    refine key.trans_eq ?_
    have e : n ^ 2 * ∑ h'', T3 h h' h'' = n * ∑ h'', n * T3 h h' h'' := by
      rw [← mul_sum]; ring
    rw [e]
    congr 1
    refine sum_congr rfl fun h'' _ => ?_
    calc ∑ x, ∑ d, D ((c3 - c1) * h') (D ((c3 - c0) * h) f3) (x + c3 * d) *
          D ((c3 - c1) * h') (D ((c3 - c0) * h) f3) (x - c2 * h'' + c3 * (d + h''))
        = ∑ d, ∑ x, D ((c3 - c2) * h'') (D ((c3 - c1) * h') (D ((c3 - c0) * h) f3))
            (x + c3 * d) := by
          rw [sum_comm]
          exact sum_congr rfl fun d _ => sum_congr rfl fun x _ => shift_mul c2 c3 _ x d h''
      _ = ∑ _d : F, T3 h h' h'' := sum_congr rfl fun d _ =>
          Fintype.sum_equiv (Equiv.addRight (c3 * d)) _ _ fun x => rfl
      _ = n * T3 h h' h'' := by simp [hn]
  have e3 : ∑ h, ∑ h', ∑ h'', T3 h h' h'' = ∑ x, ∑ h1, ∑ h2, ∑ h3,
        f3 x * f3 (x + h1) * f3 (x + h2) * f3 (x + h1 + h2) *
        f3 (x + h3) * f3 (x + h1 + h3) * f3 (x + h2 + h3) * f3 (x + h1 + h2 + h3) := by
    calc ∑ h, ∑ h', ∑ h'', T3 h h' h''
        = ∑ h1, ∑ h2, ∑ h3, ∑ x, D h3 (D h2 (D h1 f3)) x := by
          rw [← sum_scale (c3 - c0) (sub_ne_zero.mpr h03)
            (fun h1 => ∑ h2, ∑ h3, ∑ x, D h3 (D h2 (D h1 f3)) x)]
          refine sum_congr rfl fun h _ => ?_
          rw [← sum_scale (c3 - c1) (sub_ne_zero.mpr h13)
            (fun h2 => ∑ h3, ∑ x, D h3 (D h2 (D ((c3 - c0) * h) f3)) x)]
          refine sum_congr rfl fun h' _ => ?_
          exact sum_scale (c3 - c2) (sub_ne_zero.mpr h23)
            (fun h3 => ∑ x, D h3 (D ((c3 - c1) * h') (D ((c3 - c0) * h) f3)) x)
      _ = ∑ h1, ∑ h2, ∑ x, ∑ h3, D h3 (D h2 (D h1 f3)) x :=
          sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_comm
      _ = ∑ h1, ∑ x, ∑ h2, ∑ h3, D h3 (D h2 (D h1 f3)) x :=
          sum_congr rfl fun _ _ => sum_comm
      _ = ∑ x, ∑ h1, ∑ h2, ∑ h3, D h3 (D h2 (D h1 f3)) x := sum_comm
      _ = _ := by
          refine sum_congr rfl fun x _ => sum_congr rfl fun h1 _ => sum_congr rfl fun h2 _ =>
            sum_congr rfl fun h3 _ => ?_
          have a1 : x + h2 + h1 = x + h1 + h2 := by ring
          have a2 : x + h3 + h1 = x + h1 + h3 := by ring
          have a3 : x + h3 + h2 = x + h2 + h3 := by ring
          simp only [D, a1, a2, a3]
          ring_nf
  rw [← e3]
  have q4 : L ^ 4 ≤ n ^ 4 * ∑ h, ∑ h', T2 h h' := by
    calc L ^ 4 = (L ^ 2) ^ 2 := by ring
      _ ≤ (n * ∑ h, T1 h) ^ 2 := pow_le_pow_left₀ (sq_nonneg L) s1 2
      _ = n ^ 2 * (∑ h, T1 h) ^ 2 := by ring
      _ ≤ n ^ 2 * (n * ∑ h, T1 h ^ 2) := mul_le_mul_of_nonneg_left (cs _) (sq_nonneg n)
      _ ≤ n ^ 2 * (n * ∑ h, n * ∑ h', T2 h h') := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ n0) (sq_nonneg n)
          exact sum_le_sum fun h _ => s2 h
      _ = n ^ 4 * ∑ h, ∑ h', T2 h h' := by rw [← mul_sum]; ring
  calc L ^ 8 = (L ^ 4) ^ 2 := by ring
    _ ≤ (n ^ 4 * ∑ h, ∑ h', T2 h h') ^ 2 := pow_le_pow_left₀ (by positivity) q4 2
    _ = n ^ 8 * (∑ h, ∑ h', T2 h h') ^ 2 := by ring
    _ ≤ n ^ 8 * (n * ∑ h, (∑ h', T2 h h') ^ 2) :=
        mul_le_mul_of_nonneg_left (cs _) (by positivity)
    _ ≤ n ^ 8 * (n * ∑ h, n * ∑ h', T2 h h' ^ 2) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ n0) (by positivity)
        exact sum_le_sum fun h _ => cs _
    _ ≤ n ^ 8 * (n * ∑ h, n * ∑ h', n ^ 2 * ∑ h'', T3 h h' h'') := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ n0) (by positivity)
        refine sum_le_sum fun h _ => mul_le_mul_of_nonneg_left ?_ n0
        exact sum_le_sum fun h' _ => s3 h h'
    _ = n ^ 12 * ∑ h, ∑ h', ∑ h'', T3 h h' h'' := by
        simp only [← mul_sum]
        ring

end U3GvN

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R1.H2 := by
  intro p _ c0 c1 c2 c3 _ _ h03 _ h13 h23 f0 f1 f2 f3 b0 b1 b2
  have := U3GvN.gvn c0 c1 c2 c3 h03.symm h13.symm h23.symm f0 f1 f2 f3 b0 b1 b2
  rwa [ZMod.card] at this
