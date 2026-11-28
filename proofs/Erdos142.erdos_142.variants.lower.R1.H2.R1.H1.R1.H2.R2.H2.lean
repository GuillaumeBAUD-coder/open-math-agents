import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H2_R2
import Mathlib

/-!
# Step H2 of the reduction Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H2.R2

The Gowers U^s generalized von Neumann inequality on a finite field, for every s: the
(s+1)-term linear form sum_(x,d) prod_i f_i (x + c_i d) is controlled by the U^s cube sum of
the last function, provided the first s functions are bounded by 1 and the last coefficient
differs from the others.

Proof by induction on the number of functions. One van der Corput (Cauchy-Schwarz) step
  (sum_(x,d) g(x + a d) K(x,d))^2 <= |F| sum_h sum_(x,d) K(x,d) K(x - a h, d + h)
removes the first function and replaces every other f_i by the multiplicative derivative
D_((c_i - c_0) h) f_i, where D_t f (z) = f z * f (z + t). The induction hypothesis is applied
for each h, the sum over h is handled by the power mean inequality
  (sum_h u_h)^(2^t) <= |F|^(2^t - 1) sum_h u_h^(2^t)
(iterated Cauchy-Schwarz, no sign condition), and rescaling h turns the derivative of the cube
sum into the cube sum with one more direction. The exponents add up to 2^(s+1) - s - 1.
-/

namespace UsGvN

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

/-- One van der Corput step. -/
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

/-- Power mean inequality for powers of two (no sign condition needed). -/
lemma pow_sum_le (t : ℕ) (u : F → ℝ) :
    (∑ h, u h) ^ (2 ^ t) ≤ (Fintype.card F : ℝ) ^ (2 ^ t - 1) * ∑ h, u h ^ (2 ^ t) := by
  induction t generalizing u with
  | zero => simp
  | succ t ih =>
    have n0 : (0 : ℝ) ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
    have cs : (∑ h, u h) ^ 2 ≤ (Fintype.card F : ℝ) * ∑ h, u h ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := (univ : Finset F)) (f := u)
    have h1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    calc (∑ h, u h) ^ (2 ^ (t + 1)) = ((∑ h, u h) ^ 2) ^ (2 ^ t) := by
          rw [← pow_mul, pow_succ, mul_comm]
      _ ≤ ((Fintype.card F : ℝ) * ∑ h, u h ^ 2) ^ (2 ^ t) :=
          pow_le_pow_left₀ (sq_nonneg _) cs _
      _ = (Fintype.card F : ℝ) ^ (2 ^ t) * (∑ h, u h ^ 2) ^ (2 ^ t) := mul_pow _ _ _
      _ ≤ (Fintype.card F : ℝ) ^ (2 ^ t) *
            ((Fintype.card F : ℝ) ^ (2 ^ t - 1) * ∑ h, (u h ^ 2) ^ (2 ^ t)) :=
          mul_le_mul_of_nonneg_left (ih fun h => u h ^ 2) (pow_nonneg n0 _)
      _ = (Fintype.card F : ℝ) ^ (2 ^ (t + 1) - 1) * ∑ h, u h ^ (2 ^ (t + 1)) := by
          rw [← mul_assoc, ← pow_add]
          congr 1
          · congr 1
            rw [pow_succ]
            omega
          · refine sum_congr rfl fun h _ => ?_
            rw [← pow_mul, pow_succ, mul_comm]

/-- The cube sum with one more direction is the sum over that direction of the cube sum of
the multiplicative derivative. -/
lemma cube_succ (t : ℕ) (f : F → ℝ) :
    ∑ x, ∑ H : Fin (t + 1) → F, ∏ ω : Fin (t + 1) → Bool,
        f (x + ∑ j, if ω j then H j else 0) =
      ∑ h₀, ∑ x, ∑ h : Fin t → F, ∏ ω : Fin t → Bool,
        D h₀ f (x + ∑ j, if ω j then h j else 0) := by
  have hprod : ∀ (x h₀ : F) (h : Fin t → F),
      ∏ ω : Fin (t + 1) → Bool,
        f (x + ∑ j, if ω j then (Fin.cons h₀ h : Fin (t + 1) → F) j else 0) =
      ∏ ω : Fin t → Bool, D h₀ f (x + ∑ j, if ω j then h j else 0) := by
    intro x h₀ h
    rw [← (Fin.consEquiv fun _ => Bool).prod_comp, Fintype.prod_prod_type, Fintype.prod_bool]
    simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      if_true, Bool.false_eq_true, if_false, zero_add]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ω _ => ?_
    unfold D
    rw [mul_comm]
    congr 2
    ring
  calc ∑ x, ∑ H : Fin (t + 1) → F, ∏ ω : Fin (t + 1) → Bool,
        f (x + ∑ j, if ω j then H j else 0)
      = ∑ x, ∑ h₀, ∑ h : Fin t → F, ∏ ω : Fin (t + 1) → Bool,
          f (x + ∑ j, if ω j then (Fin.cons h₀ h : Fin (t + 1) → F) j else 0) := by
        refine sum_congr rfl fun x _ => ?_
        rw [← (Fin.consEquiv fun _ => F).sum_comp, Fintype.sum_prod_type]
        rfl
    _ = ∑ x, ∑ h₀, ∑ h : Fin t → F, ∏ ω : Fin t → Bool,
          D h₀ f (x + ∑ j, if ω j then h j else 0) := by
        simp_rw [hprod]
    _ = _ := sum_comm

theorem gvn : ∀ (t : ℕ) (c : Fin (t + 1) → F) (f : Fin (t + 1) → F → ℝ),
    (∀ i : Fin t, c (Fin.last t) ≠ c i.castSucc) →
    (∀ i : Fin t, ∀ x, |f i.castSucc x| ≤ 1) →
    (∑ x, ∑ d, ∏ i, f i (x + c i * d)) ^ (2 ^ t) ≤
      (Fintype.card F : ℝ) ^ (2 ^ (t + 1) - t - 1) *
        ∑ x, ∑ h : Fin t → F, ∏ ω : Fin t → Bool,
          f (Fin.last t) (x + ∑ j, if ω j then h j else 0) := by
  intro t
  induction t with
  | zero =>
    intro c f _ _
    have e : ∑ x, ∑ d, f 0 (x + c 0 * d) = (Fintype.card F : ℝ) * ∑ x, f 0 x := by
      rw [sum_comm]
      have : ∀ d, ∑ x, f 0 (x + c 0 * d) = ∑ x, f 0 x := fun d =>
        Fintype.sum_equiv (Equiv.addRight (c 0 * d)) _ _ fun x => rfl
      simp [this]
    simpa using e.le
  | succ t ih =>
    intro c f hc hb
    set n : ℝ := (Fintype.card F : ℝ) with hn
    have n0 : 0 ≤ n := Nat.cast_nonneg _
    -- peel off the first function
    have hcl : c (Fin.last (t + 1)) ≠ c 0 := by
      have := hc 0
      simpa using this
    let L : F → ℝ := fun h => ∑ x, ∑ d, ∏ i : Fin (t + 1),
      D ((c i.succ - c 0) * h) (f i.succ) (x + c i.succ * d)
    have s1 : (∑ x, ∑ d, ∏ i, f i (x + c i * d)) ^ 2 ≤ n * ∑ h, L h := by
      have key := step (f 0) (fun x => by simpa using hb 0 x) (c 0)
        (fun x d => ∏ i : Fin (t + 1), f i.succ (x + c i.succ * d))
      have eL : ∑ x, ∑ d, ∏ i, f i (x + c i * d) = ∑ x, ∑ d, f 0 (x + c 0 * d) *
          ∏ i : Fin (t + 1), f i.succ (x + c i.succ * d) := by
        refine sum_congr rfl fun x _ => sum_congr rfl fun d _ => ?_
        rw [Fin.prod_univ_succ]
      rw [eL]
      refine key.trans_eq ?_
      congr 1
      refine sum_congr rfl fun h _ => sum_congr rfl fun x _ => sum_congr rfl fun d _ => ?_
      rw [← prod_mul_distrib]
      exact prod_congr rfl fun i _ => shift_mul (c 0) (c i.succ) (f i.succ) x d h
    have s2 : ∀ h, L h ^ (2 ^ t) ≤ n ^ (2 ^ (t + 1) - t - 1) *
        ∑ x, ∑ h' : Fin t → F, ∏ ω : Fin t → Bool,
          D ((c (Fin.last (t + 1)) - c 0) * h) (f (Fin.last (t + 1)))
            (x + ∑ j, if ω j then h' j else 0) := fun h => by
      have := ih (fun i => c i.succ) (fun i => D ((c i.succ - c 0) * h) (f i.succ))
        (fun i => by simpa using hc i.succ)
        (fun i x => D_bound (fun y => by simpa using hb i.succ y) _ x)
      simpa using this
    have e2 : 2 ^ t ≤ 2 ^ (t + 1) - t - 1 + 0 + 2 ^ t := by omega
    have hexp : 2 ^ t + (2 ^ t - 1) + (2 ^ (t + 1) - t - 1) = 2 ^ (t + 1 + 1) - (t + 1) - 1 := by
      have h1 : t + 1 ≤ 2 ^ t := Nat.lt_two_pow_self
      have h2 : 2 ^ (t + 1) = 2 * 2 ^ t := by ring
      have h3 : 2 ^ (t + 1 + 1) = 4 * 2 ^ t := by ring
      omega
    calc (∑ x, ∑ d, ∏ i, f i (x + c i * d)) ^ (2 ^ (t + 1))
        = ((∑ x, ∑ d, ∏ i, f i (x + c i * d)) ^ 2) ^ (2 ^ t) := by
          rw [← pow_mul, pow_succ, mul_comm]
      _ ≤ (n * ∑ h, L h) ^ (2 ^ t) := pow_le_pow_left₀ (sq_nonneg _) s1 _
      _ = n ^ (2 ^ t) * (∑ h, L h) ^ (2 ^ t) := mul_pow _ _ _
      _ ≤ n ^ (2 ^ t) * (n ^ (2 ^ t - 1) * ∑ h, L h ^ (2 ^ t)) :=
          mul_le_mul_of_nonneg_left (pow_sum_le t L) (pow_nonneg n0 _)
      _ ≤ n ^ (2 ^ t) * (n ^ (2 ^ t - 1) * ∑ h, n ^ (2 ^ (t + 1) - t - 1) *
            ∑ x, ∑ h' : Fin t → F, ∏ ω : Fin t → Bool,
              D ((c (Fin.last (t + 1)) - c 0) * h) (f (Fin.last (t + 1)))
                (x + ∑ j, if ω j then h' j else 0)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (pow_nonneg n0 _))
            (pow_nonneg n0 _)
          exact sum_le_sum fun h _ => s2 h
      _ = n ^ (2 ^ (t + 1 + 1) - (t + 1) - 1) * ∑ h₀, ∑ x, ∑ h' : Fin t → F,
            ∏ ω : Fin t → Bool,
              D h₀ (f (Fin.last (t + 1))) (x + ∑ j, if ω j then h' j else 0) := by
          rw [← mul_sum, ← hexp, pow_add, pow_add]
          rw [sum_scale (c (Fin.last (t + 1)) - c 0) (sub_ne_zero.mpr hcl)
            (fun h₀ => ∑ x, ∑ h' : Fin t → F, ∏ ω : Fin t → Bool,
              D h₀ (f (Fin.last (t + 1))) (x + ∑ j, if ω j then h' j else 0))]
          ring
      _ = _ := by rw [cube_succ]

end UsGvN

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H2_R2.H2 := by
  intro s p _ _ c hc f hb
  have := UsGvN.gvn s c f (fun i h => (Fin.castSucc_lt_last i).ne' (hc h)) hb
  rwa [ZMod.card] at this
