import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H2_R2
import Mathlib

/-!
# The generalized von Neumann inequality for the Gowers U^s cube sum

Step H2 of reduction R1.H2.R1.H1.R1.H2.R2 of Erdős 142 (reduction by @DPS0340). For s ≥ 1,
pairwise distinct c_0, …, c_s in ZMod p and real functions f_0, …, f_s of which all but the
last are bounded by 1,

  (∑ x d, ∏ i, f_i (x + c_i d)) ^ (2^s) ≤ p ^ (2^(s+1) - s - 1) * ∑ x h, ∏ ω, f_s (x + ω · h),

the last sum running over x, h in (ZMod p)^s and ω in {0,1}^s. This is a classical inequality
(Gowers); the proof is by induction on s, one Cauchy–Schwarz step per function.

One step (`cs_step`): if |g| ≤ 1 then (∑ y d, g y Φ y d)^2 ≤ |F| ∑ y d h, Φ y d Φ y (d + h).
After the substitution y = x + c_0 d the first function becomes g y; the step removes it and
replaces every other f_i by its multiplicative derivative D_t f x = f x f (x + t) with
t = (c_i - c_0) h. The induction hypothesis is applied for each h, a power-mean inequality
(`pm`) passes from the sum over h to the sum of powers, and the cube sum satisfies
U_(t+1)(g) = ∑ h, U_t(D_h g) (`U_succ`). To avoid subtraction in exponents the induction
proves |F|^(s+1) Λ^(2^s) ≤ |F|^(2^(s+1)) U_s; this starts at s = 0. Everything is done over
an arbitrary finite field and specialised to ZMod p at the end.
-/

namespace OMAGvNGen

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

/-- Power mean: |F| (∑ Y)^(2^t) ≤ |F|^(2^t) ∑ Y^(2^t). -/
lemma pm (t : ℕ) : ∀ Y : F → ℝ,
    (Fintype.card F : ℝ) * (∑ h, Y h) ^ (2 ^ t)
      ≤ (Fintype.card F : ℝ) ^ (2 ^ t) * ∑ h, Y h ^ (2 ^ t) := by
  induction t with
  | zero =>
    intro Y
    simp
  | succ t ih =>
    intro Y
    have hN : (0 : ℝ) ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
    have e : ∀ z : ℝ, z ^ (2 ^ (t + 1)) = (z ^ 2) ^ (2 ^ t) := by
      intro z
      rw [← pow_mul, pow_succ, mul_comm]
    have h1 : ((∑ h, Y h) ^ 2) ^ (2 ^ t)
        ≤ ((Fintype.card F : ℝ) * ∑ h, Y h ^ 2) ^ (2 ^ t) :=
      pow_le_pow_left₀ (sq_nonneg _) (sq_sum_le Y) _
    have h2 := ih (fun h => Y h ^ 2)
    calc (Fintype.card F : ℝ) * (∑ h, Y h) ^ (2 ^ (t + 1))
        = (Fintype.card F : ℝ) * ((∑ h, Y h) ^ 2) ^ (2 ^ t) := by rw [e]
      _ ≤ (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) * ∑ h, Y h ^ 2) ^ (2 ^ t) :=
          mul_le_mul_of_nonneg_left h1 hN
      _ = (Fintype.card F : ℝ) ^ (2 ^ t)
            * ((Fintype.card F : ℝ) * (∑ h, Y h ^ 2) ^ (2 ^ t)) := by
          rw [mul_pow]
          ring
      _ ≤ (Fintype.card F : ℝ) ^ (2 ^ t)
            * ((Fintype.card F : ℝ) ^ (2 ^ t) * ∑ h, (Y h ^ 2) ^ (2 ^ t)) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hN _)
      _ = (Fintype.card F : ℝ) ^ (2 ^ (t + 1)) * ∑ h, Y h ^ (2 ^ (t + 1)) := by
          have e2 : (Fintype.card F : ℝ) ^ (2 ^ (t + 1))
              = (Fintype.card F : ℝ) ^ (2 ^ t) * (Fintype.card F : ℝ) ^ (2 ^ t) := by
            rw [← pow_add, pow_succ, mul_two]
          rw [e2]
          simp only [e]
          ring

/-- The unnormalised cube sum of dimension t. -/
def U (t : ℕ) (g : F → ℝ) : ℝ :=
  ∑ x : F, ∑ h : Fin t → F, ∏ ω : Fin t → Bool, g (x + ∑ j : Fin t, if ω j then h j else 0)

/-- Splitting off the first coordinate. -/
def consE (t : ℕ) (β : Type*) : β × (Fin t → β) ≃ (Fin (t + 1) → β) where
  toFun p := Fin.cons p.1 p.2
  invFun f := (f 0, Fin.tail f)
  left_inv p := by simp
  right_inv f := by simp

lemma prod_cube (t : ℕ) (g : F → ℝ) (x h0 : F) (h' : Fin t → F) :
    ∏ ω : Fin (t + 1) → Bool,
        g (x + ∑ j : Fin (t + 1), if ω j then (Fin.cons h0 h' : Fin (t + 1) → F) j else 0)
      = ∏ ω' : Fin t → Bool, D h0 g (x + ∑ j : Fin t, if ω' j then h' j else 0) := by
  have e : ∀ S : F, g (x + (h0 + S)) * g (x + S) = D h0 g (x + S) := by
    intro S
    unfold D
    rw [mul_comm, add_comm h0 S, ← add_assoc]
  rw [← Fintype.prod_equiv (consE t Bool)
      (fun p : Bool × (Fin t → Bool) => g (x + ∑ j : Fin (t + 1),
        if (Fin.cons p.1 p.2 : Fin (t + 1) → Bool) j
          then (Fin.cons h0 h' : Fin (t + 1) → F) j else 0))
      (fun ω => g (x + ∑ j : Fin (t + 1),
        if ω j then (Fin.cons h0 h' : Fin (t + 1) → F) j else 0))
      (fun p => rfl)]
  rw [Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ↓reduceIte, Bool.false_eq_true,
    zero_add]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun ω' _ => e _

lemma U_succ (t : ℕ) (g : F → ℝ) : U (t + 1) g = ∑ h0 : F, U t (D h0 g) := by
  unfold U
  calc ∑ x : F, ∑ h : Fin (t + 1) → F, ∏ ω : Fin (t + 1) → Bool,
          g (x + ∑ j : Fin (t + 1), if ω j then h j else 0)
      = ∑ x : F, ∑ p : F × (Fin t → F), ∏ ω : Fin (t + 1) → Bool,
          g (x + ∑ j : Fin (t + 1),
            if ω j then (Fin.cons p.1 p.2 : Fin (t + 1) → F) j else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        exact (Fintype.sum_equiv (consE t F)
          (fun p : F × (Fin t → F) => ∏ ω : Fin (t + 1) → Bool,
            g (x + ∑ j : Fin (t + 1),
              if ω j then (Fin.cons p.1 p.2 : Fin (t + 1) → F) j else 0))
          (fun h => ∏ ω : Fin (t + 1) → Bool,
            g (x + ∑ j : Fin (t + 1), if ω j then h j else 0))
          (fun p => rfl)).symm
    _ = ∑ x : F, ∑ h0 : F, ∑ h' : Fin t → F, ∏ ω' : Fin t → Bool,
          D h0 g (x + ∑ j : Fin t, if ω' j then h' j else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun h0 _ => Finset.sum_congr rfl fun h' _ =>
          prod_cube t g x h0 h'
    _ = _ := Finset.sum_comm

theorem gvn_gen : ∀ (s : ℕ) (c : Fin (s + 1) → F), Function.Injective c →
    ∀ (f : Fin (s + 1) → F → ℝ), (∀ i : Fin s, ∀ x, |f i.castSucc x| ≤ 1) →
    (Fintype.card F : ℝ) ^ (s + 1) * (∑ x, ∑ d, ∏ i, f i (x + c i * d)) ^ (2 ^ s)
      ≤ (Fintype.card F : ℝ) ^ (2 ^ (s + 1)) * U s (f (Fin.last s)) := by
  intro s
  induction s with
  | zero =>
    intro c _ f _
    have h1 : ∑ x, ∑ d, ∏ i : Fin 1, f i (x + c i * d)
        = (Fintype.card F : ℝ) * ∑ y, f 0 y := by
      have h := shift (c 0) (fun y _ => f 0 y)
      simp only [Fin.prod_univ_one]
      rw [h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h2 : U 0 (f (Fin.last 0)) = ∑ y, f 0 y := by
      simp [U]
    rw [h1, h2]
    exact le_of_eq (by ring)
  | succ s ih =>
    intro c hc f hf
    have hN : (0 : ℝ) ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
    have ha : Function.Injective (fun i : Fin (s + 1) => c i.succ - c 0) := fun i j h =>
      Fin.succ_injective _ (hc (sub_left_injective h))
    have hlast : c (Fin.last s).succ - c 0 ≠ 0 :=
      sub_ne_zero.mpr (fun h => Fin.succ_ne_zero _ (hc h))
    have e1 : ∑ x, ∑ d, ∏ i, f i (x + c i * d)
        = ∑ y, ∑ d, f 0 y * ∏ i : Fin (s + 1), f i.succ (y + (c i.succ - c 0) * d) := by
      rw [← shift (c 0)
        (fun y d => f 0 y * ∏ i : Fin (s + 1), f i.succ (y + (c i.succ - c 0) * d))]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => ?_
      rw [Fin.prod_univ_succ]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      congr 1
      ring
    have s1 : (∑ x, ∑ d, ∏ i, f i (x + c i * d)) ^ 2
        ≤ (Fintype.card F : ℝ) * ∑ h, ∑ y, ∑ d, ∏ i : Fin (s + 1),
            D ((c i.succ - c 0) * h) (f i.succ) (y + (c i.succ - c 0) * d) := by
      rw [e1]
      refine (cs_step (f 0) (fun x => by simpa using hf 0 x)
        (fun y d => ∏ i : Fin (s + 1), f i.succ (y + (c i.succ - c 0) * d))).trans
        (le_of_eq ?_)
      congr 1
      rw [sum3]
      refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun y _ =>
        Finset.sum_congr rfl fun d _ => ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [mul_add, ← add_assoc]
      rfl
    have s2 : ∀ h, (Fintype.card F : ℝ) ^ (s + 1) * (∑ y, ∑ d, ∏ i : Fin (s + 1),
            D ((c i.succ - c 0) * h) (f i.succ) (y + (c i.succ - c 0) * d)) ^ (2 ^ s)
        ≤ (Fintype.card F : ℝ) ^ (2 ^ (s + 1))
            * U s (D ((c (Fin.last s).succ - c 0) * h) (f (Fin.last (s + 1)))) := by
      intro h
      have h3 := ih (fun i : Fin (s + 1) => c i.succ - c 0) ha
        (fun i => D ((c i.succ - c 0) * h) (f i.succ))
        (fun i x => D_abs (fun z => by
          rw [Fin.succ_castSucc]
          exact hf i.succ z) _ x)
      rwa [Fin.succ_last] at h3
    have hpm := pm s (fun h => ∑ y, ∑ d, ∏ i : Fin (s + 1),
            D ((c i.succ - c 0) * h) (f i.succ) (y + (c i.succ - c 0) * d))
    have hU : U (s + 1) (f (Fin.last (s + 1)))
        = ∑ h, U s (D ((c (Fin.last s).succ - c 0) * h) (f (Fin.last (s + 1)))) := by
      rw [U_succ]
      exact (Fintype.sum_equiv (Equiv.mulLeft₀ _ hlast)
        (fun h => U s (D ((c (Fin.last s).succ - c 0) * h) (f (Fin.last (s + 1)))))
        (fun h0 => U s (D h0 (f (Fin.last (s + 1))))) (fun h => rfl)).symm
    rw [hU]
    have e2 : ∀ z : ℝ, z ^ (2 ^ (s + 1)) = (z ^ 2) ^ (2 ^ s) := by
      intro z
      rw [← pow_mul, pow_succ, mul_comm]
    have e3 : (Fintype.card F : ℝ) ^ (2 ^ (s + 1 + 1))
        = (Fintype.card F : ℝ) ^ (2 ^ s) * (Fintype.card F : ℝ) ^ (2 ^ s)
          * (Fintype.card F : ℝ) ^ (2 ^ (s + 1)) := by
      rw [← pow_add, ← pow_add]
      congr 1
      rw [pow_succ 2 (s + 1), pow_succ 2 s]
      ring
    have h4 := pow_le_pow_left₀ (sq_nonneg (∑ x, ∑ d, ∏ i, f i (x + c i * d))) s1 (2 ^ s)
    rw [mul_pow] at h4
    calc (Fintype.card F : ℝ) ^ (s + 1 + 1) * (∑ x, ∑ d, ∏ i, f i (x + c i * d)) ^ (2 ^ (s + 1))
        = (Fintype.card F : ℝ) ^ (s + 1) * ((Fintype.card F : ℝ)
            * ((∑ x, ∑ d, ∏ i, f i (x + c i * d)) ^ 2) ^ (2 ^ s)) := by
          rw [e2]
          ring
      _ ≤ (Fintype.card F : ℝ) ^ (s + 1) * ((Fintype.card F : ℝ)
            * ((Fintype.card F : ℝ) ^ (2 ^ s) * (∑ h, ∑ y, ∑ d, ∏ i : Fin (s + 1),
              D ((c i.succ - c 0) * h) (f i.succ) (y + (c i.succ - c 0) * d)) ^ (2 ^ s))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hN) (pow_nonneg hN _)
      _ = (Fintype.card F : ℝ) ^ (s + 1) * (Fintype.card F : ℝ) ^ (2 ^ s)
            * ((Fintype.card F : ℝ) * (∑ h, ∑ y, ∑ d, ∏ i : Fin (s + 1),
              D ((c i.succ - c 0) * h) (f i.succ) (y + (c i.succ - c 0) * d)) ^ (2 ^ s)) := by
          ring
      _ ≤ (Fintype.card F : ℝ) ^ (s + 1) * (Fintype.card F : ℝ) ^ (2 ^ s)
            * ((Fintype.card F : ℝ) ^ (2 ^ s) * ∑ h, (∑ y, ∑ d, ∏ i : Fin (s + 1),
              D ((c i.succ - c 0) * h) (f i.succ) (y + (c i.succ - c 0) * d)) ^ (2 ^ s)) :=
          mul_le_mul_of_nonneg_left hpm (mul_nonneg (pow_nonneg hN _) (pow_nonneg hN _))
      _ = (Fintype.card F : ℝ) ^ (2 ^ s) * (Fintype.card F : ℝ) ^ (2 ^ s)
            * ∑ h, (Fintype.card F : ℝ) ^ (s + 1) * (∑ y, ∑ d, ∏ i : Fin (s + 1),
              D ((c i.succ - c 0) * h) (f i.succ) (y + (c i.succ - c 0) * d)) ^ (2 ^ s) := by
          rw [← Finset.mul_sum]
          ring
      _ ≤ (Fintype.card F : ℝ) ^ (2 ^ s) * (Fintype.card F : ℝ) ^ (2 ^ s)
            * ∑ h, (Fintype.card F : ℝ) ^ (2 ^ (s + 1))
              * U s (D ((c (Fin.last s).succ - c 0) * h) (f (Fin.last (s + 1)))) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ => s2 h)
            (mul_nonneg (pow_nonneg hN _) (pow_nonneg hN _))
      _ = _ := by
          rw [← Finset.mul_sum, e3]
          ring

theorem gvn_final (s : ℕ) (c : Fin (s + 1) → F) (hc : Function.Injective c)
    (f : Fin (s + 1) → F → ℝ) (hf : ∀ i : Fin s, ∀ x, |f i.castSucc x| ≤ 1) :
    (∑ x, ∑ d, ∏ i, f i (x + c i * d)) ^ (2 ^ s)
      ≤ (Fintype.card F : ℝ) ^ (2 ^ (s + 1) - s - 1) * U s (f (Fin.last s)) := by
  have h := gvn_gen s c hc f hf
  have hcard : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hle : s + 1 < 2 ^ (s + 1) := Nat.lt_two_pow_self
  have hsplit : (Fintype.card F : ℝ) ^ (2 ^ (s + 1))
      = (Fintype.card F : ℝ) ^ (s + 1) * (Fintype.card F : ℝ) ^ (2 ^ (s + 1) - s - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, mul_assoc] at h
  exact le_of_mul_le_mul_left h (pow_pos hcard _)

end OMAGvNGen

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H2_R2.H2 := by
  intro s p _ _ c hc f hf
  have h := OMAGvNGen.gvn_final s c hc f hf
  rw [ZMod.card] at h
  exact h
