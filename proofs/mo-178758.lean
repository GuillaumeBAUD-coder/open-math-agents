import OMAStatements.S_mo_178758
import Mathlib

/-!
# MathOverflow 178758: regular polygons maximise the sum of chord lengths

Sort the points by argument, extend the sorted arguments to a monotone
sequence `T` on the naturals with `T (m + n) = T m + 2 * pi`, group the
chords by step `k`, and apply Jensen to the concave sine on `[0, pi]`.
-/

open Finset

namespace OMA.Aux178758

lemma shift (g : ℕ → ℝ) (n i : ℕ) :
    ∑ k ∈ range n, g (i + 1 + k) = ∑ k ∈ range n, g (i + k) + g (i + n) - g i := by
  have h1 := Finset.sum_range_succ (fun k => g (i + k)) n
  have h2 := Finset.sum_range_succ' (fun k => g (i + k)) n
  simp only [add_zero] at h2
  have h3 : ∀ k, g (i + (k + 1)) = g (i + 1 + k) := fun k => by
    congr 1; omega
  simp only [h3] at h2
  linarith

lemma periodic_sum (g : ℕ → ℝ) (n : ℕ) (hg : ∀ m, g (m + n) = g m) (i : ℕ) :
    ∑ k ∈ range n, g (i + k) = ∑ k ∈ range n, g k := by
  induction i with
  | zero => simp
  | succ i ih => rw [shift, ih, hg]; ring

lemma eper (x : ℝ) :
    Complex.exp (Complex.I * ((x + 2 * Real.pi : ℝ) : ℂ)) = Complex.exp (Complex.I * (x : ℂ)) := by
  push_cast
  rw [mul_add, Complex.exp_add]
  have h : Complex.I * (2 * (Real.pi : ℂ)) = 2 * Real.pi * Complex.I := by ring
  rw [h, Complex.exp_two_pi_mul_I, mul_one]

lemma chord (a b : ℝ) (h0 : b ≤ a) (h1 : a ≤ b + 2 * Real.pi) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖
      = 2 * Real.sin ((a - b) / 2) := by
  have e : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) =
      Complex.exp ((b : ℂ) * Complex.I) *
        (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    · push_cast; ring
    · ring
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi (x := (a - b) / 2) (by linarith) (by linarith)
  rw [e, norm_mul, Complex.norm_exp_I_mul_ofReal_sub_one, Complex.norm_exp_ofReal_mul_I,
    one_mul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]

lemma double (T : ℕ → ℝ) (n : ℕ) (hm : Monotone T)
    (hp : ∀ m, T (m + n) = T m + 2 * Real.pi) :
    ∑ i ∈ range n, ∑ j ∈ range n,
        ‖Complex.exp (Complex.I * (T j : ℂ)) - Complex.exp (Complex.I * (T i : ℂ))‖
      = ∑ k ∈ range n, ∑ i ∈ range n, 2 * Real.sin ((T (i + k) - T i) / 2) := by
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← periodic_sum (fun j =>
    ‖Complex.exp (Complex.I * (T j : ℂ)) - Complex.exp (Complex.I * (T i : ℂ))‖) n ?_ i]
  · refine Finset.sum_congr rfl fun k hk => ?_
    refine chord _ _ (hm (Nat.le_add_right i k)) ?_
    rw [← hp]
    have := mem_range.1 hk
    exact hm (by omega)
  · intro m
    simp only [hp, eper]

lemma arcsum (T : ℕ → ℝ) (n : ℕ) (hp : ∀ m, T (m + n) = T m + 2 * Real.pi) (k : ℕ) :
    ∑ i ∈ range n, T (k + i) = ∑ i ∈ range n, T i + 2 * Real.pi * k := by
  induction k with
  | zero => simp
  | succ k ih => rw [shift, ih, hp]; push_cast; ring

lemma jensen (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hm : Monotone T)
    (hp : ∀ m, T (m + n) = T m + 2 * Real.pi) (k : ℕ) (hk : k < n) :
    ∑ i ∈ range n, 2 * Real.sin ((T (i + k) - T i) / 2)
      ≤ n * (2 * Real.sin (Real.pi * k / n)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc := strictConcaveOn_sin_Icc.concaveOn
  have h := hc.le_map_sum (t := range n) (w := fun _ => (1 : ℝ) / n)
    (p := fun i => (T (i + k) - T i) / 2) (fun _ _ => by positivity)
    (by simp; field_simp)
    (fun i _ => ⟨by have := hm (Nat.le_add_right i k); linarith, by
      have := hm (show i + k ≤ i + n by omega)
      rw [hp] at this; linarith⟩)
  have hs : ∑ i ∈ range n, (1 : ℝ) / n * ((T (i + k) - T i) / 2) = Real.pi * k / n := by
    rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_sub_distrib]
    have h4 := arcsum T n hp k
    have h5 : ∀ i, T (k + i) = T (i + k) := fun i => by rw [add_comm]
    simp only [h5] at h4
    rw [h4]; field_simp; ring
  simp only [smul_eq_mul] at h
  rw [hs, ← Finset.mul_sum] at h
  have h6 := mul_le_mul_of_nonneg_left h hn'.le
  rw [← mul_assoc, mul_one_div_cancel hn'.ne', one_mul] at h6
  rw [← Finset.mul_sum]
  linarith

lemma toRange (n : ℕ) (w : Fin n → ℂ) (S : ℕ → ℝ)
    (h : ∀ i : Fin n, w i = Complex.exp (Complex.I * (S i : ℂ))) :
    ∑ i : Fin n, ∑ j : Fin n, ‖w j - w i‖ = ∑ i ∈ range n, ∑ j ∈ range n,
        ‖Complex.exp (Complex.I * (S j : ℂ)) - Complex.exp (Complex.I * (S i : ℂ))‖ := by
  simp only [h]
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range n,
        ‖Complex.exp (Complex.I * (S j : ℂ)) - Complex.exp (Complex.I * (S i : ℂ))‖) n]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun j =>
        ‖Complex.exp (Complex.I * (S j : ℂ)) - Complex.exp (Complex.I * (S i : ℂ))‖) n]

end OMA.Aux178758

open OMA.Aux178758 in
theorem OMA.solution : type_of% @OMA.S_mo_178758.main := by
  intro n hn z hz
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi := Real.pi_pos
  unfold OMA.S_mo_178758.distanceSum
  rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
  -- the regular polygon
  have hR : ∑ i : Fin n, ∑ j : Fin n,
      ‖OMA.S_mo_178758.regular n j - OMA.S_mo_178758.regular n i‖
      = ∑ k ∈ range n, (n : ℝ) * (2 * Real.sin (Real.pi * k / n)) := by
    rw [toRange n (OMA.S_mo_178758.regular n) (fun m => 2 * Real.pi * m / n) (fun i => rfl), double]
    · refine Finset.sum_congr rfl fun k _ => ?_
      have h7 : ∀ i ∈ range n, 2 * Real.sin ((2 * Real.pi * ((i + k : ℕ) : ℝ) / n
          - 2 * Real.pi * (i : ℝ) / n) / 2) = 2 * Real.sin (Real.pi * k / n) := fun i _ => by
        congr 2
        push_cast
        field_simp
        ring
      rw [Finset.sum_congr rfl h7, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    · intro a b hab
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      simp only
      gcongr
    · intro m
      push_cast
      field_simp
  rw [hR]
  -- sort the points
  let θ : Fin n → ℝ := fun i => Complex.arg (z i)
  have hzθ : ∀ i, z i = Complex.exp (Complex.I * (θ i : ℂ)) := fun i => by
    have := Complex.norm_mul_exp_arg_mul_I (z i)
    rw [hz i, Complex.ofReal_one, one_mul] at this
    rw [mul_comm, this]
  let σ := Tuple.sort θ
  have hσ : Monotone (θ ∘ σ) := Tuple.monotone_sort θ
  let t : ℕ → ℝ := fun r => if h : r < n then θ (σ ⟨r, h⟩) else 0
  let T : ℕ → ℝ := fun m => t (m % n) + 2 * Real.pi * ((m / n : ℕ) : ℝ)
  have hT0 : ∀ q r, r < n → T (n * q + r) = t r + 2 * Real.pi * q := fun q r h => by
    simp only [T, Nat.mul_add_mod, Nat.mod_eq_of_lt h, Nat.mul_add_div hn, Nat.div_eq_of_lt h,
      add_zero]
  have hp : ∀ m, T (m + n) = T m + 2 * Real.pi := fun m => by
    simp only [T, Nat.add_mod_right, Nat.add_div_right _ hn]
    push_cast; ring
  have hmono : Monotone T := by
    refine monotone_nat_of_le_succ fun m => ?_
    have hr := Nat.mod_lt m hn
    have hmq := Nat.div_add_mod m n
    rw [← hmq]
    generalize m / n = q at *
    generalize m % n = r at *
    by_cases h : r + 1 < n
    · rw [add_assoc, hT0 q r hr, hT0 q (r + 1) h]
      have : t r ≤ t (r + 1) := by
        simp only [t, dif_pos hr, dif_pos h]
        exact hσ (by simp [Fin.le_def])
      linarith
    · have h1 : n * q + r + 1 = n * (q + 1) + 0 := by
        have : r + 1 = n := by omega
        rw [add_assoc, this]; ring
      rw [h1, hT0 q r hr, hT0 (q + 1) 0 hn]
      have : t r ≤ t 0 + 2 * Real.pi := by
        simp only [t, dif_pos hr, dif_pos hn, θ]
        have a1 := Complex.arg_le_pi (z (σ ⟨r, hr⟩))
        have a2 := Complex.neg_pi_lt_arg (z (σ ⟨0, hn⟩))
        linarith
      push_cast
      linarith
  have hL : ∑ i : Fin n, ∑ j : Fin n, ‖z j - z i‖
      = ∑ i : Fin n, ∑ j : Fin n, ‖z (σ j) - z (σ i)‖ := by
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp σ]
  rw [hL, toRange n (fun i => z (σ i)) T (fun i => by
    have h0 := hT0 0 i.1 i.2
    simp only [mul_zero, zero_add, Nat.cast_zero, add_zero, t, dif_pos i.2] at h0
    simp only [h0]
    exact hzθ _), double T n hmono hp]
  exact Finset.sum_le_sum fun k hk => jensen T n hn hmono hp k (mem_range.1 hk)
