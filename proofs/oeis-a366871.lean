import OMAStatements.S_oeis_a366871
import Mathlib

open Filter Asymptotics

namespace OMA.A366871

set_option maxHeartbeats 600000 in
lemma error_bound (a : ℕ → ℕ) (h0 : a 0 = 0)
    (hrec : ∀ n : ℕ, 1 ≤ n → a n = n - a (a (n - 1) / 5))
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hq : c ^ 2 + 5*c = 5) (n : ℕ) :
    |(a n : ℝ) - c*n| ≤ 10 * Real.sqrt n := by
  have ha (i : ℕ) : a i ≤ i := by
    cases i with
    | zero => simp [h0]
    | succ i => rw [hrec (i+1) (by omega)]; exact Nat.sub_le _ _
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [h0]
    | succ k =>
      let m := a k / 5
      let r := a k % 5
      have hk := ha k
      have hm : 5*m ≤ k := by dsimp [m]; omega
      have hr : r ≤ 4 := by dsimp [r]; omega
      have hdiv : a k = 5*m + r := by dsimp [m, r]; omega
      have hsub : a m ≤ k+1 := (ha m).trans (by omega)
      have hs : (a (k+1) : ℝ) = (k:ℝ)+1-a m := by
        rw [hrec (k+1) (by omega)]
        simp only [Nat.add_sub_cancel, Nat.cast_sub hsub, Nat.cast_add, Nat.cast_one, m]
      have hb := ih m (by omega)
      have hd := ih k (by omega)
      rw [abs_le] at hb hd
      have hsK : Real.sqrt (k:ℝ) ≤ Real.sqrt ((k:ℝ)+1) := Real.sqrt_le_sqrt (by linarith)
      have sm := Real.sq_sqrt (Nat.cast_nonneg m : 0 ≤ (m:ℝ))
      have sk := Real.sq_sqrt (show 0 ≤ (k:ℝ)+1 by positivity)
      have hlow : 1 ≤ Real.sqrt ((k:ℝ)+1) := by
        calc
          1 = Real.sqrt 1 := by norm_num
          _ ≤ _ := Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) k])
      have hsm : 2*Real.sqrt (m:ℝ) ≤ Real.sqrt ((k:ℝ)+1) := by
        have hmR : 5*(m:ℝ) ≤ k := by exact_mod_cast hm
        nlinarith [Real.sqrt_nonneg (m:ℝ), Real.sqrt_nonneg ((k:ℝ)+1),
          Nat.cast_nonneg (α := ℝ) m]
      have hu : c*((a k:ℝ)-c*k) ≤ 10*Real.sqrt ((k:ℝ)+1) := by
        calc
          _ ≤ c*(10*Real.sqrt (k:ℝ)) := mul_le_mul_of_nonneg_left hd.2 hc
          _ ≤ 1*(10*Real.sqrt (k:ℝ)) := mul_le_mul_of_nonneg_right hc1 (by positivity)
          _ ≤ _ := by linarith
      have hl : -(10*Real.sqrt ((k:ℝ)+1)) ≤ c*((a k:ℝ)-c*k) := by
        have h := mul_le_mul_of_nonneg_left hd.1 hc
        have hh := mul_le_mul_of_nonneg_right hc1 (show 0 ≤ 10*Real.sqrt (k:ℝ) by positivity)
        linarith
      have hrR : (r:ℝ) ≤ 4 := by exact_mod_cast hr
      have hcr : c*(r:ℝ) ≤ 4 := by
        calc
          _ ≤ 1*(r:ℝ) := mul_le_mul_of_nonneg_right hc1 (by positivity)
          _ ≤ _ := by linarith
      have hi : (a k:ℝ) = 5*(m:ℝ)+r := by exact_mod_cast hdiv
      have he : 5*((a (k+1):ℝ)-c*((k:ℝ)+1)) =
          -5*((a m:ℝ)-c*m) - c*((a k:ℝ)-c*k) + c*r + c^2 := by
        rw [hs]
        linear_combination -(k+1:ℝ)*hq + c*hi
      push_cast
      apply abs_le.mpr
      constructor
      · linarith only [he, hb.2, hu, hsm, hlow, mul_nonneg hc (Nat.cast_nonneg (α := ℝ) r), sq_nonneg c]
      · nlinarith only [he, hb.1, hl, hsm, hlow, hcr, hc1, mul_nonneg hc (sub_nonneg.mpr hc1)]

end OMA.A366871

theorem OMA.solution : type_of% @OMA.S_oeis_a366871.main := by
  intro a h0 hrec
  let c : ℝ := (3*Real.sqrt 5-5)/2
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hc : 0 < c := by dsimp [c]; nlinarith [Real.sqrt_nonneg 5]
  have hc1 : c ≤ 1 := by dsimp [c]; nlinarith [Real.sqrt_nonneg 5]
  have hq : c^2+5*c = 5 := by dsimp [c]; nlinarith
  change (fun n : ℕ => (a n:ℝ)-c*n) =o[atTop] (fun n : ℕ => c*(n:ℝ))
  apply (isLittleO_const_mul_right_iff hc.ne').2
  apply isLittleO_iff.mpr
  intro ε hε
  have ht : Tendsto (fun n : ℕ => Real.sqrt (n:ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (10/ε)] with n hn
  have hεn : 10 ≤ ε*Real.sqrt (n:ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ hε).mp hn
  simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  calc
    _ ≤ 10*Real.sqrt (n:ℝ) := OMA.A366871.error_bound a h0 hrec c hc.le hc1 hq n
    _ ≤ (ε*Real.sqrt (n:ℝ))*Real.sqrt (n:ℝ) :=
      mul_le_mul_of_nonneg_right hεn (Real.sqrt_nonneg _)
    _ = ε*(n:ℝ) := by rw [mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)]
