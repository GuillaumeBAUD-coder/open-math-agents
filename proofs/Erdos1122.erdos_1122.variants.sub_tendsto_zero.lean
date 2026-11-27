import FormalConjectures.ErdosProblems.«1122»

/-! # Additive functions with vanishing successive differences -/
-- Credit: @steveDOTdigital
namespace OMA.ArithmeticLog
open Filter
open scoped Topology

private lemma scaleTop {k : ℕ} (hk : 0 < k) :
    Tendsto (fun n : ℕ => k*n) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  exact hn.trans (Nat.le_mul_of_pos_left n hk)

-- Every fixed finite shift has the same limiting difference zero.
private lemma shift {f : ℕ → ℝ} (d : Tendsto (fun n => f (n+1)-f n) atTop (𝓝 0)) (h : ℕ) :
    Tendsto (fun n => f (n+h)-f n) atTop (𝓝 0) := by
  induction h with
  | zero => simp
  | succ h ih =>
    have lim := (d.comp (tendsto_add_atTop_nat h)).add ih
    simpa only [Function.comp_apply,zero_add,sub_add_sub_cancel,Nat.add_assoc] using lim

-- A multiple of a differs by one from a number coprime to a. Compare
-- the two evaluations after these fixed shifts, first for a and then for ab.
private lemma complete {f : ℕ → ℝ}
    (hf : ∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a*b) = f a + f b)
    (d : Tendsto (fun n => f (n+1)-f n) atTop (𝓝 0)) :
    ∀ a > 0, ∀ b > 0, f (a*b) = f a + f b := by
  have scaled (a : ℕ) (ha : 0 < a) :
      Tendsto (fun n => f (a*(a*n)) - f (a*n)) atTop (𝓝 (f a)) := by
    have h₁ := d.comp (scaleTop ha)
    have h₂ := (shift d a).comp ((scaleTop ha).comp (scaleTop ha))
    have lim := ((tendsto_const_nhds (x := f a)).add h₁).sub h₂
    rw [add_zero,sub_zero] at lim
    apply lim.congr'
    filter_upwards with n
    simp only [Function.comp_apply]
    have cop : a.Coprime (a*n+1) := by
      simp
    have eq := hf a ha (a*n+1) (by omega) cop
    rw [Nat.mul_add,Nat.mul_one] at eq
    linarith
  intro a ha b hb
  have ab := scaled (a*b) (by positivity : 0 < a*b)
  have bpart := (scaled b hb).comp (scaleTop ha)
  have apart := (scaled a ha).comp (scaleTop (Nat.mul_pos hb hb))
  apply tendsto_nhds_unique ab
  convert apart.add bpart using 1
  ext n
  simp only [Function.comp_apply]
  simp [mul_comm,mul_left_comm]

private lemma logDiff :
    Tendsto (fun n : ℕ => Real.log ((n+1 : ℕ) : ℝ) - Real.log (n : ℝ)) atTop (𝓝 0) := by
  have frac := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [add_zero] at frac
  have lim := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp frac
  rw [Real.log_one] at lim
  apply lim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have nz : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have eq : 1+1/(n : ℝ) = ((n : ℝ)+1)/n := by field_simp
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, eq, Real.log_div (by positivity : (n : ℝ)+1 ≠ 0) nz]

-- A normalized completely additive function g has g(2n)=g(n).
-- Beyond a finite threshold, each binary digit changes g by at most δ.
private lemma dyadic {g : ℕ → ℝ}
    (additive : ∀ a > 0, ∀ b > 0, g (a*b) = g a + g b)
    (two : g 2 = 0) (d : Tendsto (fun n => g (n+1)-g n) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, ∀ j n : ℕ, n < 2^j → |g n| ≤ K + δ*j := by
  obtain ⟨M,hM⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.mp d) δ hδ)
  let K := ∑ i ∈ Finset.range (2*M+4), |g i|
  have small (n : ℕ) (hn : n < 2*M+4) : |g n| ≤ K :=
    Finset.single_le_sum (fun i _ => abs_nonneg (g i)) (Finset.mem_range.mpr hn)
  refine ⟨K,?_⟩
  intro j
  induction j with
  | zero =>
    intro n hn
    simp only [pow_zero] at hn
    simpa using small n (by omega)
  | succ j ih =>
    intro n hn
    by_cases cut : n < 2*M+4
    · have := small n cut
      exact this.trans (le_add_of_nonneg_right (by positivity))
    · let q := n/2
      have hq : 0 < q := by dsimp [q]; omega
      have qj : q < 2^j := by rw [pow_succ] at hn; dsimp [q]; omega
      have even : g (2*q) = g q := by rw [additive 2 (by decide) q hq,two,zero_add]
      have inc : |g n| ≤ |g q| + δ := by
        by_cases parity : n = 2*q
        · rw [parity,even]; linarith
        · have odd : n = 2*q+1 := by dsimp [q] at *; omega
          have close := hM (2*q) (by dsimp [q]; omega)
          rw [Real.dist_eq,sub_zero] at close
          have tri := abs_add_le (g (2*q+1)-g (2*q)) (g (2*q))
          rw [sub_add_cancel,even] at tri
          rw [even] at close
          rw [odd]
          linarith
      have prior := ih q qj
      push_cast
      linarith

theorem rigidity {f : ℕ → ℝ}
    (hf : ∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a*b) = f a + f b)
    (hd : Tendsto (fun n => f (n+1)-f n) atTop (𝓝 0)) :
    ∃ c : ℝ, ∀ n > 0, f n = c * Real.log n := by
  let c := f 2 / Real.log 2
  let g (n : ℕ) := f n - c * Real.log n
  have full := complete hf hd
  have ga (a : ℕ) (ha : 0 < a) (b : ℕ) (hb : 0 < b) : g (a*b) = g a + g b := by
    simp [g,full a ha b hb,Nat.cast_mul,Real.log_mul (by positivity : (a : ℝ) ≠ 0) (by positivity : (b : ℝ) ≠ 0)]
    ring
  have gt : g 2 = 0 := by
    simp [g,c,div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne']
  have gd : Tendsto (fun n => g (n+1)-g n) atTop (𝓝 0) := by
    have lim := hd.sub ((tendsto_const_nhds (x := c)).mul logDiff)
    rw [mul_zero,sub_zero] at lim
    apply lim.congr'
    filter_upwards with n
    dsimp [g]
    ring
  refine ⟨c,fun n hn => ?_⟩
  suffices gz : g n = 0 by exact sub_eq_zero.mp gz
  by_contra ne
  have positive := abs_pos.mpr ne
  let δ := |g n|/(2*(n:ℝ))
  have np : 0 < (n:ℝ) := by exact_mod_cast hn
  have hδ : 0 < δ := div_pos positive (by positivity)
  obtain ⟨K,bound⟩ := dyadic ga gt gd hδ
  have gp (k : ℕ) : g (n^k) = (k : ℝ)*g n := by
    induction k with
    | zero =>
      have h := ga 1 (by decide) 1 (by decide)
      simpa using (show g 1 = 0 by simp at h; linarith)
    | succ k ih =>
      rw [pow_succ,ga _ (pow_pos hn _) _ hn,ih,Nat.cast_succ]
      ring
  obtain ⟨k,hk⟩ := exists_nat_gt (max 0 (2*K/|g n|))
  have kp : 0 < k := by exact_mod_cast (lt_of_le_of_lt (le_max_left ..) hk : (0 : ℝ) < k)
  have lt : n^k < 2^(n*k) := by
    rw [pow_mul]
    exact Nat.pow_lt_pow_left n.lt_two_pow_self kp.ne'
  have cert := bound (n*k) (n^k) lt
  rw [gp,abs_mul,abs_of_nonneg (Nat.cast_nonneg k),Nat.cast_mul] at cert
  have deq : δ * (n : ℝ) = |g n|/2 := by dsimp [δ]; field_simp
  rw [← mul_assoc,deq] at cert
  have big := (div_lt_iff₀ positive).mp (lt_of_le_of_lt (le_max_right ..) hk)
  nlinarith
end OMA.ArithmeticLog

theorem OMA.solution : type_of% @Erdos1122.erdos_1122.variants.sub_tendsto_zero :=
  fun _ hf hd => OMA.ArithmeticLog.rigidity hf hd
