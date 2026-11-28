import OMAStatements.S_oeis_a270440
import Mathlib

namespace OMA.P270440

open OMA.S_oeis_a270440 Filter Asymptotics Real

/-- For M >= 1: binomial(k, 2) >= M exactly when k >= (sqrt(8M+1)+1)/2. -/
lemma key (M k : ℕ) (hM : 1 ≤ M) :
    M ≤ k.choose 2 ↔ (Real.sqrt (8 * (M : ℝ) + 1) + 1) / 2 ≤ (k : ℝ) := by
  have hc : ((k.choose 2 : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := Nat.cast_choose_two ℝ k
  have hMr : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  constructor
  · intro h
    have h' : (M : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) / 2 := by
      rw [← hc]
      exact_mod_cast h
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at h
      omega
    have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk0
    have hs : Real.sqrt (8 * (M : ℝ) + 1) ≤ 2 * (k : ℝ) - 1 := by
      rw [show 2 * (k : ℝ) - 1 = Real.sqrt ((2 * (k : ℝ) - 1) ^ 2) from
        (Real.sqrt_sq (by linarith)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    linarith
  · intro h
    have h1 : Real.sqrt (8 * (M : ℝ) + 1) ≤ 2 * (k : ℝ) - 1 := by linarith
    obtain ⟨_, h2⟩ := Real.sqrt_le_iff.1 h1
    have h3 : (M : ℝ) ≤ ((k.choose 2 : ℕ) : ℝ) := by
      rw [hc]
      nlinarith
    exact_mod_cast h3

lemma closed (n : ℕ) :
    a n = ⌈(Real.sqrt (8 * ((2 * n).choose n : ℝ) + 1) + 1) / 2⌉₊ := by
  have hM : 1 ≤ (2 * n).choose n := Nat.choose_pos (by omega)
  have hS : {k : ℕ | (2 * n).choose n ≤ k.choose 2}
      = {k : ℕ | ⌈(Real.sqrt (8 * ((2 * n).choose n : ℝ) + 1) + 1) / 2⌉₊ ≤ k} := by
    ext k
    constructor
    · intro h
      exact Nat.ceil_le.2 ((key _ k hM).1 h)
    · intro h
      exact (key _ k hM).2 (Nat.ceil_le.1 h)
  unfold a
  rw [hS]
  obtain ⟨c, hc⟩ : ∃ c, ⌈(Real.sqrt (8 * ((2 * n).choose n : ℝ) + 1) + 1) / 2⌉₊ = c := ⟨_, rfl⟩
  rw [hc]
  have hmem : c ∈ {k : ℕ | c ≤ k} := by simp
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · have h := Nat.sInf_mem (⟨c, hmem⟩ : {k : ℕ | c ≤ k}.Nonempty)
    simpa using h

/-- The Stirling approximant of n!. -/
noncomputable def s (n : ℕ) : ℝ := Real.sqrt (2 * n * π) * (n / exp 1) ^ n

/-- The comparison function for the central binomial coefficient. -/
noncomputable def T (n : ℕ) : ℝ := 4 ^ n / Real.sqrt (π * n)

/-- The comparison function of the conjecture. -/
noncomputable def tgt (n : ℕ) : ℝ := (2 : ℝ) ^ ((n : ℝ) + 1 / 2) / (π * (n : ℝ)) ^ ((1 : ℝ) / 4)

/-- sqrt(2 * binomial(2n, n)). -/
noncomputable def w (n : ℕ) : ℝ := Real.sqrt (2 * ((2 * n).choose n : ℝ))

lemma cb_eq (n : ℕ) : (((2 * n).choose n : ℕ) : ℝ)
    = ((2 * n).factorial : ℝ) / ((n.factorial : ℝ) * (n.factorial : ℝ)) := by
  have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [show 2 * n - n = n by omega] at h
  have h' : (((2 * n).choose n : ℕ) : ℝ) * (n.factorial : ℝ) * (n.factorial : ℝ)
      = ((2 * n).factorial : ℝ) := by exact_mod_cast h
  have hpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  rw [eq_div_iff (by positivity)]
  linarith

lemma stirling_ratio (n : ℕ) (hn : 1 ≤ n) : s (2 * n) / (s n * s n) = T n := by
  unfold s T
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have he : (0 : ℝ) < exp 1 := exp_pos 1
  obtain ⟨r, hr⟩ : ∃ r, Real.sqrt (π * n) = r := ⟨_, rfl⟩
  have hrpos : 0 < r := by
    rw [← hr]
    exact Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = π * n := by
    rw [← hr]
    exact Real.sq_sqrt (by positivity)
  obtain ⟨y, hy⟩ : ∃ y, (n : ℝ) / exp 1 = y := ⟨_, rfl⟩
  have hypos : 0 < y := by
    rw [← hy]
    positivity
  have e1 : Real.sqrt (2 * ((2 * n : ℕ) : ℝ) * π) = 2 * r := by
    have e : 2 * ((2 * n : ℕ) : ℝ) * π = (2 * r) ^ 2 := by
      push_cast
      rw [mul_pow, hr2]
      ring
    rw [e]
    exact Real.sqrt_sq (by positivity)
  have e2 : Real.sqrt (2 * (n : ℝ) * π) * Real.sqrt (2 * (n : ℝ) * π) = 2 * r ^ 2 := by
    rw [Real.mul_self_sqrt (by positivity), hr2]
    ring
  have e3 : (((2 * n : ℕ) : ℝ) / exp 1) ^ (2 * n) = 4 ^ n * (y ^ n * y ^ n) := by
    have e : ((2 * n : ℕ) : ℝ) / exp 1 = 2 * y := by
      rw [← hy]
      push_cast
      ring
    rw [e, pow_mul, show (2 * y) ^ 2 = 4 * (y * y) by ring, mul_pow, mul_pow]
  rw [e1, e3, hr, hy,
    show Real.sqrt (2 * (n : ℝ) * π) * y ^ n * (Real.sqrt (2 * (n : ℝ) * π) * y ^ n)
      = (Real.sqrt (2 * (n : ℝ) * π) * Real.sqrt (2 * (n : ℝ) * π)) * (y ^ n * y ^ n) by ring, e2]
  have hY : 0 < y ^ n := by positivity
  field_simp

lemma cb_equiv : (fun n : ℕ => (((2 * n).choose n : ℕ) : ℝ)) ~[atTop] T := by
  have h0 : (fun n : ℕ => (n.factorial : ℝ)) ~[atTop] s := Stirling.factorial_isEquivalent_stirling
  have ht : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => (by show n ≤ 2 * n; omega)) tendsto_id
  have h1 : (fun n : ℕ => ((2 * n).factorial : ℝ)) ~[atTop] (fun n => s (2 * n)) :=
    h0.comp_tendsto ht
  have h3 := h1.div (h0.mul h0)
  have h4 : ((fun n : ℕ => ((2 * n).factorial : ℝ))
      / ((fun n : ℕ => (n.factorial : ℝ)) * fun n : ℕ => (n.factorial : ℝ)))
      = fun n : ℕ => (((2 * n).choose n : ℕ) : ℝ) := by
    funext n
    simp only [Pi.div_apply, Pi.mul_apply]
    exact (cb_eq n).symm
  rw [h4] at h3
  refine h3.trans_eventuallyEq ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Pi.div_apply, Pi.mul_apply]
  exact stirling_ratio n hn

lemma T_pos (n : ℕ) (hn : 1 ≤ n) : 0 < T n := by
  unfold T
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have : 0 < Real.sqrt (π * n) := Real.sqrt_pos.2 (by positivity)
  positivity

lemma tgt_sq (n : ℕ) (hn : 1 ≤ n) : 0 < tgt n ∧ tgt n ^ 2 = 2 * T n := by
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hx : (0 : ℝ) < π * n := by positivity
  have e1 : (2 : ℝ) ^ ((n : ℝ) + 1 / 2) = 2 ^ n * Real.sqrt 2 := by
    rw [Real.rpow_add two_pos, Real.rpow_natCast, Real.sqrt_eq_rpow]
  have e2 : (π * (n : ℝ)) ^ ((1 : ℝ) / 4) = Real.sqrt (Real.sqrt (π * n)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
    norm_num
  have hr : 0 < Real.sqrt (π * n) := Real.sqrt_pos.2 hx
  have hrr : 0 < Real.sqrt (Real.sqrt (π * n)) := Real.sqrt_pos.2 hr
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt (Real.sqrt (π * n)) ^ 2 = Real.sqrt (π * n) := Real.sq_sqrt hr.le
  unfold tgt T
  rw [e1, e2]
  constructor
  · positivity
  · rw [div_pow, mul_pow, h2, h3, ← pow_mul]
    have e4 : (2 : ℝ) ^ (n * 2) = 4 ^ n := by
      rw [mul_comm, pow_mul]
      norm_num
    rw [e4]
    ring

lemma cb_ge (n : ℕ) : 2 * n ≤ (2 * n).choose n := by
  have h := Nat.choose_le_centralBinom 1 n
  rw [Nat.choose_one_right] at h
  exact h

lemma w_pos (n : ℕ) : 0 < w n := by
  unfold w
  have hM : (1 : ℝ) ≤ ((2 * n).choose n : ℝ) := by
    exact_mod_cast Nat.choose_pos (show n ≤ 2 * n by omega)
  exact Real.sqrt_pos.2 (by linarith)

lemma w_tendsto : Tendsto w atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  refine tendsto_atTop_mono (fun n => ?_) h1
  unfold w
  apply Real.sqrt_le_sqrt
  have h := cb_ge n
  have h' : (2 * (n : ℝ)) ≤ ((2 * n).choose n : ℝ) := by exact_mod_cast h
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

lemma a_bounds (n : ℕ) : w n ≤ (a n : ℝ) ∧ (a n : ℝ) ≤ w n + 2 := by
  have hM : (1 : ℝ) ≤ ((2 * n).choose n : ℝ) := by
    exact_mod_cast Nat.choose_pos (show n ≤ 2 * n by omega)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, ((2 * n).choose n : ℝ) = M := ⟨_, rfl⟩
  rw [closed n]
  unfold w
  rw [hMdef] at hM ⊢
  have hw0 : 0 ≤ Real.sqrt (2 * M) := Real.sqrt_nonneg _
  have hw2 : Real.sqrt (2 * M) ^ 2 = 2 * M := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ Real.sqrt (8 * M + 1) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (8 * M + 1) ^ 2 = 8 * M + 1 := Real.sq_sqrt (by linarith)
  have hlo : 2 * Real.sqrt (2 * M) ≤ Real.sqrt (8 * M + 1) := by nlinarith
  have hhi : Real.sqrt (8 * M + 1) ≤ 2 * Real.sqrt (2 * M) + 1 := by nlinarith
  have hx0 : 0 ≤ (Real.sqrt (8 * M + 1) + 1) / 2 := by positivity
  have hc1 := Nat.le_ceil ((Real.sqrt (8 * M + 1) + 1) / 2)
  have hc2 := Nat.ceil_lt_add_one hx0
  constructor <;> linarith

lemma a_div_w : Tendsto (fun n : ℕ => (a n : ℝ) / w n) atTop (nhds 1) := by
  have h2 : Tendsto (fun n : ℕ => 1 + 2 / w n) atTop (nhds 1) := by
    have h := (tendsto_const_nhds (x := (2 : ℝ))).div_atTop w_tendsto
    have h' := (tendsto_const_nhds (x := (1 : ℝ))).add h
    simpa using h'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun n => ?_) (fun n => ?_)
  · have hw := w_pos n
    have hb := (a_bounds n).1
    show (1 : ℝ) ≤ (a n : ℝ) / w n
    rw [le_div_iff₀ hw]
    linarith
  · have hw := w_pos n
    have hb := (a_bounds n).2
    show (a n : ℝ) / w n ≤ 1 + 2 / w n
    rw [div_le_iff₀ hw]
    field_simp
    linarith

lemma w_div_tgt : Tendsto (fun n : ℕ => w n / tgt n) atTop (nhds 1) := by
  have hT : ∀ᶠ n : ℕ in atTop, T n ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (T_pos n hn).ne'
  have h1 : Tendsto ((fun n : ℕ => (((2 * n).choose n : ℕ) : ℝ)) / T) atTop (nhds 1) :=
    (isEquivalent_iff_tendsto_one hT).1 cb_equiv
  have h2 : Tendsto (fun n : ℕ => Real.sqrt (((fun n : ℕ => (((2 * n).choose n : ℕ) : ℝ)) / T) n))
      atTop (nhds (Real.sqrt 1)) := (Real.continuous_sqrt.tendsto 1).comp h1
  rw [Real.sqrt_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨htp, hts⟩ := tgt_sq n hn
  have hTp := T_pos n hn
  simp only [Pi.div_apply]
  unfold w
  have e : Real.sqrt (2 * ((2 * n).choose n : ℝ)) / tgt n
      = Real.sqrt (2 * ((2 * n).choose n : ℝ)) / Real.sqrt (tgt n ^ 2) := by
    rw [Real.sqrt_sq htp.le]
  rw [e, hts, ← Real.sqrt_div (by positivity)]
  congr 1
  field_simp

lemma asym : (fun n : ℕ => (a n : ℝ)) ~[atTop] tgt := by
  have hz : ∀ᶠ n : ℕ in atTop, tgt n ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (tgt_sq n hn).1.ne'
  refine (isEquivalent_iff_tendsto_one hz).2 ?_
  have h := a_div_w.mul w_div_tgt
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hw := w_pos n
  have ht := (tgt_sq n hn).1
  simp only [Pi.div_apply]
  field_simp

end OMA.P270440

theorem OMA.solution : type_of% @OMA.S_oeis_a270440.main :=
  ⟨OMA.P270440.closed, OMA.P270440.asym⟩
