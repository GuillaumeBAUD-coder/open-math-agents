import OMAReductions.R_Erdos170_erdos170_existing_bounds_R1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! Leech's estimate uses a nonnegative trigonometric weight on every difference.
Each positive spacing and its negative occur among ordered pairs of ruler marks. -/

open Finset Filter Real Erdos170
open scoped Topology

private lemma ruler_weight (n : ℕ) (a : ℝ) :
    2 * (∑ k ∈ range n, (1 - cos (a * (k + 1 : ℝ)))) ≤ (F n : ℝ)^2 := by
  classical
  have hmin : F n ∈ (PerfectRulersLengthN n).image Finset.card := Finset.min'_mem _ _
  obtain ⟨A, hA, hcard⟩ := mem_image.mp hmin
  have hper := (mem_filter.mp hA).2
  have hw (k : Fin n) : ∃ p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ A ∧ p.2 = p.1 + (k.val+1) := by
    obtain ⟨u, hu, v, hv, h⟩ := hper (k.val+1) (mem_range.mpr (by omega))
    exact ⟨(u,v), hu, hv, by dsimp; omega⟩
  choose p hp1 hp2 hp using hw
  let q (k : Fin n) := (p k).swap
  have pinj : Function.Injective p := by
    intro i j h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Fin.ext (by have := hp i; have := hp j; omega)
  have qinj : Function.Injective q := fun _ _ h => pinj (Prod.swap_injective h)
  let w (z : ℕ × ℕ) := 1 - cos (a*z.2 - a*z.1)
  have wp (i : Fin n) : w (p i) = 1 - cos (a * (i.val + 1 : ℝ)) := by
    simp only [w, hp i, Nat.cast_add, Nat.cast_one]
    congr 2
    ring
  have wq (i : Fin n) : w (q i) = w (p i) := by
    dsimp [w, q]
    rw [← cos_neg (a * (p i).1 - a * (p i).2), neg_sub]
  have dis : Disjoint (univ.image p) (univ.image q) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨i, -, rfl⟩ := mem_image.mp hz
    obtain ⟨j, -, hj⟩ := mem_image.mp hz'
    have h1 := congrArg Prod.fst hj
    have h2 := congrArg Prod.snd hj
    change (p j).2 = (p i).1 at h1
    change (p j).1 = (p i).2 at h2
    have := hp i
    have := hp j
    omega
  have sub : univ.image p ∪ univ.image q ⊆ A ×ˢ A := by
    intro z hz
    rcases mem_union.mp hz with h | h <;> obtain ⟨i, -, rfl⟩ := mem_image.mp h
    · exact mem_product.mpr ⟨hp1 i, hp2 i⟩
    · exact mem_product.mpr ⟨hp2 i, hp1 i⟩
  have lower := sum_le_sum_of_subset_of_nonneg (f := w) sub
    (fun z _ _ => sub_nonneg.mpr (cos_le_one _))
  rw [sum_union dis, sum_image pinj.injOn, sum_image qinj.injOn] at lower
  simp only [wq, wp] at lower
  have upper : ∑ z ∈ A ×ˢ A, w z ≤ (A.card : ℝ)^2 := by
    simp only [w, sum_product, cos_sub, sum_sub_distrib, sum_add_distrib, ← mul_sum,
      ← sum_mul, sum_const, nsmul_eq_mul, mul_one, card_product, Nat.cast_mul]
    nlinarith [sq_nonneg (∑ x ∈ A, cos (a * x)), sq_nonneg (∑ x ∈ A, sin (a * x))]
  rw [← hcard, ← Fin.sum_univ_eq_sum_range]
  linarith

private lemma mean_cos (θ : ℝ) (hθ : θ ≠ 0) :
    Tendsto (fun n : ℕ => (∑ k ∈ range n, cos (θ / n * (k + 1 : ℝ))) / n)
      atTop (𝓝 (sin θ / θ)) := by
  let x (n : ℕ) : ℝ := (θ / 2) / n
  have hx : Tendsto x atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
  have hs : Tendsto (fun n => sinc (x n)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, sinc_zero] using (continuous_sinc.tendsto 0).comp hx
  have hc : Tendsto (fun n => cos (θ/2 + x n)) atTop (𝓝 (cos (θ/2))) := by
    exact (continuous_cos.tendsto _).comp (by simpa using tendsto_const_nhds.add hx)
  have hlim := ((tendsto_const_nhds (x := sin (θ/2))).mul hc).div
    ((tendsto_const_nhds (x := θ/2)).mul hs) (by simpa using (div_ne_zero hθ (by norm_num : (2:ℝ) ≠ 0)))
  rw [mul_one] at hlim
  have trig : sin (θ/2) * cos (θ/2) / (θ/2) = sin θ / θ := by
    have h := sin_two_mul (θ/2)
    rw [show 2*(θ/2)=θ by ring] at h
    rw [h]
    ring
  rw [trig] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1, hs.eventually_ne (by norm_num : (1:ℝ) ≠ 0)] with n hn hsn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hx' : x n ≠ 0 := div_ne_zero (div_ne_zero hθ (by norm_num)) hn'
  have formula := Real.sin_mul_sum_cos n (θ / n) (θ / n)
  have adj (k : ℕ) : θ / n * k + θ / n = θ / n * (k + 1) := by ring
  simp_rw [adj] at formula
  rw [show θ / n / 2 = x n by dsimp [x]; ring,
    show (n:ℝ) * (θ/n) / 2 = θ/2 by field_simp,
    show ((n:ℝ)-1)*(θ/n)/2 + θ/n = θ/2 + x n by dsimp [x]; field_simp; ring] at formula
  apply (div_eq_div_iff (mul_ne_zero (div_ne_zero hθ (by norm_num)) hsn) hn').mpr
  have hxmul : (θ/2) * sinc (x n) = n * sin (x n) := by
    rw [sinc_of_ne_zero hx']
    dsimp [x]
    field_simp
  dsimp only
  rw [hxmul, ← formula]
  ring

theorem OMA.solution : OMA.R_Erdos170_erdos170_existing_bounds_R1.H2 := by
  intro θ hθ ε hε
  have hmean := mean_cos θ hθ
  have hlim : Tendsto (fun n : ℕ =>
      2 * (1 - (∑ k ∈ range n, cos (θ/n * (k+1 : ℝ))) / n)) atTop
      (𝓝 (2 * (1 - sin θ / θ))) := tendsto_const_nhds.mul (tendsto_const_nhds.sub hmean)
  filter_upwards [hlim.eventually_const_lt (show 2 * (1 - sin θ / θ) - ε < _ by linarith),
    eventually_ge_atTop 1] with n hlo hn
  apply hlo.le.trans
  have hp : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hh := ruler_weight n (θ/n)
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one] at hh
  rw [div_pow, Real.sq_sqrt hp.le]
  apply (le_div_iff₀ hp).mpr
  calc
    _ = 2 * ((n : ℝ) - ∑ k ∈ range n, cos (θ/n * (k+1 : ℝ))) := by
      field_simp
    _ ≤ _ := hh
