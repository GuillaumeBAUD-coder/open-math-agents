import OMAReductions.R_Erdos5_erdos_5_variants_merikoski_measure_R1
import Mathlib.NumberTheory.Chebyshev
open Finset Real
-- Chebyshev estimate adapted from @zarnab222-dev (#1312) via the merged Romanoff H1 proof.
private theorem prime_count_lower (x : ℝ) (hx : 64 ≤ x) :
    x / (4 * log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hx' : 1 < x := by linarith
  have h₂ := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
  norm_num at h₂
  have h₈ := Real.log_le_sub_one_of_pos (x := 8) (by norm_num)
  have hlog := Real.log_le_sub_one_of_pos (x := (x+2)/8) (by linarith)
  rw [Real.log_div (by linarith) (by norm_num)] at hlog
  have h := Chebyshev.pi_ge' hx'
  apply le_trans _ h
  have he : x/(4*log x) = (x/4)/log x := by ring
  rw [he]
  apply div_le_div_of_nonneg_right _ (Real.log_pos hx').le
  nlinarith [mul_nonneg (sub_nonneg.mpr hx'.le) (sub_nonneg.mpr h₂)]
open Filter Real
open scoped Topology

private lemma logRatio : Tendsto (fun n : ℕ => log (Nat.nth Nat.Prime n) / log n) atTop (𝓝 1) := by
  let p (n : ℕ) : ℝ := Nat.nth Nat.Prime n
  let l (n : ℕ) := log (p n)
  have hp : Tendsto p atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop
  have hl : Tendsto l atTop atTop := tendsto_log_atTop.comp hp
  have h₁ : Tendsto (fun n => log 8 / l n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hl
  have h₂ : Tendsto (fun n => log (l n) / l n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hl
  have low : Tendsto (fun n => 1 - (log 8 / l n + log (l n) / l n)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub (h₁.add h₂)
  have inv : Tendsto (fun n : ℕ => log n / l n) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' low tendsto_const_nhds
    · filter_upwards [eventually_ge_atTop 64] with n hn
      have hb := Nat.add_two_le_nth_prime n
      have hp64 : 64 ≤ p n := by dsimp [p]; exact_mod_cast (by omega : 64 ≤ Nat.nth Nat.Prime n)
      have hpos : 0 < l n := Real.log_pos (by linarith)
      have hpc : Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1 := by
        rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ,
          if_pos (Nat.prime_nth_prime n), ← Nat.primeCounting', Nat.primeCounting'_nth_eq]
      have hpi := prime_count_lower (p n) hp64
      change p n / (4 * l n) ≤ _ at hpi
      have hfloor : ⌊p n⌋₊ = Nat.nth Nat.Prime n := by simp [p]
      rw [hfloor,hpc,Nat.cast_add,Nat.cast_one] at hpi
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      have hbound : p n / (8 * l n) ≤ n := by
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith [(div_le_iff₀ (show 0 < 4 * l n by positivity)).mp hpi,
          mul_nonneg (sub_nonneg.mpr hn') hpos.le]
      have hreal := Real.log_le_log (x := p n / (8*l n)) (by apply div_pos <;> linarith) hbound
      rw [Real.log_div (by linarith) (by positivity),Real.log_mul (by norm_num) hpos.ne'] at hreal
      change l n - (log 8 + log (l n)) ≤ log n at hreal
      rw [← add_div, ← div_self hpos.ne', ← sub_div]
      exact div_le_div_of_nonneg_right hreal hpos.le
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hn' : 1 < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
      have hnle : (n : ℝ) ≤ p n := by dsimp [p]; exact_mod_cast (Nat.le_of_lt (show n < Nat.nth Nat.Prime n by have := Nat.add_two_le_nth_prime n; omega))
      exact (div_le_one (Real.log_pos (hn'.trans_le hnle))).mpr (Real.log_le_log (by linarith) hnle)
  simpa [l,p] using inv.inv₀ (by norm_num : (1:ℝ) ≠ 0)
theorem OMA.solution : OMA.R_Erdos5_erdos_5_variants_merikoski_measure_R1.H2 := logRatio
