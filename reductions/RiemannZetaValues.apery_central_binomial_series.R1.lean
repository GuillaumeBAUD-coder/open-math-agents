import FormalConjectures.Wikipedia.RiemannZetaValues

/-! # Finite triangle summation and its vanishing boundary
The WZ pair is the s = 1 case of T. Amdeberhan, Faster and Faster Convergent Series for ζ(3).
-/
-- Credit: @steveDOTdigital
namespace OMA.R_RiemannZetaValues_apery_central_binomial_series_R1
open Filter Topology
def H1 : Prop := ∀ N : ℕ,
    (∑ n ∈ Finset.range N, 1 / ((n : ℂ)+1)^3) =
    (5/2 : ℂ) * (∑ n ∈ Finset.range N, (-1 : ℂ)^n /
      (((n : ℂ)+1)^3 * Nat.centralBinom (n+1))) - (1/2 : ℂ) * (∑ k ∈ Finset.range N, (-1 : ℂ)^k * (k.factorial : ℂ)^2 * ((N-k-1).factorial : ℂ) /
      (((N+k+1).factorial : ℂ) * (k+1)))
def H2 : Prop := Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (-1 : ℂ)^k * (k.factorial : ℂ)^2 * ((N-k-1).factorial : ℂ) /
      (((N+k+1).factorial : ℂ) * (k+1))) atTop (𝓝 0)

theorem main : H1 → H2 → type_of% @RiemannZetaValues.apery_central_binomial_series := by
  intro finite vanish
  let a (n : ℕ) : ℂ := 1 / ((n : ℂ)+1)^3
  let b (n : ℕ) : ℂ := (-1 : ℂ)^n / (((n : ℂ)+1)^3 * Nat.centralBinom (n+1))
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ)+1)^3) := by
    simpa using (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)^3) 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3))
  have hn (n : ℕ) : ‖((n : ℂ)+1)‖ = (n : ℝ)+1 := by
    exact_mod_cast (Complex.norm_natCast (n+1))
  have ha : Summable a := hs.of_norm_bounded fun n => by simp [a, norm_div, norm_pow, hn]
  have hb : Summable b := hs.of_norm_bounded fun n => by
    have hh : 1 ≤ (Nat.centralBinom (n+1) : ℝ) := by exact_mod_cast Nat.centralBinom_pos (n+1)
    calc
      ‖b n‖ = 1 / (((n : ℝ)+1)^3 * Nat.centralBinom (n+1)) := by simp [b,norm_pow,hn]
      _ ≤ _ := one_div_le_one_div_of_le (by positivity) (le_mul_of_one_le_right (by positivity) hh)
  have hz : riemannZeta 3 = ∑' n, a n := by
    simpa [a] using zeta_eq_tsum_one_div_nat_add_one_cpow (s := (3 : ℕ)) (by norm_num)
  rw [hz]
  apply tendsto_nhds_unique ha.hasSum.tendsto_sum_nat
  have hh := (hb.hasSum.tendsto_sum_nat.const_mul (5/2 : ℂ)).sub
    (Filter.Tendsto.const_mul (1/2 : ℂ) (show Tendsto _ _ _ from vanish))
  simpa only [mul_zero,sub_zero] using hh.congr' (Filter.Eventually.of_forall (fun n => (finite n).symm))

end OMA.R_RiemannZetaValues_apery_central_binomial_series_R1
