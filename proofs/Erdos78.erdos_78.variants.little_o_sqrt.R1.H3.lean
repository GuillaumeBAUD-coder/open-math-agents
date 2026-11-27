import OMAReductions.R_Erdos78_erdos_78_variants_little_o_sqrt_R1

/-! # Logarithmic digit depth and the homogeneous-set bound -/
-- Credit: @steveDOTdigital
namespace OMA.HexDepth
open Filter Asymptotics
open scoped Topology

theorem bound : ∃ f : ℕ → ℝ, f =o[atTop] (fun n ↦ Real.sqrt (n : ℝ)) ∧
    ∀ᶠ n : ℕ in atTop, ∃ d : ℕ, n ≤ 16^d ∧ 3^d+1 ≤ ⌈f n⌉₊ := by
  let L := Nat.log 16
  let f (n : ℕ) : ℝ := 4 * 3^(L n)
  refine ⟨f,?_,?_⟩
  · have logtop : Tendsto L atTop atTop := by
      refine tendsto_atTop.2 fun b => ?_
      filter_upwards [eventually_ge_atTop (16^b)] with n hn
      exact Nat.le_log_of_pow_le (by decide) hn
    have lim : Tendsto (fun n : ℕ => 4*((3/4:ℝ)^(L n))) atTop (𝓝 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (3/4:ℝ)) (by norm_num)).comp logtop).const_mul 4
    apply isLittleO_of_tendsto'
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact fun h => False.elim ((Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))).ne' h)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds lim
    · filter_upwards with n
      change 0 ≤ f n / Real.sqrt n
      dsimp [f]
      positivity
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have power : (16:ℝ)^(L n) ≤ n := by exact_mod_cast Nat.pow_log_le_self 16 (by omega : n ≠ 0)
      have square : ((4:ℝ)^(L n))^2 ≤ n := by
        rw [pow_two,← mul_pow]
        norm_num at *
        exact power
      have root := Real.sq_sqrt (Nat.cast_nonneg n : 0 ≤ (n:ℝ))
      have lb : (4:ℝ)^(L n) ≤ Real.sqrt n := by
        nlinarith [Real.sqrt_nonneg (n:ℝ), show 0 ≤ (4:ℝ)^(L n) by positivity]
      change f n / Real.sqrt n ≤ _
      calc
        _ ≤ f n / 4^(L n) := div_le_div_of_nonneg_left (by dsimp [f]; positivity) (by positivity) lb
        _ = _ := by rw [div_pow]; dsimp [f]; ring
  · filter_upwards with n
    refine ⟨L n+1,(Nat.lt_pow_succ_log_self (by decide : 1 < 16) n).le,?_⟩
    have exactF : f n = ((4*3^(L n) : ℕ) : ℝ) := by simp [f]
    rw [exactF,Nat.ceil_natCast,pow_succ]
    have : 0 < 3^(L n) := by positivity
    omega
end OMA.HexDepth

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_little_o_sqrt_R1.H3 := OMA.HexDepth.bound
