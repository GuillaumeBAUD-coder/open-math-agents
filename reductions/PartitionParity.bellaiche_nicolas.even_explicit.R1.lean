import FormalConjectures.Paper.PartitionParity
import Mathlib

/-!
# An explicit lower bound for even partition numbers

The inputs are Nicolas's earlier lower bound, quoted as (1.13) in Bellaïche
and Nicolas, *Parité des coefficients de formes modulaires*, and the
discriminant-support and convolution inequalities (6.6)–(6.10) in their
proof of Theorem 5. The proof below verifies the numerical comparisons and
the range below 3.
-/

namespace OMA.R_PartitionParity_bellaiche_nicolas_even_explicit_R1

open Real

private theorem small_x {x : ℝ} (hx : 1 < x) (hx₃ : x < 3) :
    0.069 * sqrt x * log (log x) ≤
      ({n : ℕ | n ≤ x ∧ Even (Nat.partitionNumber n)}.ncard : ℝ) := by
  have hlog : 0 < log x := log_pos hx
  by_cases hx₂ : x < 2
  · have hlog₁ : log x ≤ 1 := by linarith [log_le_sub_one_of_pos (by linarith : 0 < x)]
    exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) (log_nonpos hlog.le hlog₁)).trans
      (Nat.cast_nonneg _)
  · have hloglog : log (log x) ≤ 1 := by
      linarith [log_le_sub_one_of_pos hlog, log_le_sub_one_of_pos (by linarith : 0 < x)]
    have hsqrt : sqrt x ≤ 2 := (sqrt_le_left (by norm_num)).2 (by linarith)
    have hlhs : 0.069 * sqrt x * log (log x) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hloglog (show 0 ≤ 0.069 * sqrt x by positivity)
      linarith
    have hfinite : {n : ℕ | n ≤ x ∧ Even (Nat.partitionNumber n)}.Finite := by
      apply (Set.finite_Iic ⌊x⌋₊).subset
      intro n hn
      exact (Nat.le_floor_iff (by linarith : 0 ≤ x)).2 hn.1
    have hnonempty : {n : ℕ | n ≤ x ∧ Even (Nat.partitionNumber n)}.Nonempty := by
      exact ⟨2, by exact_mod_cast le_of_not_gt hx₂, by rw [Nat.partitionNumber_two]; decide⟩
    have hcount : 1 ≤ ({n : ℕ | n ≤ x ∧ Even (Nat.partitionNumber n)}.ncard : ℝ) := by
      exact_mod_cast hnonempty.ncard_pos hfinite
    exact hlhs.trans hcount

private theorem medium_x {x : ℝ} (h : log (log x) ≤ 16.4)
    (h₁ : 0.28 * sqrt x * sqrt (log (log x)) ≤
      ({n : ℕ | n ≤ x ∧ Even (Nat.partitionNumber n)}.ncard : ℝ)) :
    0.069 * sqrt x * log (log x) ≤
      ({n : ℕ | n ≤ x ∧ Even (Nat.partitionNumber n)}.ncard : ℝ) := by
  by_cases hnonneg : 0 ≤ log (log x)
  · have hsqrt : sqrt (log (log x)) ≤ 4.05 :=
      (sqrt_le_left (by norm_num)).2 (h.trans (by norm_num))
    have hconst : 0.069 * sqrt (log (log x)) ≤ 0.28 := by linarith
    refine le_trans ?_ h₁
    calc
      0.069 * sqrt x * log (log x) = (0.069 * sqrt (log (log x))) *
          (sqrt x * sqrt (log (log x))) := by
        conv_lhs => rw [← mul_self_sqrt hnonneg]
        ring
      _ ≤ 0.28 * (sqrt x * sqrt (log (log x))) :=
        mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = _ := by ring
  · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (le_of_not_ge hnonneg)).trans (Nat.cast_nonneg _)

/-- A rational Taylor lower bound suffices for the exponent appearing in (6.10). -/
private theorem log_coeff :
    (0.2965 : ℝ) ≤ 1 - 0.335 + 0.335 * log 0.335 := by
  have hexp : 1 / (0.335 : ℝ) ≤ exp (1.1 : ℝ) := calc
    _ ≤ ∑ i ∈ Finset.range 5, (1.1 : ℝ)^i / (i.factorial : ℝ) := by
      norm_num [Finset.sum_range_succ, Nat.factorial_succ]
    _ ≤ _ := sum_le_exp_of_nonneg (by norm_num) _
  have hinv : exp (-1.1 : ℝ) ≤ 0.335 := by
    rw [exp_neg]
    calc
      _ ≤ (1 / (0.335 : ℝ))⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/0.335) hexp
      _ = _ := by norm_num
  have hlog : (-1.1 : ℝ) ≤ log 0.335 := (le_log_iff_exp_le (by norm_num)).2 hinv
  linarith

private theorem exp_lower : (125 : ℝ) ≤ exp (4.8626 : ℝ) := calc
  _ ≤ ∑ i ∈ Finset.range 11, (4.8626 : ℝ)^i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  _ ≤ _ := sum_le_exp_of_nonneg (by norm_num) _

private theorem pow_log_lower {x : ℝ} (hx : 3 ≤ x) (hloglog : 16.4 ≤ log (log x)) :
    (125 : ℝ) ≤ (log (8*x)) ^ (1 - 0.335 + 0.335 * log 0.335 : ℝ) := by
  have hlogx : 0 < log x := log_pos (by linarith)
  have hle : log x ≤ log (8*x) := log_le_log (by linarith) (by linarith)
  have hlog : 0 < log (8*x) := hlogx.trans_le hle
  have hbase : (16.4 : ℝ) ≤ log (log (8*x)) := hloglog.trans (log_le_log hlogx hle)
  rw [rpow_def_of_pos hlog]
  refine exp_lower.trans (exp_le_exp.mpr ?_)
  calc
    (4.8626 : ℝ) = 16.4 * 0.2965 := by norm_num
    _ ≤ _ := mul_le_mul hbase log_coeff (by norm_num) (by linarith)

private theorem tail_x {x b β W : ℝ} (hx : 3 ≤ x) (hβ₀ : 0 ≤ β)
    (hloglog : 16.4 ≤ log (log x)) (hlead : 0.335 * log (log x) ≤ sqrt b)
    (hβ : β ≤ 0.001)
    (hW : W ≤ (3.29 * (8 + 0.001) * x) /
      ((1 - 0.335) * (log (8*x)) ^ (1 - 0.335 + 0.335 * log 0.335 : ℝ))) :
    0.069 * sqrt x * log (log x) ≤
      sqrt (3*b/8) * sqrt x * ((1 - 2*β)/(1+β)) * (2/3 - W/(x*(1-2*β))) := by
  let L := (log (8*x)) ^ (1 - 0.335 + 0.335 * log 0.335 : ℝ)
  have hL : (125 : ℝ) ≤ L := pow_log_lower hx hloglog
  have hfactor : (0.998 : ℝ) ≤ 1-2*β := by linarith
  have hβden : 0 < 1+β := by linarith
  have hWden : 0 < x*(1-2*β) := mul_pos (by linarith) (by linarith)
  have hWupper : W / (x*(1-2*β)) ≤ 8/25 := by
    refine (div_le_iff₀ hWden).2 (hW.trans ?_)
    have hdiv : 0 < (1 - 0.335) * L := mul_pos (by norm_num) (by linarith)
    apply (div_le_iff₀ hdiv).2
    have hscale : (3.29 : ℝ) * (8 + 0.001) ≤ ((8/25) * (1-2*β))*((1 - 0.335) * L) := calc
      _ ≤ ((8/25) * 0.998) * ((1 - 0.335) * 125) := by norm_num
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hfactor (by norm_num))
        (mul_le_mul_of_nonneg_left hL (by norm_num)) (by norm_num) (by linarith)
    convert mul_le_mul_of_nonneg_right hscale (show 0 ≤ x by linarith) using 1
    ring
  have hbracket : (26/75 : ℝ) ≤ 2/3 - W/(x*(1-2*β)) := by linarith
  have hratio : (0.997 : ℝ) ≤ (1-2*β)/(1+β) := (le_div_iff₀ hβden).2 (by linarith)
  have hradical : 0.61 * (0.335 * log (log x)) ≤ sqrt (3*b/8) := calc
    _ ≤ 0.61 * sqrt b := mul_le_mul_of_nonneg_left hlead (by norm_num)
    _ ≤ sqrt (3/8) * sqrt b := mul_le_mul_of_nonneg_right
      ((le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)) (sqrt_nonneg b)
    _ = _ := by rw [← sqrt_mul (by norm_num : (0 : ℝ) ≤ 3/8)]; congr 1; ring
  have hlog_nonneg : 0 ≤ log (log x) := by linarith
  calc
    0.069 * sqrt x * log (log x) ≤ (0.61 * (0.335 * log (log x)) * sqrt x) *
        0.997 * (26/75) := by
      have hnum : (0.069 : ℝ) ≤ 0.61 * 0.335 * 0.997 * (26/75) := by norm_num
      calc
        _ = 0.069 * (sqrt x * log (log x)) := by ring
        _ ≤ (0.61 * 0.335 * 0.997 * (26/75)) * (sqrt x * log (log x)) :=
          mul_le_mul_of_nonneg_right hnum (mul_nonneg (sqrt_nonneg x) hlog_nonneg)
        _ = _ := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hradical (sqrt_nonneg x))
      hratio (by norm_num) (by positivity)) hbracket (by norm_num)
      (mul_nonneg (by positivity) ((by norm_num : (0 : ℝ) ≤ 0.997).trans hratio))

/-- Nicolas's earlier explicit lower bound for even partition numbers. -/
def H1 : Prop := ∀ x : ℝ, 3 ≤ x →
  0.28 * sqrt x * sqrt (log (log x)) ≤
    ({n : ℕ | n ≤ x ∧ Even (Nat.partitionNumber n)}.ncard : ℝ)

/-- A choice of discriminant power with bounded mod-two support and the
convolution inequality relating its support to even partition numbers. -/
def H2 : Prop := by
  classical
  exact ∀ x : ℝ, 3 ≤ x → 16.4 ≤ log (log x) →
    let Δ : PowerSeries (ZMod 2) :=
      PowerSeries.mk fun n => if ∃ m : ℕ, Odd m ∧ n = m^2 then 1 else 0
    ∃ d : ℕ,
      let b := (2 : ℝ)^d
      let k : ℕ := (2^d-1)/3
      let β := sqrt (3*b/(2*x))
      let W := ({n : ℕ | (n : ℝ) ≤ 8*x+k ∧ (Δ^k).coeff n ≠ 0}.ncard : ℝ)
      0.335 * log (log x) ≤ sqrt b ∧ β ≤ 0.001 ∧
      W ≤ (3.29 * (8 + 0.001) * x) /
        ((1 - 0.335) * (log (8*x)) ^ (1 - 0.335 + 0.335 * log 0.335 : ℝ)) ∧
      sqrt (3*b/8) * sqrt x * ((1 - 2*β)/(1+β)) * (2/3 - W/(x*(1-2*β))) ≤
        ({n : ℕ | n ≤ x ∧ Even (Nat.partitionNumber n)}.ncard : ℝ)

theorem main : H1 → H2 → type_of% @PartitionParity.bellaiche_nicolas.even_explicit := by
  intro hNicolas hSupport x hx
  by_cases hx₃ : x < 3
  · exact small_x hx hx₃
  have h₃ : 3 ≤ x := le_of_not_gt hx₃
  by_cases hL : log (log x) ≤ 16.4
  · exact medium_x hL (hNicolas x h₃)
  obtain ⟨d, hlead, hβ, hW, hconv⟩ := hSupport x h₃ (le_of_not_ge hL)
  exact (tail_x h₃ (sqrt_nonneg _) (le_of_not_ge hL) hlead hβ hW).trans hconv

end OMA.R_PartitionParity_bellaiche_nicolas_even_explicit_R1
