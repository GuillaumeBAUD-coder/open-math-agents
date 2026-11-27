import FormalConjectures.ErdosProblems.«297»

/-! Tilt the independent subset choices by their reciprocal mass. On the fiber of rational
sum x the tilt is constant, so the combinatorial loss is exactly its probability. -/
namespace OMA.R_Erdos297_erdos_297_variants_general_R1
open Filter Real Finset Erdos297
open scoped Topology

/-- Calibration of the reciprocal mass fixes the critical parameter. -/
def H1 : Prop := ∀ x : ℚ, 0 < x → ∃! l : ℝ, massIntegral l = x

/-- Riemann-sum limit of the tilted partition function, with entropy in bits. -/
def H2 : Prop := ∀ (x : ℚ) (l : ℝ), 0 < x → massIntegral l = x →
    Tendsto (fun N : ℕ => l * x + log (∏ n ∈ Icc 1 N, (1 + exp (-l * (N : ℝ) / n))) / N) atTop
      (𝓝 (exponentOf x * log 2))

/-- Under the calibrated independent choices the exact rational fiber has subexponential cost. -/
def H3 : Prop := ∀ (x : ℚ) (l : ℝ), 0 < x → massIntegral l = x →
    ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, exp (-η * N) ≤ ((∑ A ∈ ((Icc 1 N).powerset.filter fun (A : Finset ℕ) => (∑ n ∈ A, (1 : ℚ) / n) = x), ∏ n ∈ A, exp (-l * N / n)) / (∏ n ∈ Icc 1 N, (1 + exp (-l * (N : ℝ) / n))))

theorem main : H1 → H2 → H3 → type_of% @Erdos297.erdos_297.variants.general := by
  intro h1 h2 h3 x hx
  let partition (l : ℝ) (N : ℕ) : ℝ :=
    ∏ n ∈ Icc 1 N, (1 + exp (-l * N / n))

  let prob (l : ℝ) (x : ℚ) (N : ℕ) : ℝ :=
    (∑ A ∈ ((Icc 1 N).powerset.filter fun (A : Finset ℕ) => (∑ n ∈ A, (1 : ℚ) / n) = x),
      ∏ n ∈ A, exp (-l * N / n)) / partition l N

  have part_pos (l : ℝ) (N : ℕ) : 0 < partition l N :=
    prod_pos fun _ _ => by positivity

  have prob_le_one (l : ℝ) (x : ℚ) (N : ℕ) : prob l x N ≤ 1 := by
    apply (div_le_iff₀ (part_pos l N)).2
    rw [one_mul]
    dsimp only [partition]
    rw [prod_one_add]
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intros
    positivity

  have exact_fiber (l : ℝ) (x : ℚ) (N : ℕ) :
      prob l x N = (count x N : ℝ) * exp (-l * N * x) / partition l N := by
    unfold prob count
    congr 1
    calc
      _ = ∑ _A ∈ ((Icc 1 N).powerset.filter fun (A : Finset ℕ) => (∑ n ∈ A, (1 : ℚ) / n) = x),
            exp (-l * N * x) := by
        apply sum_congr rfl
        intro A hA
        have hs : (∑ n ∈ A, (1 : ℝ) / n) = x := by
          have hrat : (∑ n ∈ A, (1 : ℚ) / n) = x := (mem_filter.1 hA).2
          simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using congrArg (fun t : ℚ => (t : ℝ)) hrat
        rw [← Real.exp_sum, ← hs, mul_sum]
        simp [div_eq_mul_inv]
      _ = _ := by simp
  refine ⟨h1 x hx, ?_⟩
  obtain ⟨l, hl, _⟩ := h1 x hx
  have hp : Tendsto (fun N : ℕ => log (prob l x N) / N) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [h3 x l hx hl (ε/2) (by positivity), eventually_gt_atTop 0] with N hN hNp
    have hpos : 0 < prob l x N := (exp_pos _).trans_le hN
    have hcast : (0 : ℝ) < N := by exact_mod_cast hNp
    have hlo := Real.log_le_log (exp_pos _) hN
    rw [Real.log_exp] at hlo
    have hhi := Real.log_nonpos hpos.le (prob_le_one l x N)
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ⟨(lt_div_iff₀ hcast).2 (by nlinarith), lt_of_le_of_lt (div_nonpos_of_nonpos_of_nonneg hhi hcast.le) hε⟩
  have hpart : Tendsto (fun N : ℕ => l * x + log (partition l N) / N) atTop (𝓝 (exponentOf x * log 2)) := h2 x l hx hl
  have hlim := (hpart.add hp).div_const (log 2)
  have htwo : log (2 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
  simp only [add_zero, mul_div_cancel_right₀ _ htwo] at hlim
  apply hlim.congr'
  filter_upwards [h3 x l hx hl 1 zero_lt_one, eventually_gt_atTop 0] with N hN hn
  have hpos : 0 < prob l x N := (exp_pos _).trans_le hN
  rw [exact_fiber] at hpos ⊢
  have hc : (0 : ℝ) < count x N := by
    by_contra! h
    have hzero : (count x N : ℝ) = 0 := le_antisymm h (by positivity)
    simp [hzero] at hpos
  rw [log_div (mul_pos hc (exp_pos _)).ne' (part_pos l N).ne',
    log_mul hc.ne' (exp_pos _).ne', log_exp, logb]
  have hn' : (N : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  <;> ring

end OMA.R_Erdos297_erdos_297_variants_general_R1
