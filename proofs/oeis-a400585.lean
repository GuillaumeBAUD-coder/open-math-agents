import OMAStatements.S_oeis_a400585
import Mathlib

namespace OMA.OeisA400585

open Filter Topology

private lemma choose3_mul_six (m : ℕ) : 6 * (m + 1).choose 3 = (m + 1) * m * (m - 1) := by
  induction m with
  | zero => decide
  | succ k ih =>
    have h1 : (k + 2).choose 3 = (k + 1).choose 3 + (k + 1).choose 2 := by
      rw [Nat.choose_succ_succ]; ring
    have h2 : 2 * (k + 1).choose 2 = (k + 1) * k := by
      rw [Nat.choose_two_right]
      exact Nat.mul_div_cancel' (Nat.even_mul_pred_self (k + 1)).two_dvd
    cases k with
    | zero => decide
    | succ r =>
      have hs1 : r + 1 + 1 - 1 = r + 1 := by omega
      have hs2 : r + 1 - 1 = r := by omega
      rw [hs1]
      rw [hs2] at ih
      nlinarith

private lemma choose3_le_cube (m : ℕ) : 6 * (m + 1).choose 3 ≤ m ^ 3 := by
  rw [choose3_mul_six]
  cases m with
  | zero => simp
  | succ k =>
    have : k + 1 - 1 = k := by omega
    rw [this]
    nlinarith

private lemma choose3_real (m : ℕ) :
    6 * (((m + 1).choose 3 : ℕ) : ℝ) = (m : ℝ) ^ 3 - (m : ℝ) := by
  cases m with
  | zero =>
    have h0 : (1 : ℕ).choose 3 = 0 := by decide
    simp [h0]
  | succ k =>
    have h := choose3_mul_six (k + 1)
    have hsub : k + 1 - 1 = k := by omega
    rw [hsub] at h
    have hR : (6 * (k + 2).choose 3 : ℝ) = ((k + 2) * (k + 1) * k : ℝ) := by exact_mod_cast h
    push_cast at hR ⊢
    linarith

private lemma sum_a_eq (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), OMA.S_oeis_a400585.a k =
      ∑ j ∈ Finset.range (n + 1), if Odd j then (n / j + 1).choose 3 else 0 := by
  induction n with
  | zero =>
    simp [OMA.S_oeis_a400585.a]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hprev :
        ∑ j ∈ Finset.range (n + 1), (if Odd j then (n / j + 1).choose 3 else 0) =
          ∑ j ∈ Finset.range (n + 2), (if Odd j then (n / j + 1).choose 3 else 0) := by
      symm
      rw [Finset.sum_range_succ]
      have hdiv : n / (n + 1) = 0 := Nat.div_eq_of_lt (Nat.lt_succ_self n)
      have hch : (1 : ℕ).choose 3 = 0 := by decide
      simp [hdiv, hch]
    have ha :
        OMA.S_oeis_a400585.a (n + 1) =
          ∑ j ∈ Finset.range (n + 2),
            if j ∣ n + 1 then (if Odd j then ((n + 1) / j).choose 2 else 0) else 0 := by
      unfold OMA.S_oeis_a400585.a
      rw [← Finset.sum_filter (p := fun j => j ∣ n + 1)]
      congr 1
      ext j
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_range, ne_eq,
        Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, and_true]
      constructor
      · intro h
        exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.succ_pos n) h), h⟩
      · exact fun h => h.2
    rw [hprev, ha, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases hj : Odd j
    · by_cases hd : j ∣ n + 1
      · have hdiv : (n + 1) / j = n / j + 1 := by
          have := @Nat.succ_div n j
          simp only [hd, ↓reduceIte] at this
          exact this
        simp only [hj, hd, ↓reduceIte, hdiv]
        have hch : (n / j + 1 + 1).choose 3 = (n / j + 1).choose 2 + (n / j + 1).choose 3 :=
          Nat.choose_succ_succ (n / j + 1) 2
        omega
      · have hdiv : (n + 1) / j = n / j := by
          have := @Nat.succ_div n j
          simp only [hd, ↓reduceIte, add_zero] at this
          exact this
        simp only [hj, hd, ↓reduceIte, add_zero, hdiv]
    · simp [hj]

private noncomputable def termF (n j : ℕ) : ℝ :=
  if Odd j then (((n / j + 1).choose 3 : ℕ) : ℝ) / (n : ℝ) ^ 3 else 0

private noncomputable def boundG (j : ℕ) : ℝ :=
  if Odd j then (1 / 6 : ℝ) * ((j : ℝ) ^ 3)⁻¹ else 0

private lemma tsum_termF (n : ℕ) :
    ∑' j : ℕ, termF n j = (∑ k ∈ Finset.range (n + 1), (OMA.S_oeis_a400585.a k : ℝ)) / (n : ℝ) ^ 3 := by
  have hsupp : ∀ j ∉ Finset.range (n + 1), termF n j = 0 := by
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    have hdiv : n / j = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hj)
    have hch : (1 : ℕ).choose 3 = 0 := by decide
    simp [termF, hdiv, hch]
  rw [tsum_eq_sum hsupp]
  have hsumN := sum_a_eq n
  have hsumR : (∑ k ∈ Finset.range (n + 1), (OMA.S_oeis_a400585.a k : ℝ)) =
      ∑ j ∈ Finset.range (n + 1), (if Odd j then (((n / j + 1).choose 3 : ℕ) : ℝ) else 0) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hsumN
    push_cast at this
    simpa [apply_ite (Nat.cast : ℕ → ℝ)] using this
  rw [hsumR, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro j _
  by_cases hj : Odd j <;> simp [termF, hj]

private lemma summable_inv_cube : Summable (fun j : ℕ => ((j : ℝ) ^ 3)⁻¹) := by
  exact Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 3)

private lemma summable_boundG : Summable boundG := by
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (summable_inv_cube.mul_left (1 / 6))
  · by_cases hj : Odd j
    · simp only [boundG, hj, ↓reduceIte]; positivity
    · simp only [boundG, hj, ↓reduceIte]; exact le_rfl
  · by_cases hj : Odd j
    · simp only [boundG, hj, ↓reduceIte]; exact le_rfl
    · simp only [boundG, hj, ↓reduceIte]; positivity

private lemma norm_termF_le (n j : ℕ) : ‖termF n j‖ ≤ boundG j := by
  by_cases hj : Odd j
  · simp only [termF, boundG, hj, ↓reduceIte]
    rw [Real.norm_of_nonneg (by positivity)]
    rcases n with _ | n
    · simp
    · have hjpos : (0 : ℝ) < (j : ℝ) := by
        rcases hj with ⟨k, rfl⟩
        positivity
      have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have h1 : 6 * ((((n + 1) / j + 1).choose 3 : ℕ) : ℝ) ≤ (((n + 1) / j : ℕ) : ℝ) ^ 3 := by
        exact_mod_cast choose3_le_cube ((n + 1) / j)
      have h2 : (((n + 1) / j : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / (j : ℝ) := by
        rw [le_div_iff₀ hjpos]
        exact_mod_cast Nat.div_mul_le_self (n + 1) j
      have h3 : (((n + 1) / j : ℕ) : ℝ) ^ 3 ≤ (((n + 1 : ℕ) : ℝ) / (j : ℝ)) ^ 3 := by
        exact pow_le_pow_left₀ (by positivity) h2 3
      have h4 : 6 * ((((n + 1) / j + 1).choose 3 : ℕ) : ℝ) ≤
          ((n + 1 : ℕ) : ℝ) ^ 3 / (j : ℝ) ^ 3 := by
        rw [← div_pow]; linarith
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 3)]
      have h5 : (1 / 6 : ℝ) * ((j : ℝ) ^ 3)⁻¹ * ((n + 1 : ℕ) : ℝ) ^ 3 =
          (((n + 1 : ℕ) : ℝ) ^ 3 / (j : ℝ) ^ 3) / 6 := by ring
      linarith
  · simp [termF, boundG, hj]

private lemma tendsto_termF (j : ℕ) : Tendsto (fun n => termF n j) atTop (nhds (boundG j)) := by
  by_cases hj : Odd j
  · have hjpos_nat : 0 < j := by rcases hj with ⟨k, rfl⟩; omega
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hjpos_nat
    have hdiv_tend : Tendsto (fun n : ℕ => ((n / j : ℕ) : ℝ) / (n : ℝ)) atTop (nhds ((j : ℝ)⁻¹)) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (g := fun n : ℕ => (j : ℝ)⁻¹ - (n : ℝ)⁻¹)
        (h := fun _ : ℕ => (j : ℝ)⁻¹) ?_ tendsto_const_nhds ?_ ?_
      · have h0 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
          tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
        simpa using tendsto_const_nhds.sub h0
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hlt : (n : ℝ) - (j : ℝ) < ((n / j : ℕ) : ℝ) * (j : ℝ) := by
          have h1 : n < (n / j + 1) * j := by
            have := Nat.lt_div_mul_add hjpos_nat (a := n)
            linarith
          have h1R : (n : ℝ) < (((n / j : ℕ) : ℝ) + 1) * (j : ℝ) := by exact_mod_cast h1
          linarith
        have hge : (n : ℝ) / (j : ℝ) - 1 ≤ ((n / j : ℕ) : ℝ) := by
          rw [sub_le_iff_le_add, div_le_iff₀ hjpos]; linarith
        rw [le_div_iff₀ hnpos]
        have : ((j : ℝ)⁻¹ - (n : ℝ)⁻¹) * (n : ℝ) = (n : ℝ) / (j : ℝ) - 1 := by
          field_simp
        linarith
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hle : ((n / j : ℕ) : ℝ) * (j : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast Nat.div_mul_le_self n j
        rw [div_le_iff₀ hnpos]
        have : (j : ℝ)⁻¹ * (n : ℝ) = (n : ℝ) / (j : ℝ) := by ring
        rw [this, le_div_iff₀ hjpos]
        exact hle
    have hrem_tend : Tendsto (fun n : ℕ => ((n / j : ℕ) : ℝ) / (n : ℝ) ^ 3) atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (g := fun _ : ℕ => (0 : ℝ))
        (h := fun n : ℕ => (n : ℝ)⁻¹) tendsto_const_nhds
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop) ?_ ?_
      · filter_upwards with n; positivity
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hdiv_le : ((n / j : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.div_le_self n j
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 3)]
        have : (n : ℝ)⁻¹ * (n : ℝ) ^ 3 = (n : ℝ) ^ 2 := by field_simp
        rw [this]
        nlinarith
    have hcomb : Tendsto (fun n : ℕ =>
        (1 / 6 : ℝ) * ((((n / j : ℕ) : ℝ) / (n : ℝ)) ^ 3 - ((n / j : ℕ) : ℝ) / (n : ℝ) ^ 3))
        atTop (nhds ((1 / 6 : ℝ) * (((j : ℝ)⁻¹) ^ 3 - 0))) := by
      exact ((hdiv_tend.pow 3).sub hrem_tend).const_mul (1 / 6)
    have hlim_eq : (1 / 6 : ℝ) * (((j : ℝ)⁻¹) ^ 3 - 0) = boundG j := by
      simp [boundG, hj, inv_pow]
    rw [hlim_eq] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnne : (n : ℝ) ≠ 0 := by positivity
    simp only [termF, hj, ↓reduceIte]
    have hc := choose3_real (n / j)
    field_simp
    linarith
  · simp [termF, boundG, hj]

private lemma tsum_boundG : ∑' j : ℕ, boundG j = 7 * OMA.S_oeis_a400585.zetaThree / 48 := by
  let g : ℕ → ℝ := fun j => ((j : ℝ) ^ 3)⁻¹
  have hs : Summable g := summable_inv_cube
  have hev_eq : (fun k : ℕ => g (2 * k)) = (fun k : ℕ => (1 / 8 : ℝ) * g k) := by
    ext k; simp only [g]; push_cast; ring
  have hev_summ : Summable (fun k : ℕ => g (2 * k)) := by
    rw [hev_eq]; exact hs.mul_left (1 / 8)
  have hodd_summ : Summable (fun k : ℕ => g (2 * k + 1)) :=
    hs.comp_injective (fun a b h => by omega)
  have hsplit : ∑' k : ℕ, g (2 * k) + ∑' k : ℕ, g (2 * k + 1) = ∑' j : ℕ, g j :=
    tsum_even_add_odd hev_summ hodd_summ
  have hev_val : ∑' k : ℕ, g (2 * k) = (1 / 8 : ℝ) * OMA.S_oeis_a400585.zetaThree := by
    rw [hev_eq, tsum_mul_left]; rfl
  have hodd_val : ∑' k : ℕ, g (2 * k + 1) = (7 / 8 : ℝ) * OMA.S_oeis_a400585.zetaThree := by
    have hz : ∑' j : ℕ, g j = OMA.S_oeis_a400585.zetaThree := rfl
    linarith
  let gOdd : ℕ → ℝ := fun j => if Odd j then g j else 0
  have h2_eq : (fun k : ℕ => gOdd (2 * k)) = fun _ => 0 := by
    ext k; simp [gOdd, Nat.not_odd_iff_even]
  have h3_eq : (fun k : ℕ => gOdd (2 * k + 1)) = fun k => g (2 * k + 1) := by
    ext k; simp [gOdd]
  have h2 : Summable (fun k : ℕ => gOdd (2 * k)) := by rw [h2_eq]; exact summable_zero
  have h3 : Summable (fun k : ℕ => gOdd (2 * k + 1)) := by rw [h3_eq]; exact hodd_summ
  have hodd_eq : ∑' j : ℕ, gOdd j = ∑' k : ℕ, g (2 * k + 1) := by
    rw [← tsum_even_add_odd h2 h3, h2_eq, h3_eq, tsum_zero, zero_add]
  have hbg : boundG = fun j => (1 / 6 : ℝ) * gOdd j := by
    ext j; by_cases hj : Odd j <;> simp [boundG, gOdd, g, hj]
  rw [hbg, tsum_mul_left, hodd_eq, hodd_val]
  ring

end OMA.OeisA400585

theorem OMA.solution : type_of% @OMA.S_oeis_a400585.main := by
  have hdom : Filter.Tendsto (fun n : ℕ => ∑' j : ℕ, OMA.OeisA400585.termF n j)
      Filter.atTop (nhds (∑' j : ℕ, OMA.OeisA400585.boundG j)) :=
    tendsto_tsum_of_dominated_convergence
      OMA.OeisA400585.summable_boundG
      OMA.OeisA400585.tendsto_termF
      (Filter.Eventually.of_forall OMA.OeisA400585.norm_termF_le)
  rw [OMA.OeisA400585.tsum_boundG] at hdom
  refine hdom.congr ?_
  intro n
  exact OMA.OeisA400585.tsum_termF n
