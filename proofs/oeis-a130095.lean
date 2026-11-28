import OMAStatements.S_oeis_a130095
import Mathlib

namespace OMA.P130095

open OMA.S_oeis_a130095 Filter

lemma term_lower (n : ℕ) (hn : 1 ≤ n) : Nat.fib (2 * n - 1) ≤ term n := by
  unfold term
  exact Finset.single_le_sum (f := fun d => Nat.fib (2 * d - 1)) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors_self n (by omega))

lemma term_upper (n : ℕ) (hn : 1 ≤ n) : term n ≤ Nat.fib (2 * n - 1) + Nat.fib (n + 1) := by
  unfold term
  rw [← Nat.cons_self_properDivisors (by omega : n ≠ 0), Finset.sum_cons]
  apply Nat.add_le_add_left
  have h1 : ∑ d ∈ n.properDivisors, Nat.fib (2 * d - 1)
      = ∑ j ∈ n.properDivisors.image (fun d => 2 * d - 1), Nat.fib j := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    have hx' := Nat.pos_of_mem_properDivisors hx
    have hy' := Nat.pos_of_mem_properDivisors hy
    simp only at hxy
    omega
  rw [h1]
  have h2 : n.properDivisors.image (fun d => 2 * d - 1) ⊆ Finset.range n := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨d, hd, rfl⟩ := hj
    rw [Nat.mem_properDivisors] at hd
    obtain ⟨⟨c, hc⟩, hlt⟩ := hd
    rw [Finset.mem_range]
    have hc2 : 2 ≤ c := by
      rcases c with _ | _ | c
      · simp at hc
        omega
      · simp at hc
        omega
      · omega
    have h2d : 2 * d ≤ n := by
      rw [hc]
      calc 2 * d = d * 2 := by ring
        _ ≤ d * c := Nat.mul_le_mul_left d hc2
    omega
  calc ∑ j ∈ n.properDivisors.image (fun d => 2 * d - 1), Nat.fib j
        ≤ ∑ j ∈ Finset.range n, Nat.fib j := Finset.sum_le_sum_of_subset h2
    _ ≤ Nat.fib (n + 1) := by
        rw [Nat.fib_succ_eq_succ_sum n]
        omega

/-- The normalized terms. -/
noncomputable def u (n : ℕ) : ℝ := (term n : ℝ) / (Nat.fib (2 * n - 1) : ℝ)

lemma u_bounds (n : ℕ) (hn : 5 ≤ n) : 1 ≤ u n ∧ u n ≤ 1 + 2 / (n : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have hl := term_lower (m + 1) (by omega)
  have hu := term_upper (m + 1) (by omega)
  rw [e] at hl hu
  have hsq : Nat.fib (m + 1) ^ 2 ≤ Nat.fib (2 * m + 1) := by
    rw [Nat.fib_two_mul_add_one]
    omega
  have hf2 : Nat.fib (m + 1 + 1) ≤ 2 * Nat.fib (m + 1) := by
    rw [Nat.fib_add_two]
    have hmono : Nat.fib m ≤ Nat.fib (m + 1) := Nat.fib_mono (by omega)
    omega
  have hself : m + 1 ≤ Nat.fib (m + 1) := Nat.le_fib_self hn
  have hFpos : (0 : ℝ) < (Nat.fib (2 * m + 1) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hfpos : (0 : ℝ) < (Nat.fib (m + 1) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hnpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hlR : (Nat.fib (2 * m + 1) : ℝ) ≤ (term (m + 1) : ℝ) := by exact_mod_cast hl
  have huR : (term (m + 1) : ℝ) ≤ (Nat.fib (2 * m + 1) : ℝ) + (Nat.fib (m + 1 + 1) : ℝ) := by
    exact_mod_cast hu
  have hsqR : (Nat.fib (m + 1) : ℝ) ^ 2 ≤ (Nat.fib (2 * m + 1) : ℝ) := by exact_mod_cast hsq
  have hf2R : (Nat.fib (m + 1 + 1) : ℝ) ≤ 2 * (Nat.fib (m + 1) : ℝ) := by exact_mod_cast hf2
  have hselfR : ((m + 1 : ℕ) : ℝ) ≤ (Nat.fib (m + 1) : ℝ) := by exact_mod_cast hself
  unfold u
  rw [e]
  constructor
  · rw [le_div_iff₀ hFpos]
    linarith
  · rw [div_le_iff₀ hFpos]
    have h3 : 2 / ((m + 1 : ℕ) : ℝ) * (Nat.fib (2 * m + 1) : ℝ) ≥ 2 * (Nat.fib (m + 1) : ℝ) := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hnpos]
      nlinarith
    linarith

lemma u_tendsto : Tendsto u atTop (nhds 1) := by
  have hup : Tendsto (fun n : ℕ => (1 : ℝ) + 2 / (n : ℝ)) atTop (nhds 1) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).const_add (1 : ℝ)
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · exact (eventually_ge_atTop 5).mono (fun n hn => (u_bounds n hn).1)
  · exact (eventually_ge_atTop 5).mono (fun n hn => (u_bounds n hn).2)

end OMA.P130095

theorem OMA.solution : type_of% @OMA.S_oeis_a130095.main := by
  have hu := OMA.P130095.u_tendsto
  have hu' : Filter.Tendsto (fun n : ℕ => OMA.P130095.u (n - 1)) Filter.atTop (nhds 1) :=
    hu.comp (Filter.tendsto_atTop_atTop.2 (fun b => ⟨b + 1, fun n hn => by omega⟩))
  have hg := tendsto_fib_succ_div_fib_atTop
  have t2 : Filter.Tendsto (fun n : ℕ => 2 * n - 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 (fun b => ⟨b + 2, fun n hn => by omega⟩)
  have t3 : Filter.Tendsto (fun n : ℕ => 2 * n - 3) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 (fun b => ⟨b + 3, fun n hn => by omega⟩)
  have hg2 := hg.comp t2
  have hg3 := hg.comp t3
  have hall := (hu.div hu' one_ne_zero).mul (hg2.mul hg3)
  have hval : (1 : ℝ) / 1 * (Real.goldenRatio * Real.goldenRatio) = Real.goldenRatio ^ 2 := by ring
  rw [hval] at hall
  refine hall.congr' ?_
  refine (Filter.eventually_ge_atTop 3).mono (fun n hn => ?_)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [Function.comp_apply, Pi.div_apply, Pi.mul_apply, OMA.P130095.u]
  have e1 : 2 * (m + 3) - 1 = 2 * m + 5 := by omega
  have e2 : m + 3 - 1 = m + 2 := by omega
  have e3 : 2 * (m + 2) - 1 = 2 * m + 3 := by omega
  have e4 : 2 * (m + 3) - 2 = 2 * m + 4 := by omega
  have e5 : 2 * (m + 3) - 3 = 2 * m + 3 := by omega
  rw [e1, e2, e3, e4, e5]
  have hA : (0 : ℝ) < (Nat.fib (2 * m + 5) : ℝ) := by exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hB : (0 : ℝ) < (Nat.fib (2 * m + 4) : ℝ) := by exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hC : (0 : ℝ) < (Nat.fib (2 * m + 3) : ℝ) := by exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hT : (0 : ℝ) < (OMA.S_oeis_a130095.term (m + 2) : ℝ) := by
    have h := OMA.P130095.term_lower (m + 2) (by omega)
    rw [e3] at h
    have h' : (Nat.fib (2 * m + 3) : ℝ) ≤ (OMA.S_oeis_a130095.term (m + 2) : ℝ) := by exact_mod_cast h
    linarith
  field_simp
