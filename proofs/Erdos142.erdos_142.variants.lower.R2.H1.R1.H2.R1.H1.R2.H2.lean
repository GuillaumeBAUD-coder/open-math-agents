import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R2
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Lift each term to S in [1, N]. Consecutive integer differences agree mod p and lie in
-- (-N, N) with 2N < p, so they are all one integer D, nonzero since d is nonzero in ZMod p.
-- Read the lifted progression forwards (D > 0) or backwards (D < 0).

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R2.H2 := by
  unfold OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R2.H2
  intro k N p hk hp S hS ⟨a, d, hd, h⟩
  have hx : ∀ i : ℕ, ∃ n : ℕ, i < k → n ∈ S ∧ (n : ZMod p) = a + (i : ZMod p) * d := by
    intro i
    by_cases hi : i < k
    · obtain ⟨n, hn, e⟩ := Finset.mem_image.mp (h i hi)
      exact ⟨n, fun _ => ⟨hn, e⟩⟩
    · exact ⟨0, fun h' => absurd h' hi⟩
  choose x hx using hx
  have hb : ∀ i < k, 1 ≤ x i ∧ x i ≤ N := fun i hi => Finset.mem_Icc.mp (hS (hx i hi).1)
  have step : ∀ i, i + 1 < k → ((x (i+1) : ℤ) - x i) = (x 1 : ℤ) - x 0 := by
    intro i hi
    have e1 := (hx (i+1) hi).2
    have e0 := (hx i (by omega)).2
    have f1 := (hx 1 (by omega)).2
    have f0 := (hx 0 (by omega)).2
    have hc : (((x (i+1) : ℤ) - x i : ℤ) : ZMod p) = (((x 1 : ℤ) - x 0 : ℤ) : ZMod p) := by
      simp only [Int.cast_sub, Int.cast_natCast]
      rw [e1, e0, f1, f0]; push_cast; ring
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hc
    have := Int.eq_zero_of_abs_lt_dvd hc ?_
    · linarith
    · have := hb (i+1) hi; have := hb i (by omega); have := hb 1 (by omega)
      have := hb 0 (by omega)
      rw [abs_lt]; constructor <;> push_cast <;> omega
  have hD : ∀ i < k, (x i : ℤ) = x 0 + i * ((x 1 : ℤ) - x 0) := by
    intro i hi
    induction i with
    | zero => simp
    | succ j ih =>
      have h1 := step j hi
      have h2 := ih (by omega)
      push_cast
      linear_combination h1 + h2
  have hD0 : (x 1 : ℤ) - x 0 ≠ 0 := by
    intro h0
    have h10 : x 1 = x 0 := by omega
    have e := (hx 1 (by omega)).2
    have f := (hx 0 (by omega)).2
    rw [h10] at e
    have := e.symm.trans f
    simp only [Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, add_zero] at this
    exact hd (by linear_combination this)
  rcases lt_or_gt_of_ne hD0 with hneg | hpos
  · refine ⟨x (k-1), x 0 - x 1, by omega, fun i hi => ?_⟩
    have h1 := hD (k-1) (by omega)
    have h2 := hD (k-1-i) (by omega)
    have c1 : ((k-1:ℕ):ℤ) = k - 1 := by omega
    have c2 : ((k-1-i:ℕ):ℤ) = k - 1 - i := by omega
    rw [c1] at h1
    rw [c2] at h2
    have hle : x 1 ≤ x 0 := by omega
    have h3 : (x (k-1) : ℤ) + i * ((x 0 : ℤ) - x 1) = x (k-1-i) := by
      linear_combination h1 - h2
    rw [← Nat.cast_sub hle] at h3
    have e : x (k-1) + i * (x 0 - x 1) = x (k-1-i) := by exact_mod_cast h3
    rw [e]; exact (hx _ (by omega)).1
  · refine ⟨x 0, x 1 - x 0, by omega, fun i hi => ?_⟩
    have h3 : (x 0 : ℤ) + i * ((x 1 : ℤ) - x 0) = x i := (hD i hi).symm
    rw [← Nat.cast_sub (by omega)] at h3
    have e : x 0 + i * (x 1 - x 0) = x i := by exact_mod_cast h3
    rw [e]; exact (hx i hi).1
