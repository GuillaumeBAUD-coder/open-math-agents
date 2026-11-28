import OMAStatements.S_oeis_a383377
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

-- Problem: A383377: G.f. satisfies A(x) = Sum_{n>=0} x^n * abs(1/A(x)^n).
-- Upstream: statements/oeis-a383377.lean (declaration OMA.S_oeis_a383377.main)
-- Credit: @Dolcruz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.A383377

lemma zmod2_neg (x : ZMod 2) : -x = x := by
  fin_cases x <;> rfl

lemma abs_cast_zmod2 (z : ℤ) : ((|z| : ℤ) : ZMod 2) = (z : ZMod 2) := by
  rcases le_or_gt 0 z with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, Int.cast_neg, zmod2_neg]

lemma even_of_zmod2_eq_zero (z : ℤ) (h : (z : ZMod 2) = 0) : Even z := by
  have hd : (2 : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z 2).mp h
  rcases hd with ⟨k, rfl⟩
  exact ⟨k, by ring⟩

end OMA.A383377

theorem OMA.solution : type_of% @OMA.S_oeis_a383377.main := by
  intro A hA n hn
  let B : PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2)) (A : PowerSeries ℤ)
  let Binv : PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2)) (↑A⁻¹ : PowerSeries ℤ)
  have hBBinv : B * Binv = 1 := by
    have hmul : (A : PowerSeries ℤ) * (↑A⁻¹ : PowerSeries ℤ) = 1 := Units.mul_inv A
    dsimp only [B, Binv]
    rw [← map_mul, hmul, map_one]
  have hBcoeff : ∀ k : ℕ, B.coeff k = ∑ j ∈ Finset.range (k + 1), (Binv ^ j).coeff (k - j) := by
    intro k
    have hk := congrArg (Int.cast : ℤ → ZMod 2) (hA k)
    have hL : ((PowerSeries.coeff k (A : PowerSeries ℤ) : ℤ) : ZMod 2) = B.coeff k := by
      simp [B]
    rw [hL, Int.cast_sum] at hk
    rw [hk]
    apply Finset.sum_congr rfl
    intro j _
    rw [OMA.A383377.abs_cast_zmod2]
    change (Int.castRingHom (ZMod 2)) (PowerSeries.coeff (k - j) ((↑A⁻¹ : PowerSeries ℤ) ^ j)) =
      PowerSeries.coeff (k - j) (Binv ^ j)
    rw [← PowerSeries.coeff_map, map_pow]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hm1 : 1 ≤ m := by omega
  have hshift : B.coeff (m + 1) = (B * Binv).coeff m := by
    rw [PowerSeries.coeff_mul]
    have h1 : (∑ p ∈ Finset.antidiagonal m, B.coeff p.1 * Binv.coeff p.2) =
        ∑ p ∈ Finset.antidiagonal m,
          ∑ j ∈ Finset.range (p.1 + 1), (Binv ^ j).coeff (p.1 - j) * Binv.coeff p.2 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [hBcoeff p.1, Finset.sum_mul]
    rw [h1, Finset.sum_sigma']
    have h2 : B.coeff (m + 1) =
        ∑ j ∈ Finset.range (m + 1), (Binv ^ (j + 1)).coeff (m - j) := by
      rw [hBcoeff (m + 1), Finset.sum_range_succ']
      have h0 : (Binv ^ 0).coeff (m + 1 - 0) = 0 := by
        simp [PowerSeries.coeff_one]
      rw [h0, add_zero]
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.add_sub_add_right]
    rw [h2]
    have h3 : (∑ j ∈ Finset.range (m + 1), (Binv ^ (j + 1)).coeff (m - j)) =
        ∑ j ∈ Finset.range (m + 1),
          ∑ q ∈ Finset.antidiagonal (m - j), (Binv ^ j).coeff q.1 * Binv.coeff q.2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ, PowerSeries.coeff_mul]
    rw [h3, Finset.sum_sigma']
    refine Finset.sum_bij (fun x _ => ⟨(x.1 + x.2.1, x.2.2), x.1⟩) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal] at hx ⊢
      omega
    · intro x hx y hy hxy
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal] at hx hy
      simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at hxy
      cases x with | mk j1 q1 =>
      cases y with | mk j2 q2 =>
      cases q1 with | mk a1 b1 =>
      cases q2 with | mk a2 b2 =>
      simp only at hx hy hxy
      rcases hxy with ⟨⟨hsum, hb⟩, hj⟩
      subst hj
      subst hb
      have ha : a1 = a2 := by omega
      subst ha
      rfl
    · intro y hy
      simp only [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.mem_range] at hy
      refine ⟨⟨y.2, (y.1.1 - y.2, y.1.2)⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal]
        omega
      · cases y with | mk p j =>
        cases p with | mk a b =>
        simp only at hy ⊢
        congr 1
        ext <;> omega
    · intro x _
      simp only [Nat.add_sub_cancel_left]
  have hzero : B.coeff (m + 1) = 0 := by
    rw [hshift, hBBinv, PowerSeries.coeff_one, if_neg (by omega)]
  apply OMA.A383377.even_of_zmod2_eq_zero
  simpa [B] using hzero
