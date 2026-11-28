import FormalConjectures.Wikipedia.EllipticCurveRank

/-!
# The density of rank zero and one from two 5-Selmer estimates

Reduction of EllipticCurveRank.RatEllipticCurve._08375_le_density_rank_zero_one.
Credit: @yuka30240

Write s for the 5-Selmer dimension minus the rational 5-torsion dimension.
The Kummer exact sequence expresses s as the Mordell-Weil rank plus the
dimension of the 5-torsion in the Tate-Shafarevich group. In particular
the rank is at most s, even on curves with rational 5-torsion.

Bhargava and Shankar, arXiv:1312.7859, Theorem 1 gives an upper bound of
6 for the average of 5^s. Their Theorems 6 and 39 give lower density
at least 11/40 for odd s: on a family of density at least 55%, the two
root numbers are equidistributed, and the negative sign gives odd s.
-/

namespace OMA.R_EllipticCurveRank_RatEllipticCurve__08375_le_density_rank_zero_one_R1

open EllipticCurveRank EllipticCurveRank.RatEllipticCurve Filter
open scoped Classical

/-- The mean upper bound from the average size of the full 5-Selmer group. -/
def H1 : Prop :=
  let s (E : RatEllipticCurve) := E.rank +
    Nat.log 5 (Nat.card {x : E.toWeierstrass.tateShafarevich // 5 • x = 0})
  ∀ ε : ℝ, 0 < ε → ∀ᶠ H : ℕ in atTop,
    (∑ᶠ E ∈ heightLE H, (5 : ℝ) ^ s E) / (heightLE H).ncard ≤ 6 + ε

/-- The odd-parity lower bound from the root-number family and the parity theorem. -/
def H2 : Prop :=
  let s (E : RatEllipticCurve) := E.rank +
    Nat.log 5 (Nat.card {x : E.toWeierstrass.tateShafarevich // 5 • x = 0})
  ∀ ε : ℝ, 0 < ε → ∀ᶠ H : ℕ in atTop,
    11 / 40 - ε ≤ ({E ∈ heightLE H | Odd (s E)}.ncard : ℝ) / (heightLE H).ncard

lemma finite_height (H : ℕ) : (heightLE H).Finite := by
  apply Set.Finite.of_injOn (f := fun E : RatEllipticCurve ↦ (E.A, E.B))
    (t := Set.Icc (-(H : ℤ)) H ×ˢ Set.Icc (-(H : ℤ)) H)
  · intro E hE
    obtain ⟨ha, hb⟩ := max_le_iff.mp (show E.naiveHeight ≤ H from hE)
    change 4 * E.A.natAbs ^ 3 ≤ H at ha
    change 27 * E.B.natAbs ^ 2 ≤ H at hb
    have := Nat.le_self_pow (a := E.A.natAbs) (by decide : 3 ≠ 0)
    have := Nat.le_self_pow (a := E.B.natAbs) (by decide : 2 ≠ 0)
    change (-(H : ℤ) ≤ E.A ∧ E.A ≤ H) ∧ (-(H : ℤ) ≤ E.B ∧ E.B ≤ H)
    omega
  · rintro ⟨a, b, _, _⟩ _ ⟨c, d, _, _⟩ _ h
    cases h
    rfl
  · exact (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)

/-- The three smallest Selmer sizes are 1, 5, and 25. Odd dimension
at least three contributes at least 125, covering both penalties. -/
lemma point_bound (r s : ℕ) (hrs : r ≤ s) :
    25 + 4 * (if Odd s then 1 else 0 : ℝ) ≤
      (5 : ℝ) ^ s + 24 * (if r = 0 ∨ r = 1 then 1 else 0) := by
  by_cases small : s ≤ 2
  · interval_cases s <;> interval_cases r <;> norm_num at *
  · have h : (5 : ℝ) ^ 3 ≤ 5 ^ s := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at h
    split_ifs <;> linarith

lemma count_bound (H : ℕ) (s : RatEllipticCurve → ℕ) (hrs : ∀ E, E.rank ≤ s E) :
    25 * ((heightLE H).ncard : ℝ) + 4 * {E ∈ heightLE H | Odd (s E)}.ncard ≤
      (∑ᶠ E ∈ heightLE H, (5 : ℝ) ^ s E) +
        24 * {E ∈ heightLE H | E.rank = 0 ∨ E.rank = 1}.ncard := by
  classical
  let F := (finite_height H).toFinset
  have sep (p : RatEllipticCurve → Prop) [DecidablePred p] :
      (F.filter p).card = {E ∈ heightLE H | p E}.ncard := by
    have h : (↑(F.filter p) : Set RatEllipticCurve) = {E ∈ heightLE H | p E} := by
      ext E
      simp [F]
    rw [← h]
    exact (Set.ncard_coe_finset _).symm
  have h := Finset.sum_le_sum (s := F) (fun E _ ↦ point_bound E.rank (s E) (hrs E))
  rw [finsum_mem_eq_finite_toFinset_sum _ (finite_height H)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const,
    nsmul_eq_mul] at h
  rw [sep (fun E ↦ Odd (s E)), sep (fun E ↦ E.rank = 0 ∨ E.rank = 1)] at h
  rw [Set.ncard_eq_toFinset_card (heightLE H) (finite_height H)]
  simpa only [F, mul_comm (25 : ℝ)] using h

theorem main : H1 → H2 → type_of% @EllipticCurveRank.RatEllipticCurve._08375_le_density_rank_zero_one := by
  classical
  intro hmean hodd
  let s (E : RatEllipticCurve) := E.rank +
    Nat.log 5 (Nat.card {x : E.toWeierstrass.tateShafarevich // 5 • x = 0})
  let good (H : ℕ) := {E ∈ heightLE H | E.rank = 0 ∨ E.rank = 1}
  let ratio (H : ℕ) := ((good H).ncard : ℝ) / (heightLE H).ncard
  change 0.8375 ≤ liminf ratio atTop
  have upper : atTop.IsBoundedUnder (· ≤ ·) ratio := by
    refine ⟨1, ?_⟩
    change ∀ᶠ H : ℕ in atTop, ratio H ≤ 1
    filter_upwards with H
    have h : (good H).ncard ≤ (heightLE H).ncard :=
      Set.ncard_le_ncard (Set.sep_subset (heightLE H) _) (finite_height H)
    exact div_le_one_of_le₀ (Nat.cast_le.mpr h) (Nat.cast_nonneg _)
  have lower : atTop.IsBoundedUnder (· ≥ ·) ratio := by
    refine ⟨0, ?_⟩
    change ∀ᶠ H : ℕ in atTop, 0 ≤ ratio H
    filter_upwards with H
    dsimp [ratio]
    positivity
  apply (le_liminf_iff upper.isCoboundedUnder_ge lower).2
  intro y hy
  let ε := min (0.8375 - y) (1 / 10 : ℝ)
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεy : ε ≤ 0.8375 - y := min_le_left _ _
  have hεt : ε ≤ 1 / 10 := min_le_right _ _
  filter_upwards [hmean ε hε, hodd ε hε] with H hm ho
  let N : ℝ := (heightLE H).ncard
  let O : ℝ := {E ∈ heightLE H | Odd (s E)}.ncard
  let M : ℝ := ∑ᶠ E ∈ heightLE H, (5 : ℝ) ^ s E
  change M / N ≤ 6 + ε at hm
  change 11 / 40 - ε ≤ O / N at ho
  have hN : 0 < N := by
    have hn : 0 ≤ N := by dsimp [N]; positivity
    rcases hn.eq_or_lt with hz | hp
    · rw [← hz, div_zero] at ho
      linarith
    · exact hp
  have hc : 25 * N + 4 * O ≤ M + 24 * ((good H).ncard : ℝ) :=
    count_bound H s fun E ↦ Nat.le_add_right _ _
  have hc' := div_le_div_of_nonneg_right hc hN.le
  rw [add_div, add_div, mul_div_assoc, div_self hN.ne', mul_one,
    mul_div_assoc, mul_div_assoc] at hc'
  change y < ((good H).ncard : ℝ) / N
  linarith

end OMA.R_EllipticCurveRank_RatEllipticCurve__08375_le_density_rank_zero_one_R1
