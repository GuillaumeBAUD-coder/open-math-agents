import FormalConjectures.ErdosProblems.«654»

-- Reduction Erdos654.erdos_654.variants.general_position.R1 of Erdős problem 654 (general position)
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 654 in general position: reduction to sets with almost the maximal number of isosceles triangles

Let `A` be `n` points in the plane with no three on a line. For a point `x` let `d(x)` be the
number of distinct distances from `x`, and for an ordered pair `(y, z)` of distinct points let
`b(y, z)` be the number of `x` in `A` with `|x - y| = |x - z|` (the apexes of the pair).

* All apexes of `(y, z)` lie on the perpendicular bisector of `y z`, so `b(y, z) ≤ 2` (`H2`,
  elementary).
* If the distance classes around `x` have sizes `s_1, …, s_d`, then `x` is an apex of
  `∑ s_i (s_i - 1)` ordered pairs, and `s (s - 1) ≥ 4 s - 6` for every natural `s`, so `x` is an
  apex of at least `4 (n - 1) - 6 d(x)` ordered pairs (`point_count`).
* Counting the incidences (apex, pair) in two ways (`global_count`):
  `4 n (n - 1) + D ≤ 2 n (n - 1) + 6 ∑ d(x)`, where `D` is the number of *deficient* ordered pairs,
  those with at most one apex in `A`.

So if `D ≥ δ n²`, some point has more than `(1/3 + δ/12) n` distinct distances once `n > 4/δ`.
The target is therefore reduced to the point sets with fewer than `δ n²` deficient pairs, that is,
to the sets in which all but `δ n²` of the pairs have exactly two apexes (`H1`).

`H1` is the target restricted to these near-extremal sets. It is a special case of the target
(the target implies `H1` at once), so the reduction is downward, and it is an equivalence:
it does not make the problem easier outside the near-extremal case, it only removes every other
case. The circle condition is not used in `main`; it stays available in `H1`.
-/

namespace OMA.R_Erdos654_erdos_654_variants_general_position_R1

open Filter Finset EuclideanGeometry

/-- The target for near-extremal sets: those where fewer than `δ n²` ordered pairs `(y, z)` have at
most one point of `A` on their perpendicular bisector. Open. -/
def H1 : Prop :=
  ∃ δ > (0 : ℝ), ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², #A = n →
    InGeneralPosition (A : Set ℝ²) →
    (#(A.offDiag.filter fun p => #(A.filter fun x => dist x p.1 = dist x p.2) ≤ 1) : ℝ)
      < δ * (n : ℝ) ^ 2 →
    ∃ x ∈ A, (1 / 3 + c) * (n : ℝ) < (distinctDistancesFrom A x : ℝ)

/-- With no three points on a line, at most two points of `A` are equidistant from two given
distinct points (they lie on the perpendicular bisector). Elementary. -/
def H2 : Prop :=
  ∀ A : Finset ℝ², NonTrilinear (A : Set ℝ²) → ∀ y ∈ A, ∀ z ∈ A, y ≠ z →
    #(A.filter fun x => dist x y = dist x z) ≤ 2

lemma four_mul_le (s : ℕ) : 4 * s ≤ (s * s - s) + 6 := by
  rcases Nat.lt_or_ge s 6 with h | h
  · interval_cases s <;> simp
  · have h6 : 6 * s ≤ s * s := Nat.mul_le_mul_right s h
    omega

/-- A point `x` of `A` is an apex of at least `4 (n - 1) - 6 d(x)` ordered pairs. -/
lemma point_count (A : Finset ℝ²) (x : ℝ²) (hx : x ∈ A) :
    4 * (#A - 1) ≤ #(A.offDiag.filter fun p => dist x p.1 = dist x p.2)
      + 6 * distinctDistancesFrom A x := by
  classical
  unfold distinctDistancesFrom
  have hE : #(A.erase x) = #A - 1 := Finset.card_erase_of_mem hx
  have h1 : #(A.erase x) = ∑ t ∈ (A.erase x).image (fun y => dist y x),
      #((A.erase x).filter fun y => dist y x = t) :=
    Finset.card_eq_sum_card_image _ _
  have hmaps : ∀ p ∈ A.offDiag.filter (fun p => dist x p.1 = dist x p.2),
      dist p.1 x ∈ (A.erase x).image (fun y => dist y x) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_offDiag] at hp
    obtain ⟨⟨h1A, h2A, hne⟩, hd⟩ := hp
    refine Finset.mem_image.2 ⟨p.1, Finset.mem_erase.2 ⟨?_, h1A⟩, rfl⟩
    intro h
    rw [h, dist_self] at hd
    exact hne (h.trans (dist_eq_zero.1 hd.symm))
  have h2 := Finset.card_eq_sum_card_fiberwise hmaps
  have h3 : ∀ t ∈ (A.erase x).image (fun y => dist y x),
      #(((A.erase x).filter fun y => dist y x = t).offDiag)
        ≤ #((A.offDiag.filter fun p => dist x p.1 = dist x p.2).filter
            fun p => dist p.1 x = t) := by
    intro t _
    apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_erase] at hp ⊢
    obtain ⟨⟨⟨_, h1A⟩, h1t⟩, ⟨⟨_, h2A⟩, h2t⟩, hne⟩ := hp
    refine ⟨⟨⟨h1A, h2A, hne⟩, ?_⟩, h1t⟩
    rw [dist_comm x p.1, dist_comm x p.2, h1t, h2t]
  rw [← hE, h1, h2, Finset.mul_sum]
  calc ∑ t ∈ (A.erase x).image (fun y => dist y x),
        4 * #((A.erase x).filter fun y => dist y x = t)
      ≤ ∑ t ∈ (A.erase x).image (fun y => dist y x),
        (#((A.offDiag.filter fun p => dist x p.1 = dist x p.2).filter
            fun p => dist p.1 x = t) + 6) := by
        apply Finset.sum_le_sum
        intro t ht
        have h4 := four_mul_le #((A.erase x).filter fun y => dist y x = t)
        have h5 := h3 t ht
        rw [Finset.offDiag_card] at h5
        omega
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
        congr!

/-- Double counting of the pairs (apex, ordered pair). -/
lemma global_count (A : Finset ℝ²)
    (hb : ∀ p ∈ A.offDiag, #(A.filter fun x => dist x p.1 = dist x p.2) ≤ 2) :
    4 * (#A * (#A - 1))
        + #(A.offDiag.filter fun p => #(A.filter fun x => dist x p.1 = dist x p.2) ≤ 1)
      ≤ 2 * (#A * #A - #A) + 6 * ∑ x ∈ A, distinctDistancesFrom A x := by
  have h1 : ∑ _x ∈ A, 4 * (#A - 1)
      ≤ ∑ x ∈ A, (#(A.offDiag.filter fun p => dist x p.1 = dist x p.2)
        + 6 * distinctDistancesFrom A x) :=
    Finset.sum_le_sum fun x hx => point_count A x hx
  have h2 : ∑ x ∈ A, #(A.offDiag.filter fun p => dist x p.1 = dist x p.2)
      = ∑ p ∈ A.offDiag, #(A.filter fun x => dist x p.1 = dist x p.2) := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h3 : ∑ p ∈ A.offDiag, #(A.filter fun x => dist x p.1 = dist x p.2)
      + #(A.offDiag.filter fun p => #(A.filter fun x => dist x p.1 = dist x p.2) ≤ 1)
      ≤ ∑ _p ∈ A.offDiag, 2 := by
    rw [Finset.card_filter (fun p : ℝ² × ℝ² => #(A.filter fun x => dist x p.1 = dist x p.2) ≤ 1),
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have := hb p hp
    split_ifs <;> omega
  rw [Finset.sum_const, smul_eq_mul, Finset.offDiag_card] at h3
  rw [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib, h2, ← Finset.mul_sum] at h1
  have e : 4 * (#A * (#A - 1)) = #A * (4 * (#A - 1)) := by ring
  rw [e]
  omega

theorem main : H1 → H2 → type_of% @Erdos654.erdos_654.variants.general_position := by
  intro h1 h2
  obtain ⟨δ, hδ, c₁, hc₁, hev⟩ := h1
  refine ⟨min c₁ (δ / 12), lt_min hc₁ (by positivity), ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / δ)
  filter_upwards [hev, eventually_gt_atTop N] with n hn hnN A hA hgp
  have hnR : (4 / δ) < (n : ℝ) := hN.trans (by exact_mod_cast hnN)
  have hn0 : (0 : ℝ) < n := lt_trans (by positivity) hnR
  have hδn : 4 < δ * (n : ℝ) := by
    rw [div_lt_iff₀ hδ] at hnR
    linarith
  by_cases hD : (#(A.offDiag.filter fun p =>
      #(A.filter fun x => dist x p.1 = dist x p.2) ≤ 1) : ℝ) < δ * (n : ℝ) ^ 2
  · obtain ⟨x, hx, hlt⟩ := hn A hA hgp hD
    refine ⟨x, hx, lt_of_le_of_lt ?_ hlt⟩
    have : min c₁ (δ / 12) ≤ c₁ := min_le_left _ _
    nlinarith
  · by_contra hcon
    push Not at hcon hD
    have hb : ∀ p ∈ A.offDiag, #(A.filter fun x => dist x p.1 = dist x p.2) ≤ 2 := by
      intro p hp
      rw [Finset.mem_offDiag] at hp
      exact h2 A hgp.1 p.1 hp.1 p.2 hp.2.1 hp.2.2
    have hg := global_count A hb
    have hsum : ((∑ x ∈ A, distinctDistancesFrom A x : ℕ) : ℝ)
        ≤ (n : ℝ) * ((1 / 3 + δ / 12) * (n : ℝ)) := by
      rw [Nat.cast_sum]
      calc ∑ x ∈ A, (distinctDistancesFrom A x : ℝ)
          ≤ ∑ _x ∈ A, (1 / 3 + δ / 12) * (n : ℝ) := by
            apply Finset.sum_le_sum
            intro x hx
            refine (hcon x hx).trans ?_
            have : min c₁ (δ / 12) ≤ δ / 12 := min_le_right _ _
            nlinarith
        _ = _ := by rw [Finset.sum_const, hA, nsmul_eq_mul]
    have hn1 : 1 ≤ n := by
      have : (0 : ℝ) < n := hn0
      exact_mod_cast this
    rw [hA] at hg
    have hgR : (4 * (n * (n - 1)) + #(A.offDiag.filter fun p =>
        #(A.filter fun x => dist x p.1 = dist x p.2) ≤ 1) : ℝ)
        ≤ 2 * (n * n - n) + 6 * ((∑ x ∈ A, distinctDistancesFrom A x : ℕ) : ℝ) := by
      have hle : n ≤ n * n := Nat.le_mul_self n
      have := (Nat.cast_le (α := ℝ)).2 hg
      push_cast [Nat.cast_sub hn1, Nat.cast_sub hle] at this
      push_cast
      linarith
    nlinarith

end OMA.R_Erdos654_erdos_654_variants_general_position_R1
