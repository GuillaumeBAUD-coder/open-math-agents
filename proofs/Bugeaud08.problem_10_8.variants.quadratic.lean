import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_8

-- Problem: p-adic Littlewood conjecture, quadratic case (de Mathan and Teulie 2004)
-- Upstream: formal-conjectures FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_8.lean:59 (declaration Bugeaud08.problem_10_8.variants.quadratic)

/-!
# The p-adic Littlewood conjecture for quadratic irrationals

Write the minimal polynomial as `X^2 + b X + c` and put `θ = d (2ξ + b)` with `d` the denominator
of the discriminant, so `θ^2 = D` is a non-square positive integer. For each `k`, Pell's equation
`x^2 - D p^(2k) y^2 = 1` has a solution with `y ≠ 0`; with `N = p^k |y|` the number `θ N` lies within
`1 / (|θ| N)` of an integer. Taking `q = 2 d den(b) N` gives `‖q ξ‖ ≤ den(b) / (|θ| N)` and
`|q|_p ≤ p^(-k)`, so `q |q|_p ‖q ξ‖ ≤ 2 d den(b)^2 / (|θ| p^k)`, which tends to zero.
-/

open Polynomial

namespace OMAQuadLittlewood
lemma quad_coeffs (ξ : ℝ) (hξ : (minpoly ℚ ξ).natDegree = 2) :
    ∃ b c : ℚ, ξ ^ 2 + (b : ℝ) * ξ + (c : ℝ) = 0 := by
  have hint : IsIntegral ℚ ξ := by
    by_contra hc; rw [minpoly.eq_zero hc] at hξ; simp at hξ
  have hm := minpoly.monic hint
  have h0 := minpoly.aeval ℚ ξ
  rw [aeval_eq_sum_range, hξ] at h0
  have h2 : (minpoly ℚ ξ).coeff 2 = 1 := by
    have := hm.leadingCoeff; rwa [leadingCoeff, hξ] at this
  refine ⟨(minpoly ℚ ξ).coeff 1, (minpoly ℚ ξ).coeff 0, ?_⟩
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h2] at h0
  simp only [Algebra.smul_def, eq_ratCast] at h0
  push_cast at h0
  linear_combination h0

lemma quad_irr (ξ : ℝ) (hξ : (minpoly ℚ ξ).natDegree = 2) (r : ℚ) : ξ ≠ r := by
  intro h
  have := minpoly.eq_X_sub_C ℝ r
  rw [eq_ratCast, ← h] at this
  rw [this] at hξ
  simp at hξ

lemma near_int (θ : ℝ) (hθ : θ ≠ 0) (x : ℤ) (N : ℕ) (hN : 1 ≤ N)
    (h : (x : ℝ) ^ 2 - θ ^ 2 * (N : ℝ) ^ 2 = 1) :
    ∃ n : ℤ, |θ * N - n| ≤ 1 / (|θ| * N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 < |θ| * N := mul_pos (abs_pos.mpr hθ) hN'
  set u := (x : ℝ) - θ * N
  set v := (x : ℝ) + θ * N
  have huv : u * v = 1 := by simp only [u, v]; linear_combination h
  have hsum : 2 * (|θ| * N) ≤ |u| + |v| := by
    have : v - u = 2 * (θ * N) := by simp only [u, v]; ring
    have h1 : |v - u| ≤ |u| + |v| := by
      calc |v - u| ≤ |v| + |u| := abs_sub _ _
        _ = |u| + |v| := add_comm _ _
    rw [this, abs_mul, abs_mul, abs_of_pos hN'] at h1
    simpa using h1
  have habs : |u| * |v| = 1 := by rw [← abs_mul, huv]; simp
  rcases le_total (|θ| * N) |v| with hv | hv
  · refine ⟨x, ?_⟩
    have : |θ * N - x| = |u| := by rw [abs_sub_comm]
    rw [this, le_div_iff₀ hpos]
    nlinarith [abs_nonneg u]
  · have hu : |θ| * N ≤ |u| := by
      by_contra hc; have hc := not_le.mp hc
      nlinarith [abs_nonneg u, abs_nonneg v]
    refine ⟨-x, ?_⟩
    have : |θ * N - ((-x : ℤ) : ℝ)| = |v| := by
      push_cast; simp only [v]; rw [show θ * N - -(x : ℝ) = x + θ * N by ring]
    rw [this, le_div_iff₀ hpos]
    nlinarith [abs_nonneg v]

theorem main (ξ : ℝ) (p : ℕ) (hp : p.Prime)
    (hξ : (minpoly ℚ ξ).natDegree = 2) :
    sInf {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧
      x = q * padicNorm p q * distToNearestInt (q * ξ)} = 0 := by
  have := Fact.mk hp
  obtain ⟨b, c, hbc⟩ := quad_coeffs ξ hξ
  have hirr := quad_irr ξ hξ
  set δ : ℚ := b ^ 2 - 4 * c with hδ
  set d : ℕ := δ.den with hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast δ.pos
  set D : ℤ := δ.num * d with hD
  set θ : ℝ := (d : ℝ) * (2 * ξ + b) with hθ
  have hδd : (δ : ℝ) * d = δ.num := by exact_mod_cast Rat.mul_den_eq_num δ
  have hθsq : θ ^ 2 = D := by
    have : θ ^ 2 = (d : ℝ) * ((δ : ℝ) * d) := by
      simp only [hθ, hδ]; push_cast; linear_combination (4 * (d:ℝ) ^ 2) * hbc
    rw [this, hδd, hD]; push_cast; ring
  have hξθ : ξ = (θ / d - b) / 2 := by
    simp only [hθ]; field_simp; ring
  have hθrat : ∀ r : ℚ, θ ≠ r := by
    intro r hr
    apply hirr ((r / d - b) / 2)
    rw [hξθ, hr]; push_cast; ring
  have hθ0 : θ ≠ 0 := by simpa using hθrat 0
  have hθpos : 0 < |θ| := abs_pos.mpr hθ0
  clear_value θ D d δ
  have hbden : (0 : ℝ) < b.den := by exact_mod_cast b.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  -- the set
  set S := {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧
      x = q * padicNorm p q * distToNearestInt (q * ξ)} with hS
  have hnonneg : ∀ x ∈ S, 0 ≤ x := by
    rintro x ⟨q, -, rfl⟩
    have h1 : (0 : ℝ) ≤ (padicNorm p (q : ℚ) : ℝ) := by exact_mod_cast padicNorm.nonneg _
    have h2 : 0 ≤ distToNearestInt (q * ξ) := abs_nonneg _
    positivity
  have hne : S.Nonempty := ⟨_, 1, le_rfl, rfl⟩
  have hbdd : BddBelow S := ⟨0, fun x hx => hnonneg x hx⟩
  apply le_antisymm _ (le_csInf hne hnonneg)
  apply le_of_forall_pos_le_add
  intro ε hε
  rw [zero_add]
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 * d * (b.den : ℝ) ^ 2 / (|θ| * ε)) hp1
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
  -- Pell
  have hDpos : 0 < D := by
    have : (0 : ℝ) < D := by rw [← hθsq]; positivity
    exact_mod_cast this
  have hnsq : ¬ IsSquare (D * (p : ℤ) ^ (2 * k)) := by
    rintro ⟨m, hm⟩
    have hm' : ((|θ| * (p : ℝ) ^ k)) ^ 2 = (|(m : ℝ)|) ^ 2 := by
      rw [mul_pow, sq_abs, sq_abs, hθsq, ← pow_mul, mul_comm k 2]
      have : ((D * (p : ℤ) ^ (2 * k) : ℤ) : ℝ) = ((m * m : ℤ) : ℝ) := by rw [hm]
      push_cast at this; rw [this]; ring
    have hm2 : |θ| * (p : ℝ) ^ k = |(m : ℝ)| :=
      (sq_eq_sq₀ (by positivity) (abs_nonneg _)).mp hm'
    have hθabs : |θ| = (((((|m| : ℤ) : ℚ) / ((p : ℚ) ^ k)) : ℚ) : ℝ) := by
      push_cast; rw [← hm2]; field_simp
    rcases abs_choice θ with h | h
    · exact hθrat _ (by rw [← h, hθabs])
    · apply hθrat (-(((|m| : ℤ) : ℚ) / ((p : ℚ) ^ k)))
      have : θ = -|θ| := by rw [h]; ring
      rw [this, hθabs]; push_cast; ring
  obtain ⟨x, y, hxy, hy⟩ := Pell.exists_of_not_isSquare (mul_pos hDpos (pow_pos (by exact_mod_cast hp.pos) _)) hnsq
  set N : ℕ := p ^ k * y.natAbs with hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (Int.natAbs_ne_zero.mpr hy))
  have hNR : (N : ℝ) = (p : ℝ) ^ k * |(y : ℝ)| := by
    simp only [hN]; push_cast; simp [Nat.cast_natAbs]
  have hxN : (x : ℝ) ^ 2 - θ ^ 2 * (N : ℝ) ^ 2 = 1 := by
    rw [hNR, mul_pow, sq_abs, hθsq]
    have : ((x ^ 2 - D * (p : ℤ) ^ (2 * k) * y ^ 2 : ℤ) : ℝ) = 1 := by rw [hxy]; simp
    push_cast at this; rw [← this, pow_mul]; ring
  obtain ⟨n, hn⟩ := near_int θ hθ0 x N hN1 hxN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set q : ℕ := 2 * d * b.den * N with hq
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (by
    have h1 : 0 < d := hd ▸ δ.pos
    have h2 := b.pos
    have h3 : 0 < N := hN1
    positivity)
  refine csInf_le_of_le hbdd ⟨q, hq1, rfl⟩ ?_
  -- bound each factor
  have hpad : (padicNorm p (q : ℚ) : ℝ) ≤ ((p : ℝ) ^ k)⁻¹ := by
    have hdvd : ((p ^ k : ℕ) : ℤ) ∣ ((q : ℕ) : ℤ) := by
      apply Int.natCast_dvd_natCast.mpr
      simp only [hq, hN]
      exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
    have h := padicNorm.dvd_iff_norm_le.mp hdvd
    have h' : (padicNorm p (q : ℚ) : ℝ) ≤ (((p : ℚ) ^ (-(k : ℤ)) : ℚ) : ℝ) := by
      exact_mod_cast h
    simpa [zpow_neg] using h'
  have hdist : distToNearestInt (q * ξ) ≤ b.den / (|θ| * N) := by
    set m : ℤ := b.den * n - d * N * b.num
    have hqξ : (q : ℝ) * ξ - m = b.den * (θ * N - n) := by
      have hb : (b : ℝ) * b.den = b.num := by exact_mod_cast Rat.mul_den_eq_num b
      have h1 : (q:ℝ) * ξ = b.den * (θ * N) - d * N * ((b : ℝ) * b.den) := by
        rw [hξθ]; simp only [hq]; push_cast; field_simp
      rw [h1, hb]; simp only [m]; push_cast; ring
    calc distToNearestInt (q * ξ) ≤ |(q : ℝ) * ξ - m| := round_le _ _
      _ = b.den * |θ * N - n| := by rw [hqξ, abs_mul, abs_of_pos hbden]
      _ ≤ b.den * (1 / (|θ| * N)) := by gcongr
      _ = b.den / (|θ| * N) := by ring
  have hpn : (0:ℝ) ≤ (padicNorm p (q : ℚ) : ℝ) := by exact_mod_cast padicNorm.nonneg _
  have hdn : 0 ≤ distToNearestInt (q * ξ) := abs_nonneg _
  have hqR : (q : ℝ) = 2 * d * b.den * N := by simp only [hq]; push_cast; ring
  calc (q : ℝ) * (padicNorm p (q : ℚ) : ℝ) * distToNearestInt (q * ξ)
      ≤ (q : ℝ) * ((p : ℝ) ^ k)⁻¹ * (b.den / (|θ| * N)) := by gcongr
    _ = 2 * d * (b.den : ℝ) ^ 2 / (|θ| * (p : ℝ) ^ k) := by
      rw [hqR]; field_simp
    _ ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ (by positivity)] at hk
      nlinarith

end OMAQuadLittlewood

theorem OMA.solution : type_of% @Bugeaud08.problem_10_8.variants.quadratic := by
  intro ξ p hp hξ
  exact OMAQuadLittlewood.main ξ p hp hξ
