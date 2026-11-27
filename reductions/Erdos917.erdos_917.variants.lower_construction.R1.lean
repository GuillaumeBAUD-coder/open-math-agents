import FormalConjectures.ErdosProblems.«917»

/-!
Reduction R1 of Erdos Problem 917, lower construction (Toft 1970 / Stiebitz 1987).
Route and draft by agent w1b; compiled and repaired by agent a4k.
The four hypotheses H1 (odd cycles 3-critical), H2 (Dirac join), H3 (Toft D(A1,A2) is 4-critical),
H4 (5-critical T(A,C)) imply the target via explicit families with exact arithmetic.
-/
-- Route and draft by agent w1b; repaired and compiled by agent a4k.
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos917_erdos_917_variants_lower_construction_R1

open Filter

/-- Odd cycles are `3`-critical: `C_b` has `b` vertices and `b` edges. -/
def H1 : Prop := ∀ b : ℕ, Odd b → 3 ≤ b → (∃ G : SimpleGraph (Fin (b)), Erdos917.IsKCritical G (3) ∧ G.edgeSet.ncard = (b))

/-- Dirac's join: the join of a `k₁`-critical and a `k₂`-critical graph is `(k₁ + k₂)`-critical. -/
def H2 : Prop := ∀ k₁ k₂ n₁ n₂ e₁ e₂ : ℕ, 3 ≤ k₁ → 3 ≤ k₂ → (∃ G : SimpleGraph (Fin (n₁)), Erdos917.IsKCritical G (k₁) ∧ G.edgeSet.ncard = (e₁)) → (∃ G : SimpleGraph (Fin (n₂)), Erdos917.IsKCritical G (k₂) ∧ G.edgeSet.ncard = (e₂)) →
  (∃ G : SimpleGraph (Fin (n₁ + n₂)), Erdos917.IsKCritical G (k₁ + k₂) ∧ G.edgeSet.ncard = (e₁ + e₂ + n₁ * n₂))

/-- Toft's graph: take `3`-critical graphs `A₁`, `A₂`, independent copies `B₁` of `V(A₁)` and `B₂`
of `V(A₂)`, a perfect matching between `Aᵢ` and `Bᵢ`, and all edges between `B₁` and `B₂`.
The result is `4`-critical. -/
def H3 : Prop := ∀ n₁ n₂ e₁ e₂ : ℕ, (∃ G : SimpleGraph (Fin (n₁)), Erdos917.IsKCritical G (3) ∧ G.edgeSet.ncard = (e₁)) → (∃ G : SimpleGraph (Fin (n₂)), Erdos917.IsKCritical G (3) ∧ G.edgeSet.ncard = (e₂)) →
  (∃ G : SimpleGraph (Fin (2 * n₁ + 2 * n₂)), Erdos917.IsKCritical G (4) ∧ G.edgeSet.ncard = (e₁ + e₂ + n₁ + n₂ + n₁ * n₂))

/-- Toft's `5`-critical graph: take a `4`-critical graph `A`, an independent copy `B` of `V(A)` with
a perfect matching between `A` and `B`, a `3`-critical graph `C`, and all edges between `B` and
`C`. The result is `5`-critical. -/
def H4 : Prop := ∀ n₁ n₂ e₁ e₂ : ℕ, (∃ G : SimpleGraph (Fin (n₁)), Erdos917.IsKCritical G (4) ∧ G.edgeSet.ncard = (e₁)) → (∃ G : SimpleGraph (Fin (n₂)), Erdos917.IsKCritical G (3) ∧ G.edgeSet.ncard = (e₂)) →
  (∃ G : SimpleGraph (Fin (2 * n₁ + n₂)), Erdos917.IsKCritical G (5) ∧ G.edgeSet.ncard = (e₁ + e₂ + n₁ + n₁ * n₂))

/-- Joining `r` further odd cycles `C_b` to a `k₀`-critical graph. -/
lemma iter (h1 : H1) (h2 : H2) {b : ℕ} (hb : Odd b) (hb3 : 3 ≤ b) {k₀ a e : ℕ} (hk₀ : 3 ≤ k₀)
    (h : (∃ G : SimpleGraph (Fin (a)), Erdos917.IsKCritical G (k₀) ∧ G.edgeSet.ncard = (e))) : ∀ r : ℕ, ∃ E : ℕ, (∃ G : SimpleGraph (Fin (a + r * b)), Erdos917.IsKCritical G (k₀ + 3 * r) ∧ G.edgeSet.ncard = (E)) ∧
      2 * E + r * b ^ 2 = 2 * e + 2 * r * b + 2 * a * r * b + r ^ 2 * b ^ 2 := by
  intro r
  induction r with
  | zero =>
    refine ⟨e, ?_, by ring⟩
    have h' : a + 0 * b = a := by simp
    have h2 : k₀ + 3 * 0 = k₀ := by simp
    rw [h', h2]
    exact h
  | succ r ih =>
    obtain ⟨E, hE, hE2⟩ := ih
    have hj := h2 (k₀ + 3 * r) 3 (a + r * b) b E b (by omega) le_rfl hE (h1 b hb hb3)
    refine ⟨E + b + (a + r * b) * b, ?_, ?_⟩
    · have e1 : k₀ + 3 * (r + 1) = k₀ + 3 * r + 3 := by ring
      have e2 : a + (r + 1) * b = a + r * b + b := by ring
      rw [e1, e2]
      exact hj
    · nlinarith [hE2]

/-- From a critical graph with enough edges to the target inequality. -/
lemma finish {k n E : ℕ} (D : ℝ) (hD : 0 < D)
    (hD' : (((k / 3 : ℕ) : ℝ) + Erdos917.delta k) = D) (hP : (∃ G : SimpleGraph (Fin (n)), Erdos917.IsKCritical G (k) ∧ G.edgeSet.ncard = (E)))
    (hineq : (D - 1) * (n : ℝ) ^ 2 ≤ D * (2 * (E : ℝ))) :
    1 / 2 * (1 - 1 / (((k / 3 : ℕ) : ℝ) + Erdos917.delta k)) * (n : ℝ) ^ 2 ≤
      (Erdos917.f k n : ℝ) := by
  obtain ⟨G, hG, hGE⟩ := hP
  have hle : (E : ℝ) ≤ (Erdos917.f k n : ℝ) := by
    have := Erdos917.edgeSet_ncard_le_f hG
    rw [hGE] at this
    exact_mod_cast this
  refine le_trans ?_ hle
  rw [hD']
  have hD0 : D ≠ 0 := hD.ne'
  have e : 1 / 2 * (1 - 1 / D) * (n : ℝ) ^ 2 - E =
      ((D - 1) * (n : ℝ) ^ 2 - D * (2 * (E : ℝ))) / (2 * D) := by
    field_simp
  have h0 : 1 / 2 * (1 - 1 / D) * (n : ℝ) ^ 2 - E ≤ 0 := by
    rw [e]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

theorem main : H1 → H2 → H3 → H4 →
    type_of% @Erdos917.erdos_917.variants.lower_construction := by
  intro h1 h2 h3 h4 k hk
  rw [Filter.frequently_atTop]
  intro N
  -- `k = 3 * (r + 1) + k % 3` and `j = N + 1` is the size parameter
  obtain ⟨r, hr⟩ : ∃ r : ℕ, k / 3 = r + 1 := ⟨k / 3 - 1, by omega⟩
  have hrR : (((k / 3 : ℕ) : ℝ)) = (r : ℝ) + 1 := by rw [hr, Nat.cast_add, Nat.cast_one]
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  set j : ℕ := N + 1 with hj
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with hm | hm | hm
  · -- `k = 3t`: the join of `t = r + 1` cycles of length `b = 2j + 1`
    have hb : Odd (2 * j + 1) := ⟨j, rfl⟩
    have hb3 : 3 ≤ 2 * j + 1 := by omega
    obtain ⟨E, hE, hE2⟩ := iter h1 h2 hb hb3 le_rfl (h1 _ hb hb3) r
    have hk3 : 3 + 3 * r = k := by omega
    rw [hk3] at hE
    have hE2R : (2 : ℝ) * E + r * (2 * j + 1) ^ 2 =
        2 * (2 * j + 1) + 2 * r * (2 * j + 1) + 2 * (2 * j + 1) * r * (2 * j + 1) +
          r ^ 2 * (2 * j + 1) ^ 2 := by exact_mod_cast hE2
    refine ⟨2 * j + 1 + r * (2 * j + 1), by omega, ?_⟩
    have hdelta : Erdos917.delta k = 0 := by simp [Erdos917.delta, hm]
    refine finish ((r : ℝ) + 1) (by positivity) (by rw [hrR, hdelta, add_zero]) hE ?_
    have h2E : (2 : ℝ) * E = 2 * (r + 1) * (2 * j + 1) + r * (r + 1) * (2 * j + 1) ^ 2 := by
      linarith [hE2R]
    rw [h2E]
    push_cast
    have : ((r : ℝ) + 1) * (2 * (r + 1) * (2 * j + 1) + r * (r + 1) * (2 * j + 1) ^ 2) -
        ((r : ℝ) + 1 - 1) * (2 * j + 1 + r * (2 * j + 1)) ^ 2 =
          2 * ((r : ℝ) + 1) ^ 2 * (2 * j + 1) := by ring
    have hpos : (0 : ℝ) ≤ 2 * ((r : ℝ) + 1) ^ 2 * (2 * j + 1) := by positivity
    linarith
  · -- `k = 3t + 1`: Toft's graph on `4q` vertices, `q = 4j + 1`, joined with `r = t - 1` cycles
    -- of length `b = 14j + 3`
    have hq : Odd (4 * j + 1) := ⟨2 * j, by ring⟩
    have hq3 : 3 ≤ 4 * j + 1 := by omega
    have hb : Odd (14 * j + 3) := ⟨7 * j + 1, by ring⟩
    have hb3 : 3 ≤ 14 * j + 3 := by omega
    have hC := h1 _ hq hq3
    have hT := h3 _ _ _ _ hC hC
    obtain ⟨E, hE, hE2⟩ := iter h1 h2 hb hb3 (by norm_num : 3 ≤ 4) hT r
    have hk3 : 4 + 3 * r = k := by omega
    rw [hk3] at hE
    have hE2R : (2 : ℝ) * E + r * (14 * j + 3) ^ 2 =
        2 * ((4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) * (4 * j + 1)) +
          2 * r * (14 * j + 3) +
          2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) * r * (14 * j + 3) +
          r ^ 2 * (14 * j + 3) ^ 2 := by exact_mod_cast hE2
    refine ⟨2 * (4 * j + 1) + 2 * (4 * j + 1) + r * (14 * j + 3), by omega, ?_⟩
    have hdelta : Erdos917.delta k = 1 / 7 := by simp [Erdos917.delta, hm]
    refine finish ((r : ℝ) + 1 + 1 / 7) (by positivity) (by rw [hrR, hdelta]) hE ?_
    have h2E : (2 : ℝ) * E =
        2 * ((4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) * (4 * j + 1)) +
          2 * r * (14 * j + 3) +
          2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) * r * (14 * j + 3) +
          r ^ 2 * (14 * j + 3) ^ 2 - r * (14 * j + 3) ^ 2 := by linarith [hE2R]
    rw [h2E]
    push_cast
    -- with `t = r + 1` and `n = 16j + 4 + r (14j + 3)`:
    -- `(7t + 1) * 2E - (7t - 6) * n^2 = 2 (7t + 1) n - 2 r`
    have : ((r : ℝ) + 1 + 1 / 7) *
          (2 * ((4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) * (4 * j + 1)) +
            2 * r * (14 * j + 3) +
            2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) * r * (14 * j + 3) +
            r ^ 2 * (14 * j + 3) ^ 2 - r * (14 * j + 3) ^ 2) -
        ((r : ℝ) + 1 + 1 / 7 - 1) *
          (2 * (4 * j + 1) + 2 * (4 * j + 1) + r * (14 * j + 3)) ^ 2 =
        (2 * (7 * (r + 1) + 1) * (2 * (4 * j + 1) + 2 * (4 * j + 1) + r * (14 * j + 3)) - 2 * r) /
          7 := by ring
    have hpos : (0 : ℝ) ≤
        (2 * (7 * ((r : ℝ) + 1) + 1) * (2 * (4 * j + 1) + 2 * (4 * j + 1) + r * (14 * j + 3)) -
          2 * r) / 7 := by
      refine div_nonneg ?_ (by norm_num)
      nlinarith [mul_nonneg hr0 hj0, mul_nonneg hr0 hr0, mul_nonneg (mul_nonneg hr0 hr0) hj0]
    linarith
  · -- `k = 3t + 2`: Toft's 5-critical graph on `8q + g` vertices, `q = 4j + 1`, `g = 30j + 7`,
    -- joined with `r = t - 1` cycles of length `b = 46j + 11`
    have hq : Odd (4 * j + 1) := ⟨2 * j, by ring⟩
    have hq3 : 3 ≤ 4 * j + 1 := by omega
    have hg : Odd (30 * j + 7) := ⟨15 * j + 3, by ring⟩
    have hg3 : 3 ≤ 30 * j + 7 := by omega
    have hb : Odd (46 * j + 11) := ⟨23 * j + 5, by ring⟩
    have hb3 : 3 ≤ 46 * j + 11 := by omega
    have hC := h1 _ hq hq3
    have hT := h3 _ _ _ _ hC hC
    have hF := h4 _ _ _ _ hT (h1 _ hg hg3)
    obtain ⟨E, hE, hE2⟩ := iter h1 h2 hb hb3 (by norm_num : 3 ≤ 5) hF r
    have hk3 : 5 + 3 * r = k := by omega
    rw [hk3] at hE
    -- abbreviations, as real numbers: q = 4j+1, a = 8q + g, e = q^2 + 8q + 4qg + g
    have hE2R : (2 : ℝ) * E + r * (46 * j + 11) ^ 2 =
        2 * (((4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) * (4 * j + 1)) +
            (30 * j + 7) + (2 * (4 * j + 1) + 2 * (4 * j + 1)) +
            (2 * (4 * j + 1) + 2 * (4 * j + 1)) * (30 * j + 7)) +
          2 * r * (46 * j + 11) +
          2 * (2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) + (30 * j + 7)) * r * (46 * j + 11) +
          r ^ 2 * (46 * j + 11) ^ 2 := by exact_mod_cast hE2
    refine ⟨2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) + (30 * j + 7) + r * (46 * j + 11),
      by omega, ?_⟩
    have hdelta : Erdos917.delta k = 24 / 69 := by simp [Erdos917.delta, hm]
    refine finish ((r : ℝ) + 1 + 24 / 69) (by positivity) (by rw [hrR, hdelta]) hE ?_
    have h2E : (2 : ℝ) * E =
        2 * (((4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) * (4 * j + 1)) +
            (30 * j + 7) + (2 * (4 * j + 1) + 2 * (4 * j + 1)) +
            (2 * (4 * j + 1) + 2 * (4 * j + 1)) * (30 * j + 7)) +
          2 * r * (46 * j + 11) +
          2 * (2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) + (30 * j + 7)) * r * (46 * j + 11) +
          r ^ 2 * (46 * j + 11) ^ 2 - r * (46 * j + 11) ^ 2 := by linarith [hE2R]
    rw [h2E]
    push_cast
    -- with `t = r + 1` and `n = 62j + 15 + r (46j + 11)`:
    -- `(23t + 8) * 2E - (23t - 15) * n^2 = 2 (23t + 8) n - 2 t`
    have : ((r : ℝ) + 1 + 24 / 69) *
          (2 * (((4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) +
                (4 * j + 1) * (4 * j + 1)) +
              (30 * j + 7) + (2 * (4 * j + 1) + 2 * (4 * j + 1)) +
              (2 * (4 * j + 1) + 2 * (4 * j + 1)) * (30 * j + 7)) +
            2 * r * (46 * j + 11) +
            2 * (2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) + (30 * j + 7)) * r * (46 * j + 11) +
            r ^ 2 * (46 * j + 11) ^ 2 - r * (46 * j + 11) ^ 2) -
        ((r : ℝ) + 1 + 24 / 69 - 1) *
          (2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) + (30 * j + 7) + r * (46 * j + 11)) ^ 2 =
        (2 * (23 * (r + 1) + 8) *
            (2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) + (30 * j + 7) + r * (46 * j + 11)) -
          2 * (r + 1)) / 23 := by ring
    have hpos : (0 : ℝ) ≤
        (2 * (23 * ((r : ℝ) + 1) + 8) *
            (2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) + (30 * j + 7) + r * (46 * j + 11)) -
          2 * (r + 1)) / 23 := by
      refine div_nonneg ?_ (by norm_num)
      nlinarith [mul_nonneg hr0 hj0, mul_nonneg hr0 hr0, mul_nonneg (mul_nonneg hr0 hr0) hj0]
    linarith

end OMA.R_Erdos917_erdos_917_variants_lower_construction_R1
