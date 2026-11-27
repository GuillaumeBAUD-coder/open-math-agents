import FormalConjectures.ErdosProblems.«1133»

/-!
# Discretizing the sampling nodes in Erdős 1133

Use the equally spaced grid with n³ subintervals. The first step is a uniform
mesh estimate. Markov's inequality bounds the derivative by n² times the
interval norm, and for a mesh of size 2/n³ the interval norm is controlled by
the grid norm. The second step is a finite sampling obstruction. With n and
the sample indices fixed, its bounds are linear constraints on the n+1 real
coefficients, with a finite choice of peak index and sign.
-/

namespace OMA.R_Erdos1133_erdos_1133_variants_weaker_R1

open Filter Set Polynomial

-- Uniform sampling estimate on the cubic mesh, independent of the chosen nodes.
def H1 : Prop :=
  ∀ K : ℝ, 0 < K → ∀ᶠ n : ℕ in atTop,
    let g := fun k : ℕ => 2 * (k : ℝ) / (n : ℝ)^3 - 1
    ∀ x ∈ Icc (-1 : ℝ) 1, ∃ k ≤ n^3, ∀ P : Polynomial ℝ,
      P.natDegree ≤ n → (∀ j ≤ n^3, |P.eval (g j)| ≤ K) →
      |P.eval x - P.eval (g k)| ≤ 1

-- All sample and peak indices now belong to one finite rational grid.
def H2 : Prop :=
  ∀ A : ℝ, 0 < A → ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop,
    let m := ⌊(1 + ε) * (n : ℝ)⌋₊
    let g := fun k : ℕ => 2 * (k : ℝ) / (n : ℝ)^3 - 1
    ∀ a : Fin m → ℕ, (∀ i, a i ≤ n^3) →
      ∃ P : Polynomial ℝ, P.natDegree ≤ n ∧
        (∀ i, |P.eval (g (a i))| ≤ 1) ∧
        (∀ j ≤ n^3, |P.eval (g j)| ≤ 4 * (A + 1)) ∧
        ∃ j ≤ n^3, 2 * A < |P.eval (g j)|

lemma exact_degree_of_peaking {n m : ℕ} {C : ℝ} (hC : 0 < C)
    (x : Fin m → Icc (-1 : ℝ) 1) (P : Polynomial ℝ) (hd : P.natDegree ≤ n)
    (hnodes : ∀ i, |P.eval (x i : ℝ)| ≤ 1) {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1)
    (hpeak : C < |P.eval z|) :
    ∃ Q : Polynomial ℝ, Q.natDegree = n ∧ (∀ i, |Q.eval (x i : ℝ)| ≤ 1) ∧
      C < |Q.eval z| := by
  rcases hd.eq_or_lt with heq | hlt
  · exact ⟨P, heq, hnodes, hpeak⟩
  let A := |P.eval z|
  have hA : 0 < A := hC.trans hpeak
  have hdpos : 0 < 2 * (A + 1) := by positivity
  let t := (A - C) / (2 * (A + 1))
  have ht : 0 < t := div_pos (sub_pos.mpr hpeak) hdpos
  have ht1 : t < 1 := by
    apply (div_lt_iff₀ hdpos).mpr
    linarith
  have hgap : t * (2 * (A + 1)) = A - C := div_mul_cancel₀ _ hdpos.ne'
  let Q := Polynomial.C (1-t) * P + Polynomial.C t * (X : Polynomial ℝ)^n
  have hmon : (Polynomial.C t * (X : Polynomial ℝ)^n).natDegree = n :=
    natDegree_C_mul_X_pow n t ht.ne'
  have hQ : Q.natDegree = n := by
    apply (natDegree_add_eq_right_of_natDegree_lt _).trans hmon
    rw [hmon]
    exact (natDegree_C_mul_le _ _).trans_lt hlt
  have heval (v : ℝ) : Q.eval v = (1-t) * P.eval v + t * v^n := by simp [Q]
  have hpow {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 1) : |v^n| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr hv)
  have hbound {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 1) : |t * v^n| ≤ t := by
    rw [abs_mul, abs_of_pos ht]
    exact mul_le_of_le_one_right ht.le (hpow hv)
  refine ⟨Q,hQ,?_,?_⟩
  · intro i
    rw [heval]
    calc
      _ ≤ |(1-t) * P.eval (x i : ℝ)| + |t * (x i : ℝ)^n| := abs_add_le _ _
      _ ≤ (1-t) + t := by
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr ht1.le)]
        exact add_le_add (mul_le_of_le_one_right (sub_nonneg.mpr ht1.le) (hnodes i)) (hbound (x i).property)
      _ = 1 := by ring
  · have he : |(1-t) * P.eval z| ≤ |Q.eval z| + |t * z^n| := by
      simpa only [heval, add_sub_cancel_right] using
        (abs_sub ((1-t) * P.eval z + t * z^n) (t * z^n))
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr ht1.le)] at he
    change (1-t) * A ≤ |Q.eval z| + |t * z^n| at he
    nlinarith [hbound hz]


theorem main : H1 → H2 → type_of% @Erdos1133.erdos_1133.variants.weaker := by
  intro h1 h2 A hA
  obtain ⟨ε, hε, hfinite⟩ := h2 A hA
  refine ⟨ε, hε, ?_⟩
  have hmesh := h1 (4 * (A + 1)) (by positivity)
  filter_upwards [hfinite, hmesh, Filter.eventually_ge_atTop 1] with n hn hnear hnpos
  let m := ⌊(1 + ε) * (n : ℝ)⌋₊
  let g := fun k : ℕ => 2 * (k : ℝ) / (n : ℝ)^3 - 1
  dsimp only at ⊢
  intro x
  have hchoice (i : Fin m) := hnear (x i : ℝ) (x i).property
  choose a ha happrox using hchoice
  obtain ⟨P, hdeg, hsample, hgrid, j, hj, hpeak⟩ := hn a ha
  let Q := Polynomial.C (1 / 2 : ℝ) * P
  have hevalQ (v : ℝ) : Q.eval v = (1 / 2 : ℝ) * P.eval v := by simp [Q]
  have hnodes (i : Fin m) : |Q.eval (x i : ℝ)| ≤ 1 := by
    have he := happrox i P hdeg hgrid
    have he2 : |P.eval (x i : ℝ)| ≤ |P.eval (x i : ℝ) - P.eval (g (a i))| + |P.eval (g (a i))| := by
      simpa only [sub_add_cancel] using abs_add_le (P.eval (x i : ℝ) - P.eval (g (a i))) (P.eval (g (a i)))
    rw [hevalQ, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    linarith [hsample i]
  have hjreal : (j : ℝ) ≤ (n : ℝ)^3 := by exact_mod_cast hj
  have hden : (0 : ℝ) < (n : ℝ)^3 := by positivity
  have hz : g j ∈ Icc (-1 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · dsimp [g]; linarith [div_nonneg (by positivity : 0 ≤ 2 * (j : ℝ)) hden.le]
    · dsimp [g]
      have : 2 * (j : ℝ) / (n : ℝ)^3 ≤ 2 := (div_le_iff₀ hden).mpr (by linarith)
      linarith
  have hlarge : A < |Q.eval (g j)| := by
    rw [hevalQ, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    linarith
  obtain ⟨R, hd, hR, hRpeak⟩ := exact_degree_of_peaking hA x Q ((natDegree_C_mul_le _ _).trans hdeg) hnodes hz hlarge
  exact ⟨R, hd, hR, g j, hz, hRpeak⟩

end OMA.R_Erdos1133_erdos_1133_variants_weaker_R1
