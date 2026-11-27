import FormalConjectures.ErdosProblems.«499»

-- Reduction Erdos499.vanDerWaerden.R1 of Erdős Problem 499 — van der Waerden permanent bound
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- Route: Gurvits (2008), as written up by Laurent and Schrijver (2010). For a doubly stochastic
-- matrix M and k ≤ n let F_k(y) be the permanent of M with its first k columns replaced by the
-- vector of entries sum over l < k of M i l * y l. Then F_n(y) = n! * prod (M y), F_0 = perm M, and
-- the capacity bound F_k(y) ≥ (n!/n^n) k^k prod_{l<k} y l is carried from k = n (weighted AM-GM)
-- down to k = 0. H1 is the stability input (real-rootedness), H2 the derivative of a permanent,
-- H3 the univariate Gurvits inequality. The capacity bound, the telescoping of the constants and
-- the downward induction are proved here.

open Matrix Finset Nat

namespace OMA.R_Erdos499_vanDerWaerden_R1

/-- Real-rootedness (Gurvits; a consequence of real stability of products of nonnegative linear
forms, preserved by partial derivatives and by setting variables to zero): for nonnegative
vectors `v, w` and a nonnegative matrix `C`, the permanent of the matrix whose first `k` columns
are `v + t w` and whose other columns are those of `C` is, as a function of `t`, of the form
`a * prod (t + r i)` with `a ≥ 0`, at most `k` factors and all `r i ≥ 0`. -/
def H1 : Prop :=
  ∀ (n k : ℕ) (v w : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ),
    (∀ i, 0 ≤ v i) → (∀ i, 0 ≤ w i) → (∀ i j, 0 ≤ C i j) →
    ∃ m ≤ k, ∃ a : ℝ, 0 ≤ a ∧ ∃ r : Fin m → ℝ, (∀ i, 0 ≤ r i) ∧
      ∀ t : ℝ, (Matrix.of fun i j : Fin n => if (j : ℕ) < k then v i + t * w i else C i j).permanent
        = a * ∏ i, (t + r i)

/-- Derivative of a permanent (multilinearity in the columns plus symmetry under column
permutations): for `1 ≤ k ≤ n`, the derivative at `t = 0` of the permanent of the matrix with first
`k` columns `v + t w` (other columns from `C`) is `k` times the permanent of the matrix with
columns `v` before position `k - 1`, `w` at position `k - 1` and `C` after it. -/
def H2 : Prop :=
  ∀ (n k : ℕ), 1 ≤ k → k ≤ n → ∀ (v w : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ),
    HasDerivAt
      (fun t : ℝ =>
        (Matrix.of fun i j : Fin n => if (j : ℕ) < k then v i + t * w i else C i j).permanent)
      ((k : ℝ) * (Matrix.of fun i j : Fin n =>
        if (j : ℕ) + 1 < k then v i else if (j : ℕ) + 1 = k then w i else C i j).permanent)
      0

/-- Univariate Gurvits inequality: if `f t = a * prod_{i<m} (t + r i)` with `a ≥ 0`, `r i ≥ 0`,
`m ≤ d`, `d ≥ 1`, and `L * t ≤ f t` for all `t > 0`, then `((d-1)/d)^(d-1) * L ≤ f'(0)`. -/
def H3 : Prop :=
  ∀ (d m : ℕ), 1 ≤ d → m ≤ d → ∀ (a : ℝ) (r : Fin m → ℝ) (L D : ℝ), 0 ≤ a → (∀ i, 0 ≤ r i) →
    (∀ t : ℝ, 0 < t → L * t ≤ a * ∏ i, (t + r i)) →
    HasDerivAt (fun t : ℝ => a * ∏ i, (t + r i)) D 0 →
    (((d : ℝ) - 1) / d) ^ (d - 1) * L ≤ D

/-- Weighted AM-GM: for doubly stochastic `M` and positive `x`, `prod x ≤ prod (M x)`. -/
lemma cap_ge_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n))
    (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) :
    ∏ j, x j ≤ ∏ i, ∑ j, M i j * x j := by
  obtain ⟨h0, hr, hc⟩ := hM
  have hrow : ∀ i, ∑ j, M i j = 1 := fun i => by
    have := congrFun hr i; simpa [mulVec, dotProduct] using this
  have hcol : ∀ j, ∑ i, M i j = 1 := fun j => by
    have := congrFun hc j; simpa [vecMul, dotProduct] using this
  calc ∏ j, x j = ∏ j, x j ^ (∑ i, M i j) := by simp [hcol]
    _ = ∏ j, ∏ i, x j ^ M i j := by
        refine prod_congr rfl fun j _ => ?_
        rw [Real.rpow_sum_of_pos (hx j)]
    _ = ∏ i, ∏ j, x j ^ M i j := prod_comm
    _ ≤ ∏ i, ∑ j, M i j * x j := by
        refine prod_le_prod (fun i _ => prod_nonneg fun j _ => (Real.rpow_nonneg (hx j).le _))
          fun i _ => ?_
        exact Real.geom_mean_le_arith_mean_weighted _ _ _ (fun j _ => h0 i j) (hrow i)
          (fun j _ => (hx j).le)

/-- The permanent of a matrix all of whose columns equal `u` is `n! * prod u`. -/
lemma permanent_const_cols {n : ℕ} (u : Fin n → ℝ) :
    (Matrix.of fun i (_ : Fin n) => u i).permanent = (n ! : ℝ) * ∏ i, u i := by
  simp only [permanent, of_apply]
  have : ∀ σ : Equiv.Perm (Fin n), ∏ i, u (σ i) = ∏ i, u i := fun σ => Equiv.prod_comp σ u
  simp only [this, sum_const, nsmul_eq_mul]
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

lemma pow_self_ne_zero (n : ℕ) : ((n : ℝ) ^ n) ≠ 0 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact pow_ne_zero _ (by exact_mod_cast h.ne')

/-- Telescoping of the constants: `((k+1-1)/(k+1))^k * (k+1)^(k+1) = k^k * (k+1)`. -/
lemma const_step (k : ℕ) :
    ((((k + 1 : ℕ) : ℝ) - 1) / ((k + 1 : ℕ) : ℝ)) ^ (k + 1 - 1) * ((k + 1 : ℕ) : ℝ) ^ (k + 1)
      = (k : ℝ) ^ k * ((k : ℝ) + 1) := by
  push_cast
  simp only [add_sub_cancel_right]
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [div_pow, pow_succ]
  field_simp

theorem main : H1 → H2 → H3 → type_of% @Erdos499.vanDerWaerden := by
  intro hH1 hH2 hH3 n M hM
  have hM0 : ∀ i j, 0 ≤ M i j := hM.1
  set c : ℝ := (n ! : ℝ) / (n : ℝ) ^ n with hc
  -- the capacity bound for F_k, carried down from k = n
  have key : ∀ j : ℕ, j ≤ n → ∀ y : Fin n → ℝ, (∀ l, 0 < y l) →
      c * ((n - j : ℕ) : ℝ) ^ (n - j) * ∏ l : Fin n, (if (l : ℕ) < n - j then y l else 1) ≤
        (Matrix.of fun i jj : Fin n => if (jj : ℕ) < n - j then
          ∑ l : Fin n, (if (l : ℕ) < n - j then M i l * y l else 0) else M i jj).permanent := by
    intro j
    induction j with
    | zero =>
      intro _ y hy
      simp only [Nat.sub_zero, Fin.is_lt, if_true]
      rw [permanent_const_cols]
      have h1 := cap_ge_one M hM y hy
      have : c * (n : ℝ) ^ n = n ! := by
        rw [hc]; exact div_mul_cancel₀ _ (pow_self_ne_zero n)
      rw [this]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    | succ j ih =>
      intro hj y hy
      -- k = k' + 1 = n - j, the new level is k' = n - (j+1)
      obtain ⟨k', hk'⟩ : ∃ k', n - j = k' + 1 := ⟨n - j - 1, by omega⟩
      have hk'' : n - (j + 1) = k' := by omega
      have ihk := ih (by omega)
      rw [hk'] at ihk
      rw [hk'']
      have hk'n : k' < n := by omega
      set idx : Fin n := ⟨k', hk'n⟩ with hidx
      set v : Fin n → ℝ := fun i => ∑ l : Fin n, (if (l : ℕ) < k' then M i l * y l else 0) with hv
      set w : Fin n → ℝ := fun i => M i idx with hw
      set P : ℝ := ∏ l : Fin n, (if (l : ℕ) < k' then y l else 1) with hP
      have hv0 : ∀ i, 0 ≤ v i := fun i => sum_nonneg fun l _ => by
        split_ifs
        · exact mul_nonneg (hM0 i l) (hy l).le
        · exact le_refl _
      have hw0 : ∀ i, 0 ≤ w i := fun i => hM0 i idx
      obtain ⟨m, hm, a, ha, r, hr, hfac⟩ := hH1 n (k' + 1) v w M hv0 hw0 hM0
      have hder := hH2 n (k' + 1) (by omega) (by omega) v w M
      have hfun : (fun t : ℝ =>
          (Matrix.of fun i jj : Fin n => if (jj : ℕ) < k' + 1 then v i + t * w i
            else M i jj).permanent) = fun t => a * ∏ i, (t + r i) := funext hfac
      rw [hfun] at hder
      -- the capacity bound along the line y with coordinate k' replaced by t
      have hline : ∀ t : ℝ, 0 < t →
          (c * ((k' + 1 : ℕ) : ℝ) ^ (k' + 1) * P) * t ≤ a * ∏ i, (t + r i) := by
        intro t ht
        have hyt : ∀ l, 0 < Function.update y idx t l := by
          intro l
          by_cases hl : l = idx
          · subst hl; simp [ht]
          · simp [Function.update_of_ne hl, hy l]
        have h := ihk (Function.update y idx t) hyt
        have hprod : ∏ l : Fin n, (if (l : ℕ) < k' + 1 then Function.update y idx t l else 1)
            = P * t := by
          rw [show P * t = P * ∏ l : Fin n, (if l = idx then t else 1) by simp, hP,
            ← prod_mul_distrib]
          refine prod_congr rfl fun l _ => ?_
          by_cases hl : l = idx
          · subst hl; simp [hidx]
          · have hl' : (l : ℕ) ≠ k' := fun h => hl (Fin.ext h)
            rw [Function.update_of_ne hl, if_neg hl]
            by_cases hlt : (l : ℕ) < k'
            · simp [hlt, show (l : ℕ) < k' + 1 by omega]
            · simp [hlt, show ¬ (l : ℕ) < k' + 1 by omega]
        have hmat : (Matrix.of fun i jj : Fin n => if (jj : ℕ) < k' + 1 then
            ∑ l : Fin n, (if (l : ℕ) < k' + 1 then M i l * Function.update y idx t l else 0)
            else M i jj) =
            (Matrix.of fun i jj : Fin n => if (jj : ℕ) < k' + 1 then v i + t * w i
              else M i jj) := by
          ext i jj
          simp only [of_apply]
          split_ifs with hjj
          · rw [hv, hw]
            simp only
            rw [show t * M i idx = ∑ l : Fin n, (if l = idx then t * M i l else 0) by simp,
              ← sum_add_distrib]
            refine sum_congr rfl fun l _ => ?_
            by_cases hl : l = idx
            · subst hl; simp [hidx, mul_comm]
            · rw [Function.update_of_ne hl, if_neg hl]
              have hl' : (l : ℕ) ≠ k' := fun h => hl (Fin.ext h)
              by_cases hlt : (l : ℕ) < k'
              · simp [hlt, show (l : ℕ) < k' + 1 by omega]
              · simp [hlt, show ¬ (l : ℕ) < k' + 1 by omega]
          · rfl
        rw [hprod, hmat, hfac] at h
        linarith [h]
      have h3 := hH3 (k' + 1) m (by omega) hm a r _ _ ha hr hline hder
      -- identify the matrix of H2 with F_{k'}(y)
      have hY : (Matrix.of fun i jj : Fin n =>
          if (jj : ℕ) + 1 < k' + 1 then v i else if (jj : ℕ) + 1 = k' + 1 then w i else M i jj) =
          (Matrix.of fun i jj : Fin n => if (jj : ℕ) < k' then
            ∑ l : Fin n, (if (l : ℕ) < k' then M i l * y l else 0) else M i jj) := by
        ext i jj
        simp only [of_apply]
        by_cases h1 : (jj : ℕ) < k'
        · rw [if_pos (by omega), if_pos h1]
        · rw [if_neg (by omega), if_neg h1]
          by_cases h2 : (jj : ℕ) = k'
          · rw [if_pos (by omega), hw]
            simp only
            congr 1
            exact Fin.ext h2.symm
          · rw [if_neg (by omega)]
      rw [hY] at h3
      have hcs := const_step k'
      have hPnn : 0 ≤ P := prod_nonneg fun l _ => by
        split_ifs
        · exact (hy l).le
        · exact zero_le_one
      have hpos : (0 : ℝ) < (k' : ℝ) + 1 := by positivity
      -- h3 : g * (c * (k'+1)^(k'+1) * P) ≤ (k'+1) * F
      have h4 : ((k' : ℝ) + 1) * (c * (k' : ℝ) ^ k' * P) ≤ ((k' : ℝ) + 1) *
          (Matrix.of fun i jj : Fin n => if (jj : ℕ) < k' then
            ∑ l : Fin n, (if (l : ℕ) < k' then M i l * y l else 0) else M i jj).permanent := by
        have e : ((((k' + 1 : ℕ) : ℝ) - 1) / ((k' + 1 : ℕ) : ℝ)) ^ (k' + 1 - 1) *
            (c * ((k' + 1 : ℕ) : ℝ) ^ (k' + 1) * P) = ((k' : ℝ) + 1) * (c * (k' : ℝ) ^ k' * P) := by
          calc _ = c * P * (((((k' + 1 : ℕ) : ℝ) - 1) / ((k' + 1 : ℕ) : ℝ)) ^ (k' + 1 - 1) *
                ((k' + 1 : ℕ) : ℝ) ^ (k' + 1)) := by ring
            _ = _ := by rw [hcs]; ring
        rw [← e]
        push_cast at h3 ⊢
        exact h3
      exact le_of_mul_le_mul_left h4 hpos
  have h0 := key n le_rfl (fun _ => 1) (fun _ => zero_lt_one)
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.not_lt_zero, if_false, prod_const_one,
    CharP.cast_eq_zero] at h0
  have hMeq : (Matrix.of fun i jj : Fin n => M i jj) = M := by ext; rfl
  rw [hMeq] at h0
  rw [_root_.zpow_neg, zpow_natCast]
  calc ((n : ℝ) ^ n)⁻¹ * (n ! : ℝ) = c := by rw [hc, div_eq_inv_mul]
    _ ≤ M.permanent := h0

end OMA.R_Erdos499_vanDerWaerden_R1
