import OMAStatements.S_oeis_a160999

/-!
OEIS A160999 (R. J. Mathar, Jun 01 2009): Row sums of A027052.
Conjecture: (-n+2)*a(n) +(6*n-11)*a(n-1) +(-7*n+1)*a(n-2) +2*(-4*n+27)*a(n-3) +(5*n-28)*a(n-4) +(2*n-3)*a(n-5) +3*(n-5)*a(n-6)=0.

Proof (kernel method). With u(n, d) = T(n, 2n - d), the row polynomials E_n(y) = sum_d u(n, d) y^d
satisfy y E_n = (1 + y + y^2) E_(n-1) - (1 + u(n-1, 1) y + y^(2n) - y^(2n+1)) for n >= 2
(`row_poly`). At the kernel root y = X M, M the Motzkin series, the left side cancels after
telescoping (`telescope`, `kernel`), which gives the first diagonal F_1 = sum_n u(n, 1) X^n as R F_1
= P_1 + Q_1 M with R = (1 - X)(1 - 3X - X^2 - X^3) (`hF1`). The array recursion along the diagonals
(`vert`) gives R F_d = P_d + Q_d M for the other diagonals (`hF`). Evaluating the row recursion at y
= 1 gives a(n+1) = 3 a(n) - 1 - u(n, 1) for the row sums (`rowsum`), so their series G satisfies (1
- X)((1 - 3X) G + X F_1) = 1 - 2X (`G_eq`) and (1 - 3X) R G = P + Q M (`hG`). Mathar's recurrence is
the differential equation L G = B in θ = X d/dX, an identity linear in M once θ M is replaced by its
value from the Motzkin equation (`θM`, `ode`); the coefficient of X^n is the recurrence (`recur`).
-/

namespace OMA.S_oeis_a160999

open Finset PowerSeries


/-! ### The operator θ = X d/dX on rational power series -/

/-- θ multiplies the n-th coefficient by n. -/
noncomputable def θ (F : ℚ⟦X⟧) : ℚ⟦X⟧ := PowerSeries.mk fun n => (n : ℚ) * coeff n F

lemma coeff_θ (F : ℚ⟦X⟧) (n : ℕ) : coeff n (θ F) = n * coeff n F := coeff_mk _ _

lemma θ_add (F G : ℚ⟦X⟧) : θ (F + G) = θ F + θ G := by
  ext n
  simp [coeff_θ, mul_add]

lemma θ_sub (F G : ℚ⟦X⟧) : θ (F - G) = θ F - θ G := by
  ext n
  simp [coeff_θ, mul_sub]

lemma θ_mul (F G : ℚ⟦X⟧) : θ (F * G) = θ F * G + F * θ G := by
  ext n
  simp only [coeff_θ, map_add, coeff_mul, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun p hp => ?_)
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp]
  push_cast
  ring

lemma θ_C (c : ℚ) : θ (C c) = 0 := by
  ext n
  rw [coeff_θ, coeff_C]
  split_ifs with h <;> simp [h]

lemma θ_one : θ 1 = 0 := by
  rw [← map_one C, θ_C]

lemma θ_ofNat (c : ℕ) [c.AtLeastTwo] : θ (no_index (OfNat.ofNat c : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C c, θ_C]

lemma θ_X : θ X = X := by
  ext n
  rw [coeff_θ, coeff_X]
  split_ifs with h <;> simp [h]

lemma θ_X_pow (k : ℕ) : θ (X ^ k) = (k : ℚ⟦X⟧) * X ^ k := by
  ext n
  rw [coeff_θ, coeff_X_pow, ← map_natCast C, coeff_C_mul, coeff_X_pow]
  split_ifs with h <;> simp [h]

/-! ### The Motzkin series -/

/-- The Motzkin numbers: m(n+1) = m(n) + sum_(k<n) m(k) m(n-1-k). -/
def mz : ℕ → ℚ
  | 0 => 1
  | n + 1 => mz n + ∑ k : Fin n, mz k * mz (n - 1 - k)

/-- The Motzkin series M = 1 + X M + X^2 M^2. -/
noncomputable def M : ℚ⟦X⟧ := PowerSeries.mk mz

lemma M_quad : M = 1 + X * M + X ^ 2 * M ^ 2 := by
  ext n
  rcases n with _ | _ | m
  · simp [M, mz]
  · simp [M, mz, coeff_X_pow_mul', coeff_one]
  · have h1 : coeff (m + 1 + 1) (X * M) = mz (m + 1) := by
      rw [coeff_succ_X_mul]
      simp [M]
    have h2 : coeff (m + 1 + 1) (X ^ 2 * M ^ 2) = ∑ p ∈ antidiagonal m, mz p.1 * mz p.2 := by
      rw [coeff_X_pow_mul', if_pos (by omega), show m + 1 + 1 - 2 = m by omega, pow_two, coeff_mul]
      simp [M]
    rw [map_add, map_add, h1, h2, coeff_one, if_neg (by omega), zero_add]
    simp only [M, coeff_mk]
    rw [mz, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]
    simp

lemma M_const : constantCoeff M = 1 := by
  simp [M, ← coeff_zero_eq_constantCoeff_apply, mz]

/-- θ M from the quadratic: (1 - 2X - 3X^2) θ M = (3X^2 + 3X - 2) M + 2. -/
lemma θM : (1 - 2 * X - 3 * X ^ 2) * θ M = (3 * X ^ 2 + 3 * X - 2) * M + 2 := by
  have hq := M_quad
  have h := congrArg θ hq
  rw [θ_add, θ_add, θ_one, θ_mul, θ_mul, θ_X, θ_X_pow, pow_two M, θ_mul] at h
  push_cast at h
  linear_combination (1 - X - 2 * X ^ 2 * M) * h + (2 + 4 * X ^ 2 * M + 4 * X ^ 2 * θ M) * hq

lemma M_ne_zero : M ≠ 0 := by
  intro h
  have := M_const
  rw [h, map_zero] at this
  exact zero_ne_one this

/-- The coefficients of A * B up to K only see those of B up to K. -/
lemma coeff_mul_low (A B : ℚ⟦X⟧) (K : ℕ) (h : ∀ j ≤ K, coeff j B = 0) : coeff K (A * B) = 0 := by
  rw [coeff_mul]
  refine sum_eq_zero (fun p hp => ?_)
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [h p.2 (by omega), mul_zero]

lemma coeff_X_pow_mul_low (W : ℚ⟦X⟧) (K : ℕ) : coeff K (X ^ (K + 1) * W) = 0 := by
  rw [coeff_X_pow_mul', if_neg (by omega)]

/-- Telescoping X M E(m+2) = M E(m+1) - c(m). -/
lemma telescope (E c : ℕ → ℚ⟦X⟧) (h : ∀ m, X * M * E (m + 2) = M * E (m + 1) - c m) (N : ℕ) :
    X * M * E 1 = ∑ m ∈ range N, X ^ (m + 1) * c m + X ^ (N + 1) * (M * E (N + 1)) := by
  induction N with
  | zero =>
    simp only [range_zero, sum_empty, zero_add, pow_one]
    ring
  | succ N ih =>
    rw [ih, sum_range_succ]
    linear_combination (-X ^ (N + 1)) * h N

lemma θ_neg (F : ℚ⟦X⟧) : θ (-F) = -θ F := by
  ext n
  simp [coeff_θ]

lemma ne_zero_of_constantCoeff {G : ℚ⟦X⟧} (h : constantCoeff G ≠ 0) : G ≠ 0 := by
  intro hG
  rw [hG, map_zero] at h
  exact h rfl

/-- The polynomial sum_i cs_i X^i. -/
noncomputable def pl (cs : List ℚ) : ℚ⟦X⟧ := ∑ i ∈ range cs.length, C (cs.getD i 0) * X ^ i

lemma coeff_pl_mul (cs : List ℚ) (G : ℚ⟦X⟧) (n : ℕ) (h : cs.length ≤ n + 1) :
    coeff n (pl cs * G) = ∑ i ∈ range cs.length, cs.getD i 0 * coeff (n - i) G := by
  unfold pl
  rw [sum_mul, map_sum]
  refine sum_congr rfl (fun i hi => ?_)
  rw [mem_range] at hi
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega)]

lemma coeff_pl_big (cs : List ℚ) (n : ℕ) (h : cs.length ≤ n) : coeff n (pl cs) = 0 := by
  unfold pl
  rw [map_sum]
  refine sum_eq_zero (fun i hi => ?_)
  rw [mem_range] at hi
  rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]

/-! ### The array A027052 -/

lemma T_big (n k : ℕ) (h : 2 * n < k) : T n k = 0 := by
  cases n with
  | zero => simp only [T]; rw [if_neg (by omega)]
  | succ n => rw [T, if_pos h]

lemma T_one (n k : ℕ) (h1 : k ≤ 2 * n) (h2 : k = 0 ∨ k = 2 ∨ k = 2 * n) : T n k = 1 := by
  cases n with
  | zero => simp only [T]; rw [if_pos (by omega)]
  | succ n => rw [T, if_neg (by omega), if_neg (by omega), if_pos (by omega)]

lemma T_zero_one (n : ℕ) (hn : 1 ≤ n) : T n 1 = 0 := by
  cases n with
  | zero => omega
  | succ n => rw [T, if_neg (by omega), if_pos rfl]

lemma T_rec (n k : ℕ) (h1 : 3 ≤ k) (h2 : k < 2 * (n + 1)) :
    T (n + 1) k = T n (k - 3) + T n (k - 2) + T n (k - 1) := by
  rw [T, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- u(n, d) = T(n, 2n - d): the d-th diagonal from the right edge (0 for d > 2n). -/
def u (n d : ℕ) : ℕ := if d ≤ 2 * n then T n (2 * n - d) else 0

lemma u_big (n d : ℕ) (h : 2 * n < d) : u n d = 0 := by
  rw [u, if_neg (by omega)]

lemma u_eqT (n d : ℕ) (h : d ≤ 2 * n) : u n d = T n (2 * n - d) := by
  rw [u, if_pos h]

lemma u_zero (n : ℕ) : u n 0 = 1 := by
  rw [u_eqT n 0 (by omega)]
  exact T_one n _ (by omega) (Or.inr (Or.inr (by omega)))

lemma u_rec (n d : ℕ) (h1 : 1 ≤ d) (h2 : d + 1 ≤ 2 * n) :
    u (n + 1) d = u n (d - 1) + u n d + u n (d + 1) := by
  rw [u, if_pos (by omega), T_rec n _ (by omega) (by omega), u, u, u, if_pos (by omega),
    if_pos (by omega), if_pos (by omega), show 2 * (n + 1) - d - 3 = 2 * n - (d + 1) by omega,
    show 2 * (n + 1) - d - 2 = 2 * n - d by omega, show 2 * (n + 1) - d - 1 = 2 * n - (d - 1) by omega]
  ring

/-- The row polynomial sum_d u(n, d) y^d. -/
noncomputable def rowP (n : ℕ) : Polynomial ℚ :=
  ∑ d ∈ range (2 * n + 1), Polynomial.C (u n d : ℚ) * Polynomial.X ^ d

lemma coeff_rowP (n e : ℕ) : (rowP n).coeff e = (u n e : ℚ) := by
  unfold rowP
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [mem_range] at h
    rw [u_big n e (by omega)]
    simp

/-- The row recursion as a polynomial identity. -/
lemma row_poly (n : ℕ) (hn : 1 ≤ n) :
    Polynomial.X ^ 1 * rowP (n + 1) + (1 + Polynomial.C (u n 1 : ℚ) * Polynomial.X ^ 1 +
      Polynomial.X ^ (2 * n + 2) - Polynomial.X ^ (2 * n + 3)) =
      rowP n + Polynomial.X ^ 1 * rowP n + Polynomial.X ^ 2 * rowP n := by
  ext e
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_one,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_X_pow, Polynomial.coeff_X_pow_mul', coeff_rowP]
  rcases (show e = 0 ∨ e = 1 ∨ (2 ≤ e ∧ e ≤ 2 * n) ∨ e = 2 * n + 1 ∨ e = 2 * n + 2 ∨
      e = 2 * n + 3 ∨ 2 * n + 3 < e by omega) with h | h | h | h | h | h | h
  · subst h
    simp [u_zero]
  · subst h
    simp [u_zero, show n ≠ 0 by omega]
    ring
  · simp only [if_pos (show 1 ≤ e by omega), if_neg (show ¬ e = 0 by omega),
      if_neg (show ¬ e = 1 by omega), if_neg (show ¬ e = 2 * n + 2 by omega),
      if_neg (show ¬ e = 2 * n + 3 by omega), if_pos (show 2 ≤ e by omega)]
    rw [u_rec n (e - 1) (by omega) (by omega), show e - 1 - 1 = e - 2 by omega,
      show e - 1 + 1 = e by omega]
    push_cast
    ring
  · subst h
    simp only [if_pos (show 1 ≤ 2 * n + 1 by omega), if_neg (show ¬ 2 * n + 1 = 0 by omega),
      if_neg (show ¬ 2 * n + 1 = 1 by omega), if_neg (show ¬ 2 * n + 1 = 2 * n + 2 by omega),
      if_neg (show ¬ 2 * n + 1 = 2 * n + 3 by omega), if_pos (show 2 ≤ 2 * n + 1 by omega)]
    rw [u_eqT (n + 1) _ (by omega), show 2 * (n + 1) - (2 * n + 1 - 1) = 2 by omega,
      T_one (n + 1) 2 (by omega) (Or.inr (Or.inl rfl)), u_big n (2 * n + 1) (by omega),
      u_eqT n (2 * n + 1 - 1) (by omega), show 2 * n - (2 * n + 1 - 1) = 0 by omega,
      T_one n 0 (by omega) (Or.inl rfl), u_eqT n (2 * n + 1 - 2) (by omega),
      show 2 * n - (2 * n + 1 - 2) = 1 by omega, T_zero_one n hn]
    norm_num
  · subst h
    simp only [if_pos (show 1 ≤ 2 * n + 2 by omega), if_neg (show ¬ 2 * n + 2 = 0 by omega),
      if_neg (show ¬ 2 * n + 2 = 1 by omega), if_true,
      if_neg (show ¬ 2 * n + 2 = 2 * n + 3 by omega), if_pos (show 2 ≤ 2 * n + 2 by omega)]
    rw [u_eqT (n + 1) _ (by omega), show 2 * (n + 1) - (2 * n + 2 - 1) = 1 by omega,
      T_zero_one (n + 1) (by omega), u_big n (2 * n + 2) (by omega),
      u_big n (2 * n + 2 - 1) (by omega), u_eqT n (2 * n + 2 - 2) (by omega),
      show 2 * n - (2 * n + 2 - 2) = 0 by omega, T_one n 0 (by omega) (Or.inl rfl)]
    norm_num
  · subst h
    simp only [if_pos (show 1 ≤ 2 * n + 3 by omega), if_neg (show ¬ 2 * n + 3 = 0 by omega),
      if_neg (show ¬ 2 * n + 3 = 1 by omega), if_neg (show ¬ 2 * n + 3 = 2 * n + 2 by omega),
      if_true, if_pos (show 2 ≤ 2 * n + 3 by omega)]
    rw [u_eqT (n + 1) _ (by omega), show 2 * (n + 1) - (2 * n + 3 - 1) = 0 by omega,
      T_one (n + 1) 0 (by omega) (Or.inl rfl), u_big n (2 * n + 3) (by omega),
      u_big n (2 * n + 3 - 1) (by omega), u_big n (2 * n + 3 - 2) (by omega)]
    norm_num
  · simp only [if_pos (show 1 ≤ e by omega), if_neg (show ¬ e = 0 by omega),
      if_neg (show ¬ e = 1 by omega), if_neg (show ¬ e = 2 * n + 2 by omega),
      if_neg (show ¬ e = 2 * n + 3 by omega), if_pos (show 2 ≤ e by omega)]
    rw [u_big (n + 1) _ (by omega), u_big n e (by omega), u_big n (e - 1) (by omega),
      u_big n (e - 2) (by omega)]
    norm_num

/-- The row polynomial at the kernel root X M. -/
noncomputable def E (n : ℕ) : ℚ⟦X⟧ := Polynomial.aeval (X * M) (rowP n)

lemma XM_eq : X * M = X * (1 + X * M + (X * M) ^ 2) := by
  linear_combination X * M_quad

/-- The row recursion at the kernel root. -/
lemma row_ps (m : ℕ) : X * M * E (m + 2) = M * E (m + 1) -
    (1 + (u (m + 1) 1 : ℚ⟦X⟧) * (X * M) + (X * M) ^ (2 * m + 4) - (X * M) ^ (2 * m + 5)) := by
  have h := congrArg (Polynomial.aeval (X * M)) (row_poly (m + 1) (by omega))
  simp only [map_add, map_sub, map_mul, map_pow, map_one, Polynomial.aeval_X, map_natCast] at h
  rw [show 2 * (m + 1) + 2 = 2 * m + 4 by ring, show 2 * (m + 1) + 3 = 2 * m + 5 by ring] at h
  apply mul_left_cancel₀ (X_ne_zero (R := ℚ))
  unfold E
  linear_combination X * h - Polynomial.aeval (X * M) (rowP (m + 1)) * XM_eq

/-- The diagonal series F_d = sum_n u(n, d) X^n. -/
noncomputable def F (d : ℕ) : ℚ⟦X⟧ := PowerSeries.mk fun n => (u n d : ℚ)

lemma E_one : E 1 = 1 + (X * M) ^ 2 := by
  have h0 : u 1 0 = 1 := by decide
  have h1 : u 1 1 = 0 := by decide
  have h2 : u 1 2 = 1 := by decide
  unfold E rowP
  simp only [show 2 * 1 + 1 = 3 by rfl, sum_range_succ, range_zero, sum_empty, zero_add, h0, h1, h2]
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, Nat.cast_one,
    Nat.cast_zero, map_one, map_zero, pow_zero, one_mul, zero_mul, add_zero, pow_one]

lemma F_zero : (1 - X) * F 0 = 1 := by
  ext n
  rcases n with _ | n
  · simp [F, u_zero]
  · rw [sub_mul, one_mul, map_sub, coeff_succ_X_mul]
    simp [F, u_zero, coeff_one]

lemma geom1 (N : ℕ) : (1 - X) * ∑ m ∈ range N, (X : ℚ⟦X⟧) ^ (m + 1) = X - X ^ (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih]
    ring

lemma geom3 (N : ℕ) : (1 - X * (X * M) ^ 2) *
    ∑ m ∈ range N, X ^ (m + 1) * ((X * M) ^ (2 * m + 4) - (X * M) ^ (2 * m + 5)) =
      X * ((X * M) ^ 4 - (X * M) ^ 5) -
        X ^ (N + 1) * ((X * M) ^ (2 * N + 4) - (X * M) ^ (2 * N + 5)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih]
    ring

lemma low1 (N j : ℕ) (hj : j ≤ N) :
    coeff j (∑ m ∈ range N, X ^ (m + 1) * ((u (m + 1) 1 : ℕ) : ℚ⟦X⟧)) = coeff j (F 1) := by
  rw [map_sum]
  simp only [F, coeff_mk]
  rcases j with _ | j
  · rw [sum_eq_zero (fun m _ => by rw [coeff_X_pow_mul', if_neg (by omega)])]
    rw [u_big 0 1 (by omega)]
    simp
  · rw [sum_eq_single j]
    · rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, ← map_natCast C, coeff_zero_C]
    · intro m _ hm
      rw [coeff_X_pow_mul']
      split_ifs with h
      · rw [← map_natCast C, coeff_C, if_neg (by omega)]
      · rfl
    · intro h
      rw [mem_range] at h
      omega

/-- The kernel identity: the boundary terms of the row recursion, summed. -/
lemma kernel : (1 - X) * (1 - X * (X * M) ^ 2) * (X * M * (1 + (X * M) ^ 2)) =
    (1 - X * (X * M) ^ 2) * X + (1 - X) * (1 - X * (X * M) ^ 2) * (X * M) * F 1 +
      (1 - X) * X * ((X * M) ^ 4 - (X * M) ^ 5) := by
  ext K
  have ht := telescope E (fun m => 1 + (u (m + 1) 1 : ℚ⟦X⟧) * (X * M) + (X * M) ^ (2 * m + 4) -
    (X * M) ^ (2 * m + 5)) row_ps K
  rw [E_one] at ht
  have hs : ∑ m ∈ range K, X ^ (m + 1) * (1 + (u (m + 1) 1 : ℚ⟦X⟧) * (X * M) +
      (X * M) ^ (2 * m + 4) - (X * M) ^ (2 * m + 5)) =
      ∑ m ∈ range K, (X : ℚ⟦X⟧) ^ (m + 1) +
        X * M * ∑ m ∈ range K, X ^ (m + 1) * ((u (m + 1) 1 : ℕ) : ℚ⟦X⟧) +
        ∑ m ∈ range K, X ^ (m + 1) * ((X * M) ^ (2 * m + 4) - (X * M) ^ (2 * m + 5)) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl (fun m _ => ?_)
    ring
  have hd : (1 - X) * (1 - X * (X * M) ^ 2) * (X * M * (1 + (X * M) ^ 2)) -
      ((1 - X * (X * M) ^ 2) * X + (1 - X) * (1 - X * (X * M) ^ 2) * (X * M) * F 1 +
        (1 - X) * X * ((X * M) ^ 4 - (X * M) ^ 5)) =
      (1 - X) * (1 - X * (X * M) ^ 2) * (X * M) *
          (∑ m ∈ range K, X ^ (m + 1) * ((u (m + 1) 1 : ℕ) : ℚ⟦X⟧) - F 1) +
        X ^ (K + 1) * (-(1 - X * (X * M) ^ 2) -
          (1 - X) * ((X * M) ^ (2 * K + 4) - (X * M) ^ (2 * K + 5)) +
          (1 - X) * (1 - X * (X * M) ^ 2) * (M * E (K + 1))) := by
    linear_combination (1 - X) * (1 - X * (X * M) ^ 2) * ht + (1 - X) * (1 - X * (X * M) ^ 2) * hs +
      (1 - X * (X * M) ^ 2) * geom1 K + (1 - X) * geom3 K
  have h0 : coeff K ((1 - X) * (1 - X * (X * M) ^ 2) * (X * M * (1 + (X * M) ^ 2)) -
      ((1 - X * (X * M) ^ 2) * X + (1 - X) * (1 - X * (X * M) ^ 2) * (X * M) * F 1 +
        (1 - X) * X * ((X * M) ^ 4 - (X * M) ^ 5))) = 0 := by
    rw [hd, map_add, coeff_X_pow_mul_low, add_zero]
    apply coeff_mul_low
    intro j hj
    rw [map_sub, low1 K j hj, sub_self]
  rwa [map_sub, sub_eq_zero] at h0

/-! ### The diagonals -/

/-- The first diagonal from the kernel identity: R F_1 = P_1 + Q_1 M. -/
lemma hF1 : (1 - 4 * X + 2 * X ^ 2 + X ^ 4) * F 1 = (2 * X ^ 2 - 2 * X ^ 3) + (-2 * X ^ 3 - 2 * X ^ 4) * M := by
  have hk := kernel
  have hA : (1 - X) * (1 - X * (X * M) ^ 2) * X * M ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) X_ne_zero) M_ne_zero
    · apply ne_zero_of_constantCoeff
      simp
    · apply ne_zero_of_constantCoeff
      simp
  apply mul_left_cancel₀ hA
  linear_combination (-(1 - 4 * X + 2 * X ^ 2 + X ^ 4)) * hk + ((X - 4 * X ^ 2 + 2 * X ^ 3 + X ^ 5) + (2 * X ^ 3 - 4 * X ^ 4 + 2 * X ^ 5) * M + (X ^ 3 - 5 * X ^ 4 + 8 * X ^ 5 - 2 * X ^ 6 - X ^ 7 - X ^ 8) * M ^ 2) * M_quad

/-- The row sums as a series. -/
noncomputable def G : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

lemma a_eq (n : ℕ) : (a n : ℚ) = (rowP n).eval 1 := by
  unfold a rowP
  rw [Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    one_pow, mul_one]
  push_cast
  rw [← sum_range_reflect]
  refine sum_congr rfl (fun d hd => ?_)
  rw [mem_range] at hd
  rw [u_eqT n d (by omega), show 2 * n + 1 - 1 - d = 2 * n - d by omega]

/-- The row recursion at y = 1. -/
lemma rowsum (n : ℕ) (hn : 1 ≤ n) : (a (n + 1) : ℚ) = 3 * a n - 1 - u n 1 := by
  have h := congrArg (Polynomial.eval 1) (row_poly n hn)
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, one_pow, one_mul, mul_one] at h
  rw [a_eq, a_eq]
  linarith

lemma G_eq : (1 - X) * ((1 - 3 * X) * G + X * F 1) = 1 - 2 * X := by
  have a0 : a 0 = 1 := by decide
  have a1 : a 1 = 2 := by decide
  have u01 : u 0 1 = 0 := by decide
  have e3 : (C (3 : ℚ) : ℚ⟦X⟧) = 3 := map_ofNat C 3
  have hH : (1 - 3 * X) * G + X * F 1 = PowerSeries.mk (fun n => if n = 0 then (1 : ℚ) else -1) := by
    rw [show (1 - 3 * X) * G + X * F 1 = G - X * (C (3 : ℚ) * G - F 1) by rw [e3]; ring]
    ext n
    rcases n with _ | n
    · simp [G, a0]
    · rw [map_sub, coeff_succ_X_mul, map_sub, coeff_C_mul]
      simp only [G, F, coeff_mk, if_neg (Nat.succ_ne_zero n)]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [a0, a1, u01]
        norm_num
      · rw [rowsum n hn]
        ring
  have e2 : (C (2 : ℚ) : ℚ⟦X⟧) = 2 := map_ofNat C 2
  rw [hH, ← e2]
  ext n
  rcases n with _ | _ | n
  · simp
  · rw [sub_mul, one_mul, map_sub, coeff_succ_X_mul, map_sub, coeff_C_mul, coeff_one, coeff_X]
    simp
    norm_num
  · rw [sub_mul, one_mul, map_sub, coeff_succ_X_mul, map_sub, coeff_C_mul, coeff_one, coeff_X]
    simp

lemma hG : (1 - 7 * X + 14 * X ^ 2 - 6 * X ^ 3 + X ^ 4 - 3 * X ^ 5) * G = (1 - 5 * X + 5 * X ^ 2 - X ^ 3 + 4 * X ^ 4) + (2 * X ^ 4 + 2 * X ^ 5) * M := by
  linear_combination (1 - 3 * X - X ^ 2 - X ^ 3) * G_eq + (-X) * hF1

/-! ### The differential equation and the recurrence -/

lemma θR : θ (1 - 7 * X + 14 * X ^ 2 - 6 * X ^ 3 + X ^ 4 - 3 * X ^ 5) = (-7 * X + 28 * X ^ 2 - 18 * X ^ 3 + 4 * X ^ 4 - 15 * X ^ 5) := by
  simp only [θ_add, θ_sub, θ_mul, θ_X_pow, θ_X, θ_ofNat, θ_one, θ_neg]
  push_cast
  ring

lemma θP : θ (1 - 5 * X + 5 * X ^ 2 - X ^ 3 + 4 * X ^ 4) = (-5 * X + 10 * X ^ 2 - 3 * X ^ 3 + 16 * X ^ 4) := by
  simp only [θ_add, θ_sub, θ_mul, θ_X_pow, θ_X, θ_ofNat, θ_one, θ_neg]
  push_cast
  ring

lemma θQ : θ (2 * X ^ 4 + 2 * X ^ 5) = (8 * X ^ 4 + 10 * X ^ 5) := by
  simp only [θ_add, θ_sub, θ_mul, θ_X_pow, θ_X, θ_ofNat, θ_one, θ_neg]
  push_cast
  ring

/-- Mathar's recurrence as a differential equation: L F_1 = B. -/
lemma ode : pl [-1, 6, -7, -8, 5, 2, 3] * θ (G) + pl [2, -5, -13, 30, -8, 7, 3] * G = pl [2, -3, -11, 13, -5] := by
  have e1 : (1 - 7 * X + 14 * X ^ 2 - 6 * X ^ 3 + X ^ 4 - 3 * X ^ 5) * G = (1 - 5 * X + 5 * X ^ 2 - X ^ 3 + 4 * X ^ 4) + (2 * X ^ 4 + 2 * X ^ 5) * M := hG
  have e2 : (-7 * X + 28 * X ^ 2 - 18 * X ^ 3 + 4 * X ^ 4 - 15 * X ^ 5) * G + (1 - 7 * X + 14 * X ^ 2 - 6 * X ^ 3 + X ^ 4 - 3 * X ^ 5) * θ (G) =
      (-5 * X + 10 * X ^ 2 - 3 * X ^ 3 + 16 * X ^ 4) + (8 * X ^ 4 + 10 * X ^ 5) * M + (2 * X ^ 4 + 2 * X ^ 5) * θ M := by
    have h := congrArg θ e1
    rw [θ_mul (1 - 7 * X + 14 * X ^ 2 - 6 * X ^ 3 + X ^ 4 - 3 * X ^ 5) (G), θ_add (1 - 5 * X + 5 * X ^ 2 - X ^ 3 + 4 * X ^ 4) ((2 * X ^ 4 + 2 * X ^ 5) * M), θ_mul (2 * X ^ 4 + 2 * X ^ 5) M, θR, θP, θQ] at h
    linear_combination h
  have e4 := θM
  have hK : ((1 - 16 * X + 102 * X ^ 2 - 320 * X ^ 3 + 467 * X ^ 4 - 128 * X ^ 5 - 364 * X ^ 6 + 256 * X ^ 7 - 89 * X ^ 8 + 208 * X ^ 9 - 90 * X ^ 10 - 27 * X ^ 12) : ℚ⟦X⟧) ≠ 0 := by
    apply ne_zero_of_constantCoeff
    simp
  have h : (1 - 16 * X + 102 * X ^ 2 - 320 * X ^ 3 + 467 * X ^ 4 - 128 * X ^ 5 - 364 * X ^ 6 + 256 * X ^ 7 - 89 * X ^ 8 + 208 * X ^ 9 - 90 * X ^ 10 - 27 * X ^ 12) * ((-1 + 6 * X - 7 * X ^ 2 - 8 * X ^ 3 + 5 * X ^ 4 + 2 * X ^ 5 + 3 * X ^ 6) * θ (G) + (2 - 5 * X - 13 * X ^ 2 + 30 * X ^ 3 - 8 * X ^ 4 + 7 * X ^ 5 + 3 * X ^ 6) * G) = (1 - 16 * X + 102 * X ^ 2 - 320 * X ^ 3 + 467 * X ^ 4 - 128 * X ^ 5 - 364 * X ^ 6 + 256 * X ^ 7 - 89 * X ^ 8 + 208 * X ^ 9 - 90 * X ^ 10 - 27 * X ^ 12) * (2 - 3 * X - 11 * X ^ 2 + 13 * X ^ 3 - 5 * X ^ 4) := by
    linear_combination (2 - 30 * X + 166 * X ^ 2 - 358 * X ^ 3 - 84 * X ^ 4 + 1464 * X ^ 5 - 1428 * X ^ 6 - 780 * X ^ 7 + 826 * X ^ 8 + 178 * X ^ 9 + 590 * X ^ 10 - 366 * X ^ 11 - 72 * X ^ 12 - 108 * X ^ 13) * e1 + (-1 + 15 * X - 86 * X ^ 2 + 218 * X ^ 3 - 147 * X ^ 4 - 339 * X ^ 5 + 492 * X ^ 6 + 108 * X ^ 7 - 167 * X ^ 8 - 119 * X ^ 9 - 118 * X ^ 10 + 90 * X ^ 11 + 27 * X ^ 12 + 27 * X ^ 13) * e2 + (-2 * X ^ 4 + 24 * X ^ 5 - 100 * X ^ 6 + 136 * X ^ 7 + 114 * X ^ 8 - 336 * X ^ 9 - 24 * X ^ 10 + 144 * X ^ 11 + 98 * X ^ 12 + 56 * X ^ 13 - 68 * X ^ 14 - 24 * X ^ 15 - 18 * X ^ 16) * e4
  have ha1 : pl [-1, 6, -7, -8, 5, 2, 3] = (-1 + 6 * X - 7 * X ^ 2 - 8 * X ^ 3 + 5 * X ^ 4 + 2 * X ^ 5 + 3 * X ^ 6) := by
    simp only [pl, sum_range_succ, range_zero, sum_empty, List.length_cons, List.length_nil,
      List.getD_cons_zero, List.getD_cons_succ, map_neg, map_ofNat C, map_one, map_zero]
    ring
  have ha0 : pl [2, -5, -13, 30, -8, 7, 3] = (2 - 5 * X - 13 * X ^ 2 + 30 * X ^ 3 - 8 * X ^ 4 + 7 * X ^ 5 + 3 * X ^ 6) := by
    simp only [pl, sum_range_succ, range_zero, sum_empty, List.length_cons, List.length_nil,
      List.getD_cons_zero, List.getD_cons_succ, map_neg, map_ofNat C, map_one, map_zero]
    ring
  have hB : pl [2, -3, -11, 13, -5] = (2 - 3 * X - 11 * X ^ 2 + 13 * X ^ 3 - 5 * X ^ 4) := by
    simp only [pl, sum_range_succ, range_zero, sum_empty, List.length_cons, List.length_nil,
      List.getD_cons_zero, List.getD_cons_succ, map_neg, map_ofNat C, map_one, map_zero]
    ring
  rw [ha1, ha0, hB]
  exact mul_left_cancel₀ hK h

/-- Mathar's recurrence. -/
theorem recur : ∀ n : ℕ, 6 ≤ n →
    (-(n : ℤ) + 2) * (a n : ℤ) + (6 * (n : ℤ) - 11) * (a (n - 1) : ℤ) + (-7 * (n : ℤ) + 1) * (a (n - 2) : ℤ) + 2 * (-4 * (n : ℤ) + 27) * (a (n - 3) : ℤ) + (5 * (n : ℤ) - 28) * (a (n - 4) : ℤ) + (2 * (n : ℤ) - 3) * (a (n - 5) : ℤ) + 3 * ((n : ℤ) - 5) * (a (n - 6) : ℤ) = 0 := by
  intro n hn
  have h := congrArg (coeff n) ode
  rw [map_add, coeff_pl_mul _ _ _ (by norm_num; omega), coeff_pl_mul _ _ _ (by norm_num; omega), coeff_pl_big _ _ (by norm_num; omega)] at h
  simp only [coeff_θ, G, coeff_mk, sum_range_succ, sum_range_zero, zero_add, List.getD_cons_zero,
    List.getD_cons_succ, List.length_cons, List.length_nil, Nat.sub_zero] at h
  have c1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have c2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have c3 : ((n - 3 : ℕ) : ℚ) = (n : ℚ) - 3 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have c4 : ((n - 4 : ℕ) : ℚ) = (n : ℚ) - 4 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have c5 : ((n - 5 : ℕ) : ℚ) = (n : ℚ) - 5 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have c6 : ((n - 6 : ℕ) : ℚ) = (n : ℚ) - 6 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [c1, c2, c3, c4, c5, c6] at h
  have goal : (-(n : ℚ) + 2) * (a n : ℚ) + (6 * (n : ℚ) - 11) * (a (n - 1) : ℚ) + (-7 * (n : ℚ) + 1) * (a (n - 2) : ℚ) + 2 * (-4 * (n : ℚ) + 27) * (a (n - 3) : ℚ) + (5 * (n : ℚ) - 28) * (a (n - 4) : ℚ) + (2 * (n : ℚ) - 3) * (a (n - 5) : ℚ) + 3 * ((n : ℚ) - 5) * (a (n - 6) : ℚ) = 0 := by
    linear_combination h
  exact_mod_cast goal

/-- Controls: the entry's listed terms, a(0) to a(26). -/
theorem controls :
    a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 5 ∧ a 3 = 12 ∧
    a 4 = 31 ∧ a 5 = 84 ∧ a 6 = 233 ∧ a 7 = 656 ∧
    a 8 = 1865 ∧ a 9 = 5338 ∧ a 10 = 15355 ∧ a 11 = 44342 ∧
    a 12 = 128455 ∧ a 13 = 373100 ∧ a 14 = 1086087 ∧ a 15 = 3167634 ∧
    a 16 = 9254009 ∧ a 17 = 27074666 ∧ a 18 = 79316491 ∧ a 19 = 232633206 ∧
    a 20 = 683026535 ∧ a 21 = 2007327660 ∧ a 22 = 5904415195 ∧ a 23 = 17381265934 ∧
    a 24 = 51203990457 ∧ a 25 = 150945252394 ∧ a 26 = 445252685313 := by
  have v0 : a 0 = 1 := by decide +kernel
  have v1 : a 1 = 2 := by decide +kernel
  have v2 : a 2 = 5 := by decide +kernel
  have v3 : a 3 = 12 := by decide +kernel
  have v4 : a 4 = 31 := by decide +kernel
  have v5 : a 5 = 84 := by decide +kernel
  have v6 : a 6 = 233 := by
    have h := recur 6 (by norm_num)
    rw [show (6 : ℕ) - 1 = 5 from rfl, show (6 : ℕ) - 2 = 4 from rfl, show (6 : ℕ) - 3 = 3 from rfl, show (6 : ℕ) - 4 = 2 from rfl, show (6 : ℕ) - 5 = 1 from rfl, show (6 : ℕ) - 6 = 0 from rfl, v5, v4, v3, v2, v1, v0] at h
    generalize a 6 = x at h ⊢
    push_cast at h
    omega
  have v7 : a 7 = 656 := by
    have h := recur 7 (by norm_num)
    rw [show (7 : ℕ) - 1 = 6 from rfl, show (7 : ℕ) - 2 = 5 from rfl, show (7 : ℕ) - 3 = 4 from rfl, show (7 : ℕ) - 4 = 3 from rfl, show (7 : ℕ) - 5 = 2 from rfl, show (7 : ℕ) - 6 = 1 from rfl, v6, v5, v4, v3, v2, v1] at h
    generalize a 7 = x at h ⊢
    push_cast at h
    omega
  have v8 : a 8 = 1865 := by
    have h := recur 8 (by norm_num)
    rw [show (8 : ℕ) - 1 = 7 from rfl, show (8 : ℕ) - 2 = 6 from rfl, show (8 : ℕ) - 3 = 5 from rfl, show (8 : ℕ) - 4 = 4 from rfl, show (8 : ℕ) - 5 = 3 from rfl, show (8 : ℕ) - 6 = 2 from rfl, v7, v6, v5, v4, v3, v2] at h
    generalize a 8 = x at h ⊢
    push_cast at h
    omega
  have v9 : a 9 = 5338 := by
    have h := recur 9 (by norm_num)
    rw [show (9 : ℕ) - 1 = 8 from rfl, show (9 : ℕ) - 2 = 7 from rfl, show (9 : ℕ) - 3 = 6 from rfl, show (9 : ℕ) - 4 = 5 from rfl, show (9 : ℕ) - 5 = 4 from rfl, show (9 : ℕ) - 6 = 3 from rfl, v8, v7, v6, v5, v4, v3] at h
    generalize a 9 = x at h ⊢
    push_cast at h
    omega
  have v10 : a 10 = 15355 := by
    have h := recur 10 (by norm_num)
    rw [show (10 : ℕ) - 1 = 9 from rfl, show (10 : ℕ) - 2 = 8 from rfl, show (10 : ℕ) - 3 = 7 from rfl, show (10 : ℕ) - 4 = 6 from rfl, show (10 : ℕ) - 5 = 5 from rfl, show (10 : ℕ) - 6 = 4 from rfl, v9, v8, v7, v6, v5, v4] at h
    generalize a 10 = x at h ⊢
    push_cast at h
    omega
  have v11 : a 11 = 44342 := by
    have h := recur 11 (by norm_num)
    rw [show (11 : ℕ) - 1 = 10 from rfl, show (11 : ℕ) - 2 = 9 from rfl, show (11 : ℕ) - 3 = 8 from rfl, show (11 : ℕ) - 4 = 7 from rfl, show (11 : ℕ) - 5 = 6 from rfl, show (11 : ℕ) - 6 = 5 from rfl, v10, v9, v8, v7, v6, v5] at h
    generalize a 11 = x at h ⊢
    push_cast at h
    omega
  have v12 : a 12 = 128455 := by
    have h := recur 12 (by norm_num)
    rw [show (12 : ℕ) - 1 = 11 from rfl, show (12 : ℕ) - 2 = 10 from rfl, show (12 : ℕ) - 3 = 9 from rfl, show (12 : ℕ) - 4 = 8 from rfl, show (12 : ℕ) - 5 = 7 from rfl, show (12 : ℕ) - 6 = 6 from rfl, v11, v10, v9, v8, v7, v6] at h
    generalize a 12 = x at h ⊢
    push_cast at h
    omega
  have v13 : a 13 = 373100 := by
    have h := recur 13 (by norm_num)
    rw [show (13 : ℕ) - 1 = 12 from rfl, show (13 : ℕ) - 2 = 11 from rfl, show (13 : ℕ) - 3 = 10 from rfl, show (13 : ℕ) - 4 = 9 from rfl, show (13 : ℕ) - 5 = 8 from rfl, show (13 : ℕ) - 6 = 7 from rfl, v12, v11, v10, v9, v8, v7] at h
    generalize a 13 = x at h ⊢
    push_cast at h
    omega
  have v14 : a 14 = 1086087 := by
    have h := recur 14 (by norm_num)
    rw [show (14 : ℕ) - 1 = 13 from rfl, show (14 : ℕ) - 2 = 12 from rfl, show (14 : ℕ) - 3 = 11 from rfl, show (14 : ℕ) - 4 = 10 from rfl, show (14 : ℕ) - 5 = 9 from rfl, show (14 : ℕ) - 6 = 8 from rfl, v13, v12, v11, v10, v9, v8] at h
    generalize a 14 = x at h ⊢
    push_cast at h
    omega
  have v15 : a 15 = 3167634 := by
    have h := recur 15 (by norm_num)
    rw [show (15 : ℕ) - 1 = 14 from rfl, show (15 : ℕ) - 2 = 13 from rfl, show (15 : ℕ) - 3 = 12 from rfl, show (15 : ℕ) - 4 = 11 from rfl, show (15 : ℕ) - 5 = 10 from rfl, show (15 : ℕ) - 6 = 9 from rfl, v14, v13, v12, v11, v10, v9] at h
    generalize a 15 = x at h ⊢
    push_cast at h
    omega
  have v16 : a 16 = 9254009 := by
    have h := recur 16 (by norm_num)
    rw [show (16 : ℕ) - 1 = 15 from rfl, show (16 : ℕ) - 2 = 14 from rfl, show (16 : ℕ) - 3 = 13 from rfl, show (16 : ℕ) - 4 = 12 from rfl, show (16 : ℕ) - 5 = 11 from rfl, show (16 : ℕ) - 6 = 10 from rfl, v15, v14, v13, v12, v11, v10] at h
    generalize a 16 = x at h ⊢
    push_cast at h
    omega
  have v17 : a 17 = 27074666 := by
    have h := recur 17 (by norm_num)
    rw [show (17 : ℕ) - 1 = 16 from rfl, show (17 : ℕ) - 2 = 15 from rfl, show (17 : ℕ) - 3 = 14 from rfl, show (17 : ℕ) - 4 = 13 from rfl, show (17 : ℕ) - 5 = 12 from rfl, show (17 : ℕ) - 6 = 11 from rfl, v16, v15, v14, v13, v12, v11] at h
    generalize a 17 = x at h ⊢
    push_cast at h
    omega
  have v18 : a 18 = 79316491 := by
    have h := recur 18 (by norm_num)
    rw [show (18 : ℕ) - 1 = 17 from rfl, show (18 : ℕ) - 2 = 16 from rfl, show (18 : ℕ) - 3 = 15 from rfl, show (18 : ℕ) - 4 = 14 from rfl, show (18 : ℕ) - 5 = 13 from rfl, show (18 : ℕ) - 6 = 12 from rfl, v17, v16, v15, v14, v13, v12] at h
    generalize a 18 = x at h ⊢
    push_cast at h
    omega
  have v19 : a 19 = 232633206 := by
    have h := recur 19 (by norm_num)
    rw [show (19 : ℕ) - 1 = 18 from rfl, show (19 : ℕ) - 2 = 17 from rfl, show (19 : ℕ) - 3 = 16 from rfl, show (19 : ℕ) - 4 = 15 from rfl, show (19 : ℕ) - 5 = 14 from rfl, show (19 : ℕ) - 6 = 13 from rfl, v18, v17, v16, v15, v14, v13] at h
    generalize a 19 = x at h ⊢
    push_cast at h
    omega
  have v20 : a 20 = 683026535 := by
    have h := recur 20 (by norm_num)
    rw [show (20 : ℕ) - 1 = 19 from rfl, show (20 : ℕ) - 2 = 18 from rfl, show (20 : ℕ) - 3 = 17 from rfl, show (20 : ℕ) - 4 = 16 from rfl, show (20 : ℕ) - 5 = 15 from rfl, show (20 : ℕ) - 6 = 14 from rfl, v19, v18, v17, v16, v15, v14] at h
    generalize a 20 = x at h ⊢
    push_cast at h
    omega
  have v21 : a 21 = 2007327660 := by
    have h := recur 21 (by norm_num)
    rw [show (21 : ℕ) - 1 = 20 from rfl, show (21 : ℕ) - 2 = 19 from rfl, show (21 : ℕ) - 3 = 18 from rfl, show (21 : ℕ) - 4 = 17 from rfl, show (21 : ℕ) - 5 = 16 from rfl, show (21 : ℕ) - 6 = 15 from rfl, v20, v19, v18, v17, v16, v15] at h
    generalize a 21 = x at h ⊢
    push_cast at h
    omega
  have v22 : a 22 = 5904415195 := by
    have h := recur 22 (by norm_num)
    rw [show (22 : ℕ) - 1 = 21 from rfl, show (22 : ℕ) - 2 = 20 from rfl, show (22 : ℕ) - 3 = 19 from rfl, show (22 : ℕ) - 4 = 18 from rfl, show (22 : ℕ) - 5 = 17 from rfl, show (22 : ℕ) - 6 = 16 from rfl, v21, v20, v19, v18, v17, v16] at h
    generalize a 22 = x at h ⊢
    push_cast at h
    omega
  have v23 : a 23 = 17381265934 := by
    have h := recur 23 (by norm_num)
    rw [show (23 : ℕ) - 1 = 22 from rfl, show (23 : ℕ) - 2 = 21 from rfl, show (23 : ℕ) - 3 = 20 from rfl, show (23 : ℕ) - 4 = 19 from rfl, show (23 : ℕ) - 5 = 18 from rfl, show (23 : ℕ) - 6 = 17 from rfl, v22, v21, v20, v19, v18, v17] at h
    generalize a 23 = x at h ⊢
    push_cast at h
    omega
  have v24 : a 24 = 51203990457 := by
    have h := recur 24 (by norm_num)
    rw [show (24 : ℕ) - 1 = 23 from rfl, show (24 : ℕ) - 2 = 22 from rfl, show (24 : ℕ) - 3 = 21 from rfl, show (24 : ℕ) - 4 = 20 from rfl, show (24 : ℕ) - 5 = 19 from rfl, show (24 : ℕ) - 6 = 18 from rfl, v23, v22, v21, v20, v19, v18] at h
    generalize a 24 = x at h ⊢
    push_cast at h
    omega
  have v25 : a 25 = 150945252394 := by
    have h := recur 25 (by norm_num)
    rw [show (25 : ℕ) - 1 = 24 from rfl, show (25 : ℕ) - 2 = 23 from rfl, show (25 : ℕ) - 3 = 22 from rfl, show (25 : ℕ) - 4 = 21 from rfl, show (25 : ℕ) - 5 = 20 from rfl, show (25 : ℕ) - 6 = 19 from rfl, v24, v23, v22, v21, v20, v19] at h
    generalize a 25 = x at h ⊢
    push_cast at h
    omega
  have v26 : a 26 = 445252685313 := by
    have h := recur 26 (by norm_num)
    rw [show (26 : ℕ) - 1 = 25 from rfl, show (26 : ℕ) - 2 = 24 from rfl, show (26 : ℕ) - 3 = 23 from rfl, show (26 : ℕ) - 4 = 22 from rfl, show (26 : ℕ) - 5 = 21 from rfl, show (26 : ℕ) - 6 = 20 from rfl, v25, v24, v23, v22, v21, v20] at h
    generalize a 26 = x at h ⊢
    push_cast at h
    omega
  exact ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26⟩

/-- Mathar's conjecture. -/
theorem conjecture : ∀ n : ℕ, 6 ≤ n →
      (-(n : ℤ) + 2) * (a n : ℤ) + (6 * (n : ℤ) - 11) * (a (n - 1) : ℤ) + (-7 * (n : ℤ) + 1) * (a (n - 2) : ℤ) + 2 * (-4 * (n : ℤ) + 27) * (a (n - 3) : ℤ) + (5 * (n : ℤ) - 28) * (a (n - 4) : ℤ) + (2 * (n : ℤ) - 3) * (a (n - 5) : ℤ) + 3 * ((n : ℤ) - 5) * (a (n - 6) : ℤ) = 0 :=
  recur

end OMA.S_oeis_a160999

theorem OMA.solution : type_of% @OMA.S_oeis_a160999.main :=
  OMA.S_oeis_a160999.conjecture
