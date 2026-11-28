import OMAStatements.S_oeis_a026573

/-!
OEIS A026573 (Clark Kimberling): a(n)=T(n,n-4), T given by A026568. Also a(n) = number of integer strings s(0),...,s(n) counted by T, such that s(n)=4.
Conjecture: -2*(n-4)*(n+4)*a(n) +(5*n^2-5*n-46)*a(n-1) +(4*n^2+n+18)*a(n-2) +(-11*n^2+24*n-16)*a(n-3) +2*(n-2)*(2*n-5)*a(n-4)=0.

Proof (kernel method on the half rows). With v(n, s) = T(n, n - s), the number of strings of the
comment of A026568 that end at s, the symmetry of the rows gives the recursion of v on s >= 0 (from
even values the strings may stay) with the middle column v(n+1, 0) = v(n, 0) + 2 v(n, 1) (`v_rec`,
`v_edge`). The even and odd parts of the half rows, alpha_n(z) = sum_m v(n, 2m) z^m and beta_n(z) =
sum_m v(n, 2m+1) z^m, satisfy z beta_(n+1) = (z + 1) alpha_n - v(n, 0) and alpha_(n+1) = alpha_n +
(z + 1) beta_n + v(n, 1) (`polyI`, `polyII`). At the root z = W - 1 of the kernel z (1 - X) = X^2 (z
+ 1)^2 (`kerW`) the half rows telescope (`ker_partial`, `kernel`), and with the middle column this
gives F_0^2 (1 - X)(1 - X - 4X^2) = 1 for F_0 = sum_n v(n, 0) X^n (`hF0`, `KL`). The recursion along
the diagonals then gives 2 X^s F_s = P_s + Q_s F_0 for explicit polynomials (`hF`). So F_0 satisfies
a first-order differential equation in θ = X d/dX (`ode0`), and Mathar's recurrence is the
differential equation L f = B for the target series f, an identity linear in F_0 (`ode`); its
coefficient of X^n is the recurrence (`recur`).
-/

namespace OMA.S_oeis_a026573

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

lemma θ_neg (F : ℚ⟦X⟧) : θ (-F) = -θ F := by
  ext n
  simp [coeff_θ]

lemma θ_sq (F : ℚ⟦X⟧) : θ (F ^ 2) = 2 * F * θ F := by
  rw [pow_two, θ_mul]
  ring

/-- The coefficients of A * B up to K only see those of B up to K. -/
lemma coeff_mul_low (A B : ℚ⟦X⟧) (K : ℕ) (h : ∀ j ≤ K, coeff j B = 0) : coeff K (A * B) = 0 := by
  rw [coeff_mul]
  refine sum_eq_zero (fun p hp => ?_)
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [h p.2 (by omega), mul_zero]

lemma coeff_X_pow_mul_low (W : ℚ⟦X⟧) (K : ℕ) : coeff K (X ^ (K + 1) * W) = 0 := by
  rw [coeff_X_pow_mul', if_neg (by omega)]

lemma ne_zero_of_constantCoeff {G : ℚ⟦X⟧} (h : constantCoeff G ≠ 0) : G ≠ 0 := by
  intro hG
  rw [hG, map_zero] at h
  exact h rfl

lemma cc_ofNat (c : ℕ) [c.AtLeastTwo] :
    constantCoeff (no_index (OfNat.ofNat c : ℚ⟦X⟧)) = OfNat.ofNat c := by
  rw [← map_ofNat C c, constantCoeff_C]

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

/-! ### The kernel root -/

/-- w(n+1) = w(n) - [n = 0] + sum_(k<n) w(k) w(n-1-k). -/
def wz : ℕ → ℚ
  | 0 => 1
  | n + 1 => wz n - (if n = 0 then 1 else 0) + ∑ k : Fin n, wz k * wz (n - 1 - k)

/-- W = 1 - X + X W + X^2 W^2, so that Z = W - 1 solves the kernel equation
Z (1 - X) = X^2 (Z + 1)^2. -/
noncomputable def W : ℚ⟦X⟧ := PowerSeries.mk wz

lemma W_quad : W = 1 - X + X * W + X ^ 2 * W ^ 2 := by
  ext n
  rcases n with _ | _ | m
  · simp [W, wz]
  · simp [W, wz, coeff_X_pow_mul', coeff_one, coeff_X]
  · have h1 : coeff (m + 1 + 1) (X * W) = wz (m + 1) := by
      rw [coeff_succ_X_mul]
      simp [W]
    have h2 : coeff (m + 1 + 1) (X ^ 2 * W ^ 2) = ∑ p ∈ antidiagonal m, wz p.1 * wz p.2 := by
      rw [coeff_X_pow_mul', if_pos (by omega), show m + 1 + 1 - 2 = m by omega, pow_two, coeff_mul]
      simp [W]
    rw [map_add, map_add, map_sub, h1, h2, coeff_one, if_neg (by omega), coeff_X, if_neg (by omega),
      sub_zero, zero_add]
    simp only [W, coeff_mk]
    rw [wz, if_neg (by omega), sub_zero, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      ← Fin.sum_univ_eq_sum_range]
    simp

/-- The kernel equation at z = W - 1. -/
lemma kerW : (W - 1) * (1 - X) = X ^ 2 * W ^ 2 := by
  linear_combination W_quad

lemma W_sub_one_ne : W - 1 ≠ 0 := by
  intro h
  have h2 := congrArg (coeff 2) h
  rw [map_sub, coeff_one, if_neg (by norm_num), map_zero] at h2
  have : coeff 2 W = 1 := by simp [W, wz]
  rw [this] at h2
  norm_num at h2

/-! ### The array A026568 -/

lemma T_big (i j : ℕ) (h : 2 * i < j) : T i j = 0 := by
  cases i with
  | zero => simp only [T]; rw [if_neg (by omega)]
  | succ i => rw [T, if_pos h]

lemma T_zero (i : ℕ) : T i 0 = 1 := by
  cases i with
  | zero => rfl
  | succ i => rw [T, if_neg (by omega), if_pos (Or.inl rfl)]

lemma T_top (i : ℕ) : T i (2 * i) = 1 := by
  cases i with
  | zero => rfl
  | succ i => rw [T, if_neg (by omega), if_pos (Or.inr rfl)]

lemma T_one (i : ℕ) : T (i + 1) 1 = (i + 2) / 2 := by
  rw [T, if_neg (by omega), if_neg (by omega), if_pos (Or.inl rfl)]

lemma T_top1 (i : ℕ) : T (i + 1) (2 * (i + 1) - 1) = (i + 2) / 2 := by
  rw [T, if_neg (by omega), if_neg (by omega), if_pos (Or.inr rfl)]

lemma T_rec (i j : ℕ) (h1 : 2 ≤ j) (h2 : j ≤ 2 * i) :
    T (i + 1) j = T i (j - 2) + T i j + (if (i + 1 + j) % 2 = 0 then T i (j - 1) else 0) := by
  rw [T, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  split_ifs <;> ring

/-- The rows are symmetric. -/
lemma T_sym (i j : ℕ) (h : j ≤ 2 * i) : T i (2 * i - j) = T i j := by
  induction i generalizing j with
  | zero =>
    obtain rfl : j = 0 := by omega
    rfl
  | succ i ih =>
    rcases (show j = 0 ∨ j = 1 ∨ (2 ≤ j ∧ j ≤ 2 * i) ∨ j = 2 * i + 1 ∨ j = 2 * i + 2 by omega)
      with hj | hj | hj | hj | hj
    · subst hj
      rw [Nat.sub_zero, T_top, T_zero]
    · subst hj
      rw [T_top1, T_one]
    · have a1 : T i (2 * (i + 1) - j - 2) = T i j := by
        rw [show 2 * (i + 1) - j - 2 = 2 * i - j by omega]
        exact ih j (by omega)
      have a2 : T i (2 * (i + 1) - j) = T i (j - 2) := by
        rw [show 2 * (i + 1) - j = 2 * i - (j - 2) by omega]
        exact ih (j - 2) (by omega)
      have a3 : T i (2 * (i + 1) - j - 1) = T i (j - 1) := by
        rw [show 2 * (i + 1) - j - 1 = 2 * i - (j - 1) by omega]
        exact ih (j - 1) (by omega)
      have hp : (i + 1 + (2 * (i + 1) - j)) % 2 = (i + 1 + j) % 2 := by omega
      rw [T_rec i _ (by omega) (by omega), T_rec i j hj.1 hj.2, a1, a2, a3, hp]
      ring
    · subst hj
      rw [show 2 * (i + 1) - (2 * i + 1) = 1 by omega, T_one,
        show 2 * i + 1 = 2 * (i + 1) - 1 by omega, T_top1]
    · subst hj
      rw [show 2 * (i + 1) - (2 * i + 2) = 0 by omega, T_zero,
        show 2 * i + 2 = 2 * (i + 1) by ring, T_top]

/-- v(n, s) = T(n, n - s), the strings of the comment of A026568 that end at s (0 for s > n). -/
def v (n s : ℕ) : ℕ := if s ≤ n then T n (n - s) else 0

lemma v_big (n s : ℕ) (h : n < s) : v n s = 0 := by
  rw [v, if_neg (by omega)]

lemma v_eqT (n s : ℕ) (h : s ≤ n) : v n s = T n (n - s) := by
  rw [v, if_pos h]

/-- The middle column: v(n+1, 0) = v(n, 0) + 2 v(n, 1), by the symmetry of the rows. -/
lemma v_edge (n : ℕ) : v (n + 1) 0 = v n 0 + 2 * v n 1 := by
  rcases n with _ | n
  · decide
  · have hs := T_sym (n + 1) (n + 2) (by omega)
    rw [show 2 * (n + 1) - (n + 2) = n by omega] at hs
    rw [v_eqT _ _ (by omega), v_eqT _ _ (by omega), v_eqT _ _ (by omega),
      show n + 1 + 1 - 0 = n + 2 by omega, show n + 1 - 0 = n + 1 by omega,
      show n + 1 - 1 = n by omega, T_rec (n + 1) (n + 2) (by omega) (by omega), if_pos (by omega),
      show n + 2 - 2 = n by omega, show n + 2 - 1 = n + 1 by omega, ← hs]
    ring

/-- The strings off the middle: from an even value one may also stay. -/
lemma v_rec (n s : ℕ) (hs : 1 ≤ s) :
    v (n + 1) s = v n (s - 1) + v n (s + 1) + (if s % 2 = 0 then v n s else 0) := by
  rcases (show n + 1 < s ∨ s = n + 1 ∨ s = n ∨ s + 1 ≤ n by omega) with h | h | h | h
  · rw [v_big _ _ h, v_big n (s - 1) (by omega), v_big n (s + 1) (by omega), v_big n s (by omega)]
    simp
  · subst h
    rw [v_eqT _ _ le_rfl, Nat.sub_self, T_zero, show n + 1 - 1 = n by omega, v_eqT n n le_rfl,
      Nat.sub_self, T_zero, v_big n (n + 1 + 1) (by omega), v_big n (n + 1) (by omega)]
    simp
  · subst h
    obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
    rw [v_eqT _ _ (by omega), show m + 1 + 1 - (m + 1) = 1 by omega, T_one, v_eqT _ _ (by omega),
      show m + 1 - (m + 1 - 1) = 1 by omega, show m + 1 = m + 1 by rfl, T_one,
      v_big _ (m + 1 + 1) (by omega), v_eqT _ (m + 1) le_rfl, Nat.sub_self, T_zero]
    split_ifs with h <;> omega
  · rw [v_eqT _ _ (by omega), v_eqT n (s - 1) (by omega), v_eqT n (s + 1) (by omega),
      v_eqT n s (by omega), T_rec n (n + 1 - s) (by omega) (by omega),
      show (n + 1 + (n + 1 - s)) % 2 = s % 2 by omega, show n + 1 - s - 2 = n - (s + 1) by omega,
      show n + 1 - s - 1 = n - s by omega, show n + 1 - s = n - (s - 1) by omega]
    ring

/-- The even and odd parts of the half row n as polynomials in z = y^2:
alpha_n = sum_m v(n, 2m) z^m, beta_n = sum_m v(n, 2m + 1) z^m. -/
noncomputable def α (n : ℕ) : Polynomial ℚ :=
  ∑ m ∈ range (n + 1), Polynomial.C (v n (2 * m) : ℚ) * Polynomial.X ^ m

noncomputable def β (n : ℕ) : Polynomial ℚ :=
  ∑ m ∈ range (n + 1), Polynomial.C (v n (2 * m + 1) : ℚ) * Polynomial.X ^ m

lemma coeff_α (n m : ℕ) : (α n).coeff m = (v n (2 * m) : ℚ) := by
  unfold α
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [mem_range] at h
    rw [v_big n (2 * m) (by omega)]
    simp

lemma coeff_β (n m : ℕ) : (β n).coeff m = (v n (2 * m + 1) : ℚ) := by
  unfold β
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [mem_range] at h
    rw [v_big n (2 * m + 1) (by omega)]
    simp

/-- The odd values: z beta_(n+1) = (z + 1) alpha_n - v(n, 0). -/
lemma polyI (n : ℕ) :
    Polynomial.X * β (n + 1) = (Polynomial.X + 1) * α n - Polynomial.C (v n 0 : ℚ) := by
  ext m
  rw [Polynomial.coeff_sub, add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_C]
  rcases m with _ | m
  · simp [coeff_α]
  · rw [Polynomial.coeff_X_mul, Polynomial.coeff_X_mul, coeff_β, coeff_α, coeff_α, if_neg (by omega),
      v_rec n (2 * m + 1) (by omega), if_neg (by omega), show 2 * m + 1 - 1 = 2 * m by omega,
      show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
    push_cast
    ring

/-- The even values: alpha_(n+1) = alpha_n + (z + 1) beta_n + v(n, 1). -/
lemma polyII (n : ℕ) :
    α (n + 1) = α n + (Polynomial.X + 1) * β n + Polynomial.C (v n 1 : ℚ) := by
  ext m
  rw [Polynomial.coeff_add, Polynomial.coeff_add, add_mul, one_mul, Polynomial.coeff_add,
    Polynomial.coeff_C]
  rcases m with _ | m
  · simp only [coeff_α, coeff_β, Polynomial.coeff_X_mul_zero, mul_zero, zero_add]
    rw [v_edge]
    push_cast
    ring
  · rw [Polynomial.coeff_X_mul, coeff_α, coeff_α, coeff_β, coeff_β, if_neg (by omega),
      v_rec n (2 * (m + 1)) (by omega), if_pos (by omega), show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
    push_cast
    ring

/-- The half rows at the kernel root z = W - 1. -/
noncomputable def e (n : ℕ) : ℚ⟦X⟧ := Polynomial.aeval (W - 1) (α n)

noncomputable def f (n : ℕ) : ℚ⟦X⟧ := Polynomial.aeval (W - 1) (β n)

lemma ef_I (n : ℕ) : (W - 1) * f (n + 1) = W * e n - (v n 0 : ℚ⟦X⟧) := by
  have h := congrArg (Polynomial.aeval (W - 1)) (polyI n)
  simp only [map_mul, map_sub, map_add, Polynomial.aeval_X, map_one, map_natCast] at h
  unfold e f
  linear_combination h

lemma ef_II (n : ℕ) : e (n + 1) = e n + W * f n + (v n 1 : ℚ⟦X⟧) := by
  have h := congrArg (Polynomial.aeval (W - 1)) (polyII n)
  simp only [map_mul, map_add, Polynomial.aeval_X, map_one, map_natCast] at h
  unfold e f
  linear_combination h

lemma e_zero : e 0 = 1 := by
  have h0 : v 0 0 = 1 := by decide
  simp [e, α, h0]

lemma f_zero : f 0 = 0 := by
  have h0 : v 0 1 = 0 := by decide
  simp [f, β, h0]

/-- The truncated kernel identity: the partial sums of the series below. -/
lemma ker_partial (N : ℕ) :
    (W - 1) - X ^ 2 * W * (∑ n ∈ range N, X ^ n * (v n 0 : ℚ⟦X⟧))
      + X * (W - 1) * (∑ n ∈ range N, X ^ n * (v n 1 : ℚ⟦X⟧)) =
      X ^ N * ((W - 1) * e N + X * W * (W - 1) * f N) := by
  induction N with
  | zero => simp [e_zero, f_zero]
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ]
    linear_combination ih - X ^ (N + 1) * (W - 1) * ef_II N - X ^ (N + 2) * W * ef_I N +
      X ^ N * e N * kerW

/-- The diagonal series F_s = sum_n v(n, s) X^n. -/
noncomputable def F (s : ℕ) : ℚ⟦X⟧ := PowerSeries.mk fun n => (v n s : ℚ)

lemma trunc_F (s N j : ℕ) (hj : j < N) :
    coeff j (∑ n ∈ range N, X ^ n * ((v n s : ℕ) : ℚ⟦X⟧)) = coeff j (F s) := by
  rw [map_sum, sum_eq_single j]
  · rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, ← map_natCast C, coeff_zero_C]
    simp [F]
  · intro m _ hm
    rw [coeff_X_pow_mul']
    split_ifs with h
    · rw [← map_natCast C, coeff_C, if_neg (by omega)]
    · rfl
  · intro h
    rw [mem_range] at h
    omega

/-- The kernel identity. -/
lemma kernel : (W - 1) - X ^ 2 * W * F 0 + X * (W - 1) * F 1 = 0 := by
  ext K
  have h := congrArg (coeff K) (ker_partial (K + 1))
  rw [coeff_X_pow_mul_low] at h
  have d0 : coeff K (X ^ 2 * W * (∑ n ∈ range (K + 1), X ^ n * ((v n 0 : ℕ) : ℚ⟦X⟧)) -
      X ^ 2 * W * F 0) = 0 := by
    rw [← mul_sub]
    apply coeff_mul_low
    intro j hj
    rw [map_sub, trunc_F 0 (K + 1) j (by omega), sub_self]
  have d1 : coeff K (X * (W - 1) * (∑ n ∈ range (K + 1), X ^ n * ((v n 1 : ℕ) : ℚ⟦X⟧)) -
      X * (W - 1) * F 1) = 0 := by
    rw [← mul_sub]
    apply coeff_mul_low
    intro j hj
    rw [map_sub, trunc_F 1 (K + 1) j (by omega), sub_self]
  rw [map_add, map_sub] at h
  rw [map_sub] at d0 d1
  rw [map_add, map_sub, map_zero]
  linarith

/-- The middle column along the diagonals. -/
lemma edge : F 0 = 1 + X * (F 0 + F 1 + F 1) := by
  ext n
  rcases n with _ | m
  · have : v 0 0 = 1 := by decide
    simp [F, this]
  · rw [map_add, coeff_succ_X_mul, coeff_one, if_neg (by omega), zero_add]
    simp only [F, map_add, coeff_mk]
    rw [v_edge m]
    push_cast
    ring

lemma vert_odd (k : ℕ) : F (2 * k + 1) = X * (F (2 * k) + F (2 * k + 2)) := by
  ext n
  rcases n with _ | m
  · simp [F, v_big 0 (2 * k + 1) (by omega)]
  · rw [coeff_succ_X_mul]
    simp only [F, map_add, coeff_mk]
    rw [v_rec m (2 * k + 1) (by omega), if_neg (by omega), show 2 * k + 1 - 1 = 2 * k by omega,
      show 2 * k + 1 + 1 = 2 * k + 2 by omega]
    push_cast
    ring

lemma vert_even (k : ℕ) : F (2 * k + 2) = X * (F (2 * k + 1) + F (2 * k + 3) + F (2 * k + 2)) := by
  ext n
  rcases n with _ | m
  · simp [F, v_big 0 (2 * k + 2) (by omega)]
  · rw [coeff_succ_X_mul]
    simp only [F, map_add, coeff_mk]
    rw [v_rec m (2 * k + 2) (by omega), if_pos (by omega), show 2 * k + 2 - 1 = 2 * k + 1 by omega,
      show 2 * k + 2 + 1 = 2 * k + 3 by omega]
    push_cast
    ring

/-- The middle column from the kernel identity: F_0 (2 X^2 W - (1 - X)(W - 1)) = W - 1. -/
lemma hF0 : F 0 * (2 * X ^ 2 * W - (1 - X) * (W - 1)) = W - 1 := by
  linear_combination (-2 : ℚ⟦X⟧) * kernel - (W - 1) * edge

/-- F_0^2 (1 - X)(1 - X - 4X^2) = 1. -/
lemma KL : F 0 ^ 2 * (1 - 2 * X - 3 * X ^ 2 + 4 * X ^ 3) = 1 := by
  have hD : (2 * X ^ 2 * W - (1 - X) * (W - 1)) ^ 2 =
      (1 - 2 * X - 3 * X ^ 2 + 4 * X ^ 3) * (W - 1) ^ 2 := by
    linear_combination (-4 * X ^ 2) * kerW
  apply mul_right_cancel₀ (pow_ne_zero 2 W_sub_one_ne)
  linear_combination (-F 0 ^ 2) * hD + (F 0 * (2 * X ^ 2 * W - (1 - X) * (W - 1)) + (W - 1)) * hF0

/-! ### The target series -/

/-- The first diagonal from the middle column: 2 X F_1 = P_1 + Q_1 F_0. -/
lemma hF1 : (2 * X) * F 1 = (-1) + (1 - X) * F 0 := by
  linear_combination (-1 : ℚ⟦X⟧) * edge

lemma hF2 : (2 * X ^ 2) * F 2 = (-1) + (1 - X - 2 * X ^ 2) * F 0 := by
  have hv : F 1 = X * (F 0 + F 2) := vert_odd 0
  linear_combination (-2 * X) * hv + (1) * hF1

lemma hF3 : (2 * X ^ 3) * F 3 = (-1 + X + X ^ 2) + (1 - 2 * X - 2 * X ^ 2 + 3 * X ^ 3) * F 0 := by
  have hv : F 2 = X * (F 1 + F 3 + F 2) := vert_even 0
  linear_combination (-2 * X ^ 2) * hv + (1 - X) * hF2 + (-X ^ 2) * hF1

lemma hF4 : (2 * X ^ 4) * F 4 = (-1 + X + 2 * X ^ 2) + (1 - 2 * X - 3 * X ^ 2 + 4 * X ^ 3 + 2 * X ^ 4) * F 0 := by
  have hv : F 3 = X * (F 2 + F 4) := vert_odd 1
  linear_combination (-2 * X ^ 3) * hv + (1) * hF3 + (-X ^ 2) * hF2

/-! ### The differential equation and the recurrence -/

/-- The middle column's differential equation, from F_0^2 R = c^2. -/
lemma ode0 : (2 - 4 * X - 6 * X ^ 2 + 8 * X ^ 3) * θ (F 0) = (2 * X + 6 * X ^ 2 - 12 * X ^ 3) * F 0 := by
  have h := congrArg θ KL
  simp only [θ_add, θ_sub, θ_mul, θ_sq, θ_X_pow, θ_X, θ_ofNat, θ_one, θ_neg, Nat.cast_ofNat] at h
  linear_combination (F 0 * (1 - 2 * X - 3 * X ^ 2 + 4 * X ^ 3)) * h - (2 * (1 - 2 * X - 3 * X ^ 2 + 4 * X ^ 3) * θ (F 0) + F 0 * (-2 * X - 6 * X ^ 2 + 12 * X ^ 3)) * KL

set_option maxHeartbeats 1600000 in
/-- Mathar's recurrence as a differential equation: L f = B. -/
lemma ode : pl [-2, 5, 4, -11, 4] * θ (θ (F 4)) + pl [0, 5, 17, -42, 14] * θ (F 4) + pl [32, -46, 36, -43, 12] * F 4 = pl [0] := by
  have e1 : (2 * X ^ 4) * F 4 = (-1 + X + 2 * X ^ 2) + (1 - 2 * X - 3 * X ^ 2 + 4 * X ^ 3 + 2 * X ^ 4) * F 0 := hF4
  have e2 : (8 * X ^ 4) * F 4 + (2 * X ^ 4) * θ (F 4) =
      (X + 4 * X ^ 2) + (-2 * X - 6 * X ^ 2 + 12 * X ^ 3 + 8 * X ^ 4) * F 0 + (1 - 2 * X - 3 * X ^ 2 + 4 * X ^ 3 + 2 * X ^ 4) * θ (F 0) := by
    have h := congrArg θ e1
    simp only [θ_add, θ_sub, θ_mul, θ_sq, θ_X_pow, θ_X, θ_ofNat, θ_one, θ_neg, Nat.cast_ofNat] at h
    linear_combination h
  have o1 := ode0
  have e3 : (32 * X ^ 4) * F 4 + 2 * ((8 * X ^ 4) * θ (F 4)) + (2 * X ^ 4) * θ (θ (F 4)) =
      (X + 8 * X ^ 2) + (-2 * X - 12 * X ^ 2 + 36 * X ^ 3 + 32 * X ^ 4) * F 0 + 2 * ((-2 * X - 6 * X ^ 2 + 12 * X ^ 3 + 8 * X ^ 4) * θ (F 0)) + (1 - 2 * X - 3 * X ^ 2 + 4 * X ^ 3 + 2 * X ^ 4) * θ (θ (F 0)) := by
    have h := congrArg θ e2
    simp only [θ_add, θ_sub, θ_mul, θ_sq, θ_X_pow, θ_X, θ_ofNat, θ_one, θ_neg, Nat.cast_ofNat] at h
    linear_combination h
  have o2 : (-4 * X - 12 * X ^ 2 + 24 * X ^ 3) * θ (F 0) + (2 - 4 * X - 6 * X ^ 2 + 8 * X ^ 3) * θ (θ (F 0)) = (2 * X + 12 * X ^ 2 - 36 * X ^ 3) * F 0 + (2 * X + 6 * X ^ 2 - 12 * X ^ 3) * θ (F 0) := by
    have h := congrArg θ o1
    simp only [θ_add, θ_sub, θ_mul, θ_sq, θ_X_pow, θ_X, θ_ofNat, θ_one, θ_neg, Nat.cast_ofNat] at h
    linear_combination h
  have hK : ((X ^ 4 * (4)) : ℚ⟦X⟧) ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) (ne_zero_of_constantCoeff (by simp [cc_ofNat]))
  have h : (X ^ 4 * (4)) * ((-2 + 5 * X + 4 * X ^ 2 - 11 * X ^ 3 + 4 * X ^ 4) * θ (θ (F 4)) + (5 * X + 17 * X ^ 2 - 42 * X ^ 3 + 14 * X ^ 4) * θ (F 4) + (32 - 46 * X + 36 * X ^ 2 - 43 * X ^ 3 + 12 * X ^ 4) * F 4) = (X ^ 4 * (4)) * 0 := by
    linear_combination (28 * X + 64 * X ^ 2 - 102 * X ^ 3 + 40 * X ^ 4) * e1 + (32 - 70 * X - 30 * X ^ 2 + 92 * X ^ 3 - 36 * X ^ 4) * e2 + (-4 + 10 * X + 8 * X ^ 2 - 22 * X ^ 3 + 8 * X ^ 4) * e3 + (16 - 33 * X - 10 * X ^ 2 + 31 * X ^ 3 - 12 * X ^ 4 - 2 * X ^ 5) * o1 + (-2 + 5 * X + 4 * X ^ 2 - 11 * X ^ 3 + 2 * X ^ 5) * o2
  have ha2 : pl [-2, 5, 4, -11, 4] = (-2 + 5 * X + 4 * X ^ 2 - 11 * X ^ 3 + 4 * X ^ 4) := by
    simp only [pl, sum_range_succ, range_zero, sum_empty, List.length_cons, List.length_nil,
      List.getD_cons_zero, List.getD_cons_succ, map_neg, map_ofNat C, map_one, map_zero]
    ring
  have ha1 : pl [0, 5, 17, -42, 14] = (5 * X + 17 * X ^ 2 - 42 * X ^ 3 + 14 * X ^ 4) := by
    simp only [pl, sum_range_succ, range_zero, sum_empty, List.length_cons, List.length_nil,
      List.getD_cons_zero, List.getD_cons_succ, map_neg, map_ofNat C, map_one, map_zero]
    ring
  have ha0 : pl [32, -46, 36, -43, 12] = (32 - 46 * X + 36 * X ^ 2 - 43 * X ^ 3 + 12 * X ^ 4) := by
    simp only [pl, sum_range_succ, range_zero, sum_empty, List.length_cons, List.length_nil,
      List.getD_cons_zero, List.getD_cons_succ, map_neg, map_ofNat C, map_one, map_zero]
    ring
  have hB : pl [0] = 0 := by
    simp only [pl, sum_range_succ, range_zero, sum_empty, List.length_cons, List.length_nil,
      List.getD_cons_zero, List.getD_cons_succ, map_neg, map_ofNat C, map_one, map_zero]
    ring
  rw [ha2, ha1, ha0, hB]
  exact mul_left_cancel₀ hK h

lemma u_a (m : ℕ) (hm : 4 ≤ m) : v m 4 = a m := by
  rw [v, if_pos hm, a]

/-- Mathar's recurrence. -/
theorem recur : ∀ n : ℕ, 8 ≤ n →
    -2 * ((n : ℤ) - 4) * ((n : ℤ) + 4) * (a n : ℤ) + (5 * (n : ℤ) ^ 2 - 5 * (n : ℤ) - 46) * (a (n - 1) : ℤ) + (4 * (n : ℤ) ^ 2 + (n : ℤ) + 18) * (a (n - 2) : ℤ) + (-11 * (n : ℤ) ^ 2 + 24 * (n : ℤ) - 16) * (a (n - 3) : ℤ) + 2 * ((n : ℤ) - 2) * (2 * (n : ℤ) - 5) * (a (n - 4) : ℤ) = 0 := by
  intro n hn
  have h := congrArg (coeff n) ode
  rw [map_add, map_add, coeff_pl_mul _ _ _ (by norm_num; omega), coeff_pl_mul _ _ _ (by norm_num; omega), coeff_pl_mul _ _ _ (by norm_num; omega), coeff_pl_big _ _ (by norm_num; omega)] at h
  simp only [coeff_θ, F, coeff_mk, sum_range_succ, sum_range_zero, zero_add, List.getD_cons_zero,
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
  have u0 : (v n 4 : ℚ) = (a n : ℚ) := by rw [u_a _ (by omega)]
  have u1 : (v (n - 1) 4 : ℚ) = (a (n - 1) : ℚ) := by rw [u_a _ (by omega)]
  have u2 : (v (n - 2) 4 : ℚ) = (a (n - 2) : ℚ) := by rw [u_a _ (by omega)]
  have u3 : (v (n - 3) 4 : ℚ) = (a (n - 3) : ℚ) := by rw [u_a _ (by omega)]
  have u4 : (v (n - 4) 4 : ℚ) = (a (n - 4) : ℚ) := by rw [u_a _ (by omega)]
  rw [u0, u1, u2, u3, u4, c1, c2, c3, c4] at h
  have goal : -2 * ((n : ℚ) - 4) * ((n : ℚ) + 4) * (a n : ℚ) + (5 * (n : ℚ) ^ 2 - 5 * (n : ℚ) - 46) * (a (n - 1) : ℚ) + (4 * (n : ℚ) ^ 2 + (n : ℚ) + 18) * (a (n - 2) : ℚ) + (-11 * (n : ℚ) ^ 2 + 24 * (n : ℚ) - 16) * (a (n - 3) : ℚ) + 2 * ((n : ℚ) - 2) * (2 * (n : ℚ) - 5) * (a (n - 4) : ℚ) = 0 := by
    linear_combination h
  exact_mod_cast goal

/-- Controls: the entry's listed terms, a(4) to a(29). -/
theorem controls :
    a 4 = 1 ∧ a 5 = 3 ∧ a 6 = 12 ∧ a 7 = 34 ∧
    a 8 = 103 ∧ a 9 = 281 ∧ a 10 = 778 ∧ a 11 = 2072 ∧
    a 12 = 5524 ∧ a 13 = 14488 ∧ a 14 = 37918 ∧ a 15 = 98474 ∧
    a 16 = 255137 ∧ a 17 = 658351 ∧ a 18 = 1695542 ∧ a 19 = 4356520 ∧
    a 20 = 11177720 ∧ a 21 = 28637452 ∧ a 22 = 73294698 ∧ a 23 = 187412326 ∧
    a 24 = 478861373 ∧ a 25 = 1222765699 ∧ a 26 = 3120722598 ∧ a 27 = 7961152560 ∧
    a 28 = 20302100415 ∧ a 29 = 51757554237 := by
  have v4 : a 4 = 1 := by decide +kernel
  have v5 : a 5 = 3 := by decide +kernel
  have v6 : a 6 = 12 := by decide +kernel
  have v7 : a 7 = 34 := by decide +kernel
  have v8 : a 8 = 103 := by
    have h := recur 8 (by norm_num)
    rw [show (8 : ℕ) - 1 = 7 from rfl, show (8 : ℕ) - 2 = 6 from rfl, show (8 : ℕ) - 3 = 5 from rfl, show (8 : ℕ) - 4 = 4 from rfl, v7, v6, v5, v4] at h
    generalize a 8 = x at h ⊢
    push_cast at h
    omega
  have v9 : a 9 = 281 := by
    have h := recur 9 (by norm_num)
    rw [show (9 : ℕ) - 1 = 8 from rfl, show (9 : ℕ) - 2 = 7 from rfl, show (9 : ℕ) - 3 = 6 from rfl, show (9 : ℕ) - 4 = 5 from rfl, v8, v7, v6, v5] at h
    generalize a 9 = x at h ⊢
    push_cast at h
    omega
  have v10 : a 10 = 778 := by
    have h := recur 10 (by norm_num)
    rw [show (10 : ℕ) - 1 = 9 from rfl, show (10 : ℕ) - 2 = 8 from rfl, show (10 : ℕ) - 3 = 7 from rfl, show (10 : ℕ) - 4 = 6 from rfl, v9, v8, v7, v6] at h
    generalize a 10 = x at h ⊢
    push_cast at h
    omega
  have v11 : a 11 = 2072 := by
    have h := recur 11 (by norm_num)
    rw [show (11 : ℕ) - 1 = 10 from rfl, show (11 : ℕ) - 2 = 9 from rfl, show (11 : ℕ) - 3 = 8 from rfl, show (11 : ℕ) - 4 = 7 from rfl, v10, v9, v8, v7] at h
    generalize a 11 = x at h ⊢
    push_cast at h
    omega
  have v12 : a 12 = 5524 := by
    have h := recur 12 (by norm_num)
    rw [show (12 : ℕ) - 1 = 11 from rfl, show (12 : ℕ) - 2 = 10 from rfl, show (12 : ℕ) - 3 = 9 from rfl, show (12 : ℕ) - 4 = 8 from rfl, v11, v10, v9, v8] at h
    generalize a 12 = x at h ⊢
    push_cast at h
    omega
  have v13 : a 13 = 14488 := by
    have h := recur 13 (by norm_num)
    rw [show (13 : ℕ) - 1 = 12 from rfl, show (13 : ℕ) - 2 = 11 from rfl, show (13 : ℕ) - 3 = 10 from rfl, show (13 : ℕ) - 4 = 9 from rfl, v12, v11, v10, v9] at h
    generalize a 13 = x at h ⊢
    push_cast at h
    omega
  have v14 : a 14 = 37918 := by
    have h := recur 14 (by norm_num)
    rw [show (14 : ℕ) - 1 = 13 from rfl, show (14 : ℕ) - 2 = 12 from rfl, show (14 : ℕ) - 3 = 11 from rfl, show (14 : ℕ) - 4 = 10 from rfl, v13, v12, v11, v10] at h
    generalize a 14 = x at h ⊢
    push_cast at h
    omega
  have v15 : a 15 = 98474 := by
    have h := recur 15 (by norm_num)
    rw [show (15 : ℕ) - 1 = 14 from rfl, show (15 : ℕ) - 2 = 13 from rfl, show (15 : ℕ) - 3 = 12 from rfl, show (15 : ℕ) - 4 = 11 from rfl, v14, v13, v12, v11] at h
    generalize a 15 = x at h ⊢
    push_cast at h
    omega
  have v16 : a 16 = 255137 := by
    have h := recur 16 (by norm_num)
    rw [show (16 : ℕ) - 1 = 15 from rfl, show (16 : ℕ) - 2 = 14 from rfl, show (16 : ℕ) - 3 = 13 from rfl, show (16 : ℕ) - 4 = 12 from rfl, v15, v14, v13, v12] at h
    generalize a 16 = x at h ⊢
    push_cast at h
    omega
  have v17 : a 17 = 658351 := by
    have h := recur 17 (by norm_num)
    rw [show (17 : ℕ) - 1 = 16 from rfl, show (17 : ℕ) - 2 = 15 from rfl, show (17 : ℕ) - 3 = 14 from rfl, show (17 : ℕ) - 4 = 13 from rfl, v16, v15, v14, v13] at h
    generalize a 17 = x at h ⊢
    push_cast at h
    omega
  have v18 : a 18 = 1695542 := by
    have h := recur 18 (by norm_num)
    rw [show (18 : ℕ) - 1 = 17 from rfl, show (18 : ℕ) - 2 = 16 from rfl, show (18 : ℕ) - 3 = 15 from rfl, show (18 : ℕ) - 4 = 14 from rfl, v17, v16, v15, v14] at h
    generalize a 18 = x at h ⊢
    push_cast at h
    omega
  have v19 : a 19 = 4356520 := by
    have h := recur 19 (by norm_num)
    rw [show (19 : ℕ) - 1 = 18 from rfl, show (19 : ℕ) - 2 = 17 from rfl, show (19 : ℕ) - 3 = 16 from rfl, show (19 : ℕ) - 4 = 15 from rfl, v18, v17, v16, v15] at h
    generalize a 19 = x at h ⊢
    push_cast at h
    omega
  have v20 : a 20 = 11177720 := by
    have h := recur 20 (by norm_num)
    rw [show (20 : ℕ) - 1 = 19 from rfl, show (20 : ℕ) - 2 = 18 from rfl, show (20 : ℕ) - 3 = 17 from rfl, show (20 : ℕ) - 4 = 16 from rfl, v19, v18, v17, v16] at h
    generalize a 20 = x at h ⊢
    push_cast at h
    omega
  have v21 : a 21 = 28637452 := by
    have h := recur 21 (by norm_num)
    rw [show (21 : ℕ) - 1 = 20 from rfl, show (21 : ℕ) - 2 = 19 from rfl, show (21 : ℕ) - 3 = 18 from rfl, show (21 : ℕ) - 4 = 17 from rfl, v20, v19, v18, v17] at h
    generalize a 21 = x at h ⊢
    push_cast at h
    omega
  have v22 : a 22 = 73294698 := by
    have h := recur 22 (by norm_num)
    rw [show (22 : ℕ) - 1 = 21 from rfl, show (22 : ℕ) - 2 = 20 from rfl, show (22 : ℕ) - 3 = 19 from rfl, show (22 : ℕ) - 4 = 18 from rfl, v21, v20, v19, v18] at h
    generalize a 22 = x at h ⊢
    push_cast at h
    omega
  have v23 : a 23 = 187412326 := by
    have h := recur 23 (by norm_num)
    rw [show (23 : ℕ) - 1 = 22 from rfl, show (23 : ℕ) - 2 = 21 from rfl, show (23 : ℕ) - 3 = 20 from rfl, show (23 : ℕ) - 4 = 19 from rfl, v22, v21, v20, v19] at h
    generalize a 23 = x at h ⊢
    push_cast at h
    omega
  have v24 : a 24 = 478861373 := by
    have h := recur 24 (by norm_num)
    rw [show (24 : ℕ) - 1 = 23 from rfl, show (24 : ℕ) - 2 = 22 from rfl, show (24 : ℕ) - 3 = 21 from rfl, show (24 : ℕ) - 4 = 20 from rfl, v23, v22, v21, v20] at h
    generalize a 24 = x at h ⊢
    push_cast at h
    omega
  have v25 : a 25 = 1222765699 := by
    have h := recur 25 (by norm_num)
    rw [show (25 : ℕ) - 1 = 24 from rfl, show (25 : ℕ) - 2 = 23 from rfl, show (25 : ℕ) - 3 = 22 from rfl, show (25 : ℕ) - 4 = 21 from rfl, v24, v23, v22, v21] at h
    generalize a 25 = x at h ⊢
    push_cast at h
    omega
  have v26 : a 26 = 3120722598 := by
    have h := recur 26 (by norm_num)
    rw [show (26 : ℕ) - 1 = 25 from rfl, show (26 : ℕ) - 2 = 24 from rfl, show (26 : ℕ) - 3 = 23 from rfl, show (26 : ℕ) - 4 = 22 from rfl, v25, v24, v23, v22] at h
    generalize a 26 = x at h ⊢
    push_cast at h
    omega
  have v27 : a 27 = 7961152560 := by
    have h := recur 27 (by norm_num)
    rw [show (27 : ℕ) - 1 = 26 from rfl, show (27 : ℕ) - 2 = 25 from rfl, show (27 : ℕ) - 3 = 24 from rfl, show (27 : ℕ) - 4 = 23 from rfl, v26, v25, v24, v23] at h
    generalize a 27 = x at h ⊢
    push_cast at h
    omega
  have v28 : a 28 = 20302100415 := by
    have h := recur 28 (by norm_num)
    rw [show (28 : ℕ) - 1 = 27 from rfl, show (28 : ℕ) - 2 = 26 from rfl, show (28 : ℕ) - 3 = 25 from rfl, show (28 : ℕ) - 4 = 24 from rfl, v27, v26, v25, v24] at h
    generalize a 28 = x at h ⊢
    push_cast at h
    omega
  have v29 : a 29 = 51757554237 := by
    have h := recur 29 (by norm_num)
    rw [show (29 : ℕ) - 1 = 28 from rfl, show (29 : ℕ) - 2 = 27 from rfl, show (29 : ℕ) - 3 = 26 from rfl, show (29 : ℕ) - 4 = 25 from rfl, v28, v27, v26, v25] at h
    generalize a 29 = x at h ⊢
    push_cast at h
    omega
  exact ⟨v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29⟩

/-- Mathar's conjecture. -/
theorem conjecture : ∀ n : ℕ, 8 ≤ n →
      -2 * ((n : ℤ) - 4) * ((n : ℤ) + 4) * (a n : ℤ) + (5 * (n : ℤ) ^ 2 - 5 * (n : ℤ) - 46) * (a (n - 1) : ℤ) + (4 * (n : ℤ) ^ 2 + (n : ℤ) + 18) * (a (n - 2) : ℤ) + (-11 * (n : ℤ) ^ 2 + 24 * (n : ℤ) - 16) * (a (n - 3) : ℤ) + 2 * ((n : ℤ) - 2) * (2 * (n : ℤ) - 5) * (a (n - 4) : ℤ) = 0 :=
  recur

end OMA.S_oeis_a026573

theorem OMA.solution : type_of% @OMA.S_oeis_a026573.main :=
  OMA.S_oeis_a026573.conjecture
