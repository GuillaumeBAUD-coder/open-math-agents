import OMAStatements.S_oeis_a026580

/-!
OEIS A026580 (Clark Kimberling): T(n,0) + T(n,1) + ... + T(n,n), T given by A026568.
Conjecture: n*a(n) +(n-2)*a(n-1) +(-17*n+28)*a(n-2) +5*(-n+4)*a(n-3) +2*(34*n-107)*a(n-4) +16*(n-5)*a(n-5) +32*(-2*n+9)*a(n-6)=0.

Proof (kernel method on the half rows). With v(n, s) = T(n, n - s), the number of strings of the
comment of A026568 that end at s, the symmetry of the rows gives the recursion of v on s >= 0 (from
even values the strings may stay) with the middle column v(n+1, 0) = v(n, 0) + 2 v(n, 1) (`v_rec`,
`v_edge`). The even and odd parts of the half rows, alpha_n(z) = sum_m v(n, 2m) z^m and beta_n(z) =
sum_m v(n, 2m+1) z^m, satisfy z beta_(n+1) = (z + 1) alpha_n - v(n, 0) and alpha_(n+1) = alpha_n +
(z + 1) beta_n + v(n, 1) (`polyI`, `polyII`). At the root z = W - 1 of the kernel z (1 - X) = X^2 (z
+ 1)^2 (`kerW`) the half rows telescope (`ker_partial`, `kernel`), and with the middle column this
gives F_0^2 (1 - X)(1 - X - 4X^2) = 1 for F_0 = sum_n v(n, 0) X^n (`hF0`, `KL`). The parts at z = 1
give the series G of the half-row sums: 2(1 - X - 4X^2) G = 1 + 2 * X + (1 - X - 4X^2) F_0 (`evI`,
`evII`, `hG`). So F_0 satisfies a first-order differential equation in θ = X d/dX (`ode0`), and
Mathar's recurrence is the differential equation L f = B for the target series f, an identity linear
in F_0 (`ode`); its coefficient of X^n is the recurrence (`recur`).
-/

namespace OMA.S_oeis_a026580

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

/-- The even and odd parts of the half rows at z = 1. -/
noncomputable def As : ℚ⟦X⟧ := PowerSeries.mk fun n => (α n).eval 1

noncomputable def Bs : ℚ⟦X⟧ := PowerSeries.mk fun n => (β n).eval 1

lemma evI : Bs = X * (As + As - F 0) := by
  ext n
  rcases n with _ | m
  · have : v 0 1 = 0 := by decide
    simp [Bs, β, this]
  · have h := congrArg (Polynomial.eval 1) (polyI m)
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_one, one_mul] at h
    rw [coeff_succ_X_mul]
    simp only [As, Bs, F, map_sub, map_add, coeff_mk]
    linear_combination h

lemma evII : As = 1 + X * (As + Bs + Bs + F 1) := by
  ext n
  rcases n with _ | m
  · have : v 0 0 = 1 := by decide
    simp [As, α, this]
  · have h := congrArg (Polynomial.eval 1) (polyII m)
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_one] at h
    rw [map_add, coeff_succ_X_mul, coeff_one, if_neg (by omega), zero_add]
    simp only [As, Bs, F, map_add, coeff_mk]
    linear_combination h

lemma sum_split (g : ℕ → ℚ) (N : ℕ) :
    ∑ s ∈ range (2 * N), g s = ∑ m ∈ range N, (g (2 * m) + g (2 * m + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, sum_range_succ]
    ring

/-- The half row through its parts: T(n, 0) + ... + T(n, n) = alpha_n(1) + beta_n(1). -/
lemma half_eq (n : ℕ) :
    ((∑ j ∈ range (n + 1), T n j : ℕ) : ℚ) = (α n).eval 1 + (β n).eval 1 := by
  have h1 : ∑ j ∈ range (n + 1), T n j = ∑ s ∈ range (n + 1), v n s := by
    rw [← sum_range_reflect]
    refine sum_congr rfl (fun s hs => ?_)
    rw [mem_range] at hs
    rw [v_eqT n s (by omega), show n + 1 - 1 - s = n - s by omega]
  have h2 : ∑ s ∈ range (n + 1), (v n s : ℚ) = ∑ s ∈ range (2 * (n + 1)), (v n s : ℚ) := by
    apply sum_subset
    · intro s hs
      rw [mem_range] at hs ⊢
      omega
    · intro s _ hs
      rw [mem_range] at hs
      rw [v_big n s (by omega)]
      simp
  rw [h1]
  push_cast
  rw [h2, sum_split, sum_add_distrib]
  simp only [α, β, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one]

/-- The half-row sums as a series. -/
noncomputable def G : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

lemma G_eq : G = As + Bs := by
  ext n
  simp only [G, As, Bs, coeff_mk, map_add]
  exact half_eq n

lemma hG : (2 - 2 * X - 8 * X ^ 2) * G = (1 + 2 * X) + (1 - X - 4 * X ^ 2) * F 0 := by
  linear_combination (2 + 2 * X) * evI + (2 + 4 * X) * evII + (1 + 2 * X) * hF1 + (2 - 2 * X - 8 * X ^ 2) * G_eq

/-! ### The differential equation and the recurrence -/

/-- The middle column's differential equation, from F_0^2 R = c^2. -/
lemma ode0 : (2 - 4 * X - 6 * X ^ 2 + 8 * X ^ 3) * θ (F 0) = (2 * X + 6 * X ^ 2 - 12 * X ^ 3) * F 0 := by
  have h := congrArg θ KL
  simp only [θ_add, θ_sub, θ_mul, θ_sq, θ_X_pow, θ_X, θ_ofNat, θ_one, θ_neg, Nat.cast_ofNat] at h
  linear_combination (F 0 * (1 - 2 * X - 3 * X ^ 2 + 4 * X ^ 3)) * h - (2 * (1 - 2 * X - 3 * X ^ 2 + 4 * X ^ 3) * θ (F 0) + F 0 * (-2 * X - 6 * X ^ 2 + 12 * X ^ 3)) * KL

/-- Mathar's recurrence as a differential equation: L f = B. -/
lemma ode : pl [1, 1, -17, -5, 68, 16, -64] * θ (G) + pl [0, -1, -6, 5, 58, 0, -96] * G = pl [0, 1, 4, 0, 2, 8] := by
  have e1 : (2 - 2 * X - 8 * X ^ 2) * G = (1 + 2 * X) + (1 - X - 4 * X ^ 2) * F 0 := hG
  have e2 : (-2 * X - 16 * X ^ 2) * G + (2 - 2 * X - 8 * X ^ 2) * θ (G) =
      (2 * X) + (-X - 8 * X ^ 2) * F 0 + (1 - X - 4 * X ^ 2) * θ (F 0) := by
    have h := congrArg θ e1
    simp only [θ_add, θ_sub, θ_mul, θ_sq, θ_X_pow, θ_X, θ_ofNat, θ_one, θ_neg, Nat.cast_ofNat] at h
    linear_combination h
  have o1 := ode0
  have hK : ((4) : ℚ⟦X⟧) ≠ 0 := ne_zero_of_constantCoeff (by simp [cc_ofNat])
  have h : (4) * ((1 + X - 17 * X ^ 2 - 5 * X ^ 3 + 68 * X ^ 4 + 16 * X ^ 5 - 64 * X ^ 6) * θ (G) + (-X - 6 * X ^ 2 + 5 * X ^ 3 + 58 * X ^ 4 - 96 * X ^ 6) * G) = (4) * (X + 4 * X ^ 2 + 2 * X ^ 4 + 8 * X ^ 5) := by
    linear_combination (8 * X ^ 2 + 28 * X ^ 3 - 16 * X ^ 4) * e1 + (2 + 4 * X - 22 * X ^ 2 - 16 * X ^ 3 + 32 * X ^ 4) * e2 + (1 + 3 * X - 8 * X ^ 2 - 16 * X ^ 3) * o1
  have ha1 : pl [1, 1, -17, -5, 68, 16, -64] = (1 + X - 17 * X ^ 2 - 5 * X ^ 3 + 68 * X ^ 4 + 16 * X ^ 5 - 64 * X ^ 6) := by
    simp only [pl, sum_range_succ, range_zero, sum_empty, List.length_cons, List.length_nil,
      List.getD_cons_zero, List.getD_cons_succ, map_neg, map_ofNat C, map_one, map_zero]
    ring
  have ha0 : pl [0, -1, -6, 5, 58, 0, -96] = (-X - 6 * X ^ 2 + 5 * X ^ 3 + 58 * X ^ 4 - 96 * X ^ 6) := by
    simp only [pl, sum_range_succ, range_zero, sum_empty, List.length_cons, List.length_nil,
      List.getD_cons_zero, List.getD_cons_succ, map_neg, map_ofNat C, map_one, map_zero]
    ring
  have hB : pl [0, 1, 4, 0, 2, 8] = (X + 4 * X ^ 2 + 2 * X ^ 4 + 8 * X ^ 5) := by
    simp only [pl, sum_range_succ, range_zero, sum_empty, List.length_cons, List.length_nil,
      List.getD_cons_zero, List.getD_cons_succ, map_neg, map_ofNat C, map_one, map_zero]
    ring
  rw [ha1, ha0, hB]
  exact mul_left_cancel₀ hK h

/-- Mathar's recurrence. -/
theorem recur : ∀ n : ℕ, 6 ≤ n →
    (n : ℤ) * (a n : ℤ) + ((n : ℤ) - 2) * (a (n - 1) : ℤ) + (-17 * (n : ℤ) + 28) * (a (n - 2) : ℤ) + 5 * (-(n : ℤ) + 4) * (a (n - 3) : ℤ) + 2 * (34 * (n : ℤ) - 107) * (a (n - 4) : ℤ) + 16 * ((n : ℤ) - 5) * (a (n - 5) : ℤ) + 32 * (-2 * (n : ℤ) + 9) * (a (n - 6) : ℤ) = 0 := by
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
  have goal : (n : ℚ) * (a n : ℚ) + ((n : ℚ) - 2) * (a (n - 1) : ℚ) + (-17 * (n : ℚ) + 28) * (a (n - 2) : ℚ) + 5 * (-(n : ℚ) + 4) * (a (n - 3) : ℚ) + 2 * (34 * (n : ℚ) - 107) * (a (n - 4) : ℚ) + 16 * ((n : ℚ) - 5) * (a (n - 5) : ℚ) + 32 * (-2 * (n : ℚ) + 9) * (a (n - 6) : ℚ) = 0 := by
    linear_combination h
  exact_mod_cast goal

/-- Controls: the entry's listed terms, a(0) to a(27). -/
theorem controls :
    a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 5 ∧ a 3 = 12 ∧
    a 4 = 30 ∧ a 5 = 75 ∧ a 6 = 189 ∧ a 7 = 478 ∧
    a 8 = 1211 ∧ a 9 = 3076 ∧ a 10 = 7818 ∧ a 11 = 19901 ∧
    a 12 = 50680 ∧ a 13 = 129179 ∧ a 14 = 329383 ∧ a 15 = 840336 ∧
    a 16 = 2144540 ∧ a 17 = 5474889 ∧ a 18 = 13980493 ∧ a 19 = 35709394 ∧
    a 20 = 91228015 ∧ a 21 = 233108456 ∧ a 22 = 595740568 ∧ a 23 = 1522725379 ∧
    a 24 = 3892624055 ∧ a 25 = 9952119054 ∧ a 26 = 25446913766 ∧ a 27 = 65072487645 := by
  have v0 : a 0 = 1 := by decide +kernel
  have v1 : a 1 = 2 := by decide +kernel
  have v2 : a 2 = 5 := by decide +kernel
  have v3 : a 3 = 12 := by decide +kernel
  have v4 : a 4 = 30 := by decide +kernel
  have v5 : a 5 = 75 := by decide +kernel
  have v6 : a 6 = 189 := by
    have h := recur 6 (by norm_num)
    rw [show (6 : ℕ) - 1 = 5 from rfl, show (6 : ℕ) - 2 = 4 from rfl, show (6 : ℕ) - 3 = 3 from rfl, show (6 : ℕ) - 4 = 2 from rfl, show (6 : ℕ) - 5 = 1 from rfl, show (6 : ℕ) - 6 = 0 from rfl, v5, v4, v3, v2, v1, v0] at h
    generalize a 6 = x at h ⊢
    push_cast at h
    omega
  have v7 : a 7 = 478 := by
    have h := recur 7 (by norm_num)
    rw [show (7 : ℕ) - 1 = 6 from rfl, show (7 : ℕ) - 2 = 5 from rfl, show (7 : ℕ) - 3 = 4 from rfl, show (7 : ℕ) - 4 = 3 from rfl, show (7 : ℕ) - 5 = 2 from rfl, show (7 : ℕ) - 6 = 1 from rfl, v6, v5, v4, v3, v2, v1] at h
    generalize a 7 = x at h ⊢
    push_cast at h
    omega
  have v8 : a 8 = 1211 := by
    have h := recur 8 (by norm_num)
    rw [show (8 : ℕ) - 1 = 7 from rfl, show (8 : ℕ) - 2 = 6 from rfl, show (8 : ℕ) - 3 = 5 from rfl, show (8 : ℕ) - 4 = 4 from rfl, show (8 : ℕ) - 5 = 3 from rfl, show (8 : ℕ) - 6 = 2 from rfl, v7, v6, v5, v4, v3, v2] at h
    generalize a 8 = x at h ⊢
    push_cast at h
    omega
  have v9 : a 9 = 3076 := by
    have h := recur 9 (by norm_num)
    rw [show (9 : ℕ) - 1 = 8 from rfl, show (9 : ℕ) - 2 = 7 from rfl, show (9 : ℕ) - 3 = 6 from rfl, show (9 : ℕ) - 4 = 5 from rfl, show (9 : ℕ) - 5 = 4 from rfl, show (9 : ℕ) - 6 = 3 from rfl, v8, v7, v6, v5, v4, v3] at h
    generalize a 9 = x at h ⊢
    push_cast at h
    omega
  have v10 : a 10 = 7818 := by
    have h := recur 10 (by norm_num)
    rw [show (10 : ℕ) - 1 = 9 from rfl, show (10 : ℕ) - 2 = 8 from rfl, show (10 : ℕ) - 3 = 7 from rfl, show (10 : ℕ) - 4 = 6 from rfl, show (10 : ℕ) - 5 = 5 from rfl, show (10 : ℕ) - 6 = 4 from rfl, v9, v8, v7, v6, v5, v4] at h
    generalize a 10 = x at h ⊢
    push_cast at h
    omega
  have v11 : a 11 = 19901 := by
    have h := recur 11 (by norm_num)
    rw [show (11 : ℕ) - 1 = 10 from rfl, show (11 : ℕ) - 2 = 9 from rfl, show (11 : ℕ) - 3 = 8 from rfl, show (11 : ℕ) - 4 = 7 from rfl, show (11 : ℕ) - 5 = 6 from rfl, show (11 : ℕ) - 6 = 5 from rfl, v10, v9, v8, v7, v6, v5] at h
    generalize a 11 = x at h ⊢
    push_cast at h
    omega
  have v12 : a 12 = 50680 := by
    have h := recur 12 (by norm_num)
    rw [show (12 : ℕ) - 1 = 11 from rfl, show (12 : ℕ) - 2 = 10 from rfl, show (12 : ℕ) - 3 = 9 from rfl, show (12 : ℕ) - 4 = 8 from rfl, show (12 : ℕ) - 5 = 7 from rfl, show (12 : ℕ) - 6 = 6 from rfl, v11, v10, v9, v8, v7, v6] at h
    generalize a 12 = x at h ⊢
    push_cast at h
    omega
  have v13 : a 13 = 129179 := by
    have h := recur 13 (by norm_num)
    rw [show (13 : ℕ) - 1 = 12 from rfl, show (13 : ℕ) - 2 = 11 from rfl, show (13 : ℕ) - 3 = 10 from rfl, show (13 : ℕ) - 4 = 9 from rfl, show (13 : ℕ) - 5 = 8 from rfl, show (13 : ℕ) - 6 = 7 from rfl, v12, v11, v10, v9, v8, v7] at h
    generalize a 13 = x at h ⊢
    push_cast at h
    omega
  have v14 : a 14 = 329383 := by
    have h := recur 14 (by norm_num)
    rw [show (14 : ℕ) - 1 = 13 from rfl, show (14 : ℕ) - 2 = 12 from rfl, show (14 : ℕ) - 3 = 11 from rfl, show (14 : ℕ) - 4 = 10 from rfl, show (14 : ℕ) - 5 = 9 from rfl, show (14 : ℕ) - 6 = 8 from rfl, v13, v12, v11, v10, v9, v8] at h
    generalize a 14 = x at h ⊢
    push_cast at h
    omega
  have v15 : a 15 = 840336 := by
    have h := recur 15 (by norm_num)
    rw [show (15 : ℕ) - 1 = 14 from rfl, show (15 : ℕ) - 2 = 13 from rfl, show (15 : ℕ) - 3 = 12 from rfl, show (15 : ℕ) - 4 = 11 from rfl, show (15 : ℕ) - 5 = 10 from rfl, show (15 : ℕ) - 6 = 9 from rfl, v14, v13, v12, v11, v10, v9] at h
    generalize a 15 = x at h ⊢
    push_cast at h
    omega
  have v16 : a 16 = 2144540 := by
    have h := recur 16 (by norm_num)
    rw [show (16 : ℕ) - 1 = 15 from rfl, show (16 : ℕ) - 2 = 14 from rfl, show (16 : ℕ) - 3 = 13 from rfl, show (16 : ℕ) - 4 = 12 from rfl, show (16 : ℕ) - 5 = 11 from rfl, show (16 : ℕ) - 6 = 10 from rfl, v15, v14, v13, v12, v11, v10] at h
    generalize a 16 = x at h ⊢
    push_cast at h
    omega
  have v17 : a 17 = 5474889 := by
    have h := recur 17 (by norm_num)
    rw [show (17 : ℕ) - 1 = 16 from rfl, show (17 : ℕ) - 2 = 15 from rfl, show (17 : ℕ) - 3 = 14 from rfl, show (17 : ℕ) - 4 = 13 from rfl, show (17 : ℕ) - 5 = 12 from rfl, show (17 : ℕ) - 6 = 11 from rfl, v16, v15, v14, v13, v12, v11] at h
    generalize a 17 = x at h ⊢
    push_cast at h
    omega
  have v18 : a 18 = 13980493 := by
    have h := recur 18 (by norm_num)
    rw [show (18 : ℕ) - 1 = 17 from rfl, show (18 : ℕ) - 2 = 16 from rfl, show (18 : ℕ) - 3 = 15 from rfl, show (18 : ℕ) - 4 = 14 from rfl, show (18 : ℕ) - 5 = 13 from rfl, show (18 : ℕ) - 6 = 12 from rfl, v17, v16, v15, v14, v13, v12] at h
    generalize a 18 = x at h ⊢
    push_cast at h
    omega
  have v19 : a 19 = 35709394 := by
    have h := recur 19 (by norm_num)
    rw [show (19 : ℕ) - 1 = 18 from rfl, show (19 : ℕ) - 2 = 17 from rfl, show (19 : ℕ) - 3 = 16 from rfl, show (19 : ℕ) - 4 = 15 from rfl, show (19 : ℕ) - 5 = 14 from rfl, show (19 : ℕ) - 6 = 13 from rfl, v18, v17, v16, v15, v14, v13] at h
    generalize a 19 = x at h ⊢
    push_cast at h
    omega
  have v20 : a 20 = 91228015 := by
    have h := recur 20 (by norm_num)
    rw [show (20 : ℕ) - 1 = 19 from rfl, show (20 : ℕ) - 2 = 18 from rfl, show (20 : ℕ) - 3 = 17 from rfl, show (20 : ℕ) - 4 = 16 from rfl, show (20 : ℕ) - 5 = 15 from rfl, show (20 : ℕ) - 6 = 14 from rfl, v19, v18, v17, v16, v15, v14] at h
    generalize a 20 = x at h ⊢
    push_cast at h
    omega
  have v21 : a 21 = 233108456 := by
    have h := recur 21 (by norm_num)
    rw [show (21 : ℕ) - 1 = 20 from rfl, show (21 : ℕ) - 2 = 19 from rfl, show (21 : ℕ) - 3 = 18 from rfl, show (21 : ℕ) - 4 = 17 from rfl, show (21 : ℕ) - 5 = 16 from rfl, show (21 : ℕ) - 6 = 15 from rfl, v20, v19, v18, v17, v16, v15] at h
    generalize a 21 = x at h ⊢
    push_cast at h
    omega
  have v22 : a 22 = 595740568 := by
    have h := recur 22 (by norm_num)
    rw [show (22 : ℕ) - 1 = 21 from rfl, show (22 : ℕ) - 2 = 20 from rfl, show (22 : ℕ) - 3 = 19 from rfl, show (22 : ℕ) - 4 = 18 from rfl, show (22 : ℕ) - 5 = 17 from rfl, show (22 : ℕ) - 6 = 16 from rfl, v21, v20, v19, v18, v17, v16] at h
    generalize a 22 = x at h ⊢
    push_cast at h
    omega
  have v23 : a 23 = 1522725379 := by
    have h := recur 23 (by norm_num)
    rw [show (23 : ℕ) - 1 = 22 from rfl, show (23 : ℕ) - 2 = 21 from rfl, show (23 : ℕ) - 3 = 20 from rfl, show (23 : ℕ) - 4 = 19 from rfl, show (23 : ℕ) - 5 = 18 from rfl, show (23 : ℕ) - 6 = 17 from rfl, v22, v21, v20, v19, v18, v17] at h
    generalize a 23 = x at h ⊢
    push_cast at h
    omega
  have v24 : a 24 = 3892624055 := by
    have h := recur 24 (by norm_num)
    rw [show (24 : ℕ) - 1 = 23 from rfl, show (24 : ℕ) - 2 = 22 from rfl, show (24 : ℕ) - 3 = 21 from rfl, show (24 : ℕ) - 4 = 20 from rfl, show (24 : ℕ) - 5 = 19 from rfl, show (24 : ℕ) - 6 = 18 from rfl, v23, v22, v21, v20, v19, v18] at h
    generalize a 24 = x at h ⊢
    push_cast at h
    omega
  have v25 : a 25 = 9952119054 := by
    have h := recur 25 (by norm_num)
    rw [show (25 : ℕ) - 1 = 24 from rfl, show (25 : ℕ) - 2 = 23 from rfl, show (25 : ℕ) - 3 = 22 from rfl, show (25 : ℕ) - 4 = 21 from rfl, show (25 : ℕ) - 5 = 20 from rfl, show (25 : ℕ) - 6 = 19 from rfl, v24, v23, v22, v21, v20, v19] at h
    generalize a 25 = x at h ⊢
    push_cast at h
    omega
  have v26 : a 26 = 25446913766 := by
    have h := recur 26 (by norm_num)
    rw [show (26 : ℕ) - 1 = 25 from rfl, show (26 : ℕ) - 2 = 24 from rfl, show (26 : ℕ) - 3 = 23 from rfl, show (26 : ℕ) - 4 = 22 from rfl, show (26 : ℕ) - 5 = 21 from rfl, show (26 : ℕ) - 6 = 20 from rfl, v25, v24, v23, v22, v21, v20] at h
    generalize a 26 = x at h ⊢
    push_cast at h
    omega
  have v27 : a 27 = 65072487645 := by
    have h := recur 27 (by norm_num)
    rw [show (27 : ℕ) - 1 = 26 from rfl, show (27 : ℕ) - 2 = 25 from rfl, show (27 : ℕ) - 3 = 24 from rfl, show (27 : ℕ) - 4 = 23 from rfl, show (27 : ℕ) - 5 = 22 from rfl, show (27 : ℕ) - 6 = 21 from rfl, v26, v25, v24, v23, v22, v21] at h
    generalize a 27 = x at h ⊢
    push_cast at h
    omega
  exact ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27⟩

/-- Mathar's conjecture. -/
theorem conjecture : ∀ n : ℕ, 6 ≤ n →
      (n : ℤ) * (a n : ℤ) + ((n : ℤ) - 2) * (a (n - 1) : ℤ) + (-17 * (n : ℤ) + 28) * (a (n - 2) : ℤ) + 5 * (-(n : ℤ) + 4) * (a (n - 3) : ℤ) + 2 * (34 * (n : ℤ) - 107) * (a (n - 4) : ℤ) + 16 * ((n : ℤ) - 5) * (a (n - 5) : ℤ) + 32 * (-2 * (n : ℤ) + 9) * (a (n - 6) : ℤ) = 0 :=
  recur

end OMA.S_oeis_a026580

theorem OMA.solution : type_of% @OMA.S_oeis_a026580.main :=
  OMA.S_oeis_a026580.conjecture
