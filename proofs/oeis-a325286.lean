import OMAStatements.S_oeis_a325286
import Mathlib

namespace OMA.S_oeis_a325286

-- 1. Geometric / binomial HasSum: ∑_{n=0}^∞ C(n, j) / 2^(n+1) = 1
private lemma hasSum_half_pow : HasSum (fun n : ℕ => (1 : ℝ) / 2 ^ (n + 1)) 1 := by
  have hgeom : HasSum (fun n : ℕ => ((1 / 2 : ℝ)) ^ n) ((1 - 1 / 2 : ℝ)⁻¹) :=
    hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
  have hmul := hgeom.mul_left (1 / 2 : ℝ)
  have hval : (1 / 2 : ℝ) * (1 - 1 / 2 : ℝ)⁻¹ = 1 := by norm_num
  rw [hval] at hmul
  refine hmul.congr_fun fun n => ?_
  rw [pow_succ, one_div, one_div, inv_pow]
  ring

private lemma sum_range_choose (n j : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.choose k j = Nat.choose (n + 1) (j + 1) := by
  induction n with
  | zero => cases j <;> simp [Nat.choose_eq_zero_of_lt]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, add_comm, ← Nat.choose_succ_succ]

private lemma hasSum_choose_div_pow2 :
    ∀ j : ℕ, HasSum (fun n : ℕ => (Nat.choose n j : ℝ) / 2 ^ (n + 1)) 1 := by
  intro j
  induction j with
  | zero =>
    simpa only [Nat.choose_zero_right, Nat.cast_one] using hasSum_half_pow
  | succ j ih =>
    have hs1 : Summable (fun n : ℕ => ‖(Nat.choose n j : ℝ) / 2 ^ (n + 1)‖) := by
      refine Summable.congr ih.summable fun n => ?_
      rw [Real.norm_of_nonneg (by positivity)]
    have hs2 : Summable (fun n : ℕ => ‖(1 : ℝ) / 2 ^ (n + 1)‖) := by
      refine Summable.congr hasSum_half_pow.summable fun n => ?_
      rw [Real.norm_of_nonneg (by positivity)]
    have hprod := hasSum_sum_range_mul_of_summable_norm hs1 hs2
    rw [ih.tsum_eq, hasSum_half_pow.tsum_eq, mul_one] at hprod
    have hshift : HasSum (fun n : ℕ => (Nat.choose (n + 1) (j + 1) : ℝ) / 2 ^ (n + 2)) 1 := by
      refine hprod.congr_fun fun n => ?_
      have hterm : ∀ k ∈ Finset.range (n + 1),
          ((Nat.choose k j : ℝ) / 2 ^ (k + 1)) * ((1 : ℝ) / 2 ^ (n - k + 1)) =
          (Nat.choose k j : ℝ) / 2 ^ (n + 2) := by
        intro k hk
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [div_mul_div_comm, mul_one, ← pow_add, show k + 1 + (n - k + 1) = n + 2 by omega]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← Nat.cast_sum, sum_range_choose]
    have h0 : (Nat.choose 0 (j + 1) : ℝ) / 2 ^ (0 + 1) = 0 := by simp
    have hfull := (hasSum_nat_add_iff' 1 (f := fun n : ℕ => (Nat.choose n (j + 1) : ℝ) / 2 ^ (n + 1))).mp
      (by simpa [h0] using hshift)
    simpa [h0] using hfull

-- 2. Finite difference operators & even-polynomial divisibility by 3
private def Δ (f : ℤ → ℤ) : ℤ → ℤ := fun n => f (n + 1) - f n
private def U (f : ℤ → ℤ) : ℤ → ℤ := fun n => f (n + 1) + f (n - 1) - 2 * f n

private def Δn : ℕ → (ℤ → ℤ) → (ℤ → ℤ)
  | 0, f => f
  | d + 1, f => Δ (Δn d f)

private def S (d : ℕ) (f : ℤ → ℤ) : ℤ :=
  ∑ j ∈ Finset.range (d + 1), Δn j f 0

private lemma Δn_add (d : ℕ) (f g : ℤ → ℤ) :
    Δn d (fun n => f n + g n) = fun n => Δn d f n + Δn d g n := by
  induction d with
  | zero => rfl
  | succ d ih => funext n; simp only [Δn, Δ, ih]; ring

private lemma Δn_sub (d : ℕ) (f g : ℤ → ℤ) :
    Δn d (fun n => f n - g n) = fun n => Δn d f n - Δn d g n := by
  induction d with
  | zero => rfl
  | succ d ih => funext n; simp only [Δn, Δ, ih]; ring

private lemma Δn_const_mul (d : ℕ) (c : ℤ) (f : ℤ → ℤ) :
    Δn d (fun n => c * f n) = fun n => c * Δn d f n := by
  induction d with
  | zero => rfl
  | succ d ih => funext n; simp only [Δn, Δ, ih]; ring

private lemma Δn_shift (d : ℕ) (c : ℤ) (f : ℤ → ℤ) :
    Δn d (fun n => f (n + c)) = fun n => Δn d f (n + c) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    funext n; simp only [Δn, Δ, ih]; rw [show n + 1 + c = n + c + 1 by omega]

private lemma Δn_zero_of_le (d e : ℕ) (hde : d ≤ e) (f : ℤ → ℤ) (hd : Δn d f = 0) :
    Δn e f = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hde
  clear hde
  induction k with
  | zero => simpa using hd
  | succ k ih =>
    rw [← add_assoc]; funext n; simp only [Δn, Δ, ih, Pi.zero_apply, sub_self]

private lemma newton_formula (n : ℕ) :
    ∀ f : ℤ → ℤ, f n = ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℤ) * Δn j f 0 := by
  induction n with
  | zero => intro f; simp [Δn]
  | succ n ih =>
    intro f
    have h1 : f (n + 1 : ℕ) = f n + Δ f n := by
      simp only [Δ, Nat.cast_add, Nat.cast_one]; ring
    rw [h1, ih f, ih (Δ f)]
    have hΔ : ∀ j, Δn j (Δ f) 0 = Δn (j + 1) f 0 := by
      intro j
      induction j with
      | zero => rfl
      | succ j ihj =>
        have : ∀ g : ℤ → ℤ, Δn (j + 1) (Δ g) = Δn (j + 2) g := by
          intro g; clear ih ihj
          induction j generalizing g with
          | zero => rfl
          | succ m ihm => simp only [Δn] at ihm ⊢; rw [ihm]
        exact congr_fun (this f) 0
    simp_rw [hΔ]
    rw [Finset.sum_range_succ' (n := n + 1), Finset.sum_range_succ' (n := n)]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
    rw [show Δn 0 f 0 = f 0 from rfl]
    have h2 : (∑ k ∈ Finset.range (n + 1), (Nat.choose (n + 1) (k + 1) : ℤ) * Δn (k + 1) f 0) =
        (∑ k ∈ Finset.range (n + 1), (Nat.choose n (k + 1) : ℤ) * Δn (k + 1) f 0) +
        (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * Δn (k + 1) f 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hc : (Nat.choose (n + 1) (k + 1) : ℤ) = (Nat.choose n k : ℤ) + (Nat.choose n (k + 1) : ℤ) := by
        exact_mod_cast Nat.choose_succ_succ n k
      rw [hc]; ring
    rw [h2]
    have h3 : (∑ k ∈ Finset.range (n + 1), (Nat.choose n (k + 1) : ℤ) * Δn (k + 1) f 0) =
        ∑ k ∈ Finset.range n, (Nat.choose n (k + 1) : ℤ) * Δn (k + 1) f 0 := by
      rw [Finset.sum_range_succ]; simp
    rw [h3]; ring

private lemma newton_formula_trunc (d : ℕ) (f : ℤ → ℤ) (hd : Δn (d + 1) f = 0) (n : ℕ) :
    f n = ∑ j ∈ Finset.range (d + 1), (Nat.choose n j : ℤ) * Δn j f 0 := by
  rw [newton_formula n f]
  by_cases hnd : n ≤ d
  · refine Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj => ?_
    simp only [Finset.mem_range, not_lt] at hj
    simp [Nat.choose_eq_zero_of_lt (by omega : n < j)]
  · symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj => ?_
    simp only [Finset.mem_range, not_lt] at hj
    have hz : Δn j f = 0 := Δn_zero_of_le (d + 1) j (by omega) f hd
    simp [hz]

private lemma hasSum_poly_div_pow2 (d : ℕ) (f : ℤ → ℤ) (hd : Δn (d + 1) f = 0) :
    HasSum (fun n : ℕ => (f n : ℝ) / 2 ^ (n + 1)) (S d f : ℝ) := by
  have hsum : HasSum (fun n : ℕ =>
      ∑ j ∈ Finset.range (d + 1), (Δn j f 0 : ℝ) * ((Nat.choose n j : ℝ) / 2 ^ (n + 1)))
      (∑ j ∈ Finset.range (d + 1), (Δn j f 0 : ℝ) * 1) :=
    hasSum_sum fun j _ => (hasSum_choose_div_pow2 j).mul_left (Δn j f 0 : ℝ)
  simp only [mul_one, ← Int.cast_sum] at hsum
  refine hsum.congr_fun fun n => ?_
  rw [newton_formula_trunc d f hd n, Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Int.cast_mul, Int.cast_natCast]; ring

private lemma S_shift (d : ℕ) (f : ℤ → ℤ) (hd : Δn (d + 1) f = 0) :
    S d (fun n => f (n + 1)) = 2 * S d f - f 0 := by
  have hstep : ∀ j, Δn j (fun n => f (n + 1)) 0 = Δn j f 0 + Δn (j + 1) f 0 := by
    intro j; rw [Δn_shift j 1 f]; simp only [zero_add, Δn, Δ]; ring
  simp only [S, hstep, Finset.sum_add_distrib]
  have htail : ∑ j ∈ Finset.range (d + 1), Δn (j + 1) f 0 =
      (∑ j ∈ Finset.range (d + 1), Δn j f 0) - f 0 := by
    have h1 := Finset.sum_range_succ' (f := fun j => Δn j f 0) (d + 1)
    have h2 := Finset.sum_range_succ (f := fun j => Δn j f 0) (d + 1)
    have hz : Δn (d + 1) f 0 = 0 := congr_fun hd 0
    rw [show Δn 0 f 0 = f 0 from rfl] at h1
    linarith
  linarith

private lemma S_U_even (d : ℕ) (f : ℤ → ℤ) (hd : Δn (d + 1) f = 0)
    (heven : ∀ n : ℤ, f (-n) = f n) :
    2 * S d f = 2 * f 0 + 4 * S d (U f) - U f 0 := by
  have hE := S_shift d f hd
  have hd_m1 : Δn (d + 1) (fun n => f (n - 1)) = 0 := by
    have : (fun n : ℤ => f (n - 1)) = (fun n : ℤ => f (n + (-1))) := by funext n; ring_nf
    rw [this, Δn_shift, hd]; rfl
  have hEm1 := S_shift d (fun n => f (n - 1)) hd_m1
  simp only [show (fun n : ℤ => f (n + 1 - 1)) = f from by funext n; simp, zero_sub] at hEm1
  have hU_Δ : ∀ j, Δn j (U f) 0 =
      Δn j (fun n => f (n + 1)) 0 + Δn j (fun n => f (n - 1)) 0 - 2 * Δn j f 0 := by
    intro j
    change Δn j (fun n => (f (n + 1) + f (n - 1)) - 2 * f n) 0 = _
    rw [Δn_sub, Δn_add, Δn_const_mul]
  have hU_lin : S d (U f) = S d (fun n => f (n + 1)) + S d (fun n => f (n - 1)) - 2 * S d f := by
    simp only [S, hU_Δ, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hU0 : U f 0 = 2 * f (-1) - 2 * f 0 := by
    simp only [U, zero_add, zero_sub]; have := heven 1; linarith
  linarith

private lemma Δn_U (d : ℕ) (f : ℤ → ℤ) (hd : Δn (d + 2) f = 0) :
    Δn d (U f) = 0 := by
  have hU_eq : U f = fun n => Δn 2 f (n + (-1)) := by
    funext n; simp only [U, Δn, Δ]
    rw [show n + (-1) + 1 = n by omega, show n + (-1) = n - 1 by omega]; ring
  rw [hU_eq, Δn_shift]
  have hcomp : ∀ a b : ℕ, ∀ g : ℤ → ℤ, Δn a (Δn b g) = Δn (a + b) g := by
    intro a b g
    induction a with
    | zero => simp [Δn]
    | succ a iha => simp only [Δn, iha]; rw [show a + 1 + b = a + b + 1 by omega]; rfl
  rw [hcomp d 2 f, hd]; rfl

private lemma three_dvd_S_even :
    ∀ m : ℕ, ∀ f : ℤ → ℤ, Δn (2 * m + 1) f = 0 → (∀ n : ℤ, f (-n) = f n) →
      (3 : ℤ) ∣ (2 * S (2 * m) f - 2 * f 0) := by
  intro m
  induction m with
  | zero => intro f _ _; simp [S, Δn]
  | succ m ih =>
    intro f hd heven
    have hU_even : ∀ n : ℤ, U f (-n) = U f n := by
      intro n; simp only [U]
      have h1 := heven (n - 1); have h2 := heven (n + 1); have h3 := heven n
      rw [show -(n - 1) = -n + 1 by omega] at h1
      rw [show -(n + 1) = -n - 1 by omega] at h2
      linarith
    have hU_d : Δn (2 * m + 1) (U f) = 0 := Δn_U (2 * m + 1) f (by simpa [mul_add] using hd)
    have hS_trunc : S (2 * (m + 1)) (U f) = S (2 * m) (U f) := by
      simp only [S]
      have hz1 : Δn (2 * m + 1) (U f) 0 = 0 := congr_fun hU_d 0
      have hz2 : Δn (2 * m + 2) (U f) 0 = 0 :=
        congr_fun (Δn_zero_of_le (2 * m + 1) (2 * m + 2) (by omega) (U f) hU_d) 0
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega, Finset.sum_range_succ,
        Finset.sum_range_succ, hz1, hz2, add_zero, add_zero]
    have hrec := S_U_even (2 * (m + 1)) f (by simpa [mul_add] using hd) heven
    rw [hS_trunc] at hrec
    have hih := ih (U f) hU_d hU_even
    have hrew : 2 * S (2 * (m + 1)) f - 2 * f 0 =
        2 * (2 * S (2 * m) (U f) - 2 * U f 0) + 3 * U f 0 := by linarith
    rw [hrew]
    exact dvd_add (dvd_mul_of_dvd_right hih 2) (dvd_mul_right 3 _)

-- 3. Polynomial vanishing under ΔQn
private def ΔQ (f : ℤ → ℚ) : ℤ → ℚ := fun n => f (n + 1) - f n

private def ΔQn : ℕ → (ℤ → ℚ) → (ℤ → ℚ)
  | 0, f => f
  | d + 1, f => ΔQ (ΔQn d f)

private lemma ΔQn_cast (d : ℕ) (f : ℤ → ℤ) (n : ℤ) :
    (Δn d f n : ℚ) = ΔQn d (fun k => (f k : ℚ)) n := by
  induction d generalizing n with
  | zero => rfl
  | succ d ih => simp only [Δn, Δ, ΔQn, ΔQ, Int.cast_sub, ih]

private lemma ΔQn_zero (k : ℕ) : ΔQn k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => funext n; simp [ΔQn, ΔQ, ih]

private lemma ΔQn_poly_zero :
    ∀ d : ℕ, ∀ P : Polynomial ℚ, P.natDegree < d →
      ΔQn d (fun n : ℤ => P.eval (n : ℚ)) = 0 := by
  intro d
  induction d with
  | zero => intro P hP; omega
  | succ d ih =>
    intro P hP
    by_cases hP0 : P = 0
    · subst hP0
      have : (fun n : ℤ => (0 : Polynomial ℚ).eval (n : ℚ)) = 0 := by funext n; simp
      rw [this]; exact ΔQn_zero (d + 1)
    · have hQ : ∀ n : ℤ, ΔQ (fun k : ℤ => P.eval (k : ℚ)) n =
          (P.comp (Polynomial.X + 1) - P).eval (n : ℚ) := by
        intro n
        simp only [ΔQ, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_one, Int.cast_add, Int.cast_one]
      have hcomm : ∀ k : ℕ, ∀ g : ℤ → ℚ, ΔQn (k + 1) g = ΔQn k (ΔQ g) := by
        intro k g
        induction k generalizing g with
        | zero => rfl
        | succ m ihm => simp only [ΔQn] at ihm ⊢; rw [ihm]
      rw [hcomm d, funext hQ]
      by_cases hdeg0 : P.natDegree = 0
      · have hconst : P.comp (Polynomial.X + 1) - P = 0 := by
          rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0]; simp
        rw [hconst]
        have : (fun n : ℤ => (0 : Polynomial ℚ).eval (n : ℚ)) = 0 := by funext n; simp
        rw [this]; exact ΔQn_zero d
      · have hdeg_lt : (P.comp (Polynomial.X + 1) - P).natDegree < d := by
          have hX1 : (Polynomial.X + (1 : Polynomial ℚ)).natDegree = 1 := by
            rw [show (1 : Polynomial ℚ) = Polynomial.C 1 from rfl, Polynomial.natDegree_X_add_C]
          have hdeg_comp : (P.comp (Polynomial.X + 1)).natDegree = P.natDegree := by
            rw [Polynomial.natDegree_comp, hX1, mul_one]
          have hlc : (P.comp (Polynomial.X + 1)).leadingCoeff = P.leadingCoeff := by
            rw [Polynomial.leadingCoeff_comp (by omega)]
            have : (Polynomial.X + (1 : Polynomial ℚ)).leadingCoeff = 1 := by
              rw [show (1 : Polynomial ℚ) = Polynomial.C 1 from rfl, Polynomial.leadingCoeff_X_add_C]
            simp [this]
          have hle : (P.comp (Polynomial.X + 1) - P).natDegree ≤ P.natDegree := by
            refine (Polynomial.natDegree_sub_le _ _).trans ?_; rw [hdeg_comp, max_self]
          by_cases hsub0 : P.comp (Polynomial.X + 1) - P = 0
          · rw [hsub0, Polynomial.natDegree_zero]; omega
          · have hne : (P.comp (Polynomial.X + 1) - P).natDegree ≠ P.natDegree := by
              intro heq
              have hc : (P.comp (Polynomial.X + 1) - P).coeff P.natDegree = 0 := by
                rw [Polynomial.coeff_sub, ← hdeg_comp, Polynomial.coeff_natDegree,
                  hdeg_comp, Polynomial.coeff_natDegree, hlc, sub_self]
              rw [← heq, Polynomial.coeff_natDegree] at hc
              exact Polynomial.leadingCoeff_ne_zero.mpr hsub0 hc
            omega
        exact ih _ hdeg_lt

private def ΔN : ℕ → (ℕ → ℤ) → (ℕ → ℤ)
  | 0, g => g
  | d + 1, g => fun n => ΔN d g (n + 1) - ΔN d g n

-- 4. 3-divisibility over ℤ[1/2]
private def IsDiv3Half (q : ℚ) : Prop :=
  ∃ z : ℤ, ∃ e : ℕ, q = (3 * z : ℚ) / (2 ^ e : ℚ)

private def IsHalfInt (q : ℚ) : Prop :=
  ∃ z : ℤ, ∃ e : ℕ, q = (z : ℚ) / (2 ^ e : ℚ)

private lemma isDiv3Half_zero : IsDiv3Half 0 := ⟨0, 0, by simp⟩

private lemma isDiv3Half_add {x y : ℚ} (hx : IsDiv3Half x) (hy : IsDiv3Half y) :
    IsDiv3Half (x + y) := by
  obtain ⟨z1, e1, rfl⟩ := hx; obtain ⟨z2, e2, rfl⟩ := hy
  refine ⟨z1 * 2 ^ e2 + z2 * 2 ^ e1, e1 + e2, ?_⟩
  push_cast
  have h1 : (2 : ℚ) ^ e1 ≠ 0 := by positivity
  have h2 : (2 : ℚ) ^ e2 ≠ 0 := by positivity
  rw [pow_add]; field_simp [h1, h2]

private lemma isDiv3Half_neg {x : ℚ} (hx : IsDiv3Half x) : IsDiv3Half (-x) := by
  obtain ⟨z, e, rfl⟩ := hx; exact ⟨-z, e, by push_cast; ring⟩

private lemma isDiv3Half_sub {x y : ℚ} (hx : IsDiv3Half x) (hy : IsDiv3Half y) :
    IsDiv3Half (x - y) := by rw [sub_eq_add_neg]; exact isDiv3Half_add hx (isDiv3Half_neg hy)

private lemma isDiv3Half_mul_halfInt {x y : ℚ} (hx : IsDiv3Half x) (hy : IsHalfInt y) :
    IsDiv3Half (x * y) := by
  obtain ⟨z1, e1, rfl⟩ := hx; obtain ⟨z2, e2, rfl⟩ := hy
  exact ⟨z1 * z2, e1 + e2, by push_cast; rw [pow_add]; ring⟩

private lemma isDiv3Half_of_int {m : ℤ} (hm : (3 : ℤ) ∣ m) : IsDiv3Half (m : ℚ) := by
  obtain ⟨z, rfl⟩ := hm; exact ⟨z, 0, by push_cast; simp⟩

private lemma isDiv3Half_div2 {x : ℚ} (hx : IsDiv3Half x) : IsDiv3Half (x / 2) := by
  obtain ⟨z, e, rfl⟩ := hx; exact ⟨z, e + 1, by rw [div_div, pow_succ]⟩

private lemma isDiv3Half_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, IsDiv3Half (f i)) : IsDiv3Half (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [isDiv3Half_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isDiv3Half_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma isHalfInt_add {x y : ℚ} (hx : IsHalfInt x) (hy : IsHalfInt y) :
    IsHalfInt (x + y) := by
  obtain ⟨z1, e1, rfl⟩ := hx; obtain ⟨z2, e2, rfl⟩ := hy
  refine ⟨z1 * 2 ^ e2 + z2 * 2 ^ e1, e1 + e2, ?_⟩
  push_cast
  have h1 : (2 : ℚ) ^ e1 ≠ 0 := by positivity
  have h2 : (2 : ℚ) ^ e2 ≠ 0 := by positivity
  rw [pow_add]; field_simp [h1, h2]

private lemma isHalfInt_neg {x : ℚ} (hx : IsHalfInt x) : IsHalfInt (-x) := by
  obtain ⟨z, e, rfl⟩ := hx; exact ⟨-z, e, by push_cast; ring⟩

private lemma isHalfInt_sub {x y : ℚ} (hx : IsHalfInt x) (hy : IsHalfInt y) :
    IsHalfInt (x - y) := by rw [sub_eq_add_neg]; exact isHalfInt_add hx (isHalfInt_neg hy)

private lemma isHalfInt_mul {x y : ℚ} (hx : IsHalfInt x) (hy : IsHalfInt y) :
    IsHalfInt (x * y) := by
  obtain ⟨z1, e1, rfl⟩ := hx; obtain ⟨z2, e2, rfl⟩ := hy
  exact ⟨z1 * z2, e1 + e2, by push_cast; rw [pow_add]; ring⟩

private lemma isHalfInt_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, IsHalfInt (f i)) : IsHalfInt (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isHalfInt_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma isDiv3Half_to_int_dvd {m : ℤ} (h : IsDiv3Half (m : ℚ)) : (3 : ℤ) ∣ m := by
  obtain ⟨z, e, heq⟩ := h
  have h2ne : (2 : ℚ) ^ e ≠ 0 := by positivity
  have hmul : (m : ℚ) * (2 : ℚ) ^ e = (3 * z : ℚ) := (eq_div_iff h2ne).mp heq
  have hint : m * 2 ^ e = 3 * z := by exact_mod_cast hmul
  have hdvd : (3 : ℤ) ∣ m * 2 ^ e := ⟨z, hint⟩
  have hcop : IsCoprime (3 : ℤ) ((2 : ℤ) ^ e) := (by decide : IsCoprime (3 : ℤ) 2).pow_right
  exact hcop.dvd_of_dvd_mul_right hdvd

-- 5. Formal square root B0 = (1 + X)^(1/2) via signed Catalan integers sCat:
--    1 + 4 X = (1 + 2 X S)^2 <=> S + X S^2 = 1!
private def sCat : ℕ → ℤ
  | 0 => 1
  | n + 1 => -(∑ j ∈ (Finset.range (n + 1)).attach, sCat j.1 * sCat (n - j.1))
decreasing_by all_goals (have := Finset.mem_range.mp j.2; omega)

private lemma sCat_succ (n : ℕ) :
    sCat (n + 1) = -(∑ j ∈ Finset.range (n + 1), sCat j * sCat (n - j)) := by
  rw [sCat]
  congr 1
  exact Finset.sum_attach (Finset.range (n + 1)) (fun j => sCat j * sCat (n - j))

private def b0Int : ℕ → ℤ
  | 0 => 1
  | k + 1 => 2 * sCat k

private noncomputable def B0 : PowerSeries ℚ :=
  PowerSeries.mk (fun k => (b0Int k : ℚ) / (4 ^ k : ℚ))

private lemma B0_sq : B0 * B0 = 1 + PowerSeries.X := by
  ext k
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun i j => PowerSeries.coeff i B0 * PowerSeries.coeff j B0)]
  simp only [B0, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
  rcases k with _ | _ | k
  · simp [b0Int]
  · simp [Finset.sum_range_succ, b0Int, sCat]; norm_num
  · simp only [Nat.succ_ne_zero, show k + 2 ≠ 1 by omega, ↓reduceIte, add_zero]
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    have hmid : ∑ j ∈ Finset.range (k + 1),
          ((b0Int (j + 1) : ℚ) / 4 ^ (j + 1)) * ((b0Int (k + 2 - (j + 1)) : ℚ) / 4 ^ (k + 2 - (j + 1))) =
        (∑ j ∈ Finset.range (k + 1), (4 * (sCat j * sCat (k - j)) : ℚ)) / 4 ^ (k + 2) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hsub : k + 2 - (j + 1) = (k - j) + 1 := by omega
      rw [hsub]
      simp only [b0Int, Int.cast_mul, Int.cast_ofNat]
      rw [div_mul_div_comm, ← pow_add, show j + 1 + (k - j + 1) = k + 2 by omega]
      ring
    rw [hmid]
    simp only [Nat.sub_self, Nat.sub_zero, b0Int, pow_zero, div_one, Int.cast_one, one_mul, mul_one]
    have hrec : (sCat (k + 1) : ℚ) = -(∑ j ∈ Finset.range (k + 1), (sCat j * sCat (k - j) : ℚ)) := by
      rw [sCat_succ]; push_cast; rfl
    have h4ne : (4 : ℚ) ^ (k + 2) ≠ 0 := by positivity
    rw [← Finset.mul_sum]
    push_cast at hrec ⊢
    rw [hrec]
    field_simp [h4ne]
    ring

private lemma B0_halfInt (k : ℕ) : IsHalfInt (PowerSeries.coeff k B0) := by
  simp only [B0, PowerSeries.coeff_mk]
  refine ⟨b0Int k, 2 * k, ?_⟩
  rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul]

private lemma B0_coeff_4pow (k : ℕ) : ∃ z : ℤ, PowerSeries.coeff k B0 = (z : ℚ) / (4 ^ k : ℚ) :=
  ⟨b0Int k, by simp [B0]⟩

-- 6. A0(x) = ∑_{no 2 in base 3} x^k satisfies (1 + X) * A0^2 ≡ 1 (mod 3)!
private def noTwo3 (k : ℕ) : Prop := ∀ d ∈ Nat.digits 3 k, d ≠ 2

private instance (k : ℕ) : Decidable (noTwo3 k) := by
  unfold noTwo3; infer_instance

private def a0 (k : ℕ) : ℤ := if noTwo3 k then 1 else 0

private lemma noTwo3_zero : noTwo3 0 := by simp [noTwo3]

private lemma noTwo3_mul3_add (q r : ℕ) (hr : r < 3) :
    noTwo3 (3 * q + r) ↔ (r ≠ 2 ∧ noTwo3 q) := by
  by_cases hq0 : q = 0
  · subst hq0
    simp only [mul_zero, zero_add, noTwo3_zero, and_true]
    interval_cases r <;> decide
  · have hd : Nat.digits 3 (3 * q + r) = r :: Nat.digits 3 q := by
      rw [add_comm, Nat.digits_add 3 (by omega) r q hr (Or.inr hq0)]
    simp only [noTwo3, hd, List.mem_cons, forall_eq_or_imp]

private lemma a0_A0_sq_mod3 :
    let A0 : PowerSeries ℚ := PowerSeries.mk (fun k => (a0 k : ℚ))
    ∀ k : ℕ, IsDiv3Half (PowerSeries.coeff k ((1 + PowerSeries.X) * A0 ^ 2 - 1)) := by
  intro A0
  -- Work in PowerSeries (ZMod 3)!
  let A3 : PowerSeries (ZMod 3) := PowerSeries.mk (fun k => (a0 k : ZMod 3))
  have hadd3 : ∀ f g : PowerSeries (ZMod 3), (f + g) ^ 3 = f ^ 3 + g ^ 3 := by
    intro f g
    have h1 : (f + g) ^ 3 = f ^ 3 + 3 * (f ^ 2 * g + f * g ^ 2) + g ^ 3 := by ring
    have h3 : (3 : PowerSeries (ZMod 3)) = 0 := by
      have h3z : (3 : ZMod 3) = 0 := by decide
      rw [show (3 : PowerSeries (ZMod 3)) = PowerSeries.C (3 : ZMod 3) from (map_ofNat _ 3).symm,
        h3z, map_zero]
    rw [h1, h3, zero_mul, add_zero]
  have hfrob : ∀ n : ℕ, PowerSeries.coeff n (A3 ^ 3) =
      if 3 ∣ n then PowerSeries.coeff (n / 3) A3 else 0 := by
    -- Truncate A3 to polynomial of degree n, apply Frobenius in Polynomial (ZMod 3)!
    intro n
    have htrunc : ∀ P : Polynomial (ZMod 3),
        PowerSeries.coeff n ((P : PowerSeries (ZMod 3)) ^ 3) =
        if 3 ∣ n then P.coeff (n / 3) else 0 := by
      intro P
      induction P using Polynomial.induction_on' with
      | add p q ihp ihq =>
        rw [Polynomial.coe_add, hadd3, map_add, ihp, ihq, Polynomial.coeff_add]
        split_ifs <;> simp
      | monomial m c =>
        have hc3 : c ^ 3 = c := by
          have : ∀ x : ZMod 3, x ^ 3 = x := by decide
          exact this c
        rw [Polynomial.coe_monomial, PowerSeries.monomial_pow, hc3, PowerSeries.coeff_monomial,
          Polynomial.coeff_monomial]
        by_cases h3n : 3 ∣ n
        · obtain ⟨q, rfl⟩ := h3n
          simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_right _ (by omega : 0 < 3)]
          by_cases hmq : m = q
          · subst hmq; simp [mul_comm]
          · simp [hmq, Ne.symm hmq]
        · simp only [h3n, ↓reduceIte]
          have hne : n ≠ 3 * m := by intro h; apply h3n; exact ⟨m, h⟩
          simp [hne]
    let P : Polynomial (ZMod 3) := ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k (a0 k : ZMod 3)
    have hagree : ∀ m ≤ n, PowerSeries.coeff m A3 = PowerSeries.coeff m (P : PowerSeries (ZMod 3)) := by
      intro m hm
      rw [Polynomial.coeff_coe, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range,
        show m < n + 1 by omega, ↓reduceIte, A3, PowerSeries.coeff_mk]
    have hpow_agree : ∀ r : ℕ, ∀ m ≤ n,
        PowerSeries.coeff m (A3 ^ r) = PowerSeries.coeff m ((P : PowerSeries (ZMod 3)) ^ r) := by
      intro r
      induction r with
      | zero => intro m _; simp
      | succ r ihr =>
        intro m hm
        rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (f := fun i j => PowerSeries.coeff i (A3 ^ r) * PowerSeries.coeff j A3),
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (f := fun i j => PowerSeries.coeff i ((P : PowerSeries (ZMod 3)) ^ r) *
              PowerSeries.coeff j (P : PowerSeries (ZMod 3)))]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [ihr k (by omega), hagree (m - k) (by omega)]
    rw [hpow_agree 3 n le_rfl, htrunc P]
    by_cases h3n : 3 ∣ n
    · simp only [h3n, ↓reduceIte]
      have hle : n / 3 ≤ n := Nat.div_le_self n 3
      rw [← Polynomial.coeff_coe, ← hagree (n / 3) hle]
    · simp [h3n]
  have hA3_eq : A3 = (1 + PowerSeries.X) * A3 ^ 3 := by
    ext n
    rw [add_mul, one_mul, map_add, hfrob n]
    cases n with
    | zero =>
      simp [A3, a0, noTwo3_zero, PowerSeries.coeff_zero_eq_constantCoeff]
    | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, hfrob n]
      obtain ⟨q, h | h | h⟩ : ∃ q, n + 1 = 3 * q ∨ n + 1 = 3 * q + 1 ∨ n + 1 = 3 * q + 2 :=
        ⟨(n + 1) / 3, by omega⟩
      · have h1 : 3 ∣ 3 * q := dvd_mul_right 3 q
        have h2 : ¬(3 ∣ 3 * q - 1) := by intro ⟨t, ht⟩; omega
        have hdiv : 3 * q / 3 = q := Nat.mul_div_right q (by omega)
        have hsub : n = 3 * q - 1 := by omega
        rw [h, hsub]; simp only [h1, h2, ↓reduceIte, add_zero, hdiv, A3, PowerSeries.coeff_mk]
        have := noTwo3_mul3_add q 0 (by omega)
        simp only [add_zero, ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true, true_and] at this
        simp [a0, this]
      · have h1 : ¬(3 ∣ 3 * q + 1) := by intro ⟨t, ht⟩; omega
        have h2 : 3 ∣ 3 * q := dvd_mul_right 3 q
        have hdiv : 3 * q / 3 = q := Nat.mul_div_right q (by omega)
        have hsub : n = 3 * q := by omega
        rw [h, hsub]; simp only [h1, h2, ↓reduceIte, zero_add, hdiv, A3, PowerSeries.coeff_mk]
        have := noTwo3_mul3_add q 1 (by omega)
        simp only [ne_eq, OfNat.one_ne_ofNat, not_false_eq_true, true_and] at this
        simp [a0, this]
      · have h1 : ¬(3 ∣ 3 * q + 2) := by intro ⟨t, ht⟩; omega
        have h2 : ¬(3 ∣ 3 * q + 1) := by intro ⟨t, ht⟩; omega
        have hsub : n = 3 * q + 1 := by omega
        rw [h, hsub]; simp only [h1, h2, ↓reduceIte, add_zero, A3, PowerSeries.coeff_mk]
        have := noTwo3_mul3_add q 2 (by omega)
        simp only [ne_eq, not_true_eq_false, false_and] at this
        simp [a0, this]
  have hunit : IsUnit A3 := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp [A3, a0, noTwo3_zero]
  have h1XA3 : (1 + PowerSeries.X) * A3 ^ 2 = 1 := by
    have hmul : ((1 + PowerSeries.X) * A3 ^ 2) * A3 = 1 * A3 := by
      rw [one_mul, mul_assoc, ← pow_succ, ← hA3_eq]
    exact hunit.mul_right_cancel hmul
  -- Transfer coeff k ((1 + X) * A3^2) = coeff k 1 to IsDiv3Half in PowerSeries ℚ!
  intro k
  have hc3 := congr_arg (PowerSeries.coeff k) h1XA3
  -- Compute coeff k ((1 + X) * A0^2 - 1) as integer cast to ℚ!
  have hmul_int : ∀ (f g : ℕ → ℤ) (m : ℕ),
      PowerSeries.coeff m (PowerSeries.mk (fun i => (f i : ℚ)) * PowerSeries.mk (fun i => (g i : ℚ))) =
      ((∑ i ∈ Finset.range (m + 1), f i * g (m - i) : ℤ) : ℚ) := by
    intro f g m
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j => PowerSeries.coeff i (PowerSeries.mk fun i => (f i : ℚ)) *
          PowerSeries.coeff j (PowerSeries.mk fun i => (g i : ℚ)))]
    simp [Int.cast_sum]
  have hmul_z3 : ∀ (f g : ℕ → ℤ) (m : ℕ),
      PowerSeries.coeff m (PowerSeries.mk (fun i => (f i : ZMod 3)) * PowerSeries.mk (fun i => (g i : ZMod 3))) =
      ((∑ i ∈ Finset.range (m + 1), f i * g (m - i) : ℤ) : ZMod 3) := by
    intro f g m
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j => PowerSeries.coeff i (PowerSeries.mk fun i => (f i : ZMod 3)) *
          PowerSeries.coeff j (PowerSeries.mk fun i => (g i : ZMod 3)))]
    simp [Int.cast_sum]
  let sq : ℕ → ℤ := fun m => ∑ i ∈ Finset.range (m + 1), a0 i * a0 (m - i)
  have hA0sq : A0 ^ 2 = PowerSeries.mk (fun m => (sq m : ℚ)) := by
    ext m; rw [pow_two, hmul_int]; simp [sq]
  have hA3sq : A3 ^ 2 = PowerSeries.mk (fun m => (sq m : ZMod 3)) := by
    ext m; rw [pow_two, hmul_z3]; simp [sq]
  rw [hA3sq, add_mul, one_mul, map_add] at hc3
  rw [hA0sq, map_sub, add_mul, one_mul, map_add]
  cases k with
  | zero =>
    simp [PowerSeries.coeff_zero_eq_constantCoeff, sq, Finset.sum_range_succ, a0, noTwo3_zero]
    exact isDiv3Half_zero
  | succ k =>
    simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_one,
      Nat.succ_ne_zero, ↓reduceIte, sub_zero] at hc3 ⊢
    rw [← Int.cast_add] at hc3 ⊢
    have hdvd : (3 : ℤ) ∣ (sq (k + 1) + sq k) := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hc3
    exact isDiv3Half_of_int hdvd

private lemma A0_B0_mod3 :
    let A0 : PowerSeries ℚ := PowerSeries.mk (fun k => (a0 k : ℚ))
    ∀ k : ℕ, IsDiv3Half (PowerSeries.coeff k (A0 * B0 - 1)) := by
  intro A0
  have hsq : ∀ k : ℕ, IsDiv3Half (PowerSeries.coeff k ((A0 * B0) ^ 2 - 1)) := by
    intro k
    have : (A0 * B0) ^ 2 - 1 = (1 + PowerSeries.X) * A0 ^ 2 - 1 := by
      rw [mul_pow, pow_two B0, B0_sq]; ring
    rw [this]
    exact a0_A0_sq_mod3 k
  have h0 : PowerSeries.coeff 0 (A0 * B0) = 1 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j => PowerSeries.coeff i A0 * PowerSeries.coeff j B0)]
    simp only [Finset.range_one, Finset.sum_singleton, Nat.sub_zero, A0, B0, PowerSeries.coeff_mk,
      a0, noTwo3_zero, ↓reduceIte, Int.cast_one, b0Int, pow_zero, div_one, mul_one]
  have hhalf : ∀ m : ℕ, IsHalfInt (PowerSeries.coeff m (A0 * B0)) := by
    intro m
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j => PowerSeries.coeff i A0 * PowerSeries.coeff j B0)]
    refine isHalfInt_sum _ _ fun j _ => ?_
    exact isHalfInt_mul ⟨a0 j, 0, by simp [A0]⟩ (B0_halfInt (m - j))
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      simp only [map_sub, h0, PowerSeries.coeff_one, ↓reduceIte, sub_self]
      exact isDiv3Half_zero
    | succ k =>
      have hk := hsq (k + 1)
      simp only [map_sub, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte, sub_zero] at hk ⊢
      rw [pow_two, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (f := fun i j => PowerSeries.coeff i (A0 * B0) * PowerSeries.coeff j (A0 * B0))] at hk
      rw [Finset.sum_range_succ, Finset.sum_range_succ'] at hk
      simp only [Nat.sub_self, Nat.sub_zero, h0, one_mul, mul_one] at hk
      have hmid : IsDiv3Half (∑ j ∈ Finset.range k,
          PowerSeries.coeff (j + 1) (A0 * B0) * PowerSeries.coeff (k + 1 - (j + 1)) (A0 * B0)) := by
        refine isDiv3Half_sum _ _ fun j hj => ?_
        have hjk : j < k := Finset.mem_range.mp hj
        have h1 := ih (j + 1) (by omega)
        simp only [map_sub, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte, sub_zero] at h1
        exact isDiv3Half_mul_halfInt h1 (hhalf (k + 1 - (j + 1)))
      have h2c : IsDiv3Half (2 * PowerSeries.coeff (k + 1) (A0 * B0)) := by
        have hsub := isDiv3Half_sub hk hmid
        have heq : (∑ x ∈ Finset.range k,
              PowerSeries.coeff (x + 1) (A0 * B0) * PowerSeries.coeff (k + 1 - (x + 1)) (A0 * B0)) +
            PowerSeries.coeff (k + 1) (A0 * B0) + PowerSeries.coeff (k + 1) (A0 * B0) -
            (∑ x ∈ Finset.range k,
              PowerSeries.coeff (x + 1) (A0 * B0) * PowerSeries.coeff (k + 1 - (x + 1)) (A0 * B0)) =
            2 * PowerSeries.coeff (k + 1) (A0 * B0) := by ring
        rwa [heq] at hsub
      have hdiv := isDiv3Half_div2 h2c
      simpa using hdiv

-- 7. F_n = (1 + X)^(n*(n-1)/2) * B0^n has 4^j * coeff j F_n an EVEN integer-valued polynomial in n!
private lemma F_n_coeff_poly (j : ℕ) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ 2 * j ∧
      (∀ n : ℤ, P.eval (-n : ℚ) = P.eval (n : ℚ)) ∧
      (0 < j → P.eval 0 = 0) ∧
      (∀ n : ℕ, PowerSeries.coeff j ((1 + PowerSeries.X) ^ (n * (n - 1) / 2) * B0 ^ n) = P.eval (n : ℚ)) := by
  let P : Polynomial ℚ :=
    ((Nat.factorial j : ℚ)⁻¹) •
      (∏ i ∈ Finset.range j, ((1 / 2 : ℚ) • Polynomial.X ^ 2 - Polynomial.C (i : ℚ)))
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · refine (Polynomial.natDegree_smul_le _ _).trans ?_
    refine (Polynomial.natDegree_prod_le (Finset.range j)
      (fun i => (1 / 2 : ℚ) • Polynomial.X ^ 2 - Polynomial.C (i : ℚ))).trans ?_
    have h1 : ∀ i ∈ Finset.range j,
        ((1 / 2 : ℚ) • Polynomial.X ^ 2 - Polynomial.C (i : ℚ)).natDegree ≤ 2 := by
      intro i _
      refine (Polynomial.natDegree_sub_le _ _).trans ?_
      have hsm : ((1 / 2 : ℚ) • (Polynomial.X : Polynomial ℚ) ^ 2).natDegree ≤ 2 :=
        (Polynomial.natDegree_smul_le _ _).trans (by simp)
      simp only [one_div] at hsm
      simp [hsm]
    have hsum : (∑ i ∈ Finset.range j,
        ((1 / 2 : ℚ) • Polynomial.X ^ 2 - Polynomial.C (i : ℚ)).natDegree) ≤
        ∑ _i ∈ Finset.range j, 2 := Finset.sum_le_sum h1
    simpa [mul_comm] using hsum
  · intro n
    simp only [P, Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, neg_sq]
  · intro hj
    simp only [P, Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    have h0 : (0 : ℕ) ∈ Finset.range j := Finset.mem_range.mpr hj
    rw [Finset.prod_eq_zero h0 (by simp), mul_zero]
  · intro n
    -- Prove F_n^2 = (1 + X)^(n^2) => 2*(1+X)*F_n' = n^2 * F_n => coeff recursion!
    set F : PowerSeries ℚ := (1 + PowerSeries.X) ^ (n * (n - 1) / 2) * B0 ^ n
    have hF_sq : F * F = (1 + PowerSeries.X) ^ (n ^ 2) := by
      have h1 : F * F = (1 + PowerSeries.X) ^ (2 * (n * (n - 1) / 2)) * (B0 * B0) ^ n := by
        simp only [F, mul_pow, ← pow_add, two_mul]; ring
      have hev : Even (n * (n - 1)) := by
        rcases Nat.even_or_odd n with ⟨r, rfl⟩ | ⟨r, rfl⟩
        · exact ⟨r * (r + r - 1), by ring⟩
        · exact ⟨(2 * r + 1) * r, by simp only [Nat.add_sub_cancel]; ring⟩
      have h2div : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
        obtain ⟨r, hr⟩ := hev; omega
      have hnsq : n * (n - 1) + n = n ^ 2 := by
        cases n with
        | zero => simp
        | succ m => simp only [Nat.add_sub_cancel]; ring
      rw [h1, h2div, B0_sq, ← pow_add, hnsq]
    have hF_ode : (2 : PowerSeries ℚ) * (1 + PowerSeries.X) * PowerSeries.derivative ℚ F =
        ((n ^ 2 : ℕ) : PowerSeries ℚ) * F := by
      have hd := congr_arg (PowerSeries.derivative ℚ) hF_sq
      rw [Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_pow, map_add,
        Derivation.map_one_eq_zero, PowerSeries.derivative_X, zero_add, mul_one] at hd
      have hmul := congr_arg ((1 + PowerSeries.X) * ·) hd
      have hL : (1 + PowerSeries.X) * (F * PowerSeries.derivative ℚ F + F * PowerSeries.derivative ℚ F) =
          F * ((2 : PowerSeries ℚ) * (1 + PowerSeries.X) * PowerSeries.derivative ℚ F) := by ring
      have hR : (1 + PowerSeries.X) * (((n ^ 2 : ℕ) : PowerSeries ℚ) * (1 + PowerSeries.X) ^ (n ^ 2 - 1)) =
          F * (((n ^ 2 : ℕ) : PowerSeries ℚ) * F) := by
        cases hn0 : n with
        | zero => simp
        | succ m =>
          have hpos : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow 2 (m + 1) (Nat.succ_pos m)
          have hpow : (1 + PowerSeries.X : PowerSeries ℚ) * (1 + PowerSeries.X) ^ ((m + 1) ^ 2 - 1) =
              (1 + PowerSeries.X) ^ ((m + 1) ^ 2) := by
            rw [← pow_succ', show (m + 1) ^ 2 - 1 + 1 = (m + 1) ^ 2 by omega]
          rw [hn0] at hF_sq
          rw [← hF_sq] at hpow
          calc (1 + PowerSeries.X) * ((((m + 1) ^ 2 : ℕ) : PowerSeries ℚ) * (1 + PowerSeries.X) ^ ((m + 1) ^ 2 - 1))
              = (((m + 1) ^ 2 : ℕ) : PowerSeries ℚ) * ((1 + PowerSeries.X) * (1 + PowerSeries.X) ^ ((m + 1) ^ 2 - 1)) := by ring
            _ = (((m + 1) ^ 2 : ℕ) : PowerSeries ℚ) * (F * F) := by rw [hpow]
            _ = F * ((((m + 1) ^ 2 : ℕ) : PowerSeries ℚ) * F) := by ring
      rw [hL, hR] at hmul
      have hF_unit : IsUnit F := by
        rw [PowerSeries.isUnit_iff_constantCoeff]
        simp [F, B0, b0Int]
      exact hF_unit.mul_left_cancel hmul
    have hF0 : PowerSeries.coeff 0 F = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff]
      simp [F, B0, b0Int]
    have hF_rec : ∀ m : ℕ,
        PowerSeries.coeff (m + 1) F =
        (((1 / 2 : ℚ) * (n : ℚ) ^ 2 - (m : ℚ)) / ((m + 1 : ℕ) : ℚ)) * PowerSeries.coeff m F := by
      intro m
      have hc := congr_arg (PowerSeries.coeff m) hF_ode
      have hL : PowerSeries.coeff m ((2 : PowerSeries ℚ) * (1 + PowerSeries.X) * PowerSeries.derivative ℚ F) =
          2 * (((m + 1 : ℕ) : ℚ) * PowerSeries.coeff (m + 1) F + (m : ℚ) * PowerSeries.coeff m F) := by
        have hrew : (2 : PowerSeries ℚ) * (1 + PowerSeries.X) * PowerSeries.derivative ℚ F =
            PowerSeries.derivative ℚ F + PowerSeries.derivative ℚ F +
            (PowerSeries.X * PowerSeries.derivative ℚ F + PowerSeries.X * PowerSeries.derivative ℚ F) := by
          ring
        rw [hrew, map_add, map_add, map_add, PowerSeries.coeff_derivative]
        cases m with
        | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]; ring
        | succ m =>
          rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
          push_cast; ring
      have hR : PowerSeries.coeff m (((n ^ 2 : ℕ) : PowerSeries ℚ) * F) =
          ((n : ℚ) ^ 2) * PowerSeries.coeff m F := by
        rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, Nat.cast_pow]
      rw [hL, hR] at hc
      have hm1 : ((m + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
      field_simp [hm1]
      linarith
    -- Induction on j!
    have hrec_all : ∀ m : ℕ, PowerSeries.coeff m F =
        (((Nat.factorial m : ℚ)⁻¹) •
          (∏ i ∈ Finset.range m, ((1 / 2 : ℚ) • Polynomial.X ^ 2 - Polynomial.C (i : ℚ)))).eval (n : ℚ) := by
      intro m
      induction m with
      | zero => simp [hF0]
      | succ m ihm =>
        rw [hF_rec m, ihm]
        simp only [Polynomial.eval_smul, smul_eq_mul, Finset.prod_range_succ, Polynomial.eval_mul,
          Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_C, Nat.factorial_succ, Nat.cast_mul]
        have h1 : ((m + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
        have h2 : (Nat.factorial m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
        field_simp [h1, h2]
    exact hrec_all j

private lemma F_n_coeff_4pow_int (j n : ℕ) :
    ∃ z : ℤ, PowerSeries.coeff j ((1 + PowerSeries.X) ^ (n * (n - 1) / 2) * B0 ^ n) =
      (z : ℚ) / (4 ^ j : ℚ) := by
  -- Prove by induction on n that coeff j (B0^n) has denom 4^j, then multiply by (1+X)^m!
  have hB0n : ∀ m k : ℕ, ∃ z : ℤ, PowerSeries.coeff k (B0 ^ m) = (z : ℚ) / (4 ^ k : ℚ) := by
    intro m
    induction m with
    | zero =>
      intro k
      by_cases hk : k = 0
      · subst hk; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [PowerSeries.coeff_one, hk]⟩
    | succ m ihm =>
      intro k
      rw [pow_succ, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (f := fun i j => PowerSeries.coeff i (B0 ^ m) * PowerSeries.coeff j B0)]
      choose z1 hz1 using ihm
      refine ⟨∑ i ∈ Finset.range (k + 1), z1 i * b0Int (k - i), ?_⟩
      rw [Int.cast_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [hz1 i, show PowerSeries.coeff (k - i) B0 = (b0Int (k - i) : ℚ) / (4 ^ (k - i) : ℚ) from by
        simp [B0]]
      rw [div_mul_div_comm, ← pow_add, show i + (k - i) = k by omega, Int.cast_mul]
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun i r => PowerSeries.coeff i ((1 + PowerSeries.X : PowerSeries ℚ) ^ (n * (n - 1) / 2)) *
        PowerSeries.coeff r (B0 ^ n))]
  choose z2 hz2 using hB0n n
  refine ⟨∑ i ∈ Finset.range (j + 1), (Nat.choose (n * (n - 1) / 2) i : ℤ) * 4 ^ i * z2 (j - i), ?_⟩
  rw [Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hX : PowerSeries.coeff i ((1 + PowerSeries.X : PowerSeries ℚ) ^ (n * (n - 1) / 2)) =
      (Nat.choose (n * (n - 1) / 2) i : ℚ) := by
    have hpoly : ((1 + PowerSeries.X : PowerSeries ℚ) ^ (n * (n - 1) / 2)) =
        (((1 + Polynomial.X : Polynomial ℚ) ^ (n * (n - 1) / 2) : Polynomial ℚ) : PowerSeries ℚ) := by
      simp
    rw [hpoly, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
  rw [hX, hz2 (j - i)]
  have h4i : (4 : ℚ) ^ i ≠ 0 := by positivity
  have h4ji : (4 : ℚ) ^ (j - i) ≠ 0 := by positivity
  have hpow : (4 : ℚ) ^ j = (4 : ℚ) ^ i * (4 : ℚ) ^ (j - i) := by
    rw [← pow_add, show i + (j - i) = j by omega]
  rw [hpow]; push_cast; field_simp [h4i, h4ji]

private lemma choose_poly (r : ℕ) :
    ∃ Q : Polynomial ℚ, Q.natDegree ≤ r ∧
      ∀ n : ℕ, (Nat.choose n r : ℚ) = Q.eval (n : ℚ) := by
  refine ⟨((Nat.factorial r : ℚ)⁻¹) •
      (∏ i ∈ Finset.range r, (Polynomial.X - Polynomial.C (i : ℚ))), ?_, ?_⟩
  · refine (Polynomial.natDegree_smul_le _ _).trans ?_
    refine (Polynomial.natDegree_prod_le (Finset.range r)
      (fun i => Polynomial.X - Polynomial.C (i : ℚ))).trans ?_
    have h1 : ∀ i ∈ Finset.range r, (Polynomial.X - Polynomial.C (i : ℚ)).natDegree ≤ 1 := by
      intro i _; refine (Polynomial.natDegree_sub_le _ _).trans ?_; simp
    have hsum : (∑ i ∈ Finset.range r, (Polynomial.X - Polynomial.C (i : ℚ)).natDegree) ≤
        ∑ _i ∈ Finset.range r, 1 := Finset.sum_le_sum h1
    simpa using hsum
  · intro n
    simp only [Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have hdesc : (Nat.choose n r : ℚ) * (Nat.factorial r : ℚ) =
        ∏ i ∈ Finset.range r, ((n : ℚ) - (i : ℚ)) := by
      have h1 : (Nat.descFactorial n r : ℚ) = (Nat.choose n r : ℚ) * (Nat.factorial r : ℚ) := by
        have := Nat.descFactorial_eq_factorial_mul_choose n r
        rw [mul_comm] at this; exact_mod_cast this
      rw [← h1]; clear h1
      induction r with
      | zero => simp
      | succ r ih =>
        rw [Finset.prod_range_succ, ← ih, Nat.descFactorial_succ, Nat.cast_mul, mul_comm]
        by_cases hrn : r ≤ n
        · rw [Nat.cast_sub hrn]
        · have h0 : Nat.descFactorial n r = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
          simp [h0]
    rw [← hdesc]
    have hfr : (Nat.factorial r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
    field_simp [hfr]

private lemma hasSum_F_n_choose (j r : ℕ) :
    ∃ M : ℚ, IsHalfInt M ∧
      (r = 0 → 0 < j → IsDiv3Half M) ∧
      HasSum (fun n : ℕ =>
        ((PowerSeries.coeff j ((1 + PowerSeries.X) ^ (n * (n - 1) / 2) * B0 ^ n) : ℚ) : ℝ) *
          (Nat.choose n r : ℝ) / 2 ^ (n + 1)) (M : ℝ) := by
  obtain ⟨P, hPdeg, hPeven, hP0, hPeval⟩ := F_n_coeff_poly j
  obtain ⟨Q, hQdeg, hQeval⟩ := choose_poly r
  choose zF hzF using F_n_coeff_4pow_int j
  -- fN n = zF n * C(n, r) ∈ ℤ has (fN n : ℚ) = (4^j * P * Q).eval n!
  let fN : ℕ → ℤ := fun n => zF n * (Nat.choose n r : ℤ)
  have hfN_poly : ∀ n : ℕ, (fN n : ℚ) = (((4 : ℚ) ^ j) • (P * Q)).eval (n : ℚ) := by
    intro n
    have hz : (zF n : ℚ) = (4 : ℚ) ^ j * P.eval (n : ℚ) := by
      have h1 := hzF n
      rw [hPeval n] at h1
      have h4ne : (4 : ℚ) ^ j ≠ 0 := by positivity
      exact ((eq_div_iff h4ne).mp h1).symm.trans (mul_comm _ _)
    simp only [fN, Int.cast_mul, Int.cast_natCast, Polynomial.eval_smul, smul_eq_mul,
      Polynomial.eval_mul, hz, hQeval n]
    ring
  set D := 2 * j + r
  have hdegR : (((4 : ℚ) ^ j) • (P * Q)).natDegree < D + 1 := by
    have h1 := Polynomial.natDegree_smul_le ((4 : ℚ) ^ j) (P * Q)
    have h2 := Polynomial.natDegree_mul_le (p := P) (q := Q)
    omega
  have hΔN_zero : ∀ d : ℕ, D + 1 ≤ d → ΔN d fN 0 = 0 := by
    intro d hd
    have hcast : ∀ k : ℕ, ∀ h : ℕ → ℤ, ∀ m : ℕ,
        (ΔN k h m : ℚ) = ΔQn k (fun x : ℤ => if 0 ≤ x then (h x.toNat : ℚ) else 0) (m : ℤ) := by
      intro k
      induction k with
      | zero => intro h m; simp [ΔN, ΔQn]
      | succ k ihk =>
        intro h m
        simp only [ΔN, Int.cast_sub, ihk h (m + 1), ihk h m, ΔQn, ΔQ, Nat.cast_add, Nat.cast_one]
    have hcast_eq : ∀ k : ℕ, ∀ h1 h2 : ℤ → ℚ, (∀ m : ℕ, h1 m = h2 m) →
        ∀ m : ℕ, ΔQn k h1 m = ΔQn k h2 m := by
      intro k
      induction k with
      | zero => intro h1 h2 heq m; exact heq m
      | succ k ihk =>
        intro h1 h2 heq m
        simp only [ΔQn, ΔQ]
        have h1' := ihk h1 h2 heq (m + 1); have h2' := ihk h1 h2 heq m
        simp only [Nat.cast_add, Nat.cast_one] at h1'
        rw [h1', h2']
    have hq : (ΔN d fN 0 : ℚ) = 0 := by
      rw [hcast d fN 0, hcast_eq d _ (fun x : ℤ => (((4 : ℚ) ^ j) • (P * Q)).eval (x : ℚ))
        (fun m => by simp [hfN_poly m]) 0, ΔQn_poly_zero d _ (by omega)]
      rfl
    exact_mod_cast hq
  have hnewtN : ∀ m : ℕ, fN m = ∑ i ∈ Finset.range (D + 1), (Nat.choose m i : ℤ) * ΔN i fN 0 := by
    intro m
    have h := newton_formula m (fun x : ℤ => if 0 ≤ x then fN x.toNat else 0)
    have hΔeq : ∀ i : ℕ, ∀ t : ℕ,
        Δn i (fun x : ℤ => if 0 ≤ x then fN x.toNat else 0) t = ΔN i fN t := by
      intro i
      induction i with
      | zero => intro t; simp [Δn, ΔN]
      | succ i ihi =>
        intro t; simp only [Δn, Δ, ΔN]
        have h1 := ihi (t + 1); have h2 := ihi t
        simp only [Nat.cast_add, Nat.cast_one] at h1; rw [h1, h2]
    have hΔeq0 : ∀ i, Δn i (fun x : ℤ => if 0 ≤ x then fN x.toNat else 0) 0 = ΔN i fN 0 :=
      fun i => hΔeq i 0
    have hm : fN m = ∑ i ∈ Finset.range (m + 1), (Nat.choose m i : ℤ) * ΔN i fN 0 := by
      simpa [hΔeq0] using h
    rw [hm]
    by_cases hmD : m ≤ D
    · refine Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hi => ?_
      simp only [Finset.mem_range, not_lt] at hi
      simp [Nat.choose_eq_zero_of_lt (by omega : m < i)]
    · symm
      refine Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hi => ?_
      simp only [Finset.mem_range, not_lt] at hi
      simp [hΔN_zero i (by omega)]
  set Mint : ℤ := ∑ i ∈ Finset.range (D + 1), ΔN i fN 0
  refine ⟨(Mint : ℚ) / (4 ^ j : ℚ), ⟨Mint, 2 * j, by rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul]⟩, ?_, ?_⟩
  · intro hr0 hjpos
    subst hr0
    -- When r = 0, fZ n := zF n.natAbs is EVEN, fZ 0 = 0, Δn (2*j + 1) fZ = 0 => 3 ∣ S (2*j) fZ = Mint!
    let fZ : ℤ → ℤ := fun n => zF n.natAbs
    have hfZ_poly : ∀ n : ℤ, (fZ n : ℚ) = (((4 : ℚ) ^ j) • P).eval (n : ℚ) := by
      intro n
      have h1 := hzF n.natAbs
      rw [hPeval n.natAbs] at h1
      have h4ne : (4 : ℚ) ^ j ≠ 0 := by positivity
      have h2 : (zF n.natAbs : ℚ) = (4 : ℚ) ^ j * P.eval (n.natAbs : ℚ) :=
        ((eq_div_iff h4ne).mp h1).symm.trans (mul_comm _ _)
      have hev : P.eval (n.natAbs : ℚ) = P.eval (n : ℚ) := by
        rcases Int.natAbs_eq n with hn | hn
        · have hn' : (n : ℚ) = (n.natAbs : ℚ) := by rw [← Int.cast_natCast, ← hn]
          rw [hn']
        · have hn' : (n : ℚ) = -((n.natAbs : ℤ) : ℚ) := by rw [← Int.cast_neg, ← hn]
          rw [hn', hPeven (n.natAbs : ℤ)]
          simp
      simp only [fZ, h2, hev, Polynomial.eval_smul, smul_eq_mul]
    have hfZ_Δ : Δn (2 * j + 1) fZ = 0 := by
      funext n
      have h0 : (Δn (2 * j + 1) fZ n : ℚ) = 0 := by
        rw [ΔQn_cast, funext hfZ_poly, ΔQn_poly_zero (2 * j + 1) (((4 : ℚ) ^ j) • P)
          (lt_of_le_of_lt (Polynomial.natDegree_smul_le _ _) (by omega))]
        rfl
      exact_mod_cast h0
    have hfZ_even : ∀ n : ℤ, fZ (-n) = fZ n := fun n => by simp [fZ]
    have hfZ_0 : fZ 0 = 0 := by
      have h0 := hfZ_poly 0
      simp only [Int.cast_zero, Polynomial.eval_smul, smul_eq_mul, hP0 hjpos, mul_zero] at h0
      exact_mod_cast h0
    have h3dvd : (3 : ℤ) ∣ S (2 * j) fZ := by
      have hd := three_dvd_S_even j fZ hfZ_Δ hfZ_even
      rw [hfZ_0, mul_zero, sub_zero] at hd
      exact (by decide : IsCoprime (3 : ℤ) 2).dvd_of_dvd_mul_left hd
    have hMint_eq : Mint = S (2 * j) fZ := by
      have h1 : HasSum (fun n : ℕ => (fZ n : ℝ) / 2 ^ (n + 1)) (S (2 * j) fZ : ℝ) :=
        hasSum_poly_div_pow2 (2 * j) fZ hfZ_Δ
      have h2 : HasSum (fun n : ℕ => (fN n : ℝ) / 2 ^ (n + 1)) (Mint : ℝ) := by
        have hs : HasSum (fun n : ℕ =>
            ∑ i ∈ Finset.range (D + 1), (ΔN i fN 0 : ℝ) * ((Nat.choose n i : ℝ) / 2 ^ (n + 1)))
            (∑ i ∈ Finset.range (D + 1), (ΔN i fN 0 : ℝ) * 1) :=
          hasSum_sum fun i _ => (hasSum_choose_div_pow2 i).mul_left (ΔN i fN 0 : ℝ)
        simp only [mul_one, ← Int.cast_sum] at hs
        refine hs.congr_fun fun n => ?_
        rw [hnewtN n, Int.cast_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => by rw [Int.cast_mul, Int.cast_natCast]; ring
      have heq_fn : (fun n : ℕ => (fZ n : ℝ) / 2 ^ (n + 1)) = (fun n : ℕ => (fN n : ℝ) / 2 ^ (n + 1)) := by
        funext n; simp [fZ, fN]
      rw [heq_fn] at h1
      exact_mod_cast h2.unique h1
    rw [hMint_eq]
    obtain ⟨q, hq⟩ := h3dvd
    refine ⟨q, 2 * j, ?_⟩
    rw [hq, Int.cast_mul, Int.cast_ofNat, show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul]
  · have hs : HasSum (fun n : ℕ =>
        ∑ i ∈ Finset.range (D + 1), (ΔN i fN 0 : ℝ) * ((Nat.choose n i : ℝ) / 2 ^ (n + 1)))
        (Mint : ℝ) := by
      have := hasSum_sum (s := Finset.range (D + 1))
        fun i _ => (hasSum_choose_div_pow2 i).mul_left (ΔN i fN 0 : ℝ)
      simpa only [mul_one, ← Int.cast_sum] using this
    have hs' := hs.div_const ((4 : ℝ) ^ j)
    have hcast : (Mint : ℝ) / (4 : ℝ) ^ j = (((Mint : ℚ) / (4 ^ j : ℚ) : ℚ) : ℝ) := by push_cast; rfl
    rw [hcast] at hs'
    refine hs'.congr_fun fun n => ?_
    have hfn_eq : (∑ i ∈ Finset.range (D + 1), (ΔN i fN 0 : ℝ) * ((Nat.choose n i : ℝ) / 2 ^ (n + 1))) =
        (fN n : ℝ) / 2 ^ (n + 1) := by
      rw [hnewtN n, Int.cast_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => by rw [Int.cast_mul, Int.cast_natCast]; ring
    rw [hfn_eq, hzF n]
    simp only [fN, Int.cast_mul, Int.cast_natCast, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow,
      Rat.cast_ofNat]
    ring

-- 8. Main theorem
private theorem main_proved :
    ∀ a : ℕ → ℤ,
      a 0 = 1 →
      ∀ B : PowerSeries ℚ,
        B * PowerSeries.mk (fun k => (a k : ℚ)) = 1 →
        (∀ k : ℕ,
          HasSum (fun n : ℕ =>
            ((PowerSeries.coeff k ((1 + PowerSeries.X) ^ (n * (n - 1) / 2) * B ^ n) : ℚ) : ℝ) /
              2 ^ (n + 1))
            (if k = 0 then 1 else 0)) →
        ∀ k : ℕ, a k % 3 = if (∀ d ∈ Nat.digits 3 k, d ≠ 2) then 1 else 0 := by
  intro a ha0 B hBA hsum_eq
  set A : PowerSeries ℚ := PowerSeries.mk (fun k => (a k : ℚ))
  set A0 : PowerSeries ℚ := PowerSeries.mk (fun k => (a0 k : ℚ))
  -- Construct B0inv with B0inv * B0 = 1 and IsHalfInt coeffs
  have hB0_unit : IsUnit B0 := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp [B0, b0Int]
  obtain ⟨B0inv, hB0inv⟩ : ∃ B0inv : PowerSeries ℚ, B0inv * B0 = 1 :=
    ⟨((hB0_unit.unit⁻¹ : (PowerSeries ℚ)ˣ) : PowerSeries ℚ), by
      have := hB0_unit.unit.inv_mul; exact_mod_cast this⟩
  have hB0inv_half : ∀ m : ℕ, IsHalfInt (PowerSeries.coeff m B0inv) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      have hm := congr_arg (PowerSeries.coeff m) hB0inv
      rw [PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (f := fun i j => PowerSeries.coeff i B0inv * PowerSeries.coeff j B0)] at hm
      cases m with
      | zero =>
        simp only [Finset.range_one, Finset.sum_singleton, Nat.sub_zero, PowerSeries.coeff_one,
          ↓reduceIte, B0, PowerSeries.coeff_mk, b0Int, pow_zero, div_one, Int.cast_one, mul_one] at hm
        exact ⟨1, 0, by simp [hm]⟩
      | succ m =>
        rw [Finset.sum_range_succ] at hm
        have hB0_0 : PowerSeries.coeff 0 B0 = 1 := by simp [B0, b0Int]
        simp only [Nat.sub_self, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte, hB0_0,
          mul_one] at hm
        have heq : PowerSeries.coeff (m + 1) B0inv =
            -(∑ x ∈ Finset.range (m + 1),
              PowerSeries.coeff x B0inv * PowerSeries.coeff (m + 1 - x) B0) := by linarith
        rw [heq]
        refine isHalfInt_neg (isHalfInt_sum _ _ fun x hx => ?_)
        exact isHalfInt_mul (ih x (Finset.mem_range.mp hx)) (B0_halfInt (m + 1 - x))
  have hB_half : ∀ m : ℕ, IsHalfInt (PowerSeries.coeff m B) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      have hm := congr_arg (PowerSeries.coeff m) hBA
      rw [PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (f := fun i j => PowerSeries.coeff i B * PowerSeries.coeff j A)] at hm
      cases m with
      | zero =>
        simp only [Finset.range_one, Finset.sum_singleton, Nat.sub_zero, PowerSeries.coeff_one,
          ↓reduceIte, A, PowerSeries.coeff_mk, ha0, Int.cast_one, mul_one] at hm
        exact ⟨1, 0, by simp [hm]⟩
      | succ m =>
        rw [Finset.sum_range_succ] at hm
        simp only [Nat.sub_self, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte, A,
          PowerSeries.coeff_mk, ha0, Int.cast_one, mul_one] at hm
        have heq : PowerSeries.coeff (m + 1) B =
            -(∑ x ∈ Finset.range (m + 1),
              PowerSeries.coeff x B * (a (m + 1 - x) : ℚ)) := by linarith
        rw [heq]
        refine isHalfInt_neg (isHalfInt_sum _ _ fun x hx => ?_)
        exact isHalfInt_mul (ih x (Finset.mem_range.mp hx)) ⟨a (m + 1 - x), 0, by simp⟩
  -- Define D = B * B0inv - 1, so B = B0 * (1 + D), (1 + D) * (A * B0) = 1, coeff 0 D = 0!
  set D : PowerSeries ℚ := B * B0inv - 1
  have hB_eq : B = B0 * (1 + D) := by
    have : B0 * (1 + (B * B0inv - 1)) = B * (B0inv * B0) := by ring
    rw [this, hB0inv, mul_one]
  have hD_rel : (1 + D) * (A * B0) = 1 := by
    have : (1 + D) * (A * B0) = (B0 * (1 + D)) * A := by ring
    rw [this, ← hB_eq, hBA]
  have hD0 : PowerSeries.coeff 0 D = 0 := by
    have h0 := congr_arg (PowerSeries.coeff 0) hD_rel
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j => PowerSeries.coeff i (1 + D) * PowerSeries.coeff j (A * B0))] at h0
    have hAB0 : PowerSeries.coeff 0 (A * B0) = 1 := by
      rw [PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (f := fun i j => PowerSeries.coeff i A * PowerSeries.coeff j B0)]
      simp [A, B0, ha0, b0Int]
    simp only [Finset.range_one, Finset.sum_singleton, Nat.sub_zero, map_add, PowerSeries.coeff_one,
      ↓reduceIte, hAB0, mul_one] at h0
    linarith
  have hD_half : ∀ m : ℕ, IsHalfInt (PowerSeries.coeff m D) := by
    intro m
    simp only [D, map_sub, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j => PowerSeries.coeff i B * PowerSeries.coeff j B0inv),
      PowerSeries.coeff_one]
    have h1 := isHalfInt_sum (Finset.range (m + 1)) _ fun x _ =>
      isHalfInt_mul (hB_half x) (hB0inv_half (m - x))
    split_ifs
    · exact isHalfInt_sub h1 ⟨1, 0, by simp⟩
    · simpa using h1
  have hAB0_half : ∀ m : ℕ, IsHalfInt (PowerSeries.coeff m (A * B0)) := by
    intro m
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j => PowerSeries.coeff i A * PowerSeries.coeff j B0)]
    exact isHalfInt_sum _ _ fun x _ => isHalfInt_mul ⟨a x, 0, by simp [A]⟩ (B0_halfInt (m - x))
  have hDr_zero : ∀ r m : ℕ, m < r → PowerSeries.coeff m (D ^ r) = 0 := by
    intro r
    induction r with
    | zero => intro m hm; omega
    | succ r ihr =>
      intro m hm
      rw [pow_succ, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (f := fun i j => PowerSeries.coeff i (D ^ r) * PowerSeries.coeff j D)]
      refine Finset.sum_eq_zero fun x hx => ?_
      have hxm : x ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
      by_cases hxr : x < r
      · rw [ihr x hxr, zero_mul]
      · have : m - x = 0 := by omega
        rw [this, hD0, mul_zero]
  -- Strong induction on k: prove (3 : ℤ) ∣ (a k - a0 k)!
  have h3_dvd : ∀ k : ℕ, (3 : ℤ) ∣ (a k - a0 k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero => simp [ha0, a0, noTwo3_zero]
      | succ k =>
        -- 1) For 1 <= m <= k, coeff m (A * B0) is IsDiv3Half!
        have hAB0_div3 : ∀ m : ℕ, 0 < m → m ≤ k → IsDiv3Half (PowerSeries.coeff m (A * B0)) := by
          intro m hm hmk
          have hsplit : PowerSeries.coeff m (A * B0) =
              PowerSeries.coeff m ((A - A0) * B0) + PowerSeries.coeff m (A0 * B0 - 1) := by
            have : (A - A0) * B0 + (A0 * B0 - 1) = A * B0 - 1 := by ring
            have hc := congr_arg (PowerSeries.coeff m) this
            rw [map_add] at hc
            conv_rhs at hc => rw [map_sub, PowerSeries.coeff_one, if_neg (by omega : m ≠ 0), sub_zero]
            exact hc.symm
          rw [hsplit]
          refine isDiv3Half_add ?_ (A0_B0_mod3 m)
          rw [PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (f := fun i j => PowerSeries.coeff i (A - A0) * PowerSeries.coeff j B0)]
          refine isDiv3Half_sum _ _ fun x hx => ?_
          have hxm : x ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
          simp only [map_sub, A, A0, PowerSeries.coeff_mk, ← Int.cast_sub]
          exact isDiv3Half_mul_halfInt (isDiv3Half_of_int (ih x (by omega))) (B0_halfInt (m - x))
        -- 2) For m <= k, coeff m D is IsDiv3Half!
        have hD_div3 : ∀ m : ℕ, m ≤ k → IsDiv3Half (PowerSeries.coeff m D) := by
          intro m hmk
          induction m using Nat.strong_induction_on with
          | h m ihm =>
            cases m with
            | zero => rw [hD0]; exact isDiv3Half_zero
            | succ m =>
              have hm := congr_arg (PowerSeries.coeff (m + 1)) hD_rel
              rw [PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (f := fun i j => PowerSeries.coeff i (1 + D) * PowerSeries.coeff j (A * B0))] at hm
              rw [Finset.sum_range_succ, Finset.sum_range_succ'] at hm
              have hAB0_0 : PowerSeries.coeff 0 (A * B0) = 1 := by
                rw [PowerSeries.coeff_mul,
                  Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                    (f := fun i j => PowerSeries.coeff i A * PowerSeries.coeff j B0)]
                simp [A, B0, ha0, b0Int]
              simp only [Nat.sub_self, Nat.sub_zero, map_add, PowerSeries.coeff_one,
                Nat.succ_ne_zero, ↓reduceIte, zero_add, hAB0_0, mul_one, hD0, add_zero, one_mul] at hm
              have heq : PowerSeries.coeff (m + 1) D =
                  -(PowerSeries.coeff (m + 1) (A * B0) +
                    ∑ x ∈ Finset.range m,
                      PowerSeries.coeff (x + 1) D * PowerSeries.coeff (m + 1 - (x + 1)) (A * B0)) := by
                linarith
              rw [heq]
              refine isDiv3Half_neg (isDiv3Half_add (hAB0_div3 (m + 1) (by omega) hmk)
                (isDiv3Half_sum _ _ fun x hx => ?_))
              have hxm : x < m := Finset.mem_range.mp hx
              exact isDiv3Half_mul_halfInt (ihm (x + 1) (by omega) (by omega))
                (hAB0_half (m + 1 - (x + 1)))
        -- 3) At k + 1: coeff (k + 1) D + (a (k + 1) - a0 (k + 1)) is IsDiv3Half!
        have hDk_rel : IsDiv3Half (PowerSeries.coeff (k + 1) D + ((a (k + 1) - a0 (k + 1) : ℤ) : ℚ)) := by
          have hk1 := congr_arg (PowerSeries.coeff (k + 1)) hD_rel
          rw [PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (f := fun i j => PowerSeries.coeff i (1 + D) * PowerSeries.coeff j (A * B0))] at hk1
          rw [Finset.sum_range_succ, Finset.sum_range_succ'] at hk1
          have hAB0_0 : PowerSeries.coeff 0 (A * B0) = 1 := by
            rw [PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (f := fun i j => PowerSeries.coeff i A * PowerSeries.coeff j B0)]
            simp [A, B0, ha0, b0Int]
          simp only [Nat.sub_self, Nat.sub_zero, map_add, PowerSeries.coeff_one,
            Nat.succ_ne_zero, ↓reduceIte, zero_add, hAB0_0, mul_one, hD0, add_zero, one_mul] at hk1
          -- Also decompose coeff (k + 1) (A * B0) = (a (k+1) - a0 (k+1)) + IsDiv3Half!
          have hAB0_k1 : IsDiv3Half (PowerSeries.coeff (k + 1) (A * B0) - ((a (k + 1) - a0 (k + 1) : ℤ) : ℚ)) := by
            have hsp : PowerSeries.coeff (k + 1) (A * B0) =
                PowerSeries.coeff (k + 1) ((A - A0) * B0) + PowerSeries.coeff (k + 1) (A0 * B0 - 1) := by
              have : (A - A0) * B0 + (A0 * B0 - 1) = A * B0 - 1 := by ring
              have hc := congr_arg (PowerSeries.coeff (k + 1)) this
              rw [map_add] at hc
              conv_rhs at hc => rw [map_sub, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero k), sub_zero]
              exact hc.symm
            rw [hsp, PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (f := fun i j => PowerSeries.coeff i (A - A0) * PowerSeries.coeff j B0),
              Finset.sum_range_succ]
            have hB0_0 : PowerSeries.coeff 0 B0 = 1 := by simp [B0, b0Int]
            simp only [Nat.sub_self, hB0_0, mul_one, map_sub, A, A0, PowerSeries.coeff_mk,
              ← Int.cast_sub]
            have hrew : (∑ x ∈ Finset.range (k + 1), ((a x - a0 x : ℤ) : ℚ) * PowerSeries.coeff (k + 1 - x) B0) +
                ((a (k + 1) - a0 (k + 1) : ℤ) : ℚ) + PowerSeries.coeff (k + 1) (A0 * B0 - 1) -
                ((a (k + 1) - a0 (k + 1) : ℤ) : ℚ) =
                (∑ x ∈ Finset.range (k + 1), ((a x - a0 x : ℤ) : ℚ) * PowerSeries.coeff (k + 1 - x) B0) +
                PowerSeries.coeff (k + 1) (A0 * B0 - 1) := by ring
            rw [show PowerSeries.coeff (k + 1) (PowerSeries.mk (fun k => (a0 k : ℚ)) * B0) -
                PowerSeries.coeff (k + 1) 1 = PowerSeries.coeff (k + 1) (A0 * B0 - 1) by
                  simp [A0, map_sub], hrew]
            refine isDiv3Half_add (isDiv3Half_sum _ _ fun x hx => ?_) (A0_B0_mod3 (k + 1))
            exact isDiv3Half_mul_halfInt (isDiv3Half_of_int (ih x (Finset.mem_range.mp hx)))
              (B0_halfInt (k + 1 - x))
          have hmid : IsDiv3Half (∑ x ∈ Finset.range k,
              PowerSeries.coeff (x + 1) D * PowerSeries.coeff (k + 1 - (x + 1)) (A * B0)) := by
            refine isDiv3Half_sum _ _ fun x hx => ?_
            have hxk : x < k := Finset.mem_range.mp hx
            exact isDiv3Half_mul_halfInt (hD_div3 (x + 1) (by omega)) (hAB0_half (k + 1 - (x + 1)))
          have heq : PowerSeries.coeff (k + 1) D + ((a (k + 1) - a0 (k + 1) : ℤ) : ℚ) =
              -(PowerSeries.coeff (k + 1) (A * B0) - ((a (k + 1) - a0 (k + 1) : ℤ) : ℚ)) -
              (∑ x ∈ Finset.range k,
                PowerSeries.coeff (x + 1) D * PowerSeries.coeff (k + 1 - (x + 1)) (A * B0)) := by
            linarith
          rw [heq]
          exact isDiv3Half_sub (isDiv3Half_neg hAB0_k1) hmid
        -- 4) Powers of D: IsDiv3Half for 1 ≤ r and (m ≤ k ∨ 2 ≤ r)
        have hDr_div3 : ∀ r m : ℕ, 1 ≤ r → (m ≤ k ∨ (m = k + 1 ∧ 2 ≤ r)) →
            IsDiv3Half (PowerSeries.coeff m (D ^ r)) := by
          intro r
          induction r with
          | zero => intro m hr; omega
          | succ r ihr =>
            intro m _ hm
            by_cases hr0 : r = 0
            · subst hr0
              simp only [Nat.zero_add, pow_one]
              rcases hm with hle | ⟨_, h2⟩
              · exact hD_div3 m hle
              · omega
            · rw [pow_succ, PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (f := fun i j => PowerSeries.coeff i (D ^ r) * PowerSeries.coeff j D)]
              refine isDiv3Half_sum _ _ fun x hx => ?_
              have hxm : x ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
              by_cases hmx0 : m - x = 0
              · rw [hmx0, hD0, mul_zero]; exact isDiv3Half_zero
              · have hxl : x ≤ k := by omega
                exact isDiv3Half_mul_halfInt (ihr x (by omega) (Or.inl hxl)) (hD_half (m - x))
        -- 5) Expand coeff (k + 1) ((1 + X)^(n*(n-1)/2) * B^n) = ∑ j, ∑ r, coeff (k+1-j) (D^r) * coeff j F_n * C(n, r)
        have hcoeff_expand : ∀ n : ℕ,
            PowerSeries.coeff (k + 1) ((1 + PowerSeries.X) ^ (n * (n - 1) / 2) * B ^ n) =
            ∑ j ∈ Finset.range (k + 2), ∑ r ∈ Finset.range (k + 1 - j + 1),
              PowerSeries.coeff (k + 1 - j) (D ^ r) *
                (PowerSeries.coeff j ((1 + PowerSeries.X) ^ (n * (n - 1) / 2) * B0 ^ n) *
                  (Nat.choose n r : ℚ)) := by
          intro n
          rw [hB_eq, mul_pow, ← mul_assoc, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (f := fun i j => PowerSeries.coeff i ((1 + PowerSeries.X : PowerSeries ℚ) ^ (n * (n - 1) / 2) * B0 ^ n) *
                PowerSeries.coeff j ((1 + D) ^ n))]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjk : j ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have h1D : PowerSeries.coeff (k + 1 - j) ((1 + D) ^ n) =
              ∑ r ∈ Finset.range (k + 1 - j + 1),
                (Nat.choose n r : ℚ) * PowerSeries.coeff (k + 1 - j) (D ^ r) := by
            rw [add_comm 1 D, add_pow, map_sum]
            have hterm : ∀ r,
                PowerSeries.coeff (k + 1 - j) (D ^ r * 1 ^ (n - r) * ((Nat.choose n r : ℕ) : PowerSeries ℚ)) =
                (Nat.choose n r : ℚ) * PowerSeries.coeff (k + 1 - j) (D ^ r) := by
              intro r
              rw [one_pow, mul_one, mul_comm, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
            simp_rw [hterm]
            by_cases hle : n ≤ k + 1 - j
            · refine Finset.sum_subset (Finset.range_mono (by omega)) fun r _ hr => ?_
              simp only [Finset.mem_range, not_lt] at hr
              simp [Nat.choose_eq_zero_of_lt (by omega : n < r)]
            · symm
              refine Finset.sum_subset (Finset.range_mono (by omega)) fun r _ hr => ?_
              simp only [Finset.mem_range, not_lt] at hr
              rw [hDr_zero r (k + 1 - j) (by omega), mul_zero]
          rw [h1D, Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => by ring
        -- 6) Sum over n via hasSum_F_n_choose and extract coeff (k + 1) D!
        choose M hM_half hM_div3 hM_sum using hasSum_F_n_choose
        have hHasSum_rhs : HasSum (fun n : ℕ =>
            ((PowerSeries.coeff (k + 1) ((1 + PowerSeries.X) ^ (n * (n - 1) / 2) * B ^ n) : ℚ) : ℝ) /
              2 ^ (n + 1))
            ((∑ j ∈ Finset.range (k + 2), ∑ r ∈ Finset.range (k + 1 - j + 1),
              PowerSeries.coeff (k + 1 - j) (D ^ r) * M j r : ℚ) : ℝ) := by
          have h1 : HasSum (fun n : ℕ =>
              ∑ j ∈ Finset.range (k + 2), ∑ r ∈ Finset.range (k + 1 - j + 1),
                ((PowerSeries.coeff (k + 1 - j) (D ^ r) : ℚ) : ℝ) *
                  (((PowerSeries.coeff j ((1 + PowerSeries.X) ^ (n * (n - 1) / 2) * B0 ^ n) : ℚ) : ℝ) *
                    (Nat.choose n r : ℝ) / 2 ^ (n + 1)))
              (∑ j ∈ Finset.range (k + 2), ∑ r ∈ Finset.range (k + 1 - j + 1),
                ((PowerSeries.coeff (k + 1 - j) (D ^ r) : ℚ) : ℝ) * (M j r : ℝ)) :=
            hasSum_sum fun j _ => hasSum_sum fun r _ => (hM_sum j r).mul_left _
          have hcast : (∑ j ∈ Finset.range (k + 2), ∑ r ∈ Finset.range (k + 1 - j + 1),
                ((PowerSeries.coeff (k + 1 - j) (D ^ r) : ℚ) : ℝ) * (M j r : ℝ)) =
              ((∑ j ∈ Finset.range (k + 2), ∑ r ∈ Finset.range (k + 1 - j + 1),
                PowerSeries.coeff (k + 1 - j) (D ^ r) * M j r : ℚ) : ℝ) := by
            push_cast; rfl
          rw [hcast] at h1
          refine h1.congr_fun fun n => ?_
          rw [hcoeff_expand n]
          push_cast
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun r _ => by ring
        have htotal0 : (∑ j ∈ Finset.range (k + 2), ∑ r ∈ Finset.range (k + 1 - j + 1),
            PowerSeries.coeff (k + 1 - j) (D ^ r) * M j r) = 0 := by
          have hu := hHasSum_rhs.unique (hsum_eq (k + 1))
          simp only [Nat.succ_ne_zero, ↓reduceIte] at hu
          exact_mod_cast hu
        have hM01 : M 0 1 = 1 := by
          have h1 := hM_sum 0 1
          have h0 : ∀ n : ℕ, PowerSeries.coeff 0 ((1 + PowerSeries.X) ^ (n * (n - 1) / 2) * B0 ^ n) = 1 := by
            intro n; rw [PowerSeries.coeff_zero_eq_constantCoeff]; simp [B0, b0Int]
          simp only [h0, Rat.cast_one, one_mul] at h1
          exact_mod_cast h1.unique (hasSum_choose_div_pow2 1)
        have hterm_div3 : ∀ j ∈ Finset.range (k + 2), ∀ r ∈ Finset.range (k + 1 - j + 1),
            ¬(j = 0 ∧ r = 1) → IsDiv3Half (PowerSeries.coeff (k + 1 - j) (D ^ r) * M j r) := by
          intro j hj r _ hne
          have hjk : j ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          by_cases hr0 : r = 0
          · subst hr0
            simp only [pow_zero, PowerSeries.coeff_one]
            by_cases hkj : k + 1 - j = 0
            · have hjeq : j = k + 1 := by omega
              rw [hkj, hjeq]; simp only [↓reduceIte, one_mul]
              exact hM_div3 (k + 1) 0 rfl (by omega)
            · simp only [hkj, ↓reduceIte, zero_mul]; exact isDiv3Half_zero
          · refine isDiv3Half_mul_halfInt (hDr_div3 r (k + 1 - j) (by omega) ?_) (hM_half j r)
            by_cases hj0 : j = 0
            · subst hj0; exact Or.inr ⟨by omega, by omega⟩
            · exact Or.inl (by omega)
        have hDk1_div3 : IsDiv3Half (PowerSeries.coeff (k + 1) D) := by
          have h0_mem : 0 ∈ Finset.range (k + 2) := Finset.mem_range.mpr (by omega)
          have h1_mem : 1 ∈ Finset.range (k + 2) := Finset.mem_range.mpr (by omega)
          have hsplit : (∑ j ∈ Finset.range (k + 2), ∑ r ∈ Finset.range (k + 1 - j + 1),
                PowerSeries.coeff (k + 1 - j) (D ^ r) * M j r) =
              PowerSeries.coeff (k + 1) D +
              (∑ j ∈ Finset.range (k + 2), ∑ r ∈ Finset.range (k + 1 - j + 1),
                if j = 0 ∧ r = 1 then 0 else PowerSeries.coeff (k + 1 - j) (D ^ r) * M j r) := by
            have hinner : ∀ j ∈ Finset.range (k + 2),
                (∑ r ∈ Finset.range (k + 1 - j + 1), PowerSeries.coeff (k + 1 - j) (D ^ r) * M j r) =
                (if j = 0 then PowerSeries.coeff (k + 1) D else 0) +
                ∑ r ∈ Finset.range (k + 1 - j + 1),
                  if j = 0 ∧ r = 1 then 0 else PowerSeries.coeff (k + 1 - j) (D ^ r) * M j r := by
              intro j _
              by_cases hj0 : j = 0
              · subst hj0
                simp only [↓reduceIte, Nat.sub_zero, true_and]
                rw [← Finset.add_sum_erase _ _ h1_mem, ← Finset.add_sum_erase _ _ h1_mem]
                simp only [↓reduceIte, zero_add, pow_one, hM01, mul_one]
                congr 1
                refine Finset.sum_congr rfl fun r hr => ?_
                simp [(Finset.mem_erase.mp hr).1]
              · simp [hj0]
            rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib]
            congr 1
            rw [Finset.sum_eq_single 0]
            · simp
            · intro j _ hj0; simp [hj0]
            · intro h; exact absurd h0_mem h
          rw [hsplit] at htotal0
          have hrest : IsDiv3Half (∑ j ∈ Finset.range (k + 2), ∑ r ∈ Finset.range (k + 1 - j + 1),
              if j = 0 ∧ r = 1 then 0 else PowerSeries.coeff (k + 1 - j) (D ^ r) * M j r) := by
            refine isDiv3Half_sum _ _ fun j hj => isDiv3Half_sum _ _ fun r hr => ?_
            split_ifs with hcond
            · exact isDiv3Half_zero
            · exact hterm_div3 j hj r hr hcond
          have heq : PowerSeries.coeff (k + 1) D =
              -(∑ j ∈ Finset.range (k + 2), ∑ r ∈ Finset.range (k + 1 - j + 1),
                if j = 0 ∧ r = 1 then 0 else PowerSeries.coeff (k + 1 - j) (D ^ r) * M j r) := by
            linarith
          rw [heq]; exact isDiv3Half_neg hrest
        have hdiff_div3 : IsDiv3Half ((a (k + 1) - a0 (k + 1) : ℤ) : ℚ) := by
          have hsub := isDiv3Half_sub hDk_rel hDk1_div3
          simpa using hsub
        exact isDiv3Half_to_int_dvd hdiff_div3
  intro k
  have hd := h3_dvd k
  obtain ⟨q, hq⟩ := hd
  have : a k = a0 k + 3 * q := by linarith
  rw [this]
  simp only [a0, noTwo3]
  have hiff : (∀ d ∈ Nat.digits 3 k, d ≠ 2) ↔ 2 ∉ Nat.digits 3 k :=
    ⟨fun h hm => h 2 hm rfl, fun h d hd heq => h (heq ▸ hd)⟩
  simp only [hiff]
  split_ifs <;> omega

end OMA.S_oeis_a325286

theorem OMA.solution : type_of% @OMA.S_oeis_a325286.main :=
  OMA.S_oeis_a325286.main_proved
