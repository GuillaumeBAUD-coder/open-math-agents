import OMAStatements.S_oeis_a360278
import Mathlib

-- Problem: OEIS A360278, det[L(j+k) + d(j,k)] and three conjectures on such determinants
-- for the sequences v(n+1) = A v(n) +- v(n-1) and for the Fibonacci numbers.
-- Statement: statements/oeis-a360278.lean (declaration OMA.S_oeis_a360278.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let u(0) = 0, u(1) = 1, u(n+2) = A u(n+1) + e u(n) and V(n) = 2 u(n+1) - A u(n)
-- (e = 1 or -1). The addition formulas for u give
--   2 V(j+k) = V(j) V(k) + (A^2 + 4e) u(j) u(k),   2 u(j+k) = u(j) V(k) + V(j) u(k),
-- so each matrix [f(j+k)] is a product of an n X 2 and a 2 X n matrix, and
-- det(1 + P Q) = det(1 + Q P) reduces the determinant to a 2 X 2 determinant whose entries are
-- the sums of u(k)^2, u(k) V(k) and V(k)^2 over 1 <= k <= n (lemmas det_rank2, D_formula).
-- With x = u(n), y = u(n+1): V(k)^2 = (A^2 + 4e) u(k)^2 + 4 (-e)^k, and
-- * e = 1: A sum u(k)^2 = x y, A sum u(k) V(k) = x^2 + y^2 - 1;
-- * e = -1: sum u(k) V(k) = x y, (A^2 - 4) sum u(k)^2 = y^2 - x^2 - 1 - 2n.
-- The three formulas then follow from the identity y^2 - A x y - e x^2 = (-e)^n.

namespace OMA.A360278

open OMA.S_oeis_a360278 Finset

/-- u(0) = 0, u(1) = 1, u(n+2) = A u(n+1) + e u(n). -/
def u (A e : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => A * u A e (n + 1) + e * u A e n

/-- V(n) = 2 u(n+1) - A u(n). -/
def V (A e : ℤ) (n : ℕ) : ℤ := 2 * u A e (n + 1) - A * u A e n

variable (A e : ℤ)

lemma u_succ (n : ℕ) : u A e (n + 2) = A * u A e (n + 1) + e * u A e n := rfl

lemma add1 (m k : ℕ) :
    u A e (m + k + 1) = u A e (m + 1) * u A e (k + 1) + e * u A e m * u A e k ∧
    u A e (m + (k + 1) + 1) = u A e (m + 1) * u A e (k + 1 + 1) + e * u A e m * u A e (k + 1) := by
  induction k with
  | zero =>
    refine ⟨by simp [u], ?_⟩
    show u A e (m + 2) = _
    rw [u_succ]
    simp [u]
    ring
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have h1 : u A e (m + (k + 1 + 1) + 1) = A * u A e (m + (k + 1) + 1) + e * u A e (m + k + 1) := rfl
    rw [h1, ih.1, ih.2, u_succ A e (k + 1), u_succ A e k]
    ring

lemma add0 (m k : ℕ) :
    u A e (m + k) = u A e (m + 1) * u A e k + u A e m * u A e (k + 1) - A * u A e m * u A e k ∧
    u A e (m + (k + 1)) = u A e (m + 1) * u A e (k + 1) + u A e m * u A e (k + 1 + 1)
      - A * u A e m * u A e (k + 1) := by
  induction k with
  | zero =>
    refine ⟨by simp [u], ?_⟩
    rw [u_succ]
    simp [u]
    ring
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have h1 : u A e (m + (k + 1 + 1)) = A * u A e (m + (k + 1)) + e * u A e (m + k) := rfl
    rw [h1, ih.1, ih.2, u_succ A e (k + 1), u_succ A e k]
    ring

lemma cassini (n : ℕ) :
    u A e (n + 1) ^ 2 - A * u A e n * u A e (n + 1) - e * u A e n ^ 2 = (-e) ^ n := by
  induction n with
  | zero => simp [u]
  | succ n ih =>
    have hp : (-e) ^ (n + 1) = (-e) ^ n * (-e) := pow_succ _ _
    rw [u_succ, hp, ← ih]
    ring

lemma V_zero : V A e 0 = 2 := by simp [V, u]

lemma V_one : V A e 1 = A := by
  simp only [V, u]
  ring

lemma V_succ (n : ℕ) : V A e (n + 2) = A * V A e (n + 1) + e * V A e n := by
  simp only [V, u_succ]
  ring

/-- 2 V(j+k) = V(j) V(k) + (A^2 + 4e) u(j) u(k). -/
lemma two_V (j k : ℕ) :
    2 * V A e (j + k) = V A e j * V A e k + (A ^ 2 + 4 * e) * u A e j * u A e k := by
  have h1 := (add1 A e j k).1
  have h0 := (add0 A e j k).1
  simp only [V]
  rw [h1, h0]
  ring

/-- 2 u(j+k) = u(j) V(k) + V(j) u(k). -/
lemma two_u (j k : ℕ) : 2 * u A e (j + k) = u A e j * V A e k + V A e j * u A e k := by
  have h0 := (add0 A e j k).1
  simp only [V]
  rw [h0]
  ring

lemma V_sq (k : ℕ) : V A e k ^ 2 = (A ^ 2 + 4 * e) * u A e k ^ 2 + 4 * (-e) ^ k := by
  rw [← cassini A e k]
  simp only [V]
  ring

/-- The determinant of the identity plus a matrix of rank at most 2. -/
lemma det_rank2 {n : ℕ} (p q r s : Fin n → ℚ) :
    (1 + Matrix.of fun i j => p i * r j + q i * s j).det
      = (1 + ∑ i, r i * p i) * (1 + ∑ i, s i * q i) - (∑ i, r i * q i) * (∑ i, s i * p i) := by
  let P : Matrix (Fin n) (Fin 2) ℚ := Matrix.of fun i k => if k = 0 then p i else q i
  let Q : Matrix (Fin 2) (Fin n) ℚ := Matrix.of fun k j => if k = 0 then r j else s j
  have hPQ : P * Q = Matrix.of fun i j => p i * r j + q i * s j := by
    ext i j
    simp [P, Q, Matrix.mul_apply, Fin.sum_univ_two]
  have hQP : Q * P = !![∑ i, r i * p i, ∑ i, r i * q i; ∑ i, s i * p i, ∑ i, s i * q i] := by
    ext k l
    fin_cases k <;> fin_cases l <;> simp [P, Q, Matrix.mul_apply]
  rw [← hPQ, Matrix.det_one_add_mul_comm, hQP, Matrix.det_fin_two]
  simp

/-- The determinant of the statement over the rationals. -/
lemma D_cast (f : ℕ → ℤ) (n : ℕ) :
    ((D f n : ℤ) : ℚ)
      = (1 + Matrix.of fun (i j : Fin n) => (f (((i : ℕ) + 1) + ((j : ℕ) + 1)) : ℚ)).det := by
  unfold D
  rw [show (((Matrix.of fun (j k : Fin n) =>
      f (((j : ℕ) + 1) + ((k : ℕ) + 1)) + if j = k then 1 else 0).det : ℤ) : ℚ)
      = (Int.castRingHom ℚ) (Matrix.of fun (j k : Fin n) =>
        f (((j : ℕ) + 1) + ((k : ℕ) + 1)) + if j = k then 1 else 0).det from rfl,
    RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · simp [h, Matrix.one_apply, add_comm]
  · simp [h, Matrix.one_apply]

/-- The value of the determinant for a matrix with the entries `(a(j) b(k) + c(j) d(k)) / 2`. -/
lemma D_formula (f a b c d : ℕ → ℤ) (n : ℕ)
    (h : ∀ j k, 2 * f (j + k) = a j * b k + c j * d k) :
    4 * D f n = (2 + ∑ i ∈ range n, b (i + 1) * a (i + 1)) * (2 + ∑ i ∈ range n, d (i + 1) * c (i + 1))
      - (∑ i ∈ range n, b (i + 1) * c (i + 1)) * (∑ i ∈ range n, d (i + 1) * a (i + 1)) := by
  have hq : (4 * D f n : ℚ) = ((2 + ∑ i ∈ range n, b (i + 1) * a (i + 1)) *
      (2 + ∑ i ∈ range n, d (i + 1) * c (i + 1))
      - (∑ i ∈ range n, b (i + 1) * c (i + 1)) * (∑ i ∈ range n, d (i + 1) * a (i + 1)) : ℤ) := by
    rw [D_cast]
    have hm : (Matrix.of fun (i j : Fin n) => (f (((i : ℕ) + 1) + ((j : ℕ) + 1)) : ℚ))
        = Matrix.of fun (i j : Fin n) => ((a ((i : ℕ) + 1) : ℚ) / 2) * (b ((j : ℕ) + 1) : ℚ)
          + ((c ((i : ℕ) + 1) : ℚ) / 2) * (d ((j : ℕ) + 1) : ℚ) := by
      ext i j
      have := h ((i : ℕ) + 1) ((j : ℕ) + 1)
      have hc : (2 : ℚ) * (f (((i : ℕ) + 1) + ((j : ℕ) + 1)) : ℚ)
          = (a ((i : ℕ) + 1) : ℚ) * (b ((j : ℕ) + 1) : ℚ) + (c ((i : ℕ) + 1) : ℚ) * (d ((j : ℕ) + 1) : ℚ) := by
        exact_mod_cast this
      simp only [Matrix.of_apply]
      linarith
    rw [hm, det_rank2]
    have e1 : ∀ g : ℕ → ℚ, ∑ i : Fin n, g ((i : ℕ) + 1) = ∑ i ∈ range n, g (i + 1) :=
      fun g => Fin.sum_univ_eq_sum_range (fun i => g (i + 1)) n
    rw [e1 (fun m => (b m : ℚ) * ((a m : ℚ) / 2)), e1 (fun m => (d m : ℚ) * ((c m : ℚ) / 2)),
      e1 (fun m => (b m : ℚ) * ((c m : ℚ) / 2)), e1 (fun m => (d m : ℚ) * ((a m : ℚ) / 2))]
    have e2 : ∀ g1 g2 : ℕ → ℤ, ∑ i ∈ range n, (g1 (i + 1) : ℚ) * ((g2 (i + 1) : ℚ) / 2)
        = (((∑ i ∈ range n, g1 (i + 1) * g2 (i + 1) : ℤ) : ℚ)) / 2 := by
      intro g1 g2
      push_cast
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e2, e2, e2, e2]
    push_cast
    ring
  exact_mod_cast hq

lemma r_sq (n : ℕ) : (((n % 2 : ℕ) : ℤ)) ^ 2 = ((n % 2 : ℕ) : ℤ) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

lemma neg_one_pow_eq (n : ℕ) : (-1 : ℤ) ^ n = 1 - 2 * ((n % 2 : ℕ) : ℤ) := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow, Nat.even_iff.mp h]
    simp
  · rw [h.neg_one_pow, Nat.odd_iff.mp h]
    norm_num

lemma sum_signs (n : ℕ) : ∑ i ∈ range n, (-1 : ℤ) ^ (i + 1) = -((n % 2 : ℕ) : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ, neg_one_pow_eq n]
    have : ((n + 1) % 2 : ℕ) = 1 - n % 2 := by omega
    rw [this]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

/-- A sum of u(k) V(k): A times it is u(n)^2 + u(n+1)^2 - 1 for e = 1. -/
lemma sum_uV_P (n : ℕ) :
    A * ∑ i ∈ range n, u A 1 (i + 1) * V A 1 (i + 1) = u A 1 n ^ 2 + u A 1 (n + 1) ^ 2 - 1 := by
  induction n with
  | zero => simp [u]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    simp only [V, u_succ]
    ring

lemma sum_uu_P (n : ℕ) :
    A * ∑ i ∈ range n, u A 1 (i + 1) * u A 1 (i + 1) = u A 1 n * u A 1 (n + 1) := by
  induction n with
  | zero => simp [u]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    simp only [u_succ]
    ring

lemma sum_VV (e : ℤ) (n : ℕ) :
    ∑ i ∈ range n, V A e (i + 1) * V A e (i + 1)
      = (A ^ 2 + 4 * e) * ∑ i ∈ range n, u A e (i + 1) * u A e (i + 1)
        + 4 * ∑ i ∈ range n, (-e) ^ (i + 1) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := V_sq A e (i + 1)
  linear_combination this

lemma sum_uV_M (n : ℕ) :
    ∑ i ∈ range n, u A (-1) (i + 1) * V A (-1) (i + 1) = u A (-1) n * u A (-1) (n + 1) := by
  induction n with
  | zero => simp [u]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [V, u_succ]
    ring

lemma sum_uu_M (n : ℕ) :
    (A ^ 2 - 4) * ∑ i ∈ range n, u A (-1) (i + 1) * u A (-1) (i + 1)
      = u A (-1) (n + 1) ^ 2 - u A (-1) n ^ 2 - 1 - 2 * (n : ℤ) := by
  induction n with
  | zero => simp [u]
  | succ n ih =>
    have hc := cassini A (-1) n
    simp only [neg_neg, one_pow] at hc
    rw [Finset.sum_range_succ, mul_add, ih]
    simp only [u_succ]
    push_cast
    linear_combination (-2 : ℤ) * hc

/-- The four sums in the general form of `D_formula`. -/
lemma D_V (e : ℤ) (n : ℕ) :
    4 * D (V A e) n
      = (2 + ((A ^ 2 + 4 * e) * ∑ i ∈ range n, u A e (i + 1) * u A e (i + 1)
          + 4 * ∑ i ∈ range n, (-e) ^ (i + 1)))
        * (2 + (A ^ 2 + 4 * e) * ∑ i ∈ range n, u A e (i + 1) * u A e (i + 1))
        - (A ^ 2 + 4 * e) * (∑ i ∈ range n, u A e (i + 1) * V A e (i + 1)) ^ 2 := by
  have h := D_formula (V A e) (V A e) (V A e) (fun m => (A ^ 2 + 4 * e) * u A e m) (u A e) n
    (fun j k => by rw [two_V])
  rw [h, sum_VV]
  have e1 : ∑ i ∈ range n, u A e (i + 1) * ((A ^ 2 + 4 * e) * u A e (i + 1))
      = (A ^ 2 + 4 * e) * ∑ i ∈ range n, u A e (i + 1) * u A e (i + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i ∈ range n, V A e (i + 1) * ((A ^ 2 + 4 * e) * u A e (i + 1))
      = (A ^ 2 + 4 * e) * ∑ i ∈ range n, u A e (i + 1) * V A e (i + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  ring

theorem conj1 (n : ℕ) :
    A ^ 2 * D (V A 1) n = V A 1 (n + 1) ^ 2 - (A ^ 2 + 4) * ((n % 2 : ℕ) : ℤ) := by
  have h4 := D_V A 1 n
  have hS := sum_signs n
  have hc := cassini A 1 n
  rw [neg_one_pow_eq] at hc
  have hr := r_sq n
  have huu := sum_uu_P A n
  have huv := sum_uV_P A n
  simp only [mul_one] at h4
  rw [hS] at h4
  set r : ℤ := ((n % 2 : ℕ) : ℤ) with hrdef
  set x := u A 1 n with hx
  set y := u A 1 (n + 1) with hy
  set Suu := ∑ i ∈ range n, u A 1 (i + 1) * u A 1 (i + 1) with hSuu
  set Suv := ∑ i ∈ range n, u A 1 (i + 1) * V A 1 (i + 1) with hSuv
  have hV : V A 1 (n + 1) = A * y + 2 * x := by
    simp only [V, u_succ, hx, hy]
    ring
  rw [hV]
  have step1 : 4 * (A ^ 2 * D (V A 1) n)
      = (2 * A + (A ^ 2 + 4) * (A * Suu) - 4 * r * A) * (2 * A + (A ^ 2 + 4) * (A * Suu))
        - (A ^ 2 + 4) * (A * Suv) ^ 2 := by
    linear_combination A ^ 2 * h4
  rw [huu, huv] at step1
  have step2 : 4 * (A ^ 2 * D (V A 1) n) = 4 * ((A * y + 2 * x) ^ 2 - (A ^ 2 + 4) * r) := by
    rw [step1]
    linear_combination
      ((-2 * A * (2 * A + (A ^ 2 + 4) * (x * y)) + 2 * (A ^ 2 + 4))
        - (A ^ 2 + 4) * ((y ^ 2 - A * x * y - 1 * x ^ 2) + 1 - 2 * r)) * hc
      + (-4 * (A ^ 2 + 4)) * hr
  linarith

theorem conj2 (n : ℕ) : D (V A (-1)) n = u A (-1) (n + 1) ^ 2 - (n : ℤ) ^ 2 := by
  have h4 := D_V A (-1) n
  have hc := cassini A (-1) n
  simp only [neg_neg, one_pow] at hc h4
  have huu := sum_uu_M A n
  have huv := sum_uV_M A n
  have hconst : ∑ i ∈ range n, (1 : ℤ) = (n : ℤ) := by simp
  rw [hconst, huv] at h4
  have e : A ^ 2 + 4 * (-1 : ℤ) = A ^ 2 - 4 := by ring
  rw [e, huu] at h4
  set x := u A (-1) n with hx
  set y := u A (-1) (n + 1) with hy
  have step : 4 * D (V A (-1)) n = 4 * (y ^ 2 - (n : ℤ) ^ 2) := by
    rw [h4]
    linear_combination (2 * A * x * y + (y ^ 2 - A * x * y + x ^ 2 - 1)) * hc
  linarith

theorem conj3 (n : ℕ) : D (u 1 1) n = u 1 1 (n + 1) ^ 2 + ((n % 2 : ℕ) : ℤ) := by
  have h := D_formula (u 1 1) (u 1 1) (V 1 1) (V 1 1) (u 1 1) n (fun j k => two_u 1 1 j k)
  have hS := sum_signs n
  have hc := cassini 1 1 n
  rw [neg_one_pow_eq] at hc
  have hr := r_sq n
  have huu := sum_uu_P 1 n
  have huv := sum_uV_P 1 n
  have hvv := sum_VV 1 1 n
  rw [hS] at hvv
  have e1 : ∑ i ∈ range n, V 1 1 (i + 1) * u 1 1 (i + 1)
      = ∑ i ∈ range n, u 1 1 (i + 1) * V 1 1 (i + 1) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e1, hvv] at h
  rw [one_mul] at huu huv
  rw [huu, huv] at h
  set r : ℤ := ((n % 2 : ℕ) : ℤ) with hrdef
  set x := u 1 1 n with hx
  set y := u 1 1 (n + 1) with hy
  have step : 4 * D (u 1 1) n = 4 * (y ^ 2 + r) := by
    rw [h]
    linear_combination
      ((2 * x * y - 2) + ((y ^ 2 - 1 * x * y - 1 * x ^ 2) + 1 - 2 * r)) * hc + 4 * hr
  linarith

/-- The sequences of the statement. -/
lemma vP_eq (n : ℕ) : vP A n = V A 1 n ∧ vP A (n + 1) = V A 1 (n + 1) := by
  induction n with
  | zero => exact ⟨by rw [V_zero]; rfl, by rw [V_one]; rfl⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have h1 : vP A (n + 1 + 1) = A * vP A (n + 1) + vP A n := rfl
    rw [h1, ih.1, ih.2, V_succ]
    ring

lemma vM_eq (n : ℕ) : vM A n = V A (-1) n ∧ vM A (n + 1) = V A (-1) (n + 1) := by
  induction n with
  | zero => exact ⟨by rw [V_zero]; rfl, by rw [V_one]; rfl⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have h1 : vM A (n + 1 + 1) = A * vM A (n + 1) - vM A n := rfl
    rw [h1, ih.1, ih.2, V_succ]
    ring

lemma uM_eq (n : ℕ) : uM A n = u A (-1) n ∧ uM A (n + 1) = u A (-1) (n + 1) := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have h1 : uM A (n + 1 + 1) = A * uM A (n + 1) - uM A n := rfl
    rw [h1, ih.1, ih.2, u_succ]
    ring

lemma fib_eq (n : ℕ) : (Nat.fib n : ℤ) = u 1 1 n ∧ (Nat.fib (n + 1) : ℤ) = u 1 1 (n + 1) := by
  induction n with
  | zero => exact ⟨by simp [u], by simp [u]⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [Nat.fib_add_two, u_succ]
    push_cast
    rw [ih.1, ih.2]
    ring

theorem result :
    (∀ (A : ℤ) (n : ℕ), 0 < n →
      A ^ 2 * D (vP A) n = vP A (n + 1) ^ 2 - (A ^ 2 + 4) * ((n % 2 : ℕ) : ℤ)) ∧
    (∀ n : ℕ, 0 < n → D (vP 1) n = vP 1 (n + 1) ^ 2 - 5 * ((n % 2 : ℕ) : ℤ)) ∧
    (∀ (A : ℤ) (n : ℕ), 0 < n → D (vM A) n = uM A (n + 1) ^ 2 - (n : ℤ) ^ 2) ∧
    (∀ n : ℕ, 0 < n →
      D (fun m => (Nat.fib m : ℤ)) n = (Nat.fib (n + 1) : ℤ) ^ 2 + ((n % 2 : ℕ) : ℤ)) := by
  have hvP : ∀ A : ℤ, vP A = V A 1 := fun A => funext fun n => (vP_eq A n).1
  have hvM : ∀ A : ℤ, vM A = V A (-1) := fun A => funext fun n => (vM_eq A n).1
  have hfib : (fun m => (Nat.fib m : ℤ)) = u 1 1 := funext fun n => (fib_eq n).1
  refine ⟨fun A n _ => ?_, fun n _ => ?_, fun A n _ => ?_, fun n _ => ?_⟩
  · rw [hvP]
    exact conj1 A n
  · rw [hvP]
    have := conj1 1 n
    linarith
  · rw [hvM, (uM_eq A (n + 1)).1]
    exact conj2 A n
  · rw [hfib, (fib_eq (n + 1)).1]
    exact conj3 n

end OMA.A360278

theorem OMA.solution : type_of% @OMA.S_oeis_a360278.main := OMA.A360278.result
