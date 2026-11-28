import OMAStatements.S_oeis_a360278
import Mathlib

open OMA.S_oeis_a360278

namespace P360278

open Finset

def uP (A : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => A * uP A (n + 1) + uP A n

def fb (m : ℕ) : ℤ := (Nat.fib m : ℤ)

lemma fb_rec (m : ℕ) : fb (m + 2) = 1 * fb (m + 1) + 1 * fb m := by
  simp only [fb, Nat.fib_add_two]; push_cast; ring

lemma det_formula (f p0 p1 q0 q1 : ℕ → ℤ) (n : ℕ)
    (hf : ∀ j k, f (j + k + 2) = p0 j * q0 k + p1 j * q1 k) :
    D f n = (1 + ∑ k ∈ range n, q0 k * p0 k) * (1 + ∑ k ∈ range n, q1 k * p1 k) -
      (∑ k ∈ range n, q0 k * p1 k) * (∑ k ∈ range n, q1 k * p0 k) := by
  let P : Matrix (Fin n) (Fin 2) ℤ := Matrix.of fun j r => ![p0 j, p1 j] r
  let Q : Matrix (Fin 2) (Fin n) ℤ := Matrix.of fun r k => ![q0 k, q1 k] r
  have hM : (Matrix.of fun (j k : Fin n) => f (((j : ℕ) + 1) + ((k : ℕ) + 1)) + if j = k then 1 else 0) =
      1 + P * Q := by
    ext j k
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_two, P, Q,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (j : ℕ) + 1 + ((k : ℕ) + 1) = j + k + 2 by ring, hf]
    ring
  unfold D
  rw [hM, Matrix.det_one_add_mul_comm, Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, P, Q, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, if_true, Fin.zero_eta, Fin.isValue]
  rw [Fin.sum_univ_eq_sum_range (fun k => q0 k * p0 k) n, Fin.sum_univ_eq_sum_range (fun k => q1 k * p1 k) n,
    Fin.sum_univ_eq_sum_range (fun k => q0 k * p1 k) n, Fin.sum_univ_eq_sum_range (fun k => q1 k * p0 k) n]
  simp

lemma addf (A ε : ℤ) (u s : ℕ → ℤ) (hu0 : u 0 = 0) (hu1 : u 1 = 1)
    (hu : ∀ m, u (m + 2) = A * u (m + 1) + ε * u m) (hs : ∀ m, s (m + 2) = A * s (m + 1) + ε * s m) :
    ∀ j k, s (j + k + 2) = u (j + 1) * s (k + 2) + ε * u j * s (k + 1)
  | 0, k => by simp [hu0, hu1]
  | 1, k => by
    have h1 : s (1 + k + 2) = A * s (k + 2) + ε * s (k + 1) := by
      rw [show 1 + k + 2 = (k + 1) + 2 by ring, hs]
    have h2 : u (1 + 1) = A * u 1 + ε * u 0 := hu 0
    rw [h1, h2, hu0, hu1]; ring
  | j + 2, k => by
    have e1 : s (j + 2 + k + 2) = A * s ((j + 1) + k + 2) + ε * s (j + k + 2) := by
      rw [show j + 2 + k + 2 = (j + k + 2) + 2 by ring, hs, show j + k + 2 + 1 = (j + 1) + k + 2 by ring]
    have i1 := addf A ε u s hu0 hu1 hu hs (j + 1) k
    have i0 := addf A ε u s hu0 hu1 hu hs j k
    have u3 : u (j + 2 + 1) = A * u (j + 2) + ε * u (j + 1) := hu (j + 1)
    have u2 : u (j + 2) = A * u (j + 1) + ε * u j := hu j
    rw [show j + 1 + 1 = j + 2 from rfl] at i1
    rw [e1, i1, i0, u3]
    linear_combination (-ε * s (k + 1)) * u2

lemma cas (A ε : ℤ) (u : ℕ → ℤ) (hu0 : u 0 = 0) (hu1 : u 1 = 1)
    (hu : ∀ m, u (m + 2) = A * u (m + 1) + ε * u m) :
    ∀ n, u (n + 1) ^ 2 - A * u (n + 1) * u n - ε * u n ^ 2 = (-ε) ^ n
  | 0 => by simp [hu0, hu1]
  | n + 1 => by
    have h := cas A ε u hu0 hu1 hu n
    rw [show n + 1 + 1 = n + 2 from rfl, hu n, pow_succ (-ε) n, ← h]; ring

lemma sform (A ε : ℤ) (u s : ℕ → ℤ) (hu0 : u 0 = 0) (hu1 : u 1 = 1)
    (hu : ∀ m, u (m + 2) = A * u (m + 1) + ε * u m) (hs : ∀ m, s (m + 2) = A * s (m + 1) + ε * s m)
    (hs0 : s 0 = 2) (hs1 : s 1 = A) : ∀ m, s m = 2 * u (m + 1) - A * u m
  | 0 => by rw [hs0, hu0, hu1]; ring
  | 1 => by rw [hs1, hu 0, hu0, hu1]; ring
  | m + 2 => by
    rw [hs, sform A ε u s hu0 hu1 hu hs hs0 hs1 (m + 1), sform A ε u s hu0 hu1 hu hs hs0 hs1 m,
      show m + 2 + 1 = (m + 1) + 2 by ring, hu (m + 1), hu m]
    ring

lemma uP_rec (A : ℤ) (m : ℕ) : uP A (m + 2) = A * uP A (m + 1) + 1 * uP A m := by rw [uP]; ring
lemma vP_rec (A : ℤ) (m : ℕ) : vP A (m + 2) = A * vP A (m + 1) + 1 * vP A m := by rw [vP]; ring
lemma uM_rec (A : ℤ) (m : ℕ) : uM A (m + 2) = A * uM A (m + 1) + (-1) * uM A m := by rw [uM]; ring
lemma vM_rec (A : ℤ) (m : ℕ) : vM A (m + 2) = A * vM A (m + 1) + (-1) * vM A m := by rw [vM]; ring

lemma casP (A : ℤ) (n : ℕ) : uP A (n + 1) ^ 2 - A * uP A (n + 1) * uP A n - uP A n ^ 2 = (-1 : ℤ) ^ n := by
  have := cas A 1 (uP A) rfl rfl (uP_rec A) n; linear_combination this
lemma casM (A : ℤ) (n : ℕ) : uM A (n + 1) ^ 2 - A * uM A (n + 1) * uM A n + uM A n ^ 2 = 1 := by
  have := cas A (-1) (uM A) rfl rfl (uM_rec A) n; simp only [neg_neg, one_pow] at this; linear_combination this
lemma casF (n : ℕ) : fb (n + 1) ^ 2 - fb (n + 1) * fb n - fb n ^ 2 = (-1 : ℤ) ^ n := by
  have := cas 1 1 fb (by simp [fb]) (by simp [fb]) fb_rec n; linear_combination this

lemma sfP (A : ℤ) (m : ℕ) : vP A m = 2 * uP A (m + 1) - A * uP A m :=
  sform A 1 (uP A) (vP A) rfl rfl (uP_rec A) (vP_rec A) rfl rfl m
lemma sfM (A : ℤ) (m : ℕ) : vM A m = 2 * uM A (m + 1) - A * uM A m :=
  sform A (-1) (uM A) (vM A) rfl rfl (uM_rec A) (vM_rec A) rfl rfl m

lemma hfP (A : ℤ) (j k : ℕ) : vP A (j + k + 2) = uP A (j + 1) * vP A (k + 2) + uP A j * vP A (k + 1) := by
  rw [addf A 1 (uP A) (vP A) rfl rfl (uP_rec A) (vP_rec A) j k]; ring
lemma hfM (A : ℤ) (j k : ℕ) : vM A (j + k + 2) = uM A (j + 1) * vM A (k + 2) + -uM A j * vM A (k + 1) := by
  rw [addf A (-1) (uM A) (vM A) rfl rfl (uM_rec A) (vM_rec A) j k]; ring
lemma hfF (j k : ℕ) : (fun m => (Nat.fib m : ℤ)) (j + k + 2) = fb (j + 1) * fb (k + 2) + fb j * fb (k + 1) := by
  show fb (j + k + 2) = _
  rw [addf 1 1 fb fb (by simp [fb]) (by simp [fb]) fb_rec fb_rec j k]; ring

lemma sig2 (n : ℕ) : ((-1 : ℤ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

lemma he (n : ℕ) : 2 * ((n % 2 : ℕ) : ℤ) = 1 - (-1 : ℤ) ^ n := by
  rcases Nat.even_or_odd n with h | h
  · rw [Nat.even_iff.mp h, h.neg_one_pow]; norm_num
  · rw [Nat.odd_iff.mp h, h.neg_one_pow]; norm_num

lemma P00 (A : ℤ) (n : ℕ) : 2 * A * ∑ k ∈ range n, vP A (k + 2) * uP A (k + 1) = 2 * A * uP A (n + 1) ^ 2 - A * (-1 : ℤ) ^ n - A + 4 * uP A n * uP A (n + 1) := by
  induction n with
  | zero =>
    norm_num [uP, uM, fb]
    try ring
  | succ n ih =>
    rw [Finset.sum_range_succ]
    try simp only [show n + 1 + 1 = n + 2 from rfl]
    push_cast
    have h2 : uP A (n + 2) = A * uP A (n + 1) + uP A n := by rw [uP_rec A]; ring
    have h3 : uP A (n + 3) = A * uP A (n + 2) + uP A (n + 1) := by rw [uP_rec A]; ring
    have hsf1 : vP A (n + 1) = 2 * uP A (n + 2) - A * uP A (n + 1) := sfP A (n + 1)
    have hsf2 : vP A (n + 2) = 2 * uP A (n + 3) - A * uP A (n + 2) := sfP A (n + 2)
    have hs1 : (-1 : ℤ) ^ (n + 1) = -(-1) ^ n := by ring
    have hC := casP A n
    have hs := sig2 n
    linear_combination ih + (2 * A * uP A (n + 1)) * hsf2 + (4 * A * uP A (n + 1)) * h3 + (-2 * A * uP A n - 2 * A * uP A (n + 2) - 4 * uP A (n + 1)) * h2 + (A) * hs1 + (2 * A) * hC

lemma P01 (A : ℤ) (n : ℕ) : 2 * A * ∑ k ∈ range n, vP A (k + 2) * uP A k = A ^ 2 * (-1 : ℤ) ^ n - A ^ 2 + 2 * uP A n ^ 2 + 2 * uP A (n + 1) ^ 2 - 2 := by
  induction n with
  | zero =>
    norm_num [uP, uM, fb]
    try ring
  | succ n ih =>
    rw [Finset.sum_range_succ]
    try simp only [show n + 1 + 1 = n + 2 from rfl]
    push_cast
    have h2 : uP A (n + 2) = A * uP A (n + 1) + uP A n := by rw [uP_rec A]; ring
    have h3 : uP A (n + 3) = A * uP A (n + 2) + uP A (n + 1) := by rw [uP_rec A]; ring
    have hsf1 : vP A (n + 1) = 2 * uP A (n + 2) - A * uP A (n + 1) := sfP A (n + 1)
    have hsf2 : vP A (n + 2) = 2 * uP A (n + 3) - A * uP A (n + 2) := sfP A (n + 2)
    have hs1 : (-1 : ℤ) ^ (n + 1) = -(-1) ^ n := by ring
    have hC := casP A n
    have hs := sig2 n
    linear_combination ih + (2 * A * uP A n) * hsf2 + (4 * A * uP A n) * h3 + (2 * A ^ 2 * uP A n - 2 * A * uP A (n + 1) - 2 * uP A n - 2 * uP A (n + 2)) * h2 + (-A ^ 2) * hs1 + (-2 * A ^ 2) * hC

lemma P10 (A : ℤ) (n : ℕ) : A * ∑ k ∈ range n, vP A (k + 1) * uP A (k + 1) = uP A n ^ 2 + uP A (n + 1) ^ 2 - 1 := by
  induction n with
  | zero =>
    norm_num [uP, uM, fb]
    try ring
  | succ n ih =>
    rw [Finset.sum_range_succ]
    try simp only [show n + 1 + 1 = n + 2 from rfl]
    push_cast
    have h2 : uP A (n + 2) = A * uP A (n + 1) + uP A n := by rw [uP_rec A]; ring
    have h3 : uP A (n + 3) = A * uP A (n + 2) + uP A (n + 1) := by rw [uP_rec A]; ring
    have hsf1 : vP A (n + 1) = 2 * uP A (n + 2) - A * uP A (n + 1) := sfP A (n + 1)
    have hsf2 : vP A (n + 2) = 2 * uP A (n + 3) - A * uP A (n + 2) := sfP A (n + 2)
    have hs1 : (-1 : ℤ) ^ (n + 1) = -(-1) ^ n := by ring
    have hC := casP A n
    have hs := sig2 n
    linear_combination ih + (A * uP A (n + 1)) * hsf1 + (A * uP A (n + 1) - uP A n - uP A (n + 2)) * h2

lemma P11 (A : ℤ) (n : ℕ) : 2 * A * ∑ k ∈ range n, vP A (k + 1) * uP A k = -2 * A * uP A n ^ 2 + A * (-1 : ℤ) ^ n - A + 4 * uP A n * uP A (n + 1) := by
  induction n with
  | zero =>
    norm_num [uP, uM, fb]
    try ring
  | succ n ih =>
    rw [Finset.sum_range_succ]
    try simp only [show n + 1 + 1 = n + 2 from rfl]
    push_cast
    have h2 : uP A (n + 2) = A * uP A (n + 1) + uP A n := by rw [uP_rec A]; ring
    have h3 : uP A (n + 3) = A * uP A (n + 2) + uP A (n + 1) := by rw [uP_rec A]; ring
    have hsf1 : vP A (n + 1) = 2 * uP A (n + 2) - A * uP A (n + 1) := sfP A (n + 1)
    have hsf2 : vP A (n + 2) = 2 * uP A (n + 3) - A * uP A (n + 2) := sfP A (n + 2)
    have hs1 : (-1 : ℤ) ^ (n + 1) = -(-1) ^ n := by ring
    have hC := casP A n
    have hs := sig2 n
    linear_combination ih + (2 * A * uP A n) * hsf1 + (4 * A * uP A n - 4 * uP A (n + 1)) * h2 + (-A) * hs1 + (-2 * A) * hC

lemma conj1 (A : ℤ) (n : ℕ) : A ^ 2 * D (vP A) n = vP A (n + 1) ^ 2 - (A ^ 2 + 4) * ((n % 2 : ℕ) : ℤ) := by
  have hd := det_formula (vP A) (fun j => uP A (j + 1)) (fun j => uP A j) (fun k => vP A (k + 2)) (fun k => vP A (k + 1)) n (hfP A)
  beta_reduce at hd
  have c00 := P00 A n
  have c01 := P01 A n
  have c10 := P10 A n
  have c11 := P11 A n
  have hv : vP A (n + 1) = 2 * uP A (n + 2) - A * uP A (n + 1) := sfP A (n + 1)
  have h2 : uP A (n + 2) = A * uP A (n + 1) + uP A n := by rw [uP_rec]; ring
  have hC := casP A n
  have hs := sig2 n
  have he := he n
  have key : 4 * (A ^ 2 * D (vP A) n - (vP A (n + 1) ^ 2 - (A ^ 2 + 4) * ((n % 2 : ℕ) : ℤ))) = 0 := by
    linear_combination (2 * A * (∑ k ∈ range n, vP A (k + 1) * uP A k) + 2 * A) * c00 + (2 * A * uP A (n + 1) ^ 2 - A * (-1 : ℤ) ^ n + A + 4 * uP A n * uP A (n + 1)) * c11 + (-2 * A * (∑ k ∈ range n, vP A (k + 1) * uP A (k + 1))) * c01 + (-2 * A ^ 2 * (-1 : ℤ) ^ n + 2 * A ^ 2 - 4 * uP A n ^ 2 - 4 * uP A (n + 1) ^ 2 + 4) * c10 + (4 * A ^ 2) * hd + (4 * A * uP A (n + 1) - 8 * uP A (n + 2) - 4 * vP A (n + 1)) * hv + (-16 * uP A n - 16 * uP A (n + 2)) * h2 + (2 * A ^ 2 + 8) * he + (4 * A * uP A n * uP A (n + 1) + 4 * uP A n ^ 2 - 4 * uP A (n + 1) ^ 2 - 4 * (-1 : ℤ) ^ n + 8) * hC + (-A ^ 2 - 4) * hs
  linarith

lemma M00 (A : ℤ) (n : ℕ) : 1 * ∑ k ∈ range n, vM A (k + 2) * uM A (k + 1) = uM A (n + 1) ^ 2 - (n : ℤ) - 1 := by
  induction n with
  | zero =>
    norm_num [uP, uM, fb]
    try ring
  | succ n ih =>
    rw [Finset.sum_range_succ]
    try simp only [show n + 1 + 1 = n + 2 from rfl]
    push_cast
    have h2 : uM A (n + 2) = A * uM A (n + 1) - uM A n := by rw [uM_rec A]; ring
    have h3 : uM A (n + 3) = A * uM A (n + 2) - uM A (n + 1) := by rw [uM_rec A]; ring
    have hsf1 : vM A (n + 1) = 2 * uM A (n + 2) - A * uM A (n + 1) := sfM A (n + 1)
    have hsf2 : vM A (n + 2) = 2 * uM A (n + 3) - A * uM A (n + 2) := sfM A (n + 2)
    have hs1 : (-1 : ℤ) ^ (n + 1) = -(-1) ^ n := by ring
    have hC := casM A n
    have hs := sig2 n
    linear_combination ih + (uM A (n + 1)) * hsf2 + (2 * uM A (n + 1)) * h3 + (uM A n - uM A (n + 2)) * h2 + (-1) * hC

lemma M01 (A : ℤ) (n : ℕ) : 1 * ∑ k ∈ range n, vM A (k + 2) * -uM A k = A * (n : ℤ) - uM A n * uM A (n + 1) := by
  induction n with
  | zero =>
    norm_num [uP, uM, fb]
    try ring
  | succ n ih =>
    rw [Finset.sum_range_succ]
    try simp only [show n + 1 + 1 = n + 2 from rfl]
    push_cast
    have h2 : uM A (n + 2) = A * uM A (n + 1) - uM A n := by rw [uM_rec A]; ring
    have h3 : uM A (n + 3) = A * uM A (n + 2) - uM A (n + 1) := by rw [uM_rec A]; ring
    have hsf1 : vM A (n + 1) = 2 * uM A (n + 2) - A * uM A (n + 1) := sfM A (n + 1)
    have hsf2 : vM A (n + 2) = 2 * uM A (n + 3) - A * uM A (n + 2) := sfM A (n + 2)
    have hs1 : (-1 : ℤ) ^ (n + 1) = -(-1) ^ n := by ring
    have hC := casM A n
    have hs := sig2 n
    linear_combination ih + (-uM A n) * hsf2 + (-2 * uM A n) * h3 + (-A * uM A n + uM A (n + 1)) * h2 + (A) * hC

lemma M10 (A : ℤ) (n : ℕ) : 1 * ∑ k ∈ range n, vM A (k + 1) * uM A (k + 1) = uM A n * uM A (n + 1) := by
  induction n with
  | zero =>
    norm_num [uP, uM, fb]
    try ring
  | succ n ih =>
    rw [Finset.sum_range_succ]
    try simp only [show n + 1 + 1 = n + 2 from rfl]
    push_cast
    have h2 : uM A (n + 2) = A * uM A (n + 1) - uM A n := by rw [uM_rec A]; ring
    have h3 : uM A (n + 3) = A * uM A (n + 2) - uM A (n + 1) := by rw [uM_rec A]; ring
    have hsf1 : vM A (n + 1) = 2 * uM A (n + 2) - A * uM A (n + 1) := sfM A (n + 1)
    have hsf2 : vM A (n + 2) = 2 * uM A (n + 3) - A * uM A (n + 2) := sfM A (n + 2)
    have hs1 : (-1 : ℤ) ^ (n + 1) = -(-1) ^ n := by ring
    have hC := casM A n
    have hs := sig2 n
    linear_combination ih + (uM A (n + 1)) * hsf1 + (uM A (n + 1)) * h2

lemma M11 (A : ℤ) (n : ℕ) : 1 * ∑ k ∈ range n, vM A (k + 1) * -uM A k = -uM A n ^ 2 + (n : ℤ) := by
  induction n with
  | zero =>
    norm_num [uP, uM, fb]
    try ring
  | succ n ih =>
    rw [Finset.sum_range_succ]
    try simp only [show n + 1 + 1 = n + 2 from rfl]
    push_cast
    have h2 : uM A (n + 2) = A * uM A (n + 1) - uM A n := by rw [uM_rec A]; ring
    have h3 : uM A (n + 3) = A * uM A (n + 2) - uM A (n + 1) := by rw [uM_rec A]; ring
    have hsf1 : vM A (n + 1) = 2 * uM A (n + 2) - A * uM A (n + 1) := sfM A (n + 1)
    have hsf2 : vM A (n + 2) = 2 * uM A (n + 3) - A * uM A (n + 2) := sfM A (n + 2)
    have hs1 : (-1 : ℤ) ^ (n + 1) = -(-1) ^ n := by ring
    have hC := casM A n
    have hs := sig2 n
    linear_combination ih + (-uM A n) * hsf1 + (-2 * uM A n) * h2 + (1) * hC

lemma conj2 (A : ℤ) (n : ℕ) : D (vM A) n = uM A (n + 1) ^ 2 - (n : ℤ) ^ 2 := by
  have hd := det_formula (vM A) (fun j => uM A (j + 1)) (fun j => -uM A j) (fun k => vM A (k + 2)) (fun k => vM A (k + 1)) n (hfM A)
  beta_reduce at hd
  have c00 := M00 A n
  have c01 := M01 A n
  have c10 := M10 A n
  have c11 := M11 A n
  have h2 : uM A (n + 2) = A * uM A (n + 1) - uM A n := by rw [uM_rec]; ring
  have hC := casM A n
  have key : D (vM A) n - (uM A (n + 1) ^ 2 - (n : ℤ) ^ 2) = 0 := by
    linear_combination ((∑ k ∈ range n, vM A (k + 1) * -uM A k) + 1) * c00 + (uM A (n + 1) ^ 2 - (n : ℤ)) * c11 + (-(∑ k ∈ range n, vM A (k + 1) * uM A (k + 1))) * c01 + (-A * (n : ℤ) + uM A n * uM A (n + 1)) * c10 + (1) * hd + ((n : ℤ)) * hC
  linarith

lemma F00 (n : ℕ) : 2 * ∑ k ∈ range n, fb (k + 2) * fb (k + 1) = 2 * fb (n + 1) ^ 2 - (-1 : ℤ) ^ n - 1 := by
  induction n with
  | zero =>
    norm_num [uP, uM, fb]
    try ring
  | succ n ih =>
    rw [Finset.sum_range_succ]
    try simp only [show n + 1 + 1 = n + 2 from rfl]
    push_cast
    have h2 : fb (n + 2) = fb n + fb (n + 1) := by rw [fb_rec]; ring
    have h3 : fb (n + 3) = fb (n + 1) + fb (n + 2) := by rw [fb_rec]; ring
    have hs1 : (-1 : ℤ) ^ (n + 1) = -(-1) ^ n := by ring
    have hC := casF n
    have hs := sig2 n
    linear_combination ih + (-2 * fb n - 2 * fb (n + 2)) * h2 + (1) * hs1 + (2) * hC

lemma F01 (n : ℕ) : 2 * ∑ k ∈ range n, fb (k + 2) * fb k = 2 * fb n * fb (n + 1) + (-1 : ℤ) ^ n - 1 := by
  induction n with
  | zero =>
    norm_num [uP, uM, fb]
    try ring
  | succ n ih =>
    rw [Finset.sum_range_succ]
    try simp only [show n + 1 + 1 = n + 2 from rfl]
    push_cast
    have h2 : fb (n + 2) = fb n + fb (n + 1) := by rw [fb_rec]; ring
    have h3 : fb (n + 3) = fb (n + 1) + fb (n + 2) := by rw [fb_rec]; ring
    have hs1 : (-1 : ℤ) ^ (n + 1) = -(-1) ^ n := by ring
    have hC := casF n
    have hs := sig2 n
    linear_combination ih + (2 * fb n - 2 * fb (n + 1)) * h2 + (-1) * hs1 + (-2) * hC

lemma F10 (n : ℕ) : 1 * ∑ k ∈ range n, fb (k + 1) * fb (k + 1) = fb n * fb (n + 1) := by
  induction n with
  | zero =>
    norm_num [uP, uM, fb]
    try ring
  | succ n ih =>
    rw [Finset.sum_range_succ]
    try simp only [show n + 1 + 1 = n + 2 from rfl]
    push_cast
    have h2 : fb (n + 2) = fb n + fb (n + 1) := by rw [fb_rec]; ring
    have h3 : fb (n + 3) = fb (n + 1) + fb (n + 2) := by rw [fb_rec]; ring
    have hs1 : (-1 : ℤ) ^ (n + 1) = -(-1) ^ n := by ring
    have hC := casF n
    have hs := sig2 n
    linear_combination ih + (-fb (n + 1)) * h2

lemma F11 (n : ℕ) : 2 * ∑ k ∈ range n, fb (k + 1) * fb k = 2 * fb n ^ 2 + (-1 : ℤ) ^ n - 1 := by
  induction n with
  | zero =>
    norm_num [uP, uM, fb]
    try ring
  | succ n ih =>
    rw [Finset.sum_range_succ]
    try simp only [show n + 1 + 1 = n + 2 from rfl]
    push_cast
    have h2 : fb (n + 2) = fb n + fb (n + 1) := by rw [fb_rec]; ring
    have h3 : fb (n + 3) = fb (n + 1) + fb (n + 2) := by rw [fb_rec]; ring
    have hs1 : (-1 : ℤ) ^ (n + 1) = -(-1) ^ n := by ring
    have hC := casF n
    have hs := sig2 n
    linear_combination ih + (-1) * hs1 + (-2) * hC

lemma conj3 (n : ℕ) : D (fun m => (Nat.fib m : ℤ)) n = fb (n + 1) ^ 2 + ((n % 2 : ℕ) : ℤ) := by
  have hd := det_formula (fun m => (Nat.fib m : ℤ)) (fun j => fb (j + 1)) (fun j => fb j) (fun k => fb (k + 2)) (fun k => fb (k + 1)) n hfF
  beta_reduce at hd
  have c00 := F00 n
  have c01 := F01 n
  have c10 := F10 n
  have c11 := F11 n
  have h2 : fb (n + 2) = fb (n + 1) + fb n := by rw [fb_rec]; ring
  have hC := casF n
  have hs := sig2 n
  have he := he n
  have key : 4 * (D (fun m => (Nat.fib m : ℤ)) n - (fb (n + 1) ^ 2 + ((n % 2 : ℕ) : ℤ))) = 0 := by
    linear_combination (2 * (∑ k ∈ range n, fb (k + 1) * fb k) + 2) * c00 + (2 * fb (n + 1) ^ 2 - (-1 : ℤ) ^ n + 1) * c11 + (-2 * (∑ k ∈ range n, fb (k + 1) * fb (k + 1))) * c01 + (-4 * fb n * fb (n + 1) - 2 * (-1 : ℤ) ^ n + 2) * c10 + (4) * hd + (-2) * he + (2 * (-1 : ℤ) ^ n - 2) * hC + (1) * hs
  linarith

end P360278

theorem OMA.solution : type_of% @OMA.S_oeis_a360278.main := by
  refine ⟨fun A n _ => P360278.conj1 A n, fun n _ => ?_, fun A n _ => P360278.conj2 A n,
    fun n _ => P360278.conj3 n⟩
  have := P360278.conj1 1 n
  linear_combination this
