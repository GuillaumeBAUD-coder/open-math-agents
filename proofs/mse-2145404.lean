import OMAStatements.S_mse_2145404
import Mathlib

namespace MSE2145404

def U (a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => a * U a b (n + 1) + b * U a b n

lemma U_zero (a b : ℕ) : U a b 0 = 0 := by rw [U]

lemma U_one (a b : ℕ) : U a b 1 = 1 := by rw [U]

lemma U_add_two (a b n : ℕ) : U a b (n + 2) = a * U a b (n + 1) + b * U a b n := by rw [U]

lemma F_eq (a b : ℕ) (F : ℕ → ℕ) (h0 : F 0 = 0)
    (hF : ∀ i, F (i + 2) = a * F (i + 1) + b * F i) (n : ℕ) :
    F n = F 1 * U a b n ∧ F (n + 1) = F 1 * U a b (n + 1) := by
  induction n with
  | zero => simp [U_zero, U_one, h0]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [hF, U_add_two, ih.1, ih.2]
    ring

lemma coprime_b (a b : ℕ) (hab : Nat.Coprime a b) (n : ℕ) : Nat.Coprime (U a b (n + 1)) b := by
  induction n with
  | zero => simp [U_one]
  | succ n ih =>
    rw [U_add_two, Nat.coprime_add_mul_left_left]
    exact Nat.Coprime.mul_left hab ih

lemma coprime_succ (a b : ℕ) (hab : Nat.Coprime a b) (n : ℕ) :
    Nat.Coprime (U a b n) (U a b (n + 1)) := by
  induction n with
  | zero => simp [U_zero, U_one]
  | succ n ih =>
    rw [U_add_two, Nat.coprime_mul_right_add_right]
    exact Nat.Coprime.mul_right (coprime_b a b hab n) ih.symm

lemma U_add (a b : ℕ) (n : ℕ) :
    ∀ m, U a b (m + n + 1) = U a b (m + 1) * U a b (n + 1) + b * U a b m * U a b n := by
  induction n with
  | zero =>
    intro m
    simp [U_zero, U_one]
  | succ n ih =>
    intro m
    have h := ih (m + 1)
    have e : m + (n + 1) + 1 = m + 1 + n + 1 := by ring
    rw [e, h, U_add_two, U_add_two]
    ring

lemma gcd_add_self (a b : ℕ) (hab : Nat.Coprime a b) (m n : ℕ) :
    Nat.gcd (U a b m) (U a b (n + m)) = Nat.gcd (U a b m) (U a b n) := by
  rcases n with _ | k
  · simp [U_zero]
  · have e : k + 1 + m = m + k + 1 := by ring
    rw [e, U_add]
    have e2 : U a b (m + 1) * U a b (k + 1) + b * U a b m * U a b k
        = U a b (m + 1) * U a b (k + 1) + U a b m * (b * U a b k) := by ring
    rw [e2, Nat.gcd_add_mul_left_right]
    exact Nat.Coprime.gcd_mul_left_cancel_right _ (coprime_succ a b hab m).symm

lemma gcd_add_mul_self (a b : ℕ) (hab : Nat.Coprime a b) (m n k : ℕ) :
    Nat.gcd (U a b m) (U a b (n + k * m)) = Nat.gcd (U a b m) (U a b n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : n + (k + 1) * m = n + k * m + m := by ring
    rw [e, gcd_add_self a b hab, ih]

lemma U_gcd (a b : ℕ) (hab : Nat.Coprime a b) (m n : ℕ) :
    U a b (Nat.gcd m n) = Nat.gcd (U a b m) (U a b n) := by
  induction m, n using Nat.gcd.induction with
  | H0 n => simp [U_zero]
  | H1 m n mpos h =>
    rw [← Nat.gcd_rec m n] at h
    conv_rhs => rw [← Nat.mod_add_div' n m]
    rwa [gcd_add_mul_self a b hab m (n % m) (n / m), Nat.gcd_comm (U a b m) _]

end MSE2145404

theorem OMA.solution : type_of% @OMA.S_mse_2145404.main := by
  intro a b _ _ hab F h0 _ hF m n
  have hm := (MSE2145404.F_eq a b F h0 hF m).1
  have hn := (MSE2145404.F_eq a b F h0 hF n).1
  have hg := (MSE2145404.F_eq a b F h0 hF (Nat.gcd m n)).1
  rw [hg, hm, hn, Nat.gcd_mul_left, MSE2145404.U_gcd a b hab, Nat.gcd_comm]
