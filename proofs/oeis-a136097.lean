import OMAStatements.S_oeis_a136097
import Mathlib

namespace OMA.A136097Proof

open OMA.S_oeis_a136097 Finset

variable (q : ℤ)

/-- The q-integer `[k]_q = 1 + q + ... + q^(k-1)`. -/
def qi (k : ℕ) : ℤ := ∑ t ∈ range k, q ^ t

/-- The q-factorial `[k]_q! = [1]_q [2]_q ... [k]_q`. -/
def qf : ℕ → ℤ
  | 0 => 1
  | k + 1 => qi q (k + 1) * qf k

lemma qi_add (a b : ℕ) : qi q (a + b) = qi q a + q ^ a * qi q b := by
  simp only [qi, Finset.sum_range_add, Finset.mul_sum, pow_add]

lemma qi_succ (n : ℕ) : qi q (n + 1) = 1 + q * qi q n := by
  have := qi_add q 1 n
  rw [add_comm 1 n] at this
  rw [this]; simp [qi]

lemma qi_pos (hq : 0 ≤ q) (k : ℕ) : 0 < qi q (k + 1) := by
  rw [qi_succ]
  have : 0 ≤ qi q k := Finset.sum_nonneg (fun t _ => pow_nonneg hq t)
  nlinarith

lemma qf_pos (hq : 0 ≤ q) : ∀ k, 0 < qf q k
  | 0 => by simp [qf]
  | k + 1 => by
    simp only [qf]
    exact mul_pos (qi_pos q hq k) (qf_pos hq k)

lemma qf_ne (hq : 0 ≤ q) (k : ℕ) : qf q k ≠ 0 := (qf_pos q hq k).ne'

lemma gauss_zero_right (i : ℕ) : gauss q i 0 = 1 := by
  cases i <;> simp [gauss]

lemma gauss_eq_zero : ∀ i j, i < j → gauss q i j = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => by simp [gauss]
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | i + 1, j + 1, h => by
    simp only [gauss]
    rw [gauss_eq_zero i j (by omega), gauss_eq_zero i (j + 1) (by omega)]
    simp

lemma gauss_self : ∀ i, gauss q i i = 1
  | 0 => by simp [gauss]
  | i + 1 => by
    simp only [gauss]
    rw [gauss_self i, gauss_eq_zero q i (i + 1) (by omega)]
    simp

lemma gauss_fact : ∀ i j d, j + d = i → gauss q i j * qf q j * qf q d = qf q i
  | 0, j, d, h => by
    obtain ⟨rfl, rfl⟩ : j = 0 ∧ d = 0 := by omega
    simp [gauss, qf]
  | i + 1, 0, d, h => by
    obtain rfl : d = i + 1 := by omega
    simp [gauss_zero_right, qf]
  | i + 1, j + 1, 0, h => by
    obtain rfl : j = i := by omega
    simp [gauss_self, qf]
  | i + 1, j + 1, d + 1, h => by
    have h1 := gauss_fact i j (d + 1) (by omega)
    have h2 := gauss_fact i (j + 1) d (by omega)
    have hs := qi_add q (j + 1) (d + 1)
    rw [show j + 1 + (d + 1) = i + 1 by omega] at hs
    simp only [gauss, qf] at h1 h2 ⊢
    linear_combination (qi q (j + 1)) * h1 + q ^ (j + 1) * qi q (d + 1) * h2 - qf q i * hs

lemma gauss_trinomial (hq : 0 ≤ q) (j a c : ℕ) :
    gauss q (j + a + c) (j + a) * gauss q (j + a) j = gauss q (j + a + c) j * gauss q (a + c) a := by
  apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (qf_ne q hq j) (qf_ne q hq a)) (qf_ne q hq c))
  have e1 := gauss_fact q (j + a + c) (j + a) c rfl
  have e2 := gauss_fact q (j + a) j a rfl
  have e3 := gauss_fact q (j + a + c) j (a + c) (by omega)
  have e4 := gauss_fact q (a + c) a c rfl
  linear_combination gauss q (j + a + c) (j + a) * qf q c * e2 + e1
    - gauss q (j + a + c) j * qf q j * e4 - e3

/-- `P_N(x) = Σ_m q^C(m,2) x^m [N, m]_q`. -/
def P (N : ℕ) (x : ℤ) : ℤ :=
  ∑ m ∈ range (N + 1), q ^ m.choose 2 * x ^ m * gauss q N m

lemma P_succ (N : ℕ) (x : ℤ) : P q (N + 1) x = (1 + x) * P q N (q * x) := by
  unfold P
  rw [Finset.sum_range_succ']
  have hsplit : ∀ m ∈ range (N + 1), q ^ (m + 1).choose 2 * x ^ (m + 1) * gauss q (N + 1) (m + 1)
      = x * (q ^ m.choose 2 * (q * x) ^ m * gauss q N m)
        + q ^ (m + 1).choose 2 * (q * x) ^ (m + 1) * gauss q N (m + 1) := by
    intro m _
    simp only [gauss, Nat.choose_succ_succ', Nat.choose_one_right, pow_add, mul_pow]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h2 : ∑ m ∈ range (N + 1), q ^ (m + 1).choose 2 * (q * x) ^ (m + 1) * gauss q N (m + 1)
      = ∑ m ∈ range (N + 1), q ^ m.choose 2 * (q * x) ^ m * gauss q N m - 1 := by
    have := Finset.sum_range_succ' (fun m => q ^ m.choose 2 * (q * x) ^ m * gauss q N m) (N + 1)
    rw [Finset.sum_range_succ, gauss_eq_zero q N (N + 1) (by omega)] at this
    simp only [mul_zero, add_zero, Nat.choose_zero_succ, pow_zero, gauss_zero_right, mul_one] at this
    linarith
  rw [h2]
  simp only [Nat.choose_zero_succ, pow_zero, gauss_zero_right, mul_one]
  ring

lemma alt_sum (N : ℕ) :
    ∑ a ∈ range (N + 1), (-1) ^ a * q ^ a.choose 2 * gauss q N a = if N = 0 then 1 else 0 := by
  rcases N with _ | N
  · simp [gauss]
  · have := P_succ q N (-1)
    simp only [P, add_neg_cancel, zero_mul] at this
    simp only [Nat.add_one_ne_zero, if_false]
    rw [← this]
    refine Finset.sum_congr rfl (fun a _ => by ring)

/-- The claimed inverse: `(-1)^(i-j) q^C(i-j,2) [i, j]_q`. -/
def H (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  fun i j => (-1) ^ ((i : ℕ) - j) * q ^ ((i : ℕ) - j).choose 2 * gauss q i j

lemma row_sum (hq : 0 ≤ q) (m i k : ℕ) (hi : i < m) :
    ∑ l ∈ range m, gauss q i l * ((-1) ^ (l - k) * q ^ (l - k).choose 2 * gauss q l k)
      = if i = k then 1 else 0 := by
  have hsub : ∑ l ∈ range m, gauss q i l * ((-1) ^ (l - k) * q ^ (l - k).choose 2 * gauss q l k)
      = ∑ l ∈ range (i + 1), gauss q i l * ((-1) ^ (l - k) * q ^ (l - k).choose 2 * gauss q l k) := by
    symm
    apply Finset.sum_subset (by intro x; simp; omega)
    intro x hx hx'
    simp at hx hx'
    rw [gauss_eq_zero q i x (by omega), zero_mul]
  rw [hsub]
  by_cases hki : k ≤ i
  · obtain ⟨N, rfl⟩ : ∃ N, i = k + N := ⟨i - k, by omega⟩
    rw [show k + N + 1 = k + (N + 1) by omega, Finset.sum_range_add]
    have hz : ∑ l ∈ range k, gauss q (k + N) l * ((-1) ^ (l - k) * q ^ (l - k).choose 2 * gauss q l k) = 0 :=
      Finset.sum_eq_zero (fun l hl => by
        simp at hl
        rw [gauss_eq_zero q l k hl]; ring)
    rw [hz, zero_add]
    have hterm : ∀ a ∈ range (N + 1), gauss q (k + N) (k + a) * ((-1) ^ (k + a - k) * q ^ (k + a - k).choose 2 * gauss q (k + a) k)
        = gauss q (k + N) k * ((-1) ^ a * q ^ a.choose 2 * gauss q N a) := by
      intro a ha
      simp at ha
      obtain ⟨c, hc⟩ : ∃ c, N = a + c := ⟨N - a, by omega⟩
      have := gauss_trinomial q hq k a c
      rw [show k + a - k = a by omega, hc, show k + (a + c) = k + a + c by omega]
      linear_combination ((-1) ^ a * q ^ a.choose 2) * this
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, alt_sum]
    by_cases hN : N = 0
    · subst hN; simp [gauss_self]
    · simp [hN]
  · rw [if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro l hl
    simp at hl
    rw [gauss_eq_zero q l k (by omega)]; ring

lemma mul_H (hq : 0 ≤ q) (m : ℕ) : gaussMatrix q m * H q m = 1 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [gaussMatrix, H]
  rw [Fin.sum_univ_eq_sum_range (fun l => gauss q i l * ((-1) ^ (l - k) * q ^ (l - k).choose 2 * gauss q l k)) m,
    row_sum q hq m i k i.isLt]
  simp [Fin.ext_iff]

lemma qi_dvd_central (hq : 0 ≤ q) (n : ℕ) : qi q (n + 1) ∣ gauss q (2 * n) n := by
  rcases n with _ | c
  · simp [qi]
  · have habs : qi q (c + 2) * gauss q (2 * (c + 1)) (c + 2) = qi q (c + 1) * gauss q (2 * (c + 1)) (c + 1) := by
      apply mul_right_cancel₀ (mul_ne_zero (qf_ne q hq (c + 1)) (qf_ne q hq c))
      have e1 := gauss_fact q (2 * (c + 1)) (c + 2) c (by omega)
      have e2 := gauss_fact q (2 * (c + 1)) (c + 1) (c + 1) (by omega)
      simp only [qf] at e1 e2 ⊢
      linear_combination e1 - e2
    refine ⟨gauss q (2 * (c + 1)) (c + 1) - q * gauss q (2 * (c + 1)) (c + 2), ?_⟩
    have hs := qi_succ q (c + 1)
    linear_combination q * habs - gauss q (2 * (c + 1)) (c + 1) * hs

lemma ediv_eq_qi (hq : 1 < q) (n : ℕ) : (q ^ (n + 1) - 1) / (q - 1) = qi q (n + 1) := by
  have h := geom_sum_mul q (n + 1)
  rw [← h]
  exact Int.mul_ediv_cancel _ (by omega)

theorem main_proof :
    ∀ q : ℤ, 1 < q → ∀ n : ℕ,
      (q ^ (n + 1) - 1) / (q - 1) * q ^ (n * (n - 1) / 2) ∣
        (gaussMatrix q (2 * n + 1))⁻¹ ⟨2 * n, by omega⟩ ⟨n, by omega⟩ := by
  intro q hq n
  rw [Matrix.inv_eq_right_inv (mul_H q (by omega) (2 * n + 1)), ediv_eq_qi q hq n,
    ← Nat.choose_two_right]
  simp only [H]
  rw [show 2 * n - n = n by omega]
  obtain ⟨c, hc⟩ := qi_dvd_central q (by omega) n
  exact ⟨(-1) ^ n * c, by rw [hc]; ring⟩

end OMA.A136097Proof

open OMA.A136097Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a136097.main := main_proof
