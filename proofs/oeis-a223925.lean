import OMAStatements.S_oeis_a223925
import Mathlib

namespace A223925Aux
open OMA.S_oeis_a223925 Finset

lemma ent_succ_zero (n : ℕ) : entringer (n + 1) 0 = 0 := by
  simp [entringer]

lemma ent_succ_succ (n k : ℕ) :
    entringer (n + 1) (k + 1) = entringer (n + 1) k + entringer n (n - k) := by
  simp [entringer]

def Z (m : ℕ) : ℤ := (eulerZigzag m : ℤ)

def s1 (j : ℕ) : ℤ := if j % 2 = 1 then (-1) ^ (j / 2) else 0
def s0 (i : ℕ) : ℤ := if i % 2 = 0 then (-1) ^ (i / 2) else 0

lemma s1_zero : s1 0 = 0 := by simp [s1]
lemma s1_succ (j : ℕ) : s1 (j + 1) = s0 j := by
  unfold s1 s0
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · have h1 : (j + 1) % 2 = 1 := by omega
    have h2 : (j + 1) / 2 = j / 2 := by omega
    rw [if_pos h1, if_pos h, h2]
  · have h1 : ¬ (j + 1) % 2 = 1 := by omega
    have h2 : ¬ j % 2 = 0 := by omega
    rw [if_neg h1, if_neg h2]
lemma s0_succ (j : ℕ) : s0 (j + 1) = - s1 j := by
  unfold s1 s0
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · have h1 : ¬ (j + 1) % 2 = 0 := by omega
    have h2 : ¬ j % 2 = 1 := by omega
    rw [if_neg h1, if_neg h2]; simp
  · have h1 : (j + 1) % 2 = 0 := by omega
    have h2 : (j + 1) / 2 = j / 2 + 1 := by omega
    rw [if_pos h1, if_pos h, h2, pow_succ]; ring

def Fs (n k : ℕ) : ℤ := ∑ j ∈ range (k + 1), s1 j * (k.choose j : ℤ) * Z (n - j)
def Gs (m r : ℕ) : ℤ := ∑ i ∈ range (r + 1), s0 i * (r.choose i : ℤ) * Z (m - i)

lemma stepF (n k : ℕ) : Fs n (k + 1) = Fs n k + Gs (n - 1) k := by
  unfold Fs Gs
  rw [sum_range_succ' _ (k + 1)]
  have e1 : ∑ j ∈ range (k + 1), s1 j * (k.choose j : ℤ) * Z (n - j)
      = ∑ j ∈ range (k + 1), s1 (j + 1) * (k.choose (j + 1) : ℤ) * Z (n - (j + 1)) := by
    rw [sum_range_succ' _ k, sum_range_succ _ k]
    simp [s1_zero, Nat.choose_succ_self]
  rw [e1, s1_zero, zero_mul, zero_mul, add_zero, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rw [Nat.choose_succ_succ', s1_succ, show n - (j + 1) = n - 1 - j by omega]
  push_cast; ring

lemma stepG (m r : ℕ) : Gs m (r + 1) = Gs m r - Fs (m - 1) r := by
  unfold Fs Gs
  rw [sum_range_succ' _ (r + 1)]
  have e1 : ∑ i ∈ range (r + 1), s0 i * (r.choose i : ℤ) * Z (m - i)
      = ∑ i ∈ range (r + 1), s0 (i + 1) * (r.choose (i + 1) : ℤ) * Z (m - (i + 1))
        + s0 0 * Z m := by
    rw [sum_range_succ' _ r, sum_range_succ _ r]
    simp [Nat.choose_succ_self]
  rw [e1]
  have key : ∑ k ∈ range (r + 1), s0 (k + 1) * ((r + 1).choose (k + 1) : ℤ) * Z (m - (k + 1))
      = ∑ i ∈ range (r + 1), s0 (i + 1) * (r.choose (i + 1) : ℤ) * Z (m - (i + 1))
        - ∑ i ∈ range (r + 1), s1 i * (r.choose i : ℤ) * Z (m - 1 - i) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    rw [Nat.choose_succ_succ', s0_succ, show m - (j + 1) = m - 1 - j by omega]
    push_cast; ring
  simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero] at key ⊢
  rw [key]; ring

lemma main_ind (n : ℕ) :
    (∀ k, k < n → (entringer n k : ℤ) = Fs n k) ∧
    (∀ r, r < n → (entringer n (n - r) : ℤ) = Gs n r) := by
  induction n with
  | zero => exact ⟨fun k hk => absurd hk (Nat.not_lt_zero _), fun r hr => absurd hr (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨ihA, ihB⟩ := ih
    constructor
    · intro k
      induction k with
      | zero => intro _; simp [ent_succ_zero, Fs, s1_zero]
      | succ k ihk =>
        intro hk
        rw [ent_succ_succ, Nat.cast_add, ihk (by omega), ihB k (by omega), stepF]
        simp
    · intro r
      induction r with
      | zero => intro _; simp [Gs, s0, Z, eulerZigzag]
      | succ r ihr =>
        intro hr
        have hrec := ent_succ_succ n (n - r)
        rw [show n - r + 1 = n + 1 - r by omega, show n - (n - r) = r by omega] at hrec
        rw [show n + 1 - (r + 1) = n - r by omega, stepG, Nat.add_sub_cancel,
          ← ihr (by omega), ← ihA r (by omega), hrec]
        push_cast; ring

lemma ent_one_right (m : ℕ) (hm : 1 ≤ m) : (entringer m 1 : ℤ) = Z (m - 1) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [ent_succ_succ, ent_succ_zero]
  simp [Z, eulerZigzag]

lemma G_pred (m : ℕ) (hm : 1 ≤ m) : Gs m (m - 1) = Z (m - 1) := by
  have := (main_ind m).2 (m - 1) (by omega)
  rw [show m - (m - 1) = 1 by omega, ent_one_right m hm] at this
  exact this.symm

lemma h_eq (m : ℕ) (hm : 1 ≤ m) : Gs m m = Z (m - 1) - Fs (m - 1) (m - 1) := by
  have := stepG m (m - 1)
  rw [show m - 1 + 1 = m by omega, G_pred m hm] at this
  exact this

lemma F_diag (m : ℕ) (hm : 2 ≤ m) : Fs m m = Z m + Gs (m - 1) (m - 1) := by
  have h1 := stepF m (m - 1)
  rw [show m - 1 + 1 = m by omega] at h1
  have h2 := (main_ind m).1 (m - 1) (by omega)
  have h3 : (entringer m m : ℤ) = entringer m (m - 1) := by
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 + 1 := ⟨m - 2, by omega⟩
    rw [show n + 1 + 1 - 1 = n + 1 by omega, ent_succ_succ (n + 1) (n + 1),
      show n + 1 - (n + 1) = 0 by omega, ent_succ_zero]
    simp
  have h4 : Z m = entringer m m := by simp [Z, eulerZigzag]
  rw [h1, ← h2, h4, h3]

lemma h_step (m : ℕ) (hm : 3 ≤ m) : Gs m m = - Gs (m - 2) (m - 2) := by
  rw [h_eq m (by omega), F_diag (m - 1) (by omega), show m - 1 - 1 = m - 2 by omega]
  ring

lemma h_one : Gs 1 1 = 1 := by
  simp [Gs, sum_range_succ, s0, Z, eulerZigzag, entringer]

lemma h_odd (p : ℕ) : Gs (2 * p + 1) (2 * p + 1) = (-1) ^ p := by
  induction p with
  | zero => simpa using h_one
  | succ p ih =>
    rw [h_step _ (by omega), show 2 * (p + 1) + 1 - 2 = 2 * p + 1 by omega, ih, pow_succ]
    ring

lemma Z_even (p : ℕ) (hp : 1 ≤ p) : Z (2 * p) = Fs (2 * p) (2 * p) - (-1) ^ (p - 1) := by
  rw [F_diag (2 * p) (by omega), show 2 * p - 1 = 2 * (p - 1) + 1 by omega, h_odd]
  ring

open PowerSeries

noncomputable def cs : ℚ⟦X⟧ := PowerSeries.mk fun n => (s0 n : ℚ) / (n.factorial : ℚ)
noncomputable def sn : ℚ⟦X⟧ := PowerSeries.mk fun n => (s1 n : ℚ) / (n.factorial : ℚ)
noncomputable def tau : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => if n % 2 = 1 then (Z n : ℚ) / (n.factorial : ℚ) else 0

lemma fact_succ_q (n : ℕ) : ((n + 1).factorial : ℚ) = (n + 1) * (n.factorial : ℚ) := by
  rw [Nat.factorial_succ]; push_cast; ring

lemma d_cs : d⁄dX ℚ cs = - sn := by
  ext n
  rw [coeff_derivative, cs, sn, coeff_mk, map_neg, coeff_mk, s0_succ, fact_succ_q]
  have : (n.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

lemma d_sn : d⁄dX ℚ sn = cs := by
  ext n
  rw [coeff_derivative, cs, sn, coeff_mk, coeff_mk, s1_succ, fact_succ_q]
  have : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp

lemma pyth : cs ^ 2 + sn ^ 2 = 1 := by
  have hd : d⁄dX ℚ (cs ^ 2 + sn ^ 2) = 0 := by
    rw [map_add, pow_two, pow_two, Derivation.leibniz, Derivation.leibniz, d_cs, d_sn]
    simp only [smul_eq_mul]; ring
  ext n
  rcases n with _ | n
  · simp [cs, sn, pow_two, coeff_mul, s0, s1]
  · have := congrArg (coeff n) hd
    rw [coeff_derivative, map_zero] at this
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    rw [coeff_one, if_neg (by omega)]
    exact (mul_eq_zero.mp this).resolve_right hn

lemma s0_odd (i : ℕ) (h : i % 2 = 1) : s0 i = 0 := by simp [s0, h]
lemma s1_even (i : ℕ) (h : i % 2 = 0) : s1 i = 0 := by simp [s1, h]

lemma cs_tau : cs * tau = sn := by
  ext n
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [cs, tau, sn, coeff_mk]
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · rw [s1_even n hn]
    simp only [Int.cast_zero, zero_div]
    apply sum_eq_zero
    intro i hi
    rw [mem_range] at hi
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · rw [if_neg (by omega), mul_zero]
    · rw [s0_odd i h]; simp
  · obtain ⟨p, rfl⟩ : ∃ p, n = 2 * p + 1 := ⟨n / 2, by omega⟩
    have hG := h_odd p
    have hs1 : s1 (2 * p + 1) = (-1) ^ p := by
      simp [s1, show (2 * p + 1) / 2 = p by omega]
    rw [hs1]
    have hfac : ((2 * p + 1).factorial : ℚ) ≠ 0 := by positivity
    have key : ∀ i ∈ range (2 * p + 1 + 1),
        (s0 i : ℚ) / (i.factorial : ℚ) *
          (if (2 * p + 1 - i) % 2 = 1 then (Z (2 * p + 1 - i) : ℚ) /
            ((2 * p + 1 - i).factorial : ℚ) else 0)
        = ((s0 i * ((2 * p + 1).choose i : ℤ) * Z (2 * p + 1 - i) : ℤ) : ℚ) /
            ((2 * p + 1).factorial : ℚ) := by
      intro i hi
      rw [mem_range] at hi
      rcases Nat.mod_two_eq_zero_or_one i with h | h
      · rw [if_pos (by omega)]
        push_cast
        rw [Nat.cast_choose ℚ (by omega : i ≤ 2 * p + 1)]
        have h1 : (i.factorial : ℚ) ≠ 0 := by positivity
        have h2 : ((2 * p + 1 - i).factorial : ℚ) ≠ 0 := by positivity
        field_simp
      · rw [s0_odd i h]; simp
    rw [sum_congr rfl key, ← sum_div]
    have : ∑ i ∈ range (2 * p + 1 + 1),
        ((s0 i * ((2 * p + 1).choose i : ℤ) * Z (2 * p + 1 - i) : ℤ) : ℚ)
        = ((Gs (2 * p + 1) (2 * p + 1) : ℤ) : ℚ) := by
      rw [Gs]; push_cast; rfl
    rw [this, hG]

lemma tau_ode : d⁄dX ℚ tau = 1 + tau ^ 2 := by
  have h1 := congrArg (d⁄dX ℚ) cs_tau
  rw [Derivation.leibniz, d_cs, d_sn] at h1
  simp only [smul_eq_mul] at h1
  -- h1 : cs * d tau + tau * (-sn) = cs
  have hc : cs ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro h
    have := congrArg (coeff 0) h
    simp [cs, s0] at this
  apply mul_left_cancel₀ hc
  have e1 : cs ^ 2 * d⁄dX ℚ tau = 1 := by
    linear_combination cs * h1 + sn * cs_tau + pyth
  linear_combination e1 - pyth - (cs * tau + sn) * cs_tau

lemma tan_rec (n : ℕ) (hn : 1 ≤ n) :
    Z (2 * n + 1) = ∑ i ∈ range (2 * n + 1),
      (if i % 2 = 1 then ((2 * n).choose i : ℤ) * Z i * Z (2 * n - i) else 0) := by
  have h := congrArg (coeff (2 * n)) tau_ode
  rw [coeff_derivative, map_add, coeff_one, if_neg (by omega), zero_add, pow_two, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [tau, coeff_mk] at h
  rw [if_pos (by omega)] at h
  have hf : ((2 * n).factorial : ℚ) ≠ 0 := by positivity
  have key : ∀ i ∈ range (2 * n + 1),
      (if i % 2 = 1 then (Z i : ℚ) / (i.factorial : ℚ) else 0) *
        (if (2 * n - i) % 2 = 1 then (Z (2 * n - i) : ℚ) / ((2 * n - i).factorial : ℚ) else 0)
      = (((if i % 2 = 1 then ((2 * n).choose i : ℤ) * Z i * Z (2 * n - i) else 0 : ℤ)) : ℚ)
          / ((2 * n).factorial : ℚ) := by
    intro i hi
    rw [mem_range] at hi
    rcases Nat.mod_two_eq_zero_or_one i with hi2 | hi2
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
    · rw [if_pos hi2, if_pos (by omega), if_pos hi2]
      push_cast
      rw [Nat.cast_choose ℚ (by omega : i ≤ 2 * n)]
      have h1 : (i.factorial : ℚ) ≠ 0 := by positivity
      have h2 : ((2 * n - i).factorial : ℚ) ≠ 0 := by positivity
      field_simp
  rw [sum_congr rfl key, ← sum_div, fact_succ_q] at h
  have h3 : ((2 * n : ℕ) : ℚ) + 1 ≠ 0 := by positivity
  push_cast at h
  have h4 : (Z (2 * n + 1) : ℚ) = ((∑ i ∈ range (2 * n + 1),
      (if i % 2 = 1 then ((2 * n).choose i : ℤ) * Z i * Z (2 * n - i) else 0) : ℤ) : ℚ) := by
    push_cast
    field_simp at h
    linear_combination h
  exact_mod_cast h4

lemma split_sum (g : ℕ → ℤ) (N : ℕ) :
    ∑ i ∈ range (2 * N + 1), g i = ∑ k ∈ range N, g (2 * k + 1) + ∑ k ∈ range (N + 1), g (2 * k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ (fun k => g (2 * k + 1)), sum_range_succ (fun k => g (2 * k)) (N + 1)]
    rw [show 2 * N + 1 + 1 = 2 * (N + 1) by ring]
    ring

lemma rec2 (n : ℕ) (hn : 1 ≤ n) :
    Z (2 * n + 1) = ∑ k ∈ range n,
      ((2 * n).choose (2 * k + 1) : ℤ) * Z (2 * k + 1) * Z (2 * (n - 1 - k) + 1) := by
  rw [tan_rec n hn, split_sum]
  have h0 : ∑ k ∈ range (n + 1), (if 2 * k % 2 = 1 then ((2 * n).choose (2 * k) : ℤ) * Z (2 * k)
      * Z (2 * n - 2 * k) else 0) = 0 := by
    apply sum_eq_zero; intro k _; rw [if_neg (by omega)]
  rw [h0, add_zero]
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  rw [if_pos (by omega), show 2 * n - (2 * k + 1) = 2 * (n - 1 - k) + 1 by omega]

lemma comb_id (n k : ℕ) (hk : k < n) :
    ((2 * n + 1 : ℕ) : ℤ) * ((n + 1 : ℕ) : ℤ) * ((2 * n).choose (2 * k + 1) : ℤ)
      = 2 * ((k + 1 : ℕ) : ℤ) * ((n - k : ℕ) : ℤ) *
        (((2 * n + 1).choose (2 * k + 1) : ℤ) + ((2 * n + 1).choose (2 * k + 2) : ℤ)) := by
  have e1 := Nat.choose_mul_succ_eq (2 * n) (2 * k + 1)
  have e2 := Nat.add_one_mul_choose_eq (2 * n + 1) (2 * k + 1)
  have e3 := Nat.choose_succ_succ (2 * n + 1) (2 * k + 1)
  rw [show 2 * n + 1 - (2 * k + 1) = 2 * (n - k) by omega] at e1
  have e1' : ((2 * n).choose (2 * k + 1) : ℤ) * ((2 * n + 1 : ℕ) : ℤ)
      = ((2 * n + 1).choose (2 * k + 1) : ℤ) * (2 * ((n - k : ℕ) : ℤ)) := by exact_mod_cast e1
  have e2' : (((2 * n + 1 + 1) : ℕ) : ℤ) * ((2 * n + 1).choose (2 * k + 1) : ℤ)
      = (((2 * n + 1 + 1)).choose (2 * k + 1 + 1) : ℤ) * (((2 * k + 1 + 1) : ℕ) : ℤ) := by
    exact_mod_cast e2
  have e3' : (((2 * n + 1 + 1)).choose (2 * k + 1 + 1) : ℤ)
      = ((2 * n + 1).choose (2 * k + 1) : ℤ) + ((2 * n + 1).choose (2 * k + 1 + 1) : ℤ) := by
    exact_mod_cast e3
  rw [e3'] at e2'
  push_cast at e1' e2' ⊢
  rw [show (2 * k + 1 + 1 : ℕ) = 2 * k + 2 by ring] at e2'
  linear_combination (((n : ℤ) + 1)) * e1' + ((n - k : ℕ) : ℤ) * e2'

def y (k : ℕ) : ℤ := ((k + 1 : ℕ) : ℤ) * Z (2 * k + 1)

lemma big_id (n : ℕ) (hn : 1 ≤ n) :
    ((2 * n + 1 : ℕ) : ℤ) * y n = 4 * ∑ k ∈ range n,
      ((2 * n + 1).choose (2 * k + 2) : ℤ) * y k * y (n - 1 - k) := by
  have hA : ∑ k ∈ range n, ((2 * n + 1).choose (2 * k + 1) : ℤ) * y k * y (n - 1 - k)
      = ∑ k ∈ range n, ((2 * n + 1).choose (2 * k + 2) : ℤ) * y k * y (n - 1 - k) := by
    rw [← sum_range_reflect]
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    rw [show n - 1 - (n - 1 - k) = k by omega,
      show 2 * (n - 1 - k) + 1 = 2 * n + 1 - (2 * k + 2) by omega, Nat.choose_symm (by omega)]
    ring
  have hB : ((2 * n + 1 : ℕ) : ℤ) * y n = ∑ k ∈ range n,
      2 * (((2 * n + 1).choose (2 * k + 1) : ℤ) + ((2 * n + 1).choose (2 * k + 2) : ℤ))
        * y k * y (n - 1 - k) := by
    have hy : y n = ((n + 1 : ℕ) : ℤ) * Z (2 * n + 1) := rfl
    rw [hy, rec2 n hn, mul_sum, mul_sum]
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    have := comb_id n k hk
    simp only [y]
    rw [show n - 1 - k + 1 = n - k by omega]
    linear_combination (Z (2 * k + 1) * Z (2 * (n - 1 - k) + 1)) * this
  have hC : ∑ k ∈ range n,
      2 * (((2 * n + 1).choose (2 * k + 1) : ℤ) + ((2 * n + 1).choose (2 * k + 2) : ℤ))
        * y k * y (n - 1 - k)
      = 2 * ∑ k ∈ range n, ((2 * n + 1).choose (2 * k + 1) : ℤ) * y k * y (n - 1 - k)
        + 2 * ∑ k ∈ range n, ((2 * n + 1).choose (2 * k + 2) : ℤ) * y k * y (n - 1 - k) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    ring
  rw [hB, hC, hA]
  ring

lemma cop_odd (n : ℕ) : IsCoprime ((4 : ℤ) ^ n) ((2 * n + 1 : ℕ) : ℤ) := by
  rw [show (4 : ℤ) ^ n = ((4 ^ n : ℕ) : ℤ) by push_cast; rfl, Nat.isCoprime_iff_coprime]
  have h : Nat.Coprime (2 ^ 2) (2 * n + 1) := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr ⟨n, rfl⟩)
  norm_num at h
  exact Nat.Coprime.pow_left n h

lemma Q (m : ℕ) : (4 : ℤ) ^ m ∣ y m := by
  induction m using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0; simp
    · have hd : (4 : ℤ) ^ n ∣ ((2 * n + 1 : ℕ) : ℤ) * y n := by
        rw [big_id n hn, show n = (n - 1) + 1 by omega, pow_succ, mul_comm _ (4 : ℤ)]
        rw [show n - 1 + 1 = n by omega]
        apply mul_dvd_mul_left
        apply dvd_sum
        intro k hk
        rw [mem_range] at hk
        rw [show n - 1 = k + (n - 1 - k) by omega, pow_add, mul_assoc]
        rw [show k + (n - 1 - k) = n - 1 by omega]
        exact Dvd.dvd.mul_left (mul_dvd_mul (ih k (by omega)) (ih (n - 1 - k) (by omega))) _
      exact (cop_odd n).dvd_of_dvd_mul_left hd

lemma four_pow_big (k : ℕ) (hk : 1 ≤ k) : k + 2 ≤ 4 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k _ ih => rw [pow_succ]; omega

lemma T_even (k : ℕ) (hk : 1 ≤ k) : (2 : ℤ) ∣ Z (2 * k + 1) := by
  by_contra h
  have hc : IsCoprime (2 : ℤ) (Z (2 * k + 1)) := (Int.prime_two.coprime_iff_not_dvd).mpr h
  have hc2 : IsCoprime ((4 : ℤ) ^ k) (Z (2 * k + 1)) := by
    rw [show (4 : ℤ) ^ k = 2 ^ (2 * k) by rw [pow_mul]; norm_num]
    exact hc.pow_left
  have hq := Q k
  rw [y] at hq
  have h3 := hc2.dvd_of_dvd_mul_right hq
  have h4 : (4 : ℤ) ^ k ≤ ((k + 1 : ℕ) : ℤ) := Int.le_of_dvd (by positivity) h3
  have h5 := four_pow_big k hk
  have h6 : ((k + 2 : ℕ) : ℤ) ≤ ((4 ^ k : ℕ) : ℤ) := by exact_mod_cast h5
  push_cast at h4 h6
  omega

lemma Fs_even (p : ℕ) (hp : 1 ≤ p) : (2 : ℤ) ∣ Fs (2 * p) (2 * p) := by
  unfold Fs
  apply dvd_sum
  intro j hj
  rw [mem_range] at hj
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [s1_even j h]; simp
  · by_cases hj2 : j = 2 * p - 1
    · subst hj2
      rw [Nat.choose_symm (by omega), Nat.choose_one_right]
      apply Dvd.dvd.mul_right
      apply Dvd.dvd.mul_left
      push_cast
      exact ⟨p, by ring⟩
    · apply Dvd.dvd.mul_left
      rw [show 2 * p - j = 2 * ((2 * p - j - 1) / 2) + 1 by omega]
      exact T_even _ (by omega)

lemma Zeven_odd (p : ℕ) (hp : 1 ≤ p) : ¬ (2 : ℤ) ∣ Z (2 * p) := by
  rw [Z_even p hp]
  intro h
  have h1 := Fs_even p hp
  have h2 : (2 : ℤ) ∣ (-1) ^ (p - 1) := by
    have := dvd_sub h1 h
    simpa using this
  rcases neg_one_pow_eq_or ℤ (p - 1) with h3 | h3 <;> rw [h3] at h2 <;> norm_num at h2

end A223925Aux

open A223925Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a223925.main := by
  intro n hn
  simp only [OMA.S_oeis_a223925.a132049]
  set N := OMA.S_oeis_a223925.eulerZigzag
  have hq := Q (n - 1)
  rw [y, show n - 1 + 1 = n by omega, show 2 * (n - 1) + 1 = 2 * n - 1 by omega] at hq
  have hq' : 4 ^ (n - 1) ∣ n * N (2 * n - 1) := by
    have : ((4 ^ (n - 1) : ℕ) : ℤ) ∣ ((n * N (2 * n - 1) : ℕ) : ℤ) := by
      push_cast; exact hq
    exact_mod_cast this
  have hnum : 4 ^ n ∣ 2 * (2 * n) * N (2 * n - 1) := by
    rw [show 2 * (2 * n) * N (2 * n - 1) = 4 * (n * N (2 * n - 1)) by ring,
      show n = n - 1 + 1 by omega, pow_succ, mul_comm _ 4]
    rw [show n - 1 + 1 = n by omega]
    exact mul_dvd_mul_left 4 hq'
  have hden : ¬ 2 ∣ N (2 * n) := by
    intro h
    apply Zeven_odd n hn
    have : ((2 : ℕ) : ℤ) ∣ ((N (2 * n) : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h
    show (2 : ℤ) ∣ ((N (2 * n) : ℕ) : ℤ)
    exact this
  have hg : Nat.Coprime (4 ^ n) (Nat.gcd (2 * (2 * n) * N (2 * n - 1)) (N (2 * n))) := by
    have h2 : Nat.Coprime 2 (Nat.gcd (2 * (2 * n) * N (2 * n - 1)) (N (2 * n))) := by
      rw [Nat.coprime_two_left, Nat.odd_iff]
      have := Nat.gcd_dvd_right (2 * (2 * n) * N (2 * n - 1)) (N (2 * n))
      by_contra hc
      apply hden
      exact dvd_trans (Nat.dvd_of_mod_eq_zero (by omega)) this
    rw [show 4 ^ n = 2 ^ (2 * n) by rw [pow_mul]; norm_num]
    exact Nat.Coprime.pow_left _ h2
  apply hg.dvd_of_dvd_mul_left
  rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)]
  exact hnum
