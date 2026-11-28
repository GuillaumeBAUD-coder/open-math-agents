import OMAStatements.S_oeis_a274272
import Mathlib

namespace OMA.S_oeis_a274272

def S (N : ℕ) : ℕ := ∑ d ∈ Finset.range (N / 4 + 1), ∑ c ∈ Finset.Icc d ((N - d) / 3),
    ∑ _b ∈ Finset.Icc c ((N - c - d) / 2), 1

def T (d N : ℕ) : ℕ := ∑ c ∈ Finset.Icc d ((N - d) / 3), ((N - c - d) / 2 + 1 - c)

lemma S_eq (N : ℕ) : S N = ∑ d ∈ Finset.range (N / 4 + 1), T d N := by
  unfold S T
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro c _
  simp

def G (N : ℕ) : ℕ := T 0 N

lemma T_shift (d N : ℕ) (h : 4 * d + 4 ≤ N) : T (d + 1) N = T d (N - 4) := by
  unfold T
  have e1 : (N - (d + 1)) / 3 = (N - 4 - d) / 3 + 1 := by omega
  rw [e1, show Finset.Icc (d + 1) ((N - 4 - d) / 3 + 1) = (Finset.Icc d ((N - 4 - d) / 3)).map (addRightEmbedding 1) from (Finset.map_add_right_Icc d _ 1).symm, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro c hc
  simp only [Finset.mem_Icc] at hc
  simp only [addRightEmbedding_apply]
  omega

lemma S_rec (N : ℕ) (h : 4 ≤ N) : S N = G N + S (N - 4) := by
  rw [S_eq, S_eq, show N / 4 + 1 = (N - 4) / 4 + 1 + 1 by omega, Finset.sum_range_succ' ]
  rw [add_comm]
  unfold G
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finset.mem_range] at hd
  exact T_shift d N (by omega)

lemma S_small (N : ℕ) (h : N < 4) : S N = G N := by
  rw [S_eq]
  rw [show N / 4 + 1 = 0 + 1 by omega]
  simp [G]

lemma G_rec (N : ℕ) (h : 3 ≤ N) : G N = G (N - 3) + (N / 2 + 1) := by
  unfold G T
  have e : ∀ M : ℕ, Finset.Icc 0 M = Finset.range (M + 1) := by
    intro M; ext x; simp [Nat.lt_succ_iff]
  simp only [Nat.sub_zero]
  rw [e, e, show N / 3 + 1 = (N - 3) / 3 + 1 + 1 by omega, Finset.sum_range_succ']
  congr 1
  · apply Finset.sum_congr rfl
    intro c hc
    simp only [Finset.mem_range] at hc
    omega

lemma G_small (N : ℕ) (h : N < 3) : G N = N / 2 + 1 := by
  unfold G T
  have : N / 3 = 0 := by omega
  simp [this]

def K (r : ℕ) : ℕ := [12, 5, 8, 9, 8, 5].getD r 0
def L (r : ℕ) : ℕ := [144, 65, 76, 81, 128, 49, 108, 65, 112, 81, 92, 49].getD r 0
def Fc (N : ℕ) : ℕ := N ^ 3 + 15 * N ^ 2 + (if N % 2 = 0 then 72 else 63) * N + L (N % 12)

lemma G_closed (N : ℕ) : 12 * G N = N ^ 2 + 6 * N + K (N % 6) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases h : N < 3
    · rw [G_small N h]
      interval_cases N <;> simp [K]
    · push_neg at h
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
      rw [G_rec (M + 3) h, show M + 3 - 3 = M by omega]
      have ihM := ih M (by omega)
      have hd : (M + 3) / 2 * 2 + (M + 3) % 2 = M + 3 := by omega
      have hp : (M + 3) % 2 < 2 := Nat.mod_lt _ (by norm_num)
      rcases (by omega : M % 6 = 0 ∨ M % 6 = 1 ∨ M % 6 = 2 ∨ M % 6 = 3 ∨ M % 6 = 4 ∨ M % 6 = 5) with h0 | h0 | h0 | h0 | h0 | h0
      · have e6 : (M + 3) % 6 = 3 := by omega
        have e2 : (M + 3) % 2 = 1 := by omega
        rw [h0] at ihM; rw [e6]; rw [e2] at hd; simp [K] at ihM ⊢; nlinarith
      · have e6 : (M + 3) % 6 = 4 := by omega
        have e2 : (M + 3) % 2 = 0 := by omega
        rw [h0] at ihM; rw [e6]; rw [e2] at hd; simp [K] at ihM ⊢; nlinarith
      · have e6 : (M + 3) % 6 = 5 := by omega
        have e2 : (M + 3) % 2 = 1 := by omega
        rw [h0] at ihM; rw [e6]; rw [e2] at hd; simp [K] at ihM ⊢; nlinarith
      · have e6 : (M + 3) % 6 = 0 := by omega
        have e2 : (M + 3) % 2 = 0 := by omega
        rw [h0] at ihM; rw [e6]; rw [e2] at hd; simp [K] at ihM ⊢; nlinarith
      · have e6 : (M + 3) % 6 = 1 := by omega
        have e2 : (M + 3) % 2 = 1 := by omega
        rw [h0] at ihM; rw [e6]; rw [e2] at hd; simp [K] at ihM ⊢; nlinarith
      · have e6 : (M + 3) % 6 = 2 := by omega
        have e2 : (M + 3) % 2 = 0 := by omega
        rw [h0] at ihM; rw [e6]; rw [e2] at hd; simp [K] at ihM ⊢; nlinarith

lemma F_closed (N : ℕ) : 144 * S N = Fc N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases h : N < 4
    · rw [S_small N h]
      have hc := G_closed N
      interval_cases N <;> simp [Fc, L, K] at hc ⊢ <;> omega
    · push_neg at h
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 4 := ⟨N - 4, by omega⟩
      have ihM := ih M (by omega)
      rw [S_rec (M + 4) (by omega), show M + 4 - 4 = M by omega]
      have hG := G_closed (M + 4)
      have e : 144 * (G (M + 4) + S M) = 12 * (12 * G (M + 4)) + 144 * S M := by ring
      rw [e, hG, ihM]
      rcases (by omega : M % 12 = 0 ∨ M % 12 = 1 ∨ M % 12 = 2 ∨ M % 12 = 3 ∨ M % 12 = 4 ∨ M % 12 = 5 ∨ M % 12 = 6 ∨ M % 12 = 7 ∨ M % 12 = 8 ∨ M % 12 = 9 ∨ M % 12 = 10 ∨ M % 12 = 11) with h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0
      · have e12 : (M + 4) % 12 = 4 := by omega
        have e6 : (M + 4) % 6 = 4 := by omega
        have e2 : (M + 4) % 2 = 0 := by omega
        have e2' : M % 2 = 0 := by omega
        unfold Fc
        rw [e12, e2, e6]
        simp [Fc, L, K, h0, e2']
        nlinarith
      · have e12 : (M + 4) % 12 = 5 := by omega
        have e6 : (M + 4) % 6 = 5 := by omega
        have e2 : (M + 4) % 2 = 1 := by omega
        have e2' : M % 2 = 1 := by omega
        unfold Fc
        rw [e12, e2, e6]
        simp [Fc, L, K, h0, e2']
        nlinarith
      · have e12 : (M + 4) % 12 = 6 := by omega
        have e6 : (M + 4) % 6 = 0 := by omega
        have e2 : (M + 4) % 2 = 0 := by omega
        have e2' : M % 2 = 0 := by omega
        unfold Fc
        rw [e12, e2, e6]
        simp [Fc, L, K, h0, e2']
        nlinarith
      · have e12 : (M + 4) % 12 = 7 := by omega
        have e6 : (M + 4) % 6 = 1 := by omega
        have e2 : (M + 4) % 2 = 1 := by omega
        have e2' : M % 2 = 1 := by omega
        unfold Fc
        rw [e12, e2, e6]
        simp [Fc, L, K, h0, e2']
        nlinarith
      · have e12 : (M + 4) % 12 = 8 := by omega
        have e6 : (M + 4) % 6 = 2 := by omega
        have e2 : (M + 4) % 2 = 0 := by omega
        have e2' : M % 2 = 0 := by omega
        unfold Fc
        rw [e12, e2, e6]
        simp [Fc, L, K, h0, e2']
        nlinarith
      · have e12 : (M + 4) % 12 = 9 := by omega
        have e6 : (M + 4) % 6 = 3 := by omega
        have e2 : (M + 4) % 2 = 1 := by omega
        have e2' : M % 2 = 1 := by omega
        unfold Fc
        rw [e12, e2, e6]
        simp [Fc, L, K, h0, e2']
        nlinarith
      · have e12 : (M + 4) % 12 = 10 := by omega
        have e6 : (M + 4) % 6 = 4 := by omega
        have e2 : (M + 4) % 2 = 0 := by omega
        have e2' : M % 2 = 0 := by omega
        unfold Fc
        rw [e12, e2, e6]
        simp [Fc, L, K, h0, e2']
        nlinarith
      · have e12 : (M + 4) % 12 = 11 := by omega
        have e6 : (M + 4) % 6 = 5 := by omega
        have e2 : (M + 4) % 2 = 1 := by omega
        have e2' : M % 2 = 1 := by omega
        unfold Fc
        rw [e12, e2, e6]
        simp [Fc, L, K, h0, e2']
        nlinarith
      · have e12 : (M + 4) % 12 = 0 := by omega
        have e6 : (M + 4) % 6 = 0 := by omega
        have e2 : (M + 4) % 2 = 0 := by omega
        have e2' : M % 2 = 0 := by omega
        unfold Fc
        rw [e12, e2, e6]
        simp [Fc, L, K, h0, e2']
        nlinarith
      · have e12 : (M + 4) % 12 = 1 := by omega
        have e6 : (M + 4) % 6 = 1 := by omega
        have e2 : (M + 4) % 2 = 1 := by omega
        have e2' : M % 2 = 1 := by omega
        unfold Fc
        rw [e12, e2, e6]
        simp [Fc, L, K, h0, e2']
        nlinarith
      · have e12 : (M + 4) % 12 = 2 := by omega
        have e6 : (M + 4) % 6 = 2 := by omega
        have e2 : (M + 4) % 2 = 0 := by omega
        have e2' : M % 2 = 0 := by omega
        unfold Fc
        rw [e12, e2, e6]
        simp [Fc, L, K, h0, e2']
        nlinarith
      · have e12 : (M + 4) % 12 = 3 := by omega
        have e6 : (M + 4) % 6 = 3 := by omega
        have e2 : (M + 4) % 2 = 1 := by omega
        have e2' : M % 2 = 1 := by omega
        unfold Fc
        rw [e12, e2, e6]
        simp [Fc, L, K, h0, e2']
        nlinarith

lemma pow5_mod (n : ℕ) : 5 ^ n % 12 = if n % 2 = 0 then 1 else 5 := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; split_ifs at ih ⊢ <;> omega

lemma cf (n : ℕ) : 144 * (a n : ℤ) = 57 + 8 * (-1) ^ n + 63 * 5 ^ n + 3 * 5 ^ (1 + 2 * n) + 125 ^ n := by
  have h1 : a n = S (5 ^ n) := rfl
  have hF := F_closed (5 ^ n)
  rw [← h1] at hF
  have hodd : 5 ^ n % 2 = 1 := by
    have : Odd (5 ^ n) := Odd.pow (by decide)
    exact Nat.odd_iff.mp this
  unfold Fc at hF
  rw [if_neg (by omega)] at hF
  have hz : (144 : ℤ) * (a n : ℤ) = ((5 ^ n) ^ 3 + 15 * (5 ^ n) ^ 2 + 63 * 5 ^ n + L (5 ^ n % 12) : ℕ) := by exact_mod_cast hF
  rw [hz]
  have h125 : (125 : ℤ) ^ n = (5 ^ n) ^ 3 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h25 : (5 : ℤ) ^ (1 + 2 * n) = 5 * (5 ^ n) ^ 2 := by rw [pow_add, pow_mul']; ring
  rw [h125, h25]
  rw [pow5_mod]
  rcases Nat.even_or_odd n with he | ho
  · have : n % 2 = 0 := Nat.even_iff.mp he
    rw [if_pos this, he.neg_one_pow]
    simp [L]; ring
  · have : n % 2 = 1 := Nat.odd_iff.mp ho
    rw [if_neg (by omega), ho.neg_one_pow]
    simp [L]; ring

end OMA.S_oeis_a274272

theorem OMA.solution : type_of% @OMA.S_oeis_a274272.main := by
  refine ⟨fun n => OMA.S_oeis_a274272.cf n, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have c0 := OMA.S_oeis_a274272.cf (m + 5)
  have c1 := OMA.S_oeis_a274272.cf (m + 4)
  have c2 := OMA.S_oeis_a274272.cf (m + 3)
  have c3 := OMA.S_oeis_a274272.cf (m + 2)
  have c4 := OMA.S_oeis_a274272.cf (m + 1)
  have c5 := OMA.S_oeis_a274272.cf m
  simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega,
    show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m by omega]
  apply Int.eq_of_mul_eq_mul_left (by norm_num : (144 : ℤ) ≠ 0)
  have e : ∀ k : ℕ, (125 : ℤ) ^ k = ((5 : ℤ) ^ k) ^ 3 := by intro k; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have f : ∀ k : ℕ, (5 : ℤ) ^ (1 + 2 * k) = 5 * ((5 : ℤ) ^ k) ^ 2 := by intro k; rw [pow_add, pow_mul']; ring
  simp only [e, f, pow_succ] at c0 c1 c2 c3 c4 c5
  linear_combination c0 - 155 * c1 + 3874 * c2 - 15470 * c3 - 3875 * c4 + 15625 * c5
