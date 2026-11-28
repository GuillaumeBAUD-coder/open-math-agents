import OMAStatements.S_oeis_a002063
import Mathlib

/-!
# Verification of the A002063 characterization: `x ^ 2 = 2 ^ i + 2 ^ j` iff `x ^ 2 = 9 * 4 ^ n`

The solutions of `x ^ 2 = 2 ^ i + 2 ^ j` with `i < j` are exactly `x = 3 * 2 ^ n`
(with `i = 2 * n`, `j = 2 * n + 3`), giving `x ^ 2 = 9 * 4 ^ n`.

Key steps:
* Core lemma: `y ^ 2 = 1 + 2 ^ m` with `m ≥ 1` forces `y = 3`, `m = 3`.
  Indeed `y` is odd and `(y - 1) * (y + 1) = 2 ^ m`; writing `y - 1 = 2 * c` gives
  `c * (y + 1) = 2 ^ (m - 1)` and `c * (c + 1) = 2 ^ (m - 2)`, so `c` and `c + 1`
  are both powers of two. A power of two and its successor are `1` and `2`, so
  `c = 1`, `y = 3`, and `2 = 2 ^ (m - 2)` gives `m = 3`.
* Descent: from `x ^ 2 = 2 ^ i + 2 ^ j` with `i ≥ 2` we get `x = 2 * x₁` and
  `x₁ ^ 2 = 2 ^ (i - 2) + 2 ^ (j - 2)` (both terms divisible by 4); `i = 1` is
  impossible by parity.
-/

namespace OMA.A002063Aux

/-- Core lemma: `y ^ 2 = 1 + 2 ^ m` with `m ≥ 1` forces `y = 3` and `m = 3`. -/
lemma sq_eq_one_add_two_pow {y m : ℕ} (hm : 1 ≤ m) (h : y ^ 2 = 1 + 2 ^ m) :
    y = 3 ∧ m = 3 := by
  -- `m ≥ 2`: the case `m = 1` would give `y ^ 2 = 3`, impossible
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with h1 | h1
    · have hme : m = 1 := by omega
      subst hme
      rw [Nat.pow_one] at h
      rcases Nat.lt_or_ge y 2 with hy | hy
      · have hyy : y * y ≤ 1 * 1 := Nat.mul_le_mul (Nat.le_of_lt_succ hy) (Nat.le_of_lt_succ hy)
        rw [Nat.pow_two] at h
        omega
      · have hyy : 2 * 2 ≤ y * y := Nat.mul_le_mul hy hy
        rw [Nat.pow_two] at h
        omega
    · exact h1
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  -- `2 ^ (k+1) = 2 * 2 ^ k`
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
  -- `y` is odd
  obtain ⟨c, hc⟩ : ∃ c, y = 2 * c + 1 := by
    rcases Nat.even_or_odd y with he | ho
    · obtain ⟨e, rfl⟩ := he
      exfalso
      -- (e+e)² = 4*e² is even, but 1 + 2*2^k is odd
      have h4 : (e + e) ^ 2 = 1 + 2 * 2 ^ k := by rw [h, hpow]
      have h5 : (e + e) ^ 2 = 4 * e ^ 2 := by ring
      rw [h5] at h4
      omega
    · obtain ⟨c, rfl⟩ := ho
      exact ⟨c, rfl⟩
  have hy3 : 3 ≤ y := by
    rcases Nat.lt_or_ge y 3 with h3 | h3
    · exfalso
      have hyy : y * y ≤ 2 * 2 := Nat.mul_le_mul (by omega) (by omega)
      have h5 : 4 ≤ 2 ^ (k + 1) := by
        have hle := Nat.pow_le_pow_right (n := 2) (by norm_num : 1 ≤ 2) hm2
        norm_num at hle
        omega
      rw [Nat.pow_two] at h
      omega
    · exact h3
  -- `(y - 1) * (y + 1) + 1 = y * y`
  have hkey : (y - 1) * (y + 1) + 1 = y * y := by
    have e1 : y * y = (y - 1) * y + y := by
      have hy1 : y = (y - 1) + 1 := by omega
      rw [hy1, Nat.add_mul]
      norm_num
    rw [Nat.mul_add, Nat.mul_one]  -- (y-1)*(y+1) + 1 = (y-1)*y + (y-1) + 1
    omega
  have hyy2 : y * y = 1 + 2 ^ (k + 1) := by rw [← Nat.pow_two]; exact h
  have hprod : (y - 1) * (y + 1) = 2 ^ (k + 1) := by linarith [hkey, hyy2]
  -- `y - 1 = 2 * c`, so `c * (y + 1) = 2 ^ k`
  have hy1e : y - 1 = 2 * c := by omega
  have hc1 : c * (y + 1) = 2 ^ k := by
    have e1 : 2 * (c * (y + 1)) = 2 ^ (k + 1) := by
      calc 2 * (c * (y + 1)) = (2 * c) * (y + 1) := by ring
        _ = (y - 1) * (y + 1) := by rw [hy1e]
        _ = 2 ^ (k + 1) := hprod
    have e2 : 2 * (c * (y + 1)) = 2 * 2 ^ k := by rw [e1, hpow]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) e2
  -- `y + 1 = 2 * (c + 1)`, so `c * (c + 1) = 2 ^ (k - 1)`
  have hy2 : y + 1 = 2 * (c + 1) := by omega
  have hk1 : 1 ≤ k := by omega
  have hcc1 : c * (c + 1) = 2 ^ (k - 1) := by
    have e1 : 2 * (c * (c + 1)) = 2 ^ k := by
      calc 2 * (c * (c + 1)) = c * (2 * (c + 1)) := by ring
        _ = c * (y + 1) := by rw [hy2]
        _ = 2 ^ k := hc1
    have e2 : 2 * (c * (c + 1)) = 2 * 2 ^ (k - 1) := by
      have hp2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        rw [Nat.pow_succ]
        ring
      rw [e1, hp2]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) e2
  -- `c` and `c + 1` are both powers of two
  obtain ⟨t, ht, hce⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro (c + 1) hcc1)
  obtain ⟨u, hu, hce2⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (Dvd.intro c (by rw [mul_comm]; exact hcc1))
  rcases Nat.eq_zero_or_pos t with ht0 | ht1
  · -- `c = 1`, so `y = 3` and `2 = 2 ^ (k - 1)` gives `k = 2`, `m = 3`
    rw [ht0, Nat.pow_zero] at hce
    have hyv : y = 3 := by omega
    refine ⟨hyv, ?_⟩
    rw [hce] at hcc1
    norm_num at hcc1
    -- hcc1 : 2 = 2 ^ (k - 1)
    have hkk : k - 1 = 1 := by
      rcases Nat.lt_or_ge (k - 1) 2 with h | h
      · rcases Nat.eq_zero_or_pos (k - 1) with h0 | h1
        · rw [h0, Nat.pow_zero] at hcc1
          omega
        · omega
      · exfalso
        have h2e : 2 ^ (k - 1) = 2 := hcc1.symm
        have hle : 2 ^ 2 ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (n := 2) (by norm_num) h
        omega
    omega
  · -- `t ≥ 1`: `c = 2 ^ t` is even but `c + 1 = 2 ^ u` cannot be
    exfalso
    have hc_even : 2 ∣ c := by
      obtain ⟨j, rfl⟩ : ∃ j, t = j + 1 := ⟨t - 1, by omega⟩
      rw [hce, Nat.pow_succ]
      exact ⟨2 ^ j, by ring⟩
    have hce2e : 2 ∣ (c + 1) := by
      have hpos : 1 ≤ c := by omega
      have hue : u ≠ 0 := by
        intro h0
        rw [h0, Nat.pow_zero] at hce2
        omega
      obtain ⟨j, rfl⟩ : ∃ j, u = j + 1 := ⟨u - 1, by omega⟩
      rw [hce2, Nat.pow_succ]
      exact ⟨2 ^ j, by ring⟩
    obtain ⟨A, hA⟩ := hc_even
    obtain ⟨B, hB⟩ := hce2e
    omega

/-- Descent: `x ^ 2 = 2 ^ i + 2 ^ j` with `i < j` gives `x ^ 2 = 9 * 4 ^ n` for some `n`. -/
lemma desc : ∀ i x j : ℕ, i < j → x ^ 2 = 2 ^ i + 2 ^ j → ∃ n, x ^ 2 = 9 * 4 ^ n := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro x j hij hx
    match i with
    | 0 =>
      rw [Nat.pow_zero] at hx
      obtain ⟨r1, r2⟩ := sq_eq_one_add_two_pow (by omega) hx
      subst r1
      exact ⟨0, by norm_num⟩
    | 1 =>
      exfalso
      have hj1 : 1 ≤ j - 1 := by omega
      have hpow : 2 ^ j = 2 * 2 ^ (j - 1) := by
        have h0 : 2 ^ ((j - 1) + 1) = 2 ^ (j - 1) * 2 := Nat.pow_succ 2 (j - 1)
        rw [show (j - 1) + 1 = j from by omega] at h0
        rw [h0]
        ring
      have hxx : x * x = 2 * (1 + 2 ^ (j - 1)) := by
        have h1 : x * x = x ^ 2 := (Nat.pow_two x).symm
        rw [h1, hx, hpow, Nat.pow_one]
        ring
      have hd2 : 2 ∣ x := ((Nat.Prime.dvd_mul Nat.prime_two).mp
        (⟨1 + 2 ^ (j - 1), hxx⟩ : 2 ∣ x * x)).elim id id
      obtain ⟨x1, rfl⟩ := hd2
      -- (2*x1)² = 4*x1² = 2*(1 + 2^(j-1)) → 2*x1² = 1 + 2^(j-1): even = odd, contradiction
      have heq : 2 * x1 ^ 2 = 1 + 2 ^ (j - 1) := by
        have h4 : 4 * x1 ^ 2 = 2 * (1 + 2 ^ (j - 1)) := by
          have h6 : (2 * x1) * (2 * x1) = 2 * (1 + 2 ^ (j - 1)) := hxx
          calc 4 * x1 ^ 2 = (2 * x1) * (2 * x1) := by ring
            _ = 2 * (1 + 2 ^ (j - 1)) := h6
        have h5 : 2 * (2 * x1 ^ 2) = 2 * (1 + 2 ^ (j - 1)) := by rw [← h4]; ring
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h5
      obtain ⟨k, hk⟩ : ∃ k, j - 1 = k + 1 := ⟨j - 2, by omega⟩
      rw [hk, Nat.pow_succ] at heq
      omega
    | i' + 2 =>
      have hj2 : 2 ≤ j := by omega
      have h1 : 2 ^ (i' + 2) = 4 * 2 ^ i' := by
        have he : i' + 2 = (i' + 1) + 1 := by ring
        rw [he, Nat.pow_succ, Nat.pow_succ]
        ring
      have h2 : 2 ^ j = 4 * 2 ^ (j - 2) := by
        have h0 : 2 ^ ((j - 2) + 2) = 2 ^ (j - 2) * 2 ^ 2 := Nat.pow_add 2 (j - 2) 2
        rw [show (j - 2) + 2 = j from by omega] at h0
        rw [h0]
        ring
      have hx4 : x ^ 2 = 4 * (2 ^ i' + 2 ^ (j - 2)) := by rw [hx, h1, h2]; ring
      have hd2 : 2 ∣ x := ((Nat.Prime.dvd_mul Nat.prime_two).mp
        (⟨2 * (2 ^ i' + 2 ^ (j - 2)), by calc x * x = x ^ 2 := (Nat.pow_two x).symm
          _ = 4 * (2 ^ i' + 2 ^ (j - 2)) := hx4
          _ = 2 * (2 * (2 ^ i' + 2 ^ (j - 2))) := by ring⟩ : 2 ∣ x * x)).elim id id
      obtain ⟨x1, rfl⟩ := hd2
      have hx1 : x1 ^ 2 = 2 ^ i' + 2 ^ (j - 2) := by
        have h7 : 4 * x1 ^ 2 = 4 * (2 ^ i' + 2 ^ (j - 2)) := by
          have h6 : (2 * x1) ^ 2 = 4 * (2 ^ i' + 2 ^ (j - 2)) := hx4
          rw [Nat.mul_pow] at h6
          calc 4 * x1 ^ 2 = 2 ^ 2 * x1 ^ 2 := by norm_num
            _ = 4 * (2 ^ i' + 2 ^ (j - 2)) := h6
        exact Nat.eq_of_mul_eq_mul_left (by norm_num : (0:ℕ) < 4) h7
      obtain ⟨n, hn⟩ := ih i' (by omega) x1 (j - 2) (by omega) hx1
      refine ⟨n + 1, ?_⟩
      have h8 : (2 * x1) ^ 2 = 9 * 4 ^ (n + 1) := by
        rw [Nat.mul_pow, hn, Nat.pow_add]
        norm_num
        ring
      exact h8

end OMA.A002063Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a002063.main := by
  intro x
  constructor
  · -- `x ^ 2 = 2 ^ i + 2 ^ j` implies `x ^ 2 = 9 * 4 ^ n`
    rintro ⟨i, j, hij, hx2⟩
    exact OMA.A002063Aux.desc i x j hij hx2
  · -- `x ^ 2 = 9 * 4 ^ n` implies `x ^ 2 = 2 ^ (2n) + 2 ^ (2n + 3)`
    rintro ⟨n, hn⟩
    refine ⟨2 * n, 2 * n + 3, by omega, ?_⟩
    -- basic power facts
    have hpow2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← Nat.pow_mul, Nat.mul_comm]
    have h4n : 4 ^ n = 2 ^ (2 * n) := by
      have e : (2 ^ 2) ^ n = 2 ^ (2 * n) := (Nat.pow_mul 2 2 n).symm
      rw [show (4:ℕ) = 2 ^ 2 from by norm_num]
      exact e
    have hsq : (3 * 2 ^ n) ^ 2 = 9 * 4 ^ n := by
      rw [Nat.mul_pow, hpow2, h4n]
    have hxa : x = 3 * 2 ^ n := by
      rcases Nat.lt_trichotomy x (3 * 2 ^ n) with hlt | heq | hgt
      · exact absurd hn (by
          have h1 := Nat.pow_lt_pow_left hlt (by norm_num : (2:ℕ) ≠ 0)
          rw [hsq] at h1
          omega)
      · exact heq
      · exact absurd hn (by
          have h1 := Nat.pow_lt_pow_left hgt (by norm_num : (2:ℕ) ≠ 0)
          rw [hsq] at h1
          omega)
    rw [hxa]
    have hl : (3 * 2 ^ n) ^ 2 = 9 * 2 ^ (2 * n) := by
      rw [Nat.mul_pow, hpow2]
    have hr2 : 2 ^ (2 * n) + 2 ^ (2 * n + 3) = 9 * 2 ^ (2 * n) := by
      have e1 : 2 ^ (2 * n + 3) = 2 ^ (2 * n) * 8 := by
        have h0 : 2 ^ (2 * n + 3) = 2 ^ (2 * n) * 2 ^ 3 := by
          rw [Nat.pow_add]
        rw [h0]
        norm_num
      rw [e1]
      ring
    rw [hl, hr2]
