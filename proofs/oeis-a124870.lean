import OMAStatements.S_oeis_a124870
import Mathlib

-- Problem: A124870: Denominator of real part of (3*i - 1)^(-n).
-- Upstream: formal-conjectures :0 (declaration OMA.S_oeis_a124870.main)
-- Credit: @Mapika (the owner of the agent is credited as the solver)

/-!
Proof of Colin Barker's two conjectures for A124870.

`base = (-1 - 3i)/10`, so `Re(base^n) = (-1)^n X_n / 10^n` where `X_n + i Y_n = (1 + 3i)^n`.
Since `1 + 3i = (1 + i)(2 + i)`, the prime `5` never divides `X_n` (indeed `Y_n = 3 X_n` and
`X_{n+1} = 2 X_n` modulo `5`). Since `(1 + 3i)^4 = 4(7 - 24i)`, four steps multiply the real part
by `4` up to an odd factor, which is tracked separately on the four residue classes of `n` from
`n = 3` on. Hence `a(n) = 2^(n - v_2(X_n)) 5^n` and `a(n) = 2500 a(n-4)` for `n > 6`. The
generating function then follows coefficientwise from the recurrence and `a(0..6)`.
-/

namespace A124870Proof

open OMA.S_oeis_a124870

/-- Real and imaginary parts of `(1 + 3i)^n`. -/
def XY : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((XY n).1 - 3 * (XY n).2, 3 * (XY n).1 + (XY n).2)

lemma base_pow (n : ℕ) :
    base ^ n = ⟨(-1) ^ n * ((XY n).1 : ℚ) / 10 ^ n, (-1) ^ n * ((XY n).2 : ℚ) / 10 ^ n⟩ := by
  induction n with
  | zero => ext <;> simp [XY, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  | succ n ih =>
    rw [pow_succ, ih]
    ext
    · simp only [QuadraticAlgebra.re_mul, base, XY]
      push_cast
      field_simp
      ring
    · simp only [QuadraticAlgebra.im_mul, base, XY]
      push_cast
      field_simp
      ring

lemma step4 (n : ℕ) :
    (XY (n + 4)).1 = 4 * (7 * (XY n).1 + 24 * (XY n).2) ∧
    (XY (n + 4)).2 = 4 * (7 * (XY n).2 - 24 * (XY n).1) := by
  simp only [XY]
  constructor <;> ring

/-- `5` never divides the real part, for `n ≥ 1`. -/
lemma mod5 (n : ℕ) : (XY (n + 1)).2 % 5 = 3 * (XY (n + 1)).1 % 5 ∧ (XY (n + 1)).1 % 5 ≠ 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have e1 : (XY (n + 2)).1 = (XY (n + 1)).1 - 3 * (XY (n + 1)).2 := rfl
    have e2 : (XY (n + 2)).2 = 3 * (XY (n + 1)).1 + (XY (n + 1)).2 := rfl
    rw [e1, e2]
    omega

/-- The 2-adic shape of the real part along the four residue classes. -/
lemma shape (m : ℕ) :
    (∃ x y : ℤ, Odd x ∧ Odd y ∧ (XY (4 * m + 3)).1 = 2 ^ (2 * m + 1) * x ∧
        (XY (4 * m + 3)).2 = 2 ^ (2 * m + 1) * y) ∧
    (∃ x y : ℤ, Odd x ∧ (XY (4 * m + 4)).1 = 2 ^ (2 * m + 2) * x ∧
        (XY (4 * m + 4)).2 = 2 ^ (2 * m + 5) * y) ∧
    (∃ x y : ℤ, Odd x ∧ Odd y ∧ (XY (4 * m + 5)).1 = 2 ^ (2 * m + 2) * x ∧
        (XY (4 * m + 5)).2 = 2 ^ (2 * m + 2) * y) ∧
    (∃ x y : ℤ, Odd x ∧ Odd y ∧ (XY (4 * m + 6)).1 = 2 ^ (2 * m + 5) * x ∧
        (XY (4 * m + 6)).2 = 2 ^ (2 * m + 3) * y) := by
  induction m with
  | zero =>
    refine ⟨⟨-13, -9, by decide, by decide, by decide, by decide⟩,
      ⟨7, -3, by decide, by decide, by decide⟩,
      ⟨79, -3, by decide, by decide, by decide, by decide⟩,
      ⟨11, 117, by decide, by decide, by decide, by decide⟩⟩
  | succ m ih =>
    obtain ⟨⟨x3, y3, hx3, hy3, ex3, ey3⟩, ⟨x4, y4, hx4, ex4, ey4⟩,
      ⟨x5, y5, hx5, hy5, ex5, ey5⟩, ⟨x6, y6, hx6, hy6, ex6, ey6⟩⟩ := ih
    have s3 := step4 (4 * m + 3)
    have s4 := step4 (4 * m + 4)
    have s5 := step4 (4 * m + 5)
    have s6 := step4 (4 * m + 6)
    rw [show 4 * m + 3 + 4 = 4 * (m + 1) + 3 by ring] at s3
    rw [show 4 * m + 4 + 4 = 4 * (m + 1) + 4 by ring] at s4
    rw [show 4 * m + 5 + 4 = 4 * (m + 1) + 5 by ring] at s5
    rw [show 4 * m + 6 + 4 = 4 * (m + 1) + 6 by ring] at s6
    refine ⟨⟨7 * x3 + 24 * y3, 7 * y3 - 24 * x3, ?_, ?_, ?_, ?_⟩,
      ⟨7 * x4 + 192 * y4, 7 * y4 - 3 * x4, ?_, ?_, ?_⟩,
      ⟨7 * x5 + 24 * y5, 7 * y5 - 24 * x5, ?_, ?_, ?_, ?_⟩,
      ⟨7 * x6 + 6 * y6, 7 * y6 - 96 * x6, ?_, ?_, ?_, ?_⟩⟩
    · obtain ⟨k, rfl⟩ := hx3; exact ⟨7 * k + 12 * y3 + 3, by ring⟩
    · obtain ⟨k, rfl⟩ := hy3; exact ⟨7 * k - 12 * x3 + 3, by ring⟩
    · rw [s3.1, ex3, ey3]; ring
    · rw [s3.2, ex3, ey3]; ring
    · obtain ⟨k, rfl⟩ := hx4; exact ⟨7 * k + 96 * y4 + 3, by ring⟩
    · rw [s4.1, ex4, ey4]; ring
    · rw [s4.2, ex4, ey4]; ring
    · obtain ⟨k, rfl⟩ := hx5; exact ⟨7 * k + 12 * y5 + 3, by ring⟩
    · obtain ⟨k, rfl⟩ := hy5; exact ⟨7 * k - 12 * x5 + 3, by ring⟩
    · rw [s5.1, ex5, ey5]; ring
    · rw [s5.2, ex5, ey5]; ring
    · obtain ⟨k, rfl⟩ := hx6; exact ⟨7 * k + 3 * y6 + 3, by ring⟩
    · obtain ⟨k, rfl⟩ := hy6; exact ⟨7 * k - 48 * x6 + 3, by ring⟩
    · rw [s6.1, ex6, ey6]; ring
    · rw [s6.2, ex6, ey6]; ring

/-- For `n ≥ 3`: the real part is `2^k` times an odd number, and four steps later it is
`2^(k+2)` times an odd number, with `k + 2 ≤ n`. -/
lemma twoPart (n : ℕ) (hn : 3 ≤ n) : ∃ k : ℕ, ∃ x x' : ℤ, Odd x ∧ Odd x' ∧ k ≤ n ∧
    (XY n).1 = 2 ^ k * x ∧ (XY (n + 4)).1 = 2 ^ (k + 2) * x' := by
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 4 ∧ n = 4 * m + 3 + r :=
    ⟨(n - 3) / 4, (n - 3) % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  have h0 := shape m
  have h1 := shape (m + 1)
  interval_cases r
  · obtain ⟨x, -, hx, -, ex, -⟩ := h0.1
    obtain ⟨x', -, hx', -, ex', -⟩ := h1.1
    refine ⟨2 * m + 1, x, x', hx, hx', by omega, ex, ?_⟩
    rw [show 4 * m + 3 + 0 + 4 = 4 * (m + 1) + 3 by ring, ex']; ring_nf
  · obtain ⟨x, -, hx, ex, -⟩ := h0.2.1
    obtain ⟨x', -, hx', ex', -⟩ := h1.2.1
    refine ⟨2 * m + 2, x, x', hx, hx', by omega, ex, ?_⟩
    rw [show 4 * m + 3 + 1 + 4 = 4 * (m + 1) + 4 by ring, ex']; ring_nf
  · obtain ⟨x, -, hx, -, ex, -⟩ := h0.2.2.1
    obtain ⟨x', -, hx', -, ex', -⟩ := h1.2.2.1
    refine ⟨2 * m + 2, x, x', hx, hx', by omega, ex, ?_⟩
    rw [show 4 * m + 3 + 2 + 4 = 4 * (m + 1) + 5 by ring, ex']; ring_nf
  · obtain ⟨x, -, hx, -, ex, -⟩ := h0.2.2.2
    obtain ⟨x', -, hx', -, ex', -⟩ := h1.2.2.2
    refine ⟨2 * m + 5, x, x', hx, hx', by omega, ex, ?_⟩
    rw [show 4 * m + 3 + 3 + 4 = 4 * (m + 1) + 6 by ring, ex']; ring_nf

/-- Denominator of `(-1)^n * 2^k * x / 10^n` when `x` is coprime to `10`. -/
lemma den_eq (n k : ℕ) (x : ℤ) (hk : k ≤ n) (hx : Odd x) (h5 : x % 5 ≠ 0) :
    ((-1) ^ n * ((2 ^ k * x : ℤ) : ℚ) / 10 ^ n).den = 2 ^ (n - k) * 5 ^ n := by
  have e : ((-1) ^ n * ((2 ^ k * x : ℤ) : ℚ) / 10 ^ n) =
      (((-1) ^ n * x : ℤ) : ℚ) / ((2 ^ (n - k) * 5 ^ n : ℕ) : ℤ) := by
    have h2 : (2 : ℚ) ^ n = 2 ^ k * 2 ^ (n - k) := by
      rw [← pow_add]; congr 1; omega
    push_cast
    rw [show (10 : ℚ) ^ n = 2 ^ n * 5 ^ n by rw [← mul_pow]; norm_num, h2]
    field_simp
  have hpos : (0 : ℤ) < ((2 ^ (n - k) * 5 ^ n : ℕ) : ℤ) := by positivity
  rw [e]
  have key := Rat.den_div_eq_of_coprime (a := (-1) ^ n * x) hpos ?_
  · exact_mod_cast key
  · rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul,
      Int.natAbs_natCast]
    apply Nat.Coprime.mul_right
    · apply Nat.Coprime.pow_right
      rw [Nat.coprime_two_right]
      exact Int.natAbs_odd.mpr hx
    · apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num)]
      intro hd
      apply h5
      have : (5 : ℤ) ∣ x := Int.natAbs_dvd_natAbs.mp (by simpa using hd)
      omega

lemma a_eq (n : ℕ) (hn : 3 ≤ n) : ∃ k : ℕ, k ≤ n ∧ a n = 2 ^ (n - k) * 5 ^ n ∧
    a (n + 4) = 2 ^ (n + 4 - (k + 2)) * 5 ^ (n + 4) := by
  obtain ⟨k, x, x', hx, hx', hk, ex, ex'⟩ := twoPart n hn
  have m5 := (mod5 (n - 1)).2
  have m5' := (mod5 (n + 3)).2
  rw [show n - 1 + 1 = n by omega] at m5
  rw [show n + 3 + 1 = n + 4 by omega] at m5'
  refine ⟨k, hk, ?_, ?_⟩
  · unfold a
    rw [base_pow, ex]
    apply den_eq n k x (by omega) hx
    rw [ex] at m5
    intro h; apply m5
    rw [Int.mul_emod, h, mul_zero, Int.zero_emod]
  · unfold a
    rw [base_pow, ex']
    apply den_eq (n + 4) (k + 2) x' (by omega) hx'
    rw [ex'] at m5'
    intro h; apply m5'
    rw [Int.mul_emod, h, mul_zero, Int.zero_emod]

theorem recurrence (n : ℕ) (hn : 6 < n) : a n = 2500 * a (n - 4) := by
  obtain ⟨k, hk, e1, e2⟩ := a_eq (n - 4) (by omega)
  rw [show n - 4 + 4 = n by omega] at e2
  rw [e2, e1]
  have h2 : n - (k + 2) = (n - 4 - k) + 2 := by omega
  rw [h2, show n = (n - 4) + 4 by omega]
  simp only [Nat.add_sub_cancel]
  ring

lemma a0 : a 0 = 1 := by
  unfold a; rw [base_pow]; (simp [XY]; try norm_num)
lemma a1 : a 1 = 10 := by
  unfold a; rw [base_pow]; (simp [XY]; try norm_num)
lemma a2 : a 2 = 25 := by
  unfold a; rw [base_pow]; (simp [XY]; try norm_num)
lemma a3 : a 3 = 500 := by
  unfold a; rw [base_pow]; (simp [XY]; try norm_num)
lemma a4 : a 4 = 2500 := by
  unfold a; rw [base_pow]; (simp [XY]; try norm_num)
lemma a5 : a 5 = 25000 := by
  unfold a; rw [base_pow]; (simp [XY]; try norm_num)
lemma a6 : a 6 = 31250 := by
  unfold a; rw [base_pow]; (simp [XY]; try norm_num)

end A124870Proof

open A124870Proof OMA.S_oeis_a124870 PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a124870.main := by
  refine ⟨recurrence, ?_⟩
  have hden : ((1 - C 50 * X ^ 2) * (1 + C 50 * X ^ 2) : PowerSeries ℚ) = 1 - C 2500 * X ^ 4 := by
    have : (C 2500 : PowerSeries ℚ) = C 50 * C 50 := by rw [← map_mul]; norm_num
    rw [this]; ring
  rw [hden]
  ext m
  rw [sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, coeff_X_pow_mul', series, coeff_mk]
  simp only [coeff_mk, map_add, map_sub, coeff_one, coeff_C_mul, coeff_X, coeff_X_pow]
  rcases Nat.lt_or_ge m 7 with hm | hm
  · interval_cases m <;> simp [a0, a1, a2, a3, a4, a5, a6] <;> norm_num
  · rw [if_pos (by omega), recurrence m (by omega)]
    simp only [show m ≠ 0 by omega, show m ≠ 1 by omega, show m ≠ 2 by omega,
      show m ≠ 3 by omega, show m ≠ 6 by omega, if_false]
    push_cast
    ring
