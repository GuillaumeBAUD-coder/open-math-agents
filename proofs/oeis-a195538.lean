import OMAStatements.S_oeis_a195538

/-! Credit: @unserus

convPair n is ((4v+y, y), (5v+y, v)) for a state (y, v) with (y, v) -> (y+4v, y+5v) and
invariant y^2 + 4vy - 4v^2 = 1 (y odd). Explicit Bezout identities show the reduced
denominators are (4v+y)y and 2(5v+y)v; these quadratic forms satisfy the order-3 recurrence
with signature (35, -35, 1), which gives all three claims. -/

namespace OMAA195538Helpers
open OMA.S_oeis_a195538

def st : ℕ → ℤ × ℤ
  | 0 => (1, 1)
  | n + 1 => ((st n).1 + 4 * (st n).2, (st n).1 + 5 * (st n).2)

theorem conv (n : ℕ) : convPair n =
    ((4 * (st n).2 + (st n).1, (st n).1), (5 * (st n).2 + (st n).1, (st n).2)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [convPair, ih, st]
    simp only [Prod.mk.injEq]
    refine ⟨⟨by ring, by ring⟩, by ring, by ring⟩

theorem inv (n : ℕ) : (st n).1 ^ 2 + 4 * (st n).2 * (st n).1 - 4 * (st n).2 ^ 2 = 1 ∧
    Odd (st n).1 ∧ 0 < (st n).1 ∧ 0 < (st n).2 := by
  induction n with
  | zero => refine ⟨by norm_num [st], by decide, by norm_num [st], by norm_num [st]⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [st]
    refine ⟨by linear_combination h1, ?_, by omega, by omega⟩
    obtain ⟨m, hm⟩ := h2
    exact ⟨m + 2 * (st n).2, by rw [hm]; ring⟩

def De (s : ℤ × ℤ) : ℤ := (4 * s.2 + s.1) * s.1
def Do (s : ℤ × ℤ) : ℤ := 2 * (5 * s.2 + s.1) * s.2

theorem coprime_of (a b : ℤ) (h : IsCoprime a b) : Nat.Coprime a.natAbs b.natAbs :=
  Int.isCoprime_iff_gcd_eq_one.mp h

theorem ratio_even (y v : ℤ) (hJ : y ^ 2 + 4 * v * y - 4 * v ^ 2 = 1) (hodd : Odd y)
    (hy : 0 < y) (hv : 0 < v) :
    ((((((4 * v + y : ℤ) : ℚ) ^ 2 - ((y : ℤ) : ℚ) ^ 2) /
      (2 * ((4 * v + y : ℤ) : ℚ) * ((y : ℤ) : ℚ))).den : ℕ) : ℚ) = (((4 * v + y) * y : ℤ) : ℚ) := by
  have hx : 0 < 4 * v + y := by omega
  have hr : (((4 * v + y : ℤ) : ℚ) ^ 2 - ((y : ℤ) : ℚ) ^ 2) / (2 * ((4 * v + y : ℤ) : ℚ) * ((y : ℤ) : ℚ))
      = ((8 * v ^ 2 + 4 * v * y : ℤ) : ℚ) / (((4 * v + y) * y : ℤ) : ℚ) := by
    have hy' : (y : ℚ) ≠ 0 := by exact_mod_cast hy.ne'
    have hx' : ((4 * v + y : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hx.ne'
    push_cast at hx' ⊢
    field_simp
    ring
  have hcop : IsCoprime (8 * v ^ 2 + 4 * v * y) ((4 * v + y) * y) := by
    obtain ⟨m, hm⟩ := hodd
    apply IsCoprime.mul_right
    · obtain ⟨k, hk⟩ : Odd (4 * v + y) := ⟨2 * v + m, by rw [hm]; ring⟩
      refine ⟨-k, 1 + k * (12 * v - 2 * (4 * v + y)), ?_⟩
      linear_combination hk - 2 * k * hJ
    · refine ⟨m, 1 - m * (2 * y + 12 * v), ?_⟩
      linear_combination hm - 2 * m * hJ
  rw [hr]
  have h := Rat.den_div_eq_of_coprime (by positivity) (coprime_of _ _ hcop)
  exact_mod_cast h

theorem ratio_odd (y v : ℤ) (hJ : y ^ 2 + 4 * v * y - 4 * v ^ 2 = 1)
    (hy : 0 < y) (hv : 0 < v) :
    ((((((5 * v + y : ℤ) : ℚ) ^ 2 - ((v : ℤ) : ℚ) ^ 2) /
      (2 * ((5 * v + y : ℤ) : ℚ) * ((v : ℤ) : ℚ))).den : ℕ) : ℚ) = ((2 * (5 * v + y) * v : ℤ) : ℚ) := by
  have hu : 0 < 5 * v + y := by omega
  have hr : (((5 * v + y : ℤ) : ℚ) ^ 2 - ((v : ℤ) : ℚ) ^ 2) / (2 * ((5 * v + y : ℤ) : ℚ) * ((v : ℤ) : ℚ))
      = ((24 * v ^ 2 + 10 * v * y + y ^ 2 : ℤ) : ℚ) / ((2 * (5 * v + y) * v : ℤ) : ℚ) := by
    push_cast; ring
  have hcop : IsCoprime (24 * v ^ 2 + 10 * v * y + y ^ 2) (2 * (5 * v + y) * v) := by
    apply IsCoprime.mul_right
    apply IsCoprime.mul_right
    · refine ⟨1, -(3 * (5 * v + y) * v - v ^ 2), ?_⟩
      linear_combination hJ
    · refine ⟨-1, 2 * (5 * v + y) - 6 * v, ?_⟩
      linear_combination hJ
    · refine ⟨1, 2 * v - 6 * (5 * v + y), ?_⟩
      linear_combination hJ
  rw [hr]
  have h := Rat.den_div_eq_of_coprime (by positivity) (coprime_of _ _ hcop)
  exact_mod_cast h

theorem a_even (n : ℕ) : a (2 * n) = (De (st n) : ℚ) := by
  obtain ⟨hJ, hodd, hy, hv⟩ := inv n
  simp only [a, sourceRatio, show 2 * n % 2 = 0 by omega, if_true, show 2 * n / 2 = n by omega,
    conv n, De]
  rw [ratio_even _ _ hJ hodd hy hv]

theorem a_odd (n : ℕ) : a (2 * n + 1) = (Do (st n) : ℚ) := by
  obtain ⟨hJ, -, hy, hv⟩ := inv n
  simp only [a, sourceRatio, show (2 * n + 1) % 2 = 1 by omega, show (1 : ℕ) ≠ 0 by omega,
    if_false, show (2 * n + 1) / 2 = n by omega, conv n, Do]
  rw [ratio_odd _ _ hJ hy hv]

theorem De_r3 : ∀ n : ℕ, (De (st n) : ℚ) = r3 1 5 145 (n + 1)
  | 0 => by norm_num [De, st, r3]
  | 1 => by norm_num [De, st, r3]
  | 2 => by norm_num [De, st, r3]
  | n + 3 => by
    have h0 := De_r3 n
    have h1 := De_r3 (n + 1)
    have h2 := De_r3 (n + 2)
    rw [show n + 3 + 1 = (n + 1) + 3 by ring, r3, show n + 1 + 2 = n + 2 + 1 by ring, ← h0, ← h1, ← h2]
    simp only [De, st]
    push_cast
    ring

theorem Do_r3 : ∀ n : ℕ, (Do (st n) : ℚ) = r3 0 12 420 (n + 1)
  | 0 => by norm_num [Do, st, r3]
  | 1 => by norm_num [Do, st, r3]
  | 2 => by norm_num [Do, st, r3]
  | n + 3 => by
    have h0 := Do_r3 n
    have h1 := Do_r3 (n + 1)
    have h2 := Do_r3 (n + 2)
    rw [show n + 3 + 1 = (n + 1) + 3 by ring, r3, show n + 1 + 2 = n + 2 + 1 by ring, ← h0, ← h1, ← h2]
    simp only [Do, st]
    push_cast
    ring

end OMAA195538Helpers

open OMAA195538Helpers OMA.S_oeis_a195538 in
theorem OMA.solution : type_of% @OMA.S_oeis_a195538.main := by
  have hE : ∀ n : ℕ, a (2 * n) = r3 1 5 145 (n + 1) := fun n => (a_even n).trans (De_r3 n)
  have hO : ∀ n : ℕ, a (2 * n + 1) = r3 0 12 420 (n + 1) := fun n => (a_odd n).trans (Do_r3 n)
  refine ⟨?_, hE, hO⟩
  intro n
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show 2 * k + 6 = 2 * (k + 3) by ring, show 2 * k + 4 = 2 * (k + 2) by ring,
      show 2 * k + 2 = 2 * (k + 1) by ring, hE, hE, hE, hE,
      show k + 3 + 1 = (k + 1) + 3 by ring, r3]
  · rw [show 2 * k + 1 + 6 = 2 * (k + 3) + 1 by ring, show 2 * k + 1 + 4 = 2 * (k + 2) + 1 by ring,
      show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring, hO, hO, hO, hO,
      show k + 3 + 1 = (k + 1) + 3 by ring, r3]
