import OMAStatements.S_oeis_a244713
import Mathlib

/-!
x^2 + x*y - 2*y^2 = u*v with u = x - y and v = x + 2*y = u + 3*y. If 3 does not divide u then
k = u*v is 1 mod 3. If u = 3q then k = 9*q*(q+y), and q*(q+y) = 1 mod 3 would force 3 | y and
3 | x. Conversely 3y+1 = (y+1, y), 27m = (3m+2, 3m-1) and 27m+18 = (3m+4, 3m+1), all
coprime pairs. So the positive numbers represented are those with k = 1 mod 3 or
k = 0, 18 mod 27: eleven per block of 27 consecutive positive integers, hence
a(n+11) = a(n) + 27, which is the recurrence.
-/

namespace R244713
open OMA.S_oeis_a244713

/-- The residue condition. -/
abbrev Q (j : ℕ) : Prop := j % 3 = 1 ∨ j % 27 = 0 ∨ j % 27 = 18

/-- The characterization of the primitively represented numbers. -/
abbrev P (k : ℕ) : Prop := 0 < k ∧ Q k

theorem not_both (x y : ℤ) (h : Int.gcd x y = 1) : x % 3 ≠ 0 ∨ y % 3 ≠ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨c, hcx⟩ : (3 : ℤ) ∣ x := Int.dvd_of_emod_eq_zero hc.1
  obtain ⟨d, hdy⟩ : (3 : ℤ) ∣ y := Int.dvd_of_emod_eq_zero hc.2
  obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.mpr h
  have h3 : (3 : ℤ) ∣ 1 := ⟨u * c + v * d, by rw [hcx, hdy] at huv; linear_combination (-1 : ℤ) * huv⟩
  omega

theorem fwd (k : ℕ) (x y : ℤ) (hg : Int.gcd x y = 1) (hk : x ^ 2 + x * y - 2 * y ^ 2 = k) :
    Q k := by
  have hn := not_both x y hg
  have hfac : (k : ℤ) = (x - y) * (x - y + 3 * y) := by rw [← hk]; ring
  have hu : (x - y) % 3 = 0 ∨ (x - y) % 3 = 1 ∨ (x - y) % 3 = 2 := by omega
  rcases hu with h0 | h1 | h2
  · obtain ⟨q, hq⟩ : ∃ q, x - y = 3 * q := ⟨(x - y) / 3, by omega⟩
    have hw : (k : ℤ) = 9 * (q * (q + y)) := by rw [hfac, hq]; ring
    have hm : (q * (q + y)) % 3 = ((q % 3) * ((q % 3 + y % 3) % 3)) % 3 := by
      rw [Int.mul_emod, Int.add_emod]
    have hq3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
    have hy3 : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by omega
    rcases hq3 with a | a | a <;> rcases hy3 with b | b | b <;> rw [a, b] at hm <;> omega
  · have hm : (k : ℤ) % 3 = ((x - y) % 3 * ((x - y + 3 * y) % 3)) % 3 := by
      rw [hfac, Int.mul_emod]
    rw [show (x - y + 3 * y) % 3 = (x - y) % 3 by omega, h1] at hm
    omega
  · have hm : (k : ℤ) % 3 = ((x - y) % 3 * ((x - y + 3 * y) % 3)) % 3 := by
      rw [hfac, Int.mul_emod]
    rw [show (x - y + 3 * y) % 3 = (x - y) % 3 by omega, h2] at hm
    omega

theorem bwd (k : ℕ) (hk : 0 < k) (h : Q k) : primRep k := by
  refine ⟨hk, ?_⟩
  rcases h with h | h | h
  · obtain ⟨y, hy⟩ : ∃ y : ℤ, (k : ℤ) = 3 * y + 1 := ⟨((k : ℤ) - 1) / 3, by omega⟩
    refine ⟨y + 1, y, ?_, ?_⟩
    · rw [← Int.isCoprime_iff_gcd_eq_one]
      exact ⟨1, -1, by ring⟩
    · rw [hy]; ring
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, (k : ℤ) = 27 * m := ⟨(k : ℤ) / 27, by omega⟩
    refine ⟨3 * m + 2, 3 * m - 1, ?_, ?_⟩
    · rw [← Int.isCoprime_iff_gcd_eq_one]
      exact ⟨m, -(m + 1), by ring⟩
    · rw [hm]; ring
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, (k : ℤ) = 27 * m + 18 := ⟨(k : ℤ) / 27, by omega⟩
    refine ⟨3 * m + 4, 3 * m + 1, ?_, ?_⟩
    · rw [← Int.isCoprime_iff_gcd_eq_one]
      exact ⟨-m, m + 1, by ring⟩
    · rw [hm]; ring

theorem hP : primRep = P := by
  funext k
  apply propext
  constructor
  · rintro ⟨hk, x, y, hg, he⟩
    exact ⟨hk, fwd k x y hg he⟩
  · rintro ⟨hk, h⟩
    exact bwd k hk h

theorem inf : (Set.ofPred P).Infinite :=
  Set.infinite_of_forall_exists_gt fun N =>
    ⟨3 * N + 1, show P (3 * N + 1) from ⟨by omega, Or.inl (by omega)⟩, by omega⟩

theorem win (b : ℕ) (hb : b < 27) : Nat.count (fun k => Q (b + k)) 27 = 11 := by
  have H : ∀ b < 27, Nat.count (fun k => Q (b + k)) 27 = 11 := by decide +kernel
  exact H b hb

theorem countShift (m : ℕ) (hm : 0 < m) : Nat.count P (m + 27) = Nat.count P m + 11 := by
  rw [Nat.count_add]
  congr 1
  rw [Nat.count_eq_card_filter_range, ← win (m % 27) (Nat.mod_lt _ (by norm_num)),
    Nat.count_eq_card_filter_range]
  congr 1
  apply Finset.filter_congr
  intro k _
  simp only [P, Q]
  constructor <;> intro h <;> omega

theorem shift (i : ℕ) : Nat.nth P (i + 11) = Nat.nth P i + 27 := by
  have hm : P (Nat.nth P i) := Nat.nth_mem_of_infinite inf i
  have hm27 : P (Nat.nth P i + 27) := by
    simp only [P, Q] at hm ⊢
    omega
  have hc : Nat.count P (Nat.nth P i + 27) = i + 11 := by
    rw [countShift _ hm.1, Nat.count_nth_of_infinite inf]
  have h1 := Nat.nth_count hm27
  rw [hc] at h1
  exact h1

theorem solve : ∀ n : ℕ, 13 ≤ n → (a n : ℤ) = a (n - 1) + a (n - 11) - a (n - 12) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 13 := ⟨n - 13, by omega⟩
  have e1 : a (m + 13) = a (m + 2) + 27 := by
    show Nat.nth primRep (m + 13 - 1) = Nat.nth primRep (m + 2 - 1) + 27
    rw [hP, show m + 13 - 1 = m + 1 + 11 by omega, show m + 2 - 1 = m + 1 by omega, shift]
  have e2 : a (m + 12) = a (m + 1) + 27 := by
    show Nat.nth primRep (m + 12 - 1) = Nat.nth primRep (m + 1 - 1) + 27
    rw [hP, show m + 12 - 1 = m + 11 by omega, show m + 1 - 1 = m by omega, shift]
  rw [show m + 13 - 1 = m + 12 by omega, show m + 13 - 11 = m + 2 by omega,
    show m + 13 - 12 = m + 1 by omega]
  omega

end R244713

theorem OMA.solution : type_of% @OMA.S_oeis_a244713.main := R244713.solve
