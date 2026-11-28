import Mathlib

/-!
# A358360: The 3-adic valuation of the central Delannoy numbers (A001850).

Source: https://oeis.org/A358360
Credit: @esracummings31-blip

Central Delannoy numbers (A001850): D(n) = Sum_{k=0..n} C(n,k)^2 * 2^k
(a standard formula listed in A001850; equivalently Sum_k C(n,k) C(n+k,k)).
a(n) = v_3(D(n)) (offset 0).

Conjectures from Ridouane Oudra, May 20 2026:
1. a(n) = Sum_{k=1..n} (-1)^(k+1) * A051064(k), where A051064(k) = v_3(3k).
2. a(n) = Sum_{k>=0} (floor(n/3^k) mod 2)   (terms with 3^k > n vanish, so k ≤ n suffices).
3. a(n) = A000989(floor((n+1)/2)) + A168570(n+1), where A000989(m) = v_3(C(2m,m))
   and A168570(m) = v_3(2^m - 1).
4. a(2n) = A000989(n).
5. a(2n+1) = A000989(n) + A254046(n+1), where A254046 (offset 1) is given by
   A254046(3m) = 1, A254046(3m+1) = 1, A254046(3m+2) = 1 + A254046(m+1).
-/

namespace OMA.S_oeis_a358360

/-- Central Delannoy numbers A001850. -/
def D (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k ^ 2 * 2 ^ k

/-- A358360: 3-adic valuation of the central Delannoy numbers. -/
def a (n : ℕ) : ℕ := padicValNat 3 (D n)

/-- A051064: 3-adic valuation of 3n. -/
def A051064 (k : ℕ) : ℕ := padicValNat 3 (3 * k)

/-- A000989: 3-adic valuation of C(2n, n). -/
def A000989 (n : ℕ) : ℕ := padicValNat 3 ((2 * n).choose n)

/-- A168570: exponent of 3 in 2^n - 1. -/
def A168570 (n : ℕ) : ℕ := padicValNat 3 (2 ^ n - 1)

/-- A254046 (offset 1): a(3m) = 1, a(3m+1) = 1, a(3m+2) = 1 + a(m+1). -/
def A254046 (n : ℕ) : ℕ :=
  if n % 3 = 2 then 1 + A254046 ((n + 1) / 3) else 1
decreasing_by omega

theorem main :
    (∀ n : ℕ, (a n : ℤ) = ∑ k ∈ Finset.Icc 1 n, (-1 : ℤ) ^ (k + 1) * (A051064 k : ℤ)) ∧
    (∀ n : ℕ, a n = ∑ k ∈ Finset.range (n + 1), (n / 3 ^ k) % 2) ∧
    (∀ n : ℕ, a n = A000989 ((n + 1) / 2) + A168570 (n + 1)) ∧
    (∀ n : ℕ, a (2 * n) = A000989 n) ∧
    (∀ n : ℕ, a (2 * n + 1) = A000989 n + A254046 (n + 1)) := by
  sorry

end OMA.S_oeis_a358360
