import Mathlib

/-!
# A209530: Half the number of (n+1) X 3 0..2 arrays with every 2 X 2 subblock having exactly two distinct clockwise edge differences

Source: https://oeis.org/A209530
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 9, 25, 65, 193, 513, 1537, 4097, ...). An array is a map
x : Fin (n+1) → Fin 3 → Fin 3 (row i, column j, value in 0..2); its 2 X 2 subblocks are formed by
rows i, i+1 and columns j, j+1. Going clockwise around the subblock [[p, q], [r, s]] (p -> q -> s ->
r -> p), the edge differences are q - p, s - q, r - s, p - r (integers), and exactly two distinct
values must occur among them. a(n) is half the number N(n) of such arrays.

Conjectures (Colin Barker, Jul 10 2018), together with the empirical recurrence of the entry:
a(n) = a(n-1) + 8*a(n-2) - 8*a(n-3) (stated for n ≥ 4, all indices at least the offset 1, over ℤ);
G.f.: x*(9 + 16*x - 32*x^2) / ((1 - x)*(1 - 8*x^2)) (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 3*2^((3*(n - 1))/2 + 3/2) + 1 for n even, a(n) = 2^((3*(n - 1))/2 + 3) + 1 for n odd
(n ≥ 1, over ℝ, with the exponents computed in ℝ).
-/

namespace OMA.S_oeis_a209530

/-- Exactly two distinct values among the clockwise edge differences of [[p, q], [r, s]]. -/
def CW2 (p q r s : Fin 3) : Prop :=
  ([(q : ℤ) - p, (s : ℤ) - q, (r : ℤ) - s, (p : ℤ) - r].toFinset).card = 2

/-- Both 2 X 2 subblocks formed by rows u, v satisfy the condition. -/
def BlockOK (u v : Fin 3 → Fin 3) : Prop :=
  ∀ j : Fin 2, CW2 (u j.castSucc) (u j.succ) (v j.castSucc) (v j.succ)

/-- N(n): the number of such (n+1) X 3 arrays. -/
noncomputable def N (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 3 → Fin 3 // ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)}

/-- a(n) = N(n)/2. -/
noncomputable def a (n : ℕ) : ℕ := N n / 2

/-- The conjectured g.f. x*(9 + 16*x - 32*x^2) / ((1 - x)*(1 - 8*x^2)). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (9 + 16 * PowerSeries.X - 32 * PowerSeries.X ^ 2)) *
    ((1 - PowerSeries.X) * (1 - 8 * PowerSeries.X ^ 2))⁻¹

/-- The recurrence, the g.f. and the closed forms. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = a (n - 1) + 8 * a (n - 2) - 8 * a (n - 3)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → Even n →
      (a n : ℝ) = 3 * (2 : ℝ) ^ ((3 * ((n : ℝ) - 1)) / 2 + 3 / 2) + 1) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℝ) = (2 : ℝ) ^ ((3 * ((n : ℝ) - 1)) / 2 + 3) + 1) := by
  sorry

end OMA.S_oeis_a209530
