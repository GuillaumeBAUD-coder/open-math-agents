import Mathlib

/-!
# OEIS A163733: Barry's generating function

Source: https://oeis.org/A163733 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of n X 2 binary arrays with all 1's connected, all
corners 1, and no 1 having more than two 1's adjacent. Data: 1, 1, 2, 2, 4, 6, 10, 16, 26, ...
Formula section: G.f.: (1-x^3)/(1-x-x^2) (conjecture). - Paul Barry, Aug 10 2009.
This is the first of the conjectures in the formula section of the entry; the others (a
rounding formula and a continued fraction) are not formalized here.

Formalization notes:
* An n X 2 binary array is `A : Fin n → Fin 2 → Fin 2`, with `A i j` the entry in row `i`,
  column `j`.
* Two cells are adjacent when they are orthogonal neighbors: same row and neighboring
  columns, or same column and neighboring rows.
* All 1's are connected when the set of cells holding 1 is connected for this adjacency: it
  cannot be split into two nonempty parts with no adjacent pair of cells across the parts.
* The corners are the cells in the first or the last row (both columns, as there are two).
* The number of 1's adjacent to a cell counts its leftward, rightward, upward and downward
  neighbors, when they exist, that hold 1. Every cell holding 1 has at most two of them.
* This reading reproduces all 40 data terms of the entry (brute force for n <= 8 and a row by
  row transfer count for all terms).
* The entry has offset 1 and its first term a(1) is the constant coefficient of the g.f., so
  the g.f. is Sum_(n >= 0) a(n+1) x^n. Since the denominator has constant term 1, the identity
  is stated as denominator times series equals numerator in the formal power series ring over
  the integers.
-/

namespace OMA.S_oeis_a163733

open PowerSeries

/-- Cells `p` and `q` are orthogonal neighbors. -/
def Adj {n : ℕ} (p q : Fin n × Fin 2) : Prop :=
  (p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) ∨
    (p.2 = q.2 ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val))

instance {n : ℕ} (p q : Fin n × Fin 2) : Decidable (Adj p q) := by
  unfold Adj; infer_instance

/-- The cells holding 1 are connected: every set of such cells that is nonempty and misses some
cell holding 1 contains a cell adjacent to a cell holding 1 outside the set. -/
def OnesConnected {n : ℕ} (A : Fin n → Fin 2 → Fin 2) : Prop :=
  ∀ S : Finset (Fin n × Fin 2), (∀ p ∈ S, A p.1 p.2 = 1) → S.Nonempty →
    (∃ q : Fin n × Fin 2, A q.1 q.2 = 1 ∧ q ∉ S) →
    ∃ p ∈ S, ∃ q : Fin n × Fin 2, A q.1 q.2 = 1 ∧ q ∉ S ∧ Adj p q

instance {n : ℕ} (A : Fin n → Fin 2 → Fin 2) : Decidable (OnesConnected A) := by
  unfold OnesConnected
  refine @Fintype.decidableForallFintype _ _ (fun S => ?_) _
  refine @instDecidableForall _ _ (by infer_instance) ?_
  refine @instDecidableForall _ _ (by infer_instance) ?_
  refine @instDecidableForall _ _ (by infer_instance) ?_
  infer_instance

/-- All corners are 1: every cell in the first or the last row holds 1. -/
def CornersOne {n : ℕ} (A : Fin n → Fin 2 → Fin 2) : Prop :=
  ∀ i j, (i.val = 0 ∨ i.val + 1 = n) → A i j = 1

instance {n : ℕ} (A : Fin n → Fin 2 → Fin 2) : Decidable (CornersOne A) := by
  unfold CornersOne; infer_instance

/-- The leftward neighbor of cell `(i, j)` exists and holds 1. -/
def LeftOne {n : ℕ} (A : Fin n → Fin 2 → Fin 2) (i : Fin n) (j : Fin 2) : Prop :=
  ∃ j' : Fin 2, j'.val + 1 = j.val ∧ A i j' = 1

/-- The rightward neighbor of cell `(i, j)` exists and holds 1. -/
def RightOne {n : ℕ} (A : Fin n → Fin 2 → Fin 2) (i : Fin n) (j : Fin 2) : Prop :=
  ∃ j' : Fin 2, j'.val = j.val + 1 ∧ A i j' = 1

/-- The upward neighbor of cell `(i, j)` exists and holds 1. -/
def UpOne {n : ℕ} (A : Fin n → Fin 2 → Fin 2) (i : Fin n) (j : Fin 2) : Prop :=
  ∃ i' : Fin n, i'.val + 1 = i.val ∧ A i' j = 1

/-- The downward neighbor of cell `(i, j)` exists and holds 1. -/
def DownOne {n : ℕ} (A : Fin n → Fin 2 → Fin 2) (i : Fin n) (j : Fin 2) : Prop :=
  ∃ i' : Fin n, i'.val = i.val + 1 ∧ A i' j = 1

instance {n : ℕ} (A : Fin n → Fin 2 → Fin 2) (i : Fin n) (j : Fin 2) :
    Decidable (LeftOne A i j) := by
  unfold LeftOne; infer_instance

instance {n : ℕ} (A : Fin n → Fin 2 → Fin 2) (i : Fin n) (j : Fin 2) :
    Decidable (RightOne A i j) := by
  unfold RightOne; infer_instance

instance {n : ℕ} (A : Fin n → Fin 2 → Fin 2) (i : Fin n) (j : Fin 2) :
    Decidable (UpOne A i j) := by
  unfold UpOne; infer_instance

instance {n : ℕ} (A : Fin n → Fin 2 → Fin 2) (i : Fin n) (j : Fin 2) :
    Decidable (DownOne A i j) := by
  unfold DownOne; infer_instance

/-- The number of 1's adjacent to cell `(i, j)`. -/
def numAdjOnes {n : ℕ} (A : Fin n → Fin 2 → Fin 2) (i : Fin n) (j : Fin 2) : ℕ :=
  (if LeftOne A i j then 1 else 0) + (if RightOne A i j then 1 else 0) +
    (if UpOne A i j then 1 else 0) + (if DownOne A i j then 1 else 0)

/-- All 1's are connected, all corners are 1, and no 1 has more than two 1's adjacent. -/
def Valid {n : ℕ} (A : Fin n → Fin 2 → Fin 2) : Prop :=
  OnesConnected A ∧ CornersOne A ∧ ∀ i j, A i j = 1 → numAdjOnes A i j ≤ 2

instance {n : ℕ} (A : Fin n → Fin 2 → Fin 2) : Decidable (Valid A) := by
  unfold Valid; infer_instance

/-- A163733(n): the number of valid n X 2 binary arrays. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin n → Fin 2 → Fin 2 => Valid A).card

/-- Barry's conjecture for A163733 (offset 1): the generating function
Sum_(n >= 0) a(n+1) x^n equals (1 - x^3) / (1 - x - x^2). -/
theorem main :
    (1 - X - X ^ 2) * mk (fun n => (a (n + 1) : ℤ)) = (1 - X ^ 3 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a163733
