import Mathlib

/-!
# Boundary-covering cycles on a grid of width five

Source: https://oeis.org/A358696. Recurrence conjectured by Seiichi Manyama,
November 2022. OEIS Foundation, CC BY-SA 4.0. Formalization: @shunyaekam.

A path is an unoriented cycle, counted once regardless of its starting vertex.
We encode its edge set by including both orders of each consecutive pair.
-/

namespace OMA.S_oeis_a358696

abbrev Vertex (n : ℕ) := Fin 5 × Fin n

def adjacent {n : ℕ} (u v : Vertex n) : Prop :=
  (u.1 = v.1 ∧ (u.2.val + 1 = v.2.val ∨ v.2.val + 1 = u.2.val)) ∨
  (u.2 = v.2 ∧ (u.1.val + 1 = v.1.val ∨ v.1.val + 1 = u.1.val))

def boundary {n : ℕ} (u : Vertex n) : Prop :=
  u.1.val = 0 ∨ u.1.val = 4 ∨ u.2.val = 0 ∨ u.2.val + 1 = n

def isLoop {n : ℕ} (edges : Finset (Vertex n × Vertex n)) : Prop :=
  ∃ k : ℕ, 3 ≤ k ∧ ∃ v : ℕ → Vertex n,
    Set.InjOn v (Set.Iio k) ∧
    (∀ i < k, adjacent (v i) (v ((i + 1) % k))) ∧
    (∀ p, boundary p → ∃ i < k, v i = p) ∧
    (∀ p q, (p,q) ∈ edges ↔ ∃ i < k,
      (p = v i ∧ q = v ((i + 1) % k)) ∨ (q = v i ∧ p = v ((i + 1) % k)))

noncomputable def count (n : ℕ) : ℤ := by
  classical
  exact ((Finset.univ.filter (fun e : Finset (Vertex n × Vertex n) => isLoop e)).card : ℤ)

theorem main : ∀ n : ℕ, 10 < n →
    count n = 6 * count (n-1) + count (n-2) - 20 * count (n-3) +
      37 * count (n-4) + 16 * count (n-5) - 12 * count (n-6) -
      7 * count (n-7) + 5 * count (n-8) - count (n-9) := by
  sorry

end OMA.S_oeis_a358696
