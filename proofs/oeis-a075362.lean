import OMAStatements.S_oeis_a075362
import Mathlib

/-!
# A075362 / A023855: antidiagonal sums of the multiples triangle equal A023855 (claim is true)

Statement. The triangle has entry n k in row n and column k for 1 <= k <= n (row n lists the first
n multiples of n). The m-th antidiagonal is the set of cells with row + column = m. Let antidiag(m)
be its sum. Let A023855(n) = (n+1)(n+3)(2n+1)/24 for odd n and n(n+1)(n+2)/12 for even n.
The claim is that antidiag(n+1) = A023855(n) for every n >= 1.

Proof, for every n >= 1 (write m = n+1 and let S be the antidiagonal sum):

1. Cut. A cell (row m-k, column k) is in the triangle iff k <= m-k, i.e. 2k <= m. So
   S = Sum_{k=0..t} (m-k) k, where t = floor(m/2).
2. Closed form. For 0 <= t <= m, define the partial sum P(t) = Sum_{k=0..t} (m-k) k. Then
   6 P(t) + t(t+1)(2t+1) = 3 m t (t+1). This is proved by induction on t. Going from t to t+1 adds
   6 (m-t-1)(t+1) to the left, and the cubic part changes by (t+1)(t+2)(2t+3) - t(t+1)(2t+1) = 6 (t+1)^2.
   Together these add 6 (t+1) (m - t - 1 + t + 1) = 6 m (t+1), which matches the right side.
3. Parity. Apply step 2 with t = floor((n+1)/2).
   - If n = 2u+1 is odd, then m = 2u+2 and t = u+1. Step 2 gives 6 S = (u+1)(u+2)(4u+3), so
     24 S = (2u+2)(2u+4)(4u+3) = (n+1)(n+3)(2n+1), which is 24 A023855(n).
   - If n = 2t is even, then m = 2t+1 and floor(m/2) = t. Step 2 gives 6 S = 2t(t+1)(2t+1), so
     12 S = 2t(2t+1)(2t+2) = n(n+1)(n+2), which is 12 A023855(n).
-/

namespace OMA.S_oeis_a075362

/-- Step 2: for t <= m, six times the sum of (m-k) k over k = 0..t, plus t(t+1)(2t+1), equals
3 m t (t+1). Proved by induction on t. -/
lemma six_sum (m t : ℕ) (ht : t ≤ m) :
    6 * (∑ k ∈ Finset.range (t+1), (m-k)*k) + t*(t+1)*(2*t+1) = 3*m*t*(t+1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    specialize ih (by omega)
    rw [Finset.sum_range_succ]
    -- The new term is (m - (t+1)) (t+1); this natural subtraction is undone by hm.
    have hm : m - (t+1) + (t+1) = m := by omega
    -- The induction step is the polynomial identity from the header: the new term adds
    -- 6 (m-t-1)(t+1), and the cubic part grows by 6 (t+1)^2, totalling 6 m (t+1).
    nlinarith only [ih, congrArg (fun x : ℕ => 6*x*(t+1)) hm]

/-- Step 1: the terms with 2k > m are not in the triangle, so the antidiagonal sum is the sum
over k = 0..floor(m/2) of (m-k) k. -/
lemma cut_sum (m : ℕ) (hm : 0 < m) :
    antidiag m = ∑ k ∈ Finset.range (m/2+1), (m-k)*k := by
  unfold antidiag
  have sub : Finset.range (m/2+1) ⊆ Finset.range m := Finset.range_mono (by omega)
  -- Terms with k outside range (m/2+1) have 2k > m, so their indicator is 0 and they add nothing.
  rw [← Finset.sum_subset sub (fun k _ hk => by
    simp only [Finset.mem_range] at hk
    simp [show ¬2*k ≤ m by omega])]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  -- For k <= m/2 the cell is in the triangle, so its entry is tri (m-k) k = (m-k) k.
  simp [tri, show 2*k ≤ m by omega]

end OMA.S_oeis_a075362

open OMA.S_oeis_a075362 in
theorem OMA.solution : type_of% @OMA.S_oeis_a075362.main := by
  intro n hn
  -- Step 1: replace the antidiagonal by the cut sum with t = floor((n+1)/2).
  rw [cut_sum _ (by omega)]
  -- Step 2 instantiated at m = n+1 and t = floor((n+1)/2).
  have hs := six_sum (n+1) ((n+1)/2) (by omega)
  -- Name the cut sum s, and record that t = floor((n+1)/2) satisfies 2t <= n+1 < 2t+2.
  generalize (∑ k ∈ Finset.range ((n+1)/2+1), (n+1-k)*k) = s at *
  have bounds : 2*((n+1)/2) ≤ n+1 ∧ n+1 < 2*((n+1)/2)+2 := by omega
  generalize (n+1)/2 = t at *
  unfold a023855
  -- Step 3: split on the parity of n.
  split <;> rename_i parity
  · -- Odd case n = 2u+1: then t = u+1.
    obtain ⟨u, rfl⟩ : ∃ u, n = 2*u+1 := ⟨n/2, by omega⟩
    have ht : t = u+1 := by omega
    subst t
    -- Finite algebra: 24 s = (n+1)(n+3)(2n+1) in this parity, from step 2.
    have : (2*u+1+1)*(2*u+1+3)*(2*(2*u+1)+1) = 24*s := by nlinarith only [hs]
    omega
  · -- Even case n = 2t: then floor((n+1)/2) = t.
    have he : n = 2*t := by omega
    subst n
    -- Finite algebra: 12 s = n(n+1)(n+2) in this parity, from step 2.
    have : 2*t*(2*t+1)*(2*t+2) = 12*s := by nlinarith only [hs]
    omega
