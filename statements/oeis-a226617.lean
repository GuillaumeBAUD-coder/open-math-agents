import Mathlib

/-!
# A primitive cycle with any positive number of odd terms

Source: https://oeis.org/A226617 (Geoffrey H. Morley, 2013)
Credit: @etaubman

Take D=3^n-2^n and choose r>0 with D dividing 2^r-1. Set
t=(2^r-1)/D and k=2^n t-1. Starting from one, the first n
states are odd. The next state is 2^r, which returns to one by halving.
-/

namespace OMA.S_oeis_a226617

def step (k : ℕ) (x : ℤ) : ℤ :=
  if Odd x then (3*x+k)/2 else x/2

def qualifies (n k : ℕ) : Prop :=
  0 < k ∧ Odd k ∧ ∃ (L : ℕ) (f : ℕ → ℤ),
  0 < L ∧ f 0 = 1 ∧ f L = 1 ∧
  (∀ i < L, 0 < f i ∧ f (i+1) = step k (f i)) ∧
  (∀ i, 0 < i → i < L → 1 < f i) ∧
  ((Finset.range L).filter (fun i => Odd (f i))).card = n ∧
  (∀ d : ℤ, 1 < d → ¬ ∀ i < L, d ∣ f i)

noncomputable def sequence (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, qualifies n k then Nat.find h else 0

theorem main (n : ℕ) (hn : 0 < n) : 0 < sequence n := by
  sorry

end OMA.S_oeis_a226617
