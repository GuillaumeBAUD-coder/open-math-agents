import Mathlib

/-!
# A372015: equally colored adjacent parts in n-color compositions

Source: https://oeis.org/A372015
Credit: @rgoldman73-dev

John Tyler Rascoe's conjecture (July 30, 2024), for every n >= 0.
In the standard meaning of "n-color composition", a part of size k has
colors 1,...,k; n is not a fixed number of available colors. See Hopkins
and Wang, JIS 27 (2024), Article 24.7.8, p.2.

`compositions n` enumerates all ordered positive compositions, once each.
The empty composition of zero is included. The product of the parts is
the number of their independent colorings, so `coloredCount n` counts
all colored compositions of total size n.

To count pairs of adjacent equally colored parts, distinguish the pair
and cut immediately before and after it. This uniquely gives a left
composition, two part sizes k,l, a common color in 1,...,min(k,l), and a
right composition. `pairChoices m` counts the two middle parts of total
size m; zero-sized parts contribute zero. `totalPairs N` sums over the
three sizes (left, middle, right) using finite antidiagonals. It therefore
counts occurrences of pairs, including multiple occurrences in one
composition, rather than counting only compositions that contain a pair.

The other side is the product of F(n+1) and its self-convolution at n+1,
using F(0)=0 and F(1)=1. No conjectured recurrence or generating function
is used to define either count.
-/

namespace OMA.S_oeis_a372015

def completions : ℕ → ℕ → List (List ℕ)
  | 0, k => [[k]]
  | r+1, k => completions r (k+1) ++ (completions r 1).map (k :: ·)

def compositions : ℕ → List (List ℕ)
  | 0 => [[]]
  | n+1 => completions n 1

def coloredCount (n : ℕ) : ℕ := ((compositions n).map List.prod).sum

def pairChoices (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, min p.1 p.2

def totalPairs (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coloredCount p.1 *
    (∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.2, pairChoices q.1 * coloredCount q.2)

def fibConvolution (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, Nat.fib p.1 * Nat.fib p.2

theorem main : ∀ n : ℕ,
    totalPairs (n+1) = Nat.fib (n+1) * fibConvolution (n+1) := by
  sorry

end OMA.S_oeis_a372015
