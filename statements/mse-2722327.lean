import Mathlib

/-!
# A limit involving the Thue–Morse sequence

The question: "Let's define t_n by the recurrence t_0 = 1, t_n = (-1)^n t_{⌊n/2⌋}
... Now, let L(z) = lim_{n→∞} ∑_{k=1}^{2^n-1} t_k k^z. I conjecture that the
following propositions hold: (a) The limit L(z) exists for all z ∈ ℂ.
(b) L(z) is an entire function of z. (c) L(z) = 0 if [and only if, struck out]
z ∈ ℤ⁺. Can we prove these conjectures?"

THIS STATEMENT COVERS ONLY PART OF THE QUESTION: the "if" part of (c), i.e.
L(m) exists and equals 0 for every positive integer m. Parts (a), (b) and the
(struck-out) "only if" direction are not settled on the page and are not
formalized here.

Formalized claim: for every positive integer m, the partial sums
∑_{k=1}^{2^n-1} t_k k^m converge to 0 as n → ∞ (so the limit exists and is 0).

Reading choices:
* t is defined literally by the source's recurrence, with values in ℤ
  (`n / 2` is the natural-number floor division ⌊n/2⌋).
* z ranges over ℤ⁺ = {1, 2, 3, ...}, taken as natural numbers m with 0 < m;
  k^z is written as the complex power `(k : ℂ) ^ (m : ℂ)` (equal to k^m),
  and the limit is taken in ℂ, since the source's L is a complex function.
* `Finset.Ico 1 (2 ^ n)` is the index range k = 1, ..., 2^n - 1.

How the page settles it: not by an answer but by the question's own update
("The 'if' part of the conjecture (c) is certainly true", linking the classical
Prouhet / Prouhet–Tarry–Escott identity: the sum over k < 2^n vanishes as soon
as n > m). The only answer (top-voted) gives an integral representation of L
for non-integer z and is not used.

Source: https://math.stackexchange.com/questions/2722327/a-limit-involving-the-thue-morse-sequence
Credit: @xor2k
-/

namespace OMA.S_mse_2722327

open Filter Topology

/-- Thue–Morse signs: `t 0 = 1`, `t n = (-1)^n * t (n / 2)`. -/
def t : ℕ → ℤ
  | 0 => 1
  | n + 1 => (-1) ^ (n + 1) * t ((n + 1) / 2)
decreasing_by omega

theorem main : ∀ m : ℕ, 0 < m →
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.Ico 1 (2 ^ n), (t k : ℂ) * (k : ℂ) ^ (m : ℂ))
      atTop (𝓝 0) := by
  sorry

end OMA.S_mse_2722327
