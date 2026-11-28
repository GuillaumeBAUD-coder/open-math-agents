import FormalConjectures.ErdosProblems.«373»

/-!
# A reduction of Erdős Problem 373 (Surányi's `a!b! = n!` question)

`Erdos373.erdos_373.variants.suranyi` asks: the only non-trivial solution of `n! = a! * b!`
with `1 < b ≤ a` and `a + 1 ≠ n` is `(n, a, b) = (10, 7, 6)` (since `6! * 7! = 10!`).

The problem is open: erdosproblems.com/373 reports that no other solution exists for
`n ≤ 10^3000` (Caldwell; Habsieger), while Erdős [Er93] proved `a ≥ n - 5 log log n` for
every solution and Luca proved finiteness conditionally on ABC. So the reduction splits off
everything that is *not* the hard analytic core:

* `H1` — structure of any solution: a prime `p` with `n < 2p`, `b < p ≤ a`.
  Proof sketch (elementary, no analysis): take `p` prime with `n/2 < p ≤ n` (Bertrand);
  its exponent in `n!` is `1` (as `n < 2p`), so `p` divides exactly one of `a!`, `b!`.
  It cannot divide `b!`: then `p ≤ b ≤ a` would make it divide `a!` too, giving `p^2 ∣ n!`.
  Hence `b < p ≤ a`.
* `H2` — the open core, for `n ≥ 17`, stated with the structure of `H1` already available.
* `H3` — the finite base `n ≤ 16`, which is decidable by computation.

`main` assembles the three into the exact target.
-/

namespace OMA.R_Erdos373_erdos_373_variants_suranyi_R1

/-- Every non-trivial solution has a prime `p` with `n < 2 p`, `b < p` and `p ≤ a`. -/
def H1 : Prop :=
  ∀ (n a b : ℕ), Nat.factorial n = Nat.factorial a * Nat.factorial b → 1 < n → 1 < a →
    1 < b → b ≤ a → a + 1 ≠ n →
    ∃ p : ℕ, p.Prime ∧ n < 2 * p ∧ b < p ∧ p ≤ a

/-- The core: no solution with `n ≥ 17`, assuming the structure supplied by `H1`. -/
def H2 : Prop :=
  ∀ (n a b p : ℕ), 17 ≤ n → p.Prime → n < 2 * p → b < p → p ≤ a → a + 1 ≠ n →
    Nat.factorial n = Nat.factorial a * Nat.factorial b → 1 < b → False

/-- The finite base `n ≤ 16`: the only solution is `(10, 7, 6)`. -/
def H3 : Prop :=
  ∀ (n a b : ℕ), n ≤ 16 → Nat.factorial n = Nat.factorial a * Nat.factorial b → 1 < n →
    1 < a → 1 < b → b ≤ a → a + 1 ≠ n → n = 10 ∧ a = 7 ∧ b = 6

theorem main : H1 → H2 → H3 → type_of% @Erdos373.erdos_373.variants.suranyi := by
  intro h1 h2 h3
  refine Set.ext ?_
  rintro ⟨n, a, b⟩
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨heq, hn, ha, hb, hba, hne⟩
    by_cases h16 : n ≤ 16
    · exact h3 n a b h16 heq hn ha hb hba hne
    · push_neg at h16
      obtain ⟨p, hp, h2p, hbp, hpa⟩ := h1 n a b heq hn ha hb hba hne
      exact (h2 n a b p h16 hp h2p hbp hpa hne heq hb).elim
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨?_, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    decide

end OMA.R_Erdos373_erdos_373_variants_suranyi_R1
