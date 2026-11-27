import FormalConjectures.ErdosProblems.«295»

-- Reduction Erdos295.erdos_295.variants.erdos_straus.R1 of Erdős Problem 295 — erdos straus
-- Credit: @mrmario2202
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Splits the Erdős–Straus bounds `-C < k(N) - (e-1)N ≤ O N / log N` into its two halves, each stated
directly about representations `1 = 1/n_1 + ... + 1/n_m` with `N ≤ n_1 < ... < n_m` (no `sInf`).
`main` does the glue: `H2` makes the set defining `k N` nonempty, so `k N` is attained (and `H1`
bounds it below) and is at most the length of the `H2` witness.
- `H1` (elementary lower bound): every such representation has `m > (e-1)N - C`. Since `n_i ≥ N + i`,
  `1 ≤ ∑_{i<m} 1/(N+i) ≤ log((N+m-1)/(N-1))`, so `C = 2` works for `N ≥ 2`.
- `H2` (the Erdős–Straus construction [ErSt71b]): a representation with at most
  `(e-1)N + O N / log N` terms exists for all large `N`.
-/

namespace OMA.R_Erdos295_erdos_295_variants_erdos_straus_R1

open Filter

/-- Lower bound: any representation of `1` by distinct unit fractions with denominators `≥ N`
has more than `(e - 1) N - C` terms, for all large `N`. -/
def H1 : Prop :=
  ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (n : Fin m → ℕ),
    (∀ i, N ≤ n i) → StrictMono n → ∑ i, (1 / n i : ℝ) = 1 →
      (Real.exp 1 - 1) * N - C < m

/-- Upper bound (Erdős–Straus): for all large `N` there is a representation of `1` by distinct
unit fractions with denominators `≥ N` using at most `(e - 1) N + O N / log N` terms. -/
def H2 : Prop :=
  ∃ O > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∃ (m : ℕ) (n : Fin m → ℕ),
    (∀ i, N ≤ n i) ∧ StrictMono n ∧ ∑ i, (1 / n i : ℝ) = 1 ∧
      (m : ℝ) ≤ (Real.exp 1 - 1) * N + O * N / Real.log N

theorem main : H1 → H2 → type_of% @Erdos295.erdos_295.variants.erdos_straus := by
  rintro ⟨C, hC, h1⟩ ⟨O, hO, h2⟩
  refine ⟨C, hC, O, hO, ?_⟩
  filter_upwards [h1, h2] with N hN1 hN2
  obtain ⟨m, n, hn, hmono, hsum, hm⟩ := hN2
  have hne : {k | ∃ n : Fin k → ℕ, (∀ i, N ≤ n i) ∧ StrictMono n ∧
      ∑ i, (1 / n i : ℝ) = 1}.Nonempty := ⟨m, n, hn, hmono, hsum⟩
  obtain ⟨n', hn', hmono', hsum'⟩ := Nat.sInf_mem hne
  have hlow := hN1 _ n' hn' hmono' hsum'
  have hle : Erdos295.k N ≤ m := Nat.sInf_le ⟨n, hn, hmono, hsum⟩
  have hle' : (Erdos295.k N : ℝ) ≤ m := by exact_mod_cast hle
  constructor
  · show -C < (Erdos295.k N : ℝ) - (Real.exp 1 - 1) * N
    have : (Real.exp 1 - 1) * N - C < (Erdos295.k N : ℝ) := hlow
    linarith
  · show (Erdos295.k N : ℝ) - (Real.exp 1 - 1) * N ≤ O * N / Real.log N
    linarith

end OMA.R_Erdos295_erdos_295_variants_erdos_straus_R1
