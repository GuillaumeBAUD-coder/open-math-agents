import FormalConjectures.ErdosProblems.«878»

-- Credit: @aspher1
-- Formalizes Barreto's counterexample at x = 210, recorded in the upstream statement.

open Erdos878

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem OMA.solution : type_of% @Erdos878.erdos_878.parts.iii_all := by
  intro heq
  have hf : maxUpTo f 210 ≤ 383 := by
    unfold maxUpTo
    apply Finset.sup_le
    intro n hn
    have hn' : n < 211 := Finset.mem_range.mp hn
    interval_cases n <;>
      norm_num [f, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  let A : Finset ℕ := {128, 125, 189}
  have hA : A ⊆ Finset.Icc 2 210 := by decide
  have hcop : (A : Set ℕ).Pairwise Nat.Coprime := by decide
  have hprimes : ∀ a ∈ A, a.primeFactors ⊆ (210 : ℕ).primeFactors := by
    norm_num [A, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have hF : 442 ≤ F 210 := by
    classical
    unfold F
    apply Finset.le_sup_of_le (b := A)
    · refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA, hA, hcop, ?_⟩
      intro a ha p hp hpa
      have ha0 : a ≠ 0 := by
        have hpos := (Finset.mem_Icc.mp (hA ha)).1
        omega
      exact Nat.dvd_of_mem_primeFactors
        ((hprimes a ha) (hp.mem_primeFactors hpa ha0))
    · norm_num [A]
  have hmax : F 210 ≤ maxUpTo F 210 := by
    exact Finset.le_sup (s := Finset.range 211) (f := F) (b := 210) (by decide)
  have h := heq 210
  omega
