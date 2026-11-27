import FormalConjectures.ErdosProblems.«427»

namespace OMA.R_Erdos427_erdos_427_variants_shiu_R1

/-- Arbitrarily far out, the primes in a finite interval have a sufficiently
large excess of the desired residue class over the other residue classes. -/
def H1 : Prop :=
  ∀ (k a q N : ℕ), 1 ≤ k → 1 ≤ q → a.gcd q = 1 →
    let good : ℕ → Bool := fun i => decide (Nat.nth Nat.Prime i ≡ a [MOD q])
    ∃ l r : ℕ, N < l ∧
      (k - 1) * (((Finset.Ico l r).filter (fun i => good i = false)).card + 1) <
        ((Finset.Ico l r).filter (fun i => good i = true)).card

/-- A finite binary string with few separating zeros contains a long run of ones. -/
def H2 : Prop :=
  ∀ (good : ℕ → Bool) (l r k : ℕ), 1 ≤ k →
    (k - 1) * (((Finset.Ico l r).filter (fun i => good i = false)).card + 1) <
        ((Finset.Ico l r).filter (fun i => good i = true)).card →
    ∃ m : ℕ, l ≤ m ∧ m + k ≤ r ∧ ∀ i ∈ Finset.Ico m (m + k), good i = true

theorem main : H1 → H2 → type_of% @Erdos427.erdos_427.variants.shiu := by
  intro hdensity hrun k a q hk hq hcop
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  let good : ℕ → Bool := fun i => decide (Nat.nth Nat.Prime i ≡ a [MOD q])
  obtain ⟨l, r, hl, h⟩ := hdensity k a q N hk hq hcop
  obtain ⟨m, hm, _, hmrun⟩ := hrun good l r k hk h
  refine ⟨m, ?_, lt_of_lt_of_le hl hm⟩
  intro p hp
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  exact of_decide_eq_true (hmrun i hi)

end OMA.R_Erdos427_erdos_427_variants_shiu_R1
