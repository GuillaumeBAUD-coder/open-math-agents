import OMAReductions.R_Erdos436_erdos_436_variants_six_two_R1

/-!
Equation (13) in D. H. Lehmer, Emma Lehmer and W. H. Mills,
Pairs of consecutive power residues (1963), https://doi.org/10.4153/CJM-1963-020-4,
gives the prime labels for the lower bound. The finite check excludes earlier
pairs with two zero scores. W. H. Mills, Characters with preassigned values,
Theorem 3, https://doi.org/10.4153/CJM-1963-019-3, realizes the labels at
arbitrarily large primes. This applies without restrictions for sextic
characters because 6 is twice a prime congruent to 3 modulo 4.
-/

namespace OMA.R_Erdos436_erdos_436_variants_six_two_R1_H2_R1

/-- The labels in equation (13) give no consecutive zero scores before 202124. -/
def H1 : Prop :=
  let f (q : ℕ) : ZMod 6 := if q ∈ ([3, 43, 61] : List ℕ) then 0 else
    if q ∈ ([71, 101, 331, 733, 1423, 4877, 5413, 6043] : List ℕ) then 4 else 5
  ∀ n : ℕ, 1 ≤ n → n < 202124 →
    (n.primeFactorsList.map f).sum ≠ 0 ∨ ((n + 1).primeFactorsList.map f).sum ≠ 0

/-- Arbitrarily large primes simultaneously realize the prescribed labels. -/
def H2 : Prop :=
  let f (q : ℕ) : ZMod 6 := if q ∈ ([3, 43, 61] : List ℕ) then 0 else
    if q ∈ ([71, 101, 331, 733, 1423, 4877, 5413, 6043] : List ℕ) then 4 else 5
  ∀ B : ℕ, ∃ p > B, p.Prime ∧ ∀ n : ℕ, 1 ≤ n → n ≤ 202124 →
    (Erdos436.IsPowerResidue 6 p n ↔ (n.primeFactorsList.map f).sum = 0)

theorem main : H1 → H2 → OMA.R_Erdos436_erdos_436_variants_six_two_R1.H2 := by
  intro obstruction realization B
  obtain ⟨p, hpB, hp, hres⟩ := realization B
  refine ⟨p, hpB, hp, ?_⟩
  apply le_iInf₂
  rintro n ⟨hn, hr⟩
  have hn' : 202124 ≤ n := by
    by_contra! hlt
    have hz := (hres n hn hlt.le).1 (by simpa only [Nat.add_zero] using hr 0 (by decide))
    have hz' := (hres (n + 1) (by omega) (by omega)).1 (hr 1 (by decide))
    exact (obstruction n hn hlt).elim (fun h => h hz) (fun h => h hz')
  exact_mod_cast hn'

end OMA.R_Erdos436_erdos_436_variants_six_two_R1_H2_R1
