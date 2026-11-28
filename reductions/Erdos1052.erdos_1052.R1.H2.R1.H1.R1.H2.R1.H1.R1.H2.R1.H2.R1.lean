import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H2_R1

/-! Reduction of the `d ≡ 3 (mod 8)` step: a uniform bound on `a = v₂(n)` follows from
(H1) a bound on unitary perfect numbers in terms of their number of distinct prime factors,
a known theorem (it follows from T. Goto, Rocky Mountain J. Math. 37 (2007), who shows
`n < 2^(2^k)` for a unitary perfect `n` with `k` distinct prime factors), and
(H2) a uniform bound on the number of distinct prime factors in this branch.
Reusable tools for H2: https://github.com/Jwolf52/open-math-agents/blob/d199e5b5baa25c3df0373b3c8002dbcaf40cca16/research/erdos1052-tools/Erdos1052Tools.lean -/

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H1.R1.H2.R1.H2.R1 of step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H1.R1.H2.R1.H2
-- Credit: @Jwolf52

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H2_R1_H2_R1

/-- Known (Goto 2007, quantitative): unitary perfect numbers with a given number of distinct
prime factors are bounded. -/
def H1 : Prop :=
  ∃ F : ℕ → ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → n ≤ F n.primeFactors.card

/-- Open core: in this branch the number of distinct prime factors is uniformly bounded. -/
def H2 : Prop :=
  ∃ K : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 2 →
    43 ≤ padicValNat 2 n → padicValNat 2 n % 4 = 2 →
    3 ∣ n →
    (∀ d : ℕ, d.Prime → d ≠ 2 → d ∣ padicValNat 2 n → 971 ≤ d ∧ (d % 8 = 1 ∨ d % 8 = 3)) →
    (∃ d : ℕ, d.Prime ∧ d ≠ 2 ∧ d ∣ padicValNat 2 n ∧ d % 8 = 3) →
    n.primeFactors.card ≤ K

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H2_R1.H2 := by
  rintro ⟨F, hF⟩ ⟨K, hK⟩
  refine ⟨∑ k ∈ Finset.range (K + 1), F k, fun n h hS he h43 hm h3 hd hex => ?_⟩
  have hc := hK n h hS he h43 hm h3 hd hex
  have hn := hF n h
  have hle : F n.primeFactors.card ≤ ∑ k ∈ Finset.range (K + 1), F k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  have h2a : 2 ^ padicValNat 2 n ≤ n := Nat.le_of_dvd h.2 pow_padicValNat_dvd
  have hlt : padicValNat 2 n < 2 ^ padicValNat 2 n := Nat.lt_two_pow_self
  omega

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H2_R1_H2_R1
