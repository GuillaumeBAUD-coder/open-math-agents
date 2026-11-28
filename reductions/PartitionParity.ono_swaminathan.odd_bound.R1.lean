import FormalConjectures.Paper.PartitionParity
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.ZMod.Basic

/-!
# The effective first odd term in a quadratic partition progression

Ono–Swaminathan, Parity of the partition function in quadratic progressions,
https://arxiv.org/abs/2509.09553v4. Proposition 7 identifies the coefficients
used here. The nonvanishing comes from Section 4.1, and the truncation bound
comes from the earlier theorem of Ono quoted as Theorem 8.
-/

namespace OMA.R_PartitionParity_ono_swaminathan_odd_bound_R1

open Finset Nat Polynomial NumberField
open scoped BigOperators

private theorem truncated_lambert_zero_iff (D B : ℕ) (a : ℕ → ZMod 2) :
    (∀ n ≤ B, (∑ m ∈ n.divisors,
      if m.Coprime 6 ∧ (n/m).Coprime D then a m else 0) = 0) ↔
      ∀ m ≤ B, m.Coprime 6 → a m = 0 := by
  constructor
  · intro hzero m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm hcop
      have hm0 : 0 < m := by
        by_contra! h
        have h' : m = 0 := by omega
        simp [h'] at hcop
      have hdiag : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl,hm0.ne'⟩
      have hterm : (∑ j ∈ m.divisors,
          if j.Coprime 6 ∧ (m/j).Coprime D then a j else 0) = a m := by
        rw [Finset.sum_eq_single m]
        · simp [hcop, Nat.div_self hm0]
        · intro j hj hne
          split_ifs with hjcop
          · have hjm : j ≤ m := Nat.le_of_dvd hm0 (Nat.dvd_of_mem_divisors hj)
            exact ih j (lt_of_le_of_ne hjm hne) (hjm.trans hm) hjcop.1
          · rfl
        · exact fun h => (h hdiag).elim
      exact hterm.symm.trans (hzero m hm)
  · intro hzero n hn
    apply Finset.sum_eq_zero
    intro m hm
    obtain ⟨hdiv,hn0⟩ := Nat.mem_divisors.mp hm
    split_ifs with hcop
    · exact hzero m ((Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdiv).trans hn) hcop.1
    · rfl

/-- Nonvanishing of the characteristic-two Lambert expansion. -/
def H1 : Prop := ∀ D : ℕ, 1 < D → Squarefree D → D % 24 = 23 →
    ∃ n : ℕ, (∑ m ∈ n.divisors,
      if m.Coprime 6 ∧ (n/m).Coprime D then
        (partitionNumber ((D*m^2+1)/24) : ZMod 2) else 0) ≠ 0

/-- The finite coefficient test for the normalized logarithmic differential. -/
def H2 : Prop := ∀ D : ℕ, 1 < D → Squarefree D → D % 24 = 23 →
    ∀ (_ : Fact (Irreducible (X^2 + C (D : ℚ)))),
    let B := 12 * classNumber (AdjoinRoot (X^2 + C (D : ℚ))) + 2
    let F (n : ℕ) := ∑ m ∈ n.divisors,
      if m.Coprime 6 ∧ (n/m).Coprime D then
        (partitionNumber ((D*m^2+1)/24) : ZMod 2) else 0
    (∀ n ≤ B, F n = 0) → ∀ n, F n = 0

theorem main : H1 → H2 → type_of% @PartitionParity.ono_swaminathan.odd_bound := by
  intro hgeometry hfinite D hD hsq hDmod
  let hK : Fact (Irreducible (X^2 + C (D : ℚ))) :=
    ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by omega))⟩
  let K := AdjoinRoot (X^2 + C (D : ℚ))
  let B := 12 * classNumber K + 2
  let a (m : ℕ) : ZMod 2 := (partitionNumber ((D*m^2+1)/24) : ZMod 2)
  change ∃ m : ℕ, m.Coprime 6 ∧ m ≤ B ∧ Odd (partitionNumber ((D*m^2+1)/24))
  by_contra! hnone
  have hzero : ∀ m ≤ B, m.Coprime 6 → a m = 0 := by
    intro m hm hc
    exact (Nat.not_odd_iff_even.mp (hnone m hc hm)).natCast_zmod_two
  have hbounded := (truncated_lambert_zero_iff D B a).2 hzero
  have hall := hfinite D hD hsq hDmod hK hbounded
  obtain ⟨n,hn⟩ := hgeometry D hD hsq hDmod
  exact hn (hall n)

end OMA.R_PartitionParity_ono_swaminathan_odd_bound_R1
