import FormalConjectures.ErdosProblems.«436»
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Topology.Order.LiminfLimsup

/-!
Brillhart, Lehmer and Lehmer reduce the upper bound to the case-vector
search and give a maximal vector in Table II. The lower bound uses
verification of this vector and its realization at arbitrarily large
primes. Taking exponents in the cyclic unit group transfers a
zero case-vector weight to a seventh-power residue.
-/

-- Credit: @dk8827

open Filter Finset
open scoped BigOperators

namespace OMA.R_Erdos436_erdos_436_variants_seven_two_R1

private theorem transfer (p : ℕ) (hp : p.Prime) :
    ∃ f : ℕ → ZMod 7, ∀ n : ℕ, 0 < n → n < p →
      (∑ q ∈ n.primeFactors, (n.factorization q : ZMod 7) * f q) = 0 →
      Erdos436.IsPowerResidue 7 p n := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have cast_ne (n : ℕ) (hn : 0 < n) (hpn : n < p) : (n : ZMod p) ≠ 0 := by
    intro he
    exact (not_le_of_gt hpn) (Nat.le_of_dvd hn ((ZMod.natCast_eq_zero_iff n p).1 he))
  have hnth (q : ℕ) : ∃ e : ℕ, 0 < q → q < p → (g : ZMod p) ^ e = (q : ZMod p) := by
    by_cases hq : 0 < q ∧ q < p
    · let u : (ZMod p)ˣ := Units.mk0 (q : ZMod p) (cast_ne q hq.1 hq.2)
      obtain ⟨e, he⟩ := (mem_powers_iff_mem_zpowers.2 (hg u) : u ∈ Submonoid.powers g)
      refine ⟨e, fun _ _ => ?_⟩
      simpa [u] using congrArg (fun a : (ZMod p)ˣ => (a : ZMod p)) he
    · exact ⟨0, fun hq₀ hqp => (hq ⟨hq₀, hqp⟩).elim⟩
  choose e he using hnth
  refine ⟨fun q => (e q : ZMod 7), fun n hn hnp hz => ?_⟩
  let E : ℕ := ∑ q ∈ n.primeFactors, e q * n.factorization q
  have hE : (E : ZMod 7) = 0 := by
    simpa only [E, Nat.cast_sum, Nat.cast_mul, mul_comm] using hz
  have hexp : (g : ZMod p) ^ E = (n : ZMod p) := by
    rw [← prod_pow_eq_pow_sum]
    calc
      _ = ∏ q ∈ n.primeFactors, (q : ZMod p) ^ n.factorization q := by
        apply prod_congr rfl
        intro q hq
        rw [pow_mul, he q (Nat.prime_of_mem_primeFactors hq).pos
          ((Nat.le_of_mem_primeFactors hq).trans_lt hnp)]
      _ = _ := by
        have hs := congrArg (fun m : ℕ => (m : ZMod p))
          (Nat.prod_primeFactors_pow_factorization (Nat.ne_of_gt hn)).symm
        simpa only [Nat.cast_prod, Nat.cast_pow] using hs
  obtain ⟨j, hj⟩ := (ZMod.natCast_eq_zero_iff E 7).1 hE
  refine ⟨cast_ne n hn hnp, (g : ZMod p) ^ j, ?_⟩
  rw [← pow_mul, mul_comm j, ← hj, hexp]

/-- The case-vector search for the upper bound. -/
def H1 : Prop :=
  ∀ f : ℕ → ZMod 7, ∃ n : ℕ, 1 ≤ n ∧ n ≤ 1649375 ∧
    (∑ q ∈ n.primeFactors, (n.factorization q : ZMod 7) * f q) = 0 ∧
    (∑ q ∈ (n + 1).primeFactors, ((n + 1).factorization q : ZMod 7) * f q) = 0

/-- The vector in Table II excludes every earlier pair. -/
def H2 : Prop :=
  let f (q : ℕ) : ZMod 7 := if q ∈ ([3, 41] : List ℕ) then 0 else
    if q ∈ ([79, 137, 197, 233, 269, 277, 463, 467, 797, 1709, 2647, 2903, 15791] : List ℕ)
    then 2 else 1
  ∀ n : ℕ, 1 ≤ n → n < 1649375 →
    (∑ q ∈ n.primeFactors, (n.factorization q : ZMod 7) * f q) ≠ 0 ∨
    (∑ q ∈ (n + 1).primeFactors, ((n + 1).factorization q : ZMod 7) * f q) ≠ 0

/-- The maximal vector is realized at an unbounded set of primes. -/
def H3 : Prop :=
  let f (q : ℕ) : ZMod 7 := if q ∈ ([3, 41] : List ℕ) then 0 else
    if q ∈ ([79, 137, 197, 233, 269, 277, 463, 467, 797, 1709, 2647, 2903, 15791] : List ℕ)
    then 2 else 1
  ∀ X : ℕ, ∃ p : ℕ, X ≤ p ∧ p.Prime ∧ ∀ n : ℕ, 1 ≤ n → n ≤ 1649375 →
    (Erdos436.IsPowerResidue 7 p n ↔
      (∑ q ∈ n.primeFactors, (n.factorization q : ZMod 7) * f q) = 0)

theorem main : H1 → H2 → H3 → type_of% @Erdos436.erdos_436.variants.seven_two := by
  classical
  intro upper maximal realization
  change limsup (Erdos436.r 7 2) (atTop ⊓ 𝓟 {p : ℕ | p.Prime}) = (1649375 : ℕ∞)
  apply le_antisymm
  · apply limsup_le_of_le (by isBoundedDefault)
    apply eventually_inf_principal.2
    filter_upwards [eventually_ge_atTop (1649377 : ℕ)] with p hpL hp
    obtain ⟨f, hf⟩ := transfer p hp
    obtain ⟨n, hn, hnL, h₁, h₂⟩ := upper f
    have hrun : 1 ≤ n ∧ ∀ i < 2, Erdos436.IsPowerResidue 7 p (n + i) := by
      refine ⟨hn, fun i hi => ?_⟩
      have hi' : i = 0 ∨ i = 1 := by omega
      rcases hi' with rfl | rfl
      · simpa only [Nat.add_zero] using hf n (by omega) (by omega) h₁
      · exact hf (n + 1) (by omega) (by omega) h₂
    exact (iInf₂_le n hrun).trans (by exact_mod_cast hnL)
  · apply le_limsup_of_frequently_le'
    rw [frequently_inf_principal, frequently_atTop]
    intro X
    obtain ⟨p, hpX, hp, hres⟩ := realization X
    refine ⟨p, hpX, hp, ?_⟩
    apply le_iInf₂
    rintro n ⟨hn, hh⟩
    have hL : 1649375 ≤ n := by
      by_contra! hlt
      have h₁ := (hres n hn hlt.le).1 (hh 0 (by omega))
      have h₂ := (hres (n + 1) (by omega) (by omega)).1 (hh 1 (by omega))
      exact (maximal n hn hlt).elim (fun h => h h₁) (fun h => h h₂)
    exact_mod_cast hL

end OMA.R_Erdos436_erdos_436_variants_seven_two_R1
