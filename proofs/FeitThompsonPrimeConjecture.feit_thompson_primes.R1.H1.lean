import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1
import Mathlib

/-! H1: if q % p = 1, then p divides N = sum of q ^ i (i < p), but M = sum of p ^ i (i < q) is 1 mod p. -/

namespace OMA.FeitThompsonH1

lemma cast_one_of_mod {n m : ℕ} (hm : 2 ≤ m) (h : n % m = 1) : (n : ZMod m) = 1 := by
  rw [show (1 : ZMod m) = ((1 : ℕ) : ZMod m) by simp, ZMod.natCast_eq_natCast_iff', h,
    Nat.one_mod_eq_one.mpr (by omega)]

end OMA.FeitThompsonH1

open OMA.FeitThompsonH1 in
theorem OMA.solution : OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1.H1 := by
  intro p q hp hq hpq hmod hdvd
  rw [← Nat.geomSum_eq hq.two_le, ← Nat.geomSum_eq hp.two_le] at hdvd
  have hq1 : (q : ZMod p) = 1 := cast_one_of_mod hp.two_le hmod
  have hN : ((∑ k ∈ Finset.range p, q ^ k : ℕ) : ZMod p) = 0 := by
    push_cast; simp [hq1]
  have hM : ((∑ k ∈ Finset.range q, p ^ k : ℕ) : ZMod p) = 1 := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by have := hq.two_le; omega⟩
    push_cast
    rw [Finset.sum_range_succ']
    simp
  obtain ⟨c, hc⟩ := hdvd
  have hc' := congrArg (Nat.cast : ℕ → ZMod p) hc
  rw [Nat.cast_mul, hM, hN, zero_mul] at hc'
  have := Fact.mk hp
  exact one_ne_zero hc'
