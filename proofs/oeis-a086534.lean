import OMAStatements.S_oeis_a086534
import Mathlib

/-!
# A086534: for every `n ≥ 1` some prime is sandwiched between multiples of `n`-th powers

The finiteness statement is false: every `n ≥ 1` belongs to the set.  By the Chinese remainder
theorem there is `k` with `k ≡ 1 (mod 2 ^ n)` and `k ≡ -1 (mod 3 ^ n)`; such a `k` is coprime to
`2 ^ n * 3 ^ n`, so Dirichlet's theorem gives a prime `p ≡ k (mod 2 ^ n * 3 ^ n)`.
Then `2 ^ n ∣ p - 1` and `3 ^ n ∣ p + 1`.
-/

namespace OMA.S_oeis_a086534

/-- Every `n ≥ 1` admits a sandwiched prime. -/
lemma exists_sandwiched (n : ℕ) (hn : 1 ≤ n) : ∃ p : ℕ, Sandwiched n p := by
  have h3 : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hcop : Nat.Coprime (2 ^ n) (3 ^ n) := Nat.Coprime.pow n n (by decide)
  -- Chinese remainder theorem
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop 1 (3 ^ n - 1)
  -- `k` is coprime to the modulus
  have c1 : Nat.Coprime k (2 ^ n) := by
    rw [Nat.Coprime, hk1.gcd_eq]
    exact Nat.gcd_one_left _
  have c2 : Nat.Coprime k (3 ^ n) := by
    rw [Nat.Coprime, hk2.gcd_eq]
    exact (Nat.coprime_self_sub_left h3).mpr (Nat.gcd_one_left _)
  have : NeZero (2 ^ n * 3 ^ n) := ⟨by positivity⟩
  have hunit : IsUnit ((k : ℕ) : ZMod (2 ^ n * 3 ^ n)) :=
    (ZMod.isUnit_iff_coprime k _).mpr (Nat.Coprime.mul_right c1 c2)
  -- Dirichlet's theorem
  obtain ⟨p, -, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit 0
  have hpk : p ≡ k [MOD 2 ^ n * 3 ^ n] := (ZMod.natCast_eq_natCast_iff p k _).mp hmod
  have hp1 : p ≡ 1 [MOD 2 ^ n] := (Nat.ModEq.of_mul_right _ hpk).trans hk1
  have hp2 : p ≡ 3 ^ n - 1 [MOD 3 ^ n] := (Nat.ModEq.of_mul_left _ hpk).trans hk2
  refine ⟨p, hp, ⟨2, le_rfl, ?_⟩, ⟨3, by norm_num, ?_⟩⟩
  · exact (Nat.modEq_iff_dvd' hp.one_le).mp hp1.symm
  · have h := hp2.add_right 1
    rw [Nat.sub_add_cancel h3] at h
    exact (Nat.modEq_zero_iff_dvd).mp (h.trans ((Nat.modEq_zero_iff_dvd).mpr dvd_rfl))

end OMA.S_oeis_a086534

open OMA.S_oeis_a086534 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a086534.main) := by
  intro hfin
  have hsub : Set.Ici 1 ⊆ {n : ℕ | 1 ≤ n ∧ ∃ p : ℕ, Sandwiched n p} :=
    fun n hn => ⟨hn, exists_sandwiched n hn⟩
  exact (Set.Ici_infinite 1).mono hsub hfin
