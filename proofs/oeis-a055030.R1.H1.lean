import OMAReductions.R_oeis_a055030_R1
import Mathlib

open Finset

private theorem sum_blocks (p e k : ℕ) :
    (∑ i ∈ range (p * k), (i : ZMod p) ^ e) =
      k • (∑ i ∈ range p, (i : ZMod p) ^ e) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    have shifted : (∑ i ∈ range p, ((p * k + i : ℕ) : ZMod p) ^ e) =
        ∑ i ∈ range p, (i : ZMod p) ^ e := by
      apply sum_congr rfl
      intro i _
      simp [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self]
    rw [shifted, succ_nsmul]

theorem OMA.solution : OMA.R_oeis_a055030_R1.H1 := by
  intro n hn _ hsq hdiv
  rw [Nat.squarefree_iff_prime_squarefree] at hsq
  push Not at hsq
  obtain ⟨p, hp, hpp⟩ := hsq
  letI : Fact p.Prime := ⟨(Nat.irreducible_iff_nat_prime p).mp hp⟩
  obtain ⟨q, hq⟩ := hpp
  have hpdiv : p ∣ n := ⟨p * q, by simpa [Nat.mul_assoc] using hq⟩
  have htotal : (∑ i ∈ range n, (i : ZMod p) ^ (n - 1)) = 0 := by
    rw [show n = p * (p * q) by simpa [Nat.mul_assoc] using hq, sum_blocks]
    simp [nsmul_eq_mul, Nat.cast_mul, ZMod.natCast_self]
  have hset : range n = insert 0 (Icc 1 (n - 1)) := by
    ext j
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hset, sum_insert (by simp), Nat.cast_zero, zero_pow (by omega), zero_add] at htotal
  have hbad := (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_trans hpdiv hdiv)
  push_cast at hbad
  rw [htotal, zero_add] at hbad
  exact one_ne_zero hbad