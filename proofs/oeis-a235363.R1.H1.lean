import OMAReductions.R_oeis_a235363_R1
import Mathlib

theorem OMA.aux (p e : ℕ) (M : ℕ) :
    (∑ k ∈ Finset.range (p * M), ((k : ℕ) : ZMod p) ^ e) =
      (M : ZMod p) * ∑ j ∈ Finset.range p, ((j : ℕ) : ZMod p) ^ e := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have h : ∀ x : ℕ, (((p * M + x : ℕ)) : ZMod p) = (x : ZMod p) := by
      intro x; push_cast; simp
    simp only [h]
    push_cast; ring

theorem OMA.giuga (N e : ℕ) (he : 1 ≤ e) (hN : 1 ≤ N) (hsq : ¬ Squarefree N) :
    ¬ N ∣ 1 + ∑ k ∈ Finset.Icc 1 (N - 1), k ^ e := by
  rw [Nat.squarefree_iff_prime_squarefree] at hsq
  push_neg at hsq
  obtain ⟨p, hp, m, hm⟩ := hsq
  intro hdiv
  haveI := Fact.mk hp
  have hpN : p ∣ N := ⟨p * m, by rw [hm, mul_assoc]⟩
  have h1 : p ∣ 1 + ∑ k ∈ Finset.Icc 1 (N - 1), k ^ e := hpN.trans hdiv
  have h2 : ∑ k ∈ Finset.Icc 1 (N - 1), k ^ e = ∑ k ∈ Finset.range N, k ^ e := by
    have h : Finset.range N = insert 0 (Finset.Icc 1 (N - 1)) := by
      ext x; simp; omega
    rw [h, Finset.sum_insert (by simp), zero_pow (by omega), zero_add]
  rw [h2] at h1
  have key : ((∑ k ∈ Finset.range N, k ^ e : ℕ) : ZMod p) = 0 := by
    rw [hm, mul_assoc]; push_cast; rw [OMA.aux]; push_cast; simp
  have h3 := (ZMod.natCast_eq_zero_iff _ p).2 h1
  rw [Nat.cast_add, key] at h3
  simp at h3

theorem OMA.solution : OMA.R_oeis_a235363_R1.H1 := by
  intro n hn _ hsq h
  have := OMA.giuga (2 * n + 1) (2 * n) (by omega) (by omega) hsq
  simp only [Nat.add_sub_cancel] at this
  exact this (Nat.dvd_of_mod_eq_zero h)
