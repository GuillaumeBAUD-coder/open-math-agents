import OMAStatements.S_oeis_a239293
import Mathlib

namespace OMA.P_oeis_a239293

open OMA.S_oeis_a239293

theorem neg_one (n : ℕ) : ((n : ℕ) : ZMod (n + 1)) = -1 := by
  have h : ((n + 1 : ℕ) : ZMod (n + 1)) = 0 := ZMod.natCast_self _
  push_cast at h
  exact eq_neg_of_add_eq_zero_left h

theorem modeq_iff (n : ℕ) :
    n ^ (n + 1) ≡ n [MOD n + 1] ↔ ((-1 : ZMod (n + 1)) ^ (n + 1) = -1) := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [neg_one]

theorem mem_of (n : ℕ) (ho : Odd (n + 1)) (hc : IsComposite (n + 1)) :
    n + 1 ∈ {c : ℕ | n < c ∧ IsComposite c ∧ n ^ c ≡ n [MOD c]} := by
  refine ⟨by omega, hc, ?_⟩
  rw [modeq_iff]
  exact ho.neg_one_pow

end OMA.P_oeis_a239293

theorem OMA.solution : type_of% @OMA.S_oeis_a239293.main := by
  intro n hn
  constructor
  · intro h
    have hne : {c : ℕ | n < c ∧ OMA.S_oeis_a239293.IsComposite c ∧ n ^ c ≡ n [MOD c]}.Nonempty := by
      by_contra hE
      rw [Set.not_nonempty_iff_eq_empty] at hE
      unfold OMA.S_oeis_a239293.a at h
      rw [hE, Nat.sInf_empty] at h
      omega
    have hm := Nat.sInf_mem hne
    unfold OMA.S_oeis_a239293.a at h
    rw [h] at hm
    obtain ⟨-, hc, hmod⟩ := hm
    refine ⟨?_, hc⟩
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    rw [OMA.P_oeis_a239293.modeq_iff, hev.neg_one_pow] at hmod
    have h2 : ((2 : ℕ) : ZMod (n + 1)) = 0 := by
      push_cast
      linear_combination hmod
    rw [ZMod.natCast_eq_zero_iff] at h2
    have hle := Nat.le_of_dvd (by norm_num) h2
    obtain ⟨h1, hp⟩ := hc
    have : n + 1 = 2 := by omega
    rw [this] at hp
    exact hp Nat.prime_two
  · rintro ⟨ho, hc⟩
    have hmem := OMA.P_oeis_a239293.mem_of n ho hc
    have h1 := Nat.sInf_le hmem
    have h2 := (Nat.sInf_mem ⟨_, hmem⟩).1
    unfold OMA.S_oeis_a239293.a
    omega
