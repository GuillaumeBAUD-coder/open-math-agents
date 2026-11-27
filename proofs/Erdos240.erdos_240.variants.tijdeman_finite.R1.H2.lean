import OMAReductions.R_Erdos240_erdos_240_variants_tijdeman_finite_R1
import Mathlib

/-! Elementary structure of the enumeration of P-smooth numbers.

The set of P-smooth numbers contains every power of a prime of P, so it is infinite; hence
its enumeration by Nat.nth is strictly increasing and takes values in the set. For p in P,
the number p times a P i is again P-smooth and larger than a P i, so it is enumerated at an
index larger than i, which bounds a P (i + 1).
-/

namespace O1E240H2

theorem pow_mem {P : Set ℕ} {p : ℕ} (hp : p ∈ P) (hpp : p.Prime) (k : ℕ) :
    p ^ k ∈ Erdos675.composedOf P := by
  refine ⟨pow_pos hpp.pos k, fun q hq hqd => ?_⟩
  have := (Nat.prime_dvd_prime_iff_eq hq hpp).1 (hq.dvd_of_dvd_pow hqd)
  rw [this]; exact hp

theorem mul_mem {P : Set ℕ} {p m : ℕ} (hp : p ∈ P) (hpp : p.Prime)
    (hm : m ∈ Erdos675.composedOf P) : p * m ∈ Erdos675.composedOf P := by
  refine ⟨Nat.mul_pos hpp.pos hm.1, fun q hq hqd => ?_⟩
  rcases (Nat.Prime.dvd_mul hq).1 hqd with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hq hpp).1 h]; exact hp
  · exact hm.2 q hq h

theorem infinite_of {P : Set ℕ} {p : ℕ} (hp : p ∈ P) (hpp : p.Prime) :
    (Set.ofPred (· ∈ Erdos675.composedOf P)).Infinite := by
  have hinj : Function.Injective (fun k : ℕ => p ^ k) := Nat.pow_right_injective hpp.two_le
  refine Set.infinite_of_injective_forall_mem hinj (fun k => ?_)
  exact pow_mem hp hpp k

end O1E240H2

open O1E240H2 in
theorem OMA.solution : OMA.R_Erdos240_erdos_240_variants_tijdeman_finite_R1.H2 := by
  classical
  intro P _ hne hsub
  obtain ⟨p₀, hp₀⟩ := hne
  have hinf := infinite_of hp₀ (hsub hp₀)
  have hmem : ∀ i, Erdos240.a P i ∈ Erdos675.composedOf P := fun i =>
    Nat.nth_mem_of_infinite hinf i
  refine ⟨Nat.nth_strictMono hinf, hmem, fun p hp i => ?_⟩
  have hpp : p.Prime := hsub hp
  have hpm := mul_mem hp hpp (hmem i)
  have hpos := (hmem i).1
  obtain ⟨k, hk⟩ : ∃ k, Nat.nth (· ∈ Erdos675.composedOf P) k = p * Erdos240.a P i :=
    ⟨_, Nat.nth_count hpm⟩
  have hlt : Erdos240.a P i < Nat.nth (· ∈ Erdos675.composedOf P) k := by
    rw [hk]
    have := hpp.two_le
    nlinarith
  have hik : i < k := (Nat.nth_lt_nth hinf).1 hlt
  have : Erdos240.a P (i + 1) ≤ Nat.nth (· ∈ Erdos675.composedOf P) k :=
    (Nat.nth_le_nth hinf).2 hik
  rw [hk] at this
  exact this
