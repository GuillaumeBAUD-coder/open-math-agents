import FormalConjectures.ErdosProblems.«413»

/-! Check the short window near the barrier and a finite cover of all larger candidates. -/

open ArithmeticFunction
open scoped Omega

lemma OMA.two_pow_cardFactors_le (m : ℕ) (hm : m ≠ 0) : (2 : ℕ) ^ Ω m ≤ m := by
  rw [cardFactors_apply]
  calc
    _ ≤ m.primeFactorsList.prod :=
      List.pow_card_le_prod _ _ fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le
    _ = m := Nat.prod_primeFactorsList hm

lemma OMA.small_cardFactors (m : ℕ) (hm : m < 99824) : Ω m ≤ 16 := by
  rcases eq_or_ne m 0 with rfl | hne
  · simp
  · by_contra! h
    have hpow : (2 : ℕ) ^ 17 ≤ (2 : ℕ) ^ Ω m :=
      pow_le_pow_right₀ (by decide) (by omega)
    have hlow : 131072 ≤ m := hpow.trans (OMA.two_pow_cardFactors_le m hne)
    omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma OMA.barrier_near :
    ∀ d : Fin 16, 99824 + d.val + Ω (99824 + d.val) ≤ 99840 := by
  decide +kernel

def OMA.barrierWitnesses : Finset (ℕ × ℕ) := {
  (99840, 12), (99850, 4), (99852, 5), (99856, 6),
  (99860, 4), (99862, 4), (99864, 7), (99870, 4),
  (99873, 7), (99879, 4), (99882, 5), (99885, 3),
  (99887, 2), (99888, 6), (99892, 5), (99896, 4),
  (99897, 4), (99900, 8), (99904, 8), (99910, 4),
  (99912, 6), (99916, 3), (99918, 6), (99920, 6),
  (99924, 5), (99928, 4), (99930, 4), (99932, 5),
  (99936, 8), (99940, 5), (99944, 6), (99948, 4),
  (99950, 4), (99952, 5), (99954, 6), (99958, 4),
  (99960, 8), (99966, 3), (99968, 9), (99975, 5),
  (99978, 4), (99981, 6), (99984, 6), (99988, 4),
  (99990, 6), (99994, 4), (99996, 5)}

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma OMA.barrier_witnesses_valid : ∀ p ∈ OMA.barrierWitnesses, p.2 ≤ Ω p.1 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma OMA.barrier_witnesses_cover :
    ∀ d : Fin 159, ∃ p ∈ OMA.barrierWitnesses,
      p.1 < 99841 + d.val ∧ 99841 + d.val < p.1 + p.2 := by
  decide +kernel

theorem OMA.solution : type_of% @Erdos413.erdos_413.variants.bigOmega_largest_barrier_lt_100k := by
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · intro m hm
    change (m : ℝ) + (Ω m : ℝ) ≤ 99840
    suffices m + Ω m ≤ 99840 by exact_mod_cast this
    by_cases h : m < 99824
    · have hb := OMA.small_cardFactors m h
      omega
    · let d : Fin 16 := ⟨m - 99824, by omega⟩
      have hd : 99824 + d.val = m := by dsimp [d]; omega
      simpa only [hd] using OMA.barrier_near d
  · intro n hn
    obtain ⟨hsmall, hbar⟩ := hn
    by_contra! hbig
    have hnlt : n < 100000 := hsmall
    let d : Fin 159 := ⟨n - 99841, by omega⟩
    have hd : 99841 + d.val = n := by dsimp [d]; omega
    obtain ⟨p, hp, hpl, hpu⟩ := OMA.barrier_witnesses_cover d
    rw [hd] at hpl hpu
    have hreal : (p.1 : ℝ) + (Ω p.1 : ℝ) ≤ (n : ℝ) := hbar p.1 hpl
    have hbound : p.1 + Ω p.1 ≤ n := by exact_mod_cast hreal
    have hvalid := OMA.barrier_witnesses_valid p hp
    omega