import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1

/-!
Write e for the exponent of 3. Split the task into controlling e, and controlling
one class of simple primes for each bounded e. A simple prime q congruent to
2 modulo 3 spends a factor of 3 through q+1 in the unitary divisor sum.
Such a q can divide p+1 for at most one other simple prime p, because q occurs
once on the opposite side of the balance equation. This bounds the number of
discarded simple primes by 2e. The fixed-rank finiteness theorem of Subbarao
and Warren, formalized in the first reduction, then bounds the exponent of 2.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R2

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (prod_eq_two_mul kernel_balance_one prime_dvd_three_pow facts)

def H1 : Prop :=
  ∃ E : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    (n.factorization 3 = 5 ∨ n.factorization 3 = 7 ∨ n.factorization 3 = 11 ∨
      n.factorization 3 = 13 ∨ n.factorization 3 = 19 ∨ 41 ≤ n.factorization 3) →
    (∀ d ∈ ({6,8,9,10,12,14,15,16,17,20,21,22,23,25,26,28,29,31,32,33,34,35,37,38,39} : Finset ℕ),
      n.factorization 3 % (2*d) ≠ d) →
    n.factorization 3 ≤ E

def H2 : Prop :=
  ∀ E : ℕ, ∃ K : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    (n.factorization 3 = 5 ∨ n.factorization 3 = 7 ∨ n.factorization 3 = 11 ∨
      n.factorization 3 = 13 ∨ n.factorization 3 = 19 ∨ 41 ≤ n.factorization 3) →
    (∀ d ∈ ({6,8,9,10,12,14,15,16,17,20,21,22,23,25,26,28,29,31,32,33,34,35,37,38,39} : Finset ℕ),
      n.factorization 3 % (2*d) ≠ d) →
    n.factorization 3 ≤ E →
    let P := (n.primeFactors.erase 2).filter (fun p => p ≠ 3)
    (P.filter (fun p => p % 3 = 1 ∧
      ∀ q ∈ P, q % 3 = 2 → ¬ q ∣ p+1)).card ≤ K

theorem count_charged {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2 ∧ p ≠ 3)
    (huniq : ∀ q ∈ P, ∀ p ∈ P, ∀ r ∈ P, q ∣ p+1 → q ∣ r+1 → p = r) :
    P.card ≤ 2 * (P.filter (fun q => q % 3 = 2)).card +
      (P.filter (fun p => p % 3 = 1 ∧ ∀ q ∈ P, q % 3 = 2 → ¬ q ∣ p+1)).card := by
  classical
  let B := P.filter (fun q => q % 3 = 2)
  let C := P.filter (fun p => p % 3 = 1 ∧ ∀ q ∈ P, q % 3 = 2 → ¬ q ∣ p+1)
  let T := (P \ B) \ C
  have hw : ∀ p ∈ T, ∃ q ∈ B, q ∣ p+1 := by
    intro p hp
    obtain ⟨hp', hnC⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpP, hnB⟩ := Finset.mem_sdiff.mp hp'
    have hne2 : p % 3 ≠ 2 := fun h => hnB (Finset.mem_filter.mpr ⟨hpP,h⟩)
    have hne0 : p % 3 ≠ 0 := by
      intro h0
      exact (hP p hpP).2.2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (hP p hpP).1).mp
        (Nat.dvd_of_mod_eq_zero h0)).symm
    have hr : p % 3 = 1 := by omega
    by_contra! hn
    exact hnC (Finset.mem_filter.mpr ⟨hpP,hr,fun q hq hq2 =>
      hn q (Finset.mem_filter.mpr ⟨hq,hq2⟩)⟩)
  let f (p : ℕ) : ℕ := if hp : p ∈ T then (hw p hp).choose else 0
  have hf (p : ℕ) (hp : p ∈ T) : f p ∈ B ∧ f p ∣ p+1 := by
    simpa [f, hp] using (hw p hp).choose_spec
  have hsub : T ⊆ P := (Finset.sdiff_subset).trans Finset.sdiff_subset
  have hcard : T.card ≤ B.card := by
    refine Finset.card_le_card_of_injOn f (fun p hp => (hf p hp).1) ?_
    intro p hp r hr hpr
    apply huniq (f p) (Finset.mem_filter.mp (hf p hp).1).1 p (hsub hp) r (hsub hr)
      (hf p hp).2
    exact hpr ▸ (hf r hr).2
  have hsub' : P ⊆ (B ∪ C) ∪ T := by
    intro p hp
    by_cases hb : p ∈ B
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hb)
    by_cases hc : p ∈ C
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hc)
    exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hp,hb⟩,hc⟩)
  have h1 := Finset.card_le_card hsub'
  have h2 := Finset.card_union_le (B ∪ C) T
  have h3 := Finset.card_union_le B C
  change P.card ≤ 2 * B.card + C.card
  omega

theorem prime_count_bound {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (u : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) :
    let P := (n.primeFactors.erase 2).filter (fun p => p ≠ 3)
    n.primeFactors.card ≤ 2 + 2*n.factorization 3 +
      (P.filter (fun p => p % 3 = 1 ∧ ∀ q ∈ P, q % 3 = 2 → ¬ q ∣ p+1)).card := by
  classical
  let P := (n.primeFactors.erase 2).filter (fun p => p ≠ 3)
  let B := P.filter (fun p => p % 3 = 2)
  have hP {p : ℕ} (hp : p ∈ P) : p ∈ n.primeFactors ∧ p ≠ 2 ∧ p ≠ 3 := by
    have hh := Finset.mem_filter.mp hp
    exact ⟨(Finset.mem_erase.mp hh.1).2, (Finset.mem_erase.mp hh.1).1, hh.2⟩
  have hs : ∀ p ∈ n.primeFactors, p ≠ 2 → p ≠ 3 → n.factorization p = 1 := by
    intro p hp h2 h3
    have prime := Nat.prime_of_mem_primeFactors hp
    have pos := prime.factorization_pos_of_dvd h.2.ne' (Nat.dvd_of_mem_primeFactors hp)
    have hlo : ¬ 2 ≤ n.factorization p := fun hh => h3 ((u p).mp ⟨prime, h2,
      (prime.pow_dvd_iff_le_factorization h.2.ne').mpr hh⟩)
    omega
  have hbd : 3^B.card ∣ 2*n := by
    rw [← prod_eq_two_mul h, ← Finset.prod_const]
    refine (Finset.prod_dvd_prod_of_dvd _ _ ?_).trans
      (Finset.prod_dvd_prod_of_subset _ _ _ (fun p hp => (hP (Finset.mem_filter.mp hp).1).1))
    intro p hp
    have hpr := hP (Finset.mem_filter.mp hp).1
    rw [hs p hpr.1 hpr.2.1 hpr.2.2, pow_one]
    have hmod := (Finset.mem_filter.mp hp).2
    exact Nat.dvd_of_mod_eq_zero (by omega)
  have hB := (Nat.prime_three.pow_dvd_iff_le_factorization (by have := h.2; omega : 2*n ≠ 0)).mp hbd
  rw [Nat.factorization_mul (by decide) h.2.ne', Finsupp.add_apply] at hB
  have h23 : Nat.factorization 2 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  rw [h23, zero_add] at hB
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three,
    dvd_trans (by decide : 3 ∣ 3^2) ((u 3).mpr rfl).2.2, h.2.ne'⟩
  obtain ⟨hpprime,E⟩ := kernel_balance_one h h3pf (by decide) hs
  have hf := (facts hpprime prime_dvd_three_pow E).2.2.1
  have hT := count_charged (P := P) (fun p hp => ⟨Nat.prime_of_mem_primeFactors (hP hp).1,(hP hp).2⟩) (by
    intro q hq p hp r hr
    exact hf q (Nat.prime_of_mem_primeFactors (hP hq).1) (hP hq).2.1
      (by simpa using (hP hq).2.2) p (by simpa [P] using hp) r (by simpa [P] using hr))
  have hsub : n.primeFactors ⊆ insert 2 (insert 3 P) := by
    intro p hp
    by_cases h2 : p = 2
    · simp [h2]
    by_cases h3 : p = 3
    · simp [h3]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨h2,hp⟩,h3⟩))
  have ht := Finset.card_le_card hsub
  have ht2 := Finset.card_insert_le 2 (insert 3 P)
  have ht3 := Finset.card_insert_le 3 P
  change B.card ≤ n.factorization 3 at hB
  change n.primeFactors.card ≤ 2 + 2*n.factorization 3 +
    (P.filter (fun p => p % 3 = 1 ∧ ∀ q ∈ P, q % 3 = 2 → ¬ q ∣ p+1)).card
  dsimp only [B] at hB
  omega

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.H1 := by
  rintro ⟨E,hE⟩ hK
  obtain ⟨K,hk⟩ := hK E
  let B := 2 + 2*E + K
  have hf := (Set.finite_Iic B).biUnion fun k _ =>
    OMA.R_Erdos1052_erdos_1052_R1.finite_card_primeFactors k
  obtain ⟨A,hA⟩ := (hf.image (padicValNat 2)).bddAbove
  refine ⟨A,fun n h u hs hd => ?_⟩
  apply hA
  refine ⟨n,Set.mem_biUnion (x := n.primeFactors.card) ?_ ⟨h,rfl⟩,rfl⟩
  have he := hE n h u hs hd
  have hc := prime_count_bound h u
  have hh := hk n h u hs hd he
  change n.primeFactors.card ≤ 2+2*E+K
  dsimp only at hh hc
  omega

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R2
