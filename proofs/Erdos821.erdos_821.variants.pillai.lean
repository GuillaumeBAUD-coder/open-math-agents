import FormalConjectures.ErdosProblems.«821»

-- Problem: Erdős Problem 821 — pillai
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/821.lean:68 (declaration Erdos821.erdos_821.variants.pillai)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA821

open Finset

/-- Fibers of the totient function over a positive value are finite. -/
lemma fiber_finite (n : ℕ) (hn : 0 < n) : {m : ℕ | Nat.totient m = n}.Finite := by
  apply Set.Finite.subset (Set.finite_Iic (n * ∏ i ∈ Finset.Icc 1 (n + 1), i))
  intro m hm
  simp only [Set.mem_ofPred_eq] at hm
  simp only [Set.mem_Iic]
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
    omega
  have key := Nat.totient_mul_prod_primeFactors m
  have hsub : m.primeFactors ⊆ Finset.Icc 1 (n + 1) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have h1 : Nat.totient p ∣ Nat.totient m := Nat.totient_dvd_of_dvd hpd
    rw [Nat.totient_prime hpp, hm] at h1
    have h2 := Nat.le_of_dvd hn h1
    have := hpp.two_le
    simp only [Finset.mem_Icc]
    omega
  have h1 : ∏ p ∈ m.primeFactors, p ≤ ∏ i ∈ Finset.Icc 1 (n + 1), i :=
    Finset.prod_le_prod_of_subset_of_one_le' hsub (fun i hi _ => by
      simp only [Finset.mem_Icc] at hi; omega)
  have h2 : 1 ≤ ∏ p ∈ m.primeFactors, (p - 1) := by
    apply Finset.one_le_prod'
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  rw [hm] at key
  calc m ≤ m * ∏ p ∈ m.primeFactors, (p - 1) := Nat.le_mul_of_pos_right m h2
    _ = n * ∏ p ∈ m.primeFactors, p := key.symm
    _ ≤ n * ∏ i ∈ Finset.Icc 1 (n + 1), i := Nat.mul_le_mul_left n h1

/-- Totient of a product of distinct primes. -/
lemma totient_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Nat.totient (∏ p ∈ S, p) = ∏ p ∈ S, (p - 1) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hS' : ∀ p ∈ S, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hap : a.Prime := hS a (Finset.mem_insert_self a S)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hcop : Nat.Coprime a (∏ p ∈ S, p) := by
      apply Nat.Coprime.prod_right
      intro q hq
      rw [Nat.coprime_primes hap (hS' q hq)]
      rintro rfl
      exact ha hq
    rw [Nat.totient_mul hcop, Nat.totient_prime hap, ih hS']

/-- If the prime factors of `E` are among those of `D`, then `φ (D * E) = E * φ D`. -/
lemma totient_mul_of_primeFactors_subset {D E : ℕ} (hD : D ≠ 0) (hE : E ≠ 0)
    (h : E.primeFactors ⊆ D.primeFactors) : Nat.totient (D * E) = E * Nat.totient D := by
  have hpf : (D * E).primeFactors = D.primeFactors := by
    rw [Nat.primeFactors_mul hD hE]
    exact Finset.union_eq_left.mpr h
  have k1 := Nat.totient_mul_prod_primeFactors (D * E)
  have k2 := Nat.totient_mul_prod_primeFactors D
  rw [hpf] at k1
  have hpos : 0 < ∏ p ∈ D.primeFactors, p :=
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc (D * E).totient * ∏ p ∈ D.primeFactors, p
      = D * E * ∏ p ∈ D.primeFactors, (p - 1) := k1
    _ = E * (D * ∏ p ∈ D.primeFactors, (p - 1)) := by ring
    _ = E * (D.totient * ∏ p ∈ D.primeFactors, p) := by rw [← k2]
    _ = E * D.totient * ∏ p ∈ D.primeFactors, p := by ring

/-- Construction of `k` large primes, none of which divides `q - 1` for another one `q`. -/
lemma exists_primes (B : ℕ) : ∀ k : ℕ, ∃ P : Finset ℕ, P.card = k ∧
    (∀ p ∈ P, p.Prime ∧ B < p ∧ 2 < p) ∧ ∀ p ∈ P, ∀ q ∈ P, ¬ p ∣ q - 1 := by
  intro k
  induction k with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨P, hcard, hP, hdiv⟩ := ih
    set M := ∏ p ∈ P, p with hM
    have hcop : Nat.Coprime 2 M := by
      apply Nat.Coprime.prod_right
      intro p hp
      rw [Nat.coprime_primes Nat.prime_two (hP p hp).1]
      have := (hP p hp).2.2
      omega
    have : NeZero M := ⟨by
      rw [hM]; exact Finset.prod_ne_zero_iff.mpr (fun p hp => (hP p hp).1.ne_zero)⟩
    have hunit : IsUnit ((2 : ℕ) : ZMod M) := (ZMod.isUnit_iff_coprime 2 M).mpr hcop
    obtain ⟨r, hr, hrp, hreq⟩ :=
      Nat.forall_exists_prime_gt_and_eq_mod hunit (B + P.sup id + 2)
    have hrmod : r ≡ 2 [MOD M] := (ZMod.natCast_eq_natCast_iff r 2 M).mp hreq
    have hMdvd : M ∣ r - 2 := (Nat.modEq_iff_dvd' (by omega)).mp hrmod.symm
    have hle : ∀ q ∈ P, q < r := by
      intro q hq
      have : q ≤ P.sup id := Finset.le_sup (f := id) hq
      omega
    have hrP : r ∉ P := fun h => lt_irrefl r (hle r h)
    refine ⟨insert r P, by rw [Finset.card_insert_of_notMem hrP, hcard], ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact ⟨hrp, by omega, by omega⟩
      · exact hP p hp
    · -- key divisibility facts
      have hr_not : ∀ q ∈ insert r P, ¬ r ∣ q - 1 := by
        intro q hq hd
        have hq3 : 2 < q := by
          rcases Finset.mem_insert.mp hq with rfl | hq
          · omega
          · exact (hP q hq).2.2
        have hqr : q ≤ r := by
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact le_refl _
          · exact (hle q hq).le
        have := Nat.le_of_dvd (by omega) hd
        omega
      intro p hp q hq
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact hr_not q hq
      · rcases Finset.mem_insert.mp hq with hqr | hq'
        · intro hd
          rw [hqr] at hd
          have hpM : p ∣ M := Finset.dvd_prod_of_mem _ hp
          have h2 : p ∣ r - 2 := dvd_trans hpM hMdvd
          have h3 : p ∣ (r - 1) - (r - 2) := Nat.dvd_sub hd h2
          have : (r - 1) - (r - 2) = 1 := by omega
          rw [this] at h3
          exact (hP p hp).1.one_lt.ne' (Nat.dvd_one.mp h3)
        · exact hdiv p hp q hq'

/-- For every `k` and `B` there is `n > B` with `2 ^ k ≤ g n`. -/
lemma exists_large (k B : ℕ) (hk : 1 ≤ k) : ∃ n, B < n ∧ 2 ^ k ≤ Erdos821.g n := by
  obtain ⟨P, hcard, hP, hdiv⟩ := exists_primes (B + 1) k
  set D := ∏ p ∈ P, (p - 1) with hD
  have hD0 : D ≠ 0 := by
    rw [hD, Finset.prod_ne_zero_iff]
    intro p hp
    have := (hP p hp).2.2
    omega
  have hφD : 0 < Nat.totient D := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hD0)
  set n := D * Nat.totient D with hn
  let f : Finset ℕ → ℕ := fun S => D * (∏ p ∈ P \ S, (p - 1)) * ∏ p ∈ S, p
  -- a prime of `P` never divides `D * E` for `E` dividing `D`
  have hnotdvd : ∀ S ⊆ P, ∀ p ∈ P, ¬ p ∣ D * ∏ q ∈ P \ S, (q - 1) := by
    intro S hS p hp hd
    have hpp := (hP p hp).1
    rcases (Nat.Prime.dvd_mul hpp).mp hd with h | h
    · obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp h
      exact hdiv p hp q hq hpq
    · obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp h
      exact hdiv p hp q (Finset.mem_sdiff.mp hq).1 hpq
  have hφf : ∀ S ⊆ P, Nat.totient (f S) = n := by
    intro S hS
    have hSprime : ∀ p ∈ S, p.Prime := fun p hp => (hP p (hS hp)).1
    set E := ∏ p ∈ P \ S, (p - 1) with hE
    have hE0 : E ≠ 0 := by
      rw [hE, Finset.prod_ne_zero_iff]
      intro p hp
      have := (hP p (Finset.mem_sdiff.mp hp).1).2.2
      omega
    have hED : E ∣ D := Finset.prod_dvd_prod_of_subset _ _ _ Finset.sdiff_subset
    have hcop : Nat.Coprime (D * E) (∏ p ∈ S, p) := by
      apply Nat.Coprime.symm
      apply Nat.Coprime.prod_left
      intro p hp
      exact (Nat.Prime.coprime_iff_not_dvd (hSprime p hp)).mpr (hnotdvd S hS p (hS hp))
    show Nat.totient (D * E * ∏ p ∈ S, p) = n
    rw [Nat.totient_mul hcop, totient_prod_primes S hSprime,
      totient_mul_of_primeFactors_subset hD0 hE0 (Nat.primeFactors_mono hED hD0)]
    have hsplit : E * ∏ p ∈ S, (p - 1) = D := by
      rw [hE, hD]
      exact Finset.prod_sdiff hS
    rw [hn, ← hsplit]
    ring
  have hinj : Set.InjOn f (P.powerset : Set (Finset ℕ)) := by
    intro S hS T hT hST
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset] at hS hT
    have hmem : ∀ U ⊆ P, ∀ p ∈ P, (p ∈ U ↔ p ∣ f U) := by
      intro U hU p hp
      have hpp := (hP p hp).1
      constructor
      · intro hpU
        exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hpU) _
      · intro hd
        rcases (Nat.Prime.dvd_mul hpp).mp hd with h | h
        · exact absurd h (hnotdvd U hU p hp)
        · obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp h
          have hqp := (hP q (hU hq)).1
          rw [(Nat.prime_dvd_prime_iff_eq hpp hqp).mp hpq]
          exact hq
    ext p
    by_cases hp : p ∈ P
    · rw [hmem S hS p hp, hmem T hT p hp, hST]
    · exact ⟨fun h => absurd (hS h) hp, fun h => absurd (hT h) hp⟩
  refine ⟨n, ?_, ?_⟩
  · have hne : P.Nonempty := by
      rw [← Finset.card_pos, hcard]; omega
    obtain ⟨p, hp⟩ := hne
    have h1 : p - 1 ≤ D := by
      rw [hD]
      apply Finset.single_le_prod' (fun q hq => ?_) hp
      have := (hP q hq).2.2
      omega
    have h2 := (hP p hp).2.1
    have h3 : D ≤ n := Nat.le_mul_of_pos_right D hφD
    omega
  · have hsub : ((P.powerset.image f : Finset ℕ) : Set ℕ) ⊆ {m : ℕ | Nat.totient m = n} := by
      intro m hm
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_powerset] at hm
      obtain ⟨S, hS, rfl⟩ := hm
      exact hφf S hS
    have hfin := fiber_finite n (Nat.mul_pos (Nat.pos_of_ne_zero hD0) hφD)
    have := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, Finset.card_powerset,
      hcard] at this
    exact this

end OMA821

theorem OMA.solution : type_of% @Erdos821.erdos_821.variants.pillai := by
  rw [EReal.eq_top_iff_forall_lt]
  intro y
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt y (one_lt_two : (1 : ℝ) < 2)
  have hfreq : ∃ᶠ n in Filter.atTop, (((2 : ℕ) ^ (k + 1) : ℕ) : EReal) ≤ (Erdos821.g n : EReal) := by
    rw [Filter.frequently_atTop]
    intro a
    obtain ⟨n, hn, hg⟩ := OMA821.exists_large (k + 1) a (by omega)
    exact ⟨n, hn.le, by exact_mod_cast hg⟩
  have hle := Filter.le_limsup_of_frequently_le hfreq
  refine lt_of_lt_of_le ?_ hle
  have hk' : y < ((2 ^ (k + 1) : ℕ) : ℝ) := by
    push_cast
    calc y < 2 ^ k := hk
      _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [show ((2 ^ (k + 1) : ℕ) : EReal) = (((2 ^ (k + 1) : ℕ) : ℝ) : EReal) by norm_cast]
  exact EReal.coe_lt_coe_iff.mpr hk'
