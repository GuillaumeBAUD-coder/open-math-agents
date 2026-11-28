import FormalConjectures.ErdosProblems.«1055»

/-!
Every prime has a class by strong induction on the prime. Given a prime
greater than three in class r, Dirichlet's theorem supplies a prime in a
higher class. The least prime in any class above r must have class r + 1.
Otherwise the successor definition gives a smaller prime still above r.
-/

open Erdos1055

namespace PrimeClasses

private lemma strong_induction_step {P : ℕ+ → Sort*} (n : ℕ+)
    (f : ∀ k, (∀ m, m < k → P m) → P k) :
    PNat.strongInductionOn n f = f n (fun a _ => PNat.strongInductionOn a f) := by
  rw [PNat.strongInductionOn]

private lemma class_one (p : ℕ) : IsOfClass 1 p ↔ (p + 1).primeFactors ⊆ {2, 3} := by
  unfold IsOfClass PNat.caseStrongInductionOn
  rw [PNat.strongInductionOn]
  rfl

private lemma class_succ (n : ℕ+) (p : ℕ) : IsOfClass (n + 1) p ↔
    (∀ m ≤ n, ¬ IsOfClass m p) ∧
      (∀ q ∈ (p + 1).primeFactors, ∃ m, ∃ _ : m ≤ n, IsOfClass m q) ∧
      (∃ q ∈ (p + 1).primeFactors, ∀ m ≤ n, IsOfClass m q → m = n) := by
  obtain ⟨_ | k, hk⟩ := n
  · omega
  show IsOfClass ⟨k + 2, by omega⟩ p ↔ _
  unfold IsOfClass PNat.caseStrongInductionOn
  refine (iff_of_eq (congrFun (strong_induction_step (P := fun _ : ℕ+ => ℕ → Prop)
    ⟨k + 2, by omega⟩ _) p)).trans ?_
  rfl

private lemma no_lower_class {r s : ℕ+} {p : ℕ} (hrs : r < s) (hs : IsOfClass s p) :
    ¬ IsOfClass r p := by
  have hs1 : s ≠ 1 := fun h => not_lt_of_ge one_le (h ▸ hrs)
  obtain ⟨s, rfl⟩ := PNat.exists_eq_succ_of_ne_one hs1
  exact ((class_succ s p).mp hs).1 r (PNat.lt_add_one_iff.mp hrs)

private lemma class_unique {r s : ℕ+} {p : ℕ} (hr : IsOfClass r p) (hs : IsOfClass s p) : r = s := by
  rcases lt_trichotomy r s with h | h | h
  · exact (no_lower_class h hs hr).elim
  · exact h
  · exact (no_lower_class h hr hs).elim

private lemma small_prime_class {p : ℕ} (hp : p.Prime) (h : p ≤ 3) : IsOfClass 1 p := by
  have := hp.two_le
  rw [class_one]
  interval_cases p <;> norm_num [Nat.primeFactors, Nat.primeFactorsList]

private lemma factor_lt {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hq : q ∈ (p + 1).primeFactors) : q < p := by
  have hd : 2 ∣ p + 1 := even_iff_two_dvd.mp
    ((hp.odd_of_ne_two (by omega)).add_odd (by decide))
  by_cases hq2 : q = 2
  · omega
  have hcop := (Nat.coprime_primes Nat.prime_two (Nat.prime_of_mem_primeFactors hq)).mpr (Ne.symm hq2)
  have hmul := hcop.mul_dvd_of_dvd_of_dvd hd (Nat.dvd_of_mem_primeFactors hq)
  have := Nat.le_of_dvd (by omega : 0 < p + 1) hmul
  omega

private lemma prime_has_class (p : ℕ) (hp : p.Prime) : ∃ r, IsOfClass r p := by
  classical
  induction p using Nat.strong_induction_on with
  | h p ih =>
    by_contra! hnone
    have hp3 : 3 < p := by
      by_contra! h
      exact hnone 1 (small_prime_class hp h)
    let F := (p + 1).primeFactors
    have hn : F.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      exact hnone 1 ((class_one p).mpr (by change F ⊆ _; simp [he]))
    have child (q : ℕ) (hq : q ∈ F) : ∃ r, IsOfClass r q :=
      ih q (factor_lt hp hp3 hq) (Nat.prime_of_mem_primeFactors hq)
    choose! c hc using child
    let M := F.sup' hn c
    obtain ⟨q, hq, hqM⟩ := Finset.exists_mem_eq_sup' hn c
    apply hnone (M + 1)
    refine (class_succ M p).mpr ⟨fun m _ => hnone m, ?_, q, hq, ?_⟩
    · exact fun q hq => ⟨c q, Finset.le_sup' c hq, hc q hq⟩
    · exact fun m _ hm => (class_unique hm (hc q hq)).trans hqM.symm

private lemma factor_class_lt {p q : ℕ} {r s : ℕ+} (hq : q ∈ (p + 1).primeFactors)
    (hq3 : 3 < q) (hr : IsOfClass r q) (hs : IsOfClass s p) : r < s := by
  have hs1 : s ≠ 1 := by
    rintro rfl
    have hmem := (class_one p).mp hs hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  obtain ⟨s, rfl⟩ := PNat.exists_eq_succ_of_ne_one hs1
  obtain ⟨t, ht, hqclass⟩ := ((class_succ s p).mp hs).2.1 q hq
  exact PNat.lt_add_one_iff.mpr (class_unique hr hqclass ▸ ht)

private theorem prime_gt_three_in_class (r : ℕ+) : ∃ p, 3 < p ∧ p.Prime ∧ IsOfClass r p := by
  classical
  induction r using PNat.recOn with
  | one =>
    refine ⟨5, by decide, by decide, (class_one 5).mpr ?_⟩
    norm_num [Nat.primeFactors, Nat.primeFactorsList]
  | succ r ih =>
    obtain ⟨q, hq3, hq, hr⟩ := ih
    have hex : ∃ p, p.Prime ∧ ∃ s, r < s ∧ IsOfClass s p := by
      let : NeZero q := ⟨hq.ne_zero⟩
      obtain ⟨p, -, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod
        (q := q) (a := -1) isUnit_one.neg 0
      have hd : q ∣ p + 1 := by
        rw [← ZMod.natCast_eq_zero_iff]
        push_cast
        rw [hpmod, neg_add_cancel]
      have hqf : q ∈ (p + 1).primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hd, by omega⟩
      obtain ⟨s, hs⟩ := prime_has_class p hp
      exact ⟨p, hp, s, factor_class_lt hqf hq3 hr hs, hs⟩
    let p := Nat.find hex
    obtain ⟨hp, s, hrs, hs⟩ := Nat.find_spec hex
    have hr1 : ¬ r < 1 := not_lt_of_ge one_le
    have hp3 : 3 < p := by
      by_contra! h
      exact hr1 (class_unique hs (small_prime_class hp h) ▸ hrs)
    have hs1 : s ≠ 1 := fun h => hr1 (h ▸ hrs)
    obtain ⟨s, rfl⟩ := PNat.exists_eq_succ_of_ne_one hs1
    by_cases h : r = s
    · exact ⟨p, hp3, hp, h.symm ▸ hs⟩
    have hlt := lt_of_le_of_ne (PNat.lt_add_one_iff.mp hrs) h
    obtain ⟨_, hall, t, ht, htop⟩ := (class_succ s p).mp hs
    obtain ⟨u, hu, hc⟩ := hall t ht
    exact (Nat.find_min hex (factor_lt hp hp3 ht)
      ⟨Nat.prime_of_mem_primeFactors ht, s, hlt, htop u hu hc ▸ hc⟩).elim

end PrimeClasses

theorem OMA.solution : type_of% @Erdos1055.exists_p := by
  intro r
  obtain ⟨p, _, hp, hr⟩ := PrimeClasses.prime_gt_three_in_class r
  exact ⟨p, hp, hr⟩
