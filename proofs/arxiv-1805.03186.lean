import OMAStatements.S_arxiv_1805_03186

/-!
# CRT recovery from the quasiprime matrix of any hidden forest

Source: Goodrich, Mbirika and Nielsen, Question 1, https://arxiv.org/abs/1805.03186.
Credit: @rleshner.

A retained prime power divides its original gcd entry and thus both of the
input coordinates at that cell. Distinct retained prime powers are coprime,
so the CRT permits combining all these congruences, in any grouping.
-/

open OMA.S_arxiv_1805_03186

private theorem prod_modEq_iff {P : Finset ℕ} (prime : ∀ p ∈ P, p.Prime)
    (e : ℕ → ℕ) (a b : ℕ) :
    Nat.ModEq (∏ p ∈ P, p ^ e p) a b ↔ ∀ p ∈ P, Nat.ModEq (p ^ e p) a b := by
  induction P using Finset.induction_on with
  | empty => simp [Nat.modEq_one]
  | @insert p S hp ih =>
    have hS : ∀ q ∈ S, Nat.Prime q := fun q hq => prime q (Finset.mem_insert_of_mem hq)
    have co : Nat.Coprime (p ^ e p) (∏ q ∈ S, q ^ e q) := by
      refine Nat.coprime_prod_right_iff.mpr fun q hq => ?_
      exact Nat.coprime_pow_primes _ _ (prime p (Finset.mem_insert_self _ _))
        (hS q hq) (fun h => hp (h ▸ hq))
    rw [Finset.prod_insert hp, ← Nat.modEq_and_modEq_iff_modEq_mul co, ih hS]
    simp

private theorem support_prime {n : ℕ} {g : Cell n → ℕ} {p : ℕ}
    (hp : p ∈ primes g) : p.Prime := by
  obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hp
  exact Nat.prime_of_mem_primeFactors hc

/-- Combining all congruences grouped along one axis gives precisely one
residue class, since the selected prime powers are pairwise coprime. -/
private theorem axis {n : ℕ} {g : Cell n → ℕ} (group : ℕ → Fin n) (x u : ℕ)
    (witness : ∀ p ∈ primes g, p ^ exponent g p ∣ x + (group p).val) :
    (∀ i, block g group i ∣ u + i.val) ↔ Nat.ModEq (period g) u x := by
  have combine (i : Fin n) (a b : ℕ) :
      Nat.ModEq (block g group i) a b ↔
        ∀ p ∈ (primes g).filter (fun p => group p = i), Nat.ModEq (p ^ exponent g p) a b :=
    prod_modEq_iff (fun _ h => support_prime (Finset.mem_filter.mp h).1) _ _ _
  rw [period, prod_modEq_iff (fun _ h => support_prime h)]
  constructor
  · intro rows p hp
    have h := (combine (group p) _ _).mp (Nat.modEq_zero_iff_dvd.mpr (rows (group p)))
      p (Finset.mem_filter.mpr ⟨hp, rfl⟩)
    exact Nat.ModEq.add_right_cancel' _ (h.trans (Nat.modEq_zero_iff_dvd.mpr (witness p hp)).symm)
  · intro h i
    apply Nat.modEq_zero_iff_dvd.mp
    apply (combine i _ _).mpr
    intro p hp
    obtain ⟨hm, hi⟩ := Finset.mem_filter.mp hp
    subst i
    exact ((h p hm).add_right _).trans (Nat.modEq_zero_iff_dvd.mpr (witness p hm))

theorem OMA.solution : type_of% @OMA.S_arxiv_1805_03186.main := by
  classical
  intro n hn x y _ _ _
  let g : Cell n → ℕ := grid x y
  have c0 : Cell n := (⟨0, hn⟩, ⟨0, hn⟩)
  have peak (p : ℕ) : ∃ c : Cell n, (g c).factorization p = exponent g p := by
    obtain ⟨c, _, h⟩ := Finset.exists_mem_eq_sup Finset.univ
      ⟨c0, Finset.mem_univ _⟩ (fun c => (g c).factorization p)
    exact ⟨c, h.symm⟩
  constructor
  · exact ⟨fun p => (peak p).choose, fun p _ => (peak p).choose_spec⟩
  · intro place valid u v
    have divides (p : ℕ) (hp : p ∈ primes g) : p ^ exponent g p ∣ g (place p) := by
      rw [← valid p hp]
      exact Nat.ordProj_dvd _ _
    exact and_congr
      (axis (g := g) (fun p => (place p).1) x u
        (fun p hp => (divides p hp).trans (Nat.gcd_dvd_left _ _)))
      (axis (g := g) (fun p => (place p).2) y v
        (fun p hp => (divides p hp).trans (Nat.gcd_dvd_right _ _)))
