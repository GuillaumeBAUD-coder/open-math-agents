import OMAStatements.S_oeis_a120737
import Mathlib

/-!
# OEIS A120737: if `τ(k)` divides `rad(k)` then `rad(k) = τ(k)`

Write `k = ∏ p^(v_p)` over its prime divisors `p ∈ P`, so
`τ(k) = ∏_{p ∈ P} (v_p + 1)` and `rad(k) = ∏_{p ∈ P} p`.

For each `p ∈ P` pick a prime `f(p)` dividing `v_p + 1 ≥ 2`. Then `f(p) ∣ τ(k) ∣ rad(k)`, so
`f(p) ∈ P`. The map `f : P → P` is injective: if `f(p) = f(p') = q` with `p ≠ p'`, then
`q² ∣ (v_p + 1)(v_p' + 1) ∣ τ(k) ∣ rad(k)`, impossible because `rad(k)` is a product of distinct
primes. An injective map from a finite set to itself is a bijection, hence

  `rad(k) = ∏_{p ∈ P} f(p)`, which divides `∏_{p ∈ P} (v_p + 1) = τ(k)`.

Together with the hypothesis this gives `rad(k) = τ(k)`, so the quotient is `1`.
-/

open UniqueFactorizationMonoid

namespace OMA.A120737

/-- The squarefree kernel, as an explicit product. -/
def rad (k : ℕ) : ℕ := ∏ p ∈ k.primeFactors, p

/-- The number of divisors. -/
def tau (k : ℕ) : ℕ := k.divisors.card

lemma rad_ne_zero (k : ℕ) : rad k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hp => (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- The primes dividing `rad k` are the primes dividing `k`. -/
lemma mem_of_dvd_rad {k q : ℕ} (hq : q.Prime) (h : q ∣ rad k) : q ∈ k.primeFactors := by
  have : q ∈ (rad k).primeFactors := Nat.mem_primeFactors.mpr ⟨hq, h, rad_ne_zero k⟩
  rwa [rad, Nat.primeFactors_prod_primeFactors] at this

/-- `rad k` is a product of distinct primes: no prime square divides it. -/
lemma sq_not_dvd_rad (k q : ℕ) (hq : q.Prime) : ¬ q * q ∣ rad k := by
  intro h
  have hqP : q ∈ k.primeFactors := mem_of_dvd_rad hq ((Dvd.intro _ rfl).trans h)
  unfold rad at h
  rw [← Finset.mul_prod_erase _ _ hqP] at h
  have h' : q ∣ ∏ p ∈ k.primeFactors.erase q, p := Nat.dvd_of_mul_dvd_mul_left hq.pos h
  obtain ⟨p, hp, hqp⟩ := (hq.prime.dvd_finsetProd_iff _).mp h'
  have hpP := Finset.mem_of_mem_erase hp
  have hqp' : q = p :=
    (Nat.prime_dvd_prime_iff_eq hq (Nat.prime_of_mem_primeFactors hpP)).mp hqp
  exact (Finset.ne_of_mem_erase hp) hqp'.symm

/-- The theorem. -/
lemma key (k : ℕ) (hk : 1 ≤ k) (h : tau k ∣ rad k) : rad k = tau k := by
  have hk0 : k ≠ 0 := by omega
  have hτ : tau k = ∏ p ∈ k.primeFactors, (k.factorization p + 1) := Nat.card_divisors hk0
  -- a prime factor of each `v_p + 1`
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, f = fun p => (k.factorization p + 1).minFac := ⟨_, rfl⟩
  have hfprime : ∀ p ∈ k.primeFactors, (f p).Prime := by
    intro p hp
    have hpos : 0 < k.factorization p :=
      (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hk0
        (Nat.dvd_of_mem_primeFactors hp)
    rw [hf]
    exact Nat.minFac_prime (by omega)
  have hfdvd : ∀ p ∈ k.primeFactors, f p ∣ k.factorization p + 1 := by
    intro p _
    rw [hf]
    exact Nat.minFac_dvd _
  have hfτ : ∀ p ∈ k.primeFactors, f p ∣ tau k := by
    intro p hp
    rw [hτ]
    exact (hfdvd p hp).trans (Finset.dvd_prod_of_mem _ hp)
  -- `f` maps the prime divisors of `k` to themselves
  have hfP : ∀ p ∈ k.primeFactors, f p ∈ k.primeFactors :=
    fun p hp => mem_of_dvd_rad (hfprime p hp) ((hfτ p hp).trans h)
  -- and is injective there
  have hinj : ∀ p ∈ k.primeFactors, ∀ p' ∈ k.primeFactors, f p = f p' → p = p' := by
    intro p hp p' hp' hpp'
    by_contra hne
    apply sq_not_dvd_rad k (f p) (hfprime p hp)
    refine Dvd.dvd.trans ?_ h
    have h2 : f p ∣ k.factorization p' + 1 := by rw [hpp']; exact hfdvd p' hp'
    rw [hτ, ← Finset.mul_prod_erase _ _ hp]
    exact mul_dvd_mul (hfdvd p hp)
      (h2.trans (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨Ne.symm hne, hp'⟩)))
  -- so `f` permutes them
  have himg : k.primeFactors.image f = k.primeFactors := by
    apply Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hfP)
    rw [Finset.card_image_of_injOn]
    intro x hx y hy hxy
    exact hinj x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hxy
  have hR : rad k = ∏ p ∈ k.primeFactors, f p := by
    have := Finset.prod_image (s := k.primeFactors) (g := f) (f := fun x => x) hinj
    rw [himg] at this
    exact this
  -- hence `rad k ∣ τ(k)`
  have hdiv : rad k ∣ tau k := by
    rw [hR, hτ]
    exact Finset.prod_dvd_prod_of_dvd _ _ hfdvd
  exact Nat.dvd_antisymm hdiv h

end OMA.A120737

open OMA.A120737 in
theorem OMA.solution : type_of% @OMA.S_oeis_a120737.main := by
  intro k hk h
  have e : radical k = rad k := Nat.radical_eq_prod_primeFactors
  rw [e] at h ⊢
  have heq : rad k = tau k := key k hk h
  have hpos : 0 < k.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
  rw [heq]
  exact Nat.div_self hpos
