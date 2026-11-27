import FormalConjectures.ErdosProblems.«694»

/-!
The prime selection used in Erdős's argument for preserving totient multiplicities.
See Ford, The distribution of totients, Section 1.2, https://arxiv.org/abs/1104.3264.
-/
-- Credit: @SubhanAfz

namespace OMA.R_Erdos694_erdos_694_variants_inf_unique_R1

/-- Infinitely many scaling primes force every preimage of the scaled totient
to be divisible by the scaling prime. -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → (∃ m : ℕ, Nat.totient m = n) →
    {p : ℕ | p.Prime ∧ n + 1 < p ∧
      ∀ x : ℕ, Nat.totient x = n * (p - 1) → p ∣ x}.Infinite

/-- Multiplication by a sufficiently large prime identifies the original totient
fibre with the preimages of the scaled totient divisible by that prime. -/
def H2 : Prop :=
  ∀ n p : ℕ, 0 < n → p.Prime → n + 1 < p →
    (∀ m : ℕ, Nat.totient m = n → Nat.totient (p * m) = n * (p - 1)) ∧
    ∀ x : ℕ, Nat.totient x = n * (p - 1) → p ∣ x →
      ∃ m : ℕ, Nat.totient m = n ∧ x = p * m

theorem main : H1 → H2 → type_of% @Erdos694.erdos_694.variants.inf_unique := by
  rintro selectPrimes liftFibre ⟨n, hn, m, hm, unique⟩
  let goodPrimes : Set ℕ := {p : ℕ | p.Prime ∧ n + 1 < p ∧
    ∀ x : ℕ, Nat.totient x = n * (p - 1) → p ∣ x}
  have hInfinite : goodPrimes.Infinite := selectPrimes n hn ⟨m, hm⟩
  have hInjective : Set.InjOn (fun p : ℕ ↦ n * (p - 1)) goodPrimes := by
    intro p hp q hq hEq
    have hpBound : n + 1 < p := hp.2.1
    have hqBound : n + 1 < q := hq.2.1
    have hSub := Nat.eq_of_mul_eq_mul_left hn hEq
    omega
  refine (hInfinite.image hInjective).mono ?_
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨lift, lower⟩ := liftFibre n p hn hp.1 hp.2.1
  refine ⟨p * m, lift m hm, ?_⟩
  intro x hx
  obtain ⟨k, hk, hxEq⟩ := lower x hx (hp.2.2 x hx)
  rw [unique k hk] at hxEq
  exact hxEq

end OMA.R_Erdos694_erdos_694_variants_inf_unique_R1
