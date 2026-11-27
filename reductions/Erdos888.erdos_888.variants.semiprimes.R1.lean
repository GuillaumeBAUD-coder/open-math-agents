import FormalConjectures.ErdosProblems.«888»

-- Reduction Erdos888.erdos_888.variants.semiprimes.R1 of Erdős Problem 888 — semiprimes
-- Credit: @senamakel
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-! # Semiprimes give the Cambie-Weisenberg lower bound in Erdős 888

The set of products `p * q` of two distinct primes with `p * q ≤ n` satisfies the condition.
- `H1` (Landau 1900, needs the prime number theorem): the number of pairs of primes `p < q`
  with `p * q ≤ n` is at least `(1 + o(1)) n log log n / log n`.
- `H2` (finite parity argument): if four products of two distinct primes, in increasing order,
  have a square product, then the outer product equals the inner one.
`main` takes `A` to be the image of those pairs under multiplication.
-/

namespace OMA.R_Erdos888_erdos_888_variants_semiprimes_R1

open Filter

-- Landau's count of squarefree semiprimes, lower bound with constant 1.
def H1 : Prop :=
  ∃ c : ℕ → ℝ, c =o[atTop] (1 : ℕ → ℝ) ∧ ∀ᶠ n : ℕ in atTop,
    (1 + c n) * ((n : ℝ) * Real.log (Real.log n) / Real.log n) ≤
      (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun x : ℕ × ℕ => x.1.Prime ∧ x.2.Prime ∧ x.1 < x.2 ∧ x.1 * x.2 ≤ n)).card : ℝ)

-- Four increasing products of two distinct primes with a square product: outer = inner.
def H2 : Prop :=
  ∀ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ : ℕ,
    p₁.Prime → q₁.Prime → p₁ < q₁ → p₂.Prime → q₂.Prime → p₂ < q₂ →
    p₃.Prime → q₃.Prime → p₃ < q₃ → p₄.Prime → q₄.Prime → p₄ < q₄ →
    p₁ * q₁ ≤ p₂ * q₂ → p₂ * q₂ ≤ p₃ * q₃ → p₃ * q₃ ≤ p₄ * q₄ →
    IsSquare (p₁ * q₁ * (p₂ * q₂) * (p₃ * q₃) * (p₄ * q₄)) →
    p₁ * q₁ * (p₄ * q₄) = p₂ * q₂ * (p₃ * q₃)

lemma semiprime_inj {p q r s : ℕ} (hp : p.Prime) (_hq : q.Prime) (hr : r.Prime)
    (hs : s.Prime) (hpq : p < q) (hrs : r < s) (h : p * q = r * s) : p = r ∧ q = s := by
  have hd : p ∣ r * s := h ▸ dvd_mul_right p q
  rcases (Nat.Prime.dvd_mul hp).mp hd with h1 | h1
  · have := (Nat.prime_dvd_prime_iff_eq hp hr).mp h1
    subst this
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hp.pos h⟩
  · have := (Nat.prime_dvd_prime_iff_eq hp hs).mp h1
    subst this
    have : q = r := by
      have h' : p * q = p * r := by rw [h, mul_comm]
      exact Nat.eq_of_mul_eq_mul_left hp.pos h'
    omega

open scoped Classical in
theorem main : H1 → H2 → type_of% @Erdos888.erdos_888.variants.semiprimes := by
  intro h1 h2
  obtain ⟨c, hc, hev⟩ := h1
  refine ⟨c, hc, ?_⟩
  filter_upwards [hev] with n hn
  set F := (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun x : ℕ × ℕ => x.1.Prime ∧ x.2.Prime ∧ x.1 < x.2 ∧ x.1 * x.2 ≤ n) with hF
  set A := F.image (fun x : ℕ × ℕ => x.1 * x.2) with hA
  have hmem : ∀ a ∈ A, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ p * q ≤ n ∧ a = p * q := by
    intro a ha
    rw [hA, Finset.mem_image] at ha
    obtain ⟨⟨p, q⟩, hx, rfl⟩ := ha
    rw [hF, Finset.mem_filter] at hx
    exact ⟨p, q, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2, rfl⟩
  have hcard : A.card = F.card := by
    rw [hA]
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    rw [Finset.mem_coe, hF, Finset.mem_filter] at hx hy
    obtain ⟨e1, e2⟩ := semiprime_inj hx.2.1 hx.2.2.1 hy.2.1 hy.2.2.1 hx.2.2.2.1 hy.2.2.2.1 hxy
    exact Prod.ext e1 e2
  have hsub : A ⊆ Finset.Ioc 0 n := by
    intro a ha
    obtain ⟨p, q, hp, hq', -, hle, rfl⟩ := hmem a ha
    rw [Finset.mem_Ioc]
    exact ⟨Nat.mul_pos hp.pos hq'.pos, hle⟩
  have hcond : Erdos888.RequiredCondition A n := by
    refine ⟨hsub, ?_⟩
    intro a ha b hb c' hc' d hd hab hbc hcd hsq
    obtain ⟨p₁, q₁, hp₁, hq₁, h₁, -, rfl⟩ := hmem a ha
    obtain ⟨p₂, q₂, hp₂, hq₂, h₂, -, rfl⟩ := hmem b hb
    obtain ⟨p₃, q₃, hp₃, hq₃, h₃, -, rfl⟩ := hmem c' hc'
    obtain ⟨p₄, q₄, hp₄, hq₄, h₄, -, rfl⟩ := hmem d hd
    exact h2 p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ hp₁ hq₁ h₁ hp₂ hq₂ h₂ hp₃ hq₃ h₃ hp₄ hq₄ h₄
      hab hbc hcd hsq
  have hle : A.card ≤ n := by
    simpa using Finset.card_le_card hsub
  refine le_trans hn ?_
  rw [← hcard]
  have hp : Erdos888.p n A.card := ⟨A, hcond, rfl⟩
  exact_mod_cast Nat.le_findGreatest hle hp

end OMA.R_Erdos888_erdos_888_variants_semiprimes_R1
