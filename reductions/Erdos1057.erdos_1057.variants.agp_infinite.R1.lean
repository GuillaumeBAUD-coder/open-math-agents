import FormalConjectures.ErdosProblems.«1057»

-- Reduction Erdos1057.erdos_1057.variants.agp_infinite.R1
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Follows the proof of Alford, Granville and Pomerance (Ann. of Math. 1994); no new result is claimed.

/-!
# Infinitely many Carmichael numbers, after Alford–Granville–Pomerance

The AGP argument has three independent ingredients.

* `H1` (combinatorial group theory, van Emde Boas–Kruyswijk 1969, Meshulam 1990):
  in a finite abelian group `G` of exponent `m`, any sequence of length at least
  `m * (1 + log (|G| / m))` has a nonempty subsequence with product `1`.
* `H2` (analytic, AGP Sections 3–4, built on Prachar's theorem and a Bombieri–Vinogradov
  type estimate): for arbitrarily large `L` there is `k` coprime to `L` and a set of
  primes `p = d k + 1` with `d ∣ L`, `p ∤ k L`, `L ∤ p - 1`, whose size exceeds the
  bound of `H1` for `G = (ZMod L)ˣ`.
* `H3` (Korselt's criterion, easy direction): a squarefree composite `n` such that
  `p - 1 ∣ n - 1` for every prime `p ∣ n` is a Carmichael number.

Assembly (proved below): `H1` applied to the residues of the primes of `H2` gives a
nonempty subset whose product `n` is `1 mod L`; it is also `1 mod k`, hence `1 mod k L`,
so every `p - 1 ∣ k L ∣ n - 1`. A single prime cannot be `1 mod L`, so `n` is composite,
and `n ≡ 1 mod L` forces `n > L`. Hence Carmichael numbers are unbounded, so `C(x) → ∞`.
-/

namespace OMA.R_Erdos1057_erdos_1057_variants_agp_infinite_R1

open Finset

/-- van Emde Boas–Kruyswijk / Meshulam bound on the Davenport constant. -/
def H1 : Prop :=
  ∀ (G : Type) [CommGroup G] [Finite G] (T : Finset ℕ) (g : ℕ → G),
    (Monoid.exponent G : ℝ) * (1 + Real.log ((Nat.card G : ℝ) / (Monoid.exponent G : ℝ)))
      ≤ (T.card : ℝ) →
    ∃ I ⊆ T, I.Nonempty ∧ ∏ i ∈ I, g i = 1

/-- The AGP prime-production theorem (AGP 1994, Theorem 4.1 with the choice of `L` in
Section 3): many primes `p` with `k ∣ p - 1 ∣ k L`. -/
def H2 : Prop :=
  ∀ M : ℕ, ∃ k L : ℕ, M < L ∧ Nat.Coprime k L ∧ ∃ T : Finset ℕ,
    (∀ p ∈ T, p.Prime ∧ ¬ p ∣ k * L ∧ k ∣ p - 1 ∧ (p - 1) ∣ k * L ∧ ¬ L ∣ p - 1) ∧
    (Monoid.exponent (ZMod L)ˣ : ℝ) *
        (1 + Real.log ((Nat.card (ZMod L)ˣ : ℝ) / (Monoid.exponent (ZMod L)ˣ : ℝ)))
      ≤ (T.card : ℝ)

/-- Korselt's criterion (sufficiency). -/
def H3 : Prop :=
  ∀ n : ℕ, 1 < n → ¬ n.Prime → Squarefree n →
    (∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)) → IsCarmichael n

/-- A prime dividing a product of primes is one of them. -/
lemma mem_of_prime_dvd_prod {I : Finset ℕ} (hI : ∀ q ∈ I, q.Prime) {p : ℕ} (hp : p.Prime)
    (h : p ∣ ∏ q ∈ I, q) : p ∈ I := by
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun q => q)).1 h
  rwa [(Nat.prime_dvd_prime_iff_eq hp (hI q hq)).1 hpq]

/-- A product of distinct primes is squarefree. -/
lemma squarefree_prod_primes {I : Finset ℕ} (hI : ∀ q ∈ I, q.Prime) :
    Squarefree (∏ q ∈ I, q) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpI : p ∈ I := mem_of_prime_dvd_prod hI hp (dvd_trans (Dvd.intro p rfl) hpp)
  rw [← Finset.mul_prod_erase I (fun q => q) hpI] at hpp
  have h2 : p ∣ ∏ q ∈ I.erase p, q :=
    Nat.dvd_of_mul_dvd_mul_left hp.pos hpp
  have := mem_of_prime_dvd_prod (fun q hq => hI q (Finset.mem_of_mem_erase hq)) hp h2
  simp at this

/-- The core of the AGP argument: Carmichael numbers are unbounded. -/
lemma exists_carmichael_gt (h1 : H1) (h2 : H2) (h3 : H3) (M : ℕ) :
    ∃ n, M < n ∧ IsCarmichael n := by
  obtain ⟨k, L, hML, hkL, T, hT, hcard⟩ := h2 M
  have : NeZero L := ⟨by omega⟩
  have hcop : ∀ p ∈ T, Nat.Coprime p L := by
    intro p hp
    obtain ⟨hpp, hndvd, -⟩ := hT p hp
    exact (Nat.Coprime.coprime_dvd_right (Dvd.intro_left k rfl)
      ((Nat.Prime.coprime_iff_not_dvd hpp).2 hndvd))
  classical
  let g : ℕ → (ZMod L)ˣ := fun p =>
    if h : Nat.Coprime p L then ZMod.unitOfCoprime p h else 1
  obtain ⟨I, hIT, hIne, hprod⟩ := h1 (ZMod L)ˣ T g hcard
  have hIprime : ∀ q ∈ I, q.Prime := fun q hq => (hT q (hIT hq)).1
  set n := ∏ q ∈ I, q with hn
  -- `n ≡ 1 [MOD L]`
  have hnL : n ≡ 1 [MOD L] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    have : ((∏ q ∈ I, g q : (ZMod L)ˣ) : ZMod L) = 1 := by rw [hprod]; rfl
    rw [Units.coe_prod] at this
    rw [hn, Nat.cast_prod, Nat.cast_one, ← this]
    refine Finset.prod_congr rfl fun q hq => ?_
    simp only [g, dif_pos (hcop q (hIT hq)), ZMod.coe_unitOfCoprime]
  -- `n ≡ 1 [MOD k]`
  have hnk : n ≡ 1 [MOD k] := by
    rw [← ZMod.natCast_eq_natCast_iff, hn, Nat.cast_prod, Nat.cast_one]
    refine Finset.prod_eq_one fun q hq => ?_
    obtain ⟨hqp, -, hkq, -⟩ := hT q (hIT hq)
    have h1q : 1 ≤ q := hqp.one_lt.le
    have : ((q - 1 : ℕ) : ZMod k) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hkq
    rw [Nat.cast_sub h1q, Nat.cast_one, sub_eq_zero] at this
    exact this
  have hnkL : n ≡ 1 [MOD k * L] := (Nat.modEq_and_modEq_iff_modEq_mul hkL).1 ⟨hnk, hnL⟩
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2
    (Finset.prod_ne_zero_iff.2 fun q hq => (hIprime q hq).ne_zero)
  have hdvd : k * L ∣ n - 1 := (Nat.modEq_iff_dvd' hn1).1 hnkL.symm
  have hdvdL : L ∣ n - 1 := (Nat.modEq_iff_dvd' hn1).1 hnL.symm
  -- `I` has two distinct elements
  obtain ⟨p, hpI⟩ := hIne
  have hnot_single : ∃ q ∈ I, q ≠ p := by
    by_contra hcon
    push_neg at hcon
    have hIeq : I = {p} := by
      ext q; constructor
      · intro hq; simp [hcon q hq]
      · intro hq; rw [Finset.mem_singleton] at hq; rw [hq]; exact hpI
    have : n = p := by rw [hn, hIeq, Finset.prod_singleton]
    exact (hT p (hIT hpI)).2.2.2.2 (this ▸ hdvdL)
  obtain ⟨q, hqI, hqp⟩ := hnot_single
  have hpn : p ∣ n := Finset.dvd_prod_of_mem _ hpI
  have hqn : q ∣ n := Finset.dvd_prod_of_mem _ hqI
  have hp1 : 1 < p := (hIprime p hpI).one_lt
  have hnpos : 0 < n := hn1
  have hn_gt : 1 < n := lt_of_lt_of_le hp1 (Nat.le_of_dvd hnpos hpn)
  have hnotprime : ¬ n.Prime := by
    intro hnp
    have e1 := (Nat.prime_dvd_prime_iff_eq (hIprime p hpI) hnp).1 hpn
    have e2 := (Nat.prime_dvd_prime_iff_eq (hIprime q hqI) hnp).1 hqn
    exact hqp (e2.trans e1.symm)
  refine ⟨n, ?_, h3 n hn_gt hnotprime (squarefree_prod_primes hIprime) ?_⟩
  · have hpos : 0 < n - 1 := by omega
    have := Nat.le_of_dvd hpos hdvdL
    omega
  · intro r hr hrn
    have hrI := mem_of_prime_dvd_prod hIprime hr hrn
    exact dvd_trans (hT r (hIT hrI)).2.2.2.1 hdvd

theorem main : H1 → H2 → H3 → type_of% @Erdos1057.erdos_1057.variants.agp_infinite := by
  intro h1 h2 h3
  have hinf : {n : ℕ | IsCarmichael n}.Infinite := by
    refine Set.infinite_of_not_bddAbove ?_
    rintro ⟨B, hB⟩
    obtain ⟨n, hn, hc⟩ := exists_carmichael_gt h1 h2 h3 B
    exact absurd (hB hc) (not_le.2 hn)
  rw [Filter.tendsto_atTop]
  intro b
  obtain ⟨t, hts, htc⟩ := hinf.exists_subset_card_eq (⌈b⌉₊)
  refine Filter.eventually_atTop.2 ⟨(t.sup id : ℕ), fun x hx => ?_⟩
  have hfin : {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x}.Finite := by
    refine (Set.finite_Iic ⌊x⌋₊).subset fun n hn => ?_
    exact Nat.le_floor hn.2
  have hsub : (t : Set ℕ) ⊆ {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x} := by
    intro n hn
    refine ⟨hts hn, le_trans ?_ hx⟩
    exact_mod_cast (Finset.le_sup (f := id) hn)
  have := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, htc] at this
  unfold Erdos1057.carmichaelCounting
  calc b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
    _ ≤ _ := by exact_mod_cast this

end OMA.R_Erdos1057_erdos_1057_variants_agp_infinite_R1
