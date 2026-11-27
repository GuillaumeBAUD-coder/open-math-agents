import OMAReductions.R_Erdos69_erdos_69_R1

-- Reduction Erdos69.erdos_69.R1.H1.R1 of step H1 of Erdos69.erdos_69.R1 (Erdős Problem 69)
-- Credit: @chris01-dev

/-!
# Erdős Problem 69, the elementary part: four concrete steps

Step `H1` of `Erdos69.erdos_69.R1` is the elementary part of the Tao–Teräväinen proof
(arXiv:2512.01739, Section 9). This file makes its data explicit and splits it.

**The data at scale `x`** (Sections 9.5 and 9.6 of the paper). Put `l = log log log x`,
`K = ⌊2 log l / log 2⌋`, `H = ⌊l ^ 2⌋`. A cube of primes is a family `p E`, indexed by the
subsets `E` of `range K`, of distinct primes in `[exp (l ^ 3) / 8, exp (l ^ 3)]`, with integers
`s E`; the shifts are `r E h = p E * h - s E`. In the paper `p E = p_0 + ∑ k ∈ E, v_k` and
`s E = ∑ k ∈ E, (k + 1) * v_k`; all that is used is the symmetry
`r (E ∆ {k}) (k + 1) = r E (k + 1)` and the bound `|s E| ≤ 8 * K ^ 2 * p E`. (The paper takes
the primes in the upper half of the range; the wider window changes nothing in its estimates and
lets the cube be found with Chebyshev bounds alone.) The near shifts are the
`r E h` with `K + 1 ≤ h ≤ K + H`, assumed pairwise distinct (`W ≠ 0`, where `W` is the product
of their differences). The integers `n` run over `[x / 2, x]` in the progression `n ≡ b mod Q`,
where `Q` is the product of the `p E` and of the full powers in `W` of the other primes dividing
`W`, with `b ≡ s E mod p E` and `b ≡ 0` modulo the second factor.

* `H1`: such data exist at every large scale, with `2 ^ K` large, and `Q`, the `s E` and the
  near shifts at most `exp (sqrt (log log x))` (the Hilbert cube lemma for primes, the Chinese
  remainder theorem and the hierarchy of scales).
* `H2`: for any such data the contribution of the primes up to `R = x ^ (1 / (log log x) ^ 2)`
  at the near shifts, times `q`, is at distance at least `1 / 10` from the integers for at
  least a tenth of the `n` (Sections 9.4, 9.9, 9.10 and 9.11: the small primes are frozen by the
  congruences, the medium primes are nearly independent and their total variance tends to
  infinity, so the characteristic function tends to zero).
* `H3`: the contribution of the primes in `(R, y]` at the near shifts has small mean square
  (Section 9.12, large primes), for every `y ≤ x ^ (1 / 50)`.
* `H4`: the far shifts and the square-divisibility terms are small on average (Sections 9.7 and
  9.8).

`main` proves the differencing identity over the cube (Section 9.2): for `n` in the progression,
the alternating sum over `E` of the tails at `(n - s E) / p E` equals the alternating sum of
`ω (n + r E h) / 2 ^ h` over `h > K` plus square-divisibility terms, the shifts `h ≤ K`
cancelling in pairs. Splitting `ω` by the size of the prime and applying Chebyshev's inequality
to `H3` and `H4` then gives the target, with the weights `(-1) ^ |E| / 2 ^ h` on the near shifts.
-/

namespace OMA.R_Erdos69_erdos_69_R1_H1_R1

/-- Existence of the data: a cube of primes with distinct near shifts and its progression,
with everything of size at most `exp (sqrt (log log x))`. -/
def H1 : Prop :=
  ∀ η : ℝ, 0 < η → ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
    ∃ (K H Q b : ℕ) (p : Finset ℕ → ℕ) (s : Finset ℕ → ℤ),
    let l := Real.log (Real.log (Real.log x))
    let B := Real.exp (Real.sqrt (Real.log (Real.log x)))
    let C := (Finset.range K).powerset
    let r := fun (E : Finset ℕ) (h : ℕ) => (p E : ℤ) * h - s E
    let S := C ×ˢ Finset.Ico (K + 1) (K + H + 1)
    let W := ∏ a ∈ S.offDiag, (r a.1.1 a.1.2 - r a.2.1 a.2.2).natAbs
    K = ⌊2 * Real.log l / Real.log 2⌋₊ ∧ H = ⌊l ^ 2⌋₊ ∧
    (∀ E ∈ C, (p E).Prime ∧ Real.exp (l ^ 3) ≤ 8 * p E ∧ (p E : ℝ) ≤ Real.exp (l ^ 3) ∧
      |s E| ≤ 8 * K ^ 2 * p E ∧ (b : ℤ) ≡ s E [ZMOD p E] ∧
      ∀ k < K, r (symmDiff E {k}) (k + 1) = r E (k + 1)) ∧
    Set.InjOn p C ∧ W ≠ 0 ∧
    Q = (∏ E ∈ C, p E) * ∏ ℓ ∈ W.primeFactors \ C.image p, ℓ ^ W.factorization ℓ ∧
    (∏ ℓ ∈ W.primeFactors \ C.image p, ℓ ^ W.factorization ℓ) ∣ b ∧
    1 / 2 ^ K ≤ η ∧ (Q : ℝ) ≤ B ∧ (∀ E ∈ C, |(s E : ℝ)| ≤ B) ∧
    ∀ a ∈ S, |(r a.1 a.2 : ℝ)| ≤ B

def H2 : Prop :=
  ∀ q : ℕ, 0 < q → ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
    ∀ (K H Q b : ℕ) (p : Finset ℕ → ℕ) (s : Finset ℕ → ℤ),
    let l := Real.log (Real.log (Real.log x))
    let C := (Finset.range K).powerset
    let r := fun (E : Finset ℕ) (h : ℕ) => (p E : ℤ) * h - s E
    let S := C ×ˢ Finset.Ico (K + 1) (K + H + 1)
    let W := ∏ a ∈ S.offDiag, (r a.1.1 a.1.2 - r a.2.1 a.2.2).natAbs
    let N := (Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q)
    K = ⌊2 * Real.log l / Real.log 2⌋₊ → H = ⌊l ^ 2⌋₊ →
    (∀ E ∈ C, (p E).Prime ∧ Real.exp (l ^ 3) ≤ 8 * p E ∧ (p E : ℝ) ≤ Real.exp (l ^ 3) ∧
      |s E| ≤ 8 * K ^ 2 * p E ∧ (b : ℤ) ≡ s E [ZMOD p E] ∧
      ∀ k < K, r (symmDiff E {k}) (k + 1) = r E (k + 1)) →
    Set.InjOn p C → W ≠ 0 →
    Q = (∏ E ∈ C, p E) * ∏ ℓ ∈ W.primeFactors \ C.image p, ℓ ^ W.factorization ℓ →
    (∏ ℓ ∈ W.primeFactors \ C.image p, ℓ ^ W.factorization ℓ) ∣ b →
    ∃ A : Finset ℕ, A.Nonempty ∧ A ⊆ N ∧ (N.card : ℝ) ≤ 10 * A.card ∧
      ∀ n ∈ A, ∀ z : ℤ, 1 / 10 ≤ |(q : ℝ) * (∑ a ∈ S, (-1) ^ a.1.card / 2 ^ a.2 *
        ((((n : ℤ) + r a.1 a.2).natAbs.primeFactors.filter
          (fun ℓ : ℕ => (ℓ : ℝ) ≤ (x : ℝ) ^ (1 / Real.log (Real.log x) ^ 2))).card : ℝ)) - z|

def H3 : Prop :=
  ∀ η : ℝ, 0 < η → ∃ X : ℕ, ∀ x : ℕ, X ≤ x → ∀ y : ℝ, y ≤ (x : ℝ) ^ (1 / 50 : ℝ) →
    ∀ (K H Q b : ℕ) (p : Finset ℕ → ℕ) (s : Finset ℕ → ℤ),
    let l := Real.log (Real.log (Real.log x))
    let C := (Finset.range K).powerset
    let r := fun (E : Finset ℕ) (h : ℕ) => (p E : ℤ) * h - s E
    let S := C ×ˢ Finset.Ico (K + 1) (K + H + 1)
    let W := ∏ a ∈ S.offDiag, (r a.1.1 a.1.2 - r a.2.1 a.2.2).natAbs
    let N := (Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q)
    K = ⌊2 * Real.log l / Real.log 2⌋₊ → H = ⌊l ^ 2⌋₊ →
    (∀ E ∈ C, (p E).Prime ∧ Real.exp (l ^ 3) ≤ 8 * p E ∧ (p E : ℝ) ≤ Real.exp (l ^ 3) ∧
      |s E| ≤ 8 * K ^ 2 * p E ∧ (b : ℤ) ≡ s E [ZMOD p E] ∧
      ∀ k < K, r (symmDiff E {k}) (k + 1) = r E (k + 1)) →
    Set.InjOn p C → W ≠ 0 →
    Q = (∏ E ∈ C, p E) * ∏ ℓ ∈ W.primeFactors \ C.image p, ℓ ^ W.factorization ℓ →
    (∏ ℓ ∈ W.primeFactors \ C.image p, ℓ ^ W.factorization ℓ) ∣ b →
    ∑ n ∈ N, (∑ a ∈ S, (-1) ^ a.1.card / 2 ^ a.2 *
        ((((n : ℤ) + r a.1 a.2).natAbs.primeFactors.filter
          (fun ℓ : ℕ => (x : ℝ) ^ (1 / Real.log (Real.log x) ^ 2) < ℓ ∧ (ℓ : ℝ) ≤ y)).card : ℝ)) ^ 2
      ≤ η * N.card

def H4 : Prop :=
  ∀ η : ℝ, 0 < η → ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
    ∀ (K H Q b : ℕ) (p : Finset ℕ → ℕ) (s : Finset ℕ → ℤ),
    let l := Real.log (Real.log (Real.log x))
    let C := (Finset.range K).powerset
    let r := fun (E : Finset ℕ) (h : ℕ) => (p E : ℤ) * h - s E
    let S := C ×ˢ Finset.Ico (K + 1) (K + H + 1)
    let W := ∏ a ∈ S.offDiag, (r a.1.1 a.1.2 - r a.2.1 a.2.2).natAbs
    let N := (Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q)
    K = ⌊2 * Real.log l / Real.log 2⌋₊ → H = ⌊l ^ 2⌋₊ →
    (∀ E ∈ C, (p E).Prime ∧ Real.exp (l ^ 3) ≤ 8 * p E ∧ (p E : ℝ) ≤ Real.exp (l ^ 3) ∧
      |s E| ≤ 8 * K ^ 2 * p E ∧ (b : ℤ) ≡ s E [ZMOD p E] ∧
      ∀ k < K, r (symmDiff E {k}) (k + 1) = r E (k + 1)) →
    Set.InjOn p C → W ≠ 0 →
    Q = (∏ E ∈ C, p E) * ∏ ℓ ∈ W.primeFactors \ C.image p, ℓ ^ W.factorization ℓ →
    (∏ ℓ ∈ W.primeFactors \ C.image p, ℓ ^ W.factorization ℓ) ∣ b →
    ∑ n ∈ N, ∑ E ∈ C, ∑' h : ℕ,
        ((ArithmeticFunction.cardDistinctFactors ((n : ℤ) + r E (h + K + H + 1)).natAbs : ℝ)
            / 2 ^ (h + K + H + 1)
          + (if (p E : ℤ) ^ 2 ∣ (n : ℤ) + r E (h + 1) then (1 : ℝ) else 0) / 2 ^ (h + 1))
      ≤ η * N.card

open scoped ArithmeticFunction.omega


lemma omega_prime_mul {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (ω (p * k) : ℝ) = ω k + 1 - (if p ^ 2 ∣ p * k then 1 else 0) := by
  have hdvd : p ^ 2 ∣ p * k ↔ p ∣ k := by
    rw [sq]; exact Nat.mul_dvd_mul_iff_left hp.pos
  rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors,
    ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors,
    Nat.primeFactors_mul hp.ne_zero hk.ne', hp.primeFactors]
  by_cases h : p ∣ k
  · have hmem : p ∈ k.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, h, hk.ne'⟩
    rw [if_pos (hdvd.mpr h), Finset.union_eq_right.mpr (Finset.singleton_subset_iff.mpr hmem)]
    ring
  · have hmem : p ∉ k.primeFactors := fun hm => h (Nat.dvd_of_mem_primeFactors hm)
    rw [if_neg (fun h' => h (hdvd.mp h')), Finset.singleton_union, Finset.card_insert_of_notMem hmem]
    push_cast
    ring

lemma summable_T (m : ℕ) : Summable (fun h : ℕ => (ω (m + h + 1) : ℝ) / 2 ^ (h + 1)) := by
  have hs := ArithmeticFunction.summable_cardDistinctFactors_div_two_pow
  have h1 := ((summable_nat_add_iff (m + 1)).mpr hs).mul_left ((2 : ℝ) ^ m)
  refine h1.congr fun h => ?_
  rw [show m + h + 1 = h + (m + 1) by ring, show h + (m + 1) = (h + 1) + m by ring,
    pow_add (2 : ℝ) (h + 1) m]
  field_simp

lemma tsum_half_pow : ∑' h : ℕ, (1 : ℝ) / 2 ^ (h + 1) = 1 := by
  have h1 := tsum_geometric_two' (1 : ℝ)
  have h2 : ∀ h : ℕ, (1 : ℝ) / 2 ^ (h + 1) = 1 / 2 / 2 ^ h := by
    intro h
    rw [pow_succ]
    field_simp
  rw [tsum_congr h2, h1]

lemma summable_half_pow : Summable (fun h : ℕ => (1 : ℝ) / 2 ^ (h + 1)) := by
  have := summable_geometric_two' (1 : ℝ)
  refine this.congr fun h => ?_
  rw [pow_succ]
  field_simp

/-- One vertex of the cube: the tail at `m` in terms of the progression `p * (m + h + 1)`. -/
lemma tail_dilate {p m : ℕ} (hp : p.Prime) :
    Summable (fun h : ℕ => (ω (p * (m + h + 1)) : ℝ) / 2 ^ (h + 1)) ∧
    Summable (fun h : ℕ => (if p ^ 2 ∣ p * (m + h + 1) then (1 : ℝ) else 0) / 2 ^ (h + 1)) ∧
    ∑' h : ℕ, (ω (m + h + 1) : ℝ) / 2 ^ (h + 1)
      = ∑' h : ℕ, (ω (p * (m + h + 1)) : ℝ) / 2 ^ (h + 1) - 1
        + ∑' h : ℕ, (if p ^ 2 ∣ p * (m + h + 1) then (1 : ℝ) else 0) / 2 ^ (h + 1) := by
  have hT := summable_T m
  have hI : Summable (fun h : ℕ =>
      (if p ^ 2 ∣ p * (m + h + 1) then (1 : ℝ) else 0) / 2 ^ (h + 1)) := by
    refine Summable.of_nonneg_of_le (fun h => by positivity) (fun h => ?_) summable_half_pow
    gcongr
    split_ifs <;> norm_num
  have hterm : ∀ h : ℕ, (ω (p * (m + h + 1)) : ℝ) / 2 ^ (h + 1)
      = (ω (m + h + 1) : ℝ) / 2 ^ (h + 1) + 1 / 2 ^ (h + 1)
        - (if p ^ 2 ∣ p * (m + h + 1) then (1 : ℝ) else 0) / 2 ^ (h + 1) := by
    intro h
    rw [omega_prime_mul hp (by omega : 0 < m + h + 1)]
    ring
  have hW : Summable (fun h : ℕ => (ω (p * (m + h + 1)) : ℝ) / 2 ^ (h + 1)) :=
    ((hT.add summable_half_pow).sub hI).congr fun h => (hterm h).symm
  refine ⟨hW, hI, ?_⟩
  have : ∑' h : ℕ, (ω (p * (m + h + 1)) : ℝ) / 2 ^ (h + 1)
      = ∑' h : ℕ, (ω (m + h + 1) : ℝ) / 2 ^ (h + 1) + 1
        - ∑' h : ℕ, (if p ^ 2 ∣ p * (m + h + 1) then (1 : ℝ) else 0) / 2 ^ (h + 1) := by
    rw [tsum_congr hterm, (hT.add summable_half_pow).tsum_sub hI, hT.tsum_add summable_half_pow,
      tsum_half_pow]
  linarith

lemma sign_symmDiff (E : Finset ℕ) (h : ℕ) :
    ((-1 : ℝ)) ^ (symmDiff E {h}).card = - (-1 : ℝ) ^ E.card := by
  by_cases hh : h ∈ E
  · have : symmDiff E {h} = E.erase h := by
      ext a
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
      constructor
      · rintro (⟨ha, hne⟩ | ⟨rfl, hna⟩)
        · exact ⟨hne, ha⟩
        · exact absurd hh hna
      · rintro ⟨hne, ha⟩
        exact Or.inl ⟨ha, hne⟩
    rw [this]
    have hc : E.card = (E.erase h).card + 1 := (Finset.card_erase_add_one hh).symm
    rw [hc, pow_succ]
    ring
  · have : symmDiff E {h} = insert h E := by
      ext a
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      constructor
      · rintro (⟨ha, _⟩ | ⟨rfl, _⟩)
        · exact Or.inr ha
        · exact Or.inl rfl
      · rintro (rfl | ha)
        · exact Or.inr ⟨rfl, hh⟩
        · exact Or.inl ⟨ha, fun hah => hh (hah ▸ ha)⟩
    rw [this, Finset.card_insert_of_notMem hh, pow_succ]
    ring

/-- The alternating sum over the cube kills every shift that does not depend on one coordinate. -/
lemma cube_cancel (K : ℕ) (f : Finset ℕ → ℝ) (h : ℕ) (hh : h < K)
    (hsym : ∀ E ∈ (Finset.range K).powerset, f (symmDiff E {h}) = f E) :
    ∑ E ∈ (Finset.range K).powerset, (-1 : ℝ) ^ E.card * f E = 0 := by
  refine Finset.sum_involution (fun E _ => symmDiff E {h}) ?_ ?_ ?_ ?_
  · intro E hE
    rw [sign_symmDiff, hsym E hE]
    ring
  · intro E _ _ heq
    have h1 : h ∈ symmDiff E {h} ↔ h ∈ E := by rw [heq]
    simp [Finset.mem_symmDiff] at h1
  · intro E hE
    rw [Finset.mem_powerset] at hE ⊢
    intro a ha
    rcases Finset.mem_symmDiff.mp ha with ⟨ha, _⟩ | ⟨ha, _⟩
    · exact hE ha
    · rw [Finset.mem_singleton] at ha
      exact ha ▸ Finset.mem_range.mpr hh
  · intro E _
    exact symmDiff_symmDiff_cancel_right _ _


/-- The alternating sum of tails over a cube of primes: near shifts and remainder. -/
lemma pointwise (K H : ℕ) (hK : 0 < K) (p m : Finset ℕ → ℕ)
    (hp : ∀ E ∈ (Finset.range K).powerset, (p E).Prime)
    (hsym : ∀ E ∈ (Finset.range K).powerset, ∀ h < K,
      p (symmDiff E {h}) * (m (symmDiff E {h}) + h + 1) = p E * (m E + h + 1)) :
    ∑ E ∈ (Finset.range K).powerset, (-1 : ℝ) ^ E.card *
        ∑' h : ℕ, (ω (m E + h + 1) : ℝ) / 2 ^ (h + 1)
      = ∑ a ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1),
          (-1 : ℝ) ^ a.1.card / 2 ^ a.2 * (ω (p a.1 * (m a.1 + a.2)) : ℝ)
        + ∑ E ∈ (Finset.range K).powerset, (-1 : ℝ) ^ E.card *
          (∑' h : ℕ, (ω (p E * (m E + (h + (K + H)) + 1)) : ℝ) / 2 ^ (h + (K + H) + 1)
            + ∑' h : ℕ, (if p E ^ 2 ∣ p E * (m E + h + 1) then (1 : ℝ) else 0) / 2 ^ (h + 1)) := by
  have hsign : ∑ E ∈ (Finset.range K).powerset, (-1 : ℝ) ^ E.card = 0 := by
    have := Finset.sum_powerset_neg_one_pow_card (α := ℕ) (x := Finset.range K)
    have hne : Finset.range K ≠ ∅ := by
      rw [← Finset.nonempty_iff_ne_empty]; exact Finset.nonempty_range_iff.mpr hK.ne'
    rw [if_neg hne] at this
    have h2 : ((∑ E ∈ (Finset.range K).powerset, (-1 : ℤ) ^ E.card : ℤ) : ℝ) = 0 := by
      rw [this]; simp
    push_cast at h2
    exact h2
  have hE : ∀ E ∈ (Finset.range K).powerset, (-1 : ℝ) ^ E.card *
        ∑' h : ℕ, (ω (m E + h + 1) : ℝ) / 2 ^ (h + 1)
      = (∑ h ∈ Finset.range (K + H), (-1 : ℝ) ^ E.card *
          ((ω (p E * (m E + h + 1)) : ℝ) / 2 ^ (h + 1))
        + (-1 : ℝ) ^ E.card *
          (∑' h : ℕ, (ω (p E * (m E + (h + (K + H)) + 1)) : ℝ) / 2 ^ (h + (K + H) + 1)
            + ∑' h : ℕ, (if p E ^ 2 ∣ p E * (m E + h + 1) then (1 : ℝ) else 0) / 2 ^ (h + 1)))
        - (-1 : ℝ) ^ E.card := by
    intro E hE
    obtain ⟨hW, _, hT⟩ := tail_dilate (m := m E) (hp E hE)
    rw [hT, ← hW.sum_add_tsum_nat_add (K + H), ← Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl hE, Finset.sum_sub_distrib, hsign, sub_zero, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm, Finset.sum_range_add]
  have hzero : ∑ h ∈ Finset.range K, ∑ E ∈ (Finset.range K).powerset, (-1 : ℝ) ^ E.card *
      ((ω (p E * (m E + h + 1)) : ℝ) / 2 ^ (h + 1)) = 0 := by
    refine Finset.sum_eq_zero fun h hh => ?_
    exact cube_cancel K (fun E => (ω (p E * (m E + h + 1)) : ℝ) / 2 ^ (h + 1)) h
      (Finset.mem_range.mp hh) (fun E hE => by
        rw [hsym E hE h (Finset.mem_range.mp hh)])
  rw [hzero, zero_add, Finset.sum_product, Finset.sum_comm]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [Finset.sum_Ico_eq_sum_range]
  have hH : K + H + 1 - (K + 1) = H := by omega
  rw [hH]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show m E + (K + i) + 1 = m E + (K + 1 + i) by ring, show K + i + 1 = K + 1 + i by ring]
  ring

lemma vertex_arith (P n : ℕ) (s : ℤ) (hP : 0 < P) (hs : s < n) (hc : (n : ℤ) ≡ s [ZMOD P])
    (h : ℕ) : ((P * ((((n : ℤ) - s) / P).toNat + h + 1) : ℕ) : ℤ)
      = n + ((P : ℤ) * ((h + 1 : ℕ) : ℤ) - s) := by
  have hdvd : (P : ℤ) ∣ (n : ℤ) - s := Int.modEq_iff_dvd.mp hc.symm
  obtain ⟨t, ht⟩ := hdvd
  have hPz : (0 : ℤ) < P := by exact_mod_cast hP
  have htpos : 0 < t := by
    by_contra hneg
    have h1 : t ≤ 0 := not_lt.mp hneg
    have h2 : (P : ℤ) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hPz.le h1
    linarith
  have hdiv : ((n : ℤ) - s) / P = t := by
    rw [ht]; exact Int.mul_ediv_cancel_left t hPz.ne'
  rw [hdiv]
  push_cast
  rw [Int.toNat_of_nonneg htpos.le]
  linear_combination (-1 : ℤ) * ht

lemma geom_one (K H : ℕ) :
    ∑ h ∈ Finset.Ico (K + 1) (K + H + 1), (2 : ℝ) ^ K / 2 ^ h = 1 - 1 / 2 ^ H := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [show K + (H + 1) + 1 = (K + H + 1) + 1 by ring, Finset.sum_Ico_succ_top (by omega), ih,
      show K + H + 1 = K + (H + 1) by ring, pow_add (2 : ℝ) K (H + 1), pow_succ (2 : ℝ) H]
    field_simp
    ring

lemma geom_two (K H : ℕ) :
    ∑ h ∈ Finset.Ico (K + 1) (K + H + 1), (2 : ℝ) ^ K / (2 ^ h) ^ 2
      = (1 - 1 / (2 ^ H) ^ 2) / (3 * 2 ^ K) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [show K + (H + 1) + 1 = (K + H + 1) + 1 by ring, Finset.sum_Ico_succ_top (by omega), ih,
      show K + H + 1 = K + (H + 1) by ring, pow_add (2 : ℝ) K (H + 1), pow_succ (2 : ℝ) H]
    field_simp
    ring

lemma omega_split (k : ℕ) (R y : ℝ) (hRy : R ≤ y) :
    (ω k : ℝ) = ((k.primeFactors.filter (fun ℓ : ℕ => (ℓ : ℝ) ≤ R)).card : ℝ)
      + ((k.primeFactors.filter (fun ℓ : ℕ => R < ℓ ∧ (ℓ : ℝ) ≤ y)).card : ℝ)
      + ((k.primeFactors.filter (fun ℓ : ℕ => y < ℓ)).card : ℝ) := by
  rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
  have h1 := Finset.card_filter_add_card_filter_not (s := k.primeFactors)
    (fun ℓ : ℕ => (ℓ : ℝ) ≤ R)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := k.primeFactors.filter (fun ℓ : ℕ => ¬ (ℓ : ℝ) ≤ R)) (fun ℓ : ℕ => (ℓ : ℝ) ≤ y)
  have e1 : (k.primeFactors.filter (fun ℓ : ℕ => ¬ (ℓ : ℝ) ≤ R)).filter (fun ℓ : ℕ => (ℓ : ℝ) ≤ y)
      = k.primeFactors.filter (fun ℓ : ℕ => R < ℓ ∧ (ℓ : ℝ) ≤ y) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun ℓ _ => ?_
    rw [not_le]
  have e2 : (k.primeFactors.filter (fun ℓ : ℕ => ¬ (ℓ : ℝ) ≤ R)).filter
      (fun ℓ : ℕ => ¬ (ℓ : ℝ) ≤ y) = k.primeFactors.filter (fun ℓ : ℕ => y < ℓ) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun ℓ _ => ?_
    rw [not_le, not_le]
    exact ⟨fun h => h.2, fun h => ⟨lt_of_le_of_lt hRy h, h⟩⟩
  rw [e1, e2] at h2
  rw [← h1, ← h2]
  push_cast
  ring


lemma sign_sum (K : ℕ) (hK : 0 < K) :
    ∑ E ∈ (Finset.range K).powerset, (-1 : ℝ) ^ E.card = 0 := by
  have := Finset.sum_powerset_neg_one_pow_card (α := ℕ) (x := Finset.range K)
  have hne : Finset.range K ≠ ∅ := by
    rw [← Finset.nonempty_iff_ne_empty]; exact Finset.nonempty_range_iff.mpr hK.ne'
  rw [if_neg hne] at this
  have h2 : ((∑ E ∈ (Finset.range K).powerset, (-1 : ℤ) ^ E.card : ℤ) : ℝ) = 0 := by
    rw [this]; simp
  push_cast at h2
  exact h2

lemma ind_div_nonneg (P : Prop) [Decidable P] (h : ℕ) :
    (0 : ℝ) ≤ (if P then (1 : ℝ) else 0) / 2 ^ (h + 1) := by
  split_ifs <;> positivity

/-- The combinatorial core: for a fixed cube of primes and a fixed finite set of integers,
the three analytic inputs give weights, an integer combination of tails and a large good set. -/
lemma core (q K H : ℕ) (N : Finset ℕ) (p : Finset ℕ → ℕ) (s : Finset ℕ → ℤ)
    (r : Finset ℕ → ℕ → ℤ) (y R η : ℝ) (S : Finset (Finset ℕ × ℕ))
    (hS : S = (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1))
    (hr : ∀ E h, r E h = (p E : ℤ) * (h : ℤ) - s E)
    (hq : 0 < q) (hK : 0 < K) (hRy : R ≤ y) (hKη : 1 / 2 ^ K ≤ η)
    (hp : ∀ E ∈ (Finset.range K).powerset, (p E).Prime)
    (hsym : ∀ E ∈ (Finset.range K).powerset, ∀ k < K,
      r (symmDiff E {k}) (k + 1) = r E (k + 1))
    (hinj : Set.InjOn (fun a : Finset ℕ × ℕ => r a.1 a.2) (S : Set (Finset ℕ × ℕ)))
    (hcong : ∀ n ∈ N, ∀ E ∈ (Finset.range K).powerset, (n : ℤ) ≡ s E [ZMOD p E] ∧ s E < n)
    (h1 : ∃ A : Finset ℕ, A.Nonempty ∧ A ⊆ N ∧ (N.card : ℝ) ≤ 10 * A.card ∧
      ∀ n ∈ A, ∀ z : ℤ, 1 / 10 ≤ |(q : ℝ) * (∑ a ∈ S, (-1) ^ a.1.card / 2 ^ a.2 *
          ((((n : ℤ) + r a.1 a.2).natAbs.primeFactors.filter
            (fun ℓ : ℕ => (ℓ : ℝ) ≤ R)).card : ℝ)) - z|)
    (h2 : ∑ n ∈ N, (∑ a ∈ S, (-1) ^ a.1.card / 2 ^ a.2 *
          ((((n : ℤ) + r a.1 a.2).natAbs.primeFactors.filter
            (fun ℓ : ℕ => R < ℓ ∧ (ℓ : ℝ) ≤ y)).card : ℝ)) ^ 2
      ≤ 1 / (64000 * (q : ℝ) ^ 2) * N.card)
    (h3 : ∑ n ∈ N, ∑ E ∈ (Finset.range K).powerset, ∑' h : ℕ,
        ((ω ((n : ℤ) + r E (h + K + H + 1)).natAbs : ℝ) / 2 ^ (h + K + H + 1)
          + (if (p E : ℤ) ^ 2 ∣ (n : ℤ) + r E (h + 1) then (1 : ℝ) else 0) / 2 ^ (h + 1))
      ≤ 1 / (1600 * (q : ℝ)) * N.card) :
    ∃ (w : ℤ → ℝ) (Z : ℕ → ℝ),
      ∑ ρ ∈ S.image (fun a : Finset ℕ × ℕ => r a.1 a.2), w ρ = 0 ∧
      ∑ ρ ∈ S.image (fun a : Finset ℕ × ℕ => r a.1 a.2), |w ρ| ≤ 1 ∧
      ∑ ρ ∈ S.image (fun a : Finset ℕ × ℕ => r a.1 a.2), w ρ ^ 2 ≤ η ∧
      (∀ n : ℕ, ∃ (M : Finset ℕ) (a : ℕ → ℤ), Z n = ∑ m ∈ M, (a m : ℝ) *
        ∑' h : ℕ, (ω (m + h + 1) : ℝ) / 2 ^ (h + 1)) ∧
      ∃ A : Finset ℕ, A.Nonempty ∧ A ⊆ N ∧ 1 / 20 * (N.card : ℝ) ≤ A.card ∧
        ∀ n ∈ A, ∀ z : ℤ, 1 / 20 ≤ |(q : ℝ) * (Z n -
          ∑ ρ ∈ S.image (fun a : Finset ℕ × ℕ => r a.1 a.2), w ρ *
          ((((n : ℤ) + ρ).natAbs.primeFactors.filter (fun ℓ : ℕ => y < ℓ)).card : ℝ)) - z| := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hfinj : ∀ a ∈ S, ∀ b ∈ S, r a.1 a.2 = r b.1 b.2 → a = b := fun a ha b hb h =>
    hinj (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) h
  obtain ⟨wt, hwt⟩ : ∃ wt : Finset ℕ × ℕ → ℝ, ∀ a, wt a = (-1) ^ a.1.card / 2 ^ a.2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : ℤ → ℝ, ∀ ρ, w ρ = ∑ a ∈ S.filter (fun a => r a.1 a.2 = ρ), wt a :=
    ⟨_, fun _ => rfl⟩
  have hw : ∀ a ∈ S, w (r a.1 a.2) = wt a := by
    intro a ha
    have hfil : S.filter (fun a' => r a'.1 a'.2 = r a.1 a.2) = {a} := by
      ext a'
      simp only [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun h => hfinj a' h.1 a ha h.2, fun h => by rw [h]; exact ⟨ha, rfl⟩⟩
    rw [hwdef, hfil, Finset.sum_singleton]
  have himg : ∀ G : ℤ → ℝ, ∑ ρ ∈ S.image (fun a : Finset ℕ × ℕ => r a.1 a.2), G ρ
      = ∑ a ∈ S, G (r a.1 a.2) := fun G => Finset.sum_image hinj
  have hsign := sign_sum K hK
  have hcardC : (((Finset.range K).powerset.card : ℕ) : ℝ) = 2 ^ K := by
    rw [Finset.card_powerset, Finset.card_range]
    push_cast
    rfl
  have habs : ∀ a, |wt a| = 1 / 2 ^ a.2 := by
    intro a
    rw [hwt, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (by positivity)]
  have hsum0 : ∑ a ∈ S, wt a = 0 := by
    rw [hS, Finset.sum_product]
    have : ∀ E ∈ (Finset.range K).powerset, ∑ h ∈ Finset.Ico (K + 1) (K + H + 1), wt (E, h)
        = (-1 : ℝ) ^ E.card * ∑ h ∈ Finset.Ico (K + 1) (K + H + 1), 1 / (2 : ℝ) ^ h := by
      intro E _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [hwt]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, hsign, zero_mul]
  have hsum1 : ∑ a ∈ S, |wt a| ≤ 1 := by
    rw [hS, Finset.sum_product]
    have : ∀ E ∈ (Finset.range K).powerset, ∑ h ∈ Finset.Ico (K + 1) (K + H + 1), |wt (E, h)|
        = ∑ h ∈ Finset.Ico (K + 1) (K + H + 1), 1 / (2 : ℝ) ^ h := by
      intro E _
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [habs]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hcardC, Finset.mul_sum]
    have e : ∑ h ∈ Finset.Ico (K + 1) (K + H + 1), (2 : ℝ) ^ K * (1 / 2 ^ h)
        = ∑ h ∈ Finset.Ico (K + 1) (K + H + 1), (2 : ℝ) ^ K / 2 ^ h :=
      Finset.sum_congr rfl fun h _ => by ring
    rw [e, geom_one]
    have : (0 : ℝ) < 1 / 2 ^ H := by positivity
    linarith
  have hsum2 : ∑ a ∈ S, wt a ^ 2 ≤ η := by
    rw [hS, Finset.sum_product]
    have : ∀ E ∈ (Finset.range K).powerset, ∑ h ∈ Finset.Ico (K + 1) (K + H + 1), wt (E, h) ^ 2
        = ∑ h ∈ Finset.Ico (K + 1) (K + H + 1), 1 / ((2 : ℝ) ^ h) ^ 2 := by
      intro E _
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [← sq_abs, habs, div_pow, one_pow]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hcardC, Finset.mul_sum]
    have e : ∑ h ∈ Finset.Ico (K + 1) (K + H + 1), (2 : ℝ) ^ K * (1 / (2 ^ h) ^ 2)
        = ∑ h ∈ Finset.Ico (K + 1) (K + H + 1), (2 : ℝ) ^ K / (2 ^ h) ^ 2 :=
      Finset.sum_congr rfl fun h _ => by ring
    rw [e, geom_two]
    refine le_trans ?_ hKη
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1' : (0 : ℝ) < 1 / (2 ^ H) ^ 2 := by positivity
    have h2' : (0 : ℝ) < 2 ^ K := by positivity
    nlinarith
  -- the integer combination of tails
  obtain ⟨mE, hmE⟩ : ∃ mE : ℕ → Finset ℕ → ℕ,
      ∀ n E, mE n E = (((n : ℤ) - s E) / (p E : ℤ)).toNat := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℕ → ℝ, ∀ n, Z n = ∑ E ∈ (Finset.range K).powerset, (-1 : ℝ) ^ E.card *
      ∑' h : ℕ, (ω (mE n E + h + 1) : ℝ) / 2 ^ (h + 1) := ⟨_, fun _ => rfl⟩
  have hZint : ∀ n : ℕ, ∃ (M : Finset ℕ) (a : ℕ → ℤ), Z n = ∑ m ∈ M, (a m : ℝ) *
      ∑' h : ℕ, (ω (m + h + 1) : ℝ) / 2 ^ (h + 1) := by
    intro n
    refine ⟨(Finset.range K).powerset.image (mE n), fun k =>
      ∑ E ∈ (Finset.range K).powerset.filter (fun E => mE n E = k), (-1 : ℤ) ^ E.card, ?_⟩
    rw [hZ, ← Finset.sum_fiberwise_of_maps_to (g := mE n)
      (t := (Finset.range K).powerset.image (mE n)) (fun E hE => Finset.mem_image_of_mem _ hE)]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun E hE => ?_
    rw [(Finset.mem_filter.mp hE).2]
  have hN : ∀ n ∈ N, ∀ E ∈ (Finset.range K).powerset, ∀ h : ℕ,
      ((p E * (mE n E + h + 1) : ℕ) : ℤ) = (n : ℤ) + r E (h + 1) := by
    intro n hn E hE h
    obtain ⟨hc, hlt⟩ := hcong n hn E hE
    rw [hmE, hr]
    exact vertex_arith (p E) n (s E) (hp E hE).pos hlt hc h
  have hsymN : ∀ n ∈ N, ∀ E ∈ (Finset.range K).powerset, ∀ h < K,
      p (symmDiff E {h}) * (mE n (symmDiff E {h}) + h + 1) = p E * (mE n E + h + 1) := by
    intro n hn E hE h hh
    have hE' : symmDiff E {h} ∈ (Finset.range K).powerset := by
      rw [Finset.mem_powerset] at hE ⊢
      intro a ha
      rcases Finset.mem_symmDiff.mp ha with ⟨ha, _⟩ | ⟨ha, _⟩
      · exact hE ha
      · rw [Finset.mem_singleton] at ha
        exact ha ▸ Finset.mem_range.mpr hh
    have e1 := hN n hn _ hE' h
    have e2 := hN n hn E hE h
    rw [hsym E hE h hh, ← e2] at e1
    exact_mod_cast e1
  -- the three pieces
  obtain ⟨A1, hA1⟩ : ∃ A1 : ℕ → ℝ, ∀ n, A1 n = ∑ a ∈ S, (-1) ^ a.1.card / 2 ^ a.2 *
      ((((n : ℤ) + r a.1 a.2).natAbs.primeFactors.filter
        (fun ℓ : ℕ => (ℓ : ℝ) ≤ R)).card : ℝ) := ⟨_, fun _ => rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A2 : ℕ → ℝ, ∀ n, A2 n = ∑ a ∈ S, (-1) ^ a.1.card / 2 ^ a.2 *
      ((((n : ℤ) + r a.1 a.2).natAbs.primeFactors.filter
        (fun ℓ : ℕ => R < ℓ ∧ (ℓ : ℝ) ≤ y)).card : ℝ) := ⟨_, fun _ => rfl⟩
  obtain ⟨A3, hA3⟩ : ∃ A3 : ℕ → ℝ, ∀ n, A3 n = ∑ E ∈ (Finset.range K).powerset,
      (-1 : ℝ) ^ E.card *
      (∑' h : ℕ, (ω (p E * (mE n E + (h + (K + H)) + 1)) : ℝ) / 2 ^ (h + (K + H) + 1)
        + ∑' h : ℕ, (if p E ^ 2 ∣ p E * (mE n E + h + 1) then (1 : ℝ) else 0) / 2 ^ (h + 1)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨T3, hT3⟩ : ∃ T3 : ℕ → ℝ, ∀ n, T3 n = ∑ E ∈ (Finset.range K).powerset, ∑' h : ℕ,
      ((ω ((n : ℤ) + r E (h + K + H + 1)).natAbs : ℝ) / 2 ^ (h + K + H + 1)
        + (if (p E : ℤ) ^ 2 ∣ (n : ℤ) + r E (h + 1) then (1 : ℝ) else 0) / 2 ^ (h + 1)) :=
    ⟨_, fun _ => rfl⟩
  have hid : ∀ n ∈ N, Z n - ∑ ρ ∈ S.image (fun a : Finset ℕ × ℕ => r a.1 a.2), w ρ *
      ((((n : ℤ) + ρ).natAbs.primeFactors.filter (fun ℓ : ℕ => y < ℓ)).card : ℝ)
      = A1 n + A2 n + A3 n := by
    intro n hn
    rw [hZ, pointwise K H hK p (mE n) hp (hsymN n hn), ← hS,
      himg (fun ρ => w ρ * ((((n : ℤ) + ρ).natAbs.primeFactors.filter
        (fun ℓ : ℕ => y < ℓ)).card : ℝ))]
    have hnear : ∑ a ∈ S, (-1 : ℝ) ^ a.1.card / 2 ^ a.2 * (ω (p a.1 * (mE n a.1 + a.2)) : ℝ)
        = A1 n + A2 n + ∑ a ∈ S, w (r a.1 a.2) *
          ((((n : ℤ) + r a.1 a.2).natAbs.primeFactors.filter (fun ℓ : ℕ => y < ℓ)).card : ℝ) := by
      rw [hA1, hA2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha' := ha
      rw [hS] at ha'
      obtain ⟨haE, hah⟩ := Finset.mem_product.mp ha'
      have hpos : 1 ≤ a.2 := by
        have := (Finset.mem_Ico.mp hah).1
        omega
      have hnat : p a.1 * (mE n a.1 + a.2) = ((n : ℤ) + r a.1 a.2).natAbs := by
        have e := hN n hn a.1 haE (a.2 - 1)
        rw [show a.2 - 1 + 1 = a.2 by omega,
          show mE n a.1 + (a.2 - 1) + 1 = mE n a.1 + a.2 by omega] at e
        rw [← e, Int.natAbs_natCast]
      rw [hnat, omega_split _ R y hRy, hw a ha, hwt]
      ring
    rw [hnear, hA3]
    ring
  have hA3le : ∀ n ∈ N, |A3 n| ≤ T3 n := by
    intro n hn
    rw [hA3, hT3]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun E hE => ?_)
    obtain ⟨hW, hI, _⟩ := tail_dilate (m := mE n E) (hp E hE)
    have hWs := (summable_nat_add_iff (K + H)).mpr hW
    have hterm : ∀ h : ℕ, ((ω ((n : ℤ) + r E (h + K + H + 1)).natAbs : ℝ) / 2 ^ (h + K + H + 1)
          + (if (p E : ℤ) ^ 2 ∣ (n : ℤ) + r E (h + 1) then (1 : ℝ) else 0) / 2 ^ (h + 1))
        = (ω (p E * (mE n E + (h + (K + H)) + 1)) : ℝ) / 2 ^ (h + (K + H) + 1)
          + (if p E ^ 2 ∣ p E * (mE n E + h + 1) then (1 : ℝ) else 0) / 2 ^ (h + 1) := by
      intro h
      have e1 := hN n hn E hE (h + (K + H))
      have e2 := hN n hn E hE h
      have hd : ((p E : ℤ) ^ 2 ∣ ((p E * (mE n E + h + 1) : ℕ) : ℤ))
          ↔ p E ^ 2 ∣ p E * (mE n E + h + 1) := by
        rw [← Int.natCast_dvd_natCast]
        push_cast
        rfl
      rw [show h + K + H + 1 = h + (K + H) + 1 by ring, ← e1, ← e2, Int.natAbs_natCast]
      simp only [hd]
    rw [tsum_congr hterm, hWs.tsum_add hI, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact le_of_eq (abs_of_nonneg (add_nonneg (tsum_nonneg fun _ => by positivity)
      (tsum_nonneg fun h => ind_div_nonneg _ h)))
  -- Markov bounds for the two small pieces
  obtain ⟨A, hAne, hAN, hAcard, hAfar⟩ := h1
  have hNpos : (0 : ℝ) < N.card := by
    exact_mod_cast Finset.card_pos.mpr (hAne.mono hAN)
  obtain ⟨B2, hB2⟩ : ∃ B2 : Finset ℕ, B2 = N.filter (fun n => 1 / (40 * (q : ℝ)) ≤ |A2 n|) :=
    ⟨_, rfl⟩
  obtain ⟨B3, hB3⟩ : ∃ B3 : Finset ℕ, B3 = N.filter (fun n => 1 / (40 * (q : ℝ)) ≤ |A3 n|) :=
    ⟨_, rfl⟩
  have hB2sub : B2 ⊆ N := hB2 ▸ Finset.filter_subset _ _
  have hB3sub : B3 ⊆ N := hB3 ▸ Finset.filter_subset _ _
  have hu : (0 : ℝ) < 1 / (q : ℝ) := by positivity
  have hB2card : (B2.card : ℝ) ≤ N.card / 40 := by
    have h2' : ∑ n ∈ N, A2 n ^ 2 ≤ 1 / (64000 * (q : ℝ) ^ 2) * N.card := by
      simp only [hA2]
      exact h2
    have hlow : (B2.card : ℝ) * (1 / (40 * (q : ℝ))) ^ 2 ≤ ∑ n ∈ N, A2 n ^ 2 := by
      calc (B2.card : ℝ) * (1 / (40 * (q : ℝ))) ^ 2
          = ∑ _n ∈ B2, (1 / (40 * (q : ℝ))) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ n ∈ B2, A2 n ^ 2 := Finset.sum_le_sum fun n hn => by
            rw [hB2] at hn
            have := (Finset.mem_filter.mp hn).2
            rw [← sq_abs (A2 n)]
            exact pow_le_pow_left₀ (by positivity) this 2
        _ ≤ ∑ n ∈ N, A2 n ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hB2sub (fun _ _ _ => sq_nonneg _)
    have h := hlow.trans h2'
    have e1 : (1 / (40 * (q : ℝ))) ^ 2 = (1 / (q : ℝ)) ^ 2 * (1 / 1600) := by
      field_simp
      ring
    have e2 : 1 / (64000 * (q : ℝ) ^ 2) = (1 / (q : ℝ)) ^ 2 * (1 / 64000) := by
      field_simp
    rw [e1, e2] at h
    have hu2 : (0 : ℝ) < (1 / (q : ℝ)) ^ 2 := by positivity
    have h' : (1 / (q : ℝ)) ^ 2 * ((B2.card : ℝ) / 1600)
        ≤ (1 / (q : ℝ)) ^ 2 * ((N.card : ℝ) / 64000) := by
      calc (1 / (q : ℝ)) ^ 2 * ((B2.card : ℝ) / 1600)
          = (B2.card : ℝ) * ((1 / (q : ℝ)) ^ 2 * (1 / 1600)) := by ring
        _ ≤ (1 / (q : ℝ)) ^ 2 * (1 / 64000) * N.card := h
        _ = (1 / (q : ℝ)) ^ 2 * ((N.card : ℝ) / 64000) := by ring
    have := le_of_mul_le_mul_left h' hu2
    linarith
  have hB3card : (B3.card : ℝ) ≤ N.card / 40 := by
    have h3' : ∑ n ∈ N, T3 n ≤ 1 / (1600 * (q : ℝ)) * N.card := by
      simp only [hT3]
      exact h3
    have hlow : (B3.card : ℝ) * (1 / (40 * (q : ℝ))) ≤ ∑ n ∈ N, T3 n := by
      calc (B3.card : ℝ) * (1 / (40 * (q : ℝ)))
          = ∑ _n ∈ B3, (1 / (40 * (q : ℝ))) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ n ∈ B3, T3 n := Finset.sum_le_sum fun n hn => by
            have hnN := hB3sub hn
            rw [hB3] at hn
            exact ((Finset.mem_filter.mp hn).2).trans (hA3le n hnN)
        _ ≤ ∑ n ∈ N, T3 n := Finset.sum_le_sum_of_subset_of_nonneg hB3sub
            (fun n hn _ => (abs_nonneg _).trans (hA3le n hn))
    have h := hlow.trans h3'
    have e1 : 1 / (40 * (q : ℝ)) = 1 / (q : ℝ) * (1 / 40) := by
      field_simp
    have e2 : 1 / (1600 * (q : ℝ)) = 1 / (q : ℝ) * (1 / 1600) := by
      field_simp
    rw [e1, e2] at h
    have h' : 1 / (q : ℝ) * ((B3.card : ℝ) / 40) ≤ 1 / (q : ℝ) * ((N.card : ℝ) / 1600) := by
      calc 1 / (q : ℝ) * ((B3.card : ℝ) / 40)
          = (B3.card : ℝ) * (1 / (q : ℝ) * (1 / 40)) := by ring
        _ ≤ 1 / (q : ℝ) * (1 / 1600) * N.card := h
        _ = 1 / (q : ℝ) * ((N.card : ℝ) / 1600) := by ring
    have := le_of_mul_le_mul_left h' hu
    linarith
  have hcard : 1 / 20 * (N.card : ℝ) ≤ ((A \ (B2 ∪ B3)).card : ℝ) := by
    have c1 : (A.card : ℝ) ≤ ((A \ (B2 ∪ B3)).card : ℝ) + ((B2 ∪ B3).card : ℝ) := by
      exact_mod_cast Finset.card_le_card_sdiff_add_card
    have c2 : (((B2 ∪ B3).card : ℕ) : ℝ) ≤ (B2.card : ℝ) + B3.card := by
      exact_mod_cast Finset.card_union_le B2 B3
    linarith
  refine ⟨w, Z, ?_, ?_, ?_, hZint, A \ (B2 ∪ B3), ?_, ?_, hcard, ?_⟩
  · rw [himg, Finset.sum_congr rfl hw]
    exact hsum0
  · rw [himg (fun ρ => |w ρ|), Finset.sum_congr rfl (fun a ha => by rw [hw a ha])]
    exact hsum1
  · rw [himg (fun ρ => w ρ ^ 2), Finset.sum_congr rfl (fun a ha => by rw [hw a ha])]
    exact hsum2
  · refine Finset.card_pos.mp ?_
    have : (0 : ℝ) < ((A \ (B2 ∪ B3)).card : ℝ) := lt_of_lt_of_le (by positivity) hcard
    exact_mod_cast this
  · exact Finset.sdiff_subset.trans hAN
  · intro n hn z
    obtain ⟨hnA, hnB⟩ := Finset.mem_sdiff.mp hn
    have hnN := hAN hnA
    have hn2 : |A2 n| < 1 / (40 * (q : ℝ)) := by
      by_contra hcon
      exact hnB (Finset.mem_union_left _ (hB2 ▸ Finset.mem_filter.mpr ⟨hnN, not_lt.mp hcon⟩))
    have hn3 : |A3 n| < 1 / (40 * (q : ℝ)) := by
      by_contra hcon
      exact hnB (Finset.mem_union_right _ (hB3 ▸ Finset.mem_filter.mpr ⟨hnN, not_lt.mp hcon⟩))
    have hfar := hAfar n hnA z
    rw [← hA1] at hfar
    rw [hid n hnN]
    have hq2 : (q : ℝ) * |A2 n| < 1 / 40 := by
      have := mul_lt_mul_of_pos_left hn2 hqR
      have e : (q : ℝ) * (1 / (40 * (q : ℝ))) = 1 / 40 := by
        field_simp
      linarith
    have hq3 : (q : ℝ) * |A3 n| < 1 / 40 := by
      have := mul_lt_mul_of_pos_left hn3 hqR
      have e : (q : ℝ) * (1 / (40 * (q : ℝ))) = 1 / 40 := by
        field_simp
      linarith
    have htri : |(q : ℝ) * A1 n - z| ≤ |(q : ℝ) * (A1 n + A2 n + A3 n) - z|
        + (q : ℝ) * |A2 n| + (q : ℝ) * |A3 n| := by
      calc |(q : ℝ) * A1 n - z|
          = |((q : ℝ) * (A1 n + A2 n + A3 n) - z) + (-((q : ℝ) * A2 n)) + (-((q : ℝ) * A3 n))| := by
            congr 1
            ring
        _ ≤ |(q : ℝ) * (A1 n + A2 n + A3 n) - z| + |(-((q : ℝ) * A2 n))|
            + |(-((q : ℝ) * A3 n))| := abs_add_three _ _ _
        _ = _ := by rw [abs_neg, abs_neg, abs_mul, abs_mul, abs_of_pos hqR]
    linarith


lemma four_exp_sqrt_le (x : ℕ) (hx : 16 ≤ x) :
    4 * Real.exp (Real.sqrt (Real.log (Real.log x))) ≤ x := by
  have hx16 : (16 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hu2 : 2 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have h1 := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [e]
    nlinarith
  have hlog : Real.log (Real.log x) ≤ Real.log x - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hsqrt : Real.sqrt (Real.log (Real.log x)) ≤ Real.log x / 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by linarith, ?_⟩
    nlinarith [sq_nonneg (Real.log x - 2)]
  have ht : Real.exp (Real.log x / 2) * Real.exp (Real.log x / 2) = x := by
    rw [← Real.exp_add, show Real.log x / 2 + Real.log x / 2 = Real.log x by ring]
    exact Real.exp_log hx0
  have hle : Real.exp (Real.sqrt (Real.log (Real.log x))) ≤ Real.exp (Real.log x / 2) :=
    Real.exp_le_exp.mpr hsqrt
  have htpos := Real.exp_pos (Real.log x / 2)
  have ht4 : 4 ≤ Real.exp (Real.log x / 2) := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith
  nlinarith

lemma small_rpow_le (x : ℕ) (hx : ⌈Real.exp (Real.exp 15)⌉₊ ≤ x) :
    (x : ℝ) ^ (1 / Real.log (Real.log x) ^ 2) ≤ (x : ℝ) ^ (1 / 200 : ℝ) := by
  have hxr : Real.exp (Real.exp 15) ≤ x :=
    (Nat.le_ceil _).trans (by exact_mod_cast hx)
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxr
  have h1 : Real.exp 15 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxr
  have h2 : 15 ≤ Real.log (Real.log x) :=
    (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) h1)).mpr h1
  have hx1 : (1 : ℝ) ≤ x := by
    have : (1 : ℝ) ≤ Real.exp (Real.exp 15) := Real.one_le_exp (Real.exp_pos _).le
    linarith
  refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos69_erdos_69_R1.H1 := by
  intro k1 k2 k3 k4 q hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨1 / 20, by norm_num, fun η hη => ?_⟩
  obtain ⟨X1, hX1⟩ := k1 (min η (1 / 2)) (lt_min hη (by norm_num))
  obtain ⟨X2, hX2⟩ := k2 q hq
  obtain ⟨X3, hX3⟩ := k3 (1 / (64000 * (q : ℝ) ^ 2)) (by positivity)
  obtain ⟨X4, hX4⟩ := k4 (1 / (1600 * (q : ℝ))) (by positivity)
  refine ⟨max (max X1 X2) (max (max X3 X4) (max 16 ⌈Real.exp (Real.exp 15)⌉₊)),
    fun x hx y hy1 hy2 => ?_⟩
  have hx1 : X1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : X2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : X3 ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have hx4 : X4 ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have hx16 : 16 ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have hxE : ⌈Real.exp (Real.exp 15)⌉₊ ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  obtain ⟨K, H, Q, b, p, s, hdata⟩ := hX1 x hx1
  dsimp only at hdata
  obtain ⟨hKe, hHe, hE, hpinj, hW, hQ, hWb, hKη, hQB, hsB, hrB⟩ := hdata
  have h2 := hX2 x hx2 K H Q b p s
  have h3 := hX3 x hx3 y hy2 K H Q b p s
  have h4 := hX4 x hx4 K H Q b p s
  dsimp only at h2 h3 h4
  have h2' := h2 hKe hHe hE hpinj hW hQ hWb
  have h3' := h3 hKe hHe hE hpinj hW hQ hWb
  have h4' := h4 hKe hHe hE hpinj hW hQ hWb
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h] at hKη
      have := hKη.trans (min_le_right _ _)
      norm_num at this
    · exact h
  have hB4 := four_exp_sqrt_le x hx16
  have hx16R : (16 : ℝ) ≤ x := by exact_mod_cast hx16
  have hRy : (x : ℝ) ^ (1 / Real.log (Real.log x) ^ 2) ≤ y := (small_rpow_le x hxE).trans hy1
  have hpQ : ∀ E ∈ (Finset.range K).powerset, p E ∣ Q := by
    intro E hE'
    rw [hQ]
    exact (Finset.dvd_prod_of_mem p hE').mul_right _
  have hQpos : 0 < Q := by
    rw [hQ]
    exact Nat.mul_pos (Finset.prod_pos fun E hE' => (hE E hE').1.pos)
      (Finset.prod_pos fun ℓ hℓ =>
        pow_pos (Nat.pos_of_mem_primeFactors (Finset.mem_sdiff.mp hℓ).1) _)
  have hcong : ∀ n ∈ (Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q),
      ∀ E ∈ (Finset.range K).powerset, (n : ℤ) ≡ s E [ZMOD p E] ∧ s E < n := by
    intro n hn E hE'
    obtain ⟨hnI, hnQ⟩ := Finset.mem_filter.mp hn
    constructor
    · have hnb : (n : ℤ) ≡ b [ZMOD Q] := Int.natCast_modEq_iff.mpr hnQ
      exact (hnb.of_dvd (Int.natCast_dvd_natCast.mpr (hpQ E hE'))).trans (hE E hE').2.2.2.2.1
    · have hsE := hsB E hE'
      have hn2 : x ≤ 2 * n + 1 := by
        have := (Finset.mem_Icc.mp hnI).1
        omega
      have hn2R : (x : ℝ) ≤ 2 * n + 1 := by exact_mod_cast hn2
      have hlt : (s E : ℝ) < n := by
        have := le_abs_self (s E : ℝ)
        have hpos := Real.exp_pos (Real.sqrt (Real.log (Real.log x)))
        linarith
      exact_mod_cast hlt
  have hinj : Set.InjOn (fun a : Finset ℕ × ℕ => (p a.1 : ℤ) * (a.2 : ℤ) - s a.1)
      (((Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1) :
        Finset (Finset ℕ × ℕ)) : Set (Finset ℕ × ℕ)) := by
    intro a ha c hc hac
    by_contra hne
    have hmem : (a, c) ∈ ((Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1)).offDiag :=
      Finset.mem_offDiag.mpr ⟨Finset.mem_coe.mp ha, Finset.mem_coe.mp hc, hne⟩
    have := Finset.prod_ne_zero_iff.mp hW (a, c) hmem
    apply this
    rw [Int.natAbs_eq_zero]
    exact sub_eq_zero.mpr hac
  obtain ⟨w, Z, hw0, hw1, hw2, hZ, A, hAne, hAN, hAc, hAfar⟩ :=
    core q K H ((Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q)) p s
      (fun E h => (p E : ℤ) * (h : ℤ) - s E) y ((x : ℝ) ^ (1 / Real.log (Real.log x) ^ 2)) η
      ((Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1)) rfl (fun _ _ => rfl)
      hq hK hRy (hKη.trans (min_le_left _ _)) (fun E hE' => (hE E hE').1)
      (fun E hE' => (hE E hE').2.2.2.2.2) hinj hcong h2' h3' h4'
  refine ⟨Q, b, ((Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1)).image
    (fun a : Finset ℕ × ℕ => (p a.1 : ℤ) * (a.2 : ℤ) - s a.1), w, Z, hQpos, hQB, ?_,
    hw0, hw1, hw2, hZ, A, hAne, hAN, hAc, hAfar⟩
  intro ρ hρ
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hρ
  exact hrB a ha


end OMA.R_Erdos69_erdos_69_R1_H1_R1
