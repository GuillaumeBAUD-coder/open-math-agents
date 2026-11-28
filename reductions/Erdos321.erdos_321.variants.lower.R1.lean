import FormalConjectures.ErdosProblems.«321»

-- Reduction Erdos321.erdos_321.variants.lower.R1 of Erdős Problem 321 — lower
-- Credit: @futurum-dev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- H1 (the Bleicher–Erdős construction, honest regime: every iterate log^[i] N, i ≤ k, is ≥ 1).
--   Stated for an ARBITRARY predicate P that contains ∅ and is closed under the prime-layer step
--     B ↦ B ∪ p • D   (p prime, p ∤ M where every b ∈ B divides M, D has distinct reciprocal
--                      subsums, every d ∈ D divides K, and K * Σ_{d∈D} 1/d < p).
--   So the solver only has to BUILD a big set by such steps; injectivity of the subsums is done
--   here once and for all (lemma `layer_step`: multiply the identity by p*M*K and reduce mod p).
-- H2 (the exceptional regime, pure real analysis): when some iterate log^[i] N (i ≤ k) is < 1,
--   the real-log orbit x ↦ log |x| must pass through a value of size ≤ exp(-e^k) to reach
--   log^[k] N ≥ k, which makes the tail of the product tiny; so the target is either below π(N),
--   or below the target at a smaller honest index j (where H1 applies).
-- main: honest case from H1 with P = distinct subsums; exceptional case from H2, using
--   R N ≥ π(N) (the primes ≤ N, built by `layer_step`) or the honest case at j.

namespace OMA.R_Erdos321_erdos_321_variants_lower_R1

def H1 : Prop :=
  ∀ N k : ℕ, 4 ≤ k → (k : ℝ) ≤ Real.log^[k] (N : ℝ) → (∀ i ≤ k, 1 ≤ Real.log^[i] (N : ℝ)) →
    ∀ P : Finset ℕ → Prop, P ∅ →
      (∀ (p M K : ℕ) (B D : Finset ℕ), p.Prime → 0 < M → 0 < K → (∀ b ∈ B, b ∣ M) → ¬ p ∣ M →
        (∀ d ∈ D, d ∣ K) → Set.InjOn (fun S : Finset ℕ => ∑ n ∈ S, (1 : ℚ) / n) D.powerset →
        (K : ℚ) * ∑ d ∈ D, (1 : ℚ) / d < p → P B → P (B ∪ D.image (p * ·))) →
      ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ P A ∧
        (N : ℝ) / Real.log N * ∏ i ∈ Finset.Icc 3 k, Real.log^[i] (N : ℝ) ≤ A.card

def H2 : Prop :=
  ∀ N k : ℕ, 4 ≤ k → (k : ℝ) ≤ Real.log^[k] (N : ℝ) → (∃ i ≤ k, Real.log^[i] (N : ℝ) < 1) →
    (N : ℝ) / Real.log N * ∏ i ∈ Finset.Icc 3 k, Real.log^[i] (N : ℝ) ≤ Nat.primeCounting N ∨
    ∃ j : ℕ, 4 ≤ j ∧ (j : ℝ) ≤ Real.log^[j] (N : ℝ) ∧ (∀ i ≤ j, 1 ≤ Real.log^[i] (N : ℝ)) ∧
      (N : ℝ) / Real.log N * ∏ i ∈ Finset.Icc 3 k, Real.log^[i] (N : ℝ) ≤
        (N : ℝ) / Real.log N * ∏ i ∈ Finset.Icc 3 j, Real.log^[i] (N : ℝ)

open Finset

lemma card_le_R {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N)
    (hinj : Set.InjOn (fun S : Finset ℕ => ∑ n ∈ S, (1 : ℚ) / n) A.powerset) :
    A.card ≤ Erdos321.R N := by
  unfold Erdos321.R
  refine le_csSup ⟨N, ?_⟩ ⟨A, hA, hinj, rfl⟩
  rintro n ⟨B, hB, -, rfl⟩
  simpa using Finset.card_le_card hB

lemma int_of_dvd (S : Finset ℕ) (M : ℕ) (h : ∀ b ∈ S, b ∣ M) :
    ∃ z : ℤ, (M : ℚ) * ∑ n ∈ S, (1 : ℚ) / n = z := by
  refine ⟨∑ b ∈ S, ((M / b : ℕ) : ℤ), ?_⟩
  rw [Finset.mul_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Int.cast_natCast]
  rcases Nat.eq_zero_or_pos b with h0 | hpos
  · subst h0; simp
  · rw [Nat.cast_div (h b hb) (by exact_mod_cast hpos.ne')]
    field_simp

lemma layer_step (p : ℕ) (hp : p.Prime) (B D : Finset ℕ) (M K : ℕ)
    (_hM : 0 < M) (hK : 0 < K) (hBM : ∀ b ∈ B, b ∣ M) (hpM : ¬ p ∣ M) (hDK : ∀ d ∈ D, d ∣ K)
    (hKD : (K : ℚ) * ∑ d ∈ D, (1 : ℚ) / d < p)
    (hB : Set.InjOn (fun S : Finset ℕ => ∑ n ∈ S, (1 : ℚ) / n) B.powerset)
    (hD : Set.InjOn (fun S : Finset ℕ => ∑ n ∈ S, (1 : ℚ) / n) D.powerset) :
    Set.InjOn (fun S : Finset ℕ => ∑ n ∈ S, (1 : ℚ) / n) (B ∪ D.image (p * ·)).powerset := by
  set rs : Finset ℕ → ℚ := fun S => ∑ n ∈ S, (1 : ℚ) / n with hrs
  have rs_nonneg : ∀ S, 0 ≤ rs S := fun S => Finset.sum_nonneg fun n _ => by positivity
  have rs_mono : ∀ {S T : Finset ℕ}, S ⊆ T → rs S ≤ rs T := fun h =>
    Finset.sum_le_sum_of_subset_of_nonneg h fun n _ _ => by positivity
  have hpB : ∀ b ∈ B, ¬ p ∣ b := fun b hb h => hpM (h.trans (hBM b hb))
  have key : ∀ S ⊆ B ∪ D.image (p * ·),
      rs S = rs (S.filter (· ∈ B)) + rs (D.filter (fun d => p * d ∈ S)) / p := by
    intro S hS
    have hsplit : S = S.filter (· ∈ B) ∪ (D.filter (fun d => p * d ∈ S)).image (p * ·) := by
      ext n
      simp only [mem_union, mem_filter, mem_image]
      constructor
      · intro hn
        by_cases hnB : n ∈ B
        · exact Or.inl ⟨hn, hnB⟩
        · right
          have := hS hn
          simp only [mem_union, mem_image] at this
          rcases this with h | ⟨d, hd, rfl⟩
          · exact absurd h hnB
          · exact ⟨d, ⟨hd, hn⟩, rfl⟩
      · rintro (⟨hn, _⟩ | ⟨d, ⟨_, hd⟩, rfl⟩)
        · exact hn
        · exact hd
    have hdisj : Disjoint (S.filter (· ∈ B)) ((D.filter (fun d => p * d ∈ S)).image (p * ·)) := by
      rw [Finset.disjoint_left]
      intro n hn hn'
      simp only [mem_filter, mem_image] at hn hn'
      obtain ⟨d, _, rfl⟩ := hn'
      exact hpB _ hn.2 (dvd_mul_right p d)
    conv_lhs => rw [hsplit]
    simp only [hrs]
    rw [Finset.sum_union hdisj, Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hp.pos h)]
    congr 1
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun d _ => ?_
    push_cast
    rcases Nat.eq_zero_or_pos d with h0 | _
    · subst h0; simp
    · field_simp
  intro S hS T hT hST
  simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at hS hT
  change rs S = rs T at hST
  rw [key S hS, key T hT] at hST
  set SB := S.filter (· ∈ B)
  set TB := T.filter (· ∈ B)
  set SD := D.filter (fun d => p * d ∈ S)
  set TD := D.filter (fun d => p * d ∈ T)
  obtain ⟨x, hx⟩ := int_of_dvd SB M fun b hb => hBM b (mem_filter.1 hb).2
  obtain ⟨y, hy⟩ := int_of_dvd TB M fun b hb => hBM b (mem_filter.1 hb).2
  obtain ⟨z, hz⟩ := int_of_dvd SD K fun d hd => hDK d (mem_filter.1 hd).1
  obtain ⟨w, hw⟩ := int_of_dvd TD K fun d hd => hDK d (mem_filter.1 hd).1
  change (M : ℚ) * rs SB = x at hx
  change (M : ℚ) * rs TB = y at hy
  change (K : ℚ) * rs SD = z at hz
  change (K : ℚ) * rs TD = w at hw
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have heq : ((p * K * (x - y) : ℤ) : ℚ) = ((M * (w - z) : ℤ) : ℚ) := by
    push_cast
    rw [← hx, ← hy, ← hz, ← hw]
    field_simp at hST
    linear_combination (K : ℚ) * (M : ℚ) * hST
  have heqZ : p * K * (x - y) = M * (w - z) := by exact_mod_cast heq
  have hdvd : (p : ℤ) ∣ w - z := by
    have : (p : ℤ) ∣ M * (w - z) := ⟨K * (x - y), by rw [← heqZ]; ring⟩
    rcases (Int.prime_iff_natAbs_prime.2 (by simpa using hp)).dvd_or_dvd this with h | h
    · exact absurd (Int.natCast_dvd_natCast.1 h) hpM
    · exact h
  have hSD : SD ⊆ D := filter_subset _ _
  have hTD : TD ⊆ D := filter_subset _ _
  have hbound : |((w - z : ℤ) : ℚ)| < p := by
    push_cast
    rw [← hz, ← hw, abs_lt]
    have h1 := rs_mono hSD; have h2 := rs_mono hTD
    have h3 := rs_nonneg SD; have h4 := rs_nonneg TD
    have hK' : (0 : ℚ) ≤ K := by positivity
    change (K : ℚ) * rs D < p at hKD
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1 hK', mul_le_mul_of_nonneg_left h2 hK',
      mul_nonneg hK' h3, mul_nonneg hK' h4]
  have hwz : w - z = 0 := by
    rcases hdvd with ⟨c, hc⟩
    rw [hc] at hbound
    push_cast at hbound
    rw [abs_mul, abs_of_pos (by exact_mod_cast hp.pos : (0:ℚ) < p)] at hbound
    have : |(c : ℚ)| < 1 := by
      have hp' : (0:ℚ) < p := by exact_mod_cast hp.pos
      nlinarith [abs_nonneg (c : ℚ)]
    have : c = 0 := by
      have : |c| < 1 := by exact_mod_cast this
      exact Int.abs_lt_one_iff.mp this
    simp [hc, this]
  have hK0 : (K : ℚ) ≠ 0 := by exact_mod_cast hK.ne'
  have hDeq : rs SD = rs TD := by
    have : (z : ℚ) = w := by
      have : z = w := by linarith
      rw [this]
    rw [← hz, ← hw] at this
    exact mul_left_cancel₀ hK0 this
  have hSDT : SD = TD := hD
    (by simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset]; exact hSD)
    (by simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset]; exact hTD) hDeq
  have hBeq : rs SB = rs TB := by
    rw [hDeq] at hST
    linarith
  have hSBT : SB = TB := hB
    (by simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset]
        exact fun n hn => (mem_filter.1 hn).2)
    (by simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset]
        exact fun n hn => (mem_filter.1 hn).2) hBeq
  ext n
  constructor
  · intro hn
    by_cases hnB : n ∈ B
    · have : n ∈ SB := mem_filter.2 ⟨hn, hnB⟩
      rw [hSBT] at this
      exact (mem_filter.1 this).1
    · have := hS hn
      simp only [mem_union, mem_image] at this
      rcases this with h | ⟨d, hd, rfl⟩
      · exact absurd h hnB
      · have : d ∈ SD := mem_filter.2 ⟨hd, hn⟩
        rw [hSDT] at this
        exact (mem_filter.1 this).2
  · intro hn
    by_cases hnB : n ∈ B
    · have : n ∈ TB := mem_filter.2 ⟨hn, hnB⟩
      rw [← hSBT] at this
      exact (mem_filter.1 this).1
    · have := hT hn
      simp only [mem_union, mem_image] at this
      rcases this with h | ⟨d, hd, rfl⟩
      · exact absurd h hnB
      · have : d ∈ TD := mem_filter.2 ⟨hd, hn⟩
        rw [← hSDT] at this
        exact (mem_filter.1 this).2

/-- The primes below `n` have distinct reciprocal subsums. -/
lemma primes_inj (n : ℕ) :
    Set.InjOn (fun S : Finset ℕ => ∑ m ∈ S, (1 : ℚ) / m) (Nat.primesBelow n).powerset := by
  induction n with
  | zero => simp [Nat.primesBelow, Set.InjOn]
  | succ n ih =>
    by_cases hn : n.Prime
    · have hset : Nat.primesBelow (n + 1) = Nat.primesBelow n ∪ ({1} : Finset ℕ).image (n * ·) := by
        ext m
        simp only [Nat.primesBelow, mem_filter, mem_range, mem_union, mem_image, mem_singleton]
        constructor
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | rfl
          · exact Or.inl ⟨h, h2⟩
          · exact Or.inr ⟨1, rfl, by ring⟩
        · rintro (⟨h1, h2⟩ | ⟨_, rfl, rfl⟩)
          · exact ⟨by omega, h2⟩
          · exact ⟨by omega, by simpa using hn⟩
      rw [hset]
      refine layer_step n hn _ _ (∏ q ∈ Nat.primesBelow n, q) 1
        (Finset.prod_pos fun q hq => (Nat.prime_of_mem_primesBelow hq).pos) one_pos
        (fun b hb => Finset.dvd_prod_of_mem _ hb) ?_ (fun d _ => by simp_all)
        (by simp; exact_mod_cast hn.one_lt) ih
        (by
          intro S hS T hT hST
          simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset,
            Finset.subset_singleton_iff] at hS hT
          rcases hS with rfl | rfl <;> rcases hT with rfl | rfl <;> simp_all)
      intro h
      obtain ⟨q, hq, hdq⟩ := (Prime.dvd_finsetProd_iff hn.prime _).1 h
      have hqp := Nat.prime_of_mem_primesBelow hq
      have := (Nat.prime_dvd_prime_iff_eq hn hqp).1 hdq
      have := Nat.lt_of_mem_primesBelow hq
      omega
    · have : Nat.primesBelow (n + 1) = Nat.primesBelow n := by
        ext m
        simp only [Nat.primesBelow, mem_filter, mem_range]
        constructor
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | rfl
          · exact ⟨h, h2⟩
          · exact absurd h2 hn
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      rw [this]; exact ih

lemma primeCounting_le_R (N : ℕ) : (Nat.primeCounting N : ℝ) ≤ Erdos321.R N := by
  have hsub : Nat.primesBelow (N + 1) ⊆ Finset.Icc 1 N := by
    intro m hm
    have h1 := (Nat.prime_of_mem_primesBelow hm).one_lt
    have h2 := Nat.lt_of_mem_primesBelow hm
    simp only [mem_Icc]
    omega
  have h := card_le_R hsub (primes_inj (N + 1))
  rw [Nat.primesBelow_card_eq_primeCounting'] at h
  exact_mod_cast h

theorem main : H1 → H2 → type_of% @Erdos321.erdos_321.variants.lower := by
  intro h1 h2
  have honest : ∀ N k : ℕ, 4 ≤ k → (k : ℝ) ≤ Real.log^[k] (N : ℝ) →
      (∀ i ≤ k, 1 ≤ Real.log^[i] (N : ℝ)) →
      (N : ℝ) / Real.log N * ∏ i ∈ Finset.Icc 3 k, Real.log^[i] (N : ℝ) ≤ Erdos321.R N := by
    intro N k hk hkN hall
    obtain ⟨A, hA, hinj, hcard⟩ := h1 N k hk hkN hall
      (fun A => Set.InjOn (fun S : Finset ℕ => ∑ n ∈ S, (1 : ℚ) / n) A.powerset)
      (by simp [Set.InjOn])
      (fun p M K B D hp hM hK hBM hpM hDK hD hKD hB => layer_step p hp B D M K hM hK hBM hpM hDK hKD hB hD)
    exact hcard.trans (by exact_mod_cast card_le_R hA hinj)
  intro N k hk hkN
  by_cases hall : ∀ i ≤ k, 1 ≤ Real.log^[i] (N : ℝ)
  · exact honest N k hk hkN hall
  · push Not at hall
    rcases h2 N k hk hkN hall with h | ⟨j, hj, hjN, hjall, hle⟩
    · exact h.trans (primeCounting_le_R N)
    · exact hle.trans (honest N j hj hjN hjall)

end OMA.R_Erdos321_erdos_321_variants_lower_R1
