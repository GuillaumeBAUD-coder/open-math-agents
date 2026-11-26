import FormalConjectures.ErdosProblems.«687»
import Mathlib.NumberTheory.Chebyshev

-- Reduction Erdos687.erdos_687.parts.iii.R1 of Erdős Problem 687 — iii
-- Credit: @santiemanuel
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Buchstab-sieve reduction of Erdős Problem 687 (iii)

For a cutoff `z = ⌊x ^ (1 / s)⌋₊` and interval length `y = ⌈x ^ (1 + ε)⌉₊`, we prove:

1. The exact shifted-sieve **Buchstab identity** (`buchstab_identity`), partitioning the integers
   in `[1, y]` that avoid `a p (mod p)` for all primes `p ≤ z` into the full survivors (`p ≤ x`)
   and the disjoint classes whose least bad prime `q` lies in `(z, x]`.
2. An explicit **Chebyshev-Mertens Euler-product ratio bound** (`chebyshev_eulerProd_ratio`),
   derived from `Chebyshev.theta_le_log4_mul_x` via dyadic summation by parts:
   `∏_{p ≤ z} (1 - 1 / p) ≤ 8 * exp 5 * s ^ 3 * ∏_{p ≤ x} (1 - 1 / p)` for large `x`.

This reduces `Erdos687.erdos_687.parts.iii` to two independent hypotheses:

- `H1`: The **fundamental lemma of the shifted sieve** with super-cubic accuracy `1 - δ / s ^ 3`
  for `y ≥ z ^ s` (a classical, unconditionally provable theorem of combinatorial sieve theory).
- `H2`: The **quantitative Buchstab large-prime tail bound** on `(z, x]`, asserting that the total
  mass of integers in `[1, ⌈x ^ (1 + ε)⌉₊]` whose least bad prime lies in `(z, x]` stays below
  `y * (V(z) - c * V(x))` for some `c > 0` and all sufficiently large `s`.
-/

namespace OMA.R_Erdos687_erdos_687_parts_iii_R1

open Filter Finset Real

/-- Fundamental lemma of the shifted sieve with super-cubic relative accuracy:
for every `δ > 0` and `s₀ : ℕ`, there is an integer sifting parameter `s ≥ max s₀ 2` such that
for all sufficiently large `z`, every `y ≥ z ^ s`, and every residue assignment `a : ℕ → ℕ`,
at least `(1 - δ / s ^ 3) * y * ∏_{p ≤ z} (1 - 1 / p)` integers in `[1, y]` avoid every
congruence `a p (mod p)` for primes `p ≤ z`. -/
def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ s₀ : ℕ, ∃ s : ℕ, s₀ ≤ s ∧ 2 ≤ s ∧
    ∀ᶠ z : ℕ in Filter.atTop, ∀ y : ℕ, z ^ s ≤ y → ∀ a : ℕ → ℕ,
      (1 - δ / (s : ℝ) ^ 3) * (y : ℝ) *
        (∏ p ∈ (Finset.range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) ≤
      (((Finset.Icc 1 y).filter fun m =>
        ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ)

/-- Quantitative Buchstab large-prime tail bound:
there exist `c > 0` and `s₀ ≥ 2` such that for every `s ≥ s₀`, every `ε > 0`, all sufficiently
large `x`, and every residue assignment `a : ℕ → ℕ`, letting `z = ⌊x ^ (1 / s)⌋₊` and
`y = ⌈x ^ (1 + ε)⌉₊`, the number of integers in `[1, y]` whose least bad prime lies in `(z, x]`
is at most `y * (∏_{p ≤ z} (1 - 1 / p) - c * ∏_{p ≤ x} (1 - 1 / p))`. -/
def H2 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ s₀ : ℕ, 2 ≤ s₀ ∧ ∀ s : ℕ, s₀ ≤ s → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ x : ℕ in Filter.atTop, ∀ a : ℕ → ℕ,
      let z := ⌊(x : ℝ) ^ ((1 : ℝ) / (s : ℝ))⌋₊
      let y := ⌈(x : ℝ) ^ (1 + ε)⌉₊
      (∑ q ∈ (Finset.Ioc z x).filter Nat.Prime,
        (((Finset.Icc 1 y).filter fun m =>
          m ≡ a q [MOD q] ∧ ∀ p < q, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ)) ≤
      (y : ℝ) *
        ((∏ p ∈ (Finset.range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) -
          c * (∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)))

/-- Exact shifted-sieve Buchstab identity: partitioning `z`-survivors in `[1, y]` by whether they
survive all primes `≤ x` or according to their least bad prime `q ∈ (z, x]`. -/
lemma buchstab_identity (z x y : ℕ) (hzx : z ≤ x) (a : ℕ → ℕ) :
    ((Icc 1 y).filter fun m => ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])).card =
    ((Icc 1 y).filter fun m => ∀ p ≤ x, p.Prime → ¬ (m ≡ a p [MOD p])).card +
    ∑ q ∈ (Ioc z x).filter Nat.Prime,
      ((Icc 1 y).filter fun m =>
        m ≡ a q [MOD q] ∧ ∀ p < q, p.Prime → ¬ (m ≡ a p [MOD p])).card := by
  let Sz := (Icc 1 y).filter fun m => ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])
  let Sx := (Icc 1 y).filter fun m => ∀ p ≤ x, p.Prime → ¬ (m ≡ a p [MOD p])
  let Q := (Ioc z x).filter Nat.Prime
  let R : ℕ → Finset ℕ := fun q =>
    (Icc 1 y).filter fun m => m ≡ a q [MOD q] ∧ ∀ p < q, p.Prime → ¬ (m ≡ a p [MOD p])
  have hdisj_union : Disjoint Sx (Q.biUnion R) := by
    rw [Finset.disjoint_left]
    intro m hmSx hmU
    rw [mem_biUnion] at hmU
    obtain ⟨q, hqQ, hmRq⟩ := hmU
    have hq_mem := mem_filter.mp hqQ
    have hqx : q ≤ x := (mem_Ioc.mp hq_mem.1).2
    have hqp : q.Prime := hq_mem.2
    have hcong : m ≡ a q [MOD q] := (mem_filter.mp hmRq).2.1
    exact (mem_filter.mp hmSx).2 q hqx hqp hcong
  have hpw : (Q : Set ℕ).PairwiseDisjoint R := by
    intro q₁ hq₁ q₂ hq₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro m hm₁ hm₂
    have h1 := (mem_filter.mp hm₁).2
    have h2 := (mem_filter.mp hm₂).2
    have hp₁ : q₁.Prime := (mem_filter.mp hq₁).2
    have hp₂ : q₂.Prime := (mem_filter.mp hq₂).2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact h2.2 q₁ hlt hp₁ h1.1
    · exact h1.2 q₂ hgt hp₂ h2.1
  have heq : Sz = Sx ∪ Q.biUnion R := by
    ext m
    simp only [mem_union, mem_biUnion]
    constructor
    · intro hmSz
      by_cases hmSx : m ∈ Sx
      · exact Or.inl hmSx
      · right
        have hmIcc : m ∈ Icc 1 y := (mem_filter.mp hmSz).1
        have hmAvoidZ : ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p]) := (mem_filter.mp hmSz).2
        have hex : ∃ q : ℕ, q ≤ x ∧ q.Prime ∧ m ≡ a q [MOD q] := by
          by_contra hnone
          push Not at hnone
          exact hmSx (mem_filter.mpr ⟨hmIcc, hnone⟩)
        let q := Nat.find hex
        obtain ⟨hqx, hqp, hqcong⟩ := Nat.find_spec hex
        have hqgt : z < q := by
          by_contra hle
          push Not at hle
          exact hmAvoidZ q hle hqp hqcong
        have hmin : ∀ p < q, p.Prime → ¬ (m ≡ a p [MOD p]) := by
          intro p hpq hpp hpc
          exact Nat.find_min hex hpq ⟨hpq.le.trans hqx, hpp, hpc⟩
        exact ⟨q, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hqgt, hqx⟩, hqp⟩,
          mem_filter.mpr ⟨hmIcc, hqcong, hmin⟩⟩
    · rintro (hmSx | ⟨q, hqQ, hmRq⟩)
      · have h := mem_filter.mp hmSx
        exact mem_filter.mpr ⟨h.1, fun p hpz => h.2 p (hpz.trans hzx)⟩
      · have hq_mem := mem_filter.mp hqQ
        have hqz : z < q := (mem_Ioc.mp hq_mem.1).1
        have h := mem_filter.mp hmRq
        exact mem_filter.mpr ⟨h.1, fun p hpz => h.2.2 p (lt_of_le_of_lt hpz hqz)⟩
  change Sz.card = Sx.card + ∑ q ∈ Q, (R q).card
  rw [heq, card_union_of_disjoint hdisj_union, card_biUnion hpw]

private lemma eulerProd_pos (u : ℕ) :
    0 < ∏ p ∈ (range (u + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) := by
  apply Finset.prod_pos
  intro p hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2.two_le
  have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
  linarith

private lemma eulerProd_split {z x : ℕ} (hzx : z ≤ x) :
    (∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) =
    (∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) *
    (∏ q ∈ (Ioc z x).filter Nat.Prime, (1 - (q : ℝ)⁻¹)) := by
  have hdisj : Disjoint ((range (z + 1)).filter Nat.Prime) ((Ioc z x).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    have h1 : p < z + 1 := mem_range.mp (mem_filter.mp hp₁).1
    have h2 : z < p := (mem_Ioc.mp (mem_filter.mp hp₂).1).1
    omega
  have hunion : (range (x + 1)).filter Nat.Prime =
      (range (z + 1)).filter Nat.Prime ∪ (Ioc z x).filter Nat.Prime := by
    ext p
    simp only [mem_union, mem_filter, mem_range, mem_Ioc]
    constructor
    · rintro ⟨hpx, hpp⟩
      by_cases hpz : p ≤ z
      · exact Or.inl ⟨by omega, hpp⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hpp⟩
    · rintro (⟨hpz, hpp⟩ | ⟨⟨_, hpx⟩, hpp⟩)
      · exact ⟨by omega, hpp⟩
      · exact ⟨by omega, hpp⟩
  rw [hunion, Finset.prod_union hdisj]

private lemma one_sub_inv_inv_le_exp {q : ℕ} (hq : 11 ≤ q) :
    (1 - (q : ℝ)⁻¹)⁻¹ ≤ Real.exp ((11 / 10 : ℝ) * (q : ℝ)⁻¹) := by
  set u : ℝ := (q : ℝ)⁻¹
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hu_pos : 0 < u := inv_pos.mpr hq_pos
  have hu_le : u ≤ 1 / 11 := by
    have hq11 : (11 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    simpa [u, one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 11) hq11
  have h1u_pos : 0 < 1 - u := by linarith
  have hquad : 1 ≤ (1 - u) * (1 + (11 / 10 : ℝ) * u) := by
    nlinarith
  have hexp : 1 + (11 / 10 : ℝ) * u ≤ Real.exp ((11 / 10 : ℝ) * u) := by
    linarith [Real.add_one_le_exp ((11 / 10 : ℝ) * u)]
  have hmul : 1 ≤ (1 - u) * Real.exp ((11 / 10 : ℝ) * u) :=
    hquad.trans (mul_le_mul_of_nonneg_left hexp h1u_pos.le)
  rw [inv_eq_one_div, div_le_iff₀ h1u_pos]
  linarith

private lemma sum_by_parts_Icc (f a : ℕ → ℝ) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    ∑ k ∈ Icc k₁ k₂, (f (k + 1) - f k) * a k =
      f (k₂ + 1) * a k₂ - f k₁ * a k₁ +
        ∑ k ∈ Icc (k₁ + 1) k₂, f k * (a (k - 1) - a k) := by
  induction k₂, hk using Nat.le_induction with
  | base =>
    rw [Icc_self, Finset.sum_singleton, Finset.Icc_eq_empty_of_lt (Nat.lt_succ_self k₁),
      Finset.sum_empty]
    ring
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hm), ih,
      Finset.sum_Icc_succ_top (Nat.succ_le_succ hm)]
    simp only [Nat.add_sub_cancel]
    ring

private lemma inv_le_log_sub_log {k : ℕ} (hk : 2 ≤ k) :
    (k : ℝ)⁻¹ ≤ Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hk1_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hratio : ((k - 1 : ℕ) : ℝ) / (k : ℝ) = 1 - (k : ℝ)⁻¹ := by
    rw [hcast, sub_div, div_self hk_pos.ne', one_div]
  have hexp : ((k - 1 : ℕ) : ℝ) / (k : ℝ) ≤ Real.exp (-(k : ℝ)⁻¹) := by
    rw [hratio]
    linarith [Real.add_one_le_exp (-(k : ℝ)⁻¹)]
  have hlog := Real.log_le_log (div_pos hk1_pos hk_pos) hexp
  rw [Real.log_div hk1_pos.ne' hk_pos.ne', Real.log_exp] at hlog
  linarith

private lemma sum_telescoping_Icc (g : ℕ → ℝ) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    ∑ k ∈ Icc (k₁ + 1) k₂, (g k - g (k - 1)) = g k₂ - g k₁ := by
  induction k₂, hk using Nat.le_induction with
  | base =>
    rw [Finset.Icc_eq_empty_of_lt (Nat.lt_succ_self k₁), Finset.sum_empty, sub_self]
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ hm), ih]
    simp only [Nat.add_sub_cancel]
    ring

private lemma theta_sub_theta_eq (a b : ℕ) (hab : a ≤ b) :
    Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ) =
      ∑ q ∈ (Ioc a b).filter Nat.Prime, Real.log (q : ℝ) := by
  have hθ (n : ℕ) : Chebyshev.theta (n : ℝ) =
      ∑ p ∈ (Ioc 0 n).filter Nat.Prime, Real.log (p : ℝ) := by
    simp [Chebyshev.theta]
  rw [hθ b, hθ a]
  have hdisj : Disjoint ((Ioc 0 a).filter Nat.Prime) ((Ioc a b).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    have h1 := (mem_Ioc.mp (mem_filter.mp hp₁).1).2
    have h2 := (mem_Ioc.mp (mem_filter.mp hp₂).1).1
    omega
  have hunion : (Ioc 0 b).filter Nat.Prime =
      (Ioc 0 a).filter Nat.Prime ∪ (Ioc a b).filter Nat.Prime := by
    ext p
    simp only [mem_union, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨hp0, hpb⟩, hpp⟩
      by_cases hpa : p ≤ a
      · exact Or.inl ⟨⟨hp0, hpa⟩, hpp⟩
      · exact Or.inr ⟨⟨by omega, hpb⟩, hpp⟩
    · rintro (⟨⟨hp0, hpa⟩, hpp⟩ | ⟨⟨hpa, hpb⟩, hpp⟩)
      · exact ⟨⟨hp0, hpa.trans hab⟩, hpp⟩
      · exact ⟨⟨by omega, hpb⟩, hpp⟩
  rw [hunion, Finset.sum_union hdisj, add_sub_cancel_left]

/-- Elementary dyadic Chebyshev bound on the reciprocal prime sum over `(z, x]`. -/
lemma sum_prime_inv_Ioc_le {z x : ℕ} (hz : 10 ≤ z) (hzx : z ≤ x) :
    ∑ q ∈ (Ioc z x).filter Nat.Prime, (q : ℝ)⁻¹ ≤
      4 + 2 * Real.log ((Nat.log 2 x : ℝ) / (Nat.log 2 z : ℝ)) := by
  let k₁ := Nat.log 2 z
  let k₂ := Nat.log 2 x
  have hk₁3 : 3 ≤ k₁ := by
    dsimp [k₁]
    exact Nat.le_log_of_pow_le (by norm_num) (by omega : 2 ^ 3 ≤ z)
  have hk₁₂ : k₁ ≤ k₂ := Nat.log_mono_right hzx
  have hz_ge : 2 ^ k₁ ≤ z := Nat.pow_log_le_self 2 (by omega)
  have hx_lt : x < 2 ^ (k₂ + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  -- Cover `(Ioc z x).filter Nat.Prime` by dyadic blocks `(2^k, 2^(k+1)]`.
  let B : ℕ → Finset ℕ := fun k => (Ioc (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime
  have hsub : (Ioc z x).filter Nat.Prime ⊆ (Icc k₁ k₂).biUnion B := by
    intro q hq
    rw [mem_filter, mem_Ioc] at hq
    have hq_lo : 2 ^ k₁ < q := lt_of_le_of_lt hz_ge hq.1.1
    have hq_hi : q ≤ 2 ^ (k₂ + 1) := le_of_lt (lt_of_le_of_lt hq.1.2 hx_lt)
    set k := Nat.log 2 (q - 1)
    have hq1_pos : q - 1 ≠ 0 := by
      have := hq.2.two_le
      omega
    have hk_lo : 2 ^ k < q := by
      have h : 2 ^ k ≤ q - 1 := Nat.pow_log_le_self 2 hq1_pos
      omega
    have hk_hi : q ≤ 2 ^ (k + 1) := by
      have h : q - 1 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (q - 1)
      omega
    have hk_ge : k₁ ≤ k := by
      exact Nat.le_log_of_pow_le (by norm_num) (by omega)
    have hk_le : k ≤ k₂ := by
      by_contra hgt
      push Not at hgt
      have hpow : 2 ^ (k₂ + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hgt
      omega
    exact mem_biUnion.mpr ⟨k, mem_Icc.mpr ⟨hk_ge, hk_le⟩,
      mem_filter.mpr ⟨mem_Ioc.mpr ⟨hk_lo, hk_hi⟩, hq.2⟩⟩
  have hpw_B : (Icc k₁ k₂ : Set ℕ).PairwiseDisjoint B := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro q hqi hqj
    have hi := mem_Ioc.mp (mem_filter.mp hqi).1
    have hj := mem_Ioc.mp (mem_filter.mp hqj).1
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hlt
      omega
    · have : 2 ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hgt
      omega
  have hstep1 : ∑ q ∈ (Ioc z x).filter Nat.Prime, (q : ℝ)⁻¹ ≤
      ∑ k ∈ Icc k₁ k₂, ∑ q ∈ B k, (q : ℝ)⁻¹ := by
    calc
      ∑ q ∈ (Ioc z x).filter Nat.Prime, (q : ℝ)⁻¹
          ≤ ∑ q ∈ (Icc k₁ k₂).biUnion B, (q : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = ∑ k ∈ Icc k₁ k₂, ∑ q ∈ B k, (q : ℝ)⁻¹ :=
        Finset.sum_biUnion hpw_B
  let f : ℕ → ℝ := fun k => Chebyshev.theta ((2 ^ k : ℕ) : ℝ)
  let a : ℕ → ℝ := fun k => ((2 ^ k : ℝ) * (k : ℝ) * Real.log 2)⁻¹
  have hblock (k : ℕ) (hk : k ∈ Icc k₁ k₂) :
      ∑ q ∈ B k, (q : ℝ)⁻¹ ≤ (f (k + 1) - f k) * a k := by
    have hk_ge3 : 3 ≤ k := le_trans hk₁3 (mem_Icc.mp hk).1
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hden_pos : 0 < (2 ^ k : ℝ) * (k : ℝ) * Real.log 2 := by positivity
    have hterm : ∀ q ∈ B k, (q : ℝ)⁻¹ ≤ Real.log (q : ℝ) * a k := by
      intro q hq
      have hq_lo : 2 ^ k < q := (mem_Ioc.mp (mem_filter.mp hq).1).1
      have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (mem_filter.mp hq).2.pos
      have h2k_le : (2 ^ k : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_lo.le
      have hlog_le : (k : ℝ) * Real.log 2 ≤ Real.log (q : ℝ) := by
        have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 ^ k : ℝ)) h2k_le
        rwa [Real.log_pow] at h
      have hmul : (2 ^ k : ℝ) * (k : ℝ) * Real.log 2 ≤ (q : ℝ) * Real.log (q : ℝ) := by
        calc
          (2 ^ k : ℝ) * (k : ℝ) * Real.log 2 = (2 ^ k : ℝ) * ((k : ℝ) * Real.log 2) := by ring
          _ ≤ (q : ℝ) * Real.log (q : ℝ) :=
            mul_le_mul h2k_le hlog_le (by positivity) hq_pos.le
      dsimp [a]
      rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hq_pos hden_pos]
      linarith
    calc
      ∑ q ∈ B k, (q : ℝ)⁻¹ ≤ ∑ q ∈ B k, Real.log (q : ℝ) * a k := Finset.sum_le_sum hterm
      _ = (∑ q ∈ B k, Real.log (q : ℝ)) * a k := (Finset.sum_mul _ _ _).symm
      _ = (f (k + 1) - f k) * a k := by
        congr 1
        exact (theta_sub_theta_eq (2 ^ k) (2 ^ (k + 1))
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))).symm
  have hstep2 : ∑ k ∈ Icc k₁ k₂, ∑ q ∈ B k, (q : ℝ)⁻¹ ≤
      f (k₂ + 1) * a k₂ - f k₁ * a k₁ +
        ∑ k ∈ Icc (k₁ + 1) k₂, f k * (a (k - 1) - a k) := by
    rw [← sum_by_parts_Icc f a hk₁₂]
    exact Finset.sum_le_sum hblock
  -- Bound the boundary terms.
  have hfk1_nn : 0 ≤ f k₁ * a k₁ :=
    mul_nonneg (Chebyshev.theta_nonneg _) (by dsimp [a]; positivity)
  have htop : f (k₂ + 1) * a k₂ ≤ 2 := by
    have hk2_ge3 : (3 : ℝ) ≤ (k₂ : ℝ) := by exact_mod_cast (le_trans hk₁3 hk₁₂)
    have hθ := Chebyshev.theta_le_log4_mul_x (x := ((2 ^ (k₂ + 1) : ℕ) : ℝ)) (by positivity)
    have ha_nn : 0 ≤ a k₂ := by dsimp [a]; positivity
    have h1 : f (k₂ + 1) * a k₂ ≤ Real.log 4 * ((2 ^ (k₂ + 1) : ℕ) : ℝ) * a k₂ :=
      mul_le_mul_of_nonneg_right hθ ha_nn
    have hsimp : Real.log 4 * ((2 ^ (k₂ + 1) : ℕ) : ℝ) * a k₂ = 4 / (k₂ : ℝ) := by
      dsimp [a]
      rw [hlog4, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
      have h2k_ne : (2 : ℝ) ^ k₂ ≠ 0 := by positivity
      have hk2_ne : (k₂ : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    rw [hsimp] at h1
    have h43 : 4 / (k₂ : ℝ) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    exact h1.trans h43
  -- Bound the interior sum term-by-term.
  have hinterior : ∑ k ∈ Icc (k₁ + 1) k₂, f k * (a (k - 1) - a k) ≤
      2 + 2 * Real.log ((k₂ : ℝ) / (k₁ : ℝ)) := by
    have hterm (k : ℕ) (hk : k ∈ Icc (k₁ + 1) k₂) :
        f k * (a (k - 1) - a k) ≤
          2 * (Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ)) +
            4 * (((k - 1 : ℕ) : ℝ)⁻¹ - (k : ℝ)⁻¹) := by
      have hk4 : 4 ≤ k := by
        have := (mem_Icc.mp hk).1
        omega
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
      have hk1_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < k - 1 by omega)
      have hcast1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      have hpow1 : (2 : ℝ) ^ (k - 1) * 2 = (2 : ℝ) ^ k := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      have hadiff : a (k - 1) - a k =
          ((2 ^ k : ℝ) * Real.log 2)⁻¹ * (((k : ℝ) + 1) / ((k : ℝ) * ((k - 1 : ℕ) : ℝ))) := by
        dsimp [a]
        have h2k1_ne : (2 : ℝ) ^ (k - 1) ≠ 0 := by positivity
        have h2k_ne : (2 : ℝ) ^ k ≠ 0 := by positivity
        have hlog2_ne : Real.log 2 ≠ 0 := hlog2_pos.ne'
        rw [← hpow1]
        field_simp
        rw [hcast1]
        ring
      have hadiff_nn : 0 ≤ a (k - 1) - a k := by
        rw [hadiff]
        positivity
      have hθ := Chebyshev.theta_le_log4_mul_x (x := ((2 ^ k : ℕ) : ℝ)) (by positivity)
      have hmul := mul_le_mul_of_nonneg_right hθ hadiff_nn
      have hsimp : Real.log 4 * ((2 ^ k : ℕ) : ℝ) * (a (k - 1) - a k) =
          2 * (k : ℝ)⁻¹ + 4 * (((k - 1 : ℕ) : ℝ)⁻¹ - (k : ℝ)⁻¹) := by
        rw [hadiff, hlog4, Nat.cast_pow, Nat.cast_ofNat]
        have h2k_ne : (2 : ℝ) ^ k ≠ 0 := by positivity
        have hlog2_ne : Real.log 2 ≠ 0 := hlog2_pos.ne'
        field_simp
        rw [hcast1]
        ring
      have hfk : f k * (a (k - 1) - a k) ≤
          2 * (k : ℝ)⁻¹ + 4 * (((k - 1 : ℕ) : ℝ)⁻¹ - (k : ℝ)⁻¹) := by
        dsimp [f]
        exact hmul.trans_eq hsimp
      have hlog := inv_le_log_sub_log (by omega : 2 ≤ k)
      linarith
    calc
      ∑ k ∈ Icc (k₁ + 1) k₂, f k * (a (k - 1) - a k)
          ≤ ∑ k ∈ Icc (k₁ + 1) k₂,
              (2 * (Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ)) +
                4 * (((k - 1 : ℕ) : ℝ)⁻¹ - (k : ℝ)⁻¹)) := Finset.sum_le_sum hterm
      _ = 2 * ∑ k ∈ Icc (k₁ + 1) k₂, (Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ)) -
            4 * ∑ k ∈ Icc (k₁ + 1) k₂, ((k : ℝ)⁻¹ - ((k - 1 : ℕ) : ℝ)⁻¹) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        have hneg : ∑ k ∈ Icc (k₁ + 1) k₂, (((k - 1 : ℕ) : ℝ)⁻¹ - (k : ℝ)⁻¹) =
            -(∑ k ∈ Icc (k₁ + 1) k₂, ((k : ℝ)⁻¹ - ((k - 1 : ℕ) : ℝ)⁻¹)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun k _ => by ring
        rw [hneg]
        ring
      _ = 2 * (Real.log (k₂ : ℝ) - Real.log (k₁ : ℝ)) + 4 * ((k₁ : ℝ)⁻¹ - (k₂ : ℝ)⁻¹) := by
        rw [sum_telescoping_Icc (fun n => Real.log (n : ℝ)) hk₁₂,
          sum_telescoping_Icc (fun n => (n : ℝ)⁻¹) hk₁₂]
        ring
      _ ≤ 2 + 2 * Real.log ((k₂ : ℝ) / (k₁ : ℝ)) := by
        have hk1_pos : (0 : ℝ) < (k₁ : ℝ) := by exact_mod_cast (show 0 < k₁ by omega)
        have hk2_pos : (0 : ℝ) < (k₂ : ℝ) := by exact_mod_cast (show 0 < k₂ by omega)
        have hk1_3 : (3 : ℝ) ≤ (k₁ : ℝ) := by exact_mod_cast hk₁3
        have hinv1 : (k₁ : ℝ)⁻¹ ≤ (3 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hk1_3
        have hinv2 : 0 ≤ (k₂ : ℝ)⁻¹ := by positivity
        rw [Real.log_div hk2_pos.ne' hk1_pos.ne']
        linarith
  linarith

/-- Chebyshev-Mertens Euler-product ratio bound: for every integer `s ≥ 2`, eventually
`V(⌊x ^ (1 / s)⌋₊) ≤ 8 * exp 5 * s ^ 3 * V(x)`. -/
lemma chebyshev_eulerProd_ratio (s : ℕ) (hs : 2 ≤ s) :
    ∀ᶠ x : ℕ in atTop,
      let z := ⌊(x : ℝ) ^ ((1 : ℝ) / (s : ℝ))⌋₊
      (∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) ≤
      (8 * Real.exp 5) * (s : ℝ) ^ 3 *
        (∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) := by
  filter_upwards [eventually_ge_atTop (10 ^ s)] with x hx
  dsimp only
  set z := ⌊(x : ℝ) ^ ((1 : ℝ) / (s : ℝ))⌋₊
  have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hx10s : ((10 ^ s : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hx_pos : (0 : ℝ) < (x : ℝ) := by
    have : 1 ≤ 10 ^ s := Nat.one_le_pow s 10 (by norm_num)
    exact_mod_cast (show 0 < x by omega)
  have hx_ge1 : (1 : ℝ) ≤ (x : ℝ) := by
    have : 1 ≤ 10 ^ s := Nat.one_le_pow s 10 (by norm_num)
    exact_mod_cast (show 1 ≤ x by omega)
  have h10_le_rpow : (10 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / (s : ℝ)) := by
    calc
      (10 : ℝ) = ((10 : ℝ) ^ (s : ℝ)) ^ ((1 : ℝ) / (s : ℝ)) := by
        rw [← Real.rpow_mul (by norm_num), mul_one_div_cancel hs_pos.ne', Real.rpow_one]
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / (s : ℝ)) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        simpa [Real.rpow_natCast] using hx10s
  have hz10 : 10 ≤ z := Nat.le_floor h10_le_rpow
  have hzx : z ≤ x := by
    have hrpow_le : (x : ℝ) ^ ((1 : ℝ) / (s : ℝ)) ≤ (x : ℝ) := by
      calc
        (x : ℝ) ^ ((1 : ℝ) / (s : ℝ)) ≤ (x : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx_ge1
            ((div_le_one hs_pos).mpr (by exact_mod_cast (show 1 ≤ s by omega)))
        _ = (x : ℝ) := Real.rpow_one _
    exact_mod_cast (Nat.floor_le (by positivity)).trans hrpow_le
  -- Bound `Nat.log 2 x / Nat.log 2 z ≤ 2 * s`.
  let k₁ := Nat.log 2 z
  let k₂ := Nat.log 2 x
  have hk₁3 : 3 ≤ k₁ := Nat.le_log_of_pow_le (by norm_num) (by omega : 2 ^ 3 ≤ z)
  have hk₂_lt : k₂ < s * (k₁ + 1) := by
    have hz_lt : z < 2 ^ (k₁ + 1) := Nat.lt_pow_succ_log_self (by norm_num) z
    have h1 : (x : ℝ) ^ ((1 : ℝ) / (s : ℝ)) < ((2 ^ (k₁ + 1) : ℕ) : ℝ) := by
      calc
        (x : ℝ) ^ ((1 : ℝ) / (s : ℝ)) < (z : ℝ) + 1 := Nat.lt_floor_add_one _
        _ ≤ ((2 ^ (k₁ + 1) : ℕ) : ℝ) := by exact_mod_cast (show z + 1 ≤ 2 ^ (k₁ + 1) by omega)
    have h2 : (x : ℝ) < (((2 ^ (k₁ + 1) : ℕ) : ℝ)) ^ s := by
      have hpow := pow_lt_pow_left₀ h1 (by positivity) (show s ≠ 0 by omega)
      have hleft : ((x : ℝ) ^ ((1 : ℝ) / (s : ℝ))) ^ s = (x : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le, one_div_mul_cancel hs_pos.ne',
          Real.rpow_one]
      rwa [hleft] at hpow
    have hx_lt_pow : x < 2 ^ (s * (k₁ + 1)) := by
      have h2' : (x : ℝ) < ((2 ^ (s * (k₁ + 1)) : ℕ) : ℝ) := by
        simpa [Nat.cast_pow, ← pow_mul, mul_comm] using h2
      exact_mod_cast h2'
    have h2k2_le : 2 ^ k₂ ≤ x := Nat.pow_log_le_self 2 (by omega)
    have hpow_lt : 2 ^ k₂ < 2 ^ (s * (k₁ + 1)) := lt_of_le_of_lt h2k2_le hx_lt_pow
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow_lt
  have hratio_le : (k₂ : ℝ) / (k₁ : ℝ) ≤ 2 * (s : ℝ) := by
    have hk₁_pos : (0 : ℝ) < (k₁ : ℝ) := by exact_mod_cast (show 0 < k₁ by omega)
    rw [div_le_iff₀ hk₁_pos]
    have hnat : k₂ ≤ 2 * s * k₁ := by
      have : s * (k₁ + 1) ≤ 2 * s * k₁ := by nlinarith
      omega
    exact_mod_cast hnat
  have hsum_le : ∑ q ∈ (Ioc z x).filter Nat.Prime, (q : ℝ)⁻¹ ≤
      4 + 2 * Real.log (2 * (s : ℝ)) := by
    have hbase := sum_prime_inv_Ioc_le hz10 hzx
    have hk1_pos : (0 : ℝ) < (k₁ : ℝ) := by exact_mod_cast (show 0 < k₁ by omega)
    have hk2_pos : (0 : ℝ) < (k₂ : ℝ) := by
      have : k₁ ≤ k₂ := Nat.log_mono_right hzx
      exact_mod_cast (show 0 < k₂ by omega)
    have hlog_mono : Real.log ((k₂ : ℝ) / (k₁ : ℝ)) ≤ Real.log (2 * (s : ℝ)) :=
      Real.log_le_log (div_pos hk2_pos hk1_pos) hratio_le
    linarith
  -- Convert the prime reciprocal sum bound to the Euler-product ratio bound.
  have hprod_inv : (∏ q ∈ (Ioc z x).filter Nat.Prime, (1 - (q : ℝ)⁻¹))⁻¹ ≤
      (8 * Real.exp 5) * (s : ℝ) ^ 3 := by
    rw [← Finset.prod_inv_distrib]
    have h1 : ∏ q ∈ (Ioc z x).filter Nat.Prime, (1 - (q : ℝ)⁻¹)⁻¹ ≤
        ∏ q ∈ (Ioc z x).filter Nat.Prime, Real.exp ((11 / 10 : ℝ) * (q : ℝ)⁻¹) := by
      apply Finset.prod_le_prod
      · intro q hq
        have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (mem_filter.mp hq).2.two_le
        have hinv : (q : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hq2
        exact inv_nonneg.mpr (by linarith)
      · intro q hq
        have hqz : z < q := (mem_Ioc.mp (mem_filter.mp hq).1).1
        exact one_sub_inv_inv_le_exp (by omega)
    rw [← Real.exp_sum, ← Finset.mul_sum] at h1
    have hlog2s_nn : 0 ≤ Real.log (2 * (s : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * s by omega))
    have hexp_arg : (11 / 10 : ℝ) * (∑ q ∈ (Ioc z x).filter Nat.Prime, (q : ℝ)⁻¹) ≤
        5 + Real.log ((2 * (s : ℝ)) ^ (3 : ℕ)) := by
      rw [Real.log_pow]
      norm_num
      linarith
    have h2 : Real.exp ((11 / 10 : ℝ) * ∑ q ∈ (Ioc z x).filter Nat.Prime, (q : ℝ)⁻¹) ≤
        Real.exp (5 + Real.log ((2 * (s : ℝ)) ^ (3 : ℕ))) := Real.exp_le_exp.mpr hexp_arg
    have h3 : Real.exp (5 + Real.log ((2 * (s : ℝ)) ^ (3 : ℕ))) =
        (8 * Real.exp 5) * (s : ℝ) ^ 3 := by
      rw [Real.exp_add, Real.exp_log (by positivity)]
      ring
    exact h1.trans (h2.trans_eq h3)
  have hVx_pos : 0 < ∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) := eulerProd_pos x
  have hVz_pos : 0 < ∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) := eulerProd_pos z
  have hQ_pos : 0 < ∏ q ∈ (Ioc z x).filter Nat.Prime, (1 - (q : ℝ)⁻¹) := by
    apply Finset.prod_pos
    intro q hq
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (mem_filter.mp hq).2.two_le
    have hinv : (q : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hq2
    linarith
  rw [eulerProd_split hzx]
  calc
    (∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹))
        = (∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) *
            ((∏ q ∈ (Ioc z x).filter Nat.Prime, (1 - (q : ℝ)⁻¹))⁻¹ *
              (∏ q ∈ (Ioc z x).filter Nat.Prime, (1 - (q : ℝ)⁻¹))) := by
      rw [inv_mul_cancel₀ hQ_pos.ne', mul_one]
    _ ≤ (∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) *
          (((8 * Real.exp 5) * (s : ℝ) ^ 3) *
            (∏ q ∈ (Ioc z x).filter Nat.Prime, (1 - (q : ℝ)⁻¹))) := by
      gcongr
    _ = (8 * Real.exp 5) * (s : ℝ) ^ 3 *
          ((∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) *
            (∏ q ∈ (Ioc z x).filter Nat.Prime, (1 - (q : ℝ)⁻¹))) := by ring

private lemma Y_le_of_not_covered {x y : ℕ}
    (h : ∀ a : ℕ → ℕ, ∃ m ∈ Icc 1 y, ∀ p ≤ x, p.Prime → ¬ (m ≡ a p [MOD p])) :
    Erdos687.Y x ≤ y := by
  rw [Erdos687.Y]
  refine csSup_le ⟨0, ⟨fun _ => 0, by simp⟩⟩ ?_
  rintro k ⟨a, ha⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨m, hmIcc, hmAvoid⟩ := h a
  have hmIcc' : m ∈ Icc 1 k := mem_Icc.mpr ⟨(mem_Icc.mp hmIcc).1, (mem_Icc.mp hmIcc).2.trans hlt.le⟩
  obtain ⟨p, hpx, hpp, hpm⟩ := ha m hmIcc'
  exact hmAvoid p hpx hpp hpm

theorem main : H1 → H2 → type_of% @Erdos687.erdos_687.parts.iii := by
  intro hH1 hH2 ε hε
  obtain ⟨c, hc_pos, s₀, hs₀2, hTail⟩ := hH2
  let C₀ : ℝ := 8 * Real.exp 5
  have hC₀_pos : 0 < C₀ := by positivity
  obtain ⟨s, hs_ge_s₀, hs2, hFund⟩ := hH1 (c / (2 * C₀)) (by positivity) s₀
  obtain ⟨Z₀, hZ₀⟩ := eventually_atTop.mp hFund
  rw [Asymptotics.isBigO_iff]
  refine ⟨2, ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (max (10 ^ s) (Z₀ ^ s))),
    chebyshev_eulerProd_ratio s hs2, hTail s hs_ge_s₀ ε hε] with x hx hRatio hTailx
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxZ : Z₀ ^ s ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)
  have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hx_ge1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  let z := ⌊(x : ℝ) ^ ((1 : ℝ) / (s : ℝ))⌋₊
  let y := ⌈(x : ℝ) ^ (1 + ε)⌉₊
  have hz_ge_Z₀ : Z₀ ≤ z := by
    apply Nat.le_floor
    calc
      (Z₀ : ℝ) = ((Z₀ : ℝ) ^ (s : ℝ)) ^ ((1 : ℝ) / (s : ℝ)) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg Z₀), mul_one_div_cancel hs_pos.ne', Real.rpow_one]
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / (s : ℝ)) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        simpa [Real.rpow_natCast] using (show ((Z₀ ^ s : ℕ) : ℝ) ≤ (x : ℝ) by exact_mod_cast hxZ)
  have hzx : z ≤ x := by
    have hrpow_le : (x : ℝ) ^ ((1 : ℝ) / (s : ℝ)) ≤ (x : ℝ) := by
      calc
        (x : ℝ) ^ ((1 : ℝ) / (s : ℝ)) ≤ (x : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx_ge1
            ((div_le_one hs_pos).mpr (by exact_mod_cast (show 1 ≤ s by omega)))
        _ = (x : ℝ) := Real.rpow_one _
    exact_mod_cast (Nat.floor_le (by positivity)).trans hrpow_le
  have hx_rpow_ge : (x : ℝ) ≤ (x : ℝ) ^ (1 + ε) := by
    calc
      (x : ℝ) = (x : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (x : ℝ) ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hx_ge1 (by linarith)
  have hzs_le_y : z ^ s ≤ y := by
    have h1 : ((z ^ s : ℕ) : ℝ) ≤ (x : ℝ) := by
      calc
        ((z ^ s : ℕ) : ℝ) = (z : ℝ) ^ s := by push_cast; rfl
        _ ≤ ((x : ℝ) ^ ((1 : ℝ) / (s : ℝ))) ^ s :=
          pow_le_pow_left₀ (Nat.cast_nonneg z) (Nat.floor_le (by positivity)) s
        _ = (x : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith),
            one_div_mul_cancel hs_pos.ne', Real.rpow_one]
    have h2 : (x : ℝ) ≤ (y : ℝ) := hx_rpow_ge.trans (Nat.le_ceil _)
    exact_mod_cast h1.trans h2
  have hy_pos : (0 : ℝ) < (y : ℝ) := by
    have : (1 : ℝ) ≤ (y : ℝ) := hx_ge1.trans (hx_rpow_ge.trans (Nat.le_ceil _))
    linarith
  have hY_le_y : Erdos687.Y x ≤ y := by
    apply Y_le_of_not_covered
    intro a
    let Vz := ∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)
    let Vx := ∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)
    have hVx_pos : 0 < Vx := eulerProd_pos x
    have hRatio' : Vz ≤ C₀ * (s : ℝ) ^ 3 * Vx := hRatio
    have hlow : (1 - (c / (2 * C₀)) / (s : ℝ) ^ 3) * (y : ℝ) * Vz ≤
        (((Icc 1 y).filter fun m =>
          ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) :=
      hZ₀ z hz_ge_Z₀ y hzs_le_y a
    have htail : (∑ q ∈ (Ioc z x).filter Nat.Prime,
        (((Icc 1 y).filter fun m =>
          m ≡ a q [MOD q] ∧ ∀ p < q, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ)) ≤
        (y : ℝ) * (Vz - c * Vx) := hTailx a
    have hbuch : (((Icc 1 y).filter fun m =>
          ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) =
        (((Icc 1 y).filter fun m =>
          ∀ p ≤ x, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) +
        ∑ q ∈ (Ioc z x).filter Nat.Prime,
          (((Icc 1 y).filter fun m =>
            m ≡ a q [MOD q] ∧ ∀ p < q, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) := by
      exact_mod_cast buchstab_identity z x y hzx a
    have herr : ((c / (2 * C₀)) / (s : ℝ) ^ 3) * Vz ≤ (c / 2) * Vx := by
      have hfac_nn : 0 ≤ (c / (2 * C₀)) / (s : ℝ) ^ 3 := by positivity
      calc
        ((c / (2 * C₀)) / (s : ℝ) ^ 3) * Vz
            ≤ ((c / (2 * C₀)) / (s : ℝ) ^ 3) * (C₀ * (s : ℝ) ^ 3 * Vx) :=
          mul_le_mul_of_nonneg_left hRatio' hfac_nn
        _ = (c / 2) * Vx := by
          have hs3_ne : (s : ℝ) ^ 3 ≠ 0 := by positivity
          field_simp
    have hsurv_real : (c / 2) * (y : ℝ) * Vx ≤
        (((Icc 1 y).filter fun m =>
          ∀ p ≤ x, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) := by
      have h1 : (y : ℝ) * Vz - (c / 2) * (y : ℝ) * Vx ≤
          (1 - (c / (2 * C₀)) / (s : ℝ) ^ 3) * (y : ℝ) * Vz := by
        have hmul := mul_le_mul_of_nonneg_left herr hy_pos.le
        linarith
      linarith
    have hsurv_pos : 0 < ((Icc 1 y).filter fun m =>
        ∀ p ≤ x, p.Prime → ¬ (m ≡ a p [MOD p])).card := by
      have hpos_r : (0 : ℝ) < (((Icc 1 y).filter fun m =>
          ∀ p ≤ x, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) :=
        lt_of_lt_of_le (by positivity) hsurv_real
      exact_mod_cast hpos_r
    obtain ⟨m, hm⟩ := Finset.card_pos.mp hsurv_pos
    exact ⟨m, (mem_filter.mp hm).1, (mem_filter.mp hm).2⟩
  have hrpow_ge1 : (1 : ℝ) ≤ (x : ℝ) ^ (1 + ε) := hx_ge1.trans hx_rpow_ge
  have hy_le : (y : ℝ) ≤ 2 * (x : ℝ) ^ (1 + ε) := by
    have hceil : (y : ℝ) < (x : ℝ) ^ (1 + ε) + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (by positivity)]
  exact (show (Erdos687.Y x : ℝ) ≤ (y : ℝ) by exact_mod_cast hY_le_y).trans hy_le

end OMA.R_Erdos687_erdos_687_parts_iii_R1
