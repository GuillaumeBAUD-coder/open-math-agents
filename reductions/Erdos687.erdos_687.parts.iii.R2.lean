import FormalConjectures.ErdosProblems.«687»
import Mathlib.Data.Fintype.EquivFin

/-!
# Erdős 687, part III

The fixed-exponent estimate in `H1` is needed only along an unbounded
sequence of scales. The short-block assertion in `H2` lets us turn one
sufficiently large non-cover at that scale into an entire tail of non-covers.
The proof also gives a finite lower bound on survivor counts at any cutoff.

Credit goes to @NicholasWierenga.
-/

namespace OMA.R_Erdos687_erdos_687_parts_iii_R2

open Filter
open scoped Classical

/-- For arbitrarily large j, at length K = 2^(6j) the primes up to
2 K^(2/3) cannot cover the whole interval. -/
def H1 : Prop :=
  ∀ J : ℕ, ∃ j ≥ J,
    ¬ Green46.IsCoveredByResidues (2 * 2 ^ (4 * j)) (2 ^ (6 * j))

/-- A localization principle at geometric lengths H = 2^(12j). Inside a
long full cover there is a block of length K = 2^(6j) on which the original
classes up to z = 2^(4j) leave at most as many positions as there are
primes in (z,2z]. -/
def H2 : Prop :=
  ∀ ε > (0 : ℝ), ∃ J : ℕ, ∀ j ≥ J, ∀ x : ℕ,
    (x : ℝ) ^ (1 + ε) ≤ (2 : ℝ) ^ (12 * j) → ∀ a : ℕ → ℕ,
    (∀ m ∈ Finset.Icc 1 (2 ^ (12 * j)), ∃ p ≤ x, p.Prime ∧ m ≡ a p [MOD p]) →
    let K : ℕ := 2 ^ (6 * j)
    let z : ℕ := 2 ^ (4 * j)
    ∃ b : ℕ, b + K ≤ 2 ^ (12 * j) ∧
      ((Finset.Icc 1 K).filter fun m ↦
        ¬ ∃ p ≤ z, p.Prime ∧ (b + m) ≡ a p [MOD p]).card ≤
      ((Finset.Ioc z (2 * z)).filter Nat.Prime).card

/-- Retain the low-prime classes on a block and assign each remaining
position to a different prime in the reserve interval. -/
lemma cover_block_with_reserve {K z w b : ℕ} (hzw : z ≤ w) (a : ℕ → ℕ)
    (hcard : ((Finset.Icc 1 K).filter fun m ↦
      ¬ ∃ p ≤ z, p.Prime ∧ (b + m) ≡ a p [MOD p]).card ≤
      ((Finset.Ioc z w).filter Nat.Prime).card) :
    Green46.IsCoveredByResidues w K := by
  classical
  let S := (Finset.Icc 1 K).filter fun m ↦
    ¬ ∃ p ≤ z, p.Prime ∧ (b + m) ≡ a p [MOD p]
  let T := (Finset.Ioc z w).filter Nat.Prime
  have hST : Fintype.card ↥S ≤ T.card := by
    simpa only [Fintype.card_coe] using hcard
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset hST
  let c : ℕ → ℕ := fun p ↦ if p ≤ z then a p + (p - b % p)
    else ((Function.partialInv f p).map Subtype.val).getD 0
  refine ⟨c, ?_⟩
  intro m hm
  by_cases hc : ∃ p ≤ z, p.Prime ∧ (b + m) ≡ a p [MOD p]
  · obtain ⟨p, hpz, hp, hmod⟩ := hc
    refine ⟨p, hpz.trans hzw, hp, ?_⟩
    have hcancel : b + (p - b % p) ≡ 0 [MOD p] := by
      calc
        b + (p - b % p) ≡ b % p + (p - b % p) [MOD p] :=
          (Nat.mod_modEq b p).symm.add_right _
        _ = p := by have := Nat.mod_lt b hp.pos; omega
        _ ≡ 0 [MOD p] := Nat.modulus_modEq_zero
    have heq := hmod.add_right (p - b % p)
    rw [show b + m + (p - b % p) = m + (b + (p - b % p)) by omega] at heq
    have hm' : m + (b + (p - b % p)) ≡ m [MOD p] := by
      simpa using hcancel.add_left m
    simpa only [c, if_pos hpz] using hm'.symm.trans heq
  · have hS : m ∈ S := Finset.mem_filter.mpr ⟨hm, hc⟩
    let u : ↥S := ⟨m, hS⟩
    have hT : f u ∈ T := hf ⟨u, rfl⟩
    obtain ⟨hpI, hp⟩ := Finset.mem_filter.mp hT
    obtain ⟨hzp, hpw⟩ := Finset.mem_Ioc.mp hpI
    have hinv : Function.partialInv f (f u) = some u :=
      Function.partialInv_left f.injective u
    refine ⟨f u, hpw, hp, ?_⟩
    have hres : c (f u) = m := by
      simp only [c, if_neg (not_le.mpr hzp), hinv]
      rfl
    rw [hres]

lemma covered_at_max (x : ℕ) : Green46.IsCoveredByResidues x (Erdos687.Y x) := by
  let lengths := {y : ℕ | Green46.IsCoveredByResidues x y}
  change sSup lengths ∈ lengths
  apply Nat.sSup_mem
  · exact ⟨0, fun _ ↦ 0, by simp⟩
  · exact ⟨primorial x, fun _ hy ↦ (Erdos687.lt_primorial_of_isCoveredByResidues hy).le⟩

/-- In a block too long to cover up to w, the survivors up to z outnumber
the primes still available in (z,w], for every offset and assignment. -/
lemma reserve_lt_survivors {K z w b : ℕ} (hzw : z ≤ w) (a : ℕ → ℕ)
    (hK : ¬ Green46.IsCoveredByResidues w K) :
    ((Finset.Ioc z w).filter Nat.Prime).card <
      ((Finset.Icc 1 K).filter fun m ↦
        ¬ ∃ p ≤ z, p.Prime ∧ (b + m) ≡ a p [MOD p]).card :=
  lt_of_not_ge fun h ↦ hK (cover_block_with_reserve hzw a h)

lemma covered_le_max {w K : ℕ} (hK : Green46.IsCoveredByResidues w K) :
    K ≤ Erdos687.Y w := by
  change K ≤ sSup {k : ℕ | Green46.IsCoveredByResidues w k}
  apply le_csSup (s := {k : ℕ | Green46.IsCoveredByResidues w k}) _ hK
  exact ⟨primorial w, fun _ hk ↦ (Erdos687.lt_primorial_of_isCoveredByResidues hk).le⟩

/-- The full blocks of length `K` in `[1,H]` contribute disjointly to the
count of positions satisfying `P`. -/
lemma mul_le_card_filter_of_block_lower_bound
    (P : ℕ → Prop) [DecidablePred P] {H K B : ℕ}
    (hB : ∀ j < H / K,
      B ≤ ((Finset.Icc 1 K).filter fun m ↦ P (j * K + m)).card) :
    (H / K) * B ≤ ((Finset.Icc 1 H).filter P).card := by
  let shift (j : ℕ) : ℕ ↪ ℕ :=
    ⟨fun m ↦ j * K + m, fun _ _ h ↦ Nat.add_left_cancel h⟩
  let block (j : ℕ) : Finset ℕ :=
    ((Finset.Icc 1 K).filter fun m ↦ P (j * K + m)).map (shift j)
  have block_bounds {j n : ℕ} (hn : n ∈ block j) : j * K < n ∧ n ≤ (j + 1) * K := by
    obtain ⟨m, hm, rfl⟩ := Finset.mem_map.mp hn
    obtain ⟨hm1, hmK⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
    change j * K < j * K + m ∧ j * K + m ≤ (j + 1) * K
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hd : (↑(Finset.range (H / K)) : Set ℕ).PairwiseDisjoint block := by
    intro j _ l _ hjl
    refine Finset.disjoint_left.mpr ?_
    intro n hjn hln
    have hjb := block_bounds hjn
    have hlb := block_bounds hln
    rcases lt_or_gt_of_ne hjl with hjl | hlj
    · have hbound : (j + 1) * K ≤ l * K := Nat.mul_le_mul_right K (by omega)
      omega
    · have hbound : (l + 1) * K ≤ j * K := Nat.mul_le_mul_right K (by omega)
      omega
  have hsub : (Finset.range (H / K)).biUnion block ⊆ (Finset.Icc 1 H).filter P := by
    intro n hn
    obtain ⟨j, hj, hjn⟩ := Finset.mem_biUnion.mp hn
    have hjq : j + 1 ≤ H / K := Finset.mem_range.mp hj
    have hend : (j + 1) * K ≤ H :=
      (Nat.mul_le_mul_right K hjq).trans (Nat.div_mul_le_self H K)
    obtain ⟨hstart, hfinish⟩ := block_bounds hjn
    have hnP : P n := by
      obtain ⟨m, hm, rfl⟩ := Finset.mem_map.mp hjn
      exact (Finset.mem_filter.mp hm).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hfinish.trans hend⟩, hnP⟩
  calc
    (H / K) * B = ∑ _j ∈ Finset.range (H / K), B := by simp
    _ ≤ ∑ j ∈ Finset.range (H / K), (block j).card := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [block, Finset.card_map] using hB j (Finset.mem_range.mp hj)
    _ = ((Finset.range (H / K)).biUnion block).card := (Finset.card_biUnion hd).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- Each full block of length Y(w)+1 has more survivors at z than there
are reserve primes in (z,w]. Summing them gives a uniform lower bound
on the number of survivors in any interval of length H. -/
theorem survivor_count_from_Y {z w H b : ℕ} (hzw : z ≤ w) (a : ℕ → ℕ) :
    (H / (Erdos687.Y w + 1)) * (((Finset.Ioc z w).filter Nat.Prime).card + 1) ≤
      ((Finset.Icc 1 H).filter fun m ↦
        ¬ ∃ p ≤ z, p.Prime ∧ (b + m) ≡ a p [MOD p]).card := by
  apply mul_le_card_filter_of_block_lower_bound
  intro j _
  have hlong : ¬ Green46.IsCoveredByResidues w (Erdos687.Y w + 1) :=
    fun hc ↦ (Nat.not_succ_le_self _) (covered_le_max hc)
  have h := reserve_lt_survivors (b := b + j * (Erdos687.Y w + 1)) hzw a hlong
  simpa only [Nat.add_assoc] using Nat.succ_le_of_lt h

lemma covered_prefix {x h H : ℕ} (hle : h ≤ H)
    (hc : Green46.IsCoveredByResidues x H) : Green46.IsCoveredByResidues x h := by
  obtain ⟨a, ha⟩ := hc
  exact ⟨a, fun m hm ↦ ha m (Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2.trans hle⟩)⟩

/-- Complete the shorter block supplied by the localization hypothesis. -/
lemma shorter_cover (h₂ : H2) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ j ≥ J, ∀ x : ℕ, (x : ℝ) ^ (1 + ε) ≤ (2 : ℝ) ^ (12 * j) →
      Green46.IsCoveredByResidues x (2 ^ (12 * j)) →
      Green46.IsCoveredByResidues (2 * 2 ^ (4 * j)) (2 ^ (6 * j)) := by
  obtain ⟨J, hJ⟩ := h₂ ε hε
  refine ⟨J, ?_⟩
  rintro j hj x hx ⟨a, ha⟩
  obtain ⟨b, _, hs⟩ := hJ j hj x hx a ha
  exact cover_block_with_reserve (by omega) a hs

/-- If badness propagates from a length to every admissible shorter length,
one sufficiently large good length gives an explicit threshold for all
subsequent lengths. -/
lemma eventually_good_of_descends (Bad : ℕ → Prop) {N t : ℕ}
    (descend : ∀ {j n : ℕ}, N ≤ j → 2 * j ≤ n → 2 * n ≤ 5 * j → Bad n → Bad j)
    (ht : max N 6 ≤ t) (hgood : ¬ Bad t) :
    ∀ n ≥ 16 * t, ¬ Bad n := by
  have htN : N ≤ t := (le_max_left _ _).trans ht
  have ht6 : 6 ≤ t := (le_max_right _ _).trans ht
  have propagate {a b : ℕ} (haN : N ≤ a) (ha6 : 6 ≤ a) (hab : a ≤ b)
      (hgoodInterval : ∀ j, a ≤ j → j ≤ b → ¬ Bad j) :
      ∀ n, 2 * a ≤ n → 2 * n ≤ 5 * b → ¬ Bad n := by
    intro n hnlo hnhi hn
    let j := min b (n / 2)
    have hjlo : a ≤ j := le_min hab (by omega)
    have hjhi : j ≤ b := min_le_left _ _
    have hjhalf : j ≤ n / 2 := min_le_right _ _
    have hshort : 2 * j ≤ n := by omega
    have hlong : 2 * n ≤ 5 * j := by
      rcases le_total b (n / 2) with h | h
      · simpa only [j, min_eq_left h] using hnhi
      · rw [show j = n / 2 by exact min_eq_right h]
        omega
    exact hgoodInterval j hjlo hjhi (descend (haN.trans hjlo) hshort hlong hn)
  have goodOne : ∀ n, 2 * t ≤ n → n ≤ 5 * t / 2 → ¬ Bad n := by
    intro n hnlo hnhi
    apply propagate htN ht6 le_rfl (a := t) (b := t) _ n hnlo (by omega)
    intro j hjlo hjhi
    rwa [le_antisymm hjhi hjlo]
  have goodTwo : ∀ n, 4 * t ≤ n → n ≤ 6 * t → ¬ Bad n := by
    intro n hnlo hnhi
    exact propagate (by omega) (by omega) (by omega) goodOne n (by omega) (by omega)
  have goodThree : ∀ n, 8 * t ≤ n → n ≤ 15 * t → ¬ Bad n := by
    intro n hnlo hnhi
    exact propagate (by omega) (by omega) (by omega) goodTwo n (by omega) (by omega)
  have goodFour : ∀ n, 16 * t ≤ n → n ≤ 32 * t → ¬ Bad n := by
    intro n hnlo hnhi
    exact propagate (by omega) (by omega) (by omega) goodThree n (by omega) (by omega)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnlo
    by_cases hnhi : n ≤ 32 * t
    · exact goodFour n hnlo hnhi
    · intro hn
      have hj : 16 * t ≤ n / 2 := by omega
      exact ih (n / 2) (by omega) hj (descend (by omega) (by omega) (by omega) hn)

/-- At ε = 1/8, a normalized cover at index n is long enough to invoke
localization at any j between 2n/5 and n/2. -/
lemma dyadic_growth {j n : ℕ} (hj : 2 ≤ j) (hn : 2 * n ≤ 5 * j) :
    ((2 * (2 : ℕ) ^ (4 * n) : ℕ) : ℝ) ^ (1 + (1 / 8 : ℝ)) ≤
      (2 : ℝ) ^ (12 * j) := by
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hnR : 2 * (n : ℝ) ≤ 5 * (j : ℝ) := by exact_mod_cast hn
  have hExp : ((4 * n + 1 : ℕ) : ℝ) * (1 + (1 / 8 : ℝ)) ≤ ((12 * j : ℕ) : ℝ) := by
    push_cast
    linarith
  rw [show 2 * (2 : ℕ) ^ (4 * n) = 2 ^ (4 * n + 1) by
    rw [pow_succ, mul_comm], Nat.cast_pow, Nat.cast_ofNat,
    ← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp

/-- A single large missing cover at the normalized scale rules out every
sufficiently large normalized cover. -/
lemma eventually_no_normalized_cover (h₁ : H1) (h₂ : H2) :
    ∃ A : ℕ, ∀ n ≥ A,
      ¬ Green46.IsCoveredByResidues (2 * 2 ^ (4 * n)) (2 ^ (6 * n)) := by
  let Bad (n : ℕ) := Green46.IsCoveredByResidues (2 * 2 ^ (4 * n)) (2 ^ (6 * n))
  obtain ⟨N, hN⟩ := shorter_cover h₂ (ε := 1 / 8) (by norm_num)
  obtain ⟨t, ht, hgood⟩ := h₁ (max (max N 2) 6)
  have descend {j n : ℕ} (hj : max N 2 ≤ j) (hshort : 2 * j ≤ n)
      (hlong : 2 * n ≤ 5 * j) (hc : Bad n) : Bad j := by
    have hlength : (2 : ℕ) ^ (12 * j) ≤ 2 ^ (6 * n) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    exact hN j (by omega) _ (dyadic_growth (by omega) hlong) (covered_prefix hlength hc)
  exact ⟨16 * t, eventually_good_of_descends Bad descend ht hgood⟩

/-- Interpolate between the geometric interval lengths with a factor of 4096. -/
theorem dyadic_interpolation (f : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (h : ∃ J : ℕ, ∀ j ≥ J, ∀ x : ℕ,
      (x : ℝ) ^ (1 + ε) ≤ (2 : ℝ) ^ (12 * j) → f x < (2 : ℕ) ^ (12 * j)) :
    Asymptotics.IsBigO atTop (fun x : ℕ ↦ (f x : ℝ))
      (fun x : ℕ ↦ (x : ℝ) ^ (1 + ε)) := by
  obtain ⟨J, hJ⟩ := h
  refine Asymptotics.isBigO_iff.mpr ⟨4096, eventually_atTop.mpr ?_⟩
  refine ⟨max 1 (4096 ^ J), fun x hx ↦ ?_⟩
  have hxone : (1 : ℕ) ≤ x := (le_max_left _ _).trans hx
  have hxle : (x : ℝ) ≤ (x : ℝ) ^ (1 + ε) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hxone : (1 : ℝ) ≤ x)
        (by linarith : (1 : ℝ) ≤ 1 + ε)
  have hnonneg : 0 ≤ (x : ℝ) ^ (1 + ε) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg hnonneg]
  by_contra! hlarge
  have hf0 : f x ≠ 0 := by
    intro hf
    rw [hf, Nat.cast_zero] at hlarge
    linarith
  let j := Nat.log 4096 (f x)
  have hJj : J ≤ j := by
    apply Nat.le_log_of_pow_le (by norm_num : 1 < (4096 : ℕ))
    have hxJ : (4096 : ℕ) ^ J ≤ x := (le_max_right _ _).trans hx
    have hxf : x ≤ f x := by
      exact_mod_cast hxle.trans
        (by linarith : (x : ℝ) ^ (1 + ε) ≤ (f x : ℝ))
    exact hxJ.trans hxf
  have hupper : f x < (4096 : ℕ) ^ (j + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hupperReal : (f x : ℝ) < (4096 : ℝ) ^ (j + 1) := by
    exact_mod_cast hupper
  have hinput : (x : ℝ) ^ (1 + ε) ≤ (2 : ℝ) ^ (12 * j) := by
    have hpow : (2 : ℝ) ^ (12 * j) = (4096 : ℝ) ^ j := by
      rw [pow_mul]
      norm_num
    rw [hpow]
    rw [pow_succ] at hupperReal
    linarith
  have hlower : (2 : ℕ) ^ (12 * j) ≤ f x := by
    rw [pow_mul]
    exact Nat.pow_log_le_self 4096 hf0
  exact (not_lt_of_ge hlower) (hJ j hJj x hinput)

theorem main : H1 → H2 → type_of% @Erdos687.erdos_687.parts.iii := by
  intro h₁ h₂ ε hε
  obtain ⟨A, hA⟩ := eventually_no_normalized_cover h₁ h₂
  obtain ⟨J, hJ⟩ := shorter_cover h₂ hε
  apply dyadic_interpolation Erdos687.Y ε hε
  refine ⟨max A J, ?_⟩
  intro j hj x hx
  by_contra! hlarge
  exact hA j (by omega) (hJ j (by omega) x hx (covered_prefix hlarge (covered_at_max x)))

end OMA.R_Erdos687_erdos_687_parts_iii_R2
