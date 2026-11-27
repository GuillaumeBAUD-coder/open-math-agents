import FormalConjectures.ErdosProblems.«770»
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Reduction of Erdős Problem 770 (three) to small- and large-multiplier prime counts

Reduction `Erdos770.erdos_770.variants.three.R1`.

For `n ≥ 1`, `h n = 3` holds if and only if `Nat.gcd (2 ^ n - 1) (3 ^ n - 1) = 1`.
For an odd prime `p`, any prime `q` dividing both `2 ^ p - 1` and `3 ^ p - 1` must satisfy:
- `2 * p ∣ q - 1` (as the multiplicative order of `2` mod `q` is `p`, and `q` is odd), and
- `q % 24 = 1 ∨ q % 24 = 23` (since `2 ^ p ≡ 3 ^ p ≡ 1 (mod q)` with `p` odd forces both `2`
  and `3` to be quadratic residues modulo `q`, so `q ≡ ±1 (mod 8)` and `q ≡ ±1 (mod 12)`).

We split the set of bad odd primes `p ≤ X` (those with `gcd(2^p - 1, 3^p - 1) > 1`) at the
threshold `q ≤ p * ⌊√(log₂ X)⌋`:

- `H1` (small-multiplier regime, unconditionally approachable via Selberg's sieve):
  for all sufficiently large `X`, at most `1/3` of odd primes `p ≤ X` admit such a common prime
  divisor `q ≤ p * ⌊√(log₂ X)⌋`.
- `H2` (large-multiplier regime, the open core):
  for arbitrarily large `X`, at most `1/3` of odd primes `p ≤ X` admit such a common prime
  divisor `q > p * ⌊√(log₂ X)⌋`.

`main` proves the equivalence `h n = 3 ↔ Nat.gcd (2 ^ n - 1) (3 ^ n - 1) = 1`, establishes the
congruence conditions `2 * p ∣ q - 1` and `q % 24 = 1 ∨ q % 24 = 23` via quadratic reciprocity,
and combines `H1`, `H2`, and the infinitude of primes to deduce `{n | h n = 3}.Infinite`.
-/

namespace OMA.R_Erdos770_erdos_770_variants_three_R1

open Erdos770

-- Small-multiplier regime: eventually at most 1/3 of odd primes p ≤ X have a common prime divisor
-- q ≤ p * ⌊√(log₂ X)⌋ of 2^p - 1 and 3^p - 1 with 2p ∣ q - 1 and q ≡ ±1 (mod 24).
def H1 : Prop :=
  ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    3 * {p : ℕ | p.Prime ∧ 2 < p ∧ p ≤ X ∧
      ∃ q : ℕ, q.Prime ∧ 2 * p ∣ q - 1 ∧ (q % 24 = 1 ∨ q % 24 = 23) ∧
        q ∣ 2 ^ p - 1 ∧ q ∣ 3 ^ p - 1 ∧ q ≤ p * Nat.sqrt (Nat.log 2 X)}.ncard
    ≤ {p : ℕ | p.Prime ∧ 2 < p ∧ p ≤ X}.ncard

-- Large-multiplier regime: for arbitrarily large X, at most 1/3 of odd primes p ≤ X have a common
-- prime divisor q > p * ⌊√(log₂ X)⌋ of 2^p - 1 and 3^p - 1 with 2p ∣ q - 1 and q ≡ ±1 (mod 24).
def H2 : Prop :=
  ∀ M : ℕ, ∃ X : ℕ, M ≤ X ∧
    3 * {p : ℕ | p.Prime ∧ 2 < p ∧ p ≤ X ∧
      ∃ q : ℕ, q.Prime ∧ 2 * p ∣ q - 1 ∧ (q % 24 = 1 ∨ q % 24 = 23) ∧
        q ∣ 2 ^ p - 1 ∧ q ∣ 3 ^ p - 1 ∧ p * Nat.sqrt (Nat.log 2 X) < q}.ncard
    ≤ {p : ℕ | p.Prime ∧ 2 < p ∧ p ≤ X}.ncard

lemma gcd_Icc_two_three (n : ℕ) :
    ((Finset.Icc 2 3).image fun i => (i ^ n - 1)).gcd id = Nat.gcd (2 ^ n - 1) (3 ^ n - 1) := by
  have hIcc : Finset.Icc 2 3 = {2, 3} := by decide
  rw [hIcc, Finset.image_insert, Finset.image_singleton, Finset.gcd_insert, Finset.gcd_singleton]
  simp only [id, normalize_eq]
  rfl

lemma h_eq_three_of_gcd_eq_one {n : ℕ} (hg : Nat.gcd (2 ^ n - 1) (3 ^ n - 1) = 1) :
    h n = 3 := by
  unfold h
  apply le_antisymm
  · refine sInf_le ⟨by norm_num, ?_⟩
    simpa [gcd_Icc_two_three] using hg
  · refine le_sInf ?_
    rintro m ⟨hm, -⟩
    induction m using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      have hm' : 2 < m := by exact_mod_cast hm
      exact_mod_cast (by omega : 3 ≤ m)

lemma dvd_pow_sub_one_iff {q a n : ℕ} (ha : 1 ≤ a) :
    q ∣ a ^ n - 1 ↔ (a : ZMod q) ^ n = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ ha)]
  push_cast
  exact sub_eq_zero

lemma common_prime_properties {p q : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hq : q.Prime)
    (h2 : q ∣ 2 ^ p - 1) (h3 : q ∣ 3 ^ p - 1) :
    2 * p ∣ q - 1 ∧ (q % 24 = 1 ∨ q % 24 = 23) := by
  have hq2 : q ≠ 2 := by
    rintro rfl
    have hd1 : 2 ∣ 2 ^ p := dvd_pow_self 2 (by omega)
    have hd2 := Nat.dvd_sub hd1 h2
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by norm_num))] at hd2
    omega
  have hq3 : q ≠ 3 := by
    rintro rfl
    have hd1 : 3 ∣ 3 ^ p := dvd_pow_self 3 (by omega)
    have hd2 := Nat.dvd_sub hd1 h3
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by norm_num))] at hd2
    omega
  have hq_odd : q % 2 = 1 := by
    have := hq.eq_two_or_odd
    omega
  have hp_odd : p % 2 = 1 := by
    have := hp.eq_two_or_odd
    omega
  have : Fact q.Prime := ⟨hq⟩
  have h2z : (2 : ZMod q) ^ p = 1 := (dvd_pow_sub_one_iff (by norm_num)).1 h2
  have h3z : (3 : ZMod q) ^ p = 1 := (dvd_pow_sub_one_iff (by norm_num)).1 h3
  have h2ne0 : (2 : ZMod q) ≠ 0 := by
    change ((2 : ℕ) : ZMod q) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    have := hq.two_le
    omega
  have h2ne1 : (2 : ZMod q) ≠ 1 := by
    intro h
    have hsub : ((2 - 1 : ℕ) : ZMod q) = 0 := by
      rw [Nat.cast_sub (by norm_num)]
      push_cast
      exact sub_eq_zero.2 h
    rw [ZMod.natCast_eq_zero_iff] at hsub
    have := Nat.le_of_dvd (by norm_num) hsub
    have := hq.two_le
    omega
  have hord_dvd : orderOf (2 : ZMod q) ∣ p := orderOf_dvd_of_pow_eq_one h2z
  have hord_ne1 : orderOf (2 : ZMod q) ≠ 1 := by
    rw [Ne, orderOf_eq_one_iff]
    exact h2ne1
  have hord_eq : orderOf (2 : ZMod q) = p := (hp.eq_one_or_self_of_dvd _ hord_dvd).resolve_left hord_ne1
  have hp_dvd : p ∣ q - 1 := by
    rw [← hord_eq]
    exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h2ne0)
  have h2_dvd : 2 ∣ q - 1 := by omega
  have h2p_dvd : 2 * p ∣ q - 1 := by
    have hcop : Nat.Coprime 2 p := by
      rw [Nat.coprime_two_left]
      exact Nat.odd_iff.2 hp_odd
    exact hcop.mul_dvd_of_dvd_of_dvd h2_dvd hp_dvd
  have hsq2 : IsSquare (2 : ZMod q) := by
    refine ⟨(2 : ZMod q) ^ ((p + 1) / 2), ?_⟩
    rw [← sq, ← pow_mul]
    have hmul : (p + 1) / 2 * 2 = p + 1 := by omega
    rw [hmul, pow_succ, h2z, one_mul]
  have hsq3 : IsSquare (3 : ZMod q) := by
    refine ⟨(3 : ZMod q) ^ ((p + 1) / 2), ?_⟩
    rw [← sq, ← pow_mul]
    have hmul : (p + 1) / 2 * 2 = p + 1 := by omega
    rw [hmul, pow_succ, h3z, one_mul]
  have hmod8 : q % 8 = 1 ∨ q % 8 = 7 := by
    exact (ZMod.exists_sq_eq_two_iff hq2).1 hsq2
  have hmod12 : q % 12 = 1 ∨ q % 12 = 11 := by
    have hleg3 : legendreSym q 3 = 1 := by
      rw [legendreSym.eq_one_iff]
      · simpa using hsq3
      · norm_cast
        change ((3 : ℕ) : ZMod q) ≠ 0
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro h
        have := Nat.le_of_dvd (by norm_num) h
        have := hq.two_le
        omega
    have hqr := legendreSym.quadratic_reciprocity hq2 (by decide : (3 : ℕ) ≠ 2) hq3
    simp only [Nat.cast_ofNat] at hqr
    have hmod4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
    have hmod3 : q % 3 = 1 ∨ q % 3 = 2 := by
      have : q % 3 ≠ 0 := by
        intro h0
        exact hq3 ((hq.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h0)).resolve_left (by omega)).symm
      omega
    rcases hmod4 with h4 | h4 <;> rcases hmod3 with h3m | h3m
    · left; omega
    · exfalso
      have h1 : (-1 : ℤ) ^ (q / 2 * (3 / 2)) = 1 := by
        have : q / 2 * (3 / 2) = 2 * (q / 4) := by omega
        rw [this, pow_mul]
        norm_num
      have hq3_mod : (q : ℤ) % 3 = 2 := by omega
      have hleg_q3 : legendreSym 3 (q : ℤ) = -1 := by
        rw [legendreSym.mod, Nat.cast_ofNat, hq3_mod]
        decide
      rw [h1, hleg3, hleg_q3] at hqr
      omega
    · exfalso
      have h1 : (-1 : ℤ) ^ (q / 2 * (3 / 2)) = -1 := by
        have : q / 2 * (3 / 2) = 2 * (q / 4) + 1 := by omega
        rw [this, pow_succ, pow_mul]
        norm_num
      have hq3_mod : (q : ℤ) % 3 = 1 := by omega
      have hleg_q3 : legendreSym 3 (q : ℤ) = 1 := by
        rw [legendreSym.mod, Nat.cast_ofNat, hq3_mod]
        decide
      rw [h1, hleg3, hleg_q3] at hqr
      omega
    · right; omega
  refine ⟨h2p_dvd, ?_⟩
  omega

lemma exists_large_odd_prime_ncard (M : ℕ) :
    ∃ X₁ : ℕ, M < {p : ℕ | p.Prime ∧ 2 < p ∧ p ≤ X₁}.ncard := by
  have hinf : {p : ℕ | p.Prime ∧ 2 < p}.Infinite := by
    have h1 : {p : ℕ | p.Prime}.Infinite := Nat.infinite_setOfPred_prime
    have h2 : ({p : ℕ | p.Prime} \ {2}).Infinite := h1.sdiff (Set.finite_singleton 2)
    refine h2.mono ?_
    rintro p ⟨hp, hp2⟩
    refine ⟨hp, ?_⟩
    have := hp.two_le
    simp only [Set.mem_singleton_iff] at hp2
    omega
  obtain ⟨S, hSsub, hScard⟩ := hinf.exists_subset_card_eq (M + 1)
  refine ⟨S.sup id, ?_⟩
  have hsub : (S : Set ℕ) ⊆ {p : ℕ | p.Prime ∧ 2 < p ∧ p ≤ S.sup id} := by
    intro p hp
    have hpS := hSsub hp
    exact ⟨hpS.1, hpS.2, Finset.le_sup (f := id) hp⟩
  have hfin : {p : ℕ | p.Prime ∧ 2 < p ∧ p ≤ S.sup id}.Finite :=
    (Set.finite_Iic (S.sup id)).subset (fun _ hp => hp.2.2)
  have hle := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, hScard] at hle
  omega

theorem main : H1 → H2 → type_of% @Erdos770.erdos_770.variants.three := by
  intro h1 h2
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  obtain ⟨X₀, hX₀⟩ := h1
  obtain ⟨X₁, hX₁⟩ := exists_large_odd_prime_ncard (3 * (N + 1))
  obtain ⟨X, hXge, hX2⟩ := h2 (max X₀ X₁)
  have hX0' : X₀ ≤ X := le_trans (le_max_left _ _) hXge
  have hX1' : X₁ ≤ X := le_trans (le_max_right _ _) hXge
  have hX1_bound := hX₀ X hX0'
  set P := {p : ℕ | p.Prime ∧ 2 < p ∧ p ≤ X}
  set B₁ := {p : ℕ | p.Prime ∧ 2 < p ∧ p ≤ X ∧
    ∃ q : ℕ, q.Prime ∧ 2 * p ∣ q - 1 ∧ (q % 24 = 1 ∨ q % 24 = 23) ∧
      q ∣ 2 ^ p - 1 ∧ q ∣ 3 ^ p - 1 ∧ q ≤ p * Nat.sqrt (Nat.log 2 X)}
  set B₂ := {p : ℕ | p.Prime ∧ 2 < p ∧ p ≤ X ∧
    ∃ q : ℕ, q.Prime ∧ 2 * p ∣ q - 1 ∧ (q % 24 = 1 ∨ q % 24 = 23) ∧
      q ∣ 2 ^ p - 1 ∧ q ∣ 3 ^ p - 1 ∧ p * Nat.sqrt (Nat.log 2 X) < q}
  have hP_fin : P.Finite := (Set.finite_Iic X).subset (fun _ hp => hp.2.2)
  have hB1_fin : B₁.Finite := hP_fin.subset (fun _ hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
  have hB2_fin : B₂.Finite := hP_fin.subset (fun _ hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
  have hIic_fin : (Set.Iic N).Finite := Set.finite_Iic N
  have hP_large : 3 * (N + 1) < P.ncard := by
    have hsub : {p : ℕ | p.Prime ∧ 2 < p ∧ p ≤ X₁} ⊆ P :=
      fun _ hp => ⟨hp.1, hp.2.1, le_trans hp.2.2 hX1'⟩
    exact lt_of_lt_of_le hX₁ (Set.ncard_le_ncard hsub hP_fin)
  have hcover : P ⊆ Set.Iic N ∪ (B₁ ∪ B₂) := by
    rintro p ⟨hp, hp2, hpX⟩
    by_cases hpN : p ≤ N
    · exact Or.inl hpN
    · right
      have hne3 : h p ≠ 3 := fun heq => hpN (hN heq)
      have hgcd_ne1 : Nat.gcd (2 ^ p - 1) (3 ^ p - 1) ≠ 1 :=
        fun hg => hne3 (h_eq_three_of_gcd_eq_one hg)
      obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hgcd_ne1
      have hq2 : q ∣ 2 ^ p - 1 := dvd_trans hqdvd (Nat.gcd_dvd_left _ _)
      have hq3 : q ∣ 3 ^ p - 1 := dvd_trans hqdvd (Nat.gcd_dvd_right _ _)
      obtain ⟨h2p, hmod24⟩ := common_prime_properties hp hp2 hq hq2 hq3
      rcases le_or_gt q (p * Nat.sqrt (Nat.log 2 X)) with hle | hgt
      · exact Or.inl ⟨hp, hp2, hpX, q, hq, h2p, hmod24, hq2, hq3, hle⟩
      · exact Or.inr ⟨hp, hp2, hpX, q, hq, h2p, hmod24, hq2, hq3, hgt⟩
  have hcard_le : P.ncard ≤ (Set.Iic N).ncard + (B₁.ncard + B₂.ncard) := by
    calc P.ncard
        ≤ (Set.Iic N ∪ (B₁ ∪ B₂)).ncard := Set.ncard_le_ncard hcover (hIic_fin.union (hB1_fin.union hB2_fin))
      _ ≤ (Set.Iic N).ncard + (B₁ ∪ B₂).ncard := Set.ncard_union_le _ _
      _ ≤ (Set.Iic N).ncard + (B₁.ncard + B₂.ncard) := Nat.add_le_add_left (Set.ncard_union_le _ _) _
  have hIic_card : (Set.Iic N).ncard = N + 1 := by
    have : Set.Iic N = (Finset.Iic N : Set ℕ) := by ext; simp
    rw [this, Set.ncard_coe_finset, Nat.card_Iic]
  omega

end OMA.R_Erdos770_erdos_770_variants_three_R1
