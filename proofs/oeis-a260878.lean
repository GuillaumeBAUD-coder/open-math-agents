import OMAStatements.S_oeis_a260878
import Mathlib

/-!
# Proof of Luschny's conjecture in OEIS A260878

`a(n)` is the number of set partitions of `{1, ..., 2n}` whose multiset of block sizes is `{n, n}`
or `{2n}`, and `b(6) = binomial(10, 5) + 1 = 253`. Claim: every prime `p > 253` divides
`a(p+5) - 253`.

Let `s` be a finite set with `2n` elements, `n >= 1`, and `x` an element of `s`.

1. Exactly one partition of `s` has block sizes `{2n}`: its only block is `s`.
2. A partition with block sizes `{n, n}` has two blocks `A`, `B`, disjoint with union `s`, so its
   blocks are the block `T` of `x` and `s \ T`. Conversely each `n`-subset `T` of `s` containing `x`
   gives the partition `{T, s \ T}`. So these partitions are in bijection with the `n`-subsets of
   `s` that contain `x`.
3. Complementation `T -> s \ T` exchanges the `n`-subsets containing `x` and those not containing
   `x`, so twice the number of the former is `binomial(2n, n)`.
4. The two shapes are different, hence `2 * (a(n) - 1) = binomial(2n, n)` for `n >= 1`.
5. Lucas: for a prime `p > 10`, `binomial(2p + 10, p + 5) = binomial(10, 5) * binomial(2, 1) = 504`
   modulo `p`.
6. So `p` divides `2 * (a(p+5) - 1) - 504 = 2 * (a(p+5) - 253)`, and `p` is odd.

The argument only uses `p > 10`; the entry asks for `p > 253`.
-/

/-- In a partition with block sizes `{n, n}` every block has `n` elements. -/
private lemma a260878_card_of_mem {s : Finset ℕ} {n : ℕ} (P : Finpartition s)
    (h : P.parts.val.map Finset.card = ({n, n} : Multiset ℕ)) {B : Finset ℕ} (hB : B ∈ P.parts) :
    B.card = n := by
  have hm : B.card ∈ P.parts.val.map Finset.card := Multiset.mem_map_of_mem _ hB
  rw [h] at hm
  simpa using hm

/-- A partition with block sizes `{n, n}` consists of the block of `x` and its complement. -/
private lemma a260878_decomp {s : Finset ℕ} {n x : ℕ} (hx : x ∈ s) (P : Finpartition s)
    (h : P.parts.val.map Finset.card = ({n, n} : Multiset ℕ)) :
    P.parts = {s \ P.part x, P.part x} := by
  have hc : P.parts.card = 2 := by
    have h' := congrArg Multiset.card h
    simpa using h'
  obtain ⟨A, B, hAB, hP⟩ := Finset.card_eq_two.mp hc
  have hA : A ∈ P.parts := by rw [hP]; simp
  have hB : B ∈ P.parts := by rw [hP]; simp
  have hsup : A ∪ B = s := by
    have h' := P.sup_parts
    rw [hP] at h'
    simpa using h'
  have hdisj : Disjoint A B := P.disjoint (Finset.mem_coe.2 hA) (Finset.mem_coe.2 hB) hAB
  have hT : P.part x ∈ P.parts := P.part_mem.2 hx
  generalize P.part x = T at hT ⊢
  rw [hP] at hT ⊢
  rw [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl
  · rw [← hsup, Finset.union_sdiff_cancel_left hdisj]
    exact Finset.pair_comm _ _
  · rw [← hsup, Finset.union_sdiff_cancel_right hdisj]

/-- Exactly one partition of a set with `2n >= 2` elements has block sizes `{2n}`. -/
private lemma a260878_one {s : Finset ℕ} {n : ℕ} (hn : 1 ≤ n) (hs : s.card = 2 * n) :
    ((Finset.univ : Finset (Finpartition s)).filter fun P =>
      P.parts.val.map Finset.card = ({2 * n} : Multiset ℕ)).card = 1 := by
  have hne : s ≠ ∅ := by
    intro h
    rw [h, Finset.card_empty] at hs
    omega
  rw [Finset.card_eq_one]
  refine ⟨Finpartition.indiscrete hne, ?_⟩
  ext P
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    have hc : P.parts.card = 1 := by
      have h' := congrArg Multiset.card h
      simpa using h'
    obtain ⟨B, hB⟩ := Finset.card_eq_one.mp hc
    have hBs : B = s := by
      have h' := P.sup_parts
      rw [hB] at h'
      simpa using h'
    apply Finpartition.ext
    rw [hB, hBs]
    rfl
  · rintro rfl
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [hs]

/-- The partition of `s` into the two blocks `T` and `s \ T`. -/
private def a260878_two {s T : Finset ℕ} (hT : T ⊆ s) (h1 : T ≠ ∅) (h2 : s \ T ≠ ∅) :
    Finpartition s :=
  (Finpartition.indiscrete h1).extend h2 Finset.disjoint_sdiff (Finset.union_sdiff_of_subset hT)

private lemma a260878_two_parts {s T : Finset ℕ} (hT : T ⊆ s) (h1 : T ≠ ∅) (h2 : s \ T ≠ ∅) :
    (a260878_two hT h1 h2).parts = {s \ T, T} := rfl

private lemma a260878_aux {s T : Finset ℕ} {n x : ℕ} (hn : 1 ≤ n) (hs : s.card = 2 * n)
    (hT : T ∈ (s.powersetCard n).filter fun T => x ∈ T) :
    T ⊆ s ∧ T.card = n ∧ x ∈ T ∧ T ≠ ∅ ∧ s \ T ≠ ∅ ∧ (s \ T).card = n := by
  rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
  obtain ⟨⟨hTs, hTc⟩, hxT⟩ := hT
  have hc : (s \ T).card = n := by
    rw [Finset.card_sdiff_of_subset hTs]; omega
  refine ⟨hTs, hTc, hxT, ?_, ?_, hc⟩
  · intro h; rw [h, Finset.card_empty] at hTc; omega
  · intro h; rw [h, Finset.card_empty] at hc; omega

/-- Partitions with block sizes `{n, n}` correspond to the `n`-subsets containing `x`. -/
private lemma a260878_bij {s : Finset ℕ} {n x : ℕ} (hn : 1 ≤ n) (hs : s.card = 2 * n)
    (hx : x ∈ s) :
    ((Finset.univ : Finset (Finpartition s)).filter fun P =>
      P.parts.val.map Finset.card = ({n, n} : Multiset ℕ)).card =
    ((s.powersetCard n).filter fun T => x ∈ T).card := by
  symm
  refine Finset.card_bij
    (fun T hT => a260878_two (a260878_aux hn hs hT).1 (a260878_aux hn hs hT).2.2.2.1
      (a260878_aux hn hs hT).2.2.2.2.1) ?_ ?_ ?_
  · intro T hT
    obtain ⟨hTs, hTc, hxT, h1, h2, hc⟩ := a260878_aux hn hs hT
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [a260878_two_parts]
    have hne : s \ T ∉ ({T} : Finset (Finset ℕ)) := by
      rw [Finset.mem_singleton]
      intro h
      have hd : Disjoint T (s \ T) := Finset.disjoint_sdiff
      rw [h] at hd
      exact h1 (disjoint_self.mp hd)
    rw [Finset.insert_val_of_notMem hne]
    simp [hTc, hc]
  · intro T₁ hT₁ T₂ hT₂ h
    obtain ⟨hTs₁, hTc₁, hxT₁, -⟩ := a260878_aux hn hs hT₁
    obtain ⟨hTs₂, hTc₂, hxT₂, -⟩ := a260878_aux hn hs hT₂
    have hp := congrArg Finpartition.parts h
    rw [a260878_two_parts, a260878_two_parts] at hp
    have hm : T₁ ∈ ({s \ T₂, T₂} : Finset (Finset ℕ)) := by
      rw [← hp]; simp
    rw [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · exfalso
      rw [hm] at hxT₁
      exact (Finset.mem_sdiff.mp hxT₁).2 hxT₂
    · exact hm
  · intro P hP
    rw [Finset.mem_filter] at hP
    have hsz := hP.2
    have hmem : P.part x ∈ (s.powersetCard n).filter fun T => x ∈ T := by
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨P.part_subset x, a260878_card_of_mem P hsz (P.part_mem.2 hx)⟩,
        P.mem_part_self.2 hx⟩
    refine ⟨P.part x, hmem, ?_⟩
    apply Finpartition.ext
    rw [a260878_two_parts]
    exact (a260878_decomp hx P hsz).symm

/-- Half of the `n`-subsets of a `2n`-set contain a given element. -/
private lemma a260878_half {s : Finset ℕ} {n x : ℕ} (hs : s.card = 2 * n) (hx : x ∈ s) :
    2 * ((s.powersetCard n).filter fun T => x ∈ T).card = (2 * n).choose n := by
  have h1 := Finset.card_filter_add_card_filter_not (s := s.powersetCard n) (fun T => x ∈ T)
  rw [Finset.card_powersetCard, hs] at h1
  have h2 : ((s.powersetCard n).filter fun T => ¬ x ∈ T).card =
      ((s.powersetCard n).filter fun T => x ∈ T).card := by
    refine Finset.card_bij (fun T _ => s \ T) ?_ ?_ ?_
    · intro T hT
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hT ⊢
      obtain ⟨⟨hTs, hTc⟩, hxT⟩ := hT
      refine ⟨⟨Finset.sdiff_subset, ?_⟩, Finset.mem_sdiff.mpr ⟨hx, hxT⟩⟩
      rw [Finset.card_sdiff_of_subset hTs]; omega
    · intro T₁ hT₁ T₂ hT₂ h
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hT₁ hT₂
      calc T₁ = s \ (s \ T₁) := (Finset.sdiff_sdiff_eq_self hT₁.1.1).symm
        _ = s \ (s \ T₂) := congrArg (fun U => s \ U) h
        _ = T₂ := Finset.sdiff_sdiff_eq_self hT₂.1.1
    · intro T hT
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
      obtain ⟨⟨hTs, hTc⟩, hxT⟩ := hT
      refine ⟨s \ T, ?_, Finset.sdiff_sdiff_eq_self hTs⟩
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.sdiff_subset, ?_⟩, fun h => (Finset.mem_sdiff.mp h).2 hxT⟩
      rw [Finset.card_sdiff_of_subset hTs]; omega
  omega

/-- For `n >= 1`: `2 * (a(n) - 1) = binomial(2n, n)`. -/
private lemma a260878_count {n : ℕ} (hn : 1 ≤ n) :
    2 * (OMA.S_oeis_a260878.a n - 1) = ((2 * n).choose n : ℤ) := by
  have hn0 : ¬ n = 0 := by omega
  have hs : (Finset.Icc 1 (2 * n)).card = 2 * n := by simp
  have hx : 1 ∈ Finset.Icc 1 (2 * n) := by
    rw [Finset.mem_Icc]; omega
  have hd : Disjoint
      ((Finset.univ : Finset (Finpartition (Finset.Icc 1 (2 * n)))).filter fun P =>
        P.parts.val.map Finset.card = ({n, n} : Multiset ℕ))
      ((Finset.univ : Finset (Finpartition (Finset.Icc 1 (2 * n)))).filter fun P =>
        P.parts.val.map Finset.card = ({2 * n} : Multiset ℕ)) := by
    rw [Finset.disjoint_filter]
    intro P _ h1 h2
    rw [h1] at h2
    have h' := congrArg Multiset.card h2
    simp at h'
  have hh := a260878_half hs hx
  have hh' : (2 : ℤ) *
      ((((Finset.Icc 1 (2 * n)).powersetCard n).filter fun T => 1 ∈ T).card : ℤ) =
      ((2 * n).choose n : ℤ) := by exact_mod_cast hh
  unfold OMA.S_oeis_a260878.a
  rw [if_neg hn0, Finset.filter_or, Finset.card_union_of_disjoint hd, a260878_one hn hs,
    a260878_bij hn hs hx]
  push_cast
  linarith

/-- Luschny's conjecture in A260878: `p` divides `a(p+5) - b(6)` for every prime `p > b(6) = 253`. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a260878.main := by
  intro p hp hb
  have hb6 : OMA.S_oeis_a260878.b 6 = 253 := by
    unfold OMA.S_oeis_a260878.b
    norm_num [Nat.choose]
  rw [hb6] at hb ⊢
  have hp253 : 253 < p := by exact_mod_cast hb
  have hcount := a260878_count (n := p + 5) (by omega)
  have : Fact p.Prime := ⟨hp⟩
  have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2 * (p + 5)) (k := p + 5)
    (p := p)
  have e1 : (2 * (p + 5)) % p = 10 := by
    rw [show 2 * (p + 5) = 10 + p * 2 by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
  have e2 : (2 * (p + 5)) / p = 2 := by
    rw [show 2 * (p + 5) = 10 + p * 2 by ring, Nat.add_mul_div_left _ _ hp.pos,
      Nat.div_eq_of_lt (by omega)]
  have e3 : (p + 5) % p = 5 := by
    rw [show p + 5 = 5 + p * 1 by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have e4 : (p + 5) / p = 1 := by
    rw [show p + 5 = 5 + p * 1 by ring, Nat.add_mul_div_left _ _ hp.pos,
      Nat.div_eq_of_lt (by omega)]
  have h504 : Nat.choose 10 5 * Nat.choose 2 1 = 504 := by decide
  rw [e1, e2, e3, e4, h504] at hl
  have hz : (p : ℤ) ∣ ((2 * (p + 5)).choose (p + 5) : ℤ) - 504 := by
    have h' := Nat.modEq_iff_dvd.mp hl.symm
    exact_mod_cast h'
  rw [← hcount] at hz
  have h2 : (p : ℤ) ∣ 2 * (OMA.S_oeis_a260878.a (p + 5) - 253) := by
    have e : 2 * (OMA.S_oeis_a260878.a (p + 5) - 253) =
        2 * (OMA.S_oeis_a260878.a (p + 5) - 1) - 504 := by ring
    rw [e]
    exact hz
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h2 with h | h
  · exfalso
    have hle := Int.le_of_dvd (by norm_num) h
    omega
  · exact h
