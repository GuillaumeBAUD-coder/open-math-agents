import OMAReductions.R_Erdos210_erdos_210_variants_csima_sawyer_R1

/-!
The two-pencil case is counted by pairs from the exclusive parts of
the two covering lines. The remaining local inequalities are the two
Kelly–Moser attachment lemmas, restated in Lenchner, CCCG 2005, §2.
-/

-- Credit: @dk8827

open EuclideanGeometry Finset
open scoped Pointwise BigOperators Classical

namespace OMA.TwoPencils

private theorem generated {L : AffineSubspace ℝ ℝ²}
    (hL : Module.finrank ℝ L.direction = 1) {a b : ℝ²}
    (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) : line[ℝ, a, b] = L := by
  apply (AffineSubspace.eq_iff_direction_eq_of_mem
    (left_mem_affineSpan_pair ℝ a b) ha).2
  apply Submodule.eq_of_le_of_finrank_eq
  · exact AffineSubspace.direction_le (affineSpan_pair_le_of_mem_of_mem ha hb)
  · rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hab)]
    exact hL.symm

private theorem collinear_subset {s : Set ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : Module.finrank ℝ L.direction = 1) (hs : s ⊆ L) : Collinear ℝ s := by
  rw [collinear_iff_finrank_le_one]
  have hle : vectorSpan ℝ s ≤ L.direction := by
    rw [← direction_affineSpan]
    exact AffineSubspace.direction_le (affineSpan_le.2 hs)
  exact (Submodule.finrank_mono hle).trans hL.le

theorem count (s : Finset ℝ²) (hs : 4 ≤ s.card) (hc : ¬ Collinear ℝ (s : Set ℝ²))
    (L M : AffineSubspace ℝ ℝ²) (hL : Module.finrank ℝ L.direction = 1)
    (hM : Module.finrank ℝ M.direction = 1) (hcov : ∀ p ∈ s, p ∈ L ∨ p ∈ M) :
    s.card ≤ 2 * (ordinaryLines s).card := by
  classical
  let A := s.filter (fun p => p ∈ L ∧ p ∉ M)
  let B := s.filter (fun p => p ∈ M ∧ p ∉ L)
  let I := s.filter (fun p => p ∈ L ∧ p ∈ M)
  have hLM : L ≠ M := by
    rintro rfl
    exact hc (collinear_subset hL (fun p hp => (hcov p hp).elim id id))
  have hA : A.Nonempty := by
    by_contra h
    apply hc (collinear_subset hM ?_)
    intro p hp
    by_contra hpm
    have hpl := (hcov p hp).resolve_right hpm
    exact h ⟨p, mem_filter.2 ⟨hp, hpl, hpm⟩⟩
  have hB : B.Nonempty := by
    by_contra h
    apply hc (collinear_subset hL ?_)
    intro p hp
    by_contra hpl
    have hpm := (hcov p hp).resolve_left hpl
    exact h ⟨p, mem_filter.2 ⟨hp, hpm, hpl⟩⟩
  have hI : I.card ≤ 1 := by
    apply card_le_one.2
    intro a ha b hb
    by_contra h
    obtain ⟨_, haL, haM⟩ := mem_filter.1 ha
    obtain ⟨_, hbL, hbM⟩ := mem_filter.1 hb
    exact hLM ((generated hL haL hbL h).symm.trans (generated hM haM hbM h))
  have hcard : s.card ≤ A.card + B.card + 1 := by
    have hsub : s ⊆ A ∪ B ∪ I := by
      intro p hp
      by_cases hpL : p ∈ L <;> by_cases hpM : p ∈ M
      · exact mem_union_right _ (mem_filter.2 ⟨hp, hpL, hpM⟩)
      · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hp, hpL, hpM⟩))
      · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hp, hpM, hpL⟩))
      · exact ((hcov p hp).elim hpL hpM).elim
    have h₁ := card_le_card hsub
    have h₂ := card_union_le (A ∪ B) I
    have h₃ := card_union_le A B
    omega
  have hcut (a b : ℝ²) (ha : a ∈ A) (hb : b ∈ B) :
      s.filter (fun p => p ∈ line[ℝ, a, b]) = {a, b} := by
    obtain ⟨has, haL, haM⟩ := mem_filter.1 ha
    obtain ⟨hbs, hbM, hbL⟩ := mem_filter.1 hb
    have hab : a ≠ b := fun h => hbL (h ▸ haL)
    let N : AffineSubspace ℝ ℝ² := line[ℝ, a, b]
    have haN : a ∈ N := left_mem_affineSpan_pair ℝ a b
    have hbN : b ∈ N := right_mem_affineSpan_pair ℝ a b
    have hN : Module.finrank ℝ N.direction = 1 := by
      rw [show N = line[ℝ, a, b] from rfl, direction_affineSpan, vectorSpan_pair,
        finrank_span_singleton (vsub_ne_zero.mpr hab)]
    ext z
    constructor
    · intro hz
      obtain ⟨hzs, hzN⟩ := mem_filter.1 hz
      rcases hcov z hzs with hzL | hzM
      · have hza : z = a := by
          by_contra hh
          have he := (generated hN hzN haN hh).symm.trans (generated hL hzL haL hh)
          exact hbL (he ▸ hbN)
        simp [hza]
      · have hzb : z = b := by
          by_contra hh
          have he := (generated hN hzN hbN hh).symm.trans (generated hM hzM hbM hh)
          exact haM (he ▸ haN)
        simp [hzb]
    · intro hz
      rcases mem_insert.1 hz with rfl | hz
      · exact mem_filter.2 ⟨has, haN⟩
      · obtain rfl := mem_singleton.1 hz
        exact mem_filter.2 ⟨hbs, hbN⟩
  have hcross : A.card * B.card ≤ (ordinaryLines s).card := by
    rw [← card_product]
    apply card_le_card_of_injOn (fun z : ℝ² × ℝ² => line[ℝ, z.1, z.2])
    · rintro ⟨a, b⟩ h
      obtain ⟨ha, hb⟩ := mem_product.1 h
      obtain ⟨has, haL, _⟩ := mem_filter.1 ha
      obtain ⟨hbs, _, hbL⟩ := mem_filter.1 hb
      have hab : a ≠ b := fun he => hbL (he ▸ haL)
      exact mem_ordinaryLines.2 ⟨⟨a, has, b, hbs, hab, rfl⟩, by rw [hcut a b ha hb]; simp [hab]⟩
    · rintro ⟨a, b⟩ h ⟨c, d⟩ h' he
      obtain ⟨ha, hb⟩ := mem_product.1 h
      obtain ⟨hc, hd⟩ := mem_product.1 h'
      change line[ℝ, a, b] = line[ℝ, c, d] at he
      have habcd : ({a, b} : Finset ℝ²) = {c, d} := by
        rw [← hcut a b ha hb, ← hcut c d hc hd, he]
      have hca : a = c := by
        have hm : a ∈ ({c, d} : Finset ℝ²) := habcd ▸ by simp
        have hmem := mem_insert.1 hm
        refine hmem.resolve_right ?_
        intro had
        exact (mem_filter.1 hd).2.2 ((mem_singleton.1 had) ▸ (mem_filter.1 ha).2.1)
      have hdb : b = d := by
        have hm : b ∈ ({c, d} : Finset ℝ²) := habcd ▸ by simp
        have hmem := mem_insert.1 hm
        refine mem_singleton.1 (hmem.resolve_left ?_)
        intro hbc
        exact (mem_filter.1 hc).2.2 (hbc ▸ (mem_filter.1 hb).2.1)
      exact Prod.ext hca hdb
  have hA0 := card_pos.2 hA
  have hB0 := card_pos.2 hB
  have hsizes : A.card + B.card ≤ A.card * B.card + 1 := by
    obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hA0.ne'
    obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero hB0.ne'
    rw [ha, hb, Nat.succ_mul, Nat.mul_succ]
    omega
  omega

end OMA.TwoPencils

namespace OMA.R_Erdos210_erdos_210_variants_csima_sawyer_R1_H1_R1

def H1 : Prop :=
  ∀ (s : Finset ℝ²), 8 ≤ s.card → ¬ Collinear ℝ (s : Set ℝ²) →
  ¬ (∃ L M : AffineSubspace ℝ ℝ², Module.finrank ℝ L.direction = 1 ∧
    Module.finrank ℝ M.direction = 1 ∧ ∀ p ∈ s, p ∈ L ∨ p ∈ M) →
  let O := ordinaryLines s
  let d := fun p : ℝ² => (O.filter (fun L => p ∈ L)).card
  let v := fun p : ℝ² => (![p 0, p 1, 1] : Fin 3 → ℝ)
  let attached := fun (w : ℝ²) (L : AffineSubspace ℝ ℝ²) =>
    ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
      ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
        ∀ z ∈ s, ∃ a b c : ℝ,
          v z = a • v p + b • (ε • v q) + c • (δ • v w) ∧
          ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))
  let A := fun p => (O.filter (attached p)).card
  ∀ p ∈ s, d p = 0 → 3 ≤ A p

def H2 : Prop :=
  ∀ (s : Finset ℝ²), 8 ≤ s.card → ¬ Collinear ℝ (s : Set ℝ²) →
  ¬ (∃ L M : AffineSubspace ℝ ℝ², Module.finrank ℝ L.direction = 1 ∧
    Module.finrank ℝ M.direction = 1 ∧ ∀ p ∈ s, p ∈ L ∨ p ∈ M) →
  let O := ordinaryLines s
  let d := fun p : ℝ² => (O.filter (fun L => p ∈ L)).card
  let v := fun p : ℝ² => (![p 0, p 1, 1] : Fin 3 → ℝ)
  let attached := fun (w : ℝ²) (L : AffineSubspace ℝ ℝ²) =>
    ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
      ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
        ∀ z ∈ s, ∃ a b c : ℝ,
          v z = a • v p + b • (ε • v q) + c • (δ • v w) ∧
          ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))
  let A := fun p => (O.filter (attached p)).card
  ∀ p ∈ s, d p = 1 → 2 ≤ A p

theorem main : H1 → H2 → OMA.R_Erdos210_erdos_210_variants_csima_sawyer_R1.H1 := by
  classical
  intro zero one s hs hcol
  let O := ordinaryLines s
  let d := fun p : ℝ² => (O.filter (fun L => p ∈ L)).card
  let v := fun p : ℝ² => (![p 0, p 1, 1] : Fin 3 → ℝ)
  let attached := fun (w : ℝ²) (L : AffineSubspace ℝ ℝ²) =>
    ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
      ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
        ∀ z ∈ s, ∃ a b c : ℝ,
          v z = a • v p + b • (ε • v q) + c • (δ • v w) ∧
          ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))
  let A := fun p => (O.filter (attached p)).card
  change s.card ≤ 2 * O.card ∨
    ∀ p ∈ s, 3 ≤ d p + A p ∨ (d p = 2 ∧ A p = 0)
  by_cases hcover : ∃ L M : AffineSubspace ℝ ℝ², Module.finrank ℝ L.direction = 1 ∧
      Module.finrank ℝ M.direction = 1 ∧ ∀ p ∈ s, p ∈ L ∨ p ∈ M
  · obtain ⟨L, M, hL, hM, hcov⟩ := hcover
    exact Or.inl (OMA.TwoPencils.count s (by omega) hcol L M hL hM hcov)
  · right
    intro p hp
    by_cases hd₀ : d p = 0
    · have hA : 3 ≤ A p := zero s hs hcol hcover p hp hd₀
      omega
    by_cases hd₁ : d p = 1
    · have hA : 2 ≤ A p := one s hs hcol hcover p hp hd₁
      omega
    omega

end OMA.R_Erdos210_erdos_210_variants_csima_sawyer_R1_H1_R1
