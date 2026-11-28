import OMAReductions.R_Erdos101_erdos_101_R2_H1_R1

-- Reduction Erdos101.erdos_101.R2.H1.R1.H1.R2 of step Erdos101.erdos_101.R2.H1.R1.H1

/-!
# Tripartite line extraction and scalar homogeneous weighting on four-point lines

A dense family of four-point lines in a five-free planar point set splits into
two separate ingredients:

1. A tripartite extraction step producing pairwise disjoint color classes
   `S1, S2, S3 ⊆ S` and a dense line-injective family `T` of collinear triples
   `(x, y, z) ∈ S1 × S2 × S3` lying on distinct four-point lines.
2. A purely scalar weighting step finding a dense subfamily `U ⊆ T` together
   with nonzero point weights `h : ℝ² → ℝˣ` and center ratios `s : ℝ² → ℝˣ`
   (`s x ≠ 1` on `S`) satisfying two scalar equations for the affine division
   parameter `t` of each collinear triple `z = (1 - t) • x + t • y`.

Inside `main`, we deduce two unconditional geometric consequences from scratch:
line-injectivity on distinct collinear triples forces `ExplicitDisjoint`, and
the two scalar ratio equations are equivalent to the homogeneous vector
relation in `ℝ × ℝ²`.
-/

namespace OMA.R_Erdos101_erdos_101_R2_H1_R1_H1_R2

open EuclideanGeometry SimpleGraph.TripartiteFromTriangles
open scoped Classical

/-- Extract pairwise disjoint subsets `S1, S2, S3 ⊆ S` and a dense
line-injective family of collinear triples `(x, y, z) ∈ S1 × S2 × S3`
spanning distinct four-point lines. -/
def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ S : Finset ℝ²,
    N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
    δ * (S.card : ℝ) ^ 2 ≤ (linesWithPointsFor 4 (S : Set ℝ²)).ncard →
    ∃ S1 S2 S3 : Finset ℝ²,
      S1 ⊆ S ∧ S2 ⊆ S ∧ S3 ⊆ S ∧
      Disjoint S1 S2 ∧ Disjoint S1 S3 ∧ Disjoint S2 S3 ∧
      ∃ T : Finset (S × S × S), ρ * (S.card : ℝ) ^ 2 ≤ T.card ∧
        (T : Set (S × S × S)).InjOn (fun e => line[ℝ, (e.1 : ℝ²), (e.2.1 : ℝ²)]) ∧
        ∀ e ∈ T, (e.1 : ℝ²) ∈ S1 ∧ (e.2.1 : ℝ²) ∈ S2 ∧ (e.2.2 : ℝ²) ∈ S3 ∧
          line[ℝ, (e.1 : ℝ²), (e.2.1 : ℝ²)] ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧
          (e.2.2 : ℝ²) ∈ line[ℝ, (e.1 : ℝ²), (e.2.1 : ℝ²)]

/-- A dense tripartite line-injective family of collinear triples on four-point
lines admits a dense subfamily with nonzero point weights and center-dependent
ratios satisfying the two scalar projective-division equations. -/
def H2 : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, ∀ S : Finset ℝ²,
    N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
    ∀ S1 S2 S3 : Finset ℝ²,
      S1 ⊆ S ∧ S2 ⊆ S ∧ S3 ⊆ S ∧
      Disjoint S1 S2 ∧ Disjoint S1 S3 ∧ Disjoint S2 S3 →
    ∀ T : Finset (S × S × S), ρ * (S.card : ℝ) ^ 2 ≤ T.card →
      (T : Set (S × S × S)).InjOn (fun e => line[ℝ, (e.1 : ℝ²), (e.2.1 : ℝ²)]) →
      (∀ e ∈ T, (e.1 : ℝ²) ∈ S1 ∧ (e.2.1 : ℝ²) ∈ S2 ∧ (e.2.2 : ℝ²) ∈ S3 ∧
        line[ℝ, (e.1 : ℝ²), (e.2.1 : ℝ²)] ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧
        (e.2.2 : ℝ²) ∈ line[ℝ, (e.1 : ℝ²), (e.2.1 : ℝ²)]) →
    ∃ U ⊆ T, η * (S.card : ℝ) ^ 2 ≤ U.card ∧
      ∃ h s : ℝ² → ℝˣ, (∀ x ∈ S, s x ≠ 1) ∧
        ∀ e ∈ U, ∀ t : ℝ,
          (e.2.2 : ℝ²) = (1 - t) • (e.1 : ℝ²) + t • (e.2.1 : ℝ²) →
          (h e.2.2 : ℝ) = (1 - (s e.1 : ℝ)) * (h e.1 : ℝ) + (s e.1 : ℝ) * (h e.2.1 : ℝ) ∧
          t * (h e.2.2 : ℝ) = (s e.1 : ℝ) * (h e.2.1 : ℝ)

lemma line_eq_of_mem_of_ne {x y p q : ℝ²} (hxy : x ≠ y) (hpq : p ≠ q)
    (hp : p ∈ line[ℝ, x, y]) (hq : q ∈ line[ℝ, x, y]) :
    line[ℝ, p, q] = line[ℝ, x, y] := by
  apply (AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair ℝ p q) hp).mpr
  apply Submodule.eq_of_le_of_finrank_eq
  · exact AffineSubspace.direction_le (affineSpan_pair_le_of_mem_of_mem hp hq)
  · rw [direction_affineSpan, vectorSpan_pair, direction_affineSpan, vectorSpan_pair,
      finrank_span_singleton (vsub_ne_zero.mpr hpq),
      finrank_span_singleton (vsub_ne_zero.mpr hxy)]

lemma explicitDisjoint_of_injOn_line {S : Finset ℝ²} {U : Finset (S × S × S)}
    (hinj : (U : Set (S × S × S)).InjOn (fun e => line[ℝ, (e.1 : ℝ²), (e.2.1 : ℝ²)]))
    (hdist : ∀ e ∈ U, e.1 ≠ e.2.1 ∧ e.1 ≠ e.2.2 ∧ e.2.1 ≠ e.2.2 ∧
      (e.2.2 : ℝ²) ∈ line[ℝ, (e.1 : ℝ²), (e.2.1 : ℝ²)]) :
    ExplicitDisjoint U := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c a' h1 h2
    obtain ⟨hab, _, hbc, hc1⟩ := hdist (a, b, c) h1
    obtain ⟨ha'b, _, _, hc2⟩ := hdist (a', b, c) h2
    have hL1 : line[ℝ, (b : ℝ²), (c : ℝ²)] = line[ℝ, (a : ℝ²), (b : ℝ²)] :=
      line_eq_of_mem_of_ne (Subtype.coe_ne_coe.mpr hab) (Subtype.coe_ne_coe.mpr hbc)
        (right_mem_affineSpan_pair ℝ (a : ℝ²) (b : ℝ²)) hc1
    have hL2 : line[ℝ, (b : ℝ²), (c : ℝ²)] = line[ℝ, (a' : ℝ²), (b : ℝ²)] :=
      line_eq_of_mem_of_ne (Subtype.coe_ne_coe.mpr ha'b) (Subtype.coe_ne_coe.mpr hbc)
        (right_mem_affineSpan_pair ℝ (a' : ℝ²) (b : ℝ²)) hc2
    have heq : (a, b, c) = (a', b, c) := hinj h1 h2 (hL1.symm.trans hL2)
    exact congrArg Prod.fst heq
  · intro a b c b' h1 h2
    obtain ⟨hab, hac, _, hc1⟩ := hdist (a, b, c) h1
    obtain ⟨hab', _, _, hc2⟩ := hdist (a, b', c) h2
    have hL1 : line[ℝ, (a : ℝ²), (c : ℝ²)] = line[ℝ, (a : ℝ²), (b : ℝ²)] :=
      line_eq_of_mem_of_ne (Subtype.coe_ne_coe.mpr hab) (Subtype.coe_ne_coe.mpr hac)
        (left_mem_affineSpan_pair ℝ (a : ℝ²) (b : ℝ²)) hc1
    have hL2 : line[ℝ, (a : ℝ²), (c : ℝ²)] = line[ℝ, (a : ℝ²), (b' : ℝ²)] :=
      line_eq_of_mem_of_ne (Subtype.coe_ne_coe.mpr hab') (Subtype.coe_ne_coe.mpr hac)
        (left_mem_affineSpan_pair ℝ (a : ℝ²) (b' : ℝ²)) hc2
    have heq : (a, b, c) = (a, b', c) := hinj h1 h2 (hL1.symm.trans hL2)
    exact congrArg (fun p => p.2.1) heq
  · intro a b c c' h1 h2
    have heq : (a, b, c) = (a, b, c') := hinj h1 h2 rfl
    exact congrArg (fun p => p.2.2) heq

lemma exists_unique_affine_ratio {x y z : ℝ²}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hz : z ∈ line[ℝ, x, y]) :
    ∃! t : ℝ, z = (1 - t) • x + t • y ∧ t ≠ 0 ∧ t ≠ 1 := by
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hz
  have hzt : z = (1 - t) • x + t • y := by
    rw [← ht, AffineMap.lineMap_apply_module]
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hxz
    simpa using hzt.symm
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hyz
    simpa using hzt.symm
  refine ⟨t, ⟨hzt, ht0, ht1⟩, ?_⟩
  rintro t' ⟨hzt', -, -⟩
  have hsub : (t' - t) • (y - x) = 0 := by
    have hdiff : ((1 - t') • x + t' • y) - ((1 - t) • x + t • y) = 0 := by
      rw [← hzt', ← hzt, sub_self]
    rw [← hdiff]
    module
  rcases smul_eq_zero.mp hsub with h | h
  · exact sub_eq_zero.mp h
  · exact (sub_ne_zero.mpr hxy.symm h).elim

lemma homogeneous_eq_iff_scalar_ratio_eq {x y z : ℝ²} {t : ℝ}
    (hxy : x ≠ y) (hz : z = (1 - t) • x + t • y) (h s : ℝ² → ℝˣ) :
    (((h z : ℝ), (h z : ℝ) • z) : ℝ × ℝ²) =
      (1 - (s x : ℝ)) • ((h x : ℝ), (h x : ℝ) • x) +
        (s x : ℝ) • ((h y : ℝ), (h y : ℝ) • y) ↔
      (h z : ℝ) = (1 - (s x : ℝ)) * (h x : ℝ) + (s x : ℝ) * (h y : ℝ) ∧
        t * (h z : ℝ) = (s x : ℝ) * (h y : ℝ) := by
  constructor
  · intro heq
    have h1 : (h z : ℝ) = (1 - (s x : ℝ)) * (h x : ℝ) + (s x : ℝ) * (h y : ℝ) := by
      simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using congrArg Prod.fst heq
    have hvec : (h z : ℝ) • z =
        (1 - (s x : ℝ)) • ((h x : ℝ) • x) + (s x : ℝ) • ((h y : ℝ) • y) := by
      simpa [Prod.smul_mk, Prod.mk_add_mk] using congrArg Prod.snd heq
    have hcoef : (1 - t) * (h z : ℝ) - (1 - (s x : ℝ)) * (h x : ℝ) =
        -(t * (h z : ℝ) - (s x : ℝ) * (h y : ℝ)) := by
      linarith
    have hsmul : (t * (h z : ℝ) - (s x : ℝ) * (h y : ℝ)) • (y - x) = 0 := by
      have hzero : (h z : ℝ) • ((1 - t) • x + t • y) -
          ((1 - (s x : ℝ)) • ((h x : ℝ) • x) + (s x : ℝ) • ((h y : ℝ) • y)) = 0 := by
        rw [← hz, hvec, sub_self]
      have hcomb : (h z : ℝ) • ((1 - t) • x + t • y) -
          ((1 - (s x : ℝ)) • ((h x : ℝ) • x) + (s x : ℝ) • ((h y : ℝ) • y)) =
          ((1 - t) * (h z : ℝ) - (1 - (s x : ℝ)) * (h x : ℝ)) • x +
            (t * (h z : ℝ) - (s x : ℝ) * (h y : ℝ)) • y := by
        module
      rw [hcomb, hcoef] at hzero
      have hfac : (-(t * (h z : ℝ) - (s x : ℝ) * (h y : ℝ))) • x +
          (t * (h z : ℝ) - (s x : ℝ) * (h y : ℝ)) • y =
          (t * (h z : ℝ) - (s x : ℝ) * (h y : ℝ)) • (y - x) := by
        module
      exact hfac.symm.trans hzero
    rcases smul_eq_zero.mp hsmul with h2 | hne
    · exact ⟨h1, sub_eq_zero.mp h2⟩
    · exact (sub_ne_zero.mpr hxy.symm hne).elim
  · rintro ⟨h1, h2⟩
    have h3 : (1 - t) * (h z : ℝ) = (1 - (s x : ℝ)) * (h x : ℝ) := by
      linarith
    apply Prod.ext
    · simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using h1
    · change (h z : ℝ) • z =
        (1 - (s x : ℝ)) • ((h x : ℝ) • x) + (s x : ℝ) • ((h y : ℝ) • y)
      have hsm : (h z : ℝ) • z = (h z : ℝ) • ((1 - t) • x + t • y) :=
        congrArg ((h z : ℝ) • ·) hz
      rw [hsm, smul_add, smul_smul, smul_smul, mul_comm (h z : ℝ) (1 - t),
        mul_comm (h z : ℝ) t, h3, h2, smul_smul, smul_smul]

lemma pairwise_ne_of_tripartite {S S1 S2 S3 : Finset ℝ²}
    (h12 : Disjoint S1 S2) (h13 : Disjoint S1 S3) (h23 : Disjoint S2 S3)
    {e : S × S × S} (he1 : (e.1 : ℝ²) ∈ S1) (he2 : (e.2.1 : ℝ²) ∈ S2)
    (he3 : (e.2.2 : ℝ²) ∈ S3) :
    e.1 ≠ e.2.1 ∧ e.1 ≠ e.2.2 ∧ e.2.1 ≠ e.2.2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact Finset.disjoint_left.mp h12 he1 (h ▸ he2)
  · intro h
    exact Finset.disjoint_left.mp h13 he1 (h ▸ he3)
  · intro h
    exact Finset.disjoint_left.mp h23 he2 (h ▸ he3)

theorem main : H1 → H2 → OMA.R_Erdos101_erdos_101_R2_H1_R1.H1 := by
  intro extract weight δ hδ
  obtain ⟨ρ, hρ, N, hN⟩ := extract δ hδ
  obtain ⟨η, hη, M, hM⟩ := weight ρ hρ
  refine ⟨η, hη, max N M, ?_⟩
  intro S hn hcap hdense
  obtain ⟨S1, S2, S3, hS1, hS2, hS3, h12, h13, h23, T, hTcard, hTinj, hTmem⟩ :=
    hN S ((le_max_left ..).trans hn) hcap hdense
  obtain ⟨U, hUsub, hUcard, h, s, hs, hscalar⟩ :=
    hM S ((le_max_right ..).trans hn) hcap S1 S2 S3
      ⟨hS1, hS2, hS3, h12, h13, h23⟩ T hTcard hTinj hTmem
  have hUdist : ∀ e ∈ U, e.1 ≠ e.2.1 ∧ e.1 ≠ e.2.2 ∧ e.2.1 ≠ e.2.2 ∧
      (e.2.2 : ℝ²) ∈ line[ℝ, (e.1 : ℝ²), (e.2.1 : ℝ²)] := by
    intro e he
    obtain ⟨he1, he2, he3, _, hcol⟩ := hTmem e (hUsub he)
    obtain ⟨hne1, hne2, hne3⟩ := pairwise_ne_of_tripartite h12 h13 h23 he1 he2 he3
    exact ⟨hne1, hne2, hne3, hcol⟩
  have hUdisj : ExplicitDisjoint U :=
    explicitDisjoint_of_injOn_line (hTinj.mono (Finset.coe_subset.mpr hUsub)) hUdist
  refine ⟨U, hUdisj, hUcard, hTinj.mono (Finset.coe_subset.mpr hUsub), ?_, h, s, hs, ?_⟩
  · intro e he
    obtain ⟨hne1, hne2, hne3, _⟩ := hUdist e he
    exact ⟨hne1, hne2, hne3, (hTmem e (hUsub he)).2.2.2.1⟩
  · dsimp only
    intro e he
    obtain ⟨hne1, hne2, hne3, hcol⟩ := hUdist e he
    obtain ⟨t, ⟨ht, -, -⟩, -⟩ := exists_unique_affine_ratio
      (Subtype.coe_ne_coe.mpr hne1) (Subtype.coe_ne_coe.mpr hne2)
      (Subtype.coe_ne_coe.mpr hne3) hcol
    exact (homogeneous_eq_iff_scalar_ratio_eq (Subtype.coe_ne_coe.mpr hne1) ht h s).mpr
      (hscalar e he t ht)

end OMA.R_Erdos101_erdos_101_R2_H1_R1_H1_R2
