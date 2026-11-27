import OMAReductions.R_Green69_green_69_variants_elekes_szabo_R1

-- Reduction Green69.green_69.variants.elekes_szabo.R1.H1.R1 of step Green69.green_69.variants.elekes_szabo.R1.H1
-- Credit: @chris01-dev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the step.

/-!
The step is the Elekes–Szabó conjecture for point sets on an algebraic curve of degree at most
d, the curve being the zero set of any nonzero polynomial. Elekes and Szabó (arXiv:1302.5777)
prove it for irreducible curves and deduce the general case by the pigeonhole principle
(Remark 4.2). This file carries out that deduction, so that the two hypotheses left are their
two theorems, stated for irreducible polynomials.

Proved here, inside main: the polynomial F factors into at most d irreducible factors, each of
degree at most d, and every point of B is a zero of one of them. Every triple line then has a
type, the triple of factors vanishing at its three points; there are at most d^3 types, so one
type carries at least a 1 / (d + 1)^3 share of the triple lines.

H1 is the case where the three factors coincide: the points lie on one irreducible curve
(Theorem 2.2 of Elekes and Szabó).
H2 is the case where they do not all coincide: triple lines whose three points lie on three
irreducible curves (Theorem 4.1 of Elekes and Szabó, with n^2 in place of n^(2 - eta)).

The split loses nothing: the step implies both H1 and H2.
-/

namespace OMA.R_Green69_green_69_variants_elekes_szabo_R1_H1_R1

open scoped Finset
open Green69 MvPolynomial

/-- An irreducible polynomial over a field has positive total degree. -/
lemma one_le_totalDegree_of_irreducible {g : MvPolynomial (Fin 2) ℝ} (hg : Irreducible g) :
    1 ≤ g.totalDegree := by
  by_contra h
  have h0 : g.totalDegree = 0 := by omega
  rw [totalDegree_eq_zero_iff_eq_C] at h0
  have hc : g.coeff 0 ≠ 0 := by
    intro hc
    rw [hc, map_zero] at h0
    exact hg.ne_zero h0
  apply hg.not_isUnit
  rw [h0]
  exact (IsUnit.mk0 _ hc).map C

/-- The total degree of a product of nonzero polynomials is the sum of the total degrees. -/
lemma prod_totalDegree (s : Multiset (MvPolynomial (Fin 2) ℝ)) (hs : ∀ g ∈ s, g ≠ 0) :
    s.prod.totalDegree = (s.map totalDegree).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have ha : a ≠ 0 := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ g ∈ s, g ≠ 0 := fun g hg => hs g (Multiset.mem_cons_of_mem hg)
    have hp : s.prod ≠ 0 := Multiset.prod_ne_zero (fun h0 => hs' 0 h0 rfl)
    rw [Multiset.prod_cons, totalDegree_mul_of_isDomain ha hp, ih hs', Multiset.map_cons,
      Multiset.sum_cons]

/-- A nonzero polynomial of degree at most `d` has at most `d` irreducible factors, each of
degree at most `d`, and each of its zeros is a zero of one of them. -/
lemma exists_factor_set {F : MvPolynomial (Fin 2) ℝ} (hF : F ≠ 0) (d : ℕ)
    (hd : F.totalDegree ≤ d) :
    ∃ Φ : Finset (MvPolynomial (Fin 2) ℝ), #Φ ≤ d ∧
      (∀ g ∈ Φ, Irreducible g ∧ g.totalDegree ≤ d) ∧
      ∀ a : ℝ × ℝ, eval ![a.1, a.2] F = 0 → ∃ g ∈ Φ, eval ![a.1, a.2] g = 0 := by
  classical
  obtain ⟨f, hirr, hassoc⟩ := WfDvdMonoid.exists_factors F hF
  have hne : ∀ g ∈ f, g ≠ 0 := fun g hg => (hirr g hg).ne_zero
  obtain ⟨u, hu⟩ := hassoc
  have hp0 : f.prod ≠ 0 := Multiset.prod_ne_zero (fun h0 => hne 0 h0 rfl)
  have hdeg : (f.map totalDegree).sum ≤ d := by
    rw [← prod_totalDegree f hne]
    have : F.totalDegree = f.prod.totalDegree + (u : MvPolynomial (Fin 2) ℝ).totalDegree := by
      rw [← hu, totalDegree_mul_of_isDomain hp0 u.ne_zero]
    omega
  have hcard : Multiset.card f ≤ (f.map totalDegree).sum := by
    have := Multiset.card_nsmul_le_sum (s := f.map totalDegree) (a := 1) (by
      intro x hx
      obtain ⟨g, hg, rfl⟩ := Multiset.mem_map.1 hx
      exact one_le_totalDegree_of_irreducible (hirr g hg))
    simpa using this
  refine ⟨f.toFinset, (Multiset.toFinset_card_le f).trans (hcard.trans hdeg), ?_, ?_⟩
  · intro g hg
    rw [Multiset.mem_toFinset] at hg
    refine ⟨hirr g hg, le_trans ?_ hdeg⟩
    exact Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ (Multiset.mem_map_of_mem _ hg)
  · intro a ha
    rw [← hu, map_mul] at ha
    have hu' : eval ![a.1, a.2] (u : MvPolynomial (Fin 2) ℝ) ≠ 0 :=
      (u.isUnit.map (eval ![a.1, a.2])).ne_zero
    have hp : eval ![a.1, a.2] f.prod = 0 := by
      rcases mul_eq_zero.1 ha with h | h
      · exact h
      · exact absurd h hu'
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff] at hp
    obtain ⟨g, hg, hg0⟩ := Multiset.mem_map.1 hp
    exact ⟨g, Multiset.mem_toFinset.2 hg, hg0⟩

/-- Pigeonhole: one type of triple line carries a `1 / #Φ ^ 3` share of all triple lines. -/
lemma exists_class (B : Finset (ℝ × ℝ)) (Φ : Finset (MvPolynomial (Fin 2) ℝ))
    (hB : B.Nonempty) (hcover : ∀ a ∈ B, ∃ g ∈ Φ, eval ![a.1, a.2] g = 0) :
    ∃ g₁ ∈ Φ, ∃ g₂ ∈ Φ, ∃ g₃ ∈ Φ, (tripleLines B).ncard ≤ #Φ ^ 3 *
      ({L | ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, eval ![x.1, x.2] g₁ = 0 ∧ eval ![y.1, y.2] g₂ = 0 ∧
        eval ![z.1, z.2] g₃ = 0 ∧ x ≠ y ∧ z ≠ x ∧ z ≠ y ∧ z ∈ line[ℝ, x, y] ∧
        L = line[ℝ, x, y]} : Set (AffineSubspace ℝ (ℝ × ℝ))).ncard := by
  classical
  let R : MvPolynomial (Fin 2) ℝ × MvPolynomial (Fin 2) ℝ × MvPolynomial (Fin 2) ℝ →
      Set (AffineSubspace ℝ (ℝ × ℝ)) := fun w =>
    {L | ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, eval ![x.1, x.2] w.1 = 0 ∧ eval ![y.1, y.2] w.2.1 = 0 ∧
      eval ![z.1, z.2] w.2.2 = 0 ∧ x ≠ y ∧ z ≠ x ∧ z ≠ y ∧ z ∈ line[ℝ, x, y] ∧
      L = line[ℝ, x, y]}
  have hTfin := OMA.R_Green69_green_69_variants_elekes_szabo_R1.tripleLines_finite B
  have hRsub : ∀ w, R w ⊆ tripleLines B := by
    rintro w L ⟨x, hx, y, hy, z, hz, -, -, -, hxy, hzx, hzy, hzL, rfl⟩
    exact ⟨x, hx, y, hy, z, hz, hxy, hzx, hzy, hzL, rfl⟩
  have hRfin : ∀ w, (R w).Finite := fun w => hTfin.subset (hRsub w)
  obtain ⟨a0, ha0⟩ := hB
  obtain ⟨g0, hg0, -⟩ := hcover a0 ha0
  have hne : (Φ ×ˢ Φ ×ˢ Φ).Nonempty :=
    ⟨(g0, g0, g0), Finset.mem_product.2 ⟨hg0, Finset.mem_product.2 ⟨hg0, hg0⟩⟩⟩
  obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image (Φ ×ˢ Φ ×ˢ Φ) (fun w => (R w).ncard) hne
  have hcov : hTfin.toFinset ⊆ (Φ ×ˢ Φ ×ˢ Φ).biUnion (fun w => (hRfin w).toFinset) := by
    intro L hL
    rw [Set.Finite.mem_toFinset] at hL
    obtain ⟨x, hx, y, hy, z, hz, hxy, hzx, hzy, hzL, rfl⟩ := hL
    obtain ⟨g1, hg1, h1⟩ := hcover x hx
    obtain ⟨g2, hg2, h2⟩ := hcover y hy
    obtain ⟨g3, hg3, h3⟩ := hcover z hz
    rw [Finset.mem_biUnion]
    refine ⟨(g1, g2, g3), Finset.mem_product.2 ⟨hg1, Finset.mem_product.2 ⟨hg2, hg3⟩⟩, ?_⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨x, hx, y, hy, z, hz, h1, h2, h3, hxy, hzx, hzy, hzL, rfl⟩
  have h1 : (tripleLines B).ncard = #hTfin.toFinset := Set.ncard_eq_toFinset_card _ hTfin
  have h2 := Finset.card_le_card hcov
  have h3 := Finset.card_biUnion_le_card_mul (Φ ×ˢ Φ ×ˢ Φ) (fun w => (hRfin w).toFinset)
    (R w).ncard (fun w' hw' => by
      rw [← Set.ncard_eq_toFinset_card _ (hRfin w')]
      exact hmax w' hw')
  have h4 : #(Φ ×ˢ Φ ×ˢ Φ) = #Φ ^ 3 := by
    rw [Finset.card_product, Finset.card_product]
    ring
  obtain ⟨hw1, hw23⟩ := Finset.mem_product.1 hw
  obtain ⟨hw2, hw3⟩ := Finset.mem_product.1 hw23
  refine ⟨w.1, hw1, w.2.1, hw2, w.2.2, hw3, ?_⟩
  rw [h1, ← h4]
  exact h2.trans h3

-- Points on one irreducible curve of bounded degree.
def H1 : Prop :=
  ∀ d : ℕ, ∀ c : ℝ, 0 < c → ∃ n₀ : ℕ, ∀ B : Finset (ℝ × ℝ), n₀ < #B →
    AtMostOnLine 3 B →
    (∃ G : MvPolynomial (Fin 2) ℝ, Irreducible G ∧ G.totalDegree ≤ d ∧
      ∀ a ∈ B, MvPolynomial.eval ![a.1, a.2] G = 0) →
    c * (#B : ℝ) ^ 2 ≤ (tripleLines B).ncard → ∃ S ⊆ B, #S = 10 ∧ OnCubic S

-- Triple lines whose three points lie on three irreducible curves of bounded degree.
def H2 : Prop :=
  ∀ d : ℕ, ∀ c : ℝ, 0 < c → ∃ n₀ : ℕ, ∀ B : Finset (ℝ × ℝ), n₀ < #B →
    AtMostOnLine 3 B →
    ∀ G₁ G₂ G₃ : MvPolynomial (Fin 2) ℝ, Irreducible G₁ → Irreducible G₂ → Irreducible G₃ →
    G₁.totalDegree ≤ d → G₂.totalDegree ≤ d → G₃.totalDegree ≤ d →
    ¬ (G₁ = G₂ ∧ G₂ = G₃) →
    c * (#B : ℝ) ^ 2 ≤
      ({L | ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, MvPolynomial.eval ![x.1, x.2] G₁ = 0 ∧
        MvPolynomial.eval ![y.1, y.2] G₂ = 0 ∧ MvPolynomial.eval ![z.1, z.2] G₃ = 0 ∧
        x ≠ y ∧ z ≠ x ∧ z ≠ y ∧ z ∈ line[ℝ, x, y] ∧
        L = line[ℝ, x, y]} : Set (AffineSubspace ℝ (ℝ × ℝ))).ncard →
    ∃ S ⊆ B, #S = 10 ∧ OnCubic S

theorem main : H1 → H2 → OMA.R_Green69_green_69_variants_elekes_szabo_R1.H1 := by
  classical
  intro k1 k2 d c hc
  have hd1 : (0 : ℝ) < ((d : ℝ) + 1) ^ 3 := by positivity
  have hc1 : 0 < c / ((d : ℝ) + 1) ^ 3 := div_pos hc hd1
  obtain ⟨n₁, hk1⟩ := k1 d (c / ((d : ℝ) + 1) ^ 3) hc1
  obtain ⟨n₂, hk2⟩ := k2 d (c / ((d : ℝ) + 1) ^ 3) hc1
  obtain ⟨N, hN⟩ := exists_nat_ge ((((n₁ : ℝ) + 1) ^ 2) / (c / ((d : ℝ) + 1) ^ 3))
  refine ⟨max n₂ N, fun B hB hL hcurve hden => ?_⟩
  obtain ⟨F, hF0, hFd, hFv⟩ := hcurve
  have hBn2 : n₂ < #B := lt_of_le_of_lt (le_max_left _ _) hB
  have hBN : N < #B := lt_of_le_of_lt (le_max_right _ _) hB
  have hBpos : 0 < #B := by omega
  have hBposR : (1 : ℝ) ≤ (#B : ℝ) := by exact_mod_cast hBpos
  obtain ⟨Φ, hΦcard, hΦ, hΦv⟩ := exists_factor_set hF0 d hFd
  obtain ⟨g1, hg1, g2, hg2, g3, hg3, hcls⟩ :=
    exists_class B Φ (Finset.card_pos.1 hBpos) (fun a ha => hΦv a (hFv a ha))
  have hR : c / ((d : ℝ) + 1) ^ 3 * (#B : ℝ) ^ 2 ≤
      (({L | ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, eval ![x.1, x.2] g1 = 0 ∧ eval ![y.1, y.2] g2 = 0 ∧
        eval ![z.1, z.2] g3 = 0 ∧ x ≠ y ∧ z ≠ x ∧ z ≠ y ∧ z ∈ line[ℝ, x, y] ∧
        L = line[ℝ, x, y]} : Set (AffineSubspace ℝ (ℝ × ℝ))).ncard : ℝ) := by
    have hclsR : ((tripleLines B).ncard : ℝ) ≤ (#Φ : ℝ) ^ 3 *
        (({L | ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, eval ![x.1, x.2] g1 = 0 ∧ eval ![y.1, y.2] g2 = 0 ∧
        eval ![z.1, z.2] g3 = 0 ∧ x ≠ y ∧ z ≠ x ∧ z ≠ y ∧ z ∈ line[ℝ, x, y] ∧
        L = line[ℝ, x, y]} : Set (AffineSubspace ℝ (ℝ × ℝ))).ncard : ℝ) := by
      exact_mod_cast hcls
    have hΦR : (#Φ : ℝ) ^ 3 ≤ ((d : ℝ) + 1) ^ 3 := by
      have : (#Φ : ℝ) ≤ (d : ℝ) + 1 := by
        have : (#Φ : ℝ) ≤ (d : ℝ) := by exact_mod_cast hΦcard
        linarith
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 3
    have hr0 : (0 : ℝ) ≤
        (({L | ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, eval ![x.1, x.2] g1 = 0 ∧ eval ![y.1, y.2] g2 = 0 ∧
        eval ![z.1, z.2] g3 = 0 ∧ x ≠ y ∧ z ≠ x ∧ z ≠ y ∧ z ∈ line[ℝ, x, y] ∧
        L = line[ℝ, x, y]} : Set (AffineSubspace ℝ (ℝ × ℝ))).ncard : ℝ) := Nat.cast_nonneg _
    rw [div_mul_eq_mul_div, div_le_iff₀ hd1]
    nlinarith [mul_le_mul_of_nonneg_right hΦR hr0]
  by_cases heq : g1 = g2 ∧ g2 = g3
  · obtain ⟨h12, h23⟩ := heq
    rw [← h23, ← h12] at hR
    have hsub : {L | ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, eval ![x.1, x.2] g1 = 0 ∧
        eval ![y.1, y.2] g1 = 0 ∧ eval ![z.1, z.2] g1 = 0 ∧ x ≠ y ∧ z ≠ x ∧ z ≠ y ∧
        z ∈ line[ℝ, x, y] ∧ L = line[ℝ, x, y]} ⊆
        tripleLines (B.filter fun a => eval ![a.1, a.2] g1 = 0) := by
      rintro L ⟨x, hx, y, hy, z, hz, h1, h2, h3, hxy, hzx, hzy, hzL, rfl⟩
      exact ⟨x, Finset.mem_filter.2 ⟨hx, h1⟩, y, Finset.mem_filter.2 ⟨hy, h2⟩,
        z, Finset.mem_filter.2 ⟨hz, h3⟩, hxy, hzx, hzy, hzL, rfl⟩
    have hle := Set.ncard_le_ncard hsub
      (OMA.R_Green69_green_69_variants_elekes_szabo_R1.tripleLines_finite _)
    have hleR : (({L | ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, eval ![x.1, x.2] g1 = 0 ∧
        eval ![y.1, y.2] g1 = 0 ∧ eval ![z.1, z.2] g1 = 0 ∧ x ≠ y ∧ z ≠ x ∧ z ≠ y ∧
        z ∈ line[ℝ, x, y] ∧ L = line[ℝ, x, y]} : Set (AffineSubspace ℝ (ℝ × ℝ))).ncard : ℝ) ≤
        ((tripleLines (B.filter fun a => eval ![a.1, a.2] g1 = 0)).ncard : ℝ) := by
      exact_mod_cast hle
    have hB'B : (#(B.filter fun a => eval ![a.1, a.2] g1 = 0) : ℝ) ≤ (#B : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ B)
    have hB'0 : (0 : ℝ) ≤ (#(B.filter fun a => eval ![a.1, a.2] g1 = 0) : ℝ) :=
      Nat.cast_nonneg _
    have hden' : c / ((d : ℝ) + 1) ^ 3 *
        (#(B.filter fun a => eval ![a.1, a.2] g1 = 0) : ℝ) ^ 2 ≤
        ((tripleLines (B.filter fun a => eval ![a.1, a.2] g1 = 0)).ncard : ℝ) := by
      refine le_trans ?_ (hR.trans hleR)
      have : (#(B.filter fun a => eval ![a.1, a.2] g1 = 0) : ℝ) ^ 2 ≤ (#B : ℝ) ^ 2 := by
        nlinarith
      exact mul_le_mul_of_nonneg_left this hc1.le
    have hbig : n₁ < #(B.filter fun a => eval ![a.1, a.2] g1 = 0) := by
      have hup : ((tripleLines (B.filter fun a => eval ![a.1, a.2] g1 = 0)).ncard : ℝ) ≤
          (#(B.filter fun a => eval ![a.1, a.2] g1 = 0) : ℝ) *
          (#(B.filter fun a => eval ![a.1, a.2] g1 = 0) : ℝ) := by
        exact_mod_cast
          OMA.R_Green69_green_69_variants_elekes_szabo_R1.tripleLines_ncard_le _
      have hNR : (N : ℝ) < (#B : ℝ) := by exact_mod_cast hBN
      have h3 : ((n₁ : ℝ) + 1) ^ 2 < c / ((d : ℝ) + 1) ^ 3 * (#B : ℝ) := by
        have := lt_of_le_of_lt hN hNR
        rw [div_lt_iff₀ hc1] at this
        linarith
      have h4 : c / ((d : ℝ) + 1) ^ 3 * (#B : ℝ) ≤ c / ((d : ℝ) + 1) ^ 3 * (#B : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hc1.le
        nlinarith
      have h5 : ((n₁ : ℝ) + 1) ^ 2 < (#(B.filter fun a => eval ![a.1, a.2] g1 = 0) : ℝ) *
          (#(B.filter fun a => eval ![a.1, a.2] g1 = 0) : ℝ) := by
        linarith [hR.trans hleR]
      have h6 : (n₁ : ℝ) + 1 < (#(B.filter fun a => eval ![a.1, a.2] g1 = 0) : ℝ) := by
        by_contra hcon
        push Not at hcon
        have h0 : (0 : ℝ) ≤ (n₁ : ℝ) := Nat.cast_nonneg _
        nlinarith
      have h7 : ((n₁ + 1 : ℕ) : ℝ) < (#(B.filter fun a => eval ![a.1, a.2] g1 = 0) : ℝ) := by
        push_cast
        exact h6
      have := Nat.cast_lt.1 h7
      omega
    obtain ⟨S, hS, h⟩ := hk1 (B.filter fun a => eval ![a.1, a.2] g1 = 0) hbig
      (fun S hS => hL S (hS.trans (Finset.filter_subset _ B)))
      ⟨g1, (hΦ g1 hg1).1, (hΦ g1 hg1).2, fun a ha => (Finset.mem_filter.1 ha).2⟩ hden'
    exact ⟨S, hS.trans (Finset.filter_subset _ B), h⟩
  · exact hk2 B hBn2 hL g1 g2 g3 (hΦ g1 hg1).1 (hΦ g2 hg2).1 (hΦ g3 hg3).1
      (hΦ g1 hg1).2 (hΦ g2 hg2).2 (hΦ g3 hg3).2 heq hR

end OMA.R_Green69_green_69_variants_elekes_szabo_R1_H1_R1
