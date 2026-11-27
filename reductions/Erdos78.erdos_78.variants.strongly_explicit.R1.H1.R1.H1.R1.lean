import OMAReductions.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R1
-- Reduction Erdos78.erdos_78.variants.strongly_explicit.R1.H1.R1.H1.R1
-- Credit: @adammcarter
-- Narrows the open Paley piece (no clique and no independent set of size c * k among the 0/1
-- polynomials of degree below k, for every large k) to one half of it on a thin set of sizes.
-- H1 (OPEN, pure mathematics): cliques only, and only for the full cubes: among all 0/1
--   polynomials of degree below 3^j in F_13[x]/(x^(3^j) - 2), any set whose pairwise differences
--   are all squares has fewer than c * 3^j elements. No independent sets, no intermediate sizes.
-- H2 (true, short field theory, proved separately): in F_13[x]/(x^(3^j) - 2), x times a
--   non-square is a square (x itself is a non-square and the ring is a finite field).
-- main: multiplying every vertex by x (a shift of the binary digits of its name) turns an
--   independent set into a clique one degree higher, and every size k sits inside the full cube
--   of its own field. So H1 and H2 give the whole Paley piece, with the constant 3 * c.
-- No risk is added: the Paley piece one level up contains the full cube of this level (replace
--   x by x^3), so H1 follows from it with the constant 3 * c.
namespace OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R1_H1_R1
open Filter Real ComplexityTheory Erdos78 Polynomial

-- H1 (OPEN, pure mathematics): no large clique among the 0/1 polynomials of degree below 3^j.
def H1 : Prop := ∃ c > (0 : ℝ), ∀ᶠ j : ℕ in atTop, ∀ S : Finset ℕ,
  (∀ u ∈ S, u < 2 ^ 3 ^ j) →
  (∀ u ∈ S, ∀ v ∈ S, u ≠ v →
    IsSquare (AdjoinRoot.mk (X ^ 3 ^ j - C 2 : (ZMod 13)[X])
      ((∑ i ∈ Finset.range (3 ^ j), if u.testBit i then X ^ i else 0) -
       (∑ i ∈ Finset.range (3 ^ j), if v.testBit i then X ^ i else 0)))) →
  (S.card : ℝ) < c * 3 ^ j
-- H2 (true, field theory): x times a non-square is a square in F_13[x]/(x^(3^j) - 2).
def H2 : Prop := ∀ j : ℕ, ∀ y : AdjoinRoot (X ^ 3 ^ j - C 2 : (ZMod 13)[X]),
  ¬ IsSquare y → IsSquare (AdjoinRoot.root (X ^ 3 ^ j - C 2 : (ZMod 13)[X]) * y)

theorem bp_coeff (m u n : ℕ) :
    (∑ i ∈ Finset.range m, if u.testBit i then (X : (ZMod 13)[X]) ^ i else 0).coeff n =
      if n < m ∧ u.testBit n = true then 1 else 0 := by
  rw [Polynomial.finsetSum_coeff]
  have : ∀ i ∈ Finset.range m,
      (if u.testBit i then (X : (ZMod 13)[X]) ^ i else 0).coeff n =
        if i = n then (if u.testBit n = true then (1 : ZMod 13) else 0) else 0 := by
    intro i _
    by_cases h : i = n
    · subst h
      by_cases hb : u.testBit i = true <;> simp [hb]
    · by_cases hb : u.testBit i = true <;> simp [hb, Polynomial.coeff_X_pow, Ne.symm h, h]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (Finset.range m) n]
  by_cases hn : n < m <;> by_cases hb : u.testBit n = true <;> simp [hn, hb]

/-- Doubling a vertex name multiplies its 0/1 polynomial by x, when the top digit is free. -/
theorem bp_double (m u : ℕ) (hu : u < 2 ^ (m - 1)) :
    (∑ i ∈ Finset.range m, if (2 * u).testBit i then (X : (ZMod 13)[X]) ^ i else 0) =
      X * ∑ i ∈ Finset.range m, if u.testBit i then (X : (ZMod 13)[X]) ^ i else 0 := by
  ext n
  rw [bp_coeff]
  cases n with
  | zero =>
    rw [coeff_X_mul_zero]
    have h0 : (2 * u).testBit 0 = false := by
      rw [Nat.testBit_zero]
      simp
    simp [h0]
  | succ n =>
    rw [coeff_X_mul, bp_coeff, Nat.testBit_succ, Nat.mul_div_cancel_left u (by norm_num : 0 < 2)]
    by_cases hn : n + 1 < m
    · have hn' : n < m := by omega
      simp [hn, hn']
    · by_cases hn' : n < m
      · have hnm : n = m - 1 := by omega
        have hb : u.testBit n = false := by
          rw [hnm]
          exact Nat.testBit_lt_two_pow hu
        simp [hn, hb]
      · simp [hn, hn']

theorem isSquare_neg_of (f : (ZMod 13)[X]) (y : AdjoinRoot f) (h : IsSquare y) : IsSquare (-y) := by
  obtain ⟨r, rfl⟩ := h
  refine ⟨AdjoinRoot.mk f (C 5) * r, ?_⟩
  have h5 : (AdjoinRoot.mk f (C 5)) * (AdjoinRoot.mk f (C 5)) = -1 := by
    rw [← map_mul, ← C_mul]
    have : (5 : ZMod 13) * 5 = -1 := by decide
    rw [this]
    simp
  calc -(r * r) = (-1) * (r * r) := by ring
    _ = (AdjoinRoot.mk f (C 5) * AdjoinRoot.mk f (C 5)) * (r * r) := by rw [h5]
    _ = AdjoinRoot.mk f (C 5) * r * (AdjoinRoot.mk f (C 5) * r) := by ring

theorem sq_symm (j u v : ℕ)
    (h : IsSquare (AdjoinRoot.mk (X ^ 3 ^ j - C 2 : (ZMod 13)[X])
      ((∑ i ∈ Finset.range (3 ^ j), if u.testBit i then X ^ i else 0) -
       (∑ i ∈ Finset.range (3 ^ j), if v.testBit i then X ^ i else 0)))) :
    IsSquare (AdjoinRoot.mk (X ^ 3 ^ j - C 2 : (ZMod 13)[X])
      ((∑ i ∈ Finset.range (3 ^ j), if v.testBit i then X ^ i else 0) -
       (∑ i ∈ Finset.range (3 ^ j), if u.testBit i then X ^ i else 0))) := by
  have := isSquare_neg_of _ _ h
  rw [← map_neg, neg_sub] at this
  exact this

theorem adj_iff (N j : ℕ) (hj : Nat.clog 3 (Nat.size N) = j) (u v : Fin N) (huv : u ≠ v) :
    (stronglyExplicitGraph (fun p : ℕ × ℕ × ℕ =>
      @decide (IsSquare (AdjoinRoot.mk (X ^ 3 ^ Nat.clog 3 (Nat.size p.1) - C 2 : (ZMod 13)[X])
        ((∑ i ∈ Finset.range (3 ^ Nat.clog 3 (Nat.size p.1)), if p.2.1.testBit i then X ^ i else 0) -
         (∑ i ∈ Finset.range (3 ^ Nat.clog 3 (Nat.size p.1)), if p.2.2.testBit i then X ^ i else 0))))
        (Classical.propDecidable _)) N).Adj u v ↔
    IsSquare (AdjoinRoot.mk (X ^ 3 ^ j - C 2 : (ZMod 13)[X])
      ((∑ i ∈ Finset.range (3 ^ j), if (u : ℕ).testBit i then X ^ i else 0) -
       (∑ i ∈ Finset.range (3 ^ j), if (v : ℕ).testBit i then X ^ i else 0))) := by
  subst hj
  simp only [stronglyExplicitGraph, SimpleGraph.fromRel_adj, decide_eq_true_eq]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact sq_symm _ _ _ h
  · intro h
    exact ⟨huv, Or.inl h⟩

theorem main : H1 → H2 → OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R1.H1 := by
  rintro ⟨c, hc, hev⟩ h2
  refine ⟨3 * c, by positivity, ?_⟩
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hev
  refine eventually_atTop.2 ⟨max 1 (3 ^ J), fun k hk => ?_⟩
  have hk1 : 1 ≤ k := le_trans (le_max_left _ _) hk
  have hkJ : 3 ^ J ≤ k := le_trans (le_max_right _ _) hk
  have hsize : Nat.size (2 ^ k) = k + 1 := Nat.size_pow
  obtain ⟨j, hj⟩ : ∃ j, Nat.clog 3 (Nat.size (2 ^ k)) = j := ⟨_, rfl⟩
  have hle : k + 1 ≤ 3 ^ j := by
    rw [← hj, hsize]
    exact Nat.le_pow_clog (by norm_num) _
  have hJj : J ≤ j := by
    have : 3 ^ J < 3 ^ j := by omega
    exact ((Nat.pow_lt_pow_iff_right (by norm_num)).1 this).le
  have hjpos : 0 < j := by
    rw [← hj, hsize]
    exact Nat.clog_pos (by norm_num) (by omega)
  have hlt : 3 ^ (j - 1) < k + 1 := by
    have := Nat.pow_pred_clog_lt_self (b := 3) (by norm_num) (x := k + 1) (by omega)
    rw [← hj, hsize]
    exact this
  have hup : 3 ^ j ≤ 3 * k := by
    have : 3 ^ j = 3 * 3 ^ (j - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have hbig := hJ j hJj
  have hpow : 2 ^ k ≤ 2 ^ (3 ^ j - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow' : 2 * 2 ^ (3 ^ j - 1) = 2 ^ 3 ^ j := by
    rw [← pow_succ']
    congr 1
    omega
  have hbound : ∀ S : Finset ℕ, (∀ u ∈ S, u < 2 ^ 3 ^ j) →
      (∀ u ∈ S, ∀ v ∈ S, u ≠ v →
        IsSquare (AdjoinRoot.mk (X ^ 3 ^ j - C 2 : (ZMod 13)[X])
      ((∑ i ∈ Finset.range (3 ^ j), if u.testBit i then X ^ i else 0) -
       (∑ i ∈ Finset.range (3 ^ j), if v.testBit i then X ^ i else 0)))) →
      S.card < ⌈3 * c * (k : ℝ)⌉₊ := by
    intro S h1 h2'
    have hS := hbig S h1 h2'
    have h3 : ((3 : ℝ) ^ j) ≤ 3 * (k : ℝ) := by exact_mod_cast hup
    have hS' : (S.card : ℝ) < 3 * c * (k : ℝ) := by nlinarith
    exact_mod_cast hS'.trans_le (Nat.le_ceil _)
  constructor
  · intro T hT
    have hlt' := hbound (T.map Fin.valEmbedding)
      (by
        intro a ha
        obtain ⟨x, -, rfl⟩ := Finset.mem_map.1 ha
        exact lt_of_lt_of_le x.2 (hpow.trans (by omega)))
      (by
        intro a ha b hb hab
        obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 ha
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hb
        have hxy : x ≠ y := fun h => hab (by rw [h])
        exact (adj_iff (2 ^ k) j hj x y hxy).1 (hT.isClique hx hy hxy))
    rw [Finset.card_map, hT.card_eq] at hlt'
    exact lt_irrefl _ hlt'
  · intro T hT
    have hinj : Function.Injective (fun u : Fin (2 ^ k) => 2 * (u : ℕ)) := by
      intro x y hxy
      exact Fin.ext (by simpa using hxy)
    have hlt' := hbound (T.image (fun u : Fin (2 ^ k) => 2 * (u : ℕ)))
      (by
        intro a ha
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ha
        have := lt_of_lt_of_le x.2 hpow
        omega)
      (by
        intro a ha b hb hab
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
        have hxy : x ≠ y := fun h => hab (by rw [h])
        have hnadj := hT.isClique hx hy hxy
        rw [SimpleGraph.compl_adj] at hnadj
        have hns := fun h => hnadj.2 ((adj_iff (2 ^ k) j hj x y hxy).2 h)
        have hsq := h2 j _ hns
        rw [bp_double (3 ^ j) x (lt_of_lt_of_le x.2 hpow),
          bp_double (3 ^ j) y (lt_of_lt_of_le y.2 hpow), ← mul_sub, map_mul, AdjoinRoot.mk_X]
        exact hsq)
    rw [Finset.card_image_of_injective _ hinj, hT.card_eq] at hlt'
    exact lt_irrefl _ hlt'

end OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R1_H1_R1
