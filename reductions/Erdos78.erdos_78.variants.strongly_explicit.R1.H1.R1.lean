import OMAReductions.R_Erdos78_erdos_78_variants_strongly_explicit_R1
-- Reduction Erdos78.erdos_78.variants.strongly_explicit.R1.H1.R1
-- Credit: @adammcarter
-- Splits the open core (a fast oracle for Ramsey graphs on 2^k vertices) into a purely
-- mathematical statement about one concrete family of graphs and a purely computational one.
-- The family: Paley graphs over the fields F_13[x]/(x^m - 2), m a power of 3 (the polynomial
-- is irreducible for every such m; 13 = 1 mod 4 and m is odd, so there are no subfield cliques),
-- induced on the 0/1 polynomials read off from the binary digits of the vertex names.
-- H1 (OPEN, pure mathematics, no running time): these concrete graphs on 2^k vertices have no
--   clique and no independent set of size c * k.
-- H2 (engineering, no Ramsey theory, proved separately): the adjacency rule is polynomial time.
-- main: H1 and H2 give the open core (immediate, the two halves fit together exactly).
-- paley_tower_suffices: H1 would follow from a logarithmic bound on homogeneous sets in the
--   whole Paley graphs of this tower of fields (the graphs of H1 are induced subgraphs).
namespace OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R1
open Filter Real ComplexityTheory Erdos78 Polynomial

-- H1 (OPEN, pure mathematics): the concrete graphs are Ramsey graphs. Vertices u, v below 2^k
-- are joined when the difference of their 0/1 polynomials is a square in F_13[x]/(x^m - 2),
-- m the least power of 3 above k.
def H1 : Prop := ∃ c > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
  NoHomogeneousSet (stronglyExplicitGraph (fun p : ℕ × ℕ × ℕ =>
  @decide (IsSquare (AdjoinRoot.mk (X ^ 3 ^ Nat.clog 3 (Nat.size p.1) - C 2 : (ZMod 13)[X])
    ((∑ i ∈ Finset.range (3 ^ Nat.clog 3 (Nat.size p.1)), if p.2.1.testBit i then X ^ i else 0) -
     (∑ i ∈ Finset.range (3 ^ Nat.clog 3 (Nat.size p.1)), if p.2.2.testBit i then X ^ i else 0))))
    (Classical.propDecidable _)) (2 ^ k)) ⌈c * k⌉₊
-- H2 (true, engineering): deciding whether the difference of two 0/1 polynomials is a square
-- in F_13[x]/(x^m - 2), with m the least power of 3 that is at least the bit length of n,
-- is polynomial time in the bit lengths of the inputs.
def H2 : Prop := IsPolyTime (fun p : ℕ × ℕ × ℕ =>
  @decide (IsSquare (AdjoinRoot.mk (X ^ 3 ^ Nat.clog 3 (Nat.size p.1) - C 2 : (ZMod 13)[X])
    ((∑ i ∈ Finset.range (3 ^ Nat.clog 3 (Nat.size p.1)), if p.2.1.testBit i then X ^ i else 0) -
     (∑ i ∈ Finset.range (3 ^ Nat.clog 3 (Nat.size p.1)), if p.2.2.testBit i then X ^ i else 0))))
    (Classical.propDecidable _))

theorem main : H1 → H2 → OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1.H1 := by
  rintro ⟨c, hc, hev⟩ h2
  exact ⟨c, hc, _, h2, hev⟩

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

theorem bp_degree_lt (m u : ℕ) :
    (∑ i ∈ Finset.range m, if u.testBit i then (X : (ZMod 13)[X]) ^ i else 0).degree < m := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  rw [bp_coeff]
  simp [Nat.not_lt.2 hn]

theorem mk_inj (m : ℕ) (hm : 0 < m) (a b : (ZMod 13)[X]) (ha : a.degree < m) (hb : b.degree < m)
    (h : AdjoinRoot.mk (X ^ m - C 2 : (ZMod 13)[X]) a = AdjoinRoot.mk (X ^ m - C 2) b) :
    a = b := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hd : (X ^ m - C 2 : (ZMod 13)[X]) ∣ a - b := AdjoinRoot.mk_eq_mk.1 h
  have hdeg : (a - b).degree < (X ^ m - C 2 : (ZMod 13)[X]).degree := by
    rw [Polynomial.degree_X_pow_sub_C hm]
    exact (Polynomial.degree_sub_le a b).trans_lt (max_lt ha hb)
  exact sub_eq_zero.1 (Polynomial.eq_zero_of_dvd_of_degree_lt hd hdeg)

theorem bp_inj (k m u v : ℕ) (hkm : k ≤ m) (hu : u < 2 ^ k) (hv : v < 2 ^ k)
    (h : (∑ i ∈ Finset.range m, if u.testBit i then (X : (ZMod 13)[X]) ^ i else 0) =
      ∑ i ∈ Finset.range m, if v.testBit i then (X : (ZMod 13)[X]) ^ i else 0) : u = v := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < m
  · have hc := congrArg (fun q : (ZMod 13)[X] => q.coeff i) h
    simp only [bp_coeff, hi, true_and] at hc
    have h10 : (1 : ZMod 13) ≠ 0 := by decide
    by_cases h1 : u.testBit i = true <;> by_cases h2 : v.testBit i = true
    · rw [h1, h2]
    · simp [h1, h2, h10] at hc
    · simp [h1, h2, h10.symm] at hc
    · rw [Bool.not_eq_true] at h1 h2
      rw [h1, h2]
  · have hle : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hu hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hv hle)]

/-- The graph on 2^k vertices embeds in the Paley graph, as soon as the oracle answers the
quadratic residue question on 0/1 polynomials. -/
theorem paleyEmb (k j : ℕ) (hk : k ≤ 3 ^ j) (adj : ℕ × ℕ × ℕ → Bool)
    (hadj : ∀ u v : ℕ, adj (2 ^ k, u, v) = true ↔
      IsSquare
        (AdjoinRoot.mk (X ^ 3 ^ j - C 2 : (ZMod 13)[X])
            (∑ i ∈ Finset.range (3 ^ j), if u.testBit i then X ^ i else 0) -
          AdjoinRoot.mk (X ^ 3 ^ j - C 2 : (ZMod 13)[X])
            (∑ i ∈ Finset.range (3 ^ j), if v.testBit i then X ^ i else 0))) :
    Nonempty (SimpleGraph.Embedding (stronglyExplicitGraph adj (2 ^ k))
      (SimpleGraph.fromRel fun a b : AdjoinRoot (X ^ 3 ^ j - C 2 : (ZMod 13)[X]) =>
        IsSquare (a - b))) := by
  have hm : 0 < 3 ^ j := by positivity
  have hinj : Function.Injective (fun u : Fin (2 ^ k) =>
      AdjoinRoot.mk (X ^ 3 ^ j - C 2 : (ZMod 13)[X])
        (∑ i ∈ Finset.range (3 ^ j), if (u : ℕ).testBit i then X ^ i else 0)) := by
    intro u v huv
    have := mk_inj (3 ^ j) hm _ _ (bp_degree_lt (3 ^ j) u) (bp_degree_lt (3 ^ j) v) huv
    exact Fin.ext (bp_inj k (3 ^ j) u v hk u.2 v.2 this)
  refine ⟨{ toEmbedding := ⟨_, hinj⟩, map_rel_iff' := ?_ }⟩
  intro a b
  simp only [stronglyExplicitGraph, SimpleGraph.fromRel_adj, Function.Embedding.coeFn_mk,
    hadj, hinj.ne_iff]

theorem noHom_of_emb {V W : Type} (G : SimpleGraph V) (P : SimpleGraph W) (m : ℕ)
    (e : SimpleGraph.Embedding G P) (H : NoHomogeneousSet P m) : NoHomogeneousSet G m := by
  obtain ⟨h1, h2⟩ := H
  exact ⟨h1.comap ⟨e.toCopy⟩, h2.comap ⟨(SimpleGraph.Embedding.complEquiv e).toCopy⟩⟩

/-- A logarithmic bound on homogeneous sets in the whole Paley graphs over
F_13[x]/(x^(3^j) - 2) would give H1 (the graphs of H1 are induced subgraphs of these). -/
theorem paley_tower_suffices
    (hP : ∃ c > (0 : ℝ), ∀ᶠ j : ℕ in atTop,
      NoHomogeneousSet
        (SimpleGraph.fromRel fun a b : AdjoinRoot (X ^ 3 ^ j - C 2 : (ZMod 13)[X]) =>
          IsSquare (a - b))
        ⌈c * (3 : ℝ) ^ j⌉₊) : H1 := by
  obtain ⟨c, hc, hev⟩ := hP
  refine ⟨6 * c, by positivity, ?_⟩
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hev
  refine eventually_atTop.2 ⟨max 1 (3 ^ J), fun k hk => ?_⟩
  have hk1 : 1 ≤ k := le_trans (le_max_left _ _) hk
  have hkJ : 3 ^ J ≤ k := le_trans (le_max_right _ _) hk
  have hsize : Nat.size (2 ^ k) = k + 1 := Nat.size_pow
  set j := Nat.clog 3 (Nat.size (2 ^ k)) with hj
  have hle : k + 1 ≤ 3 ^ j := by
    rw [hj, hsize]
    exact Nat.le_pow_clog (by norm_num) _
  have hJj : J ≤ j := by
    have : 3 ^ J < 3 ^ j := by omega
    exact ((Nat.pow_lt_pow_iff_right (by norm_num)).1 this).le
  have hjpos : 0 < j := by
    rw [hj, hsize]
    exact Nat.clog_pos (by norm_num) (by omega)
  have hlt : 3 ^ (j - 1) < k + 1 := by
    have := Nat.pow_pred_clog_lt_self (b := 3) (by norm_num) (x := k + 1) (by omega)
    rw [hj, hsize]
    exact this
  have hup : 3 ^ j ≤ 6 * k := by
    have : 3 ^ j = 3 * 3 ^ (j - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have hbig := hJ j hJj
  obtain ⟨e⟩ := paleyEmb k j (by omega)
    (fun p : ℕ × ℕ × ℕ =>
      @decide (IsSquare (AdjoinRoot.mk (X ^ 3 ^ Nat.clog 3 (Nat.size p.1) - C 2 : (ZMod 13)[X])
        ((∑ i ∈ Finset.range (3 ^ Nat.clog 3 (Nat.size p.1)),
            if p.2.1.testBit i then X ^ i else 0) -
         (∑ i ∈ Finset.range (3 ^ Nat.clog 3 (Nat.size p.1)),
            if p.2.2.testBit i then X ^ i else 0))))
        (Classical.propDecidable _))
    (fun u v => by
      simp only [decide_eq_true_eq, map_sub]
      rfl)
  have hno := noHom_of_emb _ _ _ e hbig
  have hm : ⌈c * (3 : ℝ) ^ j⌉₊ ≤ ⌈6 * c * (k : ℝ)⌉₊ := by
    apply Nat.ceil_mono
    have h3 : ((3 : ℝ) ^ j) ≤ 6 * (k : ℝ) := by exact_mod_cast hup
    nlinarith
  exact ⟨hno.1.mono hm, hno.2.mono hm⟩


end OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R1
