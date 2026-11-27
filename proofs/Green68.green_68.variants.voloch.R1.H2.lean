import OMAReductions.R_Green68_green_68_variants_voloch_R1
import Mathlib

/-! Conics are the zero sets of nonzero polynomials `∑ cᵢ mᵢ` in the six monomials of degree
at most two. Write `m a` for the vector of these monomials at `a`. Choose a linearly independent
subfamily of `{m a : a ∈ A}` with the same span; it has at most six vectors, so by hypothesis
the corresponding points lie on a conic with coefficient vector `c ≠ 0`. The functional
`v ↦ ∑ cᵢ vᵢ` kills the subfamily, hence the whole span, so every point of `A` lies on it. -/

open MvPolynomial

namespace G68H2

/-- The six exponents of total degree at most two. -/
noncomputable def e : Fin 6 → (Fin 2 →₀ ℕ) :=
  ![0, Finsupp.single 0 1, Finsupp.single 1 1, Finsupp.single 0 2,
    Finsupp.single 0 1 + Finsupp.single 1 1, Finsupp.single 1 2]

def tbl : Fin 6 → ℕ × ℕ := ![(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)]

lemma e_vals (i : Fin 6) : (e i 0, e i 1) = tbl i := by
  fin_cases i <;> simp [e, tbl]

lemma tbl_inj : Function.Injective tbl := by decide

lemma e_inj : Function.Injective e := by
  intro i j h
  apply tbl_inj
  rw [← e_vals, ← e_vals, h]

lemma e_deg (i : Fin 6) : e i 0 + e i 1 ≤ 2 := by
  have h := e_vals i
  have hT : ∀ j : Fin 6, (tbl j).1 + (tbl j).2 ≤ 2 := by decide
  have := hT i
  rw [← h] at this
  simpa using this

lemma mem_e_of_deg {d : Fin 2 →₀ ℕ} (hd : d 0 + d 1 ≤ 2) : ∃ i, e i = d := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 6, tbl i = (d 0, d 1) := by
    have h0 : d 0 ≤ 2 := by omega
    have h1 : d 1 ≤ 2 := by omega
    generalize d 0 = x at hd h0
    generalize d 1 = y at hd h1
    interval_cases x <;> interval_cases y <;> first | omega | decide
  refine ⟨i, ?_⟩
  have h := (e_vals i).trans hi
  ext k
  fin_cases k
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

variable {K : Type*} [Field K]

/-- The polynomial with coefficient vector `c`. -/
noncomputable def P (c : Fin 6 → K) : MvPolynomial (Fin 2) K := ∑ i, monomial (e i) (c i)

/-- The monomial vector of a point. -/
noncomputable def m (a : Fin 2 → K) : Fin 6 → K := fun i => (e i).prod fun k n => a k ^ n

lemma eval_P (c : Fin 6 → K) (a : Fin 2 → K) : eval a (P c) = ∑ i, c i * m a i := by
  simp only [P, map_sum, eval_monomial, m]

lemma coeff_P (c : Fin 6 → K) (j : Fin 6) : coeff (e j) (P c) = c j := by
  classical
  simp only [P, coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [if_neg]
    exact fun h => hij (e_inj h)
  · simp

lemma deg_P (c : Fin 6 → K) : (P c).totalDegree ≤ 2 := by
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro i _
  apply (totalDegree_monomial_le _ _).trans
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
  exact e_deg i

lemma F_eq_P (F : MvPolynomial (Fin 2) K) (hF : F.totalDegree ≤ 2) :
    F = P (fun i => coeff (e i) F) := by
  classical
  ext d
  by_cases hd : ∃ j, e j = d
  · obtain ⟨j, rfl⟩ := hd
    rw [coeff_P]
  · have hz : coeff d (P (fun i => coeff (e i) F)) = 0 := by
      simp only [P, coeff_sum, coeff_monomial]
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg]
      exact fun h => hd ⟨i, h⟩
    rw [hz]
    by_contra hne
    have hmem : d ∈ F.support := mem_support_iff.mpr hne
    have h := le_totalDegree hmem
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at h
    exact hd (mem_e_of_deg (by omega))

lemma m_one (a : Fin 2 → K) : m a 1 = a 0 := by
  simp [m, e]

lemma m_two (a : Fin 2 → K) : m a 2 = a 1 := by
  simp [m, e]

lemma m_inj : Function.Injective (m (K := K)) := by
  intro a b h
  funext k
  fin_cases k
  · have := congrFun h 1
    rwa [m_one, m_one] at this
  · have := congrFun h 2
    rwa [m_two, m_two] at this

end G68H2

open G68H2 in
theorem OMA.solution : OMA.R_Green68_green_68_variants_voloch_R1.H2 := by
  intro p _ A hA
  classical
  obtain ⟨c, hc0, hc⟩ : ∃ c : Fin 6 → ZMod p, c ≠ 0 ∧ ∀ a ∈ A, ∑ i, c i * m a i = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t, htsub, htspan, htli⟩ := exists_linearIndependent (ZMod p)
      ((A.image m : Finset (Fin 6 → ZMod p)) : Set (Fin 6 → ZMod p))
    have htfin : t.Finite := (Finset.finite_toSet _).subset htsub
    have : Fintype t := htfin.fintype
    have hTcard : Fintype.card t ≤ 6 := by
      have h := htli.fintype_card_le_finrank
      rwa [Module.finrank_fin_fun] at h
    set S := A.filter (fun a => m a ∈ t) with hSdef
    have hScard : S.card ≤ 6 := by
      have h : S.card ≤ t.toFinset.card := by
        apply Finset.card_le_card_of_injOn m
        · intro a ha
          exact Set.mem_toFinset.mpr (Finset.mem_filter.mp ha).2
        · intro a _ b _ h
          exact m_inj h
      rw [Set.toFinset_card] at h
      omega
    obtain ⟨F, hF0, hFdeg, hFS⟩ := hA S (Finset.filter_subset _ _) hScard
    set c := fun i => coeff (e i) F with hcdef
    have hFP := F_eq_P F hFdeg
    have hc0 : c ≠ 0 := by
      intro h
      apply hF0
      rw [hFP]
      have h' : (fun i => coeff (e i) F) = 0 := h
      rw [h']
      simp [P]
    let φ : (Fin 6 → ZMod p) →ₗ[ZMod p] ZMod p := ∑ i, c i • LinearMap.proj i
    have hφ : ∀ v, φ v = ∑ i, c i * v i := by
      intro v
      simp [φ]
    have hle : Submodule.span (ZMod p) t ≤ LinearMap.ker φ := by
      rw [Submodule.span_le]
      intro v hv
      have hv' := htsub hv
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hv'
      obtain ⟨a, haA, rfl⟩ := hv'
      have haS : a ∈ S := Finset.mem_filter.mpr ⟨haA, hv⟩
      have h1 := hFS a haS
      rw [hFP, eval_P] at h1
      show φ (m a) = 0
      rw [hφ]
      exact h1
    obtain ⟨a, haA, hne⟩ := hcon c hc0
    have hmem : m a ∈ Submodule.span (ZMod p) t := by
      rw [htspan]
      apply Submodule.subset_span
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨a, haA, rfl⟩
    have h2 := hle hmem
    rw [LinearMap.mem_ker, hφ] at h2
    exact hne h2
  refine ⟨P c, ?_, deg_P c, ?_⟩
  · intro h
    apply hc0
    funext j
    have h1 := coeff_P c j
    rw [h] at h1
    simpa using h1.symm
  · intro a ha
    rw [eval_P]
    exact hc a ha
