import OMAStatements.S_mo_115849

open OMA.S_mo_115849

namespace OMA.Levinson

def A : Finset (Fin 5) := {0, 1}
def B : Finset (Fin 5) := {2, 3}
def C : Finset (Fin 5) := {0, 2}
def D : Finset (Fin 5) := {1, 3}

def S : Finset (Finset (Fin 5)) := {A, B}
def SC : Finset (Finset (Fin 5)) := insert C S
def SD : Finset (Finset (Fin 5)) := insert D S
def SCD : Finset (Finset (Fin 5)) := insert C SD

noncomputable def small : levinsonSimplex 5 :=
  ⟨![1 / 100, 1 / 100, 1 / 100, 1 / 100, 71 / 100],
    by constructor
       · intro i
         fin_cases i <;> norm_num [Fin.ext_iff]
       · norm_num [Fin.sum_univ_succ]⟩

noncomputable def probeC : levinsonSimplex 5 :=
  ⟨![1 / 10, 1 / 100, 1 / 10, 1 / 100, 53 / 100],
    by constructor
       · intro i
         fin_cases i <;> norm_num [Fin.ext_iff]
       · norm_num [Fin.sum_univ_succ]⟩

noncomputable def probeD : levinsonSimplex 5 :=
  ⟨![1 / 100, 1 / 10, 1 / 100, 1 / 10, 53 / 100],
    by constructor
       · intro i
         fin_cases i <;> norm_num [Fin.ext_iff]
       · norm_num [Fin.sum_univ_succ]⟩

theorem feasible {T : Finset (Finset (Fin 5))} (hT : T ⊆ SCD) :
    levinsonIndicator T ∈ levinsonFeasible 5 := by
  refine ⟨T, ?_, ⟨small, ?_⟩, rfl⟩
  · have hcard : ∀ E ∈ SCD, E.card = 2 := by decide +kernel
    intro E hE F hF hsub
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard E (hT hE), hcard F (hT hF)])
  · have hall : ∀ E ∈ SCD, levinsonFacet E small := by
      norm_num [SCD, SD, S, A, B, C, D, levinsonFacet, small, Fin.sum_univ_succ,
        Finset.forall_mem_insert, Finset.sum_insert, Fin.ext_iff]
    classical
    have h : ∀ E ∈ T, levinsonFacet E small := fun E hE => hall E (hT hE)
    unfold levinsonIndicator
    rw [if_pos h]

theorem balance_facets {x : levinsonSimplex 5} (hA : levinsonFacet A x)
    (hB : levinsonFacet B x) : levinsonFacet C x ∨ levinsonFacet D x := by
  by_contra! hn
  simp [levinsonFacet, A, B, C, D, Finset.sum_insert, Fin.ext_iff] at hA hB hn
  linarith [hn.1, hn.2]

open Classical in
theorem indicator_insert (E : Finset (Fin 5)) (T : Finset (Finset (Fin 5)))
    (x : levinsonSimplex 5) :
    levinsonIndicator (insert E T) x =
      if levinsonFacet E x then levinsonIndicator T x else 0 := by
  unfold levinsonIndicator
  have h := Finset.forall_mem_insert E T (fun A => levinsonFacet A x)
  by_cases hE : levinsonFacet E x
  · rw [if_pos hE]
    by_cases hT : ∀ A ∈ T, levinsonFacet A x
    · rw [if_pos (h.2 ⟨hE, hT⟩), if_pos hT]
    · rw [if_neg (fun ht => hT (h.1 ht).2), if_neg hT]
  · rw [if_neg hE, if_neg (fun ht => hE (h.1 ht).1)]

/-- Inclusion-exclusion gives a relation because C or D holds wherever S holds. -/
theorem relation (x : levinsonSimplex 5) :
    levinsonIndicator S x - levinsonIndicator SC x - levinsonIndicator SD x +
      levinsonIndicator SCD x = 0 := by
  simp only [SC, SD, SCD, indicator_insert]
  by_cases hS : ∀ E ∈ S, levinsonFacet E x
  · have hAB : levinsonFacet A x ∧ levinsonFacet B x := by simpa [S] using hS
    rcases balance_facets hAB.1 hAB.2 with hC | hD
    · by_cases hD : levinsonFacet D x <;> simp [hC, hD]
    · by_cases hC : levinsonFacet C x <;> simp [hC, hD]
  · have hz : levinsonIndicator S x = 0 := by unfold levinsonIndicator; rw [if_neg hS]
    simp [hz]

noncomputable def family : Fin 4 → levinsonFeasible 5 :=
  ![⟨levinsonIndicator S, feasible (by decide +kernel)⟩,
    ⟨levinsonIndicator SC, feasible (by decide +kernel)⟩,
    ⟨levinsonIndicator SD, feasible (by decide +kernel)⟩,
    ⟨levinsonIndicator SCD, feasible (by decide +kernel)⟩]

theorem values_C (i : Fin 4) : (family i).val probeC = (![1, 0, 1, 0] : Fin 4 → ℂ) i := by
  fin_cases i <;>
    norm_num [family, levinsonIndicator, levinsonFacet, SCD, SC, SD, S, A, B, C, D, probeC,
      Fin.sum_univ_succ, Finset.forall_mem_insert, Finset.sum_insert, Fin.ext_iff]

theorem values_D (i : Fin 4) : (family i).val probeD = (![1, 1, 0, 0] : Fin 4 → ℂ) i := by
  fin_cases i <;>
    norm_num [family, levinsonIndicator, levinsonFacet, SCD, SC, SD, S, A, B, C, D, probeD,
      Fin.sum_univ_succ, Finset.forall_mem_insert, Finset.sum_insert, Fin.ext_iff]

theorem family_injective : Function.Injective family := by
  intro i j he
  have hC := congrArg (fun f : levinsonFeasible 5 => f.val probeC) he
  have hD := congrArg (fun f : levinsonFeasible 5 => f.val probeD) he
  simp only [values_C] at hC
  simp only [values_D] at hD
  fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff] at hC <;>
    norm_num [Fin.ext_iff] at hD <;> norm_num [Fin.ext_iff]

end OMA.Levinson

open OMA.Levinson

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_115849.main) := by
  intro h
  have hi : LinearIndependent ℂ (fun i => (family i).val) := (h 5).comp family family_injective
  let c : Fin 4 → ℂ := ![1, -1, -1, 1]
  have hsum : ∑ i, c i • (family i).val = 0 := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Pi.add_apply, Pi.smul_apply,
      Pi.zero_apply, smul_eq_mul]
    change 1 * levinsonIndicator S x +
      ((-1) * levinsonIndicator SC x +
        ((-1) * levinsonIndicator SD x + 1 * levinsonIndicator SCD x)) = 0
    linear_combination relation x
  have hc := (linearIndependent_iff'.1 hi) Finset.univ c hsum 0 (Finset.mem_univ 0)
  norm_num [c] at hc
