import FormalConjectures.ErdosProblems.«159»
import Mathlib.Tactic

/-!
# Reduction R4 of Erdős Problem 159 (Erdos159.erdos_159)

Target (erdosproblems.com/159, 100 dollar Erdős prize): there is `c > 0` with
`R(C_4, K_n) ≪ n^(2-c)`, formally

  `∃ c > 0, ∃ C, ∀ n ≥ 1, graphRamsey (cycleGraph 4) (completeGraph (Fin n)) ≤ C * n^(2-c)`.

State of the art: `n^(3/2)/(log n)^(3/2) ≪ R(C_4,K_n) ≪ n^2/(log n)^2` (upper bound Szemerédi,
mentioned in [EFRS78]; lower bound Spencer [Sp77]); the problem is exactly whether the upper
bound can be pushed below every polylogarithmic saving. It is open.

This file reduces the Ramsey statement to the EXTREMAL statement about independence numbers of
four-cycle-free graphs, which is where every known upper-bound proof for `R(C_4,K_n)` actually
works, and it proves the derivation:

* `H1` (the extremal crux, open): there are `q > 1/2` and `c > 0` such that every `C_4`-free
  graph on `N` vertices has an independent set of size at least `c * N^q`. This is a statement
  about extremal graphs only - no Ramsey numbers - and it is strictly stronger than what
  Szemerédi's method gives, which is only a `sqrt N` times polylogarithmic saving.
* `H2` (finite): the finitely many cases `1 <= n < 4`, bounded by one absolute constant.

The lemmas `exists_indep_finset_of_le_indepNum`, `completeGraph_isContained_compl_of_indep`,
`completeGraph_isContained_compl_of_le_indepNum`, `graphRamsey_le_of_forall` and
`graphRamsey_le_of_forall_indepNum` are the bridge from `H1` to a bound on `graphRamsey`: a large
independent set in a `C_4`-free graph is a copy of `K_n` in its complement, so `N` lies in the set
whose infimum defines `graphRamsey`. `main` then does the real arithmetic: it takes
`N = ceil((n/c)^(1/q))`, so `c * N^q >= n` and `N <= (c^(-1/q) + 1) * n^(1/q)`, and the exponent
`1/q` is `2 - (2 - 1/q)` with `2 - 1/q > 0` exactly because `q > 1/2`.
-/

open scoped SimpleGraph

namespace OMA.R_Erdos159_erdos_159_R4

/-- The extremal hypothesis: some positive power of `N` many vertices can be chosen independent
in every four-cycle-free graph on `N` vertices. -/
def H1 : Prop :=
  ∃ (q : ℝ), 1 / 2 < q ∧ q < 1 ∧ ∃ (c : ℝ), 0 < c ∧
    ∀ (N : ℕ) (C : SimpleGraph (Fin N)),
      ¬ SimpleGraph.IsContained (SimpleGraph.cycleGraph 4) C →
        c * (N : ℝ) ^ q ≤ (C.indepNum : ℝ)

/-- The finitely many small cases of the target, with one absolute constant. -/
def H2 : Prop :=
  ∃ (C₀ : ℝ), 0 ≤ C₀ ∧ ∀ (n : ℕ), 1 ≤ n → n < 4 →
    (SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
      (SimpleGraph.completeGraph (Fin n)) : ℝ) ≤ C₀

/-! ### Bridge lemmas: an independent set of size `n` is a copy of `K_n` in the complement -/

/-- If `n <= H.indepNum` there is a `Finset` of `n` vertices of `H` that is independent. -/
lemma exists_indep_finset_of_le_indepNum {V : Type*} (H : SimpleGraph V) {n : ℕ}
    (h : n ≤ H.indepNum) :
    ∃ S : Finset V, S.card = n ∧ ∀ x ∈ S, ∀ y ∈ S, ¬ H.Adj x y := by
  obtain ⟨S₀, hS₀⟩ := H.exists_isNIndepSet_indepNum
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (s := S₀) (n := n) (hS₀.card_eq ▸ h)
  refine ⟨S, hScard, ?_⟩
  have hpair : (↑S : Set V).Pairwise (fun v w => ¬ H.Adj v w) :=
    hS₀.isIndepSet.mono (by intro x hx; exact hSsub (by simpa using hx))
  intro x hx y hy
  rcases eq_or_ne x y with rfl | hne
  · exact H.irrefl
  · exact hpair (by simpa using hx) (by simpa using hy) hne

/-- A pairwise non-adjacent `Finset` of size `n` in `H` exhibits a copy of the complete graph
`K_n` inside the complement `Hᶜ`. -/
theorem completeGraph_isContained_compl_of_indep {V : Type*} (H : SimpleGraph V)
    {S : Finset V} {n : ℕ} (hS : ∀ x ∈ S, ∀ y ∈ S, ¬ H.Adj x y) (hn : S.card = n) :
    SimpleGraph.IsContained (SimpleGraph.completeGraph (Fin n)) Hᶜ := by
  classical
  set e : S ≃ Fin n := Finset.equivFinOfCardEq hn with he
  set f : Fin n → V := fun i => ((e.symm i : S) : V) with hf
  have hfinj : Function.Injective f := by
    intro i j hij
    have h1 : e.symm i = e.symm j := Subtype.val_injective hij
    exact e.symm.injective h1
  refine ⟨SimpleGraph.Copy.mk ⟨f, ?_⟩ hfinj⟩
  intro a b hab
  have hne : a ≠ b := by simpa using hab
  rw [SimpleGraph.compl_adj]
  exact ⟨hfinj.ne hne, hS _ (e.symm a).2 _ (e.symm b).2⟩

/-- Version phrased with `indepNum`. -/
theorem completeGraph_isContained_compl_of_le_indepNum {V : Type*} (C : SimpleGraph V) {n : ℕ}
    (h : n ≤ C.indepNum) :
    SimpleGraph.IsContained (SimpleGraph.completeGraph (Fin n)) Cᶜ := by
  classical
  obtain ⟨S, hcard, hind⟩ := exists_indep_finset_of_le_indepNum C h
  exact completeGraph_isContained_compl_of_indep C hind hcard

/-- If every graph `C` on `N` vertices contains a `C₄` or has a copy of `K_n` in its complement,
then the graph Ramsey number is at most `N`. -/
theorem graphRamsey_le_of_forall {N n : ℕ}
    (h : ∀ C : SimpleGraph (Fin N),
      SimpleGraph.IsContained (SimpleGraph.cycleGraph 4) C ∨
      SimpleGraph.IsContained (SimpleGraph.completeGraph (Fin n)) Cᶜ) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4) (SimpleGraph.completeGraph (Fin n)) ≤ N :=
  Nat.sInf_le h

/-- The bridge used by `main`: if every `C₄`-free graph on `N` vertices has independence number at
least `n`, then `R(C₄, K_n) <= N`. -/
theorem graphRamsey_le_of_forall_indepNum {N n : ℕ}
    (h : ∀ C : SimpleGraph (Fin N),
      ¬ SimpleGraph.IsContained (SimpleGraph.cycleGraph 4) C → n ≤ C.indepNum) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4) (SimpleGraph.completeGraph (Fin n)) ≤ N := by
  classical
  refine graphRamsey_le_of_forall (N := N) (n := n) ?_
  intro C
  rcases Classical.em (SimpleGraph.IsContained (SimpleGraph.cycleGraph 4) C) with hC | hC
  · exact Or.inl hC
  · exact Or.inr (completeGraph_isContained_compl_of_le_indepNum C (h C hC))

theorem main : H1 → H2 → type_of% @Erdos159.erdos_159 := by
  intro h1 h2
  obtain ⟨q, hq, hq1, c, hc, hext⟩ := h1
  obtain ⟨C₀, hC₀, hsmall⟩ := h2
  have hqpos : 0 < q := by linarith
  have hcoef : (0 : ℝ) < 2 - 1 / q := by
    have h : 1 / q < 2 := by
      rw [div_lt_iff₀ hqpos]
      linarith
    linarith
  refine ⟨2 - 1 / q, hcoef, max (c ^ (-(1 / q)) + 1) C₀, ?_⟩
  intro n hn
  have hqinv : (0 : ℝ) < 1 / q := by positivity
  have hpow1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / q) :=
    Real.one_le_rpow (by exact_mod_cast hn) (le_of_lt hqinv)
  have hpow0 : (0 : ℝ) ≤ (n : ℝ) ^ (1 / q) := le_trans zero_le_one hpow1
  have hexp : (2 : ℝ) - (2 - 1 / q) = 1 / q := by ring
  rw [hexp]
  by_cases hbig : 4 ≤ n
  · -- the asymptotic case: choose `N` with `c * N^q >= n`
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    set x : ℝ := ((n : ℝ) / c) ^ (1 / q) with hx
    have hnc : (0 : ℝ) < (n : ℝ) / c := by positivity
    have hxpos : 0 < x := Real.rpow_pos_of_pos hnc _
    have hxnn : (0 : ℝ) ≤ x := le_of_lt hxpos
    set N : ℕ := ⌈x⌉₊ with hNdef
    have hNge : x ≤ (N : ℝ) := Nat.le_ceil x
    have hNlt : (N : ℝ) < x + 1 := Nat.ceil_lt_add_one hxnn
    have hxq : x ^ q = (n : ℝ) / c := by
      rw [hx, ← Real.rpow_mul (le_of_lt hnc) (1 / q) q,
        one_div_mul_cancel (ne_of_gt hqpos), Real.rpow_one]
    have hNq : x ^ q ≤ (N : ℝ) ^ q := Real.rpow_le_rpow hxnn hNge (le_of_lt hqpos)
    have hcN : (n : ℝ) ≤ c * (N : ℝ) ^ q := by
      have h1 : c * x ^ q ≤ c * (N : ℝ) ^ q := mul_le_mul_of_nonneg_left hNq (le_of_lt hc)
      rw [hxq] at h1
      have h2 : c * ((n : ℝ) / c) = (n : ℝ) := by field_simp
      linarith
    have hR : (SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
        (SimpleGraph.completeGraph (Fin n)) : ℝ) ≤ (N : ℝ) := by
      have h := graphRamsey_le_of_forall_indepNum (N := N) (n := n) (fun C hC => by
        have hle := hext N C hC
        have h' : (n : ℝ) ≤ (C.indepNum : ℝ) := le_trans hcN hle
        exact_mod_cast h')
      exact_mod_cast h
    have hNle : (N : ℝ) ≤ (c ^ (-(1 / q)) + 1) * (n : ℝ) ^ (1 / q) := by
      have h2 : x = (n : ℝ) ^ (1 / q) * c ^ (-(1 / q)) := by
        rw [hx, Real.div_rpow (le_of_lt hnpos) (le_of_lt hc), div_eq_mul_inv,
          ← Real.rpow_neg (le_of_lt hc)]
      have h4 : (0 : ℝ) ≤ c ^ (-(1 / q)) := Real.rpow_nonneg (le_of_lt hc) _
      nlinarith [hNlt, h2, hpow1, h4, hpow0]
    have hmax : c ^ (-(1 / q)) + 1 ≤ max (c ^ (-(1 / q)) + 1) C₀ := le_max_left _ _
    calc (SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
          (SimpleGraph.completeGraph (Fin n)) : ℝ)
        ≤ (N : ℝ) := hR
      _ ≤ (c ^ (-(1 / q)) + 1) * (n : ℝ) ^ (1 / q) := hNle
      _ ≤ max (c ^ (-(1 / q)) + 1) C₀ * (n : ℝ) ^ (1 / q) :=
          mul_le_mul_of_nonneg_right hmax hpow0
  · -- the finitely many small cases
    have hb := hsmall n hn (by omega)
    have h1' : C₀ ≤ C₀ * (n : ℝ) ^ (1 / q) := by
      calc C₀ = C₀ * 1 := (mul_one C₀).symm
        _ ≤ C₀ * (n : ℝ) ^ (1 / q) := mul_le_mul_of_nonneg_left hpow1 hC₀
    have h2' : C₀ * (n : ℝ) ^ (1 / q) ≤
        max (c ^ (-(1 / q)) + 1) C₀ * (n : ℝ) ^ (1 / q) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hpow0
    linarith

end OMA.R_Erdos159_erdos_159_R4
