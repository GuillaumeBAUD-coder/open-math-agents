import FormalConjectures.ErdosProblems.«552»
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Defect matrices for the four-cycle versus star Ramsey problem

Credit: @TheWaler.

The classical two-path counting argument (Parsons' C₄/star Ramsey bounds) gives
a sparse graph B of pairs without a common neighbour in a C₄-free graph.  We
retain the entire defect pattern and its degree labels. Its matrix M must pass
a trace-zero integral characteristic-polynomial test before any adjacency
square roots need be considered. This reduction is independent of the
Parsons/Chen endpoint and increment reduction. See also Luis Boza, arXiv:2409.12770,
and github.com/zach7036/c4-star-ramsey for the regular degree 7, 8 and 10 cases
of this defect-graph method. The finite certificates in the accompanying handoff
extend its cyclotomic trace test with modular witnesses.
-/
namespace OMA.R_Erdos552_erdos_552_parts_ii_R2
open SimpleGraph Finset Matrix
open scoped Classical

def H1 : Prop := ∀ (m d : ℕ) (G : SimpleGraph (Fin m)), 1 ≤ d →
    (∀ v, d ≤ G.degree v) → ¬ (cycleGraph 4).IsContained G →
    ∃ B : SimpleGraph (Fin m),
      let M : Matrix (Fin m) (Fin m) ℤ := fun i j =>
        if i = j then (G.degree i : ℤ) else if B.Adj i j then 0 else 1
      (∀ v, B.degree v + (d-1)*G.degree v ≤ m-1) ∧
      (∑ v, (B.degree v + G.degree v*(G.degree v-1))) = m*(m-1) ∧
      (IsSquare M.det ∧ ∃ p : Polynomial ℤ, p.coeff 0 = 1 ∧ p.coeff 1 = 0 ∧
        ∀ t : ℤ, M.charpolyRev.eval (t*t) = p.eval t * p.eval (-t)) ∧ G.adjMatrix ℤ * G.adjMatrix ℤ = M

/-- An infinite family of finite obstructions. First enumerate sparse defect patterns
and degree labels, then apply the integral polynomial test. Only the surviving patterns
require ruling out symmetric zero-one adjacency roots with the specified row sums. -/
def H2 : Prop := ∀ K L : ℕ, ∃ n d : ℕ, L < n ∧ 1 ≤ d ∧ (d:ℝ) + K ≤ Real.sqrt n ∧
  ∀ (k : Fin (n+d) → ℕ) (B : SimpleGraph (Fin (n+d))),
    let M : Matrix (Fin (n+d)) (Fin (n+d)) ℤ := fun i j =>
      if i = j then (k i : ℤ) else if B.Adj i j then 0 else 1
    (∀ i, d ≤ k i) →
    (∀ i, B.degree i + (d-1)*k i ≤ n+d-1) →
    (∑ i, (B.degree i + k i*(k i-1))) = (n+d)*(n+d-1) →
    (IsSquare M.det ∧ ∃ p : Polynomial ℤ, p.coeff 0 = 1 ∧ p.coeff 1 = 0 ∧
        ∀ t : ℤ, M.charpolyRev.eval (t*t) = p.eval t * p.eval (-t)) → ¬ ∃ G : SimpleGraph (Fin (n+d)),
      (fun i => G.degree i) = k ∧ G.adjMatrix ℤ * G.adjMatrix ℤ = M

variable {V : Type}

private lemma four_cycle (G : SimpleGraph V) {a b c d : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (da : G.Adj d a)
    (ac : a ≠ c) (bd : b ≠ d) : (cycleGraph 4).IsContained G := by
  let f : Fin 4 → V := fun i => if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d
  have ne₁ := ab.ne
  have ne₂ := bc.ne
  have ne₃ := cd.ne
  have ne₄ := da.ne
  exact ⟨⟨⟨f,by
    intro i j e
    fin_cases i <;> fin_cases j <;> first
      | exact ab | exact bc | exact cd | exact da
      | exact ab.symm | exact bc.symm | exact cd.symm | exact da.symm
      | exfalso; revert e; decide⟩,by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]⟩⟩

private lemma no_second (G : SimpleGraph V) (free : ¬ (cycleGraph 4).IsContained G)
    {v x y z : V} (vy : G.Adj v y) (vz : G.Adj v z) (xv : x ≠ v)
    (xy : G.Adj x y) (xz : G.Adj x z) : y = z := by
  by_contra ne
  exact free (four_cycle G xy vy.symm vz xz.symm xv ne)

private theorem eval_reverse {m : ℕ} (M : Matrix (Fin m) (Fin m) ℤ) (t : ℤ) :
    M.charpolyRev.eval t = (1 - t • M).det := by
  rw [Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  change (Polynomial.evalRingHom t) ((1 : Matrix (Fin m) (Fin m) (Polynomial ℤ)) i j -
      Polynomial.X * Polynomial.C (M i j)) =
    (1 : Matrix (Fin m) (Fin m) ℤ) i j - t * M i j
  by_cases h : i = j <;> simp [Matrix.one_apply,h]

private theorem square_test {m : ℕ} (G : SimpleGraph (Fin m)) :
    let M := G.adjMatrix ℤ * G.adjMatrix ℤ
    (IsSquare M.det ∧ ∃ p : Polynomial ℤ, p.coeff 0 = 1 ∧ p.coeff 1 = 0 ∧
        ∀ t : ℤ, M.charpolyRev.eval (t*t) = p.eval t * p.eval (-t)) := by
  dsimp only
  let A := G.adjMatrix ℤ
  refine ⟨⟨A.det, Matrix.det_mul A A⟩, A.charpolyRev, ?_, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  · simp [A]
  · intro t
    change (A*A).charpolyRev.eval (t*t) = _
    rw [eval_reverse, eval_reverse, eval_reverse, ← Matrix.det_mul]
    congr 1
    simp only [neg_smul, sub_neg_eq_add, sub_mul, mul_add, one_mul, mul_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    abel

private theorem row_count {m : ℕ} (G : SimpleGraph (Fin m))
    (B : SimpleGraph (Fin m))
    (miss : ∀ v x, B.Adj v x ↔ v ≠ x ∧ ¬ ∃ u, G.Adj v u ∧ G.Adj x u)
    (free : ¬ (cycleGraph 4).IsContained G) (v : Fin m) :
    B.degree v + ∑ u ∈ G.neighborFinset v, (G.degree u-1) = m-1 := by
  classical
  let S := G.neighborFinset v
  let T := fun u => (G.neighborFinset u).erase v
  have dis : (S : Set (Fin m)).PairwiseDisjoint T := by
    intro i hi j hj ne
    apply Finset.disjoint_left.mpr
    intro x xi xj
    obtain ⟨xv,ix⟩ := Finset.mem_erase.mp xi
    obtain ⟨_,jx⟩ := Finset.mem_erase.mp xj
    exact ne (no_second G free ((G.mem_neighborFinset _ _).mp hi) ((G.mem_neighborFinset _ _).mp hj) xv
      ((G.mem_neighborFinset _ _).mp ix).symm ((G.mem_neighborFinset _ _).mp jx).symm)
  have cardT (u) (hu : u ∈ S) : (T u).card = G.degree u - 1 := by
    have mem := (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hu).symm
    exact Finset.card_erase_of_mem mem
  have cardSum : (S.biUnion T).card = ∑ u ∈ S, (G.degree u-1) :=
    (Finset.card_biUnion dis).trans (Finset.sum_congr rfl cardT)
  let D := B.neighborFinset v
  have unionEq : D ∪ S.biUnion T = Finset.univ.erase v := by
    ext x
    simp only [D,S,T,Finset.mem_union, Finset.mem_biUnion,Finset.mem_erase,
      Finset.mem_univ,and_true,SimpleGraph.mem_neighborFinset]
    rw [miss]
    change (v ≠ x ∧ ¬ ∃ u, G.Adj v u ∧ G.Adj x u) ∨
      (∃ u, G.Adj v u ∧ x ≠ v ∧ G.Adj u x) ↔ x ≠ v
    constructor
    · rintro (⟨h,_⟩|⟨_,_,h,_⟩)
      · exact h.symm
      · exact h
    · intro h
      by_cases ex : ∃ u, G.Adj v u ∧ G.Adj x u
      · obtain ⟨u,vu,xu⟩ := ex
        exact Or.inr ⟨u,vu,h,xu.symm⟩
      · exact Or.inl ⟨h.symm,ex⟩
  have db : Disjoint D (S.biUnion T) := by
    apply Finset.disjoint_left.mpr
    intro x hx mem
    obtain ⟨u,vu,xu⟩ := Finset.mem_biUnion.mp mem
    exact ((miss _ _).mp ((B.mem_neighborFinset _ _).mp hx)).2
      ⟨u,(G.mem_neighborFinset _ _).mp vu,((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp xu).2).symm⟩
  have h := congrArg Finset.card unionEq
  rw [Finset.card_union_of_disjoint db, cardSum] at h
  simpa [D,S] using h

private theorem square_profile {m : ℕ} (G : SimpleGraph (Fin m))
    (B : SimpleGraph (Fin m))
    (miss : ∀ v x, B.Adj v x ↔ v ≠ x ∧ ¬ ∃ u, G.Adj v u ∧ G.Adj x u)
    (free : ¬ (cycleGraph 4).IsContained G) :
    G.adjMatrix ℤ * G.adjMatrix ℤ = (fun i j => if i = j then (G.degree i : ℤ) else if B.Adj i j then 0 else 1) := by
  classical
  ext v x
  by_cases eq : v = x
  · subst x
    simpa using (G.adjMatrix_mul_self_apply_self (α := ℤ) v)
  rw [SimpleGraph.adjMatrix_mul_apply]
  simp only [if_neg eq]
  by_cases ex : ∃ u, G.Adj v u ∧ G.Adj x u
  · obtain ⟨u,vu,xu⟩ := ex
    have notB : ¬ B.Adj v x := fun h => ((miss _ _).mp h).2 ⟨u,vu,xu⟩
    rw [if_neg notB, Finset.sum_eq_single_of_mem u ((G.mem_neighborFinset _ _).mpr vu)]
    · simp [SimpleGraph.adjMatrix_apply,xu.symm]
    · intro j hj ne
      have no : ¬ G.Adj j x := fun jx => ne (no_second G free ((G.mem_neighborFinset _ _).mp hj) vu
        (Ne.symm eq) jx.symm xu)
      simp [SimpleGraph.adjMatrix_apply,no]
  · rw [if_pos (show B.Adj v x from (miss _ _).mpr ⟨eq,ex⟩)]
    apply Finset.sum_eq_zero
    intro j hj
    have no : ¬ G.Adj j x := fun jx => ex ⟨j,(G.mem_neighborFinset _ _).mp hj,jx.symm⟩
    simp [SimpleGraph.adjMatrix_apply,no]

/-- Both counting identities and the full arithmetic filter hold for every obstruction. -/
theorem finite_obstruction : H1 := by
  classical
  intro m d G hd lower free
  let B : SimpleGraph (Fin m) := {
    Adj := fun x y => x ≠ y ∧ ¬ ∃ u, G.Adj x u ∧ G.Adj y u
    symm := ⟨fun _ _ h => ⟨h.1.symm, fun ⟨u,a,b⟩ => h.2 ⟨u,b,a⟩⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }
  have miss (v x) : B.Adj v x ↔ v ≠ x ∧ ¬ ∃ u, G.Adj v u ∧ G.Adj x u := Iff.rfl
  have row := row_count G B miss free
  have sq := square_profile G B miss free
  refine ⟨B,?_,?_,sq ▸ square_test G,sq⟩
  · intro v
    have le := Finset.sum_le_sum (s := G.neighborFinset v) (f := fun _ => d-1)
      (g := fun u => G.degree u-1) (fun u _ => Nat.sub_le_sub_right (lower u) 1)
    simp only [Finset.sum_const,SimpleGraph.card_neighborFinset_eq_degree,smul_eq_mul] at le
    rw [Nat.mul_comm] at le
    have := row v
    omega
  · have total := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => row i)
    rw [Finset.sum_add_distrib] at total ⊢
    have exchange : (∑ v, ∑ u ∈ G.neighborFinset v, (G.degree u-1)) =
        ∑ u, G.degree u*(G.degree u-1) := by
      simp_rw [SimpleGraph.neighborFinset_eq_filter,Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      simp_rw [SimpleGraph.adj_comm (G := G) _ u]
      rw [← Finset.sum_filter]
      rw [← SimpleGraph.neighborFinset_eq_filter]
      simp [SimpleGraph.card_neighborFinset_eq_degree]
    rw [exchange] at total
    simpa using total

/-- At order d(d−1)+3, all degrees of the graph are forced to be d and every
vertex has exactly two defect partners. This is the cycle case of the test. -/
theorem defect_two (d : ℕ) (hd : 4 ≤ d) (G : SimpleGraph (Fin (d*(d-1)+3)))
    (lower : ∀ v, d ≤ G.degree v) (free : ¬ (cycleGraph 4).IsContained G) :
    (∀ v, G.degree v = d) ∧ ∃ B : SimpleGraph (Fin (d*(d-1)+3)),
      (∀ v, B.degree v = 2) ∧ G.adjMatrix ℤ * G.adjMatrix ℤ =
        (fun i j => if i = j then (d : ℤ) else if B.Adj i j then 0 else 1) := by
  classical
  let B : SimpleGraph (Fin (d*(d-1)+3)) := {
    Adj := fun x y => x ≠ y ∧ ¬ ∃ u, G.Adj x u ∧ G.Adj y u
    symm := ⟨fun _ _ h => ⟨h.1.symm, fun ⟨u,a,b⟩ => h.2 ⟨u,b,a⟩⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }
  have miss (v x) : B.Adj v x ↔ v ≠ x ∧ ¬ ∃ u, G.Adj v u ∧ G.Adj x u := Iff.rfl
  have row := row_count G B miss free
  have reg (v) : G.degree v = d := by
    have le := Finset.sum_le_sum (s := G.neighborFinset v) (f := fun _ => d-1)
      (g := fun u => G.degree u-1) (fun u _ => Nat.sub_le_sub_right (lower u) 1)
    simp only [Finset.sum_const,SimpleGraph.card_neighborFinset_eq_degree,smul_eq_mul] at le
    apply Nat.le_antisymm _ (lower v)
    by_contra! larger
    have mult := Nat.mul_le_mul_right (d-1) (show d+1 ≤ G.degree v from larger)
    rw [Nat.add_mul,Nat.one_mul] at mult
    have := row v
    omega
  refine ⟨reg,B,?_,?_⟩
  · intro v
    have h := row v
    simp only [reg,Finset.sum_const,SimpleGraph.card_neighborFinset_eq_degree,smul_eq_mul] at h
    omega
  · simpa only [reg] using square_profile G B miss free

private theorem large_star {m n : ℕ} (G : SimpleGraph (Fin m)) (v : Fin m)
    (h : n ≤ G.degree v) : (completeBipartiteGraph (Fin 1) (Fin n)).IsContained G := by
  classical
  obtain ⟨S,sub,size⟩ := Finset.exists_subset_card_eq (show n ≤ (G.neighborFinset v).card from h)
  apply completeBipartiteGraph_isContained_iff.mpr
  refine ⟨{v},S,by simp,by simpa using size,?_⟩
  intro i hi j hj
  have : i = v := by simpa using hi
  subst i
  exact (G.mem_neighborFinset _ _).mp (sub hj)

theorem main : H1 → H2 → type_of% @Erdos552.erdos_552.parts.ii := by
  classical
  intro build exclude c hc
  rw [Set.infinite_iff_exists_gt]
  intro L
  obtain ⟨K,hK⟩ := exists_nat_ge c
  obtain ⟨n,d,hn,hd,gap,test⟩ := exclude K L
  have good : ∀ G : SimpleGraph (Fin (n+d)), (cycleGraph 4).IsContained G ∨
      (completeBipartiteGraph (Fin 1) (Fin n)).IsContained Gᶜ := by
    intro G
    by_cases free : (cycleGraph 4).IsContained G
    · exact Or.inl free
    apply Or.inr
    by_contra noStar
    have minDegree (v : Fin (n+d)) : d ≤ G.degree v := by
      have lt : Gᶜ.degree v < n := by
        by_contra! ge
        apply noStar
        apply large_star Gᶜ v
        rw [SimpleGraph.degree_compl, Fintype.card_fin] at ge ⊢
        exact ge
      rw [SimpleGraph.degree_compl, Fintype.card_fin] at lt
      omega
    obtain ⟨B,localBound,total,poly,sq⟩ := build (n+d) d G hd minDegree free
    exact test _ B minDegree localBound total poly ⟨G,rfl,sq⟩
  have cap : graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) ≤ n+d :=
    Nat.sInf_le good
  refine ⟨n,?_,hn⟩
  change (_ : ℝ) ≤ (n:ℝ) + Real.sqrt n - c
  have castCap : (graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) : ℝ) ≤
      (n:ℝ) + d := by exact_mod_cast cap
  linarith

end OMA.R_Erdos552_erdos_552_parts_ii_R2
