import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1
import Mathlib

/-!
Assume a cubic graph admits a locally bijective four-coloring. Match the
color fibers along the star at color 0. Three permutations then describe
the remaining edges. If they restrict to translations on an abelian orbit,
the integer-relation certificate below embeds a 4-, 8-, or 16-cycle.
The two residual questions concern graphs with no such coloring and
connected nonbipartite tetrahedral lifts with noncommuting permutations.

Credit: @ubuwaits. The parent reduction is due to @mejiasd3v, building on
the cubic bridge reduction by @JamesSlash.
-/

open Function SimpleGraph
namespace TetrahedralReduction

private theorem addRelation {A : Type*} [AddCommGroup A] {φ : (ℤ × ℤ × ℤ) →+ A}
    {rows : List (ℤ × ℤ × ℤ)} {d : ℤ × ℤ × ℤ}
    (hd : φ d = 0) (h : ∀ v ∈ rows, φ v = 0) : ∀ v ∈ d :: rows, φ v = 0 := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | ht
  · exact hd
  · exact h _ ht

private theorem consequence {A : Type*} [AddCommGroup A] {φ : (ℤ × ℤ × ℤ) →+ A}
    {rows : List (ℤ × ℤ × ℤ)} (h : ∀ v ∈ rows, φ v = 0) (coeff : List ℤ)
    {v : ℤ × ℤ × ℤ} (eq : (List.zipWith (fun r c => c • r) rows coeff).sum = v) :
    φ v = 0 := by
  subst v
  induction rows generalizing coeff with
  | nil => simp
  | cons r rs ih =>
    cases coeff with
    | nil => simp
    | cons c cs =>
      have hr : φ r = 0 := h r (by simp)
      have ht : ∀ v ∈ rs, φ v = 0 := fun v hv => h v (by simp [hv])
      simp only [List.zipWith_cons_cons, List.sum_cons, map_add, map_zsmul,
        hr, zsmul_zero, ih ht cs, add_zero]

private theorem consequences {A : Type*} [AddCommGroup A] {φ : (ℤ × ℤ × ℤ) →+ A}
    {rows dest : List (ℤ × ℤ × ℤ)} (h : ∀ v ∈ rows, φ v = 0) (matrix : List (List ℤ))
    (eq : matrix.map (fun cs => (List.zipWith (fun r c => c • r) rows cs).sum) = dest) :
    ∀ v ∈ dest, φ v = 0 := by
  subst dest
  intro v hv
  obtain ⟨c, _, hc⟩ := List.mem_map.mp hv
  exact consequence h c hc

private theorem testWord {A V : Type*} [AddCommGroup A] (G : SimpleGraph V)
    (φ : (ℤ × ℤ × ℤ) →+ A) (e : Fin 4 × A ↪ V) (δ : Fin 4 → Fin 4 → ℤ × ℤ × ℤ)
    (neighbors : ∀ i j, i ≠ j → ∀ x, G.Adj (e (i, x)) (e (j, x + φ (δ i j))))
    {n : ℕ} [NeZero n] (allowed : n = 4 ∨ n = 8 ∨ n = 16)
    (p : Fin n → Fin 4 × (ℤ × ℤ × ℤ)) (total : ℤ × ℤ × ℤ) (collisions : List (ℤ × ℤ × ℤ))
    (edges : ∀ i, let a := p i; let b := p (i+1)
      a.1 ≠ b.1 ∧ (a.2 + δ a.1 b.1 - b.2 = 0 ∨ a.2 + δ a.1 b.1 - b.2 = total))
    (pairs : ∀ i j, i ≠ j → (p i).1 = (p j).1 →
      (p j).2 - (p i).2 ∈ collisions ∨ -((p j).2 - (p i).2) ∈ collisions)
    (closed : φ total = 0)
    (next : ∀ d ∈ collisions, φ d = 0 → cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  classical
  let label (i : Fin n) : V := e ((p i).1, φ (p i).2)
  by_cases injective : Injective label
  · have side (i : Fin n) : G.Adj (label i) (label (i+1)) := by
      obtain ⟨hne, hz⟩ := edges i
      have h : φ ((p i).2 + δ (p i).1 (p (i+1)).1 - (p (i+1)).2) = 0 := by
        rcases hz with hz | hz <;> simp [hz,closed]
      have replace : φ (p i).2 + φ (δ (p i).1 (p (i+1)).1) = φ (p (i+1)).2 := by
        simpa only [map_sub, map_add, sub_eq_zero] using h
      simpa only [label, replace] using neighbors _ _ hne (φ (p i).2)
    have contains : cycleGraph n ⊑ G := by
      refine ⟨⟨⟨label, ?_⟩, injective⟩⟩
      intro i j hij
      have h1 : 1 < n := by omega
      have h : i-j = 1 ∨ j-i = 1 := by
        simpa only [Fin.ext_iff, Fin.val_one', Nat.mod_eq_of_lt h1] using cycleGraph_adj'.mp hij
      rcases h with h | h
      · have eq : i = j+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h
        simpa only [eq] using (side j).symm
      · have eq : j = i+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h
        simpa only [eq] using side i
    rcases allowed with rfl | rfl | rfl
    · exact Or.inl contains
    · exact Or.inr (Or.inl contains)
    · exact Or.inr (Or.inr contains)
  · obtain ⟨i, j, same, ne⟩ := Function.not_injective_iff.mp injective
    have xy := e.injective same
    have hc : (p i).1 = (p j).1 := congrArg (fun z : Fin 4 × A => z.1) xy
    have hp : φ (p i).2 = φ (p j).2 := congrArg (fun z : Fin 4 × A => z.2) xy
    have dz : φ ((p j).2 - (p i).2) = 0 := by simp [hp]
    rcases pairs i j ne hc with h | h
    · exact next _ h dz
    · exact next _ h (by rw [map_neg, dz, neg_zero])

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
/-- A presentation by three abelian translations suffices on any embedded orbit. -/
theorem abelianTetrahedron {A V : Type*} [AddCommGroup A] (G : SimpleGraph V)
    (e : Fin 4 × A ↪ V) (a b c : A)
    (star : ∀ j : Fin 4, j ≠ 0 → ∀ x, G.Adj (e (0,x)) (e (j,x)))
    (twelve : ∀ x, G.Adj (e (1,x)) (e (2,x+a)))
    (twentythree : ∀ x, G.Adj (e (2,x)) (e (3,x+b)))
    (thirtyone : ∀ x, G.Adj (e (3,x)) (e (1,x+c))) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  let φ : (ℤ × ℤ × ℤ) →+ A := {
    toFun := fun z => z.1 • a + z.2.1 • b + z.2.2 • c
    map_zero' := by simp
    map_add' := by intro x y; simp only [Prod.fst_add, Prod.snd_add, add_zsmul]; abel }
  let δ (i j : Fin 4) : ℤ × ℤ × ℤ :=
    match i.val, j.val with
    | 1, 2 => (1, 0, 0)
    | 2, 3 => (0, 1, 0)
    | 3, 1 => (0, 0, 1)
    | 2, 1 => (-1, 0, 0)
    | 3, 2 => (0, -1, 0)
    | 1, 3 => (0, 0, -1)
    | _, _ => 0
  have neighbors (i j : Fin 4) (hne : i ≠ j) (x : A) :
      G.Adj (e (i,x)) (e (j,x + φ (δ i j))) := by
    fin_cases i <;> fin_cases j <;> first
    | exact (hne rfl).elim
    | simpa [δ, φ] using star _ (by decide) x
    | simpa [δ, φ] using (star _ (by decide) x).symm
    | simpa [δ, φ] using twelve x
    | simpa [δ, φ] using twentythree x
    | simpa [δ, φ] using thirtyone x
    | simpa [δ, φ, sub_eq_add_neg] using (twelve (x-a)).symm
    | simpa [δ, φ, sub_eq_add_neg] using (twentythree (x-b)).symm
    | simpa [δ, φ, sub_eq_add_neg] using (thirtyone (x-c)).symm
  let good := cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G
  -- Projected color words and their successive sheet displacements, relative
  -- to the three chord generators. The final closing vertex is implicit.

  let word0123 : Fin 4 → Fin 4 × (ℤ × ℤ × ℤ) :=
    ![(0, 0, 0, 0), (1, 0, 0, 0), (2, 1, 0, 0), (3, 1, 1, 0)]
  let word0132 : Fin 4 → Fin 4 × (ℤ × ℤ × ℤ) :=
    ![(0, 0, 0, 0), (1, 0, 0, 0), (3, 0, 0, -1), (2, 0, -1, -1)]
  let word0213 : Fin 4 → Fin 4 × (ℤ × ℤ × ℤ) :=
    ![(0, 0, 0, 0), (2, 0, 0, 0), (1, -1, 0, 0), (3, -1, 0, -1)]
  let word01203123 : Fin 8 → Fin 4 × (ℤ × ℤ × ℤ) :=
    ![(0, 0, 0, 0), (1, 0, 0, 0), (2, 1, 0, 0), (0, 1, 0, 0),
      (3, 1, 0, 0), (1, 1, 0, 1), (2, 2, 0, 1), (3, 2, 1, 1)]
  let word01230132 : Fin 8 → Fin 4 × (ℤ × ℤ × ℤ) :=
    ![(0, 0, 0, 0), (1, 0, 0, 0), (2, 1, 0, 0), (3, 1, 1, 0),
      (0, 1, 1, 0), (1, 1, 1, 0), (3, 1, 1, -1), (2, 1, 0, -1)]
  let word01230213 : Fin 8 → Fin 4 × (ℤ × ℤ × ℤ) :=
    ![(0, 0, 0, 0), (1, 0, 0, 0), (2, 1, 0, 0), (3, 1, 1, 0),
      (0, 1, 1, 0), (2, 1, 1, 0), (1, 0, 1, 0), (3, 0, 1, -1)]
  let word01302132 : Fin 8 → Fin 4 × (ℤ × ℤ × ℤ) :=
    ![(0, 0, 0, 0), (1, 0, 0, 0), (3, 0, 0, -1), (0, 0, 0, -1),
      (2, 0, 0, -1), (1, -1, 0, -1), (3, -1, 0, -2), (2, -1, -1, -2)]
  let word01320312 : Fin 8 → Fin 4 × (ℤ × ℤ × ℤ) :=
    ![(0, 0, 0, 0), (1, 0, 0, 0), (3, 0, 0, -1), (2, 0, -1, -1),
      (0, 0, -1, -1), (3, 0, -1, -1), (1, 0, -1, 0), (2, 1, -1, 0)]
  let word02130213 : Fin 8 → Fin 4 × (ℤ × ℤ × ℤ) :=
    ![(0, 0, 0, 0), (2, 0, 0, 0), (1, -1, 0, 0), (3, -1, 0, -1),
      (0, -1, 0, -1), (2, -1, 0, -1), (1, -2, 0, -1), (3, -2, 0, -2)]
  let word0120120310210213 : Fin 16 → Fin 4 × (ℤ × ℤ × ℤ) :=
    ![(0, 0, 0, 0), (1, 0, 0, 0), (2, 1, 0, 0), (0, 1, 0, 0),
      (1, 1, 0, 0), (2, 2, 0, 0), (0, 2, 0, 0), (3, 2, 0, 0),
      (1, 2, 0, 1), (0, 2, 0, 1), (2, 2, 0, 1), (1, 1, 0, 1),
      (0, 1, 0, 1), (2, 1, 0, 1), (1, 0, 0, 1), (3, 0, 0, 0)]
  let word0120120321021023 : Fin 16 → Fin 4 × (ℤ × ℤ × ℤ) :=
    ![(0, 0, 0, 0), (1, 0, 0, 0), (2, 1, 0, 0), (0, 1, 0, 0),
      (1, 1, 0, 0), (2, 2, 0, 0), (0, 2, 0, 0), (3, 2, 0, 0),
      (2, 2, -1, 0), (1, 1, -1, 0), (0, 1, -1, 0), (2, 1, -1, 0),
      (1, 0, -1, 0), (0, 0, -1, 0), (2, 0, -1, 0), (3, 0, 0, 0)]
  let word0120310310213013 : Fin 16 → Fin 4 × (ℤ × ℤ × ℤ) :=
    ![(0, 0, 0, 0), (1, 0, 0, 0), (2, 1, 0, 0), (0, 1, 0, 0),
      (3, 1, 0, 0), (1, 1, 0, 1), (0, 1, 0, 1), (3, 1, 0, 1),
      (1, 1, 0, 2), (0, 1, 0, 2), (2, 1, 0, 2), (1, 0, 0, 2),
      (3, 0, 0, 1), (0, 0, 0, 1), (1, 0, 0, 1), (3, 0, 0, 0)]
  let word0123103103213013 : Fin 16 → Fin 4 × (ℤ × ℤ × ℤ) :=
    ![(0, 0, 0, 0), (1, 0, 0, 0), (2, 1, 0, 0), (3, 1, 1, 0),
      (1, 1, 1, 1), (0, 1, 1, 1), (3, 1, 1, 1), (1, 1, 1, 2),
      (0, 1, 1, 2), (3, 1, 1, 2), (2, 1, 0, 2), (1, 0, 0, 2),
      (3, 0, 0, 1), (0, 0, 0, 1), (1, 0, 0, 1), (3, 0, 0, 0)]
  let word0213021302130213 : Fin 16 → Fin 4 × (ℤ × ℤ × ℤ) :=
    ![(0, 0, 0, 0), (2, 0, 0, 0), (1, -1, 0, 0), (3, -1, 0, -1),
      (0, -1, 0, -1), (2, -1, 0, -1), (1, -2, 0, -1), (3, -2, 0, -2),
      (0, -2, 0, -2), (2, -2, 0, -2), (1, -3, 0, -2), (3, -3, 0, -3),
      (0, -3, 0, -3), (2, -3, 0, -3), (1, -4, 0, -3), (3, -4, 0, -4)]
  have case0 (h : ∀ v ∈ ([(0, 1, 0), (0, 0, 1)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 4) (by decide)
      word0132 (0, -1, -1) []
      (by dsimp only [δ, word0132]; decide) (by dsimp only [word0132]; decide)
      (consequence h [-1, -1] (by decide))
    intro d hd hz
    simp at hd
  have case1 (h : ∀ v ∈ ([(1, 0, 0), (0, 1, 0), (0, 0, 1)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 4) (by decide)
      word0123 (1, 1, 0) []
      (by dsimp only [δ, word0123]; decide) (by dsimp only [word0123]; decide)
      (consequence h [1, 1, 0] (by decide))
    intro d hd hz
    simp at hd
  have case2 (h : ∀ v ∈ ([(1, -1, 0), (0, 0, 1)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 8) (by decide)
      word01320312 (1, -1, 0) [(0, 1, 0), (0, 1, 1), (1, 0, 1)]
      (by dsimp only [δ, word01320312]; decide) (by dsimp only [word01320312]; decide)
      (consequence h [1, 0] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact case1 (consequences (addRelation hz h) [[1, 1, 0], [1, 0, 0], [0, 0, 1]] (by decide))
    · exact case1 (consequences (addRelation hz h) [[1, 1, -1], [1, 0, -1], [0, 0, 1]] (by decide))
    · exact case1 (consequences (addRelation hz h) [[1, 0, -1], [1, -1, -1], [0, 0, 1]] (by decide))
  have case3 (h : ∀ v ∈ ([(1, 0, 0), (0, 0, 1)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 4) (by decide)
      word0213 (-1, 0, -1) []
      (by dsimp only [δ, word0213]; decide) (by dsimp only [word0213]; decide)
      (consequence h [-1, -1] (by decide))
    intro d hd hz
    simp at hd
  have case4 (h : ∀ v ∈ ([(1, 1, 0), (0, 0, 1)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 4) (by decide)
      word0123 (1, 1, 0) []
      (by dsimp only [δ, word0123]; decide) (by dsimp only [word0123]; decide)
      (consequence h [1, 0] (by decide))
    intro d hd hz
    simp at hd
  have case5 (h : ∀ v ∈ ([(2, 0, 0), (0, 0, 1)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 8) (by decide)
      word02130213 (-2, 0, -2) [(1, 0, 1)]
      (by dsimp only [δ, word02130213]; decide) (by dsimp only [word02130213]; decide)
      (consequence h [-1, -2] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    exact case3 (consequences (addRelation hz h) [[1, 0, -1], [0, 0, 1]] (by decide))
  have case6 (h : ∀ v ∈ ([(2, 1, 0), (0, 0, 1)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 8) (by decide)
      word01203123 (2, 1, 1) [(1, 0, 0), (1, 0, 1), (1, 1, 1)]
      (by dsimp only [δ, word01203123]; decide) (by dsimp only [word01203123]; decide)
      (consequence h [1, 1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact case1 (consequences (addRelation hz h) [[1, 0, 0], [-2, 1, 0], [0, 0, 1]] (by decide))
    · exact case1 (consequences (addRelation hz h) [[1, 0, -1], [-2, 1, 2], [0, 0, 1]] (by decide))
    · exact case1 (consequences (addRelation hz h) [[-1, 1, 1], [2, -1, -2], [0, 0, 1]] (by decide))
  have case7 (h : ∀ v ∈ ([(0, 0, 1)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 16) (by decide)
      word0120120321021023 (0, 0, 0) [(0, 1, 0), (1, -1, 0), (1, 0, 0), (1, 1, 0), (2, 0, 0), (2, 1, 0)]
      (by dsimp only [δ, word0120120321021023]; decide) (by dsimp only [word0120120321021023]; decide)
      (consequence h [0] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact case0 (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
    · exact case2 (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
    · exact case3 (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
    · exact case4 (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
    · exact case5 (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
    · exact case6 (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
  have case8 (h : ∀ v ∈ ([(1, 0, -1), (0, 1, 1)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 4) (by decide)
      word0123 (1, 1, 0) []
      (by dsimp only [δ, word0123]; decide) (by dsimp only [word0123]; decide)
      (consequence h [1, 1] (by decide))
    intro d hd hz
    simp at hd
  have case9 (h : ∀ v ∈ ([(1, 0, -1)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 8) (by decide)
      word01230132 (1, 0, -1) [(0, 0, 1), (1, 1, 0)]
      (by dsimp only [δ, word01230132]; decide) (by dsimp only [word01230132]; decide)
      (consequence h [1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact case3 (consequences (addRelation hz h) [[1, 1], [1, 0]] (by decide))
    · exact case8 (consequences (addRelation hz h) [[0, 1], [1, -1]] (by decide))
  have case10 (h : ∀ v ∈ ([(1, 0, 0), (0, 0, 2)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 8) (by decide)
      word02130213 (-2, 0, -2) [(1, 0, 1)]
      (by dsimp only [δ, word02130213]; decide) (by dsimp only [word02130213]; decide)
      (consequence h [-2, -1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    exact case3 (consequences (addRelation hz h) [[0, 1, 0], [1, -1, 0]] (by decide))
  have case11 (h : ∀ v ∈ ([(1, 0, 0), (0, 1, -1)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 8) (by decide)
      word01230213 (0, 1, -1) [(0, 1, 0), (1, 0, 1), (1, 1, 0)]
      (by dsimp only [δ, word01230213]; decide) (by dsimp only [word01230213]; decide)
      (consequence h [0, 1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact case1 (consequences (addRelation hz h) [[0, 1, 0], [1, 0, 0], [1, 0, -1]] (by decide))
    · exact case1 (consequences (addRelation hz h) [[0, 1, 0], [1, -1, 1], [1, -1, 0]] (by decide))
    · exact case1 (consequences (addRelation hz h) [[0, 1, 0], [1, -1, 0], [1, -1, -1]] (by decide))
  have case12 (h : ∀ v ∈ ([(1, 0, 0), (0, 1, 0)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 4) (by decide)
      word0123 (1, 1, 0) []
      (by dsimp only [δ, word0123]; decide) (by dsimp only [word0123]; decide)
      (consequence h [1, 1] (by decide))
    intro d hd hz
    simp at hd
  have case13 (h : ∀ v ∈ ([(1, 0, 0), (0, 1, 1)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 4) (by decide)
      word0132 (0, -1, -1) []
      (by dsimp only [δ, word0132]; decide) (by dsimp only [word0132]; decide)
      (consequence h [0, -1] (by decide))
    intro d hd hz
    simp at hd
  have case14 (h : ∀ v ∈ ([(1, 0, 0), (0, 1, 2)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 8) (by decide)
      word01302132 (-1, -1, -2) [(0, 0, 1), (1, 0, 1), (1, 1, 1)]
      (by dsimp only [δ, word01302132]; decide) (by dsimp only [word01302132]; decide)
      (consequence h [-1, -1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact case1 (consequences (addRelation hz h) [[0, 1, 0], [-2, 0, 1], [1, 0, 0]] (by decide))
    · exact case1 (consequences (addRelation hz h) [[0, 1, 0], [-2, 2, 1], [1, -1, 0]] (by decide))
    · exact case1 (consequences (addRelation hz h) [[0, 1, 0], [2, -2, -1], [-1, 1, 1]] (by decide))
  have case15 (h : ∀ v ∈ ([(1, 0, 0)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 16) (by decide)
      word0123103103213013 (0, 0, 0) [(0, 0, 1), (0, 0, 2), (1, 1, -1), (1, 1, 0), (1, 1, 1), (1, 1, 2)]
      (by dsimp only [δ, word0123103103213013]; decide) (by dsimp only [word0123103103213013]; decide)
      (consequence h [0] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact case3 (consequences (addRelation hz h) [[0, 1], [1, 0]] (by decide))
    · exact case10 (consequences (addRelation hz h) [[0, 1], [1, 0]] (by decide))
    · exact case11 (consequences (addRelation hz h) [[0, 1], [1, -1]] (by decide))
    · exact case12 (consequences (addRelation hz h) [[0, 1], [1, -1]] (by decide))
    · exact case13 (consequences (addRelation hz h) [[0, 1], [1, -1]] (by decide))
    · exact case14 (consequences (addRelation hz h) [[0, 1], [1, -1]] (by decide))
  have case16 (h : ∀ v ∈ ([(1, 0, 1)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 4) (by decide)
      word0213 (-1, 0, -1) []
      (by dsimp only [δ, word0213]; decide) (by dsimp only [word0213]; decide)
      (consequence h [-1] (by decide))
    intro d hd hz
    simp at hd
  have case17 (h : ∀ v ∈ ([(1, 0, 1), (0, 0, 2)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 4) (by decide)
      word0213 (-1, 0, -1) []
      (by dsimp only [δ, word0213]; decide) (by dsimp only [word0213]; decide)
      (consequence h [-1, 0] (by decide))
    intro d hd hz
    simp at hd
  have case18 (h : ∀ v ∈ ([(2, 0, 0), (0, 0, 2)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 8) (by decide)
      word02130213 (-2, 0, -2) [(1, 0, 1)]
      (by dsimp only [δ, word02130213]; decide) (by dsimp only [word02130213]; decide)
      (consequence h [-1, -1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    exact case17 (consequences (addRelation hz h) [[1, 0, 0], [2, -1, 0]] (by decide))
  have case19 (h : ∀ v ∈ ([(1, 0, 2), (0, 0, 4)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 16) (by decide)
      word0213021302130213 (-4, 0, -4) [(1, 0, 1), (2, 0, 2), (3, 0, 3)]
      (by dsimp only [δ, word0213021302130213]; decide) (by dsimp only [word0213021302130213]; decide)
      (consequence h [-4, 1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact case3 (consequences (addRelation hz h) [[2, -1, 0], [-1, 1, 0]] (by decide))
    · exact case10 (consequences (addRelation hz h) [[1, -1, 0], [-1, 2, 0]] (by decide))
    · exact case3 (consequences (addRelation hz h) [[-2, 7, -2], [1, -3, 1]] (by decide))
  have case20 (h : ∀ v ∈ ([(2, 0, 0)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 16) (by decide)
      word0120310310213013 (0, 0, 0) [(0, 0, 1), (0, 0, 2), (1, 0, -1), (1, 0, 0), (1, 0, 1), (1, 0, 2)]
      (by dsimp only [δ, word0120310310213013]; decide) (by dsimp only [word0120310310213013]; decide)
      (consequence h [0] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact case5 (consequences (addRelation hz h) [[0, 1], [1, 0]] (by decide))
    · exact case18 (consequences (addRelation hz h) [[0, 1], [1, 0]] (by decide))
    · exact case17 (consequences (addRelation hz h) [[-1, 1], [-2, 1]] (by decide))
    · exact case15 (consequences (addRelation hz h) [[1, 0]] (by decide))
    · exact case17 (consequences (addRelation hz h) [[1, 0], [2, -1]] (by decide))
    · exact case19 (consequences (addRelation hz h) [[1, 0], [2, -1]] (by decide))
  have case21 (h : ∀ v ∈ ([(2, 0, 1), (0, 0, 2)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 16) (by decide)
      word0213021302130213 (-4, 0, -4) [(1, 0, 1), (2, 0, 2), (3, 0, 3)]
      (by dsimp only [δ, word0213021302130213]; decide) (by dsimp only [word0213021302130213]; decide)
      (consequence h [-2, -1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact case3 (consequences (addRelation hz h) [[-1, 1, 0], [2, -1, 0]] (by decide))
    · exact case5 (consequences (addRelation hz h) [[-1, 2, 0], [1, -1, 0]] (by decide))
    · exact case3 (consequences (addRelation hz h) [[5, -7, -4], [-2, 3, 2]] (by decide))
  have case22 (h : ∀ v ∈ ([(1, 0, 2), (0, 1, 1), (0, 0, 3)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 4) (by decide)
      word0123 (1, 1, 0) []
      (by dsimp only [δ, word0123]; decide) (by dsimp only [word0123]; decide)
      (consequence h [1, 1, -1] (by decide))
    intro d hd hz
    simp at hd
  have case23 (h : ∀ v ∈ ([(1, 0, 2), (0, 0, 3)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 8) (by decide)
      word01230132 (1, 0, -1) [(0, 0, 1), (1, 1, 0)]
      (by dsimp only [δ, word01230132]; decide) (by dsimp only [word01230132]; decide)
      (consequence h [1, -1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact case3 (consequences (addRelation hz h) [[-2, 1, 0], [1, 0, 0]] (by decide))
    · exact case22 (consequences (addRelation hz h) [[0, 1, 0], [1, -1, 1], [0, 0, 1]] (by decide))
  have case24 (h : ∀ v ∈ ([(2, 0, 1)] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 16) (by decide)
      word0120310310213013 (0, 0, 0) [(0, 0, 1), (0, 0, 2), (1, 0, -1), (1, 0, 0), (1, 0, 1), (1, 0, 2)]
      (by dsimp only [δ, word0120310310213013]; decide) (by dsimp only [word0120310310213013]; decide)
      (consequence h [0] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact case5 (consequences (addRelation hz h) [[-1, 1], [1, 0]] (by decide))
    · exact case21 (consequences (addRelation hz h) [[0, 1], [1, 0]] (by decide))
    · exact case23 (consequences (addRelation hz h) [[-1, 1], [-2, 1]] (by decide))
    · exact case3 (consequences (addRelation hz h) [[1, 0], [-2, 1]] (by decide))
    · exact case3 (consequences (addRelation hz h) [[-1, 1], [2, -1]] (by decide))
    · exact case23 (consequences (addRelation hz h) [[1, 0], [2, -1]] (by decide))
  have case25 (h : ∀ v ∈ ([] : List (ℤ × ℤ × ℤ)), φ v = 0) : good := by
    apply testWord G φ e δ neighbors (n := 16) (by decide)
      word0120120310210213 (0, 0, 0) [(0, 0, 1), (1, 0, -1), (1, 0, 0), (1, 0, 1), (2, 0, 0), (2, 0, 1)]
      (by dsimp only [δ, word0120120310210213]; decide) (by dsimp only [word0120120310210213]; decide)
      (consequence h [] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact case7 (consequences (addRelation hz h) [[1]] (by decide))
    · exact case9 (consequences (addRelation hz h) [[1]] (by decide))
    · exact case15 (consequences (addRelation hz h) [[1]] (by decide))
    · exact case16 (consequences (addRelation hz h) [[1]] (by decide))
    · exact case20 (consequences (addRelation hz h) [[1]] (by decide))
    · exact case24 (consequences (addRelation hz h) [[1]] (by decide))
  exact case25 (by simp)

/-- Along each edge of K4 the covering induces a bijection of its fibers.
Using the three maps out of color zero as coordinates makes those maps
identities and leaves one permutation for each of the other three edges. -/
theorem normalize {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (color : V → Fin 4)
    (unique : ∀ x j, j ≠ color x → ∃! y, G.Adj x y ∧ color y = j) :
    ∃ (X : Type) (_ : Fintype X) (_ : Nonempty X) (p q r : Equiv.Perm X)
      (label : Fin 4 × X ↪ V),
      Surjective label ∧ (∀ z, color (label z) = z.1) ∧
      (∀ j : Fin 4, j ≠ 0 → ∀ x, G.Adj (label (0,x)) (label (j,x))) ∧
      (∀ x, G.Adj (label (1,x)) (label (2,p x))) ∧
      (∀ x, G.Adj (label (2,x)) (label (3,q x))) ∧
      (∀ x, G.Adj (label (3,x)) (label (1,r x))) := by
  classical
  let fiber (j : Fin 4) := {x : V // color x = j}
  let cross {i j : Fin 4} (h : i ≠ j) (x : fiber i) : fiber j :=
    let u := unique x.val j (x.property.symm ▸ h.symm)
    ⟨u.choose, u.choose_spec.1.2⟩
  have step {i j : Fin 4} (h : i ≠ j) (x : fiber i) : G.Adj x.val (cross h x).val :=
    (unique x.val j (x.property.symm ▸ h.symm)).choose_spec.1.1
  have back {i j : Fin 4} (h : i ≠ j) (x : fiber i) : cross h.symm (cross h x) = x := by
    apply Subtype.ext
    apply (unique (cross h x).val i ((cross h x).property.symm ▸ h)).unique
    · exact ⟨step h.symm _, (cross h.symm _).property⟩
    · exact ⟨(step h x).symm, x.property⟩
  let transport {i j : Fin 4} (h : i ≠ j) : fiber i ≃ fiber j :=
    ⟨cross h, cross h.symm, back h, back h.symm⟩
  let X := fiber 0
  have inhabited : Nonempty X := by
    obtain ⟨v⟩ := ‹Nonempty V›
    by_cases hv : color v = 0
    · exact ⟨⟨v,hv⟩⟩
    · obtain ⟨w,hw,_⟩ := unique v 0 (Ne.symm hv)
      exact ⟨⟨w,hw.2⟩⟩
  let frame (j : Fin 4) : X ≃ fiber j :=
    if h : j = 0 then h ▸ Equiv.refl _ else transport (Ne.symm h)
  let value (z : Fin 4 × X) : V := (frame z.1 z.2).val
  have inj : Injective value := by
    rintro ⟨i,x⟩ ⟨j,y⟩ heq
    have ij := congrArg color heq
    change color (frame i x).val = color (frame j y).val at ij
    rw [(frame i x).property, (frame j y).property] at ij
    subst j
    exact Prod.ext rfl ((frame i).injective (Subtype.ext heq))
  let label : Fin 4 × X ↪ V := ⟨value,inj⟩
  let chord {i j : Fin 4} (h : i ≠ j) : Equiv.Perm X :=
    ((frame i).trans (transport h)).trans (frame j).symm
  have edge {i j : Fin 4} (h : i ≠ j) (x : X) :
      G.Adj (label (i,x)) (label (j,chord h x)) := by
    simpa [label,value,chord,transport] using step h (frame i x)
  refine ⟨X,Fintype.ofFinite X,inhabited,chord (by decide : (1 : Fin 4) ≠ 2),
    chord (by decide : (2 : Fin 4) ≠ 3),chord (by decide : (3 : Fin 4) ≠ 1),
    label,?_,fun z => (frame z.1 z.2).property,?_,
    edge (by decide),edge (by decide),edge (by decide)⟩
  · intro v
    let w : fiber (color v) := ⟨v,rfl⟩
    use (color v,(frame (color v)).symm w)
    change (frame (color v) ((frame (color v)).symm w)).val = v
    rw [Equiv.apply_symm_apply]
  · intro j hj x
    simpa [label,value,frame,hj,transport] using step hj.symm x

end TetrahedralReduction



open Function
namespace TetrahedralReduction

open scoped IsMulCommutative in
theorem commutingOrbit {X : Type} [Nonempty X] (p q r : Equiv.Perm X)
    (hpq : Commute p q) (hqr : Commute q r) (hrp : Commute r p) :
    ∃ (A : Type) (_ : AddCommGroup A) (f : A ↪ X) (a b c : A),
      ∀ x, p (f x) = f (x+a) ∧ q (f x) = f (x+b) ∧ r (f x) = f (x+c) := by
  classical
  let generators : Set (Equiv.Perm X) := {p,q,r}
  let H := Subgroup.closure generators
  let : IsMulCommutative H := Subgroup.isMulCommutative_closure (by
    intro a ha b hb
    simp only [generators, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first | rfl | exact hpq.eq | exact hpq.symm.eq | exact hqr.eq | exact hqr.symm.eq |
        exact hrp.eq | exact hrp.symm.eq)
  let x₀ : X := Classical.arbitrary X
  let Q := H ⧸ MulAction.stabilizer H x₀
  let f : Additive Q ↪ X :=
    ⟨MulAction.ofQuotientStabilizer H x₀, MulAction.injective_ofQuotientStabilizer H x₀⟩
  let g₁ : H := ⟨p, Subgroup.subset_closure (by simp [generators])⟩
  let g₂ : H := ⟨q, Subgroup.subset_closure (by simp [generators])⟩
  let g₃ : H := ⟨r, Subgroup.subset_closure (by simp [generators])⟩
  let val (g : H) : Additive Q := Additive.ofMul (QuotientGroup.mk g : Q)
  have action (g : H) (x : Additive Q) : g.val (f x) = f (x + val g) := by
    change g • MulAction.ofQuotientStabilizer H x₀ x.toMul =
      MulAction.ofQuotientStabilizer H x₀ (x.toMul * (QuotientGroup.mk g : Q))
    rw [mul_comm]
    exact (MulAction.ofQuotientStabilizer_smul H x₀ g x.toMul).symm
  exact ⟨Additive Q, inferInstance, f, val g₁, val g₂, val g₃, fun x =>
    ⟨action g₁ x, action g₂ x, action g₃ x⟩⟩

end TetrahedralReduction

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H1_R1

/-- The remaining graphs without a locally bijective four-coloring. -/
def H1 : Prop := ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
  G.Connected → (∀ x, G.degree x = 3) →
  (∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a,b)) → ¬ G.IsBipartite →
  (¬ ∃ color : V → Fin 4, (∀ ⦃x y⦄, G.Adj x y → color x ≠ color y) ∧
    ∀ x j, j ≠ color x → ∃! y, G.Adj x y ∧ color y = j) →
  ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

/-- Connected nonbipartite tetrahedral lifts with noncommuting chord permutations.
The edges from color 0 preserve the sheet. The edges 12, 23 and 31 use p, q
and r, respectively. -/
def H2 : Prop := ∀ (X : Type) [Fintype X] [Nonempty X] (p q r : Equiv.Perm X),
  ¬ (Commute p q ∧ Commute q r ∧ Commute r p) →
  let K := SimpleGraph.fromRel (fun u v : Fin 4 × X =>
    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨
    (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨
    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨
    (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2))
  K.Connected → ¬ K.IsBipartite → ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ K

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.H1 := by
  intro noColor nonAbelian V G fin dec connected cubic bridgeless nonbipartite
  classical
  by_cases colors : ∃ color : V → Fin 4,
      (∀ ⦃x y⦄, G.Adj x y → color x ≠ color y) ∧
      ∀ x j, j ≠ color x → ∃! y, G.Adj x y ∧ color y = j
  · obtain ⟨color, proper, unique⟩ := colors
    let : Nonempty V := connected.nonempty
    obtain ⟨X, instF, instN, p, q, r, label, onto, color_label, star, oneTwo, twoThree, threeOne⟩ :=
      TetrahedralReduction.normalize G color unique
    have solve {k : ℕ} (hk : 2 ≤ k) (hc : cycleGraph (2^k) ⊑ G) :
        ∃ (j : ℕ) (v : V) (c : G.Walk v v), 2 ≤ j ∧ c.IsCycle ∧ c.length = 2^j := by
      have h : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
      obtain ⟨v,c,cyc,length⟩ := (cycleGraph_isContained_iff (by omega : 2 < 2^k)).mp hc
      exact ⟨k,v,c,hk,cyc,length⟩
    by_cases ab : ∃ (A : Type) (_ : AddCommGroup A) (f : A ↪ X) (a b c : A),
        ∀ x, p (f x) = f (x+a) ∧ q (f x) = f (x+b) ∧ r (f x) = f (x+c)
    · obtain ⟨A, ia, f, a, b, c, shifts⟩ := ab
      let e : Fin 4 × A ↪ V := (Function.Embedding.prodMap (Function.Embedding.refl _) f).trans label
      have short := TetrahedralReduction.abelianTetrahedron G e a b c
        (fun j hj x => star j hj (f x))
        (fun x => by change G.Adj (label (1,f x)) (label (2,f (x+a))); rw [← (shifts x).1]; exact oneTwo _)
        (fun x => by change G.Adj (label (2,f x)) (label (3,f (x+b))); rw [← (shifts x).2.1]; exact twoThree _)
        (fun x => by change G.Adj (label (3,f x)) (label (1,f (x+c))); rw [← (shifts x).2.2]; exact threeOne _)
      rcases short with h | h | h
      · exact solve (k := 2) (by decide) h
      · exact solve (k := 3) (by decide) h
      · exact solve (k := 4) (by decide) h
    · have nc : ¬ (Commute p q ∧ Commute q r ∧ Commute r p) :=
        fun h => ab (TetrahedralReduction.commutingOrbit p q r h.1 h.2.1 h.2.2)
      let rel (u v : Fin 4 × X) :=
        (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨
        (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨
        (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨
        (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2)
      let K := SimpleGraph.fromRel rel
      have directed (u v : Fin 4 × X)
          (h : rel u v) : G.Adj (label u) (label v) := by
        rcases u with ⟨i,x⟩
        rcases v with ⟨j,y⟩
        rcases h with h | h | h | h
        · obtain ⟨rfl,hj,rfl⟩ := h
          exact star j hj _
        · obtain ⟨rfl,rfl,rfl⟩ := h
          exact oneTwo x
        · obtain ⟨rfl,rfl,rfl⟩ := h
          exact twoThree x
        · obtain ⟨rfl,rfl,rfl⟩ := h
          exact threeOne x
      have edges {u v} (h : K.Adj u v) : G.Adj (label u) (label v) :=
        h.2.elim (directed u v) (fun h' => (directed v u h').symm)
      have neighbor (u : Fin 4 × X) (j : Fin 4) (hj : j ≠ u.1) :
          ∃ v, v.1 = j ∧ K.Adj u v := by
        obtain ⟨i,x⟩ := u
        fin_cases i <;> fin_cases j <;> first
        | exact (hj rfl).elim
        | (refine ⟨(_,x),rfl,?_⟩; solve | simp [K,rel])
        | (refine ⟨(_,p x),rfl,?_⟩; solve | simp [K,rel])
        | (refine ⟨(_,q x),rfl,?_⟩; solve | simp [K,rel])
        | (refine ⟨(_,r x),rfl,?_⟩; solve | simp [K,rel])
        | (refine ⟨(_,p.symm x),rfl,?_⟩; solve | simp [K,rel])
        | (refine ⟨(_,q.symm x),rfl,?_⟩; solve | simp [K,rel])
        | (refine ⟨(_,r.symm x),rfl,?_⟩; solve | simp [K,rel])
      have reverse {u v} (h : G.Adj (label u) (label v)) : K.Adj u v := by
        have diff : v.1 ≠ u.1 := by
          simpa only [color_label] using (proper h).symm
        obtain ⟨w,hw,edge⟩ := neighbor u v.1 diff
        have same : label w = label v :=
          (unique (label u) v.1 (by simpa only [color_label] using diff)).unique
            ⟨edges edge,(color_label w).trans hw⟩ ⟨h,color_label v⟩
        rwa [label.injective same] at edge
      let iso : K ≃g G := ⟨Equiv.ofBijective label ⟨label.injective,onto⟩, ⟨reverse,edges⟩⟩
      have nb : ¬ K.IsBipartite := fun h => nonbipartite (SimpleGraph.Colorable.of_hom iso.symm.toHom h)
      obtain ⟨k,hk,hc⟩ := nonAbelian X p q r nc (iso.connected_iff.mpr connected) nb
      exact solve hk (hc.trans ⟨⟨⟨label,fun h => edges h⟩,label.injective⟩⟩)
  · exact noColor V G connected cubic bridgeless nonbipartite colors

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H1_R1

