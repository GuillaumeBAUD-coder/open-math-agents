import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1
import Mathlib

/-!
# The connected bridgeless cubic case of Erdős–Gyárfás

The nonbipartite case remains H1. In the bipartite case, count incidences and apply Hall's
marriage theorem three times to split the edges into perfect matchings. Identify the two sides
along the first matching. The other two matchings now give permutations of the same set, and H2
asks only about pairs that do not commute.

For a commuting pair, the orbit of a vertex is the image of the abelian group ℤ² modulo its
stabilizer. Three distinct translations between two copies of an abelian group always give a
4-, 8-, or 16-cycle. The 16-step word 0101012010201212 closes before passing to the quotient;
if vertices on the same side coincide, their coordinate difference supplies a relation and one
of the shorter words applies. The case lemmas give the words and check the coordinate identities.

The parent bridge decomposition is due to @JamesSlash (PR #592). Ghaffari and Mostaghim,
Aequationes Math. 92 (2018), studied the Erdős–Gyárfás conjecture for dihedral and other Cayley
graphs. The three-translation argument here also allows noncyclic abelian groups.
-/

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1
open SimpleGraph

/-- Connected, bridgeless, cubic graphs with an odd cycle. -/
def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.Connected → (∀ x, G.degree x = 3) →
    (∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a,b)) → ¬ G.IsBipartite →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

/-- The normalized bipartite matching problem for noncommuting permutations. -/
def H2 : Prop :=
  ∀ (X : Type) [Fintype X] [Nonempty X] (p q : Equiv.Perm X),
    (∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) → ¬ Commute p q →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun a b : Bool × X =>
      a.1 = false ∧ b.1 = true ∧ (b.2 = a.2 ∨ b.2 = p a.2 ∨ b.2 = q a.2))

namespace HaarShort
open SimpleGraph

variable {A : Type*} [AddCommGroup A] (φ : (ℤ × ℤ) →+ A)
variable (G : SimpleGraph (Bool × A))

lemma forward_sound (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d))) (r : List (ℤ × ℤ)) (hr : ∀ x ∈ r, φ x = 0)
    (x y : (ℤ × ℤ)) (h : ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)).any (fun d => r.contains (y-x-d))) : G.Adj (false,φ x) (true,φ y) := by
  obtain ⟨d,hd,hm⟩ := List.any_eq_true.mp h
  have hz := hr _ (List.contains_iff_mem.mp hm)
  simp only [map_sub, sub_eq_zero] at hz
  rw [sub_eq_iff_eq_add.mp hz, add_comm]
  exact edges _ _ hd

lemma edge_sound (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d))) (r : List (ℤ × ℤ)) (hr : ∀ x ∈ r, φ x = 0)
    (x y : Bool × (ℤ × ℤ)) (h : (if x.1 = y.1 then false else if x.1 then ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)).any (fun d => r.contains (x.2-y.2-d)) else ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)).any (fun d => r.contains (y.2-x.2-d)))) : G.Adj ((x.1,φ x.2)) ((y.1,φ y.2)) := by
  obtain ⟨b,x⟩ := x; obtain ⟨c,y⟩ := y
  cases b <;> cases c <;> simp at h
  · exact forward_sound φ G edges r hr x y (by simpa using h)
  · exact (forward_sound φ G edges r hr y x (by simpa using h)).symm

lemma word (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d))) {n : ℕ} (hn : n=4 ∨ n=8 ∨ n=16)
    (p : Fin n → Bool × (ℤ × ℤ)) (rels bad : List (ℤ × ℤ)) (hr : ∀ v ∈ rels, φ v=0)
    (he : ∀ i j, (SimpleGraph.cycleGraph n).Adj i j → (if (p i).1 = (p j).1 then false else if (p i).1 then ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)).any (fun d => rels.contains ((p i).2-(p j).2-d)) else ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)).any (fun d => rels.contains ((p j).2-(p i).2-d))))
    (hd : ∀ i j, i < j → (p i).1=(p j).1 → (p i).2-(p j).2 ∈ bad)
    (branch : ∀ v ∈ bad, φ v=0 → (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G)) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  classical
  let f : SimpleGraph.cycleGraph n →g G := ⟨fun i => ((p i).1,φ (p i).2), fun {i j} h =>
    edge_sound φ G edges rels hr _ _ (he i j h)⟩
  by_cases inj : Function.Injective f
  · have hh : SimpleGraph.cycleGraph n ⊑ G := ⟨f.toCopy inj⟩
    rcases hn with rfl | rfl | rfl
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
    · exact Or.inr (Or.inr hh)
  · obtain ⟨i,j,heq,hne⟩ := Function.not_injective_iff.mp inj
    have go (a b : Fin n) (ab : a < b) (eq : f a = f b) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
      have e₁ := congrArg Prod.fst eq
      have e₂ := congrArg Prod.snd eq
      refine branch _ (hd a b ab e₁) ?_
      simpa [map_sub] using (sub_eq_zero.mpr (show φ (p a).2 = φ (p b).2 from e₂))
    rcases lt_or_gt_of_ne hne with h | h
    · exact go i j h heq
    · exact go j i h heq.symm

lemma sumZero (v w : (ℤ × ℤ)) (i j : ℤ) (hv : φ v=0) (hw : φ w=0) : φ (i • v + j • w)=0 := by rw [map_add, map_zsmul, map_zsmul, hv, hw, zsmul_zero, zsmul_zero, add_zero]

lemma relation {v w z : (ℤ × ℤ)} (hv : φ v = 0) (hw : φ w = 0) (i j : ℤ)
    (eqn : z = i • v + j • w) : φ z = 0 := by
  rw [eqn]; exact sumZero φ v w i j hv hw

/-- Each case name records the integer relation vectors as successive coordinate pairs. -/
theorem case_3_0_2_1
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (3,0)=0) (h1 : φ (2,1)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  exact False.elim (sep (1,-1) (by decide) (relation φ h0 h1 (1) (-1) (by decide)))

theorem case_1_0
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (1,0)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  exact False.elim (sep (1,0) (by decide) h0)

theorem case_1_0_0_1
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (1,0)=0) (h1 : φ (0,1)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  exact False.elim (sep (1,0) (by decide) h0)

theorem case_3_0_1_1
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (3,0)=0) (h1 : φ (1,1)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  apply word φ G edges (n := 4) (by decide)
    ![(false,(0,0)), (true,(0,0)), (false,(-1,0)), (true,(-1,0))]
    [(0,0), (-1,-1)] [(1,0)]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (map_zero φ)
    · exact (relation φ h1 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
  · decide
  · decide
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl
    intro h2
    exact case_1_0_0_1 φ G edges sep h2 (relation φ h1 h2 (1) (-1) (by decide))

theorem case_3_0_0_1
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (3,0)=0) (h1 : φ (0,1)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  exact False.elim (sep (0,1) (by decide) h1)

theorem case_3_0
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (3,0)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  apply word φ G edges (n := 8) (by decide)
    ![(false,(0,0)), (true,(0,0)), (false,(-1,0)), (true,(-1,0)), (false,(-2,0)), (true,(-2,1)),
      (false,(-3,1)), (true,(-3,1))]
    [(0,0), (-3,0)] [(1,-1), (1,0), (2,-1), (2,0), (3,-1)]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (map_zero φ)
    · exact (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
  · decide
  · decide
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · intro h1
      exact case_3_0_2_1 φ G edges sep h0 (relation φ h0 h1 (1) (-1) (by decide))
    · intro h1
      exact case_1_0 φ G edges sep h1
    · intro h1
      exact case_3_0_1_1 φ G edges sep h0 (relation φ h0 h1 (1) (-1) (by decide))
    · intro h1
      exact case_1_0 φ G edges sep (relation φ h0 h1 (1) (-1) (by decide))
    · intro h1
      exact case_3_0_0_1 φ G edges sep h0 (relation φ h0 h1 (1) (-1) (by decide))

theorem case_2_0_0_1
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (2,0)=0) (h1 : φ (0,1)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  exact False.elim (sep (0,1) (by decide) h1)

theorem case_4_0_2_1
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (4,0)=0) (h1 : φ (2,1)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  apply word φ G edges (n := 4) (by decide)
    ![(false,(0,0)), (true,(0,0)), (false,(-1,0)), (true,(-1,1))]
    [(0,0), (-2,1)] [(1,-1), (1,0)]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (map_zero φ)
    · exact (relation φ h0 h1 (-1) (1) (by decide))
  · decide
  · decide
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · intro h2
      exact case_1_0_0_1 φ G edges sep (relation φ (show φ (2,-1)=0 from (relation φ h0 h1 (1) (-1) (by decide))) h2 1 (-1) (by decide)) (relation φ (show φ (2,-1)=0 from (relation φ h0 h1 (1) (-1) (by decide))) h2 1 (-2) (by decide))
    · intro h2
      exact case_1_0_0_1 φ G edges sep h2 (relation φ (show φ (-2,1)=0 from (relation φ h0 h1 (-1) (1) (by decide))) h2 1 (2) (by decide))

theorem case_2_1
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (2,1)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  apply word φ G edges (n := 8) (by decide)
    ![(false,(0,0)), (true,(0,0)), (false,(-1,0)), (true,(-1,1)), (false,(-2,1)), (true,(-2,1)),
      (false,(-2,0)), (true,(-2,0))]
    [(0,0), (-2,-1)] [(0,1), (1,-1), (1,0), (1,1), (2,-1), (2,0)]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (map_zero φ)
    · exact (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
  · decide
  · decide
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · intro h1
      exact case_2_0_0_1 φ G edges sep (relation φ h0 h1 (1) (-1) (by decide)) h1
    · intro h1
      exact case_3_0_2_1 φ G edges sep (relation φ h0 h1 (1) (1) (by decide)) h0
    · intro h1
      exact case_1_0_0_1 φ G edges sep h1 (relation φ h0 h1 (1) (-2) (by decide))
    · intro h1
      exact case_1_0_0_1 φ G edges sep (relation φ h0 h1 (1) (-1) (by decide)) (relation φ h0 h1 (-1) (2) (by decide))
    · intro h1
      exact case_4_0_2_1 φ G edges sep (relation φ h0 h1 (1) (1) (by decide)) h0
    · intro h1
      exact case_2_0_0_1 φ G edges sep h1 (relation φ h0 h1 (1) (-1) (by decide))

theorem case_2_0
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (2,0)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  apply word φ G edges (n := 4) (by decide)
    ![(false,(0,0)), (true,(0,0)), (false,(-1,0)), (true,(-1,0))]
    [(0,0), (-2,0)] [(1,0)]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (map_zero φ)
    · exact (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
  · decide
  · decide
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl
    intro h1
    exact case_1_0 φ G edges sep h1

theorem case_m2_1
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (-2,1)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  apply word φ G edges (n := 4) (by decide)
    ![(false,(0,0)), (true,(0,0)), (false,(-1,0)), (true,(-1,1))]
    [(0,0), (-2,1)] [(1,-1), (1,0)]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (map_zero φ)
    · exact h0
  · decide
  · decide
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · intro h1
      exact case_1_0_0_1 φ G edges sep (relation φ h0 h1 (-1) (-1) (by decide)) (relation φ h0 h1 (-1) (-2) (by decide))
    · intro h1
      exact case_1_0_0_1 φ G edges sep h1 (relation φ h0 h1 (1) (2) (by decide))

theorem case_1_0_0_2
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (1,0)=0) (h1 : φ (0,2)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  exact False.elim (sep (1,0) (by decide) h0)

theorem case_2_0_1_2
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (2,0)=0) (h1 : φ (1,2)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  apply word φ G edges (n := 4) (by decide)
    ![(false,(0,0)), (true,(0,0)), (false,(-1,0)), (true,(-1,0))]
    [(0,0), (-2,0)] [(1,0)]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (map_zero φ)
    · exact (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
  · decide
  · decide
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl
    intro h2
    exact case_1_0_0_2 φ G edges sep h2 (relation φ (show φ (-1,2)=0 from (relation φ h0 h1 (-1) (1) (by decide))) h2 1 (1) (by decide))

theorem case_1_2
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (1,2)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  apply word φ G edges (n := 8) (by decide)
    ![(false,(0,0)), (true,(0,0)), (false,(-1,0)), (true,(-1,0)), (false,(-2,0)), (true,(-2,0)),
      (false,(-2,-1)), (true,(-1,-1))]
    [(0,0), (-1,-2)] [(-1,1), (0,1), (1,0), (1,1), (2,0), (2,1)]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (map_zero φ)
    · exact (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
  · decide
  · decide
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · intro h1
      exact case_3_0_2_1 φ G edges sep (relation φ h0 h1 (1) (-2) (by decide)) (relation φ h0 h1 (1) (-1) (by decide))
    · intro h1
      exact case_1_0_0_1 φ G edges sep (relation φ h0 h1 (1) (-2) (by decide)) h1
    · intro h1
      exact case_1_0_0_2 φ G edges sep h1 (relation φ h0 h1 (1) (-1) (by decide))
    · intro h1
      exact case_1_0_0_1 φ G edges sep (relation φ h0 h1 (-1) (2) (by decide)) (relation φ h0 h1 (1) (-1) (by decide))
    · intro h1
      exact case_2_0_1_2 φ G edges sep h1 h0
    · intro h1
      exact case_3_0_2_1 φ G edges sep (relation φ h0 h1 (-1) (2) (by decide)) h1

theorem case_1_1
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (1,1)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  apply word φ G edges (n := 4) (by decide)
    ![(false,(0,0)), (true,(0,0)), (false,(-1,0)), (true,(-1,0))]
    [(0,0), (-1,-1)] [(1,0)]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (map_zero φ)
    · exact (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
  · decide
  · decide
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl
    intro h1
    exact case_1_0_0_1 φ G edges sep h1 (relation φ h0 h1 (1) (-1) (by decide))

theorem case_m1_1
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (-1,1)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  exact False.elim (sep (1,-1) (by decide) (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide)))

theorem case_0_1
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (0,1)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  exact False.elim (sep (0,1) (by decide) h0)

theorem case_0_2
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (0,2)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  apply word φ G edges (n := 4) (by decide)
    ![(false,(0,0)), (true,(0,0)), (false,(0,-1)), (true,(0,-1))]
    [(0,0), (0,-2)] [(0,1)]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (map_zero φ)
    · exact (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
  · decide
  · decide
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl
    intro h1
    exact case_0_1 φ G edges sep h1

theorem case_m1_2
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (-1,2)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  apply word φ G edges (n := 4) (by decide)
    ![(false,(0,0)), (true,(0,0)), (false,(0,-1)), (true,(1,-1))]
    [(0,0), (1,-2)] [(-1,1), (0,1)]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (map_zero φ)
    · exact (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
  · decide
  · decide
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · intro h1
      exact case_1_0_0_1 φ G edges sep (relation φ h0 h1 (1) (-2) (by decide)) (relation φ h0 h1 (1) (-1) (by decide))
    · intro h1
      exact case_1_0_0_1 φ G edges sep (relation φ h0 h1 (-1) (2) (by decide)) h1

theorem case_m2_2
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (-2,2)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  apply word φ G edges (n := 4) (by decide)
    ![(false,(0,0)), (true,(1,0)), (false,(1,-1)), (true,(2,-1))]
    [(0,0), (2,-2)] [(-1,1)]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (map_zero φ)
    · exact (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
  · decide
  · decide
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl
    intro h1
    exact case_m1_1 φ G edges sep h1

theorem case_2_0_1_1
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (2,0)=0) (h1 : φ (1,1)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  exact False.elim (sep (1,-1) (by decide) (relation φ h0 h1 (1) (-1) (by decide)))

theorem case_4_0_1_1
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (4,0)=0) (h1 : φ (1,1)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  apply word φ G edges (n := 4) (by decide)
    ![(false,(0,0)), (true,(0,0)), (false,(-1,0)), (true,(-1,0))]
    [(0,0), (-1,-1)] [(1,0)]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (map_zero φ)
    · exact (relation φ h1 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
  · decide
  · decide
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl
    intro h2
    exact case_1_0_0_1 φ G edges sep h2 (relation φ h1 h2 (1) (-1) (by decide))

theorem case_m3_1
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)
    (h0 : φ (-3,1)=0) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  apply word φ G edges (n := 8) (by decide)
    ![(false,(0,0)), (true,(0,0)), (false,(-1,0)), (true,(-1,1)), (false,(-2,1)), (true,(-2,2)),
      (false,(-3,2)), (true,(-3,2))]
    [(0,0), (-3,1)] [(1,-1), (1,0), (2,-2), (2,-1), (3,-2)]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (map_zero φ)
    · exact h0
  · decide
  · decide
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · intro h1
      exact case_2_0_1_1 φ G edges sep (relation φ h0 h1 (-1) (-1) (by decide)) (relation φ h0 h1 (-1) (-2) (by decide))
    · intro h1
      exact case_1_0_0_1 φ G edges sep h1 (relation φ h0 h1 (1) (3) (by decide))
    · intro h1
      exact case_4_0_1_1 φ G edges sep (relation φ h0 h1 (-2) (-1) (by decide)) (relation φ h0 h1 (-1) (-1) (by decide))
    · intro h1
      exact case_1_0_0_1 φ G edges sep (relation φ h0 h1 (-1) (-1) (by decide)) (relation φ h0 h1 (-2) (-3) (by decide))
    · intro h1
      exact case_3_0_0_1 φ G edges sep (relation φ h0 h1 (-2) (-1) (by decide)) (relation φ h0 h1 (-1) (-1) (by decide))

theorem case_free
    (edges : (∀ (x : A) (d : (ℤ × ℤ)), d ∈ ([(0,0), (1,0), (0,1)] : List (ℤ × ℤ)) → G.Adj (false,x) (true,x + φ d)))
    (sep : ∀ v ∈ ([(1,0),(0,1),(1,-1)] : List (ℤ × ℤ)), φ v ≠ 0)  :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  apply word φ G edges (n := 16) (by decide)
    ![(false,(0,0)), (true,(0,0)), (false,(-1,0)), (true,(-1,0)), (false,(-2,0)), (true,(-2,0)),
      (false,(-3,0)), (true,(-3,1)), (false,(-3,1)), (true,(-2,1)), (false,(-2,1)), (true,(-2,2)), (false,(-2,2)), (true,(-1,2)), (false,(-1,1)), (true,(0,1))]
    [(0,0)] [(-3,0), (-2,-1), (-2,0), (-2,1), (-1,-2), (-1,-1), (-1,0), (-1,1), (0,-2), (0,-1), (1,-2), (1,-1), (1,0), (2,-2), (2,-1), (2,0), (3,-1), (3,0)]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl
    exact (map_zero φ)
  · decide
  · decide
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro h0
      exact case_3_0 φ G edges sep (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
    · intro h0
      exact case_2_1 φ G edges sep (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
    · intro h0
      exact case_2_0 φ G edges sep (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
    · intro h0
      exact case_m2_1 φ G edges sep h0
    · intro h0
      exact case_1_2 φ G edges sep (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
    · intro h0
      exact case_1_1 φ G edges sep (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
    · intro h0
      exact case_1_0 φ G edges sep (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
    · intro h0
      exact case_m1_1 φ G edges sep h0
    · intro h0
      exact case_0_2 φ G edges sep (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
    · intro h0
      exact case_0_1 φ G edges sep (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
    · intro h0
      exact case_m1_2 φ G edges sep (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
    · intro h0
      exact case_m1_1 φ G edges sep (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
    · intro h0
      exact case_1_0 φ G edges sep h0
    · intro h0
      exact case_m2_2 φ G edges sep (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
    · intro h0
      exact case_m2_1 φ G edges sep (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
    · intro h0
      exact case_2_0 φ G edges sep h0
    · intro h0
      exact case_m3_1 φ G edges sep (relation φ h0 (map_zero φ : φ (0:(ℤ × ℤ)) = 0) (-1) (0) (by decide))
    · intro h0
      exact case_3_0 φ G edges sep h0

/-- An abelian Haar graph with three distinct shifts contains a 4-, 8-, or
16-cycle. Translate the right part to normalize one of the shifts to zero. -/
theorem haar_short_cycle (G : SimpleGraph (Bool × A)) (u v : A)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (h0 : ∀ x, G.Adj (false, x) (true, x))
    (h1 : ∀ x, G.Adj (false, x) (true, x + u))
    (h2 : ∀ x, G.Adj (false, x) (true, x + v)) :
    SimpleGraph.cycleGraph 4 ⊑ G ∨ SimpleGraph.cycleGraph 8 ⊑ G ∨ SimpleGraph.cycleGraph 16 ⊑ G := by
  let ψ : (ℤ × ℤ) →+ A := {
    toFun := fun w => w.1 • u + w.2 • v
    map_zero' := by simp
    map_add' := by intro x y; simp [add_zsmul]; abel }
  apply case_free ψ G
  · intro x d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · simpa [ψ] using h0 x
    · simpa [ψ] using h1 x
    · simpa [ψ] using h2 x
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · simpa [ψ] using hu
    · simpa [ψ] using hv
    · simpa [ψ, ← sub_eq_add_neg] using (sub_ne_zero.mpr huv)


end HaarShort
namespace HaarTransfer
open SimpleGraph

/-- Choose one orbit of the commuting relative permutations of two matchings.
The action on that orbit factors faithfully through an abelian quotient of ℤ². -/
theorem commuting_matchings {V X : Type*} (G : SimpleGraph V) (s t : Equiv.Perm X)
    (comm : Commute s t) (z : X) (hs : s z ≠ z) (ht : t z ≠ z) (hst : s z ≠ t z)
    (f : (Bool × X) ↪ V)
    (h0 : ∀ x, G.Adj (f (false,x)) (f (true,x)))
    (h1 : ∀ x, G.Adj (f (false,x)) (f (true,s x)))
    (h2 : ∀ x, G.Adj (f (false,x)) (f (true,t x))) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  let act (a : ℤ × ℤ) : Equiv.Perm X := s ^ a.1 * t ^ a.2
  have add (a b : ℤ × ℤ) : act (a+b) = act a * act b := by
    change s ^ (a.1+b.1) * t ^ (a.2+b.2) = (s ^ a.1 * t ^ a.2) * (s ^ b.1 * t ^ b.2)
    rw [zpow_add, zpow_add]
    simp only [mul_assoc]
    rw [← mul_assoc (s ^ b.1), (comm.zpow_zpow b.1 a.2).eq, mul_assoc]
  letI : AddAction (ℤ × ℤ) X := {
    vadd a x := act a x
    zero_vadd x := by change act 0 x = x; simp [act]
    add_vadd a b x := congrArg (fun p : Equiv.Perm X => p x) (add a b) }
  let K := AddAction.stabilizer (ℤ × ℤ) z
  let e : ((ℤ × ℤ) ⧸ K) ↪ X := ⟨AddAction.ofQuotientStabilizer _ z, AddAction.injective_ofQuotientStabilizer _ z⟩
  let u : (ℤ × ℤ) ⧸ K := QuotientAddGroup.mk (1,0)
  let v : (ℤ × ℤ) ⧸ K := QuotientAddGroup.mk (0,1)
  have zero : e 0 = z := by change act 0 z = z; simp [act]
  have eU (x : (ℤ × ℤ) ⧸ K) : e (x+u) = s (e x) := by
    induction x using Quotient.inductionOn' with | _ a =>
      change act (a+(1,0)) z = s (act a z)
      rw [add_comm a, add]; simp [act, Equiv.Perm.mul_apply]
  have eV (x : (ℤ × ℤ) ⧸ K) : e (x+v) = t (e x) := by
    induction x using Quotient.inductionOn' with | _ a =>
      change act (a+(0,1)) z = t (act a z)
      rw [add_comm a, add]; simp [act, Equiv.Perm.mul_apply]
  have eu : e u = s z := by simpa [zero] using eU 0
  have ev : e v = t z := by simpa [zero] using eV 0
  let j := (Function.Embedding.refl Bool |>.prodMap e).trans f
  let J := G.comap j
  have sub : J ⊑ G := (isContained_iff_exists_le_comap).mpr ⟨j, le_rfl⟩
  have small := HaarShort.haar_short_cycle J u v
    (fun h => hs (eu.symm.trans ((congrArg e h).trans zero)))
    (fun h => ht (ev.symm.trans ((congrArg e h).trans zero)))
    (fun h => hst (eu.symm.trans ((congrArg e h).trans ev)))
    (fun x => h0 (e x))
    (fun x => by change G.Adj _ (f (true, e (x+u))); rw [eU]; exact h1 _)
    (fun x => by change G.Adj _ (f (true, e (x+v))); rw [eV]; exact h2 _)
  rcases small with h | h | h
  · exact Or.inl (h.trans sub)
  · exact Or.inr (Or.inl (h.trans sub))
  · exact Or.inr (Or.inr (h.trans sub))

end HaarTransfer

namespace RegularMatchings
open Finset

/-- Hall's condition follows by counting incidences between any rows and their neighbors. -/
lemma regularHall {X Y : Type*} [Fintype X] [Fintype Y] (R : X → Y → Prop) [DecidableRel R]
    {d : ℕ} (hd : 0 < d) (row : ∀ x, (univ.filter (R x)).card = d)
    (col : ∀ y, (univ.filter (fun x => R x y)).card = d) : ∃ f : X → Y, Function.Injective f ∧ ∀ x, R x (f x) := by
  classical
  let B := fun x => univ.filter (R x)
  suffices hall : ∀ s : Finset X, s.card ≤ (s.biUnion B).card by
    obtain ⟨f,hinj,hf⟩ := (all_card_le_biUnion_card_iff_exists_injective B).mp hall
    exact ⟨f,hinj,fun x => (mem_filter.mp (hf x)).2⟩
  intro s
  have total := sum_card_eq_sum_biUnion_card B s
  have le : ∀ y, (s.filter fun x => y ∈ B x).card ≤ d := by
    intro y
    rw [← col y]
    apply card_le_card
    intro x hx
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp (mem_filter.mp hx).2).2⟩
  have bound := sum_le_sum (s := s.biUnion B) (fun y _ => le y)
  have hrow (x : X) : (B x).card = d := row x
  simp only [hrow, sum_const, smul_eq_mul] at total
  have same (y : Y) : (univ.filter fun x => x ∈ s ∧ y ∈ B x) = s.filter (fun x => y ∈ B x) := by
    ext; simp
  simp_rw [same] at total
  rw [sum_const, smul_eq_mul, ← total] at bound
  exact Nat.le_of_mul_le_mul_right bound hd

lemma regularEquiv {X Y : Type*} [Fintype X] [Fintype Y] (R : X → Y → Prop) [DecidableRel R]
    {d : ℕ} (hd : 0 < d) (row : ∀ x, (univ.filter (R x)).card = d)
    (col : ∀ y, (univ.filter (fun x => R x y)).card = d) : ∃ f : X ≃ Y, ∀ x, R x (f x) := by
  obtain ⟨f, hf, hR⟩ := regularHall R hd row col
  obtain ⟨g, hg, _⟩ := regularHall (fun y x => R x y) hd col row
  have hcard := Nat.le_antisymm (Fintype.card_le_of_injective f hf) (Fintype.card_le_of_injective g hg)
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩),hR⟩

lemma removeMatching {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (R : X → Y → Prop) [DecidableRel R] (f : X ≃ Y) (hf : ∀ x, R x (f x))
    (d : ℕ) (row : ∀ x, (univ.filter (R x)).card = d+1)
    (col : ∀ y, (univ.filter (fun x => R x y)).card = d+1) :
    (∀ x, (univ.filter fun y => R x y ∧ y ≠ f x).card = d) ∧
    (∀ y, (univ.filter fun x => R x y ∧ y ≠ f x).card = d) := by
  constructor
  · intro x
    have h : (univ.filter fun y => R x y ∧ y ≠ f x) = (univ.filter (R x)).erase (f x) := by
      ext; simp [and_comm]
    rw [h,card_erase_of_mem (mem_filter.mpr ⟨mem_univ _,hf x⟩),row]; omega
  · intro y
    have h : (univ.filter fun x => R x y ∧ y ≠ f x) = (univ.filter fun x => R x y).erase (f.symm y) := by
      ext x; simp [ne_comm, Equiv.eq_symm_apply, and_comm]
    rw [h,card_erase_of_mem (mem_filter.mpr ⟨mem_univ _,by simpa using hf (f.symm y)⟩),col]; omega

lemma cubicMatchings {X Y : Type*} [Fintype X] [Fintype Y]
    (R : X → Y → Prop) [DecidableRel R] (row : ∀ x, (univ.filter (R x)).card = 3)
    (col : ∀ y, (univ.filter (fun x => R x y)).card = 3) :
    ∃ f g h : X ≃ Y, ∀ x, R x (f x) ∧ R x (g x) ∧ R x (h x) ∧
      g x ≠ f x ∧ h x ≠ f x ∧ h x ≠ g x := by
  classical
  obtain ⟨f,hf⟩ := regularEquiv R (by decide : 0<3) row col
  obtain ⟨r,c⟩ := removeMatching R f hf 2 row col
  let S := fun x y => R x y ∧ y ≠ f x
  obtain ⟨g,hg⟩ := regularEquiv S (by decide : 0<2) r c
  obtain ⟨r',c'⟩ := removeMatching S g hg 1 r c
  obtain ⟨h,hh⟩ := regularEquiv (fun x y => S x y ∧ y ≠ g x) (by decide : 0<1) r' c'
  exact ⟨f,g,h,fun x => ⟨hf x,(hg x).1,(hh x).1.1,(hg x).2,(hh x).1.2,(hh x).2⟩⟩

end RegularMatchings
namespace RegularMatchings
open SimpleGraph Finset

lemma countSide {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) [Fintype S] (x : V) (h : ∀ y, G.Adj x y → y ∈ S) :
    (univ.filter (fun y : S => G.Adj x y.val)).card = G.degree x := by
  rw [← card_neighborFinset_eq_degree]
  apply card_bij (fun y _ => y.val)
  · intro y hy; exact (G.mem_neighborFinset x y).mpr (mem_filter.mp hy).2
  · intro a _ b _ e; exact Subtype.ext e
  · intro y hy; have adj := (G.mem_neighborFinset x y).mp hy
    exact ⟨⟨y,h y adj⟩,mem_filter.mpr ⟨mem_univ _,adj⟩,rfl⟩

lemma present {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (bip : G.IsBipartite) (deg : ∀ v, G.degree v=3) :
    ∃ (X : Type) (_ : Fintype X) (_ : Nonempty X) (f : Bool × X ↪ V) (p q : Equiv.Perm X),
      ∀ x, (p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) ∧
      G.Adj (f (false,x)) (f (true,x)) ∧ G.Adj (f (false,x)) (f (true,p x)) ∧
      G.Adj (f (false,x)) (f (true,q x)) := by
  classical
  obtain ⟨L,R,b⟩ := bip.exists_isBipartiteWith
  obtain ⟨a⟩ := ‹Nonempty V›
  have pos : 0 < (G.neighborFinset a).card := by rw [card_neighborFinset_eq_degree,deg]; decide
  obtain ⟨c,hc⟩ := card_pos.mp pos
  have left : Nonempty L := by
    rcases b.mem_of_adj ((G.mem_neighborFinset a c).mp hc) with h|h
    · exact ⟨⟨a,h.1⟩⟩
    · exact ⟨⟨c,h.2⟩⟩
  let r := fun (x : L) (y : R) => G.Adj x.val y.val
  have row (x : L) : (univ.filter (r x)).card = 3 :=
    (countSide G R x.val fun _ adj => b.mem_of_mem_adj x.property adj).trans (deg x.val)
  have col (y : R) : (univ.filter (fun x => r x y)).card = 3 := by
    have t := countSide G L y.val (fun _ adj => b.symm.mem_of_mem_adj y.property adj)
    simpa only [r, G.adj_comm y.val] using t.trans (deg y.val)
  obtain ⟨a,d,e,he⟩ := cubicMatchings r row col
  let f : Bool × L → V := fun z => if z.1 then (a z.2).val else z.2.val
  have inj : Function.Injective f := by
    rintro ⟨i,x⟩ ⟨j,y⟩ hij
    cases i <;> cases j <;> simp [f] at hij ⊢
    · exact Subtype.ext hij
    · exact (Set.disjoint_left.mp b.disjoint x.property (hij ▸ (a y).property)).elim
    · exact (Set.disjoint_left.mp b.disjoint y.property (hij ▸ (a x).property)).elim
    · exact a.injective (Subtype.ext hij)
  refine ⟨L,inferInstance,left,⟨f,inj⟩,d.trans a.symm,e.trans a.symm,?_⟩
  intro x
  obtain ⟨ha,hd,he',hda,hea,hed⟩ := he x
  simp only [Function.Embedding.coeFn_mk, Equiv.trans_apply, f, Bool.false_eq_true, ↓reduceIte,
    Equiv.apply_symm_apply]
  exact ⟨⟨fun h => hda (a.symm_apply_eq.mp h), fun h => hea (a.symm_apply_eq.mp h),
    fun h => hed (a.symm.injective h).symm⟩,ha,hd,he'⟩

end RegularMatchings
theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1.H1 := by
  intro nonbip noncomm V G _ _ conn deg bridge
  classical
  by_cases bip : G.IsBipartite
  · letI : Nonempty V := conn.nonempty
    obtain ⟨X,fin,inh,f,p,q,h⟩ := RegularMatchings.present G bip deg
    letI := fin
    letI := inh
    have solve (k : ℕ) (hk : 2 ≤ k) (hc : cycleGraph (2^k) ⊑ G) :
        ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k := by
      obtain ⟨v,c,hc',hl⟩ := (cycleGraph_isContained_iff (by calc
        2 < 2^2 := by decide
        _ ≤ 2^k := Nat.pow_le_pow_right (by decide) hk)).mp hc
      exact ⟨k,v,c,hk,hc',hl⟩
    by_cases comm : Commute p q
    · let z := Classical.choice inh
      rcases HaarTransfer.commuting_matchings G p q comm z (h z).1.1 (h z).1.2.1 (h z).1.2.2
        f (fun x => (h x).2.1) (fun x => (h x).2.2.1) (fun x => (h x).2.2.2) with a | a | a
      · exact solve 2 (by decide) a
      · exact solve 3 (by decide) a
      · exact solve 4 (by decide) a
    · obtain ⟨k,hk,hkG⟩ := noncomm X p q (fun x => (h x).1) comm
      apply solve k hk (hkG.trans _)
      refine isContained_iff_exists_le_comap.mpr ⟨f,?_⟩
      have forward (a b : Bool × X) (ha : a.1 = false) (hb : b.1 = true)
          (edge : b.2 = a.2 ∨ b.2 = p a.2 ∨ b.2 = q a.2) : G.Adj (f a) (f b) := by
        obtain ⟨i,x⟩ := a; obtain ⟨j,y⟩ := b
        subst_vars
        rcases edge with rfl | rfl | rfl
        · exact (h _).2.1
        · exact (h x).2.2.1
        · exact (h x).2.2.2
      intro a b edge
      rcases edge.2 with ⟨ha,hb,e⟩ | ⟨hb,ha,e⟩
      · exact forward a b ha hb e
      · exact (forward b a hb ha e).symm
  · exact nonbip V G conn deg bridge bip

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1
