import FormalConjectures.ErdosProblems.«147»

/-!
# Erdős 147, variante cubique : réduction R1

Traduction de Janzer, *Disproof of a conjecture of Erdős and Simonovits on the Turán number of
graphs with minimum degree 3* (arXiv 2109.06110), théorème 1.1 : pour tout `ε > 0`, il existe un
graphe biparti 3-régulier `H` avec `ex(n, H) = O(n^(4/3+ε))`. Le graphe est `H_(k,ℓ)` (définition
1.2), et le théorème 1.3 se prouve en trois étapes : régularisation, ensemble bon de `8k`-cycles,
ensemble agréable, copie de `H_(k,ℓ)`.

Tout est prouvé ici sauf trois lemmes de l'article, pris pour hypothèses :

- `H1` : lemme 2.14 (peu de 4-cycles : un ensemble bon de `8k`-cycles existe) ;
- `H2` : lemme 2.15 (beaucoup de 4-cycles : idem) ;
- `H3` : lemme 2.5 (cycle homomorphe sans conflit), sous forme asymptotique.

Prouvés dans ce fichier : `H_(k,ℓ)` biparti et 3-régulier, la régularisation (variante du
lemme 2.9, sans le lemme d'Erdős–Simonovits), le nettoyage des 4-cycles (lemme 2.10), le passage
d'un ensemble bon à un ensemble agréable (lemme 2.12), l'étape 3 (lemme 2.13) depuis `H3`,
l'étape 1 depuis `H1` et `H2`, le théorème 1.3 et le passage à `O(n^(4/3+ε))`.

Les 4-cycles sont comptés étiquetés `(a, b, c, d)` : chaque copie de `C₄` en donne 8, d'où les
facteurs 8 de `H1` et `H2` devant les bornes de l'article.
-/

-- Credit: @iLc0

open SimpleGraph Finset Filter Asymptotics
open scoped Classical

namespace OMA.R_Erdos147_erdos_147_variants_cubic_R1

/-- Lemme 2.14 de Janzer (peu de 4-cycles). L'hypothèse `ε < 1/6`, absente de l'article, affaiblit
l'énoncé. `c4` est l'ensemble des 4-cycles étiquetés, `nxt` la position suivante modulo `8k` ; la
conclusion est la définition 2.11 (ensemble `n^(-ε/2)`-bon non vide de `8k`-cycles). -/
def H1 : Prop :=
  ∀ ε K : ℝ, 0 < ε → ε < 1 / 6 → 0 < K → ∀ k : ℕ, 1 / ε ≤ k → ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        let c4 : Finset (Fin n × Fin n × Fin n × Fin n) := univ.filter fun t =>
          G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2.1 ∧ G.Adj t.2.2.1 t.2.2.2 ∧ G.Adj t.2.2.2 t.1 ∧
            t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2
        let nxt : Fin (8 * k) → Fin (8 * k) := fun i => ⟨(i.val + 1) % (8 * k), Nat.mod_lt _ i.pos⟩
        (n : ℝ) ^ (4 / 3 + ε) / 6 ≤ #G.edgeFinset →
        (∀ v, (G.degree v : ℝ) ≤ K * (n : ℝ) ^ (1 / 3 + ε)) →
        (∀ e ∈ G.edgeFinset, (#(c4.filter fun t => e = s(t.1, t.2.1) ∨ e = s(t.2.1, t.2.2.1) ∨
            e = s(t.2.2.1, t.2.2.2) ∨ e = s(t.2.2.2, t.1)) : ℝ) ≤ 8 * (n : ℝ) ^ (1 / 3 + 2 * ε)) →
        ∃ C : Finset (Fin (8 * k) → Fin n), C.Nonempty ∧ ∃ s : ℝ, 0 < s ∧
          (∀ x ∈ C, Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))) ∧
          (∀ y ∈ C, ∀ i, (#(C.filter fun x => ∀ j, j ≠ i → x j = y j) : ℝ) ≤ s) ∧
          ∀ i : Fin (8 * k), ∃ P : Finset (Fin (8 * k) → Fin n),
            (#P : ℝ) ≤ (n : ℝ) ^ (-(ε / 2)) * #C / (16 * k * s) ∧
            ∀ x ∈ C, ∃ y ∈ P, ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j

/-- Lemme 2.15 de Janzer (beaucoup de 4-cycles) : `#c4 = 8 q` où `q` compte les copies de `C₄`. -/
def H2 : Prop :=
  ∀ ε K : ℝ, 0 < ε → ε < 1 / 6 → 0 < K → ∀ k : ℕ, 1 / ε ≤ k → ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        let c4 : Finset (Fin n × Fin n × Fin n × Fin n) := univ.filter fun t =>
          G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2.1 ∧ G.Adj t.2.2.1 t.2.2.2 ∧ G.Adj t.2.2.2 t.1 ∧
            t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2
        let nxt : Fin (8 * k) → Fin (8 * k) := fun i => ⟨(i.val + 1) % (8 * k), Nat.mod_lt _ i.pos⟩
        (∀ v, (G.degree v : ℝ) ≤ K * (n : ℝ) ^ (1 / 3 + ε)) →
        8 * (n : ℝ) ^ (5 / 3 + 3 * ε) / (96 * Real.log n) ≤ #c4 →
        (∀ e ∈ G.edgeFinset, (#(c4.filter fun t => e = s(t.1, t.2.1) ∨ e = s(t.2.1, t.2.2.1) ∨
            e = s(t.2.2.1, t.2.2.2) ∨ e = s(t.2.2.2, t.1)) : ℝ) ≤
            96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * #c4) →
        ∃ C : Finset (Fin (8 * k) → Fin n), C.Nonempty ∧ ∃ s : ℝ, 0 < s ∧
          (∀ x ∈ C, Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))) ∧
          (∀ y ∈ C, ∀ i, (#(C.filter fun x => ∀ j, j ≠ i → x j = y j) : ℝ) ≤ s) ∧
          ∀ i : Fin (8 * k), ∃ P : Finset (Fin (8 * k) → Fin n),
            (#P : ℝ) ≤ (n : ℝ) ^ (-(ε / 2)) * #C / (16 * k * s) ∧
            ∀ x ∈ C, ∃ y ∈ P, ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j

/-- Lemme 2.5 de Janzer (arXiv 2109.06110), sous forme asymptotique. -/
def H3 : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ θ : ℝ, 0 < θ → ∀ᶠ N : ℕ in atTop,
    ∀ (W : Type) [Fintype W], Fintype.card W = N →
    ∀ (G : SimpleGraph W) (r : W → W → Prop), (∀ u w, r u w → r w u) →
    G.edgeFinset.Nonempty →
    (∀ u v, (#((G.neighborFinset v).filter (r u)) : ℝ) ≤
        (N : ℝ) ^ (-(1 / (k : ℝ) + θ)) * G.degree v) →
    ∃ x : Fin (2 * k) → W,
      (∀ i, G.Adj (x i) (x ⟨(i.val + 1) % (2 * k), Nat.mod_lt _ i.pos⟩)) ∧
      ∀ i j, i ≠ j → ¬ r (x i) (x j)

end OMA.R_Erdos147_erdos_147_variants_cubic_R1

namespace E147Step3

open OMA.R_Erdos147_erdos_147_variants_cubic_R1

/- Les positions directes et réfléchies placent chacune des deux colonnes dans un cycle. -/
private theorem s5_row_pos :
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    ∀ {k} (b) (j : Fin (4*k)), row (pos b j) = j := by
  intro phase pos row k b j
  apply Fin.ext
  have := j.isLt
  simp only [row, pos]
  split_ifs <;> omega

private theorem s5_side_pos :
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    ∀ {k} (b) (j : Fin (4*k)), side (pos b j) = b := by
  intro phase pos row side
  have row_pos : ∀ {k} (b) (j : Fin (4*k)), row (pos b j) = j := @s5_row_pos
  intro k b j
  simp only [side, row_pos]
  have := j.isLt
  cases b <;> cases e : phase j <;> simp [pos, e] <;> omega

private theorem s5_pos_side :
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    ∀ {k} (p : Fin (8*k)), pos (side p) (row p) = p := by
  intro phase pos row side k p
  apply Fin.ext
  have := p.isLt
  by_cases h : p.val < 4*k <;> cases e : phase (row p) <;>
    simp [pos, side, h, row] <;> omega

private theorem s5_pack_pos :
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
      w (side p) (row p)
    ∀ {V : Type} {k} (w : Bool → Fin (4*k) → V) (b j), pack w (pos b j) = w b j := by
  intro phase pos row side pack
  have row_pos : ∀ {k} (b) (j : Fin (4*k)), row (pos b j) = j := @s5_row_pos
  have side_pos : ∀ {k} (b) (j : Fin (4*k)), side (pos b j) = b := @s5_side_pos
  intro V k w b j
  simp [pack, side_pos, row_pos]

private theorem s5_nxt_val {L} (p : Fin L) :
    (p.val+1) % L = if p.val+1 < L then p.val+1 else 0 := by
  have hp := p.isLt
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [show p.val+1 = L by omega, Nat.mod_self]

private theorem s5_near_val :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let near {L} (p q : Fin L) : Prop := nxt p = q ∨ nxt q = p
    ∀ {L} (p q : Fin L), near p q ↔ (if p.val + 1 < L then p.val+1 else 0) = q.val ∨
      (if q.val + 1 < L then q.val+1 else 0) = p.val := by
  intro nxt near L p q
  simp only [near, Fin.ext_iff, nxt, s5_nxt_val]

private theorem s5_near_inner :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let near {L} (p q : Fin L) : Prop := nxt p = q ∨ nxt q = p
    ∀ {k} (b : Bool) (i j : Fin (4*k)) (_ : i.val+1=j.val)
    (_ : i.val % 2 = 0), near (pos b i) (pos b j) := by
  intro nxt phase pos near
  have near_val : ∀ {L} (p q : Fin L), near p q ↔ (if p.val + 1 < L then p.val+1 else 0) = q.val ∨
      (if q.val + 1 < L then q.val+1 else 0) = p.val := @s5_near_val
  intro k b i j h he
  have hi := i.isLt
  have hj := j.isLt
  cases b <;> by_cases ei : i.val / 2 % 2 = 1 <;> by_cases ej : j.val / 2 % 2 = 1 <;>
    simp [near_val, pos, phase, ei, ej] <;> split_ifs <;> omega

private theorem s5_near_cross :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let near {L} (p q : Fin L) : Prop := nxt p = q ∨ nxt q = p
    ∀ {k} (b : Bool) (i j : Fin (4*k)) (_ : i.val+1=j.val)
    (_ : i.val % 2 ≠ 0), near (pos b i) (pos (!b) j) := by
  intro nxt phase pos near
  have near_val : ∀ {L} (p q : Fin L), near p q ↔ (if p.val + 1 < L then p.val+1 else 0) = q.val ∨
      (if q.val + 1 < L then q.val+1 else 0) = p.val := @s5_near_val
  intro k b i j h he
  have hi := i.isLt
  have hj := j.isLt
  cases b <;> by_cases ei : i.val / 2 % 2 = 1 <;> by_cases ej : j.val / 2 % 2 = 1 <;>
    simp [near_val, pos, phase, ei, ej] <;> split_ifs <;> omega

private theorem s5_near_end :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let near {L} (p q : Fin L) : Prop := nxt p = q ∨ nxt q = p
    ∀ {k} (i : Fin (4*k)) (_ : i.val = 0 ∨ i.val+1=4*k), near (pos false i) (pos true i) := by
  intro nxt phase pos near
  have near_val : ∀ {L} (p q : Fin L), near p q ↔ (if p.val + 1 < L then p.val+1 else 0) = q.val ∨
      (if q.val + 1 < L then q.val+1 else 0) = p.val := @s5_near_val
  intro k i he
  have hi := i.isLt
  by_cases ei : i.val / 2 % 2 = 1 <;> simp [near_val, pos, phase, ei] <;> split_ifs <;> omega

/- Chaque coordonnée appartient à deux positions consécutives de sa propre colonne. -/
private theorem s5_nice_positions :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let _near {L} (p q : Fin L) : Prop := nxt p = q ∨ nxt q = p
    ∀ {k} (b : Bool) (j : Fin (4*k)), ∃ i : Fin (8*k),
    (pos b j = nxt i ∨ pos b j = nxt (nxt i)) ∧ side (nxt i) = b ∧ side (nxt (nxt i)) = b := by
  intro nxt phase pos row side near
  have side_pos : ∀ {k} (b) (j : Fin (4*k)), side (pos b j) = b := @s5_side_pos
  have near_inner : ∀ {k} (b : Bool) (i j : Fin (4*k)) (_ : i.val+1=j.val)
    (_ : i.val % 2 = 0), near (pos b i) (pos b j) := @s5_near_inner
  intro k b j
  have hp : ∀ p : Fin (8*k), ∃ i, nxt i = p := by
    intro p
    refine ⟨⟨if p.val = 0 then 8*k-1 else p.val-1, by have := p.isLt; split_ifs <;> omega⟩, ?_⟩
    apply Fin.ext
    have he (t : Fin (8*k)) : (nxt t).val = if t.val+1 < 8*k then t.val+1 else 0 := s5_nxt_val t
    rw [he]
    have := p.isLt
    simp only
    split_ifs <;> omega
  have hj := j.isLt
  let a : Fin (4*k) := ⟨2*(j.val/2), by omega⟩
  let d : Fin (4*k) := ⟨2*(j.val/2)+1, by omega⟩
  have hjad : j = a ∨ j = d := by
    simp only [Fin.ext_iff, a, d]
    omega
  have had := near_inner b a d (by rfl) (by simp [a])
  obtain ⟨p,q,he,hs,ht,hj'⟩ : ∃ p q, nxt p = q ∧ side p = b ∧ side q = b ∧
      (pos b j = p ∨ pos b j = q) := by
    rcases had with e | e
    · refine ⟨pos b a, pos b d, e, side_pos .., side_pos .., ?_⟩
      exact hjad.imp (congrArg (pos b)) (congrArg (pos b))
    · refine ⟨pos b d, pos b a, e, side_pos .., side_pos .., ?_⟩
      exact hjad.symm.imp (congrArg (pos b)) (congrArg (pos b))
  obtain ⟨i,hi⟩ := hp p
  exact ⟨i, by simpa only [hi,he] using hj', by simpa only [hi] using hs,
    by simpa only [hi,he] using ht⟩

private theorem s5_pack_inj :
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let _pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
      w (side p) (row p)
    let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
      if t = b then z else y
    ∀ {k n} (b) (y : Fin (4*k) → Fin n), Function.Injective (fun z => pack (mix b y z)) := by
  intro phase pos row side pack mix
  have pack_pos : ∀ {V : Type} {k} (w : Bool → Fin (4*k) → V) (b j), pack w (pos b j) = w b j := @s5_pack_pos
  intro k n b y z w h
  funext j
  simpa [pack_pos, mix] using congrFun h (pos b j)

private theorem s5_sum_fibers_bound {U K : Type*} [Fintype K] [DecidableEq K] (A : Finset U)
    (key : U → K) (P : U → Prop) [DecidablePred P] (β : ℝ)
    (h : ∀ q, (#((A.filter P).filter fun z => key z = q) : ℝ) ≤
      β * #(A.filter fun z => key z = q)) :
    (#(A.filter P) : ℝ) ≤ β * #A := by
  have h₁ := Finset.card_eq_sum_card_fiberwise (f := key) (s := A.filter P) (t := univ)
    (fun _ _ => mem_univ _)
  have h₂ := Finset.card_eq_sum_card_fiberwise (f := key) (s := A) (t := univ)
    (fun _ _ => mem_univ _)
  rw [h₁, h₂, Nat.cast_sum, Nat.cast_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun q _ => h q

/- On fixe la colonne opposée et on somme la condition agréable sur les fibres de la restriction. -/
private theorem s5_slice_bound :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let AgreeOff {V : Type} {L : ℕ} (i : Fin L) (x y : Fin L → V) : Prop :=
      ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j
    let IsCyc {V : Type} (G : SimpleGraph V) {L : ℕ} (x : Fin L → V) : Prop :=
      Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))
    let IsNice {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (β : ℝ)
        (C : Finset (Fin (8 * k) → Fin n)) : Prop :=
      (∀ x ∈ C, IsCyc G x) ∧
        ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → Fin n) (u : Fin n),
          (#(C.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
            β * #(C.filter fun x => AgreeOff i x y)
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let _pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
      w (side p) (row p)
    let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
      if t = b then z else y
    let slice {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) (b) (y : Fin (4*k) → Fin n) :=
      univ.filter fun z => pack (mix b y z) ∈ C
    ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : IsNice G k β C) (_hβ : 0 ≤ β)
    (b) (y : Fin (4*k) → Fin n) (j : Fin (4*k)) (u : Fin n), (#((slice C b y).filter fun z => z j = u) : ℝ) ≤ β * #(slice C b y) := by
  intro nxt AgreeOff IsCyc IsNice phase pos row side pack mix slice
  have pos_side : ∀ {k} (p : Fin (8*k)), pos (side p) (row p) = p := @s5_pos_side
  have pack_pos : ∀ {V : Type} {k} (w : Bool → Fin (4*k) → V) (b j), pack w (pos b j) = w b j := @s5_pack_pos
  have nice_positions : ∀ {k} (b : Bool) (j : Fin (4*k)), ∃ i : Fin (8*k),
    (pos b j = nxt i ∨ pos b j = nxt (nxt i)) ∧ side (nxt i) = b ∧ side (nxt (nxt i)) = b := @s5_nice_positions
  have pack_inj : ∀ {k n} (b) (y : Fin (4*k) → Fin n), Function.Injective (fun z => pack (mix b y z)) := @s5_pack_inj
  intro k n G β C hC hβ b y j u
  classical
  obtain ⟨i,hj,h1,h2⟩ := nice_positions b j
  let F := fun z => pack (mix b y z)
  let readB := fun (x : Fin (8*k) → Fin n) j => x (pos b j)
  have readF (z) : readB (F z) = z := by
    funext t
    simp [readB,F,pack_pos,mix]
  let key := fun z (p : {p : Fin (8*k) // p ≠ nxt i ∧ p ≠ nxt (nxt i)}) => F z p
  apply s5_sum_fibers_bound _ key
  intro q
  by_cases hq : ∃ z ∈ slice C b y, key z = q
  · obtain ⟨z₀,hz₀,rfl⟩ := hq
    have hoff (z) : key z = key z₀ ↔ AgreeOff i (F z) (F z₀) := by
      constructor
      · exact fun e p e₁ e₂ => congrFun e ⟨p,e₁,e₂⟩
      · exact fun e => funext fun p => e p p.2.1 p.2.2
    have inv (x) (hx : AgreeOff i x (F z₀)) : F (readB x) = x := by
      funext p
      by_cases hs : side p = b
      · simp only [F,pack,mix,hs,if_pos,readB]
        rw [← hs, pos_side]
      · have hn₁ : p ≠ nxt i := fun e => hs (e ▸ h1)
        have hn₂ : p ≠ nxt (nxt i) := fun e => hs (e ▸ h2)
        rw [hx p hn₁ hn₂]
        simp [F,pack,mix,hs]
    have ha := hC.2 i (F z₀) u
    apply le_trans _ (le_trans ha (mul_le_mul_of_nonneg_left _ hβ))
    · exact_mod_cast Finset.card_le_card_of_injOn F (by
        intro z hz
        obtain ⟨⟨hzC,hzu⟩,hzq⟩ := (show (z ∈ slice C b y ∧ z j = u) ∧ key z = key z₀ by
          simpa only [Finset.mem_coe,Finset.mem_filter] using hz)
        simp only [Finset.mem_coe, Finset.mem_filter]
        refine ⟨(mem_filter.mp hzC).2, (hoff z).mp hzq, ?_⟩
        have he : F z (pos b j) = u := by simpa [F,pack_pos,mix] using hzu
        rcases hj with e | e
        · exact Or.inl (e ▸ he)
        · exact Or.inr (e ▸ he)) (pack_inj b y).injOn
    · exact_mod_cast Finset.card_le_card_of_injOn readB (by
        intro x hx
        obtain ⟨hm,ho⟩ := mem_filter.mp hx
        have he := inv x ho
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, by change F (readB x) ∈ C; rwa [he]⟩,
          (hoff _).mpr (he.symm ▸ ho)⟩) (by
        intro x hx x' hx' e
        exact (inv _ (mem_filter.mp hx).2).symm.trans
          ((congrArg F e).trans (inv _ (mem_filter.mp hx').2)))
  · have hem : ((slice C b y).filter (fun z => z j = u)).filter (fun z => key z = q) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hq ⟨z,(mem_filter.mp (mem_filter.mp hz).1).1,(mem_filter.mp hz).2⟩
    rw [hem]
    simp only [card_empty, Nat.cast_zero]
    exact mul_nonneg hβ (Nat.cast_nonneg _)

private theorem s5_mix_flip :
    let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
      if t = b then z else y
    ∀ {k n} (y z : Fin (4*k) → Fin n), mix true z y = mix false y z := by
  intro mix k n y z
  funext b; cases b <;> rfl

private theorem s5_aux_adj :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let AgreeOff {V : Type} {L : ℕ} (i : Fin L) (x y : Fin L → V) : Prop :=
      ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j
    let IsCyc {V : Type} (G : SimpleGraph V) {L : ℕ} (x : Fin L → V) : Prop :=
      Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))
    let IsNice {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (β : ℝ)
        (C : Finset (Fin (8 * k) → Fin n)) : Prop :=
      (∀ x ∈ C, IsCyc G x) ∧
        ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → Fin n) (u : Fin n),
          (#(C.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
            β * #(C.filter fun x => AgreeOff i x y)
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let _pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
      w (side p) (row p)
    let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
      if t = b then z else y
    let slice {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) (b) (y : Fin (4*k) → Fin n) :=
      univ.filter fun z => pack (mix b y z) ∈ C
    let auxG {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) :
        SimpleGraph (Fin (4*k) → Fin n) :=
      SimpleGraph.fromRel fun y z => pack (mix true y z) ∈ C
    ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (y z), (auxG C).Adj y z ↔ z ∈ slice C true y ∨ z ∈ slice C false y := by
  intro nxt AgreeOff IsCyc IsNice phase pos row side pack mix slice auxG
  have side_pos : ∀ {k} (b) (j : Fin (4*k)), side (pos b j) = b := @s5_side_pos
  have pack_pos : ∀ {V : Type} {k} (w : Bool → Fin (4*k) → V) (b j), pack w (pos b j) = w b j := @s5_pack_pos
  have mix_flip : ∀ {k n} (y z : Fin (4*k) → Fin n), mix true z y = mix false y z := @s5_mix_flip
  intro k n G β C hk hC y z
  simp only [auxG,SimpleGraph.fromRel_adj,mix_flip y z,slice,mem_filter,mem_univ,true_and]
  refine ⟨And.right, fun hz => ⟨?_,hz⟩⟩
  rintro rfl
  have hn (b : Bool) (hm : pack (mix b y y) ∈ C) : False := by
    let j : Fin (4*k) := ⟨0,by omega⟩
    have e := (hC.1 _ hm).1 (a₁ := pos true j) (a₂ := pos false j)
      (by simp [pack_pos,mix])
    have ee := congrArg side e
    simp [side_pos] at ee
  exact hz.elim (hn _) (hn _)

private theorem s5_aux_nonempty :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let AgreeOff {V : Type} {L : ℕ} (i : Fin L) (x y : Fin L → V) : Prop :=
      ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j
    let IsCyc {V : Type} (G : SimpleGraph V) {L : ℕ} (x : Fin L → V) : Prop :=
      Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))
    let IsNice {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (β : ℝ)
        (C : Finset (Fin (8 * k) → Fin n)) : Prop :=
      (∀ x ∈ C, IsCyc G x) ∧
        ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → Fin n) (u : Fin n),
          (#(C.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
            β * #(C.filter fun x => AgreeOff i x y)
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let _pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
      w (side p) (row p)
    let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
      if t = b then z else y
    let _slice {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) (b) (y : Fin (4*k) → Fin n) :=
      univ.filter fun z => pack (mix b y z) ∈ C
    let auxG {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) :
        SimpleGraph (Fin (4*k) → Fin n) :=
      SimpleGraph.fromRel fun y z => pack (mix true y z) ∈ C
    ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (_ : C.Nonempty), (auxG C).edgeFinset.Nonempty := by
  intro nxt AgreeOff IsCyc IsNice phase pos row side pack mix slice auxG
  have pos_side : ∀ {k} (p : Fin (8*k)), pos (side p) (row p) = p := @s5_pos_side
  have pack_pos : ∀ {V : Type} {k} (w : Bool → Fin (4*k) → V) (b j), pack w (pos b j) = w b j := @s5_pack_pos
  have aux_adj : ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (y z), (auxG C).Adj y z ↔ z ∈ slice C true y ∨ z ∈ slice C false y := @s5_aux_adj
  intro k n G β C hk hC hne
  obtain ⟨x,hx⟩ := hne
  let y := fun j => x (pos false j)
  let z := fun j => x (pos true j)
  have he : pack (mix true y z) = x := by
    funext p
    rw [← pos_side p]
    simp only [pack_pos]
    cases e : side p <;> simp [mix,y,z]
  have ha : (auxG C).Adj y z := (aux_adj hk hC ..).mpr <| Or.inl <|
    mem_filter.mpr ⟨mem_univ _,he ▸ hx⟩
  exact ⟨s(y,z),mem_edgeFinset.mpr ha⟩

private theorem s5_aux_bound :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let AgreeOff {V : Type} {L : ℕ} (i : Fin L) (x y : Fin L → V) : Prop :=
      ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j
    let IsCyc {V : Type} (G : SimpleGraph V) {L : ℕ} (x : Fin L → V) : Prop :=
      Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))
    let IsNice {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (β : ℝ)
        (C : Finset (Fin (8 * k) → Fin n)) : Prop :=
      (∀ x ∈ C, IsCyc G x) ∧
        ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → Fin n) (u : Fin n),
          (#(C.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
            β * #(C.filter fun x => AgreeOff i x y)
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
      w (side p) (row p)
    let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
      if t = b then z else y
    let _slice {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) (b) (y : Fin (4*k) → Fin n) :=
      univ.filter fun z => pack (mix b y z) ∈ C
    let auxG {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) :
        SimpleGraph (Fin (4*k) → Fin n) :=
      SimpleGraph.fromRel fun y z => pack (mix true y z) ∈ C
    ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (_hβ : 0 ≤ β)
    (y) (j : Fin (4*k)) (u : Fin n), (#(((auxG C).neighborFinset y).filter fun z => z j = u) : ℝ) ≤ 2*β*(auxG C).degree y := by
  intro nxt AgreeOff IsCyc IsNice phase row side pack mix slice auxG
  have slice_bound : ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : IsNice G k β C) (hβ : 0 ≤ β)
    (b) (y : Fin (4*k) → Fin n) (j : Fin (4*k)) (u : Fin n), (#((slice C b y).filter fun z => z j = u) : ℝ) ≤ β * #(slice C b y) := @s5_slice_bound
  have aux_adj : ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (y z), (auxG C).Adj y z ↔ z ∈ slice C true y ∨ z ∈ slice C false y := @s5_aux_adj
  intro k n G β C hk hC hβ y j u
  classical
  have he : (auxG C).neighborFinset y = slice C true y ∪ slice C false y := by
    ext z
    simp only [mem_neighborFinset, mem_union, aux_adj hk hC]
  have hb (b) : (#(slice C b y) : ℝ) ≤ (auxG C).degree y := by
    rw [← card_neighborFinset_eq_degree,he]
    exact_mod_cast Finset.card_le_card (by cases b <;> simp : slice C b y ⊆ _)
  rw [he,filter_union]
  have hn := Finset.card_union_le ((slice C true y).filter fun z => z j = u)
    ((slice C false y).filter fun z => z j = u)
  have h₁ := (slice_bound hC hβ true y j u).trans (mul_le_mul_of_nonneg_left (hb true) hβ)
  have h₂ := (slice_bound hC hβ false y j u).trans (mul_le_mul_of_nonneg_left (hb false) hβ)
  exact (Nat.cast_le.mpr hn).trans (by push_cast; linarith)

/- Une collision est détectée par au moins une des (4k)² paires de coordonnées. -/
private theorem s5_collision_bound :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let AgreeOff {V : Type} {L : ℕ} (i : Fin L) (x y : Fin L → V) : Prop :=
      ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j
    let IsCyc {V : Type} (G : SimpleGraph V) {L : ℕ} (x : Fin L → V) : Prop :=
      Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))
    let IsNice {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (β : ℝ)
        (C : Finset (Fin (8 * k) → Fin n)) : Prop :=
      (∀ x ∈ C, IsCyc G x) ∧
        ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → Fin n) (u : Fin n),
          (#(C.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
            β * #(C.filter fun x => AgreeOff i x y)
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
      w (side p) (row p)
    let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
      if t = b then z else y
    let auxG {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) :
        SimpleGraph (Fin (4*k) → Fin n) :=
      SimpleGraph.fromRel fun y z => pack (mix true y z) ∈ C
    let collide {k n : ℕ} (y z : Fin (4*k) → Fin n) : Prop := ∃ a b, y a = z b
    ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (hβ : 0 ≤ β)
    (x v), (#(((auxG C).neighborFinset v).filter (collide x)) : ℝ) ≤
      32*(k : ℝ)^2*β*(auxG C).degree v := by
  intro nxt AgreeOff IsCyc IsNice phase row side pack mix auxG collide
  have aux_bound : ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (hβ : 0 ≤ β)
    (y) (j : Fin (4*k)) (u : Fin n), (#(((auxG C).neighborFinset y).filter fun z => z j = u) : ℝ) ≤ 2*β*(auxG C).degree y := @s5_aux_bound
  intro k n G β C hk hC hβ x v
  classical
  let S := (auxG C).neighborFinset v
  let T := fun (p : Fin (4*k) × Fin (4*k)) => S.filter fun z => z p.2 = x p.1
  have hs : S.filter (collide x) ⊆ univ.biUnion T := by
    intro z hz
    obtain ⟨hz,a,b,he⟩ := mem_filter.mp hz
    exact mem_biUnion.mpr ⟨(a,b),mem_univ _,mem_filter.mpr ⟨hz,he.symm⟩⟩
  have hc := (card_le_card hs).trans (Finset.card_biUnion_le ..)
  calc
    _ ≤ ((∑ p, #(T p) : ℕ) : ℝ) := by exact_mod_cast hc
    _ = ∑ p, (#(T p) : ℝ) := by push_cast; rfl
    _ ≤ ∑ _p : Fin (4*k) × Fin (4*k), (2*β*(auxG C).degree v) :=
      sum_le_sum fun p _ => aux_bound hk hC hβ v p.2 (x p.1)
    _ = _ := by simp; ring

private theorem s5_aux_edges :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let AgreeOff {V : Type} {L : ℕ} (i : Fin L) (x y : Fin L → V) : Prop :=
      ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j
    let IsCyc {V : Type} (G : SimpleGraph V) {L : ℕ} (x : Fin L → V) : Prop :=
      Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))
    let IsNice {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (β : ℝ)
        (C : Finset (Fin (8 * k) → Fin n)) : Prop :=
      (∀ x ∈ C, IsCyc G x) ∧
        ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → Fin n) (u : Fin n),
          (#(C.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
            β * #(C.filter fun x => AgreeOff i x y)
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let _pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
      w (side p) (row p)
    let _near {L} (p q : Fin L) : Prop := nxt p = q ∨ nxt q = p
    let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
      if t = b then z else y
    let _slice {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) (b) (y : Fin (4*k) → Fin n) :=
      univ.filter fun z => pack (mix b y z) ∈ C
    let auxG {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) :
        SimpleGraph (Fin (4*k) → Fin n) :=
      SimpleGraph.fromRel fun y z => pack (mix true y z) ∈ C
    ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) {y z}
    (_ : (auxG C).Adj y z), Function.Injective y ∧
    (∀ i j, i.val+1=j.val → i.val%2=0 → G.Adj (y i) (y j)) ∧
    (∀ i j, i.val+1=j.val → i.val%2≠0 → G.Adj (y i) (z j)) ∧
    (∀ i, i.val=0 ∨ i.val+1=4*k → G.Adj (y i) (z i)) := by
  intro nxt AgreeOff IsCyc IsNice phase pos row side pack near mix slice auxG
  have row_pos : ∀ {k} (b) (j : Fin (4*k)), row (pos b j) = j := @s5_row_pos
  have pack_pos : ∀ {V : Type} {k} (w : Bool → Fin (4*k) → V) (b j), pack w (pos b j) = w b j := @s5_pack_pos
  have near_inner : ∀ {k} (b : Bool) (i j : Fin (4*k)) (_ : i.val+1=j.val)
    (_ : i.val % 2 = 0), near (pos b i) (pos b j) := @s5_near_inner
  have near_cross : ∀ {k} (b : Bool) (i j : Fin (4*k)) (_ : i.val+1=j.val)
    (_ : i.val % 2 ≠ 0), near (pos b i) (pos (!b) j) := @s5_near_cross
  have near_end : ∀ {k} (i : Fin (4*k)) (_ : i.val = 0 ∨ i.val+1=4*k), near (pos false i) (pos true i) := @s5_near_end
  have aux_adj : ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (y z), (auxG C).Adj y z ↔ z ∈ slice C true y ∨ z ∈ slice C false y := @s5_aux_adj
  intro k n G β C hk hC y z h
  obtain ⟨b,hm⟩ : ∃ b, pack (mix b y z) ∈ C := by
    rcases (aux_adj hk hC ..).mp h with h | h
    · exact ⟨true,(mem_filter.mp h).2⟩
    · exact ⟨false,(mem_filter.mp h).2⟩
  let w := mix b y z
  have hw : IsCyc G (pack w) := hC.1 _ hm
  have hy : w (!b) = y := by cases b <;> rfl
  have hz : w b = z := by simp [w,mix]
  have edge {t s : Bool} {i j} (he : near (pos t i) (pos s j)) :
      G.Adj (w t i) (w s j) := by
    rcases he with e | e
    · simpa only [e,pack_pos] using hw.2 (pos t i)
    · simpa only [e,pack_pos] using (hw.2 (pos s j)).symm
  refine ⟨?_,?_,?_,?_⟩
  · intro i j e
    have en := hw.1 (a₁ := pos (!b) i) (a₂ := pos (!b) j) (by simpa only [pack_pos,hy] using e)
    simpa only [row_pos] using congrArg row en
  · intro i j e h
    simpa only [hy] using edge (near_inner (!b) i j e h)
  · intro i j e h
    simpa only [Bool.not_not,hy,hz] using edge (near_cross (!b) i j e h)
  · intro i hi
    have e := edge (near_end i hi)
    cases b <;> first | exact e | exact e.symm

/- La copie lit la ligne dans la coordonnée et la colonne dans le cycle auxiliaire. -/
private theorem s5_lift_cycle :
    let hRel (k ℓ : ℕ) (a b : Fin (4 * k) × Fin (2 * ℓ)) : Prop :=
      (a.1.val + 1 = b.1.val ∧
          (if a.1.val % 2 = 0 then a.2 = b.2
           else (a.2.val + 1) % (2 * ℓ) = b.2.val ∨ (b.2.val + 1) % (2 * ℓ) = a.2.val)) ∨
        (a.1 = b.1 ∧ (a.1.val = 0 ∨ a.1.val + 1 = 4 * k) ∧ (a.2.val + 1) % (2 * ℓ) = b.2.val)
    let Hkl (k ℓ : ℕ) : SimpleGraph (Fin (4 * k) × Fin (2 * ℓ)) := SimpleGraph.fromRel (hRel k ℓ)
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let AgreeOff {V : Type} {L : ℕ} (i : Fin L) (x y : Fin L → V) : Prop :=
      ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j
    let IsCyc {V : Type} (G : SimpleGraph V) {L : ℕ} (x : Fin L → V) : Prop :=
      Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))
    let IsNice {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (β : ℝ)
        (C : Finset (Fin (8 * k) → Fin n)) : Prop :=
      (∀ x ∈ C, IsCyc G x) ∧
        ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → Fin n) (u : Fin n),
          (#(C.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
            β * #(C.filter fun x => AgreeOff i x y)
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
      w (side p) (row p)
    let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
      if t = b then z else y
    let auxG {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) :
        SimpleGraph (Fin (4*k) → Fin n) :=
      SimpleGraph.fromRel fun y z => pack (mix true y z) ∈ C
    let collide {k n : ℕ} (y z : Fin (4*k) → Fin n) : Prop := ∃ a b, y a = z b
    ∀ {k ℓ n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C)
    (X : Fin (2*ℓ) → Fin (4*k) → Fin n)
    (_ : ∀ c, (auxG C).Adj (X c) (X (nxt c)))
    (_hd : ∀ i j, i ≠ j → ¬ collide (X i) (X j)), Hkl k ℓ ⊑ G := by
  intro hRel Hkl nxt AgreeOff IsCyc IsNice phase row side pack mix auxG collide
  have aux_edges : ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) {y z}
    (_ : (auxG C).Adj y z), Function.Injective y ∧
    (∀ i j, i.val+1=j.val → i.val%2=0 → G.Adj (y i) (y j)) ∧
    (∀ i j, i.val+1=j.val → i.val%2≠0 → G.Adj (y i) (z j)) ∧
    (∀ i, i.val=0 ∨ i.val+1=4*k → G.Adj (y i) (z i)) := @s5_aux_edges
  intro k ℓ n G β C hk hC X hX hd
  let f := fun (a : Fin (4*k) × Fin (2*ℓ)) => X a.2 a.1
  have em {a b} (e : hRel k ℓ a b) : G.Adj (f a) (f b) := by
    rcases a with ⟨i,c⟩
    rcases b with ⟨j,d⟩
    change G.Adj (X c i) (X d j)
    rcases e with ⟨hi,hj⟩ | ⟨rfl,hi,hj⟩
    · by_cases hpar : i.val % 2 = 0
      · simp only [hpar,if_true] at hj
        subst d
        exact (aux_edges hk hC (hX c)).2.1 i j hi hpar
      · simp only [hpar,if_false] at hj
        rcases hj with hj | hj
        · have he : nxt c = d := Fin.ext hj
          exact he ▸ (aux_edges hk hC (hX c)).2.2.1 i j hi hpar
        · have he : nxt d = c := Fin.ext hj
          exact he ▸ (aux_edges hk hC (hX d).symm).2.2.1 i j hi hpar
    · have he : nxt c = d := Fin.ext hj
      exact he ▸ (aux_edges hk hC (hX c)).2.2.2 _ hi
  refine ⟨⟨⟨f,fun h => ?_⟩,?_⟩⟩
  · rcases h.2 with h | h
    · exact em h
    · exact (em h).symm
  · rintro ⟨i,c⟩ ⟨j,d⟩ e
    change X c i = X d j at e
    by_cases hcd : c = d
    · subst d
      exact Prod.ext ((aux_edges hk hC (hX c)).1 e) rfl
    · exact (hd c d hcd ⟨i,j,e⟩).elim

/- Les dénombrements ne dépendent pas des instances utilisées pour énumérer les ensembles finis. -/
private theorem s5_edge_instances {V : Type} {A : SimpleGraph V} {i j : Fintype A.edgeSet}
    (h : (@SimpleGraph.edgeFinset V A i).Nonempty) : (@SimpleGraph.edgeFinset V A j).Nonempty :=
  Subsingleton.elim i j ▸ h

private theorem s5_bound_instances {V : Type} {A : SimpleGraph V} {v : V} {P : V → Prop}
    {t : ℝ} {i j : Fintype (A.neighborSet v)} {d e : DecidablePred P}
    (h : (#(@Finset.filter _ P d (@SimpleGraph.neighborFinset V A v i)) : ℝ) ≤
      t * (@SimpleGraph.degree V A v i)) :
    (#(@Finset.filter _ P e (@SimpleGraph.neighborFinset V A v j)) : ℝ) ≤
      t * (@SimpleGraph.degree V A v j) := by
  cases Subsingleton.elim i j
  cases Subsingleton.elim d e
  exact h

private theorem s5_finish :
    let hRel (k ℓ : ℕ) (a b : Fin (4 * k) × Fin (2 * ℓ)) : Prop :=
      (a.1.val + 1 = b.1.val ∧
          (if a.1.val % 2 = 0 then a.2 = b.2
           else (a.2.val + 1) % (2 * ℓ) = b.2.val ∨ (b.2.val + 1) % (2 * ℓ) = a.2.val)) ∨
        (a.1 = b.1 ∧ (a.1.val = 0 ∨ a.1.val + 1 = 4 * k) ∧ (a.2.val + 1) % (2 * ℓ) = b.2.val)
    let Hkl (k ℓ : ℕ) : SimpleGraph (Fin (4 * k) × Fin (2 * ℓ)) := SimpleGraph.fromRel (hRel k ℓ)
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let AgreeOff {V : Type} {L : ℕ} (i : Fin L) (x y : Fin L → V) : Prop :=
      ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j
    let IsCyc {V : Type} (G : SimpleGraph V) {L : ℕ} (x : Fin L → V) : Prop :=
      Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))
    let IsNice {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (β : ℝ)
        (C : Finset (Fin (8 * k) → Fin n)) : Prop :=
      (∀ x ∈ C, IsCyc G x) ∧
        ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → Fin n) (u : Fin n),
          (#(C.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
            β * #(C.filter fun x => AgreeOff i x y)
    let Step3 : Prop :=
      ∀ δ : ℝ, 0 < δ → ∀ k ℓ : ℕ, 1 ≤ k → 2 ≤ ℓ → 8 * k / δ ≤ ℓ → ∀ᶠ n : ℕ in atTop,
        ∀ G : SimpleGraph (Fin n), ∀ C : Finset (Fin (8 * k) → Fin n), C.Nonempty →
          IsNice G k ((n : ℝ) ^ (-δ)) C → Hkl k ℓ ⊑ G
    ∀ (auxG : {k n : ℕ} → Finset (Fin (8*k) → Fin n) → SimpleGraph (Fin (4*k) → Fin n))
    (collide : {k n : ℕ} → (Fin (4*k) → Fin n) → (Fin (4*k) → Fin n) → Prop)
    (_ : ∀ {k n} (x y : Fin (4*k) → Fin n), collide x y → collide y x)
    (_ : ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (_ : C.Nonempty), (auxG C).edgeFinset.Nonempty)
    (_ : ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (_hβ : 0 ≤ β)
    (x v), (#(((auxG C).neighborFinset v).filter (collide x)) : ℝ) ≤
      32*(k : ℝ)^2*β*(auxG C).degree v)
    (_ : ∀ {k ℓ n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C)
    (X : Fin (2*ℓ) → Fin (4*k) → Fin n)
    (_ : ∀ c, (auxG C).Adj (X c) (X (nxt c)))
    (_hd : ∀ i j, i ≠ j → ¬ collide (X i) (X j)), Hkl k ℓ ⊑ G)
    (_ : H3), Step3 := by
  intro hRel Hkl nxt AgreeOff IsCyc IsNice Step3 auxG collide sym aux_nonempty collision_bound lift_cycle h
  classical
  intro δ hδ k ℓ hk hℓ hsize
  have hkr : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hlr : 0 < (ℓ : ℝ) := by exact_mod_cast (show 0 < ℓ by omega)
  let θ := δ / (16*k)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hN := (tendsto_pow_atTop (α := ℕ) (n := 4*k) (by omega)).eventually (h ℓ hℓ θ hθ)
  have hlarge := ((tendsto_rpow_atTop (show 0 < δ/4 by positivity)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (32*(k : ℝ)^2))
  filter_upwards [hN,hlarge,eventually_ge_atTop (1 : ℕ)] with n hn hbig hn₁
  intro G C hne hC
  have hnr : 1 ≤ (n : ℝ) := by exact_mod_cast hn₁
  have hnp : 0 < (n : ℝ) := by linarith
  change 32*(k : ℝ)^2 ≤ (n : ℝ)^(δ/4) at hbig
  have hratio : (4*(k : ℝ))*(1/(ℓ : ℝ)) ≤ δ/2 := by
    rw [← mul_div_assoc, mul_one, div_le_iff₀ hlr]
    have he := (div_le_iff₀ hδ).mp hsize
    nlinarith
  have hcancel : (4*(k : ℝ))*θ = δ/4 := by
    dsimp [θ]
    field_simp
    ring
  have hbound : 32*(k : ℝ)^2*(n : ℝ)^(-δ) ≤
      ((n^(4*k) : ℕ) : ℝ)^(-(1/(ℓ : ℝ)+θ)) := by
    calc
      _ ≤ (n : ℝ)^(δ/4)*(n : ℝ)^(-δ) := by gcongr
      _ = (n : ℝ)^(δ/4 + -δ) := (Real.rpow_add hnp ..).symm
      _ ≤ (n : ℝ)^((4*(k : ℝ))*(-(1/(ℓ : ℝ)+θ))) := by
        apply Real.rpow_le_rpow_of_exponent_le hnr
        rw [mul_neg,mul_add,hcancel]
        linarith
      _ = _ := by
        rw [Nat.cast_pow,← Real.rpow_natCast,← Real.rpow_mul hnp.le]
        norm_cast
  obtain ⟨X,hX,hd⟩ := hn (Fin (4*k) → Fin n) (by simp) (auxG C) collide
    sym (aux_nonempty hk hC hne)
    (fun x v => (collision_bound hk hC (Real.rpow_nonneg hnp.le _) x v).trans
      (mul_le_mul_of_nonneg_right hbound (by positivity)))
  exact lift_cycle hk hC X hX hd

theorem step3_of_H3 (h : H3) :
    ∀ δ : ℝ, 0 < δ → ∀ k ℓ : ℕ, 1 ≤ k → 2 ≤ ℓ → 8 * k / δ ≤ ℓ → ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), ∀ C : Finset (Fin (8 * k) → Fin n), C.Nonempty →
      let nxt : Fin (8 * k) → Fin (8 * k) := fun i => ⟨(i.val + 1) % (8 * k), Nat.mod_lt _ i.pos⟩
      ((∀ x ∈ C, Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))) ∧
        ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → Fin n) (u : Fin n),
          (#(C.filter fun x => (∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j) ∧
              (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
            (n : ℝ) ^ (-δ) * #(C.filter fun x => ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j)) →
      SimpleGraph.fromRel (fun a b : Fin (4 * k) × Fin (2 * ℓ) =>
        (a.1.val + 1 = b.1.val ∧
            (if a.1.val % 2 = 0 then a.2 = b.2
             else (a.2.val + 1) % (2 * ℓ) = b.2.val ∨ (b.2.val + 1) % (2 * ℓ) = a.2.val)) ∨
          (a.1 = b.1 ∧ (a.1.val = 0 ∨ a.1.val + 1 = 4 * k) ∧ (a.2.val + 1) % (2 * ℓ) = b.2.val))
        ⊑ G := by
  let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
  let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
    ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
  let side {k : ℕ} (p : Fin (8*k)) : Bool :=
    if p.val < 4*k then phase (row p) else !(phase (row p))
  let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
    w (side p) (row p)
  let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
    if t = b then z else y
  let auxG {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) :
      SimpleGraph (Fin (4*k) → Fin n) :=
    SimpleGraph.fromRel fun y z => pack (mix true y z) ∈ C
  let collide {k n : ℕ} (y z : Fin (4*k) → Fin n) : Prop := ∃ a b, y a = z b
  apply s5_finish @auxG @collide _ _ _ @s5_lift_cycle h
  · exact fun _ _ ⟨a,b,e⟩ => ⟨b,a,e.symm⟩
  · intro k n G β C hk hC he
    exact s5_edge_instances (s5_aux_nonempty hk hC he)
  · intro k n G β C hk hC hβ x v
    exact s5_bound_instances (s5_collision_bound hk hC hβ x v)

end E147Step3

namespace E147

open OMA.R_Erdos147_erdos_147_variants_cubic_R1

private theorem hkl_step {n u v : ℕ} (hu : u < n) :
    (u + 1) % n = v ↔ u + 1 = v ∧ v < n ∨ u + 1 = n ∧ v = 0 := by
  by_cases h : u + 1 < n
  · rw [Nat.mod_eq_of_lt h]
    omega
  · have he : u + 1 = n := by omega
    rw [he, Nat.mod_self]
    omega

private theorem hkl_step_color {k ℓ : ℕ} {a b : Fin (4 * k) × Fin (2 * ℓ)}
    (h : (a.1.val + 1 = b.1.val ∧
          (if a.1.val % 2 = 0 then a.2 = b.2
           else (a.2.val + 1) % (2 * ℓ) = b.2.val ∨ (b.2.val + 1) % (2 * ℓ) = a.2.val)) ∨
        (a.1 = b.1 ∧ (a.1.val = 0 ∨ a.1.val + 1 = 4 * k) ∧ (a.2.val + 1) % (2 * ℓ) = b.2.val)) :
    (a.2.val + (a.1.val + 1) / 2) % 2 ≠ (b.2.val + (b.1.val + 1) / 2) % 2 := by
  simp only [Fin.ext_iff, hkl_step a.2.isLt, hkl_step b.2.isLt] at h
  rcases h with ⟨_, h⟩ | ⟨_, _, h⟩
  · split at h <;> omega
  · omega

set_option maxHeartbeats 1000000 in
/-- `H_{k,ℓ}` est 3-régulier. -/
theorem hkl_regular (k ℓ : ℕ) (hk : 1 ≤ k) (hl : 2 ≤ ℓ) :
    let hRel := fun a b : Fin (4 * k) × Fin (2 * ℓ) =>
      (a.1.val + 1 = b.1.val ∧
          (if a.1.val % 2 = 0 then a.2 = b.2
           else (a.2.val + 1) % (2 * ℓ) = b.2.val ∨ (b.2.val + 1) % (2 * ℓ) = a.2.val)) ∨
        (a.1 = b.1 ∧ (a.1.val = 0 ∨ a.1.val + 1 = 4 * k) ∧ (a.2.val + 1) % (2 * ℓ) = b.2.val)
    (SimpleGraph.fromRel hRel).IsRegularOfDegree 3 := by
  intro hRel ⟨r, c⟩
  have hr := r.isLt
  have hc := c.isLt
  let m : Fin (4 * k) := ⟨if r.val % 2 = 0 then r.val + 1 else r.val - 1, by
    split <;> omega⟩
  let x : Fin (4 * k) := ⟨if r.val % 2 = 0 then r.val - 1 else min (r.val + 1) (4 * k - 1), by
    simp only [Nat.min_def]
    split_ifs <;> omega⟩
  let p : Fin (2 * ℓ) := ⟨(c.val + 1) % (2 * ℓ), Nat.mod_lt _ (by omega)⟩
  let q : Fin (2 * ℓ) := ⟨if c.val = 0 then 2 * ℓ - 1 else c.val - 1, by split <;> omega⟩
  have hp : c.val + 1 = p.val ∧ p.val < 2 * ℓ ∨ c.val + 1 = 2 * ℓ ∧ p.val = 0 :=
    (hkl_step hc).mp rfl
  have hq (d : Fin (2 * ℓ)) : (d.val + 1) % (2 * ℓ) = c.val ↔ d.val = q.val := by
    rw [hkl_step d.isLt]
    have hd := d.isLt
    dsimp only [q]
    split <;> omega
  have hpq : p.val ≠ q.val := by dsimp only [q]; split <;> omega
  have hcp : c.val ≠ p.val := by omega
  have hcq : c.val ≠ q.val := by dsimp only [q]; split <;> omega
  have N : (SimpleGraph.fromRel hRel).neighborFinset (r, c) = {(m, c), (x, p), (x, q)} := by
    ext ⟨s, d⟩
    have hs := s.isLt
    have hm : s.val = m.val ↔
        r.val + 1 = s.val ∧ r.val % 2 = 0 ∨ s.val + 1 = r.val ∧ s.val % 2 = 0 := by
      dsimp only [m]
      split <;> omega
    have hx : s.val = x.val ↔
        r.val + 1 = s.val ∧ r.val % 2 ≠ 0 ∨ s.val + 1 = r.val ∧ s.val % 2 ≠ 0 ∨
        r.val = s.val ∧ (r.val = 0 ∨ r.val + 1 = 4 * k) := by
      dsimp only [x]
      simp only [Nat.min_def]
      split_ifs <;> omega
    have hp' : (c.val + 1) % (2 * ℓ) = d.val ↔ d.val = p.val := eq_comm
    rw [SimpleGraph.mem_neighborFinset]
    simp only [SimpleGraph.fromRel_adj, hRel, mem_insert,
      mem_singleton, ne_eq, Prod.mk.injEq, Fin.ext_iff, hp', hq, hm, hx, ite_prop_iff_or]
    grind only
  rw [← SimpleGraph.card_neighborFinset_eq_degree, N]
  simp [Fin.ext_iff, hcp, hcq, hpq]

/-- `H_{k,ℓ}` est biparti. -/
theorem hkl_bipartite (k ℓ : ℕ) :
    let hRel := fun a b : Fin (4 * k) × Fin (2 * ℓ) =>
      (a.1.val + 1 = b.1.val ∧
          (if a.1.val % 2 = 0 then a.2 = b.2
           else (a.2.val + 1) % (2 * ℓ) = b.2.val ∨ (b.2.val + 1) % (2 * ℓ) = a.2.val)) ∨
        (a.1 = b.1 ∧ (a.1.val = 0 ∨ a.1.val + 1 = 4 * k) ∧ (a.2.val + 1) % (2 * ℓ) = b.2.val)
    (SimpleGraph.fromRel hRel).IsBipartite := by
  intro hRel
  let f (a : Fin (4 * k) × Fin (2 * ℓ)) : Fin 2 :=
    ⟨(a.2.val + (a.1.val + 1) / 2) % 2, Nat.mod_lt _ (by decide)⟩
  refine ⟨Coloring.mk f ?_⟩
  intro a b h he
  have e := congrArg Fin.val he
  rcases h.2 with hab | hba
  · exact hkl_step_color hab e
  · exact hkl_step_color hba e.symm

/-- Si, à partir d'un rang, tout graphe à `n` sommets et au moins `n^a` arêtes contient `H`,
alors `ex(n, H) = O(n^b)` pour tout `b ≥ a`. -/
theorem bigO_of_eventually_contains {W : Type*} (H : SimpleGraph W) (a b : ℝ) (hab : a ≤ b)
    (h : ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), (n : ℝ) ^ a ≤ #G.edgeFinset → H ⊑ G) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ b := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hpos : (0 : ℝ) ≤ (n : ℝ) ^ a := Real.rpow_nonneg (by positivity) a
  have hex : (extremalNumber n H : ℝ) ≤ (n : ℝ) ^ a := by
    have key := (extremalNumber_le_iff_of_nonneg (V := Fin n) H hpos).2
    rw [Fintype.card_fin] at key
    apply key
    intro G inst hfree
    have hinst : inst = (fun _ _ => Classical.propDecidable _) := Subsingleton.elim _ _
    subst hinst
    by_contra hlt
    exact hfree (hn G (le_of_lt (not_le.mp hlt)))
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) b),
    one_mul]
  exact hex.trans (Real.rpow_le_rpow_of_exponent_le hn1' hab)

/-- Lemme 2.10 : un sous-graphe couvrant avec la moitié des arêtes, où aucune arête n'est dans
une trop grande part des 4-cycles. -/
theorem clean_c4 {m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.edgeFinset.Nonempty) :
    let cyc4 := fun F : SimpleGraph (Fin m) => univ.filter fun t : Fin m × Fin m × Fin m × Fin m =>
      F.Adj t.1 t.2.1 ∧ F.Adj t.2.1 t.2.2.1 ∧ F.Adj t.2.2.1 t.2.2.2 ∧ F.Adj t.2.2.2 t.1 ∧
        t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2
    let UsesEdge := fun (t : Fin m × Fin m × Fin m × Fin m) (e : Sym2 (Fin m)) =>
      e = s(t.1, t.2.1) ∨ e = s(t.2.1, t.2.2.1) ∨ e = s(t.2.2.1, t.2.2.2) ∨ e = s(t.2.2.2, t.1)
    ∃ F : SimpleGraph (Fin m), F ≤ G ∧ (#G.edgeFinset : ℝ) / 2 ≤ #F.edgeFinset ∧
      ∀ e ∈ F.edgeFinset, (#((cyc4 F).filter fun t => UsesEdge t e) : ℝ) ≤
        16 * Real.log m / #F.edgeFinset * #(cyc4 F) := by
  intro cyc4 UsesEdge
  classical
  have clean_c4_delete (F : SimpleGraph (Fin m)) (e : Sym2 (Fin m)) :
      cyc4 (F.deleteEdges ({e} : Finset _)) = (cyc4 F).filter fun t => ¬ UsesEdge t e := by
    ext t
    simp only [cyc4, mem_filter, mem_univ, true_and, deleteEdges_adj, Finset.mem_coe,
      Finset.mem_singleton, UsesEdge]
    grind only
  let E : ℝ := #G.edgeFinset
  let L : ℝ := Real.log m
  let θ : ℝ := 16 * L / E
  have hEn : 0 < #G.edgeFinset := Finset.card_pos.mpr hG
  have hE : 0 < E := by dsimp only [E]; exact_mod_cast hEn
  have hm : 2 ≤ m := by
    have h := G.card_edgeFinset_le_card_choose_two
    rw [Fintype.card_fin] at h
    by_contra! hlt
    rw [Nat.choose_eq_zero_of_lt hlt] at h
    omega
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : 0 < (m : ℝ) := by linarith
  have hL : 1 / 2 ≤ L := by
    have h₂ := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    have h₃ := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hmR
    change 1 / 2 ≤ Real.log m
    linarith
  have hθ : 0 < θ := div_pos (by linarith) hE
  have hθE : θ * E = 16 * L := div_mul_cancel₀ _ hE.ne'
  let P : ℕ → Prop := fun n => ∃ F : SimpleGraph (Fin m), #F.edgeFinset = n ∧ F ≤ G ∧
    E / 2 ≤ #F.edgeFinset ∧ (#(cyc4 F) : ℝ) ≤ Real.exp (4 * L - θ * (E - #F.edgeFinset))
  have hP : ∃ n, P n := by
    refine ⟨_, G, rfl, le_rfl, ?_, ?_⟩
    · change E / 2 ≤ E
      linarith
    · change (#(cyc4 G) : ℝ) ≤ Real.exp (4 * L - θ * (E - E))
      rw [sub_self, mul_zero, sub_zero, show (4 : ℝ) = (4 : ℕ) by norm_num,
        Real.exp_nat_mul, Real.exp_log hmpos]
      have h : #(cyc4 G) ≤ m ^ 4 := by
        simpa [Fintype.card_prod, pow_succ, mul_assoc] using (cyc4 G).card_le_univ
      exact_mod_cast h
  obtain ⟨F, hFn, hFG, hhalf, hpot⟩ := Nat.find_spec hP
  refine ⟨F, hFG, hhalf, ?_⟩
  intro e he
  have hFpos : 0 < (#F.edgeFinset : ℝ) := by linarith
  have hFE : (#F.edgeFinset : ℝ) ≤ E := by
    dsimp only [E]
    exact_mod_cast card_le_card (edgeFinset_mono hFG)
  have hcoef : θ ≤ 16 * Real.log m / #F.edgeFinset := by
    exact div_le_div_of_nonneg_left (by change 0 ≤ 16 * L; linarith) hFpos hFE
  apply le_trans _ (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _))
  by_contra! hbad
  obtain ⟨D, hDel⟩ : ∃ D : SimpleGraph (Fin m), D = F.deleteEdges ({e} : Finset _) := ⟨_, rfl⟩
  have hedges : #D.edgeFinset + 1 = #F.edgeFinset := by
    subst D
    rw [edgeFinset_deleteEdges, sdiff_singleton_eq_erase]
    exact card_erase_add_one he
  have hcycles : #((cyc4 F).filter fun t => UsesEdge t e) + #(cyc4 D) = #(cyc4 F) := by
    subst D
    rw [clean_c4_delete]
    exact card_filter_add_card_filter_not _
  have hedgesR : (#D.edgeFinset : ℝ) + 1 = #F.edgeFinset := by exact_mod_cast hedges
  have hcyclesR : (#((cyc4 F).filter fun t => UsesEdge t e) : ℝ) + #(cyc4 D) = #(cyc4 F) := by
    exact_mod_cast hcycles
  have hq : 0 < #(cyc4 F) := by
    by_contra! hn
    have hz : #(cyc4 F) = 0 := by omega
    have hu : #((cyc4 F).filter fun t => UsesEdge t e) = 0 := by omega
    simp [hz, hu] at hbad
  have hqR : (1 : ℝ) ≤ #(cyc4 F) := by exact_mod_cast hq
  have hθlt : θ < 1 := by
    by_contra! hn
    have := mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg #(cyc4 F) : (0 : ℝ) ≤ _)
    linarith [Nat.cast_nonneg #(cyc4 D) (α := ℝ)]
  have hE4 : 4 ≤ E := by nlinarith [mul_lt_mul_of_pos_right hθlt hE]
  have hx := Real.one_le_exp_iff.mp (hqR.trans hpot)
  have hfrac : 0 ≤ θ * (4 * #F.edgeFinset - 3 * E) := by linarith only [hθE, hx]
  have hroom := nonneg_of_mul_nonneg_right hfrac hθ
  have hD : P #D.edgeFinset := by
    refine ⟨D, rfl, hDel ▸ (deleteEdges_le _).trans hFG, by linarith only [hroom, hE4, hedgesR], ?_⟩
    calc
      (#(cyc4 D) : ℝ) ≤ (1 - θ) * #(cyc4 F) := by linarith
      _ ≤ Real.exp (-θ) * #(cyc4 F) :=
        mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg _) (Nat.cast_nonneg _)
      _ ≤ Real.exp (-θ) * Real.exp (4 * L - θ * (E - #F.edgeFinset)) :=
        mul_le_mul_of_nonneg_left hpot (Real.exp_pos _).le
      _ = Real.exp (4 * L - θ * (E - #D.edgeFinset)) := by
        rw [← Real.exp_add, ← hedgesR]
        congr 1
        ring
  have hmin := Nat.find_min' hP hD
  omega

private theorem prune_good_classes {V : Type*} {L : ℕ} (nx : Fin L → Fin L) (T : ℝ)
    (hT : 0 ≤ T) (Q : Finset (Σ _ : Fin L, Fin L → V)) (D : Finset (Fin L → V))
    (hD : D.Nonempty) (hmass : T * #Q ≤ #D) :
    let AgreeOff := fun (i : Fin L) (x y : Fin L → V) => ∀ j, j ≠ nx i → j ≠ nx (nx i) → x j = y j
    (∀ x ∈ D, ∀ i, ∃ z, (⟨i, z⟩ ∈ Q) ∧ AgreeOff i x z) →
    ∃ E ⊆ D, E.Nonempty ∧ ∀ (i : Fin L) (y : Fin L → V),
      (E.filter fun x => AgreeOff i x y).Nonempty → T ≤ #(E.filter fun x => AgreeOff i x y) := by
  intro AgreeOff hcover
  classical
  induction Q using Finset.strongInductionOn generalizing D with
  | _ Q ih =>
    by_cases hdone : ∀ (i : Fin L) (y : Fin L → V),
      (D.filter fun x => AgreeOff i x y).Nonempty → T ≤ #(D.filter fun x => AgreeOff i x y)
    · exact ⟨D, Subset.rfl, hD, hdone⟩
    push Not at hdone
    obtain ⟨i, y, ⟨w, hw⟩, hlight⟩ := hdone
    obtain ⟨hwD, hwy⟩ := mem_filter.mp hw
    obtain ⟨z, hz, hwz⟩ := hcover w hwD i
    let q : Σ _ : Fin L, Fin L → V := ⟨i, z⟩
    let D₁ := D.filter fun x => ¬ AgreeOff i x y
    have hsplit : (#(D.filter fun x => AgreeOff i x y) : ℝ) + #D₁ = #D := by
      exact_mod_cast D.card_filter_add_card_filter_not (fun x => AgreeOff i x y)
    have hq : (#(Q.erase q) : ℝ) + 1 = #Q := by
      exact_mod_cast Finset.card_erase_add_one (show q ∈ Q from hz)
    rw [← hq] at hmass
    have hstrict : T * #(Q.erase q) < #D₁ := by nlinarith only [hsplit, hlight, hmass]
    have hpos : (0 : ℝ) < #D₁ := lt_of_le_of_lt (mul_nonneg hT (Nat.cast_nonneg _)) hstrict
    have hn : D₁.Nonempty := Finset.card_pos.mp (by exact_mod_cast hpos)
    have hsub : D₁ ⊆ D := Finset.filter_subset _ _
    obtain ⟨E, hE, hnE, hlarge⟩ := ih (Q.erase q) (Finset.erase_ssubset hz) D₁ hn hstrict.le (by
      intro x hx j
      obtain ⟨v, hv, hxv⟩ := hcover x (hsub hx) j
      refine ⟨v, mem_erase.mpr ⟨?_, hv⟩, hxv⟩
      intro he
      change (⟨j, v⟩ : Σ _ : Fin L, Fin L → V) = ⟨i, z⟩ at he
      cases he
      apply (mem_filter.mp hx).2
      intro l h₁ h₂
      exact (hxv l h₁ h₂).trans ((hwz l h₁ h₂).symm.trans (hwy l h₁ h₂)))
    exact ⟨E, hE.trans hsub, hnE, hlarge⟩

/-- Fixer l'une des deux coordonnées libres ne laisse que l'autre variable. -/
private theorem card_fixed_good {V : Type*} {L : ℕ} (nx : Fin L → Fin L)
    (C D : Finset (Fin L → V)) (hDC : D ⊆ C) (s : ℝ) (hs : 0 ≤ s)
    (hline : ∀ y ∈ C, ∀ b, (#(C.filter fun x => ∀ j, j ≠ b → x j = y j) : ℝ) ≤ s)
    (i a b : Fin L) (y : Fin L → V) (u : V)
    (hab : ∀ j, j ≠ a → j ≠ b → j ≠ nx i ∧ j ≠ nx (nx i)) :
    let AgreeOff := fun (i : Fin L) (x y : Fin L → V) => ∀ j, j ≠ nx i → j ≠ nx (nx i) → x j = y j
    (#(D.filter fun x => AgreeOff i x y ∧ x a = u) : ℝ) ≤ s := by
  intro AgreeOff
  classical
  let F := D.filter fun x => AgreeOff i x y ∧ x a = u
  change (#F : ℝ) ≤ s
  by_cases hn : F.Nonempty
  · obtain ⟨w, hw⟩ := hn
    obtain ⟨hwD, hwy, hwa⟩ := mem_filter.mp hw
    have hsub : F ⊆ C.filter (fun x => ∀ j, j ≠ b → x j = w j) := by
      intro x hx
      obtain ⟨hxD, hxy, hxa⟩ := mem_filter.mp hx
      refine mem_filter.mpr ⟨hDC hxD, ?_⟩
      intro j hj
      by_cases hja : j = a
      · subst j; exact hxa.trans hwa.symm
      · obtain ⟨h₁, h₂⟩ := hab j hja hj
        exact (hxy j h₁ h₂).trans (hwy j h₁ h₂).symm
    exact (Nat.cast_le.mpr (card_le_card hsub)).trans (hline w (hDC hwD) b)
  · simpa [Finset.not_nonempty_iff_eq_empty.mp hn] using hs

/-- Lemme 2.12 de l'article (étape 2) : un ensemble bon non vide contient un ensemble agréable
non vide. -/
theorem good_imp_nice {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 1 ≤ k)
    (β : ℝ) (hβ : 0 < β) (C : Finset (Fin (8 * k) → V)) (hC : C.Nonempty)
    (nxt : Fin (8 * k) → Fin (8 * k)) :
    let AgreeOff := fun (i : Fin (8 * k)) (x y : Fin (8 * k) → V) =>
      ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j
    (∃ s : ℝ, 0 < s ∧ (∀ x ∈ C, Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))) ∧
      (∀ y ∈ C, ∀ i, (#(C.filter fun x => ∀ j, j ≠ i → x j = y j) : ℝ) ≤ s) ∧
      ∀ i : Fin (8 * k), ∃ P : Finset (Fin (8 * k) → V),
        (#P : ℝ) ≤ β * #C / (16 * k * s) ∧ ∀ x ∈ C, ∃ y ∈ P, AgreeOff i x y) →
    ∃ D ⊆ C, D.Nonempty ∧ (∀ x ∈ D, Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))) ∧
      ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → V) (u : V),
        (#(D.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
          β * #(D.filter fun x => AgreeOff i x y) := by
  intro AgreeOff h
  classical
  obtain ⟨s, hs, hcyc, hline, hrepr⟩ := h
  choose P hP hcov using hrepr
  let T := 2 * s / β
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let Q : Finset (Σ _ : Fin (8 * k), Fin (8 * k) → V) := univ.sigma P
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hcard : (#Q : ℝ) ≤ (8 * (k : ℝ)) * (β * #C / (16 * k * s)) := by
    change (#(univ.sigma P) : ℝ) ≤ _
    rw [Finset.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ _i : Fin (8 * k), β * #C / (16 * k * s) := Finset.sum_le_sum (fun i _ => hP i)
      _ = _ := by simp
  have hmass : T * #Q ≤ #C := calc
    _ ≤ T * ((8 * (k : ℝ)) * (β * #C / (16 * k * s))) := mul_le_mul_of_nonneg_left hcard hT
    _ = _ := by dsimp [T]; field_simp [hβ.ne', hs.ne', hk'.ne']; ring
  obtain ⟨D, hDC, hnD, hlarge⟩ := prune_good_classes nxt T hT Q C hC hmass (by
    intro x hx i
    obtain ⟨y, hy, hxy⟩ := hcov i x hx
    exact ⟨y, Finset.mem_sigma.mpr ⟨mem_univ _, hy⟩, hxy⟩)
  refine ⟨D, hDC, hnD, fun x hx => hcyc x (hDC hx), ?_⟩
  intro i y u
  let F := D.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)
  change (#F : ℝ) ≤ _
  by_cases hn : F.Nonempty
  · obtain ⟨w, hw⟩ := hn
    obtain ⟨hwD, hwy, _⟩ := mem_filter.mp hw
    have hthick := hlarge i y ⟨w, mem_filter.mpr ⟨hwD, hwy⟩⟩
    let A := D.filter fun x => AgreeOff i x y ∧ x (nxt i) = u
    let B := D.filter fun x => AgreeOff i x y ∧ x (nxt (nxt i)) = u
    have hA : (#A : ℝ) ≤ s := card_fixed_good nxt C D hDC s hs.le hline i _ _ y u
      (fun _ ha hb => ⟨ha, hb⟩)
    have hB : (#B : ℝ) ≤ s := card_fixed_good nxt C D hDC s hs.le hline i _ _ y u
      (fun _ ha hb => ⟨hb, ha⟩)
    have hsub : F ⊆ A ∪ B := by
      intro x hx
      obtain ⟨hxD, hxy, hx₁ | hx₂⟩ := mem_filter.mp hx
      · exact mem_union_left _ (mem_filter.mpr ⟨hxD, hxy, hx₁⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hxD, hxy, hx₂⟩)
    have hc : (#F : ℝ) ≤ #A + #B := by
      exact_mod_cast (card_le_card hsub).trans (card_union_le A B)
    have hmul := (div_le_iff₀ hβ).mp hthick
    rw [mul_comm β]
    linarith only [hc, hA, hB, hmul]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp only [card_empty, Nat.cast_zero]
    positivity

private theorem degre_ajout_borne {m t : ℕ} (S : SimpleGraph (Fin m)) {u v : Fin m}
    (hs : ∀ x, S.degree x ≤ t) (hu : S.degree u < t) (hv : S.degree v < t) :
    ∀ x, (S ⊔ edge u v).degree x ≤ t := by
  classical
  intro x
  by_cases hx : x = u ∨ x = v
  · have hlt : S.degree x < t := hx.elim (fun e => e ▸ hu) (fun e => e ▸ hv)
    have hsub : (S ⊔ edge u v).neighborFinset x ⊆
        insert (if x = u then v else u) (S.neighborFinset x) := by
      intro y hy
      simp only [mem_neighborFinset, sup_adj, edge_adj] at hy
      simp only [mem_insert, mem_neighborFinset]
      split_ifs <;> grind
    exact (card_le_card hsub).trans ((card_insert_le _ _).trans hlt)
  · have hsub : (S ⊔ edge u v).neighborFinset x ⊆ S.neighborFinset x := by
      intro y hy
      simp only [mem_neighborFinset, sup_adj, edge_adj] at *
      tauto
    exact (card_le_card hsub).trans (hs x)

private theorem glouton_saturation {m : ℕ} (H : SimpleGraph (Fin m)) (t : ℕ) :
    ∃ S ≤ H, (∀ v, S.degree v ≤ t) ∧
      ∀ u v, H.Adj u v → ¬ S.Adj u v → t ≤ S.degree u ∨ t ≤ S.degree v := by
  classical
  let F := univ.filter (fun S : SimpleGraph (Fin m) => S ≤ H ∧ ∀ v, S.degree v ≤ t)
  have hF : F.Nonempty := by
    refine ⟨⊥, mem_filter.mpr ⟨mem_univ _, bot_le, ?_⟩⟩
    intro v
    simp [degree]
  obtain ⟨S, hS, hmax⟩ := F.exists_max_image (fun S => #S.edgeFinset) hF
  obtain ⟨hSH, hdeg⟩ := (mem_filter.mp hS).2
  refine ⟨S, hSH, hdeg, ?_⟩
  have hsat {u v} (hadj : H.Adj u v) (hmiss : ¬ S.Adj u v) : t ≤ S.degree u ∨ t ≤ S.degree v := by
    by_contra! hsmall
    have hnew : S ⊔ edge u v ∈ F := by
      refine mem_filter.mpr ⟨mem_univ _, sup_le hSH ((edge_le_iff H).mpr (.inr hadj)), ?_⟩
      intro x
      convert! degre_ajout_borne S hdeg hsmall.1 hsmall.2 x using 1
      exact congrArg (fun I => @SimpleGraph.degree _ (S ⊔ edge u v) x I) (Subsingleton.elim _ _)
    have hbad := hmax _ hnew
    have hmono {B C : SimpleGraph (Fin m)} (hlt : B < C) : #B.edgeFinset < #C.edgeFinset :=
      card_lt_card (edgeFinset_strict_mono hlt)
    exact (not_lt_of_ge hbad) (hmono (S.lt_sup_edge _ _ hadj.ne hmiss))
  exact fun _ _ => hsat

/-- Les arêtes manquées rencontrent toutes le petit ensemble saturé. On le réunit à
chaque classe modulo `p` et l'on retient la classe qui contient le plus d'arêtes. -/
private theorem concentrer {n p : ℕ} (hp : 0 < p) (hpn : p ≤ n)
    (G S : SimpleGraph (Fin n)) (hSG : S ≤ G) (A : Finset (Fin n))
    (hA : #A * p ≤ n) (hpetit : 2 * #S.edgeFinset ≤ #G.edgeFinset)
    (hcouv : ∀ u v, G.Adj u v → ¬ S.Adj u v → u ∈ A ∨ v ∈ A) :
    ∃ k, ∃ H : SimpleGraph (Fin k), H ⊑ G ∧ k * p ≤ 3 * n ∧
      #G.edgeFinset ≤ 2 * p * #H.edgeFinset := by
  classical
  let c (v : Fin n) := v.val % p
  let C (j : ℕ) := univ.filter fun v : Fin n => c v = j
  let U (j : ℕ) := A ∪ C j
  let E (j : ℕ) := G.edgeFinset.filter fun e => e.toFinset ⊆ U j
  have hc (v : Fin n) : v ∈ C (c v) := mem_filter.mpr ⟨mem_univ _, rfl⟩
  have hcover : G.edgeFinset \ S.edgeFinset ⊆ (range p).biUnion E := by
    intro e
    induction e using Sym2.inductionOn with | hf u v =>
      intro he
      obtain ⟨h₁, h₂⟩ := mem_sdiff.mp he
      rcases hcouv u v (mem_edgeFinset.mp h₁) (fun h => h₂ (mem_edgeFinset.mpr h)) with hu | hv
      · refine mem_biUnion.mpr ⟨c v, mem_range.mpr (Nat.mod_lt _ hp),
            mem_filter.mpr ⟨h₁, ?_⟩⟩
        rw [Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff]
        exact ⟨mem_union_left _ hu, mem_union_right _ (hc v)⟩
      · refine mem_biUnion.mpr ⟨c u, mem_range.mpr (Nat.mod_lt _ hp),
            mem_filter.mpr ⟨h₁, ?_⟩⟩
        rw [Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff]
        exact ⟨mem_union_right _ (hc u), mem_union_left _ hv⟩
  obtain ⟨j, hj, hbest⟩ := (range p).exists_max_image (fun j => #(E j))
    ⟨0, mem_range.mpr hp⟩
  have hcount : #(G.edgeFinset \ S.edgeFinset) ≤ p * #(E j) := calc
    _ ≤ #((range p).biUnion E) := card_le_card hcover
    _ ≤ ∑ i ∈ range p, #(E i) := card_biUnion_le
    _ ≤ ∑ _i ∈ range p, #(E j) := sum_le_sum hbest
    _ = _ := by simp
  have hf : #(C j) ≤ n / p + 1 := by
    rw [← card_range (n / p + 1)]
    apply card_le_card_of_injOn (fun v : Fin n => v.val / p)
    · intro v _
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right v.isLt.le))
    · intro v hv w hw heq
      have hv' := (mem_filter.mp hv).2
      have hw' := (mem_filter.mp hw).2
      change v.val % p = j at hv'
      change w.val % p = j at hw'
      change v.val / p = w.val / p at heq
      exact Fin.ext (calc
        _ = v.val % p + p * (v.val / p) := (Nat.mod_add_div ..).symm
        _ = w.val % p + p * (w.val / p) := by rw [hv', hw', heq]
        _ = _ := Nat.mod_add_div ..)
  let H := G.induce (U j : Set (Fin n))
  have hcard : Fintype.card (U j : Set (Fin n)) = #(U j) := Fintype.card_coe _
  refine ⟨#(U j), H.overFin hcard, ?_, ?_, ?_⟩
  · exact (show H.overFin hcard ⊑ H from ⟨(H.overFinIso hcard).symm.toCopy⟩).trans
      ⟨Copy.induce G _⟩
  · calc
      #(U j) * p ≤ (#A + #(C j)) * p := Nat.mul_le_mul_right _ (card_union_le ..)
      _ ≤ (#A + (n / p + 1)) * p := by gcongr
      _ ≤ 3 * n := by nlinarith only [hA, Nat.div_mul_le_self n p, hpn]
  · have hpart := card_sdiff_add_card_eq_card (edgeFinset_mono hSG)
    have hEq : #(E j) = #(H.overFin hcard).edgeFinset :=
      (G.card_filter_edgeFinset_toFinset_subset (U j)).trans (H.overFinIso hcard).card_edgeFinset_eq
    rw [← hEq]
    linarith only [hpart, hpetit, hcount]

private theorem aretes_le_carre {n : ℕ} (G : SimpleGraph (Fin n)) :
    #G.edgeFinset ≤ n * n := by
  classical
  have h : 2 * #G.edgeFinset ≤ n * n := calc
    _ = ∑ v, G.degree v := G.sum_degrees_eq_twice_card_edges.symm
    _ ≤ ∑ _v : Fin n, n := sum_le_sum fun v _ => by simpa using (G.degree_lt_card_verts v).le
    _ = _ := by simp
  omega

/-- Le quotient du nombre d'arêtes par `n^(1+δ)` ne décroît pas lors d'une
concentration. La constante `D`, fixée une fois pour toutes, minore ce quotient. -/
private theorem regulariser {δ D : ℝ} (hδ : 0 < δ) (hD : 0 < D) {q : ℕ}
    (hq : 2 ≤ q) (hgain : 8 ≤ (q : ℝ) ^ δ) (n : ℕ) (hn : 0 < n)
    (hdom : (n : ℝ) ^ δ ≤ D) (G : SimpleGraph (Fin n))
    (hE : D * (n : ℝ) ^ (1 + δ) ≤ #G.edgeFinset) :
    ∃ m, ∃ S : SimpleGraph (Fin m), D ≤ m ∧ S ⊑ G ∧
      (m : ℝ) ^ (1 + (δ + δ)) / 3 ≤ #S.edgeFinset ∧
      ∀ v, (S.degree v : ℝ) ≤ ((4*q : ℕ) + 1 : ℝ) * (m : ℝ) ^ (δ + δ) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    let p := 4*q
    have hp : 0 < p := by dsimp [p]; omega
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    let X := (n : ℝ) ^ (δ + δ)
    have hX : 1 ≤ X := Real.one_le_rpow hn1 (by linarith)
    have hX' : 0 < X := by linarith
    have hid : (n : ℝ) ^ (1 + (δ + δ)) = n * X := by
      rw [Real.rpow_add hn', Real.rpow_one]
    have hprod : (n : ℝ) ^ δ * (n : ℝ) ^ (1 + δ) = n * X := by
      rw [← Real.rpow_add hn', ← hid]
      congr 1
      ring
    have hden : (n : ℝ) * X ≤ #G.edgeFinset := by
      rw [← hprod]
      exact (mul_le_mul_of_nonneg_right hdom (by positivity)).trans hE
    have hsize : D ≤ n := by
      have hpow : (n : ℝ) ≤ (n : ℝ) ^ (1 + δ) := by
        rw [Real.rpow_add hn', Real.rpow_one]
        exact le_mul_of_one_le_right hn'.le (Real.one_le_rpow hn1 hδ.le)
      have htop : (#G.edgeFinset : ℝ) ≤ n * n := by exact_mod_cast aretes_le_carre G
      exact le_of_mul_le_mul_right ((mul_le_mul_of_nonneg_left hpow hD.le).trans (hE.trans htop)) hn'
    by_cases hpn : p ≤ n
    · let t := ⌈(p : ℝ) * X⌉₊
      have ht : (p : ℝ) * X ≤ t := Nat.le_ceil _
      obtain ⟨S, hSG, hdeg, hsat⟩ := glouton_saturation G t
      by_cases hdense : (n : ℝ) * X / 3 ≤ #S.edgeFinset
      · refine ⟨n, S, hsize, IsContained.of_le hSG, hid ▸ hdense, ?_⟩
        intro v
        have hd : (S.degree v : ℝ) ≤ t := by exact_mod_cast hdeg v
        have ht' : (t : ℝ) < (p : ℝ) * X + 1 := Nat.ceil_lt_add_one (by positivity)
        change (S.degree v : ℝ) ≤ ((p : ℝ) + 1) * X
        linarith only [hd, ht', hX]
      · let A := univ.filter fun v => t ≤ S.degree v
        have hsum : #A * t ≤ 2 * #S.edgeFinset := by
          rw [← S.sum_degrees_eq_twice_card_edges]
          calc
            _ = ∑ _v ∈ A, t := by simp
            _ ≤ ∑ v ∈ A, S.degree v := sum_le_sum fun v hv => (mem_filter.mp hv).2
            _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _
        have hcount : #A * p ≤ n := by
          have hl : (#A : ℝ) * ((p : ℝ) * X) ≤ #A * (t : ℝ) :=
            mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)
          have hs : (#A : ℝ) * t ≤ 2 * #S.edgeFinset := by exact_mod_cast hsum
          have : ((#A : ℝ) * p) * X ≤ n * X := by
            linarith only [hl, hs, not_le.mp hdense, Nat.cast_nonneg (α := ℝ) S.edgeFinset.card]
          exact_mod_cast le_of_mul_le_mul_right this hX'
        have hsmall : 2 * #S.edgeFinset ≤ #G.edgeFinset := by
          have : 2 * (#S.edgeFinset : ℝ) ≤ #G.edgeFinset := by
            linarith only [not_le.mp hdense, hden, Nat.cast_nonneg (α := ℝ) S.edgeFinset.card]
          exact_mod_cast this
        obtain ⟨k, H, hHG, hk, he⟩ := concentrer hp hpn G S hSG A hcount hsmall (by
          intro u v huv hnot
          simpa [A] using hsat u v huv hnot)
        have hkq : k * q ≤ n := by dsimp [p] at hk; nlinarith only [hk]
        have hkn : k < n := by nlinarith only [hkq, Nat.mul_le_mul_left k hq, hn]
        have hkpos : 0 < k := by
          by_contra! h
          have hkz : k = 0 := by omega
          have he0 : #H.edgeFinset = 0 := Nat.eq_zero_of_le_zero ((aretes_le_carre H).trans (by simp [hkz]))
          have hg0 : #G.edgeFinset = 0 := by simpa [he0] using he
          rw [hg0, Nat.cast_zero] at hE
          exact (not_lt_of_ge hE) (mul_pos hD (Real.rpow_pos_of_pos hn' _))
        have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
        have hg : (2 : ℝ) * p ≤ (q : ℝ) ^ (1 + δ) := by
          rw [Real.rpow_add hqpos, Real.rpow_one]
          dsimp [p]
          push_cast
          nlinarith only [mul_le_mul_of_nonneg_left hgain hqpos.le]
        have hstep : (k : ℝ) ^ (1 + δ) * (2 * (p : ℝ)) ≤ (n : ℝ) ^ (1 + δ) := calc
          _ ≤ (k : ℝ) ^ (1 + δ) * (q : ℝ) ^ (1 + δ) :=
            mul_le_mul_of_nonneg_left hg (by positivity)
          _ = ((k : ℝ) * q) ^ (1 + δ) := (Real.mul_rpow (by positivity) hqpos.le).symm
          _ ≤ _ := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hkq) (by linarith)
        have hE' : D * (k : ℝ) ^ (1 + δ) ≤ #H.edgeFinset := by
          have he' : (#G.edgeFinset : ℝ) ≤ 2 * p * (#H.edgeFinset : ℝ) := by exact_mod_cast he
          refine le_of_mul_le_mul_right (a := 2 * (p : ℝ)) ?_ (by positivity)
          linarith only [mul_le_mul_of_nonneg_left hstep hD.le, hE, he']
        obtain ⟨m, F, hm, hFH, hf, hd⟩ := ih k hkn hkpos
          ((Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hkn.le) hδ.le).trans hdom) H hE'
        exact ⟨m, F, hm, hFH.trans hHG, hf, hd⟩
    · refine ⟨n, G, hsize, IsContained.of_le le_rfl, ?_, ?_⟩
      · rw [hid]
        linarith only [hden, Nat.cast_nonneg (α := ℝ) G.edgeFinset.card]
      · intro v
        have hd : G.degree v ≤ p := (by simpa using (G.degree_lt_card_verts v).le : G.degree v ≤ n).trans (by omega)
        change (G.degree v : ℝ) ≤ ((p : ℝ) + 1) * X
        exact (by exact_mod_cast hd : (G.degree v : ℝ) ≤ p).trans
          ((by linarith : (p : ℝ) ≤ p + 1).trans (le_mul_of_one_le_right (by positivity) hX))

/-- Lemme 2.9 affaibli (exposant `γ > 0` existentiel), prouvé directement : tout graphe à `n`
sommets et au moins `n^{1+α}` arêtes contient un sous-graphe à `m ≥ n^γ` sommets, au moins
`m^{1+α}/3` arêtes et de degré maximal au plus `K m^α`. -/
theorem regularizationW :
    ∀ α : ℝ, 0 < α → α < 1 → ∃ K : ℝ, 0 < K ∧ ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), (n : ℝ) ^ (1 + α) ≤ #G.edgeFinset →
      ∃ m : ℕ, ∃ G' : SimpleGraph (Fin m), (n : ℝ) ^ γ ≤ m ∧ G' ⊑ G ∧
        (m : ℝ) ^ (1 + α) / 3 ≤ #G'.edgeFinset ∧ ∀ v, (G'.degree v : ℝ) ≤ K * (m : ℝ) ^ α := by
  classical
  intro α hα _
  let δ := α / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hα' : α = δ + δ := by dsimp [δ]; ring
  obtain ⟨r, hr⟩ := exists_nat_ge ((8 : ℝ) ^ δ⁻¹)
  let q := r + 2
  have hq : 2 ≤ q := by dsimp [q]; omega
  have hgain : 8 ≤ (q : ℝ) ^ δ := by
    calc
      _ = ((8 : ℝ) ^ δ⁻¹) ^ δ := (Real.rpow_inv_rpow (by norm_num) hδ.ne').symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (hr.trans (by exact_mod_cast (by dsimp [q]; omega : r ≤ q))) hδ.le
  refine ⟨((4*q : ℕ) + 1 : ℝ), by positivity, δ, hδ, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  intro G hG
  rw [hα'] at hG ⊢
  apply regulariser hδ (Real.rpow_pos_of_pos (by exact_mod_cast hn) δ) hq hgain n hn le_rfl G
  rw [← Real.rpow_add (by exact_mod_cast hn : (0 : ℝ) < n)]
  convert hG using 2
  ring

/-- L'étape 1 découle des lemmes 2.14 et 2.15, selon que le nombre de 4-cycles est petit ou
grand. -/
theorem step1_of_few_many (h14 : H1) (h15 : H2) :
    ∀ ε K : ℝ, 0 < ε → ε < 1 / 6 → 0 < K → ∀ k : ℕ, 1 / ε ≤ k → ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        let c4 : Finset (Fin n × Fin n × Fin n × Fin n) := univ.filter fun t =>
          G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2.1 ∧ G.Adj t.2.2.1 t.2.2.2 ∧ G.Adj t.2.2.2 t.1 ∧
            t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2
        let nxt : Fin (8 * k) → Fin (8 * k) := fun i => ⟨(i.val + 1) % (8 * k), Nat.mod_lt _ i.pos⟩
        (n : ℝ) ^ (4 / 3 + ε) / 6 ≤ #G.edgeFinset →
        (∀ v, (G.degree v : ℝ) ≤ K * (n : ℝ) ^ (1 / 3 + ε)) →
        (∀ e ∈ G.edgeFinset, (#(c4.filter fun t => e = s(t.1, t.2.1) ∨ e = s(t.2.1, t.2.2.1) ∨
            e = s(t.2.2.1, t.2.2.2) ∨ e = s(t.2.2.2, t.1)) : ℝ) ≤
            96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * #c4) →
        ∃ C : Finset (Fin (8 * k) → Fin n), C.Nonempty ∧ ∃ s : ℝ, 0 < s ∧
          (∀ x ∈ C, Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))) ∧
          (∀ y ∈ C, ∀ i, (#(C.filter fun x => ∀ j, j ≠ i → x j = y j) : ℝ) ≤ s) ∧
          ∀ i : Fin (8 * k), ∃ P : Finset (Fin (8 * k) → Fin n),
            (#P : ℝ) ≤ (n : ℝ) ^ (-(ε / 2)) * #C / (16 * k * s) ∧
            ∀ x ∈ C, ∃ y ∈ P, ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j := by
  intro ε K hε hε6 hK k hk
  filter_upwards [h14 ε K hε hε6 hK k hk, h15 ε K hε hε6 hK k hk, eventually_ge_atTop 2]
    with n h14n h15n hn2
  intro G c4 nxt hE hdeg hu
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hP : (0 : ℝ) < (n : ℝ) ^ (4 / 3 + ε) := Real.rpow_pos_of_pos (by linarith) _
  by_cases hq : 8 * (n : ℝ) ^ (5 / 3 + 3 * ε) / (96 * Real.log n) ≤ #c4
  · exact h15n G hdeg hq hu
  · push Not at hq
    apply h14n G hE hdeg
    intro e he
    refine (hu e he).trans ?_
    have hsplit : (n : ℝ) ^ (5 / 3 + 3 * ε) =
        (n : ℝ) ^ (4 / 3 + ε) * (n : ℝ) ^ (1 / 3 + 2 * ε) := by
      rw [← Real.rpow_add (by linarith)]
      congr 1
      ring
    calc 96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * #c4
        ≤ 96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) *
            (8 * (n : ℝ) ^ (5 / 3 + 3 * ε) / (96 * Real.log n)) := by
          apply mul_le_mul_of_nonneg_left hq.le
          positivity
      _ = 8 * (n : ℝ) ^ (1 / 3 + 2 * ε) := by
          rw [hsplit]
          field_simp

/- La cardinalité d'un filtre ne dépend pas de l'instance de décision du prédicat. -/
private theorem filtre_borne {V : Type*} {P : V → Prop} {d e : DecidablePred P}
    {S : Finset V} {t : ℝ} (h : (#(@Finset.filter _ P d S) : ℝ) ≤ t) :
    (#(@Finset.filter _ P e S) : ℝ) ≤ t := Subsingleton.elim d e ▸ h

private theorem filtres_proportion {V : Type*} {P Q : V → Prop} {d e : DecidablePred P}
    {f g : DecidablePred Q} {S : Finset V} {β : ℝ}
    (h : (#(@Finset.filter _ P d S) : ℝ) ≤ β * #(@Finset.filter _ Q f S)) :
    (#(@Finset.filter _ P e S) : ℝ) ≤ β * #(@Finset.filter _ Q g S) := by
  cases Subsingleton.elim d e
  cases Subsingleton.elim f g
  exact h

/-- Théorème 1.3 : pour `0 < ε < 1/6`, `k ≥ 1/ε`, `ℓ ≥ 16k/ε`, tout graphe à `n` sommets
(`n` grand) et au moins `n^{4/3+ε}` arêtes contient `H_{k,ℓ}`. -/
theorem thm13 (h1 : H1) (h2 : H2) (h3 : H3) (ε : ℝ) (hε : 0 < ε)
    (hε6 : ε < 1 / 6) (k ℓ : ℕ) (hk : 1 / ε ≤ k) (hl : 16 * k / ε ≤ ℓ) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ (4 / 3 + ε) ≤ #G.edgeFinset →
      SimpleGraph.fromRel (fun a b : Fin (4 * k) × Fin (2 * ℓ) =>
        (a.1.val + 1 = b.1.val ∧
          (if a.1.val % 2 = 0 then a.2 = b.2
           else (a.2.val + 1) % (2 * ℓ) = b.2.val ∨ (b.2.val + 1) % (2 * ℓ) = a.2.val)) ∨
        (a.1 = b.1 ∧ (a.1.val = 0 ∨ a.1.val + 1 = 4 * k) ∧ (a.2.val + 1) % (2 * ℓ) = b.2.val)) ⊑ G := by
  -- paramètres
  set α : ℝ := 1 / 3 + ε with hαdef
  have hα0 : 0 < α := by positivity
  have hα1 : α < 1 := by linarith
  have hk1r : (1 : ℝ) ≤ k := by
    have : (1 : ℝ) ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
    linarith
  have hk1 : 1 ≤ k := by exact_mod_cast hk1r
  have hl2 : 2 ≤ ℓ := by
    have h16 : (2 : ℝ) ≤ 16 * k / ε := by rw [le_div_iff₀ hε]; nlinarith
    exact_mod_cast h16.trans hl
  obtain ⟨K, hK, γ, hγ, hRegN⟩ := regularizationW α hα0 hα1
  have hS1' := step1_of_few_many h1 h2 ε K hε hε6 hK k hk
  have hS3' := E147Step3.step3_of_H3 h3 (ε / 2) (by positivity) k ℓ hk1 hl2 (by
    have : 8 * (k : ℝ) / (ε / 2) = 16 * k / ε := by field_simp; ring
    rw [this]; exact hl)
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hS1'.and (hS3'.and (eventually_ge_atTop 1)))
  have hγev : ∀ᶠ n : ℕ in atTop, (M : ℝ) ≤ (n : ℝ) ^ γ :=
    ((tendsto_rpow_atTop hγ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (M : ℝ)
  filter_upwards [hRegN, hγev] with n hn hnM
  intro G hG
  have hexp : (1 + α : ℝ) = 4 / 3 + ε := by rw [hαdef]; ring
  obtain ⟨m, G', hm, hG'G, hG'e, hG'deg⟩ := hn G (by rw [hexp]; exact hG)
  have hmM : M ≤ m := by exact_mod_cast hnM.trans hm
  obtain ⟨hS1m, hS3m, hm1⟩ := hM m hmM
  have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hm0r : (0 : ℝ) < m := by linarith
  have hpow0 : (0 : ℝ) < (m : ℝ) ^ (4 / 3 + ε) := Real.rpow_pos_of_pos hm0r _
  have hG'e' : (m : ℝ) ^ (4 / 3 + ε) / 3 ≤ #G'.edgeFinset := by rw [← hexp]; exact hG'e
  have hne : G'.edgeFinset.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < #G'.edgeFinset := lt_of_lt_of_le (by positivity) hG'e'
    exact_mod_cast this
  obtain ⟨F, hFG', hFe, hFc4⟩ := clean_c4 G' hne
  have hFe' : (m : ℝ) ^ (4 / 3 + ε) / 6 ≤ #F.edgeFinset := by linarith
  have hFpos : (0 : ℝ) < #F.edgeFinset := lt_of_lt_of_le (by positivity) hFe'
  have hdeg : ∀ v, (F.degree v : ℝ) ≤ K * (m : ℝ) ^ (1 / 3 + ε) := by
    intro v
    have h1 : F.degree v ≤ G'.degree v := by
      apply Finset.card_le_card
      intro w hw
      simp only [mem_neighborFinset] at hw ⊢
      exact hFG' hw
    calc (F.degree v : ℝ) ≤ G'.degree v := by exact_mod_cast h1
      _ ≤ K * (m : ℝ) ^ α := hG'deg v
  obtain ⟨C, hCne, hCgood⟩ := hS1m F hFe' hdeg (by
    intro e he
    refine (hFc4 e he).trans ?_
    have hlog : 0 ≤ Real.log m := Real.log_nonneg hm1r
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [div_le_div_iff₀ hFpos hpow0]
    nlinarith)
  obtain ⟨D, -, hDne, hDnice⟩ :=
    good_imp_nice F k hk1 ((m : ℝ) ^ (-(ε / 2))) (Real.rpow_pos_of_pos hm0r _) C hCne
      (fun i => ⟨(i.val + 1) % (8 * k), Nat.mod_lt _ i.pos⟩) (by
        obtain ⟨s, hs, hcyc, hfix, hrepr⟩ := hCgood
        exact ⟨s, hs, hcyc, fun y hy i => filtre_borne (hfix y hy i), hrepr⟩)
  have hcopy := hS3m F D hDne ⟨hDnice.1, fun i y u => filtres_proportion (hDnice.2 i y u)⟩
  exact (hcopy.trans (IsContained.of_le hFG')).trans hG'G

/-- Passage de `Fin (4k) × Fin (2ℓ)` à `Fin q`. -/
theorem transfer (h1 : H1) (h2 : H2) (h3 : H3) (ε : ℝ) (hε : 0 < ε) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsBipartite ∧ H.IsRegularOfDegree 3 ∧
      (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (4 / 3 + ε : ℝ) := by
  set ε₀ : ℝ := min ε (1 / 12) with hε₀
  have hε₀pos : 0 < ε₀ := lt_min hε (by norm_num)
  have hε₀12 : ε₀ ≤ 1 / 12 := min_le_right _ _
  have hε₀6 : ε₀ < 1 / 6 := lt_of_le_of_lt hε₀12 (by norm_num)
  have hε₀le : ε₀ ≤ ε := min_le_left _ _
  set k : ℕ := ⌈1 / ε₀⌉₊ with hkdef
  set ℓ : ℕ := ⌈16 * k / ε₀⌉₊ with hldef
  have hk : 1 / ε₀ ≤ k := Nat.le_ceil _
  have hl : 16 * k / ε₀ ≤ ℓ := Nat.le_ceil _
  let e := finProdFinEquiv (m := 4 * k) (n := 2 * ℓ)
  have hk1 : (1 : ℝ) ≤ k := by
    have : (1 : ℝ) ≤ 1 / ε₀ := by rw [le_div_iff₀ hε₀pos]; linarith
    linarith
  have hl0 : 0 < ℓ := by
    have : (0 : ℝ) < 16 * k / ε₀ := by positivity
    exact_mod_cast this.trans_le hl
  have hk0 : 0 < k := by exact_mod_cast (show (0 : ℝ) < k by linarith)
  let Hk : SimpleGraph (Fin (4 * k) × Fin (2 * ℓ)) := SimpleGraph.fromRel fun a b =>
        (a.1.val + 1 = b.1.val ∧
          (if a.1.val % 2 = 0 then a.2 = b.2
           else (a.2.val + 1) % (2 * ℓ) = b.2.val ∨ (b.2.val + 1) % (2 * ℓ) = a.2.val)) ∨
        (a.1 = b.1 ∧ (a.1.val = 0 ∨ a.1.val + 1 = 4 * k) ∧ (a.2.val + 1) % (2 * ℓ) = b.2.val)
  refine ⟨4 * k * (2 * ℓ), Hk.map e.toEmbedding, by positivity, ?_, ?_, ?_⟩
  · exact Colorable.of_hom (SimpleGraph.Iso.map e Hk).symm.toHom (hkl_bipartite k ℓ)
  · intro v
    have hd1 := (SimpleGraph.Iso.map e Hk).degree_eq (e.symm v)
    have hd2 := hkl_regular k ℓ (by exact_mod_cast hk1) (by
      have : (2 : ℝ) ≤ ℓ := by
        have h16 : (2 : ℝ) ≤ 16 * k / ε₀ := by
          rw [le_div_iff₀ hε₀pos]; nlinarith
        linarith
      exact_mod_cast this) (e.symm v)
    have hd3 : (SimpleGraph.Iso.map e Hk) (e.symm v) = v := by
      simp [SimpleGraph.Iso.map]
    rw [hd3] at hd1
    convert hd1.trans hd2 using 2
    rfl
  · have hcongr : ∀ n, extremalNumber n (Hk.map e.toEmbedding) =
        extremalNumber n Hk := fun n =>
      extremalNumber_congr_right (SimpleGraph.Iso.map e Hk).symm
    simp_rw [hcongr]
    exact bigO_of_eventually_contains Hk (4 / 3 + ε₀) (4 / 3 + ε) (by linarith)
      (thm13 h1 h2 h3 ε₀ hε₀pos hε₀6 k ℓ hk hl)

end E147

namespace OMA.R_Erdos147_erdos_147_variants_cubic_R1

theorem main : H1 → H2 → H3 → type_of% @Erdos147.erdos_147.variants.cubic := by
  intro h1 h2 h3 ε hε
  exact E147.transfer h1 h2 h3 ε hε

end OMA.R_Erdos147_erdos_147_variants_cubic_R1
