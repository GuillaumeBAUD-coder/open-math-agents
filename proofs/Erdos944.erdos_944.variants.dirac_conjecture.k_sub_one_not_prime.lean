import FormalConjectures.ErdosProblems.«944»
import Mathlib

/-!
# The composite case of the Dirac conjecture

Write `k - 1 = a * b`, with both factors at least two. The vertices are residues
modulo `4 * a * b + 1`. Two distinct residues are nonadjacent if their difference
is a horizontal, vertical, or diagonal king move with row width `2 * a`.

After deleting any vertex, the remaining rectangle splits into `a * b` two-by-two
tiles. Each tile needs one color. Conversely, after any single edge deletion,
an independent set still has at most four vertices. Pigeonhole counting gives
the lower chromatic bound, and one extra color suffices for the omitted vertex.

Credit: @desenyon
-/

namespace Erdos944Grid

open SimpleGraph
open scoped Fin.CommRing Fin.NatCast Fin.IntCast

abbrev Patch := Fin 3 × Fin 3

def Close (p q : Patch) : Prop :=
  p.1.val ≤ q.1.val + 1 ∧ q.1.val ≤ p.1.val + 1 ∧
  p.2.val ≤ q.2.val + 1 ∧ q.2.val ≤ p.2.val + 1

instance (p q : Patch) : Decidable (Close p q) := by unfold Close; infer_instance

-- Three four-colorings of the king's graph on a three-by-three square.
-- A phase shift in the last row or column separates any given pair.
def paint (mode : Fin 3) (p : Patch) : Fin 2 × Fin 2 :=
  (⟨(p.1.val + (if mode = 1 then p.2.val / 2 else 0)) % 2, by omega⟩,
   ⟨(p.2.val + (if mode = 2 then p.1.val / 2 else 0)) % 2, by omega⟩)

set_option maxRecDepth 4096 in
lemma paint_proper : ∀ (m : Fin 3) (p q : Patch),
    Close p q → paint m p = paint m q → p = q := by decide

set_option maxRecDepth 4096 in
lemma paint_separates : ∀ p q : Patch, ∃ m : Fin 3,
    p ≠ q → paint m p ≠ paint m q := by decide

def position {n : ℕ} [NeZero n] (a : ℕ) (p : Patch) : Fin n :=
  (((p.1.val : ℤ) - 1 + 2 * (a : ℤ) * ((p.2.val : ℤ) - 1) : ℤ) : Fin n)

def grid (a b : ℕ) : SimpleGraph (Fin (4 * a * b + 1)) :=
  let w : Fin (4 * a * b + 1) := 2 * (a : Fin _)
  (circulantGraph ({1, w, w + 1, w - 1} : Set _))ᶜ

lemma offset_of_nonedge {a b : ℕ} {x y : Fin (4 * a * b + 1)}
    (h : ¬ (grid a b).Adj x y) : ∃ p : Patch, x = y + position a p := by
  by_cases he : x = y
  · exact ⟨(1, 1), by simp [position, he]⟩
  have hc := Classical.byContradiction (fun h' => h ((compl_adj _ _ _).mpr ⟨he, h'⟩))
  have jump := ((circulantGraph_adj ..).mp hc).2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at jump
  rcases jump with (h | h | h | h) | (h | h | h | h)
  · exact ⟨(2, 1), by norm_num [position]; linear_combination h⟩
  · exact ⟨(1, 2), by norm_num [position]; linear_combination h⟩
  · exact ⟨(2, 2), by norm_num [position]; linear_combination h⟩
  · exact ⟨(0, 2), by norm_num [position]; linear_combination h⟩
  · exact ⟨(0, 1), by norm_num [position]; linear_combination -h⟩
  · exact ⟨(1, 0), by norm_num [position]; linear_combination -h⟩
  · exact ⟨(0, 0), by norm_num [position]; linear_combination -h⟩
  · exact ⟨(2, 0), by norm_num [position]; linear_combination -h⟩

-- No nonzero relation in this box can wrap around the modulus or span one row.
lemma local_relation (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (dx dy : ℤ)
    (hx : -3 ≤ dx ∧ dx ≤ 3) (hy : -3 ≤ dy ∧ dy ≤ 3)
    (rel : ((dx + 2 * (a : ℤ) * dy : ℤ) : Fin (4 * a * b + 1)) = 0) :
    dx = 0 ∧ dy = 0 := by
  have ha' : (2 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (2 : ℤ) ≤ b := by exact_mod_cast hb
  have dvd := (CharP.intCast_eq_zero_iff (Fin (4 * a * b + 1)) (4 * a * b + 1) _).mp rel
  have z : dx + 2 * (a : ℤ) * dy = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd dvd
    push_cast
    rw [abs_lt]
    constructor <;> nlinarith [mul_nonneg (show (0:ℤ) ≤ a by omega) (show 0 ≤ dy + 3 by omega),
      mul_nonneg (show (0:ℤ) ≤ a by omega) (show 0 ≤ 3 - dy by omega),
      mul_nonneg (show (0:ℤ) ≤ a by omega) (show 0 ≤ (b:ℤ) - 2 by omega)]
  have dy0 : dy = 0 := by
    by_contra h
    rcases lt_or_gt_of_ne h with h | h
    · nlinarith [mul_nonneg (show (0:ℤ) ≤ a by omega) (show 0 ≤ -1 - dy by omega)]
    · nlinarith [mul_nonneg (show (0:ℤ) ≤ a by omega) (show 0 ≤ dy - 1 by omega)]
  exact ⟨by simpa [dy0] using z, dy0⟩

lemma close_of_nonedge {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (v : Fin (4 * a * b + 1)) (p q : Patch)
    (h : ¬ (grid a b).Adj (v + position a p) (v + position a q)) : Close p q := by
  obtain ⟨d, hd⟩ := offset_of_nonedge h
  let dx := (p.1.val : ℤ) - q.1.val - (d.1.val - 1 : ℤ)
  let dy := (p.2.val : ℤ) - q.2.val - (d.2.val - 1 : ℤ)
  have rel : ((dx + 2 * (a : ℤ) * dy : ℤ) : Fin (4 * a * b + 1)) = 0 := by
    dsimp [dx, dy, position] at *
    push_cast at *
    linear_combination hd
  have bounds := local_relation a b ha hb dx dy
    (by dsimp [dx]; have := p.1.isLt; have := q.1.isLt; have := d.1.isLt; omega)
    (by dsimp [dy]; have := p.2.isLt; have := q.2.isLt; have := d.2.isLt; omega) rel
  dsimp [dx, dy] at bounds
  have := d.1.isLt
  have := d.2.isLt
  unfold Close
  omega

lemma independent_bound {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (e : Sym2 (Fin (4 * a * b + 1))) (S : Finset (Fin (4 * a * b + 1)))
    (ind : ((grid a b).deleteEdges {e}).IsIndepSet (S : Set _)) : S.card ≤ 4 := by
  classical
  induction e using Sym2.inductionOn with
  | _ l r =>
    have exception {x y} (hx : x ∈ S) (hy : y ∈ S) (h : (grid a b).Adj x y) :
        x = l ∧ y = r ∨ x = r ∧ y = l := by
      apply Sym2.eq_iff.mp
      by_contra hn
      exact ind hx hy h.ne (deleteEdges_adj.mpr ⟨h, hn⟩)
    by_cases small : S ⊆ {l, r}
    · have h := Finset.card_le_card small
      have hr := Finset.card_insert_le l ({r} : Finset _)
      simp only [Finset.card_singleton] at hr
      omega
    obtain ⟨v, hv, hnot⟩ : ∃ x ∈ S, x ∉ ({l, r} : Finset _) := by
      by_contra! h
      exact small h
    have neighbors (x : S) : ∃ p : Patch, x.val = v + position a p := by
      apply offset_of_nonedge
      intro hadj
      rcases exception x.property hv hadj with h | h <;> simp_all
    choose coord hcoord using neighbors
    have coord_inj : Function.Injective coord := by
      intro x y eq
      exact Subtype.ext (by rw [hcoord x, hcoord y, eq])
    let get (x : Fin (4 * a * b + 1)) : Patch :=
      if h : x ∈ S then coord ⟨x, h⟩ else (1, 1)
    obtain ⟨m, sep⟩ := paint_separates (get l) (get r)
    have inj : Function.Injective (fun x : S => paint m (coord x)) := by
      intro x y eq
      by_cases close : Close (coord x) (coord y)
      · exact coord_inj (paint_proper m _ _ close eq)
      have adj : (grid a b).Adj x.val y.val := by
        by_contra hn
        apply close
        apply close_of_nonedge ha hb v
        simpa only [← hcoord x, ← hcoord y] using hn
      have different : coord x ≠ coord y := fun h => adj.ne (congrArg Subtype.val (coord_inj h))
      have ex := exception x.property y.property adj
      have gx : get x.val = coord x := by simp [get, x.property]
      have gy : get y.val = coord y := by simp [get, y.property]
      obtain ⟨hl, hr⟩ | ⟨hr, hl⟩ := ex
      · rw [← hl, ← hr, gx, gy] at sep
        exact (sep different eq).elim
      · rw [← hl, ← hr, gy, gx] at sep
        exact (sep different.symm eq.symm).elim
    simpa using Fintype.card_le_of_injective _ inj


-- All four corners of a tile form a clique in the circulant.
lemma corners {n : ℕ} [NeZero n] (w t x y : Fin n)
    (hx : x = t ∨ x = t + 1 ∨ x = t + w ∨ x = t + w + 1)
    (hy : y = t ∨ y = t + 1 ∨ y = t + w ∨ y = t + w + 1)
    (hne : x ≠ y) :
    (circulantGraph ({1, w, w + 1, w - 1} : Set (Fin n))).Adj x y := by
  rw [circulantGraph_adj]
  refine ⟨hne, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first | exact (hne rfl).elim | ring_nf <;> tauto

lemma tiling (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    let w : Fin (4 * a * b + 1) := 2 * (a : Fin _)
    let G := (circulantGraph ({1, w, w + 1, w - 1} : Set (Fin (4 * a * b + 1))))ᶜ
    ∀ v, ∃ c : Fin (4 * a * b + 1) → Fin (a * b),
      ∀ x y, x ≠ v → y ≠ v → G.Adj x y → c x ≠ c y := by
  classical
  let w : Fin (4 * a * b + 1) := 2 * (a : Fin (4 * a * b + 1))
  dsimp only
  intro v
  let rank (x : Fin (4 * a * b + 1)) := (x - v).val - 1
  let col (x : Fin (4 * a * b + 1)) := rank x % (2 * a)
  let row (x : Fin (4 * a * b + 1)) := rank x / (2 * a)
  have rank_lt (x : Fin (4 * a * b + 1)) : rank x < 4 * a * b := by
    have := (x - v).isLt
    have : 0 < 4 * a * b := by positivity
    dsimp [rank] at *
    omega
  have col_lt (x : Fin (4 * a * b + 1)) : col x < 2 * a := Nat.mod_lt _ (by omega)
  have row_lt (x : Fin (4 * a * b + 1)) : row x < 2 * b := by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * a)).mpr
    simpa only [show 2 * b * (2 * a) = 4 * a * b by ring] using rank_lt x
  let label (x : Fin (4 * a * b + 1)) : Fin a × Fin b :=
    (⟨col x / 2, by have := col_lt x; omega⟩,
     ⟨row x / 2, by have := row_lt x; omega⟩)
  let base (ij : Fin a × Fin b) : Fin (4 * a * b + 1) :=
    v + 1 + ((2 * ij.1.val + (2 * a) * (2 * ij.2.val) : ℕ) : Fin (4 * a * b + 1))
  have in_tile (x : Fin (4 * a * b + 1)) (hx : x ≠ v) :
      x = base (label x) ∨ x = base (label x) + 1 ∨
      x = base (label x) + w ∨ x = base (label x) + w + 1 := by
    have pos : 0 < (x - v).val := Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr (sub_ne_zero.mpr hx))
    have rank_eq : rank x + 1 = (x - v).val := by dsimp [rank]; omega
    have repr : x = v + 1 + (rank x : Fin (4 * a * b + 1)) := by
      have cast_eq : ((rank x + 1 : ℕ) : Fin (4 * a * b + 1)) = ((x - v).val : Fin (4 * a * b + 1)) := congrArg _ rank_eq
      simp only [Nat.cast_add, Nat.cast_one, Fin.cast_val_eq_self] at cast_eq
      linear_combination -cast_eq
    have split_rank : col x + (2 * a) * row x = rank x := Nat.mod_add_div _ _
    have cp : col x = 2 * (col x / 2) ∨ col x = 2 * (col x / 2) + 1 := by omega
    have rp : row x = 2 * (row x / 2) ∨ row x = 2 * (row x / 2) + 1 := by omega
    let z := 2 * (col x / 2) + (2 * a) * (2 * (row x / 2))
    have steps : rank x = z ∨ rank x = z + 1 ∨ rank x = z + 2 * a ∨ rank x = z + 2 * a + 1 := by
      rcases rp with h | h <;> rcases cp with g | g
      · exact Or.inl (by dsimp [z]; rw [← g, ← h]; omega)
      · exact Or.inr (Or.inl (by dsimp [z]; rw [← h]; omega))
      · exact Or.inr (Or.inr (Or.inl (by dsimp [z]; rw [← g]; nlinarith only [split_rank, congrArg (fun r => 2 * a * r) h])))
      · exact Or.inr (Or.inr (Or.inr (by dsimp [z]; nlinarith only [split_rank, g, congrArg (fun r => 2 * a * r) h])))
    change x = v + 1 + (z : Fin (4 * a * b + 1)) ∨ x = v + 1 + (z : Fin (4 * a * b + 1)) + 1 ∨
      x = v + 1 + (z : Fin (4 * a * b + 1)) + w ∨ x = v + 1 + (z : Fin (4 * a * b + 1)) + w + 1
    rcases steps with h | h | h | h
    · exact Or.inl (by simpa only [h] using repr)
    · exact Or.inr (Or.inl (by rw [repr, h]; push_cast; ring))
    · exact Or.inr (Or.inr (Or.inl (by rw [repr, h]; push_cast; dsimp [w]; ring)))
    · exact Or.inr (Or.inr (Or.inr (by rw [repr, h]; push_cast; dsimp [w]; ring)))
  refine ⟨fun x => finProdFinEquiv (label x), ?_⟩
  intro x y hx hy adj eq
  have same := finProdFinEquiv.injective eq
  have cy := in_tile y hy
  rw [← same] at cy
  exact adj.2 (corners w (base (label x)) x y (in_tile x hx) cy adj.1)

universe u

lemma witness_of_four_vertex_classes {W : Type} [Fintype W] [Nonempty W]
    (G : SimpleGraph W) (q : ℕ) (size : Fintype.card W = 4 * q + 1)
    (tile : ∀ v, ∃ c : W → Fin q, ∀ x y, x ≠ v → y ≠ v → G.Adj x y → c x ≠ c y)
    (bound : ∀ (e : Sym2 W) (S : Finset W),
      (G.deleteEdges {e}).IsIndepSet (S : Set W) → S.card ≤ 4) :
    ∃ (V : Type u) (J : SimpleGraph V), Erdos944.SimpleGraph.IsErdos944 J (q + 1) 1 := by
  classical
  let V := ULift.{u} W
  let point : V := ULift.up (Classical.choice (inferInstance : Nonempty W))
  letI : Nonempty (Sym2 V) := ⟨Sym2.mk point point⟩
  let J := G.comap (ULift.down : V → W)
  refine ⟨V, J, ?_⟩
  have lower (E : Set (Sym2 V)) (hE : E.ncard ≤ 1) : ¬ (J.deleteEdges E).Colorable q := by
    obtain ⟨e, he⟩ := (Set.ncard_le_one_iff_subset_singleton).mp hE
    rintro ⟨c⟩
    let f : W → Fin q := fun x => c (ULift.up x)
    obtain ⟨i, hi⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f (n := 4)
      (by rw [Fintype.card_fin, size, Nat.mul_comm q 4]; omega)
    apply (Nat.not_lt_of_ge (bound (e.map ULift.down) (Finset.univ.filter (fun x => f x = i)) ?_)) hi
    intro x hx y hy _ hadj
    have hxy : (J.deleteEdges E).Adj (ULift.up x) (ULift.up y) := by
      refine deleteEdges_adj.mpr ⟨(deleteEdges_adj.mp hadj).1, ?_⟩
      intro hm
      apply (deleteEdges_adj.mp hadj).2
      exact congrArg (Sym2.map ULift.down) (Set.mem_singleton_iff.mp (he hm))
    exact c.valid hxy (((Finset.mem_filter.mp hx).2).trans ((Finset.mem_filter.mp hy).2).symm)
  obtain ⟨c, hc⟩ := tile (Classical.choice (inferInstance : Nonempty W))
  let v := Classical.choice (inferInstance : Nonempty W)
  have upper : J.Colorable (q + 1) := by
    refine ⟨Coloring.mk (fun x : V => if x.down = v then Fin.last q else (c x.down).castSucc) ?_⟩
    intro x y hxy
    change G.Adj x.down y.down at hxy
    split_ifs with hx hy hy
    · exact (hxy.ne (hx.trans hy.symm)).elim
    · exact (Fin.castSucc_ne_last _).symm
    · exact Fin.castSucc_ne_last _
    · exact fun h => hc _ _ hx hy hxy (Fin.castSucc_injective _ h)
  have chi : J.chromaticNumber = (q : ℕ∞) + 1 :=
    chromaticNumber_eq_iff_colorable_not_colorable.mpr
      ⟨upper, by simpa only [deleteEdges_empty] using lower ∅ (by simp)⟩
  constructor
  · refine ⟨by simpa using chi, ?_⟩
    intro x
    obtain ⟨d, hd⟩ := tile x.down
    let K := (⊤ : J.Subgraph).deleteVerts {x}
    have hK : K.coe.Colorable q := by
      refine ⟨Coloring.mk (fun y : K.verts => d y.val.down) ?_⟩
      intro y z hyz
      apply hd
      · exact fun h => y.property.2 (ULift.ext _ _ h)
      · exact fun h => z.property.2 (ULift.ext _ _ h)
      · exact K.adj_sub hyz
    change K.coe.chromaticNumber < (⊤ : J.Subgraph).coe.chromaticNumber
    rw [chromaticNumber_congr (Subgraph.topIso (G := J)), chi]
    exact lt_of_le_of_lt hK.chromaticNumber_le (by exact_mod_cast Nat.lt_succ_self q)
  · intro E hcrit
    by_contra! hE
    have hle : ((q + 1 : ℕ) : ℕ∞) ≤ (J.deleteEdges E).chromaticNumber := by
      apply (le_chromaticNumber_iff_not_colorable (by omega : q + 1 ≠ 0)).mpr
      simpa using lower E hE
    exact (not_lt_of_ge (show J.chromaticNumber ≤ _ by simpa [chi] using hle)) hcrit

end Erdos944Grid

open Erdos944Grid

theorem OMA.solution : type_of% @Erdos944.erdos_944.variants.dirac_conjecture.k_sub_one_not_prime := by
  intro k hk hcomposite
  obtain ⟨a, b, ha, hb, hab⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega : 2 ≤ k - 1)).mp hcomposite
  have ha2 : 2 ≤ a := by
    by_contra! h
    interval_cases a <;> simp_all <;> omega
  have hb2 : 2 ≤ b := by
    by_contra! h
    interval_cases b <;> simp_all <;> omega
  have hk' : k = a * b + 1 := by omega
  rw [hk']
  exact witness_of_four_vertex_classes (grid a b) (a * b) (by simp [Nat.mul_assoc])
    (tiling a b ha2 hb2) (independent_bound ha2 hb2)
