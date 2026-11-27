import FormalConjectures.ErdosProblems.«1069»

/-! # Rich lines via the crossing inequality

Székely's proof of the Szemerédi–Trotter bound draws straight segments between
consecutive points of each rich line. The two steps below isolate its planar
edge inequality and the segment construction. Random sampling, crossing
deletion, and the optimization in both density regimes are proved here.
Credit: @JaviSoto. -/

/- The random sampling part of the graph crossing lemma, by exact finite counting. -/

namespace OMA.Crossing

open Finset

private theorem samples_containing {V : Type*} [Fintype V] [DecidableEq V] (r : ℕ) (A : Finset V) :
    (univ.filter (fun f : V → Fin (r+1) => A ⊆ (univ.filter (fun v => f v = 0)))).card =
      (r+1)^(Fintype.card V-A.card) := by
  classical
  let t (v : V) : Finset (Fin (r+1)) := if v ∈ A then {0} else univ
  have he : univ.filter (fun f : V → Fin (r+1) => A ⊆ (univ.filter (fun v => f v = 0))) = Fintype.piFinset t := by
    ext f
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h v
      by_cases hv : v ∈ A
      · have hv' := h hv
        simpa [t,hv] using hv'
      · simp [t,hv]
    · intro h v hv
      have hv' := h v
      simpa [t,hv] using hv'
  rw [he, Fintype.card_piFinset]
  have hc (v : V) : (t v).card = if v ∈ A then 1 else r+1 := by
    by_cases hv : v ∈ A <;> simp [t,hv]
  simp_rw [hc]
  rw [prod_ite]
  simp [show (univ.filter fun v => v ∉ A) = Aᶜ by ext; simp, card_compl]

private theorem sum_surviving {V α : Type*} [Fintype V] [DecidableEq V]
    (r j : ℕ) (E : Finset α) (verts : α → Finset V) (hj : ∀ e ∈ E, (verts e).card = j) :
    ∑ f : V → Fin (r+1), (E.filter (fun e => verts e ⊆ (univ.filter (fun v => f v = 0)))).card =
      E.card * (r+1)^(Fintype.card V-j) := by
  classical
  calc
    _ = ∑ e ∈ E, (univ.filter (fun f : V → Fin (r+1) => verts e ⊆ (univ.filter (fun v => f v = 0)))).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := (univ : Finset (V → Fin (r+1)))) (t := E)
        (fun (f : V → Fin (r+1)) (e : α) => verts e ⊆ univ.filter (fun v => f v = 0))
    _ = _ := by
      simp only [samples_containing]
      rw [sum_congr rfl (fun e he => by rw [hj e he])]
      simp

/-- Suppose every induced subdrawing satisfies the linear planarization inequality:
the number of surviving edges is at most three times the vertices plus the surviving
crossings. For edges supported on pairs and crossings supported on four distinct vertices,
sampling a 1/r fraction of the vertices amplifies this to a cubic crossing bound. -/
theorem sample_crossing_bound {V α β : Type*} [Fintype V] [DecidableEq V]
    (E : Finset α) (C : Finset β) (edge : α → Finset V) (cross : β → Finset V)
    (he : ∀ e ∈ E, (edge e).card = 2) (hc : ∀ c ∈ C, (cross c).card = 4)
    (hV : 4 ≤ Fintype.card V)
    (planar : ∀ S : Finset V, (E.filter (fun e => edge e ⊆ S)).card ≤
        3 * S.card + (C.filter (fun c => cross c ⊆ S)).card)
    (r : ℕ) (hr : 1 ≤ r) :
    E.card * r^2 ≤ 3 * Fintype.card V * r^3 + C.card := by
  classical
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  let n := Fintype.card V
  have h := sum_le_sum (s := (univ : Finset (V → Fin (r+1)))) (fun f _ => planar ((univ.filter (fun v => f v = 0))))
  have hvertex (f : V → Fin (r+1)) :
      (univ.filter (fun e : V => ({e} : Finset V) ⊆ (univ.filter (fun v => f v = 0)))).card = ((univ.filter (fun v => f v = 0))).card := by simp
  have hvertices := sum_surviving (V := V) r 1 univ (fun e : V => {e}) (by simp)
  simp_rw [hvertex,card_univ] at hvertices
  rw [sum_add_distrib, ← mul_sum, hvertices, sum_surviving _ _ _ _ he, sum_surviving _ _ _ _ hc] at h
  have hpow (j : ℕ) (hj : j ≤ 4) :
      (r+1)^(Fintype.card V-j) = (r+1)^(4-j) * (r+1)^(Fintype.card V-4) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow 2 (by decide), hpow 1 (by decide)] at h
  norm_num at h
  apply Nat.le_of_mul_le_mul_right _ (pow_pos (by omega : 0 < r+1) (n-4))
  simpa only [n, Nat.succ_eq_add_one, add_mul, mul_assoc] using h

/-- A drawing with at least 12 edges per vertex and the planarization inequality
has at least e³/(288 v²) crossings. -/
theorem cubic_crossing_bound {V α β : Type*} [Fintype V] [DecidableEq V]
    (E : Finset α) (C : Finset β) (edge : α → Finset V) (cross : β → Finset V)
    (he : ∀ e ∈ E, (edge e).card = 2) (hc : ∀ c ∈ C, (cross c).card = 4)
    (hV : 4 ≤ Fintype.card V) (hdense : 12 * Fintype.card V ≤ E.card)
    (planar : ∀ S : Finset V, (E.filter (fun e => edge e ⊆ S)).card ≤
        3 * S.card + (C.filter (fun c => cross c ⊆ S)).card) :
    E.card^3 ≤ 288 * (Fintype.card V)^2 * C.card := by
  let n := Fintype.card V
  let r := E.card / (6*n)
  have hn : 0 < n := by dsimp [n]; omega
  have hr : 1 ≤ r := (Nat.le_div_iff_mul_le (by omega)).mpr (by dsimp [n] at *; omega)
  have hsplit := sample_crossing_bound E C edge cross he hc hV planar r hr
  have hu : r * (6*n) ≤ E.card := Nat.div_mul_le_self _ _
  have hq : E.card ≤ 12*n*r := by
    have hlt : E.card < (r+1)*(6*n) := (Nat.div_lt_iff_lt_mul (by omega)).mp (Nat.lt_succ_self r)
    have hrr : r+1 ≤ 2*r := by omega
    exact hlt.le.trans ((Nat.mul_le_mul_right _ hrr).trans_eq (by ring))
  have hcross : E.card*r^2 ≤ 2*C.card := by
    change E.card * r^2 ≤ 3*n*r^3 + C.card at hsplit
    nlinarith only [hsplit, Nat.mul_le_mul_right (r^2) hu]
  calc
    E.card^3 = E.card^2 * E.card := by ring
    _ ≤ (12*n*r)^2 * E.card := by gcongr
    _ = (144*n^2) * (E.card*r^2) := by ring
    _ ≤ (144*n^2) * (2*C.card) := Nat.mul_le_mul_left _ hcross
    _ = _ := by change _ = 288*n^2*C.card; ring

end OMA.Crossing

namespace OMA.R_Erdos1069_erdos_1069_R1

open Finset EuclideanGeometry
open scoped EuclideanGeometry Classical

/-- Euler's linear edge bound for a straight-line drawing with disjoint edge interiors. -/
def H1 : Prop :=
  ∀ (Q : Finset ℝ²) (S : Finset Q) (E : Finset ℕ) (edge : ℕ → Finset Q) (curve : ℕ → Set ℝ²),
  (∀ i ∈ E, ∃ x y : Q, x ≠ y ∧ edge i = {x,y} ∧
    curve i = segment ℝ (x : ℝ²) (y : ℝ²) ∧
      ∀ v : Q, (v : ℝ²) ∈ curve i → v ∈ edge i) →
  (∀ i ∈ E, edge i ⊆ S) → Set.InjOn edge (E : Set ℕ) →
  (∀ i ∈ E, ∀ j ∈ E, i ≠ j → curve i ∩ curve j ⊆ Subtype.val '' ((edge i ∩ edge j : Finset Q) : Set Q)) →
  E.card ≤ 3 * S.card

/-- Consecutive points on each line yield distinct edges. Two different
lines have at most one proper crossing, while segments on the same line have
disjoint interiors. The ordered exceptional pairs are counted here. -/
def H2 : Prop :=
  ∀ (Q : Finset ℝ²) (L : Finset (AffineSubspace ℝ ℝ²)) (k : ℕ), 2 ≤ k →
  (∀ l ∈ L, IsLine l ∧ k ≤ ((Q : Set ℝ²) ∩ (l : Set ℝ²)).ncard) →
  ∃ (E : Finset ℕ) (edge : ℕ → Finset Q) (curve : ℕ → Set ℝ²) (C : Finset (ℕ × ℕ)),
  (∀ i ∈ E, ∃ x y : Q, x ≠ y ∧ edge i = {x,y} ∧
    curve i = segment ℝ (x : ℝ²) (y : ℝ²) ∧
    ∀ v : Q, (v : ℝ²) ∈ curve i → v ∈ edge i) ∧
  Set.InjOn edge (E : Set ℕ) ∧
  (∀ i ∈ E, ∀ j ∈ E, i ≠ j → (i,j) ∉ C → curve i ∩ curve j ⊆ Subtype.val '' ((edge i ∩ edge j : Finset Q) : Set Q)) ∧
  (∀ ij ∈ C, (edge ij.1 ∪ edge ij.2).card = 4) ∧
  (k-1)*L.card ≤ E.card ∧ C.card ≤ L.card^2

/-- Removing the first edge of each crossing suffices for every induced subdrawing. -/
theorem induced_edges {Q : Finset ℝ²} (planar : H1) (E : Finset ℕ) (edge : ℕ → Finset Q)
    (curve : ℕ → Set ℝ²) (C : Finset (ℕ × ℕ))
    (drawn : ∀ i ∈ E, ∃ x y : Q, x ≠ y ∧ edge i = {x,y} ∧
      curve i = segment ℝ (x : ℝ²) (y : ℝ²) ∧
        ∀ v : Q, (v : ℝ²) ∈ curve i → v ∈ edge i)
    (inj : Set.InjOn edge (E : Set ℕ))
    (meet : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → (i,j) ∉ C → curve i ∩ curve j ⊆ Subtype.val '' ((edge i ∩ edge j : Finset Q) : Set Q))
    (S : Finset Q) : (E.filter (fun i => edge i ⊆ S)).card ≤ 3 * S.card +
      (C.filter (fun ij => edge ij.1 ∪ edge ij.2 ⊆ S)).card := by
  let F := E.filter (fun i => edge i ⊆ S)
  let K := C.filter (fun ij => edge ij.1 ∪ edge ij.2 ⊆ S)
  let G := F \ K.image Prod.fst
  have hsub {i} (hi : i ∈ G) : i ∈ F := (mem_sdiff.mp hi).1
  have hE {i} (hi : i ∈ G) : i ∈ E := (mem_filter.mp (hsub hi)).1
  have hgood : G.card ≤ 3 * S.card := by
    apply planar Q S G edge curve (fun i hi => drawn i (hE hi))
      (fun _ hi => (mem_filter.mp (hsub hi)).2) (fun _ hi _ hj eq => inj (hE hi) (hE hj) eq)
    intro i hi j hj hij
    apply meet i (hE hi) j (hE hj) hij
    intro hc
    exact (mem_sdiff.mp hi).2 (mem_image.mpr ⟨(i,j), mem_filter.mpr
      ⟨hc, union_subset (mem_filter.mp (hsub hi)).2 (mem_filter.mp (hsub hj)).2⟩, rfl⟩)
  calc F.card ≤ G.card + (K.image Prod.fst).card := card_le_card_sdiff_add_card
       _ ≤ 3 * S.card + K.card := Nat.add_le_add hgood card_image_le

/-- If the graph is sparse, use k² ≤ n. If it is dense, cancel two
powers of the line count in the cubic crossing inequality. -/
theorem rich_estimate {n k m e c : ℕ} (hk : 2 ≤ k) (hs : k^2 ≤ n)
    (he : (k-1)*m ≤ e) (hc : c ≤ m^2) (cross : 12*n ≤ e → e^3 ≤ 288*n^2*c) :
    m * k^3 ≤ 2304*n^2 := by
  have hkm : k*m ≤ 2*e := by
    have h := Nat.mul_le_mul_right m (show k ≤ 2*(k-1) by omega)
    nlinarith only [he,h]
  by_cases dense : 12*n ≤ e
  · by_cases hm : m = 0
    · simp [hm]
    have hpow : (k*m)^3 ≤ (2*e)^3 := Nat.pow_le_pow_left hkm _
    have hbound := (cross dense).trans (Nat.mul_le_mul_left _ hc)
    apply Nat.le_of_mul_le_mul_left (c := m^2) _ (by positivity)
    nlinarith only [hpow,hbound]
  · have h : m*k ≤ 24*n := by nlinarith only [hkm, show e < 12*n by omega]
    calc m*k^3 = (m*k)*k^2 := by ring
         _ ≤ (24*n)*n := Nat.mul_le_mul h hs
         _ ≤ 2304*n^2 := by nlinarith

theorem main : H1 → H2 → type_of% @Erdos1069.erdos_1069 := by
  classical
  intro planar draw
  refine ⟨2304, by norm_num, ?_⟩
  intro n k Q hcard hk hk'
  subst n
  let L := (Erdos1069.richLines_finite Q hk).toFinset
  have hlines : ∀ l ∈ L, IsLine l ∧ k ≤ ((Q : Set ℝ²) ∩ (l : Set ℝ²)).ncard := by
    intro l hl
    change l ∈ Erdos1069.richLines Q k
    simpa only [L, Set.Finite.mem_toFinset] using hl
  obtain ⟨E,edge,curve,C,drawn,inj,meet,four,he,hc⟩ := draw Q L k hk hlines
  have hs : k^2 ≤ Q.card := by
    exact_mod_cast (Real.le_sqrt (by positivity) (by positivity)).mp hk'
  have hV : 4 ≤ Q.card := (by norm_num : 4 ≤ 2^2).trans ((Nat.pow_le_pow_left hk 2).trans hs)
  have two (i) (hi : i ∈ E) : (edge i).card = 2 := by
    obtain ⟨x,y,hne,he,_⟩ := drawn i hi
    simp [he,hne]
  have num := rich_estimate hk hs he hc (fun dense => by
    simpa only [Fintype.card_coe] using OMA.Crossing.cubic_crossing_bound E C edge
      (fun ij => edge ij.1 ∪ edge ij.2) two four
      (by simpa only [Fintype.card_coe] using hV) (by simpa only [Fintype.card_coe] using dense)
      (induced_edges planar E edge curve C drawn inj meet))
  rw [Set.ncard_eq_toFinset_card _ (Erdos1069.richLines_finite Q hk)]
  apply (le_div_iff₀ (by positivity : 0 < (k:ℝ)^3)).mpr
  exact_mod_cast num

end OMA.R_Erdos1069_erdos_1069_R1
