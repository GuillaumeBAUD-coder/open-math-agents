import OMAReductions.R_Erdos23_erdos_23_variants_n5_R1_H2_R1
import Mathlib

-- Problem: Erdős Problem 23 — n5, step R1.H2.R1.H3
-- Credit: @hyprspacecoyote (the owner of the agent is credited as the solver)

/-! A degree-13 root whose 11-vertex core is not bipartite.

The neighbourhood cut gives the core at least 26 edges. Every triangle-free graph on
11 vertices with at least 26 edges is, up to isomorphism, one of 34 explicit graphs:
this is proved by induction on the number of vertices (delete a vertex of minimum
degree), each extension being matched to a listed graph by an explicit permutation
checked by the kernel. Of the 34, the non-bipartite ones are full blow-ups of C5.
Every neighbour of the root sees an independent set of the core, whose image in C5
lies in the two neighbours of one vertex, so the graph minus the root maps to C5.
The five-cut argument of reduction R3 (lemma exceptional, with the interval
certificate of R3.H1 by STARDUSTLC666) then gives a cut with at most 25 same-side edges.
-/

namespace R3Copy
open Finset SimpleGraph
open scoped Classical

def R3H1 : Prop := ∀ a t : Fin 5 → ℕ, (∑ i, a i) = 24 → t ≤ a →
  ∃ i, a i*a (i+1) + min (t i+t (i+1)+t (i+3)) (t (i+2)+t (i+4)) ≤ 25+t i*t (i+1)


end R3Copy

namespace FiveCycleBound

abbrev Row := Fin 5 → ℕ

def allThrough (p : ℕ → Bool) : ℕ → Bool
  | 0 => p 0
  | n + 1 => p (n + 1) && allThrough p n

lemma get {p : ℕ → Bool} {n x : ℕ} (h : allThrough p n = true) (hx : x ≤ n) :
    p x = true := by
  induction n with
  | zero => simpa [allThrough, Nat.eq_zero_of_le_zero hx] using h
  | succ n ih =>
    obtain ⟨top, rest⟩ := Bool.and_eq_true_iff.mp h
    rcases Nat.eq_or_lt_of_le hx with eq | lt
    · simpa [eq] using top
    · exact ih rest (by omega)

def edge (a lo hi : Row) (i j k m n : Fin 5) : Bool :=
  decide (a i * a j + min (hi i + hi j + hi m) (hi k + hi n) ≤ 25 + lo i * lo j)

def box (a lo hi : Row) : Bool :=
  edge a lo hi 0 1 2 3 4 || edge a lo hi 1 2 3 4 0 ||
  edge a lo hi 2 3 4 0 1 || edge a lo hi 3 4 0 1 2 || edge a lo hi 4 0 1 2 3

def Good (a t : Row) : Prop :=
  ∃ i, a i * a (i+1) + min (t i + t (i+1) + t (i+3)) (t (i+2) + t (i+4)) ≤
    25 + t i * t (i+1)

lemma edge_sound {a lo hi t : Row} {i j k m n : Fin 5}
    (h : edge a lo hi i j k m n = true) (lower : lo ≤ t) (upper : t ≤ hi) :
    a i * a j + min (t i + t j + t m) (t k + t n) ≤ 25 + t i * t j := by
  have he := of_decide_eq_true h
  exact (Nat.add_le_add_left (min_le_min
    (Nat.add_le_add (Nat.add_le_add (upper i) (upper j)) (upper m))
    (Nat.add_le_add (upper k) (upper n))) _).trans
    (he.trans (Nat.add_le_add_left (Nat.mul_le_mul (lower i) (lower j)) _))

lemma box_sound {a lo hi t : Row} (h : box a lo hi = true) (lower : lo ≤ t)
    (upper : t ≤ hi) : Good a t := by
  simp only [box, Bool.or_eq_true] at h
  rcases h with (((h | h) | h) | h) | h
  · exact ⟨0, edge_sound h lower upper⟩
  · exact ⟨1, edge_sound h lower upper⟩
  · exact ⟨2, edge_sound h lower upper⟩
  · exact ⟨3, edge_sound h lower upper⟩
  · exact ⟨4, edge_sound h lower upper⟩

-- An edge passing on the whole box witnesses every point in it.
-- Otherwise fix the next coordinate and test each resulting smaller box.
def checkBox (a lo hi : Row) : List (Fin 5) → Bool
  | [] => box a lo hi
  | i :: rest => box a lo hi || allThrough (fun x =>
      checkBox a (Function.update lo i x) (Function.update hi i x) rest) (hi i)

lemma checkBox_sound {a t : Row} (indices : List (Fin 5)) {lo hi : Row}
    (h : checkBox a lo hi indices = true) (lower : lo ≤ t) (upper : t ≤ hi) :
    Good a t := by
  induction indices generalizing lo hi with
  | nil => exact box_sound h lower upper
  | cons i rest ih =>
    rcases Bool.or_eq_true_iff.mp h with hit | split
    · exact box_sound hit lower upper
    · apply ih (get split (upper i))
      · intro j
        by_cases e : j = i
        · simp [e]
        · simpa [Function.update_of_ne e] using lower j
      · intro j
        by_cases e : j = i
        · simp [e]
        · simpa [Function.update_of_ne e] using upper j

-- Rotate a smallest class into position zero. Subtract its size from each
-- class, leaving four nonnegative entries whose sum is 24 - 5*m.
def slice (p : Row → Bool) (m : ℕ) : Bool :=
  let r := 24 - 5*m
  allThrough (fun b => allThrough (fun c => allThrough (fun d =>
    p ![m, m+b, m+c, m+d, m+(r-b-c-d)]) (r-b-c)) (r-b)) r

lemma slice_sound {p : Row → Bool} (a : Row) (total : ∑ i, a i = 24)
    (least : ∀ i, a 0 ≤ a i) (h : slice p (a 0) = true) : p a = true := by
  rw [Fin.sum_univ_five] at total
  have h1 := least 1
  have h2 := least 2
  have h3 := least 3
  have h4 := least 4
  let m := a 0
  let r := 24 - 5*m
  have hb := get h (show a 1 - m ≤ r by dsimp [r, m]; omega)
  have hc := get hb (show a 2 - m ≤ r - (a 1-m) by dsimp [r, m]; omega)
  have hd := get hc (show a 3 - m ≤ r - (a 1-m) - (a 2-m) by dsimp [r, m]; omega)
  change p ![m, m+(a 1-m), m+(a 2-m), m+(a 3-m),
    m+(r-(a 1-m)-(a 2-m)-(a 3-m))] = true at hd
  have last : m+(r-(a 1-m)-(a 2-m)-(a 3-m)) = a 4 := by dsimp [r, m]; omega
  rw [last, show m+(a 1-m) = a 1 by dsimp [m]; omega,
    show m+(a 2-m) = a 2 by dsimp [m]; omega,
    show m+(a 3-m) = a 3 by dsimp [m]; omega] at hd
  convert hd using 2
  funext i
  fin_cases i <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate (m : ℕ) (positive : 1 ≤ m) (small : m ≤ 4) :
    slice (fun a => checkBox a (fun _ => 0) a [0, 1, 2, 3, 4]) m = true := by
  interval_cases m <;> decide +kernel

lemma least_good (a t : Row) (total : ∑ i, a i = 24) (upper : t ≤ a)
    (least : ∀ i, a 0 ≤ a i) : Good a t := by
  have sum := total
  rw [Fin.sum_univ_five] at sum
  by_cases zero : a 0 = 0
  · refine ⟨0, ?_⟩
    change a 0 * a 1 + min (t 0 + t 1 + t 3) (t 2 + t 4) ≤ 25 + t 0 * t 1
    rw [zero, zero_mul, zero_add]
    exact (min_le_right _ _).trans
      ((Nat.add_le_add (upper 2) (upper 4)).trans (by omega))
  · have small : a 0 ≤ 4 := by
      have := least 1; have := least 2; have := least 3; have := least 4; omega
    exact checkBox_sound _ (slice_sound a total least (certificate _ (by omega) small))
      (fun _ => Nat.zero_le _) upper


theorem r3h1 : R3Copy.R3H1 := by
  intro a t total upper
  obtain ⟨r, _, least⟩ := Finset.exists_min_image Finset.univ a Finset.univ_nonempty
  let b (i : Fin 5) := a (r+i)
  let u (i : Fin 5) := t (r+i)
  have rotated : ∑ i, b i = 24 :=
    (Fintype.sum_equiv (Equiv.addLeft r) b a (fun _ => rfl)).trans total
  have lb (i : Fin 5) : b 0 ≤ b i := by
    simpa [b] using least (r+i) (Finset.mem_univ _)
  obtain ⟨i, hi⟩ := least_good b u rotated (fun j => upper (r+j)) lb
  exact ⟨r+i, by simpa [b, u, add_assoc] using hi⟩

end FiveCycleBound

namespace R3Copy
open Finset SimpleGraph
open scoped Classical

lemma erase_total {V : Type*} [DecidableEq V] (W : Finset V) {x : V} (hx : x∈W)
    (w : V → V → ℕ) (sym : ∀ i j,w i j = w j i) (diag : w x x=0) :
    (∑ i ∈ W, ∑ j ∈ W, w i j) =
      (∑ i ∈ W.erase x, ∑ j ∈ W.erase x, w i j) + 2*(∑ j ∈ W.erase x,w x j) := by
  let T := W.erase x
  have nx : x∉T := notMem_erase _ _
  have eqW : insert x T = W := insert_erase hx
  change (∑ i ∈ W, ∑ j ∈ W, w i j) = (∑ i ∈ T,∑ j ∈ T,w i j)+2*∑ j ∈ T,w x j
  conv_lhs => rw [←eqW]
  simp only [sum_insert nx,diag,zero_add,sum_add_distrib]
  have swap : (∑ i ∈ T,w i x) = ∑ i ∈ T,w x i := sum_congr rfl (fun i _ => sym i x)
  omega

lemma exceptional (cert : R3H1) (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (x : Fin 25) (g : Fin 25 → Fin 5)
    (hom : ∀ u v, u ≠ x → v ≠ x → G.Adj u v → g u+1=g v ∨ g v+1=g u) :
    ∃ f : Fin 25 → Bool, (∑ u, ∑ v, if G.Adj u v ∧ f u=f v then 1 else 0) ≤ (50:ℕ) := by
  classical
  let W := univ.erase x
  let tag (i : Fin 5) (u : Fin 25) : ℕ := if g u=i then 1 else 0
  let nbr (i : Fin 5) (u : Fin 25) : ℕ := if G.Adj x u then tag i u else 0
  let a (i : Fin 5) := ∑ u ∈ W, tag i u
  let t (i : Fin 5) := ∑ u ∈ W, nbr i u
  have total : ∑ i, a i = 24 := by
    dsimp [a]
    rw [sum_comm]
    simp [tag,W]
  have sub (i u) : nbr i u ≤ tag i u := by by_cases h : G.Adj x u <;> simp [nbr,h]
  obtain ⟨i,small⟩ := cert a t total (fun i => sum_le_sum fun u _ => sub i u)
  let paint (i j : Fin 5) : Bool := decide (j=i ∨ j=i+1 ∨ j=i+3)
  have onlyPair : ∀ i j k : Fin 5, (j+1=k ∨ k+1=j) → paint i j=paint i k →
      (j=i ∧ k=i+1) ∨ (j=i+1 ∧ k=i) := by decide
  let col (u : Fin 25) := paint i (g u)
  let cost (u v : Fin 25) : ℕ := if G.Adj u v ∧ col u=col v then 1 else 0
  have bound (u) (hu : u∈W) (v) (hv : v∈W) :
      cost u v + (nbr i u*nbr (i+1) v + nbr (i+1) u*nbr i v) ≤
      tag i u*tag (i+1) v + tag (i+1) u*tag i v := by
    by_cases good : G.Adj u v ∧ col u=col v
    · have no : ¬(G.Adj x u ∧ G.Adj x v) :=
        fun h => tri _ (is3Clique_triple_iff.mpr ⟨h.1,h.2,good.1⟩)
      have vanish (j k : Fin 5) : nbr j u*nbr k v = 0 := by
        by_cases e : G.Adj x u
        · simp [nbr,e, show ¬G.Adj x v from fun ev => no ⟨e,ev⟩]
        · simp [nbr,e]
      rw [vanish,vanish]
      rcases onlyPair i _ _ (hom _ _ (mem_erase.mp hu).1 (mem_erase.mp hv).1 good.1) good.2 with hh|hh <;>
        simp [cost,good,tag,hh.1,hh.2]
    · simp only [cost,if_neg good,zero_add]
      exact Nat.add_le_add (Nat.mul_le_mul (sub ..) (sub ..)) (Nat.mul_le_mul (sub ..) (sub ..))
  have box (p q : Fin 25 → ℕ) :
      (∑ u ∈ W, ∑ v ∈ W, p u*q v) = (∑ u ∈ W,p u)*(∑ v ∈ W,q v) := by
    simp only [mul_sum,sum_mul]
    rw [sum_comm]
  have core := sum_le_sum (s := W) (fun u hu => sum_le_sum (s := W) (fun v hv => bound u hu v hv))
  simp only [sum_add_distrib,box] at core
  change _ + (t i*t (i+1)+t (i+1)*t i) ≤ a i*a (i+1)+a (i+1)*a i at core
  rw [Nat.mul_comm (t (i+1)), Nat.mul_comm (a (i+1))] at core
  let count (b : Bool) := ∑ u ∈ W, if G.Adj x u ∧ b=col u then (1:ℕ) else 0
  have rows : ∀ i j : Fin 5,
      (if true=paint i j then 1 else 0) =
        (if j=i then 1 else 0)+(if j=i+1 then 1 else 0)+(if j=i+3 then 1 else (0:ℕ)) ∧
      (if false=paint i j then 1 else 0) =
        (if j=i+2 then 1 else 0)+(if j=i+4 then 1 else (0:ℕ)) := by decide
  have ct : count true = t i + t (i+1) + t (i+3) := by
    simp only [count,t,←sum_add_distrib]
    apply sum_congr rfl
    intro u _
    by_cases h : G.Adj x u
    · simpa [col,tag,nbr,h] using (rows i (g u)).1
    · simp [h,nbr]
  have cf : count false = t (i+2)+t (i+4) := by
    simp only [count,t,←sum_add_distrib]
    apply sum_congr rfl
    intro u _
    by_cases h : G.Adj x u
    · simpa [col,tag,nbr,h] using (rows i (g u)).2
    · simp [h,nbr]
  obtain ⟨b,hb⟩ : ∃ b, count b = min (t i + t (i+1)+t (i+3)) (t (i+2)+t (i+4)) := by
    rw [←ct,←cf]
    rcases le_total (count true) (count false) with h|h
    · exact ⟨true,(min_eq_left h).symm⟩
    · exact ⟨false,(min_eq_right h).symm⟩
  let f (u : Fin 25) := if u=x then b else col u
  let w (u v : Fin 25) : ℕ := if G.Adj u v ∧ f u=f v then 1 else 0
  have sy (u v) : w u v=w v u := by simp [w,G.adj_comm u v,eq_comm]
  have parts := erase_total univ (mem_univ x) w sy (by simp [w])
  have row : (∑ u ∈ W,w x u) = count b := by
    apply sum_congr rfl
    intro u hu
    simp [w,f,(mem_erase.mp hu).1]
  have keep : (∑ u ∈ W,∑ v ∈ W,w u v) = ∑ u ∈ W,∑ v ∈ W,cost u v := by
    apply sum_congr rfl
    intro u hu
    apply sum_congr rfl
    intro v hv
    simp [w,cost,f,(mem_erase.mp hu).1,(mem_erase.mp hv).1]
  change (∑ u,∑ v,w u v) = (∑ u ∈ W,∑ v ∈ W,w u v)+2*(∑ u ∈ W,w x u) at parts
  rw [keep,row,hb] at parts
  exact ⟨f,by change (∑ u,∑ v,w u v) ≤ 50; omega⟩

end R3Copy

namespace TFClass
open Finset

abbrev Gr (k : ℕ) := Fin k → Fin k → Bool

def adjOf (k b : ℕ) : Gr k := fun i j => b.testBit (i.val * k + j.val)

def ecount {k : ℕ} (A : Gr k) : ℕ := ∑ i, ∑ j, if A i j then 1 else 0

def deg {k : ℕ} (A : Gr k) (x : Fin k) : ℕ := ∑ j, if A x j then 1 else 0

structure Good {k : ℕ} (A : Gr k) : Prop where
  symm : ∀ i j, A i j = A j i
  irrefl : ∀ i, A i i = false
  tf : ∀ i j l, A i j = true → A j l = true → A i l = true → False

def Classified (k : ℕ) (L : List ℕ) (t : ℕ) : Prop :=
  ∀ A : Gr k, Good A → t ≤ ecount A →
    ∃ b ∈ L, ∃ σ : Equiv.Perm (Fin k), ∀ i j, A (σ i) (σ j) = adjOf k b i j

def ext {n : ℕ} (B : Gr n) (N : Fin n → Bool) : Gr (n+1) :=
  fun i j => Fin.cases (Fin.cases false N j) (fun i' => Fin.cases (N i') (B i') j) i

def pf (k : ℕ) (p : List ℕ) (i : Fin (k+1)) : Fin (k+1) :=
  ⟨(p.getD i.val 0) % (k+1), Nat.mod_lt _ (Nat.succ_pos k)⟩

def PermOK (k : ℕ) (p q : List ℕ) : Prop :=
  ∀ i : Fin (k+1), pf k q (pf k p i) = i ∧ pf k p (pf k q i) = i

def popc {n : ℕ} (m : ℕ) : ℕ := ∑ i : Fin n, if m.testBit i.val then 1 else 0

/-- certificate entries: (old graph, mask, new graph, perm, inverse perm). -/
def StepOK (n : ℕ) (Lp Ln : List ℕ) (t : ℕ)
    (certs : List (ℕ × ℕ × ℕ × List ℕ × List ℕ)) : Prop :=
  ∀ b ∈ Lp, ∀ m < 2^n,
    (∀ i j : Fin n, m.testBit i.val = true → m.testBit j.val = true → adjOf n b i j = false) →
    t ≤ ecount (adjOf n b) + 2 * popc (n := n) m →
    ∃ c ∈ certs, c.1 = b ∧ c.2.1 = m ∧ c.2.2.1 ∈ Ln ∧ PermOK n c.2.2.2.1 c.2.2.2.2 ∧
      ∀ i j : Fin (n+1), ext (adjOf n b) (fun x => m.testBit x.val)
        (pf n c.2.2.2.1 i) (pf n c.2.2.2.1 j) = adjOf (n+1) c.2.2.1 i j

instance (n : ℕ) (Lp Ln : List ℕ) (t : ℕ) (certs : List (ℕ × ℕ × ℕ × List ℕ × List ℕ)) :
    Decidable (StepOK n Lp Ln t certs) := by
  unfold StepOK PermOK; infer_instance

/-! Soundness. -/

lemma exists_mask : ∀ (n : ℕ) (N : Fin n → Bool), ∃ m < 2^n, ∀ i : Fin n, m.testBit i.val = N i
  | 0, _ => ⟨0, by simp, fun i => i.elim0⟩
  | n+1, N => by
    obtain ⟨m, hm, h⟩ := exists_mask n (fun i => N i.succ)
    refine ⟨2*m + (if N 0 then 1 else 0), ?_, ?_⟩
    · rw [pow_succ]; split <;> omega
    · intro i
      cases i using Fin.cases with
      | zero => simp only [Fin.val_zero, Nat.testBit_zero]; split <;> simp_all
      | succ i =>
        simp only [Fin.val_succ, Nat.testBit_succ]
        rw [← h i]; congr 1; split <;> omega

def permOfOK (k : ℕ) (p q : List ℕ) (h : PermOK k p q) : Equiv.Perm (Fin (k+1)) where
  toFun := pf k p
  invFun := pf k q
  left_inv i := (h i).1
  right_inv i := (h i).2

lemma ecount_perm {k : ℕ} (A : Gr k) (σ : Equiv.Perm (Fin k)) :
    ecount (fun i j => A (σ i) (σ j)) = ecount A := by
  unfold ecount
  rw [← Equiv.sum_comp σ (fun i => ∑ j, if A i j then 1 else 0)]
  apply Finset.sum_congr rfl; intro i _
  exact Equiv.sum_comp σ (fun j => if A (σ i) j then 1 else 0)

lemma deg_perm {k : ℕ} (A : Gr k) (σ : Equiv.Perm (Fin k)) (x : Fin k) :
    deg (fun i j => A (σ i) (σ j)) x = deg A (σ x) := by
  unfold deg
  exact Equiv.sum_comp σ (fun j => if A (σ x) j then 1 else 0)

lemma good_perm {k : ℕ} {A : Gr k} (hA : Good A) (σ : Equiv.Perm (Fin k)) :
    Good (fun i j => A (σ i) (σ j)) where
  symm i j := hA.symm _ _
  irrefl i := hA.irrefl _
  tf i j l h1 h2 h3 := hA.tf _ _ _ h1 h2 h3

lemma ecount_eq_sum_deg {k : ℕ} (A : Gr k) : ecount A = ∑ x, deg A x := rfl

lemma ecount_succ {n : ℕ} (A : Gr (n+1)) (hA : Good A) :
    ecount A = ecount (fun i j : Fin n => A i.succ j.succ) + 2 * deg A 0 := by
  unfold ecount deg
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ (f := fun j => if A _ j = true then 1 else 0)]
  rw [hA.irrefl 0]
  have hs : (∑ i : Fin n, if A i.succ 0 = true then 1 else 0) =
      ∑ j : Fin n, if A 0 j.succ = true then 1 else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [hA.symm]
  rw [Finset.sum_add_distrib, hs]
  simp only [Bool.false_eq_true, if_false, zero_add]
  ring

lemma good_succ {n : ℕ} {A : Gr (n+1)} (hA : Good A) : Good (fun i j : Fin n => A i.succ j.succ) where
  symm i j := hA.symm _ _
  irrefl i := hA.irrefl _
  tf i j l h1 h2 h3 := hA.tf _ _ _ h1 h2 h3

lemma min_deg {k : ℕ} (A : Gr (k+1)) : ∃ x, (k+1) * deg A x ≤ ecount A := by
  obtain ⟨x, -, hx⟩ := Finset.exists_min_image Finset.univ (deg A) Finset.univ_nonempty
  refine ⟨x, ?_⟩
  rw [ecount_eq_sum_deg]
  have := Finset.card_nsmul_le_sum Finset.univ (deg A) (deg A x) (fun y _ => hx y (mem_univ y))
  simpa using this

theorem step (n : ℕ) (Lp Ln : List ℕ) (tp tn : ℕ) (certs : List (ℕ × ℕ × ℕ × List ℕ × List ℕ))
    (hok : StepOK n Lp Ln tn certs)
    (hT : ∀ E d : ℕ, tn ≤ E → (n+1) * d ≤ E → tp + 2 * d ≤ E)
    (IH : Classified n Lp tp) : Classified (n+1) Ln tn := by
  intro A hA hE
  obtain ⟨x, hx⟩ := min_deg A
  let τ : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 x
  let A1 : Gr (n+1) := fun i j => A (τ i) (τ j)
  have g1 : Good A1 := good_perm hA τ
  have e1 : ecount A1 = ecount A := ecount_perm A τ
  have d1 : deg A1 0 = deg A x := by
    simp only [A1, deg_perm, τ, Equiv.swap_apply_left]
  let A0 : Gr n := fun i j => A1 i.succ j.succ
  have e0 : ecount A1 = ecount A0 + 2 * deg A1 0 := ecount_succ A1 g1
  obtain ⟨b', hb', σ', hσ'⟩ := IH A0 (good_succ g1) (by
    have := hT (ecount A) (deg A x) hE hx
    change tp ≤ ecount A0
    omega)
  let σ'' : Equiv.Perm (Fin (n+1)) := Equiv.Perm.decomposeFin.symm (0, σ')
  have s0 : σ'' 0 = 0 := Equiv.Perm.decomposeFin_symm_apply_zero _ _
  have ss : ∀ i : Fin n, σ'' i.succ = (σ' i).succ := by
    intro i
    simp [σ'', Equiv.Perm.decomposeFin_symm_apply_succ]
  let A2 : Gr (n+1) := fun i j => A1 (σ'' i) (σ'' j)
  have g2 : Good A2 := good_perm g1 σ''
  let N : Fin n → Bool := fun j => A2 0 j.succ
  have hext : ∀ i j, A2 i j = ext (adjOf n b') N i j := by
    intro i j
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => simp [ext, g2.irrefl]
      | succ j => simp [ext, N]
    | succ i =>
      cases j using Fin.cases with
      | zero => simp [ext, N, g2.symm (i.succ) 0]
      | succ j =>
        simp only [ext, Fin.cases_succ]
        rw [← hσ' i j]
        simp [A2, A0, ss]
  obtain ⟨m, hm, hmN⟩ := exists_mask n N
  have hN : (fun x : Fin n => m.testBit x.val) = N := funext hmN
  have indep : ∀ i j : Fin n, m.testBit i.val = true → m.testBit j.val = true →
      adjOf n b' i j = false := by
    intro i j hi hj
    rw [hmN] at hi hj
    by_contra hb
    have hb' : adjOf n b' i j = true := by simpa using hb
    have h3 : A2 i.succ j.succ = true := by
      rw [hext]; simpa [ext] using hb'
    exact g2.tf 0 i.succ j.succ hi h3 hj
  have cnt : tn ≤ ecount (adjOf n b') + 2 * popc (n := n) m := by
    have e2 := ecount_succ A2 g2
    have e2' : ecount A2 = ecount A1 := ecount_perm A1 σ''
    have eb : ecount (fun i j : Fin n => A2 i.succ j.succ) = ecount (adjOf n b') := by
      congr 1; funext i j; rw [hext]; simp [ext]
    have pc : deg A2 0 = popc (n := n) m := by
      unfold deg popc
      rw [Fin.sum_univ_succ, g2.irrefl]
      simp only [Bool.false_eq_true, if_false, zero_add]
      apply Finset.sum_congr rfl; intro j _; rw [hmN]
    omega
  obtain ⟨c, -, -, -, hcL, hcP, hcE⟩ := hok b' hb' m hm indep cnt
  let π := permOfOK n _ _ hcP
  refine ⟨c.2.2.1, hcL, π.trans (σ''.trans τ), ?_⟩
  intro i j
  have := hcE i j
  rw [hN] at this
  rw [← this, ← hext]
  rfl

theorem base : Classified 1 [0] 0 := by
  intro A hA _
  refine ⟨0, by simp, Equiv.refl _, ?_⟩
  intro i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp [hA.irrefl, adjOf]


def L1 : List ℕ := [0]

def L2 : List ℕ := [6]

def L3 : List ℕ := [170]

def L4 : List ℕ := [19026, 19268, 23130]

def L5 : List ℕ := [9087146, 10102962, 10167606]

def L6 : List ℕ := [18963801450, 20087122770, 21144353580]

def L7 : List ℕ := [152465478167210, 165830108549850]

def L8 : List ℕ := [4947860780934124842, 4948141160677463124, 5019917275460425098, 5019918374972052906, 5383290614320903498, 5455067837172004020]

def L9 : List ℕ := [645390076984985590999722, 650103238075101104351572, 650121630846210858636054, 650121648860609368118102, 702260994877317377239188, 706974156037664463727466]

def L10 : List ℕ := [337544580872724614391617901738, 337545788619104405006520242516, 338782519731418373949105722922, 338782520912009994666517026474, 340019253203762662821907309846, 341255985497821173986510938792, 340024081829251505351473804626, 341260814122155969111565841036, 341260814122157095011472683692, 340024084190434746786296542546, 341260816483340336446295421612, 368546222791744933032436737750, 371019687382163299164986495700]

def L11 : List ℕ := [707017121590449743059520504686356650, 707017121899783710904378826183844180, 707017755415598741446769424391121450, 707017755415749857174221253037959850, 708315195804932407990166381541368916, 708315195805083449930624331749698698, 708315196114417417811511450266150228, 707019022447682149713906106746880680, 708316462836864626742874940412087318, 708316462836864700529851235250293846, 708316463146349710351196303975075158, 709613269400747137231095615402977450, 709613903225896135618344535107742250, 710911343615229802161741492257989716, 710911343924714738196110266144564500, 710911343924714811983086560982771028, 709613270019566041146333924206225450, 709613270019566114897299005625770068, 709613270019717156837756955834099850, 709613903844866155261034663967894050, 709613903844866155261034672557828650, 710911344543684831625776698432857428, 712208785242050160808163232623714980, 716101107338355074174937490168382800, 712213852132141523136428863523201700, 713511292830809009986742783084670234, 713511292830809083773719077922876762, 714808099704176382722355954295818406, 712213853370081562421809139496067748, 713511294068749123059099353895742810, 716106175156750276452792647004374144, 771977215577453521385551478926436946, 773274656276423165975815170617599404, 777166344548031911844911613880387586]

def C2 : List (ℕ × ℕ × ℕ × List ℕ × List ℕ) := [
  (0, 1, 6, [0,1], [0,1])]

set_option maxRecDepth 100000 in
theorem ok2 : StepOK 1 L1 L2 1 C2 := by decide +kernel

theorem cl2 : Classified 2 L2 1 :=
  step 1 L1 L2 0 1 C2 ok2 (by intro E d h1 h2; omega) base

def C3 : List (ℕ × ℕ × ℕ × List ℕ × List ℕ) := [
  (6, 1, 170, [0,1,2], [0,1,2]),
  (6, 2, 170, [0,2,1], [0,2,1])]

set_option maxRecDepth 100000 in
theorem ok3 : StepOK 2 L2 L3 3 C3 := by decide +kernel

theorem cl3 : Classified 3 L3 3 :=
  step 2 L2 L3 1 3 C3 ok3 (by intro E d h1 h2; omega) cl2

def C4 : List (ℕ × ℕ × ℕ × List ℕ × List ℕ) := [
  (170, 1, 19026, [0,1,2,3], [0,1,2,3]),
  (170, 2, 19268, [0,1,2,3], [0,1,2,3]),
  (170, 4, 19026, [0,3,2,1], [0,3,2,1]),
  (170, 5, 23130, [0,1,2,3], [0,1,2,3])]

set_option maxRecDepth 100000 in
theorem ok4 : StepOK 3 L3 L4 6 C4 := by decide +kernel

theorem cl4 : Classified 4 L4 6 :=
  step 3 L3 L4 3 6 C4 ok4 (by intro E d h1 h2; omega) cl3

def C5 : List (ℕ × ℕ × ℕ × List ℕ × List ℕ) := [
  (19026, 5, 9087146, [0,1,2,3,4], [0,1,2,3,4]),
  (19026, 9, 10102962, [0,1,2,3,4], [0,1,2,3,4]),
  (19026, 10, 9087146, [0,4,3,2,1], [0,4,3,2,1]),
  (19268, 3, 9087146, [2,0,1,3,4], [1,2,0,3,4]),
  (19268, 9, 9087146, [4,0,1,3,2], [1,2,4,3,0]),
  (19268, 10, 9087146, [4,0,2,3,1], [1,4,2,3,0]),
  (19268, 11, 10167606, [0,1,2,3,4], [0,1,2,3,4]),
  (23130, 1, 9087146, [4,3,2,1,0], [4,3,2,1,0]),
  (23130, 2, 9087146, [3,4,1,2,0], [4,2,3,0,1]),
  (23130, 4, 9087146, [4,1,2,3,0], [4,1,2,3,0]),
  (23130, 5, 10167606, [3,0,2,1,4], [1,3,2,0,4]),
  (23130, 8, 9087146, [3,2,1,4,0], [4,2,1,0,3]),
  (23130, 10, 10167606, [4,0,1,2,3], [1,2,3,4,0])]

set_option maxRecDepth 100000 in
theorem ok5 : StepOK 4 L4 L5 10 C5 := by decide +kernel

theorem cl5 : Classified 5 L5 10 :=
  step 4 L4 L5 6 10 C5 ok5 (by intro E d h1 h2; omega) cl4

def C6 : List (ℕ × ℕ × ℕ × List ℕ × List ℕ) := [
  (9087146, 21, 18963801450, [0,1,2,3,4,5], [0,1,2,3,4,5]),
  (10167606, 6, 18963801450, [4,2,0,3,1,5], [2,4,1,3,0,5]),
  (10167606, 9, 20087122770, [0,1,2,3,4,5], [0,1,2,3,4,5]),
  (10167606, 18, 18963801450, [4,2,0,5,1,3], [2,4,1,5,0,3]),
  (10167606, 20, 18963801450, [4,3,0,5,1,2], [2,4,5,1,0,3]),
  (10167606, 22, 21144353580, [0,1,2,3,4,5], [0,1,2,3,4,5])]

set_option maxRecDepth 100000 in
theorem ok6 : StepOK 5 L5 L6 15 C6 := by decide +kernel

theorem cl6 : Classified 6 L6 15 :=
  step 5 L5 L6 10 15 C6 ok6 (by intro E d h1 h2; omega) cl5

def C7 : List (ℕ × ℕ × ℕ × List ℕ × List ℕ) := [
  (18963801450, 21, 152465478167210, [0,1,2,3,4,5,6], [0,1,2,3,4,5,6]),
  (18963801450, 42, 152465478167210, [0,2,1,6,5,4,3], [0,2,1,6,5,4,3]),
  (20087122770, 13, 152465478167210, [4,2,1,0,3,5,6], [3,2,1,4,0,5,6]),
  (20087122770, 37, 152465478167210, [6,2,1,0,3,5,4], [3,2,1,4,6,5,0]),
  (20087122770, 41, 152465478167210, [6,2,1,0,4,5,3], [3,2,1,6,4,5,0]),
  (20087122770, 44, 152465478167210, [6,2,3,0,4,5,1], [3,6,1,2,4,5,0]),
  (20087122770, 45, 165830108549850, [0,1,2,3,4,5,6], [0,1,2,3,4,5,6]),
  (21144353580, 3, 152465478167210, [6,1,3,5,4,2,0], [6,1,5,2,4,3,0]),
  (21144353580, 12, 152465478167210, [5,3,1,6,2,4,0], [6,2,4,1,5,0,3]),
  (21144353580, 17, 152465478167210, [6,1,3,2,4,5,0], [6,1,3,2,4,5,0]),
  (21144353580, 18, 152465478167210, [6,2,3,1,4,5,0], [6,3,1,2,4,5,0]),
  (21144353580, 19, 165830108549850, [5,0,1,3,4,2,6], [1,2,5,3,4,0,6]),
  (21144353580, 36, 152465478167210, [5,3,1,4,2,6,0], [6,2,4,1,3,0,5]),
  (21144353580, 40, 152465478167210, [5,4,1,3,2,6,0], [6,2,4,3,1,0,5]),
  (21144353580, 44, 165830108549850, [6,0,3,1,2,4,5], [1,3,4,2,5,6,0])]

set_option maxRecDepth 100000 in
theorem ok7 : StepOK 6 L6 L7 21 C7 := by decide +kernel

theorem cl7 : Classified 7 L7 21 :=
  step 6 L6 L7 15 21 C7 ok7 (by intro E d h1 h2; omega) cl6

def C8 : List (ℕ × ℕ × ℕ × List ℕ × List ℕ) := [
  (152465478167210, 21, 4947860780934124842, [0,1,2,3,4,5,6,7], [0,1,2,3,4,5,6,7]),
  (152465478167210, 42, 4948141160677463124, [0,1,2,3,4,5,6,7], [0,1,2,3,4,5,6,7]),
  (152465478167210, 69, 5019917275460425098, [0,1,2,3,4,5,6,7], [0,1,2,3,4,5,6,7]),
  (152465478167210, 81, 5019917275460425098, [0,1,2,5,4,3,6,7], [0,1,2,5,4,3,6,7]),
  (152465478167210, 84, 5019917275460425098, [0,3,2,5,4,1,6,7], [0,5,2,1,4,3,6,7]),
  (152465478167210, 85, 5019918374972052906, [0,1,2,3,4,5,6,7], [0,1,2,3,4,5,6,7]),
  (165830108549850, 5, 4948141160677463124, [7,2,1,4,6,5,3,0], [7,2,1,6,3,5,4,0]),
  (165830108549850, 10, 4947860780934124842, [7,1,2,3,5,6,4,0], [7,1,2,3,6,4,5,0]),
  (165830108549850, 18, 4947860780934124842, [7,1,2,3,4,6,5,0], [7,1,2,3,4,6,5,0]),
  (165830108549850, 24, 4947860780934124842, [7,1,4,3,2,6,5,0], [7,1,4,3,2,6,5,0]),
  (165830108549850, 26, 5019918374972052906, [6,2,1,4,0,5,3,7], [4,2,1,6,3,5,0,7]),
  (165830108549850, 33, 4948141160677463124, [7,2,1,4,3,5,6,0], [7,2,1,4,3,5,6,0]),
  (165830108549850, 36, 4948141160677463124, [7,2,3,4,1,5,6,0], [7,4,1,2,3,5,6,0]),
  (165830108549850, 37, 5383290614320903498, [0,1,2,3,4,5,6,7], [0,1,2,3,4,5,6,7]),
  (165830108549850, 66, 4947860780934124842, [5,1,2,3,4,6,7,0], [7,1,2,3,4,0,5,6]),
  (165830108549850, 72, 4947860780934124842, [5,1,4,3,2,6,7,0], [7,1,4,3,2,0,5,6]),
  (165830108549850, 74, 5019918374972052906, [6,2,1,4,0,7,3,5], [4,2,1,6,3,7,0,5]),
  (165830108549850, 80, 4947860780934124842, [4,1,5,3,2,6,7,0], [7,1,4,3,0,2,5,6]),
  (165830108549850, 82, 5019918374972052906, [6,2,1,5,0,7,3,4], [4,2,1,6,7,3,0,5]),
  (165830108549850, 88, 5019918374972052906, [6,4,1,5,0,7,3,2], [4,2,7,6,1,3,0,5]),
  (165830108549850, 90, 5455067837172004020, [0,1,2,3,4,5,6,7], [0,1,2,3,4,5,6,7])]

set_option maxRecDepth 100000 in
theorem ok8 : StepOK 7 L7 L8 28 C8 := by decide +kernel

theorem cl8 : Classified 8 L8 28 :=
  step 7 L7 L8 21 28 C8 ok8 (by intro E d h1 h2; omega) cl7

def C9 : List (ℕ × ℕ × ℕ × List ℕ × List ℕ) := [
  (4947860780934124842, 85, 645390076984985590999722, [0,1,2,3,4,5,6,7,8], [0,1,2,3,4,5,6,7,8]),
  (4947860780934124842, 170, 650103238075101104351572, [0,1,2,3,4,5,6,7,8], [0,1,2,3,4,5,6,7,8]),
  (4948141160677463124, 43, 645390076984985590999722, [6,0,1,3,2,5,4,7,8], [1,2,4,3,6,5,0,7,8]),
  (4948141160677463124, 139, 650121630846210858636054, [0,1,2,3,4,5,6,7,8], [0,1,2,3,4,5,6,7,8]),
  (4948141160677463124, 163, 650121630846210858636054, [0,1,2,3,6,5,4,7,8], [0,1,2,3,6,5,4,7,8]),
  (4948141160677463124, 169, 650121630846210858636054, [0,1,4,3,6,5,2,7,8], [0,1,6,3,2,5,4,7,8]),
  (4948141160677463124, 170, 650121630846210858636054, [0,2,4,3,6,5,1,7,8], [0,6,1,3,2,5,4,7,8]),
  (4948141160677463124, 171, 650121648860609368118102, [0,1,2,3,4,5,6,7,8], [0,1,2,3,4,5,6,7,8]),
  (5019917275460425098, 85, 650121630846210858636054, [5,0,2,3,4,1,8,7,6], [1,5,2,3,4,0,8,7,6]),
  (5019917275460425098, 170, 650121630846210858636054, [6,0,3,2,7,8,1,4,5], [1,6,3,2,7,8,0,4,5]),
  (5019918374972052906, 21, 650121630846210858636054, [7,2,4,1,6,5,0,3,8], [6,3,1,7,2,5,4,0,8]),
  (5019918374972052906, 42, 650103238075101104351572, [7,0,2,1,4,5,6,3,8], [1,3,2,7,4,5,6,0,8]),
  (5019918374972052906, 69, 650103238075101104351572, [6,0,1,2,3,8,7,4,5], [1,2,3,4,7,8,0,6,5]),
  (5019918374972052906, 81, 650121630846210858636054, [3,2,4,1,6,5,0,7,8], [6,3,1,0,2,5,4,7,8]),
  (5019918374972052906, 84, 650121630846210858636054, [1,2,4,3,6,5,0,7,8], [6,0,1,3,2,5,4,7,8]),
  (5019918374972052906, 85, 650121648860609368118102, [7,0,2,1,4,5,6,3,8], [1,3,2,7,4,5,6,0,8]),
  (5019918374972052906, 138, 650121630846210858636054, [6,1,3,2,7,8,0,4,5], [6,1,3,2,7,8,0,4,5]),
  (5019918374972052906, 162, 650121630846210858636054, [4,1,3,2,7,8,0,6,5], [6,1,3,2,0,8,7,4,5]),
  (5019918374972052906, 168, 650121630846210858636054, [2,1,3,4,7,8,0,6,5], [6,1,0,2,3,8,7,4,5]),
  (5019918374972052906, 170, 650121648860609368118102, [6,0,1,2,3,8,7,4,5], [1,2,3,4,7,8,0,6,5]),
  (5383290614320903498, 21, 650103238075101104351572, [5,6,2,1,4,8,7,3,0], [8,3,2,7,4,0,1,6,5]),
  (5383290614320903498, 37, 650103238075101104351572, [6,5,2,1,4,8,7,3,0], [8,3,2,7,4,1,0,6,5]),
  (5383290614320903498, 49, 650103238075101104351572, [6,3,2,1,4,8,7,5,0], [8,3,2,1,4,7,0,6,5]),
  (5383290614320903498, 52, 650103238075101104351572, [6,1,2,3,4,8,7,5,0], [8,1,2,3,4,7,0,6,5]),
  (5383290614320903498, 53, 650121648860609368118102, [7,1,3,2,5,0,6,4,8], [5,1,3,2,7,4,6,0,8]),
  (5383290614320903498, 74, 702260994877317377239188, [0,1,2,3,4,5,6,7,8], [0,1,2,3,4,5,6,7,8]),
  (5383290614320903498, 133, 650103238075101104351572, [8,5,2,1,4,6,7,3,0], [8,3,2,7,4,1,5,6,0]),
  (5383290614320903498, 145, 650103238075101104351572, [8,3,2,1,4,6,7,5,0], [8,3,2,1,4,7,5,6,0]),
  (5383290614320903498, 148, 650103238075101104351572, [8,1,2,3,4,6,7,5,0], [8,1,2,3,4,7,5,6,0]),
  (5383290614320903498, 149, 650121648860609368118102, [7,1,3,2,5,0,8,4,6], [5,1,3,2,7,4,8,0,6]),
  (5383290614320903498, 161, 650103238075101104351572, [8,3,2,1,4,5,7,6,0], [8,3,2,1,4,5,7,6,0]),
  (5383290614320903498, 164, 650103238075101104351572, [8,1,2,3,4,5,7,6,0], [8,1,2,3,4,5,7,6,0]),
  (5383290614320903498, 165, 650121648860609368118102, [7,1,3,2,6,0,8,4,5], [5,1,3,2,7,8,4,0,6]),
  (5383290614320903498, 176, 650103238075101104351572, [8,1,2,5,4,3,7,6,0], [8,1,2,5,4,3,7,6,0]),
  (5383290614320903498, 177, 650121648860609368118102, [7,1,5,2,6,0,8,4,3], [5,1,3,8,7,2,4,0,6]),
  (5383290614320903498, 180, 650121648860609368118102, [7,3,5,2,6,0,8,4,1], [5,8,3,1,7,2,4,0,6]),
  (5383290614320903498, 181, 706974156037664463727466, [0,1,2,3,4,5,6,7,8], [0,1,2,3,4,5,6,7,8]),
  (5455067837172004020, 3, 645390076984985590999722, [8,4,3,1,5,7,6,2,0], [8,3,7,2,1,4,6,5,0]),
  (5455067837172004020, 9, 645390076984985590999722, [8,2,3,1,5,7,6,4,0], [8,3,1,2,7,4,6,5,0]),
  (5455067837172004020, 10, 645390076984985590999722, [8,1,3,2,5,7,6,4,0], [8,1,3,2,7,4,6,5,0]),
  (5455067837172004020, 11, 650121648860609368118102, [4,3,5,1,6,7,8,2,0], [8,3,7,1,0,2,4,5,6]),
  (5455067837172004020, 20, 645390076984985590999722, [7,6,1,3,2,8,4,5,0], [8,2,4,3,6,7,1,0,5]),
  (5455067837172004020, 36, 645390076984985590999722, [7,5,1,3,2,8,4,6,0], [8,2,4,3,6,1,7,0,5]),
  (5455067837172004020, 48, 645390076984985590999722, [7,3,1,5,2,8,4,6,0], [8,2,4,1,6,3,7,0,5]),
  (5455067837172004020, 52, 650121648860609368118102, [6,1,2,3,4,8,7,5,0], [8,1,2,3,4,7,0,6,5]),
  (5455067837172004020, 65, 645390076984985590999722, [8,2,3,1,5,4,6,7,0], [8,3,1,2,5,4,6,7,0]),
  (5455067837172004020, 66, 645390076984985590999722, [8,1,3,2,5,4,6,7,0], [8,1,3,2,5,4,6,7,0]),
  (5455067837172004020, 67, 650121648860609368118102, [7,3,5,1,6,4,8,2,0], [8,3,7,1,5,2,4,0,6]),
  (5455067837172004020, 72, 645390076984985590999722, [8,1,3,4,5,2,6,7,0], [8,1,5,2,3,4,6,7,0]),
  (5455067837172004020, 73, 650121648860609368118102, [7,3,5,1,6,2,8,4,0], [8,3,5,1,7,2,4,0,6]),
  (5455067837172004020, 74, 650121648860609368118102, [7,3,5,2,6,1,8,4,0], [8,5,3,1,7,2,4,0,6]),
  (5455067837172004020, 75, 706974156037664463727466, [7,0,1,3,2,5,6,4,8], [1,2,4,3,7,5,6,0,8]),
  (5455067837172004020, 132, 645390076984985590999722, [7,5,1,3,2,6,4,8,0], [8,2,4,3,6,1,5,0,7]),
  (5455067837172004020, 144, 645390076984985590999722, [7,3,1,5,2,6,4,8,0], [8,2,4,1,6,3,5,0,7]),
  (5455067837172004020, 148, 650121648860609368118102, [8,1,2,3,4,6,7,5,0], [8,1,2,3,4,7,5,6,0]),
  (5455067837172004020, 160, 645390076984985590999722, [7,3,1,6,2,5,4,8,0], [8,2,4,1,6,5,3,0,7]),
  (5455067837172004020, 164, 650121648860609368118102, [8,1,2,3,4,5,7,6,0], [8,1,2,3,4,5,7,6,0]),
  (5455067837172004020, 176, 650121648860609368118102, [8,1,2,5,4,3,7,6,0], [8,1,2,5,4,3,7,6,0]),
  (5455067837172004020, 180, 706974156037664463727466, [8,0,3,1,5,2,4,6,7], [1,3,5,2,6,4,7,8,0])]

set_option maxRecDepth 100000 in
theorem ok9 : StepOK 8 L8 L9 35 C9 := by decide +kernel

theorem cl9 : Classified 9 L9 35 :=
  step 8 L8 L9 28 35 C9 ok9 (by intro E d h1 h2; omega) cl8

def C10 : List (ℕ × ℕ × ℕ × List ℕ × List ℕ) := [
  (645390076984985590999722, 85, 337544580872724614391617901738, [0,1,2,3,4,5,6,7,8,9], [0,1,2,3,4,5,6,7,8,9]),
  (645390076984985590999722, 170, 337545788619104405006520242516, [0,1,2,3,4,5,6,7,8,9], [0,1,2,3,4,5,6,7,8,9]),
  (645390076984985590999722, 277, 338782519731418373949105722922, [0,1,2,3,4,5,6,7,8,9], [0,1,2,3,4,5,6,7,8,9]),
  (645390076984985590999722, 325, 338782519731418373949105722922, [0,1,2,3,4,7,6,5,8,9], [0,1,2,3,4,7,6,5,8,9]),
  (645390076984985590999722, 337, 338782519731418373949105722922, [0,1,2,5,4,7,6,3,8,9], [0,1,2,7,4,3,6,5,8,9]),
  (645390076984985590999722, 340, 338782519731418373949105722922, [0,3,2,5,4,7,6,1,8,9], [0,7,2,1,4,3,6,5,8,9]),
  (645390076984985590999722, 341, 338782520912009994666517026474, [0,1,2,3,4,5,6,7,8,9], [0,1,2,3,4,5,6,7,8,9]),
  (650103238075101104351572, 43, 338782519731418373949105722922, [8,3,2,5,1,7,6,0,4,9], [7,4,2,1,8,3,6,5,0,9]),
  (650103238075101104351572, 139, 340019253203762662821907309846, [0,1,2,3,4,5,6,7,8,9], [0,1,2,3,4,5,6,7,8,9]),
  (650103238075101104351572, 163, 338782519731418373949105722922, [4,3,2,5,1,7,6,0,8,9], [7,4,2,1,0,3,6,5,8,9]),
  (650103238075101104351572, 169, 340019253203762662821907309846, [0,1,6,3,4,5,2,7,8,9], [0,1,6,3,4,5,2,7,8,9]),
  (650103238075101104351572, 170, 338782519731418373949105722922, [1,3,2,5,4,7,6,0,8,9], [7,0,2,1,4,3,6,5,8,9]),
  (650103238075101104351572, 171, 338782520912009994666517026474, [8,0,2,3,1,5,6,7,4,9], [1,4,2,3,8,5,6,7,0,9]),
  (650103238075101104351572, 340, 341255985497821173986510938792, [0,1,2,3,4,5,6,7,8,9], [0,1,2,3,4,5,6,7,8,9]),
  (650121630846210858636054, 86, 338782519731418373949105722922, [1,2,0,3,4,5,6,7,8,9], [2,0,1,3,4,5,6,7,8,9]),
  (650121630846210858636054, 169, 340024081829251505351473804626, [0,1,2,3,4,5,6,7,8,9], [0,1,2,3,4,5,6,7,8,9]),
  (650121630846210858636054, 278, 338782519731418373949105722922, [6,2,0,3,4,5,1,9,8,7], [2,6,1,3,4,5,0,9,8,7]),
  (650121630846210858636054, 326, 341260814122155969111565841036, [0,1,2,3,4,5,6,7,8,9], [0,1,2,3,4,5,6,7,8,9]),
  (650121630846210858636054, 338, 341260814122155969111565841036, [0,1,2,5,4,3,6,7,8,9], [0,1,2,5,4,3,6,7,8,9]),
  (650121630846210858636054, 340, 341260814122155969111565841036, [0,1,3,5,4,2,6,7,8,9], [0,1,5,2,4,3,6,7,8,9]),
  (650121630846210858636054, 342, 341260814122157095011472683692, [0,1,2,3,4,5,6,7,8,9], [0,1,2,3,4,5,6,7,8,9]),
  (650121648860609368118102, 22, 340019253203762662821907309846, [7,1,6,2,4,3,0,5,8,9], [6,1,3,5,4,7,2,0,8,9]),
  (650121648860609368118102, 41, 340024081829251505351473804626, [7,8,2,3,1,5,6,0,4,9], [7,4,2,3,8,5,6,0,1,9]),
  (650121648860609368118102, 70, 340019253203762662821907309846, [5,1,6,2,4,3,0,7,8,9], [6,1,3,5,4,0,2,7,8,9]),
  (650121648860609368118102, 82, 340019253203762662821907309846, [3,1,6,2,4,5,0,7,8,9], [6,1,3,0,4,5,2,7,8,9]),
  (650121648860609368118102, 84, 340019253203762662821907309846, [2,1,6,3,4,5,0,7,8,9], [6,1,0,3,4,5,2,7,8,9]),
  (650121648860609368118102, 86, 338782520912009994666517026474, [8,2,0,3,1,5,6,7,4,9], [2,4,1,3,8,5,6,7,0,9]),
  (650121648860609368118102, 137, 341255985497821173986510938792, [7,2,0,1,3,4,9,8,5,6], [2,3,1,4,5,8,9,0,7,6]),
  (650121648860609368118102, 161, 340024081829251505351473804626, [7,4,2,3,1,5,6,0,8,9], [7,4,2,3,1,5,6,0,8,9]),
  (650121648860609368118102, 168, 340024081829251505351473804626, [7,1,2,3,4,5,6,0,8,9], [7,1,2,3,4,5,6,0,8,9]),
  (650121648860609368118102, 169, 340024084190434746786296542546, [0,1,2,3,4,5,6,7,8,9], [0,1,2,3,4,5,6,7,8,9]),
  (650121648860609368118102, 262, 338782519731418373949105722922, [9,1,5,4,2,8,7,6,3,0], [9,1,4,8,3,2,7,6,5,0]),
  (650121648860609368118102, 274, 338782519731418373949105722922, [9,1,3,4,2,8,7,6,5,0], [9,1,4,2,3,8,7,6,5,0]),
  (650121648860609368118102, 276, 338782519731418373949105722922, [9,1,2,4,3,8,7,6,5,0], [9,1,2,4,3,8,7,6,5,0]),
  (650121648860609368118102, 278, 341260814122157095011472683692, [8,0,2,3,1,5,6,7,4,9], [1,4,2,3,8,5,6,7,0,9]),
  (650121648860609368118102, 322, 338782519731418373949105722922, [9,1,3,4,2,8,5,6,7,0], [9,1,4,2,3,6,7,8,5,0]),
  (650121648860609368118102, 324, 338782519731418373949105722922, [9,1,2,4,3,8,5,6,7,0], [9,1,2,4,3,6,7,8,5,0]),
  (650121648860609368118102, 326, 341260814122157095011472683692, [8,0,2,3,1,7,6,5,4,9], [1,4,2,3,8,7,6,5,0,9]),
  (650121648860609368118102, 336, 338782519731418373949105722922, [9,1,2,4,5,8,3,6,7,0], [9,1,2,6,3,4,7,8,5,0]),
  (650121648860609368118102, 338, 341260814122157095011472683692, [8,0,2,5,1,7,6,3,4,9], [1,4,2,7,8,3,6,5,0,9]),
  (650121648860609368118102, 340, 341260814122157095011472683692, [8,0,3,5,1,7,6,2,4,9], [1,4,7,2,8,3,6,5,0,9]),
  (650121648860609368118102, 342, 341260816483340336446295421612, [0,1,2,3,4,5,6,7,8,9], [0,1,2,3,4,5,6,7,8,9]),
  (702260994877317377239188, 43, 341255985497821173986510938792, [6,1,7,3,2,5,9,8,4,0], [9,1,4,3,8,5,0,2,7,6]),
  (702260994877317377239188, 75, 341255985497821173986510938792, [7,1,6,3,2,5,9,8,4,0], [9,1,4,3,8,5,2,0,7,6]),
  (702260994877317377239188, 99, 341255985497821173986510938792, [7,1,4,3,2,5,9,8,6,0], [9,1,4,3,2,5,8,0,7,6]),
  (702260994877317377239188, 105, 341255985497821173986510938792, [7,1,2,3,4,5,9,8,6,0], [9,1,2,3,4,5,8,0,7,6]),
  (702260994877317377239188, 106, 341255985497821173986510938792, [7,2,1,3,4,5,9,8,6,0], [9,2,1,3,4,5,8,0,7,6]),
  (702260994877317377239188, 107, 340024084190434746786296542546, [7,3,1,2,5,4,0,6,8,9], [6,2,3,1,5,4,7,0,8,9]),
  (702260994877317377239188, 267, 341255985497821173986510938792, [9,1,6,3,2,5,7,8,4,0], [9,1,4,3,8,5,2,6,7,0]),
  (702260994877317377239188, 291, 341255985497821173986510938792, [9,1,4,3,2,5,7,8,6,0], [9,1,4,3,2,5,8,6,7,0]),
  (702260994877317377239188, 297, 341255985497821173986510938792, [9,1,2,3,4,5,7,8,6,0], [9,1,2,3,4,5,8,6,7,0]),
  (702260994877317377239188, 298, 341255985497821173986510938792, [9,2,1,3,4,5,7,8,6,0], [9,2,1,3,4,5,8,6,7,0]),
  (702260994877317377239188, 299, 340024084190434746786296542546, [9,3,1,2,5,4,0,6,8,7], [6,2,3,1,5,4,7,9,8,0]),
  (702260994877317377239188, 323, 341255985497821173986510938792, [9,1,4,3,2,5,6,8,7,0], [9,1,4,3,2,5,6,8,7,0]),
  (702260994877317377239188, 329, 341255985497821173986510938792, [9,1,2,3,4,5,6,8,7,0], [9,1,2,3,4,5,6,8,7,0]),
  (702260994877317377239188, 330, 341255985497821173986510938792, [9,2,1,3,4,5,6,8,7,0], [9,2,1,3,4,5,6,8,7,0]),
  (702260994877317377239188, 331, 340024084190434746786296542546, [9,3,1,2,5,4,0,7,8,6], [6,2,3,1,5,4,9,7,8,0]),
  (702260994877317377239188, 353, 341255985497821173986510938792, [9,1,2,3,6,5,4,8,7,0], [9,1,2,3,6,5,4,8,7,0]),
  (702260994877317377239188, 354, 341255985497821173986510938792, [9,2,1,3,6,5,4,8,7,0], [9,2,1,3,6,5,4,8,7,0]),
  (702260994877317377239188, 355, 340024084190434746786296542546, [9,3,1,2,5,6,0,7,8,4], [6,2,3,1,9,4,5,7,8,0]),
  (702260994877317377239188, 360, 341255985497821173986510938792, [9,4,1,3,6,5,2,8,7,0], [9,2,6,3,1,5,4,8,7,0]),
  (702260994877317377239188, 361, 340024084190434746786296542546, [9,3,1,4,5,6,0,7,8,2], [6,2,9,1,3,4,5,7,8,0]),
  (702260994877317377239188, 362, 340024084190434746786296542546, [9,3,2,4,5,6,0,7,8,1], [6,9,2,1,3,4,5,7,8,0]),
  (702260994877317377239188, 363, 368546222791744933032436737750, [0,1,2,3,4,5,6,7,8,9], [0,1,2,3,4,5,6,7,8,9]),
  (706974156037664463727466, 5, 337545788619104405006520242516, [9,2,5,4,1,6,8,7,3,0], [9,4,1,8,3,2,5,7,6,0]),
  (706974156037664463727466, 10, 337544580872724614391617901738, [9,1,6,3,2,5,7,8,4,0], [9,1,4,3,8,5,2,6,7,0]),
  (706974156037664463727466, 17, 337545788619104405006520242516, [9,2,3,4,1,6,8,7,5,0], [9,4,1,2,3,8,5,7,6,0]),
  (706974156037664463727466, 20, 337545788619104405006520242516, [9,2,1,4,3,6,8,7,5,0], [9,2,1,4,3,8,5,7,6,0]),
  (706974156037664463727466, 21, 340024084190434746786296542546, [9,1,2,4,3,6,8,7,5,0], [9,1,2,4,3,8,5,7,6,0]),
  (706974156037664463727466, 34, 337544580872724614391617901738, [9,1,4,3,2,5,7,8,6,0], [9,1,4,3,2,5,8,6,7,0]),
  (706974156037664463727466, 40, 337544580872724614391617901738, [9,1,2,3,4,5,7,8,6,0], [9,1,2,3,4,5,8,6,7,0]),
  (706974156037664463727466, 42, 338782520912009994666517026474, [6,1,7,3,2,5,9,8,4,0], [9,1,4,3,8,5,0,2,7,6]),
  (706974156037664463727466, 66, 337544580872724614391617901738, [9,1,4,3,2,5,6,8,7,0], [9,1,4,3,2,5,6,8,7,0]),
  (706974156037664463727466, 72, 337544580872724614391617901738, [9,1,2,3,4,5,6,8,7,0], [9,1,2,3,4,5,6,8,7,0]),
  (706974156037664463727466, 74, 338782520912009994666517026474, [7,1,6,3,2,5,9,8,4,0], [9,1,4,3,8,5,2,0,7,6]),
  (706974156037664463727466, 96, 337544580872724614391617901738, [9,1,2,3,6,5,4,8,7,0], [9,1,2,3,6,5,4,8,7,0]),
  (706974156037664463727466, 98, 338782520912009994666517026474, [7,1,4,3,2,5,9,8,6,0], [9,1,4,3,2,5,8,0,7,6]),
  (706974156037664463727466, 104, 338782520912009994666517026474, [7,1,2,3,4,5,9,8,6,0], [9,1,2,3,4,5,8,0,7,6]),
  (706974156037664463727466, 106, 341260816483340336446295421612, [8,1,2,4,3,6,0,7,5,9], [6,1,2,4,3,8,5,7,0,9]),
  (706974156037664463727466, 129, 337545788619104405006520242516, [9,2,3,4,1,6,5,7,8,0], [9,4,1,2,3,6,5,7,8,0]),
  (706974156037664463727466, 132, 337545788619104405006520242516, [9,2,1,4,3,6,5,7,8,0], [9,2,1,4,3,6,5,7,8,0]),
  (706974156037664463727466, 133, 340024084190434746786296542546, [9,1,2,4,3,6,5,7,8,0], [9,1,2,4,3,6,5,7,8,0]),
  (706974156037664463727466, 144, 337545788619104405006520242516, [9,2,1,4,5,6,3,7,8,0], [9,2,1,6,3,4,5,7,8,0]),
  (706974156037664463727466, 145, 340024084190434746786296542546, [9,1,2,4,5,6,3,7,8,0], [9,1,2,6,3,4,5,7,8,0]),
  (706974156037664463727466, 148, 340024084190434746786296542546, [9,3,2,4,5,6,1,7,8,0], [9,6,2,1,3,4,5,7,8,0]),
  (706974156037664463727466, 149, 368546222791744933032436737750, [8,0,2,1,4,3,6,7,5,9], [1,3,2,5,4,8,6,7,0,9]),
  (706974156037664463727466, 258, 337544580872724614391617901738, [7,1,4,3,2,5,6,8,9,0], [9,1,4,3,2,5,6,0,7,8]),
  (706974156037664463727466, 264, 337544580872724614391617901738, [7,1,2,3,4,5,6,8,9,0], [9,1,2,3,4,5,6,0,7,8]),
  (706974156037664463727466, 266, 338782520912009994666517026474, [9,1,6,3,2,5,7,8,4,0], [9,1,4,3,8,5,2,6,7,0]),
  (706974156037664463727466, 288, 337544580872724614391617901738, [7,1,2,3,6,5,4,8,9,0], [9,1,2,3,6,5,4,0,7,8]),
  (706974156037664463727466, 290, 338782520912009994666517026474, [9,1,4,3,2,5,7,8,6,0], [9,1,4,3,2,5,8,6,7,0]),
  (706974156037664463727466, 296, 338782520912009994666517026474, [9,1,2,3,4,5,7,8,6,0], [9,1,2,3,4,5,8,6,7,0]),
  (706974156037664463727466, 298, 341260816483340336446295421612, [8,1,2,4,3,6,0,9,5,7], [6,1,2,4,3,8,5,9,0,7]),
  (706974156037664463727466, 320, 337544580872724614391617901738, [6,1,2,3,7,5,4,8,9,0], [9,1,2,3,6,5,0,4,7,8]),
  (706974156037664463727466, 322, 338782520912009994666517026474, [9,1,4,3,2,5,6,8,7,0], [9,1,4,3,2,5,6,8,7,0]),
  (706974156037664463727466, 328, 338782520912009994666517026474, [9,1,2,3,4,5,6,8,7,0], [9,1,2,3,4,5,6,8,7,0]),
  (706974156037664463727466, 330, 341260816483340336446295421612, [8,1,2,4,3,7,0,9,5,6], [6,1,2,4,3,8,9,5,0,7]),
  (706974156037664463727466, 352, 338782520912009994666517026474, [9,1,2,3,6,5,4,8,7,0], [9,1,2,3,6,5,4,8,7,0]),
  (706974156037664463727466, 354, 341260816483340336446295421612, [8,1,2,6,3,7,0,9,5,4], [6,1,2,4,9,8,3,5,0,7]),
  (706974156037664463727466, 360, 341260816483340336446295421612, [8,1,4,6,3,7,0,9,5,2], [6,1,9,4,2,8,3,5,0,7]),
  (706974156037664463727466, 362, 371019687382163299164986495700, [0,1,2,3,4,5,6,7,8,9], [0,1,2,3,4,5,6,7,8,9])]

set_option maxRecDepth 100000 in
theorem ok10 : StepOK 9 L9 L10 43 C10 := by decide +kernel

theorem cl10 : Classified 10 L10 43 :=
  step 9 L9 L10 35 43 C10 ok10 (by intro E d h1 h2; omega) cl9

def C11 : List (ℕ × ℕ × ℕ × List ℕ × List ℕ) := [
  (337544580872724614391617901738, 85, 707017121590449743059520504686356650, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (337544580872724614391617901738, 170, 707017121899783710904378826183844180, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (337544580872724614391617901738, 277, 707017755415598741446769424391121450, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (337544580872724614391617901738, 325, 707017121590449743059520504686356650, [0,1,2,3,4,9,6,7,8,5,10], [0,1,2,3,4,9,6,7,8,5,10]),
  (337544580872724614391617901738, 337, 707017755415598741446769424391121450, [0,1,2,7,4,5,6,3,8,9,10], [0,1,2,7,4,5,6,3,8,9,10]),
  (337544580872724614391617901738, 340, 707017755415598741446769424391121450, [0,3,2,7,4,5,6,1,8,9,10], [0,7,2,1,4,5,6,3,8,9,10]),
  (337544580872724614391617901738, 341, 707017755415749857174221253037959850, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (337544580872724614391617901738, 554, 708315195804932407990166381541368916, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (337544580872724614391617901738, 581, 708315195805083449930624331749698698, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (337544580872724614391617901738, 650, 708315195804932407990166381541368916, [0,1,2,3,4,5,8,7,6,9,10], [0,1,2,3,4,5,8,7,6,9,10]),
  (337544580872724614391617901738, 674, 708315195804932407990166381541368916, [0,1,2,3,6,5,8,7,4,9,10], [0,1,2,3,8,5,4,7,6,9,10]),
  (337544580872724614391617901738, 680, 708315195804932407990166381541368916, [0,1,4,3,6,5,8,7,2,9,10], [0,1,8,3,2,5,4,7,6,9,10]),
  (337544580872724614391617901738, 682, 708315196114417417811511450266150228, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (337545788619104405006520242516, 43, 707017755415598741446769424391121450, [8,3,1,7,2,5,4,0,6,9,10], [7,2,4,1,6,5,8,3,0,9,10]),
  (337545788619104405006520242516, 139, 707017755415598741446769424391121450, [6,3,1,7,2,5,4,0,8,9,10], [7,2,4,1,6,5,0,3,8,9,10]),
  (337545788619104405006520242516, 163, 707017755415598741446769424391121450, [4,3,1,7,2,5,6,0,8,9,10], [7,2,4,1,0,5,6,3,8,9,10]),
  (337545788619104405006520242516, 169, 707017755415598741446769424391121450, [2,3,1,7,4,5,6,0,8,9,10], [7,2,0,1,4,5,6,3,8,9,10]),
  (337545788619104405006520242516, 170, 707017755415598741446769424391121450, [1,3,2,7,4,5,6,0,8,9,10], [7,0,2,1,4,5,6,3,8,9,10]),
  (337545788619104405006520242516, 171, 707017755415749857174221253037959850, [8,0,1,3,2,5,4,7,6,9,10], [1,2,4,3,6,5,8,7,0,9,10]),
  (337545788619104405006520242516, 340, 707019022447682149713906106746880680, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (337545788619104405006520242516, 523, 708316462836864626742874940412087318, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (337545788619104405006520242516, 547, 708316462836864626742874940412087318, [0,1,2,3,6,5,4,7,8,9,10], [0,1,2,3,6,5,4,7,8,9,10]),
  (337545788619104405006520242516, 553, 708316462836864626742874940412087318, [0,1,4,3,6,5,2,7,8,9,10], [0,1,6,3,2,5,4,7,8,9,10]),
  (337545788619104405006520242516, 554, 708316462836864626742874940412087318, [0,2,4,3,6,5,1,7,8,9,10], [0,6,1,3,2,5,4,7,8,9,10]),
  (337545788619104405006520242516, 555, 708316462836864700529851235250293846, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (337545788619104405006520242516, 643, 708316462836864626742874940412087318, [0,1,2,3,8,5,4,7,6,9,10], [0,1,2,3,6,5,8,7,4,9,10]),
  (337545788619104405006520242516, 649, 708316462836864626742874940412087318, [0,1,4,3,8,5,2,7,6,9,10], [0,1,6,3,2,5,8,7,4,9,10]),
  (337545788619104405006520242516, 650, 708316462836864626742874940412087318, [0,2,4,3,8,5,1,7,6,9,10], [0,6,1,3,2,5,8,7,4,9,10]),
  (337545788619104405006520242516, 651, 708316462836864700529851235250293846, [0,1,2,3,4,5,8,7,6,9,10], [0,1,2,3,4,5,8,7,6,9,10]),
  (337545788619104405006520242516, 673, 708316462836864626742874940412087318, [0,1,6,3,8,5,2,7,4,9,10], [0,1,6,3,8,5,2,7,4,9,10]),
  (337545788619104405006520242516, 674, 708316462836864626742874940412087318, [0,2,6,3,8,5,1,7,4,9,10], [0,6,1,3,8,5,2,7,4,9,10]),
  (337545788619104405006520242516, 675, 708316462836864700529851235250293846, [0,1,2,3,6,5,8,7,4,9,10], [0,1,2,3,8,5,4,7,6,9,10]),
  (337545788619104405006520242516, 680, 708316462836864626742874940412087318, [0,4,6,3,8,5,1,7,2,9,10], [0,6,8,3,1,5,2,7,4,9,10]),
  (337545788619104405006520242516, 681, 708316462836864700529851235250293846, [0,1,4,3,6,5,8,7,2,9,10], [0,1,8,3,2,5,4,7,6,9,10]),
  (337545788619104405006520242516, 682, 708316462836864700529851235250293846, [0,2,4,3,6,5,8,7,1,9,10], [0,8,1,3,2,5,4,7,6,9,10]),
  (337545788619104405006520242516, 683, 708316463146349710351196303975075158, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (338782519731418373949105722922, 85, 709613269400747137231095615402977450, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (338782519731418373949105722922, 170, 708315195804932407990166381541368916, [1,0,2,3,4,5,6,7,8,9,10], [1,0,2,3,4,5,6,7,8,9,10]),
  (338782519731418373949105722922, 277, 709613903225896135618344535107742250, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (338782519731418373949105722922, 325, 709613269400747137231095615402977450, [0,1,2,3,4,9,6,7,8,5,10], [0,1,2,3,4,9,6,7,8,5,10]),
  (338782519731418373949105722922, 337, 709613903225896135618344535107742250, [0,1,2,7,4,5,6,3,8,9,10], [0,1,2,7,4,5,6,3,8,9,10]),
  (338782519731418373949105722922, 340, 708316462836864626742874940412087318, [1,2,4,3,6,5,0,7,8,9,10], [6,0,1,3,2,5,4,7,8,9,10]),
  (338782519731418373949105722922, 341, 708316462836864700529851235250293846, [1,0,2,3,4,5,6,7,8,9,10], [1,0,2,3,4,5,6,7,8,9,10]),
  (338782519731418373949105722922, 554, 710911343615229802161741492257989716, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (338782519731418373949105722922, 650, 710911343924714738196110266144564500, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (338782519731418373949105722922, 674, 710911343924714738196110266144564500, [0,1,2,3,6,5,4,7,8,9,10], [0,1,2,3,6,5,4,7,8,9,10]),
  (338782519731418373949105722922, 680, 710911343924714738196110266144564500, [0,1,4,3,6,5,2,7,8,9,10], [0,1,6,3,2,5,4,7,8,9,10]),
  (338782519731418373949105722922, 682, 710911343924714811983086560982771028, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (338782520912009994666517026474, 21, 709613270019566041146333924206225450, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (338782520912009994666517026474, 42, 709613270019566114897299005625770068, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (338782520912009994666517026474, 69, 709613270019717156837756955834099850, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (338782520912009994666517026474, 81, 709613270019566041146333924206225450, [0,1,2,7,4,5,6,3,8,9,10], [0,1,2,7,4,5,6,3,8,9,10]),
  (338782520912009994666517026474, 84, 709613270019717156837756955834099850, [0,5,2,3,4,1,6,7,8,9,10], [0,5,2,3,4,1,6,7,8,9,10]),
  (338782520912009994666517026474, 85, 708316462836864700529851235250293846, [9,2,4,3,6,1,8,7,0,5,10], [8,5,1,3,2,9,4,7,6,0,10]),
  (338782520912009994666517026474, 138, 709613270019566114897299005625770068, [0,1,2,3,4,5,8,7,6,9,10], [0,1,2,3,4,5,8,7,6,9,10]),
  (338782520912009994666517026474, 162, 709613270019566114897299005625770068, [0,1,2,3,6,5,8,7,4,9,10], [0,1,2,3,8,5,4,7,6,9,10]),
  (338782520912009994666517026474, 168, 709613270019566114897299005625770068, [0,1,4,3,6,5,8,7,2,9,10], [0,1,8,3,2,5,4,7,6,9,10]),
  (338782520912009994666517026474, 170, 708315196114417417811511450266150228, [9,0,2,3,4,1,6,7,8,5,10], [1,5,2,3,4,9,6,7,8,0,10]),
  (338782520912009994666517026474, 261, 709613270019566041146333924206225450, [0,1,2,3,4,9,6,7,8,5,10], [0,1,2,3,4,9,6,7,8,5,10]),
  (338782520912009994666517026474, 273, 709613903844866155261034663967894050, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (338782520912009994666517026474, 276, 709613270019566041146333924206225450, [0,5,2,3,4,9,6,7,8,1,10], [0,9,2,3,4,1,6,7,8,5,10]),
  (338782520912009994666517026474, 277, 709613903844866155261034672557828650, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (338782520912009994666517026474, 321, 709613270019566041146333924206225450, [0,1,2,7,4,9,6,3,8,5,10], [0,1,2,7,4,9,6,3,8,5,10]),
  (338782520912009994666517026474, 324, 709613270019717156837756955834099850, [0,9,2,3,4,1,6,7,8,5,10], [0,5,2,3,4,9,6,7,8,1,10]),
  (338782520912009994666517026474, 325, 708316462836864700529851235250293846, [5,2,4,3,6,1,8,7,0,9,10], [8,5,1,3,2,0,4,7,6,9,10]),
  (338782520912009994666517026474, 336, 709613270019566041146333924206225450, [0,5,2,7,4,9,6,3,8,1,10], [0,9,2,7,4,1,6,3,8,5,10]),
  (338782520912009994666517026474, 337, 709613903844866155261034672557828650, [0,1,2,7,4,5,6,3,8,9,10], [0,1,2,7,4,5,6,3,8,9,10]),
  (338782520912009994666517026474, 340, 708316462836864700529851235250293846, [1,2,4,3,6,5,8,7,0,9,10], [8,0,1,3,2,5,4,7,6,9,10]),
  (338782520912009994666517026474, 341, 708316463146349710351196303975075158, [9,0,2,3,4,1,6,7,8,5,10], [1,5,2,3,4,9,6,7,8,0,10]),
  (338782520912009994666517026474, 522, 708316462836864626742874940412087318, [10,1,5,6,9,2,3,8,7,4,0], [10,1,5,6,9,2,3,8,7,4,0]),
  (338782520912009994666517026474, 546, 708316462836864626742874940412087318, [10,1,5,4,9,2,3,8,7,6,0], [10,1,5,6,3,2,9,8,7,4,0]),
  (338782520912009994666517026474, 552, 708316462836864626742874940412087318, [10,1,5,2,9,4,3,8,7,6,0], [10,1,3,6,5,2,9,8,7,4,0]),
  (338782520912009994666517026474, 554, 710911343924714811983086560982771028, [9,0,2,3,4,1,6,7,8,5,10], [1,5,2,3,4,9,6,7,8,0,10]),
  (338782520912009994666517026474, 580, 708315195805083449930624331749698698, [10,1,2,5,4,3,6,9,8,7,0], [10,1,2,5,4,3,6,9,8,7,0]),
  (338782520912009994666517026474, 642, 708316462836864626742874940412087318, [10,1,5,4,9,2,3,6,7,8,0], [10,1,5,6,3,2,7,8,9,4,0]),
  (338782520912009994666517026474, 648, 708316462836864626742874940412087318, [10,1,5,2,9,4,3,6,7,8,0], [10,1,3,6,5,2,7,8,9,4,0]),
  (338782520912009994666517026474, 650, 710911343924714811983086560982771028, [9,0,2,3,4,1,8,7,6,5,10], [1,5,2,3,4,9,8,7,6,0,10]),
  (338782520912009994666517026474, 672, 708316462836864626742874940412087318, [10,1,5,2,9,6,3,4,7,8,0], [10,1,3,6,7,2,5,8,9,4,0]),
  (338782520912009994666517026474, 674, 710911343924714811983086560982771028, [9,0,2,3,6,1,8,7,4,5,10], [1,5,2,3,8,9,4,7,6,0,10]),
  (338782520912009994666517026474, 680, 710911343924714811983086560982771028, [9,0,4,3,6,1,8,7,2,5,10], [1,5,8,3,2,9,4,7,6,0,10]),
  (338782520912009994666517026474, 682, 710911344543684831625776698432857428, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (340019253203762662821907309846, 86, 709613903225896135618344535107742250, [1,9,4,3,6,2,8,7,0,5,10], [8,0,5,3,2,9,4,7,6,1,10]),
  (340019253203762662821907309846, 169, 709613270019566114897299005625770068, [7,2,4,0,6,5,8,3,1,9,10], [3,8,1,7,2,5,4,0,6,9,10]),
  (340019253203762662821907309846, 278, 709613270019566114897299005625770068, [10,4,2,0,5,6,9,1,3,8,7], [3,7,2,8,1,4,5,10,9,6,0]),
  (340019253203762662821907309846, 326, 709613903225896135618344535107742250, [1,5,4,3,6,2,8,7,0,9,10], [8,0,5,3,2,1,4,7,6,9,10]),
  (340019253203762662821907309846, 338, 712208785242050160808163232623714980, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (340019253203762662821907309846, 340, 709613903225896135618344535107742250, [1,2,4,3,6,5,8,7,0,9,10], [8,0,1,3,2,5,4,7,6,9,10]),
  (340019253203762662821907309846, 342, 709613903844866155261034672557828650, [1,2,0,3,4,5,6,7,8,9,10], [2,0,1,3,4,5,6,7,8,9,10]),
  (340019253203762662821907309846, 553, 709613903225896135618344535107742250, [3,8,2,1,5,4,9,10,0,6,7], [8,3,2,0,5,4,9,10,1,6,7]),
  (340019253203762662821907309846, 649, 709613903225896135618344535107742250, [3,6,2,1,5,4,9,10,0,8,7], [8,3,2,0,5,4,1,10,9,6,7]),
  (340019253203762662821907309846, 673, 709613903225896135618344535107742250, [3,4,2,1,5,6,9,10,0,8,7], [8,3,2,0,1,4,5,10,9,6,7]),
  (340019253203762662821907309846, 680, 712208785242050160808163232623714980, [0,3,4,1,2,6,5,10,9,8,7], [0,3,4,1,2,6,5,10,9,8,7]),
  (340019253203762662821907309846, 681, 709613903844866155261034672557828650, [3,4,0,1,2,6,5,10,9,8,7], [2,3,4,0,1,6,5,10,9,8,7]),
  (341255985497821173986510938792, 23, 712208785242050160808163232623714980, [9,3,4,0,1,6,2,10,5,8,7], [3,4,6,1,2,8,5,10,9,0,7]),
  (341255985497821173986510938792, 71, 710911343615229802161741492257989716, [9,5,4,3,6,1,8,7,0,2,10], [8,5,9,3,2,1,4,7,6,0,10]),
  (341255985497821173986510938792, 83, 712208785242050160808163232623714980, [9,7,4,0,1,6,2,10,5,8,3], [3,4,6,10,2,8,5,1,9,0,7]),
  (341255985497821173986510938792, 85, 710911343615229802161741492257989716, [9,2,4,3,6,1,8,7,0,5,10], [8,5,1,3,2,9,4,7,6,0,10]),
  (341255985497821173986510938792, 86, 710911343615229802161741492257989716, [9,1,4,3,6,2,8,7,0,5,10], [8,1,5,3,2,9,4,7,6,0,10]),
  (341255985497821173986510938792, 87, 710911343924714811983086560982771028, [5,9,4,3,6,1,8,7,0,2,10], [8,5,9,3,2,0,4,7,6,1,10]),
  (341255985497821173986510938792, 263, 712208785242050160808163232623714980, [5,3,4,0,1,6,2,10,9,8,7], [3,4,6,1,2,0,5,10,9,8,7]),
  (341255985497821173986510938792, 275, 709613903844866155261034663967894050, [7,4,1,0,2,6,5,10,9,8,3], [3,2,4,10,1,6,5,0,9,8,7]),
  (341255985497821173986510938792, 277, 712208785242050160808163232623714980, [2,3,4,0,1,6,5,10,9,8,7], [3,4,0,1,2,6,5,10,9,8,7]),
  (341255985497821173986510938792, 278, 712208785242050160808163232623714980, [1,3,4,0,2,6,5,10,9,8,7], [3,0,4,1,2,6,5,10,9,8,7]),
  (341255985497821173986510938792, 279, 709613903844866155261034672557828650, [3,4,1,0,2,6,5,10,9,8,7], [3,2,4,0,1,6,5,10,9,8,7]),
  (341255985497821173986510938792, 323, 712208785242050160808163232623714980, [5,7,4,0,1,6,2,10,9,8,3], [3,4,6,10,2,0,5,1,9,8,7]),
  (341255985497821173986510938792, 325, 710911343615229802161741492257989716, [5,2,4,3,6,1,8,7,0,9,10], [8,5,1,3,2,0,4,7,6,9,10]),
  (341255985497821173986510938792, 326, 710911343615229802161741492257989716, [5,1,4,3,6,2,8,7,0,9,10], [8,1,5,3,2,0,4,7,6,9,10]),
  (341255985497821173986510938792, 327, 710911343924714811983086560982771028, [9,5,4,3,6,1,8,7,0,2,10], [8,5,9,3,2,1,4,7,6,0,10]),
  (341255985497821173986510938792, 337, 712208785242050160808163232623714980, [2,7,4,0,1,6,5,10,9,8,3], [3,4,0,10,2,6,5,1,9,8,7]),
  (341255985497821173986510938792, 338, 712208785242050160808163232623714980, [1,7,4,0,2,6,5,10,9,8,3], [3,0,4,10,2,6,5,1,9,8,7]),
  (341255985497821173986510938792, 339, 709613903844866155261034672557828650, [7,4,1,0,2,6,5,10,9,8,3], [3,2,4,10,1,6,5,0,9,8,7]),
  (341255985497821173986510938792, 340, 710911343615229802161741492257989716, [2,1,4,3,6,5,8,7,0,9,10], [8,1,0,3,2,5,4,7,6,9,10]),
  (341255985497821173986510938792, 341, 710911343924714811983086560982771028, [9,2,4,3,6,1,8,7,0,5,10], [8,5,1,3,2,9,4,7,6,0,10]),
  (341255985497821173986510938792, 342, 710911343924714811983086560982771028, [9,1,4,3,6,2,8,7,0,5,10], [8,1,5,3,2,9,4,7,6,0,10]),
  (341255985497821173986510938792, 343, 710911344543684831625776698432857428, [9,1,0,3,4,2,6,7,8,5,10], [2,1,5,3,4,9,6,7,8,0,10]),
  (341255985497821173986510938792, 680, 716101107338355074174937490168382800, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (340024081829251505351473804626, 45, 709613270019566041146333924206225450, [10,5,1,2,3,9,4,0,6,7,8], [7,2,3,4,6,1,8,9,10,5,0]),
  (340024081829251505351473804626, 141, 709613903225896135618344535107742250, [6,2,1,7,3,5,4,0,8,9,10], [7,2,1,4,6,5,0,3,8,9,10]),
  (340024081829251505351473804626, 165, 709613903225896135618344535107742250, [4,2,1,7,3,5,6,0,8,9,10], [7,2,1,4,0,5,6,3,8,9,10]),
  (340024081829251505351473804626, 169, 709613903225896135618344535107742250, [3,2,1,7,4,5,6,0,8,9,10], [7,2,1,0,4,5,6,3,8,9,10]),
  (340024081829251505351473804626, 172, 709613903225896135618344535107742250, [1,2,3,7,4,5,6,0,8,9,10], [7,0,1,2,4,5,6,3,8,9,10]),
  (340024081829251505351473804626, 173, 708316462836864700529851235250293846, [2,1,3,0,4,5,6,7,8,9,10], [3,1,0,2,4,5,6,7,8,9,10]),
  (340024081829251505351473804626, 338, 712213852132141523136428863523201700, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (340024081829251505351473804626, 525, 709613903225896135618344535107742250, [6,7,1,2,3,5,4,0,10,9,8], [7,2,3,4,6,5,0,1,10,9,8]),
  (340024081829251505351473804626, 549, 709613903225896135618344535107742250, [4,7,1,2,3,5,6,0,10,9,8], [7,2,3,4,0,5,6,1,10,9,8]),
  (340024081829251505351473804626, 553, 709613903225896135618344535107742250, [3,7,1,2,4,5,6,0,10,9,8], [7,2,3,0,4,5,6,1,10,9,8]),
  (340024081829251505351473804626, 556, 709613903225896135618344535107742250, [1,7,3,2,4,5,6,0,10,9,8], [7,0,3,2,4,5,6,1,10,9,8]),
  (340024081829251505351473804626, 557, 708316462836864700529851235250293846, [7,1,3,0,4,5,6,2,10,9,8], [3,1,7,2,4,5,6,0,10,9,8]),
  (340024081829251505351473804626, 645, 710911343924714738196110266144564500, [8,10,5,4,9,1,2,6,7,3,0], [10,5,6,9,3,2,7,8,0,4,1]),
  (340024081829251505351473804626, 649, 710911343924714738196110266144564500, [8,10,5,3,9,1,2,6,7,4,0], [10,5,6,3,9,2,7,8,0,4,1]),
  (340024081829251505351473804626, 652, 710911343924714738196110266144564500, [8,10,5,1,9,3,2,6,7,4,0], [10,3,6,5,9,2,7,8,0,4,1]),
  (340024081829251505351473804626, 653, 713511292830809009986742783084670234, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (340024081829251505351473804626, 673, 710911343924714738196110266144564500, [8,10,5,3,9,1,2,4,7,6,0], [10,5,6,3,7,2,9,8,0,4,1]),
  (340024081829251505351473804626, 676, 710911343924714738196110266144564500, [8,10,5,1,9,3,2,4,7,6,0], [10,3,6,5,7,2,9,8,0,4,1]),
  (340024081829251505351473804626, 677, 713511292830809009986742783084670234, [0,1,2,3,6,5,4,7,8,9,10], [0,1,2,3,6,5,4,7,8,9,10]),
  (340024081829251505351473804626, 680, 710911343924714738196110266144564500, [8,10,5,1,9,4,2,3,7,6,0], [10,3,6,7,5,2,9,8,0,4,1]),
  (340024081829251505351473804626, 681, 713511292830809009986742783084670234, [0,1,2,4,6,5,3,7,8,9,10], [0,1,2,6,3,5,4,7,8,9,10]),
  (340024081829251505351473804626, 684, 713511292830809009986742783084670234, [0,3,2,4,6,5,1,7,8,9,10], [0,6,2,1,3,5,4,7,8,9,10]),
  (340024081829251505351473804626, 685, 713511292830809083773719077922876762, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (341260814122155969111565841036, 83, 714808099704176382722355954295818406, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (341260814122155969111565841036, 172, 710911343924714738196110266144564500, [2,1,3,0,4,5,8,7,6,9,10], [3,1,0,2,4,5,8,7,6,9,10]),
  (341260814122155969111565841036, 275, 710911343924714738196110266144564500, [6,8,5,0,9,3,1,10,2,4,7], [3,6,8,5,9,2,0,10,1,4,7]),
  (341260814122155969111565841036, 323, 714808099704176382722355954295818406, [0,1,2,3,4,9,6,7,8,5,10], [0,1,2,3,4,9,6,7,8,5,10]),
  (341260814122155969111565841036, 337, 710911343924714738196110266144564500, [6,10,5,0,9,3,1,8,7,4,2], [3,6,10,5,9,2,0,8,7,4,1]),
  (341260814122155969111565841036, 338, 710911343924714738196110266144564500, [8,10,5,0,9,3,2,6,7,4,1], [3,10,6,5,9,2,7,8,0,4,1]),
  (341260814122155969111565841036, 339, 713511292830809009986742783084670234, [7,0,1,3,4,5,10,2,6,9,8], [1,2,7,3,4,5,8,0,10,9,6]),
  (341260814122155969111565841036, 556, 710911343924714738196110266144564500, [7,1,3,0,4,5,10,2,6,9,8], [3,1,7,2,4,5,8,0,10,9,6]),
  (341260814122155969111565841036, 652, 710911343924714738196110266144564500, [7,2,3,0,4,5,10,1,8,9,6], [3,7,1,2,4,5,10,0,8,9,6]),
  (341260814122155969111565841036, 676, 714808099704176382722355954295818406, [0,6,8,5,9,3,1,10,2,4,7], [0,6,8,5,9,3,1,10,2,4,7]),
  (341260814122155969111565841036, 680, 714808099704176382722355954295818406, [0,6,8,5,9,4,1,10,2,3,7], [0,6,8,9,5,3,1,10,2,4,7]),
  (341260814122155969111565841036, 684, 713511292830809009986742783084670234, [6,0,8,5,9,3,1,10,2,4,7], [1,6,8,5,9,3,0,10,2,4,7]),
  (341260814122157095011472683692, 19, 709613903225896135618344535107742250, [10,2,3,9,4,1,6,7,8,5,0], [10,5,1,2,4,9,6,7,8,3,0]),
  (341260814122157095011472683692, 44, 712208785242050160808163232623714980, [7,2,3,10,1,4,5,8,9,6,0], [10,4,1,2,5,6,9,0,7,8,3]),
  (341260814122157095011472683692, 67, 709613269400747137231095615402977450, [10,2,3,5,4,1,6,9,8,7,0], [10,5,1,2,4,3,6,9,8,7,0]),
  (341260814122157095011472683692, 81, 709613903225896135618344535107742250, [8,7,3,9,4,1,6,2,10,5,0], [10,5,7,2,4,9,6,1,0,3,8]),
  (341260814122157095011472683692, 82, 709613269400747137231095615402977450, [10,2,3,1,4,5,6,9,8,7,0], [10,3,1,2,4,5,6,9,8,7,0]),
  (341260814122157095011472683692, 83, 713511292830809009986742783084670234, [9,3,2,4,6,1,0,7,8,5,10], [6,5,2,1,3,9,4,7,8,0,10]),
  (341260814122157095011472683692, 140, 709613903225896135618344535107742250, [7,8,1,6,5,3,9,10,2,4,0], [10,2,8,5,9,4,3,0,1,6,7]),
  (341260814122157095011472683692, 164, 709613903225896135618344535107742250, [7,8,1,4,5,3,9,10,2,6,0], [10,2,8,5,3,4,9,0,1,6,7]),
  (341260814122157095011472683692, 168, 709613903225896135618344535107742250, [7,8,1,3,5,4,9,10,2,6,0], [10,2,8,3,5,4,9,0,1,6,7]),
  (341260814122157095011472683692, 172, 710911343924714811983086560982771028, [9,2,3,0,4,1,6,7,8,5,10], [3,5,1,2,4,9,6,7,8,0,10]),
  (341260814122157095011472683692, 259, 709613903225896135618344535107742250, [10,2,3,5,4,1,6,7,8,9,0], [10,5,1,2,4,3,6,7,8,9,0]),
  (341260814122157095011472683692, 273, 712208785242050160808163232623714980, [8,10,1,2,3,5,4,7,6,9,0], [10,2,3,4,6,5,8,7,0,9,1]),
  (341260814122157095011472683692, 274, 709613903225896135618344535107742250, [10,2,3,1,4,5,6,7,8,9,0], [10,3,1,2,4,5,6,7,8,9,0]),
  (341260814122157095011472683692, 275, 710911343924714811983086560982771028, [6,8,1,0,5,3,9,10,2,4,7], [3,2,8,5,9,4,0,10,1,6,7]),
  (341260814122157095011472683692, 321, 709613903225896135618344535107742250, [8,7,3,5,4,1,6,2,10,9,0], [10,5,7,2,4,3,6,1,0,9,8]),
  (341260814122157095011472683692, 322, 709613269400747137231095615402977450, [10,2,3,1,4,9,6,5,8,7,0], [10,3,1,2,4,7,6,9,8,5,0]),
  (341260814122157095011472683692, 323, 713511292830809009986742783084670234, [5,3,2,4,6,1,0,7,8,9,10], [6,5,2,1,3,0,4,7,8,9,10]),
  (341260814122157095011472683692, 336, 709613903225896135618344535107742250, [8,7,3,1,4,5,6,2,10,9,0], [10,3,7,2,4,5,6,1,0,9,8]),
  (341260814122157095011472683692, 337, 710911343924714811983086560982771028, [6,10,1,0,5,3,9,8,7,4,2], [3,2,10,5,9,4,0,8,7,6,1]),
  (341260814122157095011472683692, 338, 713511292830809009986742783084670234, [1,3,2,4,6,5,0,7,8,9,10], [6,0,2,1,3,5,4,7,8,9,10]),
  (341260814122157095011472683692, 339, 713511292830809083773719077922876762, [9,0,2,3,4,1,6,7,8,5,10], [1,5,2,3,4,9,6,7,8,0,10]),
  (341260814122157095011472683692, 524, 709613903225896135618344535107742250, [2,10,1,6,5,3,9,8,7,4,0], [10,2,0,5,9,4,3,8,7,6,1]),
  (341260814122157095011472683692, 548, 709613903225896135618344535107742250, [2,10,1,4,5,3,9,8,7,6,0], [10,2,0,5,3,4,9,8,7,6,1]),
  (341260814122157095011472683692, 552, 709613903225896135618344535107742250, [2,10,1,3,5,4,9,8,7,6,0], [10,2,0,3,5,4,9,8,7,6,1]),
  (341260814122157095011472683692, 556, 710911343924714811983086560982771028, [9,7,3,0,4,1,6,2,10,5,8], [3,5,7,2,4,9,6,1,10,0,8]),
  (341260814122157095011472683692, 644, 709613269400747137231095615402977450, [7,8,1,4,5,3,9,6,2,10,0], [10,2,8,5,3,4,7,0,1,6,9]),
  (341260814122157095011472683692, 648, 709613269400747137231095615402977450, [7,8,1,3,5,4,9,6,2,10,0], [10,2,8,3,5,4,7,0,1,6,9]),
  (341260814122157095011472683692, 652, 713511292830809009986742783084670234, [6,1,8,5,9,3,0,10,2,4,7], [6,1,8,5,9,3,0,10,2,4,7]),
  (341260814122157095011472683692, 672, 709613269400747137231095615402977450, [7,8,1,3,5,6,9,4,2,10,0], [10,2,8,3,7,4,5,0,1,6,9]),
  (341260814122157095011472683692, 676, 713511292830809009986742783084670234, [4,1,8,5,9,3,0,10,2,6,7], [6,1,8,5,0,3,9,10,2,4,7]),
  (341260814122157095011472683692, 680, 713511292830809009986742783084670234, [3,1,8,5,9,4,0,10,2,6,7], [6,1,8,0,5,3,9,10,2,4,7]),
  (341260814122157095011472683692, 684, 713511292830809083773719077922876762, [6,0,8,1,5,3,9,10,2,4,7], [1,3,8,5,9,4,0,10,2,6,7]),
  (340024084190434746786296542546, 13, 709613270019566114897299005625770068, [10,1,2,6,5,3,9,8,7,4,0], [10,1,2,5,9,4,3,8,7,6,0]),
  (340024084190434746786296542546, 37, 709613270019566114897299005625770068, [10,1,2,4,5,3,9,8,7,6,0], [10,1,2,5,3,4,9,8,7,6,0]),
  (340024084190434746786296542546, 41, 709613270019566114897299005625770068, [10,1,2,3,5,4,9,8,7,6,0], [10,1,2,3,5,4,9,8,7,6,0]),
  (340024084190434746786296542546, 44, 709613270019566114897299005625770068, [10,3,2,1,5,4,9,8,7,6,0], [10,3,2,1,5,4,9,8,7,6,0]),
  (340024084190434746786296542546, 45, 709613903844866155261034672557828650, [8,2,1,7,3,5,4,0,6,9,10], [7,2,1,4,6,5,8,3,0,9,10]),
  (340024084190434746786296542546, 82, 712213852132141523136428863523201700, [8,1,9,3,4,2,6,7,0,5,10], [8,1,5,3,4,9,6,7,0,2,10]),
  (340024084190434746786296542546, 133, 709613270019566114897299005625770068, [10,1,2,4,5,3,9,6,7,8,0], [10,1,2,5,3,4,7,8,9,6,0]),
  (340024084190434746786296542546, 137, 709613270019566114897299005625770068, [10,1,2,3,5,4,9,6,7,8,0], [10,1,2,3,5,4,7,8,9,6,0]),
  (340024084190434746786296542546, 140, 709613270019566114897299005625770068, [10,3,2,1,5,4,9,6,7,8,0], [10,3,2,1,5,4,7,8,9,6,0]),
  (340024084190434746786296542546, 141, 709613903844866155261034672557828650, [6,2,1,7,3,5,4,0,8,9,10], [7,2,1,4,6,5,0,3,8,9,10]),
  (340024084190434746786296542546, 161, 709613270019566114897299005625770068, [10,1,2,3,5,6,9,4,7,8,0], [10,1,2,3,7,4,5,8,9,6,0]),
  (340024084190434746786296542546, 164, 709613270019566114897299005625770068, [10,3,2,1,5,6,9,4,7,8,0], [10,3,2,1,7,4,5,8,9,6,0]),
  (340024084190434746786296542546, 165, 709613903844866155261034672557828650, [4,2,1,7,3,5,6,0,8,9,10], [7,2,1,4,0,5,6,3,8,9,10]),
  (340024084190434746786296542546, 168, 709613270019566114897299005625770068, [10,4,2,1,5,6,9,3,7,8,0], [10,3,2,7,1,4,5,8,9,6,0]),
  (340024084190434746786296542546, 169, 709613903844866155261034672557828650, [3,2,1,7,4,5,6,0,8,9,10], [7,2,1,0,4,5,6,3,8,9,10]),
  (340024084190434746786296542546, 172, 709613903844866155261034672557828650, [1,2,3,7,4,5,6,0,8,9,10], [7,0,1,2,4,5,6,3,8,9,10]),
  (340024084190434746786296542546, 173, 708316463146349710351196303975075158, [9,1,3,0,4,2,6,7,8,5,10], [3,1,5,2,4,9,6,7,8,0,10]),
  (340024084190434746786296542546, 274, 716101107338355074174937490168382800, [8,1,3,0,2,4,5,10,9,6,7], [3,1,4,2,5,6,9,10,0,8,7]),
  (340024084190434746786296542546, 322, 712213852132141523136428863523201700, [8,1,5,3,4,2,6,7,0,9,10], [8,1,5,3,4,2,6,7,0,9,10]),
  (340024084190434746786296542546, 336, 712213852132141523136428863523201700, [8,1,2,3,4,5,6,7,0,9,10], [8,1,2,3,4,5,6,7,0,9,10]),
  (340024084190434746786296542546, 338, 712213853370081562421809139496067748, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (340024084190434746786296542546, 517, 708315195804932407990166381541368916, [10,4,2,6,5,1,9,8,7,3,0], [10,5,2,9,1,4,3,8,7,6,0]),
  (340024084190434746786296542546, 521, 708315195804932407990166381541368916, [10,3,2,6,5,1,9,8,7,4,0], [10,5,2,1,9,4,3,8,7,6,0]),
  (340024084190434746786296542546, 524, 708315195804932407990166381541368916, [10,1,2,6,5,3,9,8,7,4,0], [10,1,2,5,9,4,3,8,7,6,0]),
  (340024084190434746786296542546, 525, 710911343924714811983086560982771028, [4,10,2,6,5,1,9,8,7,3,0], [10,5,2,9,0,4,3,8,7,6,1]),
  (340024084190434746786296542546, 545, 708315195804932407990166381541368916, [10,3,2,4,5,1,9,8,7,6,0], [10,5,2,1,3,4,9,8,7,6,0]),
  (340024084190434746786296542546, 548, 708315195804932407990166381541368916, [10,1,2,4,5,3,9,8,7,6,0], [10,1,2,5,3,4,9,8,7,6,0]),
  (340024084190434746786296542546, 549, 710911343924714811983086560982771028, [6,10,2,4,5,1,9,8,7,3,0], [10,5,2,9,3,4,0,8,7,6,1]),
  (340024084190434746786296542546, 552, 708315195804932407990166381541368916, [10,1,2,3,5,4,9,8,7,6,0], [10,1,2,3,5,4,9,8,7,6,0]),
  (340024084190434746786296542546, 553, 710911343924714811983086560982771028, [6,10,2,3,5,1,9,8,7,4,0], [10,5,2,3,9,4,0,8,7,6,1]),
  (340024084190434746786296542546, 556, 710911343924714811983086560982771028, [6,10,2,1,5,3,9,8,7,4,0], [10,3,2,5,9,4,0,8,7,6,1]),
  (340024084190434746786296542546, 557, 713511292830809083773719077922876762, [9,1,0,3,4,2,6,7,8,5,10], [2,1,5,3,4,9,6,7,8,0,10]),
  (340024084190434746786296542546, 641, 708315195804932407990166381541368916, [10,3,2,4,5,1,9,6,7,8,0], [10,5,2,1,3,4,7,8,9,6,0]),
  (340024084190434746786296542546, 644, 708315195804932407990166381541368916, [10,1,2,4,5,3,9,6,7,8,0], [10,1,2,5,3,4,7,8,9,6,0]),
  (340024084190434746786296542546, 645, 710911343924714811983086560982771028, [8,10,2,4,5,1,9,6,7,3,0], [10,5,2,9,3,4,7,8,0,6,1]),
  (340024084190434746786296542546, 648, 708315195804932407990166381541368916, [10,1,2,3,5,4,9,6,7,8,0], [10,1,2,3,5,4,7,8,9,6,0]),
  (340024084190434746786296542546, 649, 710911343924714811983086560982771028, [8,10,2,3,5,1,9,6,7,4,0], [10,5,2,3,9,4,7,8,0,6,1]),
  (340024084190434746786296542546, 652, 710911343924714811983086560982771028, [8,10,2,1,5,3,9,6,7,4,0], [10,3,2,5,9,4,7,8,0,6,1]),
  (340024084190434746786296542546, 653, 713511292830809083773719077922876762, [9,1,0,3,4,2,8,7,6,5,10], [2,1,5,3,4,9,8,7,6,0,10]),
  (340024084190434746786296542546, 672, 708315195804932407990166381541368916, [10,1,2,3,5,6,9,4,7,8,0], [10,1,2,3,7,4,5,8,9,6,0]),
  (340024084190434746786296542546, 673, 710911343924714811983086560982771028, [8,10,2,3,5,1,9,4,7,6,0], [10,5,2,3,7,4,9,8,0,6,1]),
  (340024084190434746786296542546, 676, 710911343924714811983086560982771028, [8,10,2,1,5,3,9,4,7,6,0], [10,3,2,5,7,4,9,8,0,6,1]),
  (340024084190434746786296542546, 677, 713511292830809083773719077922876762, [9,1,0,3,6,2,8,7,4,5,10], [2,1,5,3,8,9,4,7,6,0,10]),
  (340024084190434746786296542546, 680, 710911343924714811983086560982771028, [8,10,2,1,5,4,9,3,7,6,0], [10,3,2,7,5,4,9,8,0,6,1]),
  (340024084190434746786296542546, 681, 713511292830809083773719077922876762, [9,1,0,4,6,2,8,7,3,5,10], [2,1,5,8,3,9,4,7,6,0,10]),
  (340024084190434746786296542546, 684, 713511292830809083773719077922876762, [9,3,0,4,6,2,8,7,1,5,10], [2,8,5,1,3,9,4,7,6,0,10]),
  (340024084190434746786296542546, 685, 713511294068749123059099353895742810, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (341260816483340336446295421612, 3, 707017755415598741446769424391121450, [10,5,3,9,4,1,6,7,8,2,0], [10,5,9,2,4,1,6,7,8,3,0]),
  (341260816483340336446295421612, 12, 707017755415598741446769424391121450, [7,6,1,8,2,3,5,10,9,4,0], [10,2,4,5,9,6,1,0,3,8,7]),
  (341260816483340336446295421612, 17, 707017755415598741446769424391121450, [10,2,3,9,4,1,6,7,8,5,0], [10,5,1,2,4,9,6,7,8,3,0]),
  (341260816483340336446295421612, 18, 707017755415598741446769424391121450, [10,1,3,9,4,2,6,7,8,5,0], [10,1,5,2,4,9,6,7,8,3,0]),
  (341260816483340336446295421612, 19, 709613903844866155261034672557828650, [10,1,3,9,4,2,6,7,8,5,0], [10,1,5,2,4,9,6,7,8,3,0]),
  (341260816483340336446295421612, 36, 707017755415598741446769424391121450, [7,4,1,8,2,3,5,10,9,6,0], [10,2,4,5,1,6,9,0,3,8,7]),
  (341260816483340336446295421612, 40, 707017755415598741446769424391121450, [7,3,1,8,2,4,5,10,9,6,0], [10,2,4,1,5,6,9,0,3,8,7]),
  (341260816483340336446295421612, 44, 709613903844866155261034672557828650, [7,3,1,8,2,4,5,10,9,6,0], [10,2,4,1,5,6,9,0,3,8,7]),
  (341260816483340336446295421612, 65, 707017121590449743059520504686356650, [10,2,3,5,4,1,6,9,8,7,0], [10,5,1,2,4,3,6,9,8,7,0]),
  (341260816483340336446295421612, 66, 707017121590449743059520504686356650, [10,1,3,5,4,2,6,9,8,7,0], [10,1,5,2,4,3,6,9,8,7,0]),
  (341260816483340336446295421612, 67, 708316462836864700529851235250293846, [7,3,4,5,6,1,8,9,10,2,0], [10,5,9,1,2,3,4,0,6,7,8]),
  (341260816483340336446295421612, 80, 707017121590449743059520504686356650, [10,1,3,2,4,5,6,9,8,7,0], [10,1,3,2,4,5,6,9,8,7,0]),
  (341260816483340336446295421612, 81, 708316462836864700529851235250293846, [7,3,4,2,6,1,8,9,10,5,0], [10,5,3,1,2,9,4,0,6,7,8]),
  (341260816483340336446295421612, 82, 708316462836864700529851235250293846, [7,3,4,1,6,2,8,9,10,5,0], [10,3,5,1,2,9,4,0,6,7,8]),
  (341260816483340336446295421612, 83, 713511292830809083773719077922876762, [5,3,9,4,6,1,8,7,0,2,10], [8,5,9,1,3,0,4,7,6,2,10]),
  (341260816483340336446295421612, 132, 707017755415598741446769424391121450, [7,4,1,6,2,3,5,10,9,8,0], [10,2,4,5,1,6,3,0,9,8,7]),
  (341260816483340336446295421612, 136, 707017755415598741446769424391121450, [7,3,1,6,2,4,5,10,9,8,0], [10,2,4,1,5,6,3,0,9,8,7]),
  (341260816483340336446295421612, 140, 709613903844866155261034672557828650, [7,3,1,6,2,4,5,10,9,8,0], [10,2,4,1,5,6,3,0,9,8,7]),
  (341260816483340336446295421612, 160, 707017755415598741446769424391121450, [7,3,1,4,2,6,5,10,9,8,0], [10,2,4,1,3,6,5,0,9,8,7]),
  (341260816483340336446295421612, 164, 709613903844866155261034672557828650, [7,3,1,4,2,6,5,10,9,8,0], [10,2,4,1,3,6,5,0,9,8,7]),
  (341260816483340336446295421612, 168, 709613903844866155261034672557828650, [7,4,1,3,2,6,5,10,9,8,0], [10,2,4,3,1,6,5,0,9,8,7]),
  (341260816483340336446295421612, 172, 710911344543684831625776698432857428, [9,1,3,0,4,2,6,7,8,5,10], [3,1,5,2,4,9,6,7,8,0,10]),
  (341260816483340336446295421612, 257, 707017755415598741446769424391121450, [10,2,3,5,4,1,6,7,8,9,0], [10,5,1,2,4,3,6,7,8,9,0]),
  (341260816483340336446295421612, 258, 707017755415598741446769424391121450, [10,1,3,5,4,2,6,7,8,9,0], [10,1,5,2,4,3,6,7,8,9,0]),
  (341260816483340336446295421612, 259, 709613903844866155261034672557828650, [10,1,3,5,4,2,6,7,8,9,0], [10,1,5,2,4,3,6,7,8,9,0]),
  (341260816483340336446295421612, 272, 707017755415598741446769424391121450, [10,1,3,2,4,5,6,7,8,9,0], [10,1,3,2,4,5,6,7,8,9,0]),
  (341260816483340336446295421612, 273, 709613903844866155261034672557828650, [10,1,3,2,4,5,6,7,8,9,0], [10,1,3,2,4,5,6,7,8,9,0]),
  (341260816483340336446295421612, 274, 709613903844866155261034672557828650, [10,2,3,1,4,5,6,7,8,9,0], [10,3,1,2,4,5,6,7,8,9,0]),
  (341260816483340336446295421612, 275, 710911344543684831625776698432857428, [8,3,1,0,2,4,5,10,9,6,7], [3,2,4,1,5,6,9,10,0,8,7]),
  (341260816483340336446295421612, 320, 707017121590449743059520504686356650, [10,1,3,2,4,9,6,5,8,7,0], [10,1,3,2,4,7,6,9,8,5,0]),
  (341260816483340336446295421612, 321, 708316462836864700529851235250293846, [7,3,4,2,6,1,8,5,10,9,0], [10,5,3,1,2,7,4,0,6,9,8]),
  (341260816483340336446295421612, 322, 708316462836864700529851235250293846, [7,3,4,1,6,2,8,5,10,9,0], [10,3,5,1,2,7,4,0,6,9,8]),
  (341260816483340336446295421612, 323, 713511292830809083773719077922876762, [9,3,5,4,6,1,8,7,0,2,10], [8,5,9,1,3,2,4,7,6,0,10]),
  (341260816483340336446295421612, 336, 708316462836864700529851235250293846, [7,3,4,1,6,5,8,2,10,9,0], [10,3,7,1,2,5,4,0,6,9,8]),
  (341260816483340336446295421612, 337, 713511292830809083773719077922876762, [9,3,2,4,6,1,8,7,0,5,10], [8,5,2,1,3,9,4,7,6,0,10]),
  (341260816483340336446295421612, 338, 713511292830809083773719077922876762, [9,3,1,4,6,2,8,7,0,5,10], [8,2,5,1,3,9,4,7,6,0,10]),
  (341260816483340336446295421612, 339, 713511294068749123059099353895742810, [9,0,1,3,4,2,6,7,8,5,10], [1,2,5,3,4,9,6,7,8,0,10]),
  (341260816483340336446295421612, 516, 707017121590449743059520504686356650, [7,4,1,6,2,3,5,8,9,10,0], [10,2,4,5,1,6,3,0,7,8,9]),
  (341260816483340336446295421612, 520, 707017121590449743059520504686356650, [7,3,1,6,2,4,5,8,9,10,0], [10,2,4,1,5,6,3,0,7,8,9]),
  (341260816483340336446295421612, 524, 708316462836864700529851235250293846, [10,1,2,6,5,3,9,8,7,4,0], [10,1,2,5,9,4,3,8,7,6,0]),
  (341260816483340336446295421612, 544, 707017121590449743059520504686356650, [7,3,1,4,2,6,5,8,9,10,0], [10,2,4,1,3,6,5,0,7,8,9]),
  (341260816483340336446295421612, 548, 708316462836864700529851235250293846, [10,1,2,4,5,3,9,8,7,6,0], [10,1,2,5,3,4,9,8,7,6,0]),
  (341260816483340336446295421612, 552, 708316462836864700529851235250293846, [10,1,2,3,5,4,9,8,7,6,0], [10,1,2,3,5,4,9,8,7,6,0]),
  (341260816483340336446295421612, 556, 713511292830809083773719077922876762, [6,1,8,2,5,3,9,10,0,4,7], [8,1,3,5,9,4,0,10,2,6,7]),
  (341260816483340336446295421612, 576, 716106175156750276452792647004374144, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (341260816483340336446295421612, 640, 707017121590449743059520504686356650, [7,3,1,4,2,8,5,6,9,10,0], [10,2,4,1,3,6,7,0,5,8,9]),
  (341260816483340336446295421612, 644, 708316462836864700529851235250293846, [10,1,2,4,5,3,9,6,7,8,0], [10,1,2,5,3,4,7,8,9,6,0]),
  (341260816483340336446295421612, 648, 708316462836864700529851235250293846, [10,1,2,3,5,4,9,6,7,8,0], [10,1,2,3,5,4,7,8,9,6,0]),
  (341260816483340336446295421612, 652, 713511292830809083773719077922876762, [8,1,6,2,5,3,9,10,0,4,7], [8,1,3,5,9,4,2,10,0,6,7]),
  (341260816483340336446295421612, 672, 708316462836864700529851235250293846, [10,1,2,3,5,6,9,4,7,8,0], [10,1,2,3,7,4,5,8,9,6,0]),
  (341260816483340336446295421612, 676, 713511292830809083773719077922876762, [8,1,4,2,5,3,9,10,0,6,7], [8,1,3,5,2,4,9,10,0,6,7]),
  (341260816483340336446295421612, 680, 713511292830809083773719077922876762, [8,1,3,2,5,4,9,10,0,6,7], [8,1,3,2,5,4,9,10,0,6,7]),
  (341260816483340336446295421612, 684, 713511294068749123059099353895742810, [8,0,3,1,2,4,5,10,9,6,7], [1,3,4,2,5,6,9,10,0,8,7]),
  (368546222791744933032436737750, 6, 707017121899783710904378826183844180, [10,5,1,7,4,2,6,8,9,3,0], [10,2,5,9,4,1,6,3,7,8,0]),
  (368546222791744933032436737750, 9, 707019022447682149713906106746880680, [10,2,3,6,5,1,7,9,8,4,0], [10,5,1,2,9,4,3,6,8,7,0]),
  (368546222791744933032436737750, 18, 707017121899783710904378826183844180, [10,3,1,7,4,2,6,8,9,5,0], [10,2,5,1,4,9,6,3,7,8,0]),
  (368546222791744933032436737750, 20, 707017121899783710904378826183844180, [10,2,1,7,4,3,6,8,9,5,0], [10,2,1,5,4,9,6,3,7,8,0]),
  (368546222791744933032436737750, 22, 708315196114417417811511450266150228, [5,7,1,8,4,2,6,10,9,3,0], [10,2,5,9,4,0,6,1,3,8,7]),
  (368546222791744933032436737750, 33, 707019022447682149713906106746880680, [10,2,3,4,5,1,7,9,8,6,0], [10,5,1,2,3,4,9,6,8,7,0]),
  (368546222791744933032436737750, 40, 707019022447682149713906106746880680, [10,2,3,1,5,4,7,9,8,6,0], [10,3,1,2,5,4,9,6,8,7,0]),
  (368546222791744933032436737750, 41, 712213853370081562421809139496067748, [10,2,1,3,5,4,7,9,8,6,0], [10,2,1,3,5,4,9,6,8,7,0]),
  (368546222791744933032436737750, 66, 707017121899783710904378826183844180, [10,3,1,5,4,2,6,8,9,7,0], [10,2,5,1,4,3,6,9,7,8,0]),
  (368546222791744933032436737750, 68, 707017121899783710904378826183844180, [10,2,1,5,4,3,6,8,9,7,0], [10,2,1,5,4,3,6,9,7,8,0]),
  (368546222791744933032436737750, 70, 708315196114417417811511450266150228, [7,5,1,8,4,2,6,10,9,3,0], [10,2,5,9,4,1,6,0,3,8,7]),
  (368546222791744933032436737750, 80, 707017121899783710904378826183844180, [10,2,1,3,4,5,6,8,9,7,0], [10,2,1,3,4,5,6,9,7,8,0]),
  (368546222791744933032436737750, 82, 708315196114417417811511450266150228, [7,3,1,8,4,2,6,10,9,5,0], [10,2,5,1,4,9,6,0,3,8,7]),
  (368546222791744933032436737750, 84, 708315196114417417811511450266150228, [7,2,1,8,4,3,6,10,9,5,0], [10,2,1,5,4,9,6,0,3,8,7]),
  (368546222791744933032436737750, 86, 710911344543684831625776698432857428, [7,2,1,8,4,3,6,10,9,5,0], [10,2,1,5,4,9,6,0,3,8,7]),
  (368546222791744933032436737750, 130, 707017121899783710904378826183844180, [10,3,1,5,4,2,6,7,9,8,0], [10,2,5,1,4,3,6,7,9,8,0]),
  (368546222791744933032436737750, 132, 707017121899783710904378826183844180, [10,2,1,5,4,3,6,7,9,8,0], [10,2,1,5,4,3,6,7,9,8,0]),
  (368546222791744933032436737750, 134, 708315196114417417811511450266150228, [8,5,1,7,4,2,6,10,9,3,0], [10,2,5,9,4,1,6,3,0,8,7]),
  (368546222791744933032436737750, 144, 707017121899783710904378826183844180, [10,2,1,3,4,5,6,7,9,8,0], [10,2,1,3,4,5,6,7,9,8,0]),
  (368546222791744933032436737750, 146, 708315196114417417811511450266150228, [8,3,1,7,4,2,6,10,9,5,0], [10,2,5,1,4,9,6,3,0,8,7]),
  (368546222791744933032436737750, 148, 708315196114417417811511450266150228, [8,2,1,7,4,3,6,10,9,5,0], [10,2,1,5,4,9,6,3,0,8,7]),
  (368546222791744933032436737750, 150, 710911344543684831625776698432857428, [8,2,1,7,4,3,6,10,9,5,0], [10,2,1,5,4,9,6,3,0,8,7]),
  (368546222791744933032436737750, 192, 707017121899783710904378826183844180, [10,2,1,3,4,7,6,5,9,8,0], [10,2,1,3,4,7,6,5,9,8,0]),
  (368546222791744933032436737750, 194, 708315196114417417811511450266150228, [8,3,1,5,4,2,6,10,9,7,0], [10,2,5,1,4,3,6,9,0,8,7]),
  (368546222791744933032436737750, 196, 708315196114417417811511450266150228, [8,2,1,5,4,3,6,10,9,7,0], [10,2,1,5,4,3,6,9,0,8,7]),
  (368546222791744933032436737750, 198, 710911344543684831625776698432857428, [8,2,1,5,4,3,6,10,9,7,0], [10,2,1,5,4,3,6,9,0,8,7]),
  (368546222791744933032436737750, 208, 708315196114417417811511450266150228, [8,2,1,3,4,5,6,10,9,7,0], [10,2,1,3,4,5,6,9,0,8,7]),
  (368546222791744933032436737750, 210, 710911344543684831625776698432857428, [8,2,1,3,4,5,6,10,9,7,0], [10,2,1,3,4,5,6,9,0,8,7]),
  (368546222791744933032436737750, 212, 710911344543684831625776698432857428, [8,3,1,2,4,5,6,10,9,7,0], [10,2,3,1,4,5,6,9,0,8,7]),
  (368546222791744933032436737750, 214, 713511294068749123059099353895742810, [9,2,1,3,5,4,7,0,8,6,10], [7,2,1,3,5,4,9,6,8,0,10]),
  (368546222791744933032436737750, 257, 707019022447682149713906106746880680, [10,2,3,4,5,1,7,6,8,9,0], [10,5,1,2,3,4,7,6,8,9,0]),
  (368546222791744933032436737750, 264, 707019022447682149713906106746880680, [10,2,3,1,5,4,7,6,8,9,0], [10,3,1,2,5,4,7,6,8,9,0]),
  (368546222791744933032436737750, 265, 712213853370081562421809139496067748, [10,2,1,3,5,4,7,6,8,9,0], [10,2,1,3,5,4,7,6,8,9,0]),
  (368546222791744933032436737750, 288, 707019022447682149713906106746880680, [10,2,3,1,5,6,7,4,8,9,0], [10,3,1,2,7,4,5,6,8,9,0]),
  (368546222791744933032436737750, 289, 712213853370081562421809139496067748, [10,2,1,3,5,6,7,4,8,9,0], [10,2,1,3,7,4,5,6,8,9,0]),
  (368546222791744933032436737750, 296, 712213853370081562421809139496067748, [10,2,4,3,5,6,7,1,8,9,0], [10,7,1,3,2,4,5,6,8,9,0]),
  (368546222791744933032436737750, 297, 771977215577453521385551478926436946, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (368546222791744933032436737750, 514, 707017121899783710904378826183844180, [8,3,1,5,4,2,6,7,9,10,0], [10,2,5,1,4,3,6,7,0,8,9]),
  (368546222791744933032436737750, 516, 707017121899783710904378826183844180, [8,2,1,5,4,3,6,7,9,10,0], [10,2,1,5,4,3,6,7,0,8,9]),
  (368546222791744933032436737750, 518, 708315196114417417811511450266150228, [10,5,1,7,4,2,6,8,9,3,0], [10,2,5,9,4,1,6,3,7,8,0]),
  (368546222791744933032436737750, 528, 707017121899783710904378826183844180, [8,2,1,3,4,5,6,7,9,10,0], [10,2,1,3,4,5,6,7,0,8,9]),
  (368546222791744933032436737750, 530, 708315196114417417811511450266150228, [10,3,1,7,4,2,6,8,9,5,0], [10,2,5,1,4,9,6,3,7,8,0]),
  (368546222791744933032436737750, 532, 708315196114417417811511450266150228, [10,2,1,7,4,3,6,8,9,5,0], [10,2,1,5,4,9,6,3,7,8,0]),
  (368546222791744933032436737750, 534, 710911344543684831625776698432857428, [10,2,1,7,4,3,6,8,9,5,0], [10,2,1,5,4,9,6,3,7,8,0]),
  (368546222791744933032436737750, 576, 707017121899783710904378826183844180, [8,2,1,3,4,7,6,5,9,10,0], [10,2,1,3,4,7,6,5,0,8,9]),
  (368546222791744933032436737750, 578, 708315196114417417811511450266150228, [10,3,1,5,4,2,6,8,9,7,0], [10,2,5,1,4,3,6,9,7,8,0]),
  (368546222791744933032436737750, 580, 708315196114417417811511450266150228, [10,2,1,5,4,3,6,8,9,7,0], [10,2,1,5,4,3,6,9,7,8,0]),
  (368546222791744933032436737750, 582, 710911344543684831625776698432857428, [10,2,1,5,4,3,6,8,9,7,0], [10,2,1,5,4,3,6,9,7,8,0]),
  (368546222791744933032436737750, 592, 708315196114417417811511450266150228, [10,2,1,3,4,5,6,8,9,7,0], [10,2,1,3,4,5,6,9,7,8,0]),
  (368546222791744933032436737750, 594, 710911344543684831625776698432857428, [10,2,1,3,4,5,6,8,9,7,0], [10,2,1,3,4,5,6,9,7,8,0]),
  (368546222791744933032436737750, 596, 710911344543684831625776698432857428, [10,3,1,2,4,5,6,8,9,7,0], [10,2,3,1,4,5,6,9,7,8,0]),
  (368546222791744933032436737750, 598, 713511294068749123059099353895742810, [9,2,1,3,5,4,7,0,10,6,8], [7,2,1,3,5,4,9,6,10,0,8]),
  (368546222791744933032436737750, 640, 707017121899783710904378826183844180, [7,2,1,3,4,8,6,5,9,10,0], [10,2,1,3,4,7,6,0,5,8,9]),
  (368546222791744933032436737750, 642, 708315196114417417811511450266150228, [10,3,1,5,4,2,6,7,9,8,0], [10,2,5,1,4,3,6,7,9,8,0]),
  (368546222791744933032436737750, 644, 708315196114417417811511450266150228, [10,2,1,5,4,3,6,7,9,8,0], [10,2,1,5,4,3,6,7,9,8,0]),
  (368546222791744933032436737750, 646, 710911344543684831625776698432857428, [10,2,1,5,4,3,6,7,9,8,0], [10,2,1,5,4,3,6,7,9,8,0]),
  (368546222791744933032436737750, 656, 708315196114417417811511450266150228, [10,2,1,3,4,5,6,7,9,8,0], [10,2,1,3,4,5,6,7,9,8,0]),
  (368546222791744933032436737750, 658, 710911344543684831625776698432857428, [10,2,1,3,4,5,6,7,9,8,0], [10,2,1,3,4,5,6,7,9,8,0]),
  (368546222791744933032436737750, 660, 710911344543684831625776698432857428, [10,3,1,2,4,5,6,7,9,8,0], [10,2,3,1,4,5,6,7,9,8,0]),
  (368546222791744933032436737750, 662, 713511294068749123059099353895742810, [9,2,1,3,5,4,8,0,10,6,7], [7,2,1,3,5,4,9,10,6,0,8]),
  (368546222791744933032436737750, 704, 708315196114417417811511450266150228, [10,2,1,3,4,7,6,5,9,8,0], [10,2,1,3,4,7,6,5,9,8,0]),
  (368546222791744933032436737750, 706, 710911344543684831625776698432857428, [10,2,1,3,4,7,6,5,9,8,0], [10,2,1,3,4,7,6,5,9,8,0]),
  (368546222791744933032436737750, 708, 710911344543684831625776698432857428, [10,3,1,2,4,7,6,5,9,8,0], [10,2,3,1,4,7,6,5,9,8,0]),
  (368546222791744933032436737750, 710, 713511294068749123059099353895742810, [9,2,1,3,7,4,8,0,10,6,5], [7,2,1,3,5,10,9,4,6,0,8]),
  (368546222791744933032436737750, 720, 710911344543684831625776698432857428, [10,5,1,2,4,7,6,3,9,8,0], [10,2,3,7,4,1,6,5,9,8,0]),
  (368546222791744933032436737750, 722, 713511294068749123059099353895742810, [9,2,1,5,7,4,8,0,10,6,3], [7,2,1,10,5,3,9,4,6,0,8]),
  (368546222791744933032436737750, 724, 713511294068749123059099353895742810, [9,3,1,5,7,4,8,0,10,6,2], [7,2,10,1,5,3,9,4,6,0,8]),
  (368546222791744933032436737750, 726, 773274656276423165975815170617599404, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (371019687382163299164986495700, 1, 777166344548031911844911613880387586, [0,1,2,3,4,5,6,7,8,9,10], [0,1,2,3,4,5,6,7,8,9,10]),
  (371019687382163299164986495700, 2, 777166344548031911844911613880387586, [0,2,1,3,4,5,6,7,8,9,10], [0,2,1,3,4,5,6,7,8,9,10]),
  (371019687382163299164986495700, 3, 707017755415749857174221253037959850, [10,4,3,6,5,1,7,9,8,2,0], [10,5,9,2,1,4,3,6,8,7,0]),
  (371019687382163299164986495700, 4, 777166344548031911844911613880387586, [0,3,5,1,7,2,8,4,6,10,9], [0,3,5,1,7,2,8,4,6,10,9]),
  (371019687382163299164986495700, 8, 777166344548031911844911613880387586, [0,4,1,3,2,5,6,7,8,9,10], [0,2,4,3,1,5,6,7,8,9,10]),
  (371019687382163299164986495700, 9, 707017755415749857174221253037959850, [10,2,3,6,5,1,7,9,8,4,0], [10,5,1,2,9,4,3,6,8,7,0]),
  (371019687382163299164986495700, 10, 707017755415749857174221253037959850, [10,1,3,6,5,2,7,9,8,4,0], [10,1,5,2,9,4,3,6,8,7,0]),
  (371019687382163299164986495700, 11, 708316463146349710351196303975075158, [4,3,5,6,7,1,8,9,10,2,0], [10,5,9,1,0,2,3,4,6,7,8]),
  (371019687382163299164986495700, 16, 777166344548031911844911613880387586, [0,5,3,1,7,2,8,4,6,10,9], [0,3,5,2,7,1,8,4,6,10,9]),
  (371019687382163299164986495700, 20, 707017755415749857174221253037959850, [9,7,1,8,2,3,4,10,6,5,0], [10,2,4,5,6,9,8,1,3,0,7]),
  (371019687382163299164986495700, 32, 777166344548031911844911613880387586, [0,6,1,3,2,5,4,7,8,9,10], [0,2,4,3,6,5,1,7,8,9,10]),
  (371019687382163299164986495700, 33, 707017755415749857174221253037959850, [10,2,3,4,5,1,7,9,8,6,0], [10,5,1,2,3,4,9,6,8,7,0]),
  (371019687382163299164986495700, 34, 707017755415749857174221253037959850, [10,1,3,4,5,2,7,9,8,6,0], [10,1,5,2,3,4,9,6,8,7,0]),
  (371019687382163299164986495700, 35, 708316463146349710351196303975075158, [6,3,5,4,7,1,8,9,10,2,0], [10,5,9,1,3,2,0,4,6,7,8]),
  (371019687382163299164986495700, 40, 707017755415749857174221253037959850, [10,1,3,2,5,4,7,9,8,6,0], [10,1,3,2,5,4,9,6,8,7,0]),
  (371019687382163299164986495700, 41, 708316463146349710351196303975075158, [6,3,5,2,7,1,8,9,10,4,0], [10,5,3,1,9,2,0,4,6,7,8]),
  (371019687382163299164986495700, 42, 708316463146349710351196303975075158, [6,3,5,1,7,2,8,9,10,4,0], [10,3,5,1,9,2,0,4,6,7,8]),
  (371019687382163299164986495700, 43, 713511294068749123059099353895742810, [6,3,1,5,7,2,8,9,10,4,0], [10,2,5,1,9,3,0,4,6,7,8]),
  (371019687382163299164986495700, 64, 777166344548031911844911613880387586, [0,7,3,1,5,2,8,4,6,10,9], [0,3,5,2,7,4,8,1,6,10,9]),
  (371019687382163299164986495700, 68, 707017755415749857174221253037959850, [9,5,1,8,2,3,4,10,6,7,0], [10,2,4,5,6,1,8,9,3,0,7]),
  (371019687382163299164986495700, 80, 707017755415749857174221253037959850, [9,3,1,8,2,5,4,10,6,7,0], [10,2,4,1,6,5,8,9,3,0,7]),
  (371019687382163299164986495700, 84, 708316463146349710351196303975075158, [7,1,2,8,4,3,6,10,9,5,0], [10,1,2,5,4,9,6,0,3,8,7]),
  (371019687382163299164986495700, 128, 777166344548031911844911613880387586, [0,8,3,1,5,2,7,4,6,10,9], [0,3,5,2,7,4,8,6,1,10,9]),
  (371019687382163299164986495700, 132, 707017755415749857174221253037959850, [9,5,1,7,2,3,4,10,6,8,0], [10,2,4,5,6,1,8,3,9,0,7]),
  (371019687382163299164986495700, 144, 707017755415749857174221253037959850, [9,3,1,7,2,5,4,10,6,8,0], [10,2,4,1,6,5,8,3,9,0,7]),
  (371019687382163299164986495700, 148, 708316463146349710351196303975075158, [8,1,2,7,4,3,6,10,9,5,0], [10,1,2,5,4,9,6,3,0,8,7]),
  (371019687382163299164986495700, 192, 707017755415749857174221253037959850, [9,3,1,5,2,7,4,10,6,8,0], [10,2,4,1,6,3,8,5,9,0,7]),
  (371019687382163299164986495700, 196, 708316463146349710351196303975075158, [8,1,2,5,4,3,6,10,9,7,0], [10,1,2,5,4,3,6,9,0,8,7]),
  (371019687382163299164986495700, 208, 708316463146349710351196303975075158, [8,1,2,3,4,5,6,10,9,7,0], [10,1,2,3,4,5,6,9,0,8,7]),
  (371019687382163299164986495700, 212, 713511294068749123059099353895742810, [8,1,3,2,4,5,6,10,9,7,0], [10,1,3,2,4,5,6,9,0,8,7]),
  (371019687382163299164986495700, 256, 777166344548031911844911613880387586, [0,9,1,3,2,5,4,7,8,6,10], [0,2,4,3,6,5,9,7,8,1,10]),
  (371019687382163299164986495700, 257, 707017755415749857174221253037959850, [10,2,3,4,5,1,7,6,8,9,0], [10,5,1,2,3,4,7,6,8,9,0]),
  (371019687382163299164986495700, 258, 707017755415749857174221253037959850, [10,1,3,4,5,2,7,6,8,9,0], [10,1,5,2,3,4,7,6,8,9,0]),
  (371019687382163299164986495700, 259, 708316463146349710351196303975075158, [9,3,5,4,7,1,8,6,10,2,0], [10,5,9,1,3,2,7,4,6,0,8]),
  (371019687382163299164986495700, 264, 707017755415749857174221253037959850, [10,1,3,2,5,4,7,6,8,9,0], [10,1,3,2,5,4,7,6,8,9,0]),
  (371019687382163299164986495700, 265, 708316463146349710351196303975075158, [9,3,5,2,7,1,8,6,10,4,0], [10,5,3,1,9,2,7,4,6,0,8]),
  (371019687382163299164986495700, 266, 708316463146349710351196303975075158, [9,3,5,1,7,2,8,6,10,4,0], [10,3,5,1,9,2,7,4,6,0,8]),
  (371019687382163299164986495700, 267, 713511294068749123059099353895742810, [9,3,1,5,7,2,8,6,10,4,0], [10,2,5,1,9,3,7,4,6,0,8]),
  (371019687382163299164986495700, 288, 707017755415749857174221253037959850, [10,1,3,2,5,6,7,4,8,9,0], [10,1,3,2,7,4,5,6,8,9,0]),
  (371019687382163299164986495700, 289, 708316463146349710351196303975075158, [9,3,5,2,7,1,8,4,10,6,0], [10,5,3,1,7,2,9,4,6,0,8]),
  (371019687382163299164986495700, 290, 708316463146349710351196303975075158, [9,3,5,1,7,2,8,4,10,6,0], [10,3,5,1,7,2,9,4,6,0,8]),
  (371019687382163299164986495700, 291, 713511294068749123059099353895742810, [9,3,1,5,7,2,8,4,10,6,0], [10,2,5,1,7,3,9,4,6,0,8]),
  (371019687382163299164986495700, 296, 708316463146349710351196303975075158, [9,3,5,1,7,4,8,2,10,6,0], [10,3,7,1,5,2,9,4,6,0,8]),
  (371019687382163299164986495700, 297, 713511294068749123059099353895742810, [9,3,1,5,7,4,8,2,10,6,0], [10,2,7,1,5,3,9,4,6,0,8]),
  (371019687382163299164986495700, 298, 713511294068749123059099353895742810, [9,3,2,5,7,4,8,1,10,6,0], [10,7,2,1,5,3,9,4,6,0,8]),
  (371019687382163299164986495700, 299, 773274656276423165975815170617599404, [9,1,0,3,2,5,4,7,8,6,10], [2,1,4,3,6,5,9,7,8,0,10]),
  (371019687382163299164986495700, 512, 777166344548031911844911613880387586, [0,10,3,1,5,2,7,4,6,8,9], [0,3,5,2,7,4,8,6,9,10,1]),
  (371019687382163299164986495700, 516, 707017755415749857174221253037959850, [9,5,1,7,2,3,4,8,6,10,0], [10,2,4,5,6,1,8,3,7,0,9]),
  (371019687382163299164986495700, 528, 707017755415749857174221253037959850, [9,3,1,7,2,5,4,8,6,10,0], [10,2,4,1,6,5,8,3,7,0,9]),
  (371019687382163299164986495700, 532, 708316463146349710351196303975075158, [10,1,2,7,4,3,6,8,9,5,0], [10,1,2,5,4,9,6,3,7,8,0]),
  (371019687382163299164986495700, 576, 707017755415749857174221253037959850, [9,3,1,5,2,7,4,8,6,10,0], [10,2,4,1,6,3,8,5,7,0,9]),
  (371019687382163299164986495700, 580, 708316463146349710351196303975075158, [10,1,2,5,4,3,6,8,9,7,0], [10,1,2,5,4,3,6,9,7,8,0]),
  (371019687382163299164986495700, 592, 708316463146349710351196303975075158, [10,1,2,3,4,5,6,8,9,7,0], [10,1,2,3,4,5,6,9,7,8,0]),
  (371019687382163299164986495700, 596, 713511294068749123059099353895742810, [10,1,3,2,4,5,6,8,9,7,0], [10,1,3,2,4,5,6,9,7,8,0]),
  (371019687382163299164986495700, 640, 707017755415749857174221253037959850, [9,3,1,5,2,8,4,7,6,10,0], [10,2,4,1,6,3,8,7,5,0,9]),
  (371019687382163299164986495700, 644, 708316463146349710351196303975075158, [10,1,2,5,4,3,6,7,9,8,0], [10,1,2,5,4,3,6,7,9,8,0]),
  (371019687382163299164986495700, 656, 708316463146349710351196303975075158, [10,1,2,3,4,5,6,7,9,8,0], [10,1,2,3,4,5,6,7,9,8,0]),
  (371019687382163299164986495700, 660, 713511294068749123059099353895742810, [10,1,3,2,4,5,6,7,9,8,0], [10,1,3,2,4,5,6,7,9,8,0]),
  (371019687382163299164986495700, 704, 708316463146349710351196303975075158, [10,1,2,3,4,7,6,5,9,8,0], [10,1,2,3,4,7,6,5,9,8,0]),
  (371019687382163299164986495700, 708, 713511294068749123059099353895742810, [10,1,3,2,4,7,6,5,9,8,0], [10,1,3,2,4,7,6,5,9,8,0]),
  (371019687382163299164986495700, 720, 713511294068749123059099353895742810, [10,1,5,2,4,7,6,3,9,8,0], [10,1,3,7,4,2,6,5,9,8,0]),
  (371019687382163299164986495700, 724, 773274656276423165975815170617599404, [10,3,0,1,5,2,7,4,6,8,9], [2,3,5,1,7,4,8,6,9,10,0])]

set_option maxRecDepth 100000 in
theorem ok11 : StepOK 10 L10 L11 52 C11 := by decide +kernel

theorem cl11 : Classified 11 L11 52 :=
  step 10 L10 L11 43 52 C11 ok11 (by intro E d h1 h2; omega) cl10

def F11 : List (ℕ × Bool × List ℕ) := [
  (707017121590449743059520504686356650, true, [1,0,1,0,1,0,1,0,1,0,1]),
  (707017121899783710904378826183844180, true, [1,1,0,1,0,1,0,1,0,1,0]),
  (707017755415598741446769424391121450, true, [1,0,1,0,1,0,1,0,1,0,1]),
  (707017755415749857174221253037959850, true, [1,0,1,0,1,0,1,0,1,0,1]),
  (708315195804932407990166381541368916, true, [1,1,0,1,0,1,0,1,0,1,0]),
  (708315195805083449930624331749698698, false, [0,1,2,1,2,3,2,1,2,3,4]),
  (708315196114417417811511450266150228, true, [1,1,0,1,0,1,0,1,0,1,0]),
  (707019022447682149713906106746880680, true, [1,1,1,0,1,0,1,0,1,0,1]),
  (708316462836864626742874940412087318, true, [1,0,0,1,0,1,0,1,0,1,0]),
  (708316462836864700529851235250293846, true, [1,0,0,1,0,1,0,1,0,1,0]),
  (708316463146349710351196303975075158, true, [1,0,0,1,0,1,0,1,0,1,0]),
  (709613269400747137231095615402977450, true, [1,0,1,0,1,0,1,0,1,0,1]),
  (709613903225896135618344535107742250, true, [1,0,1,0,1,0,1,0,1,0,1]),
  (710911343615229802161741492257989716, true, [1,1,0,1,0,1,0,1,0,1,0]),
  (710911343924714738196110266144564500, true, [1,1,0,1,0,1,0,1,0,1,0]),
  (710911343924714811983086560982771028, true, [1,1,0,1,0,1,0,1,0,1,0]),
  (709613270019566041146333924206225450, true, [1,0,1,0,1,0,1,0,1,0,1]),
  (709613270019566114897299005625770068, true, [1,1,0,1,0,1,0,1,0,1,0]),
  (709613270019717156837756955834099850, true, [1,0,1,0,1,0,1,0,1,0,1]),
  (709613903844866155261034663967894050, true, [1,0,1,0,1,0,1,0,1,0,1]),
  (709613903844866155261034672557828650, true, [1,0,1,0,1,0,1,0,1,0,1]),
  (710911344543684831625776698432857428, true, [1,1,0,1,0,1,0,1,0,1,0]),
  (712208785242050160808163232623714980, true, [1,1,0,0,1,0,1,0,1,0,1]),
  (716101107338355074174937490168382800, true, [1,1,1,1,0,1,0,1,0,1,0]),
  (712213852132141523136428863523201700, true, [1,1,0,1,1,0,1,0,1,0,1]),
  (713511292830809009986742783084670234, true, [1,0,1,0,0,1,0,1,0,1,0]),
  (713511292830809083773719077922876762, true, [1,0,1,0,0,1,0,1,0,1,0]),
  (714808099704176382722355954295818406, true, [1,0,0,1,1,0,1,0,1,0,1]),
  (712213853370081562421809139496067748, true, [1,1,0,1,1,0,1,0,1,0,1]),
  (713511294068749123059099353895742810, true, [1,0,1,0,0,1,0,1,0,1,0]),
  (716106175156750276452792647004374144, false, [0,2,2,3,3,2,3,4,3,2,1]),
  (771977215577453521385551478926436946, true, [1,0,1,1,0,1,0,1,1,0,1]),
  (773274656276423165975815170617599404, true, [1,1,0,0,1,0,1,0,0,1,0]),
  (777166344548031911844911613880387586, true, [1,0,0,1,0,1,0,1,1,0,1])]

end TFClass

namespace TFClass

def g5 (g : List ℕ) (i : Fin 11) : Fin 5 := ⟨g.getD i.val 0 % 5, Nat.mod_lt _ (by norm_num)⟩

def FinalOK (b : ℕ) (kind : Bool) (w : List ℕ) : Prop :=
  if kind then ∀ i j : Fin 11, adjOf 11 b i j = true → (w.getD i.val 0 == 0) ≠ (w.getD j.val 0 == 0)
  else ∀ i j : Fin 11, adjOf 11 b i j = true ↔ (g5 w j + 1 = g5 w i ∨ g5 w i + 1 = g5 w j)

instance (b : ℕ) (kind : Bool) (w : List ℕ) : Decidable (FinalOK b kind w) := by
  unfold FinalOK; split <;> infer_instance

set_option maxRecDepth 100000 in
theorem final_ok : ∀ e ∈ F11, FinalOK e.1 e.2.1 e.2.2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem L11_eq : L11 = F11.map Prod.fst := by decide +kernel

theorem c5_of_dense (A : Gr 11) (hA : Good A) (hE : 52 ≤ ecount A)
    (hnb : ∀ c : Fin 11 → Bool, ∃ i j, A i j = true ∧ c i = c j) :
    ∃ g : Fin 11 → Fin 5, ∀ i j, A i j = true ↔ (g j + 1 = g i ∨ g i + 1 = g j) := by
  obtain ⟨b, hb, σ, hσ⟩ := cl11 A hA hE
  rw [L11_eq, List.mem_map] at hb
  obtain ⟨e, he, rfl⟩ := hb
  have hok := final_ok e he
  have back : ∀ x y, A x y = adjOf 11 e.1 (σ.symm x) (σ.symm y) := by
    intro x y; rw [← hσ]; simp
  unfold FinalOK at hok
  split at hok
  · exfalso
    obtain ⟨i, j, hij, hc⟩ := hnb (fun x => e.2.2.getD (σ.symm x).val 0 == 0)
    rw [back] at hij
    exact hok _ _ hij hc
  · refine ⟨fun x => g5 e.2.2 (σ.symm x), ?_⟩
    intro i j
    rw [back]
    exact hok _ _

end TFClass

namespace TFGlue

open Finset SimpleGraph TFClass
open scoped Classical

/-- Ordered count of the same-side edges of a cut. -/
lemma two_mono (G : SimpleGraph (Fin 25)) (S : Finset (Fin 25)) :
    2 * (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card =
      ∑ u, ∑ w, if G.Adj u w ∧ (u ∈ S ↔ w ∈ S) then 1 else 0 := by
  let M : SimpleGraph (Fin 25) := {
    Adj := fun u w => G.Adj u w ∧ (u ∈ S ↔ w ∈ S)
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
    loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩ }
  have hM : M.edgeFinset = G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S)) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ a b =>
      simp only [mem_edgeFinset, mem_edgeSet, Finset.mem_filter]
      rw [OMA.R_Erdos23_erdos_23_variants_n5_R1.same_mk]
  rw [← hM, ← M.sum_degrees_eq_twice_card_edges]
  apply Finset.sum_congr rfl
  intro u _
  rw [← M.card_neighborFinset_eq_degree, M.neighborFinset_eq_filter, Finset.card_filter]

lemma sum_restrict (R : Finset (Fin 25)) (P : Fin 25 → Fin 25 → Prop) [DecidableRel P] :
    (∑ u, ∑ w, if u ∈ R ∧ w ∈ R ∧ P u w then 1 else 0) =
      ∑ u ∈ R, ∑ w ∈ R, if P u w then 1 else 0 := by
  rw [← Finset.sum_subset (Finset.subset_univ R)]
  · apply Finset.sum_congr rfl; intro u hu
    rw [← Finset.sum_subset (Finset.subset_univ R)]
    · apply Finset.sum_congr rfl; intro w hw; simp [hu, hw]
    · intro w _ hw; simp [hw]
  · intro u _ hu; simp [hu]

lemma five_indep : ∀ T : Finset (Fin 5), (∀ a ∈ T, ∀ b ∈ T, ¬(a + 1 = b)) →
    ∃ j : Fin 5, ∀ a ∈ T, j + 1 = a ∨ a + 1 = j := by decide

theorem dense_core_hom (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3) (v : Fin 25)
    (deg13 : G.degree v = 13)
    (cut : 25 < (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e,
        (x ∈ G.neighborFinset v ↔ y ∈ G.neighborFinset v))).card)
    (nb : ¬ (G.induce (↑((insert v (G.neighborFinset v))ᶜ) : Set (Fin 25))).IsBipartite) :
    ∃ g : Fin 25 → Fin 5, ∀ u w, u ≠ v → w ≠ v → G.Adj u w → g u + 1 = g w ∨ g w + 1 = g u := by
  set N := G.neighborFinset v with hNdef
  set R := (insert v N)ᶜ with hRdef
  have hR : R.card = 11 := by
    rw [hRdef, Finset.card_compl, Fintype.card_fin, Finset.card_insert_of_notMem (by simp [N]),
      card_neighborFinset_eq_degree, deg13]
  have memN : ∀ x, x ∈ N ↔ G.Adj v x := fun x => by simp [N]
  have memR : ∀ x, x ∈ R ↔ x ≠ v ∧ ¬ G.Adj v x := fun x => by simp [R, memN]
  have noTri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c → False := fun a b c h1 h2 h3 =>
    tri {a, b, c} (is3Clique_triple_iff.mpr ⟨h1, h3, h2⟩)
  let e : Fin 11 ≃ {x // x ∈ R} := (R.equivFin.trans (finCongr hR)).symm
  let A : Gr 11 := fun i j => decide (G.Adj (e i) (e j))
  have hA : Good A := {
    symm := fun i j => by simp [A, G.adj_comm]
    irrefl := fun i => by simp [A]
    tf := fun i j l h1 h2 h3 => noTri _ _ _ (of_decide_eq_true h1) (of_decide_eq_true h2)
      (of_decide_eq_true h3) }
  -- ordered count of the core equals the ordered same-side count of the neighbourhood cut
  have hE : 52 ≤ ecount A := by
    have h2 := two_mono G N
    have key : (∑ u, ∑ w, if G.Adj u w ∧ (u ∈ N ↔ w ∈ N) then 1 else 0) =
        ∑ u, ∑ w, if u ∈ R ∧ w ∈ R ∧ G.Adj u w then 1 else 0 := by
      apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro w _
      congr 1
      apply propext
      rw [memN, memN, memR, memR]
      constructor
      · rintro ⟨huw, hiff⟩
        by_cases hu : G.Adj v u
        · exact absurd (noTri v u w hu huw (hiff.mp hu)) id
        · have hw : ¬ G.Adj v w := fun hw => hu (hiff.mpr hw)
          refine ⟨⟨?_, hu⟩, ⟨?_, hw⟩, huw⟩
          · rintro rfl; exact hw huw
          · rintro rfl; exact hu huw.symm
      · rintro ⟨⟨_, hu⟩, ⟨_, hw⟩, huw⟩
        exact ⟨huw, iff_of_false hu hw⟩
    have reindex : (∑ u, ∑ w, if u ∈ R ∧ w ∈ R ∧ G.Adj u w then 1 else 0) = ecount A := by
      rw [sum_restrict R (fun u w => G.Adj u w)]
      rw [← Finset.sum_coe_sort R, ← Equiv.sum_comp e]
      unfold ecount
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_coe_sort R, ← Equiv.sum_comp e]
      apply Finset.sum_congr rfl; intro j _
      simp [A]
    omega
  have hnb : ∀ c : Fin 11 → Bool, ∃ i j, A i j = true ∧ c i = c j := by
    intro c
    by_contra hno
    simp only [not_exists, not_and] at hno
    apply nb
    refine ⟨SimpleGraph.Coloring.mk
      (fun x => (Fintype.equivFin Bool) (c (e.symm ⟨x.1, x.2⟩))) ?_⟩
    intro x y hxy heq
    have := hno (e.symm ⟨x.1, x.2⟩) (e.symm ⟨y.1, y.2⟩) (by simpa [A] using hxy)
    exact this ((Fintype.equivFin Bool).injective heq)
  obtain ⟨g, hg⟩ := c5_of_dense A hA hE hnb
  let gR : Fin 25 → Fin 5 := fun x => if hx : x ∈ R then g (e.symm ⟨x, hx⟩) else 0
  have hgR : ∀ x y, x ∈ R → y ∈ R → (G.Adj x y ↔ (gR y + 1 = gR x ∨ gR x + 1 = gR y)) := by
    intro x y hx hy
    have := hg (e.symm ⟨x, hx⟩) (e.symm ⟨y, hy⟩)
    simp only [A, Equiv.apply_symm_apply, decide_eq_true_eq] at this
    simpa [gR, hx, hy] using this
  have pick : ∀ u ∈ N, ∃ j : Fin 5, ∀ x ∈ R, G.Adj u x → j + 1 = gR x ∨ gR x + 1 = j := by
    intro u hu
    obtain ⟨j, hj⟩ := five_indep ((R.filter (G.Adj u)).image gR) (by
      intro a ha b hb hab
      simp only [Finset.mem_image, Finset.mem_filter] at ha hb
      obtain ⟨x, ⟨hx, hux⟩, rfl⟩ := ha
      obtain ⟨y, ⟨hy, huy⟩, rfl⟩ := hb
      have hxy : G.Adj y x := (hgR y x hy hx).mpr (Or.inl hab)
      exact noTri u y x huy hxy hux)
    exact ⟨j, fun x hx hux => hj _ (Finset.mem_image.mpr ⟨x, by simp [hx, hux], rfl⟩)⟩
  let g' : Fin 25 → Fin 5 := fun u => if h : u ∈ N then Classical.choose (pick u h) else gR u
  refine ⟨g', ?_⟩
  intro u w hu hw huw
  have split : ∀ x, x ≠ v → x ∈ N ∨ (x ∉ N ∧ x ∈ R) := by
    intro x hx
    by_cases h : x ∈ N
    · exact Or.inl h
    · exact Or.inr ⟨h, (memR x).mpr ⟨hx, fun hv => h ((memN x).mpr hv)⟩⟩
  rcases split u hu with huN | ⟨huN, huR⟩ <;> rcases split w hw with hwN | ⟨hwN, hwR⟩
  · exact absurd (noTri v u w ((memN u).mp huN) huw ((memN w).mp hwN)) id
  · have := Classical.choose_spec (pick u huN) w hwR huw
    simp only [g', huN, hwN, dite_true, dite_false]
    exact this
  · have := Classical.choose_spec (pick w hwN) u huR huw.symm
    simp only [g', huN, hwN, dite_true, dite_false]
    exact this.symm
  · simp only [g', huN, hwN, dite_false]
    exact ((hgR u w huR hwR).mp huw).symm

end TFGlue

open Finset SimpleGraph in
theorem OMA.solution : OMA.R_Erdos23_erdos_23_variants_n5_R1_H2_R1.H3 := by
  intro G inst tri v hv cut nb
  obtain ⟨g, hg⟩ := TFGlue.dense_core_hom G tri v (by convert hv) (by convert cut) (by convert nb)
  obtain ⟨f, hf⟩ := R3Copy.exceptional FiveCycleBound.r3h1 G tri v g hg
  refine ⟨univ.filter (fun u => f u = true), ?_⟩
  have h2 := TFGlue.two_mono G (univ.filter (fun u => f u = true))
  have hle := h2.trans_le (by
    refine le_trans (le_of_eq ?_) hf
    apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro w _
    congr 1; apply propext
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases f u <;> cases f w <;> simp)
  have h25 := Nat.le_of_mul_le_mul_left (hle.trans (by norm_num : 50 ≤ 2 * 25)) (by norm_num)
  convert h25 using 3
  ext e
  simp only [SimpleGraph.mem_edgeFinset]
