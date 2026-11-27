import OMAStatements.S_oeis_a275815
import Mathlib

/-!
# Maximum total number of moves of same-side queens

The perimeter placement achieves the conjectured count (Chai Wah Wu, OEIS
A275815). For the upper bound, count directed line prefixes from the border.
On boards of side at least eight, choose eight prefixes per perimeter square.
Each board square belongs to at most eight selected prefixes. Each prefix is
either hit by a queen or is an empty ray that cannot deliver a move. This gives
the bound by double counting. The uniform local rule has radius seven and is
checked on a finite set of windows. At side seven we use an explicit integral
packing. At side six we split on occupancies and use eight rational packing
certificates. Lean checks every certificate with its kernel.

Source: https://oeis.org/A275815. Credit: @physbuzz.
-/

/-! The perimeter placement realizes the proposed move count. -/
namespace OMA.QueenMoves
open OMA.S_oeis_a275815 Finset

def inner (n : ℕ) : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter (fun i => 0 < i.val ∧ i.val + 1 < n)
def core (n : ℕ) : Finset (Square n) := inner n ×ˢ inner n
def border (n : ℕ) : Finset (Square n) := univ \ core n

lemma card_inner (n : ℕ) : (inner n).card = n-2 := by
  have h : (inner n).image Fin.val = Ico 1 (n-1) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
      have h := (mem_filter.mp ha).2
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    · intro hx
      have h := mem_Ico.mp hx
      have hn : x<n := by omega
      exact mem_image.mpr ⟨⟨x,hn⟩,mem_filter.mpr ⟨mem_univ _,by change 0 < x ∧ x+1<n; omega⟩,rfl⟩
  have := congrArg Finset.card h
  simp [card_image_of_injective (inner n) Fin.val_injective] at this
  omega

lemma card_core (n : ℕ) : (core n).card=(n-2)^2 := by simp [core,card_inner,sq]

private def reach (n x : ℕ) (d : ℤ) : ℕ :=
  if d < 0 then x else if d > 0 then n-1-x else n

private lemma axis_reach {n x : ℕ} (hx : 0<x ∧ x+1<n) {d : ℤ}
    (hd : d = -1 ∨ d = 0 ∨ d = 1) :
    0<reach n x d ∧ (d≠0 → reach n x d<n) ∧
    ∀ k ≤ reach n x d, 0 ≤ (x:ℤ)+k*d ∧ (x:ℤ)+k*d < n ∧
     (k=reach n x d → d≠0 → (x:ℤ)+k*d=0 ∨ (x:ℤ)+k*d+1=n) := by
  rcases hd with rfl|rfl|rfl <;> simp [reach] <;> (repeat' apply And.intro) <;> (repeat' intro) <;> omega

lemma border_ray {n : ℕ} {p : Square n} (hp : p ∈ core n) {v : ℤ × ℤ} (hv : v ∈ rays) :
    canArrive (border n) p v := by
  obtain ⟨hx,hy⟩ := mem_product.mp hp
  have hx' := (mem_filter.mp hx).2
  have hy' := (mem_filter.mp hy).2
  have dirs : (v.1 = -1 ∨ v.1=0 ∨ v.1=1) ∧ (v.2 = -1 ∨ v.2=0 ∨ v.2=1) ∧ (v.1≠0 ∨ v.2≠0) := by
    simp only [rays,mem_insert,mem_singleton] at hv
    rcases hv with h|h|h|h|h|h|h|h <;> subst v <;> decide
  let rx := reach n p.1.val v.1
  let ry := reach n p.2.val v.2
  let k := min rx ry
  have ax := axis_reach hx' dirs.1
  have ay := axis_reach hy' dirs.2.1
  have hk : 0<k := lt_min ax.1 ay.1
  have kn : k<n := by
    rcases dirs.2.2 with h|h
    · exact (min_le_left ..).trans_lt (ax.2.1 h)
    · exact (min_le_right ..).trans_lt (ay.2.1 h)
  have xx := ax.2.2 k (min_le_left ..)
  have yy := ay.2.2 k (min_le_right ..)
  let a := (p.1.val:ℤ)+k*v.1
  let b := (p.2.val:ℤ)+k*v.2
  have ha : (a.toNat:ℤ)=a := Int.toNat_of_nonneg xx.1
  have hb : (b.toNat:ℤ)=b := Int.toNat_of_nonneg yy.1
  let q : Square n := (⟨a.toNat,by dsimp [a] at *; omega⟩,⟨b.toNat,by dsimp [b] at *; omega⟩)
  have hq : q ∉ core n := by
    intro h
    obtain ⟨hq1,hq2⟩ := mem_product.mp h
    have h1 : 0<a.toNat ∧ a.toNat+1<n := (mem_filter.mp hq1).2
    have h2 : 0<b.toNat ∧ b.toNat+1<n := (mem_filter.mp hq2).2
    rcases le_total rx ry with hxy|hyx
    · have kk : k=rx := min_eq_left hxy
      have dx : v.1≠0 := by intro h; simp [rx,reach,h] at kk; omega
      have edge := xx.2.2 kk dx
      change a=0 ∨ a+1=n at edge
      omega
    · have kk : k=ry := min_eq_right hyx
      have dy : v.2≠0 := by intro h; simp [ry,reach,h] at kk; omega
      have edge := yy.2.2 kk dy
      change b=0 ∨ b+1=n at edge
      omega
  exact ⟨fun h => (mem_sdiff.mp h).2 hp,q,mem_sdiff.mpr ⟨mem_univ _,hq⟩,k,mem_Ico.mpr ⟨hk,kn⟩,ha,hb⟩

lemma border_score (n : ℕ) : moves (border n) = 8*(n-2)^2 := by
  classical
  have raycount : rays.card=8 := by decide
  have eq (p : Square n) : (rays.filter (canArrive (border n) p)).card =
      if p ∈ core n then 8 else 0 := by
    split_ifs with h
    · rw [filter_eq_self.mpr (fun v hv => border_ray h hv),raycount]
    · have hp : p ∈ border n := mem_sdiff.mpr ⟨mem_univ _,h⟩
      rw [filter_false_of_mem (fun v _ hc => hc.1 hp)]
      simp
  unfold moves
  simp_rw [eq]
  rw [← sum_filter]
  simp [card_core,Nat.mul_comm]

end OMA.QueenMoves

namespace OMA.QueenMoves
open Finset OMA.S_oeis_a275815

abbrev Ray := ℤ × ℤ

instance {n : ℕ} (s : Finset (Square n)) (p : Square n) (v : Ray) :
    Decidable (canArrive s p v) := by
  unfold canArrive
  infer_instance

def onPrefix {n : ℕ} (q p : Square n) (v : Ray) : Prop :=
  q = p ∨ ∃ k ∈ Ico 1 n,
    (q.1.val : ℤ) = p.1.val + k*v.1 ∧ (q.2.val : ℤ) = p.2.val + k*v.2

instance {n : ℕ} (q p : Square n) (v : Ray) : Decidable (onPrefix q p v) := by
  unfold onPrefix
  infer_instance

def credit {n : ℕ} (w : Square n → Ray → ℕ) (q p : Square n) (v : Ray) :=
  if onPrefix q p v then w p v else 0

def total {n : ℕ} (w : Square n → Ray → ℕ) := ∑ p, ∑ v ∈ rays, w p v

def load {n : ℕ} (w : Square n → Ray → ℕ) (q : Square n) :=
  ∑ p, ∑ v ∈ rays, credit w q p v

/-- A weight on a directed prefix can be charged to any queen it contains. -/
private lemma one_prefix {n D : ℕ} (s : Finset (Square n))
    (w : Square n → Ray → ℕ) (p : Square n) (v : Ray) (hw : w p v ≤ D) :
    (if canArrive s p v then D else 0) + w p v ≤
      (if p ∈ s then 0 else D) + ∑ q ∈ s, credit w q p v := by
  classical
  have hit (q : Square n) (hq : q ∈ s) (hpq : onPrefix q p v) :
      w p v ≤ ∑ t ∈ s, credit w t p v := by
    simpa only [credit,if_pos hpq] using
      (Finset.single_le_sum (f := fun t => credit w t p v) (fun t _ => Nat.zero_le _) hq)
  by_cases hp : p ∈ s
  · have hno : ¬ canArrive s p v := fun h => h.1 hp
    simpa [hno,hp] using hit p hp (Or.inl rfl)
  · by_cases h : canArrive s p v
    · obtain ⟨q,hq,hk⟩ := h.2
      simpa [h,hp] using Nat.add_le_add_left (hit q hq (Or.inr hk)) D
    · simp [hp,h]
      omega

/-- Packing inequality, also valid for weights with nonuniform loads. -/
theorem packing {n D : ℕ} (s : Finset (Square n)) (w : Square n → Ray → ℕ)
    (hw : ∀ p v, v ∈ rays → w p v ≤ D) :
    moves s * D + total w ≤ (n^2-s.card)*(8*D) + ∑ q ∈ s, load w q := by
  classical
  have perCell (p : Square n) :
      (rays.filter (canArrive s p)).card * D + (∑ v ∈ rays, w p v) ≤
      (if p ∈ s then 0 else 8*D) + ∑ q ∈ s, ∑ v ∈ rays, credit w q p v := by
    have h := sum_le_sum (s := rays) (fun v hv => one_prefix s w p v (hw p v hv))
    simp only [sum_add_distrib] at h
    rw [sum_comm (s := rays) (t := s)] at h
    rw [← sum_filter] at h
    have rr : rays.card = 8 := by decide
    simpa [rr,apply_ite,Finset.sum_const,nsmul_eq_mul] using h
  have h := sum_le_sum (s := (univ : Finset (Square n))) (fun p _ => perCell p)
  simp only [sum_add_distrib] at h
  rw [sum_comm (s := univ) (t := s)] at h
  have space : (∑ p : Square n, if p ∈ s then 0 else 8*D) = (n^2-s.card)*(8*D) := by
    have rewriteIte (p : Square n) :
        (if p ∈ s then 0 else 8*D) = (if p ∈ sᶜ then 8*D else 0) := by
      by_cases hp : p ∈ s <;> simp [hp]
    simp_rw [rewriteIte]
    rw [← sum_filter]
    have hc : (univ.filter (fun p : Square n => p ∈ sᶜ)) = sᶜ := by ext; simp
    rw [hc,sum_const,Finset.card_compl]
    simp [sq]
  have me : moves s = ∑ p : Square n, (rays.filter (canArrive s p)).card := by
    unfold moves
    apply sum_congr rfl
    intro p _
    apply congrArg Finset.card
    exact filter_congr_decidable _ _ _
  rw [me,sum_mul]
  simpa only [total,load,space] using h

/-- Bounds on the occupied cells let individual prefix weights exceed a cell's uniform budget. -/
theorem branchPacking {n D : ℕ} (s forced allowed : Finset (Square n))
    (w : Square n → Ray → ℕ) (hw : ∀ p v, v ∈ rays → w p v ≤ D)
    (hf : forced ⊆ s) (ha : s ⊆ allowed) :
    moves s * D + total w + (∑ q ∈ forced, (8*D-load w q)) ≤
      n^2*(8*D) + ∑ q ∈ allowed, (load w q-8*D) := by
  have base := packing s w hw
  have hf' := sum_le_sum_of_subset_of_nonneg (f := fun q => 8*D-load w q) hf (fun _ _ _ => Nat.zero_le _)
  have ha' := sum_le_sum_of_subset_of_nonneg (f := fun q => load w q-8*D) ha (fun _ _ _ => Nat.zero_le _)
  have eq : (∑ q ∈ s, load w q) + (∑ q ∈ s, (8*D-load w q)) =
      s.card*(8*D) + (∑ q ∈ s, (load w q-8*D)) := by
    calc
      _ = ∑ q ∈ s, (load w q + (8*D-load w q)) := sum_add_distrib.symm
      _ = ∑ q ∈ s, (8*D + (load w q-8*D)) := sum_congr rfl (fun _ _ => by omega)
      _ = _ := by simp [sum_add_distrib]
  have sc : s.card ≤ n^2 := by simpa [sq] using card_le_card (subset_univ s)
  have eq' := congrArg (fun a => a*(8*D)) (Nat.sub_add_cancel sc)
  simp only [Nat.add_mul] at eq'
  omega

end OMA.QueenMoves

namespace OMA.QueenMoves.Six
open Finset OMA.S_oeis_a275815

private def lookup {n : ℕ} (weights : Array ℕ) (p : Square n) (v : Ray) :=
  weights[(p.1.val*n+p.2.val)*9+(v.1+1).toNat*3+(v.2+1).toNat]?.getD 0

private def w1 := @lookup 6 #[6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 0, 6, 6, 0, 0, 6, 0, 1, 0, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 5, 0, 0, 4, 0, 3, 6, 6, 6, 0, 0, 0, 0, 0, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 0, 6, 6, 0, 0, 6, 0, 3, 6, 6, 6, 2, 0, 0, 6, 0, 5, 0, 6, 6, 6, 0, 6, 6, 2, 0, 6, 6, 0, 0, 0, 6, 6, 3, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 5, 4, 6, 0, 6, 6, 0, 3, 4, 6, 6, 6, 0, 0, 1, 0, 6, 6, 6, 6, 0, 3, 6, 0, 0, 6, 6, 6, 0, 0, 0, 6, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 2, 1, 5, 0, 0, 6, 0, 0, 6, 6, 6, 4, 0, 0, 5, 0, 0, 6, 6, 6, 1, 0, 6, 0, 0, 0, 6, 6, 6, 0, 3, 6, 0, 0, 0, 6, 6, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6]
private def f1 : Finset (Square 6) := {(0,1), (1,5), (4,5)}
private def a1 : Finset (Square 6) := univ \ ∅

set_option maxRecDepth 20000 in
private theorem cert1 : (∀ p v, v ∈ rays → w1 p v ≤ 6) ∧
    6^2*(8*6) + (∑ q ∈ a1, (load w1 q-8*6)) <
    129*6 + total w1 + (∑ q ∈ f1, (8*6-load w1 q)) := by decide +kernel

private lemma leaf1 (s : Finset (Square 6)) (hf : f1 ⊆ s) (ha : s ⊆ a1) : moves s ≤ 128 := by
  have h := branchPacking (D := 6) s f1 a1 w1 cert1.1 hf ha
  have stop := cert1.2
  omega

private def w2 := @lookup 6 #[6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 0, 6, 6, 0, 0, 6, 0, 0, 0, 6, 6, 6, 0, 0, 5, 0, 6, 6, 6, 6, 6, 0, 0, 1, 0, 6, 6, 6, 6, 0, 0, 0, 0, 0, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 0, 6, 6, 0, 0, 6, 2, 0, 6, 1, 6, 6, 0, 6, 6, 0, 0, 0, 0, 6, 5, 0, 6, 2, 0, 6, 5, 6, 0, 0, 0, 6, 1, 0, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 0, 0, 4, 0, 0, 6, 6, 6, 6, 6, 6, 6, 0, 0, 6, 6, 6, 6, 6, 0, 4, 0, 6, 6, 6, 6, 0, 6, 6, 0, 0, 6, 6, 0, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 4, 0, 5, 0, 0, 6, 0, 0, 6, 6, 6, 1, 0, 0, 4, 0, 6, 6, 6, 6, 0, 0, 0, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 3, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 6, 0, 0, 0, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6]
private def f2 : Finset (Square 6) := {(0,1), (1,5)}
private def a2 : Finset (Square 6) := univ \ {(4,5)}

set_option maxRecDepth 20000 in
private theorem cert2 : (∀ p v, v ∈ rays → w2 p v ≤ 6) ∧
    6^2*(8*6) + (∑ q ∈ a2, (load w2 q-8*6)) <
    129*6 + total w2 + (∑ q ∈ f2, (8*6-load w2 q)) := by decide +kernel

private lemma leaf2 (s : Finset (Square 6)) (hf : f2 ⊆ s) (ha : s ⊆ a2) : moves s ≤ 128 := by
  have h := branchPacking (D := 6) s f2 a2 w2 cert2.1 hf ha
  have stop := cert2.2
  omega

private def w3 := @lookup 6 #[2, 2, 2, 2, 0, 0, 2, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 2, 0, 0, 2, 0, 0, 2, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 2, 2, 0, 2, 2, 0, 0, 0, 2, 2, 2, 0, 1, 2, 0, 0, 2, 2, 2, 0, 0, 2, 0, 0, 0, 2, 2, 2, 0, 0, 2, 0, 0, 0, 2, 2, 2, 0, 0, 2, 0, 0, 2, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 2, 2, 0, 0, 2, 0, 0, 2, 2, 1, 0, 0, 2, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 1, 1, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 2, 2, 2, 1, 0, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 0, 2, 0, 2, 2, 0, 0, 2, 0, 0, 2, 2, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 2, 0, 0, 2, 0, 0, 2, 0, 2, 2, 0, 0, 2, 0, 0, 2, 2, 2, 2, 0, 2, 0, 0, 2, 2, 2, 2, 2, 0, 2, 0, 0, 2, 2, 2, 0, 0, 0, 2, 0, 0, 2, 2, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 2, 0, 0, 2, 0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 2, 0, 0, 2, 2, 2, 2]
private def f3 : Finset (Square 6) := {(0,1), (5,4)}
private def a3 : Finset (Square 6) := univ \ {(1,5)}

set_option maxRecDepth 20000 in
private theorem cert3 : (∀ p v, v ∈ rays → w3 p v ≤ 2) ∧
    6^2*(8*2) + (∑ q ∈ a3, (load w3 q-8*2)) <
    129*2 + total w3 + (∑ q ∈ f3, (8*2-load w3 q)) := by decide +kernel

private lemma leaf3 (s : Finset (Square 6)) (hf : f3 ⊆ s) (ha : s ⊆ a3) : moves s ≤ 128 := by
  have h := branchPacking (D := 2) s f3 a3 w3 cert3.1 hf ha
  have stop := cert3.2
  omega

private def w4 := @lookup 6 #[6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 0, 6, 6, 0, 0, 6, 0, 0, 0, 6, 6, 6, 0, 6, 3, 0, 0, 6, 6, 6, 4, 0, 6, 0, 0, 2, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 0, 1, 6, 0, 0, 6, 0, 0, 6, 0, 6, 6, 0, 0, 6, 0, 6, 6, 6, 6, 1, 0, 6, 6, 0, 0, 0, 6, 6, 6, 0, 6, 5, 6, 4, 0, 0, 6, 0, 0, 6, 0, 4, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 0, 1, 6, 0, 0, 6, 0, 0, 6, 6, 4, 6, 5, 0, 6, 0, 4, 0, 5, 6, 6, 0, 6, 3, 0, 6, 4, 2, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 3, 0, 6, 0, 0, 6, 0, 0, 6, 6, 6, 5, 0, 6, 6, 0, 0, 6, 6, 6, 2, 0, 0, 0, 0, 2, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 0, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 3, 0, 0, 4, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6]
private def f4 : Finset (Square 6) := {(0,1)}
private def a4 : Finset (Square 6) := univ \ {(1,5), (5,4)}

set_option maxRecDepth 20000 in
private theorem cert4 : (∀ p v, v ∈ rays → w4 p v ≤ 6) ∧
    6^2*(8*6) + (∑ q ∈ a4, (load w4 q-8*6)) <
    129*6 + total w4 + (∑ q ∈ f4, (8*6-load w4 q)) := by decide +kernel

private lemma leaf4 (s : Finset (Square 6)) (hf : f4 ⊆ s) (ha : s ⊆ a4) : moves s ≤ 128 := by
  have h := branchPacking (D := 6) s f4 a4 w4 cert4.1 hf ha
  have stop := cert4.2
  omega

private def w5 := @lookup 6 #[2, 2, 2, 2, 0, 0, 2, 0, 0, 2, 2, 2, 2, 0, 0, 2, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 2, 0, 0, 2, 2, 0, 2, 2, 0, 0, 2, 0, 0, 2, 2, 0, 2, 0, 0, 2, 0, 0, 2, 2, 2, 1, 0, 0, 1, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 2, 0, 2, 0, 0, 2, 0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 2, 2, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 2, 2, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 2, 0, 2, 0, 0, 0, 2, 2, 1, 2, 1, 1, 0, 0, 2, 2, 2, 0, 2, 0, 2, 0, 2, 2, 2, 2, 2, 2, 2, 0, 0, 2, 2, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 1, 1, 0, 0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 2, 0, 0, 2, 2, 2, 2, 0, 0, 2, 0, 0, 2, 2, 2, 2, 0, 0, 2, 0, 0, 2, 2, 0, 2, 2, 0, 0, 2, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 2, 0, 0, 0, 2, 2, 2, 0, 0, 2, 0, 0, 2, 2, 2, 2]
private def f5 : Finset (Square 6) := {(4,0), (1,5)}
private def a5 : Finset (Square 6) := univ \ {(0,1)}

set_option maxRecDepth 20000 in
private theorem cert5 : (∀ p v, v ∈ rays → w5 p v ≤ 2) ∧
    6^2*(8*2) + (∑ q ∈ a5, (load w5 q-8*2)) <
    129*2 + total w5 + (∑ q ∈ f5, (8*2-load w5 q)) := by decide +kernel

private lemma leaf5 (s : Finset (Square 6)) (hf : f5 ⊆ s) (ha : s ⊆ a5) : moves s ≤ 128 := by
  have h := branchPacking (D := 2) s f5 a5 w5 cert5.1 hf ha
  have stop := cert5.2
  omega

private def w6 := @lookup 6 #[6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 0, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 0, 0, 4, 0, 0, 0, 6, 6, 4, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 6, 2, 6, 0, 0, 6, 4, 0, 6, 6, 6, 6, 0, 6, 0, 1, 0, 6, 6, 6, 0, 0, 2, 6, 3, 4, 0, 2, 6, 0, 0, 6, 2, 0, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 6, 0, 6, 0, 0, 0, 6, 3, 6, 6, 0, 6, 0, 0, 6, 6, 6, 0, 4, 6, 5, 0, 5, 6, 6, 5, 6, 0, 6, 0, 0, 6, 5, 6, 6, 0, 0, 6, 0, 0, 6, 1, 0, 6, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 0, 0, 0, 0, 0, 6, 6, 6, 6, 0, 6, 0, 0, 0, 6, 6, 6, 0, 0, 4, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 3, 4, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 1, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 3, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6]
private def f6 : Finset (Square 6) := {(4,0)}
private def a6 : Finset (Square 6) := univ \ {(0,1), (1,5)}

set_option maxRecDepth 20000 in
private theorem cert6 : (∀ p v, v ∈ rays → w6 p v ≤ 6) ∧
    6^2*(8*6) + (∑ q ∈ a6, (load w6 q-8*6)) <
    129*6 + total w6 + (∑ q ∈ f6, (8*6-load w6 q)) := by decide +kernel

private lemma leaf6 (s : Finset (Square 6)) (hf : f6 ⊆ s) (ha : s ⊆ a6) : moves s ≤ 128 := by
  have h := branchPacking (D := 6) s f6 a6 w6 cert6.1 hf ha
  have stop := cert6.2
  omega

private def w7 := @lookup 6 #[6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 2, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 1, 6, 6, 6, 0, 0, 4, 0, 0, 3, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 0, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 2, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 6, 6, 0, 5, 6, 6, 6, 0, 0, 6, 0, 0, 6, 0, 3, 6, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 0, 0, 4, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 4, 6, 0, 3, 6, 0, 6, 6, 5, 5, 4, 0, 6, 0, 5, 6, 4, 6, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 4, 0, 6, 0, 0, 6, 0, 0, 6, 2, 0, 6, 0, 6, 6, 6, 0, 0, 0, 6, 6, 0, 1, 6, 6, 6, 6, 0, 6, 0, 0, 6, 6, 0, 6, 0, 0, 6, 0, 0, 6, 1, 0, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 2, 0, 0, 6, 0, 4, 6, 6, 6, 0, 0, 3, 5, 0, 6, 6, 6, 0, 0, 0, 6, 1, 0, 6, 6, 0, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6]
private def f7 : Finset (Square 6) := {(5,4)}
private def a7 : Finset (Square 6) := univ \ {(0,1), (4,0)}

set_option maxRecDepth 20000 in
private theorem cert7 : (∀ p v, v ∈ rays → w7 p v ≤ 6) ∧
    6^2*(8*6) + (∑ q ∈ a7, (load w7 q-8*6)) <
    129*6 + total w7 + (∑ q ∈ f7, (8*6-load w7 q)) := by decide +kernel

private lemma leaf7 (s : Finset (Square 6)) (hf : f7 ⊆ s) (ha : s ⊆ a7) : moves s ≤ 128 := by
  have h := branchPacking (D := 6) s f7 a7 w7 cert7.1 hf ha
  have stop := cert7.2
  omega

private def w8 := @lookup 6 #[6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 3, 0, 0, 0, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 0, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 2, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 6, 6, 0, 5, 6, 6, 6, 0, 0, 6, 0, 0, 6, 5, 1, 6, 0, 0, 6, 0, 0, 6, 6, 0, 1, 6, 0, 0, 6, 0, 0, 6, 6, 5, 6, 0, 0, 6, 0, 6, 6, 6, 6, 6, 0, 4, 6, 3, 0, 6, 2, 6, 0, 0, 6, 0, 6, 5, 0, 4, 6, 0, 0, 6, 0, 5, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 0, 3, 6, 3, 0, 6, 0, 0, 6, 0, 0, 4, 5, 2, 3, 0, 1, 6, 6, 6, 0, 5, 6, 6, 0, 6, 6, 6, 6, 6, 0, 6, 0, 0, 6, 0, 6, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 5, 0, 0, 6, 0, 0, 6, 6, 6, 0, 0, 1, 3, 0, 1, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 0, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6, 0, 0, 6, 0, 0, 6, 6, 6, 6]
private def f8 : Finset (Square 6) := ∅
private def a8 : Finset (Square 6) := univ \ {(0,1), (4,0), (5,4)}

set_option maxRecDepth 20000 in
private theorem cert8 : (∀ p v, v ∈ rays → w8 p v ≤ 6) ∧
    6^2*(8*6) + (∑ q ∈ a8, (load w8 q-8*6)) <
    129*6 + total w8 + (∑ q ∈ f8, (8*6-load w8 q)) := by decide +kernel

private lemma leaf8 (s : Finset (Square 6)) (hf : f8 ⊆ s) (ha : s ⊆ a8) : moves s ≤ 128 := by
  have h := branchPacking (D := 6) s f8 a8 w8 cert8.1 hf ha
  have stop := cert8.2
  omega

theorem upperSix (s : Finset (Square 6)) : moves s ≤ 128 := by
  by_cases h0 : (0,1) ∈ s
  · by_cases h1 : (1,5) ∈ s
    · by_cases h2 : (4,5) ∈ s
      · exact leaf1 s (by simp_all [f1, Finset.insert_subset_iff]) (by simp_all [a1, Finset.subset_sdiff])
      · exact leaf2 s (by simp_all [f2, Finset.insert_subset_iff]) (by simp_all [a2, Finset.subset_sdiff])
    · by_cases h2 : (5,4) ∈ s
      · exact leaf3 s (by simp_all [f3, Finset.insert_subset_iff]) (by simp_all [a3, Finset.subset_sdiff])
      · exact leaf4 s (by simp_all [f4, Finset.insert_subset_iff]) (by simp_all [a4, Finset.subset_sdiff])
  · by_cases h1 : (4,0) ∈ s
    · by_cases h2 : (1,5) ∈ s
      · exact leaf5 s (by simp_all [f5, Finset.insert_subset_iff]) (by simp_all [a5, Finset.subset_sdiff])
      · exact leaf6 s (by simp_all [f6, Finset.insert_subset_iff]) (by simp_all [a6, Finset.subset_sdiff])
    · by_cases h2 : (5,4) ∈ s
      · exact leaf7 s (by simp_all [f7, Finset.insert_subset_iff]) (by simp_all [a7, Finset.subset_sdiff])
      · exact leaf8 s (by simp_all [f8, Finset.insert_subset_iff]) (by simp_all [a8, Finset.subset_sdiff])

end OMA.QueenMoves.Six

namespace OMA.QueenMoves.Seven
open Finset OMA.S_oeis_a275815

private def lookup {n : ℕ} (weights : Array ℕ) (p : Square n) (v : Ray) :=
  weights[(p.1.val*n+p.2.val)*9+(v.1+1).toNat*3+(v.2+1).toNat]?.getD 0

private def w7 := @lookup 7 #[1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1]

set_option maxRecDepth 20000 in
private theorem cert7 : (∀ p v, v ∈ rays → w7 p v ≤ 1) ∧
    (∀ q, load w7 q ≤ 8) ∧ total w7 = 192 := by decide +kernel

theorem upperSeven (s : Finset (Square 7)) : moves s ≤ 200 := by
  have base := packing (D := 1) s w7 cert7.1
  have hl := sum_le_sum (s := s) (g := fun _ => 8) (fun q _ => cert7.2.1 q)
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at hl
  rw [cert7.2.2] at base
  have size : s.card ≤ 49 := by simpa using card_le_card (subset_univ s)
  omega

end OMA.QueenMoves.Seven

namespace OMA.QueenMoves
open Finset OMA.S_oeis_a275815

abbrev Window := Fin 15 → Fin 15 → Bool

def boardWindow (n : ℕ) (x y : ℤ) : Window := fun i j =>
  decide (0 ≤ x+(i.val:ℤ)-7 ∧ x+(i.val:ℤ)-7 < n ∧
    0 ≤ y+(j.val:ℤ)-7 ∧ y+(j.val:ℤ)-7 < n)

def index (z : ℤ) : Fin 15 := ⟨(z+7).toNat % 15, Nat.mod_lt _ (by decide)⟩

def inside (B : Window) (u v : ℤ) := B (index u) (index v)

abbrev Pattern := Fin 7 → Fin 7 → Bool

def near (P : Pattern) (u v : ℤ) :=
  P ⟨(u+3).toNat%7, Nat.mod_lt _ (by decide)⟩ ⟨(v+3).toNat%7, Nat.mod_lt _ (by decide)⟩

def extract (B : Window) (u v : ℤ) : Pattern :=
  fun i j => inside B (u+(i.val:ℤ)-3) (v+(j.val:ℤ)-3)

def maximumLength (P : Pattern) (a b : ℤ) : ℕ := Id.run do
  if !(near P 0 0) || near P (-a) (-b) then return 0
  let horizontal := !(near P (-1) 0 && near P 1 0)
  let vertical := !(near P 0 (-1) && near P 0 1)
  if horizontal && vertical then
    return if a ≠ 0 ∧ b ≠ 0 ∧ near P a b then 4 else 1
  if a=0 ∨ b=0 then return 2
  let i := if horizontal then 0 else a
  let j := if horizontal then b else 0
  if !(near P (2*i) (2*j)) then return 1
  if !(near P (3*i) (3*j)) then return 2
  if !(near P (-2*i) (-2*j)) then return 5
  if !(near P (-3*i) (-3*j)) then return 4
  return 3

def prefixLengths (B : Window) (u v a b : ℤ) :=
  maximumLength (extract B u v) a b

def board (n : ℕ) (x y : ℤ) : Prop := 0 ≤ x ∧ x < n ∧ 0 ≤ y ∧ y < n

theorem inside_board {n : ℕ} (x y : ℤ) {u v : ℤ}
    (hu : -7 ≤ u ∧ u ≤ 7) (hv : -7 ≤ v ∧ v ≤ 7) :
    inside (boardWindow n x y) u v = true ↔ board n (x+u) (y+v) := by
  have idx {z : ℤ} (h : -7 ≤ z ∧ z ≤ 7) : ((index z).val:ℤ) = z+7 := by
    simp only [index, Nat.mod_eq_of_lt (show (z+7).toNat < 15 by omega)]
    omega
  simp only [inside,boardWindow,decide_eq_true_eq,idx hu,idx hv,board]
  omega

theorem translate_window {n : ℕ} (x y : ℤ) {u v : ℤ}
    (hu : -4 ≤ u ∧ u ≤ 4) (hv : -4 ≤ v ∧ v ≤ 4) :
    extract (boardWindow n x y) u v = extract (boardWindow n (x+u) (y+v)) 0 0 := by
  funext i j
  have hi := i.isLt
  have hj := j.isLt
  apply Bool.eq_iff_iff.mpr
  unfold extract
  rw [inside_board _ _ (by omega) (by omega),inside_board _ _ (by omega) (by omega)]
  unfold board
  omega

def localLoad (B : Window) : ℕ :=
  ∑ v ∈ rays, ∑ h ∈ range 5,
    (prefixLengths B (-(h:ℤ)*v.1) (-(h:ℤ)*v.2) v.1 v.2 - h)

def startCount (B : Window) := ∑ v ∈ rays, prefixLengths B 0 0 v.1 v.2

def isBorder (B : Window) := !(inside B 1 0 && inside B (-1) 0 && inside B 0 1 && inside B 0 (-1))

def geometry (B : Window) : Prop :=
  localLoad B ≤ 8 ∧ startCount B = (if isBorder B then 8 else 0) ∧
  ∀ v ∈ rays, prefixLengths B 0 0 v.1 v.2 ≤ 5 ∧
    ∀ j ∈ range (prefixLengths B 0 0 v.1 v.2),
      inside B ((j:ℤ)*v.1) ((j:ℤ)*v.2) = true

instance (B : Window) : Decidable (geometry B) := by unfold geometry; infer_instance

def compress (n x : ℤ) : ℤ := if x < 7 then x else if n-1-x < 7 then 15-(n-1-x) else 7

theorem compress_valid {n x : ℤ} (hn : 16 ≤ n) (hx : 0 ≤ x ∧ x < n) :
    0 ≤ compress n x ∧ compress n x < 16 := by
  unfold compress
  split_ifs <;> omega

theorem compress_window {n : ℕ} {x y : ℤ} (hn : 16 ≤ n)
    (hx : 0 ≤ x ∧ x < n) (hy : 0 ≤ y ∧ y < n) :
    boardWindow n x y = boardWindow 16 (compress n x) (compress n y) := by
  funext i j
  unfold boardWindow
  congr 1
  apply propext
  have h1 := i.isLt
  have h2 := j.isLt
  unfold compress
  split_ifs <;> omega

private theorem row_8_0 : ∀ y : Fin 8, geometry (boardWindow 8 0 y.val) := by decide +kernel

private theorem row_8_1 : ∀ y : Fin 8, geometry (boardWindow 8 1 y.val) := by decide +kernel

private theorem row_8_2 : ∀ y : Fin 8, geometry (boardWindow 8 2 y.val) := by decide +kernel

private theorem row_8_3 : ∀ y : Fin 8, geometry (boardWindow 8 3 y.val) := by decide +kernel

private theorem row_8_4 : ∀ y : Fin 8, geometry (boardWindow 8 4 y.val) := by decide +kernel

private theorem row_8_5 : ∀ y : Fin 8, geometry (boardWindow 8 5 y.val) := by decide +kernel

private theorem row_8_6 : ∀ y : Fin 8, geometry (boardWindow 8 6 y.val) := by decide +kernel

private theorem row_8_7 : ∀ y : Fin 8, geometry (boardWindow 8 7 y.val) := by decide +kernel

private theorem board_8 (x y : Fin 8) : geometry (boardWindow 8 x.val y.val) := by
  fin_cases x
  · exact row_8_0 y
  · exact row_8_1 y
  · exact row_8_2 y
  · exact row_8_3 y
  · exact row_8_4 y
  · exact row_8_5 y
  · exact row_8_6 y
  · exact row_8_7 y

private theorem row_9_0 : ∀ y : Fin 9, geometry (boardWindow 9 0 y.val) := by decide +kernel

private theorem row_9_1 : ∀ y : Fin 9, geometry (boardWindow 9 1 y.val) := by decide +kernel

private theorem row_9_2 : ∀ y : Fin 9, geometry (boardWindow 9 2 y.val) := by decide +kernel

private theorem row_9_3 : ∀ y : Fin 9, geometry (boardWindow 9 3 y.val) := by decide +kernel

private theorem row_9_4 : ∀ y : Fin 9, geometry (boardWindow 9 4 y.val) := by decide +kernel

private theorem row_9_5 : ∀ y : Fin 9, geometry (boardWindow 9 5 y.val) := by decide +kernel

private theorem row_9_6 : ∀ y : Fin 9, geometry (boardWindow 9 6 y.val) := by decide +kernel

private theorem row_9_7 : ∀ y : Fin 9, geometry (boardWindow 9 7 y.val) := by decide +kernel

private theorem row_9_8 : ∀ y : Fin 9, geometry (boardWindow 9 8 y.val) := by decide +kernel

private theorem board_9 (x y : Fin 9) : geometry (boardWindow 9 x.val y.val) := by
  fin_cases x
  · exact row_9_0 y
  · exact row_9_1 y
  · exact row_9_2 y
  · exact row_9_3 y
  · exact row_9_4 y
  · exact row_9_5 y
  · exact row_9_6 y
  · exact row_9_7 y
  · exact row_9_8 y

private theorem row_10_0 : ∀ y : Fin 10, geometry (boardWindow 10 0 y.val) := by decide +kernel

private theorem row_10_1 : ∀ y : Fin 10, geometry (boardWindow 10 1 y.val) := by decide +kernel

private theorem row_10_2 : ∀ y : Fin 10, geometry (boardWindow 10 2 y.val) := by decide +kernel

private theorem row_10_3 : ∀ y : Fin 10, geometry (boardWindow 10 3 y.val) := by decide +kernel

private theorem row_10_4 : ∀ y : Fin 10, geometry (boardWindow 10 4 y.val) := by decide +kernel

private theorem row_10_5 : ∀ y : Fin 10, geometry (boardWindow 10 5 y.val) := by decide +kernel

private theorem row_10_6 : ∀ y : Fin 10, geometry (boardWindow 10 6 y.val) := by decide +kernel

private theorem row_10_7 : ∀ y : Fin 10, geometry (boardWindow 10 7 y.val) := by decide +kernel

private theorem row_10_8 : ∀ y : Fin 10, geometry (boardWindow 10 8 y.val) := by decide +kernel

private theorem row_10_9 : ∀ y : Fin 10, geometry (boardWindow 10 9 y.val) := by decide +kernel

private theorem board_10 (x y : Fin 10) : geometry (boardWindow 10 x.val y.val) := by
  fin_cases x
  · exact row_10_0 y
  · exact row_10_1 y
  · exact row_10_2 y
  · exact row_10_3 y
  · exact row_10_4 y
  · exact row_10_5 y
  · exact row_10_6 y
  · exact row_10_7 y
  · exact row_10_8 y
  · exact row_10_9 y

private theorem row_11_0 : ∀ y : Fin 11, geometry (boardWindow 11 0 y.val) := by decide +kernel

private theorem row_11_1 : ∀ y : Fin 11, geometry (boardWindow 11 1 y.val) := by decide +kernel

private theorem row_11_2 : ∀ y : Fin 11, geometry (boardWindow 11 2 y.val) := by decide +kernel

private theorem row_11_3 : ∀ y : Fin 11, geometry (boardWindow 11 3 y.val) := by decide +kernel

private theorem row_11_4 : ∀ y : Fin 11, geometry (boardWindow 11 4 y.val) := by decide +kernel

private theorem row_11_5 : ∀ y : Fin 11, geometry (boardWindow 11 5 y.val) := by decide +kernel

private theorem row_11_6 : ∀ y : Fin 11, geometry (boardWindow 11 6 y.val) := by decide +kernel

private theorem row_11_7 : ∀ y : Fin 11, geometry (boardWindow 11 7 y.val) := by decide +kernel

private theorem row_11_8 : ∀ y : Fin 11, geometry (boardWindow 11 8 y.val) := by decide +kernel

private theorem row_11_9 : ∀ y : Fin 11, geometry (boardWindow 11 9 y.val) := by decide +kernel

private theorem row_11_10 : ∀ y : Fin 11, geometry (boardWindow 11 10 y.val) := by decide +kernel

private theorem board_11 (x y : Fin 11) : geometry (boardWindow 11 x.val y.val) := by
  fin_cases x
  · exact row_11_0 y
  · exact row_11_1 y
  · exact row_11_2 y
  · exact row_11_3 y
  · exact row_11_4 y
  · exact row_11_5 y
  · exact row_11_6 y
  · exact row_11_7 y
  · exact row_11_8 y
  · exact row_11_9 y
  · exact row_11_10 y

private theorem row_12_0 : ∀ y : Fin 12, geometry (boardWindow 12 0 y.val) := by decide +kernel

private theorem row_12_1 : ∀ y : Fin 12, geometry (boardWindow 12 1 y.val) := by decide +kernel

private theorem row_12_2 : ∀ y : Fin 12, geometry (boardWindow 12 2 y.val) := by decide +kernel

private theorem row_12_3 : ∀ y : Fin 12, geometry (boardWindow 12 3 y.val) := by decide +kernel

private theorem row_12_4 : ∀ y : Fin 12, geometry (boardWindow 12 4 y.val) := by decide +kernel

private theorem row_12_5 : ∀ y : Fin 12, geometry (boardWindow 12 5 y.val) := by decide +kernel

private theorem row_12_6 : ∀ y : Fin 12, geometry (boardWindow 12 6 y.val) := by decide +kernel

private theorem row_12_7 : ∀ y : Fin 12, geometry (boardWindow 12 7 y.val) := by decide +kernel

private theorem row_12_8 : ∀ y : Fin 12, geometry (boardWindow 12 8 y.val) := by decide +kernel

private theorem row_12_9 : ∀ y : Fin 12, geometry (boardWindow 12 9 y.val) := by decide +kernel

private theorem row_12_10 : ∀ y : Fin 12, geometry (boardWindow 12 10 y.val) := by decide +kernel

private theorem row_12_11 : ∀ y : Fin 12, geometry (boardWindow 12 11 y.val) := by decide +kernel

private theorem board_12 (x y : Fin 12) : geometry (boardWindow 12 x.val y.val) := by
  fin_cases x
  · exact row_12_0 y
  · exact row_12_1 y
  · exact row_12_2 y
  · exact row_12_3 y
  · exact row_12_4 y
  · exact row_12_5 y
  · exact row_12_6 y
  · exact row_12_7 y
  · exact row_12_8 y
  · exact row_12_9 y
  · exact row_12_10 y
  · exact row_12_11 y

private theorem row_13_0 : ∀ y : Fin 13, geometry (boardWindow 13 0 y.val) := by decide +kernel

private theorem row_13_1 : ∀ y : Fin 13, geometry (boardWindow 13 1 y.val) := by decide +kernel

private theorem row_13_2 : ∀ y : Fin 13, geometry (boardWindow 13 2 y.val) := by decide +kernel

private theorem row_13_3 : ∀ y : Fin 13, geometry (boardWindow 13 3 y.val) := by decide +kernel

private theorem row_13_4 : ∀ y : Fin 13, geometry (boardWindow 13 4 y.val) := by decide +kernel

private theorem row_13_5 : ∀ y : Fin 13, geometry (boardWindow 13 5 y.val) := by decide +kernel

private theorem row_13_6 : ∀ y : Fin 13, geometry (boardWindow 13 6 y.val) := by decide +kernel

private theorem row_13_7 : ∀ y : Fin 13, geometry (boardWindow 13 7 y.val) := by decide +kernel

private theorem row_13_8 : ∀ y : Fin 13, geometry (boardWindow 13 8 y.val) := by decide +kernel

private theorem row_13_9 : ∀ y : Fin 13, geometry (boardWindow 13 9 y.val) := by decide +kernel

private theorem row_13_10 : ∀ y : Fin 13, geometry (boardWindow 13 10 y.val) := by decide +kernel

private theorem row_13_11 : ∀ y : Fin 13, geometry (boardWindow 13 11 y.val) := by decide +kernel

private theorem row_13_12 : ∀ y : Fin 13, geometry (boardWindow 13 12 y.val) := by decide +kernel

private theorem board_13 (x y : Fin 13) : geometry (boardWindow 13 x.val y.val) := by
  fin_cases x
  · exact row_13_0 y
  · exact row_13_1 y
  · exact row_13_2 y
  · exact row_13_3 y
  · exact row_13_4 y
  · exact row_13_5 y
  · exact row_13_6 y
  · exact row_13_7 y
  · exact row_13_8 y
  · exact row_13_9 y
  · exact row_13_10 y
  · exact row_13_11 y
  · exact row_13_12 y

private theorem row_14_0 : ∀ y : Fin 14, geometry (boardWindow 14 0 y.val) := by decide +kernel

private theorem row_14_1 : ∀ y : Fin 14, geometry (boardWindow 14 1 y.val) := by decide +kernel

private theorem row_14_2 : ∀ y : Fin 14, geometry (boardWindow 14 2 y.val) := by decide +kernel

private theorem row_14_3 : ∀ y : Fin 14, geometry (boardWindow 14 3 y.val) := by decide +kernel

private theorem row_14_4 : ∀ y : Fin 14, geometry (boardWindow 14 4 y.val) := by decide +kernel

private theorem row_14_5 : ∀ y : Fin 14, geometry (boardWindow 14 5 y.val) := by decide +kernel

private theorem row_14_6 : ∀ y : Fin 14, geometry (boardWindow 14 6 y.val) := by decide +kernel

private theorem row_14_7 : ∀ y : Fin 14, geometry (boardWindow 14 7 y.val) := by decide +kernel

private theorem row_14_8 : ∀ y : Fin 14, geometry (boardWindow 14 8 y.val) := by decide +kernel

private theorem row_14_9 : ∀ y : Fin 14, geometry (boardWindow 14 9 y.val) := by decide +kernel

private theorem row_14_10 : ∀ y : Fin 14, geometry (boardWindow 14 10 y.val) := by decide +kernel

private theorem row_14_11 : ∀ y : Fin 14, geometry (boardWindow 14 11 y.val) := by decide +kernel

private theorem row_14_12 : ∀ y : Fin 14, geometry (boardWindow 14 12 y.val) := by decide +kernel

private theorem row_14_13 : ∀ y : Fin 14, geometry (boardWindow 14 13 y.val) := by decide +kernel

private theorem board_14 (x y : Fin 14) : geometry (boardWindow 14 x.val y.val) := by
  fin_cases x
  · exact row_14_0 y
  · exact row_14_1 y
  · exact row_14_2 y
  · exact row_14_3 y
  · exact row_14_4 y
  · exact row_14_5 y
  · exact row_14_6 y
  · exact row_14_7 y
  · exact row_14_8 y
  · exact row_14_9 y
  · exact row_14_10 y
  · exact row_14_11 y
  · exact row_14_12 y
  · exact row_14_13 y

private theorem row_15_0 : ∀ y : Fin 15, geometry (boardWindow 15 0 y.val) := by decide +kernel

private theorem row_15_1 : ∀ y : Fin 15, geometry (boardWindow 15 1 y.val) := by decide +kernel

private theorem row_15_2 : ∀ y : Fin 15, geometry (boardWindow 15 2 y.val) := by decide +kernel

private theorem row_15_3 : ∀ y : Fin 15, geometry (boardWindow 15 3 y.val) := by decide +kernel

private theorem row_15_4 : ∀ y : Fin 15, geometry (boardWindow 15 4 y.val) := by decide +kernel

private theorem row_15_5 : ∀ y : Fin 15, geometry (boardWindow 15 5 y.val) := by decide +kernel

private theorem row_15_6 : ∀ y : Fin 15, geometry (boardWindow 15 6 y.val) := by decide +kernel

private theorem row_15_7 : ∀ y : Fin 15, geometry (boardWindow 15 7 y.val) := by decide +kernel

private theorem row_15_8 : ∀ y : Fin 15, geometry (boardWindow 15 8 y.val) := by decide +kernel

private theorem row_15_9 : ∀ y : Fin 15, geometry (boardWindow 15 9 y.val) := by decide +kernel

private theorem row_15_10 : ∀ y : Fin 15, geometry (boardWindow 15 10 y.val) := by decide +kernel

private theorem row_15_11 : ∀ y : Fin 15, geometry (boardWindow 15 11 y.val) := by decide +kernel

private theorem row_15_12 : ∀ y : Fin 15, geometry (boardWindow 15 12 y.val) := by decide +kernel

private theorem row_15_13 : ∀ y : Fin 15, geometry (boardWindow 15 13 y.val) := by decide +kernel

private theorem row_15_14 : ∀ y : Fin 15, geometry (boardWindow 15 14 y.val) := by decide +kernel

private theorem board_15 (x y : Fin 15) : geometry (boardWindow 15 x.val y.val) := by
  fin_cases x
  · exact row_15_0 y
  · exact row_15_1 y
  · exact row_15_2 y
  · exact row_15_3 y
  · exact row_15_4 y
  · exact row_15_5 y
  · exact row_15_6 y
  · exact row_15_7 y
  · exact row_15_8 y
  · exact row_15_9 y
  · exact row_15_10 y
  · exact row_15_11 y
  · exact row_15_12 y
  · exact row_15_13 y
  · exact row_15_14 y

private theorem row_16_0 : ∀ y : Fin 16, geometry (boardWindow 16 0 y.val) := by decide +kernel

private theorem row_16_1 : ∀ y : Fin 16, geometry (boardWindow 16 1 y.val) := by decide +kernel

private theorem row_16_2 : ∀ y : Fin 16, geometry (boardWindow 16 2 y.val) := by decide +kernel

private theorem row_16_3 : ∀ y : Fin 16, geometry (boardWindow 16 3 y.val) := by decide +kernel

private theorem row_16_4 : ∀ y : Fin 16, geometry (boardWindow 16 4 y.val) := by decide +kernel

private theorem row_16_5 : ∀ y : Fin 16, geometry (boardWindow 16 5 y.val) := by decide +kernel

private theorem row_16_6 : ∀ y : Fin 16, geometry (boardWindow 16 6 y.val) := by decide +kernel

private theorem row_16_7 : ∀ y : Fin 16, geometry (boardWindow 16 7 y.val) := by decide +kernel

private theorem row_16_8 : ∀ y : Fin 16, geometry (boardWindow 16 8 y.val) := by decide +kernel

private theorem row_16_9 : ∀ y : Fin 16, geometry (boardWindow 16 9 y.val) := by decide +kernel

private theorem row_16_10 : ∀ y : Fin 16, geometry (boardWindow 16 10 y.val) := by decide +kernel

private theorem row_16_11 : ∀ y : Fin 16, geometry (boardWindow 16 11 y.val) := by decide +kernel

private theorem row_16_12 : ∀ y : Fin 16, geometry (boardWindow 16 12 y.val) := by decide +kernel

private theorem row_16_13 : ∀ y : Fin 16, geometry (boardWindow 16 13 y.val) := by decide +kernel

private theorem row_16_14 : ∀ y : Fin 16, geometry (boardWindow 16 14 y.val) := by decide +kernel

private theorem row_16_15 : ∀ y : Fin 16, geometry (boardWindow 16 15 y.val) := by decide +kernel

private theorem board_16 (x y : Fin 16) : geometry (boardWindow 16 x.val y.val) := by
  fin_cases x
  · exact row_16_0 y
  · exact row_16_1 y
  · exact row_16_2 y
  · exact row_16_3 y
  · exact row_16_4 y
  · exact row_16_5 y
  · exact row_16_6 y
  · exact row_16_7 y
  · exact row_16_8 y
  · exact row_16_9 y
  · exact row_16_10 y
  · exact row_16_11 y
  · exact row_16_12 y
  · exact row_16_13 y
  · exact row_16_14 y
  · exact row_16_15 y

private theorem smallWindow : ∀ k : Fin 9, ∀ p : Square (k.val+8),
    geometry (boardWindow (k.val+8) p.1.val p.2.val) := by
  intro k
  fin_cases k
  · exact fun p => board_8 p.1 p.2
  · exact fun p => board_9 p.1 p.2
  · exact fun p => board_10 p.1 p.2
  · exact fun p => board_11 p.1 p.2
  · exact fun p => board_12 p.1 p.2
  · exact fun p => board_13 p.1 p.2
  · exact fun p => board_14 p.1 p.2
  · exact fun p => board_15 p.1 p.2
  · exact fun p => board_16 p.1 p.2

/-- The incidence bound and the eight prefixes per border cell hold for every board size n≥8. -/
theorem templateGeometry {n : ℕ} (hn : 8 ≤ n) (p : Square n) :
    geometry (boardWindow n p.1.val p.2.val) := by
  by_cases h : 16 ≤ n
  · have h1 : 0 ≤ (p.1.val:ℤ) ∧ (p.1.val:ℤ)<n := ⟨by positivity,by exact_mod_cast p.1.isLt⟩
    have h2 : 0 ≤ (p.2.val:ℤ) ∧ (p.2.val:ℤ)<n := ⟨by positivity,by exact_mod_cast p.2.isLt⟩
    rw [compress_window h h1 h2]
    have hx := compress_valid (by exact_mod_cast h) h1
    have hy := compress_valid (by exact_mod_cast h) h2
    let a : Fin 16 := ⟨(compress n p.1.val).toNat,by omega⟩
    let b : Fin 16 := ⟨(compress n p.2.val).toNat,by omega⟩
    have good := smallWindow (8 : Fin 9) (a,b)
    change geometry (boardWindow 16 (a.val:ℤ) (b.val:ℤ)) at good
    simpa only [a,b,Int.toNat_of_nonneg hx.1,Int.toNat_of_nonneg hy.1] using good
  · obtain ⟨k,rfl⟩ : ∃ k : Fin 9, n=k.val+8 := ⟨⟨n-8,by omega⟩,by simp; omega⟩
    exact smallWindow k p

end OMA.QueenMoves

namespace OMA.QueenMoves
open Finset OMA.S_oeis_a275815

abbrev Token (n : ℕ) := Σ _ : Square n, Σ _ : Ray, ℕ

def picture {n : ℕ} (p : Square n) := boardWindow n p.1.val p.2.val

def lengths {n : ℕ} (p : Square n) (v : Ray) := prefixLengths (picture p) 0 0 v.1 v.2

def tokens (n : ℕ) : Finset (Token n) :=
  univ.sigma (fun p => rays.sigma (fun v => range (lengths p v)))

def passes {n : ℕ} (q : Square n) (t : Token n) : Prop := ∃ h ≤ t.2.2,
  (q.1.val:ℤ) = t.1.1.val+(h:ℤ)*t.2.1.1 ∧ (q.2.val:ℤ) = t.1.2.val+(h:ℤ)*t.2.1.2

def endX {n : ℕ} (t : Token n) : ℤ := t.1.1.val+(t.2.2:ℤ)*t.2.1.1
def endY {n : ℕ} (t : Token n) : ℤ := t.1.2.val+(t.2.2:ℤ)*t.2.1.2

lemma ray_small {v : Ray} (hv : v ∈ rays) : (-1 ≤ v.1 ∧ v.1 ≤ 1) ∧ (-1 ≤ v.2 ∧ v.2 ≤ 1) := by
  simp only [rays,mem_insert,mem_singleton] at hv
  rcases hv with h|h|h|h|h|h|h|h <;> subst v <;> decide

lemma opposite {v : Ray} (hv : v ∈ rays) : (-v.1,-v.2) ∈ rays := by
  simp only [rays,mem_insert,mem_singleton] at hv
  rcases hv with h|h|h|h|h|h|h|h <;> subst v <;> decide

lemma shortOffset {z : ℤ} {a : ℤ} (hz : 0 ≤ z ∧ z ≤ 4) (ha : -1 ≤ a ∧ a ≤ 1) :
    -4 ≤ z*a ∧ z*a ≤ 4 := by
  rcases ha with ⟨ha,hb⟩
  interval_cases a <;> simp_all <;> omega

lemma coord {n : ℕ} (p : Square n) : board n p.1.val p.2.val :=
  ⟨by positivity,by exact_mod_cast p.1.isLt,by positivity,by exact_mod_cast p.2.isLt⟩

lemma extract_near {n : ℕ} (p : Square n) {a b : ℤ}
    (ha : -3 ≤ a ∧ a ≤ 3) (hb : -3 ≤ b ∧ b ≤ 3) :
    near (extract (picture p) 0 0) a b = true ↔
      board n ((p.1.val:ℤ)+a) ((p.2.val:ℤ)+b) := by
  have idx {z : ℤ} (h : -3 ≤ z ∧ z ≤ 3) : (((z+3).toNat % 7 : ℕ):ℤ)-3 = z := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  unfold near extract picture
  simp only [zero_add,idx ha,idx hb]
  exact inside_board _ _ (by omega) (by omega)

lemma starts_outside {n : ℕ} {p : Square n} {v : Ray} (hv : v ∈ rays) (hl : 0 < lengths p v) :
    ¬ board n ((p.1.val:ℤ)-v.1) ((p.2.val:ℤ)-v.2) := by
  intro inside'
  have h := ray_small hv
  have hit := (extract_near p (a := -v.1) (b := -v.2) (by omega) (by omega)).mpr (by
    simpa only [sub_eq_add_neg] using inside')
  simp [lengths,prefixLengths,maximumLength,hit] at hl

lemma edge_iff {n : ℕ} (p : Square n) : isBorder (picture p) = true ↔ p ∉ core n := by
  have one (a b : ℤ) (ha : -7 ≤ a ∧ a ≤ 7) (hb : -7 ≤ b ∧ b ≤ 7) :=
    inside_board (n := n) (p.1.val:ℤ) (p.2.val:ℤ) ha hb
  have h1 := p.1.isLt
  have h2 := p.2.isLt
  have eq : isBorder (picture p) = false ↔ p ∈ core n := by
    simp only [isBorder,picture,Bool.not_eq_false',Bool.and_eq_true,
      one 1 0 (by decide) (by decide), one (-1) 0 (by decide) (by decide),
      one 0 1 (by decide) (by decide), one 0 (-1) (by decide) (by decide),
      core,inner,mem_product,mem_filter,mem_univ,true_and,board]
    omega
  cases e : isBorder (picture p) <;> simp_all

lemma card_tokens {n : ℕ} (ok : ∀ p : Square n, geometry (picture p)) :
    (tokens n).card = (n^2-(n-2)^2)*8 := by
  unfold tokens
  simp only [card_sigma,card_range]
  have start (p : Square n) : (∑ v ∈ rays, lengths p v) = if p ∉ core n then 8 else 0 := by
    simpa only [← edge_iff,startCount,lengths] using (ok p).2.1
  simp_rw [start]
  rw [← sum_filter]
  have f : (univ.filter (fun p : Square n => p ∉ core n)) = (core n)ᶜ := by ext; simp
  simp [f,card_compl,card_core,sq]

lemma end_onboard {n : ℕ} (ok : ∀ p : Square n, geometry (picture p))
    {t : Token n} (ht : t ∈ tokens n) : board n (endX t) (endY t) := by
  obtain ⟨_,hv,hj⟩ := (show t.1 ∈ univ ∧ t.2.1 ∈ rays ∧ t.2.2 ∈ range (lengths t.1 t.2.1) by
    simpa only [tokens,mem_sigma] using ht)
  have hi := (ok t.1).2.2 t.2.1 hv
  have h5 : (t.2.2:ℤ) ≤ 4 := by have h := mem_range.mp hj; have bound : lengths t.1 t.2.1 ≤ 5 := hi.1; omega
  have small := ray_small hv
  exact (inside_board _ _ (by have := shortOffset ⟨Int.natCast_nonneg _,h5⟩ small.1; omega)
    (by have := shortOffset ⟨Int.natCast_nonneg _,h5⟩ small.2; omega)).mp (hi.2 _ hj)

def endpoint {n : ℕ} (t : Token n) (h : board n (endX t) (endY t)) : Square n :=
  (⟨(endX t).toNat, by rcases h with ⟨_,a,_,_⟩; omega⟩,
   ⟨(endY t).toNat, by rcases h with ⟨_,_,_,a⟩; omega⟩)

lemma endpoint_coords {n : ℕ} (t : Token n) (h : board n (endX t) (endY t)) :
    (((endpoint t h).1.val:ℤ) = endX t) ∧ (((endpoint t h).2.val:ℤ) = endY t) :=
  ⟨Int.toNat_of_nonneg h.1,Int.toNat_of_nonneg h.2.2.1⟩

lemma segment_axis {n i k : ℕ} {x v : ℤ} (hik : i ≤ k) (hx : 0 ≤ x ∧ x < n)
    (he : 0 ≤ x+(k:ℤ)*v ∧ x+(k:ℤ)*v < n) : 0 ≤ x+(i:ℤ)*v ∧ x+(i:ℤ)*v < n := by
  have ik : (i:ℤ) ≤ k := by exact_mod_cast hik
  by_cases hv : 0 ≤ v
  · have lo := mul_nonneg (Int.natCast_nonneg i) hv
    have hi := mul_le_mul_of_nonneg_right ik hv
    omega
  · have lo := mul_le_mul_of_nonpos_right ik (le_of_not_ge hv)
    have hi := mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg i) (le_of_not_ge hv)
    omega

/-- The ray from an endpoint back through its starting border square leaves the board there. -/
lemma step_le {n : ℕ} (ok : ∀ p : Square n, geometry (picture p))
    {t : Token n} (ht : t ∈ tokens n) {q : Square n} {k : ℕ}
    (hx : (q.1.val:ℤ) = endX t-(k:ℤ)*t.2.1.1) (hy : (q.2.val:ℤ) = endY t-(k:ℤ)*t.2.1.2) :
    k ≤ t.2.2 := by
  by_contra! bad
  obtain ⟨_,hv,hj⟩ := (show t.1 ∈ univ ∧ t.2.1 ∈ rays ∧ t.2.2 < lengths t.1 t.2.1 by
    simpa only [tokens,mem_sigma,mem_range] using ht)
  apply starts_outside hv (Nat.zero_le t.2.2 |>.trans_lt hj)
  have he := end_onboard ok ht
  have coordq := coord q
  have a := segment_axis (i := t.2.2+1) (k := k) (v := -t.2.1.1) bad ⟨he.1,he.2.1⟩ (by
    rw [mul_neg,←sub_eq_add_neg,←hx]; exact ⟨coordq.1,coordq.2.1⟩)
  have b := segment_axis (i := t.2.2+1) (k := k) (v := -t.2.1.2) bad he.2.2 (by
    rw [mul_neg,←sub_eq_add_neg,←hy]; exact coordq.2.2)
  have ax : endX t+((t.2.2+1:ℕ):ℤ)*(-t.2.1.1) = (t.1.1.val:ℤ)-t.2.1.1 := by unfold endX; push_cast; ring
  have by' : endY t+((t.2.2+1:ℕ):ℤ)*(-t.2.1.2) = (t.1.2.val:ℤ)-t.2.1.2 := by unfold endY; push_cast; ring
  rw [ax] at a
  rw [by'] at b
  exact ⟨a.1,a.2,b⟩

end OMA.QueenMoves

namespace OMA.QueenMoves
open Finset OMA.S_oeis_a275815
open scoped Classical

abbrev Charge := Σ _ : Ray, Σ _ : ℕ, ℕ

def localCharges (B : Window) : Finset Charge :=
  rays.sigma fun v => (range 5).sigma fun h =>
    Ico h (prefixLengths B (-(h:ℤ)*v.1) (-(h:ℤ)*v.2) v.1 v.2)

lemma card_charges (B : Window) : (localCharges B).card = localLoad B := by
  simp [localCharges,localLoad,card_sigma]

private lemma same_start {n : ℕ} {p q : Square n} {a b c d : ℤ}
    (h1 : (p.1.val:ℤ)+a=c) (h2 : (q.1.val:ℤ)+a=c)
    (h3 : (p.2.val:ℤ)+b=d) (h4 : (q.2.val:ℤ)+b=d) : p=q :=
  Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

lemma load_bound {n : ℕ} (ok : ∀ p : Square n, geometry (picture p)) (q : Square n) :
    ((tokens n).filter (passes q)).card ≤ 8 := by
  classical
  let U := (tokens n).filter (passes q)
  let height (t : U) := Classical.choose (mem_filter.mp t.2).2
  have spec (t : U) := Classical.choose_spec (mem_filter.mp t.2).2
  let tag (t : U) : Charge := ⟨t.val.2.1,height t,t.val.2.2⟩
  have good (t : U) : tag t ∈ localCharges (picture q) := by
    have ht := (mem_filter.mp t.2).1
    obtain ⟨_,hv,hj⟩ : t.val.1 ∈ univ ∧ t.val.2.1 ∈ rays ∧ t.val.2.2 < lengths t.val.1 t.val.2.1 := by
      simpa only [tokens,mem_sigma,mem_range] using ht
    have bound : lengths t.val.1 t.val.2.1 ≤ 5 := ((ok t.val.1).2.2 t.val.2.1 hv).1
    obtain ⟨hj',hx,hy⟩ := spec t
    change height t ≤ t.val.2.2 at hj'
    change (q.1.val:ℤ) = t.val.1.1.val + (height t:ℤ)*t.val.2.1.1 at hx
    change (q.2.val:ℤ) = t.val.1.2.val + (height t:ℤ)*t.val.2.1.2 at hy
    have subx : (q.1.val:ℤ)+(-(height t:ℤ)*t.val.2.1.1)=t.val.1.1.val := by rw [neg_mul]; omega
    have suby : (q.2.val:ℤ)+(-(height t:ℤ)*t.val.2.1.2)=t.val.1.2.val := by rw [neg_mul]; omega
    have small := ray_small hv
    have sz : 0 ≤ (height t:ℤ) ∧ (height t:ℤ) ≤ 4 := by omega
    have u := shortOffset sz small.1
    have v := shortOffset sz small.2
    have eq := translate_window (n := n) (q.1.val:ℤ) (q.2.val:ℤ)
      (u := -(height t:ℤ)*t.val.2.1.1) (v := -(height t:ℤ)*t.val.2.1.2)
      (by rw [neg_mul]; omega) (by rw [neg_mul]; omega)
    rw [subx,suby] at eq
    simp only [localCharges,tag,mem_sigma,mem_range,mem_Ico]
    exact ⟨hv,by omega,hj',by simpa only [prefixLengths,picture,eq,lengths] using hj⟩
  let f (t : U) : localCharges (picture q) := ⟨tag t,good t⟩
  have inj : Function.Injective f := by
    intro t u he
    have hd := congrArg (fun c : localCharges (picture q) => c.val.1) he
    have hh := congrArg (fun c : localCharges (picture q) => c.val.2.1) he
    have hj := congrArg (fun c : localCharges (picture q) => c.val.2.2) he
    change t.val.2.1 = u.val.2.1 at hd
    change height t = height u at hh
    change t.val.2.2 = u.val.2.2 at hj
    obtain ⟨_,hx,hy⟩ := spec t
    obtain ⟨_,ux,uy⟩ := spec u
    change (q.1.val:ℤ) = t.val.1.1.val + (height t:ℤ)*t.val.2.1.1 at hx
    change (q.2.val:ℤ) = t.val.1.2.val + (height t:ℤ)*t.val.2.1.2 at hy
    rw [hd,hh] at hx hy
    have ps := same_start hx.symm ux.symm hy.symm uy.symm
    apply Subtype.ext
    exact Sigma.ext ps (heq_of_eq (Sigma.ext hd (heq_of_eq hj)))
  exact (card_le_card_of_injective (f := f) inj).trans ((card_charges _).trans_le (ok q).1)

lemma hits_bound {n : ℕ} (ok : ∀ p : Square n, geometry (picture p)) (s : Finset (Square n)) :
    ((tokens n).filter (fun t => ∃ q ∈ s, passes q t)).card ≤ s.card*8 := by
  classical
  let f (q : Square n) := (tokens n).filter (passes q)
  have eq : (tokens n).filter (fun t => ∃ q ∈ s, passes q t) = s.biUnion f := by
    ext t
    simp only [mem_filter,mem_biUnion,f]
    aesop
  rw [eq]
  have b := sum_le_sum (s := s) (g := fun _ => (8:ℕ)) (fun q _ => load_bound ok q)
  exact (card_biUnion_le).trans (by simpa only [sum_const,nsmul_eq_mul,Nat.cast_id] using b)

end OMA.QueenMoves

namespace OMA.QueenMoves
open Finset OMA.S_oeis_a275815
open scoped Classical

abbrev Miss (n : ℕ) := Σ _ : Square n, Ray

noncomputable def missing {n : ℕ} (s : Finset (Square n)) : Finset (Miss n) :=
  sᶜ.sigma (fun p => rays.filter (fun v => ¬canArrive s p v))

lemma missing_card {n : ℕ} (s : Finset (Square n)) :
    moves s + (missing s).card = (n^2-s.card)*8 := by
  classical
  let A (p : Square n) := (rays.filter (canArrive s p)).card
  have eq : moves s = ∑ p ∈ sᶜ, A p := by
    unfold moves
    calc
      _ = ∑ p : Square n, A p := by
        apply sum_congr rfl
        intro p _
        apply congrArg Finset.card
        exact filter_congr_decidable _ _ _
      _ = _ := by
        symm
        apply sum_subset (subset_univ _)
        intro p _ hp
        have ps : p ∈ s := by simpa using hp
        unfold A
        rw [filter_false_of_mem (fun v _ hc => hc.1 ps)]
        simp
  rw [eq,missing,card_sigma,← sum_add_distrib]
  have val (p : Square n) :
      A p + (rays.filter (fun v => ¬canArrive s p v)).card = 8 := by
    dsimp only [A]
    rw [card_filter_add_card_filter_not]
    decide
  simp [val,card_compl,sq]

lemma misses_bound {n : ℕ} (ok : ∀ p : Square n, geometry (picture p)) (s : Finset (Square n)) :
    ((tokens n).filter (fun t => ¬ ∃ q ∈ s, passes q t)).card ≤ (missing s).card := by
  classical
  let U := (tokens n).filter (fun t => ¬ ∃ q ∈ s, passes q t)
  have valid (t : U) : t.val ∈ tokens n := (mem_filter.mp t.2).1
  let dest (t : U) := endpoint t.val (end_onboard ok (valid t))
  have coords (t : U) := endpoint_coords t.val (end_onboard ok (valid t))
  let label (t : U) : Miss n := ⟨dest t,(-t.val.2.1.1,-t.val.2.1.2)⟩
  have good (t : U) : label t ∈ missing s := by
    obtain ⟨nx,ny⟩ := coords t
    change ((dest t).1.val:ℤ) = endX t.val at nx
    change ((dest t).2.val:ℤ) = endY t.val at ny
    have none := (mem_filter.mp t.2).2
    have de : dest t ∉ s := fun h => none ⟨dest t,h,t.val.2.2,le_rfl,nx,ny⟩
    have hv := (mem_sigma.mp (mem_sigma.mp (valid t)).2).1
    refine mem_sigma.mpr ⟨mem_compl.mpr de,mem_filter.mpr ⟨opposite hv,?_⟩⟩
    rintro ⟨_,q,hq,k,_,hx,hy⟩
    change (q.1.val:ℤ)=(dest t).1.val+(k:ℤ)*(-t.val.2.1.1) at hx
    change (q.2.val:ℤ)=(dest t).2.val+(k:ℤ)*(-t.val.2.1.2) at hy
    rw [nx,mul_neg,←sub_eq_add_neg] at hx
    rw [ny,mul_neg,←sub_eq_add_neg] at hy
    have hle := step_le ok (valid t) hx hy
    apply none
    refine ⟨q,hq,t.val.2.2-k,by omega,?_,?_⟩
    · rw [hx,endX,Nat.cast_sub hle]
      ring
    · rw [hy,endY,Nat.cast_sub hle]
      ring
  let f (t : U) : missing s := ⟨label t,good t⟩
  have inj : Function.Injective f := by
    intro t u he
    have ep : dest t = dest u := congrArg (fun c : missing s => c.val.1) he
    have ex : -t.val.2.1.1 = -u.val.2.1.1 := congrArg (fun c : missing s => c.val.2.1) he
    have ey : -t.val.2.1.2 = -u.val.2.1.2 := congrArg (fun c : missing s => c.val.2.2) he
    have hd : t.val.2.1=u.val.2.1 := Prod.ext (by omega) (by omega)
    have cx := congrArg (fun p : Square n => (p.1.val:ℤ)) ep
    have cy := congrArg (fun p : Square n => (p.2.val:ℤ)) ep
    obtain ⟨xt,yt⟩ := coords t
    obtain ⟨xu,yu⟩ := coords u
    have endx : endX t.val = endX u.val := xt.symm.trans (cx.trans xu)
    have endy : endY t.val = endY u.val := yt.symm.trans (cy.trans yu)
    have le (t u : U) (hd : t.val.2.1=u.val.2.1) (ex : endX t.val=endX u.val)
        (ey : endY t.val=endY u.val) : u.val.2.2 ≤ t.val.2.2 := by
      apply step_le ok (valid t) (q := u.val.1)
      · rw [ex,hd,endX]; ring
      · rw [ey,hd,endY]; ring
    have hj := le_antisymm (le u t hd.symm endx.symm endy.symm) (le t u hd endx endy)
    unfold endX at endx
    unfold endY at endy
    rw [hd,hj] at endx endy
    have ps : t.val.1=u.val.1 := Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    apply Subtype.ext
    exact Sigma.ext ps (heq_of_eq (Sigma.ext hd (heq_of_eq hj)))
  exact card_le_card_of_injective (f := f) inj

end OMA.QueenMoves

namespace OMA.QueenMoves
open Finset OMA.S_oeis_a275815

theorem upper_of_geometry {n : ℕ} (ok : ∀ p : Square n, geometry (picture p)) (s : Finset (Square n)) :
    moves s ≤ 8*(n-2)^2 := by
  classical
  have h1 := hits_bound ok s
  have h2 := misses_bound ok s
  have h3 := missing_card s
  have h4 := card_tokens ok
  have h5 := card_filter_add_card_filter_not (s := tokens n) (fun t => ∃ q ∈ s, passes q t)
  have all : s.card ≤ n^2 := by simpa [sq] using card_le_card (subset_univ s)
  have innerle : (n-2)^2 ≤ n^2 := by gcongr; omega
  omega

end OMA.QueenMoves

namespace OMA.QueenMoves
open OMA.S_oeis_a275815

theorem upper {n : ℕ} (hn : 6 ≤ n) (s : Finset (Square n)) :
    moves s ≤ 8*(n-2)^2 := by
  by_cases h8 : 8 ≤ n
  · exact upper_of_geometry (templateGeometry h8) s
  · obtain rfl|rfl : n=6 ∨ n=7 := by omega
    · exact Six.upperSix s
    · exact Seven.upperSeven s

end OMA.QueenMoves

theorem OMA.solution : type_of% @OMA.S_oeis_a275815.main := by
  intro n hn
  constructor
  · exact ⟨OMA.QueenMoves.border n, OMA.QueenMoves.border_score n⟩
  · rintro m ⟨s,rfl⟩
    exact OMA.QueenMoves.upper hn s
