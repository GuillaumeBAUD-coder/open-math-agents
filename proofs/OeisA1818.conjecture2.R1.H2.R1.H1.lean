import OMAReductions.R_OeisA1818_conjecture2_R1_H2_R1
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-! Inserting a distinguished vertex into a cycle splits one reciprocal-difference
factor into a sum. The insertions telescope around the cycle. Summing over
marked vertices cancels the whole cycle class, since its number of eligible
marks is positive and smaller than the prime p. -/

open Finset Equiv

private lemma split_kernel {N : ℕ} {a b z : ZMod N}
    (haz : IsUnit (z-a)) (hbz : IsUnit (b-z)) (hba : IsUnit (b-a)) :
    (b-z)⁻¹*(z-a)⁻¹ = (b-a)⁻¹*((b-z)⁻¹+(z-a)⁻¹) := by
  calc
    _ = ((b-a)⁻¹*(b-a))*((b-z)⁻¹*(z-a)⁻¹) := by rw [ZMod.inv_mul_of_unit _ hba,one_mul]
    _ = (b-a)⁻¹*((b-z)⁻¹*((z-a)*(z-a)⁻¹) + (z-a)⁻¹*((b-z)*(b-z)⁻¹)) := by ring
    _ = _ := by rw [ZMod.mul_inv_of_unit _ haz,ZMod.mul_inv_of_unit _ hbz,mul_one,mul_one]

-- Insertion redirects precisely the edge from the predecessor of x to x.
private lemma insert_weight {n : ℕ} {R : Type*} [CommRing R]
    (C : Fin (n+1) → Fin (n+1) → R)
    (three : ∀ x a : Fin n, x ≠ a → C x.succ 0*C 0 a.succ =
      C x.succ a.succ*(C x.succ 0+C 0 a.succ))
    (e : Perm (Fin n)) (x : Fin n) (moves : e x ≠ x) :
    (∏ i, C (Perm.decomposeFin.symm (x.succ,e) i) i) =
      (∏ i : Fin n, C (e i).succ i.succ) * (C x.succ 0 + C 0 (e.symm x).succ) := by
  classical
  let j := e.symm x
  have ej : e j = x := e.apply_symm_apply x
  have diff : x ≠ j := fun h => moves ((congrArg e h).trans ej)
  let D (i : Fin n) := C (e i).succ i.succ
  let D' (i : Fin n) := C (Perm.decomposeFin.symm (x.succ,e) i.succ) i.succ
  have pivot : D' j = C 0 j.succ := by simp [D',ej]
  have rest : ∏ i ∈ univ.erase j, D' i = ∏ i ∈ univ.erase j, D i := by
    apply prod_congr rfl
    intro i hi
    have ne := (mem_erase.mp hi).1
    have ex : e i ≠ x := fun h => ne (e.injective (h.trans ej.symm))
    simp [D',D,swap_apply_def,ex]
  rw [Fin.prod_univ_succ,Perm.decomposeFin_symm_apply_zero]
  change C x.succ 0*(∏ i, D' i) = (∏ i,D i)*(C x.succ 0+C 0 j.succ)
  rw [←mul_prod_erase univ D' (mem_univ j),←mul_prod_erase univ D (mem_univ j),
    pivot,rest]
  change C x.succ 0*(C 0 j.succ*_) = (C (e j).succ j.succ*_)*_
  rw [ej,←mul_assoc,three x j diff]
  ring

-- Conjugation by the old permutation takes the insertion point x to e x.
private lemma insertion_type {n : ℕ} (e : Perm (Fin n)) (x : Fin n) :
    (Perm.decomposeFin.symm (x.succ,e)).cycleType =
      (Perm.decomposeFin.symm ((e x).succ,e)).cycleType := by
  let g := Perm.decomposeFin.symm (0,e)
  apply Perm.isConj_iff_cycleType_eq.mp
  apply isConj_iff.mpr
  refine ⟨g, (mul_inv_eq_iff_eq_mul).mpr ?_⟩
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [g,Perm.mul_apply]
  · simp only [Perm.mul_apply,Perm.decomposeFin_symm_apply_succ]
    rw [g.injective.map_swap]
    simp [g]

private lemma sum_predecessor {α R : Type*} [Fintype α] [DecidableEq α] [CommRing R]
    (e : Perm α) (S : Finset α) (stable : ∀ x, x ∈ S ↔ e x ∈ S) (f : α → R) :
    ∑ x ∈ S, (f x-f (e.symm x)) = 0 := by
  rw [sum_sub_distrib,sub_eq_zero]
  apply sum_bij (fun x _ => e x)
  · intro x hx; exact (stable x).mp hx
  · intro a _ b _ h; exact e.injective h
  · intro x hx; exact ⟨e.symm x,(stable _).mpr (by simpa using hx),e.apply_symm_apply _⟩
  · intro x _; simp

private lemma pivot_zero {n : ℕ} {R : Type*} [CommRing R] (C : Fin (n+1) → Fin (n+1) → R)
    (skew : ∀ i : Fin n, C 0 i.succ = -C i.succ 0)
    (three : ∀ x a : Fin n, x ≠ a → C x.succ 0*C 0 a.succ =
      C x.succ a.succ*(C x.succ 0+C 0 a.succ)) (c : Multiset ℕ) :
    (∑ σ : Perm (Fin (n+1)), if σ.cycleType = c ∧ σ (σ 0) ≠ 0 then ∏ i, C (σ i) i else 0) = 0 := by
  classical
  let F (σ : Perm (Fin (n+1))) := if σ.cycleType=c ∧ σ (σ 0) ≠ 0 then ∏ i,C (σ i) i else 0
  change ∑ σ, F σ = 0
  rw [←Perm.decomposeFin.symm.sum_comp F,Fintype.sum_prod_type,sum_comm]
  apply sum_eq_zero
  intro e _
  rw [Fin.sum_univ_succ]
  have zero : F (Perm.decomposeFin.symm (0,e)) = 0 := by simp [F]
  rw [zero,zero_add]
  let ins (x : Fin n) := Perm.decomposeFin.symm (x.succ,e)
  let S := univ.filter (fun x => (ins x).cycleType=c ∧ e x ≠ x)
  have mem (x : Fin n) : x ∈ S ↔ (ins x).cycleType=c ∧ e x ≠ x := by simp [S]
  have flag (x : Fin n) : ins x (ins x 0) ≠ 0 ↔ e x ≠ x := by
    by_cases h : e x=x <;> simp [ins,h,swap_apply_def]
  have stable (x : Fin n) : x ∈ S ↔ e x ∈ S := by
    rw [mem,mem,insertion_type e x]
    simp only [ne_eq,Equiv.apply_eq_iff_eq]
    rfl
  let W := ∏ i : Fin n, C (e i).succ i.succ
  calc
    _ = ∑ x ∈ S, ∏ i,C (ins x i) i := by
      dsimp only [S]
      rw [sum_filter]
      apply sum_congr rfl
      intro x _
      change F (ins x) = _
      simp only [F,flag]
    _ = ∑ x ∈ S, W*(C x.succ 0-C (e.symm x).succ 0) := by
      apply sum_congr rfl
      intro x hx
      rw [show ins x = Perm.decomposeFin.symm (x.succ,e) by rfl,insert_weight C three e x ((mem x).1 hx).2,skew]
      simp only [W,sub_eq_add_neg]
    _ = 0 := by
      rw [←mul_sum,sum_predecessor e S stable (fun x => C x.succ 0),mul_zero]

private lemma pivot_at {n : ℕ} {R : Type*} [CommRing R] (C : Fin (n+1) → Fin (n+1) → R)
    (skew : ∀ i j, i ≠ j → C i j = -C j i)
    (three : ∀ i j z, i ≠ j → i ≠ z → z ≠ j →
      C i z*C z j = C i j*(C i z+C z j)) (c : Multiset ℕ) (a : Fin (n+1)) :
    (∑ σ : Perm (Fin (n+1)), if σ.cycleType = c ∧ σ (σ a) ≠ a then ∏ i, C (σ i) i else 0) = 0 := by
  classical
  let g := swap 0 a
  have g0 : g 0 = a := swap_apply_left _ _
  let D (i j : Fin (n+1)) := C (g i) (g j)
  have sk (i : Fin n) : D 0 i.succ = -D i.succ 0 :=
    skew _ _ (g.injective.ne (Fin.succ_ne_zero i).symm)
  have tr (x y : Fin n) (ne : x ≠ y) : D x.succ 0*D 0 y.succ = D x.succ y.succ*(D x.succ 0+D 0 y.succ) :=
    three _ _ _ (g.injective.ne (Fin.succ_injective _ |>.ne ne))
      (g.injective.ne (Fin.succ_ne_zero _)) (g.injective.ne (Fin.succ_ne_zero _).symm)
  let F (σ : Perm (Fin (n+1))) := if σ.cycleType = c ∧ σ (σ a) ≠ a then ∏ i,C (σ i) i else 0
  change ∑ σ, F σ = 0
  rw [←g.permCongr.sum_comp F]
  apply Eq.trans _ (pivot_zero D sk tr c)
  apply sum_congr rfl
  intro σ _
  have conj : g*σ*g⁻¹ = g.permCongr σ := by ext i; rfl
  have ty := Perm.isConj_iff_cycleType_eq.mp (isConj_iff.mpr ⟨g,conj⟩)
  have flag : g.permCongr σ (g.permCongr σ a) ≠ a ↔ σ (σ 0) ≠ 0 := by
    rw [←g0]
    simp
  dsimp only [F]
  simp only [←ty,flag]
  split_ifs
  · rw [←Equiv.prod_comp g (fun i => C (g.permCongr σ i) i)]
    simp [D]
  · rfl

private theorem class_sum {n p : ℕ} (hp : p.Prime) (small : n+1 < p)
    (C : Fin (n+1) → Fin (n+1) → ZMod (p^2))
    (skew : ∀ i j, i ≠ j → C i j = -C j i)
    (three : ∀ i j z, i ≠ j → i ≠ z → z ≠ j →
      C i z*C z j = C i j*(C i z+C z j))
    (c : Multiset ℕ) (long : ∃ k ∈ c, 3 ≤ k) :
    (∑ σ ∈ univ.filter (fun σ : Perm (Fin (n+1)) => σ.cycleType=c), ∏ i,C (σ i) i) = 0 := by
  classical
  let P := univ.filter (fun σ : Perm (Fin (n+1)) => σ.cycleType=c)
  let W (σ : Perm (Fin (n+1))) := ∏ i,C (σ i) i
  change (∑ σ ∈ P, W σ) = 0
  rcases P.eq_empty_or_nonempty with empty|⟨τ,hτ⟩
  · simp [empty]
  have tc : τ.cycleType=c := (mem_filter.mp hτ).2
  let m := (τ^2).support.card
  have pos : 0 < m := by
    by_contra! z
    have empty : (τ^2).support = ∅ := card_eq_zero.mp (Nat.eq_zero_of_le_zero z)
    have id : τ^2 = 1 := by
      apply Equiv.ext
      intro i
      change (τ^2) i = i
      by_contra ne
      have mem : i ∈ (τ^2).support := Perm.mem_support.mpr ne
      simp [empty] at mem
    obtain ⟨k,hk,h3⟩ := long
    have dvd := (Perm.dvd_of_mem_cycleType (tc ▸ hk)).trans (orderOf_dvd_of_pow_eq_one id)
    have le := Nat.le_of_dvd (by decide : 0 < 2) dvd
    omega
  have mp : m < p := (show m ≤ n+1 by simpa [m] using (τ^2).support.card_le_univ).trans_lt small
  have unit : IsUnit (m : ZMod (p^2)) := (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide)).mpr
    (fun h => (Nat.le_of_dvd pos h).not_gt mp)
  have mult (σ : Perm (Fin (n+1))) (hσ : σ ∈ P) : (σ^2).support.card = m := by
    have same : σ.cycleType=τ.cycleType := (mem_filter.mp hσ).2.trans tc.symm
    have conj := Perm.isConj_iff_cycleType_eq.mpr same
    rw [←Perm.sum_cycleType]
    dsimp only [m]
    rw [←Perm.sum_cycleType]
    exact congrArg Multiset.sum (Perm.isConj_iff_cycleType_eq.mp (conj.pow 2))
  have each (a : Fin (n+1)) :
      (∑ σ ∈ P, if σ (σ a) ≠ a then W σ else 0) = 0 := by
    dsimp only [P]
    rw [sum_filter]
    simpa only [W,ite_and] using pivot_at C skew three c a
  have all : (m:ZMod (p^2))*(∑ σ ∈ P,W σ)=0 := calc
    _ = ∑ σ ∈ P, ∑ a : Fin (n+1), if σ (σ a) ≠ a then W σ else 0 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro σ hσ
      rw [←sum_filter]
      have setEq : (univ.filter fun a => σ (σ a) ≠ a) = (σ^2).support := by
        ext i; simp [Perm.mem_support,pow_two,Perm.mul_apply]
      rw [setEq,sum_const,nsmul_eq_mul,mult σ hσ]
    _ = _ := by rw [sum_comm]; exact sum_eq_zero (fun a _ => each a)
  calc
    _ = ((m:ZMod (p^2))⁻¹*(m:ZMod (p^2)))*(∑ σ ∈ P,W σ) := by rw [ZMod.inv_mul_of_unit _ unit,one_mul]
    _ = 0 := by rw [mul_assoc,all,mul_zero]

private lemma differences_unit {p d : ℕ} (hp : p.Prime) (size : d ≤ p)
    (i j : Fin d) (ne : i ≠ j) : IsUnit ((i.val : ZMod (p^2))-j.val) := by
  have dir (x y : Fin d) (h : y.val < x.val) : IsUnit ((x.val : ZMod (p^2))-y.val) := by
    rw [←Nat.cast_sub h.le]
    apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide)).mpr
    intro hd
    have low := Nat.le_of_dvd (Nat.sub_pos_of_lt h) hd
    have high := x.isLt
    omega
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne ne) with h|h
  · have neg := (dir j i h).neg
    simpa only [neg_sub] using neg
  · exact dir i j h

private theorem cycle_cancel (p : ℕ) (hp : p.Prime) (hn : p ≠ 2) :
    let C : Matrix (Fin (p-1)) (Fin (p-1)) (ZMod (p^2)) := fun i j =>
      if i=j then 0 else ((i.val : ZMod (p^2))-j.val)⁻¹
    ∀ c : Multiset ℕ, (∃ k ∈ c, 3 ≤ k) →
      (∑ σ ∈ univ.filter (fun σ : Perm (Fin (p-1)) => σ.cycleType=c), ∏ i,C (σ i) i) = 0 := by
  have pp := hp.two_le
  obtain ⟨n,rfl⟩ : ∃ n, p=n+2 := ⟨p-2,by omega⟩
  let C (i j : Fin (n+1)) : ZMod ((n+2)^2) := if i=j then 0 else ((i.val : ZMod ((n+2)^2))-j.val)⁻¹
  have diff := differences_unit hp (show n+1 ≤ n+2 by omega)
  have sk (i j : Fin (n+1)) (ne : i ≠ j) : C i j = -C j i := by
    dsimp only [C]
    rw [if_neg ne,if_neg ne.symm]
    apply ZMod.inv_eq_of_mul_eq_one
    rw [←neg_sub (j.val : ZMod ((n+2)^2)) i.val,neg_mul_neg,ZMod.mul_inv_of_unit _ (diff _ _ ne.symm)]
  have tr (i j z : Fin (n+1)) (ij : i ≠ j) (iz : i ≠ z) (zj : z ≠ j) :
      C i z*C z j = C i j*(C i z+C z j) := by
    simp only [C,if_neg ij,if_neg iz,if_neg zj]
    exact split_kernel (diff _ _ zj) (diff _ _ iz) (diff _ _ ij)
  exact fun c h => class_sum hp (show n+1 < n+2 by omega) C sk tr c h

theorem OMA.solution : OMA.R_OeisA1818_conjecture2_R1_H2_R1.H1 := by
  exact cycle_cancel
