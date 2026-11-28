import FormalConjectures.Mathoverflow.«31809»
import Mathlib
namespace MO31809
open CategoryTheory.CategoryStruct (comp)
open Finset (sum_congr mem_univ sum_eq_zero sum_eq_single)
open CategoryTheory Preadditive Limits Pretriangulated
def rev (v : Fin 5) : Fin 5 := ⟨4 - v.1,by omega⟩
lemma z104 (v : Fin 5) : rev (rev v) = v := by
  ext; dsimp [rev]; omega
lemma rev_val (v : Fin 5) : (rev v).1 = 4 - v.1 := rfl
abbrev B := { t : Fin 5 × Fin 5 × Fin 5 //
  t.2.1.1 ≤ t.1.1 + t.2.2.1 ∧ t.2.2.1 ≤ t.2.1.1 ∧ t.1.1 + t.2.2.1 < 5 }
def B.src (b : B) : Fin 5 := b.1.1
def B.tgt (b : B) : Fin 5 := b.1.2.1
def B.deg (b : B) : Fin 5 := b.1.2.2
def eB (v : Fin 5) : B :=
  ⟨(v,v,⟨0,by omega⟩),by dsimp; omega⟩
def mulB (b₂ b₁ : B) : Option B :=
  if h : b₁.tgt = b₂.src ∧ b₁.deg.1 + b₂.deg.1 ≤ b₂.tgt.1 ∧
      b₁.src.1 + (b₁.deg.1 + b₂.deg.1) < 5 then
    some ⟨(b₁.src,b₂.tgt,⟨b₁.deg.1 + b₂.deg.1,by omega⟩),by
      have h1 := b₁.2; have h2 := b₂.2
      dsimp [B.src,B.tgt,B.deg] at h ⊢
      omega⟩
  else none
lemma z71 {x y z : B} (h : mulB x y = some z) : z.src = y.src := by
  dsimp only [mulB] at h
  by_cases hc : y.tgt = x.src ∧ y.deg.1 + x.deg.1 ≤ x.tgt.1 ∧ y.src.1 + (y.deg.1 + x.deg.1) < 5
  · rw [dif_pos hc] at h
    have h' := Option.some.inj h
    rw [← h']
    rfl
  · rw [dif_neg hc] at h
    cases h
lemma z176 {x y : B}
    (h : y.tgt = x.src ∧ y.deg.1 + x.deg.1 ≤ x.tgt.1 ∧ y.src.1 + (y.deg.1 + x.deg.1) < 5) :
    mulB x y = some ⟨(y.src,x.tgt,⟨y.deg.1 + x.deg.1,by omega⟩),by
      have h1 := y.2; have h2 := x.2; dsimp [B.src,B.tgt,B.deg] at h h1 h2 ⊢; omega⟩ := by
  unfold mulB; exact dif_pos h
lemma z128 {x y : B}
    (h : ¬ (y.tgt = x.src ∧ y.deg.1 + x.deg.1 ≤ x.tgt.1 ∧ y.src.1 + (y.deg.1 + x.deg.1) < 5)) :
    mulB x y = none := by
  unfold mulB; exact dif_neg h
lemma z151 (b₃ b₂ b₁ : B) :
    (mulB b₃ b₂).bind (fun x => mulB x b₁) = (mulB b₂ b₁).bind (fun y => mulB b₃ y) := by
  have h1 := b₁.2; have h2 := b₂.2; have h3 := b₃.2
  by_cases h32 : b₂.tgt = b₃.src ∧ b₂.deg.1 + b₃.deg.1 ≤ b₃.tgt.1 ∧
      b₂.src.1 + (b₂.deg.1 + b₃.deg.1) < 5
  · rw [z176 h32,Option.bind_some]
    by_cases h21 : b₁.tgt = b₂.src ∧ b₁.deg.1 + b₂.deg.1 ≤ b₂.tgt.1 ∧
        b₁.src.1 + (b₁.deg.1 + b₂.deg.1) < 5
    · rw [z176 h21,Option.bind_some]
      by_cases ha : b₁.tgt = b₂.src ∧ b₁.deg.1 + (b₂.deg.1 + b₃.deg.1) ≤ b₃.tgt.1 ∧
          b₁.src.1 + (b₁.deg.1 + (b₂.deg.1 + b₃.deg.1)) < 5
      · have hb : b₂.tgt = b₃.src ∧ (b₁.deg.1 + b₂.deg.1) + b₃.deg.1 ≤ b₃.tgt.1 ∧
            b₁.src.1 + ((b₁.deg.1 + b₂.deg.1) + b₃.deg.1) < 5 :=
          ⟨h32.1,by omega,by omega⟩
        rw [z176 (by simpa [B.src,B.tgt,B.deg] using ha),
            z176 (by simpa [B.src,B.tgt,B.deg] using hb)]
        congr 1; apply Subtype.ext; apply Prod.ext; rfl; apply Prod.ext; rfl
        apply Fin.ext; dsimp [B.src,B.tgt,B.deg]; omega
      · have hb : ¬ (b₂.tgt = b₃.src ∧ (b₁.deg.1 + b₂.deg.1) + b₃.deg.1 ≤ b₃.tgt.1 ∧
            b₁.src.1 + ((b₁.deg.1 + b₂.deg.1) + b₃.deg.1) < 5) := by
          intro h; apply ha; exact ⟨h21.1,by omega,by omega⟩
        rw [z128 (by simpa [B.src,B.tgt,B.deg] using ha),
            z128 (by simpa [B.src,B.tgt,B.deg] using hb)]
    · rw [z128 h21,Option.bind_none]
      have ha : ¬ (b₁.tgt = b₂.src ∧ b₁.deg.1 + (b₂.deg.1 + b₃.deg.1) ≤ b₃.tgt.1 ∧
          b₁.src.1 + (b₁.deg.1 + (b₂.deg.1 + b₃.deg.1)) < 5) := by
        intro h; apply h21; dsimp [B.src,B.tgt,B.deg] at h h1 h2 h3 h32 ⊢
        refine ⟨h.1,?_,?_⟩ <;> omega
      exact z128 (by simpa [B.src,B.tgt,B.deg] using ha)
  · rw [z128 h32,Option.bind_none]
    by_cases h21 : b₁.tgt = b₂.src ∧ b₁.deg.1 + b₂.deg.1 ≤ b₂.tgt.1 ∧
        b₁.src.1 + (b₁.deg.1 + b₂.deg.1) < 5
    · rw [z176 h21,Option.bind_some]
      have hb : ¬ (b₂.tgt = b₃.src ∧ (b₁.deg.1 + b₂.deg.1) + b₃.deg.1 ≤ b₃.tgt.1 ∧
          b₁.src.1 + ((b₁.deg.1 + b₂.deg.1) + b₃.deg.1) < 5) := by
        intro h; apply h32; dsimp [B.src,B.tgt,B.deg] at h h1 h2 h3 h21 ⊢
        refine ⟨h.1,?_,?_⟩ <;> omega
      exact (z128 (by simpa [B.src,B.tgt,B.deg] using hb)).symm
    · rw [z128 h21,Option.bind_none]
lemma z26 (v : Fin 5) (b : B) :
    mulB (eB v) b = if b.tgt = v then some b else none := by
  have hb := b.2
  unfold mulB
  by_cases h : b.tgt = v
  · have hc : b.tgt = (eB v).src ∧ b.deg.1 + (eB v).deg.1 ≤ (eB v).tgt.1 ∧
        b.src.1 + (b.deg.1 + (eB v).deg.1) < 5 := by
      dsimp [eB,B.src,B.tgt,B.deg] at h hb ⊢
      refine ⟨h,?_,?_⟩ <;> subst h <;> omega
    rw [dif_pos hc,if_pos h]
    congr 1; apply Subtype.ext
    rcases b with ⟨⟨i,j,⟨r,hr⟩⟩,_⟩
    dsimp [eB,B.src,B.tgt,B.deg] at h ⊢; subst h; rfl
  · have hc : ¬ (b.tgt = (eB v).src ∧ b.deg.1 + (eB v).deg.1 ≤ (eB v).tgt.1 ∧
        b.src.1 + (b.deg.1 + (eB v).deg.1) < 5) := fun hh => h hh.1
    rw [dif_neg hc,if_neg h]
lemma z91 (b : B) (v : Fin 5) :
    mulB b (eB v) = if v = b.src then some b else none := by
  have hb := b.2
  unfold mulB
  by_cases h : v = b.src
  · have hc : (eB v).tgt = b.src ∧ (eB v).deg.1 + b.deg.1 ≤ b.tgt.1 ∧
        (eB v).src.1 + ((eB v).deg.1 + b.deg.1) < 5 := by
      dsimp [eB,B.src,B.tgt,B.deg] at h hb ⊢
      refine ⟨h,?_,?_⟩ <;> subst h <;> omega
    rw [dif_pos hc,if_pos h]
    congr 1; apply Subtype.ext
    rcases b with ⟨⟨i,j,⟨r,hr⟩⟩,_⟩
    dsimp [eB,B.src,B.tgt,B.deg] at h ⊢; subst h; congr 2; ext; simp
  · have hc : ¬ ((eB v).tgt = b.src ∧ (eB v).deg.1 + b.deg.1 ≤ b.tgt.1 ∧
        (eB v).src.1 + ((eB v).deg.1 + b.deg.1) < 5) := fun hh => h hh.1
    rw [dif_neg hc,if_neg h]
def nuB (b : B) : B :=
  ⟨(rev b.src,rev b.tgt,⟨b.deg.1 + b.src.1 - b.tgt.1,by
    have := b.2; dsimp [B.src,B.tgt,B.deg] at *; omega⟩),by
    have := b.2; dsimp [rev,B.src,B.tgt,B.deg] at *; omega⟩
lemma z19 (b : B) : nuB (nuB b) = b := by
  have := b.2
  rcases b with ⟨⟨⟨i,hi⟩,⟨j,hj⟩,⟨r,hr⟩⟩,hb⟩
  apply Subtype.ext
  dsimp [nuB,rev,B.src,B.tgt,B.deg] at hb ⊢
  ext <;> dsimp <;> omega
lemma nuB_eB (v : Fin 5) : nuB (eB v) = eB (rev v) := by
  apply Subtype.ext; dsimp [nuB,eB,rev,B.src,B.tgt,B.deg]
  apply Prod.ext; rfl; apply Prod.ext; rfl; ext; dsimp; omega
lemma z187 (b₂ b₁ : B) :
    mulB (nuB b₂) (nuB b₁) = (mulB b₂ b₁).map nuB := by
  have h1 := b₁.2; have h2 := b₂.2
  unfold mulB
  by_cases ha : b₁.tgt = b₂.src ∧ b₁.deg.1 + b₂.deg.1 ≤ b₂.tgt.1 ∧
      b₁.src.1 + (b₁.deg.1 + b₂.deg.1) < 5
  · have hb : (nuB b₁).tgt = (nuB b₂).src ∧ (nuB b₁).deg.1 + (nuB b₂).deg.1 ≤ (nuB b₂).tgt.1 ∧
        (nuB b₁).src.1 + ((nuB b₁).deg.1 + (nuB b₂).deg.1) < 5 := by
      have hmid := congrArg Fin.val ha.1
      dsimp [nuB,rev,B.src,B.tgt,B.deg] at h1 h2 ha hmid ⊢
      refine ⟨Fin.ext (by dsimp; omega),by omega,by omega⟩
    rw [dif_pos hb,dif_pos ha,Option.map_some]
    congr 1; apply Subtype.ext
    dsimp [nuB,rev,B.src,B.tgt,B.deg] at h1 h2 ha ⊢
    apply Prod.ext; · rfl
    apply Prod.ext; · rfl
    ext; dsimp; omega
  · have hb : ¬ ((nuB b₁).tgt = (nuB b₂).src ∧ (nuB b₁).deg.1 + (nuB b₂).deg.1 ≤ (nuB b₂).tgt.1 ∧
        (nuB b₁).src.1 + ((nuB b₁).deg.1 + (nuB b₂).deg.1) < 5) := by
      intro h; apply ha
      have hmid := congrArg Fin.val h.1
      dsimp [nuB,rev,B.src,B.tgt,B.deg] at h1 h2 h hmid ⊢
      refine ⟨Fin.ext (by omega),by omega,by omega⟩
    rw [dif_neg hb,dif_neg ha]; rfl
def dualB (b : B) : B :=
  ⟨(b.tgt,rev b.src,⟨4 - b.src.1 - b.deg.1,by
    have := b.2; dsimp [B.src,B.tgt,B.deg] at *; omega⟩),by
    have := b.2; dsimp [rev,B.src,B.tgt,B.deg] at *; omega⟩
def socB (v : Fin 5) : B :=
  ⟨(v,rev v,rev v),by dsimp [rev]; omega⟩
lemma z131 (b : B) : mulB (dualB b) b = some (socB b.src) := by
  have := b.2
  unfold mulB
  have h : b.tgt = (dualB b).src ∧ b.deg.1 + (dualB b).deg.1 ≤ (dualB b).tgt.1 ∧
      b.src.1 + (b.deg.1 + (dualB b).deg.1) < 5 := by
    dsimp [dualB,rev,B.src,B.tgt,B.deg] at this ⊢
    exact ⟨rfl,by omega,by omega⟩
  rw [dif_pos h]
  congr 1; apply Subtype.ext
  dsimp [dualB,socB,rev,B.src,B.tgt,B.deg] at this ⊢
  apply Prod.ext; · rfl
  apply Prod.ext; · rfl
  ext; dsimp; omega
lemma z150 (a b : B) :
    (∃ v : Fin 5,mulB a b = some (socB v)) ↔ a = dualB b := by
  constructor
  · rintro ⟨v,hv⟩
    have ha := a.2; have hb := b.2
    unfold mulB at hv
    by_cases h : b.tgt = a.src ∧ b.deg.1 + a.deg.1 ≤ a.tgt.1 ∧
        b.src.1 + (b.deg.1 + a.deg.1) < 5
    · rw [dif_pos h] at hv
      have heq := Option.some.inj hv
      have hsrc := congrArg (fun x : B => x.1.1.1) heq
      have htgt := congrArg (fun x : B => x.1.2.1.1) heq
      have hdeg := congrArg (fun x : B => x.1.2.2.1) heq
      have hmid := congrArg Fin.val h.1
      dsimp [socB,rev,B.src,B.tgt,B.deg] at hsrc htgt hdeg hmid ha hb h
      apply Subtype.ext
      rcases a with ⟨⟨⟨ai,_⟩,⟨aj,_⟩,⟨ar,_⟩⟩,_⟩
      rcases b with ⟨⟨⟨bi,_⟩,⟨bj,_⟩,⟨br,_⟩⟩,_⟩
      dsimp [dualB,rev,B.src,B.tgt,B.deg] at hsrc htgt hdeg hmid ⊢
      ext <;> dsimp <;> omega
    · rw [dif_neg h] at hv; cases hv
  · rintro rfl
    exact ⟨b.src,z131 b⟩
structure Λ where
  val : B → ZMod 2
deriving DecidableEq
lemma Λ.ext {a b : Λ} (h : a.val = b.val) : a = b := by cases a; cases b; congr
private lemma xL {a b : Λ} (h : a.val = b.val) : a = b := Λ.ext h
instance : Fintype Λ :=
  Fintype.ofEquiv (B → ZMod 2) ⟨Λ.mk,Λ.val,fun _ => rfl,fun _ => rfl⟩
def z12 (b : B) : Λ := ⟨fun c => if c = b then 1 else 0⟩
instance : Zero Λ := ⟨⟨0⟩⟩
instance : Add Λ := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance : Neg Λ := ⟨fun a => a⟩
instance : Sub Λ := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance : SMul ℕ Λ := ⟨fun n a => ⟨n • a.val⟩⟩
instance : SMul ℤ Λ := ⟨fun n a => ⟨n • a.val⟩⟩
instance : SMul (ZMod 2) Λ := ⟨fun r a => ⟨r • a.val⟩⟩
@[simp] lemma Λ.zero_val (c : B) : (0 : Λ).val c = 0 := rfl
@[simp] lemma Λ.add_val (a b : Λ) (c : B) : (a + b).val c = a.val c + b.val c := rfl
@[simp] lemma Λ.smul_val (r : ZMod 2) (a : Λ) (c : B) : (r • a).val c = r * a.val c := rfl
instance : AddCommGroup Λ where
  add_assoc a b c := by apply xL; ext x; exact add_assoc _ _ _
  zero_add a := by apply xL; ext x; exact zero_add _
  add_zero a := by apply xL; ext x; exact add_zero _
  nsmul := (· • ·)
  nsmul_zero a := by apply xL; ext x; exact zero_nsmul _
  nsmul_succ n a := by apply xL; ext x; exact succ_nsmul _ _
  zsmul := (· • ·)
  zsmul_zero' a := by apply xL; ext x; exact zero_zsmul _
  zsmul_succ' n a := by apply xL; ext x; exact AddMonoid.nsmul_succ n (a.val x)
  zsmul_neg' n a := by
    apply xL; ext x
    change (Int.negSucc n) • a.val x = ((n + 1 : ℕ) • a.val x)
    rw [zsmul_eq_mul,nsmul_eq_mul]
    have h2 : ∀ z : ZMod 2,-z = z := by decide
    have : ((Int.negSucc n : ℤ) : ZMod 2) = -(((n + 1 : ℕ) : ZMod 2)) := by push_cast; ring
    rw [this,neg_mul,h2]
  neg_add_cancel a := by
    apply xL; ext x
    change a.val x + a.val x = 0
    generalize a.val x = z; revert z; decide
  add_comm a b := by apply xL; ext x; exact add_comm _ _
  sub_eq_add_neg a b := rfl
lemma Λ.add_self (a : Λ) : a + a = 0 := neg_add_cancel a
lemma Λ.neg_eq (a : Λ) : -a = a := rfl
instance : One Λ := ⟨⟨fun c => if c.src = c.tgt ∧ c.deg.1 = 0 then 1 else 0⟩⟩
instance : Mul Λ :=
  ⟨fun a b => ⟨fun c => ∑ x : B,∑ y : B,if mulB x y = some c then a.val x * b.val y else 0⟩⟩
lemma Λ.mul_val (a b : Λ) (c : B) :
    (a * b).val c = ∑ x : B,∑ y : B,if mulB x y = some c then a.val x * b.val y else 0 := rfl
lemma Λ.one_val_eq_sum (c : B) :
    (1 : Λ).val c = ∑ v : Fin 5,if c = eB v then (1 : ZMod 2) else 0 := by
  change (if c.src = c.tgt ∧ c.deg.1 = 0 then (1 : ZMod 2) else 0) = _
  by_cases h : c.src = c.tgt ∧ c.deg.1 = 0
  · rw [if_pos h]
    rw [sum_eq_single c.src]
    · rw [if_pos]; apply Subtype.ext; rcases c with ⟨⟨i,j,⟨r,hr⟩⟩,_⟩
      dsimp [eB,B.src,B.tgt,B.deg] at h ⊢; rcases h with ⟨rfl,rfl⟩; rfl
    · intro v _ hv; rw [if_neg]; intro heq; exact hv (congrArg B.src heq).symm
    · intro hnot; exact absurd (mem_univ _) hnot
  · rw [if_neg h]
    symm; refine sum_eq_zero fun v _ => ?_
    rw [if_neg]; intro heq; apply h; subst heq; exact ⟨rfl,rfl⟩
instance : Ring Λ where
  left_distrib a b c := by
    apply xL; ext d; simp only [Λ.mul_val,Λ.add_val]
    rw [← Finset.sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine sum_congr rfl fun y _ => by split_ifs <;> ring
  right_distrib a b c := by
    apply xL; ext d; simp only [Λ.mul_val,Λ.add_val]
    rw [← Finset.sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine sum_congr rfl fun y _ => by split_ifs <;> ring
  zero_mul a := by
    apply xL; ext d; simp only [Λ.mul_val,Λ.zero_val,zero_mul,ite_self,Finset.sum_const_zero]
  mul_zero a := by
    apply xL; ext d; simp only [Λ.mul_val,Λ.zero_val,mul_zero,ite_self,Finset.sum_const_zero]
  mul_assoc a b c := by
    apply xL; ext d
    simp only [Λ.mul_val]
    have hlhs :
        ∑ xy : B,∑ z : B,
          (if mulB xy z = some d then
            (∑ x : B,∑ y : B,if mulB x y = some xy then a.val x * b.val y else 0) * c.val z
          else 0) =
        ∑ x : B,∑ y : B,∑ z : B,
          if (mulB x y).bind (fun xy => mulB xy z) = some d then a.val x * b.val y * c.val z else 0 := by
      calc _ = ∑ xy : B,∑ z : B,∑ x : B,∑ y : B,
            if mulB xy z = some d ∧ mulB x y = some xy then a.val x * b.val y * c.val z else 0 := by
            refine sum_congr rfl fun xy _ => sum_congr rfl fun z _ => ?_
            by_cases h1 : mulB xy z = some d
            · rw [if_pos h1,Finset.sum_mul]
              refine sum_congr rfl fun x _ => ?_
              rw [Finset.sum_mul]
              refine sum_congr rfl fun y _ => ?_
              by_cases h2 : mulB x y = some xy
              · rw [if_pos h2,if_pos ⟨h1,h2⟩]
              · rw [if_neg h2,if_neg (fun hh => h2 hh.2),zero_mul]
            · rw [if_neg h1]
              symm; refine sum_eq_zero fun x _ => sum_eq_zero fun y _ => ?_
              rw [if_neg (fun hh => h1 hh.1)]
        _ = ∑ x : B,∑ y : B,∑ z : B,∑ xy : B,
            if mulB xy z = some d ∧ mulB x y = some xy then a.val x * b.val y * c.val z else 0 := by
            calc _ = ∑ xy : B,∑ x : B,∑ z : B,∑ y : B,
                  if mulB xy z = some d ∧ mulB x y = some xy then a.val x * b.val y * c.val z else 0 := by
                  refine sum_congr rfl fun xy _ => Finset.sum_comm
              _ = ∑ x : B,∑ xy : B,∑ z : B,∑ y : B,
                  if mulB xy z = some d ∧ mulB x y = some xy then a.val x * b.val y * c.val z else 0 :=
                  Finset.sum_comm
              _ = ∑ x : B,∑ xy : B,∑ y : B,∑ z : B,
                  if mulB xy z = some d ∧ mulB x y = some xy then a.val x * b.val y * c.val z else 0 := by
                  refine sum_congr rfl fun x _ => sum_congr rfl fun xy _ => Finset.sum_comm
              _ = ∑ x : B,∑ y : B,∑ xy : B,∑ z : B,
                  if mulB xy z = some d ∧ mulB x y = some xy then a.val x * b.val y * c.val z else 0 := by
                  refine sum_congr rfl fun x _ => Finset.sum_comm
              _ = _ := by
                  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => Finset.sum_comm
        _ = _ := by
            refine sum_congr rfl fun x _ => sum_congr rfl fun y _ =>
              sum_congr rfl fun z _ => ?_
            cases hxy : mulB x y with
            | none =>
              simp only [Option.bind_none,reduceCtorEq,↓reduceIte]
              refine sum_eq_zero fun xy _ => ?_
              rw [if_neg]; rintro ⟨_,h⟩; simp at h
            | some xy0 =>
              simp only [Option.bind_some,Option.some.injEq]
              rw [sum_eq_single xy0]
              · simp
              · intro xy _ hne; rw [if_neg]; rintro ⟨_,h⟩; exact hne h.symm
              · intro hnot; exact absurd (mem_univ _) hnot
    have hrhs :
        ∑ x : B,∑ yz : B,
          (if mulB x yz = some d then
            a.val x * (∑ y : B,∑ z : B,if mulB y z = some yz then b.val y * c.val z else 0)
          else 0) =
        ∑ x : B,∑ y : B,∑ z : B,
          if (mulB y z).bind (fun yz => mulB x yz) = some d then a.val x * b.val y * c.val z else 0 := by
      calc _ = ∑ x : B,∑ yz : B,∑ y : B,∑ z : B,
            if mulB x yz = some d ∧ mulB y z = some yz then a.val x * b.val y * c.val z else 0 := by
            refine sum_congr rfl fun x _ => sum_congr rfl fun yz _ => ?_
            by_cases h1 : mulB x yz = some d
            · rw [if_pos h1,Finset.mul_sum]
              refine sum_congr rfl fun y _ => ?_
              rw [Finset.mul_sum]
              refine sum_congr rfl fun z _ => ?_
              by_cases h2 : mulB y z = some yz
              · rw [if_pos h2,if_pos ⟨h1,h2⟩]; ring
              · rw [if_neg h2,if_neg (fun hh => h2 hh.2),mul_zero]
            · rw [if_neg h1]
              symm; refine sum_eq_zero fun y _ => sum_eq_zero fun z _ => ?_
              rw [if_neg (fun hh => h1 hh.1)]
        _ = ∑ x : B,∑ y : B,∑ z : B,∑ yz : B,
            if mulB x yz = some d ∧ mulB y z = some yz then a.val x * b.val y * c.val z else 0 := by
            refine sum_congr rfl fun x _ => ?_
            rw [Finset.sum_comm]
            refine sum_congr rfl fun y _ => Finset.sum_comm
        _ = _ := by
            refine sum_congr rfl fun x _ => sum_congr rfl fun y _ =>
              sum_congr rfl fun z _ => ?_
            cases hyz : mulB y z with
            | none =>
              simp only [Option.bind_none,reduceCtorEq,↓reduceIte]
              refine sum_eq_zero fun yz _ => ?_
              rw [if_neg]; rintro ⟨_,h⟩; simp at h
            | some yz0 =>
              simp only [Option.bind_some,Option.some.injEq]
              rw [sum_eq_single yz0]
              · simp
              · intro yz _ hne; rw [if_neg]; rintro ⟨_,h⟩; exact hne h.symm
              · intro hnot; exact absurd (mem_univ _) hnot
    rw [hlhs,hrhs]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ =>
      sum_congr rfl fun z _ => by rw [z151]
  one_mul a := by
    apply xL; ext d; simp only [Λ.mul_val]
    rw [sum_eq_single (eB d.tgt)]
    · rw [sum_eq_single d]
      · rw [z26,if_pos rfl,if_pos rfl,Λ.one_val_eq_sum]
        rw [sum_eq_single d.tgt]
        · simp
        · intro v _ hv; rw [if_neg]; intro h; exact hv (congrArg B.src h).symm
        · intro h; exact absurd (mem_univ _) h
      · intro y _ hy
        rw [z26]
        by_cases h1 : y.tgt = d.tgt
        · rw [if_pos h1,if_neg (fun hh => hy (Option.some.inj hh))]
        · rw [if_neg h1,if_neg (by simp)]
      · intro h; exact absurd (mem_univ _) h
    · intro x _ hx
      refine sum_eq_zero fun y _ => ?_
      rw [Λ.one_val_eq_sum]
      by_cases hx1 : ∃ v : Fin 5,x = eB v
      · obtain ⟨v,rfl⟩ := hx1
        rw [z26]
        by_cases h1 : y.tgt = v
        · rw [if_pos h1,if_neg]
          intro hh; have hd := Option.some.inj hh; apply hx; rw [← hd,h1]
        · rw [if_neg h1,if_neg (by simp)]
      · push Not at hx1
        have h0 : (∑ v : Fin 5,if x = eB v then (1 : ZMod 2) else 0) = 0 :=
          sum_eq_zero fun v _ => if_neg (hx1 v)
        simp [h0]
    · intro h; exact absurd (mem_univ _) h
  mul_one a := by
    apply xL; ext d; simp only [Λ.mul_val]
    rw [Finset.sum_comm,sum_eq_single (eB d.src)]
    · rw [sum_eq_single d]
      · rw [z91,if_pos rfl,if_pos rfl,Λ.one_val_eq_sum]
        rw [sum_eq_single d.src]
        · simp
        · intro v _ hv; rw [if_neg]; intro h; exact hv (congrArg B.src h).symm
        · intro h; exact absurd (mem_univ _) h
      · intro x _ hx
        rw [z91]
        by_cases h1 : d.src = x.src
        · rw [if_pos h1,if_neg (fun hh => hx (Option.some.inj hh))]
        · rw [if_neg h1,if_neg (by simp)]
      · intro h; exact absurd (mem_univ _) h
    · intro y _ hy
      refine sum_eq_zero fun x _ => ?_
      rw [Λ.one_val_eq_sum]
      by_cases hy1 : ∃ v : Fin 5,y = eB v
      · obtain ⟨v,rfl⟩ := hy1
        rw [z91]
        by_cases h1 : v = x.src
        · rw [if_pos h1,if_neg]
          intro hh; have hd := Option.some.inj hh; apply hy; rw [← hd,← h1]
        · rw [if_neg h1,if_neg (by simp)]
      · push Not at hy1
        have h0 : (∑ v : Fin 5,if y = eB v then (1 : ZMod 2) else 0) = 0 :=
          sum_eq_zero fun v _ => if_neg (hy1 v)
        simp [h0]
    · intro h; exact absurd (mem_univ _) h
instance : Module (ZMod 2) Λ where
  one_smul a := by apply xL; ext x; simp
  mul_smul r s a := by apply xL; ext x; simp [mul_assoc]
  smul_zero r := by apply xL; ext x; simp
  smul_add r a b := by apply xL; ext x; simp [mul_add]
  add_smul r s a := by apply xL; ext x; simp [add_mul]
  zero_smul a := by apply xL; ext x; simp
instance : Algebra (ZMod 2) Λ :=
  Algebra.ofModule (fun r a b => by
    apply xL; ext d; simp only [Λ.mul_val,Λ.smul_val,Finset.mul_sum]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => by split_ifs <;> ring)
    (fun r a b => by
    apply xL; ext d; simp only [Λ.mul_val,Λ.smul_val,Finset.mul_sum]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => by split_ifs <;> ring)
lemma z10 {M : Type*} [AddCommGroup M] [Module Λ M] (x : M) : x + x = 0 := by
  have h : ((1 : Λ) + (1 : Λ)) • x = 0 := by rw [Λ.add_self,zero_smul]
  simpa [add_smul] using h
lemma z153 {M : Type*} [AddCommGroup M] [Module Λ M] (x : M) : -x = x := by
  have := z10 x
  exact eq_neg_of_add_eq_zero_left this |>.symm
def eΛ (v : Fin 5) : Λ := z12 (eB v)
def ν : Λ ≃+* Λ where
  toFun a := ⟨fun c => a.val (nuB c)⟩
  invFun a := ⟨fun c => a.val (nuB c)⟩
  left_inv a := by apply xL; ext c; simp [z19]
  right_inv a := by apply xL; ext c; simp [z19]
  map_add' a b := by apply xL; ext c; rfl
  map_mul' a b := by
    apply xL; ext c; simp only [Λ.mul_val]
    change ∑ x : B,∑ y : B,(if mulB x y = some (nuB c) then a.val x * b.val y else 0) =
      ∑ x : B,∑ y : B,(if mulB x y = some c then a.val (nuB x) * b.val (nuB y) else 0)
    let e : B ≃ B := ⟨nuB,nuB,z19,z19⟩
    rw [← e.sum_comp]
    refine sum_congr rfl fun x _ => ?_
    rw [← e.sum_comp]
    refine sum_congr rfl fun y _ => ?_
    dsimp [e]
    have hiff : mulB (nuB x) (nuB y) = some (nuB c) ↔ mulB x y = some c := by
      rw [z187]
      cases h : mulB x y with
      | none => simp
      | some z =>
        simp only [Option.map_some,Option.some.injEq]
        exact ⟨fun hz => by rw [← z19 z,hz,z19],fun hz => by rw [hz]⟩
    simp [hiff]
lemma ν_ν (a : Λ) : ν (ν a) = a := ν.left_inv a
abbrev Bv (v : Fin 5) := { b : B // b.src = v }
structure Pv (v : Fin 5) where
  val : Bv v → ZMod 2
deriving DecidableEq
lemma Pv.ext {v : Fin 5} {a b : Pv v} (h : a.val = b.val) : a = b := by cases a; cases b; congr
private lemma xP {v : Fin 5} {a b : Pv v} (h : a.val = b.val) : a = b := Pv.ext h
instance (v : Fin 5) : Fintype (Pv v) :=
  Fintype.ofEquiv (Bv v → ZMod 2) ⟨Pv.mk,Pv.val,fun _ => rfl,fun _ => rfl⟩
instance (v : Fin 5) : AddCommGroup (Pv v) where
  zero := ⟨0⟩
  add x y := ⟨x.val + y.val⟩
  neg x := x
  sub x y := ⟨x.val + y.val⟩
  add_assoc a b c := by apply xP; ext x; exact add_assoc _ _ _
  zero_add a := by apply xP; ext x; exact zero_add _
  add_zero a := by apply xP; ext x; exact add_zero _
  nsmul n a := ⟨n • a.val⟩
  nsmul_zero a := by apply xP; ext x; exact zero_nsmul _
  nsmul_succ n a := by apply xP; ext x; exact succ_nsmul _ _
  zsmul n a := ⟨n • a.val⟩
  zsmul_zero' a := by apply xP; ext x; exact zero_zsmul _
  zsmul_succ' n a := by apply xP; ext x; exact AddMonoid.nsmul_succ n (a.val x)
  zsmul_neg' n a := by
    apply xP; ext x
    change (Int.negSucc n) • a.val x = ((n + 1 : ℕ) • a.val x)
    rw [zsmul_eq_mul,nsmul_eq_mul]
    have h2 : ∀ z : ZMod 2,-z = z := by decide
    have : ((Int.negSucc n : ℤ) : ZMod 2) = -(((n + 1 : ℕ) : ZMod 2)) := by push_cast; ring
    rw [this,neg_mul,h2]
  neg_add_cancel a := by
    apply xP; ext x; change a.val x + a.val x = 0; generalize a.val x = z; revert z; decide
  add_comm a b := by apply xP; ext x; exact add_comm _ _
  sub_eq_add_neg a b := rfl
@[simp] lemma Pv.zero_val {v : Fin 5} (c : Bv v) : (0 : Pv v).val c = 0 := rfl
@[simp] lemma Pv.add_val {v : Fin 5} (x y : Pv v) (c : Bv v) : (x + y).val c = x.val c + y.val c := rfl
instance (v : Fin 5) : Module Λ (Pv v) where
  smul a x := ⟨fun c => ∑ b : B,∑ y : Bv v,if mulB b y.1 = some c.1 then a.val b * x.val y else 0⟩
  one_smul x := by
    apply xP; ext c
    change ∑ b : B,∑ y : Bv v,(if mulB b y.1 = some c.1 then (1 : Λ).val b * x.val y else 0) = x.val c
    rw [sum_eq_single (eB c.1.tgt)]
    · rw [sum_eq_single c]
      · rw [z26,if_pos rfl,if_pos rfl,Λ.one_val_eq_sum]
        rw [sum_eq_single c.1.tgt]
        · simp
        · intro w _ hw; rw [if_neg]; intro h; exact hw (congrArg B.src h).symm
        · intro h; exact absurd (mem_univ _) h
      · intro y _ hy
        rw [z26]
        by_cases h1 : y.1.tgt = c.1.tgt
        · rw [if_pos h1,if_neg (fun hh => hy (Subtype.ext (Option.some.inj hh)))]
        · rw [if_neg h1,if_neg (by simp)]
      · intro h; exact absurd (mem_univ _) h
    · intro b _ hb
      refine sum_eq_zero fun y _ => ?_
      rw [Λ.one_val_eq_sum]
      by_cases h1 : ∃ w : Fin 5,b = eB w
      · obtain ⟨w,rfl⟩ := h1
        rw [z26]
        by_cases h2 : y.1.tgt = w
        · rw [if_pos h2,if_neg]
          intro hh; have hyeq := Option.some.inj hh; apply hb; rw [← hyeq,h2]
        · rw [if_neg h2,if_neg (by simp)]
      · push Not at h1
        have h0 : (∑ w : Fin 5,if b = eB w then (1 : ZMod 2) else 0) = 0 :=
          sum_eq_zero fun w _ => if_neg (h1 w)
        simp [h0]
    · intro h; exact absurd (mem_univ _) h
  mul_smul a b x := by
    apply xP; ext c
    change ∑ ab : B,∑ y : Bv v,
        (if mulB ab y.1 = some c.1 then
          (∑ p : B,∑ q : B,if mulB p q = some ab then a.val p * b.val q else 0) * x.val y
        else 0) =
      ∑ p : B,∑ qy : Bv v,
        (if mulB p qy.1 = some c.1 then
          a.val p * (∑ q : B,∑ y : Bv v,if mulB q y.1 = some qy.1 then b.val q * x.val y else 0)
        else 0)
    have hlhs :
        ∑ ab : B,∑ y : Bv v,
          (if mulB ab y.1 = some c.1 then
            (∑ p : B,∑ q : B,if mulB p q = some ab then a.val p * b.val q else 0) * x.val y
          else 0) =
        ∑ p : B,∑ q : B,∑ y : Bv v,
          if (mulB p q).bind (fun ab => mulB ab y.1) = some c.1 then a.val p * b.val q * x.val y else 0 := by
      calc _ = ∑ ab : B,∑ y : Bv v,∑ p : B,∑ q : B,
            if mulB ab y.1 = some c.1 ∧ mulB p q = some ab then a.val p * b.val q * x.val y else 0 := by
            refine sum_congr rfl fun ab _ => sum_congr rfl fun y _ => ?_
            by_cases h1 : mulB ab y.1 = some c.1
            · rw [if_pos h1,Finset.sum_mul]
              refine sum_congr rfl fun p _ => ?_
              rw [Finset.sum_mul]
              refine sum_congr rfl fun q _ => ?_
              by_cases h2 : mulB p q = some ab
              · rw [if_pos h2,if_pos ⟨h1,h2⟩]
              · rw [if_neg h2,if_neg (fun hh => h2 hh.2),zero_mul]
            · rw [if_neg h1]
              symm; refine sum_eq_zero fun p _ => sum_eq_zero fun q _ => ?_
              rw [if_neg (fun hh => h1 hh.1)]
        _ = ∑ p : B,∑ q : B,∑ y : Bv v,∑ ab : B,
            if mulB ab y.1 = some c.1 ∧ mulB p q = some ab then a.val p * b.val q * x.val y else 0 := by
            calc _ = ∑ ab : B,∑ p : B,∑ y : Bv v,∑ q : B,
                  if mulB ab y.1 = some c.1 ∧ mulB p q = some ab then a.val p * b.val q * x.val y else 0 := by
                  refine sum_congr rfl fun ab _ => Finset.sum_comm
              _ = ∑ p : B,∑ ab : B,∑ y : Bv v,∑ q : B,
                  if mulB ab y.1 = some c.1 ∧ mulB p q = some ab then a.val p * b.val q * x.val y else 0 :=
                  Finset.sum_comm
              _ = ∑ p : B,∑ ab : B,∑ q : B,∑ y : Bv v,
                  if mulB ab y.1 = some c.1 ∧ mulB p q = some ab then a.val p * b.val q * x.val y else 0 := by
                  refine sum_congr rfl fun p _ => sum_congr rfl fun ab _ => Finset.sum_comm
              _ = ∑ p : B,∑ q : B,∑ ab : B,∑ y : Bv v,
                  if mulB ab y.1 = some c.1 ∧ mulB p q = some ab then a.val p * b.val q * x.val y else 0 := by
                  refine sum_congr rfl fun p _ => Finset.sum_comm
              _ = _ := by
                  refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => Finset.sum_comm
        _ = _ := by
            refine sum_congr rfl fun p _ => sum_congr rfl fun q _ =>
              sum_congr rfl fun y _ => ?_
            cases hpq : mulB p q with
            | none =>
              simp only [Option.bind_none,reduceCtorEq,↓reduceIte]
              refine sum_eq_zero fun ab _ => ?_
              rw [if_neg]; rintro ⟨_,h⟩; simp at h
            | some ab0 =>
              simp only [Option.bind_some,Option.some.injEq]
              rw [sum_eq_single ab0]
              · simp
              · intro ab _ hne; rw [if_neg]; rintro ⟨_,h⟩; exact hne h.symm
              · intro h; exact absurd (mem_univ _) h
    have hrhs :
        ∑ p : B,∑ qy : Bv v,
          (if mulB p qy.1 = some c.1 then
            a.val p * (∑ q : B,∑ y : Bv v,if mulB q y.1 = some qy.1 then b.val q * x.val y else 0)
          else 0) =
        ∑ p : B,∑ q : B,∑ y : Bv v,
          if (mulB q y.1).bind (fun qy => mulB p qy) = some c.1 then a.val p * b.val q * x.val y else 0 := by
      calc _ = ∑ p : B,∑ qy : Bv v,∑ q : B,∑ y : Bv v,
            if mulB p qy.1 = some c.1 ∧ mulB q y.1 = some qy.1 then a.val p * b.val q * x.val y else 0 := by
            refine sum_congr rfl fun p _ => sum_congr rfl fun qy _ => ?_
            by_cases h1 : mulB p qy.1 = some c.1
            · rw [if_pos h1,Finset.mul_sum]
              refine sum_congr rfl fun q _ => ?_
              rw [Finset.mul_sum]
              refine sum_congr rfl fun y _ => ?_
              by_cases h2 : mulB q y.1 = some qy.1
              · rw [if_pos h2,if_pos ⟨h1,h2⟩]; ring
              · rw [if_neg h2,if_neg (fun hh => h2 hh.2),mul_zero]
            · rw [if_neg h1]
              symm; refine sum_eq_zero fun q _ => sum_eq_zero fun y _ => ?_
              rw [if_neg (fun hh => h1 hh.1)]
        _ = ∑ p : B,∑ q : B,∑ y : Bv v,∑ qy : Bv v,
            if mulB p qy.1 = some c.1 ∧ mulB q y.1 = some qy.1 then a.val p * b.val q * x.val y else 0 := by
            refine sum_congr rfl fun p _ => ?_
            rw [Finset.sum_comm]
            refine sum_congr rfl fun q _ => Finset.sum_comm
        _ = _ := by
            refine sum_congr rfl fun p _ => sum_congr rfl fun q _ =>
              sum_congr rfl fun y _ => ?_
            cases hqy : mulB q y.1 with
            | none =>
              simp only [Option.bind_none,reduceCtorEq,↓reduceIte]
              refine sum_eq_zero fun qy _ => ?_
              rw [if_neg]; rintro ⟨_,h⟩; simp at h
            | some qy0 =>
              simp only [Option.bind_some,Option.some.injEq]
              have hsrc : qy0.src = v := (z71 hqy).trans y.2
              rw [sum_eq_single ⟨qy0,hsrc⟩]
              · simp
              · intro qy _ hne; rw [if_neg]; rintro ⟨_,h⟩; exact hne (Subtype.ext h.symm)
              · intro h; exact absurd (mem_univ _) h
    rw [hlhs,hrhs]
    refine sum_congr rfl fun p _ => sum_congr rfl fun q _ =>
      sum_congr rfl fun y _ => by rw [z151]
  smul_zero a := by
    apply xP; ext c
    change ∑ b : B,∑ y : Bv v,(if mulB b y.1 = some c.1 then a.val b * (0 : Pv v).val y else 0) = 0
    simp only [Pv.zero_val,mul_zero,ite_self,Finset.sum_const_zero]
  smul_add a x y := by
    apply xP; ext c
    change ∑ b : B,∑ z : Bv v,(if mulB b z.1 = some c.1 then a.val b * (x.val z + y.val z) else 0) =
      (∑ b : B,∑ z : Bv v,if mulB b z.1 = some c.1 then a.val b * x.val z else 0) +
      (∑ b : B,∑ z : Bv v,if mulB b z.1 = some c.1 then a.val b * y.val z else 0)
    rw [← Finset.sum_add_distrib]
    refine sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_add_distrib]
    refine sum_congr rfl fun z _ => by split_ifs <;> ring
  add_smul a b x := by
    apply xP; ext c
    change ∑ p : B,∑ z : Bv v,(if mulB p z.1 = some c.1 then (a.val p + b.val p) * x.val z else 0) =
      (∑ p : B,∑ z : Bv v,if mulB p z.1 = some c.1 then a.val p * x.val z else 0) +
      (∑ p : B,∑ z : Bv v,if mulB p z.1 = some c.1 then b.val p * x.val z else 0)
    rw [← Finset.sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib]
    refine sum_congr rfl fun z _ => by split_ifs <;> ring
  zero_smul x := by
    apply xP; ext c
    change ∑ b : B,∑ y : Bv v,(if mulB b y.1 = some c.1 then (0 : Λ).val b * x.val y else 0) = 0
    simp only [Λ.zero_val,zero_mul,ite_self,Finset.sum_const_zero]
lemma Pv.smul_val {v : Fin 5} (a : Λ) (x : Pv v) (c : Bv v) :
    (a • x).val c = ∑ b : B,∑ y : Bv v,if mulB b y.1 = some c.1 then a.val b * x.val y else 0 := rfl
structure nuMod (M : Type) where
  val : M
lemma nuMod.ext {M : Type} {a b : nuMod M} (h : a.val = b.val) : a = b := by cases a; cases b; congr
private lemma xN {M : Type} {a b : nuMod M} (h : a.val = b.val) : a = b := nuMod.ext h
instance {M : Type} [Finite M] : Finite (nuMod M) :=
  Finite.of_equiv M ⟨nuMod.mk,nuMod.val,fun _ => rfl,fun _ => rfl⟩
instance {M : Type} [AddCommGroup M] : Zero (nuMod M) := ⟨⟨0⟩⟩
instance {M : Type} [AddCommGroup M] : Add (nuMod M) := ⟨fun x y => ⟨x.val + y.val⟩⟩
instance {M : Type} [AddCommGroup M] : Neg (nuMod M) := ⟨fun x => ⟨-x.val⟩⟩
instance {M : Type} [AddCommGroup M] : Sub (nuMod M) := ⟨fun x y => ⟨x.val - y.val⟩⟩
instance {M : Type} [AddCommGroup M] : SMul ℕ (nuMod M) := ⟨fun n x => ⟨n • x.val⟩⟩
instance {M : Type} [AddCommGroup M] : SMul ℤ (nuMod M) := ⟨fun n x => ⟨n • x.val⟩⟩
instance {M : Type} [AddCommGroup M] : AddCommGroup (nuMod M) :=
  Function.Injective.addCommGroup nuMod.val (fun _ _ h => nuMod.ext h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
@[simp] lemma nuMod.zero_val {M : Type} [AddCommGroup M] : (0 : nuMod M).val = 0 := rfl
@[simp] lemma nuMod.add_val {M : Type} [AddCommGroup M] (x y : nuMod M) : (x + y).val = x.val + y.val := rfl
@[simp] lemma nuMod.sub_val {M : Type} [AddCommGroup M] (x y : nuMod M) : (x - y).val = x.val - y.val := rfl
instance {M : Type} [AddCommGroup M] [Module Λ M] : Module Λ (nuMod M) where
  smul a x := ⟨(ν a) • x.val⟩
  one_smul x := by apply xN; change (ν 1) • x.val = x.val; rw [map_one,one_smul]
  mul_smul a b x := by apply xN; change (ν (a * b)) • x.val = (ν a) • ((ν b) • x.val); rw [map_mul,mul_smul]
  smul_zero a := by apply xN; change (ν a) • (0 : M) = 0; exact smul_zero (ν a)
  smul_add a x y := by apply xN; exact smul_add (ν a) x.val y.val
  add_smul a b x := by apply xN; change (ν (a + b)) • x.val = (ν a) • x.val + (ν b) • x.val; rw [map_add,add_smul]
  zero_smul x := by apply xN; change (ν 0) • x.val = 0; rw [map_zero,zero_smul]
@[simp] lemma nuMod.smul_val {M : Type} [AddCommGroup M] [Module Λ M] (a : Λ) (x : nuMod M) :
    (a • x).val = (ν a) • x.val := rfl
def nuMap {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (f : M →ₗ[Λ] N) : nuMod M →ₗ[Λ] nuMod N where
  toFun x := ⟨f x.val⟩
  map_add' x y := by apply xN; exact f.map_add x.val y.val
  map_smul' a x := by apply xN; exact f.map_smul (ν a) x.val
@[simp] lemma nuMap_apply_val {M N : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] (f : M →ₗ[Λ] N) (x : nuMod M) :
    (nuMap f x).val = f x.val := rfl
def nuModInvol {M : Type} [AddCommGroup M] [Module Λ M] : nuMod (nuMod M) ≃ₗ[Λ] M where
  toFun x := x.val.val
  invFun x := ⟨⟨x⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by change (ν (ν a)) • x.val.val = a • x.val.val; rw [ν_ν]
def z206 {u v : Fin 5} (h : rev u = v) : nuMod (Pv u) ≃ₗ[Λ] Pv v where
  toFun x := ⟨fun c => x.val.val ⟨nuB c.1,by
    have hc := c.2; dsimp [nuB,B.src] at hc ⊢; rw [hc,← h,z104]⟩⟩
  invFun y := ⟨⟨fun c => y.val ⟨nuB c.1,by
    have hc := c.2; dsimp [nuB,B.src] at hc ⊢; rw [hc,h]⟩⟩⟩
  left_inv x := by apply xN; apply xP; ext c; simp [z19]
  right_inv y := by apply xP; ext c; simp [z19]
  map_add' x y := by apply xP; ext c; rfl
  map_smul' a x := by
    apply xP; ext c
    simp only [RingHom.id_apply,nuMod.smul_val,Pv.smul_val]
    let eB_eq : B ≃ B := ⟨nuB,nuB,z19,z19⟩
    let eBv : Bv v ≃ Bv u :=
      ⟨fun y => ⟨nuB y.1,by have hy := y.2; dsimp [nuB,B.src] at hy ⊢; rw [hy,← h,z104]⟩,
       fun y => ⟨nuB y.1,by have hy := y.2; dsimp [nuB,B.src] at hy ⊢; rw [hy,h]⟩,
       fun y => by apply Subtype.ext; exact z19 y.1,
       fun y => by apply Subtype.ext; exact z19 y.1⟩
    rw [← eB_eq.sum_comp]
    refine sum_congr rfl fun b _ => ?_
    rw [← eBv.sum_comp]
    refine sum_congr rfl fun y _ => ?_
    dsimp [eB_eq,eBv,ν]
    have hiff : mulB (nuB b) (nuB y.1) = some (nuB c.1) ↔ mulB b y.1 = some c.1 := by
      rw [z187]
      cases hm : mulB b y.1 with
      | none => simp
      | some z =>
        simp only [Option.map_some,Option.some.injEq]
        exact ⟨fun hz => by rw [← z19 z,hz,z19],fun hz => by rw [hz]⟩
    simp [hiff,z19]
def z358 (v : Fin 5) : nuMod (Pv v) ≃ₗ[Λ] Pv (rev v) := z206 rfl
structure FP where
  mult : Fin 5 → ℕ
lemma FP.ext {a b : FP} (h : a.mult = b.mult) : a = b := by cases a; cases b; congr
private lemma xF {a b : FP} (h : a.mult = b.mult) : a = b := FP.ext h
abbrev FP.Mod (X : FP) : Type := (v : Fin 5) → Fin (X.mult v) → Pv v
structure FH (X Y : FP) where
  hom : X.Mod →ₗ[Λ] Y.Mod
lemma FH.ext {X Y : FP} {f g : FH X Y} (h : f.hom = g.hom) : f = g := by cases f; cases g; congr
private lemma xH {X Y : FP} {f g : FH X Y} (h : f.hom = g.hom) : f = g := FH.ext h
instance : Category FP where
  Hom X Y := FH X Y
  id X := ⟨LinearMap.id⟩
  comp f g := ⟨g.hom.comp f.hom⟩
lemma FP.hom_ext {X Y : FP} {f g : X ⟶ Y} (h : ∀ x,f.hom x = g.hom x) : f = g :=
  FH.ext (LinearMap.ext h)
@[simp] lemma FH.id_hom (X : FP) : (𝟙 X : X ⟶ X).hom = LinearMap.id := rfl
@[simp] lemma FH.comp_hom {X Y Z : FP} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (comp f g).hom = g.hom.comp f.hom := rfl
instance {X Y : FP} : Zero (FH X Y) := ⟨⟨0⟩⟩
instance {X Y : FP} : Add (FH X Y) := ⟨fun f g => ⟨f.hom + g.hom⟩⟩
instance {X Y : FP} : Neg (FH X Y) := ⟨fun f => ⟨-f.hom⟩⟩
instance {X Y : FP} : Sub (FH X Y) := ⟨fun f g => ⟨f.hom - g.hom⟩⟩
instance {X Y : FP} : SMul ℕ (FH X Y) := ⟨fun n f => ⟨n • f.hom⟩⟩
instance {X Y : FP} : SMul ℤ (FH X Y) := ⟨fun n f => ⟨n • f.hom⟩⟩
instance {X Y : FP} : AddCommGroup (FH X Y) :=
  Function.Injective.addCommGroup FH.hom (fun _ _ h => FH.ext h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
instance : Preadditive FP where
  homGroup X Y := inferInstanceAs (AddCommGroup (FH X Y))
  add_comp P Q R f f' g := by
    apply FP.hom_ext; intro x
    exact LinearMap.map_add g.hom (f.hom x) (f'.hom x)
  comp_add P Q R f g g' := by apply FP.hom_ext; intro x; rfl
@[simp] lemma FH.zero_hom {X Y : FP} : (0 : X ⟶ Y).hom = 0 := rfl
@[simp] lemma FH.add_hom {X Y : FP} (f g : X ⟶ Y) :
    (f + g).hom = f.hom + g.hom := rfl
lemma FP.add_self {X Y : FP} (f : X ⟶ Y) : f + f = 0 := by
  apply FP.hom_ext; intro x; funext v i; exact z10 (f.hom x v i)
lemma FP.neg_eq {X Y : FP} (f : X ⟶ Y) : -f = f := by
  exact eq_neg_of_add_eq_zero_left (FP.add_self f) |>.symm
def FP.zero : FP := ⟨fun _ => 0⟩
lemma FP.isZero_zero : Limits.IsZero FP.zero := by
  rw [Limits.IsZero.iff_id_eq_zero]
  apply FP.hom_ext; intro x; funext v i; exact Fin.elim0 i
instance : HasZeroObject FP := ⟨FP.zero,FP.isZero_zero⟩
def FP.sum (X Y : FP) : FP := ⟨fun v => X.mult v + Y.mult v⟩
def FP.inl (X Y : FP) : X ⟶ FP.sum X Y :=
  ⟨{ toFun := fun x v i => if h : i.1 < X.mult v then x v ⟨i.1,h⟩ else 0
     map_add' := fun x y => by
       funext v i; by_cases h : i.1 < X.mult v
       · simp [dif_pos h]
       · simp [dif_neg h]
     map_smul' := fun a x => by
       funext v i; by_cases h : i.1 < X.mult v
       · simp [dif_pos h]
       · simp [dif_neg h] }⟩
def FP.inr (X Y : FP) : Y ⟶ FP.sum X Y :=
  ⟨{ toFun := fun y v i =>
       if h : i.1 < X.mult v then 0
       else y v ⟨i.1 - X.mult v,by have := i.2; dsimp [FP.sum] at this; omega⟩
     map_add' := fun x y => by
       funext v i; by_cases h : i.1 < X.mult v
       · simp [dif_pos h]
       · simp [dif_neg h]
     map_smul' := fun a x => by
       funext v i; by_cases h : i.1 < X.mult v
       · simp [dif_pos h]
       · simp [dif_neg h] }⟩
def FP.fst (X Y : FP) : FP.sum X Y ⟶ X :=
  ⟨{ toFun := fun z v i => z v ⟨i.1,by dsimp [FP.sum]; omega⟩
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl }⟩
def FP.snd (X Y : FP) : FP.sum X Y ⟶ Y :=
  ⟨{ toFun := fun z v i => z v ⟨X.mult v + i.1,by dsimp [FP.sum]; omega⟩
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl }⟩
lemma FP.inl_fst (X Y : FP) :
    comp (FP.inl X Y) (FP.fst X Y) = 𝟙 X := by
  apply FP.hom_ext; intro x; funext v i
  change (if h : i.1 < X.mult v then x v ⟨i.1,h⟩ else 0) = x v i
  rw [dif_pos i.2]
lemma FP.inl_snd (X Y : FP) :
    comp (FP.inl X Y) (FP.snd X Y) = 0 := by
  apply FP.hom_ext; intro x; funext v i
  change (if h : X.mult v + i.1 < X.mult v then _ else 0) = 0
  rw [dif_neg (by omega)]
lemma FP.inr_fst (X Y : FP) :
    comp (FP.inr X Y) (FP.fst X Y) = 0 := by
  apply FP.hom_ext; intro y; funext v i
  change (if h : i.1 < X.mult v then 0 else _) = 0
  rw [dif_pos i.2]
lemma FP.inr_snd (X Y : FP) :
    comp (FP.inr X Y) (FP.snd X Y) = 𝟙 Y := by
  apply FP.hom_ext; intro y; funext v i
  change (if h : X.mult v + i.1 < X.mult v then 0 else y v ⟨X.mult v + i.1 - X.mult v,_⟩) = y v i
  rw [dif_neg (by omega)]
  exact congrArg (y v) (Fin.ext (by dsimp; omega))
lemma FP.total_sum (X Y : FP) :
    comp (FP.fst X Y) (FP.inl X Y) +
      comp (FP.snd X Y) (FP.inr X Y) = 𝟙 (FP.sum X Y) := by
  apply FP.hom_ext; intro z; funext v i
  change (if h : i.1 < X.mult v then z v ⟨i.1,_⟩ else 0) +
    (if h : i.1 < X.mult v then 0 else z v ⟨X.mult v + (i.1 - X.mult v),_⟩) = z v i
  by_cases h : i.1 < X.mult v
  · rw [dif_pos h,dif_pos h,add_zero]
  · rw [dif_neg h,dif_neg h,zero_add]; exact congrArg (z v) (Fin.ext (by dsimp; omega))
def FP.sumBicone (X Y : FP) : Limits.BinaryBicone X Y where
  pt := FP.sum X Y
  fst := FP.fst X Y
  snd := FP.snd X Y
  inl := FP.inl X Y
  inr := FP.inr X Y
  inl_fst := FP.inl_fst X Y
  inl_snd := FP.inl_snd X Y
  inr_fst := FP.inr_fst X Y
  inr_snd := FP.inr_snd X Y
def FP.sumIsBilimit (X Y : FP) : (FP.sumBicone X Y).IsBilimit :=
  Limits.isBinaryBilimitOfTotal _ (FP.total_sum X Y)
def z13 (X : FP) : FP := ⟨fun v => X.mult (rev v)⟩
lemma z17 (X : FP) : z13 (z13 X) = X := by
  apply xF; ext v; dsimp [z13]; rw [z104]
lemma z141 {n : Fin 5 → ℕ} (f : (v : Fin 5) → Fin (n v) → Pv v)
    {v w : Fin 5} (hw : w = v) (i : Fin (n v)) (c : Bv v) :
    (f w (Fin.cast (by rw [hw]) i)).val ⟨c.1,by rw [hw]; exact c.2⟩ = (f v i).val c := by
  subst hw; rfl
def z3 (X : FP) : nuMod X.Mod ≃ₗ[Λ] (z13 X).Mod where
  toFun x v i := z206 (z104 v) ⟨x.val (rev v) i⟩
  invFun y := ⟨fun v i => z206 (z104 v) ⟨y (rev v) (Fin.cast (by dsimp [z13]; rw [z104]) i)⟩⟩
  left_inv x := by
    apply xN; funext v i; apply xP; ext c
    dsimp [z206]
    simp only [z19]
    exact z141 x.val (z104 v) i c
  right_inv y := by
    funext v i
    apply xP; ext c
    dsimp [z206]
    simp only [z19]
    exact z141 y (z104 v) i c
  map_add' x y := by funext v i; exact (z206 (z104 v)).map_add ⟨x.val (rev v) i⟩ ⟨y.val (rev v) i⟩
  map_smul' a x := by funext v i; exact (z206 (z104 v)).map_smul a ⟨x.val (rev v) i⟩
def shiftFunctor1 : FP ⥤ FP where
  obj := z13
  map {X Y} f := ⟨(z3 Y).toLinearMap.comp
    ((nuMap f.hom).comp (z3 X).symm.toLinearMap)⟩
  map_id X := by
    apply FP.hom_ext; intro x
    exact (z3 X).apply_symm_apply x
  map_comp f g := by apply FP.hom_ext; intro x; simp [nuMap]
instance : shiftFunctor1.Additive where
  map_add {X Y f g} := by
    apply FP.hom_ext; intro x
    change (z3 Y) (nuMap f.hom ((z3 X).symm x) +
      nuMap g.hom ((z3 X).symm x)) =
      (z3 Y) (nuMap f.hom ((z3 X).symm x)) +
      (z3 Y) (nuMap g.hom ((z3 X).symm x))
    exact (z3 Y).map_add _ _
lemma FP.eqToHom_apply {X Y : FP} (h : X = Y) (x : X.Mod) (v : Fin 5) (i : Fin (Y.mult v)) :
    (eqToHom h : X ⟶ Y).hom x v i = x v (Fin.cast (by subst h; rfl) i) := by
  subst h; rfl
lemma z123 (X : FP) (x : (z13 (z13 X)).Mod) :
    ((z3 X).symm ((z3 (z13 X)).symm x).val).val =
      (eqToHom (z17 X) : z13 (z13 X) ⟶ X).hom x := by
  funext v i
  rw [FP.eqToHom_apply (z17 X)]
  apply xP; ext c
  change (x (rev (rev v))
    (Fin.cast (by dsimp [z13]; rw [z104,z104])
      (Fin.cast (by dsimp [z13]; rw [z104]) i))).val
    ⟨nuB (nuB c.1),by have hc := c.2; dsimp [nuB,B.src] at hc ⊢; rw [hc]⟩ =
    (x v (Fin.cast (by rw [z17 X]) i)).val c
  have hnu : (⟨nuB (nuB c.1),by
      have hc := c.2; dsimp [nuB,B.src] at hc ⊢; rw [hc]⟩ : Bv (rev (rev v))) =
      ⟨c.1,by rw [z104]; exact c.2⟩ := Subtype.ext (z19 c.1)
  rw [hnu]
  exact z141 x (z104 v) (Fin.cast (by rw [z17 X]) i) c
lemma z223 (X : FP) (x : X.Mod) :
    (z3 (z13 X)) ⟨z3 X ⟨x⟩⟩ =
      (eqToHom (z17 X).symm : X ⟶ z13 (z13 X)).hom x := by
  have h := z123 X ((z3 (z13 X)) ⟨z3 X ⟨x⟩⟩)
  simp only [LinearEquiv.symm_apply_apply] at h
  have h2 := congrArg (eqToHom (z17 X).symm : X ⟶ z13 (z13 X)).hom h
  have hc : comp (eqToHom (z17 X) : z13 (z13 X) ⟶ X)
      (eqToHom (z17 X).symm) = 𝟙 (z13 (z13 X)) := by simp
  have h3 := congrArg (fun (g : z13 (z13 X) ⟶ z13 (z13 X)) =>
    g.hom ((z3 (z13 X)) ⟨z3 X ⟨x⟩⟩)) hc
  simp only [FH.comp_hom,LinearMap.comp_apply,FH.id_hom,LinearMap.id_apply] at h3
  exact h3.symm.trans h2.symm
def shiftFunctor1SqIso : shiftFunctor1 ⋙ shiftFunctor1 ≅ 𝟭 FP :=
  NatIso.ofComponents
    (fun X => eqToIso (z17 X))
    (fun {X Y} f => by
      apply FP.hom_ext; intro x
      change (eqToHom (z17 Y) : z13 (z13 Y) ⟶ Y).hom
        (z3 (z13 Y) ⟨z3 Y
          ⟨f.hom ((z3 X).symm ((z3 (z13 X)).symm x).val).val⟩⟩) =
        f.hom ((eqToHom (z17 X) : z13 (z13 X) ⟶ X).hom x)
      rw [z123 X x,z223 Y]
      have hY : comp (eqToHom (z17 Y).symm)
          (eqToHom (z17 Y) : z13 (z13 Y) ⟶ Y) = 𝟙 Y := by simp
      have h3 := congrArg (fun (g : Y ⟶ Y) =>
        g.hom (f.hom ((eqToHom (z17 X) : z13 (z13 X) ⟶ X).hom x))) hY
      simp only [FH.comp_hom,LinearMap.comp_apply,FH.id_hom,LinearMap.id_apply] at h3
      exact h3)
def z301 : ℤ → Bool
  | Int.ofNat n => n % 2 == 1
  | Int.negSucc n => n % 2 == 0
lemma z155 (n : ℤ) : z301 n = decide (n % 2 = 1) := by
  cases n with
  | ofNat k =>
    simp only [z301,Int.ofNat_eq_natCast]
    by_cases h : k % 2 = 1
    · simp [h]; omega
    · have h0 : k % 2 = 0 := by omega
      simp [h0]; omega
  | negSucc k =>
    simp only [z301,Int.negSucc_eq]
    by_cases h : k % 2 = 0
    · simp [h]; omega
    · have h1 : k % 2 = 1 := by omega
      simp [h1]; omega
lemma intOdd_add (n m : ℤ) : z301 (n + m) = xor (z301 n) (z301 m) := by
  rw [z155,z155,z155]
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hn with hn | hn <;> rcases hm with hm | hm <;>
    simp [hn,hm,Int.add_emod]
def z75 : Bool → FP ⥤ FP
  | false => 𝟭 FP
  | true => shiftFunctor1
instance (b : Bool) : (z75 b).Additive := by
  cases b <;> dsimp [z75] <;> infer_instance
def z242 : ∀ a b : Bool,z75 (xor a b) ≅ z75 a ⋙ z75 b
  | false,false => (Functor.leftUnitor _).symm
  | false,true => (Functor.leftUnitor _).symm
  | true,false => (Functor.rightUnitor _).symm
  | true,true => shiftFunctor1SqIso.symm
lemma z220 (a b : Bool) (X : FP) :
    (z75 (xor a b)).obj X = (z75 a ⋙ z75 b).obj X := by
  cases a <;> cases b <;> simp [z75,shiftFunctor1,z17]
lemma z48 (a b : Bool) (X : FP) :
    (z242 a b).hom.app X = eqToHom (z220 a b X) := by
  cases a <;> cases b <;> rfl
def z260 : ShiftMkCore FP ℤ where
  F n := z75 (z301 n)
  zero := Iso.refl _
  add n m := eqToIso (by rw [intOdd_add]) ≪≫ z242 (z301 n) (z301 m)
  assoc_hom_app m₁ m₂ m₃ X := by
    simp only [Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,eqToHom_app,
      z48,eqToHom_map,eqToHom_trans]
  zero_add_hom_app n X := by
    simp only [Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,eqToHom_app,
      z48,Iso.refl_inv,NatTrans.id_app,eqToHom_trans]
    erw [CategoryTheory.Functor.map_id,Category.comp_id]
    rfl
  add_zero_hom_app n X := by
    simp only [Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,eqToHom_app,
      z48,Iso.refl_inv,NatTrans.id_app,eqToHom_trans]
    erw [Category.comp_id]
    rfl
instance : HasShift FP ℤ := hasShiftMk FP ℤ z260
instance (n : ℤ) : (shiftFunctor FP n).Additive := by
  change (z75 (z301 n)).Additive
  infer_instance
lemma z357 : shiftFunctor FP (1 : ℤ) = shiftFunctor1 := rfl
lemma z340 (X : FP) : X⟦(1 : ℤ)⟧ = z13 X := rfl
lemma z341 {X Y : FP} (f : X ⟶ Y) : f⟦(1 : ℤ)⟧' = shiftFunctor1.map f := rfl
lemma z5 {X Y : FP} (f : X ⟶ Y) (x : nuMod X.Mod) :
    z3 Y (nuMap f.hom x) = (f⟦(1 : ℤ)⟧').hom (z3 X x) := by
  change z3 Y (nuMap f.hom x) =
    z3 Y (nuMap f.hom ((z3 X).symm (z3 X x)))
  simp
def StableEq {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (f g : M →ₗ[Λ] N) : Prop :=
  ∃ (Q : FP) (p : M →ₗ[Λ] Q.Mod) (q : Q.Mod →ₗ[Λ] N),f - g = q.comp p
lemma StableEq.refl {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (f : M →ₗ[Λ] N) : StableEq f f :=
  ⟨FP.zero,0,0,by simp⟩
lemma StableEq.symm {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    {f g : M →ₗ[Λ] N} (h : StableEq f g) : StableEq g f := by
  obtain ⟨Q,p,q,hpq⟩ := h
  refine ⟨Q,p,-q,?_⟩
  have : g - f = -(f - g) := (neg_sub f g).symm
  rw [this,hpq,LinearMap.neg_comp]
lemma StableEq.trans {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    {f g h : M →ₗ[Λ] N} (h1 : StableEq f g) (h2 : StableEq g h) : StableEq f h := by
  obtain ⟨Q1,p1,q1,hpq1⟩ := h1
  obtain ⟨Q2,p2,q2,hpq2⟩ := h2
  refine ⟨FP.sum Q1 Q2,
    (FP.inl Q1 Q2).hom.comp p1 + (FP.inr Q1 Q2).hom.comp p2,
    q1.comp (FP.fst Q1 Q2).hom + q2.comp (FP.snd Q1 Q2).hom,?_⟩
  have hsum : f - h = (f - g) + (g - h) := by abel
  rw [hsum,hpq1,hpq2]
  ext x
  have h11 := congrArg (fun (m : Q1 ⟶ Q1) => m.hom (p1 x)) (FP.inl_fst Q1 Q2)
  have h12 := congrArg (fun (m : Q1 ⟶ Q2) => m.hom (p1 x)) (FP.inl_snd Q1 Q2)
  have h21 := congrArg (fun (m : Q2 ⟶ Q1) => m.hom (p2 x)) (FP.inr_fst Q1 Q2)
  have h22 := congrArg (fun (m : Q2 ⟶ Q2) => m.hom (p2 x)) (FP.inr_snd Q1 Q2)
  simp only [FH.comp_hom,FH.id_hom,FH.zero_hom,LinearMap.comp_apply,
    LinearMap.id_apply,LinearMap.zero_apply] at h11 h12 h21 h22
  simp [h11,h12,h21,h22]
lemma StableEq.add {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    {f1 g1 f2 g2 : M →ₗ[Λ] N} (h1 : StableEq f1 g1) (h2 : StableEq f2 g2) :
    StableEq (f1 + f2) (g1 + g2) := by
  have h : StableEq (f1 - g1 + (f2 - g2)) 0 := by
    obtain ⟨Q1,p1,q1,hpq1⟩ := h1
    obtain ⟨Q2,p2,q2,hpq2⟩ := h2
    have h1' : StableEq (f1 - g1) 0 := ⟨Q1,p1,q1,by simpa using hpq1⟩
    have h2' : StableEq 0 (-(f2 - g2)) := ⟨Q2,p2,q2,by simpa using hpq2⟩
    have h3 := StableEq.trans h1' h2'
    obtain ⟨Q,p,q,hpq⟩ := h3
    exact ⟨Q,p,q,by simpa [sub_eq_add_neg] using hpq⟩
  obtain ⟨Q,p,q,hpq⟩ := h
  refine ⟨Q,p,q,?_⟩
  have heq : f1 + f2 - (g1 + g2) = f1 - g1 + (f2 - g2) - 0 := by abel
  rw [heq,hpq]
lemma StableEq.comp_left {M N P : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    [AddCommGroup P] [Module Λ P] (k : N →ₗ[Λ] P) {f g : M →ₗ[Λ] N} (h : StableEq f g) :
    StableEq (k.comp f) (k.comp g) := by
  obtain ⟨Q,p,q,hpq⟩ := h
  refine ⟨Q,p,k.comp q,?_⟩
  rw [← LinearMap.comp_sub,hpq,LinearMap.comp_assoc]
lemma StableEq.comp_right {M N P : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    [AddCommGroup P] [Module Λ P] {f g : N →ₗ[Λ] P} (h : StableEq f g) (k : M →ₗ[Λ] N) :
    StableEq (f.comp k) (g.comp k) := by
  obtain ⟨Q,p,q,hpq⟩ := h
  refine ⟨Q,p.comp k,q,?_⟩
  rw [← LinearMap.sub_comp,hpq,LinearMap.comp_assoc]
lemma StableEq.nuMap {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    {f g : M →ₗ[Λ] N} (h : StableEq f g) : StableEq (MO31809.nuMap f) (MO31809.nuMap g) := by
  obtain ⟨Q,p,q,hpq⟩ := h
  refine ⟨z13 Q,
    (z3 Q).toLinearMap.comp (MO31809.nuMap p),
    (MO31809.nuMap q).comp (z3 Q).symm.toLinearMap,?_⟩
  ext x; apply xN
  simp only [LinearMap.sub_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,
    nuMod.sub_val,nuMap_apply_val,LinearEquiv.symm_apply_apply]
  exact congrArg (fun (m : M →ₗ[Λ] N) => m x.val) hpq
lemma StableEq.of_nuMap {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    {f g : M →ₗ[Λ] N} (h : StableEq (MO31809.nuMap f) (MO31809.nuMap g)) : StableEq f g := by
  have h2 := h.nuMap
  have hf : f = (nuModInvol.toLinearMap.comp (MO31809.nuMap (MO31809.nuMap f))).comp
      nuModInvol.symm.toLinearMap := by ext x; rfl
  have hg : g = (nuModInvol.toLinearMap.comp (MO31809.nuMap (MO31809.nuMap g))).comp
      nuModInvol.symm.toLinearMap := by ext x; rfl
  rw [hf,hg]
  exact (h2.comp_left _).comp_right _
def ExactAt {M N P : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    [AddCommGroup P] [Module Λ P] (f : M →ₗ[Λ] N) (g : N →ₗ[Λ] P) : Prop :=
  LinearMap.range f = LinearMap.ker g
structure ExactSeq3 (M : Type) [AddCommGroup M] [Module Λ M] where
  P0 : FP
  P1 : FP
  P2 : FP
  ι : M →ₗ[Λ] P0.Mod
  d0 : P0 ⟶ P1
  d1 : P1 ⟶ P2
  π : P2.Mod →ₗ[Λ] nuMod M
  ι_inj : Function.Injective ι
  exact0 : ExactAt ι d0.hom
  exact1 : ExactAt d0.hom d1.hom
  exact2 : ExactAt d1.hom π
  π_surj : Function.Surjective π
def ExactSeq3.d2 {M : Type} [AddCommGroup M] [Module Λ M] (E : ExactSeq3 M) :
    E.P2 ⟶ E.P0⟦(1 : ℤ)⟧ :=
  ⟨((z3 E.P0).toLinearMap.comp (nuMap E.ι)).comp E.π⟩
def ExactSeq3.triangle {M : Type} [AddCommGroup M] [Module Λ M] (E : ExactSeq3 M) :
    Triangle FP :=
  Triangle.mk E.d0 E.d1 E.d2
structure ExactSys where
  proj : ∀ (P : FP) {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (g : M →ₗ[Λ] N),Function.Surjective g → ∀ (f : P.Mod →ₗ[Λ] N),
    ∃ h : P.Mod →ₗ[Λ] M,g.comp h = f
  inj : ∀ (Q : FP) {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (i : M →ₗ[Λ] N),Function.Injective i → ∀ (f : M →ₗ[Λ] Q.Mod),
    ∃ h : N →ₗ[Λ] Q.Mod,h.comp i = f
  exists_embed : ∀ (M : Type) [AddCommGroup M] [Module Λ M] [Finite M],
    ∃ (P : FP) (j : M →ₗ[Λ] P.Mod),Function.Injective j
  exists_surj : ∀ (M : Type) [AddCommGroup M] [Module Λ M] [Finite M],
    ∃ (P : FP) (p : P.Mod →ₗ[Λ] M),Function.Surjective p
  seq : ∀ (M : Type) [AddCommGroup M] [Module Λ M] [Finite M],ExactSeq3 M
  map0 : ∀ {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N],(M →ₗ[Λ] N) → ((seq M).P0 ⟶ (seq N).P0)
  map1 : ∀ {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N],(M →ₗ[Λ] N) → ((seq M).P1 ⟶ (seq N).P1)
  map2 : ∀ {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N],(M →ₗ[Λ] N) → ((seq M).P2 ⟶ (seq N).P2)
  map0_ι : ∀ {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] (f : M →ₗ[Λ] N),
    (map0 f).hom.comp (seq M).ι = (seq N).ι.comp f
  map1_d0 : ∀ {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] (f : M →ₗ[Λ] N),
    comp (seq M).d0 (map1 f) = comp (map0 f) (seq N).d0
  map2_d1 : ∀ {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] (f : M →ₗ[Λ] N),
    comp (seq M).d1 (map2 f) = comp (map1 f) (seq N).d1
  π_map2 : ∀ {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] (f : M →ₗ[Λ] N),
    (seq N).π.comp (map2 f).hom = (nuMap f).comp (seq M).π
  map0_comp : ∀ {M N P : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] [AddCommGroup P] [Module Λ P] [Finite P]
    (f : M →ₗ[Λ] N) (g : N →ₗ[Λ] P),
    map0 (g.comp f) = comp (map0 f) (map0 g)
  map1_comp : ∀ {M N P : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] [AddCommGroup P] [Module Λ P] [Finite P]
    (f : M →ₗ[Λ] N) (g : N →ₗ[Λ] P),
    map1 (g.comp f) = comp (map1 f) (map1 g)
  map2_comp : ∀ {M N P : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] [AddCommGroup P] [Module Λ P] [Finite P]
    (f : M →ₗ[Λ] N) (g : N →ₗ[Λ] P),
    map2 (g.comp f) = comp (map2 f) (map2 g)
  map0_zero : ∀ {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N],map0 (0 : M →ₗ[Λ] N) = 0
  map1_zero : ∀ {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N],map1 (0 : M →ₗ[Λ] N) = 0
  map2_zero : ∀ {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N],map2 (0 : M →ₗ[Λ] N) = 0
  map0_exact : ∀ {U Y X : Type} [AddCommGroup U] [Module Λ U] [Finite U]
    [AddCommGroup Y] [Module Λ Y] [Finite Y] [AddCommGroup X] [Module Λ X] [Finite X]
    (w : U →ₗ[Λ] Y) (z : Y →ₗ[Λ] X),
    Function.Injective w → ExactAt w z → Function.Surjective z →
    Function.Injective (map0 w).hom ∧ ExactAt (map0 w).hom (map0 z).hom ∧
      Function.Surjective (map0 z).hom
  map1_exact : ∀ {U Y X : Type} [AddCommGroup U] [Module Λ U] [Finite U]
    [AddCommGroup Y] [Module Λ Y] [Finite Y] [AddCommGroup X] [Module Λ X] [Finite X]
    (w : U →ₗ[Λ] Y) (z : Y →ₗ[Λ] X),
    Function.Injective w → ExactAt w z → Function.Surjective z →
    Function.Injective (map1 w).hom ∧ ExactAt (map1 w).hom (map1 z).hom ∧
      Function.Surjective (map1 z).hom
  map2_exact : ∀ {U Y X : Type} [AddCommGroup U] [Module Λ U] [Finite U]
    [AddCommGroup Y] [Module Λ Y] [Finite Y] [AddCommGroup X] [Module Λ X] [Finite X]
    (w : U →ₗ[Λ] Y) (z : Y →ₗ[Λ] X),
    Function.Injective w → ExactAt w z → Function.Surjective z →
    Function.Injective (map2 w).hom ∧ ExactAt (map2 w).hom (map2 z).hom ∧
      Function.Surjective (map2 z).hom
  seq_nu : ∀ (M : Type) [AddCommGroup M] [Module Λ M] [Finite M],
    ∃ (a0 : (seq M).P0⟦(1 : ℤ)⟧ ⟶ (seq (nuMod M)).P0)
      (a1 : (seq M).P1⟦(1 : ℤ)⟧ ⟶ (seq (nuMod M)).P1)
      (a2 : (seq M).P2⟦(1 : ℤ)⟧ ⟶ (seq (nuMod M)).P2),
      a0.hom.comp ((z3 (seq M).P0).toLinearMap.comp (nuMap (seq M).ι)) =
        (seq (nuMod M)).ι ∧
      comp ((seq M).d0⟦(1 : ℤ)⟧') a1 = comp a0 (seq (nuMod M)).d0 ∧
      comp ((seq M).d1⟦(1 : ℤ)⟧') a2 = comp a1 (seq (nuMod M)).d1 ∧
      (seq (nuMod M)).π.comp a2.hom =
        (nuMap (seq M).π).comp (z3 (seq M).P2).symm.toLinearMap
  η : ∀ (M : Type) [AddCommGroup M] [Module Λ M] [Finite M],M →ₗ[Λ] M
  η_natural : ∀ {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] (f : M →ₗ[Λ] N),
    StableEq ((η N).comp f) (f.comp (η M))
  η_sq_zero : ∀ (M : Type) [AddCommGroup M] [Module Λ M] [Finite M],
    StableEq ((η M).comp (η M)) 0
  η_nu : ∀ (M : Type) [AddCommGroup M] [Module Λ M] [Finite M],
    StableEq (η (nuMod M)) (nuMap (η M))
  η_syzygy : ∀ {M K : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup K] [Module Λ K] [Finite K] {P : FP}
    (j : M →ₗ[Λ] P.Mod) (q : P.Mod →ₗ[Λ] K),
    Function.Injective j → ExactAt j q → Function.Surjective q →
    ∃ τ : P ⟶ P,τ.hom.comp j = j.comp (η M) ∧ q.comp τ.hom = (η K).comp q
lemma z33 (r : ZMod 2) : r = 0 ∨ r = 1 := by revert r; decide
lemma z38 : (1 : ZMod 2) ≠ 0 := by decide
lemma z194 : (1 : ZMod 2) + 1 = 0 := by decide
lemma dualB_src (b : B) : (dualB b).src = b.tgt := rfl
lemma dualB_tgt (b : B) : (dualB b).tgt = rev b.src := rfl
def z262 (c : B) : B :=
  ⟨(rev c.tgt,c.src,⟨c.tgt.1 - c.deg.1,by
    have := c.2; dsimp [B.src,B.tgt,B.deg] at *; omega⟩),by
    have := c.2; dsimp [rev,B.src,B.tgt,B.deg] at *; omega⟩
lemma z252 (c : B) : dualB (z262 c) = c := by
  have := c.2
  rcases c with ⟨⟨⟨j,hj⟩,⟨k,hk⟩,⟨s,hs⟩⟩,hc⟩
  apply Subtype.ext
  dsimp [dualB,z262,rev,B.src,B.tgt,B.deg] at hc ⊢
  ext <;> dsimp <;> omega
lemma z315 (b : B) : z262 (dualB b) = b := by
  have := b.2
  rcases b with ⟨⟨⟨i,hi⟩,⟨j,hj⟩,⟨r,hr⟩⟩,hb⟩
  apply Subtype.ext
  dsimp [dualB,z262,rev,B.src,B.tgt,B.deg] at hb ⊢
  ext <;> dsimp <;> omega
lemma z170 : Function.Injective dualB :=
  Function.LeftInverse.injective z315
lemma dualB_nuB (b : B) : dualB (nuB b) = nuB (dualB b) := by
  have := b.2
  rcases b with ⟨⟨⟨i,hi⟩,⟨j,hj⟩,⟨r,hr⟩⟩,hb⟩
  apply Subtype.ext
  dsimp [dualB,nuB,rev,B.src,B.tgt,B.deg] at hb ⊢
  ext <;> dsimp <;> omega
lemma dualB_socB (v : Fin 5) : dualB (socB v) = eB (rev v) := by
  apply Subtype.ext
  dsimp [dualB,socB,eB,rev,B.src,B.tgt,B.deg]
  apply Prod.ext; · rfl
  apply Prod.ext; · rfl
  ext; dsimp; omega
lemma z97 {v : Fin 5} (c : Bv v) (b d : B) :
    mulB (dualB c.1) b = some d ↔ ∃ y : Bv v,mulB b y.1 = some c.1 ∧ dualB y.1 = d := by
  constructor
  · intro h
    have hd_tgt : d.tgt = rev v := by
      have hsrc := c.2
      dsimp only [mulB] at h
      split_ifs at h with hc
      · have heq := Option.some.inj h
        rw [← heq]; dsimp [B.tgt,dualB,rev] at *; rw [hsrc]
    let y : Bv v := ⟨z262 d,by
      dsimp [z262,B.src]; rw [hd_tgt,z104]⟩
    refine ⟨y,?_,z252 d⟩
    have hassoc := z151 (dualB c.1) b y.1
    rw [h,Option.bind_some] at hassoc
    have hself : mulB d y.1 = some (socB v) := by
      have h1 : mulB (dualB y.1) y.1 = some (socB y.1.src) := z131 y.1
      rw [z252 d,y.2] at h1
      exact h1
    rw [hself] at hassoc
    cases hby : mulB b y.1 with
    | none => rw [hby,Option.bind_none] at hassoc; cases hassoc
    | some c' =>
      rw [hby,Option.bind_some] at hassoc
      have hdc : dualB c.1 = dualB c' := (z150 (dualB c.1) c').mp ⟨v,hassoc.symm⟩
      have hcc : c.1 = c' := z170 hdc
      rw [hcc]
  · rintro ⟨y,hby,rfl⟩
    have hassoc := z151 (dualB c.1) b y.1
    rw [hby,Option.bind_some,z131 c.1,c.2] at hassoc
    cases hdb : mulB (dualB c.1) b with
    | none => rw [hdb,Option.bind_none] at hassoc; cases hassoc
    | some d0 =>
      rw [hdb,Option.bind_some] at hassoc
      have hd0 : d0 = dualB y.1 := (z150 d0 y.1).mp ⟨v,hassoc⟩
      rw [hd0]
lemma z196 {v : Fin 5} (c : Bv v) (b : B) {y₁ y₂ : Bv v}
    (h1 : mulB b y₁.1 = some c.1) (h2 : mulB b y₂.1 = some c.1) : y₁ = y₂ := by
  have hd1 : mulB (dualB c.1) b = some (dualB y₁.1) := (z97 c b (dualB y₁.1)).mpr ⟨y₁,h1,rfl⟩
  have hd2 : mulB (dualB c.1) b = some (dualB y₂.1) := (z97 c b (dualB y₂.1)).mpr ⟨y₂,h2,rfl⟩
  exact Subtype.ext (z170 (Option.some.inj (hd1.symm.trans hd2)))
def z16 {M : Type*} [AddCommGroup M] (r : ZMod 2) (m : M) : M :=
  if r = 0 then 0 else m
lemma z216 {M : Type*} [AddCommGroup M] (m : M) : z16 0 m = 0 := by
  simp [z16]
lemma z241 {M : Type*} [AddCommGroup M] (m : M) : z16 1 m = m := by
  simp [z16,z38]
lemma z139 {M : Type*} [AddCommGroup M] (r : ZMod 2) : z16 r (0 : M) = 0 := by
  simp [z16]
lemma z320 {M : Type*} [AddCommGroup M] (r : ZMod 2) (m n : M) :
    z16 r (m + n) = z16 r m + z16 r n := by
  by_cases hr : r = 0 <;> simp [z16,hr]
lemma z103 {M : Type*} [AddCommGroup M] [Module Λ M] (r s : ZMod 2) (m : M) :
    z16 (r + s) m = z16 r m + z16 s m := by
  rcases z33 r with rfl | rfl <;> rcases z33 s with rfl | rfl
  · simp [z16]
  · simp [z16,z38]
  · simp [z16,z38]
  · rw [z194,z216,z241,z10]
lemma z283 {M : Type*} [AddCommGroup M] (r s : ZMod 2) (m : M) :
    z16 (r * s) m = z16 r (z16 s m) := by
  rcases z33 r with rfl | rfl <;> rcases z33 s with rfl | rfl <;>
    simp [z16,z38]
lemma z125 {M : Type*} [AddCommGroup M] [Module Λ M] (a : Λ) (r : ZMod 2) (m : M) :
    a • z16 r m = z16 r (a • m) := by
  by_cases hr : r = 0 <;> simp [z16,hr]
lemma z120 {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (f : M →+ N) (r : ZMod 2) (m : M) : f (z16 r m) = z16 r (f m) := by
  by_cases hr : r = 0 <;> simp [z16,hr]
lemma z53 {M N : Type*} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (f : M →ₗ[Λ] N) (r : ZMod 2) (m : M) : f (z16 r m) = z16 r (f m) :=
  z120 f.toAddMonoidHom r m
lemma z232 (r s : ZMod 2) : z16 r s = r * s := by
  rcases z33 r with rfl | rfl <;> simp [z16,z38]
lemma z2smul_sum {ι : Type*} {M : Type*} [AddCommGroup M] (s : Finset ι) (r : ZMod 2) (f : ι → M) :
    z16 r (∑ i ∈ s,f i) = ∑ i ∈ s,z16 r (f i) := by
  by_cases hr : r = 0 <;> simp [z16,hr]
lemma z226 {ι : Type*} {M : Type*} [AddCommGroup M] [Module Λ M]
    (s : Finset ι) (r : ι → ZMod 2) (m : M) :
    z16 (∑ i ∈ s,r i) m = ∑ i ∈ s,z16 (r i) m := by
  classical
  induction s using Finset.induction with
  | empty => simp [z16]
  | insert a s ha ih => rw [Finset.sum_insert ha,Finset.sum_insert ha,z103,ih]
@[simp] lemma basisΛ_val (b c : B) : (z12 b).val c = if c = b then 1 else 0 := rfl
lemma Λ.sum_val {ι : Type*} (s : Finset ι) (f : ι → Λ) (c : B) :
    (∑ i ∈ s,f i).val c = ∑ i ∈ s,(f i).val c := by
  let ev : Λ →+ ZMod 2 := { toFun := fun x => x.val c,map_zero' := rfl,map_add' := fun _ _ => rfl }
  exact map_sum ev f s
lemma z298 (a : Λ) : a = ∑ b : B,a.val b • z12 b := by
  apply xL; ext c
  rw [Λ.sum_val,sum_eq_single c]
  · simp [z12]
  · intro b _ hb; simp [z12,Ne.symm hb]
  · intro h; exact absurd (mem_univ _) h
lemma z219 {M : Type*} [AddCommGroup M] [Module Λ M]
    (r : ZMod 2) (a : Λ) (m : M) : (r • a) • m = z16 r (a • m) := by
  rcases z33 r with rfl | rfl
  · simp [z16]
  · simp [z16,z38]
lemma z95 {M : Type*} [AddCommGroup M] [Module Λ M] (a : Λ) (m : M) :
    a • m = ∑ b : B,z16 (a.val b) (z12 b • m) := by
  conv_lhs => rw [z298 a]
  rw [Finset.sum_smul]
  refine sum_congr rfl fun b _ => z219 _ _ _
lemma z25 (b₂ b₁ : B) :
    z12 b₂ * z12 b₁ = match mulB b₂ b₁ with | some c => z12 c | none => 0 := by
  apply xL; ext d
  rw [Λ.mul_val]
  rw [sum_eq_single b₂]
  · rw [sum_eq_single b₁]
    · simp only [basisΛ_val,↓reduceIte,mul_one]
      cases h : mulB b₂ b₁ with
      | none => simp
      | some c =>
        simp only [Option.some.injEq,basisΛ_val]
        by_cases hd : d = c
        · subst hd; simp
        · simp [hd,Ne.symm hd]
    · intro y _ hy; simp [basisΛ_val,hy]
    · intro h; exact absurd (mem_univ _) h
  · intro x _ hx
    refine sum_eq_zero fun y _ => by simp [basisΛ_val,hx]
  · intro h; exact absurd (mem_univ _) h
lemma z164 (v : Fin 5) (b : B) :
    eΛ v * z12 b = if b.tgt = v then z12 b else 0 := by
  unfold eΛ
  rw [z25,z26]
  split_ifs <;> rfl
lemma z137 (b : B) (v : Fin 5) :
    z12 b * eΛ v = if v = b.src then z12 b else 0 := by
  unfold eΛ
  rw [z25,z91]
  split_ifs <;> rfl
lemma eΛ_mul_eΛ (u v : Fin 5) : eΛ u * eΛ v = if u = v then eΛ v else 0 := by
  unfold eΛ
  rw [z25,z26]
  change (match if v = u then some (eB v) else none with | some c => z12 c | none => 0) = _
  by_cases h : u = v
  · subst h; simp
  · have h' : v ≠ u := Ne.symm h; simp [h,h']
lemma z44 (v : Fin 5) : eΛ v * eΛ v = eΛ v := by
  rw [eΛ_mul_eΛ,if_pos rfl]
lemma sum_eΛ : (∑ v : Fin 5,eΛ v) = 1 := by
  apply xL; ext c
  rw [Λ.sum_val,Λ.one_val_eq_sum]
  rfl
lemma z230 (b : B) : ν (z12 b) = z12 (nuB b) := by
  apply xL; ext c
  change (z12 b).val (nuB c) = (z12 (nuB b)).val c
  simp only [basisΛ_val]
  have hiff : nuB c = b ↔ c = nuB b :=
    ⟨fun h => by rw [← z19 c,h],fun h => by rw [h,z19]⟩
  simp [hiff]
lemma ν_eΛ (v : Fin 5) : ν (eΛ v) = eΛ (rev v) := by
  unfold eΛ; rw [z230,nuB_eB]
def z45 {v : Fin 5} (b : Bv v) : Pv v := ⟨fun c => if c = b then 1 else 0⟩
@[simp] lemma basisPv_val {v : Fin 5} (b c : Bv v) :
    (z45 b).val c = if c = b then 1 else 0 := rfl
lemma Pv.sum_val {ι : Type*} {v : Fin 5} (s : Finset ι) (f : ι → Pv v) (c : Bv v) :
    (∑ i ∈ s,f i).val c = ∑ i ∈ s,(f i).val c := by
  let ev : Pv v →+ ZMod 2 := { toFun := fun x => x.val c,map_zero' := rfl,map_add' := fun _ _ => rfl }
  exact map_sum ev f s
lemma Pv.z2smul_val {v : Fin 5} (r : ZMod 2) (x : Pv v) (c : Bv v) :
    (z16 r x).val c = r * x.val c := by
  rcases z33 r with rfl | rfl <;> simp [z16,z38]
lemma z202 {v : Fin 5} (x : Pv v) :
    x = ∑ b : Bv v,z16 (x.val b) (z45 b) := by
  apply xP; ext c
  rw [Pv.sum_val,sum_eq_single c]
  · simp [Pv.z2smul_val]
  · intro b _ hb; simp [Pv.z2smul_val,Ne.symm hb]
  · intro h; exact absurd (mem_univ _) h
lemma z27 {v : Fin 5} (a : B) (b : Bv v) :
    z12 a • z45 b =
      match mulB a b.1 with
      | some c => if h : c.src = v then z45 ⟨c,h⟩ else 0
      | none => 0 := by
  apply xP; ext d
  rw [Pv.smul_val]
  rw [sum_eq_single a]
  · rw [sum_eq_single b]
    · simp only [basisΛ_val,basisPv_val,↓reduceIte,mul_one]
      cases h : mulB a b.1 with
      | none => simp
      | some c =>
        have hsrc : c.src = v := (z71 h).trans b.2
        dsimp only
        rw [dif_pos hsrc]
        simp only [Option.some.injEq,basisPv_val]
        by_cases hd : d.1 = c
        · have hd' : d = ⟨c,hsrc⟩ := Subtype.ext hd
          subst hd'; simp
        · have hd' : d ≠ ⟨c,hsrc⟩ := fun hh => hd (congrArg Subtype.val hh)
          have hcd : c ≠ d.1 := Ne.symm hd
          simp [hcd,hd']
    · intro y _ hy; simp [basisPv_val,hy]
    · intro h; exact absurd (mem_univ _) h
  · intro x _ hx
    refine sum_eq_zero fun y _ => by simp [basisΛ_val,hx]
  · intro h; exact absurd (mem_univ _) h
def genPv (v : Fin 5) : Pv v := z45 ⟨eB v,rfl⟩
lemma z24 {v : Fin 5} (b : Bv v) : z12 b.1 • genPv v = z45 b := by
  unfold genPv
  rw [z27]
  have h : mulB b.1 (eB v) = some b.1 := by rw [z91,if_pos b.2.symm]
  rw [h]; dsimp only; rw [dif_pos b.2]
lemma z79 (v : Fin 5) : eΛ v • genPv v = genPv v := by
  exact z24 (⟨eB v,rfl⟩ : Bv v)
lemma z240 {v : Fin 5} (x : Pv v) :
    x = ∑ b : Bv v,z16 (x.val b) (z12 b.1 • genPv v) := by
  conv_lhs => rw [z202 x]
  refine sum_congr rfl fun b _ => by rw [z24]
lemma z40 {v : Fin 5} (a : B) (x : Pv v) (c : Bv v) :
    (z12 a • x).val c = ∑ y : Bv v,if mulB a y.1 = some c.1 then x.val y else 0 := by
  rw [Pv.smul_val,sum_eq_single a]
  · refine sum_congr rfl fun y _ => by simp [basisΛ_val]
  · intro b _ hb; refine sum_eq_zero fun y _ => by simp [basisΛ_val,hb]
  · intro h; exact absurd (mem_univ _) h
lemma z59 {v : Fin 5} (w : Fin 5) (x : Pv v) (c : Bv v) :
    (eΛ w • x).val c = if c.1.tgt = w then x.val c else 0 := by
  unfold eΛ
  rw [z40]
  by_cases h : c.1.tgt = w
  · rw [if_pos h,sum_eq_single c]
    · rw [z26,if_pos h,if_pos rfl]
    · intro y _ hy
      rw [z26]
      by_cases hy' : y.1.tgt = w
      · rw [if_pos hy',if_neg (fun hh => hy (Subtype.ext (Option.some.inj hh)))]
      · rw [if_neg hy',if_neg (by simp)]
    · intro hn; exact absurd (mem_univ _) hn
  · rw [if_neg h]
    refine sum_eq_zero fun y _ => ?_
    rw [z26]
    by_cases hy' : y.1.tgt = w
    · rw [if_pos hy',if_neg]
      intro hh; apply h; rw [← Option.some.inj hh]; exact hy'
    · rw [if_neg hy',if_neg (by simp)]
def z29 (v : Fin 5) {M : Type} [AddCommGroup M] [Module Λ M] :
    (Pv v →ₗ[Λ] M) ≃ { m : M // eΛ v • m = m } where
  toFun f := ⟨f (genPv v),by rw [← f.map_smul,z79]⟩
  invFun m :=
    { toFun := fun x => ∑ b : Bv v,z16 (x.val b) (z12 b.1 • m.1)
      map_add' := fun x y => by
        rw [← Finset.sum_add_distrib]
        refine sum_congr rfl fun b _ => by rw [Pv.add_val,z103]
      map_smul' := fun a x => by
        simp only [RingHom.id_apply]
        conv_rhs => rw [z95 a]
        have hlhs : ∀ c : Bv v,
            z16 ((a • x).val c) (z12 c.1 • m.1) =
              ∑ p : B,∑ y : Bv v,
                if mulB p y.1 = some c.1 then z16 (a.val p * x.val y) (z12 c.1 • m.1) else 0 := by
          intro c
          rw [Pv.smul_val,z226]
          refine sum_congr rfl fun p _ => ?_
          rw [z226]
          refine sum_congr rfl fun y _ => by split_ifs <;> simp [z16]
        simp_rw [hlhs]
        calc ∑ c : Bv v,∑ p : B,∑ y : Bv v,
              (if mulB p y.1 = some c.1 then z16 (a.val p * x.val y) (z12 c.1 • m.1) else 0)
            = ∑ p : B,∑ c : Bv v,∑ y : Bv v,
              (if mulB p y.1 = some c.1 then z16 (a.val p * x.val y) (z12 c.1 • m.1) else 0) :=
              Finset.sum_comm
          _ = ∑ p : B,∑ y : Bv v,∑ c : Bv v,
              (if mulB p y.1 = some c.1 then z16 (a.val p * x.val y) (z12 c.1 • m.1) else 0) :=
              sum_congr rfl fun p _ => Finset.sum_comm
          _ = ∑ p : B,z16 (a.val p) (z12 p • ∑ y : Bv v,z16 (x.val y) (z12 y.1 • m.1)) := by
              refine sum_congr rfl fun p _ => ?_
              rw [Finset.smul_sum,z2smul_sum]
              refine sum_congr rfl fun y _ => ?_
              rw [z125,← mul_smul,z25,← z283]
              cases hpy : mulB p y.1 with
              | none =>
                simp only [zero_smul,z139]
                refine sum_eq_zero fun c _ => by simp
              | some c0 =>
                have hsrc : c0.src = v := (z71 hpy).trans y.2
                rw [sum_eq_single ⟨c0,hsrc⟩]
                · simp
                · intro c _ hc; rw [if_neg]; intro hh; exact hc (Subtype.ext (Option.some.inj hh).symm)
                · intro h; exact absurd (mem_univ _) h }
  left_inv f := by
    apply LinearMap.ext; intro x
    conv_rhs => rw [z240 x,map_sum]
    change ∑ b : Bv v,z16 (x.val b) (z12 b.1 • f (genPv v)) =
      ∑ b : Bv v,f (z16 (x.val b) (z12 b.1 • genPv v))
    refine sum_congr rfl fun b _ => ?_
    rw [z53,f.map_smul]
  right_inv m := by
    apply Subtype.ext
    dsimp [genPv]
    rw [sum_eq_single ⟨eB v,rfl⟩]
    · simp only [↓reduceIte,z241]
      exact m.2
    · intro b _ hb; simp [hb,z216]
    · intro h; exact absurd (mem_univ _) h
lemma Pv_proj (v : Fin 5) {M N : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] (g : M →ₗ[Λ] N) (hg : Function.Surjective g)
    (f : Pv v →ₗ[Λ] N) : ∃ h : Pv v →ₗ[Λ] M,g.comp h = f := by
  obtain ⟨m0,hm0⟩ := hg (f (genPv v))
  have hm : eΛ v • (eΛ v • m0) = eΛ v • m0 := by rw [← mul_smul,z44]
  refine ⟨(z29 v).symm ⟨eΛ v • m0,hm⟩,?_⟩
  apply (z29 v).injective
  apply Subtype.ext
  change g (((z29 v).symm ⟨eΛ v • m0,hm⟩) (genPv v)) = f (genPv v)
  have h1 : ((z29 v).symm ⟨eΛ v • m0,hm⟩) (genPv v) = eΛ v • m0 :=
    congrArg Subtype.val ((z29 v).apply_symm_apply ⟨eΛ v • m0,hm⟩)
  rw [h1,g.map_smul,hm0,← f.map_smul,z79]
def z118 (P : FP) (v : Fin 5) (i : Fin (P.mult v)) : Pv v →ₗ[Λ] P.Mod where
  toFun x w j := if h : w = v then (if j = Fin.cast (by rw [h]) i then h ▸ x else 0) else 0
  map_add' x y := by
    funext w j; by_cases h : w = v
    · subst h; simp only [↓reduceDIte,Fin.cast_refl,id_eq]
      by_cases hj : j = i <;> simp [hj]
    · simp [dif_neg h]
  map_smul' a x := by
    funext w j; by_cases h : w = v
    · subst h; simp only [↓reduceDIte,Fin.cast_refl,id_eq,RingHom.id_apply]
      by_cases hj : j = i <;> simp [hj]
    · simp [dif_neg h]
lemma z249 (P : FP) (x : P.Mod) :
    x = ∑ v : Fin 5,∑ i : Fin (P.mult v),z118 P v i (x v i) := by
  funext w j
  have hev : ∀ (s : Finset (Fin 5)) (F : Fin 5 → P.Mod),
      (∑ v ∈ s,F v) w j = ∑ v ∈ s,F v w j := by
    intro s F
    let ev : P.Mod →+ Pv w := { toFun := fun z => z w j,map_zero' := rfl,map_add' := fun _ _ => rfl }
    exact map_sum ev F s
  rw [hev]
  rw [sum_eq_single w]
  · let ev : P.Mod →+ Pv w := { toFun := fun z => z w j,map_zero' := rfl,map_add' := fun _ _ => rfl }
    change x w j = ev (∑ i : Fin (P.mult w),z118 P w i (x w i))
    rw [map_sum,sum_eq_single j]
    · simp [ev,z118]
    · intro i _ hi; simp [ev,z118,Ne.symm hi]
    · intro h; exact absurd (mem_univ _) h
  · intro v _ hv
    let ev : P.Mod →+ Pv w := { toFun := fun z => z w j,map_zero' := rfl,map_add' := fun _ _ => rfl }
    change ev (∑ i : Fin (P.mult v),z118 P v i (x v i)) = 0
    rw [map_sum]
    refine sum_eq_zero fun i _ => by simp [ev,z118,Ne.symm hv]
  · intro h; exact absurd (mem_univ _) h
lemma z188 (P : FP) {M N : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] (g : M →ₗ[Λ] N) (hg : Function.Surjective g)
    (f : P.Mod →ₗ[Λ] N) : ∃ h : P.Mod →ₗ[Λ] M,g.comp h = f := by
  have hlift : ∀ (v : Fin 5) (i : Fin (P.mult v)),
      ∃ h : Pv v →ₗ[Λ] M,g.comp h = f.comp (z118 P v i) :=
    fun v i => Pv_proj v g hg (f.comp (z118 P v i))
  choose hcomp hhcomp using hlift
  refine ⟨{
    toFun := fun x => ∑ v : Fin 5,∑ i : Fin (P.mult v),hcomp v i (x v i)
    map_add' := fun x y => by
      simp only [← Finset.sum_add_distrib]
      refine sum_congr rfl fun v _ => sum_congr rfl fun i _ =>
        (hcomp v i).map_add _ _
    map_smul' := fun a x => by
      simp only [RingHom.id_apply,Finset.smul_sum]
      refine sum_congr rfl fun v _ => sum_congr rfl fun i _ =>
        (hcomp v i).map_smul a _ },?_⟩
  apply LinearMap.ext; intro x
  simp only [LinearMap.comp_apply,LinearMap.coe_mk,AddHom.coe_mk,map_sum]
  conv_rhs => rw [z249 P x]
  simp only [map_sum]
  refine sum_congr rfl fun v _ => sum_congr rfl fun i _ => ?_
  exact congrArg (fun (k : Pv v →ₗ[Λ] N) => k (x v i)) (hhcomp v i)
def z31 (v : Fin 5) {M : Type} [AddCommGroup M] [Module Λ M] :
    (M →ₗ[Λ] Pv v) ≃ { ψ : M →+ ZMod 2 // ∀ m : M,ψ (eΛ (rev v) • m) = ψ m } where
  toFun f :=
    ⟨{ toFun := fun m => (f m).val ⟨socB v,rfl⟩
       map_zero' := by simp
       map_add' := fun x y => by simp },
     fun m => by
       change (f (eΛ (rev v) • m)).val ⟨socB v,rfl⟩ = (f m).val ⟨socB v,rfl⟩
       rw [f.map_smul,z59]
       have htgt : (socB v).tgt = rev v := rfl
       rw [if_pos htgt]⟩
  invFun ψ :=
    { toFun := fun m => ⟨fun c => ψ.1 (z12 (dualB c.1) • m)⟩
      map_add' := fun x y => by apply xP; ext c; simp [smul_add]
      map_smul' := fun a m => by
        apply xP; ext c
        simp only [RingHom.id_apply,Pv.smul_val]
        conv_lhs => rw [z95 a m,Finset.smul_sum]
        rw [map_sum]
        refine sum_congr rfl fun b _ => ?_
        rw [z125,z120,z232,← mul_smul,z25]
        cases hdb : mulB (dualB c.1) b with
        | none =>
          simp only [zero_smul,map_zero,mul_zero]
          symm
          refine sum_eq_zero fun y _ => ?_
          rw [if_neg]
          intro hby
          have h1 : mulB (dualB c.1) b = some (dualB y.1) :=
            (z97 c b (dualB y.1)).mpr ⟨y,hby,rfl⟩
          rw [hdb] at h1; cases h1
        | some d =>
          obtain ⟨y0,hy0_mul,hy0_dual⟩ := (z97 c b d).mp hdb
          symm
          rw [sum_eq_single y0]
          · rw [if_pos hy0_mul,hy0_dual]
          · intro y _ hy
            rw [if_neg]
            intro hby
            exact hy (z196 c b hby hy0_mul)
          · intro hn; exact absurd (mem_univ _) hn }
  left_inv f := by
    apply LinearMap.ext; intro m; apply xP; ext c
    change (f (z12 (dualB c.1) • m)).val ⟨socB v,rfl⟩ = (f m).val c
    rw [f.map_smul,z40,sum_eq_single c]
    · rcases c with ⟨c0,hc0⟩
      subst hc0
      rw [if_pos (z131 c0)]
    · intro y _ hy
      rw [if_neg]
      intro hmy
      have heq : dualB c.1 = dualB y.1 := (z150 (dualB c.1) y.1).mp ⟨v,hmy⟩
      exact hy (Subtype.ext (z170 heq).symm)
    · intro hn; exact absurd (mem_univ _) hn
  right_inv ψ := by
    apply Subtype.ext
    ext m
    change ψ.1 (z12 (dualB (socB v)) • m) = ψ.1 m
    rw [dualB_socB]
    exact ψ.2 m
structure AsZ2 (M : Type) where
  val : M
lemma AsZ2.ext {M : Type} {a b : AsZ2 M} (h : a.val = b.val) : a = b := by cases a; cases b; congr
private lemma xA {M : Type} {a b : AsZ2 M} (h : a.val = b.val) : a = b := AsZ2.ext h
instance {M : Type} [Finite M] : Finite (AsZ2 M) :=
  Finite.of_equiv M ⟨AsZ2.mk,AsZ2.val,fun _ => rfl,fun _ => rfl⟩
instance {M : Type} [AddCommGroup M] : Zero (AsZ2 M) := ⟨⟨0⟩⟩
instance {M : Type} [AddCommGroup M] : Add (AsZ2 M) := ⟨fun x y => ⟨x.val + y.val⟩⟩
instance {M : Type} [AddCommGroup M] : Neg (AsZ2 M) := ⟨fun x => ⟨-x.val⟩⟩
instance {M : Type} [AddCommGroup M] : Sub (AsZ2 M) := ⟨fun x y => ⟨x.val - y.val⟩⟩
instance {M : Type} [AddCommGroup M] : SMul ℕ (AsZ2 M) := ⟨fun n x => ⟨n • x.val⟩⟩
instance {M : Type} [AddCommGroup M] : SMul ℤ (AsZ2 M) := ⟨fun n x => ⟨n • x.val⟩⟩
instance {M : Type} [AddCommGroup M] : AddCommGroup (AsZ2 M) :=
  Function.Injective.addCommGroup AsZ2.val (fun _ _ h => AsZ2.ext h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
@[simp] lemma AsZ2.zero_val {M : Type} [AddCommGroup M] : (0 : AsZ2 M).val = 0 := rfl
@[simp] lemma AsZ2.add_val {M : Type} [AddCommGroup M] (x y : AsZ2 M) : (x + y).val = x.val + y.val := rfl
instance {M : Type} [AddCommGroup M] [Module Λ M] : Module (ZMod 2) (AsZ2 M) where
  smul r x := ⟨z16 r x.val⟩
  one_smul x := by apply xA; exact z241 x.val
  mul_smul r s x := by apply xA; exact z283 r s x.val
  smul_zero r := by apply xA; exact z139 r
  smul_add r x y := by apply xA; exact z320 r x.val y.val
  add_smul r s x := by apply xA; exact z103 r s x.val
  zero_smul x := by apply xA; exact z216 x.val
@[simp] lemma AsZ2.smul_val {M : Type} [AddCommGroup M] [Module Λ M] (r : ZMod 2) (x : AsZ2 M) :
    (r • x).val = z16 r x.val := rfl
def z338 {M : Type} [AddCommGroup M] [Module Λ M] (ψ : M →+ ZMod 2) :
    AsZ2 M →ₗ[ZMod 2] ZMod 2 where
  toFun x := ψ x.val
  map_add' x y := ψ.map_add x.val y.val
  map_smul' r x := by
    simp only [RingHom.id_apply,AsZ2.smul_val,z120,z232,smul_eq_mul]
def asZ2Lin {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (f : M →ₗ[Λ] N) : AsZ2 M →ₗ[ZMod 2] AsZ2 N where
  toFun x := ⟨f x.val⟩
  map_add' x y := by apply xA; exact f.map_add x.val y.val
  map_smul' r x := by apply xA; exact z53 f r x.val
lemma z156 {N : Type} [AddCommGroup N] [Module Λ N]
    (S : Submodule (ZMod 2) (AsZ2 N)) (φ : S →ₗ[ZMod 2] ZMod 2) :
    ∃ Φ : AsZ2 N →ₗ[ZMod 2] ZMod 2,∀ s : S,Φ s.1 = φ s := by
  obtain ⟨T,hST⟩ := Submodule.exists_isCompl S
  let p : AsZ2 N →ₗ[ZMod 2] S := S.projectionOnto T hST
  refine ⟨φ.comp p,fun s => ?_⟩
  simp only [LinearMap.comp_apply]
  congr 1
  exact Submodule.projectionOnto_apply_left hST s
lemma Pv_inj (v : Fin 5) {M N : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] (i : M →ₗ[Λ] N) (hi : Function.Injective i)
    (f : M →ₗ[Λ] Pv v) : ∃ h : N →ₗ[Λ] Pv v,h.comp i = f := by
  let ψM := z31 v f
  let iZ := asZ2Lin i
  have hiZ : Function.Injective iZ := fun x y hxy => AsZ2.ext (hi (congrArg AsZ2.val hxy))
  let eRange : AsZ2 M ≃ₗ[ZMod 2] LinearMap.range iZ := LinearEquiv.ofInjective iZ hiZ
  let φS : LinearMap.range iZ →ₗ[ZMod 2] ZMod 2 := (z338 ψM.1).comp eRange.symm.toLinearMap
  obtain ⟨Φ,hΦ⟩ := z156 (LinearMap.range iZ) φS
  let ψN0 : N →+ ZMod 2 :=
    { toFun := fun n => Φ ⟨eΛ (rev v) • n⟩
      map_zero' := by rw [smul_zero]; exact Φ.map_zero
      map_add' := fun x y => by rw [smul_add]; exact Φ.map_add ⟨eΛ (rev v) • x⟩ ⟨eΛ (rev v) • y⟩ }
  have hψN0 : ∀ n : N,ψN0 (eΛ (rev v) • n) = ψN0 n := fun n => by
    change Φ ⟨eΛ (rev v) • (eΛ (rev v) • n)⟩ = Φ ⟨eΛ (rev v) • n⟩
    rw [← mul_smul,z44]
  refine ⟨(z31 v).symm ⟨ψN0,hψN0⟩,?_⟩
  apply (z31 v).injective
  apply Subtype.ext
  ext m
  change (((z31 v).symm ⟨ψN0,hψN0⟩) (i m)).val ⟨socB v,rfl⟩ = ψM.1 m
  have h1 : (((z31 v).symm ⟨ψN0,hψN0⟩) (i m)).val ⟨socB v,rfl⟩ = ψN0 (i m) :=
    congrArg (fun (p : { ψ : N →+ ZMod 2 // _ }) => p.1 (i m))
      ((z31 v).apply_symm_apply ⟨ψN0,hψN0⟩)
  rw [h1]
  change Φ ⟨eΛ (rev v) • i m⟩ = ψM.1 m
  have hmem : (⟨eΛ (rev v) • i m⟩ : AsZ2 N) = (eRange ⟨eΛ (rev v) • m⟩).1 := by
    apply AsZ2.ext; exact (i.map_smul (eΛ (rev v)) m).symm
  rw [hmem,hΦ (eRange ⟨eΛ (rev v) • m⟩)]
  simp only [φS,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  exact ψM.2 m
lemma z217 (Q : FP) {M N : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] (i : M →ₗ[Λ] N) (hi : Function.Injective i)
    (f : M →ₗ[Λ] Q.Mod) : ∃ h : N →ₗ[Λ] Q.Mod,h.comp i = f := by
  have hlift : ∀ (v : Fin 5) (j : Fin (Q.mult v)),
      ∃ h : N →ₗ[Λ] Pv v,h.comp i =
        { toFun := fun m => f m v j
          map_add' := fun x y => by simp
          map_smul' := fun a x => by simp } :=
    fun v j => Pv_inj v i hi _
  choose hcomp hhcomp using hlift
  refine ⟨{
    toFun := fun n v j => hcomp v j n
    map_add' := fun x y => by funext v j; exact (hcomp v j).map_add x y
    map_smul' := fun a x => by funext v j; exact (hcomp v j).map_smul a x },?_⟩
  apply LinearMap.ext; intro m; funext v j
  exact congrArg (fun (k : M →ₗ[Λ] Pv v) => k m) (hhcomp v j)
lemma z248 (M : Type) [AddCommGroup M] [Module Λ M] [Finite M] :
    ∃ (P : FP) (p : P.Mod →ₗ[Λ] M),Function.Surjective p := by
  classical
  letI : Fintype M := Fintype.ofFinite M
  let e : M ≃ Fin (Fintype.card M) := Fintype.equivFin M
  let P : FP := ⟨fun _ => Fintype.card M⟩
  have he : ∀ (v : Fin 5) (i : Fin (Fintype.card M)),
      eΛ v • (eΛ v • e.symm i) = eΛ v • e.symm i := fun v i => by
    rw [← mul_smul,z44]
  let pComp (v : Fin 5) (i : Fin (Fintype.card M)) : Pv v →ₗ[Λ] M :=
    (z29 v).symm ⟨eΛ v • e.symm i,he v i⟩
  let p : P.Mod →ₗ[Λ] M :=
    { toFun := fun x => ∑ v : Fin 5,∑ i : Fin (Fintype.card M),pComp v i (x v i)
      map_add' := fun x y => by
        simp only [← Finset.sum_add_distrib]
        refine sum_congr rfl fun v _ => sum_congr rfl fun i _ =>
          (pComp v i).map_add _ _
      map_smul' := fun a x => by
        simp only [RingHom.id_apply,Finset.smul_sum]
        refine sum_congr rfl fun v _ => sum_congr rfl fun i _ =>
          (pComp v i).map_smul a _ }
  refine ⟨P,p,fun m => ?_⟩
  refine ⟨fun v i => if i = e m then genPv v else 0,?_⟩
  change ∑ v : Fin 5,∑ i : Fin (Fintype.card M),pComp v i (if i = e m then genPv v else 0) = m
  have hterm : ∀ v : Fin 5,
      (∑ i : Fin (Fintype.card M),pComp v i (if i = e m then genPv v else 0)) = eΛ v • m := by
    intro v
    rw [sum_eq_single (e m)]
    · rw [if_pos rfl]
      have h1 : pComp v (e m) (genPv v) = eΛ v • e.symm (e m) :=
        congrArg Subtype.val ((z29 v).apply_symm_apply ⟨eΛ v • e.symm (e m),he v (e m)⟩)
      rw [h1,e.symm_apply_apply]
    · intro i _ hi; rw [if_neg hi,map_zero]
    · intro h; exact absurd (mem_univ _) h
  simp_rw [hterm]
  rw [← Finset.sum_smul,sum_eΛ,one_smul]
structure eMod (v : Fin 5) (M : Type) [AddCommGroup M] [Module Λ M] where
  val : M
  prop : eΛ v • val = val
lemma eMod.ext {v : Fin 5} {M : Type} [AddCommGroup M] [Module Λ M] {a b : eMod v M} (h : a.val = b.val) : a = b := by cases a; cases b; congr
private lemma xE {v : Fin 5} {M : Type} [AddCommGroup M] [Module Λ M] {a b : eMod v M} (h : a.val = b.val) : a = b := eMod.ext h
instance {v : Fin 5} {M : Type} [AddCommGroup M] [Module Λ M] [Finite M] : Finite (eMod v M) :=
  Finite.of_injective eMod.val (fun _ _ h => eMod.ext h)
instance {v : Fin 5} {M : Type} [AddCommGroup M] [Module Λ M] : Zero (eMod v M) :=
  ⟨⟨0,smul_zero _⟩⟩
instance {v : Fin 5} {M : Type} [AddCommGroup M] [Module Λ M] : Add (eMod v M) :=
  ⟨fun x y => ⟨x.val + y.val,by rw [smul_add,x.prop,y.prop]⟩⟩
instance {v : Fin 5} {M : Type} [AddCommGroup M] [Module Λ M] : Neg (eMod v M) :=
  ⟨fun x => ⟨-x.val,by rw [smul_neg,x.prop]⟩⟩
instance {v : Fin 5} {M : Type} [AddCommGroup M] [Module Λ M] : Sub (eMod v M) :=
  ⟨fun x y => ⟨x.val - y.val,by rw [smul_sub,x.prop,y.prop]⟩⟩
instance {v : Fin 5} {M : Type} [AddCommGroup M] [Module Λ M] : SMul ℕ (eMod v M) :=
  ⟨fun n x => ⟨n • x.val,by rw [smul_comm,x.prop]⟩⟩
instance {v : Fin 5} {M : Type} [AddCommGroup M] [Module Λ M] : SMul ℤ (eMod v M) :=
  ⟨fun n x => ⟨n • x.val,by rw [smul_comm,x.prop]⟩⟩
instance {v : Fin 5} {M : Type} [AddCommGroup M] [Module Λ M] : AddCommGroup (eMod v M) :=
  Function.Injective.addCommGroup eMod.val (fun _ _ h => eMod.ext h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
@[simp] lemma eMod.zero_val {v : Fin 5} {M : Type} [AddCommGroup M] [Module Λ M] :
    (0 : eMod v M).val = 0 := rfl
@[simp] lemma eMod.add_val {v : Fin 5} {M : Type} [AddCommGroup M] [Module Λ M]
    (x y : eMod v M) : (x + y).val = x.val + y.val := rfl
instance {v : Fin 5} {M : Type} [AddCommGroup M] [Module Λ M] : Module (ZMod 2) (eMod v M) where
  smul r x := ⟨z16 r x.val,by rw [z125,x.prop]⟩
  one_smul x := by apply xE; exact z241 x.val
  mul_smul r s x := by apply xE; exact z283 r s x.val
  smul_zero r := by apply xE; exact z139 r
  smul_add r x y := by apply xE; exact z320 r x.val y.val
  add_smul r s x := by apply xE; exact z103 r s x.val
  zero_smul x := by apply xE; exact z216 x.val
@[simp] lemma eMod.smul_val {v : Fin 5} {M : Type} [AddCommGroup M] [Module Λ M]
    (r : ZMod 2) (x : eMod v M) : (r • x).val = z16 r x.val := rfl
def z158 (v : Fin 5) {M N : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] (f : M →ₗ[Λ] N) :
    eMod v M →ₗ[ZMod 2] eMod v N where
  toFun x := ⟨f x.val,by rw [← f.map_smul,x.prop]⟩
  map_add' x y := by apply xE; exact f.map_add x.val y.val
  map_smul' r x := by apply xE; exact z53 f r x.val
lemma z136 (v : Fin 5) {U Y X : Type} [AddCommGroup U] [Module Λ U]
    [AddCommGroup Y] [Module Λ Y] [AddCommGroup X] [Module Λ X]
    (w : U →ₗ[Λ] Y) (z : Y →ₗ[Λ] X)
    (hw : Function.Injective w) (hex : ExactAt w z) (hz : Function.Surjective z) :
    Function.Injective (z158 v w) ∧
      LinearMap.range (z158 v w) = LinearMap.ker (z158 v z) ∧
      Function.Surjective (z158 v z) := by
  refine ⟨fun x y hxy => eMod.ext (hw (congrArg eMod.val hxy)),?_,?_⟩
  · ext y
    simp only [LinearMap.mem_range,LinearMap.mem_ker]
    constructor
    · rintro ⟨u,rfl⟩
      apply eMod.ext
      have hmem : w u.val ∈ LinearMap.ker z := by
        rw [← hex]; exact ⟨u.val,rfl⟩
      exact hmem
    · intro hy
      have hyz : y.val ∈ LinearMap.range w := by
        rw [hex]; exact congrArg eMod.val hy
      obtain ⟨u0,hu0⟩ := hyz
      refine ⟨⟨eΛ v • u0,by rw [← mul_smul,z44]⟩,?_⟩
      apply eMod.ext
      change w (eΛ v • u0) = y.val
      rw [w.map_smul,hu0,y.prop]
  · intro x
    obtain ⟨y0,hy0⟩ := hz x.val
    refine ⟨⟨eΛ v • y0,by rw [← mul_smul,z44]⟩,?_⟩
    apply eMod.ext
    change z (eΛ v • y0) = x.val
    rw [z.map_smul,hy0,x.prop]
structure FiberMod (V : Fin 5 → Type) where
  val : (v : Fin 5) → Bv v → V v
lemma FiberMod.ext {V : Fin 5 → Type} {a b : FiberMod V} (h : a.val = b.val) : a = b := by cases a; cases b; congr
private lemma xM {V : Fin 5 → Type} {a b : FiberMod V} (h : a.val = b.val) : a = b := FiberMod.ext h
instance {V : Fin 5 → Type} [∀ v,AddCommGroup (V v)] : Zero (FiberMod V) := ⟨⟨0⟩⟩
instance {V : Fin 5 → Type} [∀ v,AddCommGroup (V v)] : Add (FiberMod V) := ⟨fun x y => ⟨x.val + y.val⟩⟩
instance {V : Fin 5 → Type} [∀ v,AddCommGroup (V v)] : Neg (FiberMod V) := ⟨fun x => ⟨-x.val⟩⟩
instance {V : Fin 5 → Type} [∀ v,AddCommGroup (V v)] : Sub (FiberMod V) := ⟨fun x y => ⟨x.val - y.val⟩⟩
instance {V : Fin 5 → Type} [∀ v,AddCommGroup (V v)] : SMul ℕ (FiberMod V) := ⟨fun n x => ⟨n • x.val⟩⟩
instance {V : Fin 5 → Type} [∀ v,AddCommGroup (V v)] : SMul ℤ (FiberMod V) := ⟨fun n x => ⟨n • x.val⟩⟩
instance {V : Fin 5 → Type} [∀ v,AddCommGroup (V v)] : AddCommGroup (FiberMod V) :=
  Function.Injective.addCommGroup FiberMod.val (fun _ _ h => FiberMod.ext h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
@[simp] lemma FiberMod.zero_val {V : Fin 5 → Type} [∀ v,AddCommGroup (V v)] (v : Fin 5) (c : Bv v) :
    (0 : FiberMod V).val v c = 0 := rfl
@[simp] lemma FiberMod.add_val {V : Fin 5 → Type} [∀ v,AddCommGroup (V v)]
    (x y : FiberMod V) (v : Fin 5) (c : Bv v) :
    (x + y).val v c = x.val v c + y.val v c := rfl
instance {V : Fin 5 → Type} [∀ v,AddCommGroup (V v)] [∀ v,Module (ZMod 2) (V v)] :
    Module Λ (FiberMod V) where
  smul a x := ⟨fun v c => ∑ b : B,∑ y : Bv v,if mulB b y.1 = some c.1 then a.val b • x.val v y else 0⟩
  one_smul x := by
    apply xM; ext v c
    change ∑ b : B,∑ y : Bv v,
      (if mulB b y.1 = some c.1 then (1 : Λ).val b • x.val v y else 0) = x.val v c
    rw [sum_eq_single (eB c.1.tgt)]
    · rw [sum_eq_single c]
      · rw [z26,if_pos rfl,if_pos rfl,Λ.one_val_eq_sum]
        rw [sum_eq_single c.1.tgt]
        · simp
        · intro w _ hw; rw [if_neg]; intro h; exact hw (congrArg B.src h).symm
        · intro h; exact absurd (mem_univ _) h
      · intro y _ hy
        rw [z26]
        by_cases h1 : y.1.tgt = c.1.tgt
        · rw [if_pos h1,if_neg (fun hh => hy (Subtype.ext (Option.some.inj hh)))]
        · rw [if_neg h1,if_neg (by simp)]
      · intro h; exact absurd (mem_univ _) h
    · intro b _ hb
      refine sum_eq_zero fun y _ => ?_
      rw [Λ.one_val_eq_sum]
      by_cases h1 : ∃ w : Fin 5,b = eB w
      · obtain ⟨w,rfl⟩ := h1
        rw [z26]
        by_cases h2 : y.1.tgt = w
        · rw [if_pos h2,if_neg]
          intro hh; have hyeq := Option.some.inj hh; apply hb; rw [← hyeq,h2]
        · rw [if_neg h2,if_neg (by simp)]
      · push Not at h1
        have h0 : (∑ w : Fin 5,if b = eB w then (1 : ZMod 2) else 0) = 0 :=
          sum_eq_zero fun w _ => if_neg (h1 w)
        simp [h0]
    · intro h; exact absurd (mem_univ _) h
  mul_smul a b x := by
    apply xM; ext v c
    change ∑ ab : B,∑ y : Bv v,
        (if mulB ab y.1 = some c.1 then
          (∑ p : B,∑ q : B,if mulB p q = some ab then a.val p * b.val q else 0) • x.val v y
        else 0) =
      ∑ p : B,∑ qy : Bv v,
        (if mulB p qy.1 = some c.1 then
          a.val p • (∑ q : B,∑ y : Bv v,if mulB q y.1 = some qy.1 then b.val q • x.val v y else 0)
        else 0)
    have hlhs :
        ∑ ab : B,∑ y : Bv v,
          (if mulB ab y.1 = some c.1 then
            (∑ p : B,∑ q : B,if mulB p q = some ab then a.val p * b.val q else 0) • x.val v y
          else 0) =
        ∑ p : B,∑ q : B,∑ y : Bv v,
          if (mulB p q).bind (fun ab => mulB ab y.1) = some c.1 then (a.val p * b.val q) • x.val v y else 0 := by
      calc _ = ∑ ab : B,∑ y : Bv v,∑ p : B,∑ q : B,
            if mulB ab y.1 = some c.1 ∧ mulB p q = some ab then (a.val p * b.val q) • x.val v y else 0 := by
            refine sum_congr rfl fun ab _ => sum_congr rfl fun y _ => ?_
            by_cases h1 : mulB ab y.1 = some c.1
            · rw [if_pos h1,Finset.sum_smul]
              refine sum_congr rfl fun p _ => ?_
              rw [Finset.sum_smul]
              refine sum_congr rfl fun q _ => ?_
              by_cases h2 : mulB p q = some ab
              · rw [if_pos h2,if_pos ⟨h1,h2⟩]
              · rw [if_neg h2,if_neg (fun hh => h2 hh.2),zero_smul]
            · rw [if_neg h1]
              symm; refine sum_eq_zero fun p _ => sum_eq_zero fun q _ => ?_
              rw [if_neg (fun hh => h1 hh.1)]
        _ = ∑ p : B,∑ q : B,∑ y : Bv v,∑ ab : B,
            if mulB ab y.1 = some c.1 ∧ mulB p q = some ab then (a.val p * b.val q) • x.val v y else 0 := by
            calc _ = ∑ ab : B,∑ p : B,∑ y : Bv v,∑ q : B,
                  if mulB ab y.1 = some c.1 ∧ mulB p q = some ab then (a.val p * b.val q) • x.val v y else 0 := by
                  refine sum_congr rfl fun ab _ => Finset.sum_comm
              _ = ∑ p : B,∑ ab : B,∑ y : Bv v,∑ q : B,
                  if mulB ab y.1 = some c.1 ∧ mulB p q = some ab then (a.val p * b.val q) • x.val v y else 0 :=
                  Finset.sum_comm
              _ = ∑ p : B,∑ ab : B,∑ q : B,∑ y : Bv v,
                  if mulB ab y.1 = some c.1 ∧ mulB p q = some ab then (a.val p * b.val q) • x.val v y else 0 := by
                  refine sum_congr rfl fun p _ => sum_congr rfl fun ab _ => Finset.sum_comm
              _ = ∑ p : B,∑ q : B,∑ ab : B,∑ y : Bv v,
                  if mulB ab y.1 = some c.1 ∧ mulB p q = some ab then (a.val p * b.val q) • x.val v y else 0 := by
                  refine sum_congr rfl fun p _ => Finset.sum_comm
              _ = _ := by
                  refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => Finset.sum_comm
        _ = _ := by
            refine sum_congr rfl fun p _ => sum_congr rfl fun q _ =>
              sum_congr rfl fun y _ => ?_
            cases hpq : mulB p q with
            | none =>
              simp only [Option.bind_none,reduceCtorEq,↓reduceIte]
              refine sum_eq_zero fun ab _ => ?_
              rw [if_neg]; rintro ⟨_,h⟩; simp at h
            | some ab0 =>
              simp only [Option.bind_some,Option.some.injEq]
              rw [sum_eq_single ab0]
              · simp
              · intro ab _ hne; rw [if_neg]; rintro ⟨_,h⟩; exact hne h.symm
              · intro h; exact absurd (mem_univ _) h
    have hrhs :
        ∑ p : B,∑ qy : Bv v,
          (if mulB p qy.1 = some c.1 then
            a.val p • (∑ q : B,∑ y : Bv v,if mulB q y.1 = some qy.1 then b.val q • x.val v y else 0)
          else 0) =
        ∑ p : B,∑ q : B,∑ y : Bv v,
          if (mulB q y.1).bind (fun qy => mulB p qy) = some c.1 then (a.val p * b.val q) • x.val v y else 0 := by
      calc _ = ∑ p : B,∑ qy : Bv v,∑ q : B,∑ y : Bv v,
            if mulB p qy.1 = some c.1 ∧ mulB q y.1 = some qy.1 then (a.val p * b.val q) • x.val v y else 0 := by
            refine sum_congr rfl fun p _ => sum_congr rfl fun qy _ => ?_
            by_cases h1 : mulB p qy.1 = some c.1
            · rw [if_pos h1,Finset.smul_sum]
              refine sum_congr rfl fun q _ => ?_
              rw [Finset.smul_sum]
              refine sum_congr rfl fun y _ => ?_
              by_cases h2 : mulB q y.1 = some qy.1
              · rw [if_pos h2,if_pos ⟨h1,h2⟩,mul_smul]
              · rw [if_neg h2,if_neg (fun hh => h2 hh.2),smul_zero]
            · rw [if_neg h1]
              symm; refine sum_eq_zero fun q _ => sum_eq_zero fun y _ => ?_
              rw [if_neg (fun hh => h1 hh.1)]
        _ = ∑ p : B,∑ q : B,∑ y : Bv v,∑ qy : Bv v,
            if mulB p qy.1 = some c.1 ∧ mulB q y.1 = some qy.1 then (a.val p * b.val q) • x.val v y else 0 := by
            refine sum_congr rfl fun p _ => ?_
            rw [Finset.sum_comm]
            refine sum_congr rfl fun q _ => Finset.sum_comm
        _ = _ := by
            refine sum_congr rfl fun p _ => sum_congr rfl fun q _ =>
              sum_congr rfl fun y _ => ?_
            cases hqy : mulB q y.1 with
            | none =>
              simp only [Option.bind_none,reduceCtorEq,↓reduceIte]
              refine sum_eq_zero fun qy _ => ?_
              rw [if_neg]; rintro ⟨_,h⟩; simp at h
            | some qy0 =>
              simp only [Option.bind_some,Option.some.injEq]
              have hsrc : qy0.src = v := (z71 hqy).trans y.2
              rw [sum_eq_single ⟨qy0,hsrc⟩]
              · simp
              · intro qy _ hne; rw [if_neg]; rintro ⟨_,h⟩; exact hne (Subtype.ext h.symm)
              · intro h; exact absurd (mem_univ _) h
    rw [hlhs,hrhs]
    refine sum_congr rfl fun p _ => sum_congr rfl fun q _ =>
      sum_congr rfl fun y _ => by rw [z151]
  smul_zero a := by
    apply xM; ext v c
    change ∑ b : B,∑ y : Bv v,(if mulB b y.1 = some c.1 then a.val b • (0 : V v) else 0) = 0
    simp
  smul_add a x y := by
    apply xM; ext v c
    change ∑ b : B,∑ z : Bv v,(if mulB b z.1 = some c.1 then a.val b • (x.val v z + y.val v z) else 0) =
      (∑ b : B,∑ z : Bv v,if mulB b z.1 = some c.1 then a.val b • x.val v z else 0) +
      (∑ b : B,∑ z : Bv v,if mulB b z.1 = some c.1 then a.val b • y.val v z else 0)
    rw [← Finset.sum_add_distrib]
    refine sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_add_distrib]
    refine sum_congr rfl fun z _ => by split_ifs <;> simp [smul_add]
  add_smul a b x := by
    apply xM; ext v c
    change ∑ p : B,∑ z : Bv v,(if mulB p z.1 = some c.1 then (a.val p + b.val p) • x.val v z else 0) =
      (∑ p : B,∑ z : Bv v,if mulB p z.1 = some c.1 then a.val p • x.val v z else 0) +
      (∑ p : B,∑ z : Bv v,if mulB p z.1 = some c.1 then b.val p • x.val v z else 0)
    rw [← Finset.sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib]
    refine sum_congr rfl fun z _ => by split_ifs <;> simp [add_smul]
  zero_smul x := by
    apply xM; ext v c
    change ∑ b : B,∑ y : Bv v,(if mulB b y.1 = some c.1 then (0 : Λ).val b • x.val v y else 0) = 0
    simp
lemma FiberMod.smul_val {V : Fin 5 → Type} [∀ v,AddCommGroup (V v)] [∀ v,Module (ZMod 2) (V v)]
    (a : Λ) (x : FiberMod V) (v : Fin 5) (c : Bv v) :
    (a • x).val v c = ∑ b : B,∑ y : Bv v,if mulB b y.1 = some c.1 then a.val b • x.val v y else 0 := rfl
noncomputable def z22 (V : Fin 5 → Type) [∀ v,AddCommGroup (V v)]
    [∀ v,Module (ZMod 2) (V v)] : FP :=
  ⟨fun v => Module.finrank (ZMod 2) (V v)⟩
noncomputable def z197 (V : Fin 5 → Type) [∀ v,AddCommGroup (V v)]
    [∀ v,Module (ZMod 2) (V v)] [∀ v,Finite (V v)] :
    (z22 V).Mod ≃ₗ[Λ] FiberMod V :=
  let bas (v : Fin 5) : Module.Basis (Fin ((z22 V).mult v)) (ZMod 2) (V v) :=
    Module.finBasis (ZMod 2) (V v)
  { toFun := fun p => ⟨fun v c => ∑ i : Fin ((z22 V).mult v),(p v i).val c • bas v i⟩
    invFun := fun f v i => ⟨fun c => (bas v).repr (f.val v c) i⟩
    left_inv := fun p => by
      funext v i; apply xP; ext c
      change (bas v).repr (∑ j,(p v j).val c • bas v j) i = (p v i).val c
      rw [map_sum]
      simp only [LinearEquiv.map_smul,Finsupp.coe_finset_sum,Finset.sum_apply,
        Finsupp.coe_smul,Pi.smul_apply,smul_eq_mul,Module.Basis.repr_self,
        Finsupp.single_apply]
      rw [sum_eq_single i]
      · simp
      · intro j _ hj; simp [hj]
      · intro h; exact absurd (mem_univ _) h
    right_inv := fun f => by
      apply xM; ext v c
      change (∑ i,((bas v).repr (f.val v c) i) • bas v i) = f.val v c
      exact (bas v).sum_repr (f.val v c)
    map_add' := fun p q => by
      apply xM; ext v c
      change (∑ i,((p v i).val c + (q v i).val c) • bas v i) =
        (∑ i,(p v i).val c • bas v i) + (∑ i,(q v i).val c • bas v i)
      rw [← Finset.sum_add_distrib]
      refine sum_congr rfl fun i _ => add_smul _ _ _
    map_smul' := fun a p => by
      apply xM; ext v c
      simp only [RingHom.id_apply,FiberMod.smul_val]
      change (∑ i,(∑ b : B,∑ y : Bv v,
          if mulB b y.1 = some c.1 then a.val b * (p v i).val y else 0) • bas v i) =
        ∑ b : B,∑ y : Bv v,
          if mulB b y.1 = some c.1 then a.val b • ∑ i,(p v i).val y • bas v i else 0
      calc _ = ∑ i,∑ b : B,∑ y : Bv v,
            (if mulB b y.1 = some c.1 then (a.val b * (p v i).val y) • bas v i else 0) := by
            refine sum_congr rfl fun i _ => ?_
            rw [Finset.sum_smul]
            refine sum_congr rfl fun b _ => ?_
            rw [Finset.sum_smul]
            refine sum_congr rfl fun y _ => by split_ifs <;> simp
        _ = ∑ b : B,∑ i,∑ y : Bv v,
            (if mulB b y.1 = some c.1 then (a.val b * (p v i).val y) • bas v i else 0) :=
            Finset.sum_comm
        _ = ∑ b : B,∑ y : Bv v,∑ i,
            (if mulB b y.1 = some c.1 then (a.val b * (p v i).val y) • bas v i else 0) :=
            sum_congr rfl fun b _ => Finset.sum_comm
        _ = _ := by
            refine sum_congr rfl fun b _ => sum_congr rfl fun y _ => ?_
            by_cases h : mulB b y.1 = some c.1
            · rw [if_pos h,Finset.smul_sum]
              refine sum_congr rfl fun i _ => by rw [if_pos h,mul_smul]
            · rw [if_neg h]; refine sum_eq_zero fun i _ => by rw [if_neg h] }
def z261 {V W : Fin 5 → Type} [∀ v,AddCommGroup (V v)] [∀ v,Module (ZMod 2) (V v)]
    [∀ v,AddCommGroup (W v)] [∀ v,Module (ZMod 2) (W v)]
    (φ : ∀ v : Fin 5,V v →ₗ[ZMod 2] W v) : FiberMod V →ₗ[Λ] FiberMod W where
  toFun f := ⟨fun v c => φ v (f.val v c)⟩
  map_add' f g := by apply xM; ext v c; exact (φ v).map_add _ _
  map_smul' a f := by
    apply xM; ext v c
    simp only [RingHom.id_apply,FiberMod.smul_val,map_sum]
    refine sum_congr rfl fun b _ => sum_congr rfl fun y _ => ?_
    split_ifs
    · exact (φ v).map_smul _ _
    · exact (φ v).map_zero
lemma z250 {U V W : Fin 5 → Type}
    [∀ v,AddCommGroup (U v)] [∀ v,Module (ZMod 2) (U v)]
    [∀ v,AddCommGroup (V v)] [∀ v,Module (ZMod 2) (V v)]
    [∀ v,AddCommGroup (W v)] [∀ v,Module (ZMod 2) (W v)]
    (φ : ∀ v : Fin 5,U v →ₗ[ZMod 2] V v) (ψ : ∀ v : Fin 5,V v →ₗ[ZMod 2] W v)
    (h : ∀ v : Fin 5,Function.Injective (φ v) ∧ LinearMap.range (φ v) = LinearMap.ker (ψ v) ∧
      Function.Surjective (ψ v)) :
    Function.Injective (z261 φ) ∧ ExactAt (z261 φ) (z261 ψ) ∧
      Function.Surjective (z261 ψ) := by
  refine ⟨fun x y hxy => FiberMod.ext (funext fun v => funext fun c =>
      (h v).1 (congrArg (fun (z : FiberMod V) => z.val v c) hxy)),?_,?_⟩
  · ext y
    simp only [LinearMap.mem_range,LinearMap.mem_ker]
    constructor
    · rintro ⟨x,rfl⟩
      apply xM; ext v c
      have hmem : φ v (x.val v c) ∈ LinearMap.ker (ψ v) := by
        rw [← (h v).2.1]; exact ⟨x.val v c,rfl⟩
      exact hmem
    · intro hy
      have hex : ∀ (v : Fin 5) (c : Bv v),∃ u : U v,φ v u = y.val v c := fun v c => by
        have hmem : y.val v c ∈ LinearMap.range (φ v) := by
          rw [(h v).2.1]
          exact congrArg (fun (z : FiberMod W) => z.val v c) hy
        exact hmem
      choose u hu using hex
      refine ⟨⟨u⟩,by apply xM; ext v c; exact hu v c⟩
  · intro w
    have hex : ∀ (v : Fin 5) (c : Bv v),∃ y : V v,ψ v y = w.val v c :=
      fun v c => (h v).2.2 (w.val v c)
    choose y hy using hex
    refine ⟨⟨y⟩,by apply xM; ext v c; exact hy v c⟩
def mkB (i j r : Fin 5) (h : j.1 ≤ i.1 + r.1 ∧ r.1 ≤ j.1 ∧ i.1 + r.1 < 5) : B :=
  ⟨(i,j,r),h⟩
def arrB : Fin 8 → B
  | ⟨0,_⟩ => mkB 0 1 1 (by decide)
  | ⟨1,_⟩ => mkB 1 2 1 (by decide)
  | ⟨2,_⟩ => mkB 2 3 1 (by decide)
  | ⟨3,_⟩ => mkB 3 4 1 (by decide)
  | ⟨4,_⟩ => mkB 1 0 0 (by decide)
  | ⟨5,_⟩ => mkB 2 1 0 (by decide)
  | ⟨6,_⟩ => mkB 3 2 0 (by decide)
  | ⟨7,_⟩ => mkB 4 3 0 (by decide)
def z82 (k : Fin 8) : Fin 8 := ⟨(k.1 + 4) % 8,by omega⟩
def nuArr (k : Fin 8) : Fin 8 := ⟨7 - k.1,by omega⟩
lemma z159 : ∀ k : Fin 8,(arrB (z82 k)).src = (arrB k).tgt := by decide
lemma z239 : ∀ k : Fin 8,(arrB (z82 k)).tgt = (arrB k).src := by decide
lemma z337 : ∀ k : Fin 8,arrB (nuArr k) = nuB (arrB k) := by decide
lemma nuArr_nuArr : ∀ k : Fin 8,nuArr (nuArr k) = k := by decide
abbrev I1 := { p : Fin 8 × B // (arrB p.1).tgt = p.2.src }
def mkI1 (k : Fin 8) (c : B) (h : (arrB k).tgt = c.src) : I1 := ⟨(k,c),h⟩
def nuI1 (p : I1) : I1 :=
  ⟨(nuArr p.1.1,nuB p.1.2),by
    rw [z337]
    change rev (arrB p.1.1).tgt = rev p.1.2.src
    rw [p.2]⟩
lemma z360 (p : I1) : nuI1 (nuI1 p) = p := by
  apply Subtype.ext; apply Prod.ext
  · exact nuArr_nuArr p.1.1
  · exact z19 p.1.2
def allB : List B :=
  (List.finRange 5).flatMap fun i =>
    (List.finRange 5).flatMap fun j =>
      (List.finRange 5).filterMap fun r =>
        if h : j.1 ≤ i.1 + r.1 ∧ r.1 ≤ j.1 ∧ i.1 + r.1 < 5 then some ⟨(i,j,r),h⟩ else none
lemma allB_nodup : allB.Nodup := by decide
lemma z35 : ∀ b : B,b ∈ allB := by decide
def z147 {α : Type} [DecidableEq α] (le : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
    if x = y then ys
    else if le x y then x :: y :: ys
    else y :: z147 le x ys
def z9 {α : Type} [DecidableEq α] (le : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => z147 le x (z9 le xs)
def z49 {J : Type} [DecidableEq J] {M : Type} [AddCommGroup M] [Module Λ M]
    (m : M) (p : J × B) (j : J) : M :=
  if j = p.1 then z12 p.2 • m else 0
def z8 {J : Type} [DecidableEq J] {M : Type} [AddCommGroup M] [Module Λ M]
    (m : M) : List (J × B) → (J → M)
  | [] => 0
  | p :: ps => z49 m p + z8 m ps
def z4 {I J : Type} [Fintype I] [DecidableEq J] {M : Type} [AddCommGroup M] [Module Λ M]
    (op : I → List (J × B)) (x : I → M) : J → M :=
  ∑ i : I,z8 (x i) (op i)
def z106 {I J K : Type} (op2 : J → List (K × B)) (op1 : I → List (J × B)) (i : I) :
    List (K × B) :=
  (op1 i).flatMap fun p =>
    (op2 p.1).filterMap fun q =>
      (mulB q.2 p.2).map fun a21 => (q.1,a21)
lemma z132 {J : Type} [DecidableEq J] {M : Type} [AddCommGroup M] [Module Λ M]
    (m : M) (L1 L2 : List (J × B)) :
    z8 m (L1 ++ L2) = z8 m L1 + z8 m L2 := by
  induction L1 with
  | nil => simp [z8]
  | cons p ps ih => simp [z8,ih,add_assoc]
lemma z225 {J : Type} [DecidableEq J] {M : Type} [AddCommGroup M] [Module Λ M]
    (le : (J × B) → (J × B) → Bool) (m : M) (p : J × B) (L : List (J × B)) :
    z8 m (z147 le p L) = z49 m p + z8 m L := by
  induction L with
  | nil => simp [z147,z8]
  | cons q qs ih =>
    unfold z147
    by_cases hpq : p = q
    · subst hpq
      rw [if_pos rfl]
      funext j
      change z8 m qs j = z49 m p j + (z49 m p j + z8 m qs j)
      rw [← add_assoc,z10,zero_add]
    · rw [if_neg hpq]
      by_cases hle : le p q = true
      · rw [if_pos hle]; rfl
      · rw [if_neg hle]
        simp only [z8,ih]
        funext j; exact add_left_comm _ _ _
lemma z81 {J : Type} [DecidableEq J] {M : Type} [AddCommGroup M] [Module Λ M]
    (le : (J × B) → (J × B) → Bool) (m : M) (L : List (J × B)) :
    z8 m (z9 le L) = z8 m L := by
  induction L with
  | nil => rfl
  | cons p ps ih => simp [z9,z225,z8,ih]
lemma z119 {J : Type} [DecidableEq J] {M : Type} [AddCommGroup M] [Module Λ M]
    (L : List (J × B)) : z8 (0 : M) L = 0 := by
  induction L with
  | nil => rfl
  | cons p ps ih =>
    simp only [z8,ih,add_zero]
    funext j; simp [z49]
lemma z354 {J : Type} [DecidableEq J] {M : Type} [AddCommGroup M] [Module Λ M]
    (m n : M) (L : List (J × B)) :
    z8 (m + n) L = z8 m L + z8 n L := by
  induction L with
  | nil => simp [z8]
  | cons p ps ih =>
    simp only [z8,ih]
    funext j
    have hterm : z49 (m + n) p j = z49 m p j + z49 n p j := by
      unfold z49; split_ifs <;> simp [smul_add]
    simp only [Pi.add_apply,hterm]; abel
lemma z107 {I J : Type} [Fintype I] [DecidableEq J] {M : Type}
    [AddCommGroup M] [Module Λ M] (op : I → List (J × B)) (x y : I → M) :
    z4 op (x + y) = z4 op x + z4 op y := by
  unfold z4
  rw [← Finset.sum_add_distrib]
  refine sum_congr rfl fun i _ => z354 (x i) (y i) (op i)
lemma z304 {ι I J : Type} [Fintype I] [DecidableEq J] {M : Type}
    [AddCommGroup M] [Module Λ M] (op : I → List (J × B)) (s : Finset ι) (F : ι → I → M) :
    z4 op (∑ k ∈ s,F k) = ∑ k ∈ s,z4 op (F k) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    unfold z4
    refine sum_eq_zero fun i _ => z119 (op i)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha,z107,ih]
lemma z172 {I J : Type} [Fintype I] [DecidableEq J] {M : Type}
    [AddCommGroup M] [Module Λ M] (op1 op2 : I → List (J × B)) (x : I → M) :
    z4 op1 x + z4 op2 x = z4 (fun i => op1 i ++ op2 i) x := by
  unfold z4
  rw [← Finset.sum_add_distrib]
  refine sum_congr rfl fun i _ => (z132 (x i) (op1 i) (op2 i)).symm
lemma z278 {J K : Type} [Fintype J] [DecidableEq J] [DecidableEq K]
    {M : Type} [AddCommGroup M] [Module Λ M]
    (op2 : J → List (K × B)) (m : M) (p : J × B) :
    z4 op2 (z49 m p) =
      z8 m ((op2 p.1).filterMap fun q => (mulB q.2 p.2).map fun a21 => (q.1,a21)) := by
  unfold z4
  rw [sum_eq_single p.1]
  · simp only [z49,↓reduceIte]
    induction op2 p.1 with
    | nil => rfl
    | cons q qs ih =>
      simp only [z8,List.filterMap_cons,ih]
      cases hmul : mulB q.2 p.2 with
      | none =>
        simp only [Option.map_none,zero_add]
        funext k
        simp only [Pi.add_apply,z49]
        have h0 : z12 q.2 • (z12 p.2 • m) = 0 := by
          rw [← mul_smul,z25,hmul,zero_smul]
        split_ifs <;> simp [h0]
      | some a21 =>
        simp only [Option.map_some,z8]
        funext k
        simp only [Pi.add_apply,z49]
        have h1 : z12 q.2 • (z12 p.2 • m) = z12 a21 • m := by
          rw [← mul_smul,z25,hmul]
        split_ifs <;> simp [h1]
  · intro j _ hj
    have h0 : z49 m p j = 0 := if_neg hj
    rw [h0,z119]
  · intro h; exact absurd (mem_univ _) h
lemma z279 {J K : Type} [Fintype J] [DecidableEq J] [DecidableEq K]
    {M : Type} [AddCommGroup M] [Module Λ M]
    (op2 : J → List (K × B)) (m : M) (L : List (J × B)) :
    z4 op2 (z8 m L) =
      z8 m (L.flatMap fun p =>
        (op2 p.1).filterMap fun q => (mulB q.2 p.2).map fun a21 => (q.1,a21)) := by
  induction L with
  | nil =>
    simp only [z8,List.flatMap_nil]
    unfold z4
    refine sum_eq_zero fun j _ => z119 (op2 j)
  | cons p ps ih =>
    simp only [z8,List.flatMap_cons,z107,z132,
      z278,ih]
lemma z46 {I J K : Type} [Fintype I] [Fintype J] [DecidableEq J] [DecidableEq K]
    {M : Type} [AddCommGroup M] [Module Λ M]
    (op2 : J → List (K × B)) (op1 : I → List (J × B)) (x : I → M) :
    z4 op2 (z4 op1 x) = z4 (z106 op2 op1) x := by
  change z4 op2 (∑ i : I,z8 (x i) (op1 i)) = ∑ i : I,z8 (x i) (z106 op2 op1 i)
  rw [z304]
  refine sum_congr rfl fun i _ => z279 op2 (x i) (op1 i)
lemma z20 {I J : Type} [Fintype I] [DecidableEq J]
    {M : Type} [AddCommGroup M] [Module Λ M] (le : (J × B) → (J × B) → Bool)
    (op1 op2 : I → List (J × B)) (h : ∀ i,z9 le (op1 i) = z9 le (op2 i))
    (x : I → M) : z4 op1 x = z4 op2 x := by
  unfold z4
  refine sum_congr rfl fun i _ => by
    rw [← z81 le (x i) (op1 i),h i,z81 le (x i) (op2 i)]
lemma z191 {I J : Type} [Fintype I] [DecidableEq J] {M : Type}
    [AddCommGroup M] [Module Λ M] (x : I → M) :
    z4 (fun (_ : I) => ([] : List (J × B))) x = 0 := by
  unfold z4; simp [z8]
lemma z213 {I : Type} [Fintype I] [DecidableEq I] {M : Type}
    [AddCommGroup M] [Module Λ M] (v : I → Fin 5) (x : I → M)
    (hx : ∀ i,eΛ (v i) • x i = x i) :
    z4 (fun i => [(i,eB (v i))]) x = x := by
  funext j
  unfold z4
  rw [Finset.sum_apply,sum_eq_single j]
  · simp only [z8,Pi.add_apply,Pi.zero_apply,add_zero,z49,↓reduceIte]
    exact hx j
  · intro i _ hi
    simp only [z8,Pi.add_apply,Pi.zero_apply,add_zero,z49,if_neg (Ne.symm hi)]
  · intro h; exact absurd (mem_univ _) h
lemma z171 {M : Type} [AddCommGroup M] [Module Λ M] (x : Unit → M) :
    z4 (fun (_ : Unit) => (List.finRange 5).map fun v => ((),eB v)) x = x := by
  funext u
  rcases u with ⟨⟩
  unfold z4
  rw [Finset.sum_apply,sum_eq_single ()]
  · have hlist : ∀ (L : List (Fin 5)),
        z8 (x ()) (L.map fun v => ((),eB v)) () =
          (L.map fun v => eΛ v • x ()).sum := by
      intro L; induction L with
      | nil => rfl
      | cons v vs ih => simp [z8,z49,eΛ,ih]
    rw [hlist]
    have hfin : ((List.finRange 5).map fun v => eΛ v • x ()).sum = ∑ v : Fin 5,eΛ v • x () := by
      rw [← Fin.sum_univ_def]
    rw [hfin,← Finset.sum_smul,sum_eΛ,one_smul]
  · intro i _ hi; cases i; exact absurd rfl hi
  · intro h; exact absurd (mem_univ _) h
lemma z86 {I J : Type} [Fintype I] [DecidableEq J] {M : Type}
    [AddCommGroup M] [Module Λ M] (op : I → List (J × B)) (vt : J → Fin 5)
    (hvt : ∀ i : I,∀ p ∈ op i,p.2.tgt = vt p.1) (x : I → M) (j : J) :
    eΛ (vt j) • z4 op x j = z4 op x j := by
  unfold z4
  rw [Finset.sum_apply,Finset.smul_sum]
  refine sum_congr rfl fun i _ => ?_
  have hL : ∀ (L : List (J × B)),(∀ p ∈ L,p.2.tgt = vt p.1) →
      eΛ (vt j) • z8 (x i) L j = z8 (x i) L j := by
    intro L hLmem
    induction L with
    | nil => simp [z8]
    | cons p ps ih =>
      simp only [z8,Pi.add_apply,smul_add]
      congr 1
      · unfold z49
        by_cases hj : j = p.1
        · rw [if_pos hj,← mul_smul,z164,
            if_pos ((hLmem p List.mem_cons_self).trans (congrArg vt hj.symm))]
        · rw [if_neg hj,smul_zero]
      · exact ih fun q hq => hLmem q (List.mem_cons_of_mem p hq)
  exact hL (op i) (hvt i)
lemma z122 {I J : Type} [Fintype I] [DecidableEq J]
    {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (op : I → List (J × B)) (f : M →ₗ[Λ] N) (x : I → M) (j : J) :
    f (z4 op x j) = z4 op (fun i => f (x i)) j := by
  unfold z4
  rw [Finset.sum_apply,Finset.sum_apply,map_sum]
  refine sum_congr rfl fun i _ => ?_
  induction op i with
  | nil => simp [z8]
  | cons p ps ih =>
    simp only [z8,Pi.add_apply,map_add,ih]
    congr 1
    unfold z49
    split_ifs <;> simp
def leB (a b : B) : Bool :=
  a.1.1.1 < b.1.1.1 ||
    (a.1.1.1 == b.1.1.1 && (a.1.2.1.1 < b.1.2.1.1 ||
      (a.1.2.1.1 == b.1.2.1.1 && a.1.2.2.1 ≤ b.1.2.2.1)))
def leI1 (p q : I1) : Bool :=
  p.1.1.1 < q.1.1.1 || (p.1.1.1 == q.1.1.1 && leB p.1.2 q.1.2)
def z300 (_ _ : Unit) : Bool := true
def z77 {α β : Type} [DecidableEq α] (leA : α → α → Bool) (leB' : β → β → Bool)
    (x y : α × β) : Bool :=
  if x.1 = y.1 then leB' x.2 y.2 else leA x.1 y.1
def z101 (_ : Unit) : List (B × B) :=
  allB.map fun c => (c,dualB c)
def d0Col (c : B) : List (I1 × B) :=
  (List.finRange 8).flatMap fun k =>
    if h : (arrB k).src = c.src then
      (match hm : mulB c (arrB (z82 k)) with
       | some xb =>
         [(⟨(k,xb),by
             have h1 := z71 hm
             rw [h1,z159]⟩,eB (rev c.src))]
       | none => []) ++
      [(⟨(z82 k,c),(z239 k).trans h⟩,nuB (arrB k))]
    else []
def d1Col (p : I1) : List (B × B) :=
  (match mulB p.1.2 (arrB p.1.1) with
   | some xar => [(xar,eB (rev (arrB p.1.1).src))]
   | none => []) ++
  [(p.1.2,nuB (arrB p.1.1))]
def piCol (c : B) : List (Unit × B) := [((),nuB c)]
def s2Col (_ : Unit) : List (B × B) :=
  (List.finRange 5).map fun v => (eB v,eB (rev v))
def z285 (c : B) : List (Unit × B) :=
  match c.1.1.1,c.1.2.1.1,c.1.2.2.1 with
  | 0,4,4 => [((),mkB 4 4 0 (by decide))]
  | 1,3,3 => [((),mkB 3 3 0 (by decide))]
  | 2,2,2 => [((),mkB 2 2 0 (by decide))]
  | 3,1,1 => [((),mkB 1 1 0 (by decide))]
  | 4,0,0 => [((),mkB 0 0 0 (by decide))]
  | _,_,_ => []
def s1Col (c : B) : List (I1 × B) :=
  match c.1.1.1,c.1.2.1.1,c.1.2.2.1 with
  | 0,1,1 => [(mkI1 0 (mkB 1 1 0 (by decide)) (by decide),mkB 4 4 0 (by decide))]
  | 0,2,2 => [(mkI1 0 (mkB 1 2 1 (by decide)) (by decide),mkB 4 4 0 (by decide)),(mkI1 1 (mkB 2 2 0 (by decide)) (by decide),mkB 4 3 0 (by decide))]
  | 0,3,3 => [(mkI1 0 (mkB 1 3 2 (by decide)) (by decide),mkB 4 4 0 (by decide)),(mkI1 1 (mkB 2 3 1 (by decide)) (by decide),mkB 4 3 0 (by decide)),(mkI1 2 (mkB 3 3 0 (by decide)) (by decide),mkB 4 2 0 (by decide))]
  | 0,4,4 => [(mkI1 0 (mkB 1 4 3 (by decide)) (by decide),mkB 4 4 0 (by decide)),(mkI1 1 (mkB 2 4 2 (by decide)) (by decide),mkB 4 3 0 (by decide)),(mkI1 2 (mkB 3 4 1 (by decide)) (by decide),mkB 4 2 0 (by decide)),(mkI1 3 (mkB 4 4 0 (by decide)) (by decide),mkB 4 1 0 (by decide))]
  | 1,0,0 => [(mkI1 4 (mkB 0 0 0 (by decide)) (by decide),mkB 3 3 0 (by decide))]
  | 1,1,1 => [(mkI1 0 (mkB 1 1 0 (by decide)) (by decide),mkB 3 4 1 (by decide)),(mkI1 4 (mkB 0 1 1 (by decide)) (by decide),mkB 3 3 0 (by decide))]
  | 1,2,1 => [(mkI1 1 (mkB 2 2 0 (by decide)) (by decide),mkB 3 3 0 (by decide))]
  | 1,2,2 => [(mkI1 0 (mkB 1 2 1 (by decide)) (by decide),mkB 3 4 1 (by decide)),(mkI1 1 (mkB 2 2 0 (by decide)) (by decide),mkB 3 3 1 (by decide)),(mkI1 4 (mkB 0 2 2 (by decide)) (by decide),mkB 3 3 0 (by decide))]
  | 1,3,2 => [(mkI1 1 (mkB 2 3 1 (by decide)) (by decide),mkB 3 3 0 (by decide)),(mkI1 2 (mkB 3 3 0 (by decide)) (by decide),mkB 3 2 0 (by decide))]
  | 1,3,3 => [(mkI1 0 (mkB 1 3 2 (by decide)) (by decide),mkB 3 4 1 (by decide)),(mkI1 1 (mkB 2 3 1 (by decide)) (by decide),mkB 3 3 1 (by decide)),(mkI1 2 (mkB 3 3 0 (by decide)) (by decide),mkB 3 2 1 (by decide)),(mkI1 4 (mkB 0 3 3 (by decide)) (by decide),mkB 3 3 0 (by decide))]
  | 1,4,3 => [(mkI1 1 (mkB 2 4 2 (by decide)) (by decide),mkB 3 3 0 (by decide)),(mkI1 2 (mkB 3 4 1 (by decide)) (by decide),mkB 3 2 0 (by decide)),(mkI1 3 (mkB 4 4 0 (by decide)) (by decide),mkB 3 1 0 (by decide))]
  | 2,0,0 => [(mkI1 4 (mkB 0 0 0 (by decide)) (by decide),mkB 2 3 1 (by decide)),(mkI1 5 (mkB 1 0 0 (by decide)) (by decide),mkB 2 2 0 (by decide))]
  | 2,1,0 => [(mkI1 5 (mkB 1 1 0 (by decide)) (by decide),mkB 2 2 0 (by decide))]
  | 2,1,1 => [(mkI1 0 (mkB 1 1 0 (by decide)) (by decide),mkB 2 4 2 (by decide)),(mkI1 4 (mkB 0 1 1 (by decide)) (by decide),mkB 2 3 1 (by decide)),(mkI1 5 (mkB 1 1 1 (by decide)) (by decide),mkB 2 2 0 (by decide))]
  | 2,2,1 => [(mkI1 1 (mkB 2 2 0 (by decide)) (by decide),mkB 2 3 1 (by decide)),(mkI1 5 (mkB 1 2 1 (by decide)) (by decide),mkB 2 2 0 (by decide))]
  | 2,2,2 => [(mkI1 0 (mkB 1 2 1 (by decide)) (by decide),mkB 2 4 2 (by decide)),(mkI1 1 (mkB 2 2 0 (by decide)) (by decide),mkB 2 3 2 (by decide)),(mkI1 4 (mkB 0 2 2 (by decide)) (by decide),mkB 2 3 1 (by decide)),(mkI1 5 (mkB 1 2 2 (by decide)) (by decide),mkB 2 2 0 (by decide))]
  | 2,3,1 => [(mkI1 2 (mkB 3 3 0 (by decide)) (by decide),mkB 2 2 0 (by decide))]
  | 2,3,2 => [(mkI1 1 (mkB 2 3 1 (by decide)) (by decide),mkB 2 3 1 (by decide)),(mkI1 2 (mkB 3 3 0 (by decide)) (by decide),mkB 2 2 1 (by decide)),(mkI1 5 (mkB 1 3 2 (by decide)) (by decide),mkB 2 2 0 (by decide))]
  | 2,4,2 => [(mkI1 2 (mkB 3 4 1 (by decide)) (by decide),mkB 2 2 0 (by decide)),(mkI1 3 (mkB 4 4 0 (by decide)) (by decide),mkB 2 1 0 (by decide))]
  | 3,0,0 => [(mkI1 4 (mkB 0 0 0 (by decide)) (by decide),mkB 1 3 2 (by decide)),(mkI1 5 (mkB 1 0 0 (by decide)) (by decide),mkB 1 2 1 (by decide)),(mkI1 6 (mkB 2 0 0 (by decide)) (by decide),mkB 1 1 0 (by decide))]
  | 3,1,0 => [(mkI1 5 (mkB 1 1 0 (by decide)) (by decide),mkB 1 2 1 (by decide)),(mkI1 6 (mkB 2 1 0 (by decide)) (by decide),mkB 1 1 0 (by decide))]
  | 3,1,1 => [(mkI1 0 (mkB 1 1 0 (by decide)) (by decide),mkB 1 4 3 (by decide)),(mkI1 4 (mkB 0 1 1 (by decide)) (by decide),mkB 1 3 2 (by decide)),(mkI1 5 (mkB 1 1 1 (by decide)) (by decide),mkB 1 2 1 (by decide)),(mkI1 6 (mkB 2 1 1 (by decide)) (by decide),mkB 1 1 0 (by decide))]
  | 3,2,0 => [(mkI1 6 (mkB 2 2 0 (by decide)) (by decide),mkB 1 1 0 (by decide))]
  | 3,2,1 => [(mkI1 1 (mkB 2 2 0 (by decide)) (by decide),mkB 1 3 2 (by decide)),(mkI1 5 (mkB 1 2 1 (by decide)) (by decide),mkB 1 2 1 (by decide)),(mkI1 6 (mkB 2 2 1 (by decide)) (by decide),mkB 1 1 0 (by decide))]
  | 3,3,1 => [(mkI1 2 (mkB 3 3 0 (by decide)) (by decide),mkB 1 2 1 (by decide)),(mkI1 6 (mkB 2 3 1 (by decide)) (by decide),mkB 1 1 0 (by decide))]
  | 3,4,1 => [(mkI1 3 (mkB 4 4 0 (by decide)) (by decide),mkB 1 1 0 (by decide))]
  | 4,0,0 => [(mkI1 4 (mkB 0 0 0 (by decide)) (by decide),mkB 0 3 3 (by decide)),(mkI1 5 (mkB 1 0 0 (by decide)) (by decide),mkB 0 2 2 (by decide)),(mkI1 6 (mkB 2 0 0 (by decide)) (by decide),mkB 0 1 1 (by decide)),(mkI1 7 (mkB 3 0 0 (by decide)) (by decide),mkB 0 0 0 (by decide))]
  | 4,1,0 => [(mkI1 5 (mkB 1 1 0 (by decide)) (by decide),mkB 0 2 2 (by decide)),(mkI1 6 (mkB 2 1 0 (by decide)) (by decide),mkB 0 1 1 (by decide)),(mkI1 7 (mkB 3 1 0 (by decide)) (by decide),mkB 0 0 0 (by decide))]
  | 4,2,0 => [(mkI1 6 (mkB 2 2 0 (by decide)) (by decide),mkB 0 1 1 (by decide)),(mkI1 7 (mkB 3 2 0 (by decide)) (by decide),mkB 0 0 0 (by decide))]
  | 4,3,0 => [(mkI1 7 (mkB 3 3 0 (by decide)) (by decide),mkB 0 0 0 (by decide))]
  | _,_,_ => []
def s0Col (p : I1) : List (B × B) :=
  match p.1.1.1,p.1.2.1.1.1,p.1.2.1.2.1.1,p.1.2.1.2.2.1 with
  | 0,1,0,0 => [(mkB 0 0 0 (by decide),mkB 4 4 0 (by decide))]
  | 0,1,1,1 => [(mkB 0 1 1 (by decide),mkB 4 4 0 (by decide))]
  | 0,1,2,2 => [(mkB 0 2 2 (by decide),mkB 4 4 0 (by decide))]
  | 0,1,3,3 => [(mkB 0 3 3 (by decide),mkB 4 4 0 (by decide))]
  | 1,2,0,0 => [(mkB 0 0 0 (by decide),mkB 3 4 1 (by decide)),(mkB 1 0 0 (by decide),mkB 3 3 0 (by decide))]
  | 1,2,1,0 => [(mkB 1 1 0 (by decide),mkB 3 3 0 (by decide))]
  | 1,2,1,1 => [(mkB 0 1 1 (by decide),mkB 3 4 1 (by decide)),(mkB 1 1 1 (by decide),mkB 3 3 0 (by decide))]
  | 1,2,2,1 => [(mkB 1 2 1 (by decide),mkB 3 3 0 (by decide))]
  | 1,2,2,2 => [(mkB 0 2 2 (by decide),mkB 3 4 1 (by decide)),(mkB 1 2 2 (by decide),mkB 3 3 0 (by decide))]
  | 1,2,3,2 => [(mkB 1 3 2 (by decide),mkB 3 3 0 (by decide))]
  | 2,3,0,0 => [(mkB 0 0 0 (by decide),mkB 2 4 2 (by decide)),(mkB 1 0 0 (by decide),mkB 2 3 1 (by decide)),(mkB 2 0 0 (by decide),mkB 2 2 0 (by decide))]
  | 2,3,1,0 => [(mkB 1 1 0 (by decide),mkB 2 3 1 (by decide)),(mkB 2 1 0 (by decide),mkB 2 2 0 (by decide))]
  | 2,3,1,1 => [(mkB 0 1 1 (by decide),mkB 2 4 2 (by decide)),(mkB 1 1 1 (by decide),mkB 2 3 1 (by decide)),(mkB 2 1 1 (by decide),mkB 2 2 0 (by decide))]
  | 2,3,2,0 => [(mkB 2 2 0 (by decide),mkB 2 2 0 (by decide))]
  | 2,3,2,1 => [(mkB 1 2 1 (by decide),mkB 2 3 1 (by decide)),(mkB 2 2 1 (by decide),mkB 2 2 0 (by decide))]
  | 2,3,3,1 => [(mkB 2 3 1 (by decide),mkB 2 2 0 (by decide))]
  | 3,4,0,0 => [(mkB 0 0 0 (by decide),mkB 1 4 3 (by decide)),(mkB 1 0 0 (by decide),mkB 1 3 2 (by decide)),(mkB 2 0 0 (by decide),mkB 1 2 1 (by decide)),(mkB 3 0 0 (by decide),mkB 1 1 0 (by decide))]
  | 3,4,1,0 => [(mkB 1 1 0 (by decide),mkB 1 3 2 (by decide)),(mkB 2 1 0 (by decide),mkB 1 2 1 (by decide)),(mkB 3 1 0 (by decide),mkB 1 1 0 (by decide))]
  | 3,4,2,0 => [(mkB 2 2 0 (by decide),mkB 1 2 1 (by decide)),(mkB 3 2 0 (by decide),mkB 1 1 0 (by decide))]
  | 3,4,3,0 => [(mkB 3 3 0 (by decide),mkB 1 1 0 (by decide))]
  | 4,0,4,4 => [(mkB 1 4 3 (by decide),mkB 3 3 0 (by decide)),(mkB 2 4 2 (by decide),mkB 3 2 0 (by decide)),(mkB 3 4 1 (by decide),mkB 3 1 0 (by decide)),(mkB 4 4 0 (by decide),mkB 3 0 0 (by decide))]
  | 5,1,3,3 => [(mkB 1 3 2 (by decide),mkB 2 3 1 (by decide)),(mkB 2 3 1 (by decide),mkB 2 2 1 (by decide)),(mkB 2 3 2 (by decide),mkB 2 2 0 (by decide)),(mkB 3 3 0 (by decide),mkB 2 1 1 (by decide)),(mkB 3 3 1 (by decide),mkB 2 1 0 (by decide)),(mkB 4 3 0 (by decide),mkB 2 0 0 (by decide))]
  | 5,1,4,3 => [(mkB 2 4 2 (by decide),mkB 2 2 0 (by decide)),(mkB 3 4 1 (by decide),mkB 2 1 0 (by decide)),(mkB 4 4 0 (by decide),mkB 2 0 0 (by decide))]
  | 6,2,2,2 => [(mkB 1 2 1 (by decide),mkB 1 3 2 (by decide)),(mkB 2 2 0 (by decide),mkB 1 2 2 (by decide)),(mkB 2 2 1 (by decide),mkB 1 2 1 (by decide)),(mkB 3 2 0 (by decide),mkB 1 1 1 (by decide)),(mkB 3 2 1 (by decide),mkB 1 1 0 (by decide)),(mkB 4 2 0 (by decide),mkB 1 0 0 (by decide))]
  | 6,2,3,2 => [(mkB 2 3 1 (by decide),mkB 1 2 1 (by decide)),(mkB 3 3 0 (by decide),mkB 1 1 1 (by decide)),(mkB 3 3 1 (by decide),mkB 1 1 0 (by decide)),(mkB 4 3 0 (by decide),mkB 1 0 0 (by decide))]
  | 6,2,4,2 => [(mkB 3 4 1 (by decide),mkB 1 1 0 (by decide)),(mkB 4 4 0 (by decide),mkB 1 0 0 (by decide))]
  | 7,3,1,1 => [(mkB 1 1 0 (by decide),mkB 0 3 3 (by decide)),(mkB 2 1 0 (by decide),mkB 0 2 2 (by decide)),(mkB 3 1 0 (by decide),mkB 0 1 1 (by decide)),(mkB 4 1 0 (by decide),mkB 0 0 0 (by decide))]
  | 7,3,2,1 => [(mkB 2 2 0 (by decide),mkB 0 2 2 (by decide)),(mkB 3 2 0 (by decide),mkB 0 1 1 (by decide)),(mkB 4 2 0 (by decide),mkB 0 0 0 (by decide))]
  | 7,3,3,1 => [(mkB 3 3 0 (by decide),mkB 0 1 1 (by decide)),(mkB 4 3 0 (by decide),mkB 0 0 0 (by decide))]
  | 7,3,4,1 => [(mkB 4 4 0 (by decide),mkB 0 0 0 (by decide))]
  | _,_,_,_ => []
lemma iotaCol_tgt : ∀ u : Unit,∀ p ∈ z101 u,p.2.tgt = rev p.1.src := by decide
lemma d0Col_tgt : ∀ c : B,∀ p ∈ d0Col c,p.2.tgt = rev (arrB p.1.1.1).src := by decide
lemma d1Col_tgt : ∀ q : I1,∀ p ∈ d1Col q,p.2.tgt = rev p.1.src := by decide
lemma s2Col_tgt : ∀ u : Unit,∀ p ∈ s2Col u,p.2.tgt = rev p.1.src := by decide
lemma s1Col_tgt : ∀ c : B,∀ p ∈ s1Col c,p.2.tgt = rev (arrB p.1.1.1).src := by decide
lemma s0Col_tgt : ∀ q : I1,∀ p ∈ s0Col q,p.2.tgt = rev p.1.src := by decide
def allI1 : List I1 :=
  (List.finRange 8).flatMap fun k =>
    allB.filterMap fun c =>
      if h : (arrB k).tgt = c.src then some ⟨(k,c),h⟩ else none
lemma z310 (p : I1) : p ∈ allI1 := by
  unfold allI1
  rw [List.mem_flatMap]
  refine ⟨p.1.1,List.mem_finRange _,?_⟩
  rw [List.mem_filterMap]
  exact ⟨p.1.2,z35 p.1.2,by rw [dif_pos p.2]⟩
lemma check_pi_s2 :
    ∀ u : Unit,z9 (z77 z300 leB) (z106 piCol s2Col u) =
      z9 (z77 z300 leB) ((List.finRange 5).map fun v => ((),eB v)) := by decide
lemma z210 :
    allB.all (fun c =>
      z9 (z77 leB leB) (z106 d1Col s1Col c ++ z106 s2Col piCol c) ==
      z9 (z77 leB leB) [(c,eB (rev c.src))]) = true := by decide
lemma z276 (c : B) :
    z9 (z77 leB leB) (z106 d1Col s1Col c ++ z106 s2Col piCol c) =
      z9 (z77 leB leB) [(c,eB (rev c.src))] :=
  beq_iff_eq.mp (List.all_eq_true.mp z210 c (z35 c))
lemma z211 :
    allI1.all (fun p =>
      z9 (z77 leI1 leB) (z106 d0Col s0Col p ++ z106 s1Col d1Col p) ==
      z9 (z77 leI1 leB) [(p,eB (rev (arrB p.1.1).src))]) = true := by decide
lemma z277 (p : I1) :
    z9 (z77 leI1 leB) (z106 d0Col s0Col p ++ z106 s1Col d1Col p) =
      z9 (z77 leI1 leB) [(p,eB (rev (arrB p.1.1).src))] :=
  beq_iff_eq.mp (List.all_eq_true.mp z211 p (z310 p))
lemma z181 :
    allB.all (fun c =>
      z9 (z77 leB leB) (z106 z101 z285 c ++ z106 s0Col d0Col c) ==
      z9 (z77 leB leB) [(c,eB (rev c.src))]) = true := by decide
lemma z238 (c : B) :
    z9 (z77 leB leB) (z106 z101 z285 c ++ z106 s0Col d0Col c) =
      z9 (z77 leB leB) [(c,eB (rev c.src))] :=
  beq_iff_eq.mp (List.all_eq_true.mp z181 c (z35 c))
lemma z255 :
    ∀ u : Unit,z9 (z77 z300 leB) (z106 z285 z101 u) =
      z9 (z77 z300 leB) ((List.finRange 5).map fun v => ((),eB v)) := by decide
lemma z289 :
    allI1.all (fun p => z9 (z77 z300 leB) (z106 piCol d1Col p) == []) = true := by decide
lemma check_pi_d1 (p : I1) :
    z9 (z77 z300 leB) (z106 piCol d1Col p) = [] :=
  beq_iff_eq.mp (List.all_eq_true.mp z289 p (z310 p))
lemma z294 :
    allB.all (fun c => z9 (z77 leB leB) (z106 d1Col d0Col c) == []) = true := by decide
lemma check_d1_d0 (c : B) :
    z9 (z77 leB leB) (z106 d1Col d0Col c) = [] :=
  beq_iff_eq.mp (List.all_eq_true.mp z294 c (z35 c))
lemma z335 :
    ∀ u : Unit,z9 (z77 leI1 leB) (z106 d0Col z101 u) = [] := by decide
lemma z295 :
    allB.all (fun c =>
      z9 (z77 leI1 leB) ((d0Col c).map fun (p,a) => (nuI1 p,nuB a)) ==
      z9 (z77 leI1 leB) (d0Col (nuB c))) = true := by decide
lemma check_d0_nu (c : B) :
    z9 (z77 leI1 leB) ((d0Col c).map fun (p,a) => (nuI1 p,nuB a)) =
      z9 (z77 leI1 leB) (d0Col (nuB c)) :=
  beq_iff_eq.mp (List.all_eq_true.mp z295 c (z35 c))
lemma z293 :
    allI1.all (fun p =>
      z9 (z77 leB leB) ((d1Col p).map fun (c,a) => (nuB c,nuB a)) ==
      z9 (z77 leB leB) (d1Col (nuI1 p))) = true := by decide
lemma check_d1_nu (p : I1) :
    z9 (z77 leB leB) ((d1Col p).map fun (c,a) => (nuB c,nuB a)) =
      z9 (z77 leB leB) (d1Col (nuI1 p)) :=
  beq_iff_eq.mp (List.all_eq_true.mp z293 p (z310 p))
abbrev V0 (M : Type) [AddCommGroup M] [Module Λ M] (v : Fin 5) : Type := eMod (rev v) M
abbrev V1 (M : Type) [AddCommGroup M] [Module Λ M] (v : Fin 5) : Type :=
  (ar : { k : Fin 8 // (arrB k).tgt = v }) → eMod (rev (arrB ar.1).src) M
abbrev F0 (M : Type) [AddCommGroup M] [Module Λ M] : Type := FiberMod (V0 M)
abbrev F1 (M : Type) [AddCommGroup M] [Module Λ M] : Type := FiberMod (V1 M)
def z23 {M : Type} [AddCommGroup M] [Module Λ M] (f : F0 M) (c : B) : M :=
  (f.val c.src ⟨c,rfl⟩).val
lemma z126 {M : Type} [AddCommGroup M] [Module Λ M] (f : F0 M) (c : B) :
    eΛ (rev c.src) • z23 f c = z23 f c :=
  (f.val c.src ⟨c,rfl⟩).prop
def z345 {M : Type} [AddCommGroup M] [Module Λ M] (g : B → M)
    (hg : ∀ c,eΛ (rev c.src) • g c = g c) : F0 M :=
  ⟨fun v c => ⟨g c.1,by rcases c with ⟨c0,rfl⟩; exact hg c0⟩⟩
lemma z78 {M : Type} [AddCommGroup M] [Module Λ M] (g : B → M)
    (hg : ∀ c,eΛ (rev c.src) • g c = g c) : z23 (z345 g hg) = g := rfl
lemma z267 {M : Type} [AddCommGroup M] [Module Λ M] (f : F0 M) :
    z345 (z23 f) (z126 f) = f := by
  apply xM; ext v c; rcases c with ⟨c0,rfl⟩; rfl
lemma z14 {M : Type} [AddCommGroup M] [Module Λ M] :
    Function.Injective (z23 (M := M)) := fun f g h => by
  rw [← z267 f,← z267 g]
  apply xM; ext v c; apply xE; exact congrArg (fun k => k c.1) h
lemma z284 {M : Type} [AddCommGroup M] [Module Λ M] (f g : F0 M) :
    z23 (f + g) = z23 f + z23 g := rfl
lemma z51 {M : Type} [AddCommGroup M] [Module Λ M] (b : B) (f : F0 M) (c : B) :
    z23 (z12 b • f) c = ∑ y : B,if mulB b y = some c then z23 f y else 0 := by
  change (∑ p : B,∑ y : Bv c.src,
    if mulB p y.1 = some c then (z12 b).val p • f.val c.src y else 0).val = _
  rw [sum_eq_single b]
  · simp only [basisΛ_val,↓reduceIte,one_smul]
    let ev : eMod (rev c.src) M →+ M :=
      { toFun := eMod.val,map_zero' := rfl,map_add' := fun _ _ => rfl }
    change ev (∑ y : Bv c.src,if mulB b y.1 = some c then f.val c.src y else 0) = _
    rw [map_sum]
    symm
    rw [← Finset.sum_filter]
    have hsub : ∀ y : Bv c.src,
        ev (if mulB b y.1 = some c then f.val c.src y else 0) =
          if mulB b y.1 = some c then z23 f y.1 else 0 := by
      rintro ⟨y0,hy0⟩
      have hcast : ∀ {w : Fin 5} (hw : y0.src = w),(f.val w ⟨y0,hw⟩).val = z23 f y0 := by
        intro w hw; subst hw; rfl
      by_cases h : mulB b y0 = some c
      · rw [if_pos h,if_pos h]; exact hcast hy0
      · rw [if_neg h,if_neg h]; rfl
    simp_rw [hsub]
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun y hy => ⟨y,(z71 (Finset.mem_filter.mp hy).2).symm⟩)
      (fun y hy => Finset.mem_filter.mpr ⟨mem_univ _,(Finset.mem_filter.mp hy).2⟩)
      (fun _ _ _ _ h => congrArg Subtype.val h)
      (fun y hy => ⟨y.1,Finset.mem_filter.mpr ⟨mem_univ _,(Finset.mem_filter.mp hy).2⟩,rfl⟩)
      (fun _ _ => rfl)
  · intro p _ hp
    refine sum_eq_zero fun y _ => by simp [basisΛ_val,hp]
  · intro h; exact absurd (mem_univ _) h
def z47 {M : Type} [AddCommGroup M] [Module Λ M] (f : F1 M) (p : I1) : M :=
  (f.val p.1.2.src ⟨p.1.2,rfl⟩ ⟨p.1.1,p.2⟩).val
lemma z146 {M : Type} [AddCommGroup M] [Module Λ M] (f : F1 M) (p : I1) :
    eΛ (rev (arrB p.1.1).src) • z47 f p = z47 f p :=
  (f.val p.1.2.src ⟨p.1.2,rfl⟩ ⟨p.1.1,p.2⟩).prop
def ofFun1 {M : Type} [AddCommGroup M] [Module Λ M] (g : I1 → M)
    (hg : ∀ p : I1,eΛ (rev (arrB p.1.1).src) • g p = g p) : F1 M :=
  ⟨fun v c ar => ⟨g ⟨(ar.1,c.1),ar.2.trans c.2.symm⟩,hg ⟨(ar.1,c.1),ar.2.trans c.2.symm⟩⟩⟩
lemma z162 {M : Type} [AddCommGroup M] [Module Λ M] (g : I1 → M)
    (hg : ∀ p : I1,eΛ (rev (arrB p.1.1).src) • g p = g p) : z47 (ofFun1 g hg) = g := rfl
lemma z266 {M : Type} [AddCommGroup M] [Module Λ M] (f : F1 M) :
    ofFun1 (z47 f) (z146 f) = f := by
  apply xM; ext v c ar; rcases c with ⟨c0,rfl⟩; rfl
lemma z37 {M : Type} [AddCommGroup M] [Module Λ M] :
    Function.Injective (z47 (M := M)) := fun f g h => by
  rw [← z266 f,← z266 g]
  apply xM; ext v c ar; apply xE; exact congrArg (fun k => k ⟨(ar.1,c.1),ar.2.trans c.2.symm⟩) h
lemma z321 {M : Type} [AddCommGroup M] [Module Λ M] (f g : F1 M) :
    z47 (f + g) = z47 f + z47 g := rfl
lemma z73 {M : Type} [AddCommGroup M] [Module Λ M] (b : B) (f : F1 M) (p : I1) :
    z47 (z12 b • f) p =
      ∑ y : Bv p.1.2.src,if mulB b y.1 = some p.1.2 then
        z47 f ⟨(p.1.1,y.1),p.2.trans y.2.symm⟩ else 0 := by
  change ((∑ q : B,∑ y : Bv p.1.2.src,
    if mulB q y.1 = some p.1.2 then (z12 b).val q • f.val p.1.2.src y else 0) ⟨p.1.1,p.2⟩).val = _
  rw [sum_eq_single b]
  · simp only [basisΛ_val,↓reduceIte,one_smul]
    let ev : V1 M p.1.2.src →+ M :=
      { toFun := fun z => (z ⟨p.1.1,p.2⟩).val,map_zero' := rfl,map_add' := fun _ _ => rfl }
    change ev (∑ y : Bv p.1.2.src,if mulB b y.1 = some p.1.2 then f.val p.1.2.src y else 0) = _
    rw [map_sum]
    refine sum_congr rfl fun y _ => ?_
    rcases y with ⟨y0,hy0⟩
    by_cases h : mulB b y0 = some p.1.2
    · rw [if_pos h,if_pos h]
      dsimp only [ev,z47]
      have hcast : ∀ {w : Fin 5} (hw : y0.src = w) (har : (arrB p.1.1).tgt = w),
          (f.val w ⟨y0,hw⟩ ⟨p.1.1,har⟩).val =
            (f.val y0.src ⟨y0,rfl⟩ ⟨p.1.1,har.trans hw.symm⟩).val := by
        intro w hw har; subst hw; rfl
      exact hcast hy0 p.2
    · rw [if_neg h,if_neg h]; rfl
  · intro q _ hq
    refine sum_eq_zero fun y _ => by simp [basisΛ_val,hq]
  · intro h; exact absurd (mem_univ _) h
lemma z57 {M N : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] (f : M →+ N)
    (h : ∀ (b : B) (m : M),f (z12 b • m) = z12 b • f m) (a : Λ) (m : M) :
    f (a • m) = a • f m := by
  rw [z95 a m,z95 a (f m),map_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [z120 f,h b m]
lemma z94 {M : Type} [AddCommGroup M] [Module Λ M] (m : M) (c : B) :
    z4 z101 (fun _ => m) c = z12 (dualB c) • m := by
  unfold z4
  rw [Finset.sum_apply,sum_eq_single ()]
  · unfold z101
    have hL : ∀ (L : List B),L.Nodup →
        z8 m (L.map fun x => (x,dualB x)) c = if c ∈ L then z12 (dualB c) • m else 0 := by
      intro L hnd
      induction L with
      | nil => simp [z8]
      | cons x xs ih =>
        rw [List.nodup_cons] at hnd
        simp only [List.map_cons,z8,Pi.add_apply,z49,ih hnd.2,List.mem_cons]
        by_cases hcx : c = x
        · subst hcx; simp [hnd.1]
        · simp [hcx]
    rw [hL allB allB_nodup,if_pos (z35 c)]
  · intro u _ hu; cases u; exact absurd rfl hu
  · intro h; exact absurd (mem_univ _) h
lemma z121 {M : Type} [AddCommGroup M] [Module Λ M] (g : B → M) :
    z4 piCol g () = ∑ c : B,z12 (nuB c) • g c := by
  unfold z4
  rw [Finset.sum_apply]
  refine sum_congr rfl fun c _ => by simp [piCol,z8,z49]
lemma z192 {M : Type} [AddCommGroup M] [Module Λ M] (g : I1 → M)
    (hg : ∀ p : I1,eΛ (rev (arrB p.1.1).src) • g p = g p) (c : B) :
    z4 d1Col g c =
      (∑ p : I1,if mulB p.1.2 (arrB p.1.1) = some c then g p else 0) +
      (∑ p : I1,if c = p.1.2 then z12 (nuB (arrB p.1.1)) • g p else 0) := by
  unfold z4
  rw [Finset.sum_apply,← Finset.sum_add_distrib]
  refine sum_congr rfl fun p _ => ?_
  unfold d1Col
  cases hm : mulB p.1.2 (arrB p.1.1) with
  | none =>
    simp only [List.nil_append,z8,Pi.add_apply,Pi.zero_apply,add_zero,z49,
      reduceCtorEq,↓reduceIte,zero_add]
  | some xar =>
    simp only [List.cons_append,List.nil_append,z8,Pi.add_apply,Pi.zero_apply,
      add_zero,z49,Option.some.injEq]
    by_cases hc : c = xar
    · subst hc
      rw [if_pos rfl,if_pos rfl]
      change eΛ (rev (arrB p.1.1).src) • g p + _ = g p + _
      rw [hg p]
    · simp [hc,Ne.symm hc]
lemma z193 {M : Type} [AddCommGroup M] [Module Λ M] (g : B → M)
    (hg : ∀ c : B,eΛ (rev c.src) • g c = g c) (p : I1) :
    z4 d0Col g p =
      (∑ c : B,if c.src = (arrB p.1.1).src ∧ mulB c (arrB (z82 p.1.1)) = some p.1.2 then g c else 0) +
      z12 (nuB (arrB (z82 p.1.1))) • g p.1.2 := by
  have hterm : ∀ c : B,
      z8 (g c) (d0Col c) p =
        (if c.src = (arrB p.1.1).src ∧ mulB c (arrB (z82 p.1.1)) = some p.1.2 then g c else 0) +
        (if p.1.2 = c then z12 (nuB (arrB (z82 p.1.1))) • g c else 0) := by
    intro c
    unfold d0Col
    have hflat : ∀ (L : List (Fin 8)) (F : Fin 8 → List (I1 × B)),
        z8 (g c) (L.flatMap F) p = (L.map fun k => z8 (g c) (F k) p).sum := by
      intro L F; induction L with
      | nil => rfl
      | cons k ks ih => rw [List.flatMap_cons,z132,Pi.add_apply,ih]; rfl
    rw [hflat]
    have hfin : ∀ (G : Fin 8 → M),((List.finRange 8).map G).sum = ∑ k : Fin 8,G k := by
      intro G; rw [← Fin.sum_univ_def]
    rw [hfin]
    have hsplit : ∀ k : Fin 8,
        z8 (g c)
          (if h : (arrB k).src = c.src then
            (match hm : mulB c (arrB (z82 k)) with
             | some xb => [(⟨(k,xb),by have h1 := z71 hm; rw [h1,z159]⟩,eB (rev c.src))]
             | none => []) ++
            [(⟨(z82 k,c),(z239 k).trans h⟩,nuB (arrB k))]
          else []) p =
        (if k = p.1.1 ∧ c.src = (arrB p.1.1).src ∧ mulB c (arrB (z82 p.1.1)) = some p.1.2 then g c else 0) +
        (if k = z82 p.1.1 ∧ p.1.2 = c then z12 (nuB (arrB (z82 p.1.1))) • g c else 0) := by
      intro k
      by_cases hsrc : (arrB k).src = c.src
      · rw [dif_pos hsrc,z132,Pi.add_apply]
        congr 1
        · split
          next xb hm =>
            simp only [z8,Pi.add_apply,Pi.zero_apply,add_zero,z49]
            by_cases h1 : p = ⟨(k,xb),by have h1 := z71 hm; rw [h1,z159]⟩
            · have hk : k = p.1.1 := (congrArg (fun q : I1 => q.1.1) h1).symm
              have hxb : xb = p.1.2 := (congrArg (fun q : I1 => q.1.2) h1).symm
              subst hk; subst hxb
              rw [if_pos h1,if_pos ⟨rfl,hsrc.symm,hm⟩]; exact hg c
            · rw [if_neg h1,if_neg]
              rintro ⟨rfl,_,hm2⟩
              apply h1; apply Subtype.ext; apply Prod.ext; rfl
              exact (Option.some.inj (hm.symm.trans hm2)).symm
          next hm =>
            simp only [z8,Pi.zero_apply]
            symm; rw [if_neg]; rintro ⟨rfl,_,hm2⟩; rw [hm] at hm2; cases hm2
        · simp only [z8,Pi.add_apply,Pi.zero_apply,add_zero,z49]
          have hopp_iff : p = ⟨(z82 k,c),(z239 k).trans hsrc⟩ ↔ k = z82 p.1.1 ∧ p.1.2 = c := by
            constructor
            · intro h1
              have hk : p.1.1 = z82 k := congrArg (fun q : I1 => q.1.1) h1
              have hc : p.1.2 = c := congrArg (fun q : I1 => q.1.2) h1
              refine ⟨?_,hc⟩
              rw [hk]; unfold z82; ext; dsimp; omega
            · rintro ⟨rfl,rfl⟩
              apply Subtype.ext; apply Prod.ext
              · unfold z82; ext; dsimp; omega
              · rfl
          by_cases h1 : k = z82 p.1.1 ∧ p.1.2 = c
          · rw [if_pos (hopp_iff.mpr h1),if_pos h1,h1.1]
          · rw [if_neg (fun hh => h1 (hopp_iff.mp hh)),if_neg h1]
      · rw [dif_neg hsrc]; simp only [z8,Pi.zero_apply]
        have h1 : ¬ (k = p.1.1 ∧ c.src = (arrB p.1.1).src ∧ mulB c (arrB (z82 p.1.1)) = some p.1.2) := by
          rintro ⟨rfl,hc,_⟩; exact hsrc hc.symm
        have h2 : ¬ (k = z82 p.1.1 ∧ p.1.2 = c) := by
          rintro ⟨rfl,rfl⟩; exact hsrc ((z159 p.1.1).trans p.2)
        rw [if_neg h1,if_neg h2,add_zero]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [sum_eq_single p.1.1]
      · simp
      · intro k _ hk; rw [if_neg]; rintro ⟨rfl,_⟩; exact hk rfl
      · intro h; exact absurd (mem_univ _) h
    · rw [sum_eq_single (z82 p.1.1)]
      · simp
      · intro k _ hk; rw [if_neg]; rintro ⟨rfl,_⟩; exact hk rfl
      · intro h; exact absurd (mem_univ _) h
  unfold z4
  rw [Finset.sum_apply]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [sum_eq_single p.1.2]
  · simp
  · intro c _ hc; rw [if_neg (Ne.symm hc)]
  · intro h; exact absurd (mem_univ _) h
def ιF (M : Type) [AddCommGroup M] [Module Λ M] : M →ₗ[Λ] F0 M :=
  let toAdd : M →+ F0 M :=
    { toFun := fun m => z345 (z4 z101 fun _ => m) (z86 z101 (fun c => rev c.src) iotaCol_tgt _)
      map_zero' := z14 (by
        rw [z78]; funext c; simp [z94]; rfl)
      map_add' := fun x y => z14 (by
        rw [z284,z78,z78,z78]
        funext c; simp [z94,smul_add]) }
  { toFun := toAdd
    map_add' := toAdd.map_add
    map_smul' := z57 toAdd fun b m => z14 (by
      funext c
      rw [z51]
      change z4 z101 (fun _ => z12 b • m) c =
        ∑ y : B,if mulB b y = some c then z4 z101 (fun _ => m) y else 0
      simp_rw [z94]
      rw [← mul_smul,z25]
      cases hdb : mulB (dualB c) b with
      | none =>
        rw [zero_smul]
        symm; refine sum_eq_zero fun y _ => ?_
        rw [if_neg]; intro hby
        have hsrc : y.src = c.src := (z71 hby).symm
        have h1 := (z97 (⟨c,rfl⟩ : Bv c.src) b (dualB y)).mpr ⟨⟨y,hsrc⟩,hby,rfl⟩
        rw [hdb] at h1; cases h1
      | some d =>
        obtain ⟨y0,hy0_mul,hy0_dual⟩ := (z97 (⟨c,rfl⟩ : Bv c.src) b d).mp hdb
        symm
        rw [sum_eq_single y0.1]
        · rw [if_pos hy0_mul,hy0_dual]
        · intro y _ hy
          rw [if_neg]; intro hby
          have hsrc : y.src = c.src := (z71 hby).symm
          have heq := z196 (⟨c,rfl⟩ : Bv c.src) b (y₁ := ⟨y,hsrc⟩) (y₂ := y0) hby hy0_mul
          exact hy (congrArg Subtype.val heq)
        · intro h; exact absurd (mem_univ _) h) }
def d0F (M : Type) [AddCommGroup M] [Module Λ M] : F0 M →ₗ[Λ] F1 M :=
  let toAdd : F0 M →+ F1 M :=
    { toFun := fun f => ofFun1 (z4 d0Col (z23 f))
        (z86 d0Col (fun p => rev (arrB p.1.1).src) d0Col_tgt _)
      map_zero' := z37 (by
        rw [z162]; funext p
        rw [z193 _ (z126 0)]
        have h0 : ∀ c : B,z23 (0 : F0 M) c = 0 := fun _ => rfl
        simp [h0]; rfl)
      map_add' := fun f g => z37 (by
        rw [z321,z162,z162,z162,z284,z107]) }
  { toFun := toAdd
    map_add' := toAdd.map_add
    map_smul' := z57 toAdd fun b f => z37 (by
      funext p
      rw [z73]
      change z4 d0Col (z23 (z12 b • f)) p =
        ∑ y : Bv p.1.2.src,if mulB b y.1 = some p.1.2 then
          z4 d0Col (z23 f) ⟨(p.1.1,y.1),p.2.trans y.2.symm⟩ else 0
      rw [z193 _ (z126 (z12 b • f))]
      have hrhs_split :
          (∑ y : Bv p.1.2.src,if mulB b y.1 = some p.1.2 then
            z4 d0Col (z23 f) ⟨(p.1.1,y.1),p.2.trans y.2.symm⟩ else 0) =
          (∑ y : Bv p.1.2.src,if mulB b y.1 = some p.1.2 then
            ∑ c : B,if c.src = (arrB p.1.1).src ∧ mulB c (arrB (z82 p.1.1)) = some y.1 then z23 f c else 0 else 0) +
          (∑ y : Bv p.1.2.src,if mulB b y.1 = some p.1.2 then
            z12 (nuB (arrB (z82 p.1.1))) • z23 f y.1 else 0) := by
        rw [← Finset.sum_add_distrib]
        refine sum_congr rfl fun y _ => ?_
        by_cases hy : mulB b y.1 = some p.1.2
        · rw [if_pos hy,if_pos hy,if_pos hy,z193 _ (z126 f)]
        · rw [if_neg hy,if_neg hy,if_neg hy,add_zero]
      rw [hrhs_split]
      congr 1
      · simp_rw [z51]
        calc ∑ c : B,(if c.src = (arrB p.1.1).src ∧ mulB c (arrB (z82 p.1.1)) = some p.1.2 then
                ∑ z : B,if mulB b z = some c then z23 f z else 0 else 0)
            = ∑ z : B,∑ c : B,
                if c.src = (arrB p.1.1).src ∧ mulB c (arrB (z82 p.1.1)) = some p.1.2 ∧ mulB b z = some c
                then z23 f z else 0 := by
              have hinner : ∀ c : B,
                  (if c.src = (arrB p.1.1).src ∧ mulB c (arrB (z82 p.1.1)) = some p.1.2 then
                    ∑ z : B,if mulB b z = some c then z23 f z else 0 else 0) =
                  ∑ z : B,if c.src = (arrB p.1.1).src ∧ mulB c (arrB (z82 p.1.1)) = some p.1.2 ∧ mulB b z = some c
                    then z23 f z else 0 := by
                intro c
                by_cases h1 : c.src = (arrB p.1.1).src ∧ mulB c (arrB (z82 p.1.1)) = some p.1.2
                · rw [if_pos h1]; refine sum_congr rfl fun z _ => by simp [h1]
                · rw [if_neg h1]; symm; refine sum_eq_zero fun z _ => by
                    rw [if_neg]; intro hh; exact h1 ⟨hh.1,hh.2.1⟩
              simp_rw [hinner]; exact Finset.sum_comm
          _ = ∑ z : B,if z.src = (arrB p.1.1).src ∧
                (mulB b z).bind (fun c => mulB c (arrB (z82 p.1.1))) = some p.1.2
                then z23 f z else 0 := by
              refine sum_congr rfl fun z _ => ?_
              cases hbz : mulB b z with
              | none =>
                simp only [Option.bind_none,reduceCtorEq,and_false,↓reduceIte]
                refine sum_eq_zero fun c _ => rfl
              | some c0 =>
                simp only [Option.bind_some]
                rw [sum_eq_single c0]
                · have hsrc : c0.src = z.src := z71 hbz
                  simp [hsrc]
                · intro c _ hc; rw [if_neg]; rintro ⟨_,_,h⟩; exact hc (Option.some.inj h).symm
                · intro h; exact absurd (mem_univ _) h
          _ = ∑ z : B,if z.src = (arrB p.1.1).src ∧
                (mulB z (arrB (z82 p.1.1))).bind (fun y => mulB b y) = some p.1.2
                then z23 f z else 0 := by
              refine sum_congr rfl fun z _ => by rw [z151]
          _ = ∑ y : Bv p.1.2.src,if mulB b y.1 = some p.1.2 then
                ∑ z : B,if z.src = (arrB p.1.1).src ∧ mulB z (arrB (z82 p.1.1)) = some y.1 then z23 f z else 0 else 0 := by
              symm
              calc _ = ∑ z : B,∑ y : Bv p.1.2.src,
                    if mulB b y.1 = some p.1.2 ∧ z.src = (arrB p.1.1).src ∧ mulB z (arrB (z82 p.1.1)) = some y.1
                    then z23 f z else 0 := by
                    have hinner : ∀ y : Bv p.1.2.src,
                        (if mulB b y.1 = some p.1.2 then
                          ∑ z : B,if z.src = (arrB p.1.1).src ∧ mulB z (arrB (z82 p.1.1)) = some y.1 then z23 f z else 0 else 0) =
                        ∑ z : B,if mulB b y.1 = some p.1.2 ∧ z.src = (arrB p.1.1).src ∧ mulB z (arrB (z82 p.1.1)) = some y.1
                          then z23 f z else 0 := by
                      intro y; by_cases hy : mulB b y.1 = some p.1.2
                      · rw [if_pos hy]; refine sum_congr rfl fun z _ => by simp [hy]
                      · rw [if_neg hy]; symm; refine sum_eq_zero fun z _ => by simp [hy]
                    simp_rw [hinner]; exact Finset.sum_comm
                _ = _ := by
                    refine sum_congr rfl fun z _ => ?_
                    cases hza : mulB z (arrB (z82 p.1.1)) with
                    | none =>
                      simp only [Option.bind_none,reduceCtorEq,and_false,↓reduceIte]
                      refine sum_eq_zero fun y _ => rfl
                    | some y0 =>
                      simp only [Option.bind_some]
                      have hy0_src : y0.src = p.1.2.src := by
                        rw [z71 hza,z159,p.2]
                      rw [sum_eq_single ⟨y0,hy0_src⟩]
                      · simp [and_comm]
                      · intro y _ hy; rw [if_neg]; rintro ⟨_,_,h⟩; exact hy (Subtype.ext (Option.some.inj h).symm)
                      · intro h; exact absurd (mem_univ _) h
      · rw [z51,Finset.smul_sum]
        have hsmul : ∀ y : B,
            z12 (nuB (arrB (z82 p.1.1))) • (if mulB b y = some p.1.2 then z23 f y else 0) =
            if mulB b y = some p.1.2 then z12 (nuB (arrB (z82 p.1.1))) • z23 f y else 0 := by
          intro y; split_ifs <;> simp
        simp_rw [hsmul]
        rw [← Finset.sum_filter]
        symm; rw [← Finset.sum_filter]
        symm
        refine Finset.sum_bij (fun y hy => ⟨y,(z71 (Finset.mem_filter.mp hy).2).symm⟩)
          (fun y hy => Finset.mem_filter.mpr ⟨mem_univ _,(Finset.mem_filter.mp hy).2⟩)
          (fun _ _ _ _ h => congrArg Subtype.val h)
          (fun y hy => ⟨y.1,Finset.mem_filter.mpr ⟨mem_univ _,(Finset.mem_filter.mp hy).2⟩,rfl⟩)
          (fun _ _ => rfl) ) }
def d1F (M : Type) [AddCommGroup M] [Module Λ M] : F1 M →ₗ[Λ] F0 M :=
  let toAdd : F1 M →+ F0 M :=
    { toFun := fun f => z345 (z4 d1Col (z47 f))
        (z86 d1Col (fun c => rev c.src) d1Col_tgt _)
      map_zero' := z14 (by
        rw [z78]; funext c
        rw [z192 _ (z146 0)]
        have h0 : ∀ p : I1,z47 (0 : F1 M) p = 0 := fun _ => rfl
        simp [h0]; rfl)
      map_add' := fun f g => z14 (by
        rw [z284,z78,z78,z78,z321,z107]) }
  { toFun := toAdd
    map_add' := toAdd.map_add
    map_smul' := z57 toAdd fun b f => z14 (by
      funext c
      rw [z51]
      change z4 d1Col (z47 (z12 b • f)) c =
        ∑ y : B,if mulB b y = some c then z4 d1Col (z47 f) y else 0
      rw [z192 _ (z146 (z12 b • f))]
      have hrhs_split :
          (∑ y : B,if mulB b y = some c then z4 d1Col (z47 f) y else 0) =
          (∑ y : B,if mulB b y = some c then
            ∑ p : I1,if mulB p.1.2 (arrB p.1.1) = some y then z47 f p else 0 else 0) +
          (∑ y : B,if mulB b y = some c then
            ∑ p : I1,if y = p.1.2 then z12 (nuB (arrB p.1.1)) • z47 f p else 0 else 0) := by
        rw [← Finset.sum_add_distrib]
        refine sum_congr rfl fun y _ => ?_
        by_cases hy : mulB b y = some c
        · rw [if_pos hy,if_pos hy,if_pos hy,z192 _ (z146 f)]
        · rw [if_neg hy,if_neg hy,if_neg hy,add_zero]
      rw [hrhs_split]
      congr 1
      · calc ∑ p : I1,(if mulB p.1.2 (arrB p.1.1) = some c then z47 (z12 b • f) p else 0)
            = ∑ p : I1,∑ y : Bv p.1.2.src,
                if mulB p.1.2 (arrB p.1.1) = some c ∧ mulB b y.1 = some p.1.2 then
                  z47 f ⟨(p.1.1,y.1),p.2.trans y.2.symm⟩ else 0 := by
              refine sum_congr rfl fun p _ => ?_
              rw [z73]
              by_cases h1 : mulB p.1.2 (arrB p.1.1) = some c
              · rw [if_pos h1]; refine sum_congr rfl fun y _ => by simp [h1]
              · rw [if_neg h1]; symm; refine sum_eq_zero fun y _ => by simp [h1]
          _ = ∑ q : I1,
                if (mulB b q.1.2).bind (fun z => mulB z (arrB q.1.1)) = some c then z47 f q else 0 := by
              have hreidx : ∀ p : I1,
                  (∑ y : Bv p.1.2.src,
                    if mulB p.1.2 (arrB p.1.1) = some c ∧ mulB b y.1 = some p.1.2 then
                      z47 f ⟨(p.1.1,y.1),p.2.trans y.2.symm⟩ else 0) =
                  ∑ q : I1,
                    if q.1.1 = p.1.1 ∧ mulB p.1.2 (arrB p.1.1) = some c ∧ mulB b q.1.2 = some p.1.2 then
                      z47 f q else 0 := by
                intro p
                rw [← Finset.sum_filter]
                symm; rw [← Finset.sum_filter]
                refine Finset.sum_bij (fun q hq => ⟨q.1.2,((Finset.mem_filter.mp hq).2.1 ▸ q.2).symm.trans p.2⟩)
                  (fun q hq => by
                    have h := (Finset.mem_filter.mp hq).2
                    exact Finset.mem_filter.mpr ⟨mem_univ _,h.2.1,h.2.2⟩)
                  (fun q1 hq1 q2 hq2 heq => by
                    have h1 := (Finset.mem_filter.mp hq1).2.1
                    have h2 := (Finset.mem_filter.mp hq2).2.1
                    apply Subtype.ext; apply Prod.ext
                    · exact h1.trans h2.symm
                    · exact congrArg Subtype.val heq)
                  (fun y hy => ⟨⟨(p.1.1,y.1),p.2.trans y.2.symm⟩,
                    Finset.mem_filter.mpr ⟨mem_univ _,rfl,(Finset.mem_filter.mp hy).2⟩,rfl⟩)
                  (fun q hq => by
                    have h1 := (Finset.mem_filter.mp hq).2.1
                    congr 1; apply Subtype.ext; apply Prod.ext; exact h1; rfl)
              simp_rw [hreidx]
              rw [Finset.sum_comm]
              refine sum_congr rfl fun q _ => ?_
              cases hbq : mulB b q.1.2 with
              | none =>
                simp only [Option.bind_none,reduceCtorEq,↓reduceIte]
                refine sum_eq_zero fun p _ => by rw [if_neg]; rintro ⟨_,_,h⟩; simp at h
              | some z0 =>
                simp only [Option.bind_some]
                have hz0 : (arrB q.1.1).tgt = z0.src := q.2.trans (z71 hbq).symm
                rw [sum_eq_single ⟨(q.1.1,z0),hz0⟩]
                · simp
                · intro p _ hp; rw [if_neg]; rintro ⟨h1,_,h2⟩
                  apply hp; apply Subtype.ext; apply Prod.ext; exact h1.symm; exact (Option.some.inj h2).symm
                · intro h; exact absurd (mem_univ _) h
          _ = ∑ q : I1,
                if (mulB q.1.2 (arrB q.1.1)).bind (fun y => mulB b y) = some c then z47 f q else 0 := by
              refine sum_congr rfl fun q _ => by rw [z151]
          _ = _ := by
              symm
              calc _ = ∑ q : I1,∑ y : B,
                    if mulB b y = some c ∧ mulB q.1.2 (arrB q.1.1) = some y then z47 f q else 0 := by
                    have hinner : ∀ y : B,
                        (if mulB b y = some c then
                          ∑ q : I1,if mulB q.1.2 (arrB q.1.1) = some y then z47 f q else 0 else 0) =
                        ∑ q : I1,if mulB b y = some c ∧ mulB q.1.2 (arrB q.1.1) = some y then z47 f q else 0 := by
                      intro y; by_cases hy : mulB b y = some c
                      · rw [if_pos hy]; refine sum_congr rfl fun q _ => by simp [hy]
                      · rw [if_neg hy]; symm; refine sum_eq_zero fun q _ => by simp [hy]
                    simp_rw [hinner]; exact Finset.sum_comm
                _ = _ := by
                    refine sum_congr rfl fun q _ => ?_
                    cases hqa : mulB q.1.2 (arrB q.1.1) with
                    | none =>
                      simp only [Option.bind_none,reduceCtorEq,↓reduceIte]
                      refine sum_eq_zero fun y _ => by rw [if_neg]; rintro ⟨_,h⟩; simp at h
                    | some y0 =>
                      simp only [Option.bind_some]
                      rw [sum_eq_single y0]
                      · simp
                      · intro y _ hy; rw [if_neg]; rintro ⟨_,h⟩; exact hy (Option.some.inj h).symm
                      · intro h; exact absurd (mem_univ _) h
      · calc ∑ p : I1,(if c = p.1.2 then z12 (nuB (arrB p.1.1)) • z47 (z12 b • f) p else 0)
            = ∑ p : I1,∑ y : Bv p.1.2.src,
                if c = p.1.2 ∧ mulB b y.1 = some p.1.2 then
                  z12 (nuB (arrB p.1.1)) • z47 f ⟨(p.1.1,y.1),p.2.trans y.2.symm⟩ else 0 := by
              refine sum_congr rfl fun p _ => ?_
              rw [z73,Finset.smul_sum]
              by_cases h1 : c = p.1.2
              · rw [if_pos h1]
                refine sum_congr rfl fun y _ => by
                  by_cases h2 : mulB b y.1 = some p.1.2 <;> simp [h1,h2]
              · rw [if_neg h1]; symm; refine sum_eq_zero fun y _ => by simp [h1]
          _ = ∑ q : I1,
                if mulB b q.1.2 = some c then z12 (nuB (arrB q.1.1)) • z47 f q else 0 := by
              have hreidx : ∀ p : I1,
                  (∑ y : Bv p.1.2.src,
                    if c = p.1.2 ∧ mulB b y.1 = some p.1.2 then
                      z12 (nuB (arrB p.1.1)) • z47 f ⟨(p.1.1,y.1),p.2.trans y.2.symm⟩ else 0) =
                  ∑ q : I1,
                    if q.1.1 = p.1.1 ∧ c = p.1.2 ∧ mulB b q.1.2 = some p.1.2 then
                      z12 (nuB (arrB q.1.1)) • z47 f q else 0 := by
                intro p
                rw [← Finset.sum_filter]
                symm; rw [← Finset.sum_filter]
                refine Finset.sum_bij (fun q hq => ⟨q.1.2,((Finset.mem_filter.mp hq).2.1 ▸ q.2).symm.trans p.2⟩)
                  (fun q hq => by
                    have h := (Finset.mem_filter.mp hq).2
                    exact Finset.mem_filter.mpr ⟨mem_univ _,h.2.1,h.2.2⟩)
                  (fun q1 hq1 q2 hq2 heq => by
                    have h1 := (Finset.mem_filter.mp hq1).2.1
                    have h2 := (Finset.mem_filter.mp hq2).2.1
                    apply Subtype.ext; apply Prod.ext
                    · exact h1.trans h2.symm
                    · exact congrArg Subtype.val heq)
                  (fun y hy => ⟨⟨(p.1.1,y.1),p.2.trans y.2.symm⟩,
                    Finset.mem_filter.mpr ⟨mem_univ _,rfl,(Finset.mem_filter.mp hy).2⟩,rfl⟩)
                  (fun q hq => by
                    have h1 : q.1.1 = p.1.1 := (Finset.mem_filter.mp hq).2.1
                    rcases q with ⟨⟨q1,q2⟩,hq2⟩
                    dsimp at h1; subst h1; rfl)
              simp_rw [hreidx]
              rw [Finset.sum_comm]
              refine sum_congr rfl fun q _ => ?_
              by_cases hbq : mulB b q.1.2 = some c
              · have hc_src : (arrB q.1.1).tgt = c.src := q.2.trans (z71 hbq).symm
                rw [if_pos hbq,sum_eq_single ⟨(q.1.1,c),hc_src⟩]
                · simp [hbq]
                · intro p _ hp; rw [if_neg]; rintro ⟨h1,h2,_⟩
                  apply hp; apply Subtype.ext; apply Prod.ext; exact h1.symm; exact h2.symm
                · intro h; exact absurd (mem_univ _) h
              · rw [if_neg hbq]; refine sum_eq_zero fun p _ => by
                  rw [if_neg]; rintro ⟨_,rfl,h2⟩; exact hbq h2
          _ = _ := by
              symm
              have hinner : ∀ y : B,
                  (if mulB b y = some c then
                    ∑ q : I1,if y = q.1.2 then z12 (nuB (arrB q.1.1)) • z47 f q else 0 else 0) =
                  ∑ q : I1,if mulB b y = some c ∧ y = q.1.2 then
                    z12 (nuB (arrB q.1.1)) • z47 f q else 0 := by
                intro y; by_cases hy : mulB b y = some c
                · rw [if_pos hy]; refine sum_congr rfl fun q _ => by simp [hy]
                · rw [if_neg hy]; symm; refine sum_eq_zero fun q _ => by simp [hy]
              simp_rw [hinner]
              rw [Finset.sum_comm]
              refine sum_congr rfl fun q _ => ?_
              rw [sum_eq_single q.1.2]
              · simp
              · intro y _ hy; simp [hy]
              · intro h; exact absurd (mem_univ _) h) }
def πF (M : Type) [AddCommGroup M] [Module Λ M] : F0 M →ₗ[Λ] nuMod M :=
  let toAdd : F0 M →+ nuMod M :=
    { toFun := fun f => ⟨z4 piCol (z23 f) ()⟩
      map_zero' := by
        apply nuMod.ext
        change z4 piCol (z23 (0 : F0 M)) () = 0
        rw [z121]
        refine sum_eq_zero fun c _ => ?_
        change z12 (nuB c) • (0 : M) = 0; simp
      map_add' := fun f g => by
        apply nuMod.ext
        change z4 piCol (z23 f + z23 g) () =
          z4 piCol (z23 f) () + z4 piCol (z23 g) ()
        rw [z107]; rfl }
  { toFun := toAdd
    map_add' := toAdd.map_add
    map_smul' := z57 toAdd fun b f => by
      apply nuMod.ext
      change z4 piCol (z23 (z12 b • f)) () = ν (z12 b) • z4 piCol (z23 f) ()
      rw [z121,z121,z230,Finset.smul_sum]
      simp_rw [z51,Finset.smul_sum]
      rw [Finset.sum_comm]
      refine sum_congr rfl fun y _ => ?_
      rw [← mul_smul,z25,z187]
      cases hby : mulB b y with
      | none =>
        simp only [Option.map_none,zero_smul]
        refine sum_eq_zero fun c _ => by simp
      | some c0 =>
        simp only [Option.map_some]
        rw [sum_eq_single c0]
        · simp
        · intro c _ hc; simp [Ne.symm hc]
        · intro h; exact absurd (mem_univ _) h }
lemma ιF_inj (M : Type) [AddCommGroup M] [Module Λ M] : Function.Injective (ιF M) := by
  intro m1 m2 h
  have hcol : z4 z101 (fun _ => m1) = z4 z101 (fun _ => m2) := by
    have := congrArg z23 h
    exact this
  have hsn : z4 z285 (z4 z101 (fun _ => m1)) () =
      z4 z285 (z4 z101 (fun _ => m2)) () := congrArg (fun k => z4 z285 k ()) hcol
  rw [z46,z46] at hsn
  rw [z20 (z77 z300 leB) _ _ z255,
      z20 (z77 z300 leB) _ _ z255,
      z171,z171] at hsn
  exact hsn
lemma πF_surj (M : Type) [AddCommGroup M] [Module Λ M] : Function.Surjective (πF M) := by
  intro x
  let f : F0 M := z345 (z4 s2Col fun _ => x.val)
    (z86 s2Col (fun c => rev c.src) s2Col_tgt _)
  refine ⟨f,nuMod.ext ?_⟩
  change z4 piCol (z4 s2Col fun _ => x.val) () = x.val
  rw [z46,z20 (z77 z300 leB) _ _ check_pi_s2,z171]
lemma z352 (M : Type) [AddCommGroup M] [Module Λ M] : ExactAt (ιF M) (d0F M) := by
  ext f
  simp only [LinearMap.mem_range,LinearMap.mem_ker]
  constructor
  · rintro ⟨m,rfl⟩
    apply z37
    change z4 d0Col (z4 z101 fun _ => m) = 0
    rw [z46,z20 (z77 leI1 leB) _ (fun _ => []) z335,z191]
  · intro hf
    have h0 : z4 d0Col (z23 f) = 0 := congrArg z47 hf
    let m : M := z4 z285 (z23 f) ()
    refine ⟨m,z14 ?_⟩
    change z4 z101 (fun _ => z4 z285 (z23 f) ()) = z23 f
    have h1 : (fun _ : Unit => z4 z285 (z23 f) ()) = z4 z285 (z23 f) := by
      funext u; cases u; rfl
    rw [h1]
    have hsum : z4 z101 (z4 z285 (z23 f)) +
        z4 s0Col (z4 d0Col (z23 f)) = z23 f := by
      rw [z46,z46,z172,
        z20 (z77 leB leB) _ _ z238,
        z213 (fun c => rev c.src) (z23 f) (z126 f)]
    have hzero : z4 s0Col (z4 d0Col (z23 f)) = 0 := by
      rw [h0]; unfold z4; exact sum_eq_zero fun p _ => z119 (s0Col p)
    rw [hzero,add_zero] at hsum
    exact hsum
lemma z333 (M : Type) [AddCommGroup M] [Module Λ M] : ExactAt (d0F M) (d1F M) := by
  ext f
  simp only [LinearMap.mem_range,LinearMap.mem_ker]
  constructor
  · rintro ⟨g,rfl⟩
    apply z14
    change z4 d1Col (z4 d0Col (z23 g)) = 0
    rw [z46,z20 (z77 leB leB) _ (fun _ => []) check_d1_d0,z191]
  · intro hf
    have h0 : z4 d1Col (z47 f) = 0 := congrArg z23 hf
    let g : F0 M := z345 (z4 s0Col (z47 f))
      (z86 s0Col (fun c => rev c.src) s0Col_tgt _)
    refine ⟨g,z37 ?_⟩
    change z4 d0Col (z4 s0Col (z47 f)) = z47 f
    have hsum : z4 d0Col (z4 s0Col (z47 f)) +
        z4 s1Col (z4 d1Col (z47 f)) = z47 f := by
      rw [z46,z46,z172,
        z20 (z77 leI1 leB) _ _ z277,
        z213 (fun p => rev (arrB p.1.1).src) (z47 f) (z146 f)]
    have hzero : z4 s1Col (z4 d1Col (z47 f)) = 0 := by
      rw [h0]; unfold z4; exact sum_eq_zero fun c _ => z119 (s1Col c)
    rw [hzero,add_zero] at hsum
    exact hsum
lemma z353 (M : Type) [AddCommGroup M] [Module Λ M] : ExactAt (d1F M) (πF M) := by
  ext f
  simp only [LinearMap.mem_range,LinearMap.mem_ker]
  constructor
  · rintro ⟨g,rfl⟩
    apply nuMod.ext
    change z4 piCol (z4 d1Col (z47 g)) () = 0
    rw [z46,z20 (z77 z300 leB) _ (fun _ => []) check_pi_d1,z191]
    rfl
  · intro hf
    have h0 : z4 piCol (z23 f) = 0 := by
      funext u; cases u; exact congrArg nuMod.val hf
    let g : F1 M := ofFun1 (z4 s1Col (z23 f))
      (z86 s1Col (fun p => rev (arrB p.1.1).src) s1Col_tgt _)
    refine ⟨g,z14 ?_⟩
    change z4 d1Col (z4 s1Col (z23 f)) = z23 f
    have hsum : z4 d1Col (z4 s1Col (z23 f)) +
        z4 s2Col (z4 piCol (z23 f)) = z23 f := by
      rw [z46,z46,z172,
        z20 (z77 leB leB) _ _ z276,
        z213 (fun c => rev c.src) (z23 f) (z126 f)]
    have hzero : z4 s2Col (z4 piCol (z23 f)) = 0 := by
      rw [h0]; unfold z4; exact sum_eq_zero fun u _ => z119 (s2Col u)
    rw [hzero,add_zero] at hsum
    exact hsum
noncomputable def z18 (M : Type) [AddCommGroup M] [Module Λ M] [Finite M] :
    (z22 (V0 M)).Mod ≃ₗ[Λ] F0 M := z197 (V0 M)
noncomputable def z50 (M : Type) [AddCommGroup M] [Module Λ M] [Finite M] :
    (z22 (V1 M)).Mod ≃ₗ[Λ] F1 M := z197 (V1 M)
lemma z60 {A B' C C' : Type} [AddCommGroup A] [Module Λ A]
    [AddCommGroup B'] [Module Λ B'] [AddCommGroup C] [Module Λ C] [AddCommGroup C'] [Module Λ C']
    (f : A →ₗ[Λ] B') (g : B' →ₗ[Λ] C) (e : C ≃ₗ[Λ] C') (h : ExactAt f g) :
    ExactAt f (e.toLinearMap.comp g) := by
  ext x; simp only [LinearMap.mem_ker,LinearMap.comp_apply,LinearEquiv.coe_coe,
    map_eq_zero_iff _ e.injective]
  exact SetLike.ext_iff.mp h x
lemma z66 {A' A B' C : Type} [AddCommGroup A'] [Module Λ A']
    [AddCommGroup A] [Module Λ A] [AddCommGroup B'] [Module Λ B'] [AddCommGroup C] [Module Λ C]
    (e : A' ≃ₗ[Λ] A) (f : A →ₗ[Λ] B') (g : B' →ₗ[Λ] C) (h : ExactAt f g) :
    ExactAt (f.comp e.toLinearMap) g := by
  ext x; simp only [LinearMap.mem_range,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [← h]; simp only [LinearMap.mem_range]
  exact ⟨fun ⟨a',ha'⟩ => ⟨e a',ha'⟩,fun ⟨a,ha⟩ => ⟨e.symm a,by simpa using ha⟩⟩
lemma z93 {A B1 B2 C : Type} [AddCommGroup A] [Module Λ A]
    [AddCommGroup B1] [Module Λ B1] [AddCommGroup B2] [Module Λ B2] [AddCommGroup C] [Module Λ C]
    (f : A →ₗ[Λ] B1) (g : B1 →ₗ[Λ] C) (e : B1 ≃ₗ[Λ] B2) (h : ExactAt f g) :
    ExactAt (e.toLinearMap.comp f) (g.comp e.symm.toLinearMap) := by
  ext y; simp only [LinearMap.mem_range,LinearMap.mem_ker,LinearMap.comp_apply,LinearEquiv.coe_coe]
  have h1 : e.symm y ∈ LinearMap.range f ↔ e.symm y ∈ LinearMap.ker g := SetLike.ext_iff.mp h (e.symm y)
  simp only [LinearMap.mem_range,LinearMap.mem_ker] at h1
  rw [← h1]
  exact ⟨fun ⟨a,ha⟩ => ⟨a,by rw [← ha,e.symm_apply_apply]⟩,
         fun ⟨a,ha⟩ => ⟨a,by rw [ha,e.apply_symm_apply]⟩⟩
noncomputable def z6 (M : Type) [AddCommGroup M] [Module Λ M] [Finite M] :
    ExactSeq3 M where
  P0 := z22 (V0 M)
  P1 := z22 (V1 M)
  P2 := z22 (V0 M)
  ι := (z18 M).symm.toLinearMap.comp (ιF M)
  d0 := ⟨(z50 M).symm.toLinearMap.comp ((d0F M).comp (z18 M).toLinearMap)⟩
  d1 := ⟨(z18 M).symm.toLinearMap.comp ((d1F M).comp (z50 M).toLinearMap)⟩
  π := (πF M).comp (z18 M).toLinearMap
  ι_inj := (z18 M).symm.injective.comp (ιF_inj M)
  exact0 := by
    have h1 := z93 (ιF M) (d0F M) (z18 M).symm (z352 M)
    have h2 := z60 _ _ (z50 M).symm h1
    simpa [LinearMap.comp_assoc] using h2
  exact1 := by
    have h1 := z93 (d0F M) (d1F M) (z50 M).symm (z333 M)
    have h2 := z66 (z18 M) _ _ h1
    have h3 := z60 _ _ (z18 M).symm h2
    simpa [LinearMap.comp_assoc] using h3
  exact2 := by
    have h1 := z93 (d1F M) (πF M) (z18 M).symm (z353 M)
    have h2 := z66 (z50 M) _ _ h1
    simpa [LinearMap.comp_assoc] using h2
  π_surj := (πF_surj M).comp (z18 M).surjective
lemma z234 (M : Type) [AddCommGroup M] [Module Λ M] [Finite M] :
    ∃ (P : FP) (j : M →ₗ[Λ] P.Mod),Function.Injective j :=
  ⟨(z6 M).P0,(z6 M).ι,(z6 M).ι_inj⟩
def z89 {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (f : M →ₗ[Λ] N) : F0 M →ₗ[Λ] F0 N :=
  z261 fun v => z158 (rev v) f
def v1Map (v : Fin 5) {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (f : M →ₗ[Λ] N) : V1 M v →ₗ[ZMod 2] V1 N v where
  toFun g ar := z158 (rev (arrB ar.1).src) f (g ar)
  map_add' _ _ := by funext ar; exact (z158 _ f).map_add _ _
  map_smul' r _ := by funext ar; exact (z158 _ f).map_smul r _
def z113 {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (f : M →ₗ[Λ] N) : F1 M →ₗ[Λ] F1 N :=
  z261 fun v => v1Map v f
noncomputable def z58 {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] (f : M →ₗ[Λ] N) :
    (z6 M).P0 ⟶ (z6 N).P0 :=
  ⟨(z18 N).symm.toLinearMap.comp ((z89 f).comp (z18 M).toLinearMap)⟩
noncomputable def z65 {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] (f : M →ₗ[Λ] N) :
    (z6 M).P1 ⟶ (z6 N).P1 :=
  ⟨(z50 N).symm.toLinearMap.comp ((z113 f).comp (z50 M).toLinearMap)⟩
noncomputable def z237 {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] (f : M →ₗ[Λ] N) :
    (z6 M).P2 ⟶ (z6 N).P2 :=
  z58 f
lemma z318 {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] (f : M →ₗ[Λ] N) :
    (z58 f).hom.comp (z6 M).ι = (z6 N).ι.comp f := by
  apply LinearMap.ext; intro m
  change (z18 N).symm (z89 f ((z18 M) ((z18 M).symm (ιF M m)))) =
    (z18 N).symm (ιF N (f m))
  rw [(z18 M).apply_symm_apply]
  congr 1
  apply z14; funext c
  exact z122 z101 f (fun _ => m) c
lemma z303 {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] (f : M →ₗ[Λ] N) :
    comp (z6 M).d0 (z65 f) =
      comp (z58 f) (z6 N).d0 := by
  apply FP.hom_ext; intro x
  change (z50 N).symm (z113 f ((z50 M) ((z50 M).symm (d0F M (z18 M x))))) =
    (z50 N).symm (d0F N ((z18 N) ((z18 N).symm (z89 f (z18 M x)))))
  rw [(z50 M).apply_symm_apply,(z18 N).apply_symm_apply]
  congr 1
  apply z37; funext p
  exact z122 d0Col f (z23 (z18 M x)) p
lemma z302 {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] (f : M →ₗ[Λ] N) :
    comp (z6 M).d1 (z237 f) =
      comp (z65 f) (z6 N).d1 := by
  apply FP.hom_ext; intro x
  change (z18 N).symm (z89 f ((z18 M) ((z18 M).symm (d1F M (z50 M x))))) =
    (z18 N).symm (d1F N ((z50 N) ((z50 N).symm (z113 f (z50 M x)))))
  rw [(z18 M).apply_symm_apply,(z50 N).apply_symm_apply]
  congr 1
  apply z14; funext c
  exact z122 d1Col f (z47 (z50 M x)) c
lemma z316 {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] (f : M →ₗ[Λ] N) :
    (z6 N).π.comp (z237 f).hom = (nuMap f).comp (z6 M).π := by
  apply LinearMap.ext; intro x
  apply nuMod.ext
  change z4 piCol (z23 ((z18 N) ((z18 N).symm (z89 f (z18 M x))))) () =
    f (z4 piCol (z23 (z18 M x)) ())
  rw [(z18 N).apply_symm_apply]
  exact (z122 piCol f (z23 (z18 M x)) ()).symm
lemma z200 {M N P : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] [AddCommGroup P] [Module Λ P] [Finite P]
    (f : M →ₗ[Λ] N) (g : N →ₗ[Λ] P) :
    z58 (g.comp f) = comp (z58 f) (z58 g) := by
  apply FP.hom_ext; intro x
  change (z18 P).symm (z89 (g.comp f) (z18 M x)) =
    (z18 P).symm (z89 g ((z18 N) ((z18 N).symm (z89 f (z18 M x)))))
  rw [(z18 N).apply_symm_apply]
  rfl
lemma z275 {M N P : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] [AddCommGroup P] [Module Λ P] [Finite P]
    (f : M →ₗ[Λ] N) (g : N →ₗ[Λ] P) :
    z65 (g.comp f) = comp (z65 f) (z65 g) := by
  apply FP.hom_ext; intro x
  change (z50 P).symm (z113 (g.comp f) (z50 M x)) =
    (z50 P).symm (z113 g ((z50 N) ((z50 N).symm (z113 f (z50 M x)))))
  rw [(z50 N).apply_symm_apply]
  rfl
lemma z199 {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] :
    z58 (0 : M →ₗ[Λ] N) = 0 := by
  apply FP.hom_ext; intro x
  change (z18 N).symm (z89 (0 : M →ₗ[Λ] N) (z18 M x)) = 0
  have hz : z89 (0 : M →ₗ[Λ] N) (z18 M x) = 0 := by apply xM; ext v c; rfl
  rw [hz,map_zero]
lemma z274 {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] :
    z65 (0 : M →ₗ[Λ] N) = 0 := by
  apply FP.hom_ext; intro x
  change (z50 N).symm (z113 (0 : M →ₗ[Λ] N) (z50 M x)) = 0
  have hz : z113 (0 : M →ₗ[Λ] N) (z50 M x) = 0 := by apply xM; ext v c ar; rfl
  rw [hz,map_zero]
lemma z179 {U Y X : Type} [AddCommGroup U] [Module Λ U] [Finite U]
    [AddCommGroup Y] [Module Λ Y] [Finite Y] [AddCommGroup X] [Module Λ X] [Finite X]
    (w : U →ₗ[Λ] Y) (z : Y →ₗ[Λ] X)
    (hw : Function.Injective w) (hex : ExactAt w z) (hz : Function.Surjective z) :
    Function.Injective (z58 w).hom ∧
      ExactAt (z58 w).hom (z58 z).hom ∧
      Function.Surjective (z58 z).hom := by
  have hF := z250 (fun v => z158 (rev v) w) (fun v => z158 (rev v) z)
    (fun v => z136 (rev v) w z hw hex hz)
  refine ⟨((z18 Y).symm.injective.comp hF.1).comp (z18 U).injective,?_,
    ((z18 X).symm.surjective.comp hF.2.2).comp (z18 Y).surjective⟩
  have h1 := z93 (z89 w) (z89 z) (z18 Y).symm hF.2.1
  have h2 := z66 (z18 U) _ _ h1
  have h3 := z60 _ _ (z18 X).symm h2
  change ExactAt ((z18 Y).symm.toLinearMap.comp ((z89 w).comp (z18 U).toLinearMap))
    ((z18 X).symm.toLinearMap.comp ((z89 z).comp (z18 Y).toLinearMap))
  simpa [LinearMap.comp_assoc] using h3
lemma z263 {U Y X : Type} [AddCommGroup U] [Module Λ U] [Finite U]
    [AddCommGroup Y] [Module Λ Y] [Finite Y] [AddCommGroup X] [Module Λ X] [Finite X]
    (w : U →ₗ[Λ] Y) (z : Y →ₗ[Λ] X)
    (hw : Function.Injective w) (hex : ExactAt w z) (hz : Function.Surjective z) :
    Function.Injective (z65 w).hom ∧
      ExactAt (z65 w).hom (z65 z).hom ∧
      Function.Surjective (z65 z).hom := by
  have hv1 : ∀ v : Fin 5,Function.Injective (v1Map v w) ∧
      LinearMap.range (v1Map v w) = LinearMap.ker (v1Map v z) ∧
      Function.Surjective (v1Map v z) := fun v => by
    refine ⟨fun x y hxy => funext fun ar => (z136 _ w z hw hex hz).1 (congrFun hxy ar),?_,?_⟩
    · ext y; simp only [LinearMap.mem_range,LinearMap.mem_ker]
      constructor
      · rintro ⟨u,rfl⟩; funext ar
        have hmem : z158 _ w (u ar) ∈ LinearMap.ker (z158 _ z) := by
          rw [← (z136 _ w z hw hex hz).2.1]; exact ⟨u ar,rfl⟩
        exact hmem
      · intro hy
        have hchoice : ∀ ar,∃ u,z158 _ w u = y ar := fun ar => by
          have hmem : y ar ∈ LinearMap.range (z158 _ w) := by
            rw [(z136 _ w z hw hex hz).2.1]; exact congrFun hy ar
          exact hmem
        choose u hu using hchoice
        exact ⟨u,funext hu⟩
    · intro x
      have hchoice : ∀ ar,∃ y,z158 _ z y = x ar := fun ar =>
        (z136 _ w z hw hex hz).2.2 (x ar)
      choose y hy using hchoice
      exact ⟨y,funext hy⟩
  have hF := z250 (fun v => v1Map v w) (fun v => v1Map v z) hv1
  refine ⟨((z50 Y).symm.injective.comp hF.1).comp (z50 U).injective,?_,
    ((z50 X).symm.surjective.comp hF.2.2).comp (z50 Y).surjective⟩
  have h1 := z93 (z113 w) (z113 z) (z50 Y).symm hF.2.1
  have h2 := z66 (z50 U) _ _ h1
  have h3 := z60 _ _ (z50 X).symm h2
  change ExactAt ((z50 Y).symm.toLinearMap.comp ((z113 w).comp (z50 U).toLinearMap))
    ((z50 X).symm.toLinearMap.comp ((z113 z).comp (z50 Y).toLinearMap))
  simpa [LinearMap.comp_assoc] using h3
def nuF0 (M : Type) [AddCommGroup M] [Module Λ M] : nuMod (F0 M) →ₗ[Λ] F0 (nuMod M) :=
  let toAdd : nuMod (F0 M) →+ F0 (nuMod M) :=
    { toFun := fun x => z345 (fun c => ⟨z23 x.val (nuB c)⟩) (fun c => by
        apply nuMod.ext
        change ν (eΛ (rev c.src)) • z23 x.val (nuB c) = z23 x.val (nuB c)
        rw [ν_eΛ]
        exact z126 x.val (nuB c))
      map_zero' := z14 (by funext c; rfl)
      map_add' := fun x y => z14 (by funext c; rfl) }
  { toFun := toAdd
    map_add' := toAdd.map_add
    map_smul' := z57 toAdd fun b x => z14 (by
      funext c
      apply nuMod.ext
      change z23 (ν (z12 b) • x.val) (nuB c) =
        (z23 (z12 b • toAdd x) c).val
      rw [z230,z51,z51]
      let ev : nuMod M →+ M := { toFun := nuMod.val,map_zero' := rfl,map_add' := fun _ _ => rfl }
      change _ = ev (∑ y : B,if mulB b y = some c then ⟨z23 x.val (nuB y)⟩ else 0)
      rw [map_sum]
      let eB_eq : B ≃ B := ⟨nuB,nuB,z19,z19⟩
      rw [← eB_eq.sum_comp]
      refine sum_congr rfl fun y _ => ?_
      dsimp [eB_eq]
      have hiff : mulB (nuB b) (nuB y) = some (nuB c) ↔ mulB b y = some c := by
        rw [z187]
        cases h : mulB b y with
        | none => simp
        | some z =>
          simp only [Option.map_some,Option.some.injEq]
          exact ⟨fun hz => by rw [← z19 z,hz,z19],fun hz => by rw [hz]⟩
      by_cases h : mulB b y = some c
      · rw [if_pos (hiff.mpr h),if_pos h]; rfl
      · rw [if_neg (fun hh => h (hiff.mp hh)),if_neg h]; rfl) }
def nuF1 (M : Type) [AddCommGroup M] [Module Λ M] : nuMod (F1 M) →ₗ[Λ] F1 (nuMod M) :=
  let toAdd : nuMod (F1 M) →+ F1 (nuMod M) :=
    { toFun := fun x => ofFun1 (fun p => ⟨z47 x.val (nuI1 p)⟩) (fun p => by
        apply nuMod.ext
        change ν (eΛ (rev (arrB p.1.1).src)) • z47 x.val (nuI1 p) = z47 x.val (nuI1 p)
        rw [ν_eΛ]
        have hsrc : rev (arrB (nuI1 p).1.1).src = rev (rev (arrB p.1.1).src) := by
          dsimp [nuI1]; rw [z337]; rfl
        rw [← hsrc]
        exact z146 x.val (nuI1 p))
      map_zero' := z37 (by funext p; rfl)
      map_add' := fun x y => z37 (by funext p; rfl) }
  { toFun := toAdd
    map_add' := toAdd.map_add
    map_smul' := z57 toAdd fun b x => z37 (by
      funext p
      apply nuMod.ext
      change z47 (ν (z12 b) • x.val) (nuI1 p) = (z47 (z12 b • toAdd x) p).val
      rw [z230,z73,z73]
      let ev : nuMod M →+ M := { toFun := nuMod.val,map_zero' := rfl,map_add' := fun _ _ => rfl }
      change _ = ev (∑ y : Bv p.1.2.src,if mulB b y.1 = some p.1.2 then
        z47 (toAdd x) ⟨(p.1.1,y.1),p.2.trans y.2.symm⟩ else 0)
      rw [map_sum]
      let eBv : Bv p.1.2.src ≃ Bv (nuI1 p).1.2.src :=
        ⟨fun y => ⟨nuB y.1,by change rev y.1.src = rev p.1.2.src; rw [y.2]⟩,
         fun y => ⟨nuB y.1,by
           have hy : y.1.src = rev p.1.2.src := y.2
           change rev y.1.src = p.1.2.src; rw [hy,z104]⟩,
         fun y => Subtype.ext (z19 y.1),
         fun y => Subtype.ext (z19 y.1)⟩
      rw [← eBv.sum_comp]
      refine sum_congr rfl fun y _ => ?_
      change (if mulB (nuB b) (nuB y.1) = some (nuB p.1.2) then
          z47 x.val (nuI1 ⟨(p.1.1,y.1),p.2.trans y.2.symm⟩) else 0) =
        ev (if mulB b y.1 = some p.1.2 then
          z47 (toAdd x) ⟨(p.1.1,y.1),p.2.trans y.2.symm⟩ else 0)
      have hiff : mulB (nuB b) (nuB y.1) = some (nuB p.1.2) ↔ mulB b y.1 = some p.1.2 := by
        rw [z187]
        cases h : mulB b y.1 with
        | none => simp
        | some z =>
          simp only [Option.map_some,Option.some.injEq]
          exact ⟨fun hz => by rw [← z19 z,hz,z19],fun hz => by rw [hz]⟩
      by_cases h : mulB b y.1 = some p.1.2
      · rw [if_pos (hiff.mpr h),if_pos h]; rfl
      · rw [if_neg (fun hh => h (hiff.mp hh)),if_neg h]; rfl) }
lemma z201 {I J : Type} [Fintype I] [DecidableEq J] {M : Type}
    [AddCommGroup M] [Module Λ M] (le : (J × B) → (J × B) → Bool)
    (nuI : I → I) (hnuI : ∀ i,nuI (nuI i) = i)
    (nuJ : J → J) (hnuJ : ∀ j,nuJ (nuJ j) = j)
    (op : I → List (J × B))
    (hop : ∀ i : I,z9 le ((op i).map fun p => (nuJ p.1,nuB p.2)) =
      z9 le (op (nuI i)))
    (g : I → M) (j : J) :
    (⟨z4 op g (nuJ j)⟩ : nuMod M) =
      z4 op (fun i => (⟨g (nuI i)⟩ : nuMod M)) j := by
  have h1 : ∀ (L : List (J × B)) (m : M),
      (⟨z8 m L (nuJ j)⟩ : nuMod M) =
        z8 (⟨m⟩ : nuMod M) (L.map fun p => (nuJ p.1,nuB p.2)) j := by
    intro L m
    induction L with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.map_cons,z8,Pi.add_apply]
      apply nuMod.ext
      change z49 m p (nuJ j) + z8 m ps (nuJ j) =
        (z49 (⟨m⟩ : nuMod M) (nuJ p.1,nuB p.2) j).val +
        (z8 (⟨m⟩ : nuMod M) (ps.map fun q => (nuJ q.1,nuB q.2)) j).val
      rw [← congrArg nuMod.val ih]
      congr 1
      unfold z49
      have hiff : nuJ j = p.1 ↔ j = nuJ p.1 :=
        ⟨fun h => by rw [← h,hnuJ],fun h => by rw [h,hnuJ]⟩
      by_cases h : j = nuJ p.1
      · rw [if_pos (hiff.mpr h),if_pos h]
        change z12 p.2 • m = ν (z12 (nuB p.2)) • m
        rw [z230,z19]
      · rw [if_neg (fun hh => h (hiff.mp hh)),if_neg h]; rfl
  unfold z4
  rw [Finset.sum_apply,Finset.sum_apply]
  let eI : I ≃ I := ⟨nuI,nuI,hnuI,hnuI⟩
  rw [← eI.sum_comp]
  apply nuMod.ext
  let ev : nuMod M →+ M := { toFun := nuMod.val,map_zero' := rfl,map_add' := fun _ _ => rfl }
  change ∑ i : I,z8 (g (nuI i)) (op (nuI i)) (nuJ j) =
    ev (∑ i : I,z8 (⟨g (nuI i)⟩ : nuMod M) (op i) j)
  rw [map_sum]
  refine sum_congr rfl fun i _ => ?_
  have h2 := congrArg nuMod.val (h1 (op (nuI i)) (g (nuI i)))
  dsimp only [ev] at *
  rw [h2]
  have h3 := congrArg (fun (f : J → nuMod M) => (f j).val)
    (z81 le (⟨g (nuI i)⟩ : nuMod M) ((op (nuI i)).map fun p => (nuJ p.1,nuB p.2)))
  have h4 := congrArg (fun (f : J → nuMod M) => (f j).val)
    (z81 le (⟨g (nuI i)⟩ : nuMod M) (op (nuI (nuI i))))
  rw [← h3,hop (nuI i),h4,hnuI i]
  rfl
lemma z317 (M : Type) [AddCommGroup M] [Module Λ M] [Finite M] :
    ∃ (a0 : (z6 M).P0⟦(1 : ℤ)⟧ ⟶ (z6 (nuMod M)).P0)
      (a1 : (z6 M).P1⟦(1 : ℤ)⟧ ⟶ (z6 (nuMod M)).P1)
      (a2 : (z6 M).P2⟦(1 : ℤ)⟧ ⟶ (z6 (nuMod M)).P2),
      a0.hom.comp ((z3 (z6 M).P0).toLinearMap.comp (nuMap (z6 M).ι)) =
        (z6 (nuMod M)).ι ∧
      comp ((z6 M).d0⟦(1 : ℤ)⟧') a1 =
        comp a0 (z6 (nuMod M)).d0 ∧
      comp ((z6 M).d1⟦(1 : ℤ)⟧') a2 =
        comp a1 (z6 (nuMod M)).d1 ∧
      (z6 (nuMod M)).π.comp a2.hom =
        (nuMap (z6 M).π).comp (z3 (z6 M).P2).symm.toLinearMap := by
  let a0 : (z6 M).P0⟦(1 : ℤ)⟧ ⟶ (z6 (nuMod M)).P0 :=
    ⟨(z18 (nuMod M)).symm.toLinearMap.comp
      ((nuF0 M).comp ((nuMap (z18 M).toLinearMap).comp
        (z3 (z6 M).P0).symm.toLinearMap))⟩
  let a1 : (z6 M).P1⟦(1 : ℤ)⟧ ⟶ (z6 (nuMod M)).P1 :=
    ⟨(z50 (nuMod M)).symm.toLinearMap.comp
      ((nuF1 M).comp ((nuMap (z50 M).toLinearMap).comp
        (z3 (z6 M).P1).symm.toLinearMap))⟩
  refine ⟨a0,a1,a0,?_,?_,?_,?_⟩
  · apply LinearMap.ext; intro x
    change (z18 (nuMod M)).symm
      (nuF0 M (nuMap (z18 M).toLinearMap ((z3 (z22 (V0 M))).symm
        (z3 (z22 (V0 M)) (nuMap ((z18 M).symm.toLinearMap.comp (ιF M)) x))))) =
      (z18 (nuMod M)).symm (ιF (nuMod M) x)
    rw [(z3 (z22 (V0 M))).symm_apply_apply]
    congr 1
    apply z14; funext c
    change (⟨z23 ((z18 M) ((z18 M).symm (ιF M x.val))) (nuB c)⟩ : nuMod M) =
      z4 z101 (fun _ => x) c
    rw [(z18 M).apply_symm_apply]
    change (⟨z4 z101 (fun _ => x.val) (nuB c)⟩ : nuMod M) =
      z4 z101 (fun _ => x) c
    rw [z94,z94]
    apply nuMod.ext
    change z12 (dualB (nuB c)) • x.val = ν (z12 (dualB c)) • x.val
    rw [z230,dualB_nuB]
  · apply FP.hom_ext; intro x
    change (z50 (nuMod M)).symm
      (nuF1 M (nuMap (z50 M).toLinearMap ((z3 (z22 (V1 M))).symm
        (z3 (z22 (V1 M))
          (nuMap ((z50 M).symm.toLinearMap.comp ((d0F M).comp (z18 M).toLinearMap))
            ((z3 (z22 (V0 M))).symm x)))))) =
      (z50 (nuMod M)).symm
        (d0F (nuMod M) ((z18 (nuMod M)) ((z18 (nuMod M)).symm
          (nuF0 M (nuMap (z18 M).toLinearMap ((z3 (z22 (V0 M))).symm x))))))
    rw [(z3 (z22 (V1 M))).symm_apply_apply,(z18 (nuMod M)).apply_symm_apply]
    congr 1
    apply z37; funext p
    change (⟨z47 ((z50 M) ((z50 M).symm
        (d0F M (z18 M ((z3 (z22 (V0 M))).symm x).val)))) (nuI1 p)⟩ : nuMod M) =
      z4 d0Col (fun c => (⟨z23 (z18 M ((z3 (z22 (V0 M))).symm x).val) (nuB c)⟩ : nuMod M)) p
    rw [(z50 M).apply_symm_apply]
    exact z201 (z77 leI1 leB) nuB z19 nuI1 z360 d0Col check_d0_nu
      (z23 (z18 M ((z3 (z22 (V0 M))).symm x).val)) p
  · apply FP.hom_ext; intro x
    change (z18 (nuMod M)).symm
      (nuF0 M (nuMap (z18 M).toLinearMap ((z3 (z22 (V0 M))).symm
        (z3 (z22 (V0 M))
          (nuMap ((z18 M).symm.toLinearMap.comp ((d1F M).comp (z50 M).toLinearMap))
            ((z3 (z22 (V1 M))).symm x)))))) =
      (z18 (nuMod M)).symm
        (d1F (nuMod M) ((z50 (nuMod M)) ((z50 (nuMod M)).symm
          (nuF1 M (nuMap (z50 M).toLinearMap ((z3 (z22 (V1 M))).symm x))))))
    rw [(z3 (z22 (V0 M))).symm_apply_apply,(z50 (nuMod M)).apply_symm_apply]
    congr 1
    apply z14; funext c
    change (⟨z23 ((z18 M) ((z18 M).symm
        (d1F M (z50 M ((z3 (z22 (V1 M))).symm x).val)))) (nuB c)⟩ : nuMod M) =
      z4 d1Col (fun p => (⟨z47 (z50 M ((z3 (z22 (V1 M))).symm x).val) (nuI1 p)⟩ : nuMod M)) c
    rw [(z18 M).apply_symm_apply]
    exact z201 (z77 leB leB) nuI1 z360 nuB z19 d1Col check_d1_nu
      (z47 (z50 M ((z3 (z22 (V1 M))).symm x).val)) c
  · apply LinearMap.ext; intro x
    apply nuMod.ext; apply nuMod.ext
    change (z4 piCol (z23 ((z18 (nuMod M)) ((z18 (nuMod M)).symm
      (nuF0 M (nuMap (z18 M).toLinearMap ((z3 (z22 (V0 M))).symm x)))))) ()).val =
      z4 piCol (z23 (z18 M ((z3 (z22 (V0 M))).symm x).val)) ()
    rw [(z18 (nuMod M)).apply_symm_apply]
    change (z4 piCol (fun c => (⟨z23 (z18 M ((z3 (z22 (V0 M))).symm x).val) (nuB c)⟩ : nuMod M)) ()).val = _
    rw [z121,z121]
    let ev : nuMod M →+ M := { toFun := nuMod.val,map_zero' := rfl,map_add' := fun _ _ => rfl }
    change ev (∑ c : B,z12 (nuB c) • (⟨z23 (z18 M ((z3 (z22 (V0 M))).symm x).val) (nuB c)⟩ : nuMod M)) = _
    rw [map_sum]
    let eB_eq : B ≃ B := ⟨nuB,nuB,z19,z19⟩
    rw [← eB_eq.sum_comp]
    refine sum_congr rfl fun c _ => ?_
    dsimp only [ev,eB_eq]
    change ν (z12 (nuB (nuB c))) • z23 (z18 M ((z3 (z22 (V0 M))).symm x).val) (nuB (nuB c)) = _
    rw [z19,z230]
def z2Lin {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (r : ZMod 2) (f : M →ₗ[Λ] N) : M →ₗ[Λ] N :=
  if r = 0 then 0 else f
lemma z2Lin_zero {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (f : M →ₗ[Λ] N) : z2Lin 0 f = 0 := by simp [z2Lin]
lemma z280 {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (f : M →ₗ[Λ] N) : z2Lin 1 f = f := by simp [z2Lin]
lemma z43 {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (r : ZMod 2) (f : M →ₗ[Λ] N) (m : M) : z2Lin r f m = z16 r (f m) := by
  by_cases hr : r = 0 <;> simp [z2Lin,z16,hr]
lemma z54 {M N P : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] [AddCommGroup P] [Module Λ P]
    (g : N →ₗ[Λ] P) (r : ZMod 2) (f : M →ₗ[Λ] N) :
    g.comp (z2Lin r f) = z2Lin r (g.comp f) := by
  by_cases hr : r = 0 <;> simp [z2Lin,hr]
lemma z30 {M N P : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] [AddCommGroup P] [Module Λ P]
    (r : ZMod 2) (g : N →ₗ[Λ] P) (f : M →ₗ[Λ] N) :
    (z2Lin r g).comp f = z2Lin r (g.comp f) := by
  by_cases hr : r = 0 <;> simp [z2Lin,hr]
lemma z309 {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (r s : ZMod 2) (f : M →ₗ[Λ] N) : z2Lin (r + s) f = z2Lin r f + z2Lin s f := by
  apply LinearMap.ext; intro m
  simp only [LinearMap.add_apply,z43,z103]
lemma z299 {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (r : ZMod 2) (f g : M →ₗ[Λ] N) : z2Lin r (f + g) = z2Lin r f + z2Lin r g := by
  by_cases hr : r = 0 <;> simp [z2Lin,hr]
lemma z2Lin_mul {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (r s : ZMod 2) (f : M →ₗ[Λ] N) : z2Lin (r * s) f = z2Lin r (z2Lin s f) := by
  rcases z33 r with rfl | rfl <;> rcases z33 s with rfl | rfl <;> simp [z2Lin]
lemma z63 {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (r : ZMod 2) : z2Lin r (0 : M →ₗ[Λ] N) = 0 := by
  by_cases hr : r = 0 <;> simp [z2Lin,hr]
lemma StableEq.sum {ι : Type*} {M N : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] (s : Finset ι) (f g : ι → M →ₗ[Λ] N)
    (h : ∀ i ∈ s,StableEq (f i) (g i)) : StableEq (∑ i ∈ s,f i) (∑ i ∈ s,g i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using StableEq.refl (0 : M →ₗ[Λ] N)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    exact StableEq.add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
lemma z41 {ι : Type*} {M N P : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] [AddCommGroup P] [Module Λ P]
    (s : Finset ι) (f : ι → N →ₗ[Λ] P) (g : M →ₗ[Λ] N) :
    (∑ i ∈ s,f i).comp g = ∑ i ∈ s,(f i).comp g := by
  apply LinearMap.ext; intro m; simp
lemma z42 {ι : Type*} {M N P : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] [AddCommGroup P] [Module Λ P]
    (f : N →ₗ[Λ] P) (s : Finset ι) (g : ι → M →ₗ[Λ] N) :
    f.comp (∑ i ∈ s,g i) = ∑ i ∈ s,f.comp (g i) := by
  apply LinearMap.ext; intro m; simp [map_sum]
lemma StableEq.z2Lin {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (r : ZMod 2) {f g : M →ₗ[Λ] N} (h : StableEq f g) : StableEq (MO31809.z2Lin r f) (MO31809.z2Lin r g) := by
  by_cases hr : r = 0
  · simp [MO31809.z2Lin,hr]; exact StableEq.refl 0
  · simpa [MO31809.z2Lin,hr] using h
def z173 (v : Fin 5) : FP := ⟨fun w => if w = v then 1 else 0⟩
def z227 (v : Fin 5) : (z173 v).Mod ≃ₗ[Λ] Pv v where
  toFun x := x v ⟨0,by simp [z173]⟩
  invFun y w i := if h : w = v then h ▸ y else 0
  left_inv x := by
    funext w i
    by_cases h : w = v
    · subst h
      have hi : i = ⟨0,by simp [z173]⟩ := by
        have hlt : i.1 < 1 := by simpa [z173] using i.2
        ext; change i.1 = 0; omega
      subst hi; simp
    · exfalso; simpa [z173,h] using i.2
  right_inv y := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
lemma z70 (v : Fin 5) {M N : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] {f : M →ₗ[Λ] N}
    (p : M →ₗ[Λ] Pv v) (q : Pv v →ₗ[Λ] N) (h : f = q.comp p) : StableEq f 0 :=
  ⟨z173 v,(z227 v).symm.toLinearMap.comp p,
    q.comp (z227 v).toLinearMap,by
      rw [sub_zero,h]; apply LinearMap.ext; intro m; simp⟩
def z342 {u v : Fin 5} (m : B) (hm_src : m.src = v) (hm_tgt : m.tgt = u) :
    Pv u →ₗ[Λ] Pv v :=
  (z29 u).symm ⟨z45 ⟨m,hm_src⟩,by
    rw [eΛ,z27,z26,if_pos hm_tgt]; dsimp only; rw [dif_pos hm_src]⟩
lemma z204 {u v : Fin 5} (m : B) (hm_src : m.src = v) (hm_tgt : m.tgt = u) :
    z342 m hm_src hm_tgt (genPv u) = z45 ⟨m,hm_src⟩ :=
  congrArg Subtype.val ((z29 u).apply_symm_apply ⟨z45 ⟨m,hm_src⟩,_⟩)
lemma z149 {u v : Fin 5} (m : B) (hm_src : m.src = v) (hm_tgt : m.tgt = u) (b : Bv u) :
    z342 m hm_src hm_tgt (z45 b) =
      match mulB b.1 m with
      | some c => if h : c.src = v then z45 ⟨c,h⟩ else 0
      | none => 0 := by
  rw [← z24 b,LinearMap.map_smul,z204,z27]
lemma z244 {u v : Fin 5} (m : B) (hm_src : m.src = v) (hm_tgt : m.tgt = u)
    (x : Pv u) (c : Bv v) :
    (z342 m hm_src hm_tgt x).val c = ∑ y : Bv u,if mulB y.1 m = some c.1 then x.val y else 0 := by
  conv_lhs => rw [z202 x,map_sum]
  rw [Pv.sum_val]
  refine sum_congr rfl fun y _ => ?_
  rw [z53,Pv.z2smul_val,z149]
  cases h : mulB y.1 m with
  | none => simp
  | some d =>
    have hd : d.src = v := (z71 h).trans hm_src
    dsimp only; rw [dif_pos hd,basisPv_val]
    by_cases hcd : c.1 = d
    · have hcd' : c = ⟨d,hd⟩ := Subtype.ext hcd
      subst hcd'; simp
    · have hcd' : c ≠ ⟨d,hd⟩ := fun hh => hcd (congrArg Subtype.val hh)
      have hdc : d ≠ c.1 := Ne.symm hcd
      simp [hdc,hcd']
def qB : B := mkB 1 3 2 (by decide)
def iotaB : B := mkB 3 1 0 (by decide)
def alphaB : B := mkB 3 3 1 (by decide)
def alphapB : B := mkB 1 1 1 (by decide)
@[simp] lemma qB_src : qB.src = 1 := rfl
@[simp] lemma qB_tgt : qB.tgt = 3 := rfl
@[simp] lemma iotaB_src : iotaB.src = 3 := rfl
@[simp] lemma iotaB_tgt : iotaB.tgt = 1 := rfl
@[simp] lemma alphaB_src : alphaB.src = 3 := rfl
@[simp] lemma alphaB_tgt : alphaB.tgt = 3 := rfl
@[simp] lemma alphapB_src : alphapB.src = 1 := rfl
@[simp] lemma alphapB_tgt : alphapB.tgt = 1 := rfl
abbrev qBv : Bv 1 := ⟨qB,qB_src⟩
abbrev iotaBv : Bv 3 := ⟨iotaB,iotaB_src⟩
abbrev alphaBv : Bv 3 := ⟨alphaB,alphaB_src⟩
abbrev alphapBv : Bv 1 := ⟨alphapB,alphapB_src⟩
abbrev z161 : Bv 3 := ⟨socB 3,rfl⟩
abbrev z323 : Bv 1 := ⟨socB 1,rfl⟩
@[simp] lemma socB_src (v : Fin 5) : (socB v).src = v := rfl
lemma z64 (p : B → Bool) (h : allB.all p = true) : ∀ b : B,p b = true :=
  fun b => List.all_eq_true.mp h b (z35 b)
def z115 : Λ := z12 qB
def z11 : Λ := z12 iotaB
def z108 : Λ := z12 alphaB
def z15 : Λ := z12 alphapB
def rmul_q : Pv 3 →ₗ[Λ] Pv 1 := z342 (u := 3) (v := 1) qB qB_src qB_tgt
def rmul_iota : Pv 1 →ₗ[Λ] Pv 3 := z342 (u := 1) (v := 3) iotaB iotaB_src iotaB_tgt
def rmul_alpha : Pv 3 →ₗ[Λ] Pv 3 := z342 (u := 3) (v := 3) alphaB alphaB_src alphaB_tgt
def rmul_alphap : Pv 1 →ₗ[Λ] Pv 1 := z342 (u := 1) (v := 1) alphapB alphapB_src alphapB_tgt
lemma z175 : rmul_q (genPv 3) = z45 qBv := z204 (u := 3) (v := 1) qB qB_src qB_tgt
lemma z133 : rmul_iota (genPv 1) = z45 iotaBv := z204 (u := 1) (v := 3) iotaB iotaB_src iotaB_tgt
lemma z184 : rmul_alpha (genPv 3) = z45 alphaBv := z204 (u := 3) (v := 3) alphaB alphaB_src alphaB_tgt
lemma z130 : rmul_alphap (genPv 1) = z45 alphapBv := z204 (u := 1) (v := 1) alphapB alphapB_src alphapB_tgt
lemma z182 (b : Bv 3) : rmul_q (z45 b) =
    match mulB b.1 qB with | some c => if h : c.src = 1 then z45 ⟨c,h⟩ else 0 | none => 0 :=
  z149 (u := 3) (v := 1) qB qB_src qB_tgt b
lemma z169 (b : Bv 1) : rmul_iota (z45 b) =
    match mulB b.1 iotaB with | some c => if h : c.src = 3 then z45 ⟨c,h⟩ else 0 | none => 0 :=
  z149 (u := 1) (v := 3) iotaB iotaB_src iotaB_tgt b
lemma z148 (b : Bv 3) : rmul_alpha (z45 b) =
    match mulB b.1 alphaB with | some c => if h : c.src = 3 then z45 ⟨c,h⟩ else 0 | none => 0 :=
  z149 (u := 3) (v := 3) alphaB alphaB_src alphaB_tgt b
lemma z110 (b : Bv 1) : rmul_alphap (z45 b) =
    match mulB b.1 alphapB with | some c => if h : c.src = 1 then z45 ⟨c,h⟩ else 0 | none => 0 :=
  z149 (u := 1) (v := 1) alphapB alphapB_src alphapB_tgt b
lemma z174 (x : Pv 3) (c : Bv 1) :
    (rmul_q x).val c = ∑ y : Bv 3,if mulB y.1 qB = some c.1 then x.val y else 0 :=
  z244 (u := 3) (v := 1) qB qB_src qB_tgt x c
lemma z117 (x : Pv 1) (c : Bv 3) :
    (rmul_iota x).val c = ∑ y : Bv 1,if mulB y.1 iotaB = some c.1 then x.val y else 0 :=
  z244 (u := 1) (v := 3) iotaB iotaB_src iotaB_tgt x c
lemma z183 (x : Pv 3) (c : Bv 3) :
    (rmul_alpha x).val c = ∑ y : Bv 3,if mulB y.1 alphaB = some c.1 then x.val y else 0 :=
  z244 (u := 3) (v := 3) alphaB alphaB_src alphaB_tgt x c
lemma z129 (x : Pv 1) (c : Bv 1) :
    (rmul_alphap x).val c = ∑ y : Bv 1,if mulB y.1 alphapB = some c.1 then x.val y else 0 :=
  z244 (u := 1) (v := 1) alphapB alphapB_src alphapB_tgt x c
lemma nuB_qB : nuB qB = iotaB := by decide
lemma z361 : nuB iotaB = qB := by decide
lemma nuB_alphaB : nuB alphaB = alphapB := by decide
lemma nuB_alphapB : nuB alphapB = alphaB := by decide
lemma z308 : dualB iotaB = alphapB := by decide
lemma dualB_qB : dualB qB = alphaB := by decide
lemma z334 : dualB alphapB = qB := by decide
lemma z355 : dualB alphaB = iotaB := by decide
lemma z163 : mulB iotaB qB = none := by decide
lemma z208 : mulB qB iotaB = none := by decide
lemma z257 : mulB alphaB alphaB = none := by decide
lemma z152 : mulB alphapB alphapB = none := by decide
lemma z98 : mulB alphaB qB = some (socB 1) := by decide
lemma z105 : mulB qB alphapB = some (socB 1) := by decide
lemma z76 : mulB alphapB iotaB = some (socB 3) := by decide
lemma z84 : mulB iotaB alphaB = some (socB 3) := by decide
lemma z142 : rmul_q.comp rmul_iota = 0 := by
  apply (z29 1).injective; apply Subtype.ext
  change rmul_q (rmul_iota (genPv 1)) = 0
  rw [z133,z182,show iotaBv.1 = iotaB from rfl,z163]
lemma z143 : rmul_iota.comp rmul_q = 0 := by
  apply (z29 3).injective; apply Subtype.ext
  change rmul_iota (rmul_q (genPv 3)) = 0
  rw [z175,z169,show qBv.1 = qB from rfl,z208]
lemma z324 : rmul_alpha.comp rmul_alpha = 0 := by
  apply (z29 3).injective; apply Subtype.ext
  change rmul_alpha (rmul_alpha (genPv 3)) = 0
  rw [z184,z148,show alphaBv.1 = alphaB from rfl,z257]
lemma z243 : rmul_alphap.comp rmul_alphap = 0 := by
  apply (z29 1).injective; apply Subtype.ext
  change rmul_alphap (rmul_alphap (genPv 1)) = 0
  rw [z130,z110,show alphapBv.1 = alphapB from rfl,z152]
lemma z90 : rmul_q.comp rmul_alpha = rmul_alphap.comp rmul_q := by
  apply (z29 3).injective; apply Subtype.ext
  change rmul_q (rmul_alpha (genPv 3)) = rmul_alphap (rmul_q (genPv 3))
  rw [z184,z175,z182,z110,
    show alphaBv.1 = alphaB from rfl,show qBv.1 = qB from rfl,
    z98,z105]
lemma z55 : rmul_iota.comp rmul_alphap = rmul_alpha.comp rmul_iota := by
  apply (z29 1).injective; apply Subtype.ext
  change rmul_iota (rmul_alphap (genPv 1)) = rmul_alpha (rmul_iota (genPv 1))
  rw [z130,z133,z169,z148,
    show alphapBv.1 = alphapB from rfl,show iotaBv.1 = iotaB from rfl,
    z76,z84]
lemma z209 :
    allB.all (fun c =>
      if c.src == 3 then
        (mulB c qB == none) == (allB.any fun y => y.src == 1 && mulB y iotaB == some c)
      else true) = true := by decide
lemma z165 :
    allB.all (fun c =>
      if c.src == 1 then
        (mulB c iotaB == none) == (allB.any fun y => y.src == 3 && mulB y qB == some c)
      else true) = true := by decide
lemma z68 :
    allB.all (fun y1 => allB.all (fun y2 =>
      if y1.src == 3 && y2.src == 3 && mulB y1 qB != none && mulB y1 qB == mulB y2 qB then
        y1 == y2
      else true)) = true := by decide
lemma z85 :
    allB.all (fun y1 => allB.all (fun y2 =>
      if y1.src == 1 && y2.src == 1 && mulB y1 iotaB != none && mulB y1 iotaB == mulB y2 iotaB then
        y1 == y2
      else true)) = true := by decide
lemma z96 (x : Pv 3) :
    rmul_q x = 0 ↔ ∀ c : Bv 3,mulB c.1 qB ≠ none → x.val c = 0 := by
  constructor
  · intro hx c hc
    cases hd : mulB c.1 qB with
    | none => exact absurd hd hc
    | some d =>
      have hd_src : d.src = 1 := (z71 hd).trans rfl
      have h0 : (rmul_q x).val ⟨d,hd_src⟩ = 0 := by rw [hx]; rfl
      rw [z174] at h0
      rw [sum_eq_single c] at h0
      · simpa [hd] using h0
      · intro y _ hy
        rw [if_neg]; intro hym
        have hb := List.all_eq_true.mp (List.all_eq_true.mp z68 y.1 (z35 y.1))
          c.1 (z35 c.1)
        have hcond : (y.1.src == 3 && c.1.src == 3 && mulB y.1 qB != none && mulB y.1 qB == mulB c.1 qB) = true := by
          simp [y.2,c.2,hym,hd]
        rw [if_pos hcond] at hb
        exact hy (Subtype.ext (beq_iff_eq.mp hb))
      · intro hn; exact absurd (mem_univ _) hn
  · intro hx
    apply xP; ext d
    rw [z174,Pv.zero_val]
    refine sum_eq_zero fun y _ => ?_
    by_cases hy : mulB y.1 qB = some d.1
    · rw [if_pos hy]; exact hx y (by rw [hy]; simp)
    · rw [if_neg hy]
lemma z221 (x : Pv 1) :
    rmul_iota x = 0 ↔ ∀ c : Bv 1,mulB c.1 iotaB ≠ none → x.val c = 0 := by
  constructor
  · intro hx c hc
    cases hd : mulB c.1 iotaB with
    | none => exact absurd hd hc
    | some d =>
      have hd_src : d.src = 3 := (z71 hd).trans rfl
      have h0 : (rmul_iota x).val ⟨d,hd_src⟩ = 0 := by rw [hx]; rfl
      rw [z117] at h0
      rw [sum_eq_single c] at h0
      · simpa [hd] using h0
      · intro y _ hy
        rw [if_neg]; intro hym
        have hb := List.all_eq_true.mp (List.all_eq_true.mp z85 y.1 (z35 y.1))
          c.1 (z35 c.1)
        have hcond : (y.1.src == 1 && c.1.src == 1 && mulB y.1 iotaB != none && mulB y.1 iotaB == mulB c.1 iotaB) = true := by
          simp [y.2,c.2,hym,hd]
        rw [if_pos hcond] at hb
        exact hy (Subtype.ext (beq_iff_eq.mp hb))
      · intro hn; exact absurd (mem_univ _) hn
  · intro hx
    apply xP; ext d
    rw [z117,Pv.zero_val]
    refine sum_eq_zero fun y _ => ?_
    by_cases hy : mulB y.1 iotaB = some d.1
    · rw [if_pos hy]; exact hx y (by rw [hy]; simp)
    · rw [if_neg hy]
lemma z273 : ExactAt rmul_iota rmul_q := by
  ext x
  simp only [LinearMap.mem_range,LinearMap.mem_ker]
  constructor
  · rintro ⟨y,rfl⟩
    exact congrArg (fun (f : Pv 1 →ₗ[Λ] Pv 1) => f y) z142
  · intro hx
    have hker := (z96 x).mp hx
    let y : Pv 1 := ⟨fun b =>
      match h : mulB b.1 iotaB with
      | some c => x.val ⟨c,(z71 h).trans rfl⟩
      | none => 0⟩
    refine ⟨y,?_⟩
    apply xP; ext c
    rw [z117]
    by_cases hq : mulB c.1 qB = none
    · have hchk := List.all_eq_true.mp z209 c.1 (z35 c.1)
      simp only [c.2,beq_self_eq_true,↓reduceIte,hq,beq_iff_eq] at hchk
      obtain ⟨b0,_,hb0⟩ := List.any_eq_true.mp hchk.symm
      simp only [Bool.and_eq_true,beq_iff_eq] at hb0
      rw [sum_eq_single ⟨b0,hb0.1⟩]
      · rw [if_pos hb0.2]
        dsimp only [y]
        split
        next c' hc' =>
          have hcc : c' = c.1 := Option.some.inj (hc'.symm.trans hb0.2)
          congr 1; exact Subtype.ext hcc
        next hc' => rw [hb0.2] at hc'; cases hc'
      · intro b _ hb
        rw [if_neg]; intro hbm
        have huniq := List.all_eq_true.mp (List.all_eq_true.mp z85 b.1 (z35 b.1))
          b0 (z35 b0)
        have hcond : (b.1.src == 1 && b0.src == 1 && mulB b.1 iotaB != none && mulB b.1 iotaB == mulB b0 iotaB) = true := by
          simp [b.2,hb0.1,hbm,hb0.2]
        rw [if_pos hcond] at huniq
        exact hb (Subtype.ext (beq_iff_eq.mp huniq))
      · intro hn; exact absurd (mem_univ _) hn
    · rw [hker c hq]
      refine sum_eq_zero fun b _ => ?_
      rw [if_neg]; intro hbm
      have hchk := List.all_eq_true.mp z209 c.1 (z35 c.1)
      have hany : (allB.any fun z => z.src == 1 && mulB z iotaB == some c.1) = true :=
        List.any_eq_true.mpr ⟨b.1,z35 b.1,by simp [b.2,hbm]⟩
      simp only [c.2,beq_self_eq_true,↓reduceIte,hany,beq_iff_eq] at hchk
      exact hq hchk
lemma z198 : ExactAt rmul_q rmul_iota := by
  ext x
  simp only [LinearMap.mem_range,LinearMap.mem_ker]
  constructor
  · rintro ⟨y,rfl⟩
    exact congrArg (fun (f : Pv 3 →ₗ[Λ] Pv 3) => f y) z143
  · intro hx
    have hker := (z221 x).mp hx
    let y : Pv 3 := ⟨fun b =>
      match h : mulB b.1 qB with
      | some c => x.val ⟨c,(z71 h).trans rfl⟩
      | none => 0⟩
    refine ⟨y,?_⟩
    apply xP; ext c
    rw [z174]
    by_cases hi : mulB c.1 iotaB = none
    · have hchk := List.all_eq_true.mp z165 c.1 (z35 c.1)
      simp only [c.2,beq_self_eq_true,↓reduceIte,hi,beq_iff_eq] at hchk
      obtain ⟨b0,_,hb0⟩ := List.any_eq_true.mp hchk.symm
      simp only [Bool.and_eq_true,beq_iff_eq] at hb0
      rw [sum_eq_single ⟨b0,hb0.1⟩]
      · rw [if_pos hb0.2]
        dsimp only [y]
        split
        next c' hc' =>
          have hcc : c' = c.1 := Option.some.inj (hc'.symm.trans hb0.2)
          congr 1; exact Subtype.ext hcc
        next hc' => rw [hb0.2] at hc'; cases hc'
      · intro b _ hb
        rw [if_neg]; intro hbm
        have huniq := List.all_eq_true.mp (List.all_eq_true.mp z68 b.1 (z35 b.1))
          b0 (z35 b0)
        have hcond : (b.1.src == 3 && b0.src == 3 && mulB b.1 qB != none && mulB b.1 qB == mulB b0 qB) = true := by
          simp [b.2,hb0.1,hbm,hb0.2]
        rw [if_pos hcond] at huniq
        exact hb (Subtype.ext (beq_iff_eq.mp huniq))
      · intro hn; exact absurd (mem_univ _) hn
    · rw [hker c hi]
      refine sum_eq_zero fun b _ => ?_
      rw [if_neg]; intro hbm
      have hchk := List.all_eq_true.mp z165 c.1 (z35 c.1)
      have hany : (allB.any fun z => z.src == 3 && mulB z qB == some c.1) = true :=
        List.any_eq_true.mpr ⟨b.1,z35 b.1,by simp [b.2,hbm]⟩
      simp only [c.2,beq_self_eq_true,↓reduceIte,hany,beq_iff_eq] at hchk
      exact hi hchk
lemma z290 :
    allB.all (fun c => if c.src == 3 && c.tgt == 3 then (c == eB 3 || c == alphaB) else true) = true := by decide
lemma z292 :
    allB.all (fun c => if c.src == 1 && c.tgt == 1 then (c == eB 1 || c == alphapB) else true) = true := by decide
lemma z313 (f : Pv 3 →ₗ[Λ] Pv 3) :
    ∃ a b : ZMod 2,f = z2Lin a LinearMap.id + z2Lin b rmul_alpha := by
  let a := (f (genPv 3)).val ⟨eB 3,rfl⟩
  let b := (f (genPv 3)).val alphaBv
  refine ⟨a,b,?_⟩
  apply (z29 3).injective; apply Subtype.ext; apply xP; ext c
  change (f (genPv 3)).val c = (z2Lin a LinearMap.id (genPv 3) + z2Lin b rmul_alpha (genPv 3)).val c
  rw [Pv.add_val,z43,z43,Pv.z2smul_val,Pv.z2smul_val,LinearMap.id_apply,
    z184]
  have he3 : eΛ 3 • f (genPv 3) = f (genPv 3) := by rw [← f.map_smul,z79]
  have hc_tgt : (f (genPv 3)).val c = if c.1.tgt = 3 then (f (genPv 3)).val c else 0 := by
    have := congrArg (fun x : Pv 3 => x.val c) he3.symm
    rwa [z59] at this
  by_cases htgt : c.1.tgt = 3
  · have hchk := List.all_eq_true.mp z290 c.1 (z35 c.1)
    simp only [c.2,htgt,beq_self_eq_true,Bool.and_self,↓reduceIte,Bool.or_eq_true,
      beq_iff_eq] at hchk
    rcases hchk with h1 | h2
    · have hc' : c = ⟨eB 3,rfl⟩ := Subtype.ext h1
      subst hc'
      have hne : (⟨eB 3,rfl⟩ : Bv 3) ≠ alphaBv := by decide
      simp [genPv,a,hne]
    · have hc' : c = alphaBv := Subtype.ext h2
      subst hc'
      have hne : alphaBv ≠ (⟨eB 3,rfl⟩ : Bv 3) := by decide
      simp [genPv,b,hne]
  · rw [if_neg htgt] at hc_tgt
    have hne1 : c ≠ ⟨eB 3,rfl⟩ := fun h => htgt (by rw [h]; rfl)
    have hne2 : c ≠ alphaBv := fun h => htgt (by rw [h]; rfl)
    rw [hc_tgt]; simp [genPv,hne1,hne2]
lemma z314 (f : Pv 1 →ₗ[Λ] Pv 1) :
    ∃ a b : ZMod 2,f = z2Lin a LinearMap.id + z2Lin b rmul_alphap := by
  let a := (f (genPv 1)).val ⟨eB 1,rfl⟩
  let b := (f (genPv 1)).val alphapBv
  refine ⟨a,b,?_⟩
  apply (z29 1).injective; apply Subtype.ext; apply xP; ext c
  change (f (genPv 1)).val c = (z2Lin a LinearMap.id (genPv 1) + z2Lin b rmul_alphap (genPv 1)).val c
  rw [Pv.add_val,z43,z43,Pv.z2smul_val,Pv.z2smul_val,LinearMap.id_apply,
    z130]
  have he1 : eΛ 1 • f (genPv 1) = f (genPv 1) := by rw [← f.map_smul,z79]
  have hc_tgt : (f (genPv 1)).val c = if c.1.tgt = 1 then (f (genPv 1)).val c else 0 := by
    have := congrArg (fun x : Pv 1 => x.val c) he1.symm
    rwa [z59] at this
  by_cases htgt : c.1.tgt = 1
  · have hchk := List.all_eq_true.mp z292 c.1 (z35 c.1)
    simp only [c.2,htgt,beq_self_eq_true,Bool.and_self,↓reduceIte,Bool.or_eq_true,
      beq_iff_eq] at hchk
    rcases hchk with h1 | h2
    · have hc' : c = ⟨eB 1,rfl⟩ := Subtype.ext h1
      subst hc'
      have hne : (⟨eB 1,rfl⟩ : Bv 1) ≠ alphapBv := by decide
      simp [genPv,a,hne]
    · have hc' : c = alphapBv := Subtype.ext h2
      subst hc'
      have hne : alphapBv ≠ (⟨eB 1,rfl⟩ : Bv 1) := by decide
      simp [genPv,b,hne]
  · rw [if_neg htgt] at hc_tgt
    have hne1 : c ≠ ⟨eB 1,rfl⟩ := fun h => htgt (by rw [h]; rfl)
    have hne2 : c ≠ alphapBv := fun h => htgt (by rw [h]; rfl)
    rw [hc_tgt]; simp [genPv,hne1,hne2]
def nuPv3Equiv : nuMod (Pv 3) ≃ₗ[Λ] Pv 1 where
  toFun x := ⟨fun c => x.val.val ⟨nuB c.1,by change rev c.1.src = 3; rw [c.2]; rfl⟩⟩
  invFun y := ⟨⟨fun c => y.val ⟨nuB c.1,by change rev c.1.src = 1; rw [c.2]; rfl⟩⟩⟩
  left_inv x := by
    apply nuMod.ext; apply xP; ext c
    change x.val.val ⟨nuB (nuB c.1),_⟩ = x.val.val c
    congr 1; exact Subtype.ext (z19 c.1)
  right_inv y := by
    apply xP; ext c
    change y.val ⟨nuB (nuB c.1),_⟩ = y.val c
    congr 1; exact Subtype.ext (z19 c.1)
  map_add' _ _ := rfl
  map_smul' a x := (z358 3).map_smul a x
def nuPv1Equiv : nuMod (Pv 1) ≃ₗ[Λ] Pv 3 where
  toFun x := ⟨fun c => x.val.val ⟨nuB c.1,by change rev c.1.src = 1; rw [c.2]; rfl⟩⟩
  invFun y := ⟨⟨fun c => y.val ⟨nuB c.1,by change rev c.1.src = 3; rw [c.2]; rfl⟩⟩⟩
  left_inv x := by
    apply nuMod.ext; apply xP; ext c
    change x.val.val ⟨nuB (nuB c.1),_⟩ = x.val.val c
    congr 1; exact Subtype.ext (z19 c.1)
  right_inv y := by
    apply xP; ext c
    change y.val ⟨nuB (nuB c.1),_⟩ = y.val c
    congr 1; exact Subtype.ext (z19 c.1)
  map_add' _ _ := rfl
  map_smul' a x := (z358 1).map_smul a x
lemma z195 (x : nuMod (Pv 3)) :
    nuPv1Equiv (nuMap rmul_q x) = rmul_iota (nuPv3Equiv x) := by
  apply xP; ext c
  change (rmul_q x.val).val ⟨nuB c.1,_⟩ = (rmul_iota (nuPv3Equiv x)).val c
  rw [z174,z117]
  let eBv : Bv 1 ≃ Bv 3 :=
    ⟨fun y => ⟨nuB y.1,by change rev y.1.src = 3; rw [y.2]; rfl⟩,
     fun y => ⟨nuB y.1,by change rev y.1.src = 1; rw [y.2]; rfl⟩,
     fun y => Subtype.ext (z19 y.1),
     fun y => Subtype.ext (z19 y.1)⟩
  rw [← eBv.sum_comp]
  refine sum_congr rfl fun y _ => ?_
  dsimp [eBv,nuPv3Equiv]
  have hiff : mulB (nuB y.1) qB = some (nuB c.1) ↔ mulB y.1 iotaB = some c.1 := by
    rw [← z361,z187]
    cases h : mulB y.1 iotaB with
    | none => simp
    | some z =>
      simp only [Option.map_some,Option.some.injEq]
      exact ⟨fun hz => by rw [← z19 z,hz,z19],fun hz => by rw [hz]⟩
  by_cases h : mulB y.1 iotaB = some c.1
  · rw [if_pos (hiff.mpr h),if_pos h]; rfl
  · rw [if_neg (fun hh => h (hiff.mp hh)),if_neg h]
lemma z346 (x : nuMod (Pv 1)) :
    nuPv3Equiv (nuMap rmul_iota x) = rmul_q (nuPv1Equiv x) := by
  apply xP; ext c
  change (rmul_iota x.val).val ⟨nuB c.1,_⟩ = (rmul_q (nuPv1Equiv x)).val c
  rw [z117,z174]
  let eBv : Bv 3 ≃ Bv 1 :=
    ⟨fun y => ⟨nuB y.1,by change rev y.1.src = 1; rw [y.2]; rfl⟩,
     fun y => ⟨nuB y.1,by change rev y.1.src = 3; rw [y.2]; rfl⟩,
     fun y => Subtype.ext (z19 y.1),
     fun y => Subtype.ext (z19 y.1)⟩
  rw [← eBv.sum_comp]
  refine sum_congr rfl fun y _ => ?_
  dsimp [eBv,nuPv1Equiv]
  have hiff : mulB (nuB y.1) iotaB = some (nuB c.1) ↔ mulB y.1 qB = some c.1 := by
    rw [← nuB_qB,z187]
    cases h : mulB y.1 qB with
    | none => simp
    | some z =>
      simp only [Option.map_some,Option.some.injEq]
      exact ⟨fun hz => by rw [← z19 z,hz,z19],fun hz => by rw [hz]⟩
  by_cases h : mulB y.1 qB = some c.1
  · rw [if_pos (hiff.mpr h),if_pos h]; rfl
  · rw [if_neg (fun hh => h (hiff.mp hh)),if_neg h]
lemma z222 (x : nuMod (Pv 3)) :
    nuPv3Equiv (nuMap rmul_alpha x) = rmul_alphap (nuPv3Equiv x) := by
  apply xP; ext c
  change (rmul_alpha x.val).val ⟨nuB c.1,_⟩ = (rmul_alphap (nuPv3Equiv x)).val c
  rw [z183,z129]
  let eBv : Bv 1 ≃ Bv 3 :=
    ⟨fun y => ⟨nuB y.1,by change rev y.1.src = 3; rw [y.2]; rfl⟩,
     fun y => ⟨nuB y.1,by change rev y.1.src = 1; rw [y.2]; rfl⟩,
     fun y => Subtype.ext (z19 y.1),
     fun y => Subtype.ext (z19 y.1)⟩
  rw [← eBv.sum_comp]
  refine sum_congr rfl fun y _ => ?_
  dsimp [eBv,nuPv3Equiv]
  have hiff : mulB (nuB y.1) alphaB = some (nuB c.1) ↔ mulB y.1 alphapB = some c.1 := by
    rw [← nuB_alphapB,z187]
    cases h : mulB y.1 alphapB with
    | none => simp
    | some z =>
      simp only [Option.map_some,Option.some.injEq]
      exact ⟨fun hz => by rw [← z19 z,hz,z19],fun hz => by rw [hz]⟩
  by_cases h : mulB y.1 alphapB = some c.1
  · rw [if_pos (hiff.mpr h),if_pos h]; rfl
  · rw [if_neg (fun hh => h (hiff.mp hh)),if_neg h]
lemma z326 (x : nuMod (Pv 1)) :
    nuPv1Equiv (nuMap rmul_alphap x) = rmul_alpha (nuPv1Equiv x) := by
  apply xP; ext c
  change (rmul_alphap x.val).val ⟨nuB c.1,_⟩ = (rmul_alpha (nuPv1Equiv x)).val c
  rw [z129,z183]
  let eBv : Bv 3 ≃ Bv 1 :=
    ⟨fun y => ⟨nuB y.1,by change rev y.1.src = 1; rw [y.2]; rfl⟩,
     fun y => ⟨nuB y.1,by change rev y.1.src = 3; rw [y.2]; rfl⟩,
     fun y => Subtype.ext (z19 y.1),
     fun y => Subtype.ext (z19 y.1)⟩
  rw [← eBv.sum_comp]
  refine sum_congr rfl fun y _ => ?_
  dsimp [eBv,nuPv1Equiv]
  have hiff : mulB (nuB y.1) alphapB = some (nuB c.1) ↔ mulB y.1 alphaB = some c.1 := by
    rw [← nuB_alphaB,z187]
    cases h : mulB y.1 alphaB with
    | none => simp
    | some z =>
      simp only [Option.map_some,Option.some.injEq]
      exact ⟨fun hz => by rw [← z19 z,hz,z19],fun hz => by rw [hz]⟩
  by_cases h : mulB y.1 alphaB = some c.1
  · rw [if_pos (hiff.mpr h),if_pos h]; rfl
  · rw [if_neg (fun hh => h (hiff.mp hh)),if_neg h]
abbrev XMod : Type := ↥(LinearMap.ker rmul_q)
abbrev XpMod : Type := ↥(LinearMap.ker rmul_iota)
def inclX : XMod →ₗ[Λ] Pv 3 := (LinearMap.ker rmul_q).subtype
def inclXp : XpMod →ₗ[Λ] Pv 1 := (LinearMap.ker rmul_iota).subtype
lemma z312 : Function.Injective inclX := Subtype.val_injective
lemma inclXp_inj : Function.Injective inclXp := Subtype.val_injective
def projToX : Pv 1 →ₗ[Λ] XMod :=
  rmul_iota.codRestrict (LinearMap.ker rmul_q) fun y =>
    congrArg (fun (f : Pv 1 →ₗ[Λ] Pv 1) => f y) z142
def projToXp : Pv 3 →ₗ[Λ] XpMod :=
  rmul_q.codRestrict (LinearMap.ker rmul_iota) fun y =>
    congrArg (fun (f : Pv 3 →ₗ[Λ] Pv 3) => f y) z143
lemma inclX_comp_projToX : inclX.comp projToX = rmul_iota := rfl
lemma z350 : inclXp.comp projToXp = rmul_q := rfl
lemma z80 : Function.Surjective projToX := fun x => by
  have hx : x.1 ∈ LinearMap.range rmul_iota := by rw [z273]; exact x.2
  obtain ⟨y,hy⟩ := hx
  exact ⟨y,Subtype.ext hy⟩
lemma z205 : Function.Surjective projToXp := fun x => by
  have hx : x.1 ∈ LinearMap.range rmul_q := by rw [z198]; exact x.2
  obtain ⟨y,hy⟩ := hx
  exact ⟨y,Subtype.ext hy⟩
lemma z235 : ExactAt inclXp projToX := by
  ext y
  simp only [LinearMap.mem_range,LinearMap.mem_ker]
  constructor
  · rintro ⟨x,rfl⟩; exact Subtype.ext x.2
  · intro hy; exact ⟨⟨y,congrArg Subtype.val hy⟩,rfl⟩
lemma z236 : ExactAt inclX projToXp := by
  ext y
  simp only [LinearMap.mem_range,LinearMap.mem_ker]
  constructor
  · rintro ⟨x,rfl⟩; exact Subtype.ext x.2
  · intro hy; exact ⟨⟨y,congrArg Subtype.val hy⟩,rfl⟩
def αX : XMod →ₗ[Λ] XMod :=
  (rmul_alpha.comp inclX).codRestrict (LinearMap.ker rmul_q) fun x => by
    change rmul_q (rmul_alpha x.1) = 0
    have h := congrArg (fun (f : Pv 3 →ₗ[Λ] Pv 1) => f x.1) z90
    simp only [LinearMap.comp_apply] at h
    rw [h,x.2,map_zero]
def αXp : XpMod →ₗ[Λ] XpMod :=
  (rmul_alphap.comp inclXp).codRestrict (LinearMap.ker rmul_iota) fun x => by
    change rmul_iota (rmul_alphap x.1) = 0
    have h := congrArg (fun (f : Pv 1 →ₗ[Λ] Pv 3) => f x.1) z55
    simp only [LinearMap.comp_apply] at h
    rw [h,x.2,map_zero]
lemma αX_sq : αX.comp αX = 0 := by
  apply LinearMap.ext; intro x; apply Subtype.ext
  exact congrArg (fun (f : Pv 3 →ₗ[Λ] Pv 3) => f x.1) z324
lemma αXp_sq : αXp.comp αXp = 0 := by
  apply LinearMap.ext; intro x; apply Subtype.ext
  exact congrArg (fun (f : Pv 1 →ₗ[Λ] Pv 1) => f x.1) z243
lemma z186 : projToX.comp rmul_alphap = αX.comp projToX := by
  apply LinearMap.ext; intro x; apply Subtype.ext
  exact congrArg (fun (f : Pv 1 →ₗ[Λ] Pv 3) => f x) z55
lemma z185 : projToXp.comp rmul_alpha = αXp.comp projToXp := by
  apply LinearMap.ext; intro x; apply Subtype.ext
  exact congrArg (fun (f : Pv 3 →ₗ[Λ] Pv 1) => f x) z90
def gX : XMod := projToX (genPv 1)
def gXp : XpMod := projToXp (genPv 3)
lemma z259 : gX.1 = z45 iotaBv := z133
lemma z270 : gXp.1 = z45 qBv := z175
lemma z178 : eΛ 1 • gX = gX := by
  unfold gX; rw [← projToX.map_smul,z79]
lemma z245 : z115 • gX = 0 := by
  apply Subtype.ext
  change z12 qB • gX.1 = 0
  rw [z259,z27,show iotaBv.1 = iotaB from rfl,z208]
lemma αX_val (x : XMod) : (αX x).1 = rmul_alpha x.1 := rfl
lemma αXp_val (x : XpMod) : (αXp x).1 = rmul_alphap x.1 := rfl
lemma z215 : (αX gX).1 = z45 z161 := by
  rw [αX_val,z259,z148,z84]
  dsimp only; rw [dif_pos (socB_src 3)]
lemma z166 : z15 • gX = αX gX := by
  apply Subtype.ext
  change z12 alphapB • gX.1 = (αX gX).1
  rw [z259,z215,z27,z76]
  dsimp only; rw [dif_pos (socB_src 3)]
lemma z282 : αX ≠ 0 := fun h => by
  have h1 : (αX gX).1.val z161 = 0 := by rw [h]; rfl
  rw [z215,basisPv_val,if_pos rfl] at h1
  exact z38 h1
lemma z189 : eΛ 3 • gXp = gXp := by
  unfold gXp; rw [← projToXp.map_smul,z79]
lemma z256 : (αXp gXp).1 = z45 z323 := by
  rw [αXp_val,z270,z110,z105]
  dsimp only; rw [dif_pos (socB_src 1)]
def nuXEquiv : nuMod XMod ≃ₗ[Λ] XpMod where
  toFun x := ⟨nuPv3Equiv ⟨x.val.1⟩,by
    change rmul_iota (nuPv3Equiv ⟨x.val.1⟩) = 0
    rw [← z195 ⟨x.val.1⟩]
    have h0 : nuMap rmul_q ⟨x.val.1⟩ = 0 := nuMod.ext x.val.2
    rw [h0,map_zero]⟩
  invFun y := ⟨⟨(nuPv3Equiv.symm y.1).val,by
    have h1 := z195 (nuPv3Equiv.symm y.1)
    simp only [LinearEquiv.apply_symm_apply] at h1
    rw [y.2] at h1
    have h2 : nuMap rmul_q (nuPv3Equiv.symm y.1) = 0 := nuPv1Equiv.injective (by simpa using h1)
    exact congrArg nuMod.val h2⟩⟩
  left_inv x := by
    apply nuMod.ext; apply Subtype.ext
    exact congrArg nuMod.val (nuPv3Equiv.symm_apply_apply ⟨x.val.1⟩)
  right_inv y := by
    apply Subtype.ext
    exact nuPv3Equiv.apply_symm_apply y.1
  map_add' x y := by
    apply Subtype.ext
    exact nuPv3Equiv.map_add ⟨x.val.1⟩ ⟨y.val.1⟩
  map_smul' a x := by
    apply Subtype.ext
    exact nuPv3Equiv.map_smul a ⟨x.val.1⟩
lemma z127 (x : nuMod XMod) : nuXEquiv (nuMap αX x) = αXp (nuXEquiv x) := by
  apply Subtype.ext
  exact z222 ⟨x.val.1⟩
lemma nuXEquiv_gX : nuXEquiv ⟨gX⟩ = gXp := by
  apply Subtype.ext; apply xP; ext c
  change gX.1.val ⟨nuB c.1,_⟩ = gXp.1.val c
  rw [z259,z270,basisPv_val,basisPv_val]
  have hiff : (⟨nuB c.1,by change rev c.1.src = 3; rw [c.2]; rfl⟩ : Bv 3) = iotaBv ↔
      c = qBv := by
    constructor
    · intro h; apply Subtype.ext
      have h1 : nuB c.1 = iotaB := congrArg Subtype.val h
      rw [← z19 c.1,h1,z361]
    · intro h; subst h; exact Subtype.ext nuB_qB
  by_cases hc : c = qBv
  · rw [if_pos (hiff.mpr hc),if_pos hc]
  · rw [if_neg (fun hh => hc (hiff.mp hh)),if_neg hc]
lemma z336 :
    allB.all (fun c => if c.src == 3 && c.tgt == 3 then mulB c qB != none else true) = true := by decide
lemma z160 (x : XMod) : eΛ 3 • x = 0 := by
  apply Subtype.ext; apply xP; ext c
  change (eΛ 3 • x.1).val c = (0 : Pv 3).val c
  rw [z59,Pv.zero_val]
  by_cases htgt : c.1.tgt = 3
  · rw [if_pos htgt]
    have hchk := List.all_eq_true.mp z336 c.1 (z35 c.1)
    simp only [c.2,htgt,beq_self_eq_true,Bool.and_self,↓reduceIte,bne_iff_ne,ne_eq] at hchk
    exact (z96 x.1).mp x.2 c hchk
  · rw [if_neg htgt]
lemma z214 (y : XpMod) : eΛ 1 • y = 0 := by
  have h1 : nuXEquiv (eΛ 1 • nuXEquiv.symm y) = eΛ 1 • y := by rw [nuXEquiv.map_smul,nuXEquiv.apply_symm_apply]
  rw [← h1]
  have h2 : eΛ 1 • nuXEquiv.symm y = 0 := by
    apply nuMod.ext
    change ν (eΛ 1) • (nuXEquiv.symm y).val = 0
    rw [ν_eΛ]
    exact z160 _
  rw [h2,map_zero]
lemma z52 {M : Type} [AddCommGroup M] [Module Λ M]
    (f : XMod →ₗ[Λ] M) (h : f gX = 0) : f = 0 := by
  apply LinearMap.ext; intro x
  obtain ⟨p,rfl⟩ := z80 x
  have hfp : f.comp projToX = 0 := by
    apply (z29 1).injective; apply Subtype.ext; exact h
  exact congrArg (fun (k : Pv 1 →ₗ[Λ] M) => k p) hfp
lemma z116 {M : Type} [AddCommGroup M] [Module Λ M]
    (f : XpMod →ₗ[Λ] M) (h : f gXp = 0) : f = 0 := by
  apply LinearMap.ext; intro x
  obtain ⟨p,rfl⟩ := z205 x
  have hfp : f.comp projToXp = 0 := by
    apply (z29 3).injective; apply Subtype.ext; exact h
  exact congrArg (fun (k : Pv 3 →ₗ[Λ] M) => k p) hfp
lemma z328 (f : XMod →ₗ[Λ] XpMod) : f = 0 := by
  apply z52
  rw [← z178,f.map_smul]
  exact z214 (f gX)
lemma z269 (f : XpMod →ₗ[Λ] XMod) : f = 0 := by
  apply z116
  rw [← z189,f.map_smul]
  exact z160 (f gXp)
noncomputable def homFromXEquiv {M : Type} [AddCommGroup M] [Module Λ M] :
    (XMod →ₗ[Λ] M) ≃ { m : M // eΛ 1 • m = m ∧ z115 • m = 0 } where
  toFun g := ⟨g gX,by rw [← g.map_smul,z178],by rw [← g.map_smul,z245,map_zero]⟩
  invFun m :=
    let g1 : Pv 1 →ₗ[Λ] M := (z29 1).symm ⟨m.1,m.2.1⟩
    have hg1_ker : LinearMap.ker projToX ≤ LinearMap.ker g1 := by
      intro p hp
      have hp' : p ∈ LinearMap.range rmul_q := by
        rw [z198]; exact congrArg Subtype.val hp
      obtain ⟨r,rfl⟩ := hp'
      have hcomp : g1.comp rmul_q = 0 := by
        apply (z29 3).injective; apply Subtype.ext
        change g1 (rmul_q (genPv 3)) = 0
        rw [z175,← z24 qBv,g1.map_smul]
        have h1 : g1 (genPv 1) = m.1 := congrArg Subtype.val ((z29 1).apply_symm_apply ⟨m.1,m.2.1⟩)
        rw [h1]; exact m.2.2
      exact congrArg (fun (k : Pv 3 →ₗ[Λ] M) => k r) hcomp
    let qMap := Submodule.liftQ (LinearMap.ker projToX) g1 hg1_ker
    let iso : (Pv 1 ⧸ LinearMap.ker projToX) ≃ₗ[Λ] XMod :=
      LinearMap.quotKerEquivOfSurjective projToX z80
    qMap.comp iso.symm.toLinearMap
  left_inv g := by
    have hdiff : ∀ (h : XMod →ₗ[Λ] M),h gX = g gX → h = g := fun h hg => by
      have h0 : (h - g) gX = 0 := by simp [hg]
      exact sub_eq_zero.mp (z52 (h - g) h0)
    apply hdiff
    dsimp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
    have hinv : (LinearMap.quotKerEquivOfSurjective projToX z80).symm gX =
        Submodule.Quotient.mk (genPv 1) := by
      apply (LinearMap.quotKerEquivOfSurjective projToX z80).injective
      simp [gX]
    rw [hinv,Submodule.liftQ_apply]
    exact congrArg Subtype.val ((z29 1).apply_symm_apply ⟨g gX,_⟩)
  right_inv m := by
    apply Subtype.ext
    dsimp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
    have hinv : (LinearMap.quotKerEquivOfSurjective projToX z80).symm gX =
        Submodule.Quotient.mk (genPv 1) := by
      apply (LinearMap.quotKerEquivOfSurjective projToX z80).injective
      simp [gX]
    rw [hinv,Submodule.liftQ_apply]
    exact congrArg Subtype.val ((z29 1).apply_symm_apply ⟨m.1,m.2.1⟩)
lemma z180 :
    allB.all (fun c =>
      if c.src == 3 then
        match mulB c qB with
        | some d => mulB iotaB (dualB d) == some (dualB c)
        | none => true
      else true) = true := by decide
def homToXEquiv {M : Type} [AddCommGroup M] [Module Λ M] :
    (M →ₗ[Λ] XMod) ≃
      { ψ : M →+ ZMod 2 // (∀ m,ψ (eΛ 1 • m) = ψ m) ∧ (∀ m,ψ (z11 • m) = 0) } where
  toFun f :=
    let ψ := z31 3 (inclX.comp f)
    ⟨ψ.1,ψ.2,fun m => by
      have h0 : (rmul_q (f m).1).val z323 = 0 := by rw [(f m).2]; rfl
      rw [z174] at h0
      have huniq : ∀ y : Bv 3,mulB y.1 qB = some (socB 1) ↔ y = alphaBv := by
        intro y; constructor
        · intro hy
          have hb := List.all_eq_true.mp (List.all_eq_true.mp z68 y.1 (z35 y.1))
            alphaB (z35 alphaB)
          have hcond : (y.1.src == 3 && alphaB.src == 3 && mulB y.1 qB != none && mulB y.1 qB == mulB alphaB qB) = true := by
            simp [y.2,hy,z98]
          rw [if_pos hcond] at hb
          exact Subtype.ext (beq_iff_eq.mp hb)
        · rintro rfl; exact z98
      rw [sum_eq_single alphaBv] at h0
      · dsimp only at h0; rw [if_pos z98] at h0
        have hback := congrArg (fun (k : M →ₗ[Λ] Pv 3) => (k m).val alphaBv)
          ((z31 3).left_inv (inclX.comp f))
        change ψ.1 (z12 (dualB alphaB) • m) = (f m).1.val alphaBv at hback
        rw [z355] at hback
        exact hback.trans h0
      · intro y _ hy; dsimp only; rw [if_neg (fun hmy => hy ((huniq y).mp hmy))]
      · intro hn; exact absurd (mem_univ _) hn⟩
  invFun ψ :=
    let fPv : M →ₗ[Λ] Pv 3 := (z31 3).symm ⟨ψ.1,ψ.2.1⟩
    fPv.codRestrict (LinearMap.ker rmul_q) fun m => by
      rw [LinearMap.mem_ker,z96]
      intro c hc
      cases hd : mulB c.1 qB with
      | none => exact absurd hd hc
      | some d =>
        have hchk := List.all_eq_true.mp z180 c.1 (z35 c.1)
        simp only [c.2,beq_self_eq_true,↓reduceIte,hd,beq_iff_eq] at hchk
        change ψ.1 (z12 (dualB c.1) • m) = 0
        have hmul : z12 (dualB c.1) • m = z11 • (z12 (dualB d) • m) := by
          rw [← mul_smul,z11,z25,hchk]
        rw [hmul]
        exact ψ.2.2 _
  left_inv f := by
    apply LinearMap.ext; intro m; apply Subtype.ext
    exact congrArg (fun (k : M →ₗ[Λ] Pv 3) => k m) ((z31 3).left_inv (inclX.comp f))
  right_inv ψ := by
    apply Subtype.ext
    let fPv : M →ₗ[Λ] Pv 3 := (z31 3).symm ⟨ψ.1,ψ.2.1⟩
    have hcomp : inclX.comp (fPv.codRestrict (LinearMap.ker rmul_q) fun m => by
        rw [LinearMap.mem_ker,z96]
        intro c hc
        cases hd : mulB c.1 qB with
        | none => exact absurd hd hc
        | some d =>
          have hchk := List.all_eq_true.mp z180 c.1 (z35 c.1)
          simp only [c.2,beq_self_eq_true,↓reduceIte,hd,beq_iff_eq] at hchk
          change ψ.1 (z12 (dualB c.1) • m) = 0
          have hmul : z12 (dualB c.1) • m = z11 • (z12 (dualB d) • m) := by
            rw [← mul_smul,z11,z25,hchk]
          rw [hmul]
          exact ψ.2.2 _) = fPv := by
      apply LinearMap.ext; intro m; rfl
    change ((z31 3) (inclX.comp (fPv.codRestrict (LinearMap.ker rmul_q) _))).1 = ψ.1
    rw [hcomp]
    exact congrArg Subtype.val ((z31 3).right_inv ⟨ψ.1,ψ.2.1⟩)
def c0X : (XMod →ₗ[Λ] XMod) →+ ZMod 2 where
  toFun e := (e gX).1.val iotaBv
  map_zero' := rfl
  map_add' _ _ := rfl
lemma c0X_id : c0X LinearMap.id = 1 := by
  change gX.1.val iotaBv = 1
  rw [z259,basisPv_val,if_pos rfl]
lemma c0X_αX : c0X αX = 0 := by
  change (αX gX).1.val iotaBv = 0
  rw [z215,basisPv_val]
  have hne : iotaBv ≠ z161 := by decide
  rw [if_neg hne]
lemma z291 :
    allB.all (fun c => if c.src == 3 && c.tgt == 1 then (c == iotaB || c == socB 3) else true) = true := by decide
lemma z218 (e : XMod →ₗ[Λ] XMod) :
    ∃ c1 : ZMod 2,e = z2Lin (c0X e) LinearMap.id + z2Lin c1 αX := by
  let c1 : ZMod 2 := (e gX).1.val z161
  refine ⟨c1,?_⟩
  have hdiff : ((e - (z2Lin (c0X e) LinearMap.id + z2Lin c1 αX)) : XMod →ₗ[Λ] XMod) gX = 0 := by
    rw [LinearMap.sub_apply,sub_eq_zero]
    apply Subtype.ext; apply xP; ext c
    change (e gX).1.val c = (z2Lin (c0X e) LinearMap.id gX + z2Lin c1 αX gX).1.val c
    rw [show (z2Lin (c0X e) LinearMap.id gX + z2Lin c1 αX gX).1 =
      (z2Lin (c0X e) LinearMap.id gX).1 + (z2Lin c1 αX gX).1 from rfl,
      Pv.add_val,z43,z43,
      show (z16 (c0X e) (LinearMap.id gX)).1 = z16 (c0X e) gX.1 by
        by_cases h : c0X e = 0 <;> simp [z16,h],
      show (z16 c1 (αX gX)).1 = z16 c1 (αX gX).1 by
        by_cases h : c1 = 0 <;> simp [z16,h],
      Pv.z2smul_val,Pv.z2smul_val,z259,z215]
    have he1 : eΛ 1 • (e gX).1 = (e gX).1 := by
      have h1 : eΛ 1 • e gX = e gX := by rw [← e.map_smul,z178]
      exact (Submodule.coe_smul (eΛ 1) (e gX)).symm.trans (congrArg Subtype.val h1)
    have hc_tgt : (e gX).1.val c = if c.1.tgt = 1 then (e gX).1.val c else 0 := by
      have := congrArg (fun x : Pv 3 => x.val c) he1.symm
      rwa [z59] at this
    by_cases htgt : c.1.tgt = 1
    · have hchk := List.all_eq_true.mp z291 c.1 (z35 c.1)
      simp only [c.2,htgt,beq_self_eq_true,Bool.and_self,↓reduceIte,Bool.or_eq_true,
        beq_iff_eq] at hchk
      rcases hchk with h1 | h2
      · have hc' : c = iotaBv := Subtype.ext h1
        subst hc'
        have hne : iotaBv ≠ z161 := by decide
        simp [c0X,hne]
      · have hc' : c = z161 := Subtype.ext h2
        subst hc'
        have hne : z161 ≠ iotaBv := by decide
        simp [c1,hne]
    · rw [if_neg htgt] at hc_tgt
      have hne1 : c ≠ iotaBv := fun h => htgt (by rw [h]; rfl)
      have hne2 : c ≠ z161 := fun h => htgt (by rw [h]; rfl)
      simp [hc_tgt,hne1,hne2]
  exact sub_eq_zero.mp (z52 _ hdiff)
lemma z157 {e : XMod →ₗ[Λ] XMod} (h : StableEq e 0) : e = 0 := by
  obtain ⟨Q,p,q,hpq⟩ := h
  rw [sub_zero] at hpq
  obtain ⟨pext,hpext⟩ := z217 Q inclX z312 p
  apply z52
  have h1 : e gX = q (pext (inclX gX)) := by
    rw [hpq,LinearMap.comp_apply]
    congr 1; exact (congrArg (fun (k : XMod →ₗ[Λ] Q.Mod) => k gX) hpext).symm
  rw [h1]
  have hgX : inclX gX = z11 • genPv 3 := by
    change gX.1 = z12 iotaB • genPv 3
    rw [z259,← z24 iotaBv]
  rw [hgX,pext.map_smul,q.map_smul]
  have he3 : z11 * eΛ 3 = z11 := by
    rw [z11,z137,iotaB_src,if_pos rfl]
  rw [← he3,mul_smul,z160,smul_zero]
lemma z212 {M : Type} [AddCommGroup M] [Module Λ M]
    (f : M →ₗ[Λ] XMod) (g : XMod →ₗ[Λ] M) :
    c0X (f.comp g) = (homToXEquiv f).1 (z15 • g gX) := by
  have hback := congrArg (fun (k : M →ₗ[Λ] Pv 3) => (k (g gX)).val iotaBv)
    ((z31 3).left_inv (inclX.comp f))
  change (homToXEquiv f).1 (z12 (dualB iotaB) • g gX) = c0X (f.comp g) at hback
  rw [z308] at hback
  exact hback.symm
lemma z190 {N : Type} [AddCommGroup N] [Module Λ N]
    (S : Submodule (ZMod 2) (AsZ2 N)) (v : AsZ2 N) (hv : v ∉ S) :
    ∃ Φ : AsZ2 N →ₗ[ZMod 2] ZMod 2,(∀ s ∈ S,Φ s = 0) ∧ Φ v = 1 := by
  classical
  let q := S.mkQ
  have hqv : q v ≠ 0 := by
    intro h0
    exact hv ((Submodule.Quotient.mk_eq_zero S).mp h0)
  let L : Submodule (ZMod 2) (AsZ2 N ⧸ S) := Submodule.span (ZMod 2) {q v}
  let φL : L →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => if x.1 = 0 then 0 else 1
      map_add' := fun x y => by
        obtain ⟨rx,hrx⟩ := Submodule.mem_span_singleton.mp x.2
        obtain ⟨ry,hry⟩ := Submodule.mem_span_singleton.mp y.2
        have hx : x.1 = rx • q v := hrx.symm
        have hy : y.1 = ry • q v := hry.symm
        have hxy : (x + y).1 = (rx + ry) • q v := by
          change x.1 + y.1 = _; rw [hx,hy,add_smul]
        rcases z33 rx with rfl | rfl <;> rcases z33 ry with rfl | rfl
        · simp [hxy,hx,hy]
        · simp [hxy,hx,hy,hqv]
        · simp [hxy,hx,hy,hqv]
        · simp [hxy,hx,hy,hqv,z194]
      map_smul' := fun r x => by
        rcases z33 r with rfl | rfl <;> simp }
  obtain ⟨T,hLT⟩ := Submodule.exists_isCompl L
  let p : (AsZ2 N ⧸ S) →ₗ[ZMod 2] L := L.projectionOnto T hLT
  refine ⟨(φL.comp p).comp q,?_,?_⟩
  · intro s hs
    simp only [LinearMap.comp_apply]
    have hq0 : q s = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hs
    rw [hq0,map_zero,map_zero]
  · simp only [LinearMap.comp_apply]
    have hvL : q v ∈ L := Submodule.subset_span (Set.mem_singleton (q v))
    have hpv : p (q v) = ⟨q v,hvL⟩ := Submodule.projectionOnto_apply_left hLT ⟨q v,hvL⟩
    rw [hpv]
    change (if q v = 0 then (0 : ZMod 2) else 1) = 1
    rw [if_neg hqv]
lemma z339 {M : Type} [AddCommGroup M] [Module Λ M] (g : XMod →ₗ[Λ] M) :
    (∀ f : M →ₗ[Λ] XMod,c0X (f.comp g) = 0) ↔ StableEq (g.comp αX) 0 := by
  constructor
  · intro hzero
    let iotaMap : AsZ2 M →ₗ[ZMod 2] AsZ2 M :=
      { toFun := fun x => ⟨z11 • x.val⟩
        map_add' := fun x y => by apply xA; exact smul_add z11 x.val y.val
        map_smul' := fun r x => by apply xA; exact z125 z11 r x.val }
    have hmem : (⟨z15 • g gX⟩ : AsZ2 M) ∈ LinearMap.range iotaMap := by
      by_contra hnot
      obtain ⟨Φ,hΦS,hΦv⟩ := z190 (LinearMap.range iotaMap) ⟨z15 • g gX⟩ hnot
      let ψ : M →+ ZMod 2 :=
        { toFun := fun m => Φ ⟨eΛ 1 • m⟩
          map_zero' := by rw [smul_zero]; exact Φ.map_zero
          map_add' := fun x y => by rw [smul_add]; exact Φ.map_add ⟨eΛ 1 • x⟩ ⟨eΛ 1 • y⟩ }
      have hψ1 : ∀ m,ψ (eΛ 1 • m) = ψ m := fun m => by
        change Φ ⟨eΛ 1 • (eΛ 1 • m)⟩ = Φ ⟨eΛ 1 • m⟩; rw [← mul_smul,z44]
      have hψi : ∀ m,ψ (z11 • m) = 0 := fun m => by
        change Φ ⟨eΛ 1 • (z11 • m)⟩ = 0
        have he1i : eΛ 1 * z11 = z11 := by rw [z11,z164,iotaB_tgt,if_pos rfl]
        rw [← mul_smul,he1i]
        exact hΦS ⟨z11 • m⟩ ⟨⟨m⟩,rfl⟩
      let f : M →ₗ[Λ] XMod := homToXEquiv.symm ⟨ψ,hψ1,hψi⟩
      have hc0 := hzero f
      rw [z212,homToXEquiv.apply_symm_apply] at hc0
      change Φ ⟨eΛ 1 • (z15 • g gX)⟩ = 0 at hc0
      have he1a : eΛ 1 * z15 = z15 := by rw [z15,z164,alphapB_tgt,if_pos rfl]
      rw [← mul_smul,he1a,hΦv] at hc0
      exact z38 hc0
    obtain ⟨⟨n⟩,hn⟩ := hmem
    have hn' : z11 • n = z15 • g gX := congrArg AsZ2.val hn
    let n3 := eΛ 3 • n
    have hn3 : eΛ 3 • n3 = n3 := by rw [← mul_smul,z44]
    let h3 : Pv 3 →ₗ[Λ] M := (z29 3).symm ⟨n3,hn3⟩
    apply z70 3 inclX h3
    have hdiff : (g.comp αX - h3.comp inclX) gX = 0 := by
      rw [LinearMap.sub_apply,sub_eq_zero,LinearMap.comp_apply,LinearMap.comp_apply]
      have hgX : inclX gX = z11 • genPv 3 := by
        change gX.1 = z12 iotaB • genPv 3; rw [z259,← z24 iotaBv]
      rw [hgX,h3.map_smul]
      have hh3 : h3 (genPv 3) = n3 := congrArg Subtype.val ((z29 3).apply_symm_apply ⟨n3,hn3⟩)
      rw [hh3,← mul_smul]
      have hi3 : z11 * eΛ 3 = z11 := by rw [z11,z137,iotaB_src,if_pos rfl]
      rw [hi3,hn',← g.map_smul,z166]
    exact sub_eq_zero.mp (z52 _ hdiff)
  · intro hstab f
    have hcomp : StableEq ((f.comp g).comp αX) 0 := by
      rw [LinearMap.comp_assoc]; simpa using hstab.comp_left f
    obtain ⟨c1,hdec⟩ := z218 (f.comp g)
    have hzero := z157 hcomp
    rw [hdec,LinearMap.add_comp,z30,z30,LinearMap.id_comp,αX_sq,
      z63,add_zero] at hzero
    rcases z33 (c0X (f.comp g)) with h0 | h1
    · exact h0
    · rw [h1,z280] at hzero; exact absurd hzero z282
lemma z362 {M : Type} [AddCommGroup M] [Module Λ M] (f : M →ₗ[Λ] XMod) :
    (∀ g : XMod →ₗ[Λ] M,c0X (f.comp g) = 0) ↔ StableEq (αX.comp f) 0 := by
  constructor
  · intro hzero
    let ψf := (homToXEquiv f).1
    let ψaf : AsZ2 M →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun x => ψf (z15 • x.val)
        map_add' := fun x y => by rw [AsZ2.add_val,smul_add,ψf.map_add]
        map_smul' := fun r x => by
          simp only [RingHom.id_apply,AsZ2.smul_val,z125,z120,z232,smul_eq_mul] }
    let qMap : AsZ2 M →ₗ[ZMod 2] AsZ2 M :=
      { toFun := fun x => ⟨z115 • x.val⟩
        map_add' := fun x y => by apply xA; exact smul_add z115 x.val y.val
        map_smul' := fun r x => by apply xA; exact z125 z115 r x.val }
    have hker : LinearMap.ker qMap ≤ LinearMap.ker ψaf := by
      intro x hx
      have hqm : z115 • x.val = 0 := congrArg AsZ2.val hx
      let m1 := eΛ 1 • x.val
      have hm1 : eΛ 1 • m1 = m1 := by rw [← mul_smul,z44]
      have hqm1 : z115 • m1 = 0 := by
        have hqe : z115 * eΛ 1 = z115 := by rw [z115,z137,qB_src,if_pos rfl]
        rw [← mul_smul,hqe,hqm]
      let g : XMod →ₗ[Λ] M := homFromXEquiv.symm ⟨m1,hm1,hqm1⟩
      have hc0 := hzero g
      rw [z212] at hc0
      have hgg : g gX = m1 := congrArg Subtype.val (homFromXEquiv.apply_symm_apply ⟨m1,hm1,hqm1⟩)
      rw [hgg] at hc0
      change ψf (z15 • x.val) = 0
      have hae : z15 * eΛ 1 = z15 := by rw [z15,z137,alphapB_src,if_pos rfl]
      rw [← hae,mul_smul]
      exact hc0
    let qQuot : (AsZ2 M ⧸ LinearMap.ker qMap) →ₗ[ZMod 2] ZMod 2 :=
      Submodule.liftQ (LinearMap.ker qMap) ψaf hker
    let iso : (AsZ2 M ⧸ LinearMap.ker qMap) ≃ₗ[ZMod 2] LinearMap.range qMap :=
      LinearMap.quotKerEquivRange qMap
    obtain ⟨Φ,hΦ⟩ := z156 (LinearMap.range qMap) (qQuot.comp iso.symm.toLinearMap)
    have hΦq : ∀ m : M,Φ ⟨z115 • m⟩ = ψf (z15 • m) := fun m => by
      have h1 := hΦ ⟨⟨z115 • m⟩,⟨⟨m⟩,rfl⟩⟩
      have h2 : iso.symm ⟨⟨z115 • m⟩,⟨⟨m⟩,rfl⟩⟩ = Submodule.Quotient.mk ⟨m⟩ := by
        apply iso.injective
        rw [iso.apply_symm_apply]
        apply Subtype.ext; rfl
      rw [h1,LinearMap.comp_apply,LinearEquiv.coe_coe,h2,Submodule.liftQ_apply]
      rfl
    let φ : M →+ ZMod 2 :=
      { toFun := fun m => Φ ⟨eΛ 3 • m⟩
        map_zero' := by rw [smul_zero]; exact Φ.map_zero
        map_add' := fun x y => by rw [smul_add]; exact Φ.map_add ⟨eΛ 3 • x⟩ ⟨eΛ 3 • y⟩ }
    have hφ3 : ∀ m,φ (eΛ 3 • m) = φ m := fun m => by
      change Φ ⟨eΛ 3 • (eΛ 3 • m)⟩ = Φ ⟨eΛ 3 • m⟩; rw [← mul_smul,z44]
    let H : M →ₗ[Λ] Pv 1 := (z31 1).symm ⟨φ,hφ3⟩
    apply z70 1 H projToX
    have heqPv : inclX.comp (αX.comp f) = inclX.comp (projToX.comp H) := by
      apply (z31 3).injective; apply Subtype.ext; ext m
      change (αX (f m)).1.val z161 = (rmul_iota (H m)).val z161
      have hlhs : (rmul_alpha (f m).1).val z161 = (f m).1.val iotaBv := by
        rw [z183,sum_eq_single iotaBv]
        · dsimp only; rw [if_pos z84]
        · intro y _ hy
          rw [if_neg]; intro hmy
          have hdec := z64
            (fun z => !(z.src == 3 && mulB z alphaB == some (socB 3)) || z == iotaB) (by decide) y.1
          simp only [y.2,hmy,beq_self_eq_true,Bool.and_self,Bool.not_true,Bool.false_or,beq_iff_eq] at hdec
          exact hy (Subtype.ext hdec)
        · intro hn; exact absurd (mem_univ _) hn
      have hrhs : (rmul_iota (H m)).val z161 = (H m).val alphapBv := by
        rw [z117,sum_eq_single alphapBv]
        · dsimp only; rw [if_pos z76]
        · intro y _ hy
          rw [if_neg]; intro hmy
          have hdec := z64
            (fun z => !(z.src == 1 && mulB z iotaB == some (socB 3)) || z == alphapB) (by decide) y.1
          simp only [y.2,hmy,beq_self_eq_true,Bool.and_self,Bool.not_true,Bool.false_or,beq_iff_eq] at hdec
          exact hy (Subtype.ext hdec)
        · intro hn; exact absurd (mem_univ _) hn
      rw [show (αX (f m)).1 = rmul_alpha (f m).1 from rfl,hlhs,hrhs]
      have hfback := congrArg (fun (k : M →ₗ[Λ] Pv 3) => (k m).val iotaBv)
        ((z31 3).left_inv (inclX.comp f))
      change ψf (z12 (dualB iotaB) • m) = (f m).1.val iotaBv at hfback
      rw [z308] at hfback
      rw [← hfback]
      change ψf (z15 • m) = φ (z12 (dualB alphapB) • m)
      rw [z334]
      change ψf (z15 • m) = Φ ⟨eΛ 3 • (z115 • m)⟩
      have he3q : eΛ 3 * z115 = z115 := by rw [z115,z164,qB_tgt,if_pos rfl]
      rw [← mul_smul,he3q,hΦq]
    apply LinearMap.ext; intro m
    exact z312 (congrArg (fun (k : M →ₗ[Λ] Pv 3) => k m) heqPv)
  · intro hstab g
    have hcomp : StableEq (αX.comp (f.comp g)) 0 := by
      rw [← LinearMap.comp_assoc]; simpa using hstab.comp_right g
    obtain ⟨c1,hdec⟩ := z218 (f.comp g)
    have hzero := z157 hcomp
    rw [hdec,LinearMap.comp_add,z54,z54,LinearMap.comp_id,αX_sq,
      z63,add_zero] at hzero
    rcases z33 (c0X (f.comp g)) with h0 | h1
    · exact h0
    · rw [h1,z280] at hzero; exact absurd hzero z282
structure Gemstone (G : Type) [AddCommGroup G] [Module Λ G] [Finite G] where
  α : G →ₗ[Λ] G
  c0 : (G →ₗ[Λ] G) →+ ZMod 2
  c0_id : c0 LinearMap.id = 1
  α_sq : α.comp α = 0
  end_decomp : ∀ e : G →ₗ[Λ] G,∃ c1 : ZMod 2,e = z2Lin (c0 e) LinearMap.id + z2Lin c1 α
  av_right : ∀ {M : Type} [AddCommGroup M] [Module Λ M] [Finite M] (g : G →ₗ[Λ] M),
    (∀ f : M →ₗ[Λ] G,c0 (f.comp g) = 0) ↔ StableEq (g.comp α) 0
  av_left : ∀ {M : Type} [AddCommGroup M] [Module Λ M] [Finite M] (f : M →ₗ[Λ] G),
    (∀ g : G →ₗ[Λ] M,c0 (f.comp g) = 0) ↔ StableEq (α.comp f) 0
lemma Gemstone.c0_α {G : Type} [AddCommGroup G] [Module Λ G] [Finite G] (S : Gemstone G) :
    S.c0 S.α = 0 := by
  by_cases hα : S.α = 0
  · rw [hα]; exact S.c0.map_zero
  · obtain ⟨c1,hc1⟩ := S.end_decomp S.α
    rcases z33 (S.c0 S.α) with h0 | h1
    · exact h0
    · exfalso
      rw [h1,z280] at hc1
      have hsq := congrArg (fun (k : G →ₗ[Λ] G) => k.comp S.α) hc1
      rw [S.α_sq,LinearMap.add_comp,LinearMap.id_comp,z30,S.α_sq,
        z63,add_zero] at hsq
      exact hα hsq.symm
lemma Gemstone.c0_comp_end {G : Type} [AddCommGroup G] [Module Λ G] [Finite G] (S : Gemstone G)
    (e₁ e₂ : G →ₗ[Λ] G) : S.c0 (e₁.comp e₂) = S.c0 e₁ * S.c0 e₂ := by
  obtain ⟨c1,he1⟩ := S.end_decomp e₁
  obtain ⟨c2,he2⟩ := S.end_decomp e₂
  have hc0z : ∀ (r : ZMod 2) (e : G →ₗ[Λ] G),S.c0 (z2Lin r e) = r * S.c0 e := fun r e => by
    rcases z33 r with rfl | rfl <;> simp [z2Lin]
  conv_lhs => rw [he1,he2]
  simp only [LinearMap.add_comp,LinearMap.comp_add,z54,z30,
    LinearMap.id_comp,LinearMap.comp_id,S.α_sq,z63,add_zero,map_add,
    hc0z,S.c0_id,S.c0_α,mul_zero,mul_one]
  exact mul_comm _ _
def gemX : Gemstone XMod where
  α := αX
  c0 := c0X
  c0_id := c0X_id
  α_sq := αX_sq
  end_decomp := z218
  av_right := z339
  av_left := z362
@[simp] lemma gemX_α : gemX.α = αX := rfl
def z56 (e : XpMod →ₗ[Λ] XpMod) : XMod →ₗ[Λ] XMod :=
  nuModInvol.toLinearMap.comp
    ((nuMap (nuXEquiv.symm.toLinearMap.comp (e.comp nuXEquiv.toLinearMap))).comp
      nuModInvol.symm.toLinearMap)
def c0Xp : (XpMod →ₗ[Λ] XpMod) →+ ZMod 2 where
  toFun e := c0X (z56 e)
  map_zero' := by
    have hz : z56 0 = 0 := by apply LinearMap.ext; intro x; rfl
    rw [hz]; exact c0X.map_zero
  map_add' e1 e2 := by
    have ha : z56 (e1 + e2) = z56 e1 + z56 e2 := by
      apply LinearMap.ext; intro x; apply Subtype.ext; apply xP; ext c
      change (nuXEquiv.symm (e1 (nuXEquiv ⟨x⟩) + e2 (nuXEquiv ⟨x⟩))).val.1.val c = _
      rw [map_add]; rfl
    rw [ha]; exact c0X.map_add _ _
lemma z296 (e : XpMod →ₗ[Λ] XpMod) : c0Xp e = (e gXp).1.val qBv := by
  change (z56 e gX).1.val iotaBv = (e gXp).1.val qBv
  change (nuXEquiv.symm (e (nuXEquiv ⟨gX⟩))).val.1.val iotaBv = (e gXp).1.val qBv
  rw [nuXEquiv_gX]
  change (e gXp).1.val ⟨nuB iotaB,_⟩ = (e gXp).1.val qBv
  rfl
lemma z347 : z56 LinearMap.id = LinearMap.id := by
  apply LinearMap.ext; intro x
  change (nuXEquiv.symm (nuXEquiv ⟨x⟩)).val = x
  rw [nuXEquiv.symm_apply_apply]
lemma nuConjEnd_αXp : z56 αXp = αX := by
  apply LinearMap.ext; intro x
  change (nuXEquiv.symm (αXp (nuXEquiv ⟨x⟩))).val = αX x
  rw [← z127,nuXEquiv.symm_apply_apply]; rfl
lemma nuConjEnd_comp {M : Type} [AddCommGroup M] [Module Λ M]
    (f : M →ₗ[Λ] XpMod) (g : XpMod →ₗ[Λ] M) :
    z56 (f.comp g) =
      (nuModInvol.toLinearMap.comp (nuMap (nuXEquiv.symm.toLinearMap.comp f))).comp
        ((nuMap (g.comp nuXEquiv.toLinearMap)).comp nuModInvol.symm.toLinearMap) := by
  apply LinearMap.ext; intro x; rfl
def gemXp : Gemstone XpMod where
  α := αXp
  c0 := c0Xp
  c0_id := by change c0X (z56 LinearMap.id) = 1; rw [z347,c0X_id]
  α_sq := αXp_sq
  end_decomp := fun e => by
    obtain ⟨c1,hc1⟩ := z218 (z56 e)
    refine ⟨c1,?_⟩
    apply LinearMap.ext; intro y
    have h1 := congrArg (fun (k : XMod →ₗ[Λ] XMod) => k (nuXEquiv.symm y).val) hc1
    have h2 : nuXEquiv ⟨z56 e (nuXEquiv.symm y).val⟩ = e y := by
      change nuXEquiv (nuXEquiv.symm (e (nuXEquiv (nuXEquiv.symm y)))) = e y
      rw [nuXEquiv.apply_symm_apply,nuXEquiv.apply_symm_apply]
    rw [← h2,h1]
    have hlin : ∀ (r : ZMod 2) (k : XMod →ₗ[Λ] XMod) (x : XMod),
        nuXEquiv ⟨z2Lin r k x⟩ = z16 r (nuXEquiv ⟨k x⟩) := fun r k x => by
      by_cases hr : r = 0
      · simp [z2Lin,z16,hr]; rfl
      · simp [z2Lin,z16,hr]
    change nuXEquiv (⟨z2Lin (c0Xp e) LinearMap.id (nuXEquiv.symm y).val⟩ +
        ⟨z2Lin c1 αX (nuXEquiv.symm y).val⟩) = _
    rw [map_add,hlin,hlin]
    simp only [LinearMap.add_apply,z43,LinearMap.id_apply]
    congr 1
    · congr 1; exact nuXEquiv.apply_symm_apply y
    · congr 1
      have hα := z127 (nuXEquiv.symm y)
      rw [nuXEquiv.apply_symm_apply] at hα
      exact hα
  av_right := fun {M} _ _ _ g => by
    let eX : XMod ≃ₗ[Λ] nuMod XpMod :=
      nuModInvol.symm.trans
        { toFun := nuMap nuXEquiv.toLinearMap
          invFun := nuMap nuXEquiv.symm.toLinearMap
          left_inv := fun x => by apply nuMod.ext; exact nuXEquiv.symm_apply_apply x.val
          right_inv := fun y => by apply nuMod.ext; exact nuXEquiv.apply_symm_apply y.val
          map_add' := (nuMap nuXEquiv.toLinearMap).map_add
          map_smul' := (nuMap nuXEquiv.toLinearMap).map_smul }
    let g1 : XMod →ₗ[Λ] nuMod M := (nuMap g).comp eX.toLinearMap
    have hiff1 : (∀ f : M →ₗ[Λ] XpMod,c0Xp (f.comp g) = 0) ↔
        (∀ f1 : nuMod M →ₗ[Λ] XMod,c0X (f1.comp g1) = 0) := by
      constructor
      · intro h f1
        let f : M →ₗ[Λ] XpMod :=
          (nuModInvol.toLinearMap.comp (nuMap (eX.toLinearMap.comp f1))).comp nuModInvol.symm.toLinearMap
        have heq : f1.comp g1 = z56 (f.comp g) := by
          apply LinearMap.ext; intro x
          change f1 ⟨g (nuXEquiv ⟨x⟩)⟩ = (nuXEquiv.symm (nuXEquiv ⟨f1 ⟨g (nuXEquiv ⟨x⟩)⟩⟩)).val
          rw [nuXEquiv.symm_apply_apply]
        rw [heq]; exact h f
      · intro h f
        let f1 : nuMod M →ₗ[Λ] XMod := eX.symm.toLinearMap.comp (nuMap f)
        have heq : z56 (f.comp g) = f1.comp g1 := by
          apply LinearMap.ext; intro x; rfl
        change c0X (z56 (f.comp g)) = 0
        rw [heq]; exact h f1
    rw [hiff1,z339 g1]
    constructor
    · intro h
      apply StableEq.of_nuMap
      have hcomm : (nuMap (g.comp αXp)).comp eX.toLinearMap = g1.comp αX := by
        apply LinearMap.ext; intro x; apply nuMod.ext
        change g (αXp (nuXEquiv ⟨x⟩)) = g (nuXEquiv ⟨αX x⟩)
        rw [← z127]; rfl
      have heq : nuMap (g.comp αXp) = (g1.comp αX).comp eX.symm.toLinearMap := by
        rw [← hcomm,LinearMap.comp_assoc]; apply LinearMap.ext; intro y; simp
      rw [heq]
      have h0 : (0 : nuMod XpMod →ₗ[Λ] nuMod M) = nuMap (0 : XpMod →ₗ[Λ] M) := by
        apply LinearMap.ext; intro y; rfl
      rw [← h0]
      simpa using h.comp_right eX.symm.toLinearMap
    · intro h
      have hnu := h.nuMap
      have hcomm : g1.comp αX = (nuMap (g.comp αXp)).comp eX.toLinearMap := by
        apply LinearMap.ext; intro x; apply nuMod.ext
        change g (nuXEquiv ⟨αX x⟩) = g (αXp (nuXEquiv ⟨x⟩))
        rw [← z127]; rfl
      rw [hcomm]
      have h0 : (nuMap (0 : XpMod →ₗ[Λ] M)).comp eX.toLinearMap = 0 := by
        apply LinearMap.ext; intro x; rfl
      rw [← h0]
      exact hnu.comp_right eX.toLinearMap
  av_left := fun {M} _ _ _ f => by
    let eX : XMod ≃ₗ[Λ] nuMod XpMod :=
      nuModInvol.symm.trans
        { toFun := nuMap nuXEquiv.toLinearMap
          invFun := nuMap nuXEquiv.symm.toLinearMap
          left_inv := fun x => by apply nuMod.ext; exact nuXEquiv.symm_apply_apply x.val
          right_inv := fun y => by apply nuMod.ext; exact nuXEquiv.apply_symm_apply y.val
          map_add' := (nuMap nuXEquiv.toLinearMap).map_add
          map_smul' := (nuMap nuXEquiv.toLinearMap).map_smul }
    let f1 : nuMod M →ₗ[Λ] XMod := eX.symm.toLinearMap.comp (nuMap f)
    have hiff1 : (∀ g : XpMod →ₗ[Λ] M,c0Xp (f.comp g) = 0) ↔
        (∀ g1 : XMod →ₗ[Λ] nuMod M,c0X (f1.comp g1) = 0) := by
      constructor
      · intro h g1
        let g : XpMod →ₗ[Λ] M :=
          (nuModInvol.toLinearMap.comp (nuMap (g1.comp eX.symm.toLinearMap))).comp nuModInvol.symm.toLinearMap
        have heq : f1.comp g1 = z56 (f.comp g) := by
          apply LinearMap.ext; intro x
          change (nuXEquiv.symm (f (g1 x).val)).val =
            (nuXEquiv.symm (f (g1 (nuXEquiv.symm (nuXEquiv ⟨x⟩)).val).val)).val
          rw [nuXEquiv.symm_apply_apply]
        rw [heq]; exact h g
      · intro h g
        let g1 : XMod →ₗ[Λ] nuMod M := (nuMap g).comp eX.toLinearMap
        have heq : z56 (f.comp g) = f1.comp g1 := by apply LinearMap.ext; intro x; rfl
        change c0X (z56 (f.comp g)) = 0
        rw [heq]; exact h g1
    rw [hiff1,z362 f1]
    constructor
    · intro h
      apply StableEq.of_nuMap
      have hcomm : eX.toLinearMap.comp (αX.comp f1) = nuMap (αXp.comp f) := by
        apply LinearMap.ext; intro x; apply nuMod.ext
        change nuXEquiv ⟨αX (nuXEquiv.symm (f x.val)).val⟩ = αXp (f x.val)
        have hα := z127 (nuXEquiv.symm (f x.val))
        rw [nuXEquiv.apply_symm_apply] at hα
        exact hα
      have h0 : eX.toLinearMap.comp (0 : nuMod M →ₗ[Λ] XMod) = nuMap (0 : M →ₗ[Λ] XpMod) := by
        apply LinearMap.ext; intro x; rfl
      rw [← hcomm,← h0]
      exact h.comp_left eX.toLinearMap
    · intro h
      have hnu := h.nuMap
      have hcomm : αX.comp f1 = eX.symm.toLinearMap.comp (nuMap (αXp.comp f)) := by
        apply LinearMap.ext; intro x
        have h1 : nuXEquiv ⟨αX (nuXEquiv.symm (f x.val)).val⟩ = αXp (f x.val) := by
          have hα := z127 (nuXEquiv.symm (f x.val))
          rw [nuXEquiv.apply_symm_apply] at hα
          exact hα
        change αX (nuXEquiv.symm (f x.val)).val = (nuXEquiv.symm (αXp (f x.val))).val
        rw [← h1,nuXEquiv.symm_apply_apply]
      have h0 : eX.symm.toLinearMap.comp (nuMap (0 : M →ₗ[Λ] XpMod)) = 0 := by
        apply LinearMap.ext; intro x; rfl
      rw [hcomm,← h0]
      exact hnu.comp_left eX.symm.toLinearMap
structure Z2Hom (M N : Type) [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N] where
  hom : M →ₗ[Λ] N
lemma Z2Hom.ext {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N] {f g : Z2Hom M N} (h : f.hom = g.hom) : f = g := by cases f; cases g; congr
private lemma xZ {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N] {f g : Z2Hom M N} (h : f.hom = g.hom) : f = g := Z2Hom.ext h
instance {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    [Finite M] [Finite N] : Finite (Z2Hom M N) :=
  Finite.of_injective (fun f : Z2Hom M N => (f.hom : M → N))
    (fun _ _ h => Z2Hom.ext (LinearMap.ext (congrFun h)))
instance {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N] :
    Zero (Z2Hom M N) := ⟨⟨0⟩⟩
instance {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N] :
    Add (Z2Hom M N) := ⟨fun f g => ⟨f.hom + g.hom⟩⟩
instance {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N] :
    Neg (Z2Hom M N) := ⟨fun f => ⟨-f.hom⟩⟩
instance {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N] :
    Sub (Z2Hom M N) := ⟨fun f g => ⟨f.hom - g.hom⟩⟩
instance {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N] :
    SMul ℕ (Z2Hom M N) := ⟨fun n f => ⟨n • f.hom⟩⟩
instance {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N] :
    SMul ℤ (Z2Hom M N) := ⟨fun n f => ⟨n • f.hom⟩⟩
instance {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N] :
    AddCommGroup (Z2Hom M N) :=
  Function.Injective.addCommGroup Z2Hom.hom (fun _ _ h => Z2Hom.ext h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
instance {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N] :
    Module (ZMod 2) (Z2Hom M N) where
  smul r f := ⟨z2Lin r f.hom⟩
  one_smul f := by apply Z2Hom.ext; exact z280 f.hom
  mul_smul r s f := by apply Z2Hom.ext; exact z2Lin_mul r s f.hom
  smul_zero r := by apply Z2Hom.ext; exact z63 r
  smul_add r f g := by apply Z2Hom.ext; exact z299 r f.hom g.hom
  add_smul r s f := by apply Z2Hom.ext; exact z309 r s f.hom
  zero_smul f := by apply Z2Hom.ext; exact z2Lin_zero f.hom
def z109 {G : Type} [AddCommGroup G] [Module Λ G] [Finite G] (S : Gemstone G)
    {M : Type} [AddCommGroup M] [Module Λ M] {r : ℕ}
    (g : Fin r → G →ₗ[Λ] M) (f : Fin r → M →ₗ[Λ] G) : Prop :=
  ∀ (f' : M →ₗ[Λ] G) (g' : G →ₗ[Λ] M),
    S.c0 (f'.comp g') = ∑ k : Fin r,S.c0 (f'.comp (g k)) * S.c0 ((f k).comp g')
lemma z228 {G : Type} [AddCommGroup G] [Module Λ G] [Finite G] (S : Gemstone G)
    (M : Type) [AddCommGroup M] [Module Λ M] [Finite M] :
    ∃ (r : ℕ) (g : Fin r → G →ₗ[Λ] M) (f : Fin r → M →ₗ[Λ] G),z109 S g f := by
  have hc0z : ∀ (r : ZMod 2) (e : G →ₗ[Λ] G),S.c0 (z2Lin r e) = r * S.c0 e := fun r e => by
    rcases z33 r with rfl | rfl <;> simp [z2Lin]
  let KV : Submodule (ZMod 2) (Z2Hom G M) :=
    { carrier := { g | ∀ f : M →ₗ[Λ] G,S.c0 (f.comp g.hom) = 0 }
      zero_mem' := fun f => by simp [show (0 : Z2Hom G M).hom = 0 from rfl]
      add_mem' := fun {a b} ha hb f => by
        change S.c0 (f.comp (a.hom + b.hom)) = 0
        rw [LinearMap.comp_add,map_add,ha f,hb f,add_zero]
      smul_mem' := fun r {a} ha f => by
        change S.c0 (f.comp (z2Lin r a.hom)) = 0
        rw [z54,hc0z,ha f,mul_zero] }
  let KW : Submodule (ZMod 2) (Z2Hom M G) :=
    { carrier := { f | ∀ g : G →ₗ[Λ] M,S.c0 (f.hom.comp g) = 0 }
      zero_mem' := fun g => by simp [show (0 : Z2Hom M G).hom = 0 from rfl]
      add_mem' := fun {a b} ha hb g => by
        change S.c0 ((a.hom + b.hom).comp g) = 0
        rw [LinearMap.add_comp,map_add,ha g,hb g,add_zero]
      smul_mem' := fun r {a} ha g => by
        change S.c0 ((z2Lin r a.hom).comp g) = 0
        rw [z30,hc0z,ha g,mul_zero] }
  let Vbar := Z2Hom G M ⧸ KV
  let Wbar := Z2Hom M G ⧸ KW
  let rawB : Z2Hom M G →ₗ[ZMod 2] Z2Hom G M →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun f =>
        { toFun := fun g => S.c0 (f.hom.comp g.hom)
          map_add' := fun g1 g2 => by rw [show (g1 + g2).hom = g1.hom + g2.hom from rfl,LinearMap.comp_add,map_add]
          map_smul' := fun r g => by
            simp only [RingHom.id_apply,smul_eq_mul]
            change S.c0 (f.hom.comp (z2Lin r g.hom)) = r * S.c0 (f.hom.comp g.hom)
            rw [z54,hc0z] }
      map_add' := fun f1 f2 => by
        apply LinearMap.ext; intro g
        change S.c0 ((f1.hom + f2.hom).comp g.hom) = S.c0 (f1.hom.comp g.hom) + S.c0 (f2.hom.comp g.hom)
        rw [LinearMap.add_comp,map_add]
      map_smul' := fun r f => by
        apply LinearMap.ext; intro g
        simp only [RingHom.id_apply,LinearMap.smul_apply,smul_eq_mul]
        change S.c0 ((z2Lin r f.hom).comp g.hom) = r * S.c0 (f.hom.comp g.hom)
        rw [z30,hc0z] }
  let B1 : Z2Hom M G →ₗ[ZMod 2] (Vbar →ₗ[ZMod 2] ZMod 2) :=
    { toFun := fun f => Submodule.liftQ KV (rawB f) (fun g hg => hg f.hom)
      map_add' := fun f1 f2 => by
        apply LinearMap.ext; intro x
        obtain ⟨g,rfl⟩ := Submodule.Quotient.mk_surjective KV x
        change S.c0 ((f1.hom + f2.hom).comp g.hom) = S.c0 (f1.hom.comp g.hom) + S.c0 (f2.hom.comp g.hom)
        rw [LinearMap.add_comp,map_add]
      map_smul' := fun r f => by
        apply LinearMap.ext; intro x
        obtain ⟨g,rfl⟩ := Submodule.Quotient.mk_surjective KV x
        simp only [RingHom.id_apply,LinearMap.smul_apply,smul_eq_mul]
        change S.c0 ((z2Lin r f.hom).comp g.hom) = r * S.c0 (f.hom.comp g.hom)
        rw [z30,hc0z] }
  have hB1_ker : KW ≤ LinearMap.ker B1 := by
    intro f hf
    apply LinearMap.ext; intro x
    obtain ⟨g,rfl⟩ := Submodule.Quotient.mk_surjective KV x
    exact hf g.hom
  let B : Wbar →ₗ[ZMod 2] Module.Dual (ZMod 2) Vbar := Submodule.liftQ KW B1 hB1_ker
  have hB_apply : ∀ (f : Z2Hom M G) (g : Z2Hom G M),
      B (Submodule.Quotient.mk f) (Submodule.Quotient.mk g) = S.c0 (f.hom.comp g.hom) :=
    fun _ _ => rfl
  have hB_inj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot,Submodule.eq_bot_iff]
    intro w hw
    obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective KW w
    rw [Submodule.Quotient.mk_eq_zero]
    intro g
    have h0 := congrArg (fun (φ : Module.Dual (ZMod 2) Vbar) => φ (Submodule.Quotient.mk ⟨g⟩)) hw
    exact h0
  have hBf_inj : Function.Injective B.flip := by
    rw [← LinearMap.ker_eq_bot,Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨g,rfl⟩ := Submodule.Quotient.mk_surjective KV v
    rw [Submodule.Quotient.mk_eq_zero]
    intro f
    have h0 := congrArg (fun (φ : Module.Dual (ZMod 2) Wbar) => φ (Submodule.Quotient.mk ⟨f⟩)) hv
    exact h0
  have h1 : Module.finrank (ZMod 2) Wbar ≤ Module.finrank (ZMod 2) (Module.Dual (ZMod 2) Vbar) :=
    LinearMap.finrank_le_finrank_of_injective hB_inj
  have h2 : Module.finrank (ZMod 2) Vbar ≤ Module.finrank (ZMod 2) (Module.Dual (ZMod 2) Wbar) :=
    LinearMap.finrank_le_finrank_of_injective hBf_inj
  rw [Subspace.dual_finrank_eq] at h1 h2
  have hfr : Module.finrank (ZMod 2) Wbar = Module.finrank (ZMod 2) (Module.Dual (ZMod 2) Vbar) := by
    rw [Subspace.dual_finrank_eq]; omega
  have hB_surj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hB_inj
  let Bequiv : Wbar ≃ₗ[ZMod 2] Module.Dual (ZMod 2) Vbar := LinearEquiv.ofBijective B ⟨hB_inj,hB_surj⟩
  let r := Module.finrank (ZMod 2) Vbar
  let vBas : Module.Basis (Fin r) (ZMod 2) Vbar := Module.finBasis (ZMod 2) Vbar
  let wBas : Fin r → Wbar := fun k => Bequiv.symm (vBas.dualBasis k)
  have hliftV : ∀ k : Fin r,∃ g : Z2Hom G M,Submodule.Quotient.mk g = vBas k :=
    fun k => Submodule.Quotient.mk_surjective KV (vBas k)
  have hliftW : ∀ k : Fin r,∃ f : Z2Hom M G,Submodule.Quotient.mk f = wBas k :=
    fun k => Submodule.Quotient.mk_surjective KW (wBas k)
  choose gZ hgZ using hliftV
  choose fZ hfZ using hliftW
  refine ⟨r,fun k => (gZ k).hom,fun k => (fZ k).hom,fun f' g' => ?_⟩
  have hrepr : (Submodule.Quotient.mk ⟨g'⟩ : Vbar) =
      ∑ k : Fin r,vBas.repr (Submodule.Quotient.mk ⟨g'⟩) k • vBas k :=
    (vBas.sum_repr (Submodule.Quotient.mk ⟨g'⟩)).symm
  have hval : S.c0 (f'.comp g') = B (Submodule.Quotient.mk ⟨f'⟩) (Submodule.Quotient.mk ⟨g'⟩) := rfl
  rw [hval,hrepr,map_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smul,smul_eq_mul,mul_comm,← hgZ k,hB_apply]
  congr 1
  have hdual : vBas.repr (Submodule.Quotient.mk ⟨g'⟩) k = vBas.dualBasis k (Submodule.Quotient.mk ⟨g'⟩) := by
    conv_rhs => rw [hrepr]
    rw [map_sum,sum_eq_single k]
    · rw [LinearMap.map_smul,smul_eq_mul,Module.Basis.dualBasis_apply_self,if_pos rfl,mul_one]
    · intro j _ hjk
      rw [LinearMap.map_smul,smul_eq_mul,Module.Basis.dualBasis_apply_self,if_neg hjk,mul_zero]
    · intro hn; exact absurd (mem_univ _) hn
  rw [hdual]
  have hbw : B (wBas k) = vBas.dualBasis k := Bequiv.apply_symm_apply (vBas.dualBasis k)
  rw [← hbw,← hfZ k,hB_apply]
noncomputable def z88 {G : Type} [AddCommGroup G] [Module Λ G] [Finite G] (S : Gemstone G)
    {M : Type} [AddCommGroup M] [Module Λ M] {r : ℕ}
    (g : Fin r → G →ₗ[Λ] M) (f : Fin r → M →ₗ[Λ] G) : M →ₗ[Λ] M :=
  ∑ k : Fin r,(g k).comp (S.α.comp (f k))
noncomputable def ηGem {G : Type} [AddCommGroup G] [Module Λ G] [Finite G] (S : Gemstone G)
    (M : Type) [AddCommGroup M] [Module Λ M] [Finite M] :
    M →ₗ[Λ] M :=
  let ex := z228 S M
  z88 S (Classical.choose (Classical.choose_spec ex))
    (Classical.choose (Classical.choose_spec (Classical.choose_spec ex)))
lemma z36 {G : Type} [AddCommGroup G] [Module Λ G] [Finite G] (S : Gemstone G)
    (M : Type) [AddCommGroup M] [Module Λ M] [Finite M] :
    ∃ (r : ℕ) (g : Fin r → G →ₗ[Λ] M) (f : Fin r → M →ₗ[Λ] G),
      z109 S g f ∧ ηGem S M = z88 S g f := by
  let ex := z228 S M
  exact ⟨Classical.choose ex,
    Classical.choose (Classical.choose_spec ex),
    Classical.choose (Classical.choose_spec (Classical.choose_spec ex)),
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec ex)),rfl⟩
lemma z306 {G : Type} [AddCommGroup G] [Module Λ G] [Finite G] (S : Gemstone G)
    {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N]
    {r s : ℕ} (g : Fin r → G →ₗ[Λ] M) (f : Fin r → M →ₗ[Λ] G) (hM : z109 S g f)
    (g' : Fin s → G →ₗ[Λ] N) (f' : Fin s → N →ₗ[Λ] G) (hN : z109 S g' f')
    (h : M →ₗ[Λ] N) :
    StableEq ((z88 S g' f').comp h) (h.comp (z88 S g f)) := by
  have hc0z : ∀ (c : ZMod 2) (e : G →ₗ[Λ] G),S.c0 (z2Lin c e) = c * S.c0 e := fun c e => by
    rcases z33 c with rfl | rfl <;> simp [z2Lin]
  let T : M →ₗ[Λ] N :=
    ∑ l : Fin s,∑ k : Fin r,
      z2Lin (S.c0 (((f' l).comp h).comp (g k))) ((g' l).comp (S.α.comp (f k)))
  have h1 : StableEq ((z88 S g' f').comp h) T := by
    unfold z88
    rw [z41]
    refine StableEq.sum Finset.univ _ _ fun l _ => ?_
    let δ : M →ₗ[Λ] G := (f' l).comp h - ∑ k : Fin r,z2Lin (S.c0 (((f' l).comp h).comp (g k))) (f k)
    have hδ : StableEq (S.α.comp δ) 0 := (S.av_left δ).mp fun g0 => by
      simp only [δ,LinearMap.sub_comp,z41,map_sub,map_sum,z30,hc0z]
      rw [hM ((f' l).comp h) g0,sub_self]
    have hstep := hδ.comp_left (g' l)
    have hlhs : (g' l).comp (S.α.comp δ) =
        ((g' l).comp (S.α.comp (f' l))).comp h -
        ∑ k : Fin r,z2Lin (S.c0 (((f' l).comp h).comp (g k))) ((g' l).comp (S.α.comp (f k))) := by
      simp only [δ,LinearMap.comp_sub,z42,z54,LinearMap.comp_assoc]
    rw [hlhs,LinearMap.comp_zero] at hstep
    obtain ⟨Q,p,q,hpq⟩ := hstep
    exact ⟨Q,p,q,by simpa using hpq⟩
  have h2 : StableEq (h.comp (z88 S g f)) T := by
    have hTswap : T = ∑ k : Fin r,∑ l : Fin s,
        z2Lin (S.c0 ((f' l).comp (h.comp (g k)))) ((g' l).comp (S.α.comp (f k))) := by
      unfold T; rw [Finset.sum_comm]
      refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => by
        rw [LinearMap.comp_assoc]
    rw [hTswap]
    unfold z88
    rw [z42]
    refine StableEq.sum Finset.univ _ _ fun k _ => ?_
    let ε : G →ₗ[Λ] N := h.comp (g k) - ∑ l : Fin s,z2Lin (S.c0 ((f' l).comp (h.comp (g k)))) (g' l)
    have hε : StableEq (ε.comp S.α) 0 := (S.av_right ε).mp fun f0 => by
      simp only [ε,LinearMap.comp_sub,z42,map_sub,map_sum,z54,hc0z]
      rw [hN f0 (h.comp (g k))]
      have hcomm : (∑ l : Fin s,S.c0 (f0.comp (g' l)) * S.c0 ((f' l).comp (h.comp (g k)))) =
          ∑ l : Fin s,S.c0 ((f' l).comp (h.comp (g k))) * S.c0 (f0.comp (g' l)) :=
        sum_congr rfl fun l _ => mul_comm _ _
      rw [hcomm,sub_self]
    have hstep := hε.comp_right (f k)
    have hlhs : (ε.comp S.α).comp (f k) =
        h.comp ((g k).comp (S.α.comp (f k))) -
        ∑ l : Fin s,z2Lin (S.c0 ((f' l).comp (h.comp (g k)))) ((g' l).comp (S.α.comp (f k))) := by
      simp only [ε,LinearMap.sub_comp,z41,z30,LinearMap.comp_assoc]
    rw [hlhs,LinearMap.zero_comp] at hstep
    obtain ⟨Q,p,q,hpq⟩ := hstep
    exact ⟨Q,p,q,by simpa using hpq⟩
  exact h1.trans h2.symm
lemma z231 {G : Type} [AddCommGroup G] [Module Λ G] [Finite G] (S : Gemstone G)
    {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] (h : M →ₗ[Λ] N) :
    StableEq ((ηGem S N).comp h) (h.comp (ηGem S M)) := by
  obtain ⟨r,g,f,hM,hr⟩ := z36 S M
  obtain ⟨s,g',f',hN,hs⟩ := z36 S N
  rw [hr,hs]
  exact z306 S g f hM g' f' hN h
lemma z69 {G : Type} [AddCommGroup G] [Module Λ G] [Finite G] (S : Gemstone G)
    {M : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    {r : ℕ} (g : Fin r → G →ₗ[Λ] M) (f : Fin r → M →ₗ[Λ] G) (hM : z109 S g f) :
    StableEq (z88 S g f) (ηGem S M) := by
  obtain ⟨s,g0,f0,hM0,hs⟩ := z36 S M
  rw [hs]
  have h := z306 S g0 f0 hM0 g f hM LinearMap.id
  simpa using h
lemma z281 {G : Type} [AddCommGroup G] [Module Λ G] [Finite G] (S : Gemstone G)
    (M : Type) [AddCommGroup M] [Module Λ M] [Finite M] :
    (ηGem S M).comp (ηGem S M) = 0 := by
  obtain ⟨r,g,f,_,hr⟩ := z36 S M
  rw [hr]
  unfold z88
  rw [z41]
  refine sum_eq_zero fun j _ => ?_
  rw [z42]
  refine sum_eq_zero fun k _ => ?_
  have hmid : (S.α.comp ((f j).comp (g k))).comp S.α = 0 := by
    obtain ⟨c1,hdec⟩ := S.end_decomp ((f j).comp (g k))
    rw [hdec,LinearMap.comp_add,z54,z54,LinearMap.comp_id,
      LinearMap.add_comp,z30,z30,S.α_sq,
      LinearMap.zero_comp,z63,z63,add_zero]
  have hassoc : ((g j).comp (S.α.comp (f j))).comp ((g k).comp (S.α.comp (f k))) =
      (g j).comp (((S.α.comp ((f j).comp (g k))).comp S.α).comp (f k)) := by
    simp only [LinearMap.comp_assoc]
  rw [hassoc,hmid,LinearMap.zero_comp,LinearMap.comp_zero]
lemma z102 {G : Type} [AddCommGroup G] [Module Λ G] [Finite G] (S : Gemstone G)
    (M : Type) [AddCommGroup M] [Module Λ M] [Finite M]
    (h : ∀ g : G →ₗ[Λ] M,StableEq (g.comp S.α) 0) :
    StableEq (ηGem S M) 0 := by
  have h0 : z109 S (Fin.elim0 : Fin 0 → G →ₗ[Λ] M) (Fin.elim0 : Fin 0 → M →ₗ[Λ] G) :=
    fun f' g' => by simp [(S.av_right g').mpr (h g') f']
  have hst := (z69 S Fin.elim0 Fin.elim0 h0).symm
  simpa [z88] using hst
lemma ηGem_self {G : Type} [AddCommGroup G] [Module Λ G] [Finite G] (S : Gemstone G) :
    StableEq (ηGem S G) S.α := by
  have h1 : z109 S (fun (_ : Fin 1) => LinearMap.id) (fun (_ : Fin 1) => LinearMap.id) :=
    fun f' g' => by simp [S.c0_comp_end]
  have hst := (z69 S (fun _ => LinearMap.id) (fun _ => LinearMap.id) h1).symm
  simpa [z88] using hst
noncomputable def z28 (M : Type) [AddCommGroup M] [Module Λ M] [Finite M] : M →ₗ[Λ] M :=
  ηGem gemX M + ηGem gemXp M
lemma z254 {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] (f : M →ₗ[Λ] N) :
    StableEq ((z28 N).comp f) (f.comp (z28 M)) := by
  unfold z28
  rw [LinearMap.add_comp,LinearMap.comp_add]
  exact StableEq.add (z231 gemX f) (z231 gemXp f)
lemma z253 (M : Type) [AddCommGroup M] [Module Λ M] [Finite M] :
    StableEq ((z28 M).comp (z28 M)) 0 := by
  have hzero : (z28 M).comp (z28 M) = 0 := by
    unfold z28
    rw [LinearMap.add_comp,LinearMap.comp_add,LinearMap.comp_add,
      z281 gemX M,z281 gemXp M,zero_add,add_zero]
    have h12 : (ηGem gemX M).comp (ηGem gemXp M) = 0 := by
      obtain ⟨r,g,f,_,hr⟩ := z36 gemX M
      obtain ⟨s,g',f',_,hs⟩ := z36 gemXp M
      rw [hr,hs]; unfold z88
      rw [z41]
      refine sum_eq_zero fun j _ => ?_
      rw [z42]
      refine sum_eq_zero fun k _ => ?_
      have hmid : (f j).comp (g' k) = 0 := z269 ((f j).comp (g' k))
      have hassoc : ((g j).comp (gemX.α.comp (f j))).comp ((g' k).comp (gemXp.α.comp (f' k))) =
          (g j).comp (gemX.α.comp (((f j).comp (g' k)).comp (gemXp.α.comp (f' k)))) := by
        simp only [LinearMap.comp_assoc]
      rw [hassoc,hmid,LinearMap.zero_comp,LinearMap.comp_zero,LinearMap.comp_zero]
    have h21 : (ηGem gemXp M).comp (ηGem gemX M) = 0 := by
      obtain ⟨r,g,f,_,hr⟩ := z36 gemX M
      obtain ⟨s,g',f',_,hs⟩ := z36 gemXp M
      rw [hr,hs]; unfold z88
      rw [z41]
      refine sum_eq_zero fun j _ => ?_
      rw [z42]
      refine sum_eq_zero fun k _ => ?_
      have hmid : (f' j).comp (g k) = 0 := z328 ((f' j).comp (g k))
      have hassoc : ((g' j).comp (gemXp.α.comp (f' j))).comp ((g k).comp (gemX.α.comp (f k))) =
          (g' j).comp (gemXp.α.comp (((f' j).comp (g k)).comp (gemX.α.comp (f k)))) := by
        simp only [LinearMap.comp_assoc]
      rw [hassoc,hmid,LinearMap.zero_comp,LinearMap.comp_zero,LinearMap.comp_zero]
    rw [h12,h21,add_zero]
  rw [hzero]
  exact StableEq.refl 0
lemma z319 (M : Type) [AddCommGroup M] [Module Λ M] [Finite M] :
    StableEq (z28 (nuMod M)) (nuMap (z28 M)) := by
  have h1 : ∀ (N : Type) [AddCommGroup N] [Module Λ N] [Finite N],
      StableEq (ηGem gemXp (nuMod N)) (nuMap (ηGem gemX N)) := fun N _ _ _ => by
    obtain ⟨r,g,f,hM,hr⟩ := z36 gemX N
    let g' : Fin r → XpMod →ₗ[Λ] nuMod N := fun k => (nuMap (g k)).comp nuXEquiv.symm.toLinearMap
    let f' : Fin r → nuMod N →ₗ[Λ] XpMod := fun k => nuXEquiv.toLinearMap.comp (nuMap (f k))
    have hdp : z109 gemXp g' f' := fun f0 g0 => by
      let f0X : N →ₗ[Λ] XMod :=
        nuModInvol.toLinearMap.comp
          ((nuMap (nuXEquiv.symm.toLinearMap.comp f0)).comp nuModInvol.symm.toLinearMap)
      let g0X : XMod →ₗ[Λ] N :=
        nuModInvol.toLinearMap.comp
          ((nuMap (g0.comp nuXEquiv.toLinearMap)).comp nuModInvol.symm.toLinearMap)
      have hL : c0Xp (f0.comp g0) = c0X (f0X.comp g0X) := rfl
      have hR1 : ∀ k,c0Xp (f0.comp (g' k)) = c0X (f0X.comp (g k)) := fun k => by
        change c0X (z56 (f0.comp (g' k))) = c0X (f0X.comp (g k))
        congr 1; apply LinearMap.ext; intro x
        change (nuXEquiv.symm (f0 ⟨g k (nuXEquiv.symm (nuXEquiv ⟨x⟩)).val⟩)).val =
          (nuXEquiv.symm (f0 ⟨g k x⟩)).val
        rw [nuXEquiv.symm_apply_apply]
      have hR2 : ∀ k,c0Xp ((f' k).comp g0) = c0X ((f k).comp g0X) := fun k => by
        change c0X (z56 ((f' k).comp g0)) = c0X ((f k).comp g0X)
        congr 1; apply LinearMap.ext; intro x
        change (nuXEquiv.symm (nuXEquiv ⟨f k (g0 (nuXEquiv ⟨x⟩)).val⟩)).val =
          f k (g0 (nuXEquiv ⟨x⟩)).val
        rw [nuXEquiv.symm_apply_apply]
      change c0Xp (f0.comp g0) = ∑ k : Fin r,c0Xp (f0.comp (g' k)) * c0Xp ((f' k).comp g0)
      rw [hL]; simp_rw [hR1,hR2]
      exact hM f0X g0X
    have heq : z88 gemXp g' f' = nuMap (ηGem gemX N) := by
      rw [hr]; unfold z88
      apply LinearMap.ext; intro x; apply nuMod.ext
      simp only [LinearMap.sum_apply,LinearMap.comp_apply,nuMap_apply_val]
      let ev : nuMod N →+ N := { toFun := nuMod.val,map_zero' := rfl,map_add' := fun _ _ => rfl }
      change ev (∑ k : Fin r,g' k (αXp (f' k x))) = ∑ k : Fin r,g k (αX (f k x.val))
      rw [map_sum]
      refine sum_congr rfl fun k _ => ?_
      change g k (nuXEquiv.symm (αXp (nuXEquiv ⟨f k x.val⟩))).val = g k (αX (f k x.val))
      rw [← z127,nuXEquiv.symm_apply_apply]; rfl
    rw [← heq]
    exact (z69 gemXp g' f' hdp).symm
  have h2 : StableEq (ηGem gemX (nuMod M)) (nuMap (ηGem gemXp M)) := by
    apply StableEq.of_nuMap
    have h1_nuM := h1 (nuMod M)
    have hnat := z231 gemXp (nuModInvol (M := M)).toLinearMap
    have hconj : StableEq (ηGem gemXp (nuMod (nuMod M))) (nuMap (nuMap (ηGem gemXp M))) := by
      have h3 := (hnat.comp_left (nuModInvol (M := M)).symm.toLinearMap).symm
      have hl : ((nuModInvol (M := M)).symm.toLinearMap.comp (nuModInvol.toLinearMap.comp (ηGem gemXp (nuMod (nuMod M))))) =
          ηGem gemXp (nuMod (nuMod M)) := by apply LinearMap.ext; intro x; rfl
      have hr' : ((nuModInvol (M := M)).symm.toLinearMap.comp ((ηGem gemXp M).comp nuModInvol.toLinearMap)) =
          nuMap (nuMap (ηGem gemXp M)) := by apply LinearMap.ext; intro x; rfl
      rw [hl,hr'] at h3
      exact h3
    exact h1_nuM.symm.trans hconj
  unfold z28
  have hadd : nuMap (ηGem gemX M + ηGem gemXp M) = nuMap (ηGem gemX M) + nuMap (ηGem gemXp M) := by
    apply LinearMap.ext; intro x; rfl
  rw [hadd,add_comm (nuMap (ηGem gemX M))]
  exact StableEq.add h2 (h1 M)
lemma z271 {M K : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup K] [Module Λ K] {P : FP}
    (j : M →ₗ[Λ] P.Mod) (q : P.Mod →ₗ[Λ] K)
    (f : M →ₗ[Λ] XMod) (F : P.Mod →ₗ[Λ] Pv 3) (f' : K →ₗ[Λ] XpMod)
    (g : XMod →ₗ[Λ] M) (G : Pv 3 →ₗ[Λ] P.Mod) (g' : XpMod →ₗ[Λ] K)
    (hFj : F.comp j = inclX.comp f) (hFq : projToXp.comp F = f'.comp q)
    (hGi : G.comp inclX = j.comp g) (hGq : q.comp G = g'.comp projToXp) :
    c0Xp (f'.comp g') = c0X (f.comp g) := by
  obtain ⟨a,b,hab⟩ := z313 (F.comp G)
  have hcX : c0X (f.comp g) = a := by
    have hfg : inclX.comp (f.comp g) = (F.comp G).comp inclX := by
      apply LinearMap.ext; intro x
      simp only [LinearMap.comp_apply]
      have h1 : G (inclX x) = j (g x) := congrArg (fun k => k x) hGi
      have h2 : F (j (g x)) = inclX (f (g x)) := congrArg (fun k => k (g x)) hFj
      rw [h1,h2]
    have h1 : (f (g gX)).1 = (F.comp G) gX.1 := congrArg (fun (k : XMod →ₗ[Λ] Pv 3) => k gX) hfg
    rw [hab] at h1
    have hval := congrArg (fun x : Pv 3 => x.val iotaBv) h1
    change c0X (f.comp g) = (z2Lin a LinearMap.id gX.1 + z2Lin b rmul_alpha gX.1).val iotaBv at hval
    rw [Pv.add_val,z43,z43,Pv.z2smul_val,Pv.z2smul_val,LinearMap.id_apply,
      ← αX_val gX,z259,z215,basisPv_val,basisPv_val,
      if_pos rfl] at hval
    have hne : iotaBv ≠ z161 := by decide
    rw [if_neg hne,mul_one,mul_zero,add_zero] at hval
    exact hval
  have hcXp : c0Xp (f'.comp g') = a := by
    have hfg' : (f'.comp g').comp projToXp = projToXp.comp (F.comp G) := by
      apply LinearMap.ext; intro x
      simp only [LinearMap.comp_apply]
      have h1 : q (G x) = g' (projToXp x) := congrArg (fun k => k x) hGq
      have h2 : projToXp (F (G x)) = f' (q (G x)) := congrArg (fun k => k (G x)) hFq
      rw [h2,h1]
    have hpg3 : projToXp (genPv 3) = gXp := rfl
    have h1 : (f' (g' gXp)).1 = (projToXp ((F.comp G) (genPv 3))).1 := by
      have h := congrArg (fun (k : Pv 3 →ₗ[Λ] XpMod) => (k (genPv 3)).1) hfg'
      simp only [LinearMap.comp_apply,hpg3] at h
      exact h
    rw [hab] at h1
    have hval := congrArg (fun x : Pv 1 => x.val qBv) h1
    change ((f'.comp g') gXp).1.val qBv = _ at hval
    rw [← z296] at hval
    rw [LinearMap.add_apply,map_add,show (projToXp (z2Lin a LinearMap.id (genPv 3)) +
        projToXp (z2Lin b rmul_alpha (genPv 3))).1 =
        (projToXp (z2Lin a LinearMap.id (genPv 3))).1 + (projToXp (z2Lin b rmul_alpha (genPv 3))).1 from rfl,
      Pv.add_val] at hval
    have hta : (projToXp (z2Lin a LinearMap.id (genPv 3))).1 = z16 a gXp.1 := by
      rw [z43,LinearMap.id_apply]
      change rmul_q (z16 a (genPv 3)) = z16 a gXp.1
      rw [z53 rmul_q,z175,← z270]
    have htb : (projToXp (z2Lin b rmul_alpha (genPv 3))).1 = z16 b (αXp gXp).1 := by
      rw [z43,αXp_val gXp]
      change rmul_q (z16 b (rmul_alpha (genPv 3))) = z16 b (rmul_alphap gXp.1)
      rw [z53 rmul_q]
      apply congrArg (z16 b)
      have hq := congrArg (fun (k : Pv 3 →ₗ[Λ] Pv 1) => k (genPv 3)) z90
      simp only [LinearMap.comp_apply] at hq
      rw [hq,z175,← z270]
    rw [hta,htb,Pv.z2smul_val,Pv.z2smul_val,z270,z256,basisPv_val,basisPv_val,
      if_pos rfl] at hval
    have hne : qBv ≠ z323 := by decide
    rw [if_neg hne,mul_one,mul_zero,add_zero] at hval
    exact hval
  rw [hcXp,hcX]
lemma z272 {M K : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup K] [Module Λ K] {P : FP}
    (j : M →ₗ[Λ] P.Mod) (q : P.Mod →ₗ[Λ] K)
    (f : M →ₗ[Λ] XpMod) (F : P.Mod →ₗ[Λ] Pv 1) (f' : K →ₗ[Λ] XMod)
    (g : XpMod →ₗ[Λ] M) (G : Pv 1 →ₗ[Λ] P.Mod) (g' : XMod →ₗ[Λ] K)
    (hFj : F.comp j = inclXp.comp f) (hFq : projToX.comp F = f'.comp q)
    (hGi : G.comp inclXp = j.comp g) (hGq : q.comp G = g'.comp projToX) :
    c0X (f'.comp g') = c0Xp (f.comp g) := by
  obtain ⟨a,b,hab⟩ := z314 (F.comp G)
  have hcXp : c0Xp (f.comp g) = a := by
    have hfg : inclXp.comp (f.comp g) = (F.comp G).comp inclXp := by
      apply LinearMap.ext; intro x
      simp only [LinearMap.comp_apply]
      have h1 : G (inclXp x) = j (g x) := congrArg (fun k => k x) hGi
      have h2 : F (j (g x)) = inclXp (f (g x)) := congrArg (fun k => k (g x)) hFj
      rw [h1,h2]
    have h1 : (f (g gXp)).1 = (F.comp G) gXp.1 := congrArg (fun (k : XpMod →ₗ[Λ] Pv 1) => k gXp) hfg
    rw [hab] at h1
    have hval := congrArg (fun x : Pv 1 => x.val qBv) h1
    change ((f.comp g) gXp).1.val qBv = _ at hval
    rw [← z296] at hval
    rw [LinearMap.add_apply,Pv.add_val,z43,z43,Pv.z2smul_val,Pv.z2smul_val,
      LinearMap.id_apply,← αXp_val gXp,z270,z256,basisPv_val,basisPv_val,
      if_pos rfl] at hval
    have hne : qBv ≠ z323 := by decide
    rw [if_neg hne,mul_one,mul_zero,add_zero] at hval
    exact hval
  have hcX : c0X (f'.comp g') = a := by
    have hfg' : (f'.comp g').comp projToX = projToX.comp (F.comp G) := by
      apply LinearMap.ext; intro x
      simp only [LinearMap.comp_apply]
      have h1 : q (G x) = g' (projToX x) := congrArg (fun k => k x) hGq
      have h2 : projToX (F (G x)) = f' (q (G x)) := congrArg (fun k => k (G x)) hFq
      rw [h2,h1]
    have hpg1 : projToX (genPv 1) = gX := rfl
    have h1 : (f' (g' gX)).1 = (projToX ((F.comp G) (genPv 1))).1 := by
      have h := congrArg (fun (k : Pv 1 →ₗ[Λ] XMod) => (k (genPv 1)).1) hfg'
      simp only [LinearMap.comp_apply,hpg1] at h
      exact h
    rw [hab] at h1
    have hval := congrArg (fun x : Pv 3 => x.val iotaBv) h1
    change c0X (f'.comp g') = _ at hval
    rw [LinearMap.add_apply,map_add,show (projToX (z2Lin a LinearMap.id (genPv 1)) +
        projToX (z2Lin b rmul_alphap (genPv 1))).1 =
        (projToX (z2Lin a LinearMap.id (genPv 1))).1 + (projToX (z2Lin b rmul_alphap (genPv 1))).1 from rfl,
      Pv.add_val] at hval
    have hta : (projToX (z2Lin a LinearMap.id (genPv 1))).1 = z16 a gX.1 := by
      rw [z43,LinearMap.id_apply]
      change rmul_iota (z16 a (genPv 1)) = z16 a gX.1
      rw [z53 rmul_iota,z133,← z259]
    have htb : (projToX (z2Lin b rmul_alphap (genPv 1))).1 = z16 b (αX gX).1 := by
      rw [z43,αX_val gX]
      change rmul_iota (z16 b (rmul_alphap (genPv 1))) = z16 b (rmul_alpha gX.1)
      rw [z53 rmul_iota]
      apply congrArg (z16 b)
      have hi := congrArg (fun (k : Pv 1 →ₗ[Λ] Pv 3) => k (genPv 1)) z55
      simp only [LinearMap.comp_apply] at hi
      rw [hi,z133,← z259]
    rw [hta,htb,Pv.z2smul_val,Pv.z2smul_val,z259,z215,basisPv_val,basisPv_val,
      if_pos rfl] at hval
    have hne : iotaBv ≠ z161 := by decide
    rw [if_neg hne,mul_one,mul_zero,add_zero] at hval
    exact hval
  rw [hcX,hcXp]
lemma z264 {M K : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup K] [Module Λ K] [Finite K] {P : FP}
    (j : M →ₗ[Λ] P.Mod) (q : P.Mod →ₗ[Λ] K)
    (hj : Function.Injective j) (hex : ExactAt j q) (hq : Function.Surjective q) :
    ∃ τ : P ⟶ P,τ.hom.comp j = j.comp (z28 M) ∧ q.comp τ.hom = (z28 K).comp q := by
  have factorQ : ∀ {N : Type} [AddCommGroup N] [Module Λ N] (φ : P.Mod →ₗ[Λ] N),
      φ.comp j = 0 → ∃ ψ : K →ₗ[Λ] N,ψ.comp q = φ := fun {N} _ _ φ hφj => by
    have hker : LinearMap.ker q ≤ LinearMap.ker φ := by
      intro x hx
      have hmem : x ∈ LinearMap.range j := by rw [hex]; exact hx
      obtain ⟨m,rfl⟩ := hmem
      exact congrArg (fun (k : M →ₗ[Λ] N) => k m) hφj
    let iso : (P.Mod ⧸ LinearMap.ker q) ≃ₗ[Λ] K := LinearMap.quotKerEquivOfSurjective q hq
    refine ⟨(Submodule.liftQ (LinearMap.ker q) φ hker).comp iso.symm.toLinearMap,?_⟩
    apply LinearMap.ext; intro x
    have hinv : iso.symm (q x) = Submodule.Quotient.mk x := by
      apply iso.injective; simp [iso]
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,hinv,Submodule.liftQ_apply]
  have factorProjXp : ∀ {N : Type} [AddCommGroup N] [Module Λ N] (φ : Pv 3 →ₗ[Λ] N),
      φ.comp inclX = 0 → ∃ ψ : XpMod →ₗ[Λ] N,ψ.comp projToXp = φ := fun {N} _ _ φ hφ => by
    have hker : LinearMap.ker projToXp ≤ LinearMap.ker φ := by
      intro x hx
      have hmem : x ∈ LinearMap.range inclX := by rw [z236]; exact hx
      obtain ⟨m,rfl⟩ := hmem
      exact congrArg (fun (k : XMod →ₗ[Λ] N) => k m) hφ
    let iso : (Pv 3 ⧸ LinearMap.ker projToXp) ≃ₗ[Λ] XpMod :=
      LinearMap.quotKerEquivOfSurjective projToXp z205
    refine ⟨(Submodule.liftQ (LinearMap.ker projToXp) φ hker).comp iso.symm.toLinearMap,?_⟩
    apply LinearMap.ext; intro x
    have hinv : iso.symm (projToXp x) = Submodule.Quotient.mk x := by
      apply iso.injective; simp [iso]
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,hinv,Submodule.liftQ_apply]
  have factorProjX : ∀ {N : Type} [AddCommGroup N] [Module Λ N] (φ : Pv 1 →ₗ[Λ] N),
      φ.comp inclXp = 0 → ∃ ψ : XMod →ₗ[Λ] N,ψ.comp projToX = φ := fun {N} _ _ φ hφ => by
    have hker : LinearMap.ker projToX ≤ LinearMap.ker φ := by
      intro x hx
      have hmem : x ∈ LinearMap.range inclXp := by rw [z235]; exact hx
      obtain ⟨m,rfl⟩ := hmem
      exact congrArg (fun (k : XpMod →ₗ[Λ] N) => k m) hφ
    let iso : (Pv 1 ⧸ LinearMap.ker projToX) ≃ₗ[Λ] XMod :=
      LinearMap.quotKerEquivOfSurjective projToX z80
    refine ⟨(Submodule.liftQ (LinearMap.ker projToX) φ hker).comp iso.symm.toLinearMap,?_⟩
    apply LinearMap.ext; intro x
    have hinv : iso.symm (projToX x) = Submodule.Quotient.mk x := by
      apply iso.injective; simp [iso]
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,hinv,Submodule.liftQ_apply]
  have pairTransfer3 := z271 j q
  have pairTransfer1 := z272 j q
  obtain ⟨r,g,f,hdpX,hηX⟩ := z36 gemX M
  have hliftF : ∀ k : Fin r,∃ F : P.Mod →ₗ[Λ] Pv 3,F.comp j = inclX.comp (f k) :=
    fun k => Pv_inj 3 j hj (inclX.comp (f k))
  have hliftG : ∀ k : Fin r,∃ G : Pv 3 →ₗ[Λ] P.Mod,G.comp inclX = j.comp (g k) :=
    fun k => z217 P inclX z312 (j.comp (g k))
  choose F hF using hliftF
  choose G hG using hliftG
  have hfacF : ∀ k : Fin r,∃ f' : K →ₗ[Λ] XpMod,f'.comp q = projToXp.comp (F k) := fun k =>
    factorQ (projToXp.comp (F k)) (by
      apply LinearMap.ext; intro m
      simp only [LinearMap.comp_apply,LinearMap.zero_apply]
      have h1 : F k (j m) = inclX (f k m) := congrArg (fun l => l m) (hF k)
      rw [h1]; exact Subtype.ext (f k m).2)
  have hfacG : ∀ k : Fin r,∃ g' : XpMod →ₗ[Λ] K,g'.comp projToXp = q.comp (G k) := fun k =>
    factorProjXp (q.comp (G k)) (by
      apply LinearMap.ext; intro x
      simp only [LinearMap.comp_apply,LinearMap.zero_apply]
      have h1 : G k (inclX x) = j (g k x) := congrArg (fun l => l x) (hG k)
      rw [h1]
      have hmem : j (g k x) ∈ LinearMap.ker q := by rw [← hex]; exact ⟨g k x,rfl⟩
      exact hmem)
  choose f' hf' using hfacF
  choose g' hg' using hfacG
  have hdpXpK : z109 gemXp g' f' := fun f0 g0 => by
    obtain ⟨F0,hF0⟩ := z188 P projToXp z205 (f0.comp q)
    obtain ⟨G0,hG0⟩ := Pv_proj 3 q hq (g0.comp projToXp)
    have hF0j : ∀ m,F0 (j m) ∈ LinearMap.ker projToXp := fun m => by
      change projToXp (F0 (j m)) = 0
      have h1 := congrArg (fun (k : P.Mod →ₗ[Λ] XpMod) => k (j m)) hF0
      simp only [LinearMap.comp_apply] at h1
      rw [h1]
      have hqm : q (j m) = 0 := by
        have hmem : j m ∈ LinearMap.ker q := by rw [← hex]; exact ⟨m,rfl⟩
        exact hmem
      rw [hqm,map_zero]
    let f0M : M →ₗ[Λ] XMod :=
      (F0.comp j).codRestrict (LinearMap.ker rmul_q) fun m => congrArg Subtype.val (hF0j m)
    have hF0M : F0.comp j = inclX.comp f0M := rfl
    have hG0i : ∀ x : XMod,G0 (inclX x) ∈ LinearMap.range j := fun x => by
      rw [hex]
      change q (G0 (inclX x)) = 0
      have h1 := congrArg (fun (k : Pv 3 →ₗ[Λ] K) => k (inclX x)) hG0
      simp only [LinearMap.comp_apply] at h1
      rw [h1]
      have hpx : projToXp (inclX x) = 0 := Subtype.ext x.2
      rw [hpx,map_zero]
    let eJ : M ≃ₗ[Λ] LinearMap.range j := LinearEquiv.ofInjective j hj
    let g0M : XMod →ₗ[Λ] M :=
      eJ.symm.toLinearMap.comp ((G0.comp inclX).codRestrict (LinearMap.range j) hG0i)
    have hG0M : G0.comp inclX = j.comp g0M := by
      apply LinearMap.ext; intro x
      change G0 (inclX x) = (eJ (eJ.symm ⟨G0 (inclX x),hG0i x⟩)).1
      rw [eJ.apply_symm_apply]
    change c0Xp (f0.comp g0) = ∑ k : Fin r,c0Xp (f0.comp (g' k)) * c0Xp ((f' k).comp g0)
    rw [pairTransfer3 f0M F0 f0 g0M G0 g0 hF0M hF0 hG0M hG0]
    have hR1 : ∀ k,c0Xp (f0.comp (g' k)) = c0X (f0M.comp (g k)) := fun k =>
      pairTransfer3 f0M F0 f0 (g k) (G k) (g' k) hF0M hF0 (hG k) (hg' k).symm
    have hR2 : ∀ k,c0Xp ((f' k).comp g0) = c0X ((f k).comp g0M) := fun k =>
      pairTransfer3 (f k) (F k) (f' k) g0M G0 g0 (hF k) (hf' k).symm hG0M hG0
    simp_rw [hR1,hR2]
    exact hdpX f0M g0M
  let τX : P.Mod →ₗ[Λ] P.Mod := ∑ k : Fin r,(G k).comp (rmul_alpha.comp (F k))
  have hτXj : τX.comp j = j.comp (ηGem gemX M) := by
    rw [hηX]; unfold z88 τX
    rw [z41,z42]
    refine sum_congr rfl fun k _ => ?_
    apply LinearMap.ext; intro m
    simp only [LinearMap.comp_apply]
    have h1 : F k (j m) = inclX (f k m) := congrArg (fun (l : M →ₗ[Λ] Pv 3) => l m) (hF k)
    rw [h1]
    have h2 : rmul_alpha (inclX (f k m)) = inclX (αX (f k m)) := rfl
    rw [h2]
    exact congrArg (fun (l : XMod →ₗ[Λ] P.Mod) => l (αX (f k m))) (hG k)
  have hτXq : q.comp τX = (z88 gemXp g' f').comp q := by
    unfold τX z88
    rw [z42,z41]
    refine sum_congr rfl fun k _ => ?_
    apply LinearMap.ext; intro x
    simp only [LinearMap.comp_apply]
    have h1 := congrArg (fun (l : Pv 3 →ₗ[Λ] K) => l (rmul_alpha (F k x))) (hg' k).symm
    simp only [LinearMap.comp_apply] at h1
    rw [h1]
    have h2 := congrArg (fun (l : Pv 3 →ₗ[Λ] XpMod) => l (F k x)) z185
    simp only [LinearMap.comp_apply] at h2
    rw [h2]
    have h3 := congrArg (fun (l : P.Mod →ₗ[Λ] XpMod) => l x) (hf' k).symm
    simp only [LinearMap.comp_apply] at h3
    rw [h3]; rfl
  obtain ⟨s,gp,fp,hdpXp,hηXp⟩ := z36 gemXp M
  have hliftFp : ∀ k : Fin s,∃ Fp : P.Mod →ₗ[Λ] Pv 1,Fp.comp j = inclXp.comp (fp k) :=
    fun k => Pv_inj 1 j hj (inclXp.comp (fp k))
  have hliftGp : ∀ k : Fin s,∃ Gp : Pv 1 →ₗ[Λ] P.Mod,Gp.comp inclXp = j.comp (gp k) :=
    fun k => z217 P inclXp inclXp_inj (j.comp (gp k))
  choose Fp hFp using hliftFp
  choose Gp hGp using hliftGp
  have hfacFp : ∀ k : Fin s,∃ fp' : K →ₗ[Λ] XMod,fp'.comp q = projToX.comp (Fp k) := fun k =>
    factorQ (projToX.comp (Fp k)) (by
      apply LinearMap.ext; intro m
      simp only [LinearMap.comp_apply,LinearMap.zero_apply]
      have h1 : Fp k (j m) = inclXp (fp k m) := congrArg (fun l => l m) (hFp k)
      rw [h1]; exact Subtype.ext (fp k m).2)
  have hfacGp : ∀ k : Fin s,∃ gp' : XMod →ₗ[Λ] K,gp'.comp projToX = q.comp (Gp k) := fun k =>
    factorProjX (q.comp (Gp k)) (by
      apply LinearMap.ext; intro x
      simp only [LinearMap.comp_apply,LinearMap.zero_apply]
      have h1 : Gp k (inclXp x) = j (gp k x) := congrArg (fun l => l x) (hGp k)
      rw [h1]
      have hmem : j (gp k x) ∈ LinearMap.ker q := by rw [← hex]; exact ⟨gp k x,rfl⟩
      exact hmem)
  choose fp' hfp' using hfacFp
  choose gp' hgp' using hfacGp
  have hdpXK : z109 gemX gp' fp' := fun f0 g0 => by
    obtain ⟨F0,hF0⟩ := z188 P projToX z80 (f0.comp q)
    obtain ⟨G0,hG0⟩ := Pv_proj 1 q hq (g0.comp projToX)
    have hF0j : ∀ m,F0 (j m) ∈ LinearMap.ker projToX := fun m => by
      change projToX (F0 (j m)) = 0
      have h1 := congrArg (fun (k : P.Mod →ₗ[Λ] XMod) => k (j m)) hF0
      simp only [LinearMap.comp_apply] at h1
      rw [h1]
      have hqm : q (j m) = 0 := by
        have hmem : j m ∈ LinearMap.ker q := by rw [← hex]; exact ⟨m,rfl⟩
        exact hmem
      rw [hqm,map_zero]
    let f0M : M →ₗ[Λ] XpMod :=
      (F0.comp j).codRestrict (LinearMap.ker rmul_iota) fun m => congrArg Subtype.val (hF0j m)
    have hF0M : F0.comp j = inclXp.comp f0M := rfl
    have hG0i : ∀ x : XpMod,G0 (inclXp x) ∈ LinearMap.range j := fun x => by
      rw [hex]
      change q (G0 (inclXp x)) = 0
      have h1 := congrArg (fun (k : Pv 1 →ₗ[Λ] K) => k (inclXp x)) hG0
      simp only [LinearMap.comp_apply] at h1
      rw [h1]
      have hpx : projToX (inclXp x) = 0 := Subtype.ext x.2
      rw [hpx,map_zero]
    let eJ : M ≃ₗ[Λ] LinearMap.range j := LinearEquiv.ofInjective j hj
    let g0M : XpMod →ₗ[Λ] M :=
      eJ.symm.toLinearMap.comp ((G0.comp inclXp).codRestrict (LinearMap.range j) hG0i)
    have hG0M : G0.comp inclXp = j.comp g0M := by
      apply LinearMap.ext; intro x
      change G0 (inclXp x) = (eJ (eJ.symm ⟨G0 (inclXp x),hG0i x⟩)).1
      rw [eJ.apply_symm_apply]
    change c0X (f0.comp g0) = ∑ k : Fin s,c0X (f0.comp (gp' k)) * c0X ((fp' k).comp g0)
    rw [pairTransfer1 f0M F0 f0 g0M G0 g0 hF0M hF0 hG0M hG0]
    have hR1 : ∀ k,c0X (f0.comp (gp' k)) = c0Xp (f0M.comp (gp k)) := fun k =>
      pairTransfer1 f0M F0 f0 (gp k) (Gp k) (gp' k) hF0M hF0 (hGp k) (hgp' k).symm
    have hR2 : ∀ k,c0X ((fp' k).comp g0) = c0Xp ((fp k).comp g0M) := fun k =>
      pairTransfer1 (fp k) (Fp k) (fp' k) g0M G0 g0 (hFp k) (hfp' k).symm hG0M hG0
    simp_rw [hR1,hR2]
    exact hdpXp f0M g0M
  let τXp : P.Mod →ₗ[Λ] P.Mod := ∑ k : Fin s,(Gp k).comp (rmul_alphap.comp (Fp k))
  have hτXpj : τXp.comp j = j.comp (ηGem gemXp M) := by
    rw [hηXp]; unfold z88 τXp
    rw [z41,z42]
    refine sum_congr rfl fun k _ => ?_
    apply LinearMap.ext; intro m
    simp only [LinearMap.comp_apply]
    have h1 : Fp k (j m) = inclXp (fp k m) := congrArg (fun (l : M →ₗ[Λ] Pv 1) => l m) (hFp k)
    rw [h1]
    have h2 : rmul_alphap (inclXp (fp k m)) = inclXp (αXp (fp k m)) := rfl
    rw [h2]
    exact congrArg (fun (l : XpMod →ₗ[Λ] P.Mod) => l (αXp (fp k m))) (hGp k)
  have hτXpq : q.comp τXp = (z88 gemX gp' fp').comp q := by
    unfold τXp z88
    rw [z42,z41]
    refine sum_congr rfl fun k _ => ?_
    apply LinearMap.ext; intro x
    simp only [LinearMap.comp_apply]
    have h1 := congrArg (fun (l : Pv 1 →ₗ[Λ] K) => l (rmul_alphap (Fp k x))) (hgp' k).symm
    simp only [LinearMap.comp_apply] at h1
    rw [h1]
    have h2 := congrArg (fun (l : Pv 1 →ₗ[Λ] XMod) => l (Fp k x)) z186
    simp only [LinearMap.comp_apply] at h2
    rw [h2]
    have h3 := congrArg (fun (l : P.Mod →ₗ[Λ] XMod) => l x) (hfp' k).symm
    simp only [LinearMap.comp_apply] at h3
    rw [h3]; rfl
  let τ0 : P.Mod →ₗ[Λ] P.Mod := τX + τXp
  let hK : K →ₗ[Λ] K := z88 gemX gp' fp' + z88 gemXp g' f'
  have hstK : StableEq (z28 K) hK := by
    unfold z28 hK
    exact StableEq.add (z69 gemX gp' fp' hdpXK).symm
      (z69 gemXp g' f' hdpXpK).symm
  obtain ⟨Q,pQ,rQ,hQr⟩ := hstK
  obtain ⟨rLift,hrLift⟩ := z188 Q q hq rQ
  let τ : P ⟶ P := ⟨τ0 + (rLift.comp pQ).comp q⟩
  refine ⟨τ,?_,?_⟩
  · change (τ0 + (rLift.comp pQ).comp q).comp j = j.comp (z28 M)
    have hqj0 : ((rLift.comp pQ).comp q).comp j = 0 := by
      apply LinearMap.ext; intro m
      simp only [LinearMap.comp_apply,LinearMap.zero_apply]
      have hmem : j m ∈ LinearMap.ker q := by rw [← hex]; exact ⟨m,rfl⟩
      rw [show q (j m) = 0 from hmem,map_zero,map_zero]
    rw [LinearMap.add_comp,hqj0,add_zero]
    unfold τ0 z28
    rw [LinearMap.add_comp,LinearMap.comp_add,hτXj,hτXpj]
  · change q.comp (τ0 + (rLift.comp pQ).comp q) = (z28 K).comp q
    have hq2 : q.comp ((rLift.comp pQ).comp q) = (rQ.comp pQ).comp q := by
      apply LinearMap.ext; intro x
      simp only [LinearMap.comp_apply]
      exact congrArg (fun k => k (pQ (q x))) hrLift
    rw [LinearMap.comp_add,hq2,
      show q.comp τ0 = hK.comp q by
        unfold τ0 hK; rw [LinearMap.comp_add,LinearMap.add_comp,hτXq,hτXpq,add_comm],
      ← LinearMap.add_comp]
    congr 1
    have hsub : hK + rQ.comp pQ = z28 K := by
      rw [← hQr]; abel
    exact hsub
noncomputable def concreteExactSys : ExactSys where
  proj := z188
  inj := z217
  exists_embed := z234
  exists_surj := z248
  seq := z6
  map0 := z58
  map1 := z65
  map2 := z237
  map0_ι := z318
  map1_d0 := z303
  map2_d1 := z302
  π_map2 := z316
  map0_comp := z200
  map1_comp := z275
  map2_comp := z200
  map0_zero := z199
  map1_zero := z274
  map2_zero := z199
  map0_exact := z179
  map1_exact := z263
  map2_exact := z179
  seq_nu := z317
  η := z28
  η_natural := z254
  η_sq_zero := z253
  η_nu := z319
  η_syzygy := z264
def PU : FP := ⟨fun v => if v = 3 ∨ v = 1 then 1 else 0⟩
def equivPU : PU.Mod ≃ₗ[Λ] Pv 3 × Pv 1 where
  toFun x := (x 3 ⟨0,by simp [PU]⟩,x 1 ⟨0,by simp [PU]⟩)
  invFun p w i :=
    if h3 : w = 3 then h3 ▸ p.1
    else if h1 : w = 1 then h1 ▸ p.2
    else 0
  left_inv x := by
    funext w i
    by_cases h3 : w = 3
    · subst h3
      have hi : i = ⟨0,by simp [PU]⟩ := by
        have hlt : i.1 < 1 := by simpa [PU] using i.2
        ext; change i.1 = 0; omega
      subst hi; simp
    · by_cases h1 : w = 1
      · subst h1
        have hi : i = ⟨0,by simp [PU]⟩ := by
          have hlt : i.1 < 1 := by simpa [PU] using i.2
          ext; change i.1 = 0; omega
        subst hi; simp
      · exfalso; simpa [PU,h3,h1] using i.2
  right_inv p := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def UMod_sub : Submodule Λ PU.Mod where
  carrier := { x | rmul_iota (equivPU x).2 = 0 ∧ rmul_q (equivPU x).1 = rmul_alphap (equivPU x).2 }
  zero_mem' := by simp
  add_mem' := fun {x y} hx hy => by
    simp [hx.1,hy.1,hx.2,hy.2]
  smul_mem' := fun a {x} hx => by
    simp [hx.1,hx.2]
abbrev UMod : Type := ↥UMod_sub
abbrev OUMod : Type := PU.Mod ⧸ UMod_sub
def jU : UMod →ₗ[Λ] PU.Mod := UMod_sub.subtype
def qU : PU.Mod →ₗ[Λ] OUMod := UMod_sub.mkQ
lemma jU_inj : Function.Injective jU := Subtype.val_injective
lemma exact_jU_qU : ExactAt jU qU := by
  ext x
  simp only [LinearMap.mem_range,LinearMap.mem_ker,jU,qU,Submodule.subtype_apply,
    Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  exact ⟨fun ⟨u,hu⟩ => hu ▸ u.2,fun hx => ⟨⟨x,hx⟩,rfl⟩⟩
lemma qU_surj : Function.Surjective qU := Submodule.Quotient.mk_surjective UMod_sub
instance : Finite OUMod := Finite.of_surjective qU qU_surj
def sXpU : XpMod →ₗ[Λ] UMod where
  toFun x' := ⟨equivPU.symm (0,rmul_alphap x'.1),by
    simp only [UMod_sub,Submodule.mem_mk,AddSubmonoid.mem_mk,AddSubsemigroup.mem_mk,
      Set.mem_ofPred_eq,LinearEquiv.apply_symm_apply]
    constructor
    · have h := congrArg (fun (f : Pv 1 →ₗ[Λ] Pv 3) => f x'.1) z55
      simp only [LinearMap.comp_apply] at h
      rw [h,x'.2,map_zero]
    · rw [map_zero]
      exact (congrArg (fun (f : Pv 1 →ₗ[Λ] Pv 1) => f x'.1) z243).symm⟩
  map_add' x y := by
    apply Subtype.ext
    change equivPU.symm (0,rmul_alphap (x.1 + y.1)) =
      equivPU.symm (0,rmul_alphap x.1) + equivPU.symm (0,rmul_alphap y.1)
    rw [map_add,← equivPU.symm.map_add]
    exact congrArg equivPU.symm (Prod.ext (add_zero (0 : Pv 3)).symm rfl)
  map_smul' a x := by
    apply Subtype.ext
    change equivPU.symm (0,rmul_alphap (a • x.1)) = a • equivPU.symm (0,rmul_alphap x.1)
    rw [map_smul,← equivPU.symm.map_smul]
    exact congrArg equivPU.symm (Prod.ext (smul_zero a).symm rfl)
def KY_sub : Submodule Λ (UMod × Pv 1) := LinearMap.range (sXpU.prod inclXp)
abbrev YMod : Type := (UMod × Pv 1) ⧸ KY_sub
def mkY : (UMod × Pv 1) →ₗ[Λ] YMod := KY_sub.mkQ
instance : Finite YMod := Finite.of_surjective mkY (Submodule.Quotient.mk_surjective KY_sub)
def wUY : UMod →ₗ[Λ] YMod := mkY.comp (LinearMap.inl Λ UMod (Pv 1))
def zYX : YMod →ₗ[Λ] XMod :=
  Submodule.liftQ KY_sub (projToX.comp (LinearMap.snd Λ UMod (Pv 1))) (by
    rintro _ ⟨x',rfl⟩
    change projToX x'.1 = 0
    exact Subtype.ext x'.2)
lemma wUY_inj : Function.Injective wUY := by
  rw [← LinearMap.ker_eq_bot,Submodule.eq_bot_iff]
  intro u hu
  have hmem : (u,(0 : Pv 1)) ∈ KY_sub := (Submodule.Quotient.mk_eq_zero KY_sub).mp hu
  obtain ⟨x',hx'⟩ := hmem
  have h2 : x'.1 = 0 := congrArg Prod.snd hx'
  have hx0 : x' = 0 := Subtype.ext h2
  have h1 : sXpU x' = u := congrArg Prod.fst hx'
  rw [hx0,map_zero] at h1
  exact h1.symm
lemma exact_wUY_zYX : ExactAt wUY zYX := by
  ext y
  simp only [LinearMap.mem_range,LinearMap.mem_ker]
  obtain ⟨⟨u,p1⟩,rfl⟩ := Submodule.Quotient.mk_surjective KY_sub y
  constructor
  · rintro ⟨u0,hu0⟩
    rw [← hu0]
    change projToX 0 = 0
    exact map_zero projToX
  · intro hz
    have hp1 : rmul_iota p1 = 0 := congrArg Subtype.val hz
    let x' : XpMod := ⟨p1,hp1⟩
    refine ⟨u - sXpU x',?_⟩
    change mkY (u - sXpU x',0) = mkY (u,p1)
    rw [← sub_eq_zero,← map_sub]
    rw [show ((u - sXpU x',(0 : Pv 1)) - (u,p1) : UMod × Pv 1) = -(sXpU x',p1) by
      apply Prod.ext <;> simp [sub_eq_add_neg]]
    rw [map_neg,neg_eq_zero]
    exact (Submodule.Quotient.mk_eq_zero KY_sub).mpr ⟨x',rfl⟩
lemma zYX_surj : Function.Surjective zYX := fun x => by
  obtain ⟨p1,hp1⟩ := z80 x
  exact ⟨mkY (0,p1),hp1⟩
def Φ_raw : (UMod × Pv 1) →ₗ[Λ] PU.Mod :=
  jU.comp (LinearMap.fst Λ UMod (Pv 1)) +
    (equivPU.symm.toLinearMap.comp ((LinearMap.inr Λ (Pv 3) (Pv 1)).comp rmul_alphap)).comp
      (LinearMap.snd Λ UMod (Pv 1))
def Φ_conn : YMod →ₗ[Λ] PU.Mod :=
  Submodule.liftQ KY_sub Φ_raw (by
    rintro _ ⟨x',rfl⟩
    change jU (sXpU x') + equivPU.symm (0,rmul_alphap x'.1) = 0
    change equivPU.symm (0,rmul_alphap x'.1) + equivPU.symm (0,rmul_alphap x'.1) = 0
    exact z10 _)
lemma Φ_conn_wUY : Φ_conn.comp wUY = jU := by
  apply LinearMap.ext; intro u
  change jU u + equivPU.symm (0,rmul_alphap 0) = jU u
  simp
noncomputable def Os : XMod →ₗ[Λ] OUMod :=
  let hker : LinearMap.ker zYX ≤ LinearMap.ker (qU.comp Φ_conn) := by
    intro y hy
    have hmem : y ∈ LinearMap.range wUY := by rw [exact_wUY_zYX]; exact hy
    obtain ⟨u,rfl⟩ := hmem
    change qU (Φ_conn (wUY u)) = 0
    have hφ : Φ_conn (wUY u) = jU u := congrArg (fun (k : UMod →ₗ[Λ] PU.Mod) => k u) Φ_conn_wUY
    rw [hφ]
    have hj : jU u ∈ LinearMap.ker qU := by rw [← exact_jU_qU]; exact ⟨u,rfl⟩
    exact hj
  (Submodule.liftQ (LinearMap.ker zYX) (qU.comp Φ_conn) hker).comp
    (LinearMap.quotKerEquivOfSurjective zYX zYX_surj).symm.toLinearMap
lemma Os_zYX : Os.comp zYX = qU.comp Φ_conn := by
  apply LinearMap.ext; intro y
  unfold Os
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  have hinv : (LinearMap.quotKerEquivOfSurjective zYX zYX_surj).symm (zYX y) = Submodule.Quotient.mk y := by
    apply (LinearMap.quotKerEquivOfSurjective zYX zYX_surj).injective; simp
  rw [hinv,Submodule.liftQ_apply]; rfl
def u2U : UMod :=
  ⟨equivPU.symm (z45 alphaBv,z45 qBv),by
    simp only [UMod_sub,Submodule.mem_mk,AddSubmonoid.mem_mk,AddSubsemigroup.mem_mk,
      Set.mem_ofPred_eq,LinearEquiv.apply_symm_apply]
    constructor
    · rw [z169]; dsimp only; rw [z208]
    · rw [z182,z110]; dsimp only; rw [z98,z105]⟩
lemma z327 :
    equivPU (jU (z11 • u2U)) = (z45 z161,0) := by
  rw [jU.map_smul,equivPU.map_smul]
  change (z11 • (z45 alphaBv : Pv 3),z11 • (z45 qBv : Pv 1)) = _
  apply Prod.ext
  · apply xP; ext c
    change (z12 iotaB • z45 alphaBv).val c = (z45 z161).val c
    rw [z27]; dsimp only; rw [z84]; dsimp only; rw [dif_pos (socB_src 3)]
  · apply xP; ext c
    change (z12 iotaB • z45 qBv).val c = 0
    rw [z27]; dsimp only; rw [z163]; rfl
lemma z356 :
    allB.all (fun c => if c.src == 1 && c.tgt == 3 then (c == qB || c == socB 1) else true) = true := by decide
lemma z297 {a : Pv 3} (he3 : eΛ 3 • a = a) (hi : z11 • a = 0) : a = 0 := by
  apply xP; ext c
  have hc_tgt : a.val c = if c.1.tgt = 3 then a.val c else 0 := by
    have := congrArg (fun x : Pv 3 => x.val c) he3.symm
    rwa [z59] at this
  by_cases htgt : c.1.tgt = 3
  · have hchk := List.all_eq_true.mp z290 c.1 (z35 c.1)
    simp only [c.2,htgt,beq_self_eq_true,Bool.and_self,↓reduceIte,Bool.or_eq_true,
      beq_iff_eq] at hchk
    rcases hchk with h1 | h2
    · have hc' : c = ⟨eB 3,rfl⟩ := Subtype.ext h1; subst hc'
      have h0 : (z11 • a).val iotaBv = 0 := by rw [hi]; rfl
      rw [z11,z40,sum_eq_single ⟨eB 3,rfl⟩] at h0
      · have hm : mulB iotaB (eB 3) = some iotaB := by decide
        dsimp only at h0; simpa [hm] using h0
      · intro y _ hy; rw [if_neg]; intro hmy
        have hdec := z64
          (fun z => !(z.src == 3 && mulB iotaB z == some iotaB) || z == eB 3) (by decide) y.1
        simp only [y.2,hmy,beq_self_eq_true,Bool.and_self,Bool.not_true,Bool.false_or,beq_iff_eq] at hdec
        exact hy (Subtype.ext hdec)
      · intro hn; exact absurd (mem_univ _) hn
    · have hc' : c = alphaBv := Subtype.ext h2; subst hc'
      have h0 : (z11 • a).val z161 = 0 := by rw [hi]; rfl
      rw [z11,z40,sum_eq_single alphaBv] at h0
      · dsimp only at h0; simpa [z84] using h0
      · intro y _ hy; rw [if_neg]; intro hmy
        have hdec := z64
          (fun z => !(z.src == 3 && mulB iotaB z == some (socB 3)) || z == alphaB) (by decide) y.1
        simp only [y.2,hmy,beq_self_eq_true,Bool.and_self,Bool.not_true,Bool.false_or,beq_iff_eq] at hdec
        exact hy (Subtype.ext hdec)
      · intro hn; exact absurd (mem_univ _) hn
  · rw [if_neg htgt] at hc_tgt; exact hc_tgt
lemma z265 {b : Pv 1} (he3 : eΛ 3 • b = b) (ha : rmul_alphap b = 0) :
    z108 • b = 0 := by
  have hb_only : ∀ y : Bv 1,y ≠ z323 → b.val y = 0 := by
    intro y hy
    have hy_tgt : b.val y = if y.1.tgt = 3 then b.val y else 0 := by
      have := congrArg (fun x : Pv 1 => x.val y) he3.symm
      rwa [z59] at this
    by_cases htgt : y.1.tgt = 3
    · have hchk := List.all_eq_true.mp z356 y.1 (z35 y.1)
      simp only [y.2,htgt,beq_self_eq_true,Bool.and_self,↓reduceIte,Bool.or_eq_true,
        beq_iff_eq] at hchk
      rcases hchk with h1 | h2
      · have hy' : y = qBv := Subtype.ext h1; subst hy'
        have h0 : (rmul_alphap b).val z323 = 0 := by rw [ha]; rfl
        rw [z129,sum_eq_single qBv] at h0
        · dsimp only at h0; simpa [z105] using h0
        · intro z _ hz; rw [if_neg]; intro hmz
          have hdec := z64
            (fun w => !(w.src == 1 && mulB w alphapB == some (socB 1)) || w == qB) (by decide) z.1
          simp only [z.2,hmz,beq_self_eq_true,Bool.and_self,Bool.not_true,Bool.false_or,beq_iff_eq] at hdec
          exact hz (Subtype.ext hdec)
        · intro hn; exact absurd (mem_univ _) hn
      · exact absurd (Subtype.ext h2) hy
    · rw [if_neg htgt] at hy_tgt; exact hy_tgt
  apply xP; ext c
  rw [z108,z40,Pv.zero_val]
  refine sum_eq_zero fun y _ => ?_
  by_cases hy : y = z323
  · subst hy; dsimp only
    have hnone : mulB alphaB (socB 1) = none := by decide
    simp [hnone]
  · rw [hb_only y hy,ite_self]
lemma z87 {u : UMod} (he3 : eΛ 3 • u = u) (hi : z11 • u = 0) :
    z108 • u = 0 := by
  have he3_pair : eΛ 3 • (equivPU (jU u)).1 = (equivPU (jU u)).1 ∧
      eΛ 3 • (equivPU (jU u)).2 = (equivPU (jU u)).2 := by
    have h := congrArg (fun z => equivPU (jU z)) he3
    rw [jU.map_smul,equivPU.map_smul] at h
    exact ⟨(Prod.smul_fst _ _).symm.trans (congrArg Prod.fst h),
      (Prod.smul_snd _ _).symm.trans (congrArg Prod.snd h)⟩
  have hi_pair : z11 • (equivPU (jU u)).1 = 0 := by
    have h := congrArg (fun z => (equivPU (jU z)).1) hi
    rw [jU.map_smul,equivPU.map_smul,Prod.smul_fst] at h
    exact h
  have ha0 : (equivPU (jU u)).1 = 0 := z297 he3_pair.1 hi_pair
  have hrmul : rmul_alphap (equivPU (jU u)).2 = 0 := by
    change rmul_alphap (equivPU u.1).2 = 0
    rw [← u.2.2]
    exact (congrArg rmul_q ha0).trans (map_zero rmul_q)
  have hb0 : z108 • (equivPU (jU u)).2 = 0 := z265 he3_pair.2 hrmul
  apply jU_inj; apply equivPU.injective
  rw [jU.map_smul,equivPU.map_smul,map_zero,map_zero]
  exact Prod.ext (by rw [Prod.smul_fst,ha0,smul_zero]; rfl) (by rw [Prod.smul_snd,hb0]; rfl)
lemma z138 (u : UMod) (he1 : eΛ 1 • u = u) :
    ∃ r : ZMod 2,z15 • u = z11 • z16 r u2U := by
  have hb_xp : (equivPU (jU u)).2 ∈ LinearMap.ker rmul_iota := u.2.1
  have hb0 : (equivPU (jU u)).2 = 0 := by
    have h1 : eΛ 1 • (⟨(equivPU (jU u)).2,hb_xp⟩ : XpMod) = ⟨(equivPU (jU u)).2,hb_xp⟩ := by
      apply Subtype.ext
      have h := congrArg (fun z => (equivPU (jU z)).2) he1
      rw [jU.map_smul,equivPU.map_smul,Prod.smul_snd] at h
      exact h
    rw [z214] at h1
    exact (congrArg Subtype.val h1).symm
  have ha_e1 : eΛ 1 • (equivPU (jU u)).1 = (equivPU (jU u)).1 := by
    have h := congrArg (fun z => (equivPU (jU z)).1) he1
    rw [jU.map_smul,equivPU.map_smul,Prod.smul_fst] at h
    exact h
  let r : ZMod 2 := (equivPU (jU u)).1.val iotaBv
  refine ⟨r,?_⟩
  apply jU_inj; apply equivPU.injective
  have hrhs : equivPU (jU (z11 • z16 r u2U)) = (z16 r (z45 z161),0) := by
    rw [z125,z53 jU]
    change equivPU.toLinearMap (z16 r (jU (z11 • u2U))) = _
    rw [z53 equivPU.toLinearMap]
    change z16 r (equivPU (jU (z11 • u2U))) = _
    rw [z327]
    rcases z33 r with hr | hr
    · simp [z16,hr]; rfl
    · simp [z16,hr]
  rw [jU.map_smul,equivPU.map_smul,hrhs]
  apply Prod.ext
  · rw [Prod.smul_fst]
    apply xP; ext c
    rw [z15,z40,Pv.z2smul_val,basisPv_val]
    have ha_only : ∀ y : Bv 3,y ≠ iotaBv → y ≠ z161 → (equivPU (jU u)).1.val y = 0 := by
      intro y hy1 hy2
      have hyt : (equivPU (jU u)).1.val y = if y.1.tgt = 1 then (equivPU (jU u)).1.val y else 0 := by
        have := congrArg (fun x : Pv 3 => x.val y) ha_e1.symm
        rwa [z59] at this
      by_cases ht : y.1.tgt = 1
      · have hchk := List.all_eq_true.mp z291 y.1 (z35 y.1)
        simp only [y.2,ht,beq_self_eq_true,Bool.and_self,↓reduceIte,Bool.or_eq_true,
          beq_iff_eq] at hchk
        rcases hchk with h1 | h2
        · exact absurd (Subtype.ext h1) hy1
        · exact absurd (Subtype.ext h2) hy2
      · rw [if_neg ht] at hyt; exact hyt
    by_cases hc : c = z161
    · subst hc; rw [if_pos rfl,mul_one,sum_eq_single iotaBv]
      · dsimp only; rw [if_pos z76]
      · intro y _ hy
        by_cases hy2 : y = z161
        · subst hy2; dsimp only
          have hnone : mulB alphapB (socB 3) = none := by decide
          simp [hnone]
        · rw [ha_only y hy hy2,ite_self]
      · intro hn; exact absurd (mem_univ _) hn
    · rw [if_neg hc,mul_zero]
      refine sum_eq_zero fun y _ => ?_
      by_cases hy1 : y = iotaBv
      · subst hy1; dsimp only; rw [z76,if_neg (fun hh => hc (Subtype.ext (Option.some.inj hh).symm))]
      · by_cases hy2 : y = z161
        · subst hy2; dsimp only
          have hnone : mulB alphapB (socB 3) = none := by decide
          simp [hnone]
        · rw [ha_only y hy1 hy2,ite_self]
  · rw [Prod.smul_snd,hb0,smul_zero]
lemma z144 {u : UMod} {p1 : Pv 1}
    (he1u : eΛ 1 • u = u) (he1p : eΛ 1 • p1 = p1) (hq : z115 • mkY (u,p1) = 0) :
    z15 • p1 = 0 := by
  have hmem : (z115 • u,z115 • p1) ∈ KY_sub := (Submodule.Quotient.mk_eq_zero KY_sub).mp hq
  obtain ⟨x',hx'⟩ := hmem
  have h1 : sXpU x' = z115 • u := congrArg Prod.fst hx'
  have h2 : x'.1 = z115 • p1 := congrArg Prod.snd hx'
  have hb0 : (equivPU (jU u)).2 = 0 := by
    have h1' : eΛ 1 • (⟨(equivPU (jU u)).2,u.2.1⟩ : XpMod) = ⟨(equivPU (jU u)).2,u.2.1⟩ := by
      apply Subtype.ext
      have h := congrArg (fun z => (equivPU (jU z)).2) he1u
      rw [jU.map_smul,equivPU.map_smul,Prod.smul_snd] at h
      exact h
    rw [z214] at h1'
    exact (congrArg Subtype.val h1').symm
  have hrmul0 : rmul_alphap (z115 • p1) = 0 := by
    have hsnd := congrArg (fun z => (equivPU (jU z)).2) h1
    rw [jU.map_smul,equivPU.map_smul,Prod.smul_snd] at hsnd
    change rmul_alphap x'.1 = z115 • (equivPU (jU u)).2 at hsnd
    rw [h2,hb0,smul_zero] at hsnd
    exact hsnd
  have hp1_e1_val0 : p1.val ⟨eB 1,rfl⟩ = 0 := by
    have h0 : (rmul_alphap (z115 • p1)).val z323 = 0 := by rw [hrmul0]; rfl
    rw [z129,sum_eq_single qBv] at h0
    · dsimp only at h0
      rw [if_pos z105,z115,z40,sum_eq_single ⟨eB 1,rfl⟩] at h0
      · have hm : mulB qB (eB 1) = some qB := by decide
        simpa [hm] using h0
      · intro y _ hy; rw [if_neg]; intro hmy
        have hdec := z64
          (fun z => !(z.src == 1 && mulB qB z == some qB) || z == eB 1) (by decide) y.1
        simp only [y.2,hmy,beq_self_eq_true,Bool.and_self,Bool.not_true,Bool.false_or,beq_iff_eq] at hdec
        exact hy (Subtype.ext hdec)
      · intro hn; exact absurd (mem_univ _) hn
    · intro y _ hy; rw [if_neg]; intro hmy
      have hdec := z64
        (fun z => !(z.src == 1 && mulB z alphapB == some (socB 1)) || z == qB) (by decide) y.1
      simp only [y.2,hmy,beq_self_eq_true,Bool.and_self,Bool.not_true,Bool.false_or,beq_iff_eq] at hdec
      exact hy (Subtype.ext hdec)
    · intro hn; exact absurd (mem_univ _) hn
  apply xP; ext c
  rw [z15,z40,Pv.zero_val]
  refine sum_eq_zero fun y _ => ?_
  have hyt : p1.val y = if y.1.tgt = 1 then p1.val y else 0 := by
    have := congrArg (fun x : Pv 1 => x.val y) he1p.symm
    rwa [z59] at this
  by_cases ht : y.1.tgt = 1
  · have hchk := List.all_eq_true.mp z292 y.1 (z35 y.1)
    simp only [y.2,ht,beq_self_eq_true,Bool.and_self,↓reduceIte,Bool.or_eq_true,
      beq_iff_eq] at hchk
    rcases hchk with h1' | h2'
    · have hy' : y = ⟨eB 1,rfl⟩ := Subtype.ext h1'; subst hy'
      rw [hp1_e1_val0,ite_self]
    · have hy' : y = alphapBv := Subtype.ext h2'; subst hy'; dsimp only
      rw [z152]; simp
  · rw [if_neg ht] at hyt; rw [hyt,ite_self]
lemma z100 {M : Type} [AddCommGroup M] [Module Λ M]
    (g : XMod →ₗ[Λ] M) (n : M) (hn : z15 • g gX = z11 • n) :
    StableEq (g.comp αX) 0 := by
  let n3 := eΛ 3 • n
  have hn3 : eΛ 3 • n3 = n3 := by rw [← mul_smul,z44]
  let h3 : Pv 3 →ₗ[Λ] M := (z29 3).symm ⟨n3,hn3⟩
  apply z70 3 inclX h3
  have hdiff : (g.comp αX - h3.comp inclX) gX = 0 := by
    rw [LinearMap.sub_apply,sub_eq_zero,LinearMap.comp_apply,LinearMap.comp_apply]
    have hgX : inclX gX = z11 • genPv 3 := by
      change gX.1 = z12 iotaB • genPv 3; rw [z259,← z24 iotaBv]
    rw [hgX,h3.map_smul]
    have hh3 : h3 (genPv 3) = n3 := congrArg Subtype.val ((z29 3).apply_symm_apply ⟨n3,hn3⟩)
    rw [hh3,← mul_smul]
    have hi3 : z11 * eΛ 3 = z11 := by rw [z11,z137,iotaB_src,if_pos rfl]
    rw [hi3,← hn,← g.map_smul,z166]
  exact sub_eq_zero.mp (z52 _ hdiff)
lemma z167 : z108 • gXp = αXp gXp := by
  apply Subtype.ext
  change z12 alphaB • gXp.1 = (αXp gXp).1
  rw [z270,z256,z27]; dsimp only
  rw [z98]; dsimp only; rw [dif_pos (socB_src 1)]
lemma z177 : z11 • gXp = 0 := by
  apply Subtype.ext
  change z12 iotaB • gXp.1 = 0
  rw [z270,z27]; dsimp only; rw [z163]
lemma eta_U_zero : StableEq (concreteExactSys.η UMod) 0 := by
  change StableEq (ηGem gemX UMod + ηGem gemXp UMod) 0
  rw [← add_zero (0 : UMod →ₗ[Λ] UMod)]
  refine StableEq.add (z102 gemX UMod fun g => ?_) (z102 gemXp UMod fun g => ?_)
  · have he1 : eΛ 1 • g gX = g gX := by rw [← g.map_smul,z178]
    obtain ⟨r,hr⟩ := z138 (g gX) he1
    exact z100 g (z16 r u2U) hr
  · have he3 : eΛ 3 • g gXp = g gXp := by rw [← g.map_smul,z189]
    have hi : z11 • g gXp = 0 := by rw [← g.map_smul,z177,map_zero]
    have h0 : g.comp αXp = 0 := by
      apply z116
      change g (αXp gXp) = 0
      rw [← z167,g.map_smul]
      exact z87 he3 hi
    change StableEq (g.comp αXp) 0
    rw [h0]; exact StableEq.refl 0
lemma eta_Y_zero : StableEq (concreteExactSys.η YMod) 0 := by
  change StableEq (ηGem gemX YMod + ηGem gemXp YMod) 0
  rw [← add_zero (0 : YMod →ₗ[Λ] YMod)]
  refine StableEq.add (z102 gemX YMod fun g => ?_) (z102 gemXp YMod fun g => ?_)
  · obtain ⟨⟨u0,p0⟩,hup⟩ := Submodule.Quotient.mk_surjective KY_sub (g gX)
    let u := eΛ 1 • u0
    let p1 := eΛ 1 • p0
    have he1u : eΛ 1 • u = u := by rw [← mul_smul,z44]
    have he1p : eΛ 1 • p1 = p1 := by rw [← mul_smul,z44]
    have hgg : g gX = mkY (u,p1) := by
      rw [← z178,g.map_smul,← hup]
      change eΛ 1 • mkY (u0,p0) = mkY (eΛ 1 • u0,eΛ 1 • p0)
      rw [← mkY.map_smul]
      exact congrArg mkY (Prod.smul_mk _ _ _)
    have hq : z115 • mkY (u,p1) = 0 := by
      rw [← hgg,← g.map_smul,z245,map_zero]
    have hp1_0 : z15 • p1 = 0 := z144 he1u he1p hq
    obtain ⟨r,hr⟩ := z138 u he1u
    refine z100 g (wUY (z16 r u2U)) ?_
    rw [hgg,← mkY.map_smul]
    change mkY (z15 • (u,p1)) = z11 • mkY (z16 r u2U,0)
    rw [Prod.smul_mk,hr,hp1_0,← mkY.map_smul,Prod.smul_mk]
    exact congrArg mkY (Prod.ext rfl (smul_zero _).symm)
  · have hz0 : zYX (g gXp) = 0 := by
      have he3 : eΛ 3 • zYX (g gXp) = zYX (g gXp) := by
        rw [← zYX.map_smul,← g.map_smul,z189]
      rw [z160] at he3
      exact he3.symm
    have hmem : g gXp ∈ LinearMap.range wUY := by rw [exact_wUY_zYX]; exact hz0
    obtain ⟨u0,hu0⟩ := hmem
    let u := eΛ 3 • u0
    have he3u : eΛ 3 • u = u := by rw [← mul_smul,z44]
    have hwu : wUY u = g gXp := by rw [wUY.map_smul,hu0,← g.map_smul,z189]
    have hiu : z11 • u = 0 := wUY_inj (by
      rw [wUY.map_smul,hwu,← g.map_smul,z177,map_zero,map_zero])
    have hau : z108 • u = 0 := z87 he3u hiu
    have h0 : g.comp αXp = 0 := by
      apply z116
      change g (αXp gXp) = 0
      rw [← z167,g.map_smul,← hwu,← wUY.map_smul,hau,map_zero]
    change StableEq (g.comp αXp) 0
    rw [h0]; exact StableEq.refl 0
lemma eta_X_not_stable_zero : ¬ StableEq (0 : XMod →ₗ[Λ] XMod) (concreteExactSys.η XMod) := by
  intro h
  have hxp : StableEq (ηGem gemXp XMod) 0 :=
    z102 gemXp XMod fun g => by rw [z269 g,LinearMap.zero_comp]; exact StableEq.refl 0
  have hx : StableEq (ηGem gemX XMod) αX := ηGem_self gemX
  have hsum : StableEq (concreteExactSys.η XMod) αX := by
    change StableEq (ηGem gemX XMod + ηGem gemXp XMod) αX
    rw [← add_zero αX]
    exact StableEq.add hx hxp
  have h0α : StableEq αX 0 := (h.trans hsum).symm
  exact z282 (z157 h0α)
def g3OU : OUMod := qU (equivPU.symm (genPv 3,0))
def g1OU : OUMod := qU (equivPU.symm (0,genPv 1))
lemma Φ_conn_mkY (u : UMod) (p1 : Pv 1) :
    Φ_conn (mkY (u,p1)) = jU u + equivPU.symm (0,rmul_alphap p1) := rfl
lemma zYX_mkY (u : UMod) (p1 : Pv 1) : zYX (mkY (u,p1)) = projToX p1 := rfl
lemma z331 : eΛ 3 • g3OU = g3OU := by
  unfold g3OU
  rw [← qU.map_smul,← equivPU.symm.map_smul,Prod.smul_mk,z79,smul_zero]
lemma z332 : eΛ 1 • g1OU = g1OU := by
  unfold g1OU
  rw [← qU.map_smul,← equivPU.symm.map_smul,Prod.smul_mk,smul_zero,z79]
lemma Os_gX_eq : Os gX = z15 • g1OU := by
  have hzx : gX = zYX (mkY (0,genPv 1)) := (zYX_mkY 0 (genPv 1)).symm
  rw [hzx]
  have hcomm := congrArg (fun (k : YMod →ₗ[Λ] OUMod) => k (mkY (0,genPv 1))) Os_zYX
  simp only [LinearMap.comp_apply] at hcomm
  rw [hcomm,Φ_conn_mkY,map_zero,zero_add]
  unfold g1OU
  rw [← qU.map_smul,← equivPU.symm.map_smul,Prod.smul_mk,smul_zero,
    z130,z15,← z24 alphapBv]
lemma z311 : z11 • g3OU = 0 := by
  unfold g3OU
  rw [← qU.map_smul,← equivPU.symm.map_smul,Prod.smul_mk,smul_zero]
  apply (Submodule.Quotient.mk_eq_zero UMod_sub).mpr
  simp only [UMod_sub,Submodule.mem_mk,AddSubmonoid.mem_mk,AddSubsemigroup.mem_mk,
    Set.mem_ofPred_eq,LinearEquiv.apply_symm_apply,map_zero,true_and]
  rw [z11,z24 iotaBv,z182]; dsimp only; rw [z163]
lemma z305 : z108 • g3OU + z115 • g1OU = 0 := by
  unfold g3OU g1OU
  rw [← qU.map_smul,← qU.map_smul,← qU.map_add,← equivPU.symm.map_smul,
    ← equivPU.symm.map_smul,← equivPU.symm.map_add]
  have hu2eq : equivPU.symm (z108 • (genPv 3,(0 : Pv 1)) + z115 • ((0 : Pv 3),genPv 1)) = jU u2U := by
    apply equivPU.injective
    rw [equivPU.apply_symm_apply,Prod.smul_mk,Prod.smul_mk,smul_zero,smul_zero,
      Prod.mk_add_mk,add_zero,zero_add]
    change (z12 alphaB • genPv 3,z12 qB • genPv 1) = (z45 alphaBv,z45 qBv)
    exact Prod.ext (z24 alphaBv) (z24 qBv)
  rw [hu2eq]
  have hmem : jU u2U ∈ LinearMap.ker qU := by rw [← exact_jU_qU]; exact ⟨u2U,rfl⟩
  exact hmem
lemma no_lightning_flash : ∀ (φ : OUMod →ₗ[Λ] YMod),zYX.comp (φ.comp Os) = 0 := by
  intro φ
  apply z52
  change zYX (φ (Os gX)) = 0
  let y3 := φ g3OU
  let y1 := φ g1OU
  have he3_y3 : eΛ 3 • y3 = y3 := by rw [← φ.map_smul,z331]
  have he1_y1 : eΛ 1 • y1 = y1 := by rw [← φ.map_smul,z332]
  have hi_y3 : z11 • y3 = 0 := by rw [← φ.map_smul,z311,map_zero]
  have hrel2_y : z108 • y3 + z115 • y1 = 0 := by
    rw [← φ.map_smul,← φ.map_smul,← φ.map_add,z305,map_zero]
  have hz3 : zYX y3 = 0 := by
    have h := congrArg zYX he3_y3
    rw [zYX.map_smul,z160] at h
    exact h.symm
  have hy3_mem : y3 ∈ LinearMap.range wUY := by rw [exact_wUY_zYX]; exact hz3
  obtain ⟨u3_0,hu3_0⟩ := hy3_mem
  let u3 := eΛ 3 • u3_0
  have he3_u3 : eΛ 3 • u3 = u3 := by rw [← mul_smul,z44]
  have hwu3 : wUY u3 = y3 := by rw [wUY.map_smul,hu3_0,he3_y3]
  have hi_u3 : z11 • u3 = 0 := wUY_inj (by rw [wUY.map_smul,hwu3,hi_y3,map_zero])
  have ha_y3 : z108 • y3 = 0 := by
    rw [← hwu3,← wUY.map_smul,z87 he3_u3 hi_u3,map_zero]
  have hq_y1 : z115 • y1 = 0 := by
    rw [ha_y3,zero_add] at hrel2_y
    exact hrel2_y
  obtain ⟨⟨u1_0,p1_0⟩,hup1⟩ := Submodule.Quotient.mk_surjective KY_sub y1
  let u1 := eΛ 1 • u1_0
  let p1 := eΛ 1 • p1_0
  have he1_u1 : eΛ 1 • u1 = u1 := by rw [← mul_smul,z44]
  have he1_p1 : eΛ 1 • p1 = p1 := by rw [← mul_smul,z44]
  have hy1_eq : y1 = mkY (u1,p1) := by
    rw [← he1_y1,← hup1]
    change eΛ 1 • mkY (u1_0,p1_0) = mkY (eΛ 1 • u1_0,eΛ 1 • p1_0)
    rw [← mkY.map_smul]
    exact congrArg mkY (Prod.smul_mk _ _ _)
  rw [hy1_eq] at hq_y1
  have hap1 : z15 • p1 = 0 := z144 he1_u1 he1_p1 hq_y1
  rw [Os_gX_eq,φ.map_smul,zYX.map_smul]
  change z15 • zYX y1 = 0
  rw [hy1_eq,zYX_mkY,← projToX.map_smul,hap1,map_zero]
noncomputable section
section Mod2Helpers
lemma z99 {M N : Type*} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] (f : M →ₗ[Λ] N) : f + f = 0 := by
  ext x; exact z10 (f x)
lemma z287 {M N : Type*} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] (f : M →ₗ[Λ] N) : -f = f :=
  (eq_neg_of_add_eq_zero_left (z99 f)).symm
lemma z154 {M N : Type*} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] (f g : M →ₗ[Λ] N) : f - g = f + g := by
  rw [sub_eq_add_neg,z287]
lemma FP.sub_eq_add {X Y : FP} (f g : X ⟶ Y) : f - g = f + g := by
  rw [sub_eq_add_neg,FP.neg_eq]
lemma FP.isZero_mod_eq_zero {Z : FP} (hZ : Limits.IsZero Z) (z : Z.Mod) : z = 0 := by
  have hid : (𝟙 Z : Z ⟶ Z) = 0 := hZ.eq_of_src (𝟙 Z) 0
  have h1 := congrArg (fun (m : Z ⟶ Z) => m.hom z) hid
  simpa using h1
lemma z207 (M : Type) [AddCommGroup M] [Module Λ M] :
    nuMap (LinearMap.id : M →ₗ[Λ] M) = LinearMap.id := by
  ext x; rfl
lemma z83 {M N P : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] [AddCommGroup P] [Module Λ P]
    (g : N →ₗ[Λ] P) (f : M →ₗ[Λ] N) :
    nuMap (g.comp f) = (nuMap g).comp (nuMap f) := by
  ext x; rfl
lemma z359 {M N : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] (f g : M →ₗ[Λ] N) :
    nuMap (f + g) = nuMap f + nuMap g := by
  ext x; rfl
lemma nuMap_sub {M N : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] (f g : M →ₗ[Λ] N) :
    nuMap (f - g) = nuMap f - nuMap g := by
  ext x; rfl
lemma nuMap_zero {M N : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] :
    nuMap (0 : M →ₗ[Λ] N) = 0 := by
  ext x; rfl
lemma z61 {M N : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] {f : M →ₗ[Λ] N} (hf : Function.Injective f) :
    Function.Injective (nuMap f) := by
  intro x y h
  apply nuMod.ext
  exact hf (congrArg nuMod.val h)
lemma z286 {M N : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] {f : M →ₗ[Λ] N} (hf : Function.Surjective f) :
    Function.Surjective (nuMap f) := by
  intro y
  obtain ⟨x,hx⟩ := hf y.val
  exact ⟨⟨x⟩,nuMod.ext hx⟩
def z203 {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (f : nuMod M →ₗ[Λ] nuMod N) : M →ₗ[Λ] N :=
  (nuModInvol.toLinearMap.comp (nuMap f)).comp nuModInvol.symm.toLinearMap
lemma z268 {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (f : nuMod M →ₗ[Λ] nuMod N) : nuMap (z203 f) = f := by
  ext x; rfl
lemma unNuMap_nuMap {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (f : M →ₗ[Λ] N) : z203 (nuMap f) = f := by
  ext x; rfl
lemma unNuMap_apply {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (f : nuMod M →ₗ[Λ] nuMod N) (x : M) : z203 f x = (f ⟨x⟩).val := rfl
lemma unNuMap_sub {M N : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (f g : nuMod M →ₗ[Λ] nuMod N) : z203 (f - g) = z203 f - z203 g := by
  ext x; rfl
lemma unNuMap_id (M : Type) [AddCommGroup M] [Module Λ M] :
    z203 (LinearMap.id : nuMod M →ₗ[Λ] nuMod M) = LinearMap.id := by
  ext x; rfl
lemma z7 {M N P : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] [AddCommGroup P] [Module Λ P]
    (f : M →ₗ[Λ] N) (g : N →ₗ[Λ] P) :
    ExactAt f g ↔ ∀ y,g y = 0 ↔ ∃ x,f x = y := by
  constructor
  · intro h y
    have hy := SetLike.ext_iff.mp h y
    simpa [LinearMap.mem_range,LinearMap.mem_ker] using hy.symm
  · intro h
    ext y
    simpa [LinearMap.mem_range,LinearMap.mem_ker] using (h y).symm
lemma ExactAt.comp_eq_zero {M N P : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] [AddCommGroup P] [Module Λ P]
    {f : M →ₗ[Λ] N} {g : N →ₗ[Λ] P} (h : ExactAt f g) : g.comp f = 0 := by
  ext x
  exact ((z7 f g).mp h (f x)).mpr ⟨x,rfl⟩
lemma ExactAt.nuMap {M N P : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] [AddCommGroup P] [Module Λ P]
    {f : M →ₗ[Λ] N} {g : N →ₗ[Λ] P} (h : ExactAt f g) :
    ExactAt (MO31809.nuMap f) (MO31809.nuMap g) := by
  rw [z7] at h ⊢
  intro y
  constructor
  · intro hy
    obtain ⟨x,hx⟩ := (h y.val).mp (congrArg nuMod.val hy)
    exact ⟨⟨x⟩,nuMod.ext hx⟩
  · rintro ⟨x,rfl⟩
    apply nuMod.ext
    exact (h (f x.val)).mpr ⟨x.val,rfl⟩
lemma ExactAt.of_comp_inj {M N P Q : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] [AddCommGroup P] [Module Λ P] [AddCommGroup Q] [Module Λ Q]
    {f : M →ₗ[Λ] N} {g : N →ₗ[Λ] P} {k : P →ₗ[Λ] Q}
    (h : ExactAt f g) (hk : Function.Injective k) : ExactAt f (k.comp g) := by
  rw [z7] at h ⊢
  intro y
  rw [LinearMap.comp_apply,(map_eq_zero_iff k hk),h]
lemma ExactAt.of_comp_surj {A M N P : Type} [AddCommGroup A] [Module Λ A]
    [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N] [AddCommGroup P] [Module Λ P]
    {k : A →ₗ[Λ] M} {f : M →ₗ[Λ] N} {g : N →ₗ[Λ] P}
    (h : ExactAt f g) (hk : Function.Surjective k) : ExactAt (f.comp k) g := by
  rw [z7] at h ⊢
  intro y
  rw [h]
  constructor
  · rintro ⟨m,rfl⟩
    obtain ⟨a,rfl⟩ := hk m
    exact ⟨a,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨k a,rfl⟩
lemma ExactAt.of_equiv_mid {M N N' P : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] [AddCommGroup N'] [Module Λ N'] [AddCommGroup P] [Module Λ P]
    {f : M →ₗ[Λ] N} {g : N →ₗ[Λ] P} (h : ExactAt f g) (e : N ≃ₗ[Λ] N') :
    ExactAt (e.toLinearMap.comp f) (g.comp e.symm.toLinearMap) := by
  rw [z7] at h ⊢
  intro y
  rw [LinearMap.comp_apply,LinearEquiv.coe_coe,h]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x,by simp [hx]⟩
  · rintro ⟨x,hx⟩
    exact ⟨x,by simpa using congrArg e.symm hx⟩
lemma z21 {M N P Q : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] [AddCommGroup P] [Module Λ P] [AddCommGroup Q] [Module Λ Q]
    {f : M →ₗ[Λ] N} {g : N →ₗ[Λ] P}
    (hfg : ExactAt f g) (hg : Function.Surjective g)
    (k : N →ₗ[Λ] Q) (hk : k.comp f = 0) :
    ∃ c : P →ₗ[Λ] Q,c.comp g = k := by
  have hker : LinearMap.ker g ≤ LinearMap.ker k := by
    intro y hy
    have hy' : y ∈ LinearMap.range f := by rw [hfg]; exact hy
    obtain ⟨x,rfl⟩ := hy'
    change k (f x) = 0
    exact congrArg (fun m => m x) hk
  let kq : (N ⧸ LinearMap.ker g) →ₗ[Λ] Q := Submodule.liftQ (LinearMap.ker g) k hker
  let e : (N ⧸ LinearMap.ker g) ≃ₗ[Λ] P := g.quotKerEquivOfSurjective hg
  refine ⟨kq.comp e.symm.toLinearMap,?_⟩
  ext y
  have he : e (Submodule.Quotient.mk y) = g y := rfl
  change kq (e.symm (g y)) = k y
  rw [← he,e.symm_apply_apply]
  rfl
lemma z32 (S : ExactSys) {M N P : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] [AddCommGroup P] [Module Λ P]
    {f : M →ₗ[Λ] N} {g : N →ₗ[Λ] P} (hfg : ExactAt f g)
    (Q : FP) (k : N →ₗ[Λ] Q.Mod) (hk : k.comp f = 0) :
    ∃ h : P →ₗ[Λ] Q.Mod,h.comp g = k := by
  have hfg' : ExactAt f g.rangeRestrict := by
    rw [z7] at hfg ⊢
    intro y
    constructor
    · intro hy
      exact (hfg y).mp (congrArg Subtype.val hy)
    · intro hy
      exact Subtype.ext ((hfg y).mpr hy)
  obtain ⟨kbar,hkbar⟩ := z21 hfg' g.surjective_rangeRestrict k hk
  obtain ⟨h,hh⟩ := S.inj Q (LinearMap.range g).subtype Subtype.val_injective kbar
  refine ⟨h,LinearMap.ext fun y => ?_⟩
  have h1 : (h.comp g) y = h ((LinearMap.range g).subtype (g.rangeRestrict y)) := rfl
  rw [h1]
  have h2 := congrArg (fun m => m (g.rangeRestrict y)) hh
  have h3 := congrArg (fun m => m y) hkbar
  exact h2.trans h3
lemma lift_of_exact_proj (S : ExactSys) {M N P : Type} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] [AddCommGroup P] [Module Λ P]
    {f : M →ₗ[Λ] N} {g : N →ₗ[Λ] P} (hfg : ExactAt f g)
    (P0 : FP) (k : P0.Mod →ₗ[Λ] N) (hk : g.comp k = 0) :
    ∃ h : P0.Mod →ₗ[Λ] M,f.comp h = k := by
  have hmem : ∀ x,k x ∈ LinearMap.range f := by
    intro x
    rw [hfg]
    exact congrArg (fun m => m x) hk
  let k' : P0.Mod →ₗ[Λ] LinearMap.range f := k.codRestrict (LinearMap.range f) hmem
  obtain ⟨h,hh⟩ := S.proj P0 f.rangeRestrict f.surjective_rangeRestrict k'
  refine ⟨h,LinearMap.ext fun x => ?_⟩
  exact congrArg Subtype.val (congrArg (fun m => m x) hh)
lemma z111 {A M N P : Type} [AddCommGroup A] [Module Λ A]
    [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N] [AddCommGroup P] [Module Λ P]
    {i : M →ₗ[Λ] N} {q : N →ₗ[Λ] P} (hi : Function.Injective i) (hiq : ExactAt i q)
    (k : A →ₗ[Λ] N) (hk : q.comp k = 0) :
    ∃ h : A →ₗ[Λ] M,i.comp h = k := by
  have hmem : ∀ a,k a ∈ LinearMap.range i := by
    intro a
    rw [hiq]
    exact congrArg (fun m => m a) hk
  let e : M ≃ₗ[Λ] LinearMap.range i := LinearEquiv.ofInjective i hi
  let k' : A →ₗ[Λ] LinearMap.range i := k.codRestrict (LinearMap.range i) hmem
  refine ⟨e.symm.toLinearMap.comp k',LinearMap.ext fun a => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply (k' a))
def FP.desc {A B C : FP} (f : A ⟶ C) (g : B ⟶ C) : FP.sum A B ⟶ C :=
  comp (FP.fst A B) f + comp (FP.snd A B) g
def FP.lift {A B C : FP} (f : C ⟶ A) (g : C ⟶ B) : C ⟶ FP.sum A B :=
  comp f (FP.inl A B) + comp g (FP.inr A B)
def FP.mat {A B C D : FP}
    (f11 : A ⟶ C) (f12 : B ⟶ C) (f21 : A ⟶ D) (f22 : B ⟶ D) :
    FP.sum A B ⟶ FP.sum C D :=
  FP.desc (FP.lift f11 f21) (FP.lift f12 f22)
lemma FP.inl_desc {A B C : FP} (f : A ⟶ C) (g : B ⟶ C) :
    comp (FP.inl A B) (FP.desc f g) = f := by
  dsimp [FP.desc]
  rw [Preadditive.comp_add,← Category.assoc,← Category.assoc,
    FP.inl_fst,FP.inl_snd,Category.id_comp,Limits.zero_comp,add_zero]
lemma FP.inr_desc {A B C : FP} (f : A ⟶ C) (g : B ⟶ C) :
    comp (FP.inr A B) (FP.desc f g) = g := by
  dsimp [FP.desc]
  rw [Preadditive.comp_add,← Category.assoc,← Category.assoc,
    FP.inr_fst,FP.inr_snd,Limits.zero_comp,Category.id_comp,zero_add]
lemma FP.lift_fst {A B C : FP} (f : C ⟶ A) (g : C ⟶ B) :
    comp (FP.lift f g) (FP.fst A B) = f := by
  dsimp [FP.lift]
  rw [Preadditive.add_comp,Category.assoc,Category.assoc,
    FP.inl_fst,FP.inr_fst,Category.comp_id,Limits.comp_zero,add_zero]
lemma FP.lift_snd {A B C : FP} (f : C ⟶ A) (g : C ⟶ B) :
    comp (FP.lift f g) (FP.snd A B) = g := by
  dsimp [FP.lift]
  rw [Preadditive.add_comp,Category.assoc,Category.assoc,
    FP.inl_snd,FP.inr_snd,Limits.comp_zero,Category.comp_id,zero_add]
lemma FP.sum_hom_ext_left {A B C : FP} {h1 h2 : FP.sum A B ⟶ C}
    (hl : comp (FP.inl A B) h1 = comp (FP.inl A B) h2)
    (hr : comp (FP.inr A B) h1 = comp (FP.inr A B) h2) :
    h1 = h2 := by
  calc h1 = comp (𝟙 (FP.sum A B)) h1 := (Category.id_comp h1).symm
    _ = comp (comp (FP.fst A B) (FP.inl A B) +
          comp (FP.snd A B) (FP.inr A B)) h1 := by rw [FP.total_sum]
    _ = comp (FP.fst A B) (comp (FP.inl A B) h1) +
          comp (FP.snd A B) (comp (FP.inr A B) h1) := by
          rw [Preadditive.add_comp,Category.assoc,Category.assoc]
    _ = comp (FP.fst A B) (comp (FP.inl A B) h2) +
          comp (FP.snd A B) (comp (FP.inr A B) h2) := by
          rw [hl,hr]
    _ = comp (comp (FP.fst A B) (FP.inl A B) +
          comp (FP.snd A B) (FP.inr A B)) h2 := by
          rw [Preadditive.add_comp,Category.assoc,Category.assoc]
    _ = comp (𝟙 (FP.sum A B)) h2 := by rw [FP.total_sum]
    _ = h2 := Category.id_comp h2
lemma FP.sum_hom_ext_right {A B C : FP} {h1 h2 : C ⟶ FP.sum A B}
    (hf : comp h1 (FP.fst A B) = comp h2 (FP.fst A B))
    (hs : comp h1 (FP.snd A B) = comp h2 (FP.snd A B)) :
    h1 = h2 := by
  calc h1 = comp h1 (𝟙 (FP.sum A B)) := (Category.comp_id h1).symm
    _ = comp h1 (comp (FP.fst A B) (FP.inl A B) +
          comp (FP.snd A B) (FP.inr A B)) := by rw [FP.total_sum]
    _ = comp (comp h1 (FP.fst A B)) (FP.inl A B) +
          comp (comp h1 (FP.snd A B)) (FP.inr A B) := by
          rw [Preadditive.comp_add,Category.assoc,Category.assoc]
    _ = comp (comp h2 (FP.fst A B)) (FP.inl A B) +
          comp (comp h2 (FP.snd A B)) (FP.inr A B) := by
          rw [hf,hs]
    _ = comp h2 (comp (FP.fst A B) (FP.inl A B) +
          comp (FP.snd A B) (FP.inr A B)) := by
          rw [Preadditive.comp_add,Category.assoc,Category.assoc]
    _ = comp h2 (𝟙 (FP.sum A B)) := by rw [FP.total_sum]
    _ = h2 := Category.comp_id h2
lemma FP.sum_hom_eq_mat {A B C D : FP} (h : FP.sum A B ⟶ FP.sum C D) :
    h = FP.mat
      (comp (FP.inl A B) (comp h (FP.fst C D)))
      (comp (FP.inr A B) (comp h (FP.fst C D)))
      (comp (FP.inl A B) (comp h (FP.snd C D)))
      (comp (FP.inr A B) (comp h (FP.snd C D))) := by
  apply FP.sum_hom_ext_left
  · apply FP.sum_hom_ext_right
    · simp only [FP.mat,Category.assoc,FP.inl_desc,FP.lift_fst]
    · simp only [FP.mat,Category.assoc,FP.inl_desc,FP.lift_snd]
  · apply FP.sum_hom_ext_right
    · simp only [FP.mat,Category.assoc,FP.inr_desc,FP.lift_fst]
    · simp only [FP.mat,Category.assoc,FP.inr_desc,FP.lift_snd]
lemma FP.lift_desc {A B C D : FP} (f : C ⟶ A) (g : C ⟶ B) (h : A ⟶ D) (k : B ⟶ D) :
    comp (FP.lift f g) (FP.desc h k) =
      comp f h + comp g k := by
  dsimp [FP.lift,FP.desc]
  rw [Preadditive.add_comp,Preadditive.comp_add,Preadditive.comp_add,
    Category.assoc,Category.assoc,Category.assoc,Category.assoc,
    ← Category.assoc (FP.inl A B),← Category.assoc (FP.inl A B),
    ← Category.assoc (FP.inr A B),← Category.assoc (FP.inr A B),
    FP.inl_fst,FP.inl_snd,FP.inr_fst,FP.inr_snd,
    Category.id_comp,Category.id_comp,Limits.zero_comp,Limits.zero_comp,
    Limits.comp_zero,Limits.comp_zero,add_zero,zero_add]
lemma FP.inl_mat {A B C D : FP}
    (f11 : A ⟶ C) (f12 : B ⟶ C) (f21 : A ⟶ D) (f22 : B ⟶ D) :
    comp (FP.inl A B) (FP.mat f11 f12 f21 f22) = FP.lift f11 f21 :=
  FP.inl_desc _ _
lemma FP.inr_mat {A B C D : FP}
    (f11 : A ⟶ C) (f12 : B ⟶ C) (f21 : A ⟶ D) (f22 : B ⟶ D) :
    comp (FP.inr A B) (FP.mat f11 f12 f21 f22) = FP.lift f12 f22 :=
  FP.inr_desc _ _
lemma FP.mat_fst {A B C D : FP}
    (f11 : A ⟶ C) (f12 : B ⟶ C) (f21 : A ⟶ D) (f22 : B ⟶ D) :
    comp (FP.mat f11 f12 f21 f22) (FP.fst C D) = FP.desc f11 f12 := by
  apply FP.sum_hom_ext_left
  · rw [← Category.assoc,FP.inl_mat,FP.lift_fst,FP.inl_desc]
  · rw [← Category.assoc,FP.inr_mat,FP.lift_fst,FP.inr_desc]
lemma FP.mat_snd {A B C D : FP}
    (f11 : A ⟶ C) (f12 : B ⟶ C) (f21 : A ⟶ D) (f22 : B ⟶ D) :
    comp (FP.mat f11 f12 f21 f22) (FP.snd C D) = FP.desc f21 f22 := by
  apply FP.sum_hom_ext_left
  · rw [← Category.assoc,FP.inl_mat,FP.lift_snd,FP.inl_desc]
  · rw [← Category.assoc,FP.inr_mat,FP.lift_snd,FP.inr_desc]
lemma FP.mat_id (A B : FP) :
    FP.mat (𝟙 A) 0 0 (𝟙 B) = 𝟙 (FP.sum A B) := by
  apply FP.sum_hom_ext_left <;> apply FP.sum_hom_ext_right
  · simp [FP.inl_mat,FP.lift_fst,FP.inl_fst]
  · simp [FP.inl_mat,FP.lift_snd,FP.inl_snd]
  · simp [FP.inr_mat,FP.lift_fst,FP.inr_fst]
  · simp [FP.inr_mat,FP.lift_snd,FP.inr_snd]
def FP.sumEquivProd (X Y : FP) : (FP.sum X Y).Mod ≃ₗ[Λ] X.Mod × Y.Mod where
  toFun z := ((FP.fst X Y).hom z,(FP.snd X Y).hom z)
  invFun p := (FP.inl X Y).hom p.1 + (FP.inr X Y).hom p.2
  left_inv z := by
    have h := congrArg (fun (m : FP.sum X Y ⟶ FP.sum X Y) => m.hom z)
      (FP.total_sum X Y)
    simpa using h
  right_inv p := by
    ext : 1
    · have h1 := congrArg (fun (m : X ⟶ X) => m.hom p.1) (FP.inl_fst X Y)
      have h2 := congrArg (fun (m : Y ⟶ X) => m.hom p.2) (FP.inr_fst X Y)
      simp only [FH.comp_hom,FH.id_hom,FH.zero_hom,LinearMap.comp_apply,
        LinearMap.id_apply,LinearMap.zero_apply] at h1 h2
      simp [h1,h2]
    · have h1 := congrArg (fun (m : X ⟶ Y) => m.hom p.1) (FP.inl_snd X Y)
      have h2 := congrArg (fun (m : Y ⟶ Y) => m.hom p.2) (FP.inr_snd X Y)
      simp only [FH.comp_hom,FH.id_hom,FH.zero_hom,LinearMap.comp_apply,
        LinearMap.id_apply,LinearMap.zero_apply] at h1 h2
      simp [h1,h2]
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
lemma FP.mat_apply_fst {A B C D : FP}
    (f11 : A ⟶ C) (f12 : B ⟶ C) (f21 : A ⟶ D) (f22 : B ⟶ D) (z : (FP.sum A B).Mod) :
    (FP.fst C D).hom ((FP.mat f11 f12 f21 f22).hom z) =
      f11.hom ((FP.fst A B).hom z) + f12.hom ((FP.snd A B).hom z) := by
  have h := congrArg (fun (m : FP.sum A B ⟶ C) => m.hom z) (FP.mat_fst f11 f12 f21 f22)
  simpa [FP.desc] using h
lemma FP.mat_apply_snd {A B C D : FP}
    (f11 : A ⟶ C) (f12 : B ⟶ C) (f21 : A ⟶ D) (f22 : B ⟶ D) (z : (FP.sum A B).Mod) :
    (FP.snd C D).hom ((FP.mat f11 f12 f21 f22).hom z) =
      f21.hom ((FP.fst A B).hom z) + f22.hom ((FP.snd A B).hom z) := by
  have h := congrArg (fun (m : FP.sum A B ⟶ D) => m.hom z) (FP.mat_snd f11 f12 f21 f22)
  simpa [FP.desc] using h
lemma FP.mat_comp {A B C D E F : FP}
    (a11 : A ⟶ C) (a12 : B ⟶ C) (a21 : A ⟶ D) (a22 : B ⟶ D)
    (b11 : C ⟶ E) (b12 : D ⟶ E) (b21 : C ⟶ F) (b22 : D ⟶ F) :
    comp (FP.mat a11 a12 a21 a22) (FP.mat b11 b12 b21 b22) =
      FP.mat
        (comp a11 b11 + comp a21 b12)
        (comp a12 b11 + comp a22 b12)
        (comp a11 b21 + comp a21 b22)
        (comp a12 b21 + comp a22 b22) := by
  apply FP.hom_ext; intro z
  apply (FP.sumEquivProd E F).injective
  ext : 1
  · change (FP.fst E F).hom ((FP.mat b11 b12 b21 b22).hom ((FP.mat a11 a12 a21 a22).hom z)) =
      (FP.fst E F).hom ((FP.mat _ _ _ _).hom z)
    rw [FP.mat_apply_fst,FP.mat_apply_fst,FP.mat_apply_snd,FP.mat_apply_fst]
    simp only [FH.add_hom,FH.comp_hom,LinearMap.add_apply,LinearMap.comp_apply,
      map_add]
    abel
  · change (FP.snd E F).hom ((FP.mat b11 b12 b21 b22).hom ((FP.mat a11 a12 a21 a22).hom z)) =
      (FP.snd E F).hom ((FP.mat _ _ _ _).hom z)
    rw [FP.mat_apply_snd,FP.mat_apply_fst,FP.mat_apply_snd,FP.mat_apply_snd]
    simp only [FH.add_hom,FH.comp_hom,LinearMap.add_apply,LinearMap.comp_apply,
      map_add]
    abel
lemma FP.fst_inl_add_inr {X Y : FP} (x : X.Mod) (y : Y.Mod) :
    (FP.fst X Y).hom ((FP.inl X Y).hom x + (FP.inr X Y).hom y) = x :=
  congrArg Prod.fst ((FP.sumEquivProd X Y).apply_symm_apply (x,y))
lemma FP.snd_inl_add_inr {X Y : FP} (x : X.Mod) (y : Y.Mod) :
    (FP.snd X Y).hom ((FP.inl X Y).hom x + (FP.inr X Y).hom y) = y :=
  congrArg Prod.snd ((FP.sumEquivProd X Y).apply_symm_apply (x,y))
lemma FP.sum_shift_eq (X Y : FP) :
    (FP.sum X Y)⟦(1 : ℤ)⟧ = FP.sum (X⟦(1 : ℤ)⟧) (Y⟦(1 : ℤ)⟧) := rfl
def FP.sumShiftIso (X Y : FP) :
    FP.sum (X⟦(1 : ℤ)⟧) (Y⟦(1 : ℤ)⟧) ≅ (FP.sum X Y)⟦(1 : ℤ)⟧ :=
  eqToIso (FP.sum_shift_eq X Y).symm
lemma FP.sumShiftIso_hom_hom (X Y : FP)
    (z : (FP.sum (X⟦(1 : ℤ)⟧) (Y⟦(1 : ℤ)⟧)).Mod) :
    (FP.sumShiftIso X Y).hom.hom z = z := rfl
lemma FP.sumShiftIso_inv_hom (X Y : FP)
    (z : ((FP.sum X Y)⟦(1 : ℤ)⟧).Mod) :
    (FP.sumShiftIso X Y).inv.hom z = z := rfl
lemma z114 {M : Type} [AddCommGroup M] [Module Λ M]
    {X Y : FP} {i : M →ₗ[Λ] X.Mod} {f : X ⟶ Y} (h : ExactAt i f.hom) :
    ExactAt ((z3 X).toLinearMap.comp (nuMap i)) ((f⟦(1 : ℤ)⟧').hom) := by
  rw [z7] at h
  apply SetLike.ext; intro x
  change (∃ m : nuMod M,z3 X (nuMap i m) = x) ↔ (f⟦(1 : ℤ)⟧').hom x = 0
  constructor
  · rintro ⟨m,rfl⟩
    rw [← z5 f]
    have h0 : (nuMap f.hom) (nuMap i m) = 0 := by
      apply nuMod.ext
      exact (h (i m.val)).mpr ⟨m.val,rfl⟩
    rw [h0,map_zero]; rfl
  · intro hx
    have h1 : (z3 Y) (nuMap f.hom ((z3 X).symm x)) = 0 := hx
    have h2 : nuMap f.hom ((z3 X).symm x) = 0 :=
      (map_eq_zero_iff (z3 Y) (z3 Y).injective).mp h1
    obtain ⟨m,hm⟩ := (h ((z3 X).symm x).val).mp (congrArg nuMod.val h2)
    refine ⟨⟨m⟩,?_⟩
    change z3 X ⟨i m⟩ = x
    rw [hm]
    exact (z3 X).apply_symm_apply x
lemma FP.inl_shift (X Y : FP) :
    (FP.inl X Y)⟦(1 : ℤ)⟧' = FP.inl (X⟦(1 : ℤ)⟧) (Y⟦(1 : ℤ)⟧) := by
  apply FP.hom_ext; intro x; funext v i
  change z206 (z104 v)
    ⟨if h : i.1 < X.mult (rev v) then
      ((z3 X).symm x).val (rev v) ⟨i.1,h⟩
     else 0⟩ =
    if h : i.1 < X.mult (rev v) then x v ⟨i.1,h⟩ else 0
  by_cases h : i.1 < X.mult (rev v)
  · rw [dif_pos h,dif_pos h]
    have hx := congrArg (fun f : (z13 X).Mod => f v ⟨i.1,h⟩)
      ((z3 X).apply_symm_apply x)
    exact hx
  · rw [dif_neg h,dif_neg h]
    exact (z206 (z104 v)).map_zero
lemma FP.inr_shift (X Y : FP) :
    (FP.inr X Y)⟦(1 : ℤ)⟧' = FP.inr (X⟦(1 : ℤ)⟧) (Y⟦(1 : ℤ)⟧) := by
  apply FP.hom_ext; intro y; funext v i
  have hi : i.1 < X.mult (rev v) + Y.mult (rev v) := i.2
  change z206 (z104 v)
    ⟨if h : i.1 < X.mult (rev v) then 0
     else ((z3 Y).symm y).val (rev v)
       ⟨i.1 - X.mult (rev v),by omega⟩⟩ =
    if h : i.1 < X.mult (rev v) then 0
    else y v ⟨i.1 - X.mult (rev v),by change i.1 - X.mult (rev v) < Y.mult (rev v); omega⟩
  by_cases h : i.1 < X.mult (rev v)
  · rw [dif_pos h,dif_pos h]
    exact (z206 (z104 v)).map_zero
  · rw [dif_neg h,dif_neg h]
    have hy := congrArg (fun f : (z13 Y).Mod => f v
      ⟨i.1 - X.mult (rev v),by change i.1 - X.mult (rev v) < Y.mult (rev v); omega⟩)
      ((z3 Y).apply_symm_apply y)
    exact hy
lemma FP.fst_shift (X Y : FP) :
    (FP.fst X Y)⟦(1 : ℤ)⟧' = FP.fst (X⟦(1 : ℤ)⟧) (Y⟦(1 : ℤ)⟧) := by
  apply FP.hom_ext; intro z; funext v i
  have hi : i.1 < X.mult (rev v) := i.2
  have hz := congrArg (fun f : (z13 (FP.sum X Y)).Mod =>
    f v ⟨i.1,by change i.1 < X.mult (rev v) + Y.mult (rev v); omega⟩)
    ((z3 (FP.sum X Y)).apply_symm_apply z)
  exact hz
lemma FP.snd_shift (X Y : FP) :
    (FP.snd X Y)⟦(1 : ℤ)⟧' = FP.snd (X⟦(1 : ℤ)⟧) (Y⟦(1 : ℤ)⟧) := by
  apply FP.hom_ext; intro z; funext v i
  have hi : i.1 < Y.mult (rev v) := i.2
  have hz := congrArg (fun f : (z13 (FP.sum X Y)).Mod =>
    f v ⟨X.mult (rev v) + i.1,by change X.mult (rev v) + i.1 < X.mult (rev v) + Y.mult (rev v); omega⟩)
    ((z3 (FP.sum X Y)).apply_symm_apply z)
  exact hz
lemma FP.desc_shift {A B C : FP} (f : A ⟶ C) (g : B ⟶ C) :
    (FP.desc f g)⟦(1 : ℤ)⟧' = FP.desc (f⟦(1 : ℤ)⟧') (g⟦(1 : ℤ)⟧') := by
  dsimp [FP.desc]
  rw [Functor.map_add,Functor.map_comp,Functor.map_comp,FP.fst_shift,FP.snd_shift]
  rfl
lemma FP.lift_shift {A B C : FP} (f : C ⟶ A) (g : C ⟶ B) :
    (FP.lift f g)⟦(1 : ℤ)⟧' = FP.lift (f⟦(1 : ℤ)⟧') (g⟦(1 : ℤ)⟧') := by
  dsimp [FP.lift]
  rw [Functor.map_add,Functor.map_comp,Functor.map_comp,FP.inl_shift,FP.inr_shift]
  rfl
lemma FP.mat_shift {A B C D : FP}
    (f11 : A ⟶ C) (f12 : B ⟶ C) (f21 : A ⟶ D) (f22 : B ⟶ D) :
    (FP.mat f11 f12 f21 f22)⟦(1 : ℤ)⟧' =
      FP.mat (f11⟦(1 : ℤ)⟧') (f12⟦(1 : ℤ)⟧') (f21⟦(1 : ℤ)⟧') (f22⟦(1 : ℤ)⟧') := by
  dsimp [FP.mat]
  rw [FP.desc_shift,FP.lift_shift,FP.lift_shift]
  rfl
lemma FP.sumShiftIso_fst (X Y : FP) :
    comp (FP.sumShiftIso X Y).hom ((FP.fst X Y)⟦(1 : ℤ)⟧') =
      FP.fst (X⟦(1 : ℤ)⟧) (Y⟦(1 : ℤ)⟧) := by
  apply FP.hom_ext; intro z
  change ((FP.fst X Y)⟦(1 : ℤ)⟧').hom z = (FP.fst (X⟦(1 : ℤ)⟧) (Y⟦(1 : ℤ)⟧)).hom z
  rw [FP.fst_shift]; rfl
lemma FP.sumShiftIso_snd (X Y : FP) :
    comp (FP.sumShiftIso X Y).hom ((FP.snd X Y)⟦(1 : ℤ)⟧') =
      FP.snd (X⟦(1 : ℤ)⟧) (Y⟦(1 : ℤ)⟧) := by
  apply FP.hom_ext; intro z
  change ((FP.snd X Y)⟦(1 : ℤ)⟧').hom z = (FP.snd (X⟦(1 : ℤ)⟧) (Y⟦(1 : ℤ)⟧)).hom z
  rw [FP.snd_shift]; rfl
lemma FP.inl_sumShiftIso (X Y : FP) :
    comp (FP.inl (X⟦(1 : ℤ)⟧) (Y⟦(1 : ℤ)⟧)) (FP.sumShiftIso X Y).hom =
      (FP.inl X Y)⟦(1 : ℤ)⟧' := by
  apply FP.hom_ext; intro z
  change (FP.inl (X⟦(1 : ℤ)⟧) (Y⟦(1 : ℤ)⟧)).hom z = ((FP.inl X Y)⟦(1 : ℤ)⟧').hom z
  rw [FP.inl_shift]; rfl
lemma FP.inr_sumShiftIso (X Y : FP) :
    comp (FP.inr (X⟦(1 : ℤ)⟧) (Y⟦(1 : ℤ)⟧)) (FP.sumShiftIso X Y).hom =
      (FP.inr X Y)⟦(1 : ℤ)⟧' := by
  apply FP.hom_ext; intro z
  change (FP.inr (X⟦(1 : ℤ)⟧) (Y⟦(1 : ℤ)⟧)).hom z = ((FP.inr X Y)⟦(1 : ℤ)⟧').hom z
  rw [FP.inr_shift]; rfl
lemma FP.sumShiftIso_mat_shift {A B C D : FP}
    (f11 : A ⟶ C) (f12 : B ⟶ C) (f21 : A ⟶ D) (f22 : B ⟶ D) :
    comp (FP.sumShiftIso A B).hom ((FP.mat f11 f12 f21 f22)⟦(1 : ℤ)⟧') =
      comp
        (FP.mat (f11⟦(1 : ℤ)⟧') (f12⟦(1 : ℤ)⟧') (f21⟦(1 : ℤ)⟧') (f22⟦(1 : ℤ)⟧'))
        (FP.sumShiftIso C D).hom := by
  apply FP.hom_ext; intro z
  change ((FP.mat f11 f12 f21 f22)⟦(1 : ℤ)⟧').hom z =
    (FP.mat (f11⟦(1 : ℤ)⟧') (f12⟦(1 : ℤ)⟧') (f21⟦(1 : ℤ)⟧') (f22⟦(1 : ℤ)⟧')).hom z
  rw [FP.mat_shift]; rfl
def FP.isoOfLinearEquiv {X Y : FP} (e : X.Mod ≃ₗ[Λ] Y.Mod) : X ≅ Y where
  hom := ⟨e.toLinearMap⟩
  inv := ⟨e.symm.toLinearMap⟩
  hom_inv_id := by apply FP.hom_ext; intro x; exact e.symm_apply_apply x
  inv_hom_id := by apply FP.hom_ext; intro y; exact e.apply_symm_apply y
def lenB (b : B) : ℕ := 2 * b.deg.1 + b.src.1 - b.tgt.1
lemma z349 (b : B) : lenB b ≤ 4 := by
  have hb := b.2
  dsimp [lenB,B.src,B.tgt,B.deg] at hb ⊢
  omega
lemma z288 (b : B) : lenB b = 0 ↔ b = eB b.src := by
  have hb := b.2
  constructor
  · intro h
    apply Subtype.ext
    rcases b with ⟨⟨⟨i,hi⟩,⟨j,hj⟩,⟨r,hr⟩⟩,hb⟩
    dsimp [lenB,eB,B.src,B.tgt,B.deg] at hb h ⊢
    ext <;> dsimp <;> omega
  · intro h
    rw [h]
    dsimp [lenB,eB,B.src,B.tgt,B.deg]
    omega
lemma lenB_mulB {x y z : B} (h : mulB x y = some z) : lenB z = lenB x + lenB y := by
  have hx := x.2; have hy := y.2
  unfold mulB at h
  by_cases hc : y.tgt = x.src ∧ y.deg.1 + x.deg.1 ≤ x.tgt.1 ∧
      y.src.1 + (y.deg.1 + x.deg.1) < 5
  · rw [dif_pos hc] at h
    have hz := Option.some.inj h
    rw [← hz]
    have hmid := congrArg Fin.val hc.1
    dsimp [lenB,B.src,B.tgt,B.deg] at hx hy hc hmid ⊢
    omega
  · rw [dif_neg hc] at h; cases h
def z112 (k : ℕ) (a : Λ) : Prop := ∀ b : B,lenB b < k → a.val b = 0
lemma z145 (a : Λ) : z112 0 a := fun _ h => absurd h (Nat.not_lt_zero _)
lemma z135 {k l : ℕ} {a b : Λ} (ha : z112 k a) (hb : z112 l b) :
    z112 (k + l) (a * b) := by
  intro c hc
  rw [Λ.mul_val]
  refine sum_eq_zero fun x _ => sum_eq_zero fun y _ => ?_
  by_cases hm : mulB x y = some c
  · rw [if_pos hm]
    have hlen := lenB_mulB hm
    by_cases hx : lenB x < k
    · rw [ha x hx,zero_mul]
    · have hy : lenB y < l := by omega
      rw [hb y hy,mul_zero]
  · rw [if_neg hm]
lemma z247 {a : Λ} (ha : z112 5 a) : a = 0 := by
  apply xL; ext b
  exact ha b (Nat.lt_succ_of_le (z349 b))
def z325 (W : Type) [AddCommGroup W] [Module Λ W] : Submodule Λ W :=
  Submodule.span Λ { x : W | ∃ a : Λ,z112 1 a ∧ ∃ y : W,x = a • y }
def z343 (k : ℕ) (W : Type) [AddCommGroup W] [Module Λ W] : Submodule Λ W :=
  Submodule.span Λ { x : W | ∃ a : Λ,z112 k a ∧ ∃ y : W,x = a • y }
lemma radPow_zero (W : Type) [AddCommGroup W] [Module Λ W] : z343 0 W = ⊤ := by
  rw [eq_top_iff]
  intro w _
  exact Submodule.subset_span ⟨1,z145 1,w,(one_smul Λ w).symm⟩
lemma radPow_five (W : Type) [AddCommGroup W] [Module Λ W] : z343 5 W = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨a,ha,y,rfl⟩
    rw [z247 ha,zero_smul]
    exact Submodule.zero_mem _
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy; exact Submodule.add_mem _ hx hy
  · intro r x _ hx; exact Submodule.smul_mem _ r hx
lemma z39 {W : Type} [AddCommGroup W] [Module Λ W]
    (h : z325 W = ⊤) (k : ℕ) : z343 k W ≤ z343 (k + 1) W := by
  intro w hw
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨a,ha,y,rfl⟩
    have hy : y ∈ z325 W := by rw [h]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨b,hb,z,rfl⟩
      rw [← mul_smul]
      exact Submodule.subset_span ⟨a * b,z135 ha hb,z,rfl⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro x1 x2 _ _ hx1 hx2
      rw [smul_add]; exact Submodule.add_mem _ hx1 hx2
    · intro c x _ hx
      have hca : a • (c • x) = (a * c) • x := (mul_smul a c x).symm
      rw [hca]
      have hac : z112 k (a * c) := by
        simpa using z135 ha (z145 c)
      exact by
        have hstep : ∀ u ∈ z325 W,∀ a0 : Λ,z112 k a0 → a0 • u ∈ z343 (k + 1) W := by
          intro u hu
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
          · rintro _ ⟨b,hb,z,rfl⟩ a0 ha0
            rw [← mul_smul]
            exact Submodule.subset_span ⟨a0 * b,z135 ha0 hb,z,rfl⟩
          · intro a0 _; rw [smul_zero]; exact Submodule.zero_mem _
          · intro u1 u2 _ _ hu1 hu2 a0 ha0
            rw [smul_add]; exact Submodule.add_mem _ (hu1 a0 ha0) (hu2 a0 ha0)
          · intro r u1 _ hu1 a0 ha0
            rw [← mul_smul]
            exact hu1 (a0 * r) (by simpa using z135 ha0 (z145 r))
        exact hstep x (by rw [h]; trivial) (a * c) hac
  · exact Submodule.zero_mem _
  · intro x1 x2 _ _ hx1 hx2; exact Submodule.add_mem _ hx1 hx2
  · intro c x _ hx; exact Submodule.smul_mem _ c hx
lemma z224 {W : Type} [AddCommGroup W] [Module Λ W]
    (hne : ∃ w : W,w ≠ 0) : ∃ w : W,w ∉ z325 W := by
  by_contra hall
  push Not at hall
  have htop : z325 W = ⊤ := by rw [eq_top_iff]; intro w _; exact hall w
  have h05 : z343 0 W ≤ z343 5 W :=
    le_trans (z39 htop 0)
      (le_trans (z39 htop 1)
        (le_trans (z39 htop 2)
          (le_trans (z39 htop 3)
            (z39 htop 4))))
  rw [radPow_zero,radPow_five] at h05
  obtain ⟨w,hw⟩ := hne
  have : w ∈ (⊥ : Submodule Λ W) := h05 (by trivial)
  exact hw (by simpa using this)
lemma z322 : (∑ v : Fin 5,eΛ v) = 1 := by
  apply xL; ext c
  rw [Λ.one_val_eq_sum]
  have hsum : ∀ (s : Finset (Fin 5)),(∑ v ∈ s,eΛ v).val c = ∑ v ∈ s,(eΛ v).val c := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s' ha ih; rw [Finset.sum_insert ha,Finset.sum_insert ha,Λ.add_val,ih]
  rw [hsum]
  rfl
lemma z351 (v : Fin 5) : eΛ v * eΛ v = eΛ v := by
  apply xL; ext c
  rw [Λ.mul_val]
  rw [sum_eq_single (eB v)]
  · rw [sum_eq_single (eB v)]
    · rw [z26]
      have htgt : (eB v).tgt = v := rfl
      rw [if_pos htgt]
      dsimp [eΛ,z12]
      by_cases h : eB v = c
      · subst h; simp
      · rw [if_neg (by intro hh; exact h (Option.some.inj hh)),if_neg (Ne.symm h)]
    · intro y _ hy
      dsimp [eΛ,z12]; rw [if_neg hy,mul_zero,ite_self]
    · intro h; exact absurd (mem_univ _) h
  · intro x _ hx
    refine sum_eq_zero fun y _ => ?_
    dsimp [eΛ,z12]; rw [if_neg hx,zero_mul,ite_self]
  · intro h; exact absurd (mem_univ _) h
def z67 (v : Fin 5) : Pv v := ⟨fun c => if c.1 = eB v then 1 else 0⟩
lemma z329 (v : Fin 5) : z67 v ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : Pv v => x.val ⟨eB v,rfl⟩) h
  dsimp [z67] at h1
  simp at h1
def z134 {v : Fin 5} (x : Pv v) : Λ :=
  ⟨fun b => if h : b.src = v then x.val ⟨b,h⟩ else 0⟩
lemma liftPv_add {v : Fin 5} (x y : Pv v) : z134 (x + y) = z134 x + z134 y := by
  apply xL; ext b; dsimp [z134]
  by_cases h : b.src = v <;> simp [h]
lemma z348 (v : Fin 5) : z134 (z67 v) = eΛ v := by
  apply xL; ext b; dsimp [z134,z67,eΛ,z12]
  by_cases h : b.src = v
  · rw [dif_pos h]
  · rw [dif_neg h,if_neg]
    intro heq; apply h; rw [heq]; rfl
lemma z307 {v : Fin 5} (a : Λ) (x : Pv v) : z134 (a • x) = a * z134 x := by
  apply xL; ext c
  rw [Λ.mul_val]
  by_cases hc : c.src = v
  · dsimp [z134]; rw [dif_pos hc,Pv.smul_val]
    refine sum_congr rfl fun b _ => ?_
    symm
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y : B => y.src = v)]
    have hzero : (∑ y ∈ Finset.univ.filter (fun y : B => ¬ y.src = v),
        if mulB b y = some c then a.val b * if h : y.src = v then x.val ⟨y,h⟩ else 0 else 0) = 0 := by
      refine sum_eq_zero fun y hy => ?_
      have hne : ¬ y.src = v := (Finset.mem_filter.mp hy).2
      simp [hne]
    rw [hzero,add_zero]
    refine Finset.sum_bij (fun y hy => (⟨y,(Finset.mem_filter.mp hy).2⟩ : Bv v))
      (fun _ _ => mem_univ _)
      (fun y1 _ y2 _ h => congrArg Subtype.val h)
      (fun y _ => ⟨y.1,Finset.mem_filter.mpr ⟨mem_univ _,y.2⟩,Subtype.ext rfl⟩)
      (fun y hy => by
        have hsrc : y.src = v := (Finset.mem_filter.mp hy).2
        simp [hsrc])
  · dsimp [z134]; rw [dif_neg hc]
    symm
    refine sum_eq_zero fun b _ => sum_eq_zero fun y _ => ?_
    by_cases hm : mulB b y = some c
    · have hys : y.src ≠ v := by intro h; exact hc ((z71 hm).trans h)
      rw [if_pos hm,dif_neg hys,mul_zero]
    · rw [if_neg hm]
lemma z140 {v : Fin 5} (x : Pv v) : (z134 x) • z67 v = x := by
  apply xP; ext c
  rw [Pv.smul_val]
  rw [sum_eq_single c.1]
  · rw [sum_eq_single ⟨eB v,rfl⟩]
    · rw [z91,if_pos c.2.symm,if_pos rfl]
      dsimp [z134,z67]
      rw [dif_pos c.2,if_pos rfl,mul_one]
    · intro y _ hy
      dsimp [z67]
      have hy' : y.1 ≠ eB v := fun hh => hy (Subtype.ext hh)
      rw [if_neg hy',mul_zero,ite_self]
    · intro h; exact absurd (mem_univ _) h
  · intro b _ hb
    refine sum_eq_zero fun y _ => ?_
    by_cases hy : y.1 = eB v
    · rw [hy,z91]
      by_cases hbs : v = b.src
      · rw [if_pos hbs,if_neg (fun hh => hb (Option.some.inj hh))]
      · rw [if_neg hbs,if_neg (by simp)]
    · dsimp [z67]; rw [if_neg hy,mul_zero,ite_self]
  · intro h; exact absurd (mem_univ _) h
lemma z124 {v : Fin 5} {x : Pv v} (hx : x.val ⟨eB v,rfl⟩ = 0) :
    z112 1 (z134 x) := by
  intro b hb
  have h0 : lenB b = 0 := Nat.lt_one_iff.mp hb
  have heq : b = eB b.src := (z288 b).mp h0
  dsimp [z134]
  by_cases hs : b.src = v
  · rw [dif_pos hs]
    have hsub : (⟨b,hs⟩ : Bv v) = ⟨eB v,rfl⟩ := Subtype.ext (heq.trans (congrArg eB hs))
    rw [hsub]; exact hx
  · rw [dif_neg hs]
lemma z330 {u v : Fin 5} (y : Pv u) :
    (eΛ v • y).val ⟨eB u,rfl⟩ = if u = v then y.val ⟨eB u,rfl⟩ else 0 := by
  rw [Pv.smul_val]
  rw [sum_eq_single (eB v)]
  · rw [sum_eq_single ⟨eB u,rfl⟩]
    · rw [z26]
      by_cases h : u = v
      · subst h; simp [eB,B.tgt,eΛ,z12]
      · have htgt : (eB u).tgt ≠ v := h
        simp [htgt,h]
    · intro z _ hz
      rw [z26]
      by_cases h1 : z.1.tgt = v
      · rw [if_pos h1,if_neg]
        intro hh; exact hz (Subtype.ext (Option.some.inj hh))
      · rw [if_neg h1,if_neg (by simp)]
    · intro h; exact absurd (mem_univ _) h
  · intro b _ hb
    refine sum_eq_zero fun z _ => ?_
    dsimp [eΛ,z12]; rw [if_neg hb,zero_mul,ite_self]
  · intro h; exact absurd (mem_univ _) h
def PvObj (v : Fin 5) : FP := ⟨fun u => if u = v then 1 else 0⟩
def z344 (v : Fin 5) : Pv v ≃ₗ[Λ] (PvObj v).Mod where
  toFun x u i := by
    by_cases h : u = v
    · subst h; exact x
    · exact Fin.elim0 (by dsimp [PvObj] at i; rw [if_neg h] at i; exact i)
  invFun f := f v ⟨0,by dsimp [PvObj]; simp⟩
  left_inv x := by simp
  right_inv f := by
    funext u i
    by_cases h : u = v
    · subst h
      simp only [↓reduceDIte]
      have hi : i = ⟨0,by dsimp [PvObj]; simp⟩ := by
        apply Fin.ext
        have hlt : i.1 < 1 := by simpa [PvObj] using i.2
        change i.1 = 0
        omega
      rw [hi]
    · exfalso
      exact absurd i.2 (by simp [PvObj,h])
  map_add' x y := by
    funext u i
    by_cases h : u = v
    · subst h; simp
    · exfalso; exact absurd i.2 (by simp [PvObj,h])
  map_smul' a x := by
    funext u i
    by_cases h : u = v
    · subst h; simp
    · exfalso; exact absurd i.2 (by simp [PvObj,h])
def FP.coordIn {P : FP} (u : Fin 5) (k : Fin (P.mult u)) : Pv u →ₗ[Λ] P.Mod where
  toFun x w j :=
    if h : w = u then
      if j = Fin.cast (by rw [h]) k then h ▸ x else 0
    else 0
  map_add' x y := by
    funext w j
    by_cases h : w = u
    · subst h; dsimp; split_ifs <;> simp
    · simp [dif_neg h]
  map_smul' a x := by
    funext w j
    by_cases h : w = u
    · subst h; dsimp; split_ifs <;> simp
    · simp [dif_neg h]
lemma FP.mod_eq_sum_coordIn {P : FP} (z : P.Mod) :
    z = ∑ u : Fin 5,∑ k : Fin (P.mult u),FP.coordIn u k (z u k) := by
  funext w j
  rw [Finset.sum_apply,Finset.sum_apply]
  rw [sum_eq_single w]
  · rw [Finset.sum_apply,Finset.sum_apply]
    rw [sum_eq_single j]
    · simp [FP.coordIn]
    · intro k _ hkj; simp [FP.coordIn,Ne.symm hkj]
    · intro h; exact absurd (mem_univ _) h
  · intro u _ huw
    rw [Finset.sum_apply,Finset.sum_apply]
    refine sum_eq_zero fun k _ => ?_
    simp [FP.coordIn,Ne.symm huw]
  · intro h; exact absurd (mem_univ _) h
lemma z168 : ∀ (n : ℕ) {P : FP} {W : Type} [AddCommGroup W] [Module Λ W]
    [Fintype W],Fintype.card W ≤ n →
    ∀ (i : W →ₗ[Λ] P.Mod) (r : P.Mod →ₗ[Λ] W),r.comp i = LinearMap.id →
    ∃ (Z : FP),Nonempty (W ≃ₗ[Λ] Z.Mod)
  | 0,P,W,_,_,_,hcard,_,_,_ => by
    exfalso
    have hpos : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨0⟩
    omega
  | n + 1,P,W,_,_,_,hcard,i,r,hri => by
    by_cases hzero : ∀ w : W,w = 0
    · refine ⟨FP.zero,⟨{
        toFun := fun _ _ k => Fin.elim0 k
        invFun := fun _ => 0
        left_inv := fun w => (hzero w).symm
        right_inv := fun f => by funext v k; exact Fin.elim0 k
        map_add' := fun _ _ => by funext v k; exact Fin.elim0 k
        map_smul' := fun _ _ => by funext v k; exact Fin.elim0 k }⟩⟩
    · push Not at hzero
      obtain ⟨w0,hw0⟩ := z224 hzero
      have hexv : ∃ v : Fin 5,eΛ v • w0 ∉ z325 W := by
        by_contra hall
        push Not at hall
        have hsum : (∑ v : Fin 5,eΛ v • w0) ∈ z325 W :=
          Submodule.sum_mem _ fun v _ => hall v
        have h1 : (∑ v : Fin 5,eΛ v • w0) = w0 := by
          rw [← Finset.sum_smul,z322,one_smul]
        rw [h1] at hsum
        exact hw0 hsum
      obtain ⟨v,hv⟩ := hexv
      let w' : W := eΛ v • w0
      have hw'_idem : eΛ v • w' = w' := by
        change eΛ v • (eΛ v • w0) = eΛ v • w0
        rw [← mul_smul,z351]
      have hex_coord : ∃ (u : Fin 5) (k : Fin (P.mult u)),
          (i w' u k).val ⟨eB u,rfl⟩ ≠ 0 := by
        by_contra hall
        push Not at hall
        have hdecomp : i w' = ∑ u : Fin 5,∑ k : Fin (P.mult u),
            z134 (i w' u k) • FP.coordIn u k (z67 u) := by
          conv_lhs => rw [FP.mod_eq_sum_coordIn (i w')]
          refine sum_congr rfl fun u _ => sum_congr rfl fun k _ => ?_
          rw [← LinearMap.map_smul,z140]
        have hrw : w' = r (i w') := (congrArg (fun m => m w') hri).symm
        rw [hdecomp,map_sum] at hrw
        have hmem : w' ∈ z325 W := by
          rw [hrw]
          refine Submodule.sum_mem _ fun u _ => ?_
          rw [map_sum]
          refine Submodule.sum_mem _ fun k _ => ?_
          rw [LinearMap.map_smul]
          exact Submodule.subset_span ⟨z134 (i w' u k),
            z124 (hall u k),r (FP.coordIn u k (z67 u)),rfl⟩
        exact hv hmem
      obtain ⟨u,k,huk⟩ := hex_coord
      have huv : u = v := by
        have h1 : eΛ v • (i w' u k) = i w' u k := by
          have := congrArg (fun x : P.Mod => x u k) (show eΛ v • i w' = i w' by
            rw [← LinearMap.map_smul,hw'_idem])
          exact this
        have h2 := congrArg (fun x : Pv u => x.val ⟨eB u,rfl⟩) h1
        rw [z330] at h2
        by_contra hne
        rw [if_neg hne] at h2
        exact huk h2.symm
      subst huv
      have huk1 : (i w' u k).val ⟨eB u,rfl⟩ = 1 := by
        have hz2 : ∀ z : ZMod 2,z ≠ 0 → z = 1 := by decide
        exact hz2 _ huk
      let φ : Pv u →ₗ[Λ] W :=
        { toFun := fun x => (z134 x) • w'
          map_add' := fun x y => by rw [liftPv_add,add_smul]
          map_smul' := fun a x => by
            change (z134 (a • x)) • w' = a • ((z134 x) • w')
            rw [z307,mul_smul] }
      let π : W →ₗ[Λ] Pv u :=
        { toFun := fun x => i x u k
          map_add' := fun x y => by simp
          map_smul' := fun a x => by simp }
      have hφ_gen : φ (z67 u) = w' := by
        change (z134 (z67 u)) • w' = w'
        rw [z348,hw'_idem]
      let ψ : Pv u →ₗ[Λ] Pv u := π.comp φ
      let nilp : Pv u →ₗ[Λ] Pv u := ψ - LinearMap.id
      have hnilp_gen : (nilp (z67 u)).val ⟨eB u,rfl⟩ = 0 := by
        change (π (φ (z67 u)) - z67 u).val ⟨eB u,rfl⟩ = 0
        rw [hφ_gen]
        change (i w' u k).val ⟨eB u,rfl⟩ + (z67 u).val ⟨eB u,rfl⟩ = 0
        rw [huk1]
        dsimp [z67]
        rw [if_pos rfl]
        decide
      let a0 : Λ := z134 (nilp (z67 u))
      have ha0 : z112 1 a0 := z124 hnilp_gen
      have hnilp_lift : ∀ x : Pv u,z134 (nilp x) = z134 x * a0 := by
        intro x
        have h1 : nilp x = (z134 x) • (nilp (z67 u)) := by
          conv_lhs => rw [← z140 x]
          exact LinearMap.map_smul nilp (z134 x) (z67 u)
        rw [h1,z307]
      have hnilp_pow : ∀ m : ℕ,∀ x : Pv u,z112 m (z134 ((nilp ^ m) x)) := by
        intro m
        induction m with
        | zero => intro x; exact z145 _
        | succ m ih =>
          intro x
          have hpow : (nilp ^ (m + 1)) x = nilp ((nilp ^ m) x) := by
            rw [pow_succ']; rfl
          rw [hpow,hnilp_lift]
          exact z135 (ih x) ha0
      have hnilp5 : nilp ^ 5 = 0 := by
        apply LinearMap.ext; intro x
        have h5 := z247 (hnilp_pow 5 x)
        have hrec := z140 ((nilp ^ 5) x)
        rw [h5,zero_smul] at hrec
        exact hrec.symm
      let invψ : Pv u →ₗ[Λ] Pv u := 1 + nilp + nilp ^ 2 + nilp ^ 3 + nilp ^ 4
      have hinvψ : invψ.comp ψ = LinearMap.id := by
        have hψ : ψ = 1 + nilp := by
          change ψ = LinearMap.id + (ψ - LinearMap.id)
          abel
        have hmul : invψ * ψ = 1 := by
          rw [hψ]
          dsimp [invψ]
          have h2 : ∀ f : Pv u →ₗ[Λ] Pv u,f + f = 0 := z99
          have hexp :
              (1 + nilp + nilp ^ 2 + nilp ^ 3 + nilp ^ 4) * (1 + nilp) =
              1 + (nilp + nilp) + (nilp ^ 2 + nilp ^ 2) + (nilp ^ 3 + nilp ^ 3) +
                (nilp ^ 4 + nilp ^ 4) + nilp ^ 5 := by
            noncomm_ring
          rw [hexp,h2 nilp,h2 (nilp ^ 2),h2 (nilp ^ 3),h2 (nilp ^ 4),hnilp5]
          simp
        exact hmul
      let ρ : W →ₗ[Λ] Pv u := invψ.comp π
      have hρφ : ρ.comp φ = LinearMap.id := by
        change (invψ.comp π).comp φ = LinearMap.id
        rw [LinearMap.comp_assoc]
        exact hinvψ
      let W' := LinearMap.ker ρ
      letI : Fintype W' := Fintype.ofFinite W'
      let projW' : W →ₗ[Λ] W' :=
        { toFun := fun x => ⟨x - φ (ρ x),by
            change ρ (x - φ (ρ x)) = 0
            rw [map_sub]
            have h1 := congrArg (fun m => m (ρ x)) hρφ
            simp only [LinearMap.comp_apply,LinearMap.id_apply] at h1
            rw [h1,sub_self]⟩
          map_add' := fun x y => by ext; simp [sub_add_sub_comm]
          map_smul' := fun a x => by ext; simp [smul_sub] }
      let eW : W ≃ₗ[Λ] Pv u × W' :=
        { toFun := fun x => (ρ x,projW' x)
          invFun := fun p => φ p.1 + p.2.1
          left_inv := fun x => by change φ (ρ x) + (x - φ (ρ x)) = x; abel
          right_inv := fun p => by
            ext : 1
            · change ρ (φ p.1 + p.2.1) = p.1
              rw [map_add]
              have h1 := congrArg (fun m => m p.1) hρφ
              have h2 : ρ p.2.1 = 0 := p.2.2
              simp only [LinearMap.comp_apply,LinearMap.id_apply] at h1
              rw [h1,h2,add_zero]
            · apply Subtype.ext
              change (φ p.1 + p.2.1) - φ (ρ (φ p.1 + p.2.1)) = p.2.1
              rw [map_add]
              have h1 := congrArg (fun m => m p.1) hρφ
              have h2 : ρ p.2.1 = 0 := p.2.2
              simp only [LinearMap.comp_apply,LinearMap.id_apply] at h1
              rw [h1,h2,add_zero]
              abel
          map_add' := fun x y => by ext <;> simp
          map_smul' := fun a x => by ext <;> simp }
      have hcard_eq : Fintype.card W = Fintype.card (Pv u) * Fintype.card W' := by
        rw [Fintype.card_congr eW.toEquiv,Fintype.card_prod]
      have hcard_Pv : 2 ≤ Fintype.card (Pv u) := by
        have hne : (0 : Pv u) ≠ z67 u := (z329 u).symm
        exact Fintype.one_lt_card_iff.mpr ⟨0,z67 u,hne⟩
      have hcard_W'_pos : 0 < Fintype.card W' := Fintype.card_pos_iff.mpr ⟨0⟩
      have hcard_W' : Fintype.card W' ≤ n := by
        have : 2 * Fintype.card W' ≤ Fintype.card W := by
          rw [hcard_eq]
          exact Nat.mul_le_mul_right _ hcard_Pv
        omega
      have hri' : (projW'.comp r).comp (i.comp W'.subtype) = LinearMap.id := by
        ext ⟨x,hx⟩
        change (r (i x) - φ (ρ (r (i x)))) = x
        have h1 := congrArg (fun m => m x) hri
        simp only [LinearMap.comp_apply,LinearMap.id_apply] at h1
        rw [h1,hx,map_zero,sub_zero]
      obtain ⟨Z0,⟨eZ0⟩⟩ := z168 n hcard_W' (i.comp W'.subtype) (projW'.comp r) hri'
      refine ⟨FP.sum (PvObj u) Z0,⟨?_⟩⟩
      exact eW.trans ((LinearEquiv.prodCongr (z344 u) eZ0).trans
        (FP.sumEquivProd (PvObj u) Z0).symm)
lemma z229 {P : FP} {W : Type} [AddCommGroup W] [Module Λ W]
    (i : W →ₗ[Λ] P.Mod) (r : P.Mod →ₗ[Λ] W) (hri : r.comp i = LinearMap.id) :
    ∃ (Z : FP),Nonempty (W ≃ₗ[Λ] Z.Mod) := by
  have hi : Function.Injective i := Function.LeftInverse.injective
    (g := r) (fun x => congrArg (fun m => m x) hri)
  haveI : Finite W := Finite.of_injective i hi
  letI : Fintype W := Fintype.ofFinite W
  exact z168 (Fintype.card W) le_rfl i r hri
def ExactSys.u (S : ExactSys) (M : Type) [AddCommGroup M] [Module Λ M] [Finite M] :
    M →ₗ[Λ] M :=
  LinearMap.id + S.η M
lemma ExactSys.u_comp_u (S : ExactSys) (M : Type) [AddCommGroup M] [Module Λ M] [Finite M] :
    StableEq ((S.u M).comp (S.u M)) LinearMap.id := by
  have hcomp : (S.u M).comp (S.u M) = LinearMap.id + (S.η M).comp (S.η M) := by
    ext x
    change (x + S.η M x) + S.η M (x + S.η M x) = x + S.η M (S.η M x)
    rw [map_add]
    have h2 : S.η M x + S.η M x = 0 := z10 (S.η M x)
    calc (x + S.η M x) + (S.η M x + S.η M (S.η M x))
        = x + (S.η M x + S.η M x) + S.η M (S.η M x) := by abel
      _ = x + 0 + S.η M (S.η M x) := by rw [h2]
      _ = x + S.η M (S.η M x) := by abel
  rw [hcomp]
  simpa using StableEq.add (StableEq.refl (LinearMap.id : M →ₗ[Λ] M)) (S.η_sq_zero M)
lemma ExactSys.u_natural (S : ExactSys) {M N : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup N] [Module Λ N] [Finite N] (f : M →ₗ[Λ] N) :
    StableEq ((S.u N).comp f) (f.comp (S.u M)) := by
  have h1 : (S.u N).comp f = f + (S.η N).comp f := by ext x; simp [ExactSys.u]
  have h2 : f.comp (S.u M) = f + f.comp (S.η M) := by ext x; simp [ExactSys.u]
  rw [h1,h2]
  exact StableEq.add (StableEq.refl f) (S.η_natural f)
lemma ExactSys.u_nu (S : ExactSys) (M : Type) [AddCommGroup M] [Module Λ M] [Finite M] :
    StableEq (S.u (nuMod M)) (nuMap (S.u M)) := by
  have h1 : nuMap (S.u M) = LinearMap.id + nuMap (S.η M) := by
    rw [ExactSys.u,z359,z207]
  rw [ExactSys.u,h1]
  exact StableEq.add (StableEq.refl _) (S.η_nu M)
lemma ExactSys.u_syzygy (S : ExactSys) {M K : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    [AddCommGroup K] [Module Λ K] [Finite K] {P : FP}
    (j : M →ₗ[Λ] P.Mod) (q : P.Mod →ₗ[Λ] K)
    (hj : Function.Injective j) (hjq : ExactAt j q) (hq : Function.Surjective q) :
    ∃ τ : P ⟶ P,τ.hom.comp j = j.comp (S.u M) ∧ q.comp τ.hom = (S.u K).comp q := by
  obtain ⟨τ0,h1,h2⟩ := S.η_syzygy j q hj hjq hq
  refine ⟨𝟙 P + τ0,?_,?_⟩
  · apply LinearMap.ext; intro m
    have hm := congrArg (fun f => f m) h1
    simp only [FH.add_hom,FH.id_hom,LinearMap.comp_apply,LinearMap.add_apply,
      LinearMap.id_apply,ExactSys.u,map_add] at hm ⊢
    rw [hm]
  · apply LinearMap.ext; intro p
    have hp := congrArg (fun f => f p) h2
    simp only [FH.add_hom,FH.id_hom,LinearMap.comp_apply,LinearMap.add_apply,
      LinearMap.id_apply,ExactSys.u,map_add] at hp ⊢
    rw [hp]
lemma z72 (S : ExactSys)
    {M N M' N' : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    [AddCommGroup M'] [Module Λ M'] [AddCommGroup N'] [Module Λ N']
    {P0 P1 P2 Q0 Q1 Q2 : FP}
    {j : M →ₗ[Λ] P0.Mod} {d0 : P0 ⟶ P1} {d1 : P1 ⟶ P2} {π : P2.Mod →ₗ[Λ] N}
    {j' : M' →ₗ[Λ] Q0.Mod} {e0 : Q0 ⟶ Q1} {e1 : Q1 ⟶ Q2} {π' : Q2.Mod →ₗ[Λ] N'}
    (hj : Function.Injective j) (hex0 : ExactAt j d0.hom) (hex1 : ExactAt d0.hom d1.hom)
    (hex2 : ExactAt d1.hom π) (hπ : Function.Surjective π)
    (hex0' : ExactAt j' e0.hom) (hex1' : ExactAt e0.hom e1.hom) (hex2' : ExactAt e1.hom π')
    (g : M →ₗ[Λ] M') :
    ∃ (a0 : P0 ⟶ Q0) (a1 : P1 ⟶ Q1) (a2 : P2 ⟶ Q2) (c : N →ₗ[Λ] N'),
      a0.hom.comp j = j'.comp g ∧
      comp d0 a1 = comp a0 e0 ∧
      comp d1 a2 = comp a1 e1 ∧
      π'.comp a2.hom = c.comp π := by
  obtain ⟨a0h,ha0⟩ := S.inj Q0 j hj (j'.comp g)
  let a0 : P0 ⟶ Q0 := ⟨a0h⟩
  have hkill0 : (e0.hom.comp a0.hom).comp j = 0 := by
    rw [LinearMap.comp_assoc,ha0,← LinearMap.comp_assoc,hex0'.comp_eq_zero,LinearMap.zero_comp]
  obtain ⟨a1h,ha1⟩ := z32 S hex0 Q1 (e0.hom.comp a0.hom) hkill0
  let a1 : P1 ⟶ Q1 := ⟨a1h⟩
  have ha1' : comp d0 a1 = comp a0 e0 := FH.ext ha1
  have hkill1 : (e1.hom.comp a1.hom).comp d0.hom = 0 := by
    rw [LinearMap.comp_assoc,ha1,← LinearMap.comp_assoc,hex1'.comp_eq_zero,LinearMap.zero_comp]
  obtain ⟨a2h,ha2⟩ := z32 S hex1 Q2 (e1.hom.comp a1.hom) hkill1
  let a2 : P2 ⟶ Q2 := ⟨a2h⟩
  have ha2' : comp d1 a2 = comp a1 e1 := FH.ext ha2
  have hkill2 : (π'.comp a2.hom).comp d1.hom = 0 := by
    rw [LinearMap.comp_assoc,ha2,← LinearMap.comp_assoc,hex2'.comp_eq_zero,LinearMap.zero_comp]
  obtain ⟨c,hc⟩ := z21 hex2 hπ (π'.comp a2.hom) hkill2
  exact ⟨a0,a1,a2,c,ha0,ha1',ha2',hc.symm⟩
lemma z34 (S : ExactSys)
    {M N M' N' : Type} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    [AddCommGroup M'] [Module Λ M'] [AddCommGroup N'] [Module Λ N']
    {P0 P1 P2 Q0 Q1 Q2 : FP}
    {j : M →ₗ[Λ] P0.Mod} {d0 : P0 ⟶ P1} {d1 : P1 ⟶ P2} {π : P2.Mod →ₗ[Λ] N}
    {j' : M' →ₗ[Λ] Q0.Mod} {e0 : Q0 ⟶ Q1} {e1 : Q1 ⟶ Q2} {π' : Q2.Mod →ₗ[Λ] N'}
    (hj : Function.Injective j) (hex0 : ExactAt j d0.hom) (hex1 : ExactAt d0.hom d1.hom)
    (hex2 : ExactAt d1.hom π) (hπ : Function.Surjective π)
    (hex0' : ExactAt j' e0.hom) (hex1' : ExactAt e0.hom e1.hom) (hex2' : ExactAt e1.hom π')
    {g g' : M →ₗ[Λ] M'}
    {a0 b0 : P0 ⟶ Q0} {a1 b1 : P1 ⟶ Q1} {a2 b2 : P2 ⟶ Q2} {c c' : N →ₗ[Λ] N'}
    (ha0 : a0.hom.comp j = j'.comp g)
    (ha1 : comp d0 a1 = comp a0 e0)
    (ha2 : comp d1 a2 = comp a1 e1)
    (hac : π'.comp a2.hom = c.comp π)
    (hb0 : b0.hom.comp j = j'.comp g')
    (hb1 : comp d0 b1 = comp b0 e0)
    (hb2 : comp d1 b2 = comp b1 e1)
    (hbc : π'.comp b2.hom = c'.comp π)
    (hg : StableEq g g') :
    StableEq c c' := by
  obtain ⟨Q,p,q,hpq⟩ := hg
  obtain ⟨ptilde,hptilde⟩ := S.inj Q j hj p
  let δ0 : P0.Mod →ₗ[Λ] Q0.Mod := (a0.hom - b0.hom) - (j'.comp q).comp ptilde
  have hδ0 : δ0.comp j = 0 := by
    apply LinearMap.ext; intro m
    have h1 := congrArg (fun f => f m) ha0
    have h2 := congrArg (fun f => f m) hb0
    have h3 := congrArg (fun f => f m) hpq
    have h4 := congrArg (fun f => f m) hptilde
    simp only [δ0,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.zero_apply] at h1 h2 h3 h4 ⊢
    rw [h1,h2,h4,← map_sub,h3,sub_self]
  obtain ⟨h0,hh0⟩ := z32 S hex0 Q0 δ0 hδ0
  let δ1 : P1.Mod →ₗ[Λ] Q1.Mod := (a1.hom - b1.hom) - e0.hom.comp h0
  have hδ1 : δ1.comp d0.hom = 0 := by
    apply LinearMap.ext; intro x
    have h1 := congrArg (fun (f : P0 ⟶ Q1) => f.hom x) ha1
    have h2 := congrArg (fun (f : P0 ⟶ Q1) => f.hom x) hb1
    have h3 := congrArg (fun f => f x) hh0
    have h4 := congrArg (fun f => f (q (ptilde x))) hex0'.comp_eq_zero
    simp only [δ1,δ0,FH.comp_hom,LinearMap.comp_apply,LinearMap.sub_apply,
      LinearMap.zero_apply] at h1 h2 h3 h4 ⊢
    rw [h1,h2,h3,map_sub,map_sub,h4,sub_zero,sub_self]
  obtain ⟨h1,hh1⟩ := z32 S hex1 Q1 δ1 hδ1
  let δ2 : P2.Mod →ₗ[Λ] Q2.Mod := (a2.hom - b2.hom) - e1.hom.comp h1
  have hδ2 : δ2.comp d1.hom = 0 := by
    apply LinearMap.ext; intro y
    have h1' := congrArg (fun (f : P1 ⟶ Q2) => f.hom y) ha2
    have h2' := congrArg (fun (f : P1 ⟶ Q2) => f.hom y) hb2
    have h3' := congrArg (fun f => f y) hh1
    have h4' := congrArg (fun f => f (h0 y)) hex1'.comp_eq_zero
    simp only [δ2,δ1,FH.comp_hom,LinearMap.comp_apply,LinearMap.sub_apply,
      LinearMap.zero_apply] at h1' h2' h3' h4' ⊢
    rw [h1',h2',h3',map_sub,map_sub,h4',sub_zero,sub_self]
  obtain ⟨h2,hh2⟩ := z21 hex2 hπ δ2 hδ2
  refine ⟨Q2,h2,π',LinearMap.ext fun n => ?_⟩
  obtain ⟨z,rfl⟩ := hπ n
  have h1' := congrArg (fun f => f z) hac
  have h2' := congrArg (fun f => f z) hbc
  have h3' := congrArg (fun f => f z) hh2
  have h4' := congrArg (fun f => f (h1 z)) hex2'.comp_eq_zero
  simp only [δ2,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.zero_apply] at h1' h2' h3' h4' ⊢
  rw [← h1',← h2',h3',map_sub,map_sub,h4',sub_zero]
end Mod2Helpers
def IsDeltaExact (S : ExactSys) (T : Triangle FP) : Prop :=
  ∃ (M : Type) (_ : AddCommGroup M) (_ : Module Λ M) (_ : Finite M)
    (j : M →ₗ[Λ] T.obj₁.Mod) (hbar : T.obj₃.Mod →ₗ[Λ] nuMod M)
    (a0 : T.obj₁ ⟶ (S.seq M).P0) (a1 : T.obj₂ ⟶ (S.seq M).P1) (a2 : T.obj₃ ⟶ (S.seq M).P2)
    (c : nuMod M →ₗ[Λ] nuMod M),
    Function.Injective j ∧
    ExactAt j T.mor₁.hom ∧
    ExactAt T.mor₁.hom T.mor₂.hom ∧
    ExactAt T.mor₂.hom hbar ∧
    Function.Surjective hbar ∧
    T.mor₃.hom = ((z3 T.obj₁).toLinearMap.comp (nuMap j)).comp hbar ∧
    a0.hom.comp j = (S.seq M).ι ∧
    comp T.mor₁ a1 = comp a0 (S.seq M).d0 ∧
    comp T.mor₂ a2 = comp a1 (S.seq M).d1 ∧
    (S.seq M).π.comp a2.hom = c.comp hbar ∧
    StableEq c (nuMap (S.u M))
lemma IsDeltaExact.stableEq_comparison (S : ExactSys) {T : Triangle FP}
    (hT : IsDeltaExact S T)
    {M : Type} [AddCommGroup M] [Module Λ M] [Finite M]
    {j : M →ₗ[Λ] T.obj₁.Mod} {hbar : T.obj₃.Mod →ₗ[Λ] nuMod M}
    (hj : Function.Injective j)
    (hex0 : ExactAt j T.mor₁.hom) (hex1 : ExactAt T.mor₁.hom T.mor₂.hom)
    (hex2 : ExactAt T.mor₂.hom hbar) (hhbar : Function.Surjective hbar)
    (hmor3 : T.mor₃.hom = ((z3 T.obj₁).toLinearMap.comp (nuMap j)).comp hbar)
    {b0 : T.obj₁ ⟶ (S.seq M).P0} {b1 : T.obj₂ ⟶ (S.seq M).P1} {b2 : T.obj₃ ⟶ (S.seq M).P2}
    {c' : nuMod M →ₗ[Λ] nuMod M}
    (hb0 : b0.hom.comp j = (S.seq M).ι)
    (hb1 : comp T.mor₁ b1 = comp b0 (S.seq M).d0)
    (hb2 : comp T.mor₂ b2 = comp b1 (S.seq M).d1)
    (hc' : (S.seq M).π.comp b2.hom = c'.comp hbar) :
    StableEq c' (nuMap (S.u M)) := by
  rcases hT with ⟨M',_,_,_,j',hbar',a0',a1',a2',cw,
    hj',hex0',hex1',hex2',hhbar',hmor3',ha0',ha1',ha2',hcw,hstab⟩
  let e : M ≃ₗ[Λ] M' :=
    (LinearEquiv.ofInjective j hj).trans
      ((LinearEquiv.ofEq _ _ (hex0.trans hex0'.symm)).trans
        (LinearEquiv.ofInjective j' hj').symm)
  have hje : j'.comp e.toLinearMap = j := by
    apply LinearMap.ext; intro m
    have h1 : j' (e m) = ((LinearEquiv.ofInjective j' hj') (e m)).1 := rfl
    rw [LinearMap.comp_apply,LinearEquiv.coe_coe,h1]
    simp [e]
  have hhbar_eq : hbar' = (nuMap e.toLinearMap).comp hbar := by
    apply LinearMap.ext; intro z
    have hinj : Function.Injective ((z3 T.obj₁).toLinearMap.comp (nuMap j')) :=
      (z3 T.obj₁).injective.comp (z61 hj')
    apply hinj
    have h1 : T.mor₃.hom z = (z3 T.obj₁) (nuMap j' (hbar' z)) :=
      congrArg (fun f => f z) hmor3'
    have h2 : T.mor₃.hom z = (z3 T.obj₁) (nuMap j (hbar z)) :=
      congrArg (fun f => f z) hmor3
    change (z3 T.obj₁) (nuMap j' (hbar' z)) =
      (z3 T.obj₁) (nuMap j' ((nuMap e.toLinearMap) (hbar z)))
    rw [← h1,h2]
    congr 1
    change (nuMap j) (hbar z) = ((nuMap j').comp (nuMap e.toLinearMap)) (hbar z)
    rw [← z83,hje]
  let a0'' : T.obj₁ ⟶ (S.seq M).P0 := comp a0' (S.map0 e.symm.toLinearMap)
  let a1'' : T.obj₂ ⟶ (S.seq M).P1 := comp a1' (S.map1 e.symm.toLinearMap)
  let a2'' : T.obj₃ ⟶ (S.seq M).P2 := comp a2' (S.map2 e.symm.toLinearMap)
  let c'' : nuMod M →ₗ[Λ] nuMod M :=
    (nuMap e.symm.toLinearMap).comp (cw.comp (nuMap e.toLinearMap))
  have ha0'' : a0''.hom.comp j = (S.seq M).ι.comp LinearMap.id := by
    apply LinearMap.ext; intro m
    have h1 := congrArg (fun f => f m) hje
    have h2 := congrArg (fun f => f (e m)) ha0'
    have h3 := congrArg (fun f => f (e m)) (S.map0_ι e.symm.toLinearMap)
    simp only [a0'',FH.comp_hom,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearMap.id_apply] at h1 h2 h3 ⊢
    rw [← h1,h2,h3,e.symm_apply_apply]
  have ha1'' : comp T.mor₁ a1'' = comp a0'' (S.seq M).d0 := by
    dsimp [a0'',a1'']
    rw [← Category.assoc,ha1',Category.assoc,S.map1_d0,← Category.assoc]
  have ha2'' : comp T.mor₂ a2'' = comp a1'' (S.seq M).d1 := by
    dsimp [a1'',a2'']
    rw [← Category.assoc,ha2',Category.assoc,S.map2_d1,← Category.assoc]
  have hc'' : (S.seq M).π.comp a2''.hom = c''.comp hbar := by
    apply LinearMap.ext; intro z
    have h1 := congrArg (fun f => f (a2'.hom z)) (S.π_map2 e.symm.toLinearMap)
    have h2 := congrArg (fun f => f z) hcw
    have h3 := congrArg (fun f => f z) hhbar_eq
    simp only [a2'',c'',FH.comp_hom,LinearMap.comp_apply] at h1 h2 h3 ⊢
    rw [h1,h2,h3]
  have hcomp : StableEq c' c'' :=
    z34 S hj hex0 hex1 hex2 hhbar
      (S.seq M).exact0 (S.seq M).exact1 (S.seq M).exact2
      (by simpa using hb0) hb1 hb2 hc' ha0'' ha1'' ha2'' hc'' (StableEq.refl _)
  have h1 : StableEq c''
      ((nuMap e.symm.toLinearMap).comp ((nuMap (S.u M')).comp (nuMap e.toLinearMap))) :=
    (hstab.comp_right _).comp_left _
  have h2 : (nuMap e.symm.toLinearMap).comp ((nuMap (S.u M')).comp (nuMap e.toLinearMap)) =
      nuMap (e.symm.toLinearMap.comp ((S.u M').comp e.toLinearMap)) := by
    rw [← z83,← z83]
  have h3 : StableEq (e.symm.toLinearMap.comp ((S.u M').comp e.toLinearMap))
      (e.symm.toLinearMap.comp (e.toLinearMap.comp (S.u M))) :=
    (S.u_natural e.toLinearMap).comp_left _
  have h4 : e.symm.toLinearMap.comp (e.toLinearMap.comp (S.u M)) = S.u M := by
    apply LinearMap.ext; intro m; simp
  rw [h4] at h3
  exact hcomp.trans (h1.trans (by rw [h2]; exact h3.nuMap))
lemma IsDeltaExact.isomorphic (S : ExactSys) {T₁ T₂ : Triangle FP}
    (hT₁ : IsDeltaExact S T₁) (e : T₂ ≅ T₁) : IsDeltaExact S T₂ := by
  rcases hT₁ with ⟨M,_,_,_,j,hbar,a0,a1,a2,c,
    hj,hex0,hex1,hex2,hhbar,hmor3,ha0,ha1,ha2,hc,hstab⟩
  let e1 : T₂.obj₁.Mod ≃ₗ[Λ] T₁.obj₁.Mod :=
    { toFun := e.hom.hom₁.hom
      invFun := e.inv.hom₁.hom
      left_inv := fun x => congrArg (fun (f : T₂.obj₁ ⟶ T₂.obj₁) => f.hom x)
        (Iso.hom_inv_id_triangle_hom₁ e)
      right_inv := fun x => congrArg (fun (f : T₁.obj₁ ⟶ T₁.obj₁) => f.hom x)
        (Iso.inv_hom_id_triangle_hom₁ e)
      map_add' := e.hom.hom₁.hom.map_add
      map_smul' := e.hom.hom₁.hom.map_smul }
  let e2 : T₂.obj₂.Mod ≃ₗ[Λ] T₁.obj₂.Mod :=
    { toFun := e.hom.hom₂.hom
      invFun := e.inv.hom₂.hom
      left_inv := fun x => congrArg (fun (f : T₂.obj₂ ⟶ T₂.obj₂) => f.hom x)
        (Iso.hom_inv_id_triangle_hom₂ e)
      right_inv := fun x => congrArg (fun (f : T₁.obj₂ ⟶ T₁.obj₂) => f.hom x)
        (Iso.inv_hom_id_triangle_hom₂ e)
      map_add' := e.hom.hom₂.hom.map_add
      map_smul' := e.hom.hom₂.hom.map_smul }
  let e3 : T₂.obj₃.Mod ≃ₗ[Λ] T₁.obj₃.Mod :=
    { toFun := e.hom.hom₃.hom
      invFun := e.inv.hom₃.hom
      left_inv := fun x => congrArg (fun (f : T₂.obj₃ ⟶ T₂.obj₃) => f.hom x)
        (Iso.hom_inv_id_triangle_hom₃ e)
      right_inv := fun x => congrArg (fun (f : T₁.obj₃ ⟶ T₁.obj₃) => f.hom x)
        (Iso.inv_hom_id_triangle_hom₃ e)
      map_add' := e.hom.hom₃.hom.map_add
      map_smul' := e.hom.hom₃.hom.map_smul }
  let j2 : M →ₗ[Λ] T₂.obj₁.Mod := e1.symm.toLinearMap.comp j
  let hbar2 : T₂.obj₃.Mod →ₗ[Λ] nuMod M := hbar.comp e3.toLinearMap
  refine ⟨M,inferInstance,inferInstance,inferInstance,
    j2,hbar2,
    comp e.hom.hom₁ a0,
    comp e.hom.hom₂ a1,
    comp e.hom.hom₃ a2,
    c,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hstab⟩
  · exact e1.symm.injective.comp hj
  · have hmor1 : T₂.mor₁.hom = e2.symm.toLinearMap.comp (T₁.mor₁.hom.comp e1.toLinearMap) := by
      apply LinearMap.ext; intro x
      have h1 := congrArg (fun (f : T₂.obj₁ ⟶ T₁.obj₂) => e.inv.hom₂.hom (f.hom x)) e.hom.comm₁
      have h2 := congrArg (fun (f : T₂.obj₂ ⟶ T₂.obj₂) => f.hom (T₂.mor₁.hom x))
        (Iso.hom_inv_id_triangle_hom₂ e)
      simp only [FH.comp_hom,FH.id_hom,LinearMap.comp_apply,LinearMap.id_apply] at h1 h2
      exact h2.symm.trans h1
    rw [hmor1]
    exact (hex0.of_equiv_mid e1.symm).of_comp_inj e2.symm.injective
  · have hmor1 : T₂.mor₁.hom = e2.symm.toLinearMap.comp (T₁.mor₁.hom.comp e1.toLinearMap) := by
      apply LinearMap.ext; intro x
      have h1 := congrArg (fun (f : T₂.obj₁ ⟶ T₁.obj₂) => e.inv.hom₂.hom (f.hom x)) e.hom.comm₁
      have h2 := congrArg (fun (f : T₂.obj₂ ⟶ T₂.obj₂) => f.hom (T₂.mor₁.hom x))
        (Iso.hom_inv_id_triangle_hom₂ e)
      simp only [FH.comp_hom,FH.id_hom,LinearMap.comp_apply,LinearMap.id_apply] at h1 h2
      exact h2.symm.trans h1
    have hmor2 : T₂.mor₂.hom = e3.symm.toLinearMap.comp (T₁.mor₂.hom.comp e2.toLinearMap) := by
      apply LinearMap.ext; intro x
      have h1 := congrArg (fun (f : T₂.obj₂ ⟶ T₁.obj₃) => e.inv.hom₃.hom (f.hom x)) e.hom.comm₂
      have h2 := congrArg (fun (f : T₂.obj₃ ⟶ T₂.obj₃) => f.hom (T₂.mor₂.hom x))
        (Iso.hom_inv_id_triangle_hom₃ e)
      simp only [FH.comp_hom,FH.id_hom,LinearMap.comp_apply,LinearMap.id_apply] at h1 h2
      exact h2.symm.trans h1
    rw [hmor1,hmor2]
    exact ((hex1.of_comp_surj e1.surjective).of_equiv_mid e2.symm).of_comp_inj e3.symm.injective
  · have hmor2 : T₂.mor₂.hom = e3.symm.toLinearMap.comp (T₁.mor₂.hom.comp e2.toLinearMap) := by
      apply LinearMap.ext; intro x
      have h1 := congrArg (fun (f : T₂.obj₂ ⟶ T₁.obj₃) => e.inv.hom₃.hom (f.hom x)) e.hom.comm₂
      have h2 := congrArg (fun (f : T₂.obj₃ ⟶ T₂.obj₃) => f.hom (T₂.mor₂.hom x))
        (Iso.hom_inv_id_triangle_hom₃ e)
      simp only [FH.comp_hom,FH.id_hom,LinearMap.comp_apply,LinearMap.id_apply] at h1 h2
      exact h2.symm.trans h1
    rw [hmor2]
    exact (hex2.of_comp_surj e2.surjective).of_equiv_mid e3.symm
  · exact hhbar.comp e3.surjective
  · apply LinearMap.ext; intro z
    have h3 : T₂.mor₃ = comp e.hom.hom₃
        (comp T₁.mor₃ (e.inv.hom₁⟦(1 : ℤ)⟧')) := by
      rw [← Category.assoc,← e.hom.comm₃,Category.assoc,← CategoryTheory.Functor.map_comp,
        Iso.hom_inv_id_triangle_hom₁,CategoryTheory.Functor.map_id,Category.comp_id]
    have h3z := congrArg (fun (f : T₂.obj₃ ⟶ T₂.obj₁⟦(1 : ℤ)⟧) => f.hom z) h3
    change T₂.mor₃.hom z = z3 T₂.obj₁ (nuMap j2 (hbar2 z))
    rw [h3z]
    change (e.inv.hom₁⟦(1 : ℤ)⟧').hom (T₁.mor₃.hom (e.hom.hom₃.hom z)) =
      z3 T₂.obj₁ (nuMap j2 (hbar2 z))
    have hm : T₁.mor₃.hom (e.hom.hom₃.hom z) =
        z3 T₁.obj₁ (nuMap j (hbar (e.hom.hom₃.hom z))) :=
      congrArg (fun f => f (e.hom.hom₃.hom z)) hmor3
    rw [hm,← z5 e.inv.hom₁]
    rfl
  · apply LinearMap.ext; intro m
    have h1 := congrArg (fun f => f m) ha0
    have h2 := congrArg (fun (f : T₁.obj₁ ⟶ T₁.obj₁) => f.hom (j m))
      (Iso.inv_hom_id_triangle_hom₁ e)
    simp only [j2,e1,FH.comp_hom,FH.id_hom,LinearMap.comp_apply,
      LinearMap.id_apply] at h1 h2 ⊢
    change a0.hom (e.hom.hom₁.hom (e.inv.hom₁.hom (j m))) = (S.seq M).ι m
    rw [h2,h1]
  · rw [← Category.assoc,e.hom.comm₁,Category.assoc,ha1,← Category.assoc]
  · rw [← Category.assoc,e.hom.comm₂,Category.assoc,ha2,← Category.assoc]
  · apply LinearMap.ext; intro z
    have h1 := congrArg (fun f => f (e.hom.hom₃.hom z)) hc
    exact h1
lemma IsDeltaExact.contractible (S : ExactSys) (X : FP) :
    IsDeltaExact S (contractibleTriangle X) := by
  let M : Type := FP.zero.Mod
  have hM0 : ∀ m : M,m = 0 := fun m => by funext v k; exact Fin.elim0 k
  have hnuM0 : ∀ m : nuMod M,m = 0 := fun m => nuMod.ext (hM0 m.val)
  have hZ0 : ∀ z : (contractibleTriangle X).obj₃.Mod,z = 0 :=
    FP.isZero_mod_eq_zero (Limits.isZero_zero FP)
  refine ⟨M,inferInstance,inferInstance,inferInstance,
    0,0,0,0,0,0,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x y _; exact (hM0 x).trans (hM0 y).symm
  · rw [z7]; intro y
    simp only [contractibleTriangle_mor₁,FH.id_hom,LinearMap.zero_apply]
    exact ⟨fun hy => ⟨0,hy.symm⟩,fun ⟨_,hx⟩ => hx.symm⟩
  · rw [z7]; intro y
    simp only [contractibleTriangle_mor₁,contractibleTriangle_mor₂,FH.id_hom,
      FH.zero_hom]
    exact ⟨fun _ => ⟨y,rfl⟩,fun _ => rfl⟩
  · rw [z7]; intro z
    simp only [contractibleTriangle_mor₂,FH.zero_hom,LinearMap.zero_apply]
    exact ⟨fun _ => ⟨0,(hZ0 z).symm⟩,fun _ => trivial⟩
  · intro m; exact ⟨0,(hnuM0 m).symm⟩
  · apply LinearMap.ext; intro z
    change (0 : (contractibleTriangle X).obj₃ ⟶ X⟦(1 : ℤ)⟧).hom z = 0
    rfl
  · apply LinearMap.ext; intro m
    rw [hM0 m]; simp
  · simp only [Limits.comp_zero,Limits.zero_comp]
  · simp only [Limits.comp_zero,Limits.zero_comp]
  · apply LinearMap.ext; intro z; simp
  · have heq : (0 : nuMod M →ₗ[Λ] nuMod M) = nuMap (S.u M) := by
      apply LinearMap.ext; intro m; exact (hnuM0 _).symm
    rw [heq]; exact StableEq.refl _
lemma IsDeltaExact.cocone (S : ExactSys) {X Y : FP} (f : X ⟶ Y) :
    ∃ (Z : FP) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      IsDeltaExact S (Triangle.mk f g h) := by
  let M : Type := LinearMap.ker f.hom
  let j : M →ₗ[Λ] X.Mod := (LinearMap.ker f.hom).subtype
  have hj : Function.Injective j := Subtype.val_injective
  have hex0 : ExactAt j f.hom := by
    rw [z7]; intro x
    exact ⟨fun hx => ⟨⟨x,hx⟩,rfl⟩,fun ⟨⟨_,hm⟩,hx⟩ => hx ▸ hm⟩
  let C : Type := Y.Mod ⧸ LinearMap.range f.hom
  have : Finite C := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  let pC : Y.Mod →ₗ[Λ] C := (LinearMap.range f.hom).mkQ
  have hpC_surj : Function.Surjective pC := Submodule.mkQ_surjective _
  have hex_f_pC : ExactAt f.hom pC := by
    rw [z7]; intro y
    change (LinearMap.range f.hom).mkQ y = 0 ↔ ∃ x,f.hom x = y
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,LinearMap.mem_range]
  obtain ⟨Q1,iC,hiC⟩ := S.exists_embed C
  let g1 : Y ⟶ Q1 := ⟨iC.comp pC⟩
  have hex_f_g1 : ExactAt f.hom g1.hom := hex_f_pC.of_comp_inj hiC
  let D1 : Type := Q1.Mod ⧸ LinearMap.range g1.hom
  let q1 : Q1.Mod →ₗ[Λ] D1 := (LinearMap.range g1.hom).mkQ
  have hq1_surj : Function.Surjective q1 := Submodule.mkQ_surjective _
  have hex_g1_q1 : ExactAt g1.hom q1 := by
    rw [z7]; intro z
    change (LinearMap.range g1.hom).mkQ z = 0 ↔ ∃ x,g1.hom x = z
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,LinearMap.mem_range]
  obtain ⟨a0,a1,a2,c,ha0,ha1,ha2,hc⟩ :=
    z72 S hj hex0 hex_f_g1 hex_g1_q1 hq1_surj
      (S.seq M).exact0 (S.seq M).exact1 (S.seq M).exact2 LinearMap.id
  obtain ⟨b0,b1,b2,d,hb0,hb1,hb2,hd⟩ :=
    z72 S (S.seq M).ι_inj (S.seq M).exact0 (S.seq M).exact1
      (S.seq M).exact2 (S.seq M).π_surj hex0 hex_f_g1 hex_g1_q1 LinearMap.id
  have hcd : StableEq (c.comp d) LinearMap.id := by
    refine z34 S (S.seq M).ι_inj (S.seq M).exact0 (S.seq M).exact1
      (S.seq M).exact2 (S.seq M).π_surj (S.seq M).exact0 (S.seq M).exact1 (S.seq M).exact2
      (g := LinearMap.id) (g' := LinearMap.id)
      (a0 := comp b0 a0) (a1 := comp b1 a1)
      (a2 := comp b2 a2) (c := c.comp d)
      (b0 := 𝟙 _) (b1 := 𝟙 _) (b2 := 𝟙 _) (c' := LinearMap.id)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (StableEq.refl _)
    · rw [FH.comp_hom,LinearMap.comp_assoc,hb0,LinearMap.comp_id,ha0]
    · rw [← Category.assoc,hb1,Category.assoc,ha1,← Category.assoc]
    · rw [← Category.assoc,hb2,Category.assoc,ha2,← Category.assoc]
    · rw [FH.comp_hom,← LinearMap.comp_assoc,hc,LinearMap.comp_assoc,hd,
        ← LinearMap.comp_assoc]
    · simp
    · simp
    · simp
    · simp
  have hdc : StableEq (d.comp c) LinearMap.id := by
    refine z34 S hj hex0 hex_f_g1 hex_g1_q1 hq1_surj
      hex0 hex_f_g1 hex_g1_q1
      (g := LinearMap.id) (g' := LinearMap.id)
      (a0 := comp a0 b0) (a1 := comp a1 b1)
      (a2 := comp a2 b2) (c := d.comp c)
      (b0 := 𝟙 _) (b1 := 𝟙 _) (b2 := 𝟙 _) (c' := LinearMap.id)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (StableEq.refl _)
    · rw [FH.comp_hom,LinearMap.comp_assoc,ha0,LinearMap.comp_id,hb0]
    · rw [← Category.assoc,ha1,Category.assoc,hb1,← Category.assoc]
    · rw [← Category.assoc,ha2,Category.assoc,hb2,← Category.assoc]
    · rw [FH.comp_hom,← LinearMap.comp_assoc,hd,LinearMap.comp_assoc,hc,
        ← LinearMap.comp_assoc]
    · simp
    · simp
    · simp
    · simp
  let cu : D1 →ₗ[Λ] nuMod M := (nuMap (S.u M)).comp c
  let du : nuMod M →ₗ[Λ] D1 := d.comp (nuMap (S.u M))
  have hnu_uu : StableEq ((nuMap (S.u M)).comp (nuMap (S.u M))) LinearMap.id := by
    rw [← z83,← z207]
    exact (S.u_comp_u M).nuMap
  have hcudu : StableEq (cu.comp du) LinearMap.id := by
    have h1 : cu.comp du = (nuMap (S.u M)).comp ((c.comp d).comp (nuMap (S.u M))) := by
      ext x; rfl
    rw [h1]
    exact (((hcd.comp_right _).comp_left _).trans (by
      simpa using hnu_uu))
  have hducu : StableEq (du.comp cu) LinearMap.id := by
    have h1 : du.comp cu = d.comp (((nuMap (S.u M)).comp (nuMap (S.u M))).comp c) := by
      ext x; rfl
    rw [h1]
    exact (((hnu_uu.comp_right _).comp_left _).trans (by
      simpa using hdc))
  have ⟨R1,p1,r1,hr1p1⟩ := hcudu
  have ⟨R2,p2,r2,hr2p2⟩ := hducu
  have hr1_eq : cu.comp du + r1.comp p1 = LinearMap.id := by
    have h := hr1p1
    rw [z154] at h
    calc cu.comp du + r1.comp p1 = cu.comp du + (cu.comp du + LinearMap.id) := by rw [← h]
      _ = (cu.comp du + cu.comp du) + LinearMap.id := by abel
      _ = 0 + LinearMap.id := by rw [z99]
      _ = LinearMap.id := zero_add _
  have hr2_eq : du.comp cu + r2.comp p2 = LinearMap.id := by
    have h := hr2p2
    rw [z154] at h
    calc du.comp cu + r2.comp p2 = du.comp cu + (du.comp cu + LinearMap.id) := by rw [← h]
      _ = (du.comp cu + du.comp cu) + LinearMap.id := by abel
      _ = 0 + LinearMap.id := by rw [z99]
      _ = LinearMap.id := zero_add _
  let Qbig : FP := FP.sum Q1 R1
  let gbig : Y ⟶ Qbig := comp g1 (FP.inl Q1 R1)
  let ψD : D1 × R1.Mod →ₗ[Λ] nuMod M :=
    cu.comp (LinearMap.fst Λ D1 R1.Mod) + r1.comp (LinearMap.snd Λ D1 R1.Mod)
  let qbig : Qbig.Mod →ₗ[Λ] D1 × R1.Mod :=
    (q1.comp (FP.fst Q1 R1).hom).prod (FP.snd Q1 R1).hom
  let hbar_big : Qbig.Mod →ₗ[Λ] nuMod M := ψD.comp qbig
  have hqbig_surj : Function.Surjective qbig := by
    rintro ⟨d1,r⟩
    obtain ⟨x,rfl⟩ := hq1_surj d1
    refine ⟨(FP.inl Q1 R1).hom x + (FP.inr Q1 R1).hom r,?_⟩
    have h1 := congrArg (fun (m : Q1 ⟶ Q1) => m.hom x) (FP.inl_fst Q1 R1)
    have h2 := congrArg (fun (m : R1 ⟶ Q1) => m.hom r) (FP.inr_fst Q1 R1)
    have h3 := congrArg (fun (m : Q1 ⟶ R1) => m.hom x) (FP.inl_snd Q1 R1)
    have h4 := congrArg (fun (m : R1 ⟶ R1) => m.hom r) (FP.inr_snd Q1 R1)
    simp only [FH.comp_hom,FH.id_hom,FH.zero_hom,LinearMap.comp_apply,
      LinearMap.id_apply,LinearMap.zero_apply] at h1 h2 h3 h4
    ext : 1
    · change q1 ((FP.fst Q1 R1).hom ((FP.inl Q1 R1).hom x + (FP.inr Q1 R1).hom r)) = q1 x
      rw [map_add,h1,h2,add_zero]
    · change (FP.snd Q1 R1).hom ((FP.inl Q1 R1).hom x + (FP.inr Q1 R1).hom r) = r
      rw [map_add,h3,h4,zero_add]
  have hex_gbig_qbig : ExactAt gbig.hom qbig := by
    rw [z7]; intro z
    constructor
    · intro hz
      have hz1 : q1 ((FP.fst Q1 R1).hom z) = 0 := congrArg Prod.fst hz
      have hz2 : (FP.snd Q1 R1).hom z = 0 := congrArg Prod.snd hz
      obtain ⟨y,hy⟩ := ((z7 g1.hom q1).mp hex_g1_q1 _).mp hz1
      refine ⟨y,?_⟩
      apply (FP.sumEquivProd Q1 R1).injective
      ext : 1
      · change (FP.fst Q1 R1).hom ((FP.inl Q1 R1).hom (g1.hom y)) = (FP.fst Q1 R1).hom z
        have h1 := congrArg (fun (m : Q1 ⟶ Q1) => m.hom (g1.hom y)) (FP.inl_fst Q1 R1)
        simpa [hy] using h1
      · change (FP.snd Q1 R1).hom ((FP.inl Q1 R1).hom (g1.hom y)) = (FP.snd Q1 R1).hom z
        have h2 := congrArg (fun (m : Q1 ⟶ R1) => m.hom (g1.hom y)) (FP.inl_snd Q1 R1)
        simpa [hz2] using h2
    · rintro ⟨y,rfl⟩
      ext : 1
      · change q1 ((FP.fst Q1 R1).hom ((FP.inl Q1 R1).hom (g1.hom y))) = 0
        have h1 := congrArg (fun (m : Q1 ⟶ Q1) => m.hom (g1.hom y)) (FP.inl_fst Q1 R1)
        simp only [FH.comp_hom,FH.id_hom,LinearMap.comp_apply,LinearMap.id_apply] at h1
        rw [h1]
        exact congrArg (fun m => m y) hex_g1_q1.comp_eq_zero
      · change (FP.snd Q1 R1).hom ((FP.inl Q1 R1).hom (g1.hom y)) = 0
        have h2 := congrArg (fun (m : Q1 ⟶ R1) => m.hom (g1.hom y)) (FP.inl_snd Q1 R1)
        simpa using h2
  let σD : nuMod M →ₗ[Λ] D1 × R1.Mod := du.prod p1
  have hψD_σD : ψD.comp σD = LinearMap.id := by
    apply LinearMap.ext; intro m
    have h1 := congrArg (fun f => f m) hr1_eq
    simpa [ψD,σD] using h1
  have hhbar_big_surj : Function.Surjective hbar_big := by
    have hψD_surj : Function.Surjective ψD :=
      Function.RightInverse.surjective (fun m => congrArg (fun f => f m) hψD_σD)
    exact hψD_surj.comp hqbig_surj
  let KD := LinearMap.ker ψD
  let πK : D1 × R1.Mod →ₗ[Λ] KD :=
    { toFun := fun p => ⟨p + σD (ψD p),by
        change ψD (p + σD (ψD p)) = 0
        rw [map_add]
        have h1 := congrArg (fun m => m (ψD p)) hψD_σD
        simp only [LinearMap.comp_apply,LinearMap.id_apply] at h1
        rw [h1,z10]⟩
      map_add' := fun p q => by ext <;> simp <;> abel
      map_smul' := fun a p => by ext <;> simp [smul_add] }
  let αK : KD →ₗ[Λ] (FP.sum R1 R2).Mod :=
    (FP.inl R1 R2).hom.comp ((LinearMap.snd Λ D1 R1.Mod).comp KD.subtype) +
    (FP.inr R1 R2).hom.comp (p2.comp ((LinearMap.fst Λ D1 R1.Mod).comp KD.subtype))
  let β0 : (FP.sum R1 R2).Mod →ₗ[Λ] D1 × R1.Mod :=
    ((du.comp r1).comp (FP.fst R1 R2).hom + r2.comp (FP.snd R1 R2).hom).prod
      (FP.fst R1 R2).hom
  let βK : (FP.sum R1 R2).Mod →ₗ[Λ] KD := πK.comp β0
  have hβα : βK.comp αK = LinearMap.id := by
    apply LinearMap.ext; rintro ⟨⟨x,y⟩,hxy⟩
    have hxy' : cu x + r1 y = 0 := hxy
    have hcu_eq : cu x = r1 y := by
      calc cu x = cu x + (cu x + r1 y) := by rw [hxy',add_zero]
        _ = (cu x + cu x) + r1 y := by abel
        _ = 0 + r1 y := by rw [z10]
        _ = r1 y := zero_add _
    have h1 := congrArg (fun (m : R1 ⟶ R1) => m.hom y) (FP.inl_fst R1 R2)
    have h2 := congrArg (fun (m : R2 ⟶ R1) => m.hom (p2 x)) (FP.inr_fst R1 R2)
    have h3 := congrArg (fun (m : R1 ⟶ R2) => m.hom y) (FP.inl_snd R1 R2)
    have h4 := congrArg (fun (m : R2 ⟶ R2) => m.hom (p2 x)) (FP.inr_snd R1 R2)
    simp only [FH.comp_hom,FH.id_hom,FH.zero_hom,LinearMap.comp_apply,
      LinearMap.id_apply,LinearMap.zero_apply] at h1 h2 h3 h4
    have hβ0 : β0 (αK ⟨(x,y),hxy⟩) = (x,y) := by
      ext : 1
      · change du (r1 ((FP.fst R1 R2).hom ((FP.inl R1 R2).hom y + (FP.inr R1 R2).hom (p2 x)))) +
          r2 ((FP.snd R1 R2).hom ((FP.inl R1 R2).hom y + (FP.inr R1 R2).hom (p2 x))) = x
        rw [map_add (FP.fst R1 R2).hom,map_add (FP.snd R1 R2).hom,h1,h2,h3,h4,
          add_zero,zero_add,← hcu_eq]
        exact congrArg (fun m => m x) hr2_eq
      · change (FP.fst R1 R2).hom ((FP.inl R1 R2).hom y + (FP.inr R1 R2).hom (p2 x)) = y
        rw [map_add,h1,h2,add_zero]
    apply Subtype.ext
    change (β0 (αK ⟨(x,y),hxy⟩) + σD (ψD (β0 (αK ⟨(x,y),hxy⟩)))) = (x,y)
    have hψxy : ψD (x,y) = 0 := hxy
    rw [hβ0,hψxy,map_zero,add_zero]
  obtain ⟨W0,⟨eW⟩⟩ := z229 αK βK hβα
  obtain ⟨s,hs⟩ := S.proj W0 qbig hqbig_surj (KD.subtype.comp eW.symm.toLinearMap)
  have hs_inj : Function.Injective s := by
    intro w1 w2 hw
    have h1 := congrArg qbig hw
    have hs1 := congrArg (fun m => m w1) hs
    have hs2 := congrArg (fun m => m w2) hs
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe] at hs1 hs2
    rw [hs1,hs2] at h1
    exact eW.symm.injective (Subtype.val_injective h1)
  obtain ⟨t,ht⟩ := S.inj W0 s hs_inj LinearMap.id
  let Zsub := LinearMap.ker t
  let rZ : Qbig.Mod →ₗ[Λ] Zsub :=
    { toFun := fun q => ⟨q - s (t q),by
        change t (q - s (t q)) = 0
        rw [map_sub]
        have h1 := congrArg (fun m => m (t q)) ht
        simp only [LinearMap.comp_apply,LinearMap.id_apply] at h1
        rw [h1,sub_self]⟩
      map_add' := fun q1 q2 => by ext; simp [sub_add_sub_comm]
      map_smul' := fun a q => by ext; simp [smul_sub] }
  have hrZ_sub : rZ.comp Zsub.subtype = LinearMap.id := by
    apply LinearMap.ext; rintro ⟨q,hq⟩
    apply Subtype.ext
    change q - s (t q) = q
    rw [hq,map_zero,sub_zero]
  obtain ⟨Z,⟨eZ⟩⟩ := z229 Zsub.subtype rZ hrZ_sub
  let ιZ : Z ⟶ Qbig := ⟨Zsub.subtype.comp eZ.symm.toLinearMap⟩
  let ρZ : Qbig ⟶ Z := ⟨eZ.toLinearMap.comp rZ⟩
  have hιρ : comp ιZ ρZ = 𝟙 Z := by
    apply FP.hom_ext; intro z
    change eZ (rZ (Zsub.subtype (eZ.symm z))) = z
    have h1 := congrArg (fun m => m (eZ.symm z)) hrZ_sub
    simp only [LinearMap.comp_apply,LinearMap.id_apply] at h1
    rw [h1,eZ.apply_symm_apply]
  have hq_decomp : ∀ q : Qbig.Mod,q = ιZ.hom (ρZ.hom q) + s (t q) := by
    intro q
    change q = (eZ.symm (eZ (rZ q))).1 + s (t q)
    rw [eZ.symm_apply_apply]
    change q = (q - s (t q)) + s (t q)
    abel
  have hhbar_s : hbar_big.comp s = 0 := by
    apply LinearMap.ext; intro w
    change ψD (qbig (s w)) = 0
    have h1 := congrArg (fun m => m w) hs
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe] at h1
    rw [h1]
    exact (eW.symm w).2
  let g : Y ⟶ Z := comp gbig ρZ
  let hbar : Z.Mod →ₗ[Λ] nuMod M := hbar_big.comp ιZ.hom
  let h : Z ⟶ X⟦(1 : ℤ)⟧ := ⟨((z3 X).toLinearMap.comp (nuMap j)).comp hbar⟩
  have hhbar_ρZ : hbar.comp ρZ.hom = hbar_big := by
    apply LinearMap.ext; intro q
    change hbar_big (ιZ.hom (ρZ.hom q)) = hbar_big q
    conv_rhs => rw [hq_decomp q]
    rw [map_add]
    have h1 := congrArg (fun m => m (t q)) hhbar_s
    simp only [LinearMap.comp_apply,LinearMap.zero_apply] at h1
    rw [h1,add_zero]
  have hρZ_s : ∀ w : W0.Mod,ρZ.hom (s w) = 0 := by
    intro w
    change eZ (rZ (s w)) = 0
    have h1 : rZ (s w) = 0 := by
      apply Subtype.ext
      change s w - s (t (s w)) = 0
      have ht1 := congrArg (fun m => m w) ht
      simp only [LinearMap.comp_apply,LinearMap.id_apply] at ht1
      rw [ht1,sub_self]
    rw [h1,map_zero]
  have hex_f_g : ExactAt f.hom g.hom := by
    rw [z7]; intro y
    constructor
    · intro hy
      have hde := hq_decomp (gbig.hom y)
      change ρZ.hom (gbig.hom y) = 0 at hy
      rw [hy,map_zero,zero_add] at hde
      have hq0 : qbig (gbig.hom y) = 0 := congrArg (fun m => m y) hex_gbig_qbig.comp_eq_zero
      rw [hde] at hq0
      have hs1 := congrArg (fun m => m (t (gbig.hom y))) hs
      simp only [LinearMap.comp_apply,LinearEquiv.coe_coe] at hs1
      rw [hs1] at hq0
      have ht0 : t (gbig.hom y) = 0 := by
        apply eW.symm.injective
        apply Subtype.ext
        simpa using hq0
      rw [ht0,map_zero] at hde
      have hg1 : g1.hom y = 0 := by
        have h1 := congrArg (fun (m : Q1 ⟶ Q1) => m.hom (g1.hom y)) (FP.inl_fst Q1 R1)
        simp only [FH.comp_hom,FH.id_hom,LinearMap.comp_apply,LinearMap.id_apply] at h1
        change (FP.fst Q1 R1).hom (gbig.hom y) = g1.hom y at h1
        rw [hde,map_zero] at h1
        exact h1.symm
      exact ((z7 f.hom g1.hom).mp hex_f_g1 y).mp hg1
    · rintro ⟨x,rfl⟩
      change ρZ.hom ((FP.inl Q1 R1).hom (g1.hom (f.hom x))) = 0
      have hf1 : g1.hom (f.hom x) = 0 := congrArg (fun m => m x) hex_f_g1.comp_eq_zero
      rw [hf1,map_zero,map_zero]
  have hex_g_hbar : ExactAt g.hom hbar := by
    rw [z7]; intro z
    constructor
    · intro hz
      have hmem : qbig (ιZ.hom z) ∈ KD := hz
      let w : W0.Mod := eW ⟨qbig (ιZ.hom z),hmem⟩
      have hq0 : qbig (ιZ.hom z - s w) = 0 := by
        rw [map_sub]
        have hs1 := congrArg (fun m => m w) hs
        simp only [LinearMap.comp_apply,LinearEquiv.coe_coe] at hs1
        rw [hs1]
        change qbig (ιZ.hom z) - (eW.symm (eW ⟨qbig (ιZ.hom z),hmem⟩)).1 = 0
        rw [eW.symm_apply_apply,sub_self]
      obtain ⟨y,hy⟩ := ((z7 gbig.hom qbig).mp hex_gbig_qbig _).mp hq0
      refine ⟨y,?_⟩
      change ρZ.hom (gbig.hom y) = z
      rw [hy,map_sub,hρZ_s w,sub_zero]
      exact congrArg (fun (m : Z ⟶ Z) => m.hom z) hιρ
    · rintro ⟨y,rfl⟩
      change (hbar.comp ρZ.hom) (gbig.hom y) = 0
      rw [hhbar_ρZ]
      change ψD (qbig (gbig.hom y)) = 0
      have h0 := congrArg (fun m => m y) hex_gbig_qbig.comp_eq_zero
      simp only [LinearMap.comp_apply,LinearMap.zero_apply] at h0
      rw [h0,map_zero]
  have hhbar_surj : Function.Surjective hbar := by
    intro m
    obtain ⟨q,hq⟩ := hhbar_big_surj m
    refine ⟨ρZ.hom q,?_⟩
    have h1 := congrArg (fun f => f q) hhbar_ρZ
    exact h1.trans hq
  obtain ⟨a0',a1',a2',c',ha0',ha1',ha2',hc'⟩ :=
    z72 S hj hex0 hex_f_g hex_g_hbar hhbar_surj
      (S.seq M).exact0 (S.seq M).exact1 (S.seq M).exact2 LinearMap.id
  let m2 : Q1 ⟶ Z := comp (FP.inl Q1 R1) ρZ
  have hm2_g : comp g1 m2 = g := by
    dsimp [m2,g,gbig]; rw [Category.assoc]
  have hm2_hbar : hbar.comp m2.hom = cu.comp q1 := by
    apply LinearMap.ext; intro x
    change (hbar.comp ρZ.hom) ((FP.inl Q1 R1).hom x) = cu (q1 x)
    rw [hhbar_ρZ]
    have h1 := congrArg (fun (m : Q1 ⟶ Q1) => m.hom x) (FP.inl_fst Q1 R1)
    have h2 := congrArg (fun (m : Q1 ⟶ R1) => m.hom x) (FP.inl_snd Q1 R1)
    simp only [FH.comp_hom,FH.id_hom,FH.zero_hom,LinearMap.comp_apply,
      LinearMap.id_apply,LinearMap.zero_apply] at h1 h2
    change cu (q1 ((FP.fst Q1 R1).hom ((FP.inl Q1 R1).hom x))) +
      r1 ((FP.snd Q1 R1).hom ((FP.inl Q1 R1).hom x)) = cu (q1 x)
    rw [h1,h2,map_zero,add_zero]
  have hc'_cu : StableEq (c'.comp cu) c := by
    refine z34 S hj hex0 hex_f_g1 hex_g1_q1 hq1_surj
      (S.seq M).exact0 (S.seq M).exact1 (S.seq M).exact2
      (a0 := a0') (a1 := a1') (a2 := comp m2 a2') (c := c'.comp cu)
      (b0 := a0) (b1 := a1) (b2 := a2) (c' := c)
      ha0' ha1' ?_ ?_ ha0 ha1 ha2 hc (StableEq.refl _)
    · rw [← Category.assoc,hm2_g,ha2']
    · rw [FH.comp_hom,← LinearMap.comp_assoc,hc',LinearMap.comp_assoc,hm2_hbar,
        ← LinearMap.comp_assoc]
  have hc'_stab : StableEq c' (nuMap (S.u M)) := by
    have h1 : StableEq (c'.comp (cu.comp du)) (c'.comp LinearMap.id) := StableEq.comp_left c' hcudu
    have h2 : StableEq ((c'.comp cu).comp du) (c.comp du) := hc'_cu.comp_right du
    have h3 : StableEq ((c.comp d).comp (nuMap (S.u M))) (LinearMap.id.comp (nuMap (S.u M))) :=
      hcd.comp_right _
    have heq1 : c'.comp (cu.comp du) = (c'.comp cu).comp du := by ext x; rfl
    have heq2 : c.comp du = (c.comp d).comp (nuMap (S.u M)) := by ext x; rfl
    rw [LinearMap.comp_id] at h1
    rw [LinearMap.id_comp] at h3
    exact h1.symm.trans (by rw [heq1]; exact h2.trans (by rw [heq2]; exact h3))
  exact ⟨Z,g,h,M,inferInstance,inferInstance,inferInstance,
    j,hbar,a0',a1',a2',c',
    hj,hex0,hex_f_g,hex_g_hbar,hhbar_surj,rfl,
    ha0'.trans (LinearMap.comp_id _),ha1',ha2',hc',hc'_stab⟩
lemma IsDeltaExact.rotate_forward (S : ExactSys) {T : Triangle FP}
    (hT : IsDeltaExact S T) : IsDeltaExact S T.rotate := by
  rcases hT with ⟨M,_,_,_,j,hbar,a0,a1,a2,c,
    hj,hex0,hex1,hex2,hhbar,hmor3,ha0,ha1,ha2,hc,hstab⟩
  obtain ⟨Qc,pc,rc,hrcpc⟩ := hstab
  obtain ⟨rc_lift,hrc_lift⟩ := S.proj Qc (S.seq M).π (S.seq M).π_surj rc
  let a2' : T.obj₃ ⟶ (S.seq M).P2 := a2 - ⟨(rc_lift.comp pc).comp hbar⟩
  have ha2' : comp T.mor₂ a2' = comp a1 (S.seq M).d1 := by
    apply FP.hom_ext; intro y
    have h1 := congrArg (fun (f : T.obj₂ ⟶ (S.seq M).P2) => f.hom y) ha2
    have h2 := congrArg (fun f => f y) hex2.comp_eq_zero
    simp only [a2',FH.comp_hom,FP.sub_eq_add,FH.add_hom,
      LinearMap.comp_apply,LinearMap.add_apply,LinearMap.zero_apply] at h1 h2 ⊢
    rw [h1,h2,map_zero,map_zero,add_zero]
  have hc' : (S.seq M).π.comp a2'.hom = (nuMap (S.u M)).comp hbar := by
    apply LinearMap.ext; intro z
    have h1 := congrArg (fun f => f z) hc
    have h2 := congrArg (fun f => f (pc (hbar z))) hrc_lift
    have h3 := congrArg (fun f => f (hbar z)) hrcpc
    simp only [a2',FP.sub_eq_add,FH.add_hom,LinearMap.comp_apply,
      LinearMap.add_apply,LinearMap.sub_apply] at h1 h2 h3 ⊢
    rw [map_add,h1,h2,← h3,sub_eq_add_neg,z153]
    calc c (hbar z) + (c (hbar z) + nuMap (S.u M) (hbar z))
        = (c (hbar z) + c (hbar z)) + nuMap (S.u M) (hbar z) := by abel
      _ = 0 + nuMap (S.u M) (hbar z) := by rw [z10]
      _ = nuMap (S.u M) (hbar z) := zero_add _
  let K : Type := LinearMap.range T.mor₁.hom
  let q : T.obj₁.Mod →ₗ[Λ] K := T.mor₁.hom.rangeRestrict
  let iK : K →ₗ[Λ] T.obj₂.Mod := (LinearMap.range T.mor₁.hom).subtype
  have hq_surj : Function.Surjective q := T.mor₁.hom.surjective_rangeRestrict
  have hiK_inj : Function.Injective iK := Subtype.val_injective
  have hex_jq : ExactAt j q := by
    rw [z7] at hex0 ⊢
    intro x
    constructor
    · intro hx; exact (hex0 x).mp (congrArg Subtype.val hx)
    · intro hx; exact Subtype.ext ((hex0 x).mpr hx)
  have hex_iK_mor2 : ExactAt iK T.mor₂.hom := by
    rw [z7] at hex1 ⊢
    intro y
    constructor
    · intro hy; obtain ⟨x,hx⟩ := (hex1 y).mp hy; exact ⟨⟨y,⟨x,hx⟩⟩,rfl⟩
    · rintro ⟨⟨_,⟨x,rfl⟩⟩,rfl⟩; exact (hex1 _).mpr ⟨x,rfl⟩
  have hinj_j1 : Function.Injective ((z3 T.obj₁).toLinearMap.comp (nuMap j)) :=
    (z3 T.obj₁).injective.comp (z61 hj)
  have hex_mor2_mor3 : ExactAt T.mor₂.hom T.mor₃.hom := by
    rw [hmor3]; exact hex2.of_comp_inj hinj_j1
  let qtilde : (T.obj₁⟦(1 : ℤ)⟧).Mod →ₗ[Λ] nuMod K :=
    (nuMap q).comp (z3 T.obj₁).symm.toLinearMap
  have hqtilde_surj : Function.Surjective qtilde :=
    (z286 hq_surj).comp (z3 T.obj₁).symm.surjective
  have hex_mor3_qtilde : ExactAt T.mor₃.hom qtilde := by
    rw [hmor3]
    exact (hex_jq.nuMap.of_equiv_mid (z3 T.obj₁)).of_comp_surj hhbar
  have hrot_mor3 : T.rotate.mor₃.hom =
      ((z3 T.obj₂).toLinearMap.comp (nuMap iK)).comp qtilde := by
    dsimp only [Triangle.rotate,Triangle.mk_obj₁,Triangle.mk_obj₂,Triangle.mk_obj₃,
      Triangle.mk_mor₁,Triangle.mk_mor₂,Triangle.mk_mor₃]
    rw [FP.neg_eq]
    apply LinearMap.ext; intro x
    change (T.mor₁⟦(1 : ℤ)⟧').hom x =
      z3 T.obj₂ (nuMap iK (nuMap q ((z3 T.obj₁).symm x)))
    rw [← LinearMap.comp_apply,← z83]
    have hcomp : iK.comp q = T.mor₁.hom := by apply LinearMap.ext; intro y; rfl
    rw [hcomp,z5 T.mor₁]
    exact congrArg (T.mor₁⟦(1 : ℤ)⟧').hom ((z3 T.obj₁).apply_symm_apply x).symm
  obtain ⟨τ,hτj,hτq⟩ := S.u_syzygy j q hj hex_jq hq_surj
  let P0 := T.obj₁
  let m0j := S.map0 j; let m0q := S.map0 q
  let m1j := S.map1 j; let m1q := S.map1 q
  let m2j := S.map2 j; let m2q := S.map2 q
  have hm0_zero : comp m0j m0q = 0 := by
    rw [← S.map0_comp,hex_jq.comp_eq_zero,S.map0_zero]
  have hm1_zero : comp m1j m1q = 0 := by
    rw [← S.map1_comp,hex_jq.comp_eq_zero,S.map1_zero]
  have hm2_zero : comp m2j m2q = 0 := by
    rw [← S.map2_comp,hex_jq.comp_eq_zero,S.map2_zero]
  let k0 : P0.Mod →ₗ[Λ] (S.seq P0.Mod).P0.Mod :=
    (comp a0 m0j).hom + (S.seq P0.Mod).ι
  have hk0 : k0.comp j = 0 := by
    apply LinearMap.ext; intro m
    have h1 := congrArg (fun f => f m) ha0
    have h2 := congrArg (fun f => f m) (S.map0_ι j)
    simp only [k0,m0j,FH.comp_hom,LinearMap.comp_apply,LinearMap.add_apply,
      LinearMap.zero_apply] at h1 h2 ⊢
    rw [h1,h2,z10]
  obtain ⟨s0h,hs0h⟩ := z32 S hex0 (S.seq P0.Mod).P0 k0 hk0
  let s0 : T.obj₂ ⟶ (S.seq P0.Mod).P0 := ⟨s0h⟩
  let b0 : T.obj₂ ⟶ (S.seq K).P0 := comp s0 m0q
  have hb0 : b0.hom.comp iK = (S.seq K).ι := by
    apply LinearMap.ext; rintro ⟨_,⟨x,rfl⟩⟩
    have h1 := congrArg (fun f => f x) hs0h
    have h2 := congrArg (fun (f : (S.seq M).P0 ⟶ (S.seq K).P0) => f.hom (a0.hom x)) hm0_zero
    have h3 := congrArg (fun f => f x) (S.map0_ι q)
    simp only [b0,k0,m0j,m0q,FH.comp_hom,FH.zero_hom,LinearMap.comp_apply,
      LinearMap.add_apply,LinearMap.zero_apply] at h1 h2 h3 ⊢
    change m0q.hom (s0h (T.mor₁.hom x)) = (S.seq K).ι (q x)
    rw [h1,map_add,h2,zero_add,h3]
  let k1 : T.obj₂ ⟶ (S.seq P0.Mod).P1 :=
    comp s0 (S.seq P0.Mod).d0 + comp a1 m1j
  have hk1 : k1.hom.comp T.mor₁.hom = 0 := by
    apply LinearMap.ext; intro x
    have h1 := congrArg (fun f => f x) hs0h
    have h2 := congrArg (fun (f : P0 ⟶ (S.seq M).P1) => f.hom x) ha1
    have h3 := congrArg (fun (f : (S.seq M).P0 ⟶ (S.seq P0.Mod).P1) => f.hom (a0.hom x))
      (S.map1_d0 j)
    have h4 := congrArg (fun f => f x) (S.seq P0.Mod).exact0.comp_eq_zero
    simp only [k1,k0,s0,m0j,m1j,FH.comp_hom,FH.add_hom,LinearMap.comp_apply,
      LinearMap.add_apply,LinearMap.zero_apply] at h1 h2 h3 h4 ⊢
    rw [h1,map_add,h4,add_zero,h2,h3,z10]
  obtain ⟨s1h,hs1h⟩ := z32 S hex1 (S.seq P0.Mod).P1 k1.hom hk1
  let s1 : T.obj₃ ⟶ (S.seq P0.Mod).P1 := ⟨s1h⟩
  have hs1 : comp T.mor₂ s1 = k1 := FH.ext hs1h
  let b1 : T.obj₃ ⟶ (S.seq K).P1 := comp s1 m1q
  have hb1 : comp T.mor₂ b1 = comp b0 (S.seq K).d0 := by
    dsimp [b0,b1]
    rw [← Category.assoc,hs1]
    dsimp [k1]
    rw [Preadditive.add_comp,Category.assoc,Category.assoc,hm1_zero,Limits.comp_zero,
      add_zero,S.map1_d0 q,Category.assoc]
  let k2 : T.obj₃ ⟶ (S.seq P0.Mod).P2 :=
    comp s1 (S.seq P0.Mod).d1 + comp a2' m2j
  have hk2 : k2.hom.comp T.mor₂.hom = 0 := by
    apply LinearMap.ext; intro y
    have h1 := congrArg (fun (f : T.obj₂ ⟶ (S.seq P0.Mod).P1) => f.hom y) hs1
    have h2 := congrArg (fun (f : T.obj₂ ⟶ (S.seq M).P2) => f.hom y) ha2'
    have h3 := congrArg (fun (f : (S.seq M).P1 ⟶ (S.seq P0.Mod).P2) => f.hom (a1.hom y))
      (S.map2_d1 j)
    have h4 := congrArg (fun f => f (s0.hom y)) (S.seq P0.Mod).exact1.comp_eq_zero
    simp only [k2,k1,m1j,m2j,FH.comp_hom,FH.add_hom,LinearMap.comp_apply,
      LinearMap.add_apply,LinearMap.zero_apply] at h1 h2 h3 h4 ⊢
    rw [h1,map_add,h4,zero_add,h2,h3,z10]
  obtain ⟨s2h,hs2h⟩ := z32 S hex_mor2_mor3 (S.seq P0.Mod).P2 k2.hom hk2
  let s2 : T.obj₁⟦(1 : ℤ)⟧ ⟶ (S.seq P0.Mod).P2 := ⟨s2h⟩
  have hs2 : comp T.mor₃ s2 = k2 := FH.ext hs2h
  let b2 : T.obj₁⟦(1 : ℤ)⟧ ⟶ (S.seq K).P2 := comp s2 m2q
  have hb2 : comp T.mor₃ b2 = comp b1 (S.seq K).d1 := by
    dsimp [b1,b2]
    rw [← Category.assoc,hs2]
    dsimp [k2]
    rw [Preadditive.add_comp,Category.assoc,Category.assoc,hm2_zero,Limits.comp_zero,
      add_zero,S.map2_d1 q,Category.assoc]
  let s2_pi : (T.obj₁⟦(1 : ℤ)⟧).Mod →ₗ[Λ] nuMod P0.Mod := (S.seq P0.Mod).π.comp s2.hom
  let τ_shift : (T.obj₁⟦(1 : ℤ)⟧).Mod →ₗ[Λ] nuMod P0.Mod :=
    (nuMap τ.hom).comp (z3 P0).symm.toLinearMap
  let δ : (T.obj₁⟦(1 : ℤ)⟧).Mod →ₗ[Λ] nuMod P0.Mod := s2_pi + τ_shift
  have hδ : δ.comp T.mor₃.hom = 0 := by
    apply LinearMap.ext; intro z
    have h1 := congrArg (fun (f : T.obj₃ ⟶ (S.seq P0.Mod).P2) => (S.seq P0.Mod).π (f.hom z)) hs2
    have h2 := congrArg (fun f => f (s1.hom z)) (S.seq P0.Mod).exact2.comp_eq_zero
    have h3 := congrArg (fun f => f (a2'.hom z)) (S.π_map2 j)
    have h4 := congrArg (fun f => f z) hc'
    have h5 : T.mor₃.hom z = z3 P0 (nuMap j (hbar z)) :=
      congrArg (fun f => f z) hmor3
    change (S.seq P0.Mod).π (s2.hom (T.mor₃.hom z)) +
      nuMap τ.hom ((z3 P0).symm (T.mor₃.hom z)) = 0
    simp only [k2,m2j,FH.comp_hom,FH.add_hom,LinearMap.comp_apply,
      LinearMap.add_apply,LinearMap.zero_apply] at h1 h2 h3 h4
    rw [h1,map_add,h2,zero_add,h3,h4,h5,LinearEquiv.symm_apply_apply]
    have hτj' : (nuMap j) ((nuMap (S.u M)) (hbar z)) = (nuMap τ.hom) ((nuMap j) (hbar z)) := by
      apply nuMod.ext
      exact (congrArg (fun f => f (hbar z).val) hτj).symm
    rw [hτj',z10]
  obtain ⟨tmap,htmap⟩ := z21 hex_mor3_qtilde hqtilde_surj δ hδ
  let cK : nuMod K →ₗ[Λ] nuMod K := nuMap (S.u K) + (nuMap q).comp tmap
  have hcK : (S.seq K).π.comp b2.hom = cK.comp qtilde := by
    apply LinearMap.ext; intro x
    have h1 := congrArg (fun f => f (s2.hom x)) (S.π_map2 q)
    have h2 := congrArg (fun f => f x) htmap
    have h3 := congrArg (fun f => f ((z3 P0).symm x).val) hτq
    simp only [LinearMap.comp_apply] at h1 h2 h3
    change (S.seq K).π ((S.map2 q).hom (s2.hom x)) =
      nuMap (S.u K) (qtilde x) + nuMap q (tmap (qtilde x))
    rw [h1,h2]
    change nuMap q ((S.seq P0.Mod).π (s2.hom x)) =
      nuMap (S.u K) (nuMap q ((z3 P0).symm x)) +
        nuMap q ((S.seq P0.Mod).π (s2.hom x) + nuMap τ.hom ((z3 P0).symm x))
    rw [map_add]
    have h3' : nuMap q (nuMap τ.hom ((z3 P0).symm x)) =
        nuMap (S.u K) (nuMap q ((z3 P0).symm x)) := by
      apply nuMod.ext; exact h3
    rw [h3']
    calc nuMap q ((S.seq P0.Mod).π (s2.hom x))
        = 0 + nuMap q ((S.seq P0.Mod).π (s2.hom x)) := (zero_add _).symm
      _ = (nuMap (S.u K) (nuMap q ((z3 P0).symm x)) +
            nuMap (S.u K) (nuMap q ((z3 P0).symm x))) +
          nuMap q ((S.seq P0.Mod).π (s2.hom x)) := by rw [z10]
      _ = nuMap (S.u K) (nuMap q ((z3 P0).symm x)) +
          (nuMap q ((S.seq P0.Mod).π (s2.hom x)) +
            nuMap (S.u K) (nuMap q ((z3 P0).symm x))) := by abel
  have hcK_stab : StableEq cK (nuMap (S.u K)) := by
    refine ⟨P0⟦(1 : ℤ)⟧,(z3 P0).toLinearMap.comp tmap,
      (nuMap q).comp (z3 P0).symm.toLinearMap,?_⟩
    apply LinearMap.ext; intro k
    change (nuMap (S.u K) k + nuMap q (tmap k)) - nuMap (S.u K) k =
      nuMap q ((z3 P0).symm (z3 P0 (tmap k)))
    rw [LinearEquiv.symm_apply_apply]
    abel
  exact ⟨K,inferInstance,inferInstance,inferInstance,
    iK,qtilde,b0,b1,b2,cK,
    hiK_inj,hex_iK_mor2,hex_mor2_mor3,hex_mor3_qtilde,hqtilde_surj,
    hrot_mor3,hb0,hb1,hb2,hcK,hcK_stab⟩
lemma FP.rotate_mor₃ (T : Triangle FP) :
    T.rotate.mor₃ = T.mor₁⟦(1 : ℤ)⟧' :=
  FP.neg_eq _
def z233 (T : Triangle FP) :
    T ≅ T.rotate.rotate.rotate.rotate.rotate.rotate := by
  refine Triangle.isoMk _ _
    (shiftFunctor1SqIso.app T.obj₁).symm
    (shiftFunctor1SqIso.app T.obj₂).symm
    (shiftFunctor1SqIso.app T.obj₃).symm ?_ ?_ ?_
  · simp only [Triangle.rotate_mor₁,Triangle.rotate_mor₂,FP.rotate_mor₃]
    exact shiftFunctor1SqIso.inv.naturality T.mor₁
  · simp only [Triangle.rotate_mor₁,Triangle.rotate_mor₂,FP.rotate_mor₃]
    exact shiftFunctor1SqIso.inv.naturality T.mor₂
  · simp only [Triangle.rotate_mor₁,Triangle.rotate_mor₂,FP.rotate_mor₃]
    have heq : ((shiftFunctor1SqIso.app T.obj₁).symm.hom)⟦(1 : ℤ)⟧' =
        shiftFunctor1SqIso.inv.app (T.obj₁⟦(1 : ℤ)⟧) := by
      exact eqToHom_map shiftFunctor1 (z17 T.obj₁).symm
    change comp T.mor₃ (((shiftFunctor1SqIso.app T.obj₁).symm.hom)⟦(1 : ℤ)⟧') =
      comp (shiftFunctor1SqIso.inv.app T.obj₃)
        ((T.mor₃⟦(1 : ℤ)⟧')⟦(1 : ℤ)⟧')
    rw [heq]
    exact shiftFunctor1SqIso.inv.naturality T.mor₃
lemma IsDeltaExact.rotate_iff (S : ExactSys) (T : Triangle FP) :
    IsDeltaExact S T ↔ IsDeltaExact S T.rotate := by
  constructor
  · exact IsDeltaExact.rotate_forward S
  · intro h1
    have h6 := IsDeltaExact.rotate_forward S (IsDeltaExact.rotate_forward S
      (IsDeltaExact.rotate_forward S (IsDeltaExact.rotate_forward S
        (IsDeltaExact.rotate_forward S h1))))
    exact IsDeltaExact.isomorphic S h6 (z233 T)
lemma IsDeltaExact.complete_morphism (S : ExactSys)
    (T₁ T₂ : Triangle FP) (hT₁ : IsDeltaExact S T₁) (hT₂ : IsDeltaExact S T₂)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (hab : comp T₁.mor₁ b = comp a T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃,
      comp T₁.mor₂ c = comp b T₂.mor₂ ∧
      comp T₁.mor₃ (a⟦(1 : ℤ)⟧') = comp c T₂.mor₃ := by
  rcases hT₁ with ⟨M1,_,_,_,j1,hbar1,a01,a11,a21,c1,
    hj1,hex01,hex11,hex21,hhbar1,hmor31,ha01,ha11,ha21,hc1,hstab1⟩
  rcases hT₂ with ⟨M2,_,_,_,j2,hbar2,a02,a12,a22,c2,
    hj2,hex02,hex12,hex22,hhbar2,hmor32,ha02,ha12,ha22,hc2,hstab2⟩
  have ha_kill : T₂.mor₁.hom.comp (a.hom.comp j1) = 0 := by
    apply LinearMap.ext; intro m
    have h1 := congrArg (fun (f : T₁.obj₁ ⟶ T₂.obj₂) => f.hom (j1 m)) hab
    have h2 := congrArg (fun f => f m) hex01.comp_eq_zero
    simp only [FH.comp_hom,LinearMap.comp_apply,LinearMap.zero_apply] at h1 h2 ⊢
    rw [← h1,h2,map_zero]
  obtain ⟨g,hg⟩ := z111 hj2 hex02 (a.hom.comp j1) ha_kill
  have hb_kill : (T₂.mor₂.hom.comp b.hom).comp T₁.mor₁.hom = 0 := by
    apply LinearMap.ext; intro x
    have h1 := congrArg (fun (f : T₁.obj₁ ⟶ T₂.obj₂) => T₂.mor₂.hom (f.hom x)) hab
    have h2 := congrArg (fun f => f (a.hom x)) hex12.comp_eq_zero
    simp only [FH.comp_hom,LinearMap.comp_apply,LinearMap.zero_apply] at h1 h2 ⊢
    rw [h1,h2]
  obtain ⟨c0h,hc0h⟩ := z32 S hex11 T₂.obj₃ (T₂.mor₂.hom.comp b.hom) hb_kill
  let c0 : T₁.obj₃ ⟶ T₂.obj₃ := ⟨c0h⟩
  have hc0 : comp T₁.mor₂ c0 = comp b T₂.mor₂ := FH.ext hc0h
  have hc0_kill : (hbar2.comp c0.hom).comp T₁.mor₂.hom = 0 := by
    apply LinearMap.ext; intro y
    have h1 := congrArg (fun (f : T₁.obj₂ ⟶ T₂.obj₃) => hbar2 (f.hom y)) hc0
    have h2 := congrArg (fun f => f (b.hom y)) hex22.comp_eq_zero
    simp only [FH.comp_hom,LinearMap.comp_apply,LinearMap.zero_apply] at h1 h2 ⊢
    rw [h1,h2]
  obtain ⟨d,hd⟩ := z21 hex21 hhbar1 (hbar2.comp c0.hom) hc0_kill
  have hcomp_d : StableEq (c2.comp d) ((nuMap g).comp c1) := by
    refine z34 S hj1 hex01 hex11 hex21 hhbar1
      (S.seq M2).exact0 (S.seq M2).exact1 (S.seq M2).exact2
      (g := g) (g' := g)
      (a0 := comp a a02) (a1 := comp b a12)
      (a2 := comp c0 a22) (c := c2.comp d)
      (b0 := comp a01 (S.map0 g)) (b1 := comp a11 (S.map1 g))
      (b2 := comp a21 (S.map2 g)) (c' := (nuMap g).comp c1)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (StableEq.refl g)
    · rw [FH.comp_hom,LinearMap.comp_assoc,← hg,← LinearMap.comp_assoc,ha02]
    · rw [← Category.assoc,hab,Category.assoc,ha12,← Category.assoc]
    · rw [← Category.assoc,hc0,Category.assoc,ha22,← Category.assoc]
    · rw [FH.comp_hom,← LinearMap.comp_assoc,hc2,LinearMap.comp_assoc,← hd,
        ← LinearMap.comp_assoc]
    · rw [FH.comp_hom,LinearMap.comp_assoc,ha01,S.map0_ι g]
    · rw [← Category.assoc,ha11,Category.assoc,S.map1_d0 g,← Category.assoc]
    · rw [← Category.assoc,ha21,Category.assoc,S.map2_d1 g,← Category.assoc]
    · rw [FH.comp_hom,← LinearMap.comp_assoc,S.π_map2 g,LinearMap.comp_assoc,hc1,
        ← LinearMap.comp_assoc]
  have hnu_u2d : StableEq ((nuMap (S.u M2)).comp d) ((nuMap (S.u M2)).comp (nuMap g)) := by
    have h1 : StableEq ((nuMap (S.u M2)).comp d) (c2.comp d) := (hstab2.symm).comp_right d
    have h2 : StableEq ((nuMap g).comp c1) ((nuMap g).comp (nuMap (S.u M1))) := hstab1.comp_left _
    have h3 : StableEq ((nuMap g).comp (nuMap (S.u M1))) ((nuMap (S.u M2)).comp (nuMap g)) := by
      rw [← z83,← z83]
      exact (S.u_natural g).symm.nuMap
    exact h1.trans (hcomp_d.trans (h2.trans h3))
  have hd_stab : StableEq d (nuMap g) := by
    have huu : StableEq ((nuMap (S.u M2)).comp (nuMap (S.u M2))) LinearMap.id := by
      rw [← z83,← z207]; exact (S.u_comp_u M2).nuMap
    have hL : StableEq ((nuMap (S.u M2)).comp ((nuMap (S.u M2)).comp d)) d := by
      have : (nuMap (S.u M2)).comp ((nuMap (S.u M2)).comp d) =
          ((nuMap (S.u M2)).comp (nuMap (S.u M2))).comp d := by ext x; rfl
      rw [this]; simpa using huu.comp_right d
    have hR : StableEq ((nuMap (S.u M2)).comp ((nuMap (S.u M2)).comp (nuMap g))) (nuMap g) := by
      have : (nuMap (S.u M2)).comp ((nuMap (S.u M2)).comp (nuMap g)) =
          ((nuMap (S.u M2)).comp (nuMap (S.u M2))).comp (nuMap g) := by ext x; rfl
      rw [this]; simpa using huu.comp_right (nuMap g)
    exact hL.symm.trans ((hnu_u2d.comp_left _).trans hR)
  obtain ⟨Qd,pd,rd,hrdpd⟩ := hd_stab
  obtain ⟨rd_lift,hrd_lift⟩ := S.proj Qd hbar2 hhbar2 rd
  let c : T₁.obj₃ ⟶ T₂.obj₃ := c0 - ⟨(rd_lift.comp pd).comp hbar1⟩
  refine ⟨c,?_,?_⟩
  · apply FP.hom_ext; intro y
    have h1 := congrArg (fun (f : T₁.obj₂ ⟶ T₂.obj₃) => f.hom y) hc0
    have h2 := congrArg (fun f => f y) hex21.comp_eq_zero
    simp only [c,FP.sub_eq_add,FH.comp_hom,FH.add_hom,
      LinearMap.comp_apply,LinearMap.add_apply,LinearMap.zero_apply] at h1 h2 ⊢
    rw [h1,h2,map_zero,map_zero,add_zero]
  · have hbar2_c : hbar2.comp c.hom = (nuMap g).comp hbar1 := by
      apply LinearMap.ext; intro z
      have h1 := congrArg (fun f => f z) hd
      have h2 := congrArg (fun f => f (pd (hbar1 z))) hrd_lift
      have h3 := congrArg (fun f => f (hbar1 z)) hrdpd
      simp only [c,FP.sub_eq_add,FH.add_hom,LinearMap.comp_apply,
        LinearMap.add_apply,LinearMap.sub_apply] at h1 h2 h3 ⊢
      rw [map_add,← h1,h2,← h3,sub_eq_add_neg,z153]
      calc d (hbar1 z) + (d (hbar1 z) + nuMap g (hbar1 z))
          = (d (hbar1 z) + d (hbar1 z)) + nuMap g (hbar1 z) := by abel
        _ = 0 + nuMap g (hbar1 z) := by rw [z10]
        _ = nuMap g (hbar1 z) := zero_add _
    apply FP.hom_ext; intro z
    change (a⟦(1 : ℤ)⟧').hom (T₁.mor₃.hom z) = T₂.mor₃.hom (c.hom z)
    have h1 : T₁.mor₃.hom z = z3 T₁.obj₁ (nuMap j1 (hbar1 z)) :=
      congrArg (fun f => f z) hmor31
    have h2 : T₂.mor₃.hom (c.hom z) = z3 T₂.obj₁ (nuMap j2 (hbar2 (c.hom z))) :=
      congrArg (fun f => f (c.hom z)) hmor32
    have h3 : hbar2 (c.hom z) = nuMap g (hbar1 z) :=
      congrArg (fun f => f z) hbar2_c
    rw [h1,h2,h3,← z5 a]
    congr 1
    change ((nuMap a.hom).comp (nuMap j1)) (hbar1 z) = ((nuMap j2).comp (nuMap g)) (hbar1 z)
    rw [← z83,← z83,hg]
def deltaPretriangulated (S : ExactSys) : Pretriangulated FP where
  distinguishedTriangles := { T | IsDeltaExact S T }
  isomorphic_distinguished _ hT₁ _ e := IsDeltaExact.isomorphic S hT₁ e
  contractible_distinguished X := IsDeltaExact.contractible S X
  distinguished_cocone_triangle f := IsDeltaExact.cocone S f
  rotate_distinguished_triangle T := IsDeltaExact.rotate_iff S T
  complete_distinguished_triangle_morphism := IsDeltaExact.complete_morphism S
def z62 (T₁ T₂ : Triangle FP) : Triangle FP :=
  Triangle.mk
    (FP.mat T₁.mor₁ 0 0 T₂.mor₁)
    (FP.mat T₁.mor₂ 0 0 T₂.mor₂)
    (comp (FP.mat T₁.mor₃ 0 0 T₂.mor₃)
      (FP.sumShiftIso T₁.obj₁ T₂.obj₁).hom)
def FP.sumIsoPiFn (f : Bool → FP) [HasProduct f] :
    FP.sum (f true) (f false) ≅ ∏ᶜ f where
  hom := Limits.Pi.lift (fun b : Bool =>
    match b with
    | true => FP.fst (f true) (f false)
    | false => FP.snd (f true) (f false))
  inv := FP.lift (Limits.Pi.π f true) (Limits.Pi.π f false)
  hom_inv_id := by
    apply FP.sum_hom_ext_right
    · dsimp [FP.lift]
      rw [Category.assoc,Preadditive.add_comp,Category.assoc,Category.assoc,
        FP.inl_fst,FP.inr_fst,Category.comp_id,Limits.comp_zero,add_zero,
        Category.id_comp]
      exact Limits.Pi.lift_π _ true
    · dsimp [FP.lift]
      rw [Category.assoc,Preadditive.add_comp,Category.assoc,Category.assoc,
        FP.inl_snd,FP.inr_snd,Limits.comp_zero,Category.comp_id,zero_add,
        Category.id_comp]
      exact Limits.Pi.lift_π _ false
  inv_hom_id := by
    refine Limits.Pi.hom_ext _ _ fun b => ?_
    cases b
    · rw [Category.assoc,Limits.Pi.lift_π,Category.id_comp]
      exact FP.lift_snd _ _
    · rw [Category.assoc,Limits.Pi.lift_π,Category.id_comp]
      exact FP.lift_fst _ _
lemma FP.sumIsoPiFn_hom_π (f : Bool → FP) [HasProduct f] (b : Bool) :
    comp (FP.sumIsoPiFn f).hom (Limits.Pi.π f b) =
      match b with
      | true => FP.fst (f true) (f false)
      | false => FP.snd (f true) (f false) :=
  Limits.Pi.lift_π _ b
lemma z74 [Pretriangulated FP]
    {T₁ T₂ : Triangle FP}
    (hT₁ : T₁ ∈ distTriang FP) (hT₂ : T₂ ∈ distTriang FP) :
    z62 T₁ T₂ ∈ distTriang FP := by
  let F : Bool → Triangle FP := fun b => match b with | true => T₁ | false => T₂
  have hF : ∀ b,F b ∈ distTriang FP := fun b => by cases b <;> assumption
  have hP : productTriangle F ∈ distTriang FP := productTriangle_distinguished F hF
  let pTrue : z62 T₁ T₂ ⟶ T₁ :=
    Triangle.homMk (z62 T₁ T₂) T₁
      (FP.fst T₁.obj₁ T₂.obj₁) (FP.fst T₁.obj₂ T₂.obj₂) (FP.fst T₁.obj₃ T₂.obj₃)
      (by
        dsimp only [z62,Triangle.mk]
        rw [FP.mat_fst]
        dsimp [FP.desc]
        rw [Limits.comp_zero,add_zero])
      (by
        dsimp only [z62,Triangle.mk]
        rw [FP.mat_fst]
        dsimp [FP.desc]
        rw [Limits.comp_zero,add_zero])
      (by
        dsimp only [z62,Triangle.mk]
        rw [Category.assoc,FP.sumShiftIso_fst,FP.mat_fst]
        dsimp [FP.desc]
        rw [Limits.comp_zero,add_zero])
  let pFalse : z62 T₁ T₂ ⟶ T₂ :=
    Triangle.homMk (z62 T₁ T₂) T₂
      (FP.snd T₁.obj₁ T₂.obj₁) (FP.snd T₁.obj₂ T₂.obj₂) (FP.snd T₁.obj₃ T₂.obj₃)
      (by
        dsimp only [z62,Triangle.mk]
        rw [FP.mat_snd]
        dsimp [FP.desc]
        rw [Limits.comp_zero,zero_add])
      (by
        dsimp only [z62,Triangle.mk]
        rw [FP.mat_snd]
        dsimp [FP.desc]
        rw [Limits.comp_zero,zero_add])
      (by
        dsimp only [z62,Triangle.mk]
        rw [Category.assoc,FP.sumShiftIso_snd,FP.mat_snd]
        dsimp [FP.desc]
        rw [Limits.comp_zero,zero_add])
  let pFam : ∀ b,z62 T₁ T₂ ⟶ F b :=
    fun b => match b with | true => pTrue | false => pFalse
  let φ : z62 T₁ T₂ ⟶ productTriangle F :=
    productTriangle.lift F pFam
  have h1 : φ.hom₁ = (FP.sumIsoPiFn (fun b => (F b).obj₁)).hom := by
    refine Limits.Pi.hom_ext _ _ fun b => ?_
    have hL : comp φ.hom₁ (Limits.Pi.π (fun j => (F j).obj₁) b) =
        (pFam b).hom₁ := Limits.Pi.lift_π _ b
    have hR := FP.sumIsoPiFn_hom_π (fun b => (F b).obj₁) b
    refine hL.trans (Eq.trans ?_ hR.symm)
    cases b <;> rfl
  have h2 : φ.hom₂ = (FP.sumIsoPiFn (fun b => (F b).obj₂)).hom := by
    refine Limits.Pi.hom_ext _ _ fun b => ?_
    have hL : comp φ.hom₂ (Limits.Pi.π (fun j => (F j).obj₂) b) =
        (pFam b).hom₂ := Limits.Pi.lift_π _ b
    have hR := FP.sumIsoPiFn_hom_π (fun b => (F b).obj₂) b
    refine hL.trans (Eq.trans ?_ hR.symm)
    cases b <;> rfl
  have h3 : φ.hom₃ = (FP.sumIsoPiFn (fun b => (F b).obj₃)).hom := by
    refine Limits.Pi.hom_ext _ _ fun b => ?_
    have hL : comp φ.hom₃ (Limits.Pi.π (fun j => (F j).obj₃) b) =
        (pFam b).hom₃ := Limits.Pi.lift_π _ b
    have hR := FP.sumIsoPiFn_hom_π (fun b => (F b).obj₃) b
    refine hL.trans (Eq.trans ?_ hR.symm)
    cases b <;> rfl
  have : IsIso φ.hom₁ := by
    let e1 := FP.sumIsoPiFn (fun b => (F b).obj₁)
    change IsIso φ.hom₁
    exact ⟨⟨e1.inv,by rw [h1]; exact e1.hom_inv_id,by rw [h1]; exact e1.inv_hom_id⟩⟩
  have : IsIso φ.hom₂ := by
    let e2 := FP.sumIsoPiFn (fun b => (F b).obj₂)
    change IsIso φ.hom₂
    exact ⟨⟨e2.inv,by rw [h2]; exact e2.hom_inv_id,by rw [h2]; exact e2.inv_hom_id⟩⟩
  have : IsIso φ.hom₃ := by
    let e3 := FP.sumIsoPiFn (fun b => (F b).obj₃)
    change IsIso φ.hom₃
    exact ⟨⟨e3.inv,by rw [h3]; exact e3.hom_inv_id,by rw [h3]; exact e3.inv_hom_id⟩⟩
  have : IsIso φ := Triangle.isIso_of_isIsos φ inferInstance inferInstance inferInstance
  exact Pretriangulated.isomorphic_distinguished _ hP _ (asIso φ)
def FP.sumZeroRightIso (X Z : FP) (hZ : Limits.IsZero Z) :
    FP.sum X Z ≅ X where
  hom := FP.fst X Z
  inv := FP.inl X Z
  hom_inv_id := by
    have hsnd : FP.snd X Z = 0 := hZ.eq_of_tgt _ _
    calc comp (FP.fst X Z) (FP.inl X Z)
        = comp (FP.fst X Z) (FP.inl X Z) +
            comp (FP.snd X Z) (FP.inr X Z) := by
            rw [hsnd,Limits.zero_comp,add_zero]
      _ = 𝟙 (FP.sum X Z) := FP.total_sum X Z
  inv_hom_id := FP.inl_fst X Z
def FP.sumZeroLeftIso (Z : FP) (hZ : Limits.IsZero Z) (Y : FP) :
    FP.sum Z Y ≅ Y where
  hom := FP.snd Z Y
  inv := FP.inr Z Y
  hom_inv_id := by
    have hfst : FP.fst Z Y = 0 := hZ.eq_of_tgt _ _
    calc comp (FP.snd Z Y) (FP.inr Z Y)
        = comp (FP.fst Z Y) (FP.inl Z Y) +
            comp (FP.snd Z Y) (FP.inr Z Y) := by
            rw [hfst,Limits.zero_comp,zero_add]
      _ = 𝟙 (FP.sum Z Y) := FP.total_sum Z Y
  inv_hom_id := FP.inr_snd Z Y
def FP.shearIso {X X' : FP} (a : X ⟶ X') :
    FP.sum X X' ≅ FP.sum X X' where
  hom := FP.mat (𝟙 X) 0 a (𝟙 X')
  inv := FP.mat (𝟙 X) 0 a (𝟙 X')
  hom_inv_id := by
    rw [FP.mat_comp]
    simp only [Category.id_comp,Category.comp_id,Limits.zero_comp,Limits.comp_zero,
      add_zero,zero_add,FP.add_self,FP.mat_id]
  inv_hom_id := by
    rw [FP.mat_comp]
    simp only [Category.id_comp,Category.comp_id,Limits.zero_comp,Limits.comp_zero,
      add_zero,zero_add,FP.add_self,FP.mat_id]
lemma FP.counitInv_comp_shift_invRotate {X Z : FP} (w : Z ⟶ X⟦(1 : ℤ)⟧) :
    comp ((shiftEquiv FP (1 : ℤ)).counitIso.inv.app Z)
      ((shiftEquiv FP (1 : ℤ)).functor.map
        (comp ((shiftEquiv FP (1 : ℤ)).inverse.map w)
          ((shiftEquiv FP (1 : ℤ)).unitIso.inv.app X))) = w := by
  let e := shiftEquiv FP (1 : ℤ)
  have h1 : e.functor.map (comp (e.inverse.map w) (e.unitIso.inv.app X)) =
      comp (e.functor.map (e.inverse.map w)) (e.functor.map (e.unitIso.inv.app X)) :=
    CategoryTheory.Functor.map_comp e.functor (e.inverse.map w) (e.unitIso.inv.app X)
  have hnat : comp (e.counitIso.inv.app Z) (e.functor.map (e.inverse.map w)) =
      comp w (e.counitIso.inv.app (e.functor.obj X)) :=
    (e.counitIso.inv.naturality w).symm
  have htri : comp (e.counitIso.inv.app (e.functor.obj X))
      (e.functor.map (e.unitIso.inv.app X)) = 𝟙 (e.functor.obj X) := by
    have h := e.functor_unitIso_comp X
    have h1' : comp (e.functor.map (e.unitIso.hom.app X))
        (e.functor.map (e.unitIso.inv.app X)) = 𝟙 (e.functor.obj X) := by
      rw [← CategoryTheory.Functor.map_comp,Iso.hom_inv_id_app,CategoryTheory.Functor.map_id]; rfl
    apply (CategoryTheory.cancel_epi (e.counitIso.hom.app (e.functor.obj X))).mp
    have hL : comp (e.counitIso.hom.app (e.functor.obj X))
        (comp (e.counitIso.inv.app (e.functor.obj X))
          (e.functor.map (e.unitIso.inv.app X))) = e.functor.map (e.unitIso.inv.app X) := by
      rw [← Category.assoc,Iso.hom_inv_id_app,Category.id_comp]
    have hR : comp (e.counitIso.hom.app (e.functor.obj X)) (𝟙 (e.functor.obj X)) =
        e.counitIso.hom.app (e.functor.obj X) := Category.comp_id _
    rw [hL,hR]
    apply (CategoryTheory.cancel_epi (e.functor.map (e.unitIso.hom.app X))).mp
    exact h1'.trans h.symm
  have hs1 : comp (e.counitIso.inv.app Z)
      (e.functor.map (comp (e.inverse.map w) (e.unitIso.inv.app X))) =
      comp (e.counitIso.inv.app Z)
        (comp (e.functor.map (e.inverse.map w))
          (e.functor.map (e.unitIso.inv.app X))) := congrArg _ h1
  have hs2 : comp (e.counitIso.inv.app Z)
      (comp (e.functor.map (e.inverse.map w))
        (e.functor.map (e.unitIso.inv.app X))) =
      comp (comp (e.counitIso.inv.app Z)
        (e.functor.map (e.inverse.map w)))
        (e.functor.map (e.unitIso.inv.app X)) := (Category.assoc _ _ _).symm
  have hs3 : comp (comp (e.counitIso.inv.app Z)
      (e.functor.map (e.inverse.map w)))
      (e.functor.map (e.unitIso.inv.app X)) =
      comp (comp w (e.counitIso.inv.app (e.functor.obj X)))
        (e.functor.map (e.unitIso.inv.app X)) :=
    congrArg (fun m => comp m (e.functor.map (e.unitIso.inv.app X))) hnat
  have hs4 : comp (comp w (e.counitIso.inv.app (e.functor.obj X)))
      (e.functor.map (e.unitIso.inv.app X)) =
      comp w (comp (e.counitIso.inv.app (e.functor.obj X))
        (e.functor.map (e.unitIso.inv.app X))) := Category.assoc _ _ _
  have hs5 : comp w (comp (e.counitIso.inv.app (e.functor.obj X))
      (e.functor.map (e.unitIso.inv.app X))) =
      comp w (𝟙 (e.functor.obj X)) := congrArg _ htri
  exact hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans (Category.comp_id w)))))
theorem z251 [Pretriangulated FP] [IsTriangulated FP]
    {X Y Z X' Y' Z' : FP}
    {u : X ⟶ Y} {v : Y ⟶ Z} {w : Z ⟶ X⟦(1 : ℤ)⟧}
    {u' : X' ⟶ Y'} {v' : Y' ⟶ Z'} {w' : Z' ⟶ X'⟦(1 : ℤ)⟧}
    (hT₁ : Triangle.mk u v w ∈ distTriang FP)
    (hT₂ : Triangle.mk u' v' w' ∈ distTriang FP)
    (a : X ⟶ X') (b : Y ⟶ Y')
    (hab : comp u b = comp a u') :
    ∃ c : Z ⟶ Z',
      comp v c = comp b v' ∧
      comp w (a⟦(1 : ℤ)⟧') = comp c w' ∧
      Triangle.mk
        (FP.mat v 0 b u')
        (FP.mat w 0 c v')
        (comp (FP.mat (u⟦(1 : ℤ)⟧') 0 (a⟦(1 : ℤ)⟧') w')
          (FP.sumShiftIso Y X').hom) ∈ distTriang FP := by
  let eZ : Z⟦(-1 : ℤ)⟧⟦(1 : ℤ)⟧ ≅ Z := (shiftEquiv FP (1 : ℤ)).counitIso.app Z
  let w1 : Z⟦(-1 : ℤ)⟧ ⟶ X :=
    comp ((shiftEquiv FP (1 : ℤ)).inverse.map w)
      ((shiftEquiv FP (1 : ℤ)).unitIso.inv.app X)
  have hT1_inv : (Triangle.mk u v w).invRotate ∈ distTriang FP :=
    Pretriangulated.inv_rot_of_distTriang (Triangle.mk u v w) hT₁
  have hT1_inv_mor1 : (Triangle.mk u v w).invRotate.mor₁ = w1 := by
    change comp (-(w⟦(-1 : ℤ)⟧')) ((shiftEquiv FP (1 : ℤ)).unitIso.inv.app X) = w1
    rw [FP.neg_eq]
    rfl
  have hw1_u : comp w1 u = 0 := by
    rw [← hT1_inv_mor1]
    exact Pretriangulated.comp_distTriang_mor_zero₁₂ (Triangle.mk u v w).invRotate hT1_inv
  let u12 : Z⟦(-1 : ℤ)⟧ ⟶ FP.sum X X' := comp w1 (FP.inl X X')
  let v12 : FP.sum X X' ⟶ FP.sum Y X' := FP.mat u 0 0 (𝟙 X')
  let w12 : FP.sum Y X' ⟶ Z⟦(-1 : ℤ)⟧⟦(1 : ℤ)⟧ :=
    FP.desc (comp v eZ.inv) 0
  let u23 : FP.sum X X' ⟶ Y' := FP.desc (comp a u') u'
  let v23 : Y' ⟶ FP.sum (X⟦(1 : ℤ)⟧) Z' := comp v' (FP.inr (X⟦(1 : ℤ)⟧) Z')
  let w23 : FP.sum (X⟦(1 : ℤ)⟧) Z' ⟶ (FP.sum X X')⟦(1 : ℤ)⟧ :=
    comp (FP.mat (𝟙 (X⟦(1 : ℤ)⟧)) 0 (a⟦(1 : ℤ)⟧') w')
      (FP.sumShiftIso X X').hom
  let u13 : Z⟦(-1 : ℤ)⟧ ⟶ Y' := 0
  let v13 : Y' ⟶ FP.sum Z Y' := FP.inr Z Y'
  let w13 : FP.sum Z Y' ⟶ Z⟦(-1 : ℤ)⟧⟦(1 : ℤ)⟧ :=
    comp (FP.fst Z Y') eZ.inv
  have hcomm : comp u12 u23 = u13 := by
    dsimp [u12,u23,u13]
    rw [Category.assoc,FP.inl_desc,← hab,← Category.assoc,hw1_u,Limits.zero_comp]
  let Z0 : FP := (Pretriangulated.contractibleTriangle X).obj₃
  have h12 : Triangle.mk u12 v12 w12 ∈ distTriang FP := by
    have hsum := z74 hT1_inv (Pretriangulated.contractible_distinguished₁ X')
    let iso1 := (FP.sumZeroRightIso (Z⟦(-1 : ℤ)⟧) Z0 (Limits.isZero_zero FP)).symm
    refine Pretriangulated.isomorphic_distinguished _ hsum _
      (Triangle.isoMk _ _ iso1 (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
    · change comp u12 (𝟙 (FP.sum X X')) =
        comp (FP.inl (Z⟦(-1 : ℤ)⟧) Z0)
          (FP.mat (Triangle.mk u v w).invRotate.mor₁ 0 0 0)
      rw [Category.comp_id,hT1_inv_mor1]
      change u12 = comp (FP.inl (Z⟦(-1 : ℤ)⟧) Z0)
        (FP.mat w1 (0 : Z0 ⟶ X) (0 : Z⟦(-1 : ℤ)⟧ ⟶ X') (0 : Z0 ⟶ X'))
      rw [FP.inl_mat]
      dsimp [FP.lift,u12]
      rw [Limits.zero_comp,add_zero]
    · change comp (FP.mat u 0 0 (𝟙 X')) (𝟙 (FP.sum Y X')) =
        comp (𝟙 (FP.sum X X')) (FP.mat u 0 0 (𝟙 X'))
      rw [Category.comp_id,Category.id_comp]
    · change comp w12 ((FP.inl (Z⟦(-1 : ℤ)⟧) Z0)⟦(1 : ℤ)⟧') =
        comp (𝟙 (FP.sum Y X'))
          (comp (FP.mat (comp v eZ.inv) 0 0 0)
            (FP.sumShiftIso (Z⟦(-1 : ℤ)⟧) Z0).hom)
      rw [Category.id_comp,← FP.inl_sumShiftIso,← Category.assoc]
      congr 1
      apply FP.sum_hom_ext_left
      · dsimp [w12]
        rw [← Category.assoc,FP.inl_desc,FP.inl_mat]
        dsimp [FP.lift]
        rw [Limits.zero_comp,add_zero]
      · dsimp [w12]
        rw [← Category.assoc,FP.inr_desc,FP.inr_mat,Limits.zero_comp]
        dsimp [FP.lift]
        rw [Limits.zero_comp,Limits.zero_comp,add_zero]
  have h23 : Triangle.mk u23 v23 w23 ∈ distTriang FP := by
    have hsum := z74 (Pretriangulated.contractible_distinguished₂ X) hT₂
    let iso1 := FP.shearIso a
    let iso2 := (FP.sumZeroLeftIso Z0 (Limits.isZero_zero FP) Y').symm
    refine Pretriangulated.isomorphic_distinguished _ hsum _
      (Triangle.isoMk _ _ iso1 iso2 (Iso.refl _) ?_ ?_ ?_)
    · change comp u23 (FP.inr Z0 Y') =
        comp (FP.mat (𝟙 X) 0 a (𝟙 X')) (FP.mat 0 0 0 u')
      rw [FP.mat_comp]
      simp only [Category.id_comp,Limits.comp_zero,add_zero,zero_add]
      apply FP.sum_hom_ext_left
      · dsimp [u23]
        rw [← Category.assoc,FP.inl_desc,FP.inl_mat]
        dsimp [FP.lift]; rw [Limits.zero_comp,zero_add,Category.assoc]
      · dsimp [u23]
        rw [← Category.assoc,FP.inr_desc,FP.inr_mat]
        dsimp [FP.lift]; rw [Limits.zero_comp,zero_add]
    · change comp (comp v' (FP.inr (X⟦(1 : ℤ)⟧) Z')) (𝟙 _) =
        comp (FP.inr Z0 Y') (FP.mat 0 0 0 v')
      rw [Category.comp_id,FP.inr_mat]
      dsimp [FP.lift]
      rw [Limits.zero_comp,zero_add]
    · change comp
          (comp (FP.mat (𝟙 (X⟦(1 : ℤ)⟧)) 0 (a⟦(1 : ℤ)⟧') w')
            (FP.sumShiftIso X X').hom)
          ((FP.mat (𝟙 X) 0 a (𝟙 X'))⟦(1 : ℤ)⟧') =
        comp (𝟙 _)
          (comp (FP.mat (𝟙 (X⟦(1 : ℤ)⟧)) 0 0 w')
            (FP.sumShiftIso X X').hom)
      rw [Category.id_comp,Category.assoc,FP.sumShiftIso_mat_shift,← Category.assoc,
        FP.mat_comp]
      simp only [CategoryTheory.Functor.map_id,CategoryTheory.Functor.map_zero,
        Category.id_comp,Category.comp_id,Limits.zero_comp,Limits.comp_zero,
        add_zero,zero_add,FP.add_self]
  have h13 : Triangle.mk u13 v13 w13 ∈ distTriang FP := by
    have hsum := z74
      (Pretriangulated.contractible_distinguished₂ (Z⟦(-1 : ℤ)⟧))
      (Pretriangulated.contractible_distinguished₁ Y')
    let iso1 := (FP.sumZeroRightIso (Z⟦(-1 : ℤ)⟧) Z0 (Limits.isZero_zero FP)).symm
    let iso2 := (FP.sumZeroLeftIso Z0 (Limits.isZero_zero FP) Y').symm
    let iso3 : FP.sum Z Y' ≅ FP.sum (Z⟦(-1 : ℤ)⟧⟦(1 : ℤ)⟧) Y' :=
      { hom := FP.mat eZ.inv 0 0 (𝟙 Y')
        inv := FP.mat eZ.hom 0 0 (𝟙 Y')
        hom_inv_id := by
          rw [FP.mat_comp]
          simp only [Iso.inv_hom_id,Category.id_comp,Limits.zero_comp,Limits.comp_zero,
            add_zero,zero_add,FP.mat_id]
        inv_hom_id := by
          rw [FP.mat_comp]
          simp only [Iso.hom_inv_id,Category.id_comp,Limits.zero_comp,Limits.comp_zero,
            add_zero,zero_add,FP.mat_id] }
    refine Pretriangulated.isomorphic_distinguished _ hsum _
      (Triangle.isoMk _ _ iso1 iso2 iso3 ?_ ?_ ?_)
    · change comp (0 : Z⟦(-1 : ℤ)⟧ ⟶ Y') (FP.inr Z0 Y') =
        comp (FP.inl (Z⟦(-1 : ℤ)⟧) Z0) (FP.mat 0 0 0 0)
      rw [Limits.zero_comp,FP.inl_mat]
      dsimp [FP.lift]
      rw [Limits.zero_comp,Limits.zero_comp,add_zero]
    · change comp (FP.inr Z Y') (FP.mat eZ.inv 0 0 (𝟙 Y')) =
        comp (FP.inr Z0 Y') (FP.mat 0 0 0 (𝟙 Y'))
      rw [FP.inr_mat,FP.inr_mat]
    · change comp (comp (FP.fst Z Y') eZ.inv)
          ((FP.inl (Z⟦(-1 : ℤ)⟧) Z0)⟦(1 : ℤ)⟧') =
        comp (FP.mat eZ.inv 0 0 (𝟙 Y'))
          (comp (FP.mat (𝟙 (Z⟦(-1 : ℤ)⟧⟦(1 : ℤ)⟧)) 0 0 0)
            (FP.sumShiftIso (Z⟦(-1 : ℤ)⟧) Z0).hom)
      rw [← FP.inl_sumShiftIso,← Category.assoc,← Category.assoc]
      congr 1
      rw [FP.mat_comp]
      simp only [Category.comp_id,Limits.comp_zero,add_zero]
      apply FP.sum_hom_ext_left
      · rw [← Category.assoc,← Category.assoc,FP.inl_fst,Category.id_comp,FP.inl_mat]
        dsimp [FP.lift]
        rw [Limits.zero_comp,add_zero]
      · rw [← Category.assoc,← Category.assoc,FP.inr_fst,Limits.zero_comp,Limits.zero_comp,
          FP.inr_mat]
        dsimp [FP.lift]
        rw [Limits.zero_comp,Limits.zero_comp,add_zero]
  let O := Triangulated.someOctahedron hcomm h12 h23 h13
  have hm1_fst : comp O.m₁ (FP.fst Z Y') = FP.desc v 0 := by
    have h := O.comm₂
    dsimp [w13,w12] at h
    rw [← CategoryTheory.cancel_mono eZ.inv,Category.assoc,h]
    apply FP.sum_hom_ext_left
    · rw [← Category.assoc,FP.inl_desc,FP.inl_desc]
    · rw [← Category.assoc,FP.inr_desc,FP.inr_desc,Limits.zero_comp]
  have hm1_inl_fst : comp (FP.inl Y X')
      (comp O.m₁ (FP.fst Z Y')) = v := by
    rw [hm1_fst,FP.inl_desc]
  have hm1_inr_fst : comp (FP.inr Y X')
      (comp O.m₁ (FP.fst Z Y')) = 0 := by
    rw [hm1_fst,FP.inr_desc]
  let btilde : Y ⟶ Y' :=
    comp (FP.inl Y X') (comp O.m₁ (FP.snd Z Y'))
  have hm1_inr_snd : comp (FP.inr Y X')
      (comp O.m₁ (FP.snd Z Y')) = u' := by
    have h := congrArg (fun m => comp (FP.inr X X')
      (comp m (FP.snd Z Y'))) O.comm₁
    dsimp only [v12,u23,v13] at h
    rw [← Category.assoc (FP.inr X X'),← Category.assoc (FP.inr X X'),
      FP.inr_mat] at h
    dsimp only [FP.lift] at h
    rw [Limits.zero_comp,zero_add,Category.id_comp,Category.assoc (FP.inr Y X'),
      Category.assoc (FP.desc _ _),FP.inr_snd,Category.comp_id,
      FP.inr_desc] at h
    exact h
  have hu_btilde : comp u btilde = comp u b := by
    have h := congrArg (fun m => comp (FP.inl X X')
      (comp m (FP.snd Z Y'))) O.comm₁
    dsimp only [v12,u23,v13] at h
    rw [← Category.assoc (FP.inl X X'),← Category.assoc (FP.inl X X'),
      FP.inl_mat] at h
    dsimp only [FP.lift] at h
    rw [Limits.zero_comp,add_zero,Category.assoc u,Category.assoc u,
      Category.assoc (FP.desc _ _),FP.inr_snd,Category.comp_id,
      FP.inl_desc] at h
    exact h.trans hab.symm
  have hu_diff : comp u (b + btilde) = 0 := by
    rw [Preadditive.comp_add,hu_btilde,FP.add_self]
  obtain ⟨k0,hk⟩ := Pretriangulated.Triangle.yoneda_exact₂ (Triangle.mk u v w) hT₁ (b + btilde) hu_diff
  let k : Z ⟶ Y' := k0
  have hvk : comp v k = b + btilde := hk.symm
  have hm3_inr : comp (FP.inr Z Y') O.m₃ = v23 := O.comm₃
  have hm3_inr_fst : comp (FP.inr Z Y')
      (comp O.m₃ (FP.fst (X⟦(1 : ℤ)⟧) Z')) = 0 := by
    rw [← Category.assoc,hm3_inr]
    dsimp [v23]
    rw [Category.assoc,FP.inr_fst,Limits.comp_zero]
  have hm3_inr_snd : comp (FP.inr Z Y')
      (comp O.m₃ (FP.snd (X⟦(1 : ℤ)⟧) Z')) = v' := by
    rw [← Category.assoc,hm3_inr]
    dsimp [v23]
    rw [Category.assoc,FP.inr_snd,Category.comp_id]
  have hm3_w23 : comp O.m₃ (FP.mat (𝟙 (X⟦(1 : ℤ)⟧)) 0 (a⟦(1 : ℤ)⟧') w') =
      comp (FP.fst Z Y')
        (comp w (FP.inl (X⟦(1 : ℤ)⟧) (X'⟦(1 : ℤ)⟧))) := by
    have hw1_shift : comp eZ.inv (w1⟦(1 : ℤ)⟧') = w :=
      FP.counitInv_comp_shift_invRotate w
    have h := O.comm₄.symm
    dsimp only [w23,w13,u12] at h
    rw [CategoryTheory.Functor.map_comp,← FP.inl_sumShiftIso,← Category.assoc,
      ← Category.assoc,Category.assoc (FP.fst Z Y'),hw1_shift] at h
    exact (CategoryTheory.cancel_mono (FP.sumShiftIso X X').hom).mp (by
      simpa [Category.assoc] using h)
  have hm3_inl_fst : comp (FP.inl Z Y')
      (comp O.m₃ (FP.fst (X⟦(1 : ℤ)⟧) Z')) = w := by
    have h := congrArg (fun m => comp (FP.inl Z Y')
      (comp m (FP.fst (X⟦(1 : ℤ)⟧) (X'⟦(1 : ℤ)⟧)))) hm3_w23
    rw [Category.assoc O.m₃,FP.mat_fst] at h
    dsimp only [FP.desc] at h
    rw [Limits.comp_zero,add_zero,Category.comp_id,
      ← Category.assoc (FP.inl Z Y') (comp (FP.fst Z Y') _),
      ← Category.assoc (FP.inl Z Y') (FP.fst Z Y'),FP.inl_fst,Category.id_comp,
      Category.assoc w,FP.inl_fst,Category.comp_id] at h
    exact h
  let c0 : Z ⟶ Z' :=
    comp (FP.inl Z Y') (comp O.m₃ (FP.snd (X⟦(1 : ℤ)⟧) Z'))
  have hc0_w' : comp w (a⟦(1 : ℤ)⟧') = comp c0 w' := by
    have h := congrArg (fun m => comp (FP.inl Z Y')
      (comp m (FP.snd (X⟦(1 : ℤ)⟧) (X'⟦(1 : ℤ)⟧)))) hm3_w23
    have hL : comp (FP.inl Z Y')
        (comp (comp O.m₃
          (FP.mat (𝟙 (X⟦(1 : ℤ)⟧)) 0 (a⟦(1 : ℤ)⟧') w'))
          (FP.snd (X⟦(1 : ℤ)⟧) (X'⟦(1 : ℤ)⟧))) =
        comp w (a⟦(1 : ℤ)⟧') + comp c0 w' := by
      rw [Category.assoc O.m₃,FP.mat_snd]
      dsimp only [FP.desc]
      rw [Preadditive.comp_add,Preadditive.comp_add,
        ← Category.assoc O.m₃ (FP.fst _ _),← Category.assoc O.m₃ (FP.snd _ _),
        ← Category.assoc (FP.inl Z Y') (comp O.m₃ _),
        ← Category.assoc (FP.inl Z Y') (comp O.m₃ _),
        hm3_inl_fst]
    have hR : comp (FP.inl Z Y')
        (comp (comp (FP.fst Z Y')
          (comp w (FP.inl (X⟦(1 : ℤ)⟧) (X'⟦(1 : ℤ)⟧))))
          (FP.snd (X⟦(1 : ℤ)⟧) (X'⟦(1 : ℤ)⟧))) = 0 := by
      rw [← Category.assoc,← Category.assoc,FP.inl_fst,Category.id_comp,
        Category.assoc,FP.inl_snd,Limits.comp_zero]
    rw [hL,hR] at h
    have h0 : comp w (a⟦(1 : ℤ)⟧') + comp c0 w' = 0 := h
    calc comp w (a⟦(1 : ℤ)⟧')
        = comp w (a⟦(1 : ℤ)⟧') + (comp w (a⟦(1 : ℤ)⟧') +
            comp c0 w') := by rw [h0,add_zero]
      _ = (comp w (a⟦(1 : ℤ)⟧') + comp w (a⟦(1 : ℤ)⟧')) +
            comp c0 w' := by abel
      _ = 0 + comp c0 w' := by rw [FP.add_self]
      _ = comp c0 w' := zero_add _
  let c : Z ⟶ Z' := c0 + comp k v'
  let τ := FP.shearIso k
  have hm1_eq : O.m₁ = FP.mat v 0 btilde u' := by
    rw [FP.sum_hom_eq_mat O.m₁,hm1_inl_fst,hm1_inr_fst,hm1_inr_snd]
  have hm3_eq : O.m₃ = FP.mat w 0 c0 v' := by
    rw [FP.sum_hom_eq_mat O.m₃,hm3_inl_fst,hm3_inr_fst,hm3_inr_snd]
  have hM3_eq : comp w23 (v12⟦(1 : ℤ)⟧') =
      comp (FP.mat (u⟦(1 : ℤ)⟧') 0 (a⟦(1 : ℤ)⟧') w')
        (FP.sumShiftIso Y X').hom := by
    dsimp only [w23,v12]
    rw [Category.assoc,FP.sumShiftIso_mat_shift,← Category.assoc]
    simp only [CategoryTheory.Functor.map_id,CategoryTheory.Functor.map_zero]
    rw [FP.mat_comp]
    simp only [Category.id_comp,Category.comp_id,Limits.zero_comp,Limits.comp_zero,
      add_zero,zero_add]
  have hCone : Triangle.mk
      (FP.mat v 0 b u')
      (FP.mat w 0 c v')
      (comp (FP.mat (u⟦(1 : ℤ)⟧') 0 (a⟦(1 : ℤ)⟧') w')
        (FP.sumShiftIso Y X').hom) ∈ distTriang FP := by
    refine Pretriangulated.isomorphic_distinguished _ O.mem _
      (Triangle.isoMk _ _ (Iso.refl _) τ (Iso.refl _) ?_ ?_ ?_)
    · change comp (FP.mat v 0 b u') (FP.mat (𝟙 Z) 0 k (𝟙 Y')) =
        comp (𝟙 (FP.sum Y X')) O.m₁
      rw [Category.id_comp,hm1_eq,FP.mat_comp]
      simp only [Category.comp_id,Limits.zero_comp,Limits.comp_zero,
        add_zero,zero_add,hvk]
      congr 1
      calc (b + btilde) + b = (b + b) + btilde := by abel
        _ = 0 + btilde := by rw [FP.add_self]
        _ = btilde := zero_add _
    · change comp (FP.mat w 0 c v') (𝟙 (FP.sum (X⟦(1 : ℤ)⟧) Z')) =
        comp (FP.mat (𝟙 Z) 0 k (𝟙 Y')) O.m₃
      rw [Category.comp_id,hm3_eq,FP.mat_comp]
      dsimp only [c]
      simp only [Category.id_comp,Limits.zero_comp,Limits.comp_zero,
        add_zero,add_comm]
    · change comp
          (comp (FP.mat (u⟦(1 : ℤ)⟧') 0 (a⟦(1 : ℤ)⟧') w')
            (FP.sumShiftIso Y X').hom)
          ((𝟙 (FP.sum Y X'))⟦(1 : ℤ)⟧') =
        comp (𝟙 (FP.sum (X⟦(1 : ℤ)⟧) Z'))
          (comp w23 (v12⟦(1 : ℤ)⟧'))
      rw [CategoryTheory.Functor.map_id,Category.comp_id,Category.id_comp,hM3_eq]
  have hvc : comp v c = comp b v' := by
    have hzero : comp (FP.mat v 0 b u') (FP.mat w 0 c v') = 0 :=
      Pretriangulated.comp_distTriang_mor_zero₁₂ _ hCone
    rw [FP.mat_comp] at hzero
    have h21 := congrArg (fun m => comp (FP.inl Y X')
      (comp m (FP.snd (X⟦(1 : ℤ)⟧) Z'))) hzero
    rw [← Category.assoc,FP.inl_mat,FP.lift_snd,Limits.zero_comp,
      Limits.comp_zero] at h21
    calc comp v c
        = comp v c + (comp v c + comp b v') := by
            rw [h21,add_zero]
      _ = (comp v c + comp v c) + comp b v' := by abel
      _ = 0 + comp b v' := by rw [FP.add_self]
      _ = comp b v' := zero_add _
  have hcw' : comp w (a⟦(1 : ℤ)⟧') = comp c w' := by
    have hvw' : comp v' w' = 0 :=
      Pretriangulated.comp_distTriang_mor_zero₂₃ (Triangle.mk u' v' w') hT₂
    dsimp only [c]
    rw [Preadditive.add_comp,Category.assoc k v' w',hvw',Limits.comp_zero,add_zero,hc0_w']
  exact ⟨c,hvc,hcw',hCone⟩
lemma z92 (S : ExactSys)
    (M : Type) [AddCommGroup M] [Module Λ M] [Finite M]
    (hη : StableEq (S.η M) 0) :
    IsDeltaExact S (S.seq M).triangle := by
  have hu : StableEq (LinearMap.id : nuMod M →ₗ[Λ] nuMod M) (nuMap (S.u M)) := by
    have h1 : StableEq (S.u M) (LinearMap.id : M →ₗ[Λ] M) := by
      dsimp [ExactSys.u]
      simpa using StableEq.add (StableEq.refl (LinearMap.id : M →ₗ[Λ] M)) hη
    rw [← z207]
    exact h1.symm.nuMap
  exact ⟨M,inferInstance,inferInstance,inferInstance,
    (S.seq M).ι,(S.seq M).π,𝟙 (S.seq M).P0,𝟙 (S.seq M).P1,𝟙 (S.seq M).P2,LinearMap.id,
    (S.seq M).ι_inj,(S.seq M).exact0,(S.seq M).exact1,(S.seq M).exact2,(S.seq M).π_surj,
    rfl,LinearMap.id_comp _,(Category.comp_id _).trans (Category.id_comp _).symm,
    (Category.comp_id _).trans (Category.id_comp _).symm,
    (LinearMap.comp_id _).trans (LinearMap.id_comp _).symm,hu⟩
private lemma z246 (S : ExactSys)
    {U Y X : Type}
    [AddCommGroup U] [Module Λ U] [Finite U]
    [AddCommGroup Y] [Module Λ Y] [Finite Y]
    [AddCommGroup X] [Module Λ X] [Finite X]
    (w : U →ₗ[Λ] Y) (z : Y →ₗ[Λ] X)
    (hw : Function.Injective w) (hwz : ExactAt w z) (hz : Function.Surjective z) :
    let A0 := FP.sum (S.seq U).P1 (S.seq Y).P0
    let A1 := FP.sum (S.seq U).P2 (S.seq Y).P1
    let A2 := FP.sum ((S.seq U).P0⟦(1 : ℤ)⟧) (S.seq Y).P2
    let D0 : A0 ⟶ A1 := FP.mat (S.seq U).d1 0 (S.map1 w) (S.seq Y).d0
    let D1 : A1 ⟶ A2 := FP.mat (S.seq U).d2 0 (S.map2 w) (S.seq Y).d1
    let D2 : A2 ⟶ A0⟦(1 : ℤ)⟧ :=
      comp
        (FP.mat ((S.seq U).d0⟦(1 : ℤ)⟧') 0 ((S.map0 w)⟦(1 : ℤ)⟧') (S.seq Y).d2)
        (FP.sumShiftIso (S.seq U).P1 (S.seq Y).P0).hom
    let K : Type := LinearMap.ker D0.hom
    let jK : K →ₗ[Λ] A0.Mod := (LinearMap.ker D0.hom).subtype
    ∃ (β0 : K →ₗ[Λ] X) (σ0 : X →ₗ[Λ] K) (hbar_true : A2.Mod →ₗ[Λ] nuMod K)
      (m0 : A0 ⟶ (S.seq X).P0) (m1 : A1 ⟶ (S.seq X).P1) (m2 : A2 ⟶ (S.seq X).P2),
      (S.seq X).ι.comp β0 = ((S.map0 z).hom.comp (FP.snd (S.seq U).P1 (S.seq Y).P0).hom).comp jK ∧
      β0.comp σ0 = LinearMap.id ∧
      StableEq (σ0.comp β0) LinearMap.id ∧
      ExactAt D0.hom D1.hom ∧
      ExactAt D1.hom hbar_true ∧
      Function.Surjective hbar_true ∧
      ((z3 A0).toLinearMap.comp (nuMap jK)).comp hbar_true = D2.hom ∧
      m0.hom.comp jK = (S.seq X).ι.comp β0 ∧
      comp D0 m1 = comp m0 (S.seq X).d0 ∧
      comp D1 m2 = comp m1 (S.seq X).d1 ∧
      (S.seq X).π.comp m2.hom = (nuMap β0).comp hbar_true := by
  intro A0 A1 A2 D0 D1 D2 K jK
  have hzw : z.comp w = 0 := hwz.comp_eq_zero
  have hm0_zw : comp (S.map0 w) (S.map0 z) = 0 := by
    rw [← S.map0_comp,hzw,S.map0_zero]
  have hm1_zw : comp (S.map1 w) (S.map1 z) = 0 := by
    rw [← S.map1_comp,hzw,S.map1_zero]
  have hm2_zw : comp (S.map2 w) (S.map2 z) = 0 := by
    rw [← S.map2_comp,hzw,S.map2_zero]
  have hm0_ex := S.map0_exact w z hw hwz hz
  have hm1_ex := S.map1_exact w z hw hwz hz
  have hm2_ex := S.map2_exact w z hw hwz hz
  have hd2_w : comp (S.seq U).d2 ((S.map0 w)⟦(1 : ℤ)⟧') =
      comp (S.map2 w) (S.seq Y).d2 := by
    apply FP.hom_ext; intro p2
    change ((S.map0 w)⟦(1 : ℤ)⟧').hom (z3 (S.seq U).P0 (nuMap (S.seq U).ι ((S.seq U).π p2))) =
      z3 (S.seq Y).P0 (nuMap (S.seq Y).ι ((S.seq Y).π ((S.map2 w).hom p2)))
    rw [← z5 (S.map0 w)]
    congr 1; apply nuMod.ext
    have h1 := congrArg (fun f => f ((S.seq U).π p2).val) (S.map0_ι w)
    have h2 := congrArg (fun f => f p2) (S.π_map2 w)
    exact h1.trans (congrArg (S.seq Y).ι (congrArg nuMod.val h2).symm)
  have hjK : Function.Injective jK := Subtype.val_injective
  have hex_jK_D0 : ExactAt jK D0.hom := by
    rw [z7]; intro x
    exact ⟨fun hx => ⟨⟨x,hx⟩,rfl⟩,fun ⟨⟨_,hm⟩,hx⟩ => hx ▸ hm⟩
  let α0 : (S.seq U).P0.Mod →ₗ[Λ] K :=
    { toFun := fun u0 =>
        ⟨(FP.inl (S.seq U).P1 (S.seq Y).P0).hom ((S.seq U).d0.hom u0) +
          (FP.inr (S.seq U).P1 (S.seq Y).P0).hom ((S.map0 w).hom u0),by
          change D0.hom _ = 0
          apply (FP.sumEquivProd (S.seq U).P2 (S.seq Y).P1).injective
          ext : 1
          · change (FP.fst _ _).hom (D0.hom _) = 0
            rw [FP.mat_apply_fst,FP.fst_inl_add_inr,FH.zero_hom,
              LinearMap.zero_apply,add_zero]
            exact congrArg (fun f => f u0) (S.seq U).exact1.comp_eq_zero
          · change (FP.snd _ _).hom (D0.hom _) = 0
            rw [FP.mat_apply_snd,FP.fst_inl_add_inr,FP.snd_inl_add_inr]
            have hc := congrArg (fun (m : (S.seq U).P0 ⟶ (S.seq Y).P1) => m.hom u0) (S.map1_d0 w)
            simp only [FH.comp_hom,LinearMap.comp_apply] at hc
            rw [hc,z10]⟩
      map_add' := fun x y => by
        apply Subtype.ext
        change (FP.inl _ _).hom ((S.seq U).d0.hom (x + y)) +
            (FP.inr _ _).hom ((S.map0 w).hom (x + y)) =
          ((FP.inl _ _).hom ((S.seq U).d0.hom x) + (FP.inr _ _).hom ((S.map0 w).hom x)) +
          ((FP.inl _ _).hom ((S.seq U).d0.hom y) + (FP.inr _ _).hom ((S.map0 w).hom y))
        rw [map_add,map_add,map_add,map_add]; abel
      map_smul' := fun r x => by
        apply Subtype.ext
        change (FP.inl _ _).hom ((S.seq U).d0.hom (r • x)) +
            (FP.inr _ _).hom ((S.map0 w).hom (r • x)) =
          r • ((FP.inl _ _).hom ((S.seq U).d0.hom x) + (FP.inr _ _).hom ((S.map0 w).hom x))
        rw [map_smul,map_smul,map_smul,map_smul,smul_add] }
  have hα0_inj : Function.Injective α0 := by
    intro u1 u2 h
    have h2 := congrArg (fun k : K => (FP.snd (S.seq U).P1 (S.seq Y).P0).hom k.1) h
    dsimp [α0] at h2
    rw [FP.snd_inl_add_inr,FP.snd_inl_add_inr] at h2
    exact hm0_ex.1 h2
  have hβ0_kill : (S.seq X).d0.hom.comp (((S.map0 z).hom.comp (FP.snd (S.seq U).P1 (S.seq Y).P0).hom).comp jK) = 0 := by
    apply LinearMap.ext; rintro ⟨x,hx⟩
    have hx2 : (S.map1 w).hom ((FP.fst _ _).hom x) + (S.seq Y).d0.hom ((FP.snd _ _).hom x) = 0 := by
      have h := congrArg (FP.snd (S.seq U).P2 (S.seq Y).P1).hom hx
      rw [FP.mat_apply_snd,map_zero] at h; exact h
    have hd0y : (S.seq Y).d0.hom ((FP.snd _ _).hom x) = (S.map1 w).hom ((FP.fst _ _).hom x) := by
      calc (S.seq Y).d0.hom ((FP.snd _ _).hom x)
          = ((S.map1 w).hom ((FP.fst _ _).hom x) + (S.map1 w).hom ((FP.fst _ _).hom x)) +
              (S.seq Y).d0.hom ((FP.snd _ _).hom x) := by rw [z10,zero_add]
        _ = ((S.map1 w).hom ((FP.fst _ _).hom x) + (S.seq Y).d0.hom ((FP.snd _ _).hom x)) +
              (S.map1 w).hom ((FP.fst _ _).hom x) := by abel
        _ = 0 + (S.map1 w).hom ((FP.fst _ _).hom x) := by rw [hx2]
        _ = (S.map1 w).hom ((FP.fst _ _).hom x) := zero_add _
    change (S.seq X).d0.hom ((S.map0 z).hom ((FP.snd _ _).hom x)) = 0
    have hc := congrArg (fun (m : (S.seq Y).P0 ⟶ (S.seq X).P1) => m.hom ((FP.snd _ _).hom x))
      (S.map1_d0 z)
    simp only [FH.comp_hom,LinearMap.comp_apply] at hc
    rw [← hc,hd0y]
    exact congrArg (fun (m : (S.seq U).P1 ⟶ (S.seq X).P1) => m.hom ((FP.fst _ _).hom x)) hm1_zw
  obtain ⟨β0,hβ0⟩ := z111 (S.seq X).ι_inj (S.seq X).exact0
    (((S.map0 z).hom.comp (FP.snd (S.seq U).P1 (S.seq Y).P0).hom).comp jK) hβ0_kill
  have hex_α0_β0 : ExactAt α0 β0 := by
    rw [z7]; rintro ⟨x,hx⟩
    constructor
    · intro hβx
      have hz0 : (S.map0 z).hom ((FP.snd _ _).hom x) = 0 := by
        have h1 : (S.seq X).ι (β0 ⟨x,hx⟩) = (S.map0 z).hom ((FP.snd _ _).hom x) :=
          congrArg (fun f => f ⟨x,hx⟩) hβ0
        rw [hβx,map_zero] at h1; exact h1.symm
      obtain ⟨u0,hu0⟩ := ((z7 _ _).mp hm0_ex.2.1 _).mp hz0
      have hx2 : (S.map1 w).hom ((FP.fst _ _).hom x) + (S.seq Y).d0.hom ((FP.snd _ _).hom x) = 0 := by
        have h := congrArg (FP.snd (S.seq U).P2 (S.seq Y).P1).hom hx
        rw [FP.mat_apply_snd,map_zero] at h; exact h
      have hp1 : (FP.fst (S.seq U).P1 (S.seq Y).P0).hom x = (S.seq U).d0.hom u0 := by
        apply hm1_ex.1
        have hc := congrArg (fun (m : (S.seq U).P0 ⟶ (S.seq Y).P1) => m.hom u0) (S.map1_d0 w)
        simp only [FH.comp_hom,LinearMap.comp_apply] at hc
        rw [hc,hu0]
        calc (S.map1 w).hom ((FP.fst _ _).hom x)
            = (S.map1 w).hom ((FP.fst _ _).hom x) +
                ((S.seq Y).d0.hom ((FP.snd _ _).hom x) + (S.seq Y).d0.hom ((FP.snd _ _).hom x)) := by
                rw [z10,add_zero]
          _ = ((S.map1 w).hom ((FP.fst _ _).hom x) + (S.seq Y).d0.hom ((FP.snd _ _).hom x)) +
                (S.seq Y).d0.hom ((FP.snd _ _).hom x) := by abel
          _ = 0 + (S.seq Y).d0.hom ((FP.snd _ _).hom x) := by rw [hx2]
          _ = (S.seq Y).d0.hom ((FP.snd _ _).hom x) := zero_add _
      refine ⟨u0,Subtype.ext ?_⟩
      apply (FP.sumEquivProd (S.seq U).P1 (S.seq Y).P0).injective
      ext : 1
      · change (FP.fst _ _).hom (α0 u0).1 = (FP.fst _ _).hom x
        dsimp [α0]; rw [FP.fst_inl_add_inr,hp1]
      · change (FP.snd _ _).hom (α0 u0).1 = (FP.snd _ _).hom x
        dsimp [α0]; rw [FP.snd_inl_add_inr,hu0]
    · rintro ⟨u0,hu0⟩
      apply (S.seq X).ι_inj
      rw [map_zero,← hu0]
      have h1 : (S.seq X).ι (β0 (α0 u0)) = (S.map0 z).hom ((FP.snd _ _).hom (α0 u0).1) :=
        congrArg (fun f => f (α0 u0)) hβ0
      rw [h1]
      dsimp [α0]
      rw [FP.snd_inl_add_inr]
      exact congrArg (fun (m : (S.seq U).P0 ⟶ (S.seq X).P0) => m.hom u0) hm0_zw
  have hβ0_surj : Function.Surjective β0 := by
    intro x
    obtain ⟨p0,hp0⟩ := hm0_ex.2.2 ((S.seq X).ι x)
    have hd0y_kill : (S.map1 z).hom ((S.seq Y).d0.hom p0) = 0 := by
      have hc := congrArg (fun (m : (S.seq Y).P0 ⟶ (S.seq X).P1) => m.hom p0) (S.map1_d0 z)
      simp only [FH.comp_hom,LinearMap.comp_apply] at hc
      rw [hc,hp0]; exact congrArg (fun f => f x) (S.seq X).exact0.comp_eq_zero
    obtain ⟨p1,hp1⟩ := ((z7 _ _).mp hm1_ex.2.1 _).mp hd0y_kill
    have hd1u : (S.seq U).d1.hom p1 = 0 := by
      apply hm2_ex.1; rw [map_zero]
      have hc := congrArg (fun (m : (S.seq U).P1 ⟶ (S.seq Y).P2) => m.hom p1) (S.map2_d1 w)
      simp only [FH.comp_hom,LinearMap.comp_apply] at hc
      rw [hc,hp1]; exact congrArg (fun f => f p0) (S.seq Y).exact1.comp_eq_zero
    let k0 : K :=
      ⟨(FP.inl (S.seq U).P1 (S.seq Y).P0).hom p1 +
        (FP.inr (S.seq U).P1 (S.seq Y).P0).hom p0,by
        change D0.hom _ = 0
        apply (FP.sumEquivProd (S.seq U).P2 (S.seq Y).P1).injective
        ext : 1
        · change (FP.fst _ _).hom (D0.hom _) = 0
          rw [FP.mat_apply_fst,FP.fst_inl_add_inr,hd1u,FH.zero_hom,
            LinearMap.zero_apply,add_zero]
        · change (FP.snd _ _).hom (D0.hom _) = 0
          rw [FP.mat_apply_snd,FP.fst_inl_add_inr,FP.snd_inl_add_inr,hp1,
            z10]⟩
    refine ⟨k0,(S.seq X).ι_inj ?_⟩
    have h1 : (S.seq X).ι (β0 k0) = (S.map0 z).hom ((FP.snd _ _).hom k0.1) :=
      congrArg (fun f => f k0) hβ0
    rw [h1]; dsimp [k0]; rw [FP.snd_inl_add_inr,hp0]
  obtain ⟨ρ0,hρ0⟩ := S.inj (S.seq U).P0 α0 hα0_inj LinearMap.id
  have hσ_kill : (LinearMap.id - α0.comp ρ0).comp α0 = 0 := by
    apply LinearMap.ext; intro u0
    have h1 := congrArg (fun f => f u0) hρ0
    simp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,LinearMap.zero_apply] at h1 ⊢
    rw [h1,sub_self]
  obtain ⟨σ0,hσ0⟩ := z21 hex_α0_β0 hβ0_surj (LinearMap.id - α0.comp ρ0) hσ_kill
  have hβ0_σ0 : β0.comp σ0 = LinearMap.id := by
    apply LinearMap.ext; intro x
    obtain ⟨k,rfl⟩ := hβ0_surj x
    have h1 := congrArg (fun f => f k) hσ0
    simp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply] at h1 ⊢
    rw [h1,map_sub]
    have h2 : β0 (α0 (ρ0 k)) = 0 := congrArg (fun f => f (ρ0 k)) hex_α0_β0.comp_eq_zero
    rw [h2,sub_zero]
  have hσ0_β0_stab : StableEq (σ0.comp β0) LinearMap.id := by
    refine ⟨(S.seq U).P0,ρ0,α0,?_⟩
    rw [hσ0]
    apply LinearMap.ext; intro k
    change (k - α0 (ρ0 k)) - k = α0 (ρ0 k)
    rw [sub_eq_add_neg,sub_eq_add_neg,z153,z153]
    calc k + α0 (ρ0 k) + k = (k + k) + α0 (ρ0 k) := by abel
      _ = 0 + α0 (ρ0 k) := by rw [z10]
      _ = α0 (ρ0 k) := zero_add _
  have hd2U_ex : ExactAt (S.seq U).d1.hom (S.seq U).d2.hom :=
    (S.seq U).exact2.of_comp_inj
      ((z3 (S.seq U).P0).injective.comp (z61 (S.seq U).ι_inj))
  have hd2Y_ex : ExactAt (S.seq Y).d1.hom (S.seq Y).d2.hom :=
    (S.seq Y).exact2.of_comp_inj
      ((z3 (S.seq Y).P0).injective.comp (z61 (S.seq Y).ι_inj))
  have hjU1_ex : ExactAt ((z3 (S.seq U).P0).toLinearMap.comp (nuMap (S.seq U).ι))
      (((S.seq U).d0⟦(1 : ℤ)⟧').hom) := z114 (S.seq U).exact0
  have hd2U_d0_ex : ExactAt (S.seq U).d2.hom (((S.seq U).d0⟦(1 : ℤ)⟧').hom) :=
    hjU1_ex.of_comp_surj (S.seq U).π_surj
  have hex_D0_D1 : ExactAt D0.hom D1.hom := by
    rw [z7]; intro z1
    let p2 := (FP.fst (S.seq U).P2 (S.seq Y).P1).hom z1
    let p1' := (FP.snd (S.seq U).P2 (S.seq Y).P1).hom z1
    constructor
    · intro hz1
      have h1 : (S.seq U).d2.hom p2 = 0 := by
        have h := congrArg (FP.fst _ _).hom hz1
        rw [FP.mat_apply_fst,FH.zero_hom,LinearMap.zero_apply,add_zero,map_zero] at h
        exact h
      have h2 : (S.map2 w).hom p2 + (S.seq Y).d1.hom p1' = 0 := by
        have h := congrArg (FP.snd _ _).hom hz1
        rw [FP.mat_apply_snd,map_zero] at h; exact h
      obtain ⟨p1,hp1⟩ := ((z7 _ _).mp hd2U_ex p2).mp h1
      have hd1y : (S.seq Y).d1.hom (p1' + (S.map1 w).hom p1) = 0 := by
        rw [map_add]
        have hc := congrArg (fun (m : (S.seq U).P1 ⟶ (S.seq Y).P2) => m.hom p1) (S.map2_d1 w)
        simp only [FH.comp_hom,LinearMap.comp_apply] at hc
        rw [← hc,hp1,add_comm,h2]
      obtain ⟨p0,hp0⟩ := ((z7 _ _).mp (S.seq Y).exact1 _).mp hd1y
      refine ⟨(FP.inl _ _).hom p1 + (FP.inr _ _).hom p0,?_⟩
      apply (FP.sumEquivProd (S.seq U).P2 (S.seq Y).P1).injective
      ext : 1
      · change (FP.fst _ _).hom (D0.hom _) = p2
        rw [FP.mat_apply_fst,FP.fst_inl_add_inr,hp1,FH.zero_hom,
          LinearMap.zero_apply,add_zero]
      · change (FP.snd _ _).hom (D0.hom _) = p1'
        rw [FP.mat_apply_snd,FP.fst_inl_add_inr,FP.snd_inl_add_inr,hp0]
        calc (S.map1 w).hom p1 + (p1' + (S.map1 w).hom p1)
            = ((S.map1 w).hom p1 + (S.map1 w).hom p1) + p1' := by abel
          _ = 0 + p1' := by rw [z10]
          _ = p1' := zero_add _
    · rintro ⟨x0,rfl⟩
      apply (FP.sumEquivProd ((S.seq U).P0⟦(1 : ℤ)⟧) (S.seq Y).P2).injective
      ext : 1
      · change (FP.fst _ _).hom (D1.hom (D0.hom x0)) = 0
        rw [FP.mat_apply_fst,FP.mat_apply_fst]
        simp only [FH.zero_hom,LinearMap.zero_apply,add_zero]
        exact congrArg (fun f => f ((FP.fst _ _).hom x0)) hd2U_ex.comp_eq_zero
      · change (FP.snd _ _).hom (D1.hom (D0.hom x0)) = 0
        rw [FP.mat_apply_snd,FP.mat_apply_fst,FP.mat_apply_snd]
        simp only [FH.zero_hom,LinearMap.zero_apply,add_zero,map_add]
        have hc := congrArg (fun (m : (S.seq U).P1 ⟶ (S.seq Y).P2) => m.hom ((FP.fst _ _).hom x0))
          (S.map2_d1 w)
        have h0 := congrArg (fun f => f ((FP.snd _ _).hom x0)) (S.seq Y).exact1.comp_eq_zero
        simp only [FH.comp_hom,LinearMap.comp_apply,LinearMap.zero_apply] at hc h0
        rw [h0,add_zero,hc,z10]
  let D2_mat : A2 ⟶ FP.sum ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧) :=
    FP.mat ((S.seq U).d0⟦(1 : ℤ)⟧') 0 ((S.map0 w)⟦(1 : ℤ)⟧') (S.seq Y).d2
  have hD2_hom_eq : ∀ z2 : A2.Mod,D2.hom z2 = D2_mat.hom z2 := fun _ => rfl
  have hex_D1_D2 : ExactAt D1.hom D2.hom := by
    rw [z7]; intro z2
    let u0s := (FP.fst ((S.seq U).P0⟦(1 : ℤ)⟧) (S.seq Y).P2).hom z2
    let p2' := (FP.snd ((S.seq U).P0⟦(1 : ℤ)⟧) (S.seq Y).P2).hom z2
    constructor
    · intro hz2
      have hz2' : D2_mat.hom z2 = 0 := hz2
      have h1 : ((S.seq U).d0⟦(1 : ℤ)⟧').hom u0s = 0 := by
        have h := congrArg (FP.fst ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).hom hz2'
        rw [FP.mat_apply_fst,FH.zero_hom,LinearMap.zero_apply,add_zero,map_zero] at h
        exact h
      have h2 : ((S.map0 w)⟦(1 : ℤ)⟧').hom u0s + (S.seq Y).d2.hom p2' = 0 := by
        have h := congrArg (FP.snd ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).hom hz2'
        rw [FP.mat_apply_snd,map_zero] at h; exact h
      obtain ⟨p2,hp2⟩ := ((z7 _ _).mp hd2U_d0_ex u0s).mp h1
      have hd2y : (S.seq Y).d2.hom (p2' + (S.map2 w).hom p2) = 0 := by
        rw [map_add]
        have hc := congrArg (fun (m : (S.seq U).P2 ⟶ (S.seq Y).P0⟦(1 : ℤ)⟧) => m.hom p2) hd2_w
        simp only [FH.comp_hom,LinearMap.comp_apply] at hc
        rw [← hc,hp2,add_comm,h2]
      obtain ⟨p1',hp1'⟩ := ((z7 _ _).mp hd2Y_ex _).mp hd2y
      refine ⟨(FP.inl _ _).hom p2 + (FP.inr _ _).hom p1',?_⟩
      apply (FP.sumEquivProd ((S.seq U).P0⟦(1 : ℤ)⟧) (S.seq Y).P2).injective
      ext : 1
      · change (FP.fst _ _).hom (D1.hom _) = u0s
        rw [FP.mat_apply_fst,FP.fst_inl_add_inr,hp2,FH.zero_hom,
          LinearMap.zero_apply,add_zero]
      · change (FP.snd _ _).hom (D1.hom _) = p2'
        rw [FP.mat_apply_snd,FP.fst_inl_add_inr,FP.snd_inl_add_inr,hp1']
        calc (S.map2 w).hom p2 + (p2' + (S.map2 w).hom p2)
            = ((S.map2 w).hom p2 + (S.map2 w).hom p2) + p2' := by abel
          _ = 0 + p2' := by rw [z10]
          _ = p2' := zero_add _
    · rintro ⟨x1,rfl⟩
      change D2_mat.hom (D1.hom x1) = 0
      apply (FP.sumEquivProd ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).injective
      ext : 1
      · change (FP.fst _ _).hom (D2_mat.hom (D1.hom x1)) = 0
        rw [FP.mat_apply_fst,FP.mat_apply_fst]
        simp only [FH.zero_hom,LinearMap.zero_apply,add_zero]
        exact congrArg (fun f => f ((FP.fst _ _).hom x1)) hd2U_d0_ex.comp_eq_zero
      · change (FP.snd _ _).hom (D2_mat.hom (D1.hom x1)) = 0
        rw [FP.mat_apply_snd,FP.mat_apply_fst,FP.mat_apply_snd]
        simp only [FH.zero_hom,LinearMap.zero_apply,add_zero,map_add]
        have hc := congrArg (fun (m : (S.seq U).P2 ⟶ (S.seq Y).P0⟦(1 : ℤ)⟧) =>
          m.hom ((FP.fst _ _).hom x1)) hd2_w
        have h0 := congrArg (fun f => f ((FP.snd _ _).hom x1)) hd2Y_ex.comp_eq_zero
        simp only [FH.comp_hom,LinearMap.comp_apply,LinearMap.zero_apply] at hc h0
        rw [h0,add_zero,hc,z10]
  let jK1 : nuMod K →ₗ[Λ] (A0⟦(1 : ℤ)⟧).Mod :=
    (z3 A0).toLinearMap.comp (nuMap jK)
  have hjK1_inj : Function.Injective jK1 :=
    (z3 A0).injective.comp (z61 hjK)
  have hjK1_ex : ExactAt jK1 ((D0⟦(1 : ℤ)⟧').hom) := z114 hex_jK_D0
  have hD2_D0s : ((D0⟦(1 : ℤ)⟧').hom).comp D2.hom = 0 := by
    have hcomp : comp D2 (D0⟦(1 : ℤ)⟧') = 0 := by
      dsimp only [D2,D0]
      rw [Category.assoc,FP.sumShiftIso_mat_shift,← Category.assoc,
        CategoryTheory.Functor.map_zero,FP.mat_comp]
      have h11 : comp ((S.seq U).d0⟦(1 : ℤ)⟧') ((S.seq U).d1⟦(1 : ℤ)⟧') = 0 := by
        rw [← CategoryTheory.Functor.map_comp]
        have hz0 : comp (S.seq U).d0 (S.seq U).d1 = 0 :=
          FH.ext (S.seq U).exact1.comp_eq_zero
        rw [hz0,CategoryTheory.Functor.map_zero]
      have h21 : comp ((S.seq U).d0⟦(1 : ℤ)⟧') ((S.map1 w)⟦(1 : ℤ)⟧') +
          comp ((S.map0 w)⟦(1 : ℤ)⟧') ((S.seq Y).d0⟦(1 : ℤ)⟧') = 0 := by
        rw [← CategoryTheory.Functor.map_comp,← CategoryTheory.Functor.map_comp,
          S.map1_d0 w,FP.add_self]
      have h22 : comp (S.seq Y).d2 ((S.seq Y).d0⟦(1 : ℤ)⟧') = 0 := by
        apply FP.hom_ext; intro p2
        change ((S.seq Y).d0⟦(1 : ℤ)⟧').hom (z3 (S.seq Y).P0 (nuMap (S.seq Y).ι ((S.seq Y).π p2))) = 0
        rw [← z5 (S.seq Y).d0]
        have hz0 : (nuMap (S.seq Y).d0.hom) ((nuMap (S.seq Y).ι) ((S.seq Y).π p2)) = 0 := by
          apply nuMod.ext
          exact congrArg (fun f => f ((S.seq Y).π p2).val) (S.seq Y).exact0.comp_eq_zero
        rw [hz0,map_zero]; rfl
      simp only [Limits.zero_comp,Limits.comp_zero,add_zero,h11,h21,h22]
      have hmat0 : FP.mat (0 : (S.seq U).P0⟦(1 : ℤ)⟧ ⟶ (S.seq U).P2⟦(1 : ℤ)⟧)
          (0 : (S.seq Y).P2 ⟶ (S.seq U).P2⟦(1 : ℤ)⟧)
          (0 : (S.seq U).P0⟦(1 : ℤ)⟧ ⟶ (S.seq Y).P1⟦(1 : ℤ)⟧)
          (0 : (S.seq Y).P2 ⟶ (S.seq Y).P1⟦(1 : ℤ)⟧) = 0 := by
        apply FP.sum_hom_ext_left <;> apply FP.sum_hom_ext_right <;>
          simp [FP.inl_mat,FP.inr_mat,FP.lift_fst,FP.lift_snd]
      rw [hmat0,Limits.zero_comp]
    exact congrArg FH.hom hcomp
  obtain ⟨hbar_true,hhbar_true⟩ := z111 hjK1_inj hjK1_ex D2.hom hD2_D0s
  have hex_D1_hbar : ExactAt D1.hom hbar_true := by
    rw [z7] at hex_D1_D2 ⊢
    intro z2
    have h1 := congrArg (fun f => f z2) hhbar_true
    simp only [LinearMap.comp_apply] at h1
    rw [← hex_D1_D2 z2,← h1,map_eq_zero_iff jK1 hjK1_inj]
  have hhbar_surj : Function.Surjective hbar_true := by
    rintro ⟨⟨x,hx⟩⟩
    let p1 := (FP.fst (S.seq U).P1 (S.seq Y).P0).hom x
    let p0 := (FP.snd (S.seq U).P1 (S.seq Y).P0).hom x
    have hp1_d1 : (S.seq U).d1.hom p1 = 0 := by
      have h := congrArg (FP.fst (S.seq U).P2 (S.seq Y).P1).hom hx
      rw [FP.mat_apply_fst,FH.zero_hom,LinearMap.zero_apply,add_zero,map_zero] at h
      exact h
    have hp_d0 : (S.map1 w).hom p1 + (S.seq Y).d0.hom p0 = 0 := by
      have h := congrArg (FP.snd (S.seq U).P2 (S.seq Y).P1).hom hx
      rw [FP.mat_apply_snd,map_zero] at h; exact h
    obtain ⟨u0,hu0⟩ := ((z7 _ _).mp (S.seq U).exact1 p1).mp hp1_d1
    have hd0y : (S.seq Y).d0.hom (p0 + (S.map0 w).hom u0) = 0 := by
      rw [map_add]
      have hc := congrArg (fun (m : (S.seq U).P0 ⟶ (S.seq Y).P1) => m.hom u0) (S.map1_d0 w)
      simp only [FH.comp_hom,LinearMap.comp_apply] at hc
      rw [← hc,hu0,add_comm,hp_d0]
    obtain ⟨y,hy⟩ := ((z7 _ _).mp (S.seq Y).exact0 _).mp hd0y
    obtain ⟨p2',hp2'⟩ := (S.seq Y).π_surj ⟨y⟩
    let u0s : ((S.seq U).P0⟦(1 : ℤ)⟧).Mod := z3 (S.seq U).P0 ⟨u0⟩
    let z2 : A2.Mod := (FP.inl _ _).hom u0s + (FP.inr _ _).hom p2'
    refine ⟨z2,hjK1_inj ?_⟩
    have h1 : jK1 (hbar_true z2) = D2_mat.hom z2 := congrArg (fun f => f z2) hhbar_true
    rw [h1]
    apply (FP.sumEquivProd ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).injective
    ext : 1
    · change (FP.fst ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).hom (D2_mat.hom z2) =
        (FP.fst ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).hom (jK1 ⟨⟨x,hx⟩⟩)
      rw [FP.mat_apply_fst,FP.fst_inl_add_inr,FH.zero_hom,
        LinearMap.zero_apply,add_zero,← FP.fst_shift]
      change ((S.seq U).d0⟦(1 : ℤ)⟧').hom u0s =
        ((FP.fst (S.seq U).P1 (S.seq Y).P0)⟦(1 : ℤ)⟧').hom (z3 A0 ⟨x⟩)
      rw [← z5 (FP.fst (S.seq U).P1 (S.seq Y).P0)]
      dsimp [u0s]
      rw [← z5 (S.seq U).d0]
      congr 1; apply nuMod.ext; exact hu0
    · change (FP.snd ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).hom (D2_mat.hom z2) =
        (FP.snd ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).hom (jK1 ⟨⟨x,hx⟩⟩)
      rw [FP.mat_apply_snd,FP.fst_inl_add_inr,FP.snd_inl_add_inr,← FP.snd_shift]
      change ((S.map0 w)⟦(1 : ℤ)⟧').hom u0s + (S.seq Y).d2.hom p2' =
        ((FP.snd (S.seq U).P1 (S.seq Y).P0)⟦(1 : ℤ)⟧').hom (z3 A0 ⟨x⟩)
      rw [← z5 (FP.snd (S.seq U).P1 (S.seq Y).P0)]
      dsimp [u0s]
      rw [← z5 (S.map0 w)]
      change z3 (S.seq Y).P0 (nuMap (S.map0 w).hom ⟨u0⟩) +
        z3 (S.seq Y).P0 (nuMap (S.seq Y).ι ((S.seq Y).π p2')) =
        z3 (S.seq Y).P0 ⟨p0⟩
      rw [← map_add]; congr 1; apply nuMod.ext
      rw [hp2']
      change (S.map0 w).hom u0 + (S.seq Y).ι y = p0
      rw [hy]
      calc (S.map0 w).hom u0 + (p0 + (S.map0 w).hom u0)
          = ((S.map0 w).hom u0 + (S.map0 w).hom u0) + p0 := by abel
        _ = 0 + p0 := by rw [z10]
        _ = p0 := zero_add _
  let m0 : A0 ⟶ (S.seq X).P0 := FP.desc 0 (S.map0 z)
  let m1 : A1 ⟶ (S.seq X).P1 := FP.desc 0 (S.map1 z)
  let m2 : A2 ⟶ (S.seq X).P2 := FP.desc 0 (S.map2 z)
  have hm0_jK : m0.hom.comp jK = (S.seq X).ι.comp β0 := by
    apply LinearMap.ext; intro k
    have h1 := congrArg (fun f => f k) hβ0
    simp only [m0,FP.desc,FH.add_hom,FH.comp_hom,FH.zero_hom,
      LinearMap.comp_apply,LinearMap.add_apply,LinearMap.zero_apply,zero_add] at h1 ⊢
    exact h1.symm
  have hm1_D0 : comp D0 m1 = comp m0 (S.seq X).d0 := by
    apply FP.sum_hom_ext_left
    · dsimp [D0,m0,m1]
      rw [← Category.assoc,FP.inl_mat,FP.lift_desc,← Category.assoc,FP.inl_desc,
        Limits.zero_comp,Limits.comp_zero,zero_add,hm1_zw]
    · dsimp [D0,m0,m1]
      rw [← Category.assoc,FP.inr_mat,FP.lift_desc,← Category.assoc,FP.inr_desc,
        Limits.zero_comp,zero_add,S.map1_d0 z]
  have hm2_D1 : comp D1 m2 = comp m1 (S.seq X).d1 := by
    apply FP.sum_hom_ext_left
    · dsimp [D1,m1,m2]
      rw [← Category.assoc,FP.inl_mat,FP.lift_desc,← Category.assoc,FP.inl_desc,
        Limits.zero_comp,Limits.comp_zero,zero_add,hm2_zw]
    · dsimp [D1,m1,m2]
      rw [← Category.assoc,FP.inr_mat,FP.lift_desc,← Category.assoc,FP.inr_desc,
        Limits.zero_comp,zero_add,S.map2_d1 z]
  have hm2_πX : (S.seq X).π.comp m2.hom = (nuMap β0).comp hbar_true := by
    apply LinearMap.ext; intro z2
    let u0s := (FP.fst ((S.seq U).P0⟦(1 : ℤ)⟧) (S.seq Y).P2).hom z2
    let p2' := (FP.snd ((S.seq U).P0⟦(1 : ℤ)⟧) (S.seq Y).P2).hom z2
    let u0 : (S.seq U).P0.Mod := ((z3 (S.seq U).P0).symm u0s).val
    have hD2_snd : (FP.snd ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).hom
        (jK1 (hbar_true z2)) =
        (FP.snd ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).hom (D2_mat.hom z2) :=
      congrArg (fun f => (FP.snd ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).hom (f z2))
        hhbar_true
    rw [FP.mat_apply_snd] at hD2_snd
    have hL : (FP.snd ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).hom
        (jK1 (hbar_true z2)) =
        z3 (S.seq Y).P0 ⟨(FP.snd _ _).hom (hbar_true z2).val.1⟩ := by
      rw [← FP.snd_shift]
      change ((FP.snd (S.seq U).P1 (S.seq Y).P0)⟦(1 : ℤ)⟧').hom
        (z3 A0 (nuMap jK (hbar_true z2))) = _
      rw [← z5 (FP.snd (S.seq U).P1 (S.seq Y).P0)]
      rfl
    have hR : ((S.map0 w)⟦(1 : ℤ)⟧').hom u0s + (S.seq Y).d2.hom p2' =
        z3 (S.seq Y).P0 ⟨(S.map0 w).hom u0 + (S.seq Y).ι ((S.seq Y).π p2').val⟩ := by
      have hu0_eq : u0s = z3 (S.seq U).P0 ⟨u0⟩ :=
        ((z3 (S.seq U).P0).apply_symm_apply u0s).symm
      rw [hu0_eq,← z5 (S.map0 w)]
      change z3 (S.seq Y).P0 (nuMap (S.map0 w).hom ⟨u0⟩) +
        z3 (S.seq Y).P0 (nuMap (S.seq Y).ι ((S.seq Y).π p2')) = _
      rw [← map_add]; rfl
    rw [hL,hR] at hD2_snd
    have hp0_eq : (FP.snd _ _).hom (hbar_true z2).val.1 =
        (S.map0 w).hom u0 + (S.seq Y).ι ((S.seq Y).π p2').val :=
      congrArg nuMod.val ((z3 (S.seq Y).P0).injective hD2_snd)
    apply nuMod.ext
    apply (S.seq X).ι_inj
    have hβ : (S.seq X).ι (β0 (hbar_true z2).val) =
        (S.map0 z).hom ((FP.snd _ _).hom (hbar_true z2).val.1) :=
      congrArg (fun f => f (hbar_true z2).val) hβ0
    have hm2_eq : m2.hom z2 = (S.map2 z).hom p2' := by
      simp [m2,p2',FP.desc]
    change (S.seq X).ι ((S.seq X).π (m2.hom z2)).val = (S.seq X).ι (β0 (hbar_true z2).val)
    rw [hm2_eq,hβ,hp0_eq,map_add]
    have hzw0 := congrArg (fun (m : (S.seq U).P0 ⟶ (S.seq X).P0) => m.hom u0) hm0_zw
    simp only [FH.comp_hom,FH.zero_hom,LinearMap.comp_apply,LinearMap.zero_apply] at hzw0
    rw [hzw0,zero_add]
    have hπ := congrArg (fun f => f p2') (S.π_map2 z)
    have hι := congrArg (fun f => f ((S.seq Y).π p2').val) (S.map0_ι z)
    simp only [LinearMap.comp_apply] at hπ hι
    rw [congrArg nuMod.val hπ]
    exact hι.symm
  exact ⟨β0,σ0,hbar_true,m0,m1,m2,
    hβ0,hβ0_σ0,hσ0_β0_stab,hex_D0_D1,hex_D1_hbar,hhbar_surj,
    hhbar_true,hm0_jK,hm1_D0,hm2_D1,hm2_πX⟩
private lemma z258 (S : ExactSys)
    {U Y X : Type}
    [AddCommGroup U] [Module Λ U] [Finite U]
    [AddCommGroup Y] [Module Λ Y] [Finite Y]
    [AddCommGroup X] [Module Λ X] [Finite X]
    (w : U →ₗ[Λ] Y) (_z : Y →ₗ[Λ] X)
    (f2t : (S.seq U).P2 ⟶ (S.seq Y).P2)
    (hf2t_d1 : comp (S.seq U).d1 f2t = comp (S.map1 w) (S.seq Y).d1)
    (hf2t_d2 : comp (S.seq U).d2 ((S.map0 w)⟦(1 : ℤ)⟧') =
      comp f2t (S.seq Y).d2)
    (hT_tilde_delta : IsDeltaExact S
      (Triangle.mk
        (FP.mat (S.seq U).d1 0 (S.map1 w) (S.seq Y).d0)
        (FP.mat (S.seq U).d2 0 f2t (S.seq Y).d1)
        (comp
          (FP.mat ((S.seq U).d0⟦(1 : ℤ)⟧') 0 ((S.map0 w)⟦(1 : ℤ)⟧') (S.seq Y).d2)
          (FP.sumShiftIso (S.seq U).P1 (S.seq Y).P0).hom)))
    (β0 : LinearMap.ker (FP.mat (S.seq U).d1 0 (S.map1 w) (S.seq Y).d0).hom →ₗ[Λ] X)
    (σ0 : X →ₗ[Λ] LinearMap.ker (FP.mat (S.seq U).d1 0 (S.map1 w) (S.seq Y).d0).hom)
    (hbar_true : (FP.sum ((S.seq U).P0⟦(1 : ℤ)⟧) (S.seq Y).P2).Mod →ₗ[Λ]
      nuMod (LinearMap.ker (FP.mat (S.seq U).d1 0 (S.map1 w) (S.seq Y).d0).hom))
    (m0 : FP.sum (S.seq U).P1 (S.seq Y).P0 ⟶ (S.seq X).P0)
    (m1 : FP.sum (S.seq U).P2 (S.seq Y).P1 ⟶ (S.seq X).P1)
    (m2 : FP.sum ((S.seq U).P0⟦(1 : ℤ)⟧) (S.seq Y).P2 ⟶ (S.seq X).P2)
    (hσ0_β0_stab : StableEq (σ0.comp β0) LinearMap.id)
    (hex_D0_D1 : ExactAt (FP.mat (S.seq U).d1 0 (S.map1 w) (S.seq Y).d0).hom
      (FP.mat (S.seq U).d2 0 (S.map2 w) (S.seq Y).d1).hom)
    (hex_D1_hbar : ExactAt (FP.mat (S.seq U).d2 0 (S.map2 w) (S.seq Y).d1).hom hbar_true)
    (hhbar_surj : Function.Surjective hbar_true)
    (hhbar_true : ((z3 (FP.sum (S.seq U).P1 (S.seq Y).P0)).toLinearMap.comp
      (nuMap (LinearMap.ker (FP.mat (S.seq U).d1 0 (S.map1 w) (S.seq Y).d0).hom).subtype)).comp hbar_true =
      (comp
        (FP.mat ((S.seq U).d0⟦(1 : ℤ)⟧') 0 ((S.map0 w)⟦(1 : ℤ)⟧') (S.seq Y).d2)
        (FP.sumShiftIso (S.seq U).P1 (S.seq Y).P0).hom).hom)
    (hm0_jK : m0.hom.comp (LinearMap.ker (FP.mat (S.seq U).d1 0 (S.map1 w) (S.seq Y).d0).hom).subtype =
      (S.seq X).ι.comp β0)
    (hm1_D0 : comp (FP.mat (S.seq U).d1 0 (S.map1 w) (S.seq Y).d0) m1 =
      comp m0 (S.seq X).d0)
    (hm2_D1 : comp (FP.mat (S.seq U).d2 0 (S.map2 w) (S.seq Y).d1) m2 =
      comp m1 (S.seq X).d1)
    (hm2_πX : (S.seq X).π.comp m2.hom = (nuMap β0).comp hbar_true) :
    let A0 := FP.sum (S.seq U).P1 (S.seq Y).P0
    let K := LinearMap.ker (FP.mat (S.seq U).d1 0 (S.map1 w) (S.seq Y).d0).hom
    ∃ (h2_un : (S.seq U).P0.Mod →ₗ[Λ] Y)
      (h3_raw : (S.seq U).P1 ⟶ (S.seq Y).P0)
      (ψ_raw : K →ₗ[Λ] K),
      StableEq (ψ_raw - LinearMap.id) (S.η K) ∧
      h3_raw.hom.comp (S.seq U).d0.hom = (S.seq Y).ι.comp h2_un ∧
      ∀ k : K,K.subtype ((ψ_raw - LinearMap.id : K →ₗ[Λ] K) k) =
        (FP.inr (S.seq U).P1 (S.seq Y).P0).hom
          (h3_raw.hom ((FP.fst (S.seq U).P1 (S.seq Y).P0).hom k.1)) := by
  intro A0 K
  let A1 := FP.sum (S.seq U).P2 (S.seq Y).P1
  let A2 := FP.sum ((S.seq U).P0⟦(1 : ℤ)⟧) (S.seq Y).P2
  let D0 : A0 ⟶ A1 := FP.mat (S.seq U).d1 0 (S.map1 w) (S.seq Y).d0
  let D1 : A1 ⟶ A2 := FP.mat (S.seq U).d2 0 (S.map2 w) (S.seq Y).d1
  let D1t : A1 ⟶ A2 := FP.mat (S.seq U).d2 0 f2t (S.seq Y).d1
  let D2_mat : A2 ⟶ FP.sum ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧) :=
    FP.mat ((S.seq U).d0⟦(1 : ℤ)⟧') 0 ((S.map0 w)⟦(1 : ℤ)⟧') (S.seq Y).d2
  let D2 : A2 ⟶ A0⟦(1 : ℤ)⟧ :=
    comp D2_mat (FP.sumShiftIso (S.seq U).P1 (S.seq Y).P0).hom
  let jK : K →ₗ[Λ] A0.Mod := K.subtype
  have hjK : Function.Injective jK := Subtype.val_injective
  have hex_jK_D0 : ExactAt jK D0.hom := by
    rw [z7]; intro x
    exact ⟨fun hx => ⟨⟨x,hx⟩,rfl⟩,fun ⟨⟨_,hm⟩,hx⟩ => hx ▸ hm⟩
  let jK1 : nuMod K →ₗ[Λ] (A0⟦(1 : ℤ)⟧).Mod :=
    (z3 A0).toLinearMap.comp (nuMap jK)
  have hjK1_inj : Function.Injective jK1 :=
    (z3 A0).injective.comp (z61 hjK)
  have hjK1_ex : ExactAt jK1 ((D0⟦(1 : ℤ)⟧').hom) := z114 hex_jK_D0
  have hd2_w : comp (S.seq U).d2 ((S.map0 w)⟦(1 : ℤ)⟧') =
      comp (S.map2 w) (S.seq Y).d2 := by
    apply FP.hom_ext; intro p2
    change ((S.map0 w)⟦(1 : ℤ)⟧').hom (z3 (S.seq U).P0 (nuMap (S.seq U).ι ((S.seq U).π p2))) =
      z3 (S.seq Y).P0 (nuMap (S.seq Y).ι ((S.seq Y).π ((S.map2 w).hom p2)))
    rw [← z5 (S.map0 w)]
    congr 1; apply nuMod.ext
    have h1 := congrArg (fun f => f ((S.seq U).π p2).val) (S.map0_ι w)
    have h2 := congrArg (fun f => f p2) (S.π_map2 w)
    exact h1.trans (congrArg (S.seq Y).ι (congrArg nuMod.val h2).symm)
  let δ2 : (S.seq U).P2 ⟶ (S.seq Y).P2 := f2t + S.map2 w
  have hδ2_d1 : δ2.hom.comp (S.seq U).d1.hom = 0 := by
    have h : comp (S.seq U).d1 δ2 = 0 := by
      dsimp [δ2]
      rw [Preadditive.comp_add,hf2t_d1,S.map2_d1 w,FP.add_self]
    exact congrArg FH.hom h
  have hδ2_d2 : comp δ2 (S.seq Y).d2 = 0 := by
    dsimp [δ2]
    rw [Preadditive.add_comp,← hf2t_d2,← hd2_w,FP.add_self]
  obtain ⟨δbar,hδbar⟩ := z21 (S.seq U).exact2 (S.seq U).π_surj δ2.hom hδ2_d1
  have hδbar_d2 : (S.seq Y).d2.hom.comp δbar = 0 := by
    apply LinearMap.ext; intro u
    obtain ⟨p2,rfl⟩ := (S.seq U).π_surj u
    have h1 := congrArg (fun f => f p2) hδbar
    have h2 := congrArg (fun (m : (S.seq U).P2 ⟶ (S.seq Y).P0⟦(1 : ℤ)⟧) => m.hom p2) hδ2_d2
    simp only [FH.comp_hom,FH.zero_hom,LinearMap.comp_apply,LinearMap.zero_apply] at h1 h2 ⊢
    rw [h1,h2]
  let jU1 : nuMod U →ₗ[Λ] ((S.seq U).P0⟦(1 : ℤ)⟧).Mod :=
    (z3 (S.seq U).P0).toLinearMap.comp (nuMap (S.seq U).ι)
  have hjU1_inj : Function.Injective jU1 :=
    (z3 (S.seq U).P0).injective.comp (z61 (S.seq U).ι_inj)
  have hjU1_ex : ExactAt jU1 (((S.seq U).d0⟦(1 : ℤ)⟧').hom) := z114 (S.seq U).exact0
  obtain ⟨h2h,hh2h⟩ := S.inj (S.seq Y).P2 jU1 hjU1_inj δbar
  let h2 : (S.seq U).P0⟦(1 : ℤ)⟧ ⟶ (S.seq Y).P2 := ⟨h2h⟩
  have hd2_h2 : comp (S.seq U).d2 h2 = δ2 := by
    apply FP.hom_ext; intro p2
    have h1 := congrArg (fun f => f ((S.seq U).π p2)) hh2h
    have h2' := congrArg (fun f => f p2) hδbar
    exact h1.trans h2'
  have hh2_d2_kill : ((S.seq Y).d2.hom.comp h2.hom).comp jU1 = 0 := by
    rw [LinearMap.comp_assoc,hh2h,hδbar_d2]
  obtain ⟨h3h,hh3h⟩ := z32 S hjU1_ex ((S.seq Y).P0⟦(1 : ℤ)⟧)
    ((S.seq Y).d2.hom.comp h2.hom) hh2_d2_kill
  let h3 : (S.seq U).P1⟦(1 : ℤ)⟧ ⟶ (S.seq Y).P0⟦(1 : ℤ)⟧ := ⟨h3h⟩
  have hd0_h3 : comp ((S.seq U).d0⟦(1 : ℤ)⟧') h3 =
      comp h2 (S.seq Y).d2 := FH.ext hh3h
  let θ2 : A2 ⟶ A2 := FP.mat (𝟙 _) 0 h2 (𝟙 _)
  let θ3_mat : FP.sum ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧) ⟶
      FP.sum ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧) :=
    FP.mat (𝟙 _) 0 h3 (𝟙 _)
  let θ3 : A0⟦(1 : ℤ)⟧ ⟶ A0⟦(1 : ℤ)⟧ :=
    comp (FP.sumShiftIso (S.seq U).P1 (S.seq Y).P0).inv
      (comp θ3_mat (FP.sumShiftIso (S.seq U).P1 (S.seq Y).P0).hom)
  have hD1_θ2 : comp D1 θ2 = D1t := by
    dsimp [D1,θ2,D1t]
    rw [FP.mat_comp]
    simp only [Category.comp_id,Limits.zero_comp,Limits.comp_zero,
      add_zero,zero_add,hd2_h2]
    congr 1; dsimp [δ2]
    calc (f2t + S.map2 w) + S.map2 w = f2t + (S.map2 w + S.map2 w) := by abel
      _ = f2t + 0 := by rw [FP.add_self]
      _ = f2t := add_zero _
  have hθ2_D2 : comp θ2 D2 = comp D2 θ3 := by
    dsimp only [D2,θ3]
    rw [← Category.assoc,Category.assoc D2_mat,← Category.assoc (FP.sumShiftIso _ _).hom,
      Iso.hom_inv_id,Category.id_comp,← Category.assoc]
    congr 1
    dsimp [θ2,D2_mat,θ3_mat]
    rw [FP.mat_comp,FP.mat_comp]
    simp only [Category.id_comp,Category.comp_id,Limits.zero_comp,Limits.comp_zero,
      add_zero,zero_add,hd0_h3]
    congr 1; exact add_comm _ _
  have hhbar_true' : jK1.comp hbar_true = D2.hom := hhbar_true
  have hD2_D0s : ((D0⟦(1 : ℤ)⟧').hom).comp D2.hom = 0 := by
    apply LinearMap.ext; intro z2
    have h1 : jK1 (hbar_true z2) = D2.hom z2 := congrArg (fun f => f z2) hhbar_true'
    change ((D0⟦(1 : ℤ)⟧').hom) (D2.hom z2) = 0
    rw [← h1]
    exact congrArg (fun f => f (hbar_true z2)) hjK1_ex.comp_eq_zero
  have hθ3_jK1_kill : ((D0⟦(1 : ℤ)⟧').hom).comp (θ3.hom.comp jK1) = 0 := by
    apply LinearMap.ext; intro k
    obtain ⟨z2,rfl⟩ := hhbar_surj k
    have h1 := congrArg (fun f => f z2) hhbar_true'
    have h2' := congrArg (fun (m : A2 ⟶ A0⟦(1 : ℤ)⟧) => m.hom z2) hθ2_D2
    have h3' := congrArg (fun f => f (θ2.hom z2)) hD2_D0s
    simp only [FH.comp_hom,LinearMap.comp_apply,LinearMap.zero_apply] at h1 h2' h3' ⊢
    rw [h1,← h2',h3']
  obtain ⟨ψ,hψ⟩ := z111 hjK1_inj hjK1_ex (θ3.hom.comp jK1) hθ3_jK1_kill
  have hbar_θ2 : hbar_true.comp θ2.hom = ψ.comp hbar_true := by
    apply LinearMap.ext; intro z2
    apply hjK1_inj
    have h1 := congrArg (fun f => f (θ2.hom z2)) hhbar_true'
    have h2' := congrArg (fun (m : A2 ⟶ A0⟦(1 : ℤ)⟧) => m.hom z2) hθ2_D2
    have h3' := congrArg (fun f => f z2) hhbar_true'
    have h4' := congrArg (fun f => f (hbar_true z2)) hψ
    simp only [FH.comp_hom,LinearMap.comp_apply] at h1 h2' h3' h4' ⊢
    rw [h1,h2',← h3',← h4']
  have hθ2_inv : comp θ2 θ2 = 𝟙 A2 := by
    dsimp [θ2]
    rw [FP.mat_comp]
    simp only [Category.id_comp,Category.comp_id,Limits.zero_comp,Limits.comp_zero,
      add_zero,zero_add,FP.add_self,FP.mat_id]
    rfl
  let eθ2 : A2.Mod ≃ₗ[Λ] A2.Mod :=
    { toFun := θ2.hom,invFun := θ2.hom
      left_inv := fun x => congrArg (fun (m : A2 ⟶ A2) => m.hom x) hθ2_inv
      right_inv := fun x => congrArg (fun (m : A2 ⟶ A2) => m.hom x) hθ2_inv
      map_add' := θ2.hom.map_add,map_smul' := θ2.hom.map_smul }
  have hex_D0_D1t : ExactAt D0.hom D1t.hom := by
    rw [← hD1_θ2]; exact hex_D0_D1.of_comp_inj eθ2.injective
  have hex_D1t_hbar : ExactAt D1t.hom hbar_true := by
    have hD1t_D2 : ExactAt D1t.hom D2.hom := by
      rcases hT_tilde_delta with ⟨M',_,_,_,j',hbar',_,_,_,_,
        hj',_,_,hex2',_,hmor3',_,_,_,_,_⟩
      have hex2'' : ExactAt D1t.hom hbar' := hex2'
      have hmor3'' : D2.hom = ((z3 A0).toLinearMap.comp (nuMap j')).comp hbar' := hmor3'
      rw [hmor3'']
      exact hex2''.of_comp_inj ((z3 A0).injective.comp (z61 hj'))
    rw [z7] at hD1t_D2 ⊢
    intro z2
    have h1 := congrArg (fun f => f z2) hhbar_true'
    simp only [LinearMap.comp_apply] at h1
    rw [← hD1t_D2 z2,← h1,map_eq_zero_iff jK1 hjK1_inj]
  obtain ⟨b0,b1,b2,ctilde,hb0,hb1,hb2,hctilde⟩ :=
    z72 S hjK hex_jK_D0 hex_D0_D1t hex_D1t_hbar hhbar_surj
      (S.seq K).exact0 (S.seq K).exact1 (S.seq K).exact2 LinearMap.id
  have hctilde_stab : StableEq ctilde (nuMap (S.u K)) :=
    IsDeltaExact.stableEq_comparison S hT_tilde_delta hjK hex_jK_D0 hex_D0_D1t hex_D1t_hbar
      hhbar_surj hhbar_true.symm (hb0.trans (LinearMap.comp_id _)) hb1 hb2 hctilde
  have hcomp_true : StableEq ((nuMap β0).comp (ctilde.comp ψ)) (nuMap β0) := by
    refine z34 S hjK hex_jK_D0 hex_D0_D1 hex_D1_hbar hhbar_surj
      (S.seq X).exact0 (S.seq X).exact1 (S.seq X).exact2
      (g := β0) (g' := β0)
      (a0 := comp b0 (S.map0 β0))
      (a1 := comp b1 (S.map1 β0))
      (a2 := comp θ2 (comp b2 (S.map2 β0)))
      (c := (nuMap β0).comp (ctilde.comp ψ))
      (b0 := m0) (b1 := m1) (b2 := m2) (c' := nuMap β0)
      ?_ ?_ ?_ ?_ hm0_jK hm1_D0 hm2_D1 hm2_πX (StableEq.refl β0)
    · rw [FH.comp_hom,LinearMap.comp_assoc,hb0,LinearMap.comp_id,S.map0_ι β0]
    · rw [← Category.assoc,hb1,Category.assoc,S.map1_d0 β0,← Category.assoc]
    · rw [← Category.assoc,hD1_θ2,← Category.assoc,hb2,Category.assoc,S.map2_d1 β0,
        ← Category.assoc]
    · apply LinearMap.ext; intro z2
      have h1 := congrArg (fun f => f (b2.hom (θ2.hom z2))) (S.π_map2 β0)
      have h2' := congrArg (fun f => f (θ2.hom z2)) hctilde
      have h3' := congrArg (fun f => f z2) hbar_θ2
      simp only [FH.comp_hom,LinearMap.comp_apply] at h1 h2' h3' ⊢
      rw [h1,h2',h3']
  have hctilde_ψ_id : StableEq (ctilde.comp ψ) LinearMap.id := by
    have h1 := StableEq.comp_left (nuMap σ0) hcomp_true
    have hσβ : StableEq ((nuMap σ0).comp (nuMap β0)) LinearMap.id := by
      rw [← z83,← z207]; exact hσ0_β0_stab.nuMap
    have hL : StableEq ((nuMap σ0).comp ((nuMap β0).comp (ctilde.comp ψ))) (ctilde.comp ψ) := by
      have : (nuMap σ0).comp ((nuMap β0).comp (ctilde.comp ψ)) =
          ((nuMap σ0).comp (nuMap β0)).comp (ctilde.comp ψ) := by ext x; rfl
      rw [this]; simpa using hσβ.comp_right (ctilde.comp ψ)
    exact hL.symm.trans (h1.trans hσβ)
  have hψ_uK : StableEq ψ (nuMap (S.u K)) := by
    have h1 : StableEq ((nuMap (S.u K)).comp ψ) LinearMap.id :=
      (hctilde_stab.symm.comp_right ψ).trans hctilde_ψ_id
    have huu : StableEq ((nuMap (S.u K)).comp (nuMap (S.u K))) LinearMap.id := by
      rw [← z83,← z207]; exact (S.u_comp_u K).nuMap
    have hL : StableEq ((nuMap (S.u K)).comp ((nuMap (S.u K)).comp ψ)) ψ := by
      have : (nuMap (S.u K)).comp ((nuMap (S.u K)).comp ψ) =
          ((nuMap (S.u K)).comp (nuMap (S.u K))).comp ψ := by ext x; rfl
      rw [this]; simpa using huu.comp_right ψ
    exact hL.symm.trans (by simpa using StableEq.comp_left (nuMap (S.u K)) h1)
  let ψ_raw : K →ₗ[Λ] K := z203 ψ
  have hψ_raw_η : StableEq (ψ_raw - LinearMap.id) (S.η K) := by
    apply StableEq.of_nuMap
    rw [nuMap_sub,z268,z207]
    have hsub : nuMap (S.u K) - LinearMap.id = nuMap (S.η K) := by
      dsimp [ExactSys.u]; rw [z359,z207]; ext k; abel
    rw [← hsub]
    have hneg : StableEq (-LinearMap.id : nuMod K →ₗ[Λ] nuMod K) (-LinearMap.id) := StableEq.refl _
    simpa [sub_eq_add_neg] using StableEq.add hψ_uK hneg
  let h3_raw : (S.seq U).P1 ⟶ (S.seq Y).P0 :=
    ⟨z203 ((z3 (S.seq Y).P0).symm.toLinearMap.comp
      (h3.hom.comp (z3 (S.seq U).P1).toLinearMap))⟩
  have hh3_raw_shift : h3_raw⟦(1 : ℤ)⟧' = h3 := by
    apply FP.hom_ext; intro x
    change z3 (S.seq Y).P0
      (nuMap h3_raw.hom ((z3 (S.seq U).P1).symm x)) = h3.hom x
    have h1 : nuMap h3_raw.hom ((z3 (S.seq U).P1).symm x) =
        (z3 (S.seq Y).P0).symm (h3.hom ((z3 (S.seq U).P1)
          ((z3 (S.seq U).P1).symm x))) := by
      change (nuMap (z203 _)) _ = _
      rw [z268]
      rfl
    rw [h1,(z3 (S.seq U).P1).apply_symm_apply x]
    exact (z3 (S.seq Y).P0).apply_symm_apply (h3.hom x)
  let h2_un : (S.seq U).P0.Mod →ₗ[Λ] Y :=
    z203 ((S.seq Y).π.comp (h2.hom.comp (z3 (S.seq U).P0).toLinearMap))
  have hh3_d0 : h3_raw.hom.comp (S.seq U).d0.hom = (S.seq Y).ι.comp h2_un := by
    apply LinearMap.ext; intro u0
    have h1 : (h3_raw⟦(1 : ℤ)⟧').hom (((S.seq U).d0⟦(1 : ℤ)⟧').hom
        (z3 (S.seq U).P0 ⟨u0⟩)) =
        (S.seq Y).d2.hom (h2.hom (z3 (S.seq U).P0 ⟨u0⟩)) := by
      have h0 := congrArg (fun (m : (S.seq U).P0⟦(1 : ℤ)⟧ ⟶ (S.seq Y).P0⟦(1 : ℤ)⟧) =>
        m.hom (z3 (S.seq U).P0 ⟨u0⟩)) hd0_h3
      rw [← hh3_raw_shift] at h0
      exact h0
    have h2' : ((S.seq U).d0⟦(1 : ℤ)⟧').hom (z3 (S.seq U).P0 ⟨u0⟩) =
        z3 (S.seq U).P1 (nuMap (S.seq U).d0.hom ⟨u0⟩) :=
      (z5 (S.seq U).d0 ⟨u0⟩).symm
    have h3' : (h3_raw⟦(1 : ℤ)⟧').hom (z3 (S.seq U).P1 (nuMap (S.seq U).d0.hom ⟨u0⟩)) =
        z3 (S.seq Y).P0 (nuMap h3_raw.hom (nuMap (S.seq U).d0.hom ⟨u0⟩)) :=
      (z5 h3_raw _).symm
    have hL : z3 (S.seq Y).P0 (nuMap h3_raw.hom (nuMap (S.seq U).d0.hom ⟨u0⟩)) =
        (S.seq Y).d2.hom (h2.hom (z3 (S.seq U).P0 ⟨u0⟩)) :=
      h3'.symm.trans ((congrArg (h3_raw⟦(1 : ℤ)⟧').hom h2').symm.trans h1)
    exact congrArg nuMod.val ((z3 (S.seq Y).P0).injective hL)
  have hψ_raw_formula : ∀ k : K,
      jK ((ψ_raw - LinearMap.id : K →ₗ[Λ] K) k) =
        (FP.inr (S.seq U).P1 (S.seq Y).P0).hom (h3_raw.hom ((FP.fst _ _).hom k.1)) := by
    intro k
    let isoA0 := FP.sumShiftIso (S.seq U).P1 (S.seq Y).P0
    let yk : (FP.sum ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).Mod :=
      isoA0.inv.hom (jK1 ⟨k⟩)
    have h1 : isoA0.inv.hom (jK1 (ψ ⟨k⟩)) = θ3_mat.hom yk := congrArg (fun f => f ⟨k⟩) hψ
    have h2' : isoA0.inv.hom (jK1 ((ψ - LinearMap.id : nuMod K →ₗ[Λ] nuMod K) ⟨k⟩)) =
        θ3_mat.hom yk + yk := by
      simp only [LinearMap.sub_apply,LinearMap.id_apply,map_sub]
      rw [sub_eq_add_neg,z153,h1]
    have hfst_inv : ∀ z : (A0⟦(1 : ℤ)⟧).Mod,
        (FP.fst ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).hom (isoA0.inv.hom z) =
        ((FP.fst (S.seq U).P1 (S.seq Y).P0)⟦(1 : ℤ)⟧').hom z := fun z =>
      congrArg (fun (m : FP.sum ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧) ⟶
          (S.seq U).P1⟦(1 : ℤ)⟧) => m.hom (isoA0.inv.hom z))
        (FP.sumShiftIso_fst (S.seq U).P1 (S.seq Y).P0).symm
    have hsnd_inv : ∀ z : (A0⟦(1 : ℤ)⟧).Mod,
        (FP.snd ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).hom (isoA0.inv.hom z) =
        ((FP.snd (S.seq U).P1 (S.seq Y).P0)⟦(1 : ℤ)⟧').hom z := fun z =>
      congrArg (fun (m : FP.sum ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧) ⟶
          (S.seq Y).P0⟦(1 : ℤ)⟧) => m.hom (isoA0.inv.hom z))
        (FP.sumShiftIso_snd (S.seq U).P1 (S.seq Y).P0).symm
    apply (FP.sumEquivProd (S.seq U).P1 (S.seq Y).P0).injective
    have hfst_in : (FP.fst _ _).hom ((FP.inr (S.seq U).P1 (S.seq Y).P0).hom
        (h3_raw.hom ((FP.fst _ _).hom k.1))) = 0 := by
      simpa using congrArg (fun (m : (S.seq Y).P0 ⟶ (S.seq U).P1) =>
        m.hom (h3_raw.hom ((FP.fst _ _).hom k.1))) (FP.inr_fst (S.seq U).P1 (S.seq Y).P0)
    have hsnd_in : (FP.snd _ _).hom ((FP.inr (S.seq U).P1 (S.seq Y).P0).hom
        (h3_raw.hom ((FP.fst _ _).hom k.1))) = h3_raw.hom ((FP.fst _ _).hom k.1) := by
      simpa using congrArg (fun (m : (S.seq Y).P0 ⟶ (S.seq Y).P0) =>
        m.hom (h3_raw.hom ((FP.fst _ _).hom k.1))) (FP.inr_snd (S.seq U).P1 (S.seq Y).P0)
    ext : 1
    · change (FP.fst _ _).hom (jK ((ψ_raw - LinearMap.id : K →ₗ[Λ] K) k)) =
        (FP.fst _ _).hom ((FP.inr (S.seq U).P1 (S.seq Y).P0).hom
          (h3_raw.hom ((FP.fst _ _).hom k.1)))
      rw [hfst_in]
      have h3f := congrArg (FP.fst ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).hom h2'
      have hL : (FP.fst ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).hom
          (isoA0.inv.hom (jK1 ((ψ - LinearMap.id : nuMod K →ₗ[Λ] nuMod K) ⟨k⟩))) =
          z3 (S.seq U).P1 ⟨(FP.fst _ _).hom (jK ((ψ_raw - LinearMap.id : K →ₗ[Λ] K) k))⟩ := by
        rw [hfst_inv]
        change ((FP.fst (S.seq U).P1 (S.seq Y).P0)⟦(1 : ℤ)⟧').hom
          (z3 A0 (nuMap jK ((ψ - LinearMap.id : nuMod K →ₗ[Λ] nuMod K) ⟨k⟩))) = _
        rw [← z5 (FP.fst (S.seq U).P1 (S.seq Y).P0)]
        rfl
      have hR : (FP.fst ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).hom
          (θ3_mat.hom yk + yk) = 0 := by
        rw [map_add,FP.mat_apply_fst]
        simp [z10]
      rw [hL,hR] at h3f
      exact congrArg nuMod.val ((map_eq_zero_iff (z3 (S.seq U).P1)
        (z3 (S.seq U).P1).injective).mp h3f)
    · change (FP.snd _ _).hom (jK ((ψ_raw - LinearMap.id : K →ₗ[Λ] K) k)) =
        (FP.snd _ _).hom ((FP.inr (S.seq U).P1 (S.seq Y).P0).hom
          (h3_raw.hom ((FP.fst _ _).hom k.1)))
      rw [hsnd_in]
      have h3s := congrArg (FP.snd ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).hom h2'
      have hL : (FP.snd ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).hom
          (isoA0.inv.hom (jK1 ((ψ - LinearMap.id : nuMod K →ₗ[Λ] nuMod K) ⟨k⟩))) =
          z3 (S.seq Y).P0 ⟨(FP.snd _ _).hom (jK ((ψ_raw - LinearMap.id : K →ₗ[Λ] K) k))⟩ := by
        rw [hsnd_inv]
        change ((FP.snd (S.seq U).P1 (S.seq Y).P0)⟦(1 : ℤ)⟧').hom
          (z3 A0 (nuMap jK ((ψ - LinearMap.id : nuMod K →ₗ[Λ] nuMod K) ⟨k⟩))) = _
        rw [← z5 (FP.snd (S.seq U).P1 (S.seq Y).P0)]
        rfl
      have hR : (FP.snd ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).hom
          (θ3_mat.hom yk + yk) =
          z3 (S.seq Y).P0 ⟨h3_raw.hom ((FP.fst _ _).hom k.1)⟩ := by
        rw [map_add,FP.mat_apply_snd,FH.id_hom,LinearMap.id_apply]
        have hcancel : h3.hom ((FP.fst _ _).hom yk) +
            (FP.snd _ _).hom yk + (FP.snd _ _).hom yk =
            h3.hom ((FP.fst _ _).hom yk) := by
          calc _ = h3.hom ((FP.fst _ _).hom yk) +
                ((FP.snd _ _).hom yk + (FP.snd _ _).hom yk) := by abel
            _ = h3.hom ((FP.fst _ _).hom yk) + 0 := by rw [z10]
            _ = _ := add_zero _
        rw [hcancel,← hh3_raw_shift]
        have hfst : (FP.fst ((S.seq U).P1⟦(1 : ℤ)⟧) ((S.seq Y).P0⟦(1 : ℤ)⟧)).hom yk =
            z3 (S.seq U).P1 ⟨(FP.fst _ _).hom k.1⟩ := by
          dsimp [yk]
          rw [hfst_inv]
          change ((FP.fst (S.seq U).P1 (S.seq Y).P0)⟦(1 : ℤ)⟧').hom
            (z3 A0 (nuMap jK ⟨k⟩)) = _
          rw [← z5 (FP.fst (S.seq U).P1 (S.seq Y).P0)]
          rfl
        rw [hfst]
        exact (z5 h3_raw ⟨(FP.fst _ _).hom k.1⟩).symm
      rw [hL,hR] at h3s
      exact congrArg nuMod.val ((z3 (S.seq Y).P0).injective h3s)
  exact ⟨h2_un,h3_raw,ψ_raw,hψ_raw_η,hh3_d0,hψ_raw_formula⟩
theorem lightning_flash_obstruction (S : ExactSys)
    (hTri : @IsTriangulated FP _ _ _ _ _ (deltaPretriangulated S))
    {U Y X OU : Type}
    [AddCommGroup U] [Module Λ U] [Finite U]
    [AddCommGroup Y] [Module Λ Y] [Finite Y]
    [AddCommGroup X] [Module Λ X] [Finite X]
    [AddCommGroup OU] [Module Λ OU] [Finite OU]
    {PU : FP}
    (w : U →ₗ[Λ] Y) (z : Y →ₗ[Λ] X)
    (hw : Function.Injective w) (hwz : ExactAt w z) (hz : Function.Surjective z)
    (jU : U →ₗ[Λ] PU.Mod) (qU : PU.Mod →ₗ[Λ] OU)
    (hjU : Function.Injective jU) (hjUqU : ExactAt jU qU) (hqU : Function.Surjective qU)
    (Φ_conn : Y →ₗ[Λ] PU.Mod) (hΦ : Φ_conn.comp w = jU)
    (Os : X →ₗ[Λ] OU) (hOs : Os.comp z = qU.comp Φ_conn)
    (hηU : StableEq (S.η U) 0) (hηY : StableEq (S.η Y) 0) :
    ∃ φ : OU →ₗ[Λ] Y,StableEq (z.comp (φ.comp Os)) (S.η X) := by
  let _ : Pretriangulated FP := deltaPretriangulated S
  let _ : IsTriangulated FP := hTri
  have hTU : (S.seq U).triangle ∈ @Pretriangulated.distinguishedTriangles FP _ _ _ _ _ (deltaPretriangulated S) :=
    z92 S U hηU
  have hTY : (S.seq Y).triangle ∈ @Pretriangulated.distinguishedTriangles FP _ _ _ _ _ (deltaPretriangulated S) :=
    z92 S Y hηY
  obtain ⟨f2t,hf2t_d1,hf2t_d2,hT_tilde⟩ :=
    @z251 (deltaPretriangulated S) hTri _ _ _ _ _ _ _ _ _ _ _ _
      hTU hTY (S.map0 w) (S.map1 w) (S.map1_d0 w)
  obtain ⟨β0,σ0,hbar_true,m0,m1,m2,
      hβ0,hβ0_σ0,hσ0_β0_stab,hex_D0_D1,hex_D1_hbar,hhbar_surj,
      hhbar_true,hm0_jK,hm1_D0,hm2_D1,hm2_πX⟩ :=
    z246 S w z hw hwz hz
  obtain ⟨h2_un,h3_raw,ψ_raw,hψ_raw_η,hh3_d0,hψ_raw_formula⟩ :=
    z258 S w z f2t hf2t_d1 hf2t_d2 hT_tilde β0 σ0 hbar_true m0 m1 m2
      hσ0_β0_stab hex_D0_D1 hex_D1_hbar hhbar_surj hhbar_true hm0_jK hm1_D0 hm2_D1 hm2_πX
  let D0 := FP.mat (S.seq U).d1 0 (S.map1 w) (S.seq Y).d0
  let K := LinearMap.ker D0.hom
  let jK : K →ₗ[Λ] (FP.sum (S.seq U).P1 (S.seq Y).P0).Mod := K.subtype
  have hm0_zw : comp (S.map0 w) (S.map0 z) = 0 := by
    rw [← S.map0_comp,hwz.comp_eq_zero,S.map0_zero]
  have hh2_un_ι : h2_un.comp (S.seq U).ι = 0 := by
    apply LinearMap.ext; intro u
    apply (S.seq Y).ι_inj
    change (S.seq Y).ι (h2_un ((S.seq U).ι u)) = (S.seq Y).ι 0
    rw [map_zero]
    have h1 := congrArg (fun f => f ((S.seq U).ι u)) hh3_d0
    have h2' := congrArg (fun f => f u) (S.seq U).exact0.comp_eq_zero
    simp only [LinearMap.comp_apply,LinearMap.zero_apply] at h1 h2' ⊢
    rw [← h1,h2',map_zero]
  let OU_seq : Type := (S.seq U).P0.Mod ⧸ LinearMap.range (S.seq U).ι
  let q_seq : (S.seq U).P0.Mod →ₗ[Λ] OU_seq := (LinearMap.range (S.seq U).ι).mkQ
  have hq_seq_surj : Function.Surjective q_seq := Submodule.mkQ_surjective _
  have hex_ιU_qseq : ExactAt (S.seq U).ι q_seq := by
    rw [z7]; intro x
    change (LinearMap.range (S.seq U).ι).mkQ x = 0 ↔ ∃ u,(S.seq U).ι u = x
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,LinearMap.mem_range]
  obtain ⟨φ_seq,hφ_seq⟩ := z21 hex_ιU_qseq hq_seq_surj h2_un hh2_un_ι
  obtain ⟨t1h,ht1h⟩ := S.inj PU (S.seq U).ι (S.seq U).ι_inj jU
  let t1 : (S.seq U).P0 ⟶ PU := ⟨t1h⟩
  obtain ⟨t2h,ht2h⟩ := S.inj (S.seq U).P0 jU hjU (S.seq U).ι
  let t2 : PU ⟶ (S.seq U).P0 := ⟨t2h⟩
  have ht1_kill : (qU.comp t1.hom).comp (S.seq U).ι = 0 := by
    rw [LinearMap.comp_assoc,ht1h,hjUqU.comp_eq_zero]
  obtain ⟨sO,hsO⟩ := z21 hex_ιU_qseq hq_seq_surj (qU.comp t1.hom) ht1_kill
  have ht2_kill : (q_seq.comp t2.hom).comp jU = 0 := by
    rw [LinearMap.comp_assoc,ht2h,hex_ιU_qseq.comp_eq_zero]
  obtain ⟨rO,hrO⟩ := z21 hjUqU hqU (q_seq.comp t2.hom) ht2_kill
  have hrOsO : StableEq (rO.comp sO) LinearMap.id := by
    have hkill : (t2.hom.comp t1.hom - LinearMap.id).comp (S.seq U).ι = 0 := by
      apply LinearMap.ext; intro u
      have h1 := congrArg (fun f => f u) ht1h
      have h2' := congrArg (fun f => f u) ht2h
      simp only [t1,t2,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,
        LinearMap.zero_apply] at h1 h2' ⊢
      rw [h1,h2',sub_self]
    obtain ⟨kO,hkO⟩ := z21 hex_ιU_qseq hq_seq_surj
      (t2.hom.comp t1.hom - LinearMap.id) hkill
    refine ⟨(S.seq U).P0,kO,q_seq,?_⟩
    apply LinearMap.ext; intro o
    obtain ⟨u0,rfl⟩ := hq_seq_surj o
    have h1 := congrArg (fun f => f u0) hsO
    have h2' := congrArg (fun f => f (t1.hom u0)) hrO
    have h3' := congrArg (fun f => f u0) hkO
    simp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply] at h1 h2' h3' ⊢
    rw [h1,h2',h3',map_sub]
  let e_d0 : OU_seq ≃ₗ[Λ] LinearMap.range (S.seq U).d0.hom :=
    (Submodule.quotEquivOfEq _ _ (S.seq U).exact0).trans (S.seq U).d0.hom.quotKerEquivRange
  have he_d0_apply : ∀ u0 : (S.seq U).P0.Mod,(e_d0 (q_seq u0)).1 = (S.seq U).d0.hom u0 := fun _ => rfl
  let fstK_range : K →ₗ[Λ] LinearMap.range (S.seq U).d0.hom :=
    ((FP.fst (S.seq U).P1 (S.seq Y).P0).hom.comp jK).codRestrict
      (LinearMap.range (S.seq U).d0.hom) (fun k => by
        rw [(S.seq U).exact1]
        have h := congrArg (FP.fst (S.seq U).P2 (S.seq Y).P1).hom k.2
        rw [FP.mat_apply_fst,FH.zero_hom,LinearMap.zero_apply,add_zero,map_zero] at h
        exact h)
  let δK : K →ₗ[Λ] OU_seq := e_d0.symm.toLinearMap.comp fstK_range
  have hδK_eq : ∀ (k : K) (u0 : (S.seq U).P0.Mod),
      (S.seq U).d0.hom u0 = (FP.fst _ _).hom k.1 → δK k = q_seq u0 := by
    intro k u0 hu0
    apply e_d0.injective; apply Subtype.ext
    rw [he_d0_apply]
    change (e_d0 (e_d0.symm (fstK_range k))).1 = (S.seq U).d0.hom u0
    rw [e_d0.apply_symm_apply]
    exact hu0.symm
  have heq2 : z.comp (φ_seq.comp δK) = β0.comp (ψ_raw - LinearMap.id) := by
    apply LinearMap.ext; intro k
    have hp1_d1 : (S.seq U).d1.hom ((FP.fst _ _).hom k.1) = 0 := by
      have h := congrArg (FP.fst (S.seq U).P2 (S.seq Y).P1).hom k.2
      rw [FP.mat_apply_fst,FH.zero_hom,LinearMap.zero_apply,add_zero,map_zero] at h
      exact h
    obtain ⟨u0,hu0⟩ := ((z7 _ _).mp (S.seq U).exact1 _).mp hp1_d1
    apply (S.seq X).ι_inj
    have h1 := congrArg (fun f => f ((ψ_raw - LinearMap.id : K →ₗ[Λ] K) k)) hβ0
    have h2' := hψ_raw_formula k
    have hsnd_in : (FP.snd _ _).hom ((FP.inr (S.seq U).P1 (S.seq Y).P0).hom
        (h3_raw.hom ((FP.fst _ _).hom k.1))) = h3_raw.hom ((FP.fst _ _).hom k.1) := by
      simpa using congrArg (fun (m : (S.seq Y).P0 ⟶ (S.seq Y).P0) =>
        m.hom (h3_raw.hom ((FP.fst _ _).hom k.1))) (FP.inr_snd (S.seq U).P1 (S.seq Y).P0)
    have h3' := congrArg (fun f => f u0) hh3_d0
    have h4' := congrArg (fun f => f (h2_un u0)) (S.map0_ι z)
    have h5' := congrArg (fun f => f u0) hφ_seq
    simp only [LinearMap.comp_apply] at h1 h3' h4' h5' ⊢
    rw [h1,h2',hsnd_in,← hu0,h3',h4',← h5',hδK_eq k u0 hu0]
  obtain ⟨Φtilde_h,hΦtilde⟩ := S.inj PU (S.seq Y).ι (S.seq Y).ι_inj Φ_conn
  let Φtilde : (S.seq Y).P0 ⟶ PU := ⟨Φtilde_h⟩
  have hΨ_kill : (Φtilde.hom.comp (S.map0 w).hom - t1.hom).comp (S.seq U).ι = 0 := by
    apply LinearMap.ext; intro u
    have h1 := congrArg (fun f => f u) (S.map0_ι w)
    have h2' := congrArg (fun f => f (w u)) hΦtilde
    have h3' := congrArg (fun f => f u) hΦ
    have h4' := congrArg (fun f => f u) ht1h
    simp only [Φtilde,t1,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.zero_apply] at h1 h2' h3' h4' ⊢
    rw [h1,h2',h3',h4',sub_self]
  obtain ⟨Ψh,hΨh⟩ := z32 S (S.seq U).exact0 PU
    (Φtilde.hom.comp (S.map0 w).hom - t1.hom) hΨ_kill
  let Ψ : (S.seq U).P1 ⟶ PU := ⟨Ψh⟩
  have heq1 : StableEq (sO.comp δK) (Os.comp β0) := by
    refine ⟨PU,(FP.desc Ψ Φtilde).hom.comp jK,qU,?_⟩
    apply LinearMap.ext; intro k
    let p1 := (FP.fst (S.seq U).P1 (S.seq Y).P0).hom k.1
    let p0 := (FP.snd (S.seq U).P1 (S.seq Y).P0).hom k.1
    have hp1_d1 : (S.seq U).d1.hom p1 = 0 := by
      have h := congrArg (FP.fst (S.seq U).P2 (S.seq Y).P1).hom k.2
      rw [FP.mat_apply_fst,FH.zero_hom,LinearMap.zero_apply,add_zero,map_zero] at h
      exact h
    have hp_d0 : (S.map1 w).hom p1 + (S.seq Y).d0.hom p0 = 0 := by
      have h := congrArg (FP.snd (S.seq U).P2 (S.seq Y).P1).hom k.2
      rw [FP.mat_apply_snd,map_zero] at h; exact h
    obtain ⟨u0,hu0⟩ := ((z7 _ _).mp (S.seq U).exact1 p1).mp hp1_d1
    have hd0y : (S.seq Y).d0.hom (p0 + (S.map0 w).hom u0) = 0 := by
      rw [map_add]
      have hc := congrArg (fun (m : (S.seq U).P0 ⟶ (S.seq Y).P1) => m.hom u0) (S.map1_d0 w)
      simp only [FH.comp_hom,LinearMap.comp_apply] at hc
      rw [← hc,hu0,add_comm,hp_d0]
    obtain ⟨y,hy⟩ := ((z7 _ _).mp (S.seq Y).exact0 _).mp hd0y
    have hzy : z y = β0 k := by
      apply (S.seq X).ι_inj
      have h1 := congrArg (fun f => f y) (S.map0_ι z)
      have h2' := congrArg (fun f => f k) hβ0
      have hzw0 := congrArg (fun (m : (S.seq U).P0 ⟶ (S.seq X).P0) => m.hom u0) hm0_zw
      simp only [FH.comp_hom,FH.zero_hom,LinearMap.comp_apply,
        LinearMap.zero_apply] at h1 h2' hzw0
      rw [← h1,hy,map_add,hzw0,add_zero,h2']
      rfl
    have hmap0_u0 : (S.map0 w).hom u0 = p0 + (S.seq Y).ι y := by
      calc (S.map0 w).hom u0 = (p0 + p0) + (S.map0 w).hom u0 := by rw [z10,zero_add]
        _ = p0 + (p0 + (S.map0 w).hom u0) := by abel
        _ = p0 + (S.seq Y).ι y := by rw [hy]
    have ht1_u0 : t1.hom u0 = Φtilde.hom ((S.map0 w).hom u0) + Ψ.hom ((S.seq U).d0.hom u0) := by
      have h1 := congrArg (fun f => f u0) hΨh
      simp only [Φtilde,LinearMap.comp_apply,LinearMap.sub_apply] at h1
      rw [h1,sub_eq_add_neg,z153]
      calc t1.hom u0 = 0 + t1.hom u0 := (zero_add _).symm
        _ = (Φtilde.hom ((S.map0 w).hom u0) + Φtilde.hom ((S.map0 w).hom u0)) + t1.hom u0 := by
            rw [z10]
        _ = Φtilde.hom ((S.map0 w).hom u0) + (Φtilde.hom ((S.map0 w).hom u0) + t1.hom u0) := by abel
    have hdesc_k : (FP.desc Ψ Φtilde).hom (jK k) = Ψ.hom p1 + Φtilde.hom p0 := rfl
    simp only [LinearMap.sub_apply,LinearMap.comp_apply]
    rw [hδK_eq k u0 hu0]
    have hsOu0 := congrArg (fun f => f u0) hsO
    simp only [LinearMap.comp_apply] at hsOu0
    rw [hsOu0,ht1_u0,hu0,hmap0_u0,map_add,map_add,map_add,hdesc_k,map_add]
    have hΦy : Φtilde.hom ((S.seq Y).ι y) = Φ_conn y := congrArg (fun f => f y) hΦtilde
    have hOsy : qU (Φ_conn y) = Os (z y) := (congrArg (fun f => f y) hOs).symm
    rw [hΦy,hOsy,hzy,sub_eq_add_neg,z153]
    calc qU (Φtilde.hom p0) + Os (β0 k) + qU (Ψ.hom p1) + Os (β0 k)
        = qU (Ψ.hom p1) + qU (Φtilde.hom p0) + (Os (β0 k) + Os (β0 k)) := by abel
      _ = qU (Ψ.hom p1) + qU (Φtilde.hom p0) + 0 := by rw [z10]
      _ = qU (Ψ.hom p1) + qU (Φtilde.hom p0) := add_zero _
  refine ⟨φ_seq.comp rO,?_⟩
  have hchain1 : z.comp ((φ_seq.comp rO).comp Os) =
      ((z.comp φ_seq).comp (rO.comp (Os.comp β0))).comp σ0 := by
    apply LinearMap.ext; intro x
    have h1 := congrArg (fun f => f x) hβ0_σ0
    simp only [LinearMap.comp_apply,LinearMap.id_apply] at h1 ⊢
    rw [h1]
  have h1 : StableEq (((z.comp φ_seq).comp (rO.comp (Os.comp β0))).comp σ0)
      (((z.comp φ_seq).comp (rO.comp (sO.comp δK))).comp σ0) :=
    ((StableEq.comp_left rO heq1.symm).comp_left (z.comp φ_seq)).comp_right σ0
  have h2 : StableEq (((z.comp φ_seq).comp ((rO.comp sO).comp δK)).comp σ0)
      (((z.comp φ_seq).comp δK).comp σ0) :=
    (((hrOsO.comp_right δK).comp_left (z.comp φ_seq)).comp_right σ0)
  have h3 : ((z.comp φ_seq).comp δK).comp σ0 = (β0.comp (ψ_raw - LinearMap.id)).comp σ0 := by
    rw [← heq2]; ext x; rfl
  have h4 : StableEq ((β0.comp (ψ_raw - LinearMap.id)).comp σ0)
      ((β0.comp (S.η K)).comp σ0) :=
    (StableEq.comp_left β0 hψ_raw_η).comp_right σ0
  have h5 : StableEq ((β0.comp (S.η K)).comp σ0) (((S.η X).comp β0).comp σ0) :=
    (S.η_natural β0).symm.comp_right σ0
  have h6 : ((S.η X).comp β0).comp σ0 = S.η X := by
    rw [LinearMap.comp_assoc,hβ0_σ0,LinearMap.comp_id]
  rw [hchain1]
  have heq_assoc : ((z.comp φ_seq).comp (rO.comp (sO.comp δK))).comp σ0 =
      ((z.comp φ_seq).comp ((rO.comp sO).comp δK)).comp σ0 := by ext x; rfl
  exact h1.trans (by rw [heq_assoc]; exact h2.trans (by rw [h3]; exact h4.trans (by rw [← h6]; exact h5)))
end
end MO31809
namespace MO31809L
open CategoryTheory Preadditive Limits Pretriangulated ZeroObject
def UC.{v,u} (C : Type 0) : Type u := let _ := PUnit.{v + 1}; ULift.{u} C
def uO.{v,u} {C : Type 0} (x : C) : UC.{v,u} C := ULift.up x
structure UM.{v,u} {C : Type 0} [Category.{0} C] (X Y : UC.{v,u} C) : Type v where mor : X.down ⟶ Y.down
lemma UM.e.{v,u} {C : Type 0} [Category.{0} C] {X Y : UC.{v,u} C} {f g : UM.{v,u} X Y} (h : f.mor = g.mor) : f = g := by cases f; cases g; congr
section L
universe v u
variable {C : Type 0} [Category.{0} C]
instance : Category.{v,u} (UC.{v,u} C) where
  Hom X Y := UM.{v,u} X Y
  id X := ⟨𝟙 X.down⟩
  comp f g := ⟨f.mor ≫ g.mor⟩
  id_comp f := UM.e (Category.id_comp f.mor)
  comp_id f := UM.e (Category.comp_id f.mor)
  assoc f g h := UM.e (Category.assoc f.mor g.mor h.mor)
lemma cM {X Y Z : UC.{v,u} C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).mor = f.mor ≫ g.mor := rfl
lemma eM {X Y : UC.{v,u} C} (h : X = Y) : (eqToHom h : X ⟶ Y).mor = eqToHom (congrArg ULift.down h) := by subst h; rfl
section P
variable [Preadditive C]
instance {X Y : UC.{v,u} C} : Zero (UM.{v,u} X Y) := ⟨⟨0⟩⟩
instance {X Y : UC.{v,u} C} : Add (UM.{v,u} X Y) := ⟨fun f g => ⟨f.mor + g.mor⟩⟩
instance {X Y : UC.{v,u} C} : Neg (UM.{v,u} X Y) := ⟨fun f => ⟨-f.mor⟩⟩
instance {X Y : UC.{v,u} C} : Sub (UM.{v,u} X Y) := ⟨fun f g => ⟨f.mor - g.mor⟩⟩
instance {X Y : UC.{v,u} C} : SMul ℕ (UM.{v,u} X Y) := ⟨fun n f => ⟨n • f.mor⟩⟩
instance {X Y : UC.{v,u} C} : SMul ℤ (UM.{v,u} X Y) := ⟨fun n f => ⟨n • f.mor⟩⟩
instance {X Y : UC.{v,u} C} : AddCommGroup (UM.{v,u} X Y) :=
  Function.Injective.addCommGroup UM.mor (fun _ _ h => UM.e h) rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
instance : Preadditive (UC.{v,u} C) where
  homGroup X Y := inferInstanceAs (AddCommGroup (UM.{v,u} X Y))
  add_comp _ _ _ f f' g := UM.e (Preadditive.add_comp _ _ _ f.mor f'.mor g.mor)
  comp_add _ _ _ f g g' := UM.e (Preadditive.comp_add _ _ _ f.mor g.mor g'.mor)
end P
instance [Preadditive C] [HasZeroObject C] : HasZeroObject (UC.{v,u} C) :=
  ⟨uO (0 : C),by rw [Limits.IsZero.iff_id_eq_zero]; exact UM.e ((Limits.isZero_zero C).eq_of_src _ _)⟩
def lF (G : C ⥤ C) : UC.{v,u} C ⥤ UC.{v,u} C where
  obj X := uO (G.obj X.down); map f := ⟨G.map f.mor⟩
  map_id X := UM.e (G.map_id X.down); map_comp f g := UM.e (G.map_comp f.mor g.mor)
def lI {G H : C ⥤ C} (e : G ≅ H) : lF.{v,u} G ≅ lF.{v,u} H where
  hom := { app := fun X => ⟨e.hom.app X.down⟩,naturality := fun _ _ f => UM.e (e.hom.naturality f.mor) }
  inv := { app := fun X => ⟨e.inv.app X.down⟩,naturality := fun _ _ f => UM.e (e.inv.naturality f.mor) }
  hom_inv_id := by ext X; exact UM.e (Iso.hom_inv_id_app e X.down)
  inv_hom_id := by ext X; exact UM.e (Iso.inv_hom_id_app e X.down)
noncomputable def lS [HasShift C ℤ] : ShiftMkCore (UC.{v,u} C) ℤ where
  F n := lF (shiftFunctor C n); zero := lI (shiftFunctorZero C ℤ); add n m := lI (shiftFunctorAdd C n m)
  assoc_hom_app m₁ m₂ m₃ X := UM.e (by
    rw [cM,cM,cM,eM]
    have h := shiftFunctorAdd_assoc_hom_app m₁ m₂ m₃ X.down
    simp only [shiftFunctorAdd',Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,eqToHom_app,Category.assoc] at h
    exact h)
  zero_add_hom_app n X := UM.e (by rw [cM,eM]; exact shiftFunctorAdd_zero_add_hom_app n X.down)
  add_zero_hom_app n X := UM.e (by rw [cM,eM]; exact shiftFunctorAdd_add_zero_hom_app n X.down)
noncomputable instance [HasShift C ℤ] : HasShift (UC.{v,u} C) ℤ := hasShiftMk (UC.{v,u} C) ℤ lS
instance [Preadditive C] [HasShift C ℤ] [∀ n : ℤ,(shiftFunctor C n).Additive] (n : ℤ) : (shiftFunctor (UC.{v,u} C) n).Additive where
  map_add {_ _ f g} := UM.e ((shiftFunctor C n).map_add (f := f.mor) (g := g.mor))
section T
variable [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ,(shiftFunctor C n).Additive] [Pretriangulated C]
def dT (T : Triangle (UC.{v,u} C)) : Triangle C := Triangle.mk T.mor₁.mor T.mor₂.mor T.mor₃.mor
def dI {T₁ T₂ : Triangle (UC.{v,u} C)} (e : T₁ ≅ T₂) : dT T₁ ≅ dT T₂ where
  hom := { hom₁ := e.hom.hom₁.mor,hom₂ := e.hom.hom₂.mor,hom₃ := e.hom.hom₃.mor,comm₁ := congrArg UM.mor e.hom.comm₁,comm₂ := congrArg UM.mor e.hom.comm₂,comm₃ := congrArg UM.mor e.hom.comm₃ }
  inv := { hom₁ := e.inv.hom₁.mor,hom₂ := e.inv.hom₂.mor,hom₃ := e.inv.hom₃.mor,comm₁ := congrArg UM.mor e.inv.comm₁,comm₂ := congrArg UM.mor e.inv.comm₂,comm₃ := congrArg UM.mor e.inv.comm₃ }
  hom_inv_id := by
    ext
    · exact congrArg (fun m => m.hom₁.mor) e.hom_inv_id
    · exact congrArg (fun m => m.hom₂.mor) e.hom_inv_id
    · exact congrArg (fun m => m.hom₃.mor) e.hom_inv_id
  inv_hom_id := by
    ext
    · exact congrArg (fun m => m.hom₁.mor) e.inv_hom_id
    · exact congrArg (fun m => m.hom₂.mor) e.inv_hom_id
    · exact congrArg (fun m => m.hom₃.mor) e.inv_hom_id
noncomputable instance : Pretriangulated (UC.{v,u} C) where
  distinguishedTriangles := { T | dT T ∈ distTriang C }
  isomorphic_distinguished _ hT₁ _ e := isomorphic_distinguished _ hT₁ _ (dI e)
  contractible_distinguished X := by
    refine isomorphic_distinguished _ (contractible_distinguished X.down) _ ?_
    have hz : IsZero ((0 : UC.{v,u} C).down) := by
      have hzD := Limits.isZero_zero (UC.{v,u} C)
      refine ⟨fun Y => ⟨⟨⟨0⟩,fun f => ?_⟩⟩,fun Y => ⟨⟨⟨0⟩,fun f => ?_⟩⟩⟩
      · exact congrArg UM.mor (hzD.eq_of_src (UM.mk f : (0 : UC.{v,u} C) ⟶ uO Y) (0 : (0 : UC.{v,u} C) ⟶ uO Y))
      · exact congrArg UM.mor (hzD.eq_of_tgt (UM.mk f : uO Y ⟶ (0 : UC.{v,u} C)) (0 : uO Y ⟶ (0 : UC.{v,u} C)))
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (hz.iso (Limits.isZero_zero C))
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Limits.isZero_zero C).eq_of_tgt _ _) (hz.eq_of_src _ _)
  distinguished_cocone_triangle f := by obtain ⟨Z,g,h,m⟩ := distinguished_cocone_triangle f.mor; exact ⟨uO Z,⟨g⟩,⟨h⟩,m⟩
  rotate_distinguished_triangle T := rotate_distinguished_triangle (dT T)
  complete_distinguished_triangle_morphism T₁ T₂ h₁ h₂ a b c := by
    obtain ⟨k,h1,h2⟩ := complete_distinguished_triangle_morphism (dT T₁) (dT T₂) h₁ h₂ a.mor b.mor (congrArg UM.mor c)
    exact ⟨⟨k⟩,UM.e h1,UM.e h2⟩
lemma tL [IsTriangulated (UC.{v,u} C)] : IsTriangulated C where
  octahedron_axiom {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ u₁₂ u₂₃ u₁₃} comm {v₁₂ w₁₂} h₁₂ {v₂₃ w₂₃} h₂₃ {v₁₃ w₁₃} h₁₃ := by
    obtain ⟨H⟩ := IsTriangulated.octahedron_axiom (C := UC.{v,u} C)
      (X₁ := uO X₁) (X₂ := uO X₂) (X₃ := uO X₃) (Z₁₂ := uO Z₁₂) (Z₂₃ := uO Z₂₃) (Z₁₃ := uO Z₁₃)
      (u₁₂ := UM.mk u₁₂) (u₂₃ := UM.mk u₂₃) (u₁₃ := UM.mk u₁₃) (UM.e comm)
      (v₁₂ := UM.mk v₁₂) (w₁₂ := UM.mk w₁₂) h₁₂ (v₂₃ := UM.mk v₂₃) (w₂₃ := UM.mk w₂₃) h₂₃
      (v₁₃ := UM.mk v₁₃) (w₁₃ := UM.mk w₁₃) h₁₃
    exact ⟨⟨H.m₁.mor,H.m₃.mor,congrArg UM.mor H.comm₁,congrArg UM.mor H.comm₂,congrArg UM.mor H.comm₃,congrArg UM.mor H.comm₄,H.mem⟩⟩
end T
end L
end MO31809L
theorem OMA.solution : type_of% @Mathoverflow31809.mathoverflow_31809 := by
  intro hall
  letI : CategoryTheory.Pretriangulated MO31809.FP :=
    MO31809.deltaPretriangulated MO31809.concreteExactSys
  have hTriD : CategoryTheory.IsTriangulated (MO31809L.UC MO31809.FP) := hall (MO31809L.UC MO31809.FP)
  have hTri : CategoryTheory.IsTriangulated MO31809.FP := MO31809L.tL
  obtain ⟨φ, hφ⟩ := MO31809.lightning_flash_obstruction MO31809.concreteExactSys hTri
    MO31809.wUY MO31809.zYX MO31809.wUY_inj MO31809.exact_wUY_zYX MO31809.zYX_surj
    MO31809.jU MO31809.qU MO31809.jU_inj MO31809.exact_jU_qU MO31809.qU_surj
    MO31809.Φ_conn MO31809.Φ_conn_wUY MO31809.Os MO31809.Os_zYX
    MO31809.eta_U_zero MO31809.eta_Y_zero
  rw [MO31809.no_lightning_flash φ] at hφ
  exact MO31809.eta_X_not_stable_zero hφ
