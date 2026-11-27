import FormalConjectures.Arxiv.«0805.3777».TensorRank

/-! Generic rank of complex tensors of format (4,m,m).

Use a three-dimensional base and m-3 individual coordinates on each large
axis. Five points occupy the base. Each other group has two points whose
factors are supported in that group and the base. A pair of distinct
one-dimensional groups needs four independent directions. For one group
together with the base, a 28-row projected tangent matrix has a right inverse
modulo two. The 36 base rows have their own binary right inverse. Nonzero
determinants modulo two lift these rank bounds to the complex numbers. A common specialization makes all sectors span. The total
point count is 2m-1.

Dimension counting excludes smaller ranks on a dense open set. The tangent
map yields the matching generic upper bound. For the known rank formula
see [Friedland, equation (5.7)](https://arxiv.org/abs/0805.3777).
-/

namespace FourSlice

def Spans (m : ℕ) : Prop :=
  ∃ a : Fin (2*m-1) → Fin 4 → ℂ, ∃ b c : Fin (2*m-1) → Fin m → ℂ,
    ∀ T : Fin 4 → Fin m → Fin m → ℂ, ∃ u : Fin (2*m-1) → Fin 4 → ℂ,
      ∃ v w : Fin (2*m-1) → Fin m → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(b t j*c t k) + a t i*(v t j*c t k) + a t i*(b t j*w t k))

end FourSlice

namespace FourSlice

abbrev LocalAxis := Option (Fin 3)

/-- The base group is a four-by-three-by-three tensor, with five complete points. -/
def Base (a : Fin 5 → Fin 4 → ℂ) (b c : Fin 5 → Fin 3 → ℂ) : Prop :=
  ∀ T : Fin 4 → Fin 3 → Fin 3 → ℂ, ∃ u : Fin 5 → Fin 4 → ℂ, ∃ v w : Fin 5 → Fin 3 → ℂ,
    ∀ i j k, T i j k = ∑ t, (u t i*(b t j*c t k) + a t i*(v t j*c t k) + a t i*(b t j*w t k))

/-- In a single regular group, none is its one new coordinate. The base
coordinates are some j. Two complete points and ten incoming directions
from the five base points span the two arms and their intersection. -/
def Border (A : Fin 2 → Fin 4 → ℂ) (B C : Fin 2 → LocalAxis → ℂ)
    (a : Fin 5 → Fin 4 → ℂ) (b c : Fin 5 → Fin 3 → ℂ) : Prop :=
  ∀ T : Fin 4 → LocalAxis → LocalAxis → ℂ,
    ∃ u : Fin 2 → Fin 4 → ℂ, ∃ v w : Fin 2 → LocalAxis → ℂ, ∃ vb wb : Fin 5 → ℂ,
      ∀ i j k, (j=none ∨ k=none) →
        T i j k = (∑ t, (u t i*(B t j*C t k) + A t i*(v t j*C t k) + A t i*(B t j*w t k))) +
          ∑ t, (a t i*((if j=none then vb t else 0)*k.elim 0 (c t)) +
            a t i*(j.elim 0 (b t)*(if k=none then wb t else 0)))

end FourSlice

namespace FourSlice.Finite

def prodFin {A B : Type} {a b : ℕ} (ea : A ≃ Fin a) (eb : B ≃ Fin b) : A×B ≃ Fin (a*b) :=
  (ea.prodCongr eb).trans finProdFinEquiv
def sumFin {A B : Type} {a b : ℕ} (ea : A ≃ Fin a) (eb : B ≃ Fin b) : A⊕B ≃ Fin (a+b) :=
  (Equiv.sumCongr ea eb).trans finSumFinEquiv

def tab {m n : ℕ} (data : Array ℤ) (i : Fin m) (j : Fin n) : ℤ := data[i.val*n+j.val]?.getD 0
abbrev R₀ := Fin 4 × Fin 3 × Fin 3
abbrev C₀ := Fin 5 × (Fin 4 ⊕ (Fin 3 ⊕ Fin 3))
def r₀ : R₀ ≃ Fin 36 := prodFin (Equiv.refl _) (prodFin (Equiv.refl _) (Equiv.refl _))
def c₀ : C₀ ≃ Fin 50 := prodFin (Equiv.refl _) (sumFin (Equiv.refl _) finSumFinEquiv)

def baseMatrix (a : Fin 5 → Fin 4 → ℤ) (b c : Fin 5 → Fin 3 → ℤ) : Matrix R₀ C₀ ℤ
  | (i,j,k),(t,Sum.inl h) => if h=i then b t j*c t k else 0
  | (i,j,k),(t,Sum.inr (Sum.inl h)) => if h=j then a t i*c t k else 0
  | (i,j,k),(t,Sum.inr (Sum.inr h)) => if h=k then a t i*b t j else 0

lemma base_of_matrix (a : Fin 5 → Fin 4 → ℤ) (b c : Fin 5 → Fin 3 → ℤ)
    (hs : Function.Surjective ((baseMatrix a b c).map (Int.castRingHom ℂ)).mulVec) :
    Base (fun t i => (a t i : ℂ)) (fun t i => (b t i : ℂ)) (fun t i => (c t i : ℂ)) := by
  intro T
  obtain ⟨y,hy⟩ := hs fun z => T z.1 z.2.1 z.2.2
  refine ⟨fun t i => y (t,Sum.inl i),fun t j => y (t,Sum.inr (Sum.inl j)),fun t k => y (t,Sum.inr (Sum.inr k)),?_⟩
  intro i j k
  refine (congrFun hy (i,j,k)).symm.trans ?_
  change (∑ z : C₀, ((baseMatrix a b c (i,j,k) z : ℤ) : ℂ)*y z) = _
  simp [baseMatrix,Fintype.sum_prod_type,Fintype.sum_sum_type,apply_ite,Finset.sum_ite_eq',
    mul_comm,mul_assoc,add_assoc]

abbrev R₁ := Fin 4 × (LocalAxis ⊕ Fin 3)
abbrev C₁ := (Fin 2 × (Fin 4 ⊕ (LocalAxis ⊕ LocalAxis))) ⊕ (Fin 5 × Fin 2)
def r₁ : R₁ ≃ Fin 28 := prodFin (Equiv.refl _) (sumFin (finSuccEquiv 3).symm (Equiv.refl _))
def c₁ : C₁ ≃ Fin 34 :=
  sumFin (prodFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (finSuccEquiv 3).symm (finSuccEquiv 3).symm)))
    (prodFin (Equiv.refl _) (Equiv.refl _))
def coords : R₁ → Fin 4 × LocalAxis × LocalAxis
  | (i,Sum.inl k) => (i,none,k)
  | (i,Sum.inr j) => (i,some j,none)

def borderMatrix (A : Fin 2 → Fin 4 → ℤ) (B C : Fin 2 → LocalAxis → ℤ)
    (a : Fin 5 → Fin 4 → ℤ) (b c : Fin 5 → Fin 3 → ℤ) : Matrix R₁ C₁ ℤ := fun r z =>
  let (i,j,k) := coords r
  match z with
  | Sum.inl (t,Sum.inl h) => if h=i then B t j*C t k else 0
  | Sum.inl (t,Sum.inr (Sum.inl h)) => if h=j then A t i*C t k else 0
  | Sum.inl (t,Sum.inr (Sum.inr h)) => if h=k then A t i*B t j else 0
  | Sum.inr (t,h) => if h=0 then (if j=none then a t i*k.elim 0 (c t) else 0)
    else (if k=none then a t i*j.elim 0 (b t) else 0)

lemma border_of_matrix (A : Fin 2 → Fin 4 → ℤ) (B C : Fin 2 → LocalAxis → ℤ)
    (a : Fin 5 → Fin 4 → ℤ) (b c : Fin 5 → Fin 3 → ℤ)
    (hs : Function.Surjective ((borderMatrix A B C a b c).map (Int.castRingHom ℂ)).mulVec) :
    Border (fun t i => (A t i : ℂ)) (fun t i => (B t i : ℂ)) (fun t i => (C t i : ℂ))
      (fun t i => (a t i : ℂ)) (fun t i => (b t i : ℂ)) (fun t i => (c t i : ℂ)) := by
  intro T
  obtain ⟨y,hy⟩ := hs fun z => T (coords z).1 (coords z).2.1 (coords z).2.2
  refine ⟨fun t i => y (Sum.inl (t,Sum.inl i)),fun t j => y (Sum.inl (t,Sum.inr (Sum.inl j))),
    fun t k => y (Sum.inl (t,Sum.inr (Sum.inr k))),fun t => y (Sum.inr (t,0)),fun t => y (Sum.inr (t,1)),?_⟩
  intro i j k he
  obtain ⟨r,hr⟩ : ∃ r : R₁, coords r=(i,j,k) := by
    cases j with
    | none => exact ⟨(i,Sum.inl k),rfl⟩
    | some j =>
      have hk := he.resolve_left (by simp)
      subst k
      exact ⟨(i,Sum.inr j),rfl⟩
  have heq := congrFun hy r
  change (∑ z : C₁, ((borderMatrix A B C a b c r z : ℤ) : ℂ)*y z) = T (coords r).1 (coords r).2.1 (coords r).2.2 at heq
  rw [hr] at heq
  refine heq.symm.trans ?_
  rw [Fintype.sum_sum_type]
  congr 1
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    simp [borderMatrix,hr,apply_ite,Finset.sum_ite_eq']
    ring
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [Fin.sum_univ_two]
    cases j <;> cases k <;> simp [borderMatrix,hr,mul_comm,mul_assoc]

end FourSlice.Finite

namespace FourSlice.Finite.Parity

def intBit (b : Bool) : ℤ := if b then 1 else 0
def fieldBit (b : Bool) : ZMod 2 := if b then 1 else 0

lemma cast_intBit (b : Bool) : ((intBit b : ℤ) : ZMod 2) = fieldBit b := by cases b <;> rfl

lemma fieldBit_xor (a b : Bool) : fieldBit (a ^^ b) = fieldBit a + fieldBit b := by
  cases a <;> cases b <;> decide

/-- XOR of the columns whose index occurs in the mask. -/
def xorColumns (cols : ℕ → ℕ) (mask : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => xorColumns cols mask m ^^^ (if mask.testBit m then cols m else 0)

lemma xorColumns_entry (cols : ℕ → ℕ) (mask row m : ℕ) :
    fieldBit ((xorColumns cols mask m).testBit row) =
      ∑ j ∈ Finset.range m, fieldBit ((cols j).testBit row) * fieldBit (mask.testBit j) := by
  induction m with
  | zero => simp [xorColumns, fieldBit]
  | succ m ih =>
    rw [xorColumns, Nat.testBit_xor, fieldBit_xor, ih, Finset.sum_range_succ]
    cases mask.testBit m <;> simp [fieldBit]

lemma complex_surjectivity {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℤ) (B : Matrix κ ι ℤ)
    (hab : A.map (Int.castRingHom (ZMod 2)) * B.map (Int.castRingHom (ZMod 2)) = 1) :
    Function.Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  let C := A * B
  have h2 : ((C.det : ℤ) : ZMod 2) = 1 := by
    change (Int.castRingHom (ZMod 2)) C.det = 1
    rw [RingHom.map_det, RingHom.mapMatrix_apply, show C = A * B from rfl, Matrix.map_mul, hab,
      Matrix.det_one]
  have hne : C.det ≠ 0 := by
    intro he
    rw [he, Int.cast_zero] at h2
    exact zero_ne_one h2
  have hu : IsUnit (C.map (Int.castRingHom ℂ)).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    change (C.det : ℂ) ≠ 0
    exact_mod_cast hne
  have hsurj : Function.Surjective (C.map (Int.castRingHom ℂ)).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  refine ⟨(B.map (Int.castRingHom ℂ)).mulVec x, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul]
  exact hx

lemma surjective_of_certificate {d m : ℕ} (A : Matrix (Fin d) (Fin m) ℤ) (cols masks : ℕ → ℕ)
    (hcols : ∀ i j, A i j = intBit ((cols j.val).testBit i.val))
    (hcheck : ∀ i : Fin d, xorColumns cols (masks i.val) m = 2 ^ i.val) :
    Function.Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  let B : Matrix (Fin m) (Fin d) ℤ := fun j i => intBit ((masks i.val).testBit j.val)
  apply complex_surjectivity A B
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  calc
    _ = ∑ k : Fin m, fieldBit ((cols k.val).testBit i.val) * fieldBit ((masks j.val).testBit k.val) := by
      apply Finset.sum_congr rfl
      intro k _
      change ((A i k : ℤ) : ZMod 2) * ((intBit ((masks j.val).testBit k.val) : ℤ) : ZMod 2) = _
      rw [hcols, cast_intBit, cast_intBit]
    _ = ∑ k ∈ Finset.range m, fieldBit ((cols k).testBit i.val) * fieldBit ((masks j.val).testBit k) := by
      exact Fin.sum_univ_eq_sum_range (fun k => fieldBit ((cols k).testBit i.val) *
        fieldBit ((masks j.val).testBit k)) m
    _ = fieldBit ((xorColumns cols (masks j.val) m).testBit i.val) := (xorColumns_entry _ _ _ _).symm
    _ = _ := by
      rw [hcheck j, Nat.testBit_two_pow]
      by_cases h : i = j
      · subst j; simp [fieldBit]
      · have hji : j.val ≠ i.val := fun hv => h (Fin.ext hv.symm)
        simp [h, hji, fieldBit]

end FourSlice.Finite.Parity

namespace FourSlice.Finite

private lemma reindexed_rank {I K : Type} [Fintype K] {d n : ℕ}
    (M : Matrix I K ℤ) (rows : I ≃ Fin d) (cols : K ≃ Fin n) (words masks : ℕ → ℕ)
    (entries : ∀ i : Fin d, ∀ j : Fin n, M (rows.symm i) (cols.symm j) = Parity.intBit ((words j.val).testBit i.val))
    (checked : ∀ i : Fin d, Parity.xorColumns words (masks i.val) n = 2^i.val) :
    Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  let F : Matrix (Fin d) (Fin n) ℤ := fun i j => M (rows.symm i) (cols.symm j)
  have hs := Parity.surjective_of_certificate F words masks entries checked
  intro y
  obtain ⟨z,hz⟩ := hs fun i => y (rows.symm i)
  refine ⟨fun k => z (cols k),?_⟩
  funext i
  have h := congrFun hz (rows i)
  change (∑ k, ((F (rows i) k : ℤ) : ℂ) * z k) = y (rows.symm (rows i)) at h
  change (∑ k, (M i k : ℂ)*z (cols k)) = y i
  have he := cols.sum_comp (fun j : Fin n => (M i (cols.symm j) : ℂ)*z j)
  simp only [Equiv.symm_apply_apply] at he
  rw [he]
  simpa only [F,Equiv.symm_apply_apply] using h


namespace BaseWitness

def A : Fin 5 → Fin 4 → ℤ := tab #[1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1]
def B : Fin 5 → Fin 3 → ℤ := tab #[0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1]
def C : Fin 5 → Fin 3 → ℤ := tab #[0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1]

def M : Matrix R₀ C₀ ℤ := baseMatrix A B C
private def columnWords : Array ℕ := #[0x120, 0x24000, 0x4800000, 0x900000000, 0x804, 0x4020, 0x20100, 0x9048, 0x12090, 0x24120, 0x9, 0x1200, 0x240000, 0x48000000, 0x40000, 0x200000, 0x1000000, 0x240000, 0x480000, 0x900000, 0x186, 0x30c00, 0x6180000, 0xc30000000, 0x30180000, 0x180c00000, 0xc06000000, 0x209040000, 0x412080000, 0x824100000, 0x10, 0x2000, 0x400000, 0x80000000, 0x80002, 0x400010, 0x2000080, 0x200008, 0x400010, 0x800020, 0x140, 0x28000, 0x5000000, 0xa00000000, 0x28000a05, 0x140005028, 0xa00028140, 0x200008040, 0x400010080, 0x800020100]
private def rightMasks : Array ℕ := #[0x2000005400, 0x500040000, 0x49400590001, 0x2000005000, 0x40000000, 0x48000010004, 0x58000010005, 0x11004c0004, 0x48000010005, 0x320000058a3, 0x5c0340133, 0x49400590011, 0x320000050a3, 0x80000000, 0x48000010024, 0x68000010026, 0x11c04c0104, 0x48000010026, 0x4000, 0x100040000, 0x40000090004, 0x5000, 0x100000000, 0x40000010004, 0x10000, 0x1004c0004, 0x40000010000, 0xc030a00400c, 0x213c4000c, 0x40312c90008, 0xc030a00600c, 0x200000000, 0x40302010004, 0xc030201000c, 0x2038c0008, 0x4030201000c]
private def word (j : ℕ) := columnWords[j]?.getD 0
private def mask (i : ℕ) := rightMasks[i]?.getD 0

lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  apply reindexed_rank M r₀ c₀ word mask
  · decide +kernel
  · decide +kernel

end BaseWitness

namespace BorderWitness

def A : Fin 2 → Fin 4 → ℤ := tab #[0, 0, 0, 1, 1, 0, 0, 0]
def B (t : Fin 2) (j : LocalAxis) : ℤ := tab #[1, 0, 0, 0, 1, 1, 0, 1] t ((finSuccEquiv 3).symm j)
def C (t : Fin 2) (j : LocalAxis) : ℤ := tab #[1, 0, 1, 1, 1, 0, 1, 0] t ((finSuccEquiv 3).symm j)
def a : Fin 5 → Fin 4 → ℤ := tab #[1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1]
def b : Fin 5 → Fin 3 → ℤ := tab #[0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0]
def c : Fin 5 → Fin 3 → ℤ := tab #[0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0]

def M : Matrix R₁ C₁ ℤ := borderMatrix A B C a b c
private def columnWords : Array ℕ := #[0xd, 0x680, 0x34000, 0x1a00000, 0x1a00000, 0x2000000, 0x4000000, 0x8000000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x55, 0x2a80, 0x154000, 0xaa00000, 0x5, 0x10, 0x20, 0x40, 0x51, 0x2, 0x4, 0x8, 0x10004, 0x80020, 0x183060c, 0x2040810, 0x180060c, 0xa002850, 0x140050a, 0xe003870, 0xc18000, 0x2040000]
private def rightMasks : Array ℕ := #[0x111000, 0x200000, 0x101000, 0x10001, 0x20000, 0x40000, 0x31000, 0x1011110b, 0x602037ab, 0x301021ab, 0x200130a2, 0x208020000, 0xa0040040, 0x2280310a0, 0x14000004, 0x101101600, 0x1101000, 0x15101000, 0x200000020, 0x2040000, 0x215105024, 0x100, 0x200, 0x400, 0x508, 0x20, 0x40, 0x80]
private def word (j : ℕ) := columnWords[j]?.getD 0
private def mask (i : ℕ) := rightMasks[i]?.getD 0

lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  apply reindexed_rank M r₁ c₁ word mask
  · decide +kernel
  · decide +kernel

end BorderWitness

end FourSlice.Finite

namespace FourSlice

open _root_.FourSlice.Finite

lemma base_witness : ∃ a : Fin 5 → Fin 4 → ℂ, ∃ b c : Fin 5 → Fin 3 → ℂ, Base a b c := by
  exact ⟨_,_,_,base_of_matrix BaseWitness.A BaseWitness.B BaseWitness.C BaseWitness.rank⟩

lemma border_witness : ∃ A : Fin 2 → Fin 4 → ℂ, ∃ B C : Fin 2 → LocalAxis → ℂ,
    ∃ a : Fin 5 → Fin 4 → ℂ, ∃ b c : Fin 5 → Fin 3 → ℂ, Border A B C a b c := by
  exact ⟨_,_,_,_,_,_,border_of_matrix BorderWitness.A BorderWitness.B BorderWitness.C
    BorderWitness.a BorderWitness.b BorderWitness.c BorderWitness.rank⟩

end FourSlice

namespace FourSlice.Grid

open MvPolynomial

/-- A single surjective specialization gives a polynomial whose nonvanishing
guarantees surjectivity. Its determinant uses a fixed right inverse at that point. -/
lemma surjectivity_polynomial {I J V : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (M : Matrix I J (MvPolynomial V ℂ)) (x₀ : V → ℂ)
    (h₀ : Function.Surjective (M.map (eval x₀)).mulVec) :
    ∃ Q : MvPolynomial V ℂ, Q ≠ 0 ∧ ∀ x : V → ℂ,
      eval x Q ≠ 0 → Function.Surjective (M.map (eval x)).mulVec := by
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h₀
  let D := M * B.map (C : ℂ →+* MvPolynomial V ℂ)
  have specialize (x : V → ℂ) : eval x D.det = (M.map (eval x) * B).det := by
    have hconst : (B.map (C : ℂ →+* MvPolynomial V ℂ)).map (eval x) = B := by
      ext i j
      simp [Matrix.map_apply]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, show D = _ from rfl, Matrix.map_mul, hconst]
  have hvalue : eval x₀ D.det = 1 := by rw [specialize, hB, Matrix.det_one]
  refine ⟨D.det, ?_, ?_⟩
  · intro he
    rw [he, map_zero] at hvalue
    exact zero_ne_one hvalue
  · intro x hx
    rw [specialize] at hx
    have hprod : Function.Surjective (M.map (eval x) * B).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hx))
    intro y
    obtain ⟨z, hz⟩ := hprod y
    refine ⟨B.mulVec z, ?_⟩
    rw [Matrix.mulVec_mulVec]
    exact hz

lemma avoid_two {V : Type} {P Q : MvPolynomial V ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ∃ x : V → ℂ, eval x P ≠ 0 ∧ eval x Q ≠ 0 := by
  by_contra! h
  apply (mul_ne_zero hP hQ)
  apply MvPolynomial.funext
  intro x
  rw [map_mul, map_zero]
  by_cases hx : eval x P = 0
  · exact mul_eq_zero.mpr (Or.inl hx)
  · exact mul_eq_zero.mpr (Or.inr (h x hx))

/-- Separate specializations can verify blocks depending on the same parameters:
the product of their certificate polynomials is nonzero over the complex numbers. -/
lemma simultaneous_surjectivity {K V : Type} [Fintype K] {I J : K → Type}
    [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)] [∀ k, Fintype (J k)]
    (M : ∀ k, Matrix (I k) (J k) (MvPolynomial V ℂ))
    (h : ∀ k, ∃ x : V → ℂ, Function.Surjective ((M k).map (eval x)).mulVec)
    (P : MvPolynomial V ℂ) (hP : P ≠ 0) :
    ∃ x : V → ℂ, eval x P ≠ 0 ∧ ∀ k, Function.Surjective ((M k).map (eval x)).mulVec := by
  classical
  choose z hz using h
  choose Q hQ hgood using fun k => surjectivity_polynomial (M k) (z k) (hz k)
  have hprod : (∏ k, Q k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hQ k
  obtain ⟨x, hx, hrest⟩ := avoid_two hP hprod
  have hvals : (∏ k, eval x (Q k)) ≠ 0 := by simpa only [map_prod] using hrest
  exact ⟨x, hx, fun k => hgood k x (Finset.prod_ne_zero_iff.mp hvals k (Finset.mem_univ k))⟩

/-- A priority for each sector is enough. Distinct sectors at the same priority
are disjoint on their diagonal rows and columns. -/
lemma graded_surjective {R C S : Type} [Fintype R] [Fintype C] [Fintype S] [DecidableEq S]
    (f : R → S) (g : C → S) (priority : S → Fin 3) (A : Matrix R C ℂ)
    (zero_above : ∀ i j, f i ≠ g j → priority (f i) ≤ priority (g j) → A i j=0)
    (local_maps : ∀ s : S, Function.Surjective
      (A.submatrix (fun i : {i // f i=s} => i.val) (fun j : {j // g j=s} => j.val)).mulVec) :
    Function.Surjective A.mulVec := by
  classical
  have hpre (j : R) : ∃ v : {k // g k=f j} → ℂ, ∀ i : {i // f i=f j},
      (∑ k, A i.val k.val * v k) = if i.val=j then 1 else 0 := by
    obtain ⟨v,hv⟩ := local_maps (f j) fun i => if i.val=j then 1 else 0
    exact ⟨v,fun i => congrFun hv i⟩
  choose v hv using hpre
  let B : Matrix C R ℂ := fun k j => if h : g k=f j then v j ⟨k,h⟩ else 0
  let L := A*B
  have entries (i j : R) : L i j = ∑ k : {k // g k=f j}, A i k.val*v j k := by
    change (∑ k : C, A i k*(if h : g k=f j then v j ⟨k,h⟩ else 0)) = _
    let F (k : C) := A i k * (if h : g k=f j then v j ⟨k,h⟩ else 0)
    have e := (Equiv.sumCompl (fun k : C => g k=f j)).sum_comp F
    rw [Fintype.sum_sum_type] at e
    have hp (q : {k // g k=f j}) : g q.val=f j := q.property
    have hn (q : {k // g k≠f j}) : g q.val≠f j := q.property
    simpa [F,hp,hn] using e.symm
  have off (i j : R) (h : f i ≠ f j) (hle : priority (f i) ≤ priority (f j)) : L i j=0 := by
    rw [entries]
    apply Finset.sum_eq_zero
    intro k _
    rw [zero_above i k.val (by simpa only [k.property] using h)
      (by simpa only [k.property] using hle),zero_mul]
  have triangular : L.BlockTriangular (fun i => OrderDual.toDual (priority (f i))) := by
    intro i j h
    change priority (f i) < priority (f j) at h
    exact off i j (fun he => (ne_of_lt h) (congrArg priority he)) (le_of_lt h)
  have diag (s : (Fin 3)ᵒᵈ) : L.toSquareBlock (fun i => OrderDual.toDual (priority (f i))) s = 1 := by
    ext i j
    obtain ⟨i,hi⟩ := i
    obtain ⟨j,hj⟩ := j
    have hlev : priority (f i)=priority (f j) := hi.trans hj.symm
    change L i j = _
    by_cases hij : f i=f j
    · rw [entries,hv j ⟨i,hij⟩,Matrix.one_apply]
      simp only [Subtype.mk.injEq]
    · rw [off i j hij (le_of_eq hlev),Matrix.one_apply]
      simp [show i ≠ j from fun h => hij (congrArg f h)]
  have detL : L.det=1 := by rw [triangular.det_fintype]; simp [diag]
  have hL : Function.Surjective L.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (by rw [detL]; exact isUnit_one))
  intro y
  obtain ⟨z,hz⟩ := hL y
  refine ⟨B.mulVec z,?_⟩
  rw [Matrix.mulVec_mulVec]
  exact hz

/-- Transfer the row equations of a finite template to a global sector. Every
row needed by the sector has a local representative. Coincident selected
columns can be combined by summing their coefficients. -/
lemma cover_matrix {R C I J : Type} [Fintype C] [DecidableEq C] [Fintype J]
    (A : Matrix R C ℂ) (L : Matrix I J ℂ) (rmap : I → R) (cmap : J → C)
    (hR : Function.Surjective rmap) (hM : ∀ i j, A (rmap i) (cmap j)=L i j)
    (hs : Function.Surjective L.mulVec) : Function.Surjective A.mulVec := by
  classical
  let E : Matrix C J ℂ := fun k j => if k=cmap j then 1 else 0
  have hcols (i j) : (A*E) (rmap i) j=L i j := by
    rw [Matrix.mul_apply]
    simpa [E,mul_ite,Finset.sum_ite_eq'] using hM i j
  intro y
  obtain ⟨z,hz⟩ := hs (fun i => y (rmap i))
  refine ⟨E.mulVec z,?_⟩
  rw [Matrix.mulVec_mulVec]
  funext r
  obtain ⟨i,rfl⟩ := hR r
  change (∑ j, (A*E) (rmap i) j*z j) = _
  simpa only [hcols,Matrix.mulVec,dotProduct] using congrFun hz i

end FourSlice.Grid

namespace FourSlice.Grid

open MvPolynomial

abbrev Pt (G : Type) := Fin 5 ⊕ (G × Fin 2)
abbrev Axis (G : Type) := Fin 3 ⊕ G
abbrev Dir (I : Type) := Fin 4 ⊕ (I ⊕ I)
abbrev V (G : Type) := (Fin 5 × Dir (Fin 3)) ⊕ (G × Fin 2 × Dir LocalAxis)
abbrev RR (G : Type) := Fin 4 × Axis G × Axis G
abbrev CC (G : Type) := Pt G × Dir (Axis G)
abbrev Pair (G : Type) := {p : G × G // p.1 ≠ p.2}
abbrev Sector (G : Type) := Unit ⊕ (G ⊕ Pair G)
abbrev Arm := Fin 3 ⊕ (Fin 3 ⊕ Unit)

def arms : Arm → LocalAxis × LocalAxis
  | .inl k => (none,some k)
  | .inr (.inl j) => (some j,none)
  | .inr (.inr _) => (none,none)

def loc {G : Type} (g : G) : LocalAxis → Axis G
  | none => .inr g
  | some j => .inl j

def Row {G : Type} : Sector G → Type
  | .inl _ => Fin 4 × Fin 3 × Fin 3
  | .inr (.inl _) => Fin 4 × Arm
  | .inr (.inr _) => Fin 4

def Col {G : Type} : Sector G → Type
  | .inl _ => Fin 5 × Dir (Fin 3)
  | .inr (.inl _) => (Fin 2 × Dir LocalAxis) ⊕ (Fin 5 × Bool)
  | .inr (.inr _) => Fin 2 ⊕ Fin 2

instance {G : Type} (s : Sector G) : Fintype (Row s) := by rcases s with u|g|p <;> dsimp [Row] <;> infer_instance
instance {G : Type} (s : Sector G) : DecidableEq (Row s) := by rcases s with u|g|p <;> dsimp [Row] <;> infer_instance
instance {G : Type} (s : Sector G) : Fintype (Col s) := by rcases s with u|g|p <;> dsimp [Col] <;> infer_instance
instance {G : Type} (s : Sector G) : DecidableEq (Col s) := by rcases s with u|g|p <;> dsimp [Col] <;> infer_instance

def row {G : Type} : (s : Sector G) → Row s → RR G
  | .inl _,(i,j,k) => (i,.inl j,.inl k)
  | .inr (.inl g),(i,z) => (i,loc g (arms z).1,loc g (arms z).2)
  | .inr (.inr p),i => (i,.inr p.val.1,.inr p.val.2)

def col {G : Type} : (s : Sector G) → Col s → CC G
  | .inl _,(t,h) => (.inl t,h.map id (Sum.map Sum.inl Sum.inl))
  | .inr (.inl g),.inl (t,h) => (.inr (g,t),h.map id (Sum.map (loc g) (loc g)))
  | .inr (.inl g),.inr (t,false) => (.inl t,.inr (.inl (.inr g)))
  | .inr (.inl g),.inr (t,true) => (.inl t,.inr (.inr (.inr g)))
  | .inr (.inr p),.inl t => (.inr (p.val.1,t),.inr (.inr (.inr p.val.2)))
  | .inr (.inr p),.inr t => (.inr (p.val.2,t),.inr (.inl (.inr p.val.1)))

def lev {G : Type} : Sector G → Fin 3
  | .inl _ => 2
  | .inr (.inl _) => 1
  | .inr (.inr _) => 0

section
variable {G K : Type} [DecidableEq G] [CommSemiring K]

def A (x : V G → K) : Pt G → Fin 4 → K
  | .inl t,i => x (.inl (t,.inl i))
  | .inr (g,t),i => x (.inr (g,t,.inl i))

def tail (b : Fin 5 → Fin 3 → K) (B : G → Fin 2 → LocalAxis → K) : Pt G → Axis G → K
  | .inl t,.inl j => b t j
  | .inl _,.inr _ => 0
  | .inr (g,t),.inl j => B g t (some j)
  | .inr (g,t),.inr h => if h=g then B g t none else 0

def B (x : V G → K) := tail (fun t j => x (.inl (t,.inr (.inl j)))) (fun g t j => x (.inr (g,t,.inr (.inl j))))
def Cc (x : V G → K) := tail (fun t k => x (.inl (t,.inr (.inr k)))) (fun g t k => x (.inr (g,t,.inr (.inr k))))

def tangent (x : V G → K) (r : RR G) : CC G → K
  | (t,.inl h) => if h=r.1 then B x t r.2.1 * Cc x t r.2.2 else 0
  | (t,.inr (.inl h)) => if h=r.2.1 then A x t r.1 * Cc x t r.2.2 else 0
  | (t,.inr (.inr h)) => if h=r.2.2 then A x t r.1 * B x t r.2.1 else 0

def full (x : V G → K) : Matrix (Σ s : Sector G, Row s) (Σ s : Sector G, Col s) K :=
  fun r c => tangent x (row r.1 r.2) (col c.1 c.2)

def block (x : V G → K) (s : Sector G) : Matrix (Row s) (Col s) K :=
  fun r c => tangent x (row s r) (col s c)

lemma tail_loc (b : Fin 5 → Fin 3 → K) (H : G → Fin 2 → LocalAxis → K) (g : G) (t : Fin 2) (j : LocalAxis) :
    tail b H (.inr (g,t)) (loc g j) = H g t j := by cases j <;> simp [tail,loc]

lemma base_loc (b : Fin 5 → Fin 3 → K) (H : G → Fin 2 → LocalAxis → K) (g : G) (t : Fin 5) (j : LocalAxis) :
    tail b H (.inl t) (loc g j) = j.elim 0 (b t) := by cases j <;> rfl

omit [DecidableEq G] in
lemma loc_eq (g : G) (j k : LocalAxis) : loc g j=loc g k ↔ j=k := by cases j <;> cases k <;> simp [loc]

private lemma tail_map {L : Type} [CommSemiring L] (φ : K →+* L) (b : Fin 5 → Fin 3 → K)
    (H : G → Fin 2 → LocalAxis → K) (t : Pt G) (j : Axis G) :
    φ (tail b H t j) = tail (fun t j => φ (b t j)) (fun g t j => φ (H g t j)) t j := by
  rcases t with t|⟨g,t⟩ <;> rcases j with j|h <;> simp only [tail,map_zero]
  by_cases he : h=g <;> simp [he]

lemma block_eval (x : V G → ℂ) (s : Sector G) :
    (block (MvPolynomial.X : V G → MvPolynomial (V G) ℂ) s).map (eval x) = block x s := by
  ext r j
  change eval x (tangent MvPolynomial.X (row s r) (col s j)) = tangent x (row s r) (col s j)
  generalize hc : col s j = z
  rcases z with ⟨t,h|h|h⟩ <;> rcases t with t|⟨g,t⟩ <;>
    simp only [tangent,A,B,Cc,apply_ite,tail_map,map_mul,map_zero,eval_X]
  all_goals split <;> simp_all

end

lemma row_surj {G : Type} [DecidableEq G] : Function.Surjective (fun z : Σ s : Sector G, Row s => row z.1 z.2) := by
  rintro ⟨i,j|j,k|k⟩
  · exact ⟨⟨.inl (),i,j,k⟩,rfl⟩
  · exact ⟨⟨.inr (.inl k),i,.inr (.inl j)⟩,rfl⟩
  · exact ⟨⟨.inr (.inl j),i,.inl k⟩,rfl⟩
  · by_cases h : j=k
    · subst k
      exact ⟨⟨.inr (.inl j),i,.inr (.inr ())⟩,rfl⟩
    · exact ⟨⟨.inr (.inr ⟨(j,k),h⟩),i⟩,rfl⟩

end FourSlice.Grid

namespace FourSlice.Grid

variable {G : Type} [DecidableEq G]

def param (a : Fin 5 → Fin 4 → ℂ) (b c : Fin 5 → Fin 3 → ℂ)
    (A : G → Fin 2 → Fin 4 → ℂ) (B C : G → Fin 2 → LocalAxis → ℂ) : V G → ℂ
  | .inl (t,.inl i) => a t i
  | .inl (t,.inr (.inl j)) => b t j
  | .inl (t,.inr (.inr k)) => c t k
  | .inr (g,t,.inl i) => A g t i
  | .inr (g,t,.inr (.inl j)) => B g t j
  | .inr (g,t,.inr (.inr k)) => C g t k

lemma base_rank (a : Fin 5 → Fin 4 → ℂ) (b c : Fin 5 → Fin 3 → ℂ) (hb : Base a b c) :
    ∃ x : V G → ℂ, Function.Surjective (block x (.inl ())).mulVec := by
  classical
  let x : V G → ℂ := param a b c 0 0 0
  refine ⟨x,?_⟩
  intro y
  obtain ⟨u,v,w,hu⟩ := hb fun i j k => y (i,j,k)
  let z : Fin 5 × Dir (Fin 3) → ℂ := fun (t,h) => h.elim (u t) (Sum.elim (v t) (w t))
  refine ⟨z,?_⟩
  funext r
  obtain ⟨i,j,k⟩ := r
  change (∑ s : Fin 5 × Dir (Fin 3), tangent x (i,.inl j,.inl k) (col (.inl ()) s) * z s) = y (i,j,k)
  rw [hu,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp [tangent,col,x,param,A,B,Cc,tail,z,ite_mul,Finset.sum_ite_eq']
  ring

def target (y : Fin 4 × Arm → ℂ) (i : Fin 4) : LocalAxis → LocalAxis → ℂ
  | none,none => y (i,.inr (.inr ()))
  | none,some k => y (i,.inl k)
  | some j,none => y (i,.inr (.inl j))
  | some _,some _ => 0

lemma target_arms (y : Fin 4 × Arm → ℂ) (i : Fin 4) (r : Arm) :
    target y i (arms r).1 (arms r).2=y (i,r) := by rcases r with k|j|⟨⟩ <;> rfl

lemma arms_hit (r : Arm) : (arms r).1=none ∨ (arms r).2=none := by rcases r with k|j|u <;> simp [arms]

lemma border_rank (g : G) (aa : Fin 2 → Fin 4 → ℂ) (bb cc : Fin 2 → LocalAxis → ℂ)
    (a : Fin 5 → Fin 4 → ℂ) (b c : Fin 5 → Fin 3 → ℂ) (hr : Border aa bb cc a b c) :
    ∃ x : V G → ℂ, Function.Surjective (block x (.inr (.inl g))).mulVec := by
  classical
  let x : V G → ℂ := param a b c (fun _ => aa) (fun _ => bb) (fun _ => cc)
  refine ⟨x,?_⟩
  intro y
  obtain ⟨u,v,w,vb,wb,hu⟩ := hr (target y)
  let z : (Fin 2 × Dir LocalAxis) ⊕ (Fin 5 × Bool) → ℂ
    | .inl (t,h) => h.elim (u t) (Sum.elim (v t) (w t))
    | .inr (t,false) => vb t
    | .inr (t,true) => wb t
  refine ⟨z,?_⟩
  funext r
  obtain ⟨i,r⟩ := r
  change (∑ s : (Fin 2 × Dir LocalAxis) ⊕ (Fin 5 × Bool),
    tangent x (i,loc g (arms r).1,loc g (arms r).2) (col (.inr (.inl g)) s) * z s) = y (i,r)
  rw [← target_arms y i r,hu i _ _ (arms_hit r),Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_prod_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    simp [tangent,col,x,param,A,B,Cc,z,tail_loc,loc_eq,ite_mul,Finset.sum_ite_eq']
    ring
  · apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_bool]
    rcases r with k|j|⟨⟩ <;> simp [tangent,col,x,param,A,B,Cc,tail,z,arms,loc] <;> ring

lemma cross_rank (p : Pair G) : ∃ x : V G → ℂ, Function.Surjective (block x (.inr (.inr p))).mulVec := by
  classical
  let e : (Fin 2 ⊕ Fin 2) ≃ Fin 4 := finSumFinEquiv
  let a (g : G) (t : Fin 2) (i : Fin 4) : ℂ :=
    if g=p.val.1 then (if e (.inl t)=i then 1 else 0) else (if e (.inr t)=i then 1 else 0)
  let x : V G → ℂ := param 0 0 0 a (fun _ _ _ => 1) (fun _ _ _ => 1)
  refine ⟨x,?_⟩
  intro y
  refine ⟨fun j => y (e j),?_⟩
  funext i
  change (∑ j : Fin 2 ⊕ Fin 2, tangent x (row (.inr (.inr p)) i) (col (.inr (.inr p)) j)*y (e j))=y i
  have he (j : Fin 2 ⊕ Fin 2) : tangent x (row (.inr (.inr p)) i) (col (.inr (.inr p)) j) =
      (if e j=i then 1 else 0) := by cases j <;> simp [row,col,tangent,x,param,A,B,Cc,tail,a,p.property.symm]
  simp_rw [he]
  have hh := e.sum_comp (fun k => (if k=i then (1:ℂ) else 0)*y k)
  refine hh.trans ?_
  simp only [ite_mul,one_mul,zero_mul]
  refine (Finset.sum_congr rfl (fun j _ => ?_)).trans (Fintype.sum_ite_eq' i (fun j : Fin 4 => y j))
  by_cases hij : j=i <;> simp [hij]
  · exact fun hi => (hi rfl).elim
  · exact fun h => (hij h).elim

end FourSlice.Grid

namespace FourSlice.Grid

variable {G : Type} [DecidableEq G] (x : V G → ℂ)

private lemma arm_base (g : G) (r : Row (.inr (.inl g))) (z : Col (G:=G) (.inl ())) :
    tangent x (row (.inr (.inl g)) r) (col (.inl ()) z)=0 := by
  rcases r with ⟨i,k|j|⟨⟩⟩ <;> rcases z with ⟨t,h|h|h⟩ <;>
    simp [row,col,tangent,arms,loc,B,Cc,tail]

private lemma arm_other (g h : G) (gh : g ≠ h) (r : Row (.inr (.inl g))) (z : Col (.inr (.inl h))) :
    tangent x (row (.inr (.inl g)) r) (col (.inr (.inl h)) z)=0 := by
  rcases r with ⟨i,k|j|⟨⟩⟩ <;> rcases z with ⟨t,u|(_|u)|(_|u)⟩|⟨t,_|_⟩ <;>
    simp [row,col,tangent,arms,loc,B,Cc,tail,gh,gh.symm]

private lemma pair_base (p : Pair G) (r : Fin 4) (z : Col (G:=G) (.inl ())) :
    tangent x (row (.inr (.inr p)) r) (col (.inl ()) z)=0 := by
  rcases z with ⟨t,h|h|h⟩ <;> simp [row,col,tangent,B,Cc,tail]

private lemma pair_arm (p : Pair G) (h : G) (r : Fin 4) (z : Col (.inr (.inl h))) :
    tangent x (row (.inr (.inr p)) r) (col (.inr (.inl h)) z)=0 := by
  rcases p with ⟨⟨g,k⟩,hg⟩
  change g≠k at hg
  rcases z with ⟨t,u|(_|u)|(_|u)⟩|⟨t,_|_⟩ <;>
    by_cases he : g=h <;> by_cases hf : k=h <;>
    simp_all [row,col,tangent,loc,B,Cc,tail]
  all_goals grind

private lemma pair_other (p q : Pair G) (hpq : p≠q) (r : Fin 4) (z : Fin 2 ⊕ Fin 2) :
    tangent x (row (.inr (.inr p)) r) (col (.inr (.inr q)) z)=0 := by
  rcases p with ⟨⟨a,b⟩,hab⟩
  rcases q with ⟨⟨c,d⟩,hcd⟩
  have h : a=c → b≠d := by rintro rfl rfl; exact (hpq rfl).elim
  cases z <;> by_cases hac : a=c <;> by_cases hbd : b=d <;>
    simp_all [row,col,tangent,B,Cc,tail,eq_comm]

lemma off (s t : Sector G) (h : s≠t) (hl : lev s≤lev t) (r : Row s) (z : Col t) :
    tangent x (row s r) (col t z)=0 := by
  rcases s with ⟨⟩|g|p <;> rcases t with ⟨⟩|h'|q
  · exact (h rfl).elim
  · exact (by decide : ¬((2:Fin 3)≤1)) hl |>.elim
  · exact (by decide : ¬((2:Fin 3)≤0)) hl |>.elim
  · exact arm_base x g r z
  · exact arm_other x g h' (fun e => h (e ▸ rfl)) r z
  · exact (by decide : ¬((1:Fin 3)≤0)) hl |>.elim
  · exact pair_base x p r z
  · exact pair_arm x p h' r z
  · exact pair_other x p q (fun e => h (e ▸ rfl)) r z

end FourSlice.Grid

namespace FourSlice.Grid

open MvPolynomial

variable {G : Type} [Fintype G] [DecidableEq G]

def actual (x : V G → ℂ) : Matrix (RR G) (CC G) ℂ := tangent x

lemma common (hb : ∃ a b c, Base a b c) (hr : ∃ a b c d e f, Border a b c d e f) :
    ∃ x : V G → ℂ, Function.Surjective (actual x).mulVec := by
  classical
  have each (s : Sector G) : ∃ x : V G → ℂ, Function.Surjective (block x s).mulVec := by
    rcases s with ⟨⟩|g|p
    · obtain ⟨a,b,c,h⟩ := hb
      exact base_rank a b c h
    · obtain ⟨a,b,c,d,e,f,h⟩ := hr
      exact border_rank g a b c d e f h
    · exact cross_rank p
  let M (s : Sector G) := block (MvPolynomial.X : V G → MvPolynomial (V G) ℂ) s
  have openSet (s : Sector G) : ∃ x : V G → ℂ, Function.Surjective ((M s).map (eval x)).mulVec := by
    obtain ⟨x,h⟩ := each s
    exact ⟨x,by simpa only [M,block_eval] using h⟩
  obtain ⟨x,_,hx⟩ := simultaneous_surjectivity M openSet 1 one_ne_zero
  have hs (s : Sector G) : Function.Surjective (block x s).mulVec := by simpa only [M,block_eval] using hx s
  have hfull : Function.Surjective (full x).mulVec := by
    apply graded_surjective (fun r => r.1) (fun j => j.1) lev (full x)
    · rintro ⟨s,i⟩ ⟨t,j⟩ h ht
      exact off x s t h ht i j
    · intro s
      apply cover_matrix _ (block x s) (fun i => ⟨⟨s,i⟩,rfl⟩) (fun j => ⟨⟨s,j⟩,rfl⟩)
      · rintro ⟨⟨t,i⟩,ht⟩
        change t=s at ht
        subst t
        exact ⟨i,rfl⟩
      · intro i j; rfl
      · exact hs s
  exact ⟨x,cover_matrix (actual x) (full x) (fun r => row r.1 r.2) (fun j => col j.1 j.2)
    row_surj (fun _ _ => rfl) hfull⟩

lemma action (x : V G → ℂ) (z : CC G → ℂ) (i : Fin 4) (j k : Axis G) :
    (actual x).mulVec z (i,j,k) = ∑ t : Pt G,
      (z (t,.inl i)*(B x t j*Cc x t k) + A x t i*(z (t,.inr (.inl j))*Cc x t k) +
      A x t i*(B x t j*z (t,.inr (.inr k)))) := by
  classical
  change (∑ w : CC G, tangent x (i,j,k) w*z w)=_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp [tangent,ite_mul,Finset.sum_ite_eq']
  ring

end FourSlice.Grid

namespace FourSlice

open Grid

/-- A three-dimensional base and one extra coordinate per regular group suffice.
The ordered regular pairs are solved first, then the individual borders, then the base. -/
lemma spans_of_blocks (m : ℕ) (hm : 3 ≤ m) (hb : ∃ a b c, Base a b c)
    (hr : ∃ A B C a b c, Border A B C a b c) : Spans m := by
  classical
  let G := Fin (m-3)
  let e : Fin m ≃ Axis G := Fintype.equivOfCardEq (by simp [G,Axis]; omega)
  let p : Fin (2*m-1) ≃ Pt G := Fintype.equivOfCardEq (by simp [G,Pt]; omega)
  obtain ⟨x,hx⟩ := common (G:=G) hb hr
  refine ⟨fun t i => A x (p t) i,fun t j => B x (p t) (e j),fun t k => Cc x (p t) (e k),?_⟩
  intro T
  obtain ⟨z,hz⟩ := hx fun r => T r.1 (e.symm r.2.1) (e.symm r.2.2)
  refine ⟨fun t i => z (p t,.inl i),fun t j => z (p t,.inr (.inl (e j))),
    fun t k => z (p t,.inr (.inr (e k))),?_⟩
  intro i j k
  have h := (congrFun hz (i,e j,e k)).symm
  simp only [Equiv.symm_apply_apply] at h
  rw [action] at h
  exact h.trans (p.sum_comp (fun t => z (t,Sum.inl i)*(B x t (e j)*Cc x t (e k)) +
    A x t i*(z (t,Sum.inr (Sum.inl (e j)))*Cc x t (e k)) +
    A x t i*(B x t (e j)*z (t,Sum.inr (Sum.inr (e k)))))).symm

end FourSlice

namespace FourSlice

open Arxiv.«0805.3777» Set Filter
open scoped Topology

namespace Dimension

lemma interior_polynomial_zero_locus {J : Type} (P : MvPolynomial J ℂ) (hP : P ≠ 0) :
    interior {y : J → ℂ | MvPolynomial.eval y P = 0} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hn := mem_interior_iff_mem_nhds.mp ha
  rw [nhds_pi, Filter.mem_pi] at hn
  obtain ⟨I, _, box, hin, hsub⟩ := hn
  apply hP
  apply MvPolynomial.funext_set box (fun j => infinite_of_mem_nhds (a j) (hin j))
  intro y hy
  have hyI : y ∈ I.pi box := fun j _ => hy j (Set.mem_univ _)
  have hzero : MvPolynomial.eval y P = 0 := hsub hyI
  simpa only [map_zero] using hzero

lemma eval_substitution {I J : Type} (F : J → MvPolynomial I ℂ) (x : I → ℂ)
    (P : MvPolynomial J ℂ) :
    MvPolynomial.eval x (MvPolynomial.aeval F P) =
      MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) P := by
  have he : (MvPolynomial.aeval x).comp (MvPolynomial.aeval F) =
      MvPolynomial.aeval (fun j => MvPolynomial.eval x (F j)) := by
    ext j
    simp [MvPolynomial.aeval_eq_eval]
  exact DFunLike.congr_fun he P

lemma vanishing_on_polynomial_image {I J : Type} [Fintype I] [Fintype J]
    (hd : Fintype.card I < Fintype.card J) (F : J → MvPolynomial I ℂ) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧
      ∀ x : I → ℂ, MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) P = 0 := by
  classical
  have hn : ¬ AlgebraicIndependent ℂ F := by
    intro h
    have hc := h.cardinalMk_le_trdeg
    rw [MvPolynomial.trdeg_of_isDomain] at hc
    have : Fintype.card J ≤ Fintype.card I := by simpa [Cardinal.mk_fintype] using hc
    omega
  rw [algebraicIndependent_iff] at hn
  push Not at hn
  obtain ⟨P, ha, hP⟩ := hn
  refine ⟨P, hP, ?_⟩
  intro x
  rw [← eval_substitution F x P, ha, map_zero]

/-- Agreement with a lower-dimensional chart on a product of infinite subsets
extends to a polynomial identity on the entire parameter space. -/
lemma generic_chart_relation {I J K : Type} [Fintype I] [Fintype J]
    (hd : Fintype.card I < Fintype.card J) (chart : J → MvPolynomial I ℂ)
    (full : J → MvPolynomial K ℂ)
    (hnormal : ∀ x : K → ℂ, (∀ i, x i ≠ 0) →
      ∃ y : I → ℂ, ∀ j, MvPolynomial.eval x (full j) = MvPolynomial.eval y (chart j)) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧
      ∀ x : K → ℂ, MvPolynomial.eval (fun j => MvPolynomial.eval x (full j)) P = 0 := by
  classical
  obtain ⟨P, hP, hvanish⟩ := vanishing_on_polynomial_image hd chart
  have hpoly : MvPolynomial.aeval full P = 0 := by
    apply MvPolynomial.funext_set (fun _ : K => ({0}ᶜ : Set ℂ))
      (fun _ => (Set.finite_singleton (0 : ℂ)).infinite_compl)
    intro x hx
    have hx0 (i : K) : x i ≠ 0 := hx i (Set.mem_univ _)
    obtain ⟨y, hy⟩ := hnormal x hx0
    rw [eval_substitution full x P, funext hy, map_zero]
    exact hvanish y
  refine ⟨P, hP, fun x => ?_⟩
  rw [← eval_substitution full x P, hpoly, map_zero]

def index_cons_equiv (n : ℕ) (ds : List ℕ) : HolorIndex (n :: ds) ≃ Fin n × HolorIndex ds where
  toFun
    | ⟨i :: is, h⟩ => (⟨i, (List.forall₂_cons.mp h).1⟩, ⟨is, (List.forall₂_cons.mp h).2⟩)
    | ⟨[], h⟩ => nomatch h
  invFun q := ⟨q.1.val :: q.2.val, List.Forall₂.cons q.1.isLt q.2.property⟩
  left_inv := by
    rintro ⟨l, h⟩
    cases l with
    | nil => cases h
    | cons i is => rfl
  right_inv := by rintro ⟨⟨i, hi⟩, ⟨is, his⟩⟩; rfl

def vector_index_equiv (n : ℕ) : HolorIndex [n] ≃ Fin n where
  toFun i := ((index_cons_equiv n []) i).1
  invFun i := ⟨[i.val], .cons i.isLt .nil⟩
  left_inv := by
    rintro ⟨l, h⟩
    cases h with
    | cons _ h => cases h; rfl
  right_inv := by intro i; rfl

def indexEquiv (d e f : ℕ) : HolorIndex [d,e,f] ≃ Fin d × Fin e × Fin f :=
  (index_cons_equiv d [e,f]).trans (Equiv.prodCongr (Equiv.refl _)
    ((index_cons_equiv e [f]).trans (Equiv.prodCongr (Equiv.refl _) (vector_index_equiv f))))

lemma zero_is_simple (ds : List ℕ) : Holor.CPRankMax1 (0 : Holor ℂ ds) := by
  induction ds with
  | nil => exact .nil _
  | cons n ds ih =>
    have h := Holor.CPRankMax1.cons (0 : Holor ℂ [n]) (0 : Holor ℂ ds) ih
    have he : Holor.mul (0 : Holor ℂ [n]) (0 : Holor ℂ ds) = (0 : Holor ℂ (n :: ds)) := by
      funext i
      change (0 : ℂ) * 0 = 0
      simp
    rwa [he] at h

lemma decomposition_of_rank_bound {ds : List ℕ} (T : Holor ℂ ds) (r : ℕ) (hr : T.cprank ≤ r) :
    Holor.CPRankMax r T := by
  classical
  have hmin : Holor.CPRankMax T.cprank T :=
    Nat.find_spec (p := fun k => Holor.CPRankMax k T) ⟨ds.prod, Holor.cprankMax_upper_bound T⟩
  induction r, hr using Nat.le_induction with
  | base => exact hmin
  | succ k _ ih => simpa using Holor.CPRankMax.succ k 0 T (zero_is_simple ds) ih

lemma finite_sum_of_simple {ds : List ℕ} {r : ℕ} {T : Holor ℂ ds} (h : Holor.CPRankMax r T) :
    ∃ u : Fin r → Holor ℂ ds, (∀ i, Holor.CPRankMax1 (u i)) ∧ ∑ i, u i = T := by
  induction h with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i, by simp⟩
  | succ k x y hx hy ih =>
    obtain ⟨u, hu, hs⟩ := ih
    refine ⟨Fin.cons x u, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using hu j
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hs]

/-- Absorb the trailing scalar of a simple tensor into the last vector. -/
lemma simple_coordinates {d e f : ℕ} {T : Holor ℂ [d,e,f]} (h : Holor.CPRankMax1 T) :
    ∃ (a : Fin d → ℂ) (b : Fin e → ℂ) (c : Fin f → ℂ),
      ∀ i j k, T ((indexEquiv d e f).symm (i,j,k)) = a i * b j * c k := by
  cases h with
  | cons a yz hyz =>
    cases hyz with
    | cons b zs hzs =>
      cases hzs with
      | cons c z hz =>
        refine ⟨fun i => a ((vector_index_equiv d).symm i),
          fun j => b ((vector_index_equiv e).symm j),
          fun k => c ((vector_index_equiv f).symm k) * z ⟨[], .nil⟩, ?_⟩
        intro i j k
        change a _ * (b _ * (c _ * z _)) = a _ * b _ * (c _ * z _)
        rw [mul_assoc]
        rfl

abbrev Raw (d e f r : ℕ) := Fin r × (Fin (d+1) ⊕ (Fin (e+1) ⊕ Fin f))
abbrev Chart (d e f r : ℕ) := Fin r × (Fin d ⊕ (Fin e ⊕ Fin f))

noncomputable def rawCoordinate (d e f r : ℕ) (q : HolorIndex [d+1,e+1,f]) :
    MvPolynomial (Raw d e f r) ℂ :=
  let v := indexEquiv (d+1) (e+1) f q
  ∑ t : Fin r, MvPolynomial.X (t, Sum.inl v.1) * MvPolynomial.X (t, Sum.inr (Sum.inl v.2.1)) *
    MvPolynomial.X (t, Sum.inr (Sum.inr v.2.2))

noncomputable def chartCoordinate (d e f r : ℕ) (q : HolorIndex [d+1,e+1,f]) :
    MvPolynomial (Chart d e f r) ℂ :=
  let v := indexEquiv (d+1) (e+1) f q
  ∑ t : Fin r, Fin.cases 1 (fun i => MvPolynomial.X (t, Sum.inl i)) v.1 *
    Fin.cases 1 (fun j => MvPolynomial.X (t, Sum.inr (Sum.inl j))) v.2.1 *
    MvPolynomial.X (t, Sum.inr (Sum.inr v.2.2))

/-- Normalize the first coordinates of the first two vectors of each term. -/
lemma normalize (d e f r : ℕ) (x : Raw d e f r → ℂ) (hx : ∀ i, x i ≠ 0) :
    ∃ y : Chart d e f r → ℂ, ∀ q,
      MvPolynomial.eval x (rawCoordinate d e f r q) = MvPolynomial.eval y (chartCoordinate d e f r q) := by
  classical
  let y : Chart d e f r → ℂ := fun (t,s) => match s with
    | .inl i => x (t,.inl i.succ) / x (t,.inl 0)
    | .inr (.inl j) => x (t,.inr (.inl j.succ)) / x (t,.inr (.inl 0))
    | .inr (.inr k) => x (t,.inr (.inr k)) * x (t,.inl 0) * x (t,.inr (.inl 0))
  refine ⟨y,?_⟩
  intro q
  simp only [rawCoordinate,chartCoordinate,map_sum,map_mul,MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro t _
  have ha (i : Fin (d+1)) :
      MvPolynomial.eval y (Fin.cases 1 (fun i : Fin d => MvPolynomial.X (t,Sum.inl i)) i) =
        x (t,.inl i) / x (t,.inl 0) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hx]
    · simp [y]
  have hb (j : Fin (e+1)) :
      MvPolynomial.eval y (Fin.cases 1 (fun j : Fin e => MvPolynomial.X (t,Sum.inr (Sum.inl j))) j) =
        x (t,.inr (.inl j)) / x (t,.inr (.inl 0)) := by
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [hx]
    · simp [y]
  rw [ha,hb]
  dsimp only [y]
  field_simp [hx]

lemma representation (d e f r : ℕ) (T : Holor ℂ [d+1,e+1,f]) (hr : T.cprank ≤ r) :
    ∃ x : Raw d e f r → ℂ, ∀ q, MvPolynomial.eval x (rawCoordinate d e f r q) = T q := by
  classical
  obtain ⟨u,hu,hT⟩ := finite_sum_of_simple (decomposition_of_rank_bound T r hr)
  choose a b c habc using fun t => simple_coordinates (hu t)
  let x : Raw d e f r → ℂ := fun (t,s) => match s with
    | .inl i => a t i
    | .inr (.inl j) => b t j
    | .inr (.inr k) => c t k
  refine ⟨x,?_⟩
  intro q
  let v := indexEquiv (d+1) (e+1) f q
  have term (t : Fin r) : u t q = a t v.1 * b t v.2.1 * c t v.2.2 := by
    have ht := habc t v.1 v.2.1 v.2.2
    change u t ((indexEquiv (d+1) (e+1) f).symm v) = _ at ht
    simpa only [v,Equiv.symm_apply_apply] using ht
  have hcoord : (∑ t : Fin r, u t q) = T q := by
    have eqAt := Finset.sum_apply (M := fun _ : HolorIndex [d+1,e+1,f] => ℂ) q
      (Finset.univ : Finset (Fin r)) (fun t => fun v => u t v)
    exact eqAt.symm.trans (congrFun hT q)
  calc
    _ = ∑ t : Fin r, a t v.1 * b t v.2.1 * c t v.2.2 := by simp [rawCoordinate,v,x]
    _ = ∑ t : Fin r, u t q := Finset.sum_congr rfl fun t _ => (term t).symm
    _ = T q := hcoord

/-- Counting the free coordinates of the normalized chart bounds the rank for
every rectangular format. -/
theorem lower_of_count (a b c r : ℕ) (hcount : (a+b+c-2)*r < a*b*c) :
    interior (closure {T : Holor ℂ [a,b,c] | T.cprank ≤ r}) = ∅ := by
  classical
  obtain _|d := a
  · simp at hcount
  obtain _|e := b
  · simp at hcount
  let _ : Fintype (HolorIndex [d+1,e+1,c]) :=
    Fintype.ofEquiv _ (indexEquiv (d+1) (e+1) c).symm
  have hd : Fintype.card (Chart d e c r) < Fintype.card (HolorIndex [d+1,e+1,c]) := by
    rw [Fintype.card_congr (indexEquiv (d+1) (e+1) c)]
    simp only [Chart,Fintype.card_prod,Fintype.card_fin,Fintype.card_sum]
    have h : d.succ+e.succ+c-2 = d+(e+c) := by omega
    simpa only [h,Nat.mul_comm (d+(e+c)) r,Nat.mul_assoc,Nat.succ_eq_add_one] using hcount
  obtain ⟨P,hP,hzero⟩ := generic_chart_relation hd (chartCoordinate d e c r)
    (rawCoordinate d e c r) (normalize d e c r)
  let Z := {T : Holor ℂ [d+1,e+1,c] | MvPolynomial.eval T P = 0}
  have hclosed : IsClosed Z := isClosed_eq (MvPolynomial.continuous_eval P) continuous_const
  have hsub : {T : Holor ℂ [d+1,e+1,c] | T.cprank ≤ r} ⊆ Z := by
    intro T hT
    obtain ⟨x,hx⟩ := representation d e c r T hT
    have he : (fun j => MvPolynomial.eval x (rawCoordinate d e c r j)) = T := funext hx
    change MvPolynomial.eval T P = 0
    simpa only [he] using hzero x
  have hempty : interior Z = ∅ := interior_polynomial_zero_locus P hP
  apply Set.subset_empty_iff.mp
  simpa only [hempty] using interior_mono (closure_minimal hsub hclosed)

end Dimension

/-- A sum of at most two less than twice the side length occupies a nowhere
dense subset of the four-slice format. -/
theorem lower (m : ℕ) (hm : 3 ≤ m) :
    interior (closure {T : Holor ℂ [4,m,m] | T.cprank ≤ 2*m-2}) = ∅ := by
  apply Dimension.lower_of_count
  have hsum : 4+m+m-2=2*m+2 := by omega
  have hdiff : (2*m-2)+2=2*m := by omega
  rw [hsum]
  have he := congrArg (fun k => (2*m+2)*k) hdiff
  nlinarith

end FourSlice

namespace FourSlice.Dominance

open Set Filter
open FourSlice.Dimension (interior_polynomial_zero_locus eval_substitution index_cons_equiv)
open scoped Topology Classical

lemma vector_is_simple {n : ℕ} (v : Holor ℂ [n]) : Holor.CPRankMax1 v := by
  let oneScalar : Holor ℂ [] := fun _ => 1
  have he : Holor.mul v oneScalar = v := by
    funext t
    change v t.take * (1 : ℂ) = v t
    rw [mul_one]
    congr 1
    apply Subtype.ext
    exact List.take_of_length_le t.property.length_eq.le
  rw [← he]
  exact Holor.CPRankMax1.cons _ _ (.nil _)

lemma tensor_sum_rank {d e f r : ℕ} (a : Fin r → Holor ℂ [d])
    (b : Fin r → Holor ℂ [e]) (c : Fin r → Holor ℂ [f]) :
    Holor.CPRankMax r (∑ i, Holor.mul (a i) (Holor.mul (b i) (c i))) := by
  have hs (i : Fin r) : Holor.CPRankMax1 (Holor.mul (a i) (Holor.mul (b i) (c i))) :=
    .cons _ _ (.cons _ _ (vector_is_simple (c i)))
  simpa using Holor.cprankMax_sum (n := 1) Finset.univ
    (fun i => Holor.mul (a i) (Holor.mul (b i) (c i))) (fun i _ => Holor.cprankMax_1 (hs i))

/-- A constructible spectral image containing the generic point contains a
principal open neighborhood of it. -/
lemma open_in_spectral_image {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    (φ : A →+* B) (hinj : Function.Injective φ) (hfp : φ.FinitePresentation) :
    ∃ f : A, f ≠ 0 ∧ ∀ q : PrimeSpectrum A, f ∉ q.asIdeal →
      q ∈ Set.range (PrimeSpectrum.comap φ) := by
  classical
  let z : PrimeSpectrum A := ⟨⊥, inferInstance⟩
  let w : PrimeSpectrum B := ⟨⊥, inferInstance⟩
  have hg : PrimeSpectrum.comap φ w = z := by
    apply PrimeSpectrum.ext
    change Ideal.comap φ ⊥ = ⊥
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot φ).mp hinj
  obtain ⟨T, hT⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr
    (PrimeSpectrum.isConstructible_range_comap hfp)
  have hz : z ∈ T.toSet := by rw [hT]; exact ⟨w, hg⟩
  obtain ⟨C, hC, hzC⟩ := Set.mem_iUnion₂.mp hz
  change z ∈ PrimeSpectrum.zeroLocus (Set.range C.g) ∧
    z ∉ PrimeSpectrum.zeroLocus {C.f} at hzC
  have hg0 (i : Fin C.n) : C.g i = 0 := by
    have h := (PrimeSpectrum.mem_zeroLocus z _).mp hzC.1 (Set.mem_range_self i)
    exact (Ideal.mem_bot : C.g i ∈ (⊥ : Ideal A) ↔ _).mp h
  have hf0 : C.f ≠ 0 := by
    intro e
    apply hzC.2
    exact (PrimeSpectrum.mem_zeroLocus z _).mpr (Set.singleton_subset_iff.mpr (e ▸ z.asIdeal.zero_mem))
  refine ⟨C.f, hf0, ?_⟩
  intro q hq
  rw [← hT]
  apply Set.mem_iUnion₂.mpr
  refine ⟨C, hC, ?_⟩
  constructor
  · apply (PrimeSpectrum.mem_zeroLocus q _).mpr
    rintro _ ⟨i, rfl⟩
    rw [hg0 i]
    exact q.asIdeal.zero_mem
  · intro e
    exact hq ((PrimeSpectrum.mem_zeroLocus q _).mp e (Set.mem_singleton _))

/-- Hilbert's Nullstellensatz converts the principal open in the spectral image
to actual complex points in the image of the polynomial map. -/
lemma principal_open_in_image {I J : Type} [Finite I] [Finite J] (F : J → MvPolynomial I ℂ)
    (hinj : Function.Injective (MvPolynomial.aeval F : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ)) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧ ∀ y : J → ℂ, MvPolynomial.eval y P ≠ 0 →
      ∃ x : I → ℂ, ∀ j, MvPolynomial.eval x (F j) = y j := by
  classical
  let φ : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ := MvPolynomial.aeval F
  have hfp : φ.toRingHom.FinitePresentation := by
    apply RingHom.FinitePresentation.of_finiteType.mp
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (MvPolynomial J ℂ))
    have he : φ.toRingHom.comp (algebraMap ℂ (MvPolynomial J ℂ)) =
        algebraMap ℂ (MvPolynomial I ℂ) :=
      RingHom.ext (fun a => φ.commutes a)
    rw [he]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨P, hP, hU⟩ := open_in_spectral_image φ.toRingHom hinj hfp
  refine ⟨P, hP, ?_⟩
  intro y hy
  let m := MvPolynomial.pointToPoint (k := ℂ) y
  have hy' : P ∉ m.asIdeal := fun h => hy ((MvPolynomial.mem_vanishingIdeal_singleton_iff y P).mp h)
  obtain ⟨q, hq⟩ := hU m hy'
  obtain ⟨M, hM, hle⟩ := q.asIdeal.exists_le_maximal q.isPrime.ne_top
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hM
  refine ⟨x, ?_⟩
  intro j
  let v : MvPolynomial J ℂ := MvPolynomial.X j - MvPolynomial.C (y j)
  have hv : v ∈ m.asIdeal := by
    apply (MvPolynomial.mem_vanishingIdeal_singleton_iff y _).mpr
    simp [v]
  have hvq : φ v ∈ q.asIdeal := by
    change v ∈ (PrimeSpectrum.comap φ.toRingHom q).asIdeal
    rwa [hq]
  have hMx := hle hvq
  rw [hx] at hMx
  have he := (MvPolynomial.mem_vanishingIdeal_singleton_iff x _).mp hMx
  simpa [φ, v, MvPolynomial.aeval_eq_eval, sub_eq_zero] using he

lemma dense_image_interior_of_nonempty {I J : Type} [Finite I] [Finite J] (F : J → MvPolynomial I ℂ)
    (h : (interior (Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j)))).Nonempty) :
    Dense (interior (Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j)))) := by
  classical
  let image := Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j))
  have hinj : Function.Injective (MvPolynomial.aeval F : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ) := by
    apply algebraicIndependent_iff_injective_aeval.mp
    apply algebraicIndependent_iff.mpr
    intro Q hQ
    by_contra hne
    have hs : image ⊆ {y : J → ℂ | MvPolynomial.eval y Q = 0} := by
      rintro _ ⟨x, rfl⟩
      change MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) Q = 0
      rw [← eval_substitution F x Q, hQ, map_zero]
    obtain ⟨y, hy⟩ := h
    have bad := interior_mono hs hy
    rw [interior_polynomial_zero_locus Q hne] at bad
    exact bad
  obtain ⟨P, hP, hsurj⟩ := principal_open_in_image F hinj
  let Z := {y : J → ℂ | MvPolynomial.eval y P = 0}
  have ho : IsOpen Zᶜ := (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).isOpen_compl
  have hd : Dense Zᶜ := interior_eq_empty_iff_dense_compl.mp (interior_polynomial_zero_locus P hP)
  apply hd.mono
  apply interior_maximal _ ho
  intro y hy
  obtain ⟨x, hx⟩ := hsurj y hy
  exact ⟨x, funext hx⟩

/-- The derivative of each coordinate is the sum of its three factor variations. -/
lemma trilinear_image_has_interior {I J S : Type} [Fintype I] [Fintype J] [Fintype S]
    (a b c : S → J → I) (base : I → ℂ)
    (hspan : ∀ y : J → ℂ, ∃ z : I → ℂ, ∀ j,
      y j = ∑ t : S, (z (a t j) * (base (b t j) * base (c t j)) +
        base (a t j) * (z (b t j) * base (c t j)) +
        base (a t j) * (base (b t j) * z (c t j)))) :
    (interior (Set.range (fun x : I → ℂ => fun j : J =>
      ∑ t : S, x (a t j) * (x (b t j) * x (c t j))))).Nonempty := by
  classical
  let φ (x : I → ℂ) (j : J) := ∑ t : S, x (a t j) * (x (b t j) * x (c t j))
  let pr (i : I) : (I → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj i
  let D : (I → ℂ) →L[ℂ] (J → ℂ) := ContinuousLinearMap.pi fun j =>
    ∑ t : S, (base (a t j) • (base (b t j) • pr (c t j) + base (c t j) • pr (b t j)) +
      (base (b t j) * base (c t j)) • pr (a t j))
  have hder : HasStrictFDerivAt φ D base := by
    apply hasStrictFDerivAt_pi.mpr
    intro j
    apply HasStrictFDerivAt.fun_sum
    intro t _
    exact (pr (a t j)).hasStrictFDerivAt.fun_mul
      ((pr (b t j)).hasStrictFDerivAt.fun_mul (pr (c t j)).hasStrictFDerivAt)
  have hsurj : Function.Surjective D := by
    intro y
    obtain ⟨z, hz⟩ := hspan y
    refine ⟨z, funext fun j => ?_⟩
    rw [hz j]
    simp only [D, ContinuousLinearMap.pi_apply, _root_.sum_apply,
      _root_.add_apply, _root_.smul_apply, smul_eq_mul, pr,
      ContinuousLinearMap.proj_apply]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hN : Set.range φ ∈ 𝓝 (φ base) := by
    rw [← hder.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hsurj)]
    exact Filter.range_mem_map
  exact ⟨φ base, mem_interior_iff_mem_nhds.mpr hN⟩

def index_nil_equiv : HolorIndex [] ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], .nil⟩
  left_inv := by rintro ⟨l, h⟩; cases h; rfl
  right_inv := by intro x; cases x; rfl

lemma finite_index (ds : List ℕ) : Finite (HolorIndex ds) := by
  induction ds with
  | nil => exact Finite.of_equiv Unit index_nil_equiv.symm
  | cons n ds ih =>
    let _ : Finite (HolorIndex ds) := ih
    exact Finite.of_equiv (Fin n × HolorIndex ds) (index_cons_equiv n ds).symm

lemma eval_holor_sum {ds : List ℕ} {r : ℕ} (u : Fin r → Holor ℂ ds) (j : HolorIndex ds) :
    (∑ i, u i) j = ∑ i, u i j :=
  Finset.sum_apply (M := fun _ : HolorIndex ds => ℂ) j Finset.univ (fun i x => u i x)

def point {d e f : ℕ} (i : Fin d) (j : Fin e) (k : Fin f) : HolorIndex [d,e,f] :=
  ⟨[i.val,j.val,k.val], .cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩

lemma point_surjective {d e f : ℕ} (z : HolorIndex [d,e,f]) :
    ∃ i j k, z = point i j k := by
  obtain ⟨⟨i,z⟩,rfl⟩ := (index_cons_equiv d [e,f]).symm.surjective z
  obtain ⟨⟨j,z⟩,rfl⟩ := (index_cons_equiv e [f]).symm.surjective z
  obtain ⟨⟨k,z⟩,rfl⟩ := (index_cons_equiv f []).symm.surjective z
  obtain ⟨⟨⟩,rfl⟩ := index_nil_equiv.symm.surjective z
  exact ⟨i,j,k,rfl⟩

abbrev Coordinate (d e f : ℕ) := HolorIndex [d,e,f]
abbrev Parameter (d e f r : ℕ) := Fin r × (Fin d ⊕ (Fin e ⊕ Fin f))

def entry {n : ℕ} (i : HolorIndex [n]) : Fin n := (index_cons_equiv n [] i).1

def first {d e f r : ℕ} (t : Fin r) (z : Coordinate d e f) : Parameter d e f r :=
  (t, Sum.inl (entry (HolorIndex.take (ds₁ := [d]) (ds₂ := [e,f]) z)))

def second {d e f r : ℕ} (t : Fin r) (z : Coordinate d e f) : Parameter d e f r :=
  (t, Sum.inr (.inl (entry (HolorIndex.take (ds₁ := [e]) (ds₂ := [f])
    (HolorIndex.drop (ds₁ := [d]) (ds₂ := [e,f]) z)))))

def third {d e f r : ℕ} (t : Fin r) (z : Coordinate d e f) : Parameter d e f r :=
  (t, Sum.inr (.inr (entry (HolorIndex.drop (ds₁ := [e]) (ds₂ := [f])
    (HolorIndex.drop (ds₁ := [d]) (ds₂ := [e,f]) z)))))

def pack {d e f r : ℕ} (a : Fin r → Fin d → ℂ) (b : Fin r → Fin e → ℂ)
    (c : Fin r → Fin f → ℂ) (q : Parameter d e f r) : ℂ :=
  q.2.elim (a q.1) (Sum.elim (b q.1) (c q.1))

/-- The tangent map of the sum of r simple tensors is onto at one choice
of the factors. The three factor dimensions are independent. -/
def TangentSpans (d e f r : ℕ) : Prop :=
  ∃ a : Fin r → Fin d → ℂ, ∃ b : Fin r → Fin e → ℂ, ∃ c : Fin r → Fin f → ℂ,
    ∀ T : Fin d → Fin e → Fin f → ℂ, ∃ u : Fin r → Fin d → ℂ, ∃ v : Fin r → Fin e → ℂ,
      ∃ w : Fin r → Fin f → ℂ, ∀ i j k, T i j k = ∑ t, (u t i * (b t j * c t k) +
        a t i * (v t j * c t k) + a t i * (b t j * w t k))

open Arxiv.«0805.3777» in
/-- A spanning tangent configuration gives a dense open set of tensors
of CP rank at most r in a rectangular complex tensor space. -/
theorem upper_of_spans {d e f r : ℕ} (hs : TangentSpans d e f r) :
    ∃ U : Set (Holor ℂ [d,e,f]), IsOpen U ∧ Dense U ∧ ∀ T ∈ U, T.cprank ≤ r := by
  classical
  obtain ⟨a,b,c,hspan⟩ := hs
  let _ : Finite (Coordinate d e f) := finite_index _
  let _ : Fintype (Coordinate d e f) := Fintype.ofFinite _
  let φ (x : Parameter d e f r → ℂ) (j : Coordinate d e f) :=
    ∑ t : Fin r, x (first t j) * (x (second t j) * x (third t j))
  have hopen : (interior (Set.range φ)).Nonempty := by
    apply trilinear_image_has_interior first second third (pack a b c)
    intro y
    obtain ⟨u,v,w,h⟩ := hspan fun i j k => y (point i j k)
    refine ⟨pack u v w, ?_⟩
    intro z
    obtain ⟨i,j,k,rfl⟩ := point_surjective z
    exact h i j k
  let F (j : Coordinate d e f) : MvPolynomial (Parameter d e f r) ℂ :=
    ∑ t : Fin r, MvPolynomial.X (first t j) *
      (MvPolynomial.X (second t j) * MvPolynomial.X (third t j))
  have he : (fun x : Parameter d e f r → ℂ => fun j => MvPolynomial.eval x (F j)) = φ := by
    funext x j
    simp [F, φ]
  have hd := dense_image_interior_of_nonempty F (by rw [he]; exact hopen)
  rw [he] at hd
  refine ⟨interior (Set.range φ), isOpen_interior, hd, ?_⟩
  intro T hT
  obtain ⟨x,rfl⟩ := interior_subset hT
  let xa (t : Fin r) (i : HolorIndex [d]) := x (t, Sum.inl (entry i))
  let xb (t : Fin r) (j : HolorIndex [e]) := x (t, Sum.inr (.inl (entry j)))
  let xc (t : Fin r) (k : HolorIndex [f]) := x (t, Sum.inr (.inr (entry k)))
  have hx : (φ x : Holor ℂ [d,e,f]) = ∑ t, Holor.mul (xa t) (Holor.mul (xb t) (xc t)) := by
    funext j
    rw [eval_holor_sum]
    rfl
  rw [hx]
  exact Nat.find_min' _ (tensor_sum_rank xa xb xc)

end FourSlice.Dominance

namespace FourSlice

open Arxiv.«0805.3777» in
theorem upper (m : ℕ) (hs : Spans m) : ∃ U : Set (Holor ℂ [4,m,m]),
    IsOpen U ∧ Dense U ∧ ∀ T ∈ U, T.cprank ≤ 2*m-1 :=
  Dominance.upper_of_spans hs

end FourSlice

namespace FourSlice
open Arxiv.«0805.3777» Set
open scoped Topology

lemma ceiling (m : ℕ) (hm : 3 ≤ m) : 4*m^2 ⌈/⌉ (2*m+2) = 2*m-1 := by
  have hd : 0 < 2*m+2 := by omega
  have hprev : 2*m-2+2=2*m := by omega
  have num : 4*m^2=(2*m+2)*(2*m-2)+4 := by
    nlinarith [congrArg (fun x : ℕ => (2*m+2)*x) hprev]
  apply Nat.le_antisymm
  · apply (ceilDiv_le_iff_le_mul hd).mpr
    rw [num,show 2*m-1=2*m-2+1 by omega,Nat.mul_succ]
    omega
  · by_contra! h
    have hsmall : 4*m^2 ⌈/⌉ (2*m+2) ≤ 2*m-2 := by omega
    have hh := (ceilDiv_le_iff_le_mul hd).mp hsmall
    omega

end FourSlice

open Arxiv.«0805.3777» Set FourSlice in
theorem OMA.solution : type_of% @Arxiv.«0805.3777».isGenericRank_four := by
  intro m hm
  rw [ceiling m hm]
  obtain ⟨U,hu,hd,upperBound⟩ := upper m (spans_of_blocks m hm base_witness border_witness)
  let K := closure {T : Holor ℂ [4,m,m] | T.cprank ≤ 2*m-2}
  have hd' : Dense Kᶜ := interior_eq_empty_iff_dense_compl.mp (lower m hm)
  refine ⟨U ∩ Kᶜ,hu.inter isClosed_closure.isOpen_compl,hd.inter_of_isOpen_left hd' hu,?_⟩
  intro T ht
  have hi := upperBound T ht.1
  have lo : ¬ T.cprank ≤ 2*m-2 := fun h => ht.2 (subset_closure h)
  change T.cprank = 2*m-1
  omega
