import OMAReductions.R_Arxiv_0805_3777_isGenericRank_cube_R1_H3_R1_H3_R1



/-! Exterior spanning for the (n-1,n-1,n-2) format over the complex numbers.

Write n = d + 1 + 9m with d equal to 9, 12 or 15. In each factor, the
distinguished group has interior dimensions (d,d,d-1), and each of the
other m groups has nine interior coordinates. Place d extra points in the
distinguished group and eight in each other group. A cyclic assignment,
starting with triples of groups (i,j,i+j), supplies exactly (n-1)^2/3 inner
points. The coordinate equations split into sectors indexed by the groups
that occur in their interior positions.

First cover the rows belonging to two distinct groups. The diagonal sectors
then correct the rows belonging to one group. The distinguished sector
also covers the all-outer corner. The resulting block lower triangular
matrix is surjective as soon as its diagonal blocks are surjective.
A product of determinant polynomials puts the separately checked blocks
at one complex specialization. Certificates over the fields of two and
seven elements verify the finite matrices; lifting determinants transfers
their ranks to the complex numbers. The final equivalences restore the
three original coordinate ranges and the prescribed order of the points.

For the underlying geometric estimate see Thomas Lickteig, Typical
tensorial rank (1985), Lemma 4.7 and Theorem 4.4.
[Article](https://doi.org/10.1016/0024-3795(85)90070-9).
-/



namespace TensorRankColumnReduction

abbrev Packed := ℕ × ℕ × ℕ
def zero : Packed := (0,0,0)
def component (b : Bool) : ℕ := if b then 1 else 0
def atNat (x : Packed) (i : ℕ) : ℕ :=
  component (x.1.testBit i) + 2*component (x.2.1.testBit i) + 4*component (x.2.2.testBit i)
def entry (x : Packed) (i : ℕ) : ZMod 7 := (atNat x i : ZMod 7)
def vector (m : ℕ) (x : Packed) (i : Fin m) : ZMod 7 := entry x i.val

/-- Normalize the two bit encodings of zero in arithmetic modulo seven. -/
def clean (x : Packed) : Packed :=
  let mask := x.1 &&& x.2.1 &&& x.2.2
  (x.1 ^^^ mask,x.2.1 ^^^ mask,x.2.2 ^^^ mask)

def plus (x y : Packed) : Packed :=
  let s₀ := x.1 ^^^ y.1
  let c₀ := x.1 &&& y.1
  let t₁ := x.2.1 ^^^ y.2.1
  let s₁ := t₁ ^^^ c₀
  let c₁ := (x.2.1 &&& y.2.1) ||| (t₁ &&& c₀)
  let t₂ := x.2.2 ^^^ y.2.2
  let s₂ := t₂ ^^^ c₁
  let c₂ := (x.2.2 &&& y.2.2) ||| (t₂ &&& c₁)
  let d₁ := s₀ &&& c₂
  clean (s₀ ^^^ c₂,s₁ ^^^ d₁,s₂ ^^^ (s₁ &&& d₁))

def twice (x : Packed) : Packed := (x.2.2,x.1,x.2.1)
def neg (x : Packed) : Packed :=
  let mask := x.1 ||| x.2.1 ||| x.2.2
  (x.1 ^^^ mask,x.2.1 ^^^ mask,x.2.2 ^^^ mask)

lemma entry_clean (x : Packed) (i : ℕ) : entry (clean x) i = entry x i := by
  rcases x with ⟨a,b,c⟩
  simp only [entry,atNat,clean,Nat.testBit_xor,Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> decide

set_option maxHeartbeats 600000 in
lemma entry_plus (x y : Packed) (i : ℕ) : entry (plus x y) i = entry x i+entry y i := by
  rcases x with ⟨a,b,c⟩
  rcases y with ⟨d,e,f⟩
  unfold plus
  rw [entry_clean]
  simp only [entry,atNat,Nat.testBit_xor,Nat.testBit_and,Nat.testBit_or]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;>
    cases d.testBit i <;> cases e.testBit i <;> cases f.testBit i <;> decide

lemma entry_twice (x : Packed) (i : ℕ) : entry (twice x) i = 2*entry x i := by
  rcases x with ⟨a,b,c⟩
  simp only [entry,atNat,twice]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> decide

lemma entry_neg (x : Packed) (i : ℕ) : entry (neg x) i = -entry x i := by
  rcases x with ⟨a,b,c⟩
  simp only [entry,atNat,neg,Nat.testBit_or,Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> decide

def scale (a : ℕ) (x : Packed) : Packed :=
  match a%7 with
  | 0 => zero
  | 1 => x
  | 2 => twice x
  | 3 => neg (twice (twice x))
  | 4 => twice (twice x)
  | 5 => neg (twice x)
  | _ => neg x

lemma zero_entry (i : ℕ) : entry zero i = 0 := by simp [entry,zero,atNat,component]

end TensorRankColumnReduction

namespace TensorRankThreeFactor

open TensorRankColumnReduction

def prodFin {A B : Type} {a b : ℕ} (ea : A ≃ Fin a) (eb : B ≃ Fin b) : A×B ≃ Fin (a*b) :=
  (ea.prodCongr eb).trans finProdFinEquiv
def sumFin {A B : Type} {a b : ℕ} (ea : A ≃ Fin a) (eb : B ≃ Fin b) : A⊕B ≃ Fin (a+b) :=
  (Equiv.sumCongr ea eb).trans finSumFinEquiv

abbrev Side (D : Type) := Fin 1 ⊕ D
abbrev Depth (E : Type) := Fin 2 ⊕ E
abbrev BaseRows (D E : Type) := (Fin 1 × Side D × Depth E) ⊕
  ((D × Fin 1 × Depth E) ⊕ (D × D × Fin 2))
abbrev BaseCols (D E X N : Type) :=
  (X × (Side D ⊕ (Side D ⊕ Depth E))) ⊕ (N × (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)))

def baseRows (d e : ℕ) : BaseRows (Fin d) (Fin e) ≃ Fin (1*((1+d)*(2+e))+(d*(1*(2+e))+d*(d*2))) :=
  sumFin (prodFin (Equiv.refl _) (prodFin finSumFinEquiv finSumFinEquiv))
    (sumFin (prodFin (Equiv.refl _) (prodFin (Equiv.refl _) finSumFinEquiv))
      (prodFin (Equiv.refl _) (prodFin (Equiv.refl _) (Equiv.refl _))))

def baseCols (d e x n : ℕ) : BaseCols (Fin d) (Fin e) (Fin x) (Fin n) ≃
    Fin (x*((1+d)+((1+d)+(2+e)))+n*(1+(1+2))) :=
  sumFin (prodFin (Equiv.refl _) (sumFin finSumFinEquiv (sumFin finSumFinEquiv finSumFinEquiv)))
    (prodFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (Equiv.refl _))))

def xyz {D E : Type} : BaseRows D E → Side D × Side D × Depth E
  | Sum.inl (i,j,k) => (Sum.inl i,j,k)
  | Sum.inr (Sum.inl (i,j,k)) => (Sum.inr i,Sum.inl j,k)
  | Sum.inr (Sum.inr (i,j,k)) => (Sum.inr i,Sum.inr j,Sum.inl k)

def baseMatrix {D E X N K : Type} [DecidableEq D] [DecidableEq E] [CommSemiring K]
    (a b : X → Side D → K) (c : X → Depth E → K) (ai bi : N → D → K) (ci : N → E → K) :
    Matrix (BaseRows D E) (BaseCols D E X N) K := fun row col =>
  let (i,j,k) := xyz row
  match col with
  | Sum.inl (t,Sum.inl h) => if h=i then b t j * c t k else 0
  | Sum.inl (t,Sum.inr (Sum.inl h)) => if h=j then a t i * c t k else 0
  | Sum.inl (t,Sum.inr (Sum.inr h)) => if h=k then a t i * b t j else 0
  | Sum.inr (t,Sum.inl h) =>
      if Sum.inl h=i then j.elim (fun _ => 0) (bi t) * k.elim (fun _ => 0) (ci t) else 0
  | Sum.inr (t,Sum.inr (Sum.inl h)) =>
      if Sum.inl h=j then i.elim (fun _ => 0) (ai t) * k.elim (fun _ => 0) (ci t) else 0
  | Sum.inr (t,Sum.inr (Sum.inr h)) =>
      if Sum.inl h=k then i.elim (fun _ => 0) (ai t) * j.elim (fun _ => 0) (bi t) else 0

lemma base_cast {D E X N : Type} [DecidableEq D] [DecidableEq E]
    (a b : X → Side D → ℕ) (c : X → Depth E → ℕ) (ai bi : N → D → ℕ) (ci : N → E → ℕ) :
    (baseMatrix a b c ai bi ci).map (Nat.castRingHom ℂ) =
      baseMatrix (fun t i => (a t i : ℂ)) (fun t i => (b t i : ℂ)) (fun t i => (c t i : ℂ))
        (fun t i => (ai t i : ℂ)) (fun t i => (bi t i : ℂ)) (fun t i => (ci t i : ℂ)) := by
  have ez {T U : Type} (g : U → ℕ) (i : T⊕U) :
      ((i.elim (fun _ => 0) g : ℕ) : ℂ) = i.elim (fun _ => 0) (fun i => (g i : ℂ)) := by
    cases i <;> simp
  have ec (P : Prop) [Decidable P] (u : ℕ) (v : ℂ) (hu : (u : ℂ)=v) :
      ((if P then u else 0 : ℕ) : ℂ) = (if P then v else 0) := by
    by_cases h : P <;> simp [h,hu]
  ext row col
  change ((baseMatrix a b c ai bi ci row col : ℕ) : ℂ) = _
  rcases col with ⟨t,h|h|h⟩|⟨t,h|h|h⟩ <;> rcases row with ⟨i,j,k⟩|⟨i,j,k⟩|⟨i,j,k⟩ <;>
    dsimp only [baseMatrix,xyz,Sum.elim_inl,Sum.elim_inr]
  all_goals apply ec
  all_goals rw [Nat.cast_mul]
  all_goals simp only [Nat.cast_zero,ez]

def Base (d e x n : ℕ) : Prop := ∃ a b : Fin x → Side (Fin d) → ℂ, ∃ c : Fin x → Depth (Fin e) → ℂ,
  ∃ ai bi : Fin n → Fin d → ℂ, ∃ ci : Fin n → Fin e → ℂ, Function.Surjective (baseMatrix a b c ai bi ci).mulVec

def fromTable {m n : ℕ} (a : Array ℕ) (i : Fin m) (j : Fin n) : ℕ :=
  (a[i.val]?.getD 0 >>> (4*j.val))%16

end TensorRankThreeFactor

namespace TensorRankThreeFactor.FastBase

structure System (p : ℕ) where
  W : Type
  zero : W
  axpy : ℕ → W → W → W
  eval : W → ℕ → ZMod p
  test : W → ℕ → Bool
  eval_zero (j : ℕ) : eval zero j = 0
  eval_axpy (a : ℕ) (w v : W) (j : ℕ) : eval (axpy a w v) j = a * eval w j + eval v j
  test_diag {w : W} {i : ℕ} : test w i = true → eval w i ≠ 0
  test_above {w : W} {i j : ℕ} : test w i = true → i < j → eval w j = 0

private lemma bit_off {w i j : ℕ} (h : w >>> (i+1) = 0) (hij : i<j) : w.testBit j = false := by
  have he := congrArg (fun v : ℕ => v.testBit (j-(i+1))) h
  simp only [Nat.testBit_shiftRight,Nat.zero_testBit] at he
  rwa [show i+1+(j-(i+1))=j by omega] at he

def bitVal (b : Bool) : ZMod 2 := if b then 1 else 0

def binary : System 2 where
  W := ℕ
  zero := 0
  axpy a w v := if a%2=0 then v else w ^^^ v
  eval w j := bitVal (w.testBit j)
  test w i := w.testBit i && (w >>> (i+1) == 0)
  eval_zero := by simp [bitVal]
  eval_axpy := by
    intro a w v j
    have ha := Nat.mod_two_eq_zero_or_one a
    rw [← ZMod.natCast_mod a 2]
    rcases ha with ha|ha <;> simp [ha,Nat.testBit_xor,bitVal]
    cases w.testBit j <;> cases v.testBit j <;> decide
  test_diag := by
    intro w i h
    have h' := (Bool.and_eq_true_iff.mp h).1
    simp [bitVal,h']
  test_above := by
    intro w i j h hij
    have h' := beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2
    simp [bit_off h' hij,bitVal]

open TensorRankColumnReduction

private lemma entry_scale (a : ℕ) (w : Packed) (j : ℕ) :
    entry (scale a w) j = (a : ZMod 7) * entry w j := by
  rw [← ZMod.natCast_mod a 7]
  have h := Nat.mod_lt a (by decide : 0<7)
  generalize hz : a%7=n at *
  interval_cases n <;> simp only [scale,hz,entry_neg,entry_twice,zero_entry]
  all_goals push_cast
  all_goals ring_nf
  · rw [← mul_neg,show -(4 : ZMod 7)=3 by decide]
  · rw [← mul_neg,show -(2 : ZMod 7)=5 by decide]
  · rw [show (6 : ZMod 7)= -1 by decide,mul_neg_one]

def seven : System 7 where
  W := Packed
  zero := TensorRankColumnReduction.zero
  axpy a w v := if a%7=0 then v else plus (scale a w) v
  eval := entry
  test w i := (atNat w i % 7 != 0) && ((w.1 ||| w.2.1 ||| w.2.2) >>> (i+1) == 0)
  eval_zero := zero_entry
  eval_axpy := by
    intro a w v j
    split
    · rename_i h
      rw [← ZMod.natCast_mod a 7,h]
      simp
    · rw [entry_plus,entry_scale]
  test_diag := by
    intro w i h he
    have h' := (Bool.and_eq_true_iff.mp h).1
    have hh := congrArg ZMod.val he
    simp [entry,ZMod.val_natCast] at hh
    simp [hh] at h'
  test_above := by
    intro w i j h hij
    have h' := beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2
    have hb := bit_off h' hij
    simp only [Nat.testBit_or,Bool.or_eq_false_iff] at hb
    simp [entry,atNat,component,hb.1.1,hb.1.2,hb.2]

def accumulate {W : Type} : (n : ℕ) → (Fin n → W → W) → W → W
  | 0, _, v => v
  | n+1, f, v => f (Fin.last n) (accumulate n (fun i => f i.castSucc) v)

lemma eval_accumulate {p : ℕ} (s : System p) (j : ℕ) {n : ℕ}
    (f : Fin n → s.W → s.W) (v : s.W) (g : Fin n → ZMod p)
    (hf : ∀ i z, s.eval (f i z) j = g i + s.eval z j) :
    s.eval (accumulate n f v) j = (∑ i, g i) + s.eval v j := by
  induction n with
  | zero => simp [accumulate]
  | succ n ih =>
    rw [accumulate,hf,ih (fun i => f i.castSucc) (fun i => g i.castSucc)
      (fun i => hf i.castSucc),Fin.sum_univ_castSucc]
    abel

/-- Decode consecutive 16-bit blocks. Zero and one- or two-bit blocks
are represented by flags and positions. Other blocks store all sixteen bits. -/
def unpack16 : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, v =>
    if v=0 then 0
    else if v%2=0 then (unpack16 n (v >>> 1)) <<< 16
    else if v%4=1 then (1 <<< ((v >>> 2)%16)) ||| ((unpack16 n (v >>> 6)) <<< 16)
    else if v%8=3 then (1 <<< ((v >>> 3)%16)) ||| (1 <<< ((v >>> 7)%16)) |||
      ((unpack16 n (v >>> 11)) <<< 16)
    else ((v >>> 3)%65536) ||| ((unpack16 n (v >>> 19)) <<< 16)

def window (f : ℕ → Bool) (start : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => window f start n && f (start+n)

def Before (f : ℕ → Bool) (b : ℕ) := ∀ i < b, f i = true

lemma before_zero (f : ℕ → Bool) : Before f 0 := fun _ h => by omega

lemma extend {f : ℕ → Bool} {b n : ℕ} (earlier : Before f b) (h : window f b n = true) :
    Before f (b+n) := by
  induction n with
  | zero => simpa using earlier
  | succ n ih =>
    obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp h
    intro i hi
    by_cases h' : i < b+n
    · exact ih h₁ i h'
    · have he : i=b+n := by omega
      exact he ▸ h₂

structure RowWindow (f : ℕ → Bool) (n : ℕ) : Type where
  verified : Before f n

def start (f : ℕ → Bool) : RowWindow f 0 := ⟨before_zero f⟩

def nextWindow {f : ℕ → Bool} {b : ℕ} (prev : RowWindow f b) (n : ℕ)
    (h : window f b n = true) : RowWindow f (b+n) := ⟨extend prev.verified h⟩

section Rows
variable {d e x n p : ℕ} (s : System p)
variable (a b : Fin x → Side (Fin d) → ℕ) (c : Fin x → Depth (Fin e) → ℕ)
variable (ai bi : Fin n → Fin d → ℕ) (ci : Fin n → Fin e → ℕ)
def rowProduct (B : (BaseCols (Fin d) (Fin e) (Fin x) (Fin n)) → s.W) (r : (BaseRows (Fin d) (Fin e))) : s.W :=
  let u := xyz r
  let step := fun col acc => s.axpy (baseMatrix a b c ai bi ci r col) (B col) acc
  let extras := accumulate x (fun t z =>
    step (.inl (t,.inl u.1)) (step (.inl (t,.inr (.inl u.2.1))) (step (.inl (t,.inr (.inr u.2.2))) z))) s.zero
  accumulate n (fun t z => step (.inr (t,.inl 0)) (step (.inr (t,.inr (.inl 0)))
    (step (.inr (t,.inr (.inr 0))) (step (.inr (t,.inr (.inr 1))) z)))) extras

lemma rowProduct_eval (B : (BaseCols (Fin d) (Fin e) (Fin x) (Fin n)) → s.W) (r : (BaseRows (Fin d) (Fin e))) (q : ℕ) :
    s.eval (rowProduct s a b c ai bi ci B r) q =
      ∑ j : (BaseCols (Fin d) (Fin e) (Fin x) (Fin n)), ((baseMatrix a b c ai bi ci r j : ℕ) : ZMod p) * s.eval (B j) q := by
  let g : (BaseCols (Fin d) (Fin e) (Fin x) (Fin n)) → ZMod p := fun j => ((baseMatrix a b c ai bi ci r j : ℕ) : ZMod p) * s.eval (B j) q
  let u := xyz r
  let extra (t : Fin x) := g (.inl (t,.inl u.1)) + (g (.inl (t,.inr (.inl u.2.1))) + g (.inl (t,.inr (.inr u.2.2))))
  let inner (t : Fin n) := g (.inr (t,.inl 0)) + (g (.inr (t,.inr (.inl 0))) +
    (g (.inr (t,.inr (.inr 0))) + g (.inr (t,.inr (.inr 1)))))
  change _ = ∑ j, g j
  unfold rowProduct
  rw [eval_accumulate (g:=inner) (hf:=by intro t z; simp only [s.eval_axpy,g,inner,add_assoc])]
  rw [eval_accumulate (g:=extra) (hf:=by intro t z; simp only [s.eval_axpy,g,extra,u,add_assoc])]
  rw [s.eval_zero,add_zero,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_prod_type]
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    obtain ⟨i,j,k,hu⟩ : ∃ i j k, xyz r = (i,j,k) := ⟨_,_,_,rfl⟩
    simp [extra,g,u,baseMatrix,hu,Fintype.sum_sum_type,apply_ite,ite_mul]
  · apply Finset.sum_congr rfl
    intro t _
    simp only [inner,Fintype.sum_sum_type,Fin.sum_univ_one,Fin.sum_univ_two]
end Rows

private lemma lift_mod {p : ℕ} [Fact p.Prime] {I K : Type} [Fintype I] [DecidableEq I] [Fintype K]
    (A : Matrix I K ℤ) (hs : Function.Surjective (A.map (Int.castRingHom (ZMod p))).mulVec) :
    Function.Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  obtain ⟨b,hb⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hs
  let B : Matrix K I ℤ := fun k i => (b k i).val
  have hB : B.map (Int.castRingHom (ZMod p)) = b := by
    ext i j
    change (((b i j).val : ℤ) : ZMod p) = b i j
    simp
  let D := A*B
  have hp : ((D.det : ℤ) : ZMod p) = 1 := by
    change (Int.castRingHom (ZMod p)) D.det = 1
    rw [RingHom.map_det,RingHom.mapMatrix_apply,show D=A*B from rfl,Matrix.map_mul,hB,hb,Matrix.det_one]
  have hn : D.det ≠ 0 := by
    intro he
    rw [he,Int.cast_zero] at hp
    exact zero_ne_one hp
  have hu : IsUnit (D.map (Int.castRingHom ℂ)).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [← RingHom.mapMatrix_apply,← RingHom.map_det]
    change (D.det : ℂ) ≠ 0
    exact_mod_cast hn
  have hs' : Function.Surjective (D.map (Int.castRingHom ℂ)).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
  intro y
  obtain ⟨z,hz⟩ := hs' y
  refine ⟨(B.map (Int.castRingHom ℂ)).mulVec z,?_⟩
  rw [Matrix.mulVec_mulVec,← Matrix.map_mul]
  exact hz

lemma certified {d e x n m p : ℕ} [Fact p.Prime] (s : System p)
    (rows : BaseRows (Fin d) (Fin e) ≃ Fin m)
    (a b : Fin x → Side (Fin d) → ℕ) (c : Fin x → Depth (Fin e) → ℕ)
    (ai bi : Fin n → Fin d → ℕ) (ci : Fin n → Fin e → ℕ)
    (B : BaseCols (Fin d) (Fin e) (Fin x) (Fin n) → s.W)
    (h : ∀ i : Fin m, s.test (rowProduct s a b c ai bi ci B (rows.symm i)) i.val = true) :
    Base d e x n := by
  let A := baseMatrix a b c ai bi ci
  let K := BaseCols (Fin d) (Fin e) (Fin x) (Fin n)
  let M : Matrix (Fin m) K ℤ := fun i j => A (rows.symm i) j
  let N := M.map (Int.castRingHom (ZMod p))
  let T : Matrix K (Fin m) (ZMod p) := fun j i => s.eval (B j) i.val
  let L := N*T
  have hL (i j : Fin m) : L i j = s.eval (rowProduct s a b c ai bi ci B (rows.symm i)) j.val := by
    rw [rowProduct_eval]
    change (∑ k, (((A (rows.symm i) k : ℕ) : ℤ) : ZMod p) * _) = _
    simp only [Int.cast_natCast,A,T]
  have ht : L.IsLowerTriangular := fun i j hij => (hL i j).trans (s.test_above (h i) hij)
  have hd : L.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular L ht]
    exact Finset.prod_ne_zero_iff.mpr fun i _ hzero => s.test_diag (h i) ((hL i i).symm.trans hzero)
  have hl : Function.Surjective L.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  have hn : Function.Surjective N.mulVec := by
    intro y
    obtain ⟨z,hz⟩ := hl y
    exact ⟨T.mulVec z,(Matrix.mulVec_mulVec _ _ _).trans hz⟩
  have hs := lift_mod M hn
  refine ⟨fun t i => a t i,fun t i => b t i,fun t i => c t i,fun t i => ai t i,fun t i => bi t i,fun t i => ci t i,?_⟩
  rw [← base_cast]
  intro y
  obtain ⟨u,hu⟩ := hs fun i => y (rows.symm i)
  refine ⟨u,?_⟩
  funext i
  have h' := congrFun hu (rows i)
  change (∑ j, ((M (rows i) j : ℤ) : ℂ)*u j) = y (rows.symm (rows i)) at h'
  change (∑ j, (A i j : ℂ)*u j) = y i
  simpa only [M,Int.cast_natCast,Equiv.symm_apply_apply] using h'

end TensorRankThreeFactor.FastBase

namespace TensorRankThreeFactor.Base10

open TensorRankThreeFactor.FastBase

def a (t : Fin 9) (i : Side (Fin 9)) : ℕ := fromTable #[0x11, 0x101, 0x1001, 0x10001, 0x100001, 0x1000001, 0x10000001, 0x100000001, 0x1000000001] t (finSumFinEquiv i)
def b (t : Fin 9) (i : Side (Fin 9)) : ℕ := fromTable #[0x11, 0x101, 0x1001, 0x10001, 0x100001, 0x1000001, 0x10000001, 0x100000001, 0x1000000001] t (finSumFinEquiv i)
def c (t : Fin 9) (i : Depth (Fin 8)) : ℕ := fromTable #[0x101, 0x1011, 0x10021, 0x100031, 0x1000041, 0x10000051, 0x100000061, 0x1000000010, 0x4224333401] t (finSumFinEquiv i)
def ai : Fin 27 → Fin 9 → ℕ := fromTable #[0x15430506, 0x30306035, 0x606500, 0x560500030, 0x223022005, 0x60340000, 0x1004000, 0x5220220, 0x3052005, 0x600003306, 0x60504160, 0x5550002, 0x300005103, 0x401050004, 0x300440040, 0x203005500, 0x5030000, 0x30011040, 0x4001055, 0x300013000, 0x100000343, 0x530500, 0x40000213, 0x324304323, 0x300042, 0x500602050, 0x66005050]
def bi : Fin 27 → Fin 9 → ℕ := fromTable #[0x4300650, 0x400500500, 0x150065050, 0x400310, 0x1000000, 0x10031001, 0x105601061, 0x401022, 0x240130001, 0x544000200, 0x533004, 0x2403050, 0x3000102, 0x220402000, 0x435100404, 0x502600040, 0x601500040, 0x305164, 0x10500140, 0x20260340, 0x6105060, 0x100300000, 0x50002003, 0x3500, 0x4413502, 0x601500100, 0x1100000]
def ci : Fin 27 → Fin 8 → ℕ := fromTable #[0x65000020, 0x1600040, 0x162000, 0x306004, 0x23226000, 0x30400004, 0x50440522, 0x20, 0x50600014, 0x322505, 0x4405, 0x30023005, 0x60155, 0x62505000, 0x6551, 0x54550000, 0x420004, 0x62200420, 0x2401244, 0x60060003, 0x44060003, 0x5600100, 0x30040606, 0x63456056, 0x600300, 0x20526, 0x31040265]

private def unpack := unpack16 22


private def t0 : Array TensorRankColumnReduction.Packed := #[
  (unpack 0xeb19cc9a3c20e78300e4901c30839a00c801, unpack 0xa0175041e185bf7807db407db6244505f90440, unpack 0x185dff08079c11f0d02fa081cd0839a488a0bf21a8c0),
  (0, 0, 0),
  (unpack 0x6921f0795c107783b8c704386a1de40, unpack 0x5a39c4373aa32300f3f01ed020c1c180, unpack 0xb7fe008f1c0cf1e05c8d03d23011060080),
  (unpack 0xa20ef8135f55ff01fc040e3841cd01080, unpack 0x27557e04af3c0bf5801f9803ed334d121480, unpack 0xe18380a2fdc13e0607cf203dab193121480),
  (unpack 0xacbf831cf5813d1807b3e071810e02d360602700, unpack 0x8e11f8ccc0d3cc380c0e884529100, unpack 0x1dd67611aeb041fa00ff63cb6113650608700),
  (unpack 0x2764ba04f7bc3ee08d00706a47100, unpack 0x2112f01ebea021f7c0fbba8767a6c000ffd00, unpack 0x2bbfe6649fadf5817ec76ac3b334006ffd00),
  (unpack 0x32cce470fd40979100fa040e4841c0c040e00, unpack 0x443df20a7c600bff3f663841c0661eae8600, unpack 0x6359fb268f0879cac07af0072810e0330cf8600),
  (unpack 0xb993d08178028e9201ea303dd31a082aafd3700c00, unpack 0x3602fa114f681fe8407e6903e23120b1417ed60609c00, unpack 0x25a9e228de9087dc37100fb4c11417e3724c00),
  (unpack 0x76c3e838dd908bda0073640e18e93a400, unpack 0x8abfe88f3f60ff5301eaf01e914993c400, unpack 0xa93a0cd79811fd407fddd2694e9bc400),
  (unpack 0x15517f0c2f881571a03eaa81c688505cc043800, unpack 0x2a787301ee403fed007f06070c719800, unpack 0xde7de48c3b81afa302e6501e934ec6c800),
  (0, 0, 0),
  (unpack 0xda07804be284bf500ff9207dc6244505f90029, (0xca7a65438001460081802840001 <<< 243), (0xd9e04089d850a4020d001 <<< 267)),
  (unpack 0xd40fe0b839813f0711c10e00022, unpack 0x9ec7b863f1810f09f807b4083000, unpack 0xb0e5fc0af820f78f02e0781e9180883000),
  (unpack 0x82ce0039c402bfb01fc040e3841cd00072, unpack 0x1e02ff47d3ac03fda7cc01f699a689000, unpack 0x11603e4083b612f8903e7901ed58c989000),
  (unpack 0xb202e80a1fb01ff701f4740e3021c040084, unpack 0x8443d4cd3b80178902eca211000, unpack 0x4997a00ef2801f81b8407cb611000),
  (unpack 0x19721d0e8be60e70803e3401c00048, unpack 0x13133881d7536ae07f5d43b3000, unpack 0xa6a5f20a1d805ba5807d080f6ac3b3000)]

private def t1 : Array TensorRankColumnReduction.Packed := #[
  (unpack 0x28e7f37cec00fe800fc06072420e00188, unpack 0x1d9c1d8297f2197c002f0181c708380cc3000, unpack 0xa577e4607821270b01ebc01ca04380cc3000),
  (unpack 0x6f2df1344f3861d8403c4207ba63410555e0190, unpack 0x1484700dce5813f080f8d607c462416282fc800, unpack 0x1cd21c066ff017fd86a301f6982282fc800),
  (unpack 0xc83a82af7014e6c05cd9038620020, unpack 0x18d0bf90374c19eb207fdc03d229000, unpack 0x1b0d381587880ff8003dda4d29000),
  (unpack 0x64d83c3ac0471203eea81c688505c06d20, unpack 0x7b1ff4029ee833e5807b02070c406e20, unpack 0x13da5cc44ff832900f2401e934ec60620),
  (unpack 0x3887780517c83cf22d6ac01a8c0, unpack 0x4c28762f9eac8bf7504505c1acc0, unpack 0xbc87cc567aa0e7db7faca08382282e0640),
  (unpack 0x7073e6721db02b8a5101ca08388028e0005, unpack 0xf904ea00bf0053dab47be800, unpack 0x6e374137f6065e5a080ea8d2be800),
  (unpack 0x3d047e19577810f2ebb00351809, unpack 0x29b1380b27fb7e2f500359831, unpack 0x40e4303aa1b7aa00ee800c831),
  (unpack 0x26c9e0bebda18797d0009d40d, unpack 0x2c00e4145fc5950072880e0280dd435, unpack 0x2d257e02471426f1005dd01406835),
  (unpack 0x1482fc444f84197db72aa00011, unpack 0x468679285e2839fedbbb6c680039, unpack 0x20fe15b7100ae2dcb54680039),
  (unpack 0x723bd8227f5b000015, unpack 0x7189c8983c804700003d, unpack 0x18e35f49dbf40c700003d),
  (unpack 0xc29be45c7d706bfb5501c00019, unpack 0x2a91c0ebf9a4405f5d43a0002, unpack 0x644bc08478c36fb2d6ac3a0002),
  (unpack 0x4ac97c300e8059f45ebb2820e0001d, unpack 0x7a8de4067f3023c50179776ac4a000a, unpack 0xa629f8377c515007d44a000a),
  (unpack 0x53f1f8312f303de45d4007b4680021, unpack 0x2696f607c831e080bdcbb46a0012, unpack 0x73a16e77824f6d0407d46a0012),
  (unpack 0x6f2ff1201fc019c58880fa8822ae0025, unpack 0x18c65c87d38a087fb7a941071fafd001a, unpack 0xa3b78972f043afa2ea003dab04541fd001a),
  (0, 0, 0),
  (unpack 0x32307c9567140ae1405ea00380a0740, (0x12ae049da0a5 <<< 301), unpack 0x7bacea287d806bd1007b400d40)]

private def t2 : Array TensorRankColumnReduction.Packed := #[
  (unpack 0xc990e4771f85e400f649083c201c180, unpack 0x1d28ba0327142cf6ee6073010f2bd6a003f380, unpack 0x1083fc4467e612fa101e1d01c7003cc37ad36001f380),
  (unpack 0x5804f0529ec033fb4101c01680, unpack 0x4777d91a20a7fb6e8350500, unpack 0x4a9b77020f5065f45feb069b0500),
  (unpack 0x18cd5f82179c137a167b81c90438c8d1500, unpack 0x9419ea225d2043f30074780f8ac75a800, unpack 0x90cde06cfd00bf0b00e7001c70438e8d2d00),
  (unpack 0x4838fa141ce077ce00fd96211b2bd00, unpack 0x1804fd013fa05dfe1f4b2820e4a000, unpack 0x2e31f80617a023e4405dc203dab251af5600),
  (unpack 0x3486bd9b17ec78c01e51038e0078410f9600, unpack 0x252fe037dc8073e80072180e8ca29a800, unpack 0x611fe4d20878b007f6794e618a69b7200),
  (unpack 0x9533d028f820b7c403e5081d5181c43400, unpack 0x1b4abd04ebb600fe873201cb00385d49400, unpack 0x10a778344ea07dc180bb32071430f30dab58400),
  (unpack 0x4817f81edf5073f5b0e4c400, unpack 0x9842f440bc705fcc300dd400, unpack 0xf264ec5c1e202bff3009d400),
  (unpack 0xca84fa1a9d706bfbf2d2834501ce800, unpack 0x1a3cf82c0f087dc5101f50aa281c5000, unpack 0x5c7cf2109fa041f5f76dca20d45038b8800),
  (unpack 0x9cf5fa315e7007dc37e00e3021e57a000, (0x6719c2a4682f610102800c2001 <<< 248), (0xd82c020ff4086a00d040203 <<< 260)),
  (unpack 0x69c7fc59bda093da5101c05000, (0x276e30d9ca0501 <<< 297), (0x12c7726f0804d14045 <<< 283)),
  (0, 0, 0),
  ((0x17 <<< 347), 0, (0xb <<< 348)),
  (unpack 0x5208f010be6021f698ea072410e32000, unpack 0xff4730e2e781dfb00bf3c07c563a000, unpack 0x28e6fe110e980be2c0b9c0071c10e3a000),
  (unpack 0x2f50e85cbd00cfce01f9442000, unpack 0x42d079249f0819ee1e10072820e4a000, unpack 0x19475e82abc80af38407b564a000),
  ((0xf0e62366d028ce0294401c0001000001 <<< 224), unpack 0x4308f10c3f8029fc003fc346514000, unpack 0x8691c42179411f3400eecf29cc314000),
  (unpack 0x4824f0ef69b200f2840ea8c0e2000, unpack 0x25b0ec4b7e706fa08171980e5801c2ea000, (0x6ca87048341f470133200a18018000001 <<< 221))]

private def t3 : Array TensorRankColumnReduction.Packed := #[
  (unpack 0x4967b152f9841fad872000, (0x900240f194298b <<< 296), (0x3d5b1053180c71 <<< 297)),
  (unpack 0x10737f9b977008ff6e5da5068a038064c0, unpack 0x3ba87b83f004f22ca203ea1545038a0340, unpack 0x2f0bbd0207082af62db6e5106a281c5000),
  (unpack 0x5657e8263a40971801fb081d2bc1883000, unpack 0x49a1e889b8a1478b03fd0c40c3c2206000, unpack 0x2893c0bc3920f7d202e6081cf0c3c2426000),
  (unpack 0xfc53e4151c40e7c3ac01cc043caf36000, (0x2062a312000b63030880242001 <<< 248), unpack 0x863cf2189e60dbe4017f0c0ea8e52a000),
  (unpack 0x1c17dc4a5782057d102fa001ce043c229031060031, unpack 0xa177c16af0831cf803b7c073800f28a002bc0032, unpack 0x8901c0d5fbc19f8201e3f01d1954501c0032),
  (unpack 0x61e0e050de80abd0bd6796e551487009d435, unpack 0x3666ea099d5047a501f3f40f94e15140700dd43a, unpack 0x550ce6031c607bed007dc80fa8e1150980683a),
  (unpack 0x1915bc84df8c12f0c05f59e5b954521c0039, unpack 0x601bc0b272009ed003efd03e53854501c0042, unpack 0x2ae473007e1851d480bee407d4708a84c0042),
  (unpack 0x3680fc0c375013e5401e4d039c087954421c003d, unpack 0x237cbe100f8028f8e03c460386107854501c004a, unpack 0x305af6366f3029e440bd54073400f08a84c004a),
  (unpack 0xb4270184eb01bdd00bb7c072c10f08b24c0002, unpack 0x22c1fb8b1ff030e2ee354728a0429c0052, unpack 0x1c1a7a976f8028e3201e07039e107954101c0052),
  (unpack 0x4063a1d17900cff2f0f03ee38484c000a, unpack 0x214a7c087fe00afa407e0303e5b954501c005a, unpack 0xa057b926f5427ed807da4039408784524005a),
  (unpack 0xc04be036dd15d03fc501c608384029c0012, unpack 0x3270fe824f2c04f5001f110501c0062, unpack 0x21a8fe641f40df9a80fa140f8ac240062),
  (unpack 0xa607b015f8849c480fefc070c10f08b4419c001a, unpack 0x581df2108f7875f740bf6b54728a4029c006a, unpack 0x2079380e0fe469c03e2d039a00795eac006a),
  (0, 0, 0),
  (unpack 0x17377c0cdf1045e080bdbb6c680c40, unpack 0x147278045f6408f72caa03aa00d40, unpack 0x575175042f603dea00bfebdb600d40),
  (unpack 0x129f5c09178e0c70a02e069b0480, unpack 0x8373e825bd0037a800faec1a800, unpack 0x15007e0123a00978202ee80d0e80),
  (unpack 0x7d53f6123ec0278081f8d80fb4c58a00e6a0b880, unpack 0x29097f85f78401e5807de003aa64d3608300, unpack 0x2641b92702ddbc03cae07a4d64000)]

private def t4 : Array TensorRankColumnReduction.Packed := #[
  (unpack 0xd5bf31d8e48e0078fc0fb4d081900, unpack 0x18009c080f98067e000e2381f15a50d9400, unpack 0xb6c9fe0fdcf0cb87007fc7b4d282d00),
  (unpack 0x2ab1d0133920f77301fcef15a9128200, unpack 0x33c1f2323f2043f4017eb76ad686800, unpack 0x2383fd9b87502df0405cd7038e0075a6af5600),
  (unpack 0x16923e84074c08e8405eaa0392107246afa600, unpack 0xaa4ee6195f0077ff00f1140f49a34d800, unpack 0x5a4b7032af6fd36f40e7041cd07200),
  (unpack 0x1cfc98f7c80fe5203d4f03ee33790d4400, unpack 0x4ce1f12e2ea801f1803f32073d0d9400, unpack 0x15ace8023cc04bac80f74f003bd130c00),
  (unpack 0x19ece46f1e00c3b480fa4c0f8820de400, unpack 0x4af0e2047ca0fbeb80f5300f69a34d800, unpack 0x510fe2089cc00fe4ba600f96c349800),
  (unpack 0x1719f0323f20bb969ac90800, (0x1a0ec66099031040501001000000e8a1 <<< 227), unpack 0x11f5dc808f8211791728001fa2847371800),
  (unpack 0x8985e83fff304783d6ed58b1581c000, (0xc2e980980814cc00a5800040001 <<< 243), (0x79d9080c14718143a01200000545 <<< 233)),
  (unpack 0x4221702a0f9819fc5dbbdb634000, unpack 0x73cbec4c798117d1772d50000, (0x2e6b82824869500001005 <<< 267)),
  ((0xec1 <<< 340), (0x14b <<< 342), (0x10f <<< 343)),
  ((0x6c1206a76829cc00e0805040001001 <<< 231), (0x522a3023200d608053e00200000545 <<< 233), (0x1f4d09452028101a5001010000145 <<< 233)),
  (unpack 0x346d721dbf1055e500b87a07da684000, unpack 0x42cf5041ee07df2803d8a07c5694000, unpack 0x38817880577004e5805f1da694000),
  (unpack 0x5af7ff116e4019d4c07f3bc56a4000, (0xc03546ca482894019100104000001 <<< 235), unpack 0x469875223e20f6d8aa071c00eb4000),
  ((0x380809bca0238008a8009080001 <<< 242), (0x2d8900e34822ac0622800800001 <<< 243), (0x1422a0524180848009f807040001 <<< 243)),
  ((0x8320c1f0c00ca40fcf00c0000021 <<< 238), unpack 0x1e64be825fd6157ee02e8d81cf4000, unpack 0x12a3fd012be4087d101e3c00ef4000),
  ((0x95180132806430324c010000001 <<< 240), (0xa24e43ebe841ea03a6001000001 <<< 243), (0x50516650081b70050d003 <<< 267)),
  (unpack 0x1b50f22d1f003be8bf7769ac80720, unpack 0x12b17139ff1005e5d6d0007e8a11c000, unpack 0x1e42bf81c7b41072802fb2c000fd142380340)]

private def t5 : Array TensorRankColumnReduction.Packed := #[
  (unpack 0x10e9fd0daff00573e00f8e01cb0038c989000, unpack 0x705078016f1067dc40bd22071ae4c000, unpack 0x2c25700b5e6071f200799407c4d74000),
  (0, 0, 0),
  (unpack 0xb10ce201be706fc27d01f5193120032, unpack 0x8299f054fc90c3a981f18c0e3041c480004, unpack 0x5cd2f81c1d4dfe007c240e6801cd00004),
  (unpack 0x4587716de2825ea003ea0d360a03a, unpack 0x1b86de4a0798087d17aec00014, unpack 0x1cc8de88eba6127b7dd8350014),
  (unpack 0x10c41e4d07b816f8103f1f01e916280380042, unpack 0x10d8ee03de10479201f5800e5041ce80024, unpack 0xe191c073fd0127ed00f6b81ee99ae80024),
  (unpack 0x59f272126f8845e7003d70072c00e0004a, unpack 0xe139ea735ca053ad0178540f8ad280034, unpack 0x653d00ce9029f9c77b8d280034),
  (unpack 0x56b2fa1f9fb831f000ba1407b5600052, unpack 0x38d2e2367ec047fdb1d40e3841d680044, unpack 0x517b042e5815d4407e1407c5680044),
  (unpack 0x16207dccd7c606fb403fbb81ce08381a0a05a, unpack 0x200778045f2034feb3407c4500054, unpack 0x39e2780a2f6837de807dc0072c20e28d360a054),
  (unpack 0x1a151d034bfa18fae02fef81f6d9a350062, unpack 0x1e69ece4f8c0f75400f4d2f4d360a064, unpack 0x1fa21cc437b613f3903e2701cf0039be80064),
  (unpack 0x18a47e0f6ba218f3800e4c01f718b28006a, unpack 0x8bf3900af5004ec207e13039c10716dd80074, unpack 0x38c97c36be0859f540fa98071be80074),
  (0, 0, 0),
  (unpack 0x2c6afd1527f41ae2800940, (0x5f28082bcc1345001 <<< 285), unpack 0x1d4f60d2e0071f45800d40),
  (unpack 0xe978605fb0d781817b000e3861c740680, (0xb069237d28082c00bd40241 <<< 260), unpack 0xa8d1e41a1f401bf534700e7041c350e80),
  (unpack 0x9405e2007d00d3a101711c0f8ad281a80, (0x113cec2d8c00a1000ea00b <<< 266), (0x489660281e194f0157a0061 <<< 261)),
  (unpack 0x479b9168f0826e9005e5c03ee30d3729d00, unpack 0x4304fc122fc005f65b52072428e06800, unpack 0xaf4fe667ffe0c7a9807f580e2051c352d00),
  (unpack 0x1190fe86eff836ea205f45039e007c46b28a00, unpack 0xa625e0207ed067d780fba7b4f506800, unpack 0x302af63fdd00bbf530ec0f8ea0f5600)]

private def t6 : Array TensorRankColumnReduction.Packed := #[
  (unpack 0x3a173a89275022fb2cc2039a087e46afb600, (0x9cb0649d380a8001b3001001 <<< 255), unpack 0x2420f0267da02f8581fd46083fa357200),
  (unpack 0x24f37e136e7809ddc0bbb6073831e05400, (0x17cc008da410ca01a0401009 <<< 257), unpack 0x3d10f811674021f00c1503d0b0d3730c00),
  (unpack 0x7193f0289e980dfa5a8807240df400, (0x2d636819c50c7600e11005 <<< 266), unpack 0xb357a2c0f203dc0c0bb9807cb604800),
  (unpack 0x6ccbd0117d2037b175101ca02bfeb12800, unpack 0x6c8d730faf1855fc5dcb2005fd8e575a800, unpack 0x23e97f94ff3824f6c14070805fd8e5758800),
  ((0x2660223020536601d080085 <<< 259), (0xb46f50498815d30015001 <<< 268), (0x39c4d80ce80c0000a29009 <<< 266)),
  ((0x18d8524ed603 <<< 307), (0xc71bd09f681 <<< 308), (0x38c520891 <<< 316)),
  (unpack 0x17617c3081ffe1c84071c30e3a000, (0x8e3980a58020a4003d40241 <<< 260), (0x11973019a40b260033c01c1 <<< 261)),
  (unpack 0x79737404ff7051f000b88e07c5694000, (0x38c2e09c890123000ea00b <<< 266), (0x4c4695a02160f0157a0061 <<< 261)),
  (0, 0, 0),
  ((0xc351a2061416d100f1c03c001 <<< 252), (0xdd69931e0099280860012001 <<< 253), (0x542128d220167200072008001 <<< 253)),
  (unpack 0xd707c084beb5001f13410fc8000, (0x143ace5d1b8169400f3001001 <<< 255), (0x1301343d1600e020340003041 <<< 255)),
  ((0xc763830b1004d50076c03831 <<< 256), (0xd040148e4009b00b0401009 <<< 257), (0x421d48f80e0ec18082a00201 <<< 257)),
  ((0xd545884570198809c600001 <<< 258), (0x32247c3a8a0c7c00e13005 <<< 266), (0x1c1dc066768100201a6003 <<< 267)),
  (unpack 0x306af027fd2043ecbb4a02bfeb00620, unpack 0x3115fa44de80d3c4017aa00e400bfb1cae80fe60, unpack 0x18a6bc8343fa0770a02f4501c2017f6395d00dfe60),
  (unpack 0x66adec833d61c73101f5c81c30a3a5751000, unpack 0x11033e408bae0e7c166981d1a61606000, unpack 0x10333a1e8f9005fd205f660396007a61606000),
  ((0x12aa061fc40610400948048101 <<< 251), (0x1aa5fa3c90802f200ab00201 <<< 259), (0x687004301120004a80081 <<< 261))]

private def t7 : Array TensorRankColumnReduction.Packed := #[
  (unpack 0xc488e2481d60a3dc38ec0fad2220004, unpack 0xa82f01bae2821fd1500e8d20400a4, unpack 0x2d2fb0d07c037f5e03ea1039c057fd60400a4),
  (unpack 0x2d7be2471c402fc481f1340e5055ff59d00dd414, unpack 0x5549701c5e8861cb403e4b140affacc8068b4, unpack 0x297670398fc80fe81c42071030f499009d4b4),
  (unpack 0xcd6bf1da7ec10f0407c25038c157fd7280024, unpack 0x3722bf005f643bfb8d53038a0d7fd70800c4, unpack 0x98c3c0267c4077bc03fb2ca083d30800c4),
  (unpack 0xb59be019932203e2c01c602bfeb00034, unpack 0xc0e1e49539609fea7d981c806bfeb000d4, unpack 0x97abe20e5ca0db9500f2340f96e9000d4),
  (unpack 0x10529c8ec3b001f8a00e6c81f51ed300044, unpack 0xf9c8f809dec067de017a140f6ed3000e4, unpack 0x6d70e07c3f60f39b817de00e2835fd000e4),
  (unpack 0x10da9dceabc4117e300f9101ed1fd300054, unpack 0x2c0bf81dbd4053b700fd500e0815f5000f4, unpack 0x5c87f2242e406bc300bb23041e9000f4),
  (unpack 0x5198e411dcc013b90072440e2045e900064, unpack 0x1b50dc0e4fe014fe900f6cc9023feb00008, unpack 0x2a41e042beb0eb8f81f6880f88e900008),
  (unpack 0x511172149e2055c9c07924072032e5801e5640074, unpack 0x26c1f42b2e080dec00bf34073c02ff4e1740028, unpack 0x10353dc023ee1ef9f02f8601c70c3a5740028),
  (0, 0, 0),
  (unpack 0xe5f8e83b9d7013c500774a0838741acc0, unpack 0x5a1afa001fd1d4007aa80f6ac004d01c0, unpack 0x171fc00b7d402fadcbd4000d01c0),
  (unpack 0x1030de8a9b8a0b7b503feeca0839281d180, unpack 0x1ba27a88d7283af4201f42038350e80, unpack 0x15ebb058f000de3807cc803ea1a800),
  (unpack 0x4d89f46b5c400f8c80f9d40f94d681480, unpack 0x35c93a0d07a01aea207f0a03801e00380, unpack 0x183de804bcb087c40171d40e1841c01e00380),
  (unpack 0x1272be892fb4067f102eb281f29ea054300, unpack 0x5f13e877dd0037c780fa400f481b2a900, unpack 0x4444f02c1c808bb6007a640fb8c0d9400),
  (unpack 0x1149be8513e0b0303ea941c07a00, (0x72d630723409c80163 <<< 280), unpack 0x1e915e00c7b20df3700e1a01c06800),
  (unpack 0x589398f2f043fe8207f1f0780e8600, unpack 0x280c7d1097840ce7003c7e0b80de00e00, unpack 0x3103a18975074005ec5809e00e00),
  (unpack 0xe603c9477f811f3807f7513800609c00, unpack 0xd42af80c3ef0dbeb0078948e0d3602f1c00, unpack 0x14e3bd8a7f82d603cc2238004f1c00)]

private def t8 : Array TensorRankColumnReduction.Packed := #[
  (unpack 0x1a623f9237243dea805c54438081800, unpack 0x2e21f9004f681af6a01e8e03808033800, unpack 0x11553c151f8c24ec005f0a03834d800),
  (unpack 0x5b2b7313ef205de8803c5057c4329800, unpack 0x5cf7a96b7f012fec45af0c20fadb2bb8800, unpack 0x5004760e0e4071ca00b805af0c20fadb2bba800),
  (0, 0, 0),
  (unpack 0xd1e3c89d7e41272202e2820e1d000, (0x4867e908121b40004540041 <<< 261), (0x1b8d2836ac04400155401 <<< 269)),
  (unpack 0x1e4279090e4071e740febb2820e4a000, (0xa695322a980a01025 <<< 284), (0x60ad91086611cb00c9401 <<< 269)),
  (unpack 0x423fe02ce4007c6407cea07ca6b4000, (0x1fc7f61b09814a20785 <<< 279), (0x330409e36808c4010ea0061 <<< 261)),
  ((0x498699b6160429803ce00a001 <<< 253), (0xe4034cf800fc140e10001 <<< 266), (0xa3e804160146e02a6c03 <<< 268)),
  ((0x3e146060900f5480fa1 <<< 277), (0xc774231de4034a0343 <<< 280), (0x924ae02c080995028d <<< 280)),
  ((0xa545014ad81d630167c1 <<< 272), (0x58264144620418008f81 <<< 273), (0x2d9c5941820b84005401 <<< 273)),
  ((0x16835817410065805751 <<< 274), (0x5011a6ea881cac01139 <<< 275), (0x12f47631460369206211 <<< 275)),
  ((0x8a1f600aa823fc02359 <<< 276), (0x1289a0798a8253e0407 <<< 279), (0x256919e3c416300031 <<< 281)),
  (unpack 0xb0df90e47f80af285057c4006fa0, unpack 0xde70fc679d8083f8b8835e1841f5b6574060c0, unpack 0x2422be3384de45801af0c20fadb2ba0040),
  (unpack 0x3100bc0867d564c05fd283abadb2bb3000, unpack 0xac3e26edc2077bd017ab00fce34c2000, (0xb46920bad0115d014d2058001000040001 <<< 216)),
  ((0x10056a715204ea8001301 <<< 271), (0x36437020fa1d0b800f1 <<< 277), (0x15e0c0e7b6043400a85 <<< 277)),
  (unpack 0xd30fc821be0047b301fe9c1da083876600a4, unpack 0x6bccf5244ee81be540fe01074820e00088, unpack 0x2c19be1d1fa832ecc01ca02bea00088),
  (unpack 0x6fb2ffcf10538f817e28ae5041c9400b4, unpack 0x24007a8b27702cf0601cb92b88400a8, unpack 0x16eaf2693cb063e600794e0fdac8400a8)]

private def t9 : Array TensorRankColumnReduction.Packed := #[
  (unpack 0x48e6e864ff700fec007810af74d6800c4, unpack 0xada9e003bf50039201707caf94d4800c8, unpack 0xf11be2285ca08bc6807d2a0fcad4800c8),
  (unpack 0x125ab885a78805f92c232bb5000d4, unpack 0xa430fa131c404fa181feb0af96f1000e8, unpack 0x521ae0681d307ba400fe120ed801f1000e8),
  (unpack 0x206dbb9107082dea003c7703f2000e4, unpack 0x1e133e05efc027e0407e9883f200108, unpack 0x192e3ece2b9c0878502ee515c00108),
  (unpack 0x261cb9992ff815f8401f3c8bf2000f4, unpack 0xef83e45abd41575102e6191c00128, unpack 0x90d3910571403e4a07ff083f200128),
  (unpack 0x20fcfb163f4812fb8f88a3f200008, unpack 0x96f7f868f9404fcf02e9785c00148, unpack 0x2e213c1927d026f0a03ec383f200148),
  (unpack 0x6977a8e8fd02cf2205c7f23e2107c6d840028, unpack 0x292bba925fc40beaa03f40abf53c69940168, unpack 0x2e087818772021e4c07c3c8398107d6d940168),
  ((0x2081c71bc81cd11 <<< 291), (0x5b925041581183 <<< 296), (0x89b506584056d9 <<< 295)),
  (unpack 0x229a3880b7601af72ee584a0a40, unpack 0x2d61ba170f9c1af5005edd4007001c0, unpack 0x2d29f13d9ed041fc5d0407b5600b40),
  (unpack 0x30dc02df9c0d75202f0601d194501d580, unpack 0x148efdc8abe61af9600fecf29c234d800, unpack 0x18d63dc15790177cc00e6d81c7003c20d0e80),
  (unpack 0x3ca7f03b1ea031d800bcb48a003c80, unpack 0x8430e4087ce0d7ea01fb9c0e5841c00be80, unpack 0xd649ea421c808bed347c0f880107e80),
  (unpack 0x799f792f0f5831f080bfdc070c30fe83655a300, unpack 0x8047fa203f1037e181f6180e5041c001f0700, unpack 0x7c4f2019e502dc2407da6821c005f0700),
  (unpack 0x1c9e798057a064405c280b8042600, unpack 0xc1cbf251bfe027b081f47c0e03658028e00, unpack 0x136f87addf06bcc00f9580e0d650038e00),
  (unpack 0x2002789ec7442ff0615fdd80ec600, unpack 0x1ef57e40f3920bf6c80ee80fd600, unpack 0x844de8e8fbc1c7ca80fa80ed600),
  (unpack 0xd3fff011e1069d8443feb01b0cc00, unpack 0x2242700c3e6873fb88bebb06b2ec00, unpack 0x1490e673df201bcd117000701c00),
  (unpack 0x454ce059bc500b8d2070085800, (0xa9d01237d015ad <<< 296), unpack 0x7a87f8241f006ff080700c9800),
  (unpack 0x6fcde81f3940a7b57b201c20c3c20e003800, unpack 0x8098ec789cd00bd4687ba02e8202e2a5000, unpack 0xae4bf0203d20e3d06876302faae080b8a9771800)]

private def t10 : Array TensorRankColumnReduction.Packed := #[
  (0, 0, 0),
  (unpack 0x1f425e431bf0bd9772c25000, (0x1877a0cca608440014001 <<< 269), (0x453848aa4c1605010040041 <<< 261)),
  (unpack 0x5718723a0f4015f4003d180746514000, (0x4c7cc186902bb60200c0140001 <<< 248), (0x4386e0651c14460036401c0001 <<< 248)),
  (unpack 0xa423e810fb028fd2fe5d228000, (0x49341952a613ea019ce0161 <<< 261), (0xffb3614e7c0e2602c7c01 <<< 268)),
  ((0x52f2655804c9005b7001861 <<< 255), (0x7d8231ee821ef580e080141 <<< 261), (0x784930f3900a23032880341 <<< 260)),
  ((0xc3510081805c5001501 <<< 273), (0x128ef8f3a301584071d <<< 278), (0xa409a0f8506160022b <<< 279)),
  ((0x980880b81048d9 <<< 295), (0x91fc32c57010ab <<< 296), (0xebea53b2881f05 <<< 296)),
  ((0xa082602314224b1 <<< 292), (0xbb4902e416f61 <<< 293), (0x52eac845360e491 <<< 293)),
  ((0x2c18042b3f080c1 <<< 294), (0x6211831c14152d <<< 296), (0x51aa52634801c3 <<< 296)),
  (unpack 0x8060e834dc5043abb201c20c3c20060c0, unpack 0x7b9df0031ed28d2e3405d0405c54a0140, unpack 0x28b8fa4cdd50cbc0697c302faae080b8a94062c0),
  (unpack 0x6c70e03bbf4057c28074102fb8e08238a0cc3000, (0xe681e002342bef0c7641242041040001 <<< 224), (0x8a8971e5642a100c0841180040040001 <<< 224)),
  (0, 0, 0),
  (unpack 0x28c77e9b876410ea30dd78038c087019860088, unpack 0x29a97028ce003bc5a17af007d46001c8, unpack 0x3206761dcfd845e1c8bc06071420e001c8),
  (unpack 0x8f2af23b3d40abfb907d868ca29a6c1468a8, unpack 0x524770186ef061c308bda6071c00f082009d5e8, unpack 0x8887a229f001dcce138a807b4604d40dd5e8),
  (unpack 0x9484e67b5e600ba090f55c0f96cd000c8, unpack 0xc3b6ee2bfd9017df1076e80e7041c900010, unpack 0x125f4205f3819cae1fee3a4900010),
  (unpack 0xf4b2f6435d20079290fe980f6afd000e8, unpack 0x188741e7ec061d288ffa6861f900050, unpack 0x48ecf4189e90c7cc4275980e4821f900050)]

private def t11 : Array TensorRankColumnReduction.Packed := #[
  (unpack 0x1d099c41dbc00efb384f3005c00108, unpack 0x2bb1f8c838e0474686fc183c00090, unpack 0x9607d842fce00f8423eaf83c00090),
  (unpack 0x79cb7b332e7849cf813feb01a0a128, unpack 0x4105e0b33ac0ff40a8feec000d0, unpack 0x3587380b876030ea119c0d360a0d0),
  (unpack 0x15407e16373032f1349fdd8350148, unpack 0x3c14f0601e90b78d817fd60d360a110, unpack 0x153cfdc653e20d7d286faec00110),
  (unpack 0x3939bf15a7c00de315dcea0baa34108e080168, unpack 0x344f881b75368849fc5edb4204e280150, unpack 0x16d07c8a07bc25e4715fa407940878308e280150),
  (0, 0, 0),
  (unpack 0x1ca8f807ae9031c5d97a8d41b6c0, unpack 0xc218e0743d2053dbaea34000, unpack 0x6f707529aeac8bb9768d01b8c0),
  (unpack 0x276a74254f7811d980fd1207d4728ba81d980, unpack 0xd47be4211c80cfb58079100e1841e506800, unpack 0x159172098fb81dfe9b72073410f08a69b0e80),
  (unpack 0x1a8e9dc04bc81577903fae537a69b1e80, unpack 0x89c9f2431e802fc481fd3c0e7001cd00500, unpack 0x1187bd0e477834fd4f13038350500),
  (unpack 0xb503993d03cf8605edf038e0170d655cb00, unpack 0x1c6fc557a20c7f402fa001c40c386b2a900, unpack 0x4587e4761c109fd83d864841c05d300),
  (unpack 0xc4d8f019de30e3aa0172348e03658028e00, unpack 0x1265d8be7b200fc101f880d9400, unpack 0x15a7a103fe027f7807ff503808030e00),
  (unpack 0xf0601abc1077e2907a080e0d36fd600, unpack 0x72ca7e329fc013f29807a00, unpack 0xb7ab89f976c26f3605fdd8357200),
  (unpack 0x7208fa4ebe28f3c5007a080e0d372ec00, (0x12feb42852840500101 <<< 279), unpack 0x159c9c4e139c0f7140d3730c00),
  (unpack 0x4c9fee601d54b3c8b740d400, unpack 0x1a14f05e7e8093f8bfd602003ffcc00, unpack 0x6be0f01d9ec021e2803ea0000fffcc00),
  (unpack 0x18829d03a39e097a300ea801ed83668c800, unpack 0xec77f055bdf8c7cc20e5011c108bc3e2f5d43e03800, unpack 0x1751c4817e185f6a22e8191c608bc9bf75d4fe03800),
  (0, 0, 0),
  (unpack 0x8893b066f6420ff6e5dea35000, unpack 0x1340bf4e7b8c137b68203ea34000, unpack 0x396639881f841af0405ee5da34000)]

private def t12 : Array TensorRankColumnReduction.Packed := #[
  (unpack 0x16991cc403b80074603f2cf51ca2ea000, (0x511500ddc216f5814880061001 <<< 249), (0x29784054a61b520037601a0800800001 <<< 225)),
  (unpack 0x2d0f74244e6879dec07febca6f4000, (0x19039c62020424202a6807000001 <<< 243), (0x2810e028cb019180191 <<< 278)),
  ((0x63e53191060264810ba00e01 <<< 257), (0xa5cb06480227c00f080103 <<< 260), (0x458084d32089101d080121 <<< 261)),
  ((0x6ed580c3787cf800069 <<< 275), (0x187b25f0001e901b <<< 284), (0x3d8e4c63be054500d75 <<< 278)),
  ((0x18263125120cf29 <<< 293), (0x7c04079b20067 <<< 298), (0x237ab3b50c1c1b <<< 296)),
  ((0x44ac03905 <<< 313), (0x364c3c8d01 <<< 314), (0x1e4c28513 <<< 319)),
  ((0x1988e3a64d <<< 312), (0x5d11061 <<< 316), (0xf5580167b <<< 314)),
  (unpack 0x1d9afa00e76016e0605d5203db06cd0062c0, unpack 0x981e42b1d8cb3e21072808e0845e1f17aea0240, unpack 0x190c9d4b8bcd98f6820f8191c608bc9bf75d4064c0),
  (unpack 0x3552fa01179a1afaaea223a8b987000df56282fc800, (0x20b483bd10414713d4441c010308400910000555 <<< 192), (0xfaa4b081e659c7127a0408110008400f10014555 <<< 192)),
  ((0xf281065219 <<< 311), (0x13cb883fd <<< 313), (0x52246062f <<< 316)),
  (unpack 0x106791bfe1c93ca807a9c073010e24c505f901c8, unpack 0x12cdfb1157f24ef02f0403960071a0555e0210, unpack 0x657c421e90d3b400f8a40e3021c64c14555e0210),
  (unpack 0x694ff8185ea81fe0c03abc073c00f30c5d401e8, unpack 0x261d70091f3071c3807f32071030f30c1c40250, unpack 0x27a93f9bd70e45ec203e6603edb083c40250),
  (unpack 0x411dfd0dae8071f5803d374de80010, unpack 0x1b309c00d38a08f1101f6201cf0039bc80290, unpack 0x1e9cfa3a4e2cd7cb80bfbe071bc80290),
  (unpack 0x29d7d081fbc07e1007e1a1600050, unpack 0x3aa1f01f4e7021f24038ba071c21e002d0, unpack 0x700370070f04e5fd003b94073831e002d0),
  (unpack 0xceedc8e8b833874b00f0111c00090, unpack 0x13ecbf8113ad27f0103ea809c00310, unpack 0x1a123c04afb01c7bc02f9a89c00310),
  (unpack 0x5a07037af8cbbed0838000d0, unpack 0x5d0074385ee025c4c43800350, unpack 0x482f76067f1cc7db443800350)]

private def t13 : Array TensorRankColumnReduction.Packed := #[
  (unpack 0x3888e23bde71b3d8bf400110, unpack 0x10b0f3227e9021ff5800390, unpack 0xa013c06a3d92e7000390),
  (unpack 0x23217e85e788f1e8825c21238a10f783c40150, unpack 0x39f47930afa8dbcac83bb6471801e6f0bd403d0, unpack 0x7e3ef0365ed42dc3c4b8b4270c02f30fdd403d0),
  (unpack 0xa467f8d0bdd1a78782e7041d4dcc300c8feade800, (0x137ed30b209034111b0815000121000100050005 <<< 195), (0x1c00a1515652286020d815060100515810011001 <<< 195)),
  (unpack 0x1ee1f30d0e482df6dfbbb5635dfa005c1c0, unpack 0x5b26702acf3055ea803da00555c03981c0, unpack 0x1044ff9bafd7c5b510015c07801c0),
  (unpack 0x75df01caf2803ee1c4407b5611107000547f40, unpack 0x14ca3d4b87a6097e176ea411476a0019780, unpack 0x4527011df2067eac0bfbb2820e404471a0007780),
  (unpack 0x4675044f6019f140fe8e07b566c440700b80380, unpack 0x4d0c72308fc873e7003b98071bf2c020f700380, unpack 0xf045c4fa7a808fdb74981ce0838a1501c020ff980),
  (unpack 0x29ccf8219e6067d400f976071c02fac2e806a4700, unpack 0x119bfb14ff4c14f0605dcc039c107a800f2b23650168700, unpack 0x26713e0e27400ee9401d66039b6c2c80510700),
  (unpack 0x6ab076009f387ffadbb447dc7ad32807500, unpack 0x29e7f49dba20afbf02f2e05ec083eb6c24b0019fd00, unpack 0x1c4e85dbe3f0d8283fd3c6985a6c0017fd00),
  (unpack 0x1da37a390f386ff8683b080fdb70409c508b80e00, unpack 0xd08ce81d3d0d8d0477b01ea8e0423826a7700e00, unpack 0x411471342fe807e3603c90175789826af000e00),
  (unpack 0x2a09dcf9bfe0572122fac09ec581847e17a8005dc00, unpack 0x67727c468515d3843d930422f30fc1e2d3607b9c00, unpack 0x173a5e0a1bd142fca22e9091c40879a8007f16a0781c00),
  (unpack 0x3731f3203ed221f24038b487a4c18200aff6c00, unpack 0x304ab883373421f8c83c03438d722076001c00, unpack 0x8348f4289d70efcc3b140f64c172327d8c00),
  ((0x1bb0e926521901f862c10003b884012539a00101157 <<< 181), (0x302535090d9967011584021be806e384c14010000b <<< 185), (0x827e3076660381a110ea0850060110814000450063 <<< 183)),
  (0, 0, 0),
  (unpack 0x62cb7006ce5021dadab1aefd002d, unpack 0xc98bf0fcfc42efe2e2203801557000, unpack 0x153c1e0257ac197f5dd440057000),
  (unpack 0x80c00cfa008f0902ff6ed584441c002a, unpack 0x431271035f4809da00b94407d48228e000, unpack 0x1b42389e57e019f30c5041c8088e000),
  (unpack 0x8d17c8b0fc82cf9a03d4703dab3622038007a, unpack 0x6e6d7021ee680bcd003b98071bf2c000, (0x1cf3fe692f012100149807040000415 <<< 231))]

private def t14 : Array TensorRankColumnReduction.Packed := #[
  (unpack 0x245e7d81efc821ef407cb9038e017d61740094, (0x212100aa4a0ea840b4e00e082a000080001 <<< 214), unpack 0x512afc089d906bff3f900e6db0b2000),
  (unpack 0xa427c0e1b920ffe75823ee3d69940068, unpack 0xc9df835fa20cf3d00e2e05ec083eb6c2000, unpack 0x1cac9c4527bc037f878141fe9e34c2000),
  (unpack 0x10a0f80237c823f9341d0407edb8204e2801a8, (0x81b890da981c98087b81003081080001 <<< 224), unpack 0xe82eee561dc08783c079282eaf1304000),
  (unpack 0x10b0e40a3fd0ebd49077684f62c0c23f0bd401d0, (0x44069170ba84441008040422030080011 <<< 220), (0xe1c543a802a5e020e8481021000840031 <<< 220)),
  (unpack 0x4c03955b719a0e4c17f0043d6087080bf1401cd8028e00a0, (0x1005f46769c689085606000700405158180010001 <<< 191), (0x13551021be80585129e4010180602001080400041 <<< 191)),
  (unpack 0x11d01cc603d213e1d940b8003f7108e0495dcd03c8b0193eb60, unpack 0x79f8e1221d1c4bf30070b88e086ff4037e384f8280fa8041fa0, unpack 0x301438c6af6b11e91a5ca1d7821479871081ff59140700003ffc60),
  (unpack 0x481efa009f4065fc1aa207c4d29000, unpack 0xf09dd574ba6807f741e2fa1c501382e71000, unpack 0x51a1e1767c08773640e4121c301382e71000),
  (0, 0, 0),
  (unpack 0xd6bdf08f1c6057a080fc180f49a520210, unpack 0x82177781f4021c9803bb31a620120, unpack 0x1965fe86675c06f3a05fdd038620120),
  (unpack 0x571c70263f4067e2403800250, unpack 0x990afdacd003f6b0e401a0, unpack 0x3681f0d8fd004fcc30e401a0),
  (unpack 0xd287c29ee086fcd003e9807b4d00290, unpack 0x3d731a2f9053fc592607c4100220, unpack 0x16477a730e9039d1c07b8a0718300220),
  (unpack 0xca27d125f2013c4c07c32071c00e002d0, unpack 0x23bb7e056e6801e2403b9807b26002a0, unpack 0x504df1641fd06bdc80f92607a26002a0),
  (unpack 0x10dc91cf8a0e7987d2c00310, unpack 0x1de1bd5853f416fed6e821c00320, unpack 0x13c45e8a13ba09f9f02e2b21c00320),
  (unpack 0x7260fb6c2e104fdb403800350, unpack 0x50f7617de883dd69038003a0, unpack 0x56eefc48df6811cd9038003a0),
  (unpack 0x6410f46d4e8079fe5800390, unpack 0x5a0bc42df96877000420, unpack 0xad97b662ec261ee5800420),
  (unpack 0x51e1f28d9cf08f8221f01c0f64ce403d0, unpack 0x4a10ec9c5fd453948179780e1809c1004a0, unpack 0x5a597b105ff0fb90793087a4d004a0)]

private def t15 : Array TensorRankColumnReduction.Packed := #[
  ((0xb00a54396d6451540095400d570dcf02d1543 <<< 204), (0x1bea4478082e728787a8b00a802801048a41 <<< 206), (0x5b2a848718198446c61468754000008145 <<< 215)),
  (unpack 0x24507228dec05dc57400d40, (0x22a578abf01451011 <<< 285), (0x58a606e40809000141 <<< 279)),
  (unpack 0x4c37f4048fe84df600bae407d4708a84c0e80, unpack 0x9f23ec9439e0b7da6ce5b954521da800, unpack 0x1a065dc83fc01cf6803e3f81f29c2a280e000),
  ((0x5d <<< 344), (0x1d <<< 347), (0x3 <<< 348)),
  (unpack 0xc33e0613e1b2803f4781f2dd2352d00, unpack 0x419e7c0d8fa029ec1cb007180affac69b9400, unpack 0x11b4bdc5dfa215fe402ed981c806bfeb06800),
  (unpack 0xaa27d018f983bdb40383707e40f5600, unpack 0x1e323999b77c33f0607ec02b8359400, unpack 0x1c929d8883d01479402e1d95c06800),
  (unpack 0x41b5cc56fe416f7184ffac07200, unpack 0x6412732a4f693917f407a00, (0xabb605a0c878144401 <<< 279)),
  (unpack 0x1ae85e04978b3d7140d3730c00, (0x774a472f001400041 <<< 279), (0x608a65b810441001 <<< 287)),
  (unpack 0xe001fcd1bd306bf8b7404800, unpack 0x35d73a9487a43ef62ff5834d800, (0x1493803a041055001 <<< 285)),
  ((0x92b0c05b2b14c4d0ddb52005510dcf00514030003 <<< 188), (0x14e1c3197060b4080a0050600c2801060001 <<< 206), (0x14f90225ae84f24066c00107004000081 <<< 223)),
  (0, 0, 0),
  (0, 0, 0),
  (unpack 0x1972bb07d7a57a405f7203ea3845426000, unpack 0x4449c811f92147a17acf2dcaa290e000, unpack 0x1adebd40c7900af6201f7e81f29c2a280e000),
  ((0x2935015 <<< 324), (0x4d65a8d <<< 325), (0x3855115 <<< 325)),
  ((0x90bb410660c000048d0060001 <<< 250), (0x66083081da1a55018b000c055 <<< 253), (0x3cda10783207b7017660100d5 <<< 253)),
  ((0x198101103087b4001981 <<< 270), (0x5910d0896e06c1808805 <<< 273), (0x7ca3f82fe80b1b010765 <<< 273))]

private def t16 : Array TensorRankColumnReduction.Packed := #[
  ((0x3c2490b49306fce1 <<< 290), (0x1f10094c9e19429 <<< 293), (0x61ff80917812001 <<< 293)),
  ((0x13b6e0b0409 <<< 310), (0x3512a0d73b <<< 314), (0x2522213c3 <<< 315)),
  ((0x3b353d <<< 330), (0x5855 <<< 335), (0x519a7 <<< 332)),
  (unpack 0x55dcff053e8845df4879e657140af4401d4501c0340, unpack 0x3075f8b4372259f8509d8c83b6087a86292000, unpack 0x34177a5ece64b5c8a17ca707ec752c5426000),
  (0, 0, 0),
  ((0x6c3d1 <<< 331), (0x8817 <<< 332), (0x12e27 <<< 332)),
  (unpack 0x246ff7055ece59d03439c5af2825ea00bf3c03a8a07ed60120, (0x339079076983b9e89cda9a02a883e780a8a01141 <<< 193), unpack 0x839fe0065e1027c50176460e381057607e89417000),
  (unpack 0xe413f0af7a81478d02ee9e0c7030ae0087d4503f0b341469a0, unpack 0x6cd9780a0f8867c480fcf4070038e6074501c0240, unpack 0x7b671050e3e1df9343ea9af2805ea61bf3c03b9e07dc7a6c144ea0),
  (unpack 0x1e81e269bd5073978077450638182f4509fef20220, (0x182e0c530782224036d00107004040081 <<< 223), (0xbffc4065032ec4d25f352805510dcf0051403 <<< 204)),
  (unpack 0x14385ec89bfc0172502f69a0af530ae0483fddf202a0, (0xd2300353885730066800007544000081 <<< 223), (0x460bd2da1f206cd0d7350807f10dcf0051403 <<< 204)),
  (unpack 0x6a35088f2603fc347abc073005ee00bf1c03a9a073080e0320, (0xffa391392b024dd2e38a2825510fc70151407 <<< 204), (0x33218014ae0544c0c80fc60e0080821060001 <<< 206)),
  (unpack 0x6ea77c308f365df1c03d95bf3c35fa41bf3c0fa8a077200e03a0, unpack 0x3ab1fe2cbe8067ddf8fb962811e5607ef3a800, unpack 0x74fc0b8f8390f50f1f086bc2017a803fcf00ea281f71e9b0500),
  (unpack 0x21a5ba07279438e15e5cf5f79603f530fe9e07dc503f63d360a420, unpack 0xc8c7827be0e33f74079f2071018e62e0127fbdacd0500, (0xa6867018930276d381b530055305cf0a51403 <<< 204)),
  (unpack 0x404d7ba36f5853e674f98647db7000bd1403fbbc7604a0, (0x35000144ea084010213b98181005042138a02941 <<< 193), (0x2649e040a59928f8c41f8c1150854425c1403001 <<< 193)),
  ((0x970784de40581005 <<< 287), (0x727a589a6c085 <<< 301), (0x29e1470b407 <<< 306)),
  ((0x635041 <<< 328), (0x88083 <<< 332), (0x81391 <<< 329))]

private def t17 : Array TensorRankColumnReduction.Packed := #[
  ((0x92a4a073069e40341007 <<< 266), (0x9f64309c3005270142c01 <<< 268), (0x173424297f815a40129001 <<< 267)),
  ((0xc8a686ea404c14055 <<< 283), (0x80c41208c1804015 <<< 285), (0x48a3285620045 <<< 301)),
  (unpack 0x10786f5ed023b5069b0500, (0x7902e1c80069500141 <<< 279), unpack 0x844af4119c10abecb741a800),
  ((0x1 <<< 351), 0, 0),
  ((0x35d71460480dc240f5 <<< 282), (0x292700c7cc18fb013 <<< 284), (0x38007cce0a08e1001 <<< 286)),
  ((0xf3f <<< 339), (0xc05 <<< 340), (0x11d <<< 343)),
  ((0x67 <<< 343), (0x33 <<< 346), (0xf <<< 346)),
  ((0x9b9220a543 <<< 308), (0x1d8a6c346b <<< 314), (0x354821652c1 <<< 309)),
  (unpack 0x1a77de05879802fe901f8101c44000, (0x158f1a200c88005d003 <<< 266), (0xda868842c0f8240c5d005 <<< 266)),
  (unpack 0x3a41f803bf802aff2f6daa54000, unpack 0x3dd9ff04cfd01dc56ab0000, (0x4e1e5201060100051 <<< 279)),
  ((0x1 <<< 349), 0, (0x1 <<< 351)),
  (unpack 0x2c65f3138e6831fdf41a800, (0x81348144c164501 <<< 289), (0x5c1903a200481401 <<< 287)),
  (unpack 0xa12be63adc90cfe98176080f48e122000, (0x3de80e9b6081480e52001 <<< 266), (0x3281580222056340699 <<< 278)),
  (unpack 0x20fdf82f6f1811ed252a000, (0x9c1d0008304000015 <<< 283), unpack 0xa6b4e2075f4063d8bb550000),
  ((0x1 <<< 350), 0, 0),
  ((0xb926112501c1 <<< 301), (0x721d3156301 <<< 308), (0x90870103b811 <<< 303))]

private def t18 : Array TensorRankColumnReduction.Packed := #[
  (unpack 0x210ff4112fe01bea407b06071c00e39000, unpack 0x1902ba80af0016ee603e0303d224000, (0xbe41b0225c20980062001 <<< 268)),
  (unpack 0x3e91d448f841679650d54007000, unpack 0x919b90c67a412fa2e2803ea35000, (0x1d5e31651a1944005040101 <<< 261)),
  (0, 0, 0),
  (unpack 0x711d03ebf20a717dd80f4600, unpack 0xdbf874dc60c3c4017d407a00, unpack 0xc365f6091cb013feb741a800),
  ((0x6410b091053200b9e0021 <<< 262), (0x2106540f740846808cf001 <<< 266), (0x36f3284d2e05f940340007 <<< 266)),
  ((0xf6fe684e8050001540051 <<< 263), (0x13c9f22469018140410001 <<< 267), (0x1b1f040037841540445 <<< 279)),
  ((0x156f266005 <<< 315), (0x3a2e307e3 <<< 317), (0x1080d39fd <<< 316)),
  (unpack 0xbc23f020bd2bf7d069b9400, unpack 0x349e763a7eb851f5f406800, unpack 0x57afc982f8012e741a800),
  ((0xe1249343280f5201c5800400001 <<< 244), (0x3af9c0b010949404d9 <<< 278), (0x50b640351841da00e5803 <<< 267)),
  (unpack 0xd912f0629db033d1017d4a8000, (0x2a84d063e21c410044401 <<< 269), unpack 0xaeadee281f5b174501ed0000),
  (unpack 0xcaf882b841d7917e8004ea0, unpack 0x418ff1270e4811f65800340, unpack 0x61abec205d3083d4017f400240),
  (unpack 0xcdefa04bed071d4101c00280, unpack 0x75eaf9110ee021fc5fbb06a003f380, unpack 0x8240ea2a7c70abfba834d800),
  ((0x5d17331958246601 <<< 288), (0x630e0117d00cc901 <<< 289), (0xd5448b330158c81 <<< 289)),
  (unpack 0x2372be08cfbc3cf1405ea003ea0a000, (0x1aa6e8e14a0954001 <<< 285), unpack 0x221e0125d20b3caeeab0000),
  ((0x15ceaa32b504c1 <<< 299), (0x690670e5a8081 <<< 301), (0xe2e22080784d <<< 303)),
  ((0x4637486d <<< 321), (0x141358c3 <<< 322), (0x3a64d845 <<< 322))]

private def t19 : Array TensorRankColumnReduction.Packed := #[
  ((0x7568053be0655 <<< 298), (0x177a2414378793 <<< 299), (0x8c19033e000a5 <<< 299)),
  ((0x1b86849 <<< 326), (0x4343c3 <<< 327), (0x1958185 <<< 327)),
  ((0x349119 <<< 329), (0x18bf <<< 334), (0xe44b <<< 333)),
  ((0xa5d <<< 338), (0x13f9 <<< 339), (0xf23 <<< 340)),
  ((0x14b120605c023be0385000800001 <<< 243), (0x64794a007000c00145 <<< 278), (0x2da8d01cde0832002d4001 <<< 266)),
  (unpack 0x382d3c85072032fe83d000, (0x552f42137019 <<< 303), (0x35da985be501 <<< 306)),
  (0, 0, 0),
  ((0x11a99 <<< 335), (0xf14b <<< 336), (0xc59 <<< 337)),
  ((0x22971385343e9 <<< 300), (0x9ed298d94199 <<< 301), (0x4e86106902025 <<< 301)),
  (unpack 0xaa3afd0dd0cbfdbb750000, (0xc9b56450004c540045 <<< 279), (0x135800566483800015 <<< 283)),
  ((0x4a40483420090401 <<< 289), (0x2039795a5c0a15 <<< 297), (0xce8b1264e1751 <<< 297)),
  ((0x1457880d7e030540041 <<< 279), (0x670616a040f1 <<< 301), (0x57228197441241005 <<< 285)),
  (unpack 0x4326fd132ec00ffe803e43b4602000, (0x54567027dc18a1006640001 <<< 260), (0x7563020868302c01ef801 <<< 267)),
  ((0x1012acf9e50b <<< 306), (0x47c09241cc3 <<< 308), (0x452e0354203 <<< 307)),
  ((0x67 <<< 342), (0x9 <<< 343), (0x23 <<< 345)),
  ((0x340d408fc1 <<< 314), (0x660c01007 <<< 317), (0xe82a0d95 <<< 317))]

private def t20 : Array TensorRankColumnReduction.Packed := #[
  (unpack 0x2c183904872828fa005c4903e224000, (0x2d9786462003740381803800001 <<< 243), (0xa44e4749800d2066d <<< 279)),
  (unpack 0x1bb3f0b03e1315007b479b000, unpack 0xf487c8cdbd2bd97aea3d000, unpack 0xf71afe2b5ee9cb6da34000),
  (0, 0, 0),
  ((0x48a820ec900845005 <<< 285), (0xc1c58c1341451 <<< 297), (0x34a3713e201f <<< 305)),
  ((0x286f00550809f00143 <<< 280), (0x15169440e809728019 <<< 282), (0x298d685936058740e9 <<< 282)),
  ((0x1062843805075 <<< 303), (0x10289cd3e703 <<< 306), (0x6135c1130219 <<< 305)),
  (0, 0, 0),
  ((0x208fb <<< 334), (0x5a81 <<< 335), (0x1619 <<< 336)),
  ((0x525be148b407 <<< 304), (0x1e15c459c105 <<< 306), (0x5547040c815 <<< 305)),
  ((0x10b3083 <<< 327), (0x460c1 <<< 329), (0xf20211 <<< 328)),
  ((0x185cb445 <<< 323), (0x500481 <<< 327), (0x3ee8187 <<< 326)),
  ((0x96d9aaf <<< 317), (0x39c6a0b21 <<< 318), (0x24710855 <<< 321)),
  ((0x125dcc2764014440097 <<< 278), (0x701481180868da03a3 <<< 279), (0x2ad40889ea143b01f3 <<< 281)),
  ((0x66512529 <<< 319), (0xc0c49141 <<< 320), (0xdb0a4055 <<< 320)),
  (0, 0, 0),
  (unpack 0x73617f15be8819e800bd0407069b96001fff300, unpack 0x14cd7c928fa428f72c0d4000ffd00, unpack 0x2457b01478014fefeb025f5600)]

private def t21 : Array TensorRankColumnReduction.Packed := #[
  ((0xc7f673a28c09f901e0c00d <<< 264), (0xf10a26bb808160149801 <<< 267), (0x307f825d403a660353 <<< 280)),
  ((0x36237136900c5100114005 <<< 265), (0x41f7c3351041040114001 <<< 267), (0x18f2a23c0582440051 <<< 283)),
  ((0x7a241 <<< 332), (0x5799 <<< 333), (0x20bd <<< 335)),
  (unpack 0x3956bd00cfc020e7406800, unpack 0x1d545d461bc20678802feec1a800, unpack 0x2499f844b961e78a00ffac1a800),
  ((0xf429e3f48c3ea9007040141 <<< 260), (0x573a0406e8000c0049003 <<< 267), (0x1511b0028c096200a5d <<< 278)),
  (unpack 0xb1e0fa685ecddb2edb0000, (0x30e5b0aef81d010151001 <<< 269), (0xb8742025580810011 <<< 283)),
  ((0x30e4f844401845 <<< 297), (0x129d84284e01d <<< 303), (0x8865259f20041 <<< 299)),
  ((0x618c3020f <<< 316), (0x1bb0227af <<< 319), (0x9199843 <<< 322)),
  ((0x7a27828cac0ecb <<< 296), (0x42e408013c1251 <<< 297), (0x1112fc6f6a8009 <<< 299)),
  ((0x511598701e1 <<< 309), (0x8d0bc4001 <<< 315), (0x3b64003c31 <<< 314)),
  ((0x727 <<< 341), (0xe9 <<< 342), (0x133 <<< 343)),
  (unpack 0x3b13be829f6400efd60d372a900, unpack 0x3c41f41f3c61a7d17e812ad00, unpack 0x28b3380967202cffaf5069b2d00),
  (unpack 0x415780a677c00fc0f4703dac8000, (0x3fd010ed400b25c0413 <<< 278), (0x3b00501ebc0d6fc0a54001 <<< 266)),
  (unpack 0x68f8154fd816f685407b56e8000, (0x500730806010100110001 <<< 269), (0xbf0e98a1805450040001 <<< 269)),
  ((0x2d <<< 346), 0, (0x9 <<< 348)),
  ((0x45 <<< 345), (0x17 <<< 347), (0x9 <<< 346))]

private def t22 : Array TensorRankColumnReduction.Packed := #[
  ((0x36c5d441ff02f0403 <<< 286), (0x2a8147c428682801 <<< 287), (0x6a3600f8081f7a03 <<< 288)),
  ((0x2e7f <<< 337), (0xb41 <<< 340), (0x221 <<< 342)),
  ((0x3 <<< 348), (0x3 <<< 349), (0x1 <<< 350)),
  (unpack 0x47057d104f704de280bea0d3608300, unpack 0x5470fc088fc2f5d760000, unpack 0x9e5c4fe78a0470a02ee8350500),
  ((0xb630a044302dd1023300180000081 <<< 236), (0x25c708417201b20122c00c000003 <<< 241), unpack 0x341906f7cc36f0603c13038858000),
  (unpack 0x734efc245f608391017fd7b6c9d4000, unpack 0x4007e058faa16716db4c58000, unpack 0x23be7009df0015ff5cbbd5648000),
  ((0x1d01102f5 <<< 318), (0x89109cd <<< 321), (0x23759307 <<< 320)),
  ((0x26e59 <<< 333), (0x48f1 <<< 334), (0x3ea97 <<< 334)),
  ((0x11882036da039 <<< 302), (0x5deba102481 <<< 309), (0xe91ac3cfe85 <<< 307)),
  (unpack 0x1b4c854bba0d78202f6ea15000, (0x6cef305d041500014040141 <<< 261), (0x6ef621b6821855004440041 <<< 261)),
  ((0x4acc30fb <<< 320), (0x1436f41 <<< 327), (0xa67a903 <<< 324)),
  ((0x9aa9f <<< 325), (0x11d39 <<< 335), (0x17adc3 <<< 326)),
  ((0x18c902cb004f70175401 <<< 268), (0x5e4f38eaae05028013 <<< 281), (0xc40056ca081080205 <<< 278)),
  ((0x44e1512c8a01440141 <<< 281), (0x2e04b195b80645001 <<< 285), (0x5324080a420a1 <<< 301)),
  ((0x6883 <<< 336), (0xcc7 <<< 340), (0x1bbd <<< 337)),
  (unpack 0xf078f2487e9003b5d80190c0, unpack 0x7605c02d7ec017b97fac00d40, (0x72a0040a845400401 <<< 279))]

private def t23 : Array TensorRankColumnReduction.Packed := #[
  ((0x98a052ba5c2790007 <<< 284), (0xcd49329c94122403 <<< 288), (0x3803020a01400807 <<< 285)),
  ((0x48c1a124040a45005040041 <<< 261), (0x68a258414009100055 <<< 281), unpack 0x28fff88f75c06f2b50000),
  ((0x4fe3057 <<< 322), (0x9880253 <<< 323), (0x7d9d881 <<< 325)),
  (0, 0, 0),
  ((0xe32611a72c10df01e380041001 <<< 248), (0x88309050180565020480001 <<< 260), (0x571b8ef24072e00845007 <<< 266)),
  (unpack 0x1c25dc8fcb84157fb72db28000, (0x2621a067e009040055 <<< 279), (0x105c12303104c040450005 <<< 267)),
  (0, 0, 0),
  ((0x704978a6c009 <<< 305), (0x323b0000681 <<< 307), (0x2cc94cb26303 <<< 306)),
  (unpack 0x9071e423dc81c980f76774e152000, unpack 0x20cbc06078a1a717d003a308000, unpack 0x1107b987efb808ff401d4603da04000),
  (unpack 0x14337f98c7843af5401fdb655a000, unpack 0xa02de0613d90b3c8bb965041e514000, unpack 0xc6e5dc3cbdc0a7f6a003aa04000)]

private def tables : Array (Array TensorRankColumnReduction.Packed) := #[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23]

def rowCoeffs (j : BaseCols (Fin 9) (Fin 8) (Fin 9) (Fin 27)) : TensorRankColumnReduction.Packed :=
  let q := (baseCols 9 8 9 27 j).val
  ((tables[q/16]?.getD #[])[q%16]?).getD (0,0,0)

private def checkAt (r : ℕ) : Bool := seven.test
  (rowProduct seven a b c ai bi ci rowCoeffs ((baseRows 9 8).symm (Fin.ofNat 352 r))) r

private def w8 : RowWindow checkAt 8 := nextWindow (start checkAt) 8 (by decide +kernel)
private def w16 : RowWindow checkAt 16 := nextWindow w8 8 (by decide +kernel)
private def w24 : RowWindow checkAt 24 := nextWindow w16 8 (by decide +kernel)
private def w32 : RowWindow checkAt 32 := nextWindow w24 8 (by decide +kernel)
private def w40 : RowWindow checkAt 40 := nextWindow w32 8 (by decide +kernel)
private def w48 : RowWindow checkAt 48 := nextWindow w40 8 (by decide +kernel)
private def w56 : RowWindow checkAt 56 := nextWindow w48 8 (by decide +kernel)
private def w64 : RowWindow checkAt 64 := nextWindow w56 8 (by decide +kernel)
private def w72 : RowWindow checkAt 72 := nextWindow w64 8 (by decide +kernel)
private def w80 : RowWindow checkAt 80 := nextWindow w72 8 (by decide +kernel)
private def w88 : RowWindow checkAt 88 := nextWindow w80 8 (by decide +kernel)
private def w96 : RowWindow checkAt 96 := nextWindow w88 8 (by decide +kernel)
private def w104 : RowWindow checkAt 104 := nextWindow w96 8 (by decide +kernel)
private def w112 : RowWindow checkAt 112 := nextWindow w104 8 (by decide +kernel)
private def w120 : RowWindow checkAt 120 := nextWindow w112 8 (by decide +kernel)
private def w128 : RowWindow checkAt 128 := nextWindow w120 8 (by decide +kernel)
private def w136 : RowWindow checkAt 136 := nextWindow w128 8 (by decide +kernel)
private def w144 : RowWindow checkAt 144 := nextWindow w136 8 (by decide +kernel)
private def w152 : RowWindow checkAt 152 := nextWindow w144 8 (by decide +kernel)
private def w160 : RowWindow checkAt 160 := nextWindow w152 8 (by decide +kernel)
private def w168 : RowWindow checkAt 168 := nextWindow w160 8 (by decide +kernel)
private def w176 : RowWindow checkAt 176 := nextWindow w168 8 (by decide +kernel)
private def w184 : RowWindow checkAt 184 := nextWindow w176 8 (by decide +kernel)
private def w192 : RowWindow checkAt 192 := nextWindow w184 8 (by decide +kernel)
private def w200 : RowWindow checkAt 200 := nextWindow w192 8 (by decide +kernel)
private def w208 : RowWindow checkAt 208 := nextWindow w200 8 (by decide +kernel)
private def w216 : RowWindow checkAt 216 := nextWindow w208 8 (by decide +kernel)
private def w224 : RowWindow checkAt 224 := nextWindow w216 8 (by decide +kernel)
private def w232 : RowWindow checkAt 232 := nextWindow w224 8 (by decide +kernel)
private def w240 : RowWindow checkAt 240 := nextWindow w232 8 (by decide +kernel)
private def w248 : RowWindow checkAt 248 := nextWindow w240 8 (by decide +kernel)
private def w256 : RowWindow checkAt 256 := nextWindow w248 8 (by decide +kernel)
private def w264 : RowWindow checkAt 264 := nextWindow w256 8 (by decide +kernel)
private def w272 : RowWindow checkAt 272 := nextWindow w264 8 (by decide +kernel)
private def w280 : RowWindow checkAt 280 := nextWindow w272 8 (by decide +kernel)
private def w288 : RowWindow checkAt 288 := nextWindow w280 8 (by decide +kernel)
private def w296 : RowWindow checkAt 296 := nextWindow w288 8 (by decide +kernel)
private def w304 : RowWindow checkAt 304 := nextWindow w296 8 (by decide +kernel)
private def w312 : RowWindow checkAt 312 := nextWindow w304 8 (by decide +kernel)
private def w320 : RowWindow checkAt 320 := nextWindow w312 8 (by decide +kernel)
private def w328 : RowWindow checkAt 328 := nextWindow w320 8 (by decide +kernel)
private def w336 : RowWindow checkAt 336 := nextWindow w328 8 (by decide +kernel)
private def w344 : RowWindow checkAt 344 := nextWindow w336 8 (by decide +kernel)
private def w352 : RowWindow checkAt 352 := nextWindow w344 8 (by decide +kernel)

lemma spans : Base 9 8 9 27 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply certified seven (baseRows 9 8) a b c ai bi ci rowCoeffs
  intro i
  have h := w352.verified i.val i.isLt
  have he : Fin.ofNat 352 i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simpa only [checkAt,he] using h

end TensorRankThreeFactor.Base10

namespace TensorRankThreeFactor.Base13

open TensorRankThreeFactor.FastBase

def a (t : Fin 12) (i : Side (Fin 12)) : ℕ := fromTable #[0x11, 0x101, 0x1001, 0x10001, 0x100001, 0x1000001, 0x10000001, 0x100000001, 0x1000000001, 0x10000000001, 0x100000000001, 0x1000000000001] t (finSumFinEquiv i)
def b (t : Fin 12) (i : Side (Fin 12)) : ℕ := fromTable #[0x11, 0x101, 0x1001, 0x10001, 0x100001, 0x1000001, 0x10000001, 0x100000001, 0x1000000001, 0x10000000001, 0x100000000001, 0x1000000000001] t (finSumFinEquiv i)
def c (t : Fin 12) (i : Depth (Fin 11)) : ℕ := fromTable #[0x101, 0x1011, 0x10010, 0x100001, 0x1000011, 0x10000010, 0x100000001, 0x1000000011, 0x10000000010, 0x100000000001, 0x1000000000011, 0x1111111111110] t (finSumFinEquiv i)
def ai : Fin 48 → Fin 12 → ℕ := fromTable #[0x110110011100, 0x100011100010, 0x101101101000, 0x1011000011, 0x101100010010, 0x111111111, 0x111010110, 0x11001101111, 0x110010101100, 0x101000100100, 0x11011010000, 0x1001001010, 0x111100011000, 0x11100100000, 0x111101000011, 0x10001111110, 0x1101111000, 0x11000110, 0x11010101, 0x10011010, 0x100100100000, 0x1001101001, 0x10001010111, 0x1001101100, 0x110011111110, 0x100010100110, 0x111010100000, 0x111110010, 0x100100011001, 0x11000101110, 0x101101100110, 0x100001100100, 0x10001001100, 0x101010000001, 0x1001000011, 0x100001000101, 0x100000100001, 0x110010001, 0x11110100, 0x10100111101, 0x100011000010, 0x1100110110, 0x111100111000, 0x10110111011, 0x101011000000, 0x100110001100, 0x101101110011, 0x1001011000]
def bi : Fin 48 → Fin 12 → ℕ := fromTable #[0x100111001001, 0x11000001100, 0x110101001011, 0x11010000100, 0x100100010010, 0x11010100111, 0x101100000100, 0x111101, 0x1010, 0x110111110100, 0x111001000100, 0x10100100100, 0x111100001001, 0x10110000100, 0x1111000, 0x11101000010, 0x111010000000, 0x110101111101, 0x100011001010, 0x1100000010, 0x110011011111, 0x111100011001, 0x110001111, 0x11001110110, 0x1100000011, 0x10110101111, 0x1000000100, 0x100001100, 0x100011111010, 0x110101101, 0x10000011011, 0x11001010100, 0x11010000011, 0x1111110, 0x110100010111, 0x110111100101, 0x111000001000, 0x111000110110, 0x10010100001, 0x11010110111, 0x11011011100, 0x110011010111, 0x100101100, 0x100111011010, 0x1010000000, 0x111010100, 0x111110000010, 0x101010010001]
def ci : Fin 48 → Fin 11 → ℕ := fromTable #[0x10100101000, 0x11000101000, 0x1101110101, 0x1000111, 0x1000001, 0x1011000110, 0x1001000110, 0x10000010010, 0x11001100110, 0x1010100101, 0x10011110001, 0x1101001001, 0x101010110, 0x10011110100, 0x11001100100, 0x100, 0x10110011110, 0x101001010, 0x11111010, 0x11101001001, 0x1010010110, 0x1000110000, 0x10000110100, 0x10001011011, 0x10100111101, 0x11100001110, 0x10000101010, 0x10101000010, 0x1111100110, 0x11100010, 0x1111011000, 0x10101011001, 0x10010110011, 0x10001111100, 0x100110100, 0x11000010100, 0x10000, 0x111010010, 0x10000001, 0x11110010100, 0x11010010100, 0x1110100011, 0x10111110100, 0x1101110, 0x1101000001, 0x10010011110, 0x1011101110, 0x10010110110]

private def unpack := unpack16 39


private def t0 : Array ℕ := #[
  unpack 0x17d3b7784c27dd40e74d9d002798ae70098f80c8823aa3128856000001,
  unpack 0x33c0fd88d7ec1ce982bd2017dc6e705b0f2801f0d4baa3c40453a5622b65e2c03a57a0b400,
  unpack 0xa80dfc94bef23389bdf081cfe711c10abec00fad10e03587695e4c219800,
  unpack 0xc9c93d7188ef9601c019bf0b5fd0e03b1d6007e6a47547892ab880ac3bb3a712472b000,
  unpack 0x306d309c03d3b08474d4af86dde73803d7d001e0e21c0114ed401212000,
  unpack 0x62d52bb822c791d8e2185c12788e0bc1f6007c7a57001a3ad35b8da0238250fa000,
  unpack 0x64e94ffc0167da88e03b3f85aeec705d8f96fb46bb3b8cd5cb1c021dd9d3892c4000,
  unpack 0x1061bd1ef3d3a92873793e9019d2c13804dfcc01e3e61d88086d52de6e5d8000,
  unpack 0x1ae2d5dfd113efca77740e9025cbb53806976800f1611d51e24a6e20231cd54b402870000,
  unpack 0x37a0b67c07be3281cd5d3840cf1ba4f0cd4007f504754625344055c1a0000,
  unpack 0x9eed0f1b47dd553849873011f0db1c02cfa400f5300e035a9aece41f20000,
  unpack 0x10d55c67abd118732ade8025c1f23b23040d63aa3c49588340733b6c0000,
  unpack 0x436249fe801b9388739eae8017d4a67823871c01e5c85d51d430114e94d1b00746a180000,
  0,
  unpack 0xd1d56e326fff603bfdaf000de2da9c13ebd03e30ae008a7188ad978b20e000035,
  unpack 0xc18675f8982e9b91cc53bf033158e0095f400398834876000052]

private def t1 : Array ℕ := #[
  unpack 0x475f53cc4ffd58cea63fc6067be2c7046affcc0163aa3c495880aa39880012ec,
  unpack 0x13e05e1e156fe50072e49eb011efb1380a8fc001e12b5d8808a7000001918,
  unpack 0x81bdaf748a0f7799d28ef84097d8c0e0855fadd78870d5a62d001c00018b0,
  unpack 0x84fa783d475f7f08e163dc20779b6470560fb003e3d23aa3c4d5cb1c011cc400020,
  unpack 0x13e69f1f0333904271b9fe2039e7b1380f879401fd8c000006a0,
  unpack 0xd70a29eeb97f2b039402f401ae1a01e95e200b1d51894dc404639aece90400a40,
  unpack 0x1ef8797e940fbe6271dd4ea015fb82380a579001e40b1d51e24a0015734c400e80,
  unpack 0x427c917fd00bcca876470e803bff21380bdf4d2876201aece90401100,
  unpack 0x57b88072c66ebf21d1a1f800df2458e08d5ff9802c7547892b10680e6988017d00,
  unpack 0x6face57c527f5f09c232b880efc750f0f032058ea8c4a683803800ec600,
  0,
  unpack 0xcf8052f9a57ff903bbd170806e00309b2000005,
  unpack 0xde74d9d348fc584742abe1017e756382f875401e34a5d51e20229d2b101b2f1401c0000793,
  unpack 0x1ae8165f35b78a6077392e101de1013aa39800eec81c065300210004d,
  unpack 0x2ddb3f89f3f3239d2143a00a76200e00c7ed3a0ae005413d3365a8000151,
  unpack 0x1ee3f07d569b8706770f0f64d4d53807175001ea821c0114e1aca61411c0000255]

private def t2 : Array ℕ := #[
  unpack 0x68980fa862f10b9c6df7a40df35cce0367e6003bc0575476b2194ccb502100359,
  unpack 0x1df17c7f1137c1ec75bd5e86e18338005f58ad754796d900405f46c000045d,
  unpack 0x12e9dfd51cf8ba271cace100bfe36380a4f5401fe825d51894d0a017f40000561,
  unpack 0x5f3600fab53cc2639bb272061609c104bcc00faf40e00544380000665,
  unpack 0x13f3a01d111798c472e28e40cd933805c7fc6a601c0022af340000769,
  unpack 0x27c7d8bb8e77129ce5acdc6037fe2c70061e0a3a075476b23104e0e65a800086d,
  unpack 0xb75c79fdb7bd7c53906b7481afb699c13e7cc00fb00ae03199acb502100971,
  unpack 0x8ecceb3dfc43439de870a90f8ab9c04afe36aa1d818604782406c0c00000,
  unpack 0x5ff831f0a75d41139fb9f5803e0010a57a0c400,
  unpack 0x5a9e4f1d65f9053a212f4807e1917d01ebe400f63d0ea8c0d038808f04002fd01078ccaf4132800,
  unpack 0x2ffbcbb8ceaf2900e153bcc5b78270508fb003c33438028fc42a1d019000,
  unpack 0xc9eded7e8fbfbd81df617a40cf9cd4e20fc18c687456ec1d400b36000,
  unpack 0xffb2aeebd3beba53970bf4a96ef499c15cbe800fe0d0ea8c0d03b2b019004000,
  unpack 0x17e1771f7097a76873449e9023d702382a179800e1db5d01febb5eb1d8eb7199d4000,
  unpack 0x16e466ff63f3cd6e70c38e301dfd07382e97e50cc3b10a46657b48000,
  unpack 0x85bd25f2870fb481c7a1f8c067f753e8153ca007f2e870051e00eb71fbb0000]

private def t3 : Array ℕ := #[
  unpack 0x10b8dfaf02d3dbc63850ff4a8ce3569e11e800f0358ea8fdb5eb519220000,
  unpack 0x2bcffa380557e9d0eb573e6053864a7044bf88a80762e8227d19140000,
  unpack 0x272dabd8f77b4a4e0dc9c0037a5ae70462ffcdab23801c7c403b3e40000,
  unpack 0x21b8dd2ff181c7e33aa5ff5295f1babc01c3f53545ae0093e1403808a705f480f94d680000,
  0,
  (0xf1570a8395d <<< 569),
  unpack 0x2b3cd73fcaf3581c8d63ad4973e43e83f5d600790e575462681c10be400000,
  (0xc27e158ee8e803557a00c458002f1 <<< 497),
  unpack 0xc1d4bdfd8b1eaa39c98d3f2071038e82000000,
  (0x5158721caa9520bc296a354b4000094002b36800c04d <<< 438),
  unpack 0x101d1d1fc4cffc919db557a8017098ce0a21fc1e54475378daf58ec00000,
  unpack 0xb7e6cce6341d2653a3217180deb4a1c1483a800fd40a400000,
  (0x42b3f5f2fec4210ba10055825d <<< 510),
  unpack 0x14a42bb8f2f7dccecaf3c2a03dcca705daea003f2a23a9bc6d7ad400000,
  unpack 0x203c684f0bbdd3833ac0f74806f3291c07c3fdbb150e3a089f400000,
  0]

private def t4 : Array ℕ := #[
  unpack 0xe71f31e0397cf633a8ad70297fef29c1383d83ad10e0317e901ee98010fa00,
  unpack 0x17c63efdcb3fa848ed931d4057e1687014afca10d7622023c1203607ec3b00000,
  0,
  unpack 0x42ed473f294749c4eb9cff8003b9e870552f60fb1b10690ec0000c7d,
  unpack 0x1ff7301d6d5f99e4703c1eb02bf4f0fa021f9801ffb91c016789a071011e08005fa020f00000d06,
  unpack 0x41e2fa91af6a81d5997a404f501ce0a45ff1a7ec70069e1091e0910015e001d00e16,
  unpack 0x60d68afd68b76484e4967c007bd18470033fee24876078dbb07d1be80000f26,
  unpack 0x578aa375e5fef2b9d479bf636bc0e0177c1e040ea8c0d03ba150000009a,
  unpack 0x306ae73ea2f3e22c76b3fe901fd4053a1b5001e1fa5d4d86247bd08ba7000002a2,
  unpack 0xffca34e0179d077387d0ff014e2b01c0563fbd4a1c0683147000004aa,
  unpack 0x15f9a51e3507866a7115dea025fe55fa0b0fb56a2bb17465b000006b2,
  unpack 0x9f9619fab17c1f23952f7081be6f89c16e3f832acaec0f11891ef481a4807000008ba,
  unpack 0x2be0abffa17fc41ce843fc4057edea705f1f60d586bb035a0fa4af00700000ac2,
  unpack 0x253ac7ba8b73440e5fa1f11cd66700b3fa001e4b4b8034f3a0a00000cca,
  0,
  unpack 0xc1f1d67f8b8f21b9d12838004130558ecd20f51d400]

private def t5 : Array ℕ := #[
  unpack 0xfeb08fc437f8f467590be3011cbd6380d87e5886bb11011e0910015e0240b4800,
  unpack 0x6f9a7af09c9f8d81dd663a00eff59cf4cc16c1aec0f29888870c5470431ec0f09802c774247bb000,
  unpack 0x19fa99bc054b982a730ecf68e1143c23fb62a15d10848fa07ae219624a5081ae000,
  unpack 0x10b5273e0807edd53b948f080beee11c16ab8385a1d488b8762a803c0153d43a596248080ff2000,
  unpack 0x6efeff352ffd299d7ed7f63b7dce0a05ed75c2e0063e90038888703c86bb3a44aad001c000,
  unpack 0x1be5c89d82479f2071a1be201ff5a5382d97ec6cff5d51d2ed384c22a752434038000,
  unpack 0x3b925df81bafcf81cc5ebac057b490e09d7dc003d5ed70061f4b9ba460f782540d070000,
  unpack 0x5b98c37b111e3581c9377a803f566ce0077edfbc0ec0e5003a91050e02a0000,
  unpack 0x9fea99e98e7fd263948dfc813e2239c072bf032dc8e08887420d76744c0000,
  unpack 0x62ea85b903e720f8e312bd205bf48a701fbf2003c4b039b94c4463d20b81c1af40000,
  unpack 0x57a15e7e02aecab9c16db8006fa7d9e03f5d3007ae4470079f2201c4213d394c23880000,
  (0x28bed997357d01ae3d6045773011ea6002520801c4500044400000400010440104401001 <<< 326),
  unpack 0x42658a7c115bcfee7677ee3017d426382497cb79e95c0413a66000039,
  unpack 0x1de3831d369be64071953e803bcb37382a5ffc7b615d818624782440057800005a,
  unpack 0xb7f35beaae3d33339628f5812f16b1c0663da9d21c01c7808a8e0000084,
  unpack 0x41c6fb7ad3de9599cc3dfa40f72d10e0323e6007ebed7443123e81b100000a8]

private def t6 : Array ℕ := #[
  unpack 0x24a09bfa8dfda54ea4b3d4073cfe6705c2fc0e3f0ba91110ec55007802a7a874801d02930,
  unpack 0x17dc54b90d87ec94efaebd407bc3207046bf9003e4e43a1bca62221c0f21a6e3250027d0,
  unpack 0x86d4c4fb2397aad0e43ddd002b924c701e8e9003d0243aa3ca6a709834dc64a1d0fc60,
  unpack 0x1bdd93fd858fad8ced16fd4057b28078360e6ed754749b48c1ef0665d400c40,
  unpack 0x106c3de1171694ebde7c204b9f4270509f2003d9e438024fa5488287065a80e9280,
  unpack 0x7395f37c54ee5f01d3353800afa494e0bc5ff1b10d7622221d082500e9900,
  unpack 0x1fefeb9c923fe1ce76e5beb029d3e2382c479001f1f81d51d22231e905c0e0ccba80e9a00,
  unpack 0x3b9e087395bf4a21c4f2ba40aff484e00a5c102daea8f2988887a7299acb6665d400400,
  unpack 0x1fdc977d4737c9ccec16bc2053afc470160f60eb44384bb2debab00000,
  0,
  unpack 0x77da33f9a9fd3943a093f100be4ca1c1623e5b3418ea8f1256202a0e000062,
  unpack 0xee8089cc77bc328726d0e303dc8f538230fc0620a1d88074021014ea,
  unpack 0x3270cf5e51cfaba875e63e9007feb73805dfec7ca91c0187e204547065a80016f2,
  unpack 0x9944df8275f8233877375809e1481c1167e000f3898e0071f134b978fb2ba00018fa,
  unpack 0xc5be73f5403ff1b1c031b8808f699ce0a23fc1ffa4754600cb502101a0c,
  unpack 0x183d935fd823db173b929f581ce9b31c102b8c00fe888e8803a0001c2c]

private def t7 : Array ℕ := #[
  unpack 0x105eb947ddf2f41a1de203ac0b7f2d0e0135e2007be6c70038e341405f6d86988001e4c,
  unpack 0xbe52a7c336bc30072e3feb013e53638258feb75601c341051c00000134,
  unpack 0x7f1d0ffa3bfd4e07130ee8037f522380707d801fbc11d1006988000544,
  unpack 0xc993e4fa16cede19dd4bfac09f3d94ea6e4007bc6070051f880555c1acb718000954,
  unpack 0x3dcd513f2a3f42d4e5567d607be74e7016bfa003d7f438028f1a741d9b502100d64,
  unpack 0x5fe44afec4fe0639c52aba00e72504e0867fedf86d76078da6b65800000,
  unpack 0x41d939771cff5019cd8f3a80c7cf9ce0237f0184ad7004538681611c00b401c00,
  unpack 0xe788bcff251f4d63943cf401bffe91c04cbec00f5bd8ea6f1b760fa37d02402c03800,
  unpack 0x7f8a7a7994ee4699c2b7f8c0a79f58e08f5e2007a76870051e340a20f8fb28dd021000,
  unpack 0x8a3e37b9ddffa91d1997a00bf8104e0b27ff9a525747118084fb041fa834122a000,
  unpack 0x64ce9e3deedf9754ebe4fc001faa6870508eb003dbf03820d1d95da62d011d9024000,
  unpack 0x20b66bffc20fd8c13b5f171807fafa9c13cbec007a2c2ea0f53402a3fdb2808f86e96010ecb7199f4000,
  unpack 0x2dd80dbbc1afe74cefe45c4033ab6870552fc0f8883966e5d821b642458038000,
  unpack 0xc5a11af9843eda89dcb37800afa294eaf40074c18e00d3f11a396c0d75b8e50000,
  unpack 0xde4261dd33fcbb15e4e1033f5ec380f1fd801ec211c00e385401c0320000,
  unpack 0x7b8e3f735fbf8301d5ab7c80674fc4e03d7ed851aec4035d340000]

private def t8 : Array ℕ := #[
  unpack 0x1df3d79d1317fa94775b7e0027fb2638229f9800eb331d4de23188ffe80030780000,
  unpack 0x137f7fc867e167384ccf180bf5d23c12e3ee007bd12e00d3c1443808b7023a80000,
  0,
  unpack 0xd7175f4329dce739e07f4016fe501c14c3820e21c0114e1a5cb00000,
  unpack 0x9fae22e2365d2f2397897101fe8f21c1507fdbca6c0d6ec1f46fa00000,
  unpack 0x5bb779f1009ef299dbb73880c7d480e03e5fd8e18e0071f134b978fb26cc400094,
  unpack 0x2429f7f81371090eba4fd405fc2ac70133eb003cc58028f442427d824f6cb00000c8,
  unpack 0xee243fee457d94676170e001ddbc23826579001e4035cc36caed316800e0000d0,
  unpack 0x20e3a9fa0a3fe244ea64dec9c86c70172fec70c70038e3402a3fdb2808f86e96008eeb100060f90,
  unpack 0x426c561e80f385ae77875e3019d2a038011fec7c9a1d8d9b9760680001db60,
  unpack 0xd4162eaa7dd0323a27bf5019edd91c1583ec00f8f4ae451cb606a50004a01c0,
  unpack 0x281237fc99f7fa9d5917840f74e50e08c1f6007b08470038e15007018800128380,
  unpack 0x2d65fe183f047386c87480febb01c0507c800faf40e0076500004a700,
  unpack 0x109a34af2d3ae31a9c2b2fa40679d44e09f1e6003accc753788c623ffa06a5c402200,
  unpack 0xfff5f3c26e7c10473600eb005ea94380e579001e40b5d88c50d65b352801400,
  0]

private def t9 : Array ℕ := #[
  unpack 0x21b19e0fb871d0f039e4a75016f1091c028fec00f119ae0cc0f458800000,
  0,
  unpack 0x778ecdf21bdc904380b27581eee8a1c1287e4007d158ea6c1329c10002101da4,
  unpack 0x217f5fdde5c7a36472cf8e8025ee66380857cb6f695d4d84617d03621acb1250021b4,
  unpack 0x161257a6767c798eedf7c005feda670561f1003c796ba388c0077d820f03400025c4,
  unpack 0x17c3d93f802fc444e83f3d602fab2870171ff6e620baa3cb622a9d9018928c20721029d4,
  unpack 0x1129e8f0a59df87392737e5126382797d801e5235d0de5b11c5e02a1c0cb125002de4,
  unpack 0x136961cc7fb84ee77f31e101be5a67ec9c070038f8848a701acb1250031f4,
  unpack 0x15eb9f3da71be50c74716eb019fa25382f9f5800f3db1c8278800003418,
  unpack 0x8871b719b9e3709c1357ac077dd48e03e1ed9092e884653aa8070340003858,
  unpack 0x3f9b9ea1cfaba672d86e103bcfa23826875001e7385cd1810e02b9f800381acb125003c98,
  unpack 0x5fd986f61b7ef401db223840a71114e00d5f2007dd0d70038e1191fc819624a2100268,
  (0x83a2ab06af34e28960941b4020015c00034a900180c001800003 <<< 405),
  unpack 0x26f3fd854f3ed8e18e3d4017800c7a1a57a0a800,
  unpack 0x43747c9fc8affc6e73d99e8031f9513827175801e0395d5189a070546a57a18800,
  unpack 0x10b3aabf4a6ffb22384077180ef6301c00abcc0078d48ea8f10a866907cb000]

private def t10 : Array ℕ := #[
  unpack 0x6af5f229fe29438cc1f1011f8131c124be5bcf0ae62cea63c9892e2000,
  unpack 0x7f90aeef1a7fbf438bbaf5a80f0181c10abf5baf10e183076560658906c000,
  unpack 0x7f8c12f3144f8819da0c3a00cf1818e0895c44a5c0163dc007f6618f1b53a9418000,
  unpack 0x831648e49bde395385fbf4018e0039c16cbec00fff3ae0c04eecc31e36a978fba8000,
  unpack 0x43706b7d06c3a9e473cf6eb02dec95382ed7d06dd21c7404bb8e90000,
  unpack 0x27e0de7e0c3f1440ecc8fd2a43f7b47055bf8bbe875373041c032d760000,
  unpack 0x27cebab9efb78c84ea273f601f840e7009af1003f430baa31580ec863c6d9440000,
  unpack 0x1fe491dd9f6fc2fe74b1eea023fdd8255feb6b3b1d51e5b00280000,
  unpack 0x1cf7b93e27cb994872f5de0525e3717802df0c01f9111d0dc3f279114ec8ae53437c80000,
  0,
  (0x337acf175b1f602f2860608710064860033d280000000001 <<< 422),
  unpack 0x64da50bede7f1994efafbd0047d186705f2fa003f8343aa31340ee85400000,
  (0x3ec9b14c37964323e280354ea02446c00d4c0001 <<< 453),
  (0x29977726ebd22082150016e50012c90003190000404000410001 <<< 406),
  0,
  (0x1e3ec0d20b19b846aa300a0cb002c520008d2000200001 <<< 431)]

private def t11 : Array ℕ := #[
  (0x1254b83243c0507498005a4e4013804000000000c0101 <<< 434),
  0,
  (0xa738478a0bae612fba5429a68009d0c00d4c00008001 <<< 437),
  (0x30015193245d2863e0100f5ba00a042000400000602b <<< 439),
  (0x9da7e7 <<< 585),
  unpack 0x12f337eb30fc5267400ae1527fbf5382a971801f1e95d51857279080ec8d56e980104c00,
  0,
  (0xa045e21a24f11d4996038dd2015e26002bc4000000001820001c440005 <<< 378),
  unpack 0xdbe9f4076ee289c927ff80b7d6c8e01f5f01e608754335698b400700000,
  unpack 0x81f009f36d4fcf31d4b8ba540ffe9ce02f5ec1b86575460c81c00021022e8,
  unpack 0x3261315c8773d0a473a28e42ec8338069fb4204bb218888762a803c0153d43a36cb1250e8108,
  unpack 0xcf9309fe34ffe143a64375814fed11dd5ff3938ae1500f86d95da62d001c0003328,
  unpack 0x306093bcb33beeac71466e1537e831380b9fe06cba5c2a01f71b2b0002103b48,
  unpack 0x213ef65ea1c5f5173ae6674013febb1c052fff3a712e1501e8321d01b81802a7a8746d9624a1d04368,
  unpack 0x7fe598fe01fe374398487e811ed811c0267f3cb85c020df501acb125004b88,
  unpack 0x91197ec8bbe7d13bdce75801e4f31c03a7e400f31c8e1518e0000053a8]

private def t12 : Array ℕ := #[
  unpack 0xd317e4317f6423946275812f2cc1467c400fdd08e0559e000005bc8,
  unpack 0xaf7feae694dd92438774f501fe3c11dd1e40076740e105ee01acb1250063e8,
  unpack 0x4d1b7063aec939da637e239b14e0861ff9b94c75462e01c0359624a2106830,
  (0x1d52d661b2eb7156d560192d2000ae20004c6804003001 <<< 430),
  unpack 0x1fc03bbe81efc098ef7a7d600f8002068a01d2bd04066801c00,
  unpack 0xd72138f808fdc373bdadf180fffab9c05cbe0394d2ea6c3123de845d38d4af40da03800,
  unpack 0x10b15d2e2355ed133b54bf001bfce01c070fec0075e50ea6f10a8669003687000,
  unpack 0x427e9abce627e534707e103fd9433d23fb62a15d10848f0150fa98f2cb125746000,
  unpack 0x6bb9fd74094e72b9ce147ac0efd25ce0aa1f4003c04870283e1d01b81802a7a8746c00621c000,
  unpack 0x84fd8e784ddfc09ceb803d607be6e8704faff8d5c63d42472c00f32a1de0f9c778f2cd388018b8000,
  unpack 0xbc00bdf73f930876370f84ec423a8bc801fe055c10c38c027669c26a71e52ee3f5a0038000,
  unpack 0x24f7d7e4e5746d0e16a9c202fb48e700ccfe003f47639e8c71d05f2329c15078802f0416838082f34d6d0000,
  unpack 0x213cc44e034beb733a184f4013e2ac9c029fac007509afd8c0001b4e0000,
  unpack 0x1fc0f57c6601b1d4e23cc007c150e0279e20079b6df54796d90c78db20c41c0000,
  unpack 0x1aed73bf042f8e56770b9f66e4c0380b77cb72339c00e3e201c980000,
  unpack 0xc1ea4c71830e1a99c658f880e7f5c9e03b5d3003b142fc038e01e80000]

private def t13 : Array ℕ := #[
  0,
  unpack 0xd7c540e1399e5d33a58f75004f89b9c1523e5b8d4ae320200be900000,
  unpack 0x1390f9f028bd52873ab4eb033feb2380edfd001f3601c1091ef422e9c00000,
  0,
  (0xa31f008973bd800f150146d4c01cb0000e2ca0010100018d1015 <<< 404),
  unpack 0x17eefeddb10f87e8743a9e2019d583382d579801e4185d51d834190e80dc0c0153d43a400e8150,
  unpack 0x2fb8d4fd5caf0b99cde67880573d4cf0ae6007e8c47a920f6ec887783e71d8d3719280120,
  unpack 0x19edcd7d777bee4474747e003bcd67380707b068115e9c26a709a91a6e3250e87a0,
  unpack 0x3272381fb64bf5287395ae3033dce4382fe7062c6b9e9070d05f2329c15078802f0416838082f3a0012401c0,
  unpack 0xd76d09f0ba3fd8038ffa7580efa509c11dbb346ba8107b4034000490380,
  unpack 0x1fe0667c1257e9e8718ffe89bc870584fc0fcc27aa3b403a000124700,
  unpack 0x1acc99f0463e32e701c1e8017cf51380527c801f65b9d51da00000049e00,
  unpack 0x17c60278a4b7b988edf2fc005fed027a4760d0a57e01871d00e0229c3596cd000006ffd600,
  (0x3b7724935331180fd2103ab8a803b4a002499001003000600000d <<< 403),
  0,
  unpack 0x27ec80bbc3d70150ea25bf15540e0905c1bb08ea8f13572c7000700000]

private def t14 : Array ℕ := #[
  unpack 0x15e7479c042ba28474064ea01dc1b4382d57f066f31d4dad7ac76002101510,
  (0xbb5be2740bd61cef4606d704006c22000cc6000205000444000000005 <<< 382),
  unpack 0x21b88eff1165d17739a15fb465521c1783e8007d5d8e0071c680547fb65011f0dd3dadd000190,
  unpack 0x1ce684bf006fdc6673707e302fcc943bb9003e41639e80cb5021045d0,
  unpack 0x1cfad59ef5f382a471e9be82c6973b2366057a830f94e6443bc1f38ec65a8005610,
  unpack 0x2dfdcf4d7bf0989d3ffba406f78c4e03b3f81cea8702a0f6dc0077672940477374faecc25006650,
  unpack 0xb792cfef225e4523babb7181de5681c05abf5b949ae5021c000007690,
  unpack 0x15ff8fbc072fce8074167ea015e266380c575801fbc11d10069880086d0,
  unpack 0x3dc50fb9089f0b54e0fc1d6053878a70433f9001e004bd5007003525009710,
  unpack 0x80d13878e647ba44ef2efd201fd6a47016bfc0ef143fa3c4034dc64a210a750,
  0,
  unpack 0xc9c615fc5e3ffe21cb56fac0a74194e01e1f5003b82c754625342fc34af405e400,
  unpack 0x17c677c6d9f6a5ce5475d6023c26c701c0eb001e3443800c51f5332bc98256003800,
  unpack 0x296d7dc34be966721fbe1025c7833bb2003e56268280b9410710d98805b47000,
  unpack 0x86ec203da1d7d0c8e904fc600b8686705fbfb003c2f03b1b5a8359624a5092de000,
  unpack 0x1d969e4863eee13a9d1f427fd91c074be80070501b903070d6a00196ffd6000]

private def t15 : Array ℕ := #[
  unpack 0x2fb90976ce7f4e11da0c3a80cf7104e0895c44a5c0ba3edbb800eece52808ee6e9f46e80025f6801c000,
  unpack 0x9f193bf2bf5fcc738919f5010ef781c1ceba85178d32e0161e89d9b97652436a96800cfe8000,
  unpack 0x88f93fd140ebab1d9a2b8c067c714e0647dc42fa2c07351472dca6e20231ccd38cb6070000,
  unpack 0xff3e2eef253c74039e51fb1773d9c070bcc147ea50f28c344bcc8271a40f62cd12a0e6235cece502dae0000,
  unpack 0xfcd04b9acd72214e531bcc05f9c887051bea003ea34bb106b5340c81c0000,
  unpack 0x18bcef4f8133e12a3b56874811e3429c10c7c3c0f0450e0071c018d80000,
  unpack 0x39e97dfba2bf39c4e45c3f01c92cf0049e8c03fd96b801c7035aa0300000,
  0,
  unpack 0x39d534f826a7b5d0ec029d203fcaea704c3f2801f494baa3129a17d00000,
  unpack 0x7fb9ea799e9f8c89dcb83a401f9b4ce0341fc181c975378da1a0c51c00000,
  (0x22c3372a71ba88771e3010f53800f4b0011ea0005000000010000014045 <<< 379),
  0,
  (0xe1b76ba85858c236d8c00a20002bc0400ee81000002031 <<< 429),
  unpack 0x3176865c64ef8e2a761d4e9039e3c7382dd7fb7cb11c0ac3e5bb800eece52808ee6e9f5d0001a0,
  unpack 0x5b9973fe93bfa911cb56390bf59ce0cf5c028fa8e1700b0e2809ecdcbb291a000040,
  unpack 0xee2fb5c3683b08c76b90eb02fdd47383b17590bf1e25d51a28e5b94dc404639d9d4b0400d40]

private def t16 : Array ℕ := #[
  unpack 0x6fa864f0109ff901c60f3f03ca84e0921f00a3dae8794344bcc8271a40f62c2541c446b9aecb88036980,
  unpack 0x84c07fff46c7af5ceb381c407b9ace705a1ed850ec4035d9d208053b00,
  unpack 0x2169e09fb34ba10e70741ea02dc7e3380797c781f32a1d880698800092e00,
  unpack 0x77aab0760e7e5a21c92afa805ff788e02a5f0807d88570a8070114e1acb600000b7fe600,
  (0x3d5ef039374a20e6b8b02811a008b130078a2401 <<< 455),
  (0x4ca63e2ff8770c8692044a2701301001480681 <<< 458),
  0,
  unpack 0x1af54f9f9153be2476c12e3033f8233d23803f50290000e160,
  unpack 0x3fb2fff3520ea129cfd63f5b4e10e0333e7003ad28754794d4e13000000,
  (0xce0c3c9e83190508c801b0ab00a53b801d82000002000101005 <<< 407),
  unpack 0x10341dee6b7ff0e03be3cf181fe3429c168bae00fd390ea8c50138065a8002a20,
  unpack 0x84b4ff0b3ebd73aa75f5010e5ba9c05e7f53931af492a709a91acb501d04aa0,
  unpack 0x86dbc8fa4c970b18e9fc1c0037ea4670679e0945f944b80587a2766e5d948cb125006b20,
  unpack 0x9fc5c9e12f5f6373ad20f0807e42a1e11c68070000008ba0,
  unpack 0x7fea367140ef8831d52278802f0e40e0097e11179ba070034000ac20,
  unpack 0x2ff02f7f6dcf7c40ecaefd019ae070789f29c3cdd03801a6e32500cca0]

private def t17 : Array ℕ := #[
  unpack 0x16ff349c04fbc5aa711f7e3019f741380f175140edf01c006e32500ed20,
  0,
  unpack 0x5b51ae786ff0263bde9f5803e00211c2004800,
  unpack 0x42cde03d04cfc344e8a49ec1d563f4520ea003f5032d801e800,
  unpack 0x10b389ce60cdcbf03b0b6f181efe0b9c05cbf63e96c4d04147543b3a7124763000,
  unpack 0xff44eefa07bf0263bde9f5803e0238ea004a000,
  unpack 0xe73a76f61a7e877390e374278131c124be5bcf4ae436cac064250cc000,
  unpack 0x84c8957d0b477c84eb777d6057ed4e701c8f6e5e872878f6001c03b3a71254d8000,
  unpack 0x317ae0bc91a7cc887610ae203bd4223aa3c900eff55d8ba0321030000,
  unpack 0x19f7a57c47dffe0673820e002ff0223807077800e7115d8ba0332b50000,
  unpack 0xa2faf4563ff431c7c77ac04fd4ece4325f2dae00737d00520000,
  unpack 0x10ba5ede5871ea92392707d80ee6b3be0423e400f64d8ec403a0d01c0000,
  unpack 0x4e380f61e2f99f9d90b7d9bb7cce0865d6003c1ec762019180000,
  unpack 0x1eda5fb22fd8a73b203722adfe500e8a01c922b940c79518e0219f10828ecb62a21c500000,
  0,
  unpack 0x776769f09e5d6c438cf4f377c33b3e0f64038084600000]

private def t18 : Array ℕ := #[
  unpack 0x5fbed2f8440e3a89cae6ba40df9f9be8af3fedd3cd71d196c00000,
  unpack 0xb710ede3babea553a6e5f4805e92b9c156fe400f0348e88d04147000000,
  unpack 0x57c485fd8a7fc321d8587a1b2d10f0ef81c96d7448e2000000,
  unpack 0xdf7d56e7abff8843d3c6e656382d1fc7b76390d8000000,
  (0x38dab341bf41b849f6000e59880a31900279a45 <<< 459),
  (0x13083ca8c063945b2d1012289c0060c1 <<< 488),
  0,
  (0x8ee3b23540083210240c35841 <<< 509),
  (0x2699d4310d42a06980003a14a3 <<< 511),
  0,
  unpack 0x2fd35b70433e8a29da33fac03f331efc3d7c4407c9897db686c0263e21051cdcb61a21c005400,
  (0xdcc4b88e8d940051d240ef28e07114885 <<< 481),
  (0xa8734bde74c882e88180c9000144a8004c50a05 <<< 456),
  unpack 0x7ff3e37d0ebeec89cb887a40fffc8de0b37f19a08ea8f1253710118e00000,
  unpack 0xcf4bebef0bfd3933a7287180ae9a1dd018bfa00250016f20,
  (0x18425ed0913d0c55bf180385c505295000a1ca0030140000080400183d <<< 384)]

private def t19 : Array ℕ := #[
  unpack 0x9fca4bf298bf6403a5877e460f3bc120be03aa0ae451cb6000000,
  unpack 0x3be4c53e474f2fc4edd69d607799eef00fbea003cb843b100ccba801c2c0,
  unpack 0x2dddf33eac47c690e7ce5d20778600f042ff9001db16b9e9070d05f2329c15078802f0416838082f35d000240,
  unpack 0xf763bdf3023dc6038b5474005ff713c080fac85f5742ea8f11a396e53710118e6a50001340,
  unpack 0xb71e0fe203bff13398dbf481bff50bc03cbfa00250005440,
  unpack 0x6eabe6971e6d639ce671016f5eabd57bfa40273cdae7021c6417c8ce70141e1071c105a0e020bca7418009540,
  unpack 0x3ff528fe0b2c14e078dc1a9d0e9b57fb19a2070035da741800d640,
  unpack 0x6fa91576d88e4339cc213ac09f7d1fe0343c6007a4a876201accba8011740,
  (0x543eab0dfb254640902c7bc401 <<< 508),
  unpack 0x6bded87e46ae3c81dde8b8403700020abe14af400077800,
  unpack 0x40fe01bca81fb3c8e5601c4033d4e470188f80ed34ba9b0c48f7a40d24038d665793040ff5800,
  unpack 0x77166deeac5c713385e2f1003e9529c1347da0e01c01e7e21510d9881a007000,
  unpack 0x84d0c039882f8184e35c1c4073b2867a47f6c542ba2c76aa01f5068240e80e000,
  unpack 0x1019a73fd17ee2989c58cfa0077efd0e0871c600786ed7002cf656034001b5c000,
  unpack 0x2fc301f9073fca04efebbfb1830a701b8ea003f1b6b983d40436cb1000dfe4000,
  unpack 0x109bb47794c0f9421c19bfa402fb294e0ba5f41178eb0700436a96800ffc8000]

private def t20 : Array ℕ := #[
  (0xcad21d4c95a885e89180c19c851bd28040d8238790905919c01410838000105a0010500080000000020016d <<< 264),
  unpack 0x3f072ceb17fda543b9a5f1a0deeb49c8657c800ff012ea083c3083db4c82876a343d00e0000,
  unpack 0x1142f8fc931f5b43a2b9fc11be4893e16d7e000ff5dbe1d80e2321c1849f4680edbfa0000,
  unpack 0x1835dfef0123d0dc3b50cf0c19ff599c129be800feec4e1c00e2231e905c0e0d0076fa001c0000,
  (0xd157682f23b4a26d3a2e9550a7081ea20e0c7b43480fe4808aa200e540000765002a8000b6d <<< 313),
  0,
  unpack 0x62e08a7e03477ac8e7979d600be24e701d8f3003fb1801055e00000,
  (0x19a4ada8e6c2447bf14005e71401c85800c5da00410000189100008000000549 <<< 360),
  0,
  (0xd659e5c27c8c47c52501ac10001918000abd000000000108055 <<< 408),
  (0x1dfa9e1057911c75740810b50000a1d000011800001059 <<< 432),
  0,
  (0x677e4ac2ee62508825004241700085611 <<< 482),
  unpack 0x7656f38d9f51339f537500aeee09d42fbf9383cae7021c2417c8ce70141e1071c105a0e020bcece5d400f40,
  unpack 0x3ffb42784e474110e820dc631bdb067359ffb003f260ba828f1c20f6d320a1da8d65a80e9880,
  unpack 0x7f9465fb84ddc9af1874119f5b9be1253a400f0043e0d80e2321c1849f476500ea500]

private def t21 : Array ℕ := #[
  unpack 0x3f9e67e4157d25739fae74c1fee599c14b3ac0073d1ceba62231e905c0e0ccba80eb200,
  unpack 0x17f6ca5e51fbb944712a4ebb99fcd37f25d75041fee2bda003827e79105ea881c72a39bd941c75439accba8001d1c00,
  (0x98cbaf8c9a6802a3c95672b801c42321 <<< 483),
  0,
  unpack 0x37f2ea3fc5677d90e45a1fe03ff184705b0ff8d1063aa3c494002ae00000,
  unpack 0x18b028ef9887dc86381f17528ff9231c034ba800fca88ea6f1b5eb500021b40,
  (0x26d0b496ef8d80d2818166bc405b81800f3c80059140000000400105 <<< 388),
  (0x209fcbe161aa62e500c088b0e008824009904001c0000000015 <<< 409),
  unpack 0x80eb9fbdc8571d58e1b37c4a73e30070093e7fd8ea8c60838065a802de40,
  (0x196b60d01c35445f70806da0c01d7000190125 <<< 460),
  unpack 0x1dea3c9ef56bf4a67710df7005e4d806174028e77b1e51868979904e3481ec584a83888d73b2800080,
  unpack 0x73b929f3c97f0d89d3af3880e74408e4b41fc1f524744000038580,
  unpack 0xd0dbefc251cfd538953f1a05f4409c87f7c800f20caea083c7083db4c82876a3596e301d3c980,
  unpack 0x77f311e1233e2c3393ee740aeecba9caecfcc90f1fd8f28a9979104e6081e280b8ca838898735d9cba8002680,
  unpack 0x73e96cfbcb6f65a1c6887ad0974794e0053f2df08c747100d65a800a880,
  (0xcc0c5403e93e651c3095 <<< 533)]

private def t22 : Array ℕ := #[
  unpack 0x37a6c2f5031e57b9c4f4ba004f36d4e08b7d4007dd2876218807074110ecd20f4007b800,
  unpack 0x10dcdc276878e5ca1c01a7ac0e7ebdce0391f6007bdec75378dbb07d257803809020ff9800,
  unpack 0x3067c33df7c7c36674f4fe200fe7a2382707b075a21c00aabaa21b75887c007000,
  unpack 0x62d1fa7c25ffc094ed7e5c4037d6e070133f80f3c6b91378003ea63c6d9624a50f00e000,
  unpack 0x7bce2273848f2121ca887d8b1a44e0aa1ec1d7a5702af7656018807c1c000,
  unpack 0x73eefffa592e2199ca0c3a80cf7104e0895c44a1ea827d40076431e5d9d3a800f38000,
  unpack 0x15b823a2f974b5ce4f79c41d7407072be81c1c92ebaa3b5d9863c8d9620017ec0038000,
  unpack 0x33d5bfbe2297c1d0ed05bd6057b8c8f49d1ed001cc06b8028fc5d01d9b41f80070000,
  (0xd3ea3e2fff5442917205df79a1724e4909d0c010c4a994882182045010000195008980004006001001f <<< 281),
  unpack 0x5fdfeff54b0f0d83c624bf8b0409ff0c6007fe35460b01dd98227dc797660bb7c0000,
  unpack 0x33e19f3c831fee7effe73c405fb8ce7a068f01ccc23a23021c623ffb2b10680e003bfdac0000,
  (0x3967a6c1718e2d5978080a5957868949026a22a12643b2025d41002aa00003b2804d40005db <<< 314),
  0,
  unpack 0x3f29f4fca6fc8543a4ca74802efb81c0767fb1a21d8b23110e0e00000,
  unpack 0x37fa327155cf9931d60cb8804f1e54e0173fdd058e00d3f103e92bc01c00000,
  (0x52cdd701cfa4225542007834a028d0c00f14800288000000000000155 <<< 385)]

private def t23 : Array ℕ := #[
  (0xac7410c70f7881dc28403a42e00d8640017c50008000804247 <<< 413),
  (0xba820d48ee0863e15a00e606a021c8c00980000180eaf <<< 433),
  (0x39e54ea94650810ae2c05428e02892c00488955 <<< 457),
  (0xf4fb6cc07a6c3c20840ba9800178247 <<< 485),
  (0x13cd5f114772b87d02100d72929 <<< 507),
  unpack 0x20f550fd209fff00e4577c62ef8ca872b7bfb241e5e23811870d32f2209cc103c5017195071130e765c401a80,
  unpack 0xc9d421f9db0ea7abf3a23a5587aa51f02d3ec1be0875462b01dd044fa3b2802900,
  unpack 0x67f10df64b4f819df2c378c00fa690ecae7e07e048743788c623ffb2b10680e6a5c403a00,
  unpack 0x105ded8714a7fde3fdb5dba50376d4cfc813f5903f3ac7a830e3bd9e040fa82070aa8e6f65070b50e6a50001e1c00,
  0,
  (0x329e8ec2b7fdd573501 <<< 536),
  0,
  unpack 0xafad98e11ddfa9b25971817f3ba1c01af8c00f5c10e3a089f4765002b080,
  unpack 0xbf74cdeb17dc3523b873f481af0339c15a3fe3201aec44443a1000000,
  0,
  unpack 0x1feb4adf44dbde42778e7e003ffe84382e9f9001e60a1c1b01c025c4946103843680]

private def t24 : Array ℕ := #[
  (0x1ea0a95814b5870881806769001dd40001e49 <<< 464),
  0,
  unpack 0x9c70de7397e7663ac047480cf8dbbe17ebfa0025005bc80,
  unpack 0x77bddb73dfcea2a1d640fa486f535df013ff2007ec09f0ec071190e0c24fa359a4101d63e80,
  unpack 0x20693bde559fe100f2118e3027d1967c07871801f4881c1b01dd044fa359a9608068300,
  unpack 0x739cf0f8cd0e4d3bc721be21e39c1747c800faf40e007650070b00,
  0,
  unpack 0xbed477d728f9f6c70c71ea00bc005330118ecd20f400e3800,
  unpack 0x2036fd3f3a43d7073a0a8f1818fc439c178b8014340083000,
  unpack 0x106d971ea207cfe476746e901bcc57382797ec7d2d89a7550ece9076b000,
  unpack 0x21b2ceae404bc60539b97f581be1431c16c3f2bcb5c1085fcea0d31251c00e000,
  unpack 0xaf338de66cff34039761f1812f5b81c0683ec007cf4aea8f25b2b0010ec000,
  unpack 0x3798dfd6ff7609ce5421c81a46a75460c62578031fa8086dd088000,
  unpack 0x206afdff406792ea768a7e3019d933380e875540ea455d8ba029000770000,
  unpack 0x103c1eee21e7fa5738da0f000eeb4adc06c7bc00f86600a3ce80ece50790000,
  unpack 0xafae1eee317ef923942375a1fe5c79c1343e5b73c0e88034cb60000]

private def t25 : Array ℕ := #[
  unpack 0xc5ecc67c816fbe3bd078bc40afc510e0135d6007a7e9762000e01c0000,
  unpack 0x77d9beffa71c17f3bd9274013ff991c0323fdbdd50e0071c019580000,
  unpack 0x1cef001c6aafa068f5b28e3409ef53fd1bd941e8fb5e0187838071199fcba2b19800e700000,
  0,
  unpack 0xc9e67174192fc229d09d78c07fc3d4e0b35e6003c78d7620a6600000,
  unpack 0x1af8067e5123952a71679e60fda2382817b06ac01d81add82800000,
  unpack 0xdf7542fa1ffc2943b7a4f307c1a1c16a7e5be458ec0c69d000000,
  (0xc2cdd21fdda60ee4500670a50034f60067b68000040006215 <<< 414),
  (0xfa8797b81b14835ceac03c84802158400a52c001809 <<< 441),
  (0xb0ba8c2063610eb44a025a6a808140001c391 <<< 463),
  (0x3d67ff6481d231179940726d50028655 <<< 486),
  (0xf472a644c28e23898a40d150b <<< 513),
  (0xba8cfb2154de0205321 <<< 537),
  (0xf6b1ea51c42c1 <<< 560),
  0,
  unpack 0x35fdf9f91aafeac5e1d11c0847ee4d705c8f8a81f9c63c0187c96201bf974c5ad9800ecc00]

private def t26 : Array ℕ := #[
  (0x3f438a8e758b2d <<< 559),
  (0x317f982cf1327143195 <<< 538),
  unpack 0x7ba195f588bf8581d59df8401f9f44ec8f0007b20c7547892b10680e00000,
  unpack 0x77be6dffb83f0e438c0df5004e1939c06abfa00250025500,
  (0x1efdcbe66a2d20f0c1007ed65017aa6001c74000c050004460100017 <<< 390),
  (0x22a55bea2ddba03f20a02d9c0000d08001219000500020311f <<< 415),
  unpack 0x7ff1b1ffcaddfd63a343f401ff90c03efda26a1d51e5b00ccbb8c946103856100,
  (0x646b1894eaaf10bb1d6034e95001fa00038b7 <<< 466),
  (0x696448a6f9f10ec92000dd29801a08f <<< 487),
  unpack 0x2bdd20b802df9cd0ea585d407b932c70138ebf10ec40250086d00,
  unpack 0x1bd146ffc7ff385ceec4bd502bf388705cefb003e913387003888c7a4170383596e301d97100,
  unpack 0x1931ab5f4871c470bfec7f4801ed789e95afc07b5d0ea6c60438c47ff65620d01cccba80a7500,
  unpack 0x2064ec9c40eba0ce75061e8ff8c705bafa001eb843b100ccba80b7900,
  0,
  unpack 0x1fb13ff54c3e4131def4fac01f00194e100000,
  (0x1dd32a04ba5e087499080ddad805108001 <<< 480)]

private def t27 : Array ℕ := #[
  unpack 0x6f995de5993fa9bdfef4003e3481c162bda40a1c0a800000,
  unpack 0xc5d1e9f5c4aed419de5978c0af5a4ce0125fedc688700453b5000000,
  (0xb5fc15c3d92480fd92003750c02e80400d7a500000a80003 <<< 421),
  (0xff90f7ec23a88289d8403552000582c00478900381 <<< 445),
  (0xb1fe13cb9cde821be280c1ee8028106001d9 <<< 469),
  (0x75b4724cd15e4259f880145ce82f91 <<< 493),
  (0x20fc34e06f0aa27ce04099cd <<< 517),
  (0x1af2011be49a980caf <<< 543),
  (0x21964101ae5f <<< 565),
  0,
  0,
  unpack 0x37da58f501de9789cdca38c0a76dc4e0895e6003c5a87620ca600000,
  (0x69a971 <<< 587),
  (0x1 <<< 610),
  (0x263b8a919b3230b20560097f4012246001656800004000045 <<< 418),
  (0xc2bb42cc414080019400f7894041058016300000005 <<< 440)]

private def t28 : Array ℕ := #[
  0,
  (0x5fc94cf5e28620cc54400f4f3013a13 <<< 490),
  (0x53444c88f3fd4721a0805bb15 <<< 512),
  0,
  (0x34e9 <<< 599),
  (0xef1ef <<< 593),
  unpack 0x4de63f7cadecfa9c3143ac0e72a09e0ad3e7003f08570a8070114e1acb600000,
  (0x93e0c19587bc9 <<< 561),
  (0x7c65dd3dc0475456f87f <<< 534),
  unpack 0x10b710afb4fa373a519fe00cff59bc06c7d322a5d518a8070114e941600e00000,
  unpack 0x3f93b4ff8d9fc21391dc71a8bf910bc00e78a00f0e1ae1500e0229c17d203e53250109200,
  (0x2439803747ff5196b000415a44018c5000770000c04400401010005 <<< 394),
  (0x3bebe8c9bf52c30108403414a8024e200f20800000288008b <<< 417),
  unpack 0x1ccf5ed41fbe2a758dfe8521e7e27822970c01f8401c2fc9e4653b22b94cccbb8c94610390aa00,
  (0x3751e78155d03002706033332413e65002537f <<< 462),
  (0xc489d162cd56e1aef780d668280f1c3 <<< 489)]

private def t29 : Array ℕ := #[
  unpack 0x6b8be073cdbfba89db9ebac0e7fd9ffca65c3407980c7db62a31c0633e21051d96c544392804200,
  unpack 0x1bbf3fa4d77b40e9d87c7717c4467e18beb881d8d7fb400711fcf2023d51038e547765070550e65a80eca00,
  unpack 0x5b8c717dccbf5ca7c0297a908fe1d5fc115f4907dd217a800e21d9e005fa82070aa8eeca0e26a1cd665d405200,
  unpack 0xa5b09d290ff920f2e72eb415eff7fa03c140f9e85e00c38b8071119fcba2b199accba810da00,
  unpack 0x306c28fe2547afce72f01e9029d935380ad7eb6ce81c00d00000,
  (0x1c17ff4d1c4c046a71806eccc00b8900053 <<< 472),
  (0x30f02a388600989142002302000b <<< 503),
  (0xa6638308cd7483d224815715c05 <<< 504),
  (0x5b73626bc1e483 <<< 557),
  (0xb7a1 <<< 596),
  (0x1b2c5fd04b95a02396303c91b80ba5a001d5100050200010000001 <<< 399),
  unpack 0xc5ddcf46fc0cc752a8eb019e9c5382d075001e7881d880c0fa44800000,
  (0x1a8c12213d068c02c8000ae11405d8d8015 <<< 476),
  (0x495db8f5cc3750643100294b <<< 518),
  (0x1aa55eadf9d75823 <<< 552),
  (0x7ce4d9e4758b2098d1 <<< 542)]

private def t30 : Array ℕ := #[
  (0x550d00c13fa1 <<< 566),
  unpack 0x3172e21ea3eba3c67756de301bc9613b38003f64038012bd0000,
  unpack 0xaf472ef608be2b73830ef42794a1c1483a800fd40c400000,
  unpack 0x1909bc578bef6c70c71ea00bc004200000,
  (0xf28ef568c35221fdd7 <<< 541),
  unpack 0x3b88c4fa8dee6191d04d3dc07f93cce09e1f0007d7087620d6a00000,
  (0x1e6bc9aabccc0881f485 <<< 535),
  unpack 0xdf2b54fdab1e8413b2f474a93f2c99dd9e4007cf0ae08887a46400000,
  (0x38760842f4dc603de0805e98c026d000021 <<< 473),
  (0x21f8d7 <<< 590),
  (0x22fac829 <<< 583),
  (0x5afa7605 <<< 577),
  (0x1a606f28803 <<< 572),
  0,
  (0x3fc7b4f3626c80b <<< 555),
  unpack 0x2ff304f9986f7921d00afa004fbb00e0261f9621ae08887a48800000]

private def t31 : Array ℕ := #[
  unpack 0x10b916dec057ebb0399f475001fc591c1283afc43b100008400,
  (0x4c8eb164cfcc21d4ec401aaa10118b <<< 494),
  (0x22f5eb295e430fd6c6009 <<< 526),
  (0x528e7cdbf <<< 576),
  (0x2d686493ae3f304444303e84b00911a00056a4005000001 <<< 427),
  (0x21df186160c79056ecb02c34b0004230010db0007 <<< 451),
  unpack 0xb3b31e63378b6274a54eb02fc015380bd7cb699a1c0147e25ae800000,
  unpack 0x3263c63e10f7b1c2739c2e3033edf1382c8fb072b81d104c0f050800000,
  (0x350aa0b6e01 <<< 570),
  unpack 0x83d41ce8b29cee13ba4bf5818f3e99c00ebf832410ec403b3a40000,
  unpack 0x4b5bafa837ed381c5dafa40df3104e0895c44b1d518d4be800000,
  (0x126c35a3a3aa618a702030926007a12005024000c05 <<< 442),
  (0x11f8bcab066688f68ab03db5 <<< 519),
  unpack 0x4d82f302afbb81c095fac0c74a88e09e5e6007d7a070032c484000,
  (0xc08575ce3214e2f2f2403760e007c080000000018000005 <<< 425),
  (0x2c37d054af167094a86069cb3007804000000000c010005 <<< 426)]

private def t32 : Array ℕ := #[
  unpack 0x80c107bdc8b7f41ce70f5c201ffb0a70122fb001cd103801a620000,
  unpack 0x4ff8ecf4dfcf2b39d646ba802f4340e0815f200392a0700359090000,
  unpack 0x81a471f5da7f61b9c494fa403fbe18e03e1fedb3cc75378daf582c00000,
  (0x1de24df8432d18250c400bf4d0046290005e5a000010001091 <<< 416),
  (0x67 <<< 605),
  unpack 0x13f61bcc743a68e70abfe8027fad3380fd78801f7c81c0005a000,
  (0x629486f57691200640601 <<< 530),
  (0x9aee33cc741d81598500ddf0c0040c800cf0a000010001 <<< 428),
  (0x3943af <<< 591),
  unpack 0x228aabef60b84e670211f80c4d13829078801ff881c000a8000,
  (0xa66f79e5ff1241f8104080ce600780c00c5ec1 <<< 461),
  (0x4af44cd2a69d60741d40527240135 <<< 498),
  unpack 0x436770feb7d7caae71887e300fd28538241fcb716a1d8806b2c494000,
  (0x433aa1d3795e50a7 <<< 550),
  (0xd6cc344bb57aa1249 <<< 545),
  (0xf2e4daeb3c74e19810403 <<< 529)]

private def t33 : Array ℕ := #[
  unpack 0x10b8067f9bebda21388d971808e5209c15c3fbd2c00007400,
  unpack 0x419d47facb5e5399dfa678005fa48ceecc00341205000,
  (0x74712c1371c371f5d02008a47 <<< 514),
  (0x66ea8a1e4bc487efd081a9 <<< 524),
  unpack 0x9d39ff127de49bd3170015e9a11c16c3fbd2c00940000,
  (0x1bf3ffb9de1 <<< 567),
  (0x1e6ad8b46540d07a015817ab900060d8018f4a0000101 <<< 436),
  (0x1b218a9d991dcc0b835013d5d8044058008d100000100001 <<< 424),
  (0x860bb0575471c0f1240192b1 <<< 516),
  (0x959924c79b6ec2188a001580e007 <<< 501),
  (0x1696074979d598459e4807f79404e00801ad1 <<< 468),
  (0x1 <<< 611),
  (0x3115e3f37 <<< 579),
  (0x5686d0c23b3b5073c840142c10104a6006bd <<< 470),
  unpack 0xbf70fdf0b07f2063819f75817f5331c1183cc007af10ec4d5a6800000,
  (0x1775fdf188c0987bd35803 <<< 528)]

private def t34 : Array ℕ := #[
  (0x532b <<< 597),
  unpack 0x206cb97fa53ff2ce712b4e1037fb953a39001d9d03801ac80000,
  (0x26e6ec9c418281d0830373a3 <<< 515),
  unpack 0x37bf35fe8e4e1c99df1a3a80e73484f0cd6003c68876300e81901800000,
  (0xb28881d1 <<< 580),
  (0x2c824edac69a88c626b023ea800b62a0004b800031 <<< 447),
  (0x46f258f5ff5e40f9a840326a5010ab6006b46801 <<< 454),
  (0x2c66a397346731f7d9002e04100421000000680001 <<< 446),
  (0xa51d1ca979eb8d40aa02b1d2808d02000000000601 <<< 443),
  unpack 0x858e96f0155e5cb9dbc2fa803f2c88e0295f4003df88754796d90c7900000,
  (0x5fc5da1 <<< 584),
  unpack 0x41689ddf40f7e04c77bd3eb007c006200000,
  (0x19a243a81c2ea8e39e0038a6a009130003 <<< 479),
  (0x5c9 <<< 601),
  (0x6edbdc2c30db0a1 <<< 551),
  (0x419ca3 <<< 589)]

private def t35 : Array ℕ := #[
  (0x5a355110fe39118924406a567003 <<< 502),
  (0x75959e5 <<< 586),
  (0x9923383759d18d6fa2003579001b11003de2000002000001 <<< 419),
  (0x408df685716ce09 <<< 553),
  (0xbfb3ca2924ec01d0620040d <<< 521),
  (0xe1e2b21ae293889e4301a83b80984a0039 <<< 475),
  (0x18da79eddd6ad864511809441c00cad <<< 492),
  unpack 0x3defa839693f1a88e9f89d0047f5c4787f1a10d704443d2000000,
  (0xa315 <<< 594),
  (0x9e02161e2024874614804ce8c0462880115480069 <<< 448),
  (0xdfc5c79443 <<< 571),
  (0x37d9 <<< 598),
  unpack 0x5f747df790bea733ba33fe540538218fc07da81c00e80000,
  unpack 0x3dcc2cffaf070344ed0e5d403bc7c476063003d4943b100ecdb8cc8000,
  (0x5c147ae4915202a5a800b8660028c000075411025 <<< 449),
  (0x7bbd531bd6341f1e04004fb50159360000108005 <<< 450)]

private def t36 : Array ℕ := #[
  (0xf3db390b981aa309bac0f1 <<< 525),
  unpack 0x2fb48b79cfef54b1c116f8c097f400e0b13d6007a928762019009000,
  (0x53dcb6f024df11 <<< 558),
  unpack 0x49913f258f81d0e07cfd202bc3667877f8d086bb11011e0894400000,
  (0x1c3563516776215 <<< 554),
  (0xad82b48a3cd9429ce1 <<< 540),
  unpack 0x64cb9af90d7f985ceac61f2dc0607042afd6ebc4386ad000000,
  0,
  (0x66ee683070030407c200b <<< 527),
  (0x34461 <<< 595),
  (0x1f58b9bbc09f2042a29 <<< 539),
  (0x215c7a0064df5 <<< 562),
  (0xfa1966d2fb35461c8180399d400c28000bf1000001 <<< 444),
  (0x1c70d629ffa2d8407f001d14c0004b <<< 496),
  (0x1d71f0fb79 <<< 575),
  unpack 0x1059d17fc5a2e1299d3f13a008feb88f0fe3421ae08887a47200000]

private def t37 : Array ℕ := #[
  (0x158e26891945803bd05808cf <<< 520),
  unpack 0x35ec23bb26df5400e2cd9c602fa18e78372003ddc43b101100000,
  unpack 0x3decf73de7275988e0871c4037ac20704f2fd8fa5b1352aff5800000,
  (0x4d3d6687dd0b404b9 <<< 546),
  (0x6f <<< 606),
  (0x3ac6b38352c49844fe100927b000601 <<< 491),
  0,
  unpack 0x67fb7a74d58eb539cf48b840bf641ce0ba5f9421aec444438c800000,
  (0x2cc7da635335b86458b021e5a00ae11000df <<< 471),
  (0xd56a1fa15042610f6880d4be602f5ec00f905 <<< 465),
  (0x3e9f44093c9620ec64a00a3 <<< 523),
  (0x203aef826386e225 <<< 549),
  (0x4fbbdf907a938a820003d3c2002d5 <<< 495),
  unpack 0x10ddfa970d31ea239c273ff26c99c02e3fe35300e006a57a08800,
  (0x4f829c98991887c3e081 <<< 532),
  (0x411 <<< 602)]

private def t38 : Array ℕ := #[
  unpack 0x73a6a2fd552efb81d57438006fe510e00b5fb1f6087620196a0000,
  unpack 0x33c257fb60d7ed84e54c5f9e604e0ae1fde96008a9d43d000,
  unpack 0x834a1ce3affd0933a0b57581afdc11c052bc800f2058ea8f125000000,
  unpack 0x1be5c77d728f9f6c70c71ea00bc001200000,
  unpack 0x317c477d73fbd62672bf3e101be197382acfc06a4a1d88031251840e000,
  unpack 0x107b2f9c027fd14876a05e20ffd0380557d800f16a1d88086d9a41eaa3f400,
  (0xa4319 <<< 592),
  unpack 0x25c69b9090ffe40eef45c201b800c7100000,
  (0xeaed1bc9 <<< 581),
  (0x1b5527c2fd27b004b <<< 547),
  (0x17f150256905dc109 <<< 548),
  (0xdd <<< 603),
  (0xd9 <<< 604),
  unpack 0x1fede11cb13bb04e73ecafc8db653820d774b00189239000,
  (0x571b9b81cc8e201f1c60170d4004e04005 <<< 478),
  (0x1ffc45755396d06b0f080c45d8044058008d5000001000111 <<< 420)]

private def t39 : Array ℕ := #[
  (0x72e5d886b3f80005a003 <<< 531),
  (0x118f255 <<< 588),
  (0x181c50849f3d8c612f <<< 544),
  (0xd <<< 608),
  (0x6b18dddbe65883d22101cd71c009 <<< 500),
  (0x16296a8bc997b0c13ea0073b100235b000f5140000200001 <<< 423),
  (0x188ae9545 <<< 578),
  (0x918a45a3c72a805de8c08e528029028009 <<< 477),
  (0x63dcf5a651ec0022784064b <<< 522),
  (0x1da74a62ef713 <<< 563),
  (0x5717071 <<< 582),
  (0x2e5b7795b9e1 <<< 564),
  (0x17d359d4e46c482222180c549c00a88001ea48001 <<< 452),
  (0x2720debb1a5b1829ac3016b70009d08000df9 <<< 467),
  unpack 0xd6789e3b5fc3d63818efcb68b91c11c3e400fa980e8acd8a000000,
  unpack 0xe695fb0c8e46a1dc02fa40a791dce00e5f2da5a8747112000000]

private def t40 : Array ℕ := #[
  (0x1163d1908115 <<< 568),
  (0x1 <<< 612),
  (0x23a7d319429d87 <<< 556),
  (0xb <<< 609),
  unpack 0xb77f7ee3399c5043be5071019ecd31c06efa6943b100d7674820000,
  unpack 0x39d3897d019f89c8e1bd1c0073fa6a704c1f3003e280380148d0000,
  (0x3fc977ac98e8031ca8400e04a03 <<< 505),
  (0x154f366d0c2e584b71481a4f000150c11 <<< 484),
  (0x30d182c045dd085100a01bf7380a1 <<< 499),
  (0xb <<< 607),
  unpack 0x67e71ff70e1e06a9daf2b800e7c498e0955fadd788762695000000,
  unpack 0x1bc80639c6df2454eefd7c003ff0ae7a860a71000000,
  0,
  (0x170de6d039 <<< 574),
  (0x1dc1 <<< 600),
  (0xed078847a7 <<< 573)]

private def t41 : Array ℕ := #[
  (0x15959e5415b1315d7040557c001 <<< 506),
  (0x8757973e049616b1c6055ea0006e66001f <<< 474),
  0,
  unpack 0xc19bad764b8e8601c1eefa40ef21c4e0325f2de785731a79000000]

private def tables : Array (Array ℕ) := #[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41]

def rowCoeffs (j : BaseCols (Fin 12) (Fin 11) (Fin 12) (Fin 48)) : ℕ :=
  let q := (baseCols 12 11 12 48 j).val
  ((tables[q/16]?.getD #[])[q%16]?).getD 0

private def checkAt (r : ℕ) : Bool := binary.test
  (rowProduct binary a b c ai bi ci rowCoeffs ((baseRows 12 11).symm (Fin.ofNat 613 r))) r

private def w8 : RowWindow checkAt 8 := nextWindow (start checkAt) 8 (by decide +kernel)
private def w16 : RowWindow checkAt 16 := nextWindow w8 8 (by decide +kernel)
private def w24 : RowWindow checkAt 24 := nextWindow w16 8 (by decide +kernel)
private def w32 : RowWindow checkAt 32 := nextWindow w24 8 (by decide +kernel)
private def w40 : RowWindow checkAt 40 := nextWindow w32 8 (by decide +kernel)
private def w48 : RowWindow checkAt 48 := nextWindow w40 8 (by decide +kernel)
private def w56 : RowWindow checkAt 56 := nextWindow w48 8 (by decide +kernel)
private def w64 : RowWindow checkAt 64 := nextWindow w56 8 (by decide +kernel)
private def w72 : RowWindow checkAt 72 := nextWindow w64 8 (by decide +kernel)
private def w80 : RowWindow checkAt 80 := nextWindow w72 8 (by decide +kernel)
private def w88 : RowWindow checkAt 88 := nextWindow w80 8 (by decide +kernel)
private def w96 : RowWindow checkAt 96 := nextWindow w88 8 (by decide +kernel)
private def w104 : RowWindow checkAt 104 := nextWindow w96 8 (by decide +kernel)
private def w112 : RowWindow checkAt 112 := nextWindow w104 8 (by decide +kernel)
private def w120 : RowWindow checkAt 120 := nextWindow w112 8 (by decide +kernel)
private def w128 : RowWindow checkAt 128 := nextWindow w120 8 (by decide +kernel)
private def w136 : RowWindow checkAt 136 := nextWindow w128 8 (by decide +kernel)
private def w144 : RowWindow checkAt 144 := nextWindow w136 8 (by decide +kernel)
private def w152 : RowWindow checkAt 152 := nextWindow w144 8 (by decide +kernel)
private def w160 : RowWindow checkAt 160 := nextWindow w152 8 (by decide +kernel)
private def w168 : RowWindow checkAt 168 := nextWindow w160 8 (by decide +kernel)
private def w176 : RowWindow checkAt 176 := nextWindow w168 8 (by decide +kernel)
private def w184 : RowWindow checkAt 184 := nextWindow w176 8 (by decide +kernel)
private def w192 : RowWindow checkAt 192 := nextWindow w184 8 (by decide +kernel)
private def w200 : RowWindow checkAt 200 := nextWindow w192 8 (by decide +kernel)
private def w208 : RowWindow checkAt 208 := nextWindow w200 8 (by decide +kernel)
private def w216 : RowWindow checkAt 216 := nextWindow w208 8 (by decide +kernel)
private def w224 : RowWindow checkAt 224 := nextWindow w216 8 (by decide +kernel)
private def w232 : RowWindow checkAt 232 := nextWindow w224 8 (by decide +kernel)
private def w240 : RowWindow checkAt 240 := nextWindow w232 8 (by decide +kernel)
private def w248 : RowWindow checkAt 248 := nextWindow w240 8 (by decide +kernel)
private def w256 : RowWindow checkAt 256 := nextWindow w248 8 (by decide +kernel)
private def w264 : RowWindow checkAt 264 := nextWindow w256 8 (by decide +kernel)
private def w272 : RowWindow checkAt 272 := nextWindow w264 8 (by decide +kernel)
private def w280 : RowWindow checkAt 280 := nextWindow w272 8 (by decide +kernel)
private def w288 : RowWindow checkAt 288 := nextWindow w280 8 (by decide +kernel)
private def w296 : RowWindow checkAt 296 := nextWindow w288 8 (by decide +kernel)
private def w304 : RowWindow checkAt 304 := nextWindow w296 8 (by decide +kernel)
private def w312 : RowWindow checkAt 312 := nextWindow w304 8 (by decide +kernel)
private def w320 : RowWindow checkAt 320 := nextWindow w312 8 (by decide +kernel)
private def w328 : RowWindow checkAt 328 := nextWindow w320 8 (by decide +kernel)
private def w336 : RowWindow checkAt 336 := nextWindow w328 8 (by decide +kernel)
private def w344 : RowWindow checkAt 344 := nextWindow w336 8 (by decide +kernel)
private def w352 : RowWindow checkAt 352 := nextWindow w344 8 (by decide +kernel)
private def w360 : RowWindow checkAt 360 := nextWindow w352 8 (by decide +kernel)
private def w368 : RowWindow checkAt 368 := nextWindow w360 8 (by decide +kernel)
private def w376 : RowWindow checkAt 376 := nextWindow w368 8 (by decide +kernel)
private def w384 : RowWindow checkAt 384 := nextWindow w376 8 (by decide +kernel)
private def w392 : RowWindow checkAt 392 := nextWindow w384 8 (by decide +kernel)
private def w400 : RowWindow checkAt 400 := nextWindow w392 8 (by decide +kernel)
private def w408 : RowWindow checkAt 408 := nextWindow w400 8 (by decide +kernel)
private def w416 : RowWindow checkAt 416 := nextWindow w408 8 (by decide +kernel)
private def w424 : RowWindow checkAt 424 := nextWindow w416 8 (by decide +kernel)
private def w432 : RowWindow checkAt 432 := nextWindow w424 8 (by decide +kernel)
private def w440 : RowWindow checkAt 440 := nextWindow w432 8 (by decide +kernel)
private def w448 : RowWindow checkAt 448 := nextWindow w440 8 (by decide +kernel)
private def w456 : RowWindow checkAt 456 := nextWindow w448 8 (by decide +kernel)
private def w464 : RowWindow checkAt 464 := nextWindow w456 8 (by decide +kernel)
private def w472 : RowWindow checkAt 472 := nextWindow w464 8 (by decide +kernel)
private def w480 : RowWindow checkAt 480 := nextWindow w472 8 (by decide +kernel)
private def w488 : RowWindow checkAt 488 := nextWindow w480 8 (by decide +kernel)
private def w496 : RowWindow checkAt 496 := nextWindow w488 8 (by decide +kernel)
private def w504 : RowWindow checkAt 504 := nextWindow w496 8 (by decide +kernel)
private def w512 : RowWindow checkAt 512 := nextWindow w504 8 (by decide +kernel)
private def w520 : RowWindow checkAt 520 := nextWindow w512 8 (by decide +kernel)
private def w528 : RowWindow checkAt 528 := nextWindow w520 8 (by decide +kernel)
private def w536 : RowWindow checkAt 536 := nextWindow w528 8 (by decide +kernel)
private def w544 : RowWindow checkAt 544 := nextWindow w536 8 (by decide +kernel)
private def w552 : RowWindow checkAt 552 := nextWindow w544 8 (by decide +kernel)
private def w560 : RowWindow checkAt 560 := nextWindow w552 8 (by decide +kernel)
private def w568 : RowWindow checkAt 568 := nextWindow w560 8 (by decide +kernel)
private def w576 : RowWindow checkAt 576 := nextWindow w568 8 (by decide +kernel)
private def w584 : RowWindow checkAt 584 := nextWindow w576 8 (by decide +kernel)
private def w592 : RowWindow checkAt 592 := nextWindow w584 8 (by decide +kernel)
private def w600 : RowWindow checkAt 600 := nextWindow w592 8 (by decide +kernel)
private def w608 : RowWindow checkAt 608 := nextWindow w600 8 (by decide +kernel)
private def w613 : RowWindow checkAt 613 := nextWindow w608 5 (by decide +kernel)

lemma spans : Base 12 11 12 48 := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply certified binary (baseRows 12 11) a b c ai bi ci rowCoeffs
  intro i
  have h := w613.verified i.val i.isLt
  have he : Fin.ofNat 613 i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simpa only [checkAt,he] using h

end TensorRankThreeFactor.Base13

namespace TensorRankThreeFactor.Base16

open TensorRankThreeFactor.FastBase

def a (t : Fin 15) (i : Side (Fin 15)) : ℕ := fromTable #[0x11, 0x101, 0x1001, 0x10001, 0x100001, 0x1000001, 0x10000001, 0x100000001, 0x1000000001, 0x10000000001, 0x100000000001, 0x1000000000001, 0x10000000000001, 0x100000000000001, 0x1000000000000001] t (finSumFinEquiv i)
def b (t : Fin 15) (i : Side (Fin 15)) : ℕ := fromTable #[0x11, 0x101, 0x1001, 0x10001, 0x100001, 0x1000001, 0x10000001, 0x100000001, 0x1000000001, 0x10000000001, 0x100000000001, 0x1000000000001, 0x10000000000001, 0x100000000000001, 0x1000000000000001] t (finSumFinEquiv i)
def c (t : Fin 15) (i : Depth (Fin 14)) : ℕ := fromTable #[0x101, 0x1011, 0x10010, 0x100001, 0x1000011, 0x10000010, 0x100000001, 0x1000000011, 0x10000000010, 0x100000000001, 0x1000000000011, 0x10000000000010, 0x100000000000001, 0x1000000000000011, 0x1111111111111110] t (finSumFinEquiv i)
def ai : Fin 75 → Fin 15 → ℕ := fromTable #[0x100010110110010, 0x101101000100011, 0x1011000011101, 0x111101100010010, 0x10110000111111, 0x1101111000111, 0x110010101100011, 0x101000100100, 0x1010011011010, 0x100011000001001, 0x11100100000111, 0x110111101000011, 0x111000010001111, 0x11000110001101, 0x11010101000, 0x10011010, 0x101001100100100, 0x1010111001001, 0x1001101100010, 0x110110011111110, 0x100000100010100, 0x111110010111010, 0x100100011001000, 0x110011000101110, 0x100100101101100, 0x1001100100001, 0x101010000001010, 0x101001001000011, 0x100001100001000, 0x110010001100000, 0x11110100000, 0x10010100111101, 0x110110100011000, 0x100111000001100, 0x10110111011111, 0x100101011000000, 0x110011100110001, 0x1011000101101, 0x100111001001001, 0x11011000001100, 0x100110101001, 0x100010010011010, 0x11010100111100, 0x101101100000100, 0x1010000000111, 0x111110100000000, 0x111001000100110, 0x1010100100100, 0x100111100001, 0x1111000010110, 0x11101000010000, 0x101111010000000, 0x1010110101111, 0x100000010100011, 0x110011011111001, 0x111111100011001, 0x110110000110001, 0x100000011011001, 0x10110101111001, 0x100001000000100, 0x111010000100001, 0x110101101100011, 0x10000011011000, 0x11011001010100, 0x111110011010000, 0x100010111000001, 0x110111100101110, 0x110111000001000, 0x100001111000110, 0x10110111010010, 0x11011011100011, 0x100110011010111, 0x11010000100101, 0x10000000100111, 0x111010100001]
def bi : Fin 75 → Fin 15 → ℕ := fromTable #[0x1111110000010, 0x101000101010010, 0x100010100010100, 0x111011011101011, 0x100000100001000, 0x10110001100000, 0x1001001000110, 0x11001101000001, 0x101010100101110, 0x10011001111000, 0x101010110011010, 0x1001111010000, 0x100110011001, 0x11001111000000, 0x10001010010101, 0x100100100011111, 0x10100101101110, 0x10001000110000, 0x10110111000011, 0x10100111101100, 0x10101110000111, 0x101000010100001, 0x100111110011010, 0x11000000111000, 0x10101100101111, 0x100100101100111, 0x11010010001111, 0x110000101000010, 0x1000000010000, 0x100000010011101, 0x11110010100000, 0x111101001010, 0x111110100011101, 0x10000110111010, 0x11110011010000, 0x101110111010010, 0x110100101101100, 0x100100111100, 0x10001011011000, 0x101101011000011, 0x101011101010101, 0x11100100110000, 0x111010100110000, 0x101010100111000, 0x1100000101, 0x11010010000000, 0x11111100101, 0x110000100001010, 0x110101001000010, 0x101001001110101, 0x11010011110001, 0x11000010011010, 0x11000001001, 0x111010000110100, 0x110000111000010, 0x1000110100100, 0x1010001010011, 0x101001101011011, 0x111001110001000, 0x10011110011001, 0x110000010010, 0x100110100101101, 0x100010001001000, 0x1000000000000, 0x111100000010100, 0x1101111100110, 0x101010101001010, 0x11010111100100, 0x1001111000000, 0x10100111111000, 0x101001100001011, 0x111100000001, 0x1100001110, 0x101101010100010, 0x100100100011001]
def ci : Fin 75 → Fin 14 → ℕ := fromTable #[0x11010110101100, 0x101101100101, 0x11101110010, 0x10110101100110, 0x10000001011100, 0x11010010101111, 0x1011010001001, 0x10010101111000, 0x10001000100100, 0x10101101001101, 0x10111101100001, 0x1011000010000, 0x10000100000, 0x11100001101, 0x10111111010001, 0x11000110010101, 0x10100010001110, 0x1100001000100, 0x101110100101, 0x1001011011110, 0x10010111010110, 0x1000110010000, 0x10100101110011, 0x111000110011, 0x1111110011011, 0x1011110000, 0x101001000001, 0x1010011111011, 0x10111101101000, 0x10000011000, 0x11000111010101, 0x10101001001111, 0x1111011100110, 0x1110010111000, 0x10001001100011, 0x10000000110010, 0x10011010100101, 0x1001000101101, 0x10010000111, 0x100000110011, 0x10111110010000, 0x10101100000000, 0x11001101001001, 0x11101000011111, 0x1110001011111, 0x1100111010, 0x1100011000011, 0x1001100001101, 0x1010001010110, 0x11110111001000, 0x11110110001000, 0x11000111100010, 0x1011111101101, 0x1000110100, 0x100110010110, 0x101000001010, 0x1011001, 0x1111010001010, 0x11110111010000, 0x1111101100001, 0x101010101010, 0x1000011111011, 0x10100010001, 0x10111111001110, 0x11011001011000, 0x101, 0x10011000111, 0x1001101111100, 0x11011101100000, 0x100100010011, 0x10111100010100, 0x1100000011100, 0x10100101010001, 0x10100110001101, 0x1011010010001]

private def unpack := unpack16 60


private def t0 : Array ℕ := #[
  unpack 0xb15bf28cae6f9bfa0c3e661f1680e975ff8203a233f8480f8989e50039fa97e6f30bebb8e01ecaa0075a87195c983000000001,
  unpack 0x17876e8821c356bf800748e2f35a1cfe0fe94077ea0e1c01eaaabeb308c0fee8313027667003bb1841d0acd92d6cbe0163b972007930000,
  unpack 0x295e5c8a03955077e38e91cbe9a439803ff180e84d5fedcb07ffa61105ff9c661f150270ca1c40006f7f372008005e0000,
  unpack 0x1e018e3351f536bbb4c79031fd6e17abdc33aecfb4e3bafeb33418fabe807d71017b118842811c9e509fa7f3f5ef21c4c0000,
  unpack 0xbb3dfd060395dffa308e248bd084386c173a00e2e81fd22cafb8ca04bf31a83f5dd2f4ab2981fccfe6f43001780000,
  unpack 0x14cc67b3007ea14ff831dbbf7f06075be7e6501e757bdba953ec10395d17ed6a193f5ec05e3b70dd0d490bdf47a0900000,
  unpack 0x489dfd5a77a864f5631cac5784287c932fe301eeebbf2007769bf8891c7fe7cb95f52a04eca0a87769001503b9e7f9fae48005e00000,
  unpack 0xa6215c2843d156f77b8fac3fd6b03a8ea7d980ed2c5fa9cb337c662d71f80039a207060af4e0074420772194fde4fe7c840c00000,
  unpack 0xe528785dce9257db2c3a3ac75e00e90e9dc003a396fd772b7fed00396f87fd61b99dd001d9a5eb912e80077f3fe6e79e481800000,
  unpack 0xc207e16373b0de3a01d56ed0eb67ffc0038275ff4294bd2207019bfc80a1f5092f6710438841811c9e07c9cbd6002f000000,
  unpack 0x1ae438e5671845f3611eb4e7f5487f8eaff701dc487d5407cd4ff8801c05c3f3e801dd00073cfa206000000,
  unpack 0x8337b7f5a99efff3a64c7a436e5421fec0bf9c07f0c5fa901f7e6bca00705eafc8c80f770807b388c420608e4901a71fcd000bc000000,
  unpack 0x7451fbc2bb35ff7368871f0243d460fec00f0de7c92039cf8fd46f83f6bf983faef9483b3a801d6a10c8c3898000000,
  unpack 0x9263fe388e6ebdfce63a529f0d40f5091f9d95fd7b471f3d20072b68fc8aa0774001cf930000000,
  unpack 0x1d1ff712ce33eff8da3e80a73ed0e22bdc2e03e0e2ffe6e8a7ff59bd17ed61b03f5a405eca208777e9b901a01de920000000,
  unpack 0x28c4ef379ee8a49dccc39dfd778c0e0f5fce8838e067a200f8967e51039ad17eb7d007fde300e4432ef560ba6240000000]

private def t1 : Array ℕ := #[
  0,
  unpack 0x107c16dc3d33f16d7d780e05c7ce003ca49fc280f2955d1a03a13173400e3a75ff5dcc5f5402f64007761083988504724ad97c02cf000000002,
  unpack 0x2f485f5723c7e47e188fed59d48438147f4b80f3b77fd8f0be6801c50abf6bfdc3ee950270ca1c40006f000000004,
  unpack 0x15cffa6fddd3f7ed587884af1021f056bb90071517e1901c17d38a2071d32feee207d71017b1188546c9e509bd0f400000818,
  unpack 0x1075211d2813ba2277318f6cf1c4943a750fb980edd57cb003ca04fc663c01f54949eec60477a5403d0f400001030,
  unpack 0x2047dfb163ce89f4790fb009dc203dcf9f6280fc4d7c3203c4997b000e06f5f80039e057d76901bc76974352420000002060,
  unpack 0xab9fbcb1fbda7f7fa38f625dd7143ca8776380fbdfdfa9bad47a456ebebea81d24d9e46ed2002a07e7de4720000240,
  unpack 0x5b88e5c4decc77a5cc7c5dde1ca1cb7e7a88073b47ff4fbe93feb1ae2ffadc403eb041bc3801d6cdc8653000000480,
  unpack 0x16da57fde27d26ee5571feeebf94071793fea8d5f4880f69cfc0485f80039a85fd778811d9a47225d000ffcfde4720000900,
  unpack 0x2ba017bf6ae60c7d3a03ff8c7ec00f6efdc6603f7fffac00fbe8dff5993c7fd74903f58c05eca2087108302393c0f9000001200,
  unpack 0x37635d4d33fbbbfb010e2b17c9903dc94ffd6af05d0a039131fd666ea5f9e542faeea0238f407be87a0002400,
  unpack 0x8c5c7be1cf1937d6cc3816475250e64f3fc003833ef6c80f45bdf1995c17fd60a11dd4601ece231081823924069dcb91fcc00081800,
  unpack 0x14464f6169f350fab40732e7fd501f4a3f99c07f6f9f8101fe717ca2071188fc001f2127b2003b2a801d6a10c8dcfbc8e400103000,
  unpack 0x34b8e5361c617f9788785f2e9ca1c0d4fee3e378ec101c95bfd02073150fc001d14238003f9fbc8e400206000,
  unpack 0x1a607f4d6f8655f6a23bd3779e00f1ab1c2c03a8697ac80ec9d3e110396d57fe76815dd880deca20877697203403bf9fbc8e40040c000,
  unpack 0x306b7aed0ef64ff2063baac7fc10f3607ce20396ab7d78947da0072a2affad0303bbc803c8821c174c3801c0000818000]

private def t2 : Array ℕ := #[
  0,
  unpack 0x1927918a79733f1311d67bfef20797b6f6501efb07f5b1f09f4081c89cbff34188eefa00345000000005,
  unpack 0x3b31bb05b74693e5c51fe5bbf14874c67e6201f4c8f954072c8effac732bf6b1049ee93027667003bb1841d0acd92c6cbe0143bd0f400000249,
  unpack 0xe1c47ce66fe787e3c43d2d1fd480f5e93ce203b7227ed7b95df12a88fdaff9800b4000000034d,
  unpack 0x850fff01389aaf4b90efb65dea03c9fef9200f2197f5d97517b040e1c61d4a91f5dfeb5a00a823a8bf7d0f400000451,
  unpack 0x41e6abf4cb8fc465c9e23c376fa250effd3d6203e35dfac80f55f5e810391587fd79815ddc204ec010e55c82823936b23f7d0f400000555,
  unpack 0x29cdfac13c66bfa518e5983d1043ef1a7c800ec9abea003cb057fc67605f80038a807d400b40000000659,
  unpack 0x41b101f649ae6893f0a43e7f373240e3e5ffc203ffa8fc880e8f6ff199de97e5d523bbe802e5dabf7d0f40000075d,
  unpack 0x20eac5f9a7f72495edb61e86fbb86872224e5701d8e4fd24079817f2801c258bfa2a01f5002d3d0f400000861,
  unpack 0x14a4a38bf67489ce8371f6aa7f06871c05fc9b00fe480f8959f11690fc8a64700172fdf7d0f400000965,
  unpack 0xe9b87f01ef17d7f80a3db4afd4d0fa08fcaa03a3507a880ffb53e910396257ed78311de800282bfdbf7d0f400000a69,
  unpack 0x41f622711e2f098fd0e03ab167f9729abe8603bcbaf6e80faeffec00389f17d6732fea5003d95400eefd3743c652402f3d0f400000b6d,
  unpack 0x4182a77fd04ebeb1d68a3a1a671610e6aa7eee03812ffeb6c787c2455f9a108fafa002820ef7d0f400000c71,
  unpack 0x2a6607198ae6a61d9823fb9af3090f1463ec403c21d74480ffb71f299e4c748a07d755a0022abbd0000000d75,
  unpack 0x1060c81e33bbdb3df1738f0cf5fe003bc9cf6100f2e57edd867d7da66051c4b81ddcc01eb46b4c409c0ef7d0f400000e79,
  unpack 0x17237e8b4ddd6f3a6cc71671ef021e4f63998071276f1801d103fb20885fd1088eefa00740000000f7d]

private def t3 : Array ℕ := #[
  0,
  unpack 0x17fc3facf176189f8a21d92b7ca356ece2601d03b7f6407def3fe8f8070000d0000d0000,
  unpack 0xacef5cc0438becf3120e9b41fa103b41a71a00f2547e2203e9fc7fa648d1de803f6a1fd75001241c73ebd001a0000,
  unpack 0xc254f7ed8f241dd3ea3984170ac0eb729c6203bea3ffb746a1e900384717d47623ebb8c05e4442c363dfe6f5cb90340000,
  unpack 0x834f00ec0b5e63f3fe4879194fe5a1c8fbfe9007d2e9fad57cfb000e3e31c4305ddfd60ca675539e5eff3038d80000,
  unpack 0xb44a5f635b834971588f6c91e4a438012fb980e53c9ee98b8573040e5055ce301df6c0680701fcfde5e80d00000,
  unpack 0x52a9ff317df0827be8c79eeeec8a1f541f91407720aec101c3723fb3308afdaca02fb943302139e79f7d391a00000,
  unpack 0x4198a87a074fc995e6e63dcc375600fc9a7cc2039c157a080fd73de110386c17d45123ebb8e18ef5e85a7f3fe6e4738011c00000,
  unpack 0x1070e95e2afb8ba2f0838e7123ee003fa8ffb800fa2c3eda205e6881c630bdd0076607fa960471e80f5ef230023800000,
  unpack 0x8b59c09eb965ffaf30e9847dd843d3b5f9100f8d8bf699c62fb000e006ff800394e471096f7a310acdf23f99e8d000000,
  unpack 0x2cca47eabcf7cb5d2cc3d7d473650e79d9f0a03d0ddfc400f146fd90038f74756c1fd6b0238f40a0fe7fcff99a000000,
  unpack 0x347b7fd133a5957fa30e55c7ef143fbd2f9880e8883fb1be077c6624fdf5d243e2c08e000f7d34000000,
  unpack 0xaf6e9fc763a33476138e5019dd043e619f0680f91c3eddfcf1f9400e30f9f80038ee1fd7a4a3bd04a31fcf9f78d8000000,
  unpack 0x626df0973dbbb74f80e3569d4403cabcfa200f93a7d9203846473400e40fdf92689faee3003807661ce00470000000,
  unpack 0x41e32472cc0f7c91e916395857f8c0f3663f4003918dfac80fda6ff7185fa7ed71e81f5d87a03f99a0000000,
  unpack 0x6559e9831d09ebe9c872b9de3d21c1d3fb4d076828e4501ca9fffeb2526fb6fa107d04072f09e516f5600dcba4907b58011c0000000]

private def t4 : Array ℕ := #[
  unpack 0x94c5e29c9e4ed7d6447992af5c01e9acfc9807b185fcecc24fd271e5de8038601fd75001241c00000000,
  (0x1ac8a03145f168394292910082e2235c00d2b70407ec79820010d000032041 <<< 701),
  0,
  unpack 0x2b62cf157ee73a7f0243e29ef9610f6025f5dd5f576c80f389ff298a757fd71181f58c05e44423400000000,
  unpack 0x7891fec517c899f4871f0763ad68767d0f3701e84d7a440737dcffacc583f6ba580faefd00eaa00000000,
  0,
  unpack 0x615a3d54371a05f9301c042fe6487464ffb2c1ab7d20078d7bffac9483f00070d09faeda003804200000000,
  unpack 0x16b31f4bcdc2957f0d47c3d8f4521ddae78d8076e35f9901e4b9be331a20fef2005a00000000,
  (0xe5dafd727de5db103deaa8607b7764002ae5240057021a2014744d <<< 729),
  unpack 0x302678f50f35e7f40c3d0c9f7e50ea779f13004f9001d2293d20731fb59c007d690179110acdf200000000,
  unpack 0x5c4baf7ad1ed55bcad473885f3521e613fdc807d427f9101cb99fd20072e72ffcd0623bbe801400000000,
  0,
  unpack 0x3817dfca13f0aa7f080ff821eea03c60e7e972833ff5bbb27dc67dc5fb5a0257740070128c00000000,
  unpack 0x6df97e542f22f9c0c83ef8476ed0ee66bd4203b97376800f5eede9103862572a007d6d00ecc00000000,
  0,
  unpack 0x838c58ee735d664fd5dc766e1f4d21ecf87dd4076584e1901d16d3feb19c0faf2c07d77e800f72e9241f2d9c800300238000]

private def t5 : Array ℕ := #[
  unpack 0x838f09f0919d33d3d7cc7a4fbfe481da92785407a629ed001d5ae3e332748fb401ee02fba0c03c899310b20e08003780000000,
  unpack 0x1061a57da86be60d7bd00e905be8043b17e7ba00fa801dde96af94e9ba00f9187ddfd60024838a00000000,
  unpack 0x2825fe813ea8e7a328f74d1e51438e2ff6b00e62f3f9003cee7ff4dcc3fb1a87c5409c328710001bfd0000000492,
  unpack 0xafe71fa263e712fe967c71d0a03d56f79080e6a33f8003d3167b040e7465f8003e2207740039000000069a,
  unpack 0xb3d578f0af248fc3683bd2571a40e11effedd2bf7fa78833c910399cd7e7b623bb180bc8884698b3900000008a2,
  unpack 0x279fef5ae07e1fba8383237b880f6637d6c03a460fc400e276bcd1038b617fd68b93df6d8802a238018f390000000aaa,
  unpack 0xb86c5daa239390f7da8fbd03fd243ea82f9800f123bf920394ccfa44d2bfebf1c8fada00c80000000cb2,
  unpack 0x28760f2808fbad5f3063da06f9400fec85e2a03cb5278c80f1cf9e41039e897f5b707bbdac00092380000000eba,
  unpack 0x146633997e7176be2d41da85faa287cfa0e4501cd50fe0407b735fb8c3323f00070d08eef4007620163873d00000010c2,
  unpack 0x2df3ffa5cef10d1cba63d9faf1ed0e9881d6c038e827a080e89cff718f1877a00f4a11dd006e33900000012ca,
  unpack 0x14d4bfc61676354ee751f518fa56877ffef8a08bfe800e39bbc51038a957d5a623eb580bc88841111ec803800000014d2,
  unpack 0x5b3a0e67fdc59afc2907d406ecc21e4007d54079696ec801e8dd82070ffafab2017750270ca1c4418e0073d00000016da,
  unpack 0x13cdf9e7770306fcb71e4fa7f10873a3ffc101e35dbb4407617cf94ca34ba4303ebbf40193000000018e2,
  unpack 0x8a73e83f1db35bd38076f85f9801fab17ee3715ffaae1376488abf6b018aeed6000ab3fa7f30000001aea,
  unpack 0x16fc47e76a766fbf1c01f88df91087f926e7401fa05f924072ae7fa81197e000ffa87f52601e44c988153f00000001cf2,
  unpack 0x20ec07fe65078801e5351e5347aa6877db0fd401c62c7924079db1e2881cf2c3b0623eb680986390000001efa]

private def t6 : Array ℕ := #[
  unpack 0x1af5f5861c196392947c05cf6d21f4273e4c07b983e5801f18ebed30e0ae55c2eed68475110701429a280000000,
  unpack 0x70c8f914ae8139d2e23c44a782c0f701dfa403cadcfa6f207da2073452fc80c4777d0011047002afeff372007a30000,
  unpack 0x2e8117b864e9b3ff3263fef5780c0e3ee1eea03f7dd7e7676c3e41038fe87d6b323a301791108d3167bcfbcfa3d0001ae0000,
  unpack 0x16dd0bd9947d17afc521cd6afbc487a3ebf96f57bbb24077138e2168ec009ee101e1a38ed77ab0304b0f86c7a07200035c0000,
  unpack 0x475bfbe71c5183f1d87bdafec801e2843c980785b3f0901fbf3bd800737fafdacd023ea1a41c12801cc5baa87bcf2f5e8880000,
  unpack 0x45a7781947914df2311c28d7a34076829ff6c6063d0407db23f6881cf5a3ff39589fae312f21b16e07d7c9801c7754d95007579f7f983d000d700000,
  unpack 0x32f1f3591efc3fbf407dbacfa1a1d0c2fd1807f37af9901c0737e531968fc001d470381483a0503801fcdc9cf2f4600000,
  unpack 0xa72bfa40cf8e9fc22c3fe7f7c650fc29bda003dccbf8c00e42ebe4103847d7fd70315dd8338e8a20ef5eca1fcfd0f5e8c00000,
  unpack 0xad64be15b3e78ff85b0f66e1c6a03c6d2fc080ef8a9c32038d837f6662c1f9184ce6824ea200ef75f261d01c3f9bf98fe68800000,
  unpack 0x17b38bbe0d7f591f1971e76efba0879b79fe601d566fd04074aa3e6881ceaefff31448fadab6cb3a6db0e7de460087000000,
  unpack 0x25f87d498394a078ca8e8425ff903bafa7e877c83ee9df6775440e36a5c6311dda008e8208efd67a1eff339001ae000000,
  unpack 0x834720fd6a9e0823e0147d7daee481f34ef9c4076a95f94d2f5bca0071e52e780afa9706f7a33b34001ffd61fcdcf3c8c000000,
  unpack 0x45c7d25c707efe4721ff603c2207e431eaf01cddefc440756a5e6081c8943b150bbb5001c4441c18b03f98006b8000000,
  unpack 0x5f057f46a9c1643b24073e95fba81d9d87f5bb4caec101cafc7ee336f2fce88077755a2883882c8e0fe7cf230000000,
  unpack 0x14c5c384d271a6ae61e1d74a7a1287be2ef2601c3eb796407662ce3fb0ffac6423eb8041d2011d4101d0ec1ea20000000,
  unpack 0x5199fe7305e3f2ba64c7995ce1d81d5107a1d076595e4d01eb02fd20071a48ff6e4703fbb2b29e150141f5941c8c0000000]

private def t7 : Array ℕ := #[
  0,
  unpack 0xdb4de0a0bd99cf2930ee13dcfb43c7057fd79f63e9742bff8c4b03feb3100eefeb5a008823a8b00000000a,
  unpack 0x3c9c1e2dd3a24a76190f3201f5903839af4880efe83f9003dfb2fb400e2431f97800eec602f22211a62c000000014,
  unpack 0x41a36efec90f9c2fe4c63e2c17b610f6fa5d6c039b3778480f9353f1656a541fab094f1c0c76bbd58182597345345000000028,
  unpack 0x20c4117e49e71e81e8241e1e53fd28762a4eebb24ff76af8dfd38a0e5408ed5f6c7a62dd54000000050,
  unpack 0x41cb4d7ebc4f642de92e39475fca40e3e07e0a03c523fc400f8f21fd857ce2a1f7312f450873b3d7c9801c7754d950075790000004160,
  unpack 0x20e321baab176ae5f5c21e0dcbea08780e7fb301f400bd64072097fe8b7d758457d775001d1411da807bc8e4000082c0,
  unpack 0x6a26fdbf77ceb1ed531f28cbe9607d7beef601d2bdfd240760a8f94c49e3f6b3040faec8220e3d94390000010580,
  unpack 0x1fc3af31d1d327384187389ae9101f590bf5c074cfbfb4cd2c385ca3f35015dc059d5401cd7c9874070e7de4720001100,
  unpack 0x419dd7f885ae09fbecca3d79f7b410f6407ee5a53afec80f38edfe99d2c7e000ec905dd8028e2a00e74db61c800002200,
  unpack 0x3f925fd4f380897f538f430df2103d241fea80e53c5fadc17c7d662fc1f57100eefeb5a1e87be87a0004400,
  unpack 0x4f9b995775c96ea941e1a43ca60799baf3201c50abf5b39f9e6081c1583ff38dc0eed302f440873b34001ffd61fcdc8fe60008800,
  unpack 0xe97ff2ab2e9539f5663b070fd46b32deec0389f276080f3aabe41039af57fe7c111dd344441c18b03de4720011000,
  unpack 0x11648e7165d4b27a0c875e30fe4a1f6d33fd8076b0ffcec567bd80071d12feb2607d554110710591c1cfbc8e403d22000,
  unpack 0x10744e1cd7d3d8dd77700f015bf8303b6ce77380fb675f505a3ff8c6b8bfeb0ccafaeda083868039d43b03de4720044000,
  unpack 0x41fe567caa2e8eddff0c39fdd76a90fc895eee0394cbfb7d31bca0073fd8fce8bd4b403bd59dd655d362000088000]

private def t8 : Array ℕ := #[
  unpack 0x5e837e56fddfc67bd907e3d1fa921d730ff90071517e1901c17d38a2071d2afeb461fd498079132826c0c0f2480000000,
  0,
  unpack 0x1c5a1e60abf1a5fc930f7adbcea03d04efea80f7bf9d9003826e73440e2d41ff5ae847d71017b1188546c9e509fbe87a0000024,
  unpack 0x114cf75fdd13e79d0478f4bf9821dc153d50079b93ec101cf403922070698ffcea623eb180bc888468e7900072000d34,
  unpack 0x55cb1f026df9e03d3507616ee7001e55fba4c07a0fef8801c92bb982071828e650bfaef3087a68e3b5deac0c12c39a390000001144,
  unpack 0xab94fc5cef2a0bede63d537774dde7d100736c1f9801ff2438a2071972ffcc740feb8409d89942200be9206479fe61e8072001554,
  unpack 0x32d75f3b43f40bfd0b0ebec5eaa43dbd474a00e45d7f9203c6d3fb000e5fc5ff58845f6302f22644a200000001964,
  unpack 0x1bd87ccd1b89e2f7f38ef8f9c8143fde073900fe7efeb203aeebfa440e3945ff58a407d61403828a3b5dea75600000001d74,
  unpack 0xb541f11c0f11a9da623de5a7a080fc817de40396467a880f5031f5988997f5e127ba4a49df8c1202a9c3d0000002184,
  unpack 0xb2c5ca79bed1776e98f8665fe043ac36ff880fa1b5fd0156e2881c9bc3f6b4c40faef8013809a4390000002594,
  unpack 0x27adbee6972707e9951f21b3c90073a1ee6701dcdb3d400758baf94c4343fb6211c00000000029a4,
  unpack 0x507aebc51d5037be987f365e4121f7b0fdbbd41df5801c5a7bd80071178fc001ef32bbedb110aa8070f7900072002db4,
  unpack 0x98c8f2c39e8bdf8f107f0d0f6501f604fcbb2477f5901e3f4bc820736d0fc86457769817913204000000031c4,
  unpack 0x4211f1a8ce7ea3c4ea3d8b17e490f0aa9e2603c8ecfcc00f51bbe9984987fe62211c001fcf9000720035d4,
  unpack 0x1767cbed4572e23ff501c91d796687af75f6ef0e5786407290dffac9febfb5b01f5c405ec46181f2000000039e4,
  unpack 0x17151f95f578266eb171d9b27fe607f4bbef601c06dbd0407cd28f6081ce783fa7905dd4520efc62198390000003df4]

private def t9 : Array ℕ := #[
  0,
  unpack 0x5c29eefc6dd406ba7c87cbe5ffd21eeea3f94071136f9901c293bb21735f59c4aeee1027600872ae41411c9002c7f7d0f400016f0000,
  unpack 0x119afb29379d28e2171e8fdfa56878c3cec201c229794407b15cf4cc2983f3ab13df6d8802a238018f39000002ce0000,
  unpack 0x2f9fdf05cb91f979a80fa243f2103e4cf71180fd62fd120382aafc662945f90903fae1027626508802fca640c8ff3e79f4f41eac0000,
  unpack 0x14eb8fe6d67db33fb701f8ef7b7407aa70f6601c6783b5007abbff6081c3b63f6b0943ffad9493b3843bb42e59478a027606eaa7f3f5cff30000b380000,
  unpack 0xbc265f16db93adf77b0e70d9d3003c2c7f3380ffe45fedbcfcff43e03ff31841faef30879ae4a4727a1a9217be8f44016f00000,
  unpack 0x41bfb873166f13a1f2e83df04fde80e01c9e4603e87374c00ebec7f19831d7fe6b307ddc09d90150eed2002bc91044e46d867cf3cff37bef2c020e00000,
  unpack 0xf586fbdb5fa3d3e69473ac2fa1a1df2abe80079af6fcee6887fd30902fab2057f764c21de803df5cfa720059c00000,
  unpack 0x2821d73be6e220dc2e63cae47a0d0f6815ca203fd0a7e800ed567f19882c7e000f8d9bf54f2decd23320681c000a800000,
  unpack 0x5416f4db2f9d7feba43fef6f3e50f20fdeee03ad657db6723dfd31adfeba01fd68c93bf999a8603de5e95000000,
  unpack 0x28eeef1af8f72e1f6e63a6df7da10fbd7dec603b84cf4280e0337dc00385bc7f6a527bbf4c001fcff9ff3f56000000,
  unpack 0x83639beffa1fe547df5872b92e4da1e515fe940738aeeb901f5cc7d22073a96fdad5f0b98c13bb1eaeff303d1cac000000,
  unpack 0x418a53f0dacea2cddea43d37bf1640eeaefcfa03806dfa800fad23e910386037e73027ea4241de81ec607af700838000000,
  unpack 0x41f7e6700e4fb78deb44395d178390e88c5cc60390ab7da7e627f698de77f75e23bb5201cb821f5de023f006016f0000000,
  unpack 0x2a949ea99bd47679060eb091eb103ef3a7a980fee7dd8203ba99764925bf33c83dd0329e4600ee827e700002de0000000,
  unpack 0x28e3d728fefd0a5f5283eebef0a50fec37ed5a7a4ff9761ddc510399a27c800e7187e8203e402700197d600c380540000000]

private def t10 : Array ℕ := #[
  0,
  unpack 0x7e71f86e1d058b82147b628ef801c9fb3fdb1088f74f7153d80072300e5842faef0813b004395720a08e499180000000,
  unpack 0x41bf75f6690e91e9ff58bd479490e930beae03cb65fd772cefec1039a197f49707bedb10054470031e00000000,
  unpack 0x29e49fcb18f4801dd0c3b64578a80f8413e6203a89ffc400e8e0ffd2180ffacf12feb8409d89942200be920645e87a0000048,
  unpack 0x17d84e4ad5d502bd71c7e42ff7801d666ffd407fa99fdc01fc60f982070ef8fc001fe427d04074524ece10eec20179651e4b037551e87a0000090,
  unpack 0x76517709ef7921fec43cbea7e440fb491eec03e627f8c80e742de910384917f50303b00879aa224727a1a921000000120,
  unpack 0x93a07bd46e1619d2843c3aaff280ffd13d2403b0417f767b01f6981697fe63283f5c604eca2ed2002bc91044e46d8661efbe8f4000004bc0,
  unpack 0x126fe28e9c9a0f92d87d26eeb501ea5c794407f0e1f1801e6c739a0071578fa88a07f40039000000009780,
  unpack 0x97bbd7ac3a889f9db0e79d5cf243a44a7e080ef623ea003e421ff660ec1fd69c1faa796f6691990340e0390007200012f00,
  unpack 0x83b9bbfb221e7027c44c7e804ea401cea8bcc4073a49f9101c778fe24875ff5ea04f763813b93350c0e790007200025e00,
  unpack 0x20dd097d76d71ef8ec611dbf57fb2076549e4501eb8af95407b81ef2881ca98bff33040e000f7d0f4000004bc00,
  unpack 0x1dc35d2313e85f75a08f88c5e9b03e450fe080e2fa5e9003978478440e1ed1f95d02eeb1827763d5dfe607be87a000a800,
  unpack 0x8bef79346e347be32c3ee9bf3ed0fbae1f2603f22cfe880f9251d92a10fad085777ed807b181c800015000,
  unpack 0xabe07c78cb811f7f4a8e3d5ff72438ab17fd6a469fb592ec7f6641f1f94009ee968072e087d77808fc0393df7d1e87f32a000,
  unpack 0xfc4f22ddcb8b3a11c76a16ff8f26bff9007ca25fad250fa400e4b91d5b11dd8729e4600ee827e701c800054000,
  unpack 0x286d5c71939213f6210eb311fc243dd22f2180f1997ee9baf8fc6632f1c9093f54b05e475445d3620000a8000]

private def t11 : Array ℕ := #[
  unpack 0xbb7cfce403aa2076b10fe313f7143abea7fd7727fc920386a47a400e4465fda5c8faee0c23b34ebecc12581800000000,
  unpack 0xa0bdbfba63a0cdfd37618df8343d7f6f2b80f9de5f9003908affc66b75f800388c5776b403838bf4c5800000000,
  0,
  unpack 0xe4f9f2510e6303d48e3956a73400f40d1fe603f42ff2c00f473be910385ac7e50123ebb8808ef4a8755390000001a68,
  unpack 0x20c9b8b98b379ff7f9211d56ef9c687ecfbe1301d8c07f6407cc78fa9c2c738e4774a023ad2af4c5baa9fcfd0f400002288,
  unpack 0x107366dff8abcc20fbb38f3c2dc930381097d080f64f5f3a03b0ba709257f4360ffbca49c9c21dd0422f2ca3c9606eaa7f30000002aa8,
  unpack 0xdbbfcb4bb8de2f8d08e3237ff103c53d76280f7389f2203d1b9fd666411fb59441fd6a483bd29b0000000032c8,
  unpack 0x48ef743f0e2f89e76e3b2c8fbcd0f9227f2a03b0667a400e005df699e717f61323a00a387564045c0f7d0f400003ae8,
  unpack 0x4862bd7b07d2a3e7b51c6d33906875ec1ff401e644fd3d899f11e28ffcc410bfa5449d94c10fab2b64603d0f400004308,
  unpack 0x2dd3f9121784bae6751ccc9388287cdaafd001cb04fd6407f2d3ec96107688077614a3bd2b281fcfd0f400004b28,
  unpack 0x4f6f3c97a77d1bee431dbd87f30074c45f8601f1e03a2407a1e9fb8c1e8bff37dc9fafc37a7561541c0f7d0f400005348,
  unpack 0x18344e24a9f9c87ba447b3adea821d9b07d5407a0f1f0c01fd2cbb22421f9f44aee800efa6ed2bca603d0f400005b68,
  unpack 0xb235bd49a3f82efaea8f85fddd003cdd677280e0e97ee9fb3ff3040e5aa1f8003dc64fd63023bd3abf40f7d0f400006388,
  unpack 0x12c7e6ace7541fae03845af6410f3837cc203b3ebfc080fb113f1997997fd7a385f5dc01474500728ba800e07f30000006ba8,
  unpack 0xb4c61db053deee74f88fdbc9dd203f41171980f80effadd0897fc640e1fb5b0817d77fadebd580f7d0f4000073c8,
  unpack 0xdb7a2ea78f10f2671ff71ff639516e7001dd867b6007ce3df4881c5c43ff31102fad40074a008ae0390000007be8]

private def t12 : Array ℕ := #[
  0,
  unpack 0x2b057f74a7be95f9e11fb11b8d607e5c6f96f9a57a2407b59cfb4cc5cbff34188eefa001af400190000,
  unpack 0x173893c6b97974afbf41dc867ec007fc88ee301ec6b7edbcdf0e6881cb08bff37180eefdb0064f7df7d00320000,
  unpack 0x20fe033aac7796a5f6771f7e0b944873c4ee6401e96f7dd3c4dcfb4c2863f0007614bec605e44c894711cb939721ecc0000,
  unpack 0x12382f8921c84e7961875106fa821d1fb3e8c07ebf2fd001c8d43d22c71fd6182eed690706b2981cfbfccf43010380000,
  unpack 0xf9cafcd1ff6121c6a63e729730d0f1cd5d09a38a7df2480f7093ed1039d6d7ed78311ddd920e003efec680701cfbfcc7a1900000,
  unpack 0x15f1ffba7571b80efc61fb41fe5487831dff2e91d3f6baa23f8ccc343f6b79c3faeff9a19b9300e4e7d0e6600000,
  unpack 0x56f95ef235e86f3ee8877e4de7c01ef383f08070595eea1f17b440e4e15f9d44afaeeecc3bd5403dfe67af58081c00000,
  unpack 0xcb2bfa720ee83fff863f6bc73200efc45c8a03a487fb434dbe53208afdae9937bb94c0073fcfde4f799800000,
  unpack 0x55bb4e5419d60efeb847ab80fc8e1d13f080707f4f6d25f7c413fff6b08c1eebc90f7b080723d733000000,
  unpack 0x16bd43fc3e7a10bfa011fcbb3f0407bcdcf9001ea9a3edb1894fe081cf86ba5123ebbc4b401ef232000000,
  unpack 0x20f4d0fa2b3f05f3e1f71c9a6fba40795d4f87d1d40a3fa0078bcaff8c7af3ea0d83f5a400727bccc000000,
  unpack 0x1bccce0dd5cee57ef1c7ab3cfd0a1e0427d780735acff4fe597d2498dfdb802e2925ef7900e79e7d98000000,
  unpack 0x58ad6ee571c5ef79f5470e75f0681fbfefa880785bbfd6e3f33feb32b4eea4aeecc1070015f0073ef330000000,
  unpack 0x20f1b0fdaa974295f74f1e74839f2071f0afe601e0e3bf5bc7a6faccda73febf709fad2003f9b20000000,
  unpack 0xc260e6615ff533c0d470a83e31a1f82fffd5074405f9c01e8163da0071baef6c484fa080e5801c004ff26938034712899b5ccc0000000]

private def t13 : Array ℕ := #[
  (0xeb0a887ee83e8e21240cb0a13fb055d1853bd101c64208801a3540011b8240008a400000007d <<< 639),
  (0x3c40904c071b42341eae710a06242f70123379 <<< 795),
  unpack 0xfb30720a4e308df0863dd4173a00e6c43f6a0381eefcc80e2bd7d90462fcaa007d776803200000000,
  unpack 0x5cc78e4035d4933f05c7f5e8eec01c5dc7c4c07a969101f3f17856cbeb4307d8c0bc899128800000000,
  (0x71bfa3cc9e9075f10ef097801edc894001476510025e4288070e58000031001011a40000000000001001 <<< 611),
  0,
  (0xe771ad5c1fb38c801d8db68407f6cae0069a01001e6e0c1009e418003e2240003a00000000000021 <<< 626),
  (0x1661e5bbb1a1b0984336c4c40508d7c000c39240049790a201c39600000c40040469000000000001 <<< 629),
  0,
  unpack 0xb3cf3fc343a5f3fa828f5b79d6003b9fbf8980fa881dd18f0fe843d7f4740f91007908000000000,
  unpack 0x106afadce39b9d307b710ed5add2903a72c7f764e53ff5f26effa64751f8003fa168000000000,
  (0x51e6fc6cbe626f651648661a09bb5a4d <<< 819),
  (0x4071ab11be64604c1e27450417d996400623da0029ae60100ff42000134200202101400000001 <<< 638),
  (0x104c904eeabe973900a0ee89083d61280af542080117ab4401612a000f442000008200000002b <<< 640),
  0,
  unpack 0x52e12fa81dec637d19c75d9efe081ea32bcc00736ddf5101f4727fd30588fe906575580f103c9a4f0091c4a374d9cb60000c8000]

private def t14 : Array ℕ := #[
  (0x19e164b7e903e2ac1a633cb40c09409a36db300035f8a5100b0c88002952c8002dc94000000ba02050120001 <<< 594),
  unpack 0x20f7723885affc24f5451fb4ffc2687dbd2f04d1e58ffd20295fd2b8affcf1003eae241c006dfc59c5fa6800000000,
  unpack 0x2f5e7e0aa396ebff8b0ece9bd0343a19b7fb00f11d3fe9a5ee7a400e6845f80039ec57d7b893945bbf4dd0d49080000000,
  unpack 0x41a0b1f8b5aed2a5d08a3d3b9797d623d84073629ed801d23d3da0070460fad0c077698a7945bd0000000034d0,
  unpack 0x4774fde08744bff6b01ef6ef87687569eeb101d0daff24075a85f4081cd583f6bd5c9faefa033800eba8303ebe4c00e3baa6ca803abc800000110,
  unpack 0x2f34bd16779e54e1771ec513b8687b325f30c500ffa923bff5846175a457d779c01ca2f54448e4f4352421efbe8f40005550,
  unpack 0x27079f1833dd08f8738f96c9e0b03aa9773900e1317d3203e7bbfc663d05fb5ca257d773c43ca2c000000006590,
  unpack 0xfebdfb4b6f99a7f6ca3a599f2ac0e877dfca0380d8fcc00e730ded10398bd7fd65887cdc13ca2c022bbb32082e4aa3754d950075791efbe8f400075d0,
  unpack 0x4188ecfc55ae1459dc4c3e4907bcd0ed621fc60385667db7b48bfd991797e000ee293ddc80ce0032e4163f5001efbe8f40008610,
  unpack 0x2f934f9466f1791d4ae3cdddf5a50ec259c8c03851bfda66c5be810393a07ed67313f52a29e516ecfd000000009650,
  unpack 0x517ffb6539f627c9a8e30c3f8a43e0a37f100e9235fb5931f7a666175ff5f605f75a80394581247007bcbdf7d1fcc000a690,
  unpack 0x3918b832e7899ee0631e422ff8407f9a4f7401d90d3eb898fff59c307e752038b8a794586387007bcbdf7d1fcc000b6d0,
  unpack 0x5e1c79250f3533fd741f1947d04870adffc6d1f07cfd2407ac01f6801c6a2bf0007100ae8329e517b8fd001efbe8f4000c710,
  unpack 0x6eade2729de47f879c7bb4cf0521e737fa4407ddd8e5101ee2d3fd33c18ef5cbee9306700157b200fa807bcbdf7d1fcc000d750,
  unpack 0x1079de1e730b8e6170580f0461eda03a8fb76200efd1ff800396917645aa3f25291f5ca0de4377801f500000000e790,
  unpack 0x1060057db07ba365f7030ee581cc9038e89f986ba03ed54bde6801c8c0bfeb7d0be2a21e0026e007bcbdf7d1fcc000f7d0]

private def t15 : Array ℕ := #[
  (0xb8151ff137c6bb9c7eeb116028d6244005eeb40048459a201f88504002e110401294000151140001 <<< 625),
  unpack 0x4cebde1a39557ffe18f214dda00398c0fb180ff7e1fad8379fb000e70a5f90188eefa009420a3fa0f40206d70000,
  unpack 0x9db6f30adcba2ffcd477602fada1d3857b8c0723dee9901c3b2fe332c6afc001c6427bbdac0009239c9efa3d000d0e0000,
  unpack 0x8ad0f446ef5ff1fa8a3fa46f8250e1fd9c2a0382b374480ef3d9ed1039b147d4512baa083a28a3b5dea757887f33d018101c0000,
  unpack 0x27db1c8a0386bf737b8ebc1fe8143f805fc280e581ff9203b9e473400e4a11f9c188eec28070e90117ca60fe7ebdf5ebd1036b80000,
  unpack 0x1f751f25e9c5effb6947b7bce6181e9b9fad00738a7f5801e22bffeb043affae242fbbcac008af1b81c820b92a8dd5365401d507bebd7bb00000,
  unpack 0x3a3dfc49674912f4521ea4538a407a7fefc601e755ba4407efcfe2881c2ccbf3be5c0e0e05ed961c2d23b93d4211fcf9e4e793a00000,
  unpack 0x2d62f783d6e7795c5263d4a477a40ef66dff9fa2978c00f25d3c9103873977a047d761621cc5c110754f655a0e473cec00000,
  unpack 0x9fb3e8b4dcd267dd007d994f8521e845bf5807f730f1101f126fd22072acaf8101d3b1393823881c7a00ae0059c038390507f260521dd0b60fadbfcf9fe67bfcf0203800000,
  unpack 0x83a0a2fb5adc692fd2c87fc0eed581da65f990072497fb6f163be530a0dfdaf862baa02380001d000000,
  unpack 0x419545f7910e8087f0cc3d7827cc40fc469fea03ac0ef8c00f8151d91039bed7fd6d393dd0428f2801ef3ebde76000000,
  unpack 0x53ee1e122deefa7ca5c7a08be8121f9e43f5007aacbf6901dd87fe531efefceced03a98b38f407003f9bdfe78101c000000,
  unpack 0x2ab15fc25af5b03dc843a7defa2c0eb6f5fd803dc227c880e64b9f7181577e000e1307c5811c007af702038000000,
  unpack 0x83754ef3659c6dab9d9070c75f9321c533390c07dc74f4d9a3fc665839fddbb61f52147f400fe7efbb0000000,
  unpack 0x2dcd17fd00f5e6fe1fa3e5b47d440e95ebd8e03effefa4e28fd22072e74ec101c282bea8c05f8003800c080e0000000,
  unpack 0x2e3072ba0f9ba5f40439740f9290f2433f2683d34e7c280f2defe900394727fb7b387e8203c3917001eec0000000]

private def t16 : Array ℕ := #[
  0,
  unpack 0x533b72e90f0b37ce8e39bf9f0850edb43ee803b395fec00e3a7df7193917e000fc201f5dfa0096d580000000,
  unpack 0x41d5b671a66fab11cdc23db3c79250e954de8603c63f7a880fa863c3bf5fb5e404f76b000248e00000000,
  unpack 0xb5fdf1052e8dc3f02e3aac1714c0ea863de403f9fbfac80ebbafe91038e517fd62901f58500e0a28ed77a9d5800000000,
  unpack 0x217176772f17b1f22c398b770c90fc087fac03d4357fa64989e110392f870ac17d480a3bd7bb2022e000000000,
  unpack 0xb13b1f5833bc4979e38e7043f530395b179800f3f9bf5de6407fa67301f8003c420fd580a380115dd9904172551baa6ca803abc800000220,
  unpack 0x81ddfd415c181fd1507c138ed8a1cbe0ba1c07d1b6f4901deed7d80070998fca8817d765c1bdb2cb941070086fa8423de4720000440,
  unpack 0x1062acbea8639ba3ff588e6efdf88038c7cfa100e9c81f22038db6fc662ec1ff9b22077553170441d53d9569c800000880,
  unpack 0xabedfa81dcce7f84547e1aee5581d164ba4c07bb74f8901e012b9a207220afaed2207bb9411c40e3d0057002ce01c1c8283f930290ee85b07d6d7bcbdf7f98f4000049700,
  unpack 0x3db95cf003ce49f6030fc707f6003981a73a10f6c00fe9bbe931b8fc001fc7238001c800000092e00,
  unpack 0x20d1783929a7c333f4621f0e5bd4607f690f0701fa0b7a440794d0feccb6abf32901dd8028f2801eff30f40000125c00,
  unpack 0x1139fc1c6f8c87c9e83c0b37da00f3d13e2c03f3677e880f3871e51039b007e080f1987dd8a24e3d01c00f7d0f4000024b800,
  unpack 0x50e6eea349e2fc7c05879de8fb181efe038c407a752fc001cde17e333d9affcd4123ba000000000497000,
  unpack 0x2a8f7eac6f25c7fa8e3c5ad750d0f0ee3dee03f371f2480ec8eff6997f57f764a05c4051fd001c9efbe8f400092e000,
  unpack 0x20cea4f9b0f716edfc311fe75baa08759d9fd701fea838d03392207260afcec5303ebdc15f800380000000125c000,
  unpack 0x16768bfee370478f4771f20e3f6007d53be7101fe2b3f53d3ffe25d2ffccd3238142fa008bbd58ba6c40000036b8000]

private def t17 : Array ℕ := #[
  (0x6ec6cd48b7594b28b7e438d0fe37f300778544801043304039aa2000950b0000a200100150102081c8080005 <<< 592),
  0,
  unpack 0x20e2af3defc73602fb331d99eb970870745fa001c3ea7f2407ee3ff0881cbde3f00073100e926cf2376900150380000000,
  unpack 0x20eb19b82df7650de0911d1eef926075523f8ecbaa3f60071aedff8c7a4bfa5883f5db40070084e79000720069a0,
  0,
  unpack 0x17cf7f31abd19275f80fe5abe4243a17a7bb00f2729f8003da61fb040e0471ff5e604fd71813b28bb4800af24411391b619f3c9efbe8f439002a0,
  unpack 0x41d692fa308e09b5c5263b844fc850e49effae03bf7372480fc547f2987e57fd79193dd001c72601cfbc8e40000cb20,
  unpack 0x6345bfb9e7f414ea071f13b7d8287a787f3401f551397a779a0070dd0fc101e830382c97b65878a08ee4f50847bc8e40000eba0,
  unpack 0x14a0797f571b15e2571ddf7bbd607c891f4601d9423924079714f4881ce923ff3508bee939070045f3431c8017f40474491044e8476d21efbe8f40010c20,
  unpack 0xe59afd1baea5ebdf8038b6ff7640f87b5fcc0394d078880ead99ed10392f97d5360febb6200f88c007bc8e400012ca0,
  unpack 0x18e49d841bc1157c980efa51cb943912c7ec7bae1e1203ba747a47043f36a85f52828eeac00e41c8e40014d20,
  unpack 0x32039cfd73be0e773a0f8739ddef68f7201f8447f53a173ffac5f0bff3ec03faec881780aa7001fcf901c872016da0,
  unpack 0x3db0f9891d5be3a81075944e8d01c9383fcba0f9fc901ffb37c22073882fabe65fd770409f298000000018e20,
  unpack 0x11c1de5f6dcb02793147d311ef021d93abd90074f7efcef31e3d82073a18fcef870b8a0a3edb8a08ed4073fcf901c87201aea0,
  unpack 0x2dd51f1d8ce075fc40e3fec5f4440ed8b9f0803a8b878880efcc7ed0039aec7e000f4005f56800eaa01e2823b501cfbc8e40001cf20,
  unpack 0x106e529cc533ecf1f5db8ea727d9303da4275800e7d53f9dadfe7fa62c71ff9f0c4775ac87f20001c8e4001efa0]

private def t18 : Array ℕ := #[
  0,
  unpack 0x20c722382aa7e95ee1b11f963b8a487edfeee201c13aff040768e1f6881c68c3f6bd400ed56801afe6e4f4000b070000,
  unpack 0xbdeddeb3e3e0b1f6eb8f6395eab43a051fa100e8dc3ed98f9f8cca82bfebcc80eef4007620163873de7dfe6008160e0000,
  unpack 0x56effb1f47e96dfbf11d8a779a2072943ef101d65a7e64070eeef48ed9756e5fd7764d88240553e23973fcdc8182dbc0000,
  unpack 0x30973f0adb919bfeb18e5937ef843d8557f380feab7f6de3677c46f0bfa6b15e820387867651043eacb23ca607f3f7f9b9f41058380000,
  unpack 0x5079f1afaee273f5ae39a3afc8d0fcdb1fae03aa80feb70b77e90eb8ffce8527b98979120b1f5a01c07f3f793df47c300000,
  unpack 0x2fe81f7252f576dcfc23b267fb890e733bca203fb85ff77f43ff1999057ed7c317ddd96008bc6d639002fe808e8922089d08eda5fcf9fe6f7f9f2f8600000,
  unpack 0xa7ac1f934b90ccf5b88eb36bee803fe0d7d862137eaa039b447ca63e25ff5dec5f0ad9ef223f01e5356d9b92d653fe639e48400000,
  unpack 0x59dfdefc65f6e4fee087be92ff4e0b67f0c070e87fc101e83cbe20ed1ff58c467008de5e4bd68cc81a07e44ba001fdfe7fcdfcf9e605b3800000,
  unpack 0x106e393fc473e69e75f20e896bd2b43ea847b4d5efe2407406ee4881cd347febb442e4129d6483e13422ae4129f01a3cc30888712b0797f9b93d743000000,
  unpack 0xfc85ec40dc0227f4587f6a4f88a1f2c9f9d4072779e5d01ff237f632772fa9c84f7d3000fe7fcff9ff3e86000000,
  unpack 0x418b3af308afce21f962396a57b080f3655d4603bf6b7bc00ec685c5103963c7fe69211c8f03860475a0039fe7d0c000000,
  unpack 0x58fbefc495d2cbfee1077ad0e5d81cabfbf34072427fe8aa7f8440e62f1f91d48f50cb023800f7df7e18000000,
  unpack 0xa473fea073da147bea8e5bcbf1f03e2d67b880f695fda003d1bafda650d5fb58e6073c00f4801d6801fce10000000,
  unpack 0x41b4a4fd7ccebeebea70381ed7b200fb90deca03dd77fa080e67c5e999ec87fd7d217ff9d4047001ec20000000,
  unpack 0x4192fd729f8f72c7dee438a39f0e50f6f1bf0a8398ce78600e3dadec0038cc17eb79991f4203960470018201c0000000]

private def t19 : Array ℕ := #[
  0,
  0,
  unpack 0x6590fbb3ee52adc48a3ddc47b080e94c9d4e03eded7e800f4361f11812e7d88ee800ec402c70e00000000,
  unpack 0x1a290f6f29c42a7dccc70ff9f3481ec587dc8077467ffcea4c3b23541ff5fc80f749493bf18240553800000000,
  (0x273d766288c104fa07bb4d8d0429d598098392400dda420401e306000f440a0008a240040cc1020008040005 <<< 596),
  (0x25ef9406495bf10388cc6b040d727d800d1d024002f71b04018124000600900006e2d00008a1820b1 <<< 624),
  unpack 0x1064ee5d02ab9d9872b18f3df9f2803ca03f3980f26c1fa9f84c73400e75e1ff9bac4fd63c838022fc46400bf2023a2488227423b69e7de5efbfcc7a000540,
  unpack 0x10768c1fe39b81e1f2b20ef9bdff903b3e3fc080f0cabfa59e8578440e34e1fd194be14b3d4887e031c00eadb3725aca7c800000a80,
  unpack 0x815ef77bde7fafe210745abfc581cf297c140702e3f5001d097bd02070daafe80e4f200df164bc8990340fc8974003ff3fe7c8e403901500,
  unpack 0x13423e9fbba8d97ffa0f37d7ed843b994ff180e19adedd80b07b440e7cb5fda860129f44a3e134a2ae4129f01a3cc30888712b0797f9f200072085600,
  unpack 0x20d5c9f9ab1746fce2b41ccabfdf087d6befd6edf33b1407e6c3facce0abf0007754afaeea003a2823b501eff30f40010ac00,
  unpack 0xbdd2deb58bc7a67db30f286fdc203e6defc970311ee9b6f1fa660e11f8003f0c5f03c0e001cb91fcc0000493800,
  unpack 0xae53fc052e57f5d78e3e70d75c10ec77dd2203904afcc00f2e93ed103994d77281f0580e001cfbc8e40000927000,
  unpack 0x41d425ff99ae6479ec2e3d6bef5840f08a3da403d96f70c80e2b95ed10391207f795078e007000fe7fcf97beff31e87a0124e000,
  unpack 0x1063cd7c1253a625f4110f6befef903e228f9b80e4d79ff9bcda715197ed63b87f8203d4007450476a03f9fbc8e4000249c000,
  unpack 0x20ea59feb4e72da5fae21eefbfd92076b8aed301d1d8fd04070f6cff8c4eebff3314bee101eb887a008bbd58ba6c4000005b38000]

private def t20 : Array ℕ := #[
  (0xf1d4de6678119d30016e56c0731ac280a9718c009d04a0401a8a8000f18220015d0c1001 <<< 656),
  (0x1dd10e99436a421c591ec6080ead8940530a200076c512200e95000010e4004146800005 <<< 657),
  unpack 0x3666386ea705d4ffc21c36ab8d687e4f1fb301d9cb3d0407d265e4881f719620ffbbae05e1c00e8840ee432980000000,
  unpack 0x732b7df557a30af3a11dc8d3cb2871fc7eb501f7d0bfeb792df94c60cbf0007d40affaea0238f42d39000000d340,
  unpack 0x41fa59f0ff0e0561f8c03d0157dc10fb50dd0c03e4e1f8c00fc3a5d91b78e05cafeeea023a0883bd7b2800000000,
  0,
  unpack 0x9d2a7b960f6aadf08a397e1f2810ea03de8e03cb15ffa65e91c3aa5c9383fd9920e2a000000019640,
  unpack 0x3cedf999cf2ba7cb6c3de597c440fc361f6d910c7d76b1ade500394197fe62911fd54c5c110754f655a73c800001d740,
  unpack 0xeabee6fb5f4c5be8487330ef1581cf6efc8c07ceffe4d01c9defeb3081affaf260fc56cf5221f80c7003ab6cdc96b29f3c8000021840,
  unpack 0x832854fc905c04dbad987f9d2e7081d9e97f0407eb3efc101cd29fd22070e30fcb8257a088f5011c7a0390000025940,
  unpack 0x7cbcf934dd7643a59c79641f1c81c5bdfb9c07a762ffccf0dfed31cd2ffcda52fd0557fa6001c8000029a40,
  unpack 0xdedbfe4fce13abd52238b63ff640faa63f0603bdbef0e00e3e4dc910388c47d4b00fc0687fc6001c800002db40,
  unpack 0x77857c8a2ee60dc0263a88f72e50e37a5d6403b932fc800efa93cd0039c4170485ff977811c7a01c8000031c40,
  unpack 0x836b42ef7b5e8cbbdc547d25de9c21e58f7edc070e43f9901e8653c82070768ee871441c00390000035d40,
  unpack 0x41da7678464fca3de5ce39ede7a240eae9dd6003983676c80f9583fe982097f61503fbbfc6001c8000039e40,
  unpack 0x41d06c73532eff97cde03a029f4cc0f1e8dfe603edbf7c400e24f7e11039df57ed7c085ca20380073c800003df40]

private def t21 : Array ℕ := #[
  0,
  unpack 0x41b2dffb656eeb1dd428384bb7bc90ed903d8403f28afc080ec86bff58f8070004be6fd07a0250000,
  unpack 0x16bf83cae97ece6fab01fff1bd34078367f7301c2e2b9600725acfb4c87a3cd007e400dc67f37a004a0000,
  unpack 0xa4ea3f92a3983370b30f4189e3b03b2b2f747c37f00070128e6081c5ccbf6b0988faf00270134e23d0390940000,
  unpack 0x8b91f3a28e5ccdfce038c877f850e9d0bda003c0a3fcc00fc1fff718581702c57d775a41c25ca60e7df47a1280000,
  unpack 0x59c5f523ee3989ff4c39d8afbe40ed59df4e03f31df4c00e1aa9e510392807fe7eb01f5dfa3b30d00e03f9fbcbdf42500000,
  unpack 0x41d85475e7ee1d77dd2e38bb9fced0ffabdf2ddc077fe7988bfd3caafc001da40792803e23866007bc872f9600000,
  unpack 0x3f60fe66cfb1e9e7203ed2cf7ed0e61a3fcc03e993ff77ff87c51039c057e75123904478e18ef5e80fe7e9e89400000,
  unpack 0x83fef9f7a65f1087a9487f78be15a1d1acff6b5a45f9101d7adfda00720d8ffcdf13fea5811c7a03903e5800000,
  unpack 0x1bb0ff0e81de0cb93d075368e0521dfa17bd007e606f6e0e4fa440e1c63e8013b0a47d614a3bd003de474b000000,
  unpack 0x3d7e7f044e8ccdf48c3ebeaf80d0e5a4fd0603f6ba74480fe113dd1039b147a020eab95f5a808e3d000f96000000,
  unpack 0xd3a7db1efd597d68e3c273f5cc0e6137d6803ebf4fd000f6447f7199907d5e40f8b023800fe6f5f2c000000,
  unpack 0x83262afd801e2dabca087682be0d21de64bd4b39e1f74e098fca20717c0f8201fcdebb8528ef4007328000000,
  unpack 0x20e80fbe0107a29df3501d1effd2e07a688ec701efac3b2007e097e6801c5d039600774c8ee8007f3f650000000,
  unpack 0x5779f38fbe39777840f5829f7043a106f9200ef333f69daf6ffd60f81f5fdc9fafd31e804a0000000,
  unpack 0x167a2fd44e75d0ae4621e14abd2407783cf3641c1f6bb7407ae96fa843571f24f0107fcd9616fc46a2dd9fab949a5b8ee5fb8401c0000000]

private def t22 : Array ℕ := #[
  0,
  unpack 0x2b7677d7eafcd5dcce43a2f1f4480ff153f2a03d06df74cf5bed33370fdacc623ea004be80000000,
  unpack 0x559fe7b79d80a3e5807ae4af9581eb6f7fdc07f95dfd801d83b7eb322c0eb401f1403ba00dc600000000,
  unpack 0x2f92fcebc71102ee201d4123a72870b1ff6edf297a240772d1f490317e000ed181f5df00270134800000000,
  unpack 0x5f79ddad3c375fbab0ed445d3003f57a77b80ee4f5eb003e3787c45e039d9a348384a000000000,
  (0x2bca6d022427798a0482ba94033582e00d8df100144a8d1000bc800023524800230000000000003 <<< 630),
  (0x2d4f479121330d528a57a0e505f8b79005645000021ba94401beae000e84b20806200101 <<< 660),
  (0x76b8cc571719ee960c48170215490f101762f0101208b280030150001ea90011 <<< 691),
  0,
  (0x1f710c512c42d6ea2f93d79000d3f6e00a5b4a202879a40008cc2001 <<< 722),
  (0x1885e298e06ed6494547da568795a6d8034dba2003c9bda0007c8001 <<< 725),
  0,
  (0x14220b79e0c649508b4103e90f3633b00d22e2c805ebdb4400502a1 <<< 728),
  (0x6ac8e72c821f1f0a3d35f6343abb9ce00233b1203553c400066c1b <<< 730),
  0,
  unpack 0x134d9e2d73bee0feca0ecbb5e9803b7bb77980e0b27fb5c9a3fd662af1ddc9396a177370649f119d9a5269ba7b8c6803fa0003e58000]

private def t23 : Array ℕ := #[
  (0x247e8c19e763d46b0bc474090a1cffb80ab9c20009561a4001a7800015d03208d <<< 688),
  (0x4d1a50828130a1211c812a020e392d00078a749002630608063740105599600053840001 <<< 659),
  unpack 0x154ac3ce3a7725de1a71fd11bea087767b101c7037f6b03b4ff8ca90be4007a501e6c00ecd2f5c897400380000000,
  unpack 0x772a7bdff72b77fa601c3e5fde6875dcbfb001d7e2fc4407075de6801cdc43e4b8bc2faeea0238f40390007201a680,
  unpack 0x926ff011de6b2b994c7eed8fd4e2893b840709edfd4e9b77fb30dd8f5001d2403ea9049d5401deebe4c3a03800000000,
  (0xf141f6510e3c328608ab521419ba1c0022a70220085c251009d22a0018c0480013cb401001040000001000d <<< 598),
  unpack 0x107c34be16bb88a4fd1b0e982bd91e4f475980e572bd3203a09d7c40be3f40077f80eefe3001cfbc8e400032c80,
  unpack 0x1eae3f38f5e866be8487a9caff8c540bc94079fd6f1901d831b9a2070058f5101fcb27bb9411c40e3d0057002ce01c1c8283f930290ee85b07d6d7f3e5efbfcc7a000e80,
  unpack 0x837bf0ea8d5e8bcb91c470d06e7821e1b3be18072fa9ec801f5c27da2072768f9001f82279006f8b25e44c81a07e44ba001c00072043080,
  unpack 0x59d3f96387b8def2ac8d63a548787b8e9101f8523daef9df7190d47e800e2a15f5a808e3d01cfbc8e40004b280,
  unpack 0x5a3fdf18f1cedcfeb987d6effc881c0137d900702d1f4edf1c3d339579015d9923b8bb604e2061c282b8016700e0eeac1821dd0b60fadafe7cbdf7f98f40053480,
  unpack 0x11271f87c9c7347e290724acef001d6387b1807b0a7ed101ebefffeb1f62fd063df803bbf8c007a0007205b680,
  unpack 0x318d3eaa0b8060f5f30fb393e7a4385e6fe200f8861f32038d0c7b400e1825d2103e8617d767011c7a01c8000063880,
  unpack 0x778f02b8ed957ecc63d9e1f4890f9849e6a0391477d77367dcc10390bd7aa48e6381dd000f790007206ba80,
  unpack 0x2b703fb846e06ddfd443b4bd79600ecc91fa603e890fe880f89cdf198b5074270e6391ddfc60039fe7c8e400073c80,
  unpack 0x89c2777b6efd85e38638f5efb450ef01dfec03aa8b78880e4d41fd133afb001f002380039fe7c8e40007be80]

private def t24 : Array ℕ := #[
  0,
  unpack 0x107b9abc3983b2cdf4f98e1777cca43c134faa00ff485e9203ec5a71440e56a5f90188eefa00020af1011fdfe6e4f40034070000,
  unpack 0x36c639c027f492f5311d999fe8487103afc201ebc1bb2007ec8ff6801c2b83f39011f5ac05e44420888f6401cf7f9fbcfa3d04680e0000,
  unpack 0x141b83bf0e7c45af0b01f97efeb007e9fbe7301ea537d0407ad62f2801c21c3f0007ca600c47f373fcdc818da1c0000,
  unpack 0x1072d59ec163cc2ff94a8fb109f7803cf0b7a880e2ac1db003eff3f9040e3d51d0311dd8500e1d0aa0f94c1eff3f79f793d31a0380000,
  unpack 0x5a2abf9dedf6947b9947b08dfc9a1e5237c9c07372cfc001d4723fd31258fad640f77b08780491e340380e47a3d6368700000,
  unpack 0x41d13ffb27efb61be902393de7c690fdc6dda40387c37f726fbea0d25fb5ba64729b7570cc01cff3e7f9fa7286dae00000,
  unpack 0xeb58fff08e7167d48a3af01f9c50f4d1fdc403d055fc080ef64be9222affce5123905572610ef400f4e79f40db5c00000,
  unpack 0x83eaa3e49fddc7dbf8907e0fcf0821fa7e3c8407d87ff5801de807b20c21d802be32677176c09c40c385057002ce01c1dd583043ba16c1f5b7d1fcff9a1b6b800000,
  unpack 0x1d1d7996a756f3fc611ebd0ba5487608deb701e6f8ba6007b2a6f4365c0297c00379543e4d0ceaa10f0ba876dd9be47bcbd236d7000000,
  unpack 0x1a9a0f01bde4b27a2dc7b440fcd81f4ad3e8c0772b0e9101cffb3ea25716f8f8041f0403a80a3cb6da3d1439e7f9ff3c6d0e000000,
  (0xf1d9f6bc811c1ae80326283028064e403b3ebf20313f610e04adb20b1a90e80a264b44a42a0a02d900300280000029040000be580a82a000200020002000100031 <<< 426),
  unpack 0x562f6f312dea857b6d474a10f64a1c1aeb8a407b333ff6fa27b982072a8efcbaa17d765a41de801ea1b438000000,
  unpack 0xa7535f13a396dc7a628f8087df743aafbfb800fdaf5fa203d12afa780e3fc9fdf048ee8007bfce90000000,
  unpack 0x106a181c7e2bf999f57c8ec629f31438bcbf8a80fb27dd690bce003817a7e580238003dfa60000000,
  unpack 0x97767e83cf106fc7ec3d57bfda80e83a5cae83c8eefe200edf75cf80389be7fe61287f5a920ef4018801c0000000]

private def t25 : Array ℕ := #[
  0,
  unpack 0x836ce9e5bddd7dd7e6187e78df3481e59cbdc80765ddeff9aff8c81abf3c991f5f4000415fed80000000,
  unpack 0x29b88f6936e159be18c3fb07fcac0e60c7d6a03c645ffb645a7ec10399247fe73381f5dd602f222104447b200e00000000,
  0,
  unpack 0x7723f946cf8343c0623de3bfe650f9741f0e03f4cf77474cffd33662ffae420bbb4a01c7bb0aa0e000000000,
  (0x639960f4709a8321e10105a12ed85301c03110017ac740005e41000191824100c84200000000049 <<< 627),
  (0x71fa30dc77a1b8dc1357c34832a4b4800daed4403adb8a00148120000a6110001414005 <<< 661),
  (0x380f32f16f5d369842a19c6078c749c0696c824045a2ca200e04500040851055 <<< 689),
  unpack 0x83d23ff3dcdf7d4bafc07cb33f8421f4b97ebbf7d6fb4ec46fca0073b10f4015d3103b8bb604e2061c282b8016700e0eeac1821dd0b60fadbc8f7df47a001d00,
  unpack 0x20dccd7c53d76150fce61c5ccf9a407cee0f2401cff47d2407c5ade03e5ccc4ba0037b049faed80b38a843c2ea1db766f939e400003a00,
  unpack 0x4185a1f4a56f12abc8a03edfeff640faa11c4603b51970c80f5c41e812b9c007e564811dda028f2db68f450e400007400,
  unpack 0x1c79be2f39e6473a7887f7a3fc021e2503d580731eaf5801f76b7921c737d2ed059e102fd0547992de2521ea0a385b2776772d4821c5f960e5415fde41c8e4029d800,
  unpack 0x8593fe342ea7f3d28a3bfdd79e90f4121ec6038e97fe763313ff589387e000ea391dd000e41c8e4053b000,
  unpack 0x5ff94f6dc1f1477b9907c123e08a1cf13bf0007fc52f74ded27c3e0715d0ffacbf0380039e4f7dfe63f987aa76000,
  unpack 0xcc34e8c69c15679a0473ae0e94a1e9c0ba840768cffcec3b8f8e2072d72eeb80e000e41c8e414ec000,
  unpack 0x14e46ff5cf7a47cf7641dfa0bbd0074fcdf5001e1d2bf000705dee3481c900bfdb0949ffaca887a008bbd58ba6c400001a038000]

private def t26 : Array ℕ := #[
  (0x674cfd7c97e412e408438704163cb6c003053900202f4d1041e0300075304003 <<< 690),
  (0x111110858255f51986a2f682866a4c84009e626005edb1a2108101001 <<< 721),
  unpack 0x20d72c3b22874d82f1151ca5cfbc007f906ec501de1afd44071f5cfa8d787ed6aa93f5dc602f6510438841811c9e07c80000000,
  unpack 0x17fa9bfcdd73202e5e01d4417b70073896ee101e2cdbc64075223fe8a2d7e000e9101f5dd202f222159be4e7900072034d00,
  unpack 0x107e6ddc2b5bfb6172a00ffe0dfe243a0cafe9603f1f82039f01fca66435f8003f88577600a38a8039d36d800000000,
  (0x518d05eea18d8c20e76af04029fba8807e40ec007e75b40002fae00000c100808e04000040000000004005 <<< 600),
  unpack 0x3076dc0c33d6c671d10ec377cb803d1b175080e21dffdce91f6001cc0ebf2b897ddd401e42000000065900,
  0,
  unpack 0x1a269f8d9bff01fcfb0e68d3ddb03bf76f9200f8599da003d67df3400e6085f9a0c8e0129f44a3e134a2ae4129f01a3cc30888712b0797f9f3c8003902100,
  unpack 0x83d53af4e0ddfcbba0187ba24e7921eaceffc007347ff9901e355bca2070f10fa4f4403800390000096500,
  unpack 0x106a037ff013ade5f6eb0ed409eb143bb2372980e2a69e8203da9f7a1b2e67c1f801be064fd76c059c5421e1750edbb37c9cfbc80e400a6900,
  unpack 0x20f9d87bda37428be6241f2a5bc9007ee80f8701e681bf60077d69f200bcb24bd002fe5cae0131e8cb7882274e2ae4329f00a3d4b08887a59593a100ff5fcf901c8720b6d00,
  unpack 0x107c361ff79b996efbe10f6979e3003ed51fdb61513f69d77e78410e4695c8a01ddfc6001c80000c7100,
  unpack 0x20c0d1ff3c27dfeae1441d05d7f5087bd64fdac7f4bed334c9e6941ce223ff3f1c8ee80073fcf901c8720d7500,
  unpack 0x20fed3fbe997a8a7e6531cfa5fa5607eb6af5301fc507b400710e1e4a29cce6bfbe811ddfc6001c80000e7900,
  unpack 0xb498f221eec73ff88a3819df5880e6fc3c2e03e32c7a480f45a3c55039dc47f5142380039fe7c80e400f7d00]

private def t27 : Array ℕ := #[
  (0xec69cf18a08fbda8d2716ac03bddc180d874cc81060ba041 <<< 752),
  unpack 0x1afbfcd07bb40fff708eea3dd4a038d14f1900e8f57d8803a8d278440e64b1ff5ac01f5400f655003bbf4dd0f194800bcd72e4f40058070000,
  unpack 0x3663ba64d7b6cfe1f31f9bf3d7487d6c7f90ee113d4007b728e6801c95a3f3e215f5db50270ca1c4418e0073f9f3ef200cb00e0000,
  unpack 0x1f933edf0dc0fb7855c7e66ae8181d5b9bf630d98f1101c07fbb276f5dfa95df6d88855403e21cbf9b97209601c0000,
  unpack 0x41aaf4f655ef293fddc6390ac74600e4379f600384c9f2a00e32e5e9517fae1423ebbc008ea5da729e53072f79fe6f402c0380000,
  unpack 0x1486ebe78f7bc76fbf51ecbc7d40872c04e5401f0bb7db133bf12e08fc001fd00c70f1a01c07f3f793df465b0700000,
  unpack 0x1f911ed72b908c7a608f0c99e7143afe2f3b80e105be3203d5b2fb400e4325fb5f4e4f0502f0154f0cc00f79fe600b6ce00000,
  unpack 0xd8af411aecc93dee43cda0f2a10fd803da803a4bcf6e00e47d7f299fe47d6f427906873610ef401fcff98116c1c00000,
  unpack 0x14b567cc2c7875cfda11c0e23ab687a68ef9401e4b93e20071340fa9dc974031e7d89df8c007f3002c03800000,
  unpack 0x1bccf1005e1563cec8732e5ff101d85a7a5c07755dfeef3b7fc222f0805f400be932ba1ba605e2089f38ab90ca7c028f52c2221e96564e8403fd7f3e405b67000000,
  unpack 0x753cba43d72b92f2d51d297bc3087166ee7201ecb33a22c79d1afd8c2b6beab7040fac804745047b7f58147bcbf9ff34b6ce000000,
  unpack 0x8314aee2cf5cd6c7fed87b297f8821e9423fc407665de7119dc3f3feb0284fdacc90f91e070d0decf23d5dfe7081823924069dcfbef296d9c000000,
  (0x1021856dca7bf9e907f6e5090fdf256005607a095a51234441abee8146c8283083d211110c41005e4e0c8d20040004410000979602a3080000000c00040000b6d <<< 432),
  unpack 0x673dbd4b5770f9e4451ddf87baa872688fb001e5dc3964076cc8ec8e2b7fe72381c001fcff9fdb0000000,
  unpack 0x29088fcdf2f6ca5c2b038b337646ed45f8003cca5f8380f3899f199c767fd74805f52808e003dfb60000000,
  unpack 0x3960f33bdfb25b9a5c760ddf0821e9913941079524f8f81ec80beb329acfc9ae47029477a00b40000000]

private def t28 : Array ℕ := #[
  0,
  unpack 0x20f4b97bdc779f2cf3761eae5fea207c521f6201fd423e3407712df4801cf643ea7187c5003d95400eefd3743c652002f00000000,
  unpack 0x2d2e2f7f3ae5957fec03b6f57c650e69e5f2da7d37ba74851e91a68ee54aeea04e194388831c00e00000000,
  unpack 0x640ef93477f8f3fed51d9d5fef6879d0af2ee6b5f86407957ef6001c382bea7095df6d88855403800000000,
  unpack 0xbb09e6a3dd902bec8072692eb821e087bb8807a90af9c01d028bb256d5dc001f5df5b52efd3ca6000000000,
  (0x26d5906baa9e81b18a13008103f0dc100222ce880d7bc140008e02000558a2080b008000000000c7 <<< 628),
  (0x2ba13a2c1a5676e432c38c843268cca01ca85020013984000d7898000f40c82008814055 <<< 658),
  (0x11c6125dc19a05898cb55125072b92300a9b98e00c68010403d60000019cb005 <<< 692),
  (0x3721e882e36292f18a025d24060f7e30034cc0c00a000a00015e84031 <<< 720),
  unpack 0x832195e9eb9d17b7dc4c7a529f8cfd5f7c29565d3003add771405e0e95c8017c2257436665bc4113a71572194f8051ea584443d2cac9d0807fae400004200,
  unpack 0x2e21d72162fb3dfc9023d59afec90f986fe22038acff8cd9f9271e800793a87e56c381ddf368a08f6feb028f7f987a0008400,
  unpack 0x1ce1afa40dd250b89c0716bbefd81c81d7e1807b5faed019f80d7c820723e2eb981e0781c9417b3c8f577f9c20608e4901a77be87a0010800,
  unpack 0x41d2cf78132e89b3dc223d903f0650e3569f8803af427ac15f231fed1139d6974814e9085e0e239c04f1110e8821c1793f0647d200fca2087306f2c1ca8c3fa1efbe8f405c3000,
  unpack 0x3ba178f9d76061f9b71d2963a8287539ffc001c2577fbb2ca7fb8cdb23fb1701df8c007bef2f7df47f30fe6b86000,
  unpack 0xe493a15171c88f1b41d962f9e087c83ded301d4093b380782f5ec9af17e000f5d11c001efbc80e4170c000,
  unpack 0x14d257bdc47d5d5e1541f7d2f926876c31e9101c913fd4e072ca4f6881c9cabfdb7100ffaeb887a008bbd58ba6c400002c038000]

private def t29 : Array ℕ := #[
  0,
  (0x46439f0761c7e2dc2b0a8a20312e25c02728224105c2ca25 <<< 753),
  0,
  unpack 0x28a347de60e42abf70c3919ffa450fe89bf44038acbf6280e2b27f198d417e6522bea5011c7a0500000069a00,
  unpack 0x2421b8bb972868e4a41f7a87d4487e014f92ef36fa3007a59ffa85357e61523a8023a0823bf59e800000000,
  0,
  unpack 0x20ebf0fb29377bd6ff871f8307d02873228fd201f92fbb1007f7d1fecc718beb2991ddfc65a0000000cb200,
  (0xbdc5a31e19b73b84696fc5485c0759c03d42d7407468d820031d300000440040401401 <<< 665),
  0,
  unpack 0x20c747fcc4d7643ce8a61f56f7fcb1136f4301e881b954073961f6081ce2c3eaba402fad40471e80f7d0f40012ca00,
  unpack 0x15a477c7e675c77fff61e1d6fae207ea88f92e2fdba14078a9bf0895c0d03f0107836ed014796db47a28f7d0f40014d200,
  unpack 0xea35fb4e60a3f2883e82775e00f0ec7f4003bf9174ed8eaaefcd1038d657a020fc201d86d1411edfd6050000016da00,
  unpack 0xaacaf7706f86bdcba23c604fbc10f44e5cea03df9576a88f967fec1038ce47f6962bebb3808e3d01eff30f40018e200,
  unpack 0x106c8cbd4a23f8c970338f8cf5fc103fbddf9878adbfaaab84bf73400e7411ff5d0017d6a003a2823b50000001aea00,
  unpack 0x7197dfd0b9a23f4d88f4b67f68039342ff180fe121f19c3841e73040e7de1ff5e8457d4e003a2823b501eff30f4001cf200,
  unpack 0x5a82dfacf5d35a3b5d075059fcd21dde03f5b5c4de8941e6197d82071122fdac55038001c80001efa00]

private def t30 : Array ℕ := #[
  (0x8c21ba72896f28ec20982e940d2d424049776b23 <<< 786),
  unpack 0x24477dd26beab3738edb71c5903893671180ea6a9e9c3effe8f8070006ab37dfe6e4f407630000,
  unpack 0x52dbfa52ded22fcc107102ff34a1c560fdc407cd42fd6f819ffeb0c20fe80064c397f300620000,
  unpack 0x7cbbfbc6a78a71f8271da0a3d6007df80fc301e88e7f600743b4f4ccef8bfa7085dda605e44c81623f9f3c9c81a001c0000,
  unpack 0x82747feb0f8687c8c23cf42f7400f5a07dc203a2f9fed743e1f599fa17e000fc015da877dca6072fe603f180000,
  unpack 0x1c8d39edffbf0cec241cd3ef8c6872bbaf26d1d885be200769a9ff8cf34bf0007c18aeed68073718680701fcdfcc07e300000,
  unpack 0x5f9d73c78fda07f9023f26770cc0ea317f71f77672480eb7c3f10970fdac7307bb5409f29c33003d720d000e00000,
  unpack 0x2a16df0aaaefc39e7ac3ff8bfa690ee2a1d2c038e6bfe480e8685ff5862c76ae072280f3c31debd00e5cfaf79c400000,
  unpack 0xebf67f766f8c91dfa63c0fffbc90f5cdbf5dcb5278c80f2c83cd00392707a040efb8ff5dde0471e80f7d727b8800000,
  unpack 0x4184b678d26fa17be7e63e6e8746520fd94078233e5901d0ea3d808721bbffaf61a54a3bd0073cf231000000,
  unpack 0x186fd3d1db4cbde9c77a82e9581cc91fcc3c5a5f1011e802ff02071500fc001ff62fba7811c7a03dfe7ef2d000e000000,
  unpack 0x9490ee32ded23be9bfcf4e1521e45bbc4c0fb70fee819fa7979220711fafefe81fd775811c000fe7f8c000000,
  unpack 0x38cedea903b3f6f1118f24f5fc243d7abfd784e2d9bf32038a4df9400e73c1f8003c420f7604a3bd007af7f18000000,
  unpack 0x10666a3f1143c04af71a0ef605f6e438336fe330ed8cdfdb527e6881c36ebf0007b849eee530007e30000000,
  unpack 0x216776259eab3dc2943ec647be90f75fdea4038f377fa7a4c5f1990147e000f2811ddf47a03dec60000000,
  unpack 0xa2b89d5163b3d9f8370111de243f55dff9fce2e51fb823904972050e5d75e21039ee57a200f7c11f2980197dc701c1fd0464c5041dd8c0000000]

private def t31 : Array ℕ := #[
  0,
  unpack 0x41bf4efedcaea151ff4c3d90df6cc0e90fffe603d1bffe400f78bde92a8afdae1123bd006ab00000000,
  unpack 0xa8c61d9afbe0a0728b0e7f19eb903eada77b80f3a6dd1203843a79400e6b41f56540faefd0064c00000000,
  unpack 0x10f5faf06737e7fc851ffbbfa3407d73bff0c0273bb9b61f5986407fe77b05dda605e44c81000000000,
  unpack 0x5c4bd359733dfff851c2853b56074d84e3601e9327f20070784e4881ce6e39d203ea0efa000000000,
  (0x28aa9d4b54ca4c63053d42610d761e1e8ae6bac006e9d140039902000258a0080b500000000003 <<< 636),
  (0x4fa7aadbbe9e12c82ec6b28410753e6019ef430012db8d0000f688002232c820208105 <<< 666),
  (0x99f0ca9e40bd891c59130f2850201980357b700075fec200192c4000480411 <<< 697),
  (0x88b6ffd6396856263c2f64a03a56d0a03ee6da201cec25000344301 <<< 726),
  (0x1b42450f294be52888231f8004b7f8980536388004427a41 <<< 756),
  (0xd8745e45e36fe0000dfca5209fbf730188f4591 <<< 787),
  0,
  (0xb3c79f7780e458820f5416041120aa81 <<< 818),
  (0x21a944926d07b7500f1867440abd3fbb <<< 820),
  (0x3e1a62dc7 <<< 912),
  unpack 0x1cf3cfbd11efce7e4d4734def3581fe03794ae75dedf4811fbaf3e233c6afccd830fcb2203f29a3b8dd9fa0830338e0839c8003f18000]

private def t32 : Array ℕ := #[
  0,
  (0x4f6f35fac5e520b309e955c20ee3c41062298081c373c009 <<< 755),
  unpack 0xab87020ee01cbfb2c3c902fa440e7cb5d0c83b082fb64c8b922070458fe8404f770807b388c420608e4901a700000000,
  unpack 0x17219f7c35d3a67ab0c732cefc801cb417c2b238ef8901d7123da2070c3affcc6923ba00000000d3400,
  unpack 0x2f3537d27cee9ebe1283950976490f4f4de6083e16c7e61fe7d2207d97fcde703bb4c0bd1021cecd0007ff5800000000,
  (0x10596e11a9bb5faa212662042e89d2081547890023a08d0008daa00009d0802018c100001400080000203 <<< 606),
  unpack 0x1072015dfccffcdb79700e7181ef0039b39fb248f98effa9dc577fc66b45fb5f380f7d3001cfbc8e400196400,
  (0x66edd2d58e5fa3d31246301812ac9d1418c7b51012f3040001cb1c1014d96000114483d <<< 663),
  (0xf2921e1333fb282c10229c9002053848371f522010c50000095608001922c0d <<< 694),
  unpack 0x28cb0f6dfae6bcff48e3ac897ce80e1163f84838b307e880edf67fd98f387f514238003f9b91fcc00259400,
  unpack 0x5db9ff1b71d9f03f5d07f8b9f79a1d755ffd90792a0fc001c76e38a3c72ceafd059fcd2bd05471d2de2521ea0a385b2776772d4821c5f960e5415fdf5c8f47200a400,
  unpack 0x12703cdeabb5e7f6928fc4dbcf343f6cf7c0a0e39b1f9033edcdff661545fb5f9c0f03c0e4a0bd9e47abbfce1030472480d3bd00002db400,
  unpack 0x2f689c1b9bae0b7fda8efd9fe6a43ab2a7f821e5a1be1233a02cf2440e5271ff584a4f77e9800f7d0f40031c400,
  unpack 0x107ba6fe82dbb77ef6a20e4947de343a574762aaf4ac7ea20ba74871070e7125c22b3a2807a028f6a19c3043901c70b64eb970007e918bf2c1ca82bfbefbc80e4035d400,
  unpack 0x28547f2c63ce76f4cb8e71edd1243d13d71309eaa81edc899f94c4283bd0038003f9b91fcc0039e400,
  unpack 0x6011b918df256eea411fdfb7dd087a652f03c1fe65bd40077947f890247f49403ba001cfbc8e4003df400]

private def t33 : Array ℕ := #[
  0,
  unpack 0xb651fd883bfff7784b0f65cdde203e967f0980e78d7fdddc4dfb000e6b11fb5ff30000155cdf7972001a0070000,
  unpack 0x1d4cdfb9adf6087bc987a7a1eb921dcacbb10079b1affcce9f7da0072c60fc001cc72bbbdac001567f4fe7cfbcfa3d0f400e0000,
  unpack 0xa137fe8e4bc5ce7d128fa029fba439a9afa800e03a5da00387fa7643c83f22091c0188e7f9f3fcfd00e801c0000,
  unpack 0x2f617873675c68fc361e2cbf872871774f6501e502fd04075fa1ec8f847f4d023ebb8820e942d4007ca60fe7fcfd723d1d00380000,
  unpack 0x27b4bd602bfc58f3a80e9c0ddb243a5b8f4380ec579cb203a3eaf8440e4b81ff5968177630978db200f5a01c03dfe6f5ebd7a00700000,
  unpack 0xa1badc8d0bdab6f9228ff313d2303cb09f1880fbda7f8003d0bbf9440e73e1f9d9a447d54dedb8b48ed4073ebf9fa723400e00000,
  unpack 0x83efc0fe101f9203d95870211eb081ce047b9c074d84fc001c355bfeb0c58ed5c2e5441c1843bed803f9f273c86801c00000,
  unpack 0x10b5fb60b7c37efa601dd613d44877096eb001fbba7f6b87ffff8c1503e12477004faef55a00f473c8d003800000,
  unpack 0xb55ade5c4bb7e6f2a20fe051e9803f711fc86725fff59d70784a0e0a27ccb01dda528efb600e793d1a007000000,
  unpack 0x18b36e78e1e894fd8947ba60f2ec22f791807d0aae0155c6fd7b020704eaffcc670febb2c00e8a08ed403f9ff3f7db400e000000,
  unpack 0x81c5f926cebf5dfb423d5fd76010f65f9cac2bc7647b482f3319cc0c399207a8ace4a85e02a39e8270c10e5071c2d93ae5c001fa462fcb072a0afe9fcc6db5c000000,
  unpack 0x41ebf0fced8e08a5d7c03980cfae96f7021d581ba6387e5cf7bd22072558fd0d922feada4bd4441f90c5a518f7df5d0038000000,
  unpack 0xa0bfddcfabd3d5f4e08ee717cdd6394467f2b0fd209f5c017f4f81cbd8b964075201fac2147f6282f882c8e7663d3b6d70000000,
  unpack 0x6a387a9a6febd5ebb43d73772030eb657de603fa62fe800e1055ea0038afc7d779797f50222fc001e4023b5da1d83d36dae0000000,
  (0x132df9a02738f321058ce1c7731ea31ce2e6917547ef09f8801e467b2402085041a13a2080918fcb20051510001a08208003f3cb0115040001b6d <<< 481)]

private def t34 : Array ℕ := #[
  (0x1b8f22d385d833e006727f3495c8108c1 <<< 817),
  unpack 0x10d4bc952bce64fbf00e84cbf2803b489f9080e55e3f22038b5ef9400e2291ff9828476ab400055700000000,
  unpack 0x2d73c7b0b4e2bafd26a3995ff6c00ee997dc403d047fea6dd53f71dcbfd62205dded6000ab3fa00000000,
  0,
  (0x13e221709c2de6151ede08920562a76005ff59001f270000003258000c8100100405000001400000100055 <<< 603),
  (0xc34cc17c4dbc7b906945a22071766d403234320062f3ca00115070006221800040168000450059 <<< 633),
  (0x65367feb9652e6c514b15cc01bfc297001d6008012d8f60004d3041016010410100505 <<< 667),
  (0xcfc076dd79c7ee1c61271b6079e7f98035cd624031db0a00099540007064051 <<< 693),
  (0x687dd6aec720b17104d24ad012e95f000a4b50801fe5e68800284849 <<< 723),
  (0x3fd4324e43533c5055dda8403d7ac94066183040505f4a5 <<< 757),
  (0x452db84864986d8009b5e80854fbb44051024055 <<< 785),
  unpack 0xb738f7a42ed727d3823fa87f7c40e1f6fca22bfbcffa402ec7e5e01c38259748acf0a11e82a3da8670c10e4071c2d93ae5c001fa462fcb072a0afebde4072014800,
  unpack 0x41a2d77a02aefda9efca3cf7b70c04e443be6013fb90f2480e7873f698f187a100fd895cd81bc4441f90c5a518e7de4072029000,
  unpack 0x20e41b3a472760b2e2c01d7e4be8047d1adf5561e930bf200761e3e2781c9303b6407ce40e2028fec105f10591cecc3de4072052000,
  unpack 0x52f4ce0369e8a3f92cc7d016fe141e4d1fe44074955ec101cfd33d4007119afc101fce2bbb0c55f80038d0073a8760e7de40720a4000,
  unpack 0x3614bc93f3b66ef5ba0e62ebef1fb9b027cabcf25b7d32a3e6ddf9b10e7401f9d93ea40f8a88e3e5dd10438909ff964f0105e880381a0fa4618fdde58399507f5c8003d0038000]

private def t35 : Array ℕ := #[
  (0x3f0426b163194c70872569c9158c7da0162c7c00d <<< 784),
  0,
  unpack 0x41e102f2ec8e5139d06a387e0f0290e6209de203bba47c480f471be910392f47fe7f883ddc800ecaa0075a8432300000000,
  unpack 0xa1447cfc0baad6f4598fdd2ff6843e29bf3280f9f73db003a3dd7b040e1675ff5c2c5777a003809463900001a6800,
  unpack 0x107b1f9fbcabaaacf4510fada3e3943ad32f1300f0a0bf3203b6dff9400e0ed5d6281dd344441c18b000000000,
  unpack 0xb241f810bac4070e28ed6d1d1303fb2c71900f2095fe9f10afa4f14bea6905ddfb601ec6000000000,
  unpack 0x11a91c1f938c847f020ece99c0a43f38afa880ebbb9f8203d29dffc64d11fdd900e8405e7201cfbc8e40032c800,
  0,
  (0x2939b8b0219e74d986714a880fda1480072c58880e167100018fa2000d10b05 <<< 696),
  unpack 0x15868f872373972fe301edb1fd4687ab9bfb0dff3ffbbae57f6001cde0bb080751c8e0007bc8e4004b2800,
  0,
  unpack 0x147bd248b9dbdf89b0e4fdff0103bdf37c800e5411c005788fc7b004e0585e205396c178388e7013c4443a208705e4fc191f4803f28821cc1bcb072a30febde5efbe8fe6016800,
  unpack 0xfa367e3d2e7befc9463d683f9e40fcd23c4e13f6b000000000638800,
  unpack 0x218b3c97c3e6bb75010ea403f4853956d75004fe9fbf5d8b767ca64181fe1f625775b03788883f218b4a3000006ba800,
  unpack 0xfc58721daee3cdf1ee3ef4aff455e0503c0c17f89774498f4255c1113869170914e1a01e18238a0671150f88d1793f464ff97d0d1043810cf7960e54c1fd7bcbdf7f98f4073c800,
  unpack 0x20e9967fde47a5fcf9731f5a63cd2a71f3ffc101d98b7dbb84aeff4ca42bff36440ee80001c8e407be800]

private def t36 : Array ℕ := #[
  0,
  unpack 0x55d97bc1e7cb94fa101f1d83d50871c20e3701e537bf64075ea8feccb84bf00077048eeb600f22b4c401c0e6fa0f403c0070000,
  unpack 0x83381af1b65c3db7fc5871adcec081c441fec0073e3bffcd5023eb33bf2fdad602fa9807913262054fc7af4007800e0000,
  unpack 0x19988e1469c44ff9c1478504eb121dff839cc07eadae4901d5b63da0073938ffacf403eb880bd88c303e71039f797207001c0000,
  unpack 0x83f0dae630deff57ffc07c39beb1a1f2c63a1407d9d9fd101f5e63fe32d88fdaec503ebba808eb5eb2980f79fe6f41e00380000,
  unpack 0xab48f1172e13fbf4c439fb372e10fa8bfee603915e71070f3040e2701ff5f2a0fd58093800ebde007ad00e001e83c00700000,
  unpack 0x1931f8e72e64e3c3863f26179090ef263d0603b4087c080ef2ebcd103931c7fe70191dcaa8078b48ed40723d0f800e00000,
  unpack 0x41d2f576baef411ff62c3b67e7e090e44b5ee5cd217fa68a53cd1038b987d7550b85843bed801c80f001c00000,
  unpack 0x106c6c9d9fbb8a807f608e1d6bd994398a677080faf59db003d2d0ff6633b1ca9c3e4e6fd4d003ad0073c83e003800000,
  unpack 0x1cf3e5d13e7be7b1b0e12d7e1b03ad247fb00f944fd3203c5a9f3514e3f17d6811f5b528efb60073cbd1c007000000,
  unpack 0x20ea6e3c150753bfe3d31cb41fbb287a5a8fa701dc7d3d07873e56ec881c64ebf6b9482eedc007450476a03dfe7cb9b800e000000,
  unpack 0x1c483c2b53fcfaf6b20e4cb5d9303e123f01a9f9297dc003b019fb040e63b5ff59ce1f460475a00e5ef37001c000000,
  (0x57117b7eceb8fdd41b738f12aa87ded0bcd67c831410940082610d22932910d10224822a120208bc9d1930400820088200432f2c054c100000001000080007 <<< 443),
  unpack 0x20d529fa5bb744f5e0957cfc07c180f01d8e6561d16cfe2407da26f0881cbbcbdd34a42e3801c3483950efebbc047e1d98fe7cbdb070000000,
  unpack 0xa103be9f8b8b2072ee4eaaadd5243eeb4ff300fd1e9d0c03a677ff71dfacc11f8203d19676651803f3b901a01cfb60e0000000,
  (0x27fc270d25c247ab79b19465404231abcf9fb4968702e115014d08764e8c1fa08332844105633d9648012820001410410007e79602ea08000fb6d <<< 480)]

private def t37 : Array ℕ := #[
  0,
  unpack 0x418e6e7b42ae41cfc7a03d98f71890eafb5e61e0c7fac00ec119e41038d8c7fd76311f5de600f5a35a6200e0700000000,
  unpack 0x7d15f456be614f2338e60f1c03439a097d980e643deb203c20c7a040e6d01ff98461fd49807913262054fc00000000,
  unpack 0x5c413fe5e1f2443f60c73fe3f0da1d0213a4407c395e1901ca437feb27fafed6c07d71017b118607c800000000,
  0,
  (0x1fca2590b4c3e5aa1e4bf9a01f6e0420260d40000c5c08100096a8002f4008203f0b0000228caf <<< 634),
  (0x12bbbea0404793790e8d494008c75228037bc480084cc94000e38e00071000080c00055 <<< 664),
  0,
  (0x2abe554d281366eb87fe42090a1cc90009c532880ae8c844023b26a7 <<< 724),
  (0x4f50c4db4a0c9420b2ef7002a044c20106ff3202a360145 <<< 754),
  (0x2ded48f7a683d4600bcd16080c51f38003576e4f <<< 788),
  (0x3fbaaf18a4b7bcd882edb0c802f5dcaa9 <<< 816),
  unpack 0xc8d9e63f5d9627c9d07fddeef18bd2aa78042f50ceed931ee52fc802737e0f9229f2503c3047140ce22a1f11a2f27e8c9ff2fa1a20870219ef2c1ca983fbc8f7df47a02d000,
  unpack 0x55e33b48d74a64f8847ef5af9308f7021fa661f7ecfbaa533e9103836476c00f9705cf203de9072e1dfd77808fc3b31efbcbdf7d1fcc3d5a000,
  unpack 0xb1fb1ead1be6c970834f8009e3143a44df0b00fd8dfcae039d84fd45ecbf35593f8203d3927662063883f3b901a01dfcfde40720b4000,
  unpack 0x28b7be08f3d92efb09fe24d3feb53f460fa21ce4af1f3fa390d972110e6861c3d93a0e475a88e3843d1043ab08fd964e0065fe580a0fa4618fdde5839f507f5c8003e0038000]

private def t38 : Array ℕ := #[
  (0x34541276242501a8911449611 <<< 848),
  (0x6262d66544b1b6d353718b81 <<< 851),
  0,
  unpack 0x147f3b8cc472317fd841f56b78f287b2ecf3401e0cbff53568bf2801c2643f6bff40fada01d9872000fe634d000,
  unpack 0x41fb61fcdd2e1561f1cc3e6aa72090e6729ea6038d1affb7237de900389b17ed6aa01f5550441c41647000000000,
  (0xebb2727c0610bc8889e4d25097f40900b2b84c8069cca0002c4a00009f8100002d0000005c102080c047 <<< 608),
  unpack 0x41d2abfe03ce6687f20839b9ff9050e7085f6191ccf4c00fcfade41039b707ed67d05d3041c0057c01cfbc8e400659000,
  (0x5b48525f1ad44b471347164a1ee58d1002722490176a7080030e541009f9400004051 <<< 671),
  (0x4989881326cc85642ae5f69032ef38e022bb7b001a51ec0003289000354047 <<< 698),
  unpack 0x83f382e7d99df29fef407ee6ae3c81dc6e7b18072faef4ee1073e332ed0f74e032380039f791c807a965000,
  (0x7630c4b5428fad4214bb4c120643413006cffd900d9ca2f <<< 759),
  0,
  unpack 0xeadde05d5cba27a5887f9fde8b8b770bb0e4ec9d3203ac70f9040e61b5d2391df8c00393df7d1e87ac71000,
  unpack 0x3f9dbe7f2bc5a775390f1b5bd5123d65ffe330eb19bff5f9fcfb3c0e7501d3203872477480a3fb0417c416473b31ef27befa3d0fe6d75000,
  unpack 0x1069af9fa6db99107bfa3ffc21cb947e7887a930e220ff2003ac7f79040e7645ee9872573c00e5a41cb877f5de023f0ecc7f3e4f7dfe63f987ae79000,
  unpack 0x728372deaf6bb3d98abd236720d0ff9abf61d2be7ec00fa845c510390447f7170380039e4f7dfe63f987af7d000]

private def t39 : Array ℕ := #[
  (0x9c8d6943dc15d70d <<< 882),
  unpack 0x9922706eaf3a4ffe0439c6973a40f4437f6dd418ffe61779c510395a97e40623bbe802dd9a0007eb0000,
  unpack 0x14dcae8071f23dbab9074b79fb121fd7eb85c07783be5901f858bd22070c4ae5400fada02618f7df400fd60000,
  unpack 0x5e6cee85a9f34cba61c784deef0a1f3737ee31f09f0901fca4bea1895fb59e247d76d001d88866c47bebd00d40000,
  unpack 0x598a3a1887f851ee061e24c3fd4872dadeb601dbc87f2897fe90ff0fec2c47d41483a50055765307bcfafe7c83800380000,
  unpack 0x21e2fe5c47cc27e1e11d8c37a6207a02dfd501ddfbff5b7eeaf4ccf463f0007d36db6251a01c07be87a3500000,
  unpack 0x106b2b7e43638a01f2f10f49dbcda03e923f4900e16cff100390fdffd65b11fb5c2e0775b807f30281c003d06a00000,
  unpack 0xd418fe2c5cda27cdd87a13ee3821dd65ff1c076b0af74f57d3fd32c00ffced60bc44070b30e003df5cfa73c001c00000,
  unpack 0x2b125799eae0dd9cf283bf72f3680e5693f6584f2fe400e3777f199f417dc7708bdf4c000e7d3b5800000,
  unpack 0x2e6cc7b6ccfe263d2c03ed71f4c80f6f67e4203be9874c00f5013cc5039fd5ff591038001c87eb000000,
  unpack 0x175c1e9793f6ca7d420f02d3c6143e0f2fd200f8df7c0a83a89a7d000e7a81f80038884774003de5fcf9ed6000000,
  unpack 0xa9595f946fbeb2f0e88e8491e0843a85a7866da49df203eb927a040e1c85fd5cc9efa6001efad4000000,
  unpack 0xcc04eaf45c39839584737dae4d89e76f39b407a21df8801da71fd27b65ff5b84070003f9bb58000000,
  unpack 0x1069a17cea6bd617f4622e7b99e1503ea58f5080fe4fdd920394207b440e44b1f800382e470007bcfeb0000000,
  unpack 0x54727ea6c7c8047c96e70a40fa0a1f12bf8dc073ac9ff4ebcfbca2071c48ffaea527be98006a0000000,
  unpack 0x4d72f912bd4aa3c80572d8cec9a9e44a799f0732d9e8941eb2138aa073a40f7001c7403edba020fcc9137004574334c33ad40000000]

private def t40 : Array ℕ := #[
  0,
  unpack 0x6642bca9d71b4fecd01cc1638f287b798e7601df2afb44073954e6801cf003f6b0588faefd005bb00000000,
  unpack 0xf807ac967fb32e0b51e22878e20725effb2db237f2007b336f2881c82a3ff30448faeed0130c00000000,
  unpack 0x15a9bbd3717c3d4f8711f38bbfe4074838f9601eb727b2007beafffacfdcb8600bba8a41df8c433000000000,
  unpack 0x12143c4e638a9d76db8e5125cdb43db14f7a80ec307c920388cf7da64175fdd180eb5f2d0155c000000000,
  (0xf8046f8e2dbb62e80cd6fd20076ece0001b7792024b3091003e828003e704800090000000001 <<< 642),
  (0x117cb4f934ce166415790a3400ea9e400cae58202db3a4100d5a3000356000201ac85 <<< 670),
  (0x66231b835e0762911a860e4a07e8fe001d53b5800d3356880740180016b155 <<< 699),
  (0x20b6b0674c3de9a806a155cd01ce3e000850b6c8078a3000001529 <<< 732),
  (0xcf0f543ac1879e80143a58509310518040336080059b91 <<< 760),
  (0x1c0baa82266ba81443899202829abf040741dd71 <<< 789),
  (0x648d5ca641fff72616b79f341048b41 <<< 822),
  (0xb797ab3f3edc09a604622895 <<< 850),
  (0xa89a55b1514d00c5 <<< 881),
  0,
  unpack 0x294bfd85f4c4bf3115cc19b856a7426cfd081fb3bbc55077c5cf6a81c1aa3b800781c1f1101e2807f22409d0155d0cc1e01d8ece4001a8000]

private def t41 : Array ℕ := #[
  0,
  (0x1f4046651386b6d9649c6871 <<< 853),
  unpack 0x37297da44bad4cfa518e9733e7043d87a74300fb7d7f5dadc3fa4a50bf6bd5c8faec8017b28821ddfa6e40680700000000,
  unpack 0x2808c703b6fa30de3e23b9a7f36d0f3591ca403896af6480ed11ffd9892d7e7ed0beb5011c7a039000069a000,
  unpack 0x158557d56f7fef6ea221c8ce3cb72f5e6003c2a8706477647e2bff3990afab4147480475040743b000000000,
  (0xfb7f30fb24d54a0e003aa3b02b299ae011d13020041dc1000056080021e0002021ca400011800020013f <<< 610),
  unpack 0x20d3adbf3f972c28e8221d6a57a64870462fc401e1b97fa3d05f69da3e000ef781c001cfbc8e400cb2000,
  (0xf562d0e7426232807c57a9605c441900763d864075800000118c304055a0100077057 <<< 669),
  (0x67d70ed5978e09ee20712794306a42400be9502031dee00001cc98002e027 <<< 702),
  unpack 0x30ddfd20ce91bbc2ae3bb78f9490ffe53c4603e865fea790b3c1741fd8102fad40471e807bc8e4012ca000,
  (0x62ed69595da767331013bac011f9af5001ff4c8011e0d5 <<< 763),
  (0x35a4f2e74d793d298e1e320101eeaf0003a80eb <<< 792),
  unpack 0x8328a5f21bfd7be3e4c877cc7ea121f882fe2761fe3203ce9d7a44383f3a195f5a808e3d0000018e2000,
  unpack 0x2c29278cb2e98a7d3603b32af4ab0f5213c8c03d75174c00ea33ff6d8e5c7c080f2f91f52e2afc001e4023b5da1d83d0001aea000,
  unpack 0x10da3c2697a361e8d59dbb6bc26873700fd401f470bd5c070733e6081c29e3f6b7a4bffcc3c93b328c01f9dc80d00ef41c8e41cf2000,
  unpack 0x218070c33e76edcf0d3e1bbf6c50f765dfee03d2757e800f2b65c510391a871a04700001c8e41efa000]

private def t42 : Array ℕ := #[
  (0x6f32b <<< 927),
  unpack 0x4496fd508ee1c1d8a83963bff6d0e4287c6803d754f8c80e04bbff19ac47ed7fcc005a680000000,
  (0x1e1 <<< 937),
  unpack 0x7134fdf36e8595c98c3abfdfba90ec077de20381687e400efb81ed00399387fe74295f5d969077a0c400000000,
  unpack 0x20d389bc72b73003fe201f3b93d2687f6bcfaba55f6c80f6299c91038a3c7fd6e305ddad20e15653000000000,
  (0x3c17ce26af5c4c43828c26a103a2efb00ef50c40012ae14401e60200070ca000086210000002200008d <<< 616),
  (0x5d61a714ad93d5ae220d04142d163c000d20b10025dfc5000d4c18001562002001480000205 <<< 646),
  (0x2561df1aa7375a780f8225840759b32009fbba880e96c3400070a800061c8a0800b3 <<< 676),
  (0x5b9cbc8589d53c8431bb6b90232f9cc03732d32013414d000aecaa000d63 <<< 706),
  (0x3d1228766b160c83049795a10cc93330018396c000cceb40031c9 <<< 736),
  (0x9736c1d610e1d7a8311671a41c4826203bfbeba030bbf <<< 766),
  (0x172e2fbb220ef5690a95a4080dc6069a0aa8b9 <<< 796),
  (0x5a126303080d438a123024142fa82f <<< 826),
  (0x3ccefb25e9f88dd300f142b <<< 856),
  (0xb2ad3a2f234b9af <<< 886),
  0]

private def t43 : Array ℕ := #[
  0,
  unpack 0x45673d67874993eae31f6faf93687e157f3201eb6d7e6007d468fa80a97ed74811f5002d00000000,
  (0x1 <<< 945),
  0,
  (0x1f0d4ed33340c5c145921a10826e979806545924021ec5a200c45500052a110405000000040000000401 <<< 613),
  (0x1582760bd7fa0c6d056bdb2002e1fdcc04ca240006fd2da00153440006a411000071080000011 <<< 641),
  0,
  (0x2f3e163254bf655015254b9a06563e100adb74800d91400004a2000010a91 <<< 703),
  (0x499a3c1549acb534063c270a149c0f0008a1550009982080034c09 <<< 731),
  0,
  (0x6d393e9a7ff2b98438fbed283a4df00078a8b3 <<< 793),
  (0x1e74124ab4b11b9c01076c568674bdd1 <<< 821),
  0,
  0,
  0,
  unpack 0x1e2ff414e2e19c34e3a3f77e090f0d09dee8391b1fb96f50ded1039bfd7b70023febae21e8022ef562e9b100000000]

private def t44 : Array ℕ := #[
  (0x106bb94d773807225 <<< 880),
  (0xb7d442acfd0b039952c3605d <<< 849),
  unpack 0x41a467f2526e286fffaa39aaefb800ebbc9d8083a936fca80ee23fec10388897fb7f203e8203e7107621977ab05d300000000,
  unpack 0xbf0f9f6ae3d2fdf8218e658bc4243ceb976b20fc461d0a03cd51fa040e0495f2003ba207f4b887a008bbd580372e9241ed390007f334000,
  unpack 0x58d35f37fdca2e3980c73330fb021f8a0f89107a917e5d01cd4dfea43c5fadf0057f60c878540507d65000000000,
  (0x2f406439c23a333b8547af680307622204922c280935c24402228280089c18000e524000080322000803 <<< 612),
  unpack 0xda67fe6b4e3ec1d3463a6ac730d0e7a31c6a83df17fa200fd883e41039bec7b6200ffeb8120e8027f9349c01a38944cda000064000,
  (0x1daab93064eea5dd413879e087c2b89506dbd35403a5400201f2c1400528450405595 <<< 673),
  (0x3638cba90e456af10d5033c00cef75ba0a4e1820076e130403b080800008bd <<< 700),
  unpack 0xaa3b70448fba91ed4e3eb39f1a90e21bde6283ff4f7e200ed3a1ec1038a3c7df24ebb85e82239682fc470045dd9fab949a5b8ee5fa0003d94000,
  (0x2437752478ca0c1c685edb4828040c905bb2834065a41d <<< 761),
  (0xf18712dba51d16a813d5a5243f598888393c10d <<< 790),
  unpack 0x757638dbe7db57f0451c65bbdd2071d37e35f9ee94bb1047aecefe8c1183db39842f4501eec83e538032fb8e0383fa08c98a0839c8003dc4000,
  unpack 0x640ff8c287376ce9571ff2fbe47774dcee0739f013ba35475801e1621c9123c7b2755c9e5411ec43fa20879231ff2c9c028bd10070341f48c01fbbcb0722a0feb90007f3d4000,
  unpack 0xacc7bd307bad64756bfed659f3913af70750bcfae2dc15a3eee3fb110e4bc1c9d93fb3fa88f6401d1043eb19fd964f0025fe580a0fa4600fdde58397507f5c8003de4000,
  unpack 0x163d13e847f3e77e5b25dcc7ffe6276fede77c1e52439250767fcf0a81caf639c007a089fb6c9083f3244dc0115d0cd30ce9c8003df4000]

private def t45 : Array ℕ := #[
  (0x8d2da1d5db2b5e71 <<< 879),
  (0xd01 <<< 931),
  (0x3a943e3f289d1bf1861d29a9 <<< 852),
  (0x7d90cef1ab4a544a119c1a940ad750c024a3 <<< 802),
  (0x15e606ffc4473e5d85a1 <<< 869),
  unpack 0x41ac55f50a2f3f5dcb243ebd37b675a51fa18033fe5892b9a2072df0fc001f4403ba000e5c8000000,
  (0x6f2e67375ab648a0075d2cd00b068d00123fd48014c15688068210000f <<< 715),
  (0x8b691fa2eaf <<< 900),
  0,
  (0x204885883480f58c1f <<< 874),
  unpack 0x5f55bce5b73664e3e21cbbafe9287ffc2eb201dba13dbb668ce6081c2863f0007614bec605e44c8a400000000,
  (0x7874caded237437102db9f4a1c362a4017f <<< 807),
  (0x22472f523006f20405abe3842869b6c0051be9203c6240100a7 <<< 742),
  (0x38984749273a324076b346401f9184800de620403df740201 <<< 749),
  (0x120d4fcc0bce9a6609 <<< 875),
  (0x7f6f2b9d0e76d <<< 895)]

private def t46 : Array ℕ := #[
  (0x10e4824307550f <<< 892),
  (0xe956d9dc4bfc71c82f <<< 873),
  unpack 0x835098e09ddcbe0b91807b7d5e7501e97ffec8079bc8fd4e9fefda007273afdafa707bb8c03c89931b400000000,
  unpack 0x45ba3c5db7f9e6f2d21e74dbd2607f98af0701e7dbfbb3225cd10393447ed7fcc006ae80000000,
  (0x2cd03e748d2949d00095c5180241ff1 <<< 823),
  (0x2b02d0f3e4535 <<< 896),
  (0x13c55b7 <<< 920),
  (0x15e3ee115511d561c619bcc60128bb8001ab73 <<< 797),
  0,
  (0x65399743567eb4220864add81525ea200084e8101485f <<< 767),
  (0xed83d <<< 924),
  (0x1719deab <<< 916),
  (0x6a796dc1305396c363f49b43ef0f4c01b <<< 810),
  unpack 0x12693b4a078e5aea801ebbe7aa2077addf1701c369bb2007228cf94c6e4bfebe488ee8003d7a390f40000,
  (0x2838feb445ccb8a4068477ca0c6daa501edbad1 <<< 791),
  unpack 0x3238bbbbd74700ee231e267b8f6077f32ed201da13ba24078d34ff4c9c6bff3f500e354401c7ad400000000]

private def t47 : Array ℕ := #[
  0,
  unpack 0x1894bfbac9da8fbcf547ad2bfbca1caf639140792a7fb4f7aafed302c0fef28477400391e8f400000,
  (0x3b261d05187091761f5de4021067b3 <<< 827),
  (0x429da0c5124b8b971ceaf59806b1b7601eaa1d101 <<< 783),
  (0x10813672111cd <<< 897),
  (0x34fe0b199 <<< 911),
  (0xe84507104f272550e3c3f9 <<< 855),
  (0x1341dcabb081ca2342afb9 <<< 854),
  (0x555 <<< 935),
  (0x11c3da798ab4623085b4e9e40dbf6b3802b1f4c806d0a14401f60a000d1 <<< 712),
  (0xb83df <<< 926),
  (0x204969ae642bb211804705080efe50800bd27 <<< 800),
  (0x3ac54ae6c4f127e38df0988502012d380be1a608025f920403fb8a000558800009 <<< 684),
  (0x49b9ea708d6253c6002f3a901082c9501317448005205488035750001a0004101 <<< 687),
  (0x153f8bce8dc05af000b35dc00f45b94004f559101a35860801 <<< 747),
  (0x83fe2078338068884eec16401a06a9006ec382004b <<< 777)]

private def t48 : Array ℕ := #[
  (0x62cc97c93280bc4876c2c4283 <<< 845),
  unpack 0x1787fd8c1bd596fb238fb109d0a03ac517c100f27c7e8203efd77b440e0f01f9b4c0ee8003f9b900390000,
  (0x1b7d657f823dcd18c4884b40025937d0021d6964052a512201ec870000e6010001 <<< 685),
  (0x1ff3e764b4fb1ecd41 <<< 877),
  0,
  (0x1980ed35487b8dd70f623e000282fe101d <<< 811),
  (0xff4e5a0d261152e0057d753003960040266c78203fb4a5100f1a0800031040202801 <<< 674),
  unpack 0xb518f2715f5f37909c7ae3afd2d0127d4807e11de1901ecf6fd82070520fef2001a80000000,
  (0x15c10daa44909d0a0afeb9cc09c66f0808a2700805 <<< 780),
  (0xca7217d1 <<< 910),
  unpack 0xa0351ed17bc38579518fdea9df003944ef6200fda53e9dfbc17a672cff983aee2817b9199763000000000,
  unpack 0x35bfddfb5bab51f0418f941dd6843a56bf9980f4867e3203a555f048c7fd6a801f5dfab4a2d000000000,
  (0x272df51d337b98282352c7 <<< 858),
  unpack 0x83a860f0835e543bf958720adec801d8bfbf40077c98f5801c3b47ca0073fd8fc001f9423ba001ebd0000000,
  (0x599d54fc32d10ba2307cf5a4064b74600cd979002e59cd0002209000061240003 <<< 686),
  unpack 0x528e6f7299f0fe7e2cc7023ff0921dd3578cc07afbef5001e8f73fe33348fc92c07d77e803d00000000]

private def t49 : Array ℕ := #[
  unpack 0x5fe45f8d29dc947d25479a73f3081e1a77c1c07df13ed901cacf7d331642e9588e000e40000000,
  unpack 0x547e0f4191c78d7d84876177f7101fcd63a9c072068f9901cd593b23a35fd0448ee8003de5e9c800000,
  unpack 0x29d54f997afdd95c1ac3a986f9050f8285f4c03fc847160d7dc67b21f80038e607d75012c800000000,
  (0x3c334ed910e0aa002ba729084b2c31c00b2a86005bb21a2017bd000048a0004000140000101 <<< 645),
  (0x1889beae66ce842106bd4f24014ad64c067a1c2006561082009dd600070a1104054000000450400001 <<< 621),
  (0x3deeb4a1da32ea0008e38aca0468a200051e0c800cdf148002555400002004100400000001 <<< 651),
  (0xab315e36bdf04d8e1e2ddd102e6b5080358b892034598d000064b0001f704020310040101004002001 <<< 618),
  unpack 0x20dd76fef3377deafaf21f384bb76873b6afee6c5fc480fb169c510395a97e40623bbe801280000000,
  (0x65230dff2b55f5d86efd90600b0d18400c09744061db4a200f <<< 745),
  (0x147a6107e55abc7147fb2c80830bf39800e2df000183 <<< 773),
  unpack 0x18fc7d0eb39831f5138fb63fd0143b32370b80ebef1f820391ecfb400e0981fb5a4e5777b5809400000000,
  (0xd113cbde905f <<< 898),
  0,
  (0x67af7aa11dc0b304647fa7483752f1 <<< 825),
  (0x2023 <<< 932),
  (0x1de9de0310f8c3c1 <<< 883)]

private def t50 : Array ℕ := #[
  (0x1967efdae09 <<< 905),
  unpack 0x41c63e72c9ce6a5fe1ec3ce7b7a8d0e9ff1c6803906dfa080e0a91e510397cc7fe64a01c001cb90000000,
  (0x173ebbf505 <<< 909),
  (0x105 <<< 936),
  (0x40afe815c43bcd5112e0e09a0de7 <<< 835),
  (0x14221490c5b3b7b28b6445 <<< 860),
  (0x215c82a0e03bec238cc3d <<< 864),
  (0x11b4938e024f9fcc839364b0030e38c000cab <<< 801),
  (0x485639df8afaca27100af7d8044e62000b160d900dc9e60002145c001e09001 <<< 695),
  unpack 0x41cb24fb296f7c2fe2683ff9c74e80ff1e7fc60389a57c400f476fc510399817e68603ba000fe67f3e41c80000,
  (0xceddb8852f50a54048601a4879909d80667386406a62c800081910005445 <<< 705),
  unpack 0x83f3d0e51ddca95796d476aadf0821ca7c3a5407acedec901e094bd200721dafc001dd023ea0d75000000000,
  (0x65e265571544401710564f121ba2df100327b <<< 799),
  unpack 0x41e543fdf84fae3fd9c439c567748cefac0077f99fd101f15f3d800706a8fc001c9403ba000f5e8000000,
  (0x1fa17a8bbaef212819ce882012ad7280391fa900017acd100a841 <<< 734),
  unpack 0x18b18ee2b9d35cfcbc87bcdce9501f20dfcbddd5fad88297dc62211ff5fa007400000000]

private def t51 : Array ℕ := #[
  (0x1fefac3fe55077 <<< 893),
  (0x1759d68fd5af574609aa920a10a64c1018b77d901172f68000135c000e11440005a400001 <<< 655),
  (0x187ee7a3212565210b <<< 876),
  (0x5f72a16ca7371c2a572a080cf1c40031bc824036999a20149020007ac010000000000001 <<< 649),
  (0xbdf4d6313d0e68ec2b5 <<< 870),
  (0xdf259476553f858c09ac150030043900652cd0004d899a2003703 <<< 733),
  (0x968421820558ee80ec895ad097eae9 <<< 824),
  (0x73093cd04c209f <<< 891),
  unpack 0x3422f6a3afb72fc8063939dfc49bf7b8407d2cced001d44a3ea1725f58148e000f40000000,
  unpack 0x127c398ef7dad8e3151fa357e820745f6ea101cc5f3d3ba0b7fe9a29760c4774000f7d007a0000,
  (0x26ad51ef89cd49b8825040050efbcf88095be488044d63440391a800010c3 <<< 704),
  (0x5b7be6c68d01f9a41285400a098ffb10024fe010082b400002641 <<< 735),
  (0x64bb309ec18b04811ed0f9d2123b6b40157351101b0d660804c54400003 <<< 711),
  0,
  (0xb3adf091d62f808b692a006d038080c5cc08802016840014b <<< 740),
  (0x530e9a58188a802838e7d6a030d5e440086672001605 <<< 770)]

private def t52 : Array ℕ := #[
  unpack 0xae5ce9b85c9603d0947a206e2901eb9dbd8807a338f74e6aebd82071390ed4c8ee80007befa3d00000,
  (0x2b501304ef56bb790520a8ad0cfaa6200bfb30c80da4eb4403 <<< 748),
  (0x7c9eddc22feef00807384914224cf6601d8d2b2001e805100970b8000372880032c20000050408201 <<< 622),
  unpack 0xb979fe32dbfed07aa38f3dbfc5b03ac9dfa200e859fe3203905673440e5821f9a00ae2500e1cd9a000000000,
  (0x17d427ae5c819dc51068e8d21066d6000af0e080035b1480055 <<< 743),
  unpack 0x2bbd783da7548bf7f21c912bff0076e4ef1301febdfb640767e3ff4c8e6bff35048ee8000e472fe600000,
  (0x1ce557296fc2f461064187450385620800fb0a480f6d0340019a0c000a90100002205000055 <<< 648),
  (0x7b866b9c4c44e3841d681280014416501e8fec100d71168000d114000eb0040000050000145 <<< 647),
  unpack 0xbc935e7e7bb53977390e5f21c78039ac0f1180ed5c1f6d8c30f9440e7585ff9e220700073ef239000000,
  unpack 0x20c7e73ddb175466e2631da33fee0071344ff101d4dcfb2007da74f6801c37c3f0007d100ee8001cbd727a00000,
  (0x38cc4b9aa6cbef6a09fa4c410de5560800f10e400b2b234002e2a800089cb200082001 <<< 668),
  (0x58dd6ac818b6a5560b1917880819e81007bf25000123340801c6181 <<< 727),
  (0x3426c5662609cc881 <<< 878),
  (0x1c50966517511f20359bb1a41f <<< 842),
  (0x43b4b34591dd93c60f209e0003c19ac032ce41202894051 <<< 758),
  (0x654f4d7f9e56c5a210d48ac006101c7000e9c81008a1 <<< 771)]

private def t53 : Array ℕ := #[
  (0xaa7daee47976fd1c19539b485b <<< 841),
  (0x771fc259dd7a49e2046a97000dabca40163df81001c4c68001831400061140001501 <<< 675),
  (0x924e2ed <<< 918),
  (0x1f5d246408a847a38d37302403b3e590023a244804eb390002fc0e0001 <<< 716),
  (0x976b0e170e49118c1cfa48a02bb9c280009f7a00110aac0004a600003d <<< 714),
  (0xe94589 <<< 921),
  unpack 0x41f2d5f28b4e9f7dfc0c3dbddfc4c0ef02fd24039ac87a70bc7d331780ffac7303eba809000000000,
  unpack 0x292d5dbcd3add075e18ff80bda10389e5f0b00fee47f5dfb7d7ca65b25ff9e8c576ab4a6a000000000,
  (0x1b41 <<< 930),
  (0x942b3 <<< 925),
  (0x729ac74686d2394e1957d3942a83e480165ea2003 <<< 782),
  (0x7e06ca642b3364ac2024853018212a0029d15820173c8410068820001 <<< 718),
  (0xeed0a3f1bedfbcc59c47e002e8bc04073f832004d3e5a00199c10005 <<< 717),
  unpack 0x20df257d5c3771b7ecf71ead079b4879cc2f5401f511fd2dc5fed00388447f717038001eb9e7973fcc00000,
  (0x7df2fd1ba03f500435a94da00167c4e028b3e020185a8000029220000f528020231 <<< 678),
  (0x4d1708e25c63606113e574d00fdeb13015622c10171bd680034f100012b8041011d <<< 679)]

private def t54 : Array ℕ := #[
  (0x84de4f757a9f69987d7c05 <<< 857),
  (0x955fe6606666226196a935814da45401dd84000011c920800bf <<< 739),
  (0x1381eb3cd4cade0486a6a1f28290359c02682d2403 <<< 781),
  (0x9 <<< 941),
  (0x79 <<< 938),
  (0x431ed1d98c718a6e2448b110090c8640145 <<< 806),
  (0x106ab168252540dd87cb681685ecf <<< 833),
  (0x2b71dbd1 <<< 914),
  (0x2179162e98432cc60db13b88142baa601a3edd80141e508001b24c0004a9440015010000000000001 <<< 623),
  (0x1e5db31f <<< 917),
  unpack 0xb011ffac8be6bcfc088e3b81dd343867f7d880eef7de9e954fa86997fe75a17dd8209ecd239000000000,
  (0x99e6e18dfb <<< 903),
  (0x1ce0482f6a72d2ba0e6f006504b <<< 840),
  unpack 0x22a4decfa3af1bf9b90eb83fe3143aa1d77280ead35fb5ada971440e7221da991dd000072000000,
  (0xc6a676861dfdcc263568a0041c45 <<< 834),
  (0x1281f9462476d765840f1af4067ff7180204a5040786c8220028c50002a001000001 <<< 677)]

private def t55 : Array ℕ := #[
  (0x1d6789bc1e8de1311d59825814cf18601f29751001174280021a10001621 <<< 707),
  (0x3ae041294f9d871106ccc3c2123493101a26718005 <<< 779),
  unpack 0xd73b73de6f4739d9c23d28770ad0f6731c8a03ec9f7c080ec7a9c5341c4185f5dd036264000000000,
  (0x1099b709c5 <<< 908),
  unpack 0x83e248e7ee1c41ffd90871c09f8481f05238d4076c9ee8901d0f07fe32610ffcd97038001ef203900000,
  unpack 0xb12edcf96be2f87fe74a7dfc343af787f180f7ccde3003dd26f9400e6505ff9a24470003d3d1e8720000,
  (0x53859f05caaad3171b03e00802bb24001946b4000c72128801e6140001a124100d <<< 683),
  unpack 0x1075ae9c96bb970578930f876bd1303fbbb79800e6e39eb203da467fa62885ff5ca007d6d00eba00000000,
  (0x63eafa96178bb36c03a391302e06b66011e91a00112985 <<< 762),
  (0xfffb733d826b89ee2064560420cb1cc01 <<< 814),
  (0x146ee7ef0c8d6eca0a66c66803 <<< 844),
  unpack 0x26069e3ddba7cafa528f2b5be4803d26770b00facc9de011cc1038be47d5400bb55874000000000,
  (0x268f3051df3343f70b85d34a0d74bf2009dbb910051 <<< 775),
  (0xcbac2265bebc7b84b <<< 872),
  (0x3 <<< 944),
  (0x288b82f41467a4cc2a14a1282b72a5402d45f4004ac6100006ed100060c40000000400001 <<< 653)]

private def t56 : Array ℕ := #[
  (0xafa81f87aefed1 <<< 890),
  (0x38e85b4716a08fe115ed4dc80cd <<< 839),
  unpack 0x107a115c8c7bd311f5fb0f617dcf103ac13f1180e1a63ff9b0ff71440e4ae5fb5c0257d5301791108d27900000000,
  unpack 0xe1c67c690f894df82438bfcf88d0fc807fea0394967e880ec58df12752fc80c4777d0069b00000000,
  (0x9e55c91e7547bbc4060a13485585d880633e500038b918000330000025 <<< 713),
  (0xcc1a289cac4789a62fa1f8002142dc200eb871002a16c4100ee9 <<< 738),
  (0x6e3cb1793429096428941a902fd290e031f60300250bc1001 <<< 750),
  (0x68c99286d50920f30849b4521223ab2017d4a0800f3972001 <<< 751),
  (0x1fe0155f96c4936901eb95 <<< 861),
  (0x282c65310660db61851bc7800b1ee7a80726a8000fbd5 <<< 768),
  (0xd39f71 <<< 922),
  (0x8d66f1d65c4cb9 <<< 889),
  (0x1724581645dc27ad8286a3e40418cd1c06f1300401b3f <<< 769),
  (0x1f22fd11602f2a1182e3a032865218180780a800011b608200a5d <<< 737),
  unpack 0xc02bfd126edf75c8ea3da49f4e00f922fe860380fcf2480e4e81ed10398117e4c027eb9009d88859e400000000,
  unpack 0xd1976ea2f40adf16e3a24cf6ad0e8415ee003bd7a7a400f0a93d9342afcc2617d764051daacd4f400000000]

private def t57 : Array ℕ := #[
  (0x1072497e708ca8fc020132128330e20803 <<< 813),
  (0xa0b7 <<< 929),
  (0x812540c89523832402d010802dc8fe000cda130027b7e9000bc828001a4240203b80401 <<< 662),
  (0xad67118692a79d84996222056c9148069 <<< 809),
  (0x3e7323e35b71 <<< 899),
  (0xcd5efbc73bd19a0019ff5e407da4b <<< 829),
  (0x3738b5e8017c94320d736b9013b33 <<< 831),
  (0xa69743d0d17e9b0836753a100c7 <<< 836),
  (0xa6770f48849bfa0a3eff1e94295b2aa0321ac9 <<< 794),
  unpack 0x41bb117029cff4b5e6ac3cc6ff2cd0f0413d4a03bd2bfe480e32b9cd1039a157ed7f203ddfa6003d7a7a000000,
  (0x11b6dae1d233ec93036453c80de03d1016a4a0800e83128000fd44000ea920100d80a0000000001 <<< 631),
  unpack 0x837d4af4ef1da07fd20c76e60e7021f519fcc3b63af8801d32ebfd33f20fcdac07d77e894000000000,
  (0xdf5070141d <<< 906),
  unpack 0x293ee76402e3ca5e84e3b6b6f9c10e5dfdeaa03ca967ba64b8be500393f57fe77813df4c007af5e9e800000,
  (0x34aaf58244b87f7b0d482b210e47d7a00621da080326e84403760e0009b5 <<< 708),
  (0x223b6e0a03b7d1446e11e2481ca6984037e210005fc69a0016f4600033b <<< 709)]

private def t58 : Array ℕ := #[
  unpack 0x112e8f2a91d9c5bb31c73dcde1981c6d5fd580755b2f4901ef37bca2072a62ffccc1038003df43d000000,
  (0x35df9 <<< 928),
  unpack 0x8346fbeb979d0623a24876ab8efd01c642fee382adffad297fe332cfaffaf862beb5001d8824d9200000000,
  unpack 0x2a5c3e5e8bd36afd428e1093f9fe99ee501c03afe24077b74fb8caa23f6bfe6003500000000,
  (0xe54afa279ff14c06357a4a241 <<< 846),
  (0x69db90f09cf07f661f4110800023e3001ce9 <<< 803),
  (0x82905 <<< 923),
  (0x6b45549999d8a77 <<< 887),
  (0xb4373db58230634e1bba3c201652c4a011ddd00015 <<< 778),
  (0x3b4d721c5a1 <<< 901),
  (0x1f7971fd879de2354463fe0201130d8c02c7 <<< 805),
  (0x14231d5b0c26a5c08f0c76a10f26e6100e515c0806435a0001f <<< 744),
  unpack 0x418178fff04f4ff5da023a36c77440f5255d2403f7b576080f14e5cd00382187ed76981c000e4001c8000,
  (0x150d <<< 933),
  (0x17a22ceda706141387e8bbc50fdc14880287d04800e3030002f4ae00080c92000ec05 <<< 672),
  unpack 0x620d79ac774ac4ed001d6af38268766d9e8501e662fedb7929ffac7c038002500000000]

private def t59 : Array ℕ := #[
  (0x3072a495a39bff4003a87c8c0d72bd180bb1 <<< 804),
  (0x1e680f89 <<< 913),
  unpack 0x1c22fd656f591dec0e3fb0bf7450fcb61f8603ef40feb6c375e8103926571ee4fd77c8b4000000000,
  (0x160489e74a132ee80d9b1d6809eef <<< 832),
  (0x526e734432f282aa12a63b0005c3544033723a00013 <<< 774),
  (0x7 <<< 943),
  (0xec30846879f5a70858ee089064c3118054046800786cb <<< 764),
  (0x6d <<< 939),
  (0xd <<< 942),
  (0x964cffc649 <<< 904),
  (0xc7cb7f4d37ca26887f012a684a0028003d7ce2405bbe182006d <<< 741),
  (0x73e9ebaf9290dac4097 <<< 871),
  (0x4e900891 <<< 915),
  unpack 0x2c2ae745d4ebe3ddd463bdd47d880e7d5be06039cac70c80eaffbed10392187e000fa201dd0001cfbcb90e40000,
  (0x2a4e617f0fea32263849 <<< 866),
  unpack 0x507c0e1e7dd93afec5c7f27ff2881da0ebdcb1f3efb6f724bfa6f21f92408e2028ea800e3d000000000]

private def t60 : Array ℕ := #[
  (0xd5a9e7808945f0b <<< 884),
  (0x46052bf617ed93a500724b10007d9c301 <<< 815),
  unpack 0xbec9ff875b82547d830ea00dd72439afefb280e59f9f100396ee7a663e15f8003cc617d76d80bd9c56a1000000000,
  (0x9508a21d403b8fc402546f200d4f1c0029bdf24053ed1 <<< 765),
  (0xd1bc18a52042c14826420824167c5 <<< 830),
  (0xf738605696906030ebefd010c18ad <<< 828),
  (0x33 <<< 940),
  (0x38203f30aa691d061a066304128d86a0097b612029db811003 <<< 746),
  (0xd10e34641814d1283940f7802c672a801e0b6920016d29100e92b8002200402021 <<< 682),
  unpack 0xf41879b98f81a1de0a3ceba7aa40e33ffe0e03945efe400f17dde999de07e7e207bbf4c007be87a1e80000,
  (0x1b17997ae3671b85034f57d080293b8007aba86003c6bc0200af51000742090402380000000081 <<< 637),
  unpack 0x1426e7b8f279090f4071c4637b26874588fa301fad5bb6407a387fa813977a047d4348383a000000000,
  unpack 0x3449eaf55c26279b0471007fdc81d8fdf9cc07b168f1901d1523fa3ae5f5f580e0000001e8000,
  unpack 0xa7fdbcffa38535ff300e135bfbb43e051f5100ef4cbe12039ee87b000e6355fb5daa0774003df4f4000000,
  unpack 0x17eb13da0474d80f6171d395bc720701b5fc601d346bf44073897ffaccc2ba302febbec01e44323000000000,
  unpack 0x152e73e4d47baf8f9021fffdfbb0875ac4e7701f6abfb4407f28cf6001cac2bf3a895daaca9d01707000000000]

private def t61 : Array ℕ := #[
  (0x84f92f2804f51 <<< 894),
  0,
  (0x3116ec4942e367aa821db8c5040fde2003e9904007e1e344038626000584820002c050000000000001 <<< 620),
  (0x68ec154d2bccc94167a7bc011c4dd50082bf88000140288056a480000314010100400000001 <<< 643),
  (0x2f42d4f70199d89886e3ea8c082ad5880f <<< 812),
  unpack 0x106c01be75c3e65b72a98eb641fa5d6adfd280eef8bf59aeefb4ca7abfa4901c00007a03d0000,
  (0x17e6321c609b12e40006aa128257bf1c022a7304010ff00001db100000424104015 <<< 681),
  (0x7304bdd2157f8a281fe37e2400c4c6602fdcd <<< 798),
  (0x105002a4d71ca7a616a35 <<< 863),
  (0x474f73c74078988715f <<< 865),
  (0xcd02cb0fd9d14a032ee5000ac407180dc53c8000d3730001d00c000b8832080c80000001 <<< 652),
  (0x42a4dd1ab7eb28b0d55 <<< 868),
  (0x450ee65f0b <<< 907),
  unpack 0x6e8fbc73c721e9e0b71e1c8be33b5eae7301d71e7edb2a5ef2881ce1c3feb05c8ee8003d73fcc000000,
  (0x20065666b91e6bc60871599424cf5e202142a8201197211007aaa8003d600000298000001 <<< 654),
  (0x1f89c0704241bca28cd5ebec06855b1000fc120009d4a2440076aa000a00800000d <<< 680)]

private def t62 : Array ℕ := #[
  unpack 0xbb7a1ed493fce7f3928eeb0df9243892276300e2d29fb203af8cf9400e7121ca801dd000720000000,
  0,
  unpack 0x20f1b17cef076c37ef021f1533ba20760f0fe101e0477acd07fd3014ae05c9faef9012ea00000000,
  (0x50529d6a0a9d89c403a3ec5019 <<< 843),
  (0x3664a3ee8a3dd1038f2fcc0d060309a005bf3a800efd <<< 772),
  (0x61 <<< 934),
  (0x193e52f730720cc005638ee00723 <<< 837),
  (0xb2778762d4941f <<< 888),
  0,
  (0x5c2417a7a67de2003a6c1 <<< 862),
  unpack 0xfa0fc91ef5c05e5623c0fb76650ed60ff8c03b6d776800e7607f5985ec7e7522fba9c03d88cc98800000000,
  (0x681881 <<< 919),
  (0x311eed768ea1aeb89fb2ea00e64beb80ab <<< 808),
  (0xaa72a0d88cf28ec83099be14093b8e401110eb0001b1ac000728b800241 <<< 710),
  (0x5f08c31baad <<< 902),
  (0x6489c5530a7620c01afee9800b3ea400165d7c10143ab08004751c001 <<< 719)]

private def t63 : Array ℕ := #[
  (0x15fe5e75036048a9 <<< 885),
  0,
  (0x3e7a54f7a1c8ed5000c7ff4801a63e9808faac4002e9c00400fd0e000950220008c010000001 <<< 644),
  (0xdcafa2039737d1ea31266004249 <<< 838),
  (0x3d0c3a0f026421d01dc7 <<< 867),
  (0x464ed6e41473995118aec5101 <<< 847),
  (0x1a40cae663f0476b007164cc0e3e7d00028e6a000eb <<< 776),
  0,
  (0x49e3d7c78c4489160e20a3 <<< 859),
  unpack 0x837c43fc7b1ca74be3cc77fecf9521fb7c3cd8070c32f8801ef473d27e01f9d4c8e0007a0000000,
  (0xb7be04090e5be52219e1b0a01bc704c0060ba32009c8810009d410000b4288201001001011 <<< 650),
  0]

private def tables : Array (Array ℕ) := #[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, t59, t60, t61, t62, t63]

def rowCoeffs (j : BaseCols (Fin 15) (Fin 14) (Fin 15) (Fin 75)) : ℕ :=
  let q := (baseCols 15 14 15 75 j).val
  ((tables[q/16]?.getD #[])[q%16]?).getD 0

private def checkAt (r : ℕ) : Bool := binary.test
  (rowProduct binary a b c ai bi ci rowCoeffs ((baseRows 15 14).symm (Fin.ofNat 946 r))) r

private def w8 : RowWindow checkAt 8 := nextWindow (start checkAt) 8 (by decide +kernel)
private def w16 : RowWindow checkAt 16 := nextWindow w8 8 (by decide +kernel)
private def w24 : RowWindow checkAt 24 := nextWindow w16 8 (by decide +kernel)
private def w32 : RowWindow checkAt 32 := nextWindow w24 8 (by decide +kernel)
private def w40 : RowWindow checkAt 40 := nextWindow w32 8 (by decide +kernel)
private def w48 : RowWindow checkAt 48 := nextWindow w40 8 (by decide +kernel)
private def w56 : RowWindow checkAt 56 := nextWindow w48 8 (by decide +kernel)
private def w64 : RowWindow checkAt 64 := nextWindow w56 8 (by decide +kernel)
private def w72 : RowWindow checkAt 72 := nextWindow w64 8 (by decide +kernel)
private def w80 : RowWindow checkAt 80 := nextWindow w72 8 (by decide +kernel)
private def w88 : RowWindow checkAt 88 := nextWindow w80 8 (by decide +kernel)
private def w96 : RowWindow checkAt 96 := nextWindow w88 8 (by decide +kernel)
private def w104 : RowWindow checkAt 104 := nextWindow w96 8 (by decide +kernel)
private def w112 : RowWindow checkAt 112 := nextWindow w104 8 (by decide +kernel)
private def w120 : RowWindow checkAt 120 := nextWindow w112 8 (by decide +kernel)
private def w128 : RowWindow checkAt 128 := nextWindow w120 8 (by decide +kernel)
private def w136 : RowWindow checkAt 136 := nextWindow w128 8 (by decide +kernel)
private def w144 : RowWindow checkAt 144 := nextWindow w136 8 (by decide +kernel)
private def w152 : RowWindow checkAt 152 := nextWindow w144 8 (by decide +kernel)
private def w160 : RowWindow checkAt 160 := nextWindow w152 8 (by decide +kernel)
private def w168 : RowWindow checkAt 168 := nextWindow w160 8 (by decide +kernel)
private def w176 : RowWindow checkAt 176 := nextWindow w168 8 (by decide +kernel)
private def w184 : RowWindow checkAt 184 := nextWindow w176 8 (by decide +kernel)
private def w192 : RowWindow checkAt 192 := nextWindow w184 8 (by decide +kernel)
private def w200 : RowWindow checkAt 200 := nextWindow w192 8 (by decide +kernel)
private def w208 : RowWindow checkAt 208 := nextWindow w200 8 (by decide +kernel)
private def w216 : RowWindow checkAt 216 := nextWindow w208 8 (by decide +kernel)
private def w224 : RowWindow checkAt 224 := nextWindow w216 8 (by decide +kernel)
private def w232 : RowWindow checkAt 232 := nextWindow w224 8 (by decide +kernel)
private def w240 : RowWindow checkAt 240 := nextWindow w232 8 (by decide +kernel)
private def w248 : RowWindow checkAt 248 := nextWindow w240 8 (by decide +kernel)
private def w256 : RowWindow checkAt 256 := nextWindow w248 8 (by decide +kernel)
private def w264 : RowWindow checkAt 264 := nextWindow w256 8 (by decide +kernel)
private def w272 : RowWindow checkAt 272 := nextWindow w264 8 (by decide +kernel)
private def w280 : RowWindow checkAt 280 := nextWindow w272 8 (by decide +kernel)
private def w288 : RowWindow checkAt 288 := nextWindow w280 8 (by decide +kernel)
private def w296 : RowWindow checkAt 296 := nextWindow w288 8 (by decide +kernel)
private def w304 : RowWindow checkAt 304 := nextWindow w296 8 (by decide +kernel)
private def w312 : RowWindow checkAt 312 := nextWindow w304 8 (by decide +kernel)
private def w320 : RowWindow checkAt 320 := nextWindow w312 8 (by decide +kernel)
private def w328 : RowWindow checkAt 328 := nextWindow w320 8 (by decide +kernel)
private def w336 : RowWindow checkAt 336 := nextWindow w328 8 (by decide +kernel)
private def w344 : RowWindow checkAt 344 := nextWindow w336 8 (by decide +kernel)
private def w352 : RowWindow checkAt 352 := nextWindow w344 8 (by decide +kernel)
private def w360 : RowWindow checkAt 360 := nextWindow w352 8 (by decide +kernel)
private def w368 : RowWindow checkAt 368 := nextWindow w360 8 (by decide +kernel)
private def w376 : RowWindow checkAt 376 := nextWindow w368 8 (by decide +kernel)
private def w384 : RowWindow checkAt 384 := nextWindow w376 8 (by decide +kernel)
private def w392 : RowWindow checkAt 392 := nextWindow w384 8 (by decide +kernel)
private def w400 : RowWindow checkAt 400 := nextWindow w392 8 (by decide +kernel)
private def w408 : RowWindow checkAt 408 := nextWindow w400 8 (by decide +kernel)
private def w416 : RowWindow checkAt 416 := nextWindow w408 8 (by decide +kernel)
private def w424 : RowWindow checkAt 424 := nextWindow w416 8 (by decide +kernel)
private def w432 : RowWindow checkAt 432 := nextWindow w424 8 (by decide +kernel)
private def w440 : RowWindow checkAt 440 := nextWindow w432 8 (by decide +kernel)
private def w448 : RowWindow checkAt 448 := nextWindow w440 8 (by decide +kernel)
private def w456 : RowWindow checkAt 456 := nextWindow w448 8 (by decide +kernel)
private def w464 : RowWindow checkAt 464 := nextWindow w456 8 (by decide +kernel)
private def w472 : RowWindow checkAt 472 := nextWindow w464 8 (by decide +kernel)
private def w480 : RowWindow checkAt 480 := nextWindow w472 8 (by decide +kernel)
private def w488 : RowWindow checkAt 488 := nextWindow w480 8 (by decide +kernel)
private def w496 : RowWindow checkAt 496 := nextWindow w488 8 (by decide +kernel)
private def w504 : RowWindow checkAt 504 := nextWindow w496 8 (by decide +kernel)
private def w512 : RowWindow checkAt 512 := nextWindow w504 8 (by decide +kernel)
private def w520 : RowWindow checkAt 520 := nextWindow w512 8 (by decide +kernel)
private def w528 : RowWindow checkAt 528 := nextWindow w520 8 (by decide +kernel)
private def w536 : RowWindow checkAt 536 := nextWindow w528 8 (by decide +kernel)
private def w544 : RowWindow checkAt 544 := nextWindow w536 8 (by decide +kernel)
private def w552 : RowWindow checkAt 552 := nextWindow w544 8 (by decide +kernel)
private def w560 : RowWindow checkAt 560 := nextWindow w552 8 (by decide +kernel)
private def w568 : RowWindow checkAt 568 := nextWindow w560 8 (by decide +kernel)
private def w576 : RowWindow checkAt 576 := nextWindow w568 8 (by decide +kernel)
private def w584 : RowWindow checkAt 584 := nextWindow w576 8 (by decide +kernel)
private def w592 : RowWindow checkAt 592 := nextWindow w584 8 (by decide +kernel)
private def w600 : RowWindow checkAt 600 := nextWindow w592 8 (by decide +kernel)
private def w608 : RowWindow checkAt 608 := nextWindow w600 8 (by decide +kernel)
private def w616 : RowWindow checkAt 616 := nextWindow w608 8 (by decide +kernel)
private def w624 : RowWindow checkAt 624 := nextWindow w616 8 (by decide +kernel)
private def w632 : RowWindow checkAt 632 := nextWindow w624 8 (by decide +kernel)
private def w640 : RowWindow checkAt 640 := nextWindow w632 8 (by decide +kernel)
private def w648 : RowWindow checkAt 648 := nextWindow w640 8 (by decide +kernel)
private def w656 : RowWindow checkAt 656 := nextWindow w648 8 (by decide +kernel)
private def w664 : RowWindow checkAt 664 := nextWindow w656 8 (by decide +kernel)
private def w672 : RowWindow checkAt 672 := nextWindow w664 8 (by decide +kernel)
private def w680 : RowWindow checkAt 680 := nextWindow w672 8 (by decide +kernel)
private def w688 : RowWindow checkAt 688 := nextWindow w680 8 (by decide +kernel)
private def w696 : RowWindow checkAt 696 := nextWindow w688 8 (by decide +kernel)
private def w704 : RowWindow checkAt 704 := nextWindow w696 8 (by decide +kernel)
private def w712 : RowWindow checkAt 712 := nextWindow w704 8 (by decide +kernel)
private def w720 : RowWindow checkAt 720 := nextWindow w712 8 (by decide +kernel)
private def w728 : RowWindow checkAt 728 := nextWindow w720 8 (by decide +kernel)
private def w736 : RowWindow checkAt 736 := nextWindow w728 8 (by decide +kernel)
private def w744 : RowWindow checkAt 744 := nextWindow w736 8 (by decide +kernel)
private def w752 : RowWindow checkAt 752 := nextWindow w744 8 (by decide +kernel)
private def w760 : RowWindow checkAt 760 := nextWindow w752 8 (by decide +kernel)
private def w768 : RowWindow checkAt 768 := nextWindow w760 8 (by decide +kernel)
private def w776 : RowWindow checkAt 776 := nextWindow w768 8 (by decide +kernel)
private def w784 : RowWindow checkAt 784 := nextWindow w776 8 (by decide +kernel)
private def w792 : RowWindow checkAt 792 := nextWindow w784 8 (by decide +kernel)
private def w800 : RowWindow checkAt 800 := nextWindow w792 8 (by decide +kernel)
private def w808 : RowWindow checkAt 808 := nextWindow w800 8 (by decide +kernel)
private def w816 : RowWindow checkAt 816 := nextWindow w808 8 (by decide +kernel)
private def w824 : RowWindow checkAt 824 := nextWindow w816 8 (by decide +kernel)
private def w832 : RowWindow checkAt 832 := nextWindow w824 8 (by decide +kernel)
private def w840 : RowWindow checkAt 840 := nextWindow w832 8 (by decide +kernel)
private def w848 : RowWindow checkAt 848 := nextWindow w840 8 (by decide +kernel)
private def w856 : RowWindow checkAt 856 := nextWindow w848 8 (by decide +kernel)
private def w864 : RowWindow checkAt 864 := nextWindow w856 8 (by decide +kernel)
private def w872 : RowWindow checkAt 872 := nextWindow w864 8 (by decide +kernel)
private def w880 : RowWindow checkAt 880 := nextWindow w872 8 (by decide +kernel)
private def w888 : RowWindow checkAt 888 := nextWindow w880 8 (by decide +kernel)
private def w896 : RowWindow checkAt 896 := nextWindow w888 8 (by decide +kernel)
private def w904 : RowWindow checkAt 904 := nextWindow w896 8 (by decide +kernel)
private def w912 : RowWindow checkAt 912 := nextWindow w904 8 (by decide +kernel)
private def w920 : RowWindow checkAt 920 := nextWindow w912 8 (by decide +kernel)
private def w928 : RowWindow checkAt 928 := nextWindow w920 8 (by decide +kernel)
private def w936 : RowWindow checkAt 936 := nextWindow w928 8 (by decide +kernel)
private def w944 : RowWindow checkAt 944 := nextWindow w936 8 (by decide +kernel)
private def w946 : RowWindow checkAt 946 := nextWindow w944 2 (by decide +kernel)

lemma spans : Base 15 14 15 75 := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply certified binary (baseRows 15 14) a b c ai bi ci rowCoeffs
  intro i
  have h := w946.verified i.val i.isLt
  have he : Fin.ofNat 946 i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simpa only [checkAt,he] using h

end TensorRankThreeFactor.Base16

namespace TensorRankColumnReduction

/-- Lift a surjective matrix from the prime field to the complex numbers by
lifting a right inverse and taking the determinant of the resulting product. -/
lemma lift {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] (M : Matrix I K ℤ)
    (h : Function.Surjective (M.map (Int.castRingHom (ZMod 7))).mulVec) :
    Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  obtain ⟨b,hb⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h
  let B : Matrix K I ℤ := fun k i => (b k i).val
  have hB : B.map (Int.castRingHom (ZMod 7)) = b := by
    ext i j
    change (((b i j).val : ℤ) : ZMod 7) = b i j
    simp
  let D := M*B
  have h7 : ((D.det : ℤ) : ZMod 7) = 1 := by
    change (Int.castRingHom (ZMod 7)) D.det = 1
    rw [RingHom.map_det,RingHom.mapMatrix_apply,show D=M*B from rfl,Matrix.map_mul,hB,hb,Matrix.det_one]
  have hn : D.det ≠ 0 := by
    intro he
    rw [he,Int.cast_zero] at h7
    exact (by decide : (0 : ZMod 7) ≠ 1) h7
  have hu : IsUnit (D.map (Int.castRingHom ℂ)).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [← RingHom.mapMatrix_apply,← RingHom.map_det]
    change (D.det : ℂ) ≠ 0
    exact_mod_cast hn
  have hs : Function.Surjective (D.map (Int.castRingHom ℂ)).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
  intro y
  obtain ⟨z,hz⟩ := hs y
  refine ⟨(B.map (Int.castRingHom ℂ)).mulVec z,?_⟩
  rw [Matrix.mulVec_mulVec,← Matrix.map_mul]
  exact hz

end TensorRankColumnReduction

namespace TensorRankCertificates

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

end TensorRankCertificates

namespace TensorRankThreeFactor.RegularCross

open TensorRankCertificates

def ab12 : Array ℕ := #[0, 1, 2, 3, 8, 9, 10, 11, 12, 17, 18, 19, 26, 35, 44, 53, 62, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80]
def ab21 : Array ℕ := #[8, 17, 20, 21, 26, 27, 28, 29, 30, 35, 40, 41, 44, 49, 50, 53, 62, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80]
def acbc12 : Array ℕ := #[378, 468, 379, 469, 380, 470, 381, 471, 31, 139, 229, 32, 140, 230, 42, 132, 222, 312, 43, 133, 223, 313, 44, 134, 224, 314, 728]
def acbc21 : Array ℕ := #[378, 468, 379, 469, 380, 470, 381, 471, 31, 139, 229, 32, 140, 230, 42, 132, 222, 312, 43, 133, 223, 313, 44, 134, 224, 314, 728]

/-- Each of the 81 pairs of interior basis coordinates has eight scalar
directions, two for each oriented AB face and one for each AC and BC face.
The eight extras in group one have outer third factor (1,0), and the eight
in group two have (0,1). Their three interior factors are matched basis vectors. -/
def column (j : ℕ) : ℕ :=
  if j<216 then
    let r := j/27
    let s := j/3%9
    (#[36,129,80][j%3]?.getD 0) <<< (8*(9*r+s))
  else if j<432 then
    let z := j-216
    let s := z/27
    let r := z/3%9
    (#[18,72,160][z%3]?.getD 0) <<< (8*(9*r+s))
  else if j<486 then
    let z := j-432
    2^(8*(ab12[z/2]?.getD 0)+z%2)
  else if j<540 then
    let z := j-486
    2^(8*(ab21[z/2]?.getD 0)+2+z%2)
  else if j<594 then
    let z := j-540
    let triple := acbc12[z/2]?.getD 0
    let r := if z%2=0 then triple/81 else triple/9%9
    2^(8*(9*r+triple%9)+(if z%2=0 then 4 else 6))
  else
    let z := j-594
    let triple := acbc21[z/2]?.getD 0
    let s := if z%2=0 then triple/81 else triple/9%9
    2^(8*(9*(triple%9)+s)+(if z%2=0 then 5 else 7))

def preimages : Array (List ℕ) := #[
  [432],
  [433],
  [0,1,218,432],
  [2,216,217,433],
  [216,433],
  [1,218,432],
  [2,216,433],
  [1,432],
  [434],
  [435],
  [3,4,245,434],
  [5,243,244,435],
  [243,435],
  [4,245,434],
  [5,243,435],
  [4,434],
  [436],
  [437],
  [6,7,272,436],
  [8,270,271,437],
  [270,437],
  [7,272,436],
  [8,270,437],
  [7,436],
  [438],
  [439],
  [9,10,299,438],
  [11,297,298,439],
  [297,439],
  [10,299,438],
  [11,297,439],
  [10,438],
  [13,326,594],
  [324,556],
  [12,594],
  [14,325,556],
  [556],
  [594],
  [14,556],
  [326,594],
  [16,353,596],
  [351,562],
  [15,596],
  [17,352,562],
  [562],
  [596],
  [17,562],
  [353,596],
  [19,595],
  [378,568],
  [18,380,595],
  [20,379,568],
  [568],
  [380,595],
  [20,568],
  [595],
  [22,597],
  [405,576],
  [21,407,597],
  [23,406,576],
  [576],
  [407,597],
  [23,576],
  [597],
  [440],
  [441],
  [486],
  [487],
  [584],
  [24,486],
  [26,584],
  [25,440],
  [442],
  [443],
  [27,28,221,442],
  [29,219,220,443],
  [219,443],
  [28,221,442],
  [29,219,443],
  [28,442],
  [444],
  [445],
  [30,31,248,444],
  [32,246,247,445],
  [246,445],
  [31,248,444],
  [32,246,445],
  [31,444],
  [446],
  [447],
  [33,34,275,446],
  [35,273,274,447],
  [273,447],
  [34,275,446],
  [35,273,447],
  [34,446],
  [448],
  [449],
  [36,37,302,448],
  [38,300,301,449],
  [300,449],
  [37,302,448],
  [38,300,449],
  [37,448],
  [40,329,598],
  [327,558],
  [39,598],
  [41,328,558],
  [558],
  [598],
  [41,558],
  [329,598],
  [43,356,600],
  [354,564],
  [42,600],
  [44,355,564],
  [564],
  [600],
  [44,564],
  [356,600],
  [46,599],
  [381,570],
  [45,383,599],
  [47,382,570],
  [570],
  [383,599],
  [47,570],
  [599],
  [49,601],
  [408,578],
  [48,410,601],
  [50,409,578],
  [578],
  [410,601],
  [50,578],
  [601],
  [450],
  [451],
  [488],
  [489],
  [586],
  [51,488],
  [53,586],
  [52,450],
  [452],
  [453],
  [54,55,224,452],
  [56,222,223,453],
  [222,453],
  [55,224,452],
  [56,222,453],
  [55,452],
  [454],
  [455],
  [57,58,251,454],
  [59,249,250,455],
  [249,455],
  [58,251,454],
  [59,249,455],
  [58,454],
  [60,61,278,490],
  [62,276,277,491],
  [490],
  [491],
  [62,277,491],
  [60,490],
  [277,491],
  [60,278,490],
  [63,64,305,492],
  [65,303,304,493],
  [492],
  [493],
  [65,304,493],
  [63,492],
  [304,493],
  [63,305,492],
  [67,332,602],
  [330,560],
  [66,602],
  [68,331,560],
  [560],
  [602],
  [68,560],
  [332,602],
  [70,359,604],
  [357,566],
  [69,604],
  [71,358,566],
  [566],
  [604],
  [71,566],
  [359,604],
  [73,603],
  [384,572],
  [72,386,603],
  [74,385,572],
  [572],
  [386,603],
  [74,572],
  [603],
  [76,605],
  [411,580],
  [75,413,605],
  [77,412,580],
  [580],
  [413,605],
  [77,580],
  [605],
  [456],
  [457],
  [494],
  [495],
  [588],
  [78,494],
  [80,588],
  [79,456],
  [81,82,227,496],
  [83,225,226,497],
  [496],
  [497],
  [83,226,497],
  [81,496],
  [226,497],
  [81,227,496],
  [84,85,254,498],
  [86,252,253,499],
  [498],
  [499],
  [86,253,499],
  [84,498],
  [253,499],
  [84,254,498],
  [87,88,281,500],
  [89,279,280,501],
  [500],
  [501],
  [89,280,501],
  [87,500],
  [280,501],
  [87,281,500],
  [90,91,308,502],
  [92,306,307,503],
  [502],
  [503],
  [92,307,503],
  [90,502],
  [307,503],
  [90,308,502],
  [94,335,606],
  [95,333,557],
  [93,606],
  [334,557],
  [95,557],
  [606],
  [557],
  [335,606],
  [97,362,608],
  [98,360,563],
  [96,608],
  [361,563],
  [98,563],
  [608],
  [563],
  [362,608],
  [100,607],
  [387,574],
  [99,389,607],
  [101,388,574],
  [574],
  [389,607],
  [101,574],
  [607],
  [103,609],
  [414,582],
  [102,416,609],
  [104,415,582],
  [582],
  [416,609],
  [104,582],
  [609],
  [458],
  [459],
  [504],
  [505],
  [590],
  [105,504],
  [107,590],
  [106,458],
  [109,230,610],
  [228,540],
  [108,610],
  [110,229,540],
  [540],
  [610],
  [110,540],
  [230,610],
  [112,257,612],
  [255,544],
  [111,612],
  [113,256,544],
  [544],
  [612],
  [113,544],
  [257,612],
  [115,284,614],
  [282,548],
  [114,614],
  [116,283,548],
  [548],
  [614],
  [116,548],
  [284,614],
  [118,611],
  [309,552],
  [117,311,611],
  [119,310,552],
  [552],
  [311,611],
  [119,552],
  [611],
  [120,121,338,506],
  [122,336,337,507],
  [506],
  [507],
  [122,337,507],
  [120,506],
  [337,507],
  [120,338,506],
  [123,124,365,508],
  [125,363,364,509],
  [508],
  [509],
  [125,364,509],
  [123,508],
  [364,509],
  [123,365,508],
  [127,613],
  [128,390,569],
  [126,392,613],
  [391,569],
  [128,569],
  [392,613],
  [569],
  [613],
  [130,615],
  [131,417,577],
  [129,419,615],
  [418,577],
  [131,577],
  [419,615],
  [577],
  [615],
  [460],
  [461],
  [510],
  [511],
  [134,585],
  [132,510],
  [585],
  [133,460],
  [136,233,616],
  [231,542],
  [135,616],
  [137,232,542],
  [542],
  [616],
  [137,542],
  [233,616],
  [139,260,618],
  [258,546],
  [138,618],
  [140,259,546],
  [546],
  [618],
  [140,546],
  [260,618],
  [142,287,620],
  [285,550],
  [141,620],
  [143,286,550],
  [550],
  [620],
  [143,550],
  [287,620],
  [145,617],
  [312,554],
  [144,314,617],
  [146,313,554],
  [554],
  [314,617],
  [146,554],
  [617],
  [147,148,341,512],
  [149,339,340,513],
  [512],
  [513],
  [149,340,513],
  [147,512],
  [340,513],
  [147,341,512],
  [150,151,368,514],
  [152,366,367,515],
  [514],
  [515],
  [152,367,515],
  [150,514],
  [367,515],
  [150,368,514],
  [154,619],
  [155,393,571],
  [153,395,619],
  [394,571],
  [155,571],
  [395,619],
  [571],
  [619],
  [157,621],
  [158,420,579],
  [156,422,621],
  [421,579],
  [158,579],
  [422,621],
  [579],
  [621],
  [462],
  [463],
  [516],
  [517],
  [161,587],
  [159,516],
  [587],
  [160,462],
  [163,236,622],
  [164,234,541],
  [162,622],
  [235,541],
  [164,541],
  [622],
  [541],
  [236,622],
  [166,263,624],
  [167,261,545],
  [165,624],
  [262,545],
  [167,545],
  [624],
  [545],
  [263,624],
  [169,290,626],
  [170,288,549],
  [168,626],
  [289,549],
  [170,549],
  [626],
  [549],
  [290,626],
  [172,317,628],
  [173,315,553],
  [171,628],
  [316,553],
  [173,553],
  [628],
  [553],
  [317,628],
  [175,623],
  [176,342,559],
  [174,344,623],
  [343,559],
  [176,559],
  [344,623],
  [559],
  [623],
  [178,625],
  [179,369,565],
  [177,371,625],
  [370,565],
  [179,565],
  [371,625],
  [565],
  [625],
  [181,627],
  [182,396,573],
  [180,398,627],
  [397,573],
  [182,573],
  [398,627],
  [573],
  [627],
  [184,629],
  [185,423,581],
  [183,425,629],
  [424,581],
  [185,581],
  [425,629],
  [581],
  [629],
  [464],
  [465],
  [518],
  [519],
  [188,589],
  [186,518],
  [589],
  [187,464],
  [190,239,630],
  [191,237,543],
  [189,630],
  [238,543],
  [191,543],
  [630],
  [543],
  [239,630],
  [193,266,632],
  [194,264,547],
  [192,632],
  [265,547],
  [194,547],
  [632],
  [547],
  [266,632],
  [196,293,634],
  [197,291,551],
  [195,634],
  [292,551],
  [197,551],
  [634],
  [551],
  [293,634],
  [199,320,636],
  [200,318,555],
  [198,636],
  [319,555],
  [200,555],
  [636],
  [555],
  [320,636],
  [202,631],
  [203,345,561],
  [201,347,631],
  [346,561],
  [203,561],
  [347,631],
  [561],
  [631],
  [205,633],
  [206,372,567],
  [204,374,633],
  [373,567],
  [206,567],
  [374,633],
  [567],
  [633],
  [208,635],
  [209,399,575],
  [207,401,635],
  [400,575],
  [209,575],
  [401,635],
  [575],
  [635],
  [211,637],
  [212,426,583],
  [210,428,637],
  [427,583],
  [212,583],
  [428,637],
  [583],
  [637],
  [466],
  [467],
  [520],
  [521],
  [215,591],
  [213,520],
  [591],
  [214,466],
  [468],
  [469],
  [522],
  [523],
  [240,469],
  [638],
  [241,523],
  [242,638],
  [470],
  [471],
  [524],
  [525],
  [267,471],
  [640],
  [268,525],
  [269,640],
  [472],
  [473],
  [526],
  [527],
  [294,473],
  [642],
  [295,527],
  [296,642],
  [474],
  [475],
  [528],
  [529],
  [321,475],
  [644],
  [322,529],
  [323,644],
  [476],
  [477],
  [530],
  [531],
  [348,477],
  [350,639],
  [349,531],
  [639],
  [478],
  [479],
  [532],
  [533],
  [375,479],
  [377,641],
  [376,533],
  [641],
  [480],
  [481],
  [534],
  [535],
  [402,481],
  [404,643],
  [403,535],
  [643],
  [482],
  [483],
  [536],
  [537],
  [429,483],
  [431,645],
  [430,537],
  [645],
  [484],
  [485],
  [538],
  [539],
  [592],
  [646],
  [593],
  [647]]

def mask (j : ℕ) : ℕ := (preimages[j]?.getD []).foldl (fun v i => v ||| 2^i) 0

def M : Matrix (Fin 648) (Fin 648) ℤ := fun i j => intBit ((column j.val).testBit i.val)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
lemma spans : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  apply surjective_of_certificate M column mask (fun _ _ => rfl)
  decide +kernel

end TensorRankThreeFactor.RegularCross

namespace TensorRankThreeFactor.Cross

/-- The right group has nine interior coordinates on each axis; its coordinate
is shared as the first entry of `Row`. The left group has sizes `(d,d,e)`. -/
inductive Dir (d e : ℕ) where
  | abL (o : Fin 2) (h : Fin d)
  | abR (o : Fin 2) (h : Fin d)
  | acL (h : Fin d)
  | acR (h : Fin e)
  | bcL (h : Fin d)
  | bcR (h : Fin e)
  deriving DecidableEq, Fintype

abbrev Row (d e : ℕ) := Fin 9 × Dir d e

inductive Col (d e x l w : ℕ) where
  | baseA (t : Fin x) (s : Fin 9)
  | baseB (t : Fin x) (s : Fin 9)
  | baseC (t : Fin x) (s : Fin 9)
  | regA (t : Fin 8) (h : Fin d)
  | regB (t : Fin 8) (h : Fin d)
  | regC (t : Fin 8) (h : Fin e)
  | abL (t : Fin l) (o : Fin 2)
  | abR (t : Fin l) (o : Fin 2)
  | acL (t : Fin l)
  | bcL (t : Fin l)
  | acR (t : Fin w)
  | bcR (t : Fin w)
  deriving DecidableEq, Fintype

structure Extra (K : Type) (d e : ℕ) where
  a : Fin d → K
  b : Fin d → K
  c : Fin e → K
  ao : K
  bo : K
  co : Fin 2 → K

structure Factors (K : Type) (d e x l w : ℕ) where
  left : Fin x → Extra K d e
  right : Fin 8 → Extra K 9 9
  /-- In each pair the first function is on the left group. -/
  abL : Fin l → (Fin d → K) × (Fin 9 → K)
  abR : Fin l → (Fin d → K) × (Fin 9 → K)
  acL : Fin l → (Fin d → K) × (Fin 9 → K)
  bcL : Fin l → (Fin d → K) × (Fin 9 → K)
  acR : Fin w → (Fin e → K) × (Fin 9 → K)
  bcR : Fin w → (Fin e → K) × (Fin 9 → K)

/-- Exterior projection of the tangent columns onto the oriented cross faces.
For `abR`, `acR` and `bcR` the first axis named by the face is in the right group. -/
def matrix {d e x l w : ℕ} {K : Type} [CommSemiring K] (f : Factors K d e x l w) :
    Matrix (Row d e) (Col d e x l w) K := fun (s, r) j =>
  match j, r with
  | .baseA t z, .abR o h => if s=z then (f.left t).b h * (f.left t).co o else 0
  | .baseA t z, .acR h => if s=z then (f.left t).bo * (f.left t).c h else 0
  | .baseB t z, .abL o h => if s=z then (f.left t).a h * (f.left t).co o else 0
  | .baseB t z, .bcR h => if s=z then (f.left t).ao * (f.left t).c h else 0
  | .baseC t z, .acL h => if s=z then (f.left t).a h * (f.left t).bo else 0
  | .baseC t z, .bcL h => if s=z then (f.left t).ao * (f.left t).b h else 0
  | .regA t z, .abL o h => if h=z then (f.right t).b s * (f.right t).co o else 0
  | .regA t z, .acL h => if h=z then (f.right t).bo * (f.right t).c s else 0
  | .regB t z, .abR o h => if h=z then (f.right t).a s * (f.right t).co o else 0
  | .regB t z, .bcL h => if h=z then (f.right t).ao * (f.right t).c s else 0
  | .regC t z, .acR h => if h=z then (f.right t).a s * (f.right t).bo else 0
  | .regC t z, .bcR h => if h=z then (f.right t).ao * (f.right t).b s else 0
  | .abL t p, .abL o h => if o=p then (f.abL t).1 h * (f.abL t).2 s else 0
  | .abR t p, .abR o h => if o=p then (f.abR t).1 h * (f.abR t).2 s else 0
  | .acL t, .acL h => (f.acL t).1 h * (f.acL t).2 s
  | .bcL t, .bcL h => (f.bcL t).1 h * (f.bcL t).2 s
  | .acR t, .acR h => (f.acR t).1 h * (f.acR t).2 s
  | .bcR t, .bcR h => (f.bcR t).1 h * (f.bcR t).2 s
  | _, _ => 0

/-- The left factor in each triple is stored first. U and V have a left
A or B factor respectively; W has a left C factor. The W data also apply
when the two C-in-base streams of the cyclic allocation use distinct points. -/
structure MixedData (K : Type) (d l : ℕ) where
  left : Fin d → Extra K d (d-1)
  right : Fin 8 → Extra K 9 9
  u : Fin l → (Fin d → K) × (Fin 9 → K) × (Fin 9 → K)
  v : Fin l → (Fin d → K) × (Fin 9 → K) × (Fin 9 → K)
  w : Fin 27 → (Fin (d-1) → K) × (Fin 9 → K) × (Fin 9 → K)

def mixedFactors {K : Type} {d l : ℕ} (z : MixedData K d l) : Factors K d (d-1) d l 27 where
  left := z.left
  right := z.right
  abL t := ((z.u t).1, (z.u t).2.1)
  acL t := ((z.u t).1, (z.u t).2.2)
  abR t := ((z.v t).1, (z.v t).2.1)
  bcL t := ((z.v t).1, (z.v t).2.2)
  acR t := ((z.w t).1, (z.w t).2.1)
  bcR t := ((z.w t).1, (z.w t).2.2)

def Mixed (d l : ℕ) : Prop := ∃ z : MixedData ℂ d l, Function.Surjective (matrix (mixedFactors z)).mulVec

end TensorRankThreeFactor.Cross

namespace TensorRankThreeFactor.Cross

structure Point where
  s : Fin 9
  t : Fin 9
  bits : ℕ
  deriving Inhabited

structure Sample (l : ℕ) where
  u : Fin l → Point
  v : Fin l → Point
  w : Fin 27 → Point

def bitVal (u k : ℕ) : ℂ := if u.testBit k then 1 else 0

def delta {I : Type} [DecidableEq I] (i j : I) : ℂ := if i=j then 1 else 0

def leftDepth (d r : ℕ) := if r<d-1 then 2^r else 2^(d-1)-1

def leftSlope (r : ℕ) (o : Fin 2) : Prop := o=0 ∨ r%2=1
instance (r : ℕ) (o : Fin 2) : Decidable (leftSlope r o) := inferInstanceAs (Decidable (_ ∨ _))

def triple (n : ℕ) (q : Point) : (Fin n → ℂ) × (Fin 9 → ℂ) × (Fin 9 → ℂ) :=
  (fun h => bitVal q.bits h.val, fun s => delta s q.s, fun s => delta s q.t)

def sample {l : ℕ} (d : ℕ) (z : Sample l) : MixedData ℂ d l where
  left r := {a := fun h => delta h r, b := fun h => delta h r,
             c := fun h => bitVal (leftDepth d r.val) h.val,
             ao := 1, bo := 1, co := fun o => if leftSlope r.val o then 1 else 0}
  right r := {a := fun s => delta s r.castSucc, b := fun s => delta s r.castSucc,
              c := fun s => delta s r.castSucc, ao := 1, bo := 1, co := fun o => delta o 1}
  u t := triple d (z.u t)
  v t := triple d (z.v t)
  w t := triple (d-1) (z.w t)

/-- The regular coordinate on which the chosen individual tangent column is supported. -/
def owner {d l : ℕ} (z : Sample l) : Col d (d-1) d l 27 → Fin 9
  | .baseA _ s | .baseB _ s | .baseC _ s => s
  | .regA t _ | .regB t _ | .regC t _ => t.castSucc
  | .abL t _ => (z.u t).s
  | .abR t _ => (z.v t).s
  | .acL t => (z.u t).t
  | .bcL t => (z.v t).t
  | .acR t => (z.w t).s
  | .bcR t => (z.w t).t

structure Slots where
  abL : Fin 2 → ℕ := fun _ => 0
  abR : Fin 2 → ℕ := fun _ => 0
  acL : ℕ := 0
  acR : ℕ := 0
  bcL : ℕ := 0
  bcR : ℕ := 0

def slots {d l : ℕ} (z : Sample l) : Col d (d-1) d l 27 → Slots
  | .baseA r _ => {abR := fun o => if leftSlope r.val o then 2^r.val else 0, acR := leftDepth d r.val}
  | .baseB r _ => {abL := fun o => if leftSlope r.val o then 2^r.val else 0, bcR := leftDepth d r.val}
  | .baseC r _ => {acL := 2^r.val, bcL := 2^r.val}
  | .regA _ h => {abL := fun p => if p=1 then 2^h.val else 0, acL := 2^h.val}
  | .regB _ h => {abR := fun p => if p=1 then 2^h.val else 0, bcL := 2^h.val}
  | .regC _ h => {acR := 2^h.val, bcR := 2^h.val}
  | .abL t o => {abL := fun p => if p=o then (z.u t).bits else 0}
  | .abR t o => {abR := fun p => if p=o then (z.v t).bits else 0}
  | .acL t => {acL := (z.u t).bits}
  | .bcL t => {bcL := (z.v t).bits}
  | .acR t => {acR := (z.w t).bits}
  | .bcR t => {bcR := (z.w t).bits}

def scalar {d e : ℕ} (q : Slots) : Dir d e → ℂ
  | .abL o h => bitVal (q.abL o) h.val
  | .abR o h => bitVal (q.abR o) h.val
  | .acL h => bitVal q.acL h.val
  | .acR h => bitVal q.acR h.val
  | .bcL h => bitVal q.bcL h.val
  | .bcR h => bitVal q.bcR h.val

set_option maxRecDepth 2048 in
lemma sample_entry {d l : ℕ} (z : Sample l) (s : Fin 9) (r : Dir d (d-1)) (j : Col d (d-1) d l 27) :
    matrix (mixedFactors (sample d z)) (s,r) j = if s=owner z j then scalar (slots z j) r else 0 := by
  cases j <;> cases r <;> simp [matrix,mixedFactors,sample,triple,owner,scalar,slots,bitVal,delta,
    Nat.testBit_two_pow,Fin.ext_iff] <;> split_ifs <;> simp_all <;> grind

def cat (width low high : ℕ) := (low % 2^width) ||| (high <<< width)

@[simp] lemma cat_low (n lo hi : ℕ) (h : Fin n) : (cat n lo hi).testBit h.val = lo.testBit h.val := by
  simp [cat,Nat.testBit_or,h.isLt,Nat.not_le.mpr h.isLt]

@[simp] lemma cat_high (n lo hi k : ℕ) : (cat n lo hi).testBit (n+k) = hi.testBit k := by
  simp [cat,Nat.testBit_or]

def pack (d e : ℕ) (q : Slots) := cat d (q.abL 0) (cat d (q.abL 1) (cat d (q.abR 0) (cat d (q.abR 1)
  (cat d q.acL (cat e q.acR (cat d q.bcL q.bcR))))))

def index {d e : ℕ} : Dir d e → ℕ
  | .abL o h => if o=0 then h.val else d+h.val
  | .abR o h => d+(d+(if o=0 then h.val else d+h.val))
  | .acL h => d+(d+(d+(d+h.val)))
  | .acR h => d+(d+(d+(d+(d+h.val))))
  | .bcL h => d+(d+(d+(d+(d+(e+h.val)))))
  | .bcR h => d+(d+(d+(d+(d+(e+(d+h.val))))))

def height (d e : ℕ) := 6*d+2*e

def rowMap {d e : ℕ} (r : Dir d e) : Fin (height d e) := ⟨index r, by
  cases r <;> simp only [index,height] <;> (try split) <;> omega⟩

lemma rowInjective {d e : ℕ} : Function.Injective (@rowMap d e) := by
  intro r t h
  have he : index r=index t := congrArg Fin.val h
  clear h
  cases r <;> cases t <;> simp only [index] at he <;> (try split_ifs at he)
  all_goals first | (congr 1 <;> apply Fin.ext <;> omega) | (exfalso; omega)

lemma pack_entry {d e : ℕ} (q : Slots) (r : Dir d e) : bitVal (pack d e q) (index r) = scalar q r := by
  cases r with
  | abL o h => fin_cases o <;> simp [index,scalar,bitVal,pack]
  | abR o h => fin_cases o <;> simp [index,scalar,bitVal,pack]
  | acL h | acR h | bcL h | bcR h => simp [index,scalar,bitVal,pack]

end TensorRankThreeFactor.Cross

namespace TensorRankThreeFactor.Cross

open TensorRankCertificates

/-- Numbering of the physical tangent columns for choosing finite minors. -/
def decode {d l : ℕ} [NeZero d] [NeZero (d-1)] [NeZero l] (k : ℕ) : Col d (d-1) d l 27 :=
  if k<27*d then
    let t := Fin.ofNat d (k/27)
    let s := Fin.ofNat 9 (k/3%9)
    match k%3 with
    | 0 => .baseA t s
    | 1 => .baseB t s
    | _ => .baseC t s
  else if k<27*d+8*(2*d+(d-1)) then
    let j := k-27*d
    let t := Fin.ofNat 8 (j/(2*d+(d-1)))
    let v := j%(2*d+(d-1))
    if v<2*d then
      if v%2=0 then .regA t (Fin.ofNat d (v/2)) else .regB t (Fin.ofNat d (v/2))
    else .regC t (Fin.ofNat (d-1) (v-2*d))
  else
    let j := k-(27*d+8*(2*d+(d-1)))
    if j<3*l then
      let t := Fin.ofNat l (j/3)
      if j%3<2 then .abL t (Fin.ofNat 2 (j%3)) else .acL t
    else if j<6*l then
      let v := j-3*l
      let t := Fin.ofNat l (v/3)
      if v%3<2 then .abR t (Fin.ofNat 2 (v%3)) else .bcL t
    else
      let v := j-6*l
      let t := Fin.ofNat 27 (v/2)
      if v%2=0 then .acR t else .bcR t

abbrev Table := Array (Array ℕ)

def entry (t : Table) (s j : ℕ) := (t[s]?.getD #[])[j]?.getD 0

structure Certificate where
  picks : ℕ → ℕ → ℕ
  packed : ℕ → ℕ → ℕ
  masks : ℕ → ℕ → ℕ

noncomputable section

/-- A square minor in each regular-coordinate slice spans the whole cross sector. -/
lemma certify {d l : ℕ} [NeZero d] [NeZero (d-1)] [NeZero l]
    (z : Sample l) (c : Certificate)
    (hp : ∀ (s : Fin 9) (j : Fin (height d (d-1))),
      owner z (decode (d:=d) (c.picks s.val j.val)) = s)
    (hm : ∀ (s : Fin 9) (j : Fin (height d (d-1))),
      pack d (d-1) (slots z (decode (d:=d) (c.picks s.val j.val))) = c.packed s.val j.val)
    (hr : ∀ (s : Fin 9) (i : Fin (height d (d-1))),
      xorColumns (c.packed s.val) (c.masks s.val i.val) (height d (d-1)) = 2^i.val) : Mixed d l := by
  classical
  refine ⟨sample d z, ?_⟩
  let n := height d (d-1)
  let A := matrix (mixedFactors (sample d z))
  let small (s : Fin 9) : Matrix (Fin n) (Fin n) ℤ := fun i j => intBit ((c.packed s.val j.val).testBit i.val)
  let chosen (s : Fin 9) (j : Fin n) : Col d (d-1) d l 27 := decode (c.picks s.val j.val)
  have full (s : Fin 9) : Function.Surjective ((small s).map (Int.castRingHom ℂ)).mulVec :=
    surjective_of_certificate (small s) _ _ (fun _ _ => rfl) (hr s)
  intro y
  let values (s : Fin 9) : Fin n → ℂ := Function.extend rowMap (fun r => y (s,r)) (fun _ => 0)
  choose u hu using fun s => full s (values s)
  let E : Matrix (Col d (d-1) d l 27) (Fin 9 × Fin n) ℂ := fun j k => if j=chosen k.1 k.2 then 1 else 0
  let v : Fin 9 × Fin n → ℂ := fun k => u k.1 k.2
  have product (s k : Fin 9) (r : Dir d (d-1)) (j : Fin n) : (A*E) (s,r) (k,j) =
      if s=k then (((small k) (rowMap r) j : ℤ) : ℂ) else 0 := by
    rw [Matrix.mul_apply]
    simp only [E,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    change matrix _ (s,r) (decode _) = _
    rw [sample_entry,hp k j,← pack_entry,hm k j]
    by_cases h : s=k <;> simp [h,small,rowMap,bitVal,intBit,apply_ite]
  refine ⟨E.mulVec v, ?_⟩
  change A.mulVec (E.mulVec v) = y
  rw [Matrix.mulVec_mulVec]
  funext (s,r)
  change (∑ k : Fin 9 × Fin n, (A*E) (s,r) k * v k) = y (s,r)
  rw [Fintype.sum_prod_type,Finset.sum_eq_single s]
  · simp only [product,if_true,v]
    have h := congrFun (hu s) (rowMap r)
    rw [show values s (rowMap r) = y (s,r) from rowInjective.extend_apply _ _ r] at h
    exact h
  · intro b _ hb
    simp [product,Ne.symm hb]
  · simp

end

end TensorRankThreeFactor.Cross
namespace TensorRankThreeFactor.Cross

open TensorRankCertificates

def sliceTest {l : ℕ} (d : ℕ) [NeZero d] [NeZero (d-1)] [NeZero l] (z : Sample l) (c : Certificate)
    (s : Fin 9) (i : ℕ) : Bool :=
  let j := decode (d:=d) (l:=l) (c.picks s.val i)
  decide (owner z j=s) && decide (pack d (d-1) (slots z j) = c.packed s.val i) &&
    decide (xorColumns (c.packed s.val) (c.masks s.val i) (height d (d-1)) = 2^i)

def checkedRange (p : ℕ → Bool) (lo : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => checkedRange p lo n && p (lo+n)

def Covers (p : ℕ → Bool) (lo hi : ℕ) : Prop := ∀ i, lo ≤ i → i<hi → p i=true

lemma in_checked {p : ℕ → Bool} {lo n : ℕ} (h : checkedRange p lo n=true) : Covers p lo (lo+n) := by
  induction n with
  | zero => intro i hi hi'; omega
  | succ n ih =>
    obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
    intro i hi hi'
    by_cases hn : i=lo+n
    · simpa [hn] using b
    · exact ih a i hi (by omega)

lemma checked {p : ℕ → Bool} {lo hi : ℕ} (h : checkedRange p lo (hi-lo)=true) : Covers p lo hi := by
  intro i ha hb
  exact in_checked h i ha (by omega)

lemma combine {p : ℕ → Bool} {lo mid hi : ℕ} (a : Covers p lo mid) (b : Covers p mid hi) : Covers p lo hi := by
  intro i hi' hi''
  by_cases h : i < mid
  · exact a i hi' h
  · exact b i (by omega) hi''

lemma certify_slices {d l : ℕ} [NeZero d] [NeZero (d-1)] [NeZero l] (z : Sample l) (c : Certificate)
    (hv : ∀ s, Covers (sliceTest d z c s) 0 (height d (d-1))) : Mixed d l := by
  have tests (s : Fin 9) (i : Fin (height d (d-1))) := hv s i.val (by omega) i.isLt
  simp only [sliceTest,Bool.and_eq_true,decide_eq_true_eq] at tests
  exact certify z c (fun s i => (tests s i).1.1) (fun s i => (tests s i).1.2) (fun s i => (tests s i).2)

end TensorRankThreeFactor.Cross
namespace TensorRankThreeFactor.Cross

/-- The physical inner column numbers, their face codes, and independent
preimages are stored as fixed-width digits, one word per regular coordinate. -/
structure SmallTables where
  innerPicks : Array ℕ
  innerFaces : Array ℕ
  freeMasks : Array ℕ

def digit (word width i : ℕ) := (word >>> (width*i)) % 2^width

def pointAt (width word i : ℕ) : Point :=
  let q := digit word (width+8) i
  ⟨Fin.ofNat 9 ((q/16)%16), Fin.ofNat 9 (q%16), q/256⟩

def fixedWidth (d s : ℕ) := if s<8 then 5*d+(d-1) else 3*d

def chosenId (d : ℕ) (c : SmallTables) (s j : ℕ) :=
  if j<3*d then 27*(j/3)+3*s+j%3
  else if j<fixedWidth d s then 27*d+s*(2*d+(d-1))+(j-3*d)
  else 27*d+8*(2*d+(d-1))+digit (c.innerPicks[s]?.getD 0) 9 (j-fixedWidth d s)

def faceOffset (d e : ℕ) : ℕ → ℕ
  | 0 => 0 | 1 => d | 2 => 2*d | 3 => 3*d | 4 => 4*d | 5 => 5*d
  | 6 => 5*d+e | _ => 6*d+e

def smallColumn (d : ℕ) (c : SmallTables) (s j : ℕ) :=
  let e := d-1
  if j<3*d then
    let r := j/3
    let u := 2^r
    let v := if r%2=1 then u else 0
    match j%3 with
    | 0 => (u <<< (2*d)) ||| (v <<< (3*d)) ||| (leftDepth d r <<< (5*d))
    | 1 => u ||| (v <<< d) ||| (leftDepth d r <<< (6*d+e))
    | _ => (u <<< (4*d)) ||| (u <<< (5*d+e))
  else if j<fixedWidth d s then
    let v := j-3*d
    if v<2*d then
      let u := 2^(v/2)
      if v%2=0 then (u <<< d) ||| (u <<< (4*d)) else (u <<< (3*d)) ||| (u <<< (5*d+e))
    else
      let u := 2^(v-2*d)
      (u <<< (5*d)) ||| (u <<< (6*d+e))
  else
    let code := digit (c.innerFaces[s]?.getD 0) (d+3) (j-fixedWidth d s)
    (code/8) <<< faceOffset d e (code%8)

/-- The columns from the matched extras express unit-vector preimages in
terms of two free face vectors per ordinary slice, and five in the ninth slice.
The checker tests every reconstructed preimage. -/
def smallMask (d : ℕ) (c : SmallTables) (s i : ℕ) :=
  let e := d-1
  let val := digit (c.freeMasks[s]?.getD 0) (height d e)
  let y r := val r
  let w r := val (d+r)
  let z r := y r ^^^ 2^(3*r+2)
  let p r := if s<8 then y r ^^^ 2^(3*d+2*r) else val (d+e+r)
  let q r := if s<8 then z r ^^^ 2^(3*d+2*r+1) else val (2*d+e+r)
  let t r := if s<8 then w r ^^^ 2^(5*d+r) else val (3*d+e+r)
  let endFree := if s<8 then d+e else 3*d+2*e
  if i<d then
    2^(3*i+1) ^^^ (if i%2=1 then p i else 0) ^^^ (if i<e then t i else val (endFree+1))
  else if i<2*d then p (i-d)
  else if i<3*d then
    let r := i-2*d
    2^(3*r) ^^^ (if r%2=1 then q r else 0) ^^^ (if r<e then w r else val endFree)
  else if i<4*d then q (i-3*d)
  else if i<5*d then y (i-4*d)
  else if i<5*d+e then w (i-5*d)
  else if i<6*d+e then z (i-(5*d+e))
  else t (i-(6*d+e))

def expand (d : ℕ) (c : SmallTables) : Certificate := ⟨chosenId d c, smallColumn d c, smallMask d c⟩

/-- A checked prefix supplies the preceding prefix for the next window. -/
structure Window (p : ℕ → Bool) (hi : ℕ) : Type where
  valid : Covers p 0 hi

def windowStart (p : ℕ → Bool) : Window p 0 := ⟨fun i _ hi => by omega⟩

def advance {p : ℕ → Bool} {lo hi : ℕ} (v : Window p lo) (test : checkedRange p lo (hi-lo)=true) :
    Window p hi := ⟨combine v.valid (checked test)⟩

end TensorRankThreeFactor.Cross

namespace TensorRankThreeFactor.Cross

namespace D9

def z : Sample 22 where
  u i := pointAt 9 0x1c4d06745a0a847d4f1ecb3d36b2143320bf2e94b31bc939b21e6b0cad41b841e6a22ea29c603540932a220b000207 i.val
  v i := pointAt 9 0x3f686f84851c2fcc8fc0d00c88cb022498bb9036a137d286b9d18501f6766c4408e19f22f1b0769c2c3ca03a63ea52 i.val
  w i := pointAt 8 0x35247743c98662212332cb168718aa6766277f122608fe80e475076537369040b383025862549c73ff019504b8407075135212376d61 i.val

def tables : SmallTables where
  innerPicks := #[
    0xa34da411c8d381bcca5f27938760d060140200,
    0xae5629922853599ccc522891c4c1a0803c1409,
    0xb258aa14e893c9e0dc49241105c2d16088420b,
    0xb04e2652686419e8d046228e06230128902e0e,
    0xb95b2692a8f46204fe7e389887a3c148643011,
    0x9f4b25116883e990c64d219087c3a1c8dc6c35,
    0xaf552793a843b1d4da6c2e158803f1a0cc641d,
    0xab54a81248a43984c05b2d14ca0281388c4002,
    0x2d15aa5512612e803e1ecee74399c8d4692f174b2582b954a84c25928822f158a83e1e0e06c2c150a04c2408038180803]
  innerFaces := #[
    0x7f74877fd4ad5c7cb3cb27d66168db8daa0ce31e3082c011010,
    0x65d43d3fd7ff36fee6b53b527cb7ca0eea5c56cba9ba8541540,
    0x31511f3353ff09ff9bf9a49687b87af56b21b20664bc9bc8544,
    0x11d1bd59f4e7095fdef9eb560eb0ea8fc9e99e8a59a58b84e34,
    0x1af3bd4853174af5c5fda7c37c2cb6d76339338fcc569568bac,
    0x3f01531538709d51e7d37d269ef53f5233ca09a088f98f8c7c,
    0x65f55503d1bf36df03f02493492fb611e711710c79c789ec9ac,
    0x5573377254e5385097d73d72fb3fb27ce8defc9fc8bcc364014,
    0x64d43f1377f559d0177c651b51af06066063062ee3ee26136126c66c36c211b11a69b69a87e714b246616603613609a99a8b81b80cd4cd1cd0654651650829828]
  freeMasks := #[
    0x8001fe00000000000200000000000000000e8170660063e810e8780195000000000042d9f18e881926803d57a058998018fa043a3f9f1de881926803d5f0003700000000000000060400000000010a0007f000000000002486ff8e80e1a010789200fe1001868041e24a07f8400413010589350fe5050d4c841f25a27f9a91a5b051780459003a16420024124a4ff840041301058000100000080000000022800a80a0900020,
    0x4000000000000000010007f800000000000c001fe00000000000e65645762328b7ee8ea104da66600a69a01865791762329b3fe8e61027466600e79e01be16d86fbb2b29968ab95e9fd88ca6cffa36041001998029a68040a7001cb8dc8040246b2536ee2a34532c31a670dadb8d994c22c0615006f3b22090481b460da0444596c3286d31368999165a28b01030008a88c90490002240067b330490490101400a8a8c904900,
    0xb80cd59981f3df40f2e034ae6607cf7d03cf80dd59981f3df40f73c7ed732578bfdd19b10f6dddc1f9b6e4f2443c377707e6db93e9e100011541b49909a000000000000000027e10d811541b49909b3c7fcf32578bfdd180052008a08000000001868062bd7201241256e6c4df784802582918f3162b57201b61a542cc5df85c12248690093100080000920810c80155ad8004804958db1155c0048b6880488008aa0c124800,
    0xea222403716932da23a88f680dc5a4cb68bf3cb36839be9a1f73aa88b880dc5a4cb688f9005e004000012415cf29420e6fa687dccb3ca0e839be9a1f739cf29420e6fa687dcd53ca50839be9a1f73eab283a0f6fa6834c810420082a8c92482403350002a2820120100c8200000008048040480800054524804800ec60083f9880010006000000000000200002d4000bdb000490404b08020fe7248048016120089738800900,
    0x3b000be00000000000ec00500000000000016001ee000000000005081679998039e7a0b4000ae0000000000078007b800000000003d000ae00000000000572767844337df7e2e4205f466600e79e827f272d044337df7e2ce0b320020248b09b26d7b2f975003601041b06cbe08000480410392e481d5ab06506c8e469207f6009b48920054000282b2010481b4aebe574ac5845300126001dda30410480e4a320574241941b2,
    0x1c4811e000010010007120380000040040019067c08822a8224b649245f00000c204008a4917c0000308100270003800000000000214e7ce8822b8234b6f8003b800000000001000000000000000003800380000000000000368015cee4024804029880375120082012c2e8ee4cee136ca0cb6a03b8440049a08200a68005dee0020804044800771130402012d8caee91aa9b6c22c005080551112482082c1a0ef9800d348208,
    0x243adae30ea8944a2090ec938c3aa2512896635aa83288695018318d6aa0ca21a540618fd600cf28d16910c53f59bb3ca345a4431c43b4ae30ea8944a2b90eb738c3aa2512882dd8e0af0eff685b692788f130015ff04501182015400002410401fe4922423ae45638026f2468262a914aa010500384ba2010080023b24e20eaa914aa00018000000000000012f9259c0ce39148e0070800a8092410410055600cb2cc120100,
    0x99efdbaaf09b69968267b896abc26da65a31dfdb1cc94a5d3702737f3073252974dc0b60019800000000000a37f5673252974dc08e00000000000000004c003a0000000000029dfd7dcc94a5d37023a7b806abc26da65a000a000aaa08924804000a002aa820000000088e0144544104124023100511500402403a78f9955544041324e94066001000106803a54f9800404045224000080000000000000026c01ffb48920904,
    0x110000079b6a40008299821c00000480010000000079b604000004400001ecd8120020800000001b6001000000000000a4a000800100000001a42092000240000006d80040000100000000000000006000001e00010400020452e400000240201010008000000000000000cb8000012492498100b3000000900806000e7c0000100904881009900000090080604426400000240201010226000004924926000a74000010090480000000188c92492480000005124000000000000000c8892492480000000124000000000000001494000000080000073b62482402200000186c0004024080000021b4001009020000019e48920900806003000000200000108a850000041000046222a80000004824189829d0000048041046222540000004004199800c00000080000044209c0000024924089821c0000048001000181008048402410002604060021240240001010100404024800020040000000080000008001804000009000200404002000800000881010008002090000204060120241040001800300000920024]

def certificate := expand 9 tables

namespace Slice0
private abbrev p := sliceTest 9 z certificate 0
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w70 : W 70 := advance w64 (by decide +kernel)
lemma valid : Covers p 0 70 := w70.valid
end Slice0

namespace Slice1
private abbrev p := sliceTest 9 z certificate 1
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w70 : W 70 := advance w64 (by decide +kernel)
lemma valid : Covers p 0 70 := w70.valid
end Slice1

namespace Slice2
private abbrev p := sliceTest 9 z certificate 2
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w70 : W 70 := advance w64 (by decide +kernel)
lemma valid : Covers p 0 70 := w70.valid
end Slice2

namespace Slice3
private abbrev p := sliceTest 9 z certificate 3
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w70 : W 70 := advance w64 (by decide +kernel)
lemma valid : Covers p 0 70 := w70.valid
end Slice3

namespace Slice4
private abbrev p := sliceTest 9 z certificate 4
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w70 : W 70 := advance w64 (by decide +kernel)
lemma valid : Covers p 0 70 := w70.valid
end Slice4

namespace Slice5
private abbrev p := sliceTest 9 z certificate 5
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w70 : W 70 := advance w64 (by decide +kernel)
lemma valid : Covers p 0 70 := w70.valid
end Slice5

namespace Slice6
private abbrev p := sliceTest 9 z certificate 6
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w70 : W 70 := advance w64 (by decide +kernel)
lemma valid : Covers p 0 70 := w70.valid
end Slice6

namespace Slice7
private abbrev p := sliceTest 9 z certificate 7
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w70 : W 70 := advance w64 (by decide +kernel)
lemma valid : Covers p 0 70 := w70.valid
end Slice7

namespace Slice8
private abbrev p := sliceTest 9 z certificate 8
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w70 : W 70 := advance w64 (by decide +kernel)
lemma valid : Covers p 0 70 := w70.valid
end Slice8

lemma spans : Mixed 9 22 := by
  apply certify_slices z certificate
  intro s
  fin_cases s
  · exact Slice0.valid
  · exact Slice1.valid
  · exact Slice2.valid
  · exact Slice3.valid
  · exact Slice4.valid
  · exact Slice5.valid
  · exact Slice6.valid
  · exact Slice7.valid
  · exact Slice8.valid

end D9

namespace D12

def z : Sample 34 where
  u i := pointAt 12 0x37e80e8f62e9073f413263e8663842b482465512b2b8051a48360367db801876426b750dd5189a26d4a37226881a0576d153e874839d745a2839b5619540735b15b7f2818b8108a10f1208d368898c0527b8345881 i.val
  v i := pointAt 12 0xbb9620125361238f5942fed0103a80b8067178121278499c356c785b6f259078714a235160857a86ac3171e2644318627241d3325a2b8807187251768f578db754d9c80a2c3003f889a141d3316c62534667812904 i.val
  w i := pointAt 11 0xb31432292f680603e2f0e1491ea46e064fd0e2359cdcb83abf80b72c84a899fec0bed03f0485aacdfbc4132a5058a42308d4aa09e786444e2b89921823c3e836 i.val

def tables : SmallTables where
  innerPicks := #[
    0x405f8ed723757cbd5e27cfa7a33998ca4d220703611068300e06,
    0x3e9e6e76db59a4bf5a26932923a1c0de4e1d88032180a0401e02,
    0x3e5d0e36fb6984b654aa146a247234c45c2b148a2501b8d82c15,
    0x3c5cae06c35d98c357ab948793c1b8be5b2d1188a34198b04605,
    0x3d5d6e26ab4182c04c2452080399c8d0552a14c9248208a04e26,
    0x401fef86cb4d8cb056aa91e7f3f1b4d83e1d0e45c2d158a83408,
    0x3f5e8ea74b519aca64add2e964aa18e261301648e401f8e03e1e,
    0x3ede4f077b85729b44a150882409a8d25e2e8f4783517894481d,
    0x1eeec73379a2cf62aed74b258ab156a652a853a9c4a24d188b452210e833e1ecee763a9acc8632c15c984b2510c8432188c052221085c26120702c14090200c0200]
  innerFaces := #[
    0x599dda295ff3eda655ffb5ff6a03aca2cb673516612962528dfa595c7db92a865500454f123e242630cc60,
    0x3f5fa39fef2c5e2a9489eff6e1785586eb0d13969a1da66f4cd32a80dd936b0d6c9ad818b8114422822c4,
    0x871c4aabc17778e58b7d670bc6b6f76de85298a52d337a66ba3e7a0c63896906d2032ac89a31342dfcdbf8,
    0x1adcfb7b55d0c2a2a9cfa2b09299c7338852b5163a2c58c5ba427a09f4106c04d806a51d4a0da3168a13dc,
    0xdc1d6e7bc15678ec4d7d65faca1e2c4e4c9c96dbe9a1734284a731c163816911468a8d01879d0e7a1c1cec,
    0x5995917a1c50c2e44fc0494ce66c7d6dfb4cf6dbbdb758c4f189135c0dd21ba06808d006d12da20d6e4c64,
    0xed1db82adcd12aecf14fa3ddcbbb9570087898f12431c4a3b4cf7479e8f0c7d0d820c39187113526d4cda8,
    0x3fdfa286b5397ed57ee03561e071c4a2c94547ab8f548ccd1997481e9004d649ac6a541a0873a4e744aa4,
    0x8f795fd3fdaef1589b9827612c074c0e9093b1274d8edb1d483b9074a2d95e9abd24316862a8af515ba2b40e2c1c547aed9c7b3880ff01fb03f48cd8df89bf063e2c7c2cacd95851a8fb65f6c1134226244c3a1e2d115a216ff062c8c58f129a6d34d8e9b027b24f61160a2c0]
  freeMasks := #[
    0x1270f027e011118d478a31c849c3c160404446351e28c7217e85858162202af2e3cf28dfee2c2e058dc5e88a3fbdcb7bbc32b6c2579fc6befcdf3980e8132fc55273159b037ba76249a9d34648ce4d74a1c7c473f839cc85c5c3da9d113832546af784759d6990c02db4901e80b310c4448014020816da18eeed73616a39c74b7bdcf330bde091a392fe5dbbbc4e73d27d304088c9d4889bd90076b0000586258482012010018ed0005550441248240000151800010c664a402002490014850001649d6900824104055310003f68490090480080045890004348d2004004024047080003a6c4c2010490400008ec000141014820020900046600002aaa28a0004124100446c0001618960040040240135300015c261a090092490015250005758c6900824104,
    0x1679f87dc85318b8ea224e9459e7e008e14c62e3a8893a50d540e2638cc88823f28be3f5322dade00566066563bce9b9c8b6a400159819958ef3a6d55035bf23322208fda2e8bcc481613805598102114da20bcc7b52f201a02a32dda4293c80a380f0400009b4da2d9699e7e1f2e14c62e3a8893a50b00033770000000004004104cb7d86f427e40eb542bc2ae2d4aed0e88c888b8bb297b929b1f40b227e73c05d3be808ae05902c89f9cf1174cb322020082000000002492482410a620982c2ee280137dcfa022b20fe0b004660645f3bcc9800602800a24a4e100804020028112002228028410082480a4e0982ca6428a133dcba0202a14a00237c42c490412400a4a2982ca6428a9375eba062981bc0b232a33a0cf7ae898a620f82c2ea2c4137dcfa02,
    0x1c09630604045d9401442e3870258de7d01176500510b8e0e2963b1f8c4915a3a4b80c3da209a29404563005d7d0aa94901682a02258c4004344a23aa099e7f3465038b143b144618303cf0330004171c0608594550f3e31249b0c828141002000c80cc0ccce3b0faefbe160dc1a33033fe0cd38acf07364fc9da93a1305e4f1ac2aa65d6e350981540041daa6bb0e7f0686606dfa725cb2310611240039c7d7c090010080044a80006d32e012010490002563000381af1a41000001005068000cd18628200201040614a00039c69280900100800010c00040414400000000007479000235649840000040004001000cf3dff8241209240502040033cf7fc400090480194a8000e53ac202010480004079400101114649041201010489000e71f5f020120820,
    0xa00006ab000000000000000280000550000000000000001e6eb31d956020191f3bd0206b24aeae55a39301320940a2f79312e28b1a80a333b526053eb4c0ce5c7a25f248509a8979313608b1a80a333b52600a183ef86446221f08627961ded510334a06084e521c02aaed7dc3a542213411eee306b9ed510e54a06084e521c02a660f88d4c7010277e868402a8ed513084a06084e521c02af81ed8eea702315ee04639c3e17be3bacd18817bc018650f934feeea4a0a03a7207394005b038000a8a00920804800012a8c0016a3806492410083e1417bbacc0cc4ebc13867000082e001444112400480083e1694bba991cc57bc018650016c000002a280248201200001b82000dd18a1124000100f81050eeb303313ae00e3940012a3800500401904020800,
    0x1b8ebc75c2526408ceb6b7346e3af028c94990233adadcd2b06383fab92380ba330ec11b5b0a360882033220a41b4d024721178464006695f088b3138a539e0169a301309b680052940840a60cca0948365049e8713a80e82428fe414f88477e29a1aec40c063b747d8f9e72f53eba799319dd4a9e3eb04711a079ef80520d36c92233e945e36917197e1db4e5bae0dd903c56a8cecfc55a8300004a001150544000000000101b4800af2686920124000051040000e6af10490012080045b0000878c06804120820052650002bc9a1808008041004d14000938946100904904048658003cd326e40000008002834000192b4c92490010405321a001a3bf56082082410105268007cea9512490400400829800121bd74080490080029a08001c2f48920920900,
    0x12610539d94590934484882849841518a516424d121220a159ca165a22426a245eaecc36ef0071888808aa986c30594336e835a20f519263a9ede3b4756dece9c6dcc24cb485ad8cb4c7e596ee7a362c78908ba07e9526156464b5b1f36a308e82094866a2a2d1fab86f0e4f64e1c85c56490b5e6410df9cffb332867abd28df002c7585c250c7d424fc7aaa18cb122342ba428400941054ac00490200281e5640104100100d241800a0795992000082003aa140005bcc8c4124800100aa5100003b7730240201200202460000510020120124000b04480014005092490000000ab420000eddce0820920800800080000000080480490002804400005100008249009009891800a3ce2a804004800016254002de7cac48040009008815000b79f2b100020824,
    0x207b46785400518265040b6081ed061d5001460994102d9cf5b0f609c2e5f42653f2874c05a0a611401476510912da9e4834809f8746924829201f7d6c2f8270b97d0994fca1d8da4febd4463462b845368beb6c9e294058c5fcb01dc8f4be4833e89f87469248292019044ce0200ea46740b45821b2f2048a5c82e0ec0003b231ccba5d41e753522c295202e95ca1434502ca0e22ed612bb16931f1fc4d2e18e7584b208524efc7f988111bb9e36486005e800015ba176082090010522ffc7f988111a99f164860212200037e2b0a4920020000043300041451110002400414c5f31fe3cb174ee5c592180168a00057a84812480002016d7ff1fc428e6ea77c5b2185225ec7f8d8455a99f16486020ce00022f2a5c40241209000719000400504824104024,
    0x1c95306038890092583d041e7254c07f2224024960f41079872e616f315e3e598543121dc5455356231030939b482e2a29fa5b09dd078ce0cda57a56a77cc3a7611f73da760770f3b2bea1a5bd5417e52b4cb8d273711a538da93981a17aa6f170627447a0bce8d9b45fb254c078e224024960f41079d7691a61f4872e32e7ba1f0a454547a6231030939b482e1e07c4c53b0a920fd0f2310905801000020880a0120800000a204800280a2a90092410003222800346a9cc0804004901aa2c000acb44d924800004040a88001d4f0f24924804800e82600089dd3400000412002a2280036621c4000480490008a8800d0ff6780092410401283000282082a40248008002aa6000fdb41c92090002003283a002970d6c4800800100080480080aa22800924104,
    0x8c000000d1a0038001240001020100000000000410400008c000000449687c04800924a300000007043014104900008c0000000486878240009248300000020098020824100100000000010100040002000003000000106580d0820000100000000004904500000080023000000076400240049040004000000189647d2012492480000000006180c000000010880000005c10c15049240209c4cac8800000000480092087078b6020000000804900105c4f248080000002012400410100a1000000000000000000046a8088000000249249249707897020000000804900105c5dac880000000048009208001e80020000000924924924057884180000002492492490010a4240000000000000001c4d84c900000000480092080110a420000000000000000000000003169b014924924920000000064864852492492480000000132190b49249249200000000e4a648d24924924a100000022093164904800900000000020200080000000021000000024131c4904800900000000009208a000000000000000001361b094924924928400000044a687c00804900800000000041008000000000840000002000cd1241200240801bc618000000200000008519871840000000124900124020142000000000010000001086f1840000000800000124801b841800000024004000840e640000000000904120000447906d800000004904820010e030320000000800800924002148480000000000000404086b186000000090410002002214840000000000000001000008490008000482000490080000240104800201008240001080100013020904120900800212400208000080410402000040024130248248049008042024000040904124120000108490008100092010010000420200000809240000200001004802091024124124000000012000244080090082000000000004030000000000000040124092000804824820]

def certificate := expand 12 tables

namespace Slice0
private abbrev p := sliceTest 12 z certificate 0
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w72 : W 72 := advance w64 (by decide +kernel)
private def w80 : W 80 := advance w72 (by decide +kernel)
private def w88 : W 88 := advance w80 (by decide +kernel)
private def w94 : W 94 := advance w88 (by decide +kernel)
lemma valid : Covers p 0 94 := w94.valid
end Slice0

namespace Slice1
private abbrev p := sliceTest 12 z certificate 1
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w72 : W 72 := advance w64 (by decide +kernel)
private def w80 : W 80 := advance w72 (by decide +kernel)
private def w88 : W 88 := advance w80 (by decide +kernel)
private def w94 : W 94 := advance w88 (by decide +kernel)
lemma valid : Covers p 0 94 := w94.valid
end Slice1

namespace Slice2
private abbrev p := sliceTest 12 z certificate 2
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w72 : W 72 := advance w64 (by decide +kernel)
private def w80 : W 80 := advance w72 (by decide +kernel)
private def w88 : W 88 := advance w80 (by decide +kernel)
private def w94 : W 94 := advance w88 (by decide +kernel)
lemma valid : Covers p 0 94 := w94.valid
end Slice2

namespace Slice3
private abbrev p := sliceTest 12 z certificate 3
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w72 : W 72 := advance w64 (by decide +kernel)
private def w80 : W 80 := advance w72 (by decide +kernel)
private def w88 : W 88 := advance w80 (by decide +kernel)
private def w94 : W 94 := advance w88 (by decide +kernel)
lemma valid : Covers p 0 94 := w94.valid
end Slice3

namespace Slice4
private abbrev p := sliceTest 12 z certificate 4
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w72 : W 72 := advance w64 (by decide +kernel)
private def w80 : W 80 := advance w72 (by decide +kernel)
private def w88 : W 88 := advance w80 (by decide +kernel)
private def w94 : W 94 := advance w88 (by decide +kernel)
lemma valid : Covers p 0 94 := w94.valid
end Slice4

namespace Slice5
private abbrev p := sliceTest 12 z certificate 5
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w72 : W 72 := advance w64 (by decide +kernel)
private def w80 : W 80 := advance w72 (by decide +kernel)
private def w88 : W 88 := advance w80 (by decide +kernel)
private def w94 : W 94 := advance w88 (by decide +kernel)
lemma valid : Covers p 0 94 := w94.valid
end Slice5

namespace Slice6
private abbrev p := sliceTest 12 z certificate 6
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w72 : W 72 := advance w64 (by decide +kernel)
private def w80 : W 80 := advance w72 (by decide +kernel)
private def w88 : W 88 := advance w80 (by decide +kernel)
private def w94 : W 94 := advance w88 (by decide +kernel)
lemma valid : Covers p 0 94 := w94.valid
end Slice6

namespace Slice7
private abbrev p := sliceTest 12 z certificate 7
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w72 : W 72 := advance w64 (by decide +kernel)
private def w80 : W 80 := advance w72 (by decide +kernel)
private def w88 : W 88 := advance w80 (by decide +kernel)
private def w94 : W 94 := advance w88 (by decide +kernel)
lemma valid : Covers p 0 94 := w94.valid
end Slice7

namespace Slice8
private abbrev p := sliceTest 12 z certificate 8
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w72 : W 72 := advance w64 (by decide +kernel)
private def w80 : W 80 := advance w72 (by decide +kernel)
private def w88 : W 88 := advance w80 (by decide +kernel)
private def w94 : W 94 := advance w88 (by decide +kernel)
lemma valid : Covers p 0 94 := w94.valid
end Slice8

lemma spans : Mixed 12 34 := by
  apply certify_slices z certificate
  intro s
  fin_cases s
  · exact Slice0.valid
  · exact Slice1.valid
  · exact Slice2.valid
  · exact Slice3.valid
  · exact Slice4.valid
  · exact Slice5.valid
  · exact Slice6.valid
  · exact Slice7.valid
  · exact Slice8.valid

end D12

namespace D15

def z : Sample 45 where
  u i := pointAt 15 0x128a63225a80f43144d622c7e5365c3aa70da089cf2bb17ea6457bb0a58e860fe462377fa8205bc49959e0522f9a76d273a124eaf9fa035bec4144354fa9a02da0e1444289be1236d61ec29e24921c440072383f4b430457e024400456d8854f0e9031481cdc00b56c1765f56e9eb7a092bd9b97e88274380e971ca3a59c0bc9310 i.val
  v i := pointAt 15 0x316e21ebce8daaa09881e0432993089ced0306a2011142e77a8044c4aefdb809820183e728121df0cc0b049ce1923da384f886eb7615602adc3632b30c7d91034a90537f0aab257320168ff8d1e20d0a9ebfc78ce2ecefe8605c3cab5a4282387ac1e6e21232723f2ce046ac24e04104cd691c2be785cc9d05c3604f96231564c01 i.val
  w i := pointAt 14 0x227652770042cb7730b655a2664180c85fe2a252d5d9fd6605603597bc0324ca203e3b42bc10d92db4398b9c00ae237d9c60741711b061f74d64906c866d7060da4120df380dc96068784 i.val

def tables : SmallTables where
  innerPicks := #[
    0x141994b64b168a409eaed7634554a04fa210e83281188a35160a04e1f0f0281202,
    0x1409dce2411f8cb89c2c7632cd34994723512802e11c803f1d8b85a1c0d8140200,
    0x1439b4be57228c42e0ae36fb795a9d4e2491873391c4d6622f1746e360a0380e06,
    0x13f974a24f23893fdd4d067b15789b4ba591e863b1d4d0582b958823d1e0c8200f,
    0x13a9549a371587c21c0dd6532582c053a894282409b4d8643197cb24a1c0884217,
    0x1429e4de6731883c1b4d66ab2176ba57ab92a7f3f1f0f67a371a8d253249208826,
    0x13d9a4c2531a8bbf5f8e66a2d568b054aa1168a42a10f278381bcca3e1d0e43a1a,
    0x13e9ccd6491e8eb6188c3612f97ab85bad9489e3a154a8522888032180b054220b,
    0x12c90c72271187411fcfb7d3e5eef67a3cdd0e772b91b8db6bb4da4ce66b317eb9592c558ab53295309449a45207d3b99ccc613016cb44f27134984b219086833188c05e2b150a44a241184c240d060200803]
  innerFaces := #[
    0xee077acd499474c5dd36bd06d3481e2cef59fb726081b195e387bb9673e59cab263ac988896c7cfd3ea69fa9a21c4422bf2440191000629118a41d0e174381e49c,
    0xee0544cdd01953ecf43a0f4837d81636058937f34dfc9fd0e0208c0822e1b0f86c2ac999e864cacf3ea6c110a44428d61f3d2d1f4b40dc0137003a59c79265e498,
    0x113b77c555de077c77c0575483758b72d550981667386dce1ab4859ab0b6ac2b3276e5899b4116d040f2bc7bb13bfd405bc416f04f1253c48f5bd0bf444b8e52e38,
    0x165bf77815782525b7c057741bf594ca6080b195bc6569592e83438082635a4cd692e1b189454c3aa70ea8c743122f948be3b694110b1f0917c240391c4af652bd8,
    0x113357c77496dd6e9bc1b4f0d0ffaf3a73879ed1e1a54c69522016c805af371a3272e59d88969225a3f531fd4c3e461f918016f448bf0a21c4f1313c394f0e17d5c,
    0x113b505b35f1577acdcc06f06e551312f887aec2bbb0a937f68342e0d0a70f2dc3ca57cf9e8617a180d62135883f29cfd4d1eec17bb02849428864a2186d072b6c4,
    0x16cf16af4c06d5e09dba6d4dafe273b89ce8877e0ab7b38bbce2e9c3ce387ace1eae588f9622251449450fca67f2983cae4f2b8f9191f094d61e7587837012b60c,
    0x165bd4065c5abf4c5d43a0d0d83fe21a564ad592a2017bf1a3fc68b5fe3d7f8b38be8c9d9ab0e6d053b691eda428491a12406294ad826b6085f5657d584af71d0e4,
    0x99453ecfc360d41bfc1b970d0f481e689cf860d61834c60d20444c1112cef4f3bd27ce4df39221dec877a7b46ded1abb0b82adb0ab6b1f66c7d8f1f62fc69b5fe67f42dfd0ab484ed212f370fcdc235a595f3b57ceb3273cc9c8d624c3ab31d09c7423bfd1eff432b39cace1f3f17cfc35becd6fa75be86d065b418871061c400e4643918f4b508af922be24404adb06b6c04f0f3d6f1f5bc0bf412fd012e3ce9667a598]
  freeMasks := #[
    0x2427b2bd92fb3e0b030762d128cdb4909ecaf1b40cf82c0c1d8b44a336d354648b9bde548bc05241cec8c2254393476477cc48ce84ebfe0aad89fe96532da6f404e8ac2eac91be3e6b6a594a574bf62e1040264d909b09b24b8749f1a0047d6a72dabf36f16a6de367156ef7cc8ae2c0874a5385bd6cb26e3c5922fedabf2cb1b64bc4aeda46fb301f15cafac868f24ade61eda9bede1a09946561e34900309a61000021bdbe733ec9e4c0c1db1ab13f6da84836900042880808892102106496f6f833ea2b3362d070879dbf11f2e917b99ba62911ca901244ec12ae0345bcf465a0c0e7620264daa74b9724001aa38200030c1801124124920804016202a8001bbe387a48008041241000aaaa20001ac382bb001248208040002e080001b9490fac10480402400002b88800010eba2122010080002001580a88001d0c78d6092012402010004a92800064da414b0082012400400686c88001f84d0fe8800120804100422a08000743b63520410482410000088620001f8670fc49008240248000289800001a63a0b220100800020014844a800178e587e0804124904000540828000208a000b00824000124010a8c00000410400440009249200000a1b000007eb361f204004920104,
    0x2a3b40fad047cc3a3488edcf3e960ea8ed03ecbeff30e8d223b73cfa58399b4fb374f584e7d643514fec2e8d857a5413fe972be04a6aa66d3623d99dc2510c33e8ea0824b09121108a009e6ead25cf520671367de5756b96f96521f3e55880330230114fbe430f884d5d1f747d53bc0e82e01bbf2dd63f483b3c91c9822130a0f936808ac64737952fe970231128b82243bb7519bc580f0f8ce0066601d00067cf450faa23825b44514114c927013d96a9b66f0ef99c3f456233399c038aaeb684ddd1f747d53bc0e82e01bff2dc634d9f5ceda870b1f570c88fc48462e0cc49504dff712607aef9562b2fd600285d0800010d1d573009240040240215709000122bf58a010492092400085058c00060ad74a10000492400002150420001001550001049209240002929840006478b0d3208048001240221a0800005a2a45041201240001008154800006a09f6ea041208248000025e0100017a871c28120100904100211c8400064f830f10412002012002b4703000169d00de4120020824900a971040005af0831a0092492012402a0449000031ed18688201049009008554800006a0df6aa04124824900001546b0001da9d970880492010000009698c0007429e58204804024104,
    0x2af6c1d524b8058128965a19fc25d8abdb07536d001604a2596867f097605191b5445c9c0c520c362d472801c15ac4295bdc31f9c4f9a85f9608ebb50d8bd0f49892bb2b224350eaadb8712b711ad7c515186f18c0fe720a3ff99afcd2a98e24c3952d3756c27d4d6c0cbed4be3c3d4618ee256528d728bc1d92416940c733506a2660a7577fa80210e4a31f9c299a04f160b754aff34b940a8b7100196315bdea9c2a2b04ca117a0426cc848888ac21dcc77abaa64148b53212b5789996aa39b043b8e00085c950270c2659403018b297db540a830b129b02a7278a8aaf2b04ca6d0c0426cc848888ac21dcc0206b140000202828b00020920800005ba1600000d0c426c000804820800022b540001e6c520c2410412000400d2a4200007c958ad09041248009003603080000149b2b920120900900005180100005c3d80d81001040041003403400001d27623f04024820904004038600005415005092012400090020075400000008200240000209000098a80000079b34034124900024900100f5c0001505c214248049000240009a1700007993c2940049208041001081500001d27623f04924800904009a38600005111401092010400010012ee100000b69901804800020800,
    0x3a1bb5429613c12ff324da0335daa5e86ed50da7af04bfcc93680cd76a979ea194cb6170251835808aee4163105afce7349bb273fe582b872a052abfca144df61203189a820808a61a05e0e6ed12d85b011ba3fb6a8ddb5c45d2ab4d9664f18fb32f136bca438182e61725412c82a462c71f2dde366fb9338a8d94ecc06cc25dd2037cf387e32a717191e86a026c28dac9282afeb31019a997cd9d4c1d5ecbf91e2bd9f755037d84d4c372a1a00049a642350832ced8ba000a28a308a60b251682ad782653bb4d952326403ba0ea0c5a1e7d044b4cad763e2a6140e0eaf3b33421ee1ca48204c054a88659cec00126480000d3166ba04820904020002dda30000b447b84c0000008209002f568c0007d05ff07200208200040014903000034cdba6c1209049009000e74480002802a22204824104800003dca30000b447b8480001200208002f4400000550555052002082000400850910001541d74900201008001002540a00005fad570d0080080000000080810000000820800001000040000560280000fb94618208248208240090921000160d8ee788008200208002d4400000550555052002482010400958b000017495debc0200200000000922080000d3166ba24004924124,
    0x30d2e2dbfffb1dd092928109a0810cc34b8b68000c77424a4a04268204319e25600b79b2291129dc5f364877275a083ee3942ca2666002d044228a3b0cd63790eaf309135e0e099685c4c3639b7cdbcc17444a6afd2a8c043d30a0b0508d0180180083e5302841362d8505efe657140613211049a3b83462cd13ab3aab080a165158870d71c970c7a226e1bb00672c3f0f462828c089a133300118100842a2b0784c2754a7c90a9425726661dc7a35821175e462deb26bc819925591f36481fff96828da74621122640d6f4f42225eae6fcc898ebc19912d9859b60853e083358de934bcc244d7838265a171000408ca000268209160400000082400d50108000151040108209249040002062f800020880829009241209040001a3a0000820002849008240248001000c2000014411100090402082001810848000aa8202849048208248006020380000a28888800100120000001421c0000baa224f482012090090074200a0000f6c988c048041000040010832000038a22670100000020900116af0000034e113a00120104900018083a000028a222200040048000006468c20002caa819f20120820104001120c8000baa224f4800824004100400a220000008088824804900024,
    0x3dcd30100dfc517753a1a48e1485acf734c047c81145dd4e8692385216b0a27a2b53138361c66e49b01b45304194962a184806a848a457d9a2217488699df983ccbc766e20d7b41eba17f73ec140731725bd2e986837e2eeb1c329ea3242556783653c9d6cc1f4566bf1e449dc656d5b798d8f7ea6ea092522f41f91ae047ee32582586d04a734c04064d145dd4e8692385216b010f18a1e8655ae572156da7a085a149a4b0c85936b1d57289b4d16002112d80c06164931130316f6596cc9edca21949059268ea42c0ab4f13b22b3e365db1e448642a26a35bf6da8464b1aeb1cc8a10d1b512974eded0fa1006429b000005e8324b2000012012401b42cc000043a315bc92482480000009081000015a8d52e0492080012401248a400005c835cbc8008240040006129300005a4fd5ca0480482492400a504400014995d52c8200248041006941820005ae7f7c00410082012000252ec80007c29deb89041048000004d01860005fa7e7802002412010400a0a8500013d3e033c9209049209006943100005265754a04100820120002102980002a8a8a000241001201002d29a400012c84744000208200240034a48800174bf96041249008048002809940004f4f22ef24824124824,
    0x2ef25d5aa2c1e530006d6c667489cbbbc9756d74e794c001b5b199d2272d866e7360d65d1341c3d66f1186a336ee0ca5f2588a1b508b74422d007029e8da27b944f8d1559d1e847c760edfd22298faf47434754b7bb7f1bb9c811b6b858594f3a6e46c67eb49f33f37bfb0c15996b0dd2fc8d45013ec6ba44b75b9426e2b204d85c9d83d6be2d7f7335e8c8445382d0eddb2896081048b8c16f493c0e3b41b6c86934df9455f3ff57c6b566ee30ee93565a96c0391dfae26736d59c10d34d880dad7f736be0c8445382d0eddb2896114b91cd6385cb5b223d3aa6bc7e0c96245bb0002f5f78d38934da40345800344220007bf9770f0412080000000851480001e54554949248001048002a45060002c45443424904100104022851c800040ffd8a01209200201009251320003c7ab21c0082400000402451418000e44015c082490400410018416600006ed663e0400080080000a554400000e1f45481201000001009210100006ac3d07724804900104024044180010387cbdc0001209240000b15460007f1c91b900024104024006d4058000ae1f45c89040240240002204020002aa8220a2080080412002245418000fd7707b09249240241009150120003b92857220924100104,
    0x235d3e5cd6113133020dafcbeea7308d74f90ca644c4cc0836bf2fba9cf1d8637e785d54626145df624f652d0c9f070d35988b1912eac92192ad56b4eb0c911eaee169cf597fac3dc76f222bc01a4b11c0d14164f4070002557041ec785aaac28c71c72f59a44123213c6857955189059b799975347cbc84f1a23ed54624166de665d4d1f60a9434d6caff5de624b28360a0586b0add415eb044d430a3419088400439b00c617239998181f5d75c05d01e4804c02496b3202211fbbf05c29195c5287dc140ee68e205a6b6063e5584bebd267bf376d6319beb25c6512eec6bc4957ee113504201025269a0d8000501600008aa888b00120100920016baa58000574fe7389208241248005afa020001d797144248209049200049681000164f5d50092412092010058d040000666ca407201001000240140cb58000665aeb100248040249005a5a5000037fb59cd2080082080001088340001aa0db6349041209200005202000006201c70d04000904020004b4a58001eefd7f0c120820824800524a160004083ed8e0412080490001094b0800100a59c3800482010490052609000048abcd8e20024924904012b0b48000774fef10124920904000426a120004083ed8e24024924120,
    0x40000000003633a226024920100008050b860e8000000001040240208002000000000643092661001209201050000000000ed8a4b884124904900020000000001c7922d49208040048250000000001bd200ac8490490490000000000000f31980f60001000000000000000001440209000000800000000000000000f07b0c60000040000050000000000fd880bc0492492490002000000000dc7912149248041048250000000000e9284b80492490410002000000000674e92660001209241050000000001b92243c84924904920000000000007b4800b292492492482400000000007144c25a4000100900a80ec458f20000000004820800104800404241000000000000000000000280ed4d8a280000000048208001048a06a536780000000001208200041228044680a140000000001041248201a07e1322c00000000012082000412001440801280000000000000000000002e0b600d0000000012492492492681a8058f08000000004820800104800101004000000000000000000000001ed6495340000000049249249249a03e1366880000000012082000412000f92c84140000000049249249249a07e0326c000000000120820004120004548102000000000000000000001800000000179921ac20920020804060000000005621a2108248008201050000000001fcd2925a0000020024920000000000100020202480002082500000000035d8610da000002002480000000000a21100a40000000000000000000002880412000000000000000000000000a0520840000000000050000000001dcd612ca000002002492000000000810022820248000208250000000001f596924a0000020024860000000005475a2108248008201050000000003558282da0000020024940000000005520801280000080092480000000000d408a080920000820801818d8600000000000800000000080509960490000000000002402080080492815300000000049001009248042e9a448d000000001249041248008030a98ab000000000492090092480028810025000000000000040000021148a51320000000000104100824980783060ed000000000040241208000060601800000000000000000800084568b06650000000012082010000081b0a8130000000000492010090488474020441000000001208201041008030c992b000000000492010092400008a90204000000000000000000040c0010600300000100049008041200380041810800012420020804124800a0012600000000100241248001240180001800402010024124100904100a0012604100000800209041041040380009000800010404004100120100c0002204200004101001200048040280040000802012424000120800900e0002400200004009001040048040280008800c0000240010400090480060002400100804009041040201040200040000c0201040402412092010060002000100000908208240040040000001010802012404804024804800a001020020000490820820104924]

def certificate := expand 15 tables

namespace Slice0
private abbrev p := sliceTest 15 z certificate 0
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w72 : W 72 := advance w64 (by decide +kernel)
private def w80 : W 80 := advance w72 (by decide +kernel)
private def w88 : W 88 := advance w80 (by decide +kernel)
private def w96 : W 96 := advance w88 (by decide +kernel)
private def w104 : W 104 := advance w96 (by decide +kernel)
private def w112 : W 112 := advance w104 (by decide +kernel)
private def w118 : W 118 := advance w112 (by decide +kernel)
lemma valid : Covers p 0 118 := w118.valid
end Slice0

namespace Slice1
private abbrev p := sliceTest 15 z certificate 1
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w72 : W 72 := advance w64 (by decide +kernel)
private def w80 : W 80 := advance w72 (by decide +kernel)
private def w88 : W 88 := advance w80 (by decide +kernel)
private def w96 : W 96 := advance w88 (by decide +kernel)
private def w104 : W 104 := advance w96 (by decide +kernel)
private def w112 : W 112 := advance w104 (by decide +kernel)
private def w118 : W 118 := advance w112 (by decide +kernel)
lemma valid : Covers p 0 118 := w118.valid
end Slice1

namespace Slice2
private abbrev p := sliceTest 15 z certificate 2
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w72 : W 72 := advance w64 (by decide +kernel)
private def w80 : W 80 := advance w72 (by decide +kernel)
private def w88 : W 88 := advance w80 (by decide +kernel)
private def w96 : W 96 := advance w88 (by decide +kernel)
private def w104 : W 104 := advance w96 (by decide +kernel)
private def w112 : W 112 := advance w104 (by decide +kernel)
private def w118 : W 118 := advance w112 (by decide +kernel)
lemma valid : Covers p 0 118 := w118.valid
end Slice2

namespace Slice3
private abbrev p := sliceTest 15 z certificate 3
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w72 : W 72 := advance w64 (by decide +kernel)
private def w80 : W 80 := advance w72 (by decide +kernel)
private def w88 : W 88 := advance w80 (by decide +kernel)
private def w96 : W 96 := advance w88 (by decide +kernel)
private def w104 : W 104 := advance w96 (by decide +kernel)
private def w112 : W 112 := advance w104 (by decide +kernel)
private def w118 : W 118 := advance w112 (by decide +kernel)
lemma valid : Covers p 0 118 := w118.valid
end Slice3

namespace Slice4
private abbrev p := sliceTest 15 z certificate 4
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w72 : W 72 := advance w64 (by decide +kernel)
private def w80 : W 80 := advance w72 (by decide +kernel)
private def w88 : W 88 := advance w80 (by decide +kernel)
private def w96 : W 96 := advance w88 (by decide +kernel)
private def w104 : W 104 := advance w96 (by decide +kernel)
private def w112 : W 112 := advance w104 (by decide +kernel)
private def w118 : W 118 := advance w112 (by decide +kernel)
lemma valid : Covers p 0 118 := w118.valid
end Slice4

namespace Slice5
private abbrev p := sliceTest 15 z certificate 5
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w72 : W 72 := advance w64 (by decide +kernel)
private def w80 : W 80 := advance w72 (by decide +kernel)
private def w88 : W 88 := advance w80 (by decide +kernel)
private def w96 : W 96 := advance w88 (by decide +kernel)
private def w104 : W 104 := advance w96 (by decide +kernel)
private def w112 : W 112 := advance w104 (by decide +kernel)
private def w118 : W 118 := advance w112 (by decide +kernel)
lemma valid : Covers p 0 118 := w118.valid
end Slice5

namespace Slice6
private abbrev p := sliceTest 15 z certificate 6
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w72 : W 72 := advance w64 (by decide +kernel)
private def w80 : W 80 := advance w72 (by decide +kernel)
private def w88 : W 88 := advance w80 (by decide +kernel)
private def w96 : W 96 := advance w88 (by decide +kernel)
private def w104 : W 104 := advance w96 (by decide +kernel)
private def w112 : W 112 := advance w104 (by decide +kernel)
private def w118 : W 118 := advance w112 (by decide +kernel)
lemma valid : Covers p 0 118 := w118.valid
end Slice6

namespace Slice7
private abbrev p := sliceTest 15 z certificate 7
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w72 : W 72 := advance w64 (by decide +kernel)
private def w80 : W 80 := advance w72 (by decide +kernel)
private def w88 : W 88 := advance w80 (by decide +kernel)
private def w96 : W 96 := advance w88 (by decide +kernel)
private def w104 : W 104 := advance w96 (by decide +kernel)
private def w112 : W 112 := advance w104 (by decide +kernel)
private def w118 : W 118 := advance w112 (by decide +kernel)
lemma valid : Covers p 0 118 := w118.valid
end Slice7

namespace Slice8
private abbrev p := sliceTest 15 z certificate 8
private abbrev W := Window p
private def w0 : W 0 := windowStart p
private def w8 : W 8 := advance w0 (by decide +kernel)
private def w16 : W 16 := advance w8 (by decide +kernel)
private def w24 : W 24 := advance w16 (by decide +kernel)
private def w32 : W 32 := advance w24 (by decide +kernel)
private def w40 : W 40 := advance w32 (by decide +kernel)
private def w48 : W 48 := advance w40 (by decide +kernel)
private def w56 : W 56 := advance w48 (by decide +kernel)
private def w64 : W 64 := advance w56 (by decide +kernel)
private def w72 : W 72 := advance w64 (by decide +kernel)
private def w80 : W 80 := advance w72 (by decide +kernel)
private def w88 : W 88 := advance w80 (by decide +kernel)
private def w96 : W 96 := advance w88 (by decide +kernel)
private def w104 : W 104 := advance w96 (by decide +kernel)
private def w112 : W 112 := advance w104 (by decide +kernel)
private def w118 : W 118 := advance w112 (by decide +kernel)
lemma valid : Covers p 0 118 := w118.valid
end Slice8

lemma spans : Mixed 15 45 := by
  apply certify_slices z certificate
  intro s
  fin_cases s
  · exact Slice0.valid
  · exact Slice1.valid
  · exact Slice2.valid
  · exact Slice3.valid
  · exact Slice4.valid
  · exact Slice5.valid
  · exact Slice6.valid
  · exact Slice7.valid
  · exact Slice8.valid

end D15

end TensorRankThreeFactor.Cross

namespace TensorRankThreeFactor.Cyclic

inductive Shape | nine | twelve | fifteen
  deriving DecidableEq

def Shape.d₀ : Shape → ℕ
  | .nine => 9 | .twelve => 12 | .fifteen => 15

def Shape.trade : Shape → ℕ
  | .nine => 5 | .twelve => 2 | .fifteen => 0

def Shape.edge (q : Shape) := 27 + 3 * (q.d₀ - 9) - q.trade

def dimension (m : ℕ) (q : Shape) := q.d₀ + 1 + 9 * m

lemma exists_dimension {n : ℕ} (hn : 10 ≤ n) (hr : n % 3 = 1) :
    ∃ m q, n = dimension m q := by
  let m := (n - 10) / 9
  have : n = 10 + 9 * m ∨ n = 13 + 9 * m ∨ n = 16 + 9 * m := by dsimp [m]; omega
  rcases this with h | h | h
  · exact ⟨m, .nine, h⟩
  · exact ⟨m, .twelve, h⟩
  · exact ⟨m, .fifteen, h⟩

abbrev Group (m : ℕ) := Fin (m + 1)
abbrev Regular (m : ℕ) := {g : Group m // g ≠ 0}

lemma card_regular (m : ℕ) : Fintype.card (Regular m) = m := by
  rw [show Fintype.card (Regular m) = _ from Fintype.card_subtype_compl (fun g : Group m => g = 0)]
  simp [Group]

variable {m : ℕ} {q : Shape}

def fiberSize (base regular : ℕ) (g : Group m) := if g = 0 then base else regular

@[simp] lemma fiberSize_zero (b r : ℕ) : fiberSize b r (0 : Group m) = b := by simp [fiberSize]
@[simp] lemma fiberSize_regular (b r : ℕ) (g : Regular m) : fiberSize b r g.val = r := by
  simp [fiberSize, g.property]

abbrev Extra (m : ℕ) (q : Shape) := Σ g : Group m, Fin (fiberSize q.d₀ 8 g)
abbrev InnerA (m : ℕ) (q : Shape) := Σ g : Group m, Fin (fiberSize q.d₀ 9 g)
abbrev InnerC (m : ℕ) (q : Shape) := Σ g : Group m, Fin (fiberSize (q.d₀ - 1) 9 g)

private lemma card_fibers (m b r : ℕ) :
    Fintype.card (Σ g : Group m, Fin (fiberSize b r g)) = b + m * r := by
  simp only [Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_succ]
  simp [fiberSize]

lemma card_extra (m : ℕ) (q : Shape) : Fintype.card (Extra m q) = q.d₀ + 8 * m := by
  rw [Nat.mul_comm 8 m]; exact card_fibers _ _ _

lemma card_innerA (m : ℕ) (q : Shape) : Fintype.card (InnerA m q) = dimension m q - 1 := by
  rw [card_fibers, Nat.mul_comm m 9]; unfold dimension; omega

lemma card_innerC (m : ℕ) (q : Shape) : Fintype.card (InnerC m q) = dimension m q - 2 := by
  rw [card_fibers, Nat.mul_comm m 9]; cases q <;> simp [dimension, Shape.d₀] <;> omega

lemma card_extra_budget (m : ℕ) (q : Shape) :
    Fintype.card (Extra m q) = dimension m q - (dimension m q - 1) / 9 := by
  rw [card_extra]; cases q <;> simp [dimension, Shape.d₀] <;> omega

inductive Slot (m : ℕ) (q : Shape) where
  | base (t : Fin (q.d₀ * q.d₀ / 3))
  | trade (i : Regular m) (t : Fin (2 * q.trade))
  | left (j : Regular m) (t : Fin q.edge)
  | right (i : Regular m) (t : Fin q.edge)
  | normal (i j : Regular m) (t : Fin 27)
  deriving DecidableEq

private abbrev SlotSum (m : ℕ) (q : Shape) :=
  Fin (q.d₀ * q.d₀ / 3) ⊕ (Regular m × Fin (2 * q.trade)) ⊕ (Regular m × Fin q.edge) ⊕
    (Regular m × Fin q.edge) ⊕ (Regular m × Regular m × Fin 27)

private def slotSumEquiv : Slot m q ≃ SlotSum m q where
  toFun
    | .base t => .inl t
    | .trade i t => .inr (.inl (i, t))
    | .left i t => .inr (.inr (.inl (i, t)))
    | .right i t => .inr (.inr (.inr (.inl (i, t))))
    | .normal i j t => .inr (.inr (.inr (.inr (i, j, t))))
  invFun
    | .inl t => .base t
    | .inr (.inl (i, t)) => .trade i t
    | .inr (.inr (.inl (i, t))) => .left i t
    | .inr (.inr (.inr (.inl (i, t)))) => .right i t
    | .inr (.inr (.inr (.inr (i, j, t)))) => .normal i j t
  left_inv := by rintro (_ | ⟨i,t⟩ | ⟨i,t⟩ | ⟨i,t⟩ | ⟨i,j,t⟩) <;> rfl
  right_inv := by rintro (_ | ⟨i,t⟩ | ⟨i,t⟩ | ⟨i,t⟩ | ⟨i,j,t⟩) <;> rfl

instance : Fintype (Slot m q) := Fintype.ofEquiv (SlotSum m q) slotSumEquiv.symm

lemma card_slot (m : ℕ) (q : Shape) :
    Fintype.card (Slot m q) = (dimension m q - 1) * (dimension m q - 1) / 3 := by
  rw [Fintype.card_congr slotSumEquiv]
  simp only [SlotSum, Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, card_regular]
  have h : q.d₀ + 1 + 9 * m - 1 = q.d₀ + 9 * m := by omega
  unfold dimension
  rw [h]
  have hx : 3 * (q.d₀ * q.d₀ / 3 + (m * (2 * q.trade) +
      (m * q.edge + (m * q.edge + m * (m * 27)))) ) =
      (q.d₀ + 9 * m) * (q.d₀ + 9 * m) := by
    cases q <;> norm_num [Shape.d₀, Shape.trade, Shape.edge] <;> ring
  omega

def axisA : Slot m q → Group m
  | .base _ | .left _ _ => 0
  | .trade i _ | .right i _ | .normal i _ _ => i

def axisB : Slot m q → Group m
  | .base _ | .right _ _ => 0
  | .trade j _ | .left j _ | .normal _ j _ => j

def axisC : Slot m q → Group m
  | .base _ => 0
  | .trade i _ | .left i _ | .right i _ => i
  | .normal i j _ => i.val + j.val

inductive Face | ab | ac | bc
  deriving DecidableEq

def labels (f : Face) (s : Slot m q) : Group m × Group m :=
  match f with
  | .ab => (axisA s, axisB s)
  | .ac => (axisA s, axisC s)
  | .bc => (axisB s, axisC s)

abbrev Fiber (m : ℕ) (q : Shape) (f : Face) (i j : Group m) :=
  {s : Slot m q // labels f s = (i, j)}

/-- The unique normal slot on the ordered face from i to j. -/
def diff (j i : Regular m) (hne : i ≠ j) : Regular m :=
  ⟨j.val - i.val, sub_ne_zero.mpr (fun h => hne (Subtype.ext h.symm))⟩

def regReg (f : Face) (i j : Regular m) (hne : i ≠ j) (t : Fin 27) : Slot m q :=
  match f with
  | .ab => .normal i j t
  | .ac => .normal i (diff j i hne) t
  | .bc => .normal (diff j i hne) i t

def opposite (i : Regular m) : Regular m := ⟨-i.val, neg_ne_zero.mpr i.property⟩

def baseReg (f : Face) (i : Regular m) (t : Fin q.edge) : Slot m q :=
  match f with
  | .ab | .ac => .left i t
  | .bc => .right i t

def regBaseSize (q : Shape) : Face → ℕ
  | .ab => q.edge
  | .ac | .bc => 27

def regBase (i : Regular m) : (f : Face) → Fin (regBaseSize q f) → Slot m q
  | .ab, t => .right i t
  | .ac, t => .normal i (opposite i) t
  | .bc, t => .normal (opposite i) i t

def regDiagSize (q : Shape) : Face → ℕ
  | .ab => 27
  | .ac | .bc => q.edge

def regDiag (i : Regular m) (f : Face) :
    Fin (2 * q.trade) ⊕ Fin (regDiagSize q f) → Slot m q
  | .inl t => .trade i t
  | .inr t => match f with
    | .ab => .normal i i t
    | .ac => .right i t
    | .bc => .left i t

end TensorRankThreeFactor.Cyclic

namespace TensorRankThreeFactor.Cyclic

variable {m : ℕ} {q : Shape}

private def keys (f : Face) (x y : Group m) : Group m × Group m :=
  match f with
  | .ab => (x,y)
  | .ac => (x,y-x)
  | .bc => (y-x,x)

private lemma normal_labels_iff (f : Face) (a b : Regular m) (t : Fin 27) (x y : Group m) :
    labels f (.normal (q := q) a b t) = (x,y) ↔ (a.val,b.val) = keys f x y := by
  cases f with
  | ab => rfl
  | ac =>
    change ((a.val, a.val + b.val) = (x,y)) ↔ (a.val,b.val) = (x,y-x)
    constructor
    · rintro ⟨⟩
      simp
    · intro h
      obtain ⟨h₁,h₂⟩ := Prod.mk.inj h
      rw [h₁,h₂,add_sub_cancel]
  | bc =>
    change ((b.val, a.val + b.val) = (x,y)) ↔ (a.val,b.val) = (y-x,x)
    constructor
    · rintro ⟨⟩
      simp
    · intro h
      obtain ⟨h₁,h₂⟩ := Prod.mk.inj h
      rw [h₁,h₂,sub_add_cancel]

private noncomputable def fiberEquiv {T : Type} {f : Face} {i j : Group m}
    (stream : T → Slot m q) (hinj : Function.Injective stream)
    (htags : ∀ t, labels f (stream t) = (i,j))
    (hfull : ∀ s : Slot m q, labels f s = (i,j) → ∃ t, s = stream t) : T ≃ Fiber m q f i j :=
  Equiv.ofBijective (fun t => ⟨stream t, htags t⟩) ⟨
    fun _ _ h => hinj (congrArg Subtype.val h),
    fun s => by obtain ⟨t, ht⟩ := hfull s.val s.property; exact ⟨t, Subtype.ext ht.symm⟩⟩

lemma regReg_labels (f : Face) (i j : Regular m) (hne : i ≠ j) (t : Fin 27) :
    labels f (regReg (q := q) f i j hne t) = (i.val,j.val) := by
  cases f <;> simp [regReg, labels, axisA, axisB, axisC, diff]

lemma regReg_injective (f : Face) (i j : Regular m) (hne : i ≠ j) :
    Function.Injective (regReg (q := q) f i j hne) := by
  intro s t h
  cases f <;> simpa [regReg] using h

lemma regReg_full (f : Face) (i j : Regular m) (hne : i ≠ j) (s : Slot m q)
    (hs : labels f s = (i.val,j.val)) : ∃ t, s = regReg f i j hne t := by
  have h₀ : (0 : Group m) ≠ i.val := i.property.symm
  have h₁ : (0 : Group m) ≠ j.val := j.property.symm
  have h₂ : i.val ≠ j.val := fun h => hne (Subtype.ext h)
  cases s with
  | base t | trade k t | left k t | right k t =>
    cases f <;> simp [labels, axisA, axisB, axisC, h₀, h₁] at hs <;>
      exact (h₂ (hs.1.symm.trans hs.2)).elim
  | normal a b t =>
    have hh := (normal_labels_iff f a b t i.val j.val).mp hs
    refine ⟨t, ?_⟩
    cases f <;> obtain ⟨h₁,h₂⟩ := Prod.mk.inj hh <;>
      exact congrArg₂ (fun x y => Slot.normal x y t) (Subtype.ext h₁) (Subtype.ext h₂)

noncomputable def regRegEquiv (f : Face) (i j : Regular m) (hne : i ≠ j) :
    Fin 27 ≃ Fiber m q f i.val j.val :=
  fiberEquiv _ (regReg_injective f i j hne) (regReg_labels f i j hne) (regReg_full f i j hne)

@[simp] lemma regRegEquiv_val (f : Face) (i j : Regular m) (hne : i ≠ j) (t : Fin 27) :
    (regRegEquiv (q := q) f i j hne t).val = regReg f i j hne t := rfl

lemma baseBase_labels (f : Face) (t : Fin (q.d₀ * q.d₀ / 3)) :
    labels f (.base (m := m) t) = (0,0) := by cases f <;> rfl

lemma baseBase_full (f : Face) (s : Slot m q) (hs : labels f s = (0,0)) :
    ∃ t, s = .base t := by
  cases s with
  | base t => exact ⟨t,rfl⟩
  | trade k t | left k t | right k t =>
    cases f <;> simp [labels, axisA, axisB, axisC, k.property] at hs
  | normal a b t =>
    cases f <;> simp [labels, axisA, axisB, axisC, a.property, b.property] at hs

noncomputable def baseBaseEquiv (f : Face) :
    Fin (q.d₀ * q.d₀ / 3) ≃ Fiber m q f 0 0 :=
  fiberEquiv _ (fun _ _ h => Slot.base.inj h) (baseBase_labels f) (baseBase_full f)

@[simp] lemma baseBaseEquiv_val (f : Face) (t : Fin (q.d₀ * q.d₀ / 3)) :
    (baseBaseEquiv (m := m) (q := q) f t).val = .base t := rfl

lemma baseReg_labels (f : Face) (i : Regular m) (t : Fin q.edge) :
    labels f (baseReg f i t) = (0,i.val) := by cases f <;> rfl

lemma baseReg_full (f : Face) (i : Regular m) (s : Slot m q) (hs : labels f s = (0,i.val)) :
    ∃ t, s = baseReg f i t := by
  have h₀ := i.property.symm
  cases s with
  | base t =>
    cases f <;> simp [labels, axisA, axisB, axisC, h₀] at hs
  | trade k t =>
    cases f <;> simp [labels, axisA, axisB, axisC, k.property] at hs
  | left k t | right k t =>
    cases f <;> simp [labels, axisA, axisB, axisC, k.property, h₀] at hs <;>
      exact ⟨t, by cases Subtype.ext hs; rfl⟩
  | normal a b t =>
    cases f <;> simp [labels, axisA, axisB, axisC, a.property, b.property] at hs

noncomputable def baseRegEquiv (f : Face) (i : Regular m) :
    Fin q.edge ≃ Fiber m q f 0 i.val :=
  fiberEquiv _ (by intro s t h; cases f <;> simpa [baseReg] using h)
    (baseReg_labels f i) (baseReg_full f i)

@[simp] lemma baseRegEquiv_val (f : Face) (i : Regular m) (t : Fin q.edge) :
    (baseRegEquiv f i t).val = baseReg f i t := rfl

lemma regBase_labels (i : Regular m) (f : Face) (t : Fin (regBaseSize q f)) :
    labels f (regBase i f t) = (i.val,0) := by
  cases f <;> simp [regBase, labels, axisA, axisB, axisC, opposite]

lemma regBase_full (i : Regular m) (f : Face) (s : Slot m q) (hs : labels f s = (i.val,0)) :
    ∃ t, s = regBase i f t := by
  have h₀ := i.property.symm
  cases s with
  | base t =>
    cases f <;> simp [labels, axisA, axisB, axisC, h₀] at hs
  | trade k t | left k t | right k t =>
    cases f <;> simp [labels, axisA, axisB, axisC, k.property, h₀] at hs <;>
      exact ⟨t, by cases Subtype.ext hs; rfl⟩
  | normal a b t =>
    have hh := (normal_labels_iff f a b t i.val 0).mp hs
    cases f with
    | ab => exact (b.property (Prod.mk.inj hh).2).elim
    | ac | bc =>
      simp [keys] at hh
      exact ⟨t, congrArg₂ (fun x y => Slot.normal x y t) (Subtype.ext hh.1) (Subtype.ext hh.2)⟩

noncomputable def regBaseEquiv (i : Regular m) (f : Face) :
    Fin (regBaseSize q f) ≃ Fiber m q f i.val 0 :=
  fiberEquiv _ (by
    intro s t h
    cases f with
    | ab => exact (Slot.right.inj h).2
    | ac | bc => exact (Slot.normal.inj h).2.2)
    (regBase_labels i f) (regBase_full i f)

@[simp] lemma regBaseEquiv_val (i : Regular m) (f : Face) (t : Fin (regBaseSize q f)) :
    (regBaseEquiv i f t).val = regBase i f t := rfl

lemma regDiag_labels (i : Regular m) (f : Face) (t : Fin (2 * q.trade) ⊕ Fin (regDiagSize q f)) :
    labels f (regDiag i f t) = (i.val,i.val) := by cases f <;> cases t <;> rfl

lemma regDiag_full (i : Regular m) (f : Face) (s : Slot m q) (hs : labels f s = (i.val,i.val)) :
    ∃ t, s = regDiag i f t := by
  have h₀ := i.property.symm
  cases s with
  | base t =>
    cases f <;> simp [labels, axisA, axisB, axisC, h₀] at hs
  | trade k t =>
    cases f <;> simp [labels, axisA, axisB, axisC] at hs <;>
      exact ⟨Sum.inl t, by cases Subtype.ext hs; rfl⟩
  | left k t | right k t =>
    cases f <;> simp [labels, axisA, axisB, axisC, h₀] at hs
    exact ⟨Sum.inr t, by cases Subtype.ext hs; rfl⟩
  | normal a b t =>
    have hh := (normal_labels_iff f a b t i.val i.val).mp hs
    cases f with
    | ab =>
      exact ⟨Sum.inr t, congrArg₂ (fun x y => Slot.normal x y t)
        (Subtype.ext (Prod.mk.inj hh).1) (Subtype.ext (Prod.mk.inj hh).2)⟩
    | ac | bc => simp [keys, a.property, b.property] at hh

noncomputable def regDiagEquiv (i : Regular m) (f : Face) :
    Fin (2 * q.trade) ⊕ Fin (regDiagSize q f) ≃ Fiber m q f i.val i.val :=
  fiberEquiv _ (by
    intro s t h
    cases f <;> cases s <;> cases t <;> simp_all [regDiag] <;> first
      | exact (Slot.normal.inj h).2.2
      | exact (Slot.right.inj h).2
      | exact (Slot.left.inj h).2)
    (regDiag_labels i f) (regDiag_full i f)

@[simp] lemma regDiagEquiv_val (i : Regular m) (f : Face)
    (t : Fin (2 * q.trade) ⊕ Fin (regDiagSize q f)) :
    (regDiagEquiv i f t).val = regDiag i f t := rfl

end TensorRankThreeFactor.Cyclic

namespace TensorRankThreeFactor.Cyclic

variable {m : ℕ} {q : Shape}

lemma regReg_ac_eq_bc_iff (i j : Regular m) (hne : i ≠ j) (t u : Fin 27) :
    regReg (q := q) .ac i j hne t = regReg .bc i j hne u ↔
      i.val + i.val = j.val ∧ t = u := by
  change Slot.normal i (diff j i hne) t = Slot.normal (diff j i hne) i u ↔ _
  rw [Slot.normal.injEq]
  constructor
  · rintro ⟨h, _, he⟩
    exact ⟨eq_sub_iff_add_eq.mp (congrArg Subtype.val h), he⟩
  · rintro ⟨h, rfl⟩
    have e : i = diff j i hne := Subtype.ext (eq_sub_iff_add_eq.mpr h)
    exact ⟨e,e.symm,rfl⟩

lemma regReg_ab_ne (i j : Regular m) (hne : i ≠ j) {f : Face} (hf : f ≠ .ab) (t u : Fin 27) :
    regReg (q := q) .ab i j hne t ≠ regReg f i j hne u := by
  intro h
  have hc := congrArg axisC h
  cases f <;> simp [regReg, axisC, diff, i.property] at hc hf

/-- Slots on oppositely oriented regular faces never coincide. -/
lemma regReg_reverse_ne (f k : Face) (i j : Regular m) (hne : i ≠ j) (t u : Fin 27) :
    regReg (q := q) f i j hne t ≠ regReg k j i hne.symm u := by
  have hv : i.val ≠ j.val := fun h => hne (Subtype.ext h)
  intro h
  have hc := congrArg axisC h
  have ha := congrArg axisA h
  cases f <;> cases k <;>
    simp [regReg, axisA, axisC, diff, hv, hv.symm, i.property, j.property] at hc ha

/-- Only the two C-faces can meet within a regular orientation. -/
lemma regReg_eq_iff (f k : Face) (i j : Regular m) (hne : i ≠ j) (t u : Fin 27) :
    regReg (q := q) f i j hne t = regReg k i j hne u ↔
      t = u ∧ (f = k ∨ (f ≠ .ab ∧ k ≠ .ab ∧ i.val + i.val = j.val)) := by
  have self (l : Face) := (regReg_injective (q := q) l i j hne).eq_iff (a := t) (b := u)
  have ha := regReg_ab_ne (q := q) i j hne (f := .ac) (by decide)
  have hb := regReg_ab_ne (q := q) i j hne (f := .bc) (by decide)
  cases f <;> cases k <;> simp [self, ha, hb, Ne.symm (ha u t), Ne.symm (hb u t),
    regReg_ac_eq_bc_iff, and_comm]
  rw [eq_comm, regReg_ac_eq_bc_iff]
  tauto

lemma baseReg_ab_eq_ac (i : Regular m) (t : Fin q.edge) :
    baseReg .ab i t = baseReg .ac i t := rfl

lemma baseReg_bc_eq_regBase_ab (i : Regular m) (t : Fin q.edge) :
    baseReg .bc i t = regBase i .ab t := rfl

lemma regBase_ac_eq_bc_iff (i : Regular m) (t u : Fin 27) :
    regBase (q := q) i .ac t = regBase i .bc u ↔ i.val + i.val = 0 ∧ t = u := by
  change Slot.normal i (opposite i) t = Slot.normal (opposite i) i u ↔ _
  rw [Slot.normal.injEq]
  constructor
  · rintro ⟨h, _, he⟩
    exact ⟨eq_neg_iff_add_eq_zero.mp (congrArg Subtype.val h), he⟩
  · rintro ⟨h, rfl⟩
    have e : i = opposite i := Subtype.ext (eq_neg_iff_add_eq_zero.mpr h)
    exact ⟨e, e.symm, rfl⟩

@[simp] lemma regDiag_trade (i : Regular m) (f : Face) (t : Fin (2 * q.trade)) :
    regDiag i f (.inl t) = .trade i t := rfl

end TensorRankThreeFactor.Cyclic

namespace TensorRankThreeFactor.Cyclic

variable {m : ℕ} {q : Shape} {A B C : Type}

def Face.Pair : Face → Type → Type → Type → Type
  | .ab, X, Y, _ => X × Y
  | .ac, X, _, Z => X × Z
  | .bc, _, Y, Z => Y × Z

def Face.project (f : Face) (v : A × B × C) : f.Pair A B C :=
  match f with
  | .ab => (v.1,v.2.1)
  | .ac => (v.1,v.2.2)
  | .bc => (v.2.1,v.2.2)

/-- Factors of one oriented regular-pair certificate. Both C-faces use the
same third vector in each slot of the finite template. -/
structure RegularFaceData (A B C : Type) where
  ab : Fin 27 → A × B
  acbc : Fin 27 → A × B × C

def RegularFaceData.values (data : RegularFaceData A B C) (f : Face) (t : Fin 27) :
    f.Pair A B C :=
  match f with
  | .ab => data.ab t
  | .ac => ((data.acbc t).1, (data.acbc t).2.2)
  | .bc => (data.acbc t).2

/-- Assign factors to actual cyclic slots for both orientations of a regular
pair. The two streams ending at j use the same C vector, including when
the group law identifies the underlying points. -/
def regRegFactors (i j : Regular m) (ij ji : RegularFaceData A B C) (other : A × B × C) :
    Slot m q → A × B × C
  | .normal g h t =>
    let a := if g = i then (if h = j then (ij.ab t).1 else (ij.acbc t).1)
      else if g = j then (if h = i then (ji.ab t).1 else (ji.acbc t).1) else other.1
    let b := if h = i then (if g = j then (ji.ab t).2 else (ij.acbc t).2.1)
      else if h = j then (if g = i then (ij.ab t).2 else (ji.acbc t).2.1) else other.2.1
    let c := if g.val + h.val = j.val then (ij.acbc t).2.2
      else if g.val + h.val = i.val then (ji.acbc t).2.2 else other.2.2
    (a,b,c)
  | _ => other

lemma diff_ne_target (i j : Regular m) (hne : i ≠ j) : diff j i hne ≠ j := by
  intro he
  have e : j.val - i.val = j.val := congrArg Subtype.val he
  exact (add_ne_left.mpr i.property) (sub_eq_iff_eq_add.mp e).symm

lemma regRegFactors_forward (f : Face) (i j : Regular m) (hne : i ≠ j)
    (ij ji : RegularFaceData A B C) (other : A × B × C) (t : Fin 27) :
    f.project (regRegFactors i j ij ji other (regReg (q := q) f i j hne t)) = ij.values f t := by
  have hd := diff_ne_target i j hne
  have hsum : i.val + (diff j i hne).val = j.val := add_sub_cancel _ _
  have hsum' : (diff j i hne).val + i.val = j.val := sub_add_cancel _ _
  cases f <;> simp [regReg, regRegFactors, RegularFaceData.values, Face.project,
    hd, hne, hne.symm, hsum, hsum'] <;> rfl

lemma regRegFactors_reverse (f : Face) (i j : Regular m) (hne : i ≠ j)
    (ij ji : RegularFaceData A B C) (other : A × B × C) (t : Fin 27) :
    f.project (regRegFactors i j ij ji other (regReg (q := q) f j i hne.symm t)) =
      ji.values f t := by
  have hd := diff_ne_target j i hne.symm
  have hv : i.val ≠ j.val := fun h => hne (Subtype.ext h)
  have hsum : j.val + (diff i j hne.symm).val = i.val := add_sub_cancel _ _
  have hsum' : (diff i j hne.symm).val + j.val = i.val := sub_add_cancel _ _
  cases f <;> simp [regReg, regRegFactors, RegularFaceData.values, Face.project,
    hd, hne.symm, hv, hsum, hsum'] <;> rfl

/-- The base-regular template has two edge triples and one inverse-pair
triple. If i and -i differ, copying the inverse-pair triple realizes each
of its two face projections on its own actual slot. -/
structure BaseRegData (q : Shape) (A B C : Type) where
  left : Fin q.edge → A × B × C
  right : Fin q.edge → A × B × C
  inversePair : Fin 27 → A × B × C

def baseRegFactors (i : Regular m) (data : BaseRegData q A B C) (other : A × B × C) :
    Slot m q → A × B × C
  | .left g t => if g = i then data.left t else other
  | .right g t => if g = i then data.right t else other
  | .normal g h t => if (g = i ∧ h = opposite i) ∨ (g = opposite i ∧ h = i)
    then data.inversePair t else other
  | _ => other

def BaseRegData.forward (data : BaseRegData q A B C) (f : Face) (t : Fin q.edge) : A × B × C :=
  match f with
  | .ab | .ac => data.left t
  | .bc => data.right t

def BaseRegData.reverse (data : BaseRegData q A B C) : (f : Face) → Fin (regBaseSize q f) → A × B × C
  | .ab, t => data.right t
  | .ac, t | .bc, t => data.inversePair t

lemma baseRegFactors_forward (f : Face) (i : Regular m) (data : BaseRegData q A B C)
    (other : A × B × C) (t : Fin q.edge) :
    baseRegFactors i data other (baseReg f i t) = data.forward f t := by
  cases f <;> simp [baseReg, baseRegFactors, BaseRegData.forward]

lemma baseRegFactors_reverse (f : Face) (i : Regular m) (data : BaseRegData q A B C)
    (other : A × B × C) (t : Fin (regBaseSize q f)) :
    baseRegFactors i data other (regBase i f t) = data.reverse f t := by
  cases f <;> simp [regBase, baseRegFactors, BaseRegData.reverse]

structure RegDiagData (q : Shape) (A B C : Type) where
  trade : Fin (2 * q.trade) → A × B × C
  left : Fin q.edge → A × B × C
  right : Fin q.edge → A × B × C
  normal : Fin 27 → A × B × C

def regDiagFactors (i : Regular m) (data : RegDiagData q A B C) (other : A × B × C) :
    Slot m q → A × B × C
  | .trade g t => if g = i then data.trade t else other
  | .left g t => if g = i then data.left t else other
  | .right g t => if g = i then data.right t else other
  | .normal g h t => if g = i ∧ h = i then data.normal t else other
  | .base _ => other

def RegDiagData.values (data : RegDiagData q A B C) (f : Face) :
    Fin (2 * q.trade) ⊕ Fin (regDiagSize q f) → A × B × C
  | .inl t => data.trade t
  | .inr t => match f with
    | .ab => data.normal t
    | .ac => data.right t
    | .bc => data.left t

lemma regDiagFactors_values (f : Face) (i : Regular m) (data : RegDiagData q A B C)
    (other : A × B × C) (t : Fin (2 * q.trade) ⊕ Fin (regDiagSize q f)) :
    regDiagFactors i data other (regDiag i f t) = data.values f t := by
  cases f <;> cases t <;> simp [regDiag, regDiagFactors, RegDiagData.values]

def baseFactors (data : Fin (q.d₀ * q.d₀ / 3) → A × B × C) (other : A × B × C) :
    Slot m q → A × B × C
  | .base t => data t
  | _ => other

@[simp] lemma baseFactors_base (data : Fin (q.d₀ * q.d₀ / 3) → A × B × C)
    (other : A × B × C) (t : Fin (q.d₀ * q.d₀ / 3)) :
    baseFactors (m := m) data other (.base t) = data t := rfl

end TensorRankThreeFactor.Cyclic

namespace TensorRankThreeFactor.Global

open MvPolynomial

abbrev V (G : Type) (D E X : G → Type) (N : Type) :=
  (Sigma X × (Side (Sigma D) ⊕ (Side (Sigma D) ⊕ Depth (Sigma E)))) ⊕
    (N × (Sigma D ⊕ (Sigma D ⊕ Sigma E)))

def extra {G O K : Type} [Zero K] [DecidableEq G] {D : G → Type}
    (g : G) (a : O ⊕ Sigma D → K) : O ⊕ Sigma D → K :=
  Sum.elim (fun o => a (Sum.inl o)) (fun d => if d.1=g then a (Sum.inr d) else 0)
def inner {G K : Type} [Zero K] [DecidableEq G] {D : G → Type}
    (g : G) (a : Sigma D → K) (d : Sigma D) : K := if d.1=g then a d else 0

section Factors
variable {G N K : Type} {D E X : G → Type} [Zero K] [DecidableEq G]
    (v : V G D E X N → K)
def xa (t : Sigma X) := extra t.1 (fun i => v (Sum.inl (t,Sum.inl i)))
def xb (t : Sigma X) := extra t.1 (fun j => v (Sum.inl (t,Sum.inr (Sum.inl j))))
def xc (t : Sigma X) := extra t.1 (fun k => v (Sum.inl (t,Sum.inr (Sum.inr k))))
def na (a : N → G) (t : N) := inner (a t) (fun i => v (Sum.inr (t,Sum.inl i)))
def nb (b : N → G) (t : N) := inner (b t) (fun j => v (Sum.inr (t,Sum.inr (Sum.inl j))))
def nc (c : N → G) (t : N) := inner (c t) (fun k => v (Sum.inr (t,Sum.inr (Sum.inr k))))
end Factors

def mat {G N K : Type} {D E X : G → Type} [DecidableEq G] [∀ g, DecidableEq (D g)] [∀ g, DecidableEq (E g)]
    [CommSemiring K] (a b c : N → G) (v : V G D E X N → K) :
    Matrix (BaseRows (Sigma D) (Sigma E)) (BaseCols (Sigma D) (Sigma E) (Sigma X) N) K :=
  baseMatrix (xa v) (xb v) (xc v) (na v a) (nb v b) (nc v c)

def labels {G O : Type} {D : G → Type} : O ⊕ Sigma D → Finset G :=
  Sum.elim (fun _ => ∅) (fun i => {i.1})

def raw {G : Type} {D E : G → Type} [DecidableEq G] (r : BaseRows (Sigma D) (Sigma E)) : Finset G :=
  let (i,j,k) := xyz r
  labels i ∪ labels j ∪ labels k

def rowSector {G : Type} [Zero G] [DecidableEq G] {D E : G → Type} (r : BaseRows (Sigma D) (Sigma E)) :=
  if raw r = ∅ then ({0} : Finset G) else raw r

def colSector {G N : Type} [DecidableEq G] {D E X : G → Type} (a b c : N → G) :
    BaseCols (Sigma D) (Sigma E) (Sigma X) N → Finset G
  | Sum.inl (t,Sum.inl i) => insert t.1 (labels i)
  | Sum.inl (t,Sum.inr (Sum.inl j)) => insert t.1 (labels j)
  | Sum.inl (t,Sum.inr (Sum.inr k)) => insert t.1 (labels k)
  | Sum.inr (t,Sum.inl _) => {b t,c t}
  | Sum.inr (t,Sum.inr (Sum.inl _)) => {a t,c t}
  | Sum.inr (t,Sum.inr (Sum.inr _)) => {a t,b t}

def level {G : Type} [Zero G] [DecidableEq G] (s : Finset G) : Fin 3 :=
  if 1<s.card then 0 else if s={0} then 2 else 1

lemma labels_card {G O : Type} {D : G → Type} (i : O ⊕ Sigma D) : (labels i).card ≤ 1 := by
  cases i <;> simp [labels]

lemma extra_labels {G O K : Type} [Zero K] [DecidableEq G] {D : G → Type}
    (g : G) (f : O ⊕ Sigma D → K) (i : O ⊕ Sigma D) (hi : extra g f i ≠ 0) : labels i ⊆ {g} := by
  cases i with
  | inl i => simp [labels]
  | inr i =>
    by_cases h : i.1=g
    · simp [labels,h]
    · simp [extra,h] at hi

lemma inner_labels {G O K : Type} [Zero K] [DecidableEq G] {D : G → Type}
    (g : G) (f : Sigma D → K) (i : O ⊕ Sigma D)
    (hi : i.elim (fun _ => 0) (inner g f) ≠ 0) : labels i ⊆ {g} := by
  cases i with
  | inl i => simp at hi
  | inr i =>
    by_cases h : i.1=g
    · simp [labels,h]
    · simp [inner,h] at hi

lemma col_bounds {G N : Type} [DecidableEq G] {D E X : G → Type} (a b c : N → G)
    (j : BaseCols (Sigma D) (Sigma E) (Sigma X) N) :
    (colSector a b c j).Nonempty ∧ (colSector a b c j).card ≤ 2 := by
  have bound (g : G) (s : Finset G) (h : s.card≤1) : (insert g s).Nonempty ∧ (insert g s).card≤2 :=
    ⟨Finset.insert_nonempty _ _,(Finset.card_insert_le _ _).trans (by omega)⟩
  rcases j with ⟨t,h|h|h⟩ | ⟨t,h|h|h⟩
  · exact bound _ _ (labels_card h)
  · exact bound _ _ (labels_card h)
  · exact bound _ _ (labels_card h)
  · exact bound _ _ (by simp)
  · exact bound _ _ (by simp)
  · exact bound _ _ (by simp)

lemma subset_grade {G : Type} [DecidableEq G] [Zero G] {s t : Finset G}
    (hst : s⊆t) (_ht : t.Nonempty) (ht2 : t.card≤2)
    (hne : (if s=∅ then ({0} : Finset G) else s) ≠ t) :
    level t < level (if s=∅ then {0} else s) := by
  by_cases he : s=∅
  · subst s
    simp only [if_true] at hne ⊢
    by_cases hk : 1<t.card <;> simp [level,hk,Ne.symm hne]
  · simp only [if_neg he] at hne ⊢
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hst,hne⟩)
    have hs : 0<s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
    have h1 : s.card=1 := by omega
    have h2 : t.card=2 := by omega
    by_cases hs0 : s={0} <;> simp [level,h1,h2,hs0]

lemma raw_subset {G N : Type} [DecidableEq G] {D E X : G → Type} [∀ g, DecidableEq (D g)]
    [∀ g, DecidableEq (E g)] (a b c : N → G) (v : V G D E X N → ℂ)
    (r : BaseRows (Sigma D) (Sigma E)) (z : BaseCols (Sigma D) (Sigma E) (Sigma X) N)
    (hn : mat a b c v r z ≠ 0) : raw r ⊆ colSector a b c z := by
  classical
  have cond {P : Prop} [Decidable P] {t : ℂ} (h : (if P then t else 0)≠0) : P ∧ t≠0 := by
    by_cases hp : P
    · exact ⟨hp,by simpa [hp] using h⟩
    · simp [hp] at h
  generalize hr : xyz r = ijk
  obtain ⟨i,j,k⟩ := ijk
  simp only [mat,baseMatrix,hr] at hn
  simp only [raw,hr]
  rcases z with ⟨t,h|h|h⟩ | ⟨t,h|h|h⟩
  · obtain ⟨rfl,h⟩ := cond hn
    have hb := extra_labels _ _ _ (mul_ne_zero_iff.mp h).1
    have hc := extra_labels _ _ _ (mul_ne_zero_iff.mp h).2
    simp only [colSector,Finset.union_subset_iff]
    exact ⟨⟨Finset.subset_insert _ _,hb.trans (by simp)⟩,hc.trans (by simp)⟩
  · obtain ⟨rfl,h⟩ := cond hn
    have ha := extra_labels _ _ _ (mul_ne_zero_iff.mp h).1
    have hc := extra_labels _ _ _ (mul_ne_zero_iff.mp h).2
    simp only [colSector,Finset.union_subset_iff]
    exact ⟨⟨ha.trans (by simp),Finset.subset_insert _ _⟩,hc.trans (by simp)⟩
  · obtain ⟨rfl,h⟩ := cond hn
    have ha := extra_labels _ _ _ (mul_ne_zero_iff.mp h).1
    have hb := extra_labels _ _ _ (mul_ne_zero_iff.mp h).2
    simp only [colSector,Finset.union_subset_iff]
    exact ⟨⟨ha.trans (by simp),hb.trans (by simp)⟩,Finset.subset_insert _ _⟩
  · obtain ⟨rfl,h⟩ := cond hn
    have hb := inner_labels _ _ _ (mul_ne_zero_iff.mp h).1
    have hc := inner_labels _ _ _ (mul_ne_zero_iff.mp h).2
    simp only [colSector,labels,Sum.elim_inl,Finset.empty_union,Finset.union_subset_iff]
    exact ⟨hb.trans (by simp),hc.trans (by simp)⟩
  · obtain ⟨rfl,h⟩ := cond hn
    have ha := inner_labels _ _ _ (mul_ne_zero_iff.mp h).1
    have hc := inner_labels _ _ _ (mul_ne_zero_iff.mp h).2
    simp only [colSector,labels,Sum.elim_inl,Finset.union_empty,Finset.union_subset_iff]
    exact ⟨ha.trans (by simp),hc.trans (by simp)⟩
  · obtain ⟨rfl,h⟩ := cond hn
    have ha := inner_labels _ _ _ (mul_ne_zero_iff.mp h).1
    have hb := inner_labels _ _ _ (mul_ne_zero_iff.mp h).2
    simp only [colSector,labels,Sum.elim_inl,Finset.union_empty,Finset.union_subset_iff]
    exact ⟨ha.trans (by simp),hb.trans (by simp)⟩

end TensorRankThreeFactor.Global

namespace TensorRankThreeFactor.Global

open MvPolynomial

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

lemma map_base {D E X N K L : Type} [CommSemiring K] [CommSemiring L] [DecidableEq D] [DecidableEq E]
    (φ : K →+* L) (a b : X → Side D → K) (c : X → Depth E → K)
    (ai bi : N → D → K) (ci : N → E → K) :
    (baseMatrix a b c ai bi ci).map φ =
      baseMatrix (fun t i => φ (a t i)) (fun t i => φ (b t i)) (fun t i => φ (c t i))
        (fun t i => φ (ai t i)) (fun t i => φ (bi t i)) (fun t i => φ (ci t i)) := by
  have ez {T U : Type} (h : U → K) (i : T ⊕ U) :
      φ (i.elim (fun _ => 0) h) = i.elim (fun _ => 0) (fun t => φ (h t)) := by cases i <;> simp
  have eif (P : Prop) [Decidable P] (u : K) (v : L) (hu : φ u=v) :
      φ (if P then u else 0) = (if P then v else 0) := by by_cases h : P <;> simp [h,hu]
  ext row col
  change φ (baseMatrix a b c ai bi ci row col) = _
  rcases col with ⟨t,h|h|h⟩|⟨t,h|h|h⟩ <;> rcases row with ⟨i,j,k⟩|⟨i,j,k⟩|⟨i,j,k⟩ <;>
    dsimp only [baseMatrix,xyz,Sum.elim_inl,Sum.elim_inr]
  all_goals apply eif
  all_goals rw [map_mul]
  all_goals simp only [map_zero,ez]

lemma map_extra {G O K L : Type} [DecidableEq G] [CommSemiring K] [CommSemiring L] {D : G → Type}
    (φ : K →+* L) (g : G) (f : O ⊕ Sigma D → K) :
    (fun i => φ (extra g f i)) = extra g (fun j => φ (f j)) := by
  funext i
  cases i with
  | inl i => rfl
  | inr i => by_cases h : i.1=g <;> simp [extra,h]

lemma map_inner {G K L : Type} [DecidableEq G] [CommSemiring K] [CommSemiring L] {D : G → Type}
    (φ : K →+* L) (g : G) (f : Sigma D → K) :
    (fun i => φ (inner g f i)) = inner g (fun j => φ (f j)) := by
  funext i
  by_cases h : i.1=g <;> simp [inner,h]

section Family
variable {G N : Type} {D E X : G → Type} [DecidableEq G] [∀ g,DecidableEq (D g)] [∀ g,DecidableEq (E g)]
  [Zero G] (a b c : N → G)

abbrev LocalRows (D E : G → Type) (s : Finset G) :=
  {r : BaseRows (Sigma D) (Sigma E) // rowSector r=s}
abbrev LocalCols (D E X : G → Type) (a b c : N → G) (s : Finset G) :=
  {z : BaseCols (Sigma D) (Sigma E) (Sigma X) N // colSector a b c z=s}

def block {K : Type} [CommSemiring K] (s : Finset G) (v : V G D E X N → K) :
    Matrix (LocalRows D E s) (LocalCols D E X a b c s) K :=
  (mat a b c v).submatrix Subtype.val Subtype.val

lemma evaluate (s : Finset G) (v : V G D E X N → ℂ) :
    (block a b c s (MvPolynomial.X : V G D E X N → MvPolynomial (V G D E X N) ℂ)).map (eval v) =
      block a b c s v := by
  have hbase := map_base (eval v) (xa (MvPolynomial.X : V G D E X N → MvPolynomial (V G D E X N) ℂ))
    (xb MvPolynomial.X) (xc MvPolynomial.X) (na MvPolynomial.X a) (nb MvPolynomial.X b) (nc MvPolynomial.X c)
  have hex {O : Type} {H : G → Type} (g : G) (k : O ⊕ Sigma H → V G D E X N) :
      (fun i => eval v (extra g (fun j => MvPolynomial.X (k j)) i)) = extra g (fun j => v (k j)) := by
    rw [map_extra]
    simp only [eval_X]
  have hin {H : G → Type} (g : G) (k : Sigma H → V G D E X N) :
      (fun i => eval v (inner g (fun j => MvPolynomial.X (k j)) i)) = inner g (fun j => v (k j)) := by
    rw [map_inner]
    simp only [eval_X]
  have h : (mat a b c (MvPolynomial.X : V G D E X N → MvPolynomial (V G D E X N) ℂ)).map (eval v) =
      mat a b c v := by
    unfold mat
    rw [hbase]
    congr 1 <;> funext t <;> first | apply hex | apply hin
  ext i j
  exact congrFun (congrFun h i.val) j.val

variable [Fintype G] [Fintype N] [∀ g,Fintype (D g)] [∀ g,Fintype (E g)] [∀ g,Fintype (X g)]

def At (s : Finset G) (v : V G D E X N → ℂ) : Prop := Function.Surjective (block a b c s v).mulVec

lemma common (h : ∀ s : Finset G, ∃ v : V G D E X N → ℂ, At a b c s v) :
    ∃ v : V G D E X N → ℂ, Function.Surjective (mat a b c v).mulVec := by
  classical
  let P := MvPolynomial (V G D E X N) ℂ
  let M (s : Finset G) := block a b c s (MvPolynomial.X : V G D E X N → P)
  have good (s : Finset G) : ∃ v : V G D E X N → ℂ, Function.Surjective ((M s).map (eval v)).mulVec := by
    obtain ⟨v,hv⟩ := h s
    refine ⟨v,?_⟩
    dsimp only [M]
    rw [evaluate]
    exact hv
  choose z hz using good
  choose Q hQ cert using fun s => OMA.R_Arxiv_0805_3777_isGenericRank_cube_R1_H3_R1_H3_R1.surjectivity_polynomial (M s) (z s) (hz s)
  have hprod : (∏ s,Q s) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun s _ => hQ s
  have hpoint : ∃ v : V G D E X N → ℂ, eval v (∏ s,Q s) ≠ 0 := by
    by_contra! hn
    exact hprod (MvPolynomial.funext fun v => by rw [hn v, map_zero])
  obtain ⟨v,hv⟩ := hpoint
  have hn : (∏ s,eval v (Q s)) ≠ 0 := by simpa only [map_prod] using hv
  refine ⟨v,?_⟩
  apply graded_surjective rowSector (colSector a b c) level
  · intro i j hdiff hle
    by_contra hne
    have hb := col_bounds (D:=D) (E:=E) (X:=X) a b c j
    exact (not_lt_of_ge hle) (subset_grade (raw_subset a b c v i j hne) hb.1 hb.2 hdiff)
  · intro s
    have h := cert s v (Finset.prod_ne_zero_iff.mp hn s (Finset.mem_univ s))
    dsimp only [M] at h
    rw [evaluate] at h
    exact h

end Family

end TensorRankThreeFactor.Global

namespace TensorRankThreeFactor.Global

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

section
variable {G N : Type} [Fintype G] [Zero G] [DecidableEq G] [Fintype N] [DecidableEq N]
  {D E X : G → Type} [∀g,Fintype (D g)] [∀g,Fintype (E g)] [∀g,Fintype (X g)]
  [∀g,DecidableEq (D g)] [∀g,DecidableEq (E g)]

lemma at_of_template (a b c : N → G) (s : Finset G) (v : V G D E X N → ℂ) {I J : Type}
    [Fintype J] (L : Matrix I J ℂ) (rmap : I → BaseRows (Sigma D) (Sigma E))
    (cmap : J → BaseCols (Sigma D) (Sigma E) (Sigma X) N)
    (cover : ∀ r, rowSector r=s → ∃i,rmap i=r) (hc : ∀j,colSector a b c (cmap j)=s)
    (hm : ∀i j, mat a b c v (rmap i) (cmap j)=L i j) (hs : Function.Surjective L.mulVec) :
    At a b c s v := by
  classical
  let E' : Matrix (LocalCols D E X a b c s) J ℂ := fun k j => if k.val=cmap j then 1 else 0
  have hcol (r : LocalRows D E s) (j : J) :
      (block a b c s v * E') r j=mat a b c v r.val (cmap j) := by
    let p : LocalCols D E X a b c s := ⟨cmap j,hc j⟩
    rw [Matrix.mul_apply]
    have h (k : LocalCols D E X a b c s) : E' k j = (if k=p then 1 else 0) := by
      simp [E',p,Subtype.ext_iff]
    simp [h,mul_ite,Finset.sum_ite_eq',p,block,Matrix.submatrix_apply]
  intro y
  let yy (i : I) := if h : rowSector (rmap i)=s then y ⟨rmap i,h⟩ else 0
  obtain ⟨z,hz⟩ := hs yy
  refine ⟨E'.mulVec z,?_⟩
  rw [Matrix.mulVec_mulVec]
  funext r
  obtain ⟨i,hi⟩ := cover r.val r.property
  have he : yy i = y r := by simp [yy,hi,r.property]
  calc
    _ = ∑ j, mat a b c v r.val (cmap j)*z j := by
      change (∑ j, (block a b c s v*E') r j*z j)=_
      simp only [hcol]
    _ = L.mulVec z i := by rw [← hi]; simp only [hm,Matrix.mulVec,dotProduct]
    _ = y r := (congrFun hz i).trans he

end
end TensorRankThreeFactor.Global

namespace TensorRankThreeFactor.Construction

open Cyclic Global
abbrev DF (m : ℕ) (q : Shape) (g : Group m) := Fin (fiberSize q.d₀ 9 g)
abbrev EF (m : ℕ) (q : Shape) (g : Group m) := Fin (fiberSize (q.d₀-1) 9 g)
abbrev XF (m : ℕ) (q : Shape) (g : Group m) := Fin (fiberSize q.d₀ 8 g)
abbrev Param (m : ℕ) (q : Shape) := Global.V (Group m) (DF m q) (EF m q) (XF m q) (Slot m q)
abbrev R (m : ℕ) (q : Shape) := BaseRows (InnerA m q) (InnerC m q)
abbrev C (m : ℕ) (q : Shape) := BaseCols (InnerA m q) (InnerC m q) (Extra m q) (Slot m q)
def SolvedAt (m : ℕ) (q : Shape) (s : Finset (Group m)) : Prop :=
  ∃ v : Param m q → ℂ, Global.At axisA axisB axisC s v

end TensorRankThreeFactor.Construction

namespace TensorRankThreeFactor.Construction

open Cyclic Global

private lemma row_sizes {m : ℕ} {q : Shape} (r : R m q) :
    (rowSector r).Nonempty ∧ (rowSector r).card≤2 := by
  have hraw : (raw r).card≤2 := by
    have pair {A B : Type} {U W : Group m → Type} (i : A ⊕ Sigma U) (j : B ⊕ Sigma W) :
        (Global.labels i ∪ Global.labels j).card ≤ 2 :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add (labels_card i) (labels_card j))
    rcases r with ⟨i,j,k⟩|⟨i,j,k⟩|⟨i,j,k⟩
    · simpa only [raw,xyz,Global.labels,Sum.elim_inl,Finset.empty_union] using pair j k
    · simpa only [raw,xyz,Global.labels,Sum.elim_inl,Finset.union_empty] using pair (Sum.inr i : Side (InnerA m q)) k
    · simpa only [raw,xyz,Global.labels,Sum.elim_inl,Finset.union_empty] using
        pair (Sum.inr i : Side (InnerA m q)) (Sum.inr j : Side (InnerA m q))
  by_cases hr : raw r=∅
  · simp [rowSector,hr]
  · exact ⟨by simpa only [rowSector,if_neg hr] using Finset.nonempty_iff_ne_empty.mpr hr,
      by simpa only [rowSector,if_neg hr] using hraw⟩

/-- Each nonempty row sector is a singleton or an unordered pair of
different groups. The common all-outer rows lie in the base singleton. -/
lemma all_sectors (m : ℕ) (q : Shape)
    (base : SolvedAt m q {0}) (diag : ∀ g : Regular m, SolvedAt m q {g.val})
    (mixed : ∀ g : Regular m, SolvedAt m q {0,g.val})
    (regular : ∀ g h : Regular m, g≠h → SolvedAt m q {g.val,h.val}) :
    ∀ s : Finset (Group m), SolvedAt m q s := by
  classical
  intro s
  by_cases existsRow : ∃ r : R m q, rowSector r=s
  · obtain ⟨r,hr⟩ := existsRow
    have hb := row_sizes r
    rw [hr] at hb
    have hp : 0<s.card := Finset.card_pos.mpr hb.1
    by_cases hone : s.card=1
    · obtain ⟨g,rfl⟩ := Finset.card_eq_one.mp hone
      by_cases hg : g=0
      · subst g
        exact base
      · exact diag ⟨g,hg⟩
    · obtain ⟨g,h,hd,rfl⟩ := Finset.card_eq_two.mp (show s.card=2 by omega)
      by_cases hg : g=0
      · subst g
        exact mixed ⟨h,Ne.symm hd⟩
      by_cases hh : h=0
      · subst h
        simpa only [Finset.pair_comm g 0] using mixed ⟨g,hd⟩
      · exact regular ⟨g,hg⟩ ⟨h,hh⟩ (fun eq => hd (congrArg Subtype.val eq))
  · refine ⟨fun _ => 0,?_⟩
    intro y
    refine ⟨0,?_⟩
    funext r
    exact (existsRow ⟨r.val,r.property⟩).elim

end TensorRankThreeFactor.Construction

namespace TensorRankThreeFactor.Cross

open Cyclic (RegularFaceData)

structure RegularData (K : Type) where
  left : Fin 8 → Extra K 9 9
  right : Fin 8 → Extra K 9 9
  forward : RegularFaceData (Fin 9 → K) (Fin 9 → K) (Fin 9 → K)
  reverse : RegularFaceData (Fin 9 → K) (Fin 9 → K) (Fin 9 → K)

def regularFactors {K : Type} (v : RegularData K) : Factors K 9 9 8 27 27 where
  left := v.left
  right := v.right
  abL := v.forward.ab
  abR t := ((v.reverse.ab t).2, (v.reverse.ab t).1)
  acL t := ((v.forward.acbc t).1, (v.forward.acbc t).2.2)
  bcL t := (v.forward.acbc t).2
  acR t := ((v.reverse.acbc t).2.2, (v.reverse.acbc t).1)
  bcR t := ((v.reverse.acbc t).2.2, (v.reverse.acbc t).2.1)

def Regular : Prop := ∃ z : RegularData ℂ, Function.Surjective (matrix (regularFactors z)).mulVec

namespace Coordinate

private abbrev Rows := Row 9 9
private abbrev Cols := Col 9 9 8 27 27

private def residue (n : ℕ) [NeZero n] (z : ℕ) : Fin n := ⟨z%n, Nat.mod_lt _ (NeZero.pos _)⟩

private def abFirst (data : Array ℕ) (t : Fin 27) : Fin 9 :=
  residue 9 ((data[t.val]?.getD 0) / 9)
private def lastCoord (data : Array ℕ) (t : Fin 27) : Fin 9 :=
  residue 9 (data[t.val]?.getD 0)
private def triFirst (data : Array ℕ) (t : Fin 27) : Fin 9 :=
  residue 9 ((data[t.val]?.getD 0) / 81)

private def unit {K : Type} [Zero K] [One K] {n : ℕ} (i j : Fin n) : K := if j = i then 1 else 0

private def extra {K : Type} [Zero K] [One K] (o : Fin 2) (t : Fin 8) : Extra K 9 9 :=
  {a := unit t.castSucc, b := unit t.castSucc, c := unit t.castSucc,
   ao := 1, bo := 1, co := unit o}

private def triple {K : Type} [Zero K] [One K] (data : Array ℕ) (t : Fin 27) :
    (Fin 9 → K) × (Fin 9 → K) × (Fin 9 → K) :=
  (unit (triFirst data t), unit (abFirst data t), unit (lastCoord data t))

def data (K : Type) [Zero K] [One K] : RegularData K where
  left := extra 0
  right := extra 1
  forward := {
    ab := fun t => (unit (abFirst RegularCross.ab12 t), unit (lastCoord RegularCross.ab12 t))
    acbc := triple RegularCross.acbc12 }
  reverse := {
    ab := fun t => (unit (lastCoord RegularCross.ab21 t), unit (abFirst RegularCross.ab21 t))
    acbc := triple RegularCross.acbc21 }

private def leftCoord : Dir 9 9 → Fin 9
  | .abL _ h | .abR _ h | .acL h | .acR h | .bcL h | .bcR h => h

private def digit : Dir 9 9 → Fin 8
  | .abL o _ => ⟨o.val, by omega⟩
  | .abR o _ => ⟨2 + o.val, by omega⟩
  | .acL _ => 4 | .acR _ => 5 | .bcL _ => 6 | .bcR _ => 7

private def rowCode (r : Rows) : Fin 648 :=
  ⟨8 * (9 * (leftCoord r.2).val + r.1.val) + (digit r.2).val, by
    have := (leftCoord r.2).isLt; have := r.1.isLt; have := (digit r.2).isLt; omega⟩

private def rowDecode (n : Fin 648) : Rows :=
  let r := residue 9 (n.val / 72)
  let s := residue 9 (n.val / 8)
  let o := residue 2 n.val
  (s, match n.val % 8 with
  | 0 | 1 => .abL o r | 2 | 3 => .abR o r | 4 => .acL r | 5 => .acR r
  | 6 => .bcL r | _ => .bcR r)

private def colIndex : Cols → ℕ
  | .baseA t z => 27*t.val+3*z.val | .baseB t z => 27*t.val+3*z.val+1
  | .baseC t z => 27*t.val+3*z.val+2 | .regA t z => 216+27*t.val+3*z.val
  | .regB t z => 216+27*t.val+3*z.val+1 | .regC t z => 216+27*t.val+3*z.val+2
  | .abL t o => 432+2*t.val+o.val | .abR t o => 486+2*t.val+o.val
  | .acL t => 540+2*t.val | .bcL t => 540+2*t.val+1
  | .acR t => 594+2*t.val | .bcR t => 594+2*t.val+1

private def colCode (c : Cols) : Fin 648 := ⟨colIndex c, by cases c <;> simp only [colIndex] <;> omega⟩

private def colDecode (n : Fin 648) : Cols :=
  let t := residue 8 (n.val / 27)
  let z := residue 9 (n.val / 3)
  let x := residue 27 (n.val / 2)
  let o := residue 2 n.val
  if n.val < 216 then match n.val % 3 with
    | 0 => .baseA t z | 1 => .baseB t z | _ => .baseC t z
  else if n.val < 432 then match n.val % 3 with
    | 0 => .regA t z | 1 => .regB t z | _ => .regC t z
  else if n.val < 486 then .abL x o
  else if n.val < 540 then .abR x o
  else if n.val < 594 then if o = 0 then .acL x else .bcL x
  else if o = 0 then .acR x else .bcR x

set_option maxRecDepth 10000 in
private def rows : Rows ≃ Fin 648 where
  toFun := rowCode
  invFun := rowDecode
  left_inv := by decide +kernel
  right_inv := by decide +kernel

set_option maxRecDepth 10000 in
private def cols : Cols ≃ Fin 648 where
  toFun := colCode
  invFun := colDecode
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private structure Cell where
  left : Fin 9
  right : Fin 9
  byte : Fin 256

private def cell : Cols → Cell
  | .baseA t z => ⟨t.castSucc,z,36⟩
  | .baseB t z => ⟨t.castSucc,z,129⟩
  | .baseC t z => ⟨t.castSucc,z,80⟩
  | .regA t z => ⟨z,t.castSucc,18⟩
  | .regB t z => ⟨z,t.castSucc,72⟩
  | .regC t z => ⟨z,t.castSucc,160⟩
  | .abL t o => ⟨abFirst RegularCross.ab12 t, lastCoord RegularCross.ab12 t,
      if o = 0 then 1 else 2⟩
  | .abR t o => ⟨abFirst RegularCross.ab21 t, lastCoord RegularCross.ab21 t,
      if o = 0 then 4 else 8⟩
  | .acL t => ⟨triFirst RegularCross.acbc12 t, lastCoord RegularCross.acbc12 t,16⟩
  | .bcL t => ⟨abFirst RegularCross.acbc12 t, lastCoord RegularCross.acbc12 t,64⟩
  | .acR t => ⟨lastCoord RegularCross.acbc21 t, triFirst RegularCross.acbc21 t,32⟩
  | .bcR t => ⟨lastCoord RegularCross.acbc21 t, abFirst RegularCross.acbc21 t,128⟩

private def Cell.word (c : Cell) := c.byte.val <<< (8 * (9 * c.left.val + c.right.val))

set_option maxRecDepth 10000 in
private lemma column_words : ∀ j : Cols, (cell j).word = RegularCross.column (colCode j).val := by
  decide +kernel

private def Cell.entry (c : Cell) (s : Fin 9) (r : Dir 9 9) : ℂ :=
  if leftCoord r = c.left ∧ s = c.right ∧ c.byte.val.testBit (digit r).val then 1 else 0

private lemma cell_bit (c : Cell) (s : Fin 9) (r : Dir 9 9) :
    c.entry s r = ((TensorRankCertificates.intBit (c.word.testBit (rowCode (s,r)).val) : ℤ) : ℂ) := by
  by_cases h : leftCoord r = c.left ∧ s = c.right
  · simp [Cell.entry, Cell.word, rowCode, h.1, h.2, TensorRankCertificates.intBit]
  · have hne : 9 * (leftCoord r).val + s.val ≠ 9 * c.left.val + c.right.val := by
      intro hh
      apply h
      constructor <;> apply Fin.ext <;> omega
    by_cases hlo : 9 * (leftCoord r).val + s.val < 9 * c.left.val + c.right.val
    · have hn : ¬ 8 * (9*c.left.val+c.right.val) ≤
          8 * (9*(leftCoord r).val+s.val) + (digit r).val := by
        have := (digit r).isLt
        omega
      simp [Cell.entry, Cell.word, rowCode, ← and_assoc, h, hn, TensorRankCertificates.intBit]
    · have hd : 8 ≤ (8 * (9 * (leftCoord r).val+s.val) + (digit r).val) -
          8 * (9*c.left.val+c.right.val) := by omega
      have hb := Nat.testBit_lt_two_pow (lt_of_lt_of_le c.byte.isLt
        (show 2^8 ≤ 2^_ from Nat.pow_le_pow_right (by decide) hd))
      simp [Cell.entry, Cell.word, rowCode, ← and_assoc, h, hb, TensorRankCertificates.intBit]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private lemma matrix_cell (s : Fin 9) (r : Dir 9 9) (j : Cols) :
    matrix (regularFactors (data ℂ)) (s,r) j = (cell j).entry s r := by
  cases j
  case' abL t o => fin_cases o
  case' abR t o => fin_cases o
  all_goals
    cases r
    case' abL o h => fin_cases o
    case' abR o h => fin_cases o
  all_goals
    simp [matrix, regularFactors, data, extra, triple, unit, Cell.entry, leftCoord, digit, cell, Nat.testBit]
  all_goals split_ifs <;> first | rfl | tauto

private lemma matrix_eq :
    matrix (regularFactors (data ℂ)) = (RegularCross.M.map (Int.castRingHom ℂ)).submatrix rows cols := by
  ext ⟨s,r⟩ j
  change matrix (regularFactors (data ℂ)) (s,r) j =
    ((TensorRankCertificates.intBit
      ((RegularCross.column (colCode j).val).testBit (rowCode (s,r)).val) : ℤ) : ℂ)
  rw [matrix_cell, ← column_words]
  exact cell_bit _ _ _

theorem spans : Function.Surjective (matrix (regularFactors (data ℂ))).mulVec := by
  rw [matrix_eq]
  intro y
  obtain ⟨v,hv⟩ := RegularCross.spans (y ∘ rows.symm)
  refine ⟨v ∘ cols, ?_⟩
  rw [Matrix.submatrix_mulVec_equiv]
  have he : (v ∘ cols) ∘ cols.symm = v := by ext; simp
  rw [he,hv]
  ext
  simp

end Coordinate

theorem regular_spans : Regular := ⟨Coordinate.data ℂ, Coordinate.spans⟩

end TensorRankThreeFactor.Cross

namespace TensorRankThreeFactor.Construction.CrossAdapter

open Cyclic
open TensorRankThreeFactor.Cross

variable {m d e x l w : ℕ} {q : Shape} {g h : Group m}

/-- Encode an ordinary finite index as an index of the indicated group. -/
private def coord {b r n : ℕ} (g : Group m) (eqn : n = fiberSize b r g) (i : Fin n) :
    Σ k : Group m, Fin (fiberSize b r k) := ⟨g,i.cast eqn⟩

@[simp] private lemma coord_fst {b r n : ℕ} (eqn : n = fiberSize b r g) (i : Fin n) :
    (coord g eqn i).1 = g := rfl

@[simp] private lemma coord_val {b r n : ℕ} (eqn : n = fiberSize b r g) (i : Fin n) :
    (coord g eqn i).2.val = i.val := rfl

@[simp] private lemma coord_inj {b r n : ℕ} (eqn : n = fiberSize b r g) (i j : Fin n) :
    coord g eqn i = coord g eqn j ↔ i=j := by
  constructor
  · intro he
    exact Fin.ext (congrArg (fun p => p.2.val) he)
  · rintro rfl
    rfl

private lemma coord_ne {b r n n' : ℕ} (hg : n = fiberSize b r g) (hh : n' = fiberSize b r h)
    (hne : g ≠ h) (i : Fin n) (j : Fin n') : coord g hg i ≠ coord h hh j :=
  fun he => hne (congrArg Sigma.fst he)

private lemma coord_all {b r n : ℕ} (eqn : n = fiberSize b r g) (v : Fin (fiberSize b r g)) :
    ∃ i, coord g eqn i = ⟨g,v⟩ := ⟨v.cast eqn.symm, by simp [coord]⟩

private structure Sizes (m : ℕ) (q : Shape) (g : Group m) (d e x : ℕ) : Prop where
  a : d = fiberSize q.d₀ 9 g
  c : e = fiberSize (q.d₀-1) 9 g
  ext : x = fiberSize q.d₀ 8 g

private lemma sizesBase (m : ℕ) (q : Shape) : Sizes m q 0 q.d₀ (q.d₀-1) q.d₀ :=
  ⟨(fiberSize_zero _ _).symm,(fiberSize_zero _ _).symm,(fiberSize_zero _ _).symm⟩

private lemma sizesReg (i : Cyclic.Regular m) (q : Shape) : Sizes m q i.val 9 9 8 :=
  ⟨(fiberSize_regular _ _ i).symm,(fiberSize_regular _ _ i).symm,(fiberSize_regular _ _ i).symm⟩

private def rowMap (sg : Sizes m q g d e x) (sh : Sizes m q h 9 9 8) : Cross.Row d e → R m q
  | (s,.abL o z) => .inr (.inr (coord g sg.a z,coord h sh.a s,o))
  | (s,.abR o z) => .inr (.inr (coord h sh.a s,coord g sg.a z,o))
  | (s,.acL z) => .inr (.inl (coord g sg.a z,0,.inr (coord h sh.c s)))
  | (s,.acR z) => .inr (.inl (coord h sh.a s,0,.inr (coord g sg.c z)))
  | (s,.bcL z) => .inl (0,.inr (coord g sg.a z),.inr (coord h sh.c s))
  | (s,.bcR z) => .inl (0,.inr (coord h sh.a s),.inr (coord g sg.c z))

private lemma not_singleton (hne : g≠h) (z : Group m) : ({z} : Finset _) ≠ {g,h} := by
  intro he
  have hc := congrArg Finset.card he
  simp [Finset.card_pair hne] at hc

private lemma orient {a b : Group m} (hne : g≠h) (he : ({a,b} : Finset _) = {g,h}) :
    (a=g ∧ b=h) ∨ (a=h ∧ b=g) := by
  have hg : g ∈ ({a,b} : Finset _) := he.symm ▸ Finset.mem_insert_self _ _
  have hh : h ∈ ({a,b} : Finset _) := he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  simp only [Finset.mem_insert,Finset.mem_singleton] at hg hh
  grind

private lemma cover (sg : Sizes m q g d e x) (sh : Sizes m q h 9 9 8) (hne : g≠h)
    (r : R m q) (hr : Global.rowSector r = {g,h}) : ∃ v, rowMap sg sh v = r := by
  have hs := not_singleton hne
  rcases r with ⟨o,j,k⟩ | ⟨i,o,k⟩ | ⟨i,j,p⟩
  · have ho : o=0 := Subsingleton.elim _ _
    subst o
    rcases j with j | ⟨a,j⟩ <;> rcases k with k | ⟨b,k⟩ <;>
      simp [Global.rowSector,Global.raw,Global.labels,xyz,hs] at hr
    rcases orient hne hr with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · obtain ⟨z,rfl'⟩ := coord_all sg.a j
      obtain ⟨s,hs'⟩ := coord_all sh.c k
      exact ⟨(s,.bcL z), by simp [rowMap,rfl',hs']⟩
    · obtain ⟨s,hs'⟩ := coord_all sh.a j
      obtain ⟨z,hz⟩ := coord_all sg.c k
      exact ⟨(s,.bcR z), by simp [rowMap,hz,hs']⟩
  · have ho : o=0 := Subsingleton.elim _ _
    subst o
    obtain ⟨a,i⟩ := i
    rcases k with k | ⟨b,k⟩ <;> simp [Global.rowSector,Global.raw,Global.labels,xyz,hs] at hr
    rcases orient hne hr with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · obtain ⟨z,hz⟩ := coord_all sg.a i
      obtain ⟨s,hs'⟩ := coord_all sh.c k
      exact ⟨(s,.acL z), by simp [rowMap,hz,hs']⟩
    · obtain ⟨s,hs'⟩ := coord_all sh.a i
      obtain ⟨z,hz⟩ := coord_all sg.c k
      exact ⟨(s,.acR z), by simp [rowMap,hz,hs']⟩
  · obtain ⟨a,i⟩ := i
    obtain ⟨b,j⟩ := j
    simp [Global.rowSector,Global.raw,Global.labels,xyz] at hr
    rcases orient hne hr with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · obtain ⟨z,hz⟩ := coord_all sg.a i
      obtain ⟨s,hs'⟩ := coord_all sh.a j
      exact ⟨(s,.abL p z), by simp [rowMap,hz,hs']⟩
    · obtain ⟨s,hs'⟩ := coord_all sh.a i
      obtain ⟨z,hz⟩ := coord_all sg.a j
      exact ⟨(s,.abR p z), by simp [rowMap,hz,hs']⟩

/-- Global slots for the six local face streams. Their type carries the two
group labels used by the derivative along the missing axis. -/
private structure Streams (m : ℕ) (q : Shape) (g h : Group m) (l w : ℕ) where
  abL : Fin l → Fiber m q .ab g h
  abR : Fin l → Fiber m q .ab h g
  acL : Fin l → Fiber m q .ac g h
  bcL : Fin l → Fiber m q .bc g h
  acR : Fin w → Fiber m q .ac h g
  bcR : Fin w → Fiber m q .bc h g

private def colMap (sg : Sizes m q g d e x) (sh : Sizes m q h 9 9 8) (u : Streams m q g h l w) :
    Cross.Col d e x l w → C m q
  | .baseA t z => .inl (coord g sg.ext t,.inl (.inr (coord h sh.a z)))
  | .baseB t z => .inl (coord g sg.ext t,.inr (.inl (.inr (coord h sh.a z))))
  | .baseC t z => .inl (coord g sg.ext t,.inr (.inr (.inr (coord h sh.c z))))
  | .regA t z => .inl (coord h sh.ext t,.inl (.inr (coord g sg.a z)))
  | .regB t z => .inl (coord h sh.ext t,.inr (.inl (.inr (coord g sg.a z))))
  | .regC t z => .inl (coord h sh.ext t,.inr (.inr (.inr (coord g sg.c z))))
  | .abL t o => .inr ((u.abL t).val,.inr (.inr o))
  | .abR t o => .inr ((u.abR t).val,.inr (.inr o))
  | .acL t => .inr ((u.acL t).val,.inr (.inl 0))
  | .bcL t => .inr ((u.bcL t).val,.inl 0)
  | .acR t => .inr ((u.acR t).val,.inr (.inl 0))
  | .bcR t => .inr ((u.bcR t).val,.inl 0)

private lemma ab_a (p : Fiber m q .ab g h) : axisA p.val = g := congrArg Prod.fst p.property
private lemma ab_b (p : Fiber m q .ab g h) : axisB p.val = h := congrArg Prod.snd p.property
private lemma ac_a (p : Fiber m q .ac g h) : axisA p.val = g := congrArg Prod.fst p.property
private lemma ac_c (p : Fiber m q .ac g h) : axisC p.val = h := congrArg Prod.snd p.property
private lemma bc_b (p : Fiber m q .bc g h) : axisB p.val = g := congrArg Prod.fst p.property
private lemma bc_c (p : Fiber m q .bc g h) : axisC p.val = h := congrArg Prod.snd p.property

private lemma tag (sg : Sizes m q g d e x) (sh : Sizes m q h 9 9 8) (u : Streams m q g h l w)
    (j : Cross.Col d e x l w) : Global.colSector axisA axisB axisC (colMap sg sh u j) = {g,h} := by
  cases j <;> simp [colMap,Global.colSector,Global.labels,ab_a,ab_b,ac_a,ac_c,bc_b,bc_c,
    Finset.pair_comm]

private abbrev Vec := ℕ → ℂ
private abbrev Triple := Vec × Vec × Vec

private def pad {n : ℕ} (v : Fin n → ℂ) : Vec := fun k => if h : k<n then v ⟨k,h⟩ else 0

@[simp] private lemma pad_apply {n : ℕ} (v : Fin n → ℂ) (i : Fin n) : pad v i.val = v i := by
  simp [pad,i.isLt]

private structure ExtraValues where
  a : Fin 1 ⊕ ℕ → ℂ
  b : Fin 1 ⊕ ℕ → ℂ
  c : Fin 2 ⊕ ℕ → ℂ

private def extraValues {d e x : ℕ} (z : Fin x → Cross.Extra ℂ d e) (t : ℕ) : ExtraValues :=
  if ht : t<x then
    let f := z ⟨t,ht⟩
    ⟨Sum.elim (fun _ => f.ao) (pad f.a), Sum.elim (fun _ => f.bo) (pad f.b), Sum.elim f.co (pad f.c)⟩
  else ⟨0,0,0⟩

private def localIndex {O : Type} {b r : ℕ} : O ⊕ (Σ k : Group m, Fin (fiberSize b r k)) → O ⊕ ℕ :=
  Sum.map id (fun i => i.2.val)

private def assignment (g : Group m) (f : Factors ℂ d e x l w) (v : Slot m q → Triple) :
    Param m q → ℂ
  | .inl (t,j) =>
    let z := if t.1=g then extraValues f.left t.2.val else extraValues f.right t.2.val
    match j with
    | .inl i => z.a (localIndex i)
    | .inr (.inl i) => z.b (localIndex i)
    | .inr (.inr i) => z.c (localIndex i)
  | .inr (t,.inl i) => (v t).1 i.2.val
  | .inr (t,.inr (.inl i)) => (v t).2.1 i.2.val
  | .inr (t,.inr (.inr i)) => (v t).2.2 i.2.val

/-- The prescribed vectors on each actual slot have the two projections
specified by the local matrix. Reversed faces list their left vector second. -/
private structure Agreement (u : Streams m q g h l w) (f : Factors ℂ d e x l w)
    (v : Slot m q → Triple) : Prop where
  abL : ∀ t, Face.ab.project (v (u.abL t).val) = (pad (f.abL t).1,pad (f.abL t).2)
  abR : ∀ t, Face.ab.project (v (u.abR t).val) = (pad (f.abR t).2,pad (f.abR t).1)
  acL : ∀ t, Face.ac.project (v (u.acL t).val) = (pad (f.acL t).1,pad (f.acL t).2)
  bcL : ∀ t, Face.bc.project (v (u.bcL t).val) = (pad (f.bcL t).1,pad (f.bcL t).2)
  acR : ∀ t, Face.ac.project (v (u.acR t).val) = (pad (f.acR t).2,pad (f.acR t).1)
  bcR : ∀ t, Face.bc.project (v (u.bcR t).val) = (pad (f.bcR t).2,pad (f.bcR t).1)

set_option maxHeartbeats 2400000 in
private lemma entries (sg : Sizes m q g d e x) (sh : Sizes m q h 9 9 8) (hne : g≠h)
    (u : Streams m q g h l w) (f : Factors ℂ d e x l w) (v : Slot m q → Triple)
    (agree : Agreement u f v) (i : Cross.Row d e) (j : Cross.Col d e x l w) :
    Global.mat axisA axisB axisC (assignment g f v) (rowMap sg sh i) (colMap sg sh u j) =
      Cross.matrix f i j := by
  have disjoint {b r n n' : ℕ} (hg : n = fiberSize b r g) (hh : n' = fiberSize b r h)
      (k : Fin n) (k' : Fin n') := coord_ne hg hh hne k k'
  have disjoint' {b r n n' : ℕ} (hh : n = fiberSize b r h) (hg : n' = fiberSize b r g)
      (k : Fin n) (k' : Fin n') := coord_ne hh hg hne.symm k k'
  have flipped := hne.symm
  obtain ⟨s,r⟩ := i
  cases j
  case' abL t o => obtain ⟨h1,h2⟩ := Prod.mk.inj (agree.abL t)
  case' abR t o => obtain ⟨h1,h2⟩ := Prod.mk.inj (agree.abR t)
  case' acL t => obtain ⟨h1,h2⟩ := Prod.mk.inj (agree.acL t)
  case' acR t => obtain ⟨h1,h2⟩ := Prod.mk.inj (agree.acR t)
  case' bcL t => obtain ⟨h1,h2⟩ := Prod.mk.inj (agree.bcL t)
  case' bcR t => obtain ⟨h1,h2⟩ := Prod.mk.inj (agree.bcR t)
  all_goals
    cases r <;>
      simp [Global.mat,baseMatrix,xyz,rowMap,colMap,Cross.matrix, Global.xa,Global.xb,Global.xc,
        Global.na,Global.nb,Global.nc,Global.inner,Global.extra,assignment,localIndex,extraValues,
        ab_a,ab_b,ac_a,ac_c,bc_b,bc_c,eq_comm,mul_comm, *]

private lemma lift (sg : Sizes m q g d e x) (sh : Sizes m q h 9 9 8) (hne : g≠h)
    (u : Streams m q g h l w) (f : Factors ℂ d e x l w) (v : Slot m q → Triple)
    (agree : Agreement u f v) (hs : Function.Surjective (Cross.matrix f).mulVec) : SolvedAt m q {g,h} := by
  refine ⟨assignment g f v, Global.at_of_template axisA axisB axisC _ _ _ (rowMap sg sh) (colMap sg sh u) ?_ ?_ ?_ hs⟩
  · exact cover sg sh hne
  · exact tag sg sh u
  · exact entries sg sh hne u f v agree

private noncomputable def mixedStreams (i : Cyclic.Regular m) (q : Shape) :
    Streams m q 0 i.val q.edge 27 where
  abL := baseRegEquiv .ab i
  acL := baseRegEquiv .ac i
  bcL := baseRegEquiv .bc i
  abR := regBaseEquiv i .ab
  acR := regBaseEquiv i .ac
  bcR := regBaseEquiv i .bc

private def mixedData (z : MixedData ℂ q.d₀ q.edge) : BaseRegData q Vec Vec Vec where
  left t := (pad (z.u t).1,pad (z.u t).2.1,pad (z.u t).2.2)
  right t := (pad (z.v t).2.1,pad (z.v t).1,pad (z.v t).2.2)
  inversePair t := (pad (z.w t).2.1,pad (z.w t).2.2,pad (z.w t).1)

/-- Each finite base–regular witness specializes the global block at any
ordinary group, including the case in which the inverse group is itself. -/
theorem mixed_at (q : Shape) (i : Cyclic.Regular m) (hs : Cross.Mixed q.d₀ q.edge) :
    SolvedAt m q {0,i.val} := by
  obtain ⟨z,hz⟩ := hs
  apply lift (sizesBase m q) (sizesReg i q) i.property.symm (mixedStreams i q)
    (mixedFactors z) (baseRegFactors i (mixedData z) (0,0,0)) _ hz
  have fw (k : Face) (t : Fin q.edge) := congrArg k.project
    (baseRegFactors_forward k i (mixedData (q:=q) z) (0,0,0) t)
  have bw (k : Face) (t : Fin (regBaseSize q k)) := congrArg k.project
    (baseRegFactors_reverse k i (mixedData (q:=q) z) (0,0,0) t)
  exact ⟨fw .ab,bw .ab,fw .ac,fw .bc,bw .ac,bw .bc⟩

private noncomputable def regularStreams (i j : Cyclic.Regular m) (hne : i ≠ j) (q : Shape) :
    Streams m q i.val j.val 27 27 where
  abL := regRegEquiv .ab i j hne
  acL := regRegEquiv .ac i j hne
  bcL := regRegEquiv .bc i j hne
  abR := regRegEquiv .ab j i hne.symm
  acR := regRegEquiv .ac j i hne.symm
  bcR := regRegEquiv .bc j i hne.symm

private def padded (z : RegularFaceData (Fin 9 → ℂ) (Fin 9 → ℂ) (Fin 9 → ℂ)) :
    RegularFaceData Vec Vec Vec where
  ab t := (pad (z.ab t).1,pad (z.ab t).2)
  acbc t := (pad (z.acbc t).1,pad (z.acbc t).2.1,pad (z.acbc t).2.2)

/-- Each regular-pair witness specializes the global block at any distinct
pair. Both orientations use the same global cyclic slot factors. -/
theorem regular_at (q : Shape) (i j : Cyclic.Regular m) (hne : i ≠ j) (hs : Cross.Regular) :
    SolvedAt m q {i.val,j.val} := by
  obtain ⟨z,hz⟩ := hs
  apply lift (sizesReg i q) (sizesReg j q) (fun he => hne (Subtype.ext he)) (regularStreams i j hne q)
    (regularFactors z) (regRegFactors i j (padded z.forward) (padded z.reverse) (0,0,0)) _ hz
  have fw (k : Face) := regRegFactors_forward (q:=q) k i j hne
    (padded z.forward) (padded z.reverse) (0,0,0)
  have bw (k : Face) := regRegFactors_reverse (q:=q) k i j hne
    (padded z.forward) (padded z.reverse) (0,0,0)
  exact ⟨fw .ab,bw .ab,fw .ac,fw .bc,bw .ac,bw .bc⟩

end TensorRankThreeFactor.Construction.CrossAdapter

namespace TensorRankThreeFactor.RegularDiagonal

open TensorRankThreeFactor.FastBase TensorRankColumnReduction

abbrev D := Fin 9
abbrev S := Fin 1 ⊕ D
abbrev T := Fin 2 ⊕ D
abbrev Rows := (D × D × Fin 2) ⊕ ((D × D) ⊕ ((D × D) ⊕ ((D × Fin 2) ⊕ ((D × Fin 2) ⊕ D))))
abbrev Shift := Fin 1 ⊕ (Fin 1 ⊕ Fin 2)
abbrev Cols (z t : ℕ) := (Fin 8 × (S ⊕ (S ⊕ T))) ⊕
  ((Fin 27 × Fin 2) ⊕ (Fin z ⊕ (Fin z ⊕ (Fin t × Shift))))

structure Factors (K : Type) (z t : ℕ) where
  a : Fin 8 → S → K
  b : Fin 8 → S → K
  c : Fin 8 → T → K
  abA : Fin 27 → D → K
  abB : Fin 27 → D → K
  acA : Fin z → D → K
  acC : Fin z → D → K
  bcB : Fin z → D → K
  bcC : Fin z → D → K
  triA : Fin t → D → K
  triB : Fin t → D → K
  triC : Fin t → D → K

def xyz : Rows → S × S × T
  | .inl (i,j,h) => (.inr i,.inr j,.inl h)
  | .inr (.inl (i,k)) => (.inr i,.inl 0,.inr k)
  | .inr (.inr (.inl (j,k))) => (.inl 0,.inr j,.inr k)
  | .inr (.inr (.inr (.inl (i,h)))) => (.inr i,.inl 0,.inl h)
  | .inr (.inr (.inr (.inr (.inl (j,h))))) => (.inl 0,.inr j,.inl h)
  | .inr (.inr (.inr (.inr (.inr k)))) => (.inl 0,.inl 0,.inr k)

section Geometry
variable {K : Type} [CommSemiring K] {z t : ℕ}

def extra (f : Factors K z t) (r : Rows) : Fin 8 × (S ⊕ (S ⊕ T)) → K
  | (v,.inl h) => if h=(xyz r).1 then f.b v (xyz r).2.1 * f.c v (xyz r).2.2 else 0
  | (v,.inr (.inl h)) => if h=(xyz r).2.1 then f.a v (xyz r).1 * f.c v (xyz r).2.2 else 0
  | (v,.inr (.inr h)) => if h=(xyz r).2.2 then f.a v (xyz r).1 * f.b v (xyz r).2.1 else 0

def ab (a b : D → K) (h : Fin 2) : Rows → K
  | .inl (i,j,k) => if h=k then a i * b j else 0
  | _ => 0

def ac (a c : D → K) : Rows → K
  | .inr (.inl (i,k)) => a i * c k
  | _ => 0

def bc (b c : D → K) : Rows → K
  | .inr (.inr (.inl (j,k))) => b j * c k
  | _ => 0

def matrix (f : Factors K z t) : Matrix Rows (Cols z t) K := fun r j =>
  match j with
  | .inl w => extra f r w
  | .inr (.inl (v,h)) => ab (f.abA v) (f.abB v) h r
  | .inr (.inr (.inl v)) => ac (f.acA v) (f.acC v) r
  | .inr (.inr (.inr (.inl v))) => bc (f.bcB v) (f.bcC v) r
  | .inr (.inr (.inr (.inr (v,.inl _)))) => bc (f.triB v) (f.triC v) r
  | .inr (.inr (.inr (.inr (v,.inr (.inl _))))) => ac (f.triA v) (f.triC v) r
  | .inr (.inr (.inr (.inr (v,.inr (.inr h))))) => ab (f.triA v) (f.triB v) h r
end Geometry

def complexify {z t : ℕ} (f : Factors ℕ z t) : Factors ℂ z t :=
  ⟨fun v i => f.a v i,fun v i => f.b v i,fun v i => f.c v i,
   fun v i => f.abA v i,fun v i => f.abB v i,fun v i => f.acA v i,fun v i => f.acC v i,
   fun v i => f.bcB v i,fun v i => f.bcC v i,fun v i => f.triA v i,
   fun v i => f.triB v i,fun v i => f.triC v i⟩

lemma cast_matrix {z t : ℕ} (f : Factors ℕ z t) :
    (matrix f : Matrix Rows (Cols z t) ℕ).map (Nat.castRingHom ℂ) = matrix (complexify f) := by
  ext r j
  change ((matrix f r j : ℕ) : ℂ) = _
  rcases j with ⟨v,h|h|h⟩|⟨v,h⟩|v|v|⟨v,h|h|h⟩ <;>
    rcases r with ⟨i,j,k⟩|⟨i,k⟩|⟨j,k⟩|⟨i,k⟩|⟨j,k⟩|k <;>
    simp only [matrix,extra,ab,ac,bc,complexify,apply_ite,Nat.cast_zero,Nat.cast_mul]
  all_goals split <;> simp_all

abbrev abCol {z t} (j : Fin 27) (k : Fin 2) : Cols z t := .inr (.inl (j,k))
abbrev acCol {z t} (j : Fin z) : Cols z t := .inr (.inr (.inl j))
abbrev bcCol {z t} (j : Fin z) : Cols z t := .inr (.inr (.inr (.inl j)))
abbrev triCol {z t} (j : Fin t) (h : Shift) : Cols z t := .inr (.inr (.inr (.inr (j,h))))

/-- Only one free coordinate per axis of an extra point can contribute to a given row. -/
def extraProduct {z t : ℕ} (f : Factors ℕ z t) (B : Cols z t → seven.W) (r : Rows) : seven.W :=
  let (i,j,k) := xyz r
  accumulate 8 (fun v w =>
    seven.axpy (f.b v j*f.c v k) (B (.inl (v,.inl i)))
      (seven.axpy (f.a v i*f.c v k) (B (.inl (v,.inr (.inl j))))
        (seven.axpy (f.a v i*f.b v j) (B (.inl (v,.inr (.inr k)))) w))) seven.zero

def foldRows {n : ℕ} (a : Fin n → ℕ) (b : Fin n → seven.W) (w : seven.W) : seven.W :=
  accumulate n (fun v p => seven.axpy (a v) (b v) p) w

def rowProduct {z t : ℕ} (f : Factors ℕ z t) (B : Cols z t → seven.W) (r : Rows) : seven.W :=
  let w := extraProduct f B r
  match r with
  | .inl (i,j,h) =>
    let w := foldRows (fun v => f.abA v i*f.abB v j) (fun v => B (abCol v h)) w
    foldRows (fun v => f.triA v i*f.triB v j) (fun v => B (triCol v (.inr (.inr h)))) w
  | .inr (.inl (i,k)) =>
    let w := foldRows (fun v => f.acA v i*f.acC v k) (fun v => B (acCol v)) w
    foldRows (fun v => f.triA v i*f.triC v k) (fun v => B (triCol v (.inr (.inl 0)))) w
  | .inr (.inr (.inl (j,k))) =>
    let w := foldRows (fun v => f.bcB v j*f.bcC v k) (fun v => B (bcCol v)) w
    foldRows (fun v => f.triB v j*f.triC v k) (fun v => B (triCol v (.inl 0))) w
  | _ => w

lemma sum_axpy {n : ℕ} (a : Fin n → ℕ) (b : Fin n → seven.W) (w : seven.W) (q : ℕ) :
    seven.eval (foldRows a b w) q =
    (∑ v, (a v : ZMod 7) * seven.eval (b v) q) + seven.eval w q :=
  eval_accumulate seven q _ _ _ (fun _ _ => seven.eval_axpy _ _ _ _)

lemma extraProduct_eval {z t : ℕ} (f : Factors ℕ z t) (B : Cols z t → seven.W) (r : Rows) (q : ℕ) :
    seven.eval (extraProduct f B r) q =
      ∑ k : Fin 8 × (S ⊕ (S ⊕ T)), ((extra f r k : ℕ) : ZMod 7) * seven.eval (B (.inl k)) q := by
  obtain ⟨i,j,k,hu⟩ : ∃ i j k, xyz r = (i,j,k) := ⟨_,_,_,rfl⟩
  let g (v : Fin 8) := ((f.b v j*f.c v k : ℕ) : ZMod 7)*seven.eval (B (.inl (v,.inl i))) q +
     (((f.a v i*f.c v k : ℕ) : ZMod 7)*seven.eval (B (.inl (v,.inr (.inl j)))) q +
       ((f.a v i*f.b v j : ℕ) : ZMod 7)*seven.eval (B (.inl (v,.inr (.inr k)))) q)
  simp only [extraProduct,hu]
  rw [eval_accumulate seven q (g:=g) (hf:=by intro v p; simp only [g,seven.eval_axpy,add_assoc]),
    seven.eval_zero,add_zero,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  simp [extra,hu,Fintype.sum_sum_type,g,apply_ite,ite_mul]

lemma rowProduct_eval {z t : ℕ} (f : Factors ℕ z t) (B : Cols z t → seven.W) (r : Rows) (q : ℕ) :
    seven.eval (rowProduct f B r) q = ∑ j : Cols z t, ((matrix f r j : ℕ) : ZMod 7)*seven.eval (B j) q := by
  rw [Fintype.sum_sum_type]
  change _ = (∑ j, ((extra f r j : ℕ) : ZMod 7) * _) + _
  rw [← extraProduct_eval f B r q]
  rcases r with ⟨i,j,k⟩|⟨i,k⟩|⟨j,k⟩|⟨i,k⟩|⟨j,k⟩|k <;>
    simp only [rowProduct,sum_axpy,Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_one,
      matrix,ab,ac,bc,apply_ite,ite_mul,Nat.cast_zero,zero_mul,Finset.sum_const_zero,add_zero,zero_add,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true,abCol,acCol,bcCol,triCol]
  all_goals abel

/-- A lower triangular modular product with the geometric matrix certifies the complex specialization. -/
lemma certified {z t : ℕ} (f : Factors ℕ z t) (B : Cols z t → seven.W)
    (order : Fin 369 ≃ Rows)
    (h : ∀ i : Fin 369, seven.test (rowProduct f B (order i)) i.val=true) :
    ∃ f : Factors ℂ z t, Function.Surjective (matrix f : Matrix Rows (Cols z t) ℂ).mulVec := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let M : Matrix (Fin 369) (Cols z t) ℤ := fun i j => (matrix f (order i) j : ℕ)
  let C := M.map (Int.castRingHom (ZMod 7))
  let T : Matrix (Cols z t) (Fin 369) (ZMod 7) := fun j i => seven.eval (B j) i.val
  let L := C*T
  have he (i j : Fin 369) : L i j = seven.eval (rowProduct f B (order i)) j.val := by
    rw [rowProduct_eval]
    change (∑ k, (((matrix f (order i) k : ℕ) : ℤ) : ZMod 7)*_) = _
    simp only [Int.cast_natCast,T]
  have ht : L.IsLowerTriangular := fun i j hij => (he i j).trans (seven.test_above (h i) hij)
  have hd : L.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular L ht]
    exact Finset.prod_ne_zero_iff.mpr fun i _ hz => seven.test_diag (h i) ((he i i).symm.trans hz)
  have hl : Function.Surjective L.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  have hs := lift M (fun y => by
    obtain ⟨v,hv⟩ := hl y
    exact ⟨T.mulVec v,(Matrix.mulVec_mulVec _ _ _).trans hv⟩)
  refine ⟨complexify f,?_⟩
  rw [← cast_matrix]
  intro y
  obtain ⟨v,hv⟩ := hs fun i => y (order i)
  refine ⟨v,?_⟩
  funext r
  have hv' := congrFun hv (order.symm r)
  change (∑ k, ((M (order.symm r) k : ℤ) : ℂ)*v k) = y (order (order.symm r)) at hv'
  change (∑ k, ((matrix f r k : ℕ) : ℂ)*v k) = y r
  simpa only [M,Int.cast_natCast,Equiv.apply_symm_apply] using hv'

end TensorRankThreeFactor.RegularDiagonal

namespace TensorRankThreeFactor.RegularDiagonal

open TensorRankColumnReduction TensorRankThreeFactor.FastBase

def rows : Rows ≃ Fin 369 :=
  sumFin (prodFin (Equiv.refl D) finProdFinEquiv)
    (sumFin finProdFinEquiv
      (sumFin finProdFinEquiv (sumFin finProdFinEquiv (sumFin finProdFinEquiv (Equiv.refl D)))))

def colNumber {z t : ℕ} : Cols z t → ℕ
  | .inl (v,.inl i) => 31*v.val+(finSumFinEquiv i).val
  | .inl (v,.inr (.inl j)) => 31*v.val+10+(finSumFinEquiv j).val
  | .inl (v,.inr (.inr k)) => 31*v.val+20+(finSumFinEquiv k).val
  | .inr (.inl (v,h)) => 248+2*v.val+h.val
  | .inr (.inr (.inl v)) => 302+v.val
  | .inr (.inr (.inr (.inl v))) => 302+z+v.val
  | .inr (.inr (.inr (.inr (v,.inl _)))) => 302+2*z+4*v.val
  | .inr (.inr (.inr (.inr (v,.inr (.inl _))))) => 303+2*z+4*v.val
  | .inr (.inr (.inr (.inr (v,.inr (.inr h))))) => 304+2*z+4*v.val+h.val

def atSlopes (v : Fin 8) : T → ℕ
  | .inl h => if v.val=7 then h.val else if h=0 then 1 else v.val
  | .inr i => if v.val=i.val then 1 else 0

def atSide (v : Fin 8) : S → ℕ
  | .inl _ => 1
  | .inr i => if v.val=i.val then 1 else 0

/-- Each twelve-bit chunk holds a row index times seven plus a coefficient. -/
def unpack : ℕ → ℕ → Packed
  | 0,_ => zero
  | n+1,w => if w=0 then zero else
    let d := w%4096
    let u := (1 : ℕ) <<< (d/7)
    let q := unpack n (w >>> 12)
    let v := d%7
    ((if v.testBit 0 then u ||| q.1 else q.1),
      (if v.testBit 1 then u ||| q.2.1 else q.2.1),
      (if v.testBit 2 then u ||| q.2.2 else q.2.2))

def indices (a : Array ℕ) (i : Fin 369) : Fin 369 := Fin.ofNat 369 (a[i.val]?.getD 0)

def ordering (forward back : Array ℕ)
    (hf : ∀ i, indices back (indices forward i) = i)
    (hb : ∀ i, indices forward (indices back i) = i) : Fin 369 ≃ Rows :=
  (Equiv.mk (indices forward) (indices back) hf hb).trans rows.symm

end TensorRankThreeFactor.RegularDiagonal

namespace TensorRankThreeFactor.RegularDiagonal
namespace Data9

open TensorRankColumnReduction TensorRankThreeFactor.FastBase

def factors : Factors ℕ 22 10 :=
  ⟨atSide,atSide,atSlopes,
fromTable #[
  0x10000000,0x100000000,1,0x10000,0x10000000,0x1000000,0x1000,0x100,0x10,0x10000,0x1000,0x10,0x1000000,
  0x100000000,0x1000000,1,0x100000,1,0x10000000,0x100000000,0x10000,0x100000,0x100000000,0x10000200,
  0x100000600,0x100050,0x102400350],
   fromTable #[
  0x1000,0x100000,0x1000,0x100000000,0x10000,0x1000000,0x100000000,0x1000000,0x10000,0x1000,0x1000,
  1,0x10000000,1,0x100000,0x100000000,0x1000,0x10,0x100,0x1000000,0x100000,0x10,0x100000000,0x600000060,
  0x20040000,0x500050000,0x360100520],
   fromTable #[
  0x1000,0x10000,0x100000000,0x1000,0x10000000,0x10,0x10,0x10000,0x100000000,0x10,0x10,0x10,0x100000000,
  0x100,0x1000000,0x10000,1,0x100000000,0x100,0x10000,0x100,0x100],
   fromTable #[
  0x100000000,0x10000,0x100,0x1000000,1,0x10000000,0x100,0x1000000,0x10000000,0x1000,0x1000000,0x100000000,
  0x100000000,0x100000000,0x1000,0x100000000,0x10000000,0x10,0x100000,0x100,1,0x100000],
   fromTable #[
  0x100000,0x10000000,0x1000000,0x100000000,0x10000,0x100,0x100000000,0x1000000,0x10,0x100000000,0x1000,
  0x10,0x100000,0x100000000,0x100000000,1,0x100000,0x100000000,1,0x10000000,0x100000000,0x100000000],
   fromTable #[
  0x10,0x10000000,0x10,0x100000,0x100000,0x10,0x1000,0x100000000,1,0x10000,0x10,0x100000,0x100000000,
  0x100000000,0x100,0x100,0x100,0x10,0x100000000,0x10,0x10000000,0x1000000],
   fromTable #[
  0x1000000,0x10000000,0x100000000,0x100,0x100000,1,0x1000000,0x100000,1,0x100000000],
   fromTable #[
  0x100,0x10000000,0x1000,0x1000,1,0x100000,0x10000,0x10000000,0x1000000,0x100],
   fromTable #[
  0x10000000,0x10000,0x1000,0x100,0x1000000,0x1000,1,0x100000000,0x10000,0x10000]⟩

def seq : Array ℕ := #[
  17,145,242,323,1,14,15,126,127,170,251,224,305,233,314,234,144,250,169,260,179,269,188,278,197,287,
  206,306,225,315,16,368,215,296,142,5,4,164,261,9,8,37,245,36,180,55,54,189,246,270,68,69,196,277,
  309,73,72,198,279,247,166,86,87,205,286,109,108,128,226,136,137,230,295,214,138,139,231,304,228,
  132,133,239,240,156,157,311,312,3,6,7,11,13,19,70,71,88,89,91,104,105,122,130,134,135,140,150,151,
  154,155,160,161,165,216,223,235,236,237,238,241,249,307,310,316,317,318,319,320,321,322,2,10,12,
  18,42,43,48,49,78,79,82,83,90,96,97,116,117,123,131,148,149,173,174,177,178,195,200,204,213,219,
  229,252,257,262,265,268,271,272,284,289,290,291,298,301,129,143,163,167,168,171,175,176,181,183,
  184,186,187,190,191,193,194,199,201,203,207,208,209,210,211,217,218,220,221,227,254,255,258,259,
  266,276,281,285,288,294,297,300,26,27,60,61,92,93,112,113,118,119,120,121,141,182,185,202,273,313,
  152,153,24,25,30,31,32,52,58,59,264,62,63,274,282,64,65,275,66,67,74,75,280,256,76,77,84,85,102,
  103,302,114,115,124,146,244,248,267,292,299,308,0,33,80,81,159,172,192,212,222,232,243,263,283,338,
  56,57,330,331,356,34,35,332,333,363,20,21,40,41,100,101,162,339,355,357,364,22,28,46,106,343,325,
  342,324,158,340,50,51,253,293,303,337,354,367,38,44,45,350,351,94,110,336,348,358,344,23,47,341,
  349,347,29,326,328,327,360,53,359,366,39,345,95,365,346,107,361,362,329,98,353,335,99,111,334,352,
  125,147]

def back : Array ℕ := #[
  274,4,129,87,36,35,88,89,40,39,130,90,131,91,5,6,30,0,132,92,298,299,309,338,235,236,215,216,310,
  343,237,238,239,275,293,294,43,41,327,351,300,301,133,134,328,329,311,339,135,136,319,320,240,348,
  46,45,288,289,241,242,217,218,244,245,248,249,251,252,50,51,93,94,56,55,253,254,257,258,137,138,
  276,277,139,140,259,260,61,62,95,96,141,97,219,220,332,353,142,143,360,363,302,303,261,262,98,99,
  312,356,66,65,333,364,221,222,264,265,144,145,223,224,225,226,100,146,266,367,7,8,67,173,101,147,
  79,80,102,103,69,70,74,75,104,227,34,174,16,1,267,368,148,149,105,106,233,234,107,108,83,84,317,
  278,109,110,304,175,37,111,60,176,177,18,9,178,279,150,151,179,180,152,153,20,44,181,228,182,183,
  229,184,185,22,47,186,187,280,188,189,154,52,24,57,190,155,191,230,192,156,63,26,193,194,195,196,
  197,281,157,73,32,112,198,199,158,200,201,282,113,11,28,68,202,78,159,71,76,283,13,15,114,115,116,
  117,81,82,118,2,284,268,42,48,59,269,119,17,10,160,321,203,204,256,161,205,206,19,38,162,285,243,
  163,207,270,164,21,49,165,166,231,246,250,208,53,23,58,255,209,247,286,167,210,64,25,211,168,169,
  170,271,322,212,72,33,213,171,272,214,172,263,323,77,12,27,120,273,54,121,85,86,232,14,29,122,123,
  124,125,126,127,128,3,316,314,344,346,345,359,290,291,295,296,365,362,334,324,287,305,318,340,315,
  313,337,352,355,342,335,341,330,331,366,361,325,306,292,307,336,349,347,357,358,297,308,354,350,
  326,31]

def order : Fin 369 ≃ Rows := ordering seq back (by decide +kernel) (by decide +kernel)

def cert : Array ℕ := #[
  0x7c5,0xa14a0fa058a377f,0x97c96e4df,0x12e,0x143,0x189,0xa16a0ca04a019fa983548,0x1cf,0x32,0x6a,0xa13a0aa0689e851,
  0,0xa16a0a9f89a699f97c938,0xfd,0x158,0x119,0xa16a0ca04a019fa9835c6,0xa14a0ea049fc9f59285d4,0x24,
  0xcc,0xa13a0aa0689e,0x1d,0,0xa12a0ca078954ca,0x104,0x151,0x19e,0xa11a0ea084d1,0x8aa4d8,0x78,0x40,
  0xa139778c8,0xa15a0da04890,0,0xa12a0d99f8f2,0x7ed7e1,0x6f3,0xa13a0aa079fa9c4,0xa0e9f5,0x1d6,0xa1574e,
  0xa13977,0xa15a0da04890755,0,0xa12a0d944874,0x67a66e,0x6fa,0xa13a0c96787b,0x68867c,0xa1568a,0xa11a0a9bd,
  0xa14827,0xa13a0d82e,0x977969,0xa1497c7a2,0xa11a0d99f58e,0x7ed595,0x7064e6,0xa11a0c9674ed,0xa14a0e9f592159c,
  0xa13a0f98a5a3,0x86,0xa0b9d79b6,0xf6,0xa11a0c93f,0,0x69f,0x714708,0xa12a0b9ad915,0xa13a0c9d79cb,
  0xa148ba,0xa14a0a9528b3,0xa11a0a9d799a970,0x120,0xa16a0c99a,0,0x95992a,0x9058f9,0xa11a0a94b882,0xa13a0c9d79cb771,
  0xa148ba778,0xa15691,0xa16835,0xa11a0f83c,0x10b,0xa15a0c99a8f74f4,0xa0e9d29bb7cc,0x6ab4fb,0xa15905502,
  0xa11a0b9ad5aa,0xa0d9d7509,0xa0d8c6510,0x94,0xa11a0ba089f99ef9e7820,0x8a9897,0x675,0x6a6,0,0x6c2,
  0xa11a0ba089f99ef9e7,0x745739,0x223,0xa0f94d,0,0x13c,0x7e8,0x6a4698,0xa16a0ea039f69f29ec954,0x6b96ad,
  0x6d56c9,0x6e5,0x15f,0xa11a0a991931,0x7ef,0x7f6,0x14a,0x7e87e6517,0x6a451e,0x7a9,0x6b9525,0x6d552c,
  0x7455b1,0x16d,0xa2,0xa15a0c9ee913907,0x112,0x701,0xa12900,0x6b4,0,0xa12a0b9ef9d9,0xa14a049fc,0xa157fd,
  0xa158ac,0x81e812,0x182,0x6f86ec,0x70f,0x6bb,0,0xa12a0b9ef9d976a,0x722716,0x1ac,0xa15a0b9bf98c,0x78d,
  0x794,0x190,0x6f8533,0x9008fe5b8,0x6c753a,0xa12a0d9f390e90c7d3,0x81e541,0xa12a0d9f35bf,0x1ba,0xb0,
  0xa14a0da039af8cf,0xa16a0ba03,0xa16a0d962,0xa13a0f946,0x6d0,0x819,0,0x732,0x1e4,0x238,0xa14a0da039af,
  0xa16a0ba0375c,0xa16a0a9f89a1,0xa16a0e9a8,0x6d7,0xa14a0a9f290e,0,0x730724,0x254,0xa11a0c9bf889,0xa13843,
  0xa14a0c84a,0xa11a0da079fc9f597e,0xa14a0fa049f59c954f,0xa15a0e9a891a556,0xa16a0ea039f69f29ec55d,
  0xa15a0e9f29de564,0xa13a0ca089b47b0,0xa15a0fa049f39e55cd,0x1f9,0xda,0,0x8a5,0x683,0xa0c9d2,0x6ea6de,
  0x71d,0x72b,0xa14a0ea049f59f29e59d7993,0x207,0x23f,0xa13a0ba079fa9ef9e09d29988d6,0x1c8,0xa13a0b9fa91c,
  0xa0c9d2763,0x740,0xa15a0c9ee,0xa12a0aa079ee9e0,0,0x25b,0xa11747,0xa0fa07a019fa9d29d09238e4,0xa11a0a9d39cf85f,
  0xa13a0ba07a019fa923,0xa0b9fa56b,0xa14a0d9d29d0572,0x6ea5db,0xa13a07a01579,0x737580,0x8db7b7,0x21c,
  0x4e,0xa11866,0x2b,0xa14a0e786,0xa0c8c1,0x166,0x1b3,0x200,0xa15a0ba089fe9fa8dd,0xa14a0c98a8f07be,
  0xa12a0a8ad79b,0xa13a0d9858eb,0x39,0xa14a0a9854bc,0xa12a0f9d49ba9a995b,0x174,0x1c1,0x1eb,0x20e,0,
  0xa14a0a9854c3,0xa158bf8027da,0x8be858,0xbe,0x1dd,0xa138bf587,0x17b,0xa11a0ba049fc9ef9d990086d,0x1f2,
  0x215,0,0x5c,0x22a,0x231,0xa162ee,0xa11a0f2f5,0x8a689c269,0x8aa89a270,0xa12a0e9c099129a,0xa11a0f9be98e2a1,
  0xa128022cb,0xa117ff2d2,0xa13a0c9fc9ef9e09cb9989288e9628,0xa13a0da049f59f29e59d59cc99386462f,0xa16a0f98c93628c,
  0xa14a0d98e934293,0xa14a0a9d07763b2,0xa11a0d9d49cf7753b9,0xa12a0a9bd8067066ff5e2,0xa0b9bd80d7036ff5e9,
  0x6c76c03c0,0x6c56bd3c7,0xa11a0ba089f99ef9e79597f45f0,0xa13a0fa069f59f39e99577fb5f7,0xa12a0ca0797796989575a4e439d,
  0xa12a0ca0789575a285,0xa122bd,0xa039ff9f58e23ff,0x71,8,0xa13a0fa049f39e573761a,0xa14a0fa079ee9e0733621,
  0xd3,1,0xa16a0ea039f69f29ec6dc3e3,0xa14a0aa059fa9ee9ea6d83ea,0xa13a0ba079f79a199a97793d895388,0xa12a0ca07895262,
  0xa138bf2c4,0xa14a0a9d59b79ac9608be406,0x246,0x24d,0xa15a0e9f29de81e76f3ce,0xa16a0f9f39db81a76c3d5,
  0xa14a0ea049f89c99a65fe,0xa13a049f69c99a2605,0xa142fc,0xa13a0d303,0xef,0xa14a0a985,0xa148b0660,0xa128b1667,
  0xa13a0e9c1804,0xa0c9c180b,0xa11,0xa16a0a,0xa9,0xa15a0c9ee9139078198177d864b,0xa13a0f94d8b8326,0x7406e56e35b6437,
  0xc5,0xa0c98578b5a8430,0xa1599a94459341b,0xa15a0c9ee7225c4445,0xa15a0f8b07a033b,0x7e867a59a422,0xa13a0b9fa91c6885a1429,
  0x8d,0xf,0x9b,0x74073e6e55e0453,0xb7,0x7f,0xa1275331f,0xa13a0f9a894b644,0x9058f970f70d5bd43e,0x135,
  0,0xa0ea079fa9c4962880554499,0xa1686b659,0xa0e9f56836815704ae,0xa16a0d9c088e373,0xa13a0f9ef913819546492,
  0x99f93f8f28794f946f,0xa16a0f98c936365,0x55,0xa11a0f9f79a199a96e93d461,0xa12a0e9c099136c,0x7ed7e167567351c484,
  0xa0c9f79a69624f2468,0xe8,0x16,0xa1269635e,0x127,0xa11a0a9ad94691588755b4a0,0xa16a0f9c2357,0x47,
  0xa1268f349,0xa13a0f98a4c8381,0xa1674c37a,0xa15a0d9d59b79ac9608c151547d,0xa12a0ea039ff9f58e2318,
  0xa11a0a9d076860c,0xa14a0a9d49cf763613,0xa16a0ea07a019f29de905872350,0xa11a0ea07a019f29de90587280245a,
  0xa128ba7fd7df2d9,0xa13a0d9858eb8bb85d7c3636,0x9598257ae652,0xa0a95232d,0xa0a9522e0,0xa0c9502e7,
  0x95492f69f52348b,0xa16a0a9b699f9757d163d,0x95492f6ab3a4,0x95592e6a93ab,0x8a54dd342,0xa12a0aa079ee9e07305d244c,
  0xa12a0ba069fc9f597e76154d3dc,0xa15a0da0475d2a8,0xa11a0ba089f99ef9e76d06ce5624a7,0x8a689c30a,0xa12a0ba069fc9f597e5cb38f,
  0xa15a0da04277,0x197,0xa14a0ea049fc9f5928311,0xa15a0da07a019f33f1,0xa13a0ca089fe9ee3f8,0x63,0xe1,
  0xa142af,0xa13a0d2b6,0xa14a049fc71d71b57e4b5,0x1a5,0xa13a0ba07a019fa9238aa5d9396,0x8a527e,0xa12900714507476,
  0xa128b1334,0xa15a0f94d8b840d,0xa1494e8b7414]

def B (j : Cols 22 10) : Packed := unpack 11 (cert[colNumber j]?.getD 0)

end Data9

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
lemma spans9 : ∃ f : Factors ℂ 22 10, Function.Surjective (matrix f).mulVec := by
  apply certified Data9.factors Data9.B Data9.order
  decide +kernel

end TensorRankThreeFactor.RegularDiagonal

namespace TensorRankThreeFactor.RegularDiagonal
namespace Data12

open TensorRankColumnReduction TensorRankThreeFactor.FastBase

def factors : Factors ℕ 34 4 :=
  ⟨atSide,atSide,atSlopes,
fromTable #[
  0x1000000,0x10000000,0x100,0x100000000,0x10,0x1000000,0x10,0x10000,0x10000,1,0x10000000,0x100,0x10,
  0x10,1,0x10000000,1,0x100000000,0x100000,0x100000,0x10000,0x100000000,0x300050000,0x200000003,0x4003,
  0x520000100,0x406200000],
   fromTable #[
  0x100000000,0x100000000,0x1000,0x1000,0x100,0x100,0x10000000,0x1000,0x10000,0x10000000,0x100,0x10000000,
  0x100000000,1,0x100,0x10,0x1000,0x10000,0x100000,0x1000000,1,0x100000000,0x300000400,0x30000002,
  0x400060000,0x301000004,0x260000030],
   fromTable #[
  0x10,0x1000000,1,0x100000000,0x100000,0x10000000,0x1000000,1,0x1000,0x1000000,1,0x10,0x100000000,
  0x10000,0x100,0x10000,0x100,0x10000,0x100000000,0x1000,1,0x100000,0x10,0x10000,0x1000000,1,0x10000000,
  0x100000000,0x100000000,0x1000,0x10000,0x100000000,0x1000,0x100000000],
   fromTable #[
  0x1000,0x1000,0x10000,0x100000000,0x100000,0x100000,0x10000000,0x10,0x1000,0x100000,0x100000000,
  0x100000000,0x1000,0x10000000,0x100000000,0x10000,0x10000,0x1000000,0x10000000,0x100000000,0x100,
  0x10000000,0x1000000,0x10,0x1000000,0x1000000,0x10000,0x1000000,1,0x10,0x100,0x100,0x10000000,0x10],
   fromTable #[
  0x100,0x100000,0x10,0x1000000,0x10000000,0x1000,0x100000,0x10,0x10000000,0x10,0x1000000,0x10000000,
  0x100000000,1,0x1000000,0x1000000,0x100000,0x100,0x100000000,0x1000,1,0x10000000,0x100000000,0x100000,
  0x100000000,0x100000000,0x100000,0x100000,0x100000000,0x10000000,0x100000000,0x10000,0x100000000,
  0],
   fromTable #[
  0x1000000,0x1000000,0x100,0x100,0x100,1,0x100000000,0x10000,0x10,0x100000,0x100000000,0x100000000,
  0x100000000,0x1000000,1,0x10,0x1000,1,0x10000,0x1000000,0x100000,0x1000,0x100000,0x10,1,0x1000,0x100,
  1,0x10000000,0x1000000,0x100,0x100000,0x1000000,0],
   fromTable #[
  0x100000000,0x10,0x1000,0x1000000],
   fromTable #[
  0x100000,0x10,0x100,0x10000],
   fromTable #[
  0x10000,1,0x100000,0x100000000]⟩

def seq : Array ℕ := #[
  242,323,140,206,287,215,296,233,314,251,170,260,179,269,188,278,197,368,224,305,17,3,2,9,11,10,167,
  13,12,55,54,189,246,68,69,71,318,70,8,16,315,279,198,86,87,310,91,248,90,207,288,109,108,216,297,
  132,133,228,309,277,196,134,229,135,286,205,136,137,295,165,7,239,154,155,316,34,35,5,6,19,32,50,
  72,73,128,130,142,150,151,152,153,163,166,168,214,230,234,235,236,237,238,240,241,249,252,270,317,
  319,320,321,322,4,14,15,18,22,23,33,42,43,51,58,59,78,79,102,103,112,113,116,117,124,125,129,131,
  143,164,171,174,177,184,190,194,199,200,204,219,221,223,254,256,257,261,266,267,276,284,289,290,
  291,292,294,298,299,307,308,312,1,126,127,169,173,175,176,178,180,181,183,185,186,187,191,193,195,
  201,203,208,209,210,211,213,217,218,220,225,226,227,231,244,245,247,255,258,259,265,268,271,275,
  280,281,285,300,302,304,306,311,20,21,80,81,100,101,160,161,192,202,212,222,88,89,158,24,25,28,29,
  30,31,38,39,262,44,45,46,47,52,56,57,62,63,274,282,64,65,74,75,82,83,84,85,301,94,95,98,99,106,114,
  115,118,119,122,146,148,149,76,77,156,250,264,272,145,325,40,41,60,61,105,120,121,123,141,144,159,
  162,172,182,243,273,283,293,303,313,324,332,333,352,353,26,27,37,66,67,96,97,138,330,331,363,349,
  348,104,0,232,346,359,36,360,48,92,139,253,263,336,365,326,327,110,338,342,343,358,364,350,351,107,
  93,147,111,337,345,366,340,344,356,334,335,339,341,357,354,361,329,347,355,362,367,328,53,49,157]

def back : Array ℕ := #[
  320,167,22,21,111,77,78,70,38,23,25,24,28,27,112,113,39,20,114,79,216,217,115,116,231,232,306,307,
  233,234,235,236,80,117,75,76,324,308,237,238,281,282,118,119,240,241,242,243,326,367,81,120,244,
  366,30,29,245,246,121,122,283,284,247,248,251,252,309,310,33,34,37,35,82,83,253,254,273,274,123,
  124,218,219,255,256,257,258,43,44,228,229,48,46,327,344,260,261,311,312,262,263,220,221,125,126,
  319,285,264,343,52,51,335,346,127,128,265,266,129,130,267,268,286,287,269,288,131,132,168,169,84,
  133,85,134,55,56,61,63,66,67,313,328,2,289,86,135,290,279,270,345,271,272,87,88,89,90,72,73,275,
  368,230,291,222,223,292,91,136,69,92,26,93,170,10,137,293,171,138,172,173,139,174,12,175,176,294,
  177,140,178,179,180,14,31,141,181,224,182,142,183,60,16,42,143,144,184,225,185,145,65,3,49,186,187,
  188,189,226,190,94,5,53,191,192,146,193,147,227,148,18,194,195,196,57,62,95,197,321,7,96,97,98,99,
  100,71,101,102,0,295,198,199,32,200,47,103,276,9,104,329,149,201,150,151,202,203,11,152,239,330,
  277,204,153,154,205,13,105,206,278,296,249,207,155,59,15,41,208,209,250,297,156,210,64,4,50,157,
  158,159,160,298,161,68,6,54,162,163,211,259,212,299,213,19,214,164,165,58,45,215,166,300,8,40,74,
  106,36,107,108,109,110,1,301,280,333,334,365,360,314,315,302,303,353,354,331,347,336,355,350,356,
  337,338,351,348,322,361,318,317,341,342,304,305,358,362,352,357,339,323,325,359,363,316,340,332,
  349,364,17]

def order : Fin 369 ≃ Rows := ordering seq back (by decide +kernel) (by decide +kernel)

def cert : Array ℕ := #[
  0x812,0xa16a059728c67fd,0x99f98a91c,0xa048e24ca,0xd3,0x127,0x151,0x16d,0xa16499,0xa119717ef,0xa11a069738c1,
  0,0x9b,0xa04a019f39e58cf,0x8b3,0x10b,0xb0,0xc5,0xa165db,0x112,0xa11a0683c,0xa14a047a2492,0,0xa15a0893f93d56b,
  0xa14a04872572,0xe1,0xa16a05944579,0xb7,0xa15a0a9af98c,0xa12a037924a7,0x40,0xa11a0aa03a019d7900,
  0x94,0,0x683,0x6c06b4,0x6f86ec,0x969,0x977,0xa16a0aa01931,0x971763,0,0xa12a03944938,0xa16a0fa089fc9d2,
  0x68a,0x659,0x86b85f,0x66c660,0x67a66e,0xa0aa019c99a1,0x207,0x99a,0xa11a0ba03a019fa989923,0xa15a079728e4,
  0x804,0x98a4ae,0x6c0580,0x86b4b5,0x66c4bc,0x97797392f587,0xa11a0ba03a019fa4c3,0x4e,0xa0fa079fc9ee,
  0xa16a057a9,0x985,0,0x89e,0x784778,0x724,0x97e,0xa14a0f9fc,0x77576a,0xa0fa079fc9ee907,0xa13a0786d,
  0x68867c,0,0x89e79b,0x698,0x6ab69f,0xa16a0f8eb,0xa11a0f9fc9c4,0xa146ad,0x7b0,0x7b7,0xa078dd,0x6884d1,
  0xa0aa04a019f390c80b,0x8aa4d8,0x784595,0x6ab4df,0xa0f4e6,0xa0da059fd9ef9de4ed,0x5c,0x8ac,0x1e4,0x65e652,
  0x8a5,0,0x6d7,0x88e882,0x74c740,0x182,0xa14a049c2993,0x8a3897,0xcc,0x6bb,0x8a5794,0,0x6ce6c2,0x6ea6de,
  0x880874,0xe8,0xf6,0x7be,0x7c5,0xda,0x65e5a3,0x8a34f4,0x8b1819,0x6ce4fb,0x88e5aa,0x880502,0x19e,
  0x6a,0xa11a06960954,0xa2,0x866,0x69d691,0x6c9,0,0x732,0x716,0x1ac,0xa079bd,0,0xa11a0693f,0x6f3,0x77f,
  0x6d0,0xa16a0594d,0x7066fa,0x714708,0x12e,0x771,0x843,0x84a,0x120,0x8668645b1,0x69d5b8,0x6dc509,
  0x95b959952820,0x706510,0x9605bf,0x1c1,0x16,0,0xa9,0x667,0x6a6,0x6e5,0x701,0xa12a0ca049ec9b49a8,
  0x75a74e,0x1cf,0x1f2,0xa15a0da079e7971915,0x143,0x97096e8f2,0x72971d,0x889,0x73772b,0,0xa15a0da079e7,
  0x9718ba,0x972739,0x851,0x858,0x158,0x96e517,0x72951e,0x889887525,0x73752c,0x827,0x9b4533,0x1dd,
  0x24,0xa13a0da049ec9cb,0xbe,0x675,0xa0a,0x87b,0x70f,0x9af,0,0xa15890,0xa12786,0x98397c90e,0x166,
  0x97c97292a,0xa0a9e0,0x747,0x95b,0x755,0,0x97575c,0xa13973946,0x7d3,0x7da,0x174,0x97c53a,0x983541,
  0x87b8795c6,0x71b548,0xa12a0ca049ec5cd,0xa14a0ca079e79d082e,0xa16a048fe5d4,0x78,0x835,0xa15a0878d,
  0xa16a0ea089fc9f5,0xa0ca06a009f29d9,0xef,0x135,0x9638bb7cc,0x9709677e1,0xa12a0f9fc9bb7e8,0xa14a049759657f6,
  0xa15a0aa019b68c8,0xa15a084a0,0xa16a0ea089fc9f558e,0xa0ca06a009f29d959c,0x189,0x1ba,0x1d6,0xa11a078f9,
  0,0xa129729468d6,0xf,0xa15a0aa019b6,0xa1154f,0xa11a0f9fc936556,0xa13a0aa0155d,0x190,0x13c,0x9748bf5e2,
  0xa12895564,0,0x32,0xa1497494b396,0xa1396394639d,0xa1125b,0xa0397394b8db3b2,0x8aa8a37a033b,0x8a88a279f342,
  0xa13a079bd998262,0xa12a039bf996269,0x98a68f326,0x98968f32d,0xa0f9e598337a,0xa0a9e0982381,0xa0f9fc9c49a6231,
  0xa11a0aa039fa9c49a6334,0x6dc6d535e,0x6da6d2365,0xa11a069528485f7,0xa14a0494f84f5fe,0xa1197064f5e0311,
  0xa11a067a6792318,0xa13a0aa01254,0xa16a0fa059ef9de5a13ab,0xa16a0aa019c9238,0xa15a0fa059ef9de9c8349,
  0x20e,0x215,0xa15a0899a98593f93d92131f,0xa15a0893f93d22a,0xa11a049fc9ee9e08d47ae30a,0xa12a037ad21c,
  0xa11a0f9fc93624d,0xa12a0aa039fa9365933a4,0x8b8223,0x1eb,0xa049c2270,0xa039bf277,0xa15a0da079e79af9ad856605,
  0xa14a0fa069eb9b39a985d60c,0xa12a0ca049ec9b436c,0xa13a0aa059e89af373,0xa16a0594423f,0xa13a07941246,
  0xa16975772641613,0xa15a0897196777164861a,0x77663d,0x773644,0x97264b,0xa14a047a2,0x104,0x8d,0xa11,
  0xa12a03,0x970,0x974962,0x6bb6596575853c7,0x8808747477455cb3ff,0xa11a0693f57e285,1,0x9af9ad97491a82c62f,
  0x9718ba5e729a,0xa11a079759628f97e65d940d,0xa12a0394493857027e,0x8ac89e89c81e621,0xa15a0da079e77557535d2406,
  0x47,0x55,0xa13a079bd9982b6,0x1c8,0x63,0x96095494d825628,0x77f69869659a3d5,0x95b7145c43f8,0xa13a079709647fb2cb,
  0x71,0xa14a0486d7ae5773b9,0x9668be7d1293,0x97c97292a67a58c3ce,0x86b85f6f36f15b63ea,0xa13a0da049ec9cb97e977913833636,
  0xa12a0f9b499128c,0x1b3,0xa1578b2c4,0xa169747f42a1,0x6bb6b96595a83dc,0x77f77d6985bd3f1,0x77276f2af,
  0x1a5,0x9747682a8,0x9e54eb437,0x9af75a538468,0x9856836814b3414,0xa11a0a97e8f0546476,0xa139c9562484,
  0x8b82e0,0x2b,0x8666f84ba41b,0xa169c49a693155b47d,0x9759698f76674c1422,0x86,0x39,8,0xa12a0f9b49912d2,
  0x17b,0x97767567353f46f,0x88e8826e56e352a45a,0x9fc9ee9e08e28d4429,0x7762ee,0x87b74c50743e,0x14a,
  0x197,0x97373e2f5,0x96966766551c44c,0x119,0xfd,0x7246a66a4523453,0x15f,0xa1597394b8db303,0xa1597089076156948b,
  0xa136b22e7,0x732730701515445,0xa1497294b2fc,0,0x7327016ff531461,0xa049c22bd,0x1f9,0x200,0xa12a049738e92d9,
  0xa12a0499a9859739218e93c0,0xa11a0aa03a019d799f5e9,0xa0f9f59d79869285f0,0x7247226a64e4430,0x8896ea5af3e3,
  0x8aa8a3799350,0x8a88a2797357,0x1d,0x7f,0x96071b388,0x95b71838f]

def B (j : Cols 34 4) : Packed := unpack 10 (cert[colNumber j]?.getD 0)

end Data12

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
lemma spans12 : ∃ f : Factors ℂ 34 4, Function.Surjective (matrix f).mulVec := by
  apply certified Data12.factors Data12.B Data12.order
  decide +kernel

end TensorRankThreeFactor.RegularDiagonal

namespace TensorRankThreeFactor.RegularDiagonal
namespace Data15

open TensorRankColumnReduction TensorRankThreeFactor.FastBase

def factors : Factors ℕ 45 0 :=
  ⟨atSide,atSide,atSlopes,
fromTable #[
  1,0x1000000,0x1000000,0x100,0x10,0x100000000,1,0x100,0x100000,0x100000000,0x100000000,0x10000,0x1000,
  0x10000000,0x100000,0x1000000,0x10000,0x1000000,0x10000,0x10,0x10000000,0x200010000,0x200030,0x400003000,
  0x440000000,0x200000600,0x30004],
   fromTable #[
  0x1000,0x1000000,0x100000000,0x1000,1,0x10000,1,1,0x1000,0x100000000,0x10,0x10000,0x10000000,0x100000000,
  0x100,0x1000,0x1000000,0x100,0x10,0x10,0x100000,0x40005000,0x400030000,0x400300000,0x604,0x503000000,
  0x401000000],
   fromTable #[
  0x1000,1,0x1000000,0x100000000,0x10000000,0x10000000,0x100000,0x100,0x100,1,0x10000,0x100,1,0x10,
  0x1000000,0x10000000,0x1000000,1,0x100000000,0x10,0x10,0x10,0x100000000,1,0x100000,0x1000,0x100000000,
  0x10000,0x100000000,0x1000000,0x1000,0x1000000,0x100000,0x10,0x100,0x10,0x100,0x100,0x100000,0x100000000,
  0x100000000,0x100000000,0x100000000,0,0],
   fromTable #[
  0x100000,0x10,1,0x10,0x10000000,0x10000,0x1000,0x1000000,0x100000,0x100000,0x100000,0x10000000,0x10000000,
  0x100000000,0x100000000,0x100,0x10000000,1,0x10000000,0x1000000,1,0x1000,0x100000,0x10000,0x10,0x10000,
  1,0x100000000,0x10000,0x10,0x10000000,0x1000,0x10000000,0x100000,0x100000000,0x100,0x10,0x10000,
  1,0x1000000,0x100000000,0x1000,0x100,0,0],
   fromTable #[
  0x1000,1,0x10000,0x100000000,0x10000,0x100,0x10000,0x10000,0x100000000,0x100000000,0x100000,0x100000,
  0x1000,0x10000000,0x100000000,0x10000000,0x100000,0x100,0x10000,0x10000000,0x100000000,0x100000,
  0x1000,0x10,0x10,0x1000,0x100000000,0x1000000,0x10,0x100000,1,0x10000000,0x10000000,0x10000000,0x1000000,
  1,0x100000000,0x10000,0x100000000,0x100000000,0x10000,1,0x100000000,1,0],
   fromTable #[
  0x100000,0x100000000,0x1000000,0x100000000,0x10000000,0x1000,0x10000,0x1000,0x1000000,0x100000,0x100000000,
  0x1000000,0x10,0x1000000,0x10000,0x1000,0x10000,0x10000000,1,0x100000000,0x1000,0x100000,0x100,0x10000000,
  0x10,0x100000000,0x10000000,0x10000,0x100000000,0x100,0x1000000,0x100000,0x10,1,0x100000,0x1000,
  0x10,0x100,1,0x100,0x1000000,0x10,1,0x100000000,0],
   fromTable #[
  ],
   fromTable #[
  ],
   fromTable #[
  ]⟩

def seq : Array ℕ := #[
  142,242,323,14,15,140,170,197,278,215,296,233,314,269,188,287,206,305,224,368,179,260,17,145,127,
  250,169,158,3,2,252,5,4,164,261,180,9,8,11,10,288,13,168,32,33,178,50,51,308,55,54,189,270,73,72,
  198,279,247,166,86,310,89,319,88,12,16,297,91,90,207,248,167,104,105,109,249,108,216,122,123,128,
  129,259,226,307,132,133,228,277,134,229,135,138,139,231,312,304,223,149,236,148,126,144,234,225,
  306,130,227,131,150,237,151,87,159,241,205,286,245,36,37,338,136,230,311,356,68,309,1,6,7,19,69,
  124,125,137,143,146,147,152,153,163,171,187,196,214,235,238,239,240,246,251,268,315,316,317,318,
  320,321,322,18,42,43,74,75,84,85,94,95,96,97,112,113,114,115,160,161,173,174,176,177,181,184,185,
  186,193,194,203,208,210,217,219,244,264,271,272,275,281,282,290,292,294,301,302,165,175,183,190,
  191,195,199,200,201,204,209,211,213,218,220,221,254,255,257,258,262,265,266,267,274,284,289,291,
  295,298,300,325,0,20,21,80,81,120,121,162,232,253,283,285,293,34,35,52,53,70,71,22,23,24,25,28,29,
  30,31,38,39,44,45,46,47,58,59,62,63,82,83,92,93,102,103,106,107,26,27,256,280,110,111,116,117,118,
  119,154,155,64,65,156,157,358,359,48,49,299,276,340,341,343,40,41,60,61,100,352,101,353,141,339,
  172,182,192,202,212,222,243,360,313,367,357,327,342,365,56,57,344,361,66,67,330,331,273,76,77,78,
  79,348,349,98,99,364,350,351,363,328,329,263,362,324,346,347,332,333,366,303,334,335,336,354,337,
  355,326,345]

def back : Array ℕ := #[
  235,127,29,28,32,31,128,129,37,36,39,38,64,41,3,4,65,22,159,130,236,237,254,255,256,257,280,281,
  258,259,260,261,43,44,248,249,118,119,262,263,305,306,160,161,264,265,266,267,298,299,46,47,250,
  251,50,49,329,330,268,269,307,308,270,271,292,293,333,334,125,131,252,253,54,53,162,163,338,339,
  340,341,238,239,272,273,164,165,59,112,63,61,68,67,274,275,166,167,168,169,344,345,309,311,276,277,
  72,73,278,279,76,74,284,285,170,171,172,173,286,287,288,289,240,241,78,79,132,133,101,24,80,81,106,
  108,85,86,89,91,121,134,92,93,5,313,0,135,102,23,136,137,100,98,109,111,138,139,290,291,294,295,
  27,113,174,175,242,140,33,203,58,71,42,26,6,141,315,176,177,204,178,179,45,20,35,180,316,205,181,
  182,183,142,14,51,206,207,317,184,185,208,143,7,55,209,210,211,318,186,212,115,16,69,187,213,188,
  214,319,215,144,9,77,189,216,190,217,218,320,97,18,104,83,107,87,90,122,94,243,11,103,145,99,110,
  146,147,148,114,1,321,191,117,149,57,70,75,25,150,30,244,219,220,282,221,222,82,21,34,223,352,192,
  224,225,226,151,13,52,193,194,337,227,195,301,88,8,56,283,196,197,245,228,246,116,15,40,229,198,
  230,199,247,200,231,10,66,232,300,233,201,202,360,96,17,105,84,48,126,60,123,95,323,12,152,153,154,
  155,62,156,157,158,2,354,234,367,326,350,351,335,336,357,358,361,362,363,365,120,314,302,303,327,
  304,331,368,355,356,342,343,347,348,310,312,364,366,124,325,296,297,322,332,353,349,346,328,359,
  324,19]

def order : Fin 369 ≃ Rows := ordering seq back (by decide +kernel) (by decide +kernel)

def cert : Array ℕ := #[
  0x8c8,0x9af,0xa11a0a,0xf6,0x15f,0x17b,0x1dd,0x215,0x2c4,0x2cb,0x8cf,0,0xcc,0xe1,0x16d,0x104,0x112,
  0x1c1,0x16,0x1c8,0x99d8f2,0x99d667,0,0x915,0xe8,0x99f58e,0x190,0x1eb,0x127,0xb0,0x2b,0,0xc5,0,0x73772b,
  0x90c900,0x7be,0x78b77f,0x7d17c5,0x231,0x84f843,0,0x99c851,0xa11,0x6fa,0x70d701,0x7b57a9,0x716,0x724,
  0x12e,0x7a2,0xa1690e,0x8eb,0xd3,0x89e,0x7375fe,0x90c605,0x7b5595,0x78b60c,0x7d1613,0x13c,0x86,0x9a1,
  0xda,0x6ff6f3,0,0x75c,0x94b93f,0x9a8,0x835,0x2e7,0x2af,0x99a993,0x334,0x732,0,0x96795b,0x745739,
  0x753747,0x833827,0x143,0x812,0x858,0x85f,0xef,0x6ff61a,0x99f9988a5,0x99a99159c,0x94b621,0x9c2628,
  0x9bd9bb62f,0x8dd,0x5c,0x938,0x99a,0x708,0x99f98c,0,0x95994d,0x9e7,0xa03,0x254,0x2fc,0x92a,0x158,
  0x907,0x761755,0,0x76f763,0x804,0x92891c,0x365,0x7f6,0x866,0x86d,0x166,0x9079055a3,0x7615aa,0x92f8ac,
  0x959636,0x9bd9708f9,0x9285b1,0x269,0x32,0x977,0xfd,0x7b0,0x740,0x76a,0,0x975969,0x7da,0x270,0x84a,
  0x9d09c4,0x174,0x7b7,0x946,0x954,0,0x77d771,0xa039f5,0x19e,0x1ac,0x97e,0x985,0x182,0x7c35b8,0x9469445bf,
  0x9549525c6,0x9cb9c98b3,0x97563d,0x9d05cd,0x326,0x6a,0x87b,0x10b,0x71b70f,0x74e,0x8097fd,0x778,0,
  0x7e8,0x349,0x7f67ef,0x9ec9e0,0x1d6,0x786,0x9bd,0x962,0x970,0,0x79978d,0x1f9,0x7a479b,0x874,0x882,
  0x119,0x71b644,0x9ad5d4,0x80964b,0x97096e5db,0x9e79e58ba,0x7995e2,0x88e652,0x40,0x9d2,0x120,0x72971d,
  0x82e,0x923,0x9cb,0x794,0,0x285,0x81480b,0x9d9,0x207,0x7cc,0x9c29b6,0x92383c,0x7df7d3,0x7ed7e1,0,
  0x223,0x819,0xa089ee,0xa069fc,0x1cf,0x729659,0x83a5e9,0x923921660,0x7df5f0,0x7ed5f7,0x9de8c1,0x2a1,
  0x78,0x8d6,0x1d,0x135,0x14a,0x931,0x311,0x200,0x22a,0x8e9890,0x318,0x897,0xa9,0x238,0x2f5,0x25b,
  0x27e,0x889,0x28c,0,0x820,0x24,0x8e4,0x2d9,0x246,0x151,0x262,0x1a5,0x357,0x293,0,0x4e,0x99f381,0x99d388,
  0xa039f3691,0xa05a01698,0x81e39d,0x8193a4,0x99a991962960461,0x99c98f96395f468,0xa16a0f99d85645a,
  0x99d85638f,0x84f3c7,0x84c3ce,0x9b499c8f766e,0x99c66c37a,0x33b,0x342,0x9ec967499,0x9ea9634a0,0x8167fb6e96da4c3,
  0x8147f96f06e14ca,0x84a8483b9,0x84a8483c0,0x983683,0x98a68a,0x36c,0x936396,1,0x8253b2,0x9c29ad48b,
  0x9be9ac492,0xa089288414b5,0xa0692383c4bc,0xa089fa9d047d,0xa059f79cb484,0x9bd9bb83a4a7,0x9c29b68394ae,
  0x7c37bc46f,0x7c37b9476,0x913675,0xa168f067c,0x350,0x88e3ab,0xbe,0x30a,0x7a56c9,0x7a56d0,0x7f96e5,
  0x7fa6ec,0x2bd,0xa2,0x8146d7,0x8176de,0x1ba,0x9b,0x9c29758fe804802510,0x91a3d5,0x21c,0x84a8483f8,
  0x8e489c8956a6,0x277,0x9ec804650525,0x9c29b6833634502,0x9bd75362d4fb,0x1f2,0x97077d642517,0x8e23e3,
  0xb7,0x8d,0x7f,0x2ee,0x2a8,0x9b48d469f,0x31f,0x7cc7247226184e6,0xa16a0f3dc,0x90770d60a4d8,0x7fb7f4406,
  0x197,0x78678471664951e,0x95476f63b509,0x2d2,0x71,0x84f3ff,0x7cc7ca72465e52c,0x9363ea,0xa0892891c665533,
  0x8896573f1,0x7867167146114df,0x63,0x7326fa6f86034d1,0x7327306fa61f4ed,0x9467456264f4,0x1e4,0x81581040d,
  8,0x303,0x2b6,0,0,0x9c29759678fe556,0x41b,0x9cb7da7d86bb,0xf,0x32d,0x99f98c75c75a5a1541,0x9d09c497c8b86b4,
  0x95994d76a7685cb564,0x81e44c,0x7a57a0445,0x47,0x7e87e67945e7579,0x90c9007087065a8548,0x29a,0x1b3,
  0x373,0x9759697787765e0572,0x8e2422,0x189,0x55,0x7fb43e,0x9ec9e08bf8806c2,0x96296075c5af54f,0x23f,
  0xa168a36ad,0x39,0x825453,0xa089fa7da5f5580,0x94,0x9a874e74c5d956b,0x20e,0x35e,0x24d,0x2e0,0x7e87947925fc587,
  0x99a593414,0x7a7430,0x94b93f74073e5c455d,0x429,0x817437,0,0x99d91a85653a,0,0,0]

def B (j : Cols 45 0) : Packed := unpack 6 (cert[colNumber j]?.getD 0)

end Data15

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
lemma spans15 : ∃ f : Factors ℂ 45 0, Function.Surjective (matrix f).mulVec := by
  apply certified Data15.factors Data15.B Data15.order
  decide +kernel

end TensorRankThreeFactor.RegularDiagonal

namespace TensorRankThreeFactor.RegularDiagonal

/-- Pad an interior factor by zero on the outer coordinates of the axis. -/
def pad {K O : Type} [Zero K] (a : D → K) : O ⊕ D → K := Sum.elim (fun _ => 0) a

lemma ab_xyz {K : Type} [CommSemiring K] (a b : D → K) (h : Fin 2) (r : Rows) :
    ab a b h r = if Sum.inl h=(xyz r).2.2 then pad a (xyz r).1*pad b (xyz r).2.1 else 0 := by
  rcases r with ⟨i,j,k⟩|⟨i,k⟩|⟨j,k⟩|⟨i,k⟩|⟨j,k⟩|k <;> simp [ab,xyz,pad]

lemma ac_xyz {K : Type} [CommSemiring K] (a c : D → K) (h : Fin 1) (r : Rows) :
    ac a c r = if Sum.inl h=(xyz r).2.1 then pad a (xyz r).1*pad c (xyz r).2.2 else 0 := by
  have hh : h=0 := Subsingleton.elim _ _
  subst h
  rcases r with ⟨i,j,k⟩|⟨i,k⟩|⟨j,k⟩|⟨i,k⟩|⟨j,k⟩|k <;> simp [ac,xyz,pad]

lemma bc_xyz {K : Type} [CommSemiring K] (b c : D → K) (h : Fin 1) (r : Rows) :
    bc b c r = if Sum.inl h=(xyz r).1 then pad b (xyz r).2.1*pad c (xyz r).2.2 else 0 := by
  have hh : h=0 := Subsingleton.elim _ _
  subst h
  rcases r with ⟨i,j,k⟩|⟨i,k⟩|⟨j,k⟩|⟨i,k⟩|⟨j,k⟩|k <;> simp [bc,xyz,pad]

/-- Mixed coordinates retain at least one inner and one outer factor. -/
def Mixed : S × S × T → Prop
  | (.inl _,.inl _,.inl _) => False
  | (.inr _,.inr _,.inr _) => False
  | _ => True

def fromMixed : (r : S × S × T) → Mixed r → Rows
  | (.inl _,.inl _,.inl _), h => h.elim
  | (.inr _,.inr _,.inr _), h => h.elim
  | (.inr i,.inr j,.inl h), _ => .inl (i,j,h)
  | (.inr i,.inl _,.inr k), _ => .inr (.inl (i,k))
  | (.inl _,.inr j,.inr k), _ => .inr (.inr (.inl (j,k)))
  | (.inr i,.inl _,.inl h), _ => .inr (.inr (.inr (.inl (i,h))))
  | (.inl _,.inr j,.inl h), _ => .inr (.inr (.inr (.inr (.inl (j,h)))))
  | (.inl _,.inl _,.inr k), _ => .inr (.inr (.inr (.inr (.inr k))))

lemma mixed_xyz (r : Rows) : Mixed (xyz r) := by
  rcases r with ⟨i,j,k⟩|⟨i,k⟩|⟨j,k⟩|⟨i,k⟩|⟨j,k⟩|k <;> trivial

def rowsEquiv : Rows ≃ {r : S × S × T // Mixed r} where
  toFun r := ⟨xyz r,mixed_xyz r⟩
  invFun p := fromMixed p.val p.property
  left_inv r := by
    rcases r with ⟨i,j,k⟩|⟨i,k⟩|⟨j,k⟩|⟨i,k⟩|⟨j,k⟩|k <;> rfl
  right_inv := by
    rintro ⟨⟨i|i,j|j,k|k⟩,h⟩ <;> apply Subtype.ext <;>
      first | exact h.elim |
        simp only [fromMixed,xyz,Prod.mk.injEq,Sum.inl.injEq]
        repeat' constructor
        all_goals first | rfl | apply Subsingleton.elim

end TensorRankThreeFactor.RegularDiagonal

namespace TensorRankThreeFactor.RegularDiagonal.Transport

open Cyclic Construction

variable {m : ℕ} {q : Shape}

private def enc (g : Regular m) (b : ℕ) {r : ℕ} (u : Fin r) : Σ h : Group m, Fin (fiberSize b r h) :=
  ⟨g.val,Fin.cast (fiberSize_regular b r g).symm u⟩

private def get {b r : ℕ} [NeZero r] (u : Σ h : Group m, Fin (fiberSize b r h)) : Fin r :=
  Fin.ofNat r u.2.val

@[simp] private lemma get_enc (g : Regular m) (b : ℕ) {r : ℕ} [NeZero r] (u : Fin r) :
    get (enc g b u) = u := Fin.ext (Nat.mod_eq_of_lt u.isLt)

private lemma restore (g : Regular m) {b r : ℕ} [NeZero r]
    (u : Σ h : Group m, Fin (fiberSize b r h)) (h : u.1=g.val) : enc g b (get u)=u := by
  rcases u with ⟨v,u⟩
  dsimp only at h
  subst v
  unfold enc
  apply congrArg (Sigma.mk g.val)
  apply Fin.ext
  exact Nat.mod_eq_of_lt (lt_of_lt_of_eq u.isLt (fiberSize_regular b r g))

private def tag {O : Type} (g : Regular m) (b : ℕ) {r : ℕ} : O ⊕ Fin r → O ⊕ (Σ h : Group m, Fin (fiberSize b r h)) :=
  Sum.map id (enc g b)

private def untag {O : Type} {b r : ℕ} [NeZero r] : O ⊕ (Σ h : Group m, Fin (fiberSize b r h)) → O ⊕ Fin r :=
  Sum.map id get

@[simp] private lemma untag_tag {O : Type} (g : Regular m) (b : ℕ) {r : ℕ} [NeZero r] (u : O ⊕ Fin r) :
    untag (tag g b u)=u := by cases u <;> simp [tag,untag]

@[simp] private lemma tag_eq {O : Type} (g : Regular m) (b : ℕ) {r : ℕ} [NeZero r] (u v : O ⊕ Fin r) :
    tag g b u=tag g b v ↔ u=v := by
  constructor
  · intro h
    simpa only [untag_tag] using congrArg untag h
  · exact congrArg _

@[simp] private lemma outer_tag {O : Type} (g : Regular m) (b : ℕ) {r : ℕ} [NeZero r] (o : O) (u : O ⊕ Fin r) :
    Sum.inl o=tag g b u ↔ Sum.inl o=u := tag_eq g b (.inl o) u

private def rmap (g : Regular m) : Rows → R m q
  | .inl (i,j,k) => .inr (.inr (enc g q.d₀ i,enc g q.d₀ j,k))
  | .inr (.inl (i,k)) => .inr (.inl (enc g q.d₀ i,0,.inr (enc g (q.d₀-1) k)))
  | .inr (.inr (.inl (j,k))) => .inl (0,.inr (enc g q.d₀ j),.inr (enc g (q.d₀-1) k))
  | .inr (.inr (.inr (.inl (i,k)))) => .inr (.inl (enc g q.d₀ i,0,.inl k))
  | .inr (.inr (.inr (.inr (.inl (j,k))))) => .inl (0,.inr (enc g q.d₀ j),.inl k)
  | .inr (.inr (.inr (.inr (.inr k)))) => .inl (0,.inl 0,.inr (enc g (q.d₀-1) k))

private lemma rmap_xyz (g : Regular m) (r : Rows) :
    TensorRankThreeFactor.xyz (rmap (q:=q) g r) =
      (tag g q.d₀ (xyz r).1,tag g q.d₀ (xyz r).2.1,tag g (q.d₀-1) (xyz r).2.2) := by
  rcases r with ⟨i,j,k⟩|⟨i,k⟩|⟨j,k⟩|⟨i,k⟩|⟨j,k⟩|k <;> rfl

private lemma cover (g : Regular m) (r : R m q) (hr : Global.rowSector r={g.val}) :
    ∃ i, rmap g i=r := by
  have hraw : Global.raw r={g.val} := by
    by_cases he : Global.raw r=∅
    · simp [Global.rowSector,he] at hr
      exact (g.property hr.symm).elim
    · simpa only [Global.rowSector,if_neg he] using hr
  have eqg (k : Group m) (h : k ∈ Global.raw r) : k=g.val := Finset.mem_singleton.mp (hraw ▸ h)
  rcases r with ⟨a,b,k⟩|⟨a,b,k⟩|⟨a,b,k⟩
  · have ha : a=0 := Subsingleton.elim _ _
    subst a
    rcases b with b|b <;> rcases k with k|k
    · simp [Global.raw,TensorRankThreeFactor.xyz,Global.labels] at hraw
    · obtain rfl : b=0 := Subsingleton.elim _ _
      refine ⟨.inr (.inr (.inr (.inr (.inr (get k))))),?_⟩
      simp only [rmap,restore g k (eqg _ (by simp [Global.raw,TensorRankThreeFactor.xyz,Global.labels]))]
    · refine ⟨.inr (.inr (.inr (.inr (.inl (get b,k))))),?_⟩
      simp only [rmap,restore g b (eqg _ (by simp [Global.raw,TensorRankThreeFactor.xyz,Global.labels]))]
    · refine ⟨.inr (.inr (.inl (get b,get k))),?_⟩
      simp only [rmap,restore g b (eqg _ (by simp [Global.raw,TensorRankThreeFactor.xyz,Global.labels])),
        restore g k (eqg _ (by simp [Global.raw,TensorRankThreeFactor.xyz,Global.labels]))]
  · obtain rfl : b=0 := Subsingleton.elim _ _
    rcases k with k|k
    · refine ⟨.inr (.inr (.inr (.inl (get a,k)))),?_⟩
      simp only [rmap,restore g a (eqg _ (by simp [Global.raw,TensorRankThreeFactor.xyz,Global.labels]))]
    · refine ⟨.inr (.inl (get a,get k)),?_⟩
      simp only [rmap,restore g a (eqg _ (by simp [Global.raw,TensorRankThreeFactor.xyz,Global.labels])),
        restore g k (eqg _ (by simp [Global.raw,TensorRankThreeFactor.xyz,Global.labels]))]
  · refine ⟨.inl (get a,get b,k),?_⟩
    simp only [rmap,restore g a (eqg _ (by simp [Global.raw,TensorRankThreeFactor.xyz,Global.labels])),
      restore g b (eqg _ (by simp [Global.raw,TensorRankThreeFactor.xyz,Global.labels]))]

private def cmap (g : Regular m) : Cols q.edge (2*q.trade) → C m q
  | .inl (v,.inl i) => .inl (enc g q.d₀ v,.inl (tag g q.d₀ i))
  | .inl (v,.inr (.inl j)) => .inl (enc g q.d₀ v,.inr (.inl (tag g q.d₀ j)))
  | .inl (v,.inr (.inr k)) => .inl (enc g q.d₀ v,.inr (.inr (tag g (q.d₀-1) k)))
  | .inr (.inl (v,h)) => .inr (.normal g g v,.inr (.inr h))
  | .inr (.inr (.inl v)) => .inr (.right g v,.inr (.inl 0))
  | .inr (.inr (.inr (.inl v))) => .inr (.left g v,.inl 0)
  | .inr (.inr (.inr (.inr (v,h)))) => .inr (.trade g v,h)

private lemma inserted {O : Type} (g : Regular m) (b : ℕ) {r : ℕ} (u : O ⊕ Fin r) :
    insert g.val (Global.labels (tag g b u)) = {g.val} := by cases u <;> simp [tag,enc,Global.labels]

private lemma tagged (g : Regular m) (j : Cols q.edge (2*q.trade)) :
    Global.colSector axisA axisB axisC (cmap (q:=q) g j)={g.val} := by
  rcases j with ⟨v,h|h|h⟩|⟨v,h⟩|v|v|⟨v,h|h|h⟩ <;>
    simp only [cmap,Global.colSector,axisA,axisB,axisC,Finset.insert_eq_of_mem,Finset.mem_singleton_self,inserted,enc]

private def data (f : Factors ℂ q.edge (2*q.trade)) : RegDiagData q (D → ℂ) (D → ℂ) (D → ℂ) :=
  ⟨fun t => (f.triA t,f.triB t,f.triC t),fun t => (0,f.bcB t,f.bcC t),
    fun t => (f.acA t,0,f.acC t),fun t => (f.abA t,f.abB t,0)⟩

private def values (g : Regular m) (f : Factors ℂ q.edge (2*q.trade)) : Param m q → ℂ
  | .inl (t,.inl u) => f.a (get t) (untag u)
  | .inl (t,.inr (.inl u)) => f.b (get t) (untag u)
  | .inl (t,.inr (.inr u)) => f.c (get t) (untag u)
  | .inr (t,.inl u) => (regDiagFactors g (data f) 0 t).1 (get u)
  | .inr (t,.inr (.inl u)) => (regDiagFactors g (data f) 0 t).2.1 (get u)
  | .inr (t,.inr (.inr u)) => (regDiagFactors g (data f) 0 t).2.2 (get u)

@[simp] private lemma enc_group (g : Regular m) (b : ℕ) {r : ℕ} (u : Fin r) : (enc g b u).1=g.val := rfl

@[simp] private lemma xa_tag (g : Regular m) (f : Factors ℂ q.edge (2*q.trade)) (v : Fin 8) (u : S) :
    Global.xa (values g f) (enc g q.d₀ v) (tag g q.d₀ u)=f.a v u := by
  cases u <;> simp [Global.xa,Global.extra,tag,values,untag]

@[simp] private lemma xb_tag (g : Regular m) (f : Factors ℂ q.edge (2*q.trade)) (v : Fin 8) (u : S) :
    Global.xb (values g f) (enc g q.d₀ v) (tag g q.d₀ u)=f.b v u := by
  cases u <;> simp [Global.xb,Global.extra,tag,values,untag]

@[simp] private lemma xc_tag (g : Regular m) (f : Factors ℂ q.edge (2*q.trade)) (v : Fin 8) (u : T) :
    Global.xc (values g f) (enc g q.d₀ v) (tag g (q.d₀-1) u)=f.c v u := by
  cases u <;> simp [Global.xc,Global.extra,tag,values,untag]

private lemma na_pad (g : Regular m) (f : Factors ℂ q.edge (2*q.trade)) (t : Slot m q)
    (ht : axisA t=g.val) (u : S) :
    (tag g q.d₀ u).elim (fun _ => 0) (Global.na (values g f) axisA t) =
      pad (regDiagFactors g (data f) 0 t).1 u := by
  cases u <;> simp [tag,Global.na,Global.inner,values,ht,pad]

private lemma nb_pad (g : Regular m) (f : Factors ℂ q.edge (2*q.trade)) (t : Slot m q)
    (ht : axisB t=g.val) (u : S) :
    (tag g q.d₀ u).elim (fun _ => 0) (Global.nb (values g f) axisB t) =
      pad (regDiagFactors g (data f) 0 t).2.1 u := by
  cases u <;> simp [tag,Global.nb,Global.inner,values,ht,pad]

private lemma nc_pad (g : Regular m) (f : Factors ℂ q.edge (2*q.trade)) (t : Slot m q)
    (ht : axisC t=g.val) (u : T) :
    (tag g (q.d₀-1) u).elim (fun _ => 0) (Global.nc (values g f) axisC t) =
      pad (regDiagFactors g (data f) 0 t).2.2 u := by
  cases u <;> simp [tag,Global.nc,Global.inner,values,ht,pad]

private lemma entries (g : Regular m) (f : Factors ℂ q.edge (2*q.trade)) (r : Rows)
    (j : Cols q.edge (2*q.trade)) :
    Global.mat axisA axisB axisC (values g f) (rmap g r) (cmap g j) = matrix f r j := by
  rcases j with ⟨v,h|h|h⟩|⟨v,h⟩|v|v|⟨v,h|h|h⟩ <;>
    simp only [Global.mat,baseMatrix,rmap_xyz,cmap,matrix,extra,tag_eq,xa_tag,xb_tag,xc_tag,outer_tag]
  · rw [ab_xyz,na_pad g f (.normal g g v) rfl _,nb_pad g f (.normal g g v) rfl _]
    simp [regDiagFactors,data]
  · rw [ac_xyz _ _ 0,na_pad g f (.right g v) rfl _,nc_pad g f (.right g v) rfl _]
    simp [regDiagFactors,data]
  · rw [bc_xyz _ _ 0,nb_pad g f (.left g v) rfl _,nc_pad g f (.left g v) rfl _]
    simp [regDiagFactors,data]
  · rw [bc_xyz _ _ h,nb_pad g f (.trade g v) rfl _,nc_pad g f (.trade g v) rfl _]
    simp [regDiagFactors,data]
  · rw [ac_xyz _ _ h,na_pad g f (.trade g v) rfl _,nc_pad g f (.trade g v) rfl _]
    simp [regDiagFactors,data]
  · rw [ab_xyz,na_pad g f (.trade g v) rfl _,nb_pad g f (.trade g v) rfl _]
    simp [regDiagFactors,data]

/-- Every regular singleton group is covered by its nine-dimensional diagonal certificate. -/
lemma solved (m : ℕ) (q : Shape) (g : Regular m) : SolvedAt m q {g.val} := by
  have hs : ∃ f : Factors ℂ q.edge (2*q.trade), Function.Surjective (matrix f).mulVec := by
    cases q with
    | nine => exact spans9
    | twelve => exact spans12
    | fifteen => exact spans15
  obtain ⟨f,hf⟩ := hs
  exact ⟨values g f,Global.at_of_template axisA axisB axisC {g.val} (values g f)
    (matrix f) (rmap g) (cmap g) (cover g) (tagged g) (entries g f) hf⟩

end TensorRankThreeFactor.RegularDiagonal.Transport

namespace TensorRankThreeFactor.BaseDiagonal

open Cyclic Construction

private instance baseSizeNeZero (q : Shape) : NeZero q.d₀ := ⟨by cases q <;> decide⟩
private instance depthSizeNeZero (q : Shape) : NeZero (q.d₀-1) := ⟨by cases q <;> decide⟩

private def enc (m r : ℕ) {b : ℕ} (u : Fin b) : Σ h : Group m, Fin (fiberSize b r h) :=
  ⟨0,Fin.cast (fiberSize_zero b r).symm u⟩

private def get {m b r : ℕ} [NeZero b] (u : Σ h : Group m, Fin (fiberSize b r h)) : Fin b :=
  Fin.ofNat b u.2.val

@[simp] private lemma get_enc (m r : ℕ) {b : ℕ} [NeZero b] (u : Fin b) :
    get (enc m r u) = u := Fin.ext (Nat.mod_eq_of_lt u.isLt)

private lemma restore {m b r : ℕ} [NeZero b] (u : Σ h : Group m, Fin (fiberSize b r h))
    (h : u.1=0) : enc m r (get u)=u := by
  rcases u with ⟨g,u⟩
  dsimp only at h
  subst g
  unfold enc
  apply congrArg (Sigma.mk 0)
  apply Fin.ext
  exact Nat.mod_eq_of_lt (lt_of_lt_of_eq u.isLt (fiberSize_zero b r))

private def tag {O : Type} (m r : ℕ) {b : ℕ} : O ⊕ Fin b → O ⊕ (Σ h : Group m, Fin (fiberSize b r h)) :=
  Sum.map id (enc m r)

private def untag {O : Type} {m b r : ℕ} [NeZero b] :
    O ⊕ (Σ h : Group m, Fin (fiberSize b r h)) → O ⊕ Fin b := Sum.map id get

@[simp] private lemma untag_tag {O : Type} (m r : ℕ) {b : ℕ} [NeZero b] (u : O ⊕ Fin b) :
    untag (tag m r u)=u := by cases u <;> simp [tag,untag]

private lemma tag_restore {O : Type} {m r b : ℕ} [NeZero b]
    (u : O ⊕ (Σ h : Group m, Fin (fiberSize b r h))) (h : ∀ g ∈ Global.labels u, g=0) :
    tag m r (untag u) = u := by
  cases u with
  | inl u => rfl
  | inr u => exact congrArg Sum.inr (restore u (h _ (by simp [Global.labels])))

@[simp] private lemma tag_eq {O : Type} (m r : ℕ) {b : ℕ} [NeZero b] (u v : O ⊕ Fin b) :
    tag m r u=tag m r v ↔ u=v := by
  constructor
  · intro h
    simpa only [untag_tag] using congrArg untag h
  · exact congrArg _

@[simp] private lemma outer_tag {O : Type} (m r : ℕ) {b : ℕ} [NeZero b] (o : O) (u : O ⊕ Fin b) :
    Sum.inl o=tag m r u ↔ Sum.inl o=u := tag_eq m r (.inl o) u

private abbrev LocalR (q : Shape) := BaseRows (Fin q.d₀) (Fin (q.d₀-1))
private abbrev LocalC (q : Shape) := BaseCols (Fin q.d₀) (Fin (q.d₀-1)) (Fin q.d₀) (Fin (q.d₀*q.d₀/3))

private def rmap (m : ℕ) {q : Shape} : LocalR q → R m q
  | .inl (i,j,k) => .inl (i,tag m 9 j,tag m 9 k)
  | .inr (.inl (i,j,k)) => .inr (.inl (enc m 9 i,j,tag m 9 k))
  | .inr (.inr (i,j,k)) => .inr (.inr (enc m 9 i,enc m 9 j,k))

private lemma rmap_xyz (m : ℕ) {q : Shape} (r : LocalR q) :
    xyz (rmap m r) = (tag m 9 (xyz r).1,tag m 9 (xyz r).2.1,tag m 9 (xyz r).2.2) := by
  rcases r with ⟨i,j,k⟩|⟨i,j,k⟩|⟨i,j,k⟩ <;> rfl

private lemma cover (m : ℕ) {q : Shape} (r : R m q) (hr : Global.rowSector r={0}) :
    ∃ i, rmap m i=r := by
  have zero_at (g : Group m) (hg : g ∈ Global.raw r) : g=0 := by
    by_cases he : Global.raw r=∅
    · simp [he] at hg
    · have hh : Global.raw r={0} := by simpa [Global.rowSector,he] using hr
      exact Finset.mem_singleton.mp (hh ▸ hg)
  rcases r with ⟨i,j,k⟩|⟨i,j,k⟩|⟨i,j,k⟩
  · refine ⟨.inl (i,untag j,untag k),?_⟩
    rw [rmap,tag_restore j (fun g hg => zero_at g (by simp [Global.raw,xyz,hg])),
      tag_restore k (fun g hg => zero_at g (by simp [Global.raw,xyz,hg]))]
  · refine ⟨.inr (.inl (get i,j,untag k)),?_⟩
    rw [rmap,restore i (zero_at _ (by simp [Global.raw,xyz,Global.labels])),
      tag_restore k (fun g hg => zero_at g (by simp [Global.raw,xyz,hg]))]
  · refine ⟨.inr (.inr (get i,get j,k)),?_⟩
    rw [rmap,restore i (zero_at _ (by simp [Global.raw,xyz,Global.labels])),
      restore j (zero_at _ (by simp [Global.raw,xyz,Global.labels]))]

private def cmap (m : ℕ) {q : Shape} : LocalC q → C m q
  | .inl (t,.inl i) => .inl (enc m 8 t,.inl (tag m 9 i))
  | .inl (t,.inr (.inl j)) => .inl (enc m 8 t,.inr (.inl (tag m 9 j)))
  | .inl (t,.inr (.inr k)) => .inl (enc m 8 t,.inr (.inr (tag m 9 k)))
  | .inr (t,h) => .inr (.base t,h)

private lemma inserted {O : Type} (m r : ℕ) {b : ℕ} (u : O ⊕ Fin b) :
    insert (0 : Group m) (Global.labels (tag m r u))={0} := by cases u <;> simp [tag,enc,Global.labels]

@[simp] private lemma enc_group (m r : ℕ) {b : ℕ} (u : Fin b) : (enc m r u).1=0 := rfl

private lemma tagged (m : ℕ) {q : Shape} (j : LocalC q) :
    Global.colSector axisA axisB axisC (cmap m j)={0} := by
  rcases j with ⟨t,h|h|h⟩|⟨t,h|h|h⟩ <;>
    simp only [cmap,Global.colSector,axisA,axisB,axisC,enc_group,inserted,Finset.insert_eq_of_mem,Finset.mem_singleton_self]

private structure Factors (q : Shape) where
  a : Fin q.d₀ → Side (Fin q.d₀) → ℂ
  b : Fin q.d₀ → Side (Fin q.d₀) → ℂ
  c : Fin q.d₀ → Depth (Fin (q.d₀-1)) → ℂ
  ai : Fin (q.d₀*q.d₀/3) → Fin q.d₀ → ℂ
  bi : Fin (q.d₀*q.d₀/3) → Fin q.d₀ → ℂ
  ci : Fin (q.d₀*q.d₀/3) → Fin (q.d₀-1) → ℂ

private def values (m : ℕ) {q : Shape} (f : Factors q) : Param m q → ℂ
  | .inl (t,.inl i) => f.a (get t) (untag i)
  | .inl (t,.inr (.inl j)) => f.b (get t) (untag j)
  | .inl (t,.inr (.inr k)) => f.c (get t) (untag k)
  | .inr (t,.inl i) => (baseFactors (fun s => (f.ai s,f.bi s,f.ci s)) 0 t).1 (get i)
  | .inr (t,.inr (.inl j)) => (baseFactors (fun s => (f.ai s,f.bi s,f.ci s)) 0 t).2.1 (get j)
  | .inr (t,.inr (.inr k)) => (baseFactors (fun s => (f.ai s,f.bi s,f.ci s)) 0 t).2.2 (get k)

private lemma xa_tag (m : ℕ) {q : Shape} (f : Factors q) (t : Fin q.d₀) (u : Side (Fin q.d₀)) :
    Global.xa (values m f) (enc m 8 t) (tag m 9 u)=f.a t u := by
  cases u <;> simp [Global.xa,Global.extra,tag,values,untag]

private lemma xb_tag (m : ℕ) {q : Shape} (f : Factors q) (t : Fin q.d₀) (u : Side (Fin q.d₀)) :
    Global.xb (values m f) (enc m 8 t) (tag m 9 u)=f.b t u := by
  cases u <;> simp [Global.xb,Global.extra,tag,values,untag]

private lemma xc_tag (m : ℕ) {q : Shape} (f : Factors q) (t : Fin q.d₀) (u : Depth (Fin (q.d₀-1))) :
    Global.xc (values m f) (enc m 8 t) (tag m 9 u)=f.c t u := by
  cases u <;> simp [Global.xc,Global.extra,tag,values,untag]

private lemma na_tag (m : ℕ) {q : Shape} (f : Factors q) (t : Fin (q.d₀*q.d₀/3)) (u : Side (Fin q.d₀)) :
    (tag m 9 u).elim (fun _ => 0) (Global.na (values m f) axisA (.base t)) = u.elim (fun _ => 0) (f.ai t) := by
  cases u <;> simp [tag,Global.na,Global.inner,axisA,values]

private lemma nb_tag (m : ℕ) {q : Shape} (f : Factors q) (t : Fin (q.d₀*q.d₀/3)) (u : Side (Fin q.d₀)) :
    (tag m 9 u).elim (fun _ => 0) (Global.nb (values m f) axisB (.base t)) = u.elim (fun _ => 0) (f.bi t) := by
  cases u <;> simp [tag,Global.nb,Global.inner,axisB,values]

private lemma nc_tag (m : ℕ) {q : Shape} (f : Factors q) (t : Fin (q.d₀*q.d₀/3)) (u : Depth (Fin (q.d₀-1))) :
    (tag m 9 u).elim (fun _ => 0) (Global.nc (values m f) axisC (.base t)) = u.elim (fun _ => 0) (f.ci t) := by
  cases u <;> simp [tag,Global.nc,Global.inner,axisC,values]

private lemma entries (m : ℕ) {q : Shape} (f : Factors q) (r : LocalR q) (j : LocalC q) :
    Global.mat axisA axisB axisC (values m f) (rmap m r) (cmap m j)=baseMatrix f.a f.b f.c f.ai f.bi f.ci r j := by
  rcases j with ⟨t,h|h|h⟩|⟨t,h|h|h⟩ <;>
    simp only [Global.mat,baseMatrix,rmap_xyz,cmap,tag_eq,outer_tag,xa_tag,xb_tag,xc_tag,na_tag,nb_tag,nc_tag]

/-- The distinguished group's finite matrix includes the wholly outer corner. -/
lemma of_base (m : ℕ) (q : Shape) (hs : Base q.d₀ (q.d₀-1) q.d₀ (q.d₀*q.d₀/3)) :
    SolvedAt m q {0} := by
  obtain ⟨a,b,c,ai,bi,ci,h⟩ := hs
  let f : Factors q := ⟨a,b,c,ai,bi,ci⟩
  exact ⟨values m f,Global.at_of_template axisA axisB axisC {0} (values m f)
    (baseMatrix f.a f.b f.c f.ai f.bi f.ci) (rmap m) (cmap m) (cover m) (tagged m) (entries m f) h⟩

lemma solved (m : ℕ) (q : Shape) : SolvedAt m q {0} := by
  apply of_base
  cases q with
  | nine => exact Base10.spans
  | twelve => exact Base13.spans
  | fifteen => exact Base16.spans

end TensorRankThreeFactor.BaseDiagonal

namespace TensorRankThreeFactor.FinalPack

variable {D E X N : Type}

private def factor {O I : Type} (outside : X → O ⊕ I → ℂ) (inside : N → I → ℂ) :
    N ⊕ X → O ⊕ I → ℂ
  | .inl t => Sum.elim (fun _ => 0) (inside t)
  | .inr t => outside t

private def direction {O I : Type} (outside : X → O ⊕ I → ℂ) (inside : N → O → ℂ) :
    N ⊕ X → O ⊕ I → ℂ
  | .inl t => Sum.elim (inside t) (fun _ => 0)
  | .inr t => outside t

private def u (y : BaseCols D E X N → ℂ) :=
  direction (fun t i => y (.inl (t, .inl i))) (fun t i => y (.inr (t, .inl i)))
private def v (y : BaseCols D E X N → ℂ) :=
  direction (fun t j => y (.inl (t, .inr (.inl j)))) (fun t j => y (.inr (t, .inr (.inl j))))
private def w (y : BaseCols D E X N → ℂ) :=
  direction (fun t k => y (.inl (t, .inr (.inr k)))) (fun t k => y (.inr (t, .inr (.inr k))))

private lemma outer_sum {O I : Type} [Fintype O] [DecidableEq O] [DecidableEq I]
    (i : O ⊕ I) (c : ℂ) (f : O → ℂ) :
    (∑ o : O, if Sum.inl o = i then c * f o else 0) = c * i.elim f (fun _ => 0) := by
  cases i <;> simp

set_option maxHeartbeats 400000 in
private lemma action [Fintype D] [Fintype E] [Fintype X] [Fintype N] [DecidableEq D] [DecidableEq E]
    (a b : X → Side D → ℂ) (c : X → Depth E → ℂ) (ai bi : N → D → ℂ) (ci : N → E → ℂ)
    (y : BaseCols D E X N → ℂ) (r : BaseRows D E) :
    (baseMatrix a b c ai bi ci).mulVec y r =
      let (i,j,k) := xyz r
      ∑ t : N ⊕ X, (u y t i * (factor b bi t j * factor c ci t k) +
        factor a ai t i * (v y t j * factor c ci t k) +
        factor a ai t i * (factor b bi t j * w y t k)) := by
  generalize hp : xyz r = ijk
  obtain ⟨i,j,k⟩ := ijk
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
    baseMatrix, hp, u, v, w, direction, factor, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, outer_sum]
  rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro t _ <;> ring

private def axis {o d n : ℕ} (e : D ≃ Fin d) (h : d + o = n) : Fin o ⊕ D ≃ Fin n :=
  ((Equiv.sumComm _ _).trans (sumFin e (Equiv.refl _))).trans (finCongr h)

private lemma axis_inner {o d n : ℕ} (e : D ≃ Fin d) (h : d + o = n) (i : D) :
    (axis e h (.inr i)).val < d := (e i).isLt

private lemma extra_ge {s p : ℕ} (en : N ≃ Fin s) (ex : X ≃ Fin p) (t : X) :
    s ≤ (sumFin en ex (.inr t)).val := by
  change s ≤ s + (ex t).val
  omega

private def pull {P Q I J : Type} (p : P ≃ Q) (e : I ≃ J) (f : P → I → ℂ) (t : Q) (i : J) :=
  f (p.symm t) (e.symm i)

private lemma supported {s p o d n : ℕ} (en : N ≃ Fin s) (ex : X ≃ Fin p)
    (ed : D ≃ Fin d) (hd : d + o = n) (a : X → Fin o ⊕ D → ℂ) (ai : N → D → ℂ)
    (t : Fin (s+p)) (ht : t.val < s) (i : Fin n) (hi : d ≤ i.val) :
    pull (sumFin en ex) (axis ed hd) (factor a ai) t i = 0 := by
  obtain ⟨t,rfl⟩ := (sumFin en ex).surjective t
  obtain ⟨i,rfl⟩ := (axis ed hd).surjective i
  cases t with
  | inr t => exact (not_lt_of_ge (extra_ge en ex t) ht).elim
  | inl t =>
    cases i with
    | inr i => exact (not_lt_of_ge hi (axis_inner ed hd i)).elim
    | inl i => simp [pull, factor]

private def Packed (n d e s p : ℕ) : Prop :=
  ∃ a b c : Fin (s+p) → Fin n → ℂ,
    (∀ (t : Fin (s+p)), t.val < s → ∀ i : Fin n,
      (d ≤ i.val → a t i = 0 ∧ b t i = 0) ∧ (e ≤ i.val → c t i = 0)) ∧
    ∀ T : Fin n → Fin n → Fin n → ℂ, ∃ u v w : Fin (s+p) → Fin n → ℂ, ∀ i j k,
      (d ≤ i.val ∨ d ≤ j.val ∨ e ≤ k.val) →
        T i j k = ∑ t, (u t i * (b t j * c t k) + a t i * (v t j * c t k) +
          a t i * (b t j * w t k))

private lemma of_matrix [Fintype D] [Fintype E] [Fintype X] [Fintype N]
    [DecidableEq D] [DecidableEq E] {n d e s p : ℕ} (h₁ : d+1=n) (h₂ : e+2=n)
    (hD : Fintype.card D=d) (hE : Fintype.card E=e) (hX : Fintype.card X=p) (hN : Fintype.card N=s)
    (a b : X → Side D → ℂ) (c : X → Depth E → ℂ) (ai bi : N → D → ℂ) (ci : N → E → ℂ)
    (hm : Function.Surjective (baseMatrix a b c ai bi ci).mulVec) : Packed n d e s p := by
  classical
  let en := Fintype.equivFinOfCardEq hN
  let ex := Fintype.equivFinOfCardEq hX
  let ed := Fintype.equivFinOfCardEq hD
  let ec := Fintype.equivFinOfCardEq hE
  let pt := sumFin en ex
  let ab := axis ed h₁
  let cd := axis ec h₂
  refine ⟨pull pt ab (factor a ai), pull pt ab (factor b bi), pull pt cd (factor c ci), ?_, ?_⟩
  · intro t ht i
    exact ⟨fun hi => ⟨supported en ex ed h₁ a ai t ht i hi, supported en ex ed h₁ b bi t ht i hi⟩,
      supported en ex ec h₂ c ci t ht i⟩
  · intro T
    obtain ⟨y,hy⟩ := hm fun r => T (ab (xyz r).1) (ab (xyz r).2.1) (cd (xyz r).2.2)
    refine ⟨pull pt ab (u y), pull pt ab (v y), pull pt cd (w y), ?_⟩
    intro i j k h
    obtain ⟨i,rfl⟩ := ab.surjective i
    obtain ⟨j,rfl⟩ := ab.surjective j
    obtain ⟨k,rfl⟩ := cd.surjective k
    have hex : ∃ r : BaseRows D E, xyz r = (i,j,k) := by
      cases i with
      | inl i => exact ⟨.inl (i,j,k), rfl⟩
      | inr i =>
        cases j with
        | inl j => exact ⟨.inr (.inl (i,j,k)), rfl⟩
        | inr j =>
          cases k with
          | inl k => exact ⟨.inr (.inr (i,j,k)), rfl⟩
          | inr k =>
            rcases h with hi | hj | hk
            · exact (not_lt_of_ge hi (axis_inner ed h₁ i)).elim
            · exact (not_lt_of_ge hj (axis_inner ed h₁ j)).elim
            · exact (not_lt_of_ge hk (axis_inner ec h₂ k)).elim
    obtain ⟨r,hr⟩ := hex
    have hsum := (congrFun hy r).symm.trans (action a b c ai bi ci y r)
    rw [← pt.sum_comp]
    simpa only [hr, pull, Equiv.symm_apply_apply] using hsum

/-- A surjective cyclic exterior matrix in every shape gives the supported
configuration in each dimension required by the cubic exterior estimate. -/
theorem h2_of_global
    (h : ∀ (m : ℕ) (q : Cyclic.Shape), ∃ z : Construction.Param m q → ℂ,
      Function.Surjective (Global.mat Cyclic.axisA Cyclic.axisB Cyclic.axisC z).mulVec) :
    OMA.R_Arxiv_0805_3777_isGenericRank_cube_R1_H3_R1_H3_R1.H2 := by
  intro n hn hr
  obtain ⟨m,q,rfl⟩ := Cyclic.exists_dimension hn hr
  obtain ⟨z,hz⟩ := h m q
  exact of_matrix (by omega) (by omega) (Cyclic.card_innerA m q) (Cyclic.card_innerC m q)
    (Cyclic.card_extra_budget m q) (Cyclic.card_slot m q) (Global.xa z) (Global.xb z) (Global.xc z)
    (Global.na z Cyclic.axisA) (Global.nb z Cyclic.axisB) (Global.nc z Cyclic.axisC) hz

end TensorRankThreeFactor.FinalPack

open TensorRankThreeFactor in
theorem OMA.solution : OMA.R_Arxiv_0805_3777_isGenericRank_cube_R1_H3_R1_H3_R1.H2 := by
  apply FinalPack.h2_of_global
  intro m q
  apply Global.common Cyclic.axisA Cyclic.axisB Cyclic.axisC
  apply Construction.all_sectors m q (BaseDiagonal.solved m q) (RegularDiagonal.Transport.solved m q)
  · intro g
    apply Construction.CrossAdapter.mixed_at q g
    cases q with
    | nine => exact Cross.D9.spans
    | twelve => exact Cross.D12.spans
    | fifteen => exact Cross.D15.spans
  · intro g h hne
    exact Construction.CrossAdapter.regular_at q g h hne Cross.regular_spans
