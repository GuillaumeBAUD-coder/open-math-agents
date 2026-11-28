import OMAStatements.S_oeis_a352656

/-!
# MacMahon box congruences

Bajaj and Burns proved the congruence for boxes of dimensions (n, n, c*n) in
https://github.com/rbajaj5/a183068-supercongruence/blob/e6955c6a329a713e7ed7b3f1dca165f587131c90/related-results/SymmetricBoxPlanePartitionTower.md.
For independent side lengths, this proof adapts the localization and pairing
from @physbuzz's proof of OEIS A008793 (open-math-agents PR 13260).
The Gauss implication uses prime-power lifting from the formalization of
A352657 (open-math-agents PR 17642).

Antidiagonal weights isolate the factors divisible by the scaling prime.
Squaring pairs every remaining factor, including a possible central factor.
The resulting harmonic kernel splits into complete blocks. The dyadic case
uses the parity of the side lengths and a factorial valuation layer at the
preceding scale.
-/

namespace RectangularBox

open Finset OMA.S_oeis_a352656

def wt (A B x : ℕ) := min (min x A) (min B (A+B-x))

lemma fiber_size (A B x : ℕ) (hx : x ∈ Ico 1 (A+B)) :
    (((Icc 1 A) ×ˢ (Icc 1 B)).filter (fun ij : ℕ×ℕ => ij.1+ij.2-1=x)).card =
      wt A B x := by
  let a := max 1 (x+1-B)
  let b := min A x
  have card : (((Icc 1 A) ×ˢ (Icc 1 B)).filter (fun ij : ℕ×ℕ => ij.1+ij.2-1=x)).card =
      (Icc a b).card := by
    apply card_bij (fun ij _ => ij.1)
    · intro ij hij
      simp only [mem_filter,mem_product,mem_Icc] at hij
      simp only [mem_Icc,a,b]; omega
    · rintro ⟨i,j⟩ hij ⟨i',j'⟩ hij' h
      simp only [mem_filter,mem_product,mem_Icc] at hij hij'
      simp only [Prod.mk.injEq]
      dsimp at *
      omega
    · intro i hi
      simp only [mem_Icc,a,b] at hi
      refine ⟨(i,x+1-i),?_,rfl⟩
      simp only [mem_filter,mem_product,mem_Icc]
      omega
  rw [card,Nat.card_Icc]
  have := mem_Ico.mp hx
  dsimp [a,b,wt]; omega

def small (p L : ℕ) := (Ico 1 L).filter (fun x => ¬p∣x)

def term (C x : ℕ) : ℚ := ((C+x:ℕ):ℚ)/x

def residual (p A B C : ℕ) : ℚ :=
  ∏ x ∈ small p (A+B), term C x ^ wt A B x

lemma reflect_weight {A B x : ℕ} (hx : x ≤ A+B) :
    wt A B (A+B-x) = wt A B x := by
  unfold wt
  rw [show A+B-(A+B-x)=x by omega]
  omega

lemma box_swap_ab (A B C : ℕ) : box A B C = box B A C := by
  unfold OMA.S_oeis_a352656.box
  rw [prod_comm]
  apply prod_congr rfl
  intro j hj
  apply prod_congr rfl
  intro i hi
  apply prod_congr rfl
  intro k hk
  rw [add_comm i j]

lemma box_swap_bc (A B C : ℕ) : box A B C = box A C B := by
  unfold OMA.S_oeis_a352656.box
  apply prod_congr rfl
  intro i hi
  rw [prod_comm]
  apply prod_congr rfl
  intro k hk
  apply prod_congr rfl
  intro j hj
  rw [add_right_comm i j k]

lemma telescope (C x : ℕ) (hx : x ≠ 0) :
    (∏ k ∈ range C, (((x+k+1:ℕ):ℚ)/((x+k:ℕ):ℚ)))=term C x := by
  induction C with
  | zero => simp [term,hx]
  | succ C ih =>
    rw [prod_range_succ,ih]
    unfold term
    have hn : (x:ℚ) ≠ 0 := by exact_mod_cast hx
    have hm : ((x:ℚ)+C) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma box_double (A B C : ℕ) : box A B C =
    ∏ i ∈ range A, ∏ j ∈ range B, term C (i+j+1) := by
  unfold OMA.S_oeis_a352656.box
  apply prod_congr rfl
  intro i hi
  apply prod_congr rfl
  intro j hj
  rw [← telescope C (i+j+1) (by omega)]
  apply prod_congr rfl
  intro k hk
  congr 2 <;> omega

lemma shift_product (N : ℕ) (f : ℕ → ℚ) :
    (∏ i ∈ Icc 1 N,f i)=∏ i ∈ range N, f (i+1) := by
  rw [← Ico_add_one_right_eq_Icc,prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel]; apply prod_congr rfl; intro i hi; rw [add_comm 1 i]

lemma box_grouped (A B C : ℕ) :
    box A B C = ∏ x ∈ Ico 1 (A+B), term C x ^ wt A B x := by
  let S := (Icc 1 A) ×ˢ (Icc 1 B)
  let f := fun ij : ℕ×ℕ => ij.1+ij.2-1
  have hmap (ij : ℕ×ℕ) (h : ij∈S) : f ij ∈ Ico 1 (A+B) := by
    simp only [S,mem_product,mem_Icc] at h
    simp only [f,mem_Ico]; omega
  rw [box_double]
  calc
    _ = ∏ i ∈ Icc 1 A, ∏ j ∈ Icc 1 B, term C (i+j-1) := by
      symm
      rw [shift_product]
      apply prod_congr rfl; intro i hi
      rw [shift_product]
      apply prod_congr rfl; intro j hj
      congr 1
      omega
    _ = ∏ ij ∈ S, term C (f ij) := by
      exact (prod_product' (s := Icc 1 A) (t := Icc 1 B) (fun i j => term C (i+j-1))).symm
    _ = ∏ x ∈ Ico 1 (A+B), ∏ ij ∈ S with f ij=x, term C (f ij) :=
      (prod_fiberwise_of_maps_to hmap _).symm
    _ = _ := by
      apply prod_congr rfl
      intro x hx
      calc
        _ = ∏ _ij ∈ S with f _ij=x, term C x := by
          apply prod_congr rfl
          intro ij h
          rw [(mem_filter.mp h).2]
        _ = _ := by rw [prod_const,fiber_size A B x hx]

private lemma mul_min (p x y : ℕ) : min (p*x) (p*y) = p*min x y := by
  rcases le_total x y with h|h
  · rw [min_eq_left h, min_eq_left (Nat.mul_le_mul_left _ h)]
  · rw [min_eq_right h, min_eq_right (Nat.mul_le_mul_left _ h)]

lemma scale_wt (p A B x : ℕ) : wt (p*A) (p*B) (p*x) = p*wt A B x := by
  unfold wt
  rw [← Nat.mul_add, ← Nat.mul_sub]
  simp only [mul_min]

lemma split {p : ℕ} (hp : 0 < p) (A B C : ℕ) :
    box (p*A) (p*B) (p*C) = box A B C^p * residual p (p*A) (p*B) (p*C) := by
  let r := Ico 1 (p*A+p*B)
  let mult := r.filter (fun x => p∣x)
  let weight := fun x => term (p*C) x ^ wt (p*A) (p*B) x
  have part : (∏ x ∈ mult,weight x)*residual p (p*A) (p*B) (p*C) =
      box (p*A) (p*B) (p*C) := by
    rw [box_grouped]
    exact prod_filter_mul_prod_filter_not ..
  have left : (∏ x ∈ mult,weight x)=box A B C^p := by
    rw [box_grouped,← Finset.prod_pow]
    symm
    apply prod_bij (fun x _ => p*x)
    · intro x hx
      have h := mem_Ico.mp hx
      simp only [mult,r,mem_filter,mem_Ico,← Nat.mul_add]
      exact ⟨⟨by nlinarith [Nat.mul_pos hp h.1],Nat.mul_lt_mul_of_pos_left h.2 hp⟩,dvd_mul_right _ _⟩
    · intro x hx y hy h
      exact Nat.eq_of_mul_eq_mul_left hp h
    · intro x hx
      obtain ⟨hr,k,hk⟩ := mem_filter.mp hx
      obtain ⟨lo,hi⟩ := mem_Ico.mp hr
      refine ⟨k,mem_Ico.mpr ⟨?_,?_⟩,hk.symm⟩
      · by_contra! h
        have : k=0 := by omega
        simp [this] at hk
        omega
      · change x < p*A+p*B at hi
        rw [hk,← Nat.mul_add] at hi
        exact Nat.lt_of_mul_lt_mul_left hi
    · intro x hx
      dsimp [weight]
      rw [scale_wt,← pow_mul,mul_comm p]
      congr 1
      unfold term
      push_cast
      field_simp [show (p:ℚ) ≠ 0 by positivity]
      ring
  rw [← part,left]

end RectangularBox

namespace RectangularBox

open Finset

def floorSum (D t : ℕ) : ℤ := ∑ i ∈ range t, ((i/D:ℕ):ℤ)

def floorDiff (D B i : ℕ) : ℤ := (((i+B)/D:ℕ):ℤ)-(i/D:ℕ)

def layer (D A B C : ℕ) : ℤ :=
  ∑ i ∈ range A, (floorDiff D B (i+C)-floorDiff D B i)

lemma floor_shift {D : ℕ} (hD : 0<D) (n : ℕ) : floorSum D (D+n)=floorSum D n+n := by
  unfold floorSum
  rw [sum_range_add,show (∑ i ∈ range D, ((i/D:ℕ):ℤ))=0 from
    sum_eq_zero (fun i hi => by simp [Nat.div_eq_of_lt (mem_range.mp hi)]),zero_add]
  simp only [Nat.add_div_left _ hD,Nat.cast_add,Nat.cast_one,sum_add_distrib,sum_const,card_range,nsmul_eq_mul,mul_one]

lemma floor_sum_slice (D t n : ℕ) :
    (∑ i ∈ range n, (((i+t)/D:ℕ):ℤ))=floorSum D (t+n)-floorSum D t := by
  unfold floorSum
  rw [sum_range_add,add_sub_cancel_left]
  apply sum_congr rfl
  intro i hi
  rw [add_comm i t]

lemma floor_diff_period {D : ℕ} (hD : 0<D) (B i : ℕ) :
    floorDiff D B (D+i)=floorDiff D B i := by
  unfold floorDiff
  rw [add_assoc, Nat.add_div_left _ hD, Nat.add_div_left _ hD]
  push_cast
  ring

lemma floor_diff_add {D : ℕ} (hD : 0<D) (B i : ℕ) :
    floorDiff D (D+B) i=floorDiff D B i+1 := by
  unfold floorDiff
  rw [show i+(D+B)=D+(i+B) by omega, Nat.add_div_left _ hD]
  push_cast
  ring

lemma floor_block {D : ℕ} (hD : 0<D) (B C : ℕ) :
    (∑ i ∈ range D, floorDiff D B (i+C))=(B:ℤ) := by
  have e (i : ℕ) : i+C+B=i+(C+B) := by omega
  simp only [floorDiff,e,sum_sub_distrib,floor_sum_slice]
  rw [add_comm (C+B) D, add_comm C D, floor_shift hD, floor_shift hD]
  push_cast
  ring

lemma layer_add_A {D : ℕ} (hD : 0<D) (A B C : ℕ) :
    layer D (D+A) B C=layer D A B C := by
  unfold layer
  rw [sum_range_add, sum_sub_distrib (s := range D), floor_block hD B C]
  have hz : (∑ i ∈ range D, floorDiff D B i)=(B:ℤ) := by simpa using floor_block hD B 0
  rw [hz,sub_self,zero_add]
  apply sum_congr rfl
  intro i hi
  rw [add_assoc,floor_diff_period hD,floor_diff_period hD]

lemma layer_add_B {D : ℕ} (hD : 0<D) (A B C : ℕ) :
    layer D A (D+B) C=layer D A B C := by
  unfold layer
  simp only [floor_diff_add hD,add_sub_add_right_eq_sub]

lemma layer_add_C {D : ℕ} (hD : 0<D) (A B C : ℕ) :
    layer D A B (D+C)=layer D A B C := by
  unfold layer
  apply sum_congr rfl
  intro i hi
  rw [show i+(D+C)=D+(i+C) by omega,floor_diff_period hD]

lemma period_reduce {D : ℕ} {f : ℕ → ℤ} (h : ∀ t, f (D+t)=f t) (t : ℕ) :
    f t=f (t%D) := by
  have ht : t=D*(t/D)+t%D := (Nat.mod_add_div t D).symm.trans (Nat.add_comm _ _)
  have aux (q s : ℕ) : f (D*q+s)=f s := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show D*(q+1)+s=D+(D*q+s) by ring,h,ih]
  nth_rw 1 [ht]
  exact aux _ _

lemma layer_reduce {D : ℕ} (hD : 0<D) (A B C : ℕ) :
    layer D A B C=layer D (A%D) (B%D) (C%D) := by
  calc
    _=layer D (A%D) B C := period_reduce (f := fun t => layer D t B C) (fun t => layer_add_A hD t B C) A
    _=layer D (A%D) (B%D) C := period_reduce (f := fun t => layer D (A%D) t C) (fun t => layer_add_B hD (A%D) t C) B
    _=_ := period_reduce (f := fun t => layer D (A%D) (B%D) t) (fun t => layer_add_C hD (A%D) (B%D) t) C

lemma floorDiff_indicator {D B : ℕ} (hD : 0<D) (hB : B<D) (i : ℕ) :
    floorDiff D B i=if D ≤ i%D+B then 1 else 0 := by
  unfold floorDiff
  rw [Nat.add_div hD]
  simp only [Nat.div_eq_of_lt hB, Nat.mod_eq_of_lt hB]
  split <;> push_cast <;> ring

lemma floorDiff_unit {D B : ℕ} (hD : 0<D) (hB : B<D) (i : ℕ) :
    0≤floorDiff D B i ∧ floorDiff D B i≤1 := by
  rw [floorDiff_indicator hD hB]
  split <;> omega

lemma floor_default {D A B : ℕ} (hD : 0<D) (hA : A≤D) (hB : B<D) :
    (∑ i ∈ range A, floorDiff D B i)=((A+B-D:ℕ):ℤ) := by
  let q := min A (D-B)
  have hq : q≤A := min_le_left _ _
  nth_rw 1 [show A=q+(A-q) by omega]
  rw [sum_range_add]
  have hz : (∑ i ∈ range q,floorDiff D B i)=0 := by
    apply sum_eq_zero
    intro i hi
    have hl := mem_range.mp hi
    have h₁ : i<D := by omega
    rw [floorDiff_indicator hD hB,Nat.mod_eq_of_lt h₁,if_neg]
    dsimp [q] at hl
    omega
  have ho : (∑ i ∈ range (A-q), floorDiff D B (q+i))=(A-q:ℕ) := by
    have ho' : (∑ i ∈ range (A-q), floorDiff D B (q+i))=
        ∑ _i ∈ range (A-q), (1:ℤ) := by
      apply sum_congr rfl
      intro i hi
      have h₁ := mem_range.mp hi
      have h₂ : q+i<D := by omega
      have hq' : q=D-B := by dsimp [q] at *; omega
      rw [floorDiff_indicator hD hB,Nat.mod_eq_of_lt h₂,if_pos]
      omega
    simpa using ho'
  rw [hz,ho,zero_add]
  dsimp [q]
  omega

lemma layer_nonneg_small {D A B : ℕ} (hD : 0<D) (hA : A≤D) (hB : B<D) (C : ℕ) :
    0≤layer D A B C := by
  let s := ∑ i ∈ range A, floorDiff D B (i+C)
  have h0 : 0 ≤ s := sum_nonneg (fun i _ => (floorDiff_unit hD hB _).1)
  have hcomp : (∑ i ∈ range (D-A),floorDiff D B (A+i+C))≤(D-A:ℕ) := by
    calc
      _≤∑ _i ∈ range (D-A), (1:ℤ) := sum_le_sum (fun i _ => (floorDiff_unit hD hB _).2)
      _=_ := by simp
  have hb := floor_block hD B C
  nth_rw 1 [show D=A+(D-A) by omega] at hb
  rw [sum_range_add] at hb
  unfold layer
  rw [sum_sub_distrib,floor_default hD hA hB]
  change 0 ≤ s - _
  change s+_=(B:ℤ) at hb
  omega

lemma layer_nonneg {D : ℕ} (hD : 0<D) (A B C : ℕ) : 0≤layer D A B C := by
  rw [layer_reduce hD]
  exact layer_nonneg_small hD (Nat.mod_lt _ hD).le (Nat.mod_lt _ hD) _

lemma odd_mod_twice {z : ℕ} (hz : 0<z) (k : ℕ) : ((2*k+1)*z)%(2*z)=z := by
  rw [show (2*k+1)*z=z+(2*z)*k by ring,Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (by omega)]

lemma layer_mid (z : ℕ) (hz : 0<z) (a b c : ℕ) :
    layer (2*z) ((2*a+1)*z) ((2*b+1)*z) ((2*c+1)*z)=(z:ℤ) := by
  rw [layer_reduce (by omega),odd_mod_twice hz,odd_mod_twice hz,odd_mod_twice hz]
  unfold layer
  rw [sum_sub_distrib,floor_default (by omega) (by omega) (by omega)]
  have hf : (∑ i ∈ range z,floorDiff (2*z) z (i+z))=(z:ℤ) := by
    calc
      _=∑ _i ∈ range z,(1:ℤ) := by
        apply sum_congr rfl
        intro i hi
        have h := mem_range.mp hi
        rw [floorDiff_indicator (by omega) (by omega),Nat.mod_eq_of_lt (by omega),if_pos (by omega)]
      _=_ := by simp
  rw [hf]
  omega

end RectangularBox
namespace RectangularBox

open Finset OMA.S_oeis_a352656

def facQ (k : ℕ) : ℚ := k.factorial

lemma fac_pos (k : ℕ) : 0<facQ k := by unfold facQ; positivity

lemma rising (m k : ℕ) : (∏ i ∈ range k, ((m+i+1:ℕ):ℚ)) = facQ (m+k)/facQ m := by
  induction k with
  | zero => simp [(fac_pos m).ne']
  | succ k ih =>
    rw [prod_range_succ,ih]
    have hs : facQ (m+(k+1))=((m+k+1:ℕ):ℚ)*facQ (m+k) := by
      rw [show m+(k+1)=(m+k)+1 by omega]
      simp [facQ,Nat.factorial_succ]
    rw [hs]; ring

def rowQ (B C i : ℕ) := facQ (i+C+B)*facQ i/(facQ (i+C)*facQ (i+B))

lemma rows (A B C : ℕ) : box A B C=∏ i ∈ range A,rowQ B C i := by
  rw [box_double]
  apply prod_congr rfl
  intro i hi
  simp only [term,prod_div_distrib]
  have hh (c : ℕ) : (∏ j ∈ range B, ((c+i+j+1:ℕ):ℚ))=facQ (i+c+B)/facQ (i+c) := by
    rw [show i+c=c+i by omega, ← rising]
  have hnum : (∏ j ∈ range B, ((C+(i+j+1):ℕ):ℚ))=facQ (i+C+B)/facQ (i+C) := by
    rw [← hh C]
    apply prod_congr rfl; intro j hj; congr 1; omega
  have hden : (∏ j ∈ range B, ((i+j+1:ℕ):ℚ))=facQ (i+B)/facQ i := rising i B
  rw [hnum,hden]; unfold rowQ
  field_simp [(fac_pos i).ne',(fac_pos (i+B)).ne',(fac_pos (i+C)).ne']

lemma row_pos (B C i : ℕ) : 0 < rowQ B C i := by
  unfold rowQ; exact div_pos (mul_pos (fac_pos _) (fac_pos _)) (mul_pos (fac_pos _) (fac_pos _))

lemma box_pos (A B C : ℕ) : 0<box A B C := by
  rw [rows]; exact prod_pos fun i _ => row_pos B C i

lemma val_rows {p : ℕ} [Fact p.Prime] (A B C : ℕ) :
    padicValRat p (box A B C)= ∑ i ∈ range A,
      ((padicValNat p (i+C+B).factorial:ℤ)+padicValNat p i.factorial-
        padicValNat p (i+C).factorial-padicValNat p (i+B).factorial) := by
  rw [rows]
  have prodVal (s : Finset ℕ) :
      padicValRat p (∏ i ∈ s,rowQ B C i)=∑ i ∈ s,padicValRat p (rowQ B C i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [prod_insert hi,sum_insert hi,padicValRat.mul (row_pos _ _ _).ne'
        (prod_pos (fun i _ => row_pos B C i)).ne',ih]
  rw [prodVal]; apply sum_congr rfl; intro i hi
  unfold rowQ
  rw [padicValRat.div (mul_pos (fac_pos _) (fac_pos _)).ne' (mul_pos (fac_pos _) (fac_pos _)).ne',
    padicValRat.mul (fac_pos _).ne' (fac_pos _).ne',padicValRat.mul (fac_pos _).ne' (fac_pos _).ne']
  simp [facQ,padicValRat.of_nat, sub_add_eq_sub_sub]

lemma box_val {p : ℕ} [Fact p.Prime] (A B C : ℕ) :
    padicValRat p (box A B C)=∑ t ∈ Ico 1 (A+B+C+1),layer (p^t) A B C := by
  rw [val_rows]
  have leg (k : ℕ) (hk : k≤A+B+C) : (padicValNat p k.factorial:ℤ)=
      ∑ t ∈ Ico 1 (A+B+C+1), ((k/p^t:ℕ):ℤ) := by
    rw [padicValNat_factorial (show Nat.log p k<A+B+C+1 by have := Nat.log_le_self p k; omega)]
    push_cast; rfl
  calc
    _ = ∑ i ∈ range A, ∑ t ∈ Ico 1 (A+B+C+1),
      ((((i+C+B)/p^t:ℕ):ℤ)+((i/p^t:ℕ):ℤ)-(((i+C)/p^t:ℕ):ℤ)-(((i+B)/p^t:ℕ):ℤ)) := by
        apply sum_congr rfl; intro i hi
        have ih := mem_range.mp hi
        rw [leg _ (by omega),leg _ (by omega),leg _ (by omega),leg _ (by omega)]
        rw [sum_sub_distrib,sum_sub_distrib,sum_add_distrib]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro t ht
      unfold layer
      apply sum_congr rfl
      intro i hi
      unfold floorDiff
      ring

lemma integer_box (A B C : ℕ) : ∃ z : ℕ, box A B C=(z:ℚ) := by
  let q := box A B C
  have nonnegative (p : ℕ) [Fact p.Prime] : 0≤padicValRat p q := by
    rw [show q=box A B C from rfl,box_val]
    exact sum_nonneg fun t _ => layer_nonneg (pow_pos (Fact.out : p.Prime).pos _) _ _ _
  have den : q.den=1 := by
    by_contra hn
    obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd hn
    let _ : Fact p.Prime := ⟨hp⟩
    have hnum : ¬p∣q.num.natAbs := by
      intro hd
      exact hp.not_dvd_one (q.reduced ▸ Nat.dvd_gcd hd hpd)
    have val := nonnegative p
    rw [padicValRat_def,padicValInt,padicValNat.eq_zero_of_not_dvd hnum] at val
    have hpos := one_le_padicValNat_of_dvd q.den_nz hpd
    omega
  have hnum : 0≤q.num := Rat.num_nonneg.mpr (box_pos A B C).le
  refine ⟨q.num.toNat,?_⟩
  have eq := q.num_div_den
  rw [den,Nat.cast_one,div_one] at eq
  have he := Int.toNat_of_nonneg hnum
  exact eq.symm.trans (by exact_mod_cast he.symm)

lemma two_div_box (a b c r m : ℕ) (hr : 0<r) (ha : Odd a) (hb : Odd b) (hc : Odd c)
    (eq : box (a*2^(r-1)) (b*2^(r-1)) (c*2^(r-1))=(m:ℚ)) : 2^r∣m := by
  obtain ⟨i,hi⟩ := ha
  obtain ⟨j,hj⟩ := hb
  obtain ⟨k,hk⟩ := hc
  let z := 2^(r-1)
  have pos : 0<z := by positivity
  have hrz : r≤z := by
    have h : r-1<z := Nat.lt_two_pow_self
    omega
  have hza : z≤a*z := Nat.le_mul_of_pos_left _ (by omega)
  have mem : r∈Ico 1 (a*z+b*z+c*z+1) := mem_Ico.mpr ⟨by omega,by omega⟩
  have low := single_le_sum
    (fun t (_ : t∈Ico 1 (a*z+b*z+c*z+1)) => layer_nonneg (show 0<2^t by positivity) (a*z) (b*z) (c*z)) mem
  rw [← box_val (p:=2) (a*z) (b*z) (c*z)] at low
  have e : (2:ℕ)^r=2*z := by
    nth_rw 1 [show r=r-1+1 by omega]
    rw [pow_succ, mul_comm]
  have mid : layer (2^r) (a*z) (b*z) (c*z)=(z:ℤ) := by
    rw [e,hi,hj,hk]
    exact layer_mid z pos i j k
  rw [mid,show box (a*z) (b*z) (c*z)=(m:ℚ) from eq,padicValRat.of_nat] at low
  have mh : m≠0 := by
    rintro rfl
    have hh := box_pos (a*z) (b*z) (c*z)
    rw [show box (a*z) (b*z) (c*z)=((0:ℕ):ℚ) from eq] at hh
    norm_num at hh
  exact (padicValNat_dvd_iff_le mh).mpr (by exact_mod_cast (show (r:ℤ)≤(padicValNat 2 m:ℤ) by omega))

end RectangularBox

namespace RectangularBox
open Finset

def localRing (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {q | ∃ a : ℤ, ∃ b : ℕ, ¬p∣b ∧ q*b=a}
  zero_mem' := ⟨0,1,(Fact.out : p.Prime).not_dvd_one,by simp⟩
  one_mem' := ⟨1,1,(Fact.out : p.Prime).not_dvd_one,by simp⟩
  add_mem' := by
    rintro x y ⟨a,b,hb,he⟩ ⟨c,d,hd,hf⟩
    refine ⟨a*d+c*b,b*d,fun h => ((Fact.out : p.Prime).dvd_mul.mp h).elim hb hd,?_⟩
    push_cast
    linear_combination (d:ℚ)*he+(b:ℚ)*hf
  mul_mem' := by
    rintro x y ⟨a,b,hb,he⟩ ⟨c,d,hd,hf⟩
    refine ⟨a*c,b*d,fun h => ((Fact.out : p.Prime).dvd_mul.mp h).elim hb hd,?_⟩
    push_cast
    linear_combination (y*(d:ℚ))*he+(a:ℚ)*hf
  neg_mem' := by
    rintro x ⟨a,b,hb,h⟩
    exact ⟨-a,b,hb,by push_cast; linarith⟩

lemma linv {p : ℕ} [Fact p.Prime] (x : ℕ) (hx : ¬p∣x) : (x:ℚ)⁻¹ ∈ localRing p := by
  have hn : x≠0 := by rintro rfl; simp at hx
  exact ⟨1,x,hx,by simp [hn]⟩

lemma int_from_local {p : ℕ} [Fact p.Prime] {m : ℤ} {k : ℕ} {u : ℚ}
    (hu : u∈localRing p) (hm : (m:ℚ)=(p:ℚ)^k*u) : (p:ℤ)^k ∣ m := by
  obtain ⟨a,b,hb,he⟩ := hu
  have h : (p:ℤ)^k∣m*(b:ℤ) := by
    refine ⟨a,?_⟩
    exact_mod_cast (show (m:ℚ)*b=(p:ℚ)^k*a by rw [hm,mul_assoc,he])
  have cop : IsCoprime ((p:ℤ)^k) (b:ℤ) := by
    exact (Nat.Coprime.isCoprime ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hb)).pow_left
  exact cop.dvd_of_dvd_mul_right h

lemma first_power {R : Type*} [CommRing R] (z v : R) (k : ℕ) :
    z^2 ∣ (1+z*v)^k-1-z*(k:R)*v := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨u,hu⟩ := ih
    refine ⟨u*(1+z*v)+(k:R)*v^2,?_⟩
    rw [pow_succ]; push_cast
    linear_combination (1+z*v)*hu

lemma first_product {R ι : Type*} [CommRing R] [DecidableEq ι]
    (s : Finset ι) (z : R) (v : ι → R) (k : ι → ℕ) :
    z^2 ∣ (∏ x ∈ s, (1+z*v x)^(k x))-1-z*∑ x ∈ s,(k x:R)*v x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨a,ha⟩ := first_power z (v i) (k i)
    obtain ⟨b,hb⟩ := ih
    rw [prod_insert hi,sum_insert hi]
    let w := ∑ x ∈ s,(k x:R)*v x
    let e := ∏ x ∈ s,(1+z*v x)^(k x)
    change e-1-z*w=z^2*b at hb
    change z^2 ∣ (1+z*v i)^(k i)*e-1-z*((k i:R)*v i+w)
    refine ⟨a*e+b+((k i:R)*v i)*(w+z*b),?_⟩
    linear_combination e*ha+(1+z*(k i:R)*v i)*hb

end RectangularBox

/-! Reduction of these rationals modulo a prime power. -/

namespace RectangularBox
variable {p r : ℕ} [Fact p.Prime]

private lemma reduce_exists (hr : 0<r) (x : localRing p) :
    ∃ z : ZMod (p^r), ∀ (a : ℤ) (b : ℕ), ¬p∣b → (x:ℚ)*b=a → z*b=a := by
  obtain ⟨a,b,hb,he⟩ := x.property
  have ub := (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mpr hb
  refine ⟨(a:ZMod (p^r))*(b:ZMod (p^r))⁻¹,?_⟩
  intro c d hd hf
  have eq : a*(d:ℤ)=c*(b:ℤ) := by
    exact_mod_cast (show (a:ℚ)*d=(c:ℚ)*b by rw [← he,← hf]; ring)
  have eq' := congrArg (fun t : ℤ => (t : ZMod (p^r))) eq
  push_cast at eq'
  have bi := ZMod.mul_inv_of_unit _ ub
  linear_combination (b:ZMod (p^r))⁻¹*eq'+(c:ZMod (p^r))*bi

noncomputable def red (hr : 0<r) (x : localRing p) := (reduce_exists hr x).choose

lemma red_spec (hr : 0<r) (x : localRing p) (a : ℤ) (b : ℕ) (hb : ¬p∣b)
    (he : (x:ℚ)*b=a) : red hr x*b=a := (reduce_exists hr x).choose_spec a b hb he

noncomputable def reduce (hr : 0<r) : localRing p →+* ZMod (p^r) where
  toFun := red hr
  map_zero' := by simpa using red_spec (p:=p) hr 0 0 1 (Fact.out : p.Prime).not_dvd_one (by simp)
  map_one' := by simpa using red_spec (p:=p) hr 1 1 1 (Fact.out : p.Prime).not_dvd_one (by simp)
  map_add' := by
    intro x y
    obtain ⟨a,b,hb,he⟩ := x.property
    obtain ⟨c,d,hd,hf⟩ := y.property
    have hbd : ¬p∣b*d := fun h => ((Fact.out : p.Prime).dvd_mul.mp h).elim hb hd
    have hz := red_spec hr (x+y) (a*d+c*b) (b*d) hbd (by push_cast; linear_combination (d:ℚ)*he+(b:ℚ)*hf)
    have hx := red_spec hr x a b hb he
    have hy := red_spec hr y c d hd hf
    apply ((ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mpr hbd).mul_left_inj.mp
    push_cast at hz ⊢
    linear_combination hz-(d:ZMod (p^r))*hx-(b:ZMod (p^r))*hy
  map_mul' := by
    intro x y
    obtain ⟨a,b,hb,he⟩ := x.property
    obtain ⟨c,d,hd,hf⟩ := y.property
    have hbd : ¬p∣b*d := fun h => ((Fact.out : p.Prime).dvd_mul.mp h).elim hb hd
    have hz := red_spec hr (x*y) (a*c) (b*d) hbd (by push_cast; linear_combination (y.val*(d:ℚ))*he+(a:ℚ)*hf)
    have hx := red_spec hr x a b hb he
    have hy := red_spec hr y c d hd hf
    apply ((ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mpr hbd).mul_left_inj.mp
    push_cast at hz ⊢
    linear_combination hz-(red hr y*(d:ZMod (p^r)))*hx-(a:ZMod (p^r))*hy

lemma ker_reduce (hr : 0<r) (x : localRing p) (h : reduce hr x=0) : (p:localRing p)^r ∣ x := by
  obtain ⟨a,b,hb,he⟩ := x.property
  have hz := red_spec hr x a b hb he
  change red hr x = 0 at h
  rw [h,zero_mul] at hz
  obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz.symm
  let inv : localRing p := ⟨(b:ℚ)⁻¹,linv b hb⟩
  have bn : b≠0 := by rintro rfl; simp at hb
  refine ⟨(k:localRing p)*inv,Subtype.ext ?_⟩
  change (x:ℚ)=(p:ℚ)^r*((k:ℚ)*(b:ℚ)⁻¹)
  field_simp [bn]
  have hq := congrArg (fun t : ℤ => (t:ℚ)) hk
  push_cast at hq
  linear_combination he+hq

noncomputable def invNat (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : ¬p∣k) : localRing p :=
  ⟨(k:ℚ)⁻¹,linv k hk⟩

lemma red_inv (hr : 0<r) (k : ℕ) (hk : ¬p∣k) : reduce hr (invNat p k hk)=(k:ZMod (p^r))⁻¹ := by
  have hn : k≠0 := by rintro rfl; simp at hk
  have he := red_spec hr (invNat p k hk) 1 k hk (by simp [invNat,hn])
  have un := (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mpr hk
  change red hr _ = _
  apply un.mul_left_inj.mp
  simpa only [ZMod.inv_mul_of_unit _ un,Int.cast_one] using he

end RectangularBox

/-! Inverse-square sums over complete blocks of residues. -/

namespace RectangularBox
open Finset
variable {p r : ℕ} [Fact p.Prime]

noncomputable def safe (p : ℕ) [Fact p.Prime] (x : ℕ) : localRing p :=
  if h : ¬p∣x then invNat p x h else 0

lemma safe_inv (x : ℕ) (h : ¬p∣x) : (x:localRing p)*safe p x = 1 := by
  have nz : x≠0 := by rintro rfl; simp at h
  apply Subtype.ext
  simp [safe,h,invNat,nz]

noncomputable def invSq (P : ℕ) (z : ZMod P) : ZMod P := by classical exact if IsUnit z then z⁻¹^2 else 0

lemma three_sum_zero (modulus : ℕ) [NeZero modulus] (htwo : IsUnit (2 : ZMod modulus)) :
    3*(∑ z : ZMod modulus, invSq modulus z)=0 := by
  classical
  let u := htwo.unit
  have ue : (u:ZMod modulus)=2 := htwo.unit_spec
  have perm := Equiv.sum_comp u.mulLeft (invSq modulus)
  have point (z : ZMod modulus) : 4*invSq modulus (u.mulLeft z)=invSq modulus z := by
    change 4*invSq modulus ((u:ZMod modulus)*z)=_
    rw [ue]
    by_cases hz : IsUnit z
    · simp only [invSq,if_pos hz,if_pos (htwo.mul hz)]
      have a := ZMod.mul_inv_of_unit _ (htwo.mul hz)
      have b := ZMod.mul_inv_of_unit _ hz
      have he : 2*((2:ZMod modulus)*z)⁻¹=z⁻¹ := by
        apply hz.mul_left_inj.mp
        linear_combination a-b
      calc
        4*((2:ZMod modulus)*z)⁻¹^2=(2*((2:ZMod modulus)*z)⁻¹)^2 := by ring
        _ = _ := by rw [he]
    · have bad : ¬ IsUnit ((2:ZMod modulus)*z) := fun h => hz (isUnit_of_mul_isUnit_right h)
      simp [invSq,hz,bad]
  have hs : 4*(∑ z : ZMod modulus, invSq modulus z)=(∑ z : ZMod modulus, invSq modulus z) := by
    conv_lhs => rw [← perm,Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => point z
  linear_combination hs

lemma periodic_sum {P : ℕ} [NeZero P] (hP : 0<P) (n : ℕ) (f : ZMod P → ZMod P) :
    (∑ x ∈ range (n*P), f x)=(n:ZMod P)*∑ z : ZMod P, f z := by
  have block : (∑ x ∈ range P, f x)=∑ z : ZMod P, f z := by
    cases P with
    | zero => omega
    | succ P =>
      rw [← Fin.sum_univ_eq_sum_range]
      apply sum_congr rfl
      intro i hi
      congr 1
      exact ZMod.natCast_zmod_val (n:=P+1) (show ZMod (P+1) from i)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul,sum_range_add,ih]
    simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,zero_add,block,Nat.cast_succ]
    ring

lemma three_square_local (r N : ℕ) (hr : 0<r) (hN : p^r∣N) (hodd : p≠2) :
    (p:localRing p)^r ∣ 3*(∑ x ∈ range N, (safe p x)^2) := by
  apply ker_reduce hr
  let P := p^r
  have hP : 0<P := pow_pos (Fact.out : p.Prime).pos _
  let _ : NeZero P := ⟨hP.ne'⟩
  have nd2 : ¬p∣2 := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_two).mp h with bad|bad
    · exact (Fact.out : p.Prime).ne_one bad
    · exact hodd bad
  have hu : IsUnit (2:ZMod P) := by
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mpr nd2
  have each (x : ℕ) : reduce hr (safe p x)^2=invSq P x := by
    by_cases hx : p∣x
    · have bad := mt (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mp (not_not.mpr hx)
      simp [safe,hx,invSq,P,bad]
    · have good := (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mpr hx
      simp [safe,hx,red_inv,invSq,P,good]
  obtain ⟨n,hn⟩ := hN
  simp only [map_mul,map_ofNat,map_sum,map_pow,each]
  have he : N=n*P := by simpa only [P,mul_comm] using hn
  rw [he,periodic_sum hP]
  linear_combination (n:ZMod P)*three_sum_zero P hu

end RectangularBox

namespace RectangularBox
open Finset
variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
lemma reflection {R : Type*} [AddCommMonoid R] {N : ℕ} (hN : p∣N) (f : ℕ → R) :
    (∑ x ∈ small p N,f (N-x))=∑ x ∈ small p N,f x := by
  apply sum_bij (fun x _ => N-x)
  · intro x hx
    obtain ⟨hr,hd⟩ := mem_filter.mp hx
    obtain ⟨lo,hi⟩ := mem_Ico.mp hr
    refine mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩
    intro h
    have hh := Nat.dvd_sub hN h
    rw [show N-(N-x)=x by omega] at hh; exact hd hh
  · intro x hx y hy he
    have := mem_Ico.mp (mem_filter.mp hx).1
    have := mem_Ico.mp (mem_filter.mp hy).1
    omega
  · intro x hx
    obtain ⟨hr,hd⟩ := mem_filter.mp hx
    obtain ⟨lo,hi⟩ := mem_Ico.mp hr
    refine ⟨N-x,mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩,by omega⟩
    intro h
    have hh := Nat.dvd_sub hN h
    rw [show N-(N-x)=x by omega] at hh; exact hd hh
  · intros; rfl

end RectangularBox
namespace RectangularBox

open Finset
variable {p : ℕ} [Fact p.Prime]

noncomputable def unitProduct (p A B C : ℕ) [Fact p.Prime] : localRing p :=
  ∏ x ∈ small p (A+B), (1+(C:localRing p)*safe p x)^wt A B x

noncomputable def kernelSum (p A B : ℕ) [Fact p.Prime] : localRing p :=
  ∑ x ∈ small p (A+B), (wt A B x:localRing p)*safe p x*safe p (A+B-x)

def coeff (p A B C : ℕ) [Fact p.Prime] : localRing p :=
  (C:localRing p)*((A:localRing p)+(B:localRing p)+C)

lemma unitProduct_coe {A B C : ℕ} : (unitProduct p A B C : ℚ)=residual p A B C := by
  unfold unitProduct residual
  change (localRing p).subtype _ = _
  rw [map_prod]
  apply prod_congr rfl
  intro x hx
  have hd := (mem_filter.mp hx).2
  have x0 : x≠0 := by rintro rfl; exact hd (dvd_zero _)
  rw [map_pow]
  congr 1
  change 1+(C:ℚ)*((safe p x:localRing p):ℚ)=term C x
  have he := congrArg (fun y : localRing p => (y:ℚ)) (safe_inv x hd)
  change (x:ℚ)*(safe p x:ℚ)=1 at he
  unfold term
  push_cast
  field_simp [show (x:ℚ)≠0 by exact_mod_cast x0]
  linear_combination (C:ℚ)*he

omit [Fact p.Prime] in
lemma reflection_mem {L x : ℕ} (hL : p∣L) (hx : x∈small p L) :
    L-x∈small p L := by
  obtain ⟨h,hd⟩ := mem_filter.mp hx
  obtain ⟨lo,hi⟩ := mem_Ico.mp h
  refine mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩
  intro hf
  have hd' := Nat.dvd_sub hL hf
  rw [show L-(L-x)=x by omega] at hd'
  exact hd hd'

lemma local_term_pair {A B C x : ℕ} (hL : p∣A+B) (hx : x∈small p (A+B)) :
    (1+(C:localRing p)*safe p x)*(1+(C:localRing p)*safe p (A+B-x)) =
      1+coeff p A B C*(safe p x*safe p (A+B-x)) := by
  have hd := (mem_filter.mp hx).2
  have hd' := (mem_filter.mp (reflection_mem hL hx)).2
  have hxL := (mem_Ico.mp (mem_filter.mp hx).1).2
  have eq : ((A+B-x:ℕ):localRing p)+(x:localRing p)=(A:localRing p)+B := by
    norm_cast
    omega
  have hu := safe_inv x hd
  have hv := safe_inv (A+B-x) hd'
  unfold coeff
  linear_combination (C:localRing p)*safe p x*safe p (A+B-x)*eq
    - (C:localRing p)*safe p (A+B-x)*hu - (C:localRing p)*safe p x*hv

omit [Fact p.Prime] in
lemma product_reflect {R : Type*} [CommMonoid R] {L : ℕ} (hL : p∣L) (f : ℕ→R) :
    (∏ x ∈ small p L, f x)=(∏ x ∈ small p L, f (L-x)) := by
  symm
  apply prod_bij (fun x _ => L-x)
  · intro x hx
    exact reflection_mem hL hx
  · intro x hx y hy h
    have hl := (mem_Ico.mp (mem_filter.mp hx).1).2
    have hr := (mem_Ico.mp (mem_filter.mp hy).1).2
    omega
  · intro y hy
    have hl := (mem_Ico.mp (mem_filter.mp hy).1).2
    exact ⟨L-y,reflection_mem hL hy,by omega⟩
  · intros; rfl

lemma unitProduct_sq {A B C : ℕ} (hL : p∣A+B) :
    unitProduct p A B C^2 =
      ∏ x ∈ small p (A+B),
        (1+coeff p A B C*(safe p x*safe p (A+B-x)))^wt A B x := by
  rw [pow_two]
  unfold unitProduct
  nth_rw 2 [product_reflect hL (fun x => (1+(C:localRing p)*safe p x)^wt A B x)]
  rw [←prod_mul_distrib]
  apply prod_congr rfl
  intro x hx
  have hle := (mem_Ico.mp (mem_filter.mp hx).1).2.le
  rw [reflect_weight hle, ←mul_pow, local_term_pair hL hx]

lemma square_expansion {A B C : ℕ} (hL : p∣A+B) :
    coeff p A B C^2 ∣ unitProduct p A B C^2-1-coeff p A B C*kernelSum p A B := by
  rw [unitProduct_sq hL]
  simpa only [kernelSum,mul_assoc] using
    first_product (small p (A+B)) (coeff p A B C) (fun x => safe p x*safe p (A+B-x))
      (wt A B)

lemma product_one_mod {R ι : Type*} [CommRing R] [DecidableEq ι]
    (s : Finset ι) (z : R) (v : ι→R) (k : ι→ℕ) :
    z∣(∏ x ∈ s,(1+z*v x)^k x)-1 := by
  obtain ⟨q,hq⟩ := first_product s z v k
  refine ⟨z*q+∑ x ∈ s,(k x:R)*v x,?_⟩
  linear_combination hq

lemma unitProduct_one_mod {A B C : ℕ} :
    (C:localRing p) ∣ unitProduct p A B C-1 := by
  exact product_one_mod _ _ _ _

lemma cancel_one_add_multiple {R : Type*} [CommRing R] [IsDomain R]
    {p : R} (hp : p≠0) (k : ℕ) {a b : R} (h : p^k ∣ a*(1+p*b)) : p^k∣a := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    obtain ⟨u,hu⟩ := h
    let q := p^k*u-a*b
    have ha : a=p*q := by
      dsimp [q]
      rw [pow_succ] at hu
      linear_combination hu
    have he : q*(1+p*b)=p^k*u := by
      apply mul_left_cancel₀ hp
      calc
        _ = a*(1+p*b) := by rw [←mul_assoc,←ha]
        _ = _ := by rw [hu,pow_succ]; ring
    obtain ⟨v,hv⟩ := ih ⟨u,he⟩
    refine ⟨v,?_⟩
    rw [ha,hv,pow_succ]; ring

lemma odd_square_extract (hp : p≠2) {U : localRing p} (k : ℕ)
    (hOne : (p:localRing p)∣U-1)
    (hSq : (p:localRing p)^k ∣ U^2-1) :
    (p:localRing p)^k ∣ U-1 := by
  have hn : ¬p∣2 := fun h => ((Nat.dvd_prime Nat.prime_two).mp h).elim (Fact.out : p.Prime).ne_one hp
  have hInv := safe_inv 2 hn
  norm_cast at hInv
  obtain ⟨u,hu⟩ := hOne
  have he : (U-1)*(1+(p:localRing p)*(u*safe p 2))=(U^2-1)*safe p 2 := by
    calc
      _ = ((U-1)*(2+(p:localRing p)*u))*safe p 2 := by
        linear_combination (1-U)*hInv
      _ = _ := by
        rw [show (2:localRing p)+(p:localRing p)*u=U+1 by linear_combination -hu]
        ring
  apply cancel_one_add_multiple (show (p:localRing p)≠0 by
    exact_mod_cast (Fact.out : p.Prime).ne_zero) k
  rw [he]
  exact dvd_mul_of_dvd_left hSq _

lemma two_square_extract [Fact (Nat.Prime 2)] {U : localRing 2} (k : ℕ)
    (hOne : (2:localRing 2)^2 ∣ U-1)
    (hSq : (2:localRing 2)^(k+1) ∣ U^2-1) :
    (2:localRing 2)^k ∣ U-1 := by
  obtain ⟨v,hv⟩ := hOne
  obtain ⟨w,hw⟩ := hSq
  have he : (U-1)*(1+(2:localRing 2)*v)=(2:localRing 2)^k*w := by
    apply mul_left_cancel₀ (show (2:localRing 2)≠0 by norm_num)
    calc
      _ = U^2-1 := by linear_combination (1-U)*hv
      _ = _ := by rw [hw,pow_succ]; ring
  exact cancel_one_add_multiple (by norm_num) k ⟨w,he⟩

lemma unitProduct_one_mod_four [Fact (Nat.Prime 2)] {A B C : ℕ}
    (hL : 2∣A+B) (hC : 2∣C) (h4 : 4∣C ∨ 4∣A+B) :
    (2:localRing 2)^2 ∣ unitProduct 2 A B C-1 := by
  rcases h4 with hc|hl
  · apply dvd_trans _ unitProduct_one_mod
    obtain ⟨q,hq⟩ := hc
    refine ⟨(q:localRing 2),?_⟩
    exact_mod_cast (show C=(2:ℕ)^2*q by exact hq)
  let L := A+B
  let lo := (small 2 L).filter (fun x => 2*x<L)
  let hi := (small 2 L).filter (fun x => ¬2*x<L)
  let f := fun x => (1+(C:localRing 2)*safe 2 x)^wt A B x
  have decomp : (∏ x ∈ lo, f x)*(∏ x ∈ hi, f x)=unitProduct 2 A B C := by
    change _=∏ x ∈ small 2 L, f x
    exact prod_filter_mul_prod_filter_not ..
  have rev : (∏ x ∈ lo, f (L-x))=(∏ x ∈ hi, f x) := by
    apply prod_bij (fun x _ => L-x)
    · intro x hx
      obtain ⟨hx',xlo⟩ := mem_filter.mp hx
      have xhi := (mem_Ico.mp (mem_filter.mp hx').1).2
      refine mem_filter.mpr ⟨reflection_mem hL hx',?_⟩
      omega
    · intro x hx y hy h
      have hx' := (mem_Ico.mp (mem_filter.mp (mem_filter.mp hx).1).1).2
      have hy' := (mem_Ico.mp (mem_filter.mp (mem_filter.mp hy).1).1).2
      omega
    · intro y hy
      obtain ⟨hy',yhi⟩ := mem_filter.mp hy
      have yd := (mem_filter.mp hy').2
      have yl := (mem_Ico.mp (mem_filter.mp hy').1).2
      have yn : 2*y≠L := by
        obtain ⟨s,hs⟩ := hl
        intro h
        exact yd ⟨s,by change L=4*s at hs; omega⟩
      exact ⟨L-y,mem_filter.mpr ⟨reflection_mem hL hy',by omega⟩,by omega⟩
    · intros; rfl
  have he : unitProduct 2 A B C =
      ∏ x ∈ lo, (1+coeff 2 A B C*(safe 2 x*safe 2 (L-x)))^wt A B x := by
    rw [←decomp,←rev,←prod_mul_distrib]
    apply prod_congr rfl
    intro x hx
    have hx' := (mem_filter.mp hx).1
    have xl := (mem_Ico.mp (mem_filter.mp hx').1).2
    dsimp [f,L]
    dsimp [L] at xl
    rw [reflect_weight xl.le,←mul_pow,local_term_pair hL hx']
  rw [he]
  apply dvd_trans _ (product_one_mod _ _ _ _)
  obtain ⟨c,hc⟩ := hC
  obtain ⟨d,hd⟩ := hL
  refine ⟨(c:localRing 2)*(d+c),?_⟩
  unfold coeff
  have e : C*(A+B+C)=(2:ℕ)^2*(c*(d+c)) := by
    rw [hd,hc]; ring
  exact_mod_cast e

end RectangularBox

namespace RectangularBox

open Finset
variable {p : ℕ} [Fact p.Prime]

noncomputable def inverseSquares (p P : ℕ) [Fact p.Prime] : localRing p :=
  ∑ j ∈ small p P, (safe p j)^2

noncomputable def harmonicBlock (p P k : ℕ) [Fact p.Prime] : localRing p :=
  ∑ j ∈ small p P, safe p (k*P+j)

noncomputable def pairBlock (p P l k : ℕ) [Fact p.Prime] : localRing p :=
  ∑ j ∈ small p P, safe p (k*P+j)*safe p ((l-k)*P-j)

omit [Fact p.Prime] in
private theorem blockUnit {P k j : ℕ} (hP : p ∣ P) (hj : ¬p∣j) :
    ¬p∣k*P+j := fun h => hj ((Nat.dvd_add_iff_right (dvd_mul_of_dvd_right hP k)).mpr h)

omit [Fact p.Prime] in
private theorem reverseBlockUnit {P l j : ℕ} (hP : p ∣ P) (hj : ¬p∣j)
    (hjlt : j ≤ l*P) : ¬p∣l*P-j := by
  intro h
  have hd := Nat.dvd_sub (dvd_mul_of_dvd_right hP l) h
  rw [show l*P-(l*P-j)=j by omega] at hd
  exact hj hd

private theorem pair_point {r k t j : ℕ} (hr : 0 < r) (hjt : j ≤ t*p^r) (hj : ¬p∣j) :
    (p:localRing p)^r ∣
      safe p (k*p^r+j)*safe p (t*p^r-j)+(safe p j)^2 := by
  let P := p^r
  have hP : p∣P := dvd_pow_self p hr.ne'
  have h1 := safe_inv (k*P+j) (blockUnit hP hj)
  have h2 := safe_inv (t*P-j) (reverseBlockUnit hP hj hjt)
  have h0 := safe_inv j hj
  let u := safe p (k*P+j)
  let v := safe p (t*P-j)
  let w := safe p j
  have h1' : ((k:localRing p)*(p:localRing p)^r+j)*u=1 := by
    simpa only [P,u,Nat.cast_add,Nat.cast_mul,Nat.cast_pow] using h1
  have h2' : ((t:localRing p)*(p:localRing p)^r-j)*v=1 := by
    simpa only [P,v,Nat.cast_sub hjt,Nat.cast_mul,Nat.cast_pow] using h2
  have hu : u-w= -(p:localRing p)^r*k*u*w := by
    linear_combination w*h1'-u*h0
  have hv : v+w=(p:localRing p)^r*t*v*w := by
    linear_combination -v*h0-w*h2'
  change (p:localRing p)^r ∣ u*v+w^2
  refine ⟨(t:localRing p)*v*w^2-k*u*w*v,?_⟩
  linear_combination v*hu+w*hv

private theorem pairBlock_mod {r l k : ℕ} (hr : 0<r) (hk : k<l) :
    (p:localRing p)^r ∣ pairBlock p (p^r) l k + inverseSquares p (p^r) := by
  unfold pairBlock inverseSquares
  rw [← sum_add_distrib]
  apply Finset.dvd_sum
  intro j hj
  obtain ⟨jr, jprime⟩ := mem_filter.mp hj
  have jlt := (mem_Ico.mp jr).2
  apply pair_point hr _ jprime
  exact jlt.le.trans (by
    simpa only [one_mul] using
      (Nat.mul_le_mul_right (p^r) (show 1 ≤ l-k by omega)))

private theorem harmonic_reflect_complete {r k : ℕ} (hr : 0<r) :
    2*harmonicBlock p (p^r) k =
      ((2*k+1:ℕ):localRing p)*(p:localRing p)^r*pairBlock p (p^r) (2*k+1) k := by
  let P := p^r
  have hP : p∣P := dvd_pow_self p hr.ne'
  have hshift : (∑ j ∈ small p P, safe p ((k+1)*P-j)) = harmonicBlock p P k := by
    unfold harmonicBlock
    rw [← reflection hP (fun j => safe p (k*P+j))]
    apply sum_congr rfl
    intro j hj
    have hl : j ≤ P := (mem_Ico.mp (mem_filter.mp hj).1).2.le
    rw [Nat.add_mul,one_mul,Nat.add_sub_assoc hl]
  change 2*harmonicBlock p P k = ((2*k+1:ℕ):localRing p)*(p:localRing p)^r*
    pairBlock p P (2*k+1) k
  rw [two_mul]
  nth_rw 2 [← hshift]
  unfold harmonicBlock pairBlock
  rw [← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro j hj
  have jp : ¬p∣j := (mem_filter.mp hj).2
  have jlt := (mem_Ico.mp (mem_filter.mp hj).1).2
  have hjt : j ≤ (k+1)*P := jlt.le.trans (by
    simpa only [one_mul] using Nat.mul_le_mul_right P (show 1 ≤ k+1 by omega))
  rw [show 2*k+1-k=k+1 by omega]
  have h1 := safe_inv (k*P+j) (blockUnit hP jp)
  have h2 := safe_inv ((k+1)*P-j) (reverseBlockUnit hP jp hjt)
  have he : (((k*P+j:ℕ):localRing p)+(((k+1)*P-j:ℕ):localRing p)) =
      ((2*k+1:ℕ):localRing p)*(p:localRing p)^r := by
    have hz : k*P+j+((k+1)*P-j)=(2*k+1)*p^r := by
      rw [show k*P+j+((k+1)*P-j)=k*P+(k+1)*P by omega]
      dsimp [P]
      ring
    exact_mod_cast hz
  linear_combination
    (safe p (k*P+j)*safe p ((k+1)*P-j))*he -
      safe p ((k+1)*P-j)*h1 - safe p (k*P+j)*h2

private theorem harmonicBlock_mod {r k : ℕ} (hr : 0<r) :
    (p:localRing p)^(2*r) ∣
      2*harmonicBlock p (p^r) k +
      ((2*k+1:ℕ):localRing p)*(p:localRing p)^r*inverseSquares p (p^r) := by
  rw [harmonic_reflect_complete hr]
  obtain ⟨c,hc⟩ := pairBlock_mod (p:=p) (k:=k) (l:=2*k+1) hr (by omega)
  refine ⟨((2*k+1:ℕ):localRing p)*c,?_⟩
  rw [show 2*r=r+r by omega,pow_add]
  linear_combination ((2*k+1:ℕ):localRing p)*(p:localRing p)^r*hc

end RectangularBox
namespace RectangularBox

open Finset
variable {p : ℕ} [Fact p.Prime]

private lemma safe_of_dvd {x : ℕ} (h : p ∣ x) : safe p x = 0 := by
  simp [safe,h]

omit [Fact p.Prime] in
private theorem completeBlocks {R : Type*} [AddCommMonoid R] {P : ℕ}
    (hP : p ∣ P) (f : ℕ → R) (hf : ∀ x, p ∣ x → f x = 0) (k n : ℕ) :
    (∑ x ∈ Ico (k*P) ((k+n)*P), f x) =
      ∑ i ∈ range n, ∑ j ∈ small p P, f ((k+i)*P+j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ← Finset.sum_Ico_consecutive f (Nat.mul_le_mul_right P (by omega))
      (Nat.mul_le_mul_right P (show k+n ≤ k+(n+1) by omega)), ih]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range, show (k+(n+1))*P-(k+n)*P=P by
      rw [show k+(n+1)=k+n+1 by omega,Nat.add_mul,one_mul]; omega]
    symm
    apply sum_subset
    · intro j hj
      exact mem_range.mpr (mem_Ico.mp (mem_filter.mp hj).1).2
    · intro j hj hout
      apply hf
      have jp : p ∣ j := by
        by_cases jz : j=0
        · simp [jz]
        by_contra h
        exact hout (mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,mem_range.mp hj⟩,h⟩)
      exact dvd_add (dvd_mul_of_dvd_right hP _) jp

private theorem linearOddSum (k n : ℕ) :
    (∑ i ∈ range n, ((2*(k+i)+1:ℕ):localRing p)) = (n:localRing p)*(2*k+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,ih]
    push_cast
    ring

private theorem sum_harmonic_mod {r : ℕ} (hr : 0<r) (b a : ℕ) :
    (p:localRing p)^(2*r) ∣
      2*(∑ x ∈ Ico (b*p^r) ((b+a)*p^r), safe p x) +
      (a:localRing p)*(2*b+a)*(p:localRing p)^r*inverseSquares p (p^r) := by
  rw [completeBlocks (dvd_pow_self p hr.ne') (safe p) (fun _ h => safe_of_dvd h),
    mul_sum]
  change (p:localRing p)^(2*r) ∣ (∑ i ∈ range a, 2*harmonicBlock p (p^r) (b+i)) + _
  rw [←linearOddSum b a, sum_mul, sum_mul, ←sum_add_distrib]
  exact Finset.dvd_sum fun i _ => harmonicBlock_mod hr (k:=b+i)

private theorem sum_pair_mod {r : ℕ} (hr : 0<r) {a b : ℕ} (hab : a≤b) :
    (p:localRing p)^r ∣
      (∑ x ∈ Ico (a*p^r) (b*p^r), safe p x*safe p ((a+b)*p^r-x)) +
      ((b-a:ℕ):localRing p)*inverseSquares p (p^r) := by
  have hb : a+(b-a)=b := by omega
  have he : (∑ x ∈ Ico (a*p^r) (b*p^r), safe p x*safe p ((a+b)*p^r-x)) =
      ∑ i ∈ range (b-a), pairBlock p (p^r) (a+b) (a+i) := by
    nth_rw 1 [←hb]
    rw [completeBlocks (dvd_pow_self p hr.ne') _
      (fun x h => by rw [safe_of_dvd h,zero_mul])]
    apply sum_congr rfl
    intro i hi
    unfold pairBlock
    apply sum_congr rfl
    intro j hj
    rw [Nat.sub_add_eq, ←Nat.sub_mul]
  rw [he]
  have const : ((b-a:ℕ):localRing p)*inverseSquares p (p^r) =
      ∑ _ ∈ range (b-a), inverseSquares p (p^r) := by simp
  rw [const, ←sum_add_distrib]
  apply Finset.dvd_sum
  intro i hi
  apply pairBlock_mod hr
  have hi' := mem_range.mp hi
  omega

end RectangularBox
namespace RectangularBox

open Finset
variable {p : ℕ} [Fact p.Prime]

private theorem tail_reflect {A B : ℕ} (ha : 0<A) (hB : p∣B) :
    (∑ x ∈ Ico 1 A, safe p (A+B-x)) =
      ∑ x ∈ Ico B (A+B), safe p x := by
  have hsplit := Finset.sum_Ico_consecutive (safe p) (show B≤B+1 by omega)
    (show B+1≤A+B by omega)
  have hsingle : Ico B (B+1) = {B} := by
    ext x
    simp only [mem_Ico,mem_singleton]
    omega
  rw [hsingle, sum_singleton, safe_of_dvd hB, zero_add] at hsplit
  rw [←hsplit]
  apply sum_bij (fun x _ => A+B-x)
  · intro x hx
    have := mem_Ico.mp hx
    exact mem_Ico.mpr ⟨by omega,by omega⟩
  · intro x hx y hy he
    have := mem_Ico.mp hx
    have := mem_Ico.mp hy
    omega
  · intro y hy
    have := mem_Ico.mp hy
    exact ⟨A+B-y,mem_Ico.mpr ⟨by omega,by omega⟩,by omega⟩
  · intros
    rfl

private theorem split_kernel {A B : ℕ} (hab : A≤B) (hB : p∣B) (hL : p∣A+B) :
    kernelSum p A B =
      2*(∑ x ∈ Ico B (A+B), safe p x) +
      (A:localRing p)*(∑ x ∈ Ico A B, safe p x*safe p (A+B-x)) := by
  by_cases hA : A=0
  · subst A
    simp [kernelSum,wt]
  have hapos : 1≤A := by omega
  let L := A+B
  let f := fun x => (wt A B x:localRing p)*safe p x*safe p (L-x)
  have extend : (∑ x ∈ small p L, f x) = ∑ x ∈ Ico 1 L, f x := by
    apply sum_subset (filter_subset _ _)
    intro x hin hout
    have hd : p∣x := by
      by_contra hn
      exact hout (mem_filter.mpr ⟨hin,hn⟩)
    simp [f,safe_of_dvd hd]
  change (∑ x ∈ small p L, f x) = _
  rw [extend, ←Finset.sum_Ico_consecutive f hapos (show A≤L by omega),
    ←Finset.sum_Ico_consecutive f hab (show B≤L by omega)]
  have head : (∑ x ∈ Ico 1 A, f x) = ∑ x ∈ Ico B L, safe p x := by
    rw [←tail_reflect (by omega) hB]
    apply sum_congr rfl
    intro x hx
    have hh := mem_Ico.mp hx
    have hw : wt A B x = x := by unfold wt; omega
    dsimp only [f]
    rw [hw]
    by_cases hd : p∣x
    · have hd' : p∣L-x := Nat.dvd_sub hL hd
      simp [safe_of_dvd hd, safe_of_dvd (show p∣A+B-x from hd')]
    · rw [safe_inv x hd,one_mul]
  have mid : (∑ x ∈ Ico A B, f x) =
      ∑ x ∈ Ico A B, (A:localRing p)*(safe p x*safe p (L-x)) := by
    apply sum_congr rfl
    intro x hx
    have hh := mem_Ico.mp hx
    have hw : wt A B x = A := by unfold wt; omega
    simp only [f,hw,mul_assoc]
  have tail : (∑ x ∈ Ico B L, f x) = ∑ x ∈ Ico B L, safe p x := by
    apply sum_congr rfl
    intro x hx
    have hh := mem_Ico.mp hx
    have hw : wt A B x = L-x := by dsimp only [L] at hh ⊢; unfold wt; omega
    dsimp only [f]
    rw [hw]
    by_cases hd : p∣x
    · rw [safe_of_dvd hd,mul_zero,zero_mul]
    · have hd' : ¬p∣L-x := by
        intro hy
        have hz := Nat.dvd_sub hL hy
        rw [show L-(L-x)=x by omega] at hz
        exact hd hz
      rw [mul_comm _ (safe p x),mul_assoc,safe_inv (L-x) hd',mul_one]
  rw [head,mid,tail,←mul_sum]
  change _ + (_ + _) = 2*(∑ x ∈ Ico B L, safe p x) + _
  ring

private theorem kernel_base {r a b : ℕ} (hr : 0<r) (hab : a≤b) :
    (p:localRing p)^(2*r) ∣
      kernelSum p (a*p^r) (b*p^r) +
        3*(a:localRing p)*b*(p:localRing p)^r*inverseSquares p (p^r) := by
  have hP : p∣p^r := dvd_pow_self p hr.ne'
  have hA := dvd_mul_of_dvd_right hP a
  have hB := dvd_mul_of_dvd_right hP b
  rw [split_kernel (Nat.mul_le_mul_right _ hab) hB (dvd_add hA hB),←Nat.add_mul a b]
  obtain ⟨h,hH⟩ := sum_harmonic_mod (p:=p) hr b a
  obtain ⟨j,hJ⟩ := sum_pair_mod (p:=p) hr hab
  rw [add_comm b a] at hH
  refine ⟨h+(a:localRing p)*j,?_⟩
  push_cast [Nat.cast_sub hab]
  push_cast [Nat.cast_sub hab] at hJ
  rw [show 2*r=r+r by omega,pow_add] at hH ⊢
  linear_combination hH+(a:localRing p)*(p:localRing p)^r*hJ

private theorem inverseSquares_eq_range (P : ℕ) :
    inverseSquares p P = ∑ x ∈ range P, (safe p x)^2 := by
  unfold inverseSquares
  apply sum_subset
  · intro x hx
    exact mem_range.mpr (mem_Ico.mp (mem_filter.mp hx).1).2
  · intro x hx hn
    have hd : p∣x := by
      by_cases x0 : x=0
      · simp [x0]
      by_contra hx'
      exact hn (mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,mem_range.mp hx⟩,hx'⟩)
    simp [safe_of_dvd hd]

lemma kernel_odd {r a b : ℕ} (hr : 0<r) (hp : p≠2) (hab : a≤b) :
    (p:localRing p)^(2*r) ∣ kernelSum p (a*p^r) (b*p^r) := by
  obtain ⟨h,hH⟩ := kernel_base (p:=p) hr hab
  have hq : (p:localRing p)^r ∣ 3*inverseSquares p (p^r) := by
    rw [inverseSquares_eq_range]
    exact three_square_local r (p^r) hr dvd_rfl hp
  obtain ⟨q,hQ⟩ := hq
  refine ⟨h-(a:localRing p)*b*q,?_⟩
  rw [show 2*r=r+r by omega,pow_add] at hH ⊢
  linear_combination hH-(a:localRing p)*b*(p:localRing p)^r*hQ

end RectangularBox
namespace RectangularBox

open Finset

private theorem sumInvSq_eq_sumSq (P : ℕ) [NeZero P] :
    (∑ z : ZMod P, invSq P z) = ∑ z : ZMod P, if IsUnit z then z ^ 2 else 0 := by
  classical
  let f : ZMod P → ZMod P := fun z => if IsUnit z then z⁻¹ else z
  have hff : Function.Involutive f := by
    intro z
    by_cases h : IsUnit z
    · obtain ⟨u,rfl⟩ := h
      dsimp only [f]
      rw [if_pos u.isUnit, ZMod.inv_coe_unit, if_pos u⁻¹.isUnit,
        ZMod.inv_coe_unit, inv_inv]
    · simp [f, h]
  let e : ZMod P ≃ ZMod P := ⟨f, f, hff, hff⟩
  have he (z : ZMod P) : invSq P (e z) = if IsUnit z then z ^ 2 else 0 := by
    change invSq P (f z) = _
    by_cases h : IsUnit z
    · obtain ⟨u,rfl⟩ := h
      simp only [f, invSq, if_pos u.isUnit, ZMod.inv_coe_unit, if_pos u⁻¹.isUnit, inv_inv]
    · simp [f, invSq, h]
  rw [← Equiv.sum_comp e (invSq P)]
  exact sum_congr rfl (fun z _ => he z)

private theorem oddSquareSum (R : Type*) [CommRing R] (n : ℕ) :
    3 * (∑ j ∈ range n, (2 * (j : R) + 1)^2) + (n : R) = 4 * (n : R)^3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Nat.cast_succ]
    linear_combination ih

theorem two_mul_sum_invSq {r : ℕ} (hr : 0 < r) :
    (2 : ZMod (2^r)) * (∑ z : ZMod (2^r), invSq (2^r) z) = 0 := by
  classical
  let P := 2^r
  let n := 2^(r-1)
  have hP : P = 2*n := by
    dsimp only [P,n]
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ r)]
  have : NeZero P := ⟨pow_ne_zero _ (by decide)⟩
  change (2 : ZMod P) * (∑ z : ZMod P, invSq P z) = 0
  have hUnits (z : ZMod P) : IsUnit z ↔ z.val % 2 = 1 := by
    have aux := ZMod.isUnit_natCast_iff_not_dvd_pow (a := z.val) Nat.prime_two hr
    change IsUnit (z.val : ZMod P) ↔ ¬ 2 ∣ z.val at aux
    rw [ZMod.natCast_zmod_val] at aux
    rw [aux, Nat.dvd_iff_mod_eq_zero]
    omega
  have hsum :
      (∑ z : ZMod P, if IsUnit z then z^2 else 0) =
         ∑ j ∈ range n, (2*(j : ZMod P)+1)^2 := by
    rw [← Finset.sum_filter]
    symm
    refine sum_bij (fun j _ => ((2*j+1 : ℕ) : ZMod P)) ?_ ?_ ?_ ?_
    · intro j hj
      have hlt := mem_range.mp hj
      have hw : 2*j+1 < P := by omega
      rw [mem_filter, hUnits, ZMod.val_natCast_of_lt hw]
      exact ⟨mem_univ _, by omega⟩
    · intro i hi j hj h
      have hi' := mem_range.mp hi
      have hj' := mem_range.mp hj
      have hiP : 2*i+1 < P := by omega
      have hjP : 2*j+1 < P := by omega
      have he := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt hiP, ZMod.val_natCast_of_lt hjP] at he
      omega
    · intro z hz
      have hzU := (mem_filter.mp hz).2
      have hzodd := (hUnits z).mp hzU
      have hzP := ZMod.val_lt z
      refine ⟨z.val / 2, mem_range.mpr (by omega), ?_⟩
      rw [show 2*(z.val/2)+1 = z.val by omega, ZMod.natCast_zmod_val]
    · intro j _
      push_cast
      rfl
  rw [sumInvSq_eq_sumSq, hsum]
  have hn0 : (2 : ZMod P) * (n : ZMod P) = 0 := by
    rw [show (2 : ZMod P) = ((2 : ℕ) : ZMod P) by simp, ← Nat.cast_mul, ← hP, ZMod.natCast_self]
  have h3 :
      (3 : ZMod P) * ((2 : ZMod P) * (∑ j ∈ range n, (2*(j : ZMod P)+1)^2)) = 0 := by
    calc
      _ = 2*(3*(∑ j ∈ range n, (2*(j : ZMod P)+1)^2)+(n : ZMod P)) -
          2*(n : ZMod P) := by ring
      _ = 2*(4*(n : ZMod P)^3) := by rw [oddSquareSum, hn0, sub_zero]
      _ = 4*(n : ZMod P)^2*(2*(n : ZMod P)) := by ring
      _ = 0 := by rw [hn0, mul_zero]
  have hunit : IsUnit (3 : ZMod P) := by
    apply (ZMod.isUnit_natCast_iff_not_dvd_pow (a := 3) Nat.prime_two hr).mpr
    decide
  obtain ⟨u, hu⟩ := hunit
  apply u.mulLeft.injective
  change (u : ZMod P) * _ = (u : ZMod P) * 0
  rw [hu, h3, mul_zero]

end RectangularBox
namespace RectangularBox

open Finset
variable [Fact (Nat.Prime 2)]

private theorem two_inverseSquares {r : ℕ} (hr : 0<r) :
    (2:localRing 2)^r ∣ 2*inverseSquares 2 (2^r) := by
  let P := 2^r
  have hP : 0<P := pow_pos (by decide : 0<(2:ℕ)) _
  let _ : NeZero P := ⟨hP.ne'⟩
  apply ker_reduce hr
  rw [inverseSquares_eq_range]
  have each (x : ℕ) : reduce hr (safe 2 x)^2=invSq P x := by
    by_cases hx : 2∣x
    · have bad := mt (ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two hr).mp (not_not.mpr hx)
      simp [safe,hx,invSq,P,bad]
    · have good := (ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two hr).mpr hx
      simp [safe,hx,red_inv,invSq,P,good]
  simp only [map_mul,map_ofNat,map_sum,map_pow,each]
  change (2:ZMod P)*(∑ x ∈ range P, invSq P x)=0
  have he := periodic_sum hP 1 (invSq P)
  simp only [one_mul,Nat.cast_one] at he
  rw [he]
  exact two_mul_sum_invSq hr

lemma kernel_two {r a b : ℕ} (hr : 0<r) (hab : a≤b) :
    (2:localRing 2)^(2*r-1) ∣ kernelSum 2 (a*2^r) (b*2^r) := by
  obtain ⟨h,hH⟩ := kernel_base (p:=2) hr hab
  obtain ⟨q,hQ⟩ := two_inverseSquares hr
  have he : (2:localRing 2)^r*inverseSquares 2 (2^r)=(2:localRing 2)^(2*r-1)*q := by
    calc
      _ = (2:localRing 2)^(r-1)*(2*inverseSquares 2 (2^r)) := by
        nth_rw 1 [show r=(r-1)+1 by omega]
        rw [pow_succ,mul_assoc]
      _ = _ := by rw [hQ,←mul_assoc,←pow_add,show r-1+r=2*r-1 by omega]
  refine ⟨2*h-3*(a:localRing 2)*b*q,?_⟩
  nth_rw 1 [show 2*r=(2*r-1)+1 by omega] at hH
  rw [pow_succ] at hH
  have hc : kernelSum 2 (a*2^r) (b*2^r) +
       3*(a:localRing 2)*b*((2:localRing 2)^r*inverseSquares 2 (2^r)) =
       (2:localRing 2)^(2*r-1)*2*h := by linear_combination hH
  rw [he] at hc
  linear_combination hc

lemma kernel_two_even {r a b : ℕ} (hr : 0<r) (hab : a≤b) (hev : Even (a*b)) :
    (2:localRing 2)^(2*r) ∣ kernelSum 2 (a*2^r) (b*2^r) := by
  obtain ⟨h,hH⟩ := kernel_base (p:=2) hr hab
  obtain ⟨q,hQ⟩ := two_inverseSquares hr
  obtain ⟨k,hk⟩ := hev
  have hk' : (a:localRing 2)*b=2*k := by
    norm_cast
    omega
  refine ⟨h-3*(k:localRing 2)*q,?_⟩
  have hc : kernelSum 2 (a*2^r) (b*2^r) +
       3*((a:localRing 2)*b)*(2:localRing 2)^r*inverseSquares 2 (2^r) =
       (2:localRing 2)^(2*r)*h := by linear_combination hH
  rw [hk'] at hc
  rw [show 2*r=r+r by omega,pow_add] at hc ⊢
  linear_combination hc-3*(k:localRing 2)*(2:localRing 2)^r*hQ

end RectangularBox
namespace RectangularBox

open Finset OMA.S_oeis_a352656

variable {p : ℕ} [Fact p.Prime]

lemma kernelSum_swap (a b : ℕ) : kernelSum p a b=kernelSum p b a := by
  have h (x : ℕ) : wt a b x=wt b a x := by unfold wt; omega
  unfold kernelSum
  simp_rw [show a+b=b+a by omega]
  apply sum_congr rfl
  intro x hx
  rw [h]

lemma coeff_scaled (a b c r : ℕ) :
    coeff p (a*p^r) (b*p^r) (c*p^r)=
      (p:localRing p)^(2*r)*((c:localRing p)*((a:localRing p)+b+c)) := by
  unfold coeff
  push_cast
  rw [show 2*r=r+r by omega,pow_add]
  ring

lemma mul_dvd_power {R : Type*} [CommMonoid R] {x a b : R} {i j : ℕ}
    (h : x^i∣a) (k : x^j∣b) : x^(i+j)∣a*b := by
  rw [pow_add]
  exact mul_dvd_mul h k

lemma square_dvd {A B C k : ℕ} (hL : p∣A+B)
    (h1 : (p:localRing p)^k ∣ coeff p A B C*kernelSum p A B)
    (h2 : (p:localRing p)^k ∣ coeff p A B C^2) :
    (p:localRing p)^k ∣ unitProduct p A B C^2-1 := by
  simpa only [sub_add_cancel] using
    dvd_add (h2.trans (square_expansion hL)) h1

lemma scaled_unit_delta (a b c r m : ℕ) (hr : 0<r)
    (hm : box (a*p^(r-1)) (b*p^(r-1)) (c*p^(r-1))=(m:ℚ))
    (hOdd : p≠2 → (p:localRing p)^(2*r)∣kernelSum p (a*p^r) (b*p^r))
    (hTwo : p=2 → (p:localRing p)^(2*r-1)∣kernelSum p (a*p^r) (b*p^r))
    (hEven : p=2 → Even (a*b) → (p:localRing p)^(2*r)∣kernelSum p (a*p^r) (b*p^r))
    (hParity : p=2 → Even c ∨ Odd a ∧ Odd b ∧ Odd c) :
    (p:localRing p)^(4*r)∣
      (m:localRing p)^p*(unitProduct p (a*p^r) (b*p^r) (c*p^r)-1) := by
  let A := a*p^r
  let B := b*p^r
  let C := c*p^r
  let K := coeff p A B C
  let S := kernelSum p A B
  let U := unitProduct p A B C
  have pP : p∣p^r := dvd_pow_self _ hr.ne'
  have hpL : p∣A+B := dvd_add (dvd_mul_of_dvd_right pP _) (dvd_mul_of_dvd_right pP _)
  have hpC : p∣C := dvd_mul_of_dvd_right pP _
  have kCast : K=(p:localRing p)^(2*r)*((c:localRing p)*((a:localRing p)+b+c)) :=
    coeff_scaled a b c r
  have kBase : (p:localRing p)^(2*r)∣K := Dvd.intro _ kCast.symm
  change (p:localRing p)^(4*r)∣(m:localRing p)^p*(U-1)
  by_cases hp : p=2
  · subst p
    simp only [Nat.cast_ofNat] at kCast kBase
    have hs : (2:localRing 2)^(2*r-1)∣S := hTwo rfl
    have hsGood (h : Even (a*b)) : (2:localRing 2)^(2*r)∣S := hEven rfl h
    rcases hParity rfl with hc|⟨ha,hb,hc⟩
    · have hc2 := even_iff_two_dvd.mp hc
      have hc4 : 4∣C := Nat.mul_dvd_mul hc2 pP
      have u4 : (2:localRing 2)^2∣U-1 := unitProduct_one_mod_four hpL hpC (Or.inl hc4)
      have k1 : (2:localRing 2)^(2*r+1)∣K := by
        obtain ⟨q,hq⟩ := hc2
        refine ⟨(q:localRing 2)*((a:localRing 2)+b+c),?_⟩
        have eqR : (c:localRing 2)=2*(q:localRing 2) := by exact_mod_cast hq
        rw [kCast,pow_succ]
        nth_rw 1 [eqR]
        ring
      have quad : (2:localRing 2)^(4*r+1)∣K^2 :=
        (pow_dvd_pow _ (show 4*r+1≤(2*r+1)+(2*r+1) by omega)).trans
          (by simpa only [pow_two] using mul_dvd_power k1 k1)
      have lead : (2:localRing 2)^(4*r+1)∣K*S := by
        by_cases h : Even (a*b)
        · simpa only [show 4*r+1=(2*r+1)+2*r by omega] using mul_dvd_power k1 (hsGood h)
        · have ha : Odd a := Nat.not_even_iff_odd.mp fun e =>
            h (even_iff_two_dvd.mpr (dvd_mul_of_dvd_left (even_iff_two_dvd.mp e) b))
          have hb : Odd b := Nat.not_even_iff_odd.mp fun e =>
            h (even_iff_two_dvd.mpr (dvd_mul_of_dvd_right (even_iff_two_dvd.mp e) a))
          have he : 2∣a+b+c := even_iff_two_dvd.mp ((ha.add_odd hb).add hc)
          obtain ⟨q,hq⟩ := hc2
          obtain ⟨s,hs'⟩ := he
          have k2 : (2:localRing 2)^(2*r+2)∣K := by
            refine ⟨(q:localRing 2)*s,?_⟩
            rw [kCast,pow_add]
            have eq : c*(a+b+c)=(2:ℕ)^2*(q*s) := by
              calc
                _=(2*q)*(2*s) := congrArg₂ (·*·) hq hs'
                _=_ := by ring
            have eqR : (c:localRing 2)*((a:localRing 2)+b+c)=2^2*((q:localRing 2)*s) := by
              exact_mod_cast eq
            rw [eqR,mul_assoc]
          simpa only [show 4*r+1=(2*r+2)+(2*r-1) by omega] using mul_dvd_power k2 hs
      exact dvd_mul_of_dvd_right (two_square_extract (4*r) u4 (square_dvd hpL lead quad)) _
    · have hL4 : 4∣A+B := by
        change 4∣a*2^r+b*2^r
        rw [← Nat.add_mul]
        exact Nat.mul_dvd_mul (even_iff_two_dvd.mp (ha.add_odd hb)) pP
      have u4 : (2:localRing 2)^2∣U-1 := unitProduct_one_mod_four hpL hpC (Or.inr hL4)
      have quad : (2:localRing 2)^(4*r-1)∣K^2 :=
        (pow_dvd_pow _ (show 4*r-1≤2*r+2*r by omega)).trans
          (by simpa only [pow_two] using mul_dvd_power kBase kBase)
      have lead : (2:localRing 2)^(4*r-1)∣K*S := by
        simpa only [show 4*r-1=2*r+(2*r-1) by omega] using mul_dvd_power kBase hs
      have sq : (2:localRing 2)^((4*r-2)+1)∣U^2-1 := by
        rw [show (4*r-2)+1=4*r-1 by omega]
        exact square_dvd hpL lead quad
      have mu : (2:localRing 2)^r∣(m:localRing 2) := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using
          (Nat.cast_dvd_cast (α := localRing 2) (two_div_box a b c r m hr ha hb hc hm))
      have mu1 : (2:localRing 2)∣(m:localRing 2) := by
        simpa only [pow_one] using (pow_dvd_pow _ (show 1≤r by omega)).trans mu
      have mu2 := pow_dvd_pow_of_dvd mu1 2
      rw [show 4*r=2+(4*r-2) by omega]
      exact mul_dvd_power mu2 (two_square_extract (4*r-2) u4 sq)
  · have u1 : (p:localRing p)∣U-1 :=
      (Nat.cast_dvd_cast (α := localRing p) hpC).trans unitProduct_one_mod
    have quad : (p:localRing p)^(4*r)∣K^2 := by
      simpa only [pow_two, show 4*r=2*r+2*r by omega] using mul_dvd_power kBase kBase
    have lead : (p:localRing p)^(4*r)∣K*S := by
      simpa only [show 4*r=2*r+2*r by omega] using mul_dvd_power kBase (hOdd hp)
    exact dvd_mul_of_dvd_right (odd_square_extract hp (4*r) u1 (square_dvd hpL lead quad)) _

lemma local_to_integral_box (a b c r : ℕ) (hr : 0<r)
    (hOdd : p≠2 → (p:localRing p)^(2*r)∣kernelSum p (a*p^r) (b*p^r))
    (hTwo : p=2 → (p:localRing p)^(2*r-1)∣kernelSum p (a*p^r) (b*p^r))
    (hEven : p=2 → Even (a*b) → (p:localRing p)^(2*r)∣kernelSum p (a*p^r) (b*p^r))
    (hParity : p=2 → Even c ∨ Odd a ∧ Odd b ∧ Odd c) :
    ∃ t : ℤ, box (a*p^r) (b*p^r) (c*p^r)-
      box (a*p^(r-1)) (b*p^(r-1)) (c*p^(r-1))^p = (p:ℚ)^(4*r)*t := by
  obtain ⟨v,hv⟩ := integer_box (a*p^r) (b*p^r) (c*p^r)
  obtain ⟨m,hm⟩ := integer_box (a*p^(r-1)) (b*p^(r-1)) (c*p^(r-1))
  have rescale (a : ℕ) : p*(a*p^(r-1))=a*p^r := by
    have e : p^r=p^(r-1)*p := by nth_rw 1 [show r=r-1+1 by omega]; rw [pow_succ]
    rw [e]
    ring
  have eqV : (v:localRing p)-(m:localRing p)^p =
      (m:localRing p)^p*(unitProduct p (a*p^r) (b*p^r) (c*p^r)-1) := by
    apply Subtype.ext
    change (v:ℚ)-(m:ℚ)^p=(m:ℚ)^p*((unitProduct p (a*p^r) (b*p^r) (c*p^r):ℚ)-1)
    have he := split (Fact.out : p.Prime).pos (a*p^(r-1)) (b*p^(r-1)) (c*p^(r-1))
    simp only [rescale,hm,hv] at he
    rw [unitProduct_coe,he]
    ring
  have dvdV : (p:localRing p)^(4*r)∣(v:localRing p)-(m:localRing p)^p := by
    rw [eqV]
    exact scaled_unit_delta a b c r m hr hm hOdd hTwo hEven hParity
  obtain ⟨u,hu⟩ := dvdV
  let Δ : ℤ := (v:ℤ)-(m:ℤ)^p
  have eqD : (Δ:ℚ)=(p:ℚ)^(4*r)*(u:ℚ) := by
    have hh := congrArg (fun z : localRing p => (z:ℚ)) hu
    dsimp [Δ]; push_cast
    exact_mod_cast hh
  obtain ⟨k,hk⟩ := int_from_local u.property eqD
  refine ⟨k,?_⟩
  rw [hm,hv]
  dsimp [Δ] at hk
  exact_mod_cast hk

end RectangularBox
namespace RectangularBox

open OMA.S_oeis_a352656
variable {p : ℕ} [Fact p.Prime]

lemma box_swap_ac (A B C : ℕ) : box A B C=box C B A := by
  rw [box_swap_ab A B C,box_swap_bc B A C,box_swap_ab B C A]

theorem fourth_from_kernel
    (a b c r : ℕ) (hr : 0<r)
    (hOdd : ∀ u v : ℕ, p≠2 → u≤v →
      (p:localRing p)^(2*r)∣kernelSum p (u*p^r) (v*p^r))
    (hTwo : ∀ u v : ℕ, p=2 → u≤v →
      (p:localRing p)^(2*r-1)∣kernelSum p (u*p^r) (v*p^r))
    (hEven : ∀ u v : ℕ, p=2 → u≤v → Even (u*v) →
      (p:localRing p)^(2*r)∣kernelSum p (u*p^r) (v*p^r)) :
    ∃ t : ℤ, box (a*p^r) (b*p^r) (c*p^r)-
      box (a*p^(r-1)) (b*p^(r-1)) (c*p^(r-1))^p = (p:ℚ)^(4*r)*t := by
  have g (u v w : ℕ) (hp : p=2 → Even w ∨ Odd u ∧ Odd v ∧ Odd w) :
      ∃ t : ℤ, box (u*p^r) (v*p^r) (w*p^r)-
        box (u*p^(r-1)) (v*p^(r-1)) (w*p^(r-1))^p = (p:ℚ)^(4*r)*t := by
    apply local_to_integral_box u v w r hr _ _ _ hp
    · intro hn
      rcases le_total u v with h|h
      · exact hOdd u v hn h
      · rw [kernelSum_swap]; exact hOdd v u hn h
    · intro hp2
      rcases le_total u v with h|h
      · exact hTwo u v hp2 h
      · rw [kernelSum_swap]; exact hTwo v u hp2 h
    · intro hp2 hev
      rcases le_total u v with h|h
      · exact hEven u v hp2 h hev
      · rw [kernelSum_swap]
        exact hEven v u hp2 h (mul_comm u v ▸ hev)
  by_cases hp : p=2
  · by_cases hc : Even c
    · exact g a b c (fun _ => Or.inl hc)
    by_cases hb : Even b
    · rw [box_swap_bc (a*p^r) (b*p^r) (c*p^r),
        box_swap_bc (a*p^(r-1)) (b*p^(r-1)) (c*p^(r-1))]
      exact g a c b (fun _ => Or.inl hb)
    by_cases ha : Even a
    · rw [box_swap_ac (a*p^r) (b*p^r) (c*p^r),
        box_swap_ac (a*p^(r-1)) (b*p^(r-1)) (c*p^(r-1))]
      exact g c b a (fun _ => Or.inl ha)
    exact g a b c (fun _ => Or.inr
      ⟨Nat.not_even_iff_odd.mp ha,Nat.not_even_iff_odd.mp hb,Nat.not_even_iff_odd.mp hc⟩)
  · exact g a b c (fun h => (hp h).elim)

end RectangularBox
open Finset

private theorem powLift {p k : ℕ} (hk : 0 < k) {x y : ℤ}
    (h : x ≡ y [ZMOD (p : ℤ) ^ k]) :
    x ^ p ≡ y ^ p [ZMOD (p : ℤ) ^ (k + 1)] := by
  have hp : (p : ℤ) ∣ (p : ℤ) ^ k := by
    simpa only [pow_one] using (pow_dvd_pow (p : ℤ) (show 1 ≤ k from hk))
  have hxy : (x : ZMod p) = (y : ZMod p) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub x y p).mpr (hp.trans h.dvd)
  have hgeom : (p : ℤ) ∣ ∑ i ∈ range p, y ^ i * x ^ (p - 1 - i) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    rw [← hxy]
    calc
      _ = ∑ _ ∈ range p, (x : ZMod p) ^ (p - 1) := by
        apply sum_congr rfl
        intro i hi
        rw [← pow_add, Nat.add_sub_of_le (by simpa using Nat.le_pred_of_lt (mem_range.mp hi))]
      _ = 0 := by simp
  apply Int.modEq_of_dvd
  have hd := mul_dvd_mul h.dvd hgeom
  rw [← pow_succ, mul_comm (y - x), geom_sum₂_mul] at hd
  exact hd

private theorem linearTower {p : ℕ} (hp : p.Prime) (a : ℕ → ℤ)
    (h : ∀ n, a (n + 1) ≡ a n ^ p [ZMOD (p : ℤ) ^ (4 * (n + 1))]) :
    ∀ n, a (n + 1) ≡ a n [ZMOD (p : ℤ) ^ (n + 1)] := by
  intro n
  induction n with
  | zero =>
    have : Fact p.Prime := ⟨hp⟩
    have hF : a 0 ^ p ≡ a 0 [ZMOD (p : ℤ) ^ 1] := by
      rw [pow_one, ← ZMod.intCast_eq_intCast_iff]
      push_cast
      exact ZMod.pow_card _
    exact ((h 0).of_dvd (pow_dvd_pow _ (by decide))).trans hF
  | succ n ih =>
    have high := (h (n+1)).of_dvd (pow_dvd_pow (p : ℤ) (show n + 1 + 1 ≤ 4 * (n+1+1) by omega))
    have prev := (h n).of_dvd (pow_dvd_pow (p : ℤ) (show n + 1 + 1 ≤ 4 * (n+1) by omega))
    exact high.trans ((powLift (by omega) ih).trans prev.symm)

open RectangularBox OMA.S_oeis_a352656 in
theorem OMA.solution : type_of% @OMA.S_oeis_a352656.main := by
  have fourth (p r a b c : ℕ) (hp : p.Prime) (hr : 0<r) :
      ∃ t : ℤ, box (a*p^r) (b*p^r) (c*p^r)-
        box (a*p^(r-1)) (b*p^(r-1)) (c*p^(r-1))^p = (p:ℚ)^(4*r)*t := by
    let _ : Fact p.Prime := ⟨hp⟩
    apply fourth_from_kernel a b c r hr
    · intro u v hne huv
      exact kernel_odd hr hne huv
    · intro u v he huv
      subst p
      simpa only [Nat.cast_ofNat] using kernel_two hr huv
    · intro u v he huv hprod
      subst p
      simpa only [Nat.cast_ofNat] using kernel_two_even hr huv hprod
  have seqFourth (p n r : ℕ) (hp : p.Prime) (_hn : 0<n) (hr : 0<r) :
      ∃ t : ℤ, a (n*p^r)-a (n*p^(r-1))^p=(p:ℚ)^(4*r)*t := by
    simpa only [a,Nat.mul_assoc] using fourth p r n n (2*n) hp hr
  refine ⟨fourth,?_,seqFourth⟩
  intro p n r hp hn hr
  let count (j : ℕ) : ℕ := (integer_box (n*p^j) (n*p^j) (2*(n*p^j))).choose
  have count_spec (j : ℕ) : a (n*p^j)=(count j:ℚ) :=
    (integer_box (n*p^j) (n*p^j) (2*(n*p^j))).choose_spec
  have high (j : ℕ) :
      (count (j+1):ℤ) ≡ (count j:ℤ)^p [ZMOD (p:ℤ)^(4*(j+1))] := by
    obtain ⟨m,hm⟩ := seqFourth p n (j+1) hp hn (by omega)
    rw [Nat.add_sub_cancel,count_spec,count_spec] at hm
    apply Int.modEq_of_dvd
    refine ⟨-m,?_⟩
    apply (Int.cast_inj (α:=ℚ)).mp
    push_cast
    linear_combination -hm
  have low := linearTower hp (fun j => (count j:ℤ)) high (r-1)
  have he : r-1+1=r := by omega
  rw [he] at low
  obtain ⟨m,hm⟩ := low.dvd
  refine ⟨-m,?_⟩
  rw [count_spec,count_spec]
  have h := congrArg (fun x : ℤ => (x:ℚ)) hm
  push_cast at h ⊢
  linear_combination -h
