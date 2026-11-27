import OMAReductions.R_Green95_green_95_variants_three_palindromes_R1_H2_R1

/-!
The long-number case of Cilleruelo, Luca and Baxter's three-palindrome theorem.

Use symmetric digit lists temporarily padded with leading and trailing zeros.
For lengths (k+2,k+1,k) and (k+3,k+1,k), the padded sums cover explicit
integer intervals. To grow each length by two, fix outer digits x,y and
choose z by the units congruence. The accessible intervals of inner sums
overlap as y increases, including the jump to the next x. At the final
step all three outer digits are positive, so the padded lists become actual
palindromes. Three overlapping ranges give the required leading digits.

There are two initial lengths per family. Their only nontrivial arithmetic
is a three- or four-column carry calculation. The free inner digit lies in
an interval, and the finite cover of the remaining digit inequalities is
verified by integer linear arithmetic.
-/

namespace G95Long
open Green95

def Pad (g l : ℕ) (v : ℤ) : Prop :=
  ∃ w : List ℕ, w.length=l ∧ w.reverse=w ∧ (∀ d ∈ w, d<g) ∧ ((Nat.ofDigits g w : ℕ) : ℤ)=v

def actual (g : ℕ) (v : ℤ) := ∃ n : ℕ, (n:ℤ)=v ∧ IsPalindrome g n

def triple (f h k : ℤ → Prop) (n : ℤ) := ∃ a b c, f a ∧ h b ∧ k c ∧ a+b+c=n

def wt (g : ℕ) (i : ℕ) : ℤ := (g:ℤ)^(i+1)+1

lemma wrap {g i : ℕ} (hg : 5≤g) {v x : ℤ} (h : Pad g i v) (hx : 0≤x ∧ x<g) :
    Pad g (i+2) (x*wt g i+g*v) ∧ (0<x → actual g (x*wt g i+g*v)) := by
  obtain ⟨x,rfl⟩ := Int.eq_ofNat_of_zero_le hx.1
  obtain ⟨w,hw,rev,ds,rfl⟩ := h
  let W := x :: (w ++ [x])
  have len : W.length=i+2 := by simp [W,hw]
  have symm : W.reverse=W := by simp [W,rev]
  have valid : ∀ d ∈ W, d<g := by
    simp only [W,List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
    rintro d (rfl|h|rfl)
    · omega
    · exact ds _ h
    · omega
  have eq : ((Nat.ofDigits g W : ℕ) : ℤ)=(x:ℤ)*wt g i+g*Nat.ofDigits g w := by
    simp only [W,Nat.ofDigits_cons,Nat.ofDigits_append,List.length_cons,hw,Nat.ofDigits_nil,
      mul_zero,add_zero,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,wt,pow_succ]
    ring
  refine ⟨⟨W,len,symm,valid,eq⟩,fun pos => ⟨Nat.ofDigits g W,eq,?_⟩⟩
  rw [IsPalindrome,Nat.digits_ofDigits _ (by omega) _ valid (by simp [W]; omega)]
  exact symm

def inside (g a b c : ℕ) := triple (Pad g a) (Pad g b) (Pad g c)
def done (g : ℕ) := triple (actual g) (actual g) (actual g)

lemma wrapThree {g a b c : ℕ} (hg : 5≤g) {q x y z : ℤ} (iq : inside g a b c q)
    (hx : 0≤x ∧ x<g) (hy : 0≤y ∧ y<g) (hz : 0≤z ∧ z<g) :
    let n := x*wt g a+y*wt g b+z*wt g c+g*q
    inside g (a+2) (b+2) (c+2) n ∧ (0<x → 0<y → 0<z → done g n) := by
  obtain ⟨u,v,w,hu,hv,hw,rfl⟩ := iq
  have h1 := wrap hg hu hx
  have h2 := wrap hg hv hy
  have h3 := wrap hg hw hz
  exact ⟨⟨_,_,_,h1.1,h2.1,h3.1,by ring⟩,
    fun X Y Z => ⟨_,_,_,h1.2 X,h2.2 Y,h3.2 Z,by ring⟩⟩

private lemma align {g m : ℤ} (hg : 5≤g) (hm : m=0 ∨ m=1) (n x y : ℤ) :
    ∃ Y Z k : ℤ, y-m ≤ Y ∧ Y ≤ y+m ∧ (m≤y ∧ y<g → m≤Y ∧ Y<g) ∧
      m ≤ Z ∧ Z<g ∧ x+Y+Z=n+k*g := by
  let r := (n-x-y)%g
  let k := -((n-x-y)/g)
  have hr₁ : 0≤r := Int.emod_nonneg _ (by omega)
  have hr₂ : r<g := Int.emod_lt_of_pos _ (by omega)
  have eq : x+y+r=n+k*g := by
    dsimp [r,k]; linarith [Int.emod_add_mul_ediv (n-x-y) g]
  by_cases h : m≤r
  · exact ⟨y,r,k,by omega,by omega,id,h,hr₂,eq⟩
  · have rz : r=0 := by omega
    by_cases endrow : y=g-1
    · exact ⟨y-1,1,k,by omega,by omega,by omega,by omega,by omega,by linarith⟩
    · exact ⟨y+1,g-1,k+1,by omega,by omega,by omega,by omega,by omega,by linarith⟩

private lemma walk {a b : ℤ} {P : ℤ → Prop} (h : a≤b) (base : P a)
    (step : ∀ j, a≤j → j<b → P j → P (j+1)) : P b := by
  obtain ⟨k,hk⟩ := Int.eq_ofNat_of_zero_le (show 0≤b-a by omega)
  have aux : ∀ i : ℕ, i≤k → P (a+i) := by
    intro i; induction i with
    | zero => intro _; simpa using base
    | succ i ih =>
      intro hi
      simpa [Nat.cast_succ,add_assoc] using step (a+i) (by omega) (by omega) (ih (by omega))
  simpa [show a+(k:ℤ)=b by omega] using aux k le_rfl

/-- For each pair of outer digits choose the third to match the units column.
The intervals of possible inner quotients overlap along each row and at the
transition to the next row. All three digit lengths may be different. -/
theorem grid {g m A B C lo hi L U n : ℤ} (hg : 5≤g) (hm : m=0 ∨ m=1) (hlh : lo≤hi)
    (hB : 0≤B) (hC : 0≤C) (a' b' c' : ℤ)
    (hA' : A=g*a'+1) (hB' : B=g*b'+1) (hC' : C=g*c'+1)
    (dy : (1+2*m)*B+(g-1-m)*C ≤ g*(U-L+1))
    (dx : lo=hi ∨ A+(3*m+1-g)*B+(g-1-m)*C ≤ g*(U-L+1))
    (start : lo*A+2*m*B+(g-1)*C+g*L ≤ n)
    (stop : n ≤ hi*A+(g-1-m)*B+m*C+g*U) :
    ∃ x y z q, lo≤x ∧ x≤hi ∧ m≤y ∧ y<g ∧ m≤z ∧ z<g ∧ L≤q ∧ q≤U ∧
      n=x*A+y*B+z*C+g*q := by
  choose Y Z K Yn Yp Yv Zn Zp E using align hg hm n
  let Q (x y : ℤ) := -(K x y+x*a'+Y x y*b'+Z x y*c')
  have eq (x y : ℤ) : n=x*A+Y x y*B+Z x y*C+g*(Q x y) := by
    dsimp [Q]; rw [hA',hB',hC']; linear_combination -(E x y)
  by_contra fail
  have jump (x y : ℤ) (hx : lo≤x ∧ x≤hi) (hy : m≤y ∧ y<g)
      (hL : L≤Q x y) : U<Q x y := by
    by_contra! h
    exact fail ⟨x,Y x y,Z x y,Q x y,hx.1,hx.2,(Yv x y hy).1,(Yv x y hy).2,
      Zn x y,Zp x y,hL,h,eq x y⟩
  have hop (x y x' y' : ℤ) (h : U<Q x y)
      (diff : x'*A+Y x' y'*B+Z x' y'*C-(x*A+Y x y*B+Z x y*C) ≤ g*(U-L+1)) :
      L≤Q x' y' := by
    by_contra! bad
    have le := mul_le_mul_of_nonneg_left (show U-L+2 ≤ Q x y-Q x' y' by omega) (show 0≤g by omega)
    linarith [eq x y,eq x' y']
  have bottom (x : ℤ) (hx : lo≤x ∧ x≤hi) (h : U<Q x m) : U<Q x (g-1) := by
    apply walk (P:=fun j => U<Q x j) (show m≤g-1 by omega) h
    intro y hy hy' old
    apply jump _ _ hx ⟨by omega,by omega⟩
    apply hop x y _ _ old
    have h1 := mul_le_mul_of_nonneg_right
      (show Y x (y+1)-Y x y≤1+2*m by linarith [Yp x (y+1),Yn x y]) hB
    have h2 := mul_le_mul_of_nonneg_right
      (show Z x (y+1)-Z x y≤g-1-m by have := Zp x (y+1); have := Zn x y; omega) hC
    linarith
  have first : U<Q lo m := by
    apply jump _ _ ⟨le_rfl,hlh⟩ ⟨le_rfl,by omega⟩
    by_contra! bad
    have h1 := mul_le_mul_of_nonneg_right (show Y lo m≤2*m by linarith [Yp lo m]) hB
    have h2 := mul_le_mul_of_nonneg_right (show Z lo m≤g-1 by have := Zp lo m; omega) hC
    have h3 := mul_le_mul_of_nonneg_left (show Q lo m≤L-1 by omega) (show 0≤g by omega)
    linarith [eq lo m]
  have last : U<Q hi m := by
    apply walk (P:=fun j => U<Q j m) hlh first
    intro x hx hx' old
    apply jump _ _ ⟨by omega,by omega⟩ ⟨le_rfl,by omega⟩
    apply hop x (g-1) _ _ (bottom x ⟨hx,by omega⟩ old)
    have h1 := mul_le_mul_of_nonneg_right (show Y (x+1) m-Y x (g-1) ≤ 3*m+1-g by
      linarith [Yp (x+1) m,Yn x (g-1)]) hB
    have h2 := mul_le_mul_of_nonneg_right (show Z (x+1) m-Z x (g-1) ≤ g-1-m by
      have := Zp (x+1) m; have := Zn x (g-1); omega) hC
    rcases dx with h | h
    · omega
    · linarith
  have high := bottom hi ⟨hlh,le_rfl⟩ last
  have h1 := mul_le_mul_of_nonneg_right (Yn hi (g-1)) hB
  have h2 := mul_le_mul_of_nonneg_right (Zn hi (g-1)) hC
  have h3 := mul_le_mul_of_nonneg_left (show U+1≤Q hi (g-1) by omega) (show 0≤g by omega)
  linarith [eq hi (g-1)]

def cov (g a b c : ℕ) (L U : ℤ) := ∀ n : ℤ, L≤n → n≤U → inside g a b c n
def LA (g : ℤ) (k : ℕ) := 2*g^k
def UA (g : ℤ) (k : ℕ) := g^(k+2)+g^(k+1)-g^k-3
def LB (g : ℤ) (k : ℕ) := g^(k+1)
def UB (g : ℤ) (k : ℕ) := g^(k+3)+g^k-3
def A (g k : ℕ) := cov g (k+2) (k+1) k (LA g k) (UA g k)
def B (g k : ℕ) := cov g (k+3) (k+1) k (LB g k) (UB g k)

def bottom (g m lo a b c l : ℤ) := lo*a+2*m*b+(g-1)*c+g*l
def top (g m hi a b c u : ℤ) := hi*a+(g-1-m)*b+m*c+g*u

theorem liftGrid {g a b c : ℕ} (hg : 5≤g) {m lo hi L U n : ℤ}
    (cv : cov g a b c L U) (hm : m=0 ∨ m=1) (hlim : m≤lo ∧ lo≤hi ∧ hi<g)
    (dy : (1+2*m)*wt g b+(g-1-m)*wt g c ≤ g*(U-L+1))
    (dx : lo=hi ∨ wt g a+(3*m+1-g)*wt g b+(g-1-m)*wt g c ≤ g*(U-L+1))
    (s : bottom g m lo (wt g a) (wt g b) (wt g c) L ≤ n)
    (t : n ≤ top g m hi (wt g a) (wt g b) (wt g c) U) :
    inside g (a+2) (b+2) (c+2) n ∧ (m=1 → done g n) := by
  obtain ⟨x,y,z,q,hx₁,hx₂,hy₁,hy₂,hz₁,hz₂,hL,hU,rfl⟩ := grid (by exact_mod_cast hg)
    hm hlim.2.1 (show 0≤wt g b by dsimp [wt]; positivity) (show 0≤wt g c by dsimp [wt]; positivity)
    ((g:ℤ)^a) ((g:ℤ)^b) ((g:ℤ)^c) (by simp [wt,pow_succ']) (by simp [wt,pow_succ'])
    (by simp [wt,pow_succ']) dy dx s t
  have ans := wrapThree hg (cv q hL hU) (x:=x) (y:=y) (z:=z)
    ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  exact ⟨ans.1,fun _ => ans.2 (by omega) (by omega) (by omega)⟩

/- Polynomial endpoint comparisons. Write the base as five plus a nonnegative
integer and its common power as one plus a nonnegative integer. -/
theorem stepA {g : ℕ} (hg : 5≤g) (j : ℕ) (old : A g (j+1)) : A g (j+3) := by
  intro n low high
  obtain ⟨s,hs⟩ := Int.eq_ofNat_of_zero_le (show 0≤(g:ℤ)-5 by omega)
  have hbase : (g:ℤ)=5+s := by omega
  have hpos : 0<(g:ℤ)^j := by positivity
  obtain ⟨t,ht⟩ := Int.eq_ofNat_of_zero_le (show 0≤(g:ℤ)^j-1 by omega)
  have hpw : (g:ℤ)^j=1+t := by omega
  apply (liftGrid hg (a:=j+1+2) (b:=j+1+1) (c:=j+1) (m:=0) (lo:=0) (hi:=(g:ℤ)-1) old
    (Or.inl rfl) ⟨by omega,by omega,by omega⟩ ?_ (Or.inr ?_) ?_ ?_).1
  · (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  · (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  · apply le_trans _ low; (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  · apply le_trans high; (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))

theorem stepB {g : ℕ} (hg : 5≤g) (j : ℕ) (old : B g (j+2)) : B g (j+4) := by
  intro n low high
  obtain ⟨s,hs⟩ := Int.eq_ofNat_of_zero_le (show 0≤(g:ℤ)-5 by omega)
  have hbase : (g:ℤ)=5+s := by omega
  have hpos : 0<(g:ℤ)^j := by positivity
  obtain ⟨t,ht⟩ := Int.eq_ofNat_of_zero_le (show 0≤(g:ℤ)^j-1 by omega)
  have hpw : (g:ℤ)^j=1+t := by omega
  apply (liftGrid hg (a:=j+2+3) (b:=j+2+1) (c:=j+2) (m:=0) (lo:=0) (hi:=(g:ℤ)-1) old
    (Or.inl rfl) ⟨by omega,by omega,by omega⟩ ?_ (Or.inr ?_) ?_ ?_).1
  · (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  · (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  · apply le_trans _ low; (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  · apply le_trans high; (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))

theorem allA {g : ℕ} (hg : 5≤g) (base1 : A g 1) (base2 : A g 2) : ∀ k, A g (k+1) := by
  intro k; induction k using Nat.twoStepInduction with
  | zero => exact base1
  | one => exact base2
  | more j ih _ => exact stepA hg j ih

theorem allB {g : ℕ} (hg : 5≤g) (base2 : B g 2) (base3 : B g 3) : ∀ k, B g (k+2) := by
  intro k; induction k using Nat.twoStepInduction with
  | zero => exact base2
  | one => exact base3
  | more j ih _ => exact stepB hg j ih

theorem longFromBases {g : ℕ} (hg : 5≤g) (hA₁ : A g 1) (hA₂ : A g 2)
    (hB₂ : B g 2) (hB₃ : B g 3) (j : ℕ) (n : ℤ) (lo : (g:ℤ)^(j+6)≤n)
    (hi : n<(g:ℤ)^(j+7)) : done g n := by
  obtain ⟨s,hs⟩ := Int.eq_ofNat_of_zero_le (show 0≤(g:ℤ)-5 by omega)
  have hbase : (g:ℤ)=5+s := by omega
  have hpos : 0<(g:ℤ)^j := by positivity
  obtain ⟨t,ht⟩ := Int.eq_ofNat_of_zero_le (show 0≤(g:ℤ)^j-1 by omega)
  have hpw : (g:ℤ)^j=1+t := by omega
  by_cases s₀ : n≤top g 1 ((g:ℤ)-1) (wt g (j+2+2)) (wt g (j+2+1)) (wt g (j+2)) (UA g (j+2))
  · apply (liftGrid hg (m:=1) (lo:=1) (hi:=(g:ℤ)-1) (allA hg hA₁ hA₂ (j+1))
      (Or.inr rfl) ⟨le_rfl,by omega,by omega⟩ ?_ (Or.inr ?_) ?_ s₀).2 rfl
    · (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
    · (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
    · apply le_trans _ lo; (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  by_cases s₁ : n≤top g 1 1 (wt g (j+2+3)) (wt g (j+2+1)) (wt g (j+2)) (UB g (j+2))
  · apply (liftGrid hg (m:=1) (lo:=1) (hi:=1) (allB hg hB₂ hB₃ j)
      (Or.inr rfl) ⟨le_rfl,le_rfl,by omega⟩ ?_ (Or.inl rfl) ?_ s₁).2 rfl
    · (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
    · apply le_trans _ (le_of_not_ge s₀); (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  apply (liftGrid hg (m:=1) (lo:=1) (hi:=(g:ℤ)-1) (allA hg hA₁ hA₂ (j+2))
    (Or.inr rfl) ⟨le_rfl,by omega,by omega⟩ ?_ (Or.inr ?_) ?_ ?_).2 rfl
  · (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  · (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  · apply le_trans _ (le_of_not_ge s₁); (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  · apply le_trans hi.le; (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))

theorem fromBases (ba₁ : ∀ g, 5≤g → A g 1) (ba₂ : ∀ g, 5≤g → A g 2)
    (bb₂ : ∀ g, 5≤g → B g 2) (bb₃ : ∀ g, 5≤g → B g 3) :
    OMA.R_Green95_green_95_variants_three_palindromes_R1_H2_R1.H2 := by
  intro g hg n lo
  let l := (Nat.digits g n).length
  have big : 6<l := (Nat.lt_digits_length_iff (by omega) n).mpr lo
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (show 7≤l by omega)
  have hj' : l=j+7 := by omega
  have lb : g^(j+6)≤n := (Nat.lt_digits_length_iff (by omega) n).mp (by change j+6<l; omega)
  have ub : n<g^(j+7) := hj' ▸ Nat.lt_base_pow_length_digits (m:=n) (by omega : 1<g)
  obtain ⟨x,y,z,⟨p,hp,hP⟩,⟨q,hq,hQ⟩,⟨r,hr,hR⟩,eq⟩ :=
    longFromBases hg (ba₁ g hg) (ba₂ g hg) (bb₂ g hg) (bb₃ g hg) j n (by exact_mod_cast lb) (by exact_mod_cast ub)
  exact ⟨p,q,r,hP,hQ,hR,by omega⟩

abbrev dig (g a : ℤ) := 0≤a ∧ a<g

def coreA (g n : ℤ) := ∃ b c d e : ℤ, dig g b ∧ dig g c ∧ dig g d ∧ dig g e ∧
  b*(g^2+g)+c*(g^2+1)+d*g+e*(g+1)=n
def coreB (g n : ℤ) := ∃ b c d e : ℤ, dig g b ∧ dig g c ∧ dig g d ∧ dig g e ∧
  b*g^2+c*(g^2+1)+d*g+e*(g+1)=n
def coreC (g n : ℤ) := ∃ z a b c d : ℤ,
  dig g z ∧ dig g a ∧ dig g b ∧ dig g c ∧ dig g d ∧
  z*(g^3+g^2)+a*(g^3+1)+b*(g^2+g)+c*(g^2+1)+d*g=n

private def loW (g S T : ℤ) := max 0 (max (S-g+1) (T-g+1))
private def hiW (g S T : ℤ) := min (g-1) (min S T)

/-- A free digit w contributes with coefficient two to one middle column. -/
private lemma chooseW {l h a b u : ℤ} (hh : l≤h) (hab : a<b)
    (hl : 2*l+u≤b) (hu : a≤2*h+u) :
    ∃ w : ℤ, l≤w ∧ w≤h ∧ a≤2*w+u ∧ 2*w+u≤b := by
  exact ⟨max l ((a-u+1)/2),by omega,by omega,by omega,by omega⟩

private lemma buildA {g n S T U : ℤ} (hg : 5≤g)
    (h1 : loW g S T ≤ hiW g S T) (h2 : 2*loW g S T+U<g)
    (h3 : 0≤2*hiW g S T+U)
    (eq : ∀ w : ℤ, (T-w)*(g^2+g)+w*(g^2+1)+(U+2*w)*g+(S-w)*(g+1)=n) :
    coreA g n := by
  obtain ⟨w,wl,wh,el,eh⟩ := chooseW h1 (show 0<g-1 by omega) (by omega : 2*loW g S T+U≤g-1) h3
  dsimp [loW,hiW] at wl wh
  exact ⟨T-w,w,U+2*w,S-w,⟨by omega,by omega⟩,⟨by omega,by omega⟩,
    ⟨by omega,by omega⟩,⟨by omega,by omega⟩,eq w⟩

private lemma buildB {g n S T U : ℤ}
    (h : max (loW g S T) (-U) ≤ min (hiW g S T) (g-1-U))
    (eq : ∀ w : ℤ, (T-w)*g^2+w*(g^2+1)+(U+w)*g+(S-w)*(g+1)=n) : coreB g n := by
  let w := max (loW g S T) (-U)
  have wl : loW g S T ≤ w := le_max_left _ _
  have wh : w ≤ hiW g S T := le_trans h (min_le_left _ _)
  have hU : dig g (U+w) := by
    dsimp [w]; have := le_trans h (min_le_right _ _); constructor <;> omega
  dsimp [loW,hiW] at wl wh
  exact ⟨T-w,w,U+w,S-w,⟨by omega,by omega⟩,⟨by omega,by omega⟩,hU,
    ⟨by omega,by omega⟩,eq w⟩

private lemma buildC {g n S T U V : ℤ}
    (h1 : loW g S T ≤ hiW g S T) (h2 : max 0 (V-g+1) < min (g-1) V)
    (h3 : 2*loW g S T+U ≤ min (g-1) V)
    (h4 : max 0 (V-g+1) ≤ 2*hiW g S T+U)
    (eq : ∀ w : ℤ, (T-w)*(g^3+g^2)+w*(g^3+1)+(U+2*w)*(g^2+g)+
      (S-w)*(g^2+1)+(V-U-2*w)*g=n) : coreC g n := by
  obtain ⟨w,wl,wh,el,eh⟩ := chooseW h1 h2 h3 h4
  dsimp [loW,hiW] at wl wh
  exact ⟨T-w,w,U+2*w,S-w,V-U-2*w,⟨by omega,by omega⟩,⟨by omega,by omega⟩,
    ⟨by omega,by omega⟩,⟨by omega,by omega⟩,⟨by omega,by omega⟩,eq w⟩

theorem digitsA {g c e f : ℤ} (hg : 5≤g) (hc : 2≤c ∧ c≤g+2)
    (he : dig g e) (hf : dig g f) : coreA g (c*g^2+e*g+f) := by
  obtain ⟨he₁,he₂⟩ := he
  obtain ⟨hf₁,hf₂⟩ := hf
  have h : (0 ≤ - c + e + f ∧ 0 ≤ c + e - f) ∨
      (0 ≤ c - e + f - 2 ∧ 0 ≤ g - c + f ∧ 0 ≤ 2*g - c - e + f - 2) ∨
      (0 ≤ c - f - 2 ∧ 0 ≤ g - f - 2 ∧ 0 ≤ 2*g - c + e - f - 2) := by omega
  rcases h with h | h | h
  · apply buildA hg (S:=f) (T:=c) (U:=- c + e - f)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildA hg (S:=f) (T:=c - 1) (U:=g - c + e - f + 1)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildA hg (S:=g + f) (T:=c - 1) (U:=- c + e - f)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega

theorem digitsB {g c e f : ℤ} (hg : 5≤g) (hc : 1≤c ∧ c≤g+1)
    (he : dig g e) (hf : dig g f) : coreB g (c*g^2+e*g+f) := by
  obtain ⟨he₁,he₂⟩ := he
  obtain ⟨hf₁,hf₂⟩ := hf
  have h : (0 ≤ c + e - f ∧ 0 ≤ g - c + f - 1) ∨
      (0 ≤ - e + f - 1 ∧ 0 ≤ g - c - e + f - 1) ∨
      (0 ≤ c - f - 2 ∧ 0 ≤ g - f - 2) := by omega
  rcases h with h | h | h
  · apply buildB (S:=f) (T:=c) (U:=e - f)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildB (S:=f) (T:=c - 1) (U:=g + e - f)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildB (S:=g + f) (T:=c - 1) (U:=e - f - 1)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega

theorem digitsC {g c d e f : ℤ} (hg : 5≤g) (hc : 2≤c ∧ c≤g+2)
    (hd : dig g d) (he : dig g e) (hf : dig g f) : coreC g (c*g^3+d*g^2+e*g+f) := by
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨he₁,he₂⟩ := he
  obtain ⟨hf₁,hf₂⟩ := hf
  have h : (0 ≤ - c + d + f ∧ 0 ≤ e - 1 ∧ 0 ≤ c - d + e + f ∧ 0 ≤ c + d - f) ∨
      (0 ≤ - g + c - d + e + f - 1 ∧ 0 ≤ e - 1 ∧ 0 ≤ g - c - d + e + f - 1 ∧ 0 ≤ g - c + f) ∨
      (0 ≤ - c + d - e + f - 2 ∧ 0 ≤ c + d - e - f - 2) ∨
      (0 ≤ c - d + f - 1 ∧ 0 ≤ g - c + f ∧ 0 ≤ g - c + d - e + f - 1 ∧ 0 ≤ g - e - 3 ∧ 0 ≤ g + c + d - e - f - 3) ∨
      (0 ≤ e - 2 ∧ 0 ≤ c - d + e - f - 4 ∧ 0 ≤ c - f - 2 ∧ 0 ≤ g - f - 2 ∧ 0 ≤ 2*g - c - d + e + f - 2 ∧ 0 ≤ 2*g - c + d - f - 1) ∨
      (0 ≤ c - f - 2 ∧ 0 ≤ c + d - e - f - 2 ∧ 0 ≤ g - e - 2 ∧ 0 ≤ g - f - 2 ∧ 0 ≤ 2*g - c + d - e - f - 2) ∨
      (0 ≤ c - d - f - 4 ∧ 0 ≤ g - e - 2) := by omega
  rcases h with h | h | h | h | h | h | h
  · apply buildC (S:=f) (T:=c) (U:=- c + d - f) (V:=e)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildC (S:=f) (T:=c - 1) (U:=g - c + d - f + 1) (V:=e)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildC (S:=f) (T:=c) (U:=- c + d - f - 1) (V:=g + e)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildC (S:=f) (T:=c - 1) (U:=g - c + d - f) (V:=g + e)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildC (S:=g + f) (T:=c - 1) (U:=- c + d - f + 1) (V:=e - 1)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildC (S:=g + f) (T:=c - 1) (U:=- c + d - f) (V:=g + e - 1)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildC (S:=g + f) (T:=c - 2) (U:=g - c + d - f + 1) (V:=g + e - 1)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega

private lemma splitBlock {b n l u : ℤ} (hb : 0<b) (lo : l*b ≤ n) (hi : n<(u+1)*b) :
    ∃ q r : ℤ, l≤q ∧ q≤u ∧ 0≤r ∧ r<b ∧ n=q*b+r := by
  have eq := Int.emod_add_ediv_mul n b
  have r₁ := Int.emod_nonneg n (by omega : b≠0)
  have r₂ := Int.emod_lt_of_pos n hb
  refine ⟨n/b,n%b,?_,?_,r₁,r₂,by linarith⟩
  · by_contra! h
    have := mul_le_mul_of_nonneg_right (show n/b≤l-1 by omega) hb.le
    linarith
  · by_contra! h
    have := mul_le_mul_of_nonneg_right (show u+1≤n/b by omega) hb.le
    linarith

private lemma twoLow {g r : ℤ} (hg : 5≤g) (h : 0≤r ∧ r<g^2) :
    ∃ e f, dig g e ∧ dig g f ∧ r=e*g+f := by
  obtain ⟨e,f,he,he',hf,hf',eq⟩ := splitBlock (b:=g) (l:=0) (u:=g-1) (by omega)
    (by simpa using h.1) (by nlinarith [h.2])
  exact ⟨e,f,⟨he,by omega⟩,⟨hf,hf'⟩,eq⟩

private lemma coreArange {g n : ℤ} (hg : 5≤g) (lo : 2*g^2≤n) (hi : n<(g+3)*g^2) :
    coreA g n := by
  obtain ⟨c,r,h₁,h₂,hr,hr',eq⟩ := splitBlock (b:=g^2) (u:=g+2) (by positivity) lo (by linarith)
  obtain ⟨e,f,he,hf,rfl⟩ := twoLow hg ⟨hr,hr'⟩
  rw [eq,←add_assoc]; exact digitsA hg ⟨h₁,h₂⟩ he hf

private lemma coreBrange {g n : ℤ} (hg : 5≤g) (lo : g^2≤n) (hi : n<(g+2)*g^2) :
    coreB g n := by
  obtain ⟨c,r,h₁,h₂,hr,hr',eq⟩ := splitBlock (b:=g^2) (l:=1) (u:=g+1) (by positivity)
    (by simpa using lo) (by linarith)
  obtain ⟨e,f,he,hf,rfl⟩ := twoLow hg ⟨hr,hr'⟩
  rw [eq,←add_assoc]; exact digitsB hg ⟨h₁,h₂⟩ he hf

private lemma coreCrange {g n : ℤ} (hg : 5≤g) (lo : 2*g^3≤n) (hi : n<(g+3)*g^3) :
    coreC g n := by
  obtain ⟨c,r,h₁,h₂,hr,hr',eq⟩ := splitBlock (b:=g^3) (l:=2) (u:=g+2) (by positivity) lo (by linarith)
  obtain ⟨d,r',hd,hd',hh,hh',er⟩ := splitBlock (b:=g^2) (l:=0) (u:=g-1) (by positivity)
    (by simpa using hr) (by nlinarith)
  obtain ⟨e,f,he,hf,er'⟩ := twoLow hg ⟨hh,hh'⟩
  rw [eq,er,er']; simp only [←add_assoc]
  exact digitsC hg ⟨h₁,h₂⟩ ⟨hd,by omega⟩ he hf

private def maxCoreA (g : ℤ) := (g-1)*((g^2+g)+(g^2+1)+g+(g+1))
private lemma coreAwide {g n : ℤ} (hg : 5≤g) (lo : 2*g^2≤n) (hi : n ≤ maxCoreA g-2*g^2) :
    coreA g n := by
  by_cases h : n<(g+3)*g^2
  · exact coreArange hg lo h
  have hm : maxCoreA g-n<(g+3)*g^2 := by dsimp [maxCoreA] at *; nlinarith [sq_nonneg g]
  obtain ⟨b,c,d,e,hb,hc,hd,he,eq⟩ := coreArange hg (n:=maxCoreA g-n) (by omega) hm
  obtain ⟨hb₁,hb₂⟩ := hb
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨he₁,he₂⟩ := he
  exact ⟨g-1-b,g-1-c,g-1-d,g-1-e,⟨by omega,by omega⟩,⟨by omega,by omega⟩,
    ⟨by omega,by omega⟩,⟨by omega,by omega⟩,by dsimp [maxCoreA] at eq; linarith⟩

private lemma coin {g w l u n : ℤ} (hg : 5≤g) (hw : 0<w) (space : w≤u-l+1)
    (lo : l≤n) (hi : n≤u+(g-1)*w) : ∃ a q, dig g a ∧ l≤q ∧ q≤u ∧ n=a*w+q := by
  let a := (n-l)/w
  have ad : 0≤a := Int.ediv_nonneg (by omega) hw.le
  have r₁ := Int.emod_nonneg (n-l) (by omega : w≠0)
  have r₂ := Int.emod_lt_of_pos (n-l) hw
  have eq : (n-l)%w+a*w=n-l := Int.emod_add_ediv_mul _ _
  by_cases h : a<g
  · exact ⟨a,l+(n-l)%w,⟨ad,h⟩,by omega,by omega,by linarith⟩
  · have le := mul_le_mul_of_nonneg_right (show g-1≤a by omega) hw.le
    exact ⟨g-1,n-(g-1)*w,⟨by omega,by omega⟩,by linarith,by linarith,by ring⟩

private lemma pad1 {g : ℕ} {x : ℤ} (hx : dig g x) :
    Pad g 1 (x) := by
  obtain ⟨x,rfl⟩ := Int.eq_ofNat_of_zero_le hx.1
  have hx' : x<g := by exact_mod_cast hx.2
  exact ⟨[x],rfl,rfl,by simp_all,by simp [Nat.ofDigits]⟩

private lemma pad2 {g : ℕ} {x : ℤ} (hx : dig g x) :
    Pad g 2 (x*(g+1)) := by
  obtain ⟨x,rfl⟩ := Int.eq_ofNat_of_zero_le hx.1
  have hx' : x<g := by exact_mod_cast hx.2
  exact ⟨[x,x],rfl,rfl,by simp_all,by simp [Nat.ofDigits]; ring⟩

private lemma pad3 {g : ℕ} {x y : ℤ} (hx : dig g x) (hy : dig g y) :
    Pad g 3 (x*(g^2+1)+y*g) := by
  obtain ⟨x,rfl⟩ := Int.eq_ofNat_of_zero_le hx.1
  have hx' : x<g := by exact_mod_cast hx.2
  obtain ⟨y,rfl⟩ := Int.eq_ofNat_of_zero_le hy.1
  have hy' : y<g := by exact_mod_cast hy.2
  exact ⟨[x,y,x],rfl,rfl,by simp_all,by simp [Nat.ofDigits]; ring⟩

private lemma pad4 {g : ℕ} {x y : ℤ} (hx : dig g x) (hy : dig g y) :
    Pad g 4 (x*(g^3+1)+y*(g^2+g)) := by
  obtain ⟨x,rfl⟩ := Int.eq_ofNat_of_zero_le hx.1
  have hx' : x<g := by exact_mod_cast hx.2
  obtain ⟨y,rfl⟩ := Int.eq_ofNat_of_zero_le hy.1
  have hy' : y<g := by exact_mod_cast hy.2
  exact ⟨[x,y,y,x],rfl,rfl,by simp_all,by simp [Nat.ofDigits]; ring⟩

private lemma pad5 {g : ℕ} {x y z : ℤ} (hx : dig g x) (hy : dig g y) (hz : dig g z) :
    Pad g 5 (x*(g^4+1)+y*(g^3+g)+z*g^2) := by
  obtain ⟨x,rfl⟩ := Int.eq_ofNat_of_zero_le hx.1
  have hx' : x<g := by exact_mod_cast hx.2
  obtain ⟨y,rfl⟩ := Int.eq_ofNat_of_zero_le hy.1
  have hy' : y<g := by exact_mod_cast hy.2
  obtain ⟨z,rfl⟩ := Int.eq_ofNat_of_zero_le hz.1
  have hz' : z<g := by exact_mod_cast hz.2
  exact ⟨[x,y,z,y,x],rfl,rfl,by simp_all,by simp [Nat.ofDigits]; ring⟩

private lemma pad6 {g : ℕ} {x y z : ℤ} (hx : dig g x) (hy : dig g y) (hz : dig g z) :
    Pad g 6 (x*(g^5+1)+y*(g^4+g)+z*(g^3+g^2)) := by
  obtain ⟨x,rfl⟩ := Int.eq_ofNat_of_zero_le hx.1
  have hx' : x<g := by exact_mod_cast hx.2
  obtain ⟨y,rfl⟩ := Int.eq_ofNat_of_zero_le hy.1
  have hy' : y<g := by exact_mod_cast hy.2
  obtain ⟨z,rfl⟩ := Int.eq_ofNat_of_zero_le hz.1
  have hz' : z<g := by exact_mod_cast hz.2
  exact ⟨[x,y,z,z,y,x],rfl,rfl,by simp_all,by simp [Nat.ofDigits]; ring⟩

theorem smallA1 (g : ℕ) (hg : 5≤g) : A g 1 := by
  intro n lo hi
  let G : ℤ := g
  have hg' : 5≤G := by dsimp [G]; exact_mod_cast hg
  obtain ⟨j,hj⟩ := Int.eq_ofNat_of_zero_le (show 0≤G-5 by omega)
  have H : G=5+j := by omega
  change LA G 1 ≤ n at lo
  change n ≤ UA G 1 at hi
  obtain ⟨a,s,ha,ls,hs,eq₁⟩ := coin (g:=G) (l:=0) (u:=2*G^2-2) (w:=G^2+1) hg'
    (by positivity) (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)) (le_trans (by dsimp [LA]; positivity) lo)
    (le_trans hi (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)))
  obtain ⟨c,t,hc,lt,ht,eq₂⟩ := coin (g:=G) (l:=0) (u:=G^2-1) (w:=G+1) hg'
    (by omega) (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)) ls (le_trans hs (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)))
  obtain ⟨b,d,hb,ld,hd,eq₃⟩ := coin (g:=G) (l:=0) (u:=G-1) (w:=G) hg'
    (by omega) (by omega) lt (le_trans ht (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)))
  exact ⟨_,_,_,pad3 (g:=g) ha hb,pad2 hc,pad1 ⟨ld,by omega⟩,by change a*(G^2+1)+b*G+c*(G+1)+d=n; linarith⟩

theorem smallA2 (g : ℕ) (hg : 5≤g) : A g 2 := by
  intro n lo hi
  let G : ℤ := g
  have hg' : 5≤G := by dsimp [G]; exact_mod_cast hg
  obtain ⟨j,hj⟩ := Int.eq_ofNat_of_zero_le (show 0≤G-5 by omega)
  have H : G=5+j := by omega
  change n≤UA G 2 at hi
  obtain ⟨a,r,ha,lr,hr,eq⟩ := coin (g:=G) (l:=2*G^2) (u:=maxCoreA G-2*G^2) (w:=G^3+1) hg'
    (by positivity) (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)) lo (le_trans hi (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)))
  obtain ⟨b,c,d,e,hb,hc,hd,he,h⟩ := coreAwide hg' lr hr
  exact ⟨_,_,_,pad4 (g:=g) ha hb,pad3 hc hd,pad2 he,
    by change a*(G^3+1)+b*(G^2+G)+(c*(G^2+1)+d*G)+e*(G+1)=n; linarith⟩

theorem smallB2 (g : ℕ) (hg : 5≤g) : B g 2 := by
  intro n lo hi
  let G : ℤ := g
  have hg' : 5≤G := by dsimp [G]; exact_mod_cast hg
  obtain ⟨j,hj⟩ := Int.eq_ofNat_of_zero_le (show 0≤G-5 by omega)
  have H : G=5+j := by omega
  change LB G 2 ≤ n at lo
  change n ≤ UB G 2 at hi
  obtain ⟨x,s,hx,ls,hs,eq₁⟩ := coin (g:=G) (l:=(G^2)) (u:=((G+2)*G^2-1+(G-1)*(G^3+G))) (w:=G^4+1) hg'
    (by positivity) (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)) (le_trans (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)) lo) (le_trans hi (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)))
  obtain ⟨y,r,hy,lr,hr,eq₂⟩ := coin (g:=G) (l:=(G^2)) (u:=(G+2)*G^2-1) (w:=(G^3+G)) hg'
    (by positivity) (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)) ls hs
  obtain ⟨z,b,c,d,hz,hb,hc,hd,eq₃⟩ := coreBrange hg' lr (by omega)
  exact ⟨_,_,_,pad5 (g:=g) hx hy hz,pad3 hb hc,pad2 hd,
    by change x*(G^4+1)+y*(G^3+G)+z*G^2+(b*(G^2+1)+c*G)+d*(G+1)=n; linarith⟩

theorem smallB3 (g : ℕ) (hg : 5≤g) : B g 3 := by
  intro n lo hi
  let G : ℤ := g
  have hg' : 5≤G := by dsimp [G]; exact_mod_cast hg
  obtain ⟨j,hj⟩ := Int.eq_ofNat_of_zero_le (show 0≤G-5 by omega)
  have H : G=5+j := by omega
  change LB G 3 ≤ n at lo
  change n ≤ UB G 3 at hi
  obtain ⟨x,s,hx,ls,hs,eq₁⟩ := coin (g:=G) (l:=(2*G^3)) (u:=((G+3)*G^3-1+(G-1)*(G^4+G))) (w:=G^5+1) hg'
    (by positivity) (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)) (le_trans (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)) lo) (le_trans hi (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)))
  obtain ⟨y,r,hy,lr,hr,eq₂⟩ := coin (g:=G) (l:=(2*G^3)) (u:=(G+3)*G^3-1) (w:=(G^4+G)) hg'
    (by positivity) (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)) ls hs
  obtain ⟨z,b,c,d,e,hz,hb,hc,hd,he,eq₃⟩ := coreCrange hg' lr (by omega)
  exact ⟨_,_,_,pad6 (g:=g) hx hy hz,pad4 hb hc,pad3 hd he,
    by change x*(G^5+1)+y*(G^4+G)+z*(G^3+G^2)+(b*(G^3+1)+c*(G^2+G))+(d*(G^2+1)+e*G)=n; linarith⟩

end G95Long

theorem OMA.solution : OMA.R_Green95_green_95_variants_three_palindromes_R1_H2_R1.H2 :=
  G95Long.fromBases G95Long.smallA1 G95Long.smallA2 G95Long.smallB2 G95Long.smallB3
