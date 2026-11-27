import OMAReductions.R_Green95_green_95_variants_three_palindromes_R1_H2_R1

/-! Five and six digits in the three-palindrome problem of Cilleruelo, Luca and Baxter.

For five digits choose a five-digit palindrome leaving a remainder of at least g².
Backing up one prefix avoids the exceptional three-digit remainder when necessary.
For six digits, adding two five-digit palindromes permits independent middle digit
sums between 0 and 2g-2. Fixing the carry into the second leading column to one
then lets us finish with a six-digit palindrome for all leading digits at least
three. Smaller leading digits need a short table of carry choices. All its cells
are linear inequalities in the base and the digits, checked below by omega.

The digit constructors and three-digit classification are adapted from
@marcusbuffett, open-math-agents PR 2948. -/
namespace G95Med
open Green95

private lemma zeroPal (g : ℕ) : IsPalindrome g 0 := by simp [IsPalindrome]

private lemma one {g a : ℕ} (hg : 5 ≤ g) (hu : a < g) :
    IsPalindrome g (a) := by
  by_cases hz : a=0
  · simpa [hz] using zeroPal g
  have eq : Nat.ofDigits g [a] = a := by simp [Nat.ofDigits]
  rw [← eq, IsPalindrome, Nat.digits_ofDigits _ (by omega) _ (by simp_all) (by simp_all)]
  rfl

private lemma two {g a : ℕ} (hg : 5 ≤ g) (hu : a < g) :
    IsPalindrome g (a*(g+1)) := by
  by_cases hz : a=0
  · simpa [hz] using zeroPal g
  have eq : Nat.ofDigits g [a,a] = a*(g+1) := by simp [Nat.ofDigits]; ring
  rw [← eq, IsPalindrome, Nat.digits_ofDigits _ (by omega) _ (by simp_all) (by simp_all)]
  rfl

private lemma three {g a b : ℕ} (hg : 5 ≤ g) (ha : 0 < a) (hu : a < g) (hb : b < g) :
    IsPalindrome g (a*(g^2+1)+b*g) := by
  have eq : Nat.ofDigits g [a,b,a] = a*(g^2+1)+b*g := by simp [Nat.ofDigits]; ring
  rw [← eq, IsPalindrome, Nat.digits_ofDigits _ (by omega) _ (by simp_all) (by simp_all; omega)]
  rfl

private lemma four {g a b : ℕ} (hg : 5 ≤ g) (ha : 0 < a) (hu : a < g) (hb : b < g) :
    IsPalindrome g (a*(g^3+1)+b*g*(g+1)) := by
  have eq : Nat.ofDigits g [a,b,b,a] = a*(g^3+1)+b*g*(g+1) := by simp [Nat.ofDigits]; ring
  rw [← eq, IsPalindrome, Nat.digits_ofDigits _ (by omega) _ (by simp_all) (by simp_all; omega)]
  rfl

private lemma shortClass {g a b c : ℕ} (hg : 5 ≤ g) (ha : a<g) (hb : b<g) (hc : c<g) :
    let n := a*g^2+b*g+c
    (∃ p q, IsPalindrome g p ∧ IsPalindrome g q ∧ p+q=n) ∨
    (∃ u, 1 ≤ u ∧ u < g ∧ n+1 = u*(g+1)) ∨ n=2*g^2+1 := by
  dsimp only
  by_cases h0 : a=0
  · subst a
    simp only [zero_mul,zero_add]
    by_cases hbc : b ≤ c
    · left
      refine ⟨_,_,two hg hb,one hg (show c-b < g by omega),?_⟩
      rw [Nat.mul_add, Nat.mul_one]; omega
    · by_cases edge : c+1=b
      · right; left; exact ⟨b,by omega,hb,by rw [Nat.mul_add,Nat.mul_one]; omega⟩
      · left
        obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
        refine ⟨_,_,two hg (show j < g by omega),one hg (show g+c-j < g by omega),?_⟩
        rw [Nat.succ_mul,Nat.mul_add,Nat.mul_one]; omega
  by_cases ca : a ≤ c
  · left
    refine ⟨_,_,three hg (by omega) ha hb,one hg (show c-a < g by omega),?_⟩
    rw [Nat.mul_add,Nat.mul_one]; omega
  by_cases b0 : b=0
  · subst b
    simp only [zero_mul,add_zero]
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    by_cases j0 : j=0
    · subst j; have : c=0 := by omega
      subst c; left
      refine ⟨_,_,two hg (show g-1<g by omega),one hg (show 1<g by omega),?_⟩
      zify [show 1≤g by omega]; ring
    by_cases edge : c=j
    · subst c
      by_cases j1 : j=1
      · right; right; simp [j1]
      · left
        obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero j0
        refine ⟨_,_,three hg (by decide : 0<1) (by omega) (by omega : 1<g),
          three hg (by omega : 0<u) (by omega) (show g-1<g by omega),?_⟩
        zify [show 1≤g by omega]; ring
    · left
      refine ⟨_,_,three hg (by omega : 0<j) (by omega) (show g-1<g by omega),
        one hg (show g+c-j<g by omega),?_⟩
      zify [show 1≤g by omega,show j≤g+c by omega]; ring
  · left
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero b0
    refine ⟨_,_,three hg (by omega) ha (show j<g by omega),
      one hg (show g+c-a<g by omega),?_⟩
    zify [show a≤g+c by omega]; ring

private lemma classify {g n : ℕ} (hg : 5 ≤ g) (hn : n<g^3) :
    (∃ p q, IsPalindrome g p ∧ IsPalindrome g q ∧ p+q=n) ∨
    (∃ u, 1 ≤ u ∧ u < g ∧ n+1 = u*(g+1)) ∨ n=2*g^2+1 := by
  let a := n/g/g
  let b := n/g%g
  let c := n%g
  have ha : a<g := by
    dsimp [a]; rw [Nat.div_lt_iff_lt_mul (by omega),Nat.div_lt_iff_lt_mul (by omega)]
    simpa [pow_succ] using hn
  have e1 : c+g*(n/g)=n := Nat.mod_add_div _ _
  have e2 : b+g*a=n/g := Nat.mod_add_div _ _
  have e : a*g^2+b*g+c=n := by linear_combination e1 + g*e2
  rw [←e]
  exact shortClass hg ha (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))

private lemma five {g a b c : ℕ} (hg : 5 ≤ g) (ha : 0 < a) (hu : a < g) (hb : b < g)
    (hc : c < g) : IsPalindrome g (a*(g^4+1)+b*(g^3+g)+c*g^2) := by
  have eq : Nat.ofDigits g [a,b,c,b,a] = a*(g^4+1)+b*(g^3+g)+c*g^2 := by
    simp [Nat.ofDigits]; ring
  rw [← eq, IsPalindrome, Nat.digits_ofDigits _ (by omega) _ (by simp_all) (by simp_all; omega)]
  rfl

private abbrev SumThree (g n : ℕ) :=
  ∃ p q r, IsPalindrome g p ∧ IsPalindrome g q ∧ IsPalindrome g r ∧ p+q+r=n

private lemma fill {g n p : ℕ} (hg : 5 ≤ g) (hp : IsPalindrome g p)
    (lo : p+g^2 ≤ n) (hi : n < p+g^3) (ne : n≠p+2*g^2+1) : SumThree g n := by
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le (show p ≤ n by omega)
  rcases classify hg (show r < g^3 by omega) with ⟨x,y,hx,hy,h⟩ | ⟨u,hu,hug,h⟩ | h
  · exact ⟨p,x,y,hp,hx,hy,by omega⟩
  · have le := Nat.mul_le_mul_right (g+1) (show u ≤ g-1 by omega)
    zify [show 1≤g by omega] at le h lo hr
    nlinarith
  · omega

private lemma fiveDigits {g n : ℕ} (hg : 5 ≤ g) (hn₁ : g^4 ≤ n) (hn₂ : n < g^5) :
    SumThree g n := by
  let a := n/g^4
  let b := (n%g^4)/g^3
  let t := (n%g^4)%g^3
  have ha : 0<a := by dsimp [a]; exact Nat.div_pos hn₁ (by positivity)
  have ha' : a<g := by
    dsimp [a]; rw [Nat.div_lt_iff_lt_mul (by positivity)]; simpa [pow_succ,mul_comm] using hn₂
  have hb : b<g := by
    dsimp [b]; rw [Nat.div_lt_iff_lt_mul (by positivity)]
    simpa [pow_succ,mul_comm] using Nat.mod_lt n (show 0<g^4 by positivity)
  have ht : t<g^3 := Nat.mod_lt _ (by positivity)
  have e1 : n%g^4+g^4*a=n := Nat.mod_add_div _ _
  have e2 : t+g^3*b=n%g^4 := Nat.mod_add_div _ _
  have en : n=a*g^4+b*g^3+t := by linear_combination -e1-e2
  clear_value a b t
  clear e1 e2 hn₁ hn₂
  let p := a*(g^4+1)+b*(g^3+g)
  have hp : IsPalindrome g p := by simpa [p] using five hg ha ha' hb (show 0<g by omega)
  by_cases big : p+g^2 ≤ n
  · by_cases ex : n=p+2*g^2+1
    · exact ⟨_,_,_,five hg ha ha' hb (show 1<g by omega),
        three hg (show 0<1 by decide) (by omega) (show 0<g by omega),zeroPal g,
        by rw [ex]; dsimp [p]; ring⟩
    · apply fill hg hp big _ ex
      dsimp [p]; nlinarith
  have hbase : 4*g^2+g+2 < g^3 := by
    nlinarith [Nat.mul_le_mul_right (g^2) hg,
      Nat.mul_le_mul_right g hg]
  have hab : b*g+a < g^2 := by
    have le := Nat.mul_le_mul_right g (show b+1 ≤ g by omega)
    nlinarith
  dsimp [p] at big
  by_cases bz : b=0
  · subst b
    by_cases az : a=1
    · subst a
      apply fill hg (four hg (show 0<g-1 by omega) (by omega) (show g-3<g by omega))
      all_goals zify [show 1≤g by omega,show 3≤g by omega] at *; nlinarith
    · apply fill hg (five hg (show 0<a-1 by omega) (by omega) (show g-1<g by omega)
        (show g-3<g by omega))
      all_goals zify [show 1≤a by omega,show 1≤g by omega,show 3≤g by omega] at *; nlinarith
  · apply fill hg (five hg ha ha' (show b-1<g by omega) (show g-3<g by omega))
    all_goals zify [show 1≤b by omega,show 3≤g by omega] at *; nlinarith

private abbrev digit (g x : ℤ) := 0 ≤ x ∧ x < g
private abbrev dbl (g x : ℤ) := 0 ≤ x ∧ x ≤ 2*g-2

private lemma splitPair {g v : ℤ} (l : ℤ)
    (hv : 2*l ≤ v ∧ v ≤ 2*g-2) :
    ∃ a b, l ≤ a ∧ a < g ∧ l ≤ b ∧ b < g ∧ a+b=v := by
  by_cases h : v-l<g
  · exact ⟨l,v-l,by omega,by omega,by omega,by omega,by omega⟩
  · exact ⟨g-1,v-(g-1),by omega,by omega,by omega,by omega,by omega⟩

private def p5 (g a b c : ℤ) := a*(g^4+1)+b*(g^3+g)+c*g^2
private def p6 (g a b c : ℤ) := a*(g^5+1)+b*(g^4+g)+c*(g^3+g^2)
private def num (g a b c d e f : ℤ) := a*g^5+b*g^4+c*g^3+d*g^2+e*g+f
private abbrev ThreeI (g : ℕ) (v : ℤ) := ∃ n : ℕ, (n : ℤ)=v ∧ SumThree g n

private lemma pal5I {g : ℕ} (hg : 5≤g) {a b c : ℤ} (ha : 0<a ∧ a<g)
    (hb : digit g b) (hc : digit g c) :
    ∃ n : ℕ, (n : ℤ)=p5 g a b c ∧ IsPalindrome g n := by
  obtain ⟨a,rfl⟩ := Int.eq_ofNat_of_zero_le (show 0≤a by omega)
  obtain ⟨b,rfl⟩ := Int.eq_ofNat_of_zero_le hb.1
  obtain ⟨c,rfl⟩ := Int.eq_ofNat_of_zero_le hc.1
  exact ⟨a*(g^4+1)+b*(g^3+g)+c*g^2,by simp [p5],five hg (by omega) (by omega) (by have := hb.2; omega) (by have := hc.2; omega)⟩

private lemma pal6I {g : ℕ} (hg : 5≤g) {a b c : ℤ} (ha : 0<a ∧ a<g)
    (hb : digit g b) (hc : digit g c) :
    ∃ n : ℕ, (n : ℤ)=p6 g a b c ∧ IsPalindrome g n := by
  obtain ⟨a,rfl⟩ := Int.eq_ofNat_of_zero_le (show 0≤a by omega)
  obtain ⟨b,rfl⟩ := Int.eq_ofNat_of_zero_le hb.1
  obtain ⟨c,rfl⟩ := Int.eq_ofNat_of_zero_le hc.1
  have eq : Nat.ofDigits g [a,b,c,c,b,a] = a*(g^5+1)+b*(g^4+g)+c*(g^3+g^2) := by
    simp [Nat.ofDigits]; ring
  refine ⟨a*(g^5+1)+b*(g^4+g)+c*(g^3+g^2),by simp [p6],?_⟩
  rw [← eq, IsPalindrome, Nat.digits_ofDigits _ (by omega) _ (by simp_all [digit])
    (by simp_all [digit]; omega)]
  rfl

private lemma twoFives {g : ℕ} (hg : 5≤g) {a b c : ℤ} (ha : 2≤a ∧ a≤2*g-2)
    (hb : dbl g b) (hc : dbl g c) :
    ∃ p q : ℕ, (p:ℤ)+q=p5 g a b c ∧ IsPalindrome g p ∧ IsPalindrome g q := by
  obtain ⟨a₁,a₂,ha₁,ha₁',ha₂,ha₂',rfl⟩ := splitPair 1 ha
  obtain ⟨b₁,b₂,hb₁,hb₁',hb₂,hb₂',rfl⟩ := splitPair 0 hb
  obtain ⟨c₁,c₂,hc₁,hc₁',hc₂,hc₂',rfl⟩ := splitPair 0 hc
  obtain ⟨p,hp,hP⟩ := pal5I hg ⟨ha₁,ha₁'⟩ ⟨hb₁,hb₁'⟩ ⟨hc₁,hc₁'⟩
  obtain ⟨q,hq,hQ⟩ := pal5I hg ⟨ha₂,ha₂'⟩ ⟨hb₂,hb₂'⟩ ⟨hc₂,hc₂'⟩
  exact ⟨p,q,by rw [hp,hq]; dsimp [p5]; ring,hP,hQ⟩

private lemma residue {g : ℤ} (hg : 0<g) (lo x : ℤ) :
    ∃ y k : ℤ, lo ≤ y ∧ y < lo+g ∧ y=x+k*g := by
  refine ⟨lo+(x-lo)%g,-((x-lo)/g),?_,?_,?_⟩
  · have := Int.emod_nonneg (x-lo) (by omega : g≠0); omega
  · have := Int.emod_lt_of_pos (x-lo) hg; omega
  · linarith [Int.emod_add_mul_ediv (x-lo) g]

private lemma boundsCarry {g s d k : ℤ} (hg : 0<g) (hs : 0 ≤ s ∧ s < 3*g)
    (hd : digit g d) (h : s=d+k*g) : 0≤k ∧ k≤2 := by
  obtain ⟨hd₁,hd₂⟩ := hd
  constructor
  · by_contra! bad
    have := mul_le_mul_of_nonneg_right (show k≤ -1 by omega) hg.le
    linarith
  · by_contra! bad
    have := mul_le_mul_of_nonneg_right (show 3≤k by omega) hg.le
    linarith

private lemma center {g t d k : ℤ} (hg : 5≤g) (ht : 1≤t ∧ t≤g) (hd : digit g d)
    (hk : 0≤k ∧ k≤2) :
    ∃ c z j : ℤ, digit g c ∧ dbl g z ∧ c+j=t ∧ c+z+k=d+j*g := by
  obtain ⟨hd₁,hd₂⟩ := hd
  by_cases lo : 0≤d+g-t+1-k
  · by_cases hi : d+g-t+1-k≤2*g-2
    · exact ⟨t-1,d+g-t+1-k,1,by constructor <;> omega,⟨lo,hi⟩,by omega,by ring⟩
    · refine ⟨t,d-t-k,0,⟨by omega,by omega⟩,⟨by omega,by omega⟩,by omega,by ring⟩
  · refine ⟨t-2,d+2*g-t+2-k,2,⟨by omega,by omega⟩,⟨by omega,by omega⟩,by omega,by ring⟩

private lemma finish655 {g : ℕ} (hg : 5≤g) {a b c d e f x y X k₁ k₅ : ℤ}
    (hc : digit g c) (hd : digit g d) (he : digit g e) (hf : digit g f)
    (hx : 0<x ∧ x<g) (hy : digit g y) (hX : 2≤X ∧ X≤2*g-2)
    (h₀ : x+X=f+k₁*g) (h₄ : y+X+1=b+k₅*g) (h₅ : x+k₅=a) :
    ThreeI g (num g a b c d e f) := by
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hy₁,hy₂⟩ := hy
  obtain ⟨he₁,he₂⟩ := he
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  have hk₁ := boundsCarry (by omega) ⟨by omega,by omega⟩ hf h₀
  obtain ⟨Y,k₂,hY₁,hY₂,hY⟩ := residue (g:=(g:ℤ)) (by omega) c (e-y-k₁)
  have h₁ : y+Y+k₁=e+k₂*g := by linarith
  have hk₂ := boundsCarry (by omega) ⟨by omega,by omega⟩ ⟨he₁,he₂⟩ h₁
  obtain ⟨z,Z,k₃,hz,hZ,hz',h₂⟩ := center hg' (t:=c+g-Y) ⟨by omega,by omega⟩ hd hk₂
  obtain ⟨p,hp,hP⟩ := pal6I hg hx ⟨hy₁,hy₂⟩ hz
  obtain ⟨q,r,hqr,hQ,hR⟩ := twoFives hg (b:=Y) hX ⟨by omega,by omega⟩ hZ
  refine ⟨p+q+r,?_,p,q,r,hP,hQ,hR,rfl⟩
  push_cast
  rw [add_assoc,hp,hqr]
  dsimp [p6,p5,num]
  linear_combination h₀ + (g:ℤ)*h₁ + (g:ℤ)^2*h₂ + (g:ℤ)^3*hz' + (g:ℤ)^4*h₄ + (g:ℤ)^5*h₅

private lemma pal3I {g : ℕ} (hg : 5≤g) {a b : ℤ} (ha : 0<a ∧ a<g) (hb : digit g b) :
    ∃ n : ℕ, (n : ℤ)=a*(g^2+1)+b*g ∧ IsPalindrome g n := by
  obtain ⟨a,rfl⟩ := Int.eq_ofNat_of_zero_le (show 0≤a by omega)
  obtain ⟨b,rfl⟩ := Int.eq_ofNat_of_zero_le hb.1
  exact ⟨a*(g^2+1)+b*g,by simp,three hg (by omega) (by omega) (by have := hb.2; omega)⟩

private lemma general553 {g : ℕ} (hg : 5≤g) {b c d e f z k₁ : ℤ}
    (hb : digit g b) (hc : digit g c) (hd : digit g d) (he : digit g e) (hf : digit g f)
    (hz : 0<z ∧ z<g) (safe : z+2≤g ∨ 0<d)
    (h₀ : (g:ℤ)+b-1+z=f+k₁*g) : ThreeI g (num g 1 b c d e f) := by
  obtain ⟨hb₁,hb₂⟩ := hb
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hd₁,hd₂⟩ := hd
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  have hk₁ := boundsCarry (by omega) ⟨by omega,by omega⟩ hf h₀
  obtain ⟨w,k₂,hw₁,hw₂,hw⟩ := residue (g:=(g:ℤ)) (by omega) 0 (e-(g+c-1)-k₁)
  have h₁ : (g:ℤ)+c-1+w+k₁=e+k₂*g := by linarith
  have hk₂ := boundsCarry (by omega) ⟨by omega,by omega⟩ he h₁
  obtain ⟨p,q,hpq,hP,hQ⟩ := twoFives hg (a:=(g:ℤ)+b-1) (b:=(g:ℤ)+c-1)
    (c:=(g:ℤ)+d-k₂-z) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  obtain ⟨r,hr,hR⟩ := pal3I hg hz ⟨hw₁,by omega⟩
  refine ⟨p+q+r,?_,p,q,r,hP,hQ,hR,rfl⟩
  push_cast; rw [hpq,hr]; dsimp [num,p5]
  linear_combination h₀ + (g:ℤ)*h₁

private def edgeOne (g b d f : ℤ) : Prop :=
  (b ≤ 3 ∧ (f=b-1 ∨ f=g+b-1)) ∨ (b ≤ 4 ∧ d=0 ∧ (f=b-2 ∨ f=g+b-2))
private def edgeTwo (b f : ℤ) : Prop :=
  (b=0 ∧ (f=1 ∨ f=2)) ∨ (b=1 ∧ f=2)

private lemma leadingOne {g : ℕ} (hg : 5≤g) {b c d e f : ℤ}
    (hb : digit g b) (hc : digit g c) (hd : digit g d) (he : digit g e) (hf : digit g f)
    (good : ¬edgeOne g b d f) : ThreeI g (num g 1 b c d e f) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨z,k,hz₁,hz₂,hz⟩ := residue (g:=(g:ℤ)) (by omega) 0 (f-(g+b-1))
  have h₀ : (g:ℤ)+b-1+z=f+k*g := by linarith
  by_cases ok : 0<z ∧ (z+2≤g ∨ 0<d)
  · exact general553 hg hb hc hd he hf ⟨ok.1,by omega⟩ ok.2 h₀
  obtain ⟨hb₁,hb₂⟩ := hb
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨hf₁,hf₂⟩ := hf
  have hk := boundsCarry (by omega) ⟨by omega,by omega⟩ ⟨hf₁,hf₂⟩ h₀
  have hcase : 2≤f-1 ∧ f≤b := by
    dsimp [edgeOne] at good
    obtain ⟨kl,ku⟩ := hk
    interval_cases k <;> simp_all <;> omega
  exact finish655 hg hc ⟨hd₁,hd₂⟩ he ⟨hf₁,hf₂⟩ (x:=1) (y:=b-f) (X:=f-1)
    (k₁:=0) (k₅:=0) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    ⟨by omega,by omega⟩ (by ring) (by ring) (by ring)

private lemma leadingMany {g : ℕ} (hg : 5≤g) {a b c d e f : ℤ}
    (ha : 2≤a ∧ a<g) (hb : digit g b) (hc : digit g c) (hd : digit g d)
    (he : digit g e) (hf : digit g f) (good : a≠2 ∨ ¬edgeTwo b f) :
    ThreeI g (num g a b c d e f) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hb₁,hb₂⟩ := hb
  obtain ⟨X,k,hX₁,hX₂,hX⟩ := residue (g:=(g:ℤ)) (by omega) b (f-(a-1))
  by_cases h : 2≤X
  · exact finish655 hg hc hd he hf (x:=a-1) (y:=b+g-X-1) (X:=X) (k₁:=k) (k₅:=1)
      ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨h,by omega⟩ (by linarith) (by ring) (by ring)
  have h₀ : a-1+X=f+k*g := by linarith
  obtain ⟨hf₁,hf₂⟩ := hf
  have hk := boundsCarry (by omega) ⟨by omega,by omega⟩ ⟨hf₁,hf₂⟩ h₀
  have a₂ : 2<a := by
    dsimp [edgeTwo] at good
    obtain ⟨kl,ku⟩ := hk
    interval_cases k <;> simp_all <;> omega
  exact finish655 hg hc hd he ⟨hf₁,hf₂⟩ (x:=a-2) (y:=b+g-X-2) (X:=X+g+1)
    (k₁:=k+1) (k₅:=2) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    ⟨by omega,by omega⟩ (by linarith) (by ring) (by ring)

private lemma pal4I {g : ℕ} (hg : 5≤g) {a b : ℤ} (ha : 0<a ∧ a<g) (hb : digit g b) :
    ∃ n : ℕ, (n : ℤ)=a*(g^3+1)+b*g*(g+1) ∧ IsPalindrome g n := by
  obtain ⟨a,rfl⟩ := Int.eq_ofNat_of_zero_le (show 0≤a by omega)
  obtain ⟨b,rfl⟩ := Int.eq_ofNat_of_zero_le hb.1
  exact ⟨a*(g^3+1)+b*g*(g+1),by simp,four hg (by omega) (by omega) (by have := hb.2; omega)⟩

private lemma form553 {g : ℕ} (hg : 5≤g) {v X Y Z z w : ℤ}
    (hX : 2≤X ∧ X≤2*g-2) (hY : dbl g Y) (hZ : dbl g Z)
    (hz : 0<z ∧ z<g) (hw : digit g w) (eq : p5 g X Y Z + z*(g^2+1)+w*g=v) :
    ThreeI g v := by
  obtain ⟨p,q,hpq,hP,hQ⟩ := twoFives hg hX hY hZ
  obtain ⟨r,hr,hR⟩ := pal3I hg hz hw
  exact ⟨p+q+r,by push_cast; rw [hpq,hr]; linarith,p,q,r,hP,hQ,hR,rfl⟩

private lemma form554 {g : ℕ} (hg : 5≤g) {v X Y Z z w : ℤ}
    (hX : 2≤X ∧ X≤2*g-2) (hY : dbl g Y) (hZ : dbl g Z)
    (hz : 0<z ∧ z<g) (hw : digit g w) (eq : p5 g X Y Z + z*(g^3+1)+w*g*(g+1)=v) :
    ThreeI g v := by
  obtain ⟨p,q,hpq,hP,hQ⟩ := twoFives hg hX hY hZ
  obtain ⟨r,hr,hR⟩ := pal4I hg hz hw
  exact ⟨p+q+r,by push_cast; rw [hpq,hr]; linarith,p,q,r,hP,hQ,hR,rfl⟩

/- In a 6+5+4 digit pattern, the free middle digit w must fit the three
digit intervals for S-w, T-w and U+2*w as well as its own interval. -/
private lemma form654 {g : ℕ} (hg : 5≤g) {v x y z B S T U : ℤ}
    (hx : 0<x ∧ x<g) (hy : 0<y ∧ y<g) (hz : 0<z ∧ z<g) (hB : digit g B)
    (hS : dbl g S) (hT : dbl g T) (hST : S-T<g ∧ T-S<g)
    (hu₁ : 0≤2*((g:ℤ)-1)+U ∧ 0≤2*S+U ∧ 0≤2*T+U)
    (hu₂ : U<g ∧ 2*(S-g+1)+U<g ∧ 2*(T-g+1)+U<g)
    (eq : ∀ w : ℤ, p6 g x B (T-w)+p5 g y w (U+2*w)+
      (z*(g^3+1)+(S-w)*g*(g+1))=v) : ThreeI g v := by
  obtain ⟨hs₁,hs₂⟩ := hS
  obtain ⟨ht₁,ht₂⟩ := hT
  let w := max 0 (max (S-g+1) (max (T-g+1) ((1-U)/2)))
  have hw : digit g w := by dsimp [w,digit]; constructor <;> omega
  have hsw : digit g (S-w) := by dsimp [w,digit]; constructor <;> omega
  have htw : digit g (T-w) := by dsimp [w,digit]; constructor <;> omega
  have huw : digit g (U+2*w) := by dsimp [w,digit]; constructor <;> omega
  obtain ⟨p,hp,hP⟩ := pal6I hg hx hB htw
  obtain ⟨q,hq,hQ⟩ := pal5I hg hy hw huw
  obtain ⟨r,hr,hR⟩ := pal4I hg hz hsw
  exact ⟨p+q+r,by push_cast; rw [hp,hq,hr]; exact eq w,p,q,r,hP,hQ,hR,rfl⟩

private lemma exceptional0 {g : ℕ} (hg : 5≤g) {c d e : ℤ}
    (hc : digit g c) (hd : digit g d) (he : digit g e) :
    ThreeI g (num g (1) (0) (c) (d) (e) ((g:ℤ) - 1)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ - c + e ∧ 0 ≤ c - 1) ∨
      (0 ≤ c - e - 1) ∨
      (0 ≤ - c ∧ 0 ≤ (g:ℤ) + c - e - 3 ∧ 0 ≤ (g:ℤ) + c + d - e - 4) ∨
      (0 ≤ - (g:ℤ) - c + e + 2 ∧ 0 ≤ - c) ∨
      (0 ≤ - c ∧ 0 ≤ - d + 1 ∧ 0 ≤ (g:ℤ) + c - e - 3) := by omega
  rcases h with h | h | h | h | h
  · apply form553 hg (X:=(g:ℤ)) (Y:=c - 1) (Z:=d + 1) (z:=(g:ℤ) - 1) (w:=- c + e)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form553 hg (X:=(g:ℤ)) (Y:=c - 1) (Z:=d) (z:=(g:ℤ) - 1) (w:=(g:ℤ) - c + e)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form554 hg (X:=(g:ℤ) - 2) (Y:=2*(g:ℤ) + c - 2) (Z:=(g:ℤ) + c + d - e - 4) (z:=1) (w:=- c + e + 2)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form554 hg (X:=(g:ℤ) - 2) (Y:=2*(g:ℤ) + c - 2) (Z:=2*(g:ℤ) + c + d - e - 3) (z:=1) (w:=- (g:ℤ) - c + e + 2)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form553 hg (X:=(g:ℤ) - 2) (Y:=2*(g:ℤ) + c - 2) (Z:=2*(g:ℤ) + d - 3) (z:=1) (w:=- c + e + 2)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)

private lemma exceptional1 {g : ℕ} (hg : 5≤g) {c d e : ℤ}
    (hc : digit g c) (hd : digit g d) (he : digit g e) :
    ThreeI g (num g (1) (1) (c) (d) (e) (0)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ c - e ∧ 0 ≤ c - 1) ∨
      (0 ≤ - c + e - 1 ∧ 0 ≤ c - 1) ∨
      (0 ≤ - c ∧ 0 ≤ (g:ℤ) + c - e - 2 ∧ 0 ≤ (g:ℤ) + c + d - e - 3) ∨
      (0 ≤ - (g:ℤ) - c + e + 1) ∨
      (0 ≤ - c ∧ 0 ≤ - d + 1 ∧ 0 ≤ (g:ℤ) + c - e - 2) := by omega
  rcases h with h | h | h | h | h
  · apply form553 hg (X:=(g:ℤ) + 1) (Y:=c - 1) (Z:=d) (z:=(g:ℤ) - 1) (w:=(g:ℤ) - c + e - 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form553 hg (X:=(g:ℤ) + 1) (Y:=c - 1) (Z:=d + 1) (z:=(g:ℤ) - 1) (w:=- c + e - 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form554 hg (X:=(g:ℤ) - 1) (Y:=2*(g:ℤ) + c - 2) (Z:=(g:ℤ) + c + d - e - 3) (z:=1) (w:=- c + e + 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form554 hg (X:=(g:ℤ) - 1) (Y:=2*(g:ℤ) + c - 2) (Z:=2*(g:ℤ) + c + d - e - 2) (z:=1) (w:=- (g:ℤ) - c + e + 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form553 hg (X:=(g:ℤ) - 1) (Y:=2*(g:ℤ) + c - 2) (Z:=2*(g:ℤ) + d - 3) (z:=1) (w:=- c + e + 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)

private lemma exceptional2 {g : ℕ} (hg : 5≤g) {c d e : ℤ}
    (hc : digit g c) (hd : digit g d) (he : digit g e) :
    ThreeI g (num g (1) (2) (c) (d) (e) (1)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ e - 1 ∧ 0 ≤ c - d + e - 2) ∨
      (0 ≤ c - e) ∨
      (0 ≤ - c + d + e - 2 ∧ 0 ≤ e - 1 ∧ 0 ≤ c + d - e + 2) ∨
      (0 ≤ - c ∧ 0 ≤ (g:ℤ) + c - e - 2 ∧ 0 ≤ (g:ℤ) + c + d - e - 3) := by omega
  rcases h with h | h | h | h
  · apply form654 hg (x:=1) (y:=1) (z:=(g:ℤ) - 1) (B:=0) (S:=e - 1) (T:=c) (U:=(g:ℤ) - c + d - e + 1)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=1) (z:=(g:ℤ) - 1) (B:=0) (S:=(g:ℤ) + e - 1) (T:=c) (U:=- c + d - e)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=1) (z:=(g:ℤ) - 1) (B:=0) (S:=e - 1) (T:=c + 1) (U:=- c + d - e)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form554 hg (X:=(g:ℤ)) (Y:=2*(g:ℤ) + c - 2) (Z:=(g:ℤ) + c + d - e - 3) (z:=1) (w:=- c + e + 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)

private lemma exceptional3 {g : ℕ} (hg : 5≤g) {c d e : ℤ}
    (hc : digit g c) (hd : digit g d) (he : digit g e) :
    ThreeI g (num g (1) (3) (c) (d) (e) (2)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ e - 1 ∧ 0 ≤ c - d + e - 2) ∨
      (0 ≤ c - e) ∨
      (0 ≤ - c + d + e - 2 ∧ 0 ≤ e - 1 ∧ 0 ≤ c + d - e + 2) ∨
      (0 ≤ - c ∧ 0 ≤ (g:ℤ) + c - e - 2 ∧ 0 ≤ (g:ℤ) + c + d - e - 3) := by omega
  rcases h with h | h | h | h
  · apply form654 hg (x:=1) (y:=2) (z:=(g:ℤ) - 1) (B:=0) (S:=e - 1) (T:=c) (U:=(g:ℤ) - c + d - e + 1)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=2) (z:=(g:ℤ) - 1) (B:=0) (S:=(g:ℤ) + e - 1) (T:=c) (U:=- c + d - e)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=2) (z:=(g:ℤ) - 1) (B:=0) (S:=e - 1) (T:=c + 1) (U:=- c + d - e)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form554 hg (X:=(g:ℤ) + 1) (Y:=2*(g:ℤ) + c - 2) (Z:=(g:ℤ) + c + d - e - 3) (z:=1) (w:=- c + e + 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)

private lemma exceptional4 {g : ℕ} (hg : 5≤g) {c e : ℤ}
    (hc : digit g c) (he : digit g e) :
    ThreeI g (num g (1) (0) (c) (0) (e) ((g:ℤ) - 2)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ - c + e + 1 ∧ 0 ≤ (g:ℤ) + c - e - 2) ∨
      (0 ≤ c - e - 1) ∨
      (0 ≤ - c + e - 1) := by omega
  rcases h with h | h | h
  · apply form553 hg (X:=(g:ℤ) - 1) (Y:=(g:ℤ) + c - 2) (Z:=(g:ℤ)) (z:=(g:ℤ) - 1) (w:=- c + e + 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form553 hg (X:=(g:ℤ)) (Y:=c - 1) (Z:=1) (z:=(g:ℤ) - 2) (w:=(g:ℤ) - c + e)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form554 hg (X:=(g:ℤ) - 1) (Y:=c) (Z:=(g:ℤ) + c - e + 1) (z:=(g:ℤ) - 1) (w:=- c + e - 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)

private lemma exceptional5 {g : ℕ} (hg : 5≤g) {c e : ℤ}
    (hc : digit g c) (he : digit g e) :
    ThreeI g (num g (1) (1) (c) (0) (e) ((g:ℤ) - 1)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ - c + e + 1 ∧ 0 ≤ (g:ℤ) + c - e - 2) ∨
      (0 ≤ c - e - 1) ∨
      (0 ≤ - c + e - 1) := by omega
  rcases h with h | h | h
  · apply form553 hg (X:=(g:ℤ)) (Y:=(g:ℤ) + c - 2) (Z:=(g:ℤ)) (z:=(g:ℤ) - 1) (w:=- c + e + 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form553 hg (X:=(g:ℤ) + 1) (Y:=c - 1) (Z:=1) (z:=(g:ℤ) - 2) (w:=(g:ℤ) - c + e)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form554 hg (X:=(g:ℤ)) (Y:=c) (Z:=(g:ℤ) + c - e + 1) (z:=(g:ℤ) - 1) (w:=- c + e - 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)

private lemma exceptional6 {g : ℕ} (hg : 5≤g) {c e : ℤ}
    (hc : digit g c) (he : digit g e) :
    ThreeI g (num g (1) (2) (c) (0) (e) (0)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ e - 1 ∧ 0 ≤ (g:ℤ) - c + e - 3) ∨
      (0 ≤ c - e + 1 ∧ 0 ≤ 2*(g:ℤ) - c - e - 3) := by omega
  rcases h with h | h
  · apply form654 hg (x:=1) (y:=1) (z:=(g:ℤ) - 2) (B:=0) (S:=e - 1) (T:=c + 1) (U:=(g:ℤ) - c - e)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=1) (z:=(g:ℤ) - 2) (B:=0) (S:=(g:ℤ) + e - 1) (T:=c + 1) (U:=- c - e - 1)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)

private lemma exceptional7 {g : ℕ} (hg : 5≤g) {c e : ℤ}
    (hc : digit g c) (he : digit g e) :
    ThreeI g (num g (1) (3) (c) (0) (e) (1)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ (g:ℤ) - c + e - 2 ∧ 0 ≤ (g:ℤ) + c - e - 2) ∨
      (0 ≤ e - 2 ∧ 0 ≤ c + e - 3) ∨
      (0 ≤ - (g:ℤ) + c - e + 2 ∧ 0 ≤ - (g:ℤ) + c + 1) := by omega
  rcases h with h | h | h
  · apply form654 hg (x:=1) (y:=1) (z:=(g:ℤ) - 1) (B:=0) (S:=(g:ℤ) + e - 1) (T:=(g:ℤ) + c - 1) (U:=- c - e + 1)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=1) (z:=(g:ℤ) - 1) (B:=1) (S:=e - 2) (T:=c) (U:=(g:ℤ) - c - e + 2)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=2) (z:=(g:ℤ) - 2) (B:=1) (S:=(g:ℤ) + e - 2) (T:=- (g:ℤ) + c + 1) (U:=(g:ℤ) - c - e)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)

private lemma exceptional8 {g : ℕ} (hg : 5≤g) {c e : ℤ}
    (hc : digit g c) (he : digit g e) :
    ThreeI g (num g (1) (4) (c) (0) (e) (2)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ (g:ℤ) - c + e - 2 ∧ 0 ≤ (g:ℤ) + c - e - 2) ∨
      (0 ≤ e - 2 ∧ 0 ≤ c + e - 3) ∨
      (0 ≤ - (g:ℤ) + c - e + 2 ∧ 0 ≤ - (g:ℤ) + c + 1) := by omega
  rcases h with h | h | h
  · apply form654 hg (x:=1) (y:=2) (z:=(g:ℤ) - 1) (B:=0) (S:=(g:ℤ) + e - 1) (T:=(g:ℤ) + c - 1) (U:=- c - e + 1)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=2) (z:=(g:ℤ) - 1) (B:=1) (S:=e - 2) (T:=c) (U:=(g:ℤ) - c - e + 2)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=3) (z:=(g:ℤ) - 2) (B:=1) (S:=(g:ℤ) + e - 2) (T:=- (g:ℤ) + c + 1) (U:=(g:ℤ) - c - e)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)

private lemma exceptional9 {g : ℕ} (hg : 5≤g) {c d e : ℤ}
    (hc : digit g c) (hd : digit g d) (he : digit g e) :
    ThreeI g (num g (2) (0) (c) (d) (e) (1)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ c - d + e + 7 ∧ 0 ≤ (g:ℤ) + c - e - 2 ∧ 0 ≤ 3*(g:ℤ) - c + d - e - 10) ∨
      (0 ≤ - c + e ∧ 0 ≤ e - 1 ∧ 0 ≤ (g:ℤ) - c - d + e - 2 ∧ 0 ≤ (g:ℤ) + c - d + e - 4) ∨
      (0 ≤ (g:ℤ) - c + d - e + 2 ∧ 0 ≤ (g:ℤ) + c - e - 2) ∨
      (0 ≤ (g:ℤ) - c + d - e + 6 ∧ 0 ≤ (g:ℤ) + c - e - 2 ∧ 0 ≤ 2*(g:ℤ) + c - d + e - 9) := by omega
  rcases h with h | h | h | h
  · apply form654 hg (x:=1) (y:=4) (z:=(g:ℤ) - 4) (B:=(g:ℤ) - 5) (S:=e + 4) (T:=c + 3) (U:=(g:ℤ) - c + d - e - 8)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=(g:ℤ) - 1) (z:=1) (B:=0) (S:=e - 1) (T:=(g:ℤ) + c - 2) (U:=- c + d - e + 3)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=(g:ℤ) - 2) (z:=2) (B:=1) (S:=(g:ℤ) + e - 2) (T:=(g:ℤ) + c - 3) (U:=- (g:ℤ) - c + d - e + 4)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=(g:ℤ) - 4) (z:=4) (B:=3) (S:=(g:ℤ) + e - 4) (T:=(g:ℤ) + c - 5) (U:=- (g:ℤ) - c + d - e + 8)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)

private lemma exceptional10 {g : ℕ} (hg : 5≤g) {c d e : ℤ}
    (hc : digit g c) (hd : digit g d) (he : digit g e) :
    ThreeI g (num g (2) (0) (c) (d) (e) (2)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ c - d + e + 6 ∧ 0 ≤ (g:ℤ) + c - e - 3 ∧ 0 ≤ 3*(g:ℤ) - c + d - e - 9) ∨
      (0 ≤ - c + e + 2 ∧ 0 ≤ (g:ℤ) - c - 2 ∧ 0 ≤ 2*(g:ℤ) - c + d - e - 6) ∨
      (0 ≤ - (g:ℤ) + e + 2 ∧ 0 ≤ - (g:ℤ) + c - d + e + 1) ∨
      (0 ≤ (g:ℤ) - c + d - e + 5 ∧ 0 ≤ (g:ℤ) + c - e - 3 ∧ 0 ≤ 2*(g:ℤ) + c - d + e - 8) := by omega
  rcases h with h | h | h | h
  · apply form654 hg (x:=1) (y:=4) (z:=(g:ℤ) - 3) (B:=(g:ℤ) - 5) (S:=e + 4) (T:=c + 2) (U:=(g:ℤ) - c + d - e - 7)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=2) (z:=(g:ℤ) - 1) (B:=(g:ℤ) - 4) (S:=e + 3) (T:=(g:ℤ) + c) (U:=- c + d - e - 4)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=2) (z:=(g:ℤ) - 1) (B:=(g:ℤ) - 3) (S:=- (g:ℤ) + e + 2) (T:=c) (U:=2*(g:ℤ) - c + d - e - 2)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=(g:ℤ) - 3) (z:=4) (B:=2) (S:=(g:ℤ) + e - 3) (T:=(g:ℤ) + c - 5) (U:=- (g:ℤ) - c + d - e + 7)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)

private lemma exceptional11 {g : ℕ} (hg : 5≤g) {c d e : ℤ}
    (hc : digit g c) (hd : digit g d) (he : digit g e) :
    ThreeI g (num g (2) (1) (c) (d) (e) (2)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ (g:ℤ) - c + d - e + 6 ∧ 0 ≤ (g:ℤ) + c - e - 2 ∧ 0 ≤ 2*(g:ℤ) + c - d + e - 9) ∨
      (0 ≤ - c + e + 1 ∧ 0 ≤ (g:ℤ) - c - 2 ∧ 0 ≤ 2*(g:ℤ) - c + d - e - 5) ∨
      (0 ≤ c - d + e + 3 ∧ 0 ≤ (g:ℤ) + c - e - 2) := by omega
  rcases h with h | h | h
  · apply form654 hg (x:=1) (y:=(g:ℤ) - 3) (z:=4) (B:=3) (S:=(g:ℤ) + e - 4) (T:=(g:ℤ) + c - 5) (U:=- (g:ℤ) - c + d - e + 8)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=2) (z:=(g:ℤ) - 1) (B:=(g:ℤ) - 3) (S:=e + 2) (T:=(g:ℤ) + c) (U:=- c + d - e - 3)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=3) (z:=(g:ℤ) - 2) (B:=(g:ℤ) - 3) (S:=e + 2) (T:=c + 1) (U:=(g:ℤ) - c + d - e - 4)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
private lemma allSix {g : ℕ} (hg : 5≤g) {a b c d e f : ℤ}
    (ha : 0<a ∧ a<g) (hb : digit g b) (hc : digit g c) (hd : digit g d)
    (he : digit g e) (hf : digit g f) : ThreeI g (num g a b c d e f) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  have hb₁ := hb.1
  have hf₁ := hf.1
  have hf₂ := hf.2
  by_cases h₁ : a=1
  · subst a
    by_cases good : ¬edgeOne g b d f
    · exact leadingOne hg hb hc hd he hf good
    · have h := Classical.not_not.mp good
      rcases h with ⟨hle,hlast⟩ | ⟨hle,rfl,hlast⟩
      · interval_cases b
        all_goals first
          | (convert exceptional0 hg hc hd he using 2 <;> omega)
          | (convert exceptional1 hg hc hd he using 2 <;> omega)
          | (convert exceptional2 hg hc hd he using 2 <;> omega)
          | (convert exceptional3 hg hc hd he using 2 <;> omega)
      · interval_cases b
        all_goals first
          | (convert exceptional4 hg hc he using 2 <;> omega)
          | (convert exceptional5 hg hc he using 2 <;> omega)
          | (convert exceptional6 hg hc he using 2 <;> omega)
          | (convert exceptional7 hg hc he using 2 <;> omega)
          | (convert exceptional8 hg hc he using 2 <;> omega)
  · by_cases good : a≠2 ∨ ¬edgeTwo b f
    · exact leadingMany hg ⟨by omega,ha.2⟩ hb hc hd he hf good
    · push Not at good
      obtain ⟨rfl,hh⟩ := good
      rcases hh with ⟨rfl,rfl|rfl⟩ | ⟨rfl,rfl⟩
      · exact exceptional9 hg hc hd he
      · exact exceptional10 hg hc hd he
      · exact exceptional11 hg hc hd he

private lemma sixDigits {g n : ℕ} (hg : 5≤g) (lo : g^5≤n) (hi : n<g^6) : SumThree g n := by
  let n₁ := n/g
  let n₂ := n₁/g
  let n₃ := n₂/g
  let n₄ := n₃/g
  let a := n₄/g
  let b := n₄%g
  let c := n₃%g
  let d := n₂%g
  let e := n₁%g
  let f := n%g
  have r₀ : f+g*n₁=n := Nat.mod_add_div _ _
  have r₁ : e+g*n₂=n₁ := Nat.mod_add_div _ _
  have r₂ : d+g*n₃=n₂ := Nat.mod_add_div _ _
  have r₃ : c+g*n₄=n₃ := Nat.mod_add_div _ _
  have r₄ : b+g*a=n₄ := Nat.mod_add_div _ _
  have en : a*g^5+b*g^4+c*g^3+d*g^2+e*g+f=n := by
    linear_combination r₀ + g*r₁ + g^2*r₂ + g^3*r₃ + g^4*r₄
  have adiv : a=n/g^5 := by dsimp [a,n₁,n₂,n₃,n₄]; rw [Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul]; congr 1; ring
  have ha : 0<a := by rw [adiv]; exact Nat.div_pos lo (by positivity)
  have ha' : a<g := by
    rw [adiv,Nat.div_lt_iff_lt_mul (by positivity)]
    simpa [pow_succ,mul_comm] using hi
  have digitMod (x : ℕ) : digit g (x%g : ℕ) := ⟨by positivity,by exact_mod_cast Nat.mod_lt x (show 0<g by omega)⟩
  obtain ⟨m,hm,hM⟩ := allSix hg (a:=(a:ℤ)) ⟨by exact_mod_cast ha,by exact_mod_cast ha'⟩
    (digitMod n₄) (digitMod n₃) (digitMod n₂) (digitMod n₁) (digitMod n)
  have hn : (n:ℤ)=num g a b c d e f := by dsimp [num]; exact_mod_cast en.symm
  have heq : m=n := by exact_mod_cast hm.trans hn.symm
  rwa [←heq]

end G95Med

theorem OMA.solution : OMA.R_Green95_green_95_variants_three_palindromes_R1_H2_R1.H1 := by
  intro g hg n lo hi
  by_cases h : n<g^5
  · exact G95Med.fiveDigits hg lo h
  · exact G95Med.sixDigits hg (by omega) hi

