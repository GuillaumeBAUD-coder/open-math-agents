import OMAReductions.R_Green95_green_95_variants_three_palindromes_R1

/-! The short expansions follow Cilleruelo, Luca and Baxter, Lemmas 4.2–4.4.
Through three digits, record the exceptions to the two-palindrome construction.
One more outer pair of digits then suffices through four digits. -/
namespace OMA.R_Green95_green_95_variants_three_palindromes_R1_H2_R1
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

private lemma remainder {g p t : ℕ} (hg : 5≤g) (hp : IsPalindrome g p) (ht : t ≤ g) :
    ∃ x y z, IsPalindrome g x ∧ IsPalindrome g y ∧ IsPalindrome g z ∧ x+y+z=p+t := by
  by_cases h : t<g
  · exact ⟨_,_,_,hp,one hg h,zeroPal g,by omega⟩
  · exact ⟨_,_,_,hp,one hg (show g-1<g by omega),one hg (show 1<g by omega),by omega⟩

private lemma short {g n : ℕ} (hg : 5≤g) (hn : n<g^4) :
    ∃ p q r, IsPalindrome g p ∧ IsPalindrome g q ∧ IsPalindrome g r ∧ p+q+r=n := by
  let a := n/g^3
  let z := n%g^3
  have ha : a<g := by dsimp [a]; rw [Nat.div_lt_iff_lt_mul (by positivity)]; simpa [pow_succ,mul_comm] using hn
  have hz : z<g^3 := Nat.mod_lt _ (by positivity)
  have eq : z+g^3*a=n := Nat.mod_add_div _ _
  clear_value a z
  by_cases a0 : a=0
  · have nz : n=z := by simpa [a0] using eq.symm
    rcases classify hg (nz ▸ hz) with ⟨p,q,hp,hq,h⟩ | ⟨u,hu,hug,h⟩ | h
    · exact ⟨_,_,_,hp,hq,zeroPal g,by omega⟩
    · obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u≠0)
      have e : n=j*(g+1)+g := by rw [Nat.succ_mul] at h; omega
      rw [e]; exact remainder hg (two hg (by omega)) le_rfl
    · refine ⟨_,_,_,three hg (by decide : 0<1) (by omega) (show g-1<g by omega),one hg (show g-1<g by omega),one hg (show 1<g by omega),?_⟩
      rw [h]; zify [show 1≤g by omega]; ring
  by_cases za : z<a
  · by_cases a1 : a=1
    · have zn : n=g^3 := by
        have hzero : z=0 := by omega
        simpa [hzero,a1] using eq.symm
      refine ⟨_,_,_,three hg (show 0<g-1 by omega) (by omega) (show g-1<g by omega),one hg (show 1<g by omega),zeroPal g,?_⟩
      rw [zn]; zify [show 1≤g by omega]; ring
    · have e : n = (a-1)*(g^3+1)+(g-1)*g*(g+1)+(g+z-(a-1)) := by
        rw [←eq]; zify [show 1≤a by omega,show 1≤g by omega,show a-1≤g+z by omega]; ring
      rw [e]
      exact remainder hg (four hg (by omega) (by omega) (by omega)) (by omega)
  let m := z-a
  have hm : m+a=z := by dsimp [m]; omega
  clear_value m
  have en : n=a*(g^3+1)+m := by rw [←eq, ←hm]; ring
  rcases classify hg (show m<g^3 by omega) with ⟨p,q,hp,hq,h⟩ | ⟨u,hu,hug,h⟩ | h
  · refine ⟨_,_,_,four hg (by omega) ha (show 0<g by omega),hp,hq,?_⟩
    rw [en, ←h]; ring
  · by_cases a1 : a=1
    · refine ⟨_,_,_,three hg (show 0<g-1 by omega) (by omega) (show g-1<g by omega),two hg hug,one hg (show 1<g by omega),?_⟩
      rw [en,a1]; zify [show 1≤g by omega] at h ⊢; linarith
    · refine ⟨_,_,_,four hg (show 0<a-1 by omega) (by omega) (show g-2<g by omega),
        three hg (by decide : 0<1) (by omega) (show 3<g by omega),two hg (show u-1<g by omega),?_⟩
      rw [en]; zify [show 1≤a by omega,show 2≤g by omega,hu] at h ⊢; linarith
  · by_cases a1 : a=1
    · refine ⟨_,_,_,four hg (by decide : 0<1) (by omega) (show 1<g by omega),two hg (show g-2<g by omega),one hg (show 3<g by omega),?_⟩
      rw [en,h,a1]; zify [show 2≤g by omega]; ring
    · refine ⟨_,_,_,four hg (show 0<a-1 by omega) (by omega) (show g-1<g by omega),
        three hg (by decide : 0<2) (by omega) (show 1<g by omega),zeroPal g,?_⟩
      rw [en,h]; zify [show 1≤a by omega,show 1≤g by omega]; ring

def H1 : Prop := ∀ g : ℕ, 5 ≤ g → ∀ n : ℕ, g^4 ≤ n → n < g^6 →
  ∃ p q r, IsPalindrome g p ∧ IsPalindrome g q ∧ IsPalindrome g r ∧ p+q+r=n

def H2 : Prop := ∀ g : ℕ, 5 ≤ g → ∀ n : ℕ, g^6 ≤ n →
  ∃ p q r, IsPalindrome g p ∧ IsPalindrome g q ∧ IsPalindrome g r ∧ p+q+r=n

theorem main : H1 → H2 → OMA.R_Green95_green_95_variants_three_palindromes_R1.H2 := by
  intro medium large g hg n _
  by_cases shortN : n<g^4
  · exact short hg shortN
  by_cases mediumN : n<g^6
  · exact medium g hg n (by omega) mediumN
  · exact large g hg n (by omega)
end OMA.R_Green95_green_95_variants_three_palindromes_R1_H2_R1
