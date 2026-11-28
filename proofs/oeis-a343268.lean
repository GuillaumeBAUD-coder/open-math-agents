import OMAStatements.S_oeis_a343268
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

-- Problem: A343268, sums of four positive binary squares.
-- Source: https://oeis.org/A343268
-- Statement credit: @keiichisince1986-bot.
-- Madhusudan, Nowotka, Rajasekaran and Shallit, Lagrange's Theorem for Binary
-- Squares, MFCS 2018, arXiv:1710.04247, prove the at-most-four version and pose
-- the positive exactly-four target as a conjecture. Their result is background;
-- the interval construction and finite certificates below are independent.
-- Write N=CQ+R and group four terms m*(c*C+1), c in {1,2,4,8,16}, by width.
-- The carry equations reduce the construction to intersections of integer
-- intervals. There are 78 large-range family/carry choices across 13 patterns,
-- covering 25 sectors; the small-range extensions use 101 choices in total.
-- Symbolic search discovered the choices. Every coverage inequality, witness,
-- finite initial case, and obstruction is checked in Lean's kernel.

-- Component: A343268Base

namespace A343268Proof

def Width (c : ℤ) : Prop := c = 1 ∨ c = 2 ∨ c = 4 ∨ c = 8 ∨ c = 16

def Four (t N : ℤ) : Prop :=
  ∃ a b c d w x y z : ℤ,
    Width a ∧ Width b ∧ Width c ∧ Width d ∧
    a*t ≤ w ∧ w < 2*a*t ∧ b*t ≤ x ∧ x < 2*b*t ∧
    c*t ≤ y ∧ y < 2*c*t ∧ d*t ≤ z ∧ z < 2*d*t ∧
    N = (2*a*t+1)*w + (2*b*t+1)*x + (2*c*t+1)*y + (2*d*t+1)*z

def split_two (l u s : ℤ) (hlu : l ≤ u) (hs : 2*l ≤ s ∧ s ≤ 2*u) :
    ∃ x y : ℤ, l ≤ x ∧ x ≤ u ∧ l ≤ y ∧ y ≤ u ∧ x+y=s := by
  refine ⟨max l (s-u), s-max l (s-u), ?_⟩
  rcases le_total l (s-u) with h|h <;> simp only [max_eq_right h, max_eq_left h] <;> omega

def split_three (l u s : ℤ) (hlu : l ≤ u) (hs : 3*l ≤ s ∧ s ≤ 3*u) :
    ∃ x y z : ℤ, l ≤ x ∧ x ≤ u ∧ l ≤ y ∧ y ≤ u ∧ l ≤ z ∧ z ≤ u ∧ x+y+z=s := by
  let x := max l (s-2*u)
  have hx : l ≤ x ∧ x ≤ u ∧ 2*l ≤ s-x ∧ s-x ≤ 2*u := by
    dsimp [x]
    rcases le_total l (s-2*u) with h|h <;> simp only [max_eq_right h, max_eq_left h] <;> omega
  obtain ⟨y,z,hy,huy,hz,huz,heq⟩ := split_two l u (s-x) hlu ⟨hx.2.2.1,hx.2.2.2⟩
  exact ⟨x,y,z,hx.1,hx.2.1,hy,huy,hz,huz,by omega⟩

/-- A closed integer interval meets three rational lower and upper bounds. -/
def three_interval (L U A B C D : ℤ) (v : ℤ) (hv : v = 3 ∨ v = 7 ∨ v = 15)
    (hLU : L ≤ U)
    (hL1 : v*L ≤ C) (hL2 : (v-1)*L ≤ D)
    (hU1 : A ≤ v*U) (hU2 : B ≤ (v-1)*U)
    (h11 : A+v ≤ C) (h12 : (v-1)*A+v*(v-1) ≤ v*D)
    (h21 : v*B+v*(v-1) ≤ (v-1)*C) (h22 : B+(v-1) ≤ D) :
    ∃ z : ℤ, L ≤ z ∧ z ≤ U ∧ A ≤ v*z ∧ v*z ≤ C ∧
      B ≤ (v-1)*z ∧ (v-1)*z ≤ D := by
  rcases hv with rfl | rfl | rfl
  · refine ⟨max L (max ((A+2)/3) ((B+1)/2)), ?_⟩
    omega
  · refine ⟨max L (max ((A+6)/7) ((B+5)/6)), ?_⟩
    omega
  · refine ⟨max L (max ((A+14)/15) ((B+13)/14)), ?_⟩
    omega

end A343268Proof

-- Component: A343268Bridge

namespace A343268Proof
open OMA.S_oeis_a343268

def Representable (n : ℕ) : Prop := ∃ a b c d : ℕ,
  IsBinSquare a ∧ IsBinSquare b ∧ IsBinSquare c ∧ IsBinSquare d ∧ a+b+c+d=n

def width_power (c : ℤ) (hc : Width c) : ∃ e : ℕ, c = (2:ℤ)^e := by
  rcases hc with rfl|rfl|rfl|rfl|rfl
  · exact ⟨0,by norm_num⟩
  · exact ⟨1,by norm_num⟩
  · exact ⟨2,by norm_num⟩
  · exact ⟨3,by norm_num⟩
  · exact ⟨4,by norm_num⟩

def square_of_bounds (k e : ℕ) (m : ℤ)
    (hm : (2:ℤ)^(k+e)≤m ∧ m<(2:ℤ)^(k+e+1)) :
    IsBinSquare (m.toNat*(2^(k+e+1)+1)) := by
  have hm0 : 0≤m := le_trans (by positivity) hm.1
  have hcast : (m.toNat:ℤ)=m := Int.toNat_of_nonneg hm0
  refine ⟨k+e+1,m.toNat,by omega,?_,?_,rfl⟩
  · have h := hm.1
    rw [← hcast] at h
    simpa using (show 2^(k+e)≤m.toNat by exact_mod_cast h)
  · have h := hm.2
    rw [← hcast] at h
    exact_mod_cast h

def four_is_representable (k : ℕ) (N : ℤ) (hf : Four ((2:ℤ)^k) N) :
    Representable N.toNat := by
  rcases hf with ⟨a,b,c,d,w,x,y,z,ha,hb,hc,hd,hw,hw',hx,hx',hy,hy',hz,hz',heq⟩
  obtain ⟨i,rfl⟩ := width_power a ha
  obtain ⟨j,rfl⟩ := width_power b hb
  obtain ⟨l,rfl⟩ := width_power c hc
  obtain ⟨m,rfl⟩ := width_power d hd
  have hp (e : ℕ) : (2:ℤ)^(k+e)=(2:ℤ)^e*2^k := by rw [pow_add]; ring
  have hp' (e : ℕ) : (2:ℤ)^(k+e+1)=2*(2:ℤ)^e*2^k := by rw [pow_add,pow_add]; norm_num; ring
  have bw : (2:ℤ)^(k+i)≤w ∧ w<(2:ℤ)^(k+i+1) := by simpa [hp,hp'] using And.intro hw hw'
  have bx : (2:ℤ)^(k+j)≤x ∧ x<(2:ℤ)^(k+j+1) := by simpa [hp,hp'] using And.intro hx hx'
  have by' : (2:ℤ)^(k+l)≤y ∧ y<(2:ℤ)^(k+l+1) := by simpa [hp,hp'] using And.intro hy hy'
  have bz : (2:ℤ)^(k+m)≤z ∧ z<(2:ℤ)^(k+m+1) := by simpa [hp,hp'] using And.intro hz hz'
  have hw0 : 0≤w := le_trans (by positivity) bw.1
  have hx0 : 0≤x := le_trans (by positivity) bx.1
  have hy0 : 0≤y := le_trans (by positivity) by'.1
  have hz0 : 0≤z := le_trans (by positivity) bz.1
  have hN0 : 0≤N := by rw [heq]; positivity
  refine ⟨w.toNat*(2^(k+i+1)+1),x.toNat*(2^(k+j+1)+1),y.toNat*(2^(k+l+1)+1),z.toNat*(2^(k+m+1)+1),square_of_bounds k i w bw,square_of_bounds k j x bx,square_of_bounds k l y by',square_of_bounds k m z bz,?_⟩
  apply Int.ofNat_injective
  change (((w.toNat*(2^(k+i+1)+1)+x.toNat*(2^(k+j+1)+1)+y.toNat*(2^(k+l+1)+1)+z.toNat*(2^(k+m+1)+1)) : ℕ) : ℤ) = (N.toNat : ℤ)
  push_cast
  rw [Int.toNat_of_nonneg hw0,Int.toNat_of_nonneg hx0,Int.toNat_of_nonneg hy0,Int.toNat_of_nonneg hz0,Int.toNat_of_nonneg hN0]
  simp only [hp']
  rw [heq]
  ring

end A343268Proof

-- Component: A343268Cases

namespace A343268Proof
def c0_0 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  15*(16*t)≤(((4*q+-12)-(R+24*t))-(2*t)) ∧
  14*(16*t)≤((4*t-2)-(R+24*t)+((4*q+-12)-(R+24*t))) ∧
  (((4*q+-12)-(R+24*t))-(4*t-1))≤15*(32*t-1) ∧
  ((2*t)-(R+24*t)+((4*q+-12)-(R+24*t)))≤14*(32*t-1) ∧
  (((4*q+-12)-(R+24*t))-(4*t-1))+15≤(((4*q+-12)-(R+24*t))-(2*t)) ∧
  14*(((4*q+-12)-(R+24*t))-(4*t-1))+210≤15*((4*t-2)-(R+24*t)+((4*q+-12)-(R+24*t))) ∧
  15*((2*t)-(R+24*t)+((4*q+-12)-(R+24*t)))+210≤14*(((4*q+-12)-(R+24*t))-(2*t)) ∧
  ((2*t)-(R+24*t)+((4*q+-12)-(R+24*t)))+14≤((4*t-2)-(R+24*t)+((4*q+-12)-(R+24*t)))
def c0_0_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_0 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((4*q+-12)-(R+24*t))-(4*t-1)) ((2*t)-(R+24*t)+((4*q+-12)-(R+24*t))) (((4*q+-12)-(R+24*t))-(2*t)) ((4*t-2)-(R+24*t)+((4*q+-12)-(R+24*t))) 15 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-12)-(R+24*t))-15*z
  let x : ℤ := (R+24*t)-((4*q+-12)-(R+24*t))+14*z
  have hx : (2*t)≤x ∧ x≤(4*t-2) := by dsimp [x]; omega
  have hy : (2*t)≤y ∧ y≤(4*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (1*t) (2*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,1,2,16,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (2*t+1)*x + (4*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c0_1 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  15*(16*t)≤(((4*q+-12)-(R+24*t))-(4*t)) ∧
  14*(16*t)≤((2*t-1)-(R+24*t)+((4*q+-12)-(R+24*t))) ∧
  (((4*q+-12)-(R+24*t))-(8*t-2))≤15*(32*t-1) ∧
  ((1*t)-(R+24*t)+((4*q+-12)-(R+24*t)))≤14*(32*t-1) ∧
  (((4*q+-12)-(R+24*t))-(8*t-2))+15≤(((4*q+-12)-(R+24*t))-(4*t)) ∧
  14*(((4*q+-12)-(R+24*t))-(8*t-2))+210≤15*((2*t-1)-(R+24*t)+((4*q+-12)-(R+24*t))) ∧
  15*((1*t)-(R+24*t)+((4*q+-12)-(R+24*t)))+210≤14*(((4*q+-12)-(R+24*t))-(4*t)) ∧
  ((1*t)-(R+24*t)+((4*q+-12)-(R+24*t)))+14≤((2*t-1)-(R+24*t)+((4*q+-12)-(R+24*t)))
def c0_1_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_1 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((4*q+-12)-(R+24*t))-(8*t-2)) ((1*t)-(R+24*t)+((4*q+-12)-(R+24*t))) (((4*q+-12)-(R+24*t))-(4*t)) ((2*t-1)-(R+24*t)+((4*q+-12)-(R+24*t))) 15 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-12)-(R+24*t))-15*z
  let x : ℤ := (R+24*t)-((4*q+-12)-(R+24*t))+14*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (2*t) (4*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,2,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (2*t+1)*x + (4*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c0_2 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  15*(16*t)≤(((4*q+-14)-(R+28*t))-(4*t)) ∧
  14*(16*t)≤((2*t-1)-(R+28*t)+((4*q+-14)-(R+28*t))) ∧
  (((4*q+-14)-(R+28*t))-(8*t-2))≤15*(32*t-1) ∧
  ((1*t)-(R+28*t)+((4*q+-14)-(R+28*t)))≤14*(32*t-1) ∧
  (((4*q+-14)-(R+28*t))-(8*t-2))+15≤(((4*q+-14)-(R+28*t))-(4*t)) ∧
  14*(((4*q+-14)-(R+28*t))-(8*t-2))+210≤15*((2*t-1)-(R+28*t)+((4*q+-14)-(R+28*t))) ∧
  15*((1*t)-(R+28*t)+((4*q+-14)-(R+28*t)))+210≤14*(((4*q+-14)-(R+28*t))-(4*t)) ∧
  ((1*t)-(R+28*t)+((4*q+-14)-(R+28*t)))+14≤((2*t-1)-(R+28*t)+((4*q+-14)-(R+28*t)))
def c0_2_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_2 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((4*q+-14)-(R+28*t))-(8*t-2)) ((1*t)-(R+28*t)+((4*q+-14)-(R+28*t))) (((4*q+-14)-(R+28*t))-(4*t)) ((2*t-1)-(R+28*t)+((4*q+-14)-(R+28*t))) 15 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-14)-(R+28*t))-15*z
  let x : ℤ := (R+28*t)-((4*q+-14)-(R+28*t))+14*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (2*t) (4*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,2,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (2*t+1)*x + (4*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c0_3 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  15*(16*t)≤(((4*q+-15)-(R+30*t))-(4*t)) ∧
  14*(16*t)≤((2*t-1)-(R+30*t)+((4*q+-15)-(R+30*t))) ∧
  (((4*q+-15)-(R+30*t))-(8*t-2))≤15*(32*t-1) ∧
  ((1*t)-(R+30*t)+((4*q+-15)-(R+30*t)))≤14*(32*t-1) ∧
  (((4*q+-15)-(R+30*t))-(8*t-2))+15≤(((4*q+-15)-(R+30*t))-(4*t)) ∧
  14*(((4*q+-15)-(R+30*t))-(8*t-2))+210≤15*((2*t-1)-(R+30*t)+((4*q+-15)-(R+30*t))) ∧
  15*((1*t)-(R+30*t)+((4*q+-15)-(R+30*t)))+210≤14*(((4*q+-15)-(R+30*t))-(4*t)) ∧
  ((1*t)-(R+30*t)+((4*q+-15)-(R+30*t)))+14≤((2*t-1)-(R+30*t)+((4*q+-15)-(R+30*t)))
def c0_3_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_3 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((4*q+-15)-(R+30*t))-(8*t-2)) ((1*t)-(R+30*t)+((4*q+-15)-(R+30*t))) (((4*q+-15)-(R+30*t))-(4*t)) ((2*t-1)-(R+30*t)+((4*q+-15)-(R+30*t))) 15 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-15)-(R+30*t))-15*z
  let x : ℤ := (R+30*t)-((4*q+-15)-(R+30*t))+14*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (2*t) (4*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,2,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (2*t+1)*x + (4*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c0_4 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-2) ∧
  7*(16*t)≤(((4*q+-12)-(R+24*t))-(2*t)) ∧
  6*(16*t)≤((2*t-1)-(R+24*t)+((4*q+-12)-(R+24*t))) ∧
  (((4*q+-12)-(R+24*t))-(4*t-1))≤7*(32*t-2) ∧
  ((1*t)-(R+24*t)+((4*q+-12)-(R+24*t)))≤6*(32*t-2) ∧
  (((4*q+-12)-(R+24*t))-(4*t-1))+7≤(((4*q+-12)-(R+24*t))-(2*t)) ∧
  6*(((4*q+-12)-(R+24*t))-(4*t-1))+42≤7*((2*t-1)-(R+24*t)+((4*q+-12)-(R+24*t))) ∧
  7*((1*t)-(R+24*t)+((4*q+-12)-(R+24*t)))+42≤6*(((4*q+-12)-(R+24*t))-(2*t)) ∧
  ((1*t)-(R+24*t)+((4*q+-12)-(R+24*t)))+6≤((2*t-1)-(R+24*t)+((4*q+-12)-(R+24*t)))
def c0_4_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_4 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-2) (((4*q+-12)-(R+24*t))-(4*t-1)) ((1*t)-(R+24*t)+((4*q+-12)-(R+24*t))) (((4*q+-12)-(R+24*t))-(2*t)) ((2*t-1)-(R+24*t)+((4*q+-12)-(R+24*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-12)-(R+24*t))-7*z
  let x : ℤ := (R+24*t)-((4*q+-12)-(R+24*t))+6*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (2*t)≤y ∧ y≤(4*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-2) := ⟨hzL,hzU⟩
  obtain ⟨z0,z1,hz0L,hz0U,hz1L,hz1U,hzsum⟩ := split_two (8*t) (16*t-1) z (by omega) (by rcases hz with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,8,8,x,y,z0,z1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (2*t+1)*x + (4*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hzsum]
        ring

def c0_5 (t q R : ℤ) : Prop :=
  (8*t)≤(16*t-1) ∧
  3*(8*t)≤(((2*q+-7)-(R+28*t))-(4*t)) ∧
  2*(8*t)≤((8*t-2)-(R+28*t)+((2*q+-7)-(R+28*t))) ∧
  (((2*q+-7)-(R+28*t))-(8*t-1))≤3*(16*t-1) ∧
  ((4*t)-(R+28*t)+((2*q+-7)-(R+28*t)))≤2*(16*t-1) ∧
  (((2*q+-7)-(R+28*t))-(8*t-1))+3≤(((2*q+-7)-(R+28*t))-(4*t)) ∧
  2*(((2*q+-7)-(R+28*t))-(8*t-1))+6≤3*((8*t-2)-(R+28*t)+((2*q+-7)-(R+28*t))) ∧
  3*((4*t)-(R+28*t)+((2*q+-7)-(R+28*t)))+6≤2*(((2*q+-7)-(R+28*t))-(4*t)) ∧
  ((4*t)-(R+28*t)+((2*q+-7)-(R+28*t)))+2≤((8*t-2)-(R+28*t)+((2*q+-7)-(R+28*t)))
def c0_5_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_5 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (8*t) (16*t-1) (((2*q+-7)-(R+28*t))-(8*t-1)) ((4*t)-(R+28*t)+((2*q+-7)-(R+28*t))) (((2*q+-7)-(R+28*t))-(4*t)) ((8*t-2)-(R+28*t)+((2*q+-7)-(R+28*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-7)-(R+28*t))-3*z
  let x : ℤ := (R+28*t)-((2*q+-7)-(R+28*t))+2*z
  have hx : (4*t)≤x ∧ x≤(8*t-2) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (8*t)≤z ∧ z≤(16*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (2*t) (4*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,2,4,8,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c0_6 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-7)-(R+28*t))-(4*t)) ∧
  6*(16*t)≤((8*t-2)-(R+28*t)+((2*q+-7)-(R+28*t))) ∧
  (((2*q+-7)-(R+28*t))-(8*t-1))≤7*(32*t-1) ∧
  ((4*t)-(R+28*t)+((2*q+-7)-(R+28*t)))≤6*(32*t-1) ∧
  (((2*q+-7)-(R+28*t))-(8*t-1))+7≤(((2*q+-7)-(R+28*t))-(4*t)) ∧
  6*(((2*q+-7)-(R+28*t))-(8*t-1))+42≤7*((8*t-2)-(R+28*t)+((2*q+-7)-(R+28*t))) ∧
  7*((4*t)-(R+28*t)+((2*q+-7)-(R+28*t)))+42≤6*(((2*q+-7)-(R+28*t))-(4*t)) ∧
  ((4*t)-(R+28*t)+((2*q+-7)-(R+28*t)))+6≤((8*t-2)-(R+28*t)+((2*q+-7)-(R+28*t)))
def c0_6_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_6 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-7)-(R+28*t))-(8*t-1)) ((4*t)-(R+28*t)+((2*q+-7)-(R+28*t))) (((2*q+-7)-(R+28*t))-(4*t)) ((8*t-2)-(R+28*t)+((2*q+-7)-(R+28*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-7)-(R+28*t))-7*z
  let x : ℤ := (R+28*t)-((2*q+-7)-(R+28*t))+6*z
  have hx : (4*t)≤x ∧ x≤(8*t-2) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (2*t) (4*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,2,4,16,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c0_7 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-10)-(R+40*t))-(4*t)) ∧
  6*(16*t)≤((8*t-2)-(R+40*t)+((2*q+-10)-(R+40*t))) ∧
  (((2*q+-10)-(R+40*t))-(8*t-1))≤7*(32*t-1) ∧
  ((4*t)-(R+40*t)+((2*q+-10)-(R+40*t)))≤6*(32*t-1) ∧
  (((2*q+-10)-(R+40*t))-(8*t-1))+7≤(((2*q+-10)-(R+40*t))-(4*t)) ∧
  6*(((2*q+-10)-(R+40*t))-(8*t-1))+42≤7*((8*t-2)-(R+40*t)+((2*q+-10)-(R+40*t))) ∧
  7*((4*t)-(R+40*t)+((2*q+-10)-(R+40*t)))+42≤6*(((2*q+-10)-(R+40*t))-(4*t)) ∧
  ((4*t)-(R+40*t)+((2*q+-10)-(R+40*t)))+6≤((8*t-2)-(R+40*t)+((2*q+-10)-(R+40*t)))
def c0_7_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_7 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-10)-(R+40*t))-(8*t-1)) ((4*t)-(R+40*t)+((2*q+-10)-(R+40*t))) (((2*q+-10)-(R+40*t))-(4*t)) ((8*t-2)-(R+40*t)+((2*q+-10)-(R+40*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-10)-(R+40*t))-7*z
  let x : ℤ := (R+40*t)-((2*q+-10)-(R+40*t))+6*z
  have hx : (4*t)≤x ∧ x≤(8*t-2) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (2*t) (4*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,2,4,16,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c0_8 (t q R : ℤ) : Prop :=
  (8*t)≤(16*t-1) ∧
  3*(8*t)≤(((2*q+-5)-(R+20*t))-(8*t)) ∧
  2*(8*t)≤((4*t-1)-(R+20*t)+((2*q+-5)-(R+20*t))) ∧
  (((2*q+-5)-(R+20*t))-(16*t-2))≤3*(16*t-1) ∧
  ((2*t)-(R+20*t)+((2*q+-5)-(R+20*t)))≤2*(16*t-1) ∧
  (((2*q+-5)-(R+20*t))-(16*t-2))+3≤(((2*q+-5)-(R+20*t))-(8*t)) ∧
  2*(((2*q+-5)-(R+20*t))-(16*t-2))+6≤3*((4*t-1)-(R+20*t)+((2*q+-5)-(R+20*t))) ∧
  3*((2*t)-(R+20*t)+((2*q+-5)-(R+20*t)))+6≤2*(((2*q+-5)-(R+20*t))-(8*t)) ∧
  ((2*t)-(R+20*t)+((2*q+-5)-(R+20*t)))+2≤((4*t-1)-(R+20*t)+((2*q+-5)-(R+20*t)))
def c0_8_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_8 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (8*t) (16*t-1) (((2*q+-5)-(R+20*t))-(16*t-2)) ((2*t)-(R+20*t)+((2*q+-5)-(R+20*t))) (((2*q+-5)-(R+20*t))-(8*t)) ((4*t-1)-(R+20*t)+((2*q+-5)-(R+20*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-5)-(R+20*t))-3*z
  let x : ℤ := (R+20*t)-((2*q+-5)-(R+20*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (8*t)≤z ∧ z≤(16*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,8,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c0_9 (t q R : ℤ) : Prop :=
  (8*t)≤(16*t-1) ∧
  3*(8*t)≤(((2*q+-6)-(R+24*t))-(8*t)) ∧
  2*(8*t)≤((4*t-1)-(R+24*t)+((2*q+-6)-(R+24*t))) ∧
  (((2*q+-6)-(R+24*t))-(16*t-2))≤3*(16*t-1) ∧
  ((2*t)-(R+24*t)+((2*q+-6)-(R+24*t)))≤2*(16*t-1) ∧
  (((2*q+-6)-(R+24*t))-(16*t-2))+3≤(((2*q+-6)-(R+24*t))-(8*t)) ∧
  2*(((2*q+-6)-(R+24*t))-(16*t-2))+6≤3*((4*t-1)-(R+24*t)+((2*q+-6)-(R+24*t))) ∧
  3*((2*t)-(R+24*t)+((2*q+-6)-(R+24*t)))+6≤2*(((2*q+-6)-(R+24*t))-(8*t)) ∧
  ((2*t)-(R+24*t)+((2*q+-6)-(R+24*t)))+2≤((4*t-1)-(R+24*t)+((2*q+-6)-(R+24*t)))
def c0_9_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_9 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (8*t) (16*t-1) (((2*q+-6)-(R+24*t))-(16*t-2)) ((2*t)-(R+24*t)+((2*q+-6)-(R+24*t))) (((2*q+-6)-(R+24*t))-(8*t)) ((4*t-1)-(R+24*t)+((2*q+-6)-(R+24*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-6)-(R+24*t))-3*z
  let x : ℤ := (R+24*t)-((2*q+-6)-(R+24*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (8*t)≤z ∧ z≤(16*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,8,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c0_10 (t q R : ℤ) : Prop :=
  (8*t)≤(16*t-1) ∧
  3*(8*t)≤(((2*q+-7)-(R+28*t))-(8*t)) ∧
  2*(8*t)≤((4*t-1)-(R+28*t)+((2*q+-7)-(R+28*t))) ∧
  (((2*q+-7)-(R+28*t))-(16*t-2))≤3*(16*t-1) ∧
  ((2*t)-(R+28*t)+((2*q+-7)-(R+28*t)))≤2*(16*t-1) ∧
  (((2*q+-7)-(R+28*t))-(16*t-2))+3≤(((2*q+-7)-(R+28*t))-(8*t)) ∧
  2*(((2*q+-7)-(R+28*t))-(16*t-2))+6≤3*((4*t-1)-(R+28*t)+((2*q+-7)-(R+28*t))) ∧
  3*((2*t)-(R+28*t)+((2*q+-7)-(R+28*t)))+6≤2*(((2*q+-7)-(R+28*t))-(8*t)) ∧
  ((2*t)-(R+28*t)+((2*q+-7)-(R+28*t)))+2≤((4*t-1)-(R+28*t)+((2*q+-7)-(R+28*t)))
def c0_10_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_10 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (8*t) (16*t-1) (((2*q+-7)-(R+28*t))-(16*t-2)) ((2*t)-(R+28*t)+((2*q+-7)-(R+28*t))) (((2*q+-7)-(R+28*t))-(8*t)) ((4*t-1)-(R+28*t)+((2*q+-7)-(R+28*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-7)-(R+28*t))-3*z
  let x : ℤ := (R+28*t)-((2*q+-7)-(R+28*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (8*t)≤z ∧ z≤(16*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,8,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c0_11 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-9)-(R+36*t))-(8*t)) ∧
  6*(16*t)≤((4*t-1)-(R+36*t)+((2*q+-9)-(R+36*t))) ∧
  (((2*q+-9)-(R+36*t))-(16*t-2))≤7*(32*t-1) ∧
  ((2*t)-(R+36*t)+((2*q+-9)-(R+36*t)))≤6*(32*t-1) ∧
  (((2*q+-9)-(R+36*t))-(16*t-2))+7≤(((2*q+-9)-(R+36*t))-(8*t)) ∧
  6*(((2*q+-9)-(R+36*t))-(16*t-2))+42≤7*((4*t-1)-(R+36*t)+((2*q+-9)-(R+36*t))) ∧
  7*((2*t)-(R+36*t)+((2*q+-9)-(R+36*t)))+42≤6*(((2*q+-9)-(R+36*t))-(8*t)) ∧
  ((2*t)-(R+36*t)+((2*q+-9)-(R+36*t)))+6≤((4*t-1)-(R+36*t)+((2*q+-9)-(R+36*t)))
def c0_11_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_11 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-9)-(R+36*t))-(16*t-2)) ((2*t)-(R+36*t)+((2*q+-9)-(R+36*t))) (((2*q+-9)-(R+36*t))-(8*t)) ((4*t-1)-(R+36*t)+((2*q+-9)-(R+36*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-9)-(R+36*t))-7*z
  let x : ℤ := (R+36*t)-((2*q+-9)-(R+36*t))+6*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c0_12 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-2) ∧
  3*(16*t)≤(((2*q+-7)-(R+28*t))-(4*t)) ∧
  2*(16*t)≤((4*t-1)-(R+28*t)+((2*q+-7)-(R+28*t))) ∧
  (((2*q+-7)-(R+28*t))-(8*t-1))≤3*(32*t-2) ∧
  ((2*t)-(R+28*t)+((2*q+-7)-(R+28*t)))≤2*(32*t-2) ∧
  (((2*q+-7)-(R+28*t))-(8*t-1))+3≤(((2*q+-7)-(R+28*t))-(4*t)) ∧
  2*(((2*q+-7)-(R+28*t))-(8*t-1))+6≤3*((4*t-1)-(R+28*t)+((2*q+-7)-(R+28*t))) ∧
  3*((2*t)-(R+28*t)+((2*q+-7)-(R+28*t)))+6≤2*(((2*q+-7)-(R+28*t))-(4*t)) ∧
  ((2*t)-(R+28*t)+((2*q+-7)-(R+28*t)))+2≤((4*t-1)-(R+28*t)+((2*q+-7)-(R+28*t)))
def c0_12_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_12 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-2) (((2*q+-7)-(R+28*t))-(8*t-1)) ((2*t)-(R+28*t)+((2*q+-7)-(R+28*t))) (((2*q+-7)-(R+28*t))-(4*t)) ((4*t-1)-(R+28*t)+((2*q+-7)-(R+28*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-7)-(R+28*t))-3*z
  let x : ℤ := (R+28*t)-((2*q+-7)-(R+28*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-2) := ⟨hzL,hzU⟩
  obtain ⟨z0,z1,hz0L,hz0U,hz1L,hz1U,hzsum⟩ := split_two (8*t) (16*t-1) z (by omega) (by rcases hz with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,8,8,x,y,z0,z1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hzsum]
        ring

def c0_13 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-2) ∧
  3*(16*t)≤(((2*q+-9)-(R+36*t))-(4*t)) ∧
  2*(16*t)≤((4*t-1)-(R+36*t)+((2*q+-9)-(R+36*t))) ∧
  (((2*q+-9)-(R+36*t))-(8*t-1))≤3*(32*t-2) ∧
  ((2*t)-(R+36*t)+((2*q+-9)-(R+36*t)))≤2*(32*t-2) ∧
  (((2*q+-9)-(R+36*t))-(8*t-1))+3≤(((2*q+-9)-(R+36*t))-(4*t)) ∧
  2*(((2*q+-9)-(R+36*t))-(8*t-1))+6≤3*((4*t-1)-(R+36*t)+((2*q+-9)-(R+36*t))) ∧
  3*((2*t)-(R+36*t)+((2*q+-9)-(R+36*t)))+6≤2*(((2*q+-9)-(R+36*t))-(4*t)) ∧
  ((2*t)-(R+36*t)+((2*q+-9)-(R+36*t)))+2≤((4*t-1)-(R+36*t)+((2*q+-9)-(R+36*t)))
def c0_13_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_13 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-2) (((2*q+-9)-(R+36*t))-(8*t-1)) ((2*t)-(R+36*t)+((2*q+-9)-(R+36*t))) (((2*q+-9)-(R+36*t))-(4*t)) ((4*t-1)-(R+36*t)+((2*q+-9)-(R+36*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-9)-(R+36*t))-3*z
  let x : ℤ := (R+36*t)-((2*q+-9)-(R+36*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-2) := ⟨hzL,hzU⟩
  obtain ⟨z0,z1,hz0L,hz0U,hz1L,hz1U,hzsum⟩ := split_two (8*t) (16*t-1) z (by omega) (by rcases hz with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,8,8,x,y,z0,z1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hzsum]
        ring

def c0_14 (t q R : ℤ) : Prop :=
  (12*t)≤((R+32*t)-((1*q+-4)-(R+32*t))) ∧
  ((R+32*t)-((1*q+-4)-(R+32*t)))≤(24*t-3) ∧
  (8*t)≤((1*q+-4)-(R+32*t)) ∧
  ((1*q+-4)-(R+32*t))≤(16*t-1)
def c0_14_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_14 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  let y : ℤ := ((1*q+-4)-(R+32*t))
  let x : ℤ := ((R+32*t)-((1*q+-4)-(R+32*t)))
  have hx : (12*t)≤x ∧ x≤(24*t-3) := ⟨hc.1,hc.2.1⟩
  have hy : (8*t)≤y ∧ y≤(16*t-1) := hc.2.2
  obtain ⟨x0,x1,x2,hx0L,hx0U,hx1L,hx1U,hx2L,hx2U,hxsum⟩ := split_three (4*t) (8*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,4,4,8,x0,x1,x2,y, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c0_15 (t q R : ℤ) : Prop :=
  (8*t)≤((R+24*t)-((1*q+-3)-(R+24*t))) ∧
  ((R+24*t)-((1*q+-3)-(R+24*t)))≤(16*t-2) ∧
  (16*t)≤((1*q+-3)-(R+24*t)) ∧
  ((1*q+-3)-(R+24*t))≤(32*t-2)
def c0_15_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_15 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  let y : ℤ := ((1*q+-3)-(R+24*t))
  let x : ℤ := ((R+24*t)-((1*q+-3)-(R+24*t)))
  have hx : (8*t)≤x ∧ x≤(16*t-2) := ⟨hc.1,hc.2.1⟩
  have hy : (16*t)≤y ∧ y≤(32*t-2) := hc.2.2
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (4*t) (8*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (8*t) (16*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,4,8,8,x0,x1,y0,y1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum,← hysum]
        ring

def c0_16 (t q R : ℤ) : Prop :=
  (8*t)≤((R+32*t)-((1*q+-4)-(R+32*t))) ∧
  ((R+32*t)-((1*q+-4)-(R+32*t)))≤(16*t-2) ∧
  (16*t)≤((1*q+-4)-(R+32*t)) ∧
  ((1*q+-4)-(R+32*t))≤(32*t-2)
def c0_16_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_16 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  let y : ℤ := ((1*q+-4)-(R+32*t))
  let x : ℤ := ((R+32*t)-((1*q+-4)-(R+32*t)))
  have hx : (8*t)≤x ∧ x≤(16*t-2) := ⟨hc.1,hc.2.1⟩
  have hy : (16*t)≤y ∧ y≤(32*t-2) := hc.2.2
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (4*t) (8*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (8*t) (16*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,4,8,8,x0,x1,y0,y1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum,← hysum]
        ring

def c0_17 (t q R : ℤ) : Prop :=
  (8*t)≤((R+40*t)-((1*q+-5)-(R+40*t))) ∧
  ((R+40*t)-((1*q+-5)-(R+40*t)))≤(16*t-2) ∧
  (16*t)≤((1*q+-5)-(R+40*t)) ∧
  ((1*q+-5)-(R+40*t))≤(32*t-2)
def c0_17_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_17 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  let y : ℤ := ((1*q+-5)-(R+40*t))
  let x : ℤ := ((R+40*t)-((1*q+-5)-(R+40*t)))
  have hx : (8*t)≤x ∧ x≤(16*t-2) := ⟨hc.1,hc.2.1⟩
  have hy : (16*t)≤y ∧ y≤(32*t-2) := hc.2.2
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (4*t) (8*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (8*t) (16*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,4,8,8,x0,x1,y0,y1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum,← hysum]
        ring

def c0_18 (t q R : ℤ) : Prop :=
  (4*t)≤((R+32*t)-((1*q+-4)-(R+32*t))) ∧
  ((R+32*t)-((1*q+-4)-(R+32*t)))≤(8*t-1) ∧
  (24*t)≤((1*q+-4)-(R+32*t)) ∧
  ((1*q+-4)-(R+32*t))≤(48*t-3)
def c0_18_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_18 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  let y : ℤ := ((1*q+-4)-(R+32*t))
  let x : ℤ := ((R+32*t)-((1*q+-4)-(R+32*t)))
  have hx : (4*t)≤x ∧ x≤(8*t-1) := ⟨hc.1,hc.2.1⟩
  have hy : (24*t)≤y ∧ y≤(48*t-3) := hc.2.2
  obtain ⟨y0,y1,y2,hy0L,hy0U,hy1L,hy1U,hy2L,hy2U,hysum⟩ := split_three (8*t) (16*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,8,8,8,x,y0,y1,y2, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c1_0 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  15*(16*t)≤(((4*q+-11)-(R+24*t))-(4*t)) ∧
  14*(16*t)≤((2*t-1)-(R+24*t)+((4*q+-11)-(R+24*t))) ∧
  (((4*q+-11)-(R+24*t))-(8*t-2))≤15*(32*t-1) ∧
  ((1*t)-(R+24*t)+((4*q+-11)-(R+24*t)))≤14*(32*t-1) ∧
  (((4*q+-11)-(R+24*t))-(8*t-2))+15≤(((4*q+-11)-(R+24*t))-(4*t)) ∧
  14*(((4*q+-11)-(R+24*t))-(8*t-2))+210≤15*((2*t-1)-(R+24*t)+((4*q+-11)-(R+24*t))) ∧
  15*((1*t)-(R+24*t)+((4*q+-11)-(R+24*t)))+210≤14*(((4*q+-11)-(R+24*t))-(4*t)) ∧
  ((1*t)-(R+24*t)+((4*q+-11)-(R+24*t)))+14≤((2*t-1)-(R+24*t)+((4*q+-11)-(R+24*t)))
def c1_0_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_0 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((4*q+-11)-(R+24*t))-(8*t-2)) ((1*t)-(R+24*t)+((4*q+-11)-(R+24*t))) (((4*q+-11)-(R+24*t))-(4*t)) ((2*t-1)-(R+24*t)+((4*q+-11)-(R+24*t))) 15 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-11)-(R+24*t))-15*z
  let x : ℤ := (R+24*t)-((4*q+-11)-(R+24*t))+14*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (2*t) (4*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,2,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (2*t+1)*x + (4*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c1_1 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  15*(16*t)≤(((4*q+-12)-(R+26*t))-(4*t)) ∧
  14*(16*t)≤((2*t-1)-(R+26*t)+((4*q+-12)-(R+26*t))) ∧
  (((4*q+-12)-(R+26*t))-(8*t-2))≤15*(32*t-1) ∧
  ((1*t)-(R+26*t)+((4*q+-12)-(R+26*t)))≤14*(32*t-1) ∧
  (((4*q+-12)-(R+26*t))-(8*t-2))+15≤(((4*q+-12)-(R+26*t))-(4*t)) ∧
  14*(((4*q+-12)-(R+26*t))-(8*t-2))+210≤15*((2*t-1)-(R+26*t)+((4*q+-12)-(R+26*t))) ∧
  15*((1*t)-(R+26*t)+((4*q+-12)-(R+26*t)))+210≤14*(((4*q+-12)-(R+26*t))-(4*t)) ∧
  ((1*t)-(R+26*t)+((4*q+-12)-(R+26*t)))+14≤((2*t-1)-(R+26*t)+((4*q+-12)-(R+26*t)))
def c1_1_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_1 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((4*q+-12)-(R+26*t))-(8*t-2)) ((1*t)-(R+26*t)+((4*q+-12)-(R+26*t))) (((4*q+-12)-(R+26*t))-(4*t)) ((2*t-1)-(R+26*t)+((4*q+-12)-(R+26*t))) 15 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-12)-(R+26*t))-15*z
  let x : ℤ := (R+26*t)-((4*q+-12)-(R+26*t))+14*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (2*t) (4*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,2,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (2*t+1)*x + (4*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c1_2 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  15*(16*t)≤(((4*q+-10)-(R+22*t))-(4*t)) ∧
  14*(16*t)≤((2*t-1)-(R+22*t)+((4*q+-10)-(R+22*t))) ∧
  (((4*q+-10)-(R+22*t))-(8*t-2))≤15*(32*t-1) ∧
  ((1*t)-(R+22*t)+((4*q+-10)-(R+22*t)))≤14*(32*t-1) ∧
  (((4*q+-10)-(R+22*t))-(8*t-2))+15≤(((4*q+-10)-(R+22*t))-(4*t)) ∧
  14*(((4*q+-10)-(R+22*t))-(8*t-2))+210≤15*((2*t-1)-(R+22*t)+((4*q+-10)-(R+22*t))) ∧
  15*((1*t)-(R+22*t)+((4*q+-10)-(R+22*t)))+210≤14*(((4*q+-10)-(R+22*t))-(4*t)) ∧
  ((1*t)-(R+22*t)+((4*q+-10)-(R+22*t)))+14≤((2*t-1)-(R+22*t)+((4*q+-10)-(R+22*t)))
def c1_2_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_2 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((4*q+-10)-(R+22*t))-(8*t-2)) ((1*t)-(R+22*t)+((4*q+-10)-(R+22*t))) (((4*q+-10)-(R+22*t))-(4*t)) ((2*t-1)-(R+22*t)+((4*q+-10)-(R+22*t))) 15 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-10)-(R+22*t))-15*z
  let x : ℤ := (R+22*t)-((4*q+-10)-(R+22*t))+14*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (2*t) (4*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,2,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (2*t+1)*x + (4*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c1_3 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  15*(16*t)≤(((4*q+-10)-(R+22*t))-(2*t)) ∧
  14*(16*t)≤((4*t-2)-(R+22*t)+((4*q+-10)-(R+22*t))) ∧
  (((4*q+-10)-(R+22*t))-(4*t-1))≤15*(32*t-1) ∧
  ((2*t)-(R+22*t)+((4*q+-10)-(R+22*t)))≤14*(32*t-1) ∧
  (((4*q+-10)-(R+22*t))-(4*t-1))+15≤(((4*q+-10)-(R+22*t))-(2*t)) ∧
  14*(((4*q+-10)-(R+22*t))-(4*t-1))+210≤15*((4*t-2)-(R+22*t)+((4*q+-10)-(R+22*t))) ∧
  15*((2*t)-(R+22*t)+((4*q+-10)-(R+22*t)))+210≤14*(((4*q+-10)-(R+22*t))-(2*t)) ∧
  ((2*t)-(R+22*t)+((4*q+-10)-(R+22*t)))+14≤((4*t-2)-(R+22*t)+((4*q+-10)-(R+22*t)))
def c1_3_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_3 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((4*q+-10)-(R+22*t))-(4*t-1)) ((2*t)-(R+22*t)+((4*q+-10)-(R+22*t))) (((4*q+-10)-(R+22*t))-(2*t)) ((4*t-2)-(R+22*t)+((4*q+-10)-(R+22*t))) 15 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-10)-(R+22*t))-15*z
  let x : ℤ := (R+22*t)-((4*q+-10)-(R+22*t))+14*z
  have hx : (2*t)≤x ∧ x≤(4*t-2) := by dsimp [x]; omega
  have hy : (2*t)≤y ∧ y≤(4*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (1*t) (2*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,1,2,16,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (2*t+1)*x + (4*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c1_4 (t q R : ℤ) : Prop :=
  (8*t)≤(16*t-1) ∧
  7*(8*t)≤(((4*q+-9)-(R+20*t))-(2*t)) ∧
  6*(8*t)≤((4*t-2)-(R+20*t)+((4*q+-9)-(R+20*t))) ∧
  (((4*q+-9)-(R+20*t))-(4*t-1))≤7*(16*t-1) ∧
  ((2*t)-(R+20*t)+((4*q+-9)-(R+20*t)))≤6*(16*t-1) ∧
  (((4*q+-9)-(R+20*t))-(4*t-1))+7≤(((4*q+-9)-(R+20*t))-(2*t)) ∧
  6*(((4*q+-9)-(R+20*t))-(4*t-1))+42≤7*((4*t-2)-(R+20*t)+((4*q+-9)-(R+20*t))) ∧
  7*((2*t)-(R+20*t)+((4*q+-9)-(R+20*t)))+42≤6*(((4*q+-9)-(R+20*t))-(2*t)) ∧
  ((2*t)-(R+20*t)+((4*q+-9)-(R+20*t)))+6≤((4*t-2)-(R+20*t)+((4*q+-9)-(R+20*t)))
def c1_4_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_4 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (8*t) (16*t-1) (((4*q+-9)-(R+20*t))-(4*t-1)) ((2*t)-(R+20*t)+((4*q+-9)-(R+20*t))) (((4*q+-9)-(R+20*t))-(2*t)) ((4*t-2)-(R+20*t)+((4*q+-9)-(R+20*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-9)-(R+20*t))-7*z
  let x : ℤ := (R+20*t)-((4*q+-9)-(R+20*t))+6*z
  have hx : (2*t)≤x ∧ x≤(4*t-2) := by dsimp [x]; omega
  have hy : (2*t)≤y ∧ y≤(4*t-1) := by dsimp [y]; omega
  have hz : (8*t)≤z ∧ z≤(16*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (1*t) (2*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,1,2,8,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (2*t+1)*x + (4*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c1_5 (t q R : ℤ) : Prop :=
  (4*t)≤((R+34*t)-((1*q+-4)-(R+34*t))) ∧
  ((R+34*t)-((1*q+-4)-(R+34*t)))≤(8*t-1) ∧
  (24*t)≤((1*q+-4)-(R+34*t)) ∧
  ((1*q+-4)-(R+34*t))≤(48*t-3)
def c1_5_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_5 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  let y : ℤ := ((1*q+-4)-(R+34*t))
  let x : ℤ := ((R+34*t)-((1*q+-4)-(R+34*t)))
  have hx : (4*t)≤x ∧ x≤(8*t-1) := ⟨hc.1,hc.2.1⟩
  have hy : (24*t)≤y ∧ y≤(48*t-3) := hc.2.2
  obtain ⟨y0,y1,y2,hy0L,hy0U,hy1L,hy1U,hy2L,hy2U,hysum⟩ := split_three (8*t) (16*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,8,8,8,x,y0,y1,y2, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c1_6 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-10)-(R+42*t))-(8*t)) ∧
  6*(16*t)≤((4*t-1)-(R+42*t)+((2*q+-10)-(R+42*t))) ∧
  (((2*q+-10)-(R+42*t))-(16*t-2))≤7*(32*t-1) ∧
  ((2*t)-(R+42*t)+((2*q+-10)-(R+42*t)))≤6*(32*t-1) ∧
  (((2*q+-10)-(R+42*t))-(16*t-2))+7≤(((2*q+-10)-(R+42*t))-(8*t)) ∧
  6*(((2*q+-10)-(R+42*t))-(16*t-2))+42≤7*((4*t-1)-(R+42*t)+((2*q+-10)-(R+42*t))) ∧
  7*((2*t)-(R+42*t)+((2*q+-10)-(R+42*t)))+42≤6*(((2*q+-10)-(R+42*t))-(8*t)) ∧
  ((2*t)-(R+42*t)+((2*q+-10)-(R+42*t)))+6≤((4*t-1)-(R+42*t)+((2*q+-10)-(R+42*t)))
def c1_6_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_6 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-10)-(R+42*t))-(16*t-2)) ((2*t)-(R+42*t)+((2*q+-10)-(R+42*t))) (((2*q+-10)-(R+42*t))-(8*t)) ((4*t-1)-(R+42*t)+((2*q+-10)-(R+42*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-10)-(R+42*t))-7*z
  let x : ℤ := (R+42*t)-((2*q+-10)-(R+42*t))+6*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c1_7 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  3*(16*t)≤(((1*q+-5)-(R+42*t))-(8*t)) ∧
  2*(16*t)≤((16*t-2)-(R+42*t)+((1*q+-5)-(R+42*t))) ∧
  (((1*q+-5)-(R+42*t))-(16*t-1))≤3*(32*t-1) ∧
  ((8*t)-(R+42*t)+((1*q+-5)-(R+42*t)))≤2*(32*t-1) ∧
  (((1*q+-5)-(R+42*t))-(16*t-1))+3≤(((1*q+-5)-(R+42*t))-(8*t)) ∧
  2*(((1*q+-5)-(R+42*t))-(16*t-1))+6≤3*((16*t-2)-(R+42*t)+((1*q+-5)-(R+42*t))) ∧
  3*((8*t)-(R+42*t)+((1*q+-5)-(R+42*t)))+6≤2*(((1*q+-5)-(R+42*t))-(8*t)) ∧
  ((8*t)-(R+42*t)+((1*q+-5)-(R+42*t)))+2≤((16*t-2)-(R+42*t)+((1*q+-5)-(R+42*t)))
def c1_7_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_7 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((1*q+-5)-(R+42*t))-(16*t-1)) ((8*t)-(R+42*t)+((1*q+-5)-(R+42*t))) (((1*q+-5)-(R+42*t))-(8*t)) ((16*t-2)-(R+42*t)+((1*q+-5)-(R+42*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((1*q+-5)-(R+42*t))-3*z
  let x : ℤ := (R+42*t)-((1*q+-5)-(R+42*t))+2*z
  have hx : (8*t)≤x ∧ x≤(16*t-2) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (4*t) (8*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,4,8,16,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (8*t+1)*x + (16*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c1_8 (t q R : ℤ) : Prop :=
  (8*t)≤((R+42*t)-((1*q+-5)-(R+42*t))) ∧
  ((R+42*t)-((1*q+-5)-(R+42*t)))≤(16*t-2) ∧
  (16*t)≤((1*q+-5)-(R+42*t)) ∧
  ((1*q+-5)-(R+42*t))≤(32*t-2)
def c1_8_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_8 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  let y : ℤ := ((1*q+-5)-(R+42*t))
  let x : ℤ := ((R+42*t)-((1*q+-5)-(R+42*t)))
  have hx : (8*t)≤x ∧ x≤(16*t-2) := ⟨hc.1,hc.2.1⟩
  have hy : (16*t)≤y ∧ y≤(32*t-2) := hc.2.2
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (4*t) (8*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (8*t) (16*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,4,8,8,x0,x1,y0,y1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum,← hysum]
        ring

def c1_9 (t q R : ℤ) : Prop :=
  (12*t)≤((R+34*t)-((1*q+-4)-(R+34*t))) ∧
  ((R+34*t)-((1*q+-4)-(R+34*t)))≤(24*t-3) ∧
  (8*t)≤((1*q+-4)-(R+34*t)) ∧
  ((1*q+-4)-(R+34*t))≤(16*t-1)
def c1_9_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_9 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  let y : ℤ := ((1*q+-4)-(R+34*t))
  let x : ℤ := ((R+34*t)-((1*q+-4)-(R+34*t)))
  have hx : (12*t)≤x ∧ x≤(24*t-3) := ⟨hc.1,hc.2.1⟩
  have hy : (8*t)≤y ∧ y≤(16*t-1) := hc.2.2
  obtain ⟨x0,x1,x2,hx0L,hx0U,hx1L,hx1U,hx2L,hx2U,hxsum⟩ := split_three (4*t) (8*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,4,4,8,x0,x1,x2,y, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c1_10 (t q R : ℤ) : Prop :=
  (12*t)≤((R+26*t)-((1*q+-3)-(R+26*t))) ∧
  ((R+26*t)-((1*q+-3)-(R+26*t)))≤(24*t-3) ∧
  (8*t)≤((1*q+-3)-(R+26*t)) ∧
  ((1*q+-3)-(R+26*t))≤(16*t-1)
def c1_10_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_10 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  let y : ℤ := ((1*q+-3)-(R+26*t))
  let x : ℤ := ((R+26*t)-((1*q+-3)-(R+26*t)))
  have hx : (12*t)≤x ∧ x≤(24*t-3) := ⟨hc.1,hc.2.1⟩
  have hy : (8*t)≤y ∧ y≤(16*t-1) := hc.2.2
  obtain ⟨x0,x1,x2,hx0L,hx0U,hx1L,hx1U,hx2L,hx2U,hxsum⟩ := split_three (4*t) (8*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,4,4,8,x0,x1,x2,y, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c1_11 (t q R : ℤ) : Prop :=
  (8*t)≤(16*t-1) ∧
  3*(8*t)≤(((2*q+-7)-(R+30*t))-(8*t)) ∧
  2*(8*t)≤((4*t-1)-(R+30*t)+((2*q+-7)-(R+30*t))) ∧
  (((2*q+-7)-(R+30*t))-(16*t-2))≤3*(16*t-1) ∧
  ((2*t)-(R+30*t)+((2*q+-7)-(R+30*t)))≤2*(16*t-1) ∧
  (((2*q+-7)-(R+30*t))-(16*t-2))+3≤(((2*q+-7)-(R+30*t))-(8*t)) ∧
  2*(((2*q+-7)-(R+30*t))-(16*t-2))+6≤3*((4*t-1)-(R+30*t)+((2*q+-7)-(R+30*t))) ∧
  3*((2*t)-(R+30*t)+((2*q+-7)-(R+30*t)))+6≤2*(((2*q+-7)-(R+30*t))-(8*t)) ∧
  ((2*t)-(R+30*t)+((2*q+-7)-(R+30*t)))+2≤((4*t-1)-(R+30*t)+((2*q+-7)-(R+30*t)))
def c1_11_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_11 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (8*t) (16*t-1) (((2*q+-7)-(R+30*t))-(16*t-2)) ((2*t)-(R+30*t)+((2*q+-7)-(R+30*t))) (((2*q+-7)-(R+30*t))-(8*t)) ((4*t-1)-(R+30*t)+((2*q+-7)-(R+30*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-7)-(R+30*t))-3*z
  let x : ℤ := (R+30*t)-((2*q+-7)-(R+30*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (8*t)≤z ∧ z≤(16*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,8,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c1_12 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-2) ∧
  3*(16*t)≤(((2*q+-9)-(R+38*t))-(4*t)) ∧
  2*(16*t)≤((4*t-1)-(R+38*t)+((2*q+-9)-(R+38*t))) ∧
  (((2*q+-9)-(R+38*t))-(8*t-1))≤3*(32*t-2) ∧
  ((2*t)-(R+38*t)+((2*q+-9)-(R+38*t)))≤2*(32*t-2) ∧
  (((2*q+-9)-(R+38*t))-(8*t-1))+3≤(((2*q+-9)-(R+38*t))-(4*t)) ∧
  2*(((2*q+-9)-(R+38*t))-(8*t-1))+6≤3*((4*t-1)-(R+38*t)+((2*q+-9)-(R+38*t))) ∧
  3*((2*t)-(R+38*t)+((2*q+-9)-(R+38*t)))+6≤2*(((2*q+-9)-(R+38*t))-(4*t)) ∧
  ((2*t)-(R+38*t)+((2*q+-9)-(R+38*t)))+2≤((4*t-1)-(R+38*t)+((2*q+-9)-(R+38*t)))
def c1_12_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_12 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-2) (((2*q+-9)-(R+38*t))-(8*t-1)) ((2*t)-(R+38*t)+((2*q+-9)-(R+38*t))) (((2*q+-9)-(R+38*t))-(4*t)) ((4*t-1)-(R+38*t)+((2*q+-9)-(R+38*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-9)-(R+38*t))-3*z
  let x : ℤ := (R+38*t)-((2*q+-9)-(R+38*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-2) := ⟨hzL,hzU⟩
  obtain ⟨z0,z1,hz0L,hz0U,hz1L,hz1U,hzsum⟩ := split_two (8*t) (16*t-1) z (by omega) (by rcases hz with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,8,8,x,y,z0,z1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hzsum]
        ring

def c1_13 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-2) ∧
  3*(16*t)≤(((2*q+-7)-(R+30*t))-(4*t)) ∧
  2*(16*t)≤((4*t-1)-(R+30*t)+((2*q+-7)-(R+30*t))) ∧
  (((2*q+-7)-(R+30*t))-(8*t-1))≤3*(32*t-2) ∧
  ((2*t)-(R+30*t)+((2*q+-7)-(R+30*t)))≤2*(32*t-2) ∧
  (((2*q+-7)-(R+30*t))-(8*t-1))+3≤(((2*q+-7)-(R+30*t))-(4*t)) ∧
  2*(((2*q+-7)-(R+30*t))-(8*t-1))+6≤3*((4*t-1)-(R+30*t)+((2*q+-7)-(R+30*t))) ∧
  3*((2*t)-(R+30*t)+((2*q+-7)-(R+30*t)))+6≤2*(((2*q+-7)-(R+30*t))-(4*t)) ∧
  ((2*t)-(R+30*t)+((2*q+-7)-(R+30*t)))+2≤((4*t-1)-(R+30*t)+((2*q+-7)-(R+30*t)))
def c1_13_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_13 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-2) (((2*q+-7)-(R+30*t))-(8*t-1)) ((2*t)-(R+30*t)+((2*q+-7)-(R+30*t))) (((2*q+-7)-(R+30*t))-(4*t)) ((4*t-1)-(R+30*t)+((2*q+-7)-(R+30*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-7)-(R+30*t))-3*z
  let x : ℤ := (R+30*t)-((2*q+-7)-(R+30*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-2) := ⟨hzL,hzU⟩
  obtain ⟨z0,z1,hz0L,hz0U,hz1L,hz1U,hzsum⟩ := split_two (8*t) (16*t-1) z (by omega) (by rcases hz with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,8,8,x,y,z0,z1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hzsum]
        ring

def c1_14 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-2) ∧
  3*(16*t)≤(((2*q+-6)-(R+26*t))-(4*t)) ∧
  2*(16*t)≤((4*t-1)-(R+26*t)+((2*q+-6)-(R+26*t))) ∧
  (((2*q+-6)-(R+26*t))-(8*t-1))≤3*(32*t-2) ∧
  ((2*t)-(R+26*t)+((2*q+-6)-(R+26*t)))≤2*(32*t-2) ∧
  (((2*q+-6)-(R+26*t))-(8*t-1))+3≤(((2*q+-6)-(R+26*t))-(4*t)) ∧
  2*(((2*q+-6)-(R+26*t))-(8*t-1))+6≤3*((4*t-1)-(R+26*t)+((2*q+-6)-(R+26*t))) ∧
  3*((2*t)-(R+26*t)+((2*q+-6)-(R+26*t)))+6≤2*(((2*q+-6)-(R+26*t))-(4*t)) ∧
  ((2*t)-(R+26*t)+((2*q+-6)-(R+26*t)))+2≤((4*t-1)-(R+26*t)+((2*q+-6)-(R+26*t)))
def c1_14_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_14 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-2) (((2*q+-6)-(R+26*t))-(8*t-1)) ((2*t)-(R+26*t)+((2*q+-6)-(R+26*t))) (((2*q+-6)-(R+26*t))-(4*t)) ((4*t-1)-(R+26*t)+((2*q+-6)-(R+26*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-6)-(R+26*t))-3*z
  let x : ℤ := (R+26*t)-((2*q+-6)-(R+26*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-2) := ⟨hzL,hzU⟩
  obtain ⟨z0,z1,hz0L,hz0U,hz1L,hz1U,hzsum⟩ := split_two (8*t) (16*t-1) z (by omega) (by rcases hz with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,8,8,x,y,z0,z1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hzsum]
        ring

def c1_15 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-8)-(R+34*t))-(8*t)) ∧
  6*(16*t)≤((4*t-1)-(R+34*t)+((2*q+-8)-(R+34*t))) ∧
  (((2*q+-8)-(R+34*t))-(16*t-2))≤7*(32*t-1) ∧
  ((2*t)-(R+34*t)+((2*q+-8)-(R+34*t)))≤6*(32*t-1) ∧
  (((2*q+-8)-(R+34*t))-(16*t-2))+7≤(((2*q+-8)-(R+34*t))-(8*t)) ∧
  6*(((2*q+-8)-(R+34*t))-(16*t-2))+42≤7*((4*t-1)-(R+34*t)+((2*q+-8)-(R+34*t))) ∧
  7*((2*t)-(R+34*t)+((2*q+-8)-(R+34*t)))+42≤6*(((2*q+-8)-(R+34*t))-(8*t)) ∧
  ((2*t)-(R+34*t)+((2*q+-8)-(R+34*t)))+6≤((4*t-1)-(R+34*t)+((2*q+-8)-(R+34*t)))
def c1_15_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_15 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-8)-(R+34*t))-(16*t-2)) ((2*t)-(R+34*t)+((2*q+-8)-(R+34*t))) (((2*q+-8)-(R+34*t))-(8*t)) ((4*t-1)-(R+34*t)+((2*q+-8)-(R+34*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-8)-(R+34*t))-7*z
  let x : ℤ := (R+34*t)-((2*q+-8)-(R+34*t))+6*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c1_16 (t q R : ℤ) : Prop :=
  (8*t)≤(16*t-1) ∧
  3*(8*t)≤(((2*q+-6)-(R+26*t))-(8*t)) ∧
  2*(8*t)≤((4*t-1)-(R+26*t)+((2*q+-6)-(R+26*t))) ∧
  (((2*q+-6)-(R+26*t))-(16*t-2))≤3*(16*t-1) ∧
  ((2*t)-(R+26*t)+((2*q+-6)-(R+26*t)))≤2*(16*t-1) ∧
  (((2*q+-6)-(R+26*t))-(16*t-2))+3≤(((2*q+-6)-(R+26*t))-(8*t)) ∧
  2*(((2*q+-6)-(R+26*t))-(16*t-2))+6≤3*((4*t-1)-(R+26*t)+((2*q+-6)-(R+26*t))) ∧
  3*((2*t)-(R+26*t)+((2*q+-6)-(R+26*t)))+6≤2*(((2*q+-6)-(R+26*t))-(8*t)) ∧
  ((2*t)-(R+26*t)+((2*q+-6)-(R+26*t)))+2≤((4*t-1)-(R+26*t)+((2*q+-6)-(R+26*t)))
def c1_16_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_16 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (8*t) (16*t-1) (((2*q+-6)-(R+26*t))-(16*t-2)) ((2*t)-(R+26*t)+((2*q+-6)-(R+26*t))) (((2*q+-6)-(R+26*t))-(8*t)) ((4*t-1)-(R+26*t)+((2*q+-6)-(R+26*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-6)-(R+26*t))-3*z
  let x : ℤ := (R+26*t)-((2*q+-6)-(R+26*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (8*t)≤z ∧ z≤(16*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,8,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c1_17 (t q R : ℤ) : Prop :=
  (8*t)≤(16*t-1) ∧
  3*(8*t)≤(((2*q+-5)-(R+22*t))-(8*t)) ∧
  2*(8*t)≤((4*t-1)-(R+22*t)+((2*q+-5)-(R+22*t))) ∧
  (((2*q+-5)-(R+22*t))-(16*t-2))≤3*(16*t-1) ∧
  ((2*t)-(R+22*t)+((2*q+-5)-(R+22*t)))≤2*(16*t-1) ∧
  (((2*q+-5)-(R+22*t))-(16*t-2))+3≤(((2*q+-5)-(R+22*t))-(8*t)) ∧
  2*(((2*q+-5)-(R+22*t))-(16*t-2))+6≤3*((4*t-1)-(R+22*t)+((2*q+-5)-(R+22*t))) ∧
  3*((2*t)-(R+22*t)+((2*q+-5)-(R+22*t)))+6≤2*(((2*q+-5)-(R+22*t))-(8*t)) ∧
  ((2*t)-(R+22*t)+((2*q+-5)-(R+22*t)))+2≤((4*t-1)-(R+22*t)+((2*q+-5)-(R+22*t)))
def c1_17_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_17 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (8*t) (16*t-1) (((2*q+-5)-(R+22*t))-(16*t-2)) ((2*t)-(R+22*t)+((2*q+-5)-(R+22*t))) (((2*q+-5)-(R+22*t))-(8*t)) ((4*t-1)-(R+22*t)+((2*q+-5)-(R+22*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-5)-(R+22*t))-3*z
  let x : ℤ := (R+22*t)-((2*q+-5)-(R+22*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (8*t)≤z ∧ z≤(16*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,8,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c1_18 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-2) ∧
  7*(16*t)≤(((4*q+-10)-(R+22*t))-(2*t)) ∧
  6*(16*t)≤((2*t-1)-(R+22*t)+((4*q+-10)-(R+22*t))) ∧
  (((4*q+-10)-(R+22*t))-(4*t-1))≤7*(32*t-2) ∧
  ((1*t)-(R+22*t)+((4*q+-10)-(R+22*t)))≤6*(32*t-2) ∧
  (((4*q+-10)-(R+22*t))-(4*t-1))+7≤(((4*q+-10)-(R+22*t))-(2*t)) ∧
  6*(((4*q+-10)-(R+22*t))-(4*t-1))+42≤7*((2*t-1)-(R+22*t)+((4*q+-10)-(R+22*t))) ∧
  7*((1*t)-(R+22*t)+((4*q+-10)-(R+22*t)))+42≤6*(((4*q+-10)-(R+22*t))-(2*t)) ∧
  ((1*t)-(R+22*t)+((4*q+-10)-(R+22*t)))+6≤((2*t-1)-(R+22*t)+((4*q+-10)-(R+22*t)))
def c1_18_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_18 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-2) (((4*q+-10)-(R+22*t))-(4*t-1)) ((1*t)-(R+22*t)+((4*q+-10)-(R+22*t))) (((4*q+-10)-(R+22*t))-(2*t)) ((2*t-1)-(R+22*t)+((4*q+-10)-(R+22*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-10)-(R+22*t))-7*z
  let x : ℤ := (R+22*t)-((4*q+-10)-(R+22*t))+6*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (2*t)≤y ∧ y≤(4*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-2) := ⟨hzL,hzU⟩
  obtain ⟨z0,z1,hz0L,hz0U,hz1L,hz1U,hzsum⟩ := split_two (8*t) (16*t-1) z (by omega) (by rcases hz with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,8,8,x,y,z0,z1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (2*t+1)*x + (4*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hzsum]
        ring

def c1_19 (t q R : ℤ) : Prop :=
  (8*t)≤((R+34*t)-((1*q+-4)-(R+34*t))) ∧
  ((R+34*t)-((1*q+-4)-(R+34*t)))≤(16*t-2) ∧
  (16*t)≤((1*q+-4)-(R+34*t)) ∧
  ((1*q+-4)-(R+34*t))≤(32*t-2)
def c1_19_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_19 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  let y : ℤ := ((1*q+-4)-(R+34*t))
  let x : ℤ := ((R+34*t)-((1*q+-4)-(R+34*t)))
  have hx : (8*t)≤x ∧ x≤(16*t-2) := ⟨hc.1,hc.2.1⟩
  have hy : (16*t)≤y ∧ y≤(32*t-2) := hc.2.2
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (4*t) (8*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (8*t) (16*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,4,8,8,x0,x1,y0,y1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum,← hysum]
        ring

def c2_0 (t q R : ℤ) : Prop :=
  (8*t)≤((R+36*t)-((1*q+-4)-(R+36*t))) ∧
  ((R+36*t)-((1*q+-4)-(R+36*t)))≤(16*t-2) ∧
  (16*t)≤((1*q+-4)-(R+36*t)) ∧
  ((1*q+-4)-(R+36*t))≤(32*t-2)
def c2_0_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_0 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  let y : ℤ := ((1*q+-4)-(R+36*t))
  let x : ℤ := ((R+36*t)-((1*q+-4)-(R+36*t)))
  have hx : (8*t)≤x ∧ x≤(16*t-2) := ⟨hc.1,hc.2.1⟩
  have hy : (16*t)≤y ∧ y≤(32*t-2) := hc.2.2
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (4*t) (8*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (8*t) (16*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,4,8,8,x0,x1,y0,y1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum,← hysum]
        ring

def c2_1 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-2) ∧
  3*(16*t)≤(((2*q+-7)-(R+32*t))-(4*t)) ∧
  2*(16*t)≤((4*t-1)-(R+32*t)+((2*q+-7)-(R+32*t))) ∧
  (((2*q+-7)-(R+32*t))-(8*t-1))≤3*(32*t-2) ∧
  ((2*t)-(R+32*t)+((2*q+-7)-(R+32*t)))≤2*(32*t-2) ∧
  (((2*q+-7)-(R+32*t))-(8*t-1))+3≤(((2*q+-7)-(R+32*t))-(4*t)) ∧
  2*(((2*q+-7)-(R+32*t))-(8*t-1))+6≤3*((4*t-1)-(R+32*t)+((2*q+-7)-(R+32*t))) ∧
  3*((2*t)-(R+32*t)+((2*q+-7)-(R+32*t)))+6≤2*(((2*q+-7)-(R+32*t))-(4*t)) ∧
  ((2*t)-(R+32*t)+((2*q+-7)-(R+32*t)))+2≤((4*t-1)-(R+32*t)+((2*q+-7)-(R+32*t)))
def c2_1_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_1 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-2) (((2*q+-7)-(R+32*t))-(8*t-1)) ((2*t)-(R+32*t)+((2*q+-7)-(R+32*t))) (((2*q+-7)-(R+32*t))-(4*t)) ((4*t-1)-(R+32*t)+((2*q+-7)-(R+32*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-7)-(R+32*t))-3*z
  let x : ℤ := (R+32*t)-((2*q+-7)-(R+32*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-2) := ⟨hzL,hzU⟩
  obtain ⟨z0,z1,hz0L,hz0U,hz1L,hz1U,hzsum⟩ := split_two (8*t) (16*t-1) z (by omega) (by rcases hz with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,8,8,x,y,z0,z1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hzsum]
        ring

def c2_2 (t q R : ℤ) : Prop :=
  (12*t)≤((R+28*t)-((1*q+-3)-(R+28*t))) ∧
  ((R+28*t)-((1*q+-3)-(R+28*t)))≤(24*t-3) ∧
  (8*t)≤((1*q+-3)-(R+28*t)) ∧
  ((1*q+-3)-(R+28*t))≤(16*t-1)
def c2_2_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_2 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  let y : ℤ := ((1*q+-3)-(R+28*t))
  let x : ℤ := ((R+28*t)-((1*q+-3)-(R+28*t)))
  have hx : (12*t)≤x ∧ x≤(24*t-3) := ⟨hc.1,hc.2.1⟩
  have hy : (8*t)≤y ∧ y≤(16*t-1) := hc.2.2
  obtain ⟨x0,x1,x2,hx0L,hx0U,hx1L,hx1U,hx2L,hx2U,hxsum⟩ := split_three (4*t) (8*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,4,4,8,x0,x1,x2,y, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c2_3 (t q R : ℤ) : Prop :=
  (4*t)≤((R+36*t)-((1*q+-4)-(R+36*t))) ∧
  ((R+36*t)-((1*q+-4)-(R+36*t)))≤(8*t-1) ∧
  (24*t)≤((1*q+-4)-(R+36*t)) ∧
  ((1*q+-4)-(R+36*t))≤(48*t-3)
def c2_3_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_3 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  let y : ℤ := ((1*q+-4)-(R+36*t))
  let x : ℤ := ((R+36*t)-((1*q+-4)-(R+36*t)))
  have hx : (4*t)≤x ∧ x≤(8*t-1) := ⟨hc.1,hc.2.1⟩
  have hy : (24*t)≤y ∧ y≤(48*t-3) := hc.2.2
  obtain ⟨y0,y1,y2,hy0L,hy0U,hy1L,hy1U,hy2L,hy2U,hysum⟩ := split_three (8*t) (16*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,8,8,8,x,y0,y1,y2, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c2_4 (t q R : ℤ) : Prop :=
  (8*t)≤((R+28*t)-((1*q+-3)-(R+28*t))) ∧
  ((R+28*t)-((1*q+-3)-(R+28*t)))≤(16*t-2) ∧
  (16*t)≤((1*q+-3)-(R+28*t)) ∧
  ((1*q+-3)-(R+28*t))≤(32*t-2)
def c2_4_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_4 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  let y : ℤ := ((1*q+-3)-(R+28*t))
  let x : ℤ := ((R+28*t)-((1*q+-3)-(R+28*t)))
  have hx : (8*t)≤x ∧ x≤(16*t-2) := ⟨hc.1,hc.2.1⟩
  have hy : (16*t)≤y ∧ y≤(32*t-2) := hc.2.2
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (4*t) (8*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (8*t) (16*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,4,8,8,x0,x1,y0,y1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum,← hysum]
        ring

def c2_5 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-2) ∧
  7*(16*t)≤(((4*q+-14)-(R+32*t))-(2*t)) ∧
  6*(16*t)≤((2*t-1)-(R+32*t)+((4*q+-14)-(R+32*t))) ∧
  (((4*q+-14)-(R+32*t))-(4*t-1))≤7*(32*t-2) ∧
  ((1*t)-(R+32*t)+((4*q+-14)-(R+32*t)))≤6*(32*t-2) ∧
  (((4*q+-14)-(R+32*t))-(4*t-1))+7≤(((4*q+-14)-(R+32*t))-(2*t)) ∧
  6*(((4*q+-14)-(R+32*t))-(4*t-1))+42≤7*((2*t-1)-(R+32*t)+((4*q+-14)-(R+32*t))) ∧
  7*((1*t)-(R+32*t)+((4*q+-14)-(R+32*t)))+42≤6*(((4*q+-14)-(R+32*t))-(2*t)) ∧
  ((1*t)-(R+32*t)+((4*q+-14)-(R+32*t)))+6≤((2*t-1)-(R+32*t)+((4*q+-14)-(R+32*t)))
def c2_5_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_5 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-2) (((4*q+-14)-(R+32*t))-(4*t-1)) ((1*t)-(R+32*t)+((4*q+-14)-(R+32*t))) (((4*q+-14)-(R+32*t))-(2*t)) ((2*t-1)-(R+32*t)+((4*q+-14)-(R+32*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-14)-(R+32*t))-7*z
  let x : ℤ := (R+32*t)-((4*q+-14)-(R+32*t))+6*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (2*t)≤y ∧ y≤(4*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-2) := ⟨hzL,hzU⟩
  obtain ⟨z0,z1,hz0L,hz0U,hz1L,hz1U,hzsum⟩ := split_two (8*t) (16*t-1) z (by omega) (by rcases hz with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,8,8,x,y,z0,z1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (2*t+1)*x + (4*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hzsum]
        ring

def c2_6 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-2) ∧
  7*(16*t)≤(((4*q+-13)-(R+30*t))-(2*t)) ∧
  6*(16*t)≤((2*t-1)-(R+30*t)+((4*q+-13)-(R+30*t))) ∧
  (((4*q+-13)-(R+30*t))-(4*t-1))≤7*(32*t-2) ∧
  ((1*t)-(R+30*t)+((4*q+-13)-(R+30*t)))≤6*(32*t-2) ∧
  (((4*q+-13)-(R+30*t))-(4*t-1))+7≤(((4*q+-13)-(R+30*t))-(2*t)) ∧
  6*(((4*q+-13)-(R+30*t))-(4*t-1))+42≤7*((2*t-1)-(R+30*t)+((4*q+-13)-(R+30*t))) ∧
  7*((1*t)-(R+30*t)+((4*q+-13)-(R+30*t)))+42≤6*(((4*q+-13)-(R+30*t))-(2*t)) ∧
  ((1*t)-(R+30*t)+((4*q+-13)-(R+30*t)))+6≤((2*t-1)-(R+30*t)+((4*q+-13)-(R+30*t)))
def c2_6_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_6 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-2) (((4*q+-13)-(R+30*t))-(4*t-1)) ((1*t)-(R+30*t)+((4*q+-13)-(R+30*t))) (((4*q+-13)-(R+30*t))-(2*t)) ((2*t-1)-(R+30*t)+((4*q+-13)-(R+30*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-13)-(R+30*t))-7*z
  let x : ℤ := (R+30*t)-((4*q+-13)-(R+30*t))+6*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (2*t)≤y ∧ y≤(4*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-2) := ⟨hzL,hzU⟩
  obtain ⟨z0,z1,hz0L,hz0U,hz1L,hz1U,hzsum⟩ := split_two (8*t) (16*t-1) z (by omega) (by rcases hz with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,8,8,x,y,z0,z1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (2*t+1)*x + (4*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hzsum]
        ring

def c2_7 (t q R : ℤ) : Prop :=
  (8*t)≤(16*t-1) ∧
  3*(8*t)≤(((2*q+-5)-(R+24*t))-(4*t)) ∧
  2*(8*t)≤((8*t-2)-(R+24*t)+((2*q+-5)-(R+24*t))) ∧
  (((2*q+-5)-(R+24*t))-(8*t-1))≤3*(16*t-1) ∧
  ((4*t)-(R+24*t)+((2*q+-5)-(R+24*t)))≤2*(16*t-1) ∧
  (((2*q+-5)-(R+24*t))-(8*t-1))+3≤(((2*q+-5)-(R+24*t))-(4*t)) ∧
  2*(((2*q+-5)-(R+24*t))-(8*t-1))+6≤3*((8*t-2)-(R+24*t)+((2*q+-5)-(R+24*t))) ∧
  3*((4*t)-(R+24*t)+((2*q+-5)-(R+24*t)))+6≤2*(((2*q+-5)-(R+24*t))-(4*t)) ∧
  ((4*t)-(R+24*t)+((2*q+-5)-(R+24*t)))+2≤((8*t-2)-(R+24*t)+((2*q+-5)-(R+24*t)))
def c2_7_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_7 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (8*t) (16*t-1) (((2*q+-5)-(R+24*t))-(8*t-1)) ((4*t)-(R+24*t)+((2*q+-5)-(R+24*t))) (((2*q+-5)-(R+24*t))-(4*t)) ((8*t-2)-(R+24*t)+((2*q+-5)-(R+24*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-5)-(R+24*t))-3*z
  let x : ℤ := (R+24*t)-((2*q+-5)-(R+24*t))+2*z
  have hx : (4*t)≤x ∧ x≤(8*t-2) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (8*t)≤z ∧ z≤(16*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (2*t) (4*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,2,4,8,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c2_8 (t q R : ℤ) : Prop :=
  (8*t)≤(16*t-1) ∧
  3*(8*t)≤(((2*q+-4)-(R+20*t))-(8*t)) ∧
  2*(8*t)≤((4*t-1)-(R+20*t)+((2*q+-4)-(R+20*t))) ∧
  (((2*q+-4)-(R+20*t))-(16*t-2))≤3*(16*t-1) ∧
  ((2*t)-(R+20*t)+((2*q+-4)-(R+20*t)))≤2*(16*t-1) ∧
  (((2*q+-4)-(R+20*t))-(16*t-2))+3≤(((2*q+-4)-(R+20*t))-(8*t)) ∧
  2*(((2*q+-4)-(R+20*t))-(16*t-2))+6≤3*((4*t-1)-(R+20*t)+((2*q+-4)-(R+20*t))) ∧
  3*((2*t)-(R+20*t)+((2*q+-4)-(R+20*t)))+6≤2*(((2*q+-4)-(R+20*t))-(8*t)) ∧
  ((2*t)-(R+20*t)+((2*q+-4)-(R+20*t)))+2≤((4*t-1)-(R+20*t)+((2*q+-4)-(R+20*t)))
def c2_8_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_8 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (8*t) (16*t-1) (((2*q+-4)-(R+20*t))-(16*t-2)) ((2*t)-(R+20*t)+((2*q+-4)-(R+20*t))) (((2*q+-4)-(R+20*t))-(8*t)) ((4*t-1)-(R+20*t)+((2*q+-4)-(R+20*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-4)-(R+20*t))-3*z
  let x : ℤ := (R+20*t)-((2*q+-4)-(R+20*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (8*t)≤z ∧ z≤(16*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,8,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c2_9 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-8)-(R+36*t))-(4*t)) ∧
  6*(16*t)≤((8*t-2)-(R+36*t)+((2*q+-8)-(R+36*t))) ∧
  (((2*q+-8)-(R+36*t))-(8*t-1))≤7*(32*t-1) ∧
  ((4*t)-(R+36*t)+((2*q+-8)-(R+36*t)))≤6*(32*t-1) ∧
  (((2*q+-8)-(R+36*t))-(8*t-1))+7≤(((2*q+-8)-(R+36*t))-(4*t)) ∧
  6*(((2*q+-8)-(R+36*t))-(8*t-1))+42≤7*((8*t-2)-(R+36*t)+((2*q+-8)-(R+36*t))) ∧
  7*((4*t)-(R+36*t)+((2*q+-8)-(R+36*t)))+42≤6*(((2*q+-8)-(R+36*t))-(4*t)) ∧
  ((4*t)-(R+36*t)+((2*q+-8)-(R+36*t)))+6≤((8*t-2)-(R+36*t)+((2*q+-8)-(R+36*t)))
def c2_9_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_9 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-8)-(R+36*t))-(8*t-1)) ((4*t)-(R+36*t)+((2*q+-8)-(R+36*t))) (((2*q+-8)-(R+36*t))-(4*t)) ((8*t-2)-(R+36*t)+((2*q+-8)-(R+36*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-8)-(R+36*t))-7*z
  let x : ℤ := (R+36*t)-((2*q+-8)-(R+36*t))+6*z
  have hx : (4*t)≤x ∧ x≤(8*t-2) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (2*t) (4*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,2,4,16,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c2_10 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  15*(16*t)≤(((4*q+-10)-(R+24*t))-(4*t)) ∧
  14*(16*t)≤((2*t-1)-(R+24*t)+((4*q+-10)-(R+24*t))) ∧
  (((4*q+-10)-(R+24*t))-(8*t-2))≤15*(32*t-1) ∧
  ((1*t)-(R+24*t)+((4*q+-10)-(R+24*t)))≤14*(32*t-1) ∧
  (((4*q+-10)-(R+24*t))-(8*t-2))+15≤(((4*q+-10)-(R+24*t))-(4*t)) ∧
  14*(((4*q+-10)-(R+24*t))-(8*t-2))+210≤15*((2*t-1)-(R+24*t)+((4*q+-10)-(R+24*t))) ∧
  15*((1*t)-(R+24*t)+((4*q+-10)-(R+24*t)))+210≤14*(((4*q+-10)-(R+24*t))-(4*t)) ∧
  ((1*t)-(R+24*t)+((4*q+-10)-(R+24*t)))+14≤((2*t-1)-(R+24*t)+((4*q+-10)-(R+24*t)))
def c2_10_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_10 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((4*q+-10)-(R+24*t))-(8*t-2)) ((1*t)-(R+24*t)+((4*q+-10)-(R+24*t))) (((4*q+-10)-(R+24*t))-(4*t)) ((2*t-1)-(R+24*t)+((4*q+-10)-(R+24*t))) 15 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-10)-(R+24*t))-15*z
  let x : ℤ := (R+24*t)-((4*q+-10)-(R+24*t))+14*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (2*t) (4*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,2,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (2*t+1)*x + (4*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c2_11 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-2) ∧
  7*(16*t)≤(((4*q+-12)-(R+28*t))-(2*t)) ∧
  6*(16*t)≤((2*t-1)-(R+28*t)+((4*q+-12)-(R+28*t))) ∧
  (((4*q+-12)-(R+28*t))-(4*t-1))≤7*(32*t-2) ∧
  ((1*t)-(R+28*t)+((4*q+-12)-(R+28*t)))≤6*(32*t-2) ∧
  (((4*q+-12)-(R+28*t))-(4*t-1))+7≤(((4*q+-12)-(R+28*t))-(2*t)) ∧
  6*(((4*q+-12)-(R+28*t))-(4*t-1))+42≤7*((2*t-1)-(R+28*t)+((4*q+-12)-(R+28*t))) ∧
  7*((1*t)-(R+28*t)+((4*q+-12)-(R+28*t)))+42≤6*(((4*q+-12)-(R+28*t))-(2*t)) ∧
  ((1*t)-(R+28*t)+((4*q+-12)-(R+28*t)))+6≤((2*t-1)-(R+28*t)+((4*q+-12)-(R+28*t)))
def c2_11_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_11 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-2) (((4*q+-12)-(R+28*t))-(4*t-1)) ((1*t)-(R+28*t)+((4*q+-12)-(R+28*t))) (((4*q+-12)-(R+28*t))-(2*t)) ((2*t-1)-(R+28*t)+((4*q+-12)-(R+28*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-12)-(R+28*t))-7*z
  let x : ℤ := (R+28*t)-((4*q+-12)-(R+28*t))+6*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (2*t)≤y ∧ y≤(4*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-2) := ⟨hzL,hzU⟩
  obtain ⟨z0,z1,hz0L,hz0U,hz1L,hz1U,hzsum⟩ := split_two (8*t) (16*t-1) z (by omega) (by rcases hz with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,8,8,x,y,z0,z1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (2*t+1)*x + (4*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hzsum]
        ring

def c2_12 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-7)-(R+32*t))-(4*t)) ∧
  6*(16*t)≤((8*t-2)-(R+32*t)+((2*q+-7)-(R+32*t))) ∧
  (((2*q+-7)-(R+32*t))-(8*t-1))≤7*(32*t-1) ∧
  ((4*t)-(R+32*t)+((2*q+-7)-(R+32*t)))≤6*(32*t-1) ∧
  (((2*q+-7)-(R+32*t))-(8*t-1))+7≤(((2*q+-7)-(R+32*t))-(4*t)) ∧
  6*(((2*q+-7)-(R+32*t))-(8*t-1))+42≤7*((8*t-2)-(R+32*t)+((2*q+-7)-(R+32*t))) ∧
  7*((4*t)-(R+32*t)+((2*q+-7)-(R+32*t)))+42≤6*(((2*q+-7)-(R+32*t))-(4*t)) ∧
  ((4*t)-(R+32*t)+((2*q+-7)-(R+32*t)))+6≤((8*t-2)-(R+32*t)+((2*q+-7)-(R+32*t)))
def c2_12_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_12 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-7)-(R+32*t))-(8*t-1)) ((4*t)-(R+32*t)+((2*q+-7)-(R+32*t))) (((2*q+-7)-(R+32*t))-(4*t)) ((8*t-2)-(R+32*t)+((2*q+-7)-(R+32*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-7)-(R+32*t))-7*z
  let x : ℤ := (R+32*t)-((2*q+-7)-(R+32*t))+6*z
  have hx : (4*t)≤x ∧ x≤(8*t-2) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (2*t) (4*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,2,4,16,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c2_13 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-6)-(R+28*t))-(4*t)) ∧
  6*(16*t)≤((8*t-2)-(R+28*t)+((2*q+-6)-(R+28*t))) ∧
  (((2*q+-6)-(R+28*t))-(8*t-1))≤7*(32*t-1) ∧
  ((4*t)-(R+28*t)+((2*q+-6)-(R+28*t)))≤6*(32*t-1) ∧
  (((2*q+-6)-(R+28*t))-(8*t-1))+7≤(((2*q+-6)-(R+28*t))-(4*t)) ∧
  6*(((2*q+-6)-(R+28*t))-(8*t-1))+42≤7*((8*t-2)-(R+28*t)+((2*q+-6)-(R+28*t))) ∧
  7*((4*t)-(R+28*t)+((2*q+-6)-(R+28*t)))+42≤6*(((2*q+-6)-(R+28*t))-(4*t)) ∧
  ((4*t)-(R+28*t)+((2*q+-6)-(R+28*t)))+6≤((8*t-2)-(R+28*t)+((2*q+-6)-(R+28*t)))
def c2_13_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_13 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-6)-(R+28*t))-(8*t-1)) ((4*t)-(R+28*t)+((2*q+-6)-(R+28*t))) (((2*q+-6)-(R+28*t))-(4*t)) ((8*t-2)-(R+28*t)+((2*q+-6)-(R+28*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-6)-(R+28*t))-7*z
  let x : ℤ := (R+28*t)-((2*q+-6)-(R+28*t))+6*z
  have hx : (4*t)≤x ∧ x≤(8*t-2) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (2*t) (4*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,2,4,16,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c2_14 (t q R : ℤ) : Prop :=
  (8*t)≤(16*t-1) ∧
  3*(8*t)≤(((2*q+-5)-(R+24*t))-(8*t)) ∧
  2*(8*t)≤((4*t-1)-(R+24*t)+((2*q+-5)-(R+24*t))) ∧
  (((2*q+-5)-(R+24*t))-(16*t-2))≤3*(16*t-1) ∧
  ((2*t)-(R+24*t)+((2*q+-5)-(R+24*t)))≤2*(16*t-1) ∧
  (((2*q+-5)-(R+24*t))-(16*t-2))+3≤(((2*q+-5)-(R+24*t))-(8*t)) ∧
  2*(((2*q+-5)-(R+24*t))-(16*t-2))+6≤3*((4*t-1)-(R+24*t)+((2*q+-5)-(R+24*t))) ∧
  3*((2*t)-(R+24*t)+((2*q+-5)-(R+24*t)))+6≤2*(((2*q+-5)-(R+24*t))-(8*t)) ∧
  ((2*t)-(R+24*t)+((2*q+-5)-(R+24*t)))+2≤((4*t-1)-(R+24*t)+((2*q+-5)-(R+24*t)))
def c2_14_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_14 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (8*t) (16*t-1) (((2*q+-5)-(R+24*t))-(16*t-2)) ((2*t)-(R+24*t)+((2*q+-5)-(R+24*t))) (((2*q+-5)-(R+24*t))-(8*t)) ((4*t-1)-(R+24*t)+((2*q+-5)-(R+24*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-5)-(R+24*t))-3*z
  let x : ℤ := (R+24*t)-((2*q+-5)-(R+24*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (8*t)≤z ∧ z≤(16*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,8,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c2_15 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-9)-(R+40*t))-(4*t)) ∧
  6*(16*t)≤((8*t-2)-(R+40*t)+((2*q+-9)-(R+40*t))) ∧
  (((2*q+-9)-(R+40*t))-(8*t-1))≤7*(32*t-1) ∧
  ((4*t)-(R+40*t)+((2*q+-9)-(R+40*t)))≤6*(32*t-1) ∧
  (((2*q+-9)-(R+40*t))-(8*t-1))+7≤(((2*q+-9)-(R+40*t))-(4*t)) ∧
  6*(((2*q+-9)-(R+40*t))-(8*t-1))+42≤7*((8*t-2)-(R+40*t)+((2*q+-9)-(R+40*t))) ∧
  7*((4*t)-(R+40*t)+((2*q+-9)-(R+40*t)))+42≤6*(((2*q+-9)-(R+40*t))-(4*t)) ∧
  ((4*t)-(R+40*t)+((2*q+-9)-(R+40*t)))+6≤((8*t-2)-(R+40*t)+((2*q+-9)-(R+40*t)))
def c2_15_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_15 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-9)-(R+40*t))-(8*t-1)) ((4*t)-(R+40*t)+((2*q+-9)-(R+40*t))) (((2*q+-9)-(R+40*t))-(4*t)) ((8*t-2)-(R+40*t)+((2*q+-9)-(R+40*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-9)-(R+40*t))-7*z
  let x : ℤ := (R+40*t)-((2*q+-9)-(R+40*t))+6*z
  have hx : (4*t)≤x ∧ x≤(8*t-2) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (2*t) (4*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,2,4,16,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c2_16 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  15*(16*t)≤(((4*q+-10)-(R+24*t))-(2*t)) ∧
  14*(16*t)≤((4*t-2)-(R+24*t)+((4*q+-10)-(R+24*t))) ∧
  (((4*q+-10)-(R+24*t))-(4*t-1))≤15*(32*t-1) ∧
  ((2*t)-(R+24*t)+((4*q+-10)-(R+24*t)))≤14*(32*t-1) ∧
  (((4*q+-10)-(R+24*t))-(4*t-1))+15≤(((4*q+-10)-(R+24*t))-(2*t)) ∧
  14*(((4*q+-10)-(R+24*t))-(4*t-1))+210≤15*((4*t-2)-(R+24*t)+((4*q+-10)-(R+24*t))) ∧
  15*((2*t)-(R+24*t)+((4*q+-10)-(R+24*t)))+210≤14*(((4*q+-10)-(R+24*t))-(2*t)) ∧
  ((2*t)-(R+24*t)+((4*q+-10)-(R+24*t)))+14≤((4*t-2)-(R+24*t)+((4*q+-10)-(R+24*t)))
def c2_16_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_16 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((4*q+-10)-(R+24*t))-(4*t-1)) ((2*t)-(R+24*t)+((4*q+-10)-(R+24*t))) (((4*q+-10)-(R+24*t))-(2*t)) ((4*t-2)-(R+24*t)+((4*q+-10)-(R+24*t))) 15 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-10)-(R+24*t))-15*z
  let x : ℤ := (R+24*t)-((4*q+-10)-(R+24*t))+14*z
  have hx : (2*t)≤x ∧ x≤(4*t-2) := by dsimp [x]; omega
  have hy : (2*t)≤y ∧ y≤(4*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (1*t) (2*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,1,2,16,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (2*t+1)*x + (4*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c2_17 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-5)-(R+24*t))-(4*t)) ∧
  6*(16*t)≤((8*t-2)-(R+24*t)+((2*q+-5)-(R+24*t))) ∧
  (((2*q+-5)-(R+24*t))-(8*t-1))≤7*(32*t-1) ∧
  ((4*t)-(R+24*t)+((2*q+-5)-(R+24*t)))≤6*(32*t-1) ∧
  (((2*q+-5)-(R+24*t))-(8*t-1))+7≤(((2*q+-5)-(R+24*t))-(4*t)) ∧
  6*(((2*q+-5)-(R+24*t))-(8*t-1))+42≤7*((8*t-2)-(R+24*t)+((2*q+-5)-(R+24*t))) ∧
  7*((4*t)-(R+24*t)+((2*q+-5)-(R+24*t)))+42≤6*(((2*q+-5)-(R+24*t))-(4*t)) ∧
  ((4*t)-(R+24*t)+((2*q+-5)-(R+24*t)))+6≤((8*t-2)-(R+24*t)+((2*q+-5)-(R+24*t)))
def c2_17_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_17 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-5)-(R+24*t))-(8*t-1)) ((4*t)-(R+24*t)+((2*q+-5)-(R+24*t))) (((2*q+-5)-(R+24*t))-(4*t)) ((8*t-2)-(R+24*t)+((2*q+-5)-(R+24*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-5)-(R+24*t))-7*z
  let x : ℤ := (R+24*t)-((2*q+-5)-(R+24*t))+6*z
  have hx : (4*t)≤x ∧ x≤(8*t-2) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (2*t) (4*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,2,4,16,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c3_0 (t q R : ℤ) : Prop :=
  (8*t)≤(16*t-1) ∧
  3*(8*t)≤(((2*q+-4)-(R+22*t))-(8*t)) ∧
  2*(8*t)≤((4*t-1)-(R+22*t)+((2*q+-4)-(R+22*t))) ∧
  (((2*q+-4)-(R+22*t))-(16*t-2))≤3*(16*t-1) ∧
  ((2*t)-(R+22*t)+((2*q+-4)-(R+22*t)))≤2*(16*t-1) ∧
  (((2*q+-4)-(R+22*t))-(16*t-2))+3≤(((2*q+-4)-(R+22*t))-(8*t)) ∧
  2*(((2*q+-4)-(R+22*t))-(16*t-2))+6≤3*((4*t-1)-(R+22*t)+((2*q+-4)-(R+22*t))) ∧
  3*((2*t)-(R+22*t)+((2*q+-4)-(R+22*t)))+6≤2*(((2*q+-4)-(R+22*t))-(8*t)) ∧
  ((2*t)-(R+22*t)+((2*q+-4)-(R+22*t)))+2≤((4*t-1)-(R+22*t)+((2*q+-4)-(R+22*t)))
def c3_0_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_0 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (8*t) (16*t-1) (((2*q+-4)-(R+22*t))-(16*t-2)) ((2*t)-(R+22*t)+((2*q+-4)-(R+22*t))) (((2*q+-4)-(R+22*t))-(8*t)) ((4*t-1)-(R+22*t)+((2*q+-4)-(R+22*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-4)-(R+22*t))-3*z
  let x : ℤ := (R+22*t)-((2*q+-4)-(R+22*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (8*t)≤z ∧ z≤(16*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,8,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c3_1 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  15*(16*t)≤(((4*q+-12)-(R+30*t))-(4*t)) ∧
  14*(16*t)≤((2*t-1)-(R+30*t)+((4*q+-12)-(R+30*t))) ∧
  (((4*q+-12)-(R+30*t))-(8*t-2))≤15*(32*t-1) ∧
  ((1*t)-(R+30*t)+((4*q+-12)-(R+30*t)))≤14*(32*t-1) ∧
  (((4*q+-12)-(R+30*t))-(8*t-2))+15≤(((4*q+-12)-(R+30*t))-(4*t)) ∧
  14*(((4*q+-12)-(R+30*t))-(8*t-2))+210≤15*((2*t-1)-(R+30*t)+((4*q+-12)-(R+30*t))) ∧
  15*((1*t)-(R+30*t)+((4*q+-12)-(R+30*t)))+210≤14*(((4*q+-12)-(R+30*t))-(4*t)) ∧
  ((1*t)-(R+30*t)+((4*q+-12)-(R+30*t)))+14≤((2*t-1)-(R+30*t)+((4*q+-12)-(R+30*t)))
def c3_1_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_1 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((4*q+-12)-(R+30*t))-(8*t-2)) ((1*t)-(R+30*t)+((4*q+-12)-(R+30*t))) (((4*q+-12)-(R+30*t))-(4*t)) ((2*t-1)-(R+30*t)+((4*q+-12)-(R+30*t))) 15 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-12)-(R+30*t))-15*z
  let x : ℤ := (R+30*t)-((4*q+-12)-(R+30*t))+14*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (2*t) (4*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,2,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (2*t+1)*x + (4*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c3_2 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-2) ∧
  7*(16*t)≤(((4*q+-9)-(R+24*t))-(2*t)) ∧
  6*(16*t)≤((2*t-1)-(R+24*t)+((4*q+-9)-(R+24*t))) ∧
  (((4*q+-9)-(R+24*t))-(4*t-1))≤7*(32*t-2) ∧
  ((1*t)-(R+24*t)+((4*q+-9)-(R+24*t)))≤6*(32*t-2) ∧
  (((4*q+-9)-(R+24*t))-(4*t-1))+7≤(((4*q+-9)-(R+24*t))-(2*t)) ∧
  6*(((4*q+-9)-(R+24*t))-(4*t-1))+42≤7*((2*t-1)-(R+24*t)+((4*q+-9)-(R+24*t))) ∧
  7*((1*t)-(R+24*t)+((4*q+-9)-(R+24*t)))+42≤6*(((4*q+-9)-(R+24*t))-(2*t)) ∧
  ((1*t)-(R+24*t)+((4*q+-9)-(R+24*t)))+6≤((2*t-1)-(R+24*t)+((4*q+-9)-(R+24*t)))
def c3_2_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_2 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-2) (((4*q+-9)-(R+24*t))-(4*t-1)) ((1*t)-(R+24*t)+((4*q+-9)-(R+24*t))) (((4*q+-9)-(R+24*t))-(2*t)) ((2*t-1)-(R+24*t)+((4*q+-9)-(R+24*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-9)-(R+24*t))-7*z
  let x : ℤ := (R+24*t)-((4*q+-9)-(R+24*t))+6*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (2*t)≤y ∧ y≤(4*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-2) := ⟨hzL,hzU⟩
  obtain ⟨z0,z1,hz0L,hz0U,hz1L,hz1U,hzsum⟩ := split_two (8*t) (16*t-1) z (by omega) (by rcases hz with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,8,8,x,y,z0,z1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (2*t+1)*x + (4*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hzsum]
        ring

def c3_3 (t q R : ℤ) : Prop :=
  (8*t)≤(16*t-1) ∧
  3*(8*t)≤(((2*q+-5)-(R+26*t))-(4*t)) ∧
  2*(8*t)≤((8*t-2)-(R+26*t)+((2*q+-5)-(R+26*t))) ∧
  (((2*q+-5)-(R+26*t))-(8*t-1))≤3*(16*t-1) ∧
  ((4*t)-(R+26*t)+((2*q+-5)-(R+26*t)))≤2*(16*t-1) ∧
  (((2*q+-5)-(R+26*t))-(8*t-1))+3≤(((2*q+-5)-(R+26*t))-(4*t)) ∧
  2*(((2*q+-5)-(R+26*t))-(8*t-1))+6≤3*((8*t-2)-(R+26*t)+((2*q+-5)-(R+26*t))) ∧
  3*((4*t)-(R+26*t)+((2*q+-5)-(R+26*t)))+6≤2*(((2*q+-5)-(R+26*t))-(4*t)) ∧
  ((4*t)-(R+26*t)+((2*q+-5)-(R+26*t)))+2≤((8*t-2)-(R+26*t)+((2*q+-5)-(R+26*t)))
def c3_3_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_3 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (8*t) (16*t-1) (((2*q+-5)-(R+26*t))-(8*t-1)) ((4*t)-(R+26*t)+((2*q+-5)-(R+26*t))) (((2*q+-5)-(R+26*t))-(4*t)) ((8*t-2)-(R+26*t)+((2*q+-5)-(R+26*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-5)-(R+26*t))-3*z
  let x : ℤ := (R+26*t)-((2*q+-5)-(R+26*t))+2*z
  have hx : (4*t)≤x ∧ x≤(8*t-2) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (8*t)≤z ∧ z≤(16*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (2*t) (4*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,2,4,8,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c3_4 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  15*(16*t)≤(((4*q+-14)-(R+34*t))-(4*t)) ∧
  14*(16*t)≤((2*t-1)-(R+34*t)+((4*q+-14)-(R+34*t))) ∧
  (((4*q+-14)-(R+34*t))-(8*t-2))≤15*(32*t-1) ∧
  ((1*t)-(R+34*t)+((4*q+-14)-(R+34*t)))≤14*(32*t-1) ∧
  (((4*q+-14)-(R+34*t))-(8*t-2))+15≤(((4*q+-14)-(R+34*t))-(4*t)) ∧
  14*(((4*q+-14)-(R+34*t))-(8*t-2))+210≤15*((2*t-1)-(R+34*t)+((4*q+-14)-(R+34*t))) ∧
  15*((1*t)-(R+34*t)+((4*q+-14)-(R+34*t)))+210≤14*(((4*q+-14)-(R+34*t))-(4*t)) ∧
  ((1*t)-(R+34*t)+((4*q+-14)-(R+34*t)))+14≤((2*t-1)-(R+34*t)+((4*q+-14)-(R+34*t)))
def c3_4_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_4 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((4*q+-14)-(R+34*t))-(8*t-2)) ((1*t)-(R+34*t)+((4*q+-14)-(R+34*t))) (((4*q+-14)-(R+34*t))-(4*t)) ((2*t-1)-(R+34*t)+((4*q+-14)-(R+34*t))) 15 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-14)-(R+34*t))-15*z
  let x : ℤ := (R+34*t)-((4*q+-14)-(R+34*t))+14*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (2*t) (4*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,2,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (2*t+1)*x + (4*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c3_5 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  15*(16*t)≤(((4*q+-15)-(R+36*t))-(4*t)) ∧
  14*(16*t)≤((2*t-1)-(R+36*t)+((4*q+-15)-(R+36*t))) ∧
  (((4*q+-15)-(R+36*t))-(8*t-2))≤15*(32*t-1) ∧
  ((1*t)-(R+36*t)+((4*q+-15)-(R+36*t)))≤14*(32*t-1) ∧
  (((4*q+-15)-(R+36*t))-(8*t-2))+15≤(((4*q+-15)-(R+36*t))-(4*t)) ∧
  14*(((4*q+-15)-(R+36*t))-(8*t-2))+210≤15*((2*t-1)-(R+36*t)+((4*q+-15)-(R+36*t))) ∧
  15*((1*t)-(R+36*t)+((4*q+-15)-(R+36*t)))+210≤14*(((4*q+-15)-(R+36*t))-(4*t)) ∧
  ((1*t)-(R+36*t)+((4*q+-15)-(R+36*t)))+14≤((2*t-1)-(R+36*t)+((4*q+-15)-(R+36*t)))
def c3_5_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_5 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((4*q+-15)-(R+36*t))-(8*t-2)) ((1*t)-(R+36*t)+((4*q+-15)-(R+36*t))) (((4*q+-15)-(R+36*t))-(4*t)) ((2*t-1)-(R+36*t)+((4*q+-15)-(R+36*t))) 15 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-15)-(R+36*t))-15*z
  let x : ℤ := (R+36*t)-((4*q+-15)-(R+36*t))+14*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (2*t) (4*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,2,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (2*t+1)*x + (4*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c3_6 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-2) ∧
  7*(16*t)≤(((4*q+-12)-(R+30*t))-(2*t)) ∧
  6*(16*t)≤((2*t-1)-(R+30*t)+((4*q+-12)-(R+30*t))) ∧
  (((4*q+-12)-(R+30*t))-(4*t-1))≤7*(32*t-2) ∧
  ((1*t)-(R+30*t)+((4*q+-12)-(R+30*t)))≤6*(32*t-2) ∧
  (((4*q+-12)-(R+30*t))-(4*t-1))+7≤(((4*q+-12)-(R+30*t))-(2*t)) ∧
  6*(((4*q+-12)-(R+30*t))-(4*t-1))+42≤7*((2*t-1)-(R+30*t)+((4*q+-12)-(R+30*t))) ∧
  7*((1*t)-(R+30*t)+((4*q+-12)-(R+30*t)))+42≤6*(((4*q+-12)-(R+30*t))-(2*t)) ∧
  ((1*t)-(R+30*t)+((4*q+-12)-(R+30*t)))+6≤((2*t-1)-(R+30*t)+((4*q+-12)-(R+30*t)))
def c3_6_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_6 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-2) (((4*q+-12)-(R+30*t))-(4*t-1)) ((1*t)-(R+30*t)+((4*q+-12)-(R+30*t))) (((4*q+-12)-(R+30*t))-(2*t)) ((2*t-1)-(R+30*t)+((4*q+-12)-(R+30*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-12)-(R+30*t))-7*z
  let x : ℤ := (R+30*t)-((4*q+-12)-(R+30*t))+6*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (2*t)≤y ∧ y≤(4*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-2) := ⟨hzL,hzU⟩
  obtain ⟨z0,z1,hz0L,hz0U,hz1L,hz1U,hzsum⟩ := split_two (8*t) (16*t-1) z (by omega) (by rcases hz with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,8,8,x,y,z0,z1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (2*t+1)*x + (4*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hzsum]
        ring

def c3_7 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-2) ∧
  3*(16*t)≤(((2*q+-5)-(R+26*t))-(4*t)) ∧
  2*(16*t)≤((4*t-1)-(R+26*t)+((2*q+-5)-(R+26*t))) ∧
  (((2*q+-5)-(R+26*t))-(8*t-1))≤3*(32*t-2) ∧
  ((2*t)-(R+26*t)+((2*q+-5)-(R+26*t)))≤2*(32*t-2) ∧
  (((2*q+-5)-(R+26*t))-(8*t-1))+3≤(((2*q+-5)-(R+26*t))-(4*t)) ∧
  2*(((2*q+-5)-(R+26*t))-(8*t-1))+6≤3*((4*t-1)-(R+26*t)+((2*q+-5)-(R+26*t))) ∧
  3*((2*t)-(R+26*t)+((2*q+-5)-(R+26*t)))+6≤2*(((2*q+-5)-(R+26*t))-(4*t)) ∧
  ((2*t)-(R+26*t)+((2*q+-5)-(R+26*t)))+2≤((4*t-1)-(R+26*t)+((2*q+-5)-(R+26*t)))
def c3_7_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_7 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-2) (((2*q+-5)-(R+26*t))-(8*t-1)) ((2*t)-(R+26*t)+((2*q+-5)-(R+26*t))) (((2*q+-5)-(R+26*t))-(4*t)) ((4*t-1)-(R+26*t)+((2*q+-5)-(R+26*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-5)-(R+26*t))-3*z
  let x : ℤ := (R+26*t)-((2*q+-5)-(R+26*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-2) := ⟨hzL,hzU⟩
  obtain ⟨z0,z1,hz0L,hz0U,hz1L,hz1U,hzsum⟩ := split_two (8*t) (16*t-1) z (by omega) (by rcases hz with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,8,8,x,y,z0,z1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hzsum]
        ring

def c3_8 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  15*(16*t)≤(((4*q+-13)-(R+32*t))-(4*t)) ∧
  14*(16*t)≤((2*t-1)-(R+32*t)+((4*q+-13)-(R+32*t))) ∧
  (((4*q+-13)-(R+32*t))-(8*t-2))≤15*(32*t-1) ∧
  ((1*t)-(R+32*t)+((4*q+-13)-(R+32*t)))≤14*(32*t-1) ∧
  (((4*q+-13)-(R+32*t))-(8*t-2))+15≤(((4*q+-13)-(R+32*t))-(4*t)) ∧
  14*(((4*q+-13)-(R+32*t))-(8*t-2))+210≤15*((2*t-1)-(R+32*t)+((4*q+-13)-(R+32*t))) ∧
  15*((1*t)-(R+32*t)+((4*q+-13)-(R+32*t)))+210≤14*(((4*q+-13)-(R+32*t))-(4*t)) ∧
  ((1*t)-(R+32*t)+((4*q+-13)-(R+32*t)))+14≤((2*t-1)-(R+32*t)+((4*q+-13)-(R+32*t)))
def c3_8_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_8 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((4*q+-13)-(R+32*t))-(8*t-2)) ((1*t)-(R+32*t)+((4*q+-13)-(R+32*t))) (((4*q+-13)-(R+32*t))-(4*t)) ((2*t-1)-(R+32*t)+((4*q+-13)-(R+32*t))) 15 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-13)-(R+32*t))-15*z
  let x : ℤ := (R+32*t)-((4*q+-13)-(R+32*t))+14*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (2*t) (4*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,2,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (2*t+1)*x + (4*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c3_9 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-2) ∧
  7*(16*t)≤(((4*q+-13)-(R+32*t))-(2*t)) ∧
  6*(16*t)≤((2*t-1)-(R+32*t)+((4*q+-13)-(R+32*t))) ∧
  (((4*q+-13)-(R+32*t))-(4*t-1))≤7*(32*t-2) ∧
  ((1*t)-(R+32*t)+((4*q+-13)-(R+32*t)))≤6*(32*t-2) ∧
  (((4*q+-13)-(R+32*t))-(4*t-1))+7≤(((4*q+-13)-(R+32*t))-(2*t)) ∧
  6*(((4*q+-13)-(R+32*t))-(4*t-1))+42≤7*((2*t-1)-(R+32*t)+((4*q+-13)-(R+32*t))) ∧
  7*((1*t)-(R+32*t)+((4*q+-13)-(R+32*t)))+42≤6*(((4*q+-13)-(R+32*t))-(2*t)) ∧
  ((1*t)-(R+32*t)+((4*q+-13)-(R+32*t)))+6≤((2*t-1)-(R+32*t)+((4*q+-13)-(R+32*t)))
def c3_9_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_9 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-2) (((4*q+-13)-(R+32*t))-(4*t-1)) ((1*t)-(R+32*t)+((4*q+-13)-(R+32*t))) (((4*q+-13)-(R+32*t))-(2*t)) ((2*t-1)-(R+32*t)+((4*q+-13)-(R+32*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-13)-(R+32*t))-7*z
  let x : ℤ := (R+32*t)-((4*q+-13)-(R+32*t))+6*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (2*t)≤y ∧ y≤(4*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-2) := ⟨hzL,hzU⟩
  obtain ⟨z0,z1,hz0L,hz0U,hz1L,hz1U,hzsum⟩ := split_two (8*t) (16*t-1) z (by omega) (by rcases hz with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,8,8,x,y,z0,z1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (2*t+1)*x + (4*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hzsum]
        ring

def c3_10 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-6)-(R+30*t))-(4*t)) ∧
  6*(16*t)≤((8*t-2)-(R+30*t)+((2*q+-6)-(R+30*t))) ∧
  (((2*q+-6)-(R+30*t))-(8*t-1))≤7*(32*t-1) ∧
  ((4*t)-(R+30*t)+((2*q+-6)-(R+30*t)))≤6*(32*t-1) ∧
  (((2*q+-6)-(R+30*t))-(8*t-1))+7≤(((2*q+-6)-(R+30*t))-(4*t)) ∧
  6*(((2*q+-6)-(R+30*t))-(8*t-1))+42≤7*((8*t-2)-(R+30*t)+((2*q+-6)-(R+30*t))) ∧
  7*((4*t)-(R+30*t)+((2*q+-6)-(R+30*t)))+42≤6*(((2*q+-6)-(R+30*t))-(4*t)) ∧
  ((4*t)-(R+30*t)+((2*q+-6)-(R+30*t)))+6≤((8*t-2)-(R+30*t)+((2*q+-6)-(R+30*t)))
def c3_10_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_10 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-6)-(R+30*t))-(8*t-1)) ((4*t)-(R+30*t)+((2*q+-6)-(R+30*t))) (((2*q+-6)-(R+30*t))-(4*t)) ((8*t-2)-(R+30*t)+((2*q+-6)-(R+30*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-6)-(R+30*t))-7*z
  let x : ℤ := (R+30*t)-((2*q+-6)-(R+30*t))+6*z
  have hx : (4*t)≤x ∧ x≤(8*t-2) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (2*t) (4*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,2,4,16,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c3_11 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-2) ∧
  3*(16*t)≤(((2*q+-7)-(R+34*t))-(4*t)) ∧
  2*(16*t)≤((4*t-1)-(R+34*t)+((2*q+-7)-(R+34*t))) ∧
  (((2*q+-7)-(R+34*t))-(8*t-1))≤3*(32*t-2) ∧
  ((2*t)-(R+34*t)+((2*q+-7)-(R+34*t)))≤2*(32*t-2) ∧
  (((2*q+-7)-(R+34*t))-(8*t-1))+3≤(((2*q+-7)-(R+34*t))-(4*t)) ∧
  2*(((2*q+-7)-(R+34*t))-(8*t-1))+6≤3*((4*t-1)-(R+34*t)+((2*q+-7)-(R+34*t))) ∧
  3*((2*t)-(R+34*t)+((2*q+-7)-(R+34*t)))+6≤2*(((2*q+-7)-(R+34*t))-(4*t)) ∧
  ((2*t)-(R+34*t)+((2*q+-7)-(R+34*t)))+2≤((4*t-1)-(R+34*t)+((2*q+-7)-(R+34*t)))
def c3_11_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_11 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-2) (((2*q+-7)-(R+34*t))-(8*t-1)) ((2*t)-(R+34*t)+((2*q+-7)-(R+34*t))) (((2*q+-7)-(R+34*t))-(4*t)) ((4*t-1)-(R+34*t)+((2*q+-7)-(R+34*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-7)-(R+34*t))-3*z
  let x : ℤ := (R+34*t)-((2*q+-7)-(R+34*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-2) := ⟨hzL,hzU⟩
  obtain ⟨z0,z1,hz0L,hz0U,hz1L,hz1U,hzsum⟩ := split_two (8*t) (16*t-1) z (by omega) (by rcases hz with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,8,8,x,y,z0,z1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hzsum]
        ring

def c3_12 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  15*(16*t)≤(((4*q+-16)-(R+38*t))-(4*t)) ∧
  14*(16*t)≤((2*t-1)-(R+38*t)+((4*q+-16)-(R+38*t))) ∧
  (((4*q+-16)-(R+38*t))-(8*t-2))≤15*(32*t-1) ∧
  ((1*t)-(R+38*t)+((4*q+-16)-(R+38*t)))≤14*(32*t-1) ∧
  (((4*q+-16)-(R+38*t))-(8*t-2))+15≤(((4*q+-16)-(R+38*t))-(4*t)) ∧
  14*(((4*q+-16)-(R+38*t))-(8*t-2))+210≤15*((2*t-1)-(R+38*t)+((4*q+-16)-(R+38*t))) ∧
  15*((1*t)-(R+38*t)+((4*q+-16)-(R+38*t)))+210≤14*(((4*q+-16)-(R+38*t))-(4*t)) ∧
  ((1*t)-(R+38*t)+((4*q+-16)-(R+38*t)))+14≤((2*t-1)-(R+38*t)+((4*q+-16)-(R+38*t)))
def c3_12_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_12 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((4*q+-16)-(R+38*t))-(8*t-2)) ((1*t)-(R+38*t)+((4*q+-16)-(R+38*t))) (((4*q+-16)-(R+38*t))-(4*t)) ((2*t-1)-(R+38*t)+((4*q+-16)-(R+38*t))) 15 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-16)-(R+38*t))-15*z
  let x : ℤ := (R+38*t)-((4*q+-16)-(R+38*t))+14*z
  have hx : (1*t)≤x ∧ x≤(2*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (2*t) (4*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,2,2,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (2*t+1)*x + (4*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c3_13 (t q R : ℤ) : Prop :=
  (8*t)≤((R+30*t)-((1*q+-3)-(R+30*t))) ∧
  ((R+30*t)-((1*q+-3)-(R+30*t)))≤(16*t-2) ∧
  (16*t)≤((1*q+-3)-(R+30*t)) ∧
  ((1*q+-3)-(R+30*t))≤(32*t-2)
def c3_13_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_13 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  let y : ℤ := ((1*q+-3)-(R+30*t))
  let x : ℤ := ((R+30*t)-((1*q+-3)-(R+30*t)))
  have hx : (8*t)≤x ∧ x≤(16*t-2) := ⟨hc.1,hc.2.1⟩
  have hy : (16*t)≤y ∧ y≤(32*t-2) := hc.2.2
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (4*t) (8*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (8*t) (16*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,4,8,8,x0,x1,y0,y1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum,← hysum]
        ring

def c3_14 (t q R : ℤ) : Prop :=
  (8*t)≤(16*t-1) ∧
  3*(8*t)≤(((2*q+-5)-(R+26*t))-(8*t)) ∧
  2*(8*t)≤((4*t-1)-(R+26*t)+((2*q+-5)-(R+26*t))) ∧
  (((2*q+-5)-(R+26*t))-(16*t-2))≤3*(16*t-1) ∧
  ((2*t)-(R+26*t)+((2*q+-5)-(R+26*t)))≤2*(16*t-1) ∧
  (((2*q+-5)-(R+26*t))-(16*t-2))+3≤(((2*q+-5)-(R+26*t))-(8*t)) ∧
  2*(((2*q+-5)-(R+26*t))-(16*t-2))+6≤3*((4*t-1)-(R+26*t)+((2*q+-5)-(R+26*t))) ∧
  3*((2*t)-(R+26*t)+((2*q+-5)-(R+26*t)))+6≤2*(((2*q+-5)-(R+26*t))-(8*t)) ∧
  ((2*t)-(R+26*t)+((2*q+-5)-(R+26*t)))+2≤((4*t-1)-(R+26*t)+((2*q+-5)-(R+26*t)))
def c3_14_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_14 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (8*t) (16*t-1) (((2*q+-5)-(R+26*t))-(16*t-2)) ((2*t)-(R+26*t)+((2*q+-5)-(R+26*t))) (((2*q+-5)-(R+26*t))-(8*t)) ((4*t-1)-(R+26*t)+((2*q+-5)-(R+26*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-5)-(R+26*t))-3*z
  let x : ℤ := (R+26*t)-((2*q+-5)-(R+26*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (8*t)≤z ∧ z≤(16*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,8,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c3_15 (t q R : ℤ) : Prop :=
  (8*t)≤((R+38*t)-((1*q+-4)-(R+38*t))) ∧
  ((R+38*t)-((1*q+-4)-(R+38*t)))≤(16*t-2) ∧
  (16*t)≤((1*q+-4)-(R+38*t)) ∧
  ((1*q+-4)-(R+38*t))≤(32*t-2)
def c3_15_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_15 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  let y : ℤ := ((1*q+-4)-(R+38*t))
  let x : ℤ := ((R+38*t)-((1*q+-4)-(R+38*t)))
  have hx : (8*t)≤x ∧ x≤(16*t-2) := ⟨hc.1,hc.2.1⟩
  have hy : (16*t)≤y ∧ y≤(32*t-2) := hc.2.2
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (4*t) (8*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (8*t) (16*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,4,8,8,x0,x1,y0,y1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum,← hysum]
        ring

def c3_16 (t q R : ℤ) : Prop :=
  (12*t)≤((R+30*t)-((1*q+-3)-(R+30*t))) ∧
  ((R+30*t)-((1*q+-3)-(R+30*t)))≤(24*t-3) ∧
  (8*t)≤((1*q+-3)-(R+30*t)) ∧
  ((1*q+-3)-(R+30*t))≤(16*t-1)
def c3_16_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_16 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  let y : ℤ := ((1*q+-3)-(R+30*t))
  let x : ℤ := ((R+30*t)-((1*q+-3)-(R+30*t)))
  have hx : (12*t)≤x ∧ x≤(24*t-3) := ⟨hc.1,hc.2.1⟩
  have hy : (8*t)≤y ∧ y≤(16*t-1) := hc.2.2
  obtain ⟨x0,x1,x2,hx0L,hx0U,hx1L,hx1U,hx2L,hx2U,hxsum⟩ := split_three (4*t) (8*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,4,4,8,x0,x1,x2,y, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c3_17 (t q R : ℤ) : Prop :=
  (4*t)≤((R+38*t)-((1*q+-4)-(R+38*t))) ∧
  ((R+38*t)-((1*q+-4)-(R+38*t)))≤(8*t-1) ∧
  (24*t)≤((1*q+-4)-(R+38*t)) ∧
  ((1*q+-4)-(R+38*t))≤(48*t-3)
def c3_17_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_17 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  let y : ℤ := ((1*q+-4)-(R+38*t))
  let x : ℤ := ((R+38*t)-((1*q+-4)-(R+38*t)))
  have hx : (4*t)≤x ∧ x≤(8*t-1) := ⟨hc.1,hc.2.1⟩
  have hy : (24*t)≤y ∧ y≤(48*t-3) := hc.2.2
  obtain ⟨y0,y1,y2,hy0L,hy0U,hy1L,hy1U,hy2L,hy2U,hysum⟩ := split_three (8*t) (16*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,8,8,8,x,y0,y1,y2, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c3_18 (t q R : ℤ) : Prop :=
  (12*t)≤((R+22*t)-((1*q+-2)-(R+22*t))) ∧
  ((R+22*t)-((1*q+-2)-(R+22*t)))≤(24*t-3) ∧
  (8*t)≤((1*q+-2)-(R+22*t)) ∧
  ((1*q+-2)-(R+22*t))≤(16*t-1)
def c3_18_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_18 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  let y : ℤ := ((1*q+-2)-(R+22*t))
  let x : ℤ := ((R+22*t)-((1*q+-2)-(R+22*t)))
  have hx : (12*t)≤x ∧ x≤(24*t-3) := ⟨hc.1,hc.2.1⟩
  have hy : (8*t)≤y ∧ y≤(16*t-1) := hc.2.2
  obtain ⟨x0,x1,x2,hx0L,hx0U,hx1L,hx1U,hx2L,hx2U,hxsum⟩ := split_three (4*t) (8*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,4,4,8,x0,x1,x2,y, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c3_19 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-5)-(R+26*t))-(4*t)) ∧
  6*(16*t)≤((8*t-2)-(R+26*t)+((2*q+-5)-(R+26*t))) ∧
  (((2*q+-5)-(R+26*t))-(8*t-1))≤7*(32*t-1) ∧
  ((4*t)-(R+26*t)+((2*q+-5)-(R+26*t)))≤6*(32*t-1) ∧
  (((2*q+-5)-(R+26*t))-(8*t-1))+7≤(((2*q+-5)-(R+26*t))-(4*t)) ∧
  6*(((2*q+-5)-(R+26*t))-(8*t-1))+42≤7*((8*t-2)-(R+26*t)+((2*q+-5)-(R+26*t))) ∧
  7*((4*t)-(R+26*t)+((2*q+-5)-(R+26*t)))+42≤6*(((2*q+-5)-(R+26*t))-(4*t)) ∧
  ((4*t)-(R+26*t)+((2*q+-5)-(R+26*t)))+6≤((8*t-2)-(R+26*t)+((2*q+-5)-(R+26*t)))
def c3_19_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_19 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-5)-(R+26*t))-(8*t-1)) ((4*t)-(R+26*t)+((2*q+-5)-(R+26*t))) (((2*q+-5)-(R+26*t))-(4*t)) ((8*t-2)-(R+26*t)+((2*q+-5)-(R+26*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-5)-(R+26*t))-7*z
  let x : ℤ := (R+26*t)-((2*q+-5)-(R+26*t))+6*z
  have hx : (4*t)≤x ∧ x≤(8*t-2) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (2*t) (4*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,2,4,16,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c3_20 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  15*(16*t)≤(((4*q+-8)-(R+22*t))-(2*t)) ∧
  14*(16*t)≤((4*t-2)-(R+22*t)+((4*q+-8)-(R+22*t))) ∧
  (((4*q+-8)-(R+22*t))-(4*t-1))≤15*(32*t-1) ∧
  ((2*t)-(R+22*t)+((4*q+-8)-(R+22*t)))≤14*(32*t-1) ∧
  (((4*q+-8)-(R+22*t))-(4*t-1))+15≤(((4*q+-8)-(R+22*t))-(2*t)) ∧
  14*(((4*q+-8)-(R+22*t))-(4*t-1))+210≤15*((4*t-2)-(R+22*t)+((4*q+-8)-(R+22*t))) ∧
  15*((2*t)-(R+22*t)+((4*q+-8)-(R+22*t)))+210≤14*(((4*q+-8)-(R+22*t))-(2*t)) ∧
  ((2*t)-(R+22*t)+((4*q+-8)-(R+22*t)))+14≤((4*t-2)-(R+22*t)+((4*q+-8)-(R+22*t)))
def c3_20_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_20 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((4*q+-8)-(R+22*t))-(4*t-1)) ((2*t)-(R+22*t)+((4*q+-8)-(R+22*t))) (((4*q+-8)-(R+22*t))-(2*t)) ((4*t-2)-(R+22*t)+((4*q+-8)-(R+22*t))) 15 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((4*q+-8)-(R+22*t))-15*z
  let x : ℤ := (R+22*t)-((4*q+-8)-(R+22*t))+14*z
  have hx : (2*t)≤x ∧ x≤(4*t-2) := by dsimp [x]; omega
  have hy : (2*t)≤y ∧ y≤(4*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (1*t) (2*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨1,1,2,16,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (2*t+1)*x + (4*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

end A343268Proof

-- Component: A343268Cover

namespace A343268Proof
def sector0 (t q R : ℤ) (ht : 16≤t) (hqL : 32*t≤q) (hqU : q<44*t) (hql : 128*t≤4*q+0) (hqu : 4*q+0<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+0)+R) := by
  have hc : c0_8 t q R ∨ c0_9 t q R ∨ c0_10 t q R ∨ c0_14 t q R := by
    unfold c0_8 c0_9 c0_10 c0_14
    omega
  rcases hc with h8 | h9 | h10 | h14
  · exact c0_8_sound t q R (by omega) h8
  · exact c0_9_sound t q R (by omega) h9
  · exact c0_10_sound t q R (by omega) h10
  · exact c0_14_sound t q R (by omega) h14

def sector1 (t q R : ℤ) (ht : 16≤t) (hqL : 44*t≤q) (hqU : q<56*t) (hql : 128*t≤4*q+0) (hqu : 4*q+0<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+0)+R) := by
  have hc : c0_4 t q R ∨ c0_12 t q R ∨ c0_16 t q R := by
    unfold c0_4 c0_12 c0_16
    omega
  rcases hc with h4 | h12 | h16
  · exact c0_4_sound t q R (by omega) h4
  · exact c0_12_sound t q R (by omega) h12
  · exact c0_16_sound t q R (by omega) h16

def sector2 (t q R : ℤ) (ht : 16≤t) (hqL : 56*t≤q) (hqU : q<68*t) (hql : 128*t≤4*q+0) (hqu : 4*q+0<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+0)+R) := by
  have hc : c0_13 t q R ∨ c0_16 t q R ∨ c0_17 t q R ∨ c0_18 t q R := by
    unfold c0_13 c0_16 c0_17 c0_18
    omega
  rcases hc with h13 | h16 | h17 | h18
  · exact c0_13_sound t q R (by omega) h13
  · exact c0_16_sound t q R (by omega) h16
  · exact c0_17_sound t q R (by omega) h17
  · exact c0_18_sound t q R (by omega) h18

def sector3 (t q R : ℤ) (ht : 16≤t) (hqL : 68*t≤q) (hqU : q<80*t) (hql : 128*t≤4*q+0) (hqu : 4*q+0<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+0)+R) := by
  have hc : c0_1 t q R ∨ c0_6 t q R ∨ c0_13 t q R ∨ c0_17 t q R := by
    unfold c0_1 c0_6 c0_13 c0_17
    omega
  rcases hc with h1 | h6 | h13 | h17
  · exact c0_1_sound t q R (by omega) h1
  · exact c0_6_sound t q R (by omega) h6
  · exact c0_13_sound t q R (by omega) h13
  · exact c0_17_sound t q R (by omega) h17

def sector4 (t q R : ℤ) (ht : 16≤t) (hqL : 80*t≤q) (hqU : q<128*t) (hql : 128*t≤4*q+0) (hqu : 4*q+0<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+0)+R) := by
  have hc : c0_6 t q R ∨ c0_7 t q R ∨ c0_11 t q R := by
    unfold c0_6 c0_7 c0_11
    omega
  rcases hc with h6 | h7 | h11
  · exact c0_6_sound t q R (by omega) h6
  · exact c0_7_sound t q R (by omega) h7
  · exact c0_11_sound t q R (by omega) h11

def sector5 (t q R : ℤ) (ht : 16≤t) (hqL : 32*t≤q) (hqU : q<44*t) (hql : 128*t≤4*q+1) (hqu : 4*q+1<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+1)+R) := by
  have hc : c1_4 t q R ∨ c1_14 t q R ∨ c1_16 t q R := by
    unfold c1_4 c1_14 c1_16
    omega
  rcases hc with h4 | h14 | h16
  · exact c1_4_sound t q R (by omega) h4
  · exact c1_14_sound t q R (by omega) h14
  · exact c1_16_sound t q R (by omega) h16

def sector6 (t q R : ℤ) (ht : 16≤t) (hqL : 44*t≤q) (hqU : q<56*t) (hql : 128*t≤4*q+1) (hqu : 4*q+1<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+1)+R) := by
  have hc : c1_19 t q R ∨ c1_14 t q R ∨ c1_13 t q R ∨ c1_9 t q R := by
    unfold c1_19 c1_14 c1_13 c1_9
    omega
  rcases hc with h19 | h14 | h13 | h9
  · exact c1_19_sound t q R (by omega) h19
  · exact c1_14_sound t q R (by omega) h14
  · exact c1_13_sound t q R (by omega) h13
  · exact c1_9_sound t q R (by omega) h9

def sector7 (t q R : ℤ) (ht : 16≤t) (hqL : 56*t≤q) (hqU : q<68*t) (hql : 128*t≤4*q+1) (hqu : 4*q+1<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+1)+R) := by
  have hc : c1_5 t q R ∨ c1_19 t q R ∨ c1_12 t q R ∨ c1_13 t q R := by
    unfold c1_5 c1_19 c1_12 c1_13
    omega
  rcases hc with h5 | h19 | h12 | h13
  · exact c1_5_sound t q R (by omega) h5
  · exact c1_19_sound t q R (by omega) h19
  · exact c1_12_sound t q R (by omega) h12
  · exact c1_13_sound t q R (by omega) h13

def sector8 (t q R : ℤ) (ht : 16≤t) (hqL : 68*t≤q) (hqU : q<80*t) (hql : 128*t≤4*q+1) (hqu : 4*q+1<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+1)+R) := by
  have hc : c1_0 t q R ∨ c1_1 t q R ∨ c1_2 t q R := by
    unfold c1_0 c1_1 c1_2
    omega
  rcases hc with h0 | h1 | h2
  · exact c1_0_sound t q R (by omega) h0
  · exact c1_1_sound t q R (by omega) h1
  · exact c1_2_sound t q R (by omega) h2

def sector9 (t q R : ℤ) (ht : 16≤t) (hqL : 80*t≤q) (hqU : q<128*t) (hql : 128*t≤4*q+1) (hqu : 4*q+1<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+1)+R) := by
  have hc : c1_0 t q R ∨ c1_1 t q R ∨ c1_15 t q R ∨ c1_7 t q R := by
    unfold c1_0 c1_1 c1_15 c1_7
    omega
  rcases hc with h0 | h1 | h15 | h7
  · exact c1_0_sound t q R (by omega) h0
  · exact c1_1_sound t q R (by omega) h1
  · exact c1_15_sound t q R (by omega) h15
  · exact c1_7_sound t q R (by omega) h7

def sector10 (t q R : ℤ) (ht : 16≤t) (hqL : 32*t≤q) (hqU : q<44*t) (hql : 128*t≤4*q+2) (hqu : 4*q+2<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+2)+R) := by
  have hc : c2_7 t q R ∨ c2_2 t q R ∨ c2_8 t q R := by
    unfold c2_7 c2_2 c2_8
    omega
  rcases hc with h7 | h2 | h8
  · exact c2_7_sound t q R (by omega) h7
  · exact c2_2_sound t q R (by omega) h2
  · exact c2_8_sound t q R (by omega) h8

def sector11 (t q R : ℤ) (ht : 16≤t) (hqL : 44*t≤q) (hqU : q<56*t) (hql : 128*t≤4*q+2) (hqu : 4*q+2<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+2)+R) := by
  have hc : c2_2 t q R ∨ c2_11 t q R ∨ c2_4 t q R ∨ c2_1 t q R := by
    unfold c2_2 c2_11 c2_4 c2_1
    omega
  rcases hc with h2 | h11 | h4 | h1
  · exact c2_2_sound t q R (by omega) h2
  · exact c2_11_sound t q R (by omega) h11
  · exact c2_4_sound t q R (by omega) h4
  · exact c2_1_sound t q R (by omega) h1

def sector12 (t q R : ℤ) (ht : 16≤t) (hqL : 56*t≤q) (hqU : q<68*t) (hql : 128*t≤4*q+2) (hqu : 4*q+2<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+2)+R) := by
  have hc : c2_0 t q R ∨ c2_1 t q R ∨ c2_3 t q R := by
    unfold c2_0 c2_1 c2_3
    omega
  rcases hc with h0 | h1 | h3
  · exact c2_0_sound t q R (by omega) h0
  · exact c2_1_sound t q R (by omega) h1
  · exact c2_3_sound t q R (by omega) h3

def sector13 (t q R : ℤ) (ht : 16≤t) (hqL : 68*t≤q) (hqU : q<74*t) (hql : 128*t≤4*q+2) (hqu : 4*q+2<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+2)+R) := by
  have hc : c2_17 t q R ∨ c2_0 t q R ∨ c2_10 t q R ∨ c2_3 t q R := by
    unfold c2_17 c2_0 c2_10 c2_3
    omega
  rcases hc with h17 | h0 | h10 | h3
  · exact c2_17_sound t q R (by omega) h17
  · exact c2_0_sound t q R (by omega) h0
  · exact c2_10_sound t q R (by omega) h10
  · exact c2_3_sound t q R (by omega) h3

def sector14 (t q R : ℤ) (ht : 16≤t) (hqL : 74*t≤q) (hqU : q<80*t) (hql : 128*t≤4*q+2) (hqu : 4*q+2<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+2)+R) := by
  have hc : c2_13 t q R ∨ c2_10 t q R := by
    unfold c2_13 c2_10
    omega
  rcases hc with h13 | h10
  · exact c2_13_sound t q R (by omega) h13
  · exact c2_10_sound t q R (by omega) h10

def sector15 (t q R : ℤ) (ht : 16≤t) (hqL : 80*t≤q) (hqU : q<128*t) (hql : 128*t≤4*q+2) (hqu : 4*q+2<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+2)+R) := by
  have hc : c2_13 t q R ∨ c2_15 t q R ∨ c2_12 t q R ∨ c2_9 t q R := by
    unfold c2_13 c2_15 c2_12 c2_9
    omega
  rcases hc with h13 | h15 | h12 | h9
  · exact c2_13_sound t q R (by omega) h13
  · exact c2_15_sound t q R (by omega) h15
  · exact c2_12_sound t q R (by omega) h12
  · exact c2_9_sound t q R (by omega) h9

def sector16 (t q R : ℤ) (ht : 16≤t) (hqL : 32*t≤q) (hqU : q<44*t) (hql : 128*t≤4*q+3) (hqu : 4*q+3<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+3)+R) := by
  have hc : c3_14 t q R ∨ c3_16 t q R ∨ c3_0 t q R := by
    unfold c3_14 c3_16 c3_0
    omega
  rcases hc with h14 | h16 | h0
  · exact c3_14_sound t q R (by omega) h14
  · exact c3_16_sound t q R (by omega) h16
  · exact c3_0_sound t q R (by omega) h0

def sector17 (t q R : ℤ) (ht : 16≤t) (hqL : 44*t≤q) (hqU : q<50*t) (hql : 128*t≤4*q+3) (hqu : 4*q+3<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+3)+R) := by
  have hc : c3_7 t q R ∨ c3_13 t q R ∨ c3_16 t q R := by
    unfold c3_7 c3_13 c3_16
    omega
  rcases hc with h7 | h13 | h16
  · exact c3_7_sound t q R (by omega) h7
  · exact c3_13_sound t q R (by omega) h13
  · exact c3_16_sound t q R (by omega) h16

def sector18 (t q R : ℤ) (ht : 16≤t) (hqL : 50*t≤q) (hqU : q<56*t) (hql : 128*t≤4*q+3) (hqu : 4*q+3<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+3)+R) := by
  have hc : c3_13 t q R ∨ c3_6 t q R ∨ c3_11 t q R := by
    unfold c3_13 c3_6 c3_11
    omega
  rcases hc with h13 | h6 | h11
  · exact c3_13_sound t q R (by omega) h13
  · exact c3_6_sound t q R (by omega) h6
  · exact c3_11_sound t q R (by omega) h11

def sector19 (t q R : ℤ) (ht : 16≤t) (hqL : 56*t≤q) (hqU : q<68*t) (hql : 128*t≤4*q+3) (hqu : 4*q+3<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+3)+R) := by
  have hc : c3_6 t q R ∨ c3_15 t q R ∨ c3_11 t q R := by
    unfold c3_6 c3_15 c3_11
    omega
  rcases hc with h6 | h15 | h11
  · exact c3_6_sound t q R (by omega) h6
  · exact c3_15_sound t q R (by omega) h15
  · exact c3_11_sound t q R (by omega) h11

def sector20 (t q R : ℤ) (ht : 16≤t) (hqL : 68*t≤q) (hqU : q<74*t) (hql : 128*t≤4*q+3) (hqu : 4*q+3<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+3)+R) := by
  have hc : c3_19 t q R ∨ c3_15 t q R ∨ c3_20 t q R ∨ c3_17 t q R := by
    unfold c3_19 c3_15 c3_20 c3_17
    omega
  rcases hc with h19 | h15 | h20 | h17
  · exact c3_19_sound t q R (by omega) h19
  · exact c3_15_sound t q R (by omega) h15
  · exact c3_20_sound t q R (by omega) h20
  · exact c3_17_sound t q R (by omega) h17

def sector21 (t q R : ℤ) (ht : 16≤t) (hqL : 74*t≤q) (hqU : q<80*t) (hql : 128*t≤4*q+3) (hqu : 4*q+3<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+3)+R) := by
  have hc : c3_19 t q R ∨ c3_10 t q R := by
    unfold c3_19 c3_10
    omega
  rcases hc with h19 | h10
  · exact c3_19_sound t q R (by omega) h19
  · exact c3_10_sound t q R (by omega) h10

def sector22 (t q R : ℤ) (ht : 16≤t) (hqL : 80*t≤q) (hqU : q<104*t) (hql : 128*t≤4*q+3) (hqu : 4*q+3<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+3)+R) := by
  have hc : c3_8 t q R ∨ c3_10 t q R ∨ c3_1 t q R := by
    unfold c3_8 c3_10 c3_1
    omega
  rcases hc with h8 | h10 | h1
  · exact c3_8_sound t q R (by omega) h8
  · exact c3_10_sound t q R (by omega) h10
  · exact c3_1_sound t q R (by omega) h1

def sector23 (t q R : ℤ) (ht : 16≤t) (hqL : 104*t≤q) (hqU : q<116*t) (hql : 128*t≤4*q+3) (hqu : 4*q+3<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+3)+R) := by
  have hc : c3_5 t q R ∨ c3_8 t q R ∨ c3_4 t q R ∨ c3_1 t q R := by
    unfold c3_5 c3_8 c3_4 c3_1
    omega
  rcases hc with h5 | h8 | h4 | h1
  · exact c3_5_sound t q R (by omega) h5
  · exact c3_8_sound t q R (by omega) h8
  · exact c3_4_sound t q R (by omega) h4
  · exact c3_1_sound t q R (by omega) h1

def sector24 (t q R : ℤ) (ht : 16≤t) (hqL : 116*t≤q) (hqU : q<128*t) (hql : 128*t≤4*q+3) (hqu : 4*q+3<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+3)+R) := by
  have hc : c3_5 t q R ∨ c3_4 t q R ∨ c3_12 t q R := by
    unfold c3_5 c3_4 c3_12
    omega
  rcases hc with h5 | h4 | h12
  · exact c3_5_sound t q R (by omega) h5
  · exact c3_4_sound t q R (by omega) h4
  · exact c3_12_sound t q R (by omega) h12

def cover0 (t q R : ℤ) (ht : 16≤t) (hql : 128*t≤4*q+0) (hqu : 4*q+0<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+0)+R) := by
  by_cases h0 : q<44*t
  · exact sector0 t q R ht (by omega) h0 hql hqu hrl hru
  by_cases h1 : q<56*t
  · exact sector1 t q R ht (by omega) h1 hql hqu hrl hru
  by_cases h2 : q<68*t
  · exact sector2 t q R ht (by omega) h2 hql hqu hrl hru
  by_cases h3 : q<80*t
  · exact sector3 t q R ht (by omega) h3 hql hqu hrl hru
  exact sector4 t q R ht (by omega) (by omega) hql hqu hrl hru

def cover1 (t q R : ℤ) (ht : 16≤t) (hql : 128*t≤4*q+1) (hqu : 4*q+1<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+1)+R) := by
  by_cases h5 : q<44*t
  · exact sector5 t q R ht (by omega) h5 hql hqu hrl hru
  by_cases h6 : q<56*t
  · exact sector6 t q R ht (by omega) h6 hql hqu hrl hru
  by_cases h7 : q<68*t
  · exact sector7 t q R ht (by omega) h7 hql hqu hrl hru
  by_cases h8 : q<80*t
  · exact sector8 t q R ht (by omega) h8 hql hqu hrl hru
  exact sector9 t q R ht (by omega) (by omega) hql hqu hrl hru

def cover2 (t q R : ℤ) (ht : 16≤t) (hql : 128*t≤4*q+2) (hqu : 4*q+2<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+2)+R) := by
  by_cases h10 : q<44*t
  · exact sector10 t q R ht (by omega) h10 hql hqu hrl hru
  by_cases h11 : q<56*t
  · exact sector11 t q R ht (by omega) h11 hql hqu hrl hru
  by_cases h12 : q<68*t
  · exact sector12 t q R ht (by omega) h12 hql hqu hrl hru
  by_cases h13 : q<74*t
  · exact sector13 t q R ht (by omega) h13 hql hqu hrl hru
  by_cases h14 : q<80*t
  · exact sector14 t q R ht (by omega) h14 hql hqu hrl hru
  exact sector15 t q R ht (by omega) (by omega) hql hqu hrl hru

def cover3 (t q R : ℤ) (ht : 16≤t) (hql : 128*t≤4*q+3) (hqu : 4*q+3<512*t) (hrl : 0≤R) (hru : R<2*t) :
    Four t (2*t*(4*q+3)+R) := by
  by_cases h16 : q<44*t
  · exact sector16 t q R ht (by omega) h16 hql hqu hrl hru
  by_cases h17 : q<50*t
  · exact sector17 t q R ht (by omega) h17 hql hqu hrl hru
  by_cases h18 : q<56*t
  · exact sector18 t q R ht (by omega) h18 hql hqu hrl hru
  by_cases h19 : q<68*t
  · exact sector19 t q R ht (by omega) h19 hql hqu hrl hru
  by_cases h20 : q<74*t
  · exact sector20 t q R ht (by omega) h20 hql hqu hrl hru
  by_cases h21 : q<80*t
  · exact sector21 t q R ht (by omega) h21 hql hqu hrl hru
  by_cases h22 : q<104*t
  · exact sector22 t q R ht (by omega) h22 hql hqu hrl hru
  by_cases h23 : q<116*t
  · exact sector23 t q R ht (by omega) h23 hql hqu hrl hru
  exact sector24 t q R ht (by omega) (by omega) hql hqu hrl hru

end A343268Proof

-- Component: A343268Large

namespace A343268Proof

def cover_all (t Q R : ℤ) (ht : 16≤t) (hql : 128*t≤Q) (hqu : Q<512*t)
    (hrl : 0≤R) (hru : R<2*t) : Four t (2*t*Q+R) := by
  have hmod0 := Int.emod_nonneg Q (by norm_num : (4:ℤ) ≠ 0)
  have hmod4 := Int.emod_lt_of_pos Q (by norm_num : (0:ℤ)<4)
  have heq := Int.ediv_mul_add_emod Q 4
  have hs : Q%4=0 ∨ Q%4=1 ∨ Q%4=2 ∨ Q%4=3 := by omega
  rcases hs with h|h|h|h
  · have hQ : Q=4*(Q/4)+0 := by omega
    rw [hQ]
    exact cover0 t (Q/4) R ht (by omega) (by omega) hrl hru
  · have hQ : Q=4*(Q/4)+1 := by omega
    rw [hQ]
    exact cover1 t (Q/4) R ht (by omega) (by omega) hrl hru
  · have hQ : Q=4*(Q/4)+2 := by omega
    rw [hQ]
    exact cover2 t (Q/4) R ht (by omega) (by omega) hrl hru
  · have hQ : Q=4*(Q/4)+3 := by omega
    rw [hQ]
    exact cover3 t (Q/4) R ht (by omega) (by omega) hrl hru

def power_four (k : ℕ) : (4:ℤ)^k=((2:ℤ)^k)^2 := by
  rw [show (4:ℤ)=(2:ℤ)^2 by norm_num, ← pow_mul, Nat.mul_comm 2 k, pow_mul]

def represent_large (n : ℕ) (hn : 65536≤n) : Representable n := by
  have hn0 : n ≠ 0 := by omega
  have hlog : 8≤Nat.log 4 n := Nat.le_log_of_pow_le (by norm_num) (by norm_num; exact hn)
  let k := Nat.log 4 n-4
  have hk : 4≤k := by dsimp [k]; omega
  have hlogeq : Nat.log 4 n=k+4 := by dsimp [k]; omega
  let t : ℤ := (2:ℤ)^k
  have ht : 16≤t := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hk
    norm_num at h
    exact h
  have htpos : 0<2*t := by omega
  have hlo := Nat.pow_log_le_self 4 hn0
  have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1<4) n
  rw [hlogeq] at hlo hhi
  have hlow : 256*t^2≤(n:ℤ) := by
    have h : (4:ℤ)^(k+4)≤(n:ℤ) := by exact_mod_cast hlo
    simp only [pow_add,power_four] at h
    norm_num at h
    dsimp [t]
    nlinarith [h]
  have hhigh : (n:ℤ)<1024*t^2 := by
    have h : (n:ℤ)<(4:ℤ)^((k+4)+1) := by exact_mod_cast hhi
    simp only [pow_add,power_four] at h
    norm_num at h
    dsimp [t]
    nlinarith [h]
  let Q : ℤ := (n:ℤ)/(2*t)
  let R : ℤ := (n:ℤ)%(2*t)
  have hQL : 128*t≤Q := by
    dsimp [Q]
    apply (Int.le_ediv_iff_mul_le htpos).2
    nlinarith [hlow]
  have hQU : Q<512*t := by
    dsimp [Q]
    apply (Int.ediv_lt_iff_lt_mul htpos).2
    nlinarith [hhigh]
  have hRL : 0≤R := Int.emod_nonneg _ (by omega)
  have hRU : R<2*t := Int.emod_lt_of_pos _ htpos
  have heq : 2*t*Q+R=(n:ℤ) := by
    dsimp [Q,R]
    nlinarith [Int.ediv_mul_add_emod (n:ℤ) (2*t)]
  have hf := cover_all t Q R ht hQL hQU hRL hRU
  rw [heq] at hf
  simpa using four_is_representable k (n:ℤ) hf

end A343268Proof

-- Component: A343268ExtraCases

namespace A343268Proof

def c0_19 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-8)-(R+32*t))-(8*t)) ∧
  6*(16*t)≤((4*t-1)-(R+32*t)+((2*q+-8)-(R+32*t))) ∧
  (((2*q+-8)-(R+32*t))-(16*t-2))≤7*(32*t-1) ∧
  ((2*t)-(R+32*t)+((2*q+-8)-(R+32*t)))≤6*(32*t-1) ∧
  (((2*q+-8)-(R+32*t))-(16*t-2))+7≤(((2*q+-8)-(R+32*t))-(8*t)) ∧
  6*(((2*q+-8)-(R+32*t))-(16*t-2))+42≤7*((4*t-1)-(R+32*t)+((2*q+-8)-(R+32*t))) ∧
  7*((2*t)-(R+32*t)+((2*q+-8)-(R+32*t)))+42≤6*(((2*q+-8)-(R+32*t))-(8*t)) ∧
  ((2*t)-(R+32*t)+((2*q+-8)-(R+32*t)))+6≤((4*t-1)-(R+32*t)+((2*q+-8)-(R+32*t)))
def c0_19_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_19 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-8)-(R+32*t))-(16*t-2)) ((2*t)-(R+32*t)+((2*q+-8)-(R+32*t))) (((2*q+-8)-(R+32*t))-(8*t)) ((4*t-1)-(R+32*t)+((2*q+-8)-(R+32*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-8)-(R+32*t))-7*z
  let x : ℤ := (R+32*t)-((2*q+-8)-(R+32*t))+6*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c0_20 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-10)-(R+40*t))-(8*t)) ∧
  6*(16*t)≤((4*t-1)-(R+40*t)+((2*q+-10)-(R+40*t))) ∧
  (((2*q+-10)-(R+40*t))-(16*t-2))≤7*(32*t-1) ∧
  ((2*t)-(R+40*t)+((2*q+-10)-(R+40*t)))≤6*(32*t-1) ∧
  (((2*q+-10)-(R+40*t))-(16*t-2))+7≤(((2*q+-10)-(R+40*t))-(8*t)) ∧
  6*(((2*q+-10)-(R+40*t))-(16*t-2))+42≤7*((4*t-1)-(R+40*t)+((2*q+-10)-(R+40*t))) ∧
  7*((2*t)-(R+40*t)+((2*q+-10)-(R+40*t)))+42≤6*(((2*q+-10)-(R+40*t))-(8*t)) ∧
  ((2*t)-(R+40*t)+((2*q+-10)-(R+40*t)))+6≤((4*t-1)-(R+40*t)+((2*q+-10)-(R+40*t)))
def c0_20_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_20 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-10)-(R+40*t))-(16*t-2)) ((2*t)-(R+40*t)+((2*q+-10)-(R+40*t))) (((2*q+-10)-(R+40*t))-(8*t)) ((4*t-1)-(R+40*t)+((2*q+-10)-(R+40*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-10)-(R+40*t))-7*z
  let x : ℤ := (R+40*t)-((2*q+-10)-(R+40*t))+6*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c0_21 (t q R : ℤ) : Prop :=
  (8*t)≤(16*t-1) ∧
  3*(8*t)≤(((2*q+-5)-(R+20*t))-(4*t)) ∧
  2*(8*t)≤((8*t-2)-(R+20*t)+((2*q+-5)-(R+20*t))) ∧
  (((2*q+-5)-(R+20*t))-(8*t-1))≤3*(16*t-1) ∧
  ((4*t)-(R+20*t)+((2*q+-5)-(R+20*t)))≤2*(16*t-1) ∧
  (((2*q+-5)-(R+20*t))-(8*t-1))+3≤(((2*q+-5)-(R+20*t))-(4*t)) ∧
  2*(((2*q+-5)-(R+20*t))-(8*t-1))+6≤3*((8*t-2)-(R+20*t)+((2*q+-5)-(R+20*t))) ∧
  3*((4*t)-(R+20*t)+((2*q+-5)-(R+20*t)))+6≤2*(((2*q+-5)-(R+20*t))-(4*t)) ∧
  ((4*t)-(R+20*t)+((2*q+-5)-(R+20*t)))+2≤((8*t-2)-(R+20*t)+((2*q+-5)-(R+20*t)))
def c0_21_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_21 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (8*t) (16*t-1) (((2*q+-5)-(R+20*t))-(8*t-1)) ((4*t)-(R+20*t)+((2*q+-5)-(R+20*t))) (((2*q+-5)-(R+20*t))-(4*t)) ((8*t-2)-(R+20*t)+((2*q+-5)-(R+20*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-5)-(R+20*t))-3*z
  let x : ℤ := (R+20*t)-((2*q+-5)-(R+20*t))+2*z
  have hx : (4*t)≤x ∧ x≤(8*t-2) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (8*t)≤z ∧ z≤(16*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (2*t) (4*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,2,4,8,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c0_22 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-6)-(R+24*t))-(4*t)) ∧
  6*(16*t)≤((8*t-2)-(R+24*t)+((2*q+-6)-(R+24*t))) ∧
  (((2*q+-6)-(R+24*t))-(8*t-1))≤7*(32*t-1) ∧
  ((4*t)-(R+24*t)+((2*q+-6)-(R+24*t)))≤6*(32*t-1) ∧
  (((2*q+-6)-(R+24*t))-(8*t-1))+7≤(((2*q+-6)-(R+24*t))-(4*t)) ∧
  6*(((2*q+-6)-(R+24*t))-(8*t-1))+42≤7*((8*t-2)-(R+24*t)+((2*q+-6)-(R+24*t))) ∧
  7*((4*t)-(R+24*t)+((2*q+-6)-(R+24*t)))+42≤6*(((2*q+-6)-(R+24*t))-(4*t)) ∧
  ((4*t)-(R+24*t)+((2*q+-6)-(R+24*t)))+6≤((8*t-2)-(R+24*t)+((2*q+-6)-(R+24*t)))
def c0_22_sound (t q R : ℤ) (ht : 1≤t) (hc : c0_22 t q R) :
    Four t (2*t*(4*q+0)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-6)-(R+24*t))-(8*t-1)) ((4*t)-(R+24*t)+((2*q+-6)-(R+24*t))) (((2*q+-6)-(R+24*t))-(4*t)) ((8*t-2)-(R+24*t)+((2*q+-6)-(R+24*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-6)-(R+24*t))-7*z
  let x : ℤ := (R+24*t)-((2*q+-6)-(R+24*t))+6*z
  have hx : (4*t)≤x ∧ x≤(8*t-2) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (2*t) (4*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,2,4,16,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+0)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c1_20 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-7)-(R+30*t))-(4*t)) ∧
  6*(16*t)≤((8*t-2)-(R+30*t)+((2*q+-7)-(R+30*t))) ∧
  (((2*q+-7)-(R+30*t))-(8*t-1))≤7*(32*t-1) ∧
  ((4*t)-(R+30*t)+((2*q+-7)-(R+30*t)))≤6*(32*t-1) ∧
  (((2*q+-7)-(R+30*t))-(8*t-1))+7≤(((2*q+-7)-(R+30*t))-(4*t)) ∧
  6*(((2*q+-7)-(R+30*t))-(8*t-1))+42≤7*((8*t-2)-(R+30*t)+((2*q+-7)-(R+30*t))) ∧
  7*((4*t)-(R+30*t)+((2*q+-7)-(R+30*t)))+42≤6*(((2*q+-7)-(R+30*t))-(4*t)) ∧
  ((4*t)-(R+30*t)+((2*q+-7)-(R+30*t)))+6≤((8*t-2)-(R+30*t)+((2*q+-7)-(R+30*t)))
def c1_20_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_20 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-7)-(R+30*t))-(8*t-1)) ((4*t)-(R+30*t)+((2*q+-7)-(R+30*t))) (((2*q+-7)-(R+30*t))-(4*t)) ((8*t-2)-(R+30*t)+((2*q+-7)-(R+30*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-7)-(R+30*t))-7*z
  let x : ℤ := (R+30*t)-((2*q+-7)-(R+30*t))+6*z
  have hx : (4*t)≤x ∧ x≤(8*t-2) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (2*t) (4*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,2,4,16,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c1_21 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-6)-(R+26*t))-(4*t)) ∧
  6*(16*t)≤((8*t-2)-(R+26*t)+((2*q+-6)-(R+26*t))) ∧
  (((2*q+-6)-(R+26*t))-(8*t-1))≤7*(32*t-1) ∧
  ((4*t)-(R+26*t)+((2*q+-6)-(R+26*t)))≤6*(32*t-1) ∧
  (((2*q+-6)-(R+26*t))-(8*t-1))+7≤(((2*q+-6)-(R+26*t))-(4*t)) ∧
  6*(((2*q+-6)-(R+26*t))-(8*t-1))+42≤7*((8*t-2)-(R+26*t)+((2*q+-6)-(R+26*t))) ∧
  7*((4*t)-(R+26*t)+((2*q+-6)-(R+26*t)))+42≤6*(((2*q+-6)-(R+26*t))-(4*t)) ∧
  ((4*t)-(R+26*t)+((2*q+-6)-(R+26*t)))+6≤((8*t-2)-(R+26*t)+((2*q+-6)-(R+26*t)))
def c1_21_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_21 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-6)-(R+26*t))-(8*t-1)) ((4*t)-(R+26*t)+((2*q+-6)-(R+26*t))) (((2*q+-6)-(R+26*t))-(4*t)) ((8*t-2)-(R+26*t)+((2*q+-6)-(R+26*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-6)-(R+26*t))-7*z
  let x : ℤ := (R+26*t)-((2*q+-6)-(R+26*t))+6*z
  have hx : (4*t)≤x ∧ x≤(8*t-2) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (2*t) (4*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,2,4,16,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c1_22 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-7)-(R+30*t))-(8*t)) ∧
  6*(16*t)≤((4*t-1)-(R+30*t)+((2*q+-7)-(R+30*t))) ∧
  (((2*q+-7)-(R+30*t))-(16*t-2))≤7*(32*t-1) ∧
  ((2*t)-(R+30*t)+((2*q+-7)-(R+30*t)))≤6*(32*t-1) ∧
  (((2*q+-7)-(R+30*t))-(16*t-2))+7≤(((2*q+-7)-(R+30*t))-(8*t)) ∧
  6*(((2*q+-7)-(R+30*t))-(16*t-2))+42≤7*((4*t-1)-(R+30*t)+((2*q+-7)-(R+30*t))) ∧
  7*((2*t)-(R+30*t)+((2*q+-7)-(R+30*t)))+42≤6*(((2*q+-7)-(R+30*t))-(8*t)) ∧
  ((2*t)-(R+30*t)+((2*q+-7)-(R+30*t)))+6≤((4*t-1)-(R+30*t)+((2*q+-7)-(R+30*t)))
def c1_22_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_22 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-7)-(R+30*t))-(16*t-2)) ((2*t)-(R+30*t)+((2*q+-7)-(R+30*t))) (((2*q+-7)-(R+30*t))-(8*t)) ((4*t-1)-(R+30*t)+((2*q+-7)-(R+30*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-7)-(R+30*t))-7*z
  let x : ℤ := (R+30*t)-((2*q+-7)-(R+30*t))+6*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c1_23 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-8)-(R+34*t))-(4*t)) ∧
  6*(16*t)≤((8*t-2)-(R+34*t)+((2*q+-8)-(R+34*t))) ∧
  (((2*q+-8)-(R+34*t))-(8*t-1))≤7*(32*t-1) ∧
  ((4*t)-(R+34*t)+((2*q+-8)-(R+34*t)))≤6*(32*t-1) ∧
  (((2*q+-8)-(R+34*t))-(8*t-1))+7≤(((2*q+-8)-(R+34*t))-(4*t)) ∧
  6*(((2*q+-8)-(R+34*t))-(8*t-1))+42≤7*((8*t-2)-(R+34*t)+((2*q+-8)-(R+34*t))) ∧
  7*((4*t)-(R+34*t)+((2*q+-8)-(R+34*t)))+42≤6*(((2*q+-8)-(R+34*t))-(4*t)) ∧
  ((4*t)-(R+34*t)+((2*q+-8)-(R+34*t)))+6≤((8*t-2)-(R+34*t)+((2*q+-8)-(R+34*t)))
def c1_23_sound (t q R : ℤ) (ht : 1≤t) (hc : c1_23 t q R) :
    Four t (2*t*(4*q+1)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-8)-(R+34*t))-(8*t-1)) ((4*t)-(R+34*t)+((2*q+-8)-(R+34*t))) (((2*q+-8)-(R+34*t))-(4*t)) ((8*t-2)-(R+34*t)+((2*q+-8)-(R+34*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-8)-(R+34*t))-7*z
  let x : ℤ := (R+34*t)-((2*q+-8)-(R+34*t))+6*z
  have hx : (4*t)≤x ∧ x≤(8*t-2) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (2*t) (4*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,2,4,16,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+1)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c2_18 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-2) ∧
  3*(16*t)≤(((2*q+-9)-(R+40*t))-(4*t)) ∧
  2*(16*t)≤((4*t-1)-(R+40*t)+((2*q+-9)-(R+40*t))) ∧
  (((2*q+-9)-(R+40*t))-(8*t-1))≤3*(32*t-2) ∧
  ((2*t)-(R+40*t)+((2*q+-9)-(R+40*t)))≤2*(32*t-2) ∧
  (((2*q+-9)-(R+40*t))-(8*t-1))+3≤(((2*q+-9)-(R+40*t))-(4*t)) ∧
  2*(((2*q+-9)-(R+40*t))-(8*t-1))+6≤3*((4*t-1)-(R+40*t)+((2*q+-9)-(R+40*t))) ∧
  3*((2*t)-(R+40*t)+((2*q+-9)-(R+40*t)))+6≤2*(((2*q+-9)-(R+40*t))-(4*t)) ∧
  ((2*t)-(R+40*t)+((2*q+-9)-(R+40*t)))+2≤((4*t-1)-(R+40*t)+((2*q+-9)-(R+40*t)))
def c2_18_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_18 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-2) (((2*q+-9)-(R+40*t))-(8*t-1)) ((2*t)-(R+40*t)+((2*q+-9)-(R+40*t))) (((2*q+-9)-(R+40*t))-(4*t)) ((4*t-1)-(R+40*t)+((2*q+-9)-(R+40*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-9)-(R+40*t))-3*z
  let x : ℤ := (R+40*t)-((2*q+-9)-(R+40*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-2) := ⟨hzL,hzU⟩
  obtain ⟨z0,z1,hz0L,hz0U,hz1L,hz1U,hzsum⟩ := split_two (8*t) (16*t-1) z (by omega) (by rcases hz with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,8,8,x,y,z0,z1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hzsum]
        ring

def c2_19 (t q R : ℤ) : Prop :=
  (12*t)≤((R+36*t)-((1*q+-4)-(R+36*t))) ∧
  ((R+36*t)-((1*q+-4)-(R+36*t)))≤(24*t-3) ∧
  (8*t)≤((1*q+-4)-(R+36*t)) ∧
  ((1*q+-4)-(R+36*t))≤(16*t-1)
def c2_19_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_19 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  let y : ℤ := ((1*q+-4)-(R+36*t))
  let x : ℤ := ((R+36*t)-((1*q+-4)-(R+36*t)))
  have hx : (12*t)≤x ∧ x≤(24*t-3) := ⟨hc.1,hc.2.1⟩
  have hy : (8*t)≤y ∧ y≤(16*t-1) := hc.2.2
  obtain ⟨x0,x1,x2,hx0L,hx0U,hx1L,hx1U,hx2L,hx2U,hxsum⟩ := split_three (4*t) (8*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,4,4,8,x0,x1,x2,y, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c2_20 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-7)-(R+32*t))-(8*t)) ∧
  6*(16*t)≤((4*t-1)-(R+32*t)+((2*q+-7)-(R+32*t))) ∧
  (((2*q+-7)-(R+32*t))-(16*t-2))≤7*(32*t-1) ∧
  ((2*t)-(R+32*t)+((2*q+-7)-(R+32*t)))≤6*(32*t-1) ∧
  (((2*q+-7)-(R+32*t))-(16*t-2))+7≤(((2*q+-7)-(R+32*t))-(8*t)) ∧
  6*(((2*q+-7)-(R+32*t))-(16*t-2))+42≤7*((4*t-1)-(R+32*t)+((2*q+-7)-(R+32*t))) ∧
  7*((2*t)-(R+32*t)+((2*q+-7)-(R+32*t)))+42≤6*(((2*q+-7)-(R+32*t))-(8*t)) ∧
  ((2*t)-(R+32*t)+((2*q+-7)-(R+32*t)))+6≤((4*t-1)-(R+32*t)+((2*q+-7)-(R+32*t)))
def c2_20_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_20 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-7)-(R+32*t))-(16*t-2)) ((2*t)-(R+32*t)+((2*q+-7)-(R+32*t))) (((2*q+-7)-(R+32*t))-(8*t)) ((4*t-1)-(R+32*t)+((2*q+-7)-(R+32*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-7)-(R+32*t))-7*z
  let x : ℤ := (R+32*t)-((2*q+-7)-(R+32*t))+6*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c2_21 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-8)-(R+36*t))-(8*t)) ∧
  6*(16*t)≤((4*t-1)-(R+36*t)+((2*q+-8)-(R+36*t))) ∧
  (((2*q+-8)-(R+36*t))-(16*t-2))≤7*(32*t-1) ∧
  ((2*t)-(R+36*t)+((2*q+-8)-(R+36*t)))≤6*(32*t-1) ∧
  (((2*q+-8)-(R+36*t))-(16*t-2))+7≤(((2*q+-8)-(R+36*t))-(8*t)) ∧
  6*(((2*q+-8)-(R+36*t))-(16*t-2))+42≤7*((4*t-1)-(R+36*t)+((2*q+-8)-(R+36*t))) ∧
  7*((2*t)-(R+36*t)+((2*q+-8)-(R+36*t)))+42≤6*(((2*q+-8)-(R+36*t))-(8*t)) ∧
  ((2*t)-(R+36*t)+((2*q+-8)-(R+36*t)))+6≤((4*t-1)-(R+36*t)+((2*q+-8)-(R+36*t)))
def c2_21_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_21 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-8)-(R+36*t))-(16*t-2)) ((2*t)-(R+36*t)+((2*q+-8)-(R+36*t))) (((2*q+-8)-(R+36*t))-(8*t)) ((4*t-1)-(R+36*t)+((2*q+-8)-(R+36*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-8)-(R+36*t))-7*z
  let x : ℤ := (R+36*t)-((2*q+-8)-(R+36*t))+6*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c2_22 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-9)-(R+40*t))-(8*t)) ∧
  6*(16*t)≤((4*t-1)-(R+40*t)+((2*q+-9)-(R+40*t))) ∧
  (((2*q+-9)-(R+40*t))-(16*t-2))≤7*(32*t-1) ∧
  ((2*t)-(R+40*t)+((2*q+-9)-(R+40*t)))≤6*(32*t-1) ∧
  (((2*q+-9)-(R+40*t))-(16*t-2))+7≤(((2*q+-9)-(R+40*t))-(8*t)) ∧
  6*(((2*q+-9)-(R+40*t))-(16*t-2))+42≤7*((4*t-1)-(R+40*t)+((2*q+-9)-(R+40*t))) ∧
  7*((2*t)-(R+40*t)+((2*q+-9)-(R+40*t)))+42≤6*(((2*q+-9)-(R+40*t))-(8*t)) ∧
  ((2*t)-(R+40*t)+((2*q+-9)-(R+40*t)))+6≤((4*t-1)-(R+40*t)+((2*q+-9)-(R+40*t)))
def c2_22_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_22 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-9)-(R+40*t))-(16*t-2)) ((2*t)-(R+40*t)+((2*q+-9)-(R+40*t))) (((2*q+-9)-(R+40*t))-(8*t)) ((4*t-1)-(R+40*t)+((2*q+-9)-(R+40*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-9)-(R+40*t))-7*z
  let x : ℤ := (R+40*t)-((2*q+-9)-(R+40*t))+6*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c2_23 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-2) ∧
  3*(16*t)≤(((2*q+-6)-(R+28*t))-(4*t)) ∧
  2*(16*t)≤((4*t-1)-(R+28*t)+((2*q+-6)-(R+28*t))) ∧
  (((2*q+-6)-(R+28*t))-(8*t-1))≤3*(32*t-2) ∧
  ((2*t)-(R+28*t)+((2*q+-6)-(R+28*t)))≤2*(32*t-2) ∧
  (((2*q+-6)-(R+28*t))-(8*t-1))+3≤(((2*q+-6)-(R+28*t))-(4*t)) ∧
  2*(((2*q+-6)-(R+28*t))-(8*t-1))+6≤3*((4*t-1)-(R+28*t)+((2*q+-6)-(R+28*t))) ∧
  3*((2*t)-(R+28*t)+((2*q+-6)-(R+28*t)))+6≤2*(((2*q+-6)-(R+28*t))-(4*t)) ∧
  ((2*t)-(R+28*t)+((2*q+-6)-(R+28*t)))+2≤((4*t-1)-(R+28*t)+((2*q+-6)-(R+28*t)))
def c2_23_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_23 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-2) (((2*q+-6)-(R+28*t))-(8*t-1)) ((2*t)-(R+28*t)+((2*q+-6)-(R+28*t))) (((2*q+-6)-(R+28*t))-(4*t)) ((4*t-1)-(R+28*t)+((2*q+-6)-(R+28*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-6)-(R+28*t))-3*z
  let x : ℤ := (R+28*t)-((2*q+-6)-(R+28*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-2) := ⟨hzL,hzU⟩
  obtain ⟨z0,z1,hz0L,hz0U,hz1L,hz1U,hzsum⟩ := split_two (8*t) (16*t-1) z (by omega) (by rcases hz with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,8,8,x,y,z0,z1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hzsum]
        ring

def c2_24 (t q R : ℤ) : Prop :=
  (4*t)≤((R+28*t)-((1*q+-3)-(R+28*t))) ∧
  ((R+28*t)-((1*q+-3)-(R+28*t)))≤(8*t-1) ∧
  (24*t)≤((1*q+-3)-(R+28*t)) ∧
  ((1*q+-3)-(R+28*t))≤(48*t-3)
def c2_24_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_24 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  let y : ℤ := ((1*q+-3)-(R+28*t))
  let x : ℤ := ((R+28*t)-((1*q+-3)-(R+28*t)))
  have hx : (4*t)≤x ∧ x≤(8*t-1) := ⟨hc.1,hc.2.1⟩
  have hy : (24*t)≤y ∧ y≤(48*t-3) := hc.2.2
  obtain ⟨y0,y1,y2,hy0L,hy0U,hy1L,hy1U,hy2L,hy2U,hysum⟩ := split_three (8*t) (16*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,8,8,8,x,y0,y1,y2, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c2_25 (t q R : ℤ) : Prop :=
  (8*t)≤(16*t-1) ∧
  3*(8*t)≤(((2*q+-4)-(R+20*t))-(4*t)) ∧
  2*(8*t)≤((8*t-2)-(R+20*t)+((2*q+-4)-(R+20*t))) ∧
  (((2*q+-4)-(R+20*t))-(8*t-1))≤3*(16*t-1) ∧
  ((4*t)-(R+20*t)+((2*q+-4)-(R+20*t)))≤2*(16*t-1) ∧
  (((2*q+-4)-(R+20*t))-(8*t-1))+3≤(((2*q+-4)-(R+20*t))-(4*t)) ∧
  2*(((2*q+-4)-(R+20*t))-(8*t-1))+6≤3*((8*t-2)-(R+20*t)+((2*q+-4)-(R+20*t))) ∧
  3*((4*t)-(R+20*t)+((2*q+-4)-(R+20*t)))+6≤2*(((2*q+-4)-(R+20*t))-(4*t)) ∧
  ((4*t)-(R+20*t)+((2*q+-4)-(R+20*t)))+2≤((8*t-2)-(R+20*t)+((2*q+-4)-(R+20*t)))
def c2_25_sound (t q R : ℤ) (ht : 1≤t) (hc : c2_25 t q R) :
    Four t (2*t*(4*q+2)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (8*t) (16*t-1) (((2*q+-4)-(R+20*t))-(8*t-1)) ((4*t)-(R+20*t)+((2*q+-4)-(R+20*t))) (((2*q+-4)-(R+20*t))-(4*t)) ((8*t-2)-(R+20*t)+((2*q+-4)-(R+20*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-4)-(R+20*t))-3*z
  let x : ℤ := (R+20*t)-((2*q+-4)-(R+20*t))+2*z
  have hx : (4*t)≤x ∧ x≤(8*t-2) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (8*t)≤z ∧ z≤(16*t-1) := ⟨hzL,hzU⟩
  obtain ⟨x0,x1,hx0L,hx0U,hx1L,hx1U,hxsum⟩ := split_two (2*t) (4*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,2,4,8,x0,x1,y,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+2)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring

def c3_21 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-8)-(R+38*t))-(8*t)) ∧
  6*(16*t)≤((4*t-1)-(R+38*t)+((2*q+-8)-(R+38*t))) ∧
  (((2*q+-8)-(R+38*t))-(16*t-2))≤7*(32*t-1) ∧
  ((2*t)-(R+38*t)+((2*q+-8)-(R+38*t)))≤6*(32*t-1) ∧
  (((2*q+-8)-(R+38*t))-(16*t-2))+7≤(((2*q+-8)-(R+38*t))-(8*t)) ∧
  6*(((2*q+-8)-(R+38*t))-(16*t-2))+42≤7*((4*t-1)-(R+38*t)+((2*q+-8)-(R+38*t))) ∧
  7*((2*t)-(R+38*t)+((2*q+-8)-(R+38*t)))+42≤6*(((2*q+-8)-(R+38*t))-(8*t)) ∧
  ((2*t)-(R+38*t)+((2*q+-8)-(R+38*t)))+6≤((4*t-1)-(R+38*t)+((2*q+-8)-(R+38*t)))
def c3_21_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_21 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-8)-(R+38*t))-(16*t-2)) ((2*t)-(R+38*t)+((2*q+-8)-(R+38*t))) (((2*q+-8)-(R+38*t))-(8*t)) ((4*t-1)-(R+38*t)+((2*q+-8)-(R+38*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-8)-(R+38*t))-7*z
  let x : ℤ := (R+38*t)-((2*q+-8)-(R+38*t))+6*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c3_22 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-9)-(R+42*t))-(8*t)) ∧
  6*(16*t)≤((4*t-1)-(R+42*t)+((2*q+-9)-(R+42*t))) ∧
  (((2*q+-9)-(R+42*t))-(16*t-2))≤7*(32*t-1) ∧
  ((2*t)-(R+42*t)+((2*q+-9)-(R+42*t)))≤6*(32*t-1) ∧
  (((2*q+-9)-(R+42*t))-(16*t-2))+7≤(((2*q+-9)-(R+42*t))-(8*t)) ∧
  6*(((2*q+-9)-(R+42*t))-(16*t-2))+42≤7*((4*t-1)-(R+42*t)+((2*q+-9)-(R+42*t))) ∧
  7*((2*t)-(R+42*t)+((2*q+-9)-(R+42*t)))+42≤6*(((2*q+-9)-(R+42*t))-(8*t)) ∧
  ((2*t)-(R+42*t)+((2*q+-9)-(R+42*t)))+6≤((4*t-1)-(R+42*t)+((2*q+-9)-(R+42*t)))
def c3_22_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_22 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-9)-(R+42*t))-(16*t-2)) ((2*t)-(R+42*t)+((2*q+-9)-(R+42*t))) (((2*q+-9)-(R+42*t))-(8*t)) ((4*t-1)-(R+42*t)+((2*q+-9)-(R+42*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-9)-(R+42*t))-7*z
  let x : ℤ := (R+42*t)-((2*q+-9)-(R+42*t))+6*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c3_23 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-7)-(R+34*t))-(8*t)) ∧
  6*(16*t)≤((4*t-1)-(R+34*t)+((2*q+-7)-(R+34*t))) ∧
  (((2*q+-7)-(R+34*t))-(16*t-2))≤7*(32*t-1) ∧
  ((2*t)-(R+34*t)+((2*q+-7)-(R+34*t)))≤6*(32*t-1) ∧
  (((2*q+-7)-(R+34*t))-(16*t-2))+7≤(((2*q+-7)-(R+34*t))-(8*t)) ∧
  6*(((2*q+-7)-(R+34*t))-(16*t-2))+42≤7*((4*t-1)-(R+34*t)+((2*q+-7)-(R+34*t))) ∧
  7*((2*t)-(R+34*t)+((2*q+-7)-(R+34*t)))+42≤6*(((2*q+-7)-(R+34*t))-(8*t)) ∧
  ((2*t)-(R+34*t)+((2*q+-7)-(R+34*t)))+6≤((4*t-1)-(R+34*t)+((2*q+-7)-(R+34*t)))
def c3_23_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_23 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-7)-(R+34*t))-(16*t-2)) ((2*t)-(R+34*t)+((2*q+-7)-(R+34*t))) (((2*q+-7)-(R+34*t))-(8*t)) ((4*t-1)-(R+34*t)+((2*q+-7)-(R+34*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-7)-(R+34*t))-7*z
  let x : ℤ := (R+34*t)-((2*q+-7)-(R+34*t))+6*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c3_24 (t q R : ℤ) : Prop :=
  (4*t)≤((R+30*t)-((1*q+-3)-(R+30*t))) ∧
  ((R+30*t)-((1*q+-3)-(R+30*t)))≤(8*t-1) ∧
  (24*t)≤((1*q+-3)-(R+30*t)) ∧
  ((1*q+-3)-(R+30*t))≤(48*t-3)
def c3_24_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_24 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  let y : ℤ := ((1*q+-3)-(R+30*t))
  let x : ℤ := ((R+30*t)-((1*q+-3)-(R+30*t)))
  have hx : (4*t)≤x ∧ x≤(8*t-1) := ⟨hc.1,hc.2.1⟩
  have hy : (24*t)≤y ∧ y≤(48*t-3) := hc.2.2
  obtain ⟨y0,y1,y2,hy0L,hy0U,hy1L,hy1U,hy2L,hy2U,hysum⟩ := split_three (8*t) (16*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,8,8,8,x,y0,y1,y2, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c3_25 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-1) ∧
  7*(16*t)≤(((2*q+-6)-(R+30*t))-(8*t)) ∧
  6*(16*t)≤((4*t-1)-(R+30*t)+((2*q+-6)-(R+30*t))) ∧
  (((2*q+-6)-(R+30*t))-(16*t-2))≤7*(32*t-1) ∧
  ((2*t)-(R+30*t)+((2*q+-6)-(R+30*t)))≤6*(32*t-1) ∧
  (((2*q+-6)-(R+30*t))-(16*t-2))+7≤(((2*q+-6)-(R+30*t))-(8*t)) ∧
  6*(((2*q+-6)-(R+30*t))-(16*t-2))+42≤7*((4*t-1)-(R+30*t)+((2*q+-6)-(R+30*t))) ∧
  7*((2*t)-(R+30*t)+((2*q+-6)-(R+30*t)))+42≤6*(((2*q+-6)-(R+30*t))-(8*t)) ∧
  ((2*t)-(R+30*t)+((2*q+-6)-(R+30*t)))+6≤((4*t-1)-(R+30*t)+((2*q+-6)-(R+30*t)))
def c3_25_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_25 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-1) (((2*q+-6)-(R+30*t))-(16*t-2)) ((2*t)-(R+30*t)+((2*q+-6)-(R+30*t))) (((2*q+-6)-(R+30*t))-(8*t)) ((4*t-1)-(R+30*t)+((2*q+-6)-(R+30*t))) 7 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-6)-(R+30*t))-7*z
  let x : ℤ := (R+30*t)-((2*q+-6)-(R+30*t))+6*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (8*t)≤y ∧ y≤(16*t-2) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-1) := ⟨hzL,hzU⟩
  obtain ⟨y0,y1,hy0L,hy0U,hy1L,hy1U,hysum⟩ := split_two (4*t) (8*t-1) y (by omega) (by rcases hy with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,4,16,x,y0,y1,z, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (4*t+1)*x + (8*t+1)*y + (32*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hysum]
        ring

def c3_26 (t q R : ℤ) : Prop :=
  (16*t)≤(32*t-2) ∧
  3*(16*t)≤(((2*q+-6)-(R+30*t))-(4*t)) ∧
  2*(16*t)≤((4*t-1)-(R+30*t)+((2*q+-6)-(R+30*t))) ∧
  (((2*q+-6)-(R+30*t))-(8*t-1))≤3*(32*t-2) ∧
  ((2*t)-(R+30*t)+((2*q+-6)-(R+30*t)))≤2*(32*t-2) ∧
  (((2*q+-6)-(R+30*t))-(8*t-1))+3≤(((2*q+-6)-(R+30*t))-(4*t)) ∧
  2*(((2*q+-6)-(R+30*t))-(8*t-1))+6≤3*((4*t-1)-(R+30*t)+((2*q+-6)-(R+30*t))) ∧
  3*((2*t)-(R+30*t)+((2*q+-6)-(R+30*t)))+6≤2*(((2*q+-6)-(R+30*t))-(4*t)) ∧
  ((2*t)-(R+30*t)+((2*q+-6)-(R+30*t)))+2≤((4*t-1)-(R+30*t)+((2*q+-6)-(R+30*t)))
def c3_26_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_26 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨z,hzL,hzU,hzA,hzC,hzB,hzD⟩ := three_interval (16*t) (32*t-2) (((2*q+-6)-(R+30*t))-(8*t-1)) ((2*t)-(R+30*t)+((2*q+-6)-(R+30*t))) (((2*q+-6)-(R+30*t))-(4*t)) ((4*t-1)-(R+30*t)+((2*q+-6)-(R+30*t))) 3 (by norm_num) h0 h1 h2 h3 h4 h5 (by nlinarith [h6]) (by nlinarith [h7]) h8
  let y : ℤ := ((2*q+-6)-(R+30*t))-3*z
  let x : ℤ := (R+30*t)-((2*q+-6)-(R+30*t))+2*z
  have hx : (2*t)≤x ∧ x≤(4*t-1) := by dsimp [x]; omega
  have hy : (4*t)≤y ∧ y≤(8*t-1) := by dsimp [y]; omega
  have hz : (16*t)≤z ∧ z≤(32*t-2) := ⟨hzL,hzU⟩
  obtain ⟨z0,z1,hz0L,hz0U,hz1L,hz1U,hzsum⟩ := split_two (8*t) (16*t-1) z (by omega) (by rcases hz with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨2,4,8,8,x,y,z0,z1, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (4*t+1)*x + (8*t+1)*y + (16*t+1)*z := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hzsum]
        ring

def c3_27 (t q R : ℤ) : Prop :=
  (12*t)≤((R+38*t)-((1*q+-4)-(R+38*t))) ∧
  ((R+38*t)-((1*q+-4)-(R+38*t)))≤(24*t-3) ∧
  (8*t)≤((1*q+-4)-(R+38*t)) ∧
  ((1*q+-4)-(R+38*t))≤(16*t-1)
def c3_27_sound (t q R : ℤ) (ht : 1≤t) (hc : c3_27 t q R) :
    Four t (2*t*(4*q+3)+R) := by
  let y : ℤ := ((1*q+-4)-(R+38*t))
  let x : ℤ := ((R+38*t)-((1*q+-4)-(R+38*t)))
  have hx : (12*t)≤x ∧ x≤(24*t-3) := ⟨hc.1,hc.2.1⟩
  have hy : (8*t)≤y ∧ y≤(16*t-1) := hc.2.2
  obtain ⟨x0,x1,x2,hx0L,hx0U,hx1L,hx1U,hx2L,hx2U,hxsum⟩ := split_three (4*t) (8*t-1) x (by omega) (by rcases hx with ⟨hl,hu⟩; constructor <;> omega)
  refine ⟨4,4,4,8,x0,x1,x2,y, by norm_num [Width], by norm_num [Width], by norm_num [Width], by norm_num [Width], ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · calc
      2*t*(4*q+3)+R = (8*t+1)*x + (16*t+1)*y := by dsimp [x,y]; ring
      _ = _ := by
        rw [← hxsum]
        ring



end A343268Proof

-- Component: A343268FiniteCore

namespace A343268Proof
open OMA.S_oeis_a343268

def codeVal (z : ℕ) : ℕ := (z/16)*(2^(z%16)+1)
def codeOK (z : ℕ) : Bool :=
  decide (1 ≤ z%16 ∧ 2^(z%16-1) ≤ z/16 ∧ z/16 < 2^(z%16))

def code_sound (z : ℕ) (h : codeOK z = true) : IsBinSquare (codeVal z) := by
  have h' : 1 ≤ z%16 ∧ 2^(z%16-1) ≤ z/16 ∧ z/16 < 2^(z%16) := by
    simpa only [codeOK, decide_eq_true_eq] using h
  exact ⟨z%16,z/16,h'.1,h'.2.1,h'.2.2,rfl⟩

abbrev Quad := ℕ × ℕ × ℕ × ℕ
def checkQuad (n : ℕ) (w : Quad) : Bool :=
  codeOK w.1 && codeOK w.2.1 && codeOK w.2.2.1 && codeOK w.2.2.2 &&
    decide (codeVal w.1+codeVal w.2.1+codeVal w.2.2.1+codeVal w.2.2.2=n)

def checkQuad_sound (n : ℕ) (w : Quad) (h : checkQuad n w = true) : Representable n := by
  have h' : codeOK w.1=true ∧ codeOK w.2.1=true ∧ codeOK w.2.2.1=true ∧
      codeOK w.2.2.2=true ∧ codeVal w.1+codeVal w.2.1+codeVal w.2.2.1+codeVal w.2.2.2=n := by
    simpa only [checkQuad, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h
  exact ⟨_,_,_,_,code_sound _ h'.1,code_sound _ h'.2.1,
    code_sound _ h'.2.2.1,code_sound _ h'.2.2.2.1,h'.2.2.2.2⟩

def checkFrom : ℕ → List Quad → Bool
  | _, [] => true
  | n, w::ws => checkQuad n w && checkFrom (n+1) ws

def checkFrom_sound (n : ℕ) (ws : List Quad) (h : checkFrom n ws = true)
    (i : ℕ) (hi : i < ws.length) : Representable (n+i) := by
  induction ws generalizing n i with
  | nil => simp at hi
  | cons w ws ih =>
    have h' : checkQuad n w=true ∧ checkFrom (n+1) ws=true := by
      simpa only [checkFrom, Bool.and_eq_true] using h
    cases i with
    | zero => simpa using checkQuad_sound n w h'.1
    | succ i =>
      have hi' : i < ws.length := by simpa using hi
      have hs := ih (n+1) h'.2 i hi'
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hs

def checkTagged (ws : List (ℕ × Quad)) : Bool := ws.all fun p => checkQuad p.1 p.2

def checkTagged_sound (ws : List (ℕ × Quad)) (h : checkTagged ws = true)
    (n : ℕ) (hn : n ∈ ws.map Prod.fst) : Representable n := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hn
  apply checkQuad_sound p.1 p.2
  exact List.all_eq_true.mp h p hp

end A343268Proof

-- Component: A343268Finite

namespace A343268Proof

def smallW0 : List Quad := [(17,99,341,501),
  (34,50,357,501),
  (17,212,261,501),
  (50,83,341,501),
  (99,228,261,469),
  (164,244,261,405),
  (50,50,357,501),
  (34,99,341,501),
  (34,180,277,501),
  (17,115,341,501),
  (115,132,277,501),
  (115,164,261,501),
  (50,99,341,501),
  (50,180,277,501),
  (50,212,261,501),
  (17,17,373,501),
  (34,115,341,501),
  (17,164,293,501),
  (83,115,325,501),
  (17,228,261,501),
  (99,212,261,485),
  (50,115,341,501),
  (17,34,373,501),
  (34,132,309,501),
  (17,83,357,501),
  (83,132,293,501),
  (83,164,277,501),
  (17,50,373,501),
  (50,132,309,501),
  (34,34,373,501),
  (50,196,277,501),
  (34,83,357,501),
  (212,261,261,261),
  (17,99,357,501),
  (34,50,373,501),
  (17,212,277,501),
  (50,83,357,501),
  (99,228,261,485),
  (164,244,261,421),
  (50,50,373,501),
  (34,99,357,501),
  (34,180,293,501),
  (17,115,357,501),
  (115,132,293,501),
  (115,164,277,501),
  (50,99,357,501),
  (50,180,293,501),
  (50,212,277,501),
  (17,17,389,501),
  (34,115,357,501),
  (17,164,309,501),
  (83,115,341,501),
  (17,228,277,501),
  (99,212,261,501),
  (50,115,357,501),
  (17,34,389,501),
  (34,132,325,501),
  (17,83,373,501),
  (83,132,309,501),
  (83,164,293,501),
  (17,50,389,501),
  (50,132,325,501),
  (34,34,389,501),
  (50,196,293,501),
  (34,83,373,501),
  (212,261,261,277),
  (17,99,373,501),
  (34,50,389,501),
  (17,212,293,501),
  (50,83,373,501),
  (99,228,261,501),
  (164,244,261,437),
  (50,50,389,501),
  (34,99,373,501),
  (34,180,309,501),
  (17,115,373,501),
  (115,132,309,501),
  (115,164,293,501),
  (50,99,373,501),
  (50,180,309,501),
  (50,212,293,501),
  (17,17,405,501),
  (34,115,373,501),
  (17,164,325,501),
  (83,115,357,501),
  (17,228,293,501),
  (99,212,277,501),
  (50,115,373,501),
  (17,34,405,501),
  (34,132,341,501),
  (17,83,389,501),
  (83,132,325,501),
  (83,164,309,501),
  (17,50,405,501),
  (50,132,341,501),
  (34,34,405,501),
  (50,196,309,501),
  (34,83,389,501),
  (212,261,261,293),
  (17,99,389,501),
  (34,50,405,501),
  (17,212,309,501),
  (50,83,389,501),
  (99,228,277,501),
  (164,244,261,453),
  (50,50,405,501),
  (34,99,389,501),
  (34,180,325,501),
  (17,115,389,501),
  (115,132,325,501),
  (115,164,309,501),
  (50,99,389,501),
  (50,180,325,501),
  (50,212,309,501),
  (17,17,421,501),
  (34,115,389,501),
  (17,164,341,501),
  (83,115,373,501),
  (17,228,309,501),
  (99,212,293,501),
  (50,115,389,501),
  (17,34,421,501),
  (34,132,357,501),
  (17,83,405,501),
  (83,132,341,501),
  (83,164,325,501),
  (17,50,421,501),
  (50,132,357,501)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def smallCheck0 : checkFrom 1773 smallW0 = true := by decide +kernel
set_option maxRecDepth 10000 in
def smallBlock0 (n : ℕ) (hl : 1773 ≤ n) (hu : n < 1901) : Representable n := by
  have h := checkFrom_sound 1773 smallW0 smallCheck0 (n-1773) (by change _ < 128; omega)
  have e : 1773+(n-1773) = n := by omega
  simpa only [e] using h

def smallW1 : List Quad := [(34,34,421,501),
  (50,196,325,501),
  (34,83,405,501),
  (212,261,261,309),
  (17,99,405,501),
  (34,50,421,501),
  (17,212,325,501),
  (50,83,405,501),
  (99,228,293,501),
  (164,244,261,469),
  (50,50,421,501),
  (34,99,405,501),
  (34,180,341,501),
  (17,115,405,501),
  (115,132,341,501),
  (115,164,325,501),
  (50,99,405,501),
  (50,180,341,501),
  (50,212,325,501),
  (17,17,437,501),
  (34,115,405,501),
  (17,164,357,501),
  (83,115,389,501),
  (17,228,325,501),
  (99,212,309,501),
  (50,115,405,501),
  (17,34,437,501),
  (34,132,373,501),
  (17,83,421,501),
  (83,132,357,501),
  (83,164,341,501),
  (17,50,437,501),
  (50,132,373,501),
  (34,34,437,501),
  (50,196,341,501),
  (34,83,421,501),
  (212,261,261,325),
  (17,99,421,501),
  (34,50,437,501),
  (17,212,341,501),
  (50,83,421,501),
  (99,228,309,501),
  (164,244,261,485),
  (50,50,437,501),
  (34,99,421,501),
  (34,180,357,501),
  (17,115,421,501),
  (115,132,357,501),
  (115,164,341,501),
  (50,99,421,501),
  (50,180,357,501),
  (50,212,341,501),
  (17,17,453,501),
  (34,115,421,501),
  (17,164,373,501),
  (83,115,405,501),
  (17,228,341,501),
  (99,212,325,501),
  (50,115,421,501),
  (17,34,453,501),
  (34,132,389,501),
  (17,83,437,501),
  (83,132,373,501),
  (83,164,357,501),
  (17,50,453,501),
  (50,132,389,501),
  (34,34,453,501),
  (50,196,357,501),
  (34,83,437,501),
  (212,261,261,341),
  (17,99,437,501),
  (34,50,453,501),
  (17,212,357,501),
  (50,83,437,501),
  (99,228,325,501),
  (164,244,261,501),
  (50,50,453,501),
  (34,99,437,501),
  (34,180,373,501),
  (17,115,437,501),
  (115,132,373,501),
  (115,164,357,501),
  (50,99,437,501),
  (50,180,373,501),
  (50,212,357,501),
  (17,17,469,501),
  (34,115,437,501),
  (17,164,389,501),
  (83,115,421,501),
  (17,228,357,501),
  (99,212,341,501),
  (50,115,437,501),
  (17,34,469,501),
  (34,132,405,501),
  (17,83,453,501),
  (83,132,389,501),
  (83,164,373,501),
  (17,50,469,501),
  (50,132,405,501),
  (34,34,469,501),
  (50,196,373,501),
  (34,83,453,501),
  (212,261,261,357),
  (17,99,453,501),
  (34,50,469,501),
  (17,212,373,501),
  (50,83,453,501),
  (99,228,341,501),
  (164,244,277,501),
  (50,50,469,501),
  (34,99,453,501),
  (34,180,389,501),
  (17,115,453,501),
  (115,132,389,501),
  (115,164,373,501),
  (50,99,453,501),
  (50,180,389,501),
  (50,212,373,501),
  (17,17,485,501),
  (34,115,453,501),
  (17,164,405,501),
  (83,115,437,501),
  (17,228,373,501),
  (99,212,357,501),
  (50,115,453,501),
  (17,34,485,501),
  (34,132,421,501),
  (17,83,469,501)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def smallCheck1 : checkFrom 1901 smallW1 = true := by decide +kernel
set_option maxRecDepth 10000 in
def smallBlock1 (n : ℕ) (hl : 1901 ≤ n) (hu : n < 2029) : Representable n := by
  have h := checkFrom_sound 1901 smallW1 smallCheck1 (n-1901) (by change _ < 128; omega)
  have e : 1901+(n-1901) = n := by omega
  simpa only [e] using h

def smallW2 : List Quad := [(83,132,405,501),
  (83,164,389,501),
  (17,50,485,501),
  (50,132,421,501),
  (34,34,485,501),
  (50,196,389,501),
  (34,83,469,501),
  (212,261,261,373),
  (17,99,469,501),
  (34,50,485,501),
  (17,212,389,501),
  (50,83,469,501),
  (99,228,357,501),
  (164,244,293,501),
  (50,50,485,501),
  (34,99,469,501),
  (34,180,405,501),
  (17,115,469,501),
  (115,132,405,501),
  (115,164,389,501),
  (50,99,469,501),
  (50,180,405,501),
  (50,212,389,501),
  (17,17,501,501),
  (34,115,469,501),
  (17,164,421,501),
  (83,115,453,501),
  (17,228,389,501),
  (99,212,373,501),
  (50,115,469,501),
  (17,34,501,501),
  (34,132,437,501),
  (17,83,485,501),
  (83,132,421,501),
  (83,164,405,501),
  (17,50,501,501),
  (50,132,437,501),
  (34,34,501,501),
  (50,196,405,501),
  (34,83,485,501),
  (212,261,261,389),
  (17,99,485,501),
  (34,50,501,501),
  (17,212,405,501),
  (50,83,485,501),
  (99,228,373,501),
  (164,244,309,501),
  (50,50,501,501),
  (34,99,485,501),
  (34,180,421,501),
  (17,115,485,501),
  (115,132,421,501),
  (115,164,405,501),
  (50,99,485,501),
  (50,180,421,501),
  (50,212,405,501),
  (17,67,501,501),
  (34,115,485,501),
  (17,164,437,501),
  (83,115,469,501),
  (17,17,17,518),
  (99,212,389,501),
  (50,115,485,501),
  (34,67,501,501),
  (34,132,453,501),
  (17,83,501,501),
  (83,132,437,501),
  (17,17,34,518),
  (50,67,501,501),
  (50,132,453,501),
  (50,164,437,501),
  (50,196,421,501),
  (17,17,50,518),
  (212,261,261,405),
  (17,34,34,518),
  (17,180,437,501),
  (17,212,421,501),
  (50,83,501,501),
  (99,228,389,501),
  (17,34,50,518),
  (196,244,309,501),
  (34,34,34,518),
  (34,180,437,501),
  (17,115,501,501),
  (17,50,50,518),
  (115,164,421,501),
  (34,34,50,518),
  (50,180,437,501),
  (50,212,421,501),
  (67,67,501,501),
  (34,115,501,501),
  (34,50,50,518),
  (83,115,485,501),
  (17,17,67,518),
  (99,212,405,501),
  (50,115,501,501),
  (50,50,50,518),
  (34,132,469,501),
  (67,83,501,501),
  (83,132,453,501),
  (17,34,67,518),
  (99,115,485,501),
  (17,17,83,518),
  (50,164,453,501),
  (50,196,437,501),
  (17,50,67,518),
  (212,261,261,421),
  (34,34,67,518),
  (17,180,453,501),
  (17,34,83,518),
  (115,115,485,501),
  (17,17,99,518),
  (34,50,67,518),
  (196,244,325,501),
  (17,50,83,518),
  (34,180,453,501),
  (34,34,83,518),
  (50,50,67,518),
  (17,34,99,518),
  (50,148,469,501),
  (17,17,115,518),
  (34,50,83,518),
  (50,244,421,501),
  (17,50,99,518),
  (17,164,469,501),
  (17,17,17,534),
  (50,50,83,518),
  (17,34,115,518)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def smallCheck2 : checkFrom 2029 smallW2 = true := by decide +kernel
set_option maxRecDepth 10000 in
def smallBlock2 (n : ℕ) (hl : 2029 ≤ n) (hu : n < 2157) : Representable n := by
  have h := checkFrom_sound 2029 smallW2 smallCheck2 (n-2029) (by change _ < 128; omega)
  have e : 2029+(n-2029) = n := by omega
  simpa only [e] using h

def smallW3 : List Quad := [(99,244,405,501),
  (180,244,341,501),
  (34,50,99,518),
  (34,164,469,501),
  (17,17,34,534),
  (34,67,67,518),
  (34,34,115,518),
  (50,50,99,518),
  (50,164,469,501),
  (17,17,50,534),
  (50,67,67,518),
  (17,34,34,534),
  (17,148,485,501),
  (17,180,469,501),
  (34,67,83,518),
  (115,115,501,501),
  (17,34,50,534),
  (164,244,357,501),
  (34,34,34,534),
  (50,67,83,518),
  (34,180,469,501),
  (17,50,50,534),
  (115,132,469,501),
  (34,34,50,534),
  (50,148,485,501),
  (17,67,115,518),
  (50,212,453,501),
  (50,244,437,501),
  (34,50,50,534),
  (17,164,485,501),
  (17,17,67,534),
  (67,67,67,518),
  (34,67,115,518),
  (50,50,50,534),
  (17,83,115,518),
  (34,132,501,501),
  (34,164,485,501),
  (17,34,67,534),
  (83,164,469,501),
  (17,17,83,534),
  (67,67,83,518),
  (34,83,115,518),
  (17,50,67,534),
  (17,99,115,518),
  (34,34,67,534),
  (17,148,501,501),
  (17,34,83,534),
  (17,212,469,501),
  (17,17,99,534),
  (34,50,67,534),
  (34,99,115,518),
  (17,50,83,534),
  (17,115,115,518),
  (34,34,83,534),
  (50,50,67,534),
  (17,34,99,534),
  (115,164,469,501),
  (17,17,115,534),
  (34,50,83,534),
  (34,115,115,518),
  (17,50,99,534),
  (67,132,501,501),
  (17,17,17,550),
  (50,50,83,534),
  (17,34,115,534),
  (17,17,132,518),
  (99,244,437,501),
  (34,50,99,534),
  (212,244,357,501),
  (17,17,34,550),
  (34,67,67,534),
  (34,34,115,534),
  (17,34,132,518),
  (115,180,469,501),
  (17,17,50,550),
  (50,67,67,534),
  (17,34,34,550),
  (17,50,132,518),
  (67,148,501,501),
  (34,34,132,518),
  (17,212,485,501),
  (17,34,50,550),
  (17,17,148,518),
  (34,34,34,550),
  (34,50,132,518),
  (67,115,115,518),
  (17,50,50,550),
  (83,148,501,501),
  (34,34,50,550),
  (17,34,148,518),
  (17,67,115,534),
  (50,180,501,501),
  (50,212,485,501),
  (34,50,50,550),
  (17,50,148,518),
  (17,17,67,550),
  (34,34,148,518),
  (34,67,115,534),
  (50,50,50,550),
  (17,17,164,518),
  (180,244,389,501),
  (34,50,148,518),
  (17,34,67,550),
  (99,115,115,518),
  (17,17,83,550),
  (34,67,132,518),
  (17,34,164,518),
  (17,50,67,550),
  (17,99,115,534),
  (34,34,67,550),
  (50,67,132,518),
  (17,34,83,550),
  (115,115,115,518),
  (17,17,99,550),
  (34,50,67,550),
  (17,67,148,518),
  (17,17,180,518),
  (17,115,115,534),
  (34,34,83,550),
  (50,50,67,550),
  (17,34,99,550),
  (83,180,501,501),
  (17,17,115,550),
  (17,34,180,518),
  (17,83,148,518),
  (17,50,99,550),
  (50,244,485,501),
  (17,17,17,566)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def smallCheck3 : checkFrom 2157 smallW3 = true := by decide +kernel
set_option maxRecDepth 10000 in
def smallBlock3 (n : ℕ) (hl : 2157 ≤ n) (hu : n < 2285) : Representable n := by
  have h := checkFrom_sound 2157 smallW3 smallCheck3 (n-2157) (by change _ < 128; omega)
  have e : 2157+(n-2157) = n := by omega
  simpa only [e] using h

def smallW4 : List Quad := [(17,50,180,518),
  (17,34,115,550),
  (17,17,132,534),
  (34,83,148,518),
  (34,50,99,550),
  (17,17,196,518),
  (17,17,34,566),
  (34,50,180,518),
  (34,34,115,550),
  (17,34,132,534),
  (83,196,501,501),
  (17,17,50,566),
  (17,34,196,518),
  (17,34,34,566),
  (17,50,132,534),
  (212,261,261,501),
  (34,34,132,534),
  (17,50,196,518),
  (17,34,50,566),
  (17,17,148,534),
  (34,34,34,566),
  (34,50,132,534),
  (17,17,212,518),
  (17,50,50,566),
  (34,50,196,518),
  (34,34,50,566),
  (17,34,148,534),
  (17,67,115,550),
  (34,67,180,518),
  (17,34,212,518),
  (34,50,50,566),
  (17,50,148,534),
  (17,17,67,566),
  (34,34,148,534),
  (17,50,212,518),
  (50,50,50,566),
  (17,17,164,534),
  (34,83,180,518),
  (34,50,148,534),
  (17,17,228,518),
  (99,115,115,534),
  (17,17,83,566),
  (34,67,132,534),
  (17,34,164,534),
  (17,50,67,566),
  (34,67,196,518),
  (17,34,228,518),
  (17,83,196,518),
  (17,34,83,566),
  (115,115,115,534),
  (17,17,99,566),
  (17,50,228,518),
  (17,67,148,534),
  (17,17,180,534),
  (34,83,196,518),
  (34,34,83,566),
  (17,17,244,518),
  (17,34,99,566),
  (34,50,228,518),
  (17,17,115,566),
  (17,34,180,534),
  (17,83,148,534),
  (17,50,99,566),
  (17,34,244,518),
  (17,17,17,582),
  (17,50,180,534),
  (17,34,115,566),
  (17,17,132,550),
  (17,50,244,518),
  (34,50,99,566),
  (17,17,196,534),
  (17,17,34,582),
  (34,50,180,534),
  (34,34,115,566),
  (17,34,132,550),
  (34,50,244,518),
  (17,17,50,582),
  (17,34,196,534),
  (17,34,34,582),
  (17,50,132,550),
  (50,50,244,518),
  (34,34,132,550),
  (17,50,196,534),
  (17,34,50,582),
  (17,17,148,550),
  (34,34,34,582),
  (34,50,132,550),
  (17,17,212,534),
  (17,50,50,582),
  (34,50,196,534),
  (34,34,50,582),
  (17,34,148,550),
  (17,67,115,566),
  (34,67,180,534),
  (17,34,212,534),
  (34,50,50,582),
  (17,50,148,550),
  (17,17,67,582),
  (34,34,148,550),
  (17,50,212,534),
  (50,50,50,582),
  (17,17,164,550),
  (34,83,180,534),
  (34,50,148,550),
  (17,17,228,534),
  (34,83,244,518),
  (17,17,83,582),
  (34,67,132,550),
  (17,34,164,550),
  (17,50,67,582),
  (34,67,196,534),
  (17,34,228,534),
  (17,83,196,534),
  (17,34,83,582),
  (34,99,244,518),
  (17,17,99,582),
  (17,50,228,534),
  (17,67,148,550),
  (17,17,180,550),
  (34,83,196,534),
  (34,34,83,582),
  (17,17,244,534),
  (17,34,99,582),
  (34,50,228,534),
  (17,17,115,582),
  (17,34,180,550),
  (17,83,148,550),
  (17,50,99,582)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def smallCheck4 : checkFrom 2285 smallW4 = true := by decide +kernel
set_option maxRecDepth 10000 in
def smallBlock4 (n : ℕ) (hl : 2285 ≤ n) (hu : n < 2413) : Representable n := by
  have h := checkFrom_sound 2285 smallW4 smallCheck4 (n-2285) (by change _ < 128; omega)
  have e : 2285+(n-2285) = n := by omega
  simpa only [e] using h

def smallW5 : List Quad := [(17,34,244,534),
  (17,17,17,598),
  (17,50,180,550),
  (17,34,115,582),
  (17,17,132,566),
  (17,50,244,534),
  (34,50,99,582),
  (17,17,196,550),
  (17,17,34,598),
  (34,50,180,550),
  (34,34,115,582),
  (17,34,132,566),
  (34,50,244,534),
  (17,17,50,598),
  (17,34,196,550),
  (17,34,34,598),
  (17,50,132,566),
  (50,50,244,534),
  (34,34,132,566),
  (17,50,196,550),
  (17,34,50,598),
  (17,17,148,566),
  (34,34,34,598),
  (34,50,132,566),
  (17,17,212,550),
  (17,50,50,598),
  (34,50,196,550),
  (34,34,50,598),
  (17,34,148,566),
  (17,67,115,582),
  (34,67,180,550),
  (17,34,212,550),
  (34,50,50,598),
  (17,50,148,566),
  (17,17,67,598),
  (34,34,148,566),
  (17,50,212,550),
  (50,50,50,598),
  (17,17,164,566),
  (34,83,180,550),
  (34,50,148,566),
  (17,17,228,550),
  (34,83,244,534),
  (17,17,83,598),
  (34,67,132,566),
  (17,34,164,566),
  (17,50,67,598),
  (34,67,196,550),
  (17,34,228,550),
  (17,83,196,550),
  (17,34,83,598),
  (34,99,244,534),
  (17,17,99,598),
  (17,50,228,550),
  (17,67,148,566),
  (17,17,180,566),
  (34,83,196,550),
  (34,34,83,598),
  (17,17,244,550),
  (17,34,99,598),
  (34,50,228,550),
  (17,17,115,598),
  (17,34,180,566),
  (17,83,148,566),
  (17,50,99,598),
  (17,34,244,550),
  (17,17,17,614),
  (17,50,180,566),
  (17,34,115,598),
  (17,17,132,582),
  (17,50,244,550),
  (34,50,99,598),
  (17,17,196,566),
  (17,17,34,614),
  (34,50,180,566),
  (34,34,115,598),
  (17,34,132,582),
  (34,50,244,550),
  (17,17,50,614),
  (17,34,196,566),
  (17,34,34,614),
  (17,50,132,582),
  (50,50,244,550),
  (34,34,132,582),
  (17,50,196,566),
  (17,34,50,614),
  (17,17,148,582),
  (34,34,34,614),
  (34,50,132,582),
  (17,17,212,566),
  (17,50,50,614),
  (34,50,196,566),
  (34,34,50,614),
  (17,34,148,582),
  (17,67,115,598),
  (34,67,180,566),
  (17,34,212,566),
  (34,50,50,614),
  (17,50,148,582),
  (17,17,67,614),
  (34,34,148,582),
  (17,50,212,566),
  (50,50,50,614),
  (17,17,164,582),
  (34,83,180,566),
  (34,50,148,582),
  (17,17,228,566),
  (34,83,244,550),
  (17,17,83,614),
  (34,67,132,582),
  (17,34,164,582),
  (17,50,67,614),
  (34,67,196,566),
  (17,34,228,566),
  (17,83,196,566),
  (17,34,83,614),
  (34,99,244,550),
  (17,17,99,614),
  (17,50,228,566),
  (17,67,148,582),
  (17,17,180,582),
  (34,83,196,566),
  (34,34,83,614),
  (17,17,244,566),
  (17,34,99,614),
  (34,50,228,566),
  (17,17,115,614),
  (17,34,180,582)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def smallCheck5 : checkFrom 2413 smallW5 = true := by decide +kernel
set_option maxRecDepth 10000 in
def smallBlock5 (n : ℕ) (hl : 2413 ≤ n) (hu : n < 2541) : Representable n := by
  have h := checkFrom_sound 2413 smallW5 smallCheck5 (n-2413) (by change _ < 128; omega)
  have e : 2413+(n-2413) = n := by omega
  simpa only [e] using h

def smallW6 : List Quad := [(17,83,148,582),
  (17,50,99,614),
  (17,34,244,566),
  (17,17,17,630),
  (17,50,180,582),
  (17,34,115,614),
  (17,17,132,598),
  (17,50,244,566),
  (34,50,99,614),
  (17,17,196,582),
  (17,17,34,630),
  (34,50,180,582),
  (34,34,115,614),
  (17,34,132,598),
  (34,50,244,566),
  (17,17,50,630),
  (17,34,196,582),
  (17,34,34,630),
  (17,50,132,598),
  (50,50,244,566),
  (34,34,132,598),
  (17,50,196,582),
  (17,34,50,630),
  (17,17,148,598),
  (34,34,34,630),
  (34,50,132,598),
  (17,17,212,582),
  (17,50,50,630),
  (34,50,196,582),
  (34,34,50,630),
  (17,34,148,598),
  (17,67,115,614),
  (34,67,180,582),
  (17,34,212,582),
  (34,50,50,630),
  (17,50,148,598),
  (17,17,67,630),
  (34,34,148,598),
  (17,50,212,582),
  (50,50,50,630),
  (17,17,164,598),
  (34,83,180,582),
  (34,50,148,598),
  (17,17,228,582),
  (34,83,244,566),
  (17,17,83,630),
  (34,67,132,598),
  (17,34,164,598),
  (17,50,67,630),
  (34,67,196,582),
  (17,34,228,582),
  (17,83,196,582),
  (17,34,83,630),
  (34,99,244,566),
  (17,17,99,630),
  (17,50,228,582),
  (17,67,148,598),
  (17,17,180,598),
  (34,83,196,582),
  (34,34,83,630),
  (17,17,244,582),
  (17,34,99,630),
  (34,50,228,582),
  (17,17,115,630),
  (17,34,180,598),
  (17,83,148,598),
  (17,50,99,630),
  (17,34,244,582),
  (17,17,17,646),
  (17,50,180,598),
  (17,34,115,630),
  (17,17,132,614),
  (17,50,244,582),
  (17,17,261,518),
  (17,17,196,598),
  (17,17,34,646),
  (34,50,180,598),
  (34,34,115,630),
  (17,34,132,614),
  (34,50,244,582),
  (17,17,50,646),
  (17,34,196,598),
  (17,34,34,646),
  (17,50,132,614),
  (50,50,244,582),
  (17,50,261,518),
  (17,50,196,598),
  (17,34,50,646),
  (17,17,148,614),
  (34,34,34,646),
  (34,50,132,614),
  (17,17,212,598),
  (17,50,50,646),
  (34,50,196,598),
  (34,34,50,646),
  (17,34,148,614),
  (17,67,115,630),
  (50,50,261,518),
  (17,34,212,598),
  (34,50,50,646),
  (17,50,148,614),
  (17,17,67,646),
  (34,34,148,614),
  (17,50,212,598),
  (50,50,50,646),
  (17,17,164,614),
  (17,17,277,518),
  (34,50,148,614),
  (17,17,228,598),
  (34,83,244,582),
  (17,17,83,646),
  (34,67,132,614),
  (17,34,164,614),
  (17,34,277,518),
  (34,67,196,598),
  (17,34,228,598),
  (17,83,196,598),
  (17,34,83,646),
  (17,50,277,518),
  (17,17,99,646),
  (17,50,228,598),
  (17,67,148,614),
  (17,17,180,614),
  (34,83,196,598),
  (34,34,83,646),
  (17,17,244,598),
  (17,34,99,646),
  (34,50,228,598)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def smallCheck6 : checkFrom 2541 smallW6 = true := by decide +kernel
set_option maxRecDepth 10000 in
def smallBlock6 (n : ℕ) (hl : 2541 ≤ n) (hu : n < 2669) : Representable n := by
  have h := checkFrom_sound 2541 smallW6 smallCheck6 (n-2541) (by change _ < 128; omega)
  have e : 2541+(n-2541) = n := by omega
  simpa only [e] using h

def smallW7 : List Quad := [(17,17,115,646),
  (17,34,180,614),
  (50,50,277,518),
  (17,50,99,646),
  (17,34,244,598),
  (17,17,17,662),
  (17,50,180,614),
  (17,34,115,646),
  (17,17,132,630),
  (17,50,244,598),
  (17,17,261,534),
  (17,17,196,614),
  (17,17,34,662),
  (34,50,180,614),
  (34,34,115,646),
  (17,34,132,630),
  (34,50,244,598),
  (17,17,50,662),
  (17,34,196,614),
  (17,34,34,662),
  (17,50,132,630),
  (50,50,244,598),
  (17,50,261,534),
  (17,50,196,614),
  (17,34,50,662),
  (17,17,148,630),
  (34,34,34,662),
  (34,50,132,630),
  (17,17,212,614),
  (17,50,50,662),
  (34,50,196,614),
  (34,34,50,662),
  (17,34,148,630),
  (17,67,115,646),
  (50,50,261,534),
  (17,34,212,614),
  (34,50,50,662),
  (17,50,148,630),
  (17,17,67,662),
  (34,34,148,630),
  (17,50,212,614),
  (50,50,50,662),
  (17,17,164,630),
  (17,17,277,534),
  (17,17,309,518),
  (17,17,228,614),
  (34,83,244,598),
  (17,17,83,662),
  (34,67,132,630),
  (17,34,164,630),
  (17,34,277,534),
  (17,34,309,518),
  (17,34,228,614),
  (17,83,196,614),
  (17,34,83,662),
  (17,50,277,534),
  (17,17,99,662),
  (17,50,228,614),
  (34,34,309,518),
  (17,17,180,630),
  (34,83,196,614),
  (34,34,83,662),
  (17,17,244,614),
  (17,34,99,662),
  (34,50,228,614),
  (17,17,115,662),
  (17,34,180,630),
  (50,50,277,534),
  (17,50,99,662),
  (17,34,244,614),
  (17,17,17,678),
  (17,50,180,630),
  (17,34,115,662),
  (17,17,132,646),
  (17,50,244,614),
  (17,17,261,550),
  (17,17,196,630),
  (17,17,34,678),
  (34,50,180,630),
  (34,34,115,662),
  (17,34,132,646),
  (34,50,244,614),
  (17,17,50,678),
  (17,34,196,630),
  (17,34,34,678),
  (17,50,132,646),
  (50,50,244,614),
  (17,50,261,550),
  (17,50,196,630),
  (17,34,50,678),
  (17,17,148,646),
  (34,34,34,678),
  (34,50,132,646),
  (17,17,212,630),
  (17,50,50,678),
  (34,50,196,630),
  (34,34,50,678),
  (17,34,148,646),
  (17,67,115,662),
  (50,50,261,550),
  (17,34,212,630),
  (34,50,50,678),
  (17,50,148,646),
  (17,17,67,678),
  (34,34,148,646),
  (17,50,212,630),
  (50,50,50,678),
  (17,17,164,646),
  (17,17,277,550),
  (17,17,309,534),
  (17,17,228,630),
  (34,83,244,614),
  (17,17,83,678),
  (34,67,132,646),
  (17,34,164,646),
  (17,34,277,550),
  (17,34,309,534),
  (17,34,228,630),
  (17,83,196,630),
  (17,34,83,678),
  (17,50,277,550),
  (17,17,99,678),
  (17,50,228,630),
  (34,34,309,534),
  (17,17,180,646),
  (34,83,196,630),
  (34,34,83,678),
  (17,17,244,630)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def smallCheck7 : checkFrom 2669 smallW7 = true := by decide +kernel
set_option maxRecDepth 10000 in
def smallBlock7 (n : ℕ) (hl : 2669 ≤ n) (hu : n < 2797) : Representable n := by
  have h := checkFrom_sound 2669 smallW7 smallCheck7 (n-2669) (by change _ < 128; omega)
  have e : 2669+(n-2669) = n := by omega
  simpa only [e] using h

def smallW8 : List Quad := [(17,34,99,678),
  (34,50,228,630),
  (17,17,115,678),
  (17,34,180,646),
  (50,50,277,550),
  (17,50,99,678),
  (17,34,244,630),
  (17,17,17,694),
  (17,50,180,646),
  (17,34,115,678),
  (17,17,132,662),
  (17,50,244,630),
  (17,17,261,566),
  (17,17,196,646),
  (17,17,34,694),
  (17,17,357,518),
  (34,34,115,678),
  (17,34,132,662),
  (34,50,244,630),
  (17,17,50,694),
  (17,34,196,646),
  (17,34,34,694),
  (17,34,357,518),
  (50,50,244,630),
  (17,50,261,566),
  (17,50,196,646),
  (17,34,50,694),
  (17,17,148,662),
  (34,34,34,694),
  (34,34,357,518),
  (17,17,212,646),
  (17,50,50,694),
  (34,50,196,646),
  (34,34,50,694),
  (17,34,148,662),
  (17,67,115,678),
  (50,50,261,566),
  (17,34,212,646),
  (34,50,50,694),
  (17,50,148,662),
  (17,17,67,694),
  (34,34,148,662),
  (17,50,212,646),
  (50,50,50,694),
  (17,17,164,662),
  (17,17,277,566),
  (17,17,309,550),
  (17,17,228,646),
  (17,17,373,518),
  (17,17,83,694),
  (34,67,132,662),
  (17,34,164,662),
  (17,34,277,566),
  (17,34,309,550),
  (17,34,228,646),
  (17,34,373,518),
  (17,34,83,694),
  (17,50,277,566),
  (17,17,99,694),
  (17,50,228,646),
  (17,50,373,518),
  (17,17,180,662),
  (34,34,373,518),
  (34,34,83,694),
  (17,17,244,646),
  (17,34,99,694),
  (34,50,228,646),
  (17,17,115,694),
  (17,34,180,662),
  (50,50,277,566),
  (17,50,99,694),
  (17,34,244,646),
  (17,17,17,710),
  (17,50,180,662),
  (17,34,115,694),
  (17,17,132,678),
  (17,50,244,646),
  (17,17,261,582),
  (17,17,196,662),
  (17,17,34,710),
  (17,17,357,534),
  (17,17,389,518),
  (17,34,132,678),
  (34,50,244,646),
  (17,17,50,710),
  (17,34,196,662),
  (17,34,34,710),
  (17,34,357,534),
  (17,34,389,518),
  (17,50,261,582),
  (17,50,196,662),
  (17,34,50,710),
  (17,17,148,678),
  (17,50,389,518),
  (34,34,357,534),
  (17,17,212,662),
  (17,50,50,710),
  (34,50,196,662),
  (34,34,50,710),
  (17,34,148,678),
  (34,50,389,518),
  (50,50,261,582),
  (17,34,212,662),
  (34,50,50,710),
  (17,50,148,678),
  (17,17,67,710),
  (34,34,148,678),
  (17,50,212,662),
  (50,50,50,710),
  (17,17,164,678),
  (17,17,277,582),
  (17,17,309,566),
  (17,17,228,662),
  (17,17,373,534),
  (17,17,83,710),
  (34,67,132,678),
  (17,34,164,678),
  (17,34,277,582),
  (17,34,309,566),
  (17,34,228,662),
  (17,34,373,534),
  (17,34,83,710),
  (17,50,277,582),
  (17,17,99,710),
  (17,50,228,662),
  (17,50,373,534),
  (17,17,180,678),
  (34,34,373,534)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def smallCheck8 : checkFrom 2797 smallW8 = true := by decide +kernel
set_option maxRecDepth 10000 in
def smallBlock8 (n : ℕ) (hl : 2797 ≤ n) (hu : n < 2925) : Representable n := by
  have h := checkFrom_sound 2797 smallW8 smallCheck8 (n-2797) (by change _ < 128; omega)
  have e : 2797+(n-2797) = n := by omega
  simpa only [e] using h

def smallW9 : List Quad := [(34,34,83,710),
  (17,17,244,662),
  (17,34,99,710),
  (34,50,228,662),
  (17,17,115,710),
  (17,34,180,678),
  (50,50,277,582),
  (17,50,99,710),
  (17,34,244,662),
  (17,17,17,726),
  (17,50,180,678),
  (17,34,115,710),
  (17,17,132,694),
  (17,50,244,662),
  (17,17,261,598),
  (17,17,196,678),
  (17,17,34,726),
  (17,17,357,550),
  (17,17,389,534),
  (17,17,421,518),
  (34,50,244,662),
  (17,17,50,726),
  (17,34,196,678),
  (17,34,34,726),
  (17,34,357,550),
  (17,34,389,534),
  (17,34,421,518),
  (17,50,196,678),
  (17,34,50,726),
  (17,17,148,694),
  (17,50,389,534),
  (17,50,421,518),
  (17,17,212,678),
  (17,50,50,726),
  (34,50,196,678),
  (34,34,50,726),
  (17,34,148,694),
  (34,50,389,534),
  (34,50,421,518),
  (17,34,212,678),
  (34,50,50,726),
  (17,50,148,694),
  (17,17,67,726),
  (34,34,148,694),
  (17,50,212,678),
  (50,50,50,726),
  (17,17,164,694),
  (17,17,277,598),
  (17,17,309,582),
  (17,17,228,678),
  (17,17,373,550),
  (17,17,83,726),
  (17,17,437,518),
  (17,34,164,694),
  (17,34,277,598),
  (17,34,309,582),
  (17,34,228,678),
  (17,34,373,550),
  (17,34,83,726),
  (17,34,437,518),
  (17,17,99,726),
  (17,50,228,678),
  (17,50,373,550),
  (17,17,180,694),
  (17,50,437,518),
  (34,34,83,726),
  (17,17,244,678),
  (17,34,99,726),
  (34,50,228,678),
  (17,17,115,726),
  (17,34,180,694),
  (34,50,437,518),
  (17,50,99,726),
  (17,34,244,678),
  (17,17,17,742),
  (17,50,180,694),
  (17,34,115,726),
  (17,17,132,710),
  (17,50,244,678),
  (17,17,261,614),
  (17,17,196,694),
  (17,17,34,742),
  (17,17,357,566),
  (17,17,389,550),
  (17,17,421,534),
  (17,17,453,518),
  (17,17,50,742),
  (17,34,196,694),
  (17,34,34,742),
  (17,34,357,566),
  (17,34,389,550),
  (17,34,421,534),
  (17,34,453,518),
  (17,34,50,742),
  (17,17,148,710),
  (17,50,389,550),
  (17,50,421,534),
  (17,17,212,694),
  (17,50,50,742),
  (34,34,453,518),
  (34,34,50,742),
  (17,34,148,710),
  (34,50,389,550),
  (34,50,421,534),
  (17,34,212,694),
  (34,50,50,742),
  (17,50,148,710),
  (17,17,67,742),
  (34,34,148,710),
  (17,50,212,694),
  (50,50,50,742),
  (17,17,164,710),
  (17,17,277,614),
  (17,17,309,598),
  (17,17,228,694),
  (17,17,373,566),
  (17,17,83,742),
  (17,17,437,534),
  (17,17,469,518),
  (17,34,277,614),
  (17,34,309,598),
  (17,34,228,694),
  (17,34,373,566),
  (17,34,83,742),
  (17,34,437,534),
  (17,17,99,742),
  (17,50,228,694),
  (17,50,373,566)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def smallCheck9 : checkFrom 2925 smallW9 = true := by decide +kernel
set_option maxRecDepth 10000 in
def smallBlock9 (n : ℕ) (hl : 2925 ≤ n) (hu : n < 3053) : Representable n := by
  have h := checkFrom_sound 2925 smallW9 smallCheck9 (n-2925) (by change _ < 128; omega)
  have e : 2925+(n-2925) = n := by omega
  simpa only [e] using h

def smallW10 : List Quad := [(17,17,180,710),
  (17,50,437,534),
  (17,50,469,518),
  (17,17,244,694),
  (17,34,99,742),
  (34,50,228,694),
  (17,17,115,742),
  (17,34,180,710),
  (34,50,437,534),
  (17,50,99,742),
  (17,34,244,694),
  (17,17,17,758),
  (17,50,180,710),
  (17,34,115,742),
  (17,17,132,726),
  (17,50,244,694),
  (17,17,261,630),
  (17,17,196,710),
  (17,17,34,758),
  (17,17,357,582),
  (17,17,389,566),
  (17,17,421,550),
  (17,17,453,534),
  (17,17,50,758),
  (17,34,196,710),
  (17,34,34,758),
  (17,34,357,582),
  (17,34,389,566),
  (17,34,421,550),
  (17,34,453,534),
  (17,34,50,758),
  (17,17,148,726),
  (17,50,389,566),
  (17,50,421,550),
  (17,17,212,710),
  (17,50,50,758),
  (34,34,453,534),
  (34,34,50,758),
  (17,34,148,726),
  (34,50,389,566),
  (34,50,421,550),
  (17,34,212,710),
  (34,50,50,758),
  (17,50,148,726),
  (17,17,67,758),
  (34,34,148,726),
  (17,50,212,710),
  (50,50,50,758),
  (17,17,164,726),
  (17,17,277,630),
  (17,17,309,614),
  (17,17,228,710),
  (17,17,373,582),
  (17,17,83,758),
  (17,17,437,550),
  (17,17,469,534),
  (17,17,501,518),
  (17,34,309,614),
  (17,34,228,710),
  (17,34,373,582),
  (17,34,83,758),
  (17,34,437,550),
  (17,17,99,758),
  (17,34,501,518),
  (17,50,373,582),
  (17,17,180,726),
  (17,50,437,550),
  (17,50,469,534),
  (17,17,244,710),
  (17,34,99,758),
  (34,34,501,518),
  (17,17,115,758),
  (17,34,180,726),
  (34,50,437,550),
  (17,50,99,758),
  (17,34,244,710),
  (17,17,17,774),
  (17,50,180,726),
  (17,34,115,758),
  (17,17,132,742),
  (17,50,244,710),
  (17,17,261,646),
  (17,17,196,726),
  (17,17,34,774),
  (17,17,357,598),
  (17,17,389,582),
  (17,17,421,566),
  (17,17,453,550),
  (17,17,50,774),
  (17,34,196,726),
  (17,34,34,774),
  (17,34,357,598),
  (17,34,389,582),
  (17,34,421,566),
  (17,34,453,550),
  (17,34,50,774),
  (17,17,148,742),
  (17,50,389,582),
  (17,50,421,566),
  (17,17,212,726),
  (17,50,50,774),
  (34,34,453,550),
  (34,34,50,774),
  (17,34,148,742),
  (34,50,389,582),
  (34,50,421,566),
  (17,34,212,726),
  (34,50,50,774),
  (17,50,148,742),
  (17,17,67,774),
  (34,34,148,742),
  (17,50,212,726),
  (50,50,50,774),
  (17,17,164,742),
  (17,17,277,646),
  (17,17,309,630),
  (17,17,228,726),
  (17,17,373,598),
  (17,17,83,774),
  (17,17,437,566),
  (17,17,469,550),
  (17,17,501,534),
  (17,34,309,630),
  (17,34,228,726),
  (17,34,373,598),
  (17,34,83,774),
  (17,34,437,566),
  (17,17,99,774)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def smallCheck10 : checkFrom 3053 smallW10 = true := by decide +kernel
set_option maxRecDepth 10000 in
def smallBlock10 (n : ℕ) (hl : 3053 ≤ n) (hu : n < 3181) : Representable n := by
  have h := checkFrom_sound 3053 smallW10 smallCheck10 (n-3053) (by change _ < 128; omega)
  have e : 3053+(n-3053) = n := by omega
  simpa only [e] using h

def smallW11 : List Quad := [(17,34,501,534),
  (17,50,373,598),
  (17,17,180,742),
  (17,50,437,566),
  (17,50,469,550),
  (17,17,244,726),
  (17,34,99,774),
  (34,34,501,534),
  (17,17,115,774),
  (17,34,180,742),
  (34,50,437,566),
  (17,50,99,774),
  (17,34,244,726),
  (17,17,17,790),
  (17,50,180,742),
  (17,34,115,774),
  (17,17,132,758),
  (17,50,244,726),
  (17,17,261,662),
  (17,17,196,742),
  (17,17,34,790),
  (17,17,357,614),
  (17,17,389,598),
  (17,17,421,582),
  (17,17,453,566),
  (17,17,50,790),
  (17,34,196,742),
  (17,34,34,790),
  (17,34,357,614),
  (17,34,389,598),
  (17,34,421,582),
  (17,34,453,566),
  (17,34,50,790),
  (17,17,148,758),
  (17,50,389,598),
  (17,50,421,582),
  (17,17,212,742),
  (17,50,50,790),
  (34,34,453,566),
  (34,34,50,790),
  (17,34,148,758),
  (34,50,389,598),
  (34,50,421,582),
  (17,34,212,742),
  (34,50,50,790),
  (17,50,148,758),
  (17,17,67,790),
  (34,34,148,758),
  (17,50,212,742),
  (50,50,50,790),
  (17,17,164,758),
  (17,17,277,662),
  (17,17,309,646),
  (17,17,228,742),
  (17,17,373,614),
  (17,17,83,790),
  (17,17,437,582),
  (17,17,469,566),
  (17,17,501,550),
  (17,34,309,646),
  (17,34,228,742),
  (17,34,373,614),
  (17,34,83,790),
  (17,34,437,582),
  (17,17,99,790),
  (17,34,501,550),
  (17,50,373,614),
  (17,17,180,758),
  (17,50,437,582),
  (17,50,469,566),
  (17,17,244,742),
  (17,34,99,790),
  (34,34,501,550),
  (17,17,115,790),
  (17,34,180,758),
  (34,50,437,582),
  (17,50,99,790),
  (17,34,244,742),
  (17,17,17,806),
  (17,50,180,758),
  (17,34,115,790),
  (17,17,132,774),
  (17,50,244,742),
  (17,17,261,678),
  (17,17,196,758),
  (17,17,34,806),
  (17,17,357,630),
  (17,17,389,614),
  (17,17,421,598),
  (17,17,453,582),
  (17,17,50,806),
  (17,34,196,758),
  (17,34,34,806),
  (17,34,357,630),
  (17,34,389,614),
  (17,34,421,598),
  (17,34,453,582),
  (17,34,50,806),
  (17,17,148,774),
  (17,50,389,614),
  (17,50,421,598),
  (17,17,212,758),
  (17,50,50,806),
  (34,34,453,582),
  (34,34,50,806),
  (17,34,148,774),
  (34,50,389,614),
  (34,50,421,598),
  (17,34,212,758),
  (34,50,50,806),
  (17,50,148,774),
  (17,17,67,806),
  (34,34,148,774),
  (17,50,212,758),
  (50,50,50,806),
  (17,17,164,774),
  (17,17,277,678),
  (17,17,309,662),
  (17,17,228,758),
  (17,17,373,630),
  (17,17,83,806),
  (17,17,437,598),
  (17,17,469,582),
  (17,17,501,566),
  (17,34,309,662),
  (17,34,228,758),
  (17,34,373,630),
  (17,34,83,806)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def smallCheck11 : checkFrom 3181 smallW11 = true := by decide +kernel
set_option maxRecDepth 10000 in
def smallBlock11 (n : ℕ) (hl : 3181 ≤ n) (hu : n < 3309) : Representable n := by
  have h := checkFrom_sound 3181 smallW11 smallCheck11 (n-3181) (by change _ < 128; omega)
  have e : 3181+(n-3181) = n := by omega
  simpa only [e] using h

def smallW12 : List Quad := [(17,34,437,598),
  (17,17,99,806),
  (17,34,501,566),
  (17,50,373,630),
  (17,17,180,774),
  (17,50,437,598),
  (17,50,469,582),
  (17,17,244,758),
  (17,34,99,806),
  (34,34,501,566),
  (17,17,115,806),
  (17,34,180,774),
  (34,50,437,598),
  (17,50,99,806),
  (17,34,244,758),
  (17,17,17,822),
  (17,50,180,774),
  (17,34,115,806),
  (17,17,132,790),
  (17,50,244,758),
  (17,17,261,694),
  (17,17,196,774),
  (17,17,34,822),
  (17,17,357,646),
  (17,17,389,630),
  (17,17,421,614),
  (17,17,453,598),
  (17,17,50,822),
  (17,34,196,774),
  (17,34,34,822),
  (17,34,357,646),
  (17,34,389,630),
  (17,34,421,614),
  (17,34,453,598),
  (17,34,50,822),
  (17,17,148,790),
  (17,50,389,630),
  (17,50,421,614),
  (17,17,212,774),
  (17,50,50,822),
  (34,34,453,598),
  (34,34,50,822),
  (17,34,148,790),
  (34,50,389,630),
  (34,50,421,614),
  (17,34,212,774),
  (34,50,50,822),
  (17,50,148,790),
  (17,17,67,822),
  (34,34,148,790),
  (17,50,212,774),
  (50,50,50,822),
  (17,17,164,790),
  (17,17,277,694),
  (17,17,309,678),
  (17,17,228,774),
  (17,17,373,646),
  (17,17,83,822),
  (17,17,437,614),
  (17,17,469,598),
  (17,17,501,582),
  (17,34,309,678),
  (17,34,228,774),
  (17,34,373,646),
  (17,34,83,822),
  (17,34,437,614),
  (17,17,99,822),
  (17,34,501,582),
  (17,50,373,646),
  (17,17,180,790),
  (17,50,437,614),
  (17,50,469,598),
  (17,17,244,774),
  (17,34,99,822),
  (34,34,501,582),
  (17,17,115,822),
  (17,34,180,790),
  (34,50,437,614),
  (17,50,99,822),
  (17,34,244,774),
  (17,17,17,838),
  (17,50,180,790),
  (17,34,115,822),
  (17,17,132,806),
  (17,50,244,774),
  (17,17,261,710),
  (17,17,196,790),
  (17,17,34,838),
  (17,17,357,662),
  (17,17,389,646),
  (17,17,421,630),
  (17,17,453,614),
  (17,17,50,838),
  (17,34,196,790),
  (17,34,34,838),
  (17,34,357,662),
  (17,34,389,646),
  (17,34,421,630),
  (17,34,453,614),
  (17,34,50,838),
  (17,17,148,806),
  (17,50,389,646),
  (17,50,421,630),
  (17,17,212,790),
  (17,50,50,838),
  (34,34,453,614),
  (34,34,50,838),
  (17,34,148,806),
  (34,50,389,646),
  (34,50,421,630),
  (17,34,212,790),
  (34,50,50,838),
  (17,50,148,806),
  (17,17,67,838),
  (34,34,148,806),
  (17,50,212,790),
  (50,50,50,838),
  (17,17,164,806),
  (17,17,277,710),
  (17,17,309,694),
  (17,17,228,790),
  (17,17,373,662),
  (17,17,83,838),
  (17,17,437,630),
  (17,17,469,614),
  (17,17,501,598),
  (17,34,309,694),
  (17,34,228,790)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def smallCheck12 : checkFrom 3309 smallW12 = true := by decide +kernel
set_option maxRecDepth 10000 in
def smallBlock12 (n : ℕ) (hl : 3309 ≤ n) (hu : n < 3437) : Representable n := by
  have h := checkFrom_sound 3309 smallW12 smallCheck12 (n-3309) (by change _ < 128; omega)
  have e : 3309+(n-3309) = n := by omega
  simpa only [e] using h

def smallW13 : List Quad := [(17,34,373,662),
  (17,34,83,838),
  (17,34,437,630),
  (17,17,99,838),
  (17,34,501,598),
  (17,50,373,662),
  (17,17,180,806),
  (17,50,437,630),
  (17,50,469,614),
  (17,17,244,790),
  (17,34,99,838),
  (34,34,501,598),
  (17,17,115,838),
  (17,34,180,806),
  (34,50,437,630),
  (17,50,99,838),
  (17,34,244,790),
  (17,17,17,854),
  (17,50,180,806),
  (17,34,115,838),
  (17,17,132,822),
  (17,50,244,790),
  (17,17,261,726),
  (17,17,196,806),
  (17,17,34,854),
  (17,17,357,678),
  (17,17,389,662),
  (17,17,421,646),
  (17,17,453,630),
  (17,17,50,854),
  (17,34,196,806),
  (17,34,34,854),
  (17,34,357,678),
  (17,34,389,662),
  (17,34,421,646),
  (17,34,453,630),
  (17,34,50,854),
  (17,17,148,822),
  (17,50,389,662),
  (17,50,421,646),
  (17,17,212,806),
  (17,50,50,854),
  (34,34,453,630),
  (34,34,50,854),
  (17,34,148,822),
  (34,50,389,662),
  (34,50,421,646),
  (17,34,212,806),
  (34,50,50,854),
  (17,50,148,822),
  (17,17,67,854),
  (34,34,148,822),
  (17,50,212,806),
  (50,50,50,854),
  (17,17,164,822),
  (17,17,277,726),
  (17,17,309,710),
  (17,17,228,806),
  (17,17,373,678),
  (17,17,83,854),
  (17,17,437,646),
  (17,17,469,630),
  (17,17,501,614),
  (17,34,309,710),
  (17,34,228,806),
  (17,34,373,678),
  (17,34,83,854),
  (17,34,437,646),
  (17,17,99,854),
  (17,34,501,614),
  (17,50,373,678),
  (17,17,180,822),
  (17,50,437,646),
  (17,50,469,630),
  (17,17,244,806),
  (17,34,99,854),
  (34,34,501,614),
  (17,17,115,854),
  (17,34,180,822),
  (34,50,437,646),
  (17,50,99,854),
  (17,34,244,806),
  (17,17,17,870),
  (17,50,180,822),
  (17,34,115,854),
  (17,17,132,838),
  (17,50,244,806),
  (17,17,261,742),
  (17,17,196,822),
  (17,17,34,870),
  (17,17,357,694),
  (17,17,389,678),
  (17,17,421,662),
  (17,17,453,646),
  (17,17,50,870),
  (17,34,196,822),
  (17,34,34,870),
  (17,34,357,694),
  (17,34,389,678),
  (17,34,421,662),
  (17,34,453,646),
  (17,34,50,870),
  (17,17,148,838),
  (17,50,389,678),
  (17,50,421,662),
  (17,17,212,822),
  (17,50,50,870),
  (34,34,453,646),
  (34,34,50,870),
  (17,34,148,838),
  (34,50,389,678),
  (34,50,421,662),
  (17,34,212,822),
  (34,50,50,870),
  (17,50,148,838),
  (17,17,67,870),
  (34,34,148,838),
  (17,50,212,822),
  (50,50,50,870),
  (17,17,164,838),
  (17,17,277,742),
  (17,17,309,726),
  (17,17,228,822),
  (17,17,373,694),
  (17,17,83,870),
  (17,17,437,662),
  (17,17,469,646),
  (17,17,501,630)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def smallCheck13 : checkFrom 3437 smallW13 = true := by decide +kernel
set_option maxRecDepth 10000 in
def smallBlock13 (n : ℕ) (hl : 3437 ≤ n) (hu : n < 3565) : Representable n := by
  have h := checkFrom_sound 3437 smallW13 smallCheck13 (n-3437) (by change _ < 128; omega)
  have e : 3437+(n-3437) = n := by omega
  simpa only [e] using h

def smallW14 : List Quad := [(17,34,309,726),
  (17,34,228,822),
  (17,34,373,694),
  (17,34,83,870),
  (17,34,437,662),
  (17,17,99,870),
  (17,34,501,630),
  (17,50,373,694),
  (17,17,180,838),
  (17,50,437,662),
  (17,50,469,646),
  (17,17,244,822),
  (17,34,99,870),
  (34,34,501,630),
  (17,17,115,870),
  (17,34,180,838),
  (34,50,437,662),
  (17,50,99,870),
  (17,34,244,822),
  (17,17,17,886),
  (17,50,180,838),
  (17,34,115,870),
  (17,17,132,854),
  (17,50,244,822),
  (17,17,261,758),
  (17,17,196,838),
  (17,17,34,886),
  (17,17,357,710),
  (17,17,389,694),
  (17,17,421,678),
  (17,17,453,662),
  (17,17,50,886),
  (17,34,196,838),
  (17,34,34,886),
  (17,34,357,710),
  (17,34,389,694),
  (17,34,421,678),
  (17,34,453,662),
  (17,34,50,886),
  (17,17,148,854),
  (17,50,389,694),
  (17,50,421,678),
  (17,17,212,838),
  (17,50,50,886),
  (34,34,453,662),
  (34,34,50,886),
  (17,34,148,854),
  (34,50,389,694),
  (34,50,421,678),
  (17,34,212,838),
  (34,50,50,886),
  (17,50,148,854),
  (17,17,67,886),
  (34,34,148,854),
  (17,50,212,838),
  (50,50,50,886),
  (17,17,164,854),
  (17,17,277,758),
  (17,17,309,742),
  (17,17,228,838),
  (17,17,373,710),
  (17,17,83,886),
  (17,17,437,678),
  (17,17,469,662),
  (17,17,501,646),
  (17,34,309,742),
  (17,34,228,838),
  (17,34,373,710),
  (17,34,83,886),
  (17,34,437,678),
  (17,17,99,886),
  (17,34,501,646),
  (17,50,373,710),
  (17,17,180,854),
  (17,50,437,678),
  (17,50,469,662),
  (17,17,244,838),
  (17,34,99,886),
  (34,34,501,646),
  (17,17,115,886),
  (17,34,180,854),
  (34,50,437,678),
  (17,50,99,886),
  (17,34,244,838),
  (17,17,17,902),
  (17,50,180,854),
  (17,34,115,886),
  (17,17,132,870),
  (17,50,244,838),
  (17,17,261,774),
  (17,17,196,854),
  (17,17,34,902),
  (17,17,357,726),
  (17,17,389,710),
  (17,17,421,694),
  (17,17,453,678),
  (17,17,50,902),
  (17,34,196,854),
  (17,34,34,902),
  (17,34,357,726),
  (17,34,389,710),
  (17,34,421,694),
  (17,34,453,678),
  (17,34,50,902),
  (17,17,148,870),
  (17,50,389,710),
  (17,50,421,694),
  (17,17,212,854),
  (17,50,50,902),
  (34,34,453,678),
  (34,34,50,902),
  (17,34,148,870),
  (34,50,389,710),
  (34,50,421,694),
  (17,34,212,854),
  (34,50,50,902),
  (17,50,148,870),
  (17,17,67,902),
  (34,34,148,870),
  (17,50,212,854),
  (50,50,50,902),
  (17,17,164,870),
  (17,17,277,774),
  (17,17,309,758),
  (17,17,228,854),
  (17,17,373,726),
  (17,17,83,902),
  (17,17,437,694)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def smallCheck14 : checkFrom 3565 smallW14 = true := by decide +kernel
set_option maxRecDepth 10000 in
def smallBlock14 (n : ℕ) (hl : 3565 ≤ n) (hu : n < 3693) : Representable n := by
  have h := checkFrom_sound 3565 smallW14 smallCheck14 (n-3565) (by change _ < 128; omega)
  have e : 3565+(n-3565) = n := by omega
  simpa only [e] using h

def smallW15 : List Quad := [(17,17,469,678),
  (17,17,501,662),
  (17,34,309,758),
  (17,34,228,854),
  (17,34,373,726),
  (17,34,83,902),
  (17,34,437,694),
  (17,17,99,902),
  (17,34,501,662),
  (17,50,373,726),
  (17,17,180,870),
  (17,50,437,694),
  (17,50,469,678),
  (17,17,244,854),
  (17,34,99,902),
  (34,34,501,662),
  (17,17,115,902),
  (17,34,180,870),
  (34,50,437,694),
  (17,50,99,902),
  (17,34,244,854),
  (17,17,17,918),
  (17,50,180,870),
  (17,34,115,902),
  (17,17,132,886),
  (17,50,244,854),
  (17,17,261,790),
  (17,17,196,870),
  (17,17,34,918),
  (17,17,357,742),
  (17,17,389,726),
  (17,17,421,710),
  (17,17,453,694),
  (17,17,50,918),
  (17,34,196,870),
  (17,34,34,918),
  (17,34,357,742),
  (17,34,389,726),
  (17,34,421,710),
  (17,34,453,694),
  (17,34,50,918),
  (17,17,148,886),
  (17,50,389,726),
  (17,50,421,710),
  (17,17,212,870),
  (17,50,50,918),
  (34,34,453,694),
  (34,34,50,918),
  (17,34,148,886),
  (34,50,389,726),
  (34,50,421,710),
  (17,34,212,870),
  (34,50,50,918),
  (17,50,148,886),
  (17,17,67,918),
  (34,34,148,886),
  (17,50,212,870),
  (50,50,50,918),
  (17,17,164,886),
  (17,17,277,790),
  (17,17,309,774),
  (17,17,228,870),
  (17,17,373,742),
  (17,17,83,918),
  (17,17,437,710),
  (17,17,469,694),
  (17,17,501,678),
  (17,34,309,774),
  (17,34,228,870),
  (17,34,373,742),
  (17,34,83,918),
  (17,34,437,710),
  (17,17,99,918),
  (17,34,501,678),
  (17,50,373,742),
  (17,17,180,886),
  (17,50,437,710),
  (17,50,469,694),
  (17,17,244,870),
  (17,34,99,918),
  (34,34,501,678),
  (17,17,115,918),
  (17,34,180,886),
  (34,50,437,710),
  (17,50,99,918),
  (17,34,244,870),
  (17,17,17,934),
  (17,50,180,886),
  (17,34,115,918),
  (17,17,132,902),
  (17,50,244,870),
  (17,17,261,806),
  (17,17,196,886),
  (17,17,34,934),
  (17,17,357,758),
  (17,17,389,742),
  (17,17,421,726),
  (17,17,453,710),
  (17,17,50,934),
  (17,34,196,886),
  (17,34,34,934),
  (17,34,357,758),
  (17,34,389,742),
  (17,34,421,726),
  (17,34,453,710),
  (17,34,50,934),
  (17,17,148,902),
  (17,50,389,742),
  (17,50,421,726),
  (17,17,212,886),
  (17,50,50,934),
  (34,34,453,710),
  (34,34,50,934),
  (17,34,148,902),
  (34,50,389,742),
  (34,50,421,726),
  (17,34,212,886),
  (34,50,50,934),
  (17,50,148,902),
  (17,17,67,934),
  (34,34,148,902),
  (17,50,212,886),
  (50,50,50,934),
  (17,17,164,902),
  (17,17,277,806),
  (17,17,309,790),
  (17,17,228,886),
  (17,17,373,758)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def smallCheck15 : checkFrom 3693 smallW15 = true := by decide +kernel
set_option maxRecDepth 10000 in
def smallBlock15 (n : ℕ) (hl : 3693 ≤ n) (hu : n < 3821) : Representable n := by
  have h := checkFrom_sound 3693 smallW15 smallCheck15 (n-3693) (by change _ < 128; omega)
  have e : 3693+(n-3693) = n := by omega
  simpa only [e] using h

def smallW16 : List Quad := [(17,17,83,934),
  (17,17,437,726),
  (17,17,469,710),
  (17,17,501,694),
  (17,34,309,790),
  (17,34,228,886),
  (17,34,373,758),
  (17,34,83,934),
  (17,34,437,726),
  (17,17,99,934),
  (17,34,501,694),
  (17,50,373,758),
  (17,17,180,902),
  (17,50,437,726),
  (17,50,469,710),
  (17,17,244,886),
  (17,34,99,934),
  (34,34,501,694),
  (17,17,115,934),
  (17,34,180,902),
  (34,50,437,726),
  (17,50,99,934),
  (17,34,244,886),
  (17,17,17,950),
  (17,50,180,902),
  (17,34,115,934),
  (17,17,132,918),
  (17,50,244,886),
  (17,17,261,822),
  (17,17,196,902),
  (17,17,34,950),
  (17,17,357,774),
  (17,17,389,758),
  (17,17,421,742),
  (17,17,453,726),
  (17,17,50,950),
  (17,34,196,902),
  (17,34,34,950),
  (17,34,357,774),
  (17,34,389,758),
  (17,34,421,742),
  (17,34,453,726),
  (17,34,50,950),
  (17,17,148,918),
  (17,50,389,758),
  (17,50,421,742),
  (17,17,212,902),
  (17,50,50,950),
  (34,34,453,726),
  (34,34,50,950),
  (17,34,148,918),
  (34,50,389,758),
  (34,50,421,742),
  (17,34,212,902),
  (34,50,50,950),
  (17,50,148,918),
  (17,17,67,950),
  (34,34,148,918),
  (17,50,212,902),
  (50,50,50,950),
  (17,17,164,918),
  (17,17,277,822),
  (17,17,309,806),
  (17,17,228,902),
  (17,17,373,774),
  (17,17,83,950),
  (17,17,437,742),
  (17,17,469,726),
  (17,17,501,710),
  (17,34,309,806),
  (17,34,228,902),
  (17,34,373,774),
  (17,34,83,950),
  (17,34,437,742),
  (17,17,99,950),
  (17,34,501,710),
  (17,50,373,774),
  (17,17,180,918),
  (17,50,437,742),
  (17,50,469,726),
  (17,17,244,902),
  (17,34,99,950),
  (34,34,501,710),
  (17,17,115,950),
  (17,34,180,918),
  (34,50,437,742),
  (17,50,99,950),
  (17,34,244,902),
  (17,17,17,966),
  (17,50,180,918),
  (17,34,115,950),
  (17,17,132,934),
  (17,50,244,902),
  (17,17,261,838),
  (17,17,196,918),
  (17,17,34,966),
  (17,17,357,790),
  (17,17,389,774),
  (17,17,421,758),
  (17,17,453,742),
  (17,17,50,966),
  (17,34,196,918),
  (17,34,34,966),
  (17,34,357,790),
  (17,34,389,774),
  (17,34,421,758),
  (17,34,453,742),
  (17,34,50,966),
  (17,17,148,934),
  (17,50,389,774),
  (17,50,421,758),
  (17,17,212,918),
  (17,50,50,966),
  (34,34,453,742),
  (34,34,50,966),
  (17,34,148,934),
  (34,50,389,774),
  (34,50,421,758),
  (17,34,212,918),
  (34,50,50,966),
  (17,50,148,934),
  (17,17,67,966),
  (34,34,148,934),
  (17,50,212,918),
  (50,50,50,966),
  (17,17,164,934),
  (17,17,277,838),
  (17,17,309,822)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def smallCheck16 : checkFrom 3821 smallW16 = true := by decide +kernel
set_option maxRecDepth 10000 in
def smallBlock16 (n : ℕ) (hl : 3821 ≤ n) (hu : n < 3949) : Representable n := by
  have h := checkFrom_sound 3821 smallW16 smallCheck16 (n-3821) (by change _ < 128; omega)
  have e : 3821+(n-3821) = n := by omega
  simpa only [e] using h

def smallW17 : List Quad := [(17,17,228,918),
  (17,17,373,790),
  (17,17,83,966),
  (17,17,437,758),
  (17,17,469,742),
  (17,17,501,726),
  (17,34,309,822),
  (17,34,228,918),
  (17,34,373,790),
  (17,34,83,966),
  (17,34,437,758),
  (17,17,99,966),
  (17,34,501,726),
  (17,50,373,790),
  (17,17,180,934),
  (17,50,437,758),
  (17,50,469,742),
  (17,17,244,918),
  (17,34,99,966),
  (34,34,501,726),
  (17,17,115,966),
  (17,34,180,934),
  (34,50,437,758),
  (17,50,99,966),
  (17,34,244,918),
  (17,17,17,982),
  (17,50,180,934),
  (17,34,115,966),
  (17,17,132,950),
  (17,50,244,918),
  (17,17,261,854),
  (17,17,196,934),
  (17,17,34,982),
  (17,17,357,806),
  (17,17,389,790),
  (17,17,421,774),
  (17,17,453,758),
  (17,17,50,982),
  (17,34,196,934),
  (17,34,34,982),
  (17,34,357,806),
  (17,34,389,790),
  (17,34,421,774),
  (17,34,453,758),
  (17,34,50,982),
  (17,17,148,950),
  (17,50,389,790),
  (17,50,421,774),
  (17,17,212,934),
  (17,50,50,982),
  (34,34,453,758),
  (34,34,50,982),
  (17,34,148,950),
  (34,50,389,790),
  (34,50,421,774),
  (17,34,212,934),
  (34,50,50,982),
  (17,50,148,950),
  (17,17,67,982),
  (34,34,148,950),
  (17,50,212,934),
  (50,50,50,982),
  (17,17,164,950),
  (17,17,277,854),
  (17,17,309,838),
  (17,17,228,934),
  (17,17,373,806),
  (17,17,83,982),
  (17,17,437,774),
  (17,17,469,758),
  (17,17,501,742),
  (17,34,309,838),
  (17,34,228,934),
  (17,34,373,806),
  (17,34,83,982),
  (17,34,437,774),
  (17,17,99,982),
  (17,34,501,742),
  (17,50,373,806),
  (17,17,180,950),
  (17,50,437,774),
  (17,50,469,758),
  (17,17,244,934),
  (17,34,99,982),
  (34,34,501,742),
  (17,17,115,982),
  (17,34,180,950),
  (34,50,437,774),
  (17,50,99,982),
  (17,34,244,934),
  (17,17,17,998),
  (17,50,180,950),
  (17,34,115,982),
  (17,17,132,966),
  (17,50,244,934),
  (17,17,261,870),
  (17,17,196,950),
  (17,17,34,998),
  (17,17,357,822),
  (17,17,389,806),
  (17,17,421,790),
  (17,17,453,774),
  (17,17,50,998),
  (17,34,196,950),
  (17,34,34,998),
  (17,34,357,822),
  (17,34,389,806),
  (17,34,421,790),
  (17,34,453,774),
  (17,34,50,998),
  (17,17,148,966),
  (17,50,389,806),
  (17,50,421,790),
  (17,17,212,950),
  (17,50,50,998),
  (34,34,453,774),
  (34,34,50,998),
  (17,34,148,966),
  (34,50,389,806),
  (34,50,421,790),
  (17,34,212,950),
  (34,50,50,998),
  (17,50,148,966),
  (17,17,67,998),
  (34,34,148,966),
  (17,50,212,950),
  (50,50,50,998),
  (17,17,164,966)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def smallCheck17 : checkFrom 3949 smallW17 = true := by decide +kernel
set_option maxRecDepth 10000 in
def smallBlock17 (n : ℕ) (hl : 3949 ≤ n) (hu : n < 4077) : Representable n := by
  have h := checkFrom_sound 3949 smallW17 smallCheck17 (n-3949) (by change _ < 128; omega)
  have e : 3949+(n-3949) = n := by omega
  simpa only [e] using h

def smallW18 : List Quad := [(17,17,277,870),
  (17,17,309,854),
  (17,17,228,950),
  (17,17,373,822),
  (17,17,83,998),
  (17,17,437,790),
  (17,17,469,774),
  (17,17,501,758),
  (17,34,309,854),
  (17,34,228,950),
  (17,34,373,822),
  (17,34,83,998),
  (17,34,437,790),
  (17,17,99,998),
  (17,34,501,758),
  (17,50,373,822),
  (17,17,180,966),
  (17,50,437,790),
  (17,50,469,774)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def smallCheck18 : checkFrom 4077 smallW18 = true := by decide +kernel
set_option maxRecDepth 10000 in
def smallBlock18 (n : ℕ) (hl : 4077 ≤ n) (hu : n < 4096) : Representable n := by
  have h := checkFrom_sound 4077 smallW18 smallCheck18 (n-4077) (by change _ < 19; omega)
  have e : 4077+(n-4077) = n := by omega
  simpa only [e] using h

def represent_small (n : ℕ) (hn : 1772 < n) (hu : n < 4096) : Representable n := by
  by_cases h0 : n < 1901
  · exact smallBlock0 n (by omega) h0
  by_cases h1 : n < 2029
  · exact smallBlock1 n (by omega) h1
  by_cases h2 : n < 2157
  · exact smallBlock2 n (by omega) h2
  by_cases h3 : n < 2285
  · exact smallBlock3 n (by omega) h3
  by_cases h4 : n < 2413
  · exact smallBlock4 n (by omega) h4
  by_cases h5 : n < 2541
  · exact smallBlock5 n (by omega) h5
  by_cases h6 : n < 2669
  · exact smallBlock6 n (by omega) h6
  by_cases h7 : n < 2797
  · exact smallBlock7 n (by omega) h7
  by_cases h8 : n < 2925
  · exact smallBlock8 n (by omega) h8
  by_cases h9 : n < 3053
  · exact smallBlock9 n (by omega) h9
  by_cases h10 : n < 3181
  · exact smallBlock10 n (by omega) h10
  by_cases h11 : n < 3309
  · exact smallBlock11 n (by omega) h11
  by_cases h12 : n < 3437
  · exact smallBlock12 n (by omega) h12
  by_cases h13 : n < 3565
  · exact smallBlock13 n (by omega) h13
  by_cases h14 : n < 3693
  · exact smallBlock14 n (by omega) h14
  by_cases h15 : n < 3821
  · exact smallBlock15 n (by omega) h15
  by_cases h16 : n < 3949
  · exact smallBlock16 n (by omega) h16
  by_cases h17 : n < 4077
  · exact smallBlock17 n (by omega) h17
  exact smallBlock18 n (by omega) hu

def exW0 : List (ℕ × Quad) := [(5897,(132,277,518,774)),
  (5930,(99,212,518,886)),
  (5962,(132,277,518,790)),
  (5995,(99,212,518,902)),
  (6027,(132,277,518,806)),
  (6060,(99,212,518,918)),
  (6092,(132,277,518,822)),
  (6125,(99,212,518,934)),
  (6157,(132,277,518,838)),
  (6190,(99,212,518,950)),
  (6222,(132,277,518,854)),
  (6239,(34,99,518,1014)),
  (6255,(99,212,518,966)),
  (6287,(132,277,518,870)),
  (6304,(34,99,534,1014)),
  (6320,(99,212,518,982)),
  (6352,(132,277,518,886)),
  (6369,(34,99,550,1014)),
  (6385,(99,212,518,998)),
  (6417,(132,277,518,902)),
  (6434,(34,99,566,1014)),
  (6450,(99,212,518,1014)),
  (6482,(132,277,518,918)),
  (6499,(34,99,582,1014)),
  (6515,(99,212,534,1014)),
  (6547,(132,277,518,934)),
  (6564,(34,99,598,1014)),
  (6580,(99,212,550,1014)),
  (6612,(132,277,518,950)),
  (6629,(34,99,614,1014)),
  (6645,(99,212,566,1014)),
  (6677,(132,277,518,966)),
  (6694,(34,99,630,1014)),
  (6710,(99,212,582,1014)),
  (6742,(132,277,518,982)),
  (6759,(34,99,646,1014)),
  (6775,(99,212,598,1014)),
  (6807,(132,277,518,998)),
  (6824,(34,99,662,1014)),
  (6840,(99,212,614,1014)),
  (6872,(132,277,518,1014)),
  (6889,(34,99,678,1014)),
  (6905,(99,212,630,1014)),
  (6937,(132,277,534,1014)),
  (6954,(34,99,694,1014)),
  (6970,(99,212,646,1014)),
  (7002,(132,277,550,1014)),
  (7019,(34,99,710,1014)),
  (7035,(99,212,662,1014)),
  (7067,(132,277,566,1014)),
  (7084,(34,99,726,1014)),
  (7100,(99,212,678,1014)),
  (7132,(132,277,582,1014)),
  (7149,(34,99,742,1014)),
  (7165,(99,212,694,1014)),
  (7214,(34,99,758,1014)),
  (7279,(34,99,774,1014)),
  (7344,(34,99,790,1014)),
  (7409,(34,99,806,1014)),
  (7474,(34,99,822,1014)),
  (7539,(34,99,838,1014)),
  (7604,(34,99,854,1014)),
  (7669,(34,99,870,1014)),
  (7734,(34,99,886,1014)),
  (7799,(34,99,902,1014)),
  (7864,(34,99,918,1014)),
  (7929,(34,99,934,1014)),
  (7994,(34,99,950,1014)),
  (8059,(34,99,966,1014)),
  (8124,(34,99,982,1014)),
  (8189,(34,99,998,1014)),
  (8254,(34,99,1014,1014)),
  (8319,(17,50,83,1031)),
  (8384,(99,325,886,1014)),
  (8449,(17,17,180,1031)),
  (8514,(34,34,228,1031)),
  (8579,(34,34,83,1063)),
  (8644,(34,83,196,1047)),
  (8709,(34,50,164,1063)),
  (8774,(17,67,212,1063)),
  (8839,(17,34,99,1095)),
  (8904,(17,17,244,1079)),
  (8969,(34,34,341,1031)),
  (9002,(34,34,357,1031)),
  (9034,(34,83,293,1047)),
  (9035,(34,34,373,1031)),
  (9067,(17,34,148,1111)),
  (9068,(34,34,389,1031)),
  (9099,(17,17,115,1127)),
  (9100,(34,50,83,1127)),
  (9101,(17,34,180,1111)),
  (9132,(17,50,421,1031)),
  (9133,(34,50,293,1063)),
  (9134,(34,34,421,1031)),
  (9164,(34,34,373,1047)),
  (9165,(17,50,437,1031)),
  (9166,(34,50,309,1063)),
  (9167,(34,34,437,1031)),
  (9197,(34,34,389,1047)),
  (9198,(17,50,453,1031)),
  (9199,(34,50,50,1143)),
  (9200,(34,34,453,1031)),
  (9229,(34,50,83,1143)),
  (9230,(17,34,180,1127)),
  (9231,(17,50,99,1143)),
  (9232,(34,50,341,1063)),
  (9233,(34,34,99,1143)),
  (9262,(34,50,293,1079)),
  (9263,(34,34,421,1047)),
  (9264,(17,34,212,1127)),
  (9265,(34,50,357,1063)),
  (9266,(34,34,485,1031)),
  (9295,(34,50,309,1079)),
  (9296,(34,34,437,1047)),
  (9297,(17,17,17,1159)),
  (9298,(17,34,244,1127)),
  (9299,(34,34,501,1031)),
  (9311,(17,34,34,1159)),
  (9328,(34,50,50,1159)),
  (9329,(34,34,453,1047)),
  (9330,(17,17,67,1159)),
  (9331,(34,50,389,1063)),
  (9332,(34,34,148,1143)),
  (9344,(34,34,67,1159)),
  (9361,(34,50,341,1079)),
  (9362,(34,34,99,1159)),
  (9363,(50,50,83,1159)),
  (9364,(17,34,115,1159))]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def exCheck0 : checkTagged exW0 = true := by decide +kernel

def exW1 : List (ℕ × Quad) := [(9365,(50,164,453,1031)),
  (9377,(17,83,164,1143)),
  (9394,(34,50,357,1079)),
  (9395,(34,34,485,1047)),
  (9396,(50,50,293,1095)),
  (9397,(34,50,421,1063)),
  (9398,(17,50,212,1143)),
  (9399,(50,50,357,1079)),
  (9410,(17,34,228,1143)),
  (9427,(17,34,244,1143)),
  (9428,(34,34,501,1047)),
  (9429,(50,50,309,1095)),
  (9430,(17,17,132,1159)),
  (9431,(50,67,212,1143)),
  (9432,(17,50,244,1143)),
  (9443,(34,67,228,1143)),
  (9460,(34,50,389,1079)),
  (9461,(34,34,148,1159)),
  (9462,(50,50,50,1175)),
  (9463,(34,50,453,1063)),
  (9464,(17,17,164,1159)),
  (9476,(17,50,164,1159)),
  (9493,(17,34,115,1175)),
  (9494,(50,164,453,1047)),
  (9495,(34,34,180,1159)),
  (9496,(34,50,99,1175)),
  (9509,(50,67,164,1159)),
  (9526,(34,50,421,1079)),
  (9527,(17,50,212,1159)),
  (9528,(50,50,357,1095)),
  (9542,(17,164,357,1079)),
  (9559,(17,17,132,1175)),
  (9560,(50,67,212,1159)),
  (9561,(17,50,244,1159)),
  (9575,(17,115,212,1159)),
  (9591,(50,50,50,1191)),
  (9592,(34,50,453,1079)),
  (9593,(17,17,164,1175)),
  (9607,(17,34,341,1111)),
  (9608,(34,83,132,1175)),
  (9623,(50,164,453,1063)),
  (9624,(34,34,180,1175)),
  (9625,(34,50,99,1191)),
  (9639,(17,17,485,1079)),
  (9640,(17,34,357,1111)),
  (9641,(34,34,196,1175)),
  (9655,(34,50,421,1095)),
  (9656,(17,50,212,1175)),
  (9657,(50,50,357,1111)),
  (9671,(17,164,357,1095)),
  (9672,(17,17,501,1079)),
  (9673,(17,34,373,1111)),
  (9688,(17,17,132,1191)),
  (9689,(50,67,212,1175)),
  (9690,(17,50,244,1175)),
  (9704,(17,115,212,1175)),
  (9705,(17,17,148,1191)),
  (9706,(17,34,389,1111)),
  (9720,(50,50,50,1207)),
  (9721,(34,50,453,1095)),
  (9722,(17,17,164,1191)),
  (9736,(17,34,341,1127)),
  (9737,(34,83,132,1191)),
  (9738,(17,50,83,1207)),
  (9752,(50,164,453,1079)),
  (9753,(34,34,180,1191)),
  (9754,(34,50,99,1207)),
  (9768,(17,17,485,1095)),
  (9769,(17,34,357,1127)),
  (9770,(34,34,196,1191)),
  (9784,(34,50,421,1111)),
  (9785,(17,50,212,1191)),
  (9786,(50,50,357,1127)),
  (9800,(17,164,357,1111)),
  (9801,(17,17,501,1095)),
  (9802,(17,34,373,1127)),
  (9817,(17,17,132,1207)),
  (9818,(50,67,212,1191)),
  (9819,(17,50,244,1191)),
  (9833,(17,115,212,1191)),
  (9834,(17,17,148,1207)),
  (9835,(17,34,389,1127)),
  (9849,(50,50,50,1223)),
  (9850,(34,50,453,1111)),
  (9851,(17,17,164,1207)),
  (9865,(17,34,341,1143)),
  (9866,(34,83,132,1207)),
  (9867,(17,50,83,1223)),
  (9881,(50,164,453,1095)),
  (9882,(34,34,180,1207)),
  (9883,(34,50,99,1223)),
  (9898,(17,34,357,1143)),
  (9899,(34,34,196,1207)),
  (9914,(17,50,212,1207)),
  (9915,(50,50,357,1143)),
  (9931,(17,34,373,1143)),
  (9947,(50,67,212,1207)),
  (9948,(17,50,244,1207)),
  (9964,(17,34,389,1143)),
  (9980,(17,17,164,1223)),
  (35861,(17,50,437,2184)),
  (35926,(34,67,614,2088)),
  (35991,(17,34,244,2232)),
  (36055,(50,50,83,2248)),
  (36056,(17,34,115,2248)),
  (36119,(50,132,373,2200)),
  (36120,(34,34,437,2200)),
  (36121,(34,67,662,2088)),
  (36184,(17,50,469,2200)),
  (36185,(17,50,180,2248)),
  (36186,(34,34,469,2200)),
  (36248,(17,34,244,2248)),
  (36249,(17,83,212,2248)),
  (36250,(17,50,501,2200)),
  (36251,(34,67,694,2088)),
  (36313,(17,34,115,2264)),
  (36314,(50,50,277,2232)),
  (36315,(17,67,838,2056)),
  (36316,(34,50,99,2264)),
  (36377,(34,34,437,2216)),
  (36378,(34,67,662,2104)),
  (36379,(17,17,132,2264)),
  (36380,(50,50,309,2232)),
  (36381,(34,67,726,2088)),
  (36442,(17,50,180,2264)),
  (36443,(34,34,469,2216)),
  (36444,(34,34,180,2264)),
  (36445,(17,67,870,2056))]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def exCheck1 : checkTagged exW1 = true := by decide +kernel

def exW2 : List (ℕ × Quad) := [(36446,(50,50,341,2232)),
  (36506,(17,83,212,2264)),
  (36507,(17,50,501,2216)),
  (36508,(34,67,694,2104)),
  (36509,(34,34,501,2216)),
  (36510,(17,17,34,2280)),
  (36511,(34,67,758,2088)),
  (36571,(50,50,277,2248)),
  (36572,(17,67,838,2072)),
  (36573,(34,50,99,2280)),
  (36574,(17,115,261,2248)),
  (36575,(17,50,115,2280)),
  (36576,(34,67,67,2280)),
  (36635,(34,67,662,2120)),
  (36636,(17,17,132,2280)),
  (36637,(50,50,309,2248)),
  (36638,(34,67,726,2104)),
  (36639,(34,50,437,2232)),
  (36640,(17,67,918,2056)),
  (36641,(34,67,790,2088)),
  (36700,(34,34,469,2232)),
  (36701,(34,34,180,2280)),
  (36702,(17,67,870,2072)),
  (36703,(50,50,341,2248)),
  (36704,(17,17,196,2280)),
  (36705,(34,50,469,2232)),
  (36706,(34,50,180,2280)),
  (36764,(17,50,501,2232)),
  (36765,(34,67,694,2120)),
  (36766,(34,34,501,2232)),
  (36767,(17,17,34,2296)),
  (36768,(34,67,758,2104)),
  (36769,(34,34,244,2280)),
  (36770,(17,67,950,2056)),
  (36771,(17,17,261,2264)),
  (36829,(17,67,838,2088)),
  (36830,(34,50,99,2296)),
  (36831,(17,115,261,2264)),
  (36832,(17,50,115,2296)),
  (36833,(34,67,67,2296)),
  (36834,(34,34,115,2296)),
  (36835,(50,50,99,2296)),
  (36836,(34,67,838,2088)),
  (36893,(17,17,132,2296)),
  (36894,(50,50,309,2264)),
  (36895,(34,67,726,2120)),
  (36896,(34,50,437,2248)),
  (36897,(17,67,918,2072)),
  (36898,(34,67,790,2104)),
  (36899,(50,148,950,2056)),
  (36900,(17,34,132,2296)),
  (36901,(50,50,437,2248)),
  (36958,(34,34,180,2296)),
  (36959,(17,67,870,2088)),
  (36960,(50,50,341,2264)),
  (36961,(17,17,196,2296)),
  (36962,(34,50,469,2248)),
  (36963,(34,50,180,2296)),
  (36964,(50,83,148,2296)),
  (36965,(17,67,998,2056)),
  (36966,(34,67,870,2088)),
  (37023,(34,34,501,2248)),
  (37024,(17,17,34,2312)),
  (37025,(34,67,758,2120)),
  (37026,(34,34,244,2296)),
  (37027,(17,67,950,2072)),
  (37028,(17,17,261,2280)),
  (37029,(17,17,50,2312)),
  (37030,(17,67,1014,2056)),
  (37031,(17,34,34,2312)),
  (37055,(34,34,582,2168)),
  (37088,(17,115,261,2280)),
  (37089,(17,50,115,2312)),
  (37090,(34,67,67,2312)),
  (37091,(34,34,115,2312)),
  (37092,(50,50,99,2312)),
  (37093,(34,67,838,2104)),
  (37094,(17,17,293,2280)),
  (37095,(17,83,838,2104)),
  (37096,(34,50,115,2312)),
  (37120,(34,34,598,2168)),
  (37153,(34,50,437,2264)),
  (37154,(17,67,918,2088)),
  (37155,(34,67,790,2120)),
  (37156,(50,148,950,2072)),
  (37157,(17,34,132,2312)),
  (37158,(50,50,437,2264)),
  (37159,(34,99,421,2264)),
  (37160,(17,17,325,2280)),
  (37161,(34,67,918,2088)),
  (37185,(34,34,614,2168)),
  (37218,(17,17,196,2312)),
  (37219,(34,50,469,2264)),
  (37220,(34,50,180,2312)),
  (37221,(50,83,148,2312)),
  (37222,(17,67,998,2072)),
  (37223,(34,67,870,2104)),
  (37224,(50,50,469,2264)),
  (37225,(17,34,196,2312)),
  (37250,(34,34,630,2168)),
  (37283,(34,34,244,2312)),
  (37284,(17,67,950,2088)),
  (37285,(17,17,261,2296)),
  (37286,(17,17,50,2328)),
  (37287,(17,67,1014,2072)),
  (37288,(17,34,34,2328)),
  (37289,(50,83,212,2312)),
  (37290,(50,50,501,2264)),
  (37315,(34,34,646,2168)),
  (37348,(34,34,115,2328)),
  (37349,(50,50,99,2328)),
  (37350,(34,67,838,2120)),
  (37351,(17,17,293,2296)),
  (37352,(17,83,838,2120)),
  (37353,(34,50,115,2328)),
  (37354,(83,115,228,2312)),
  (37380,(34,34,662,2168)),
  (37413,(50,148,950,2088)),
  (37414,(17,34,132,2328)),
  (37415,(50,50,437,2280)),
  (37416,(34,99,421,2280)),
  (37417,(17,17,325,2296)),
  (37418,(34,67,918,2104)),
  (37445,(34,34,678,2168)),
  (37478,(50,83,148,2328)),
  (37479,(17,67,998,2088)),
  (37480,(34,67,870,2120)),
  (37481,(50,50,469,2280))]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def exCheck2 : checkTagged exW2 = true := by decide +kernel

def exW3 : List (ℕ × Quad) := [(37482,(17,34,196,2328)),
  (37510,(34,34,694,2168)),
  (37543,(17,17,50,2344)),
  (37544,(17,67,1014,2088)),
  (37545,(17,34,34,2344)),
  (37546,(50,83,212,2328)),
  (37547,(50,50,501,2280)),
  (37575,(17,17,277,2312)),
  (37608,(17,17,293,2312)),
  (37609,(17,83,838,2136)),
  (37610,(34,50,115,2344)),
  (37611,(83,115,228,2328)),
  (37640,(34,34,726,2168)),
  (37673,(34,99,421,2296)),
  (37674,(17,17,325,2312)),
  (37675,(34,67,918,2120)),
  (37705,(17,34,164,2344)),
  (37738,(50,50,469,2296)),
  (37739,(17,34,196,2344)),
  (37770,(34,34,758,2168)),
  (37803,(50,83,212,2344)),
  (37804,(50,50,501,2296)),
  (37835,(34,34,67,2360)),
  (37868,(83,115,228,2344)),
  (37900,(34,34,790,2168))]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def exCheck3 : checkTagged exW3 = true := by decide +kernel

def exceptionNumbers : List ℕ := [5897,5930,5962,5995,6027,6060,6092,6125,6157,6190,6222,6239,6255,6287,6304,6320,6352,6369,6385,6417,6434,6450,6482,6499,6515,6547,6564,6580,6612,6629,6645,6677,6694,6710,6742,6759,6775,6807,6824,6840,6872,6889,6905,6937,6954,6970,7002,7019,7035,7067,7084,7100,7132,7149,7165,7214,7279,7344,7409,7474,7539,7604,7669,7734,7799,7864,7929,7994,8059,8124,8189,8254,8319,8384,8449,8514,8579,8644,8709,8774,8839,8904,8969,9002,9034,9035,9067,9068,9099,9100,9101,9132,9133,9134,9164,9165,9166,9167,9197,9198,9199,9200,9229,9230,9231,9232,9233,9262,9263,9264,9265,9266,9295,9296,9297,9298,9299,9311,9328,9329,9330,9331,9332,9344,9361,9362,9363,9364,9365,9377,9394,9395,9396,9397,9398,9399,9410,9427,9428,9429,9430,9431,9432,9443,9460,9461,9462,9463,9464,9476,9493,9494,9495,9496,9509,9526,9527,9528,9542,9559,9560,9561,9575,9591,9592,9593,9607,9608,9623,9624,9625,9639,9640,9641,9655,9656,9657,9671,9672,9673,9688,9689,9690,9704,9705,9706,9720,9721,9722,9736,9737,9738,9752,9753,9754,9768,9769,9770,9784,9785,9786,9800,9801,9802,9817,9818,9819,9833,9834,9835,9849,9850,9851,9865,9866,9867,9881,9882,9883,9898,9899,9914,9915,9931,9947,9948,9964,9980,35861,35926,35991,36055,36056,36119,36120,36121,36184,36185,36186,36248,36249,36250,36251,36313,36314,36315,36316,36377,36378,36379,36380,36381,36442,36443,36444,36445,36446,36506,36507,36508,36509,36510,36511,36571,36572,36573,36574,36575,36576,36635,36636,36637,36638,36639,36640,36641,36700,36701,36702,36703,36704,36705,36706,36764,36765,36766,36767,36768,36769,36770,36771,36829,36830,36831,36832,36833,36834,36835,36836,36893,36894,36895,36896,36897,36898,36899,36900,36901,36958,36959,36960,36961,36962,36963,36964,36965,36966,37023,37024,37025,37026,37027,37028,37029,37030,37031,37055,37088,37089,37090,37091,37092,37093,37094,37095,37096,37120,37153,37154,37155,37156,37157,37158,37159,37160,37161,37185,37218,37219,37220,37221,37222,37223,37224,37225,37250,37283,37284,37285,37286,37287,37288,37289,37290,37315,37348,37349,37350,37351,37352,37353,37354,37380,37413,37414,37415,37416,37417,37418,37445,37478,37479,37480,37481,37482,37510,37543,37544,37545,37546,37547,37575,37608,37609,37610,37611,37640,37673,37674,37675,37705,37738,37739,37770,37803,37804,37835,37868,37900]

def checkTagged_append (xs ys : List (ℕ × Quad)) :
    checkTagged (xs++ys) = (checkTagged xs && checkTagged ys) := by
  simp only [checkTagged, List.all_append]

set_option maxRecDepth 10000 in
def represent_exception (n : ℕ) (hn : n ∈ exceptionNumbers) : Representable n := by
  have he : exceptionNumbers = (exW0 ++ exW1 ++ exW2 ++ exW3).map Prod.fst := by rfl
  rw [he] at hn
  have hc : checkTagged (exW0 ++ exW1 ++ exW2 ++ exW3) = true := by
    rw [checkTagged_append,checkTagged_append,checkTagged_append,
      exCheck0,exCheck1,exCheck2,exCheck3]
    rfl
  exact checkTagged_sound _ hc n hn

end A343268Proof

-- Component: A343268Middle

namespace A343268Proof
set_option maxRecDepth 10000 in
def middle_4_0_0 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+0)+0 : ℤ).toNat) := by
  by_cases h0 : q≤148
  ·
    exact four_is_representable 2 _ (c0_9_sound 4 q 0 (by norm_num) (by unfold c0_9; omega))
  by_cases h1 : q≤174
  ·
    exact four_is_representable 2 _ (c0_10_sound 4 q 0 (by norm_num) (by unfold c0_10; omega))
  by_cases h2 : q≤195
  ·
    exact four_is_representable 2 _ (c0_14_sound 4 q 0 (by norm_num) (by unfold c0_14; omega))
  by_cases h3 : q≤196
  ·
    exact four_is_representable 2 _ (c0_12_sound 4 q 0 (by norm_num) (by unfold c0_12; omega))
  by_cases h4 : q≤197
  ·
    have hq : q=197 := by omega
    subst q
    exact represent_exception 6304 (by decide +kernel)
  by_cases h5 : q≤228
  ·
    exact four_is_representable 2 _ (c0_16_sound 4 q 0 (by norm_num) (by unfold c0_16; omega))
  by_cases h6 : q≤244
  ·
    exact four_is_representable 2 _ (c0_18_sound 4 q 0 (by norm_num) (by unfold c0_18; omega))
  by_cases h7 : q≤261
  ·
    exact four_is_representable 2 _ (c0_13_sound 4 q 0 (by norm_num) (by unfold c0_13; omega))
  by_cases h8 : q≤262
  ·
    have hq : q=262 := by omega
    subst q
    exact represent_exception 8384 (by decide +kernel)
  by_cases h9 : q≤291
  ·
    exact four_is_representable 2 _ (c0_17_sound 4 q 0 (by norm_num) (by unfold c0_17; omega))
  by_cases h10 : q≤292
  ·
    have hq : q=292 := by omega
    subst q
    exact represent_exception 9344 (by decide +kernel)
  by_cases h11 : q≤326
  ·
    exact four_is_representable 2 _ (c0_6_sound 4 q 0 (by norm_num) (by unfold c0_6; omega))
  by_cases h12 : q≤371
  ·
    exact four_is_representable 2 _ (c0_19_sound 4 q 0 (by norm_num) (by unfold c0_19; omega))
  by_cases h13 : q≤435
  ·
    exact four_is_representable 2 _ (c0_11_sound 4 q 0 (by norm_num) (by unfold c0_11; omega))
  by_cases h14 : q≤500
  ·
    exact four_is_representable 2 _ (c0_20_sound 4 q 0 (by norm_num) (by unfold c0_20; omega))
  exact four_is_representable 2 _ (c0_7_sound 4 q 0 (by norm_num) (by unfold c0_7; omega))

set_option maxRecDepth 10000 in
def middle_4_0_1 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+0)+1 : ℤ).toNat) := by
  by_cases h0 : q≤150
  ·
    exact four_is_representable 2 _ (c0_9_sound 4 q 1 (by norm_num) (by unfold c0_9; omega))
  by_cases h1 : q≤175
  ·
    exact four_is_representable 2 _ (c0_10_sound 4 q 1 (by norm_num) (by unfold c0_10; omega))
  by_cases h2 : q≤196
  ·
    exact four_is_representable 2 _ (c0_14_sound 4 q 1 (by norm_num) (by unfold c0_14; omega))
  by_cases h3 : q≤198
  ·
    exact four_is_representable 2 _ (c0_12_sound 4 q 1 (by norm_num) (by unfold c0_12; omega))
  by_cases h4 : q≤199
  ·
    have hq : q=199 := by omega
    subst q
    exact represent_exception 6369 (by decide +kernel)
  by_cases h5 : q≤230
  ·
    exact four_is_representable 2 _ (c0_16_sound 4 q 1 (by norm_num) (by unfold c0_16; omega))
  by_cases h6 : q≤246
  ·
    exact four_is_representable 2 _ (c0_18_sound 4 q 1 (by norm_num) (by unfold c0_18; omega))
  by_cases h7 : q≤263
  ·
    exact four_is_representable 2 _ (c0_13_sound 4 q 1 (by norm_num) (by unfold c0_13; omega))
  by_cases h8 : q≤264
  ·
    have hq : q=264 := by omega
    subst q
    exact represent_exception 8449 (by decide +kernel)
  by_cases h9 : q≤292
  ·
    exact four_is_representable 2 _ (c0_17_sound 4 q 1 (by norm_num) (by unfold c0_17; omega))
  by_cases h10 : q≤293
  ·
    have hq : q=293 := by omega
    subst q
    exact represent_exception 9377 (by decide +kernel)
  by_cases h11 : q≤330
  ·
    exact four_is_representable 2 _ (c0_6_sound 4 q 1 (by norm_num) (by unfold c0_6; omega))
  by_cases h12 : q≤375
  ·
    exact four_is_representable 2 _ (c0_19_sound 4 q 1 (by norm_num) (by unfold c0_19; omega))
  by_cases h13 : q≤439
  ·
    exact four_is_representable 2 _ (c0_11_sound 4 q 1 (by norm_num) (by unfold c0_11; omega))
  by_cases h14 : q≤504
  ·
    exact four_is_representable 2 _ (c0_20_sound 4 q 1 (by norm_num) (by unfold c0_20; omega))
  exact four_is_representable 2 _ (c0_7_sound 4 q 1 (by norm_num) (by unfold c0_7; omega))

set_option maxRecDepth 10000 in
def middle_4_0_2 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+0)+2 : ℤ).toNat) := by
  by_cases h0 : q≤152
  ·
    exact four_is_representable 2 _ (c0_9_sound 4 q 2 (by norm_num) (by unfold c0_9; omega))
  by_cases h1 : q≤176
  ·
    exact four_is_representable 2 _ (c0_10_sound 4 q 2 (by norm_num) (by unfold c0_10; omega))
  by_cases h2 : q≤197
  ·
    exact four_is_representable 2 _ (c0_14_sound 4 q 2 (by norm_num) (by unfold c0_14; omega))
  by_cases h3 : q≤200
  ·
    exact four_is_representable 2 _ (c0_12_sound 4 q 2 (by norm_num) (by unfold c0_12; omega))
  by_cases h4 : q≤201
  ·
    have hq : q=201 := by omega
    subst q
    exact represent_exception 6434 (by decide +kernel)
  by_cases h5 : q≤232
  ·
    exact four_is_representable 2 _ (c0_16_sound 4 q 2 (by norm_num) (by unfold c0_16; omega))
  by_cases h6 : q≤248
  ·
    exact four_is_representable 2 _ (c0_18_sound 4 q 2 (by norm_num) (by unfold c0_18; omega))
  by_cases h7 : q≤265
  ·
    exact four_is_representable 2 _ (c0_13_sound 4 q 2 (by norm_num) (by unfold c0_13; omega))
  by_cases h8 : q≤266
  ·
    have hq : q=266 := by omega
    subst q
    exact represent_exception 8514 (by decide +kernel)
  by_cases h9 : q≤293
  ·
    exact four_is_representable 2 _ (c0_17_sound 4 q 2 (by norm_num) (by unfold c0_17; omega))
  by_cases h10 : q≤294
  ·
    have hq : q=294 := by omega
    subst q
    exact represent_exception 9410 (by decide +kernel)
  by_cases h11 : q≤334
  ·
    exact four_is_representable 2 _ (c0_6_sound 4 q 2 (by norm_num) (by unfold c0_6; omega))
  by_cases h12 : q≤379
  ·
    exact four_is_representable 2 _ (c0_19_sound 4 q 2 (by norm_num) (by unfold c0_19; omega))
  by_cases h13 : q≤443
  ·
    exact four_is_representable 2 _ (c0_11_sound 4 q 2 (by norm_num) (by unfold c0_11; omega))
  by_cases h14 : q≤508
  ·
    exact four_is_representable 2 _ (c0_20_sound 4 q 2 (by norm_num) (by unfold c0_20; omega))
  exact four_is_representable 2 _ (c0_7_sound 4 q 2 (by norm_num) (by unfold c0_7; omega))

set_option maxRecDepth 10000 in
def middle_4_0_3 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+0)+3 : ℤ).toNat) := by
  by_cases h0 : q≤154
  ·
    exact four_is_representable 2 _ (c0_9_sound 4 q 3 (by norm_num) (by unfold c0_9; omega))
  by_cases h1 : q≤177
  ·
    exact four_is_representable 2 _ (c0_10_sound 4 q 3 (by norm_num) (by unfold c0_10; omega))
  by_cases h2 : q≤198
  ·
    exact four_is_representable 2 _ (c0_14_sound 4 q 3 (by norm_num) (by unfold c0_14; omega))
  by_cases h3 : q≤202
  ·
    exact four_is_representable 2 _ (c0_12_sound 4 q 3 (by norm_num) (by unfold c0_12; omega))
  by_cases h4 : q≤203
  ·
    have hq : q=203 := by omega
    subst q
    exact represent_exception 6499 (by decide +kernel)
  by_cases h5 : q≤234
  ·
    exact four_is_representable 2 _ (c0_16_sound 4 q 3 (by norm_num) (by unfold c0_16; omega))
  by_cases h6 : q≤250
  ·
    exact four_is_representable 2 _ (c0_18_sound 4 q 3 (by norm_num) (by unfold c0_18; omega))
  by_cases h7 : q≤267
  ·
    exact four_is_representable 2 _ (c0_13_sound 4 q 3 (by norm_num) (by unfold c0_13; omega))
  by_cases h8 : q≤268
  ·
    have hq : q=268 := by omega
    subst q
    exact represent_exception 8579 (by decide +kernel)
  by_cases h9 : q≤294
  ·
    exact four_is_representable 2 _ (c0_17_sound 4 q 3 (by norm_num) (by unfold c0_17; omega))
  by_cases h10 : q≤295
  ·
    have hq : q=295 := by omega
    subst q
    exact represent_exception 9443 (by decide +kernel)
  by_cases h11 : q≤338
  ·
    exact four_is_representable 2 _ (c0_6_sound 4 q 3 (by norm_num) (by unfold c0_6; omega))
  by_cases h12 : q≤383
  ·
    exact four_is_representable 2 _ (c0_19_sound 4 q 3 (by norm_num) (by unfold c0_19; omega))
  by_cases h13 : q≤447
  ·
    exact four_is_representable 2 _ (c0_11_sound 4 q 3 (by norm_num) (by unfold c0_11; omega))
  exact four_is_representable 2 _ (c0_20_sound 4 q 3 (by norm_num) (by unfold c0_20; omega))

set_option maxRecDepth 10000 in
def middle_4_0_4 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+0)+4 : ℤ).toNat) := by
  by_cases h0 : q≤156
  ·
    exact four_is_representable 2 _ (c0_9_sound 4 q 4 (by norm_num) (by unfold c0_9; omega))
  by_cases h1 : q≤178
  ·
    exact four_is_representable 2 _ (c0_10_sound 4 q 4 (by norm_num) (by unfold c0_10; omega))
  by_cases h2 : q≤199
  ·
    exact four_is_representable 2 _ (c0_14_sound 4 q 4 (by norm_num) (by unfold c0_14; omega))
  by_cases h3 : q≤204
  ·
    exact four_is_representable 2 _ (c0_12_sound 4 q 4 (by norm_num) (by unfold c0_12; omega))
  by_cases h4 : q≤205
  ·
    have hq : q=205 := by omega
    subst q
    exact represent_exception 6564 (by decide +kernel)
  by_cases h5 : q≤236
  ·
    exact four_is_representable 2 _ (c0_16_sound 4 q 4 (by norm_num) (by unfold c0_16; omega))
  by_cases h6 : q≤252
  ·
    exact four_is_representable 2 _ (c0_18_sound 4 q 4 (by norm_num) (by unfold c0_18; omega))
  by_cases h7 : q≤269
  ·
    exact four_is_representable 2 _ (c0_13_sound 4 q 4 (by norm_num) (by unfold c0_13; omega))
  by_cases h8 : q≤270
  ·
    have hq : q=270 := by omega
    subst q
    exact represent_exception 8644 (by decide +kernel)
  by_cases h9 : q≤295
  ·
    exact four_is_representable 2 _ (c0_17_sound 4 q 4 (by norm_num) (by unfold c0_17; omega))
  by_cases h10 : q≤296
  ·
    have hq : q=296 := by omega
    subst q
    exact represent_exception 9476 (by decide +kernel)
  by_cases h11 : q≤342
  ·
    exact four_is_representable 2 _ (c0_6_sound 4 q 4 (by norm_num) (by unfold c0_6; omega))
  by_cases h12 : q≤387
  ·
    exact four_is_representable 2 _ (c0_19_sound 4 q 4 (by norm_num) (by unfold c0_19; omega))
  by_cases h13 : q≤451
  ·
    exact four_is_representable 2 _ (c0_11_sound 4 q 4 (by norm_num) (by unfold c0_11; omega))
  exact four_is_representable 2 _ (c0_20_sound 4 q 4 (by norm_num) (by unfold c0_20; omega))

set_option maxRecDepth 10000 in
def middle_4_0_5 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+0)+5 : ℤ).toNat) := by
  by_cases h0 : q≤129
  ·
    exact four_is_representable 2 _ (c0_21_sound 4 q 5 (by norm_num) (by unfold c0_21; omega))
  by_cases h1 : q≤158
  ·
    exact four_is_representable 2 _ (c0_9_sound 4 q 5 (by norm_num) (by unfold c0_9; omega))
  by_cases h2 : q≤179
  ·
    exact four_is_representable 2 _ (c0_10_sound 4 q 5 (by norm_num) (by unfold c0_10; omega))
  by_cases h3 : q≤200
  ·
    exact four_is_representable 2 _ (c0_14_sound 4 q 5 (by norm_num) (by unfold c0_14; omega))
  by_cases h4 : q≤206
  ·
    exact four_is_representable 2 _ (c0_12_sound 4 q 5 (by norm_num) (by unfold c0_12; omega))
  by_cases h5 : q≤207
  ·
    have hq : q=207 := by omega
    subst q
    exact represent_exception 6629 (by decide +kernel)
  by_cases h6 : q≤238
  ·
    exact four_is_representable 2 _ (c0_16_sound 4 q 5 (by norm_num) (by unfold c0_16; omega))
  by_cases h7 : q≤254
  ·
    exact four_is_representable 2 _ (c0_18_sound 4 q 5 (by norm_num) (by unfold c0_18; omega))
  by_cases h8 : q≤271
  ·
    exact four_is_representable 2 _ (c0_13_sound 4 q 5 (by norm_num) (by unfold c0_13; omega))
  by_cases h9 : q≤272
  ·
    have hq : q=272 := by omega
    subst q
    exact represent_exception 8709 (by decide +kernel)
  by_cases h10 : q≤296
  ·
    exact four_is_representable 2 _ (c0_17_sound 4 q 5 (by norm_num) (by unfold c0_17; omega))
  by_cases h11 : q≤297
  ·
    have hq : q=297 := by omega
    subst q
    exact represent_exception 9509 (by decide +kernel)
  by_cases h12 : q≤346
  ·
    exact four_is_representable 2 _ (c0_6_sound 4 q 5 (by norm_num) (by unfold c0_6; omega))
  by_cases h13 : q≤391
  ·
    exact four_is_representable 2 _ (c0_19_sound 4 q 5 (by norm_num) (by unfold c0_19; omega))
  by_cases h14 : q≤455
  ·
    exact four_is_representable 2 _ (c0_11_sound 4 q 5 (by norm_num) (by unfold c0_11; omega))
  exact four_is_representable 2 _ (c0_20_sound 4 q 5 (by norm_num) (by unfold c0_20; omega))

set_option maxRecDepth 10000 in
def middle_4_0_6 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+0)+6 : ℤ).toNat) := by
  by_cases h0 : q≤131
  ·
    exact four_is_representable 2 _ (c0_21_sound 4 q 6 (by norm_num) (by unfold c0_21; omega))
  by_cases h1 : q≤160
  ·
    exact four_is_representable 2 _ (c0_9_sound 4 q 6 (by norm_num) (by unfold c0_9; omega))
  by_cases h2 : q≤180
  ·
    exact four_is_representable 2 _ (c0_10_sound 4 q 6 (by norm_num) (by unfold c0_10; omega))
  by_cases h3 : q≤201
  ·
    exact four_is_representable 2 _ (c0_14_sound 4 q 6 (by norm_num) (by unfold c0_14; omega))
  by_cases h4 : q≤208
  ·
    exact four_is_representable 2 _ (c0_12_sound 4 q 6 (by norm_num) (by unfold c0_12; omega))
  by_cases h5 : q≤209
  ·
    have hq : q=209 := by omega
    subst q
    exact represent_exception 6694 (by decide +kernel)
  by_cases h6 : q≤240
  ·
    exact four_is_representable 2 _ (c0_16_sound 4 q 6 (by norm_num) (by unfold c0_16; omega))
  by_cases h7 : q≤256
  ·
    exact four_is_representable 2 _ (c0_18_sound 4 q 6 (by norm_num) (by unfold c0_18; omega))
  by_cases h8 : q≤273
  ·
    exact four_is_representable 2 _ (c0_13_sound 4 q 6 (by norm_num) (by unfold c0_13; omega))
  by_cases h9 : q≤274
  ·
    have hq : q=274 := by omega
    subst q
    exact represent_exception 8774 (by decide +kernel)
  by_cases h10 : q≤297
  ·
    exact four_is_representable 2 _ (c0_17_sound 4 q 6 (by norm_num) (by unfold c0_17; omega))
  by_cases h11 : q≤298
  ·
    have hq : q=298 := by omega
    subst q
    exact represent_exception 9542 (by decide +kernel)
  by_cases h12 : q≤350
  ·
    exact four_is_representable 2 _ (c0_6_sound 4 q 6 (by norm_num) (by unfold c0_6; omega))
  by_cases h13 : q≤395
  ·
    exact four_is_representable 2 _ (c0_19_sound 4 q 6 (by norm_num) (by unfold c0_19; omega))
  by_cases h14 : q≤459
  ·
    exact four_is_representable 2 _ (c0_11_sound 4 q 6 (by norm_num) (by unfold c0_11; omega))
  exact four_is_representable 2 _ (c0_20_sound 4 q 6 (by norm_num) (by unfold c0_20; omega))

set_option maxRecDepth 10000 in
def middle_4_0_7 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+0)+7 : ℤ).toNat) := by
  by_cases h0 : q≤133
  ·
    exact four_is_representable 2 _ (c0_21_sound 4 q 7 (by norm_num) (by unfold c0_21; omega))
  by_cases h1 : q≤162
  ·
    exact four_is_representable 2 _ (c0_9_sound 4 q 7 (by norm_num) (by unfold c0_9; omega))
  by_cases h2 : q≤181
  ·
    exact four_is_representable 2 _ (c0_10_sound 4 q 7 (by norm_num) (by unfold c0_10; omega))
  by_cases h3 : q≤202
  ·
    exact four_is_representable 2 _ (c0_14_sound 4 q 7 (by norm_num) (by unfold c0_14; omega))
  by_cases h4 : q≤210
  ·
    exact four_is_representable 2 _ (c0_12_sound 4 q 7 (by norm_num) (by unfold c0_12; omega))
  by_cases h5 : q≤211
  ·
    have hq : q=211 := by omega
    subst q
    exact represent_exception 6759 (by decide +kernel)
  by_cases h6 : q≤242
  ·
    exact four_is_representable 2 _ (c0_16_sound 4 q 7 (by norm_num) (by unfold c0_16; omega))
  by_cases h7 : q≤258
  ·
    exact four_is_representable 2 _ (c0_18_sound 4 q 7 (by norm_num) (by unfold c0_18; omega))
  by_cases h8 : q≤275
  ·
    exact four_is_representable 2 _ (c0_13_sound 4 q 7 (by norm_num) (by unfold c0_13; omega))
  by_cases h9 : q≤276
  ·
    have hq : q=276 := by omega
    subst q
    exact represent_exception 8839 (by decide +kernel)
  by_cases h10 : q≤298
  ·
    exact four_is_representable 2 _ (c0_17_sound 4 q 7 (by norm_num) (by unfold c0_17; omega))
  by_cases h11 : q≤299
  ·
    have hq : q=299 := by omega
    subst q
    exact represent_exception 9575 (by decide +kernel)
  by_cases h12 : q≤300
  ·
    have hq : q=300 := by omega
    subst q
    exact represent_exception 9607 (by decide +kernel)
  by_cases h13 : q≤301
  ·
    have hq : q=301 := by omega
    subst q
    exact represent_exception 9639 (by decide +kernel)
  by_cases h14 : q≤302
  ·
    have hq : q=302 := by omega
    subst q
    exact represent_exception 9671 (by decide +kernel)
  by_cases h15 : q≤354
  ·
    exact four_is_representable 2 _ (c0_6_sound 4 q 7 (by norm_num) (by unfold c0_6; omega))
  by_cases h16 : q≤399
  ·
    exact four_is_representable 2 _ (c0_19_sound 4 q 7 (by norm_num) (by unfold c0_19; omega))
  by_cases h17 : q≤463
  ·
    exact four_is_representable 2 _ (c0_11_sound 4 q 7 (by norm_num) (by unfold c0_11; omega))
  exact four_is_representable 2 _ (c0_20_sound 4 q 7 (by norm_num) (by unfold c0_20; omega))

set_option maxRecDepth 10000 in
def middle_4_1_0 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+1)+0 : ℤ).toNat) := by
  by_cases h0 : q≤131
  ·
    exact four_is_representable 2 _ (c1_17_sound 4 q 0 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤164
  ·
    exact four_is_representable 2 _ (c1_16_sound 4 q 0 (by norm_num) (by unfold c1_16; omega))
  by_cases h2 : q≤182
  ·
    exact four_is_representable 2 _ (c1_11_sound 4 q 0 (by norm_num) (by unfold c1_11; omega))
  by_cases h3 : q≤203
  ·
    exact four_is_representable 2 _ (c1_9_sound 4 q 0 (by norm_num) (by unfold c1_9; omega))
  by_cases h4 : q≤212
  ·
    exact four_is_representable 2 _ (c1_13_sound 4 q 0 (by norm_num) (by unfold c1_13; omega))
  by_cases h5 : q≤213
  ·
    have hq : q=213 := by omega
    subst q
    exact represent_exception 6824 (by decide +kernel)
  by_cases h6 : q≤244
  ·
    exact four_is_representable 2 _ (c1_19_sound 4 q 0 (by norm_num) (by unfold c1_19; omega))
  by_cases h7 : q≤260
  ·
    exact four_is_representable 2 _ (c1_5_sound 4 q 0 (by norm_num) (by unfold c1_5; omega))
  by_cases h8 : q≤277
  ·
    exact four_is_representable 2 _ (c1_12_sound 4 q 0 (by norm_num) (by unfold c1_12; omega))
  by_cases h9 : q≤278
  ·
    have hq : q=278 := by omega
    subst q
    exact represent_exception 8904 (by decide +kernel)
  by_cases h10 : q≤299
  ·
    exact four_is_representable 2 _ (c1_8_sound 4 q 0 (by norm_num) (by unfold c1_8; omega))
  by_cases h11 : q≤300
  ·
    have hq : q=300 := by omega
    subst q
    exact represent_exception 9608 (by decide +kernel)
  by_cases h12 : q≤301
  ·
    have hq : q=301 := by omega
    subst q
    exact represent_exception 9640 (by decide +kernel)
  by_cases h13 : q≤302
  ·
    have hq : q=302 := by omega
    subst q
    exact represent_exception 9672 (by decide +kernel)
  by_cases h14 : q≤303
  ·
    have hq : q=303 := by omega
    subst q
    exact represent_exception 9704 (by decide +kernel)
  by_cases h15 : q≤304
  ·
    have hq : q=304 := by omega
    subst q
    exact represent_exception 9736 (by decide +kernel)
  by_cases h16 : q≤305
  ·
    have hq : q=305 := by omega
    subst q
    exact represent_exception 9768 (by decide +kernel)
  by_cases h17 : q≤306
  ·
    have hq : q=306 := by omega
    subst q
    exact represent_exception 9800 (by decide +kernel)
  by_cases h18 : q≤358
  ·
    exact four_is_representable 2 _ (c1_20_sound 4 q 0 (by norm_num) (by unfold c1_20; omega))
  by_cases h19 : q≤403
  ·
    exact four_is_representable 2 _ (c1_15_sound 4 q 0 (by norm_num) (by unfold c1_15; omega))
  by_cases h20 : q≤423
  ·
    exact four_is_representable 2 _ (c1_23_sound 4 q 0 (by norm_num) (by unfold c1_23; omega))
  exact four_is_representable 2 _ (c1_7_sound 4 q 0 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_4_1_1 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+1)+1 : ℤ).toNat) := by
  by_cases h0 : q≤133
  ·
    exact four_is_representable 2 _ (c1_17_sound 4 q 1 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤166
  ·
    exact four_is_representable 2 _ (c1_16_sound 4 q 1 (by norm_num) (by unfold c1_16; omega))
  by_cases h2 : q≤183
  ·
    exact four_is_representable 2 _ (c1_11_sound 4 q 1 (by norm_num) (by unfold c1_11; omega))
  by_cases h3 : q≤184
  ·
    have hq : q=184 := by omega
    subst q
    exact represent_exception 5897 (by decide +kernel)
  by_cases h4 : q≤204
  ·
    exact four_is_representable 2 _ (c1_9_sound 4 q 1 (by norm_num) (by unfold c1_9; omega))
  by_cases h5 : q≤214
  ·
    exact four_is_representable 2 _ (c1_13_sound 4 q 1 (by norm_num) (by unfold c1_13; omega))
  by_cases h6 : q≤215
  ·
    have hq : q=215 := by omega
    subst q
    exact represent_exception 6889 (by decide +kernel)
  by_cases h7 : q≤246
  ·
    exact four_is_representable 2 _ (c1_19_sound 4 q 1 (by norm_num) (by unfold c1_19; omega))
  by_cases h8 : q≤262
  ·
    exact four_is_representable 2 _ (c1_5_sound 4 q 1 (by norm_num) (by unfold c1_5; omega))
  by_cases h9 : q≤279
  ·
    exact four_is_representable 2 _ (c1_12_sound 4 q 1 (by norm_num) (by unfold c1_12; omega))
  by_cases h10 : q≤280
  ·
    have hq : q=280 := by omega
    subst q
    exact represent_exception 8969 (by decide +kernel)
  by_cases h11 : q≤300
  ·
    exact four_is_representable 2 _ (c1_8_sound 4 q 1 (by norm_num) (by unfold c1_8; omega))
  by_cases h12 : q≤301
  ·
    have hq : q=301 := by omega
    subst q
    exact represent_exception 9641 (by decide +kernel)
  by_cases h13 : q≤302
  ·
    have hq : q=302 := by omega
    subst q
    exact represent_exception 9673 (by decide +kernel)
  by_cases h14 : q≤303
  ·
    have hq : q=303 := by omega
    subst q
    exact represent_exception 9705 (by decide +kernel)
  by_cases h15 : q≤304
  ·
    have hq : q=304 := by omega
    subst q
    exact represent_exception 9737 (by decide +kernel)
  by_cases h16 : q≤305
  ·
    have hq : q=305 := by omega
    subst q
    exact represent_exception 9769 (by decide +kernel)
  by_cases h17 : q≤306
  ·
    have hq : q=306 := by omega
    subst q
    exact represent_exception 9801 (by decide +kernel)
  by_cases h18 : q≤307
  ·
    have hq : q=307 := by omega
    subst q
    exact represent_exception 9833 (by decide +kernel)
  by_cases h19 : q≤308
  ·
    have hq : q=308 := by omega
    subst q
    exact represent_exception 9865 (by decide +kernel)
  by_cases h20 : q≤342
  ·
    exact four_is_representable 2 _ (c1_22_sound 4 q 1 (by norm_num) (by unfold c1_22; omega))
  by_cases h21 : q≤407
  ·
    exact four_is_representable 2 _ (c1_15_sound 4 q 1 (by norm_num) (by unfold c1_15; omega))
  by_cases h22 : q≤427
  ·
    exact four_is_representable 2 _ (c1_23_sound 4 q 1 (by norm_num) (by unfold c1_23; omega))
  exact four_is_representable 2 _ (c1_7_sound 4 q 1 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_4_1_2 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+1)+2 : ℤ).toNat) := by
  by_cases h0 : q≤135
  ·
    exact four_is_representable 2 _ (c1_17_sound 4 q 2 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤168
  ·
    exact four_is_representable 2 _ (c1_16_sound 4 q 2 (by norm_num) (by unfold c1_16; omega))
  by_cases h2 : q≤184
  ·
    exact four_is_representable 2 _ (c1_11_sound 4 q 2 (by norm_num) (by unfold c1_11; omega))
  by_cases h3 : q≤185
  ·
    have hq : q=185 := by omega
    subst q
    exact represent_exception 5930 (by decide +kernel)
  by_cases h4 : q≤186
  ·
    have hq : q=186 := by omega
    subst q
    exact represent_exception 5962 (by decide +kernel)
  by_cases h5 : q≤205
  ·
    exact four_is_representable 2 _ (c1_9_sound 4 q 2 (by norm_num) (by unfold c1_9; omega))
  by_cases h6 : q≤216
  ·
    exact four_is_representable 2 _ (c1_13_sound 4 q 2 (by norm_num) (by unfold c1_13; omega))
  by_cases h7 : q≤217
  ·
    have hq : q=217 := by omega
    subst q
    exact represent_exception 6954 (by decide +kernel)
  by_cases h8 : q≤248
  ·
    exact four_is_representable 2 _ (c1_19_sound 4 q 2 (by norm_num) (by unfold c1_19; omega))
  by_cases h9 : q≤264
  ·
    exact four_is_representable 2 _ (c1_5_sound 4 q 2 (by norm_num) (by unfold c1_5; omega))
  by_cases h10 : q≤280
  ·
    exact four_is_representable 2 _ (c1_12_sound 4 q 2 (by norm_num) (by unfold c1_12; omega))
  by_cases h11 : q≤281
  ·
    have hq : q=281 := by omega
    subst q
    exact represent_exception 9002 (by decide +kernel)
  by_cases h12 : q≤282
  ·
    have hq : q=282 := by omega
    subst q
    exact represent_exception 9034 (by decide +kernel)
  by_cases h13 : q≤301
  ·
    exact four_is_representable 2 _ (c1_8_sound 4 q 2 (by norm_num) (by unfold c1_8; omega))
  by_cases h14 : q≤302
  ·
    exact four_is_representable 2 _ (c1_21_sound 4 q 2 (by norm_num) (by unfold c1_21; omega))
  by_cases h15 : q≤303
  ·
    have hq : q=303 := by omega
    subst q
    exact represent_exception 9706 (by decide +kernel)
  by_cases h16 : q≤304
  ·
    have hq : q=304 := by omega
    subst q
    exact represent_exception 9738 (by decide +kernel)
  by_cases h17 : q≤305
  ·
    have hq : q=305 := by omega
    subst q
    exact represent_exception 9770 (by decide +kernel)
  by_cases h18 : q≤306
  ·
    have hq : q=306 := by omega
    subst q
    exact represent_exception 9802 (by decide +kernel)
  by_cases h19 : q≤307
  ·
    have hq : q=307 := by omega
    subst q
    exact represent_exception 9834 (by decide +kernel)
  by_cases h20 : q≤308
  ·
    have hq : q=308 := by omega
    subst q
    exact represent_exception 9866 (by decide +kernel)
  by_cases h21 : q≤309
  ·
    have hq : q=309 := by omega
    subst q
    exact represent_exception 9898 (by decide +kernel)
  by_cases h22 : q≤346
  ·
    exact four_is_representable 2 _ (c1_22_sound 4 q 2 (by norm_num) (by unfold c1_22; omega))
  by_cases h23 : q≤411
  ·
    exact four_is_representable 2 _ (c1_15_sound 4 q 2 (by norm_num) (by unfold c1_15; omega))
  exact four_is_representable 2 _ (c1_7_sound 4 q 2 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_4_1_3 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+1)+3 : ℤ).toNat) := by
  by_cases h0 : q≤137
  ·
    exact four_is_representable 2 _ (c1_17_sound 4 q 3 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤169
  ·
    exact four_is_representable 2 _ (c1_16_sound 4 q 3 (by norm_num) (by unfold c1_16; omega))
  by_cases h2 : q≤186
  ·
    exact four_is_representable 2 _ (c1_14_sound 4 q 3 (by norm_num) (by unfold c1_14; omega))
  by_cases h3 : q≤187
  ·
    have hq : q=187 := by omega
    subst q
    exact represent_exception 5995 (by decide +kernel)
  by_cases h4 : q≤188
  ·
    have hq : q=188 := by omega
    subst q
    exact represent_exception 6027 (by decide +kernel)
  by_cases h5 : q≤206
  ·
    exact four_is_representable 2 _ (c1_9_sound 4 q 3 (by norm_num) (by unfold c1_9; omega))
  by_cases h6 : q≤218
  ·
    exact four_is_representable 2 _ (c1_13_sound 4 q 3 (by norm_num) (by unfold c1_13; omega))
  by_cases h7 : q≤219
  ·
    have hq : q=219 := by omega
    subst q
    exact represent_exception 7019 (by decide +kernel)
  by_cases h8 : q≤250
  ·
    exact four_is_representable 2 _ (c1_19_sound 4 q 3 (by norm_num) (by unfold c1_19; omega))
  by_cases h9 : q≤266
  ·
    exact four_is_representable 2 _ (c1_5_sound 4 q 3 (by norm_num) (by unfold c1_5; omega))
  by_cases h10 : q≤281
  ·
    exact four_is_representable 2 _ (c1_12_sound 4 q 3 (by norm_num) (by unfold c1_12; omega))
  by_cases h11 : q≤282
  ·
    have hq : q=282 := by omega
    subst q
    exact represent_exception 9035 (by decide +kernel)
  by_cases h12 : q≤283
  ·
    have hq : q=283 := by omega
    subst q
    exact represent_exception 9067 (by decide +kernel)
  by_cases h13 : q≤284
  ·
    have hq : q=284 := by omega
    subst q
    exact represent_exception 9099 (by decide +kernel)
  by_cases h14 : q≤302
  ·
    exact four_is_representable 2 _ (c1_8_sound 4 q 3 (by norm_num) (by unfold c1_8; omega))
  by_cases h15 : q≤306
  ·
    exact four_is_representable 2 _ (c1_21_sound 4 q 3 (by norm_num) (by unfold c1_21; omega))
  by_cases h16 : q≤307
  ·
    have hq : q=307 := by omega
    subst q
    exact represent_exception 9835 (by decide +kernel)
  by_cases h17 : q≤308
  ·
    have hq : q=308 := by omega
    subst q
    exact represent_exception 9867 (by decide +kernel)
  by_cases h18 : q≤309
  ·
    have hq : q=309 := by omega
    subst q
    exact represent_exception 9899 (by decide +kernel)
  by_cases h19 : q≤310
  ·
    have hq : q=310 := by omega
    subst q
    exact represent_exception 9931 (by decide +kernel)
  by_cases h20 : q≤350
  ·
    exact four_is_representable 2 _ (c1_22_sound 4 q 3 (by norm_num) (by unfold c1_22; omega))
  by_cases h21 : q≤415
  ·
    exact four_is_representable 2 _ (c1_15_sound 4 q 3 (by norm_num) (by unfold c1_15; omega))
  exact four_is_representable 2 _ (c1_7_sound 4 q 3 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_4_1_4 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+1)+4 : ℤ).toNat) := by
  by_cases h0 : q≤139
  ·
    exact four_is_representable 2 _ (c1_17_sound 4 q 4 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤170
  ·
    exact four_is_representable 2 _ (c1_16_sound 4 q 4 (by norm_num) (by unfold c1_16; omega))
  by_cases h2 : q≤188
  ·
    exact four_is_representable 2 _ (c1_14_sound 4 q 4 (by norm_num) (by unfold c1_14; omega))
  by_cases h3 : q≤189
  ·
    have hq : q=189 := by omega
    subst q
    exact represent_exception 6060 (by decide +kernel)
  by_cases h4 : q≤190
  ·
    have hq : q=190 := by omega
    subst q
    exact represent_exception 6092 (by decide +kernel)
  by_cases h5 : q≤207
  ·
    exact four_is_representable 2 _ (c1_9_sound 4 q 4 (by norm_num) (by unfold c1_9; omega))
  by_cases h6 : q≤220
  ·
    exact four_is_representable 2 _ (c1_13_sound 4 q 4 (by norm_num) (by unfold c1_13; omega))
  by_cases h7 : q≤221
  ·
    have hq : q=221 := by omega
    subst q
    exact represent_exception 7084 (by decide +kernel)
  by_cases h8 : q≤252
  ·
    exact four_is_representable 2 _ (c1_19_sound 4 q 4 (by norm_num) (by unfold c1_19; omega))
  by_cases h9 : q≤268
  ·
    exact four_is_representable 2 _ (c1_5_sound 4 q 4 (by norm_num) (by unfold c1_5; omega))
  by_cases h10 : q≤282
  ·
    exact four_is_representable 2 _ (c1_12_sound 4 q 4 (by norm_num) (by unfold c1_12; omega))
  by_cases h11 : q≤283
  ·
    have hq : q=283 := by omega
    subst q
    exact represent_exception 9068 (by decide +kernel)
  by_cases h12 : q≤284
  ·
    have hq : q=284 := by omega
    subst q
    exact represent_exception 9100 (by decide +kernel)
  by_cases h13 : q≤285
  ·
    have hq : q=285 := by omega
    subst q
    exact represent_exception 9132 (by decide +kernel)
  by_cases h14 : q≤286
  ·
    have hq : q=286 := by omega
    subst q
    exact represent_exception 9164 (by decide +kernel)
  by_cases h15 : q≤303
  ·
    exact four_is_representable 2 _ (c1_8_sound 4 q 4 (by norm_num) (by unfold c1_8; omega))
  by_cases h16 : q≤310
  ·
    exact four_is_representable 2 _ (c1_21_sound 4 q 4 (by norm_num) (by unfold c1_21; omega))
  by_cases h17 : q≤311
  ·
    have hq : q=311 := by omega
    subst q
    exact represent_exception 9964 (by decide +kernel)
  by_cases h18 : q≤354
  ·
    exact four_is_representable 2 _ (c1_22_sound 4 q 4 (by norm_num) (by unfold c1_22; omega))
  by_cases h19 : q≤419
  ·
    exact four_is_representable 2 _ (c1_15_sound 4 q 4 (by norm_num) (by unfold c1_15; omega))
  exact four_is_representable 2 _ (c1_7_sound 4 q 4 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_4_1_5 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+1)+5 : ℤ).toNat) := by
  by_cases h0 : q≤141
  ·
    exact four_is_representable 2 _ (c1_17_sound 4 q 5 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤171
  ·
    exact four_is_representable 2 _ (c1_16_sound 4 q 5 (by norm_num) (by unfold c1_16; omega))
  by_cases h2 : q≤190
  ·
    exact four_is_representable 2 _ (c1_14_sound 4 q 5 (by norm_num) (by unfold c1_14; omega))
  by_cases h3 : q≤191
  ·
    have hq : q=191 := by omega
    subst q
    exact represent_exception 6125 (by decide +kernel)
  by_cases h4 : q≤192
  ·
    have hq : q=192 := by omega
    subst q
    exact represent_exception 6157 (by decide +kernel)
  by_cases h5 : q≤208
  ·
    exact four_is_representable 2 _ (c1_9_sound 4 q 5 (by norm_num) (by unfold c1_9; omega))
  by_cases h6 : q≤222
  ·
    exact four_is_representable 2 _ (c1_13_sound 4 q 5 (by norm_num) (by unfold c1_13; omega))
  by_cases h7 : q≤223
  ·
    have hq : q=223 := by omega
    subst q
    exact represent_exception 7149 (by decide +kernel)
  by_cases h8 : q≤254
  ·
    exact four_is_representable 2 _ (c1_19_sound 4 q 5 (by norm_num) (by unfold c1_19; omega))
  by_cases h9 : q≤270
  ·
    exact four_is_representable 2 _ (c1_5_sound 4 q 5 (by norm_num) (by unfold c1_5; omega))
  by_cases h10 : q≤283
  ·
    exact four_is_representable 2 _ (c1_12_sound 4 q 5 (by norm_num) (by unfold c1_12; omega))
  by_cases h11 : q≤284
  ·
    have hq : q=284 := by omega
    subst q
    exact represent_exception 9101 (by decide +kernel)
  by_cases h12 : q≤285
  ·
    have hq : q=285 := by omega
    subst q
    exact represent_exception 9133 (by decide +kernel)
  by_cases h13 : q≤286
  ·
    have hq : q=286 := by omega
    subst q
    exact represent_exception 9165 (by decide +kernel)
  by_cases h14 : q≤287
  ·
    have hq : q=287 := by omega
    subst q
    exact represent_exception 9197 (by decide +kernel)
  by_cases h15 : q≤288
  ·
    have hq : q=288 := by omega
    subst q
    exact represent_exception 9229 (by decide +kernel)
  by_cases h16 : q≤304
  ·
    exact four_is_representable 2 _ (c1_8_sound 4 q 5 (by norm_num) (by unfold c1_8; omega))
  by_cases h17 : q≤314
  ·
    exact four_is_representable 2 _ (c1_21_sound 4 q 5 (by norm_num) (by unfold c1_21; omega))
  by_cases h18 : q≤358
  ·
    exact four_is_representable 2 _ (c1_22_sound 4 q 5 (by norm_num) (by unfold c1_22; omega))
  by_cases h19 : q≤423
  ·
    exact four_is_representable 2 _ (c1_15_sound 4 q 5 (by norm_num) (by unfold c1_15; omega))
  exact four_is_representable 2 _ (c1_7_sound 4 q 5 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_4_1_6 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+1)+6 : ℤ).toNat) := by
  by_cases h0 : q≤143
  ·
    exact four_is_representable 2 _ (c1_17_sound 4 q 6 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤172
  ·
    exact four_is_representable 2 _ (c1_16_sound 4 q 6 (by norm_num) (by unfold c1_16; omega))
  by_cases h2 : q≤192
  ·
    exact four_is_representable 2 _ (c1_14_sound 4 q 6 (by norm_num) (by unfold c1_14; omega))
  by_cases h3 : q≤193
  ·
    have hq : q=193 := by omega
    subst q
    exact represent_exception 6190 (by decide +kernel)
  by_cases h4 : q≤194
  ·
    have hq : q=194 := by omega
    subst q
    exact represent_exception 6222 (by decide +kernel)
  by_cases h5 : q≤209
  ·
    exact four_is_representable 2 _ (c1_9_sound 4 q 6 (by norm_num) (by unfold c1_9; omega))
  by_cases h6 : q≤224
  ·
    exact four_is_representable 2 _ (c1_13_sound 4 q 6 (by norm_num) (by unfold c1_13; omega))
  by_cases h7 : q≤225
  ·
    have hq : q=225 := by omega
    subst q
    exact represent_exception 7214 (by decide +kernel)
  by_cases h8 : q≤256
  ·
    exact four_is_representable 2 _ (c1_19_sound 4 q 6 (by norm_num) (by unfold c1_19; omega))
  by_cases h9 : q≤272
  ·
    exact four_is_representable 2 _ (c1_5_sound 4 q 6 (by norm_num) (by unfold c1_5; omega))
  by_cases h10 : q≤284
  ·
    exact four_is_representable 2 _ (c1_12_sound 4 q 6 (by norm_num) (by unfold c1_12; omega))
  by_cases h11 : q≤285
  ·
    have hq : q=285 := by omega
    subst q
    exact represent_exception 9134 (by decide +kernel)
  by_cases h12 : q≤286
  ·
    have hq : q=286 := by omega
    subst q
    exact represent_exception 9166 (by decide +kernel)
  by_cases h13 : q≤287
  ·
    have hq : q=287 := by omega
    subst q
    exact represent_exception 9198 (by decide +kernel)
  by_cases h14 : q≤288
  ·
    have hq : q=288 := by omega
    subst q
    exact represent_exception 9230 (by decide +kernel)
  by_cases h15 : q≤289
  ·
    have hq : q=289 := by omega
    subst q
    exact represent_exception 9262 (by decide +kernel)
  by_cases h16 : q≤318
  ·
    exact four_is_representable 2 _ (c1_21_sound 4 q 6 (by norm_num) (by unfold c1_21; omega))
  by_cases h17 : q≤362
  ·
    exact four_is_representable 2 _ (c1_22_sound 4 q 6 (by norm_num) (by unfold c1_22; omega))
  by_cases h18 : q≤427
  ·
    exact four_is_representable 2 _ (c1_15_sound 4 q 6 (by norm_num) (by unfold c1_15; omega))
  exact four_is_representable 2 _ (c1_7_sound 4 q 6 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_4_1_7 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+1)+7 : ℤ).toNat) := by
  by_cases h0 : q≤145
  ·
    exact four_is_representable 2 _ (c1_17_sound 4 q 7 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤177
  ·
    exact four_is_representable 2 _ (c1_10_sound 4 q 7 (by norm_num) (by unfold c1_10; omega))
  by_cases h2 : q≤194
  ·
    exact four_is_representable 2 _ (c1_14_sound 4 q 7 (by norm_num) (by unfold c1_14; omega))
  by_cases h3 : q≤195
  ·
    have hq : q=195 := by omega
    subst q
    exact represent_exception 6255 (by decide +kernel)
  by_cases h4 : q≤196
  ·
    have hq : q=196 := by omega
    subst q
    exact represent_exception 6287 (by decide +kernel)
  by_cases h5 : q≤210
  ·
    exact four_is_representable 2 _ (c1_9_sound 4 q 7 (by norm_num) (by unfold c1_9; omega))
  by_cases h6 : q≤226
  ·
    exact four_is_representable 2 _ (c1_13_sound 4 q 7 (by norm_num) (by unfold c1_13; omega))
  by_cases h7 : q≤227
  ·
    have hq : q=227 := by omega
    subst q
    exact represent_exception 7279 (by decide +kernel)
  by_cases h8 : q≤258
  ·
    exact four_is_representable 2 _ (c1_19_sound 4 q 7 (by norm_num) (by unfold c1_19; omega))
  by_cases h9 : q≤274
  ·
    exact four_is_representable 2 _ (c1_5_sound 4 q 7 (by norm_num) (by unfold c1_5; omega))
  by_cases h10 : q≤285
  ·
    exact four_is_representable 2 _ (c1_12_sound 4 q 7 (by norm_num) (by unfold c1_12; omega))
  by_cases h11 : q≤286
  ·
    have hq : q=286 := by omega
    subst q
    exact represent_exception 9167 (by decide +kernel)
  by_cases h12 : q≤287
  ·
    have hq : q=287 := by omega
    subst q
    exact represent_exception 9199 (by decide +kernel)
  by_cases h13 : q≤288
  ·
    have hq : q=288 := by omega
    subst q
    exact represent_exception 9231 (by decide +kernel)
  by_cases h14 : q≤289
  ·
    have hq : q=289 := by omega
    subst q
    exact represent_exception 9263 (by decide +kernel)
  by_cases h15 : q≤290
  ·
    have hq : q=290 := by omega
    subst q
    exact represent_exception 9295 (by decide +kernel)
  by_cases h16 : q≤322
  ·
    exact four_is_representable 2 _ (c1_21_sound 4 q 7 (by norm_num) (by unfold c1_21; omega))
  by_cases h17 : q≤366
  ·
    exact four_is_representable 2 _ (c1_22_sound 4 q 7 (by norm_num) (by unfold c1_22; omega))
  by_cases h18 : q≤431
  ·
    exact four_is_representable 2 _ (c1_15_sound 4 q 7 (by norm_num) (by unfold c1_15; omega))
  exact four_is_representable 2 _ (c1_7_sound 4 q 7 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_4_2_0 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+2)+0 : ℤ).toNat) := by
  by_cases h0 : q≤151
  ·
    exact four_is_representable 2 _ (c2_7_sound 4 q 0 (by norm_num) (by unfold c2_7; omega))
  by_cases h1 : q≤178
  ·
    exact four_is_representable 2 _ (c2_2_sound 4 q 0 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤196
  ·
    exact four_is_representable 2 _ (c2_23_sound 4 q 0 (by norm_num) (by unfold c2_23; omega))
  by_cases h3 : q≤197
  ·
    have hq : q=197 := by omega
    subst q
    exact represent_exception 6320 (by decide +kernel)
  by_cases h4 : q≤198
  ·
    have hq : q=198 := by omega
    subst q
    exact represent_exception 6352 (by decide +kernel)
  by_cases h5 : q≤211
  ·
    exact four_is_representable 2 _ (c2_19_sound 4 q 0 (by norm_num) (by unfold c2_19; omega))
  by_cases h6 : q≤228
  ·
    exact four_is_representable 2 _ (c2_1_sound 4 q 0 (by norm_num) (by unfold c2_1; omega))
  by_cases h7 : q≤229
  ·
    have hq : q=229 := by omega
    subst q
    exact represent_exception 7344 (by decide +kernel)
  by_cases h8 : q≤260
  ·
    exact four_is_representable 2 _ (c2_0_sound 4 q 0 (by norm_num) (by unfold c2_0; omega))
  by_cases h9 : q≤276
  ·
    exact four_is_representable 2 _ (c2_3_sound 4 q 0 (by norm_num) (by unfold c2_3; omega))
  by_cases h10 : q≤286
  ·
    exact four_is_representable 2 _ (c2_18_sound 4 q 0 (by norm_num) (by unfold c2_18; omega))
  by_cases h11 : q≤287
  ·
    have hq : q=287 := by omega
    subst q
    exact represent_exception 9200 (by decide +kernel)
  by_cases h12 : q≤288
  ·
    have hq : q=288 := by omega
    subst q
    exact represent_exception 9232 (by decide +kernel)
  by_cases h13 : q≤289
  ·
    have hq : q=289 := by omega
    subst q
    exact represent_exception 9264 (by decide +kernel)
  by_cases h14 : q≤290
  ·
    have hq : q=290 := by omega
    subst q
    exact represent_exception 9296 (by decide +kernel)
  by_cases h15 : q≤291
  ·
    have hq : q=291 := by omega
    subst q
    exact represent_exception 9328 (by decide +kernel)
  by_cases h16 : q≤326
  ·
    exact four_is_representable 2 _ (c2_13_sound 4 q 0 (by norm_num) (by unfold c2_13; omega))
  by_cases h17 : q≤370
  ·
    exact four_is_representable 2 _ (c2_20_sound 4 q 0 (by norm_num) (by unfold c2_20; omega))
  by_cases h18 : q≤435
  ·
    exact four_is_representable 2 _ (c2_21_sound 4 q 0 (by norm_num) (by unfold c2_21; omega))
  by_cases h19 : q≤499
  ·
    exact four_is_representable 2 _ (c2_22_sound 4 q 0 (by norm_num) (by unfold c2_22; omega))
  exact four_is_representable 2 _ (c2_15_sound 4 q 0 (by norm_num) (by unfold c2_15; omega))

set_option maxRecDepth 10000 in
def middle_4_2_1 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+2)+1 : ℤ).toNat) := by
  by_cases h0 : q≤153
  ·
    exact four_is_representable 2 _ (c2_7_sound 4 q 1 (by norm_num) (by unfold c2_7; omega))
  by_cases h1 : q≤179
  ·
    exact four_is_representable 2 _ (c2_2_sound 4 q 1 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤198
  ·
    exact four_is_representable 2 _ (c2_23_sound 4 q 1 (by norm_num) (by unfold c2_23; omega))
  by_cases h3 : q≤199
  ·
    have hq : q=199 := by omega
    subst q
    exact represent_exception 6385 (by decide +kernel)
  by_cases h4 : q≤200
  ·
    have hq : q=200 := by omega
    subst q
    exact represent_exception 6417 (by decide +kernel)
  by_cases h5 : q≤212
  ·
    exact four_is_representable 2 _ (c2_19_sound 4 q 1 (by norm_num) (by unfold c2_19; omega))
  by_cases h6 : q≤230
  ·
    exact four_is_representable 2 _ (c2_1_sound 4 q 1 (by norm_num) (by unfold c2_1; omega))
  by_cases h7 : q≤231
  ·
    have hq : q=231 := by omega
    subst q
    exact represent_exception 7409 (by decide +kernel)
  by_cases h8 : q≤262
  ·
    exact four_is_representable 2 _ (c2_0_sound 4 q 1 (by norm_num) (by unfold c2_0; omega))
  by_cases h9 : q≤278
  ·
    exact four_is_representable 2 _ (c2_3_sound 4 q 1 (by norm_num) (by unfold c2_3; omega))
  by_cases h10 : q≤287
  ·
    exact four_is_representable 2 _ (c2_18_sound 4 q 1 (by norm_num) (by unfold c2_18; omega))
  by_cases h11 : q≤288
  ·
    have hq : q=288 := by omega
    subst q
    exact represent_exception 9233 (by decide +kernel)
  by_cases h12 : q≤289
  ·
    have hq : q=289 := by omega
    subst q
    exact represent_exception 9265 (by decide +kernel)
  by_cases h13 : q≤290
  ·
    have hq : q=290 := by omega
    subst q
    exact represent_exception 9297 (by decide +kernel)
  by_cases h14 : q≤291
  ·
    have hq : q=291 := by omega
    subst q
    exact represent_exception 9329 (by decide +kernel)
  by_cases h15 : q≤292
  ·
    have hq : q=292 := by omega
    subst q
    exact represent_exception 9361 (by decide +kernel)
  by_cases h16 : q≤330
  ·
    exact four_is_representable 2 _ (c2_13_sound 4 q 1 (by norm_num) (by unfold c2_13; omega))
  by_cases h17 : q≤374
  ·
    exact four_is_representable 2 _ (c2_20_sound 4 q 1 (by norm_num) (by unfold c2_20; omega))
  by_cases h18 : q≤439
  ·
    exact four_is_representable 2 _ (c2_21_sound 4 q 1 (by norm_num) (by unfold c2_21; omega))
  by_cases h19 : q≤503
  ·
    exact four_is_representable 2 _ (c2_22_sound 4 q 1 (by norm_num) (by unfold c2_22; omega))
  exact four_is_representable 2 _ (c2_15_sound 4 q 1 (by norm_num) (by unfold c2_15; omega))

set_option maxRecDepth 10000 in
def middle_4_2_2 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+2)+2 : ℤ).toNat) := by
  by_cases h0 : q≤155
  ·
    exact four_is_representable 2 _ (c2_7_sound 4 q 2 (by norm_num) (by unfold c2_7; omega))
  by_cases h1 : q≤180
  ·
    exact four_is_representable 2 _ (c2_2_sound 4 q 2 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤200
  ·
    exact four_is_representable 2 _ (c2_23_sound 4 q 2 (by norm_num) (by unfold c2_23; omega))
  by_cases h3 : q≤201
  ·
    have hq : q=201 := by omega
    subst q
    exact represent_exception 6450 (by decide +kernel)
  by_cases h4 : q≤202
  ·
    have hq : q=202 := by omega
    subst q
    exact represent_exception 6482 (by decide +kernel)
  by_cases h5 : q≤213
  ·
    exact four_is_representable 2 _ (c2_19_sound 4 q 2 (by norm_num) (by unfold c2_19; omega))
  by_cases h6 : q≤232
  ·
    exact four_is_representable 2 _ (c2_1_sound 4 q 2 (by norm_num) (by unfold c2_1; omega))
  by_cases h7 : q≤233
  ·
    have hq : q=233 := by omega
    subst q
    exact represent_exception 7474 (by decide +kernel)
  by_cases h8 : q≤264
  ·
    exact four_is_representable 2 _ (c2_0_sound 4 q 2 (by norm_num) (by unfold c2_0; omega))
  by_cases h9 : q≤280
  ·
    exact four_is_representable 2 _ (c2_3_sound 4 q 2 (by norm_num) (by unfold c2_3; omega))
  by_cases h10 : q≤288
  ·
    exact four_is_representable 2 _ (c2_18_sound 4 q 2 (by norm_num) (by unfold c2_18; omega))
  by_cases h11 : q≤289
  ·
    have hq : q=289 := by omega
    subst q
    exact represent_exception 9266 (by decide +kernel)
  by_cases h12 : q≤290
  ·
    have hq : q=290 := by omega
    subst q
    exact represent_exception 9298 (by decide +kernel)
  by_cases h13 : q≤291
  ·
    have hq : q=291 := by omega
    subst q
    exact represent_exception 9330 (by decide +kernel)
  by_cases h14 : q≤292
  ·
    have hq : q=292 := by omega
    subst q
    exact represent_exception 9362 (by decide +kernel)
  by_cases h15 : q≤293
  ·
    have hq : q=293 := by omega
    subst q
    exact represent_exception 9394 (by decide +kernel)
  by_cases h16 : q≤334
  ·
    exact four_is_representable 2 _ (c2_13_sound 4 q 2 (by norm_num) (by unfold c2_13; omega))
  by_cases h17 : q≤378
  ·
    exact four_is_representable 2 _ (c2_20_sound 4 q 2 (by norm_num) (by unfold c2_20; omega))
  by_cases h18 : q≤443
  ·
    exact four_is_representable 2 _ (c2_21_sound 4 q 2 (by norm_num) (by unfold c2_21; omega))
  by_cases h19 : q≤507
  ·
    exact four_is_representable 2 _ (c2_22_sound 4 q 2 (by norm_num) (by unfold c2_22; omega))
  exact four_is_representable 2 _ (c2_15_sound 4 q 2 (by norm_num) (by unfold c2_15; omega))

set_option maxRecDepth 10000 in
def middle_4_2_3 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+2)+3 : ℤ).toNat) := by
  by_cases h0 : q≤156
  ·
    exact four_is_representable 2 _ (c2_7_sound 4 q 3 (by norm_num) (by unfold c2_7; omega))
  by_cases h1 : q≤181
  ·
    exact four_is_representable 2 _ (c2_2_sound 4 q 3 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤201
  ·
    exact four_is_representable 2 _ (c2_4_sound 4 q 3 (by norm_num) (by unfold c2_4; omega))
  by_cases h3 : q≤202
  ·
    exact four_is_representable 2 _ (c2_23_sound 4 q 3 (by norm_num) (by unfold c2_23; omega))
  by_cases h4 : q≤203
  ·
    have hq : q=203 := by omega
    subst q
    exact represent_exception 6515 (by decide +kernel)
  by_cases h5 : q≤204
  ·
    have hq : q=204 := by omega
    subst q
    exact represent_exception 6547 (by decide +kernel)
  by_cases h6 : q≤214
  ·
    exact four_is_representable 2 _ (c2_19_sound 4 q 3 (by norm_num) (by unfold c2_19; omega))
  by_cases h7 : q≤234
  ·
    exact four_is_representable 2 _ (c2_1_sound 4 q 3 (by norm_num) (by unfold c2_1; omega))
  by_cases h8 : q≤235
  ·
    have hq : q=235 := by omega
    subst q
    exact represent_exception 7539 (by decide +kernel)
  by_cases h9 : q≤266
  ·
    exact four_is_representable 2 _ (c2_0_sound 4 q 3 (by norm_num) (by unfold c2_0; omega))
  by_cases h10 : q≤282
  ·
    exact four_is_representable 2 _ (c2_3_sound 4 q 3 (by norm_num) (by unfold c2_3; omega))
  by_cases h11 : q≤289
  ·
    exact four_is_representable 2 _ (c2_18_sound 4 q 3 (by norm_num) (by unfold c2_18; omega))
  by_cases h12 : q≤290
  ·
    have hq : q=290 := by omega
    subst q
    exact represent_exception 9299 (by decide +kernel)
  by_cases h13 : q≤291
  ·
    have hq : q=291 := by omega
    subst q
    exact represent_exception 9331 (by decide +kernel)
  by_cases h14 : q≤292
  ·
    have hq : q=292 := by omega
    subst q
    exact represent_exception 9363 (by decide +kernel)
  by_cases h15 : q≤293
  ·
    have hq : q=293 := by omega
    subst q
    exact represent_exception 9395 (by decide +kernel)
  by_cases h16 : q≤294
  ·
    have hq : q=294 := by omega
    subst q
    exact represent_exception 9427 (by decide +kernel)
  by_cases h17 : q≤338
  ·
    exact four_is_representable 2 _ (c2_13_sound 4 q 3 (by norm_num) (by unfold c2_13; omega))
  by_cases h18 : q≤382
  ·
    exact four_is_representable 2 _ (c2_20_sound 4 q 3 (by norm_num) (by unfold c2_20; omega))
  by_cases h19 : q≤447
  ·
    exact four_is_representable 2 _ (c2_21_sound 4 q 3 (by norm_num) (by unfold c2_21; omega))
  exact four_is_representable 2 _ (c2_22_sound 4 q 3 (by norm_num) (by unfold c2_22; omega))

set_option maxRecDepth 10000 in
def middle_4_2_4 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+2)+4 : ℤ).toNat) := by
  by_cases h0 : q≤155
  ·
    exact four_is_representable 2 _ (c2_14_sound 4 q 4 (by norm_num) (by unfold c2_14; omega))
  by_cases h1 : q≤182
  ·
    exact four_is_representable 2 _ (c2_2_sound 4 q 4 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤203
  ·
    exact four_is_representable 2 _ (c2_4_sound 4 q 4 (by norm_num) (by unfold c2_4; omega))
  by_cases h3 : q≤204
  ·
    exact four_is_representable 2 _ (c2_23_sound 4 q 4 (by norm_num) (by unfold c2_23; omega))
  by_cases h4 : q≤205
  ·
    have hq : q=205 := by omega
    subst q
    exact represent_exception 6580 (by decide +kernel)
  by_cases h5 : q≤206
  ·
    have hq : q=206 := by omega
    subst q
    exact represent_exception 6612 (by decide +kernel)
  by_cases h6 : q≤215
  ·
    exact four_is_representable 2 _ (c2_19_sound 4 q 4 (by norm_num) (by unfold c2_19; omega))
  by_cases h7 : q≤219
  ·
    exact four_is_representable 2 _ (c2_24_sound 4 q 4 (by norm_num) (by unfold c2_24; omega))
  by_cases h8 : q≤236
  ·
    exact four_is_representable 2 _ (c2_1_sound 4 q 4 (by norm_num) (by unfold c2_1; omega))
  by_cases h9 : q≤237
  ·
    have hq : q=237 := by omega
    subst q
    exact represent_exception 7604 (by decide +kernel)
  by_cases h10 : q≤268
  ·
    exact four_is_representable 2 _ (c2_0_sound 4 q 4 (by norm_num) (by unfold c2_0; omega))
  by_cases h11 : q≤284
  ·
    exact four_is_representable 2 _ (c2_3_sound 4 q 4 (by norm_num) (by unfold c2_3; omega))
  by_cases h12 : q≤290
  ·
    exact four_is_representable 2 _ (c2_18_sound 4 q 4 (by norm_num) (by unfold c2_18; omega))
  by_cases h13 : q≤291
  ·
    have hq : q=291 := by omega
    subst q
    exact represent_exception 9332 (by decide +kernel)
  by_cases h14 : q≤292
  ·
    have hq : q=292 := by omega
    subst q
    exact represent_exception 9364 (by decide +kernel)
  by_cases h15 : q≤293
  ·
    have hq : q=293 := by omega
    subst q
    exact represent_exception 9396 (by decide +kernel)
  by_cases h16 : q≤294
  ·
    have hq : q=294 := by omega
    subst q
    exact represent_exception 9428 (by decide +kernel)
  by_cases h17 : q≤295
  ·
    have hq : q=295 := by omega
    subst q
    exact represent_exception 9460 (by decide +kernel)
  by_cases h18 : q≤342
  ·
    exact four_is_representable 2 _ (c2_13_sound 4 q 4 (by norm_num) (by unfold c2_13; omega))
  by_cases h19 : q≤386
  ·
    exact four_is_representable 2 _ (c2_20_sound 4 q 4 (by norm_num) (by unfold c2_20; omega))
  by_cases h20 : q≤451
  ·
    exact four_is_representable 2 _ (c2_21_sound 4 q 4 (by norm_num) (by unfold c2_21; omega))
  exact four_is_representable 2 _ (c2_22_sound 4 q 4 (by norm_num) (by unfold c2_22; omega))

set_option maxRecDepth 10000 in
def middle_4_2_5 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+2)+5 : ℤ).toNat) := by
  by_cases h0 : q≤157
  ·
    exact four_is_representable 2 _ (c2_14_sound 4 q 5 (by norm_num) (by unfold c2_14; omega))
  by_cases h1 : q≤183
  ·
    exact four_is_representable 2 _ (c2_2_sound 4 q 5 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤205
  ·
    exact four_is_representable 2 _ (c2_4_sound 4 q 5 (by norm_num) (by unfold c2_4; omega))
  by_cases h3 : q≤206
  ·
    exact four_is_representable 2 _ (c2_23_sound 4 q 5 (by norm_num) (by unfold c2_23; omega))
  by_cases h4 : q≤207
  ·
    have hq : q=207 := by omega
    subst q
    exact represent_exception 6645 (by decide +kernel)
  by_cases h5 : q≤208
  ·
    have hq : q=208 := by omega
    subst q
    exact represent_exception 6677 (by decide +kernel)
  by_cases h6 : q≤216
  ·
    exact four_is_representable 2 _ (c2_19_sound 4 q 5 (by norm_num) (by unfold c2_19; omega))
  by_cases h7 : q≤221
  ·
    exact four_is_representable 2 _ (c2_24_sound 4 q 5 (by norm_num) (by unfold c2_24; omega))
  by_cases h8 : q≤238
  ·
    exact four_is_representable 2 _ (c2_1_sound 4 q 5 (by norm_num) (by unfold c2_1; omega))
  by_cases h9 : q≤239
  ·
    have hq : q=239 := by omega
    subst q
    exact represent_exception 7669 (by decide +kernel)
  by_cases h10 : q≤270
  ·
    exact four_is_representable 2 _ (c2_0_sound 4 q 5 (by norm_num) (by unfold c2_0; omega))
  by_cases h11 : q≤286
  ·
    exact four_is_representable 2 _ (c2_3_sound 4 q 5 (by norm_num) (by unfold c2_3; omega))
  by_cases h12 : q≤291
  ·
    exact four_is_representable 2 _ (c2_18_sound 4 q 5 (by norm_num) (by unfold c2_18; omega))
  by_cases h13 : q≤292
  ·
    have hq : q=292 := by omega
    subst q
    exact represent_exception 9365 (by decide +kernel)
  by_cases h14 : q≤293
  ·
    have hq : q=293 := by omega
    subst q
    exact represent_exception 9397 (by decide +kernel)
  by_cases h15 : q≤294
  ·
    have hq : q=294 := by omega
    subst q
    exact represent_exception 9429 (by decide +kernel)
  by_cases h16 : q≤295
  ·
    have hq : q=295 := by omega
    subst q
    exact represent_exception 9461 (by decide +kernel)
  by_cases h17 : q≤296
  ·
    have hq : q=296 := by omega
    subst q
    exact represent_exception 9493 (by decide +kernel)
  by_cases h18 : q≤346
  ·
    exact four_is_representable 2 _ (c2_13_sound 4 q 5 (by norm_num) (by unfold c2_13; omega))
  by_cases h19 : q≤390
  ·
    exact four_is_representable 2 _ (c2_20_sound 4 q 5 (by norm_num) (by unfold c2_20; omega))
  by_cases h20 : q≤455
  ·
    exact four_is_representable 2 _ (c2_21_sound 4 q 5 (by norm_num) (by unfold c2_21; omega))
  exact four_is_representable 2 _ (c2_22_sound 4 q 5 (by norm_num) (by unfold c2_22; omega))

set_option maxRecDepth 10000 in
def middle_4_2_6 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+2)+6 : ℤ).toNat) := by
  by_cases h0 : q≤131
  ·
    exact four_is_representable 2 _ (c2_25_sound 4 q 6 (by norm_num) (by unfold c2_25; omega))
  by_cases h1 : q≤159
  ·
    exact four_is_representable 2 _ (c2_14_sound 4 q 6 (by norm_num) (by unfold c2_14; omega))
  by_cases h2 : q≤184
  ·
    exact four_is_representable 2 _ (c2_2_sound 4 q 6 (by norm_num) (by unfold c2_2; omega))
  by_cases h3 : q≤207
  ·
    exact four_is_representable 2 _ (c2_4_sound 4 q 6 (by norm_num) (by unfold c2_4; omega))
  by_cases h4 : q≤208
  ·
    exact four_is_representable 2 _ (c2_23_sound 4 q 6 (by norm_num) (by unfold c2_23; omega))
  by_cases h5 : q≤209
  ·
    have hq : q=209 := by omega
    subst q
    exact represent_exception 6710 (by decide +kernel)
  by_cases h6 : q≤210
  ·
    have hq : q=210 := by omega
    subst q
    exact represent_exception 6742 (by decide +kernel)
  by_cases h7 : q≤217
  ·
    exact four_is_representable 2 _ (c2_19_sound 4 q 6 (by norm_num) (by unfold c2_19; omega))
  by_cases h8 : q≤223
  ·
    exact four_is_representable 2 _ (c2_24_sound 4 q 6 (by norm_num) (by unfold c2_24; omega))
  by_cases h9 : q≤240
  ·
    exact four_is_representable 2 _ (c2_1_sound 4 q 6 (by norm_num) (by unfold c2_1; omega))
  by_cases h10 : q≤241
  ·
    have hq : q=241 := by omega
    subst q
    exact represent_exception 7734 (by decide +kernel)
  by_cases h11 : q≤272
  ·
    exact four_is_representable 2 _ (c2_0_sound 4 q 6 (by norm_num) (by unfold c2_0; omega))
  by_cases h12 : q≤288
  ·
    exact four_is_representable 2 _ (c2_3_sound 4 q 6 (by norm_num) (by unfold c2_3; omega))
  by_cases h13 : q≤292
  ·
    exact four_is_representable 2 _ (c2_18_sound 4 q 6 (by norm_num) (by unfold c2_18; omega))
  by_cases h14 : q≤293
  ·
    have hq : q=293 := by omega
    subst q
    exact represent_exception 9398 (by decide +kernel)
  by_cases h15 : q≤294
  ·
    have hq : q=294 := by omega
    subst q
    exact represent_exception 9430 (by decide +kernel)
  by_cases h16 : q≤295
  ·
    have hq : q=295 := by omega
    subst q
    exact represent_exception 9462 (by decide +kernel)
  by_cases h17 : q≤296
  ·
    have hq : q=296 := by omega
    subst q
    exact represent_exception 9494 (by decide +kernel)
  by_cases h18 : q≤297
  ·
    have hq : q=297 := by omega
    subst q
    exact represent_exception 9526 (by decide +kernel)
  by_cases h19 : q≤350
  ·
    exact four_is_representable 2 _ (c2_13_sound 4 q 6 (by norm_num) (by unfold c2_13; omega))
  by_cases h20 : q≤394
  ·
    exact four_is_representable 2 _ (c2_20_sound 4 q 6 (by norm_num) (by unfold c2_20; omega))
  by_cases h21 : q≤459
  ·
    exact four_is_representable 2 _ (c2_21_sound 4 q 6 (by norm_num) (by unfold c2_21; omega))
  exact four_is_representable 2 _ (c2_22_sound 4 q 6 (by norm_num) (by unfold c2_22; omega))

set_option maxRecDepth 10000 in
def middle_4_2_7 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+2)+7 : ℤ).toNat) := by
  by_cases h0 : q≤133
  ·
    exact four_is_representable 2 _ (c2_25_sound 4 q 7 (by norm_num) (by unfold c2_25; omega))
  by_cases h1 : q≤161
  ·
    exact four_is_representable 2 _ (c2_14_sound 4 q 7 (by norm_num) (by unfold c2_14; omega))
  by_cases h2 : q≤185
  ·
    exact four_is_representable 2 _ (c2_2_sound 4 q 7 (by norm_num) (by unfold c2_2; omega))
  by_cases h3 : q≤209
  ·
    exact four_is_representable 2 _ (c2_4_sound 4 q 7 (by norm_num) (by unfold c2_4; omega))
  by_cases h4 : q≤210
  ·
    exact four_is_representable 2 _ (c2_23_sound 4 q 7 (by norm_num) (by unfold c2_23; omega))
  by_cases h5 : q≤211
  ·
    have hq : q=211 := by omega
    subst q
    exact represent_exception 6775 (by decide +kernel)
  by_cases h6 : q≤212
  ·
    have hq : q=212 := by omega
    subst q
    exact represent_exception 6807 (by decide +kernel)
  by_cases h7 : q≤218
  ·
    exact four_is_representable 2 _ (c2_19_sound 4 q 7 (by norm_num) (by unfold c2_19; omega))
  by_cases h8 : q≤225
  ·
    exact four_is_representable 2 _ (c2_24_sound 4 q 7 (by norm_num) (by unfold c2_24; omega))
  by_cases h9 : q≤242
  ·
    exact four_is_representable 2 _ (c2_1_sound 4 q 7 (by norm_num) (by unfold c2_1; omega))
  by_cases h10 : q≤243
  ·
    have hq : q=243 := by omega
    subst q
    exact represent_exception 7799 (by decide +kernel)
  by_cases h11 : q≤274
  ·
    exact four_is_representable 2 _ (c2_0_sound 4 q 7 (by norm_num) (by unfold c2_0; omega))
  by_cases h12 : q≤290
  ·
    exact four_is_representable 2 _ (c2_3_sound 4 q 7 (by norm_num) (by unfold c2_3; omega))
  by_cases h13 : q≤292
  ·
    exact four_is_representable 2 _ (c2_18_sound 4 q 7 (by norm_num) (by unfold c2_18; omega))
  by_cases h14 : q≤293
  ·
    have hq : q=293 := by omega
    subst q
    exact represent_exception 9399 (by decide +kernel)
  by_cases h15 : q≤294
  ·
    have hq : q=294 := by omega
    subst q
    exact represent_exception 9431 (by decide +kernel)
  by_cases h16 : q≤295
  ·
    have hq : q=295 := by omega
    subst q
    exact represent_exception 9463 (by decide +kernel)
  by_cases h17 : q≤296
  ·
    have hq : q=296 := by omega
    subst q
    exact represent_exception 9495 (by decide +kernel)
  by_cases h18 : q≤297
  ·
    have hq : q=297 := by omega
    subst q
    exact represent_exception 9527 (by decide +kernel)
  by_cases h19 : q≤298
  ·
    have hq : q=298 := by omega
    subst q
    exact represent_exception 9559 (by decide +kernel)
  by_cases h20 : q≤299
  ·
    have hq : q=299 := by omega
    subst q
    exact represent_exception 9591 (by decide +kernel)
  by_cases h21 : q≤300
  ·
    have hq : q=300 := by omega
    subst q
    exact represent_exception 9623 (by decide +kernel)
  by_cases h22 : q≤301
  ·
    have hq : q=301 := by omega
    subst q
    exact represent_exception 9655 (by decide +kernel)
  by_cases h23 : q≤354
  ·
    exact four_is_representable 2 _ (c2_13_sound 4 q 7 (by norm_num) (by unfold c2_13; omega))
  by_cases h24 : q≤398
  ·
    exact four_is_representable 2 _ (c2_20_sound 4 q 7 (by norm_num) (by unfold c2_20; omega))
  by_cases h25 : q≤463
  ·
    exact four_is_representable 2 _ (c2_21_sound 4 q 7 (by norm_num) (by unfold c2_21; omega))
  exact four_is_representable 2 _ (c2_22_sound 4 q 7 (by norm_num) (by unfold c2_22; omega))

set_option maxRecDepth 10000 in
def middle_4_3_0 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+3)+0 : ℤ).toNat) := by
  by_cases h0 : q≤131
  ·
    exact four_is_representable 2 _ (c3_0_sound 4 q 0 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤163
  ·
    exact four_is_representable 2 _ (c3_14_sound 4 q 0 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤186
  ·
    exact four_is_representable 2 _ (c3_16_sound 4 q 0 (by norm_num) (by unfold c3_16; omega))
  by_cases h3 : q≤211
  ·
    exact four_is_representable 2 _ (c3_13_sound 4 q 0 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤212
  ·
    exact four_is_representable 2 _ (c3_26_sound 4 q 0 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤213
  ·
    have hq : q=213 := by omega
    subst q
    exact represent_exception 6840 (by decide +kernel)
  by_cases h6 : q≤214
  ·
    have hq : q=214 := by omega
    subst q
    exact represent_exception 6872 (by decide +kernel)
  by_cases h7 : q≤219
  ·
    exact four_is_representable 2 _ (c3_27_sound 4 q 0 (by norm_num) (by unfold c3_27; omega))
  by_cases h8 : q≤227
  ·
    exact four_is_representable 2 _ (c3_24_sound 4 q 0 (by norm_num) (by unfold c3_24; omega))
  by_cases h9 : q≤244
  ·
    exact four_is_representable 2 _ (c3_11_sound 4 q 0 (by norm_num) (by unfold c3_11; omega))
  by_cases h10 : q≤245
  ·
    have hq : q=245 := by omega
    subst q
    exact represent_exception 7864 (by decide +kernel)
  by_cases h11 : q≤276
  ·
    exact four_is_representable 2 _ (c3_15_sound 4 q 0 (by norm_num) (by unfold c3_15; omega))
  by_cases h12 : q≤292
  ·
    exact four_is_representable 2 _ (c3_17_sound 4 q 0 (by norm_num) (by unfold c3_17; omega))
  by_cases h13 : q≤293
  ·
    exact four_is_representable 2 _ (c3_19_sound 4 q 0 (by norm_num) (by unfold c3_19; omega))
  by_cases h14 : q≤294
  ·
    have hq : q=294 := by omega
    subst q
    exact represent_exception 9432 (by decide +kernel)
  by_cases h15 : q≤295
  ·
    have hq : q=295 := by omega
    subst q
    exact represent_exception 9464 (by decide +kernel)
  by_cases h16 : q≤296
  ·
    have hq : q=296 := by omega
    subst q
    exact represent_exception 9496 (by decide +kernel)
  by_cases h17 : q≤297
  ·
    have hq : q=297 := by omega
    subst q
    exact represent_exception 9528 (by decide +kernel)
  by_cases h18 : q≤298
  ·
    have hq : q=298 := by omega
    subst q
    exact represent_exception 9560 (by decide +kernel)
  by_cases h19 : q≤299
  ·
    have hq : q=299 := by omega
    subst q
    exact represent_exception 9592 (by decide +kernel)
  by_cases h20 : q≤300
  ·
    have hq : q=300 := by omega
    subst q
    exact represent_exception 9624 (by decide +kernel)
  by_cases h21 : q≤301
  ·
    have hq : q=301 := by omega
    subst q
    exact represent_exception 9656 (by decide +kernel)
  by_cases h22 : q≤302
  ·
    have hq : q=302 := by omega
    subst q
    exact represent_exception 9688 (by decide +kernel)
  by_cases h23 : q≤303
  ·
    have hq : q=303 := by omega
    subst q
    exact represent_exception 9720 (by decide +kernel)
  by_cases h24 : q≤304
  ·
    have hq : q=304 := by omega
    subst q
    exact represent_exception 9752 (by decide +kernel)
  by_cases h25 : q≤305
  ·
    have hq : q=305 := by omega
    subst q
    exact represent_exception 9784 (by decide +kernel)
  by_cases h26 : q≤358
  ·
    exact four_is_representable 2 _ (c3_10_sound 4 q 0 (by norm_num) (by unfold c3_10; omega))
  by_cases h27 : q≤402
  ·
    exact four_is_representable 2 _ (c3_23_sound 4 q 0 (by norm_num) (by unfold c3_23; omega))
  by_cases h28 : q≤467
  ·
    exact four_is_representable 2 _ (c3_21_sound 4 q 0 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 2 _ (c3_22_sound 4 q 0 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_4_3_1 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+3)+1 : ℤ).toNat) := by
  by_cases h0 : q≤133
  ·
    exact four_is_representable 2 _ (c3_0_sound 4 q 1 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤165
  ·
    exact four_is_representable 2 _ (c3_14_sound 4 q 1 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤187
  ·
    exact four_is_representable 2 _ (c3_16_sound 4 q 1 (by norm_num) (by unfold c3_16; omega))
  by_cases h3 : q≤213
  ·
    exact four_is_representable 2 _ (c3_13_sound 4 q 1 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤214
  ·
    exact four_is_representable 2 _ (c3_26_sound 4 q 1 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤215
  ·
    have hq : q=215 := by omega
    subst q
    exact represent_exception 6905 (by decide +kernel)
  by_cases h6 : q≤216
  ·
    have hq : q=216 := by omega
    subst q
    exact represent_exception 6937 (by decide +kernel)
  by_cases h7 : q≤220
  ·
    exact four_is_representable 2 _ (c3_27_sound 4 q 1 (by norm_num) (by unfold c3_27; omega))
  by_cases h8 : q≤229
  ·
    exact four_is_representable 2 _ (c3_24_sound 4 q 1 (by norm_num) (by unfold c3_24; omega))
  by_cases h9 : q≤246
  ·
    exact four_is_representable 2 _ (c3_11_sound 4 q 1 (by norm_num) (by unfold c3_11; omega))
  by_cases h10 : q≤247
  ·
    have hq : q=247 := by omega
    subst q
    exact represent_exception 7929 (by decide +kernel)
  by_cases h11 : q≤278
  ·
    exact four_is_representable 2 _ (c3_15_sound 4 q 1 (by norm_num) (by unfold c3_15; omega))
  by_cases h12 : q≤294
  ·
    exact four_is_representable 2 _ (c3_17_sound 4 q 1 (by norm_num) (by unfold c3_17; omega))
  by_cases h13 : q≤297
  ·
    exact four_is_representable 2 _ (c3_19_sound 4 q 1 (by norm_num) (by unfold c3_19; omega))
  by_cases h14 : q≤298
  ·
    have hq : q=298 := by omega
    subst q
    exact represent_exception 9561 (by decide +kernel)
  by_cases h15 : q≤299
  ·
    have hq : q=299 := by omega
    subst q
    exact represent_exception 9593 (by decide +kernel)
  by_cases h16 : q≤300
  ·
    have hq : q=300 := by omega
    subst q
    exact represent_exception 9625 (by decide +kernel)
  by_cases h17 : q≤301
  ·
    have hq : q=301 := by omega
    subst q
    exact represent_exception 9657 (by decide +kernel)
  by_cases h18 : q≤302
  ·
    have hq : q=302 := by omega
    subst q
    exact represent_exception 9689 (by decide +kernel)
  by_cases h19 : q≤303
  ·
    have hq : q=303 := by omega
    subst q
    exact represent_exception 9721 (by decide +kernel)
  by_cases h20 : q≤304
  ·
    have hq : q=304 := by omega
    subst q
    exact represent_exception 9753 (by decide +kernel)
  by_cases h21 : q≤305
  ·
    have hq : q=305 := by omega
    subst q
    exact represent_exception 9785 (by decide +kernel)
  by_cases h22 : q≤306
  ·
    have hq : q=306 := by omega
    subst q
    exact represent_exception 9817 (by decide +kernel)
  by_cases h23 : q≤307
  ·
    have hq : q=307 := by omega
    subst q
    exact represent_exception 9849 (by decide +kernel)
  by_cases h24 : q≤308
  ·
    have hq : q=308 := by omega
    subst q
    exact represent_exception 9881 (by decide +kernel)
  by_cases h25 : q≤342
  ·
    exact four_is_representable 2 _ (c3_25_sound 4 q 1 (by norm_num) (by unfold c3_25; omega))
  by_cases h26 : q≤406
  ·
    exact four_is_representable 2 _ (c3_23_sound 4 q 1 (by norm_num) (by unfold c3_23; omega))
  by_cases h27 : q≤471
  ·
    exact four_is_representable 2 _ (c3_21_sound 4 q 1 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 2 _ (c3_22_sound 4 q 1 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_4_3_2 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+3)+2 : ℤ).toNat) := by
  by_cases h0 : q≤135
  ·
    exact four_is_representable 2 _ (c3_0_sound 4 q 2 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤167
  ·
    exact four_is_representable 2 _ (c3_14_sound 4 q 2 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤188
  ·
    exact four_is_representable 2 _ (c3_16_sound 4 q 2 (by norm_num) (by unfold c3_16; omega))
  by_cases h3 : q≤215
  ·
    exact four_is_representable 2 _ (c3_13_sound 4 q 2 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤216
  ·
    exact four_is_representable 2 _ (c3_26_sound 4 q 2 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤217
  ·
    have hq : q=217 := by omega
    subst q
    exact represent_exception 6970 (by decide +kernel)
  by_cases h6 : q≤218
  ·
    have hq : q=218 := by omega
    subst q
    exact represent_exception 7002 (by decide +kernel)
  by_cases h7 : q≤221
  ·
    exact four_is_representable 2 _ (c3_27_sound 4 q 2 (by norm_num) (by unfold c3_27; omega))
  by_cases h8 : q≤231
  ·
    exact four_is_representable 2 _ (c3_24_sound 4 q 2 (by norm_num) (by unfold c3_24; omega))
  by_cases h9 : q≤248
  ·
    exact four_is_representable 2 _ (c3_11_sound 4 q 2 (by norm_num) (by unfold c3_11; omega))
  by_cases h10 : q≤249
  ·
    have hq : q=249 := by omega
    subst q
    exact represent_exception 7994 (by decide +kernel)
  by_cases h11 : q≤280
  ·
    exact four_is_representable 2 _ (c3_15_sound 4 q 2 (by norm_num) (by unfold c3_15; omega))
  by_cases h12 : q≤296
  ·
    exact four_is_representable 2 _ (c3_17_sound 4 q 2 (by norm_num) (by unfold c3_17; omega))
  by_cases h13 : q≤301
  ·
    exact four_is_representable 2 _ (c3_19_sound 4 q 2 (by norm_num) (by unfold c3_19; omega))
  by_cases h14 : q≤302
  ·
    have hq : q=302 := by omega
    subst q
    exact represent_exception 9690 (by decide +kernel)
  by_cases h15 : q≤303
  ·
    have hq : q=303 := by omega
    subst q
    exact represent_exception 9722 (by decide +kernel)
  by_cases h16 : q≤304
  ·
    have hq : q=304 := by omega
    subst q
    exact represent_exception 9754 (by decide +kernel)
  by_cases h17 : q≤305
  ·
    have hq : q=305 := by omega
    subst q
    exact represent_exception 9786 (by decide +kernel)
  by_cases h18 : q≤306
  ·
    have hq : q=306 := by omega
    subst q
    exact represent_exception 9818 (by decide +kernel)
  by_cases h19 : q≤307
  ·
    have hq : q=307 := by omega
    subst q
    exact represent_exception 9850 (by decide +kernel)
  by_cases h20 : q≤308
  ·
    have hq : q=308 := by omega
    subst q
    exact represent_exception 9882 (by decide +kernel)
  by_cases h21 : q≤309
  ·
    have hq : q=309 := by omega
    subst q
    exact represent_exception 9914 (by decide +kernel)
  by_cases h22 : q≤346
  ·
    exact four_is_representable 2 _ (c3_25_sound 4 q 2 (by norm_num) (by unfold c3_25; omega))
  by_cases h23 : q≤410
  ·
    exact four_is_representable 2 _ (c3_23_sound 4 q 2 (by norm_num) (by unfold c3_23; omega))
  by_cases h24 : q≤475
  ·
    exact four_is_representable 2 _ (c3_21_sound 4 q 2 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 2 _ (c3_22_sound 4 q 2 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_4_3_3 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+3)+3 : ℤ).toNat) := by
  by_cases h0 : q≤137
  ·
    exact four_is_representable 2 _ (c3_0_sound 4 q 3 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤168
  ·
    exact four_is_representable 2 _ (c3_14_sound 4 q 3 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤189
  ·
    exact four_is_representable 2 _ (c3_16_sound 4 q 3 (by norm_num) (by unfold c3_16; omega))
  by_cases h3 : q≤217
  ·
    exact four_is_representable 2 _ (c3_13_sound 4 q 3 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤218
  ·
    exact four_is_representable 2 _ (c3_26_sound 4 q 3 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤219
  ·
    have hq : q=219 := by omega
    subst q
    exact represent_exception 7035 (by decide +kernel)
  by_cases h6 : q≤220
  ·
    have hq : q=220 := by omega
    subst q
    exact represent_exception 7067 (by decide +kernel)
  by_cases h7 : q≤222
  ·
    exact four_is_representable 2 _ (c3_27_sound 4 q 3 (by norm_num) (by unfold c3_27; omega))
  by_cases h8 : q≤233
  ·
    exact four_is_representable 2 _ (c3_24_sound 4 q 3 (by norm_num) (by unfold c3_24; omega))
  by_cases h9 : q≤250
  ·
    exact four_is_representable 2 _ (c3_11_sound 4 q 3 (by norm_num) (by unfold c3_11; omega))
  by_cases h10 : q≤251
  ·
    have hq : q=251 := by omega
    subst q
    exact represent_exception 8059 (by decide +kernel)
  by_cases h11 : q≤282
  ·
    exact four_is_representable 2 _ (c3_15_sound 4 q 3 (by norm_num) (by unfold c3_15; omega))
  by_cases h12 : q≤298
  ·
    exact four_is_representable 2 _ (c3_17_sound 4 q 3 (by norm_num) (by unfold c3_17; omega))
  by_cases h13 : q≤305
  ·
    exact four_is_representable 2 _ (c3_19_sound 4 q 3 (by norm_num) (by unfold c3_19; omega))
  by_cases h14 : q≤306
  ·
    have hq : q=306 := by omega
    subst q
    exact represent_exception 9819 (by decide +kernel)
  by_cases h15 : q≤307
  ·
    have hq : q=307 := by omega
    subst q
    exact represent_exception 9851 (by decide +kernel)
  by_cases h16 : q≤308
  ·
    have hq : q=308 := by omega
    subst q
    exact represent_exception 9883 (by decide +kernel)
  by_cases h17 : q≤309
  ·
    have hq : q=309 := by omega
    subst q
    exact represent_exception 9915 (by decide +kernel)
  by_cases h18 : q≤310
  ·
    have hq : q=310 := by omega
    subst q
    exact represent_exception 9947 (by decide +kernel)
  by_cases h19 : q≤350
  ·
    exact four_is_representable 2 _ (c3_25_sound 4 q 3 (by norm_num) (by unfold c3_25; omega))
  by_cases h20 : q≤414
  ·
    exact four_is_representable 2 _ (c3_23_sound 4 q 3 (by norm_num) (by unfold c3_23; omega))
  by_cases h21 : q≤479
  ·
    exact four_is_representable 2 _ (c3_21_sound 4 q 3 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 2 _ (c3_22_sound 4 q 3 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_4_3_4 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+3)+4 : ℤ).toNat) := by
  by_cases h0 : q≤139
  ·
    exact four_is_representable 2 _ (c3_0_sound 4 q 4 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤169
  ·
    exact four_is_representable 2 _ (c3_14_sound 4 q 4 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤190
  ·
    exact four_is_representable 2 _ (c3_16_sound 4 q 4 (by norm_num) (by unfold c3_16; omega))
  by_cases h3 : q≤219
  ·
    exact four_is_representable 2 _ (c3_13_sound 4 q 4 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤220
  ·
    exact four_is_representable 2 _ (c3_26_sound 4 q 4 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤221
  ·
    have hq : q=221 := by omega
    subst q
    exact represent_exception 7100 (by decide +kernel)
  by_cases h6 : q≤222
  ·
    have hq : q=222 := by omega
    subst q
    exact represent_exception 7132 (by decide +kernel)
  by_cases h7 : q≤235
  ·
    exact four_is_representable 2 _ (c3_24_sound 4 q 4 (by norm_num) (by unfold c3_24; omega))
  by_cases h8 : q≤252
  ·
    exact four_is_representable 2 _ (c3_11_sound 4 q 4 (by norm_num) (by unfold c3_11; omega))
  by_cases h9 : q≤253
  ·
    have hq : q=253 := by omega
    subst q
    exact represent_exception 8124 (by decide +kernel)
  by_cases h10 : q≤284
  ·
    exact four_is_representable 2 _ (c3_15_sound 4 q 4 (by norm_num) (by unfold c3_15; omega))
  by_cases h11 : q≤300
  ·
    exact four_is_representable 2 _ (c3_17_sound 4 q 4 (by norm_num) (by unfold c3_17; omega))
  by_cases h12 : q≤309
  ·
    exact four_is_representable 2 _ (c3_19_sound 4 q 4 (by norm_num) (by unfold c3_19; omega))
  by_cases h13 : q≤310
  ·
    have hq : q=310 := by omega
    subst q
    exact represent_exception 9948 (by decide +kernel)
  by_cases h14 : q≤311
  ·
    have hq : q=311 := by omega
    subst q
    exact represent_exception 9980 (by decide +kernel)
  by_cases h15 : q≤354
  ·
    exact four_is_representable 2 _ (c3_25_sound 4 q 4 (by norm_num) (by unfold c3_25; omega))
  by_cases h16 : q≤418
  ·
    exact four_is_representable 2 _ (c3_23_sound 4 q 4 (by norm_num) (by unfold c3_23; omega))
  by_cases h17 : q≤483
  ·
    exact four_is_representable 2 _ (c3_21_sound 4 q 4 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 2 _ (c3_22_sound 4 q 4 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_4_3_5 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+3)+5 : ℤ).toNat) := by
  by_cases h0 : q≤141
  ·
    exact four_is_representable 2 _ (c3_0_sound 4 q 5 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤170
  ·
    exact four_is_representable 2 _ (c3_14_sound 4 q 5 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤191
  ·
    exact four_is_representable 2 _ (c3_16_sound 4 q 5 (by norm_num) (by unfold c3_16; omega))
  by_cases h3 : q≤221
  ·
    exact four_is_representable 2 _ (c3_13_sound 4 q 5 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤222
  ·
    exact four_is_representable 2 _ (c3_26_sound 4 q 5 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤223
  ·
    have hq : q=223 := by omega
    subst q
    exact represent_exception 7165 (by decide +kernel)
  by_cases h6 : q≤237
  ·
    exact four_is_representable 2 _ (c3_24_sound 4 q 5 (by norm_num) (by unfold c3_24; omega))
  by_cases h7 : q≤254
  ·
    exact four_is_representable 2 _ (c3_11_sound 4 q 5 (by norm_num) (by unfold c3_11; omega))
  by_cases h8 : q≤255
  ·
    have hq : q=255 := by omega
    subst q
    exact represent_exception 8189 (by decide +kernel)
  by_cases h9 : q≤286
  ·
    exact four_is_representable 2 _ (c3_15_sound 4 q 5 (by norm_num) (by unfold c3_15; omega))
  by_cases h10 : q≤302
  ·
    exact four_is_representable 2 _ (c3_17_sound 4 q 5 (by norm_num) (by unfold c3_17; omega))
  by_cases h11 : q≤313
  ·
    exact four_is_representable 2 _ (c3_19_sound 4 q 5 (by norm_num) (by unfold c3_19; omega))
  by_cases h12 : q≤358
  ·
    exact four_is_representable 2 _ (c3_25_sound 4 q 5 (by norm_num) (by unfold c3_25; omega))
  by_cases h13 : q≤422
  ·
    exact four_is_representable 2 _ (c3_23_sound 4 q 5 (by norm_num) (by unfold c3_23; omega))
  by_cases h14 : q≤487
  ·
    exact four_is_representable 2 _ (c3_21_sound 4 q 5 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 2 _ (c3_22_sound 4 q 5 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_4_3_6 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+3)+6 : ℤ).toNat) := by
  by_cases h0 : q≤143
  ·
    exact four_is_representable 2 _ (c3_0_sound 4 q 6 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤171
  ·
    exact four_is_representable 2 _ (c3_14_sound 4 q 6 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤192
  ·
    exact four_is_representable 2 _ (c3_16_sound 4 q 6 (by norm_num) (by unfold c3_16; omega))
  by_cases h3 : q≤223
  ·
    exact four_is_representable 2 _ (c3_13_sound 4 q 6 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤224
  ·
    exact four_is_representable 2 _ (c3_26_sound 4 q 6 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤239
  ·
    exact four_is_representable 2 _ (c3_24_sound 4 q 6 (by norm_num) (by unfold c3_24; omega))
  by_cases h6 : q≤256
  ·
    exact four_is_representable 2 _ (c3_11_sound 4 q 6 (by norm_num) (by unfold c3_11; omega))
  by_cases h7 : q≤257
  ·
    have hq : q=257 := by omega
    subst q
    exact represent_exception 8254 (by decide +kernel)
  by_cases h8 : q≤288
  ·
    exact four_is_representable 2 _ (c3_15_sound 4 q 6 (by norm_num) (by unfold c3_15; omega))
  by_cases h9 : q≤304
  ·
    exact four_is_representable 2 _ (c3_17_sound 4 q 6 (by norm_num) (by unfold c3_17; omega))
  by_cases h10 : q≤317
  ·
    exact four_is_representable 2 _ (c3_19_sound 4 q 6 (by norm_num) (by unfold c3_19; omega))
  by_cases h11 : q≤362
  ·
    exact four_is_representable 2 _ (c3_25_sound 4 q 6 (by norm_num) (by unfold c3_25; omega))
  by_cases h12 : q≤426
  ·
    exact four_is_representable 2 _ (c3_23_sound 4 q 6 (by norm_num) (by unfold c3_23; omega))
  by_cases h13 : q≤491
  ·
    exact four_is_representable 2 _ (c3_21_sound 4 q 6 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 2 _ (c3_22_sound 4 q 6 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_4_3_7 (q : ℤ) (hlo : 128≤q) (hhi : q≤511) :
    Representable ((8*(4*q+3)+7 : ℤ).toNat) := by
  by_cases h0 : q≤145
  ·
    exact four_is_representable 2 _ (c3_0_sound 4 q 7 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤172
  ·
    exact four_is_representable 2 _ (c3_14_sound 4 q 7 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤193
  ·
    exact four_is_representable 2 _ (c3_16_sound 4 q 7 (by norm_num) (by unfold c3_16; omega))
  by_cases h3 : q≤194
  ·
    have hq : q=194 := by omega
    subst q
    exact represent_exception 6239 (by decide +kernel)
  by_cases h4 : q≤225
  ·
    exact four_is_representable 2 _ (c3_13_sound 4 q 7 (by norm_num) (by unfold c3_13; omega))
  by_cases h5 : q≤241
  ·
    exact four_is_representable 2 _ (c3_24_sound 4 q 7 (by norm_num) (by unfold c3_24; omega))
  by_cases h6 : q≤258
  ·
    exact four_is_representable 2 _ (c3_11_sound 4 q 7 (by norm_num) (by unfold c3_11; omega))
  by_cases h7 : q≤259
  ·
    have hq : q=259 := by omega
    subst q
    exact represent_exception 8319 (by decide +kernel)
  by_cases h8 : q≤289
  ·
    exact four_is_representable 2 _ (c3_15_sound 4 q 7 (by norm_num) (by unfold c3_15; omega))
  by_cases h9 : q≤290
  ·
    have hq : q=290 := by omega
    subst q
    exact represent_exception 9311 (by decide +kernel)
  by_cases h10 : q≤321
  ·
    exact four_is_representable 2 _ (c3_19_sound 4 q 7 (by norm_num) (by unfold c3_19; omega))
  by_cases h11 : q≤366
  ·
    exact four_is_representable 2 _ (c3_25_sound 4 q 7 (by norm_num) (by unfold c3_25; omega))
  by_cases h12 : q≤430
  ·
    exact four_is_representable 2 _ (c3_23_sound 4 q 7 (by norm_num) (by unfold c3_23; omega))
  by_cases h13 : q≤495
  ·
    exact four_is_representable 2 _ (c3_21_sound 4 q 7 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 2 _ (c3_22_sound 4 q 7 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_8_0_0 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+0)+0 : ℤ).toNat) := by
  by_cases h0 : q≤296
  ·
    exact four_is_representable 3 _ (c0_9_sound 8 q 0 (by norm_num) (by unfold c0_9; omega))
  by_cases h1 : q≤346
  ·
    exact four_is_representable 3 _ (c0_10_sound 8 q 0 (by norm_num) (by unfold c0_10; omega))
  by_cases h2 : q≤392
  ·
    exact four_is_representable 3 _ (c0_12_sound 8 q 0 (by norm_num) (by unfold c0_12; omega))
  by_cases h3 : q≤452
  ·
    exact four_is_representable 3 _ (c0_16_sound 8 q 0 (by norm_num) (by unfold c0_16; omega))
  by_cases h4 : q≤484
  ·
    exact four_is_representable 3 _ (c0_18_sound 8 q 0 (by norm_num) (by unfold c0_18; omega))
  by_cases h5 : q≤521
  ·
    exact four_is_representable 3 _ (c0_13_sound 8 q 0 (by norm_num) (by unfold c0_13; omega))
  by_cases h6 : q≤579
  ·
    exact four_is_representable 3 _ (c0_17_sound 8 q 0 (by norm_num) (by unfold c0_17; omega))
  by_cases h7 : q≤580
  ·
    have hq : q=580 := by omega
    subst q
    exact represent_exception 37120 (by decide +kernel)
  by_cases h8 : q≤670
  ·
    exact four_is_representable 3 _ (c0_6_sound 8 q 0 (by norm_num) (by unfold c0_6; omega))
  by_cases h9 : q≤759
  ·
    exact four_is_representable 3 _ (c0_19_sound 8 q 0 (by norm_num) (by unfold c0_19; omega))
  by_cases h10 : q≤887
  ·
    exact four_is_representable 3 _ (c0_11_sound 8 q 0 (by norm_num) (by unfold c0_11; omega))
  by_cases h11 : q≤1016
  ·
    exact four_is_representable 3 _ (c0_20_sound 8 q 0 (by norm_num) (by unfold c0_20; omega))
  exact four_is_representable 3 _ (c0_7_sound 8 q 0 (by norm_num) (by unfold c0_7; omega))

set_option maxRecDepth 10000 in
def middle_8_0_1 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+0)+1 : ℤ).toNat) := by
  by_cases h0 : q≤298
  ·
    exact four_is_representable 3 _ (c0_9_sound 8 q 1 (by norm_num) (by unfold c0_9; omega))
  by_cases h1 : q≤347
  ·
    exact four_is_representable 3 _ (c0_10_sound 8 q 1 (by norm_num) (by unfold c0_10; omega))
  by_cases h2 : q≤394
  ·
    exact four_is_representable 3 _ (c0_12_sound 8 q 1 (by norm_num) (by unfold c0_12; omega))
  by_cases h3 : q≤454
  ·
    exact four_is_representable 3 _ (c0_16_sound 8 q 1 (by norm_num) (by unfold c0_16; omega))
  by_cases h4 : q≤486
  ·
    exact four_is_representable 3 _ (c0_18_sound 8 q 1 (by norm_num) (by unfold c0_18; omega))
  by_cases h5 : q≤523
  ·
    exact four_is_representable 3 _ (c0_13_sound 8 q 1 (by norm_num) (by unfold c0_13; omega))
  by_cases h6 : q≤580
  ·
    exact four_is_representable 3 _ (c0_17_sound 8 q 1 (by norm_num) (by unfold c0_17; omega))
  by_cases h7 : q≤581
  ·
    have hq : q=581 := by omega
    subst q
    exact represent_exception 37185 (by decide +kernel)
  by_cases h8 : q≤674
  ·
    exact four_is_representable 3 _ (c0_6_sound 8 q 1 (by norm_num) (by unfold c0_6; omega))
  by_cases h9 : q≤763
  ·
    exact four_is_representable 3 _ (c0_19_sound 8 q 1 (by norm_num) (by unfold c0_19; omega))
  by_cases h10 : q≤891
  ·
    exact four_is_representable 3 _ (c0_11_sound 8 q 1 (by norm_num) (by unfold c0_11; omega))
  by_cases h11 : q≤1020
  ·
    exact four_is_representable 3 _ (c0_20_sound 8 q 1 (by norm_num) (by unfold c0_20; omega))
  exact four_is_representable 3 _ (c0_7_sound 8 q 1 (by norm_num) (by unfold c0_7; omega))

set_option maxRecDepth 10000 in
def middle_8_0_2 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+0)+2 : ℤ).toNat) := by
  by_cases h0 : q≤300
  ·
    exact four_is_representable 3 _ (c0_9_sound 8 q 2 (by norm_num) (by unfold c0_9; omega))
  by_cases h1 : q≤348
  ·
    exact four_is_representable 3 _ (c0_10_sound 8 q 2 (by norm_num) (by unfold c0_10; omega))
  by_cases h2 : q≤396
  ·
    exact four_is_representable 3 _ (c0_12_sound 8 q 2 (by norm_num) (by unfold c0_12; omega))
  by_cases h3 : q≤456
  ·
    exact four_is_representable 3 _ (c0_16_sound 8 q 2 (by norm_num) (by unfold c0_16; omega))
  by_cases h4 : q≤488
  ·
    exact four_is_representable 3 _ (c0_18_sound 8 q 2 (by norm_num) (by unfold c0_18; omega))
  by_cases h5 : q≤525
  ·
    exact four_is_representable 3 _ (c0_13_sound 8 q 2 (by norm_num) (by unfold c0_13; omega))
  by_cases h6 : q≤581
  ·
    exact four_is_representable 3 _ (c0_17_sound 8 q 2 (by norm_num) (by unfold c0_17; omega))
  by_cases h7 : q≤582
  ·
    have hq : q=582 := by omega
    subst q
    exact represent_exception 37250 (by decide +kernel)
  by_cases h8 : q≤678
  ·
    exact four_is_representable 3 _ (c0_6_sound 8 q 2 (by norm_num) (by unfold c0_6; omega))
  by_cases h9 : q≤767
  ·
    exact four_is_representable 3 _ (c0_19_sound 8 q 2 (by norm_num) (by unfold c0_19; omega))
  by_cases h10 : q≤895
  ·
    exact four_is_representable 3 _ (c0_11_sound 8 q 2 (by norm_num) (by unfold c0_11; omega))
  exact four_is_representable 3 _ (c0_20_sound 8 q 2 (by norm_num) (by unfold c0_20; omega))

set_option maxRecDepth 10000 in
def middle_8_0_3 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+0)+3 : ℤ).toNat) := by
  by_cases h0 : q≤302
  ·
    exact four_is_representable 3 _ (c0_9_sound 8 q 3 (by norm_num) (by unfold c0_9; omega))
  by_cases h1 : q≤349
  ·
    exact four_is_representable 3 _ (c0_10_sound 8 q 3 (by norm_num) (by unfold c0_10; omega))
  by_cases h2 : q≤390
  ·
    exact four_is_representable 3 _ (c0_14_sound 8 q 3 (by norm_num) (by unfold c0_14; omega))
  by_cases h3 : q≤398
  ·
    exact four_is_representable 3 _ (c0_12_sound 8 q 3 (by norm_num) (by unfold c0_12; omega))
  by_cases h4 : q≤458
  ·
    exact four_is_representable 3 _ (c0_16_sound 8 q 3 (by norm_num) (by unfold c0_16; omega))
  by_cases h5 : q≤490
  ·
    exact four_is_representable 3 _ (c0_18_sound 8 q 3 (by norm_num) (by unfold c0_18; omega))
  by_cases h6 : q≤527
  ·
    exact four_is_representable 3 _ (c0_13_sound 8 q 3 (by norm_num) (by unfold c0_13; omega))
  by_cases h7 : q≤582
  ·
    exact four_is_representable 3 _ (c0_17_sound 8 q 3 (by norm_num) (by unfold c0_17; omega))
  by_cases h8 : q≤583
  ·
    have hq : q=583 := by omega
    subst q
    exact represent_exception 37315 (by decide +kernel)
  by_cases h9 : q≤682
  ·
    exact four_is_representable 3 _ (c0_6_sound 8 q 3 (by norm_num) (by unfold c0_6; omega))
  by_cases h10 : q≤771
  ·
    exact four_is_representable 3 _ (c0_19_sound 8 q 3 (by norm_num) (by unfold c0_19; omega))
  by_cases h11 : q≤899
  ·
    exact four_is_representable 3 _ (c0_11_sound 8 q 3 (by norm_num) (by unfold c0_11; omega))
  exact four_is_representable 3 _ (c0_20_sound 8 q 3 (by norm_num) (by unfold c0_20; omega))

set_option maxRecDepth 10000 in
def middle_8_0_4 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+0)+4 : ℤ).toNat) := by
  by_cases h0 : q≤304
  ·
    exact four_is_representable 3 _ (c0_9_sound 8 q 4 (by norm_num) (by unfold c0_9; omega))
  by_cases h1 : q≤350
  ·
    exact four_is_representable 3 _ (c0_10_sound 8 q 4 (by norm_num) (by unfold c0_10; omega))
  by_cases h2 : q≤391
  ·
    exact four_is_representable 3 _ (c0_14_sound 8 q 4 (by norm_num) (by unfold c0_14; omega))
  by_cases h3 : q≤400
  ·
    exact four_is_representable 3 _ (c0_12_sound 8 q 4 (by norm_num) (by unfold c0_12; omega))
  by_cases h4 : q≤460
  ·
    exact four_is_representable 3 _ (c0_16_sound 8 q 4 (by norm_num) (by unfold c0_16; omega))
  by_cases h5 : q≤492
  ·
    exact four_is_representable 3 _ (c0_18_sound 8 q 4 (by norm_num) (by unfold c0_18; omega))
  by_cases h6 : q≤529
  ·
    exact four_is_representable 3 _ (c0_13_sound 8 q 4 (by norm_num) (by unfold c0_13; omega))
  by_cases h7 : q≤583
  ·
    exact four_is_representable 3 _ (c0_17_sound 8 q 4 (by norm_num) (by unfold c0_17; omega))
  by_cases h8 : q≤584
  ·
    have hq : q=584 := by omega
    subst q
    exact represent_exception 37380 (by decide +kernel)
  by_cases h9 : q≤686
  ·
    exact four_is_representable 3 _ (c0_6_sound 8 q 4 (by norm_num) (by unfold c0_6; omega))
  by_cases h10 : q≤775
  ·
    exact four_is_representable 3 _ (c0_19_sound 8 q 4 (by norm_num) (by unfold c0_19; omega))
  by_cases h11 : q≤903
  ·
    exact four_is_representable 3 _ (c0_11_sound 8 q 4 (by norm_num) (by unfold c0_11; omega))
  exact four_is_representable 3 _ (c0_20_sound 8 q 4 (by norm_num) (by unfold c0_20; omega))

set_option maxRecDepth 10000 in
def middle_8_0_5 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+0)+5 : ℤ).toNat) := by
  by_cases h0 : q≤306
  ·
    exact four_is_representable 3 _ (c0_9_sound 8 q 5 (by norm_num) (by unfold c0_9; omega))
  by_cases h1 : q≤351
  ·
    exact four_is_representable 3 _ (c0_10_sound 8 q 5 (by norm_num) (by unfold c0_10; omega))
  by_cases h2 : q≤392
  ·
    exact four_is_representable 3 _ (c0_14_sound 8 q 5 (by norm_num) (by unfold c0_14; omega))
  by_cases h3 : q≤402
  ·
    exact four_is_representable 3 _ (c0_12_sound 8 q 5 (by norm_num) (by unfold c0_12; omega))
  by_cases h4 : q≤462
  ·
    exact four_is_representable 3 _ (c0_16_sound 8 q 5 (by norm_num) (by unfold c0_16; omega))
  by_cases h5 : q≤494
  ·
    exact four_is_representable 3 _ (c0_18_sound 8 q 5 (by norm_num) (by unfold c0_18; omega))
  by_cases h6 : q≤531
  ·
    exact four_is_representable 3 _ (c0_13_sound 8 q 5 (by norm_num) (by unfold c0_13; omega))
  by_cases h7 : q≤584
  ·
    exact four_is_representable 3 _ (c0_17_sound 8 q 5 (by norm_num) (by unfold c0_17; omega))
  by_cases h8 : q≤585
  ·
    have hq : q=585 := by omega
    subst q
    exact represent_exception 37445 (by decide +kernel)
  by_cases h9 : q≤690
  ·
    exact four_is_representable 3 _ (c0_6_sound 8 q 5 (by norm_num) (by unfold c0_6; omega))
  by_cases h10 : q≤779
  ·
    exact four_is_representable 3 _ (c0_19_sound 8 q 5 (by norm_num) (by unfold c0_19; omega))
  by_cases h11 : q≤907
  ·
    exact four_is_representable 3 _ (c0_11_sound 8 q 5 (by norm_num) (by unfold c0_11; omega))
  exact four_is_representable 3 _ (c0_20_sound 8 q 5 (by norm_num) (by unfold c0_20; omega))

set_option maxRecDepth 10000 in
def middle_8_0_6 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+0)+6 : ℤ).toNat) := by
  by_cases h0 : q≤308
  ·
    exact four_is_representable 3 _ (c0_9_sound 8 q 6 (by norm_num) (by unfold c0_9; omega))
  by_cases h1 : q≤352
  ·
    exact four_is_representable 3 _ (c0_10_sound 8 q 6 (by norm_num) (by unfold c0_10; omega))
  by_cases h2 : q≤393
  ·
    exact four_is_representable 3 _ (c0_14_sound 8 q 6 (by norm_num) (by unfold c0_14; omega))
  by_cases h3 : q≤404
  ·
    exact four_is_representable 3 _ (c0_12_sound 8 q 6 (by norm_num) (by unfold c0_12; omega))
  by_cases h4 : q≤464
  ·
    exact four_is_representable 3 _ (c0_16_sound 8 q 6 (by norm_num) (by unfold c0_16; omega))
  by_cases h5 : q≤496
  ·
    exact four_is_representable 3 _ (c0_18_sound 8 q 6 (by norm_num) (by unfold c0_18; omega))
  by_cases h6 : q≤533
  ·
    exact four_is_representable 3 _ (c0_13_sound 8 q 6 (by norm_num) (by unfold c0_13; omega))
  by_cases h7 : q≤585
  ·
    exact four_is_representable 3 _ (c0_17_sound 8 q 6 (by norm_num) (by unfold c0_17; omega))
  by_cases h8 : q≤586
  ·
    have hq : q=586 := by omega
    subst q
    exact represent_exception 37510 (by decide +kernel)
  by_cases h9 : q≤694
  ·
    exact four_is_representable 3 _ (c0_6_sound 8 q 6 (by norm_num) (by unfold c0_6; omega))
  by_cases h10 : q≤783
  ·
    exact four_is_representable 3 _ (c0_19_sound 8 q 6 (by norm_num) (by unfold c0_19; omega))
  by_cases h11 : q≤911
  ·
    exact four_is_representable 3 _ (c0_11_sound 8 q 6 (by norm_num) (by unfold c0_11; omega))
  exact four_is_representable 3 _ (c0_20_sound 8 q 6 (by norm_num) (by unfold c0_20; omega))

set_option maxRecDepth 10000 in
def middle_8_0_7 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+0)+7 : ℤ).toNat) := by
  by_cases h0 : q≤310
  ·
    exact four_is_representable 3 _ (c0_9_sound 8 q 7 (by norm_num) (by unfold c0_9; omega))
  by_cases h1 : q≤353
  ·
    exact four_is_representable 3 _ (c0_10_sound 8 q 7 (by norm_num) (by unfold c0_10; omega))
  by_cases h2 : q≤394
  ·
    exact four_is_representable 3 _ (c0_14_sound 8 q 7 (by norm_num) (by unfold c0_14; omega))
  by_cases h3 : q≤406
  ·
    exact four_is_representable 3 _ (c0_12_sound 8 q 7 (by norm_num) (by unfold c0_12; omega))
  by_cases h4 : q≤466
  ·
    exact four_is_representable 3 _ (c0_16_sound 8 q 7 (by norm_num) (by unfold c0_16; omega))
  by_cases h5 : q≤498
  ·
    exact four_is_representable 3 _ (c0_18_sound 8 q 7 (by norm_num) (by unfold c0_18; omega))
  by_cases h6 : q≤535
  ·
    exact four_is_representable 3 _ (c0_13_sound 8 q 7 (by norm_num) (by unfold c0_13; omega))
  by_cases h7 : q≤586
  ·
    exact four_is_representable 3 _ (c0_17_sound 8 q 7 (by norm_num) (by unfold c0_17; omega))
  by_cases h8 : q≤587
  ·
    have hq : q=587 := by omega
    subst q
    exact represent_exception 37575 (by decide +kernel)
  by_cases h9 : q≤698
  ·
    exact four_is_representable 3 _ (c0_6_sound 8 q 7 (by norm_num) (by unfold c0_6; omega))
  by_cases h10 : q≤787
  ·
    exact four_is_representable 3 _ (c0_19_sound 8 q 7 (by norm_num) (by unfold c0_19; omega))
  by_cases h11 : q≤915
  ·
    exact four_is_representable 3 _ (c0_11_sound 8 q 7 (by norm_num) (by unfold c0_11; omega))
  exact four_is_representable 3 _ (c0_20_sound 8 q 7 (by norm_num) (by unfold c0_20; omega))

set_option maxRecDepth 10000 in
def middle_8_0_8 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+0)+8 : ℤ).toNat) := by
  by_cases h0 : q≤312
  ·
    exact four_is_representable 3 _ (c0_9_sound 8 q 8 (by norm_num) (by unfold c0_9; omega))
  by_cases h1 : q≤354
  ·
    exact four_is_representable 3 _ (c0_10_sound 8 q 8 (by norm_num) (by unfold c0_10; omega))
  by_cases h2 : q≤395
  ·
    exact four_is_representable 3 _ (c0_14_sound 8 q 8 (by norm_num) (by unfold c0_14; omega))
  by_cases h3 : q≤408
  ·
    exact four_is_representable 3 _ (c0_12_sound 8 q 8 (by norm_num) (by unfold c0_12; omega))
  by_cases h4 : q≤468
  ·
    exact four_is_representable 3 _ (c0_16_sound 8 q 8 (by norm_num) (by unfold c0_16; omega))
  by_cases h5 : q≤500
  ·
    exact four_is_representable 3 _ (c0_18_sound 8 q 8 (by norm_num) (by unfold c0_18; omega))
  by_cases h6 : q≤537
  ·
    exact four_is_representable 3 _ (c0_13_sound 8 q 8 (by norm_num) (by unfold c0_13; omega))
  by_cases h7 : q≤587
  ·
    exact four_is_representable 3 _ (c0_17_sound 8 q 8 (by norm_num) (by unfold c0_17; omega))
  by_cases h8 : q≤588
  ·
    have hq : q=588 := by omega
    subst q
    exact represent_exception 37640 (by decide +kernel)
  by_cases h9 : q≤702
  ·
    exact four_is_representable 3 _ (c0_6_sound 8 q 8 (by norm_num) (by unfold c0_6; omega))
  by_cases h10 : q≤791
  ·
    exact four_is_representable 3 _ (c0_19_sound 8 q 8 (by norm_num) (by unfold c0_19; omega))
  by_cases h11 : q≤919
  ·
    exact four_is_representable 3 _ (c0_11_sound 8 q 8 (by norm_num) (by unfold c0_11; omega))
  exact four_is_representable 3 _ (c0_20_sound 8 q 8 (by norm_num) (by unfold c0_20; omega))

set_option maxRecDepth 10000 in
def middle_8_0_9 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+0)+9 : ℤ).toNat) := by
  by_cases h0 : q≤314
  ·
    exact four_is_representable 3 _ (c0_9_sound 8 q 9 (by norm_num) (by unfold c0_9; omega))
  by_cases h1 : q≤355
  ·
    exact four_is_representable 3 _ (c0_10_sound 8 q 9 (by norm_num) (by unfold c0_10; omega))
  by_cases h2 : q≤396
  ·
    exact four_is_representable 3 _ (c0_14_sound 8 q 9 (by norm_num) (by unfold c0_14; omega))
  by_cases h3 : q≤410
  ·
    exact four_is_representable 3 _ (c0_12_sound 8 q 9 (by norm_num) (by unfold c0_12; omega))
  by_cases h4 : q≤470
  ·
    exact four_is_representable 3 _ (c0_16_sound 8 q 9 (by norm_num) (by unfold c0_16; omega))
  by_cases h5 : q≤502
  ·
    exact four_is_representable 3 _ (c0_18_sound 8 q 9 (by norm_num) (by unfold c0_18; omega))
  by_cases h6 : q≤539
  ·
    exact four_is_representable 3 _ (c0_13_sound 8 q 9 (by norm_num) (by unfold c0_13; omega))
  by_cases h7 : q≤588
  ·
    exact four_is_representable 3 _ (c0_17_sound 8 q 9 (by norm_num) (by unfold c0_17; omega))
  by_cases h8 : q≤589
  ·
    have hq : q=589 := by omega
    subst q
    exact represent_exception 37705 (by decide +kernel)
  by_cases h9 : q≤706
  ·
    exact four_is_representable 3 _ (c0_6_sound 8 q 9 (by norm_num) (by unfold c0_6; omega))
  by_cases h10 : q≤795
  ·
    exact four_is_representable 3 _ (c0_19_sound 8 q 9 (by norm_num) (by unfold c0_19; omega))
  by_cases h11 : q≤923
  ·
    exact four_is_representable 3 _ (c0_11_sound 8 q 9 (by norm_num) (by unfold c0_11; omega))
  exact four_is_representable 3 _ (c0_20_sound 8 q 9 (by norm_num) (by unfold c0_20; omega))

set_option maxRecDepth 10000 in
def middle_8_0_10 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+0)+10 : ℤ).toNat) := by
  by_cases h0 : q≤316
  ·
    exact four_is_representable 3 _ (c0_9_sound 8 q 10 (by norm_num) (by unfold c0_9; omega))
  by_cases h1 : q≤356
  ·
    exact four_is_representable 3 _ (c0_10_sound 8 q 10 (by norm_num) (by unfold c0_10; omega))
  by_cases h2 : q≤397
  ·
    exact four_is_representable 3 _ (c0_14_sound 8 q 10 (by norm_num) (by unfold c0_14; omega))
  by_cases h3 : q≤412
  ·
    exact four_is_representable 3 _ (c0_12_sound 8 q 10 (by norm_num) (by unfold c0_12; omega))
  by_cases h4 : q≤472
  ·
    exact four_is_representable 3 _ (c0_16_sound 8 q 10 (by norm_num) (by unfold c0_16; omega))
  by_cases h5 : q≤504
  ·
    exact four_is_representable 3 _ (c0_18_sound 8 q 10 (by norm_num) (by unfold c0_18; omega))
  by_cases h6 : q≤541
  ·
    exact four_is_representable 3 _ (c0_13_sound 8 q 10 (by norm_num) (by unfold c0_13; omega))
  by_cases h7 : q≤589
  ·
    exact four_is_representable 3 _ (c0_17_sound 8 q 10 (by norm_num) (by unfold c0_17; omega))
  by_cases h8 : q≤590
  ·
    have hq : q=590 := by omega
    subst q
    exact represent_exception 37770 (by decide +kernel)
  by_cases h9 : q≤710
  ·
    exact four_is_representable 3 _ (c0_6_sound 8 q 10 (by norm_num) (by unfold c0_6; omega))
  by_cases h10 : q≤799
  ·
    exact four_is_representable 3 _ (c0_19_sound 8 q 10 (by norm_num) (by unfold c0_19; omega))
  by_cases h11 : q≤927
  ·
    exact four_is_representable 3 _ (c0_11_sound 8 q 10 (by norm_num) (by unfold c0_11; omega))
  exact four_is_representable 3 _ (c0_20_sound 8 q 10 (by norm_num) (by unfold c0_20; omega))

set_option maxRecDepth 10000 in
def middle_8_0_11 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+0)+11 : ℤ).toNat) := by
  by_cases h0 : q≤318
  ·
    exact four_is_representable 3 _ (c0_9_sound 8 q 11 (by norm_num) (by unfold c0_9; omega))
  by_cases h1 : q≤357
  ·
    exact four_is_representable 3 _ (c0_10_sound 8 q 11 (by norm_num) (by unfold c0_10; omega))
  by_cases h2 : q≤398
  ·
    exact four_is_representable 3 _ (c0_14_sound 8 q 11 (by norm_num) (by unfold c0_14; omega))
  by_cases h3 : q≤414
  ·
    exact four_is_representable 3 _ (c0_12_sound 8 q 11 (by norm_num) (by unfold c0_12; omega))
  by_cases h4 : q≤474
  ·
    exact four_is_representable 3 _ (c0_16_sound 8 q 11 (by norm_num) (by unfold c0_16; omega))
  by_cases h5 : q≤506
  ·
    exact four_is_representable 3 _ (c0_18_sound 8 q 11 (by norm_num) (by unfold c0_18; omega))
  by_cases h6 : q≤543
  ·
    exact four_is_representable 3 _ (c0_13_sound 8 q 11 (by norm_num) (by unfold c0_13; omega))
  by_cases h7 : q≤590
  ·
    exact four_is_representable 3 _ (c0_17_sound 8 q 11 (by norm_num) (by unfold c0_17; omega))
  by_cases h8 : q≤591
  ·
    have hq : q=591 := by omega
    subst q
    exact represent_exception 37835 (by decide +kernel)
  by_cases h9 : q≤714
  ·
    exact four_is_representable 3 _ (c0_6_sound 8 q 11 (by norm_num) (by unfold c0_6; omega))
  by_cases h10 : q≤803
  ·
    exact four_is_representable 3 _ (c0_19_sound 8 q 11 (by norm_num) (by unfold c0_19; omega))
  by_cases h11 : q≤931
  ·
    exact four_is_representable 3 _ (c0_11_sound 8 q 11 (by norm_num) (by unfold c0_11; omega))
  exact four_is_representable 3 _ (c0_20_sound 8 q 11 (by norm_num) (by unfold c0_20; omega))

set_option maxRecDepth 10000 in
def middle_8_0_12 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+0)+12 : ℤ).toNat) := by
  by_cases h0 : q≤320
  ·
    exact four_is_representable 3 _ (c0_9_sound 8 q 12 (by norm_num) (by unfold c0_9; omega))
  by_cases h1 : q≤358
  ·
    exact four_is_representable 3 _ (c0_10_sound 8 q 12 (by norm_num) (by unfold c0_10; omega))
  by_cases h2 : q≤399
  ·
    exact four_is_representable 3 _ (c0_14_sound 8 q 12 (by norm_num) (by unfold c0_14; omega))
  by_cases h3 : q≤416
  ·
    exact four_is_representable 3 _ (c0_12_sound 8 q 12 (by norm_num) (by unfold c0_12; omega))
  by_cases h4 : q≤476
  ·
    exact four_is_representable 3 _ (c0_16_sound 8 q 12 (by norm_num) (by unfold c0_16; omega))
  by_cases h5 : q≤508
  ·
    exact four_is_representable 3 _ (c0_18_sound 8 q 12 (by norm_num) (by unfold c0_18; omega))
  by_cases h6 : q≤545
  ·
    exact four_is_representable 3 _ (c0_13_sound 8 q 12 (by norm_num) (by unfold c0_13; omega))
  by_cases h7 : q≤591
  ·
    exact four_is_representable 3 _ (c0_17_sound 8 q 12 (by norm_num) (by unfold c0_17; omega))
  by_cases h8 : q≤592
  ·
    have hq : q=592 := by omega
    subst q
    exact represent_exception 37900 (by decide +kernel)
  by_cases h9 : q≤718
  ·
    exact four_is_representable 3 _ (c0_6_sound 8 q 12 (by norm_num) (by unfold c0_6; omega))
  by_cases h10 : q≤807
  ·
    exact four_is_representable 3 _ (c0_19_sound 8 q 12 (by norm_num) (by unfold c0_19; omega))
  by_cases h11 : q≤935
  ·
    exact four_is_representable 3 _ (c0_11_sound 8 q 12 (by norm_num) (by unfold c0_11; omega))
  exact four_is_representable 3 _ (c0_20_sound 8 q 12 (by norm_num) (by unfold c0_20; omega))

set_option maxRecDepth 10000 in
def middle_8_0_13 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+0)+13 : ℤ).toNat) := by
  by_cases h0 : q≤265
  ·
    exact four_is_representable 3 _ (c0_21_sound 8 q 13 (by norm_num) (by unfold c0_21; omega))
  by_cases h1 : q≤322
  ·
    exact four_is_representable 3 _ (c0_9_sound 8 q 13 (by norm_num) (by unfold c0_9; omega))
  by_cases h2 : q≤359
  ·
    exact four_is_representable 3 _ (c0_10_sound 8 q 13 (by norm_num) (by unfold c0_10; omega))
  by_cases h3 : q≤400
  ·
    exact four_is_representable 3 _ (c0_14_sound 8 q 13 (by norm_num) (by unfold c0_14; omega))
  by_cases h4 : q≤418
  ·
    exact four_is_representable 3 _ (c0_12_sound 8 q 13 (by norm_num) (by unfold c0_12; omega))
  by_cases h5 : q≤478
  ·
    exact four_is_representable 3 _ (c0_16_sound 8 q 13 (by norm_num) (by unfold c0_16; omega))
  by_cases h6 : q≤510
  ·
    exact four_is_representable 3 _ (c0_18_sound 8 q 13 (by norm_num) (by unfold c0_18; omega))
  by_cases h7 : q≤547
  ·
    exact four_is_representable 3 _ (c0_13_sound 8 q 13 (by norm_num) (by unfold c0_13; omega))
  by_cases h8 : q≤592
  ·
    exact four_is_representable 3 _ (c0_17_sound 8 q 13 (by norm_num) (by unfold c0_17; omega))
  by_cases h9 : q≤594
  ·
    exact four_is_representable 3 _ (c0_22_sound 8 q 13 (by norm_num) (by unfold c0_22; omega))
  by_cases h10 : q≤722
  ·
    exact four_is_representable 3 _ (c0_6_sound 8 q 13 (by norm_num) (by unfold c0_6; omega))
  by_cases h11 : q≤811
  ·
    exact four_is_representable 3 _ (c0_19_sound 8 q 13 (by norm_num) (by unfold c0_19; omega))
  by_cases h12 : q≤939
  ·
    exact four_is_representable 3 _ (c0_11_sound 8 q 13 (by norm_num) (by unfold c0_11; omega))
  exact four_is_representable 3 _ (c0_20_sound 8 q 13 (by norm_num) (by unfold c0_20; omega))

set_option maxRecDepth 10000 in
def middle_8_0_14 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+0)+14 : ℤ).toNat) := by
  by_cases h0 : q≤267
  ·
    exact four_is_representable 3 _ (c0_21_sound 8 q 14 (by norm_num) (by unfold c0_21; omega))
  by_cases h1 : q≤324
  ·
    exact four_is_representable 3 _ (c0_9_sound 8 q 14 (by norm_num) (by unfold c0_9; omega))
  by_cases h2 : q≤360
  ·
    exact four_is_representable 3 _ (c0_10_sound 8 q 14 (by norm_num) (by unfold c0_10; omega))
  by_cases h3 : q≤401
  ·
    exact four_is_representable 3 _ (c0_14_sound 8 q 14 (by norm_num) (by unfold c0_14; omega))
  by_cases h4 : q≤420
  ·
    exact four_is_representable 3 _ (c0_12_sound 8 q 14 (by norm_num) (by unfold c0_12; omega))
  by_cases h5 : q≤480
  ·
    exact four_is_representable 3 _ (c0_16_sound 8 q 14 (by norm_num) (by unfold c0_16; omega))
  by_cases h6 : q≤512
  ·
    exact four_is_representable 3 _ (c0_18_sound 8 q 14 (by norm_num) (by unfold c0_18; omega))
  by_cases h7 : q≤549
  ·
    exact four_is_representable 3 _ (c0_13_sound 8 q 14 (by norm_num) (by unfold c0_13; omega))
  by_cases h8 : q≤593
  ·
    exact four_is_representable 3 _ (c0_17_sound 8 q 14 (by norm_num) (by unfold c0_17; omega))
  by_cases h9 : q≤598
  ·
    exact four_is_representable 3 _ (c0_22_sound 8 q 14 (by norm_num) (by unfold c0_22; omega))
  by_cases h10 : q≤726
  ·
    exact four_is_representable 3 _ (c0_6_sound 8 q 14 (by norm_num) (by unfold c0_6; omega))
  by_cases h11 : q≤815
  ·
    exact four_is_representable 3 _ (c0_19_sound 8 q 14 (by norm_num) (by unfold c0_19; omega))
  by_cases h12 : q≤943
  ·
    exact four_is_representable 3 _ (c0_11_sound 8 q 14 (by norm_num) (by unfold c0_11; omega))
  exact four_is_representable 3 _ (c0_20_sound 8 q 14 (by norm_num) (by unfold c0_20; omega))

set_option maxRecDepth 10000 in
def middle_8_0_15 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+0)+15 : ℤ).toNat) := by
  by_cases h0 : q≤269
  ·
    exact four_is_representable 3 _ (c0_21_sound 8 q 15 (by norm_num) (by unfold c0_21; omega))
  by_cases h1 : q≤326
  ·
    exact four_is_representable 3 _ (c0_9_sound 8 q 15 (by norm_num) (by unfold c0_9; omega))
  by_cases h2 : q≤361
  ·
    exact four_is_representable 3 _ (c0_10_sound 8 q 15 (by norm_num) (by unfold c0_10; omega))
  by_cases h3 : q≤402
  ·
    exact four_is_representable 3 _ (c0_14_sound 8 q 15 (by norm_num) (by unfold c0_14; omega))
  by_cases h4 : q≤422
  ·
    exact four_is_representable 3 _ (c0_12_sound 8 q 15 (by norm_num) (by unfold c0_12; omega))
  by_cases h5 : q≤482
  ·
    exact four_is_representable 3 _ (c0_16_sound 8 q 15 (by norm_num) (by unfold c0_16; omega))
  by_cases h6 : q≤514
  ·
    exact four_is_representable 3 _ (c0_18_sound 8 q 15 (by norm_num) (by unfold c0_18; omega))
  by_cases h7 : q≤551
  ·
    exact four_is_representable 3 _ (c0_13_sound 8 q 15 (by norm_num) (by unfold c0_13; omega))
  by_cases h8 : q≤594
  ·
    exact four_is_representable 3 _ (c0_17_sound 8 q 15 (by norm_num) (by unfold c0_17; omega))
  by_cases h9 : q≤602
  ·
    exact four_is_representable 3 _ (c0_22_sound 8 q 15 (by norm_num) (by unfold c0_22; omega))
  by_cases h10 : q≤730
  ·
    exact four_is_representable 3 _ (c0_6_sound 8 q 15 (by norm_num) (by unfold c0_6; omega))
  by_cases h11 : q≤819
  ·
    exact four_is_representable 3 _ (c0_19_sound 8 q 15 (by norm_num) (by unfold c0_19; omega))
  by_cases h12 : q≤947
  ·
    exact four_is_representable 3 _ (c0_11_sound 8 q 15 (by norm_num) (by unfold c0_11; omega))
  exact four_is_representable 3 _ (c0_20_sound 8 q 15 (by norm_num) (by unfold c0_20; omega))

set_option maxRecDepth 10000 in
def middle_8_1_0 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+1)+0 : ℤ).toNat) := by
  by_cases h0 : q≤263
  ·
    exact four_is_representable 3 _ (c1_17_sound 8 q 0 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤328
  ·
    exact four_is_representable 3 _ (c1_16_sound 8 q 0 (by norm_num) (by unfold c1_16; omega))
  by_cases h2 : q≤362
  ·
    exact four_is_representable 3 _ (c1_11_sound 8 q 0 (by norm_num) (by unfold c1_11; omega))
  by_cases h3 : q≤403
  ·
    exact four_is_representable 3 _ (c1_9_sound 8 q 0 (by norm_num) (by unfold c1_9; omega))
  by_cases h4 : q≤424
  ·
    exact four_is_representable 3 _ (c1_13_sound 8 q 0 (by norm_num) (by unfold c1_13; omega))
  by_cases h5 : q≤484
  ·
    exact four_is_representable 3 _ (c1_19_sound 8 q 0 (by norm_num) (by unfold c1_19; omega))
  by_cases h6 : q≤516
  ·
    exact four_is_representable 3 _ (c1_5_sound 8 q 0 (by norm_num) (by unfold c1_5; omega))
  by_cases h7 : q≤553
  ·
    exact four_is_representable 3 _ (c1_12_sound 8 q 0 (by norm_num) (by unfold c1_12; omega))
  by_cases h8 : q≤595
  ·
    exact four_is_representable 3 _ (c1_8_sound 8 q 0 (by norm_num) (by unfold c1_8; omega))
  by_cases h9 : q≤606
  ·
    exact four_is_representable 3 _ (c1_21_sound 8 q 0 (by norm_num) (by unfold c1_21; omega))
  by_cases h10 : q≤734
  ·
    exact four_is_representable 3 _ (c1_20_sound 8 q 0 (by norm_num) (by unfold c1_20; omega))
  by_cases h11 : q≤863
  ·
    exact four_is_representable 3 _ (c1_23_sound 8 q 0 (by norm_num) (by unfold c1_23; omega))
  exact four_is_representable 3 _ (c1_7_sound 8 q 0 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_8_1_1 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+1)+1 : ℤ).toNat) := by
  by_cases h0 : q≤265
  ·
    exact four_is_representable 3 _ (c1_17_sound 8 q 1 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤330
  ·
    exact four_is_representable 3 _ (c1_16_sound 8 q 1 (by norm_num) (by unfold c1_16; omega))
  by_cases h2 : q≤363
  ·
    exact four_is_representable 3 _ (c1_11_sound 8 q 1 (by norm_num) (by unfold c1_11; omega))
  by_cases h3 : q≤404
  ·
    exact four_is_representable 3 _ (c1_9_sound 8 q 1 (by norm_num) (by unfold c1_9; omega))
  by_cases h4 : q≤426
  ·
    exact four_is_representable 3 _ (c1_13_sound 8 q 1 (by norm_num) (by unfold c1_13; omega))
  by_cases h5 : q≤486
  ·
    exact four_is_representable 3 _ (c1_19_sound 8 q 1 (by norm_num) (by unfold c1_19; omega))
  by_cases h6 : q≤518
  ·
    exact four_is_representable 3 _ (c1_5_sound 8 q 1 (by norm_num) (by unfold c1_5; omega))
  by_cases h7 : q≤555
  ·
    exact four_is_representable 3 _ (c1_12_sound 8 q 1 (by norm_num) (by unfold c1_12; omega))
  by_cases h8 : q≤596
  ·
    exact four_is_representable 3 _ (c1_8_sound 8 q 1 (by norm_num) (by unfold c1_8; omega))
  by_cases h9 : q≤610
  ·
    exact four_is_representable 3 _ (c1_21_sound 8 q 1 (by norm_num) (by unfold c1_21; omega))
  by_cases h10 : q≤738
  ·
    exact four_is_representable 3 _ (c1_20_sound 8 q 1 (by norm_num) (by unfold c1_20; omega))
  by_cases h11 : q≤867
  ·
    exact four_is_representable 3 _ (c1_23_sound 8 q 1 (by norm_num) (by unfold c1_23; omega))
  exact four_is_representable 3 _ (c1_7_sound 8 q 1 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_8_1_2 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+1)+2 : ℤ).toNat) := by
  by_cases h0 : q≤267
  ·
    exact four_is_representable 3 _ (c1_17_sound 8 q 2 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤332
  ·
    exact four_is_representable 3 _ (c1_16_sound 8 q 2 (by norm_num) (by unfold c1_16; omega))
  by_cases h2 : q≤364
  ·
    exact four_is_representable 3 _ (c1_11_sound 8 q 2 (by norm_num) (by unfold c1_11; omega))
  by_cases h3 : q≤405
  ·
    exact four_is_representable 3 _ (c1_9_sound 8 q 2 (by norm_num) (by unfold c1_9; omega))
  by_cases h4 : q≤428
  ·
    exact four_is_representable 3 _ (c1_13_sound 8 q 2 (by norm_num) (by unfold c1_13; omega))
  by_cases h5 : q≤488
  ·
    exact four_is_representable 3 _ (c1_19_sound 8 q 2 (by norm_num) (by unfold c1_19; omega))
  by_cases h6 : q≤520
  ·
    exact four_is_representable 3 _ (c1_5_sound 8 q 2 (by norm_num) (by unfold c1_5; omega))
  by_cases h7 : q≤556
  ·
    exact four_is_representable 3 _ (c1_12_sound 8 q 2 (by norm_num) (by unfold c1_12; omega))
  by_cases h8 : q≤597
  ·
    exact four_is_representable 3 _ (c1_8_sound 8 q 2 (by norm_num) (by unfold c1_8; omega))
  by_cases h9 : q≤614
  ·
    exact four_is_representable 3 _ (c1_21_sound 8 q 2 (by norm_num) (by unfold c1_21; omega))
  by_cases h10 : q≤742
  ·
    exact four_is_representable 3 _ (c1_20_sound 8 q 2 (by norm_num) (by unfold c1_20; omega))
  by_cases h11 : q≤871
  ·
    exact four_is_representable 3 _ (c1_23_sound 8 q 2 (by norm_num) (by unfold c1_23; omega))
  exact four_is_representable 3 _ (c1_7_sound 8 q 2 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_8_1_3 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+1)+3 : ℤ).toNat) := by
  by_cases h0 : q≤269
  ·
    exact four_is_representable 3 _ (c1_17_sound 8 q 3 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤333
  ·
    exact four_is_representable 3 _ (c1_16_sound 8 q 3 (by norm_num) (by unfold c1_16; omega))
  by_cases h2 : q≤366
  ·
    exact four_is_representable 3 _ (c1_14_sound 8 q 3 (by norm_num) (by unfold c1_14; omega))
  by_cases h3 : q≤406
  ·
    exact four_is_representable 3 _ (c1_9_sound 8 q 3 (by norm_num) (by unfold c1_9; omega))
  by_cases h4 : q≤430
  ·
    exact four_is_representable 3 _ (c1_13_sound 8 q 3 (by norm_num) (by unfold c1_13; omega))
  by_cases h5 : q≤490
  ·
    exact four_is_representable 3 _ (c1_19_sound 8 q 3 (by norm_num) (by unfold c1_19; omega))
  by_cases h6 : q≤522
  ·
    exact four_is_representable 3 _ (c1_5_sound 8 q 3 (by norm_num) (by unfold c1_5; omega))
  by_cases h7 : q≤557
  ·
    exact four_is_representable 3 _ (c1_12_sound 8 q 3 (by norm_num) (by unfold c1_12; omega))
  by_cases h8 : q≤598
  ·
    exact four_is_representable 3 _ (c1_8_sound 8 q 3 (by norm_num) (by unfold c1_8; omega))
  by_cases h9 : q≤618
  ·
    exact four_is_representable 3 _ (c1_21_sound 8 q 3 (by norm_num) (by unfold c1_21; omega))
  by_cases h10 : q≤746
  ·
    exact four_is_representable 3 _ (c1_20_sound 8 q 3 (by norm_num) (by unfold c1_20; omega))
  by_cases h11 : q≤875
  ·
    exact four_is_representable 3 _ (c1_23_sound 8 q 3 (by norm_num) (by unfold c1_23; omega))
  exact four_is_representable 3 _ (c1_7_sound 8 q 3 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_8_1_4 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+1)+4 : ℤ).toNat) := by
  by_cases h0 : q≤271
  ·
    exact four_is_representable 3 _ (c1_17_sound 8 q 4 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤334
  ·
    exact four_is_representable 3 _ (c1_16_sound 8 q 4 (by norm_num) (by unfold c1_16; omega))
  by_cases h2 : q≤368
  ·
    exact four_is_representable 3 _ (c1_14_sound 8 q 4 (by norm_num) (by unfold c1_14; omega))
  by_cases h3 : q≤407
  ·
    exact four_is_representable 3 _ (c1_9_sound 8 q 4 (by norm_num) (by unfold c1_9; omega))
  by_cases h4 : q≤432
  ·
    exact four_is_representable 3 _ (c1_13_sound 8 q 4 (by norm_num) (by unfold c1_13; omega))
  by_cases h5 : q≤492
  ·
    exact four_is_representable 3 _ (c1_19_sound 8 q 4 (by norm_num) (by unfold c1_19; omega))
  by_cases h6 : q≤524
  ·
    exact four_is_representable 3 _ (c1_5_sound 8 q 4 (by norm_num) (by unfold c1_5; omega))
  by_cases h7 : q≤558
  ·
    exact four_is_representable 3 _ (c1_12_sound 8 q 4 (by norm_num) (by unfold c1_12; omega))
  by_cases h8 : q≤599
  ·
    exact four_is_representable 3 _ (c1_8_sound 8 q 4 (by norm_num) (by unfold c1_8; omega))
  by_cases h9 : q≤622
  ·
    exact four_is_representable 3 _ (c1_21_sound 8 q 4 (by norm_num) (by unfold c1_21; omega))
  by_cases h10 : q≤750
  ·
    exact four_is_representable 3 _ (c1_20_sound 8 q 4 (by norm_num) (by unfold c1_20; omega))
  by_cases h11 : q≤879
  ·
    exact four_is_representable 3 _ (c1_23_sound 8 q 4 (by norm_num) (by unfold c1_23; omega))
  exact four_is_representable 3 _ (c1_7_sound 8 q 4 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_8_1_5 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+1)+5 : ℤ).toNat) := by
  by_cases h0 : q≤273
  ·
    exact four_is_representable 3 _ (c1_17_sound 8 q 5 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤335
  ·
    exact four_is_representable 3 _ (c1_16_sound 8 q 5 (by norm_num) (by unfold c1_16; omega))
  by_cases h2 : q≤370
  ·
    exact four_is_representable 3 _ (c1_14_sound 8 q 5 (by norm_num) (by unfold c1_14; omega))
  by_cases h3 : q≤408
  ·
    exact four_is_representable 3 _ (c1_9_sound 8 q 5 (by norm_num) (by unfold c1_9; omega))
  by_cases h4 : q≤434
  ·
    exact four_is_representable 3 _ (c1_13_sound 8 q 5 (by norm_num) (by unfold c1_13; omega))
  by_cases h5 : q≤494
  ·
    exact four_is_representable 3 _ (c1_19_sound 8 q 5 (by norm_num) (by unfold c1_19; omega))
  by_cases h6 : q≤526
  ·
    exact four_is_representable 3 _ (c1_5_sound 8 q 5 (by norm_num) (by unfold c1_5; omega))
  by_cases h7 : q≤559
  ·
    exact four_is_representable 3 _ (c1_12_sound 8 q 5 (by norm_num) (by unfold c1_12; omega))
  by_cases h8 : q≤560
  ·
    have hq : q=560 := by omega
    subst q
    exact represent_exception 35861 (by decide +kernel)
  by_cases h9 : q≤600
  ·
    exact four_is_representable 3 _ (c1_8_sound 8 q 5 (by norm_num) (by unfold c1_8; omega))
  by_cases h10 : q≤626
  ·
    exact four_is_representable 3 _ (c1_21_sound 8 q 5 (by norm_num) (by unfold c1_21; omega))
  by_cases h11 : q≤754
  ·
    exact four_is_representable 3 _ (c1_20_sound 8 q 5 (by norm_num) (by unfold c1_20; omega))
  by_cases h12 : q≤883
  ·
    exact four_is_representable 3 _ (c1_23_sound 8 q 5 (by norm_num) (by unfold c1_23; omega))
  exact four_is_representable 3 _ (c1_7_sound 8 q 5 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_8_1_6 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+1)+6 : ℤ).toNat) := by
  by_cases h0 : q≤275
  ·
    exact four_is_representable 3 _ (c1_17_sound 8 q 6 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤336
  ·
    exact four_is_representable 3 _ (c1_16_sound 8 q 6 (by norm_num) (by unfold c1_16; omega))
  by_cases h2 : q≤372
  ·
    exact four_is_representable 3 _ (c1_14_sound 8 q 6 (by norm_num) (by unfold c1_14; omega))
  by_cases h3 : q≤409
  ·
    exact four_is_representable 3 _ (c1_9_sound 8 q 6 (by norm_num) (by unfold c1_9; omega))
  by_cases h4 : q≤436
  ·
    exact four_is_representable 3 _ (c1_13_sound 8 q 6 (by norm_num) (by unfold c1_13; omega))
  by_cases h5 : q≤496
  ·
    exact four_is_representable 3 _ (c1_19_sound 8 q 6 (by norm_num) (by unfold c1_19; omega))
  by_cases h6 : q≤528
  ·
    exact four_is_representable 3 _ (c1_5_sound 8 q 6 (by norm_num) (by unfold c1_5; omega))
  by_cases h7 : q≤560
  ·
    exact four_is_representable 3 _ (c1_12_sound 8 q 6 (by norm_num) (by unfold c1_12; omega))
  by_cases h8 : q≤561
  ·
    have hq : q=561 := by omega
    subst q
    exact represent_exception 35926 (by decide +kernel)
  by_cases h9 : q≤562
  ·
    exact four_is_representable 3 _ (c1_3_sound 8 q 6 (by norm_num) (by unfold c1_3; omega))
  by_cases h10 : q≤601
  ·
    exact four_is_representable 3 _ (c1_8_sound 8 q 6 (by norm_num) (by unfold c1_8; omega))
  by_cases h11 : q≤630
  ·
    exact four_is_representable 3 _ (c1_21_sound 8 q 6 (by norm_num) (by unfold c1_21; omega))
  by_cases h12 : q≤758
  ·
    exact four_is_representable 3 _ (c1_20_sound 8 q 6 (by norm_num) (by unfold c1_20; omega))
  by_cases h13 : q≤887
  ·
    exact four_is_representable 3 _ (c1_23_sound 8 q 6 (by norm_num) (by unfold c1_23; omega))
  exact four_is_representable 3 _ (c1_7_sound 8 q 6 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_8_1_7 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+1)+7 : ℤ).toNat) := by
  by_cases h0 : q≤277
  ·
    exact four_is_representable 3 _ (c1_17_sound 8 q 7 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤337
  ·
    exact four_is_representable 3 _ (c1_16_sound 8 q 7 (by norm_num) (by unfold c1_16; omega))
  by_cases h2 : q≤374
  ·
    exact four_is_representable 3 _ (c1_14_sound 8 q 7 (by norm_num) (by unfold c1_14; omega))
  by_cases h3 : q≤410
  ·
    exact four_is_representable 3 _ (c1_9_sound 8 q 7 (by norm_num) (by unfold c1_9; omega))
  by_cases h4 : q≤438
  ·
    exact four_is_representable 3 _ (c1_13_sound 8 q 7 (by norm_num) (by unfold c1_13; omega))
  by_cases h5 : q≤498
  ·
    exact four_is_representable 3 _ (c1_19_sound 8 q 7 (by norm_num) (by unfold c1_19; omega))
  by_cases h6 : q≤530
  ·
    exact four_is_representable 3 _ (c1_5_sound 8 q 7 (by norm_num) (by unfold c1_5; omega))
  by_cases h7 : q≤561
  ·
    exact four_is_representable 3 _ (c1_12_sound 8 q 7 (by norm_num) (by unfold c1_12; omega))
  by_cases h8 : q≤562
  ·
    have hq : q=562 := by omega
    subst q
    exact represent_exception 35991 (by decide +kernel)
  by_cases h9 : q≤563
  ·
    have hq : q=563 := by omega
    subst q
    exact represent_exception 36055 (by decide +kernel)
  by_cases h10 : q≤564
  ·
    have hq : q=564 := by omega
    subst q
    exact represent_exception 36119 (by decide +kernel)
  by_cases h11 : q≤602
  ·
    exact four_is_representable 3 _ (c1_8_sound 8 q 7 (by norm_num) (by unfold c1_8; omega))
  by_cases h12 : q≤634
  ·
    exact four_is_representable 3 _ (c1_21_sound 8 q 7 (by norm_num) (by unfold c1_21; omega))
  by_cases h13 : q≤762
  ·
    exact four_is_representable 3 _ (c1_20_sound 8 q 7 (by norm_num) (by unfold c1_20; omega))
  by_cases h14 : q≤891
  ·
    exact four_is_representable 3 _ (c1_23_sound 8 q 7 (by norm_num) (by unfold c1_23; omega))
  exact four_is_representable 3 _ (c1_7_sound 8 q 7 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_8_1_8 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+1)+8 : ℤ).toNat) := by
  by_cases h0 : q≤279
  ·
    exact four_is_representable 3 _ (c1_17_sound 8 q 8 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤338
  ·
    exact four_is_representable 3 _ (c1_16_sound 8 q 8 (by norm_num) (by unfold c1_16; omega))
  by_cases h2 : q≤376
  ·
    exact four_is_representable 3 _ (c1_14_sound 8 q 8 (by norm_num) (by unfold c1_14; omega))
  by_cases h3 : q≤411
  ·
    exact four_is_representable 3 _ (c1_9_sound 8 q 8 (by norm_num) (by unfold c1_9; omega))
  by_cases h4 : q≤440
  ·
    exact four_is_representable 3 _ (c1_13_sound 8 q 8 (by norm_num) (by unfold c1_13; omega))
  by_cases h5 : q≤500
  ·
    exact four_is_representable 3 _ (c1_19_sound 8 q 8 (by norm_num) (by unfold c1_19; omega))
  by_cases h6 : q≤532
  ·
    exact four_is_representable 3 _ (c1_5_sound 8 q 8 (by norm_num) (by unfold c1_5; omega))
  by_cases h7 : q≤562
  ·
    exact four_is_representable 3 _ (c1_12_sound 8 q 8 (by norm_num) (by unfold c1_12; omega))
  by_cases h8 : q≤563
  ·
    have hq : q=563 := by omega
    subst q
    exact represent_exception 36056 (by decide +kernel)
  by_cases h9 : q≤564
  ·
    have hq : q=564 := by omega
    subst q
    exact represent_exception 36120 (by decide +kernel)
  by_cases h10 : q≤565
  ·
    have hq : q=565 := by omega
    subst q
    exact represent_exception 36184 (by decide +kernel)
  by_cases h11 : q≤566
  ·
    have hq : q=566 := by omega
    subst q
    exact represent_exception 36248 (by decide +kernel)
  by_cases h12 : q≤603
  ·
    exact four_is_representable 3 _ (c1_8_sound 8 q 8 (by norm_num) (by unfold c1_8; omega))
  by_cases h13 : q≤638
  ·
    exact four_is_representable 3 _ (c1_21_sound 8 q 8 (by norm_num) (by unfold c1_21; omega))
  by_cases h14 : q≤766
  ·
    exact four_is_representable 3 _ (c1_20_sound 8 q 8 (by norm_num) (by unfold c1_20; omega))
  by_cases h15 : q≤895
  ·
    exact four_is_representable 3 _ (c1_23_sound 8 q 8 (by norm_num) (by unfold c1_23; omega))
  exact four_is_representable 3 _ (c1_7_sound 8 q 8 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_8_1_9 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+1)+9 : ℤ).toNat) := by
  by_cases h0 : q≤281
  ·
    exact four_is_representable 3 _ (c1_17_sound 8 q 9 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤339
  ·
    exact four_is_representable 3 _ (c1_16_sound 8 q 9 (by norm_num) (by unfold c1_16; omega))
  by_cases h2 : q≤378
  ·
    exact four_is_representable 3 _ (c1_14_sound 8 q 9 (by norm_num) (by unfold c1_14; omega))
  by_cases h3 : q≤412
  ·
    exact four_is_representable 3 _ (c1_9_sound 8 q 9 (by norm_num) (by unfold c1_9; omega))
  by_cases h4 : q≤442
  ·
    exact four_is_representable 3 _ (c1_13_sound 8 q 9 (by norm_num) (by unfold c1_13; omega))
  by_cases h5 : q≤502
  ·
    exact four_is_representable 3 _ (c1_19_sound 8 q 9 (by norm_num) (by unfold c1_19; omega))
  by_cases h6 : q≤534
  ·
    exact four_is_representable 3 _ (c1_5_sound 8 q 9 (by norm_num) (by unfold c1_5; omega))
  by_cases h7 : q≤563
  ·
    exact four_is_representable 3 _ (c1_12_sound 8 q 9 (by norm_num) (by unfold c1_12; omega))
  by_cases h8 : q≤564
  ·
    have hq : q=564 := by omega
    subst q
    exact represent_exception 36121 (by decide +kernel)
  by_cases h9 : q≤565
  ·
    have hq : q=565 := by omega
    subst q
    exact represent_exception 36185 (by decide +kernel)
  by_cases h10 : q≤566
  ·
    have hq : q=566 := by omega
    subst q
    exact represent_exception 36249 (by decide +kernel)
  by_cases h11 : q≤567
  ·
    have hq : q=567 := by omega
    subst q
    exact represent_exception 36313 (by decide +kernel)
  by_cases h12 : q≤568
  ·
    have hq : q=568 := by omega
    subst q
    exact represent_exception 36377 (by decide +kernel)
  by_cases h13 : q≤604
  ·
    exact four_is_representable 3 _ (c1_8_sound 8 q 9 (by norm_num) (by unfold c1_8; omega))
  by_cases h14 : q≤642
  ·
    exact four_is_representable 3 _ (c1_21_sound 8 q 9 (by norm_num) (by unfold c1_21; omega))
  by_cases h15 : q≤770
  ·
    exact four_is_representable 3 _ (c1_20_sound 8 q 9 (by norm_num) (by unfold c1_20; omega))
  by_cases h16 : q≤899
  ·
    exact four_is_representable 3 _ (c1_23_sound 8 q 9 (by norm_num) (by unfold c1_23; omega))
  exact four_is_representable 3 _ (c1_7_sound 8 q 9 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_8_1_10 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+1)+10 : ℤ).toNat) := by
  by_cases h0 : q≤283
  ·
    exact four_is_representable 3 _ (c1_17_sound 8 q 10 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤340
  ·
    exact four_is_representable 3 _ (c1_16_sound 8 q 10 (by norm_num) (by unfold c1_16; omega))
  by_cases h2 : q≤380
  ·
    exact four_is_representable 3 _ (c1_14_sound 8 q 10 (by norm_num) (by unfold c1_14; omega))
  by_cases h3 : q≤413
  ·
    exact four_is_representable 3 _ (c1_9_sound 8 q 10 (by norm_num) (by unfold c1_9; omega))
  by_cases h4 : q≤444
  ·
    exact four_is_representable 3 _ (c1_13_sound 8 q 10 (by norm_num) (by unfold c1_13; omega))
  by_cases h5 : q≤504
  ·
    exact four_is_representable 3 _ (c1_19_sound 8 q 10 (by norm_num) (by unfold c1_19; omega))
  by_cases h6 : q≤536
  ·
    exact four_is_representable 3 _ (c1_5_sound 8 q 10 (by norm_num) (by unfold c1_5; omega))
  by_cases h7 : q≤564
  ·
    exact four_is_representable 3 _ (c1_12_sound 8 q 10 (by norm_num) (by unfold c1_12; omega))
  by_cases h8 : q≤565
  ·
    have hq : q=565 := by omega
    subst q
    exact represent_exception 36186 (by decide +kernel)
  by_cases h9 : q≤566
  ·
    have hq : q=566 := by omega
    subst q
    exact represent_exception 36250 (by decide +kernel)
  by_cases h10 : q≤567
  ·
    have hq : q=567 := by omega
    subst q
    exact represent_exception 36314 (by decide +kernel)
  by_cases h11 : q≤568
  ·
    have hq : q=568 := by omega
    subst q
    exact represent_exception 36378 (by decide +kernel)
  by_cases h12 : q≤569
  ·
    have hq : q=569 := by omega
    subst q
    exact represent_exception 36442 (by decide +kernel)
  by_cases h13 : q≤570
  ·
    have hq : q=570 := by omega
    subst q
    exact represent_exception 36506 (by decide +kernel)
  by_cases h14 : q≤605
  ·
    exact four_is_representable 3 _ (c1_8_sound 8 q 10 (by norm_num) (by unfold c1_8; omega))
  by_cases h15 : q≤646
  ·
    exact four_is_representable 3 _ (c1_21_sound 8 q 10 (by norm_num) (by unfold c1_21; omega))
  by_cases h16 : q≤774
  ·
    exact four_is_representable 3 _ (c1_20_sound 8 q 10 (by norm_num) (by unfold c1_20; omega))
  by_cases h17 : q≤903
  ·
    exact four_is_representable 3 _ (c1_23_sound 8 q 10 (by norm_num) (by unfold c1_23; omega))
  exact four_is_representable 3 _ (c1_7_sound 8 q 10 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_8_1_11 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+1)+11 : ℤ).toNat) := by
  by_cases h0 : q≤285
  ·
    exact four_is_representable 3 _ (c1_17_sound 8 q 11 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤345
  ·
    exact four_is_representable 3 _ (c1_10_sound 8 q 11 (by norm_num) (by unfold c1_10; omega))
  by_cases h2 : q≤382
  ·
    exact four_is_representable 3 _ (c1_14_sound 8 q 11 (by norm_num) (by unfold c1_14; omega))
  by_cases h3 : q≤414
  ·
    exact four_is_representable 3 _ (c1_9_sound 8 q 11 (by norm_num) (by unfold c1_9; omega))
  by_cases h4 : q≤446
  ·
    exact four_is_representable 3 _ (c1_13_sound 8 q 11 (by norm_num) (by unfold c1_13; omega))
  by_cases h5 : q≤506
  ·
    exact four_is_representable 3 _ (c1_19_sound 8 q 11 (by norm_num) (by unfold c1_19; omega))
  by_cases h6 : q≤538
  ·
    exact four_is_representable 3 _ (c1_5_sound 8 q 11 (by norm_num) (by unfold c1_5; omega))
  by_cases h7 : q≤565
  ·
    exact four_is_representable 3 _ (c1_12_sound 8 q 11 (by norm_num) (by unfold c1_12; omega))
  by_cases h8 : q≤566
  ·
    have hq : q=566 := by omega
    subst q
    exact represent_exception 36251 (by decide +kernel)
  by_cases h9 : q≤567
  ·
    have hq : q=567 := by omega
    subst q
    exact represent_exception 36315 (by decide +kernel)
  by_cases h10 : q≤568
  ·
    have hq : q=568 := by omega
    subst q
    exact represent_exception 36379 (by decide +kernel)
  by_cases h11 : q≤569
  ·
    have hq : q=569 := by omega
    subst q
    exact represent_exception 36443 (by decide +kernel)
  by_cases h12 : q≤570
  ·
    have hq : q=570 := by omega
    subst q
    exact represent_exception 36507 (by decide +kernel)
  by_cases h13 : q≤571
  ·
    have hq : q=571 := by omega
    subst q
    exact represent_exception 36571 (by decide +kernel)
  by_cases h14 : q≤572
  ·
    have hq : q=572 := by omega
    subst q
    exact represent_exception 36635 (by decide +kernel)
  by_cases h15 : q≤606
  ·
    exact four_is_representable 3 _ (c1_8_sound 8 q 11 (by norm_num) (by unfold c1_8; omega))
  by_cases h16 : q≤650
  ·
    exact four_is_representable 3 _ (c1_21_sound 8 q 11 (by norm_num) (by unfold c1_21; omega))
  by_cases h17 : q≤778
  ·
    exact four_is_representable 3 _ (c1_20_sound 8 q 11 (by norm_num) (by unfold c1_20; omega))
  by_cases h18 : q≤907
  ·
    exact four_is_representable 3 _ (c1_23_sound 8 q 11 (by norm_num) (by unfold c1_23; omega))
  exact four_is_representable 3 _ (c1_7_sound 8 q 11 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_8_1_12 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+1)+12 : ℤ).toNat) := by
  by_cases h0 : q≤287
  ·
    exact four_is_representable 3 _ (c1_17_sound 8 q 12 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤347
  ·
    exact four_is_representable 3 _ (c1_10_sound 8 q 12 (by norm_num) (by unfold c1_10; omega))
  by_cases h2 : q≤384
  ·
    exact four_is_representable 3 _ (c1_14_sound 8 q 12 (by norm_num) (by unfold c1_14; omega))
  by_cases h3 : q≤415
  ·
    exact four_is_representable 3 _ (c1_9_sound 8 q 12 (by norm_num) (by unfold c1_9; omega))
  by_cases h4 : q≤448
  ·
    exact four_is_representable 3 _ (c1_13_sound 8 q 12 (by norm_num) (by unfold c1_13; omega))
  by_cases h5 : q≤508
  ·
    exact four_is_representable 3 _ (c1_19_sound 8 q 12 (by norm_num) (by unfold c1_19; omega))
  by_cases h6 : q≤540
  ·
    exact four_is_representable 3 _ (c1_5_sound 8 q 12 (by norm_num) (by unfold c1_5; omega))
  by_cases h7 : q≤566
  ·
    exact four_is_representable 3 _ (c1_12_sound 8 q 12 (by norm_num) (by unfold c1_12; omega))
  by_cases h8 : q≤567
  ·
    have hq : q=567 := by omega
    subst q
    exact represent_exception 36316 (by decide +kernel)
  by_cases h9 : q≤568
  ·
    have hq : q=568 := by omega
    subst q
    exact represent_exception 36380 (by decide +kernel)
  by_cases h10 : q≤569
  ·
    have hq : q=569 := by omega
    subst q
    exact represent_exception 36444 (by decide +kernel)
  by_cases h11 : q≤570
  ·
    have hq : q=570 := by omega
    subst q
    exact represent_exception 36508 (by decide +kernel)
  by_cases h12 : q≤571
  ·
    have hq : q=571 := by omega
    subst q
    exact represent_exception 36572 (by decide +kernel)
  by_cases h13 : q≤572
  ·
    have hq : q=572 := by omega
    subst q
    exact represent_exception 36636 (by decide +kernel)
  by_cases h14 : q≤573
  ·
    have hq : q=573 := by omega
    subst q
    exact represent_exception 36700 (by decide +kernel)
  by_cases h15 : q≤574
  ·
    have hq : q=574 := by omega
    subst q
    exact represent_exception 36764 (by decide +kernel)
  by_cases h16 : q≤607
  ·
    exact four_is_representable 3 _ (c1_8_sound 8 q 12 (by norm_num) (by unfold c1_8; omega))
  by_cases h17 : q≤654
  ·
    exact four_is_representable 3 _ (c1_21_sound 8 q 12 (by norm_num) (by unfold c1_21; omega))
  by_cases h18 : q≤782
  ·
    exact four_is_representable 3 _ (c1_20_sound 8 q 12 (by norm_num) (by unfold c1_20; omega))
  by_cases h19 : q≤911
  ·
    exact four_is_representable 3 _ (c1_23_sound 8 q 12 (by norm_num) (by unfold c1_23; omega))
  exact four_is_representable 3 _ (c1_7_sound 8 q 12 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_8_1_13 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+1)+13 : ℤ).toNat) := by
  by_cases h0 : q≤289
  ·
    exact four_is_representable 3 _ (c1_17_sound 8 q 13 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤349
  ·
    exact four_is_representable 3 _ (c1_10_sound 8 q 13 (by norm_num) (by unfold c1_10; omega))
  by_cases h2 : q≤386
  ·
    exact four_is_representable 3 _ (c1_14_sound 8 q 13 (by norm_num) (by unfold c1_14; omega))
  by_cases h3 : q≤416
  ·
    exact four_is_representable 3 _ (c1_9_sound 8 q 13 (by norm_num) (by unfold c1_9; omega))
  by_cases h4 : q≤450
  ·
    exact four_is_representable 3 _ (c1_13_sound 8 q 13 (by norm_num) (by unfold c1_13; omega))
  by_cases h5 : q≤510
  ·
    exact four_is_representable 3 _ (c1_19_sound 8 q 13 (by norm_num) (by unfold c1_19; omega))
  by_cases h6 : q≤542
  ·
    exact four_is_representable 3 _ (c1_5_sound 8 q 13 (by norm_num) (by unfold c1_5; omega))
  by_cases h7 : q≤567
  ·
    exact four_is_representable 3 _ (c1_12_sound 8 q 13 (by norm_num) (by unfold c1_12; omega))
  by_cases h8 : q≤568
  ·
    have hq : q=568 := by omega
    subst q
    exact represent_exception 36381 (by decide +kernel)
  by_cases h9 : q≤569
  ·
    have hq : q=569 := by omega
    subst q
    exact represent_exception 36445 (by decide +kernel)
  by_cases h10 : q≤570
  ·
    have hq : q=570 := by omega
    subst q
    exact represent_exception 36509 (by decide +kernel)
  by_cases h11 : q≤571
  ·
    have hq : q=571 := by omega
    subst q
    exact represent_exception 36573 (by decide +kernel)
  by_cases h12 : q≤572
  ·
    have hq : q=572 := by omega
    subst q
    exact represent_exception 36637 (by decide +kernel)
  by_cases h13 : q≤573
  ·
    have hq : q=573 := by omega
    subst q
    exact represent_exception 36701 (by decide +kernel)
  by_cases h14 : q≤574
  ·
    have hq : q=574 := by omega
    subst q
    exact represent_exception 36765 (by decide +kernel)
  by_cases h15 : q≤575
  ·
    have hq : q=575 := by omega
    subst q
    exact represent_exception 36829 (by decide +kernel)
  by_cases h16 : q≤576
  ·
    have hq : q=576 := by omega
    subst q
    exact represent_exception 36893 (by decide +kernel)
  by_cases h17 : q≤608
  ·
    exact four_is_representable 3 _ (c1_8_sound 8 q 13 (by norm_num) (by unfold c1_8; omega))
  by_cases h18 : q≤658
  ·
    exact four_is_representable 3 _ (c1_21_sound 8 q 13 (by norm_num) (by unfold c1_21; omega))
  by_cases h19 : q≤786
  ·
    exact four_is_representable 3 _ (c1_20_sound 8 q 13 (by norm_num) (by unfold c1_20; omega))
  by_cases h20 : q≤915
  ·
    exact four_is_representable 3 _ (c1_23_sound 8 q 13 (by norm_num) (by unfold c1_23; omega))
  exact four_is_representable 3 _ (c1_7_sound 8 q 13 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_8_1_14 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+1)+14 : ℤ).toNat) := by
  by_cases h0 : q≤291
  ·
    exact four_is_representable 3 _ (c1_17_sound 8 q 14 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤351
  ·
    exact four_is_representable 3 _ (c1_10_sound 8 q 14 (by norm_num) (by unfold c1_10; omega))
  by_cases h2 : q≤388
  ·
    exact four_is_representable 3 _ (c1_14_sound 8 q 14 (by norm_num) (by unfold c1_14; omega))
  by_cases h3 : q≤417
  ·
    exact four_is_representable 3 _ (c1_9_sound 8 q 14 (by norm_num) (by unfold c1_9; omega))
  by_cases h4 : q≤452
  ·
    exact four_is_representable 3 _ (c1_13_sound 8 q 14 (by norm_num) (by unfold c1_13; omega))
  by_cases h5 : q≤512
  ·
    exact four_is_representable 3 _ (c1_19_sound 8 q 14 (by norm_num) (by unfold c1_19; omega))
  by_cases h6 : q≤544
  ·
    exact four_is_representable 3 _ (c1_5_sound 8 q 14 (by norm_num) (by unfold c1_5; omega))
  by_cases h7 : q≤568
  ·
    exact four_is_representable 3 _ (c1_12_sound 8 q 14 (by norm_num) (by unfold c1_12; omega))
  by_cases h8 : q≤569
  ·
    have hq : q=569 := by omega
    subst q
    exact represent_exception 36446 (by decide +kernel)
  by_cases h9 : q≤570
  ·
    have hq : q=570 := by omega
    subst q
    exact represent_exception 36510 (by decide +kernel)
  by_cases h10 : q≤571
  ·
    have hq : q=571 := by omega
    subst q
    exact represent_exception 36574 (by decide +kernel)
  by_cases h11 : q≤572
  ·
    have hq : q=572 := by omega
    subst q
    exact represent_exception 36638 (by decide +kernel)
  by_cases h12 : q≤573
  ·
    have hq : q=573 := by omega
    subst q
    exact represent_exception 36702 (by decide +kernel)
  by_cases h13 : q≤574
  ·
    have hq : q=574 := by omega
    subst q
    exact represent_exception 36766 (by decide +kernel)
  by_cases h14 : q≤575
  ·
    have hq : q=575 := by omega
    subst q
    exact represent_exception 36830 (by decide +kernel)
  by_cases h15 : q≤576
  ·
    have hq : q=576 := by omega
    subst q
    exact represent_exception 36894 (by decide +kernel)
  by_cases h16 : q≤577
  ·
    have hq : q=577 := by omega
    subst q
    exact represent_exception 36958 (by decide +kernel)
  by_cases h17 : q≤662
  ·
    exact four_is_representable 3 _ (c1_21_sound 8 q 14 (by norm_num) (by unfold c1_21; omega))
  by_cases h18 : q≤790
  ·
    exact four_is_representable 3 _ (c1_20_sound 8 q 14 (by norm_num) (by unfold c1_20; omega))
  by_cases h19 : q≤919
  ·
    exact four_is_representable 3 _ (c1_23_sound 8 q 14 (by norm_num) (by unfold c1_23; omega))
  exact four_is_representable 3 _ (c1_7_sound 8 q 14 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_8_1_15 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+1)+15 : ℤ).toNat) := by
  by_cases h0 : q≤293
  ·
    exact four_is_representable 3 _ (c1_17_sound 8 q 15 (by norm_num) (by unfold c1_17; omega))
  by_cases h1 : q≤353
  ·
    exact four_is_representable 3 _ (c1_10_sound 8 q 15 (by norm_num) (by unfold c1_10; omega))
  by_cases h2 : q≤390
  ·
    exact four_is_representable 3 _ (c1_14_sound 8 q 15 (by norm_num) (by unfold c1_14; omega))
  by_cases h3 : q≤418
  ·
    exact four_is_representable 3 _ (c1_9_sound 8 q 15 (by norm_num) (by unfold c1_9; omega))
  by_cases h4 : q≤454
  ·
    exact four_is_representable 3 _ (c1_13_sound 8 q 15 (by norm_num) (by unfold c1_13; omega))
  by_cases h5 : q≤514
  ·
    exact four_is_representable 3 _ (c1_19_sound 8 q 15 (by norm_num) (by unfold c1_19; omega))
  by_cases h6 : q≤546
  ·
    exact four_is_representable 3 _ (c1_5_sound 8 q 15 (by norm_num) (by unfold c1_5; omega))
  by_cases h7 : q≤569
  ·
    exact four_is_representable 3 _ (c1_12_sound 8 q 15 (by norm_num) (by unfold c1_12; omega))
  by_cases h8 : q≤570
  ·
    have hq : q=570 := by omega
    subst q
    exact represent_exception 36511 (by decide +kernel)
  by_cases h9 : q≤571
  ·
    have hq : q=571 := by omega
    subst q
    exact represent_exception 36575 (by decide +kernel)
  by_cases h10 : q≤572
  ·
    have hq : q=572 := by omega
    subst q
    exact represent_exception 36639 (by decide +kernel)
  by_cases h11 : q≤573
  ·
    have hq : q=573 := by omega
    subst q
    exact represent_exception 36703 (by decide +kernel)
  by_cases h12 : q≤574
  ·
    have hq : q=574 := by omega
    subst q
    exact represent_exception 36767 (by decide +kernel)
  by_cases h13 : q≤575
  ·
    have hq : q=575 := by omega
    subst q
    exact represent_exception 36831 (by decide +kernel)
  by_cases h14 : q≤576
  ·
    have hq : q=576 := by omega
    subst q
    exact represent_exception 36895 (by decide +kernel)
  by_cases h15 : q≤577
  ·
    have hq : q=577 := by omega
    subst q
    exact represent_exception 36959 (by decide +kernel)
  by_cases h16 : q≤578
  ·
    have hq : q=578 := by omega
    subst q
    exact represent_exception 37023 (by decide +kernel)
  by_cases h17 : q≤666
  ·
    exact four_is_representable 3 _ (c1_21_sound 8 q 15 (by norm_num) (by unfold c1_21; omega))
  by_cases h18 : q≤794
  ·
    exact four_is_representable 3 _ (c1_20_sound 8 q 15 (by norm_num) (by unfold c1_20; omega))
  by_cases h19 : q≤923
  ·
    exact four_is_representable 3 _ (c1_23_sound 8 q 15 (by norm_num) (by unfold c1_23; omega))
  exact four_is_representable 3 _ (c1_7_sound 8 q 15 (by norm_num) (by unfold c1_7; omega))

set_option maxRecDepth 10000 in
def middle_8_2_0 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+2)+0 : ℤ).toNat) := by
  by_cases h0 : q≤303
  ·
    exact four_is_representable 3 _ (c2_7_sound 8 q 0 (by norm_num) (by unfold c2_7; omega))
  by_cases h1 : q≤354
  ·
    exact four_is_representable 3 _ (c2_2_sound 8 q 0 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤392
  ·
    exact four_is_representable 3 _ (c2_23_sound 8 q 0 (by norm_num) (by unfold c2_23; omega))
  by_cases h3 : q≤419
  ·
    exact four_is_representable 3 _ (c2_19_sound 8 q 0 (by norm_num) (by unfold c2_19; omega))
  by_cases h4 : q≤456
  ·
    exact four_is_representable 3 _ (c2_1_sound 8 q 0 (by norm_num) (by unfold c2_1; omega))
  by_cases h5 : q≤516
  ·
    exact four_is_representable 3 _ (c2_0_sound 8 q 0 (by norm_num) (by unfold c2_0; omega))
  by_cases h6 : q≤548
  ·
    exact four_is_representable 3 _ (c2_3_sound 8 q 0 (by norm_num) (by unfold c2_3; omega))
  by_cases h7 : q≤570
  ·
    exact four_is_representable 3 _ (c2_18_sound 8 q 0 (by norm_num) (by unfold c2_18; omega))
  by_cases h8 : q≤571
  ·
    have hq : q=571 := by omega
    subst q
    exact represent_exception 36576 (by decide +kernel)
  by_cases h9 : q≤572
  ·
    have hq : q=572 := by omega
    subst q
    exact represent_exception 36640 (by decide +kernel)
  by_cases h10 : q≤573
  ·
    have hq : q=573 := by omega
    subst q
    exact represent_exception 36704 (by decide +kernel)
  by_cases h11 : q≤574
  ·
    have hq : q=574 := by omega
    subst q
    exact represent_exception 36768 (by decide +kernel)
  by_cases h12 : q≤575
  ·
    have hq : q=575 := by omega
    subst q
    exact represent_exception 36832 (by decide +kernel)
  by_cases h13 : q≤576
  ·
    have hq : q=576 := by omega
    subst q
    exact represent_exception 36896 (by decide +kernel)
  by_cases h14 : q≤577
  ·
    have hq : q=577 := by omega
    subst q
    exact represent_exception 36960 (by decide +kernel)
  by_cases h15 : q≤578
  ·
    have hq : q=578 := by omega
    subst q
    exact represent_exception 37024 (by decide +kernel)
  by_cases h16 : q≤579
  ·
    have hq : q=579 := by omega
    subst q
    exact represent_exception 37088 (by decide +kernel)
  by_cases h17 : q≤670
  ·
    exact four_is_representable 3 _ (c2_13_sound 8 q 0 (by norm_num) (by unfold c2_13; omega))
  by_cases h18 : q≤798
  ·
    exact four_is_representable 3 _ (c2_12_sound 8 q 0 (by norm_num) (by unfold c2_12; omega))
  by_cases h19 : q≤927
  ·
    exact four_is_representable 3 _ (c2_9_sound 8 q 0 (by norm_num) (by unfold c2_9; omega))
  exact four_is_representable 3 _ (c2_15_sound 8 q 0 (by norm_num) (by unfold c2_15; omega))

set_option maxRecDepth 10000 in
def middle_8_2_1 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+2)+1 : ℤ).toNat) := by
  by_cases h0 : q≤305
  ·
    exact four_is_representable 3 _ (c2_7_sound 8 q 1 (by norm_num) (by unfold c2_7; omega))
  by_cases h1 : q≤355
  ·
    exact four_is_representable 3 _ (c2_2_sound 8 q 1 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤394
  ·
    exact four_is_representable 3 _ (c2_23_sound 8 q 1 (by norm_num) (by unfold c2_23; omega))
  by_cases h3 : q≤420
  ·
    exact four_is_representable 3 _ (c2_19_sound 8 q 1 (by norm_num) (by unfold c2_19; omega))
  by_cases h4 : q≤458
  ·
    exact four_is_representable 3 _ (c2_1_sound 8 q 1 (by norm_num) (by unfold c2_1; omega))
  by_cases h5 : q≤518
  ·
    exact four_is_representable 3 _ (c2_0_sound 8 q 1 (by norm_num) (by unfold c2_0; omega))
  by_cases h6 : q≤550
  ·
    exact four_is_representable 3 _ (c2_3_sound 8 q 1 (by norm_num) (by unfold c2_3; omega))
  by_cases h7 : q≤571
  ·
    exact four_is_representable 3 _ (c2_18_sound 8 q 1 (by norm_num) (by unfold c2_18; omega))
  by_cases h8 : q≤572
  ·
    have hq : q=572 := by omega
    subst q
    exact represent_exception 36641 (by decide +kernel)
  by_cases h9 : q≤573
  ·
    have hq : q=573 := by omega
    subst q
    exact represent_exception 36705 (by decide +kernel)
  by_cases h10 : q≤574
  ·
    have hq : q=574 := by omega
    subst q
    exact represent_exception 36769 (by decide +kernel)
  by_cases h11 : q≤575
  ·
    have hq : q=575 := by omega
    subst q
    exact represent_exception 36833 (by decide +kernel)
  by_cases h12 : q≤576
  ·
    have hq : q=576 := by omega
    subst q
    exact represent_exception 36897 (by decide +kernel)
  by_cases h13 : q≤577
  ·
    have hq : q=577 := by omega
    subst q
    exact represent_exception 36961 (by decide +kernel)
  by_cases h14 : q≤578
  ·
    have hq : q=578 := by omega
    subst q
    exact represent_exception 37025 (by decide +kernel)
  by_cases h15 : q≤579
  ·
    have hq : q=579 := by omega
    subst q
    exact represent_exception 37089 (by decide +kernel)
  by_cases h16 : q≤580
  ·
    have hq : q=580 := by omega
    subst q
    exact represent_exception 37153 (by decide +kernel)
  by_cases h17 : q≤674
  ·
    exact four_is_representable 3 _ (c2_13_sound 8 q 1 (by norm_num) (by unfold c2_13; omega))
  by_cases h18 : q≤802
  ·
    exact four_is_representable 3 _ (c2_12_sound 8 q 1 (by norm_num) (by unfold c2_12; omega))
  by_cases h19 : q≤931
  ·
    exact four_is_representable 3 _ (c2_9_sound 8 q 1 (by norm_num) (by unfold c2_9; omega))
  exact four_is_representable 3 _ (c2_15_sound 8 q 1 (by norm_num) (by unfold c2_15; omega))

set_option maxRecDepth 10000 in
def middle_8_2_2 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+2)+2 : ℤ).toNat) := by
  by_cases h0 : q≤307
  ·
    exact four_is_representable 3 _ (c2_7_sound 8 q 2 (by norm_num) (by unfold c2_7; omega))
  by_cases h1 : q≤356
  ·
    exact four_is_representable 3 _ (c2_2_sound 8 q 2 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤396
  ·
    exact four_is_representable 3 _ (c2_23_sound 8 q 2 (by norm_num) (by unfold c2_23; omega))
  by_cases h3 : q≤421
  ·
    exact four_is_representable 3 _ (c2_19_sound 8 q 2 (by norm_num) (by unfold c2_19; omega))
  by_cases h4 : q≤460
  ·
    exact four_is_representable 3 _ (c2_1_sound 8 q 2 (by norm_num) (by unfold c2_1; omega))
  by_cases h5 : q≤520
  ·
    exact four_is_representable 3 _ (c2_0_sound 8 q 2 (by norm_num) (by unfold c2_0; omega))
  by_cases h6 : q≤552
  ·
    exact four_is_representable 3 _ (c2_3_sound 8 q 2 (by norm_num) (by unfold c2_3; omega))
  by_cases h7 : q≤572
  ·
    exact four_is_representable 3 _ (c2_18_sound 8 q 2 (by norm_num) (by unfold c2_18; omega))
  by_cases h8 : q≤573
  ·
    have hq : q=573 := by omega
    subst q
    exact represent_exception 36706 (by decide +kernel)
  by_cases h9 : q≤574
  ·
    have hq : q=574 := by omega
    subst q
    exact represent_exception 36770 (by decide +kernel)
  by_cases h10 : q≤575
  ·
    have hq : q=575 := by omega
    subst q
    exact represent_exception 36834 (by decide +kernel)
  by_cases h11 : q≤576
  ·
    have hq : q=576 := by omega
    subst q
    exact represent_exception 36898 (by decide +kernel)
  by_cases h12 : q≤577
  ·
    have hq : q=577 := by omega
    subst q
    exact represent_exception 36962 (by decide +kernel)
  by_cases h13 : q≤578
  ·
    have hq : q=578 := by omega
    subst q
    exact represent_exception 37026 (by decide +kernel)
  by_cases h14 : q≤579
  ·
    have hq : q=579 := by omega
    subst q
    exact represent_exception 37090 (by decide +kernel)
  by_cases h15 : q≤580
  ·
    have hq : q=580 := by omega
    subst q
    exact represent_exception 37154 (by decide +kernel)
  by_cases h16 : q≤581
  ·
    have hq : q=581 := by omega
    subst q
    exact represent_exception 37218 (by decide +kernel)
  by_cases h17 : q≤678
  ·
    exact four_is_representable 3 _ (c2_13_sound 8 q 2 (by norm_num) (by unfold c2_13; omega))
  by_cases h18 : q≤806
  ·
    exact four_is_representable 3 _ (c2_12_sound 8 q 2 (by norm_num) (by unfold c2_12; omega))
  by_cases h19 : q≤935
  ·
    exact four_is_representable 3 _ (c2_9_sound 8 q 2 (by norm_num) (by unfold c2_9; omega))
  exact four_is_representable 3 _ (c2_15_sound 8 q 2 (by norm_num) (by unfold c2_15; omega))

set_option maxRecDepth 10000 in
def middle_8_2_3 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+2)+3 : ℤ).toNat) := by
  by_cases h0 : q≤308
  ·
    exact four_is_representable 3 _ (c2_7_sound 8 q 3 (by norm_num) (by unfold c2_7; omega))
  by_cases h1 : q≤357
  ·
    exact four_is_representable 3 _ (c2_2_sound 8 q 3 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤398
  ·
    exact four_is_representable 3 _ (c2_23_sound 8 q 3 (by norm_num) (by unfold c2_23; omega))
  by_cases h3 : q≤422
  ·
    exact four_is_representable 3 _ (c2_19_sound 8 q 3 (by norm_num) (by unfold c2_19; omega))
  by_cases h4 : q≤462
  ·
    exact four_is_representable 3 _ (c2_1_sound 8 q 3 (by norm_num) (by unfold c2_1; omega))
  by_cases h5 : q≤522
  ·
    exact four_is_representable 3 _ (c2_0_sound 8 q 3 (by norm_num) (by unfold c2_0; omega))
  by_cases h6 : q≤554
  ·
    exact four_is_representable 3 _ (c2_3_sound 8 q 3 (by norm_num) (by unfold c2_3; omega))
  by_cases h7 : q≤573
  ·
    exact four_is_representable 3 _ (c2_18_sound 8 q 3 (by norm_num) (by unfold c2_18; omega))
  by_cases h8 : q≤574
  ·
    have hq : q=574 := by omega
    subst q
    exact represent_exception 36771 (by decide +kernel)
  by_cases h9 : q≤575
  ·
    have hq : q=575 := by omega
    subst q
    exact represent_exception 36835 (by decide +kernel)
  by_cases h10 : q≤576
  ·
    have hq : q=576 := by omega
    subst q
    exact represent_exception 36899 (by decide +kernel)
  by_cases h11 : q≤577
  ·
    have hq : q=577 := by omega
    subst q
    exact represent_exception 36963 (by decide +kernel)
  by_cases h12 : q≤578
  ·
    have hq : q=578 := by omega
    subst q
    exact represent_exception 37027 (by decide +kernel)
  by_cases h13 : q≤579
  ·
    have hq : q=579 := by omega
    subst q
    exact represent_exception 37091 (by decide +kernel)
  by_cases h14 : q≤580
  ·
    have hq : q=580 := by omega
    subst q
    exact represent_exception 37155 (by decide +kernel)
  by_cases h15 : q≤581
  ·
    have hq : q=581 := by omega
    subst q
    exact represent_exception 37219 (by decide +kernel)
  by_cases h16 : q≤582
  ·
    have hq : q=582 := by omega
    subst q
    exact represent_exception 37283 (by decide +kernel)
  by_cases h17 : q≤682
  ·
    exact four_is_representable 3 _ (c2_13_sound 8 q 3 (by norm_num) (by unfold c2_13; omega))
  by_cases h18 : q≤810
  ·
    exact four_is_representable 3 _ (c2_12_sound 8 q 3 (by norm_num) (by unfold c2_12; omega))
  by_cases h19 : q≤939
  ·
    exact four_is_representable 3 _ (c2_9_sound 8 q 3 (by norm_num) (by unfold c2_9; omega))
  exact four_is_representable 3 _ (c2_15_sound 8 q 3 (by norm_num) (by unfold c2_15; omega))

set_option maxRecDepth 10000 in
def middle_8_2_4 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+2)+4 : ℤ).toNat) := by
  by_cases h0 : q≤309
  ·
    exact four_is_representable 3 _ (c2_7_sound 8 q 4 (by norm_num) (by unfold c2_7; omega))
  by_cases h1 : q≤358
  ·
    exact four_is_representable 3 _ (c2_2_sound 8 q 4 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤400
  ·
    exact four_is_representable 3 _ (c2_23_sound 8 q 4 (by norm_num) (by unfold c2_23; omega))
  by_cases h3 : q≤423
  ·
    exact four_is_representable 3 _ (c2_19_sound 8 q 4 (by norm_num) (by unfold c2_19; omega))
  by_cases h4 : q≤464
  ·
    exact four_is_representable 3 _ (c2_1_sound 8 q 4 (by norm_num) (by unfold c2_1; omega))
  by_cases h5 : q≤524
  ·
    exact four_is_representable 3 _ (c2_0_sound 8 q 4 (by norm_num) (by unfold c2_0; omega))
  by_cases h6 : q≤556
  ·
    exact four_is_representable 3 _ (c2_3_sound 8 q 4 (by norm_num) (by unfold c2_3; omega))
  by_cases h7 : q≤574
  ·
    exact four_is_representable 3 _ (c2_18_sound 8 q 4 (by norm_num) (by unfold c2_18; omega))
  by_cases h8 : q≤575
  ·
    have hq : q=575 := by omega
    subst q
    exact represent_exception 36836 (by decide +kernel)
  by_cases h9 : q≤576
  ·
    have hq : q=576 := by omega
    subst q
    exact represent_exception 36900 (by decide +kernel)
  by_cases h10 : q≤577
  ·
    have hq : q=577 := by omega
    subst q
    exact represent_exception 36964 (by decide +kernel)
  by_cases h11 : q≤578
  ·
    have hq : q=578 := by omega
    subst q
    exact represent_exception 37028 (by decide +kernel)
  by_cases h12 : q≤579
  ·
    have hq : q=579 := by omega
    subst q
    exact represent_exception 37092 (by decide +kernel)
  by_cases h13 : q≤580
  ·
    have hq : q=580 := by omega
    subst q
    exact represent_exception 37156 (by decide +kernel)
  by_cases h14 : q≤581
  ·
    have hq : q=581 := by omega
    subst q
    exact represent_exception 37220 (by decide +kernel)
  by_cases h15 : q≤582
  ·
    have hq : q=582 := by omega
    subst q
    exact represent_exception 37284 (by decide +kernel)
  by_cases h16 : q≤583
  ·
    have hq : q=583 := by omega
    subst q
    exact represent_exception 37348 (by decide +kernel)
  by_cases h17 : q≤686
  ·
    exact four_is_representable 3 _ (c2_13_sound 8 q 4 (by norm_num) (by unfold c2_13; omega))
  by_cases h18 : q≤814
  ·
    exact four_is_representable 3 _ (c2_12_sound 8 q 4 (by norm_num) (by unfold c2_12; omega))
  by_cases h19 : q≤943
  ·
    exact four_is_representable 3 _ (c2_9_sound 8 q 4 (by norm_num) (by unfold c2_9; omega))
  exact four_is_representable 3 _ (c2_15_sound 8 q 4 (by norm_num) (by unfold c2_15; omega))

set_option maxRecDepth 10000 in
def middle_8_2_5 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+2)+5 : ℤ).toNat) := by
  by_cases h0 : q≤310
  ·
    exact four_is_representable 3 _ (c2_7_sound 8 q 5 (by norm_num) (by unfold c2_7; omega))
  by_cases h1 : q≤359
  ·
    exact four_is_representable 3 _ (c2_2_sound 8 q 5 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤402
  ·
    exact four_is_representable 3 _ (c2_23_sound 8 q 5 (by norm_num) (by unfold c2_23; omega))
  by_cases h3 : q≤424
  ·
    exact four_is_representable 3 _ (c2_19_sound 8 q 5 (by norm_num) (by unfold c2_19; omega))
  by_cases h4 : q≤466
  ·
    exact four_is_representable 3 _ (c2_1_sound 8 q 5 (by norm_num) (by unfold c2_1; omega))
  by_cases h5 : q≤526
  ·
    exact four_is_representable 3 _ (c2_0_sound 8 q 5 (by norm_num) (by unfold c2_0; omega))
  by_cases h6 : q≤558
  ·
    exact four_is_representable 3 _ (c2_3_sound 8 q 5 (by norm_num) (by unfold c2_3; omega))
  by_cases h7 : q≤575
  ·
    exact four_is_representable 3 _ (c2_18_sound 8 q 5 (by norm_num) (by unfold c2_18; omega))
  by_cases h8 : q≤576
  ·
    have hq : q=576 := by omega
    subst q
    exact represent_exception 36901 (by decide +kernel)
  by_cases h9 : q≤577
  ·
    have hq : q=577 := by omega
    subst q
    exact represent_exception 36965 (by decide +kernel)
  by_cases h10 : q≤578
  ·
    have hq : q=578 := by omega
    subst q
    exact represent_exception 37029 (by decide +kernel)
  by_cases h11 : q≤579
  ·
    have hq : q=579 := by omega
    subst q
    exact represent_exception 37093 (by decide +kernel)
  by_cases h12 : q≤580
  ·
    have hq : q=580 := by omega
    subst q
    exact represent_exception 37157 (by decide +kernel)
  by_cases h13 : q≤581
  ·
    have hq : q=581 := by omega
    subst q
    exact represent_exception 37221 (by decide +kernel)
  by_cases h14 : q≤582
  ·
    have hq : q=582 := by omega
    subst q
    exact represent_exception 37285 (by decide +kernel)
  by_cases h15 : q≤583
  ·
    have hq : q=583 := by omega
    subst q
    exact represent_exception 37349 (by decide +kernel)
  by_cases h16 : q≤584
  ·
    have hq : q=584 := by omega
    subst q
    exact represent_exception 37413 (by decide +kernel)
  by_cases h17 : q≤690
  ·
    exact four_is_representable 3 _ (c2_13_sound 8 q 5 (by norm_num) (by unfold c2_13; omega))
  by_cases h18 : q≤818
  ·
    exact four_is_representable 3 _ (c2_12_sound 8 q 5 (by norm_num) (by unfold c2_12; omega))
  by_cases h19 : q≤947
  ·
    exact four_is_representable 3 _ (c2_9_sound 8 q 5 (by norm_num) (by unfold c2_9; omega))
  exact four_is_representable 3 _ (c2_15_sound 8 q 5 (by norm_num) (by unfold c2_15; omega))

set_option maxRecDepth 10000 in
def middle_8_2_6 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+2)+6 : ℤ).toNat) := by
  by_cases h0 : q≤311
  ·
    exact four_is_representable 3 _ (c2_7_sound 8 q 6 (by norm_num) (by unfold c2_7; omega))
  by_cases h1 : q≤360
  ·
    exact four_is_representable 3 _ (c2_2_sound 8 q 6 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤404
  ·
    exact four_is_representable 3 _ (c2_23_sound 8 q 6 (by norm_num) (by unfold c2_23; omega))
  by_cases h3 : q≤425
  ·
    exact four_is_representable 3 _ (c2_19_sound 8 q 6 (by norm_num) (by unfold c2_19; omega))
  by_cases h4 : q≤468
  ·
    exact four_is_representable 3 _ (c2_1_sound 8 q 6 (by norm_num) (by unfold c2_1; omega))
  by_cases h5 : q≤528
  ·
    exact four_is_representable 3 _ (c2_0_sound 8 q 6 (by norm_num) (by unfold c2_0; omega))
  by_cases h6 : q≤560
  ·
    exact four_is_representable 3 _ (c2_3_sound 8 q 6 (by norm_num) (by unfold c2_3; omega))
  by_cases h7 : q≤576
  ·
    exact four_is_representable 3 _ (c2_18_sound 8 q 6 (by norm_num) (by unfold c2_18; omega))
  by_cases h8 : q≤577
  ·
    have hq : q=577 := by omega
    subst q
    exact represent_exception 36966 (by decide +kernel)
  by_cases h9 : q≤578
  ·
    have hq : q=578 := by omega
    subst q
    exact represent_exception 37030 (by decide +kernel)
  by_cases h10 : q≤579
  ·
    have hq : q=579 := by omega
    subst q
    exact represent_exception 37094 (by decide +kernel)
  by_cases h11 : q≤580
  ·
    have hq : q=580 := by omega
    subst q
    exact represent_exception 37158 (by decide +kernel)
  by_cases h12 : q≤581
  ·
    have hq : q=581 := by omega
    subst q
    exact represent_exception 37222 (by decide +kernel)
  by_cases h13 : q≤582
  ·
    have hq : q=582 := by omega
    subst q
    exact represent_exception 37286 (by decide +kernel)
  by_cases h14 : q≤583
  ·
    have hq : q=583 := by omega
    subst q
    exact represent_exception 37350 (by decide +kernel)
  by_cases h15 : q≤584
  ·
    have hq : q=584 := by omega
    subst q
    exact represent_exception 37414 (by decide +kernel)
  by_cases h16 : q≤585
  ·
    have hq : q=585 := by omega
    subst q
    exact represent_exception 37478 (by decide +kernel)
  by_cases h17 : q≤694
  ·
    exact four_is_representable 3 _ (c2_13_sound 8 q 6 (by norm_num) (by unfold c2_13; omega))
  by_cases h18 : q≤822
  ·
    exact four_is_representable 3 _ (c2_12_sound 8 q 6 (by norm_num) (by unfold c2_12; omega))
  by_cases h19 : q≤951
  ·
    exact four_is_representable 3 _ (c2_9_sound 8 q 6 (by norm_num) (by unfold c2_9; omega))
  exact four_is_representable 3 _ (c2_15_sound 8 q 6 (by norm_num) (by unfold c2_15; omega))

set_option maxRecDepth 10000 in
def middle_8_2_7 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+2)+7 : ℤ).toNat) := by
  by_cases h0 : q≤312
  ·
    exact four_is_representable 3 _ (c2_7_sound 8 q 7 (by norm_num) (by unfold c2_7; omega))
  by_cases h1 : q≤361
  ·
    exact four_is_representable 3 _ (c2_2_sound 8 q 7 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤406
  ·
    exact four_is_representable 3 _ (c2_23_sound 8 q 7 (by norm_num) (by unfold c2_23; omega))
  by_cases h3 : q≤426
  ·
    exact four_is_representable 3 _ (c2_19_sound 8 q 7 (by norm_num) (by unfold c2_19; omega))
  by_cases h4 : q≤470
  ·
    exact four_is_representable 3 _ (c2_1_sound 8 q 7 (by norm_num) (by unfold c2_1; omega))
  by_cases h5 : q≤530
  ·
    exact four_is_representable 3 _ (c2_0_sound 8 q 7 (by norm_num) (by unfold c2_0; omega))
  by_cases h6 : q≤562
  ·
    exact four_is_representable 3 _ (c2_3_sound 8 q 7 (by norm_num) (by unfold c2_3; omega))
  by_cases h7 : q≤577
  ·
    exact four_is_representable 3 _ (c2_18_sound 8 q 7 (by norm_num) (by unfold c2_18; omega))
  by_cases h8 : q≤578
  ·
    have hq : q=578 := by omega
    subst q
    exact represent_exception 37031 (by decide +kernel)
  by_cases h9 : q≤579
  ·
    have hq : q=579 := by omega
    subst q
    exact represent_exception 37095 (by decide +kernel)
  by_cases h10 : q≤580
  ·
    have hq : q=580 := by omega
    subst q
    exact represent_exception 37159 (by decide +kernel)
  by_cases h11 : q≤581
  ·
    have hq : q=581 := by omega
    subst q
    exact represent_exception 37223 (by decide +kernel)
  by_cases h12 : q≤582
  ·
    have hq : q=582 := by omega
    subst q
    exact represent_exception 37287 (by decide +kernel)
  by_cases h13 : q≤583
  ·
    have hq : q=583 := by omega
    subst q
    exact represent_exception 37351 (by decide +kernel)
  by_cases h14 : q≤584
  ·
    have hq : q=584 := by omega
    subst q
    exact represent_exception 37415 (by decide +kernel)
  by_cases h15 : q≤585
  ·
    have hq : q=585 := by omega
    subst q
    exact represent_exception 37479 (by decide +kernel)
  by_cases h16 : q≤586
  ·
    have hq : q=586 := by omega
    subst q
    exact represent_exception 37543 (by decide +kernel)
  by_cases h17 : q≤698
  ·
    exact four_is_representable 3 _ (c2_13_sound 8 q 7 (by norm_num) (by unfold c2_13; omega))
  by_cases h18 : q≤826
  ·
    exact four_is_representable 3 _ (c2_12_sound 8 q 7 (by norm_num) (by unfold c2_12; omega))
  by_cases h19 : q≤955
  ·
    exact four_is_representable 3 _ (c2_9_sound 8 q 7 (by norm_num) (by unfold c2_9; omega))
  exact four_is_representable 3 _ (c2_15_sound 8 q 7 (by norm_num) (by unfold c2_15; omega))

set_option maxRecDepth 10000 in
def middle_8_2_8 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+2)+8 : ℤ).toNat) := by
  by_cases h0 : q≤313
  ·
    exact four_is_representable 3 _ (c2_7_sound 8 q 8 (by norm_num) (by unfold c2_7; omega))
  by_cases h1 : q≤362
  ·
    exact four_is_representable 3 _ (c2_2_sound 8 q 8 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤408
  ·
    exact four_is_representable 3 _ (c2_23_sound 8 q 8 (by norm_num) (by unfold c2_23; omega))
  by_cases h3 : q≤427
  ·
    exact four_is_representable 3 _ (c2_19_sound 8 q 8 (by norm_num) (by unfold c2_19; omega))
  by_cases h4 : q≤472
  ·
    exact four_is_representable 3 _ (c2_1_sound 8 q 8 (by norm_num) (by unfold c2_1; omega))
  by_cases h5 : q≤532
  ·
    exact four_is_representable 3 _ (c2_0_sound 8 q 8 (by norm_num) (by unfold c2_0; omega))
  by_cases h6 : q≤564
  ·
    exact four_is_representable 3 _ (c2_3_sound 8 q 8 (by norm_num) (by unfold c2_3; omega))
  by_cases h7 : q≤578
  ·
    exact four_is_representable 3 _ (c2_18_sound 8 q 8 (by norm_num) (by unfold c2_18; omega))
  by_cases h8 : q≤579
  ·
    have hq : q=579 := by omega
    subst q
    exact represent_exception 37096 (by decide +kernel)
  by_cases h9 : q≤580
  ·
    have hq : q=580 := by omega
    subst q
    exact represent_exception 37160 (by decide +kernel)
  by_cases h10 : q≤581
  ·
    have hq : q=581 := by omega
    subst q
    exact represent_exception 37224 (by decide +kernel)
  by_cases h11 : q≤582
  ·
    have hq : q=582 := by omega
    subst q
    exact represent_exception 37288 (by decide +kernel)
  by_cases h12 : q≤583
  ·
    have hq : q=583 := by omega
    subst q
    exact represent_exception 37352 (by decide +kernel)
  by_cases h13 : q≤584
  ·
    have hq : q=584 := by omega
    subst q
    exact represent_exception 37416 (by decide +kernel)
  by_cases h14 : q≤585
  ·
    have hq : q=585 := by omega
    subst q
    exact represent_exception 37480 (by decide +kernel)
  by_cases h15 : q≤586
  ·
    have hq : q=586 := by omega
    subst q
    exact represent_exception 37544 (by decide +kernel)
  by_cases h16 : q≤587
  ·
    have hq : q=587 := by omega
    subst q
    exact represent_exception 37608 (by decide +kernel)
  by_cases h17 : q≤702
  ·
    exact four_is_representable 3 _ (c2_13_sound 8 q 8 (by norm_num) (by unfold c2_13; omega))
  by_cases h18 : q≤830
  ·
    exact four_is_representable 3 _ (c2_12_sound 8 q 8 (by norm_num) (by unfold c2_12; omega))
  by_cases h19 : q≤959
  ·
    exact four_is_representable 3 _ (c2_9_sound 8 q 8 (by norm_num) (by unfold c2_9; omega))
  exact four_is_representable 3 _ (c2_15_sound 8 q 8 (by norm_num) (by unfold c2_15; omega))

set_option maxRecDepth 10000 in
def middle_8_2_9 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+2)+9 : ℤ).toNat) := by
  by_cases h0 : q≤314
  ·
    exact four_is_representable 3 _ (c2_7_sound 8 q 9 (by norm_num) (by unfold c2_7; omega))
  by_cases h1 : q≤363
  ·
    exact four_is_representable 3 _ (c2_2_sound 8 q 9 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤410
  ·
    exact four_is_representable 3 _ (c2_23_sound 8 q 9 (by norm_num) (by unfold c2_23; omega))
  by_cases h3 : q≤428
  ·
    exact four_is_representable 3 _ (c2_19_sound 8 q 9 (by norm_num) (by unfold c2_19; omega))
  by_cases h4 : q≤474
  ·
    exact four_is_representable 3 _ (c2_1_sound 8 q 9 (by norm_num) (by unfold c2_1; omega))
  by_cases h5 : q≤534
  ·
    exact four_is_representable 3 _ (c2_0_sound 8 q 9 (by norm_num) (by unfold c2_0; omega))
  by_cases h6 : q≤566
  ·
    exact four_is_representable 3 _ (c2_3_sound 8 q 9 (by norm_num) (by unfold c2_3; omega))
  by_cases h7 : q≤579
  ·
    exact four_is_representable 3 _ (c2_18_sound 8 q 9 (by norm_num) (by unfold c2_18; omega))
  by_cases h8 : q≤580
  ·
    have hq : q=580 := by omega
    subst q
    exact represent_exception 37161 (by decide +kernel)
  by_cases h9 : q≤581
  ·
    have hq : q=581 := by omega
    subst q
    exact represent_exception 37225 (by decide +kernel)
  by_cases h10 : q≤582
  ·
    have hq : q=582 := by omega
    subst q
    exact represent_exception 37289 (by decide +kernel)
  by_cases h11 : q≤583
  ·
    have hq : q=583 := by omega
    subst q
    exact represent_exception 37353 (by decide +kernel)
  by_cases h12 : q≤584
  ·
    have hq : q=584 := by omega
    subst q
    exact represent_exception 37417 (by decide +kernel)
  by_cases h13 : q≤585
  ·
    have hq : q=585 := by omega
    subst q
    exact represent_exception 37481 (by decide +kernel)
  by_cases h14 : q≤586
  ·
    have hq : q=586 := by omega
    subst q
    exact represent_exception 37545 (by decide +kernel)
  by_cases h15 : q≤587
  ·
    have hq : q=587 := by omega
    subst q
    exact represent_exception 37609 (by decide +kernel)
  by_cases h16 : q≤588
  ·
    have hq : q=588 := by omega
    subst q
    exact represent_exception 37673 (by decide +kernel)
  by_cases h17 : q≤706
  ·
    exact four_is_representable 3 _ (c2_13_sound 8 q 9 (by norm_num) (by unfold c2_13; omega))
  by_cases h18 : q≤834
  ·
    exact four_is_representable 3 _ (c2_12_sound 8 q 9 (by norm_num) (by unfold c2_12; omega))
  by_cases h19 : q≤963
  ·
    exact four_is_representable 3 _ (c2_9_sound 8 q 9 (by norm_num) (by unfold c2_9; omega))
  exact four_is_representable 3 _ (c2_15_sound 8 q 9 (by norm_num) (by unfold c2_15; omega))

set_option maxRecDepth 10000 in
def middle_8_2_10 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+2)+10 : ℤ).toNat) := by
  by_cases h0 : q≤315
  ·
    exact four_is_representable 3 _ (c2_7_sound 8 q 10 (by norm_num) (by unfold c2_7; omega))
  by_cases h1 : q≤364
  ·
    exact four_is_representable 3 _ (c2_2_sound 8 q 10 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤412
  ·
    exact four_is_representable 3 _ (c2_23_sound 8 q 10 (by norm_num) (by unfold c2_23; omega))
  by_cases h3 : q≤429
  ·
    exact four_is_representable 3 _ (c2_19_sound 8 q 10 (by norm_num) (by unfold c2_19; omega))
  by_cases h4 : q≤476
  ·
    exact four_is_representable 3 _ (c2_1_sound 8 q 10 (by norm_num) (by unfold c2_1; omega))
  by_cases h5 : q≤536
  ·
    exact four_is_representable 3 _ (c2_0_sound 8 q 10 (by norm_num) (by unfold c2_0; omega))
  by_cases h6 : q≤568
  ·
    exact four_is_representable 3 _ (c2_3_sound 8 q 10 (by norm_num) (by unfold c2_3; omega))
  by_cases h7 : q≤581
  ·
    exact four_is_representable 3 _ (c2_17_sound 8 q 10 (by norm_num) (by unfold c2_17; omega))
  by_cases h8 : q≤582
  ·
    have hq : q=582 := by omega
    subst q
    exact represent_exception 37290 (by decide +kernel)
  by_cases h9 : q≤583
  ·
    have hq : q=583 := by omega
    subst q
    exact represent_exception 37354 (by decide +kernel)
  by_cases h10 : q≤584
  ·
    have hq : q=584 := by omega
    subst q
    exact represent_exception 37418 (by decide +kernel)
  by_cases h11 : q≤585
  ·
    have hq : q=585 := by omega
    subst q
    exact represent_exception 37482 (by decide +kernel)
  by_cases h12 : q≤586
  ·
    have hq : q=586 := by omega
    subst q
    exact represent_exception 37546 (by decide +kernel)
  by_cases h13 : q≤587
  ·
    have hq : q=587 := by omega
    subst q
    exact represent_exception 37610 (by decide +kernel)
  by_cases h14 : q≤588
  ·
    have hq : q=588 := by omega
    subst q
    exact represent_exception 37674 (by decide +kernel)
  by_cases h15 : q≤589
  ·
    have hq : q=589 := by omega
    subst q
    exact represent_exception 37738 (by decide +kernel)
  by_cases h16 : q≤710
  ·
    exact four_is_representable 3 _ (c2_13_sound 8 q 10 (by norm_num) (by unfold c2_13; omega))
  by_cases h17 : q≤838
  ·
    exact four_is_representable 3 _ (c2_12_sound 8 q 10 (by norm_num) (by unfold c2_12; omega))
  by_cases h18 : q≤967
  ·
    exact four_is_representable 3 _ (c2_9_sound 8 q 10 (by norm_num) (by unfold c2_9; omega))
  exact four_is_representable 3 _ (c2_15_sound 8 q 10 (by norm_num) (by unfold c2_15; omega))

set_option maxRecDepth 10000 in
def middle_8_2_11 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+2)+11 : ℤ).toNat) := by
  by_cases h0 : q≤317
  ·
    exact four_is_representable 3 _ (c2_14_sound 8 q 11 (by norm_num) (by unfold c2_14; omega))
  by_cases h1 : q≤365
  ·
    exact four_is_representable 3 _ (c2_2_sound 8 q 11 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤409
  ·
    exact four_is_representable 3 _ (c2_4_sound 8 q 11 (by norm_num) (by unfold c2_4; omega))
  by_cases h3 : q≤414
  ·
    exact four_is_representable 3 _ (c2_23_sound 8 q 11 (by norm_num) (by unfold c2_23; omega))
  by_cases h4 : q≤430
  ·
    exact four_is_representable 3 _ (c2_19_sound 8 q 11 (by norm_num) (by unfold c2_19; omega))
  by_cases h5 : q≤478
  ·
    exact four_is_representable 3 _ (c2_1_sound 8 q 11 (by norm_num) (by unfold c2_1; omega))
  by_cases h6 : q≤538
  ·
    exact four_is_representable 3 _ (c2_0_sound 8 q 11 (by norm_num) (by unfold c2_0; omega))
  by_cases h7 : q≤570
  ·
    exact four_is_representable 3 _ (c2_3_sound 8 q 11 (by norm_num) (by unfold c2_3; omega))
  by_cases h8 : q≤585
  ·
    exact four_is_representable 3 _ (c2_17_sound 8 q 11 (by norm_num) (by unfold c2_17; omega))
  by_cases h9 : q≤586
  ·
    have hq : q=586 := by omega
    subst q
    exact represent_exception 37547 (by decide +kernel)
  by_cases h10 : q≤587
  ·
    have hq : q=587 := by omega
    subst q
    exact represent_exception 37611 (by decide +kernel)
  by_cases h11 : q≤588
  ·
    have hq : q=588 := by omega
    subst q
    exact represent_exception 37675 (by decide +kernel)
  by_cases h12 : q≤589
  ·
    have hq : q=589 := by omega
    subst q
    exact represent_exception 37739 (by decide +kernel)
  by_cases h13 : q≤590
  ·
    have hq : q=590 := by omega
    subst q
    exact represent_exception 37803 (by decide +kernel)
  by_cases h14 : q≤714
  ·
    exact four_is_representable 3 _ (c2_13_sound 8 q 11 (by norm_num) (by unfold c2_13; omega))
  by_cases h15 : q≤842
  ·
    exact four_is_representable 3 _ (c2_12_sound 8 q 11 (by norm_num) (by unfold c2_12; omega))
  by_cases h16 : q≤971
  ·
    exact four_is_representable 3 _ (c2_9_sound 8 q 11 (by norm_num) (by unfold c2_9; omega))
  exact four_is_representable 3 _ (c2_15_sound 8 q 11 (by norm_num) (by unfold c2_15; omega))

set_option maxRecDepth 10000 in
def middle_8_2_12 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+2)+12 : ℤ).toNat) := by
  by_cases h0 : q≤319
  ·
    exact four_is_representable 3 _ (c2_14_sound 8 q 12 (by norm_num) (by unfold c2_14; omega))
  by_cases h1 : q≤366
  ·
    exact four_is_representable 3 _ (c2_2_sound 8 q 12 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤411
  ·
    exact four_is_representable 3 _ (c2_4_sound 8 q 12 (by norm_num) (by unfold c2_4; omega))
  by_cases h3 : q≤416
  ·
    exact four_is_representable 3 _ (c2_23_sound 8 q 12 (by norm_num) (by unfold c2_23; omega))
  by_cases h4 : q≤431
  ·
    exact four_is_representable 3 _ (c2_19_sound 8 q 12 (by norm_num) (by unfold c2_19; omega))
  by_cases h5 : q≤443
  ·
    exact four_is_representable 3 _ (c2_24_sound 8 q 12 (by norm_num) (by unfold c2_24; omega))
  by_cases h6 : q≤480
  ·
    exact four_is_representable 3 _ (c2_1_sound 8 q 12 (by norm_num) (by unfold c2_1; omega))
  by_cases h7 : q≤540
  ·
    exact four_is_representable 3 _ (c2_0_sound 8 q 12 (by norm_num) (by unfold c2_0; omega))
  by_cases h8 : q≤572
  ·
    exact four_is_representable 3 _ (c2_3_sound 8 q 12 (by norm_num) (by unfold c2_3; omega))
  by_cases h9 : q≤589
  ·
    exact four_is_representable 3 _ (c2_17_sound 8 q 12 (by norm_num) (by unfold c2_17; omega))
  by_cases h10 : q≤590
  ·
    have hq : q=590 := by omega
    subst q
    exact represent_exception 37804 (by decide +kernel)
  by_cases h11 : q≤591
  ·
    have hq : q=591 := by omega
    subst q
    exact represent_exception 37868 (by decide +kernel)
  by_cases h12 : q≤718
  ·
    exact four_is_representable 3 _ (c2_13_sound 8 q 12 (by norm_num) (by unfold c2_13; omega))
  by_cases h13 : q≤846
  ·
    exact four_is_representable 3 _ (c2_12_sound 8 q 12 (by norm_num) (by unfold c2_12; omega))
  by_cases h14 : q≤975
  ·
    exact four_is_representable 3 _ (c2_9_sound 8 q 12 (by norm_num) (by unfold c2_9; omega))
  exact four_is_representable 3 _ (c2_15_sound 8 q 12 (by norm_num) (by unfold c2_15; omega))

set_option maxRecDepth 10000 in
def middle_8_2_13 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+2)+13 : ℤ).toNat) := by
  by_cases h0 : q≤321
  ·
    exact four_is_representable 3 _ (c2_14_sound 8 q 13 (by norm_num) (by unfold c2_14; omega))
  by_cases h1 : q≤367
  ·
    exact four_is_representable 3 _ (c2_2_sound 8 q 13 (by norm_num) (by unfold c2_2; omega))
  by_cases h2 : q≤413
  ·
    exact four_is_representable 3 _ (c2_4_sound 8 q 13 (by norm_num) (by unfold c2_4; omega))
  by_cases h3 : q≤418
  ·
    exact four_is_representable 3 _ (c2_23_sound 8 q 13 (by norm_num) (by unfold c2_23; omega))
  by_cases h4 : q≤432
  ·
    exact four_is_representable 3 _ (c2_19_sound 8 q 13 (by norm_num) (by unfold c2_19; omega))
  by_cases h5 : q≤445
  ·
    exact four_is_representable 3 _ (c2_24_sound 8 q 13 (by norm_num) (by unfold c2_24; omega))
  by_cases h6 : q≤482
  ·
    exact four_is_representable 3 _ (c2_1_sound 8 q 13 (by norm_num) (by unfold c2_1; omega))
  by_cases h7 : q≤542
  ·
    exact four_is_representable 3 _ (c2_0_sound 8 q 13 (by norm_num) (by unfold c2_0; omega))
  by_cases h8 : q≤574
  ·
    exact four_is_representable 3 _ (c2_3_sound 8 q 13 (by norm_num) (by unfold c2_3; omega))
  by_cases h9 : q≤593
  ·
    exact four_is_representable 3 _ (c2_17_sound 8 q 13 (by norm_num) (by unfold c2_17; omega))
  by_cases h10 : q≤722
  ·
    exact four_is_representable 3 _ (c2_13_sound 8 q 13 (by norm_num) (by unfold c2_13; omega))
  by_cases h11 : q≤850
  ·
    exact four_is_representable 3 _ (c2_12_sound 8 q 13 (by norm_num) (by unfold c2_12; omega))
  by_cases h12 : q≤979
  ·
    exact four_is_representable 3 _ (c2_9_sound 8 q 13 (by norm_num) (by unfold c2_9; omega))
  exact four_is_representable 3 _ (c2_15_sound 8 q 13 (by norm_num) (by unfold c2_15; omega))

set_option maxRecDepth 10000 in
def middle_8_2_14 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+2)+14 : ℤ).toNat) := by
  by_cases h0 : q≤267
  ·
    exact four_is_representable 3 _ (c2_25_sound 8 q 14 (by norm_num) (by unfold c2_25; omega))
  by_cases h1 : q≤323
  ·
    exact four_is_representable 3 _ (c2_14_sound 8 q 14 (by norm_num) (by unfold c2_14; omega))
  by_cases h2 : q≤368
  ·
    exact four_is_representable 3 _ (c2_2_sound 8 q 14 (by norm_num) (by unfold c2_2; omega))
  by_cases h3 : q≤415
  ·
    exact four_is_representable 3 _ (c2_4_sound 8 q 14 (by norm_num) (by unfold c2_4; omega))
  by_cases h4 : q≤420
  ·
    exact four_is_representable 3 _ (c2_23_sound 8 q 14 (by norm_num) (by unfold c2_23; omega))
  by_cases h5 : q≤433
  ·
    exact four_is_representable 3 _ (c2_19_sound 8 q 14 (by norm_num) (by unfold c2_19; omega))
  by_cases h6 : q≤447
  ·
    exact four_is_representable 3 _ (c2_24_sound 8 q 14 (by norm_num) (by unfold c2_24; omega))
  by_cases h7 : q≤484
  ·
    exact four_is_representable 3 _ (c2_1_sound 8 q 14 (by norm_num) (by unfold c2_1; omega))
  by_cases h8 : q≤544
  ·
    exact four_is_representable 3 _ (c2_0_sound 8 q 14 (by norm_num) (by unfold c2_0; omega))
  by_cases h9 : q≤576
  ·
    exact four_is_representable 3 _ (c2_3_sound 8 q 14 (by norm_num) (by unfold c2_3; omega))
  by_cases h10 : q≤597
  ·
    exact four_is_representable 3 _ (c2_17_sound 8 q 14 (by norm_num) (by unfold c2_17; omega))
  by_cases h11 : q≤726
  ·
    exact four_is_representable 3 _ (c2_13_sound 8 q 14 (by norm_num) (by unfold c2_13; omega))
  by_cases h12 : q≤854
  ·
    exact four_is_representable 3 _ (c2_12_sound 8 q 14 (by norm_num) (by unfold c2_12; omega))
  by_cases h13 : q≤983
  ·
    exact four_is_representable 3 _ (c2_9_sound 8 q 14 (by norm_num) (by unfold c2_9; omega))
  exact four_is_representable 3 _ (c2_15_sound 8 q 14 (by norm_num) (by unfold c2_15; omega))

set_option maxRecDepth 10000 in
def middle_8_2_15 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+2)+15 : ℤ).toNat) := by
  by_cases h0 : q≤269
  ·
    exact four_is_representable 3 _ (c2_25_sound 8 q 15 (by norm_num) (by unfold c2_25; omega))
  by_cases h1 : q≤325
  ·
    exact four_is_representable 3 _ (c2_14_sound 8 q 15 (by norm_num) (by unfold c2_14; omega))
  by_cases h2 : q≤369
  ·
    exact four_is_representable 3 _ (c2_2_sound 8 q 15 (by norm_num) (by unfold c2_2; omega))
  by_cases h3 : q≤417
  ·
    exact four_is_representable 3 _ (c2_4_sound 8 q 15 (by norm_num) (by unfold c2_4; omega))
  by_cases h4 : q≤422
  ·
    exact four_is_representable 3 _ (c2_23_sound 8 q 15 (by norm_num) (by unfold c2_23; omega))
  by_cases h5 : q≤434
  ·
    exact four_is_representable 3 _ (c2_19_sound 8 q 15 (by norm_num) (by unfold c2_19; omega))
  by_cases h6 : q≤449
  ·
    exact four_is_representable 3 _ (c2_24_sound 8 q 15 (by norm_num) (by unfold c2_24; omega))
  by_cases h7 : q≤486
  ·
    exact four_is_representable 3 _ (c2_1_sound 8 q 15 (by norm_num) (by unfold c2_1; omega))
  by_cases h8 : q≤546
  ·
    exact four_is_representable 3 _ (c2_0_sound 8 q 15 (by norm_num) (by unfold c2_0; omega))
  by_cases h9 : q≤578
  ·
    exact four_is_representable 3 _ (c2_3_sound 8 q 15 (by norm_num) (by unfold c2_3; omega))
  by_cases h10 : q≤601
  ·
    exact four_is_representable 3 _ (c2_17_sound 8 q 15 (by norm_num) (by unfold c2_17; omega))
  by_cases h11 : q≤730
  ·
    exact four_is_representable 3 _ (c2_13_sound 8 q 15 (by norm_num) (by unfold c2_13; omega))
  by_cases h12 : q≤858
  ·
    exact four_is_representable 3 _ (c2_12_sound 8 q 15 (by norm_num) (by unfold c2_12; omega))
  by_cases h13 : q≤987
  ·
    exact four_is_representable 3 _ (c2_9_sound 8 q 15 (by norm_num) (by unfold c2_9; omega))
  exact four_is_representable 3 _ (c2_15_sound 8 q 15 (by norm_num) (by unfold c2_15; omega))

set_option maxRecDepth 10000 in
def middle_8_3_0 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+3)+0 : ℤ).toNat) := by
  by_cases h0 : q≤263
  ·
    exact four_is_representable 3 _ (c3_0_sound 8 q 0 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤327
  ·
    exact four_is_representable 3 _ (c3_14_sound 8 q 0 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤370
  ·
    exact four_is_representable 3 _ (c3_16_sound 8 q 0 (by norm_num) (by unfold c3_16; omega))
  by_cases h3 : q≤419
  ·
    exact four_is_representable 3 _ (c3_13_sound 8 q 0 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤424
  ·
    exact four_is_representable 3 _ (c3_26_sound 8 q 0 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤435
  ·
    exact four_is_representable 3 _ (c3_27_sound 8 q 0 (by norm_num) (by unfold c3_27; omega))
  by_cases h6 : q≤451
  ·
    exact four_is_representable 3 _ (c3_24_sound 8 q 0 (by norm_num) (by unfold c3_24; omega))
  by_cases h7 : q≤488
  ·
    exact four_is_representable 3 _ (c3_11_sound 8 q 0 (by norm_num) (by unfold c3_11; omega))
  by_cases h8 : q≤548
  ·
    exact four_is_representable 3 _ (c3_15_sound 8 q 0 (by norm_num) (by unfold c3_15; omega))
  by_cases h9 : q≤580
  ·
    exact four_is_representable 3 _ (c3_17_sound 8 q 0 (by norm_num) (by unfold c3_17; omega))
  by_cases h10 : q≤605
  ·
    exact four_is_representable 3 _ (c3_19_sound 8 q 0 (by norm_num) (by unfold c3_19; omega))
  by_cases h11 : q≤734
  ·
    exact four_is_representable 3 _ (c3_10_sound 8 q 0 (by norm_num) (by unfold c3_10; omega))
  by_cases h12 : q≤822
  ·
    exact four_is_representable 3 _ (c3_23_sound 8 q 0 (by norm_num) (by unfold c3_23; omega))
  by_cases h13 : q≤951
  ·
    exact four_is_representable 3 _ (c3_21_sound 8 q 0 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 3 _ (c3_22_sound 8 q 0 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_8_3_1 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+3)+1 : ℤ).toNat) := by
  by_cases h0 : q≤265
  ·
    exact four_is_representable 3 _ (c3_0_sound 8 q 1 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤329
  ·
    exact four_is_representable 3 _ (c3_14_sound 8 q 1 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤371
  ·
    exact four_is_representable 3 _ (c3_16_sound 8 q 1 (by norm_num) (by unfold c3_16; omega))
  by_cases h3 : q≤421
  ·
    exact four_is_representable 3 _ (c3_13_sound 8 q 1 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤426
  ·
    exact four_is_representable 3 _ (c3_26_sound 8 q 1 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤436
  ·
    exact four_is_representable 3 _ (c3_6_sound 8 q 1 (by norm_num) (by unfold c3_6; omega))
  by_cases h6 : q≤453
  ·
    exact four_is_representable 3 _ (c3_24_sound 8 q 1 (by norm_num) (by unfold c3_24; omega))
  by_cases h7 : q≤490
  ·
    exact four_is_representable 3 _ (c3_11_sound 8 q 1 (by norm_num) (by unfold c3_11; omega))
  by_cases h8 : q≤550
  ·
    exact four_is_representable 3 _ (c3_15_sound 8 q 1 (by norm_num) (by unfold c3_15; omega))
  by_cases h9 : q≤582
  ·
    exact four_is_representable 3 _ (c3_17_sound 8 q 1 (by norm_num) (by unfold c3_17; omega))
  by_cases h10 : q≤609
  ·
    exact four_is_representable 3 _ (c3_19_sound 8 q 1 (by norm_num) (by unfold c3_19; omega))
  by_cases h11 : q≤738
  ·
    exact four_is_representable 3 _ (c3_10_sound 8 q 1 (by norm_num) (by unfold c3_10; omega))
  by_cases h12 : q≤826
  ·
    exact four_is_representable 3 _ (c3_23_sound 8 q 1 (by norm_num) (by unfold c3_23; omega))
  by_cases h13 : q≤955
  ·
    exact four_is_representable 3 _ (c3_21_sound 8 q 1 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 3 _ (c3_22_sound 8 q 1 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_8_3_2 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+3)+2 : ℤ).toNat) := by
  by_cases h0 : q≤267
  ·
    exact four_is_representable 3 _ (c3_0_sound 8 q 2 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤331
  ·
    exact four_is_representable 3 _ (c3_14_sound 8 q 2 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤372
  ·
    exact four_is_representable 3 _ (c3_16_sound 8 q 2 (by norm_num) (by unfold c3_16; omega))
  by_cases h3 : q≤423
  ·
    exact four_is_representable 3 _ (c3_13_sound 8 q 2 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤428
  ·
    exact four_is_representable 3 _ (c3_26_sound 8 q 2 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤438
  ·
    exact four_is_representable 3 _ (c3_6_sound 8 q 2 (by norm_num) (by unfold c3_6; omega))
  by_cases h6 : q≤455
  ·
    exact four_is_representable 3 _ (c3_24_sound 8 q 2 (by norm_num) (by unfold c3_24; omega))
  by_cases h7 : q≤492
  ·
    exact four_is_representable 3 _ (c3_11_sound 8 q 2 (by norm_num) (by unfold c3_11; omega))
  by_cases h8 : q≤552
  ·
    exact four_is_representable 3 _ (c3_15_sound 8 q 2 (by norm_num) (by unfold c3_15; omega))
  by_cases h9 : q≤584
  ·
    exact four_is_representable 3 _ (c3_17_sound 8 q 2 (by norm_num) (by unfold c3_17; omega))
  by_cases h10 : q≤613
  ·
    exact four_is_representable 3 _ (c3_19_sound 8 q 2 (by norm_num) (by unfold c3_19; omega))
  by_cases h11 : q≤742
  ·
    exact four_is_representable 3 _ (c3_10_sound 8 q 2 (by norm_num) (by unfold c3_10; omega))
  by_cases h12 : q≤830
  ·
    exact four_is_representable 3 _ (c3_23_sound 8 q 2 (by norm_num) (by unfold c3_23; omega))
  by_cases h13 : q≤959
  ·
    exact four_is_representable 3 _ (c3_21_sound 8 q 2 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 3 _ (c3_22_sound 8 q 2 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_8_3_3 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+3)+3 : ℤ).toNat) := by
  by_cases h0 : q≤269
  ·
    exact four_is_representable 3 _ (c3_0_sound 8 q 3 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤332
  ·
    exact four_is_representable 3 _ (c3_14_sound 8 q 3 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤373
  ·
    exact four_is_representable 3 _ (c3_16_sound 8 q 3 (by norm_num) (by unfold c3_16; omega))
  by_cases h3 : q≤425
  ·
    exact four_is_representable 3 _ (c3_13_sound 8 q 3 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤430
  ·
    exact four_is_representable 3 _ (c3_26_sound 8 q 3 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤440
  ·
    exact four_is_representable 3 _ (c3_6_sound 8 q 3 (by norm_num) (by unfold c3_6; omega))
  by_cases h6 : q≤457
  ·
    exact four_is_representable 3 _ (c3_24_sound 8 q 3 (by norm_num) (by unfold c3_24; omega))
  by_cases h7 : q≤494
  ·
    exact four_is_representable 3 _ (c3_11_sound 8 q 3 (by norm_num) (by unfold c3_11; omega))
  by_cases h8 : q≤554
  ·
    exact four_is_representable 3 _ (c3_15_sound 8 q 3 (by norm_num) (by unfold c3_15; omega))
  by_cases h9 : q≤586
  ·
    exact four_is_representable 3 _ (c3_17_sound 8 q 3 (by norm_num) (by unfold c3_17; omega))
  by_cases h10 : q≤617
  ·
    exact four_is_representable 3 _ (c3_19_sound 8 q 3 (by norm_num) (by unfold c3_19; omega))
  by_cases h11 : q≤746
  ·
    exact four_is_representable 3 _ (c3_10_sound 8 q 3 (by norm_num) (by unfold c3_10; omega))
  by_cases h12 : q≤834
  ·
    exact four_is_representable 3 _ (c3_23_sound 8 q 3 (by norm_num) (by unfold c3_23; omega))
  by_cases h13 : q≤963
  ·
    exact four_is_representable 3 _ (c3_21_sound 8 q 3 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 3 _ (c3_22_sound 8 q 3 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_8_3_4 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+3)+4 : ℤ).toNat) := by
  by_cases h0 : q≤271
  ·
    exact four_is_representable 3 _ (c3_0_sound 8 q 4 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤333
  ·
    exact four_is_representable 3 _ (c3_14_sound 8 q 4 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤374
  ·
    exact four_is_representable 3 _ (c3_16_sound 8 q 4 (by norm_num) (by unfold c3_16; omega))
  by_cases h3 : q≤427
  ·
    exact four_is_representable 3 _ (c3_13_sound 8 q 4 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤432
  ·
    exact four_is_representable 3 _ (c3_26_sound 8 q 4 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤442
  ·
    exact four_is_representable 3 _ (c3_6_sound 8 q 4 (by norm_num) (by unfold c3_6; omega))
  by_cases h6 : q≤459
  ·
    exact four_is_representable 3 _ (c3_24_sound 8 q 4 (by norm_num) (by unfold c3_24; omega))
  by_cases h7 : q≤496
  ·
    exact four_is_representable 3 _ (c3_11_sound 8 q 4 (by norm_num) (by unfold c3_11; omega))
  by_cases h8 : q≤556
  ·
    exact four_is_representable 3 _ (c3_15_sound 8 q 4 (by norm_num) (by unfold c3_15; omega))
  by_cases h9 : q≤588
  ·
    exact four_is_representable 3 _ (c3_17_sound 8 q 4 (by norm_num) (by unfold c3_17; omega))
  by_cases h10 : q≤621
  ·
    exact four_is_representable 3 _ (c3_19_sound 8 q 4 (by norm_num) (by unfold c3_19; omega))
  by_cases h11 : q≤750
  ·
    exact four_is_representable 3 _ (c3_10_sound 8 q 4 (by norm_num) (by unfold c3_10; omega))
  by_cases h12 : q≤838
  ·
    exact four_is_representable 3 _ (c3_23_sound 8 q 4 (by norm_num) (by unfold c3_23; omega))
  by_cases h13 : q≤967
  ·
    exact four_is_representable 3 _ (c3_21_sound 8 q 4 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 3 _ (c3_22_sound 8 q 4 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_8_3_5 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+3)+5 : ℤ).toNat) := by
  by_cases h0 : q≤273
  ·
    exact four_is_representable 3 _ (c3_0_sound 8 q 5 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤334
  ·
    exact four_is_representable 3 _ (c3_14_sound 8 q 5 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤375
  ·
    exact four_is_representable 3 _ (c3_16_sound 8 q 5 (by norm_num) (by unfold c3_16; omega))
  by_cases h3 : q≤429
  ·
    exact four_is_representable 3 _ (c3_13_sound 8 q 5 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤434
  ·
    exact four_is_representable 3 _ (c3_26_sound 8 q 5 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤444
  ·
    exact four_is_representable 3 _ (c3_6_sound 8 q 5 (by norm_num) (by unfold c3_6; omega))
  by_cases h6 : q≤461
  ·
    exact four_is_representable 3 _ (c3_24_sound 8 q 5 (by norm_num) (by unfold c3_24; omega))
  by_cases h7 : q≤498
  ·
    exact four_is_representable 3 _ (c3_11_sound 8 q 5 (by norm_num) (by unfold c3_11; omega))
  by_cases h8 : q≤558
  ·
    exact four_is_representable 3 _ (c3_15_sound 8 q 5 (by norm_num) (by unfold c3_15; omega))
  by_cases h9 : q≤590
  ·
    exact four_is_representable 3 _ (c3_17_sound 8 q 5 (by norm_num) (by unfold c3_17; omega))
  by_cases h10 : q≤625
  ·
    exact four_is_representable 3 _ (c3_19_sound 8 q 5 (by norm_num) (by unfold c3_19; omega))
  by_cases h11 : q≤754
  ·
    exact four_is_representable 3 _ (c3_10_sound 8 q 5 (by norm_num) (by unfold c3_10; omega))
  by_cases h12 : q≤842
  ·
    exact four_is_representable 3 _ (c3_23_sound 8 q 5 (by norm_num) (by unfold c3_23; omega))
  by_cases h13 : q≤971
  ·
    exact four_is_representable 3 _ (c3_21_sound 8 q 5 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 3 _ (c3_22_sound 8 q 5 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_8_3_6 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+3)+6 : ℤ).toNat) := by
  by_cases h0 : q≤275
  ·
    exact four_is_representable 3 _ (c3_0_sound 8 q 6 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤335
  ·
    exact four_is_representable 3 _ (c3_14_sound 8 q 6 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤376
  ·
    exact four_is_representable 3 _ (c3_16_sound 8 q 6 (by norm_num) (by unfold c3_16; omega))
  by_cases h3 : q≤431
  ·
    exact four_is_representable 3 _ (c3_13_sound 8 q 6 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤436
  ·
    exact four_is_representable 3 _ (c3_26_sound 8 q 6 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤446
  ·
    exact four_is_representable 3 _ (c3_6_sound 8 q 6 (by norm_num) (by unfold c3_6; omega))
  by_cases h6 : q≤463
  ·
    exact four_is_representable 3 _ (c3_24_sound 8 q 6 (by norm_num) (by unfold c3_24; omega))
  by_cases h7 : q≤500
  ·
    exact four_is_representable 3 _ (c3_11_sound 8 q 6 (by norm_num) (by unfold c3_11; omega))
  by_cases h8 : q≤560
  ·
    exact four_is_representable 3 _ (c3_15_sound 8 q 6 (by norm_num) (by unfold c3_15; omega))
  by_cases h9 : q≤592
  ·
    exact four_is_representable 3 _ (c3_17_sound 8 q 6 (by norm_num) (by unfold c3_17; omega))
  by_cases h10 : q≤629
  ·
    exact four_is_representable 3 _ (c3_19_sound 8 q 6 (by norm_num) (by unfold c3_19; omega))
  by_cases h11 : q≤758
  ·
    exact four_is_representable 3 _ (c3_10_sound 8 q 6 (by norm_num) (by unfold c3_10; omega))
  by_cases h12 : q≤846
  ·
    exact four_is_representable 3 _ (c3_23_sound 8 q 6 (by norm_num) (by unfold c3_23; omega))
  by_cases h13 : q≤975
  ·
    exact four_is_representable 3 _ (c3_21_sound 8 q 6 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 3 _ (c3_22_sound 8 q 6 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_8_3_7 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+3)+7 : ℤ).toNat) := by
  by_cases h0 : q≤277
  ·
    exact four_is_representable 3 _ (c3_0_sound 8 q 7 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤336
  ·
    exact four_is_representable 3 _ (c3_14_sound 8 q 7 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤377
  ·
    exact four_is_representable 3 _ (c3_16_sound 8 q 7 (by norm_num) (by unfold c3_16; omega))
  by_cases h3 : q≤433
  ·
    exact four_is_representable 3 _ (c3_13_sound 8 q 7 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤438
  ·
    exact four_is_representable 3 _ (c3_26_sound 8 q 7 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤448
  ·
    exact four_is_representable 3 _ (c3_6_sound 8 q 7 (by norm_num) (by unfold c3_6; omega))
  by_cases h6 : q≤465
  ·
    exact four_is_representable 3 _ (c3_24_sound 8 q 7 (by norm_num) (by unfold c3_24; omega))
  by_cases h7 : q≤502
  ·
    exact four_is_representable 3 _ (c3_11_sound 8 q 7 (by norm_num) (by unfold c3_11; omega))
  by_cases h8 : q≤562
  ·
    exact four_is_representable 3 _ (c3_15_sound 8 q 7 (by norm_num) (by unfold c3_15; omega))
  by_cases h9 : q≤594
  ·
    exact four_is_representable 3 _ (c3_17_sound 8 q 7 (by norm_num) (by unfold c3_17; omega))
  by_cases h10 : q≤633
  ·
    exact four_is_representable 3 _ (c3_19_sound 8 q 7 (by norm_num) (by unfold c3_19; omega))
  by_cases h11 : q≤762
  ·
    exact four_is_representable 3 _ (c3_10_sound 8 q 7 (by norm_num) (by unfold c3_10; omega))
  by_cases h12 : q≤850
  ·
    exact four_is_representable 3 _ (c3_23_sound 8 q 7 (by norm_num) (by unfold c3_23; omega))
  by_cases h13 : q≤979
  ·
    exact four_is_representable 3 _ (c3_21_sound 8 q 7 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 3 _ (c3_22_sound 8 q 7 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_8_3_8 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+3)+8 : ℤ).toNat) := by
  by_cases h0 : q≤279
  ·
    exact four_is_representable 3 _ (c3_0_sound 8 q 8 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤337
  ·
    exact four_is_representable 3 _ (c3_14_sound 8 q 8 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤378
  ·
    exact four_is_representable 3 _ (c3_16_sound 8 q 8 (by norm_num) (by unfold c3_16; omega))
  by_cases h3 : q≤435
  ·
    exact four_is_representable 3 _ (c3_13_sound 8 q 8 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤440
  ·
    exact four_is_representable 3 _ (c3_26_sound 8 q 8 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤450
  ·
    exact four_is_representable 3 _ (c3_6_sound 8 q 8 (by norm_num) (by unfold c3_6; omega))
  by_cases h6 : q≤467
  ·
    exact four_is_representable 3 _ (c3_24_sound 8 q 8 (by norm_num) (by unfold c3_24; omega))
  by_cases h7 : q≤504
  ·
    exact four_is_representable 3 _ (c3_11_sound 8 q 8 (by norm_num) (by unfold c3_11; omega))
  by_cases h8 : q≤564
  ·
    exact four_is_representable 3 _ (c3_15_sound 8 q 8 (by norm_num) (by unfold c3_15; omega))
  by_cases h9 : q≤596
  ·
    exact four_is_representable 3 _ (c3_17_sound 8 q 8 (by norm_num) (by unfold c3_17; omega))
  by_cases h10 : q≤637
  ·
    exact four_is_representable 3 _ (c3_19_sound 8 q 8 (by norm_num) (by unfold c3_19; omega))
  by_cases h11 : q≤766
  ·
    exact four_is_representable 3 _ (c3_10_sound 8 q 8 (by norm_num) (by unfold c3_10; omega))
  by_cases h12 : q≤854
  ·
    exact four_is_representable 3 _ (c3_23_sound 8 q 8 (by norm_num) (by unfold c3_23; omega))
  by_cases h13 : q≤983
  ·
    exact four_is_representable 3 _ (c3_21_sound 8 q 8 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 3 _ (c3_22_sound 8 q 8 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_8_3_9 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+3)+9 : ℤ).toNat) := by
  by_cases h0 : q≤281
  ·
    exact four_is_representable 3 _ (c3_0_sound 8 q 9 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤338
  ·
    exact four_is_representable 3 _ (c3_14_sound 8 q 9 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤379
  ·
    exact four_is_representable 3 _ (c3_16_sound 8 q 9 (by norm_num) (by unfold c3_16; omega))
  by_cases h3 : q≤437
  ·
    exact four_is_representable 3 _ (c3_13_sound 8 q 9 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤442
  ·
    exact four_is_representable 3 _ (c3_26_sound 8 q 9 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤452
  ·
    exact four_is_representable 3 _ (c3_6_sound 8 q 9 (by norm_num) (by unfold c3_6; omega))
  by_cases h6 : q≤469
  ·
    exact four_is_representable 3 _ (c3_24_sound 8 q 9 (by norm_num) (by unfold c3_24; omega))
  by_cases h7 : q≤506
  ·
    exact four_is_representable 3 _ (c3_11_sound 8 q 9 (by norm_num) (by unfold c3_11; omega))
  by_cases h8 : q≤566
  ·
    exact four_is_representable 3 _ (c3_15_sound 8 q 9 (by norm_num) (by unfold c3_15; omega))
  by_cases h9 : q≤598
  ·
    exact four_is_representable 3 _ (c3_17_sound 8 q 9 (by norm_num) (by unfold c3_17; omega))
  by_cases h10 : q≤641
  ·
    exact four_is_representable 3 _ (c3_19_sound 8 q 9 (by norm_num) (by unfold c3_19; omega))
  by_cases h11 : q≤770
  ·
    exact four_is_representable 3 _ (c3_10_sound 8 q 9 (by norm_num) (by unfold c3_10; omega))
  by_cases h12 : q≤858
  ·
    exact four_is_representable 3 _ (c3_23_sound 8 q 9 (by norm_num) (by unfold c3_23; omega))
  by_cases h13 : q≤987
  ·
    exact four_is_representable 3 _ (c3_21_sound 8 q 9 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 3 _ (c3_22_sound 8 q 9 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_8_3_10 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+3)+10 : ℤ).toNat) := by
  by_cases h0 : q≤283
  ·
    exact four_is_representable 3 _ (c3_0_sound 8 q 10 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤339
  ·
    exact four_is_representable 3 _ (c3_14_sound 8 q 10 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤380
  ·
    exact four_is_representable 3 _ (c3_16_sound 8 q 10 (by norm_num) (by unfold c3_16; omega))
  by_cases h3 : q≤439
  ·
    exact four_is_representable 3 _ (c3_13_sound 8 q 10 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤444
  ·
    exact four_is_representable 3 _ (c3_26_sound 8 q 10 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤471
  ·
    exact four_is_representable 3 _ (c3_24_sound 8 q 10 (by norm_num) (by unfold c3_24; omega))
  by_cases h6 : q≤508
  ·
    exact four_is_representable 3 _ (c3_11_sound 8 q 10 (by norm_num) (by unfold c3_11; omega))
  by_cases h7 : q≤568
  ·
    exact four_is_representable 3 _ (c3_15_sound 8 q 10 (by norm_num) (by unfold c3_15; omega))
  by_cases h8 : q≤600
  ·
    exact four_is_representable 3 _ (c3_17_sound 8 q 10 (by norm_num) (by unfold c3_17; omega))
  by_cases h9 : q≤645
  ·
    exact four_is_representable 3 _ (c3_19_sound 8 q 10 (by norm_num) (by unfold c3_19; omega))
  by_cases h10 : q≤774
  ·
    exact four_is_representable 3 _ (c3_10_sound 8 q 10 (by norm_num) (by unfold c3_10; omega))
  by_cases h11 : q≤862
  ·
    exact four_is_representable 3 _ (c3_23_sound 8 q 10 (by norm_num) (by unfold c3_23; omega))
  by_cases h12 : q≤991
  ·
    exact four_is_representable 3 _ (c3_21_sound 8 q 10 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 3 _ (c3_22_sound 8 q 10 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_8_3_11 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+3)+11 : ℤ).toNat) := by
  by_cases h0 : q≤285
  ·
    exact four_is_representable 3 _ (c3_0_sound 8 q 11 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤340
  ·
    exact four_is_representable 3 _ (c3_14_sound 8 q 11 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤381
  ·
    exact four_is_representable 3 _ (c3_7_sound 8 q 11 (by norm_num) (by unfold c3_7; omega))
  by_cases h3 : q≤441
  ·
    exact four_is_representable 3 _ (c3_13_sound 8 q 11 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤446
  ·
    exact four_is_representable 3 _ (c3_26_sound 8 q 11 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤473
  ·
    exact four_is_representable 3 _ (c3_24_sound 8 q 11 (by norm_num) (by unfold c3_24; omega))
  by_cases h6 : q≤510
  ·
    exact four_is_representable 3 _ (c3_11_sound 8 q 11 (by norm_num) (by unfold c3_11; omega))
  by_cases h7 : q≤570
  ·
    exact four_is_representable 3 _ (c3_15_sound 8 q 11 (by norm_num) (by unfold c3_15; omega))
  by_cases h8 : q≤602
  ·
    exact four_is_representable 3 _ (c3_17_sound 8 q 11 (by norm_num) (by unfold c3_17; omega))
  by_cases h9 : q≤649
  ·
    exact four_is_representable 3 _ (c3_19_sound 8 q 11 (by norm_num) (by unfold c3_19; omega))
  by_cases h10 : q≤778
  ·
    exact four_is_representable 3 _ (c3_10_sound 8 q 11 (by norm_num) (by unfold c3_10; omega))
  by_cases h11 : q≤866
  ·
    exact four_is_representable 3 _ (c3_23_sound 8 q 11 (by norm_num) (by unfold c3_23; omega))
  by_cases h12 : q≤995
  ·
    exact four_is_representable 3 _ (c3_21_sound 8 q 11 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 3 _ (c3_22_sound 8 q 11 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_8_3_12 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+3)+12 : ℤ).toNat) := by
  by_cases h0 : q≤287
  ·
    exact four_is_representable 3 _ (c3_0_sound 8 q 12 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤341
  ·
    exact four_is_representable 3 _ (c3_14_sound 8 q 12 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤383
  ·
    exact four_is_representable 3 _ (c3_7_sound 8 q 12 (by norm_num) (by unfold c3_7; omega))
  by_cases h3 : q≤443
  ·
    exact four_is_representable 3 _ (c3_13_sound 8 q 12 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤448
  ·
    exact four_is_representable 3 _ (c3_26_sound 8 q 12 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤475
  ·
    exact four_is_representable 3 _ (c3_24_sound 8 q 12 (by norm_num) (by unfold c3_24; omega))
  by_cases h6 : q≤512
  ·
    exact four_is_representable 3 _ (c3_11_sound 8 q 12 (by norm_num) (by unfold c3_11; omega))
  by_cases h7 : q≤572
  ·
    exact four_is_representable 3 _ (c3_15_sound 8 q 12 (by norm_num) (by unfold c3_15; omega))
  by_cases h8 : q≤604
  ·
    exact four_is_representable 3 _ (c3_17_sound 8 q 12 (by norm_num) (by unfold c3_17; omega))
  by_cases h9 : q≤653
  ·
    exact four_is_representable 3 _ (c3_19_sound 8 q 12 (by norm_num) (by unfold c3_19; omega))
  by_cases h10 : q≤782
  ·
    exact four_is_representable 3 _ (c3_10_sound 8 q 12 (by norm_num) (by unfold c3_10; omega))
  by_cases h11 : q≤870
  ·
    exact four_is_representable 3 _ (c3_23_sound 8 q 12 (by norm_num) (by unfold c3_23; omega))
  by_cases h12 : q≤999
  ·
    exact four_is_representable 3 _ (c3_21_sound 8 q 12 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 3 _ (c3_22_sound 8 q 12 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_8_3_13 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+3)+13 : ℤ).toNat) := by
  by_cases h0 : q≤289
  ·
    exact four_is_representable 3 _ (c3_0_sound 8 q 13 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤342
  ·
    exact four_is_representable 3 _ (c3_14_sound 8 q 13 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤385
  ·
    exact four_is_representable 3 _ (c3_7_sound 8 q 13 (by norm_num) (by unfold c3_7; omega))
  by_cases h3 : q≤445
  ·
    exact four_is_representable 3 _ (c3_13_sound 8 q 13 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤450
  ·
    exact four_is_representable 3 _ (c3_26_sound 8 q 13 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤477
  ·
    exact four_is_representable 3 _ (c3_24_sound 8 q 13 (by norm_num) (by unfold c3_24; omega))
  by_cases h6 : q≤514
  ·
    exact four_is_representable 3 _ (c3_11_sound 8 q 13 (by norm_num) (by unfold c3_11; omega))
  by_cases h7 : q≤574
  ·
    exact four_is_representable 3 _ (c3_15_sound 8 q 13 (by norm_num) (by unfold c3_15; omega))
  by_cases h8 : q≤606
  ·
    exact four_is_representable 3 _ (c3_17_sound 8 q 13 (by norm_num) (by unfold c3_17; omega))
  by_cases h9 : q≤657
  ·
    exact four_is_representable 3 _ (c3_19_sound 8 q 13 (by norm_num) (by unfold c3_19; omega))
  by_cases h10 : q≤786
  ·
    exact four_is_representable 3 _ (c3_10_sound 8 q 13 (by norm_num) (by unfold c3_10; omega))
  by_cases h11 : q≤874
  ·
    exact four_is_representable 3 _ (c3_23_sound 8 q 13 (by norm_num) (by unfold c3_23; omega))
  by_cases h12 : q≤1003
  ·
    exact four_is_representable 3 _ (c3_21_sound 8 q 13 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 3 _ (c3_22_sound 8 q 13 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_8_3_14 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+3)+14 : ℤ).toNat) := by
  by_cases h0 : q≤291
  ·
    exact four_is_representable 3 _ (c3_0_sound 8 q 14 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤343
  ·
    exact four_is_representable 3 _ (c3_14_sound 8 q 14 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤387
  ·
    exact four_is_representable 3 _ (c3_7_sound 8 q 14 (by norm_num) (by unfold c3_7; omega))
  by_cases h3 : q≤447
  ·
    exact four_is_representable 3 _ (c3_13_sound 8 q 14 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤452
  ·
    exact four_is_representable 3 _ (c3_26_sound 8 q 14 (by norm_num) (by unfold c3_26; omega))
  by_cases h5 : q≤479
  ·
    exact four_is_representable 3 _ (c3_24_sound 8 q 14 (by norm_num) (by unfold c3_24; omega))
  by_cases h6 : q≤516
  ·
    exact four_is_representable 3 _ (c3_11_sound 8 q 14 (by norm_num) (by unfold c3_11; omega))
  by_cases h7 : q≤576
  ·
    exact four_is_representable 3 _ (c3_15_sound 8 q 14 (by norm_num) (by unfold c3_15; omega))
  by_cases h8 : q≤608
  ·
    exact four_is_representable 3 _ (c3_17_sound 8 q 14 (by norm_num) (by unfold c3_17; omega))
  by_cases h9 : q≤661
  ·
    exact four_is_representable 3 _ (c3_19_sound 8 q 14 (by norm_num) (by unfold c3_19; omega))
  by_cases h10 : q≤790
  ·
    exact four_is_representable 3 _ (c3_10_sound 8 q 14 (by norm_num) (by unfold c3_10; omega))
  by_cases h11 : q≤878
  ·
    exact four_is_representable 3 _ (c3_23_sound 8 q 14 (by norm_num) (by unfold c3_23; omega))
  by_cases h12 : q≤1007
  ·
    exact four_is_representable 3 _ (c3_21_sound 8 q 14 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 3 _ (c3_22_sound 8 q 14 (by norm_num) (by unfold c3_22; omega))

set_option maxRecDepth 10000 in
def middle_8_3_15 (q : ℤ) (hlo : 256≤q) (hhi : q≤1023) :
    Representable ((16*(4*q+3)+15 : ℤ).toNat) := by
  by_cases h0 : q≤293
  ·
    exact four_is_representable 3 _ (c3_0_sound 8 q 15 (by norm_num) (by unfold c3_0; omega))
  by_cases h1 : q≤344
  ·
    exact four_is_representable 3 _ (c3_14_sound 8 q 15 (by norm_num) (by unfold c3_14; omega))
  by_cases h2 : q≤389
  ·
    exact four_is_representable 3 _ (c3_7_sound 8 q 15 (by norm_num) (by unfold c3_7; omega))
  by_cases h3 : q≤449
  ·
    exact four_is_representable 3 _ (c3_13_sound 8 q 15 (by norm_num) (by unfold c3_13; omega))
  by_cases h4 : q≤481
  ·
    exact four_is_representable 3 _ (c3_24_sound 8 q 15 (by norm_num) (by unfold c3_24; omega))
  by_cases h5 : q≤518
  ·
    exact four_is_representable 3 _ (c3_11_sound 8 q 15 (by norm_num) (by unfold c3_11; omega))
  by_cases h6 : q≤577
  ·
    exact four_is_representable 3 _ (c3_15_sound 8 q 15 (by norm_num) (by unfold c3_15; omega))
  by_cases h7 : q≤578
  ·
    have hq : q=578 := by omega
    subst q
    exact represent_exception 37055 (by decide +kernel)
  by_cases h8 : q≤665
  ·
    exact four_is_representable 3 _ (c3_19_sound 8 q 15 (by norm_num) (by unfold c3_19; omega))
  by_cases h9 : q≤794
  ·
    exact four_is_representable 3 _ (c3_10_sound 8 q 15 (by norm_num) (by unfold c3_10; omega))
  by_cases h10 : q≤882
  ·
    exact four_is_representable 3 _ (c3_23_sound 8 q 15 (by norm_num) (by unfold c3_23; omega))
  by_cases h11 : q≤1011
  ·
    exact four_is_representable 3 _ (c3_21_sound 8 q 15 (by norm_num) (by unfold c3_21; omega))
  exact four_is_representable 3 _ (c3_22_sound 8 q 15 (by norm_num) (by unfold c3_22; omega))

def middle_4_0 (q R : ℤ) (hlo : 128≤q) (hhi : q≤511) (hrl : 0≤R) (hru : R<8) :
    Representable ((8*(4*q+0)+R : ℤ).toNat) := by
  interval_cases R
  · exact middle_4_0_0 q hlo hhi
  · exact middle_4_0_1 q hlo hhi
  · exact middle_4_0_2 q hlo hhi
  · exact middle_4_0_3 q hlo hhi
  · exact middle_4_0_4 q hlo hhi
  · exact middle_4_0_5 q hlo hhi
  · exact middle_4_0_6 q hlo hhi
  · exact middle_4_0_7 q hlo hhi

def middle_4_1 (q R : ℤ) (hlo : 128≤q) (hhi : q≤511) (hrl : 0≤R) (hru : R<8) :
    Representable ((8*(4*q+1)+R : ℤ).toNat) := by
  interval_cases R
  · exact middle_4_1_0 q hlo hhi
  · exact middle_4_1_1 q hlo hhi
  · exact middle_4_1_2 q hlo hhi
  · exact middle_4_1_3 q hlo hhi
  · exact middle_4_1_4 q hlo hhi
  · exact middle_4_1_5 q hlo hhi
  · exact middle_4_1_6 q hlo hhi
  · exact middle_4_1_7 q hlo hhi

def middle_4_2 (q R : ℤ) (hlo : 128≤q) (hhi : q≤511) (hrl : 0≤R) (hru : R<8) :
    Representable ((8*(4*q+2)+R : ℤ).toNat) := by
  interval_cases R
  · exact middle_4_2_0 q hlo hhi
  · exact middle_4_2_1 q hlo hhi
  · exact middle_4_2_2 q hlo hhi
  · exact middle_4_2_3 q hlo hhi
  · exact middle_4_2_4 q hlo hhi
  · exact middle_4_2_5 q hlo hhi
  · exact middle_4_2_6 q hlo hhi
  · exact middle_4_2_7 q hlo hhi

def middle_4_3 (q R : ℤ) (hlo : 128≤q) (hhi : q≤511) (hrl : 0≤R) (hru : R<8) :
    Representable ((8*(4*q+3)+R : ℤ).toNat) := by
  interval_cases R
  · exact middle_4_3_0 q hlo hhi
  · exact middle_4_3_1 q hlo hhi
  · exact middle_4_3_2 q hlo hhi
  · exact middle_4_3_3 q hlo hhi
  · exact middle_4_3_4 q hlo hhi
  · exact middle_4_3_5 q hlo hhi
  · exact middle_4_3_6 q hlo hhi
  · exact middle_4_3_7 q hlo hhi

def middle_8_0 (q R : ℤ) (hlo : 256≤q) (hhi : q≤1023) (hrl : 0≤R) (hru : R<16) :
    Representable ((16*(4*q+0)+R : ℤ).toNat) := by
  interval_cases R
  · exact middle_8_0_0 q hlo hhi
  · exact middle_8_0_1 q hlo hhi
  · exact middle_8_0_2 q hlo hhi
  · exact middle_8_0_3 q hlo hhi
  · exact middle_8_0_4 q hlo hhi
  · exact middle_8_0_5 q hlo hhi
  · exact middle_8_0_6 q hlo hhi
  · exact middle_8_0_7 q hlo hhi
  · exact middle_8_0_8 q hlo hhi
  · exact middle_8_0_9 q hlo hhi
  · exact middle_8_0_10 q hlo hhi
  · exact middle_8_0_11 q hlo hhi
  · exact middle_8_0_12 q hlo hhi
  · exact middle_8_0_13 q hlo hhi
  · exact middle_8_0_14 q hlo hhi
  · exact middle_8_0_15 q hlo hhi

def middle_8_1 (q R : ℤ) (hlo : 256≤q) (hhi : q≤1023) (hrl : 0≤R) (hru : R<16) :
    Representable ((16*(4*q+1)+R : ℤ).toNat) := by
  interval_cases R
  · exact middle_8_1_0 q hlo hhi
  · exact middle_8_1_1 q hlo hhi
  · exact middle_8_1_2 q hlo hhi
  · exact middle_8_1_3 q hlo hhi
  · exact middle_8_1_4 q hlo hhi
  · exact middle_8_1_5 q hlo hhi
  · exact middle_8_1_6 q hlo hhi
  · exact middle_8_1_7 q hlo hhi
  · exact middle_8_1_8 q hlo hhi
  · exact middle_8_1_9 q hlo hhi
  · exact middle_8_1_10 q hlo hhi
  · exact middle_8_1_11 q hlo hhi
  · exact middle_8_1_12 q hlo hhi
  · exact middle_8_1_13 q hlo hhi
  · exact middle_8_1_14 q hlo hhi
  · exact middle_8_1_15 q hlo hhi

def middle_8_2 (q R : ℤ) (hlo : 256≤q) (hhi : q≤1023) (hrl : 0≤R) (hru : R<16) :
    Representable ((16*(4*q+2)+R : ℤ).toNat) := by
  interval_cases R
  · exact middle_8_2_0 q hlo hhi
  · exact middle_8_2_1 q hlo hhi
  · exact middle_8_2_2 q hlo hhi
  · exact middle_8_2_3 q hlo hhi
  · exact middle_8_2_4 q hlo hhi
  · exact middle_8_2_5 q hlo hhi
  · exact middle_8_2_6 q hlo hhi
  · exact middle_8_2_7 q hlo hhi
  · exact middle_8_2_8 q hlo hhi
  · exact middle_8_2_9 q hlo hhi
  · exact middle_8_2_10 q hlo hhi
  · exact middle_8_2_11 q hlo hhi
  · exact middle_8_2_12 q hlo hhi
  · exact middle_8_2_13 q hlo hhi
  · exact middle_8_2_14 q hlo hhi
  · exact middle_8_2_15 q hlo hhi

def middle_8_3 (q R : ℤ) (hlo : 256≤q) (hhi : q≤1023) (hrl : 0≤R) (hru : R<16) :
    Representable ((16*(4*q+3)+R : ℤ).toNat) := by
  interval_cases R
  · exact middle_8_3_0 q hlo hhi
  · exact middle_8_3_1 q hlo hhi
  · exact middle_8_3_2 q hlo hhi
  · exact middle_8_3_3 q hlo hhi
  · exact middle_8_3_4 q hlo hhi
  · exact middle_8_3_5 q hlo hhi
  · exact middle_8_3_6 q hlo hhi
  · exact middle_8_3_7 q hlo hhi
  · exact middle_8_3_8 q hlo hhi
  · exact middle_8_3_9 q hlo hhi
  · exact middle_8_3_10 q hlo hhi
  · exact middle_8_3_11 q hlo hhi
  · exact middle_8_3_12 q hlo hhi
  · exact middle_8_3_13 q hlo hhi
  · exact middle_8_3_14 q hlo hhi
  · exact middle_8_3_15 q hlo hhi

def represent_block_4 (n : ℕ) (hlo : 4096≤n) (hhi : n<16384) : Representable n := by
  let q : ℤ := (n:ℤ)/32
  let R : ℤ := (n:ℤ)%8
  let s : ℤ := ((n:ℤ)/8)%4
  have hqL : 128≤q := by dsimp [q]; omega
  have hqU : q≤511 := by dsimp [q]; omega
  have hRL : 0≤R := by dsimp [R]; omega
  have hRU : R<8 := by dsimp [R]; omega
  have heq : (8*(4*q+s)+R)=(n:ℤ) := by dsimp [q,R,s]; omega
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 := by dsimp [s]; omega
  rcases hs with h|h|h|h
  · have hrep := middle_4_0 q R hqL hqU hRL hRU
    rw [h] at heq
    rw [heq] at hrep
    simpa using hrep
  · have hrep := middle_4_1 q R hqL hqU hRL hRU
    rw [h] at heq
    rw [heq] at hrep
    simpa using hrep
  · have hrep := middle_4_2 q R hqL hqU hRL hRU
    rw [h] at heq
    rw [heq] at hrep
    simpa using hrep
  · have hrep := middle_4_3 q R hqL hqU hRL hRU
    rw [h] at heq
    rw [heq] at hrep
    simpa using hrep

def represent_block_8 (n : ℕ) (hlo : 16384≤n) (hhi : n<65536) : Representable n := by
  let q : ℤ := (n:ℤ)/64
  let R : ℤ := (n:ℤ)%16
  let s : ℤ := ((n:ℤ)/16)%4
  have hqL : 256≤q := by dsimp [q]; omega
  have hqU : q≤1023 := by dsimp [q]; omega
  have hRL : 0≤R := by dsimp [R]; omega
  have hRU : R<16 := by dsimp [R]; omega
  have heq : (16*(4*q+s)+R)=(n:ℤ) := by dsimp [q,R,s]; omega
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 := by dsimp [s]; omega
  rcases hs with h|h|h|h
  · have hrep := middle_8_0 q R hqL hqU hRL hRU
    rw [h] at heq
    rw [heq] at hrep
    simpa using hrep
  · have hrep := middle_8_1 q R hqL hqU hRL hRU
    rw [h] at heq
    rw [heq] at hrep
    simpa using hrep
  · have hrep := middle_8_2 q R hqL hqU hRL hRU
    rw [h] at heq
    rw [heq] at hrep
    simpa using hrep
  · have hrep := middle_8_3 q R hqL hqU hRL hRU
    rw [h] at heq
    rw [heq] at hrep
    simpa using hrep

def represent_middle (n : ℕ) (hlo : 4096≤n) (hhi : n<65536) : Representable n := by
  by_cases h : n<16384
  · exact represent_block_4 n hlo h
  · exact represent_block_8 n (by omega) hhi

end A343268Proof

-- Component: A343268ObstructionCore

namespace A343268Proof
open OMA.S_oeis_a343268

def smallSquares : List ℕ := [3, 10, 15, 36, 45, 54, 63, 136, 153, 170, 187, 204, 221, 238, 255, 528, 561, 594, 627, 660, 693, 726, 759, 792, 825, 858, 891, 924, 957, 990, 1023]

def smallPairs : List ℕ := [6, 13, 18, 20, 25, 30, 39, 46, 48, 51, 55, 57, 60, 64, 66, 69, 72, 73, 78, 81, 90, 99, 108, 117, 126, 139, 146, 151, 156, 163, 168, 172, 173, 180, 181, 185, 189, 190, 197, 198, 199, 202, 206, 207, 214, 215, 216, 219, 223, 224, 231, 232, 233, 236, 240, 241, 248, 249, 250, 253, 257, 258, 265, 266, 267, 270, 272, 274, 275, 283, 284, 289, 291, 292, 300, 301, 306, 309, 318, 323, 340, 357, 374, 391, 408, 425, 442, 459, 476, 493, 510, 531, 538, 543, 564, 571, 573, 576, 582, 591, 597, 604, 606, 609, 615, 624, 630, 637, 639, 642, 648, 657, 663, 664, 670, 672, 675, 681, 690, 696, 697, 698, 703, 705, 708, 714, 715, 723, 729, 730, 731, 732, 736, 738, 741, 747, 748, 749, 756, 762, 763, 764, 765, 766, 769, 771, 774, 780, 781, 782, 783, 789, 795, 796, 797, 798, 799, 802, 804, 807, 813, 814, 815, 816, 822, 828, 829, 830, 831, 832, 835, 837, 840, 846, 847, 848, 849, 855, 861, 862, 863, 864, 865, 868, 870, 873, 879, 880, 881, 882, 888, 894, 895, 896, 897, 898, 901, 903, 906, 912, 913, 914, 915, 921, 927, 928, 929, 930, 931, 934, 936, 939, 945, 946, 947, 948, 954, 960, 961, 962, 963, 964, 967, 969, 972, 978, 979, 980, 981, 987, 993, 994, 995, 996, 997, 1000, 1002, 1005, 1011, 1012, 1013, 1014, 1020, 1026, 1027, 1028, 1029, 1030, 1033, 1035, 1038, 1044, 1045, 1046, 1047, 1053, 1056, 1059, 1060, 1061, 1062, 1063, 1068, 1077, 1078, 1079, 1080, 1086, 1089, 1093, 1094, 1095, 1096, 1110, 1111, 1112, 1113, 1122, 1126, 1127, 1128, 1129, 1143, 1144, 1145, 1146, 1155, 1159, 1160, 1161, 1162, 1176, 1177, 1178, 1179, 1188, 1193, 1194, 1195, 1210, 1211, 1212, 1221, 1227, 1228, 1244, 1245, 1254, 1261, 1278, 1287, 1320, 1353, 1386, 1419, 1452, 1485, 1518, 1551, 1584, 1617, 1650, 1683, 1716, 1749, 1782, 1815, 1848, 1881, 1914, 1947, 1980, 2013, 2046]

def small_square_mem (a : ℕ) (h : IsBinSquare a) (ha : a ≤ 1772) : a ∈ smallSquares := by
  rcases h with ⟨k,m,hk,hm,hmu,rfl⟩
  have hkb : k ≤ 5 := by
    by_contra hc
    have hp : 64 ≤ 2^k := Nat.pow_le_pow_right (by decide : (0:ℕ)<2) (show 6 ≤ k by omega)
    have hq : 32 ≤ 2^(k-1) := Nat.pow_le_pow_right (by decide : (0:ℕ)<2) (show 5 ≤ k-1 by omega)
    have hprod := Nat.mul_le_mul (show 32 ≤ m by omega) (show 65 ≤ 2^k+1 by omega)
    omega
  interval_cases k <;> norm_num at *
  all_goals interval_cases m <;> norm_num [smallSquares]

def small_pair_mem_chunk0 : List ℕ := [3, 10, 15, 36]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def small_pair_mem_cert0 :
    small_pair_mem_chunk0.all (fun a => smallSquares.all (fun b => smallPairs.contains (a+b))) = true := by
  decide +kernel

def small_pair_mem_chunk1 : List ℕ := [45, 54, 63, 136]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def small_pair_mem_cert1 :
    small_pair_mem_chunk1.all (fun a => smallSquares.all (fun b => smallPairs.contains (a+b))) = true := by
  decide +kernel

def small_pair_mem_chunk2 : List ℕ := [153, 170, 187, 204]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def small_pair_mem_cert2 :
    small_pair_mem_chunk2.all (fun a => smallSquares.all (fun b => smallPairs.contains (a+b))) = true := by
  decide +kernel

def small_pair_mem_chunk3 : List ℕ := [221, 238, 255, 528]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def small_pair_mem_cert3 :
    small_pair_mem_chunk3.all (fun a => smallSquares.all (fun b => smallPairs.contains (a+b))) = true := by
  decide +kernel

def small_pair_mem_chunk4 : List ℕ := [561, 594, 627, 660]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def small_pair_mem_cert4 :
    small_pair_mem_chunk4.all (fun a => smallSquares.all (fun b => smallPairs.contains (a+b))) = true := by
  decide +kernel

def small_pair_mem_chunk5 : List ℕ := [693, 726, 759, 792]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def small_pair_mem_cert5 :
    small_pair_mem_chunk5.all (fun a => smallSquares.all (fun b => smallPairs.contains (a+b))) = true := by
  decide +kernel

def small_pair_mem_chunk6 : List ℕ := [825, 858, 891, 924]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def small_pair_mem_cert6 :
    small_pair_mem_chunk6.all (fun a => smallSquares.all (fun b => smallPairs.contains (a+b))) = true := by
  decide +kernel

def small_pair_mem_chunk7 : List ℕ := [957, 990, 1023]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def small_pair_mem_cert7 :
    small_pair_mem_chunk7.all (fun a => smallSquares.all (fun b => smallPairs.contains (a+b))) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
def small_pair_mem_check :
    smallSquares.all (fun a => smallSquares.all (fun b => smallPairs.contains (a+b))) = true := by
  change (small_pair_mem_chunk0 ++ small_pair_mem_chunk1 ++ small_pair_mem_chunk2 ++ small_pair_mem_chunk3 ++ small_pair_mem_chunk4 ++ small_pair_mem_chunk5 ++ small_pair_mem_chunk6 ++ small_pair_mem_chunk7).all (fun a => smallSquares.all (fun b => smallPairs.contains (a+b))) = true
  simp only [Bool.true_and, List.all_append, small_pair_mem_cert0, small_pair_mem_cert1, small_pair_mem_cert2, small_pair_mem_cert3, small_pair_mem_cert4, small_pair_mem_cert5, small_pair_mem_cert6, small_pair_mem_cert7]

def small_pair_mem : ∀ a ∈ smallSquares, ∀ b ∈ smallSquares, a+b ∈ smallPairs := by
  intro a ha b hb
  exact List.contains_iff_mem.mp
    (List.all_eq_true.mp (List.all_eq_true.mp small_pair_mem_check a ha) b hb)

def small_pair_ne_chunk0 : List ℕ := [6, 13, 18, 20, 25, 30, 39, 46, 48, 51, 55, 57, 60, 64, 66, 69, 72, 73, 78, 81, 90, 99, 108, 117, 126, 139, 146, 151, 156, 163, 168, 172]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def small_pair_ne_cert0 :
    small_pair_ne_chunk0.all (fun x => smallPairs.all (fun y => !(x+y == 1772))) = true := by
  decide +kernel

def small_pair_ne_chunk1 : List ℕ := [173, 180, 181, 185, 189, 190, 197, 198, 199, 202, 206, 207, 214, 215, 216, 219, 223, 224, 231, 232, 233, 236, 240, 241, 248, 249, 250, 253, 257, 258, 265, 266]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def small_pair_ne_cert1 :
    small_pair_ne_chunk1.all (fun x => smallPairs.all (fun y => !(x+y == 1772))) = true := by
  decide +kernel

def small_pair_ne_chunk2 : List ℕ := [267, 270, 272, 274, 275, 283, 284, 289, 291, 292, 300, 301, 306, 309, 318, 323, 340, 357, 374, 391, 408, 425, 442, 459, 476, 493, 510, 531, 538, 543, 564, 571]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def small_pair_ne_cert2 :
    small_pair_ne_chunk2.all (fun x => smallPairs.all (fun y => !(x+y == 1772))) = true := by
  decide +kernel

def small_pair_ne_chunk3 : List ℕ := [573, 576, 582, 591, 597, 604, 606, 609, 615, 624, 630, 637, 639, 642, 648, 657, 663, 664, 670, 672, 675, 681, 690, 696, 697, 698, 703, 705, 708, 714, 715, 723]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def small_pair_ne_cert3 :
    small_pair_ne_chunk3.all (fun x => smallPairs.all (fun y => !(x+y == 1772))) = true := by
  decide +kernel

def small_pair_ne_chunk4 : List ℕ := [729, 730, 731, 732, 736, 738, 741, 747, 748, 749, 756, 762, 763, 764, 765, 766, 769, 771, 774, 780, 781, 782, 783, 789, 795, 796, 797, 798, 799, 802, 804, 807]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def small_pair_ne_cert4 :
    small_pair_ne_chunk4.all (fun x => smallPairs.all (fun y => !(x+y == 1772))) = true := by
  decide +kernel

def small_pair_ne_chunk5 : List ℕ := [813, 814, 815, 816, 822, 828, 829, 830, 831, 832, 835, 837, 840, 846, 847, 848, 849, 855, 861, 862, 863, 864, 865, 868, 870, 873, 879, 880, 881, 882, 888, 894]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def small_pair_ne_cert5 :
    small_pair_ne_chunk5.all (fun x => smallPairs.all (fun y => !(x+y == 1772))) = true := by
  decide +kernel

def small_pair_ne_chunk6 : List ℕ := [895, 896, 897, 898, 901, 903, 906, 912, 913, 914, 915, 921, 927, 928, 929, 930, 931, 934, 936, 939, 945, 946, 947, 948, 954, 960, 961, 962, 963, 964, 967, 969]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def small_pair_ne_cert6 :
    small_pair_ne_chunk6.all (fun x => smallPairs.all (fun y => !(x+y == 1772))) = true := by
  decide +kernel

def small_pair_ne_chunk7 : List ℕ := [972, 978, 979, 980, 981, 987, 993, 994, 995, 996, 997, 1000, 1002, 1005, 1011, 1012, 1013, 1014, 1020, 1026, 1027, 1028, 1029, 1030, 1033, 1035, 1038, 1044, 1045, 1046, 1047, 1053]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def small_pair_ne_cert7 :
    small_pair_ne_chunk7.all (fun x => smallPairs.all (fun y => !(x+y == 1772))) = true := by
  decide +kernel

def small_pair_ne_chunk8 : List ℕ := [1056, 1059, 1060, 1061, 1062, 1063, 1068, 1077, 1078, 1079, 1080, 1086, 1089, 1093, 1094, 1095, 1096, 1110, 1111, 1112, 1113, 1122, 1126, 1127, 1128, 1129, 1143, 1144, 1145, 1146, 1155, 1159]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def small_pair_ne_cert8 :
    small_pair_ne_chunk8.all (fun x => smallPairs.all (fun y => !(x+y == 1772))) = true := by
  decide +kernel

def small_pair_ne_chunk9 : List ℕ := [1160, 1161, 1162, 1176, 1177, 1178, 1179, 1188, 1193, 1194, 1195, 1210, 1211, 1212, 1221, 1227, 1228, 1244, 1245, 1254, 1261, 1278, 1287, 1320, 1353, 1386, 1419, 1452, 1485, 1518, 1551, 1584]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def small_pair_ne_cert9 :
    small_pair_ne_chunk9.all (fun x => smallPairs.all (fun y => !(x+y == 1772))) = true := by
  decide +kernel

def small_pair_ne_chunk10 : List ℕ := [1617, 1650, 1683, 1716, 1749, 1782, 1815, 1848, 1881, 1914, 1947, 1980, 2013, 2046]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def small_pair_ne_cert10 :
    small_pair_ne_chunk10.all (fun x => smallPairs.all (fun y => !(x+y == 1772))) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
def small_pair_ne_check :
    smallPairs.all (fun x => smallPairs.all (fun y => !(x+y == 1772))) = true := by
  change (small_pair_ne_chunk0 ++ small_pair_ne_chunk1 ++ small_pair_ne_chunk2 ++ small_pair_ne_chunk3 ++ small_pair_ne_chunk4 ++ small_pair_ne_chunk5 ++ small_pair_ne_chunk6 ++ small_pair_ne_chunk7 ++ small_pair_ne_chunk8 ++ small_pair_ne_chunk9 ++ small_pair_ne_chunk10).all (fun x => smallPairs.all (fun y => !(x+y == 1772))) = true
  simp only [Bool.true_and, List.all_append, small_pair_ne_cert0, small_pair_ne_cert1, small_pair_ne_cert2, small_pair_ne_cert3, small_pair_ne_cert4, small_pair_ne_cert5, small_pair_ne_cert6, small_pair_ne_cert7, small_pair_ne_cert8, small_pair_ne_cert9, small_pair_ne_cert10]

def small_pair_ne : ∀ x ∈ smallPairs, ∀ y ∈ smallPairs, x+y ≠ 1772 := by
  intro x hx y hy
  have h := List.all_eq_true.mp (List.all_eq_true.mp small_pair_ne_check x hx) y hy
  intro he
  simpa only [he, beq_self_eq_true, Bool.not_true, Bool.false_eq_true] using h

def not_four1772 : ¬ ∃ a b c d : ℕ,
    IsBinSquare a ∧ IsBinSquare b ∧ IsBinSquare c ∧ IsBinSquare d ∧ a+b+c+d=1772 := by
  rintro ⟨a,b,c,d,ha,hb,hc,hd,hs⟩
  have hma := small_square_mem a ha (by omega)
  have hmb := small_square_mem b hb (by omega)
  have hmc := small_square_mem c hc (by omega)
  have hmd := small_square_mem d hd (by omega)
  have hp := small_pair_mem a hma b hmb
  have hq := small_pair_mem c hmc d hmd
  have hne := small_pair_ne (a+b) hp (c+d) hq
  apply hne
  omega

end A343268Proof

-- Component: A343268Obstruction

namespace A343268Proof

def not_representable1772 : ¬ Representable 1772 := not_four1772

end A343268Proof

-- Component: A343268Finish

namespace A343268Proof

def represent_above (n : ℕ) (hn : 1772<n) : Representable n := by
  by_cases h1 : n<4096
  · exact represent_small n hn h1
  · by_cases h2 : n<65536
    · exact represent_middle n (by omega) h2
    · exact represent_large n (by omega)

end A343268Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a343268.main := by
  constructor
  · exact A343268Proof.not_representable1772
  · intro n hn
    by_contra h
    exact hn (A343268Proof.represent_above n (by omega))
