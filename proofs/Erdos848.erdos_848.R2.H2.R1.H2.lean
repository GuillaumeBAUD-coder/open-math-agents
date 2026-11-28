import OMAReductions.R_Erdos848_erdos_848_R2_H2_R1
import Mathlib

/-!
# Hall's inequality for the two exceptional residue classes in Erdős 848

At every endpoint N = 25k + 7 the bipartite squarefree-product graph between
the residues 7 and 18 modulo 25 satisfies Hall's inequality. Deldor14
formalized the proof here. For the analytic range we use the root-spacing
and quadratic-residue sieve of Alex Chengyu Li, together with explicit
prime counts and a complementary-divisor argument. For the finite range
we check matchings on successive short suffixes by kernel computation.
Li’s proof of the transformed-root spacing appears in the pure opposite-base
matching subsection of the manuscript.
https://github.com/crabsatellite/erdos-848-squarefree-product/blob/011a0d98f54fb31953a8f0896b4555a70ae56b83/paper/erdos_848_kernel_checked_exact_extremal_bound.tex
The modular squarefree sieve incorporates lemmas
from Raymond Jung's Lean formalization of Sawhney's stability argument.
Apache-2.0 code, with contributors Claude Opus 4.5, GPT-5.2 Pro/xHigh,
Gemini 3.0 and Aristotle.
https://github.com/The-Obstacle-Is-The-Way/erdos-banger/blob/1cc2ac8e9d70516e979733c6ea5c4d2eb652d1f5/formal/lean/Erdos/848.lean
The Hall-cut formulation was suggested by Alex Chengyu Li.
https://github.com/crabsatellite/erdos-848-squarefree-product
-/

open scoped BigOperators

open scoped Finset

open scoped Nat.Prime

namespace Erdos848Gap

end Erdos848Gap

namespace Erdos848Unitary

private theorem coprime_factor_ext {a c a' c' : ℕ}
    (pos : 0 < a*c) (eq : a*c=a'*c') (ha : a.Coprime c) (ha' : a'.Coprime c')
    (hs : a.primeFactors=a'.primeFactors) : a=a' := by
  have pos' : 0 < a'*c' := eq ▸ pos
  have ac := Nat.pos_of_mul_pos_right pos
  have av := Nat.pos_of_mul_pos_left pos
  have ac' := Nat.pos_of_mul_pos_right pos'
  have av' := Nat.pos_of_mul_pos_left pos'
  have h : a.Coprime c' := (Nat.disjoint_primeFactors (by positivity) (by positivity)).mp
    (hs ▸ ha'.disjoint_primeFactors)
  have h' : a'.Coprime c := (Nat.disjoint_primeFactors (by positivity) (by positivity)).mp
    (hs ▸ ha.disjoint_primeFactors)
  apply Nat.dvd_antisymm
  · exact h.dvd_of_dvd_mul_right (eq ▸ dvd_mul_right a c)
  · exact h'.dvd_of_dvd_mul_right (eq ▸ dvd_mul_right a' c')

/-- Count divisors of b with gcd at most two with the complementary factor. -/
theorem count_unitary_keys (b : ℕ) (bpos : 0 < b) :
    (b.divisors.filter (fun g => (Nat.gcd g (b/g)) ∣ 2)).card ≤ 2 * 2^b.primeFactors.card := by
  classical
  let k (g : ℕ) := Nat.gcd g (b/g)
  let a (g : ℕ) := g/k g
  let c (g : ℕ) := (b/g)/k g
  let D := b.divisors.filter (fun g => k g ∣ 2)
  let K := (Finset.Icc 1 2).product b.primeFactors.powerset
  let code (g : ℕ) := (k g, (a g).primeFactors)
  have gd {g : ℕ} (hg : g ∈ D) : g ∣ b := (Nat.mem_divisors.mp (Finset.mem_filter.mp hg).1).1
  have kg {g : ℕ} (hg : g ∈ D) : 0 < k g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos (gd hg) bpos)
  have ag (g : ℕ) : a g*k g=g := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
  have cg (g : ℕ) : c g*k g=b/g := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
  have B {g : ℕ} (hg : g ∈ D) : (a g*c g)*(k g*k g)=b := calc
    _ = (a g*k g)*(c g*k g) := by ring
    _ = b := by rw [ag,cg,Nat.mul_div_cancel' (gd hg)]
  have count : D.card ≤ K.card := by
    apply Finset.card_le_card_of_injOn code
    · intro g hg
      refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨kg hg,?_⟩, Finset.mem_powerset.mpr ?_⟩
      · exact Nat.le_of_dvd (by decide) (Finset.mem_filter.mp hg).2
      · exact Nat.primeFactors_mono ((Nat.div_dvd_of_dvd (Nat.gcd_dvd_left ..)).trans (gd hg)) bpos.ne'
    · intro x hx y hy he
      have hk : k x=k y := congrArg Prod.fst he
      have hs : (a x).primeFactors=(a y).primeFactors := congrArg Prod.snd he
      have e : a x*c x=a y*c y := by
        apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (kg hx) (kg hx))
        rw [B hx,hk,B hy]
      have pp : 0 < a x*c x := Nat.pos_of_mul_pos_right (show 0 < (a x*c x)*(k x*k x) by rw [B hx]; exact bpos)
      have ax := coprime_factor_ext pp e (Nat.coprime_div_gcd_div_gcd (kg hx)) (Nat.coprime_div_gcd_div_gcd (kg hy)) hs
      rw [← ag x,← ag y,ax,hk]
  simpa [K, Finset.card_product] using count

end Erdos848Unitary

namespace Erdos848RootRefined

private theorem root_factor {B D R X T U : ℤ}
    (hr : D*R^2=B*T+1) (hx : D*X^2=B*U+1) : B ∣ (X-R)*(X+R) := by
  refine ⟨R^2*U-X^2*T, ?_⟩
  linear_combination R^2*hx - X^2*hr

private theorem gcd_times_sum {B R X : ℤ} (hx : B ∣ (X-R)*(X+R)) :
    B ∣ (Int.gcd B (X-R) : ℤ)*(X+R) := by
  obtain ⟨q,hq⟩ := hx
  refine ⟨Int.gcdA B (X-R)*(X+R)+Int.gcdB B (X-R)*q, ?_⟩
  rw [Int.gcd_eq_gcd_ab]
  linear_combination Int.gcdB B (X-R)*hq

theorem roots_in_class {B D R X Y T U V : ℤ}
    (hr : D*R^2=B*T+1) (hx : D*X^2=B*U+1) (hy : D*Y^2=B*V+1)
    (hg : Int.gcd B (X-R) = Int.gcd B (Y-R)) : B ∣ 2*(Y-X) := by
  let g : ℤ := Int.gcd B (X-R)
  have h₁ : B ∣ g*(X+R) := gcd_times_sum (root_factor hr hx)
  have h₂ : B ∣ g*(Y+R) := by simpa only [g,hg] using gcd_times_sum (root_factor hr hy)
  have h₃ : B ∣ g*(Y-X) := by
    convert! dvd_sub h₂ h₁ using 1
    ring
  have gx : g ∣ X-R := Int.gcd_dvd_right ..
  have gy : g ∣ Y-R := by simpa only [g,hg] using Int.gcd_dvd_right B (Y-R)
  have gxy : g ∣ Y-X := by
    convert! dvd_sub gy gx using 1
    ring
  have plus : B ∣ (Y-X)*(X+R) := h₁.trans (mul_dvd_mul_right gxy _)
  have minus : B ∣ (Y-X)*(X-R) := by
    rw [mul_comm (Y-X) (X-R)]
    exact h₃.trans (mul_dvd_mul_right gx _)
  have twice : B ∣ 2*R*(Y-X) := by
    convert! dvd_sub plus minus using 1
    ring
  obtain ⟨k,hk⟩ := twice
  refine ⟨D*R*k-2*(Y-X)*T,?_⟩
  linear_combination D*R*hk-2*(Y-X)*hr

theorem root_key_valid {b : ℕ} (bpos : 0 < b) {D R X T U : ℤ}
    (hr : D*R^2=(b : ℤ)*T+1) (hx : D*X^2=(b : ℤ)*U+1) :
    let g := Int.gcd (b : ℤ) (X-R)
    Nat.gcd g (b/g) ∣ 2 := by
  let g := Int.gcd (b : ℤ) (X-R)
  let h := b/g
  let k := Nat.gcd g h
  change k ∣ 2
  have gb : g ∣ b := by exact_mod_cast Int.gcd_dvd_left (b : ℤ) (X-R)
  have gpos := Nat.pos_of_dvd_of_pos gb bpos
  have gh : (g : ℤ)*(h : ℤ)=(b : ℤ) := by exact_mod_cast Nat.mul_div_cancel' gb
  have gs : (b : ℤ) ∣ (g : ℤ)*(X+R) := gcd_times_sum (root_factor hr hx)
  obtain ⟨q,hq⟩ := gs
  have hs : (h : ℤ) ∣ X+R := by
    refine ⟨q,mul_left_cancel₀ (show (g : ℤ) ≠ 0 by exact_mod_cast gpos.ne') ?_⟩
    rw [← mul_assoc,gh,hq]
  have kg : (k : ℤ) ∣ (g : ℤ) := by exact_mod_cast Nat.gcd_dvd_left g h
  have kh : (k : ℤ) ∣ (h : ℤ) := by exact_mod_cast Nat.gcd_dvd_right g h
  have km : (k : ℤ) ∣ X-R := kg.trans (Int.gcd_dvd_right ..)
  have kp : (k : ℤ) ∣ X+R := kh.trans hs
  have kr := dvd_sub kp km
  rw [show X+R-(X-R)=2*R by ring] at kr
  have kb : (k : ℤ) ∣ (b : ℤ) := kg.trans (by exact_mod_cast gb)
  have old : (k : ℤ) ∣ (2*R)*(D*R)-2*((b : ℤ)*T) :=
    dvd_sub (dvd_mul_of_dvd_left kr _) (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left kb _) _)
  have two : (2 : ℤ) = (2*R)*(D*R)-2*((b : ℤ)*T) := by linear_combination -2*hr
  rw [← two] at old
  exact_mod_cast old

end Erdos848RootRefined

namespace Erdos848Gap

/-- Count solutions using a divisor of b and the interval of length b containing 2p. -/
theorem count_mixed_divisors_unitary {N b C U : ℕ} (bpos : 0 < b) (bN : b ≤ N)
    (S : Finset ℕ) (p d : ℕ → ℕ)
    (eq : ∀ n ∈ S, d n * (p n)^2 = b*n+1)
    (pr : ∀ n ∈ S, p n ≤ U) (dr : ∀ n ∈ S, d n*N < C*b) :
    S.card ≤ (C*b/N)*(2*2^b.primeFactors.card)*(2*U/b+1) := by
  classical
  let anchor (j : ℕ) : ℕ := if h : ∃ t ∈ S, d t = j then h.choose else 0
  have anchor_spec (n : ℕ) (hn : n ∈ S) :
      anchor (d n) ∈ S ∧ d (anchor (d n)) = d n := by
    have h : ∃ t ∈ S, d t = d n := ⟨n,hn,rfl⟩
    simpa only [anchor,dif_pos h] using h.choose_spec
  let r (j : ℕ) := p (anchor j)
  let g (n : ℕ) := Int.gcd (b : ℤ) ((p n : ℤ) - (r (d n) : ℤ))
  let code (n : ℕ) := (d n, g n, 2*p n/b)
  let keys := b.divisors.filter (fun j => Nat.gcd j (b/j) ∣ 2)
  let T := (Finset.Icc 1 (C*b/N)).product (keys.product (Finset.range (2*U/b+1)))
  have eqz (n : ℕ) (hn : n ∈ S) :
      (d n : ℤ)*(p n : ℤ)^2=(b : ℤ)*(n : ℤ)+1 := by exact_mod_cast eq n hn
  have Npos := bpos.trans_le bN
  have count : S.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn code
    · intro n hn
      have hdn : 0 < d n := by
        by_contra! h
        have e := eq n hn
        rw [show d n=0 by omega,zero_mul] at e
        omega
      have hdv : g n ∣ b := by
        have hz : (g n : ℤ) ∣ (b : ℤ) := Int.gcd_dvd_left ..
        exact_mod_cast hz
      have hbnd : 2*p n/b ≤ 2*U/b := Nat.div_le_div_right (by have := pr n hn; omega)
      refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hdn,?_⟩, Finset.mem_product.mpr ⟨?_,?_⟩⟩
      · exact (Nat.le_div_iff_mul_le Npos).mpr (dr n hn).le
      · refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdv,bpos.ne'⟩,?_⟩
        have ha := anchor_spec n hn
        have er := eqz _ ha.1
        rw [ha.2] at er
        exact Erdos848RootRefined.root_key_valid bpos er (eqz n hn)
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hbnd)
    · intro x hx y hy hc
      have hd : d x = d y := congrArg Prod.fst hc
      have hg : g x = g y := congrArg (fun u => u.2.1) hc
      have hq : 2*p x/b=2*p y/b := congrArg (fun u => u.2.2) hc
      have ha := anchor_spec x hx
      have er := eqz _ ha.1
      rw [ha.2] at er
      have ey := eqz y hy
      rw [← hd] at ey
      change Int.gcd _ ((p x : ℤ) - (r (d x) : ℤ)) = Int.gcd _ ((p y : ℤ) - (r (d y) : ℤ)) at hg
      rw [← hd] at hg
      have hu := Erdos848RootRefined.roots_in_class er (eqz x hx) ey hg
      have hm : 2*p x ≡ 2*p y [MOD b] := by
        apply Int.natCast_modEq_iff.mp
        rw [Int.modEq_iff_dvd]
        convert! hu using 1
        push_cast
        ring
      have ex := Nat.mod_add_div (2*p x) b
      have ey' := Nat.mod_add_div (2*p y) b
      change (2*p x)%b=(2*p y)%b at hm
      rw [hm,hq] at ex
      have hp : p x=p y := by omega
      have et := eq x hx
      rw [hd,hp,eq y hy] at et
      exact Nat.eq_of_mul_eq_mul_left bpos (by omega)
  have bound : S.card ≤ (C*b/N)*keys.card*(2*U/b+1) := by
    simpa [T, Finset.card_product, mul_assoc] using count
  exact bound.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Erdos848Unitary.count_unitary_keys b bpos)))

end Erdos848Gap

namespace Erdos848Gap
open Finset

theorem support_fourth (b : ℕ) (bp : 0<b) :
    (2*2^b.primeFactors.card)^4 ≤ 8944*b := by
  classical
  let s : Finset ℕ := {2,3,5,7,11,13}
  let weight (p : ℕ) : ℚ := if p∈s then 16 / (p:ℚ) else 1
  have nums (p : ℕ) (hp : p∈s) : p=2 ∨ p=3 ∨ p=5 ∨ p=7 ∨ p=11 ∨ p=13 := by simpa [s] using hp
  have ge (p : ℕ) : 1≤weight p := by
    by_cases hp : p∈s
    · rcases nums p hp with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [weight,s]
    · simp [weight,hp]
  have per (p : ℕ) (hp : p∈b.primeFactors) : (16:ℚ) ≤ weight p * p^(b.factorization p) := by
    have prime := Nat.prime_of_mem_primeFactors hp
    have nz : p∈b.factorization.support := by simpa only [Nat.support_factorization] using hp
    have expo : 0<b.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp nz)
    have qpos : (1:ℚ) ≤ p := by exact_mod_cast prime.one_le
    have factor : (p:ℚ) ≤ p^(b.factorization p) := by
      simpa using pow_le_pow_right₀ qpos (show 1≤b.factorization p from expo)
    by_cases h : p∈s
    · simp only [weight,if_pos h]
      exact (div_mul_cancel₀ 16 (show (p:ℚ)≠0 by positivity)).symm.le.trans
        (mul_le_mul_of_nonneg_left factor (by positivity))
    · have bound : 16≤p := by
        by_contra! small
        interval_cases p <;> norm_num [s] at *
      simp only [weight,if_neg h,one_mul]
      exact (show (16:ℚ)≤p by exact_mod_cast bound).trans factor
  have wTotal : ∏ p∈b.primeFactors,weight p ≤ 559 := by
    rw [← Finset.prod_subset (s₁:=b.primeFactors ∩ s) (s₂:=b.primeFactors) (f:=weight) Finset.inter_subset_left (by
      intro p hp hn
      exact if_neg (fun h => hn (Finset.mem_inter.mpr ⟨hp,h⟩)))]
    calc _ ≤ ∏ p∈s,weight p := Finset.prod_le_prod_of_subset_of_one_le Finset.inter_subset_right
          (fun p _ => (by linarith [ge p] : 0≤weight p)) (fun p _ _ => ge p)
         _ ≤ 559 := by norm_num [weight,s,Finset.prod_insert]
  have prod : (∏ p∈b.primeFactors,(p:ℚ)^(b.factorization p))=b := by
    exact_mod_cast Nat.prod_factorization_pow_eq_self bp.ne'
  have comparison : (16:ℚ)^b.primeFactors.card ≤ 559*b := by
    calc _ = ∏ _∈b.primeFactors,(16:ℚ) := by simp
         _ ≤ ∏ p∈b.primeFactors,weight p*p^(b.factorization p) :=
           Finset.prod_le_prod (fun _ _ => by norm_num) per
         _ ≤ _ := by rw [Finset.prod_mul_distrib,prod]; gcongr
  have n : 16^b.primeFactors.card ≤ 559*b := by exact_mod_cast comparison
  rw [mul_pow,←pow_mul,Nat.mul_comm b.primeFactors.card 4,pow_mul]
  change 16*16^b.primeFactors.card ≤ _
  omega
end Erdos848Gap

namespace Erdos848Gap
open Finset

end Erdos848Gap

namespace Erdos848Gap

end Erdos848Gap
namespace Erdos848Port

def A₇ (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => n % 25 = 7)

def A₁₈ (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => n % 25 = 18)

lemma dvd_pow_two_mul_add_one_iff_zmod_eq_neg_inv
    {p a b : ℕ} (hp : Nat.Prime p) (ha : ¬p ∣ a) :
    p ^ 2 ∣ (a * b + 1) ↔ (b : ZMod (p ^ 2)) = -((a : ZMod (p ^ 2))⁻¹) := by
  set n : ℕ := p ^ 2
  have hcop : Nat.Coprime a n := by
    simpa [n] using hp.coprime_pow_of_not_dvd (m := 2) ha
  have haUnit : IsUnit (a : ZMod n) := (ZMod.isUnit_iff_coprime a n).2 hcop
  constructor
  · intro hdiv
    have hz : ((a * b + 1 : ℕ) : ZMod n) = 0 :=
      (ZMod.natCast_eq_zero_iff (a * b + 1) n).2 hdiv
    have hz' : (a : ZMod n) * (b : ZMod n) + 1 = 0 := by
      simpa [n, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hz
    have hprod : (a : ZMod n) * (b : ZMod n) = (-1 : ZMod n) := by
      simpa using (eq_neg_of_add_eq_zero_left hz')
    have hb : (b : ZMod n) = (a : ZMod n)⁻¹ * (-1 : ZMod n) := by
      have hb0 := congrArg (fun x : ZMod n => (a : ZMod n)⁻¹ * x) hprod
      have hb1 :
          ((a : ZMod n)⁻¹ * (a : ZMod n)) * (b : ZMod n) =
            (a : ZMod n)⁻¹ * (-1 : ZMod n) := by
        simpa [mul_assoc] using hb0
      simpa [ZMod.inv_mul_of_unit (a : ZMod n) haUnit] using hb1
    simpa [n, mul_comm, mul_left_comm, mul_assoc] using hb
  · intro hb
    have hz' : (a : ZMod n) * (b : ZMod n) + 1 = 0 := by
      simp [hb, ZMod.mul_inv_of_unit (a : ZMod n) haUnit]
    have hz : ((a * b + 1 : ℕ) : ZMod n) = 0 := by
      simpa [n, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hz'
    exact (ZMod.natCast_eq_zero_iff (a * b + 1) n).1 hz

lemma cross_residue_not_div_25_of_residue (r a b : ℕ) (hr : r * r % 25 = 24) (ha : a % 25 = r)
    (hb : b % 25 ≠ r) : ¬ (25 ∣ a * b + 1) := by
  intro hdiv
  have hr_lt : r < 25 := by
    have : a % 25 < 25 := Nat.mod_lt a (by decide : 0 < 25)
    simpa [ha] using this
  have h0 : ((a * b + 1 : ℕ) : ZMod 25) = 0 :=
    (ZMod.natCast_eq_zero_iff (a * b + 1) 25).2 hdiv
  have haZ : (a : ZMod 25) = (r : ZMod 25) := by
    have ha_mod : a % 25 = r % 25 := by
      have h := congrArg (fun x => x % 25) ha
      have hleft : (a % 25) % 25 = a % 25 :=
        Nat.mod_eq_of_lt (Nat.mod_lt a (by decide : 0 < 25))
      simpa [hleft] using h
    exact (ZMod.natCast_eq_natCast_iff' a r 25).2 ha_mod
  have h1 : (r : ZMod 25) * (b : ZMod 25) + 1 = 0 := by
    have : (a : ZMod 25) * (b : ZMod 25) + 1 = 0 := by
      simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using h0
    simpa [haZ] using this
  have h2 : (r : ZMod 25) * (b : ZMod 25) = (-1 : ZMod 25) := by
    simpa using (eq_neg_of_add_eq_zero_left h1)
  have hrZ : (r : ZMod 25) * (r : ZMod 25) = (-1 : ZMod 25) := by
    have hrr : ((r * r : ℕ) : ZMod 25) = (24 : ZMod 25) := by
      have : (r * r) % 25 = 24 % 25 := by
        simpa [Nat.mod_eq_of_lt (by decide : 24 < 25)] using hr
      exact (ZMod.natCast_eq_natCast_iff' (r * r) 24 25).2 this
    have hrr' : (r : ZMod 25) * (r : ZMod 25) = (24 : ZMod 25) := by simpa using hrr
    exact hrr'.trans (by decide : (24 : ZMod 25) = (-1 : ZMod 25))
  have hr_inv : (-(r : ZMod 25)) * (r : ZMod 25) = (1 : ZMod 25) := by
    calc
      (-(r : ZMod 25)) * (r : ZMod 25) = -((r : ZMod 25) * (r : ZMod 25)) := by simp
      _ = -(-1 : ZMod 25) := by simp [hrZ]
      _ = (1 : ZMod 25) := by simp
  have hbZ : (b : ZMod 25) = (r : ZMod 25) := by
    have hmul : (-(r : ZMod 25)) * ((r : ZMod 25) * (b : ZMod 25)) =
        (-(r : ZMod 25)) * (-1 : ZMod 25) := by
      simpa [mul_assoc] using congrArg (fun x => (-(r : ZMod 25)) * x) h2
    have hmul' : ((-(r : ZMod 25)) * (r : ZMod 25)) * (b : ZMod 25) =
        (-(r : ZMod 25)) * (-1 : ZMod 25) := by
      simpa [mul_assoc] using hmul
    have hmul'' : ((-(r : ZMod 25)) * (r : ZMod 25)) * (b : ZMod 25) = (r : ZMod 25) := by
      simpa using hmul'
    have : (1 : ZMod 25) * (b : ZMod 25) = (r : ZMod 25) := by
      simpa [hr_inv] using hmul''
    simpa using this
  have hbmod : b % 25 = r := by
    have hb' : b % 25 = r % 25 := (ZMod.natCast_eq_natCast_iff' b r 25).1 hbZ
    simpa [Nat.mod_eq_of_lt hr_lt] using hb'
  exact hb hbmod

noncomputable section DensityLemmas

lemma card_filter_mod_eq_le (N m r : ℕ) :
    ((Finset.range N).filter (fun n => n ≡ r [MOD m])).card ≤ N / m + 1 := by
  have h_set :
      Finset.filter (fun n => n ≡ r [MOD m]) (Finset.range N) ⊆
        Finset.image (fun q => q * m + (r % m)) (Finset.range (N / m + 1)) := by
    intro n hn
    obtain ⟨hnlt,heq⟩ := Finset.mem_filter.mp hn
    have hnN := Finset.mem_range.mp hnlt
    refine Finset.mem_image.mpr ⟨n/m, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hnN.le)), ?_⟩
    change n % m = r % m at heq
    rw [← heq, Nat.mul_comm (n/m) m, Nat.add_comm, Nat.mod_add_div]
  exact le_trans (Finset.card_le_card h_set) (Finset.card_image_le.trans (by norm_num))

lemma card_filter_modEq_and_modEq_le (N m n a b : ℕ) (hcop : Nat.Coprime m n) :
    ((Finset.range N).filter (fun x => x ≡ a [MOD m] ∧ x ≡ b [MOD n])).card ≤ N / (m * n) + 1 := by
  classical
  have hsub :
      (Finset.range N).filter (fun x => x ≡ a [MOD m] ∧ x ≡ b [MOD n]) ⊆
        (Finset.range N).filter (fun x => x ≡ Nat.chineseRemainder hcop a b [MOD m * n]) := by
    intro x hx
    simp [Finset.mem_filter, Finset.mem_range] at hx ⊢
    refine ⟨hx.1, ?_⟩
    exact Nat.chineseRemainder_modEq_unique (co := hcop) hx.2.1 hx.2.2
  have hcard :
      ((Finset.range N).filter (fun x => x ≡ a [MOD m] ∧ x ≡ b [MOD n])).card ≤
        ((Finset.range N).filter (fun x => x ≡ Nat.chineseRemainder hcop a b [MOD m * n])).card :=
    Finset.card_le_card hsub
  exact le_trans hcard (card_filter_mod_eq_le N (m * n) (Nat.chineseRemainder hcop a b))

end DensityLemmas

lemma card_range_filter_mod25_eq (r : ℕ) (hr : r ≤ 24) (N : ℕ) :
    ((Finset.range N).filter (fun n => n % 25 = r)).card = (N + (24 - r)) / 25 := by
  classical
  have hr_lt : r < 25 := lt_of_le_of_lt hr (by decide : 24 < 25)
  set K : ℕ := (N + (24 - r)) / 25
  have hbij :
      ((Finset.range N).filter (fun n => n % 25 = r)).card = (Finset.range K).card := by
    refine (Finset.card_bij (s := Finset.range K) (t := (Finset.range N).filter (fun n => n % 25 = r))
      (i := fun k _hk => 25 * k + r) ?_ ?_ ?_).symm
    · intro k hk
      have hk' : k < K := by simpa [Finset.mem_range] using hk
      have hk1 : k + 1 ≤ K := Nat.succ_le_iff.2 hk'
      have hmul : 25 * (k + 1) ≤ 25 * K := Nat.mul_le_mul_left 25 hk1
      have hK : 25 * K ≤ N + (24 - r) := by
        simpa [K] using Nat.mul_div_le (N + (24 - r)) 25
      have hmul' : 25 * (k + 1) ≤ N + (24 - r) := le_trans hmul hK
      have hlt : 25 * k + r < N := by omega
      simp [Finset.mem_filter, Finset.mem_range, hlt, Nat.add_mod, hr_lt]
    · intro k₁ _hk₁ k₂ _hk₂ h
      have h' : 25 * k₁ = 25 * k₂ := Nat.add_right_cancel h
      exact Nat.mul_left_cancel (by decide : 0 < 25) h'
    · intro a ha
      have ha' : a < N ∧ a % 25 = r := by
        simpa [Finset.mem_filter, Finset.mem_range] using ha
      have ha_eq : 25 * (a / 25) + r = a := by
        have h := Nat.mod_add_div a 25
        simpa [ha'.2, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
      refine ⟨a / 25, ?_, ?_⟩
      · have hlt : 25 * (a / 25) + r < N := by simpa [ha_eq] using ha'.1
        have hmul : 25 * ((a / 25) + 1) ≤ N + (24 - r) := by omega
        have hle : a / 25 + 1 ≤ K := by
          have hmul' : (a / 25 + 1) * 25 ≤ N + (24 - r) := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
          have := (Nat.le_div_iff_mul_le (k0 := (by decide : 0 < 25))).2 hmul'
          simpa [K] using this
        have hltK : a / 25 < K := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hle
        simpa [Finset.mem_range] using hltK
      · exact ha_eq
  simpa [Finset.card_range, K] using hbij

lemma A₇_card (N : ℕ) : (A₇ N).card = (N + 17) / 25 := by
  simpa [A₇, Nat.sub_sub] using (card_range_filter_mod25_eq 7 (by decide) N)

lemma A₁₈_card (N : ℕ) : (A₁₈ N).card = (N + 6) / 25 := by
  simpa [A₁₈, Nat.sub_sub] using (card_range_filter_mod25_eq 18 (by decide) N)

open Filter Finset

def primeCutoff : ℕ := 2000

def primesUpTo (B : ℕ) : Finset ℕ :=
  (Finset.range (B + 1)).filter Nat.Prime

def offPrimesCoarse : Finset ℕ :=
  (primesUpTo primeCutoff).filter (fun p => p ≠ 2 ∧ p ≠ 5)

def no5PrimesCoarse : Finset ℕ :=
  (primesUpTo primeCutoff).filter (fun p => p ≠ 5)

/-- Each prime passes all trial divisions, including trial division by itself. -/
private def sievePass (p : ℕ) : Bool :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43].all fun d =>
    decide (d = 1 ∨ d = p ∨ ¬ d ∣ p)

private theorem prime_sievePass {p : ℕ} (hp : p.Prime) : sievePass p = true := by
  apply List.all_eq_true.mpr
  intro d _
  apply decide_eq_true
  by_cases hd : d ∣ p
  · rcases (Nat.dvd_prime hp).mp hd with eq | eq
    · exact Or.inl eq
    · exact Or.inr (Or.inl eq)
  · exact Or.inr (Or.inr hd)

/-- Round each reciprocal square upward in units of 10⁻¹⁰. -/
private def upperWeight (p : ℕ) : ℕ := 10000000000 / (p*p) + 1

private def sieveTerm (keep : ℕ → Bool) (p : ℕ) : ℕ :=
  if 2 ≤ p ∧ keep p = true ∧ sievePass p = true then upperWeight p else 0

private def accumulate (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => accumulate f i + f i

private theorem accumulate_eq (f : ℕ → ℕ) (n : ℕ) :
    accumulate f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [accumulate]
  | succ n ih => rw [accumulate, Finset.sum_range_succ, ih]

private theorem sum_reciprocal_bound (P : Finset ℕ) (pos : ∀ p ∈ P, 0 < p) :
    ∑ p ∈ P, (1:ℚ)/(p:ℚ)^2 ≤ ((∑ p ∈ P, upperWeight p : ℕ):ℚ) / 10000000000 := by
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro p hp
  have strict := Nat.lt_mul_div_succ 10000000000 (Nat.mul_pos (pos p hp) (pos p hp))
  have h : (10000000000 : ℚ) ≤ ((p*p:ℕ):ℚ) * (upperWeight p : ℚ) := by
    exact_mod_cast strict.le
  push_cast at h
  apply (div_le_div_iff₀ (sq_pos_of_pos (by exact_mod_cast pos p hp)) (by norm_num)).mpr
  linarith only [show (10000000000 : ℚ) ≤ (p:ℚ)^2 * (upperWeight p : ℚ) by simpa [sq] using h]

private theorem sieve_bound (P : Finset ℕ) (keep : ℕ → Bool)
    (member : ∀ p ∈ P, p ∈ Finset.range 2001 ∧ p.Prime ∧ keep p = true) :
    (∑ p ∈ P, (1:ℚ)/(p:ℚ)^2) ≤ (accumulate (sieveTerm keep) 2001 : ℚ) / 10000000000 := by
  have subset : P ⊆ Finset.range 2001 := fun p hp => (member p hp).1
  have total : ∑ p ∈ P, upperWeight p ≤ accumulate (sieveTerm keep) 2001 := by
    rw [accumulate_eq]
    calc
      ∑ p ∈ P, upperWeight p = ∑ p ∈ P, sieveTerm keep p := by
        apply Finset.sum_congr rfl
        intro p hp
        obtain ⟨_, pr, hkeep⟩ := member p hp
        simp only [sieveTerm, pr.two_le, hkeep, prime_sievePass pr, and_self, if_true]
      _ ≤ ∑ p ∈ Finset.range 2001, sieveTerm keep p :=
        Finset.sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => Nat.zero_le _)
  apply (sum_reciprocal_bound P (fun p hp => (member p hp).2.1.pos)).trans
  exact div_le_div_of_nonneg_right (by exact_mod_cast total) (by norm_num)

private def offKeep (p : ℕ) : Bool := decide (p ≠ 2 ∧ p ≠ 5)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem offSumCertificate :
    accumulate (sieveTerm offKeep) 2001 = 1621891203 := by decide +kernel

private def offPrimeSumCoarse : ℚ :=
  ∑ p ∈ offPrimesCoarse, (1:ℚ)/(p:ℚ)^2

private theorem offPrimesCoarse_sum_eq :
    (∑ p ∈ offPrimesCoarse, (1:ℚ)/(p:ℚ)^2) = offPrimeSumCoarse := rfl

private theorem offPrimeSumCoarse_bound :
    offPrimeSumCoarse + (1:ℚ)/primeCutoff ≤ (163:ℚ) / 1000 := by
  have estimate := sieve_bound offPrimesCoarse offKeep (fun p hp => by
    obtain ⟨hpr, pass⟩ := Finset.mem_filter.mp hp
    obtain ⟨hrange, prime⟩ := Finset.mem_filter.mp hpr
    exact ⟨hrange, prime, decide_eq_true pass⟩)
  rw [offSumCertificate] at estimate
  exact (add_le_add_left estimate ((1:ℚ)/2000) : _).trans (by norm_num [primeCutoff])

private def no5Keep (p : ℕ) : Bool := decide (p ≠ 5)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem no5SumCertificate :
    accumulate (sieveTerm no5Keep) 2001 = 4121891204 := by decide +kernel

private def no5PrimeSumCoarse : ℚ :=
  ∑ p ∈ no5PrimesCoarse, (1:ℚ)/(p:ℚ)^2

private theorem no5PrimesCoarse_sum_eq :
    (∑ p ∈ no5PrimesCoarse, (1:ℚ)/(p:ℚ)^2) = no5PrimeSumCoarse := rfl

private theorem no5PrimeSumCoarse_bound :
    no5PrimeSumCoarse + (1:ℚ)/primeCutoff ≤ (413:ℚ) / 1000 := by
  have estimate := sieve_bound no5PrimesCoarse no5Keep (fun p hp => by
    obtain ⟨hpr, pass⟩ := Finset.mem_filter.mp hp
    obtain ⟨hrange, prime⟩ := Finset.mem_filter.mp hpr
    exact ⟨hrange, prime, decide_eq_true pass⟩)
  rw [no5SumCertificate] at estimate
  exact (add_le_add_left estimate ((1:ℚ)/2000) : _).trans (by norm_num [primeCutoff])

lemma sum_Ioc_inv_sq_le_inv (B N : ℕ) (hB : B ≠ 0) :
    (∑ i ∈ Finset.Ioc B N, (1 : ℚ) / (i ^ 2 : ℚ)) ≤ (1 : ℚ) / B := by
  by_cases hBN : B < N
  · have hle : B ≤ N := Nat.le_of_lt hBN
    have hsub := sum_Ioc_inv_sq_le_sub (α := ℚ) (k := B) (n := N) hB hle
    have hnonneg : 0 ≤ (N : ℚ)⁻¹ := by positivity
    have hsub' : (B : ℚ)⁻¹ - (N : ℚ)⁻¹ ≤ (B : ℚ)⁻¹ := sub_le_self _ hnonneg
    simpa [one_div] using hsub.trans hsub'
  · have hIoc : (Finset.Ioc B N) = ∅ := by
      apply Finset.Ioc_eq_empty
      exact not_lt.2 (Nat.le_of_not_gt hBN)
    simp [hIoc, one_div]

def offPrimesUpTo (N : ℕ) : Finset ℕ :=
  (primesUpTo N).filter (fun p => p ≠ 2 ∧ p ≠ 5)

def no5PrimesUpTo (N : ℕ) : Finset ℕ :=
  (primesUpTo N).filter (fun p => p ≠ 5)

lemma sq_pred_add_one_lt_sq (N : ℕ) (hN : 100 ≤ N) : (N - 1) * (N - 1) + 1 < N ^ 2 := by
  have h2 : 2 ≤ N := le_trans (by norm_num : 2 ≤ 100) hN
  have h1 : 1 ≤ N := le_trans (by norm_num : 1 ≤ 2) h2
  have hsub : N - 1 + 1 = N := Nat.sub_add_cancel h1
  have hpos : 0 < N - 1 := by omega
  calc (N - 1) * (N - 1) + 1
      < (N - 1) * (N - 1) + 2 * (N - 1) + 1 := by omega
    _ = (N - 1 + 1) * (N - 1 + 1) := by ring
    _ = N * N := by rw [hsub]
    _ = N ^ 2 := by rw [Nat.pow_two]

set_option maxRecDepth 10000 in
lemma sum_offPrimesUpTo_le (N : ℕ) :
    (∑ p ∈ offPrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (163 : ℚ) / 1000 := by
  classical
  let f : ℕ → ℚ := fun p => (1 : ℚ) / (p ^ 2 : ℚ)
  have hsubset : offPrimesUpTo N ⊆ offPrimesCoarse ∪ Finset.Ioc primeCutoff N := by
    intro p hp
    have hp_mem : p ∈ primesUpTo N := (Finset.mem_filter.1 hp).1
    have hp_cond : p ≠ 2 ∧ p ≠ 5 := (Finset.mem_filter.1 hp).2
    have hp_prime : Nat.Prime p := (Finset.mem_filter.1 hp_mem).2
    have hp_le_N : p ≤ N := by
      have hp_range : p ∈ Finset.range (N + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < N + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    by_cases hp_le_cutoff : p ≤ primeCutoff
    · have hp_mem_cutoff : p ∈ primesUpTo primeCutoff := by
        have hp_lt_cutoff : p < primeCutoff + 1 := Nat.lt_succ_of_le hp_le_cutoff
        simp [primesUpTo, hp_lt_cutoff, hp_prime]
      have : p ∈ offPrimesCoarse := by
        simp [offPrimesCoarse, hp_mem_cutoff, hp_cond.1, hp_cond.2]
      exact Finset.mem_union.2 (Or.inl this)
    · have hp_gt_cutoff : primeCutoff < p := lt_of_not_ge hp_le_cutoff
      have : p ∈ Finset.Ioc primeCutoff N := by
        simp [Finset.mem_Ioc, hp_gt_cutoff, hp_le_N]
      exact Finset.mem_union.2 (Or.inr this)
  have hdisj : Disjoint offPrimesCoarse (Finset.Ioc primeCutoff N) := by
    refine Finset.disjoint_left.2 ?_
    intro p hp_coarse hp_Ioc
    have hp_mem : p ∈ primesUpTo primeCutoff := (Finset.mem_filter.1 hp_coarse).1
    have hp_le_cutoff : p ≤ primeCutoff := by
      have hp_range : p ∈ Finset.range (primeCutoff + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < primeCutoff + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    have hp_gt_cutoff : primeCutoff < p := (Finset.mem_Ioc.1 hp_Ioc).1
    exact (not_lt_of_ge hp_le_cutoff) hp_gt_cutoff
  have hsum_le_union :
      (∑ p ∈ offPrimesUpTo N, f p) ≤ ∑ p ∈ offPrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro p _hp _hnot
    positivity
  have hsum_le :
      (∑ p ∈ offPrimesUpTo N, f p) ≤
        offPrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
    calc
      (∑ p ∈ offPrimesUpTo N, f p) ≤
          ∑ p ∈ offPrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := hsum_le_union
      _ = (∑ p ∈ offPrimesCoarse, f p) + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp [Finset.sum_union hdisj]
      _ = offPrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp only [f, offPrimesCoarse_sum_eq]
  have htail :
      (∑ i ∈ Finset.Ioc primeCutoff N, f i) ≤ (1 : ℚ) / primeCutoff := by
    simpa [f] using sum_Ioc_inv_sq_le_inv primeCutoff N (by simp [primeCutoff])
  have hsum_le' :
      (∑ p ∈ offPrimesUpTo N, f p) ≤ offPrimeSumCoarse + (1 : ℚ) / primeCutoff := by
    exact hsum_le.trans (add_le_add_right htail offPrimeSumCoarse)
  exact hsum_le'.trans offPrimeSumCoarse_bound

set_option maxRecDepth 10000 in
lemma sum_no5PrimesUpTo_le (N : ℕ) :
    (∑ p ∈ no5PrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (413 : ℚ) / 1000 := by
  classical
  let f : ℕ → ℚ := fun p => (1 : ℚ) / (p ^ 2 : ℚ)
  have hsubset : no5PrimesUpTo N ⊆ no5PrimesCoarse ∪ Finset.Ioc primeCutoff N := by
    intro p hp
    have hp_mem : p ∈ primesUpTo N := (Finset.mem_filter.1 hp).1
    have hp_cond : p ≠ 5 := (Finset.mem_filter.1 hp).2
    have hp_prime : Nat.Prime p := (Finset.mem_filter.1 hp_mem).2
    have hp_le_N : p ≤ N := by
      have hp_range : p ∈ Finset.range (N + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < N + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    by_cases hp_le_cutoff : p ≤ primeCutoff
    · have hp_mem_cutoff : p ∈ primesUpTo primeCutoff := by
        have hp_lt_cutoff : p < primeCutoff + 1 := Nat.lt_succ_of_le hp_le_cutoff
        simp [primesUpTo, hp_lt_cutoff, hp_prime]
      have : p ∈ no5PrimesCoarse := by
        simp [no5PrimesCoarse, hp_mem_cutoff, hp_cond]
      exact Finset.mem_union.2 (Or.inl this)
    · have hp_gt_cutoff : primeCutoff < p := lt_of_not_ge hp_le_cutoff
      have : p ∈ Finset.Ioc primeCutoff N := by
        simp [Finset.mem_Ioc, hp_gt_cutoff, hp_le_N]
      exact Finset.mem_union.2 (Or.inr this)
  have hdisj : Disjoint no5PrimesCoarse (Finset.Ioc primeCutoff N) := by
    refine Finset.disjoint_left.2 ?_
    intro p hp_coarse hp_Ioc
    have hp_mem : p ∈ primesUpTo primeCutoff := (Finset.mem_filter.1 hp_coarse).1
    have hp_le_cutoff : p ≤ primeCutoff := by
      have hp_range : p ∈ Finset.range (primeCutoff + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < primeCutoff + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    have hp_gt_cutoff : primeCutoff < p := (Finset.mem_Ioc.1 hp_Ioc).1
    exact (not_lt_of_ge hp_le_cutoff) hp_gt_cutoff
  have hsum_le_union :
      (∑ p ∈ no5PrimesUpTo N, f p) ≤ ∑ p ∈ no5PrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro p _hp _hnot
    positivity
  have hsum_le :
      (∑ p ∈ no5PrimesUpTo N, f p) ≤
        no5PrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
    calc
      (∑ p ∈ no5PrimesUpTo N, f p) ≤
          ∑ p ∈ no5PrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := hsum_le_union
      _ = (∑ p ∈ no5PrimesCoarse, f p) + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp [Finset.sum_union hdisj]
      _ = no5PrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp only [f, no5PrimesCoarse_sum_eq]
  have htail :
      (∑ i ∈ Finset.Ioc primeCutoff N, f i) ≤ (1 : ℚ) / primeCutoff := by
    simpa [f] using sum_Ioc_inv_sq_le_inv primeCutoff N (by simp [primeCutoff])
  have hsum_le' :
      (∑ p ∈ no5PrimesUpTo N, f p) ≤ no5PrimeSumCoarse + (1 : ℚ) / primeCutoff := by
    exact hsum_le.trans (add_le_add_right htail no5PrimeSumCoarse)
  exact hsum_le'.trans no5PrimeSumCoarse_bound

lemma prime_eq_of_dvd_5 (p : ℕ) (hp : Nat.Prime p) (h : p ∣ 5) : p = 5 := by
  have hp_le5 : p ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) h
  have hp_ge2 : 2 ≤ p := hp.two_le
  interval_cases p <;> simp_all

lemma coprime_25_pow_two_of_prime_ne5 (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≠ 5) :
    Nat.Coprime 25 (p ^ 2) := by
  have hnot : ¬ p ∣ 25 := by
    intro h
    have hpow : p ∣ 5 ^ 2 := by
      have : (5 ^ 2 : ℕ) = 25 := by rfl
      simpa [this] using h
    have h5 : p ∣ 5 := hp.dvd_of_dvd_pow hpow
    exact hp5 (prime_eq_of_dvd_5 p hp h5)
  simpa [Nat.coprime_comm] using hp.coprime_pow_of_not_dvd (a := 25) (m := 2) hnot

lemma prime_square_exists {n : ℕ} (hn : ¬ Squarefree n) :
    ∃ p : ℕ, Nat.Prime p ∧ p ^ 2 ∣ n := by
  classical
  have hnot : ¬ ∀ p : ℕ, Nat.Prime p → ¬ p * p ∣ n := by
    intro hall
    exact hn ((Nat.squarefree_iff_prime_squarefree).2 hall)
  push Not at hnot
  rcases hnot with ⟨p, hp, hpp⟩
  refine ⟨p, hp, ?_⟩
  simpa [pow_two] using hpp

lemma prime_square_exists_ne5 {n : ℕ} (hn : ¬ Squarefree n) (h25 : ¬ 25 ∣ n) :
    ∃ p : ℕ, Nat.Prime p ∧ p ≠ 5 ∧ p ^ 2 ∣ n := by
  obtain ⟨p, hp, hp2⟩ := prime_square_exists (n := n) hn
  refine ⟨p, hp, ?_, hp2⟩
  intro hp5
  subst hp5
  have : 25 ∣ n := by simpa [pow_two] using hp2
  exact (h25 this).elim

lemma cross_residue_7_18_not_div_25 (a b : ℕ) (ha : a % 25 = 7) (hb : b % 25 = 18) :
    ¬ (25 ∣ a * b + 1) := by
  have hb_ne : b % 25 ≠ 7 := by
    intro hb7
    have : (18 : ℕ) = 7 := hb.symm.trans hb7
    exact (by decide : (18 : ℕ) ≠ 7) this
  exact cross_residue_not_div_25_of_residue 7 a b (by norm_num) ha hb_ne

lemma cross_residue_18_7_not_div_25 (a b : ℕ) (ha : a % 25 = 18) (hb : b % 25 = 7) :
    ¬ (25 ∣ a * b + 1) := by
  simpa [Nat.mul_comm] using cross_residue_7_18_not_div_25 b a hb ha

lemma off_count_modEq25_le (N p b t : ℕ) (hp : Nat.Prime p) (hb : ¬ p ∣ b) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1)).card ≤
      N / (25 * p ^ 2) + 1 := by
  classical
  have hcop : Nat.Coprime 25 (p ^ 2) := coprime_25_pow_two_of_prime_ne5 p hp hp5
  have hp0 : (p ^ 2 : ℕ) ≠ 0 := pow_ne_zero 2 hp.ne_zero
  let rZ : ZMod (p ^ 2) := -((b : ZMod (p ^ 2))⁻¹)
  let r : ℕ := rZ.val
  have hrZ : (r : ZMod (p ^ 2)) = rZ := by
    have : NeZero (p ^ 2) := ⟨hp0⟩
    simp [r, rZ]
  have hsubset :
      (Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1) ⊆
        (Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ a ≡ r [MOD p ^ 2]) := by
    intro a ha
    simp [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨ha.1, ha.2.1, ?_⟩
    have hdiv : p ^ 2 ∣ b * a + 1 := ha.2.2
    have hEq : (a : ZMod (p ^ 2)) = -((b : ZMod (p ^ 2))⁻¹) := by
      have : p ^ 2 ∣ b * a + 1 := by simpa [Nat.mul_comm] using hdiv
      exact (dvd_pow_two_mul_add_one_iff_zmod_eq_neg_inv (p := p) (a := b) (b := a) hp hb).1 this
    have : (a : ZMod (p ^ 2)) = (r : ZMod (p ^ 2)) := by
      simpa [rZ, hrZ] using hEq
    exact (ZMod.natCast_eq_natCast_iff a r (p ^ 2)).1 this
  have hcard := Finset.card_le_card hsubset
  exact le_trans hcard (card_filter_modEq_and_modEq_le N 25 (p ^ 2) t r hcop)

private lemma not_sq_dvd_mul_add_one_of_prime_dvd_left
    {p b a : ℕ} (hp : Nat.Prime p) (hb : p ∣ b) : ¬ p ^ 2 ∣ b * a + 1 := by
  intro hp2
  have hp1 : p ∣ b * a + 1 := Nat.dvd_of_pow_dvd (by decide : 1 ≤ 2) hp2
  have hpa : p ∣ b * a := dvd_mul_of_dvd_left hb a
  have : p ∣ 1 := (Nat.dvd_add_right hpa).mp hp1
  exact hp.not_dvd_one this

lemma filter_empty_of_prime_dvd_left_of_pred
    {N p b : ℕ} (hp : Nat.Prime p) (hb : p ∣ b)
    (pred : ℕ → Prop) [DecidablePred pred] :
    (Finset.range N).filter (fun a => pred a ∧ p ^ 2 ∣ b * a + 1) = ∅ := by
  classical
  ext a
  simp [not_sq_dvd_mul_add_one_of_prime_dvd_left (p := p) (b := b) (a := a) hp hb]

lemma off_count_modEq25_le' (N p b t : ℕ) (hp : Nat.Prime p) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1)).card ≤
      N / (25 * p ^ 2) + 1 := by
  by_cases hb : p ∣ b
  · 
    have hempty :
        (Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1) = ∅ := by
      simpa using
        (filter_empty_of_prime_dvd_left_of_pred (N := N) (p := p) (b := b) hp hb
          (pred := fun a => a ≡ t [MOD 25]))
    simp [hempty]
  · exact off_count_modEq25_le N p b t hp hb hp5

lemma prime_le_of_sq_dvd_lt_sq {p N X : ℕ} (hXpos : 0 < X) (hXlt : X < N ^ 2) (hp2 : p ^ 2 ∣ X) : p ≤ N := by
  have hp2_le : p ^ 2 ≤ X := Nat.le_of_dvd hXpos hp2
  have hp2_lt : p ^ 2 < N ^ 2 := lt_of_le_of_lt hp2_le hXlt
  by_contra hp_le
  have hNp : N ≤ p := le_of_lt (Nat.not_le.mp hp_le)
  have hN2le : N ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hNp 2
  exact (not_lt_of_ge hN2le) hp2_lt

lemma sum_div_add_one_le_real (N : ℕ) (P : Finset ℕ) (k : ℕ) :
    ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) ≤
      (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (P.card : ℝ) := by
  classical
  have hsplit :
      ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) =
        ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) + (P.card : ℝ) := by
    have :
        (∑ p ∈ P, (N / (k * p ^ 2) + 1 : ℕ)) =
          (∑ p ∈ P, (N / (k * p ^ 2) : ℕ)) + P.card := by
      simp [Finset.sum_add_distrib]
    exact_mod_cast this
  have hterm :
      ∀ p ∈ P, ((N / (k * p ^ 2) : ℕ) : ℝ) ≤ (N : ℝ) / (k * (p : ℝ) ^ 2) := by
    intro p hp
    have h := (Nat.cast_div_le (α := ℝ) (m := N) (n := k * p ^ 2))
    simpa [Nat.cast_mul, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using h
  have hdiv' :
      ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) ≤
        ∑ p ∈ P, (N : ℝ) / (k * (p : ℝ) ^ 2) := by
    exact_mod_cast (Finset.sum_le_sum fun p hp => hterm p hp)
  have hdiv :
      ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) ≤
        (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) := by
    have :
        (∑ p ∈ P, (N : ℝ) / (k * (p : ℝ) ^ 2)) =
          (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) := by
      simp [div_eq_mul_inv, mul_sum, mul_comm]
    exact hdiv'.trans (le_of_eq this)
  have h := add_le_add_right hdiv (P.card : ℝ)
  calc
    ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) =
        ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) + (P.card : ℝ) := hsplit
    _ ≤ (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (P.card : ℝ) := by
        simpa [add_comm, add_left_comm, add_assoc] using h

lemma sieve_set_card_bound
    (N k : ℕ) (P S : Finset ℕ) (pred : ℕ → ℕ → Prop) [∀ p, DecidablePred (pred p)]
    (hsubset :
      S ⊆ P.biUnion (fun p => (Finset.range N).filter (fun n => pred p n)))
    (hper : ∀ p ∈ P, ((Finset.range N).filter (fun n => pred p n)).card ≤ N / (k * p ^ 2) + 1) :
    (S.card : ℝ) ≤
      (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (P.card : ℝ) := by
  classical
  have hcard : S.card ≤ (∑ p ∈ P, (N / (k * p ^ 2) + 1)) := by
    calc
      S.card ≤
          ((P.biUnion (fun p => (Finset.range N).filter (fun n => pred p n))).card) :=
        Finset.card_le_card hsubset
      _ ≤ ∑ p ∈ P, ((Finset.range N).filter (fun n => pred p n)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ p ∈ P, (N / (k * p ^ 2) + 1) := by
          apply Finset.sum_le_sum
          intro p hp
          exact hper p hp
  have hcard_real :
      (S.card : ℝ) ≤ ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  exact hcard_real.trans (sum_div_add_one_le_real (N := N) (P := P) (k := k))

end Erdos848Port

/- Quantitative bounds on prime-square errors in cross-residue bipartite graphs. -/
namespace Erdos848Pure
open Erdos848Gap Finset
private theorem count_by_theta (N M e : ℕ) (Mpos : 0 < M)
    (hlogM : Real.log (M : ℝ) = e * Real.log 2)
    : e*N.primeCounting ≤ e*M+2*N := by
  let small := N.primesLE.filter (fun q => q ≤ M)
  let large := N.primesLE.filter (fun q => ¬ q ≤ M)
  have partition : small.card + large.card = N.primeCounting := by
    simpa only [small, large, Nat.primesLE_card_eq_primeCounting] using
      (Finset.card_filter_add_card_filter_not (s := N.primesLE) (fun q => q ≤ M))
  have sub : small ⊆ Finset.Icc 1 M := by
    intro q hq
    obtain ⟨hp, hle⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.pos, hle⟩
  have hsmall : small.card ≤ M := by simpa using Finset.card_le_card sub
  have filterSub : large ⊆ N.primesLE := Finset.filter_subset _ _
  have lower : (large.card : ℝ) * Real.log M ≤ Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    calc
      (large.card : ℝ) * Real.log M = ∑ _q ∈ large, Real.log M := by simp
      _ ≤ ∑ q ∈ large, Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        apply Real.log_le_log (by exact_mod_cast Mpos)
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hq).2))
      _ ≤ ∑ q ∈ N.primesLE, Real.log q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg filterSub
        intro q hq _
        exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hq).2.one_lt.le)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hupper := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by positivity)
  rw [hlogM] at lower
  rw [hlog4] at hupper
  have hlarge : e * (large.card : ℝ) ≤ 2 * (N : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    linarith only [lower, hupper]
  have count : (small.card : ℝ) + (large.card : ℝ) = N.primeCounting := by exact_mod_cast partition
  have sm : (small.card : ℝ) ≤ M := by exact_mod_cast hsmall
  exact_mod_cast (show e*(N.primeCounting : ℝ) ≤ e*(M : ℝ)+2*(N : ℝ) by
    nlinarith only [count, hlarge, mul_le_mul_of_nonneg_left sm (show (0:ℝ) ≤ (e:ℝ) by positivity)])


private theorem log_nat_two_pow (n : ℕ) : Real.log ((2^n : ℕ) : ℝ) = n*Real.log 2 := by
  rw [Nat.cast_pow,Real.log_pow]
  norm_num

private theorem mixed24_count {N b : ℕ} (bp : 0<b) (bn : b≤N)
    (S : Finset ℕ) (p d : ℕ → ℕ)
    (eq : ∀ n∈S,d n*(p n)^2=b*n+1) (pr : ∀ n∈S,p n≤N)
    (link : ∀ n∈S, ∀ c : ℕ, N<c*p n → d n*N < c^2*b)
    (cut : ∀ n∈S,N<24*p n) : S.card ≤ 876*(2*2^b.primeFactors.card) := by
  classical
  let small := S.filter (fun n => 6*p n≤N)
  let large := S.filter (fun n => ¬ 6*p n≤N)
  have smallS : small ⊆ S := Finset.filter_subset _ _
  have largeS : large ⊆ S := Finset.filter_subset _ _
  have pr' (n) (hn : n∈small) : p n≤N/6 := by
    have := (Finset.mem_filter.mp hn).2
    omega
  have d1 (n) (hn : n∈small) : d n*N<576*b := by
    exact link n (smallS hn) 24 (cut n (smallS hn))
  have d2 (n) (hn : n∈large) : d n*N<36*b := by
    exact link n (largeS hn) 6 (lt_of_not_ge (Finset.mem_filter.mp hn).2)
  have s := count_mixed_divisors_unitary bp bn small p d (fun n h => eq n (smallS h)) pr' d1
  have lraw := count_mixed_divisors_unitary bp bn large p d (fun n h => eq n (largeS h))
    (fun n h => pr n (largeS h)) d2
  let P := 576*b/N
  let W := 2*(N/6)/b
  have pd : P*N ≤ 576*b := Nat.div_mul_le_self _ _
  have wd : W*b ≤ 2*(N/6) := Nat.div_mul_le_self _ _
  have u : 6*(N/6)≤N := by omega
  have num : 3*(W*b) ≤ N := by omega
  have Np : 0<N := bp.trans_le bn
  have p250 : P≤576 := by
    exact Nat.le_of_mul_le_mul_right (pd.trans (Nat.mul_le_mul_left _ bn)) Np
  have pw : P*W≤192 := by
    have z := (Nat.mul_le_mul_right W pd).trans_eq (show 576*b*W=576*(W*b) by ring)
    have a := (Nat.mul_le_mul_left 192 num)
    have l1 : (P*W)*N ≤ 192*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right l1 Np
  have sum : P*(W+1) ≤ 768 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have sa : small.card ≤ 768*(2*2^b.primeFactors.card) := by
    refine s.trans ?_
    calc _ = (P*(W+1))*(2*2^b.primeFactors.card) := by dsimp only [P,W]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ sum
  let Q := 36*b/N
  let K := 2*N/b
  have qd : Q*N ≤ 36*b := Nat.div_mul_le_self _ _
  have kd : K*b ≤ 2*N := Nat.div_mul_le_self _ _
  have q1600 : Q≤36 := Nat.le_of_mul_le_mul_right (qd.trans (Nat.mul_le_mul_left _ bn)) Np
  have qk : Q*K ≤ 72 := by
    have z := Nat.mul_le_mul_right K qd
    have a := Nat.mul_le_mul_left 36 kd
    have mul : (Q*K)*N ≤ 72*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right mul Np
  have qsum : Q*(K+1) ≤ 108 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have l : large.card ≤ 108*(2*2^b.primeFactors.card) := by
    refine lraw.trans ?_
    calc _ = (Q*(K+1))*(2*2^b.primeFactors.card) := by dsimp only [Q,K]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ qsum
  have parts : small.card+large.card=S.card := Finset.card_filter_add_card_filter_not _
  omega

private theorem mixed24_error {N b : ℕ} (big : 400000000 ≤ N) (bp : 0<b) (bn : b≤N)
    {z : ℕ} (bound : z ≤ 876*(2*2^b.primeFactors.card)) : 330*z ≤ N := by
  have powb := support_fourth b bp
  have h : 330*z ≤ 289080*(2*2^b.primeFactors.card) := by omega
  apply h.trans
  by_contra! bad
  have lo := Nat.pow_lt_pow_left bad (by decide : 4≠0)
  rw [mul_pow] at lo
  have hi := Nat.mul_le_mul_left (289080^4) (powb.trans (Nat.mul_le_mul_left 8944 bn))
  have cutoff := Nat.pow_le_pow_left big 3
  have mc := Nat.mul_le_mul_right N cutoff
  nlinarith only [lo,hi,mc,Nat.zero_le N]
theorem large_mixed_24 {N b : ℕ} (big : 400000000 ≤ N) (bN : b < N)
    (S : Finset ℕ) (choosePrime : ∀n∈S, n < N ∧ ∃p : ℕ, p≤N ∧ N < 24*p ∧ p^2 ∣ b*n+1) :
    330*S.card ≤ N := by
  classical
  by_cases non : S.Nonempty
  · let p (n : ℕ) := if h : n ∈ S then ((choosePrime n h).2).choose else 1
    let d (n : ℕ) := (b*n+1)/(p n)^2
    have info (n : ℕ) (hn : n ∈ S) : p n ≤ N ∧ N < 24*p n ∧ (p n)^2 ∣ b*n+1 := by
      simpa only [p,dif_pos hn] using ((choosePrime n hn).2).choose_spec
    have eq (n : ℕ) (hn : n ∈ S) : d n*(p n)^2 = b*n+1 := Nat.div_mul_cancel (info n hn).2.2
    obtain ⟨v,hv⟩ := non
    have bp : 0 < b := by
      by_contra! h
      have bz : b=0 := by omega
      have hd := (info v hv).2.2
      simp only [bz,zero_mul,zero_add,Nat.dvd_one] at hd
      have hq := (info v hv).2.1
      have pq : 2 ≤ p v := by omega
      have sq := Nat.pow_le_pow_left pq 2
      omega
    have bound (n : ℕ) (hn : n∈S) : b*n+1 ≤ b*N := by
      have h := Nat.mul_le_mul_left b (show n+1 ≤ N from (choosePrime n hn).1)
      rw [Nat.mul_add,Nat.mul_one] at h
      omega
    have link (n : ℕ) (hn : n∈S) (c : ℕ) (lc : N<c*p n) : d n*N<c^2*b := by
      have positive : 0<d n := by
        by_contra! dz
        have e := eq n hn
        rw [show d n=0 by omega,zero_mul] at e
        omega
      have rr := Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left lc (by decide : 2≠0)) positive
      have bd := Nat.mul_le_mul_left (c^2) (bound n hn)
      have scaled := congrArg (c^2*·) (eq n hn)
      have cmp : (d n*N)*N < (c^2*b)*N := by nlinarith only [rr,bd,scaled]
      exact Nat.lt_of_mul_lt_mul_right cmp
    exact mixed24_error big bp bN.le (mixed24_count bp bN.le S p d eq (fun n hn => (info n hn).1) link
      (fun n hn => (info n hn).2.1))
  · rw [Finset.not_nonempty_iff_eq_empty.mp non]
    simp

theorem small_primes_24 {N : ℕ} (big : 400000000 ≤ N) (Q : Finset ℕ)
    (prime : ∀ p ∈ Q, p.Prime) (small : ∀ p ∈ Q, 24*p ≤ N) :
    190 * Q.card ≤ N := by
  let X := N/24
  have sub : Q ⊆ X.primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨by dsimp [X]; have := small p hp; omega,prime p hp⟩
  have count := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at count
  have weight := count_by_theta X (2^17) 17 (by decide) (log_nat_two_pow 17)
  have trunc : 24*X≤N := by dsimp [X]; omega
  norm_num at weight
  omega

private theorem mixed112_count {N b : ℕ} (bp : 0<b) (bn : b≤N)
    (S : Finset ℕ) (p d : ℕ → ℕ)
    (eq : ∀ n∈S,d n*(p n)^2=b*n+1) (pr : ∀ n∈S,p n≤N)
    (link : ∀ n∈S, ∀ c : ℕ, N<c*p n → d n*N < c^2*b)
    (cut : ∀ n∈S,N<112*p n) : S.card ≤ 14924*(2*2^b.primeFactors.card) := by
  classical
  let small := S.filter (fun n => 14*p n≤N)
  let large := S.filter (fun n => ¬ 14*p n≤N)
  have smallS : small ⊆ S := Finset.filter_subset _ _
  have largeS : large ⊆ S := Finset.filter_subset _ _
  have pr' (n) (hn : n∈small) : p n≤N/14 := by
    have := (Finset.mem_filter.mp hn).2
    omega
  have d1 (n) (hn : n∈small) : d n*N<12544*b := by
    exact link n (smallS hn) 112 (cut n (smallS hn))
  have d2 (n) (hn : n∈large) : d n*N<196*b := by
    exact link n (largeS hn) 14 (lt_of_not_ge (Finset.mem_filter.mp hn).2)
  have s := count_mixed_divisors_unitary bp bn small p d (fun n h => eq n (smallS h)) pr' d1
  have lraw := count_mixed_divisors_unitary bp bn large p d (fun n h => eq n (largeS h))
    (fun n h => pr n (largeS h)) d2
  let P := 12544*b/N
  let W := 2*(N/14)/b
  have pd : P*N ≤ 12544*b := Nat.div_mul_le_self _ _
  have wd : W*b ≤ 2*(N/14) := Nat.div_mul_le_self _ _
  have u : 14*(N/14)≤N := by omega
  have num : 7*(W*b) ≤ N := by omega
  have Np : 0<N := bp.trans_le bn
  have p250 : P≤12544 := by
    exact Nat.le_of_mul_le_mul_right (pd.trans (Nat.mul_le_mul_left _ bn)) Np
  have pw : P*W≤1792 := by
    have z := (Nat.mul_le_mul_right W pd).trans_eq (show 12544*b*W=12544*(W*b) by ring)
    have a := (Nat.mul_le_mul_left 1792 num)
    have l1 : (P*W)*N ≤ 1792*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right l1 Np
  have sum : P*(W+1) ≤ 14336 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have sa : small.card ≤ 14336*(2*2^b.primeFactors.card) := by
    refine s.trans ?_
    calc _ = (P*(W+1))*(2*2^b.primeFactors.card) := by dsimp only [P,W]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ sum
  let Q := 196*b/N
  let K := 2*N/b
  have qd : Q*N ≤ 196*b := Nat.div_mul_le_self _ _
  have kd : K*b ≤ 2*N := Nat.div_mul_le_self _ _
  have q1600 : Q≤196 := Nat.le_of_mul_le_mul_right (qd.trans (Nat.mul_le_mul_left _ bn)) Np
  have qk : Q*K ≤ 392 := by
    have z := Nat.mul_le_mul_right K qd
    have a := Nat.mul_le_mul_left 196 kd
    have mul : (Q*K)*N ≤ 392*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right mul Np
  have qsum : Q*(K+1) ≤ 588 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have l : large.card ≤ 588*(2*2^b.primeFactors.card) := by
    refine lraw.trans ?_
    calc _ = (Q*(K+1))*(2*2^b.primeFactors.card) := by dsimp only [Q,K]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ qsum
  have parts : small.card+large.card=S.card := Finset.card_filter_add_card_filter_not _
  omega

private theorem mixed112_error {N b : ℕ} (big : 250000000000 ≤ N) (bp : 0<b) (bn : b≤N)
    {z : ℕ} (bound : z ≤ 14924*(2*2^b.primeFactors.card)) : 2430*z ≤ N := by
  have powb := support_fourth b bp
  have h : 2430*z ≤ 36265320*(2*2^b.primeFactors.card) := by omega
  apply h.trans
  by_contra! bad
  have lo := Nat.pow_lt_pow_left bad (by decide : 4≠0)
  rw [mul_pow] at lo
  have hi := Nat.mul_le_mul_left (36265320^4) (powb.trans (Nat.mul_le_mul_left 8944 bn))
  have cutoff := Nat.pow_le_pow_left big 3
  have mc := Nat.mul_le_mul_right N cutoff
  nlinarith only [lo,hi,mc,Nat.zero_le N]
theorem large_mixed_112 {N b : ℕ} (big : 250000000000 ≤ N) (bN : b < N)
    (S : Finset ℕ) (choosePrime : ∀n∈S, n < N ∧ ∃p : ℕ, p≤N ∧ N < 112*p ∧ p^2 ∣ b*n+1) :
    2430*S.card ≤ N := by
  classical
  by_cases non : S.Nonempty
  · let p (n : ℕ) := if h : n ∈ S then ((choosePrime n h).2).choose else 1
    let d (n : ℕ) := (b*n+1)/(p n)^2
    have info (n : ℕ) (hn : n ∈ S) : p n ≤ N ∧ N < 112*p n ∧ (p n)^2 ∣ b*n+1 := by
      simpa only [p,dif_pos hn] using ((choosePrime n hn).2).choose_spec
    have eq (n : ℕ) (hn : n ∈ S) : d n*(p n)^2 = b*n+1 := Nat.div_mul_cancel (info n hn).2.2
    obtain ⟨v,hv⟩ := non
    have bp : 0 < b := by
      by_contra! h
      have bz : b=0 := by omega
      have hd := (info v hv).2.2
      simp only [bz,zero_mul,zero_add,Nat.dvd_one] at hd
      have hq := (info v hv).2.1
      have pq : 2 ≤ p v := by omega
      have sq := Nat.pow_le_pow_left pq 2
      omega
    have bound (n : ℕ) (hn : n∈S) : b*n+1 ≤ b*N := by
      have h := Nat.mul_le_mul_left b (show n+1 ≤ N from (choosePrime n hn).1)
      rw [Nat.mul_add,Nat.mul_one] at h
      omega
    have link (n : ℕ) (hn : n∈S) (c : ℕ) (lc : N<c*p n) : d n*N<c^2*b := by
      have positive : 0<d n := by
        by_contra! dz
        have e := eq n hn
        rw [show d n=0 by omega,zero_mul] at e
        omega
      have rr := Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left lc (by decide : 2≠0)) positive
      have bd := Nat.mul_le_mul_left (c^2) (bound n hn)
      have scaled := congrArg (c^2*·) (eq n hn)
      have cmp : (d n*N)*N < (c^2*b)*N := by nlinarith only [rr,bd,scaled]
      exact Nat.lt_of_mul_lt_mul_right cmp
    exact mixed112_error big bp bN.le (mixed112_count bp bN.le S p d eq (fun n hn => (info n hn).1) link
      (fun n hn => (info n hn).2.1))
  · rw [Finset.not_nonempty_iff_eq_empty.mp non]
    simp

theorem small_primes_112 {N : ℕ} (big : 250000000000 ≤ N) (Q : Finset ℕ)
    (prime : ∀ p ∈ Q, p.Prime) (small : ∀ p ∈ Q, 112*p ≤ N) :
    1230 * Q.card ≤ N := by
  let X := N/112
  have sub : Q ⊆ X.primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨by dsimp [X]; have := small p hp; omega,prime p hp⟩
  have count := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at count
  have weight := count_by_theta X (2^23) 23 (by decide) (log_nat_two_pow 23)
  have trunc : 112*X≤N := by dsimp [X]; omega
  norm_num at weight
  omega

end Erdos848Pure

/- Uniform bounds on nonsquarefree products along either residue class. -/
namespace Erdos848Pure
open Finset Erdos848Port

private theorem prime_sum (N b : ℕ) (P : Finset ℕ) (no5 : P ⊆ no5PrimesUpTo N)
    (no2 : 2 ∣ b → P ⊆ offPrimesUpTo N) :
    (∑ p ∈ P, (1:ℝ)/(25*(p:ℝ)^2)) ≤ (if 2 ∣ b then 163 else 413)/25000 := by
  have h : (∑ p ∈ P,(1:ℚ)/(p:ℚ)^2) ≤ (if 2 ∣ b then 163 else 413)/1000 := by
    by_cases h : 2 ∣ b
    · rw [if_pos h]
      exact (Finset.sum_le_sum_of_subset_of_nonneg (no2 h) (fun i _ _ => by positivity)).trans
        (sum_offPrimesUpTo_le N)
    · rw [if_neg h]
      exact (Finset.sum_le_sum_of_subset_of_nonneg no5 (fun i _ _ => by positivity)).trans
        (sum_no5PrimesUpTo_le N)
  have cast := (Rat.cast_le (K:=ℝ)).mpr h
  simp only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast,
    apply_ite Rat.cast,Rat.cast_ofNat] at cast
  have f (p : ℕ) : (1:ℝ)/(25*(p:ℝ)^2) = (1/25) * (1/(p:ℝ)^2) := by ring
  simp only [f,←Finset.mul_sum]
  by_cases z : 2 ∣ b <;> simp [z] at cast ⊢ <;> linarith only [cast]

private theorem weighted_bound {N b r C lo hi : ℕ} (largeN : 100 ≤ N) (bn : b < N)
    (S : Finset ℕ) (inRange : S ⊆ range N) (res : ∀ n ∈ S, n ≡ r [MOD 25])
    (bad : ∀ n ∈ S, ¬ Squarefree (b*n+1)) (h25 : ∀ n ∈ S, ¬25 ∣ b*n+1)
    (small : ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → (∀ p ∈ Q,C*p≤N) → lo*Q.card≤N)
    (large : ∀ T : Finset ℕ, (∀ n∈T,n<N ∧ ∃ p : ℕ,p≤N ∧ N<C*p ∧ p^2∣b*n+1) → hi*T.card≤N)
    (lop : 0<lo) (hip : 0<hi) (w : ℝ)
    (limit : ∀ Q : Finset ℕ, Q ⊆ no5PrimesUpTo N → (2∣b → Q ⊆ offPrimesUpTo N) →
      (3∣b → 3∉Q) → ∑ p∈Q,(1:ℝ)/(25*(p:ℝ)^2) ≤ w) :
    (S.card:ℝ) ≤ N*w + (N:ℝ)/lo + (N:ℝ)/hi := by
  classical
  let P := (no5PrimesUpTo N).filter (fun p => ¬p∣b)
  let Q := P.filter (fun p => C*p≤N)
  let R := P.filter (fun p => N<C*p)
  let B (p : ℕ) := (range N).filter (fun n => n ≡ r [MOD 25] ∧ p^2∣b*n+1)
  have no5 : P ⊆ no5PrimesUpTo N := Finset.filter_subset .. 
  have no2 (ev : 2 ∣ b) : P ⊆ offPrimesUpTo N := by
    intro p hp
    obtain ⟨mem,div⟩ := Finset.mem_filter.mp hp
    obtain ⟨pm,p5⟩ := Finset.mem_filter.mp mem
    exact Finset.mem_filter.mpr ⟨pm,fun h => div (h ▸ ev),p5⟩
  have prime {p : ℕ} (h : p ∈ P) : p.Prime :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (no5 h)).1).2
  have bound {p : ℕ} (h : p ∈ P) : p ≤ N :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (no5 h)).1).1)
  have cover : S ⊆ Q.biUnion B ∪ R.biUnion B := by
    intro n hn
    obtain ⟨p,hp,p5,pdv⟩ := prime_square_exists_ne5 (bad n hn) (h25 n hn)
    have nN := Finset.mem_range.mp (inRange hn)
    have pred := Nat.mul_le_mul (Nat.le_pred_of_lt bn) (Nat.le_pred_of_lt nN)
    have le := prime_le_of_sq_dvd_lt_sq (Nat.succ_pos _) ((Nat.add_le_add_right pred 1).trans_lt
      (sq_pred_add_one_lt_sq N largeN)) pdv
    have pnd : ¬p∣b := by
      intro h
      exact hp.not_dvd_one ((Nat.dvd_add_right (dvd_mul_of_dvd_left h n)).mp
        (Nat.dvd_of_pow_dvd (by decide : 1 ≤ 2) pdv))
    have mem : p ∈ P := by
      simp [P,no5PrimesUpTo,primesUpTo,hp,Nat.lt_succ_of_le le,p5,pnd]
    have nb : n ∈ B p := Finset.mem_filter.mpr ⟨inRange hn,res n hn,pdv⟩
    by_cases h : C*p ≤ N
    · exact mem_union_left _ (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,h⟩,nb⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,Nat.lt_of_not_ge h⟩,nb⟩)
  have cards : S.card ≤ (Q.biUnion B).card + (R.biUnion B).card :=
    (card_le_card cover).trans (card_union_le ..)
  have sub : Q ⊆ P := Finset.filter_subset ..
  have lc := small Q (fun _ h => prime (sub h)) (fun _ h => (mem_filter.mp h).2)
  have hc := large (R.biUnion B) (by
    intro n hn
    obtain ⟨p,hp,nb⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨nN,pdv⟩ := Finset.mem_filter.mp nb
    exact ⟨Finset.mem_range.mp nN,p,bound (mem_filter.mp hp).1,(mem_filter.mp hp).2,pdv.2⟩)
  have first := sieve_set_card_bound N 25 Q (Q.biUnion B) (fun p n => n ≡ r [MOD 25] ∧ p^2∣b*n+1)
    Subset.rfl (fun p hp => off_count_modEq25_le' N p b r (prime (sub hp)) (mem_filter.mp (no5 (sub hp))).2)
  have est := limit Q (sub.trans no5) (fun he => sub.trans (no2 he)) (fun dv h => (mem_filter.mp (sub h)).2 dv)
  have weight := mul_le_mul_of_nonneg_left est (show 0 ≤ (N:ℝ) by positivity)
  have countR : (S.card:ℝ) ≤ ((Q.biUnion B).card:ℝ) + ((R.biUnion B).card:ℝ) := by exact_mod_cast cards
  have lcr : (Q.card:ℝ) ≤ (N:ℝ)/lo := by
    apply (le_div_iff₀ (by exact_mod_cast lop)).mpr
    rw [mul_comm]
    exact_mod_cast lc
  have hcr : ((R.biUnion B).card:ℝ) ≤ (N:ℝ)/hi := by
    apply (le_div_iff₀ (by exact_mod_cast hip)).mpr
    rw [mul_comm]
    exact_mod_cast hc
  linarith only [first,weight,countR,lcr,hcr]

private theorem uniform_bound {N b r C lo hi : ℕ} (largeN : 100 ≤ N) (bn : b < N)
    (S : Finset ℕ) (inRange : S ⊆ range N) (res : ∀ n ∈ S, n ≡ r [MOD 25])
    (bad : ∀ n ∈ S, ¬ Squarefree (b*n+1)) (h25 : ∀ n ∈ S, ¬25 ∣ b*n+1)
    (small : ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → (∀ p ∈ Q,C*p≤N) → lo*Q.card≤N)
    (large : ∀ T : Finset ℕ, (∀ n∈T,n<N ∧ ∃ p : ℕ,p≤N ∧ N<C*p ∧ p^2∣b*n+1) → hi*T.card≤N)
    (lop : 0<lo) (hip : 0<hi) :
    (S.card:ℝ) ≤ N*((if 2 ∣ b then 163 else 413)/25000:ℝ) + (N:ℝ)/lo + (N:ℝ)/hi :=
  weighted_bound largeN bn S inRange res bad h25 small large lop hip _
    (fun Q no5 no2 _ => prime_sum N b Q no5 no2)

theorem bad_bound_400M {N b r : ℕ} (big : 400000000 ≤ N) (bn : b < N)
    (S : Finset ℕ) (inRange : S ⊆ range N) (res : ∀ n ∈ S, n ≡ r [MOD 25])
    (bad : ∀ n ∈ S, ¬ Squarefree (b*n+1)) (h25 : ∀ n ∈ S, ¬25 ∣ b*n+1) :
    (S.card:ℝ) ≤ (N:ℝ)*((if 2 ∣ b then 163 else 413)/25000:ℝ) + (N:ℝ)/120 := by
  have h := uniform_bound (by omega : 100≤N) bn S inRange res bad h25
    (small_primes_24 big) (large_mixed_24 big bn) (by decide) (by decide)
  norm_num at h
  linarith only [h,Nat.cast_nonneg (α:=ℝ) N]

theorem bad_bound_250B {N b r : ℕ} (big : 250000000000 ≤ N) (bn : b < N)
    (S : Finset ℕ) (inRange : S ⊆ range N) (res : ∀ n ∈ S, n ≡ r [MOD 25])
    (bad : ∀ n ∈ S, ¬ Squarefree (b*n+1)) (h25 : ∀ n ∈ S, ¬25 ∣ b*n+1) :
    (S.card:ℝ) ≤ (N:ℝ)*((if 2 ∣ b then 163 else 413)/25000:ℝ) + (N:ℝ)/800 := by
  have h := uniform_bound (by omega : 100≤N) bn S inRange res bad h25
    (small_primes_112 big) (large_mixed_112 big bn) (by decide) (by decide)
  norm_num at h
  linarith only [h,Nat.cast_nonneg (α:=ℝ) N]

theorem bad_bound_250B_sharp {N b r : ℕ} (big : 250000000000 ≤ N) (bn : b < N)
    (S : Finset ℕ) (inRange : S ⊆ range N) (res : ∀ n ∈ S, n ≡ r [MOD 25])
    (bad : ∀ n ∈ S, ¬ Squarefree (b*n+1)) (h25 : ∀ n ∈ S, ¬25 ∣ b*n+1) :
    (S.card:ℝ) ≤ (N:ℝ)*((if 2 ∣ b then 163 else 413)/25000:ℝ) + (N:ℝ)/816 := by
  have h := uniform_bound (by omega : 100≤N) bn S inRange res bad h25
    (small_primes_112 big) (large_mixed_112 big bn) (by decide) (by decide)
  norm_num at h
  linarith only [h,Nat.cast_nonneg (α:=ℝ) N]


theorem bad_bound_six {N b r : ℕ} (big : 250000000000 ≤ N) (bn : b < N) (six : 6∣b)
    (S : Finset ℕ) (inRange : S ⊆ range N) (res : ∀ n∈S, n ≡ r [MOD 25])
    (bad : ∀ n∈S, ¬ Squarefree (b*n+1)) (h25 : ∀ n∈S, ¬25 ∣ b*n+1) :
    (S.card:ℝ) ≤ (N:ℝ)/250 := by
  have even : 2∣b := (by decide : 2∣6).trans six
  have tri : 3∣b := (by decide : 3∣6).trans six
  have bound := weighted_bound (by omega : 100≤N) bn S inRange res bad h25
    (small_primes_112 big) (large_mixed_112 big bn) (by decide) (by decide)
    (163/25000-1/225) (by
      intro Q no5 no2 no3
      have h3 : 3∈primesUpTo N := by
        simp [primesUpTo,Nat.prime_three,show 3<N+1 by omega]
      have in5 : insert 3 Q ⊆ no5PrimesUpTo N := Finset.insert_subset (by
        exact mem_filter.mpr ⟨h3,by decide⟩) no5
      have in2 : insert 3 Q ⊆ offPrimesUpTo N := Finset.insert_subset (by
        exact mem_filter.mpr ⟨h3,by decide⟩) (no2 even)
      have e := prime_sum N b (insert 3 Q) in5 (fun _ => in2)
      rw [if_pos even,sum_insert (no3 tri)] at e
      norm_num only [Nat.cast_ofNat] at e
      linarith only [e])
  norm_num at bound
  linarith only [bound,Nat.cast_nonneg (α:=ℝ) N]

end Erdos848Pure

/- Hall's inequality between the two exceptional classes, for endpoints above
400 million. A potential empty rectangle with an even vertex can use the
stronger sieve omitting the square of two. Two odd-only sets together contain
at most one vertex per quotient by 25. -/

namespace Erdos848Pure
open Finset Erdos848Port

private theorem odd_rectangle (k : ℕ) (X Y : Finset ℕ)
    (xs : ∀ n ∈ X, n < 25*k+7 ∧ n%25=18 ∧ ¬2∣n)
    (ys : ∀ n ∈ Y, n < 25*k+7 ∧ n%25=7 ∧ ¬2∣n) :
    X.card+Y.card ≤ k := by
  classical
  have info (x : ℕ) (hx : x ∈ X ∪ Y) : x < 25*k+7 ∧ (x%25=18 ∨ x%25=7) ∧ ¬2∣x := by
    rcases Finset.mem_union.mp hx with h|h
    · obtain ⟨lo,r,o⟩ := xs x h
      exact ⟨lo,Or.inl r,o⟩
    · obtain ⟨lo,r,o⟩ := ys x h
      exact ⟨lo,Or.inr r,o⟩
  have dis : Disjoint X Y := Finset.disjoint_left.mpr (by
    intro x xX xY
    have := (xs x xX).2.1
    have := (ys x xY).2.1
    omega)
  have inj : (X∪Y).card ≤ (range k).card := Finset.card_le_card_of_injOn (fun x => x/25)
    (by intro x h; obtain ⟨lo,r,_⟩ := info x h; apply Finset.mem_range.mpr; change x/25 < k; rcases r with h|h <;> omega)
    (by
      intro x hx y hy eq
      obtain ⟨_,rx,ox⟩ := info x hx
      obtain ⟨_,ry,oy⟩ := info y hy
      change x/25 = y/25 at eq
      rcases rx with h|h <;> rcases ry with h|h <;> omega)
  simpa [card_union_of_disjoint dis] using inj

theorem hall_400M (k : ℕ) (big : 400000000 ≤ 25*k+7) (X : Finset ℕ)
    (xs : X ⊆ (range (25*k+7)).filter (fun n => n%25=18)) :
    X.card ≤ ((Erdos848.A₇ (25*k+7)).filter (fun a => ∃ b∈X, Squarefree (a*b+1))).card := by
  classical
  let N := 25*k+7
  let Γ := (Erdos848.A₇ N).filter (fun a => ∃ b∈X, Squarefree (a*b+1))
  let Y := Erdos848.A₇ N \ Γ
  have xin (x : ℕ) (h : x∈X) : x<N ∧ x%25=18 := by
    have e := Finset.mem_filter.mp (xs h)
    exact ⟨Finset.mem_range.mp e.1,e.2⟩
  have yin (y : ℕ) (h : y∈Y) : y<N ∧ y%25=7 := by
    have e := Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1
    exact ⟨Finset.mem_range.mp e.1,e.2⟩
  have conflict {x y : ℕ} (xh : x∈X) (yh : y∈Y) : ¬Squarefree (y*x+1) := by
    intro sq
    exact (Finset.mem_sdiff.mp yh).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp yh).1,x,xh,sq⟩)
  have base : (Erdos848.A₇ N).card = k := by change (Erdos848Port.A₇ N).card = k; rw [A₇_card]; dsimp [N]; omega
  have parts : Y.card + Γ.card = k := by
    rw [←base]
    exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset ..)
  change X.card ≤ Γ.card
  by_cases xe : X.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp xe]
    simp
  by_cases ye : Y.Nonempty
  swap
  · have empty := Finset.not_nonempty_iff_eq_empty.mp ye
    rw [empty,card_empty,zero_add] at parts
    rw [parts]
    have bound : X.card ≤ (A₁₈ N).card := Finset.card_le_card xs
    rw [A₁₈_card] at bound
    dsimp [N] at bound
    omega
  have fromX (x : ℕ) (xh : x∈X) : (Y.card:ℝ) ≤
      (N:ℝ)*((if 2∣x then 163 else 413)/25000:ℝ)+(N:ℝ)/120 := by
    apply bad_bound_400M big (xin x xh).1 Y (r:=7)
      (fun y h => Finset.mem_range.mpr (yin y h).1) (fun y h => (yin y h).2)
    · intro y yh
      simpa [Nat.mul_comm x y] using conflict xh yh
    · intro y yh
      exact cross_residue_18_7_not_div_25 x y (xin x xh).2 (yin y yh).2
  have fromY (y : ℕ) (yh : y∈Y) : (X.card:ℝ) ≤
      (N:ℝ)*((if 2∣y then 163 else 413)/25000:ℝ)+(N:ℝ)/120 := by
    apply bad_bound_400M big (yin y yh).1 X (r:=18)
      (fun x h => Finset.mem_range.mpr (xin x h).1) (fun x h => (xin x h).2)
    · intro x xh
      exact conflict xh yh
    · intro x xh
      exact cross_residue_7_18_not_div_25 y x (yin y yh).2 (xin x xh).2
  have count (x y : ℕ) (xh : x∈X) (yh : y∈Y) (even : 2∣x ∨ 2∣y) : X.card+Y.card ≤ k := by
    have a := fromX x xh
    have b := fromY y yh
    have kbig : (100:ℝ) ≤ k := by exact_mod_cast (show 100 ≤ k by omega)
    dsimp [N] at a b
    push_cast at a b
    exact_mod_cast (show (X.card:ℝ)+(Y.card:ℝ) ≤ k by
      by_cases xE : 2∣x <;> by_cases yE : 2∣y <;> simp [xE,yE] at a b even <;> linarith)
  by_cases ex : ∃ x∈X, 2∣x
  · obtain ⟨x,hx,h⟩ := ex
    obtain ⟨y,hy⟩ := ye
    have := count x y hx hy (Or.inl h)
    omega
  by_cases ey : ∃ y∈Y, 2∣y
  · obtain ⟨y,hy,h⟩ := ey
    obtain ⟨x,hx⟩ := xe
    have := count x y hx hy (Or.inr h)
    omega
  have bound := odd_rectangle k X Y (fun x h => ⟨(xin x h).1,(xin x h).2,fun e => ex ⟨x,h,e⟩⟩)
    (fun y h => ⟨(yin y h).1,(yin y h).2,fun e => ey ⟨y,h,e⟩⟩)
  omega

end Erdos848Pure

namespace Erdos848Pure
open Finset

theorem support_medium (b : ℕ) (bp : 0<b) (size : b≤400000000) (no5 : ¬5∣b) :
    2*2^b.primeFactors.card ≤ 512 := by
  classical
  let s : Finset ℕ := {2,3,7,11,13,17,19,23}
  let weight (p : ℕ) : ℚ := if p∈s then 28 / (p:ℚ) else 1
  have nums (p : ℕ) (hp : p∈s) : p=2 ∨ p=3 ∨ p=7 ∨ p=11 ∨ p=13 ∨ p=17 ∨ p=19 ∨ p=23 := by simpa [s] using hp
  have ge (p : ℕ) : 1≤weight p := by
    by_cases hp : p∈s
    · rcases nums p hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [weight,s]
    · simp [weight,hp]
  have per (p : ℕ) (hp : p∈b.primeFactors) : (28:ℚ) ≤ weight p * p^(b.factorization p) := by
    have p5 : p ≠ 5 := fun e => no5 (e ▸ Nat.dvd_of_mem_primeFactors hp)
    have prime := Nat.prime_of_mem_primeFactors hp
    have nz : p∈b.factorization.support := by simpa only [Nat.support_factorization] using hp
    have expo : 0<b.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp nz)
    have qpos : (1:ℚ) ≤ p := by exact_mod_cast prime.one_le
    have factor : (p:ℚ) ≤ p^(b.factorization p) := by
      simpa using pow_le_pow_right₀ qpos (show 1≤b.factorization p from expo)
    by_cases h : p∈s
    · simp only [weight,if_pos h]
      exact (div_mul_cancel₀ 28 (show (p:ℚ)≠0 by positivity)).symm.le.trans
        (mul_le_mul_of_nonneg_left factor (by positivity))
    · have bound : 28≤p := by
        by_contra! small
        interval_cases p <;> norm_num [s] at *
      simp only [weight,if_neg h,one_mul]
      exact (show (28:ℚ)≤p by exact_mod_cast bound).trans factor
  have wTotal : ∏ p∈b.primeFactors,weight p ≤ 8500 := by
    rw [← Finset.prod_subset (s₁:=b.primeFactors ∩ s) (s₂:=b.primeFactors) (f:=weight) Finset.inter_subset_left (by
      intro p hp hn
      exact if_neg (fun h => hn (Finset.mem_inter.mpr ⟨hp,h⟩)))]
    calc _ ≤ ∏ p∈s,weight p := Finset.prod_le_prod_of_subset_of_one_le Finset.inter_subset_right
          (fun p _ => (by linarith [ge p] : 0≤weight p)) (fun p _ _ => ge p)
         _ ≤ 8500 := by norm_num [weight,s,Finset.prod_insert]
  have prod : (∏ p∈b.primeFactors,(p:ℚ)^(b.factorization p))=b := by
    exact_mod_cast Nat.prod_factorization_pow_eq_self bp.ne'
  have comparison : (28:ℚ)^b.primeFactors.card ≤ 8500*b := by
    calc _ = ∏ _∈b.primeFactors,(28:ℚ) := by simp
         _ ≤ ∏ p∈b.primeFactors,weight p*p^(b.factorization p) :=
           Finset.prod_le_prod (fun _ _ => by norm_num) per
         _ ≤ _ := by rw [Finset.prod_mul_distrib,prod]; gcongr
  have n : 28^b.primeFactors.card ≤ 8500*b := by exact_mod_cast comparison
  have cnt : b.primeFactors.card ≤ 8 := by
    by_contra! large
    have pows := Nat.pow_le_pow_right (by decide : 0<28) (show 9≤b.primeFactors.card by omega)
    norm_num at pows
    omega
  have pows := Nat.pow_le_pow_right (by decide : 0<2) cnt
  norm_num at pows
  omega
private theorem count_by_theta_refined (N M e : ℕ) (Mpos : 0 < M)
    (hlogM : Real.log (M : ℝ) = e * Real.log 2)
    : e*N.primeCounting ≤ e*M.primeCounting+2*N := by
  let small := N.primesLE.filter (fun q => q ≤ M)
  let large := N.primesLE.filter (fun q => ¬ q ≤ M)
  have partition : small.card + large.card = N.primeCounting := by
    simpa only [small, large, Nat.primesLE_card_eq_primeCounting] using
      (Finset.card_filter_add_card_filter_not (s := N.primesLE) (fun q => q ≤ M))
  have sub : small ⊆ M.primesLE := by
    intro q hq
    obtain ⟨hp,hle⟩ := Finset.mem_filter.mp hq
    exact Nat.mem_primesLE.mpr ⟨hle,(Nat.mem_primesLE.mp hp).2⟩
  have hsmall := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at hsmall
  have filterSub : large ⊆ N.primesLE := Finset.filter_subset _ _
  have lower : (large.card : ℝ) * Real.log M ≤ Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    calc
      (large.card : ℝ) * Real.log M = ∑ _q ∈ large, Real.log M := by simp
      _ ≤ ∑ q ∈ large, Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        apply Real.log_le_log (by exact_mod_cast Mpos)
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hq).2))
      _ ≤ ∑ q ∈ N.primesLE, Real.log q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg filterSub
        intro q hq _
        exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hq).2.one_lt.le)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hupper := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by positivity)
  rw [hlogM] at lower
  rw [hlog4] at hupper
  have hlarge : e * (large.card : ℝ) ≤ 2 * (N : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    linarith only [lower, hupper]
  have count : (small.card : ℝ) + (large.card : ℝ) = N.primeCounting := by exact_mod_cast partition
  have sm : (small.card : ℝ) ≤ M.primeCounting := by exact_mod_cast hsmall
  exact_mod_cast (show e*(N.primeCounting : ℝ) ≤ e*(M.primeCounting : ℝ)+2*(N : ℝ) by
    nlinarith only [count, hlarge, mul_le_mul_of_nonneg_left sm (show (0:ℝ) ≤ (e:ℝ) by positivity)])


private theorem medium_log_nat_two_pow (n : ℕ) : Real.log ((2^n : ℕ) : ℝ) = n*Real.log 2 := by
  rw [Nat.cast_pow,Real.log_pow]
  norm_num


set_option maxRecDepth 1500 in
theorem prime_count_medium {N : ℕ} (Q : Finset ℕ) (pr : ∀p∈Q,p.Prime)
    (cut : ∀p∈Q,24*p≤N) : 408*Q.card ≤ 2*N + 408*25880 := by
  let X := N/24
  have sub : Q ⊆ X.primesLE := fun p hp => Nat.mem_primesLE.mpr
    ⟨by dsimp [X]; have := cut p hp; omega,pr p hp⟩
  have bound := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at bound
  have top := count_by_theta_refined X (2^17) 17 (by decide) (medium_log_nat_two_pow 17)
  have med := count_by_theta_refined (2^17) (2^11) 11 (by decide) (medium_log_nat_two_pow 11)
  have sub' : (2^11).primesLE ⊆ Finset.Icc 1 (2^11) := fun i hi =>
    Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hi).2.pos,(Nat.mem_primesLE.mp hi).1⟩
  have mid := Finset.card_le_card sub'
  rw [Nat.primesLE_card_eq_primeCounting] at mid
  norm_num only [Nat.card_Icc] at mid
  simp only [show (2^17:ℕ) = 131072 by decide,show (2^11:ℕ) = 2048 by decide] at top med mid
  have hX : 24*X≤N := by dsimp [X]; omega
  omega
end Erdos848Pure

namespace Erdos848Pure
open Finset

private theorem root_tag (d p q : ℕ)
    (hp : (d*p^2)%25=2) (hq : (d*q^2)%25=2) (tag : (p%25≤12) = (q%25≤12)) :
    p ≡ q [MOD 25] := by
  have check : ∀ a x y : Fin 25, (a.val*x.val^2)%25=2 → (a.val*y.val^2)%25=2 →
      (x.val≤12) = (y.val≤12) → x=y := by decide +kernel
  let a : Fin 25 := ⟨d%25,Nat.mod_lt _ (by decide)⟩
  let x : Fin 25 := ⟨p%25,Nat.mod_lt _ (by decide)⟩
  let y : Fin 25 := ⟨q%25,Nat.mod_lt _ (by decide)⟩
  have r (z : ℕ) : ((d%25)*(z%25)^2)%25 = (d*z^2)%25 := by
    rw [Nat.mul_mod d, Nat.pow_mod z]
    simp [Nat.mul_mod]
  exact congrArg Fin.val (check a x y ((r p).trans hp) ((r q).trans hq) tag)

private theorem fibre_spacing {b N d x y p q : ℕ} (bp : 0<b) (dp : 0<d)
    (hx : x<N) (hy : y<N) (ex : d*p^2=b*x+1) (ey : d*q^2=b*y+1)
    (big : N<24*p) (lt : p<q) (hm : 2*p ≡ 2*q [MOD 25*b]) : False := by
  have gap := hm.add_le_of_lt (by omega : 2*p<2*q)
  let t := q-p
  have expand : q=p+t := by dsimp [t]; omega
  have g : 25*b≤2*t := by omega
  have m := Nat.mul_le_mul_right p g
  have n := Nat.mul_lt_mul_of_pos_right big bp
  have bt : b*N < 2*p*t := by nlinarith only [m,n,Nat.zero_le (b*p)]
  have e : b*y = b*x+d*(2*p*t+t^2) := by rw [expand] at ey; nlinarith only [ex,ey]
  have scale := Nat.mul_le_mul_right (2*p*t+t^2) dp
  have blt := Nat.mul_lt_mul_of_pos_left hy bp
  nlinarith only [scale,e,bt,blt,Nat.zero_le (b*x),Nat.zero_le (t^2)]

theorem count_root_fibres {N b : ℕ} (bp : 0 < b) (cop : Nat.Coprime 25 b)
    (S D : Finset ℕ) (p d : ℕ → ℕ)
    (domain : ∀ n∈S,n<N) (eq : ∀ n∈S,d n*(p n)^2=b*n+1)
    (cong : ∀ n∈S,(b*n+1)%25=2) (big : ∀ n∈S,N<24*p n)
    (allowed : ∀ n∈S,d n∈D) :
    S.card ≤ 2*D.card*((b.divisors.filter (fun j => Nat.gcd j (b/j) ∣ 2)).card) := by
  classical
  let anchor (j : ℕ) := if h : ∃ n∈S,d n=j then h.choose else 0
  have spec (n : ℕ) (h : n∈S) : anchor (d n)∈S ∧ d (anchor (d n))=d n := by
    have w : ∃ t∈S,d t=d n := ⟨n,h,rfl⟩
    simpa only [anchor,dif_pos w] using w.choose_spec
  let r (j : ℕ) := p (anchor j)
  let g (n : ℕ) := Int.gcd (b:ℤ) ((p n:ℤ)-(r (d n):ℤ))
  let key (n : ℕ) := (d n, g n, decide ((p n)%25≤12))
  let keys := b.divisors.filter (fun j => Nat.gcd j (b/j) ∣ 2)
  have ez (n : ℕ) (h : n∈S) : (d n:ℤ)*(p n:ℤ)^2=(b:ℤ)*(n:ℤ)+1 := by exact_mod_cast eq n h
  have estimate : S.card ≤ (D.product (keys.product (univ : Finset Bool))).card := by
    apply Finset.card_le_card_of_injOn key
    · intro n hn
      have div : g n∣b := by
        have dg : (g n:ℤ) ∣ (b:ℤ) := Int.gcd_dvd_left .. 
        exact_mod_cast dg
      have ea := ez _ (spec n hn).1
      rw [(spec n hn).2] at ea
      exact mem_product.mpr ⟨allowed n hn,mem_product.mpr
        ⟨mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨div,bp.ne'⟩,Erdos848RootRefined.root_key_valid bp ea (ez n hn)⟩,mem_univ _⟩⟩
    · intro x hx y hy h
      have hd : d x=d y := congrArg Prod.fst h
      have hk : g x=g y := congrArg (fun u=>u.2.1) h
      have ht : decide ((p x)%25≤12)=decide ((p y)%25≤12) := congrArg (fun u=>u.2.2) h
      have tag : ((p x)%25≤12) = ((p y)%25≤12) := propext (by simpa using ht)
      have ex := eq x hx
      have ey := eq y hy
      rw [←hd] at ey
      have h25 := root_tag (d x) (p x) (p y) (ex ▸ cong x hx) (ey ▸ cong y hy) tag
      have ea := ez _ (spec x hx).1
      rw [(spec x hx).2] at ea
      have ezy := ez y hy
      rw [←hd] at ezy
      change Int.gcd _ ((p x:ℤ)-(r (d x):ℤ))=Int.gcd _ ((p y:ℤ)-(r (d y):ℤ)) at hk
      rw [←hd] at hk
      have s := Erdos848RootRefined.roots_in_class ea (ez x hx) ezy hk
      have hm : 2*p x ≡ 2*p y [MOD b] := by
        apply Int.natCast_modEq_iff.mp
        rw [Int.modEq_iff_dvd]
        convert! s using 1
        push_cast
        ring
      have both := (Nat.modEq_and_modEq_iff_modEq_mul cop).mp ⟨h25.mul_left 2,hm⟩
      have dp : 0<d x := by by_contra! h; rw [show d x=0 by omega,zero_mul] at ex; omega
      rcases lt_trichotomy (p x) (p y) with lt|same|gt
      · exact (fibre_spacing bp dp (domain x hx) (domain y hy) ex ey (big x hx) lt both).elim
      · rw [same,ey] at ex
        exact Nat.eq_of_mul_eq_mul_left bp (by omega)
      · exact (fibre_spacing bp dp (domain y hy) (domain x hx) ey ex (big y hy) gt both.symm).elim
  simpa [keys,Finset.card_product,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using estimate

end Erdos848Pure

namespace Erdos848Pure
open Finset
def smallPrimes : Finset ℕ := {2,3,7,11,13,17,19,23}
private def qrBits : ℕ → ℕ
  | 2 => 2
  | 3 => 2
  | 7 => 22
  | 11 => 570
  | 13 => 5658
  | 17 => 107286
  | 19 => 199410
  | 23 => 340830
  | _ => 0

private def qr (q d : ℕ) : Bool := (qrBits q).testBit (d%q)
def admissibleDivs (s : Finset ℕ) := (Finset.range 577).filter (fun d =>
  (d%5=2 ∨ d%5=3) ∧ ∀ q∈s, qr q d=true)

private theorem qr_ok {q d p : ℕ} (hq : q∈smallPrimes) (h : (d*p^2)%q=1) :
    qr q d=true := by
  have qpos : 0<q := by
    have e : q=2 ∨ q=3 ∨ q=7 ∨ q=11 ∨ q=13 ∨ q=17 ∨ q=19 ∨ q=23 := by simpa [smallPrimes] using hq
    omega
  let a : Fin q := ⟨d%q,Nat.mod_lt _ qpos⟩
  let x : Fin q := ⟨p%q,Nat.mod_lt _ qpos⟩
  have test : ∀ q∈smallPrimes, ∀ a x : Fin q, (a.val*x.val^2)%q=1 → qr q a.val=true := by decide +kernel
  have xx : (a.val*x.val^2)%q=1 := by
    change ((d%q)*(p%q)^2)%q=1
    rw [←h]
    rw [Nat.mul_mod d, Nat.pow_mod p]
    simp [Nat.mul_mod]
  simpa [a,qr] using test q hq a x xx

theorem div_admissible {b n p d : ℕ} (h : d*p^2=b*n+1)
    (res : (b*n+1)%25=2) (bound : d≤576) : d∈admissibleDivs (b.primeFactors ∩ smallPrimes) := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),?_,?_⟩
  · have e : (d*p^2)%5=2 := by omega
    let a : Fin 5 := ⟨d%5,Nat.mod_lt _ (by decide)⟩
    let x : Fin 5 := ⟨p%5,Nat.mod_lt _ (by decide)⟩
    have finite : ∀ a x : Fin 5, (a.val*x.val^2)%5=2 → a.val=2 ∨ a.val=3 := by decide
    apply finite a x
    change ((d%5)*(p%5)^2)%5=2
    have z : ((d%5)*(p%5)^2)%5=(d*p^2)%5 := by
      rw [Nat.mul_mod d,Nat.pow_mod p]
      simp [Nat.mul_mod]
    exact z.trans e
  · intro q hq
    obtain ⟨qb,qs⟩ := mem_inter.mp hq
    apply qr_ok qs
    have prime := Nat.prime_of_mem_primeFactors qb
    have dv := dvd_mul_of_dvd_left (Nat.dvd_of_mem_primeFactors qb) n
    rw [h, Nat.add_mod, Nat.mod_eq_zero_of_dvd dv, zero_add, Nat.mod_eq_of_lt prime.one_lt, Nat.mod_eq_of_lt prime.one_lt]

private theorem product_support_bound {b : ℕ} (bp : 0<b) (no5 : ¬5∣b) :
    (∏ q ∈ b.primeFactors ∩ smallPrimes,q) *
        29^(b.primeFactors \ smallPrimes).card ≤ b := by
  let s := b.primeFactors ∩ smallPrimes
  let t := b.primeFactors \ smallPrimes
  have gt (q : ℕ) (hq : q∈t) : 29≤q := by
    obtain ⟨qb,small⟩ := mem_sdiff.mp hq
    have prime := Nat.prime_of_mem_primeFactors qb
    have five : q≠5 := fun e => no5 (e ▸ Nat.dvd_of_mem_primeFactors qb)
    by_contra! low
    interval_cases q <;> norm_num [smallPrimes] at *
  have cmp : 29^t.card ≤ ∏ q∈t,q := by
    rw [←Finset.prod_const]
    exact Finset.prod_le_prod' gt
  have cover : Disjoint s t := Finset.disjoint_left.mpr (by intro q h h'; exact (mem_sdiff.mp h').2 (mem_inter.mp h).2)
  have all : s∪t=b.primeFactors := by ext q; simp [s,t]; tauto
  have div : (∏ q∈b.primeFactors,q) ∣ b := Nat.prod_primeFactors_dvd b
  calc _ ≤ (∏ q∈s,q)*(∏ q∈t,q) := Nat.mul_le_mul_left _ cmp
       _ = _ := by rw [←Finset.prod_union cover,all]
       _ ≤ b := Nat.le_of_dvd bp div

private def listPrimes : List ℕ := [2,3,7,11,13,17,19,23]
private def initial : List ℕ := (List.range 577).filter fun d => decide (d%5=2 ∨ d%5=3)
private def walk : List ℕ → List ℕ → ℕ → Bool
  | [], good, c => if c≤3 then decide (2^c*good.length≤230) else decide (good.length≤14)
  | q::l, good, c => walk l good c && walk l (good.filter (qr q)) (c+1)

private theorem walk_sound (l good : List ℕ) (c : ℕ) (h : walk l good c=true)
    (s D : Finset ℕ) (sub : ∀ q∈s,q∈l) (domain : ∀ d∈D,d∈good)
    (local_qr : ∀ d∈D,∀ q∈s,qr q d=true) :
    if c+s.card≤3 then 2^(c+s.card)*D.card≤230 else D.card≤14 := by
  induction l generalizing s good c with
  | nil =>
    have se : s=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun q hq => by simpa using sub q hq)
    have count : D.card ≤ good.length := (Finset.card_le_card (t:=good.toFinset)
      (fun d hd => List.mem_toFinset.mpr (domain d hd))).trans (List.toFinset_card_le ..)
    simp only [se,card_empty,Nat.add_zero] at *
    by_cases b : c≤3
    · simp [walk,b] at h ⊢
      exact (Nat.mul_le_mul_left _ count).trans h
    · simp [walk,b] at h ⊢
      omega
  | cons q l ih =>
    simp only [walk,Bool.and_eq_true] at h
    by_cases active : q∈s
    · have sub' (r : ℕ) (hr : r∈s.erase q) : r∈l :=
        (List.mem_cons.mp (sub r (mem_of_mem_erase hr))).resolve_left (ne_of_mem_erase hr)
      have d' (d : ℕ) (hd : d∈D) : d∈good.filter (qr q) :=
        List.mem_filter.mpr ⟨domain d hd,local_qr d hd q active⟩
      have result := ih (good.filter (qr q)) (c+1) h.2 (s.erase q) sub' d'
        (fun d hd r hr => local_qr d hd r (mem_of_mem_erase hr))
      have eq : c+1+(s.erase q).card = c+s.card := by have := card_erase_add_one active; omega
      simpa only [eq] using result
    · exact ih good c h.1 s (fun r hr => (List.mem_cons.mp (sub r hr)).resolve_left (fun e => active (e ▸ hr)))
        domain local_qr

set_option maxRecDepth 1500 in
set_option maxHeartbeats 0 in
private theorem numeric : walk listPrimes initial 0=true := by decide +kernel

private theorem small_table : ∀ s∈smallPrimes.powerset,
    if s.card≤3 then 2^s.card*(admissibleDivs s).card≤230 else (admissibleDivs s).card≤14 := by
  intro s h
  have a : ∀ q∈s,q∈listPrimes := by
    intro q hq
    simpa [listPrimes,smallPrimes] using (mem_powerset.mp h hq)
  have d : ∀ n∈admissibleDivs s,n∈initial := by
    intro n hn
    obtain ⟨lo,allowed,rest⟩ := mem_filter.mp hn
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (mem_range.mp lo),decide_eq_true allowed⟩
  simpa only [Nat.zero_add] using
    walk_sound listPrimes initial 0 numeric s (admissibleDivs s) a d
      (fun n hn => (mem_filter.mp hn).2.2)

private theorem divisor_weight {b j : ℕ} (bp : 0<b) (no5 : ¬5∣b)
    (hi : b≤400000000) (powhi : b<29^(j+1)) (jlo : 4≤j) :
    4*2^b.primeFactors.card*(admissibleDivs (b.primeFactors ∩ smallPrimes)).card ≤ 4*2^j*230 := by
  let s := b.primeFactors ∩ smallPrimes
  let t := b.primeFactors \ smallPrimes
  have table := small_table s (mem_powerset.mpr inter_subset_right)
  have m := product_support_bound bp no5
  have pos : 0< ∏ q∈s,q := Finset.prod_pos (fun q h => (Nat.prime_of_mem_primeFactors (mem_inter.mp h).1).pos)
  have small : t.card ≤ j := by
    by_contra! h
    have e := Nat.pow_le_pow_right (by decide : 0<29) (show j+1≤t.card by omega)
    have z := Nat.mul_le_mul_right (29^t.card) pos
    change (∏ q∈s,q)*29^t.card ≤ b at m
    omega
  have size : t.card+s.card=b.primeFactors.card := card_sdiff_add_card_inter _ _
  change 4*2^b.primeFactors.card*(admissibleDivs s).card ≤ _
  by_cases few : s.card≤3
  · rw [if_pos few] at table
    rw [←size,pow_add]
    have mul := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0<2) small) table
    nlinarith only [mul]
  · rw [if_neg few] at table
    have sup := support_medium b bp (by omega) no5
    have g := Nat.mul_le_mul (show 4*2^b.primeFactors.card ≤ 1024 by omega) table
    have pj := Nat.pow_le_pow_right (by decide : 0<2) jlo
    norm_num at pj
    omega

theorem divisor_weight_low {b : ℕ} (bp : 0<b) (no5 : ¬5∣b) (hi : b≤12000000) :
    4*2^b.primeFactors.card*(admissibleDivs (b.primeFactors ∩ smallPrimes)).card ≤ 14720 :=
  divisor_weight (j:=4) bp no5 (by omega) (by norm_num; omega) (by decide)

theorem divisor_weight_mid {b : ℕ} (bp : 0<b) (no5 : ¬5∣b) (hi : b≤400000000) :
    4*2^b.primeFactors.card*(admissibleDivs (b.primeFactors ∩ smallPrimes)).card ≤ 29440 :=
  divisor_weight (j:=5) bp no5 hi (by norm_num; omega) (by decide)
end Erdos848Pure

namespace Erdos848Pure
open Finset Erdos848Gap
theorem large_crt {N b K : ℕ} (big : 3300000 ≤ N) (bN : b < N)
    (kk : 0<b → 4*2^b.primeFactors.card*(admissibleDivs (b.primeFactors ∩ smallPrimes)).card ≤ K) (no5 : ¬5∣b) (S : Finset ℕ) (mods : ∀ n∈S,(b*n+1)%25=2) (choosePrime : ∀n∈S, n < N ∧ ∃p : ℕ, p≤N ∧ N < 24*p ∧ p^2 ∣ b*n+1) :
    S.card ≤ K := by
  classical
  by_cases non : S.Nonempty
  · let p (n : ℕ) := if h : n ∈ S then ((choosePrime n h).2).choose else 1
    let d (n : ℕ) := (b*n+1)/(p n)^2
    have info (n : ℕ) (hn : n ∈ S) : p n ≤ N ∧ N < 24*p n ∧ (p n)^2 ∣ b*n+1 := by
      simpa only [p,dif_pos hn] using ((choosePrime n hn).2).choose_spec
    have eq (n : ℕ) (hn : n ∈ S) : d n*(p n)^2 = b*n+1 := Nat.div_mul_cancel (info n hn).2.2
    obtain ⟨v,hv⟩ := non
    have bp : 0 < b := by
      by_contra! h
      have bz : b=0 := by omega
      have hd := (info v hv).2.2
      simp only [bz,zero_mul,zero_add,Nat.dvd_one] at hd
      have hq := (info v hv).2.1
      have pq : 2 ≤ p v := by omega
      have sq := Nat.pow_le_pow_left pq 2
      omega
    have bound (n : ℕ) (hn : n∈S) : b*n+1 ≤ b*N := by
      have h := Nat.mul_le_mul_left b (show n+1 ≤ N from (choosePrime n hn).1)
      rw [Nat.mul_add,Nat.mul_one] at h
      omega
    have link (n : ℕ) (hn : n∈S) (c : ℕ) (lc : N<c*p n) : d n*N<c^2*b := by
      have positive : 0<d n := by
        by_contra! dz
        have e := eq n hn
        rw [show d n=0 by omega,zero_mul] at e
        omega
      have rr := Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left lc (by decide : 2≠0)) positive
      have bd := Nat.mul_le_mul_left (c^2) (bound n hn)
      have scaled := congrArg (c^2*·) (eq n hn)
      have cmp : (d n*N)*N < (c^2*b)*N := by nlinarith only [rr,bd,scaled]
      exact Nat.lt_of_mul_lt_mul_right cmp
    let D := admissibleDivs (b.primeFactors ∩ smallPrimes)
    have da (n : ℕ) (hn : n∈S) : d n∈D := by
      apply div_admissible (eq n hn) (mods n hn)
      have cmp := link n hn 24 (info n hn).2.1
      have l : d n*N < 576*N := cmp.trans_le (Nat.mul_le_mul_left 576 bN.le)
      exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_right l)
    have cop : Nat.Coprime 25 b := (Nat.prime_five.coprime_iff_not_dvd.mpr no5).pow_left 2
    have cnt := count_root_fibres bp cop S D p d (fun n h => (choosePrime n h).1) eq mods
      (fun n h => (info n h).2.1) da
    have key := Erdos848Unitary.count_unitary_keys b bp
    calc _ ≤ _ := cnt
         _ ≤ (2*D.card)*(2*2^b.primeFactors.card) := Nat.mul_le_mul_left _ key
         _ = 4*2^b.primeFactors.card*D.card := by ring
         _ ≤ K := kk bp
  · rw [Finset.not_nonempty_iff_eq_empty.mp non]; simp

end Erdos848Pure

namespace Erdos848Pure.PrimeBlocks
open Finset
private def values : List ℕ := [821, 811, 809, 797, 787, 773, 769, 761, 757, 751, 743, 739, 733, 727, 719, 709, 701, 691, 683, 677, 673, 661, 659, 653, 647, 643, 641, 631, 619, 617, 613, 607, 601, 599, 593, 587, 577, 571, 569, 563, 557, 547, 541, 523, 521, 509, 503, 499, 491, 487, 479, 467, 463, 461, 457, 449, 443, 439, 433, 431, 421, 419, 409, 401, 397, 389, 383, 379, 373, 367, 359, 353, 349, 347, 337, 331, 317, 313, 311, 307, 293, 283, 281, 277, 271, 269, 263, 257, 251, 241, 239, 233, 229, 227, 223, 211, 199, 197, 193, 191, 181, 179, 173, 167, 163, 157, 151, 149, 139, 137, 131, 127, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2]
private def primes : List ℕ := ((List.range 822).filter fun q => decide q.Prime).reverse
private theorem mem_primes (q : ℕ) : q∈primes ↔ q<822 ∧ q.Prime := by simp [primes]
private def candidates (l : List ℕ) (x : ℕ) :=
  (Icc 1 x).filter (fun n => ∀ p∈l, ¬p∣n)
private def phi : List ℕ → ℕ → ℕ
  | [], x => x
  | q::l, x =>
      if x≤q then min x 1 else phi l x - phi l (x/q)

private theorem prime_list {l : List ℕ} (pr : ∀ q∈l,q.Prime)
    (ord : l.Pairwise (·>·))
    (complete : ∀ q∈l, ∀ p≤q, p.Prime → p∈l) (x : ℕ) :
    phi l x = (candidates l x).card := by
  induction l generalizing x with
  | nil => simp [phi,candidates]
  | cons q l ih =>
    have pq := pr q (List.mem_cons_self ..)
    have tailpr (r : ℕ) (hr : r∈l) := pr r (List.mem_cons_of_mem q hr)
    have lt (r : ℕ) (hr : r∈l) : r<q := (List.pairwise_cons.mp ord).1 r hr
    have full (r : ℕ) (hr : r∈l) (p : ℕ) (hp : p≤r) (pp : p.Prime) : p∈l := by
      have h := complete r (List.mem_cons_of_mem q hr) p hp pp
      have z := lt r hr
      exact (List.mem_cons.mp h).resolve_left (by omega)
    have tail := ih tailpr (List.pairwise_cons.mp ord).2 full
    rw [phi]
    split
    · rename_i small
      have trivial : candidates (q::l) x = (Icc 1 (min x 1)) := by
        ext n
        simp only [candidates,mem_filter,mem_Icc]
        constructor
        · rintro ⟨⟨pos,le⟩,h⟩
          refine ⟨pos,le_min le ?_⟩
          by_contra! large
          obtain ⟨r,prime,dv⟩ := Nat.exists_prime_and_dvd (show n≠1 by omega)
          have rn := Nat.le_of_dvd pos dv
          exact h r (complete q (List.mem_cons_self ..) r (by omega) prime) dv
        · rintro ⟨pos,le⟩
          have low := le_min_iff.mp le
          have eq : n=1 := by omega
          exact ⟨⟨pos,low.1⟩,fun r hr dv => (pr r hr).not_dvd_one (eq ▸ dv)⟩
      rw [trivial,Nat.card_Icc]
      omega
    · rw [tail x,tail (x/q)]
      let A := candidates l x
      have rest : A.filter (fun n=>¬q∣n) = candidates (q::l) x := by
        ext n
        simp [A,candidates]
        tauto
      have divs : A.filter (fun n=>q∣n) = (candidates l (x/q)).image (q*·) := by
        ext n
        constructor
        · intro h
          obtain ⟨hh,⟨m,eq⟩⟩ := mem_filter.mp h
          obtain ⟨bounds,allow⟩ := mem_filter.mp hh
          obtain ⟨pos,le⟩ := mem_Icc.mp bounds
          subst n
          refine mem_image.mpr ⟨m,mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mul_pos_left pos,?_⟩,?_⟩,rfl⟩
          · exact (Nat.le_div_iff_mul_le pq.pos).mpr (by simpa [Nat.mul_comm] using le)
          · intro r hr dv
            exact allow r hr (dvd_mul_of_dvd_right dv _)
        · intro h
          obtain ⟨m,hm,rfl⟩ := mem_image.mp h
          obtain ⟨bounds,allow⟩ := mem_filter.mp hm
          obtain ⟨pos,le⟩ := mem_Icc.mp bounds
          refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos pq.pos pos,?_⟩,?_⟩, dvd_mul_right ..⟩
          · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le pq.pos).mp le
          · intro r hr dv
            rcases (tailpr r hr).dvd_mul.mp dv with a|a
            · have z := (pq.dvd_iff_eq (tailpr r hr).ne_one).mp a
              have := lt r hr
              omega
            · exact allow r hr a
      have inj : Function.Injective (q*·) := fun _ _ e => Nat.eq_of_mul_eq_mul_left pq.pos e
      have m := card_filter_add_card_filter_not (s:=A) (fun n=>q∣n)
      rw [rest,divs,card_image_of_injective _ inj] at m
      change A.card-(candidates l (x/q)).card = _
      omega

private theorem plist : ∀ q∈primes,q.Prime := fun q h => ((mem_primes q).mp h).2
private theorem sorted : primes.Pairwise (·>·) := List.pairwise_reverse.mpr
  (List.Pairwise.filter _ List.pairwise_lt_range)

private theorem cap (x : ℕ) (Q : Finset ℕ) (pr : ∀ q∈Q,q.Prime)
    (small : ∀ q∈Q,q≤x) : Q.card ≤ primes.length+phi primes x := by
  have all : ∀ q∈primes,∀ p≤q,p.Prime → p∈primes := by
    intro q h p le prime
    exact (mem_primes p).mpr ⟨le.trans_lt ((mem_primes q).mp h).1,prime⟩
  have sub : Q ⊆ primes.toFinset ∪ candidates primes x := by
    intro r hr
    by_cases mem : r∈primes
    · exact mem_union_left _ (List.mem_toFinset.mpr mem)
    · apply mem_union_right
      apply mem_filter.mpr
      refine ⟨mem_Icc.mpr ⟨(pr r hr).pos,small r hr⟩,?_⟩
      intro p hp dvd
      have eq := ((pr r hr).dvd_iff_eq (plist p hp).ne_one).mp dvd
      exact mem (eq.symm ▸ hp)
  have h := (card_le_card sub).trans (card_union_le ..)
  rw [←prime_list plist sorted all x] at h
  exact h.trans (Nat.add_le_add_right (List.toFinset_card_le ..) _)
set_option maxRecDepth 2500 in
private theorem literal : primes=values := by decide +kernel
set_option maxRecDepth 2000 in
set_option maxHeartbeats 0 in
private theorem numerical142 : primes.length+phi primes 141999=13185 := by rw [literal]; decide +kernel
theorem cap142000 (Q : Finset ℕ) (pr : ∀ q∈Q,q.Prime) (small : ∀q∈Q,q<142000) : Q.card≤13185 := by
  rw [← numerical142]
  exact cap _ Q pr (fun q h => by have := small q h; omega)
set_option maxRecDepth 2000 in
set_option maxHeartbeats 0 in
private theorem numerical151 : primes.length+phi primes 150999=13934 := by rw [literal]; decide +kernel
theorem cap151000 (Q : Finset ℕ) (pr : ∀ q∈Q,q.Prime) (small : ∀q∈Q,q<151000) : Q.card≤13934 := by
  rw [← numerical151]
  exact cap _ Q pr (fun q h => by have := small q h; omega)
set_option maxRecDepth 2000 in
set_option maxHeartbeats 0 in
private theorem numerical167 : primes.length+phi primes 166999=15255 := by rw [literal]; decide +kernel
theorem cap167000 (Q : Finset ℕ) (pr : ∀ q∈Q,q.Prime) (small : ∀q∈Q,q<167000) : Q.card≤15255 := by
  rw [← numerical167]
  exact cap _ Q pr (fun q h => by have := small q h; omega)
set_option maxRecDepth 2000 in
set_option maxHeartbeats 0 in
private theorem numerical209 : primes.length+phi primes 208999=18720 := by rw [literal]; decide +kernel
theorem cap209000 (Q : Finset ℕ) (pr : ∀ q∈Q,q.Prime) (small : ∀q∈Q,q<209000) : Q.card≤18720 := by
  rw [← numerical209]
  exact cap _ Q pr (fun q h => by have := small q h; omega)
set_option maxRecDepth 2000 in
set_option maxHeartbeats 0 in
private theorem numerical292 : primes.length+phi primes 291999=25386 := by rw [literal]; decide +kernel
theorem cap292000 (Q : Finset ℕ) (pr : ∀ q∈Q,q.Prime) (small : ∀q∈Q,q<292000) : Q.card≤25386 := by
  rw [← numerical292]
  exact cap _ Q pr (fun q h => by have := small q h; omega)
set_option maxRecDepth 2000 in
set_option maxHeartbeats 0 in
private theorem numerical501 : primes.length+phi primes 500999=41618 := by rw [literal]; decide +kernel
theorem cap501000 (Q : Finset ℕ) (pr : ∀ q∈Q,q.Prime) (small : ∀q∈Q,q<501000) : Q.card≤41618 := by
  rw [← numerical501]
  exact cap _ Q pr (fun q h => by have := small q h; omega)
set_option maxRecDepth 2000 in
set_option maxHeartbeats 0 in
private theorem numerical667 : primes.length+phi primes 666999=54096 := by rw [literal]; decide +kernel
theorem cap667000 (Q : Finset ℕ) (pr : ∀ q∈Q,q.Prime) (small : ∀q∈Q,q<667000) : Q.card≤54096 := by
  rw [← numerical667]
  exact cap _ Q pr (fun q h => by have := small q h; omega)
end Erdos848Pure.PrimeBlocks

namespace Erdos848Pure
open Finset Erdos848Port
private theorem crt_prime_sum (N b : ℕ) (P : Finset ℕ) (no5 : P ⊆ no5PrimesUpTo N)
    (no2 : 2 ∣ b → P ⊆ offPrimesUpTo N) :
    (∑ p ∈ P, (1:ℝ)/(25*(p:ℝ)^2)) ≤ (if 2 ∣ b then 163 else 413)/25000 := by
  have h : (∑ p ∈ P,(1:ℚ)/(p:ℚ)^2) ≤ (if 2 ∣ b then 163 else 413)/1000 := by
    by_cases h : 2 ∣ b
    · rw [if_pos h]
      exact (Finset.sum_le_sum_of_subset_of_nonneg (no2 h) (fun i _ _ => by positivity)).trans
        (sum_offPrimesUpTo_le N)
    · rw [if_neg h]
      exact (Finset.sum_le_sum_of_subset_of_nonneg no5 (fun i _ _ => by positivity)).trans
        (sum_no5PrimesUpTo_le N)
  have cast := (Rat.cast_le (K:=ℝ)).mpr h
  simp only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast,
    apply_ite Rat.cast,Rat.cast_ofNat] at cast
  have f (p : ℕ) : (1:ℝ)/(25*(p:ℝ)^2) = (1/25) * (1/(p:ℝ)^2) := by ring
  simp only [f,←Finset.mul_sum]
  by_cases z : 2 ∣ b <;> simp [z] at cast ⊢ <;> linarith only [cast]


theorem crt_bad {N b r : ℕ} (big : 3300000 ≤ N) (ceiling : N ≤ 400000000) (bn : b<N)
    (no5b : ¬5∣b) (prod : (b*r+1)%25=2)
    (S : Finset ℕ) (inRange : S ⊆ range N) (res : ∀ n∈S,n ≡ r [MOD 25])
    (bad : ∀ n∈S, ¬Squarefree (b*n+1)) (h25 : ∀ n∈S, ¬25∣b*n+1) :
    (S.card:ℝ) ≤ N*((if 2∣b then 163 else 413)/25000:ℝ) + (N:ℝ)*(212/25000)-1 := by
  classical
  let P := (no5PrimesUpTo N).filter (fun p => ¬p∣b)
  let Q := P.filter (fun p => 24*p≤N)
  let R := P.filter (fun p => N<24*p)
  let B (p : ℕ) := (range N).filter (fun n => n ≡ r [MOD 25] ∧ p^2∣b*n+1)
  have no5 : P ⊆ no5PrimesUpTo N := Finset.filter_subset .. 
  have no2 (ev : 2 ∣ b) : P ⊆ offPrimesUpTo N := by
    intro p hp
    obtain ⟨mem,div⟩ := Finset.mem_filter.mp hp
    obtain ⟨pm,p5⟩ := Finset.mem_filter.mp mem
    exact Finset.mem_filter.mpr ⟨pm,fun h => div (h ▸ ev),p5⟩
  have prime {p : ℕ} (h : p ∈ P) : p.Prime :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (no5 h)).1).2
  have bound {p : ℕ} (h : p ∈ P) : p ≤ N :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (no5 h)).1).1)
  have cover : S ⊆ Q.biUnion B ∪ R.biUnion B := by
    intro n hn
    obtain ⟨p,hp,p5,pdv⟩ := prime_square_exists_ne5 (bad n hn) (h25 n hn)
    have nN := Finset.mem_range.mp (inRange hn)
    have pred := Nat.mul_le_mul (Nat.le_pred_of_lt bn) (Nat.le_pred_of_lt nN)
    have le := prime_le_of_sq_dvd_lt_sq (Nat.succ_pos _) ((Nat.add_le_add_right pred 1).trans_lt
      (sq_pred_add_one_lt_sq N (by omega))) pdv
    have pnd : ¬p∣b := by
      intro h
      exact hp.not_dvd_one ((Nat.dvd_add_right (dvd_mul_of_dvd_left h n)).mp
        (Nat.dvd_of_pow_dvd (by decide : 1 ≤ 2) pdv))
    have mem : p ∈ P := by
      simp [P,no5PrimesUpTo,primesUpTo,hp,Nat.lt_succ_of_le le,p5,pnd]
    have nb : n ∈ B p := Finset.mem_filter.mpr ⟨inRange hn,res n hn,pdv⟩
    by_cases h : 24*p ≤ N
    · exact mem_union_left _ (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,h⟩,nb⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,Nat.lt_of_not_ge h⟩,nb⟩)
  have cards : S.card ≤ (Q.biUnion B).card + (R.biUnion B).card :=
    (card_le_card cover).trans (card_union_le ..)
  have sub : Q ⊆ P := Finset.filter_subset ..
  let K : ℕ := if N≤12000000 then 14720 else 29440
  have kk (bp : 0<b) : 4*2^b.primeFactors.card*(admissibleDivs (b.primeFactors ∩ smallPrimes)).card ≤ K := by
    dsimp [K]
    split
    · rename_i hi; exact divisor_weight_low bp no5b (by omega)
    · exact divisor_weight_mid bp no5b (by omega)
  have smallPr (q : ℕ) (hq : q∈Q) : q.Prime := prime (sub hq)
  have cutoff (q : ℕ) (hq : q∈Q) : 24*q≤N := (mem_filter.mp hq).2
  have lc := prime_count_medium Q (fun _ h => prime (sub h)) (fun _ h => (mem_filter.mp h).2)
  have hc := large_crt big bn kk no5b (R.biUnion B) (by
    intro n hn
    obtain ⟨p,_,mem⟩ := Finset.mem_biUnion.mp hn
    have rn : n ≡ r [MOD 25] := (Finset.mem_filter.mp mem).2.1
    have e : b*n+1 ≡ b*r+1 [MOD 25] := (rn.mul_left b).add_right 1
    change (b*n+1)%25=(b*r+1)%25 at e
    exact e.trans prod) (by
    intro n hn
    obtain ⟨p,hp,nb⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨nN,pdv⟩ := Finset.mem_filter.mp nb
    exact ⟨Finset.mem_range.mp nN,p,bound (mem_filter.mp hp).1,(mem_filter.mp hp).2,pdv.2⟩)
  have first := sieve_set_card_bound N 25 Q (Q.biUnion B) (fun p n => n ≡ r [MOD 25] ∧ p^2∣b*n+1)
    Subset.rfl (fun p hp => off_count_modEq25_le' N p b r (prime (sub hp)) (mem_filter.mp (no5 (sub hp))).2)
  have est := crt_prime_sum N b Q (sub.trans no5) (fun he => sub.trans (no2 he))
  have weight := mul_le_mul_of_nonneg_left est (show 0 ≤ (N:ℝ) by positivity)
  have countR : (S.card:ℝ) ≤ ((Q.biUnion B).card:ℝ) + ((R.biUnion B).card:ℝ) := by exact_mod_cast cards
  have lcr : 408*(Q.card:ℝ) ≤ 2*(N:ℝ)+408*25880 := by exact_mod_cast lc
  have hcr : (((R.biUnion B).card:ℕ):ℝ) ≤ K := by exact_mod_cast hc
  have errors : (Q.card:ℝ)+(K:ℝ) ≤ (N:ℝ)*(212/25000)-1 := by
    by_cases h3400000 : N≤3400000
    · have c := PrimeBlocks.cap142000 Q smallPr (fun q hq => by have := cutoff q hq; omega)
      have cr : (Q.card:ℝ)≤13185 := by exact_mod_cast c
      have kr : K=14720 := by dsimp [K]; split <;> omega
      rw [kr]
      have n : (3300000:ℝ)≤N := by exact_mod_cast (show 3300000≤N by omega)
      linarith only [cr,n]
    by_cases h3600000 : N≤3600000
    · have c := PrimeBlocks.cap151000 Q smallPr (fun q hq => by have := cutoff q hq; omega)
      have cr : (Q.card:ℝ)≤13934 := by exact_mod_cast c
      have kr : K=14720 := by dsimp [K]; split <;> omega
      rw [kr]
      have n : (3400000:ℝ)≤N := by exact_mod_cast (show 3400000≤N by omega)
      linarith only [cr,n]
    by_cases h4000000 : N≤4000000
    · have c := PrimeBlocks.cap167000 Q smallPr (fun q hq => by have := cutoff q hq; omega)
      have cr : (Q.card:ℝ)≤15255 := by exact_mod_cast c
      have kr : K=14720 := by dsimp [K]; split <;> omega
      rw [kr]
      have n : (3600000:ℝ)≤N := by exact_mod_cast (show 3600000≤N by omega)
      linarith only [cr,n]
    by_cases h5000000 : N≤5000000
    · have c := PrimeBlocks.cap209000 Q smallPr (fun q hq => by have := cutoff q hq; omega)
      have cr : (Q.card:ℝ)≤18720 := by exact_mod_cast c
      have kr : K=14720 := by dsimp [K]; split <;> omega
      rw [kr]
      have n : (4000000:ℝ)≤N := by exact_mod_cast (show 4000000≤N by omega)
      linarith only [cr,n]
    by_cases h7000000 : N≤7000000
    · have c := PrimeBlocks.cap292000 Q smallPr (fun q hq => by have := cutoff q hq; omega)
      have cr : (Q.card:ℝ)≤25386 := by exact_mod_cast c
      have kr : K=14720 := by dsimp [K]; split <;> omega
      rw [kr]
      have n : (5000000:ℝ)≤N := by exact_mod_cast (show 5000000≤N by omega)
      linarith only [cr,n]
    by_cases h12000000 : N≤12000000
    · have c := PrimeBlocks.cap501000 Q smallPr (fun q hq => by have := cutoff q hq; omega)
      have cr : (Q.card:ℝ)≤41618 := by exact_mod_cast c
      have kr : K=14720 := by dsimp [K]; split <;> omega
      rw [kr]
      have n : (7000000:ℝ)≤N := by exact_mod_cast (show 7000000≤N by omega)
      linarith only [cr,n]
    by_cases h16000000 : N≤16000000
    · have c := PrimeBlocks.cap667000 Q smallPr (fun q hq => by have := cutoff q hq; omega)
      have cr : (Q.card:ℝ)≤54096 := by exact_mod_cast c
      have kr : K=29440 := by dsimp [K]; split <;> omega
      rw [kr]
      have n : (12000000:ℝ)≤N := by exact_mod_cast (show 12000000≤N by omega)
      linarith only [cr,n]
    have kr : K=29440 := by dsimp [K]; split <;> omega
    rw [kr]
    have n : (16000000:ℝ)≤N := by exact_mod_cast (show 16000000≤N by omega)
    linarith only [n,lcr]
  linarith only [first,weight,countR,hcr,errors]
end Erdos848Pure

namespace Erdos848Pure
open Finset Erdos848Port

private theorem odd_rectangle_crt (k : ℕ) (X Y : Finset ℕ)
    (xs : ∀ n ∈ X, n < 25*k+7 ∧ n%25=18 ∧ ¬2∣n)
    (ys : ∀ n ∈ Y, n < 25*k+7 ∧ n%25=7 ∧ ¬2∣n) :
    X.card+Y.card ≤ k := by
  classical
  have info (x : ℕ) (hx : x ∈ X ∪ Y) : x < 25*k+7 ∧ (x%25=18 ∨ x%25=7) ∧ ¬2∣x := by
    rcases Finset.mem_union.mp hx with h|h
    · obtain ⟨lo,r,o⟩ := xs x h
      exact ⟨lo,Or.inl r,o⟩
    · obtain ⟨lo,r,o⟩ := ys x h
      exact ⟨lo,Or.inr r,o⟩
  have dis : Disjoint X Y := Finset.disjoint_left.mpr (by
    intro x xX xY
    have := (xs x xX).2.1
    have := (ys x xY).2.1
    omega)
  have inj : (X∪Y).card ≤ (range k).card := Finset.card_le_card_of_injOn (fun x => x/25)
    (by intro x h; obtain ⟨lo,r,_⟩ := info x h; apply Finset.mem_range.mpr; change x/25 < k; rcases r with h|h <;> omega)
    (by
      intro x hx y hy eq
      obtain ⟨_,rx,ox⟩ := info x hx
      obtain ⟨_,ry,oy⟩ := info y hy
      change x/25 = y/25 at eq
      rcases rx with h|h <;> rcases ry with h|h <;> omega)
  simpa [card_union_of_disjoint dis] using inj

theorem hall_3300k (k : ℕ) (big : 3300000 ≤ 25*k+7) (X : Finset ℕ)
    (xs : X ⊆ (range (25*k+7)).filter (fun n => n%25=18)) :
    X.card ≤ ((Erdos848.A₇ (25*k+7)).filter (fun a => ∃ b∈X, Squarefree (a*b+1))).card := by
  classical
  by_cases prior : 400000000 ≤ 25*k+7
  · exact hall_400M k prior X xs
  have hi : 25*k+7 ≤ 400000000 := by omega
  let N := 25*k+7
  let Γ := (Erdos848.A₇ N).filter (fun a => ∃ b∈X, Squarefree (a*b+1))
  let Y := Erdos848.A₇ N \ Γ
  have xin (x : ℕ) (h : x∈X) : x<N ∧ x%25=18 := by
    have e := Finset.mem_filter.mp (xs h)
    exact ⟨Finset.mem_range.mp e.1,e.2⟩
  have yin (y : ℕ) (h : y∈Y) : y<N ∧ y%25=7 := by
    have e := Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1
    exact ⟨Finset.mem_range.mp e.1,e.2⟩
  have conflict {x y : ℕ} (xh : x∈X) (yh : y∈Y) : ¬Squarefree (y*x+1) := by
    intro sq
    exact (Finset.mem_sdiff.mp yh).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp yh).1,x,xh,sq⟩)
  have base : (Erdos848.A₇ N).card = k := by change (Erdos848Port.A₇ N).card = k; rw [A₇_card]; dsimp [N]; omega
  have parts : Y.card + Γ.card = k := by
    rw [←base]
    exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset ..)
  change X.card ≤ Γ.card
  by_cases xe : X.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp xe]
    simp
  by_cases ye : Y.Nonempty
  swap
  · have empty := Finset.not_nonempty_iff_eq_empty.mp ye
    rw [empty,card_empty,zero_add] at parts
    rw [parts]
    have bound : X.card ≤ (A₁₈ N).card := Finset.card_le_card xs
    rw [A₁₈_card] at bound
    dsimp [N] at bound
    omega
  have fromX (x : ℕ) (xh : x∈X) : (Y.card:ℝ) ≤
      (N:ℝ)*((if 2∣x then 163 else 413)/25000:ℝ)+(N:ℝ)*(212/25000)-1 := by
    have residue := (xin x xh).2
    apply crt_bad big hi (xin x xh).1 (r:=7) (by omega) (by omega) Y
      (fun y h => Finset.mem_range.mpr (yin y h).1) (fun y h => (yin y h).2)
    · intro y yh
      simpa [Nat.mul_comm x y] using conflict xh yh
    · intro y yh
      exact cross_residue_18_7_not_div_25 x y (xin x xh).2 (yin y yh).2
  have fromY (y : ℕ) (yh : y∈Y) : (X.card:ℝ) ≤
      (N:ℝ)*((if 2∣y then 163 else 413)/25000:ℝ)+(N:ℝ)*(212/25000)-1 := by
    have residue := (yin y yh).2
    apply crt_bad big hi (yin y yh).1 (r:=18) (by omega) (by omega) X
      (fun x h => Finset.mem_range.mpr (xin x h).1) (fun x h => (xin x h).2)
    · intro x xh
      exact conflict xh yh
    · intro x xh
      exact cross_residue_7_18_not_div_25 y x (yin y yh).2 (xin x xh).2
  have count (x y : ℕ) (xh : x∈X) (yh : y∈Y) (even : 2∣x ∨ 2∣y) : X.card+Y.card ≤ k := by
    have a := fromX x xh
    have b := fromY y yh
    have kbig : (132000:ℝ) ≤ k := by exact_mod_cast (show 132000 ≤ k by omega)
    dsimp [N] at a b
    push_cast at a b
    exact_mod_cast (show (X.card:ℝ)+(Y.card:ℝ) ≤ k by
      by_cases xE : 2∣x <;> by_cases yE : 2∣y <;> simp [xE,yE] at a b even <;> linarith)
  by_cases ex : ∃ x∈X, 2∣x
  · obtain ⟨x,hx,h⟩ := ex
    obtain ⟨y,hy⟩ := ye
    have := count x y hx hy (Or.inl h)
    omega
  by_cases ey : ∃ y∈Y, 2∣y
  · obtain ⟨y,hy,h⟩ := ey
    obtain ⟨x,hx⟩ := xe
    have := count x y hx hy (Or.inr h)
    omega
  have bound := odd_rectangle_crt k X Y (fun x h => ⟨(xin x h).1,(xin x h).2,fun e => ex ⟨x,h,e⟩⟩)
    (fun y h => ⟨(yin y h).1,(yin y h).2,fun e => ey ⟨y,h,e⟩⟩)
  omega

end Erdos848Pure

namespace Erdos848Pure.Window
open Finset Erdos848

def Matching (k : ℕ) : Prop := ∃ f : ℕ → ℕ,
    (∀ i<k,f i<k ∧ Squarefree ((25*(f i)+7)*(25*i+18)+1)) ∧
    ∀ i<k, ∀ j<k, f i=f j → i=j

private theorem join {s t : ℕ} (pre : Matching s) (g : ℕ → ℕ)
    (good : ∀ i<t,g i<t ∧ Squarefree ((25*(s+g i)+7)*(25*(s+i)+18)+1))
    (inject : ∀ i<t, ∀ j<t,g i=g j → i=j) : Matching (s+t) := by
  obtain ⟨f,fi,inj⟩ := pre
  let h (i : ℕ) := if i<s then f i else s+g (i-s)
  refine ⟨h,?_,?_⟩
  · intro i hi
    dsimp [h]
    split
    · rename_i lt
      exact ⟨by have := (fi i lt).1; omega,(fi i lt).2⟩
    · rename_i lt
      have row := good (i-s) (by omega)
      rw [show s+(i-s)=i by omega] at row
      exact ⟨by omega,row.2⟩
  · intro i hi j hj eq
    dsimp [h] at eq
    split_ifs at eq with il jl jl
    · exact inj i il j jl eq
    · have := (fi i il).1
      omega
    · have := (fi j jl).1
      omega
    · have res := inject (i-s) (by omega) (j-s) (by omega) (by omega)
      omega

def checkRow (fast : ℕ → Bool) (k t : ℕ) (g : ℕ → ℕ) : Bool :=
  decide (0<t ∧ t≤k) && (List.range t).all (fun i =>
    decide (g i<t) && fast ((25*(k-t+g i)+7)*(25*(k-t+i)+18)+1) &&
    (List.range i).all (fun j => decide (g i≠g j)))

private theorem row_sound {fast : ℕ → Bool} (sound : ∀ n,fast n=true → Squarefree n)
    {k t : ℕ} {g : ℕ → ℕ} (h : checkRow fast k t g=true) (pre : Matching (k-t)) : Matching k := by
  simp only [checkRow,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range] at h
  have size : k-t+t=k := by omega
  rw [←size]
  apply join pre g
  · intro i hi
    have row := h.2 i hi
    exact ⟨row.1.1,sound _ row.1.2⟩
  · intro i hi j hj eq
    rcases lt_trichotomy i j with lt|same|gt
    · exact ((h.2 j hj).2 i lt eq.symm).elim
    · exact same
    · exact ((h.2 i hi).2 j gt eq).elim

theorem all_prefixes {fast : ℕ → Bool} (sound : ∀ n,fast n=true → Squarefree n)
    (T : ℕ → ℕ) (rows : ℕ → ℕ → ℕ) (B : ℕ)
    (audit : ∀ k, 0<k → k≤B → checkRow fast k (T k) (rows k)=true) :
    ∀ k≤B,Matching k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro kB
    by_cases z : k=0
    · subst k
      exact ⟨id,by simp,by simp⟩
    · have h := audit k (by omega) kB
      have pos : 0<T k ∧ T k≤k := by
        simp only [checkRow,Bool.and_eq_true,decide_eq_true_eq] at h
        exact h.1
      exact row_sound sound h (ih (k-T k) (by omega) (by omega))

theorem hall_of_matching {k : ℕ} (match_k : Matching k) (X : Finset ℕ)
    (xs : X ⊆ (range (25*k+7)).filter (fun n => n%25=18)) :
    X.card ≤ ((A₇ (25*k+7)).filter (fun a => ∃ b∈X,Squarefree (a*b+1))).card := by
  obtain ⟨f,good,inj⟩ := match_k
  have info (x : ℕ) (hx : x∈X) : x/25<k ∧ x=25*(x/25)+18 := by
    obtain ⟨hr,hd⟩ := mem_filter.mp (xs hx)
    have := mem_range.mp hr
    omega
  apply card_le_card_of_injOn (fun x => 25*(f (x/25))+7)
  · intro x hx
    obtain ⟨short,eq⟩ := info x hx
    have g := good (x/25) short
    have base : 25*(f (x/25))+7 ∈ A₇ (25*k+7) := mem_filter.mpr ⟨mem_range.mpr (by omega),by omega⟩
    apply mem_filter.mpr
    refine ⟨base,x,hx,?_⟩
    convert! g.2 using 2
    exact congrArg (fun n => (25*f (x/25)+7)*n) eq
  · intro x hx y hy eq
    change 25*(f (x/25))+7=25*(f (y/25))+7 at eq
    obtain ⟨xi,xx⟩ := info x hx
    obtain ⟨yi,yy⟩ := info y hy
    have := inj _ xi _ yi (by omega)
    omega

end Erdos848Pure.Window

namespace Deldor14.Cube848
open Finset
def cut (B:ℕ) : Finset ℕ := (range (B+1)).filter Nat.Prime
def primorial (B:ℕ) : ℕ := ∏ p∈cut B, p

theorem prod_free {S:Finset ℕ} (h:∀p∈S,Nat.Prime p) : Squarefree (∏p∈S,p) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have pr := h a (by simp)
    have hpr (p) (hp:p∈s) := h p (mem_insert_of_mem hp)
    rw [prod_insert ha,Nat.squarefree_mul_iff]
    refine ⟨pr.coprime_iff_not_dvd.mpr ?_,pr.squarefree,ih hpr⟩
    intro hd
    obtain ⟨b,hb,div⟩ := (pr.prime.dvd_finsetProd_iff ..).mp hd
    have eq := ((hpr b hb).dvd_iff_eq pr.ne_one).mp div
    exact ha (eq ▸ hb)

theorem primorial_free (B:ℕ) : Squarefree (primorial B) :=
  prod_free (fun p h => (mem_filter.mp h).2)

theorem dvd_primorial {B p:ℕ} (hp:p.Prime) (hle:p≤B) : p∣primorial B := by
  exact Finset.dvd_prod_of_mem id (mem_filter.mpr ⟨mem_range.mpr (by omega),hp⟩)

def test (B P n : ℕ) : Bool :=
  let g := n.gcd (P%n)
  let r := n/g
  decide (0<n ∧ n≤B^3 ∧ g.Coprime r ∧ (r=1 ∨ ¬IsSquare r))

theorem sound_facts {B P n:ℕ} (freeP : Squarefree P) (includes : ∀p, Nat.Prime p → p≤B → p∣P) (yes:test B P n=true) : Squarefree n := by
  let g := n.gcd (P%n)
  let r := n/g
  obtain ⟨pos,small,cop,ns⟩ := of_decide_eq_true yes
  change g.Coprime r at cop
  change r=1 ∨ ¬IsSquare r at ns
  have gd : g∣n := Nat.gcd_dvd_left .. 
  have gp : g∣P := (Nat.dvd_mod_iff gd).mp (Nat.gcd_dvd_right ..)
  have divide : r*g=n := Nat.div_mul_cancel gd
  have free : Squarefree g := Squarefree.squarefree_of_dvd gp freeP
  have low (p:ℕ) (pr:p.Prime) (pd:p∣r) : B<p := by
    by_contra! lo
    have dn : p∣n := divide ▸ pd.trans (dvd_mul_right ..)
    have dP : p∣P := includes p pr lo
    have dg : p∣g := Nat.dvd_gcd dn ((Nat.dvd_mod_iff dn).mpr dP)
    exact (Nat.Prime.not_dvd_one pr) (cop ▸ Nat.dvd_gcd dg pd)
  have rf : Squarefree r := by
    apply Nat.squarefree_iff_prime_squarefree.mpr
    intro q prime bad
    obtain ⟨a,ha⟩ := bad
    have dq : q∣r := ⟨q*a,by simpa [Nat.mul_assoc] using ha⟩
    have lq := low q prime dq
    have one : a≠1 := by
      rintro rfl
      rcases ns with o|no
      · simp [o] at ha; nlinarith [prime.two_le]
      · exact no ⟨q,by simpa using ha⟩
    obtain ⟨s,sp,sa⟩ := Nat.exists_prime_and_dvd one
    have ds : s∣r := ha ▸ sa.trans (dvd_mul_left ..)
    have ls := low s sp ds
    have three : B*B*B < q*q*s :=
      Nat.mul_lt_mul_of_lt_of_le (Nat.mul_self_lt_mul_self lq)
       (Nat.le_of_lt ls) (by omega)
    have le : r≤n := Nat.div_le_self .. 
    have apos : 0 < a := by
      by_contra! nope
      have az : a=0 := by omega
      rw [az,mul_zero] at ha
      rw [ha,zero_mul] at divide
      omega
    have sa' := Nat.le_of_dvd apos sa
    rw [ha] at le
    nlinarith [Nat.mul_le_mul_left (q*q) sa']
  rw [←divide,Nat.squarefree_mul_iff]
  exact ⟨cop.symm,rf,free⟩
end Deldor14.Cube848
namespace Erdos848Pure.Prim
open Deldor14.Cube848
private def base : ℕ := 0x23e53db59edc5d34f8aa3605a5ee7eb76eb88534d985cf3706
private theorem base_dvd : base∣Nat.factorial 151 := by decide +kernel
private def ok (P q : Nat) : Bool :=
  decide (q < 2 ∨ (q ≤ 151 ∧ ¬ q.Prime) ∨
    (151 < q ∧ q.gcd base ≠ 1) ∨ (q ∣ P ∧ ¬q*q ∣ P))

private def oddBlock (P start len : Nat) : Bool :=
  (List.range len).all fun i => ok P (2*(start+i)+1)

private theorem ok_sound {q P : Nat} (hp : q.Prime) (h : ok P q = true) :
    q ∣ P ∧ ¬q*q ∣ P := by
  rcases of_decide_eq_true h with h | ⟨_,h⟩ | ⟨large,nontrivial⟩ | good
  · have := hp.two_le
    omega
  · exact (h hp).elim
  · rcases (Nat.dvd_prime hp).mp (Nat.gcd_dvd_left q base) with one | eq
    · exact (nontrivial one).elim
    · have dvd := Nat.gcd_dvd_right q base
      rw [eq] at dvd
      exact (Nat.not_le_of_lt large (hp.dvd_factorial.mp (dvd.trans base_dvd))).elim
  · exact good

private def prim22166 : ℕ := 0x6bc2a5e24ba7302b03d329ce40aaf88187d927dc5ffea08b54181256c2940464372897848817d3cd9f041bad9433bde9b41170fbf9cb1622908e28538cab2b91bb95f96a05ff9c683386957e34330db11bae01d1dd648d7f80c28ccb5a3af0b349cd433ba0338760062fad362f285c04a798d28ace2f51329eddeb0acb25de243a8d93d4c544b0a32dcc2acb18a96aded088992a70a3b78ee55a15e755a9de5b19fe05758e0f4c842e3c95c63ef8ebcac3f52d0b0cda376946b2952ed63b8ec3c27e547afc54aad5b5580e13bc9396008a9ee1751d0d42bf24510b0ba7c4e54b44e74d4106fe10194df3e15b72b6105b456eff642b70366759bc67eac31f351a944bd70fd3c205d2bbb12fa85d83f446fdc7c89dfcd53730d7377df79e193229446c1d8874b2b1fca745ebd10f05e0a3c2a2b8e67cd5e7db40035ec9c2cfe1a386533d4c1c1d27b6713eab82ad95e1d9607b276e4970a053e46c08e4b0e5666feb27e9cbe93c130542ac6975473fbf149fd8f0c0a8cb5d57de0f2d4089feddc3eaa85cf2bebb92798d3e6140dcdcb66648cf8cdc4066dcc9bd9eacbd4183095a2ebccc222c4e72f98f56c78ced7fdd6b56287f703b474501ab3cb563b204073f02dfc4d36ae7ee8e04b4fafa193f3d64f0eef78ae588aa5ed928956009d5740497350fa06fab40b39d64a487588db21e7ee8cf2348dec1adbe7acce3c3f58465f83f9f2ab6eaa867200494cee6c3bb1621b30bddab664385c37ccbe8ca503ab8be9332de6c51282a6d6b176037b3e36e097d555cad52975bab7fd2453944c156e27fecc11f981732e76f58bb394ee548d7520b672bd0d67e64313723d24b632e664369db49e92d5263bedac744ceb86ae5a34d4a286db71c4a63a41c3e4099eb69e80d707e48f288100428110cd8f6f822a9705a3aab14026cac205de7e069f3e42e98be0d331ccf56ec7e908ee0f3e7cd1f5df64ff86329400314879e2b67fc07b0b0b3be399e8887dec831cc35d69aab0e3798a60a726014a0e9fd68f747a759d52d6e207353cbec7d6ae2a7dca3b221f024bf342edb152c534a80619ea2bb0432a6a73cbce133a2aef24be1f30dfaf500be2110208f3647a32269497a9bef0d1c001e1f48e6406d3e1999a9b50fbad4f1df09f5d06ecb88e17624e791e548ccff49bfa3eeb22492cf031ae6e126aadac5b6565178d08f5817b5387437c7b90d3f4d6386b6b64c15714838f15e4c77b6365948e2ce5257daa3d5a8640c23ccf495cf7d2406018885ea3f185aee6ba2bb6eac9613257dd16c0f404f51a79d32c3f82929790e6c53e81be7d92fd122b2a7022bb8713868613242b67331bde7a7476c89f1123c6c6228d8034022a28b57772043d9e200baae5af26dfd2cf7cdc8c06a35af6a6cfac10d702f9bee1000833d62050e00b3576028ba7d3a48a15bc9c9b31326559b0c48aec35ee710690d5b66e737585f3f1dfbb3f6c89622819e69b07d12cfb7e153b7b2c8254e13a57aef960dfa5f7bf5445e6262fe48001e43580e4647cd810ea589a753604d38c229ed6a86f759340b95f2792aac041859f2bd724bc93162c83e4136ad9ecc7c3e428e9747440824551a5f0f088f3de14071a72e47f058837c6c86727e035b38b6b460c0cee66f03fde2b2ac071dd0b8ef4e362b6cd53c1aa3175198179f10044bf7acfbe3f6700437926e06b07ae1066f61cf32a689c9d0d23ec14922c360e842b224d4566c088b2eae4b5c324d223af4aa8c10b0983d771f50306f2ce1ef99c7f0bfbb04f3e9bad677f01a15a083889aa0d3b1455013e91f7a497cd768dd1c2767b66ed567dbfb2266a5ed614493de25c6004b8438a7e828cf35a0cb4cc9a66b9d7b0723935df9a2095eabce39b68d9c322350a38e8aee3f116b1fa3879d1cdea5b662d89b8bf065dde1e4414235fba15332cf970f063786c732421a3d46fe733f05c16498a9e3292b5d2269272f1ad42f773216cd4fc6c62be3d4e2251a779859e0f5c2dba04e6cac3b2c69e4a182aae409ad8f44c0e728afaf7c142362e7095a80cbd91e02c5cdf7472f799530032f99f8eadca61434d9ce74dc3cd8028db57b67b06b217867f36880ae45130abbf99fdf2ff3a46ba3fa758aff074b6d7e58a7b4e8b42a67bc3fd3c101c420c24984ba5e6235447b95eb04fbd84287569de047ea62a4c740ed3bb0e43658d9724fcf4f1742e7e89f5b60d741df26764c3302b1210641c2c74cbc74ba33a53ba7a96470e06eab93ddb2b9f0f53fee6ad3c2188964a43ae95cc6780599b547c8ec58b8c116de316f002ee53e17d783d819f4bd481bcd1c6e157ff491b92174d82d2ed718dd946418ec3dc319ebac01b795ead1e9768d43c28d5bab6ef5fa6112fc3929657215db62f8454351fad0feb6565363b67129f891dc919496eabcf9af85142d3f22602920ca615bee83badb904c0d99a56c46786e6770a0f153fe0a2753c41cc4f73ad27e09eda5a427e52765b6920774676d4ee67f8a1e69a8eb96b7cc06eff20113b7371725119e946161bcb828b6ce972444a52193a4e4b2544df7040334fce1ed9adc2f9cea16cabded5d07319b5edce7062712f4df79f0193526d77f598f8d1c7cd1e50307ae546da6531953dc74217c4eb8a80f96bb0c0455f343a3459434c135d4fe7c519859af8725ee37dea41f1ae30fc772454fa6c4b82e89f98477f6eecf2df28ba50c18abc882495995018a8c40ccb0ee8b09596be72f2643b43c8853cbad1ede2388f15771f7b46cc7e43cf4ff2dc9faa3cbb1c0420955e4b31033c66cead3e2de129697651ee59883626c4c509ed9d9058d1d52885302c9a036fde6ecb456a145cb8f238af7b1cc519b1877753da624e42ede26169b16f1beed899d16cbb088c13b92e34d71dc76866acad6036bd341028896eeb285b7076568ad5165c6ab42f453b9dfadd23a22692ebf9a74bd34b6545f0c8b98cf3b741f0aebd175696e35a9f95f527319ec92891dfbdea3a218fe37379e17a77b43c4d4fe6e8f25d2eb39e04baf9a3c7dd81b1e513fa15b026ec9142317065a42082359d7cabedc0aa6941a41c318feff4ba43d159f068627bf9f738e2e7cfa03bb3f5868ab3e7004e290bb033bb312627b5f1ea5a7faba1007d93b978552ca96827a2fa4fda7caa3d99d0ee0d1100bab781e640d72632127c40619bba885759ec08653a25cb835f7b0dcfae4646329e2b8058fb41fc01df9c6a32a964e751b52890173c718f2e3fdb33856d021e8fb2c9d7bf3928ad3827b7ff9cf133c91984d4b45449c2b4f6c8577d1c082e5dbb0ea6f8356cf8ddd602a1b09bfbfdee6aa7d64eb920e5d7f1daa3dcea6d5933120b0ced3052b6404fa0adf568e750dbc3a80ab542b0ca80ac6ad16064378259d12ff9f4229760e1813fa92a9f1c724ff98c74afc6edcd633fa160a8557c641c363bd7347fb24f9b9eab3476a6b7b2623636bd4754fe725870a06f276c484059d3fa94feaa92163f36adeaadf3e8fb380f71ef117b72f75fe39c2a69de258e51fe9b995ad68328257542589140cfc2d4c44c954653b1b7f45699856d7db5dd420dd344ae3e99db7156cca242d2628ea2d5da83b566909c84985d18b35e9b8af0314f1e3b70385c83de5117e64981e261f8548e1c6239cc7e16e44b42877fe71b230728b2379e52824823fad7e7ec8f599af2de80107904b80208689fb7eeb5f2fd1988ce3d5734bc041fd420896a2b47d2d5fbb2a6f338d6cafa2a9a6ce317fcf820f0cf1c7f6a13b46846939a554cd8f4d59e9971c431fd9f9eab24af47d0741d44cc3c355460d70bc1d38cb6ba95cf0db292c3d6ca3e7c6587cb8a9f6543de88fedf44dc0440134ebffb55badb85accbd3ddcb7b7b5b07cf427026c2f1170412677f91f93bbe2d6f6661978d6237d7313d69b5ab66f073cc3e2c65bbbe1351f76c621b283920fe89bf1db1973186b0ebab5e1a40dae38eff89c7ca241ba8612b6d5635cafa29896b775710b44e7a78c7fbf8755cf54f1af2e2849598527ce78ab08c9ede3383e512b39ae68cf3620ba57e1444ca5c1528f8da188c53e46e97941a60c8107d8104841b25a521084dd11c5514898def8b5978fbf3b668992982430149bd82311eb4052af39617b2b9823b2d23fd1ac46886e59773314f2bdfdeb5801d131315db85b0be1d649950ff4d27703f75849e61079bf4c1463bc7331ec7541294ce9120e838dbc249ef3941ad80adbbc30a320c42f05b6069795b8d835b447fece4c12b5958807f90c659a20d691370a8ec76d8e69b247abf010bfd624d3c86a2b5e07a0c05624147d8f3ee18dd02a960472fa9daa417dc77209a88032376dc272593e6807d41c23d8356450b8e9f916572368c9d6b35c425aca625e244382006496840f7524cb3cd6757332271a88b00630649aaa71367412c3ca2a6abe4e9f6a5192dad1a776e868fd4b6805ce1b0105c2be31e2c1911d6251667ca52fa3d6e83eb903c0c9db28608427a2c737f7aabe1e5ce35a1a16ce6d508f01357e8a1c75c8cd59fdeefd983bdc39a385cb6c4261112883f6b42a149bb6acde2d908517a5ac2bcbdaf0d483386c58e1c9f5d30b0122abf9ccf17d42e32acdba4920bcbfbd9bf332ae90748166f1b632c235a6be800d8b3a78171c244740cb3d4605cc85fe1186ecbcb4df4f344a7beed1b7d5004ec366d4e0955aec1992bad82ac8255077a6b1d552648062f1816f54290a634b65561d1cebdbec9480f2c6c02dd6d9424f793a9508bc3aa21670d922f3a5ceee0d3f05e76db24e7f22bedc51084dda48ba4511a0aef5795c16b5fe8659073489e4486c99f490c30b648927b4a66152ef8dad8b987db997fb3f698915220eac707b04ab47898473ebddcd33425c639c529ecbae0085c98ed556a3fe6c0c2f5289de2c7dd0c4b9e72039bf04982189c1d0644ebea666e839c57e414aa4eb2aa08103e523c09db2392b2d3de5cc402c162896cde29c7aacf70838f8451aabb9bd8b8aa19003b5e05b31feb8bec30754e947fa356fc326c9193b07182068c84a2c21cb9e7daf725822df2b835394f9900d4a5ec3d52c71e44650a564a28911e56dc405dd6be59d4240a18a33b7fd8b202096ea314ab783e04de21a96a8ad15500b0efc8794b66446aed062a4637b305b3168d528f1f05246847d5066eb209fdbec646f666f9b20e655a46e7e2fbef0720b6b689a9f5db3c6a64b39ca564d22327c3a5345dd9c90a9af29dfc4624f8b5a216bb28e7f5cb0c891447c79e8c26279901947ac3df1363369f13ef01c3e9980f16e63e17cfdd38f125cc1c380178c2290a1c2b53a11fce0a043820efde6f7e580e5dc9cff292651365025994ff9204b86a71c5ec33da9efcf5bb23333959cf3ea137c0c2cb71480f822c93432fc436b97a2d8cb8e9dba7686d9c66e7e24e654788c7dc6536f4ce9aec1b77ef4363b146e62afc24454f854465567ef9a097a55a988e74572d3714999fccb4ca296426c56e5cf92429ab943cd4c6bd58fca2a4bbbf79ba764a71d23c30fea3607c0145c75f25516de56047832fbb2b0314a97e346493c267ca9f2d0d987840cd50d67ea1ae012884473c5b03f840afe
set_option maxRecDepth 60000 in
private theorem certBlocks22166 : ∀i:Fin 87, (List.range 128).all (fun j =>  decide (22166<2*(i.val*128+j)+1) || ok prim22166 (2*(i.val*128+j)+1))=true := by decide +kernel
private theorem all22166 (r:ℕ) (pr:r.Prime) (bound:r≤22166) : r∣prim22166 ∧ ¬r*r∣prim22166 := by
  by_cases e : r%2=0
  · have hd : 2∣r := Nat.dvd_of_mod_eq_zero e
    rcases (Nat.dvd_prime pr).mp hd with h|h
    · omega
    · subst r; decide +kernel
  · let i : Fin 87 := ⟨r/2/128,by omega⟩
    have eq : 2*(i.val*128+r/2%128)+1=r := by dsimp [i];omega
    have h := List.all_eq_true.mp (certBlocks22166 i) (r/2%128)
      (List.mem_range.mpr (Nat.mod_lt _ (by decide : 0<128)))
    change (decide (22166<2*(i.val*128+r/2%128)+1) || ok prim22166 (2*(i.val*128+r/2%128)+1))=true at h
    rw [eq] at h
    exact ok_sound pr (by simpa [Nat.not_lt.mpr bound] using h)
set_option maxRecDepth 60000 in
private theorem fac22166 : prim22166 ∣ Nat.factorial 22166 := by decide +kernel
private theorem free22166 : Squarefree prim22166 := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro r pr div
  have d : r∣prim22166 := (dvd_mul_right r r).trans div
  exact (all22166 r pr (pr.dvd_factorial.mp (d.trans fac22166))).2 div

def fast (n : ℕ) := Deldor14.Cube848.test 22166 prim22166 n
theorem sound (n : ℕ) : fast n=true → Squarefree n :=
  Deldor14.Cube848.sound_facts free22166 (fun r pr h => (all22166 r pr h).1)
end Erdos848Pure.Prim

namespace Erdos848Pure.Window.Data
open Erdos848Pure.Window
open Erdos848Pure.Prim

private def pack0 : Array ℕ := #[0x200800200800800500200800200500204,0x8008002008052008002008002008004,0x50020080020080080080020080020084,0x200800200800200800200800200800204,0x2005002008002008002008002008004,0x80520080020080020080020080020084,0xc0008000400200040008000400200010008000405,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x10008003000200010008000400200010008000405,0x8008008008002008002008002008004,0x80020080080080020080020080020084,0x200800200800280800200800202800204,0x2008002808002008002008002008004,0x50800800080000800080000800080000800200002000086,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x2000080000800080000800080000800200000800050800806,0x2008002008002008008008002008004,0x80080080020080020080020080020084,0x200800200800200800200800580800804,0x200009800000200000800000200000800000200000800000200000800008,0x80020080020080020080080080020084,0x200800200800200800200800200800204,0x2008002808002008002008002008004,0x80000800080000800080000800200000800080000800086,0x200800200800200800200800200800204,0x2008002008002008002008008008004,0x50020080080080020080020080020084,0x10008014400200010008000400200010008003005,0x800080000800080000800850000800080000800200006,0x880000800080000800080000800080000800050000a00086,0x200800200800800800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x800200000800080000800050000800080000800080000806,0x2008002008002008008008002008004,0x80020080020080020080020080020084,0x10008000400200010008000400201040008000405,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800584,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x2000200000800080000800080000800080000800080000806,0x800200000800080002000080000800080000800080006,0x80020080020080020080020080020084,0x200800205800200800800520200800284,0x2008002008002008002008002005204,0x80020080020080020080020080020084,0x2000008000002000008000002000008000002000008000002009808000002008,0x800000800000800000800050200000800009800000800000200000800008,0x80020080020080020080020080020084,0x800080000800080000800200000800080000800080000806,0x8008008008002008002008002008004,0x80020080020080020050080080020084,0x200800200800800800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020280020084,0x10008000400700010008000400200010008014405,0x800080000800080000800080000800200000800080006,0x80020080020080020080020080020084,0x200500200800200800200800200800204,0x8008008008002008008008002008004,0x80020080020080020080020080520084,0x200800800800800800202805200800204,0x8008002808002008002008002008004,0x80020080080080020080020050020084,0x200800200800200800200800200520204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080080084,0x800805200800200800280800200800804,0x2008002008002008002008002008004,0x80000800080000800200000800080000800080000800086,0x800800200800200800200800200800204,0x2008002008002008002008002008004,0x80000800080000800200000800050000800080000800086,0x200800200800200800200800200805204,0x2008002008002008002008002008004,0x80020080020080020080080080020084,0x200800200800800800800800200800204,0x2008002008002008002008008008004,0x80000800080000800080000800080000800200002000206,0x200800200800200800800800202800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x800080000800080000800050802000080000800200006,0x80020080020052080080020080020084,0x200800200800200805200800200800204,0x2008002008002008008008008008004,0x2000100080004007000100080004002000100085,0x200800200800200800200800280800204,0x2008008005202008002008002008004,0x80020080020080020080020080020084,0x200500202800200800200800200800204]
private def pack1 : Array ℕ := #[0x2008052008002008002008002008004,0x80020080080080020080020080020084,0x200800200800200520200800200800204,0x2008002005008008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020280020084,0x200800200800200800200800800800204,0x40020001000800040020001001c00040020005,0x80080080020080020080020080080084,0x200800200800200805200800200800204,0x2008008008002008002008002008004,0x2000100080004002000100080030002000100085,0x800080000800080000800080000800080200800080002006,0x2008002008002008002008002008004,0x80020080020080020080080080080084,0x800200000800080000800080000800200800800080000806,0x40020001000800040020001000800300020005,0x80020080020080020080020080020084,0x2000008000002000008000002000208000008000008000002000008000098008,0x8008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200520200800204,0x2008002008052008008008002008004,0x80020080020080020080020080020084,0x200800200800200800202800200800204,0x2008002008002008002005002008004,0x80000800080000800080000800200000800080000800086,0x200800200800280800200800800800204,0x2008002028002008002008002008004,0x80020080020050020080020080080084,0x200800800800200800200800200800204,0x2008002008002008002008002008004,0x80000800200000800080000800080000800080000800086,0x800080000800080000800200000800080000800080000806,0x2008008008002008002008002008004,0x80000800080000800080000800080000800200000800086,0x200800200800200800800800200800204,0x2008002008002008002008002008004,0x200000800080000800080000800080002000080000800086,0x200800200800200800202805200800204,0x2008002008002008002008002008004,0x2080000020000080000080000080000020000080000020000080000970000088,0x200800200800200800200800200800204,0x800080000800080000800080000800200000800880006,0x80020080020080020080020080020284,0x40008001000201040008000400200012008001005,0x2008002008002008002008008008004,0x80000800080000800200002000080000800080000800086,0x200800200800200800252800200800204,0x8008002008002008002008002008004,0x200000800080000800080000800080000800080000800086,0x10008000400700010008000400200040008000405,0x2008002008002008002008002008004,0x80020080020080080080020080020084,0x10008003000144010008000400200010008000405,0x2008002008002008002008002008004,0x50020080080080020080020080020084,0x200800200800200800800800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x800080000800050802000080000800200000800080006,0x80020080020080080080020080020084,0x800800800800200800200800200800204,0x2808002008002008002008002008004,0x80080080020080020080020080080084,0x200800200800200805200800200800204,0x2008008008002008002008002008004,0x80020080020080020080028080020084,0x200800200800200800280800200800204,0x2000080000800200000800080000800080000800080006,0x80020080020080020080520080020084,0x200800202800200800200800200520204,0x2008002008002808002008008008004,0x80020080020080020080020080020084,0x200800200800200520200800200800804,0x2008002008002008002008008008004,0x80020080080080080080020080020084,0x200800200800200800200505200800204,0x800080000800080050800080000800200000800080006,0x80020080020080020080020080080084,0x200500280800200800200800200800204,0x2008002008002008008008002008004,0x80020080020080020080020080020084,0x200800200800200800200800800800204,0x2008002008002808002008002008004,0x200000800080000800080006000080000800080000800086,0x200800200800200800200800200800204,0x2008002005002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800800800200800204,0x2008002008008008002008002008004,0x50020080020080020080020080080084,0x200800200800202800800800200800204,0x40014401000800040020001000800040070005,0x80020080020080020080020080020084,0x200800200500200800200800200800204,0x1440020001000800040070001000800040014405]
private def pack2 : Array ℕ := #[0x80080080020080020080020080020084,0x200805200800200800200800200800204,0x2008008008002008002008002008004,0x80020080020080020080020080020084,0x800080002000080005c80200000800200000800080000806,0x800080000800080000800200800800080000800080006,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200520200800200800200800200500204,0x8008002008002008008008008008004,0x2000008008800008000800060001c0000800080000800086,0x200800800800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020050020080080084,0x800080000800080000800200800880080000800080000806,0x2008002808002008008008002008004,0x80020080020052020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x20001000800040020001001c0004002000400085,0x2000080050800080200800080000800050000800080000806,0x52008002008008008002008002008004,0x80020080020080028080080080020084,0x200800200800200800200800200800204,0x2008002005002008002008002008004,0x80020080020080080080020080020084,0x202800200800200800200800200800204,0x2028002008002008002008002008004,0x80020080020080020080080080020084,0x200800200520200800200800200800204,0x2008002008002008002008008008004,0x80080080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008008008002008004,0x80000020000080000020000080000020000080000020000080000020000988,0x280800800800200800200800200800204,0x8008002008002008002008002005004,0x80020080020080080080020080020084,0x200800200800200800200800200800204,0x2008002008002008008008002008004,0x80080080020080020080020080020084,0x800080000800080000800080000800080000800200002006,0x800080000800200000800080000800080000800080006,0x80020080020080020080020080020084,0x200800200800200800280800800800204,0x2008002008002008002008002008004,0x80020080080080020080020080020084,0x200800202800202800200800200520204,0x2008002008008008002005208008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x40020001001c00040020001000800040020005,0x80020080020080020080020080020054,0x200800200800200800200800200800204,0x2008002008008008002008002008054,0x80080080020080020080020080020084,0x200800280800200800200500200800204,0x2008008008002008002008002008004,0x2000100080004002000c00080004002000100085,0x200800200800200800200500200800204,0x2008008008002008002008002008004,0x80000800200050800080000800080002000080000800086,0x200800200800200800200800200800204,0x2008002008002008002008002005204,0x80020080020080020080080080028084,0x800080000800200000800080000800080000800080002006,0x8008008008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80080080020080020080020080020084,0x200800200800200800200800200800204,0x2008008008008008002008002008004,0x80020080020080020080020080020084,0x800080050800080000800080000800200002000080000806,0x2008002008002008002008002008004,0x80020080080080020080020080080084,0x200800200800200805200800800800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008008028004,0x80020080020080020080020080020084,0x200520200500200800800800200800204,0x4002000100080004002000c000800040020005,0x80020080020080020080080080020084,0x200800200800200800200800200800204,0x800080000800050800800080000800080000800200006,0x80000800080000800080000800080000800080000800206,0x200800200800800800200800200800204,0x2008002008002008002028002808004,0x80020080020080020080020080020084,0x800200000800080002000080000800080000800080000806,0x202008002008008008002008002008004,0x80020080020080080080020080020054,0x800080000800080000800080000800200000800080000806,0x2008002008002008002008002008004,0x20001000800040020001001c0004002005100085]
private def pack3 : Array ℕ := #[0x200800200800200800200800200800204,0x8008002028002008008008002008004,0x80020280020080020080020080020084,0x202800800800200800200800200800204,0x2008002008002008002008002008004,0x80050080080080020080020080020084,0x200800200800200800800800800800204,0x800200000800080000800080000800080000800080006,0x80000800142000800080000800080000800080000800206,0x200800200800200800200800200800204,0x2008002008002008002008052008004,0x80020080080080020080020080020084,0xba008000400200040008000400200010008000405,0x2008002008002008002008002008004,0x80080080020280020080080080020084,0x200800200520200800200800200800204,0x2008002008008008002008002008004,0x80020052020080080050020080020084,0x200800200800200800200800800800204,0x2008002008002008002005202008004,0x98080000020000080000020000080000020000080000020000080000020000088,0x200800200500200800280800200800204,0x2008002008002008002008008008004,0x80020080020080020080020080020084,0x200800200800800800200800200800804,0x8008002008002008002008002008004,0x890000020000080000020000080000020000080000020000080000020000088,0x250800200800200800200800200800204,0x2008002008008008002008002008004,0x80020280020080020080020080025284,0x200800200800200800200800200800204,0x800080000800080000800200002000080000800200056,0x80020080020080020080020080020084,0x2000008000002000008000002000008000002000008000098000008000002008,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x580800200800200800200800200800204,0x8008002008002008002028002008004,0x80020080020080020080020080080084,0x800080000800200000800080000800080000800880000806,0x8008002008008008002008002005204,0x80020080020080020080020080020084,0x200800200800200800800800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800280800280800200800204,0x2008002008002008002808002008004,0x80020080020080020080080080020084,0x200800202800200800200800200800204,0x800080002000080000800080000800080000800200006,0x80020080020080020080020080020084,0x800080000800080002000200000800080002000080000806,0x2008002008002008002008002008004,0x80020080020080020050020280020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80000800200000800080000800080000800080000800086,0x200800200800200800200800200800204,0x8008002008002008002008002028004,0x80020080080080020080020080020084,0x200800800800200500200800200800204,0x8008002008002008002008002008004,0x800008002000008000800008000800008002000008001c6,0x200800200800800800200800200805204,0x2008002008002008052008002008004,0x80020080020080080080028080020084,0x200800200800200800200800200800204,0x2008002008002008002008002808004,0x50020080020080020080020080080084,0x800800800800800800200800200800204,0x2008002008002008002008002008004,0x80000800080000800080000800200000800080000800086,0x800080000800080000800080000880200000800080000806,0x8008002008002005202008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x50020080020080020080080080020084,0x200800280805200800200800200800204,0x2008002008002008002008008008004,0x80020050020080520080020080020084,0x800800200805200800200800200800204,0x2008002008002008008008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008052005004,0x80020080020080080080080080020084,0x800080000800080000800080000800200000800080000806,0x2008002008002008008008002008004,0x80020080020080020080020080020084,0x200800200800200800200500200800204,0x2008002008002028002008002008004,0x80020080080080020080020080020084,0x200800200800200800200800200800204,0x800080000800080002000200000800050800800080006,0x80020050080080020080020052020084,0x200800200800500800200800200800204,0x2008002008008008002008002008004,0x80020080020080020080520080020084,0x800080000800080000800080000800080000800200002006]
private def pack4 : Array ℕ := #[0x2008002008002808002008002008004,0x80020080020080080080080080020084,0x200800200800200800200800800800204,0x800080000800080000800080000800080000800200006,0x80080080020080020080020080020084,0x800080000800200000800080000800080000800080002006,0x2005208008002008002008002008004,0x4d00100080004002000100080004002000100085,0x800800200800800800200800200805204,0x2008002008008008002008002008004,0x80080080020080020080020280020084,0x200800200800200800200800200800204,0x2008002008002005002028002008004,0x80020080020080020080020080020084,0x200520200800200800200800200800804,0x8008008008002008008008002008004,0x80000800050000800080000800080000800200000800086,0x200800200800200800200800200800204,0x2008002008052008002008002008004,0x20001000800040020001000800100020001001c5,0x200800200800200800200800200800204,0x2008002008002008002808008008004,0x80020080020080020080020080020084,0x200800200800200800200800800800204,0x800080200800080000800200000800080000800080006,0x80020080020080020080020080080084,0x880080000800080000800080000800080000800200000806,0x2008008005202008002008002008004,0x80020080020080020080020280020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080080080020080020080020084,0xc0008000400200010008001000200010008000405,0x2008002008002008002008008008004,0x80000020000890000020000080000020000080000080000080000020000088,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800280800200800200800200800804,0x2008002008002008052008002008004,0x80020080020080020080020080020084,0xc0008000400200040008000400200010008000405,0x2008002008002008002008002008004,0x80020080020080080080020080020084,0x200800280800200800200800200500204,0x2008002028002008002008002005004,0x80020080020080020080020080020084,0x202800200800200800200800200800204,0x2008002008002005202008002008004,0x80020080020080020080020080020084,0x200520800800200800800800200800204,0x2008002008002008002008002008004,0x80000800080002000200000800080000800080000800086,0x200800200800200800200800200800204,0x2008002508002008008008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x800200000800080000800080000800080000800080006,0x80020052020080020080020080020084,0x98000018000008000008000002000008000002000208000002000008000008008,0x2008008008002028002008002008004,0x80080080080080020080020080080084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80080080080080028080020080020084,0x200800200800200800200800200800204,0x800200000800080000800a00000800080000800080006,0x80020080020080020080020080020084,0x800200000800080000800080000800080000800080000806,0x2008002008002008002008008005004,0x20001000800040020001001c0004002000100085,0x200800200800200800200800200800804,0x2008052008002008002008002008004,0x80020080020080020080020080080084,0x200800200800200800200800200800204,0x2005002008002808002008002008004,0x80020080020080020080020080020084,0x200805200800200800200800200800804,0x2008002008002008008008002008004,0x80020080020080020080020080020084,0x200800200800200800200800800500204,0x2005202008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800800800200800204,0x2008002008002008002008002008004,0x80020080028080020080020080020084,0x200800280800200800200800200800204,0x52008002008008008008008002008004,0x80020080020080020080020080020084,0x800080000800080000800200002000080000800080000806,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x800080000800080000800080000800080000800200000806,0x800200000800080050800080000800080000800080006,0x80020080020080020052520080020084,0x200800800800200800200800200800204,0x2008008008008008008008002008004,0x80020080020080520080020080020084,0x800080000800080002000080000800080000800200000806,0x2028008008002008002008002008004]
private def pack5 : Array ℕ := #[0x80020080020080020080020050020084,0x200800200800200800200800200800204,0x2008002005202008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x8008002008002008002008002008004,0x80020080020080020080080080080084,0x200800800800200500200800200800204,0x2808002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800800800804,0x2005002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x100020001000800040020001000800040041005,0x80020080020080020080020080080084,0x800800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080080080020080020084,0x800200000800080000800080000800080000800080000806,0x2008002028002008002008002008004,0x80000800080000800080000800080000800200000800086,0x200800200800200800800800202800204,0x2008002008002008002008002008004,0x80000800080000800200000800050802000080000800086,0x200800200800200800200800200800204,0x52008002008002008002008008008004,0x80020080020080020280020080020084,0x200800800800200800200800800800804,0x800200000880080000800080000800080000800080006,0x80020080020080020080020080020084,0x200800200800280800200800200800204,0x2028008008002008002008002008004,0x80020080020080080080020080020084,0x800080000800080000800200000800080000800080000806,0x202008002008002008008008002008004,0x80020080020080020080020080020054,0x200800200800200800200800200800204,0x2008002008002008002008052008004,0x80020080080080020080520050020084,0x200800200500200800200800200800204,0x40020001000800040020001000800300020005,0x80020080080080020080020080020084,0x280800200800200500200800200800804,0x2008002008008008002008002008004,0x2000120144004002000100080004002000400085,0x200800200800200800200800200800204,0x2008052008002008002008002028004,0x80020080020080020080020050020084,0x200800200800200800200800200800284,0x2008002008002008002008002008004,0x80080080020080080080020080020084,0x800200000800080000800080000800080000800050800806,0x2008008008002005002008002008004,0x80020080020080020080020080020284,0x200805200800200800800800200800204,0x40051001000800040020001000800040020005,0x80020080020080020080020080020084,0x200800200800200800200800200500204,0x2000200002000080002000080000800080000800080006,0x80020080020080020080080080020084,0x800080000800080000800200000800080000800080002006,0x8008002008002008008008002008004,0x80080080028080020080020080028084,0x200800200800200520200800200800204,0x800080000800200800800080000800080000800080006,0x20001000800040020001000800040020001001c5,0x200800800800200800800800200800204,0x800080000800080000800080000800200000800080006,0x80020080020080020080080080020084,0x200500200800200500200800800800204,0x2008002008002008002008002008004,0x80020080020080020080020080080084,0x200800200800200800200800200800204,0x2028002008002008002008008008004,0x2000100080004002000100080004007000100085,0x800080000800200000800080000800050000800080000806,0x2008002008002008002008002008054,0x80000800200000800080000800080000800080002000086,0x200800200800200800800800200800204,0x2008002005202008002008002008004,0x80020080020080020080080080528084,0x200800200800200800200800200800204,0x2808002008002008002008002005004,0x80000800080000800200000800080000800080000800086,0x200800200800200800200800200800204,0x2008002008008008002008002008004,0x80020080020080020080020080020084,0x200800200800800800200800200800204,0x2008002008002008002008002008004,0x80020080020080080080020052020084,0x200800200800800800800800200800204,0x2008002008002008002008002008004,0x80000800080000800142000800080000800200000800086,0x200800200800200800200800200800204,0x2028002008002008002008002008004,0x80080080520080020080020080020084,0x200800800800200800200800200800204,0x40020001000800040020001000800040070005,0x80020080080080020080020080020084]
private def pack6 : Array ℕ := #[0x200800800800200800200800200800204,0x52008002008008008002008002008004,0x2000100080004001405100080004007000100085,0x200800200800200800200800200800204,0x2008002008002008002008008008004,0x80020080020080020080020080020084,0x800500200800200800200800200800204,0x2008002008002008002008002008004,0x80080080020080020080020280020084,0x200800200800200800200800800800204,0x800800080000800080000800080000800200000800080006,0x80020080020080020080020080020054,0x200800800800200800200800200800204,0x2008002008002008002005208008004,0x80020080020080020080020080080084,0x200800200800200800800800200800204,0x800080002000080000800880000800200002000080006,0x80020080020080020080028080020284,0x200800200800200800200800202800804,0x2008002008008008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x800080000800080000800200000800080000800080006,0x80020080020080080080080080080084,0x1001c000400200010008000400200010008000405,0x2008002005202008008008002008004,0x80000020000080000020002080000020098080000020000080000020000088,0x800080000800080000800200000800080002000080000806,0x2008002008002008002008002008004,0x80020080020080020080020080020284,0x200800200800200800200800200800204,0x8008002008002008002008002008004,0x980000020000080000020000080000020000080000020000080000020000088,0x200800200500200800200800200800204,0x2008002008008008002005002008004,0x80080080020080020080520080020084,0x200800200800200800800800200800204,0x2008002008002008002008002008004,0x80020080020050028080020080028084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080080084,0x2000008000002000008000002009808000002000008000008000008000002008,0x2008008008002008002808002808004,0x80020080020080028052020080020084,0x200800200800800800200800200800204,0x2008002008002008002028008008004,0x200000800080000800080000800080000800080000800086,0x10008000400700010008000400200010008000405,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x8008002008002008002008002008004,0x80020080020080020080020080020084,0x40008041000200040008000400200010008000405,0x2008002008002008002008002008004,0x80000800080000800200000800080000800080050800086,0x200800200800200800200800200800204,0x2008002008008008002008002008004,0x80020080020080080080020080020084,0x200800200800200800200800200800204,0x2008002008008008002058002008004,0x80000a00080000800080000800880000800080002000086,0x800800200800200800200800200800804,0x8008002008002008002008002008004,0x1400100080004002000100080004005100100085,0x200800200800200800200800200800204,0x2008002028002008002008002008004,0x80080080020080020080020080020084,0x800200000800080000800080000800080000800080000806,0x2008002008002008002005002008004,0x80020080020080028080080080020084,0x200800200800200800200800200800204,0x2008002008002008002008008008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x800080000800200000800080000800080050800080006,0x80000800080000800200000800080002000080000800086,0x200800200800200800200800200800204,0x800080000800200000800080000800080000800080006,0x80020080020080080080020080020084,0x200800200800200800200800800800204,0x2008002008002008008008002008004,0x80020080020080020080020280020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080080080080080020080020084,0x800080000800080002000080000800080000800200000806,0x800080000800080000800080000800200000800080006,0x80020080080080520080020080020084,0x200800200800200800280520200800204,0x2008002008008008002008002008004,0x2000100144004002000100080004802000100085,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x2005100080004002000100080004007000100085,0x200800200800200800200800200800204,0x800080000800200000800080002000080000800080056,0x80080080020052020080020080020084,0x800800200800200800200800200800204]
private def pack7 : Array ℕ := #[0x2008008008002008002008002008004,0x7000100080004002000100080004002000100085,0x200800200800200800200800200800204,0x8008002008002008002005002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080080080020080020084,0x200800200800200800800800200500804,0x8008002008002008002008002008004,0x80000020000080000020000080000020000080091080000080000020000088,0x8000800008000800008000802008002000008001c0000806,0x2008002008002005202008002008004,0x80020080020050020080080080020084,0x10008000400200010008000400200082008000405,0x2008002008002008002008002008004,0x80020080020280020080020080020084,0x200800200800200800200800800800204,0x2008002008002008008008008008004,0x200000800080000800080000800050800800080004c80086,0x200500200800200800200800200800204,0x2008002008002008002008002008004,0x2000100080010002000100080004005100100085,0x200800200800200800200520200800204,0x2008008008002008002008002008004,0x80020280028080028080020080020084,0x200800200800800800800800200800204,0x2008002008002008002008002008004,0x80020080020080020080080080020084,0x200800200800200800200500200800204,0x800200000800080000800080000800080000800080006,0x80020080020080020080020080020084,0x2000080000800080000800080200800080000800080000806,0x2008002005002008002008002008004,0x80020080020080020050020080020084,0x800800200800800800200800200800204,0x8008002008002008002008002008004,0x80000800080000800200002000880000800080000800086,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x2000008000002000008000002000008000002000098000002000008000002008,0x2008002008002008002808002008004,0x80000800080050800050800800080000800080000800206,0x200800800800200800200800200800204,0x2008002008002028008008002008004,0x80020080080080028080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80058080020080020080080080020084,0x200800200500200800200800200800804,0x800080000800200000800080000800080000800080006,0x80020052020080020080020080020084,0x800800200800200800200800200800204,0x2008002008002008002008002008004,0x80080080080080020080020080020084,0x202800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080080080020080020080020084,0x200800200800800800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020054,0x800200000800080000800080000800080002000080000886,0x2008002008002008002008008008004,0x80020080020280520080020080020084,0x200800200800200800200500200800804,0x2008008008002008002008002008004,0x200000800080000800080000800080000800080000800086,0x200800200800200800200800200800804,0x2008002008002008002008002008004,0x80000020098080000020000080000020000080000020000080000020000088,0x800800200800200800200800200800204,0x2008002008002008008008002008004,0x80020080020052020080020080020084,0x2000008000002000589000002000008000008000008000008000008000002008,0x2028002008002008052008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008008008002005004,0x80028080020080020080020080020084,0x200800200800200800200800200800204,0x2008008008008008002008002008004,0x80020080020080020080080080020084,0x10008000400200010008001000600010008000405,0x2008002008002008002008002008004,0x800008000800008000800008001c0000800880000800206,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800800800200800200800204,0x2008008008002008002008002008004,0x52080080020280020080020080020084,0x200800200500800800200800200800204,0x2008002008002008002008002008004,0x80020080080080020080020080020084,0x800080000800080000800200000800080000800080050806,0x2008002008002008002008002008004,0x80520080020080020080020080020054,0x200800200800200800200800200800204,0x8008008008002008002005002008004]
private def pack8 : Array ℕ := #[0x80020080028080020080020080020084,0x10008001000200010008000400200010008002e85,0x2008002008002008002008002808004,0x80020080020080020080020080020084,0x800800200800200800200800200800204,0x800080000800080000800080000800200000800080006,0x50800800080000800080000800200000800080000800086,0x200800200800800800200800200800204,0x2008002008002008002008002008004,0x80000800080000800080000800080000800200002000086,0x98000008000002000008000002000008000002000008000002000008000002008,0x2008002005202008002008002008004,0x80020080020080080080020080020084,0x200800200800200800800800500800204,0x2008002008002008002008002008004,0x80000800080000800080000800080000800080000800206,0x200800200800200800200800200800204,0x2008002008002008008008002008004,0x80020080520080020080080080020084,0x200800200800200800200800200800204,0x2008002008002008002008008008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008008008002008002008002008004,0x280020080020080020050020080020084,0x800800200800200800200800200800204,0x2008002008002008002008002008004,0x80020052080080080080020080020084,0x800080000800200000800080000800080000800080000806,0x2008002008002008008008002008004,0x2000100080004007000100080004002000100085,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200805200800200800200800284,0x40020001000800040020001001c00040020005,0x80020080080080020080020080080084,0x200800200800200800200800200800204,0x800080000800080002000080000800080000800200006,0x80000800080000800080000800080000800200000800086,0x200800200800200800200800200800804,0x800080000800080000880080000800080000800080206,0x80020080020080020080020080020084,0x200800200800800800200800200800204,0x800000800000200980800000200000800000200000800000200000800008,0x80080280020080020080020080080084,0x8000000800000008000002000000008000000800000d9400000080000000800000080000000800a,0x2008008008002008002008002008004,0x80020280020080020080020080020084,0x800080000800200000800080000800080000800080000806,0x2008002008002008008008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200805204,0x2008002008052008002008002008004,0x80028080520080020080020080020084,0x200800200800200800200800200800804,0x8008002008002008002008008005004,0x80002000080000800080000800080000a00080000800086,0x800080002000080000800080000800200000800080000806,0x2008002008002008002008002008004,0x80020080020080020050020080020084,0x200800200800200800800800280520204,0x2008008008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800800800204,0x2028002008002008002008002008004,0x80020080020080020080020080080084,0x200800200800200800200800200800204,0x800200000800080000800080000800080000800080006,0x80000800200000800080000800080000800080002000086,0x200800200800200800200800200800204,0x800080000800080000800200000800080000800080056,0x140200800080000800080000800080000800080000800086,0x200800200800200800800800280800804,0x2008002008052008002008002008004,0x80020080020080020080080080020084,0x10008003000200040008000400200010008000405,0x2008002008002008002008002008004,0x20001000800040020001001c0004002000100085,0x800200800800080000800080000800080000800880000806,0x202008002008002008002008002008004,0x52020080020080080080020080020054,0x200800200800800800200800200800204,0x2008002008002008002008002008004,0x80020080020080080080020080020084,0x200800200800200800800800200800204,0x2008002008002008002008002008004,0x80020050020080020058020080020084,0x200800200800200800200800280800204,0x2008052008002008002008002008004,0x80020080020080020080020080020084,0x200800800800200800200800200520204,0x2008002008002005202008002005004,0x80000800080002000080000800200000800080000800086,0x200800200800200800200805200800204,0x2008008008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x800050800800080000800080000800200000800080006,0x280020080020080020080020080020084]
private def pack9 : Array ℕ := #[0x800800200800200800200800200800204,0x800080000800080000800200000800080000800050006,0x80080080020080020080020080020084,0x800200000800080000800080000800080000800080000806,0x2008002008002008002008008008004,0x80020080020080020080020080020084,0x10008003000200010005100400200510008000405,0x2008002008002008002008002008004,0x80020080020080080080080080080084,0x200800200800200800200800200800284,0x800050800800080000800080000800080002000200006,0x80020080080080020080020080020084,0x200800200800200800200800200800804,0x2008002008002008002008002008004,0x80020080020080080080020080020084,0x200800200800200800200520200800204,0x2008002008002008002008008008004,0x80020080020080020080020080020084,0x200800800800200800800800800800204,0x800080000800080000800200002000080000800080006,0x80020080020080020080020080020084,0x200800200800200800800800800800204,0x2008002008002008002008008008004,0x80020050028080020080020080020084,0x200800200800200800200800202800204,0x800080000800200000800080000800080000800080006,0x80080080020080020080020080020084,0x200800200800200800200800200805204,0x2008002008008008002008002008004,0x80020080020080020080020080020084,0x200500800800200800800800200800204,0x2008002008002008002008002008004,0x2000100080004002000100480004002000c00085,0x800080000800080000801480000800880000800200000806,0x2005202008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200520204,0x2008008008002008002008008008004,0x80020080020080020080020080020084,0x8000008000002000008000098000008000002000008000002000008000002008,0x200000800000208002000000200000800000200000800000800008900008,0x80000800200000800080000800080000800080002000086,0x200800200800200800280800200800204,0x200980800000200000800000200000800000200000800000200000800008,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x8008002008002008002008002008004,0x80000800080000800200000800080000800080000800086,0x200800800800200800200800200800204,0x2008002008008008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200500204,0x2008002008002008002008002008004,0x80020080028080080080020080020084,0x200800200800200800200800202800204,0x2008002008002005002008002008004,0x80020080020080020080080080080084,0x800800200800200800200800200800804,0x800080000880080000800080000800080000800200006,0x2000ba0080004002000100080004002000100085,0x200800200800800805280800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x800080002000080000800080000800080000a00080000806,0x800200000800080000800080000800080002000080006,0x200000800080000800080000800080002000080000800086,0x200800200800200800200800200800204,0x2008002008002008002008008005004,0x80020080020080020080020080020084,0x200800200800200520200800200800204,0x2008002008002008002008002008004,0x80080080080080020080020080020084,0x200800200800200800200800800800204,0x200000800050200000800000200009800000200000800000200000800008,0x2000100080004002000c00080004002000100085,0x200800200800200800800800200800204,0x2008002008002008008008008008004,0x200000010000008000000400007cd1a000100000080000004000002000000100000089,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800800800200805200800204,0x2005002008008008002008002008004,0x80020080080080020080020080020084,0x200800200800200800200800200800204,0x2008002008008008002008002008004,0x80020080020080080080020080020084,0x200800200800202800200520200500204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200520200800204,0x202008002008002008002008002008004,0x200002000080000800080000800080000800080000800056,0x200800200800200805200800200800204,0x8008008008002008002008002008004,0x80020080020080020080020080020084,0x800080000800080000880200000800080000800080000806,0x2008002008002008002008002008004,0x80080080020080020080020080020084,0x200800200800200800200800200800204]
private def pack10 : Array ℕ := #[0x2008002008002008002008002008004,0x80000800200000800080000800080000800080000800086,0x200800200800200800200800200800804,0x8008002008008008008008002008004,0x80020080020080020080020080020084,0x4000800040020001000800040020004001c000405,0x2008002008002008002008002008004,0x280020080020080020080020080020084,0x800080000800080000800080000800a00000800080000806,0x202008002008002008002008008008004,0x80080080020080020080020080020054,0x10008000400200010008000400201040008000405,0x800080002000080000800080050800200000800080006,0x80020052020080020080020080080084,0x800080000800080200800050000800880000800080000806,0x2008002008002808002008008008004,0x80020080020080020080020080020084,0x200800200800800800280800200800204,0x2005002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800800800200800204,0x2008002008008008002008002008004,0x80020080028080020080080080080084,0x200800200520200800202800200800204,0x2008002008002008002058002008004,0x80020080020080020080020080020084,0x200800200800200500200800200800204,0x8008002008002008002008002008004,0x80000800080000800080000800080000800200000800086,0x200800200800800800200800200800204,0x800080000800080000800080000800200000800080006,0x80080080020080080080020080020084,0x200800200800200800200800200800204,0x800080000800200000800080000800080000800080006,0x80020080020080020080020080020084,0x200800200800200805200800800800804,0x800200000800080000800080000800080000800080006,0x80020080020052020080020080020084,0x200800800520200800200800200800204,0x2e8020001000800040020001000800040020005,0x80020080080080020080080080020084,0x200800202800200800200800200800204,0x2008002008002008002008002008004,0x80000020800080000020000080000020000080000020000080000020098088,0x200800200800200520200800800800204,0x2008002008002008002008002008004,0x80020080020080020080020050020084,0x800800200800200800200800200800204,0x2008002008002008002008002008004,0x80080050020080020080020080020084,0x200800280800800500200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008008008002008002008004,0x200000800080000800080000800080000800080000800086,0x200800200800200800800800800800204,0x2008002005002008002008008008004,0x80020080020080020080020080020084,0x800200002000080000880080000800080000800080002006,0x2008002008002008002008002008004,0x80020080020080520080080080020084,0x800800200800202800200805200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800280800200800200800200800204,0x800000800000800000500000200002000009800000800000200000800008,0x80020080020080020080020080020084,0x800080050800080000800200000800080002000080000806,0x2008002058002008002008002008004,0x80020080020080020080020080020084,0x200800200800280800200800200800204,0x52008002008002008002008002808004,0x80020080020080020080080080020084,0x200800200800200800200800200800204,0x2008002008008008002008002008004,0x80000800080000800080000800080000800080000800206,0x200520200800200800800800800800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800800800200800200800200800204,0x2008002008002008002005002008004,0x80020080080080020080020050020084,0x800080000800080000800080000800200000800080000806,0x2005008008002008002008002008004,0x80020080080080020080020080020084,0x200800200800800800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x10008001000201040005100400200010008000405,0x2008002008002008002008002028004,0x80000800080000800200000800080000800880000800086,0x200800200805200800200800200800204,0x8008002008002008008008002008004,0x80020080020080020080020080020084,0x802800800800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200520800800800800200800204,0x2000080000800080000800200000800080000800080006]
private def pack11 : Array ℕ := #[0x80000800080000800080000800080000800200000800086,0x800080050800080000800080000800200000800080000806,0x2008002008002008002008002008004,0x80020080020080020080020080080084,0xba008000400200010008000400200010008000405,0x2008052008002008002008008008004,0x200002000080000800080000800080000800080000800086,0x200800200800200800200800200800204,0x2008002008002008008008002008004,0x80000800050000800200000800080000800052000800086,0x800080000800080000800080000800080000800200002006,0x2008002008002008002008002005004,0x80020080020080020080080080020084,0x800200000800080000800080000800080000800080000806,0x2008002008002008008008008008004,0x80020080020080020080020080020084,0x200800202800200800280800200800204,0x2008002008002808002008002008004,0x80020080080080020080020080020084,0x200800200800200800800800200800204,0x800080000800200000800080002000080000800080006,0x80020080020080080080020050020084,0x200800200800802800280800200800204,0x800080000800200000800080002000200000800080206,0x80020080020080020080020080020084,0x200520280800200800200800200800204,0x2008002008002008002008002008004,0x80020050020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008052008004,0x80020080080080020080080080080084,0x800200000800080000800080000800080000800080002006,0x2008002008008008002008002005204,0x80020080020080020080020080020084,0x2000080000800200000800080000800080000800080000806,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80080080020080020080020080028084,0x200800200800200800200800200800204,0x2008008008002008008005002008004,0x80020050020080020080020280020084,0x10008014400600010008000400200010008000405,0x2008002008002008002008002008004,0x80020080020050020080080080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800804,0x800000800000200002000000200000800000200000800000200980800008,0x80020080020080020080020080020084,0x200580200800200800200800200800204,0x2008008008002008002008002028004,0x200000800080000800080000800200000800080000800086,0x200800200800200800800800200800204,0x2008002008002005002008002008004,0x80020080080080020080080080020084,0x800520280800200800200800800800204,0x2008002008002008002008002808004,0x80020080020080020080020080080084,0x800800800800200800200800200800204,0x2008002008002008002008002008004,0x80000800080000800200000800080000800080000800086,0x800080000800080000800080000800200000800080002006,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x800800200800200800800800200800204,0x200800080000800080000800080000800080000800080006,0x80000800080000800080000800080002000080050800206,0x202800200800200800800800200805204,0x2008002008002008002008002008004,0x50020080020080020080020080520084,0x200800200800200800200800200800204,0x2000200000800080000800080000800080000800080006,0x80020080020080020080020080020084,0x200800200800800800800800200800204,0x2008002008002008002005052008004,0x80020080020080080080020080020084,0x280800200800200800200800200800204,0x2008002008002008008008002008004,0x200000800080000800080000800080050800080000800086,0x200800200800200800200800200800204,0x2008002008008008002008002008004,0x80020080020080020080020050020084,0x200800800800200800200800200800204,0x800080002000200000800080000800050800800080006,0x2000100080410002000100080004002000100085,0x200800200520200800200800200800204,0x2008002008002008002008002008004,0x80020080080080020080020080020084,0x200805200800200800200800200800204,0x2008002008002008002008002008004,0x80020080080080080080020080020084,0x800800200800200800200800200800204,0x800080000800080000800080000880200800800080006,0x80080080020080020052020080020084,0x200500200800200800200800200800204,0x2008002008002008002008002008054,0x80020080020080020080020080080084]
private def pack12 : Array ℕ := #[0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800804,0x2008002005002008008028008008004,0x80020080020080020080020080020084,0x200800200800200800200800200800804,0x2008002008002005002008002005204,0x50020080020080020052020080020084,0x200800200800200800800800800800204,0x2008002008002008002008002008004,0x20001000800040020001001c0004002000100085,0x200800200800200800200800200800204,0x40020001000800040020009a00800040020005,0x80020080020080020080020080020084,0x200800200800200800200800800800204,0x802008002008002008002008002008004,0x2000100080004002000100080004002000100145,0x8000800008000800008002000008001c0000800080000806,0x2028002008002008002008002008004,0x80080080020080020080020080020084,0x200800802800200800200800200800204,0x2008002008008008002008002005204,0x80020080020080020080020080020084,0x200800200800200800800800200800204,0x200000800000800000800000200000800000800000800000800980800008,0x200000800080000800080000800080000800080000800086,0x200800200800200800800800200800204,0x2008002008002008002008002008054,0x80000800080000800080000800080000800080000800206,0x200800200800200800200800200800204,0x4002000ba00800040020051000800040020005,0x80020080020080020050020080080084,0x2000008000002000008000008000008000002000098000002000008000002008,0x2008002008002008002008002808004,0x80020080020080020080020080020084,0x8000800008001c0000800080000800200000800080002006,0x2008002008002008002008002008004,0x80020080020080020080028080080084,0x200800200800200800200800200520204,0x268020001000500040014401000800040020005,0x80000800080000800080000800880000800080000800206,0x10008003000200010008000400200010008000405,0x2008002008002008002008002008004,0x80020080020080080080020080020084,0x800080000800080000800200800800080000800080000806,0x2008002008002008002008002008004,0x80020280020080080080020080020084,0x2009808000002000008000002000008000008000008000002000008000002008,0x800080000800080000800080000800080000800200006,0x80000800080000800080000800080000800080002000206,0x800800200800200800200800200800204,0x800080000800080000800080000800080200800080006,0x80020080020080020080020080020084,0x200800800800800800200800800800204,0x2008002008002008002008002008004,0x80080080020080020080020080020084,0x280800200800200800200800200800804,0x800080002000200000800880000800080002000080006,0x80020080020080020080080080020084,0x200800200800200800200800200800204,0x2008002008002005002005208008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002808002008008008004,0x80020080020080080080020080020054,0x200800200800200800200800200800204,0x2008002008002008008008002008004,0x80020080020080080080520080080084,0x800080000800200000800080000800050000800080000806,0x2008002008002008002008002008004,0x80020080020080020080020080028084,0x200800200800200800200800280800204,0x2008002008002008002008002008004,0x80020080080080080080020080020084,0x200800200800200800200800200800204,0x800080000800080002000080000800880000800200006,0x80020080020080020080020080020084,0x800080000800200000800080002000080000800080000806,0x2008002008002008002008002008004,0x80000800080002000080000800080000800200000800086,0x200800200800200800200800200800204,0x2008002008052008002008002008004,0x80080080020080020080020080020084,0x200520200800200800200800200800204,0x2008008008008008002808002008004,0x80080080020080020080020080020084,0x800080000800080000800080000800200000800050800806,0x40020001000800040020001001c00040120055,0x80020080020080020080020080020084,0x200800800800200800200800200800204,0x2008002005202008002008002008004,0x80020080020080020080020080020084,0x200800200800205800200800200800804,0x8008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200500200800200800200800204]
private def pack13 : Array ℕ := #[0x2008002008002008002008008008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008008008002008002008004,0x80000800080000800080000800200000800080002000056,0x200800200800200800200800800800204,0x2008002008002008052008002008004,0x80020080020052020080020080080084,0x10008000400200010008001000700010008000405,0x2008002008002008002008002008004,0x80020080020080080080020080020084,0x200800200800200800200800200800204,0x2008002028008008002008002008004,0x80000800080000800080000800200000800080002000086,0x200800200800200800800800200800204,0x2008002008002005202008002008004,0x80020080020080080080080080028084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x202800200800200800800800800800204,0x2008002808002008002008002008004,0x80002000080000800080000800080000800080000800206,0x200800200800800800200800200800204,0x2008002008002008002008002008004,0x80020080020080080080020080020084,0x800200002000080200800080000800080000800080000806,0x800200050800080000800080000800080000800080006,0x80020080020080020080020080080084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020050020080020084,0x200800800800200800200800200800204,0x2008002008002028002008002008004,0x80020080080080020080020080020084,0x200800200500200800200800800800204,0x2008002008002008002008002808004,0x80000800080000800080000880200000800080000800086,0x200800200800200800200800200800204,0x2008052008002008008008008008004,0x80020080020280020080020080020084,0x800500200800200800200800200800204,0x2008002008002808002008002008004,0x80080080020080020080020080020084,0x200800200800200800200800200800204,0x40020001000800100020001000800040070005,0x20001001c0004002000100080004002000100085,0x200800200800200800200800200800204,0x2005202008002008002008002008004,0x80020080020080080080020080020084,0x200800200800200800200800200500204,0x8008002008002008002008008008004,0x52020080020080020080020080080084,0x800080002000200000800080000800080000800080002006,0x2008002028002008002008002005204,0x80020080020080020080020080080084,0x200800200800200800200800200800204,0x8008002008002008008008002808004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x800080000800080050800200002000080000800080006,0x80080080020080020080020080020284,0x200800200800200800200800800800204,0x2008002008002008002008002005004,0x80020080020080020080020080020084,0x200800200800200800200800200500204,0x2028002008002008002008002008004,0x80020080020080020050020080020084,0x200800200800200800200800800800204,0x40020001000510300020001000800040020005,0x80020080020080520080020080020084,0x200800200800200800800800200800204,0x800080000800080000800080000800080002000200006,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2808002008002008002008002008004,0x80000800200000800080000800080000800080000800086,0x200800200800200800200800200800204,0x2008008028002008002008002008004,0x80020080020080020080020080020084,0x100080004002000c0008000400200010008000405,0x200000800000200000800000200000800000200000800000200028900008,0x80020080020080020080020080028084,0x800080002000080002000080000800200000800080000806,0x2008002008008008002008002008004,0x80000800080000800080000800200000800080000800086,0x200800200800200800200800200800204,0x8008002028002008002008002005204,0x80020080020080020080020080020084,0x200800800800200800200800200800204,0x8008002008002008002028052008004,0x80000800080000800200000800080000800080000800086,0x200800200800202800200800200800204,0x52008002008002008002008008008004,0x80080050020080020080020080020084,0x200800800800200800200800200800204,0x2008002808002008002008002008004,0x80020080020080020080020080080084,0x8000008000002000098000002000008000002000008000002000008000002008,0x2008002008002008002008002005004]
private def pack14 : Array ℕ := #[0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x202008008008002008002008002008004,0x80020080020080020080080080020054,0x200800200800200800200800200800204,0x2005202008002028002008008008004,0x80020052020280020080080080020084,0x200800200800800800200800800800204,0x800080000800080000800200000800080006000080006,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080028080020080020084,0x200800200800800800200800200800204,0x800080050800080000800200000800050000800080006,0x80000020000080000020000080000980000080000080000080000020000088,0x200800200800200805200800200800204,0x800080000800080002000080002000080000800200006,0x80028080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002028004,0x80020080020080020080020080020284,0x200800200800200800200800200800204,0x2005202008002008002008002008004,0x80020080080080020080020080020084,0x2000080000800200000800080000800080000800080000806,0x2008002008008005002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x8008002008002008002008002008004,0x80020050020080020080020080028084,0x200800280800800800200800200800204,0x2808002008002008002008002008004,0x2010400080004002000400051004002000100085,0x200800200800200800200800200800204,0x200000800000800000800000200000800000200009800000200000800008,0x80020080028080020080080080020084,0x200800200800200800200800200800204,0x2008002008002008002005002008004,0x80000800a00000800080000800080000800080000800086,0x800080000800080000800080000800080002000200000806,0x800980800000200001c00000200000800000200000800000200000800008,0x80020080020080020080020080020084,0x200800200800200800200800200800804,0x8008002008002008002008002008004,0x80000800200000800080000800080000800080000800086,0x800800200800200800200800200800204,0x2008002008002008002008008008004,0x80000020000980000080000080000020000080000020000080005020000088,0x200800200800200800200800200800204,0x2808002008002008002008002008004,0x80020080020080020080020080020084,0x800800200800800800200800800800204,0x2008002008002008002008002008004,0x80020080020280020080020080080084,0x200800200800200800200800200800204,0x40020001000800300020001200800040020005,0x200000010000008000000400000200000010000008000000400007cd1a000100000089,0x800800200800200800200800200500204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800800800200800204,0x8008002008002005002008002008004,0x80020080020080020080080080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80000800080000800080000800080000800080000800206,0x200800200800200800200800200800204,0x52008002008002008002008002008004,0x80020080520080020080020080020084,0x200800200800800800200800200800204,0x40070001000800040014004000800040020005,0x80020080020080080080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080080280020084,0x200800200800200800200800200800204,0x40010000200000400008000308000200000400008000010000200007,0x80080080080080020080020080020054,0x200800800800200800200800200800204,0x800080000800080000800200000880080000800080006,0x80020080080080020080020080020084,0x2000008000002000008000002000008000002000008000002000089000002008,0x2008002008002008002008002008004,0x80020080020080020080528080020084,0x800080002000080002000080200800080000800080000806,0x800080000800080000800080000800200800800080006,0x52020080020080020080020080020084,0x800800200800200800200800200800204,0x40014001000800040060051000800040020005,0x80080080020080020080020080020084,0x200800200800280800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200500804,0x2008002008002008002008002008004,0x80020080020080020080020080020284,0x800800200800200800200800200800204,0x2008002008002008002008008008004,0x200000800080000800050000800080000800080000800086]
private def pack15 : Array ℕ := #[0x200800200800200800200800200800804,0x8008002008002008002008002008004,0x80020080020080020080520080020084,0x800080000800080000800200000800080000800080000806,0x2008008008002008008005202005004,0x52020080020080020080020080028084,0x200800800800200800200800200800204,0x40020001000800040070004000800040020005,0x80020080020080020080080080020084,0x200800200800200800200800800800204,0x2008002005208008008008002008004,0x80020052020080020052020080020084,0x800080000800080000800080000800080000800200000806,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x40020004000800300020001000800040020005,0x80020080020080020080020080020084,0x200800200800200800800800200800204,0x2008002008002008002028002008004,0x80020080080080020080020080020084,0x1000800040020001001c000400200010008000405,0x2005002008002008002008002008004,0x80020080020080020080020080520084,0x200800200800200800200800200800204,0x2005008008002008002008002008004,0x80020080020080020080020080020084,0x10008000400200040008000400200010008003005,0x2008002008002008008008002008054,0x80020080020080020280020080020084,0x800800200800200800200800200800204,0x2008002008002008002008002008004,0x80000800080000800080000800080000800200800800086,0x200800200800200800200800200800204,0x8008002008002008052008002008004,0x80000880080000800080000800080000800200000800086,0x200800800800200800200800200800204,0x2008002008002008002008002008004,0x280020080020080028080020080020084,0x200800200800200800800800200800204,0x2008002008002008002008002008004,0x50020080020080020080020080020084,0x200800200800200800200800800800804,0x800200000800200000800080002000080000800080006,0x80020080020080020080020080080084,0x800800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x200009800000800000800000200000800000200000800000200000800008,0x80000020000080000020000080005020002080000020098080000020000088,0x200800200800200800200800200800204,0x2008002008002008002008008008004,0x80020080080080020080080050020084,0x800080000800080000800080000800080000800200000806,0x2008008008002808002008008008004,0x20001000800040020051001c0004002000100085,0x200800200800200500200800200800204,0x2008002008002008002008002008004,0x80020080020080020080028080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80080080020080080080020080080084,0x10008000400200010008000400200010208000405,0x2008002008002008008028002008004,0x2000100080004005100100080004002000100085,0x800200000800080000800080000800080000800050002006,0x202008002008002008002008002008004,0x80050800080200800080000800080000800080000800056,0x200800800800200800200800200800204,0x2808002008002008002008002008004,0x80020080080080020080020080020084,0x200800200800200800800800200800204,0x8008008008008008002008002008004,0x80020080020080020080020080080084,0x800080000800080000800200000800080000800200000806,0x2008002008002008008008002028004,0x80028080020080020080520080020084,0x200500200800200800200800200800204,0x2008002008002008002008002008004,0x80080080020080020080020080020084,0x200800200800200800200800200800204,0x4002000c000800040020001000800040020005,0x80020080020280020080020080020084,0x200500800800200800200800200800204,0x800142000800080000800200800800080000800080006,0x80020080080080020052020080020084,0x200800200800200800200800200800204,0x2008008008052008002008002008004,0x80020080020080028080020050020084,0x200800200800280800200800200800804,0x8008002008002008002008002008004,0x80020080028080020080020052020084,0x200800200800200800200800200800204,0x8008002008002008002008002008004,0x80020080020080020080020080080084,0x200800200800200800200800200800804,0x800200000800080000800080000800080000800080006,0x80000800080000800200000800080000800080000800086,0x200800200800200800200800800800804]
private def pack16 : Array ℕ := #[0x2008002008002008002008002008004,0x80020080020080020080020080080084,0x200800200800200800200800200800204,0x800200000800080000800080000800080000800080006,0x80020080020080020280020080020084,0x800800200800800800800800200520204,0x2008002008002008002008002008004,0x80000800080000800080002000080000800200000800086,0x800080000800080000800080002000200000800080000806,0x2008002008002008002008002008004,0x80020080520080020080080080020084,0x1000800040020001001c001000200010008000405,0x2008002008002008002008008008004,0x80020080020080028080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020050020080020080020084,0x800080002000080002000200000800080000800080000806,0x2008002008002028002008002008004,0x80020052020080080080020080020084,0x200500200800200800200800200800204,0x2005008008002008002008002008004,0x80020080020080020080020080020084,0x10008000400600010008000400200010008000405,0x2008002008002008002008002008004,0x80000800080000800080000800080000800080000800206,0x200800800800200800200800200800204,0x2008002008002008002008002008004,0x52020080080080020080020080020084,0x200800200800200800200800200800204,0x800080000800080000800080000800200002000080006,0x80020080020080520080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080080084,0x800800200800200800200800200800284,0x2008002008002005002008002008004,0x80080280020080020080080080080084,0x800200000800080000800080000800080000800880000806,0x2008002008002008002008002008004,0x80000800080000800200802000080000800080000800086,0x200800200800800800200800200800204,0x800200000800080000800080000800080000800080056,0x80020080020080080080020080520084,0x200800200800200800800800200800204,0x8008002008002008002008008008004,0x80028080020080020080020080020084,0x200800200800200800200800200800804,0x40020001000800040020001001c00040020005,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x200000800000200001c00000200000800009700000800000200000800008,0x20004000800040014001000800040020001001c5,0x200800200800200800200800200800204,0x8008002808002008008008002008004,0x80200800080000800080000800080000800080000800086,0x200800800800200800200800800800204,0x2008002008002008002005002008004,0x80020080020280020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x200000800080000800080000800080000800080000800086,0x800080000800080000800200000800080000800080000806,0x2008002008008008002008008008004,0x80050800080000800080000800080000800080000800206,0x200800200800200800800520200800204,0x2008002008002008002008002008004,0x80020080028080020080020080080084,0x800800800800200800200520200805204,0x2008002008002005202008002008004,0x80000800080000800200000800080002000080000800086,0x200800200800200800200800200800204,0x2008008008002008002008002008004,0x52020080020080020080020080020084,0x200800200800800800200800200800204,0x8008002008008008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x50020280020080080080020080020084,0x200800280800200500200800200800204,0x8008002008002008002008002008004,0x80020080020080020080020080020084,0x200800800800200800200500200800204,0x802008002005202008002005002008004,0x80002000080050800080000800080002000200000800146,0x200800200800200800200800200800204,0x2008052008002008002008002008004,0x80020080020080020080080080020084,0x200800800800200800200800200800204,0x2008002008002008002008002008004,0x280020080020080020080020080080084,0x800800200800200800200800200800204,0x800080000800200000800080000800080000800080006,0x80020052020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800800800204,0x2808002008002008002008002008004]
private def pack17 : Array ℕ := #[0x200000800080002000080002000080002000080000800086,0x200800200800200800202800200800284,0x800080000800080000800080000800200002000080006,0x80020080020080020080020080020084,0x200800200800200800200520200800204,0x2008002008002008002008008008004,0x80000800080000800080000800080000800200000800086,0x200800202800200800200800200800204,0x2008002008008008002008002008004,0x2000100080004002000c00080004002000100085,0x800080000800080000800200000800080000800080000806,0x2008002005002008008008002005004,0x80080280020080080080020080020084,0x800800200800200800200800200800204,0x800080000800080000800080000800080000800200006,0x200000800080000800080000800080000800080000800086,0x2000008000002000098000002000008000002000008000002000008000002008,0x2008002028002008002008002008004,0x80020080080080020080020080020084,0x800080000800080000800080000800080000800200050806,0x8028002008008008002008002008004,0x280028080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80080080020080020080020080020084,0x800080000800080000800080000800200000800080000806,0x2008002008002008002008002008004,0x80080080020080020080020080020084,0x200800200800200800200800800520204,0x2008008008008008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800800800204,0x2008002008002008008008008008004,0x200000800080000800080000800080000800080000800086,0x200800200800200800200800580800204,0x2008002008002008002008008008004,0x80000020000080000020000080000020000080000020000200000970000088,0x2000008000002000008000002000008000002000208000002000098000008008,0x8008002008002008002008002008004,0x80520080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200520800800200500200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800802800204,0x2008002005008008002008002808004,0x52020080020080020080028080080084,0x200800200800200800200800200800204,0x2008002008008008002008002008004,0x80020080020080020080020080020084,0x800200000800080000800080000800080000800080000806,0x5e00080000800080000800080000800080000800080006,0x80020080020080020080020080080084,0x200800200800200800800805280800204,0x2008002008002008002008002008004,0x80002000080000800080000800080002000080000800206,0x200800200800200800200800200800204,0x2008002008002008002008002808004,0x20001000800040020001001c0004002000100085,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80080080020080020080020080020084,0x200800200800800800200500200800804,0x2000080000800200000880080000800080000800080056,0x280020080020080080080080080020084,0x800080000800080000a00080000800080050800080002006,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x800200000800080000800080000800080002000080000806,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800800800200800200805200800204,0x2008002008002008002008002008004,0x80020080080080020080020080020054,0x200800200800800800200800200800284,0x2008002808002008002008002008004,0x80000800080000800080000800080000800200000800086,0x200800200800200800200500200800204,0x2008002008008008002008002008004,0x80000800080000800080000800200000800080000800086,0x800800200800200800200520200800204,0x2005202008002008002008002008004,0x80080080020080020080020080020084,0x200800200800200800200800200800204,0x52008002008002008002008002008004,0x80020080020080020080020080020084,0x8000008000002000084000002000008000002000008000002000008000002008,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2e0020001000800040020001000800100020005,0x80020080020080020080020080020084,0x10008000400200010008000400200010008041005,0x2008008008008008002008002008004,0x80020080020080020080020080020084,0x800080000800080000800080000800200000800080000806,0x2008002008002008002008002008004,0x80020080520080080080080080020084]
private def pack18 : Array ℕ := #[0x800080200800080000800080000800880000800080000806,0x2008002008002008008008008008004,0x80020080020080020080020080020054,0x200800200800200525200800800520204,0x2008002008002008008008002008004,0x80020080020080020080020080020084,0x200800200500200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x800800200800200800280800200800204,0x2008002008008008002008002008004,0x80020080080080020080020080020054,0x200800200800200800800800200800204,0x2008002008052008002008002008004,0x50000800080000800200000800080000800080000800086,0x200800200800800800200800200800204,0x2058002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008008008002008002008002008004,0x80000800080000800200000800200000800080000800086,0x800800200800800800200800202800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800800800200800204,0x802000080000800080000800080000800080000800200006,0x80020080020080080080020080020054,0x1000800040020001000807e680200040005100405,0x8008002008002008002008002008004,0x80000800080000800080000800080000800080000800206,0x200800800800200800200800280800204,0x2005002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800280800200800204,0x2008002008002008008008002008004,0x80020080020080020080020080020084,0x200800200800202520200800200800204,0x52008002008002008002008002008004,0x80020080020080020050080050080084,0x800800200800200800200800200800204,0x2008002005008005002008002008004,0x80020080020080020080020080020084,0x800080000800200000800880000800080000800080000806,0x2008002008002008002008002008004,0x80020080080080020080020080020084,0x1001c000400200010008000400200010008000405,0x2008002008002008002008002008004,0x80020080020080020080080080020084,0x200800200800800800200805200800204,0x2008008008002008002008008008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x800080002000080000800080000800080000800200006,0x80020080020080020080080080028084,0x200800200800202800200800200800204,0x2008002008002008002008002008004,0x80020080020080080080020080020084,0x800080000800080000800200000800050800800080002006,0x8008002008002008008008002008004,0x80020080020080020080020080080084,0x2000080000800200000800080000800080000800080000806,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800280800200800200800204,0x2008002008002008002008008008004,0x80020080080080020080520080020084,0x200800200800200805200800200800204,0x2008002008008008008008002008004,0x20001001c0004002000100080004002000100085,0x200800200800200800200800200800204,0x2008002008002008002008002005004,0x80000800200000800080000800080002000080000800086,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80000980000080005020000080000020000050000020000080000020000088,0x200800200800200800202800200800204,0x2008008008002008002008002008004,0x280020080020080020080020080020084,0x200800200800202800200800800800204,0x800080006000880000800080000800200000800080006,0x80020080020080020080020080020084,0x280800200805200800200800200805204,0x202008002008002008002008002008004,0x80000800200002000080000800080000800080000800056,0x200800200800200800280800200800804,0x9800000800000200000800000200000800000200000800000200000800008,0x80020080020080020080020080520084,0x200800200800200800200800200800204,0x800080000800080000800080000800200000800080006,0x80020080020080020080020080020084,0x200800800520800800200800200800804,0x2008002008002008002008002008004,0x80000800080000800080000800200000800080000800086,0x800800200800200800200800800800204,0x2008002008002008002008002008004,0x80020080020080020080020080080084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080080080020080020080020084,0x200800200800200800200800200800204]
private def pack19 : Array ℕ := #[0x2008002008002008002008002008004,0x80080050020080020080020080020084,0x10008000400144010008041000200010008000405,0x2008002008008008002008002008004,0x80028080020080020080080080020084,0x280800200800200800200800200800204,0x800000800000200000800000200000800009800000800000200000500008,0x80020080020080020080020080080084,0x200800202800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800800520200800200800204,0x2008008008002008002008002008004,0x80000800080000800200002000080000800080000800086,0x200800200800200800200800200800204,0x880080000800080000800200000800080000800080006,0x80020080080080020080020080020284,0x200800280800205800200800200800204,0x2008002008002008002008002008004,0x80020052020080020080020280020084,0x200800800800200800200800200800204,0x2008002008002008002008002008004,0x200000800080002000080002000080002000080000800086,0x200800200800200800200800200800204,0x800080000800080000800080000800080000800200006,0x80020080020080020080020080080084,0x200800200800280800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x800800200800202800200800200800804,0x2008002008002008002008002008004,0x80080080020080020080020080020084,0x200800200800280520200800200800204,0x800080000800080000800200000800080000800080006,0x80020080020080020080020080020084,0x200805202800200800800800200800204,0x2008002008002008002008002008004,0x80020050020080020080020080020084,0x200520200800280800200800200800204,0x800080000800080000800080002000080002000200006,0x80000800080000800080000800200000800080000800086,0x200800200800200800200800200800804,0x2008002008002008002008002008004,0x80020080020080020080020080520084,0x800520200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x800080002000080000800080000800080000800200000806,0x8008002008002008008008002008004,0x80020080020080020080020080020084,0x200800200800200800200800800800204,0x2008008008002008002008002008004,0x80020080020080080080028080020084,0x800800200800200800200800200800204,0x2008002008002008002008008008004,0x200000800200000800080000800080000800080000800086,0x200800200805200800200800200500204,0x8008002008008008052008002008004,0x80080080020080520080020080080084,0x200800200800200800800800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x205800200800200800200800200800804,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x1000800040052e510008000400200010005000405,0x2008008008002008002005002008004,0x80020080020080020080020080020084,0x200800200800800800200800200800204,0x800080000800080000800200000800080000800080006,0x80020080020080080080020080020084,0x280800200800200800200800200800204,0x2008002005002008002008002008004,0x80020080020080020080020080020054,0x200800200800200800800800200800204,0x2000080000800080000800080000800080000800200006,0x80020080020080020080020080020084,0x800080002000080000800080000800080000800200000806,0x800200000800080000800080000800080000800080006,0x80020080020080020080020080020084,0x200800800800200800200800200800204,0x800080000800080000800080000800200000800080006,0x80020080020080020080020052020084,0x200800202520200800200800200800204,0x2005208008002008002008002008004,0x8000008000008000008000008000008000008008e020000080000080000088,0x800800200800200800200800200800204,0x200000800000200002000000200008900000200000800000200000800008,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x8008002008002008002008002008054,0x80020080020080020080020080020084,0x200800280800200800200800200800204,0x2008002008002008002008008008004,0x80020080020080020080080080020084,0x200500200800200800200800200800204,0x2005002008002008002008008008004,0x80080080020080020080020080080084,0x200800200800200800200800200800204,0x2808002008002008002008002005204]
private def pack20 : Array ℕ := #[0x80020080020080020080020080020084,0x200520200800200800200800200500204,0x2008008008002008002008002008004,0x80020080020080080080020080020084,0x200800200800200800200800200800204,0x2008002008002008008008002008004,0x80020080020080020080020080020084,0x200800200800200800800800200800284,0x2008002008002008002008008008004,0x80020080020080020080020080020084,0x800080050800080000800200000800080000800080000806,0x2008002008002008002008002008004,0x80000020000080000980000080000020000080000020000080000020000058,0x200800200800200800200800200800204,0x2008002008008008002008002008004,0x80080080020080020080020280020084,0x200800200800200800200800200800204,0x2008002008005808008008002028004,0x280020080020080020080020080020084,0x800050802000080000800080000800080000800200000806,0x2008002008002008002008002008004,0x80080080020080020080020080020084,0x200800200800200800200800200800204,0x800080002000200000800080000800080000800080006,0x80020080020080020080080080020084,0x200800200800200800200800200800204,0x400200010008000400200010008002e8020005,0x80020080020080020080020080020084,0x200800200800200500200800200800204,0x800080000800080000800200000800080000800080006,0x58020080020080020080020080080084,0x800080000880080000800080000800200000800080002006,0x8005052008002008002008002008004,0x80028080020080020080020080080084,0x800d94080000000800000080000000800000080000000800000080000000800000080000000800a,0x8008002008002008002008002008004,0x80020080020080020080020280020084,0x202800200800200800202800200800204,0x2008002008008008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800800800204,0x800200000800200000800080000800080000800080006,0x80000800080000800080002000080000800200002000086,0x200800200800200800200800200800204,0x800080000800080000800080000800080200800080006,0x80020080020080020080020080020084,0x2080008000002000008000002000008000002009808000002000008000002008,0x2008002008002008002008002008004,0x200002000080000800080000800080000800080002000886,0x200800200800200800800800800800804,0x800200000800080000800080000800080000800880006,0x80020080080080028080080080020084,0x200800800800200800200800200800204,0x2008002008002008002005202008004,0x80020080020080020280020080020084,0x200800800800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800800800200800200800204,0xa00080000800080000800080000800080000800080006,0x80000800080000800080002000080000800200000800086,0x200800200800200500200800800800204,0x2008002008002808002008002008004,0x80020080028080020080020080020084,0x200805200800200500200800200800204,0x2008002008002008002008008008054,0x80020080020080020080020080020084,0x200800800800200800200800200800204,0x2008002008002008002008002008004,0x80020080080080020080020080020084,0x200800200800200800800800200800204,0x800080000800080002000200000800880000800080006,0x80020080020080020080020080020084,0x800200000800080000800080000800080000800080000806,0x2008002008002008002008002005204,0x80020080020080080080020080020084,0x800800200520200800200800200800204,0x2008002008002008002008002008004,0x80080080020080020080020080020084,0x200800200800200800200800200800204,0x8008008008002008002808002008004,0x80020080020080020052020080020084,0x800080000800080000800200000800080000800080000806,0x8008002008002008002008008008004,0x80020080020080520080020080020084,0x800080000800080000800200000800080000800080000806,0x2008002008002008052008008008004,0x80080080020080020080020080020084,0x200800200800200800200800200800804,0x2008002008002008002008002008004,0x80020080020080020080020080020054,0x10005000400200010008000400700010008000405,0x2008002008008008002008002028004,0x80020080020080020080020080020084,0x200800200800200800200800800800204,0x2008002008002008008008002008004,0x80000800200000800080000800880000800050000800206,0x200800200805200800200800800800804,0x2008002008002008052008008008004,0x80020080020080020080020080020084]
private def pack21 : Array ℕ := #[0x200800200800200800200800200800204,0x8008002008002008002008002805204,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008008008002008002008004,0x80000880080000800200000800080000800080000800086,0x200800200800800800800800200800204,0x2008002028002005202008002008004,0x80020080020080020080020080020084,0x200800200800200800800800200800204,0x2008002008008008002008002008004,0x80020080020080020080020080020084,0x10008000400200080008001000200012008000405,0x2008008008002008002008002008004,0x2000100080004002000100480004007000100085,0x200800200800800800200800200805204,0x2000080000800200002000080000800080050800080006,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008052008004,0x80080080020080020080020080020084,0x200800200800200800200800200800204,0x8008002008002008002008002008004,0x80020052020050020080020080020084,0x200800800800200800200800200800204,0x2008002008002028002008002008004,0x80020080020080020080020080020084,0x1001c000400200010008000400200010008000405,0x800080000800080000800080000800200800800080006,0x80020080020080020080080080020084,0x280800200800200800200500200800204,0x2008002008002008002008002008004,0x80020080020080020080020080080084,0x2000200000800080000800080000800080002000080000806,0x2008002008002808002008002028004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x800080000800080000800080000800200000800080006,0x80020080020080020080020050020084,0x800080000800200002000080000800080000800080000806,0x2008002008002008002008002008004,0x80020080020080080052080080020084,0x200800200800200520200800200800204,0x2008002008008008002008008008004,0x80020080020080020080080080080084,0x800200000800080000800080000800080000800080000806,0x2008002008002008002028002008004,0x80020080020080020080080080020084,0x200800200800200800200800200800804,0x2008002008002008002008002008004,0x800020000800008800800060000800008002000008001c6,0x800800200800200800200800200800204,0x2008002008052008008028002008004,0x2000100080004007000100080004002000100085,0x200800200800200800200800200800204,0x8008002008002008002805008008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80000800080002000050000800080000800080000800206,0x200800200800200800200800200800204,0x2008002005208008002008002008004,0x80020080020080020050080080020084,0x200800200800200800200520200500204,0x2008002008002008002008002008054,0x80020080020080020080020080020084,0x202800200800200800200800800800204,0x2008002008002008002008002008004,0x200002000080000800080000800080000800080000800086,0x200800200800200800200800200800204,0x2008008008002008002008002008004,0x80020080020080520080020080020084,0x200800200800200800200800200800204,0x2008002008002008052008002008004,0x80020080080080020080020080020084,0x800800800800200800200800200800204,0x2008002008002008002008002008004,0x80000800080000800200000800080000800080000800086,0x200800200800800800200800200800804,0x8008002028002008002008002008004,0x80020080020052020080020080020084,0x200800200800200800200800200800204,0x2008002008052005202008002008004,0x80020080520080020080020080020084,0x2000080000800080000800080000800200000800080000806,0x2008002008002008002008002008004,0x50020080020080020080020080020084,0x1000500040020001000800040020004001c000405,0x8008002808002008002008002008004,0x80020080020080020080020080080084,0x200800200800200800200800200800204,0x2008002008002008002005002008004,0x2000100080004002000100080004007000100085,0x1005c000400200040008000400200010008000405,0x2008002008002008002008002008004,0x80020052020080020080020080020284,0x200800200800200800800800800800204,0x2008002008002008008008002005004,0x80020080020080020080080080020084,0x200800200800200800200800200800204]
private def pack22 : Array ℕ := #[0x800080000800200000800880000800050800800080006,0x80020080080080020080080080080084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80000800080000800080000800200000800080000800086,0x200800200800800800200800200800204,0x2008052008002028002008002008004,0x80020080080080080080020080020084,0x200800200800200800200800200800204,0x800080000800080000880080000800200000800080006,0x80020080020080020080020080020084,0x800080000800200002000080000800080000800080000806,0x800080000800200800800080000800080000800080006,0x80000020000080000020098080000020000080000020000080000020000088,0x200800800800200800200800200800284,0x2005202008002008002008002008004,0x80080080080080020080020080020084,0x200800200800200800200800200800804,0x2008002005002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800280800804,0x2008002008002008052808002008004,0x50020080020080020080020080020084,0x800800200800200800200800200800204,0x2008002008002008002008008008004,0x80080080020080020080020080020084,0x800080002000200000800080000800080000800080000806,0x800080200800080050800080000800080000800080006,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008008008002808004,0x80020080020080020080020080020084,0x800080000800080000800080000800200000800080000806,0x2028002008002008002028008008004,0x80020080020080020080080080020084,0x200800200800200800200800200800804,0x2008002005202008002008002008004,0x80020080020080020080080080020084,0x200800200800200800200800200800204,0x2008002008002008008008008008004,0x200000800080000800080000800080000800080000800086,0x200800200800200800200800200800204,0xa00080002000080000800080002000080000800080006,0x80020080020080020080020080020084,0x200800200800200800200800800800204,0x2008002008002008002008002008004,0x80020080080080080080020080080084,0x200800200800800800200800200800204,0x200000800000200000800000200000800000200000800000200009800008,0x80028080020080020080020080020084,0x200800200800200800200500200800804,0x2008002008008008002008002008004,0x80000800080000800080000800080000800080000800206,0x200800200800200800800800200800804,0x8000500008009c0000800200000800080000800080006,0x80020080020080020080020080020084,0x800800200800200800200800200800204,0x2008002008002008002008002008004,0x80000800080000800200000800080000800080000800086,0x200800200800200800200800200800204,0x52008008008002008002008002008004,0x80020080020080020080020080020084,0x200800200800800800200800200800204,0x2008002808002008002008052008004,0x80000800080000800080000800080000800080000800206,0x200800200800200800800800200800204,0x2008002008002008052008002008004,0x80020080020080020080020080020084,0x200800200800280800200800200800204,0x208008002008002008008008002008004,0x80080080020080020052020080020054,0x200800800800200800200800200800804,0x880080050800200000800080000800080000800080006,0x80520080020080020080020080020084,0x800800200800200800200800800800204,0x2008008008002008002008002008004,0x80020080520080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020052080080020080020052080084,0x800800200800200800200800200800204,0x2008052008002008002008002008004,0x80520080020080020080020080020054,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80000800080000800200800800080000800080000800086,0x200800200800200800200500200800204,0x2008002008002008002008002008004,0x80020080020080020080080080080254,0x200800200800200800200800200800204,0x2005202008002008002008008008004,0x80020080020080020080020080020084,0x200800200800200800200800200800804,0x2008002008002008002008002008004,0x80000800080000800080000800200000880080000800086,0x10008000400700010008001000200010008000405,0x2008002008002008002008002008004,0x80020080020080080080020080028084,0x200800200800200800800800200800204,0x2008002008002005208008002005204]
private def pack23 : Array ℕ := #[0x80020080080080020080080052020084,0x200800200800200800200800200800204,0x40020004000800100020004001400040020005,0x80020080020080020080020080020084,0x800080000800080000800080000800200000800080000806,0x2008002008002008002008002008004,0x80020080080080020080020080020084,0x200800200800200800200800200800204,0x2028002008008008002008002008004,0x80020080020080020080020080020084,0x200800800800200800200800200800204,0x800080000800080000800080000800200000800080006,0x800000200921c0000020000080000020000080000020000080000020000088,0x200800200500200800200800200800204,0x8008008008002008002008002008004,0x80080080020080020080020080520084,0x200800200800200800200800200800204,0x2808008008002008002008002008004,0x80020080020080020080020080020054,0x800080000800200000800080000800080000800080000806,0x2008002008002008002008002008004,0x80020080020080020080020080080084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020052020084,0x200800200800200800200800200800804,0x8008002008002008002008002008004,0x80000020000080000020000080000020000890000020000080000020000088,0x200800200800200800200800200800204,0x2008002008002008002808002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002028008008002008004,0x80020080020080080080020080020084,0x200800200800200800800800800800204,0x52008002008002008002008002008004,0x80000800080000800080000800080000800080002000206,0x10008000400200010008041000200010008000405,0x2008002008002008002008002008004,0x2000c00080004002000100080004002000100085,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80000020000080000020000050000020000080000020098080000020000088,0x200800800800200800800800200800204,0x40040070001000800040020001000800040020005,0x2000100080010002000100050010002000100135,0x2000008000002000008000002000008000002000098000002000008000002008,0x2008008008002008002008002008004,0x80020080020080020080020080020084,0x200800200500200800200800800800284,0x2008002008002008002008002008004,0x200010008000401200010008002e802000100085,0x200800202800800800200800200800204,0x2008002008002008002008002008004,0x80020080020080080080020080020084,0x200800200800200800200800200800204,0x800080000800080000800200000800080002000080006,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x800080000800080000800050000800080000800200006,0x80020080020080020080020080080084,0x200800800800200800200800200800204,0x800080000800080000800080050800080000800200006,0x80020080080080020080020080020284,0x200800200800200800200800200800204,0x8008002008002008002008002008004,0x200000800080002000080002000080000800080002000086,0x10008000400700010008000400200010008000405,0x2008002008002008002008002008004,0x80020080020080020052520080020084,0x800800200800200800800500200800204,0x2008002008002008002008002008004,0x80080080020080020050020080028084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2808002008002008002008002005004,0x52080080020080020052020080020084,0x200800200800200800200800200800284,0x800080000800200000800080000800080002000080006,0x80020080020080020050020080020084,0x10008001000144010008000400200010008041005,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80000800080000800080000800200000800080000800086,0x200800200800200800200800200800204,0x2008002008002008008008008008004,0x80000800200000800080000800080000800080050800086,0x200800200800200800200800800800204,0x2008002008002008002008002008004,0x80020080020080020080020080080084,0x200800202800800800200800200800204,0x2008002008002008002008002008004,0x80020080020080020280020080020084,0x200800800800800800200800200800204,0x2008002005208008002008002008004,0x80000800080000800080002000200000800142000800086]
private def pack24 : Array ℕ := #[0x200800200800200800800800200800204,0x2008002008005008002008002028004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x2000100080004002000ba0080004002000100085,0x200800200800200800200800200800204,0x2008008008002008002008002008004,0x80020050020080020080020080020084,0x200800200800800800200800200800204,0x800080000800200002000080000800080000800080006,0x280080080020080020080020080020084,0x800080000800080000800080000800080000800200000806,0x40020001000800040020001000800040070005,0x80020080020080020080020080020084,0x200800800800200800200800200800204,0x8008002008002008002008002008004,0x80020080020080020080020280020084,0x200800800800200800200800200800204,0x2008008008002008002008002008004,0x80020080020080020080020080020084,0x2000008000002000008000002000008000002000008000002000089000002008,0x800080000800080000800a00000800080000800080006,0x80020080020080520080020080020084,0x200800200800200800200800800800204,0x2008002008002008002008002008004,0x80020080020080020080028080080084,0xba008000400200010008000400200010008000405,0x2008002008002808002008008008004,0x80000800200000800080002000080002000080000800086,0x200800200800200805200800200800204,0x100020001004801440020001000800040070005,0x2000100080004007d00100080004002000100085,0x200800200800200800200800200800204,0x2008002005008008002008002008004,0x80020080020080020080080080020084,0x200800200800200800200800200800204,0x2008002008002008002008008008004,0x80020080020080080080020080020084,0x200800200800200800200800200800204,0x2008002008002005002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80080050020080080080528080020084,0x202800200500200800200800200800204,0x300020001000800040020004000800040020005,0x80020080020080020080020080020084,0x200800200800200800800800280800204,0x8008002008002008002008002008004,0x80000080000080000020098080000020000080000020000080000020000088,0x200800200800200800200800200800204,0x2008002008002808002008002008004,0x80020080080080020052020080020084,0x800080000800080000800080000800080000800200000806,0x800080000800080002000050800800080000800200006,0x2000100144004002000100080004002000100085,0x200580200800200800200800800800204,0x2808002008002008008008002008004,0x80020080028080020080020080020084,0x800500200800200800200800200800204,0x2008002008052008002008008008004,0x80002000200000800080000800080000800080000800056,0x200800200800200800200800200800204,0x40070004000800040020001000800040020005,0x80020080020080020080020080020084,0x200800202800200800200800200800204,0x2008002008002008002008002008004,0x50020080020080020080020080020084,0xc0008014400200040008000400200010008000405,0x2008002008002008002008002008004,0x80020080020080020280020080020084,0x200800200800200800200500200500804,0x8008002008008008002008002008004,0x80020080020080020080020080020084,0x800080000800080000800080000800200000800080000806,0x2008002008002005002008002008004,0x80020080520080020080020080020084,0x200800200800200800200800200520204,0x8008002008002008002008002008004,0x80020080020080028080020080020084,0x10008000400200010008000400201040008000405,0x2008002008002008002008002008004,0x80080080020080020080020080080084,0x200800200800200800200800200800204,0x800200000800080000800080000800080000800080006,0x80020052020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800800800200800204,0x2008002008002008002008002008004,0x80000080000080000080000080000020000080000980000080000020000088,0x200800800800200800200800200800204,0x800080000800080000800200000800080000800080006,0x80020080020080020080020080020084,0x200800200800200805200800800800204,0x800050800800080000800200000800080000800080006,0x80020080080080520080020080020084,0x200800200800800800200800200800204]
private def pack25 : Array ℕ := #[0x2008002008002008002008002008004,0x80000800080000800080002000080000800080200800086,0x800080000800080002000200000800080000800080000806,0x40070001000800040020001000800040020005,0x80020280020080020080080080020084,0x200800200800200800200800200800204,0x2008002008008008002008002008004,0x80000800080000800200800800080000800080000800086,0x800800800800200800200800200500204,0x2008002008002008002028002008004,0x80020080080080020280020080020084,0x200800200800200800200800202800204,0x2008002008002008002008002008004,0x80028080020080020080020080020084,0x800800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x2000080000800080000800200000800080000800080000806,0x8008002008002008002008002008004,0x80002000080000800080000800080000800080000800206,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80000800200000800080000800080000800080000800086,0x200800200800200800200800200800204,0x2008002008005008008008002005004,0x80020080020280020080080080020084,0x2000080000800080000800080000800080000800200000806,0x2008002808002008002008008008004,0x80020080020080020080020080020084,0x2000008000002000008000002000089000002000008000008000008000018008,0x2028002008002008002008002008004,0x80520080020080020080020080020084,0x200800200800200800200800800800204,0x2008002808002008002008002008004,0x80020080028080020080020080020084,0x200800200800280500200520200800204,0x800080000a00080000800080002000080000800080006,0x80020080050080020080020080020084,0x200800200800200800200800800500204,0x2005002008002008002008002008004,0x200800800080000800080000800080000800080000800086,0x200800200800800800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800804,0x2008002008008008002008002008054,0x80020080020080020080020080020084,0x2000080000800080002000080005c80080000800080200806,0x2008002008002008002008002008004,0x2000100080004002000100080004007000100085,0x200800200800200800200800200800204,0x8008002008002008002008002008004,0x80020080520050020080020080020084,0x200800200800200800200800200800204,0x2008008008002008002008002008004,0x80020080020080020080020080020084,0x100080004002000c0008000400200040008001005,0x40070001000510040020001000800040020005,0x280020080020080020080020080020084,0x200800200800800800200800200800204,0x2008052008002008008008002008004,0x80000800050800800080000800080000800200800800086,0x200800200800200800200800200800204,0x8008002008002008002008002008004,0x80020080020080020080080080020084,0x800080002000080000800080000800080000800200000806,0x2008002008002008002008002008004,0x80020080020080020080020050020084,0x800080000800080000800080000800080000800080200886,0x800200000800080000800080000800080000800080006,0x80020080080080020080020080020084,0x200800200800200500200800200800204,0x2008002008002008002008002008004,0x80000800080000800080000800200000800200002000086,0x2000080000800080002000080200800080000800080000806,0x2008052008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200520200800204,0x800080000800080000800200000800080000800080006,0x80020280020080020080020080020084,0x800200000800080000800080050800080000800080000806,0x2008002008002008002008002008004,0x80020080020080020080080080020084,0x800080000800200000800080000800080000800080001406,0x2008002008002008002008008008004,0x80020080020080020080020080020084,0x800800200800200800200500200805204,0x8008008008002008002008002008004,0x80028080020080020080020080520084,0x800080000800080002000200000800080050800080000806,0x800080000800080000800200000800080000800080006,0x80020080020080080080020080080084,0x800800200800200800200800200800204,0x2008002008002008008008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200520204,0x202008002008008008002008002008004,0x80080080020080020080080080020054,0x200500200800200800200800200800204,0x2008002008002008002008002008004]
private def pack26 : Array ℕ := #[0x80020080080080020080020080020084,0x200800200800200800200800200800204,0x2008002008008008002008002008004,0x80020080020080020050020050020084,0x800080000800080000800080000800080000800080200806,0x2008008008002008002008002008004,0x80520080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80080080080080020080020080020084,0x200800200800200800202800200800204,0x2008008008002008002008002008004,0x80000800080000800200000800080000800080000800086,0x200800200800200800200800202800204,0x800080000800080000800200800800080000800080006,0x1440400080004001440100080004012000100185,0x200800200800200800200800200800804,0x2008002008002005202008002008004,0x80020080020080020080020080020084,0x8000008000002000008000008000008000008000008000002000008000098008,0x8008002008002008002008002008004,0x80000800080000800080000800080000800200000800086,0x200800800800200800200800280800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200520200800200800200800200800204,0x2808002005002008002008002008004,0x80000800080000800080000800200000800080000800086,0x10008000400200010008003000200040008000405,0x2008002008002008002008002008004,0x80020080020050020080020080080284,0x200800200800200800200800200800204,0x800200000800080000800080002000050800800080006,0x280020080020080020080020080020084,0x200500200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x800200000800080000800080002000080000800080000806,0x2008008008002008008008002008004,0x80020080020080020080080080020084,0x200800200800200800200805200800204,0x2008002005002008002008002008004,0x80020080050080020080020080020084,0x200800200800200800200800800800284,0x800080000800080000800080000800200000800080006,0x80020080020080020080020080020084,0x100080010002000ba008000400200010008000405,0x2008002008002008002008002008004,0x80020080020080080080020080020084,0x200800200800200800200520200800204,0x2008002008002008002008002008004,0x80020080020080020080080080080084,0x800200000800080000800080000800080000800080000806,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800800800200800200800200800804,0x2008002008002008002005202008004,0x80020080080080020080020080020084,0x2000008000002000008000002000008000002000008000002000089000002008,0x52008002008002008002008002008004,0x50000800080000800080000800080000800200000800086,0x200800280800200800800800200805204,0x40020001000800040020001001f00040020005,0x80020080020080020080020080020084,0xc0005000400200010008000400200010008000405,0x2008002008002008008008002008004,0x880002000080006000050000800200800800080000800086,0x200800200800200800202800200800204,0x2008002008002008002008002028004,0x20001000800040020001000800040020001001c5,0x280800200800200800200800200520204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800800800200800200800200800204,0x2008002008002008002008008008004,0x200000800080000800080000800080000800080000800086,0x200800200800200520280800200800804,0x2008008008002008002008002008004,0x80020080020080020080020080020084,0x200800200805200800200800200800204,0x2008002008002008002008002008004,0x80000800080000800200000800080000800080000800086,0x800800800800200800200800200800204,0x2008002008002008008008002008004,0x80000800080000800200000800080000800080002000086,0x200800200800200800200800800800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800202800804,0x800200000800080000800080000800080000800080006,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x800080000800080002000050000800080002000a00006,0x50020080020080020080028080020084,0x2000008000002000008000002000008009117080008000002000008000002008,0x2008002008002008002008002008004,0x80020080020080080080080052020084,0x200800200800200800200800280800804,0x2008002008002008002005002008004,0x80020080020080020080020080020084]
private def pack27 : Array ℕ := #[0x800080000800080000800200006000080000800080000806,0x2008008008002008002008002008004,0x50020080020080020080020080020084,0x200800200800800520200800200800204,0x2008002008002008002008002008004,0x80080080020080020080020080020084,0x200800800800200800200800200800204,0x800080000800200000800080000800080000800080006,0x80020080020080020080020080020084,0x200800200800202800200805200800204,0x8008008008002008002008002008004,0x80020080020080020080020080020084,0x200800800800200800200500200800204,0x2008002008002008002008002008004,0x80020080080080080080020080020084,0x200800200800200800200805200800804,0x800080000800080000800080000800200000800080006,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x40020001000800040020001000800300020005,0x80020080020080020080020080080084,0x800800200800202800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080080084,0x200800200800200800200520200800204,0x200009800000200000500000200000800000200000800000200000800008,0x80020080020080020080020080028084,0x800080000800080000800200000800080000800080000806,0x2008002008002008002008002008004,0x50020080020080080080080280020084,0x200800200800280800200800200800204,0x2008002008002808002008008008004,0x80020050020080020080020080020084,0x200800200800200800800800202800204,0x2008002008002008002008002008004,0x80000800200000800080000800080000800080000800086,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080080080020080020084,0x800080000800080000800080000800200000800080000806,0x2008002008002008008008002008004,0x80080080020080020280020080020084,0x800000080000000800000080000000800000080000002000d94080000000800000080000000800a,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x40000008007f930080002000000100000080000004000002000000100000080000004009,0x50800080000800080000800080002000200002000080006,0x7000100480010002000100080010002000100085,0x200800200805200800200800200800204,0x2008002008008008002008002008004,0x80020080020080020080020080020084,0x200800200800200800280800200800204,0x2008002008002008002008008008004,0x80020080020080020080020080020084,0x200800200800200800200800200800804,0x2008002008002008002008002008004,0x80080080020080020080020080080084,0x200800200520200800200500200800204,0x2008008008002008002008002008004,0x80020080020080020080020080520084,0x800800200800200800200800200800204,0x2008002005002008002008002005004,0x80020080020080020080080080020084,0x200800200800200800200800200800204,0x2008002008008008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800804,0x8008002008002008002008002008004,0x80000800080000800080002000080000800200000800086,0x800080000800080000800080200800080000800080000806,0x2008002008002008002008002008004,0x20001000800040020001000800040020001001c5,0x200800200800200800200800200580204,0x2008002008002008002005202008004,0x80080080020080020080020080020084,0x200800202520200800200800800800204,0x2008002008002008002008002008004,0x80080080020080020080020080080084,0x200805800800200520200800200800804,0x800080000800200000800080000800080000800142006,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800280800200500800500200800204,0x2008002008002008002008002008004,0x80020080020080020080080080020084,0x200800200800800800200800800800204,0x2008002008002008002008002008004,0x200000800080000800080000800080000800080000800206,0x200800200800200800200800200800204,0x2008002008002008008008008008004,0x80020080020080020080020080020084,0x800080000800080002000200000800050000800080000806,0x2008002008002008002008002008004,0x2000100050004002000c00051004002000100085,0x200800200800202800200800800800204,0x2008002008008008002008008005204,0x80020080020080020080020080020084,0x200800200800200800200800280520204]
private def pack28 : Array ℕ := #[0x800080000800080000800200000800080000800080006,0x80020080020080080080020080020084,0x800080102000200000800080000800080000800080000806,0x2008008008002008002008002008004,0x80020080080080020080020080520084,0x200800200800280800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800202800200800200800200800204,0x8008008008008008002008002008004,0x80020080020080020080020080020084,0x2000050800800080000800080000800200000800080000806,0x2008002008002008002008002008004,0x80080080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x800200000800080000800080000800080000800080000806,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x280800200500200800200800800800204,0x2008002008002008002008008008004,0x80020080020080020080020080020084,0x200800200805200800200800200800804,0x2008002028002008008008008008004,0x80020280020080020080028080020054,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020280020080020084,0x202800200800200800200800200800204,0x2008002008002008008008002008004,0x80020080020080020080020080020084,0x200800200520800800200800800800204,0x2008002008002008002008002008004,0x80000800080000800080000800200000800200000800086,0x800200000800080000800080000800080000800080000806,0x200000800000200000800009100000800000200000800000200000800008,0x80020080020080020080020080020084,0x280800200800200800200800200800204,0x2008002008008008002008002008004,0x80020080020080020080020080020084,0x200800200800800800800800800800204,0x8008002008002008002008002008004,0x80000800080000800080000800080000800080000800206,0x5c000800001000020000040000800001000020000040001c00001007,0x800080000800200000800080000800080002000080006,0x80080080020080020080020080020084,0x200800200800200800800800200800204,0x2008008008002008002008002008004,0x280020080020080020080020080020084,0x280800202800800800200800200800204,0x2008002008002008002008002008004,0x80020080020080020050020080028084,0x200800200800200800200800800800204,0x800080000800200000800080000800080000800080006,0x80020080020080020080080080020084,0x200800200520200800200800200800204,0x8008002008002008002008002008054,0x80020080020080020080520080020084,0x10008002e802000100080004002000c0008000405,0x2008002008002008002008002008004,0x80000800080000800080000800080000800200000800086,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800800800200800200800204,0x800080000800080000800080000800080000800200806,0x80020080020080020080020080080084,0x800800200800200800200800200800204,0x2008002008008008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x8028002008002008002008002008004,0x80020080020080020080020080080084,0x10005100400700010008000400200010008000405,0x2008002008002008002008002008004,0x80020080020052020080080080020084,0x2000080200800080000800080000800080000800080000806,0x2008002008002008002008008008054,0x80020080020080080080028080020084,0x200800200800200800200800200800204,0x300020001000800040020001000800040020005,0x80020080020080020080020080020084,0x200800200800200800200800200500204,0x2008002008002008002008008025004,0x80000800080000800080002000080000800200000800086,0x200520200800200800200800200800204,0x2008002008002008008008002008004,0x80020080020080020050080080020084,0x200800200800200800200800200800204,0x40020001000800300020001000800040020005,0x80020080020080020080020080020084,0x200800200800200800200800800800204,0x2008002008002008002008002808004,0x80020080080052020080020080020084,0x200800200800200800800800200800204,0x2008002008008008002008002008004,0x20001001c0004002000100080004002000100085,0x800080000800080000800080000800200000800080000806,0x200800080000800080000800080000800080000800080006]
private def pack29 : Array ℕ := #[0x80020080080080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80002000080000800200050800080000800080000800086,0x40048001000201040008000400200010008000405,0x2008008008002008008008002008004,0x80000800080000800080000800200000800080000800086,0x202800200800200800200800200800204,0x40070001000800040020001000800040020005,0x80020080020080020080020080020084,0x800800200800200800200800200800204,0x200000800000200000800000200000800000200980800050200000800008,0x50020080020080020080020080020084,0x280800200800200800200800200800804,0x2000080200800080000800080000800080000800080006,0x80020050020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020050020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002005202005004,0x80020080020080080280020080520084,0x100080004002000100080004002000c0008000405,0x2008002008002008008008002008004,0x80020080020080028080020080080084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020280020080080080020084,0x800200000800080000800080000800080000800080000806,0x800050800800080000800200000800080000800080006,0x58020080020080020080020080020084,0x200800200800200800800800200800804,0x800080000800080000800080000800080000800200056,0x80020080080080020080080080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080080080080080020084,0x200800200800800800200800200800204,0x800080000800080002000080000800880000800200006,0x80020080020080020080020080020084,0x200800800800800800200800200800204,0x2008002008002008002008002005204,0x80020080020080080080020080020054,0x200800200800200800200800200800204,0x2008002008002008008008002808004,0x80020080020080020080020080020084,0x200800200800200800200800200800804,0x2008002008002005002808002008004,0x80020080020080020080020080020084,0x800800800800200800200800200800204,0x2008002008002008002008002008004,0x80020050080080020080020080020084,0x1000800040020001001c000400200010008000405,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008008008002008004,0x80020080020080520050020080020084,0x800800200800200800200800200800204,0x2008002008002008002008008028004,0x80080080020080020080080080020084,0x800080000800080000800080000800080000800200000806,0x2008002008002008002008002008004,0x80000800080002000080000800080000800080000800206,0x200800200800200800200800200805204,0x800080000800080000800200050800080000800080006,0x80020080020080020080028080020084,0x800800200800200800200800200800204,0x40020004000800040020001000800268020005,0x80000800200000800080000800080000800080000800086,0x800080000800080000800080000800200000800080002006,0x40020004000800040020001001c00040020005,0x80020080080252020080020080020084,0x200800200800200805200800200800204,0x2005202008002005202008002005204,0x80000800080000800200000800080002000080000800086,0x200800200800200800200800200800204,0x2008002008002008008008052008004,0x52020080020080020080020080020084,0x200800200800200800200800800500804,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x800800200800200800202800200800804,0x2000008000002000008000002008d0500000200000800000200000800008,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008008008002008052008004,0x80020080020080020080020080020084,0x200800200800200800800800200800204,0x2008008008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800800800200800204,0x800200000800080000800880000800080000800080006,0x80000800050800800080000800080000800200000800086,0x200800200800800800200800200800204,0x2008008008002008008005202008004,0x80000800080000800200050800080000800080000800086,0x2000008000002000008000098000008000002000008000002000008000002008,0x2008002008002008002008002008004,0x80002000080002000080000800080000800080200800086]
private def pack30 : Array ℕ := #[0x200800200800200800200800200800204,0x200000800000800000800000208009800000200000800000200000800008,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x8008002008002008002008002008004,0x80020080080080020080020080020084,0x800080002000200000800080000800080000800080000806,0x2008002008002008002008002028004,0x80020080028080020080020080020084,0x200800280800200800200800200800204,0x2005002028002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x40020001000800040020001005c00040020005,0x80020080020080020080020080080084,0x800800200800200800200800200500204,0x2008002008002008002008002008004,0x2000100080010002000100080004007000100085,0x200800200800200800200800200800804,0x2008002008052008008008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002808002008004,0x80020080028080020080080080020084,0x800080000800080000800200002000080000800880000806,0x2008002008002008002008008008004,0x80020280020080020080020080020084,0x200800200800200800200800200800204,0x800080000800200800800080002000080000800080006,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008008008008008002008004,0x80020080020080080080020080020084,0x800080000800080000800080000800080000800200000806,0x2008002008002008008008002008004,0x80020080020080020080020080020084,0x200800800800200800200800200800204,0x2008002008002008002008002008004,0x200000800080000800080000800080000800080000800086,0x800800200800200800200800280800204,0x2008008008002008052008002008004,0x80020080080080020080020080020084,0x800200000800080000800050000800080000800080000806,0x2008002008008008002808002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2005002028002008002008002008004,0x80020080020080020080020080080084,0x200800200800200800200800200800204,0x2008002008002005202008002008004,0x80080080020080020080020080020084,0x200805200800200800200800200800804,0x2008008008008008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002808002008002008002008004,0x80000800080050800080000800080000800200000800086,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080080080020080020084,0x800200000800080000800080000a00080000800080002006,0x8008002008002008002008052008004,0x80000020000080000980000080000020000080005020000080000020000088,0x200800200800200800800500800800804,0x800200000800080000800080000800200000800080006,0x80020280020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002028002008002008004,0x80020080020080020080020080020084,0x200800800800200800200800800800204,0x2008002008002008002008002008004,0x80000800080000800080000800200000800080002000086,0x200800200800200800800800200800204,0x2008058008002008002005202008004,0x2000100080004002000100080004007000100085,0x200800200800200800200800200800204,0x2008002008002805052008002008004,0x80020080020080020080020080020084,0x200800200800200500800800200800204,0x2008002008002008002008002008004,0x80020080020080020052080080080084,0x800080200800080000800080000800080000800080000806,0x2005202008002008002008008008004,0x80020080020080020080020050020084,0x10008000400200010008000400510010008000405,0x2008002008002008002008002008004,0x80020080020080020080020080080084,0x800200000800080002000050800800080000800080000806,0x800000800000200002002000200000800000200000800000200980800008,0x80020080020080080080020080020084,0x200800200800200800200800200800204,0x800080002000080000800080000800080000800080206,0x52020080020080080080020080020084,0x800080002000080000800080000800080000800200000806,0x8008008008052028002008002008004,0x80020080020080020080020080020084,0x800080002000080000800200002000080000800080000806,0x2008002008002008002008002008004,0x80020080080080020080020080020084,0x200800200500200800200800200800204]
private def pack31 : Array ℕ := #[0x2028002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002005202008002008002008004,0x80080080020080020080020080020084,0x800500200800200800200800200800204,0x800080000800200000800080000800880000800080006,0x80080080020080020080020080020084,0x200800800800200800200800800800204,0x2e8020001000800040020001000800040020005,0x80020080020080020080020050020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200500200800204,0x800080000800080000800080000800080002000200006,0x80020080020080020080020080020084,0x200800200800200800200800200800804,0x2008002008002008002008002008004,0x2000100080004007000100080004002000400085,0x200800200800200800200800200800204,0x2008002028002008002008002008004,0x80028080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008008008002008004,0x880000800080000800200000800080000800080000800086,0x200800200800800800800520800800204,0x52008002008008008002008002008004,0x80000800080000800080000800880000800200000800086,0x200800200800200800200800200800204,0x2008002808002008002008002008004,0x200000800080000800080002000080000800080000800086,0x200800200800200800200800200800204,0x800080000800080002000080000800200000800200006,0x80020080020080020080020080020084,0x10008000400200010008003000200010008000405,0x802008002008002008002008008008004,0x80080080020050020080020080020054,0x200800200800200800200800200800204,0x2008008005002008002008008008004,0x80020080020080020080020080020284,0x800000050000002000000080000000800000080000000800000080000000800d94080000000800a,0x2008008008002808002008002008004,0x80020080020080020080020080020054,0x200800200800800800200800200800204,0x2808002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008052008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800800800204,0x2000080000800080000800080000800200000800080006,0x80000800080000800080000800080000a00080000800086,0x200800800800200800200800200800204,0x2008002008002008002008008008004,0x80520080020080020080020080020584,0x200800200800200800200800200800204,0x2005802008002008002008002008004,0x80000800200000800080000800080002000080002000086,0x800200000800050000800080000800080000800080000806,0x2008002008008008002008002008004,0x80020080020080020080020080080084,0x800800200800800800200800200800204,0x2008002008002008002008002008004,0x80020080020080080080020080028084,0x200800200800200800200800200800204,0x2008002008002008002808002008004,0x80020080020080028080020080020084,0x200800200800200800200800200800204,0x800080000800080000800080000800200000800080006,0x580020080020080020080080080020084,0x200800200800200800200800200800204,0x8008002008002005202008008008004,0x80020080020050020080020080020084,0x800080000800080000800080000800200000800080000806,0x2028002008052008002008002008004,0x80080080020080020080020080080084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80000800200000800080002000080000800080000800086,0x200800200800200800200800200800204,0x2008002008002008008008002008004,0x200000800080000800080000800080000800080050800086,0x2000008000002000008000002000008000002000008000098000008000002008,0x2808002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008008008004,0x80020080080080020080020080080084,0x800800800800200800200800202800204,0x2008002008008008002008002008004,0x80000800080000800200000800080000800050800800086,0x800800200800200800200800200520204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800800800200800200800204,0x2008002008002008002005002008004,0x80080080080080020080020080020084,0x10008017000140010008000400200010008000405,0x800080002000200002000080000800080000800080006]
private def pack32 : Array ℕ := #[0x7000100080004007000100080004002000100085,0x200800200800200800200800200800204,0x52008002008002008002008002008004,0x80020080520080020080020080020084,0x200800200800200800200800200800204,0x8008002008002028002005002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800804,0x8008002008002008002008002008004,0x80080080020080020080020280020084,0x200800200800200800200800200800204,0x2000800200000800080000800080000800080000800080006,0x2000100080004002000100080010002000100145,0x200800280800200800200800200800204,0x800080000800200000800080000800080000800080006,0x80020080020080020080020080020084,0x200800200800200500200800800800204,0x2008002008002008002008002008004,0x80520080020080020080058080080084,0x200800200800200800200800200800204,0x2008002008002008008008002008054,0x80020080080080080080020080020084,0x200800200800200800200800800800284,0x800080000800080000800200000800200000800080006,0x80020080020080020080020080020084,0x200800200800200800800800202800204,0x2008002008002008002008002008004,0x80020080020080020080080080020084,0x200800200800800800800800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020284,0x200800200800200800200800200800204,0x40020001000500100020001000800040070005,0x200000800080000800080000800080000800080000800086,0x200800200800800800200800200500204,0x52005002008002008002008002008004,0x50020080020080080080520080020084,0x200800200800200800200800200800204,0x2008002008002008008008002008004,0x80020080020080020080020080028084,0x800800200800200800200800200800204,0x8008002808002008002008002008004,0x80000800080000800080000800080000800080000800206,0x200800800800200500200800200800204,0x8008002008002008002008002008004,0x80020080080080020052020052020084,0x800142000800080000800080000800200802000080000806,0x2008002008002008002008002005204,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080080080020084,0x800800200800200800200800200800204,0x2008002008002008008008008008004,0x200002000080000800080000800080000800080000800086,0x800080000800080000800080000800080002000080200806,0x2008002008002008002008002008004,0x80020080020080020050020080520084,0x200800200800200800200800200800204,0x2028002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200805200800200800204,0x40020001000800040020001000800300020005,0x80020080080080020280020080020084,0x200800200800200800200500200800804,0x2008002008002008002008002008004,0x80020080020080020080020052020084,0x10005014400200040008000400600010008000405,0x800080000800200000800080000800080000800080006,0x80020080020080020080020080028084,0x200800200800200800200800200800204,0x2008002005202008008008002008004,0x80020080020080028080020080020084,0x800800200800200800200500800800204,0x800080200800080000800080002000080000800080006,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2000080000800200000800080000800080000800080006,0x80000800080000800080000800080000800080000800206,0x200800200800200800200800200800204,0x2008002008008008002008002008004,0x80020080020080020080020080020084,0x200800200800200800800800200800204,0x2008002008002008002008002008004,0x80080080020080020080020280020084,0x200800200800200800200800200800804,0x800080000800200000800080002000080000800080006,0x80020080020080020080080080020084,0x800080000800080000800080000800080000800200000806,0x2008008008002008002008002008004,0x200000020000080000020000080005020000080000980000080000020000088,0x200800200800800800200520200800204,0x40070001000800040020001000800100020005,0x80020280020080020080028080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080080080020080020080020054,0x2000008000002009808000002000008000008000008000002000008000002008,0x8028002008002008008008002008004,0x80020080020052020080020080020084]
private def pack33 : Array ℕ := #[0x200800800800800800200500200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002025002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080080084,0x2000080000800200000800080000800080000800080002006,0x2008002008002008002008002008004,0x80020080020080020080520080020084,0x92000208000002000008000002000008000002000008000002000008000002008,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200520204,0x2008008008008008002008002008004,0x80020080020280020080080080020084,0x800080000800080000800080000800200000800080000806,0x2008002008002008008005208008004,0x2000100080004002000100134004002000100085,0x200800200800200800200800280800204,0x2008002008002008002008002008004,0x80000800200800800080000800080002000080000800086,0x200800200800200800202800200800284,0x2008002005202008002008002808004,0x80020080028080080080020080020084,0x200800200500200800200800200800204,0x2008002008002008008008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x800200002000080000800080000800080000800080006,0x80020080020080020080020080020054,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80000800080002000080000800080000800080000800206,0x200800200800200800200800200800204,0x2008002008008008002008002008004,0x80020080020080020580020080020084,0x200800200800200800200800200800204,0x2808002008002008002008002008004,0x80000020000080000020000080000020000980000020000080000080000088,0x800080000800200000800080000800200000800080002006,0x2008002008002008002008002008004,0x80080080520080020080020080020084,0x800800200800200800200800200800204,0x2008008008002008002008002008004,0x80020080028080028080020080020084,0x200800200800200800800800800800204,0x2008002008002008002008002008004,0x80000020000080000020000080000020000080000020000080000020000988,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020052020080020080020080020084,0x10008000400200010008002000200510008001005,0x8008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x800080000800080000800080002000200000800080006,0x80020080020080020050020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200505200800200800800800204,0x2008008008002008002008002008004,0x80020080020080520080020080080084,0x200800200800800800200800200800204,0x2008002008002008002008002008004,0x80020080080080020080020080020084,0x200800200800800800200800200800204,0x2005202008002008002008002008004,0x80020280020080020080020080020084,0x200500200800200800800800200800204,0x200800080000800080000800080000800080000800200006,0x80020080020052020080080080020084,0x200800200800200800200800200800204,0x2008002008052008002008002008004,0x20001000801440020001005c0004002000400085,0x200800200800200800200800200800804,0x8008002008002008002008002008004,0x80028080020080020080020080080084,0x800080000800200002000080000800080000800080002006,0x2008002008002008002008002008004,0x80020080020080080080020080020084,0x200800200800200800200800280800204,0x2008002008002008002008002008004,0x80000800080000800080002000080000800080000800206,0x200800200800200800800800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800800800200580200800200800204,0x2005002008002008008008002005004,0x80080080080280020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80000800080000800080000800200000800080002000086,0x2000008000002000008000002000098000002000008000002000020000002008,0x2008002008002008002008002008004,0x80520080020080020080020080020084,0x800800800800200800200800200800204]
private def pack34 : Array ℕ := #[0x2008002005202008002008002008004,0x80080080025080020080020080020084,0x800050800800200000800080000800080000800080000806,0x202028008008008008002008002008004,0x80000800200000800080000800080000800080000800056,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x52020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002808002008002008008008004,0x80020080020080020080020080080084,0x200800800800800800200800200800804,0x2008002008002008002008002008004,0x80000800080000800080000800200000800080000800086,0x200800200800200800200800200800804,0x800080000800080000800080000800080000800200006,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008008008002008004,0x80020080520080020080020080020084,0x200800200800200800280800800800204,0x2008002008002008002008002008004,0x80020050020052080080020080020084,0x200800200500202800200800200800204,0x2008002008002008002008002008004,0x280020080020080020080020080020084,0x200800200800200800800800200800204,0x2008002008008008002008008005004,0x80020052020080020080020080020084,0x200800200800200800800800280800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800800800200800200800200800204,0x2008002008002008002008002008004,0x80020280020080020080020080020084,0x200800200800200800200800200800284,0x40020004000800040070001000510040020005,0x80020080020080020080020080020084,0x2000008000002000008000098000008000002000008000002000008000002008,0x2008002008002008002008002008004,0x80000800080000800080000800080002000200000880086,0x10008000400700010008000480200010048000405,0x2008002008002008002008002008004,0x80020080020080080080080080020084,0x200800200800200800200800200800204,0x2000080000800080000800080000800080002000200006,0x80020280020080020080020080020084,0x200800800800200800200800200800204,0x800080000800200000800080050800080000800080006,0x80020080020080020080020080080084,0x800080000800200000800080000800080000800080000806,0x2008002008002008002008008008004,0x80020080020080020080020080020084,0x200800200800200505200800200805204,0x2008002008002005002008002008004,0x2000120080004002000b80480004002000400085,0x800800200800202800200800200800204,0x2008002008002008002008002008004,0x80020050020080020080020080020084,0x200800200800200800800800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200520204,0x2008002008002008002008002008004,0x80020080020080020080080080020084,0x200800200800200800200800200800204,0x2008008008002008002008008008004,0x80080080020080020080020080020084,0x800080000800080000800080000800080000800200000806,0x10040020001000800040020001001c00040020005,0x80000800080000800080000800200000800080000800056,0x200800800800200800200800200800204,0x2008002008002008002008002008004,0x80520080020080080080020080520084,0x800800200800200800200800200800204,0x2008002008002008008008008008004,0x80000800200000880080000800080002000080000800086,0x10008003000200010008000400200010008000405,0x2008002008002008002008008008004,0x80020080020080020080020080020084,0x200800200800200800200800202800204,0x2008002808002008002008002008004,0x52028080080080020080020080080084,0x200800200800200800200800200800204,0x2008002008008008002008002008004,0x80020080080080020080020080080084,0x200800200800200800200800200500204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x10008000400170010008000400200012008000405,0x2008002008008005002008002008004,0x80080080020080020080020080020084,0x200800200800280800200800200800204,0x2008008008002008002008002008004,0x80000800080000800080002000200000800080000800086,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020050020080020084,0x280800200800200800200800200800204,0x800200000800080000800080000800880000800080006]
private def pack35 : Array ℕ := #[0x280080080020080020080020080020084,0x200800200800200800200800200800804,0x8008002008002008002008002008004,0x80020080020080020080020080020284,0x800200002000080000800080000800080000800080000806,0x2008002008002008002008002008004,0x80080080080080020080020080020084,0x200800200800200800200805200800204,0x200000800000200000800009800001c00000200000800000200000800008,0x80020080020080020080020080020084,0x200800200800200800200800800800284,0x2008002008002008002008002008004,0x80000800200000800080000800080000800080002000086,0x200800200800200800200800800800204,0x2008002008002008002008002008004,0x980000020000080000020000080000020000080000020000080000020000088,0x200800200800200800200520200800204,0x2005002008002008002008008008004,0x80020080020080020080020080020084,0x200800200800280800800800200800204,0x2008002008002008002008002008004,0x80020080020080020080080080020084,0x200800202800200800200800200500204,0x2008002008008008002008052008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008008008002008002008002008004,0x2000100080004002000800080004002000100085,0x200800280800800800200800200805204,0x2008002008002008002008002008004,0x80020080020080080080020080020054,0x800080000800080000800200000800080000800080002006,0x2008002008002008002008008008004,0x80020080020080020080020080020084,0x200800200800200800202805200800204,0x8008008008002005252008002008004,0x80020080020080020080080080020084,0x200800800800200800200800200520204,0x800080000800080002000080002000080000800200006,0x80080080080280080080028080028084,0x2000008000002000008000002000008000002000008000002000089000002008,0x40020001000800040020001001400040020005,0x80020080020080020080020080020084,0x200800200800200800280800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x800800200500200800200800800800204,0x2008002028002008002008002008004,0x80002000080000800200000800080000800080000800086,0x200800200800200500200800200800204,0x2008008008002008002008008008004,0x80020080020080020080020080020084,0x800080000800080200800080000800080000800080000806,0x40070001000800040020001000800040020005,0x80020080020080020080020080020084,0x200800200800200800200800202800204,0x2008002008002008002008008008004,0x80020080020080020080020080020084,0x200800200800800800200800200800804,0x800080000800080000800080000800080000800200006,0x80020080020052020080020080020084,0x10008000400144010008041000200010008000405,0x2008002008008008002008002008004,0x80000800080000800080000800080000800200000800086,0x200800200800200800200800280800204,0x8000000800000008000000800000008000000800000d7c000000800000008000000800000a,0x80020080020080020080020080020084,0x200800200800200800200800800800204,0x8008002008002008002008002008004,0x80020080020080020080020052020084,0x200800200800200520200800800800804,0x800200000800080000800080000800080000800080006,0x80080050020080020080520080020084,0x200800200800200800200800200800204,0x2008002008008008002008002008004,0x80000800080000800200000800080000800080000800086,0x200800200800200800800800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x40020001000800040070001000800040020005,0x80020080020080020080080050020084,0x200800200800200800200805200800204,0x2008008008002008002008002008004,0x80080080020080020080020080020084,0x800080000800080002000200000800080002000080000806,0x2008002008002008002008002008004,0x80020080020080020080020080028084,0x200580200800202800200800200800204,0x2008008008002008002008002008004,0x80020080020080020080020080020084,0x200800200800800800200520200800204,0x8008002008002008002008002008004,0x80020080020080020080020080020084,0x800200006000080000800080000880080000800080000806,0x2008002008008008002008002008004,0x20001000800040020001000800040020001001c5,0x200800200800280800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084]
private def pack36 : Array ℕ := #[0x200800200800200800200800200800204,0x8008008008002008002008002005004,0x800000008000002000000008000000800000008000000800000008000080800000d040000008a,0x2000050000800080000800200000800080000800080000806,0x2008002008002008002008002008004,0x80000800200000800080000800080000800080000800086,0x800080000800200000800080000800200000800080000806,0x8008002008002008002008002008004,0x80020080020080020080020080520084,0x200800200800200800202800200800204,0x202008002008002008002008002008004,0x80020080020080020080080080020054,0x200500800800280800200800200800204,0x800080000800080000800080000800200002000880006,0x2000100080004002005100080030012000100085,0x200800200805200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020050020084,0x200800280800200800280800800800204,0x2008002008002008002008002008004,0x80020080020080080080020080020084,0x202800200800200800200800200800204,0x2008002008002008008008002008004,0x80020080020080020080080080020084,0x200800200520200800200800200800204,0x2008002008002008002008002008004,0x80000800080002000200000800080000800080000800086,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080080080020080020080020084,0x200800200800800800200800200800204,0x2008002008008008002008002008004,0x80020080020080020080020080020084,0x200800200500800800800800200800204,0x2008002008002008002008002008004,0x80000800080000800080000800080000800200002000086,0x802800200500200525200800200800204,0x2008002008002008002008002008004,0x80080080080080028080020080020084,0x200800200800200800280800200800204,0x8008008008002808002008002008004,0x80020080020080020080020080020084,0x200800202800200800200800200800204,0x2008002008002008002008002008004,0x80000020000080000020000910000020000080000020000080000020000088,0x200800200800200520800800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x800050000800080000800080000800080000800200002006,0x8008002008008008008008002008004,0x80020080020080020080020080020084,0x200805280800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080080080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x7000100080004002000100080004002000100085,0x200800200800200800280800800800204,0x800080000800080000800080000800200000800080006,0x80020080080080020080020080080084,0x200800200800200800200800200800284,0x2008052008002008002008002008004,0x80020080020080020080020080020084,0x250800200800802800200800200800204,0x2008002008002008002008002008004,0x52020080020080020080080080080084,0x800200000800080000800080002000080000800080000806,0x800080000800080000800200000800080000800080006,0x80020080020080020052080080020084,0x800080200800080002000080000800080000800080000806,0x2008002008002008002008002008004,0x80020080020080520080020080020084,0x200800200800280800200520200800804,0x800080000800200000800200000800080000800080006,0x80020080020080020080020080020084,0x800800200800800800200800200800204,0x2008002008002008002005002008004,0x80020080020080080080020080020084,0x200520200800200800200800200800204,0x800080000800080000800080000800080000800080206,0x2000100080004007000100080004002000100085,0x200800200800200800200800200800204,0x2008002008002008008008002008004,0x80020080020080020080020080020084,0x10008001000200010008000400200010008003005,0x2008002008002008002008002008004,0x80020080080080020080080080020084,0x200800200800200800200800200800204,0x8008002008002008002008002005204,0x7000100080004002000100080004002000100085,0x200800200805200800200800800800204,0x52008002008002008002008002008004,0x80020080080080020080020080020084,0x97000008000002000008000002000008000008000008000002000008002002008,0x2008008008002008002008002008004,0x80000980000080000020000080000020000080000020000080000020000088,0x802800800800200800200800200800204,0x2008002008002008002008002008004,0x80000800080002000200000800080000800080000800086,0x200800200520200800200800200800204]
private def pack37 : Array ℕ := #[0x2008002008002008002008002008004,0x80020080020080020580020080020084,0x200800200800200800200800200800204,0x2008002008002008002008008008004,0x80020080020080020080020080020084,0x280800200800200800200800200800804,0x2008002008002008002008002008004,0x50020080020080020080020050020084,0x800800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x800080000800080000800080000800080000800200000806,0x2008002008008008008005002008004,0x80020080020080020080020080020084,0x200800200800200800200800800800204,0x800200000800080000800080000800080000800080006,0x80020080020080020080020080020084,0x280800202800200800800800200800204,0x2008002008002008002005202008004,0x80020080020080020052020080020084,0x200800200800200800200800200800204,0x800080000800200002000080002000080000800880006,0x80020080020080020080020080020084,0x200800200800200800800800200800204,0x2008002008002008002008002008054,0x80020080020080020080080080080084,0x200800280800200800200800200800204,0x8008008008002008002008002008004,0x80020080080080080080020080020084,0x200800200800200800200800200800204,0x800080002000080000800050000800200000800080006,0x80020080080080020080020080020084,0x200800200800800800200800200800204,0x2008002008002008002008002005204,0x80020080020080020080080080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80080080028080020080020080020084,0x200800200800200800200800200800204,0x8008002005002008002008002008004,0x80020080020080020080020080080084,0x1000800100020001000800040020001001c000405,0x2008002008002008002008002008004,0x50020080020080020080020050020084,0x200805200800200800200800200800804,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080080084,0x800800200800200800800800200800204,0x40020001000800040020001000800040120105,0x80020080020080020080020080020084,0x800050800800080000800080000800200000800080000806,0x4002000100080004002000c000800040020005,0x80020080020080020080020080020084,0x200800200800200800200800200800804,0x2008002008002008002008002008004,0x80020080020080020080080080020084,0x200800200800200800200800200800204,0x40020001000800040020004000800268020005,0x7000100080004002000100080004002000100085,0x200800800805200800200800200800204,0x2008002008002008002008002008004,0x80000020000080000020000080000020000080000020000080000020000988,0x800080000800080000800080000800200000800880000806,0x2008008008002008002008002008004,0x80020080020052080080020080020084,0x200800202800200800200800200800204,0x2008002008002008008008002008004,0x80020280520080080080020080020084,0x202800200800200800200500200800204,0x2028002008002008002008002008004,0x80020080020080020080020080080084,0x200800200800200800200805200800204,0x800200000800050000800080000800080000800080006,0x80020080080080020080020080020084,0x200800200800200800200800200800804,0x800080000800080002000080000800080200800200806,0x80020080020080020080020080020084,0x280800200800200800200800200800804,0x2008002008002058002008002008004,0x80020080020080020080020080020084,0x800080000800080000800200000800080002000080000806,0x2008002008002008002008002005004,0x80002000080000800080002000080000800080000800206,0x200800200800202800200800200800204,0x2028008008002008002005202008004,0x80020080020080020080020080080084,0x200800200800200800800800200800204,0x2008002008002008002008002008004,0x80080080020080020080020080020084,0x800800200800200800200800200800804,0x800080000800200000800080000800080000800080006,0x80020080020080020080020080020084,0x200800800800200800200800200800804,0x300020001000800040020001000800040020005,0x80020080020080020080020080028084,0x200800200800200800200800280800204,0x2008008008002008002008002008054]
private def pack38 : Array ℕ := #[0x80020080020580020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020054,0x200800200800200800200800800800204,0x8008002008002008002028002008004,0x80020080020080020080020080080084,0x10008000400200010008000400700010008000405,0x800200000800080000800080000800080002000050806,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080080084,0x200500200800200800800800200800204,0x2008002008002008002808002008004,0x80020080020080020080080080020084,0x800080000800200000800080000800080000800080000806,0x2008002008002008002008002808004,0x80020080020080080080020080020084,0x800080000800080000800200000800080000800080000806,0x2008002008002008002028002008004,0x80020080020080020080020080020084,0x200800200800800800800800200800204,0x2008008008008008002008002008004,0x80020080020080080080020080020084,0x800080000800080000800080000800200000800080000806,0x2008002008002008002008002028004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x20004000800040020001000800040020001001c5,0x880080002000080000800080000800200000800080000806,0x2008002008002008052008002008004,0x80020080080080080080020080020084,0x200800800500200800200800200800204,0x2008002008002008002008002808004,0x80028080020080020080020080020084,0x200800200800200800200800200800804,0x2008002008002008002008002008004,0x80020080020080020080028080020054,0x800800200800200800200800200800204,0x40020001000800040014401000800300020005,0x80000980000080000020000080000020000080000020000080000020000088,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080028080020080020080080084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80000800080000800080000800200000800080000800086,0x200800200805200800200800200800204,0x40020051000800040014401000804100020005,0x80000800080000800080000800080000800200002000086,0x200800200800200800200800200800804,0x2008002008008008002008052008004,0x80020080020080020080020080020084,0x200800200800200800800800800800204,0x2008002008002008002008002008004,0x80000800080000800080002000050000800080000800206,0x200800200800200800200800200800204,0x2008002008002028008008002008004,0x80020080020080020080020080020084,0x200800200800200800200800800800204,0x2008002008002008002005202008004,0x80080080020080020080020080020084,0x800500200800200800200800200800204,0x40070001000800040020001000800040020005,0x80020052020080020050020080020084,0x200800800800200800200800200800204,0x400200010008002e8020001000800040020005,0x80520080020080020080020080020084,0x200800200500200800800800200800204,0x2008002008002008002008002808004,0x80020080020080020080020050020084,0x800080000800200000800080000800080000800080000806,0x2008002008002008002808002008004,0x52020080020080020080020080020084,0x800080000800080002000200000800080002000080000806,0x2008008008002008002008002005204,0x80020080020080020080020080020054,0x800800200800800800200800200800204,0x100000000020000000001000000000800000000040000000020000000004000000400800000000100000005af4000000d,0x80020080020080028080020080020084,0x200800200800200800800800200800204,0x2008002008002008002008002008004,0x80000800080000800080000800080000800200000800086,0x200800200800200800200800200800204,0x8000000008000000002000000008000d40367000000005002000002000000008000000002000000005000000c,0x80020080020080020080080080080084,0x800080102000200000800080000800080000800050000806,0x2008002008002008002808002008004,0x80020080020080080080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002005202008002008002008004,0x80020080020080520080020080080084,0x800800200800200800200800200800204,0x100020001000800040020001000800040070005,0x80020280020080020080020080020084]
private def pack39 : Array ℕ := #[0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80080080020080020050020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020052080080020084,0x200800200800200800200800800800204,0x2008002008002008052008008008004,0x80020080020080020080020080020084,0x200800200800200800200800800800204,0x2008002008002008002008002008004,0x80000800200000800050000800080000800080000800086,0x200800200800200800200800200800204,0x2008002028002008002008008008004,0x80020080020080080080020080020084,0x200800200800200800200800200800204,0x4002000100080004001440ba00800040020005,0x80020080020080020080020080020084,0x800200002000080002000080000800080000800080000806,0x2008002008002028002008002008004,0x20001000800040020001001c0004002000100085,0x800080000800200002000080000800080000800080000806,0x2008002808002008002008002008004,0x80020080080080020080020080020084,0x200800200800200800200800200800204,0x2008002008008008002008002008004,0x80020080020080020080020080020084,0x800200000800080000800080000800080000800080000806,0x2008002008002028002008008008004,0x80020050020280020080020080020084,0x200800200800200800200800200800204,0x8008002008002008002008002008004,0x80080080080080020080020080020084,0x200800200800200500200800200800204,0x2008008008002028002008002005004,0x80080080020080020080020080020084,0x100080004002000100080004002000c0008000485,0x2008002008002008002008002008004,0x80000800080000800080000800200000800080000800086,0x200800200800200800200800200800204,0x2008052008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800804,0x300020001000800048070001000800040020005,0x80000800080000800080000800080002000200000800086,0x800800200800200800200800200800204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800800800204,0x2005202008002008052008002008004,0x80020080020080080080080080020084,0x200800200800200800200800800800204,0x800080000800080000800080000800080000800200006,0x80020080020080020080020080080084,0x200805280800800800200800200800204,0x2808002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002008008008002008002008004,0x80020080020080020080020080020084,0x200800200800200800800800200800204,0x2008002008052005002008052008004,0x80020080020080020080080080020084,0x200800200800200800200800200800204,0x2008002005002008002005002008004,0x2008008001c0000800080000800080000800080000800086,0x500800200800200800200800200800204,0x2028002008002008002008002008004,0x80020080020080020080020080020084,0x10008000400200040008000400510010008014405,0x8008002005202008002008002008004,0x80020080020080080080020080020084,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80080080020080020080020080020084,0x800080000800080000800080000800080000800200000806,0x2808002008002008002008002008004,0x80000020000080000020000080000020000080000980000080000020000088,0x200800800800200800200800200800204,0x2008002008002008002008002008004,0x80020080080080020080020080020084,0x800800200800500800200800800800204,0x800080000800080000800080000800080002000200006,0x20001001c0004002000100080004002000100085,0x200800200805200800200800200800204,0x2008002005202008002008002008004,0x80000800080000800200002000080000800080000800086,0x800800200800200800200800200800204,0x40020001024800040020001000800040020005,0x80002000080002000080000800080000800080000800206,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x2000100080004007000100080004002000100085,0x200800200800800800200800200500204,0x52008002008002008002008002005004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2008002808002005002008008008004,0x280020080020080080080020080020084,0x800800200800200800200800200800804]
private def pack40 : Array ℕ := #[0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x208008002008002008002008002008004,0x80000800080000800080000800200000800080000800056,0x200800200800200800200800200800204,0x800200000800080000800080002000080000800080006,0x80020080020080020080520080020084,0x200800800800200805200800800800204,0x2008002008002008002008002008004,0x80020080020280020080020080020084,0x800200000800080000800080000800080000800080000806,0x800200800800050800800080002000080000800080006,0x80080080080080020080020080020084,0x200800200800200800200800200800204,0x800080050800080005c80200000800080000800080006,0x80020080020080020080080080020084,0x200800200800200800800800200800204,0x802008002028002008002008002008004,0x80020080020080020080020080020054,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x2000100080030001400100080004002000100485,0x200800200800200800200800200800204,0x2005208008002008002008002008004,0x280020080020080020080020080020084,0x200800200800800800200800200800204,0x40070001000800040020001000800040014005,0x80020080020080020080020080020084,0x200800200800200800200800200500204,0x2008002008002008002008002008004,0x80080080020080020080020080028084,0x200800200800200800200800200800204,0x8028002005202008002008002008004,0x52020052020080020080020080020084,0x200800800800200800800800280800804,0x200000800000200000800000200000800000200008900000200000800008,0x80020080020080020080020080020084,0x8000008000002000008000002000098000002000008000002000208000002008,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2028002008002008002008002008004,0x80020080020080020080020080080084,0x98000008000002000008000002000008000008000008000002000008000002008,0x2005002008008008008008002008004,0x80000800200000800080000800080000800080000800086,0x800080000800080000800080000800080000800200000806,0x2008002008052008002008002008004,0x80050800080000800080000800080002000080200800086,0x200800200800200800200800200800204,0x2808002008002008002008002008004,0x80020080020080020080080080020084,0x200800200800200800200800200800204,0x800080000800080000800080000800200002000080006,0x80020080020080020080020080020084,0x200800200800200500200800200800204,0x2008008008002008002008002008004,0x80020080020080020080020052020084,0x200800200800200800200800200800204,0x2005008008002008002008002008004,0x80020080080080080080020080020084,0x200800200800200800200800200800204,0x4002000100080004002000c000800040020005,0x80020080020080020080020080020084,0x200800200800200800200800200520204,0x2008002008002008002008002008004,0x80020080020080020080020080020084,0x800080000800080000800080000800080200800080002006,0x52008002008002008002008002008004,0x80000800080002000080000800080000800200000800086,0x800800200800200800200800200800204,0x2008002008008008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x2028002008002008002008002008004,0x80020080020050020080020280020084,0x200800200800200800200800800800804,0x800800200000800080000800080000800080000800080006,0x800020000800008001c0000800200000800080000800056,0x200800800800200800800800200800204,0x2008008008002008002008002008004,0x80020080020080020080020080020084,0x200800200800200800200800200800204,0x40051001000800040020004000800040020005,0x80080080080280020080028080020084,0x200800200800200800200800202800204,0x2008002008002005002028002008004,0x80020080020080020080020050020084,0x200800200800200800200800200800804,0x2000080002000080000800200000800080000800080006,0x80020080020080020080020080020084,0x200800200800200500200800200800204,0x2008002008002008002008002008004,0x2000100080030002000100080004002000100085,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80000020000080000020000080000020000080000020000080000020098088,0x200800200800200800200800805800204,0x2008002008002008002008002008004]
private def pack41 : Array ℕ := #[0x200000800080000800080000800080000800080002000086,0x800200000800080000800080000800080002000080000806,0x2008002008002008002008002008004,0x80020080020080020080520080080084,0x200800200800200800200800200800204,0x2008002008002008008008002008004,0x80020080020080020080020080028084,0x200800200800200800800800200800804,0x8008008008002008002008008008004,0x80020080020080020080080080020084,0x1000800040020001001c000400200010008000405,0x2008002008002008002008002008004,0x80000800080000800080000a00142000800080000800086,0x10008000480200012008003000200010008000405,0x2008002808002008002008002008004,0x80020080020080020080020080020084,0x200800200800800800200800200800204,0x2028002008002008008008002008004,0x80020080020080080080020080020084,0x200500200800200800200800200800204,0x2008002008002008002008002008004,0x980000020000080000020000080000020000080000020000080000020000088,0x200800200800200800200800200800204,0x2008002008002008002008002008004,0x80000020000080000020098080000020000080000020000050005020000088]
private def packages : Array (Array ℕ) := #[pack0,pack1,pack2,pack3,pack4,pack5,pack6,pack7,pack8,pack9,pack10,pack11,pack12,pack13,pack14,pack15,pack16,pack17,pack18,pack19,pack20,pack21,pack22,pack23,pack24,pack25,pack26,pack27,pack28,pack29,pack30,pack31,pack32,pack33,pack34,pack35,pack36,pack37,pack38,pack39,pack40,pack41]
private def rowCode (k : ℕ) : ℕ :=
  let i := k-1-0
  let v := ((packages[i/3200]?).getD #[])[i/32%100]?.getD 0
  let w := v%16
  ((v/16) >>> (w*(i%32)))%(2^w)
private def lengthOf (code : ℕ) : ℕ :=
  if code < 1 then 1 else
  if code < 3 then 2 else
  if code < 9 then 3 else
  if code < 33 then 4 else
  if code < 153 then 5 else
  if code < 873 then 6 else
  7
private def rankOf (t : ℕ) (code : ℕ) : ℕ :=
  if t=1 then code-0 else
  if t=2 then code-1 else
  if t=3 then code-3 else
  if t=4 then code-9 else
  if t=5 then code-33 else
  if t=6 then code-153 else
  code-873
private def unpack : ℕ → List ℕ → ℕ → List ℕ
  | 0,_,_ => []
  | n+1,choices,c =>
      let i := c%choices.length
      (choices[i]?.getD 0)::unpack n (choices.eraseIdx i) (c/choices.length)
private def T (k : ℕ) : ℕ := lengthOf (rowCode k)
private def rows (k i : ℕ) : ℕ :=
  let t := T k
  let perm := unpack t (List.range t) (rankOf t (rowCode k))
  perm[i]?.getD 0
private def chunk (c : ℕ) : Bool :=
  (List.range 50).all (fun j => let k := 0+50*c+j+1; checkRow fast k (T k) (rows k))
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud0 (i : Fin 10) : chunk (0+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud10 (i : Fin 10) : chunk (10+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud20 (i : Fin 10) : chunk (20+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud30 (i : Fin 10) : chunk (30+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud40 (i : Fin 10) : chunk (40+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud50 (i : Fin 10) : chunk (50+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud60 (i : Fin 10) : chunk (60+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud70 (i : Fin 10) : chunk (70+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud80 (i : Fin 10) : chunk (80+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud90 (i : Fin 10) : chunk (90+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud100 (i : Fin 10) : chunk (100+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud110 (i : Fin 10) : chunk (110+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud120 (i : Fin 10) : chunk (120+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud130 (i : Fin 10) : chunk (130+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud140 (i : Fin 10) : chunk (140+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud150 (i : Fin 10) : chunk (150+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud160 (i : Fin 10) : chunk (160+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud170 (i : Fin 10) : chunk (170+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud180 (i : Fin 10) : chunk (180+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud190 (i : Fin 10) : chunk (190+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud200 (i : Fin 10) : chunk (200+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud210 (i : Fin 10) : chunk (210+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud220 (i : Fin 10) : chunk (220+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud230 (i : Fin 10) : chunk (230+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud240 (i : Fin 10) : chunk (240+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud250 (i : Fin 10) : chunk (250+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud260 (i : Fin 10) : chunk (260+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud270 (i : Fin 10) : chunk (270+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud280 (i : Fin 10) : chunk (280+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud290 (i : Fin 10) : chunk (290+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud300 (i : Fin 10) : chunk (300+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud310 (i : Fin 10) : chunk (310+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud320 (i : Fin 10) : chunk (320+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud330 (i : Fin 10) : chunk (330+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud340 (i : Fin 10) : chunk (340+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud350 (i : Fin 10) : chunk (350+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud360 (i : Fin 10) : chunk (360+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud370 (i : Fin 10) : chunk (370+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud380 (i : Fin 10) : chunk (380+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud390 (i : Fin 10) : chunk (390+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud400 (i : Fin 10) : chunk (400+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud410 (i : Fin 10) : chunk (410+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud420 (i : Fin 10) : chunk (420+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud430 (i : Fin 10) : chunk (430+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud440 (i : Fin 10) : chunk (440+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud450 (i : Fin 10) : chunk (450+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud460 (i : Fin 10) : chunk (460+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud470 (i : Fin 10) : chunk (470+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud480 (i : Fin 10) : chunk (480+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud490 (i : Fin 10) : chunk (490+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud500 (i : Fin 10) : chunk (500+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud510 (i : Fin 10) : chunk (510+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud520 (i : Fin 10) : chunk (520+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud530 (i : Fin 10) : chunk (530+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud540 (i : Fin 10) : chunk (540+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud550 (i : Fin 10) : chunk (550+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud560 (i : Fin 10) : chunk (560+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud570 (i : Fin 10) : chunk (570+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud580 (i : Fin 10) : chunk (580+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud590 (i : Fin 10) : chunk (590+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud600 (i : Fin 10) : chunk (600+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud610 (i : Fin 10) : chunk (610+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud620 (i : Fin 10) : chunk (620+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud630 (i : Fin 10) : chunk (630+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud640 (i : Fin 10) : chunk (640+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud650 (i : Fin 10) : chunk (650+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud660 (i : Fin 10) : chunk (660+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud670 (i : Fin 10) : chunk (670+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud680 (i : Fin 10) : chunk (680+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud690 (i : Fin 10) : chunk (690+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud700 (i : Fin 10) : chunk (700+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud710 (i : Fin 10) : chunk (710+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud720 (i : Fin 10) : chunk (720+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud730 (i : Fin 10) : chunk (730+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud740 (i : Fin 10) : chunk (740+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud750 (i : Fin 10) : chunk (750+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud760 (i : Fin 10) : chunk (760+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud770 (i : Fin 10) : chunk (770+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud780 (i : Fin 10) : chunk (780+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud790 (i : Fin 10) : chunk (790+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud800 (i : Fin 10) : chunk (800+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud810 (i : Fin 10) : chunk (810+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud820 (i : Fin 10) : chunk (820+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud830 (i : Fin 10) : chunk (830+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud840 (i : Fin 10) : chunk (840+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud850 (i : Fin 10) : chunk (850+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud860 (i : Fin 10) : chunk (860+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud870 (i : Fin 10) : chunk (870+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud880 (i : Fin 10) : chunk (880+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud890 (i : Fin 10) : chunk (890+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud900 (i : Fin 10) : chunk (900+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud910 (i : Fin 10) : chunk (910+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud920 (i : Fin 10) : chunk (920+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud930 (i : Fin 10) : chunk (930+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud940 (i : Fin 10) : chunk (940+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud950 (i : Fin 10) : chunk (950+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud960 (i : Fin 10) : chunk (960+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud970 (i : Fin 10) : chunk (970+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud980 (i : Fin 10) : chunk (980+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud990 (i : Fin 10) : chunk (990+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1000 (i : Fin 10) : chunk (1000+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1010 (i : Fin 10) : chunk (1010+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1020 (i : Fin 10) : chunk (1020+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1030 (i : Fin 10) : chunk (1030+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1040 (i : Fin 10) : chunk (1040+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1050 (i : Fin 10) : chunk (1050+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1060 (i : Fin 10) : chunk (1060+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1070 (i : Fin 10) : chunk (1070+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1080 (i : Fin 10) : chunk (1080+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1090 (i : Fin 10) : chunk (1090+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1100 (i : Fin 10) : chunk (1100+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1110 (i : Fin 10) : chunk (1110+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1120 (i : Fin 10) : chunk (1120+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1130 (i : Fin 10) : chunk (1130+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1140 (i : Fin 10) : chunk (1140+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1150 (i : Fin 10) : chunk (1150+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1160 (i : Fin 10) : chunk (1160+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1170 (i : Fin 10) : chunk (1170+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1180 (i : Fin 10) : chunk (1180+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1190 (i : Fin 10) : chunk (1190+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1200 (i : Fin 10) : chunk (1200+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1210 (i : Fin 10) : chunk (1210+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1220 (i : Fin 10) : chunk (1220+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1230 (i : Fin 10) : chunk (1230+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1240 (i : Fin 10) : chunk (1240+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1250 (i : Fin 10) : chunk (1250+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1260 (i : Fin 10) : chunk (1260+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1270 (i : Fin 10) : chunk (1270+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1280 (i : Fin 10) : chunk (1280+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1290 (i : Fin 10) : chunk (1290+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1300 (i : Fin 10) : chunk (1300+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1310 (i : Fin 10) : chunk (1310+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1320 (i : Fin 10) : chunk (1320+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1330 (i : Fin 10) : chunk (1330+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1340 (i : Fin 10) : chunk (1340+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1350 (i : Fin 10) : chunk (1350+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1360 (i : Fin 10) : chunk (1360+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1370 (i : Fin 10) : chunk (1370+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1380 (i : Fin 10) : chunk (1380+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1390 (i : Fin 10) : chunk (1390+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1400 (i : Fin 10) : chunk (1400+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1410 (i : Fin 10) : chunk (1410+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1420 (i : Fin 10) : chunk (1420+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1430 (i : Fin 10) : chunk (1430+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1440 (i : Fin 10) : chunk (1440+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1450 (i : Fin 10) : chunk (1450+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1460 (i : Fin 10) : chunk (1460+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1470 (i : Fin 10) : chunk (1470+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1480 (i : Fin 10) : chunk (1480+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1490 (i : Fin 10) : chunk (1490+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1500 (i : Fin 10) : chunk (1500+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1510 (i : Fin 10) : chunk (1510+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1520 (i : Fin 10) : chunk (1520+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1530 (i : Fin 10) : chunk (1530+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1540 (i : Fin 10) : chunk (1540+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1550 (i : Fin 10) : chunk (1550+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1560 (i : Fin 10) : chunk (1560+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1570 (i : Fin 10) : chunk (1570+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1580 (i : Fin 10) : chunk (1580+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1590 (i : Fin 10) : chunk (1590+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1600 (i : Fin 10) : chunk (1600+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1610 (i : Fin 10) : chunk (1610+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1620 (i : Fin 10) : chunk (1620+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1630 (i : Fin 10) : chunk (1630+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1640 (i : Fin 10) : chunk (1640+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1650 (i : Fin 10) : chunk (1650+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1660 (i : Fin 10) : chunk (1660+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1670 (i : Fin 10) : chunk (1670+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1680 (i : Fin 10) : chunk (1680+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1690 (i : Fin 10) : chunk (1690+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1700 (i : Fin 10) : chunk (1700+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1710 (i : Fin 10) : chunk (1710+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1720 (i : Fin 10) : chunk (1720+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1730 (i : Fin 10) : chunk (1730+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1740 (i : Fin 10) : chunk (1740+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1750 (i : Fin 10) : chunk (1750+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1760 (i : Fin 10) : chunk (1760+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1770 (i : Fin 10) : chunk (1770+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1780 (i : Fin 10) : chunk (1780+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1790 (i : Fin 10) : chunk (1790+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1800 (i : Fin 10) : chunk (1800+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1810 (i : Fin 10) : chunk (1810+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1820 (i : Fin 10) : chunk (1820+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1830 (i : Fin 10) : chunk (1830+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1840 (i : Fin 10) : chunk (1840+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1850 (i : Fin 10) : chunk (1850+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1860 (i : Fin 10) : chunk (1860+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1870 (i : Fin 10) : chunk (1870+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1880 (i : Fin 10) : chunk (1880+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1890 (i : Fin 10) : chunk (1890+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1900 (i : Fin 10) : chunk (1900+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1910 (i : Fin 10) : chunk (1910+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1920 (i : Fin 10) : chunk (1920+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1930 (i : Fin 10) : chunk (1930+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1940 (i : Fin 10) : chunk (1940+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1950 (i : Fin 10) : chunk (1950+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1960 (i : Fin 10) : chunk (1960+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1970 (i : Fin 10) : chunk (1970+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1980 (i : Fin 10) : chunk (1980+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud1990 (i : Fin 10) : chunk (1990+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2000 (i : Fin 10) : chunk (2000+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2010 (i : Fin 10) : chunk (2010+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2020 (i : Fin 10) : chunk (2020+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2030 (i : Fin 10) : chunk (2030+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2040 (i : Fin 10) : chunk (2040+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2050 (i : Fin 10) : chunk (2050+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2060 (i : Fin 10) : chunk (2060+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2070 (i : Fin 10) : chunk (2070+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2080 (i : Fin 10) : chunk (2080+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2090 (i : Fin 10) : chunk (2090+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2100 (i : Fin 10) : chunk (2100+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2110 (i : Fin 10) : chunk (2110+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2120 (i : Fin 10) : chunk (2120+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2130 (i : Fin 10) : chunk (2130+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2140 (i : Fin 10) : chunk (2140+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2150 (i : Fin 10) : chunk (2150+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2160 (i : Fin 10) : chunk (2160+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2170 (i : Fin 10) : chunk (2170+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2180 (i : Fin 10) : chunk (2180+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2190 (i : Fin 10) : chunk (2190+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2200 (i : Fin 10) : chunk (2200+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2210 (i : Fin 10) : chunk (2210+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2220 (i : Fin 10) : chunk (2220+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2230 (i : Fin 10) : chunk (2230+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2240 (i : Fin 10) : chunk (2240+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2250 (i : Fin 10) : chunk (2250+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2260 (i : Fin 10) : chunk (2260+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2270 (i : Fin 10) : chunk (2270+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2280 (i : Fin 10) : chunk (2280+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2290 (i : Fin 10) : chunk (2290+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2300 (i : Fin 10) : chunk (2300+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2310 (i : Fin 10) : chunk (2310+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2320 (i : Fin 10) : chunk (2320+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2330 (i : Fin 10) : chunk (2330+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2340 (i : Fin 10) : chunk (2340+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2350 (i : Fin 10) : chunk (2350+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2360 (i : Fin 10) : chunk (2360+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2370 (i : Fin 10) : chunk (2370+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2380 (i : Fin 10) : chunk (2380+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2390 (i : Fin 10) : chunk (2390+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2400 (i : Fin 10) : chunk (2400+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2410 (i : Fin 10) : chunk (2410+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2420 (i : Fin 10) : chunk (2420+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2430 (i : Fin 10) : chunk (2430+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2440 (i : Fin 10) : chunk (2440+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2450 (i : Fin 10) : chunk (2450+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2460 (i : Fin 10) : chunk (2460+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2470 (i : Fin 10) : chunk (2470+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2480 (i : Fin 10) : chunk (2480+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2490 (i : Fin 10) : chunk (2490+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2500 (i : Fin 10) : chunk (2500+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2510 (i : Fin 10) : chunk (2510+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2520 (i : Fin 10) : chunk (2520+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2530 (i : Fin 10) : chunk (2530+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2540 (i : Fin 10) : chunk (2540+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2550 (i : Fin 10) : chunk (2550+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2560 (i : Fin 10) : chunk (2560+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2570 (i : Fin 10) : chunk (2570+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2580 (i : Fin 10) : chunk (2580+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2590 (i : Fin 10) : chunk (2590+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2600 (i : Fin 10) : chunk (2600+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2610 (i : Fin 10) : chunk (2610+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2620 (i : Fin 10) : chunk (2620+i.val)=true := by decide +kernel +revert
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem aud2630 (i : Fin 10) : chunk (2630+i.val)=true := by decide +kernel +revert
set_option maxHeartbeats 0 in
set_option maxRecDepth 4000 in
private theorem checked (c : ℕ) (h : c<2640) : chunk c=true := by
  by_cases h1320 : c<1320
  · by_cases h660 : c<660
    · by_cases h330 : c<330
      · by_cases h160 : c<160
        · by_cases h80 : c<80
          · by_cases h40 : c<40
            · by_cases h20 : c<20
              · by_cases h10 : c<10
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 0+(c-0)=c by omega] using aud0 ⟨c-0,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 10+(c-10)=c by omega] using aud10 ⟨c-10,by omega⟩)
              · by_cases h30 : c<30
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 20+(c-20)=c by omega] using aud20 ⟨c-20,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 30+(c-30)=c by omega] using aud30 ⟨c-30,by omega⟩)
            · by_cases h60 : c<60
              · by_cases h50 : c<50
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 40+(c-40)=c by omega] using aud40 ⟨c-40,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 50+(c-50)=c by omega] using aud50 ⟨c-50,by omega⟩)
              · by_cases h70 : c<70
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 60+(c-60)=c by omega] using aud60 ⟨c-60,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 70+(c-70)=c by omega] using aud70 ⟨c-70,by omega⟩)
          · by_cases h120 : c<120
            · by_cases h100 : c<100
              · by_cases h90 : c<90
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 80+(c-80)=c by omega] using aud80 ⟨c-80,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 90+(c-90)=c by omega] using aud90 ⟨c-90,by omega⟩)
              · by_cases h110 : c<110
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 100+(c-100)=c by omega] using aud100 ⟨c-100,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 110+(c-110)=c by omega] using aud110 ⟨c-110,by omega⟩)
            · by_cases h140 : c<140
              · by_cases h130 : c<130
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 120+(c-120)=c by omega] using aud120 ⟨c-120,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 130+(c-130)=c by omega] using aud130 ⟨c-130,by omega⟩)
              · by_cases h150 : c<150
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 140+(c-140)=c by omega] using aud140 ⟨c-140,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 150+(c-150)=c by omega] using aud150 ⟨c-150,by omega⟩)
        · by_cases h240 : c<240
          · by_cases h200 : c<200
            · by_cases h180 : c<180
              · by_cases h170 : c<170
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 160+(c-160)=c by omega] using aud160 ⟨c-160,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 170+(c-170)=c by omega] using aud170 ⟨c-170,by omega⟩)
              · by_cases h190 : c<190
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 180+(c-180)=c by omega] using aud180 ⟨c-180,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 190+(c-190)=c by omega] using aud190 ⟨c-190,by omega⟩)
            · by_cases h220 : c<220
              · by_cases h210 : c<210
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 200+(c-200)=c by omega] using aud200 ⟨c-200,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 210+(c-210)=c by omega] using aud210 ⟨c-210,by omega⟩)
              · by_cases h230 : c<230
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 220+(c-220)=c by omega] using aud220 ⟨c-220,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 230+(c-230)=c by omega] using aud230 ⟨c-230,by omega⟩)
          · by_cases h280 : c<280
            · by_cases h260 : c<260
              · by_cases h250 : c<250
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 240+(c-240)=c by omega] using aud240 ⟨c-240,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 250+(c-250)=c by omega] using aud250 ⟨c-250,by omega⟩)
              · by_cases h270 : c<270
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 260+(c-260)=c by omega] using aud260 ⟨c-260,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 270+(c-270)=c by omega] using aud270 ⟨c-270,by omega⟩)
            · by_cases h300 : c<300
              · by_cases h290 : c<290
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 280+(c-280)=c by omega] using aud280 ⟨c-280,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 290+(c-290)=c by omega] using aud290 ⟨c-290,by omega⟩)
              · by_cases h310 : c<310
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 300+(c-300)=c by omega] using aud300 ⟨c-300,by omega⟩)
                · by_cases h320 : c<320
                  · exact (show chunk c=true by simpa only [Fin.val_mk,show 310+(c-310)=c by omega] using aud310 ⟨c-310,by omega⟩)
                  · exact (show chunk c=true by simpa only [Fin.val_mk,show 320+(c-320)=c by omega] using aud320 ⟨c-320,by omega⟩)
      · by_cases h490 : c<490
        · by_cases h410 : c<410
          · by_cases h370 : c<370
            · by_cases h350 : c<350
              · by_cases h340 : c<340
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 330+(c-330)=c by omega] using aud330 ⟨c-330,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 340+(c-340)=c by omega] using aud340 ⟨c-340,by omega⟩)
              · by_cases h360 : c<360
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 350+(c-350)=c by omega] using aud350 ⟨c-350,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 360+(c-360)=c by omega] using aud360 ⟨c-360,by omega⟩)
            · by_cases h390 : c<390
              · by_cases h380 : c<380
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 370+(c-370)=c by omega] using aud370 ⟨c-370,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 380+(c-380)=c by omega] using aud380 ⟨c-380,by omega⟩)
              · by_cases h400 : c<400
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 390+(c-390)=c by omega] using aud390 ⟨c-390,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 400+(c-400)=c by omega] using aud400 ⟨c-400,by omega⟩)
          · by_cases h450 : c<450
            · by_cases h430 : c<430
              · by_cases h420 : c<420
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 410+(c-410)=c by omega] using aud410 ⟨c-410,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 420+(c-420)=c by omega] using aud420 ⟨c-420,by omega⟩)
              · by_cases h440 : c<440
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 430+(c-430)=c by omega] using aud430 ⟨c-430,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 440+(c-440)=c by omega] using aud440 ⟨c-440,by omega⟩)
            · by_cases h470 : c<470
              · by_cases h460 : c<460
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 450+(c-450)=c by omega] using aud450 ⟨c-450,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 460+(c-460)=c by omega] using aud460 ⟨c-460,by omega⟩)
              · by_cases h480 : c<480
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 470+(c-470)=c by omega] using aud470 ⟨c-470,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 480+(c-480)=c by omega] using aud480 ⟨c-480,by omega⟩)
        · by_cases h570 : c<570
          · by_cases h530 : c<530
            · by_cases h510 : c<510
              · by_cases h500 : c<500
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 490+(c-490)=c by omega] using aud490 ⟨c-490,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 500+(c-500)=c by omega] using aud500 ⟨c-500,by omega⟩)
              · by_cases h520 : c<520
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 510+(c-510)=c by omega] using aud510 ⟨c-510,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 520+(c-520)=c by omega] using aud520 ⟨c-520,by omega⟩)
            · by_cases h550 : c<550
              · by_cases h540 : c<540
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 530+(c-530)=c by omega] using aud530 ⟨c-530,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 540+(c-540)=c by omega] using aud540 ⟨c-540,by omega⟩)
              · by_cases h560 : c<560
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 550+(c-550)=c by omega] using aud550 ⟨c-550,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 560+(c-560)=c by omega] using aud560 ⟨c-560,by omega⟩)
          · by_cases h610 : c<610
            · by_cases h590 : c<590
              · by_cases h580 : c<580
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 570+(c-570)=c by omega] using aud570 ⟨c-570,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 580+(c-580)=c by omega] using aud580 ⟨c-580,by omega⟩)
              · by_cases h600 : c<600
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 590+(c-590)=c by omega] using aud590 ⟨c-590,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 600+(c-600)=c by omega] using aud600 ⟨c-600,by omega⟩)
            · by_cases h630 : c<630
              · by_cases h620 : c<620
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 610+(c-610)=c by omega] using aud610 ⟨c-610,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 620+(c-620)=c by omega] using aud620 ⟨c-620,by omega⟩)
              · by_cases h640 : c<640
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 630+(c-630)=c by omega] using aud630 ⟨c-630,by omega⟩)
                · by_cases h650 : c<650
                  · exact (show chunk c=true by simpa only [Fin.val_mk,show 640+(c-640)=c by omega] using aud640 ⟨c-640,by omega⟩)
                  · exact (show chunk c=true by simpa only [Fin.val_mk,show 650+(c-650)=c by omega] using aud650 ⟨c-650,by omega⟩)
    · by_cases h990 : c<990
      · by_cases h820 : c<820
        · by_cases h740 : c<740
          · by_cases h700 : c<700
            · by_cases h680 : c<680
              · by_cases h670 : c<670
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 660+(c-660)=c by omega] using aud660 ⟨c-660,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 670+(c-670)=c by omega] using aud670 ⟨c-670,by omega⟩)
              · by_cases h690 : c<690
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 680+(c-680)=c by omega] using aud680 ⟨c-680,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 690+(c-690)=c by omega] using aud690 ⟨c-690,by omega⟩)
            · by_cases h720 : c<720
              · by_cases h710 : c<710
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 700+(c-700)=c by omega] using aud700 ⟨c-700,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 710+(c-710)=c by omega] using aud710 ⟨c-710,by omega⟩)
              · by_cases h730 : c<730
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 720+(c-720)=c by omega] using aud720 ⟨c-720,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 730+(c-730)=c by omega] using aud730 ⟨c-730,by omega⟩)
          · by_cases h780 : c<780
            · by_cases h760 : c<760
              · by_cases h750 : c<750
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 740+(c-740)=c by omega] using aud740 ⟨c-740,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 750+(c-750)=c by omega] using aud750 ⟨c-750,by omega⟩)
              · by_cases h770 : c<770
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 760+(c-760)=c by omega] using aud760 ⟨c-760,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 770+(c-770)=c by omega] using aud770 ⟨c-770,by omega⟩)
            · by_cases h800 : c<800
              · by_cases h790 : c<790
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 780+(c-780)=c by omega] using aud780 ⟨c-780,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 790+(c-790)=c by omega] using aud790 ⟨c-790,by omega⟩)
              · by_cases h810 : c<810
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 800+(c-800)=c by omega] using aud800 ⟨c-800,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 810+(c-810)=c by omega] using aud810 ⟨c-810,by omega⟩)
        · by_cases h900 : c<900
          · by_cases h860 : c<860
            · by_cases h840 : c<840
              · by_cases h830 : c<830
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 820+(c-820)=c by omega] using aud820 ⟨c-820,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 830+(c-830)=c by omega] using aud830 ⟨c-830,by omega⟩)
              · by_cases h850 : c<850
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 840+(c-840)=c by omega] using aud840 ⟨c-840,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 850+(c-850)=c by omega] using aud850 ⟨c-850,by omega⟩)
            · by_cases h880 : c<880
              · by_cases h870 : c<870
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 860+(c-860)=c by omega] using aud860 ⟨c-860,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 870+(c-870)=c by omega] using aud870 ⟨c-870,by omega⟩)
              · by_cases h890 : c<890
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 880+(c-880)=c by omega] using aud880 ⟨c-880,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 890+(c-890)=c by omega] using aud890 ⟨c-890,by omega⟩)
          · by_cases h940 : c<940
            · by_cases h920 : c<920
              · by_cases h910 : c<910
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 900+(c-900)=c by omega] using aud900 ⟨c-900,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 910+(c-910)=c by omega] using aud910 ⟨c-910,by omega⟩)
              · by_cases h930 : c<930
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 920+(c-920)=c by omega] using aud920 ⟨c-920,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 930+(c-930)=c by omega] using aud930 ⟨c-930,by omega⟩)
            · by_cases h960 : c<960
              · by_cases h950 : c<950
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 940+(c-940)=c by omega] using aud940 ⟨c-940,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 950+(c-950)=c by omega] using aud950 ⟨c-950,by omega⟩)
              · by_cases h970 : c<970
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 960+(c-960)=c by omega] using aud960 ⟨c-960,by omega⟩)
                · by_cases h980 : c<980
                  · exact (show chunk c=true by simpa only [Fin.val_mk,show 970+(c-970)=c by omega] using aud970 ⟨c-970,by omega⟩)
                  · exact (show chunk c=true by simpa only [Fin.val_mk,show 980+(c-980)=c by omega] using aud980 ⟨c-980,by omega⟩)
      · by_cases h1150 : c<1150
        · by_cases h1070 : c<1070
          · by_cases h1030 : c<1030
            · by_cases h1010 : c<1010
              · by_cases h1000 : c<1000
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 990+(c-990)=c by omega] using aud990 ⟨c-990,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1000+(c-1000)=c by omega] using aud1000 ⟨c-1000,by omega⟩)
              · by_cases h1020 : c<1020
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1010+(c-1010)=c by omega] using aud1010 ⟨c-1010,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1020+(c-1020)=c by omega] using aud1020 ⟨c-1020,by omega⟩)
            · by_cases h1050 : c<1050
              · by_cases h1040 : c<1040
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1030+(c-1030)=c by omega] using aud1030 ⟨c-1030,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1040+(c-1040)=c by omega] using aud1040 ⟨c-1040,by omega⟩)
              · by_cases h1060 : c<1060
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1050+(c-1050)=c by omega] using aud1050 ⟨c-1050,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1060+(c-1060)=c by omega] using aud1060 ⟨c-1060,by omega⟩)
          · by_cases h1110 : c<1110
            · by_cases h1090 : c<1090
              · by_cases h1080 : c<1080
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1070+(c-1070)=c by omega] using aud1070 ⟨c-1070,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1080+(c-1080)=c by omega] using aud1080 ⟨c-1080,by omega⟩)
              · by_cases h1100 : c<1100
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1090+(c-1090)=c by omega] using aud1090 ⟨c-1090,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1100+(c-1100)=c by omega] using aud1100 ⟨c-1100,by omega⟩)
            · by_cases h1130 : c<1130
              · by_cases h1120 : c<1120
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1110+(c-1110)=c by omega] using aud1110 ⟨c-1110,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1120+(c-1120)=c by omega] using aud1120 ⟨c-1120,by omega⟩)
              · by_cases h1140 : c<1140
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1130+(c-1130)=c by omega] using aud1130 ⟨c-1130,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1140+(c-1140)=c by omega] using aud1140 ⟨c-1140,by omega⟩)
        · by_cases h1230 : c<1230
          · by_cases h1190 : c<1190
            · by_cases h1170 : c<1170
              · by_cases h1160 : c<1160
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1150+(c-1150)=c by omega] using aud1150 ⟨c-1150,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1160+(c-1160)=c by omega] using aud1160 ⟨c-1160,by omega⟩)
              · by_cases h1180 : c<1180
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1170+(c-1170)=c by omega] using aud1170 ⟨c-1170,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1180+(c-1180)=c by omega] using aud1180 ⟨c-1180,by omega⟩)
            · by_cases h1210 : c<1210
              · by_cases h1200 : c<1200
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1190+(c-1190)=c by omega] using aud1190 ⟨c-1190,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1200+(c-1200)=c by omega] using aud1200 ⟨c-1200,by omega⟩)
              · by_cases h1220 : c<1220
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1210+(c-1210)=c by omega] using aud1210 ⟨c-1210,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1220+(c-1220)=c by omega] using aud1220 ⟨c-1220,by omega⟩)
          · by_cases h1270 : c<1270
            · by_cases h1250 : c<1250
              · by_cases h1240 : c<1240
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1230+(c-1230)=c by omega] using aud1230 ⟨c-1230,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1240+(c-1240)=c by omega] using aud1240 ⟨c-1240,by omega⟩)
              · by_cases h1260 : c<1260
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1250+(c-1250)=c by omega] using aud1250 ⟨c-1250,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1260+(c-1260)=c by omega] using aud1260 ⟨c-1260,by omega⟩)
            · by_cases h1290 : c<1290
              · by_cases h1280 : c<1280
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1270+(c-1270)=c by omega] using aud1270 ⟨c-1270,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1280+(c-1280)=c by omega] using aud1280 ⟨c-1280,by omega⟩)
              · by_cases h1300 : c<1300
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1290+(c-1290)=c by omega] using aud1290 ⟨c-1290,by omega⟩)
                · by_cases h1310 : c<1310
                  · exact (show chunk c=true by simpa only [Fin.val_mk,show 1300+(c-1300)=c by omega] using aud1300 ⟨c-1300,by omega⟩)
                  · exact (show chunk c=true by simpa only [Fin.val_mk,show 1310+(c-1310)=c by omega] using aud1310 ⟨c-1310,by omega⟩)
  · by_cases h1980 : c<1980
    · by_cases h1650 : c<1650
      · by_cases h1480 : c<1480
        · by_cases h1400 : c<1400
          · by_cases h1360 : c<1360
            · by_cases h1340 : c<1340
              · by_cases h1330 : c<1330
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1320+(c-1320)=c by omega] using aud1320 ⟨c-1320,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1330+(c-1330)=c by omega] using aud1330 ⟨c-1330,by omega⟩)
              · by_cases h1350 : c<1350
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1340+(c-1340)=c by omega] using aud1340 ⟨c-1340,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1350+(c-1350)=c by omega] using aud1350 ⟨c-1350,by omega⟩)
            · by_cases h1380 : c<1380
              · by_cases h1370 : c<1370
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1360+(c-1360)=c by omega] using aud1360 ⟨c-1360,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1370+(c-1370)=c by omega] using aud1370 ⟨c-1370,by omega⟩)
              · by_cases h1390 : c<1390
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1380+(c-1380)=c by omega] using aud1380 ⟨c-1380,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1390+(c-1390)=c by omega] using aud1390 ⟨c-1390,by omega⟩)
          · by_cases h1440 : c<1440
            · by_cases h1420 : c<1420
              · by_cases h1410 : c<1410
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1400+(c-1400)=c by omega] using aud1400 ⟨c-1400,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1410+(c-1410)=c by omega] using aud1410 ⟨c-1410,by omega⟩)
              · by_cases h1430 : c<1430
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1420+(c-1420)=c by omega] using aud1420 ⟨c-1420,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1430+(c-1430)=c by omega] using aud1430 ⟨c-1430,by omega⟩)
            · by_cases h1460 : c<1460
              · by_cases h1450 : c<1450
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1440+(c-1440)=c by omega] using aud1440 ⟨c-1440,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1450+(c-1450)=c by omega] using aud1450 ⟨c-1450,by omega⟩)
              · by_cases h1470 : c<1470
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1460+(c-1460)=c by omega] using aud1460 ⟨c-1460,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1470+(c-1470)=c by omega] using aud1470 ⟨c-1470,by omega⟩)
        · by_cases h1560 : c<1560
          · by_cases h1520 : c<1520
            · by_cases h1500 : c<1500
              · by_cases h1490 : c<1490
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1480+(c-1480)=c by omega] using aud1480 ⟨c-1480,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1490+(c-1490)=c by omega] using aud1490 ⟨c-1490,by omega⟩)
              · by_cases h1510 : c<1510
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1500+(c-1500)=c by omega] using aud1500 ⟨c-1500,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1510+(c-1510)=c by omega] using aud1510 ⟨c-1510,by omega⟩)
            · by_cases h1540 : c<1540
              · by_cases h1530 : c<1530
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1520+(c-1520)=c by omega] using aud1520 ⟨c-1520,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1530+(c-1530)=c by omega] using aud1530 ⟨c-1530,by omega⟩)
              · by_cases h1550 : c<1550
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1540+(c-1540)=c by omega] using aud1540 ⟨c-1540,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1550+(c-1550)=c by omega] using aud1550 ⟨c-1550,by omega⟩)
          · by_cases h1600 : c<1600
            · by_cases h1580 : c<1580
              · by_cases h1570 : c<1570
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1560+(c-1560)=c by omega] using aud1560 ⟨c-1560,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1570+(c-1570)=c by omega] using aud1570 ⟨c-1570,by omega⟩)
              · by_cases h1590 : c<1590
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1580+(c-1580)=c by omega] using aud1580 ⟨c-1580,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1590+(c-1590)=c by omega] using aud1590 ⟨c-1590,by omega⟩)
            · by_cases h1620 : c<1620
              · by_cases h1610 : c<1610
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1600+(c-1600)=c by omega] using aud1600 ⟨c-1600,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1610+(c-1610)=c by omega] using aud1610 ⟨c-1610,by omega⟩)
              · by_cases h1630 : c<1630
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1620+(c-1620)=c by omega] using aud1620 ⟨c-1620,by omega⟩)
                · by_cases h1640 : c<1640
                  · exact (show chunk c=true by simpa only [Fin.val_mk,show 1630+(c-1630)=c by omega] using aud1630 ⟨c-1630,by omega⟩)
                  · exact (show chunk c=true by simpa only [Fin.val_mk,show 1640+(c-1640)=c by omega] using aud1640 ⟨c-1640,by omega⟩)
      · by_cases h1810 : c<1810
        · by_cases h1730 : c<1730
          · by_cases h1690 : c<1690
            · by_cases h1670 : c<1670
              · by_cases h1660 : c<1660
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1650+(c-1650)=c by omega] using aud1650 ⟨c-1650,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1660+(c-1660)=c by omega] using aud1660 ⟨c-1660,by omega⟩)
              · by_cases h1680 : c<1680
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1670+(c-1670)=c by omega] using aud1670 ⟨c-1670,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1680+(c-1680)=c by omega] using aud1680 ⟨c-1680,by omega⟩)
            · by_cases h1710 : c<1710
              · by_cases h1700 : c<1700
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1690+(c-1690)=c by omega] using aud1690 ⟨c-1690,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1700+(c-1700)=c by omega] using aud1700 ⟨c-1700,by omega⟩)
              · by_cases h1720 : c<1720
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1710+(c-1710)=c by omega] using aud1710 ⟨c-1710,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1720+(c-1720)=c by omega] using aud1720 ⟨c-1720,by omega⟩)
          · by_cases h1770 : c<1770
            · by_cases h1750 : c<1750
              · by_cases h1740 : c<1740
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1730+(c-1730)=c by omega] using aud1730 ⟨c-1730,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1740+(c-1740)=c by omega] using aud1740 ⟨c-1740,by omega⟩)
              · by_cases h1760 : c<1760
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1750+(c-1750)=c by omega] using aud1750 ⟨c-1750,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1760+(c-1760)=c by omega] using aud1760 ⟨c-1760,by omega⟩)
            · by_cases h1790 : c<1790
              · by_cases h1780 : c<1780
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1770+(c-1770)=c by omega] using aud1770 ⟨c-1770,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1780+(c-1780)=c by omega] using aud1780 ⟨c-1780,by omega⟩)
              · by_cases h1800 : c<1800
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1790+(c-1790)=c by omega] using aud1790 ⟨c-1790,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1800+(c-1800)=c by omega] using aud1800 ⟨c-1800,by omega⟩)
        · by_cases h1890 : c<1890
          · by_cases h1850 : c<1850
            · by_cases h1830 : c<1830
              · by_cases h1820 : c<1820
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1810+(c-1810)=c by omega] using aud1810 ⟨c-1810,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1820+(c-1820)=c by omega] using aud1820 ⟨c-1820,by omega⟩)
              · by_cases h1840 : c<1840
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1830+(c-1830)=c by omega] using aud1830 ⟨c-1830,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1840+(c-1840)=c by omega] using aud1840 ⟨c-1840,by omega⟩)
            · by_cases h1870 : c<1870
              · by_cases h1860 : c<1860
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1850+(c-1850)=c by omega] using aud1850 ⟨c-1850,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1860+(c-1860)=c by omega] using aud1860 ⟨c-1860,by omega⟩)
              · by_cases h1880 : c<1880
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1870+(c-1870)=c by omega] using aud1870 ⟨c-1870,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1880+(c-1880)=c by omega] using aud1880 ⟨c-1880,by omega⟩)
          · by_cases h1930 : c<1930
            · by_cases h1910 : c<1910
              · by_cases h1900 : c<1900
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1890+(c-1890)=c by omega] using aud1890 ⟨c-1890,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1900+(c-1900)=c by omega] using aud1900 ⟨c-1900,by omega⟩)
              · by_cases h1920 : c<1920
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1910+(c-1910)=c by omega] using aud1910 ⟨c-1910,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1920+(c-1920)=c by omega] using aud1920 ⟨c-1920,by omega⟩)
            · by_cases h1950 : c<1950
              · by_cases h1940 : c<1940
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1930+(c-1930)=c by omega] using aud1930 ⟨c-1930,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1940+(c-1940)=c by omega] using aud1940 ⟨c-1940,by omega⟩)
              · by_cases h1960 : c<1960
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1950+(c-1950)=c by omega] using aud1950 ⟨c-1950,by omega⟩)
                · by_cases h1970 : c<1970
                  · exact (show chunk c=true by simpa only [Fin.val_mk,show 1960+(c-1960)=c by omega] using aud1960 ⟨c-1960,by omega⟩)
                  · exact (show chunk c=true by simpa only [Fin.val_mk,show 1970+(c-1970)=c by omega] using aud1970 ⟨c-1970,by omega⟩)
    · by_cases h2310 : c<2310
      · by_cases h2140 : c<2140
        · by_cases h2060 : c<2060
          · by_cases h2020 : c<2020
            · by_cases h2000 : c<2000
              · by_cases h1990 : c<1990
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1980+(c-1980)=c by omega] using aud1980 ⟨c-1980,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 1990+(c-1990)=c by omega] using aud1990 ⟨c-1990,by omega⟩)
              · by_cases h2010 : c<2010
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2000+(c-2000)=c by omega] using aud2000 ⟨c-2000,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2010+(c-2010)=c by omega] using aud2010 ⟨c-2010,by omega⟩)
            · by_cases h2040 : c<2040
              · by_cases h2030 : c<2030
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2020+(c-2020)=c by omega] using aud2020 ⟨c-2020,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2030+(c-2030)=c by omega] using aud2030 ⟨c-2030,by omega⟩)
              · by_cases h2050 : c<2050
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2040+(c-2040)=c by omega] using aud2040 ⟨c-2040,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2050+(c-2050)=c by omega] using aud2050 ⟨c-2050,by omega⟩)
          · by_cases h2100 : c<2100
            · by_cases h2080 : c<2080
              · by_cases h2070 : c<2070
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2060+(c-2060)=c by omega] using aud2060 ⟨c-2060,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2070+(c-2070)=c by omega] using aud2070 ⟨c-2070,by omega⟩)
              · by_cases h2090 : c<2090
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2080+(c-2080)=c by omega] using aud2080 ⟨c-2080,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2090+(c-2090)=c by omega] using aud2090 ⟨c-2090,by omega⟩)
            · by_cases h2120 : c<2120
              · by_cases h2110 : c<2110
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2100+(c-2100)=c by omega] using aud2100 ⟨c-2100,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2110+(c-2110)=c by omega] using aud2110 ⟨c-2110,by omega⟩)
              · by_cases h2130 : c<2130
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2120+(c-2120)=c by omega] using aud2120 ⟨c-2120,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2130+(c-2130)=c by omega] using aud2130 ⟨c-2130,by omega⟩)
        · by_cases h2220 : c<2220
          · by_cases h2180 : c<2180
            · by_cases h2160 : c<2160
              · by_cases h2150 : c<2150
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2140+(c-2140)=c by omega] using aud2140 ⟨c-2140,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2150+(c-2150)=c by omega] using aud2150 ⟨c-2150,by omega⟩)
              · by_cases h2170 : c<2170
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2160+(c-2160)=c by omega] using aud2160 ⟨c-2160,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2170+(c-2170)=c by omega] using aud2170 ⟨c-2170,by omega⟩)
            · by_cases h2200 : c<2200
              · by_cases h2190 : c<2190
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2180+(c-2180)=c by omega] using aud2180 ⟨c-2180,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2190+(c-2190)=c by omega] using aud2190 ⟨c-2190,by omega⟩)
              · by_cases h2210 : c<2210
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2200+(c-2200)=c by omega] using aud2200 ⟨c-2200,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2210+(c-2210)=c by omega] using aud2210 ⟨c-2210,by omega⟩)
          · by_cases h2260 : c<2260
            · by_cases h2240 : c<2240
              · by_cases h2230 : c<2230
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2220+(c-2220)=c by omega] using aud2220 ⟨c-2220,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2230+(c-2230)=c by omega] using aud2230 ⟨c-2230,by omega⟩)
              · by_cases h2250 : c<2250
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2240+(c-2240)=c by omega] using aud2240 ⟨c-2240,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2250+(c-2250)=c by omega] using aud2250 ⟨c-2250,by omega⟩)
            · by_cases h2280 : c<2280
              · by_cases h2270 : c<2270
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2260+(c-2260)=c by omega] using aud2260 ⟨c-2260,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2270+(c-2270)=c by omega] using aud2270 ⟨c-2270,by omega⟩)
              · by_cases h2290 : c<2290
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2280+(c-2280)=c by omega] using aud2280 ⟨c-2280,by omega⟩)
                · by_cases h2300 : c<2300
                  · exact (show chunk c=true by simpa only [Fin.val_mk,show 2290+(c-2290)=c by omega] using aud2290 ⟨c-2290,by omega⟩)
                  · exact (show chunk c=true by simpa only [Fin.val_mk,show 2300+(c-2300)=c by omega] using aud2300 ⟨c-2300,by omega⟩)
      · by_cases h2470 : c<2470
        · by_cases h2390 : c<2390
          · by_cases h2350 : c<2350
            · by_cases h2330 : c<2330
              · by_cases h2320 : c<2320
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2310+(c-2310)=c by omega] using aud2310 ⟨c-2310,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2320+(c-2320)=c by omega] using aud2320 ⟨c-2320,by omega⟩)
              · by_cases h2340 : c<2340
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2330+(c-2330)=c by omega] using aud2330 ⟨c-2330,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2340+(c-2340)=c by omega] using aud2340 ⟨c-2340,by omega⟩)
            · by_cases h2370 : c<2370
              · by_cases h2360 : c<2360
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2350+(c-2350)=c by omega] using aud2350 ⟨c-2350,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2360+(c-2360)=c by omega] using aud2360 ⟨c-2360,by omega⟩)
              · by_cases h2380 : c<2380
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2370+(c-2370)=c by omega] using aud2370 ⟨c-2370,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2380+(c-2380)=c by omega] using aud2380 ⟨c-2380,by omega⟩)
          · by_cases h2430 : c<2430
            · by_cases h2410 : c<2410
              · by_cases h2400 : c<2400
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2390+(c-2390)=c by omega] using aud2390 ⟨c-2390,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2400+(c-2400)=c by omega] using aud2400 ⟨c-2400,by omega⟩)
              · by_cases h2420 : c<2420
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2410+(c-2410)=c by omega] using aud2410 ⟨c-2410,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2420+(c-2420)=c by omega] using aud2420 ⟨c-2420,by omega⟩)
            · by_cases h2450 : c<2450
              · by_cases h2440 : c<2440
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2430+(c-2430)=c by omega] using aud2430 ⟨c-2430,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2440+(c-2440)=c by omega] using aud2440 ⟨c-2440,by omega⟩)
              · by_cases h2460 : c<2460
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2450+(c-2450)=c by omega] using aud2450 ⟨c-2450,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2460+(c-2460)=c by omega] using aud2460 ⟨c-2460,by omega⟩)
        · by_cases h2550 : c<2550
          · by_cases h2510 : c<2510
            · by_cases h2490 : c<2490
              · by_cases h2480 : c<2480
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2470+(c-2470)=c by omega] using aud2470 ⟨c-2470,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2480+(c-2480)=c by omega] using aud2480 ⟨c-2480,by omega⟩)
              · by_cases h2500 : c<2500
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2490+(c-2490)=c by omega] using aud2490 ⟨c-2490,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2500+(c-2500)=c by omega] using aud2500 ⟨c-2500,by omega⟩)
            · by_cases h2530 : c<2530
              · by_cases h2520 : c<2520
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2510+(c-2510)=c by omega] using aud2510 ⟨c-2510,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2520+(c-2520)=c by omega] using aud2520 ⟨c-2520,by omega⟩)
              · by_cases h2540 : c<2540
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2530+(c-2530)=c by omega] using aud2530 ⟨c-2530,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2540+(c-2540)=c by omega] using aud2540 ⟨c-2540,by omega⟩)
          · by_cases h2590 : c<2590
            · by_cases h2570 : c<2570
              · by_cases h2560 : c<2560
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2550+(c-2550)=c by omega] using aud2550 ⟨c-2550,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2560+(c-2560)=c by omega] using aud2560 ⟨c-2560,by omega⟩)
              · by_cases h2580 : c<2580
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2570+(c-2570)=c by omega] using aud2570 ⟨c-2570,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2580+(c-2580)=c by omega] using aud2580 ⟨c-2580,by omega⟩)
            · by_cases h2610 : c<2610
              · by_cases h2600 : c<2600
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2590+(c-2590)=c by omega] using aud2590 ⟨c-2590,by omega⟩)
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2600+(c-2600)=c by omega] using aud2600 ⟨c-2600,by omega⟩)
              · by_cases h2620 : c<2620
                · exact (show chunk c=true by simpa only [Fin.val_mk,show 2610+(c-2610)=c by omega] using aud2610 ⟨c-2610,by omega⟩)
                · by_cases h2630 : c<2630
                  · exact (show chunk c=true by simpa only [Fin.val_mk,show 2620+(c-2620)=c by omega] using aud2620 ⟨c-2620,by omega⟩)
                  · exact (show chunk c=true by simpa only [Fin.val_mk,show 2630+(c-2630)=c by omega] using aud2630 ⟨c-2630,by omega⟩)
theorem all132000 : ∀ k≤132000,Matching k := by
  apply all_prefixes sound T rows
  intro k pos hi
  let c := (k-1)/50
  let j := (k-1)%50
  have h := checked c (by dsimp [c]; omega)
  have e : checkRow fast (0+50*c+j+1) (T (0+50*c+j+1)) (rows (0+50*c+j+1))=true := List.all_eq_true.mp h j (List.mem_range.mpr (Nat.mod_lt _ (by decide : 0<50)))
  simpa only [show 0+50*c+j+1=k by dsimp [c,j]; omega] using e
end Erdos848Pure.Window.Data

namespace Erdos848Pure
open Finset
theorem hall_every_endpoint (k : ℕ) (X : Finset ℕ)
    (xs : X ⊆ (range (25*k+7)).filter (fun b => b%25=18)) :
    X.card ≤ ((Erdos848.A₇ (25*k+7)).filter (fun a => ∃ b∈X,Squarefree (a*b+1))).card := by
  by_cases tail : 3300000≤25*k+7
  · exact hall_3300k k tail X xs
  · exact Window.hall_of_matching (Window.Data.all132000 k (by omega)) X xs
end Erdos848Pure

theorem OMA.solution : OMA.R_Erdos848_erdos_848_R2_H2_R1.H2 := by
  intro k _ _ X xs
  exact Erdos848Pure.hall_every_endpoint k X xs
