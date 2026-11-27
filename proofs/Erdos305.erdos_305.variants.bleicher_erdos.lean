import FormalConjectures.ErdosProblems.«305»
import Mathlib

-- Credit: @marcusbuffett
/-! Bleicher and Erdős, Denominators of Egyptian fractions II, Illinois Journal
of Mathematics 20 (1976), Theorem 1. Write P for a primorial just above b.
For a new prime p the squarefree integers in (p/256,p) occupy more than
half the residues, even after a residue is removed. Two complementary
divisors of the previous primorial Q therefore correct the target numerator
modulo p. Removing them and dividing by p preserves the induction range.
Their complementary denominators after the lift are at most p². -/
open Finset Nat

namespace Primorial305

lemma step (n : ℕ) : primorial (n+1) = primorial n * (if (n+1).Prime then n+1 else 1) := by
  simp [primorial,prod_filter,prod_range_succ]

private lemma div_primorial {p n : ℕ} (hp : p.Prime) :
    p ∣ primorial n ↔ p ≤ n := by
  have h := Nat.mem_primeFactors_of_ne_zero (p:=p) (primorial_ne_zero n)
  rwa [primeFactors_primorial,Nat.mem_primesLE,and_iff_left hp,and_iff_right hp,iff_comm] at h

lemma size (n : ℕ) : n ≤ primorial n := by
  by_contra! h
  let p := (primorial n+1).minFac
  have hn : primorial n+1 ≠ 1 := by have := primorial_pos n; omega
  have pp : p.Prime := Nat.minFac_prime hn
  have hd : p ∣ primorial n+1 := Nat.minFac_dvd _
  have hpn : p ≤ n := (Nat.le_of_dvd (Nat.succ_pos _) hd).trans (by omega)
  have : p ∣ 1 := (Nat.dvd_add_right ((div_primorial pp).mpr hpn)).mp hd
  exact pp.not_dvd_one this

lemma complete (k a : ℕ) (ha : a ≤ (if 3 ≤ k then 2 else 1)*primorial k) :
    ∃ E : Finset ℕ, E ⊆ (primorial k).divisors ∧ ∑ d ∈ E, d = a := by
  induction k generalizing a with
  | zero =>
    norm_num only [primorial_zero,show ¬ 3≤0 by decide,if_false,one_mul] at ha ⊢
    interval_cases a
    · exact ⟨∅,empty_subset _,by simp⟩
    · exact ⟨{1},by simp,by simp⟩
  | succ k ih =>
    by_cases boundary : k = 2
    · subst k
      have small : ∀ n : Fin 13, ∃ E ∈ (primorial 3).divisors.powerset, ∑ d ∈ E, d = n.val := by decide
      have ha' : a < 13 := by
        have hval : (if 3 ≤ 2+1 then 2 else 1)*primorial (2+1) = 12 := by decide
        rw [hval] at ha; omega
      obtain ⟨E,hE,h⟩ := small ⟨a,ha'⟩
      exact ⟨E,mem_powerset.mp hE,h⟩
    have hc : (if 3 ≤ k+1 then 2 else 1 : ℕ) = (if 3 ≤ k then 2 else 1) := by split_ifs <;> omega
    rw [hc] at ha
    let c := if 3 ≤ k then 2 else 1
    have hcpos : 1 ≤ c := by dsimp [c]; split <;> decide
    by_cases hp : (k+1).Prime
    · let p := k+1
      let P := primorial k
      have he : primorial (k+1) = P*p := by rw [step,if_pos hp]
      rw [he] at ha ⊢
      have hq : a/p ≤ c*P := Nat.div_le_of_le_mul (by simpa [c,mul_left_comm,mul_comm,mul_assoc] using ha)
      have hr0 : a%p ≤ P := by
        have h := Nat.mod_lt a hp.pos
        have := size k
        dsimp [p,P] at *
        omega
      have hr : a%p ≤ c*P := hr0.trans (by simpa using Nat.mul_le_mul_right P hcpos)
      obtain ⟨Q,hQ,hqsum⟩ := ih (a/p) hq
      obtain ⟨R,hR,hrsum⟩ := ih (a%p) hr
      let Z := Q.image (fun d => p*d)
      have dj : Disjoint R Z := by
        apply disjoint_left.mpr
        intro x hx hz
        obtain ⟨d,hd,rfl⟩ := mem_image.mp hz
        have hh : p ∣ P := (dvd_mul_right p d).trans (Nat.dvd_of_mem_divisors (hR hx))
        have := (div_primorial hp).mp hh
        omega
      have hn : P*p ≠ 0 := Nat.mul_ne_zero (primorial_ne_zero _) hp.ne_zero
      refine ⟨R ∪ Z,?_,?_⟩
      · intro d hd
        apply Nat.mem_divisors.mpr
        refine ⟨?_,hn⟩
        rcases mem_union.mp hd with hd | hd
        · exact dvd_mul_of_dvd_left (Nat.dvd_of_mem_divisors (hR hd)) _
        · obtain ⟨v,hv,rfl⟩ := mem_image.mp hd
          rw [mul_comm P]
          exact Nat.mul_dvd_mul_left p (Nat.dvd_of_mem_divisors (hQ hv))
      · rw [sum_union dj,show Z = _ from rfl,
          sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hp.pos h),← mul_sum,hqsum,hrsum]
        exact Nat.mod_add_div _ _
    · simpa [step k,hp] using ih a (by simpa [step k,hp] using ha)

theorem small (k a : ℕ) (ha : a ≤ primorial k) : ∃ E : Finset ℕ,
    E ⊆ (primorial k).divisors ∧ (∑ d ∈ E, (1:ℚ)/d) = a / (primorial k) := by
  let P := primorial k
  obtain ⟨S,hS,hs⟩ := complete k a (by split_ifs <;> omega)
  have hdiv (d : ℕ) (hd : d ∈ S) := Nat.dvd_of_mem_divisors (hS hd)
  have hpos (d : ℕ) (hd : d ∈ S) : 0 < P/d := Nat.div_pos (Nat.divisor_le (hS hd)) (Nat.pos_of_mem_divisors (hS hd))
  refine ⟨S.image (fun d => P/d),?_,?_⟩
  · rintro d hd
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hd
    exact Nat.mem_divisors.mpr ⟨⟨v,(Nat.div_mul_cancel (hdiv v hv)).symm⟩,primorial_ne_zero _⟩
  · rw [sum_image,← hs, Nat.cast_sum,sum_div]
    · apply sum_congr rfl
      intro d hd
      apply (div_eq_div_iff (by exact_mod_cast (hpos d hd).ne') (by exact_mod_cast primorial_ne_zero k)).mpr
      rw [one_mul]
      exact_mod_cast (Nat.mul_div_cancel' (hdiv d hd)).symm
    · intro x hx y hy h
      apply Nat.eq_of_mul_eq_mul_left (hpos x hx)
      calc
        _ = P := Nat.div_mul_cancel (hdiv x hx)
        _ = P/y*y := (Nat.div_mul_cancel (hdiv y hy)).symm
        _ = _ := congrArg (fun z => z*y) h.symm

end Primorial305

open Finset Nat Filter Real
namespace Locate305

private lemma low_theta : ∀ᶠ n : ℕ in atTop, (n:ℝ)/4 ≤ Chebyshev.theta n := by
  have little := (isLittleO_log_rpow_atTop (r:=1/2) (by norm_num)).bound
    (show 0 < (1/16 : ℝ) by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually little,eventually_ge_atTop 16] with n h hn
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have h16 : (16:ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_nonneg h1
  have hs : Real.log (n:ℝ) ≤ 1/16 * Real.sqrt n := by
    rw [← Real.sqrt_eq_rpow,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hlog,abs_of_nonneg (Real.sqrt_nonneg _)] at h
    exact h
  have hs2 := Real.sq_sqrt (show 0 ≤ (n:ℝ) by positivity)
  have hnlog : Real.log ((n:ℝ)+1) ≤ Real.log 2 + Real.log n := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  have htwo : (1:ℝ)/2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<2 by norm_num)
    linarith
  have h2u : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]
  have hroot : Real.sqrt (n:ℝ) ≤ n := by nlinarith [Real.sqrt_nonneg (n:ℝ),sq_nonneg (Real.sqrt n-1)]
  apply le_trans _ (Chebyshev.theta_ge n)
  nlinarith only [h16,hs,hroot,hnlog,h2u,hs2,mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg n),
    mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (n:ℝ))]

theorem locate (size : ∀ n, n ≤ primorial n) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, ∀ᶠ b : ℕ in atTop,
      ∃ k ≥ K, b ≤ primorial k ∧ (primorial k : ℝ) ≤ C*b*Real.log b ∧ (k:ℝ) ≤ C*Real.log b := by
  use 5,by norm_num
  intro K
  obtain ⟨N,hN⟩ := eventually_atTop.mp low_theta
  have loglarge := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [loglarge,eventually_gt_atTop (primorial (max K (N+1)))] with b hlog hb
  change 1 ≤ Real.log (b:ℝ) at hlog
  have hex : ∃ j, b ≤ primorial j := ⟨b,size b⟩
  let k := Nat.find hex
  have hP : b ≤ primorial k := Nat.find_spec hex
  have hbig : max K (N+1) < k := by
    by_contra! h
    exact hb.not_ge (hP.trans (primorial_mono h))
  have hk0 : 0 < k := by omega
  have hprev : primorial (k-1) < b := Nat.lt_of_not_ge (Nat.find_min hex (show k-1 < k by omega))
  have hθ := hN (k-1) (by omega)
  rw [Chebyshev.theta_eq_log_primorial,Nat.floor_natCast] at hθ
  have hln := Real.log_le_log (by exact_mod_cast primorial_pos (k-1))
    (show (primorial (k-1):ℝ) ≤ b by exact_mod_cast hprev.le)
  have hk : (k:ℝ) ≤ 5*Real.log b := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)] at hθ
    norm_num at hθ
    linarith
  refine ⟨k,by omega,hP,?_,hk⟩
  have hsucc (m : ℕ) : primorial (m+1) ≤ primorial m*(m+1) := by
    have hh : primorial (m+1) = primorial m * (if (m+1).Prime then m+1 else 1) := by
      simp [primorial,prod_filter,prod_range_succ]
    rw [hh]; apply Nat.mul_le_mul_left; split_ifs <;> omega
  have hbk : primorial k ≤ b*k := by
    have h := hsucc (k-1)
    rw [Nat.sub_add_cancel (by omega : 1≤k)] at h
    exact h.trans (Nat.mul_le_mul_right _ hprev.le)
  calc
    _ ≤ (b:ℝ)*k := by exact_mod_cast hbk
    _ ≤ (b:ℝ)*(5*Real.log b) := by gcongr
    _ = _ := by ring
end Locate305

open Finset Nat
namespace Dense305

private lemma primes_sum (n : ℕ) (hn : 31 ≤ n) :
    ∑ d ∈ (Ioc 0 n).filter Nat.Prime, ((d : ℝ)^2)⁻¹ ≤ 49/100 := by
  let s := (Ioc 0 31).filter Nat.Prime
  have hs : s = {2,3,5,7,11,13,17,19,23,29,31} := by decide
  have hu : (Ioc 0 n).filter Nat.Prime ⊆ s ∪ Ioc 31 n := by
    intro d hd
    obtain ⟨hd,hp⟩ := mem_filter.mp hd
    by_cases h : d ≤ 31
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hd).1,h⟩,hp⟩)
    · exact mem_union_right _ (mem_Ioc.mpr ⟨by omega,(mem_Ioc.mp hd).2⟩)
  have dj : Disjoint s (Ioc 31 n) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have := (mem_Ioc.mp (mem_filter.mp hx).1).2
    have := (mem_Ioc.mp hy).1
    omega
  have small : (∑ d ∈ s, ((d : ℝ)^2)⁻¹) + (31:ℝ)⁻¹ ≤ 49/100 := by
    rw [hs]; norm_num
  have tail := sum_Ioc_inv_sq_le_sub (α:=ℝ) (by decide : (31:ℕ)≠0) hn
  calc
    _ ≤ ∑ d ∈ s ∪ Ioc 31 n, ((d : ℝ)^2)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hu (by intros; positivity)
    _ ≤ _ := by rw [sum_union dj]; linarith [inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) n)]

private lemma nonsquarefree (n : ℕ) (hn : 31 ≤ n) :
    (((Ioc 0 n).filter fun d => ¬ Squarefree d).card:ℝ) ≤ (49/100)*n := by
  classical
  let S := (Ioc 0 n).filter Nat.Prime
  let M := fun p : ℕ => (Ioc 0 n).filter (fun d => p^2 ∣ d)
  have hsub : ((Ioc 0 n).filter fun d => ¬ Squarefree d) ⊆ S.biUnion M := by
    intro d hd
    obtain ⟨hd,hbad⟩ := mem_filter.mp hd
    rw [Nat.squarefree_iff_prime_squarefree] at hbad
    push Not at hbad
    obtain ⟨p,hp,hp2⟩ := hbad
    have hpd := (dvd_mul_right p p).trans hp2
    have hpn := (Nat.le_of_dvd (mem_Ioc.mp hd).1 hpd).trans (mem_Ioc.mp hd).2
    exact mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp.pos,hpn⟩,hp⟩,
      mem_filter.mpr ⟨hd,by simpa [sq] using hp2⟩⟩
  have hsum : (((Ioc 0 n).filter fun d => ¬ Squarefree d).card:ℝ) ≤
      ∑ p ∈ S, ((M p).card:ℝ) := by exact_mod_cast (card_le_card hsub).trans card_biUnion_le
  calc
    _ ≤ _ := hsum
    _ ≤ ∑ p ∈ S, (n:ℝ)*((p:ℝ)^2)⁻¹ := by
      apply sum_le_sum
      intro p hp
      dsimp [M]
      rw [Nat.Ioc_filter_dvd_card_eq_div]
      have h := (Nat.cast_div_le (α:=ℝ) (m:=n) (n:=p^2))
      rw [Nat.cast_pow, div_eq_mul_inv] at h
      exact h
    _ ≤ _ := by
      rw [← mul_sum,mul_comm (49/100:ℝ)]
      exact mul_le_mul_of_nonneg_left (primes_sum n hn) (Nat.cast_nonneg _)

def pool (p : ℕ) := (Ioc (p/256) (p-1)).filter Squarefree

theorem pool_card (p : ℕ) (hp : 10000 ≤ p) : p+2 < 2*(pool p).card := by
  classical
  let bad := (Ioc 0 p).filter fun d => ¬ Squarefree d
  have hb := nonsquarefree p (by omega)
  have hbr : ((bad.card:ℝ)*100) ≤ 49*p := by dsimp [bad]; linarith
  have hbad : bad.card*100 ≤ 49*p := by exact_mod_cast hbr
  have hu : Ioc 0 p ⊆ (Ioc 0 (p/256) ∪ {p}) ∪ (bad ∪ pool p) := by
    intro d hd
    by_cases h : d ≤ p/256
    · exact mem_union_left _ (mem_union_left _ (mem_Ioc.mpr ⟨(mem_Ioc.mp hd).1,h⟩))
    by_cases he : d=p
    · exact mem_union_left _ (mem_union_right _ (mem_singleton.mpr he))
    by_cases hs : Squarefree d
    · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨mem_Ioc.mpr
        ⟨by omega,by have := (mem_Ioc.mp hd).2; omega⟩,hs⟩))
    · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hd,hs⟩))
  have h1 := (card_le_card hu).trans (card_union_le _ _)
  have h2 := card_union_le (Ioc 0 (p/256)) ({p}:Finset ℕ)
  have h3 := card_union_le bad (pool p)
  simp only [Nat.card_Ioc, tsub_zero,card_singleton] at h1 h2
  omega

end Dense305

open Finset Nat

namespace Correct305

private theorem two_residues {p : ℕ} [Fact p.Prime] (hp : 2 < p) (T : Finset (ZMod p))
    (hc : p+2 < 2*T.card) (r : ZMod p) :
    ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ x+y=r := by
  classical
  let f := fun z : ZMod p => r-z
  have hf : Function.Injective f := fun _ _ h => sub_right_inj.mp h
  let S := T ∩ T.image f
  have hS : 1 < S.card := by
    have hi := card_union_add_card_inter T (T.image f)
    rw [card_image_of_injective _ hf] at hi
    have hu : (T ∪ T.image f).card ≤ p := by simpa [ZMod.card] using (T ∪ T.image f).card_le_univ
    dsimp [S]; omega
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp hS
  have htwo : (2:ZMod p) ≠ 0 := by
    have h : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) hp
    simpa using (mt (ZMod.natCast_eq_zero_iff 2 p).mp h)
  have get (z : ZMod p) (hz : z ∈ S) (hn : z+z ≠ r) :
      ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ x+y=r := by
    obtain ⟨hz1,hz2⟩ := mem_inter.mp hz
    obtain ⟨y,hy,hyz⟩ := mem_image.mp hz2
    have he : z+y=r := by dsimp [f] at hyz; linear_combination -hyz
    exact ⟨z,hz1,y,hy,fun e => hn (e ▸ he),he⟩
  by_cases h : a+a=r
  · apply get b hb
    intro he
    apply hab
    apply mul_left_cancel₀ htwo
    simpa only [two_mul] using h.trans he.symm
  · exact get a ha h

theorem correction (p r : ℕ) (hp : p.Prime) (hbig : 2 < p)
    (D : Finset ℕ) (hcard : p+2 < 2*D.card)
    (hD : ∀ d ∈ D, d < p ∧ p ≤ 256*d ∧ Squarefree d) :
    let P := primorial (p-1)
    ∃ a b : ℕ, a ∣ P ∧ b ∣ P ∧ a ≠ b ∧ ¬p ∣ a ∧ ¬p ∣ b ∧
      P ≤ a*p ∧ P ≤ b*p ∧ p*a ≤ 256*P ∧ p*b ≤ 256*P ∧ r ≡ a+b [MOD p] := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let P := primorial (p-1)
  let base := fun d => P/d
  let residue := fun d => ((base d:ℕ):ZMod p)
  have hn : ¬ p ∣ P := fun h => by have := hp.dvd_primorial_iff.mp h; omega
  have hP : (P : ZMod p) ≠ 0 := mt (ZMod.natCast_eq_zero_iff P p).mp hn
  have dv (d : ℕ) (hd : d ∈ D) : d ∣ P :=
    (hD d hd).2.2.dvd_primorial.trans (primorial_dvd_primorial (by have := (hD d hd).1; omega))
  have eq (d : ℕ) (hd : d ∈ D) : base d*d = P := Nat.div_mul_cancel (dv d hd)
  have eqz (d : ℕ) (hd : d ∈ D) : residue d*(d:ZMod p)=P := by dsimp only [residue]; rw [← Nat.cast_mul,eq d hd]
  have inj : Set.InjOn residue (D : Set ℕ) := by
    intro x hx y hy he
    have hresidue : residue x ≠ 0 := fun hz => hP (by rw [←eqz x hx,hz,zero_mul])
    have e : (x:ZMod p) = y := mul_left_cancel₀ hresidue (by rw [eqz x hx,he,eqz y hy])
    have h := congrArg ZMod.val e
    simpa only [ZMod.val_natCast_of_lt (hD x hx).1,ZMod.val_natCast_of_lt (hD y hy).1] using h
  have hT : p+2 < 2*(D.image residue).card := by rw [Finset.card_image_of_injOn inj]; exact hcard
  obtain ⟨x,hx,y,hy,hnxy,he⟩ := two_residues hbig (D.image residue) hT (r:ZMod p)
  obtain ⟨d,hd,rfl⟩ := mem_image.mp hx
  obtain ⟨e,he',rfl⟩ := mem_image.mp hy
  have divides (j : ℕ) (hj : j ∈ D) : base j ∣ P := ⟨j,(eq j hj).symm⟩
  have low (j : ℕ) (hj : j ∈ D) : P ≤ base j*p := by
    calc
      _ = base j*j := (eq j hj).symm
      _ ≤ _ := Nat.mul_le_mul_left _ (hD j hj).1.le
  have upper (j : ℕ) (hj : j ∈ D) : p*base j ≤ 256*P := by
    calc
      _ ≤ (256*j)*base j := Nat.mul_le_mul_right _ (hD j hj).2.1
      _ = _ := by rw [← eq j hj]; ring
  refine ⟨base d,base e,divides d hd,divides e he',
    fun h => hnxy (congrArg (fun n : ℕ => (n:ZMod p)) h),
    fun h => hn (h.trans (divides d hd)),fun h => hn (h.trans (divides e he')),
    low d hd,low e he',upper d hd,upper e he',?_⟩
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  simpa [residue] using he.symm

end Correct305


namespace Large305
open Nat Finset Filter
open Primorial305 Dense305 Correct305

private def cap (k : ℕ) := max (primorial 10000) (k^2)

private def Rep (k r : ℕ) : Prop := ∃ E : Finset ℕ, E ⊆ (primorial k).divisors ∧
  ∑ d ∈ E, d = r ∧ ∀ d ∈ E, primorial k ≤ cap k*d

private theorem at_base (r : ℕ) (hr : r ≤ 2*primorial 10000) : Rep 10000 r := by
  obtain ⟨E,hE,hs⟩ := Primorial305.complete 10000 r (by simpa only [show 3 ≤ 10000 by decide,if_true] using hr)
  refine ⟨E,hE,hs,?_⟩
  intro d hd
  have hcap : primorial 10000 ≤ cap 10000 := le_max_left _ _
  exact hcap.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_mem_divisors (hE hd)))

private theorem cap_mono (k : ℕ) : cap k ≤ cap (k+1) :=
  max_le_max_left _ (Nat.pow_le_pow_left (by omega : k ≤ k+1) _)

private theorem raise_prime (k : ℕ) (hk : 10000 ≤ k) (r : ℕ) (hp : (k+1).Prime)
    (hi : ∀ s, primorial k*k ≤ k*s+1024*primorial k → s ≤ 2*primorial k → Rep k s)
    (hr : primorial (k+1)*(k+1) ≤ (k+1)*r+1024*primorial (k+1))
    (hh : r ≤ 2*primorial (k+1)) : Rep (k+1) r := by
  let p := k+1
  let Q := primorial k
  have hpk : p = k+1 := rfl
  have hstep : primorial (k+1) = Q*p := by rw [Primorial305.step,if_pos hp]
  have hQ := primorial_pos k
  have hpool (d : ℕ) (hd : d ∈ pool p) : d < p ∧ p ≤ 256*d ∧ Squarefree d := by
    obtain ⟨hi,hs⟩ := mem_filter.mp hd
    obtain ⟨ilo,ihi⟩ := mem_Ioc.mp hi
    exact ⟨by omega,by omega,hs⟩
  obtain ⟨a,b,ha,hb,hab,hna,hnb,la,lb,ua,ub,hm⟩ :=
    correction p r hp (by omega) (pool p) (pool_card p (by omega)) hpool
  change a ∣ Q at ha
  change b ∣ Q at hb
  change Q ≤ a*p at la
  change Q ≤ b*p at lb
  change p*a ≤ 256*Q at ua
  change p*b ≤ 256*Q at ub
  rw [hstep] at hr hh
  change Q*p*p ≤ p*r + 1024*(Q*p) at hr
  have hlow : Q*p ≤ r+1024*Q := by
    apply Nat.le_of_mul_le_mul_right (c:=p) _ hp.pos
    nlinarith only [hr]
  have hcost : p*(a+b) ≤ 512*Q := by nlinarith only [ua,ub]
  have habr : a+b ≤ r := by
    have h1 : a+b ≤ p*(a+b) := Nat.le_mul_of_pos_left _ hp.pos
    have h2 : 1536*Q ≤ p*Q := Nat.mul_le_mul_right _ (by omega)
    nlinarith only [h1,h2,hcost,hlow]
  obtain ⟨w,hw⟩ := (Nat.modEq_iff_dvd' habr).mp hm.symm
  have he : a+b+p*w=r := by omega
  have hwlo : Q*k ≤ k*w+1024*Q := by
    apply Nat.le_of_mul_le_mul_left (c:=p) _ hp.pos
    have hc : k*(a+b) ≤ p*(a+b) := Nat.mul_le_mul_right _ (by omega)
    have hl := Nat.mul_le_mul_left k hlow
    rw [← he] at hl
    dsimp only [p] at *
    nlinarith only [hl,hcost,hc]
  have hwup : w ≤ 2*Q := by
    apply Nat.le_of_mul_le_mul_left (c:=p) _ hp.pos
    nlinarith only [he,hh]
  obtain ⟨E,hE,hEs,hEc⟩ := hi w hwlo hwup
  let F := E.image (fun d => p*d)
  have hs : ∑ d ∈ F, d = p*w := by
    dsimp [F]
    rw [sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hp.pos h),←mul_sum,hEs]
  have haF : a ∉ F := by
    intro h; obtain ⟨d,_,hd⟩ := mem_image.mp h; exact hna ⟨d,hd.symm⟩
  have hbF : b ∉ F := by
    intro h; obtain ⟨d,_,hd⟩ := mem_image.mp h; exact hnb ⟨d,hd.symm⟩
  have hcoef : p^2 ≤ cap (k+1) := le_max_right _ _
  refine ⟨insert a (insert b F),?_,?_,?_⟩
  · intro v hv
    rw [hstep]
    apply Nat.mem_divisors.mpr
    refine ⟨?_,Nat.mul_ne_zero hQ.ne' hp.ne_zero⟩
    rcases mem_insert.mp hv with rfl | hv
    · exact dvd_mul_of_dvd_left ha _
    rcases mem_insert.mp hv with rfl | hv
    · exact dvd_mul_of_dvd_left hb _
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hv
    rw [mul_comm Q]
    exact Nat.mul_dvd_mul_left p (Nat.dvd_of_mem_divisors (hE hd))
  · rw [sum_insert (by simp [hab,haF]),sum_insert hbF,hs]
    omega
  · intro v hv
    rw [hstep]
    rcases mem_insert.mp hv with rfl | hv
    · exact (show Q*p ≤ p^2*v by nlinarith only [Nat.mul_le_mul_right p la]).trans
        (Nat.mul_le_mul_right _ hcoef)
    rcases mem_insert.mp hv with rfl | hv
    · exact (show Q*p ≤ p^2*v by nlinarith only [Nat.mul_le_mul_right p lb]).trans
        (Nat.mul_le_mul_right _ hcoef)
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hv
    have h := (hEc _ hd).trans (Nat.mul_le_mul_right d (cap_mono k))
    nlinarith only [Nat.mul_le_mul_right p h]

private theorem near (k : ℕ) (hk : 10000 ≤ k) : ∀ r,
    primorial k*k ≤ k*r+1024*primorial k → r ≤ 2*primorial k → Rep k r := by
  induction k, hk using Nat.le_induction with
  | base => exact fun r _ hh => at_base r hh
  | succ k hk ih =>
    intro r hl hh
    by_cases hp : (k+1).Prime
    · exact raise_prime k hk r hp ih hl hh
    have h : primorial (k+1) = primorial k := by rw [Primorial305.step,if_neg hp,mul_one]
    rw [h] at hl hh
    have hlo : primorial k*k ≤ k*r+1024*primorial k := by
      by_cases hc : primorial k ≤ r
      · nlinarith [Nat.mul_le_mul_right k hc]
      · nlinarith
    obtain ⟨E,hE,hs,hw⟩ := ih r hlo hh
    exact ⟨E,h ▸ hE,hs,fun d hd => h ▸ (hw _ hd).trans (Nat.mul_le_mul_right d (cap_mono k))⟩

theorem large : ∀ᶠ k : ℕ in atTop, ∀ r : ℕ, primorial k ≤ r → r < 2*primorial k →
    ∃ F : Finset ℕ, F ⊆ (primorial k).divisors ∧ (∀ d ∈ F, d ≤ 2*k^2) ∧
      (∑ d ∈ F, (1:ℚ)/d) = r / (primorial k) := by
  filter_upwards [eventually_ge_atTop (max 10000 (primorial 10000))] with k hk r hl hh
  have hcap : cap k ≤ 2*k^2 := by
    have : primorial 10000 ≤ k := (le_max_right _ _).trans hk
    dsimp [cap]; apply max_le <;> nlinarith [Nat.le_self_pow (by decide : 2≠0) k]
  obtain ⟨E,hE,hs,hw⟩ := near k ((le_max_left _ _).trans hk) r (by
    nlinarith [Nat.mul_le_mul_right k hl]) hh.le
  let P := primorial k
  have eq (d : ℕ) (hd : d ∈ E) : P/d*d = P := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors (hE hd))
  have pos (d : ℕ) (hd : d ∈ E) : 0 < P/d :=
    Nat.div_pos (Nat.divisor_le (hE hd)) (Nat.pos_of_mem_divisors (hE hd))
  refine ⟨E.image (fun d => P/d),?_,?_,?_⟩
  · intro v hv
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hv
    exact Nat.mem_divisors.mpr ⟨⟨d,(eq d hd).symm⟩,primorial_ne_zero _⟩
  · intro v hv
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hv
    apply le_trans _ hcap
    apply Nat.le_of_mul_le_mul_right (c:=d) _ (Nat.pos_of_mem_divisors (hE hd))
    rw [eq d hd]
    exact hw _ hd
  · rw [sum_image,←hs,Nat.cast_sum,sum_div]
    · apply sum_congr rfl
      intro d hd
      apply (div_eq_div_iff (by exact_mod_cast (pos d hd).ne') (by exact_mod_cast primorial_ne_zero k)).mpr
      rw [one_mul]
      exact_mod_cast (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors (hE hd))).symm
    · intro x hx y hy h
      change P/x = P/y at h
      apply Nat.eq_of_mul_eq_mul_left (pos x hx)
      calc
        _ = P := eq x hx
        _ = P/y*y := (eq y hy).symm
        _ = _ := by rw [h]
end Large305

namespace Egyptian305


open Finset Filter Real Nat

/-- Size of the first primorial above b. The cutoff k can be made arbitrarily
large, while k is logarithmic in b and the overshoot is at most a factor k. -/
def CutoffBound : Prop := ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, ∀ᶠ b : ℕ in atTop,
  ∃ k ≥ K, b ≤ primorial k ∧ (primorial k : ℝ) ≤ C*b*Real.log b ∧ (k:ℝ) ≤ C*Real.log b

/-- The divisors of a primorial have every integer up to the primorial as a
subset sum (use the bijection d ↦ P/d to obtain the displayed form). -/
def SmallSums : Prop := ∀ k a : ℕ, a ≤ primorial k → ∃ E : Finset ℕ,
  E ⊆ (primorial k).divisors ∧ (∑ d ∈ E, (1:ℚ)/d) = a / (primorial k)

/-- Large-divisor subset sums, the range needed from Lemma 4 of the paper.
For sums from P through 2P−1 it suffices to use divisors at least P/(2k²).
This gives the stated bound on the complementary denominators. -/
def LargeSums : Prop := ∀ᶠ k : ℕ in atTop, ∀ r : ℕ, primorial k ≤ r → r < 2*primorial k →
  ∃ F : Finset ℕ, F ⊆ (primorial k).divisors ∧ (∀ d ∈ F, d ≤ 2*k^2) ∧
    (∑ d ∈ F, (1:ℚ)/d) = r / (primorial k)

lemma scale {b : ℕ} (hb : 0 < b) (F : Finset ℕ) :
    (∑ d ∈ F.image (fun d => b*d), (1:ℚ)/d) = (∑ d ∈ F, (1:ℚ)/d)/b := by
  rw [sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hb h),sum_div]
  apply sum_congr rfl
  intro d _
  push_cast
  ring

lemma bound (small : SmallSums) (k b : ℕ) (hb : 0 < b) (hP : b ≤ primorial k)
    (large : ∀ r : ℕ, primorial k ≤ r → r < 2*primorial k →
      ∃ F : Finset ℕ, F ⊆ (primorial k).divisors ∧ (∀ d ∈ F, d ≤ 2*k^2) ∧
        (∑ d ∈ F, (1:ℚ)/d) = r / (primorial k)) :
    Erdos305.Dmax b ≤ max (primorial k) (b*(2*k^2)) := by
  classical
  apply Finset.sup_le
  intro a ha
  obtain ⟨ha,hab⟩ := mem_Ico.mp ha
  let P := primorial k
  have hPpos : 0 < P := primorial_pos k
  have nonzero {E : Finset ℕ} (hE : E ⊆ P.divisors) : 0 ∉ E :=
    fun h => (Nat.pos_of_mem_divisors (hE h)).false
  by_cases hdiv : b ∣ P
  · let c := a*(P/b)
    have hc : b*c = a*P := by dsimp [c]; rw [mul_left_comm,Nat.mul_div_cancel' hdiv]
    have hcP : c ≤ P := by
      dsimp [c]
      calc
        _ ≤ b*(P/b) := Nat.mul_le_mul_right _ hab.le
        _ = P := Nat.mul_div_cancel' hdiv
    obtain ⟨E,hE,hq⟩ := small k c hcP
    apply Nat.sInf_le
    refine ⟨E,nonzero hE,fun d hd => (Nat.divisor_le (hE hd)).trans (le_max_left _ _),?_⟩
    rw [hq]
    apply (div_eq_div_iff (by exact_mod_cast hPpos.ne') (by exact_mod_cast hb.ne')).mpr
    exact_mod_cast (mul_comm c b ▸ hc)
  · let t := (a-1)*P
    let q := t/b
    let r := P+t%b
    have ht : t+P=a*P := by
      dsimp [t]
      rw [← Nat.succ_mul,show (a-1).succ=a by omega]
    have hsum : q*b+r=a*P := by
      dsimp [q,r]
      have := Nat.div_add_mod' t b
      omega
    have hqle : q ≤ P := by
      apply Nat.le_of_mul_le_mul_left (c:=b)
      · calc
          b*q = q*b := mul_comm _ _
          _ ≤ q*b+r := by omega
          _ = a*P := hsum
          _ ≤ b*P := Nat.mul_le_mul_right _ hab.le
      · exact hb
    obtain ⟨E,hE,hqe⟩ := small k q hqle
    obtain ⟨F,hF,hshort,hrf⟩ := large r (Nat.le_add_right _ _) (by
      change P + t%b < 2*P
      have := Nat.mod_lt t hb
      change b ≤ P at hP
      omega)
    let B := F.image (fun d => b*d)
    have hdj : Disjoint E B := by
      apply Finset.disjoint_left.mpr
      intro x hx hxb
      obtain ⟨d,hd,rfl⟩ := mem_image.mp hxb
      exact hdiv ((dvd_mul_right b d).trans (Nat.dvd_of_mem_divisors (hE hx)))
    apply Nat.sInf_le
    refine ⟨E ∪ B,?_,?_,?_⟩
    · intro h
      rcases mem_union.mp h with h | h
      · exact nonzero hE h
      · obtain ⟨d,hd,he⟩ := mem_image.mp h
        exact (Nat.mul_pos hb (Nat.pos_of_mem_divisors (hF hd))).ne' he
    · intro d hd
      rcases mem_union.mp hd with h | h
      · exact (Nat.divisor_le (hE h)).trans (le_max_left _ _)
      · obtain ⟨v,hv,rfl⟩ := mem_image.mp h
        exact (Nat.mul_le_mul_left b (hshort _ hv)).trans (le_max_right _ _)
    · rw [sum_union hdj,show B = _ from rfl,scale hb,hqe,hrf]
      change (q:ℚ)/P + (r:ℚ)/P/b = (a:ℚ)/b
      have h : (q:ℚ)*b+r = a*P := by exact_mod_cast hsum
      field_simp
      linarith

theorem assemble : CutoffBound → SmallSums → LargeSums → type_of% @Erdos305.erdos_305.variants.bleicher_erdos := by
  intro locate small large
  obtain ⟨C,hC,hk⟩ := locate
  obtain ⟨K,hK⟩ := eventually_atTop.mp large
  refine ⟨C+2*C^2,by positivity,?_⟩
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hk K,hlog,eventually_ge_atTop 1] with b hloc hlog hb
  change 1 ≤ Real.log (b:ℝ) at hlog
  obtain ⟨k,hk,hbP,hP,hsize⟩ := hloc
  have hbound := bound small k b hb hbP (hK k hk)
  have hreal : (Erdos305.Dmax b:ℝ) ≤ max (primorial k:ℝ) (b*(2*(k:ℝ)^2)) := by exact_mod_cast hbound
  apply hreal.trans
  apply max_le
  · apply hP.trans
    have : C*(b:ℝ)*Real.log b ≤ C*b*(Real.log b)^2 := by
      nlinarith [mul_nonneg (show 0 ≤ C*(b:ℝ)*Real.log b by positivity) (sub_nonneg.mpr hlog)]
    nlinarith [mul_nonneg (show 0 ≤ 2*C^2*(b:ℝ) by positivity) (sq_nonneg (Real.log b))]
  · calc
      _ ≤ (b:ℝ)*(2*(C*Real.log b)^2) := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ C*(b:ℝ) by positivity) (sq_nonneg (Real.log b))]


end Egyptian305

theorem OMA.solution : type_of% @Erdos305.erdos_305.variants.bleicher_erdos :=
  Egyptian305.assemble (Locate305.locate Primorial305.size) Primorial305.small Large305.large
