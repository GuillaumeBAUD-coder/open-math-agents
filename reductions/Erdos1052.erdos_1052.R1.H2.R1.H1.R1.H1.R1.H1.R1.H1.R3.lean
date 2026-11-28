import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1
import Mathlib

/-! Bound the wide 2-adic links in a fixed odd-kernel unitary perfect number.
The parent is the exponent-five branch of @adammcarter's reduction. The team's
weight identity (in particular @MechaNuggan's observation) motivates separating
the count and maximum valuation, but here only primes 3 mod 4 need be counted.
Prime-factor ownership and the 3-budget come from the ancestor reductions.
A disjoint-child count bounds breaks in Cunningham chains of the second kind.
Fermat bounds every interval of ordinary links, after which induction bounds
the primes at all break points. Credit: @physbuzz. -/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R3
open Finset
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main

/-- Uniformly bound the number of non-Mersenne simple odd primes congruent to 3 modulo 4. -/
def H1 : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 5 →
    262 ≤ padicValNat 2 n →
    (∀ d, 10 ≤ d → d ≤ 257 → d ∉ ({11, 13} : Finset ℕ) → padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144,
        524288} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    (padicValNat 2 n % 2 = 1 →
      ((padicValNat 2 n).primeFactors.filter (fun p => p % 3 = 2)).card ≤ 4) →
    ((n.primeFactors.erase 3).filter (fun p => 4 ∣ p+1 ∧ p+1 ≠ 2^((p+1).factorization 2))).card ≤ C

/-- Uniformly bound the multiplicity of 2 in the successor of any simple odd prime. -/
def H2 : Prop :=
  ∃ D : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 5 →
    262 ≤ padicValNat 2 n →
    (∀ d, 10 ≤ d → d ≤ 257 → d ∉ ({11, 13} : Finset ℕ) → padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144,
        524288} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    (padicValNat 2 n % 2 = 1 →
      ((padicValNat 2 n).primeFactors.filter (fun p => p % 3 = 2)).card ≤ 4) →
    ∀ p ∈ n.primeFactors, p ≠ 2 → p ≠ 3 → (p+1).factorization 2 ≤ D

lemma link_succ {r j : ℕ} : (fun r j : ℕ => 2^j*(r-1)+1) r (j+1)+1=2*(fun r j : ℕ => 2^j*(r-1)+1) r j := by
  simp only [pow_succ];ring

lemma short_chain {r j : ℕ} (hp : r.Prime) (h2 : r ≠ 2)
    (h : ∀ i ≤ j, ((fun r j : ℕ => 2^j*(r-1)+1) r i).Prime) : j < r-1 := by
  have hr:=hp.two_le
  have co : r.Coprime 2 := hp.coprime_iff_not_dvd.mpr
    (fun dv => h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp dv))
  have fermat : 2^(r-1) ≡ 1 [MOD r] := Nat.ModEq.pow_card_sub_one_eq_one hp co.symm
  have dx : r ∣ (fun r j : ℕ => 2^j*(r-1)+1) r (r-1) := by
    have e:=(fermat.mul_right (r-1)).add_right 1
    apply Nat.dvd_of_mod_eq_zero
    change (2^(r-1)*(r-1)+1)%r=(1*(r-1)+1)%r at e
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ r)] using e
  by_contra! nj
  have big : 1 < 2^(r-1) := Nat.one_lt_pow (by omega) (by decide)
  have product := Nat.mul_lt_mul_of_pos_right big (show 0 < r-1 by omega)
  have ne : r < (fun r j : ℕ => 2^j*(r-1)+1) r (r-1) := by dsimp only;omega
  exact ne.ne ((Nat.prime_dvd_prime_iff_eq hp (h _ nj)).mp dx)


lemma prefix_bound {P : Finset ℕ} (pr : ∀ x ∈ P, x.Prime ∧ x ≠ 2) {B X : ℕ}
    (base : ∀ e ∈ (P.filter (fun x => ¬∃ r ∈ P, x+1=2*r)), e ≤ X → e ≤ B) :
    ∀ p ∈ P, p ≤ X → p ≤ (fun B : ℕ => 2^B*B+1) B := by
  have chain (p : ℕ) (mem : p ∈ P) (fit : p ≤ X) :
      ∃ r ∈ P, r ≤ B ∧ ∃ j, p=(fun r j : ℕ => 2^j*(r-1)+1) r j ∧ ∀ i ≤ j, (fun r j : ℕ => 2^j*(r-1)+1) r i ∈ P := by
    induction p using Nat.strong_induction_on with
    | h p ih =>
      have pp:=(pr p mem).1.two_le
      by_cases small : p ≤ B
      · have z : (fun r j : ℕ => 2^j*(r-1)+1) p 0=p := by simp [Nat.sub_add_cancel (by omega : 1 ≤ p)]
        exact ⟨p,mem,small,0,z.symm,fun i hi => by
          have h0 : i = 0 := Nat.eq_zero_of_le_zero hi
          simpa only [h0, z] using mem⟩
      have plain : ∃ t ∈ P, p+1=2*t := by
        by_contra hn
        exact small (base p (mem_filter.mpr ⟨mem,hn⟩) fit)
      obtain ⟨t,ht,et⟩:=plain
      obtain ⟨r,hr,rb,j,eq,run⟩:=ih t (by omega) ht (by omega)
      have s:=link_succ (r:=r) (j:=j)
      have top : p=(fun r j : ℕ => 2^j*(r-1)+1) r (j+1) := by omega
      refine ⟨r,hr,rb,j+1,top,?_⟩
      intro i hi
      by_cases e : i=j+1
      · rwa [e,←top]
      · exact run i (by omega)
  intro p mem fit
  obtain ⟨r,hr,rb,j,eq,seq⟩:=chain p mem fit
  have short := short_chain (pr r hr).1 (pr r hr).2 (fun i hi => (pr _ (seq i hi)).1)
  rw [eq]
  dsimp only
  exact Nat.add_le_add_right (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (by omega)) (by omega)) _

lemma branch_children {P : Finset ℕ} (pr : ∀ x ∈ P, x.Prime ∧ x ≠ 2)
    (no3 : 3 ∉ P)
    (closed : ∀ r, r.Prime → r ≠ 2 → r ≠ 3 → ∀ p ∈ P, r ∣ p+1 → r ∈ P)
    (square : ∀ r, r.Prime → r ≠ 2 → r ≠ 3 → ∀ p ∈ P, ¬r*r ∣ p+1)
    {p : ℕ} (hp : p ∈ P) (low : ¬4 ∣ p+1) (clean : ¬3 ∣ p+1) :
    1+(if p ∈ (P.filter (fun x => ¬∃ r ∈ P, x+1=2*r)) then 1 else 0) ≤ (P.filter (fun r => r ∣ p+1)).card := by
  have pp:=pr p hp
  have po:=pp.1.odd_of_ne_two pp.2
  obtain ⟨m,hm⟩:=po
  let x:=m+1
  have eq : p+1=2*x := by dsimp [x];omega
  have px:=pp.1.two_le
  have large : 1 < x := by omega
  have odd : ¬2 ∣ x := fun e => low (by rw [eq];exact Nat.mul_dvd_mul_left 2 e)
  let r:=x.minFac
  have rp : r.Prime := Nat.minFac_prime (by omega)
  have rd : r ∣ x := Nat.minFac_dvd _
  have all {t : ℕ} (pt : t.Prime) (ht : t ∣ x) :
      t ∈ P.filter (fun z => z ∣ p+1) ∧ t ≠ 2 ∧ t ≠ 3 := by
    have d : t ∣ p+1 := eq ▸ dvd_mul_of_dvd_right ht _
    have nt : t ≠ 2 := by rintro rfl;exact odd ht
    have th : t ≠ 3 := by rintro rfl;exact clean d
    exact ⟨mem_filter.mpr ⟨closed _ pt nt th _ hp d,d⟩,nt,th⟩
  obtain ⟨rm,r2,r3⟩:=all rp rd
  by_cases ex : p ∈ (P.filter (fun x => ¬∃ r ∈ P, x+1=2*r))
  · rw [if_pos ex]
    obtain ⟨z,hz⟩:=rd
    have nz : z ≠ 1 := by
      intro h;rw [h,mul_one] at hz
      exact (mem_filter.mp ex).2 ⟨r,(mem_filter.mp rm).1,by omega⟩
    let t:=z.minFac
    have tp : t.Prime := Nat.minFac_prime nz
    have tz : t ∣ z := Nat.minFac_dvd _
    have tx : t ∣ x := hz ▸ dvd_mul_of_dvd_right tz _
    have neq : r ≠ t := by
      intro h
      have sq : r*r ∣ x := by rw [hz];exact Nat.mul_dvd_mul_left _ (h ▸ tz)
      exact square r rp r2 r3 p hp (eq ▸ dvd_mul_of_dvd_right sq _)
    exact one_lt_card.mpr ⟨r,rm,t,(all tp tx).1,neq⟩
  · rw [if_neg ex]
    exact card_pos.mpr ⟨r,rm⟩

theorem exceptional_count {P : Finset ℕ} (pr : ∀ x ∈ P, x.Prime ∧ x ≠ 2)
    (no3 : 3 ∉ P)
    (closed : ∀ r, r.Prime → r ≠ 2 → r ≠ 3 → ∀ p ∈ P, r ∣ p+1 → r ∈ P)
    (owned : ∀ r ∈ P, ∀ p ∈ P, ∀ q ∈ P, r ∣ p+1 → r ∣ q+1 → p=q)
    (square : ∀ r, r.Prime → r ≠ 2 → r ≠ 3 → ∀ p ∈ P, ¬r*r ∣ p+1) :
    ((P.filter (fun x => ¬∃ r ∈ P, x+1=2*r))).card ≤ 2*((P.filter (fun p => 4 ∣ p+1)).card+
      (P.filter (fun p => 3 ∣ p+1)).card) := by
  let children:=fun p => P.filter (fun r => r ∣ p+1)
  have dis : (P : Set ℕ).PairwiseDisjoint children := by
    intro p hp q hq ne
    apply disjoint_left.mpr
    intro r hr hr'
    exact ne (owned r (mem_filter.mp hr).1 p hp q hq (mem_filter.mp hr).2 (mem_filter.mp hr').2)
  have small : P.biUnion children ⊆ P := by
    intro r hr;obtain ⟨q,_,hq⟩:=mem_biUnion.mp hr;exact (mem_filter.mp hq).1
  have edges:=card_le_card small
  rw [card_biUnion dis] at edges
  have sumB:=sum_le_sum (s:=P) (f:=fun p => 1+(if p ∈ (P.filter (fun x => ¬∃ r ∈ P, x+1=2*r)) then 1 else 0 : ℕ))
    (g:=fun p => (children p).card+((if 4 ∣ p+1 then 1 else 0)+(if 3 ∣ p+1 then 1 else 0))*2)
    (fun p hp => by
      by_cases hi : 4 ∣ p+1
      · simp only [if_pos hi];split_ifs <;> omega
      by_cases cl : 3 ∣ p+1
      · simp only [if_neg hi,if_pos cl];split_ifs <;> omega
      simpa [hi,cl,children] using branch_children pr no3 closed square hp hi cl)
  simp only [sum_add_distrib,←sum_mul,sum_const,nsmul_eq_mul,mul_one,sum_boole] at sumB
  have ex : P.filter (fun p => p ∈ (P.filter (fun x => ¬∃ r ∈ P, x+1=2*r)))=(P.filter (fun x => ¬∃ r ∈ P, x+1=2*r)) := by
    ext x;simp only [mem_filter];tauto
  rw [ex] at sumB
  simp only [Nat.cast_id] at sumB
  omega

lemma value_bound (x M W : ℕ) (hx : 0 < x)
    (small : ∀ t ∈ x.primeFactors, t ≤ M ∧ x.factorization t ≤ W) :
    x ≤ (max 1 M ^ W)^(M+1) := by
  have sub : x.primeFactors ⊆ range (M+1) := fun t ht => mem_range.mpr (by have := (small t ht).1;omega)
  have card:=card_le_card sub
  rw [card_range] at card
  calc
    x = ∏ t ∈ x.primeFactors, t^x.factorization t := (Nat.prod_primeFactors_pow_factorization hx.ne')
    _ ≤ ∏ _ ∈ x.primeFactors, max 1 M^W := prod_le_prod' (fun t ht =>
      (Nat.pow_le_pow_left ((small t ht).1.trans (le_max_right _ _)) _).trans
        (Nat.pow_le_pow_right (by omega) (small t ht).2))
    _ = (max 1 M ^ W)^x.primeFactors.card := by simp
    _ ≤ _ := Nat.pow_le_pow_right (by positivity) card

/-- Bounds a whole prime set from the number of breaks in its Cunningham chains
and a local bound on the size of the next prime with small children. -/
lemma finite_growth (step : ℕ → ℕ) (C B : ℕ) :
    ∃ K, ∀ P : Finset ℕ, (∀ x ∈ P, x.Prime ∧ x ≠ 2) →
      (∀ e ∈ P, ∀ y, (∀ r ∈ P, r < e → r ≤ y) → e ≤ step y) →
      (((P.filter (fun x => ¬∃ r ∈ P, x+1=2*r))).filter (fun e => B < e)).card ≤ C →
      ∀ p ∈ P, p ≤ K := by
  induction C generalizing B with
  | zero =>
    refine ⟨(fun B : ℕ => 2^B*B+1) B,?_⟩
    intro P pr _ cnt p hp
    apply prefix_bound (X:=p) pr _ p hp le_rfl
    intro e he _
    by_contra! ne
    have mem : e ∈ ((P.filter (fun x => ¬∃ r ∈ P, x+1=2*r))).filter (fun e => B < e) := mem_filter.mpr ⟨he,ne⟩
    have pos:=card_pos.mpr ⟨e,mem⟩
    omega
  | succ c ih =>
    let B':=max B (step ((fun B : ℕ => 2^B*B+1) B))
    obtain ⟨K,hK⟩:=ih B'
    refine ⟨max ((fun B : ℕ => 2^B*B+1) B) K,?_⟩
    intro P pr localBound cnt p hp
    let E:=((P.filter (fun x => ¬∃ r ∈ P, x+1=2*r))).filter (fun e => B < e)
    by_cases ne : E.Nonempty
    · let e:=E.min' ne
      have he : e ∈ E := min'_mem .. 
      have heP : e ∈ P := (mem_filter.mp (mem_filter.mp he).1).1
      have cap : e ≤ step ((fun B : ℕ => 2^B*B+1) B) := by
        apply localBound _ heP
        intro r hr re
        apply prefix_bound (X:=r) pr _ r hr le_rfl
        intro z hz zr
        by_contra! large
        have hmin:=min'_le E z (mem_filter.mpr ⟨hz,large⟩)
        change e ≤ z at hmin
        omega
      let E':=((P.filter (fun x => ¬∃ r ∈ P, x+1=2*r))).filter (fun e => B' < e)
      have sub : E' ⊆ E := by
        intro z hz
        obtain ⟨m,lt⟩:=mem_filter.mp hz
        exact mem_filter.mpr ⟨m,(le_max_left ..).trans_lt lt⟩
      have strict : E' ⊂ E := Finset.ssubset_iff_subset_ne.mpr ⟨sub,by
        intro eq
        have hm : e ∈ E' := eq ▸ he
        have ub : e ≤ B' := cap.trans (le_max_right ..)
        exact (not_lt_of_ge ub) (mem_filter.mp hm).2⟩
      have less:=card_lt_card strict
      have before : E.card ≤ c+1 := cnt
      exact (hK P pr localBound (show E'.card ≤ c by omega) p hp).trans (le_max_right ..)
    · apply le_trans _ (le_max_left ..)
      apply prefix_bound (X:=p) pr _ p hp le_rfl
      intro e he _
      by_contra! z
      exact ne ⟨e,mem_filter.mpr ⟨he,z⟩⟩

/-- Uniformity in this lemma is essential. The bound depends only on the two
statistics, while the other simple primes may have arbitrary cardinality. -/
theorem balanced_bound (C D : ℕ) :
    ∃ A, ∀ (m : ℕ) (P : Finset ℕ), (∀ q ∈ P, q.Prime ∧ q ≠ 2) → 3 ∉ P →
      (2^m+1)*(1+3^5)*∏ q ∈ P, (q+1) = 2^(m+1)*3^5*∏ q ∈ P, q →
      (P.filter (fun q => 4 ∣ q+1)).card ≤ C →
      (∀ q ∈ P, (q+1).factorization 2 ≤ D) → m ≤ A := by
  let step:=fun y : ℕ => ((max 3 y)^(max 5 D))^(max 3 y+1)
  obtain ⟨K,hK⟩:=finite_growth step (2*(C+5)) 0
  refine ⟨244*(K+1)^(K+1),?_⟩
  intro m P pr no3 eq cnt exp
  obtain ⟨cl,_,uniq,_,_,sq,_,_⟩:=facts (N:=({3}:Finset ℕ)) pr
    (fun t pt dv => by
      have he := (Nat.prime_dvd_prime_iff_eq pt Nat.prime_three).mp (pt.dvd_of_dvd_pow dv)
      simpa using he) eq
  have close := fun r (hr:r.Prime) (h2:r ≠ 2) (h3:r ≠ 3) => cl r hr h2 (by simpa using h3)
  have square := fun r (hr:r.Prime) (h2:r ≠ 2) (h3:r ≠ 3) => sq r hr h2 (by simpa using h3)
  have owned : ∀ r ∈ P, ∀ p ∈ P, ∀ q ∈ P, r ∣ p+1 → r ∣ q+1 → p=q := by
    intro r hr
    exact uniq r (pr r hr).1 (pr r hr).2 (by intro ht;have := mem_singleton.mp ht;exact no3 (this ▸ hr))
  let S:=P.filter (fun q => 3 ∣ q+1)
  have lim3 : S.card ≤ 5 := by
    by_contra! large
    have div := prod_dvd_prod_of_dvd (s:=S) (fun _ => 3) (fun q => q+1)
      (fun q hq => (mem_filter.mp hq).2)
    rw [prod_const] at div
    exact budget_kernel3 pr no3 eq (filter_subset _ _) ((pow_dvd_pow 3 (by omega : 5+1 ≤ S.card)).trans
      (dvd_mul_of_dvd_right div _))
  have breaks:=exceptional_count pr no3 close owned square
  have all : ∀ p ∈ P, p ≤ K := by
    apply hK P pr _ ((card_filter_le ..).trans (show ((P.filter (fun x => ¬∃ r ∈ P, x+1=2*r))).card ≤ 2*(C+5) by
      dsimp [S] at lim3;omega))
    intro e he y inherited
    have ep:=(pr e he).1
    have eo:=ep.odd_of_ne_two (pr e he).2
    obtain ⟨t,ht⟩:=eo
    have vertex := value_bound (e+1) (max 3 y) (max 5 D) (by omega) (fun r hr => by
      have pp:=Nat.prime_of_mem_primeFactors hr
      have dv:=Nat.dvd_of_mem_primeFactors hr
      by_cases is2 : r=2
      · subst r;exact ⟨by omega,(exp _ he).trans (le_max_right ..)⟩
      by_cases is3 : r=3
      · subst r
        refine ⟨by omega,le_trans ?_ (le_max_left 5 D)⟩
        by_contra! big
        have d:3^(5+1) ∣ e+1 := (Nat.prime_three.pow_dvd_iff_le_factorization (by omega)).mpr big
        apply budget_kernel3 pr no3 eq (S:={e}) (by simpa using he)
        simpa using dvd_mul_of_dvd_right d (2^m+1)
      have re : r < e := by
        have le := Nat.le_of_dvd (by omega : 0 < e+1) dv
        obtain ⟨w,hw⟩:=pp.odd_of_ne_two is2
        have ne : r ≠ e := by
          rintro rfl
          have := (Nat.dvd_add_right (dvd_refl _)).mp dv
          exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 1) ep.one_lt) this
        omega
      refine ⟨(inherited _ (close r pp is2 is3 e he dv) re).trans (le_max_right ..),?_⟩
      have one : (e+1).factorization r ≤ 1 := by
        by_contra! big
        exact square r pp is2 is3 e he (by simpa [pow_two] using
          (pp.pow_dvd_iff_le_factorization (by omega : e+1 ≠ 0)).mpr (show 2 ≤ (e+1).factorization r by omega))
      omega)
    dsimp [step]
    rw [max_eq_right (by omega : 1 ≤ max 3 y)] at vertex
    omega
  have cardP : P.card ≤ K+1 := by
    simpa using card_le_card (show P ⊆ range (K+1) from fun x hx => mem_range.mpr (by have:=all x hx;omega))
  have dv : 2^m ∣ (2^m+1)*((1+3^5)*∏ q ∈ P, (q+1)) := by
    rw [←mul_assoc,eq,pow_succ]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right ..) _) _
  have co : (2^m).Coprime (2^m+1) := by simp
  have pos : 0 < (1+3^5)*∏ q ∈ P, (q+1) := Nat.mul_pos (by decide) (prod_pos (by intros;omega))
  have size:=Nat.le_of_dvd pos (co.dvd_of_dvd_mul_left dv)
  have small : (∏ q ∈ P, (q+1)) ≤ (K+1)^(K+1) := calc
    _ ≤ ∏ _ ∈ P, (K+1) := prod_le_prod' (fun q h => by have:=all q h;omega)
    _ = (K+1)^P.card := by simp
    _ ≤ _ := Nat.pow_le_pow_right (by omega) cardP
  have := Nat.lt_two_pow_self (n:=m)
  norm_num at size
  omega


lemma count_mixed_and_powers {P : Finset ℕ} {D : ℕ}
    (depth : ∀ p ∈ P, (p+1).factorization 2 ≤ D) :
    (P.filter (fun p => 4 ∣ p+1)).card ≤
    (P.filter (fun p => 4 ∣ p+1 ∧ p+1 ≠ 2^((p+1).factorization 2))).card+(D+1) := by
  let powers:=P.filter (fun p => p+1=2^((p+1).factorization 2))
  have inj : Set.InjOn (fun p : ℕ => (p+1).factorization 2) powers := by
    intro p hp q hq eq
    have a:= (mem_filter.mp hp).2
    have b:= (mem_filter.mp hq).2
    change (p+1).factorization 2=(q+1).factorization 2 at eq
    rw [eq] at a
    omega
  have size : powers.card ≤ D+1 := by
    have sub : powers.image (fun p => (p+1).factorization 2) ⊆ range (D+1) := by
      intro k hk;obtain ⟨p,hp,rfl⟩:=mem_image.mp hk
      exact mem_range.mpr (by have:=depth p (mem_filter.mp hp).1;omega)
    simpa [card_image_of_injOn inj] using card_le_card sub
  let mixed:=P.filter (fun p => 4 ∣ p+1 ∧ p+1 ≠ 2^((p+1).factorization 2))
  have sub : (P.filter (fun p => 4 ∣ p+1)) ⊆ mixed ∪ powers := by
    intro p hp
    obtain ⟨m,d⟩:=mem_filter.mp hp
    by_cases eq : p+1=2^((p+1).factorization 2)
    · exact mem_union_right _ (mem_filter.mpr ⟨m,eq⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨m,d,eq⟩)
  exact (card_le_card sub).trans ((card_union_le ..).trans (Nat.add_le_add_left size _))

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1.H1 := by
  rintro ⟨C,counts⟩ ⟨D,depths⟩
  obtain ⟨A,bound⟩:=balanced_bound (C+(D+1)) D
  refine ⟨A,?_⟩
  intro n perfect rep e5 large sieve deep oddcount
  have nz := perfect.2.ne'
  have simple : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r=1 := by
    intro r hr r2 r3
    have prime:=Nat.prime_of_mem_primeFactors hr
    have pos:=prime.factorization_pos_of_dvd nz (Nat.dvd_of_mem_primeFactors hr)
    have no : ¬2 ≤ n.factorization r := fun h => r3 ((rep r).mp
      ⟨prime,r2,(prime.pow_dvd_iff_le_factorization nz).mpr h⟩)
    omega
  have mem3 : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_three,Nat.dvd_of_factorization_pos (by omega),nz⟩
  obtain ⟨pr,eq⟩:=kernel_balance_one perfect mem3 (by decide) simple
  rw [e5] at eq
  rw [←Nat.factorization_def n Nat.prime_two]
  have dep : ∀ q ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)), (q+1).factorization 2 ≤ D := by
    intro q hq
    obtain ⟨hq,n3⟩:=mem_filter.mp hq
    exact depths n perfect rep e5 large sieve deep oddcount q (mem_of_mem_erase hq)
      (ne_of_mem_erase hq) (by simpa using n3)
  apply bound _ _ pr (by simp) eq _ dep
  apply (count_mixed_and_powers dep).trans
  apply Nat.add_le_add_right _ _
  apply le_trans (card_le_card ?_) (counts n perfect rep e5 large sieve deep oddcount)
  intro q hq
  obtain ⟨h,four⟩:=mem_filter.mp hq
  obtain ⟨hq,n3⟩:=mem_filter.mp h
  exact mem_filter.mpr ⟨mem_erase.mpr ⟨by simpa using n3,mem_of_mem_erase hq⟩,four⟩

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R3
