import FormalConjectures.Wikipedia.DescartesNumber
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Finset.Sort

/-!
Finite search for cube-free Descartes integers with fewer than seven prime factors.
The next base in an increasing factorization is bounded by replacing all
remaining factors of the abundancy ratio by the largest possible factor at that base.
-/

open Finset
open scoped ArithmeticFunction.sigma

namespace OMA.DescartesCube

private def numerator (p : ℕ) : ℕ := p^2+p+1

private def upperOK (k A B p : ℕ) : Bool :=
  decide (2*B*(p^2)^k ≤ A*(numerator p)^k)

private def cut (ok : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ
  | 0, _, hi => hi
  | f+1, lo, hi =>
    let mid := (lo+hi)/2
    if ok mid then cut ok f (mid+1) hi else cut ok f lo mid

private theorem cut_not_ok {ok : ℕ → Bool} (f lo hi : ℕ) (h : ok hi = false) :
    ok (cut ok f lo hi) = false := by
  induction f generalizing lo hi with
  | zero => exact h
  | succ f ih =>
    rw [cut]
    cases hmid : ok ((lo+hi)/2) with
    | true => simpa [hmid] using ih (((lo+hi)/2)+1) hi h
    | false => simpa [hmid] using ih lo ((lo+hi)/2) hmid

private def oneFactor (A B lo : ℕ) (spoof : Bool) : Bool :=
  let d := 2*B-A
  if spoof then
    let p := A/d
    !(d*p == A && decide (lo ≤ p) && decide (9 ≤ p) && p%2 == 1 && p.gcd B == 1) ||
      (B*p == DescartesNumber.descartesExample)
  else
    let D := A^2+4*A*d
    let p := (A+D.sqrt)/(2*d)
    !(d*p^2 == A*(p+1) && decide (lo ≤ p) && p%2 == 1 && p.gcd B == 1) ||
      (B*p^2 == DescartesNumber.descartesExample)

private def verifyRange (ok : ℕ → Bool) (lo n : ℕ) : Bool :=
  if n = 0 then true
  else if n = 1 then ok lo
  else verifyRange ok lo (n/2) && verifyRange ok (lo+n/2) (n-n/2)
termination_by n
decreasing_by all_goals omega

private theorem verifyRange_sound (ok : ℕ → Bool) (lo len : ℕ)
    (h : verifyRange ok lo len = true) {i : ℕ} (hlo : lo ≤ i) (hhi : i < lo+len) :
    ok i = true := by
  rw [verifyRange] at h
  split_ifs at h with h0 h1
  · omega
  · have : i = lo := by omega
    simpa [this] using h
  · rw [Bool.and_eq_true] at h
    by_cases hleft : i < lo+len/2
    · exact verifyRange_sound ok lo (len/2) h.1 hlo hleft
    · exact verifyRange_sound ok (lo+len/2) (len-len/2) h.2 (by omega) (by omega)
termination_by len
decreasing_by all_goals omega

private def advance (next : ℕ → ℕ → ℕ → Bool → Bool)
    (A B lo : ℕ) (spoof : Bool) (i : ℕ) : Bool :=
  let p := lo+2*i
  if p.gcd B != 1 then true
  else if p.minFac == p then next (A*numerator p) (B*p^2) (p+2) spoof
  else if spoof && decide (9 ≤ p) then next (A*(p+1)) (B*p) (p+2) false
  else true

private def verify : ℕ → ℕ → ℕ → ℕ → Bool → Bool
  | 0, A, B, _, _ => (A != 2*B) || (B == DescartesNumber.descartesExample)
  | 1, A, B, lo, spoof =>
    if 2*B ≤ A then true else oneFactor A B lo spoof
  | k+2, A, B, lo, spoof =>
    if 2*B ≤ A then true
    else
      let ok := upperOK (k+2) A B
      if ok 50001 then false
      else
        let hi := cut ok 16 (min lo 50001) 50001
        verifyRange (advance (verify (k+1)) A B lo spoof) 0 ((hi-lo+1)/2)

private structure Factor where
  base : ℕ
  spoof : Bool

private def Factor.num (f : Factor) : ℕ := if f.spoof then f.base+1 else numerator f.base
private def Factor.den (f : Factor) : ℕ := if f.spoof then f.base else f.base^2
private def Factor.valid (f : Factor) : Prop :=
  Odd f.base ∧ if f.spoof then f.base.Composite else f.base.Prime

private def Factor.inOrder (f g : Factor) : Prop := f.base < g.base ∧ f.base.Coprime g.base

private theorem odd_composite_ge_nine {p : ℕ} (hc : p.Composite) (ho : Odd p) : 9 ≤ p := by
  by_contra! h
  have hv : ∀ u : Fin 9, ¬ (u.val.Composite ∧ Odd u.val) := by decide
  exact hv ⟨p,h⟩ ⟨hc,ho⟩

private theorem Factor.den_pos {f : Factor} (h : f.valid) : 0 < f.den := by
  have h0 : 0 < f.base := by obtain ⟨i,hi⟩ := h.1; omega
  unfold den
  split <;> positivity

private theorem Factor.den_lt_num (f : Factor) : f.den < f.num := by
  unfold den num numerator
  cases f.spoof <;> simp

private theorem Factor.cross_bound {f : Factor} {p : ℕ}
    (hp : p ≤ f.base) : f.num * p^2 ≤ f.den * numerator p := by
  let q := f.base
  have hq : p ≤ q := hp
  have h2 : p*p ≤ q*q := Nat.mul_le_mul hq hq
  by_cases hsp : f.spoof = true
  · simp only [Factor.den, Factor.num, hsp, if_true]
    change (q+1)*p^2 ≤ q*numerator p
    unfold numerator
    nlinarith [Nat.mul_le_mul_left p hq]
  · have hs : f.spoof = false := Bool.eq_false_of_not_eq_true hsp
    simp only [Factor.den, Factor.num, hs, Bool.false_eq_true, if_false]
    change numerator q*p^2 ≤ q^2*numerator p
    unfold numerator
    have h3 : p*p*q ≤ p*q*q := by
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        Nat.mul_le_mul_left (p*q) hq
    nlinarith

private theorem upper_sound (L : List Factor) (A B p : ℕ)
    (hL : ∀ x ∈ L, x.valid ∧ p ≤ x.base)
    (heq : A*(L.map Factor.num).prod = 2*(B*(L.map Factor.den).prod))
    (hpos : 0 < (L.map Factor.den).prod) :
    upperOK L.length A B p = true := by
  have hineq : (L.map Factor.num).prod * (p^2)^L.length
      ≤ (L.map Factor.den).prod * (numerator p)^L.length := by
    clear heq hpos
    induction L with
    | nil => simp
    | cons x L ih =>
      have hx := hL x (List.mem_cons_self ..)
      have hrest : ∀ f ∈ L, f.valid ∧ p ≤ f.base :=
        fun y hy => hL y (List.mem_cons_of_mem _ hy)
      simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
      calc
        _ = (x.num*p^2)*((L.map Factor.num).prod*(p^2)^L.length) := by ring
        _ ≤ (x.den*numerator p)*((L.map Factor.den).prod*(numerator p)^L.length) :=
          Nat.mul_le_mul (Factor.cross_bound hx.2) (ih hrest)
        _ = _ := by ring
  unfold upperOK
  apply decide_eq_true
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc
    _ = (2*(B*(L.map Factor.den).prod))*(p^2)^L.length := by ring
    _ = (A*(L.map Factor.num).prod)*(p^2)^L.length := by rw [heq]
    _ = A*((L.map Factor.num).prod*(p^2)^L.length) := by ring
    _ ≤ A*((L.map Factor.den).prod*(numerator p)^L.length) := Nat.mul_le_mul_left _ hineq
    _ = _ := by ring

private theorem product_bounds (L : List Factor) (hL : ∀ x ∈ L, x.valid) :
    0 < (L.map Factor.den).prod ∧ (L.map Factor.den).prod ≤ (L.map Factor.num).prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    obtain ⟨hp,hle⟩ := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
    exact ⟨Nat.mul_pos (Factor.den_pos (hL x (List.mem_cons_self ..))) hp,
      Nat.mul_le_mul x.den_lt_num.le hle⟩

private theorem product_pos_strict {x : Factor} {L : List Factor} (hL : ∀ y ∈ L, y.valid) :
    (x.den*(L.map Factor.den).prod) < x.num*(L.map Factor.num).prod := by
  obtain ⟨hp,hle⟩ := product_bounds L hL
  exact (Nat.mul_lt_mul_of_pos_right x.den_lt_num hp).trans_le (Nat.mul_le_mul_left _ hle)

private theorem prefix_lt {A B : ℕ} (hB : 0 < B) {x : Factor} {L : List Factor}
    (hL : ∀ y ∈ L, y.valid)
    (he : A * (x.num*(L.map Factor.num).prod) = 2*(B*(x.den*(L.map Factor.den).prod))) :
    A < 2*B := by
  by_contra! hbad
  have hg := Nat.mul_le_mul_right (x.num*(L.map Factor.num).prod) hbad
  have hs := Nat.mul_lt_mul_of_pos_left (product_pos_strict (x := x) hL) (by omega : 0 < 2*B)
  have hs' : 2*(B*(x.den*(L.map Factor.den).prod)) < (2*B)*(x.num*(L.map Factor.num).prod) := by
    simpa only [Nat.mul_assoc] using hs
  exact (not_lt_of_ge hg) (he ▸ hs')

private theorem get_deficit {A B n m : ℕ} (h : A*(n+m) = 2*(B*n)) :
    (2*B-A)*n = A*m := by
  rw [Nat.sub_mul]
  rw [Nat.mul_add] at h
  simp only [Nat.mul_assoc]
  omega

private theorem ordinary_last_candidate {A d p : ℕ} (hp : 0 < p) (hd : 0 < d)
    (he : d*p^2 = A*(p+1)) : (A+(A^2+4*A*d).sqrt)/(2*d) = p := by
  have hle : A ≤ d*p := by
    apply Nat.le_of_mul_le_mul_right _ hp
    calc
      A*p ≤ A*(p+1) := Nat.mul_le_mul_left A (by omega)
      _ = d*p^2 := he.symm
      _ = (d*p)*p := by ring
  have hle2 : A ≤ 2*d*p := hle.trans (by nlinarith)
  let u := 2*d*p-A
  have hu : u+A = 2*d*p := Nat.sub_add_cancel hle2
  have hsq := congrArg (fun n : ℕ => n^2) hu
  have hA := congrArg (fun n : ℕ => 2*A*n) hu
  have hh := congrArg (fun n : ℕ => 4*d*n) he
  have hr : u^2 = A^2+4*A*d := by
    change (u+A)^2 = (2*d*p)^2 at hsq
    change 2*A*(u+A) = 2*A*(2*d*p) at hA
    change 4*d*(d*p^2) = 4*d*(A*(p+1)) at hh
    nlinarith
  rw [← hr,Nat.sqrt_eq']
  apply Nat.div_eq_of_eq_mul_right (by omega)
  omega

private theorem oneFactor_sound {A B lo : ℕ} (hAB : A < 2*B) (f : Factor)
    (hf : f.valid) (hlo : lo ≤ f.base) (hcop : f.base.Coprime B)
    (he : A*f.num = 2*(B*f.den))
    (hc : oneFactor A B lo f.spoof = true) : B*f.den = DescartesNumber.descartesExample := by
  let d := 2*B-A
  have hd : 0 < d := Nat.sub_pos_of_lt hAB
  have hm := Nat.odd_iff.mp hf.1
  have hg := hcop.gcd_eq_one
  have hp0 : 0 < f.base := by omega
  cases hsp : f.spoof with
  | true =>
    have hp9 : 9 ≤ f.base := odd_composite_ge_nine (by simpa only [hsp,if_true] using hf.2) hf.1
    simp only [Factor.num,Factor.den,hsp,if_true] at he ⊢
    have h' := get_deficit (show A*(f.base+1) = 2*(B*f.base) from he)
    have hp : A/d = f.base := Nat.div_eq_of_eq_mul_right hd (by simpa [d] using h'.symm)
    rw [hsp] at hc
    change (!(d*(A/d) == A && decide (lo ≤ A/d) && decide (9 ≤ A/d) &&
      (A/d)%2 == 1 && (A/d).gcd B == 1) || (B*(A/d) == DescartesNumber.descartesExample)) = true at hc
    simpa [hp,show d*f.base = A by simpa [d] using h',hlo,hp9,hm,hg] using hc
  | false =>
    simp only [Factor.num,Factor.den,hsp,Bool.false_eq_true,if_false] at he ⊢
    have h' : d*f.base^2 = A*(f.base+1) := by
      apply get_deficit
      simpa [numerator,Nat.add_assoc] using he
    have hp := ordinary_last_candidate hp0 hd h'
    let p := (A+(A^2+4*A*d).sqrt)/(2*d)
    rw [hsp] at hc
    change (!(d*p^2 == A*(p+1) && decide (lo ≤ p) && p%2 == 1 && p.gcd B == 1) ||
      (B*p^2 == DescartesNumber.descartesExample)) = true at hc
    change p = f.base at hp
    simpa [hp,h',hlo,hm,hg] using hc

set_option maxHeartbeats 800000 in
private theorem verify_sound (L : List Factor) (A B lo : ℕ) (spoof : Bool) (hlo : Odd lo)
    (hB : 0 < B)
    (hv : ∀ x ∈ L, x.valid ∧ lo ≤ x.base ∧ x.base.Coprime B)
    (horder : L.Pairwise Factor.inOrder)
    (hcount : (L.filter Factor.spoof).length = if spoof then 1 else 0)
    (heq : A*(L.map Factor.num).prod = 2*(B*(L.map Factor.den).prod))
    (hcheck : verify L.length A B lo spoof = true) :
    B*(L.map Factor.den).prod = DescartesNumber.descartesExample := by
  induction L generalizing A B lo spoof with
  | nil =>
    simp only [List.map_nil,List.prod_nil,mul_one] at heq ⊢
    simpa [verify,heq] using hcheck
  | cons x L ih =>
    have hx := hv x (List.mem_cons_self ..)
    have hrest : ∀ y ∈ L, y.valid := fun y hy => (hv y (List.mem_cons_of_mem _ hy)).1
    have hAB : A < 2*B := prefix_lt (x := x) hB hrest heq
    have hnot : ¬ 2*B ≤ A := by omega
    cases L with
    | nil =>
      have hsp : x.spoof = spoof := by
        cases hxs : x.spoof <;> cases hss : spoof <;> simp [hxs,hss] at hcount ⊢
      simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at heq ⊢
      apply oneFactor_sound hAB x hx.1 hx.2.1 hx.2.2 heq
      simpa [verify,hnot,hsp] using hcheck
    | cons y ys =>
      let L := y::ys
      let k := L.length+1
      let ok := upperOK k A B
      have check' :
          (if ok 50001 then false else
            let hi := cut ok 16 (min lo 50001) 50001
            verifyRange (advance (verify L.length) A B lo spoof) 0 ((hi-lo+1)/2)) = true := by
        simpa [k,L,ok,verify,hnot] using hcheck
      have hcap : ok 50001 = false := by
        cases hc : ok 50001 <;> simp [hc] at check' ⊢
      let hi := cut ok 16 (min lo 50001) 50001
      have hcut := cut_not_ok 16 (min lo 50001) 50001 hcap
      change ok hi = false at hcut
      have hcheckR : verifyRange (advance (verify L.length) A B lo spoof) 0 ((hi-lo+1)/2) = true := by
        simpa only [hi,hcap,Bool.false_eq_true,if_false] using check'
      have hord := List.pairwise_cons.mp horder
      have hlt : x.base < hi := by
        by_contra! hg
        have hall : ∀ q ∈ x::L, q.valid ∧ hi ≤ q.base := by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact ⟨hx.1,hg⟩
          · exact ⟨hrest q hq,hg.trans (hord.1 q hq).1.le⟩
        have he := upper_sound (x::L) A B hi hall heq (product_bounds _ (fun q hq => (hall q hq).1)).1
        have he' : ok hi = true := he
        exact Bool.false_ne_true (hcut.symm.trans he')
      obtain ⟨i,hi'⟩ : ∃ i, lo+2*i = x.base := by
        have h₁ := Nat.odd_iff.mp hlo
        have h₂ := Nat.odd_iff.mp hx.1.1
        exact ⟨(x.base-lo)/2,by have := hx.2.1; omega⟩
      have hiR : i < 0+((hi-lo+1)/2) := by omega
      have hnext := verifyRange_sound _ 0 _ hcheckR (Nat.zero_le i) hiR
      have hxg := hx.2.2.gcd_eq_one
      have hpos : 0 < B*x.den := Nat.mul_pos hB (Factor.den_pos hx.1)
      have hlox : Odd (x.base+2) := by
        obtain ⟨q,hq⟩ := hx.1.1
        exact ⟨q+1,by omega⟩
      have hvalid : ∀ z ∈ L, z.valid ∧ x.base+2 ≤ z.base ∧ z.base.Coprime (B*x.den) := by
        intro z hz
        have hzv := hv z (List.mem_cons_of_mem _ hz)
        obtain ⟨hord,hcop⟩ := hord.1 z hz
        have h₂ := Nat.odd_iff.mp hx.1.1
        have h₃ := Nat.odd_iff.mp hzv.1.1
        have hden : z.base.Coprime x.den := by
          cases hsp : x.spoof
          · simpa [Factor.den,hsp] using hcop.symm.pow_right 2
          · simpa [Factor.den,hsp] using hcop.symm
        exact ⟨hzv.1,by omega,hzv.2.2.mul_right hden⟩
      have hEq' : (A*x.num)*(L.map Factor.num).prod = 2*((B*x.den)*(L.map Factor.den).prod) := by
        simpa only [L,List.map_cons,List.prod_cons,Nat.mul_assoc] using heq
      change B*(x.den*(L.map Factor.den).prod) = DescartesNumber.descartesExample
      rw [← Nat.mul_assoc]
      cases hsp : x.spoof with
      | false =>
        have hp : x.base.Prime := by simpa [Factor.valid,hsp] using hx.1.2
        have ht : (L.filter Factor.spoof).length = if spoof then 1 else 0 := by
          simpa [L,List.filter_cons,hsp] using hcount
        apply ih (A*x.num) (B*x.den) (x.base+2) spoof hlox hpos hvalid hord.2 ht hEq'
        simpa [L,advance,hi',hxg,hp.minFac_eq,Factor.num,Factor.den,hsp] using hnext
      | true =>
        have hp : x.base.Composite := by simpa [Factor.valid,hsp] using hx.1.2
        have hp9 := odd_composite_ge_nine hp hx.1.1
        have hn : x.base.minFac ≠ x.base :=
          fun h => hp.2 (Nat.prime_def_minFac.mpr ⟨hp.1,h⟩)
        have hsp' : spoof = true := by cases spoof <;> simp [List.filter_cons,hsp] at hcount ⊢
        have ht : (L.filter Factor.spoof).length = if false then 1 else 0 := by
          simp [L,List.filter_cons,hsp,hsp'] at hcount ⊢
          omega
        apply ih (A*x.num) (B*x.den) (x.base+2) false hlox hpos hvalid hord.2 ht hEq'
        simpa [L,advance,hi',hxg,hn,hsp',hp9,Factor.num,Factor.den,hsp] using hnext

private theorem sigma_odd_of_factorization {m w : ℕ} (h : DescartesNumber.IsDescartesFactorization m w) :
    Odd (σ 1 m) := by
  obtain ⟨hm,hw⟩ := Nat.odd_mul.mp h.2.1
  have hc : w.Coprime (w+1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have hd : w ∣ σ 1 m := hc.dvd_of_dvd_mul_right ⟨2*m,by simpa [mul_comm w] using h.2.2.2⟩
  obtain ⟨k,hk⟩ := hd
  have hw0 : 0 < w := by obtain ⟨v,hv⟩ := hw; omega
  obtain ⟨v,hv⟩ : Even (w+1) := by obtain ⟨v,hv⟩ := hw; exact ⟨v+1,by omega⟩
  have he : w * (k*(v+v)) = w*(2*m) := by
    calc
      _ = σ 1 m * (w+1) := by rw [hk,hv]; ring
      _ = _ := by rw [h.2.2.2]; ring
  have he' := Nat.eq_of_mul_eq_mul_left hw0 he
  have hm' : m = k*v := by
    have hterm : k*(v+v) = 2*(k*v) := by ring
    omega
  rw [hk]
  exact hw.mul ((Nat.odd_mul.mp (hm' ▸ hm)).1)

private theorem exists_odd_square_of_sigma {m : ℕ} (hm : Odd m) (hs : Odd (σ 1 m)) :
    ∃ r : ℕ, Odd r ∧ m = r^2 := by
  have hm0 : m ≠ 0 := by obtain ⟨v,hv⟩ := hm; omega
  rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm0] at hs
  simp only [mul_one] at hs
  have he (p : ℕ) (hp : p ∈ m.primeFactors) : Even (m.factorization p) := by
    let a := m.factorization p
    let F := fun p : ℕ => ∑ i ∈ range (m.factorization p + 1), p^i
    have hF : Odd (F p) := by
      by_contra! hb
      have h2 : 2 ∣ F p := even_iff_two_dvd.mp ((Nat.not_odd_iff_even).mp hb)
      exact (Nat.not_even_iff_odd.mpr hs)
        (even_iff_two_dvd.mpr (h2.trans (Finset.dvd_prod_of_mem F hp)))
    have hodd : Odd p := hm.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    have ha : Odd (a+1) := by
      change Odd (∑ i ∈ range (a+1),p^i) at hF
      rw [Finset.odd_sum_iff_odd_card_odd] at hF
      have hall : ∀ i ∈ range (a+1), Odd (p^i) := fun _ _ => hodd.pow
      simpa only [Finset.filter_true_of_mem hall, Finset.card_range] using hF
    obtain ⟨j,hj⟩ := ha
    exact ⟨j,by omega⟩
  refine ⟨∏ p ∈ m.primeFactors,p^(m.factorization p/2), ?_, ?_⟩
  · have hq : (∏ p ∈ m.primeFactors,p^(m.factorization p/2)) ∣ m := by
      conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hm0]
      exact prod_dvd_prod_of_dvd _ _ (fun _ _ => pow_dvd_pow _ (Nat.div_le_self _ _))
    exact hm.of_dvd_nat hq
  · rw [← Finset.prod_pow]
    calc
      m = ∏ p ∈ m.primeFactors,p^m.factorization p := Nat.prod_primeFactors_pow_factorization hm0
      _ = _ := by
        apply prod_congr rfl
        intro p hp
        rw [← pow_mul, show m.factorization p / 2 * 2 = m.factorization p by
          obtain ⟨k,hk⟩ := he p hp
          omega]

private theorem exponent_two {m w : ℕ} (hm : Odd m) (hs : Odd (σ 1 m))
    (hcf : Powerfree 3 (m*w)) {p : ℕ} (hp : p ∈ m.primeFactors) :
    m.factorization p = 2 := by
  have hmp : m ≠ 0 := by obtain ⟨i,hi⟩ := hm; omega
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hpPos : 0 < m.factorization p :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by simpa using hp))
  have hep : Even (m.factorization p) := by
    obtain ⟨r,_,hr⟩ := exists_odd_square_of_sigma hm hs
    rw [hr,Nat.factorization_pow,Finsupp.smul_apply,nsmul_eq_mul]
    exact ⟨r.factorization p,by omega⟩
  have hb : m.factorization p < 3 := by
    by_contra! hle
    have hpd : p^3 ∣ m := (hpprime.pow_dvd_iff_le_factorization hmp).mpr hle
    exact hpprime.ne_one (Nat.isUnit_iff.mp (hcf (hpd.trans (dvd_mul_right _ _))))
  obtain ⟨i,hi⟩ := hep
  omega

private def encodeFactor (w p : ℕ) : Factor := ⟨p,p==w⟩

set_option maxHeartbeats 750000 in
private theorem result_of_checks
    (closed : ∀ k ≤ 6, verify k 1 1 3 true = true)
    (n : ℕ) (hd : DescartesNumber.IsDescartesNumber n)
    (hcf : Powerfree 3 n) (hcard : n.primeFactors.card < 7) :
    n = DescartesNumber.descartesExample := by
  classical
  obtain ⟨m,w,rfl,h⟩ := hd
  obtain ⟨hm,hw⟩ := Nat.odd_mul.mp h.2.1
  have hm0 : m ≠ 0 := by obtain ⟨i,hi⟩ := hm; omega
  have hw0 : w ≠ 0 := by have := h.1.1; omega
  have he (p : ℕ) (hp : p ∈ m.primeFactors) :
      m.factorization p = 2 := exponent_two hm (sigma_odd_of_factorization h) hcf hp
  have hprodDen : (∏ p ∈ m.primeFactors,p^2) = m := by
    calc
      _ = ∏ p ∈ m.primeFactors, p^m.factorization p := by
        exact prod_congr rfl (fun p hp => by rw [he p hp])
      _ = _ := (Nat.prod_primeFactors_pow_factorization hm0).symm
  have hprodNum : (∏ p ∈ m.primeFactors,numerator p) = σ 1 m := by
    rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm0]
    apply prod_congr rfl
    intro p hp
    rw [he p hp]
    simp [Finset.sum_range_succ,numerator]
    ring
  have hwn : w ∉ m.primeFactors := fun hw => h.1.2 (Nat.prime_of_mem_primeFactors hw)
  let S := insert w m.primeFactors
  let bases := S.sort
  let factors : List Factor := bases.map (encodeFactor w)
  have hL : factors.length ≤ 6 := by
    have hwcard : 1 ≤ w.primeFactors.card := by
      obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt h.1.1)
      exact Finset.card_pos.mpr ⟨p,Nat.mem_primeFactors.mpr ⟨hp,hpd,hw0⟩⟩
    rw [Nat.primeFactors_mul hm0 hw0, Finset.card_union_of_disjoint h.2.2.1.disjoint_primeFactors] at hcard
    simp only [factors,bases,List.length_map,Finset.length_sort,S,Finset.card_insert_of_notMem hwn]
    omega
  have hmemb {p : ℕ} : p ∈ bases ↔ p = w ∨ p ∈ m.primeFactors := by
    simp [bases,S]
  have hv : ∀ x ∈ factors, x.valid ∧ 3 ≤ x.base ∧ x.base.Coprime 1 := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
    rcases hmemb.mp hp with heq | hp
    · subst p
      have hw9 := odd_composite_ge_nine h.1 hw
      simp [encodeFactor,Factor.valid,hw,show 3 ≤ w by omega]
      exact h.1
    · have hpP := Nat.prime_of_mem_primeFactors hp
      have hpw : p ≠ w := fun h => hwn (h ▸ hp)
      have hpO := hm.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
      have hp3 : 3 ≤ p := by
        have := Nat.odd_iff.mp hpO
        have := hpP.two_le
        omega
      simp [encodeFactor,Factor.valid,hpw,hpO,hpP,hp3]
  have horder : factors.Pairwise Factor.inOrder := by
    apply List.pairwise_map.mpr
    have hsort : bases.Pairwise (· < ·) := (Finset.sortedLT_sort S).pairwise
    apply hsort.imp_of_mem
    intro p q hp hq hlt
    refine ⟨hlt,?_⟩
    change p.Coprime q
    rcases hmemb.mp hp with hpw | hpM
    · rcases hmemb.mp hq with hqw | hqM
      · omega
      · rw [hpw]
        exact h.2.2.1.symm.coprime_dvd_right (Nat.dvd_of_mem_primeFactors hqM)
    · rcases hmemb.mp hq with hqw | hqM
      · rw [hqw]
        exact h.2.2.1.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hpM)
      · exact (Nat.prime_of_mem_primeFactors hpM).coprime_iff_not_dvd.mpr
          (fun hd => hlt.ne ((Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hpM)
            (Nat.prime_of_mem_primeFactors hqM)).mp hd))
  have hcount : (factors.filter Factor.spoof).length = if true then 1 else 0 := by
    simp only [factors,List.filter_map,List.length_map,if_true]
    change (bases.filter (· == w)).length = 1
    rw [← List.count_eq_length_filter]
    exact List.count_eq_one_of_mem (Finset.sort_nodup S _) (hmemb.mpr (Or.inl rfl))
  have hprod (f : ℕ → ℕ) : (bases.map f).prod = ∏ p ∈ S,f p := by
    exact ((Finset.sort_perm_toList S _).map f).prod_eq.trans (S.prod_map_toList f)
  have hden : (factors.map Factor.den).prod = m*w := by
    simp only [factors,List.map_map,hprod,S,prod_insert hwn,Function.comp_apply]
    have hwf : (encodeFactor w w).den = w := by simp [encodeFactor,Factor.den]
    have hF : (∏ p ∈ m.primeFactors,(encodeFactor w p).den) =
        ∏ p ∈ m.primeFactors,p^2 := prod_congr rfl fun p hp =>
      by have hn : p ≠ w := fun he => hwn (he ▸ hp); simp [encodeFactor,Factor.den,hn]
    rw [hwf,hF,hprodDen,mul_comm]
  have hnum : (factors.map Factor.num).prod = (σ 1 m)*(w+1) := by
    simp only [factors,List.map_map,hprod,S,prod_insert hwn,Function.comp_apply]
    have hwf : (encodeFactor w w).num = w+1 := by simp [encodeFactor,Factor.num]
    have hF : (∏ p ∈ m.primeFactors,(encodeFactor w p).num) =
        ∏ p ∈ m.primeFactors,numerator p := prod_congr rfl fun p hp =>
      by have hn : p ≠ w := fun he => hwn (he ▸ hp); simp [encodeFactor,Factor.num,hn]
    rw [hwf,hF,hprodNum,mul_comm]
  have hEq : 1*(factors.map Factor.num).prod = 2*(1*(factors.map Factor.den).prod) := by
    simpa [hnum,hden,Nat.mul_assoc] using h.2.2.2
  simpa [hden] using verify_sound factors 1 1 3 true (by decide) (by decide)
    hv horder hcount hEq (closed factors.length hL)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem certificate0 : verify 0 1 1 3 true = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem certificate1 : verify 1 1 1 3 true = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem certificate2 : verify 2 1 1 3 true = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem certificate3 : verify 3 1 1 3 true = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem certificate4 : verify 4 1 1 3 true = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem certificate5 : verify 5 1 1 3 true = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 160000000 in
private theorem certificate6 : verify 6 1 1 3 true = true := by decide +kernel

private theorem certificates (k : ℕ) (hk : k ≤ 6) : verify k 1 1 3 true = true := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  · exact certificate0
  · exact certificate1
  · exact certificate2
  · exact certificate3
  · exact certificate4
  · exact certificate5
  · exact certificate6

end OMA.DescartesCube

theorem OMA.solution : type_of% @DescartesNumber.descartes_cubeFree_lt_seven_primeFactors_unique :=
  OMA.DescartesCube.result_of_checks OMA.DescartesCube.certificates