import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1
import Mathlib

-- Credit: @strantalis. Uses the unitary divisor product and the prime-power
-- product in @adammcarter's Erdős 1052 root reduction.
-- For both exponents at least 5, the ordinary part must contain 5 or 7.
-- We prove this by an unconditional estimate on the full ordinary support.
-- Two boundedness problems remain: the 5-divisible case and the 7-divisible
-- case coprime to 5. Each retains its parent's residue information.
namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R2

open Finset
open OMA.R_Erdos1052_erdos_1052_R1 (prod_eq_two_mul prod_primeFactors_pow_self)

set_option maxHeartbeats 12000000 in
-- A terminal ordinary prime r has r+1 = 2^(i+1)*3^j. The small box is
-- checked by ten exact rational products; the contribution of the two
-- remaining geometric strips is bounded uniformly over finite subsets.
private theorem terminal_grid_upper (s : Finset (ℕ × ℕ)) :
  let gridValue (x : (ℕ × ℕ)) : ℕ := 2^(x.1+1) * 3^x.2

  let gridWeight (x : (ℕ × ℕ)) : ℚ :=
    let p := gridValue x - 1
    if 7 < p ∧ p.Prime then ((p:ℚ)+1)/(p-1) else 1
  (∏ x∈s,(gridWeight x : ℝ)) < 189/100 := by
  classical
  let gridValue (x : (ℕ × ℕ)) : ℕ := 2^(x.1+1) * 3^x.2
  let box : Finset (ℕ × ℕ) := (range 10) ×ˢ (range 7)
  let gridWeight (x : (ℕ × ℕ)) : ℚ :=
    let p := gridValue x - 1
    if 7 < p ∧ p.Prime then ((p:ℚ)+1)/(p-1) else 1
  have weight_ge_one (x : (ℕ × ℕ)) : 1 ≤ gridWeight x := by
    simp only [gridWeight]
    split_ifs with ok
    · have h : (7:ℚ) < (gridValue x-1 : ℕ) := by exact_mod_cast ok.1
      apply (le_div_iff₀ (by linarith)).mpr
      linarith
    · rfl

  let tailWeight (x : (ℕ × ℕ)) : ℝ := 2*(1/2:ℝ)^x.1*(1/3:ℝ)^x.2

  have geom (c : ℝ) (pos : 0≤c) (small : c<1) (N : ℕ) :
      ∑ i∈range N,c^i ≤ (1-c)⁻¹ := by
    rw [←tsum_geometric_of_lt_one pos small]
    apply (summable_geometric_of_lt_one pos small).sum_le_tsum
    intro _ _; positivity

  have grid_sum (s : Finset (ℕ × ℕ)) : ∑ x∈s,tailWeight x ≤ 6 := by
    let M := s.sup Prod.fst + 1
    let N := s.sup Prod.snd + 1
    have sub : s⊆range M ×ˢ range N := by
      intro x hx
      exact mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (le_sup (f:=Prod.fst) hx)),
        mem_range.mpr (Nat.lt_succ_of_le (le_sup (f:=Prod.snd) hx))⟩
    apply le_trans (sum_le_sum_of_subset_of_nonneg sub (by intro i _ _; dsimp [tailWeight]; positivity))
    rw [sum_product]
    simp only [tailWeight,←mul_sum,←sum_mul]
    have h1 := geom (1/2) (by norm_num) (by norm_num) M
    have h2 := geom (1/3) (by norm_num) (by norm_num) N
    norm_num at h1 h2
    calc
      _ ≤ 2*2*(3/2:ℝ) := by gcongr
      _ = _ := by norm_num

  have shift_first (s : Finset (ℕ × ℕ)) (high : ∀ x∈s,10≤x.1) :
      ∑ x∈s,tailWeight x ≤ 6/2^10 := by
    let f (x : (ℕ × ℕ)) : (ℕ × ℕ) := (x.1-10,x.2)
    have inj : Set.InjOn f s := by
      intro x hx y hy eq
      have a := congrArg Prod.fst eq
      have b := congrArg Prod.snd eq
      dsimp [f] at a b
      exact Prod.ext (by have := high x hx; have := high y hy; omega) b
    have h := grid_sum (s.image f)
    rw [sum_image inj] at h
    have same (x : (ℕ × ℕ)) (mem : x∈s) : tailWeight x = (1/2:ℝ)^10*tailWeight (f x) := by
      have eq : x.1=10+(x.1-10) := by have := high x mem; omega
      dsimp [tailWeight,f]; nth_rw 1 [eq]; rw [pow_add]; ring
    rw [sum_congr rfl same,←mul_sum]
    norm_num
    linarith

  have shift_second (s : Finset (ℕ × ℕ)) (high : ∀ x∈s,7≤x.2) :
      ∑ x∈s,tailWeight x ≤ 6/3^7 := by
    let f (x : (ℕ × ℕ)) : (ℕ × ℕ) := (x.1,x.2-7)
    have inj : Set.InjOn f s := by
      intro x hx y hy eq
      have a := congrArg Prod.fst eq
      have b := congrArg Prod.snd eq
      dsimp [f] at a b
      exact Prod.ext a (by have := high x hx; have := high y hy; omega)
    have h := grid_sum (s.image f)
    rw [sum_image inj] at h
    have same (x : (ℕ × ℕ)) (mem : x∈s) : tailWeight x = (1/3:ℝ)^7*tailWeight (f x) := by
      have eq : x.2=7+(x.2-7) := by have := high x mem; omega
      dsimp [tailWeight,f]; nth_rw 1 [eq]; rw [pow_add]; ring
    rw [sum_congr rfl same,←mul_sum]
    norm_num
    linarith

  have tail_sum (s : Finset (ℕ × ℕ)) (out : ∀ x∈s,x∉box) :
      ∑ x∈s,tailWeight x < 9/1000 := by
    let t := s.filter (fun x => 10≤x.1)
    have sub : t⊆s := filter_subset ..
    have first := shift_first t (fun x h => (mem_filter.mp h).2)
    have second := shift_second (s\t) (by
      intro x hx
      obtain ⟨ms,mt⟩ := mem_sdiff.mp hx
      have low : x.1<10 := by by_contra! no; exact mt (mem_filter.mpr ⟨ms,no⟩)
      have outside := out x ms
      simp [box,low] at outside
      exact outside)
    rw [←sum_sdiff sub]
    linarith

  let row (i : ℕ) := ∏ j∈range 7,gridWeight (i,j)

  have row0 : row 0 = 243/208 := by
    norm_num [row,prod_range_succ,gridWeight,gridValue]

  have row1 : row 1 = 157464/128525 := by
    norm_num [row,prod_range_succ,gridWeight,gridValue]

  have row2 : row 2 = 139968/124355 := by
    norm_num [row,prod_range_succ,gridWeight,gridValue]

  have row3 : row 3 = 5184/4945 := by
    norm_num [row,prod_range_succ,gridWeight,gridValue]

  have row4 : row 4 = 34828517376/32548225675 := by
    norm_num [row,prod_range_succ,gridWeight,gridValue]

  have row5 : row 5 = 746496/738625 := by
    norm_num [row,prod_range_succ,gridWeight,gridValue]

  have row6 : row 6 = 786432/768775 := by
    norm_num [row,prod_range_succ,gridWeight,gridValue]

  have row7 : row 7 = 107495424/107460865 := by
    norm_num [row,prod_range_succ,gridWeight,gridValue]

  have row8 : row 8 = 1/1 := by
    norm_num [row,prod_range_succ,gridWeight,gridValue]

  have row9 : row 9 = 13824/13823 := by
    norm_num [row,prod_range_succ,gridWeight,gridValue]

  have box_checked : (∏ x∈box,gridWeight x) < 187/100 := by
    dsimp only [box]
    rw [prod_product]
    change (∏ i∈range 10,row i) < _
    norm_num [prod_range_succ,row0,row1,row2,row3,row4,row5,row6,row7,row8,row9]

  have weight_upper (x : (ℕ × ℕ)) : (gridWeight x : ℝ) ≤ 1+tailWeight x := by
    have x2 : 2 ≤ gridValue x := by
      simp [gridValue,pow_succ]
      have : 0<2^x.1*3^x.2 := by positivity
      nlinarith
    have reciprocal : tailWeight x=4/(gridValue x:ℝ) := by
      simp [tailWeight,gridValue,pow_succ]
      field_simp
      ring
    rw [reciprocal]
    simp only [gridWeight]
    split_ifs with ok
    · have p : ((gridValue x-1 : ℕ):ℝ)=(gridValue x:ℝ)-1 := by
        rw [Nat.cast_sub (by omega : 1≤gridValue x)]; norm_num
      have large : (7:ℝ)<(gridValue x-1 : ℕ) := by exact_mod_cast ok.1
      have den : 0<(gridValue x:ℝ)-1-1 := by linarith
      have pos : 0<(gridValue x:ℝ) := by linarith
      push_cast
      rw [p]
      field_simp
      nlinarith
    · push_cast
      exact le_add_of_nonneg_right (by positivity)

  have product_aux (s : Finset (ℕ × ℕ)) (f : (ℕ × ℕ)→ℝ) (pos : ∀ x,0≤f x) :
      (∏ x∈s,(1+f x)) * (1-∑ x∈s,f x) ≤ 1 := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih =>
      rw [prod_insert hx,sum_insert hx]
      have ps : 0 ≤ ∏ y∈s,(1+f y) := prod_nonneg (fun y _ => by linarith [pos y])
      have ss : 0 ≤ ∑ y∈s,f y := sum_nonneg (fun y _ => pos y)
      have step : (1+f x)*(1-(f x+∑ y∈s,f y))≤1-∑ y∈s,f y := by
        nlinarith [mul_nonneg ss (pos x),sq_nonneg (f x)]
      calc
        _ = (∏ y∈s,(1+f y)) * ((1+f x)*(1-(f x+∑ y∈s,f y))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left step ps
        _ ≤ 1 := ih

  have grid_product_upper (cert : (∏ x∈box,gridWeight x) < 187/100)
      (s : Finset (ℕ × ℕ)) : ∏ x∈s,(gridWeight x:ℝ) < 189/100 := by
    let t := s ∩ box
    have st : t⊆s := inter_subset_left
    have tb : t⊆box := inter_subset_right
    have tail := tail_sum (s\t) (by intro x hx b; exact (mem_sdiff.mp hx).2 (mem_inter.mpr ⟨(mem_sdiff.mp hx).1,b⟩))
    have pos (x : (ℕ × ℕ)) : 0≤tailWeight x := by unfold tailWeight; positivity
    have fpos (x : (ℕ × ℕ)) : 0 ≤ (gridWeight x : ℝ) := by exact_mod_cast (zero_le_one.trans (weight_ge_one x))
    have boxprod : ∏ x∈t,(gridWeight x : ℝ) < 187/100 := by
      have lim : ∏ x∈box,(gridWeight x:ℝ) < 187/100 := by
        have c := (Rat.cast_lt (K:=ℝ)).mpr cert
        push_cast at c
        exact c
      apply lt_of_le_of_lt _ lim
      exact prod_le_prod_of_subset_of_one_le tb (fun x _ => fpos x)
        (fun x _ _ => by exact_mod_cast weight_ge_one x)
    have prelim := product_aux (s\t) tailWeight pos
    have pp : 0 ≤ ∏ x∈s\t,(1+tailWeight x) := prod_nonneg (fun y _ => by linarith [pos y])
    have rem : ∏ x∈s\t,(1+tailWeight x) ≤ 1000/991 := by
      nlinarith [mul_nonneg pp (show 0≤9/1000-∑ x∈s\t,tailWeight x by linarith)]
    have tailprod : ∏ x∈s\t,(gridWeight x:ℝ) ≤ 1000/991 :=
      (prod_le_prod (fun x _ => fpos x) (fun x _ => weight_upper x)).trans rem
    rw [←prod_sdiff st]
    calc
      _ ≤ (1000/991)*(187/100:ℝ) := mul_le_mul tailprod boxprod.le (prod_nonneg (fun x _ => fpos x)) (by norm_num)
      _ < _ := by norm_num
  exact grid_product_upper box_checked s

-- Each nonterminal prime can charge one distinct smaller prime.
set_option maxHeartbeats 12000000 in
private theorem five_or_seven {n : ℕ} (unit : Erdos1052.IsUnitaryPerfect n)
    (rep : ∀ p, p.Prime ∧ p≠2 ∧ p^2∣n ↔ p=3)
    (a : 5≤n.factorization 2) (b : 5≤n.factorization 3) : 5∣n ∨ 7∣n := by
  classical
  let gridValue (x : (ℕ × ℕ)) : ℕ := 2^(x.1+1) * 3^x.2

  let gridWeight (x : (ℕ × ℕ)) : ℚ :=
    let p := gridValue x - 1
    if 7 < p ∧ p.Prime then ((p:ℚ)+1)/(p-1) else 1

  have child_lt {p q : ℕ} (hp : p.Prime) (large : 3<p) (hq : q∈(p+1).primeFactors) : q<p := by
    have prime := Nat.prime_of_mem_primeFactors hq
    have div := Nat.dvd_of_mem_primeFactors hq
    have le := Nat.le_of_dvd (by omega : 0<p+1) div
    by_contra! hi
    by_cases eq : q=p
    · subst q
      exact hp.not_dvd_one ((Nat.dvd_add_iff_right dvd_rfl).mpr div)
    · have ⟨j,odd⟩ := hp.odd_of_ne_two (by omega)
      have ⟨k,odd'⟩ := prime.odd_of_ne_two (by omega)
      omega


  have collision {n a b q : ℕ} (unit : Erdos1052.IsUnitaryPerfect n)
      (ha : a∈n.primeFactors) (hb : b∈n.primeFactors) (ab : a≠b)
      (pq : q.Prime) (odd : q≠2)
      (da : q ∣ 1+a^n.factorization a) (db : q ∣ 1+b^n.factorization b) : q^2∣n := by
    let f := fun p => 1+p^n.factorization p
    have both := Finset.prod_dvd_prod_of_subset {a,b} n.primeFactors f
      (by intro z hz; simp only [mem_insert,mem_singleton] at hz; rcases hz with rfl|rfl <;> assumption)
    have div : q^2∣2*n := by
      rw [←prod_eq_two_mul unit,sq]
      apply (mul_dvd_mul da db).trans
      simpa [f,ab] using both
    have cop := ((Nat.coprime_primes pq Nat.prime_two).mpr odd).pow_left 2
    exact cop.dvd_of_dvd_mul_left div


  let potential (p : ℕ) : ℝ := (p:ℝ)/(p-1)
  let gain (p : ℕ) : ℝ := ((p:ℝ)+1)/p

  have budget_edge {q p : ℕ} (qpos : 3<q) (edge : 2*q≤p+1) :
      gain p * potential p ≤ potential q := by
    have hp : (1:ℝ)<p := by exact_mod_cast (show 1<p by omega)
    have hq : (1:ℝ)<q := by exact_mod_cast (show 1<q by omega)
    have hh : (2:ℝ)*q≤p+1 := by exact_mod_cast edge
    unfold gain potential
    have hp0 : (0:ℝ)<p := by linarith
    have hp1 : 0<(p:ℝ)-1 := by linarith
    have hq1 : 0<(q:ℝ)-1 := by linarith
    rw [div_mul_div_cancel₀ (ne_of_gt hp0)]
    apply (div_le_div_iff₀ hp1 hq1).mpr
    nlinarith

  have abundance_le_terminal (S : Finset ℕ) (large : ∀ q∈S,3<q)
      (I : Finset ℕ) (sub : I⊆S) (child : ℕ→ℕ)
      (into : ∀ p∈I,child p∈S) (inj : Set.InjOn child I)
      (edge : ∀ p∈I,2*child p≤p+1) :
      ∏ p∈S,gain p ≤ ∏ r∈S\I,(gain r * potential r) := by
    have pot (p : ℕ) (m : p∈S) : 1≤potential p := by
      have hp : (1:ℝ)<p := by exact_mod_cast (show 1<p by have := large p m; omega)
      unfold potential
      apply (le_div_iff₀ (by linarith)).mpr
      linarith
    have nonneg {p : ℕ} (mem : p∈S) : 0 ≤ gain p * potential p := by
      apply mul_nonneg _ (by linarith [pot p mem])
      unfold gain; positivity
    have injectprod : (∏ p∈I,potential (child p)) ≤ ∏ q∈S,potential q := by
      rw [←Finset.prod_image inj]
      apply Finset.prod_le_prod_of_subset_of_one_le
      · intro q m; obtain ⟨p,mem,rfl⟩ := mem_image.mp m; exact into p mem
      · intro q m; obtain ⟨p,mem,rfl⟩ := mem_image.mp m; linarith [pot _ (into p mem)]
      · intro q m _; exact pot q m
    have bounded : (∏ p∈I,gain p * potential p) ≤ ∏ q∈S,potential q :=
      le_trans (Finset.prod_le_prod (fun i hi => nonneg (sub hi))
        (fun p hp => budget_edge (large _ (into p hp)) (edge p hp))) injectprod
    have pp : 0 < ∏ q∈S,potential q :=
      Finset.prod_pos (fun p mem => by linarith [pot p mem])
    apply le_of_mul_le_mul_right _ pp
    rw [←Finset.prod_mul_distrib,←Finset.prod_sdiff sub]
    exact mul_le_mul_of_nonneg_left bounded
      (Finset.prod_nonneg (fun i hi => nonneg (mem_sdiff.mp hi).1))

  let ordinarySet (n : ℕ) := n.primeFactors.filter (3<·)
  let nonterminalSet (n : ℕ) := (ordinarySet n).filter (fun p => ∃ q∈(p+1).primeFactors,3<q)

  have unitary_terminal_bound {n : ℕ} (unit : Erdos1052.IsUnitaryPerfect n)
      (rep : ∀ p, p.Prime ∧ p≠2 ∧ p^2∣n ↔ p=3) :
      ∏ p∈ordinarySet n,gain p ≤ ∏ r∈ordinarySet n\nonterminalSet n,(gain r * potential r) := by
    classical
    let S := ordinarySet n
    let I := nonterminalSet n
    have sub : I⊆S := filter_subset ..
    have large {p} (m : p∈S) : 3<p := (mem_filter.mp m).2
    have pf {p} (m : p∈S) : p∈n.primeFactors := (mem_filter.mp m).1
    have exp1 {p} (m : p∈S) : n.factorization p=1 := by
      have prime := Nat.prime_of_mem_primeFactors (pf m)
      have pos := prime.factorization_pos_of_dvd unit.2.ne' (Nat.dvd_of_mem_primeFactors (pf m))
      have gt := large m
      by_contra bad
      have sq := (prime.pow_dvd_iff_le_factorization unit.2.ne').mpr (show 2≤n.factorization p by omega)
      have := (rep p).mp ⟨prime,by omega,sq⟩
      omega
    have pick (p : ℕ) (hp : p∈I) : ∃ q∈(p+1).primeFactors,3<q := (mem_filter.mp hp).2
    let child (p : ℕ) := if hp : p∈I then (pick p hp).choose else 0
    have spec (p : ℕ) (hp : p∈I) : child p∈(p+1).primeFactors ∧ 3<child p := by
      simpa [child,hp] using (pick p hp).choose_spec
    have component {p} (hp : p∈I) : child p∣1+p^n.factorization p := by
      simpa [exp1 (sub hp),Nat.add_comm] using Nat.dvd_of_mem_primeFactors (spec p hp).1
    apply abundance_le_terminal S (fun _ m => large m) I sub child
    · intro p hp
      have prime := Nat.prime_of_mem_primeFactors (spec p hp).1
      have gt := (spec p hp).2
      have d := (component hp).trans (Finset.dvd_prod_of_mem (fun i => 1+i^n.factorization i) (pf (sub hp)))
      rw [OMA.R_Erdos1052_erdos_1052_R1.prod_eq_two_mul unit] at d
      have nd : ¬child p∣2 := by intro div; have := Nat.le_of_dvd (by decide : 0<2) div; omega
      exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨prime,(prime.dvd_mul.mp d).resolve_left nd,unit.2.ne'⟩,gt⟩
    · intro p hp r hr eq
      by_contra distinct
      have gt := (spec p hp).2
      have prime := Nat.prime_of_mem_primeFactors (spec p hp).1
      have dup := collision unit (pf (sub hp)) (pf (sub hr)) distinct prime (by omega)
        (component hp) (eq.symm ▸ component hr)
      have := (rep _).mp ⟨prime,by omega,dup⟩
      omega
    · intro p hp
      have smaller := child_lt (Nat.prime_of_mem_primeFactors (pf (sub hp))) (large (sub hp)) (spec p hp).1
      have ⟨k,mul⟩ := Nat.dvd_of_mem_primeFactors (spec p hp).1
      have hk : 2≤k := by
        by_contra! h
        interval_cases k <;> simp only [Nat.mul_zero,Nat.mul_one] at mul <;> omega
      simpa [Nat.mul_comm,mul] using Nat.mul_le_mul_left (child p) hk

  let encode (p : ℕ) : (ℕ × ℕ) := ((p+1).factorization 2-1,(p+1).factorization 3)

  have terminal_decode {p n : ℕ} (mem : p∈ordinarySet n\nonterminalSet n) :
      gridValue (encode p)=p+1 := by
    obtain ⟨ord,nt⟩ := mem_sdiff.mp mem
    have pf := Nat.prime_of_mem_primeFactors (mem_filter.mp ord).1
    have large : 3<p := (mem_filter.mp ord).2
    have only {q} (mq : q∈(p+1).primeFactors) : q=2 ∨ q=3 := by
      have lo := (Nat.prime_of_mem_primeFactors mq).two_le
      have hi : ¬3<q := fun big => nt (mem_filter.mpr ⟨ord,q,mq,big⟩)
      omega
    have two : 2∣p+1 := by
      have ⟨k,eq⟩ := pf.odd_of_ne_two (by omega)
      exact ⟨k+1,by omega⟩
    have pos := Nat.prime_two.factorization_pos_of_dvd (by omega : p+1≠0) two
    have e : (p+1).factorization 2-1+1 = (p+1).factorization 2 := by omega
    simp only [gridValue,encode,e]
    apply Nat.eq_of_factorization_eq (by positivity) (by omega)
    intro q
    rw [Nat.factorization_mul (by positivity) (by positivity),Nat.factorization_pow,
      Nat.factorization_pow,Nat.prime_two.factorization,Nat.prime_three.factorization]
    by_cases e2 : q=2
    · subst q; simp
    by_cases e3 : q=3
    · subst q; simp
    have absent : (p+1).factorization q=0 := by
      by_contra nz
      have memq : q∈(p+1).primeFactors := by
        rw [←Nat.support_factorization]; exact Finsupp.mem_support_iff.mpr nz
      exact (only memq).elim e2 e3
    simp [Finsupp.smul_single,e2,e3,absent]

  have terminal_inj (n : ℕ) : Set.InjOn encode (ordinarySet n\nonterminalSet n : Finset ℕ) := by
    intro x hx y hy eq
    have e := congrArg gridValue eq
    rw [terminal_decode hx,terminal_decode hy] at e
    omega

  have smooth_product_bound
      {n : ℕ} (no5 : ¬5∣n) (no7 : ¬7∣n) :
      ∏ r∈ordinarySet n\nonterminalSet n,(gain r*potential r) < 189/100 := by
    let T := ordinarySet n\nonterminalSet n
    have h := terminal_grid_upper (T.image encode)
    change (∏ x∈T.image encode,(gridWeight x : ℝ)) < 189/100 at h
    rw [prod_image (terminal_inj n)] at h
    have eq (r : ℕ) (m : r∈T) : (gridWeight (encode r) : ℝ)=gain r*potential r := by
      obtain ⟨pf,gt⟩ := mem_filter.mp (mem_sdiff.mp m).1
      have prime := Nat.prime_of_mem_primeFactors pf
      have dv := Nat.dvd_of_mem_primeFactors pf
      have big : 7<r := by
        by_contra! small
        interval_cases r <;> contradiction
      have v := terminal_decode m
      simp only [gridWeight,v,Nat.add_sub_cancel,if_pos (show 7<r ∧ r.Prime from ⟨big,prime⟩)]
      push_cast
      unfold gain potential
      rw [div_mul_div_cancel₀ (by exact_mod_cast prime.ne_zero : (r:ℝ)≠0)]
    change (∏ r∈T,gain r*potential r)<_
    change (∏ r∈T,(gridWeight (encode r):ℝ))<_ at h
    rwa [prod_congr rfl eq] at h

  let component (p k : ℕ) : ℝ := (1+(p:ℝ)^k)/(p:ℝ)^k

  have unitary_ratio {n : ℕ} (unit : Erdos1052.IsUnitaryPerfect n)
      (rep : ∀ p, p.Prime ∧ p≠2 ∧ p^2∣n ↔ p=3)
      (apos : 0<n.factorization 2) (bpos : 0<n.factorization 3) :
      component 2 (n.factorization 2) * component 3 (n.factorization 3) *
        ∏ p∈ordinarySet n,gain p = 2 := by
    have nz := unit.2.ne'
    have pr : ∏ p∈n.primeFactors,(1+(p:ℝ)^n.factorization p) = 2*n := by
      exact_mod_cast prod_eq_two_mul unit
    have pd : ∏ p∈n.primeFactors,(p:ℝ)^n.factorization p = n := by
      exact_mod_cast prod_primeFactors_pow_self nz
    have val : ∏ p∈n.primeFactors,component p (n.factorization p)=2 := by
      simp only [component,prod_div_distrib,pr,pd]
      field_simp
    have mem2 : 2∈n.primeFactors := by rw [←Nat.support_factorization,Finsupp.mem_support_iff]; omega
    have mem3 : 3∈n.primeFactors := by rw [←Nat.support_factorization,Finsupp.mem_support_iff]; omega
    have eq : n.primeFactors = insert 2 (insert 3 (ordinarySet n)) := by
      ext p
      by_cases m2 : p=2
      · subst p; simp [mem2]
      by_cases m3 : p=3
      · subst p; simp [mem3]
      simp only [ordinarySet,mem_insert,m2,m3,mem_filter,false_or,iff_self_and]
      intro m
      have := (Nat.prime_of_mem_primeFactors m).two_le
      omega
    have small2 : 2∉ordinarySet n := by simp [ordinarySet]
    have small3 : 3∉ordinarySet n := by simp [ordinarySet]
    rw [eq,prod_insert (by simp [small2]),prod_insert small3,←mul_assoc] at val
    have agree (p : ℕ) (mem : p∈ordinarySet n) : component p (n.factorization p)=gain p := by
      obtain ⟨m,big⟩ := mem_filter.mp mem
      have prime := Nat.prime_of_mem_primeFactors m
      have pos := prime.factorization_pos_of_dvd nz (Nat.dvd_of_mem_primeFactors m)
      have one : n.factorization p=1 := by
        by_contra bad
        have div := (prime.pow_dvd_iff_le_factorization nz).mpr (by omega : 2≤n.factorization p)
        have := (rep p).mp ⟨prime,by omega,div⟩
        omega
      simp [one,component,gain,add_comm]
    rwa [prod_congr rfl agree] at val

  have component_upper {p a : ℕ} (prime : p.Prime) (big : 5≤a) :
      component p a ≤ component p 5 := by
    have pos : 0<(p:ℝ) := by exact_mod_cast prime.pos
    have one : 1≤(p:ℝ) := by exact_mod_cast prime.one_le
    have lb := pow_le_pow_right₀ one big
    unfold component
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  by_contra! neither
  obtain ⟨no5,no7⟩ := neither
  have bound := (unitary_terminal_bound unit rep).trans_lt (smooth_product_bound no5 no7)
  have ratio := unitary_ratio unit rep (by omega) (by omega)
  have u := component_upper Nat.prime_two a
  have v := component_upper Nat.prime_three b
  norm_num [component] at u v
  have p2 : 0≤component 2 (n.factorization 2) := by unfold component; positivity
  have p3 : 0≤component 3 (n.factorization 3) := by unfold component; positivity
  have pg : 0≤∏ p∈ordinarySet n,gain p := prod_nonneg (fun p _ => by unfold gain; positivity)
  have c2 : component 2 (n.factorization 2) ≤ 33/32 := u
  have c3 : component 3 (n.factorization 3) ≤ 244/243 := v
  have total : component 2 (n.factorization 2) * component 3 (n.factorization 3) *
      ∏ p∈ordinarySet n,gain p ≤ 33/32*(244/243)*(189/100) := by
    apply mul_le_mul _ bound.le pg (by norm_num)
    exact mul_le_mul c2 c3 p3 (by norm_num)
  rw [ratio] at total
  norm_num at total

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    5 ∣ n →
    800 < n.factorization 3 →
    (∀ d ∈ ({502, 503, 508, 509, 512, 514, 521, 523, 524, 526, 538, 541, 542, 547, 548, 554, 556, 557,
        562, 563, 566, 569, 571, 586, 587, 593, 596, 599, 601, 604, 607, 613, 614, 617, 619,
        622, 626, 628, 631, 634, 641, 643, 647, 652, 653, 659, 661, 662, 668, 673, 674, 677,
        683, 691, 692, 694, 698, 701, 706, 709, 716, 718, 719, 724, 727, 733, 734, 739, 743,
        746, 751, 757, 758, 761, 766, 769, 772, 773, 778, 787, 788, 794, 796, 797} : Finset ℕ),
      n.factorization 3 % (2 * d) ≠ d) →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    (¬5 ∣ n ∧ 7 ∣ n) →
    800 < n.factorization 3 →
    (∀ d ∈ ({502, 503, 508, 509, 512, 514, 521, 523, 524, 526, 538, 541, 542, 547, 548, 554, 556, 557,
        562, 563, 566, 569, 571, 586, 587, 593, 596, 599, 601, 604, 607, 613, 614, 617, 619,
        622, 626, 628, 631, 634, 641, 643, 647, 652, 653, 659, 661, 662, 668, 673, 674, 677,
        683, 691, 692, 694, 698, 701, 706, 709, 716, 718, 719, 724, 727, 733, 734, 739, 743,
        746, 751, 757, 758, 761, 766, 769, 772, 773, 778, 787, 788, 794, 796, 797} : Finset ℕ),
      n.factorization 3 % (2 * d) ≠ d) →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1.H1 := by
  rintro ⟨A,hA⟩ ⟨B,hB⟩
  refine ⟨max 4 (max A B),?_⟩
  intro n unit rep b res3 res2
  have va : n.factorization 2=padicValNat 2 n := by
    rw [Nat.factorization_def n Nat.prime_two]
  by_cases large : 5≤n.factorization 2
  · by_cases d : 5∣n
    · have := hA n unit rep d b res3 res2
      omega
    · have sev := (five_or_seven unit rep large (by omega)).resolve_left d
      have := hB n unit rep ⟨d,sev⟩ b res3 res2
      omega
  · omega

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R2
