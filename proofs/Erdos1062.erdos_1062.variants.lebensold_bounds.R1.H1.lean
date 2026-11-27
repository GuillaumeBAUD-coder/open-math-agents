import OMAReductions.R_Erdos1062_erdos_1062_variants_lebensold_bounds_R1

/-!
A finite certificate for Lebensold’s lower bound. Start with the integers in (n/3,n]. For each of 91 disjoint scale ranges, replace part of this interval in sets of the form r times a 5-smooth integer, with r coprime to 30. The certificate records the additions and deletions; the kernel checks all possible multiples of a new member. On multiples of 30000000000 the resulting density is at least 0.6725070096. Monotonicity absorbs the rounding for arbitrary large n.
-/
namespace L1062
open Finset Erdos1062
structure Pattern where
  lo : ℕ
  hi : ℕ
  inc : Finset ℕ
  del : Finset ℕ
deriving DecidableEq

def options (p : Pattern) (a : ℕ) := (Icc 2 5).filter fun k => k*a<p.hi ∧ k*a∉p.del ∧ (p.lo<3*(k*a) ∨ k*a∈p.inc)
abbrev Valid (p : Pattern) : Prop := 0<p.lo ∧ p.lo<p.hi ∧
    ∀ a∈p.inc, 0<a ∧ 3*a ≤ p.lo ∧ p.hi ≤ 6*a ∧ a∣30^12 ∧ (options p a).card ≤ 1

lemma splitRough {r q a b : ℕ} (hr : r.Coprime b) (hq : q.Coprime a) (e : r*a=q*b) : r=q := by
  exact Nat.dvd_antisymm (hr.dvd_of_dvd_mul_right (e ▸ dvd_mul_right r a))
    (hq.dvd_of_dvd_mul_right (e.symm ▸ dvd_mul_right q b))

lemma trade {ι : Type*} [DecidableEq ι] (J : Finset ι) (r : ι → ℕ) (p : ι → Pattern) (n : ℕ)
    (inj : Set.InjOn r (J:Set ι)) (valid : ∀ i∈J, Valid (p i))
    (rough : ∀ i∈J,(r i).Coprime 30) (rpos : ∀ i∈J,0 < r i)
    (band : ∀ i∈J,(p i).lo * r i  ≤  n ∧ n < (p i).hi * r i) :
    n-n/3 + (∑ i∈J,(p i).inc.card)  ≤  f n + ∑ i∈J,(p i).del.card := by
  classical
  let base := Icc (n/3+1) n
  let lift (i : ι) (S : Finset ℕ) := S.image fun t => r i*t
  let A := J.biUnion fun i => lift i (p i).inc
  let D := J.biUnion fun i => lift i (p i).del
  let V := (base ∪ A) \ D
  have sm {i j : ι} (hi : i∈J) (hj : j∈J) {a : ℕ} (ha : a∈(p j).inc) : (r i).Coprime a :=
    Nat.Coprime.of_dvd_right ((valid j hj).2.2 a ha).2.2.2.1 ((rough i hi).pow_right 12)
  have mulinj {i : ι} (hi : i∈J) : Function.Injective (fun a => r i*a) :=
    fun _ _ eq => Nat.eq_of_mul_eq_mul_left (rpos i hi) eq
  have hdis : (J:Set ι).PairwiseDisjoint fun i => lift i (p i).inc := by
    intro i hi j hj hne
    apply disjoint_left.mpr
    intro v hv hw
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hv
    obtain ⟨b,hb,eq⟩ := mem_image.mp hw
    exact hne (inj hi hj (splitRough (sm hi hj hb) (sm hj hi ha) eq.symm))
  have hA : A.card=∑ i∈J,(p i).inc.card := by
    rw [show A.card=_ from card_biUnion hdis]
    exact sum_congr rfl fun i hi => card_image_of_injective _ (mulinj hi)
  have hD : D.card ≤ ∑ i∈J,(p i).del.card := card_biUnion_le.trans (sum_le_sum (fun _ _ => card_image_le))
  have added {x : ℕ} (hx : x∈A) : ∃ i∈J, ∃ a∈(p i).inc, r i*a=x := by
    obtain ⟨i,hi,hx⟩ := mem_biUnion.mp hx
    obtain ⟨a,ha,eq⟩ := mem_image.mp hx
    exact ⟨i,hi,a,ha,eq⟩
  have bounds {x : ℕ} (hx : x∈A) : 0<x ∧ 3*x ≤ n ∧ n<6*x := by
    obtain ⟨i,hi,a,ha,rfl⟩ := added hx
    have v := (valid i hi).2.2 a ha
    have h1 := Nat.mul_le_mul_right (r i) v.2.1
    have h2 := Nat.mul_le_mul_right (r i) v.2.2.1
    obtain ⟨h3,h4⟩ := band i hi
    exact ⟨Nat.mul_pos (rpos i hi) v.1,by nlinarith,by nlinarith⟩
  have hBA : Disjoint base A := disjoint_left.mpr (fun x h1 h2 => by
    have := (mem_Icc.mp h1).1
    have := (bounds h2).2.1
    omega)
  have sub : V ⊆ Icc 1 n := by
    intro x hx
    rcases mem_union.mp (mem_sdiff.mp hx).1 with h|h
    · exact mem_Icc.mpr ⟨by have := (mem_Icc.mp h).1; omega,(mem_Icc.mp h).2⟩
    · obtain ⟨h1,h2,_⟩ := bounds h; exact mem_Icc.mpr ⟨h1,by omega⟩
  have fork : ForkFree (V:Set ℕ) := by
    intro x hx y hy z hz
    obtain ⟨⟨hy,hy'⟩,k,rfl⟩ := hy
    obtain ⟨⟨hz,hz'⟩,l,rfl⟩ := hz
    have hxpos := (mem_Icc.mp (sub hx)).1
    have hyN := (mem_Icc.mp (sub hy)).2
    have hzN := (mem_Icc.mp (sub hz)).2
    have small {s : ℕ} (hs : x*s∈V) (hne : x*s∉({x}:Set ℕ)) : 2 ≤ s := by
      by_contra! h
      interval_cases s
      · have := (mem_Icc.mp (sub hs)).1; simp at this
      · simp at hne
    have hk := small hy hy'
    have hl := small hz hz'
    congr 1
    rcases mem_union.mp (mem_sdiff.mp hx).1 with hb|hadd
    · have H := (mem_Icc.mp hb).1
      have h3 : n<3*x := by omega
      have cap {t : ℕ} (h : x*t  ≤  n) : t<3 := by
        by_contra! ht
        have := Nat.mul_le_mul_left x ht; nlinarith
      have := cap hyN; have := cap hzN; omega
    obtain ⟨i,hi,a,ha,eq⟩ := added hadd
    have hx6 := (bounds hadd).2.2
    have member {t : ℕ} (ht : 2 ≤ t) (hmem : x*t∈V) : t∈options (p i) a := by
      have hN := (mem_Icc.mp (sub hmem)).2
      have hp := rpos i hi
      have h5 : t ≤ 5 := by
        by_contra! H; have := Nat.mul_le_mul_left x (show 6 ≤ t by omega); nlinarith
      have hnum : r i*(t*a)=x*t := by rw [←eq]; ring
      obtain ⟨blo,bhi⟩ := band i hi
      have top : t*a<(p i).hi := by
        apply (Nat.mul_lt_mul_right hp).mp
        rw [Nat.mul_comm (t*a),hnum]
        omega
      have exc : t*a∉(p i).del := by
        intro hd
        exact (mem_sdiff.mp hmem).2 (mem_biUnion.mpr ⟨i,hi,mem_image.mpr ⟨t*a,hd,hnum⟩⟩)
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨ht,h5⟩,top,exc,?_⟩
      rcases mem_union.mp (mem_sdiff.mp hmem).1 with H|H
      · left
        have hb := (mem_Icc.mp H).1
        have h3 : n<3*(x*t) := by omega
        apply (Nat.mul_lt_mul_right hp).mp
        calc (p i).lo*r i  ≤  n := blo
             _ < 3*(x*t) := h3
             _ = (3*(t*a))*r i := by rw [←hnum]; ring
      · right
        obtain ⟨j,hj,b,hb,hjv⟩ := added H
        have htD : t ∣ 30^12 := by interval_cases t <;> decide
        have cop := Nat.Coprime.of_dvd_right htD ((rough j hj).pow_right 12)
        have eqr := splitRough (sm hi hj hb) (cop.mul_right (sm hj hi ha)) (hnum.trans hjv.symm)
        have e := inj hi hj eqr
        subst j
        have E := mulinj hi (hnum.trans hjv.symm)
        exact E ▸ hb
    exact card_le_one.mp ((valid i hi).2.2 a ha).2.2.2.2 k (member hk hy) l (member hl hz)
  have hf : V.card ≤ f n := by
    apply Nat.le_findGreatest
    · simpa using card_le_card sub
    · exact ⟨(V:Set ℕ),fun _ h => mem_Icc.mp (sub h),fork,Set.ncard_coe_finset _⟩
  have hdel := le_card_sdiff D (base ∪ A)
  have hsplit : (base∪A).card=base.card+A.card := card_union_of_disjoint hBA
  have hb : base.card=n-n/3 := by simp [base]
  change (base ∪ A).card - D.card  ≤  V.card at hdel
  omega
end L1062


namespace L1062
open Finset Erdos1062
def grid : ℕ := 1000000000
def residues : Finset ℕ := {1,7,11,13,17,19,23,29}
theorem res_spec : ∀ c ∈ residues, 0<c ∧ c<30 ∧ c.Coprime 30 := by decide
def blockCount (p : Pattern) := 8 * (grid/p.lo - (grid/p.hi+1))
def pool (p : Pattern) (k : ℕ) := ((Ico ((grid/p.hi+1)*k) (grid/p.lo*k)) ×ˢ residues).image
    fun v : ℕ × ℕ => 30*v.1+v.2

lemma pool_card (p : Pattern) (k : ℕ) : (pool p k).card = k*blockCount p := by
  have hinj : Set.InjOn (fun v : ℕ × ℕ => 30*v.1+v.2)
      ((Ico ((grid/p.hi+1)*k) (grid/p.lo*k) ×ˢ residues : Finset (ℕ × ℕ)) : Set _) := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    have hb := (res_spec _ (mem_product.mp hab).2).2.1
    have hd := (res_spec _ (mem_product.mp hcd).2).2.1
    change 30*a+b=30*c+d at he
    exact Prod.ext (by omega) (by omega)
  rw [pool,card_image_of_injOn hinj,card_product,Nat.card_Ico,show residues.card=8 by decide,←Nat.sub_mul]
  unfold blockCount
  ring

lemma pool_spec {p : Pattern} (hv : Valid p) {k r : ℕ} (hk : 0<k) (hr : r∈pool p k) :
    0<r ∧ r.Coprime 30 ∧ p.lo*r ≤ 30*grid*k ∧ 30*grid*k < p.hi*r := by
  obtain ⟨⟨j,c⟩,hm,rfl⟩ := mem_image.mp hr
  obtain ⟨hj,hc⟩ := mem_product.mp hm
  obtain ⟨hj1,hj2⟩ := mem_Ico.mp hj
  obtain ⟨h0,hc',hcop⟩ := res_spec c hc
  dsimp only at *
  refine ⟨by omega, by simpa using hcop,?_,?_⟩
  · have upper : 30*j+c ≤ 30*(grid/p.lo*k) := by omega
    have H := Nat.mul_le_mul_left p.lo upper
    have H' := Nat.mul_le_mul_right (30*k) (Nat.div_mul_le_self grid p.lo)
    nlinarith only [H,H']
  · have hhi := hv.1.trans hv.2.1
    have base := Nat.lt_mul_div_succ grid hhi
    have H := Nat.mul_lt_mul_of_pos_right base (Nat.mul_pos (by decide : 0<30) hk)
    have H' := Nat.mul_le_mul_left (30*p.hi) hj1
    nlinarith only [H,H',Nat.zero_le (p.hi*c)]

lemma grid_bound (tab : List Pattern) (valid : ∀ p∈tab, Valid p)
    (hsort : tab.Pairwise (fun p q => p.hi ≤ q.lo)) (k : ℕ) (hk : 0<k) :
    20*grid*k + k*(tab.map (fun p => blockCount p*p.inc.card)).sum ≤
    f (30*grid*k) + k*(tab.map (fun p => blockCount p*p.del.card)).sum := by
  classical
  let p (i : Fin tab.length) := tab.get i
  let J := univ.sigma (fun i => pool (p i) k)
  have hv (i : Fin tab.length) := valid (p i) (List.get_mem ..)
  have hsp {z : (i : Fin tab.length) × ℕ} (hz : z∈J) :=
    pool_spec (hv z.1) hk (mem_sigma.mp hz).2
  have hlt (i j : Fin tab.length) (hij : i<j) : (p i).hi ≤ (p j).lo :=
    (List.pairwise_iff_getElem.mp hsort) _ _ i.isLt j.isLt hij
  have hinj : Set.InjOn (fun z : (i : Fin tab.length) × ℕ => z.2) (J : Set _) := by
    rintro ⟨i,r⟩ hi ⟨j,s⟩ hj eq
    change r=s at eq; subst s
    have ha := (hsp hi).2.2
    have hb := (hsp hj).2.2
    rcases lt_trichotomy i j with h|h|h
    · have H := Nat.mul_le_mul_right r (hlt i j h)
      change (p i).lo*r ≤ _ ∧ _ < (p i).hi*r at ha
      change (p j).lo*r ≤ _ ∧ _ < (p j).hi*r at hb
      omega
    · subst j; rfl
    · have H := Nat.mul_le_mul_right r (hlt j i h)
      change (p i).lo*r ≤ _ ∧ _ < (p i).hi*r at ha
      change (p j).lo*r ≤ _ ∧ _ < (p j).hi*r at hb
      omega
  have H := trade J (fun z => z.2) (fun z => p z.1) (30*grid*k) hinj (fun z _ => hv z.1)
    (fun _ hz => (hsp hz).2.1) (fun _ hz => (hsp hz).1) (fun _ hz => (hsp hz).2.2)
  have mass (size : Pattern → ℕ) : (∑ z∈J,size (p z.1)) = k*(tab.map (fun t => blockCount t*size t)).sum := by
    simp only [J,sum_sigma,sum_const,nsmul_eq_mul,pool_card,Nat.cast_id,mul_assoc,←mul_sum]
    congr 1
    rw [←List.sum_ofFn]
    congr 1
    apply List.ext_getElem <;> simp [p]
  rw [mass (fun t => t.inc.card),mass (fun t => t.del.card)] at H
  change 20000000000*k+_ ≤ _+_
  change 30000000000*k-(30000000000*k)/3+_ ≤ _+_ at H
  omega
end L1062


namespace L1062
open Finset
def p0 : Pattern := ⟨27,30,{6,8,9},{18,24}⟩
theorem v0 : Valid p0 := by decide +kernel
def p1 : Pattern := ⟨30,32,{6,8,9,10},{18,24,30}⟩
theorem v1 : Valid p1 := by decide +kernel
def p2 : Pattern := ⟨54,60,{12,15,16,18},{30,36,48}⟩
theorem v2 : Valid p2 := by decide +kernel
def p3 : Pattern := ⟨60,64,{12,16,18,20},{36,48,60}⟩
theorem v3 : Valid p3 := by decide +kernel
def p4 : Pattern := ⟨81,90,{18,24,25,27},{54,72,75}⟩
theorem v4 : Valid p4 := by decide +kernel
def p5 : Pattern := ⟨90,96,{18,24,27,30},{54,72,90}⟩
theorem v5 : Valid p5 := by decide +kernel
def p6 : Pattern := ⟨96,100,{18,24,27,30,32},{54,72,90,96}⟩
theorem v6 : Valid p6 := by decide +kernel
def p7 : Pattern := ⟨100,108,{18,24,27,30,32},{54,72,90,96}⟩
theorem v7 : Valid p7 := by decide +kernel
def p8 : Pattern := ⟨108,120,{24,30,32,36},{60,72,96}⟩
theorem v8 : Valid p8 := by decide +kernel
def p9 : Pattern := ⟨120,125,{24,32,36,40},{72,96,120}⟩
theorem v9 : Valid p9 := by decide +kernel
def p10 : Pattern := ⟨125,128,{24,32,36,40},{72,96,120}⟩
theorem v10 : Valid p10 := by decide +kernel
def p11 : Pattern := ⟨135,144,{30,36,40,45},{72,90,120}⟩
theorem v11 : Valid p11 := by decide +kernel
def p12 : Pattern := ⟨144,150,{30,40,45,48},{90,120,144}⟩
theorem v12 : Valid p12 := by decide +kernel
def p13 : Pattern := ⟨150,160,{30,40,45,48,50},{90,120,144,150}⟩
theorem v13 : Valid p13 := by decide +kernel
def p14 : Pattern := ⟨162,180,{30,36,45,48,50,54},{90,108,120,144,150}⟩
theorem v14 : Valid p14 := by decide +kernel
def p15 : Pattern := ⟨180,192,{36,48,54,60},{108,144,180}⟩
theorem v15 : Valid p15 := by decide +kernel
def p16 : Pattern := ⟨192,200,{36,48,54,60,64},{108,144,180,192}⟩
theorem v16 : Valid p16 := by decide +kernel
def p17 : Pattern := ⟨200,216,{36,48,54,60,64},{108,144,180,192}⟩
theorem v17 : Valid p17 := by decide +kernel
def p18 : Pattern := ⟨216,225,{48,60,64,72},{144,180,192}⟩
theorem v18 : Valid p18 := by decide +kernel
def p19 : Pattern := ⟨225,240,{48,60,64,72,75},{144,150,180,192}⟩
theorem v19 : Valid p19 := by decide +kernel
def p20 : Pattern := ⟨240,243,{48,60,64,72,75,80},{144,150,180,192,240}⟩
theorem v20 : Valid p20 := by decide +kernel
def p21 : Pattern := ⟨243,250,{48,54,60,64,72,75,80,81},{144,150,162,180,192,216,240}⟩
theorem v21 : Valid p21 := by decide +kernel
def p22 : Pattern := ⟨250,256,{48,54,60,64,72,75,80,81},{144,150,162,180,192,216,240}⟩
theorem v22 : Valid p22 := by decide +kernel
def p23 : Pattern := ⟨256,270,{54,60,72,75,80,81},{150,162,180,216,240}⟩
theorem v23 : Valid p23 := by decide +kernel
def p24 : Pattern := ⟨270,288,{60,72,75,80,81,90},{150,162,180,216,240}⟩
theorem v24 : Valid p24 := by decide +kernel
def p25 : Pattern := ⟨288,300,{60,75,80,81,90,96},{150,162,180,240,288}⟩
theorem v25 : Valid p25 := by decide +kernel
def p26 : Pattern := ⟨300,320,{60,80,81,90,96,100},{162,180,240,288,300}⟩
theorem v26 : Valid p26 := by decide +kernel
def p27 : Pattern := ⟨320,324,{54,72,81,90,96,100},{162,216,270,288,300}⟩
theorem v27 : Valid p27 := by decide +kernel
def p28 : Pattern := ⟨324,360,{60,72,90,96,100,108},{180,216,240,288,300}⟩
theorem v28 : Valid p28 := by decide +kernel
def p29 : Pattern := ⟨360,375,{72,96,100,108,120},{216,288,300,360}⟩
theorem v29 : Valid p29 := by decide +kernel
def p30 : Pattern := ⟨375,384,{72,96,100,108,120,125},{216,288,300,360,375}⟩
theorem v30 : Valid p30 := by decide +kernel
def p31 : Pattern := ⟨384,400,{72,96,100,108,120,125,128},{216,288,300,360,375,384}⟩
theorem v31 : Valid p31 := by decide +kernel
def p32 : Pattern := ⟨400,405,{72,96,108,120,125,128},{216,288,360,375,384}⟩
theorem v32 : Valid p32 := by decide +kernel
def p33 : Pattern := ⟨405,432,{72,90,96,108,120,125,128,135},{216,270,288,360,375,384}⟩
theorem v33 : Valid p33 := by decide +kernel
def p34 : Pattern := ⟨432,450,{90,96,120,125,128,135,144},{270,288,360,375,384}⟩
theorem v34 : Valid p34 := by decide +kernel
def p35 : Pattern := ⟨450,480,{90,96,120,128,135,144,150},{270,288,360,384,450}⟩
theorem v35 : Valid p35 := by decide +kernel
def p36 : Pattern := ⟨480,486,{90,96,120,128,135,144,150,160},{270,288,360,384,450,480}⟩
theorem v36 : Valid p36 := by decide +kernel
def p37 : Pattern := ⟨486,500,{90,96,108,120,128,135,144,150,160,162},{270,288,324,360,384,432,450,480}⟩
theorem v37 : Valid p37 := by decide +kernel
def p38 : Pattern := ⟨500,512,{90,96,108,120,128,135,144,150,160,162},{270,288,324,360,384,432,450,480}⟩
theorem v38 : Valid p38 := by decide +kernel
def p39 : Pattern := ⟨512,540,{90,108,120,135,144,150,160,162},{270,324,360,432,450,480}⟩
theorem v39 : Valid p39 := by decide +kernel
def p40 : Pattern := ⟨540,576,{120,144,150,160,162,180},{300,324,360,432,480}⟩
theorem v40 : Valid p40 := by decide +kernel
def p41 : Pattern := ⟨576,600,{120,150,160,162,180,192},{300,324,360,480,576}⟩
theorem v41 : Valid p41 := by decide +kernel
def p42 : Pattern := ⟨600,625,{120,160,162,180,192,200},{324,360,480,576,600}⟩
theorem v42 : Valid p42 := by decide +kernel
def p43 : Pattern := ⟨625,640,{120,160,162,180,192,200},{324,360,480,576,600}⟩
theorem v43 : Valid p43 := by decide +kernel
def p44 : Pattern := ⟨640,648,{108,144,162,180,192,200},{324,432,540,576,600}⟩
theorem v44 : Valid p44 := by decide +kernel
def p45 : Pattern := ⟨648,675,{144,180,192,200,216},{360,432,576,600}⟩
theorem v45 : Valid p45 := by decide +kernel
def p46 : Pattern := ⟨675,720,{144,150,180,192,200,216,225},{360,432,450,576,600}⟩
theorem v46 : Valid p46 := by decide +kernel
def p47 : Pattern := ⟨720,729,{144,150,192,200,216,225,240},{432,450,576,600,720}⟩
theorem v47 : Valid p47 := by decide +kernel
def p48 : Pattern := ⟨729,750,{150,162,192,200,216,225,240,243},{450,486,576,600,648,720}⟩
theorem v48 : Valid p48 := by decide +kernel
def p49 : Pattern := ⟨750,768,{150,162,192,200,216,225,240,243,250},{450,486,576,600,648,720,750}⟩
theorem v49 : Valid p49 := by decide +kernel
def p50 : Pattern := ⟨768,800,{150,162,192,200,216,225,240,243,250,256},{450,486,576,600,648,720,750,768}⟩
theorem v50 : Valid p50 := by decide +kernel
def p51 : Pattern := ⟨800,810,{162,192,216,225,240,243,250,256},{450,486,576,648,720,750,768}⟩
theorem v51 : Valid p51 := by decide +kernel
def p52 : Pattern := ⟨810,864,{144,150,180,192,216,225,240,243,250,256,270},{432,450,486,540,576,600,720,750,768}⟩
theorem v52 : Valid p52 := by decide +kernel
def p53 : Pattern := ⟨864,900,{150,180,192,225,240,243,250,256,270,288},{450,486,540,576,600,720,750,768}⟩
theorem v53 : Valid p53 := by decide +kernel
def p54 : Pattern := ⟨900,960,{180,192,240,243,256,270,288,300},{486,540,576,720,768,900}⟩
theorem v54 : Valid p54 := by decide +kernel
def p55 : Pattern := ⟨960,972,{180,192,240,243,256,270,288,300,320},{486,540,576,720,768,900,960}⟩
theorem v55 : Valid p55 := by decide +kernel
def p56 : Pattern := ⟨972,1000,{180,192,240,256,270,288,300,320,324},{540,576,648,720,768,900,960}⟩
theorem v56 : Valid p56 := by decide +kernel
def p57 : Pattern := ⟨1000,1024,{180,192,240,256,270,288,300,320,324},{540,576,648,720,768,900,960}⟩
theorem v57 : Valid p57 := by decide +kernel
def p58 : Pattern := ⟨1024,1080,{180,216,240,270,288,300,320,324},{540,648,720,864,900,960}⟩
theorem v58 : Valid p58 := by decide +kernel
def p59 : Pattern := ⟨1080,1125,{240,288,300,320,324,360},{648,720,864,900,960}⟩
theorem v59 : Valid p59 := by decide +kernel
def p60 : Pattern := ⟨1125,1152,{240,288,300,320,324,360,375},{648,720,750,864,900,960}⟩
theorem v60 : Valid p60 := by decide +kernel
def p61 : Pattern := ⟨1152,1200,{240,300,320,324,360,375,384},{648,720,750,900,960,1152}⟩
theorem v61 : Valid p61 := by decide +kernel
def p62 : Pattern := ⟨1200,1215,{240,300,320,324,360,375,384,400},{648,720,750,900,960,1152,1200}⟩
theorem v62 : Valid p62 := by decide +kernel
def p63 : Pattern := ⟨1215,1250,{216,240,270,288,300,320,324,360,375,384,400,405},{648,720,750,810,864,900,960,1080,1152,1200}⟩
theorem v63 : Valid p63 := by decide +kernel
def p64 : Pattern := ⟨1250,1280,{216,240,270,288,300,320,324,360,375,384,400,405},{648,720,750,810,864,900,960,1080,1152,1200}⟩
theorem v64 : Valid p64 := by decide +kernel
def p65 : Pattern := ⟨1280,1296,{216,270,288,300,324,360,375,384,400,405},{648,750,810,864,900,1080,1152,1200}⟩
theorem v65 : Valid p65 := by decide +kernel
def p66 : Pattern := ⟨1296,1350,{270,288,300,360,375,384,400,405,432},{750,810,864,900,1080,1152,1200}⟩
theorem v66 : Valid p66 := by decide +kernel
def p67 : Pattern := ⟨1350,1440,{288,300,360,375,384,400,405,432,450},{720,750,810,864,900,1152,1200}⟩
theorem v67 : Valid p67 := by decide +kernel
def p68 : Pattern := ⟨1440,1458,{288,300,375,384,400,405,432,450,480},{750,810,864,900,1152,1200,1440}⟩
theorem v68 : Valid p68 := by decide +kernel
def p69 : Pattern := ⟨1458,1500,{300,324,375,384,400,405,432,450,480,486},{750,810,900,972,1152,1200,1296,1440}⟩
theorem v69 : Valid p69 := by decide +kernel
def p70 : Pattern := ⟨1500,1536,{300,324,384,400,405,432,450,480,486,500},{810,900,972,1152,1200,1296,1440,1500}⟩
theorem v70 : Valid p70 := by decide +kernel
def p71 : Pattern := ⟨1536,1600,{300,324,384,400,405,432,450,480,486,500,512},{810,900,972,1152,1200,1296,1440,1500,1536}⟩
theorem v71 : Valid p71 := by decide +kernel
def p72 : Pattern := ⟨1600,1620,{270,324,360,384,405,432,450,480,486,500,512},{810,972,1080,1152,1296,1350,1440,1500,1536}⟩
theorem v72 : Valid p72 := by decide +kernel
def p73 : Pattern := ⟨1620,1728,{288,300,360,384,432,450,480,486,500,512,540},{864,900,972,1080,1152,1200,1440,1500,1536}⟩
theorem v73 : Valid p73 := by decide +kernel
def p74 : Pattern := ⟨1728,1800,{300,360,384,450,480,486,500,512,540,576},{900,972,1080,1152,1200,1440,1500,1536}⟩
theorem v74 : Valid p74 := by decide +kernel
def p75 : Pattern := ⟨1800,1875,{360,384,480,486,500,512,540,576,600},{972,1080,1152,1440,1500,1536,1800}⟩
theorem v75 : Valid p75 := by decide +kernel
def p76 : Pattern := ⟨1875,1920,{360,384,480,486,500,512,540,576,600,625},{972,1080,1152,1440,1500,1536,1800,1875}⟩
theorem v76 : Valid p76 := by decide +kernel
def p77 : Pattern := ⟨1920,1944,{360,384,480,486,500,512,540,576,600,625,640},{972,1080,1152,1440,1500,1536,1800,1875,1920}⟩
theorem v77 : Valid p77 := by decide +kernel
def p78 : Pattern := ⟨1944,2000,{360,384,480,500,512,540,576,600,625,640,648},{1080,1152,1296,1440,1500,1536,1800,1875,1920}⟩
theorem v78 : Valid p78 := by decide +kernel
def p79 : Pattern := ⟨2000,2025,{360,384,480,512,540,576,600,625,640,648},{1080,1152,1296,1440,1536,1800,1875,1920}⟩
theorem v79 : Valid p79 := by decide +kernel
def p80 : Pattern := ⟨2025,2048,{360,384,450,480,512,540,576,600,625,640,648,675},{1080,1152,1296,1350,1440,1536,1800,1875,1920}⟩
theorem v80 : Valid p80 := by decide +kernel
def p81 : Pattern := ⟨2048,2160,{360,432,450,480,540,576,600,625,640,648,675},{1080,1296,1350,1440,1728,1800,1875,1920}⟩
theorem v81 : Valid p81 := by decide +kernel
def p82 : Pattern := ⟨2160,2187,{450,480,576,600,625,640,648,675,720},{1296,1350,1440,1728,1800,1875,1920}⟩
theorem v82 : Valid p82 := by decide +kernel
def p83 : Pattern := ⟨2187,2250,{450,480,486,576,600,625,640,648,675,720,729},{1350,1440,1458,1728,1800,1875,1920,1944}⟩
theorem v83 : Valid p83 := by decide +kernel
def p84 : Pattern := ⟨2250,2304,{450,480,486,576,600,640,648,675,720,729,750},{1350,1440,1458,1728,1800,1920,1944,2250}⟩
theorem v84 : Valid p84 := by decide +kernel
def p85 : Pattern := ⟨2304,2400,{450,480,486,600,640,648,675,720,729,750,768},{1350,1440,1458,1800,1920,1944,2250,2304}⟩
theorem v85 : Valid p85 := by decide +kernel
def p86 : Pattern := ⟨2400,2430,{450,480,486,600,640,648,675,720,729,750,768,800},{1350,1440,1458,1800,1920,1944,2250,2304,2400}⟩
theorem v86 : Valid p86 := by decide +kernel
def p87 : Pattern := ⟨2430,2500,{432,450,480,540,576,600,640,648,675,720,729,750,768,800,810},{1296,1350,1440,1458,1620,1728,1800,1920,2160,2250,2304,2400}⟩
theorem v87 : Valid p87 := by decide +kernel
def p88 : Pattern := ⟨2500,2560,{432,450,480,540,576,600,640,648,675,720,729,750,768,800,810},{1296,1350,1440,1458,1620,1728,1800,1920,2160,2250,2304,2400}⟩
theorem v88 : Valid p88 := by decide +kernel
def p89 : Pattern := ⟨2560,2592,{432,450,540,576,600,648,675,720,729,750,768,800,810},{1296,1350,1458,1620,1728,1800,2160,2250,2304,2400}⟩
theorem v89 : Valid p89 := by decide +kernel
def p90 : Pattern := ⟨2592,2700,{450,540,576,600,675,720,729,750,768,800,810,864},{1350,1458,1620,1728,1800,2160,2250,2304,2400}⟩
theorem v90 : Valid p90 := by decide +kernel
def table : List Pattern := [p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29,p30,p31,p32,p33,p34,p35,p36,p37,p38,p39,p40,p41,p42,p43,p44,p45,p46,p47,p48,p49,p50,p51,p52,p53,p54,p55,p56,p57,p58,p59,p60,p61,p62,p63,p64,p65,p66,p67,p68,p69,p70,p71,p72,p73,p74,p75,p76,p77,p78,p79,p80,p81,p82,p83,p84,p85,p86,p87,p88,p89,p90]
theorem allvalid : ∀ p∈table, Valid p := by
  intro p hp
  simp only [table,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact v0
  · exact v1
  · exact v2
  · exact v3
  · exact v4
  · exact v5
  · exact v6
  · exact v7
  · exact v8
  · exact v9
  · exact v10
  · exact v11
  · exact v12
  · exact v13
  · exact v14
  · exact v15
  · exact v16
  · exact v17
  · exact v18
  · exact v19
  · exact v20
  · exact v21
  · exact v22
  · exact v23
  · exact v24
  · exact v25
  · exact v26
  · exact v27
  · exact v28
  · exact v29
  · exact v30
  · exact v31
  · exact v32
  · exact v33
  · exact v34
  · exact v35
  · exact v36
  · exact v37
  · exact v38
  · exact v39
  · exact v40
  · exact v41
  · exact v42
  · exact v43
  · exact v44
  · exact v45
  · exact v46
  · exact v47
  · exact v48
  · exact v49
  · exact v50
  · exact v51
  · exact v52
  · exact v53
  · exact v54
  · exact v55
  · exact v56
  · exact v57
  · exact v58
  · exact v59
  · exact v60
  · exact v61
  · exact v62
  · exact v63
  · exact v64
  · exact v65
  · exact v66
  · exact v67
  · exact v68
  · exact v69
  · exact v70
  · exact v71
  · exact v72
  · exact v73
  · exact v74
  · exact v75
  · exact v76
  · exact v77
  · exact v78
  · exact v79
  · exact v80
  · exact v81
  · exact v82
  · exact v83
  · exact v84
  · exact v85
  · exact v86
  · exact v87
  · exact v88
  · exact v89
  · exact v90
theorem sorted_table : table.Pairwise (fun p q => p.hi ≤ q.lo) := by decide +kernel
theorem total_table : (table.map (fun p => blockCount p * p.inc.card)).sum ≥ (table.map (fun p => blockCount p * p.del.card)).sum + 175210288 := by decide +kernel
end L1062

namespace L1062
open Filter Finset Erdos1062
lemma mono_f : Monotone f := by
  classical
  intro n m h
  have spec : ∃ A ⊆ Set.Icc 1 n, ForkFree A ∧ A.ncard=f n := by
    apply Nat.findGreatest_spec (P:=fun k => ∃ A ⊆ Set.Icc 1 n, ForkFree A ∧ A.ncard=k) (m:=0) (Nat.zero_le n)
    exact ⟨∅,Set.empty_subset _,by simp [ForkFree],by simp⟩
  obtain ⟨A,hA,hf,hc⟩ := spec
  apply Nat.le_findGreatest ((Nat.findGreatest_le _).trans h)
  exact ⟨A,hA.trans (Set.Icc_subset_Icc_right h),hf,hc⟩

theorem lower : ∀ᶠ n : ℕ in atTop, (0.6725 : ℝ)*n ≤ f n := by
  filter_upwards [eventually_ge_atTop (30000000000*100000 : ℕ)] with n hn
  let k := n/30000000000
  have hk : 100000 ≤ k := by dsimp [k]; omega
  have H := grid_bound table allvalid sorted_table k (by omega)
  have eff := Nat.mul_le_mul_left k total_table
  rw [Nat.mul_add] at eff
  change 20000000000*k+_ ≤ f (30000000000*k)+_ at H
  have H' := mono_f (show 30000000000*k ≤ n by dsimp [k]; omega)
  have Hn : n<30000000000*(k+1) := by dsimp [k]; omega
  have hnat : 6725*n ≤ 10000*f n := by omega
  have hreal : (6725:ℝ)*n ≤ 10000*f n := by exact_mod_cast hnat
  linarith
end L1062


theorem OMA.solution : OMA.R_Erdos1062_erdos_1062_variants_lebensold_bounds_R1.H1 := L1062.lower
