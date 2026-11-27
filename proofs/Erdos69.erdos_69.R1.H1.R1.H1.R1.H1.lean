import OMAReductions.R_Erdos69_erdos_69_R1_H1_R1_H1_R1
import Mathlib

/-! Credit: @marcusbuffett. A positive-density intersection argument constructs a prime Hilbert cube with bounded-coefficient independent directions and basepoint. Chebyshev estimates supply enough primes. -/

namespace PrimeCube69
open Finset Filter
open scoped Classical Topology

private def intersectShift (A : Finset ℕ) (d : ℕ) := A.filter fun b => b+d ∈ A

private lemma pair_count {A : Finset ℕ} {N : ℕ} (bound : ∀ a ∈ A, a ≤ N) :
    A.card^2 ≤ 2*∑ d ∈ range (N+1), (intersectShift A d).card := by
  let code (a : ℕ × ℕ) : Bool × (Σ _ : ℕ, ℕ) :=
    if a.1 ≤ a.2 then (false,⟨a.2-a.1,a.1⟩) else (true,⟨a.1-a.2,a.2⟩)
  let decode (v : Bool × (Σ _ : ℕ, ℕ)) : ℕ × ℕ :=
    if v.1 then (v.2.2+v.2.1,v.2.2) else (v.2.2,v.2.2+v.2.1)
  have hinj : Function.Injective code := by
    apply Function.LeftInverse.injective (g:=decode)
    rintro ⟨a,b⟩
    by_cases h : a ≤ b
    · simp [code,decode,h,Nat.add_sub_of_le h]
    · simp [code,decode,h,Nat.add_sub_of_le (by omega : b ≤ a)]
  let T := (univ : Finset Bool) ×ˢ ((range (N+1)).sigma (intersectShift A))
  have h : (A ×ˢ A).card ≤ T.card := by
    apply card_le_card_of_injOn code _ hinj.injOn
    rintro ⟨a,b⟩ hab
    obtain ⟨ha,hb⟩ := mem_product.mp hab
    have ha' := bound a ha
    have hb' := bound b hb
    by_cases hab' : a ≤ b
    · have z : b-a < N+1 := by omega
      simp [T,code,hab',z,intersectShift,ha,hb,Nat.add_sub_of_le hab']
    · have z : a-b < N+1 := by omega
      simp [T,code,hab',z,intersectShift,hb,ha,Nat.add_sub_of_le (by omega : b ≤ a)]
  simpa [T,pow_two] using h

private lemma good_shift {A D : Finset ℕ} {N : ℕ} (bound : ∀ a ∈ A, a ≤ N)
    (large : 4*D.card < A.card) :
    ∃ d ∈ range (N+1), d ∉ D ∧
      (A.card:ℝ)^2/(8*((N:ℝ)+1)) ≤ (intersectShift A d).card := by
  classical
  let I := range (N+1)
  let good := I \ D
  let bad := I ∩ D
  have hcov : good ∪ bad = I := by ext x; simp [good,bad]; tauto
  let f (d : ℕ) : ℝ := (intersectShift A d).card
  have hcnt : (A.card:ℝ)^2 ≤ 2*∑ d ∈ I, f d := by
    dsimp only [I,f]; exact_mod_cast pair_count bound
  have badsum : ∑ d ∈ bad, f d ≤ D.card*(A.card:ℝ) := by
    calc
      _ ≤ ∑ _ ∈ bad, (A.card:ℝ) := sum_le_sum fun d _ => by
        dsimp only [f]; exact_mod_cast card_filter_le A _
      _ = (bad.card:ℝ)*A.card := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card inter_subset_right) (Nat.cast_nonneg _)
  have split : (∑ d ∈ I, f d) = (∑ d ∈ good, f d)+(∑ d ∈ bad, f d) := by
    conv_lhs => rw [←hcov]
    exact sum_union (by
      apply disjoint_left.mpr
      intro a ha hb
      exact (mem_sdiff.mp ha).2 (mem_inter.mp hb).2)
  rw [split] at hcnt
  by_contra! h
  let B := (A.card:ℝ)^2/(8*((N:ℝ)+1))
  have goodsum : ∑ d ∈ good, f d ≤ ((N:ℝ)+1)*B := by
    calc
      _ ≤ ∑ _ ∈ good, B := sum_le_sum fun d hd =>
        (h d (mem_sdiff.mp hd).1 (mem_sdiff.mp hd).2).le
      _ = (good.card:ℝ)*B := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by dsimp [B]; positivity)
        exact_mod_cast (show good.card ≤ N+1 from (card_le_card sdiff_subset).trans (by simp [I]))
  have den : 0 < (N:ℝ)+1 := by positivity
  have e : ((N:ℝ)+1)*B = (A.card:ℝ)^2/8 := by dsimp [B]; field_simp
  rw [e] at goodsum
  have hlarge : 4*(D.card:ℝ) < A.card := by exact_mod_cast large
  have ha : (0:ℝ)<A.card := by exact_mod_cast (show 0 < A.card by omega)
  nlinarith only [hcnt,badsum,goodsum,mul_lt_mul_of_pos_right hlarge ha,sq_pos_of_pos ha]

/-- No nonzero bounded coefficients give a vanishing combination of the chosen directions. -/
private def Free (v : ℕ → ℕ) (j M : ℕ) : Prop :=
  ∀ c : ℕ → ℤ, (∀ i<j, |c i| ≤ M) → (∑ i ∈ range j, c i*(v i:ℤ)) = 0 →
    ∀ i<j, c i = 0

private noncomputable def banned (v : ℕ → ℕ) (j M : ℕ) : Finset ℕ :=
  univ.image fun c : Fin (j+1) → Fin (2*M+1) =>
    let a (i : Fin (j+1)) : ℤ := (c i:ℕ)-(M:ℤ)
    ((-(∑ i : Fin j, a i.castSucc * (v i:ℤ)))/a (Fin.last j)).toNat

private lemma banned_card (v : ℕ → ℕ) (j M : ℕ) : (banned v j M).card ≤ (2*M+1)^(j+1) := by
  exact card_image_le.trans (by simp)

private lemma extend_free {v : ℕ → ℕ} {j M d : ℕ} (hf : Free v j M) (hd : d ∉ banned v j M) :
    Free (Function.update v j d) (j+1) M := by
  intro c hc heq
  let code (i : Fin (j+1)) : Fin (2*M+1) :=
    ⟨((c i+(M:ℤ)).toNat), by
      have b := abs_le.mp (hc i i.isLt)
      omega⟩
  have decode (i : Fin (j+1)) : ((code i:ℕ):ℤ)-(M:ℤ)=c i := by
    have b := abs_le.mp (hc i i.isLt)
    dsimp [code]
    omega
  have old : (∑ i ∈ range j, c i*(Function.update v j d i:ℤ)) =
      ∑ i ∈ range j, c i*(v i:ℤ) := by
    apply sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Nat.ne_of_lt (mem_range.mp hi))]
  rw [sum_range_succ,old,Function.update_self] at heq
  have cj : c j=0 := by
    by_contra hn
    apply hd
    apply mem_image.mpr
    refine ⟨code, mem_univ _,?_⟩
    dsimp only
    simp_rw [decode]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => c i*(v i:ℤ)) j]
    have he : -(∑ i ∈ range j, c i*(v i:ℤ)) = (d:ℤ)*c j := by linarith
    rw [he,Int.mul_ediv_cancel _ hn]
    simp
  have zero := hf c (fun i hi => hc i (by omega)) (by simpa [cj] using heq)
  intro i hi
  by_cases eq : i=j
  · simpa [eq] using cj
  · exact zero i (by omega)


private lemma dense_directions (N K M : ℕ) (A : Finset ℕ) (hA : A ⊆ range (N+1)) :
    let X : ℝ := (N:ℝ)+1
    let δ := (A.card:ℝ)/(8*X)
    8*((2*M+1:ℕ):ℝ)^(K+1) < X*δ^(2^K) →
    ∃ (z : ℕ) (v : ℕ → ℕ), Free (Function.update v K z) (K+1) M ∧
      ∀ E ⊆ range K, z + ∑ i ∈ E, v i ∈ A := by
  classical
  intro X δ hL
  have hX : 0 < X := by dsimp [X]; positivity
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have hcard : A.card ≤ N+1 := (card_le_card hA).trans (by simp)
  have hδ1 : δ ≤ 1 := by
    apply (div_le_one (show 0<8*X by positivity)).2
    have hz : (A.card:ℝ) ≤ X := by dsimp [X]; exact_mod_cast hcard
    linarith
  have levels (j : ℕ) (hj : j≤K) : 8*((2*M+1:ℕ):ℝ)^(j+1) < X*δ^(2^j) := by
    calc
      _ ≤ 8*((2*M+1:ℕ):ℝ)^(K+1) := by
        gcongr
        · exact_mod_cast (show 1≤2*M+1 by omega)
      _ < _ := hL
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hδ0 hδ1
        (Nat.pow_le_pow_right (by decide : 0<2) hj)) hX.le
  have induction_step (j : ℕ) (hj : j≤K) :
      ∃ v : ℕ → ℕ, ∃ T : Finset ℕ, T ⊆ A ∧ Free v j M ∧
        8*X*δ^(2^j) ≤ T.card ∧ ∀ b ∈ T, ∀ E ⊆ range j, b+∑ i ∈ E, v i ∈ A := by
    induction j with
    | zero =>
      refine ⟨fun _ => 0,A,Subset.rfl,fun _ _ _ i hi => by omega,?_,?_⟩
      · simp only [pow_zero,pow_one,δ]
        field_simp [hX.ne'] <;> rfl
      · intro b hb E he
        simpa using hb
    | succ j ih =>
      have hj' : j≤K := by omega
      obtain ⟨v,T,ht,hfree,hsize,hbase⟩ := ih hj'
      have hl := levels j hj'
      have hbc : ((banned v j M).card:ℝ) ≤ ((2*M+1:ℕ):ℝ)^(j+1) := by exact_mod_cast banned_card v j M
      have hs : 4*(banned v j M).card < T.card := by
        have non : 0 ≤ X*δ^(2^j) := mul_nonneg hX.le (pow_nonneg hδ0 _)
        exact_mod_cast (show 4*((banned v j M).card:ℝ) < T.card by nlinarith)
      obtain ⟨d,_,hd,hnew⟩ := good_shift (fun b hb => Nat.le_of_lt_succ (mem_range.mp (hA (ht hb)))) hs
      refine ⟨Function.update v j d,intersectShift T d,
        fun b hb => ht (mem_filter.mp hb).1, extend_free hfree hd,?_,?_⟩
      · apply le_trans _ hnew
        apply (le_div_iff₀ (show 0<8*((N:ℝ)+1) by positivity)).2
        have sqle := pow_le_pow_left₀ (show 0≤8*X*δ^(2^j) by positivity) hsize 2
        change 8*X*δ^(2^(j+1))*(8*X) ≤ _
        rw [pow_succ, pow_mul]
        nlinarith only [sqle]
      · intro b hb E hE
        obtain ⟨hb,hbd⟩ := mem_filter.mp hb
        have old (F : Finset ℕ) (hf : F ⊆ range j) :
            ∑ i ∈ F, Function.update v j d i = ∑ i ∈ F, v i := by
          apply sum_congr rfl
          intro i hi
          exact Function.update_of_ne (Nat.ne_of_lt (mem_range.mp (hf hi))) _ _
        by_cases hjE : j ∈ E
        · have hF : E.erase j ⊆ range j := by
            intro i hi
            have mem := mem_erase.mp hi
            have bound := mem_range.mp (hE mem.2)
            exact mem_range.mpr (by omega)
          obtain he := hbase (b+d) hbd (E.erase j) hF
          rw [← insert_erase hjE, sum_insert (notMem_erase _ _),Function.update_self,old _ hF]
          simpa [Nat.add_assoc] using he
        · have hF : E ⊆ range j := by
            intro i hi
            have bound := mem_range.mp (hE hi)
            have ne : i≠j := fun e => hjE (e ▸ hi)
            exact mem_range.mpr (by omega)
          rw [old E hF]
          exact hbase b hb E hF
  obtain ⟨v,T,_,hf,hsize,hbase⟩ := induction_step K le_rfl
  have hb : ((banned v K M).card:ℝ) ≤ ((2*M+1:ℕ):ℝ)^(K+1) := by exact_mod_cast banned_card v K M
  have non : 0 ≤ X*δ^(2^K) := mul_nonneg hX.le (pow_nonneg hδ0 _)
  have hlt : (banned v K M).card < T.card := by
    exact_mod_cast (show ((banned v K M).card:ℝ) < T.card by nlinarith)
  obtain ⟨z,hz,hz'⟩ := exists_mem_notMem_of_card_lt_card hlt
  exact ⟨z,v,extend_free hf hz',hbase z hz⟩



private lemma unique_digits {v : ℕ → ℕ} {j M : ℕ} (hf : Free v j M)
    (a b : ℕ → ℤ) (ha : ∀ i<j, 0 ≤ a i ∧ a i ≤ M) (hb : ∀ i<j, 0 ≤ b i ∧ b i ≤ M)
    (he : (∑ i ∈ range j, a i*(v i:ℤ)) = ∑ i ∈ range j, b i*(v i:ℤ)) :
    ∀ i<j, a i = b i := by
  have h := hf (fun i => a i-b i) (fun i hi => abs_le.mpr
    ⟨by linarith [(ha i hi).1,(hb i hi).2],by linarith [(ha i hi).2,(hb i hi).1]⟩)
    (by simp only [sub_mul,sum_sub_distrib,he,sub_self])
  intro i hi
  exact sub_eq_zero.mp (h i hi)

private def digit (K : ℕ) (E : Finset ℕ) (g : ℕ → ℤ) (h : ℤ) (i : ℕ) : ℤ :=
  if i=K then h else if i ∈ E then g i else 0

private lemma representation (K z : ℕ) (v : ℕ → ℕ) (E : Finset ℕ) (hE : E ⊆ range K)
    (g : ℕ → ℤ) (h : ℤ) :
    (∑ i ∈ range (K+1), digit K E g h i * (Function.update v K z i:ℤ)) =
      (∑ i ∈ E, g i*(v i:ℤ))+h*z := by
  rw [sum_range_succ]
  simp only [digit,if_pos rfl,Function.update_self]
  congr 1
  have fe : (range K).filter (· ∈ E) = E := filter_mem_eq_inter.trans (inter_eq_right.mpr hE)
  rw [←fe,sum_filter]
  apply sum_congr rfl
  intro i hi
  have hn := (mem_range.mp hi).ne
  simp [hn,mem_range.mp hi,Function.update_of_ne hn,ite_mul]

private lemma finite_cube (N K H : ℕ) (hK : 0<K) (A : Finset ℕ) (hA : A ⊆ range (N+1))
    (large : 8*((2*(K+H+1)+1:ℕ):ℝ)^(K+1) < ((N:ℝ)+1)*
      ((A.card:ℝ)/(8*((N:ℝ)+1)))^(2^K)) :
    ∃ (p : Finset ℕ → ℕ) (s : Finset ℕ → ℤ),
      (∀ E ∈ (range K).powerset, p E ∈ A ∧ |s E| ≤ 8*(K:ℤ)^2*p E ∧
        ∀ k<K, (p (symmDiff E {k}):ℤ)*(k+1:ℕ)-s (symmDiff E {k}) =
          (p E:ℤ)*(k+1:ℕ)-s E) ∧ Set.InjOn p ((range K).powerset) ∧
      (∏ a ∈ ((range K).powerset ×ˢ Ico (K+1) (K+H+1)).offDiag,
        (((p a.1.1:ℤ)*a.1.2-s a.1.1)-((p a.2.1:ℤ)*a.2.2-s a.2.1)).natAbs) ≠ 0 := by
  classical
  let M := K+H+1
  obtain ⟨z,v,hf,hA'⟩ := dense_directions N K M A hA large
  let p (E : Finset ℕ) := z+∑ i ∈ E, v i
  let s (E : Finset ℕ) : ℤ := ∑ i ∈ E, ((i:ℤ)+1)*v i
  have hr (E : Finset ℕ) (h : ℕ) : (p E:ℤ)*h-s E =
      (∑ i ∈ E, ((h:ℤ)-(i+1))*v i) + (h:ℤ)*z := by
    dsimp only [p,s]
    push_cast
    simp only [sub_mul,sum_sub_distrib,sum_mul,add_mul]
    ring_nf
  refine ⟨p,s,?_,?_,?_⟩
  · intro E hE
    have he := mem_powerset.mp hE
    refine ⟨hA' E he,?_,?_⟩
    · have hspos : 0 ≤ s E := sum_nonneg fun i _ => by positivity
      rw [abs_of_nonneg hspos]
      calc
        _ ≤ ∑ i ∈ E, (K:ℤ)*v i := sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_range.mp (he hi))) (by positivity)
        _ = (K:ℤ)*↑(∑ i ∈ E, v i) := by push_cast; rw [mul_sum]
        _ ≤ (K:ℤ)*(p E:ℤ) := by
          gcongr
          exact_mod_cast (Nat.le_add_left (∑ i ∈ E, v i) z)
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hk : (1:ℤ) ≤ K := by exact_mod_cast hK
          nlinarith [sq_nonneg ((K:ℤ)-1)]
    · intro k _
      rw [hr,hr]
      congr 1
      let t (i : ℕ) : ℤ := (((k+1:ℕ):ℤ)-(i+1))*v i
      change (∑ i ∈ symmDiff E {k}, t i) = ∑ i ∈ E, t i
      have tk : t k = 0 := by simp [t]
      by_cases hk : k∈E
      · have hsd : symmDiff E {k} = E.erase k := by
          ext i; simp only [mem_symmDiff,mem_erase,mem_singleton]; aesop
        have hsum := sum_erase_add E t hk
        simpa [hsd,tk] using hsum
      · have hsd : symmDiff E {k} = insert k E := by
          ext i; simp only [mem_symmDiff,mem_insert,mem_singleton]; aesop
        simp [hsd,sum_insert hk,tk]
  · intro E he F hF heq
    have bound (F : Finset ℕ) (i : ℕ) (_ : i<K+1) :
        0 ≤ digit K F (fun _ => 1) 1 i ∧ digit K F (fun _ => 1) 1 i ≤ M := by
      dsimp [digit,M]; split <;> (try split) <;> omega
    have eq := unique_digits hf _ _ (bound E) (bound F) (by
      rw [representation _ _ _ _ (mem_powerset.mp he),representation _ _ _ _ (mem_powerset.mp hF)]
      have h : (p E:ℤ) = (p F:ℤ) := by exact_mod_cast heq
      simpa [p,add_comm] using h)
    ext i
    by_cases hi : i<K
    · have hh := eq i (by omega)
      by_cases he : i∈E <;> by_cases hf : i∈F <;> simp_all [digit,hi.ne]
    · have h1 : i ∉ E := fun h => hi (mem_range.mp (mem_powerset.mp he h))
      have h2 : i ∉ F := fun h => hi (mem_range.mp (mem_powerset.mp hF h))
      simp [h1,h2]
  · apply prod_ne_zero_iff.mpr
    rintro ⟨⟨E,h⟩,⟨F,g⟩⟩ hpair hbad
    obtain ⟨he,hf',hne⟩ := mem_offDiag.mp hpair
    obtain ⟨e0,eh⟩ := mem_product.mp he
    obtain ⟨f0,fg⟩ := mem_product.mp hf'
    have eS := mem_powerset.mp e0
    have fS := mem_powerset.mp f0
    have h1 := mem_Ico.mp eh
    have h2 := mem_Ico.mp fg
    change K+1 ≤ h ∧ h<K+H+1 at h1
    change K+1 ≤ g ∧ g<K+H+1 at h2
    have bad := sub_eq_zero.mp (Int.natAbs_eq_zero.mp hbad)
    change (p E:ℤ)*h-s E = (p F:ℤ)*g-s F at bad
    rw [hr,hr] at bad
    let f (h i : ℕ) := (h:ℤ)-(i+1)
    have bound (E' : Finset ℕ) (u : ℕ) (hu : K+1≤u ∧ u<K+H+1) (i : ℕ) (hi : i<K+1) :
        0 ≤ digit K E' (f u) u i ∧ digit K E' (f u) u i ≤ M := by
      dsimp [digit,f,M]; split <;> (try split) <;> omega
    have eq := unique_digits hf _ _ (bound E h h1) (bound F g h2) (by
      rw [representation _ _ _ _ eS,representation _ _ _ _ fS]; exact bad)
    have hg : h=g := by exact_mod_cast (show (h:ℤ)=g by simpa [digit] using eq K (by omega))
    subst g
    apply hne
    refine Prod.ext ?_ rfl
    ext i
    by_cases hi : i<K
    · have hh := eq i (by omega)
      have hp : f h i ≠ 0 := by dsimp [f]; omega
      by_cases e : i∈E <;> by_cases f' : i∈F <;> simp_all [digit,hi.ne]
    · have h1' : i ∉ E := fun h => hi (mem_range.mp (eS h))
      have h2' : i ∉ F := fun h => hi (mem_range.mp (fS h))
      simp [h1',h2']



private noncomputable def primePool (P : ℝ) := Nat.primesLE ⌊P⌋₊ \ Nat.primesLE ⌊P/8⌋₊

private lemma pool_mem {P : ℝ} (hp : 0≤P) {p : ℕ} :
    p ∈ primePool P ↔ p.Prime ∧ P/8 < p ∧ (p:ℝ) ≤ P := by
  classical
  constructor
  · intro he
    obtain ⟨h1,h2⟩ := Finset.mem_sdiff.mp he
    obtain ⟨hu,hpr⟩ := Nat.mem_primesLE.mp h1
    refine ⟨hpr,lt_of_not_ge (fun hlo => h2 (Nat.mem_primesLE.mpr ⟨Nat.le_floor hlo,hpr⟩)),
      (Nat.le_floor_iff hp).mp hu⟩
  · rintro ⟨hpr,hlo,hup⟩
    exact mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hup,hpr⟩,
      fun he => hlo.not_ge ((Nat.le_floor_iff (show 0≤P/8 by positivity)).mp (Nat.mem_primesLE.mp he).1)⟩

private lemma prime_density (t : ℝ) (tbig : 300 ≤ t) :
    Real.exp t ≤ 8*((primePool (Real.exp t)).card:ℝ)*t := by
  let P := Real.exp t
  let u := Real.exp (t/2)
  have ht : 0≤t := by linarith
  have hu := Real.exp_pos (t/2)
  have hp := Real.exp_pos t
  have ppos : 0<P := hp
  have eu : P=u^2 := by dsimp [P,u]; rw [←Real.exp_nat_mul]; congr 1; push_cast; ring
  have hl := Real.pow_div_factorial_le_exp (t/2) (by positivity) 2
  norm_num at hl
  have htu : 32*t ≤ u := by
    dsimp [u]
    nlinarith [mul_le_mul_of_nonneg_right tbig ht]
  have u0 : 0≤u := hu.le
  have hP : 2 ≤ P := by nlinarith [sq_nonneg (u-1)]
  have logp : Real.log P=t := Real.log_exp _
  have elog : Real.log (P+2) ≤ t+1 := by
    calc
      _ ≤ Real.log (P*2) := Real.log_le_log (by positivity) (by linarith)
      _ = t+Real.log 2 := by rw [Real.log_mul ppos.ne' (by norm_num),logp]
      _ ≤ _ := by linarith [Real.log_two_lt_d9]
  have lo := Chebyshev.theta_ge' (x:=P) (by linarith)
  rw [logp,show Real.sqrt P=u by rw [eu,Real.sqrt_sq u0]] at lo
  have up := Chebyshev.theta_le_log4_mul_x (x:=P/8) (by positivity)
  have e4 : Real.log 4=2*Real.log 2 := by rw [show (4:ℝ)=2*2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]; ring
  rw [e4] at up
  have d : P/8 ≤ Chebyshev.theta P-Chebyshev.theta (P/8) := by
    have h0 : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have sm : t+2 ≤ P/16 := by nlinarith [sq_nonneg (u-1)]
    have xu := mul_le_mul_of_nonneg_right htu u0
    nlinarith only [lo,up,elog,eu,sm,xu,h1,mul_le_mul_of_nonneg_right h0 ppos.le,
      mul_le_mul_of_nonneg_right h1 ppos.le]
  have sub : Nat.primesLE ⌊P/8⌋₊ ⊆ Nat.primesLE ⌊P⌋₊ := by
    intro p h
    obtain ⟨hle,hpr⟩ := Nat.mem_primesLE.mp h
    exact Nat.mem_primesLE.mpr ⟨hle.trans (Nat.floor_mono (by linarith)),hpr⟩
  rw [Chebyshev.theta_eq_sum_primesLE,Chebyshev.theta_eq_sum_primesLE,←sum_sdiff_eq_sub sub] at d
  have ht' : (∑ p ∈ primePool P, Real.log p) ≤ (primePool P).card*t := by
    calc
      _ ≤ ∑ _ ∈ primePool P, t := sum_le_sum fun p hm =>
        (Real.log_le_log (by exact_mod_cast ((pool_mem ppos.le).mp hm).1.pos) ((pool_mem ppos.le).mp hm).2.2).trans_eq logp
      _ = _ := by simp
  change P ≤ _
  change P/8 ≤ ∑ p ∈ primePool P, Real.log p at d
  linarith

private lemma scales (l : ℝ) (hl : 1000000 ≤ l) :
    let t := l^3
    let P := Real.exp t
    let N := ⌊P⌋₊
    let K := ⌊2*Real.log l/Real.log 2⌋₊
    let H := ⌊l^2⌋₊
    0<K ∧ 8*((2*(K+H+1)+1:ℕ):ℝ)^(K+1) < ((N:ℝ)+1)*
       (((primePool P).card:ℝ)/(8*((N:ℝ)+1)))^(2^K) := by
  intro t P N K H
  let X := (N:ℝ)+1
  let δ := ((primePool P).card:ℝ)/(8*X)
  have lp : 0<l := by linarith
  have one : 1≤l := by linarith
  have tp : 0<t := pow_pos lp _
  have tlarge : 300≤t := (show (300:ℝ) ≤ l by linarith).trans (by
    simpa [t] using pow_le_pow_right₀ one (by decide : 1≤3))
  have log2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hlog : Real.log 2 ≤ Real.log l := Real.log_le_log (by norm_num) (by linarith)
  have hK : 1 ≤ K := by
    apply Nat.le_floor
    apply (le_div_iff₀ log2).2
    push_cast; linarith
  have floorK : (K:ℝ) ≤ 2*Real.log l/Real.log 2 := Nat.floor_le (by positivity [Real.log_nonneg one])
  have hC : (2:ℝ)^K ≤ l^2 := by
    have e := Real.exp_le_exp.mpr ((le_div_iff₀ log2).mp floorK)
    rwa [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2),
      show 2*Real.log l=Real.log l+Real.log l by ring,Real.exp_add,Real.exp_log lp,←sq] at e
  have hk : (K:ℝ) ≤ l^2 := le_trans (by exact_mod_cast K.lt_two_pow_self.le) hC
  have hh : (H:ℝ) ≤ l^2 := Nat.floor_le (sq_nonneg l)
  have hP : 1 ≤ P := Real.one_le_exp tp.le
  have hXP : P ≤ X := (Nat.lt_floor_add_one P).le
  have hx : X ≤ 2*P := by
    have hn : (N:ℝ) ≤ P := Nat.floor_le (by positivity : 0 ≤ Real.exp t)
    dsimp [X]; linarith
  have xpos : 0<X := by dsimp [X]; positivity
  have density := prime_density t tlarge
  change P ≤ 8*((primePool P).card:ℝ)*t at density
  have low : 1/(128*t) ≤ δ := by
    apply (div_le_div_iff₀ (by positivity) (by dsimp [X]; positivity)).2
    nlinarith
  have grow : 128*t ≤ Real.exp (l/4) := by
    have e := Real.pow_div_factorial_le_exp (l/4) (by positivity) 4
    norm_num at e
    have ht4 := mul_le_mul_of_nonneg_right hl (pow_nonneg lp.le 3)
    rw [div_pow] at e
    dsimp [t]; nlinarith only [e,ht4,pow_nonneg lp.le 3]
  have dlow : Real.exp (-(l/4)) ≤ δ := by
    rw [Real.exp_neg,←one_div]
    exact (one_div_le_one_div_of_le (by positivity) grow).trans low
  have powerlow : Real.exp (-(t/4)) ≤ δ^(2^K) := by
    calc
      _ ≤ Real.exp (((2^K:ℕ):ℝ)*(-(l/4))) := Real.exp_le_exp.mpr (by
        push_cast; dsimp [t]; nlinarith only [mul_le_mul_of_nonneg_right hC lp.le])
      _ = (Real.exp (-(l/4)))^(2^K) := Real.exp_nat_mul _ _
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le dlow _
  have rhs : Real.exp (3*t/4) ≤ X*δ^(2^K) := by
    rw [show 3*t/4=t+(-(t/4)) by ring,Real.exp_add]
    exact mul_le_mul hXP powerlow (Real.exp_pos _).le xpos.le
  have base : ((2*(K+H+1)+1:ℕ):ℝ) ≤ Real.exp (l/4) := by
    apply le_trans _ grow
    push_cast
    dsimp [t]
    have h3 := pow_le_pow_right₀ one (by decide : 2≤3)
    nlinarith
  have lhs : ((2*(K+H+1)+1:ℕ):ℝ)^(K+1) ≤ Real.exp (t/2) := by
    calc
      _ ≤ (Real.exp (l/4))^(K+1) := pow_le_pow_left₀ (Nat.cast_nonneg _) base _
      _ = Real.exp (((K+1:ℕ):ℝ)*(l/4)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        push_cast; dsimp [t]
        nlinarith [mul_le_mul_of_nonneg_right hk lp.le,
          show l ≤ l^3 by simpa using pow_le_pow_right₀ one (by decide : 1≤3)])
  have h8 : 8 < Real.exp (t/4) := by linarith [Real.add_one_le_exp (t/4)]
  refine ⟨hK,?_⟩
  calc
    _ ≤ 8*Real.exp (t/2) := mul_le_mul_of_nonneg_left lhs (by norm_num)
    _ < Real.exp (t/4)*Real.exp (t/2) := mul_lt_mul_of_pos_right h8 (Real.exp_pos _)
    _ = Real.exp (3*t/4) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := rhs



theorem prime_cube : ∀ᶠ l : ℝ in atTop,
    let K := ⌊2 * Real.log l / Real.log 2⌋₊
    let H := ⌊l^2⌋₊
    ∃ (p : Finset ℕ → ℕ) (s : Finset ℕ → ℤ),
    (∀ E ∈ (range K).powerset, (p E).Prime ∧ Real.exp (l^3) ≤ 8*p E ∧
      (p E:ℝ) ≤ Real.exp (l^3) ∧ |s E| ≤ 8*(K:ℤ)^2*p E ∧
      ∀ k < K, (p (symmDiff E {k}):ℤ) * ((k+1:ℕ):ℤ) - s (symmDiff E {k}) = (p E:ℤ) * ((k+1:ℕ):ℤ) - s E) ∧
    Set.InjOn p ((range K).powerset) ∧ (∏ a ∈ ((range K).powerset ×ˢ Ico (K+1) (K+H+1)).offDiag, (((p a.1.1:ℤ)*(a.1.2:ℤ)-s a.1.1)-((p a.2.1:ℤ)*(a.2.2:ℤ)-s a.2.1)).natAbs) ≠ 0 := by
  classical
  filter_upwards [eventually_ge_atTop (1000000:ℝ)] with l hl
  let P := Real.exp (l^3)
  let A := primePool P
  let N := ⌊P⌋₊
  let K := ⌊2*Real.log l/Real.log 2⌋₊
  let H := ⌊l^2⌋₊
  obtain ⟨hk,hsize⟩ := scales l hl
  have hA : A ⊆ range (N+1) := by
    intro a ha
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor ((pool_mem (Real.exp_pos _).le).mp ha).2.2))
  obtain ⟨p,s,hp,hi,hd⟩ := finite_cube N K H hk A hA hsize
  refine ⟨p,s,?_,hi,hd⟩
  intro E hE
  obtain ⟨he,hs,hf⟩ := hp E hE
  obtain ⟨hpr,hlo,hup⟩ := (pool_mem (Real.exp_pos _).le).mp he
  exact ⟨hpr,by linarith,hup,hs,hf⟩

end PrimeCube69

theorem OMA.solution : OMA.R_Erdos69_erdos_69_R1_H1_R1_H1_R1.H1 := PrimeCube69.prime_cube
