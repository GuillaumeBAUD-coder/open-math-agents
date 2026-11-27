import OMAReductions.R_Erdos69_erdos_69_R1_H1_R1_H3_R1
import Mathlib

/-! Credit: @marcusbuffett. Count one or two congruences over an interval by complete periods, then sum covariances. The zero-sum weights cancel each pair of distinct primes. -/

namespace FiniteSieve69
open Finset
open scoped Classical

private def blockPrefix (n m r : ℕ) := (range n).filter fun i => i%m=r

private lemma full_blocks (k m r : ℕ) (hm : 0 < m) (hr : r < m) :
    (blockPrefix (k*m) m r).card = k := by
  have eq : blockPrefix (k*m) m r = (range k).image (fun t => t*m+r) := by
    ext i
    simp only [blockPrefix,mem_filter,mem_range,mem_image]
    constructor
    · rintro ⟨hi,he⟩
      exact ⟨i/m,(Nat.div_lt_iff_lt_mul hm).2 hi, by
        rw [←he,Nat.mul_comm]; exact Nat.div_add_mod i m⟩
    · rintro ⟨t,ht,rfl⟩
      constructor
      · calc
          _ < t*m+m := Nat.add_lt_add_left hr _
          _ = (t+1)*m := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ ht
      · simp [Nat.add_mod,Nat.mod_eq_of_lt hr]
  rw [eq,card_image_of_injective,card_range]
  intro u v he
  exact Nat.eq_of_mul_eq_mul_right hm (Nat.add_right_cancel he)

private lemma prefix_error (n m r : ℕ) (hm : 0 < m) (hr : r < m) :
    |((blockPrefix n m r).card:ℝ)-(n:ℝ)/m| ≤ 1 := by
  have mono {a b : ℕ} (h : a ≤ b) : blockPrefix a m r ⊆ blockPrefix b m r :=
    filter_subset_filter _ (range_mono h)
  have l := card_le_card (mono (Nat.div_mul_le_self n m))
  have u := card_le_card (mono (a:=n) (b:=(n/m+1)*m) (by
    exact ((Nat.div_lt_iff_lt_mul hm).1 (Nat.lt_succ_self (n/m))).le))
  rw [full_blocks _ _ _ hm hr] at l u
  have l' : ((n/m:ℕ):ℝ) ≤ (blockPrefix n m r).card := by exact_mod_cast l
  have u' : ((blockPrefix n m r).card:ℝ) ≤ (n/m:ℕ)+1 := by exact_mod_cast u
  have dl : ((n/m:ℕ):ℝ)*(m:ℝ) ≤ n := by exact_mod_cast Nat.div_mul_le_self n m
  have du : (n:ℝ) < (((n/m:ℕ):ℝ)+1)*m := by
    exact_mod_cast ((Nat.div_lt_iff_lt_mul hm).1 (Nat.lt_succ_self (n/m)))
  have mp : (0:ℝ) < m := by exact_mod_cast hm
  have lo := (le_div_iff₀ mp).2 dl
  have up := (div_lt_iff₀ mp).2 du
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private def interval (L U m r : ℕ) := (Icc L U).filter fun i => i%m=r%m

private lemma interval_error (L U m r : ℕ) (hm : 0 < m) :
    |((interval L U m r).card:ℝ)-((U+1-L:ℕ):ℝ)/m| ≤ 2 := by
  by_cases h : L ≤ U+1
  · have hsub : blockPrefix L m (r%m) ⊆ blockPrefix (U+1) m (r%m) :=
      filter_subset_filter _ (range_mono h)
    have e : interval L U m r = blockPrefix (U+1) m (r%m) \ blockPrefix L m (r%m) := by
      ext i
      simp only [interval,blockPrefix,mem_sdiff,mem_filter,mem_Icc,mem_range]
      omega
    rw [e,card_sdiff_of_subset hsub,Nat.cast_sub (card_le_card hsub),Nat.cast_sub h,Nat.cast_add_one]
    have h1 := abs_le.mp (prefix_error (U+1) m (r%m) hm (Nat.mod_lt _ hm))
    have h2 := abs_le.mp (prefix_error L m (r%m) hm (Nat.mod_lt _ hm))
    push_cast at h1
    rw [sub_div]
    exact abs_le.mpr ⟨by linarith [h1.1,h2.2],by linarith [h1.2,h2.1]⟩
  · have h' : U<L := by omega
    simp [interval,Finset.Icc_eq_empty_of_lt h',Nat.sub_eq_zero_of_le (by omega : U+1≤L)]

private lemma class_error (L U Q b m r : ℕ) (hQ : 0<Q) (hm : 0 < m) (co : Q.Coprime m) :
    |(((interval L U Q b).filter (fun i => i%m=r%m)).card:ℝ) -
      ((interval L U Q b).card:ℝ)/m| ≤ 4 := by
  let c := Nat.chineseRemainder co b r
  have e : (interval L U Q b).filter (fun i => i%m=r%m) = interval L U (Q*m) c.val := by
    ext i
    simp only [interval,mem_filter,mem_Icc]
    change ((_ ∧ i ≡ b [MOD Q]) ∧ i ≡ r [MOD m]) ↔ _ ∧ i ≡ c.val [MOD Q*m]
    rw [← Nat.modEq_and_modEq_iff_modEq_mul co]
    constructor
    · rintro ⟨⟨a,hb⟩,hr⟩
      exact ⟨a,hb.trans c.prop.1.symm,hr.trans c.prop.2.symm⟩
    · rintro ⟨a,hb,hr⟩
      exact ⟨⟨a,hb.trans c.prop.1⟩,hr.trans c.prop.2⟩
  rw [e]
  have h1 := interval_error L U (Q*m) c.val (Nat.mul_pos hQ hm)
  have h2 := interval_error L U Q b hQ
  have m1 : 1≤(m:ℝ) := by exact_mod_cast hm
  have h2' : |(((interval L U Q b).card:ℝ)-((U+1-L:ℕ):ℝ)/Q)/m| ≤ 2 := by
    rw [abs_div,abs_of_pos (by positivity : (0:ℝ) < m)]
    exact (div_le_iff₀ (by positivity)).2 (by linarith)
  rw [sub_div,div_div] at h2'
  rw [Nat.cast_mul] at h1
  obtain ⟨h1l,h1u⟩ := abs_le.mp h1
  obtain ⟨h2l,h2u⟩ := abs_le.mp h2'
  exact abs_le.mpr ⟨by linarith,by linarith⟩


private def residue (q : ℕ) (z : ℤ) := ((-z : ℤ) : ZMod q).val

private lemma residue_iff {q n : ℕ} (hq : q ≠ 0) (z : ℤ) :
    (q:ℤ) ∣ (n:ℤ)+z ↔ n ≡ residue q z [MOD q] := by
  letI : NeZero q := ⟨hq⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,← ZMod.natCast_eq_natCast_iff]
  simp [residue,ZMod.natCast_zmod_val,eq_neg_iff_add_eq_zero]

private lemma pair_error (L U Q b : ℕ) (hQ : 0<Q) (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpQ : ¬p ∣ Q) (hqQ : ¬q ∣ Q)
    (u v : ℤ) (distinct : p=q → u≠v → ¬(p:ℤ) ∣ u-v) :
    let N := interval L U Q b
    let S := N.filter fun (n : ℕ) => (p:ℤ) ∣ (n:ℤ)+u ∧ (q:ℤ) ∣ (n:ℤ)+v
    |(S.card:ℝ)-N.card*(if p=q then (if u=v then 1/(p:ℝ) else 0)
       else 1/((p:ℝ)*q))| ≤ 4 := by
  intro N S
  by_cases e : p=q
  · subst q
    rw [if_pos rfl]
    by_cases f : u=v
    · subst v
      rw [if_pos rfl]
      have he : S = N.filter (fun n => n%p=(residue p u)%p) := by
        ext n
        simp only [S,mem_filter,and_self,residue_iff hp.ne_zero]
        rfl
      rw [he,mul_one_div]
      exact class_error L U Q b p (residue p u) hQ hp.pos (hp.coprime_iff_not_dvd.mpr hpQ).symm
    · have he : S = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro n hn
        obtain ⟨hu,hv⟩ := (mem_filter.mp hn).2
        have d := Int.dvd_sub hu hv
        rw [show (n:ℤ)+u-((n:ℤ)+v)=u-v by ring] at d
        exact distinct rfl f d
      simp [he,f]
  · rw [if_neg e]
    have co := (Nat.coprime_primes hp hq).mpr e
    let c := Nat.chineseRemainder co (residue p u) (residue q v)
    have he : S = N.filter (fun n => n%(p*q)=c.val%(p*q)) := by
      ext n
      simp only [S,mem_filter,residue_iff hp.ne_zero,residue_iff hq.ne_zero]
      change _ ∧ _ ↔ _ ∧ n ≡ c.val [MOD p*q]
      rw [← Nat.modEq_and_modEq_iff_modEq_mul co]
      exact and_congr_right fun _ => ⟨fun h => ⟨h.1.trans c.prop.1.symm,h.2.trans c.prop.2.symm⟩,
        fun h => ⟨h.1.trans c.prop.1,h.2.trans c.prop.2⟩⟩
    rw [he,mul_one_div]
    have H := class_error L U Q b (p*q) c.val hQ (Nat.mul_pos hp.pos hq.pos)
      ((hp.coprime_iff_not_dvd.mpr hpQ).symm.mul_right (hq.coprime_iff_not_dvd.mpr hqQ).symm)
    simpa using H



private lemma moments {α : Type} [DecidableEq α] (A : Finset α) (N : Finset ℕ)
    (c : α → ℝ) (g : α → ℕ → Prop) [∀ a,DecidablePred (g a)] :
    ∑ n ∈ N, (∑ a ∈ A, if g a n then c a else 0)^2 =
      ∑ a ∈ A, ∑ b ∈ A, (c a*c b) * ((N.filter fun n => g a n ∧ g b n).card:ℝ) := by
  classical
  calc
    _ = ∑ n ∈ N, ∑ a ∈ A, ∑ b ∈ A,
          (if g a n then c a else 0)*(if g b n then c b else 0) := by
      simp only [pow_two,sum_mul,mul_sum]
      simp only [mul_comm]
    _ = ∑ a ∈ A, ∑ b ∈ A, ∑ n ∈ N,
          (if g a n then c a else 0)*(if g b n then c b else 0) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      calc
        _ = ∑ n ∈ N, if g a n ∧ g b n then c a*c b else 0 := by
          apply sum_congr rfl
          intro n _
          by_cases ha : g a n <;> by_cases hb : g b n <;> simp [ha,hb]
        _ = _ := by rw [← sum_filter]; simp [mul_comm]

private noncomputable def mean {α : Type} [DecidableEq α] (a b : ℕ × α) : ℝ :=
  if a.1=b.1 then (if a.2=b.2 then 1/(a.1:ℝ) else 0) else 1/((a.1:ℝ)*b.1)

private lemma mean_sum {α : Type} [DecidableEq α] (S : Finset α) (P : Finset ℕ) (w : α → ℝ)
    (hz : ∑ i ∈ S, w i = 0) :
    ∑ a ∈ P ×ˢ S, ∑ b ∈ P ×ˢ S, w a.2*w b.2 * mean a b =
       (∑ i ∈ S, (w i)^2)*(∑ p ∈ P, (1:ℝ)/p) := by
  classical
  simp only [sum_product]
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [sum_comm]
  rw [sum_eq_single p]
  · apply Eq.trans _ (sum_mul ..).symm
    apply sum_congr rfl
    intro i hi
    rw [sum_eq_single i]
    · simp [mean,pow_two]
    · intro j hj hji
      simp [mean,Ne.symm hji]
    · exact fun h => (h hi).elim
  · intro q hq hqp
    apply sum_eq_zero
    intro i hi
    simp only [mean,if_neg hqp.symm]
    calc
      _ = (w i*(1/((p:ℝ)*q)))*∑ j ∈ S, w j := by rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ = 0 := by rw [hz,mul_zero]
  · exact fun h => (h hp).elim

theorem variance (L U Q b : ℕ) (S : Finset (Finset ℕ × ℕ)) (P : Finset ℕ)
    (r : Finset ℕ × ℕ → ℤ) (w : Finset ℕ × ℕ → ℝ)
    (hQ : 0<Q) (hP : ∀ p ∈ P, p.Prime ∧ ¬p ∣ Q)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ p ∈ P, ¬(p:ℤ) ∣ r i-r j)
    (hz : ∑ i ∈ S, w i = 0) :
    let N := (Icc L U).filter (fun n => n%Q=b%Q)
    ∑ n ∈ N, (∑ i ∈ S, w i * ((P.filter fun (p:ℕ) => (p:ℤ) ∣ (n:ℤ)+r i).card:ℝ))^2 ≤
      (N.card:ℝ)*(∑ i ∈ S, (w i)^2)*(∑ p ∈ P, (1:ℝ)/p) +
      4*((P.card:ℝ)*(∑ i ∈ S, |w i|))^2 := by
  classical
  intro N
  let A := P ×ˢ S
  let g (a : ℕ × (Finset ℕ × ℕ)) (n : ℕ) := (a.1:ℤ) ∣ (n:ℤ)+r a.2
  let c (a : ℕ × (Finset ℕ × ℕ)) := w a.2
  have e (n : ℕ) :
      ∑ i ∈ S, w i * ((P.filter fun (p:ℕ) => (p:ℤ) ∣ (n:ℤ)+r i).card:ℝ) =
        ∑ a ∈ A, if g a n then c a else 0 := by
    rw [show A = P ×ˢ S by rfl,sum_product,sum_comm]
    apply sum_congr rfl
    intro i _
    dsimp only [g,c]
    rw [←sum_filter]
    simp [mul_comm]
  let cnt (a b : ℕ × (Finset ℕ × ℕ)) : ℝ := (N.filter fun n => g a n ∧ g b n).card
  have point (a) (ha : a ∈ A) (v) (hv : v ∈ A) :
      (c a*c v)*cnt a v ≤ (N.card:ℝ)*(c a*c v*mean a v)+4*(|c a| * |c v|) := by
    obtain ⟨pa,si⟩ := mem_product.mp ha
    obtain ⟨pv,sj⟩ := mem_product.mp hv
    have hne : r a.2 = r v.2 ↔ a.2 = v.2 := by
      constructor
      · intro he
        by_contra ij
        exact hd a.2 si v.2 sj ij a.1 pa (by rw [he,sub_self]; exact dvd_zero _)
      · exact congrArg r
    have hh := pair_error L U Q b hQ a.1 v.1 (hP _ pa).1 (hP _ pv).1 (hP _ pa).2 (hP _ pv).2
      (r a.2) (r v.2) (fun _ hne' => hd a.2 si v.2 sj (fun h => hne' (congrArg r h)) a.1 pa)
    have h' : |cnt a v-N.card*mean a v| ≤ 4 := by
      simpa [cnt,g,N,interval,mean,hne] using hh
    have hle := (le_abs_self ((c a*c v)*(cnt a v-N.card*mean a v))).trans
      ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_left h' (abs_nonneg _)))
    rw [abs_mul] at hle
    linarith only [hle]
  calc
    _ = ∑ a ∈ A, ∑ v ∈ A, (c a*c v)*cnt a v := by
      simp_rw [e]
      exact moments A N c g
    _ ≤ ∑ a ∈ A, ∑ v ∈ A, ((N.card:ℝ)*(c a*c v*mean a v)+4*(|c a| * |c v|)) :=
      sum_le_sum fun a ha => sum_le_sum (point a ha)
    _ = (N.card:ℝ)*(∑ a ∈ A, ∑ v ∈ A, c a*c v*mean a v)+
        4*(∑ a ∈ A, |c a|)^2 := by
      simp only [sum_add_distrib,←mul_sum,pow_two,sum_mul]
    _ = _ := by
      rw [show (∑ a ∈ A, ∑ v ∈ A, c a*c v*mean a v) = _ from mean_sum S P w hz]
      simp [A,c,sum_product,mul_assoc]


end FiniteSieve69

theorem OMA.solution : OMA.R_Erdos69_erdos_69_R1_H1_R1_H3_R1.H1 := FiniteSieve69.variance
