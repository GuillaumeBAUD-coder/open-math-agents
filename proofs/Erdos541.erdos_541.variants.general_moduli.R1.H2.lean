import OMAReductions.R_Erdos541_erdos_541_variants_general_moduli_R1

/-!
The central case of the Graham conjecture follows the dichotomy of
Gao, Hamidoune and Wang (arXiv:0902.4758). A Scherk–Kemperman bound
on the transversal sums produces an element occurring at least r times.
For a nongenerator, all remaining terms have odd representatives.
For a generator, normalize it to 1 and analyze the integer subset sums
of the remaining terms in the interval from their number to 2r.
-/
namespace SC541Central
open Finset
open scoped Pointwise Classical

/-- The unique-representation case of the Scherk–Kemperman inequality. -/
lemma scherk {G : Type*} [AddCommGroup G] [DecidableEq G] (A B : Finset G)
    (hA : 0∈A) (hB : 0∈B) (hu : ∀ a∈A, ∀ b∈B, a+b=0 → b=0) :
    A.card+B.card ≤ (A+B).card+1 := by
  generalize hk : B.card=k
  induction k using Nat.strong_induction_on generalizing A B with
  | h k ih =>
    by_cases ex : ∃ e∈A, ∃ b∈B, e+b∉A
    · obtain ⟨e,he,b,hb,heb⟩ := ex
      let E := B.filter fun y => e+y∈A
      let shift := B.image (e+·)
      let D := A∪shift
      have hE : 0∈E := mem_filter.mpr ⟨hB,by simpa⟩
      have hD : 0∈D := mem_union_left _ hA
      have hEs : E⊆B := filter_subset .. 
      have hlt : E.card<k := by
        rw [←hk]
        apply card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hEs,?_⟩)
        intro eq
        have hx : b∈E := eq ▸ hb
        exact heb (mem_filter.mp hx).2
      have us : ∀ x∈D, ∀ y∈E, x+y=0 → y=0 := by
        intro x hx y hy hz
        obtain ⟨hyB,hyA⟩ := mem_filter.mp hy
        rcases mem_union.mp hx with hx|hx
        · exact hu x hx y hyB hz
        · obtain ⟨t,ht,rfl⟩ := mem_image.mp hx
          have heq : (e+y)+t=0 := by simpa [add_assoc,add_comm,add_left_comm] using hz
          have ht0 := hu _ hyA _ ht heq
          rw [ht0,add_zero] at heq
          exact hu _ he _ hyB heq
      have sub : D+E⊆A+B := by
        intro z hz
        obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hz
        obtain ⟨hyB,hyA⟩ := mem_filter.mp hy
        rcases mem_union.mp hx with hx|hx
        · exact add_mem_add hx hyB
        · obtain ⟨t,ht,rfl⟩ := mem_image.mp hx
          simpa only [add_assoc,add_left_comm,add_comm] using add_mem_add hyA ht
      have inter : A∩shift = E.image (e+·) := by
        ext z
        simp only [mem_inter,shift,E,mem_image,mem_filter]
        constructor
        · rintro ⟨hz,t,ht,rfl⟩; exact ⟨t,⟨ht,hz⟩,rfl⟩
        · rintro ⟨t,⟨ht,h⟩,rfl⟩; exact ⟨h,t,ht,rfl⟩
      have hcard := card_union_add_card_inter A shift
      rw [inter,card_image_of_injective _ (add_right_injective e)] at hcard
      change D.card+E.card=A.card+shift.card at hcard
      rw [show shift.card=B.card from card_image_of_injective _ (add_right_injective e)] at hcard
      have H := ih _ hlt D E hD hE us rfl
      have H' := card_le_card sub
      omega
    · push Not at ex
      have hb : B ⊆ {0} := by
        intro b hb
        let T := A.image (·+b)
        have hsub : T ⊆ A := by
          intro y hy
          obtain ⟨a,ha,rfl⟩ := mem_image.mp hy
          exact ex a ha b hb
        have hEq : T=A := eq_of_subset_of_card_le hsub (by
          dsimp [T]; rw [card_image_of_injective _ (add_left_injective b)])
        have hz : 0∈T := hEq ▸ hA
        obtain ⟨a,ha,he⟩ := mem_image.mp hz
        simpa using hu a ha b hb he
      have eq := Subset.antisymm hb (singleton_subset_iff.mpr hB)
      subst B
      simp at hk ⊢
      omega

end SC541Central

namespace SC541Central
open Finset
open scoped Pointwise Classical

variable {n r : ℕ}
private def freq (a : Fin n → ZMod n) (t : ZMod n) := univ.filter fun i => a i=t
private def prev (a : Fin n → ZMod n) (i : Fin n) := univ.filter fun j => j < i ∧ a j=a i
private def rank (a : Fin n → ZMod n) (i : Fin n) := (prev a i).card
private def layer (a : Fin n → ZMod n) (k : ℕ) := univ.filter fun i => rank a i=k
private def colors (a : Fin n → ZMod n) (k : ℕ) := insert 0 ((layer a k).image a)
private def reach (a : Fin n → ZMod n) : ℕ → Finset (ZMod n)
  | 0 => {0}
  | k+1 => reach a k + colors a k

private lemma rank_lt (a : Fin n → ZMod n) (i : Fin n) : rank a i < (freq a (a i)).card := by
  apply card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr ⟨fun j hj => by
    simpa [freq] using (mem_filter.mp hj).2.2,?_⟩
  intro he
  have h : i∈prev a i := he ▸ (by simp [freq] : i∈freq a (a i))
  simpa [prev] using h

private lemma rank_strict (a : Fin n → ZMod n) {i j : Fin n} (h : i<j) (he : a i=a j) : rank a i<rank a j := by
  apply card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr ⟨fun k hk => by
    obtain ⟨_,hk,he'⟩ := mem_filter.mp hk
    exact mem_filter.mpr ⟨mem_univ _,hk.trans h,he'.trans he⟩,?_⟩
  intro eq
  have hj : i∈prev a j := mem_filter.mpr ⟨mem_univ _,h,he⟩
  rw [←eq] at hj
  simpa [prev] using hj

private lemma layer_inj (a : Fin n → ZMod n) (k : ℕ) : Set.InjOn a (layer a k : Set (Fin n)) := by
  intro i hi j hj he
  have h1 := (mem_filter.mp hi).2
  have h2 := (mem_filter.mp hj).2
  rcases lt_trichotomy i j with h|h|h
  · have := rank_strict a h he; omega
  · exact h
  · have := rank_strict a h he.symm; omega

private lemma rep (a : Fin n → ZMod n) (k : ℕ) {z : ZMod n} (hz : z∈reach a k) :
    ∃ W : Finset (Fin n), (∀ i∈W,rank a i<k) ∧ W.card≤k ∧ ∑ i∈W,a i=z := by
  induction k generalizing z with
  | zero =>
    simp only [reach,mem_singleton] at hz
    exact ⟨∅,by simp,by simp,by simp [hz]⟩
  | succ k ih =>
    obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hz
    obtain ⟨W,hW,hcard,rfl⟩ := ih hx
    rcases mem_insert.mp hy with rfl|hy
    · exact ⟨W,fun i hi => (hW i hi).trans (Nat.lt_succ_self _),by omega,by simp⟩
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
      have hri := (mem_filter.mp hi).2
      have hni : i∉W := fun h => by have := hW i h; omega
      exact ⟨insert i W,fun j hj => by
        rcases mem_insert.mp hj with rfl|hj
        · omega
        · have := hW j hj; omega,
        by rw [card_insert_of_notMem hni]; omega,by rw [sum_insert hni,add_comm]⟩

private lemma zero_reach (a : Fin n → ZMod n) (k : ℕ) : 0∈reach a k := by
  induction k with
  | zero => simp [reach]
  | succ k ih => simpa [reach,colors] using add_mem_add ih (mem_insert_self 0 ((layer a k).image a))

theorem heavy {a : Fin n → ZMod n} (hn : 0<n) (hr : 1<r)
    (hZ : ∀ S : Finset (Fin n), S≠∅ → ∑ i∈S,a i=0 → S.card=r) :
    ∃ t, r ≤ (univ.filter fun i => a i=t).card := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  by_contra! hall
  have hsmall (i : Fin n) : rank a i < r-1 := by
    have := hall (a i)
    change (freq a (a i)).card < r at this
    have := rank_lt a i
    omega
  have hnz (i : Fin n) : a i≠0 := by
    intro h
    have hh := hZ {i} (by simp) (by simp [h])
    simp at hh
    omega
  have hmass (k : ℕ) (hk : k<r) : 1 + ∑ j∈range k,(layer a j).card ≤ (reach a k).card := by
    induction k with
    | zero => simp [reach]
    | succ k ih =>
      have hh := ih (by omega)
      have hc : (colors a k).card=(layer a k).card+1 := by
        rw [colors,card_insert_of_notMem,card_image_of_injOn (layer_inj a k)]
        intro h
        obtain ⟨i,_,he⟩ := mem_image.mp h
        exact hnz i he
      have hs := scherk (reach a k) (colors a k) (zero_reach ..) (mem_insert_self ..) (by
        intro x hx y hy he
        rcases mem_insert.mp hy with h|h
        · exact h
        · obtain ⟨i,hi,rfl⟩ := mem_image.mp h
          obtain ⟨W,hW,hc,rfl⟩ := rep a k hx
          have hri := (mem_filter.mp hi).2
          have hni : i∉W := fun h => by have := hW i h; omega
          have eq := hZ (insert i W) (insert_ne_empty i W) (by rw [sum_insert hni,add_comm]; exact he)
          rw [card_insert_of_notMem hni] at eq
          omega)
      rw [hc] at hs
      rw [sum_range_succ,reach]
      omega
  have he : ∑ j∈range (r-1),(layer a j).card = n := by
    unfold layer
    rw [sum_card_fiberwise_eq_card_filter,filter_eq_self.mpr (by simpa using hsmall),card_univ,Fintype.card_fin]
  have h := hmass (r-1) (by omega)
  rw [he] at h
  have H := card_le_univ (reach a (r-1))
  rw [ZMod.card] at H
  omega

end SC541Central

namespace SC541Central
open Finset

theorem interval_gap {ι : Type*} [DecidableEq ι] (F : Finset ι) (b : ι → ℕ) {r : ℕ}
    (hr : F.card ≤ r) (hb : ∀ i ∈ F, 2 ≤ b i ∧ b i < 2*r)
    (gap : ∀ W ⊆ F, F.card ≤ ∑ i ∈ W,b i → ∑ i ∈ W,b i ≤ 2*r →
      ∑ i ∈ W,b i = r+W.card) : ∀ i∈F, ∀ j∈F, b i=b j := by
  classical
  let t := F.card
  have one {i : ι} (hi : i∈F) (h : t ≤ b i) : b i=r+1 := by
    simpa using gap {i} (singleton_subset_iff.mpr hi) (by simpa using h) (by simpa using (hb i hi).2.le)
  have two {i j : ι} (hi : i∈F) (hj : j∈F) (hij : i≠j) (h : t ≤ b i+b j) (hl : b i+b j≤2*r) :
      b i+b j=r+2 := by
    simpa [hij] using gap {i,j} (insert_subset hi (singleton_subset_iff.mpr hj)) (by simpa [hij] using h) (by simpa [hij] using hl)
  by_cases big : ∃ i∈F,t ≤ b i
  · obtain ⟨i,hi,hh⟩ := big
    have e := one hi hh
    have each (j : ι) (hj : j∈F) : b j=r+1 := by
      by_cases h : t ≤ b j
      · exact one hj h
      · have hn : i≠j := fun eq => h (eq ▸ hh)
        have htr : t≤r := hr
        have hh' := two hi hj hn (by omega) (by omega)
        have := (hb j hj).1
        omega
    exact fun k hk l hl => (each k hk).trans (each l hl).symm
  · push Not at big
    by_cases hne : F.Nonempty
    swap
    · simpa [Finset.not_nonempty_iff_eq_empty.mp hne]
    have twoT : 2*t ≤ ∑ i∈F,b i := by
      simpa [t,mul_comm] using card_nsmul_le_sum F b 2 (fun i hi => (hb i hi).1)
    have tpos : 0<t := card_pos.mpr hne
    let D := F.powerset.filter fun W => t ≤ ∑ i ∈W,b i
    have hin : F∈D := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl,by omega⟩
    obtain ⟨W,hw,hmin⟩ := exists_min_image D Finset.card ⟨F,hin⟩
    obtain ⟨hs,hlo⟩ := mem_filter.mp hw
    have hWF := mem_powerset.mp hs
    have hWne : W.Nonempty := by by_contra! h; simp [h] at hlo; omega
    obtain ⟨a,ha⟩ := hWne
    have hsum := add_sum_erase W b ha
    have hlt : (∑ i∈W.erase a,b i)<t := by
      by_contra! h
      have hD : W.erase a ∈ D := mem_filter.mpr ⟨mem_powerset.mpr ((erase_subset ..).trans hWF),h⟩
      have hmin' := hmin _ hD
      rw [card_erase_of_mem ha] at hmin'
      have := card_pos.mpr (show W.Nonempty from ⟨_,ha⟩)
      omega
    have hclose : (∑ i∈W,b i)<2*t := by have := big a (hWF ha); omega
    have hnWF : ¬ F⊆W := by
      intro h
      have e := Subset.antisymm h hWF
      rw [←e] at hclose
      omega
    obtain ⟨c,hc,hc'⟩ := Finset.not_subset.mp hnWF
    have htr : t≤r := hr
    have cross {V : Finset ι} (hV : V⊆F) (hlo : t≤∑ i∈V,b i) (hhi : (∑ i∈V,b i)≤2*r)
        {i j : ι} (hi : i∈V) (hj : j∈F) (hj' : j∉V) : b i+b j=r+2 := by
      have H := gap V hV hlo hhi
      have hrem := add_sum_erase V b hi
      have hrem' : (∑ u∈V.erase i,b u)<t := by
        by_contra! h
        have h' := gap (V.erase i) ((erase_subset ..).trans hV) h (by omega)
        rw [card_erase_of_mem hi] at h'
        have := (hb i (hV hi)).1
        omega
      have hadd : 2*r < b j + ∑ u∈V,b u := by
        by_contra! h
        have h' := gap (insert j V) (insert_subset hj hV) (by rw [sum_insert hj']; omega) (by rwa [sum_insert hj'])
        rw [sum_insert hj',card_insert_of_notMem hj'] at h'
        have := (hb j hj).1
        omega
      exact two (hV hi) hj (fun e => hj' (e ▸ hi)) (by omega)
        (by have := big i (hV hi); have := big j hj; omega)
    have cw {i j} (hi : i∈W) (hj : j∈F) (hj' : j∉W) :=
      cross hWF hlo (by omega) hi hj hj'
    have hac : a≠c := fun e => hc' (e ▸ ha)
    have eqac := cw ha hc hc'
    have hsub : {a,c} ⊆ F := insert_subset (hWF ha) (singleton_subset_iff.mpr hc)
    have no : ¬ F ⊆ {a,c} := by
      intro incl
      have siz := card_le_card incl
      simp [hac] at siz
      have hba := (hb a (hWF ha)).1
      have hl := big a (hWF ha)
      change t≤2 at siz
      omega
    obtain ⟨k,hk,hk'⟩ := Finset.not_subset.mp no
    have low : t≤∑ u∈({a,c}:Finset ι),b u := by simp [hac]; omega
    have high : (∑ u∈({a,c}:Finset ι),b u)≤2*r := by
      simp [hac]; have := big a (hWF ha); have := big c hc; omega
    have e1 := cross hsub low high (mem_insert_self ..) hk hk'
    have e2 := cross hsub low high (mem_insert_of_mem (mem_singleton_self c)) hk hk'
    have eac : b a=b c := by omega
    have each (i : ι) (hi : i∈F) : b i=b a := by
      by_cases hi' : i∈W
      · have := cw hi' hc hc'; omega
      · have := cw ha hi hi'; omega
    exact fun i hi j hj => (each i hi).trans (each j hj).symm

end SC541Central

namespace SC541Central
open Finset
open scoped Classical
variable {n r : ℕ}
def same (a : Fin n → ZMod n) (c : ZMod n) := univ.filter fun i => a i=c
def Uni (a : Fin n → ZMod n) (r : ℕ) := ∀ S : Finset (Fin n), S≠∅ → ∑ i∈S,a i=0 → S.card=r

lemma fill {a : Fin n → ZMod n} (hZ : Uni a r) {c : ZMod n} {W : Finset (Fin n)} (m : ℕ)
    (hw : W ⊆ (same a c)ᶜ) (hm : m ≤ (same a c).card) (hne : 0 < m ∨ W.Nonempty)
    (hs : (m:ZMod n)*c+∑ i∈W,a i=0) : m+W.card=r := by
  obtain ⟨P,hP,hc⟩ := exists_subset_card_eq hm
  have hd : Disjoint P W := disjoint_left.mpr (fun i hi h => (mem_compl.mp (hw h)) (hP hi))
  have he : ∑ i∈P,a i = (m:ZMod n)*c := by
    rw [sum_congr rfl (fun i hi => (mem_filter.mp (hP hi)).2),sum_const,nsmul_eq_mul,hc]
  have hpw : P∪W≠∅ := by
    rw [← nonempty_iff_ne_empty]
    rcases hne with h|h
    · exact (card_pos.mp (hc ▸ h)).mono (subset_union_left ..)
    · exact h.mono (subset_union_right ..)
  have h := hZ (P∪W) hpw (by rwa [sum_union hd,he])
  rwa [card_union_of_disjoint hd,hc] at h

lemma card_two {a : Fin n → ZMod n} {c : ZMod n}
    (h : ∀ i∈(same a c)ᶜ,∀ j∈(same a c)ᶜ,a i=a j) : (Set.range a).ncard ≤ 2 := by
  classical
  let F := (same a c)ᶜ
  by_cases hn : F.Nonempty
  · obtain ⟨j,hj⟩ := hn
    have hs : Set.range a ⊆ {c,a j} := by
      rintro _ ⟨i,rfl⟩
      by_cases hi : a i=c
      · simp [hi]
      · exact Set.mem_insert_of_mem _ (h i (by simp [same,hi]) j hj)
    exact (Set.ncard_le_ncard hs (Set.toFinite _)).trans (by simpa using Set.ncard_insert_le c ({a j}:Set (ZMod n)))
  · have zero : F=∅ := not_nonempty_iff_eq_empty.mp hn
    have hs : Set.range a ⊆ {c} := by
      rintro _ ⟨i,rfl⟩
      by_contra h'
      have hi : i∈F := by simpa [F,same] using h'
      simp [zero] at hi
    exact (Set.ncard_le_ncard hs (Set.finite_singleton _)).trans (by simp)

lemma nonunit {a : Fin n → ZMod n} [NeZero n] (hZ : Uni a r) (hN : 2*r=n)
    (hr : 1<r) (c : ZMod n) (hv : r≤(same a c).card) (hnu : ¬ IsUnit c) :
    (Set.range a).ncard ≤ 2 := by
  have hn : 0<n := Nat.pos_of_ne_zero (NeZero.ne n)
  have ho := ZMod.addOrderOf_coe c.val hn.ne'
  rw [ZMod.natCast_zmod_val] at ho
  have hg : 2≤n.gcd c.val := by
    have hh := Nat.gcd_pos_of_pos_left c.val hn
    by_contra! hl
    have hc : c.val.Coprime n := (show n.Coprime c.val from by change n.gcd c.val=1; omega).symm
    exact hnu (by simpa using (ZMod.isUnit_iff_coprime ..).mpr hc)
  have hle : addOrderOf c≤r := by
    have h : n/n.gcd c.val ≤ n/2 := Nat.div_le_div_left hg (by decide)
    omega
  have h0 := addOrderOf_nsmul_eq_zero c
  rw [nsmul_eq_mul] at h0
  have hh := fill hZ (c:=c) (W:=∅) (addOrderOf c) (empty_subset _) (hle.trans hv) (Or.inl (addOrderOf_pos c)) (by simpa using h0)
  simp only [card_empty,add_zero] at hh
  have hgd : n.gcd c.val=2 := by
    have he := Nat.div_mul_cancel (Nat.gcd_dvd_left n c.val)
    rw [←ho,hh] at he
    nlinarith
  have hrc : (r:ZMod n)*c=0 := hh ▸ h0
  let F := (same a c)ᶜ
  have avoid {i : Fin n} (hi : i∈F) : a i≠c := by simpa [F,same] using hi
  have relates (W : Finset (Fin n)) (hw : W⊆F) (hne : W.Nonempty)
      (k : ℕ) (hk : k<r) (he : ∑ i∈W,a i=(k:ZMod n)*c) : k=W.card := by
    have hsum : ((r-k:ℕ):ZMod n)*c+∑ i∈W,a i=0 := by rw [Nat.cast_sub hk.le,he,sub_mul,sub_add_cancel,hrc]
    have h := fill hZ (r-k) hw (by omega) (Or.inr hne) hsum
    omega
  have repr (z : ZMod n) (hz : Even z.val) : ∃ k<r, (k:ZMod n)*c=z := by
    obtain ⟨s,hs⟩ := hz
    let v := (s:ZMod n)*c⁻¹
    have he : v*c=z := by
      have H := ZMod.mul_inv_eq_gcd c
      rw [Nat.gcd_comm,hgd] at H
      calc v*c = (s:ZMod n)*(c*c⁻¹) := by dsimp [v]; ring
           _ = z := by rw [H,←ZMod.natCast_zmod_val z,hs,Nat.cast_add]; push_cast; ring
    refine ⟨v.val%r,Nat.mod_lt _ (by omega),?_⟩
    have id := Nat.mod_add_div v.val r
    have e := congrArg (fun l : ℕ => (l:ZMod n)*c) id
    push_cast at e
    rw [ZMod.natCast_zmod_val,add_mul,mul_right_comm (r:ZMod n),hrc,zero_mul,add_zero] at e
    exact e.trans he
  have odd {i : Fin n} (hi : i∈F) : Odd (a i).val := by
    apply Nat.not_even_iff_odd.mp
    intro hev
    obtain ⟨k,hk,he⟩ := repr _ hev
    have h := relates {i} (singleton_subset_iff.mpr hi) (singleton_nonempty _) k hk (by simpa using he.symm)
    simp only [card_singleton] at h
    exact avoid hi (by simpa [h] using he.symm)
  have pair {i j : Fin n} (hi : i∈F) (hj : j∈F) (hne : i≠j) : a i+a j=(2:ZMod n)*c := by
    have hev : Even (a i+a j).val := by
      rw [ZMod.val_add]
      have hn2 : 2∣n := ⟨r,hN.symm⟩
      exact Nat.even_iff.mpr (by rw [Nat.mod_mod_of_dvd _ hn2]; have h := (odd hi).add_odd (odd hj); exact Nat.even_iff.mp h)
    obtain ⟨k,hk,he⟩ := repr _ hev
    have hk' := relates {i,j} (insert_subset hi (singleton_subset_iff.mpr hj)) (insert_nonempty ..) k hk (by simpa [hne] using he.symm)
    have h2k : k=2 := by simpa [hne] using hk'
    simpa [h2k] using he.symm
  apply card_two (c:=c)
  intro i hi j hj
  by_cases hij : i=j
  · rw [hij]
  by_cases hsub : F ⊆ {i,j}
  · have hF : F={i,j} := Subset.antisymm hsub (insert_subset hi (singleton_subset_iff.mpr hj))
    have hsize := card_compl_add_card (same a c)
    change F.card+(same a c).card = _ at hsize
    simp only [Fintype.card_fin,hF,card_insert_of_notMem (by simpa using hij : i∉({j}:Finset (Fin n))),card_singleton] at hsize
    have hNc : (n:ZMod n)*c=0 := by simp
    have h2 : 2≤n := by omega
    have hsum : ((n-2:ℕ):ZMod n)*c+∑ l∈({i,j}:Finset (Fin n)),a l=0 := by
      rw [Nat.cast_sub h2]
      simp [hij,pair hi hj hij]
    have h := fill hZ (c:=c) (W:={i,j}) (n-2) (insert_subset hi (singleton_subset_iff.mpr hj)) (by omega) (Or.inr (insert_nonempty ..)) hsum
    simp [hij] at h; omega
  · obtain ⟨k,hk,hk'⟩ := Finset.not_subset.mp hsub
    simp only [mem_insert,mem_singleton,not_or] at hk'
    exact add_right_cancel ((pair hi hk (Ne.symm hk'.1)).trans (pair hj hk (Ne.symm hk'.2)).symm)

end SC541Central


namespace SC541Central
open Finset
theorem main : OMA.R_Erdos541_erdos_541_variants_general_moduli_R1.H2 := by
  classical
  intro n a r hZ hN
  by_cases hn : n≤2
  · calc (Set.range a).ncard = (univ.image a).card := by rw [← Set.ncard_coe_finset]; simp
         _ ≤ (univ : Finset (Fin n)).card := card_image_le
         _ ≤ 2 := by simpa using hn
  have hr : 1<r := by omega
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨c,hc⟩ := heavy (by omega) hr hZ
  change r≤(same a c).card at hc
  by_cases hu : IsUnit c
  swap
  · exact nonunit hZ hN hr c hc hu
  obtain ⟨u,rfl⟩ := hu
  let b (i : Fin n) : ZMod n := ↑u⁻¹ * a i
  have hU : IsUnit (↑u⁻¹ : ZMod n) := u⁻¹.isUnit
  have he (i : Fin n) : b i=1 ↔ a i=↑u := by
    change ↑u⁻¹ * a i = 1 ↔ _
    simpa only [Units.inv_mul] using (hU.mul_right_inj (b:=a i) (c:=(u:ZMod n)))
  have hsame : same b 1=same a ↑u := by ext i; simp [same,he]
  have hB : Uni b r := by
    intro S hn h
    change ∑ i∈S, (↑u⁻¹:ZMod n)*a i=0 at h
    rw [←mul_sum] at h
    exact hZ S hn (hU.mul_right_eq_zero.mp h)
  let F := (same b 1)ᶜ
  have hsize : F.card + (same b 1).card=n := by simpa [F] using card_compl_add_card (same b 1)
  have hF : F.card≤r := by rw [←hsame] at hc; omega
  have hb (i : Fin n) (hi : i∈F) : 2≤(b i).val ∧ (b i).val<2*r := by
    have h1 : b i≠1 := by simpa [F,same] using hi
    have h0 : b i≠0 := by
      intro eq
      have h := hB {i} (by simp) (by simp [eq])
      simp at h
      omega
    have hpos := ZMod.val_pos.mpr h0
    have hne : (b i).val≠1 := by
      intro eq
      have h := ZMod.natCast_zmod_val (b i)
      rw [eq,Nat.cast_one] at h
      exact h1 h.symm
    exact ⟨by omega,by rw [hN]; exact ZMod.val_lt _⟩
  have gap (W : Finset (Fin n)) (hw : W⊆F) (hlo : F.card ≤ ∑ i∈W,(b i).val)
      (hhi : ∑ i∈W,(b i).val ≤ 2*r) : ∑ i∈W,(b i).val=r+W.card := by
    let s := ∑ i∈W,(b i).val
    change F.card ≤ s at hlo
    change s ≤ 2*r at hhi
    change s=r+W.card
    have hns : n-s+s=n := by omega
    have hs : ((n-s:ℕ):ZMod n)*1+∑ i∈W,b i=0 := by
      rw [mul_one,←OMA.R_Erdos541_erdos_541_variants_general_moduli_R1.cast_sum_val,←Nat.cast_add]
      change ((n-s+s:ℕ):ZMod n)=0
      rw [hns]; simp
    have hne : 0 < n-s ∨ W.Nonempty := by
      by_cases H : W=∅
      · left; simp [s,H]; omega
      · exact Or.inr (nonempty_iff_ne_empty.mpr H)
    have eq := fill hB (c:=1) (n-s) hw (by omega) hne hs
    omega
  have allEq := interval_gap F (fun i => (b i).val) hF hb gap
  apply card_two (c:=(u:ZMod n))
  intro i hi j hj
  rw [←hsame] at hi hj
  exact hU.mul_right_inj.mp (ZMod.val_injective _ (allEq i hi j hj))
end SC541Central

theorem OMA.solution : OMA.R_Erdos541_erdos_541_variants_general_moduli_R1.H2 := SC541Central.main
