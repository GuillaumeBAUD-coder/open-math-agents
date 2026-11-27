import OMAReductions.R_Erdos541_erdos_541_variants_general_moduli_R1

/-!
The Savchev–Chen structure theorem for long zero-sum-free sequences.
This follows V. F. Lev, Zero-sum-free sequences with few subsequence sums,
with a translation argument for uniqueness of a sharp extension. For a
sharp extension, shifting the old set with its total erased gives the
old set with zero erased, and the analogous identity holds for the new
set. These identities force the translating element to be unique.
-/

namespace SC541
open Finset
open scoped Classical
variable {ι G : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq ι]
variable (x : ι → G)

def sums (V : Finset ι) := V.powerset.image (fun W => ∑ i ∈ W, x i)
def Free (U : Finset ι) := ∀ W ⊆ U, W.Nonempty → ∑ i ∈ W, x i ≠ 0
def shift (S : Finset G) (v : G) := S.image fun t => t+v

lemma mem_sums {V : Finset ι} {t : G} :
    t ∈ sums x V ↔ ∃ W ⊆ V, ∑ i ∈ W, x i = t := by simp [sums]
lemma zero_mem (V : Finset ι) : 0 ∈ sums x V := (mem_sums x).mpr ⟨∅,empty_subset _,by simp⟩
lemma tot_mem (V : Finset ι) : (∑ i ∈ V, x i) ∈ sums x V := (mem_sums x).mpr ⟨V,Subset.rfl,rfl⟩
lemma sums_mono {V U : Finset ι} (h : V ⊆ U) : sums x V ⊆ sums x U := by
  intro z hz
  obtain ⟨w,hw,rfl⟩ := (mem_sums x).mp hz
  exact (mem_sums x).mpr ⟨w,hw.trans h,rfl⟩

lemma sums_insert {V : Finset ι} {i : ι} (hi : i∉V) :
    sums x (insert i V) = sums x V ∪ shift (sums x V) (x i) := by
  ext z
  constructor
  · intro h
    obtain ⟨w,hw,rfl⟩ := (mem_sums x).mp h
    by_cases hit : i∈w
    · have hs : w.erase i ⊆ V := fun j hj => by
        have := hw (mem_of_mem_erase hj)
        simpa [(mem_erase.mp hj).1] using this
      exact mem_union_right _ (mem_image.mpr ⟨_,(mem_sums x).mpr ⟨w.erase i,hs,rfl⟩,sum_erase_add _ _ hit⟩)
    · exact mem_union_left _ ((mem_sums x).mpr ⟨w,fun j hj => (mem_insert.mp (hw hj)).resolve_left
        (fun e => hit (e ▸ hj)),rfl⟩)
  · intro h
    rcases mem_union.mp h with h|h
    · exact sums_mono x (subset_insert ..) h
    · obtain ⟨v,hv,rfl⟩ := mem_image.mp h
      obtain ⟨w,hw,rfl⟩ := (mem_sums x).mp hv
      exact (mem_sums x).mpr ⟨insert i w, insert_subset_insert _ hw,
        by rw [sum_insert (fun h => hi (hw h)),add_comm]⟩

lemma fresh {V : Finset ι} {i : ι} (hi : i∉V) (hf : Free x (insert i V)) :
    (∑ j ∈ insert i V, x j) ∉ sums x V := by
  intro h
  obtain ⟨w,hw,he⟩ := (mem_sums x).mp h
  have hsub := hw.trans (subset_insert i V)
  have hmem : i ∈ insert i V \ w := mem_sdiff.mpr ⟨mem_insert_self ..,fun h => hi (hw h)⟩
  have hh := sum_sdiff hsub (f:=x)
  exact hf _ sdiff_subset ⟨i,hmem⟩ (by rw [← he] at hh; exact add_right_cancel (hh.trans (zero_add _).symm))

lemma neg_absent {V : Finset ι} {i : ι} (hi : i∉V) (hf : Free x (insert i V)) :
    -(x i) ∉ sums x V := by
  intro h
  obtain ⟨w,hw,he⟩ := (mem_sums x).mp h
  exact hf _ (insert_subset_insert i hw) (insert_nonempty ..)
    (by rw [sum_insert (fun h => hi (hw h)), he,add_neg_cancel])

lemma grows {V : Finset ι} {i : ι} (hi : i∉V) (hf : Free x (insert i V)) :
    (sums x V).card < (sums x (insert i V)).card := by
  have hsub := sums_mono x (subset_insert i V)
  apply card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,?_⟩)
  intro he
  exact fresh x hi hf (he ▸ tot_mem x (insert i V))

lemma atLeast {V : Finset ι} (hf : Free x V) : V.card+1 ≤ (sums x V).card := by
  induction V using Finset.induction_on with
  | empty => simp [sums]
  | @insert i V hi ih =>
    have h := ih (fun w hw => hf w (hw.trans (subset_insert i V)))
    have h' := grows x hi hf
    rw [card_insert_of_notMem hi]; omega

def Sharp (V : Finset ι) (i : ι) := (sums x (insert i V)).card ≤ (sums x V).card+1

lemma layout {V : Finset ι} {i : ι} (hi : i∉V) (hf : Free x (insert i V)) (hs : Sharp x V i) :
    sums x (insert i V) = insert (∑ j ∈ insert i V,x j) (sums x V) := by
  symm
  apply eq_of_subset_of_card_le (insert_subset (tot_mem ..) (sums_mono x (subset_insert ..)))
  rwa [card_insert_of_notMem (fresh x hi hf)]

lemma eq_shift_erase {T : Finset G} {s v w : G} (hs : s≠0) (hz : 0∈T)
    (hv : shift (T.erase s) v = T.erase 0) (hw : shift (T.erase s) w = T.erase 0) : v=w := by
  let A := T.erase s
  let B := T.erase 0
  change shift A v = B at hv
  change shift A w = B at hw
  have mov {t : G} (ht : t∈A) : t+(v-w)∈A := by
    have hit : t+v ∈ shift A w := by rw [hw,←hv]; exact mem_image_of_mem _ ht
    obtain ⟨q,hq,he⟩ := mem_image.mp hit
    have e : t+(v-w)=q := calc
      _ = (t+v)-w := by abel
      _ = q := by rw [← he,add_sub_cancel_right]
    rwa [e]
  have back {t : G} (ht : t+(v-w)∈B) : t∈B := by
    rw [← hv] at ht
    obtain ⟨q,hq,he⟩ := mem_image.mp ht
    rw [← hw]
    apply mem_image.mpr ⟨q,hq,?_⟩
    calc q+w = (q+v)-(v-w) := by abel
         _ = t := by rw [he,add_sub_cancel_right]
  have h0 : (0:G)∈A := mem_erase.mpr ⟨Ne.symm hs,hz⟩
  have hmov := mov h0
  rw [zero_add] at hmov
  by_contra h
  have hb : (0:G)+(v-w)∈B := by rw [zero_add]; exact mem_erase.mpr ⟨sub_ne_zero.mpr h,mem_of_mem_erase hmov⟩
  exact (mem_erase.mp (back hb)).1 rfl

lemma shift_card (S : Finset G) (v : G) : (shift S v).card = S.card :=
  card_image_of_injective _ (fun _ _ he => add_right_cancel he)

lemma sharp_shifts {V : Finset ι} {i : ι} (hi : i∉V) (hf : Free x (insert i V)) (hs : Sharp x V i) :
    shift ((sums x V).erase (∑ j ∈ V,x j)) (x i) = (sums x V).erase 0 ∧
    shift (sums x V) (x i) = (sums x (insert i V)).erase 0 := by
  have lay := layout x hi hf hs
  have hin {v : G} (hv : v∈sums x V) : v+x i ∈ sums x (insert i V) := by
    rw [sums_insert x hi]
    exact mem_union_right _ (mem_image_of_mem _ hv)
  have hn {v : G} (hv : v∈sums x V) : v+x i ≠ 0 := by
    intro hz
    exact neg_absent x hi hf ((eq_neg_of_add_eq_zero_left hz) ▸ hv)
  constructor
  · apply eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hz
      obtain ⟨hne,ht⟩ := mem_erase.mp ht
      have h := hin ht
      rw [lay, sum_insert hi,add_comm (x i), mem_insert] at h
      exact mem_erase.mpr ⟨hn ht, h.resolve_left (fun e => hne (add_right_cancel e))⟩
    · rw [shift_card,card_erase_of_mem (zero_mem ..),card_erase_of_mem (tot_mem ..)]
  · apply eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hz
      exact mem_erase.mpr ⟨hn ht,hin ht⟩
    · rw [shift_card,card_erase_of_mem (zero_mem ..)]
      exact Nat.sub_le_of_le_add (by simpa [Sharp,Nat.add_comm] using hs)

end SC541


namespace SC541
open Finset
open scoped Classical
variable {ι G : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq ι]
variable (x : ι → G)

lemma free_sub {U V : Finset ι} (h : V ⊆ U) (hf : Free x U) : Free x V :=
  fun w hw => hf w (hw.trans h)

lemma sharp_same_start {V : Finset ι} {i j : ι} (hV : V.Nonempty) (hi : i∉V) (hj : j∉V)
    (fi : Free x (insert i V)) (fj : Free x (insert j V)) (si : Sharp x V i) (sj : Sharp x V j) :
    x i = x j := by
  apply eq_shift_erase (fi V (subset_insert i V) hV) (zero_mem x V)
  · exact (sharp_shifts x hi fi si).1
  · exact (sharp_shifts x hj fj sj).1

lemma sharp_same_end {U : Finset ι} (hf : Free x U) {i j : ι} (hi : i∈U) (hj : j∈U)
    (si : Sharp x (U.erase i) i) (sj : Sharp x (U.erase j) j) : x i=x j := by
  have aux (k : ι) (hk : k∈U) (sk : Sharp x (U.erase k) k) :
      shift ((sums x U).erase (∑ l ∈ U, x l)) (x k) = (sums x U).erase 0 := by
    have fh : Free x (insert k (U.erase k)) := by simpa [hk] using hf
    have lay := layout x (notMem_erase k U) fh sk
    have fr := fresh x (notMem_erase k U) fh
    have sh := (sharp_shifts x (notMem_erase k U) fh sk).2
    rw [insert_erase hk] at lay fr sh
    have er := congrArg (fun (S : Finset G) => S.erase (∑ l ∈ U, x l)) lay
    simp [fr] at er
    rw [er,sh]
  exact eq_shift_erase (hf U Subset.rfl ⟨i,hi⟩) (zero_mem x U) (aux i hi si) (aux j hj sj)

lemma sharp_transfer {V : Finset ι} {i j : ι} (hi : i∉V) (hj : j∉V) (he : x j=x i)
    (hs : Sharp x V i) : Sharp x V j := by
  simpa [Sharp,sums_insert x hi,sums_insert x hj,he] using hs

lemma sharp_next {V : Finset ι} {i j : ι} (hi : i∉insert j V) (hj : j∉V) (he : x j=x i)
    (hf : Free x (insert j V)) (hs : Sharp x V i) : Sharp x (insert j V) i := by
  have hi' : i∉V := fun h => hi (mem_insert_of_mem h)
  have hj' := sharp_transfer x hi' hj he hs
  have lay := layout x hj hf hj'
  let W := insert j V
  let t := ∑ k ∈ W,x k
  have hsub : sums x (insert i W) ⊆ insert (t+x i) (sums x W) := by
    intro z hz
    rw [sums_insert x hi] at hz
    rcases mem_union.mp hz with h|h
    · exact mem_insert_of_mem h
    · obtain ⟨v,hv,rfl⟩ := mem_image.mp h
      rw [lay] at hv
      rcases mem_insert.mp hv with rfl|hv
      · exact mem_insert_self ..
      · apply mem_insert_of_mem
        rw [sums_insert x hj]
        apply mem_union_right
        rw [he]
        exact mem_image_of_mem _ hv
  exact (card_le_card hsub).trans (card_insert_le ..)

lemma sharp_many {U B : Finset ι} {i : ι} (hf : Free x U) (hi : i∈U) (hB : B⊆U)
    (hiB : i∉B) (hs : Sharp x B i)
    (he : ∀ j ∈ U, j∉B → x j = x i) : Sharp x (U.erase i) i := by
  have go (R : Finset ι) (hR : R ⊆ U.erase i) : Sharp x (R∪B) i := by
    induction R using Finset.induction_on with
    | empty => simpa using hs
    | @insert j R hj ih =>
      have hr := (insert_subset_iff.mp hR).2
      have hjU := (insert_subset_iff.mp hR).1
      have hind := ih hr
      rw [insert_union]
      by_cases hjB : j∈B
      · simpa [insert_eq_of_mem (mem_union_right R hjB)] using hind
      · apply sharp_next x _ (by simp [hj,hjB]) (he j (mem_of_mem_erase hjU) hjB) _ hind
        · simp [Ne.symm (mem_erase.mp hjU).1,hiB]
          exact fun h => (mem_erase.mp (hr h)).1 rfl
        · apply free_sub x _ hf
          exact insert_subset (mem_of_mem_erase hjU) (union_subset (hr.trans (erase_subset ..)) hB)
  have hb' : B⊆U.erase i := fun j hj => mem_erase.mpr ⟨fun e => hiB (e ▸ hj),hB hj⟩
  simpa [union_eq_left.mpr hb'] using go (U.erase i) Subset.rfl

lemma large_last {U P : Finset ι} (hf : Free x U) (hU : (sums x U).card < 2*U.card)
    (hP : P⊆U) (hne : P.Nonempty) (hbig : 2*P.card ≤ (sums x P).card) :
    ∃ i∈U, i∉P ∧ Sharp x (U.erase i) i := by
  let F := U.powerset.filter fun V => P⊆V ∧ 2*V.card ≤ (sums x V).card
  obtain ⟨B,hB,hmax⟩ := exists_max_image F Finset.card ⟨P,mem_filter.mpr
    ⟨mem_powerset.mpr hP,Subset.rfl,hbig⟩⟩
  obtain ⟨hb,hPB,hbigB⟩ := mem_filter.mp hB
  have hbU := mem_powerset.mp hb
  have hneU : ¬ U⊆B := fun h => by have e := Subset.antisymm h hbU; rw [←e] at hbigB; omega
  obtain ⟨i,hi,hiB⟩ := Finset.not_subset.mp hneU
  have sharp (j : ι) (hj : j∈U) (hn : j∉B) : Sharp x B j := by
    by_contra h
    have hc := card_insert_of_notMem hn
    change ¬ (sums x (insert j B)).card ≤ (sums x B).card+1 at h
    have hmem : insert j B ∈ F := mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hj hbU),
      hPB.trans (subset_insert ..),by omega⟩
    have := hmax _ hmem
    omega
  have fre (j : ι) (hj : j∈U) := free_sub x (insert_subset hj hbU) hf
  exact ⟨i,hi,fun h => hiB (hPB h),sharp_many x hf hi hbU hiB (sharp i hi hiB) (fun j hj hnj =>
    sharp_same_start x (hne.mono hPB) hnj hiB (fre j hj) (fre i hi) (sharp j hj hnj) (sharp i hi hiB))⟩

end SC541



namespace SC541
open Finset
open scoped Classical
variable {ι : Type*} [DecidableEq ι] {n : ℕ} (x : ι → ZMod n)

def Beh (a : ZMod n) (V : Finset ι) : Prop :=
  ∃ w : ι → ℕ, (∀ i ∈ V, 0<w i ∧ x i=(w i : ZMod n)*a) ∧
    ∀ t ≤ ∑ i ∈ V,w i, ∃ W ⊆ V, ∑ i ∈ W,w i=t

lemma weighted {w : ι → ℕ} {a : ZMod n} {V W : Finset ι}
    (he : ∀ i ∈ V, 0<w i ∧ x i=(w i : ZMod n)*a) (hW : W⊆V) :
    ∑ i ∈ W,x i = ((∑ i ∈ W,w i : ℕ) : ZMod n)*a := by
  push_cast
  rw [sum_mul]
  exact sum_congr rfl fun i hi => (he _ (hW hi)).2

lemma beh_same {a : ZMod n} {V : Finset ι} (h : ∀ i ∈ V,x i=a) : Beh x a V := by
  refine ⟨fun _ => 1, fun i hi => ⟨by norm_num,by simp [h i hi]⟩,?_⟩
  intro t ht
  simp only [sum_const,smul_eq_mul,mul_one] at ht ⊢
  exact exists_subset_card_eq ht

lemma extend_beh {a : ZMod n} {V : Finset ι} {j : ι} (hj : j∉V)
    (hf : Free x (insert j V)) (hb : Beh x a V)
    (hh : ¬ Disjoint (sums x V) (shift (sums x V) (x j))) : Beh x a (insert j V) := by
  obtain ⟨w,he,hw⟩ := hb
  let T := ∑ i ∈ V,w i
  obtain ⟨z,hz,hz'⟩ := not_disjoint_iff.mp hh
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hz'
  obtain ⟨R,hR,hr⟩ := (mem_sums x).mp hu
  obtain ⟨S,hS,hs⟩ := (mem_sums x).mp hz
  let r := ∑ i ∈ R,w i
  let s := ∑ i ∈ S,w i
  have er : u=(r:ZMod n)*a := hr.symm.trans (weighted x he hR)
  have es : u+x j=(s:ZMod n)*a := hs.symm.trans (weighted x he hS)
  have hrT : r≤T := sum_le_sum_of_subset hR
  have hsT : s≤T := sum_le_sum_of_subset hS
  have hrs : r<s := by
    by_contra! h
    obtain ⟨W,hW,hEq⟩ := hw (r-s) (by dsimp only [T] at hrT; omega)
    have heW : ∑ i ∈ W,x i = -(x j) := by
      rw [weighted x he hW,hEq,Nat.cast_sub h,sub_mul,← er,← es]
      abel
    exact neg_absent x hj hf ((mem_sums x).mpr ⟨W,hW,heW⟩)
  let t := s-r
  have ht : 0<t ∧ t≤T := by dsimp [t]; omega
  have hxt : x j=(t:ZMod n)*a := by
    dsimp only [t]
    rw [Nat.cast_sub hrs.le,sub_mul,← er,← es]
    abel
  let f := Function.update w j t
  have ef {i : ι} (hi : i∈V) : f i=w i := Function.update_of_ne (show i≠j from fun h => hj (h ▸ hi)) ..
  have efj : f j=t := Function.update_self ..
  have efW {W : Finset ι} (hW : W⊆V) : ∑ i ∈ W,f i = ∑ i ∈ W,w i :=
    sum_congr rfl fun i hi => ef (hW hi)
  refine ⟨f,?_,?_⟩
  · intro i hi
    rcases mem_insert.mp hi with rfl|hi
    · rw [efj]; exact ⟨ht.1,hxt⟩
    · rw [ef hi]; exact he i hi
  · intro v hv
    rw [sum_insert hj,efj,efW Subset.rfl] at hv
    change v≤t+T at hv
    by_cases h : v≤T
    · obtain ⟨W,hW,hv'⟩ := hw v h
      exact ⟨W,hW.trans (subset_insert ..),(efW hW).trans hv'⟩
    · obtain ⟨W,hW,hv'⟩ := hw (v-t) (Nat.sub_le_iff_le_add.mpr (by omega))
      exact ⟨insert j W,insert_subset_insert _ hW,by
        rw [sum_insert (fun h => hj (hW h)),efj,efW hW,hv']; omega⟩

lemma final_or_last {U P : Finset ι} (hf : Free x U) (hU : (sums x U).card < 2*U.card)
    {a : ZMod n} (hP : P⊆U) (hne : P.Nonempty) (hB : Beh x a P) :
    Beh x a U ∨ ∃ i∈U, i∉P ∧ Sharp x (U.erase i) i := by
  classical
  let F := U.powerset.filter fun V => P⊆V ∧ Beh x a V
  obtain ⟨V,hV,hmax⟩ := exists_max_image F Finset.card ⟨P,mem_filter.mpr ⟨mem_powerset.mpr hP,Subset.rfl,hB⟩⟩
  obtain ⟨hv,hpv,hb⟩ := mem_filter.mp hV
  have hvU := mem_powerset.mp hv
  by_cases e : V=U
  · exact Or.inl (e ▸ hb)
  · have hno : ¬ U⊆V := fun h => e (Subset.antisymm hvU h)
    obtain ⟨j,hj,hjV⟩ := Finset.not_subset.mp hno
    have hf' := free_sub x (insert_subset hj hvU) hf
    have hdis : Disjoint (sums x V) (shift (sums x V) (x j)) := by
      by_contra hd
      have hn : insert j V ∈ F := mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hj hvU),
        hpv.trans (subset_insert ..), extend_beh x hjV hf' hb hd⟩
      have h := hmax _ hn
      rw [card_insert_of_notMem hjV] at h
      omega
    have hlarge : 2*(insert j V).card ≤ (sums x (insert j V)).card := by
      rw [sums_insert x hjV,card_union_of_disjoint hdis,shift_card,card_insert_of_notMem hjV]
      have := atLeast x (free_sub x hvU hf)
      omega
    obtain ⟨i,hi,hi',hsh⟩ := large_last x hf hU (insert_subset hj hvU) (insert_nonempty ..) hlarge
    exact Or.inr ⟨i,hi,fun h => hi' (mem_insert_of_mem (hpv h)),hsh⟩

theorem structured {U : Finset ι} (hf : Free x U) (hU : (sums x U).card < 2*U.card) :
    ∃ a, Beh x a U := by
  classical
  have hn : U.Nonempty := by by_contra! h; simp [h] at hU
  obtain ⟨j,hj⟩ := hn
  have hsing : Beh x (x j) {j} := beh_same x (by simp)
  rcases final_or_last x hf hU (singleton_subset_iff.mpr hj) (singleton_nonempty j) hsing with h|⟨i,hi,_,hsh⟩
  · exact ⟨_,h⟩
  let P := U.filter fun k => x k=x i
  have hiP : i∈P := mem_filter.mpr ⟨hi,rfl⟩
  have hb : Beh x (x i) P := beh_same x (fun k hk => (mem_filter.mp hk).2)
  rcases final_or_last x hf hU (filter_subset ..) ⟨i,hiP⟩ hb with h|⟨k,hk,hkP,hksh⟩
  · exact ⟨_,h⟩
  · exact False.elim (hkP (mem_filter.mpr ⟨hk,sharp_same_end x hf hk hi hksh hsh⟩))

end SC541


namespace SC541
open Finset
open scoped Classical

theorem main (n : ℕ) (ι : Type) (U : Finset ι) (x : ι → ZMod n) (hn : 0<n)
    (hf : ∀ W ⊆ U, W.Nonempty → ∑ i ∈ W, x i ≠ 0) (hsize : n < 2*U.card) :
    ∃ u : ZMod n, IsUnit u ∧ ∑ i ∈ U, (u*x i).val < n := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  have hbig : (sums x U).card < 2*U.card := by
    have he := Finset.card_le_univ (sums x U)
    rw [ZMod.card] at he
    omega
  obtain ⟨a,w,hw,hreal⟩ := structured x hf hbig
  let T := ∑ i ∈ U,w i
  have hT : U.card ≤ T := by
    simpa using Finset.card_nsmul_le_sum U w 1 (fun i hi => (hw i hi).1)
  have ho : 0 < addOrderOf a := addOrderOf_pos a
  have hLT : T < addOrderOf a := by
    by_contra! h
    obtain ⟨W,hW,hWsum⟩ := hreal (addOrderOf a) h
    have hne : W.Nonempty := by
      by_contra! h'
      rw [h'] at hWsum
      simp at hWsum
      omega
    apply hf W hW hne
    rw [weighted x hw hW,hWsum,←nsmul_eq_mul,addOrderOf_nsmul_eq_zero]
  have hord := ZMod.addOrderOf_coe a.val hn.ne'
  rw [ZMod.natCast_zmod_val] at hord
  have hcop : n.gcd a.val = 1 := by
    have hp := Nat.gcd_pos_of_pos_left a.val hn
    by_contra h
    have hs : n / n.gcd a.val ≤ n/2 := Nat.div_le_div_left (by omega) (by decide)
    omega
  rw [hcop,Nat.div_one] at hord
  rw [hord] at hLT
  have hu : IsUnit a := by
    rw [←ZMod.natCast_zmod_val a,ZMod.isUnit_iff_coprime]
    exact (show n.Coprime a.val from hcop).symm
  obtain ⟨b,hb⟩ := hu
  refine ⟨↑b⁻¹,b⁻¹.isUnit,?_⟩
  have hsum : ∑ i ∈ U, ((↑b⁻¹ : ZMod n)*x i).val = T := by
    apply sum_congr rfl
    intro i hi
    have hle : w i ≤ T := single_le_sum (fun j _ => Nat.zero_le (w j)) hi
    rw [(hw i hi).2,← hb,mul_comm (w i : ZMod n),←mul_assoc]
    simpa using ZMod.val_natCast_of_lt (hle.trans_lt hLT)
  rwa [hsum]

end SC541


theorem OMA.solution : OMA.R_Erdos541_erdos_541_variants_general_moduli_R1.H1 := SC541.main
