import FormalConjectures.ErdosProblems.«790»
/-! Popular pair sums propagate from one dyadic layer to the next. -/
open Finset Erdos790 Filter Asymptotics
open scoped Classical
namespace SumFreeUpper

lemma split_sorted (S : Finset ℕ) (r : ℕ) (hr : r ≤ S.card) :
    ∃ L M : Finset ℕ, Disjoint L M ∧ L ∪ M = S ∧ L.card = r ∧
      ∀ a ∈ L, ∀ b ∈ M, a < b := by
  induction r generalizing S with
  | zero => exact ⟨∅,S,by simp,by simp,by simp,by simp⟩
  | succ r ih =>
    have hs : S.Nonempty := card_pos.mp (by omega)
    let m := S.min' hs
    have hm : m ∈ S := min'_mem _ _
    have hc := card_erase_of_mem hm
    obtain ⟨L,M,hd,hu,hl,hlt⟩ := ih (S.erase m) (by omega)
    have hn : m ∉ L ∪ M := by rw [hu]; simp
    have hmL : m ∉ L := fun hh => hn (mem_union_left _ hh)
    have hmM : m ∉ M := fun hh => hn (mem_union_right _ hh)
    refine ⟨insert m L, M, disjoint_insert_left.mpr ⟨hmM,hd⟩, ?_, by simp [hmL,hl], ?_⟩
    · rw [insert_union,hu,insert_erase hm]
    · intro a ha b hb
      rcases mem_insert.mp ha with rfl | ha
      · have hb' : b ∈ S.erase m := hu ▸ mem_union_right _ hb
        exact lt_of_le_of_ne (min'_le _ _ (mem_erase.mp hb').2) (mem_erase.mp hb').1.symm
      · exact hlt a ha b hb

def interval (M : ℕ) := Ico M (2*M)
def reps (D : Finset ℕ) (x : ℕ) :=
  D.filter (fun a => ∃ b ∈ D, a ≠ b ∧ a+b=2*x)
def popular (D : Finset ℕ) (M R : ℕ) :=
  (interval M).filter (fun x => R < (reps D x).card)

lemma pop_count {D : Finset ℕ} {M R r : ℕ} (hD : D ⊆ interval M)
    {P : Finset ℕ} (hpD : P ⊆ D) (parity : ∀ a ∈ P, ∀ b ∈ P, a%2=b%2)
    (hr : 0 < r) :
    2*P.card*r ≤ (popular D M R).card*r + M*R + 4*r*r := by
  by_cases hsz : 2*r ≤ P.card
  swap
  · nlinarith only [Nat.mul_le_mul_right r (show P.card ≤ 2*r by omega),
      Nat.zero_le ((popular D M R).card*r),Nat.zero_le (M*R)]
  obtain ⟨L,U,hdLU,hLU,hL,ltLU⟩ := split_sorted P r (by omega)
  have cu := card_union_of_disjoint hdLU
  rw [hLU,hL] at cu
  let m := U.card-r
  obtain ⟨T,H,hdTH,hTH,hT,ltTH⟩ := split_sorted U m (Nat.sub_le ..)
  have ch := card_union_of_disjoint hdTH
  rw [hTH,hT] at ch
  have hH : H.card = r := by dsimp [m] at ch; omega
  have hP : L ∪ (T ∪ H) = P := by rw [hTH,hLU]
  have hLP : L ⊆ P := hLU ▸ subset_union_left
  have hTP : T ⊆ P := hP ▸ subset_union_left.trans subset_union_right
  have hHP : H ⊆ P := hP ▸ subset_union_right.trans subset_union_right
  have ltLT (a) (ha : a ∈ L) (b) (hb : b ∈ T) := ltLU a ha b (hTH ▸ mem_union_left H hb)
  have hdLH : Disjoint L H := hdLU.mono_right (hTH ▸ subset_union_right)
  let F := (L ∪ H) ×ˢ T
  let g := fun p : ℕ × ℕ => (p.1+p.2)/2
  have props (p : ℕ×ℕ) (h : p ∈ F) :
      p.1 ∈ P ∧ p.2 ∈ P ∧ p.1 ≠ p.2 ∧ p.1+p.2=2*g p := by
    obtain ⟨ha,hb⟩ := mem_product.mp h
    have haP := (union_subset hLP hHP) ha
    have hbP := hTP hb
    have hp := parity _ haP _ hbP
    refine ⟨haP,hbP,?_,by dsimp [g]; omega⟩
    rcases mem_union.mp ha with hl | hh
    · exact (ltLT _ hl _ hb).ne
    · exact (ltTH _ hb _ hh).ne'
  have hg (p : ℕ×ℕ) (hp : p ∈ F) : g p ∈ interval M := by
    obtain ⟨ha,hb,_,he⟩ := props p hp
    obtain ⟨ha1,ha2⟩ := mem_Ico.mp (hD (hpD ha))
    obtain ⟨hb1,hb2⟩ := mem_Ico.mp (hD (hpD hb))
    exact mem_Ico.mpr ⟨by omega,by omega⟩
  let fiber := fun x => F.filter (fun p => g p = x)
  have fib_mem {x : ℕ} {p : ℕ×ℕ} (hp : p ∈ fiber x) :
      p ∈ F ∧ p.1+p.2=2*x := by
    obtain ⟨h,e⟩ := mem_filter.mp hp
    exact ⟨h, e ▸ (props p h).2.2.2⟩
  have inj (x : ℕ) : Set.InjOn (Prod.fst : ℕ × ℕ → ℕ) (fiber x : Set (ℕ × ℕ)) := by
    intro p hp q hq he
    exact Prod.ext he (by have h := (fib_mem hp).2; have h' := (fib_mem hq).2; omega)
  have cardLow (x) : (fiber x).card ≤ (reps D x).card := by
    apply card_le_card_of_injOn Prod.fst _ (inj x)
    intro p hp
    obtain ⟨h,e⟩ := fib_mem hp
    obtain ⟨h1,h2,hn,_⟩ := props p h
    exact mem_filter.mpr ⟨hpD h1,_,hpD h2,hn,e⟩
  have cardHigh (x) : (fiber x).card ≤ r := by
    by_cases hex : ∃ p ∈ fiber x, p.1 ∈ L
    · obtain ⟨p,hp,hl⟩ := hex
      rw [← hL]
      apply card_le_card_of_injOn Prod.fst _ (inj x)
      intro q hq
      obtain ⟨hpF,ep⟩ := fib_mem hp
      obtain ⟨hqF,eq⟩ := fib_mem hq
      rcases mem_union.mp (mem_product.mp hqF).1 with hlq | hhq
      · exact hlq
      · have h1 := ltLT _ hl _ (mem_product.mp hqF).2
        have h2 := ltTH _ (mem_product.mp hpF).2 _ hhq
        omega
    · rw [← hH]
      apply card_le_card_of_injOn Prod.fst _ (inj x)
      intro p hp
      exact (mem_union.mp (mem_product.mp (fib_mem hp).1).1).resolve_left (fun hl => hex ⟨p,hp,hl⟩)
  let C := popular D M R
  have hc : C ⊆ interval M := filter_subset .. 
  have counts := card_eq_sum_card_fiberwise hg
  change F.card = ∑ x ∈ interval M, (fiber x).card at counts
  rw [← sum_sdiff hc] at counts
  have hlow := sum_le_sum (s := interval M \ C) (g := fun _ => R) (fun x hx => by
    have hn := (mem_sdiff.mp hx).2
    have hi := (mem_sdiff.mp hx).1
    have hh : ¬ R < (reps D x).card := fun hh => hn (mem_filter.mpr ⟨hi,hh⟩)
    exact (cardLow x).trans (by omega))
  have hhigh := sum_le_sum (s := C) (g := fun _ => r) (fun x _ => cardHigh x)
  have hcM : (interval M \ C).card ≤ M := by
    simpa [interval,two_mul] using card_le_card (sdiff_subset (s := interval M) (t := C))
  have hF : F.card = (r+r)*m := by simp only [F,card_product,card_union_of_disjoint hdLH,hL,hH,hT]
  simp only [sum_const,smul_eq_mul] at hlow hhigh
  have hmm : m+2*r=P.card := by dsimp [m]; omega
  change 2*P.card*r ≤ C.card*r + M*R + _
  nlinarith only [counts,hlow,hhigh,Nat.mul_le_mul_right R hcM,hF,congrArg (fun a => a*r) hmm]

def q (s : ℕ) := 2^(s+3)
def width (s : ℕ) := (q s)^3
def loss (s : ℕ) := 5*(q s)^2

lemma popular_size (s : ℕ) (D : Finset ℕ) (h : D ⊆ interval (width s)) :
    D.card ≤ (popular D (width s) (q s)).card + loss s := by
  let E := D.filter (fun x => x%2=0)
  let O := D \ E
  have hd : E ⊆ D := filter_subset ..
  have hc := card_sdiff_add_card_eq_card hd
  have hP : ∃ P ⊆ D, D.card ≤ 2*P.card ∧ ∀ a ∈ P, ∀ b ∈ P, a%2=b%2 := by
    by_cases he : D.card ≤ 2*E.card
    · exact ⟨E,hd,he,fun _ ha _ hb => (mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm⟩
    · have hO {a} (ha : a ∈ O) : a%2 ≠ 0 := fun hh =>
        (mem_sdiff.mp ha).2 (mem_filter.mpr ⟨(mem_sdiff.mp ha).1,hh⟩)
      exact ⟨O,sdiff_subset,by dsimp [O]; omega,fun a ha b hb => by have := hO ha; have := hO hb; omega⟩
  obtain ⟨P,hp,hc,parity⟩ := hP
  have hq : 0 < q s := by dsimp [q]; positivity
  have hh := pop_count (R := q s) (r := (q s)^2) h hp parity (by positivity)
  apply Nat.le_of_mul_le_mul_right (c := (q s)^2) _ (by positivity)
  dsimp [width,loss] at hh ⊢
  nlinarith only [hh,Nat.mul_le_mul_right ((q s)^2) hc]

/-- A set of targets with many representations by pairs can use pairwise disjoint pairs. -/
lemma expand {D T : Finset ℕ} {R : ℕ} (h : ∀ x ∈ T, R < (reps D x).card)
    (budget : 4*T.card ≤ R) :
    ∃ W ⊆ D, W.card = 2*T.card ∧ ∑ w ∈ W, w = 2*∑ t ∈ T,t := by
  induction T using Finset.induction_on with
  | empty => exact ⟨∅,by simp,by simp,by simp⟩
  | @insert x T hx ih =>
    have hc := card_insert_of_notMem hx
    obtain ⟨W,hWD,hw,hs⟩ := ih (fun t ht => h _ (mem_insert_of_mem ht)) (by omega)
    let bad := W ∪ W.image (fun w => 2*x-w)
    have hbad : bad.card ≤ 2*W.card :=
      (card_union_le ..).trans (by have := card_image_le (s := W) (f := fun w => 2*x-w); omega)
    have hh := h x (mem_insert_self ..)
    have hn : ¬ reps D x ⊆ bad := fun sub => by have := card_le_card sub; omega
    obtain ⟨a,ha,han⟩ := not_subset.mp hn
    obtain ⟨haD,b,hbD,hab,hsum⟩ := mem_filter.mp ha
    have haW : a ∉ W := fun ha => han (mem_union_left _ ha)
    have hbW : b ∉ W := fun hb => han (mem_union_right _ (mem_image.mpr ⟨b,hb,by omega⟩))
    have hni : a ∉ insert b W := by simp [hab,haW]
    refine ⟨insert a (insert b W),insert_subset haD (insert_subset hbD hWD),?_,?_⟩
    · rw [card_insert_of_notMem hni,card_insert_of_notMem hbW,hc,hw]; omega
    · rw [sum_insert hni,sum_insert hbW,sum_insert hx,hs]; omega

def lowerFree (B : Finset ℕ) := ∀ a ∈ B, ∀ S ⊆ B, (∀ z ∈ S, z < a) → (∑ z ∈ S,z) ≠ a
def layer (B : Finset ℕ) (M i : ℕ) := (interval M).filter (fun a => 2^i*a ∈ B)
def carried (B : Finset ℕ) (s : ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | i+1 => popular (carried B s i ∪ layer B (width s) i) (width s) (q s)

lemma carried_sub (B : Finset ℕ) (s i : ℕ) : carried B s i ⊆ interval (width s) := by
  cases i with
  | zero => simp [carried]
  | succ i => exact filter_subset ..

lemma carried_sum (B : Finset ℕ) (s i : ℕ) (hi : i ≤ s+1)
    (T : Finset ℕ) (ht : T ⊆ carried B s i) (hb : T.card ≤ 2^(s+1-i)) :
    ∃ S ⊆ B, (∀ z ∈ S, z < 2^i*width s) ∧ ∑ z ∈ S,z = 2^i*∑ t ∈ T,t := by
  induction i generalizing T with
  | zero =>
    have he : T = ∅ := subset_empty.mp ht
    exact ⟨∅,empty_subset _,by simp,by simp [he]⟩
  | succ i ih =>
    let C := carried B s i
    let L := layer B (width s) i
    have hq : 4*T.card ≤ q s := by
      have hn := Nat.pow_le_pow_right (by decide : 0 < 2) (show s+1-(i+1) ≤ s by omega)
      dsimp [q]; rw [pow_add]
      omega
    obtain ⟨W,hW,hw,hs⟩ := expand (D := C ∪ L) (fun x hx => (mem_filter.mp (ht hx)).2) hq
    let V := W.filter (· ∈ C)
    let U := W \ V
    have hvW : V ⊆ W := filter_subset ..
    have hvC : V ⊆ C := fun _ hh => (mem_filter.mp hh).2
    have hUL : U ⊆ L := by
      intro u hu
      obtain ⟨huW,hn⟩ := mem_sdiff.mp hu
      exact (mem_union.mp (hW huW)).resolve_left (fun hh => hn (mem_filter.mpr ⟨huW,hh⟩))
    have hv : V.card ≤ 2^(s+1-i) := by
      have hc := card_le_card hvW
      rw [show s+1-i=(s+1-(i+1))+1 by omega,pow_succ]
      omega
    obtain ⟨S,hSB,hSm,hSum⟩ := ih (by omega) V hvC hv
    let f := fun u : ℕ => 2^i*u
    have hU {u} (hu : u ∈ U) : u ∈ interval (width s) ∧ f u ∈ B := mem_filter.mp (hUL hu)
    have hpow : 0 < (2:ℕ)^i := by positivity
    have hd : Disjoint S (U.image f) := by
      rw [disjoint_left]
      intro z hz hu
      obtain ⟨u,hu0,rfl⟩ := mem_image.mp hu
      exact (not_lt_of_ge (Nat.mul_le_mul_left _ (mem_Ico.mp (hU hu0).1).1)) (hSm _ hz)
    have hsumU : (∑ z ∈ U.image f,z) = 2^i*∑ u ∈ U,u := by
      rw [sum_image (fun a _ b _ he => Nat.eq_of_mul_eq_mul_left hpow he),mul_sum]
    have hsumW : (∑ u ∈ U,u) + ∑ v ∈ V,v = ∑ w ∈ W,w := sum_sdiff hvW
    refine ⟨S ∪ U.image f,union_subset hSB (fun z hz => ?_),?_,?_⟩
    · obtain ⟨u,hu,rfl⟩ := mem_image.mp hz
      exact (hU hu).2
    · intro z hz
      rcases mem_union.mp hz with hz | hz
      · have hh := hSm _ hz
        rw [pow_succ]; nlinarith only [hh]
      · obtain ⟨u,hu,rfl⟩ := mem_image.mp hz
        have hh := Nat.mul_lt_mul_of_pos_left (mem_Ico.mp (hU hu).1).2 hpow
        dsimp [f]; rw [pow_succ]; nlinarith only [hh]
    · rw [sum_union hd,hsumU,hSum,pow_succ]
      nlinarith only [congrArg (fun x => 2^i*x) hsumW,congrArg (fun x => 2^i*x) hs]

lemma carried_disjoint (B : Finset ℕ) (free : lowerFree B) (s i : ℕ) (hi : i ≤ s+1) :
    Disjoint (carried B s i) (layer B (width s) i) := by
  rw [disjoint_left]
  intro x hx hL
  obtain ⟨hI,hB⟩ := mem_filter.mp hL
  obtain ⟨W,hW,hm,hs⟩ := carried_sum B s i hi {x} (by simpa) (by simp only [card_singleton]; exact Nat.one_le_pow _ _ (by decide))
  apply free _ hB W hW (fun z hz => (hm z hz).trans_le (Nat.mul_le_mul_left _ (mem_Ico.mp hI).1))
  simpa using hs

lemma layer_count (B : Finset ℕ) (free : lowerFree B) (s k : ℕ) (hk : k ≤ s+1) :
    ∑ i ∈ range k,(layer B (width s) i).card ≤ (carried B s k).card + k*loss s := by
  induction k with
  | zero => simp
  | succ k ih =>
    let C := carried B s k
    let L := layer B (width s) k
    have h : C ∪ L ⊆ interval (width s) := union_subset (carried_sub ..) (filter_subset ..)
    have hh := popular_size s _ h
    rw [card_union_of_disjoint (carried_disjoint B free s k (by omega))] at hh
    change (carried B s k).card + (layer B (width s) k).card ≤ (carried B s (k+1)).card + loss s at hh
    rw [sum_range_succ,Nat.succ_mul]
    have := ih (by omega); omega

def scaled (M i : ℕ) := (interval M).image (fun a => 2^i*a)
def tower (s : ℕ) := (range (s+1)).biUnion (scaled (width s))

lemma scaled_bounds {M i x : ℕ} (h : x ∈ scaled M i) : 2^i*M ≤ x ∧ x < 2^(i+1)*M := by
  obtain ⟨a,ha,rfl⟩ := mem_image.mp h
  obtain ⟨hl,hu⟩ := mem_Ico.mp ha
  refine ⟨Nat.mul_le_mul_left _ hl,?_⟩
  have hh := Nat.mul_lt_mul_of_pos_left hu (by positivity : 0 < 2^i)
  rw [pow_succ]; nlinarith only [hh]

lemma tower_card (s : ℕ) : (tower s).card = (s+1)*width s := by
  have disj {i j : ℕ} (hl : i < j) : Disjoint (scaled (width s) i) (scaled (width s) j) := by
    rw [disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge (scaled_bounds hy).1) ((scaled_bounds hx).2.trans_le
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hl)))
  rw [tower,card_biUnion (fun a _ b _ hab => by rcases Nat.lt_or_gt_of_ne hab with h | h
                                                exact disj h
                                                exact (disj h).symm)]
  have hc (i) : (scaled (width s) i).card = width s := by
    rw [scaled,card_image_of_injective _ (fun _ _ he => Nat.eq_of_mul_eq_mul_left (by positivity) he)]
    simp [interval,two_mul]
  simp [hc]

lemma q_lb (s : ℕ) : 5*(s+1) ≤ q s := by
  induction s with
  | zero => decide
  | succ s ih =>
    have hr : q (s+1) = q s * 2 := by simp [q,pow_succ]
    omega

lemma bound_B (s : ℕ) (B : Finset ℕ) (hB : B ⊆ tower s) (free : lowerFree B) :
    B.card ≤ 2*width s := by
  let F := fun i => (layer B (width s) i).image (fun a => 2^i*a)
  have hUF : B ⊆ (range (s+1)).biUnion F := by
    intro x hx
    obtain ⟨i,hi,hy⟩ := mem_biUnion.mp (hB hx)
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hy
    exact mem_biUnion.mpr ⟨i,hi,mem_image.mpr ⟨a,mem_filter.mpr ⟨ha,hx⟩,rfl⟩⟩
  have hcnt := (card_le_card hUF).trans (card_biUnion_le.trans
    (sum_le_sum (fun i _ => card_image_le (s := layer B (width s) i) (f := fun a => 2^i*a))))
  have hsum := layer_count B free s (s+1) le_rfl
  have hc := card_le_card (carried_sub B s (s+1))
  simp [interval,two_mul] at hc
  have hq := q_lb s
  have hl : (s+1)*loss s ≤ width s := by
    dsimp [loss,width]
    nlinarith only [Nat.mul_le_mul_right (q s ^ 2) hq]
  omega

lemma coe_card (U : Finset ℕ) : (U.image (Nat.cast : ℕ → ℤ)).card = U.card :=
  card_image_of_injective _ Nat.cast_injective

lemma guarantees_bound (n s : ℕ) (h : n ≤ (s+1)*width s) : l n ≤ 2*width s := by
  classical
  have hg0 : Guarantees n 0 := fun _ _ => ⟨∅,empty_subset _,by simp [DistinctSubsetSumFree],by simp⟩
  have hg : Guarantees n (l n) := Nat.findGreatest_spec (Nat.zero_le _) hg0
  let X := tower s
  obtain ⟨N,hNX,hN⟩ := exists_subset_card_eq (s := X.image (Nat.cast : ℕ → ℤ))
    (n := n) (by rwa [coe_card,tower_card])
  obtain ⟨Y,hYN,free,size⟩ := hg N hN
  let B := X.filter (fun (a : ℕ) => (a:ℤ) ∈ Y)
  have castB : B.image (Nat.cast : ℕ → ℤ) = Y := by
    ext y
    constructor
    · intro hy
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hy
      exact (mem_filter.mp ha).2
    · intro hy
      obtain ⟨a,ha,rfl⟩ := mem_image.mp (hNX (hYN hy))
      exact mem_image.mpr ⟨a,mem_filter.mpr ⟨ha,hy⟩,rfl⟩
  have pos {a : ℕ} (ha : a ∈ B) : 0 < a := by
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp (mem_filter.mp ha).1
    exact lt_of_lt_of_le (by dsimp [width,q]; positivity) (scaled_bounds hi).1
  have hfree : lowerFree B := by
    intro a ha S hSB hlt he
    have hsc : 2 ≤ S.card := by
      by_contra! hn
      rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp (show S.card ≤ 1 by omega)) with hz | ho
      · obtain rfl := card_eq_zero.mp hz
        simp at he
        exact (pos ha).ne he
      · obtain ⟨x,rfl⟩ := card_eq_one.mp ho
        have hh := hlt x (mem_singleton_self x)
        simp at he
        omega
    let U := S.image (Nat.cast : ℕ → ℤ)
    apply free (a:ℤ) (castB ▸ mem_image_of_mem _ ha) U _ (by simpa [U,coe_card] using hsc)
    · rw [← he]
      simp [U,sum_image Nat.cast_injective.injOn]
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
      exact mem_erase.mpr ⟨by exact_mod_cast (hlt x hx).ne, castB ▸ mem_image_of_mem _ (hSB hx)⟩
  rw [← castB,coe_card] at size
  exact size.trans (bound_B s B (filter_subset ..) hfree)

lemma size_log (s n : ℕ) (hn : 0 < n) (h : n ≤ (s+1)*width s) :
    Real.log n ≤ 10*((s:ℝ)+1) := by
  have hs : s+1 ≤ 2^(s+1) := Nat.lt_two_pow_self.le
  have hwidth : width s = 2^(3*(s+3)) := by
    rw [width,q,← pow_mul]; congr 1; omega
  have hpow : n ≤ 2^((s+1)+3*(s+3)) := by
    refine h.trans ?_
    rw [pow_add,hwidth]
    exact Nat.mul_le_mul_right _ hs
  have hr := Real.log_le_log (by exact_mod_cast hn : 0 < (n:ℝ))
    (by exact_mod_cast hpow : (n:ℝ) ≤ (2:ℝ)^((s+1)+3*(s+3)))
  rw [Real.log_pow] at hr
  push_cast at hr
  have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  nlinarith only [hr,h2,mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg s),Nat.cast_nonneg (α := ℝ) s]

end SumFreeUpper
open SumFreeUpper

theorem OMA.solution : type_of% @Erdos790.erdos_790.variants.upper_bound := by
  classical
  apply Asymptotics.IsBigO.of_bound (320:ℝ)
  filter_upwards [eventually_ge_atTop 513] with n hn
  have hn' : 1 < (n:ℝ) := by exact_mod_cast (show 1 < n by omega)
  let P := fun s => n ≤ (s+1)*width s
  have ex : ∃ s, P s := ⟨n,by
    have hp : 0 < width n := by dsimp [width,q]; positivity
    exact Nat.le_trans (Nat.le_succ _) (Nat.le_mul_of_pos_right _ hp)⟩
  let s := Nat.find ex
  have h := Nat.find_spec ex
  change n ≤ (s+1)*width s at h
  have hs : 0 < s := by
    by_contra! he
    have he' : s=0 := by omega
    rw [he'] at h
    norm_num [width,q] at h
    omega
  have hprev := Nat.find_min ex (m := s-1) (show s-1 < s by omega)
  change ¬ n ≤ (s-1+1)*width (s-1) at hprev
  have hwidth : width s = 8*width (s-1) := by
    have hq : q s = 2*q (s-1) := by
      unfold q
      rw [show s+3 = (s-1+3)+1 by omega,pow_succ]; omega
    simp only [width,hq]; ring
  have hmul : (s+1)*width s ≤ 16*n := by
    rw [show s-1+1=s by omega] at hprev
    have hh : width (s-1) ≤ s*width (s-1) := Nat.le_mul_of_pos_left _ hs
    rw [hwidth]
    nlinarith only [lt_of_not_ge hprev,hh]
  have hsum : (l n : ℝ) ≤ 2*width s := by exact_mod_cast guarantees_bound n s h
  have hm : ((s:ℝ)+1)*width s ≤ 16*(n:ℝ) := by exact_mod_cast hmul
  have hlog := size_log s n (by omega) h
  have hpos := Real.log_pos hn'
  simp only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (l n)),
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hpos.le)]
  rw [← mul_div_assoc,le_div_iff₀ hpos]
  nlinarith only [mul_le_mul_of_nonneg_right hsum hpos.le,
    mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) (width s)),hm]
