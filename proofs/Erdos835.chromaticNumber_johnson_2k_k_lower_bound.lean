import FormalConjectures.ErdosProblems.«835»
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort

/-! Small Johnson graphs via derived Steiner systems and finite exact cover. -/

open Finset SimpleGraph

namespace OMA.E835

def pointSet (b : ℕ) : Finset ℕ := Finset.equivBitIndices b

def blockCode (S : Finset ℕ) : ℕ := Finset.equivBitIndices.symm S

@[simp] theorem pointSet_blockCode (S : Finset ℕ) : pointSet (blockCode S) = S :=
  Finset.equivBitIndices.apply_symm_apply S

@[simp] theorem blockCode_pointSet (b : ℕ) : blockCode (pointSet b) = b :=
  Finset.equivBitIndices.symm_apply_apply b

@[simp] theorem mem_pointSet {b i : ℕ} : i ∈ pointSet b ↔ b.testBit i := by
  simp [pointSet, Finset.equivBitIndices]

@[simp] theorem card_pointSet (b : ℕ) : (pointSet b).card = b.bitIndices.length := by
  change b.bitIndices.toFinset.card = b.bitIndices.length
  exact List.toFinset_card_of_nodup Nat.bitIndices_nodup

def smallSets (n r : ℕ) : List ℕ :=
  (List.range (2^n)).filter fun b => b.bitIndices.length == r

@[simp] theorem mem_smallSets {n r b : ℕ} :
    b ∈ smallSets n r ↔ b < 2^n ∧ (pointSet b).card = r := by
  simp [smallSets]

theorem points_bounded {b n i : ℕ} (hb : b < 2^n) (hi : i ∈ pointSet b) : i < n := by
  have h := Nat.ge_two_pow_of_testBit (mem_pointSet.mp hi)
  by_contra! hni
  exact hb.not_ge ((Nat.pow_le_pow_right (by decide) hni).trans h)

theorem code_bounded {n : ℕ} {S : Finset ℕ} (hS : ∀ i ∈ S, i < n) :
    blockCode S < 2^n := by
  classical
  have hsub : S ⊆ range n := fun i hi => mem_range.mpr (hS i hi)
  change (∑ i ∈ S, 2^i) < 2^n
  have H : ∑ i ∈ S, 2^i ≤ ∑ i ∈ range n, 2^i :=
    sum_le_sum_of_subset hsub
  have hsum (m : ℕ) : (∑ i ∈ range m, 2^i) + 1 = 2^m := by
    induction m with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, pow_succ]
      omega
  have ht := hsum n
  omega

theorem code_mem {n r : ℕ} {S : Finset ℕ} (hc : S.card = r) (hS : ∀ i ∈ S, i < n) :
    blockCode S ∈ smallSets n r :=
  mem_smallSets.mpr ⟨code_bounded hS, by simpa using hc⟩

def contained (t b : ℕ) : Bool := t.bitIndices.all (fun i => b.testBit i)

@[simp] theorem contained_iff {t b : ℕ} :
    contained t b = true ↔ pointSet t ⊆ pointSet b := by
  simp only [contained, List.all_eq_true, subset_iff, mem_pointSet, Nat.mem_bitIndices]

def separated (b c : ℕ) : Bool := (b &&& c).bitIndices.length < 3

@[simp] theorem separated_iff {b c : ℕ} :
    separated b c = true ↔ (pointSet b ∩ pointSet c).card < 3 := by
  have he : pointSet (b &&& c) = pointSet b ∩ pointSet c := by
    ext i
    simp [Nat.testBit_and]
  simp [separated, ← card_pointSet, he]

def QSystem (n : ℕ) (D : Set ℕ) : Prop :=
  (∀ b ∈ D, b ∈ smallSets n 4) ∧
    ∀ t ∈ smallSets n 3, ∃! b, b ∈ D ∧ contained t b = true

theorem separated_of_system {n b c : ℕ} {D : Set ℕ} (h : QSystem n D)
    (hb : b ∈ D) (hc : c ∈ D) (hne : b ≠ c) : separated b c = true := by
  apply separated_iff.mpr
  by_contra! hbig
  obtain ⟨T,hT,hcard⟩ := exists_subset_card_eq hbig
  have hBt := (mem_smallSets.mp (h.1 b hb)).1
  have ht : blockCode T ∈ smallSets n 3 := code_mem hcard (fun i hi =>
    points_bounded hBt (mem_inter.mp (hT hi)).1)
  have hTb : contained (blockCode T) b = true := contained_iff.mpr
    (by rw [pointSet_blockCode]; exact hT.trans inter_subset_left)
  have hTc : contained (blockCode T) c = true := contained_iff.mpr
    (by rw [pointSet_blockCode]; exact hT.trans inter_subset_right)
  obtain ⟨d,_,hd⟩ := h.2 _ ht
  exact hne ((hd b ⟨hb,hTb⟩).trans (hd c ⟨hc,hTc⟩).symm)

theorem code_insert {i : ℕ} {S : Finset ℕ} (hi : i ∉ S) :
    blockCode (insert i S) = blockCode S + 2^i := by
  change (∑ j ∈ insert i S, 2^j) = (∑ j ∈ S, 2^j) + 2^i
  rw [sum_insert hi, Nat.add_comm]

def choices (n t : ℕ) (chosen : List ℕ) : List ℕ :=
  ((List.range n).filterMap fun i =>
    if t.testBit i then none else some (t + 2^i)).filter
      (fun b => chosen.all (separated b))

theorem mem_choices_of_block {n t b : ℕ} {chosen : List ℕ}
    (ht : t ∈ smallSets n 3) (hb : b ∈ smallSets n 4)
    (hsub : contained t b = true) (hsep : chosen.all (separated b) = true) :
    b ∈ choices n t chosen := by
  have hs := contained_iff.mp hsub
  have hcard : ((pointSet b) \ pointSet t).card = 1 := by
    rw [card_sdiff_of_subset hs, (mem_smallSets.mp hb).2, (mem_smallSets.mp ht).2]
  obtain ⟨i,hi⟩ := card_eq_one.mp hcard
  have hib : i ∈ pointSet b := (mem_sdiff.mp (by rw [hi]; exact mem_singleton_self _)).1
  have hit : i ∉ pointSet t := (mem_sdiff.mp (by rw [hi]; exact mem_singleton_self _)).2
  have hset : insert i (pointSet t) = pointSet b := by
    apply Subset.antisymm (insert_subset hib hs)
    intro j hj
    by_cases h : j ∈ pointSet t
    · exact mem_insert_of_mem h
    · have he : j ∈ pointSet b \ pointSet t := mem_sdiff.mpr ⟨hj,h⟩
      rw [hi,mem_singleton] at he
      subst j
      exact mem_insert_self _ _
  have he : t + 2^i = b := by
    rw [← blockCode_pointSet t,← code_insert hit,hset,blockCode_pointSet]
  apply List.mem_filter.mpr
  refine ⟨List.mem_filterMap.mpr ⟨i,List.mem_range.mpr (points_bounded (mem_smallSets.mp hb).1 hib),?_⟩,hsep⟩
  have hitb : t.testBit i = false := Bool.eq_false_of_not_eq_true (fun H => hit (mem_pointSet.mpr H))
  simp [hitb,he]

/-- Each row asks which block covers a particular still-uncovered triple. -/
inductive Split where
  | leaf
  | branch (triple : ℕ) (children : List (ℕ × Split))
deriving Inhabited

def extendSearch (n : ℕ) : ℕ → Split → List ℕ → Option (List (List ℕ))
  | 0, _, _ => none
  | _+1, .leaf, chosen => some [chosen]
  | fuel+1, .branch t children, chosen =>
    if (t < 2^n && t.bitIndices.length == 3) &&
        !(chosen.any (contained t)) &&
        (choices n t chosen).all (fun b => (children.lookup b).isSome) then
      ((choices n t chosen).mapM (fun b =>
        extendSearch n fuel ((children.lookup b).getD .leaf) (b::chosen))).map List.flatten
    else none

theorem some_path_complete {n : ℕ} {D : Set ℕ} (hD : QSystem n D) (tree : Split)
    {fuel : ℕ} {chosen : List ℕ} {outputs : List (List ℕ)}
    (hin : ∀ b ∈ chosen, b ∈ D)
    (h : extendSearch n fuel tree chosen = some outputs) :
    ∃ selection ∈ outputs, ∀ b ∈ selection, b ∈ D := by
  induction fuel generalizing tree chosen outputs with
  | zero => simp [extendSearch] at h
  | succ fuel ih =>
    cases tree with
    | leaf =>
      cases Option.some.inj h
      exact ⟨chosen,by simp,hin⟩
    | branch t children =>
      rw [extendSearch] at h
      split at h
      next hg =>
        have ht : t ∈ smallSets n 3 := by
          have hh := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hg).1).1
          simpa using hh
        have huncovered : ∀ b ∈ chosen, contained t b ≠ true := by
          have hh := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hg).1).2
          simpa [List.any_eq_false] using hh
        obtain ⟨b,⟨hb,hbt⟩,huniq⟩ := hD.2 t ht
        have hbc : b ∈ choices n t chosen := by
          apply mem_choices_of_block ht (hD.1 b hb) hbt
          apply List.all_eq_true.mpr
          intro c hc
          have hne : b ≠ c := by
            intro he
            rw [he] at hbt
            exact huncovered c hc hbt
          exact separated_of_system hD hb (hin c hc) hne
        -- Pull the branch result for the block selected by the actual system.
        generalize hMap : (choices n t chosen).mapM (fun a =>
          extendSearch n fuel ((children.lookup a).getD .leaf) (a::chosen)) = result at h
        cases result with
        | none => simp at h
        | some lists =>
          have out : List.flatten lists = outputs := Option.some.inj h
          have find {α β : Type} {L : List α} {f : α → Option β} {res : List β}
              (h : L.mapM f = some res) {a : α} (ha : a ∈ L) :
              ∃ v ∈ res, f a = some v := by
            induction L generalizing res with
            | nil => simp at ha
            | cons x L ih =>
              simp only [List.mapM_cons] at h
              cases hx : f x with
              | none => simp [hx] at h
              | some y =>
                cases ht : L.mapM f with
                | none => simp [hx,ht] at h
                | some ys =>
                  simp [hx,ht] at h
                  subst res
                  rcases List.mem_cons.mp ha with rfl | hrest
                  · exact ⟨y,by simp,hx⟩
                  · obtain ⟨v,hv,hf⟩ := ih ht hrest
                    exact ⟨v,by simp [hv],hf⟩
          obtain ⟨res,hres,hr⟩ := find hMap hbc
          obtain ⟨selection, hs, hsubset⟩ := ih _ (fun a ha =>
            (List.mem_cons.mp ha).elim (fun e => e.symm ▸ hb) (hin a)) hr
          exact ⟨selection,out ▸ List.mem_flatten.mpr ⟨res,hres,hs⟩,hsubset⟩
      next => contradiction

def subtriples (b : ℕ) : List ℕ :=
  b.bitIndices.map (fun i => b - 2^i)

theorem subtriples_contained {t b : ℕ} (h : t ∈ subtriples b) :
    contained t b = true := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
  have hi' : i ∈ pointSet b := mem_pointSet.mpr (Nat.mem_bitIndices.mp hi)
  have hc : blockCode ((pointSet b).erase i) + 2^i = b := by
    change (∑ j ∈ (pointSet b).erase i, 2^j) + 2^i = b
    rw [sum_erase_add _ _ hi']
    exact blockCode_pointSet b
  have he : b - 2^i = blockCode ((pointSet b).erase i) := by omega
  exact contained_iff.mpr (by rw [he,pointSet_blockCode]; exact erase_subset _ _)

def allCovered (n : ℕ) (selection : List ℕ) : Bool :=
  (selection.flatMap subtriples).insertionSort (· ≤ ·) == smallSets n 3

theorem allCovered_sound {n t : ℕ} {L : List ℕ} (h : allCovered n L = true)
    (ht : t ∈ smallSets n 3) : ∃ a ∈ L, contained t a = true := by
  have he := eq_of_beq h
  have hmem : t ∈ (L.flatMap subtriples).insertionSort (· ≤ ·) := he ▸ ht
  obtain ⟨a,ha,hta⟩ := List.mem_flatMap.mp ((List.mem_insertionSort (· ≤ ·)).mp hmem)
  exact ⟨a,ha,subtriples_contained hta⟩

theorem eq_of_covered_path {n : ℕ} {S : Set ℕ} (hS : QSystem n S)
    {L : List ℕ} (hL : ∀ b ∈ L, b ∈ S) (hC : allCovered n L = true) :
    S = {b | b ∈ L} := by
  ext b
  constructor
  · intro hb
    obtain ⟨hbnd,hcard⟩ := mem_smallSets.mp (hS.1 b hb)
    obtain ⟨T,hT,hc⟩ := exists_subset_card_eq (show 3 ≤ (pointSet b).card by omega)
    have ht := code_mem hc (fun i hi => points_bounded hbnd (hT hi))
    have hcB : contained (blockCode T) b = true := contained_iff.mpr (by simpa using hT)
    obtain ⟨a,ha,hTa⟩ := allCovered_sound hC ht
    obtain ⟨c,_,hc⟩ := hS.2 _ ht
    have hab := (hc a ⟨hL a ha,hTa⟩).trans (hc b ⟨hb,hcB⟩).symm
    exact hab ▸ ha
  · exact hL b

/-- A permutation and its inverse on the initial interval; the lists are concrete certificate data. -/
structure PermWord where
  forward : List ℕ
  backward : List ℕ

def PermWord.f (p : PermWord) (i : ℕ) : ℕ := p.forward[i]?.getD i

def PermWord.g (p : PermWord) (i : ℕ) : ℕ := p.backward[i]?.getD i

def PermWord.good (n : ℕ) (p : PermWord) : Bool :=
  (List.range n).all fun i =>
    decide (p.f i < n ∧ p.g i < n ∧ p.f (p.g i) = i ∧ p.g (p.f i) = i)

theorem PermWord.spec {n : ℕ} {p : PermWord} (hp : p.good n = true) {i : ℕ} (hi : i < n) :
    p.f i < n ∧ p.g i < n ∧ p.f (p.g i) = i ∧ p.g (p.f i) = i := by
  simpa using (List.all_eq_true.mp hp i (List.mem_range.mpr hi))

def PermWord.symm (p : PermWord) : PermWord := ⟨p.backward,p.forward⟩

theorem PermWord.good_symm {n : ℕ} {p : PermWord} (hp : p.good n = true) :
    p.symm.good n = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have H := p.spec hp (List.mem_range.mp hi)
  exact decide_eq_true (show p.g i < n ∧ p.f i < n ∧ p.g (p.f i) = i ∧ p.f (p.g i) = i from
    ⟨H.2.1,H.1,H.2.2.2,H.2.2.1⟩)

def addPoint (i b : ℕ) : ℕ := if b.testBit i then b else b + 2^i

theorem pointSet_addPoint (i b : ℕ) : pointSet (addPoint i b) = insert i (pointSet b) := by
  unfold addPoint
  split
  next h => rw [insert_eq_of_mem (mem_pointSet.mpr h)]
  next h =>
    have hi : i ∉ pointSet b := fun hp => h (mem_pointSet.mp hp)
    have he := code_insert hi
    rw [blockCode_pointSet] at he
    rw [← he,pointSet_blockCode]

def imageCode (f : ℕ → ℕ) : List ℕ → ℕ
  | [] => 0
  | i::is => addPoint (f i) (imageCode f is)

theorem pointSet_imageCode (f : ℕ → ℕ) (is : List ℕ) :
    pointSet (imageCode f is) = is.toFinset.image f := by
  induction is with
  | nil => simp [imageCode,pointSet,Finset.equivBitIndices]
  | cons i is ih => rw [imageCode,pointSet_addPoint,ih,List.toFinset_cons,image_insert]

def rename (f : ℕ → ℕ) (b : ℕ) : ℕ := imageCode f b.bitIndices

@[simp] theorem pointSet_rename (f : ℕ → ℕ) (b : ℕ) : pointSet (rename f b) = (pointSet b).image f :=
  pointSet_imageCode f b.bitIndices

theorem rename_eq (f : ℕ → ℕ) (b : ℕ) : rename f b = blockCode ((pointSet b).image f) := by
  rw [← pointSet_rename,blockCode_pointSet]

theorem rename_bounded {n b : ℕ} {p : PermWord} (hp : p.good n = true) (hb : b < 2^n) :
    rename p.f b < 2^n := by
  rw [rename_eq]
  apply code_bounded
  intro i hi
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
  exact (p.spec hp (points_bounded hb hj)).1

theorem rename_leftInv {n b : ℕ} {p : PermWord} (hp : p.good n = true) (hb : b < 2^n) :
    rename p.g (rename p.f b) = b := by
  rw [rename_eq,pointSet_rename,image_image]
  have H : (pointSet b).image (p.g ∘ p.f) = pointSet b := by
    rw [show (pointSet b).image (p.g ∘ p.f) = (pointSet b).image id from
      image_congr (fun i hi => (p.spec hp (points_bounded hb hi)).2.2.2), image_id]
  rw [H,blockCode_pointSet]

theorem rename_rightInv {n b : ℕ} {p : PermWord} (hp : p.good n = true) (hb : b < 2^n) :
    rename p.f (rename p.g b) = b :=
  rename_leftInv (p := p.symm) (PermWord.good_symm hp) hb

theorem rename_injective {n b c : ℕ} {p : PermWord} (hp : p.good n = true)
    (hb : b < 2^n) (hc : c < 2^n) (he : rename p.f b = rename p.f c) : b = c := by
  simpa [rename_leftInv hp hb, rename_leftInv hp hc] using congrArg (rename p.g) he

theorem rename_smallSets {n b k : ℕ} {p : PermWord} (hp : p.good n = true) (hb : b ∈ smallSets n k) :
    rename p.f b ∈ smallSets n k := by
  obtain ⟨hbound,hcard⟩ := mem_smallSets.mp hb
  refine mem_smallSets.mpr ⟨rename_bounded hp hbound,?_⟩
  rw [pointSet_rename,card_image_of_injOn ?_,hcard]
  intro i hi j hj hij
  have h₁ := (p.spec hp (points_bounded hbound hi)).2.2.2
  have h₂ := (p.spec hp (points_bounded hbound hj)).2.2.2
  rw [hij] at h₁
  exact h₁.symm.trans h₂

theorem rename_contained {n b t : ℕ} {p : PermWord} (hp : p.good n = true)
    (hb : b < 2^n) (ht : t < 2^n) :
    contained (rename p.f t) (rename p.f b) = true ↔ contained t b = true := by
  rw [contained_iff,contained_iff,pointSet_rename,pointSet_rename]
  constructor
  · intro h i hi
    obtain ⟨j,hj,hji⟩ := mem_image.mp (h (mem_image_of_mem _ hi))
    have h₁ := (p.spec hp (points_bounded hb hj)).2.2.2
    have h₂ := (p.spec hp (points_bounded ht hi)).2.2.2
    rw [hji] at h₁
    exact (h₁.symm.trans h₂) ▸ hj
  · intro h
    exact image_mono _ h

def renameFamily (f : ℕ → ℕ) (D : Set ℕ) : Set ℕ := rename f '' D

theorem rename_system {n : ℕ} {p : PermWord} (hp : p.good n = true) {D : Set ℕ} (hD : QSystem n D) :
    QSystem n (renameFamily p.f D) := by
  constructor
  · rintro b ⟨a,ha,rfl⟩
    exact rename_smallSets hp (hD.1 a ha)
  · intro t ht
    have htBound := (mem_smallSets.mp ht).1
    have ht' : rename p.g t ∈ smallSets n 3 := rename_smallSets (p := p.symm) (PermWord.good_symm hp) ht
    have hrename : rename p.f (rename p.g t) = t := rename_rightInv hp htBound
    obtain ⟨a,⟨ha,hta⟩,hu⟩ := hD.2 _ ht'
    have htb : contained t (rename p.f a) = true := by
      rw [← hrename,rename_contained hp (mem_smallSets.mp (hD.1 a ha)).1 (mem_smallSets.mp ht').1]
      exact hta
    refine ⟨rename p.f a,⟨⟨a,ha,rfl⟩,htb⟩,?_⟩
    rintro b ⟨⟨c,hc,rfl⟩,htc⟩
    have H := (rename_contained hp (mem_smallSets.mp (hD.1 c hc)).1 (mem_smallSets.mp ht').1).mp
      (hrename.symm ▸ htc)
    exact congrArg (rename p.f) (hu c ⟨hc,H⟩)

theorem rename_disjoint {n : ℕ} {p : PermWord} (hp : p.good n = true)
    {A B : Set ℕ} (hA : QSystem n A) (hB : QSystem n B) (hdis : Disjoint A B) :
    Disjoint (renameFamily p.f A) (renameFamily p.f B) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨a,ha,haq⟩ ⟨b,hb,hbq⟩
  have h := rename_injective hp (mem_smallSets.mp (hA.1 a ha)).1
    (mem_smallSets.mp (hB.1 b hb)).1 (haq.trans hbq.symm)
  exact Set.disjoint_left.mp hdis (h ▸ ha) hb

theorem rename_family_list (f : ℕ → ℕ) (L : List ℕ) :
    renameFamily f {b | b ∈ L} = {b | b ∈ L.map (rename f)} := by
  ext b
  simp [renameFamily,List.mem_map]

theorem rename_cancel {n : ℕ} {p : PermWord} (hp : p.good n = true)
    {D : Set ℕ} (hD : QSystem n D) :
    renameFamily p.g (renameFamily p.f D) = D := by
  ext b
  simp only [renameFamily, Set.mem_image]
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,e⟩
    rw [rename_leftInv hp (mem_smallSets.mp (hD.1 a ha)).1] at e
    exact e ▸ ha
  · intro hb
    exact ⟨_,⟨b,hb,rfl⟩,rename_leftInv hp (mem_smallSets.mp (hD.1 b hb)).1⟩

def firstCommon : ℕ → List ℕ → List ℕ → Bool
  | fuel+1, a::as, b::bs =>
    if a = b then true
    else if a < b then firstCommon fuel as (b::bs)
    else firstCommon fuel (a::as) bs
  | _, _, _ => false

theorem firstCommon_sound {fuel : ℕ} {A B : List ℕ} (h : firstCommon fuel A B = true) :
    ∃ x, x ∈ A ∧ x ∈ B := by
  induction fuel generalizing A B with
  | zero => simp [firstCommon] at h
  | succ fuel ih =>
    cases A with
    | nil => simp [firstCommon] at h
    | cons a as =>
      cases B with
      | nil => simp [firstCommon] at h
      | cons b bs =>
        simp only [firstCommon] at h
        split at h
        next hab => subst b; exact ⟨a,by simp,by simp⟩
        next =>
          split at h
          next =>
            obtain ⟨x,hx,hy⟩ := ih h
            exact ⟨x,List.mem_cons_of_mem _ hx,hy⟩
          next =>
            obtain ⟨x,hx,hy⟩ := ih h
            exact ⟨x,hx,List.mem_cons_of_mem _ hy⟩

def mutuallyDisjoint (A B : List ℕ) : Bool := !firstCommon (A.length + B.length) A B

theorem disjoint_bool {A B : List ℕ}
    (h : Disjoint {b | b ∈ A} ({b | b ∈ B} : Set ℕ)) :
    mutuallyDisjoint A B = true := by
  suffices firstCommon (A.length + B.length) A B = false by simp [mutuallyDisjoint,this]
  apply Bool.eq_false_of_not_eq_true
  intro hc
  obtain ⟨x,hA,hB⟩ := firstCommon_sound hc
  exact Set.disjoint_left.mp h hA hB

/-- Iterate over each possible first choice with the suffix following it. -/
def firstChoice {α : Type} (p : α → List α → Bool) : List α → Bool
  | [] => false
  | a::as => p a as || firstChoice p as

def packSearch : ℕ → List (List ℕ) → Bool
  | 0, _ => true
  | k+1, L => firstChoice (fun A tail =>
    packSearch k (tail.filter (mutuallyDisjoint A))) L

theorem firstChoice_select {α : Type} [DecidableEq α] {T : Finset α} (hT : T.Nonempty)
    {L : List α} (hsub : ∀ a ∈ T, a ∈ L) {p : α → List α → Bool}
    (hp : ∀ a ∈ T, ∀ R : List α, (∀ b ∈ T.erase a, b ∈ R) → p a R = true) :
    firstChoice p L = true := by
  induction L with
  | nil =>
    obtain ⟨a,ha⟩ := hT
    exact False.elim (List.not_mem_nil (hsub a ha))
  | cons a as ih =>
    rw [firstChoice]
    by_cases h : a ∈ T
    · have hrest (b : α) (hb : b ∈ T.erase a) : b ∈ as :=
        (List.mem_cons.mp (hsub b (mem_erase.mp hb).2)).resolve_left (mem_erase.mp hb).1
      simp [hp a h as hrest]
    · have hrest (b : α) (hb : b ∈ T) : b ∈ as :=
        (List.mem_cons.mp (hsub b hb)).resolve_left fun eq => h (eq ▸ hb)
      simp [ih hrest]

theorem packing_sound {k : ℕ} {L : List (List ℕ)} {T : Finset (List ℕ)}
    (hc : T.card = k) (hsub : ∀ A ∈ T, A ∈ L)
    (hsep : (T : Set (List ℕ)).Pairwise (fun A B => mutuallyDisjoint A B = true)) :
    packSearch k L = true := by
  induction k generalizing L T with
  | zero => rfl
  | succ k ih =>
    rw [packSearch]
    apply firstChoice_select (card_pos.mp (by omega)) hsub
    intro A hA R hR
    apply ih (T := T.erase A)
    · rw [card_erase_of_mem hA,hc]
      omega
    · intro B hB
      exact List.mem_filter.mpr ⟨hR B hB,hsep hA (mem_erase.mp hB).2 (mem_erase.mp hB).1.symm⟩
    · exact hsep.mono (coe_subset.mpr (erase_subset _ _))

structure ProofTables where
  seeds : List ℕ
  matchSearch : Split
  matchWords : List (List ℕ × PermWord)
  normSearch : Split
  normWords : List (List ℕ × PermWord)
  canonical : List ℕ

  prunes : Array (Array ℕ)

/-- A hint may discard a candidate only if it exhibits a block in common
with the canonical system. -/
def prune (C : ProofTables) (m q : List ℕ × PermWord) (i j : ℕ) : Bool :=
  let b := ((C.prunes[i]?.getD #[])[j]?).getD 0
  q.1.contains b && C.canonical.contains (rename m.2.f b)

def shortlist (C : ProofTables) : List (List ℕ) :=
  C.matchWords.zipIdx.flatMap fun (m,i) =>
    C.normWords.zipIdx.filterMap fun (q,j) =>
      if prune C m q i j then none else some ((q.1.map (rename m.2.f)).insertionSort (· ≤ ·))

theorem shortlist_complete {C : ProofTables} {m q : List ℕ × PermWord}
    (hm : m ∈ C.matchWords) (hq : q ∈ C.normWords)
    (hd : Disjoint {b | b ∈ C.canonical} ({b | b ∈ q.1.map (rename m.2.f)} : Set ℕ)) :
    (q.1.map (rename m.2.f)).insertionSort (· ≤ ·) ∈ shortlist C := by
  obtain ⟨i,hi⟩ : ∃ i, (m,i) ∈ C.matchWords.zipIdx := by
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
    exact ⟨i,List.mem_iff_getElem.mpr ⟨i,by simpa using hi,by simp [List.getElem_zipIdx,he]⟩⟩
  obtain ⟨j,hj⟩ : ∃ j, (q,j) ∈ C.normWords.zipIdx := by
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hq
    exact ⟨j,List.mem_iff_getElem.mpr ⟨j,by simpa using hj,by simp [List.getElem_zipIdx,he]⟩⟩
  have hp : prune C m q i j = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp h
    let b := ((C.prunes[i]?.getD #[])[j]?).getD 0
    exact Set.disjoint_left.mp hd (by simpa using h₂ : rename m.2.f b ∈ C.canonical)
      (List.mem_map.mpr ⟨b,by simpa using h₁,rfl⟩)
  apply List.mem_flatMap.mpr
  refine ⟨(m,i),hi,List.mem_filterMap.mpr ⟨(q,j),hj,?_⟩⟩
  simp [hp]

structure ValidTables (n : ℕ) (C : ProofTables) : Prop where
  canonicalBounded : C.canonical.all (fun b => b < 2^n) = true
  seedsBounded : C.seeds.all (fun b => b < 2^n) = true
  matchEnumerate :
    extendSearch n 32 C.matchSearch [] = some (C.matchWords.map Prod.fst)
  matchGood : C.matchWords.all (fun r => r.2.good n &&
    (C.seeds.map (rename r.2.f)).all r.1.contains) = true
  normEnumerate :
    extendSearch n 32 C.normSearch C.seeds = some (C.normWords.map Prod.fst)
  normGood : C.normWords.all (fun r => r.2.good n && allCovered n r.1 &&
    (r.1.insertionSort (· ≤ ·) == (C.canonical.map (rename r.2.f)).insertionSort (· ≤ ·))) = true

theorem complete_tables {n : ℕ} {C : ProofTables} (hc : ValidTables n C) {D : Set ℕ}
    (hD : QSystem n D) :
    ∃ m ∈ C.matchWords, ∃ q ∈ C.normWords,
      m.2.good n = true ∧ q.2.good n = true ∧
      D = {b | b ∈ q.1.map (rename m.2.f)} ∧
      {b | b ∈ q.1} = renameFamily q.2.f {b | b ∈ C.canonical} := by
  obtain ⟨M,hM,hMsub⟩ := some_path_complete hD C.matchSearch
    (by simp : ∀ b ∈ ([] : List ℕ), b ∈ D) hc.matchEnumerate
  obtain ⟨m,hm,hmM⟩ := List.mem_map.mp hM
  subst M
  have hg := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hc.matchGood m hm)
  have hN := rename_system (PermWord.good_symm hg.1) hD
  have hinit (a : ℕ) (ha : a ∈ C.seeds) : a ∈ renameFamily m.2.g D := by
    have H := List.all_eq_true.mp hg.2 _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
    have H' := hMsub _ (by simpa using H)
    have hBound : a < 2^n := of_decide_eq_true (List.all_eq_true.mp hc.seedsBounded a ha)
    exact ⟨rename m.2.f a,H',rename_leftInv hg.1 hBound⟩
  obtain ⟨Q,hQ,hQsub⟩ := some_path_complete hN C.normSearch hinit hc.normEnumerate
  obtain ⟨q,hq,hqQ⟩ := List.mem_map.mp hQ
  subst Q
  have hqg := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hc.normGood q hq)).1
  have hqiso := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hc.normGood q hq)).2
  have H := eq_of_covered_path hN hQsub hqg.2
  refine ⟨m,hm,q,hq,hg.1,hqg.1,?_,?_⟩
  · have h := congrArg (renameFamily m.2.f) H
    have Hcancel : renameFamily m.2.f (renameFamily m.2.g D) = D :=
      rename_cancel (p := m.2.symm) (PermWord.good_symm hg.1) hD
    change renameFamily m.2.f (renameFamily m.2.g D) = _ at h
    rw [Hcancel,rename_family_list] at h
    exact h
  · rw [rename_family_list]
    have iso := eq_of_beq hqiso
    ext b
    simpa only [Set.mem_ofPred_eq,List.mem_insertionSort] using Iff.of_eq (congrArg (fun s : List ℕ => b ∈ s) iso)

theorem rename_cancel_bounded {n : ℕ} {p : PermWord} (hp : p.good n = true)
    {D : Set ℕ} (hD : ∀ b ∈ D, b < 2^n) :
    renameFamily p.g (renameFamily p.f D) = D := by
  ext b
  simp only [renameFamily, Set.mem_image]
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,e⟩
    rw [rename_leftInv hp (hD a ha)] at e
    exact e ▸ ha
  · intro hb
    exact ⟨_,⟨b,hb,rfl⟩,rename_leftInv hp (hD b hb)⟩

theorem no_pack_of_tables {n l : ℕ} {C : ProofTables} (hc : ValidTables n C)
    (hno : packSearch l (shortlist C) = false) (ht : 7 ∈ smallSets n 3)
    (F : Fin (l+1) → Set ℕ) (hF : ∀ b, QSystem n (F b))
    (hdis : Pairwise (fun i j => Disjoint (F i) (F j))) : False := by
  classical
  obtain ⟨m0,hm0,q0,hq0,hmg,hqg,hF0,hqIso⟩ := complete_tables hc (hF 0)
  let G (i : Fin (l+1)) := renameFamily q0.2.g (renameFamily m0.2.g (F i))
  have hM (i : Fin (l+1)) : QSystem n (renameFamily m0.2.g (F i)) :=
    rename_system (p := m0.2.symm) (PermWord.good_symm hmg) (hF i)
  have hG (i) : QSystem n (G i) :=
    rename_system (p := q0.2.symm) (PermWord.good_symm hqg) (hM i)
  have hGdis : Pairwise (fun i j => Disjoint (G i) (G j)) := by
    intro i j hij
    exact rename_disjoint (p := q0.2.symm) (PermWord.good_symm hqg) (hM i) (hM j)
      (rename_disjoint (p := m0.2.symm) (PermWord.good_symm hmg) (hF i) (hF j) (hdis hij))
  have hcanon : G 0 = {b | b ∈ C.canonical} := by
    have hFR : F 0 = renameFamily m0.2.f {b | b ∈ q0.1} := by
      rw [rename_family_list,hF0]
    have hQBound (b) (hb : b ∈ ({b | b ∈ q0.1} : Set ℕ)) : b < 2^n := by
      rw [hqIso] at hb
      obtain ⟨a,ha,rfl⟩ := hb
      exact rename_bounded hqg (of_decide_eq_true (List.all_eq_true.mp hc.canonicalBounded a ha))
    unfold G
    rw [hFR,rename_cancel_bounded hmg hQBound,hqIso,rename_cancel_bounded hqg]
    intro b hb
    exact of_decide_eq_true (List.all_eq_true.mp hc.canonicalBounded b hb)
  have chooseRep (i : Fin l) : ∃ A ∈ shortlist C, G i.succ = {b | b ∈ A} := by
    obtain ⟨m,hm,q,hq,hmGood,hqGood,hEq,_⟩ := complete_tables hc (hG i.succ)
    have disj : Disjoint (G 0) (G i.succ) := hGdis (Ne.symm (Fin.succ_ne_zero i))
    rw [hcanon,hEq] at disj
    exact ⟨_,shortlist_complete hm hq disj,by simpa only [List.mem_insertionSort] using hEq⟩
  choose L hL hEq using chooseRep
  have hInj : Function.Injective L := by
    intro i j h
    by_contra! hne
    obtain ⟨b,⟨hb,_⟩,_⟩ := (hG i.succ).2 7 ht
    have hEqSet : G i.succ = G j.succ := by rw [hEq i,hEq j,h]
    exact Set.disjoint_left.mp (hGdis (fun e => hne (Fin.succ_injective _ e))) hb
      (hEqSet ▸ hb)
  let E : Fin l ↪ List ℕ := ⟨L,hInj⟩
  let T := Finset.univ.map E
  have hcT : T.card = l := by simp [T]
  have hsub (A : List ℕ) (hA : A ∈ T) : A ∈ shortlist C := by
    obtain ⟨i,_,rfl⟩ := mem_map.mp hA
    exact hL i
  have hsep : (T : Set (List ℕ)).Pairwise (fun A B => mutuallyDisjoint A B = true) := by
    intro A hA B hB hne
    obtain ⟨i,_,rfl⟩ := mem_map.mp hA
    obtain ⟨j,_,rfl⟩ := mem_map.mp hB
    have hh : Disjoint (G i.succ) (G j.succ) := hGdis (show i.succ ≠ j.succ from fun e => hne (congrArg E (Fin.succ_injective _ e)))
    rw [hEq i,hEq j] at hh
    exact disjoint_bool hh
  exact Bool.false_ne_true (hno ▸ packing_sound hcT hsub hsep)

abbrev Vertices (n m : ℕ) := {S : Finset (Fin n) // S.card = m}

theorem extend_colors {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (c : (SimpleGraph.johnson n m).Coloring (Fin (n-m+1)))
    (T : Finset (Fin n)) (hT : T.card = m-1) (a : Fin (n-m+1)) :
    ∃! A : Vertices n m, T ⊆ A.1 ∧ c A = a := by
  classical
  let R : Finset (Fin n) := univ \ T
  let ext (x : R) : Vertices n m := ⟨insert x.1 T,by
    rw [card_insert_of_notMem (mem_sdiff.mp x.2).2,hT]
    omega⟩
  have adj (A B : Vertices n m) (hA : T ⊆ A.1) (hB : T ⊆ B.1) (hne : A ≠ B) :
      (SimpleGraph.johnson n m).Adj A B := by
    apply johnson_adj_iff_ge.mpr
    have hcard := card_le_card (subset_inter hA hB)
    exact ⟨hne,by omega⟩
  have hIj : Function.Injective (fun x : R => c (ext x)) := by
    intro x y he
    by_contra hn
    have hne : ext x ≠ ext y := by
      intro e
      have hmem : x.1 ∈ (ext y).1 := e ▸ mem_insert_self _ _
      have hxy := (mem_insert.mp hmem).resolve_right (mem_sdiff.mp x.2).2
      exact hn (Subtype.ext hxy)
    exact (c.valid (adj _ _ (subset_insert _ _) (subset_insert _ _) hne)) he
  have hR : Fintype.card R = Fintype.card (Fin (n-m+1)) := by
    simp [R,hT]
    omega
  have hSurj := ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hIj,hR⟩).2
  obtain ⟨x,hx⟩ := hSurj a
  refine ⟨ext x,⟨subset_insert _ _,hx⟩,?_⟩
  rintro B ⟨hB,hBa⟩
  by_contra hne
  exact (c.valid (adj _ _ hB (subset_insert _ _) hne)) (hBa.trans hx.symm)

theorem design_divisibility {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (c : (SimpleGraph.johnson n m).Coloring (Fin (n-m+1))) :
    m ∣ n.choose (m-1) := by
  classical
  let a : Fin (n-m+1) := ⟨0,by omega⟩
  let D : Finset (Vertices n m) := univ.filter (fun A => c A = a)
  let f (A : Vertices n m) := A.1.powersetCard (m-1)
  have hAll : D.biUnion f = (univ : Finset (Fin n)).powersetCard (m-1) := by
    ext T
    constructor
    · intro h
      obtain ⟨A,hA,hT⟩ := mem_biUnion.mp h
      exact mem_powersetCard.mpr ⟨subset_univ _,(mem_powersetCard.mp hT).2⟩
    · intro h
      obtain ⟨A,⟨hTA,hAc⟩,_⟩ := extend_colors hm hmn c T (mem_powersetCard.mp h).2 a
      exact mem_biUnion.mpr ⟨A,mem_filter.mpr ⟨mem_univ _,hAc⟩,
        mem_powersetCard.mpr ⟨hTA,(mem_powersetCard.mp h).2⟩⟩
  have hDis : (D : Set (Vertices n m)).PairwiseDisjoint f := by
    intro A hA B hB hAB
    apply Finset.disjoint_left.mpr
    intro T hTA hTB
    have hcard := (mem_powersetCard.mp hTA).2
    obtain ⟨K,_,huniq⟩ := extend_colors hm hmn c T hcard a
    exact hAB ((huniq A ⟨(mem_powersetCard.mp hTA).1,(mem_filter.mp hA).2⟩).trans
      (huniq B ⟨(mem_powersetCard.mp hTB).1,(mem_filter.mp hB).2⟩).symm)
  have h := congrArg Finset.card hAll
  rw [card_biUnion hDis, card_powersetCard,card_univ,Fintype.card_fin] at h
  have hmC : m.choose (m-1) = m := by
    rw [← Nat.choose_symm (show m-1 ≤ m by omega),show m-(m-1)=1 by omega,Nat.choose_one_right]
  simp [f,card_powersetCard,show ∀ A : Vertices n m, A.1.card = m from fun A => A.2,hmC] at h
  exact ⟨D.card,by simpa [mul_comm] using h.symm⟩

def toNatPoints (n : ℕ) : Fin n ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩

def colorsToSystems {n : ℕ} (c : (SimpleGraph.johnson n 4).Coloring (Fin (n-4+1)))
    (a : Fin (n-4+1)) : Set ℕ :=
  {b | ∃ A : Vertices n 4, c A = a ∧ blockCode (A.1.map (toNatPoints n)) = b}

theorem codes_to_system {n : ℕ} (h4 : 4 ≤ n)
    (c : (SimpleGraph.johnson n 4).Coloring (Fin (n-4+1))) (a : Fin (n-4+1)) :
    QSystem n (colorsToSystems c a) := by
  classical
  constructor
  · rintro b ⟨A,hA,rfl⟩
    exact code_mem (by simp [A.2]) (fun i hi => by
      obtain ⟨x,_,rfl⟩ := mem_map.mp hi
      exact x.isLt)
  · intro t ht
    let T : Finset (Fin n) := univ.filter (fun i => i.val ∈ pointSet t)
    have hMap : T.map (toNatPoints n) = pointSet t := by
      ext x
      constructor
      · intro h
        obtain ⟨i,hi,rfl⟩ := mem_map.mp h
        exact (mem_filter.mp hi).2
      · intro hx
        have hn := points_bounded (mem_smallSets.mp ht).1 hx
        exact mem_map.mpr ⟨⟨x,hn⟩,mem_filter.mpr ⟨mem_univ _,hx⟩,rfl⟩
    have hcard : T.card = 4-1 := by
      rw [← card_map (f := toNatPoints n),hMap]
      exact (mem_smallSets.mp ht).2
    have hIncl (A : Vertices n 4) : contained t (blockCode (A.1.map (toNatPoints n))) = true ↔ T ⊆ A.1 := by
      rw [contained_iff,pointSet_blockCode,← hMap,map_subset_map]
    obtain ⟨A,⟨hTA,hAc⟩,huniq⟩ := extend_colors (by decide) h4 c T hcard a
    refine ⟨blockCode (A.1.map (toNatPoints n)),⟨⟨A,hAc,rfl⟩,(hIncl A).mpr hTA⟩,?_⟩
    rintro b ⟨⟨B,hB,rfl⟩,hTB⟩
    rw [huniq B ⟨(hIncl B).mp hTB,hB⟩]

theorem different_colors_disjoint {n : ℕ}
    (c : (SimpleGraph.johnson n 4).Coloring (Fin (n-4+1))) :
    Pairwise (fun a b => Disjoint (colorsToSystems c a) (colorsToSystems c b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  rintro x ⟨A,hA,hcodeA⟩ ⟨B,hB,hcodeB⟩
  have he : A = B := by
    apply Subtype.ext
    have hh := congrArg pointSet (hcodeA.trans hcodeB.symm)
    exact Finset.map_injective (toNatPoints n) (by simpa only [pointSet_blockCode] using hh)
  exact hab (hA.symm.trans (he.symm ▸ hB))

def vertexExtension {n m : ℕ} (r : ℕ) : SimpleGraph.johnson n m →g SimpleGraph.johnson (n+r) (m+r) := by
  classical
  let e : Fin n ↪ Fin (n+r) := Fin.castLEEmb (Nat.le_add_right n r)
  let I : Finset (Fin (n+r)) := univ \ (univ : Finset (Fin n)).map e
  have hIc : I.card = r := by simp [I,card_sdiff]
  have hdis (A : Finset (Fin n)) : Disjoint I (A.map e) := by
    apply Finset.disjoint_left.mpr
    intro i hi hA
    exact (mem_sdiff.mp hi).2 (map_subset_map.mpr (subset_univ _) hA)
  let f (A : Vertices n m) : Vertices (n+r) (m+r) := ⟨I ∪ A.1.map e,by
    rw [card_union_of_disjoint (hdis A.1),hIc,card_map,A.2,add_comm]⟩
  refine ⟨f, ?_⟩
  intro A B hAB
  change ((I ∪ A.1.map e) ∩ (I ∪ B.1.map e)).card + 1 = m+r
  change (A.1 ∩ B.1).card + 1 = m at hAB
  rw [← union_inter_distrib_left,← map_inter,card_union_of_disjoint (hdis (A.1 ∩ B.1)),
    hIc,card_map]
  omega

def tables8 : ProofTables where
  seeds := [15, 51, 195]
  matchSearch := (.branch 7 [
    (15, (.branch 19 [
      (51, (.branch 67 [
        (195, .leaf)
      ])),
      (83, (.branch 35 [
        (163, .leaf)
      ])),
      (147, (.branch 35 [
        (99, .leaf)
      ]))
    ])),
    (23, (.branch 11 [
      (43, (.branch 67 [
        (195, .leaf)
      ])),
      (75, (.branch 35 [
        (163, .leaf)
      ])),
      (139, (.branch 35 [
        (99, .leaf)
      ]))
    ])),
    (39, (.branch 11 [
      (27, (.branch 67 [
        (195, .leaf)
      ])),
      (75, (.branch 19 [
        (147, .leaf)
      ])),
      (139, (.branch 19 [
        (83, .leaf)
      ]))
    ])),
    (71, (.branch 11 [
      (27, (.branch 35 [
        (163, .leaf)
      ])),
      (43, (.branch 19 [
        (147, .leaf)
      ])),
      (139, (.branch 19 [
        (51, .leaf)
      ]))
    ])),
    (135, (.branch 11 [
      (27, (.branch 35 [
        (99, .leaf)
      ])),
      (43, (.branch 19 [
        (83, .leaf)
      ])),
      (75, (.branch 19 [
        (51, .leaf)
      ]))
    ]))
  ])
  matchWords := [
  ([195, 51, 15], ⟨[0, 1, 6, 7, 4, 5, 2, 3], [0, 1, 6, 7, 4, 5, 2, 3]⟩),
  ([163, 83, 15], ⟨[0, 1, 5, 7, 4, 6, 2, 3], [0, 1, 6, 7, 4, 2, 5, 3]⟩),
  ([99, 147, 15], ⟨[0, 1, 5, 6, 4, 7, 2, 3], [0, 1, 6, 7, 4, 2, 3, 5]⟩),
  ([195, 43, 23], ⟨[0, 1, 6, 7, 3, 5, 2, 4], [0, 1, 6, 4, 7, 5, 2, 3]⟩),
  ([163, 75, 23], ⟨[0, 1, 5, 7, 3, 6, 2, 4], [0, 1, 6, 4, 7, 2, 5, 3]⟩),
  ([99, 139, 23], ⟨[0, 1, 5, 6, 3, 7, 2, 4], [0, 1, 6, 4, 7, 2, 3, 5]⟩),
  ([195, 27, 39], ⟨[0, 1, 6, 7, 3, 4, 2, 5], [0, 1, 6, 4, 5, 7, 2, 3]⟩),
  ([147, 75, 39], ⟨[0, 1, 4, 7, 3, 6, 2, 5], [0, 1, 6, 4, 2, 7, 5, 3]⟩),
  ([83, 139, 39], ⟨[0, 1, 4, 6, 3, 7, 2, 5], [0, 1, 6, 4, 2, 7, 3, 5]⟩),
  ([163, 27, 71], ⟨[0, 1, 5, 7, 3, 4, 2, 6], [0, 1, 6, 4, 5, 2, 7, 3]⟩),
  ([147, 43, 71], ⟨[0, 1, 4, 7, 3, 5, 2, 6], [0, 1, 6, 4, 2, 5, 7, 3]⟩),
  ([51, 139, 71], ⟨[0, 1, 4, 5, 3, 7, 2, 6], [0, 1, 6, 4, 2, 3, 7, 5]⟩),
  ([99, 27, 135], ⟨[0, 1, 5, 6, 3, 4, 2, 7], [0, 1, 6, 4, 5, 2, 3, 7]⟩),
  ([83, 43, 135], ⟨[0, 1, 4, 6, 3, 5, 2, 7], [0, 1, 6, 4, 2, 5, 3, 7]⟩),
  ([51, 75, 135], ⟨[0, 1, 4, 5, 3, 6, 2, 7], [0, 1, 6, 4, 2, 3, 5, 7]⟩)]
  normSearch := (.branch 21 [
    (85, (.branch 22 [
      (150, (.branch 25 [
        (153, (.branch 26 [
          (90, (.branch 28 [
            (60, (.branch 37 [
              (165, (.branch 38 [
                (102, (.branch 41 [
                  (105, (.branch 42 [
                    (170, (.branch 76 [
                      (204, (.branch 112 [
                        (240, .leaf)
                      ]))
                    ]))
                  ]))
                ]))
              ]))
            ]))
          ]))
        ]))
      ]))
    ])),
    (149, (.branch 22 [
      (86, (.branch 25 [
        (89, (.branch 26 [
          (154, (.branch 28 [
            (60, (.branch 37 [
              (101, (.branch 38 [
                (166, (.branch 41 [
                  (169, (.branch 42 [
                    (106, (.branch 76 [
                      (204, (.branch 112 [
                        (240, .leaf)
                      ]))
                    ]))
                  ]))
                ]))
              ]))
            ]))
          ]))
        ]))
      ]))
    ]))
  ])
  normWords := [
  ([240, 204, 170, 105, 102, 165, 60, 90, 153, 150, 85, 15, 51, 195], ⟨[0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7]⟩),
  ([240, 204, 106, 169, 166, 101, 60, 154, 89, 86, 149, 15, 51, 195], ⟨[0, 1, 3, 2, 4, 5, 6, 7], [0, 1, 3, 2, 4, 5, 6, 7]⟩)]
  canonical := [240, 204, 170, 105, 102, 165, 60, 90, 153, 150, 85, 15, 51, 195]
  prunes := #[
  #[240, 240],
  #[102, 60],
  #[60, 166],
  #[240, 240],
  #[102, 0],
  #[0, 101],
  #[240, 240],
  #[0, 101],
  #[102, 0],
  #[0, 106],
  #[105, 0],
  #[240, 240],
  #[105, 0],
  #[0, 106],
  #[240, 240]]

def shortlistData8 : List (List ℕ) := [
  [23, 46, 57, 75, 92, 101, 114, 141, 154, 163, 180, 198, 209, 232],
  [23, 45, 58, 78, 89, 99, 116, 139, 156, 166, 177, 197, 210, 232],
  [29, 39, 58, 75, 86, 108, 113, 142, 147, 169, 180, 197, 216, 226],
  [30, 39, 57, 77, 83, 106, 116, 139, 149, 172, 178, 198, 216, 225],
  [27, 45, 54, 71, 92, 106, 113, 142, 149, 163, 184, 201, 210, 228],
  [30, 43, 53, 71, 89, 108, 114, 141, 147, 166, 184, 202, 212, 225],
  [27, 46, 53, 77, 86, 99, 120, 135, 156, 169, 178, 202, 209, 228],
  [29, 43, 54, 78, 83, 101, 120, 135, 154, 172, 177, 201, 212, 226]]

def tables10 : ProofTables where
  seeds := [15, 51, 195, 771]
  matchSearch := (.branch 7 [
    (15, (.branch 19 [
      (51, (.branch 67 [
        (195, (.branch 259 [
          (771, .leaf)
        ])),
        (323, (.branch 131 [
          (643, .leaf)
        ])),
        (579, (.branch 131 [
          (387, .leaf)
        ]))
      ])),
      (83, (.branch 35 [
        (163, (.branch 259 [
          (771, .leaf)
        ])),
        (291, (.branch 131 [
          (643, .leaf)
        ])),
        (547, (.branch 131 [
          (387, .leaf)
        ]))
      ])),
      (147, (.branch 35 [
        (99, (.branch 259 [
          (771, .leaf)
        ])),
        (291, (.branch 67 [
          (579, .leaf)
        ])),
        (547, (.branch 67 [
          (323, .leaf)
        ]))
      ])),
      (275, (.branch 35 [
        (99, (.branch 131 [
          (643, .leaf)
        ])),
        (163, (.branch 67 [
          (579, .leaf)
        ])),
        (547, (.branch 67 [
          (195, .leaf)
        ]))
      ])),
      (531, (.branch 35 [
        (99, (.branch 131 [
          (387, .leaf)
        ])),
        (163, (.branch 67 [
          (323, .leaf)
        ])),
        (291, (.branch 67 [
          (195, .leaf)
        ]))
      ]))
    ])),
    (23, (.branch 11 [
      (43, (.branch 67 [
        (195, (.branch 259 [
          (771, .leaf)
        ])),
        (323, (.branch 131 [
          (643, .leaf)
        ])),
        (579, (.branch 131 [
          (387, .leaf)
        ]))
      ])),
      (75, (.branch 35 [
        (163, (.branch 259 [
          (771, .leaf)
        ])),
        (291, (.branch 131 [
          (643, .leaf)
        ])),
        (547, (.branch 131 [
          (387, .leaf)
        ]))
      ])),
      (139, (.branch 35 [
        (99, (.branch 259 [
          (771, .leaf)
        ])),
        (291, (.branch 67 [
          (579, .leaf)
        ])),
        (547, (.branch 67 [
          (323, .leaf)
        ]))
      ])),
      (267, (.branch 35 [
        (99, (.branch 131 [
          (643, .leaf)
        ])),
        (163, (.branch 67 [
          (579, .leaf)
        ])),
        (547, (.branch 67 [
          (195, .leaf)
        ]))
      ])),
      (523, (.branch 35 [
        (99, (.branch 131 [
          (387, .leaf)
        ])),
        (163, (.branch 67 [
          (323, .leaf)
        ])),
        (291, (.branch 67 [
          (195, .leaf)
        ]))
      ]))
    ])),
    (39, (.branch 11 [
      (27, (.branch 67 [
        (195, (.branch 259 [
          (771, .leaf)
        ])),
        (323, (.branch 131 [
          (643, .leaf)
        ])),
        (579, (.branch 131 [
          (387, .leaf)
        ]))
      ])),
      (75, (.branch 19 [
        (147, (.branch 259 [
          (771, .leaf)
        ])),
        (275, (.branch 131 [
          (643, .leaf)
        ])),
        (531, (.branch 131 [
          (387, .leaf)
        ]))
      ])),
      (139, (.branch 19 [
        (83, (.branch 259 [
          (771, .leaf)
        ])),
        (275, (.branch 67 [
          (579, .leaf)
        ])),
        (531, (.branch 67 [
          (323, .leaf)
        ]))
      ])),
      (267, (.branch 19 [
        (83, (.branch 131 [
          (643, .leaf)
        ])),
        (147, (.branch 67 [
          (579, .leaf)
        ])),
        (531, (.branch 67 [
          (195, .leaf)
        ]))
      ])),
      (523, (.branch 19 [
        (83, (.branch 131 [
          (387, .leaf)
        ])),
        (147, (.branch 67 [
          (323, .leaf)
        ])),
        (275, (.branch 67 [
          (195, .leaf)
        ]))
      ]))
    ])),
    (71, (.branch 11 [
      (27, (.branch 35 [
        (163, (.branch 259 [
          (771, .leaf)
        ])),
        (291, (.branch 131 [
          (643, .leaf)
        ])),
        (547, (.branch 131 [
          (387, .leaf)
        ]))
      ])),
      (43, (.branch 19 [
        (147, (.branch 259 [
          (771, .leaf)
        ])),
        (275, (.branch 131 [
          (643, .leaf)
        ])),
        (531, (.branch 131 [
          (387, .leaf)
        ]))
      ])),
      (139, (.branch 19 [
        (51, (.branch 259 [
          (771, .leaf)
        ])),
        (275, (.branch 35 [
          (547, .leaf)
        ])),
        (531, (.branch 35 [
          (291, .leaf)
        ]))
      ])),
      (267, (.branch 19 [
        (51, (.branch 131 [
          (643, .leaf)
        ])),
        (147, (.branch 35 [
          (547, .leaf)
        ])),
        (531, (.branch 35 [
          (163, .leaf)
        ]))
      ])),
      (523, (.branch 19 [
        (51, (.branch 131 [
          (387, .leaf)
        ])),
        (147, (.branch 35 [
          (291, .leaf)
        ])),
        (275, (.branch 35 [
          (163, .leaf)
        ]))
      ]))
    ])),
    (135, (.branch 11 [
      (27, (.branch 35 [
        (99, (.branch 259 [
          (771, .leaf)
        ])),
        (291, (.branch 67 [
          (579, .leaf)
        ])),
        (547, (.branch 67 [
          (323, .leaf)
        ]))
      ])),
      (43, (.branch 19 [
        (83, (.branch 259 [
          (771, .leaf)
        ])),
        (275, (.branch 67 [
          (579, .leaf)
        ])),
        (531, (.branch 67 [
          (323, .leaf)
        ]))
      ])),
      (75, (.branch 19 [
        (51, (.branch 259 [
          (771, .leaf)
        ])),
        (275, (.branch 35 [
          (547, .leaf)
        ])),
        (531, (.branch 35 [
          (291, .leaf)
        ]))
      ])),
      (267, (.branch 19 [
        (51, (.branch 67 [
          (579, .leaf)
        ])),
        (83, (.branch 35 [
          (547, .leaf)
        ])),
        (531, (.branch 35 [
          (99, .leaf)
        ]))
      ])),
      (523, (.branch 19 [
        (51, (.branch 67 [
          (323, .leaf)
        ])),
        (83, (.branch 35 [
          (291, .leaf)
        ])),
        (275, (.branch 35 [
          (99, .leaf)
        ]))
      ]))
    ])),
    (263, (.branch 11 [
      (27, (.branch 35 [
        (99, (.branch 131 [
          (643, .leaf)
        ])),
        (163, (.branch 67 [
          (579, .leaf)
        ])),
        (547, (.branch 67 [
          (195, .leaf)
        ]))
      ])),
      (43, (.branch 19 [
        (83, (.branch 131 [
          (643, .leaf)
        ])),
        (147, (.branch 67 [
          (579, .leaf)
        ])),
        (531, (.branch 67 [
          (195, .leaf)
        ]))
      ])),
      (75, (.branch 19 [
        (51, (.branch 131 [
          (643, .leaf)
        ])),
        (147, (.branch 35 [
          (547, .leaf)
        ])),
        (531, (.branch 35 [
          (163, .leaf)
        ]))
      ])),
      (139, (.branch 19 [
        (51, (.branch 67 [
          (579, .leaf)
        ])),
        (83, (.branch 35 [
          (547, .leaf)
        ])),
        (531, (.branch 35 [
          (99, .leaf)
        ]))
      ])),
      (523, (.branch 19 [
        (51, (.branch 67 [
          (195, .leaf)
        ])),
        (83, (.branch 35 [
          (163, .leaf)
        ])),
        (147, (.branch 35 [
          (99, .leaf)
        ]))
      ]))
    ])),
    (519, (.branch 11 [
      (27, (.branch 35 [
        (99, (.branch 131 [
          (387, .leaf)
        ])),
        (163, (.branch 67 [
          (323, .leaf)
        ])),
        (291, (.branch 67 [
          (195, .leaf)
        ]))
      ])),
      (43, (.branch 19 [
        (83, (.branch 131 [
          (387, .leaf)
        ])),
        (147, (.branch 67 [
          (323, .leaf)
        ])),
        (275, (.branch 67 [
          (195, .leaf)
        ]))
      ])),
      (75, (.branch 19 [
        (51, (.branch 131 [
          (387, .leaf)
        ])),
        (147, (.branch 35 [
          (291, .leaf)
        ])),
        (275, (.branch 35 [
          (163, .leaf)
        ]))
      ])),
      (139, (.branch 19 [
        (51, (.branch 67 [
          (323, .leaf)
        ])),
        (83, (.branch 35 [
          (291, .leaf)
        ])),
        (275, (.branch 35 [
          (99, .leaf)
        ]))
      ])),
      (267, (.branch 19 [
        (51, (.branch 67 [
          (195, .leaf)
        ])),
        (83, (.branch 35 [
          (163, .leaf)
        ])),
        (147, (.branch 35 [
          (99, .leaf)
        ]))
      ]))
    ]))
  ])
  matchWords := [
  ([771, 195, 51, 15], ⟨[0, 1, 8, 9, 6, 7, 4, 5, 2, 3], [0, 1, 8, 9, 6, 7, 4, 5, 2, 3]⟩),
  ([643, 323, 51, 15], ⟨[0, 1, 7, 9, 6, 8, 4, 5, 2, 3], [0, 1, 8, 9, 6, 7, 4, 2, 5, 3]⟩),
  ([387, 579, 51, 15], ⟨[0, 1, 7, 8, 6, 9, 4, 5, 2, 3], [0, 1, 8, 9, 6, 7, 4, 2, 3, 5]⟩),
  ([771, 163, 83, 15], ⟨[0, 1, 8, 9, 5, 7, 4, 6, 2, 3], [0, 1, 8, 9, 6, 4, 7, 5, 2, 3]⟩),
  ([643, 291, 83, 15], ⟨[0, 1, 7, 9, 5, 8, 4, 6, 2, 3], [0, 1, 8, 9, 6, 4, 7, 2, 5, 3]⟩),
  ([387, 547, 83, 15], ⟨[0, 1, 7, 8, 5, 9, 4, 6, 2, 3], [0, 1, 8, 9, 6, 4, 7, 2, 3, 5]⟩),
  ([771, 99, 147, 15], ⟨[0, 1, 8, 9, 5, 6, 4, 7, 2, 3], [0, 1, 8, 9, 6, 4, 5, 7, 2, 3]⟩),
  ([579, 291, 147, 15], ⟨[0, 1, 6, 9, 5, 8, 4, 7, 2, 3], [0, 1, 8, 9, 6, 4, 2, 7, 5, 3]⟩),
  ([323, 547, 147, 15], ⟨[0, 1, 6, 8, 5, 9, 4, 7, 2, 3], [0, 1, 8, 9, 6, 4, 2, 7, 3, 5]⟩),
  ([643, 99, 275, 15], ⟨[0, 1, 7, 9, 5, 6, 4, 8, 2, 3], [0, 1, 8, 9, 6, 4, 5, 2, 7, 3]⟩),
  ([579, 163, 275, 15], ⟨[0, 1, 6, 9, 5, 7, 4, 8, 2, 3], [0, 1, 8, 9, 6, 4, 2, 5, 7, 3]⟩),
  ([195, 547, 275, 15], ⟨[0, 1, 6, 7, 5, 9, 4, 8, 2, 3], [0, 1, 8, 9, 6, 4, 2, 3, 7, 5]⟩),
  ([387, 99, 531, 15], ⟨[0, 1, 7, 8, 5, 6, 4, 9, 2, 3], [0, 1, 8, 9, 6, 4, 5, 2, 3, 7]⟩),
  ([323, 163, 531, 15], ⟨[0, 1, 6, 8, 5, 7, 4, 9, 2, 3], [0, 1, 8, 9, 6, 4, 2, 5, 3, 7]⟩),
  ([195, 291, 531, 15], ⟨[0, 1, 6, 7, 5, 8, 4, 9, 2, 3], [0, 1, 8, 9, 6, 4, 2, 3, 5, 7]⟩),
  ([771, 195, 43, 23], ⟨[0, 1, 8, 9, 6, 7, 3, 5, 2, 4], [0, 1, 8, 6, 9, 7, 4, 5, 2, 3]⟩),
  ([643, 323, 43, 23], ⟨[0, 1, 7, 9, 6, 8, 3, 5, 2, 4], [0, 1, 8, 6, 9, 7, 4, 2, 5, 3]⟩),
  ([387, 579, 43, 23], ⟨[0, 1, 7, 8, 6, 9, 3, 5, 2, 4], [0, 1, 8, 6, 9, 7, 4, 2, 3, 5]⟩),
  ([771, 163, 75, 23], ⟨[0, 1, 8, 9, 5, 7, 3, 6, 2, 4], [0, 1, 8, 6, 9, 4, 7, 5, 2, 3]⟩),
  ([643, 291, 75, 23], ⟨[0, 1, 7, 9, 5, 8, 3, 6, 2, 4], [0, 1, 8, 6, 9, 4, 7, 2, 5, 3]⟩),
  ([387, 547, 75, 23], ⟨[0, 1, 7, 8, 5, 9, 3, 6, 2, 4], [0, 1, 8, 6, 9, 4, 7, 2, 3, 5]⟩),
  ([771, 99, 139, 23], ⟨[0, 1, 8, 9, 5, 6, 3, 7, 2, 4], [0, 1, 8, 6, 9, 4, 5, 7, 2, 3]⟩),
  ([579, 291, 139, 23], ⟨[0, 1, 6, 9, 5, 8, 3, 7, 2, 4], [0, 1, 8, 6, 9, 4, 2, 7, 5, 3]⟩),
  ([323, 547, 139, 23], ⟨[0, 1, 6, 8, 5, 9, 3, 7, 2, 4], [0, 1, 8, 6, 9, 4, 2, 7, 3, 5]⟩),
  ([643, 99, 267, 23], ⟨[0, 1, 7, 9, 5, 6, 3, 8, 2, 4], [0, 1, 8, 6, 9, 4, 5, 2, 7, 3]⟩),
  ([579, 163, 267, 23], ⟨[0, 1, 6, 9, 5, 7, 3, 8, 2, 4], [0, 1, 8, 6, 9, 4, 2, 5, 7, 3]⟩),
  ([195, 547, 267, 23], ⟨[0, 1, 6, 7, 5, 9, 3, 8, 2, 4], [0, 1, 8, 6, 9, 4, 2, 3, 7, 5]⟩),
  ([387, 99, 523, 23], ⟨[0, 1, 7, 8, 5, 6, 3, 9, 2, 4], [0, 1, 8, 6, 9, 4, 5, 2, 3, 7]⟩),
  ([323, 163, 523, 23], ⟨[0, 1, 6, 8, 5, 7, 3, 9, 2, 4], [0, 1, 8, 6, 9, 4, 2, 5, 3, 7]⟩),
  ([195, 291, 523, 23], ⟨[0, 1, 6, 7, 5, 8, 3, 9, 2, 4], [0, 1, 8, 6, 9, 4, 2, 3, 5, 7]⟩),
  ([771, 195, 27, 39], ⟨[0, 1, 8, 9, 6, 7, 3, 4, 2, 5], [0, 1, 8, 6, 7, 9, 4, 5, 2, 3]⟩),
  ([643, 323, 27, 39], ⟨[0, 1, 7, 9, 6, 8, 3, 4, 2, 5], [0, 1, 8, 6, 7, 9, 4, 2, 5, 3]⟩),
  ([387, 579, 27, 39], ⟨[0, 1, 7, 8, 6, 9, 3, 4, 2, 5], [0, 1, 8, 6, 7, 9, 4, 2, 3, 5]⟩),
  ([771, 147, 75, 39], ⟨[0, 1, 8, 9, 4, 7, 3, 6, 2, 5], [0, 1, 8, 6, 4, 9, 7, 5, 2, 3]⟩),
  ([643, 275, 75, 39], ⟨[0, 1, 7, 9, 4, 8, 3, 6, 2, 5], [0, 1, 8, 6, 4, 9, 7, 2, 5, 3]⟩),
  ([387, 531, 75, 39], ⟨[0, 1, 7, 8, 4, 9, 3, 6, 2, 5], [0, 1, 8, 6, 4, 9, 7, 2, 3, 5]⟩),
  ([771, 83, 139, 39], ⟨[0, 1, 8, 9, 4, 6, 3, 7, 2, 5], [0, 1, 8, 6, 4, 9, 5, 7, 2, 3]⟩),
  ([579, 275, 139, 39], ⟨[0, 1, 6, 9, 4, 8, 3, 7, 2, 5], [0, 1, 8, 6, 4, 9, 2, 7, 5, 3]⟩),
  ([323, 531, 139, 39], ⟨[0, 1, 6, 8, 4, 9, 3, 7, 2, 5], [0, 1, 8, 6, 4, 9, 2, 7, 3, 5]⟩),
  ([643, 83, 267, 39], ⟨[0, 1, 7, 9, 4, 6, 3, 8, 2, 5], [0, 1, 8, 6, 4, 9, 5, 2, 7, 3]⟩),
  ([579, 147, 267, 39], ⟨[0, 1, 6, 9, 4, 7, 3, 8, 2, 5], [0, 1, 8, 6, 4, 9, 2, 5, 7, 3]⟩),
  ([195, 531, 267, 39], ⟨[0, 1, 6, 7, 4, 9, 3, 8, 2, 5], [0, 1, 8, 6, 4, 9, 2, 3, 7, 5]⟩),
  ([387, 83, 523, 39], ⟨[0, 1, 7, 8, 4, 6, 3, 9, 2, 5], [0, 1, 8, 6, 4, 9, 5, 2, 3, 7]⟩),
  ([323, 147, 523, 39], ⟨[0, 1, 6, 8, 4, 7, 3, 9, 2, 5], [0, 1, 8, 6, 4, 9, 2, 5, 3, 7]⟩),
  ([195, 275, 523, 39], ⟨[0, 1, 6, 7, 4, 8, 3, 9, 2, 5], [0, 1, 8, 6, 4, 9, 2, 3, 5, 7]⟩),
  ([771, 163, 27, 71], ⟨[0, 1, 8, 9, 5, 7, 3, 4, 2, 6], [0, 1, 8, 6, 7, 4, 9, 5, 2, 3]⟩),
  ([643, 291, 27, 71], ⟨[0, 1, 7, 9, 5, 8, 3, 4, 2, 6], [0, 1, 8, 6, 7, 4, 9, 2, 5, 3]⟩),
  ([387, 547, 27, 71], ⟨[0, 1, 7, 8, 5, 9, 3, 4, 2, 6], [0, 1, 8, 6, 7, 4, 9, 2, 3, 5]⟩),
  ([771, 147, 43, 71], ⟨[0, 1, 8, 9, 4, 7, 3, 5, 2, 6], [0, 1, 8, 6, 4, 7, 9, 5, 2, 3]⟩),
  ([643, 275, 43, 71], ⟨[0, 1, 7, 9, 4, 8, 3, 5, 2, 6], [0, 1, 8, 6, 4, 7, 9, 2, 5, 3]⟩),
  ([387, 531, 43, 71], ⟨[0, 1, 7, 8, 4, 9, 3, 5, 2, 6], [0, 1, 8, 6, 4, 7, 9, 2, 3, 5]⟩),
  ([771, 51, 139, 71], ⟨[0, 1, 8, 9, 4, 5, 3, 7, 2, 6], [0, 1, 8, 6, 4, 5, 9, 7, 2, 3]⟩),
  ([547, 275, 139, 71], ⟨[0, 1, 5, 9, 4, 8, 3, 7, 2, 6], [0, 1, 8, 6, 4, 2, 9, 7, 5, 3]⟩),
  ([291, 531, 139, 71], ⟨[0, 1, 5, 8, 4, 9, 3, 7, 2, 6], [0, 1, 8, 6, 4, 2, 9, 7, 3, 5]⟩),
  ([643, 51, 267, 71], ⟨[0, 1, 7, 9, 4, 5, 3, 8, 2, 6], [0, 1, 8, 6, 4, 5, 9, 2, 7, 3]⟩),
  ([547, 147, 267, 71], ⟨[0, 1, 5, 9, 4, 7, 3, 8, 2, 6], [0, 1, 8, 6, 4, 2, 9, 5, 7, 3]⟩),
  ([163, 531, 267, 71], ⟨[0, 1, 5, 7, 4, 9, 3, 8, 2, 6], [0, 1, 8, 6, 4, 2, 9, 3, 7, 5]⟩),
  ([387, 51, 523, 71], ⟨[0, 1, 7, 8, 4, 5, 3, 9, 2, 6], [0, 1, 8, 6, 4, 5, 9, 2, 3, 7]⟩),
  ([291, 147, 523, 71], ⟨[0, 1, 5, 8, 4, 7, 3, 9, 2, 6], [0, 1, 8, 6, 4, 2, 9, 5, 3, 7]⟩),
  ([163, 275, 523, 71], ⟨[0, 1, 5, 7, 4, 8, 3, 9, 2, 6], [0, 1, 8, 6, 4, 2, 9, 3, 5, 7]⟩),
  ([771, 99, 27, 135], ⟨[0, 1, 8, 9, 5, 6, 3, 4, 2, 7], [0, 1, 8, 6, 7, 4, 5, 9, 2, 3]⟩),
  ([579, 291, 27, 135], ⟨[0, 1, 6, 9, 5, 8, 3, 4, 2, 7], [0, 1, 8, 6, 7, 4, 2, 9, 5, 3]⟩),
  ([323, 547, 27, 135], ⟨[0, 1, 6, 8, 5, 9, 3, 4, 2, 7], [0, 1, 8, 6, 7, 4, 2, 9, 3, 5]⟩),
  ([771, 83, 43, 135], ⟨[0, 1, 8, 9, 4, 6, 3, 5, 2, 7], [0, 1, 8, 6, 4, 7, 5, 9, 2, 3]⟩),
  ([579, 275, 43, 135], ⟨[0, 1, 6, 9, 4, 8, 3, 5, 2, 7], [0, 1, 8, 6, 4, 7, 2, 9, 5, 3]⟩),
  ([323, 531, 43, 135], ⟨[0, 1, 6, 8, 4, 9, 3, 5, 2, 7], [0, 1, 8, 6, 4, 7, 2, 9, 3, 5]⟩),
  ([771, 51, 75, 135], ⟨[0, 1, 8, 9, 4, 5, 3, 6, 2, 7], [0, 1, 8, 6, 4, 5, 7, 9, 2, 3]⟩),
  ([547, 275, 75, 135], ⟨[0, 1, 5, 9, 4, 8, 3, 6, 2, 7], [0, 1, 8, 6, 4, 2, 7, 9, 5, 3]⟩),
  ([291, 531, 75, 135], ⟨[0, 1, 5, 8, 4, 9, 3, 6, 2, 7], [0, 1, 8, 6, 4, 2, 7, 9, 3, 5]⟩),
  ([579, 51, 267, 135], ⟨[0, 1, 6, 9, 4, 5, 3, 8, 2, 7], [0, 1, 8, 6, 4, 5, 2, 9, 7, 3]⟩),
  ([547, 83, 267, 135], ⟨[0, 1, 5, 9, 4, 6, 3, 8, 2, 7], [0, 1, 8, 6, 4, 2, 5, 9, 7, 3]⟩),
  ([99, 531, 267, 135], ⟨[0, 1, 5, 6, 4, 9, 3, 8, 2, 7], [0, 1, 8, 6, 4, 2, 3, 9, 7, 5]⟩),
  ([323, 51, 523, 135], ⟨[0, 1, 6, 8, 4, 5, 3, 9, 2, 7], [0, 1, 8, 6, 4, 5, 2, 9, 3, 7]⟩),
  ([291, 83, 523, 135], ⟨[0, 1, 5, 8, 4, 6, 3, 9, 2, 7], [0, 1, 8, 6, 4, 2, 5, 9, 3, 7]⟩),
  ([99, 275, 523, 135], ⟨[0, 1, 5, 6, 4, 8, 3, 9, 2, 7], [0, 1, 8, 6, 4, 2, 3, 9, 5, 7]⟩),
  ([643, 99, 27, 263], ⟨[0, 1, 7, 9, 5, 6, 3, 4, 2, 8], [0, 1, 8, 6, 7, 4, 5, 2, 9, 3]⟩),
  ([579, 163, 27, 263], ⟨[0, 1, 6, 9, 5, 7, 3, 4, 2, 8], [0, 1, 8, 6, 7, 4, 2, 5, 9, 3]⟩),
  ([195, 547, 27, 263], ⟨[0, 1, 6, 7, 5, 9, 3, 4, 2, 8], [0, 1, 8, 6, 7, 4, 2, 3, 9, 5]⟩),
  ([643, 83, 43, 263], ⟨[0, 1, 7, 9, 4, 6, 3, 5, 2, 8], [0, 1, 8, 6, 4, 7, 5, 2, 9, 3]⟩),
  ([579, 147, 43, 263], ⟨[0, 1, 6, 9, 4, 7, 3, 5, 2, 8], [0, 1, 8, 6, 4, 7, 2, 5, 9, 3]⟩),
  ([195, 531, 43, 263], ⟨[0, 1, 6, 7, 4, 9, 3, 5, 2, 8], [0, 1, 8, 6, 4, 7, 2, 3, 9, 5]⟩),
  ([643, 51, 75, 263], ⟨[0, 1, 7, 9, 4, 5, 3, 6, 2, 8], [0, 1, 8, 6, 4, 5, 7, 2, 9, 3]⟩),
  ([547, 147, 75, 263], ⟨[0, 1, 5, 9, 4, 7, 3, 6, 2, 8], [0, 1, 8, 6, 4, 2, 7, 5, 9, 3]⟩),
  ([163, 531, 75, 263], ⟨[0, 1, 5, 7, 4, 9, 3, 6, 2, 8], [0, 1, 8, 6, 4, 2, 7, 3, 9, 5]⟩),
  ([579, 51, 139, 263], ⟨[0, 1, 6, 9, 4, 5, 3, 7, 2, 8], [0, 1, 8, 6, 4, 5, 2, 7, 9, 3]⟩),
  ([547, 83, 139, 263], ⟨[0, 1, 5, 9, 4, 6, 3, 7, 2, 8], [0, 1, 8, 6, 4, 2, 5, 7, 9, 3]⟩),
  ([99, 531, 139, 263], ⟨[0, 1, 5, 6, 4, 9, 3, 7, 2, 8], [0, 1, 8, 6, 4, 2, 3, 7, 9, 5]⟩),
  ([195, 51, 523, 263], ⟨[0, 1, 6, 7, 4, 5, 3, 9, 2, 8], [0, 1, 8, 6, 4, 5, 2, 3, 9, 7]⟩),
  ([163, 83, 523, 263], ⟨[0, 1, 5, 7, 4, 6, 3, 9, 2, 8], [0, 1, 8, 6, 4, 2, 5, 3, 9, 7]⟩),
  ([99, 147, 523, 263], ⟨[0, 1, 5, 6, 4, 7, 3, 9, 2, 8], [0, 1, 8, 6, 4, 2, 3, 5, 9, 7]⟩),
  ([387, 99, 27, 519], ⟨[0, 1, 7, 8, 5, 6, 3, 4, 2, 9], [0, 1, 8, 6, 7, 4, 5, 2, 3, 9]⟩),
  ([323, 163, 27, 519], ⟨[0, 1, 6, 8, 5, 7, 3, 4, 2, 9], [0, 1, 8, 6, 7, 4, 2, 5, 3, 9]⟩),
  ([195, 291, 27, 519], ⟨[0, 1, 6, 7, 5, 8, 3, 4, 2, 9], [0, 1, 8, 6, 7, 4, 2, 3, 5, 9]⟩),
  ([387, 83, 43, 519], ⟨[0, 1, 7, 8, 4, 6, 3, 5, 2, 9], [0, 1, 8, 6, 4, 7, 5, 2, 3, 9]⟩),
  ([323, 147, 43, 519], ⟨[0, 1, 6, 8, 4, 7, 3, 5, 2, 9], [0, 1, 8, 6, 4, 7, 2, 5, 3, 9]⟩),
  ([195, 275, 43, 519], ⟨[0, 1, 6, 7, 4, 8, 3, 5, 2, 9], [0, 1, 8, 6, 4, 7, 2, 3, 5, 9]⟩),
  ([387, 51, 75, 519], ⟨[0, 1, 7, 8, 4, 5, 3, 6, 2, 9], [0, 1, 8, 6, 4, 5, 7, 2, 3, 9]⟩),
  ([291, 147, 75, 519], ⟨[0, 1, 5, 8, 4, 7, 3, 6, 2, 9], [0, 1, 8, 6, 4, 2, 7, 5, 3, 9]⟩),
  ([163, 275, 75, 519], ⟨[0, 1, 5, 7, 4, 8, 3, 6, 2, 9], [0, 1, 8, 6, 4, 2, 7, 3, 5, 9]⟩),
  ([323, 51, 139, 519], ⟨[0, 1, 6, 8, 4, 5, 3, 7, 2, 9], [0, 1, 8, 6, 4, 5, 2, 7, 3, 9]⟩),
  ([291, 83, 139, 519], ⟨[0, 1, 5, 8, 4, 6, 3, 7, 2, 9], [0, 1, 8, 6, 4, 2, 5, 7, 3, 9]⟩),
  ([99, 275, 139, 519], ⟨[0, 1, 5, 6, 4, 8, 3, 7, 2, 9], [0, 1, 8, 6, 4, 2, 3, 7, 5, 9]⟩),
  ([195, 51, 267, 519], ⟨[0, 1, 6, 7, 4, 5, 3, 8, 2, 9], [0, 1, 8, 6, 4, 5, 2, 3, 7, 9]⟩),
  ([163, 83, 267, 519], ⟨[0, 1, 5, 7, 4, 6, 3, 8, 2, 9], [0, 1, 8, 6, 4, 2, 5, 3, 7, 9]⟩),
  ([99, 147, 267, 519], ⟨[0, 1, 5, 6, 4, 7, 3, 8, 2, 9], [0, 1, 8, 6, 4, 2, 3, 5, 7, 9]⟩)]
  normSearch := (.branch 21 [
    (85, (.branch 261 [
      (293, (.branch 133 [
        (645, (.branch 161 [
          (169, (.branch 97 [
            (609, (.branch 73 [
              (329, (.branch 25 [
                (537, (.branch 145 [
                  (401, (.branch 22 [
                    (150, (.branch 152 [
                      (216, (.branch 26 [
                        (282, (.branch 28 [
                          (60, (.branch 76 [
                            (588, (.branch 74 [
                              (106, (.branch 38 [
                                (550, (.branch 70 [
                                  (326, (.branch 82 [
                                    (594, (.branch 100 [
                                      (228, (.branch 112 [
                                        (368, (.branch 138 [
                                          (650, (.branch 140 [
                                            (396, (.branch 162 [
                                              (418, (.branch 176 [
                                                (688, (.branch 276 [
                                                  (788, (.branch 296 [
                                                    (808, (.branch 448 [
                                                      (960, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ])),
                    (278, (.branch 134 [
                      (166, (.branch 70 [
                        (582, (.branch 82 [
                          (90, (.branch 98 [
                            (354, (.branch 42 [
                              (554, (.branch 100 [
                                (108, (.branch 28 [
                                  (156, (.branch 52 [
                                    (564, (.branch 56 [
                                      (312, (.branch 112 [
                                        (240, (.branch 138 [
                                          (394, (.branch 146 [
                                            (658, (.branch 196 [
                                              (452, (.branch 200 [
                                                (712, (.branch 268 [
                                                  (780, (.branch 336 [
                                                    (848, (.branch 416 [
                                                      (928, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ])),
                    (534, (.branch 146 [
                      (154, (.branch 82 [
                        (338, (.branch 70 [
                          (102, (.branch 74 [
                            (586, (.branch 42 [
                              (298, (.branch 76 [
                                (204, (.branch 88 [
                                  (120, (.branch 28 [
                                    (284, (.branch 44 [
                                      (556, (.branch 52 [
                                        (180, (.branch 134 [
                                          (390, (.branch 162 [
                                            (674, (.branch 208 [
                                              (720, (.branch 224 [
                                                (480, (.branch 304 [
                                                  (816, (.branch 324 [
                                                    (836, (.branch 392 [
                                                      (904, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ]))
                  ]))
                ]))
              ]))
            ]))
          ]))
        ]))
      ])),
      (389, (.branch 37 [
        (549, (.branch 161 [
          (169, (.branch 97 [
            (353, (.branch 73 [
              (585, (.branch 25 [
                (281, (.branch 145 [
                  (657, (.branch 22 [
                    (150, (.branch 152 [
                      (216, (.branch 26 [
                        (538, (.branch 28 [
                          (60, (.branch 76 [
                            (332, (.branch 74 [
                              (106, (.branch 38 [
                                (294, (.branch 70 [
                                  (582, (.branch 82 [
                                    (338, (.branch 100 [
                                      (228, (.branch 112 [
                                        (624, (.branch 138 [
                                          (394, (.branch 140 [
                                            (652, (.branch 162 [
                                              (674, (.branch 176 [
                                                (432, (.branch 276 [
                                                  (788, (.branch 296 [
                                                    (808, (.branch 448 [
                                                      (960, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ])),
                    (278, (.branch 146 [
                      (154, (.branch 82 [
                        (594, (.branch 70 [
                          (102, (.branch 74 [
                            (330, (.branch 42 [
                              (554, (.branch 76 [
                                (204, (.branch 88 [
                                  (120, (.branch 28 [
                                    (540, (.branch 44 [
                                      (300, (.branch 52 [
                                        (180, (.branch 134 [
                                          (646, (.branch 162 [
                                            (418, (.branch 208 [
                                              (464, (.branch 224 [
                                                (736, (.branch 304 [
                                                  (816, (.branch 324 [
                                                    (836, (.branch 392 [
                                                      (904, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ])),
                    (534, (.branch 134 [
                      (166, (.branch 70 [
                        (326, (.branch 82 [
                          (90, (.branch 98 [
                            (610, (.branch 42 [
                              (298, (.branch 100 [
                                (108, (.branch 28 [
                                  (156, (.branch 52 [
                                    (308, (.branch 56 [
                                      (568, (.branch 112 [
                                        (240, (.branch 138 [
                                          (650, (.branch 146 [
                                            (402, (.branch 196 [
                                              (708, (.branch 200 [
                                                (456, (.branch 268 [
                                                  (780, (.branch 336 [
                                                    (848, (.branch 416 [
                                                      (928, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ]))
                  ]))
                ]))
              ]))
            ]))
          ]))
        ]))
      ]))
    ])),
    (149, (.branch 261 [
      (293, (.branch 69 [
        (581, (.branch 97 [
          (105, (.branch 81 [
            (337, (.branch 25 [
              (537, (.branch 137 [
                (393, (.branch 161 [
                  (673, (.branch 22 [
                    (86, (.branch 88 [
                      (216, (.branch 26 [
                        (282, (.branch 28 [
                          (60, (.branch 74 [
                            (586, (.branch 42 [
                              (170, (.branch 38 [
                                (550, (.branch 76 [
                                  (332, (.branch 98 [
                                    (354, (.branch 100 [
                                      (228, (.branch 112 [
                                        (624, (.branch 134 [
                                          (390, (.branch 140 [
                                            (652, (.branch 146 [
                                              (658, (.branch 176 [
                                                (432, (.branch 276 [
                                                  (788, (.branch 296 [
                                                    (808, (.branch 448 [
                                                      (960, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ])),
                    (278, (.branch 70 [
                      (102, (.branch 84 [
                        (92, (.branch 26 [
                          (154, (.branch 52 [
                            (564, (.branch 44 [
                              (172, (.branch 56 [
                                (312, (.branch 42 [
                                  (554, (.branch 74 [
                                    (330, (.branch 82 [
                                      (594, (.branch 112 [
                                        (240, (.branch 134 [
                                          (646, (.branch 162 [
                                            (418, (.branch 196 [
                                              (452, (.branch 200 [
                                                (712, (.branch 268 [
                                                  (780, (.branch 352 [
                                                    (864, (.branch 400 [
                                                      (912, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ])),
                    (534, (.branch 82 [
                      (90, (.branch 84 [
                        (116, (.branch 28 [
                          (284, (.branch 38 [
                            (166, (.branch 44 [
                              (556, (.branch 42 [
                                (298, (.branch 56 [
                                  (184, (.branch 70 [
                                    (326, (.branch 76 [
                                      (204, (.branch 98 [
                                        (610, (.branch 138 [
                                          (650, (.branch 146 [
                                            (402, (.branch 208 [
                                              (720, (.branch 224 [
                                                (480, (.branch 304 [
                                                  (816, (.branch 328 [
                                                    (840, (.branch 388 [
                                                      (900, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ]))
                  ]))
                ]))
              ]))
            ]))
          ]))
        ]))
      ])),
      (325, (.branch 37 [
        (549, (.branch 97 [
          (105, (.branch 81 [
            (593, (.branch 25 [
              (281, (.branch 137 [
                (649, (.branch 161 [
                  (417, (.branch 22 [
                    (86, (.branch 88 [
                      (216, (.branch 26 [
                        (538, (.branch 28 [
                          (60, (.branch 74 [
                            (330, (.branch 42 [
                              (170, (.branch 38 [
                                (294, (.branch 76 [
                                  (588, (.branch 98 [
                                    (610, (.branch 100 [
                                      (228, (.branch 112 [
                                        (368, (.branch 134 [
                                          (646, (.branch 140 [
                                            (396, (.branch 146 [
                                              (402, (.branch 176 [
                                                (688, (.branch 276 [
                                                  (788, (.branch 296 [
                                                    (808, (.branch 448 [
                                                      (960, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ])),
                    (278, (.branch 82 [
                      (90, (.branch 84 [
                        (116, (.branch 28 [
                          (540, (.branch 38 [
                            (166, (.branch 44 [
                              (300, (.branch 42 [
                                (554, (.branch 56 [
                                  (184, (.branch 70 [
                                    (582, (.branch 76 [
                                      (204, (.branch 98 [
                                        (354, (.branch 138 [
                                          (394, (.branch 146 [
                                            (658, (.branch 208 [
                                              (464, (.branch 224 [
                                                (736, (.branch 304 [
                                                  (816, (.branch 328 [
                                                    (840, (.branch 388 [
                                                      (900, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ])),
                    (534, (.branch 70 [
                      (102, (.branch 84 [
                        (92, (.branch 26 [
                          (154, (.branch 52 [
                            (308, (.branch 44 [
                              (172, (.branch 56 [
                                (568, (.branch 42 [
                                  (298, (.branch 74 [
                                    (586, (.branch 82 [
                                      (338, (.branch 112 [
                                        (240, (.branch 134 [
                                          (390, (.branch 162 [
                                            (674, (.branch 196 [
                                              (708, (.branch 200 [
                                                (456, (.branch 268 [
                                                  (780, (.branch 352 [
                                                    (864, (.branch 400 [
                                                      (912, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ]))
                  ]))
                ]))
              ]))
            ]))
          ]))
        ]))
      ]))
    ])),
    (277, (.branch 69 [
      (101, (.branch 133 [
        (645, (.branch 145 [
          (153, (.branch 81 [
            (593, (.branch 73 [
              (329, (.branch 41 [
                (553, (.branch 161 [
                  (417, (.branch 22 [
                    (86, (.branch 88 [
                      (120, (.branch 28 [
                        (540, (.branch 26 [
                          (282, (.branch 42 [
                            (170, (.branch 44 [
                              (300, (.branch 38 [
                                (550, (.branch 52 [
                                  (180, (.branch 74 [
                                    (586, (.branch 76 [
                                      (204, (.branch 98 [
                                        (354, (.branch 134 [
                                          (390, (.branch 146 [
                                            (658, (.branch 208 [
                                              (464, (.branch 224 [
                                                (736, (.branch 304 [
                                                  (816, (.branch 324 [
                                                    (836, (.branch 392 [
                                                      (904, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ])),
                    (150, (.branch 84 [
                      (92, (.branch 52 [
                        (564, (.branch 38 [
                          (294, (.branch 44 [
                            (172, (.branch 42 [
                              (106, (.branch 56 [
                                (312, (.branch 26 [
                                  (538, (.branch 70 [
                                    (582, (.branch 82 [
                                      (338, (.branch 112 [
                                        (240, (.branch 138 [
                                          (394, (.branch 162 [
                                            (674, (.branch 196 [
                                              (452, (.branch 200 [
                                                (712, (.branch 268 [
                                                  (780, (.branch 352 [
                                                    (864, (.branch 400 [
                                                      (912, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ])),
                    (534, (.branch 70 [
                      (326, (.branch 38 [
                        (166, (.branch 52 [
                          (60, (.branch 82 [
                            (90, (.branch 42 [
                              (298, (.branch 84 [
                                (212, (.branch 76 [
                                  (588, (.branch 98 [
                                    (610, (.branch 104 [
                                      (232, (.branch 112 [
                                        (368, (.branch 138 [
                                          (650, (.branch 140 [
                                            (396, (.branch 146 [
                                              (402, (.branch 176 [
                                                (688, (.branch 280 [
                                                  (792, (.branch 292 [
                                                    (804, (.branch 448 [
                                                      (960, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ]))
                  ]))
                ]))
              ]))
            ]))
          ]))
        ]))
      ])),
      (581, (.branch 37 [
        (165, (.branch 81 [
          (89, (.branch 97 [
            (353, (.branch 41 [
              (553, (.branch 137 [
                (393, (.branch 145 [
                  (657, (.branch 22 [
                    (86, (.branch 100 [
                      (108, (.branch 52 [
                        (564, (.branch 28 [
                          (156, (.branch 38 [
                            (294, (.branch 42 [
                              (170, (.branch 56 [
                                (312, (.branch 26 [
                                  (538, (.branch 74 [
                                    (330, (.branch 98 [
                                      (610, (.branch 112 [
                                        (240, (.branch 134 [
                                          (646, (.branch 146 [
                                            (402, (.branch 196 [
                                              (452, (.branch 200 [
                                                (712, (.branch 268 [
                                                  (780, (.branch 336 [
                                                    (848, (.branch 416 [
                                                      (928, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ])),
                    (150, (.branch 84 [
                      (116, (.branch 28 [
                        (540, (.branch 26 [
                          (282, (.branch 44 [
                            (300, (.branch 38 [
                              (550, (.branch 56 [
                                (184, (.branch 42 [
                                  (106, (.branch 70 [
                                    (326, (.branch 76 [
                                      (204, (.branch 82 [
                                        (594, (.branch 138 [
                                          (650, (.branch 162 [
                                            (418, (.branch 208 [
                                              (464, (.branch 224 [
                                                (736, (.branch 304 [
                                                  (816, (.branch 328 [
                                                    (840, (.branch 388 [
                                                      (900, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ])),
                    (534, (.branch 82 [
                      (338, (.branch 26 [
                        (154, (.branch 28 [
                          (60, (.branch 70 [
                            (102, (.branch 42 [
                              (298, (.branch 74 [
                                (586, (.branch 84 [
                                  (212, (.branch 76 [
                                    (332, (.branch 104 [
                                      (232, (.branch 112 [
                                        (624, (.branch 134 [
                                          (390, (.branch 140 [
                                            (652, (.branch 162 [
                                              (674, (.branch 176 [
                                                (432, (.branch 280 [
                                                  (792, (.branch 292 [
                                                    (804, (.branch 448 [
                                                      (960, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ]))
                  ]))
                ]))
              ]))
            ]))
          ]))
        ]))
      ]))
    ])),
    (533, (.branch 69 [
      (101, (.branch 133 [
        (389, (.branch 145 [
          (153, (.branch 81 [
            (337, (.branch 73 [
              (585, (.branch 41 [
                (297, (.branch 161 [
                  (673, (.branch 22 [
                    (86, (.branch 88 [
                      (120, (.branch 28 [
                        (284, (.branch 26 [
                          (538, (.branch 42 [
                            (170, (.branch 44 [
                              (556, (.branch 38 [
                                (294, (.branch 52 [
                                  (180, (.branch 74 [
                                    (330, (.branch 76 [
                                      (204, (.branch 98 [
                                        (610, (.branch 134 [
                                          (646, (.branch 146 [
                                            (402, (.branch 208 [
                                              (720, (.branch 224 [
                                                (480, (.branch 304 [
                                                  (816, (.branch 324 [
                                                    (836, (.branch 392 [
                                                      (904, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ])),
                    (150, (.branch 84 [
                      (92, (.branch 52 [
                        (308, (.branch 38 [
                          (550, (.branch 44 [
                            (172, (.branch 42 [
                              (106, (.branch 56 [
                                (568, (.branch 26 [
                                  (282, (.branch 70 [
                                    (326, (.branch 82 [
                                      (594, (.branch 112 [
                                        (240, (.branch 138 [
                                          (650, (.branch 162 [
                                            (418, (.branch 196 [
                                              (708, (.branch 200 [
                                                (456, (.branch 268 [
                                                  (780, (.branch 352 [
                                                    (864, (.branch 400 [
                                                      (912, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ])),
                    (278, (.branch 70 [
                      (582, (.branch 38 [
                        (166, (.branch 52 [
                          (60, (.branch 82 [
                            (90, (.branch 42 [
                              (554, (.branch 84 [
                                (212, (.branch 76 [
                                  (332, (.branch 98 [
                                    (354, (.branch 104 [
                                      (232, (.branch 112 [
                                        (624, (.branch 138 [
                                          (394, (.branch 140 [
                                            (652, (.branch 146 [
                                              (658, (.branch 176 [
                                                (432, (.branch 280 [
                                                  (792, (.branch 292 [
                                                    (804, (.branch 448 [
                                                      (960, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ]))
                  ]))
                ]))
              ]))
            ]))
          ]))
        ]))
      ])),
      (325, (.branch 37 [
        (165, (.branch 81 [
          (89, (.branch 97 [
            (609, (.branch 41 [
              (297, (.branch 137 [
                (649, (.branch 145 [
                  (401, (.branch 22 [
                    (86, (.branch 100 [
                      (108, (.branch 52 [
                        (308, (.branch 28 [
                          (156, (.branch 38 [
                            (550, (.branch 42 [
                              (170, (.branch 56 [
                                (568, (.branch 26 [
                                  (282, (.branch 74 [
                                    (586, (.branch 98 [
                                      (354, (.branch 112 [
                                        (240, (.branch 134 [
                                          (390, (.branch 146 [
                                            (658, (.branch 196 [
                                              (708, (.branch 200 [
                                                (456, (.branch 268 [
                                                  (780, (.branch 336 [
                                                    (848, (.branch 416 [
                                                      (928, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ])),
                    (150, (.branch 84 [
                      (116, (.branch 28 [
                        (284, (.branch 26 [
                          (538, (.branch 44 [
                            (556, (.branch 38 [
                              (294, (.branch 56 [
                                (184, (.branch 42 [
                                  (106, (.branch 70 [
                                    (582, (.branch 76 [
                                      (204, (.branch 82 [
                                        (338, (.branch 138 [
                                          (394, (.branch 162 [
                                            (674, (.branch 208 [
                                              (720, (.branch 224 [
                                                (480, (.branch 304 [
                                                  (816, (.branch 328 [
                                                    (840, (.branch 388 [
                                                      (900, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ])),
                    (278, (.branch 82 [
                      (594, (.branch 26 [
                        (154, (.branch 28 [
                          (60, (.branch 70 [
                            (102, (.branch 42 [
                              (554, (.branch 74 [
                                (330, (.branch 84 [
                                  (212, (.branch 76 [
                                    (588, (.branch 104 [
                                      (232, (.branch 112 [
                                        (368, (.branch 134 [
                                          (646, (.branch 140 [
                                            (396, (.branch 162 [
                                              (418, (.branch 176 [
                                                (688, (.branch 280 [
                                                  (792, (.branch 292 [
                                                    (804, (.branch 448 [
                                                      (960, .leaf)
                                                    ]))
                                                  ]))
                                                ]))
                                              ]))
                                            ]))
                                          ]))
                                        ]))
                                      ]))
                                    ]))
                                  ]))
                                ]))
                              ]))
                            ]))
                          ]))
                        ]))
                      ]))
                    ]))
                  ]))
                ]))
              ]))
            ]))
          ]))
        ]))
      ]))
    ]))
  ])
  normWords := [
  ([960, 808, 788, 688, 418, 396, 650, 368, 228, 594, 326, 550, 106, 588, 60, 282, 216, 150, 401, 537, 329, 609, 169, 645, 293, 85, 15, 51, 195, 771], ⟨[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]⟩),
  ([928, 848, 780, 712, 452, 658, 394, 240, 312, 564, 156, 108, 554, 354, 90, 582, 166, 278, 401, 537, 329, 609, 169, 645, 293, 85, 15, 51, 195, 771], ⟨[0, 1, 3, 2, 9, 8, 4, 5, 6, 7], [0, 1, 3, 2, 6, 7, 8, 9, 5, 4]⟩),
  ([904, 836, 816, 480, 720, 674, 390, 180, 556, 284, 120, 204, 298, 586, 102, 338, 154, 534, 401, 537, 329, 609, 169, 645, 293, 85, 15, 51, 195, 771], ⟨[0, 1, 3, 2, 7, 6, 5, 4, 8, 9], [0, 1, 3, 2, 7, 6, 5, 4, 8, 9]⟩),
  ([960, 808, 788, 432, 674, 652, 394, 624, 228, 338, 582, 294, 106, 332, 60, 538, 216, 150, 657, 281, 585, 353, 169, 549, 389, 85, 15, 51, 195, 771], ⟨[0, 1, 3, 2, 5, 4, 7, 6, 8, 9], [0, 1, 3, 2, 5, 4, 7, 6, 8, 9]⟩),
  ([904, 836, 816, 736, 464, 418, 646, 180, 300, 540, 120, 204, 554, 330, 102, 594, 154, 278, 657, 281, 585, 353, 169, 549, 389, 85, 15, 51, 195, 771], ⟨[0, 1, 2, 3, 6, 7, 4, 5, 8, 9], [0, 1, 2, 3, 6, 7, 4, 5, 8, 9]⟩),
  ([928, 848, 780, 456, 708, 402, 650, 240, 568, 308, 156, 108, 298, 610, 90, 326, 166, 534, 657, 281, 585, 353, 169, 549, 389, 85, 15, 51, 195, 771], ⟨[0, 1, 3, 2, 8, 9, 4, 5, 6, 7], [0, 1, 3, 2, 6, 7, 8, 9, 4, 5]⟩),
  ([960, 808, 788, 432, 658, 652, 390, 624, 228, 354, 332, 550, 170, 586, 60, 282, 216, 86, 673, 393, 537, 337, 105, 581, 293, 149, 15, 51, 195, 771], ⟨[0, 1, 2, 3, 4, 5, 7, 6, 8, 9], [0, 1, 2, 3, 4, 5, 7, 6, 8, 9]⟩),
  ([912, 864, 780, 712, 452, 418, 646, 240, 594, 330, 554, 312, 172, 564, 154, 92, 102, 278, 673, 393, 537, 337, 105, 581, 293, 149, 15, 51, 195, 771], ⟨[0, 1, 2, 3, 8, 9, 5, 4, 6, 7], [0, 1, 2, 3, 7, 6, 8, 9, 4, 5]⟩),
  ([900, 840, 816, 480, 720, 402, 650, 610, 204, 326, 184, 298, 556, 166, 284, 116, 90, 534, 673, 393, 537, 337, 105, 581, 293, 149, 15, 51, 195, 771], ⟨[0, 1, 3, 2, 6, 7, 5, 4, 8, 9], [0, 1, 3, 2, 7, 6, 4, 5, 8, 9]⟩),
  ([960, 808, 788, 688, 402, 396, 646, 368, 228, 610, 588, 294, 170, 330, 60, 538, 216, 86, 417, 649, 281, 593, 105, 549, 325, 149, 15, 51, 195, 771], ⟨[0, 1, 3, 2, 5, 4, 6, 7, 8, 9], [0, 1, 3, 2, 5, 4, 6, 7, 8, 9]⟩),
  ([900, 840, 816, 736, 464, 658, 394, 354, 204, 582, 184, 554, 300, 166, 540, 116, 90, 278, 417, 649, 281, 593, 105, 549, 325, 149, 15, 51, 195, 771], ⟨[0, 1, 2, 3, 7, 6, 4, 5, 8, 9], [0, 1, 2, 3, 6, 7, 5, 4, 8, 9]⟩),
  ([912, 864, 780, 456, 708, 674, 390, 240, 338, 586, 298, 568, 172, 308, 154, 92, 102, 534, 417, 649, 281, 593, 105, 549, 325, 149, 15, 51, 195, 771], ⟨[0, 1, 2, 3, 9, 8, 5, 4, 6, 7], [0, 1, 2, 3, 7, 6, 8, 9, 5, 4]⟩),
  ([904, 836, 816, 736, 464, 658, 390, 354, 204, 586, 180, 550, 300, 170, 282, 540, 120, 86, 417, 553, 329, 593, 153, 645, 101, 277, 15, 51, 195, 771], ⟨[0, 1, 3, 2, 7, 6, 4, 5, 8, 9], [0, 1, 3, 2, 6, 7, 5, 4, 8, 9]⟩),
  ([912, 864, 780, 712, 452, 674, 394, 240, 338, 582, 538, 312, 106, 172, 294, 564, 92, 150, 417, 553, 329, 593, 153, 645, 101, 277, 15, 51, 195, 771], ⟨[0, 1, 3, 2, 9, 8, 5, 4, 6, 7], [0, 1, 3, 2, 7, 6, 8, 9, 5, 4]⟩),
  ([960, 804, 792, 688, 402, 396, 650, 368, 232, 610, 588, 212, 298, 90, 60, 166, 326, 534, 417, 553, 329, 593, 153, 645, 101, 277, 15, 51, 195, 771], ⟨[0, 1, 2, 3, 5, 4, 6, 7, 8, 9], [0, 1, 2, 3, 5, 4, 6, 7, 8, 9]⟩),
  ([928, 848, 780, 712, 452, 402, 646, 240, 610, 330, 538, 312, 170, 294, 156, 564, 108, 86, 657, 393, 553, 353, 89, 165, 581, 277, 15, 51, 195, 771], ⟨[0, 1, 2, 3, 8, 9, 4, 5, 6, 7], [0, 1, 2, 3, 6, 7, 8, 9, 4, 5]⟩),
  ([900, 840, 816, 736, 464, 418, 650, 594, 204, 326, 106, 184, 550, 300, 282, 540, 116, 150, 657, 393, 553, 353, 89, 165, 581, 277, 15, 51, 195, 771], ⟨[0, 1, 3, 2, 6, 7, 4, 5, 8, 9], [0, 1, 3, 2, 6, 7, 4, 5, 8, 9]⟩),
  ([960, 804, 792, 432, 674, 652, 390, 624, 232, 332, 212, 586, 298, 102, 60, 154, 338, 534, 657, 393, 553, 353, 89, 165, 581, 277, 15, 51, 195, 771], ⟨[0, 1, 2, 3, 5, 4, 7, 6, 8, 9], [0, 1, 2, 3, 5, 4, 7, 6, 8, 9]⟩),
  ([904, 836, 816, 480, 720, 402, 646, 610, 204, 330, 180, 294, 556, 170, 538, 284, 120, 86, 673, 297, 585, 337, 153, 389, 101, 533, 15, 51, 195, 771], ⟨[0, 1, 2, 3, 6, 7, 5, 4, 8, 9], [0, 1, 2, 3, 7, 6, 4, 5, 8, 9]⟩),
  ([912, 864, 780, 456, 708, 418, 650, 240, 594, 326, 282, 568, 106, 172, 550, 308, 92, 150, 673, 297, 585, 337, 153, 389, 101, 533, 15, 51, 195, 771], ⟨[0, 1, 3, 2, 8, 9, 5, 4, 6, 7], [0, 1, 3, 2, 7, 6, 8, 9, 4, 5]⟩),
  ([960, 804, 792, 432, 658, 652, 394, 624, 232, 354, 332, 212, 554, 90, 60, 166, 582, 278, 673, 297, 585, 337, 153, 389, 101, 533, 15, 51, 195, 771], ⟨[0, 1, 3, 2, 4, 5, 7, 6, 8, 9], [0, 1, 3, 2, 4, 5, 7, 6, 8, 9]⟩),
  ([928, 848, 780, 456, 708, 658, 390, 240, 354, 586, 282, 568, 170, 550, 156, 308, 108, 86, 401, 649, 297, 609, 89, 165, 325, 533, 15, 51, 195, 771], ⟨[0, 1, 2, 3, 9, 8, 4, 5, 6, 7], [0, 1, 2, 3, 6, 7, 8, 9, 5, 4]⟩),
  ([900, 840, 816, 480, 720, 674, 394, 338, 204, 582, 106, 184, 294, 556, 538, 284, 116, 150, 401, 649, 297, 609, 89, 165, 325, 533, 15, 51, 195, 771], ⟨[0, 1, 2, 3, 7, 6, 5, 4, 8, 9], [0, 1, 2, 3, 7, 6, 5, 4, 8, 9]⟩),
  ([960, 804, 792, 688, 418, 396, 646, 368, 232, 588, 212, 330, 554, 102, 60, 154, 594, 278, 401, 649, 297, 609, 89, 165, 325, 533, 15, 51, 195, 771], ⟨[0, 1, 3, 2, 4, 5, 6, 7, 8, 9], [0, 1, 3, 2, 4, 5, 6, 7, 8, 9]⟩)]
  canonical := [960, 808, 788, 688, 418, 396, 650, 368, 228, 594, 326, 550, 106, 588, 60, 282, 216, 150, 401, 537, 329, 609, 169, 645, 293, 85, 15, 51, 195, 771]
  prunes := #[
  #[960, 658, 15, 960, 554, 90, 960, 554, 166, 960, 658, 15, 658, 394, 960, 15, 15, 960, 673, 673, 960, 658, 394, 960],
  #[960, 658, 204, 960, 204, 240, 960, 240, 610, 960, 658, 240, 658, 394, 960, 240, 204, 960, 610, 240, 960, 658, 394, 960],
  #[960, 780, 816, 960, 816, 780, 960, 780, 816, 960, 816, 780, 816, 780, 960, 780, 816, 960, 816, 780, 960, 780, 816, 960],
  #[282, 848, 904, 432, 904, 848, 432, 554, 15, 15, 736, 390, 904, 582, 804, 848, 736, 804, 904, 282, 804, 848, 582, 804],
  #[418, 848, 904, 585, 904, 848, 658, 418, 610, 610, 658, 708, 904, 240, 804, 848, 418, 804, 904, 708, 804, 848, 533, 804],
  #[326, 928, 586, 394, 281, 928, 658, 780, 326, 216, 658, 780, 658, 780, 326, 928, 326, 586, 533, 780, 658, 928, 394, 649],
  #[808, 848, 15, 808, 736, 848, 808, 172, 900, 808, 900, 172, 736, 582, 650, 848, 900, 432, 294, 650, 432, 848, 900, 15],
  #[650, 928, 534, 294, 657, 928, 282, 780, 650, 610, 116, 780, 282, 780, 650, 928, 650, 534, 610, 780, 585, 928, 294, 325],
  #[609, 848, 904, 674, 904, 848, 586, 240, 534, 417, 417, 708, 904, 674, 804, 848, 657, 804, 904, 708, 804, 848, 674, 804],
  #[808, 848, 401, 808, 418, 848, 808, 418, 900, 808, 900, 456, 282, 240, 326, 848, 900, 353, 673, 456, 673, 848, 900, 418],
  #[282, 928, 390, 585, 120, 928, 390, 780, 534, 325, 354, 780, 390, 780, 212, 928, 282, 390, 120, 780, 354, 928, 401, 212],
  #[688, 848, 904, 15, 904, 848, 390, 330, 480, 688, 554, 390, 904, 172, 804, 848, 15, 804, 904, 172, 804, 848, 480, 804],
  #[326, 928, 120, 281, 646, 928, 586, 780, 402, 402, 281, 780, 586, 780, 402, 928, 326, 212, 402, 780, 212, 928, 533, 646],
  #[808, 848, 674, 808, 281, 848, 808, 240, 900, 808, 900, 456, 354, 674, 402, 848, 900, 674, 402, 456, 354, 848, 900, 325],
  #[808, 848, 480, 808, 330, 848, 808, 330, 900, 808, 900, 172, 15, 172, 688, 848, 900, 534, 480, 650, 15, 848, 900, 688],
  #[960, 780, 204, 960, 204, 780, 960, 780, 204, 960, 394, 780, 204, 780, 960, 780, 204, 960, 204, 780, 960, 780, 394, 960],
  #[960, 394, 0, 960, 585, 610, 960, 0, 610, 960, 394, 417, 417, 394, 960, 610, 0, 960, 610, 585, 960, 0, 394, 960],
  #[960, 609, 586, 960, 418, 0, 960, 418, 393, 960, 0, 586, 586, 0, 960, 393, 418, 960, 0, 418, 960, 586, 609, 960],
  #[650, 848, 390, 432, 736, 848, 432, 780, 650, 549, 736, 780, 736, 780, 650, 848, 736, 432, 297, 780, 432, 848, 582, 297],
  #[808, 848, 120, 808, 418, 848, 808, 418, 650, 808, 540, 456, 282, 172, 688, 848, 418, 0, 610, 456, 585, 848, 0, 688],
  #[808, 848, 480, 808, 120, 848, 808, 172, 480, 808, 394, 708, 586, 674, 0, 848, 0, 674, 480, 708, 394, 848, 480, 102],
  #[282, 848, 645, 432, 736, 848, 432, 780, 393, 294, 736, 780, 736, 780, 645, 848, 736, 432, 294, 780, 432, 848, 582, 554],
  #[808, 848, 480, 808, 120, 848, 808, 172, 480, 808, 0, 708, 282, 172, 610, 848, 282, 332, 480, 708, 332, 848, 480, 0],
  #[808, 848, 120, 808, 540, 848, 808, 172, 0, 808, 540, 456, 586, 172, 688, 848, 550, 586, 120, 456, 0, 848, 649, 688],
  #[688, 848, 904, 216, 904, 848, 282, 452, 0, 688, 554, 172, 904, 452, 688, 848, 418, 0, 904, 418, 554, 848, 150, 688],
  #[106, 848, 904, 106, 904, 848, 390, 172, 480, 216, 0, 390, 904, 106, 0, 848, 106, 390, 904, 282, 332, 848, 480, 401],
  #[550, 928, 390, 106, 154, 928, 390, 240, 284, 588, 649, 456, 390, 240, 588, 928, 106, 390, 284, 456, 297, 928, 106, 588],
  #[216, 848, 904, 674, 904, 848, 332, 172, 480, 402, 281, 674, 904, 674, 402, 848, 0, 674, 904, 568, 332, 848, 480, 0],
  #[688, 848, 904, 216, 904, 848, 586, 452, 402, 688, 540, 586, 904, 452, 688, 848, 540, 586, 904, 172, 0, 848, 0, 688],
  #[588, 928, 284, 294, 646, 928, 86, 452, 402, 402, 149, 240, 86, 452, 402, 928, 393, 393, 402, 240, 101, 928, 294, 646],
  #[960, 240, 816, 960, 816, 240, 960, 418, 816, 960, 816, 240, 816, 240, 960, 240, 816, 960, 816, 418, 960, 240, 816, 960],
  #[960, 401, 390, 960, 594, 0, 960, 594, 537, 960, 0, 390, 390, 0, 960, 165, 594, 960, 0, 594, 960, 390, 401, 960],
  #[960, 401, 390, 960, 102, 0, 960, 594, 581, 960, 0, 390, 390, 0, 960, 89, 594, 960, 0, 594, 960, 390, 401, 960],
  #[550, 928, 390, 106, 154, 928, 390, 240, 284, 588, 649, 456, 390, 240, 588, 928, 106, 390, 284, 456, 297, 928, 106, 588],
  #[688, 848, 154, 0, 418, 848, 550, 418, 900, 688, 900, 456, 550, 312, 688, 848, 900, 212, 0, 456, 212, 848, 900, 688],
  #[401, 848, 480, 394, 102, 848, 332, 312, 900, 0, 900, 172, 0, 394, 212, 848, 900, 332, 480, 172, 394, 848, 900, 212],
  #[588, 928, 284, 294, 646, 928, 86, 452, 402, 402, 149, 240, 86, 452, 402, 928, 393, 393, 402, 240, 101, 928, 294, 646],
  #[0, 848, 480, 674, 0, 848, 332, 312, 900, 402, 900, 674, 101, 674, 402, 848, 900, 674, 480, 172, 332, 848, 900, 212],
  #[688, 848, 0, 582, 540, 848, 0, 312, 900, 688, 900, 456, 540, 582, 688, 848, 900, 212, 402, 456, 212, 848, 900, 688],
  #[688, 848, 0, 0, 418, 848, 581, 712, 610, 688, 540, 172, 540, 712, 804, 848, 418, 804, 646, 418, 804, 848, 116, 804],
  #[106, 848, 480, 674, 0, 848, 390, 712, 480, 0, 582, 674, 390, 712, 804, 848, 106, 804, 480, 568, 804, 848, 480, 804],
  #[650, 848, 390, 432, 736, 848, 432, 780, 650, 549, 736, 780, 736, 780, 650, 848, 736, 432, 297, 780, 432, 848, 582, 297],
  #[0, 848, 480, 332, 278, 848, 332, 712, 480, 610, 116, 298, 0, 712, 804, 848, 116, 804, 480, 568, 804, 848, 480, 804],
  #[688, 848, 609, 582, 540, 848, 0, 712, 116, 688, 582, 172, 540, 712, 804, 848, 540, 804, 0, 172, 804, 848, 582, 804],
  #[282, 848, 645, 432, 736, 848, 432, 780, 393, 294, 736, 780, 736, 780, 645, 848, 736, 432, 294, 780, 432, 848, 582, 554],
  #[418, 537, 816, 106, 816, 650, 282, 418, 840, 396, 840, 92, 816, 106, 396, 165, 840, 165, 816, 418, 297, 282, 840, 418],
  #[788, 156, 390, 788, 464, 708, 788, 594, 840, 788, 840, 708, 464, 0, 688, 156, 840, 390, 556, 708, 0, 708, 840, 688],
  #[788, 293, 674, 788, 464, 708, 788, 864, 556, 788, 464, 864, 464, 864, 0, 0, 464, 674, 180, 864, 332, 708, 674, 102],
  #[106, 928, 556, 394, 464, 928, 624, 581, 840, 538, 840, 649, 464, 394, 166, 928, 840, 624, 204, 106, 394, 928, 840, 649],
  #[688, 394, 556, 394, 464, 156, 0, 312, 900, 688, 900, 417, 464, 394, 688, 538, 900, 232, 556, 0, 394, 156, 900, 688],
  #[418, 312, 180, 332, 464, 90, 332, 864, 900, 0, 900, 864, 464, 864, 232, 312, 900, 232, 180, 864, 232, 0, 900, 418],
  #[368, 928, 720, 652, 15, 928, 652, 452, 840, 402, 840, 298, 86, 452, 402, 928, 840, 652, 720, 15, 652, 928, 840, 368],
  #[609, 312, 480, 582, 0, 402, 393, 312, 900, 402, 900, 0, 0, 582, 402, 402, 900, 393, 480, 0, 166, 156, 900, 609],
  #[0, 312, 720, 582, 180, 456, 0, 864, 900, 402, 900, 864, 180, 864, 402, 402, 900, 0, 720, 864, 90, 456, 900, 0],
  #[688, 452, 298, 652, 278, 298, 652, 452, 840, 688, 840, 298, 417, 452, 804, 452, 840, 804, 610, 101, 804, 89, 840, 804],
  #[106, 582, 480, 624, 204, 166, 624, 0, 840, 60, 840, 0, 204, 582, 804, 538, 840, 804, 480, 106, 804, 297, 840, 804],
  #[228, 780, 0, 432, 549, 780, 432, 864, 0, 228, 582, 864, 282, 864, 60, 780, 106, 432, 294, 864, 432, 780, 582, 60],
  #[960, 658, 180, 960, 418, 568, 960, 418, 610, 960, 658, 568, 658, 101, 960, 610, 418, 960, 610, 418, 960, 658, 297, 960],
  #[960, 658, 390, 960, 180, 90, 960, 0, 204, 960, 658, 390, 658, 582, 960, 0, 204, 960, 204, 585, 960, 658, 204, 960],
  #[960, 780, 390, 960, 0, 780, 960, 780, 393, 960, 658, 780, 658, 780, 960, 780, 282, 960, 0, 780, 960, 780, 582, 960],
  #[396, 645, 836, 294, 836, 534, 170, 92, 816, 396, 816, 586, 836, 294, 396, 170, 816, 586, 836, 282, 101, 586, 816, 396],
  #[788, 0, 180, 788, 464, 708, 788, 864, 556, 788, 464, 864, 464, 864, 593, 294, 464, 332, 180, 864, 332, 708, 294, 0],
  #[788, 156, 556, 788, 464, 708, 788, 0, 840, 788, 840, 708, 464, 538, 688, 610, 840, 0, 610, 708, 166, 708, 840, 688],
  #[169, 928, 836, 394, 836, 928, 624, 646, 204, 646, 464, 586, 836, 394, 101, 928, 464, 624, 836, 389, 394, 928, 394, 646],
  #[0, 394, 674, 674, 464, 0, 332, 864, 900, 294, 900, 864, 464, 864, 232, 312, 900, 674, 180, 864, 394, 586, 900, 232],
  #[688, 312, 556, 0, 464, 650, 393, 418, 900, 688, 900, 0, 464, 312, 688, 610, 900, 232, 610, 418, 232, 156, 900, 688],
  #[368, 928, 836, 652, 836, 928, 652, 154, 720, 368, 15, 456, 836, 15, 368, 928, 550, 652, 836, 456, 652, 928, 720, 368],
  #[418, 312, 720, 0, 418, 456, 550, 864, 900, 0, 900, 864, 586, 864, 0, 312, 900, 586, 720, 864, 0, 456, 900, 418],
  #[401, 394, 480, 394, 0, 156, 537, 312, 900, 610, 900, 0, 0, 394, 610, 610, 900, 165, 480, 0, 394, 156, 900, 401],
  #[960, 609, 674, 960, 180, 568, 960, 102, 298, 960, 417, 674, 390, 674, 960, 657, 657, 960, 180, 568, 960, 390, 674, 960],
  #[960, 0, 180, 960, 418, 657, 960, 418, 204, 960, 204, 586, 204, 0, 960, 646, 418, 960, 646, 418, 960, 586, 204, 960],
  #[960, 780, 0, 960, 646, 780, 960, 780, 610, 960, 394, 780, 0, 780, 960, 780, 657, 960, 646, 780, 960, 780, 394, 960],
  #[688, 452, 102, 652, 418, 90, 652, 452, 840, 688, 840, 102, 277, 452, 804, 452, 840, 804, 297, 418, 804, 297, 840, 804],
  #[60, 90, 480, 624, 204, 298, 390, 102, 840, 60, 840, 390, 390, 0, 804, 165, 840, 804, 480, 0, 804, 390, 840, 804],
  #[228, 780, 390, 432, 154, 780, 432, 864, 298, 228, 281, 864, 390, 864, 298, 780, 550, 432, 0, 864, 432, 780, 0, 60],
  #[688, 156, 904, 228, 904, 308, 390, 0, 556, 688, 464, 390, 904, 417, 688, 170, 464, 390, 904, 282, 0, 390, 556, 688],
  #[418, 0, 904, 228, 904, 308, 228, 864, 184, 228, 464, 864, 904, 864, 0, 86, 464, 332, 904, 864, 332, 282, 106, 418],
  #[106, 928, 556, 394, 464, 928, 624, 581, 840, 538, 840, 649, 464, 394, 166, 928, 840, 624, 204, 106, 394, 928, 840, 649],
  #[688, 712, 836, 394, 836, 156, 0, 712, 556, 688, 464, 0, 836, 712, 792, 712, 464, 792, 836, 594, 792, 156, 394, 792],
  #[594, 712, 674, 674, 464, 0, 332, 864, 184, 0, 464, 864, 464, 864, 792, 712, 464, 792, 556, 864, 792, 297, 674, 792],
  #[418, 537, 816, 106, 816, 650, 282, 418, 840, 396, 840, 92, 816, 106, 396, 165, 840, 165, 816, 418, 297, 282, 840, 418],
  #[688, 278, 836, 652, 836, 456, 652, 594, 298, 688, 278, 456, 836, 101, 792, 89, 594, 792, 836, 456, 792, 456, 401, 792],
  #[594, 240, 154, 106, 594, 456, 550, 864, 0, 588, 0, 864, 550, 864, 792, 240, 594, 792, 297, 864, 792, 456, 106, 792],
  #[396, 401, 816, 294, 816, 0, 60, 594, 840, 396, 840, 0, 816, 106, 396, 294, 840, 60, 816, 594, 60, 282, 840, 396],
  #[960, 564, 674, 960, 102, 402, 960, 594, 402, 960, 184, 674, 277, 674, 960, 402, 594, 960, 402, 594, 960, 89, 674, 960],
  #[960, 240, 102, 960, 646, 402, 960, 646, 402, 960, 0, 240, 0, 240, 960, 402, 594, 960, 402, 240, 960, 240, 609, 960],
  #[960, 0, 816, 960, 816, 402, 960, 646, 816, 960, 816, 417, 816, 294, 960, 402, 816, 960, 816, 594, 960, 0, 816, 960],
  #[418, 452, 102, 652, 736, 15, 652, 912, 840, 368, 840, 912, 736, 912, 368, 452, 840, 652, 15, 912, 652, 282, 840, 418],
  #[594, 564, 480, 0, 300, 708, 390, 912, 840, 0, 840, 912, 390, 912, 0, 156, 840, 390, 480, 912, 0, 708, 840, 102],
  #[594, 0, 390, 281, 180, 456, 390, 912, 0, 417, 300, 912, 390, 912, 417, 0, 594, 390, 180, 912, 585, 456, 0, 154],
  #[228, 582, 904, 674, 904, 308, 390, 864, 184, 228, 464, 864, 904, 864, 298, 0, 464, 674, 904, 864, 332, 390, 674, 0],
  #[688, 156, 904, 228, 904, 308, 228, 418, 610, 688, 464, 308, 904, 0, 688, 646, 464, 0, 904, 418, 389, 156, 556, 688],
  #[169, 928, 836, 394, 836, 928, 624, 646, 204, 646, 464, 586, 836, 394, 101, 928, 464, 624, 836, 389, 394, 928, 394, 646],
  #[0, 712, 556, 582, 464, 298, 332, 864, 184, 593, 464, 864, 464, 864, 792, 712, 464, 792, 556, 864, 792, 0, 582, 792],
  #[688, 712, 836, 0, 836, 156, 170, 712, 610, 688, 464, 534, 836, 712, 792, 712, 464, 792, 836, 0, 792, 170, 556, 792],
  #[396, 645, 836, 294, 836, 534, 170, 92, 816, 396, 816, 586, 836, 294, 396, 170, 816, 586, 836, 282, 101, 586, 816, 396],
  #[960, 658, 401, 960, 278, 90, 960, 564, 184, 960, 658, 593, 658, 394, 960, 564, 184, 960, 673, 673, 960, 658, 394, 960],
  #[960, 658, 401, 960, 0, 240, 960, 240, 610, 960, 658, 240, 658, 394, 960, 240, 0, 960, 610, 240, 960, 658, 394, 960],
  #[960, 658, 816, 960, 816, 0, 960, 418, 816, 960, 816, 586, 816, 593, 960, 0, 816, 960, 816, 418, 960, 658, 816, 960],
  #[688, 90, 836, 652, 836, 456, 652, 102, 402, 688, 90, 456, 836, 593, 792, 402, 277, 792, 836, 456, 792, 456, 297, 792],
  #[588, 240, 298, 60, 102, 456, 60, 864, 402, 402, 90, 864, 593, 864, 792, 402, 0, 792, 402, 864, 792, 456, 0, 792],
  #[396, 166, 816, 60, 816, 402, 60, 105, 840, 402, 840, 298, 816, 538, 402, 402, 840, 298, 816, 0, 60, 0, 840, 396],
  #[368, 15, 836, 652, 836, 456, 652, 912, 534, 368, 736, 912, 836, 912, 368, 170, 736, 652, 836, 912, 652, 456, 15, 368],
  #[418, 0, 180, 549, 418, 456, 586, 912, 0, 593, 300, 912, 586, 912, 593, 0, 418, 586, 180, 912, 153, 456, 0, 418],
  #[0, 394, 480, 394, 300, 708, 0, 912, 840, 610, 840, 912, 300, 912, 610, 610, 840, 0, 480, 912, 394, 708, 840, 0]]

def shortlistData10 : List (List ℕ) := [
  [23, 43, 78, 101, 120, 156, 166, 177, 201, 210, 281, 300, 306, 323, 340, 389, 394, 480, 525, 538, 564, 593, 610, 643, 680, 708, 774, 801, 840, 912],
  [23, 43, 77, 90, 116, 153, 172, 178, 198, 225, 284, 294, 305, 323, 360, 389, 394, 464, 526, 549, 568, 593, 610, 643, 660, 712, 777, 786, 836, 928],
  [23, 43, 90, 108, 113, 142, 153, 180, 197, 226, 269, 294, 312, 323, 340, 402, 417, 456, 540, 549, 562, 582, 585, 643, 680, 720, 778, 785, 864, 900],
  [23, 43, 92, 101, 114, 141, 166, 184, 202, 209, 270, 281, 308, 323, 360, 402, 417, 452, 538, 556, 561, 582, 585, 643, 660, 736, 773, 802, 848, 904],
  [23, 43, 92, 102, 113, 142, 165, 184, 201, 210, 281, 300, 306, 325, 330, 387, 404, 480, 525, 538, 564, 579, 616, 657, 674, 708, 774, 801, 848, 904],
  [23, 43, 89, 108, 114, 141, 154, 180, 198, 225, 284, 294, 305, 325, 330, 387, 424, 464, 526, 549, 568, 579, 596, 657, 674, 712, 777, 786, 864, 900],
  [23, 43, 78, 89, 116, 154, 172, 177, 197, 226, 269, 294, 312, 338, 353, 387, 404, 456, 540, 549, 562, 579, 616, 646, 649, 720, 778, 785, 836, 928],
  [23, 43, 77, 102, 120, 156, 165, 178, 202, 209, 270, 281, 308, 338, 353, 387, 424, 452, 538, 556, 561, 579, 596, 646, 649, 736, 773, 802, 840, 912],
  [23, 46, 75, 92, 113, 153, 165, 178, 198, 232, 269, 291, 312, 338, 356, 394, 404, 449, 538, 553, 564, 581, 610, 643, 652, 720, 774, 785, 840, 928],
  [23, 46, 75, 101, 120, 141, 154, 177, 212, 226, 281, 291, 308, 332, 338, 390, 424, 449, 540, 553, 562, 582, 593, 643, 676, 712, 773, 778, 864, 912],
  [23, 57, 75, 92, 102, 142, 165, 178, 209, 232, 269, 298, 308, 338, 353, 387, 408, 452, 538, 547, 556, 581, 624, 649, 660, 706, 774, 785, 840, 928],
  [23, 58, 75, 108, 113, 142, 153, 165, 212, 226, 284, 294, 297, 325, 338, 387, 432, 456, 525, 547, 564, 582, 600, 658, 680, 705, 778, 785, 864, 900],
  [23, 57, 77, 90, 102, 139, 172, 178, 212, 225, 270, 291, 308, 337, 360, 389, 408, 450, 540, 549, 554, 579, 624, 646, 657, 712, 777, 786, 836, 928],
  [23, 58, 77, 102, 113, 139, 156, 165, 210, 232, 281, 291, 300, 330, 340, 390, 432, 449, 526, 553, 564, 579, 600, 657, 674, 708, 773, 786, 864, 904],
  [23, 45, 78, 89, 114, 139, 166, 184, 212, 225, 284, 298, 305, 323, 356, 389, 402, 456, 538, 547, 564, 581, 616, 652, 657, 706, 774, 777, 848, 928],
  [23, 45, 90, 102, 113, 139, 156, 178, 197, 232, 281, 298, 308, 323, 332, 390, 417, 464, 526, 547, 568, 585, 596, 657, 676, 706, 773, 786, 864, 904],
  [23, 45, 90, 99, 116, 142, 153, 178, 197, 232, 267, 294, 312, 332, 337, 404, 417, 450, 540, 554, 561, 582, 585, 643, 676, 720, 773, 786, 864, 904],
  [23, 46, 77, 99, 120, 153, 165, 178, 202, 212, 267, 284, 305, 338, 356, 390, 424, 449, 538, 553, 564, 582, 593, 643, 652, 736, 773, 802, 840, 912],
  [23, 57, 77, 90, 102, 142, 163, 180, 209, 232, 267, 300, 306, 340, 353, 389, 408, 450, 540, 549, 554, 579, 624, 649, 658, 708, 774, 785, 840, 928],
  [23, 57, 78, 101, 114, 154, 163, 172, 201, 212, 267, 284, 294, 337, 360, 389, 432, 450, 525, 554, 564, 579, 600, 646, 657, 736, 786, 801, 836, 904],
  [23, 58, 77, 99, 116, 142, 153, 165, 210, 232, 284, 294, 297, 330, 337, 387, 432, 452, 523, 556, 561, 582, 600, 660, 674, 705, 773, 786, 864, 904],
  [23, 58, 89, 99, 108, 141, 166, 177, 202, 212, 270, 297, 308, 325, 338, 387, 408, 480, 523, 540, 549, 582, 624, 658, 680, 705, 785, 802, 840, 900],
  [23, 45, 90, 102, 113, 142, 163, 184, 201, 212, 281, 298, 308, 323, 332, 389, 402, 480, 523, 540, 562, 581, 616, 657, 676, 706, 774, 801, 848, 904],
  [23, 46, 77, 90, 113, 153, 163, 180, 198, 232, 284, 297, 306, 323, 356, 389, 394, 464, 523, 549, 568, 596, 610, 652, 658, 705, 774, 785, 840, 928],
  [27, 39, 86, 108, 113, 142, 149, 184, 201, 226, 269, 298, 308, 323, 344, 402, 417, 452, 540, 553, 562, 581, 586, 643, 676, 720, 774, 785, 864, 904],
  [27, 39, 92, 105, 114, 141, 170, 180, 198, 209, 270, 277, 312, 323, 356, 402, 417, 456, 534, 556, 561, 581, 586, 643, 664, 736, 777, 802, 848, 900],
  [27, 39, 78, 105, 116, 156, 170, 177, 197, 210, 277, 300, 306, 323, 344, 390, 393, 480, 525, 534, 568, 593, 610, 643, 676, 712, 778, 801, 836, 912],
  [27, 39, 77, 86, 120, 149, 172, 178, 202, 225, 284, 298, 305, 323, 356, 390, 393, 464, 526, 553, 564, 593, 610, 643, 664, 708, 773, 786, 840, 928],
  [27, 39, 86, 108, 113, 142, 149, 184, 201, 226, 284, 297, 306, 325, 330, 387, 420, 464, 525, 554, 564, 579, 600, 658, 673, 708, 774, 785, 864, 904],
  [27, 39, 92, 105, 114, 141, 170, 180, 198, 209, 278, 300, 305, 325, 330, 387, 408, 480, 526, 533, 568, 579, 612, 658, 673, 712, 777, 802, 848, 900],
  [27, 39, 78, 105, 116, 156, 170, 177, 197, 210, 269, 278, 312, 337, 354, 387, 420, 456, 533, 556, 562, 579, 600, 646, 649, 736, 778, 801, 836, 912],
  [27, 39, 77, 86, 120, 149, 172, 178, 202, 225, 270, 297, 308, 337, 354, 387, 408, 452, 540, 554, 561, 579, 612, 646, 649, 720, 773, 786, 840, 928],
  [30, 39, 75, 108, 113, 153, 170, 180, 197, 210, 269, 275, 312, 340, 354, 390, 417, 456, 533, 553, 562, 582, 600, 643, 652, 736, 778, 804, 833, 912],
  [29, 39, 75, 86, 120, 154, 172, 177, 197, 226, 275, 298, 308, 332, 353, 390, 393, 464, 526, 553, 562, 593, 612, 643, 660, 712, 773, 792, 834, 928],
  [39, 57, 75, 86, 108, 141, 154, 180, 209, 226, 270, 277, 306, 344, 353, 387, 424, 452, 531, 540, 554, 581, 624, 646, 673, 712, 777, 804, 834, 912],
  [39, 57, 75, 92, 114, 149, 154, 172, 198, 225, 269, 278, 298, 337, 356, 387, 432, 456, 526, 531, 564, 581, 616, 649, 674, 720, 792, 801, 834, 900],
  [39, 58, 78, 89, 116, 139, 149, 172, 210, 225, 275, 284, 297, 325, 354, 390, 432, 456, 525, 534, 561, 579, 616, 664, 674, 708, 778, 804, 848, 897],
  [39, 58, 86, 89, 108, 139, 156, 177, 197, 226, 269, 275, 308, 330, 353, 390, 424, 464, 526, 533, 553, 579, 624, 658, 676, 712, 792, 802, 836, 897],
  [30, 39, 89, 108, 114, 139, 149, 184, 198, 225, 269, 298, 305, 323, 340, 402, 420, 456, 531, 553, 564, 581, 586, 652, 674, 720, 774, 792, 864, 897],
  [29, 39, 90, 105, 116, 139, 172, 178, 198, 209, 278, 298, 305, 323, 332, 389, 408, 480, 526, 531, 568, 581, 610, 660, 673, 712, 777, 804, 848, 898],
  [30, 39, 83, 105, 116, 153, 172, 178, 197, 202, 267, 277, 312, 332, 354, 390, 417, 464, 525, 554, 561, 582, 600, 643, 660, 736, 786, 804, 833, 904],
  [30, 39, 77, 83, 120, 153, 170, 180, 198, 225, 267, 300, 305, 340, 354, 389, 402, 456, 533, 553, 562, 586, 612, 643, 652, 720, 774, 792, 833, 928],
  [39, 58, 86, 89, 108, 141, 147, 180, 202, 225, 267, 284, 305, 325, 354, 390, 424, 464, 526, 533, 553, 579, 624, 664, 674, 708, 786, 804, 840, 897],
  [39, 57, 77, 90, 116, 147, 156, 170, 198, 225, 267, 278, 300, 337, 354, 389, 432, 456, 526, 533, 562, 579, 616, 649, 676, 720, 792, 801, 836, 898],
  [39, 58, 83, 92, 105, 142, 153, 180, 197, 226, 269, 278, 305, 330, 356, 387, 424, 464, 523, 533, 556, 582, 624, 658, 673, 712, 792, 802, 833, 900],
  [39, 57, 78, 83, 116, 149, 154, 172, 201, 226, 269, 278, 298, 344, 353, 387, 432, 452, 523, 540, 562, 581, 616, 646, 673, 720, 785, 804, 834, 904],
  [29, 39, 90, 105, 116, 142, 147, 184, 197, 226, 278, 298, 305, 323, 332, 393, 420, 464, 523, 556, 562, 582, 593, 660, 673, 712, 773, 792, 864, 898],
  [29, 39, 90, 108, 113, 147, 170, 180, 198, 201, 270, 297, 306, 323, 340, 389, 408, 480, 523, 534, 568, 581, 610, 652, 673, 720, 785, 804, 840, 898],
  [27, 46, 71, 105, 116, 156, 165, 178, 202, 209, 277, 291, 312, 332, 338, 390, 393, 480, 525, 534, 561, 600, 610, 643, 680, 708, 778, 804, 833, 912],
  [27, 45, 71, 92, 114, 149, 166, 184, 202, 225, 270, 291, 308, 337, 360, 393, 402, 452, 534, 554, 561, 585, 612, 643, 652, 720, 773, 792, 834, 928],
  [27, 54, 71, 92, 105, 142, 165, 184, 209, 226, 269, 298, 305, 338, 356, 387, 404, 456, 533, 547, 556, 586, 624, 649, 658, 708, 774, 792, 833, 928],
  [27, 54, 71, 108, 113, 156, 165, 170, 201, 210, 270, 277, 297, 344, 354, 387, 432, 452, 525, 547, 568, 586, 596, 646, 657, 736, 786, 804, 833, 904],
  [29, 43, 71, 108, 114, 154, 166, 177, 201, 212, 270, 275, 308, 344, 353, 389, 424, 450, 534, 549, 568, 586, 593, 643, 652, 736, 777, 802, 836, 912],
  [29, 43, 71, 90, 116, 142, 165, 178, 209, 232, 275, 294, 312, 332, 353, 393, 404, 450, 534, 556, 561, 585, 610, 643, 664, 708, 773, 778, 848, 928],
  [43, 54, 71, 89, 108, 141, 154, 177, 212, 226, 270, 277, 312, 338, 353, 387, 420, 456, 531, 540, 549, 586, 624, 646, 680, 705, 777, 802, 836, 912],
  [43, 53, 71, 92, 114, 141, 154, 166, 209, 232, 278, 281, 300, 330, 353, 387, 432, 452, 526, 531, 568, 585, 612, 660, 673, 706, 773, 802, 848, 904],
  [54, 57, 71, 90, 108, 139, 156, 165, 209, 226, 269, 275, 298, 340, 353, 390, 432, 456, 526, 533, 547, 585, 624, 658, 680, 708, 792, 804, 834, 897],
  [30, 45, 71, 89, 114, 139, 166, 177, 212, 232, 275, 298, 308, 332, 353, 389, 408, 450, 533, 547, 568, 586, 612, 652, 658, 705, 774, 777, 848, 928],
  [53, 58, 71, 89, 108, 139, 156, 166, 210, 225, 270, 275, 297, 340, 354, 389, 432, 456, 525, 534, 547, 586, 624, 657, 680, 708, 792, 804, 833, 898],
  [29, 46, 71, 90, 113, 139, 165, 178, 212, 232, 275, 297, 308, 332, 354, 390, 408, 449, 534, 547, 568, 585, 612, 652, 657, 706, 773, 778, 848, 928],
  [46, 57, 71, 90, 116, 139, 149, 178, 204, 225, 269, 278, 291, 337, 360, 408, 420, 450, 531, 540, 549, 585, 610, 646, 680, 720, 778, 816, 836, 897],
  [29, 58, 71, 105, 116, 139, 166, 177, 204, 210, 278, 291, 300, 330, 337, 389, 408, 480, 526, 531, 549, 600, 610, 660, 680, 705, 777, 816, 836, 898],
  [30, 53, 71, 105, 114, 139, 166, 184, 204, 209, 281, 291, 300, 330, 340, 389, 402, 480, 525, 531, 554, 600, 612, 660, 673, 706, 774, 816, 833, 904],
  [45, 54, 71, 90, 113, 139, 149, 184, 204, 226, 270, 281, 291, 340, 360, 402, 420, 449, 531, 540, 554, 585, 612, 646, 673, 720, 773, 816, 834, 904],
  [29, 54, 71, 90, 105, 147, 165, 170, 204, 240, 267, 300, 305, 340, 354, 390, 408, 449, 526, 547, 568, 593, 612, 649, 660, 706, 773, 786, 840, 928],
  [30, 45, 71, 89, 114, 147, 170, 180, 204, 225, 267, 294, 305, 340, 360, 389, 408, 450, 533, 547, 568, 586, 612, 646, 649, 720, 780, 786, 833, 928],
  [30, 57, 71, 108, 114, 141, 163, 180, 202, 209, 267, 277, 294, 344, 353, 402, 424, 452, 531, 549, 554, 585, 596, 646, 664, 736, 780, 816, 834, 897],
  [29, 46, 71, 105, 114, 154, 163, 180, 204, 209, 267, 278, 305, 344, 356, 389, 424, 450, 531, 549, 568, 586, 596, 646, 649, 736, 780, 802, 833, 912],
  [29, 54, 71, 90, 105, 147, 165, 170, 204, 240, 270, 291, 312, 337, 356, 393, 404, 450, 523, 556, 561, 596, 610, 646, 664, 705, 773, 786, 840, 928],
  [53, 58, 71, 92, 105, 141, 147, 166, 202, 240, 270, 281, 291, 338, 356, 404, 424, 449, 523, 534, 556, 593, 610, 664, 673, 708, 773, 816, 840, 898],
  [54, 57, 71, 90, 108, 142, 149, 163, 201, 240, 269, 275, 298, 340, 353, 408, 420, 450, 523, 540, 549, 593, 610, 658, 680, 708, 774, 816, 840, 897],
  [29, 58, 71, 108, 113, 142, 163, 180, 201, 210, 275, 294, 297, 330, 340, 389, 408, 480, 523, 534, 549, 600, 610, 657, 680, 708, 780, 816, 833, 898],
  [27, 53, 92, 102, 105, 135, 172, 178, 202, 209, 270, 291, 312, 325, 338, 393, 404, 480, 525, 534, 554, 579, 624, 664, 673, 708, 785, 804, 840, 898],
  [27, 53, 77, 102, 120, 135, 156, 170, 210, 225, 278, 291, 300, 330, 337, 393, 432, 452, 526, 553, 562, 579, 596, 657, 676, 712, 773, 792, 864, 898],
  [27, 45, 92, 102, 113, 135, 170, 180, 201, 210, 270, 277, 306, 323, 360, 408, 417, 452, 534, 547, 568, 581, 586, 652, 657, 736, 777, 804, 848, 898],
  [27, 46, 86, 101, 120, 135, 156, 177, 201, 226, 277, 297, 306, 323, 332, 394, 420, 464, 525, 547, 564, 586, 593, 658, 680, 708, 774, 792, 864, 897],
  [43, 53, 78, 89, 114, 135, 154, 172, 212, 225, 275, 284, 294, 325, 360, 393, 432, 450, 525, 534, 568, 579, 612, 657, 674, 712, 778, 801, 848, 900],
  [43, 54, 78, 89, 101, 135, 156, 177, 210, 232, 269, 275, 312, 340, 354, 394, 420, 449, 533, 538, 556, 579, 624, 649, 674, 708, 774, 801, 840, 912],
  [30, 43, 89, 101, 114, 135, 172, 177, 202, 212, 277, 294, 312, 323, 332, 393, 402, 480, 525, 531, 564, 582, 616, 664, 674, 705, 778, 801, 848, 900],
  [30, 43, 77, 102, 113, 135, 153, 180, 210, 232, 277, 300, 306, 323, 344, 394, 417, 452, 531, 549, 568, 586, 596, 652, 674, 705, 774, 777, 864, 912],
  [30, 57, 75, 101, 114, 135, 170, 180, 204, 209, 269, 275, 294, 340, 360, 408, 417, 450, 533, 547, 556, 582, 600, 649, 658, 736, 778, 816, 833, 900],
  [45, 58, 75, 86, 113, 135, 153, 180, 204, 226, 275, 284, 294, 325, 360, 394, 417, 464, 526, 533, 547, 600, 612, 658, 680, 705, 777, 816, 834, 900],
  [46, 53, 75, 86, 120, 135, 153, 178, 204, 225, 275, 284, 297, 325, 354, 394, 420, 464, 525, 538, 547, 593, 612, 660, 680, 706, 774, 816, 840, 897],
  [29, 54, 75, 101, 120, 135, 170, 177, 204, 210, 270, 275, 297, 340, 354, 408, 420, 449, 538, 547, 556, 582, 593, 649, 660, 736, 773, 816, 840, 898],
  [54, 57, 75, 92, 101, 135, 154, 172, 209, 226, 270, 277, 291, 338, 360, 393, 432, 452, 525, 531, 554, 582, 624, 660, 673, 712, 792, 804, 833, 898],
  [30, 45, 75, 102, 113, 135, 153, 178, 212, 232, 277, 291, 312, 332, 338, 394, 420, 449, 531, 554, 564, 581, 600, 652, 673, 706, 774, 777, 864, 912],
  [53, 58, 75, 92, 102, 135, 153, 172, 210, 225, 269, 278, 291, 337, 360, 394, 432, 452, 526, 531, 553, 581, 624, 660, 674, 712, 792, 804, 834, 897],
  [29, 46, 75, 101, 114, 135, 154, 177, 212, 232, 278, 291, 312, 332, 337, 393, 420, 450, 531, 553, 564, 582, 600, 652, 674, 705, 773, 778, 864, 912],
  [54, 57, 78, 83, 101, 135, 156, 170, 201, 240, 267, 277, 300, 344, 354, 402, 417, 452, 525, 538, 547, 596, 616, 657, 676, 706, 774, 816, 833, 904],
  [30, 53, 83, 102, 105, 135, 153, 170, 204, 240, 267, 300, 306, 325, 344, 404, 417, 450, 525, 547, 568, 586, 596, 658, 676, 705, 774, 785, 864, 904],
  [30, 57, 77, 99, 116, 135, 172, 178, 202, 209, 267, 277, 294, 338, 360, 408, 417, 452, 531, 549, 554, 582, 600, 649, 660, 736, 780, 816, 833, 898],
  [53, 58, 77, 86, 99, 135, 153, 172, 202, 240, 267, 284, 294, 337, 360, 402, 417, 452, 526, 531, 553, 600, 612, 660, 674, 705, 773, 816, 834, 904],
  [30, 53, 83, 102, 105, 135, 153, 170, 204, 240, 269, 291, 312, 330, 340, 402, 420, 449, 523, 556, 562, 581, 600, 660, 673, 706, 774, 785, 864, 904],
  [29, 46, 83, 105, 116, 135, 154, 177, 204, 226, 278, 291, 312, 325, 330, 393, 420, 464, 523, 549, 562, 582, 600, 660, 680, 705, 780, 785, 864, 898],
  [29, 58, 78, 99, 116, 135, 172, 177, 201, 210, 275, 294, 297, 325, 344, 394, 404, 480, 523, 534, 549, 593, 616, 664, 674, 708, 780, 816, 834, 897],
  [30, 45, 89, 99, 116, 135, 170, 177, 204, 210, 275, 294, 312, 325, 330, 393, 404, 480, 523, 533, 562, 582, 616, 664, 676, 705, 780, 801, 848, 898],
  [27, 45, 86, 99, 120, 156, 166, 177, 197, 202, 263, 298, 308, 332, 337, 393, 402, 480, 526, 533, 562, 585, 612, 643, 680, 720, 792, 801, 834, 900],
  [27, 45, 78, 99, 116, 149, 166, 184, 201, 210, 263, 284, 306, 337, 360, 394, 417, 452, 534, 554, 561, 581, 600, 643, 652, 736, 777, 804, 834, 912],
  [27, 53, 92, 102, 105, 142, 163, 184, 197, 210, 263, 300, 306, 330, 337, 393, 404, 480, 525, 534, 554, 579, 624, 657, 676, 712, 792, 801, 836, 898],
  [27, 54, 78, 101, 120, 149, 163, 172, 201, 210, 263, 284, 297, 337, 354, 394, 432, 452, 525, 554, 561, 579, 596, 646, 664, 736, 786, 804, 840, 897],
  [29, 43, 78, 83, 116, 154, 166, 177, 197, 232, 263, 300, 306, 344, 353, 393, 404, 450, 534, 549, 568, 585, 610, 643, 652, 720, 778, 785, 836, 928],
  [30, 43, 83, 101, 120, 141, 166, 177, 202, 212, 263, 281, 308, 332, 354, 402, 424, 449, 533, 556, 562, 582, 585, 643, 664, 736, 778, 801, 848, 900],
  [43, 54, 78, 89, 101, 141, 147, 184, 212, 226, 263, 284, 305, 338, 360, 394, 420, 449, 533, 538, 556, 579, 624, 646, 673, 712, 777, 802, 836, 912],
  [43, 54, 77, 90, 113, 147, 156, 165, 198, 232, 263, 281, 300, 340, 354, 394, 432, 449, 526, 533, 568, 579, 612, 649, 674, 720, 786, 801, 840, 900],
  [29, 46, 75, 86, 113, 147, 165, 184, 204, 226, 263, 297, 306, 344, 356, 394, 404, 449, 538, 547, 564, 581, 616, 646, 649, 720, 780, 785, 834, 928],
  [45, 54, 75, 92, 113, 142, 147, 184, 197, 226, 263, 281, 298, 338, 356, 404, 417, 456, 533, 538, 547, 582, 616, 649, 676, 720, 780, 816, 833, 898],
  [46, 57, 75, 86, 101, 149, 154, 163, 204, 240, 263, 284, 306, 337, 360, 393, 420, 450, 525, 531, 564, 600, 610, 646, 680, 705, 778, 801, 836, 912],
  [30, 45, 75, 102, 113, 149, 163, 184, 204, 210, 263, 281, 306, 340, 360, 394, 420, 449, 531, 554, 564, 581, 600, 646, 649, 736, 780, 801, 834, 912],
  [45, 54, 78, 83, 120, 139, 156, 177, 197, 226, 263, 281, 298, 340, 353, 402, 420, 456, 533, 538, 547, 585, 612, 646, 680, 720, 780, 816, 834, 897],
  [53, 58, 78, 83, 105, 139, 156, 166, 197, 240, 263, 281, 300, 340, 354, 402, 417, 456, 525, 534, 547, 600, 612, 657, 680, 706, 778, 816, 833, 900],
  [54, 57, 77, 90, 99, 139, 149, 172, 198, 240, 263, 284, 298, 337, 356, 402, 417, 456, 526, 531, 549, 596, 616, 664, 674, 705, 777, 816, 834, 900],
  [45, 58, 86, 89, 99, 139, 149, 166, 204, 240, 263, 284, 305, 330, 356, 402, 424, 449, 526, 531, 564, 581, 616, 664, 673, 706, 777, 802, 848, 900],
  [30, 57, 77, 83, 102, 149, 163, 172, 202, 240, 263, 298, 308, 344, 353, 393, 402, 452, 523, 549, 562, 596, 616, 646, 664, 705, 780, 785, 834, 928],
  [45, 58, 83, 92, 102, 142, 149, 163, 201, 240, 263, 281, 308, 330, 353, 402, 424, 452, 523, 534, 561, 581, 616, 664, 676, 706, 780, 802, 848, 897],
  [46, 53, 83, 92, 105, 141, 154, 163, 198, 240, 263, 281, 306, 330, 356, 404, 424, 449, 523, 534, 568, 581, 610, 657, 676, 712, 780, 801, 848, 898],
  [29, 54, 78, 83, 105, 154, 163, 172, 197, 240, 263, 298, 305, 344, 356, 393, 404, 450, 523, 549, 568, 596, 610, 646, 657, 712, 780, 786, 833, 928],
  [54, 57, 77, 90, 99, 142, 147, 165, 212, 232, 263, 284, 298, 337, 356, 393, 432, 450, 523, 533, 556, 582, 624, 664, 674, 705, 786, 801, 840, 900],
  [29, 46, 90, 99, 116, 147, 165, 184, 198, 201, 263, 297, 306, 332, 337, 394, 404, 480, 523, 534, 561, 581, 616, 652, 674, 720, 792, 804, 834, 897],
  [53, 58, 78, 89, 99, 141, 147, 166, 212, 232, 263, 284, 297, 338, 356, 394, 432, 449, 523, 534, 556, 581, 624, 664, 673, 706, 785, 802, 840, 900],
  [30, 45, 89, 99, 116, 147, 166, 184, 197, 202, 263, 298, 305, 332, 338, 393, 404, 480, 523, 533, 562, 582, 616, 652, 673, 720, 792, 804, 833, 898],
  [27, 54, 77, 99, 120, 156, 165, 170, 198, 209, 270, 277, 297, 338, 356, 387, 432, 456, 519, 556, 561, 586, 596, 649, 658, 736, 792, 802, 833, 900],
  [27, 53, 86, 99, 108, 141, 166, 184, 202, 209, 270, 297, 306, 325, 344, 387, 404, 480, 519, 540, 554, 585, 624, 658, 673, 708, 785, 804, 834, 904],
  [27, 46, 92, 101, 114, 149, 163, 184, 198, 201, 269, 278, 305, 323, 360, 394, 420, 464, 519, 553, 564, 586, 593, 652, 658, 736, 792, 802, 836, 897],
  [27, 46, 86, 101, 120, 141, 163, 180, 202, 209, 277, 297, 306, 323, 332, 390, 408, 480, 519, 540, 561, 585, 610, 658, 680, 708, 778, 804, 848, 897],
  [43, 53, 83, 92, 102, 142, 153, 178, 197, 232, 269, 278, 312, 330, 353, 387, 420, 464, 519, 538, 556, 585, 624, 660, 673, 706, 785, 802, 836, 904],
  [43, 53, 78, 83, 120, 141, 154, 166, 212, 225, 278, 281, 300, 325, 354, 387, 432, 456, 519, 540, 562, 585, 612, 657, 680, 706, 778, 801, 848, 900],
  [30, 43, 89, 101, 114, 141, 147, 180, 198, 232, 277, 294, 312, 323, 332, 394, 417, 464, 519, 556, 561, 586, 596, 664, 674, 705, 777, 786, 864, 900],
  [29, 43, 78, 101, 114, 147, 166, 184, 201, 212, 278, 300, 305, 323, 344, 389, 394, 480, 519, 538, 564, 593, 616, 652, 673, 706, 777, 802, 836, 912],
  [54, 57, 75, 92, 101, 141, 147, 170, 198, 240, 270, 277, 291, 338, 360, 408, 420, 449, 519, 538, 556, 593, 610, 660, 673, 712, 777, 816, 836, 898],
  [46, 53, 75, 92, 114, 141, 147, 184, 198, 225, 278, 281, 291, 325, 360, 394, 420, 464, 519, 538, 553, 593, 612, 660, 674, 712, 780, 816, 834, 897],
  [46, 57, 75, 86, 101, 149, 154, 163, 204, 240, 269, 275, 308, 344, 354, 390, 424, 449, 519, 540, 562, 593, 616, 649, 676, 706, 778, 801, 836, 912],
  [53, 58, 75, 86, 108, 142, 153, 163, 197, 240, 269, 275, 294, 344, 353, 404, 424, 450, 519, 540, 553, 593, 610, 658, 676, 712, 778, 816, 836, 897],
  [46, 53, 77, 83, 120, 139, 156, 178, 198, 225, 278, 281, 291, 330, 356, 389, 424, 464, 519, 538, 553, 596, 610, 657, 676, 712, 780, 816, 833, 898],
  [30, 45, 83, 102, 120, 139, 149, 178, 204, 225, 281, 291, 308, 325, 330, 390, 424, 464, 519, 554, 561, 585, 596, 664, 676, 706, 780, 786, 864, 897],
  [29, 46, 86, 99, 120, 139, 165, 178, 204, 209, 275, 297, 308, 325, 330, 390, 408, 480, 519, 538, 561, 585, 612, 660, 680, 706, 780, 802, 848, 897],
  [45, 58, 86, 89, 99, 139, 149, 166, 204, 240, 270, 275, 308, 325, 360, 408, 417, 450, 519, 540, 561, 586, 612, 658, 680, 705, 777, 802, 848, 900],
  [54, 57, 78, 83, 101, 141, 154, 163, 212, 232, 267, 277, 300, 344, 354, 390, 432, 449, 519, 540, 554, 585, 624, 657, 676, 706, 786, 801, 836, 904],
  [29, 46, 83, 101, 120, 154, 163, 180, 198, 201, 267, 278, 305, 332, 354, 389, 424, 464, 519, 553, 562, 586, 596, 652, 657, 736, 792, 804, 833, 898],
  [53, 58, 77, 83, 102, 142, 153, 163, 212, 232, 267, 278, 300, 344, 353, 389, 432, 450, 519, 540, 553, 586, 624, 658, 676, 705, 785, 802, 836, 904],
  [30, 45, 83, 102, 120, 153, 163, 180, 197, 202, 267, 277, 306, 332, 353, 390, 424, 464, 519, 554, 561, 585, 596, 652, 658, 736, 792, 804, 834, 897],
  [46, 57, 77, 86, 99, 147, 156, 165, 202, 240, 267, 277, 306, 344, 356, 390, 424, 449, 519, 538, 564, 593, 616, 649, 674, 708, 780, 801, 834, 912],
  [29, 58, 86, 99, 108, 142, 147, 165, 201, 240, 267, 294, 305, 325, 344, 404, 424, 450, 519, 553, 564, 586, 593, 664, 674, 708, 780, 786, 864, 897],
  [30, 53, 89, 99, 108, 141, 147, 170, 198, 240, 267, 294, 312, 325, 338, 404, 417, 456, 519, 553, 562, 586, 596, 664, 676, 705, 780, 785, 864, 898],
  [45, 54, 78, 89, 99, 147, 156, 170, 197, 240, 267, 277, 312, 338, 356, 390, 417, 456, 519, 538, 561, 596, 616, 649, 676, 706, 780, 802, 833, 912]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem tables8_valid : ValidTables 8 tables8 :=
  ⟨by decide +kernel, by decide +kernel, rfl, by decide +kernel, rfl, by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem tables10_valid : ValidTables 10 tables10 :=
  ⟨by decide +kernel, by decide +kernel, rfl, by decide +kernel, rfl, by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem tables8_shortlist : shortlist tables8 = shortlistData8 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem tables8_impossible : packSearch 4 (shortlist tables8) = false := by rw [tables8_shortlist]; decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem tables10_shortlist : shortlist tables10 = shortlistData10 := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem tables10_impossible : packSearch 6 (shortlist tables10) = false := by rw [tables10_shortlist]; decide +kernel

set_option maxRecDepth 20000 in
private theorem noSmallColor8 (c : (SimpleGraph.johnson 8 4).Coloring (Fin 5)) : False :=
  no_pack_of_tables tables8_valid tables8_impossible (mem_smallSets.mpr ⟨by decide, by rw [card_pointSet]; decide⟩) (colorsToSystems c)
    (codes_to_system (by decide) c) (different_colors_disjoint c)

set_option maxRecDepth 20000 in
private theorem noSmallColor10 (c : (SimpleGraph.johnson 10 4).Coloring (Fin 7)) : False :=
  no_pack_of_tables tables10_valid tables10_impossible (mem_smallSets.mpr ⟨by decide, by rw [card_pointSet]; decide⟩) (colorsToSystems c)
    (codes_to_system (by decide) c) (different_colors_disjoint c)

end OMA.E835

open OMA.E835

set_option maxRecDepth 20000 in
theorem OMA.solution : type_of% @Erdos835.chromaticNumber_johnson_2k_k_lower_bound := by
  intro k hk hk'
  apply lt_of_not_ge
  intro h
  obtain ⟨c⟩ := SimpleGraph.chromaticNumber_le_iff_colorable.mp h
  interval_cases k
  · exact (by decide : ¬ 2 ∣ Nat.choose 5 (2-1))
      (design_divisibility (by decide) (by decide) (c.comp (vertexExtension (n:=5) (m:=2) 1)))
  · exact noSmallColor8 c
  · exact (by decide : ¬ 2 ∣ Nat.choose 7 (2-1))
      (design_divisibility (by decide) (by decide) (c.comp (vertexExtension (n:=7) (m:=2) 3)))
  · exact noSmallColor10 (c.comp (vertexExtension (n:=10) (m:=4) 2))
  · exact (by decide : ¬ 2 ∣ Nat.choose 9 (2-1))
      (design_divisibility (by decide) (by decide) (c.comp (vertexExtension (n:=9) (m:=2) 5)))
  · exact (by decide : ¬ 3 ∣ Nat.choose 11 (3-1))
      (design_divisibility (by decide) (by decide) (c.comp (vertexExtension (n:=11) (m:=3) 5)))