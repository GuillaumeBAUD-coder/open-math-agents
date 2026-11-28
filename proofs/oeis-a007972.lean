import OMAStatements.S_oeis_a007972

namespace OMA.S_oeis_a007972

/- Index an interval from one and extend its permutation by the identity outside it. -/
def reflectInterval (a b t : Nat) := if a ≤ t ∧ t ≤ b then a+b-t else t

def idxOne (m : Nat) (f : Nat → Nat) : Prop :=
  ∃ i j, 1 ≤ i ∧ i < j ∧ j ≤ m ∧ f = reflectInterval i j

def idxSphere (m : Nat) : Set (Nat → Nat) :=
  {f | f ≠ id ∧ ¬idxOne m f ∧ ∃ g h, idxOne m g ∧ idxOne m h ∧ f = g ∘ h}

def idxCore (m : Nat) : Set (Nat → Nat) :=
  {f ∈ idxSphere m | f 1 ≠ 1 ∧ f m ≠ m}

theorem reflectInterval_invol {a b t : Nat} : reflectInterval a b (reflectInterval a b t) = t := by
  unfold reflectInterval
  split_ifs <;> omega

def wordIndex (w : List Nat) (t : Nat) :=
  if h : 1 ≤ t ∧ t ≤ w.length then w[t-1]'(by omega) + 1 else t

theorem wordIndex_range (m : Nat) : wordIndex (List.range m) = id := by
  funext t
  unfold wordIndex
  split <;> simp_all [List.getElem_range]

theorem wordIndex_inj {w v : List Nat} (hlen : w.length = v.length)
    (h : wordIndex w = wordIndex v) : w = v := by
  apply List.ext_getElem hlen
  intro i hi hi'
  have ht := congrFun h (i+1)
  simpa [wordIndex, show i+1 ≤ w.length by omega, show i+1 ≤ v.length by omega] using ht

theorem wordIndex_flip (a b c : List Nat) :
    wordIndex (a ++ b.reverse ++ c) =
      wordIndex (a ++ b ++ c) ∘ reflectInterval (a.length+1) (a.length+b.length) := by
  funext t
  simp only [Function.comp_apply, reflectInterval]
  by_cases h₀ : t = 0
  · subst t
    simp [wordIndex]
  by_cases hl : t ≤ a.length
  · have h : ¬(a.length+1 ≤ t ∧ t ≤ a.length+b.length) := by omega
    rw [if_neg h]
    simp only [wordIndex, List.length_append, List.length_reverse]
    split_ifs
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by omega),
          List.getElem_append_left (by simp; omega), List.getElem_append_left (by omega)]
    · rfl
  by_cases hr : a.length+b.length < t
  · have h : ¬(a.length+1 ≤ t ∧ t ≤ a.length+b.length) := by omega
    rw [if_neg h]
    simp only [wordIndex, List.length_append, List.length_reverse]
    split_ifs
    · rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by simp; omega)]
      simp only [List.length_append, List.length_reverse]
    · rfl
  have h : a.length+1 ≤ t ∧ t ≤ a.length+b.length := by omega
  rw [if_pos h]
  simp only [wordIndex, List.length_append, List.length_reverse]
  split_ifs <;> try omega
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega),
      List.getElem_reverse, List.getElem_append_left (by simp; omega),
      List.getElem_append_right (by omega)]
  congr 2
  omega

theorem step_to_index {u v : List Nat} (h : RevStep u v) :
    v.length = u.length ∧ ∃ i j, 1 ≤ i ∧ i < j ∧ j ≤ u.length ∧ 
       wordIndex v = wordIndex u ∘ reflectInterval i j := by
  obtain ⟨a,b,c,hb,rfl,rfl⟩ := h
  refine ⟨by simp, a.length+1, a.length+b.length, by omega, by omega, by simp, ?_⟩
  exact wordIndex_flip a b c

theorem step_from_interval (u : List Nat) {i j : Nat} (hi : 1 ≤ i) (hij : i < j)
    (hj : j ≤ u.length) : ∃ v, RevStep u v ∧ 
      wordIndex v = wordIndex u ∘ reflectInterval i j := by
  let a := u.take (i-1)
  let b := (u.drop (i-1)).take (j-(i-1))
  let c := (u.drop (i-1)).drop (j-(i-1))
  have ha : a.length = i-1 := by simp [a, Nat.min_eq_left (by omega : i-1 ≤ u.length)]
  have hb : b.length = j-(i-1) := by
    simp [b, Nat.min_eq_left (by omega : j-(i-1) ≤ u.length-(i-1))]
  have hu : u = a++b++c := by simp [a,b,c,List.append_assoc]
  refine ⟨a++b.reverse++c, ⟨a,b,c,by omega,hu,rfl⟩, ?_⟩
  rw [wordIndex_flip, ←hu, ha, hb]
  congr 2 <;> omega

theorem step_index_iff {u v : List Nat} : RevStep u v ↔ 
    v.length = u.length ∧ ∃ i j, 1 ≤ i ∧ i < j ∧ j ≤ u.length ∧ 
       wordIndex v = wordIndex u ∘ reflectInterval i j := by
  refine ⟨step_to_index, ?_⟩
  rintro ⟨hlen,i,j,hi,hij,hj,he⟩
  obtain ⟨v',hv',he'⟩ := step_from_interval u hi hij hj
  obtain rfl : v = v' := wordIndex_inj (hlen.trans (step_to_index hv').1.symm) (he.trans he'.symm)
  exact hv'

theorem sphere_length {m : Nat} {v : List Nat} (hv : v ∈ distTwoPerms m) :
    v.length = m := by
  obtain ⟨_,_,u,hu,hv⟩ := hv
  have hh := (step_to_index hv).1.trans (step_to_index hu).1
  simpa using hh

theorem image_idxSphere (m : Nat) : wordIndex '' distTwoPerms m = idxSphere m := by
  ext f
  constructor
  · rintro ⟨w,hw,rfl⟩
    have hlen := sphere_length hw
    obtain ⟨hid,hone,u,hu,hw⟩ := hw
    obtain ⟨huL,i,j,hi,hij,hj,he⟩ := step_to_index hu
    obtain ⟨_,k,l,hk,hkl,hl,hf⟩ := step_to_index hw
    simp only [List.length_range, wordIndex_range, Function.id_comp] at huL hj he
    refine ⟨?_,?_,_,_,⟨i,j,hi,hij,hj,rfl⟩,⟨k,l,hk,hkl,by omega,rfl⟩,he ▸ hf⟩
    · intro he
      apply hid
      exact wordIndex_inj (by simpa using hlen) (he.trans (wordIndex_range m).symm)
    · rintro ⟨a,b,ha,hab,hb,hw⟩
      apply hone
      apply step_index_iff.mpr
      simpa only [List.length_range, wordIndex_range, Function.id_comp] using
        And.intro hlen (Exists.intro a (Exists.intro b ⟨ha,hab,hb,hw⟩))
  · rintro ⟨hid,hone,g,h,⟨i,j,hi,hij,hj,rfl⟩,⟨k,l,hk,hkl,hl,rfl⟩,rfl⟩
    obtain ⟨u,hu,heu⟩ := step_from_interval (List.range m) hi hij (by simpa using hj)
    obtain ⟨w,hw,hew⟩ := step_from_interval u hk hkl (by
      have huL := (step_to_index hu).1
      simp only [List.length_range] at huL
      omega)
    simp only [wordIndex_range, Function.id_comp] at heu
    rw [heu] at hew
    refine ⟨w,⟨?_,?_,u,hu,hw⟩,hew⟩
    · intro he
      apply hid
      rw [←hew,he,wordIndex_range]
    · intro he
      obtain ⟨_,a,b,ha,hab,hb,heab⟩ := step_to_index he
      simp only [List.length_range, wordIndex_range, Function.id_comp] at hb heab
      exact hone ⟨a,b,ha,hab,hb,hew.symm.trans heab⟩

theorem idxSphere_card (m : Nat) : (distTwoPerms m).ncard = (idxSphere m).ncard := by
  rw [← image_idxSphere]
  exact (Set.InjOn.ncard_image (fun a ha b hb => wordIndex_inj
    ((sphere_length ha).trans (sphere_length hb).symm))).symm

/- A permutation moving both endpoints comes from a whole-interval reversal and a proper reversal, or from a proper initial and final interval. -/
theorem reflection_eq {i j k l : Nat} (hij : i < j) (hkl : k < l)
    (h : reflectInterval i j = reflectInterval k l) : i = k ∧ j = l := by
  have hi := congrFun h i
  have hk := congrFun h k
  unfold reflectInterval at hi hk
  split_ifs at hi hk <;> omega

def prefixSuffix (m a b t : Nat) := reflectInterval 1 a (reflectInterval b m t)
def suffixPrefix (m a b t : Nat) := reflectInterval b m (reflectInterval 1 a t)

theorem prefixSuffix_first {m a b : Nat} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    prefixSuffix m a b 1 = a := by
  unfold prefixSuffix reflectInterval
  split_ifs <;> omega

theorem prefixSuffix_last {m a b : Nat} (ha : a < m) (hb : 2 ≤ b) (hbm : b < m) :
    prefixSuffix m a b m = if b ≤ a then a+1-b else b := by
  unfold prefixSuffix reflectInterval
  split_ifs <;> omega

theorem prefixSuffix_inj {m a b c d : Nat} (ha : 2 ≤ a) (ham : a < m) (hb : 2 ≤ b) (hbm : b < m)
    (hc : 2 ≤ c) (hcm : c < m) (hd : 2 ≤ d) (hdm : d < m)
    (h : prefixSuffix m a b = prefixSuffix m c d) : a = c ∧ b = d := by
  have hf := congrFun h 1
  have hl := congrFun h m
  rw [prefixSuffix_first ha hb, prefixSuffix_first hc hd] at hf
  rw [prefixSuffix_last ham hb hbm, prefixSuffix_last hcm hd hdm] at hl
  split_ifs at hl <;> omega

theorem suffixPrefix_inj {m a b c d : Nat} (ha : 2 ≤ a) (ham : a < m) (hb : 2 ≤ b) (hbm : b < m)
    (hc : 2 ≤ c) (hcm : c < m) (hd : 2 ≤ d) (hdm : d < m)
    (h : suffixPrefix m a b = suffixPrefix m c d) : a = c ∧ b = d := by
  apply prefixSuffix_inj ha ham hb hbm hc hcm hd hdm
  funext x
  have he := congrFun h (prefixSuffix m a b x)
  unfold prefixSuffix suffixPrefix at *
  have h2 := congrArg (reflectInterval 1 c ∘ reflectInterval d m) he
  simpa [Function.comp_def, reflectInterval_invol] using h2.symm

theorem ps_ne_sp {m a b c d : Nat} (hm : 5 ≤ m)
    (ha : 2 ≤ a) (ham : a < m) (hb : 2 ≤ b) (hbm : b < m)
    (hc : 2 ≤ c) (hcm : c < m) (hd : 2 ≤ d) (hdc : d ≤ c) :
    prefixSuffix m a b ≠ suffixPrefix m c d := by
  intro h
  have hf := congrFun h 1
  have hl := congrFun h m
  rw [prefixSuffix_first ha hb] at hf
  rw [prefixSuffix_last ham hb hbm] at hl
  have hs : a = d+m-c := by
    unfold suffixPrefix reflectInterval at hf
    split_ifs at hf <;> omega
  have ht : d = a+1-b := by
    unfold suffixPrefix reflectInterval at hl
    split_ifs at hl <;> omega
  have hn := congrFun h 2
  have key : b = 2 ∧ a = m-1 := by
    unfold prefixSuffix suffixPrefix reflectInterval at hn
    split_ifs at hn <;> omega
  obtain ⟨rfl, rfl⟩ := key
  have hp := congrFun h (m-1)
  unfold prefixSuffix suffixPrefix reflectInterval at hp
  split_ifs at hp <;> omega

def fullSub (m i j t : Nat) := reflectInterval 1 m (reflectInterval i j t)

theorem fullSub_inj {m i j k l : Nat} (hij : i < j) (hkl : k < l)
    (h : fullSub m i j = fullSub m k l) : i = k ∧ j = l := by
  apply reflection_eq hij hkl
  funext t
  have ht := congrArg (reflectInterval 1 m) (congrFun h t)
  simpa [fullSub, reflectInterval_invol] using ht

theorem fullSub_ne_ps {m a b i j : Nat} (hm : 5 ≤ m)
    (ha : 2 ≤ a) (ham : a < m) (hb : 2 ≤ b) (hbm : b < m)
    (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ m) (hpart : i ≠ 1 ∨ j ≠ m) :
    fullSub m i j ≠ prefixSuffix m a b := by
  intro h
  have hf := congrFun h 1
  rw [prefixSuffix_first ha hb] at hf
  have hfi : i = 1 ∧ a = 1+m-j := by
    unfold fullSub reflectInterval at hf
    split_ifs at hf <;> omega
  obtain ⟨rfl, hfj⟩ := hfi
  have hl := congrFun h m
  rw [prefixSuffix_last ham hb hbm] at hl
  have hba : b = a := by
    unfold fullSub reflectInterval at hl
    split_ifs at hl <;> omega
  have hn := congrFun h 2
  unfold fullSub prefixSuffix reflectInterval at hn
  split_ifs at hn <;> omega

theorem fullSub_ne_sp {m a b i j : Nat} (hm : 5 ≤ m)
    (ha : 2 ≤ a) (ham : a < m) (hb : 2 ≤ b) (hba : b ≤ a)
    (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ m) (hpart : i ≠ 1 ∨ j ≠ m) :
    fullSub m i j ≠ suffixPrefix m a b := by
  intro h
  have hl := congrFun h m
  have hfj : j = m ∧ b = 1+m-i := by
    unfold fullSub suffixPrefix reflectInterval at hl
    split_ifs at hl <;> omega
  obtain ⟨rfl, hbi⟩ := hfj
  have hf := congrFun h 1
  have hab : a = b := by
    unfold fullSub suffixPrefix reflectInterval at hf
    split_ifs at hf <;> omega
  have hn := congrFun h (j-1)
  unfold fullSub suffixPrefix reflectInterval at hn
  split_ifs at hn <;> omega

open Finset

def fsDomain (m : Nat) : Finset (Nat × Nat) :=
  ((((Icc 1 m) ×ˢ (Icc 1 m)).filter fun p => p.1 < p.2)).erase (1,m)
def psDomain (m : Nat) : Finset (Nat × Nat) :=
  (Ico 2 m) ×ˢ (Ico 2 m)
def spDomain (m : Nat) : Finset (Nat × Nat) :=
  (psDomain m).filter fun p => ¬p.1 < p.2

theorem fs_mem {m i j : Nat} : (i,j) ∈ fsDomain m ↔ 
    1 ≤ i ∧ i < j ∧ j ≤ m ∧ (i ≠ 1 ∨ j ≠ m) := by
  simp [fsDomain, Prod.ext_iff]
  omega

theorem ps_mem {m a b : Nat} : (a,b) ∈ psDomain m ↔ 2 ≤ a ∧ a < m ∧ 2 ≤ b ∧ b < m := by
  simp [psDomain, and_assoc]

theorem sp_mem {m a b : Nat} : (a,b) ∈ spDomain m ↔ 2 ≤ a ∧ a < m ∧ 2 ≤ b ∧ b ≤ a := by
  simp only [spDomain, mem_filter, ps_mem, not_lt]
  omega

noncomputable def coreFamilies (m : Nat) : Finset (Nat → Nat) := by
  classical
  exact ((fsDomain m).image fun p => fullSub m p.1 p.2) ∪
    ((psDomain m).image fun p => prefixSuffix m p.1 p.2) ∪
    ((spDomain m).image fun p => suffixPrefix m p.1 p.2)

theorem coreFamilies_card_sum (m : Nat) (hm : 5 ≤ m) :
    (coreFamilies m).card = (fsDomain m).card + (psDomain m).card + (spDomain m).card := by
  classical
  let f (p : Nat × Nat) := fullSub m p.1 p.2
  let g (p : Nat × Nat) := prefixSuffix m p.1 p.2
  let t (p : Nat × Nat) := suffixPrefix m p.1 p.2
  have fa : Set.InjOn f (fsDomain m) := by
    rintro ⟨i,j⟩ hi ⟨k,l⟩ hk he
    obtain ⟨rfl,rfl⟩ := fullSub_inj (fs_mem.mp hi).2.1 (fs_mem.mp hk).2.1 he
    rfl
  have ga : Set.InjOn g (psDomain m) := by
    rintro ⟨a,b⟩ hx ⟨c,d⟩ hy he
    obtain ⟨ha,ham,hb,hbm⟩ := ps_mem.mp hx
    obtain ⟨hc,hcm,hd,hdm⟩ := ps_mem.mp hy
    obtain ⟨rfl,rfl⟩ := prefixSuffix_inj ha ham hb hbm hc hcm hd hdm he
    rfl
  have ta : Set.InjOn t (spDomain m) := by
    rintro ⟨a,b⟩ hx ⟨c,d⟩ hy he
    obtain ⟨ha,ham,hb,hba⟩ := sp_mem.mp hx
    obtain ⟨hc,hcm,hd,hdc⟩ := sp_mem.mp hy
    obtain ⟨rfl,rfl⟩ := suffixPrefix_inj ha ham hb (by omega) hc hcm hd (by omega) he
    rfl
  have fg : Disjoint ((fsDomain m).image f) ((psDomain m).image g) := by
    apply disjoint_left.mpr
    intro w hw hv
    obtain ⟨⟨i,j⟩,hx,rfl⟩ := mem_image.mp hw
    obtain ⟨⟨a,b⟩,hy,he⟩ := mem_image.mp hv
    obtain ⟨hi,hij,hj,hpart⟩ := fs_mem.mp hx
    obtain ⟨ha,ham,hb,hbm⟩ := ps_mem.mp hy
    exact fullSub_ne_ps hm ha ham hb hbm hi hij hj hpart he.symm
  have ft : Disjoint ((fsDomain m).image f) ((spDomain m).image t) := by
    apply disjoint_left.mpr
    intro w hw hv
    obtain ⟨⟨i,j⟩,hx,rfl⟩ := mem_image.mp hw
    obtain ⟨⟨a,b⟩,hy,he⟩ := mem_image.mp hv
    obtain ⟨hi,hij,hj,hpart⟩ := fs_mem.mp hx
    obtain ⟨ha,ham,hb,hba⟩ := sp_mem.mp hy
    exact fullSub_ne_sp hm ha ham hb hba hi hij hj hpart he.symm
  have gt : Disjoint ((psDomain m).image g) ((spDomain m).image t) := by
    apply disjoint_left.mpr
    intro w hw hv
    obtain ⟨⟨a,b⟩,hx,rfl⟩ := mem_image.mp hw
    obtain ⟨⟨c,d⟩,hy,he⟩ := mem_image.mp hv
    obtain ⟨ha,ham,hb,hbm⟩ := ps_mem.mp hx
    obtain ⟨hc,hcm,hd,hdc⟩ := sp_mem.mp hy
    exact ps_ne_sp hm ha ham hb hbm hc hcm hd hdc he.symm
  change (((fsDomain m).image f ∪ (psDomain m).image g) ∪ (spDomain m).image t).card = _
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨ft,gt⟩), card_union_of_disjoint fg,
    card_image_of_injOn fa, card_image_of_injOn ga, card_image_of_injOn ta]

theorem coreFamilies_card (m : Nat) (hm : 5 ≤ m) :
    (coreFamilies m).card = 2*(m-1)*(m-2) := by
  rw [coreFamilies_card_sum m hm]
  let outer := (Icc 1 m)
  let inner := (Ico 2 m)
  have hf : (fsDomain m).card + 1 = m.choose 2 := by
    have h : (1,m) ∈ (outer ×ˢ outer).filter (fun p => p.1 < p.2) := by simp [outer]; omega
    have he := card_erase_add_one h
    simpa [fsDomain, outer, card_product_filter_lt, Nat.card_Icc] using he
  have hg : (psDomain m).card = (m-2)*(m-2) := by simp [psDomain]
  have ht : (m-2).choose 2 + (spDomain m).card = (psDomain m).card := by
    have he := card_filter_add_card_filter_not (s := psDomain m) (p := fun p => p.1 < p.2)
    simpa [psDomain, spDomain, card_product_filter_lt] using he
  obtain ⟨k,rfl⟩ : ∃ k, m = k+2 := ⟨m-2, by omega⟩
  have hc : (k+2).choose 2 = k.choose 2 + 2*k+1 := by
    rw [Nat.choose_succ_succ (k+1) 1, Nat.choose_succ_succ k 1]
    simp
    omega
  simp only [Nat.add_sub_cancel] at *
  have hs : k+2-1 = k+1 := by omega
  rw [hs]
  nlinarith only [hf, hg, ht, hc]

theorem full_conjugate {m i j : Nat} (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ m) :
    reflectInterval i j ∘ reflectInterval 1 m = fullSub m (1+m-j) (1+m-i) := by
  funext t
  unfold fullSub Function.comp reflectInterval
  split_ifs <;> omega

theorem ps_sp_comm {m a b : Nat} (hab : a < b) (hb : b ≤ m) :
    suffixPrefix m a b = prefixSuffix m a b := by
  funext t
  unfold prefixSuffix suffixPrefix reflectInterval
  split_ifs <;> omega

theorem full_coverage {m i j k l : Nat} (hm : 5 ≤ m)
    (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ m) (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ m)
    (hne : (i,j) ≠ (k,l))
    (hleft : i = 1 ∨ k = 1) (hright : j = m ∨ l = m) :
    reflectInterval i j ∘ reflectInterval k l ∈ coreFamilies m := by
  classical
  simp only [coreFamilies, mem_union, mem_image]
  rcases hleft with rfl | rfl <;> rcases hright with rfl | rfl
  · left; left
    exact ⟨(k,l), fs_mem.mpr ⟨hk,hkl,hl,by simp [Prod.ext_iff] at hne; omega⟩,rfl⟩
  · by_cases hk1 : k = 1
    · subst k
      left; left
      refine ⟨(1+l-j,1+l-1),fs_mem.mpr ⟨by omega,by omega,by omega,?_⟩,?_⟩
      · simp [Prod.ext_iff] at hne
        omega
      · exact (full_conjugate hi hij hj).symm
    by_cases hjl : j = l
    · subst j
      left; left
      exact ⟨(k,l), fs_mem.mpr ⟨hk,hkl,le_refl _,Or.inl hk1⟩,rfl⟩
    left; right
    exact ⟨(j,k),ps_mem.mpr ⟨by omega,by omega,by omega,by omega⟩,rfl⟩
  · by_cases hi1 : i = 1
    · subst i
      left; left
      refine ⟨(1,l),fs_mem.mpr ⟨by omega,by omega,hl,?_⟩,rfl⟩
      simp [Prod.ext_iff] at hne
      omega
    by_cases hlj : l = j
    · subst l
      left; left
      refine ⟨(1+j-j,1+j-i),fs_mem.mpr ⟨by omega,by omega,by omega,by omega⟩,?_⟩
      exact (full_conjugate hi hij (by omega)).symm
    by_cases hsep : l < i
    · left; right
      refine ⟨(l,i),ps_mem.mpr ⟨by omega,by omega,by omega,by omega⟩,?_⟩
      exact (ps_sp_comm hsep (by omega)).symm
    right
    exact ⟨(l,i),sp_mem.mpr ⟨by omega,by omega,by omega,by omega⟩,rfl⟩
  · left; left
    refine ⟨(1+l-j,1+l-i),fs_mem.mpr ⟨by omega,by omega,by omega,?_⟩,?_⟩
    · simp [Prod.ext_iff] at hne
      omega
    · exact (full_conjugate hi hij hj).symm

theorem fullSub_endpoints {m i j : Nat} (hm : 5 ≤ m) (hi : 1 ≤ i) (hij : i < j)
    (hj : j ≤ m) (hp : i ≠ 1 ∨ j ≠ m) :
    fullSub m i j 1 ≠ 1 ∧ fullSub m i j m ≠ m := by
  unfold fullSub reflectInterval
  split_ifs <;> omega

theorem ps_endpoints {m a b : Nat} (ha : 2 ≤ a) (ham : a < m) (hb : 2 ≤ b) (hbm : b < m) :
    prefixSuffix m a b 1 ≠ 1 ∧ prefixSuffix m a b m ≠ m := by
  rw [prefixSuffix_first ha hb, prefixSuffix_last ham hb hbm]
  split_ifs <;> omega

theorem sp_endpoints {m a b : Nat} (ha : 2 ≤ a) (ham : a < m) (hb : 2 ≤ b) (hba : b ≤ a) :
    suffixPrefix m a b 1 ≠ 1 ∧ suffixPrefix m a b m ≠ m := by
  unfold suffixPrefix reflectInterval
  split_ifs <;> omega

theorem fullSub_ne_full {m i j : Nat} (_hi : 1 ≤ i) (hij : i < j)
    (_hj : j ≤ m) : fullSub m i j ≠ reflectInterval 1 m := by
  intro he
  have hn := congrArg (reflectInterval 1 m) (congrFun he i)
  simp only [fullSub, reflectInterval_invol] at hn
  unfold reflectInterval at hn
  split_ifs at hn <;> omega

theorem core_eq (m : Nat) (hm : 5 ≤ m) : idxCore m = (coreFamilies m : Set (Nat → Nat)) := by
  classical
  ext f
  constructor
  · rintro ⟨⟨hid,_,g,h,⟨i,j,hi,hij,hj,rfl⟩,⟨k,l,hk,hkl,hl,rfl⟩,rfl⟩,h1,hmv⟩
    apply full_coverage hm hi hij hj hk hkl hl
    · rintro he
      obtain ⟨rfl,rfl⟩ := Prod.ext_iff.mp he
      apply hid
      funext t
      exact reflectInterval_invol
    · by_contra! he
      apply h1
      simp [Function.comp_apply,reflectInterval, show ¬k ≤ 1 by omega,show ¬i ≤ 1 by omega]
    · by_contra! he
      apply hmv
      simp [Function.comp_apply,reflectInterval, show ¬m ≤ l by omega,show ¬m ≤ j by omega]
  · intro hf
    have hn : f 1 ≠ 1 ∧ f m ≠ m ∧ f ≠ reflectInterval 1 m ∧ 
        ∃ g h, idxOne m g ∧ idxOne m h ∧ f = g ∘ h := by
      change f ∈ coreFamilies m at hf
      simp only [coreFamilies, mem_union, mem_image] at hf
      rcases hf with ((⟨⟨i,j⟩,hp,rfl⟩ | ⟨⟨a,b⟩,hp,rfl⟩) | ⟨⟨a,b⟩,hp,rfl⟩)
      · obtain ⟨hi,hij,hj,hp⟩ := fs_mem.mp hp
        have he := fullSub_endpoints hm hi hij hj hp
        exact ⟨he.1,he.2,fullSub_ne_full hi hij hj,_,_,
          ⟨1,m,by omega,by omega,by omega,rfl⟩,⟨i,j,hi,hij,hj,rfl⟩,rfl⟩
      · obtain ⟨ha,ham,hb,hbm⟩ := ps_mem.mp hp
        have he := ps_endpoints ha ham hb hbm
        refine ⟨he.1,he.2,?_,_,_,⟨1,a,by omega, by omega, by omega,rfl⟩,
          ⟨b,m,by omega,by omega,by omega,rfl⟩,rfl⟩
        intro heq
        have ht := congrFun heq 1
        rw [prefixSuffix_first ha hb] at ht
        simp [reflectInterval, show 1 ≤ m by omega] at ht
        omega
      · obtain ⟨ha,ham,hb,hba⟩ := sp_mem.mp hp
        have he := sp_endpoints ha ham hb hba
        refine ⟨he.1,he.2,?_,_,_,⟨b,m,by omega,by omega,by omega,rfl⟩,
          ⟨1,a,by omega,by omega,by omega,rfl⟩,rfl⟩
        intro heq
        have ht := congrFun heq m
        unfold suffixPrefix reflectInterval at ht
        split_ifs at ht <;> omega
    obtain ⟨h1,hmv,hfull,hprod⟩ := hn
    refine ⟨⟨fun he => h1 (by rw [he]; rfl),?_,hprod⟩,h1,hmv⟩
    rintro ⟨i,j,hi,hij,hj,rfl⟩
    have he : i = 1 ∧ j = m := by
      unfold reflectInterval at h1 hmv
      split_ifs at h1 hmv <;> omega
    obtain ⟨rfl,rfl⟩ := he
    exact hfull rfl

theorem idxCore_card (m : Nat) (hm : 5 ≤ m) : (idxCore m).ncard = 2*(m-1)*(m-2) := by
  rw [core_eq m hm, Set.ncard_coe_finset, coreFamilies_card m hm]

/- Inclusion-exclusion on fixed endpoints reduces the total count to the preceding two widths. -/
theorem rrRestrict (m : Nat) :
    {f ∈ idxSphere (m+1) | f (m+1) = m+1} = idxSphere m := by
  have mono {f : Nat → Nat} (h : idxOne m f) : idxOne (m+1) f := by
    obtain ⟨a,b,ha,hab,hb,rfl⟩ := h
    exact ⟨a,b,ha,hab,by omega,rfl⟩
  have fix {f : Nat → Nat} (h : idxOne m f) : f (m+1) = m+1 := by
    obtain ⟨a,b,ha,hab,hb,rfl⟩ := h
    simp [reflectInterval, show ¬ m+1 ≤ b by omega]
  ext f
  constructor
  · rintro ⟨⟨hid,hone,_,_,⟨a,b,ha,hab,hb,rfl⟩,⟨c,d,hc,hcd,hd,rfl⟩,rfl⟩,hf⟩
    have he := congrArg (reflectInterval a b) hf
    simp only [Function.comp_apply,reflectInterval_invol] at he
    have he' : b ≤ m ∧ d ≤ m ∨ a = c ∧ b = d := by
      unfold reflectInterval at he
      split_ifs at he <;> omega
    obtain ⟨hb',hd'⟩ | ⟨rfl,rfl⟩ := he'
    · exact ⟨hid,fun h => hone (mono h),_,_,⟨a,b,ha,hab,hb',rfl⟩,⟨c,d,hc,hcd,hd',rfl⟩,rfl⟩
    · exact False.elim (hid (funext fun _ => reflectInterval_invol))
  · rintro ⟨hid,hone,g,h,hg,hh,rfl⟩
    have hfix : (g ∘ h) (m+1) = m+1 := by simp [fix hh,fix hg]
    refine ⟨⟨hid,?_,g,h,mono hg,mono hh,rfl⟩,hfix⟩
    rintro ⟨a,b,ha,hab,hb,he⟩
    rw [he] at hfix
    have hb' : b ≤ m := by unfold reflectInterval at hfix; split_ifs at hfix <;> omega
    exact hone ⟨a,b,ha,hab,hb',he⟩

def rrMirror (m : Nat) (f : Nat → Nat) (t : Nat) :=
  reflectInterval 1 m (f (reflectInterval 1 m t))

theorem rrMirror_inv (m : Nat) (f : Nat → Nat) : rrMirror m (rrMirror m f) = f := by
  funext t
  simp [rrMirror,reflectInterval_invol]

theorem rrMirror_id (m : Nat) : rrMirror m id = id := by
  funext t
  simp [rrMirror,reflectInterval_invol]

theorem rrMirror_mul (m : Nat) (f g : Nat → Nat) :
    rrMirror m (f ∘ g) = rrMirror m f ∘ rrMirror m g := by
  funext t
  simp [rrMirror,reflectInterval_invol]

theorem rrMirror_one {m : Nat} {f : Nat → Nat} (hf : idxOne m f) : idxOne m (rrMirror m f) := by
  obtain ⟨a,b,ha,hab,hb,rfl⟩ := hf
  refine ⟨1+m-b,1+m-a,by omega,by omega,by omega,?_⟩
  funext t
  unfold rrMirror reflectInterval
  split_ifs <;> omega

theorem rrMirror_mem {m : Nat} {f : Nat → Nat} (hf : f ∈ idxSphere m) :
    rrMirror m f ∈ idxSphere m := by
  obtain ⟨hid,hone,g,h,hg,hh,rfl⟩ := hf
  refine ⟨fun he => hid ?_, fun he => hone ?_,_,_,rrMirror_one hg,rrMirror_one hh,rrMirror_mul ..⟩
  · simpa only [rrMirror_inv,rrMirror_id] using congrArg (rrMirror m) he
  · simpa only [rrMirror_inv] using rrMirror_one he

theorem rrMirror_end {m : Nat} (hm : 1 ≤ m) (f : Nat → Nat) :
    rrMirror m f 1 = 1 ↔ f m = m := by
  have h₁ : reflectInterval 1 m 1 = m := by simp [reflectInterval,hm]
  have h₂ : reflectInterval 1 m m = 1 := by simp [reflectInterval,hm]
  unfold rrMirror
  rw [h₁]
  exact ⟨fun h => by simpa only [reflectInterval_invol,h₁] using congrArg (reflectInterval 1 m) h,
    fun h => by rw [h,h₂]⟩

theorem rrLeft (m : Nat) : {f ∈ idxSphere (m+1) | f 1 = 1}.ncard = (idxSphere m).ncard := by
  rw [← rrRestrict m]
  have he : rrMirror (m+1) '' {f ∈ idxSphere (m+1) | f (m+1) = m+1} =
      {f ∈ idxSphere (m+1) | f 1 = 1} := by
    ext f
    constructor
    · rintro ⟨g,⟨hg,hz⟩,rfl⟩
      exact ⟨rrMirror_mem hg,(rrMirror_end (by omega) _).2 hz⟩
    · rintro ⟨hg,hz⟩
      refine ⟨rrMirror (m+1) f,⟨rrMirror_mem hg,?_⟩,rrMirror_inv ..⟩
      apply (rrMirror_end (by omega) _).1
      rwa [rrMirror_inv]
  rw [← he,Set.ncard_image_of_injective _ (Function.LeftInverse.injective (rrMirror_inv (m+1)))]

theorem rrFinite (m : Nat) : (idxSphere m).Finite := by
  let op (p : Fin (m+1) × Fin (m+1)) := reflectInterval p.1 p.2
  let pr (p : (Fin (m+1) × Fin (m+1)) × (Fin (m+1) × Fin (m+1))) := op p.1 ∘ op p.2
  apply (Set.finite_range pr).subset
  rintro f ⟨_,_,g,h,⟨a,b,ha,hab,hb,rfl⟩,⟨c,d,hc,hcd,hd,rfl⟩,rfl⟩
  exact ⟨((⟨a,by omega⟩,⟨b,by omega⟩),(⟨c,by omega⟩,⟨d,by omega⟩)),rfl⟩

theorem idxSphere_step (m : Nat) : (idxSphere (m+2)).ncard + (idxSphere m).ncard =
    2*(idxSphere (m+1)).ncard + (idxCore (m+2)).ncard := by
  let S := idxSphere (m+2)
  let A := {f ∈ S | f 1 = 1}
  let B := {f ∈ S | f (m+2) = m+2}
  have ha : A ⊆ S := fun _ h => h.1
  have hb : B ⊆ S := fun _ h => h.1
  have hfin : S.Finite := rrFinite _
  have hu := Set.ncard_union_add_ncard_inter A B (hfin.subset ha) (hfin.subset hb)
  have hd := Set.ncard_sdiff_add_ncard_of_subset (Set.union_subset ha hb) hfin
  have hac : A.ncard = (idxSphere (m+1)).ncard := rrLeft _
  have hbe : B = idxSphere (m+1) := rrRestrict _
  have hie : A ∩ B = {f ∈ idxSphere (m+1) | f 1 = 1} := by
    rw [← hbe]
    ext f
    change ((f ∈ S ∧ f 1 = 1) ∧ f ∈ B) ↔ f ∈ B ∧ f 1 = 1
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨hb h.1,h.2⟩,h.1⟩⟩
  have hde : S \ (A ∪ B) = idxCore (m+2) := by
    ext f
    change (f ∈ S ∧ ¬((f ∈ S ∧ f 1 = 1) ∨ (f ∈ S ∧ f (m+2) = m+2))) ↔ 
      f ∈ S ∧ f 1 ≠ 1 ∧ f (m+2) ≠ m+2
    tauto
  rw [hie,rrLeft,hac,hbe] at hu
  rw [hde,hbe] at hd
  change S.ncard + (idxSphere m).ncard = _
  omega

def neighbors (w : List ℕ) : Finset (List ℕ) :=
  (Finset.range (w.length + 1)).biUnion fun i =>
    ((Finset.range ((w.drop i).length + 1)).filter fun t => 2 ≤ t).image fun t =>
      w.take i ++ ((w.drop i).take t).reverse ++ (w.drop i).drop t

theorem mem_neighbors {u v : List ℕ} : v ∈ neighbors u ↔ RevStep u v := by
  simp only [neighbors, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Finset.mem_filter, Nat.lt_succ_iff]
  constructor
  · rintro ⟨i, _, t, ⟨ht, htwo⟩, rfl⟩
    refine ⟨u.take i, (u.drop i).take t, (u.drop i).drop t, ?_, ?_, rfl⟩
    · rw [List.length_take, min_eq_left ht]
      exact htwo
    · simp [List.append_assoc]
  · rintro ⟨a, b, c, hb, rfl, rfl⟩
    refine ⟨a.length, by simp, b.length, ⟨?_, hb⟩, ?_⟩ <;>
      simp [List.append_assoc]

def sphere (m : ℕ) : Finset (List ℕ) :=
  let identity := List.range m
  let one := neighbors identity
  one.biUnion neighbors \ insert identity one

theorem card_sphere (m : ℕ) : (distTwoPerms m).ncard = (sphere m).card := by
  have h : distTwoPerms m = (sphere m : Set (List ℕ)) := by
    ext w
    simp [sphere, distTwoPerms, mem_neighbors, and_comm, and_assoc]
  rw [h, Set.ncard_coe_finset]

theorem sphere_three : (distTwoPerms 3).ncard = 2 := by rw [card_sphere]; decide

theorem sphere_four : (distTwoPerms 4).ncard = 15 := by rw [card_sphere]; decide

theorem closed_form_of_recurrence (s : ℕ → ℕ) (hone : s 1 = 2) (htwo : s 2 = 15)
    (hstep : ∀ n, 1 ≤ n → s (n+2) + s n = 2*s (n+1) + 2*(n+2)*(n+3)) :
    ∀ n, 1 ≤ n → s n = (n^4 + 6*n^3 + 11*n^2 - 12*n + 6)/6 := by
  let P (n : ℕ) := 6*s n + 12*n = n^4 + 6*n^3 + 11*n^2 + 6
  have hs (k : ℕ) : P (k+1) ∧ P (k+2) := by
    induction k with
    | zero => norm_num [P, hone, htwo]
    | succ k ih =>
      obtain ⟨ha, hb⟩ := ih
      refine ⟨hb, ?_⟩
      dsimp [P] at ha hb ⊢
      have h := hstep (k+1) (by omega)
      nlinarith only [ha, hb, h]
  intro n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨h, _⟩ := hs k
  dsimp [P] at h
  change s (k+1) = ((k+1)^4 + 6*(k+1)^3 + 11*(k+1)^2 - 12*(k+1) + 6)/6
  have hbound : 12*(k+1) ≤ (k+1)^4 + 6*(k+1)^3 + 11*(k+1)^2 := by
    nlinarith only [Nat.zero_le k, Nat.zero_le (k^2), Nat.zero_le (k^3), Nat.zero_le (k^4)]
  omega

end OMA.S_oeis_a007972

open OMA.S_oeis_a007972

theorem OMA.solution : type_of% @OMA.S_oeis_a007972.main := by
  apply closed_form_of_recurrence (fun n => (distTwoPerms (n+2)).ncard) sphere_three sphere_four
  intro n hn
  have h := idxSphere_step (n+2)
  rw [idxCore_card _ (by omega)] at h
  simp only [idxSphere_card]
  have ha : n+2+2-1 = n+3 := by omega
  have hb : n+2+2-2 = n+2 := by omega
  rw [ha,hb] at h
  simpa only [Nat.add_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h
