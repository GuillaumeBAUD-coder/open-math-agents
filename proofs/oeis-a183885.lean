import OMAStatements.S_oeis_a183885
/- The capped-count approach builds on the exceptional-word classification shared by @shunendo181-boop. All 125 states and their transition certificates are checked by the kernel. -/
namespace OMA.WordsThree
open OMA.S_oeis_a183885
open Finset
private def count {ι : Type*} (s : Finset ι) (w : ι → Fin 3) (b : Fin 3) : ℕ :=
  (s.filter (fun i => w i = b)).card

private theorem count_sizes {ι : Type*} (s : Finset ι) (w : ι → Fin 3) :
    s.card = count s w 0 + count s w 1 + count s w 2 ∧
    (∑ i ∈ s, (w i).val) = count s w 1 + 2*count s w 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [count]
  | @insert i s hi ih =>
    have h0 : i ∉ s.filter (fun j => w j = 0) := by simp [hi]
    have h1 : i ∉ s.filter (fun j => w j = 1) := by simp [hi]
    have h2 : i ∉ s.filter (fun j => w j = 2) := by simp [hi]
    unfold count at *
    generalize h : w i = b
    fin_cases b <;> simp [Finset.filter_insert, h, hi, h0,h1,h2] at * <;> omega

private def canSelect (a b c v : ℕ) : Prop :=
  ∃ x : Fin 4, ∃ y : Fin 4, ∃ z : Fin 4,
    x.val ≤ a ∧ y.val ≤ b ∧ z.val ≤ c ∧
    x.val + y.val + z.val = 3 ∧ (y.val + 2*z.val) % 3 = v

private theorem select_iff {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → Fin 3) (v : ℕ) :
    (∃ t ⊆ s, t.card = 3 ∧ (∑ j ∈ t, (w j).val) % 3 = v) ↔
    canSelect (count s w 0) (count s w 1) (count s w 2) v := by
  constructor
  · rintro ⟨t,ht,hc,hv⟩
    obtain ⟨sz,sm⟩ := count_sizes t w
    have le (b : Fin 3) : count t w b ≤ count s w b :=
      Finset.card_le_card (Finset.filter_subset_filter _ ht)
    exact ⟨⟨count t w 0,by omega⟩,⟨count t w 1,by omega⟩,⟨count t w 2,by omega⟩,le 0,le 1,le 2,sz.symm.trans hc,sm ▸ hv⟩
  · rintro ⟨x,y,z,hx,hy,hz,hs,hv⟩
    obtain ⟨u,hu,cu⟩ := Finset.exists_subset_card_eq hx
    obtain ⟨t,ht,ct⟩ := Finset.exists_subset_card_eq hy
    obtain ⟨r,hr,cr⟩ := Finset.exists_subset_card_eq hz
    have hu' j (h : j ∈ u) := (Finset.mem_filter.mp (hu h))
    have ht' j (h : j ∈ t) := (Finset.mem_filter.mp (ht h))
    have hr' j (h : j ∈ r) := (Finset.mem_filter.mp (hr h))
    have dut : Disjoint u t := Finset.disjoint_left.mpr (fun _ h1 h2 => by
      have := (hu' _ h1).2.symm.trans (ht' _ h2).2
      contradiction)
    have dur : Disjoint u r := Finset.disjoint_left.mpr (fun _ h1 h2 => by
      have := (hu' _ h1).2.symm.trans (hr' _ h2).2
      contradiction)
    have dtr : Disjoint t r := Finset.disjoint_left.mpr (fun _ h1 h2 => by
      have := (ht' _ h1).2.symm.trans (hr' _ h2).2
      contradiction)
    have d : Disjoint (u ∪ t) r := disjoint_sup_left.mpr ⟨dur,dtr⟩
    refine ⟨u ∪ t ∪ r, ?_, ?_, ?_⟩
    · exact Finset.union_subset (Finset.union_subset (hu.trans (Finset.filter_subset _ _))
        (ht.trans (Finset.filter_subset _ _))) (hr.trans (Finset.filter_subset _ _))
    · rw [Finset.card_union_of_disjoint d,Finset.card_union_of_disjoint dut,cu,ct,cr,hs]
    · rw [Finset.sum_union d,Finset.sum_union dut]
      have sum_one (U : Finset ι) (b : Fin 3) (hU : ∀ j ∈ U, w j = b) :
          (∑ j ∈ U, (w j).val) = U.card * b.val := by
        calc
          _ = ∑ _j ∈ U, b.val := Finset.sum_congr rfl (fun j hj => by rw [hU j hj])
          _ = _ := by simp
      rw [sum_one u 0 (fun j hj => (hu' j hj).2),sum_one t 1 (fun j hj => (ht' j hj).2),
        sum_one r 2 (fun j hj => (hr' j hj).2),cu,ct,cr]
      simpa [Nat.mul_comm] using hv

private def good (c : Fin 3 → ℕ) : Prop := ∀ b : Fin 3, 0 < c b →
  canSelect (c 0 - (if b = 0 then 1 else 0)) (c 1 - (if b = 1 then 1 else 0))
    (c 2 - (if b = 2 then 1 else 0)) b.val

private theorem valid_good {N} (w : Fin N → Fin 3) :
    Valid w ↔ good (count univ w) := by
  have erase_count (i : Fin N) (b : Fin 3) :
      count (univ.erase i) w b = count univ w b - (if w i = b then 1 else 0) := by
    unfold count
    rw [Finset.filter_erase]
    by_cases h : w i = b <;> simp [h,Finset.card_erase_of_mem]
  have select_at (i : Fin N) :
      (∃ t : Finset (Fin N), t.card = 3 ∧ i ∉ t ∧ (∑ j ∈ t, (w j).val) % 3 = (w i).val) ↔
      canSelect (count univ w 0 - (if w i = 0 then 1 else 0))
        (count univ w 1 - (if w i = 1 then 1 else 0))
        (count univ w 2 - (if w i = 2 then 1 else 0)) (w i).val := by
    rw [← erase_count,← erase_count,← erase_count,← select_iff]
    constructor
    · rintro ⟨t,hc,hi,hs⟩
      exact ⟨t,fun j hj => Finset.mem_erase.mpr ⟨fun h => hi (h ▸ hj),Finset.mem_univ _⟩,hc,hs⟩
    · rintro ⟨t,ht,hc,hs⟩
      exact ⟨t,hc,fun hi => Finset.notMem_erase i _ (ht hi),hs⟩
  constructor
  · intro h b hb
    obtain ⟨i,hi⟩ := Finset.card_pos.mp hb
    obtain ⟨_,he⟩ := Finset.mem_filter.mp hi
    exact he ▸ (select_at i).mp (h i)
  · intro h i
    apply (select_at i).mpr
    exact h _ (Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩)

private def capped (c : Fin 3 → ℕ) : Fin 3 → ℕ := fun b => min 4 (c b)

private theorem good_cap (c : Fin 3 → ℕ) : good (capped c) ↔ good c := by
  have bound (x : Fin 4) (k : ℕ) (b : Prop) [Decidable b] :
      x.val ≤ min 4 k - (if b then 1 else 0) ↔ x.val ≤ k - (if b then 1 else 0) := by
    have := x.isLt
    split <;> omega
  simp only [good,capped,canSelect,bound,lt_min_iff,show 0 < 4 by decide,true_and]

private instance canDec (a b c v : ℕ) : Decidable (canSelect a b c v) := by
  unfold canSelect
  infer_instance

private instance goodDec (c : Fin 3 → ℕ) : Decidable (good c) := by
  unfold good
  infer_instance

private abbrev State := Fin 3 → Fin 5
private def stateOf (c : Fin 3 → ℕ) : State := fun b => ⟨min 4 (c b),by omega⟩
private def addColor (c : Fin 3 → ℕ) (b : Fin 3) : Fin 3 → ℕ :=
  fun j => c j + if b = j then 1 else 0
private def step (s : State) (b : Fin 3) : State := stateOf (addColor (fun j => (s j).val) b)
private theorem step_state (c : Fin 3 → ℕ) (b : Fin 3) :
    stateOf (addColor c b) = step (stateOf c) b := by
  funext j
  apply Fin.ext
  simp only [stateOf,step,addColor]
  split <;> omega

private def completions : ℕ → State → ℤ
  | 0,s => if good (fun j => (s j).val) then 1 else 0
  | n+1,s => completions n (step s 0) + completions n (step s 1) + completions n (step s 2)

private theorem count_cons {N : ℕ} (b j : Fin 3) (w : Fin N → Fin 3) :
    count univ (Fin.cons b w) j = (if b = j then 1 else 0) + count univ w j := by
  unfold count
  have expand {ι : Type} [Fintype ι] (v : ι → Fin 3) :
      (univ.filter (fun i => v i = j)).card = ∑ i, if v i = j then 1 else 0 :=
    (Finset.sum_boole (R := ℕ) _ _).symm
  rw [expand,expand, Fin.sum_univ_succ]
  simp

private def wordSum (N : ℕ) (c : Fin 3 → ℕ) : ℤ :=
  ∑ w : Fin N → Fin 3, if good (fun j => c j + count univ w j) then 1 else 0

private theorem wordSum_eq (N : ℕ) (c : Fin 3 → ℕ) :
    wordSum N c = completions N (stateOf c) := by
  induction N generalizing c with
  | zero =>
    simp [wordSum,completions,count,stateOf,← good_cap c] <;> rfl
  | succ n ih =>
    let F (w : Fin (n+1) → Fin 3) : ℤ := if good (fun j => c j + count univ w j) then 1 else 0
    change (∑ w, F w) = _
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Fin 3)).sum_comp F, Fintype.sum_prod_type]
    have inner (b : Fin 3) :
        (∑ w : Fin n → Fin 3, F (Fin.cons b w)) = wordSum n (addColor c b) := by
      unfold wordSum F
      simp only [count_cons,addColor,Nat.add_assoc]
    change (∑ b : Fin 3, ∑ w : Fin n → Fin 3, F (Fin.cons b w)) = _
    simp_rw [inner,ih,step_state]
    simp [completions,Fin.sum_univ_succ,add_assoc]

private theorem a_eq (n : ℕ) (hn : n ≠ 0) :
    a n = completions (n+3) (stateOf (fun _ => 0)) := by
  rw [← wordSum_eq]
  simp only [a,if_neg hn,wordSum,Nat.zero_add,←valid_good,Finset.sum_boole]

end OMA.WordsThree

namespace OMA.WordsThree
private def values : Array (Array ℤ) :=
  #[#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 2, 0, 1, 2, 3, 3, 0, 1, 2, 3, 3, 0, 0, 0, 2, 2, 0, 0, 2, 3, 3, 0, 2, 3, 3, 3, 2, 3, 3, 3, 3, 2, 3, 3, 3, 3, 0, 0, 2, 3, 3, 0, 2, 3, 3, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 0, 3, 3, 3, 0, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 3, 3, 3, 1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
    #[0, 0, 0, 3, 3, 0, 0, 3, 6, 6, 0, 3, 7, 8, 8, 3, 6, 8, 9, 9, 3, 6, 8, 9, 9, 0, 0, 6, 8, 8, 0, 6, 9, 9, 9, 6, 9, 9, 9, 9, 8, 9, 9, 9, 9, 8, 9, 9, 9, 9, 1, 4, 9, 9, 9, 4, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 1, 6, 9, 9, 9, 6, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 3, 6, 9, 9, 9, 6, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9],
    #[0, 0, 12, 17, 17, 0, 12, 22, 23, 23, 12, 22, 25, 26, 26, 17, 23, 26, 27, 27, 17, 23, 26, 27, 27, 1, 16, 26, 26, 26, 16, 26, 27, 27, 27, 26, 27, 27, 27, 27, 26, 27, 27, 27, 27, 26, 27, 27, 27, 27, 9, 23, 27, 27, 27, 23, 26, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 15, 23, 27, 27, 27, 23, 26, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 15, 23, 27, 27, 27, 23, 26, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27],
    #[1, 40, 65, 66, 66, 40, 70, 75, 76, 76, 65, 75, 79, 80, 80, 66, 76, 80, 81, 81, 66, 76, 80, 81, 81, 41, 75, 80, 80, 80, 75, 80, 81, 81, 81, 80, 81, 81, 81, 81, 80, 81, 81, 81, 81, 80, 81, 81, 81, 81, 61, 76, 81, 81, 81, 76, 80, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 61, 76, 81, 81, 81, 76, 80, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 61, 76, 81, 81, 81, 76, 80, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81],
    #[121, 210, 221, 222, 222, 210, 230, 236, 237, 237, 221, 236, 241, 242, 242, 222, 237, 242, 243, 243, 222, 237, 242, 243, 243, 211, 236, 242, 242, 242, 236, 242, 243, 243, 243, 242, 243, 243, 243, 243, 242, 243, 243, 243, 243, 242, 243, 243, 243, 243, 213, 237, 243, 243, 243, 237, 242, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 213, 237, 243, 243, 243, 237, 242, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 213, 237, 243, 243, 243, 237, 242, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243, 243],
    #[631, 687, 700, 701, 701, 687, 714, 721, 722, 722, 700, 721, 727, 728, 728, 701, 722, 728, 729, 729, 701, 722, 728, 729, 729, 685, 721, 728, 728, 728, 721, 728, 729, 729, 729, 728, 729, 729, 729, 729, 728, 729, 729, 729, 729, 728, 729, 729, 729, 729, 687, 722, 729, 729, 729, 722, 728, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 687, 722, 729, 729, 729, 722, 728, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 687, 722, 729, 729, 729, 722, 728, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729, 729],
    #[2059, 2135, 2150, 2151, 2151, 2135, 2170, 2178, 2179, 2179, 2150, 2178, 2185, 2186, 2186, 2151, 2179, 2186, 2187, 2187, 2151, 2179, 2186, 2187, 2187, 2129, 2178, 2186, 2186, 2186, 2178, 2186, 2187, 2187, 2187, 2186, 2187, 2187, 2187, 2187, 2186, 2187, 2187, 2187, 2187, 2186, 2187, 2187, 2187, 2187, 2131, 2179, 2187, 2187, 2187, 2179, 2186, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2131, 2179, 2187, 2187, 2187, 2179, 2186, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2131, 2179, 2187, 2187, 2187, 2179, 2186, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187, 2187],
    #[6399, 6498, 6515, 6516, 6516, 6498, 6542, 6551, 6552, 6552, 6515, 6551, 6559, 6560, 6560, 6516, 6552, 6560, 6561, 6561, 6516, 6552, 6560, 6561, 6561, 6487, 6551, 6560, 6560, 6560, 6551, 6560, 6561, 6561, 6561, 6560, 6561, 6561, 6561, 6561, 6560, 6561, 6561, 6561, 6561, 6560, 6561, 6561, 6561, 6561, 6489, 6552, 6561, 6561, 6561, 6552, 6560, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6489, 6552, 6561, 6561, 6561, 6552, 6560, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6489, 6552, 6561, 6561, 6561, 6552, 6560, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561, 6561],
    #[19483, 19608, 19627, 19628, 19628, 19608, 19662, 19672, 19673, 19673, 19627, 19672, 19681, 19682, 19682, 19628, 19673, 19682, 19683, 19683, 19628, 19673, 19682, 19683, 19683, 19591, 19672, 19682, 19682, 19682, 19672, 19682, 19683, 19683, 19683, 19682, 19683, 19683, 19683, 19683, 19682, 19683, 19683, 19683, 19683, 19682, 19683, 19683, 19683, 19683, 19593, 19673, 19683, 19683, 19683, 19673, 19682, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19593, 19673, 19683, 19683, 19683, 19673, 19682, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19593, 19673, 19683, 19683, 19683, 19673, 19682, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683, 19683],
    #[58807, 58961, 58982, 58983, 58983, 58961, 59026, 59037, 59038, 59038, 58982, 59037, 59047, 59048, 59048, 58983, 59038, 59048, 59049, 59049, 58983, 59038, 59048, 59049, 59049, 58937, 59037, 59048, 59048, 59048, 59037, 59048, 59049, 59049, 59049, 59048, 59049, 59049, 59049, 59049, 59048, 59049, 59049, 59049, 59049, 59048, 59049, 59049, 59049, 59049, 58939, 59038, 59049, 59049, 59049, 59038, 59048, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 58939, 59038, 59049, 59049, 59049, 59038, 59048, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 58939, 59038, 59049, 59049, 59049, 59038, 59048, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049, 59049]]
private def entry (n : ℕ) (s : State) : ℤ :=
  (values[n]?.getD #[])[25*(s 0).val + 5*(s 1).val + (s 2).val]?.getD 0

private theorem by_three {P : State → Prop}
    (h : ∀ i j k : Fin 5, P ![i,j,k]) (s : State) : P s := by
  have he : s = ![s 0,s 1,s 2] := by funext b; fin_cases b <;> rfl
  rw [he]
  exact h _ _ _

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem init (s : State) : completions 0 s = entry 0 s := by
  apply by_three (s := s)
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem advance (i : Fin 10) (s : State) :
    entry (i.val+1) s = entry i.val (step s 0) + entry i.val (step s 1) + entry i.val (step s 2) := by
  have check : ∀ a : Fin 10, ∀ b c d : Fin 5, entry (a.val+1) ![b,c,d] =
      entry a.val (step ![b,c,d] 0) + entry a.val (step ![b,c,d] 1) +
      entry a.val (step ![b,c,d] 2) := by decide +kernel
  apply by_three (s := s)
  exact check i

private theorem tabulated (i : ℕ) (hi : i ≤ 10) (s : State) : completions i s = entry i s := by
  induction i generalizing s with
  | zero => exact init s
  | succ i ih =>
    rw [completions,ih (by omega),ih (by omega),ih (by omega)]
    exact (advance ⟨i,by omega⟩ s).symm

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem relation (m : ℕ) (s : State) :
    completions (m+10) s = 6*completions (m+9) s - 12*completions (m+8) s +
      10*completions (m+7) s - 3*completions (m+6) s := by
  induction m generalizing s with
  | zero =>
    simp only [Nat.zero_add]
    simp only [tabulated _ (by decide : 10 ≤ 10),tabulated _ (by decide : 9 ≤ 10),
      tabulated _ (by decide : 8 ≤ 10),tabulated _ (by decide : 7 ≤ 10),
      tabulated _ (by decide : 6 ≤ 10)]
    apply by_three (s := s)
    decide +kernel
  | succ m ih =>
    change completions ((m+10)+1) s = 6*completions ((m+9)+1) s -
      12*completions ((m+8)+1) s + 10*completions ((m+7)+1) s - 3*completions ((m+6)+1) s
    have grow (k : ℕ) : completions (k+1) s = completions k (step s 0) +
        completions k (step s 1) + completions k (step s 2) := rfl
    rw [grow (m+10),grow (m+9),grow (m+8),grow (m+7),grow (m+6)]
    linarith [ih (step s 0),ih (step s 1),ih (step s 2)]
end OMA.WordsThree

namespace OMA.WordsThree
open OMA.S_oeis_a183885 PowerSeries
private theorem rec (n : ℕ) (hn : 6 < n) :
    a n = 6*a (n-1) - 12*a (n-2) + 10*a (n-3) - 3*a (n-4) := by
  simp only [a_eq _ (by omega : n ≠ 0),a_eq _ (by omega : n-1 ≠ 0),
    a_eq _ (by omega : n-2 ≠ 0),a_eq _ (by omega : n-3 ≠ 0),a_eq _ (by omega : n-4 ≠ 0)]
  simpa only [show n-7+10 = n+3 by omega,
    show n-7+9 = (n-1)+3 by omega,
    show n-7+8 = (n-2)+3 by omega,
    show n-7+7 = (n-3)+3 by omega,
    show n-7+6 = (n-4)+3 by omega] using relation (n-7) (stateOf (fun _ => 0))
private theorem value0 : a 0 = 0 := by
  rfl
private theorem value1 : a 1 = 1 := by
  rw [a_eq _ (by decide), tabulated _ (by decide)]
  decide +kernel
private theorem value2 : a 2 = 121 := by
  rw [a_eq _ (by decide), tabulated _ (by decide)]
  decide +kernel
private theorem value3 : a 3 = 631 := by
  rw [a_eq _ (by decide), tabulated _ (by decide)]
  decide +kernel
private theorem value4 : a 4 = 2059 := by
  rw [a_eq _ (by decide), tabulated _ (by decide)]
  decide +kernel
private theorem value5 : a 5 = 6399 := by
  rw [a_eq _ (by decide), tabulated _ (by decide)]
  decide +kernel
private theorem value6 : a 6 = 19483 := by
  rw [a_eq _ (by decide), tabulated _ (by decide)]
  decide +kernel

private theorem closed (n : ℕ) (hn : 3 ≤ n) : a n = 3^(n+3) - 2*((n : ℤ)+4)^2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n ≤ 6
    · interval_cases n <;> norm_num [value3,value4,value5,value6]
    · rw [rec n (by omega)]
      rw [ih (n-1) (by omega) (by omega)]
      rw [ih (n-2) (by omega) (by omega)]
      rw [ih (n-3) (by omega) (by omega)]
      rw [ih (n-4) (by omega) (by omega)]
      simp (disch := omega) only [Nat.cast_sub,Nat.cast_one,Nat.cast_ofNat]
      rw [show (3 : ℤ)^(n+3) = 3^(n-1)*3^4 by rw [←pow_add]; congr 1 <;> omega]
      rw [pow_add (3 : ℤ) (n-1) 3]
      rw [show (3 : ℤ)^((n-2)+3) = 3^(n-1)*3^2 by rw [←pow_add]; congr 1 <;> omega]
      rw [show (3 : ℤ)^((n-3)+3) = 3^(n-1)*3^1 by rw [←pow_add]; congr 1 <;> omega]
      rw [show (n-4)+3 = n-1 by omega]
      ring

private theorem gf : PowerSeries.mk a * ((1-X)^3*(1-3*X)) = X*(1+115*X-83*X^2-285*X^3+410*X^4-150*X^5) := by
  have d : ((1-X)^3*(1-3*X) : PowerSeries ℤ) = C (1 : ℤ) * X ^ 0 + C (-6 : ℤ) * X ^ 1 + C (12 : ℤ) * X ^ 2 + C (-10 : ℤ) * X ^ 3 + C (3 : ℤ) * X ^ 4 := by
    simp only [map_ofNat, map_one, map_neg]; ring
  have b : (X*(1+115*X-83*X^2-285*X^3+410*X^4-150*X^5) : PowerSeries ℤ) = C (1 : ℤ) * X ^ 1 + C (115 : ℤ) * X ^ 2 + C (-83 : ℤ) * X ^ 3 + C (-285 : ℤ) * X ^ 4 + C (410 : ℤ) * X ^ 5 + C (-150 : ℤ) * X ^ 6 := by
    simp only [map_ofNat, map_one, map_neg]; ring
  have expand (F : PowerSeries ℤ) : F * (C (1 : ℤ) * X ^ 0 + C (-6 : ℤ) * X ^ 1 + C (12 : ℤ) * X ^ 2 + C (-10 : ℤ) * X ^ 3 + C (3 : ℤ) * X ^ 4) = C (1 : ℤ) * (F * X ^ 0) + C (-6 : ℤ) * (F * X ^ 1) + C (12 : ℤ) * (F * X ^ 2) + C (-10 : ℤ) * (F * X ^ 3) + C (3 : ℤ) * (F * X ^ 4) := by ring
  rw [d,b,expand]
  ext n
  simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C]
  by_cases h : n ≤ 6
  · interval_cases n <;> norm_num [value0,value1,value2,value3,value4,value5,value6]
  · have hr := rec n (by omega)
    simp (disch := omega) only [if_pos,if_neg,Nat.sub_zero]
    linarith
end OMA.WordsThree

theorem OMA.solution : type_of% @OMA.S_oeis_a183885.main :=
  ⟨OMA.WordsThree.closed, OMA.WordsThree.gf, OMA.WordsThree.rec⟩
