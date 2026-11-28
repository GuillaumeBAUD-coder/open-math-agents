import OMAStatements.S_oeis_a250065
import Mathlib

/- The threshold-set recursion is adapted from @Salofe’s merged proofs of A249963 and A250064. -/
namespace OMA.WindowCount
open OMA.S_oeis_a250065 Finset

def Cy (y : Fin 7 → ℕ) : Prop :=
  ∃ S ∈ (univ : Finset (Fin 7)).powersetCard 2, ∃ v, (∀ t ∈ S, y t ≤ v) ∧ (∃ t ∈ S, y t = v) ∧
    (∀ t ∉ S, v ≤ y t) ∧ (∃ t ∉ S, y t = v)



theorem pair_iff (y : Fin 7 → ℕ) : MaxPairEqMinRest y ↔ Cy y := by
  constructor
  · rintro ⟨i,j,hij,hm⟩
    let S : Finset (Fin 7) := {i,j}
    have hS : S.card = 2 := by simp [S,hij]
    have hc : Sᶜ.Nonempty := by
      apply card_pos.mp
      rw [card_compl,hS]
      decide
    let v := max (y i) (y j)
    have he : (v : WithTop ℕ) = Sᶜ.inf (fun k => (y k : WithTop ℕ)) := hm
    obtain ⟨k,hk,ek⟩ := exists_mem_eq_inf Sᶜ hc (fun t => (y t : WithTop ℕ))
    refine ⟨S,mem_powersetCard.mpr ⟨subset_univ _,hS⟩,v,?_,?_,?_,?_⟩
    · intro t ht
      rcases mem_insert.mp ht with rfl | ht
      · exact le_max_left _ _
      · obtain rfl := mem_singleton.mp ht
        exact le_max_right _ _
    · rcases le_total (y i) (y j) with h|h
      · exact ⟨j,by simp [S],(max_eq_right h).symm⟩
      · exact ⟨i,by simp [S],(max_eq_left h).symm⟩
    · intro t ht
      exact WithTop.coe_le_coe.mp (he.trans_le (inf_le (mem_compl.mpr ht)))
    · exact ⟨k,mem_compl.mp hk,WithTop.coe_injective (he.trans ek).symm⟩
  · rintro ⟨S,hS,v,hlo,⟨i0,hi0,ei⟩,hhi,⟨k,hk,ek⟩⟩
    obtain ⟨i,j,hij,rfl⟩ := card_eq_two.mp (mem_powersetCard.mp hS).2
    refine ⟨i,j,hij,?_⟩
    have hm : max (y i) (y j) = v := by
      apply le_antisymm (max_le (hlo i (by simp)) (hlo j (by simp)))
      rcases mem_insert.mp hi0 with rfl | hj
      · exact ei ▸ le_max_left _ _
      · obtain rfl := mem_singleton.mp hj
        exact ei ▸ le_max_right _ _
    rw [hm]
    apply le_antisymm
    · exact Finset.le_inf (fun t ht => WithTop.coe_le_coe.mpr (hhi t (mem_compl.mp ht)))
    · rw [← ek]
      exact inf_le (mem_compl.mpr hk)

theorem cy_to (y : Fin 7 → ℕ) (h : Cy y) (w : ℕ) : (univ.filter (fun t => y t ≤ w)).card ≠ 2 := by
  obtain ⟨S, hS, v, h1, ⟨s, hs, hsv⟩, h3, ⟨t0, ht0, ht0v⟩⟩ := h
  have hc : S.card = 2 := (Finset.mem_powersetCard.1 hS).2
  by_cases hw : w < v
  · have hsub : univ.filter (fun t => y t ≤ w) ⊆ S.erase s := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      have htS : t ∈ S := by
        by_contra hn
        have := h3 t hn
        omega
      refine Finset.mem_erase.2 ⟨?_, htS⟩
      rintro rfl
      omega
    have h1' := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hs, hc] at h1'
    omega
  · have hsub : insert t0 S ⊆ univ.filter (fun t => y t ≤ w) := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_insert.1 ht with rfl | ht'
      · omega
      · have := h1 t ht'
        omega
    have h1' := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem ht0, hc] at h1'
    omega

theorem cy_of (y : Fin 7 → ℕ) (h : ∀ w : ℕ, (univ.filter (fun t => y t ≤ w)).card ≠ 2) :
    Cy y := by
  set U := univ.filter (fun s => 2 ≤ (univ.filter (fun t => y t ≤ y s)).card) with hU
  have hUne : U.Nonempty := by
    obtain ⟨m, _, hm⟩ := Finset.exists_max_image (univ : Finset (Fin 7)) y Finset.univ_nonempty
    refine ⟨m, ?_⟩
    rw [hU, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have : univ.filter (fun t => y t ≤ y m) = univ := by
      apply Finset.filter_true_of_mem
      intro t _
      exact hm t (Finset.mem_univ t)
    rw [this]
    simp
  obtain ⟨s, hsU, hmin⟩ := Finset.exists_min_image U y hUne
  have hs2 : 2 ≤ (univ.filter (fun t => y t ≤ y s)).card := by
    rw [hU, Finset.mem_filter] at hsU
    exact hsU.2
  have hs3 : 3 ≤ (univ.filter (fun t => y t ≤ y s)).card := by
    have := h (y s)
    omega
  set L := univ.filter (fun t => y t < y s) with hL
  set E := univ.filter (fun t => y t = y s) with hE
  have hLc : L.card ≤ 1 := by
    by_cases hLne : L.Nonempty
    · obtain ⟨l, hl, hlmax⟩ := Finset.exists_max_image L y hLne
      have hyl : y l < y s := by
        rw [hL, Finset.mem_filter] at hl
        exact hl.2
      have hlU : l ∉ U := by
        intro hlU
        have := hmin l hlU
        omega
      have hcl : (univ.filter (fun t => y t ≤ y l)).card ≤ 1 := by
        rw [hU, Finset.mem_filter] at hlU
        have : ¬ 2 ≤ (univ.filter (fun t => y t ≤ y l)).card :=
          fun h2 => hlU ⟨Finset.mem_univ _, h2⟩
        omega
      have hsub : L ⊆ univ.filter (fun t => y t ≤ y l) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hlmax t ht
      exact le_trans (Finset.card_le_card hsub) hcl
    · rw [Finset.not_nonempty_iff_eq_empty.mp hLne]
      simp
  have hsplit : (univ.filter (fun t => y t ≤ y s)) ⊆ L ∪ E := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [Finset.mem_union, hL, hE, Finset.mem_filter, Finset.mem_filter]
    rcases Nat.lt_or_ge (y t) (y s) with h' | h'
    · exact Or.inl ⟨Finset.mem_univ _, h'⟩
    · exact Or.inr ⟨Finset.mem_univ _, by omega⟩
  have hcard := le_trans (Finset.card_le_card hsplit) (Finset.card_union_le L E)
  have hsE : s ∈ E := by
    rw [hE, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hnotL : ∀ t, ¬ y t < y s → t ∉ L := by
    intro t ht htL
    rw [hL, Finset.mem_filter] at htL
    exact ht htL.2
  rcases Nat.lt_or_ge 0 L.card with hpos | hzero
  · -- one value below `y s`
    obtain ⟨l, hLl⟩ := Finset.card_eq_one.1 (by omega : L.card = 1)
    have hlL : l ∈ L := by rw [hLl]; exact Finset.mem_singleton_self l
    have hyl : y l < y s := by
      rw [hL, Finset.mem_filter] at hlL
      exact hlL.2
    have hE1 : 1 ≤ (E.erase s).card := by
      rw [Finset.card_erase_of_mem hsE]
      omega
    obtain ⟨e, he⟩ := Finset.card_pos.1 (by omega : 0 < (E.erase s).card)
    have hes : e ≠ s := (Finset.mem_erase.1 he).1
    have hye : y e = y s := by
      have := (Finset.mem_erase.1 he).2
      rw [hE, Finset.mem_filter] at this
      exact this.2
    have hls : l ≠ s := by
      rintro rfl
      omega
    refine ⟨{l, s}, ?_, y s, ?_, ⟨s, by simp, rfl⟩, ?_, ⟨e, ?_, hye⟩⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Finset.card_pair hls⟩
    · intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht'
      · omega
      · rw [Finset.mem_singleton.1 ht']
    · intro t ht
      by_contra hlt
      rw [not_le] at hlt
      have htL : t ∈ L := by
        rw [hL, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hlt⟩
      rw [hLl, Finset.mem_singleton] at htL
      apply ht
      rw [htL]
      exact Finset.mem_insert_self l {s}
    · intro he'
      rcases Finset.mem_insert.1 he' with rfl | he''
      · omega
      · exact hes (Finset.mem_singleton.1 he'')
  · -- no value below `y s`
    have hL0 : L.card = 0 := by omega
    have hE3 : 3 ≤ E.card := by omega
    have hE2 : 1 < (E.erase s).card := by
      rw [Finset.card_erase_of_mem hsE]
      omega
    obtain ⟨e1, he1, e2, he2, he12⟩ := Finset.one_lt_card.1 hE2
    have he1s : e1 ≠ s := (Finset.mem_erase.1 he1).1
    have he2s : e2 ≠ s := (Finset.mem_erase.1 he2).1
    have hye1 : y e1 = y s := by
      have := (Finset.mem_erase.1 he1).2
      rw [hE, Finset.mem_filter] at this
      exact this.2
    have hye2 : y e2 = y s := by
      have := (Finset.mem_erase.1 he2).2
      rw [hE, Finset.mem_filter] at this
      exact this.2
    have hLempty : L = ∅ := Finset.card_eq_zero.1 hL0
    refine ⟨{s, e1}, ?_, y s, ?_, ⟨s, by simp, rfl⟩, ?_, ⟨e2, ?_, hye2⟩⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Finset.card_pair he1s.symm⟩
    · intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht'
      · exact le_rfl
      · rw [Finset.mem_singleton.1 ht', hye1]
    · intro t _
      by_contra hlt
      rw [not_le] at hlt
      have htL : t ∈ L := by
        rw [hL, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hlt⟩
      rw [hLempty] at htL
      exact Finset.notMem_empty t htL
    · intro he'
      rcases Finset.mem_insert.1 he' with h' | h'
      · exact he2s h'
      · exact he12 (Finset.mem_singleton.1 h').symm

theorem window_iff (y : Fin 7 → ℕ) :
    Cy y ↔ ∀ v : ℕ, (univ.filter (fun t => y t ≤ v)).card ≠ 2 :=
  ⟨cy_to y, cy_of y⟩

/-! ### Negated window condition as a condition on consecutive strict threshold counts -/

theorem not_cy_iff (y : Fin 7 → ℕ) :
    ¬ Cy y ↔ ∀ v : ℕ, ¬ ((univ.filter (fun t => y t < v)).card ≤ 1 ∧
      3 ≤ (univ.filter (fun t => y t < v + 1)).card) := by
  rw [window_iff, not_forall]
  simp only [ne_eq, not_not]
  constructor
  · rintro ⟨w, hw⟩ v ⟨h1, h3⟩
    rcases Nat.lt_or_ge w v with h | h
    · have hsub : univ.filter (fun t => y t ≤ w) ⊆ univ.filter (fun t => y t < v) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        omega
      have := Finset.card_le_card hsub
      omega
    · have hsub : univ.filter (fun t => y t < v + 1) ⊆ univ.filter (fun t => y t ≤ w) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        omega
      have := Finset.card_le_card hsub
      omega
  · intro h
    by_contra hne
    simp only [not_exists] at hne
    have key : ∀ v, (univ.filter (fun t => y t < v)).card ≤ 1 := by
      intro v
      induction v with
      | zero => simp
      | succ v ih =>
        have h1 := h v
        have h2 := hne v
        have e : univ.filter (fun t => y t < v + 1) = univ.filter (fun t => y t ≤ v) := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        rw [e] at h1 ⊢
        by_contra hc
        exact h1 ⟨ih, by omega⟩
    have hall : univ.filter (fun t => y t < univ.sup y + 1) = univ := by
      apply Finset.filter_true_of_mem
      intro t _
      have := Finset.le_sup (f := y) (Finset.mem_univ t)
      omega
    have := key (univ.sup y + 1)
    rw [hall] at this
    simp at this



def fget (f : Fin 12 → Bool) (k : ℕ) : Bool := if h : k < 12 then f ⟨k, h⟩ else false

/-- Number of positions of window `i` lying in the set `f`. -/
def cntW (f : Fin 12 → Bool) (i : ℕ) : ℕ :=
  (univ.filter (fun t : Fin 7 => fget f (i + t) = true)).card

/-- Two consecutive strict threshold sets: no window goes from at most one position to at least
three positions. -/
def Comp (S T : Fin 12 → Bool) : Prop := ∀ i < (6 : ℕ), ¬ (cntW S i ≤ 1 ∧ 3 ≤ cntW T i)

instance decComp (S T : Fin 12 → Bool) : Decidable (Comp S T) := by
  unfold Comp
  infer_instance

/-- The positions where `x` is below `v`. -/
def Lt {n : ℕ} (x : Fin 12 → Fin (n + 1)) (v : ℕ) : Fin 12 → Bool :=
  fun p => decide ((x p : ℕ) < v)



def get {n : ℕ} (x : Fin 12 → Fin (n+1)) (k : ℕ) : ℕ := if h : k < 12 then (x ⟨k,h⟩).val else 0

theorem cnt_univ : ∀ i < (6 : ℕ), cntW (fun _ => true) i = 7 := by
  decide

theorem good_iff {n : ℕ} (x : Fin 12 → Fin (n + 1)) :
    (∀ s, ¬ MaxPairEqMinRest (window x s)) ↔ ∀ v ≤ n, Comp (Lt x v) (Lt x (v + 1)) := by


  have step1 : (∀ s, ¬ MaxPairEqMinRest (window x s)) ↔
      ∀ i < (6 : ℕ), ¬ Cy (fun t : Fin 7 => get x (i + t)) := by
    have aux (i : Fin 6) : window x i = fun t : Fin 7 => get x (i.val + t) := by
      funext t
      have ht := t.isLt
      have hi := i.isLt
      simp [window,get,show i.val+t.val < 12 by omega]
    constructor
    · intro h i hi
      simpa only [pair_iff,aux] using h ⟨i,hi⟩
    · intro h i
      simpa only [pair_iff,aux] using h i.val i.isLt

  have step2 : ∀ i < (6 : ℕ), ∀ v : ℕ,
      (univ.filter (fun t : Fin 7 => get x (i + t) < v)).card = cntW (Lt x v) i := by
    intro i hi v
    unfold cntW
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have ht : i + (t : ℕ) < 12 := by have := t.isLt; omega
    unfold get fget Lt
    rw [dif_pos ht, dif_pos ht, decide_eq_true_iff]
  have hfull : ∀ w, n < w → Lt x w = fun _ => true := by
    intro w hw
    funext p
    unfold Lt
    have := (x p).isLt
    simp only [decide_eq_true_iff]
    omega
  rw [step1]
  constructor
  · intro h v _ i hi
    have := (not_cy_iff _).1 (h i hi) v
    simp only [step2 i hi v, step2 i hi (v + 1)] at this
    exact this
  · intro h i hi
    rw [not_cy_iff]
    intro v
    simp only [step2 i hi v, step2 i hi (v + 1)]
    by_cases hv : v ≤ n
    · exact h v hv i hi
    · rw [hfull v (by omega), cnt_univ i hi]
      omega

/-! ### Chains of strict threshold sets -/

/-- Arrays with entries in `0..n` whose consecutive strict threshold sets are compatible, with
`Lt x n ⊆ T` and `Lt x n` compatible with `T`. -/
noncomputable def M (n : ℕ) (T : Fin 12 → Bool) : ℕ := by
  classical
  exact ((univ : Finset (Fin 12 → Fin (n + 1))).filter
    (fun x => (∀ p, Lt x n p = true → T p = true) ∧ (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧
      Comp (Lt x n) T)).card

theorem Lt_zero {n : ℕ} (x : Fin 12 → Fin (n + 1)) : Lt x 0 = fun _ => false := by
  funext p
  unfold Lt
  simp

theorem M_zero (T : Fin 12 → Bool) : M 0 T = if Comp (fun _ => false) T then 1 else 0 := by
  classical
  unfold M
  split_ifs with h
  · rw [Finset.filter_true_of_mem]
    · simp
    · intro x _
      refine ⟨fun p hp => ?_, fun v hv => absurd hv (Nat.not_lt_zero _), ?_⟩
      · rw [Lt_zero] at hp
        exact absurd hp (by simp)
      · rw [Lt_zero]
        exact h
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    apply h
    rw [← Lt_zero x]
    exact hx.2.2

/-- Restriction of an array with entries in `0..n+1` to entries in `0..n`. -/
def lower {n : ℕ} (x : Fin 12 → Fin (n + 2)) : Fin 12 → Fin (n + 1) :=
  fun p => ⟨min (x p : ℕ) n, by omega⟩

/-- Extension of an array with entries in `0..n` by the top value `n + 1` outside `S`. -/
def raise {n : ℕ} (S : Fin 12 → Bool) (x : Fin 12 → Fin (n + 1)) : Fin 12 → Fin (n + 2) :=
  fun p => if S p = true then ⟨x p, by omega⟩ else ⟨n + 1, by omega⟩

theorem Lt_lower {n : ℕ} (x : Fin 12 → Fin (n + 2)) (v : ℕ) (hv : v ≤ n) :
    Lt (lower x) v = Lt x v := by
  funext p
  show decide (min (x p : ℕ) n < v) = decide ((x p : ℕ) < v)
  rw [decide_eq_decide]
  constructor <;> intro h <;> omega

theorem raise_val {n : ℕ} (S : Fin 12 → Bool) (x : Fin 12 → Fin (n + 1)) (p : Fin 12) :
    ((raise S x p : Fin (n + 2)) : ℕ) = if S p = true then (x p : ℕ) else n + 1 := by
  unfold raise
  split_ifs <;> rfl

theorem M_succ (n : ℕ) (T : Fin 12 → Bool) :
    M (n + 1) T = ∑ S : Fin 12 → Bool,
      if Comp S T ∧ (∀ p, S p = true → T p = true) then M n S else 0 := by
  classical
  unfold M
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => Lt x (n + 1)) (t := univ)
    (fun x _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.filter_filter]
  split_ifs with hS
  · apply Finset.card_bij' (fun x _ => lower x) (fun x _ => raise S x)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨⟨_, h2, _⟩, h3⟩ := hx
      refine ⟨fun p hp => ?_, fun v hv => ?_, ?_⟩
      · rw [Lt_lower x n le_rfl] at hp
        rw [← h3]
        have hp' : (x p : ℕ) < n := of_decide_eq_true hp
        exact decide_eq_true (by omega)
      · rw [Lt_lower x v (by omega), Lt_lower x (v + 1) (by omega)]
        exact h2 v (by omega)
      · rw [Lt_lower x n le_rfl, ← h3]
        exact h2 n (by omega)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨h1, h2, h3⟩ := hx
      have hTS : Lt (raise S x) (n + 1) = S := by
        funext p
        show decide (((raise S x p : Fin (n + 2)) : ℕ) < n + 1) = S p
        rw [raise_val]
        by_cases hp : S p = true
        · rw [if_pos hp, hp]
          have := (x p).isLt
          exact decide_eq_true (by omega)
        · rw [if_neg hp]
          simp only [Bool.not_eq_true] at hp
          rw [hp]
          exact decide_eq_false (by omega)
      have hlow : ∀ v ≤ n, Lt (raise S x) v = Lt x v := by
        intro v hv
        funext p
        show decide (((raise S x p : Fin (n + 2)) : ℕ) < v) = decide ((x p : ℕ) < v)
        rw [raise_val]
        split_ifs with hp
        · rfl
        · have hxp : ¬ (x p : ℕ) < n := fun h => hp (h1 p (decide_eq_true h))
          rw [decide_eq_decide]
          omega
      refine ⟨⟨?_, fun v hv => ?_, ?_⟩, hTS⟩
      · rw [hTS]
        exact hS.2
      · rcases Nat.lt_or_ge v n with hv' | hv'
        · rw [hlow v (by omega), hlow (v + 1) (by omega)]
          exact h2 v hv'
        · obtain rfl : v = n := by omega
          rw [hlow v le_rfl, hTS]
          exact h3
      · rw [hTS]
        exact hS.1
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨_, h3⟩ := hx
      funext p
      apply Fin.ext
      rw [raise_val]
      have hiff : S p = true ↔ (x p : ℕ) < n + 1 := by
        rw [← h3]
        exact decide_eq_true_iff
      split_ifs with hp
      · show min (x p : ℕ) n = x p
        have := hiff.1 hp
        omega
      · have : ¬ (x p : ℕ) < n + 1 := fun h => hp (hiff.2 h)
        have := (x p).isLt
        omega
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨h1, _⟩ := hx
      funext p
      apply Fin.ext
      show min ((raise S x p : Fin (n + 2)) : ℕ) n = x p
      rw [raise_val]
      split_ifs with hp
      · have := (x p).isLt
        omega
      · have hxp : ¬ (x p : ℕ) < n := fun h => hp (h1 p (decide_eq_true h))
        have := (x p).isLt
        omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _
    rintro ⟨⟨h1, _, h3⟩, h4⟩
    apply hS
    rw [← h4]
    exact ⟨h3, h1⟩

/-! ### Codes -/

/-- The set of positions with code `u`: position `p` is in it iff bit `p` of `u` is set. -/
def row (u : Fin 4096) : Fin 12 → Bool := fun p => Nat.testBit u.val p.val

theorem blocks (P : Fin 4096 → Prop)
    (h : ∀ j : Fin 64, ∀ i : Fin 64, P ⟨j.val*64+i.val,by have := j.isLt; have := i.isLt; omega⟩) :
    ∀ u : Fin 4096, P u := by
  intro u
  have hu := u.isLt
  have e := h ⟨u.val / 64,by omega⟩ ⟨u.val % 64, Nat.mod_lt _ (by decide)⟩
  convert e using 2
  dsimp
  omega

theorem row_injective : Function.Injective row := by
  intro a b h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · exact congrFun h ⟨i,hi⟩
  · have hb : 4096 ≤ 2^i := by
      calc 4096 = 2^12 := by decide
           _ ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (a.isLt.trans_le hb), Nat.testBit_eq_false_of_lt (b.isLt.trans_le hb)]

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩



def lowPack : ℕ → ℕ
  | 0 => 0x820820820820820820820820c30c30c30c30e38e38f3cfbfc30c30c30c30e38e38f3cfbfe38e38f3cfbff3cfbffbffff
  | 1 => 0x820820820820820820820820c30c30c30c30e38e38f3cfbf
  | 2 => 0x1820820820820820820820821c30c30c30c31e38e39f3dfff
  | 3 => 0x1
  | 4 => 0x838208208208208208208208a3c30c30c30cb3e38ebbfbffff
  | 5 => 0x83
  | 6 => 0x10000000000000000000000010000000000010000010010c3
  | 7 => 0x1
  | 8 => 0x1041878208208208208208209249a7c30c30d34db7f3cfbffbffff
  | 9 => 0x104187
  | 10 => 0x10000000000000000000000010000000000010000011051c7
  | 11 => 0x1
  | 12 => 0x830000000000000000000000830000000000830000831871c7
  | 13 => 0x83
  | 14 => 0x10000000000000000000000010000000000010000010010c3
  | 15 => 0x1
  | 16 => 0x20820830c38f820820820820a28a28b2cbafe38e38f3cfbff3cfbffbffff
  | 17 => 0x20820830c38f
  | 18 => 0x100000000000000000000000100000000000120820930d3cf
  | 19 => 0x1
  | 20 => 0x8300000000000000000000008300000000008320828b38f3cf
  | 21 => 0x83
  | 22 => 0x10000000000000000000000010000000000010000010010c3
  | 23 => 0x1
  | 24 => 0x10418700000000000000000010418700000010418730c38f38f3cf
  | 25 => 0x104187
  | 26 => 0x10000000000000000000000010000000000010000011051c7
  | 27 => 0x1
  | 28 => 0x830000000000000000000000830000000000830000831871c7
  | 29 => 0x83
  | 30 => 0x10000000000000000000000010000000000010000010010c3
  | 31 => 0x1
  | 32 => 0x41041041041061861871c79fc30c30c30c30e38e38f3cfbfe38e38f3cfbff3cfbffbffff
  | 33 => 0x41041041041061861871c79f
  | 34 => 0x100000000000000000000000141041041041161861971d7df
  | 35 => 0x1
  | 36 => 0x8300000000000000000000008341041041049361869b79f7df
  | 37 => 0x83
  | 38 => 0x10000000000000000000000010000000000010000010010c3
  | 39 => 0x1
  | 40 => 0x10418700000000000000000010418741041051459771c79f79f7df
  | 41 => 0x104187
  | 42 => 0x10000000000000000000000010000000000010000011051c7
  | 43 => 0x1
  | 44 => 0x830000000000000000000000830000000000830000831871c7
  | 45 => 0x83
  | 46 => 0x10000000000000000000000010000000000010000010010c3
  | 47 => 0x1
  | 48 => 0x20820830c38f00000000000020820830c38f61861871c79f71c79f79f7df
  | 49 => 0x20820830c38f
  | 50 => 0x100000000000000000000000100000000000120820930d3cf
  | 51 => 0x1
  | 52 => 0x8300000000000000000000008300000000008320828b38f3cf
  | 53 => 0x83
  | 54 => 0x10000000000000000000000010000000000010000010010c3
  | 55 => 0x1
  | 56 => 0x10418700000000000000000010418700000010418730c38f38f3cf
  | 57 => 0x104187
  | 58 => 0x10000000000000000000000010000000000010000011051c7
  | 59 => 0x1
  | 60 => 0x830000000000000000000000830000000000830000831871c7
  | 61 => 0x83
  | 62 => 0x10000000000000000000000010000000000010000010010c3
  | 63 => 0x1
  | _ => 0

def low (u : ℕ) : ℕ := (lowPack (u / 64) >>> (6*(u % 64))) % 64

def highPack : ℕ → ℕ
  | 0 => 0x3cf3cf3cf3cf1c71c70c30401c71c70c30400c30400400001c71c70c30400c30400400000c3040040000040000000000
  | 1 => 0x7df7df7df7df7df7df7df7df3cf3cf3cf3cf1c71c70c30403cf3cf3cf3cf1c71c70c30401c71c70c30400c3040040000
  | 2 => 0x7df7df7df7df7df7df7df7de3cf3cf3cf3ce1c71c60c20003cf3cf3cf3ce1c71c60c20001c71c60c20000c2000000000
  | 3 => 0xfffffffffffffffffffffffffffffffffffffffffffffffe7df7df7df7df7df7df7df7de3cf3cf3cf3ce1c71c60c2000
  | 4 => 0x7df7df7df7df7df7df7df75c3cf3cf3cf34c1c71440400003cf3cf3cf34c1c71440400001c7144040000040000000000
  | 5 => 0xffffffffffffffffffffffffffffffffffffffffffffff7c7df7df7df7df7df7df7df75c3cf3cf3cf34c1c7144040000
  | 6 => 0xfffffffffffffffffffffffefffffffffffefffffeffef3c7df7df7df7de7df7de7de71c3cf3ce3ce30c1c6104000000
  | 7 => 0xfffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffefffffffffffefffffeffef3c
  | 8 => 0x7df7df7df7df7df7df6db6583cf3cf2cb2480c30400400003cf3cf2cb2480c30400400000c3040040000040000000000
  | 9 => 0xffffffffffffffffffffffffffffffffffffffffffefbe787df7df7df7df7df7df6db6583cf3cf2cb2480c3040040000
  | 10 => 0xfffffffffffffffffffffffefffffffffffefffffeefae387df7df7df7de7df7de6da6183cf3ce2ca2080c2000000000
  | 11 => 0xfffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffefffffffffffefffffeefae38
  | 12 => 0xffffffffffffffffffffff7cffffffffff7cffff7ce78e387df7df7df75c7df75c6586183cf34c248208040000000000
  | 13 => 0xffffffffffffffffffffffffffffffffffffffffffffff7cffffffffffffffffffffff7cffffffffff7cffff7ce78e38
  | 14 => 0xfffffffffffffffffffffffefffffffffffefffffeffef3cfffffffffffefffffeffef3cfffffeffef3cffef3ce38e38
  | 15 => 0xfffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffefffffffffffefffffeffef3c
  | 16 => 0x7df7df7df7df5d75d74d34501c71c70c30400c30400400001c71c70c30400c30400400000c3040040000040000000000
  | 17 => 0xffffffffffffffffffffffffffffffffffffdf7df7cf3c707df7df7df7df5d75d74d34501c71c70c30400c3040040000
  | 18 => 0xfffffffffffffffffffffffefffffffffffedf7df6cf2c307df7df7df7de5d75d64d24101c71c60c20000c2000000000
  | 19 => 0xfffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffefffffffffffedf7df6cf2c30
  | 20 => 0xffffffffffffffffffffff7cffffffffff7cdf7d74c70c307df7df7df75c5d75544504101c7144040000040000000000
  | 21 => 0xffffffffffffffffffffffffffffffffffffffffffffff7cffffffffffffffffffffff7cffffffffff7cdf7d74c70c30
  | 22 => 0xfffffffffffffffffffffffefffffffffffefffffeffef3cfffffffffffefffffeffef3cfffffeffef3cdf6d34c30c30
  | 23 => 0xfffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffefffffffffffefffffeffef3c
  | 24 => 0xffffffffffffffffffefbe78ffffffefbe78cf3c70c70c307df7df6db6584d34504504100c3040040000040000000000
  | 25 => 0xffffffffffffffffffffffffffffffffffffffffffefbe78ffffffffffffffffffefbe78ffffffefbe78cf3c70c70c30
  | 26 => 0xfffffffffffffffffffffffefffffffffffefffffeefae38fffffffffffefffffeefae38fffffeefae38cf2c30c30c30
  | 27 => 0xfffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffefffffffffffefffffeefae38
  | 28 => 0xffffffffffffffffffffff7cffffffffff7cffff7ce78e38ffffffffff7cffff7ce78e38ffff7ce78e38c70c30c30c30
  | 29 => 0xffffffffffffffffffffffffffffffffffffffffffffff7cffffffffffffffffffffff7cffffffffff7cffff7ce78e38
  | 30 => 0xfffffffffffffffffffffffefffffffffffefffffeffef3cfffffffffffefffffeffef3cfffffeffef3cffef3ce38e38
  | 31 => 0xfffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffefffffffffffefffffeffef3c
  | 32 => 0x3cf3cf3cf3cf1c71c70c30401c71c70c30400c30400400001c71c70c30400c30400400000c3040040000040000000000
  | 33 => 0xffffffffffffffffffffffffbefbefbefbef9e79e78e38603cf3cf3cf3cf1c71c70c30401c71c70c30400c3040040000
  | 34 => 0xfffffffffffffffffffffffebefbefbefbee9e79e68e28203cf3cf3cf3ce1c71c60c20001c71c60c20000c2000000000
  | 35 => 0xfffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffebefbefbefbee9e79e68e2820
  | 36 => 0xffffffffffffffffffffff7cbefbefbefb6c9e79648608203cf3cf3cf34c1c71440400001c7144040000040000000000
  | 37 => 0xffffffffffffffffffffffffffffffffffffffffffffff7cffffffffffffffffffffff7cbefbefbefb6c9e7964860820
  | 38 => 0xfffffffffffffffffffffffefffffffffffefffffeffef3cfffffffffffefffffeffef3cbefbeebeeb2c9e6924820820
  | 39 => 0xfffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffefffffffffffefffffeffef3c
  | 40 => 0xffffffffffffffffffefbe78befbefaeba688e38608608203cf3cf2cb2480c30400400000c3040040000040000000000
  | 41 => 0xffffffffffffffffffffffffffffffffffffffffffefbe78ffffffffffffffffffefbe78befbefaeba688e3860860820
  | 42 => 0xfffffffffffffffffffffffefffffffffffefffffeefae38fffffffffffefffffeefae38befbeeaeaa288e2820820820
  | 43 => 0xfffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffefffffffffffefffffeefae38
  | 44 => 0xffffffffffffffffffffff7cffffffffff7cffff7ce78e38ffffffffff7cffff7ce78e38befb6ca68a28860820820820
  | 45 => 0xffffffffffffffffffffffffffffffffffffffffffffff7cffffffffffffffffffffff7cffffffffff7cffff7ce78e38
  | 46 => 0xfffffffffffffffffffffffefffffffffffefffffeffef3cfffffffffffefffffeffef3cfffffeffef3cffef3ce38e38
  | 47 => 0xfffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffefffffffffffefffffeffef3c
  | 48 => 0xffffffffffffdf7df7cf3c709e79e78e38608e38608608201c71c70c30400c30400400000c3040040000040000000000
  | 49 => 0xffffffffffffffffffffffffffffffffffffdf7df7cf3c70ffffffffffffdf7df7cf3c709e79e78e38608e3860860820
  | 50 => 0xfffffffffffffffffffffffefffffffffffedf7df6cf2c30fffffffffffedf7df6cf2c309e79e68e28208e2820820820
  | 51 => 0xfffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffefffffffffffedf7df6cf2c30
  | 52 => 0xffffffffffffffffffffff7cffffffffff7cdf7d74c70c30ffffffffff7cdf7d74c70c309e7964860820860820820820
  | 53 => 0xffffffffffffffffffffffffffffffffffffffffffffff7cffffffffffffffffffffff7cffffffffff7cdf7d74c70c30
  | 54 => 0xfffffffffffffffffffffffefffffffffffefffffeffef3cfffffffffffefffffeffef3cfffffeffef3cdf6d34c30c30
  | 55 => 0xfffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffefffffffffffefffffeffef3c
  | 56 => 0xffffffffffffffffffefbe78ffffffefbe78cf3c70c70c30ffffffefbe78cf3c70c70c308e3860860820860820820820
  | 57 => 0xffffffffffffffffffffffffffffffffffffffffffefbe78ffffffffffffffffffefbe78ffffffefbe78cf3c70c70c30
  | 58 => 0xfffffffffffffffffffffffefffffffffffefffffeefae38fffffffffffefffffeefae38fffffeefae38cf2c30c30c30
  | 59 => 0xfffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffefffffffffffefffffeefae38
  | 60 => 0xffffffffffffffffffffff7cffffffffff7cffff7ce78e38ffffffffff7cffff7ce78e38ffff7ce78e38c70c30c30c30
  | 61 => 0xffffffffffffffffffffffffffffffffffffffffffffff7cffffffffffffffffffffff7cffffffffff7cffff7ce78e38
  | 62 => 0xfffffffffffffffffffffffefffffffffffefffffeffef3cfffffffffffefffffeffef3cfffffeffef3cffef3ce38e38
  | 63 => 0xfffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffefffffffffffefffffeffef3c
  | _ => 0

def high (u : ℕ) : ℕ := (highPack (u / 64) >>> (6*(u % 64))) % 64

def compc (s t : ℕ) : Bool := (low s &&& high t) == 0

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 65536 in
theorem compc_iff (s t : Fin 4096) : Comp (row s) (row t) ↔ compc s.val t.val = true := by

  have lowSpec : ∀ u : Fin 4096, (((low u.val).testBit 0) = true ↔ cntW (row u) 0 ≤ 1) ∧ (((low u.val).testBit 1) = true ↔ cntW (row u) 1 ≤ 1) ∧ (((low u.val).testBit 2) = true ↔ cntW (row u) 2 ≤ 1) ∧ (((low u.val).testBit 3) = true ↔ cntW (row u) 3 ≤ 1) ∧ (((low u.val).testBit 4) = true ↔ cntW (row u) 4 ≤ 1) ∧ (((low u.val).testBit 5) = true ↔ cntW (row u) 5 ≤ 1) := by
    apply blocks
    intro j
    fin_cases j <;> decide +kernel

  have highSpec : ∀ u : Fin 4096, (((high u.val).testBit 0) = true ↔ cntW (row u) 0 ≥ 3) ∧ (((high u.val).testBit 1) = true ↔ cntW (row u) 1 ≥ 3) ∧ (((high u.val).testBit 2) = true ↔ cntW (row u) 2 ≥ 3) ∧ (((high u.val).testBit 3) = true ↔ cntW (row u) 3 ≥ 3) ∧ (((high u.val).testBit 4) = true ↔ cntW (row u) 4 ≥ 3) ∧ (((high u.val).testBit 5) = true ↔ cntW (row u) 5 ≥ 3) := by
    apply blocks
    intro j
    fin_cases j <;> decide +kernel

  have maskSpec : ∀ a : Fin 64, ∀ b : Fin 64, ((a.val &&& b.val) == 0) = true ↔ ¬ (a.val.testBit 0 = true ∧ b.val.testBit 0 = true) ∧ ¬ (a.val.testBit 1 = true ∧ b.val.testBit 1 = true) ∧ ¬ (a.val.testBit 2 = true ∧ b.val.testBit 2 = true) ∧ ¬ (a.val.testBit 3 = true ∧ b.val.testBit 3 = true) ∧ ¬ (a.val.testBit 4 = true ∧ b.val.testBit 4 = true) ∧ ¬ (a.val.testBit 5 = true ∧ b.val.testBit 5 = true) := by decide +kernel

  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := lowSpec s
  obtain ⟨g0,g1,g2,g3,g4,g5⟩ := highSpec t

  unfold compc
  rw [maskSpec ⟨low s.val, Nat.mod_lt _ (by decide)⟩ ⟨high t.val,Nat.mod_lt _ (by decide)⟩]
  simp only [h0,h1,h2,h3,h4,h5,g0,g1,g2,g3,g4,g5]
  constructor
  · intro h
    exact ⟨h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide),h 4 (by decide),h 5 (by decide)⟩
  · rintro ⟨p0,p1,p2,p3,p4,p5⟩ i hi
    interval_cases i <;> assumption

theorem sub_iff (w u : Fin 4096) : (∀ p, row w p = true → row u p = true) ↔
    (w.val &&& u.val == w.val) = true := by
  rw [beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land]
    by_cases hi : i < 12
    · have := h ⟨i, hi⟩
      unfold row at this
      cases hw : w.val.testBit i <;> simp_all
    · have hw : w.val.testBit i = false := by
        apply Nat.testBit_eq_false_of_lt
        have h1 : (4096 : ℕ) ≤ 2 ^ i := by
          calc (4096 : ℕ) = 2 ^ 12 := by norm_num
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
        have := w.isLt
        omega
      simp [hw]
  · intro h p hp
    unfold row at hp ⊢
    rw [← h, Nat.testBit_land] at hp
    simp only [Bool.and_eq_true] at hp
    exact hp.2

/-- The codes of the subsets of the set with code `u`. -/
def subs (u : Fin 4096) : Finset (Fin 4096) :=
  univ.filter (fun w : Fin 4096 => (w.val &&& u.val == w.val) = true)

/-- The chain recursion on codes. -/
def G : ℕ → Fin 4096 → ℕ
  | 0, u => if compc 0 u.val = true then 1 else 0
  | n + 1, u => ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0

theorem row_zero : row 0 = fun _ => false := by
  funext p
  simp [row]

theorem M_eq_G (n : ℕ) : ∀ u : Fin 4096, M n (row u) = G n u := by
  induction n with
  | zero =>
    intro u
    rw [M_zero, ← row_zero, G]
    exact if_congr (compc_iff 0 u) rfl rfl
  | succ n ih =>
    intro u
    rw [M_succ, ← row_bijective.sum_comp]
    simp only [G, subs]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ih w]
    by_cases h1 : (w.val &&& u.val == w.val) = true
    · rw [if_pos h1]
      exact if_congr ((and_iff_left ((sub_iff w u).2 h1)).trans (compc_iff w u)) rfl rfl
    · rw [if_neg h1, if_neg (fun h => h1 ((sub_iff w u).1 h.2))]

theorem row_full : ∀ p, row 4095 p = true := by
  decide

theorem a_eq_G (n : ℕ) : a n = G n 4095 := by
  classical
  have h1 : (univ.filter (fun x : Fin 12 → Fin (n + 1) => ∀ s, ¬ MaxPairEqMinRest (window x s))) =
      univ.filter (fun x => (∀ p, Lt x n p = true → row 4095 p = true) ∧
        (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧ Comp (Lt x n) (row 4095)) := by
    apply Finset.filter_congr
    intro x _
    rw [good_iff]
    have hr : row 4095 = fun _ => true := funext row_full
    have hn : Lt x (n + 1) = row 4095 := by
      rw [hr]
      funext p
      unfold Lt
      have := (x p).isLt
      simp only [decide_eq_true_iff]
      omega
    constructor
    · intro h
      refine ⟨fun p _ => row_full p, fun v hv => h v (by omega), ?_⟩
      rw [← hn]
      exact h n le_rfl
    · rintro ⟨_, h2, h3⟩ v hv
      rcases Nat.lt_or_ge v n with h | h
      · exact h2 v h
      · obtain rfl : v = n := by omega
        rw [hn]
        exact h3
  unfold a
  rw [h1, ← M_eq_G]
  unfold M
  rfl



theorem G_succ (n : ℕ) (u : Fin 4096) :
    G (n + 1) u = ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0 :=
  rfl



def stateIndexPack : ℕ → ℕ
  | 0 => 0x30140a040281008030281008030200c06020281008030200c06020200c06020180804010281008030200c06020200c06020180804010200c0602018080401018080401010040200
  | 1 => 0x38180c05030140a04030140a04028100803030140a040281008030281008030200c0602030140a040281008030281008030200c06020281008030200c06020200c0602018080401
  | 2 => 0x78381a0c06830160a06830160a05828120306830160a0582812030582812030480c100206830160a0582812030582812030480c10020582812030480c10020480c1002040080401
  | 3 => 0x88401e0e078381a0c078381a0c06830160a078381a0c06830160a06830160a058281203078381a0c06830160a06830160a05828120306830160a0582812030582812030480c1002
  | 4 => 0xb8342c0c0a82c280a0a82c280a0982412030a82c280a0982412030982412030902010020a82c280a098241203098241203090201002098241203090201002090201002040080401
  | 5 => 0xc83c300e0b8342c0c0b8342c0c0a82c280a0b8342c0c0a82c280a0a82c280a0982412030b8342c0c0a82c280a0a82c280a0982412030a82c280a098241203098241203090201002
  | 6 => 0x13094482311084401f11084401f0f074380a11084401f0f074380a0f074380a0d824240311084401f0f074380a0f074380a0d82424030f074380a0d82424030d82424030d0201002
  | 7 => 0x190c4602f170b4582b170b4582b150a4500c170b4582b150a4500c150a4500c1382c260413094482311084401f11084401f0f074380a11084401f0f074380a0f074380a0d8242403
  | 8 => 0x1b0542a0b1a850280a1a04c26090982412031a04c26090982412031984824080902010021a04c2609098241203198482408090201002198482408090201002090201002040080401
  | 9 => 0x1c05c2e0d1b8582c0c1b0542a0b1a850280a1b0542a0b1a850280a1a04c26090982412031b0542a0b1a850280a1a04c26090982412031a04c2609098241203198482408090201002
  | 10 => 0x211044421200fc401f1f0f43c1d1e0ec380a1f0f43c1d1e0ec380a1d07036090d82424031f0f43c1d1e0ec380a1d07036090d82424031d07036090d82424031c84834080d0201002
  | 11 => 0x2612c5c2d25124582b2411c542923114500c2411c542923114500c220a04e0b218502604211044421200fc401f1f0f43c1d1e0ec380a1f0f43c1d1e0ec380a1d07036090d8242403
  | 12 => 0x2b088aa212a080a61f29078a21d28070380a29078a21d28070380a2786c360927048240329078a21d28070380a2786c36092704824032786c36092704824032686834080d0201002
  | 13 => 0x300b8be2d2f0b0ba2b2e0a8b6292d0a0b20c2e0a8b6292d0a0b20c2c09c860b2b84c26042b088aa212a080a61f29078a21d28070380a29078a21d28070380a2786c3609270482403
  | 14 => 0x3d1e4f0773b1d4e823399c8e221380f4de0c399c8e221380f4de0c37078740b2784c6604369b0d66a349a0ce1f33194c81d31870c40a33194c81d31870c40a3086c7209268482403
  | 15 => 0x43a190a8441a09022f401fcfc2d3e91cf80e401fcfc2d3e91cf80e3d8a8880d2c05468053d1e4f0773b1d4e823399c8e221380f4de0c399c8e221380f4de0c37078740b2784c6604
  | 16 => 0x448d068131a04c26091a04c2609098241203440cc6612198482408198482408090201002440cc6612198482408198482408090201002198482408090201002090201002040080401
  | 17 => 0x458d86c151b0542a0b450d46a141a850280a448d068131a04c26091a04c2609098241203448d068131a04c26091a04c2609098241203440cc6612198482408198482408090201002
  | 18 => 0x48a407c3d1f0f43c1d47a38783b1e0ec380a469bc741c1d07036091d07036090d8242403469bc741c1d07036091d07036090d82424034618872121c84834081c84834080d0201002
  | 19 => 0x4ba5890472411c54294aa508c4523114500c499f08828220a04e0b49164861421850260448a407c3d1f0f43c1d47a38783b1e0ec380a469bc741c1d07036091d07036090d8242403
  | 20 => 0x4f0f93a3d29078a21d4e0f1363b28070380a4d0e9321c2786c36092786c36092704824034d0e9321c2786c36092786c36092704824034c0e472122686834082686834080d0201002
  | 21 => 0x531214a472e0a8b6295211946452d0a0b20c5111142282c09c860b5010d3e142b84c26044f0f93a3d29078a21d4e0f1363b28070380a4d0e9321c2786c36092786c3609270482403
  | 22 => 0x5bad96a75399c8e2215a2cd643f380f4de0c589c5602037078740b5794532142784c6604572b5586833194c81d55aa9523b31870c40a541914e1c3086c72093086c7209268482403
  | 23 => 0x602fd7c82401fcfc2d5eaf176493e91cf80e5d1f9722c3d8a8880d5c16d42162c05468055bad96a75399c8e2215a2cd643f380f4de0c589c5602037078740b5794532142784c6604
  | 24 => 0x63148a41e62944a21d62140a01c28070380a6193c9e1b2786c3609611389c122704824036193c9e1b2786c3609611389c12270482403609349a1a2686834082686834080d0201002
  | 25 => 0x66970b82a6616cb62965968b42865164b20c64960b0276410c860b6395cae132b84c260463148a41e62944a21d62140a01c28070380a6193c9e1b2786c3609611389c12270482403
  | 26 => 0x6eb70e6726dacce2216d364e03d6c238de0c6b9c0dc1e6b0f0740b6a9409e132784c66046a34ccc65692a8c81d68b40c61c31870c40a6798cc21b3086c7209671389a12268482403
  | 27 => 0x73395007f722f0fc2d71b88fa4770a50f80e701f4f62a6f918880d6f168b015640d468056eb70e6726dacce2216d364e03d6c238de0c6b9c0dc1e6b0f0740b6a9409e132784c6604
  | 28 => 0x7b1cdea727a1c5e621791c1e23d781bcde0c779b95e1e6a8e8740b7713c9e13610cc660476999d86575990c81d7518cc61c74988c40a74184c21b670e47209739349a12268482403
  | 29 => 0x80201fe7f7f1f9fa2d7e1f5f6477d1f1f20e7c1ed702a6f111240d7b9614015638d068057b1cdea727a1c5e621791c1e23d781bcde0c779b95e1e6a8e8740b7713c9e13610cc6604
  | 30 => 0x8a44e247988ada202587b721c4186a42180e859cd62226b8f91a0d779493415618d1100585426106c83ab60c2182b4e083d819be040c80999501e678e9180b7413d3013608cc6604
  | 31 => 0x8f47638868dafe34318cb96304b8ba5a2c108aa01742e70121260f7c1714417648d912068a44e247988ada202587b721c4186a42180e859cd62226b8f91a0d779493415618d11005
  | 32 => 0x8fa211033440cc6612440cc6612198482408440cc6612198482408198482408090201002440cc6612198482408198482408090201002198482408090201002090201002040080401
  | 33 => 0x902251234448d06813448d068131a04c2609448d068131a04c26091a04c26090982412038fa211033440cc6612440cc6612198482408440cc6612198482408198482408090201002
  | 34 => 0x914311a6f469bc741c469bc741c1d0703609469bc741c1d07036091d07036090d824240390c0918624618872124618872121c84834084618872121c84834081c84834080d0201002
  | 35 => 0x92459267c499f08828499f08828220a04e0b91be52459491648614491648614218502604914311a6f469bc741c469bc741c1d0703609469bc741c1d07036091d07036090d8242403
  | 36 => 0x942364e6f4d0e9321c4d0e9321c2786c36094d0e9321c2786c36092786c3609270482403932324a624c0e472124c0e472122686834084c0e472122686834082686834080d0201002
  | 37 => 0x9624e567c5111142285111142282c09c860b9524a52595010d3e145010d3e142b84c2604942364e6f4d0e9321c4d0e9321c2786c36094d0e9321c2786c36092786c3609270482403
  | 38 => 0x994426274589c56020589c5602037078740b983ce5e535794532145794532142784c66049741a5a67541914e1c541914e1c3086c7209541914e1c3086c72093086c7209268482403
  | 39 => 0x9b46a6a815d1f9722c5d1f9722c3d8a8880d9a3f6665d5c16d42165c16d42162c0546805994426274589c56020589c5602037078740b983ce5e535794532145794532142784c6604
  | 40 => 0x9ca69343a9c265321c6193c9e1b2786c36096193c9e1b2786c3609611389c122704824039ba6130394c0e47212609349a1a268683408609349a1a2686834082686834080d0201002
  | 41 => 0x9ea8944449e285422864960b0276410c860b9da8140439d27d3e146395cae132b84c26049ca69343a9c265321c6193c9e1b2786c36096193c9e1b2786c3609611389c12270482403
  | 42 => 0xa1c396271a12c960206b9c0dc1e6b0f0740ba0bc55e51a026d32146a9409e132784c66049fc1150649f2a54e1c6798cc21b3086c72096798cc21b3086c7209671389a12268482403
  | 43 => 0xa3c61747ea32ed722c701f4f62a6f918880da2bed705ba228d42166f168b015640d46805a1c396271a12c960206b9c0dc1e6b0f0740ba0bc55e51a026d32146a9409e132784c6604
  | 44 => 0xa82c69e71a72c25e20779b95e1e6a8e8740ba6abe9851a5a6532147713c9e13610cc6604a52a29264a429d4e1c74184c21b670e4720974184c21b670e47209739349a12268482403
  | 45 => 0xab2eaaa7eaa2e6662c7c1ed702a6f111240da9ae2a45ba8a8652167b9614015638d06805a82c69e71a72c25e20779b95e1e6a8e8740ba6abe9851a5a6532147713c9e13610cc6604
  | 46 => 0xb044abe78af2d66224859cd62226b8f91a0daebd69e55ae2764e16779493415618d11005adc22b46bacab25a2080999501e678e9180bac3b29251aba664a147413d3013608cc6604
  | 47 => 0xb2c72c885b1afa6a308aa01742e70121260fb13feaa5fb0a9656187c1714417648d91206b044abe78af2d66224859cd62226b8f91a0daebd69e55ae2764e16779493415618d11005
  | 48 => 0xb430d864f6193c9e1b6193c9e1b2786c3609b3b09844e611389c12611389c12270482403b3305824d609349a1a609349a1a268683408609349a1a2686834082686834080d0201002
  | 49 => 0xb5b25925864960b027b532190436410c860bb4b1d8e576395cae136395cae132b84c2604b430d864f6193c9e1b6193c9e1b2786c3609b3b09844e611389c12611389c12270482403
  | 50 => 0xb8435ae706b9c0dc1eb7b61ac3c6b0f0740bb73c1aa506a9409e136a9409e132784c6604b6c0d9e636798cc21b6798cc21b3086c7209b63a59c4e671389a12671389a12268482403
  | 51 => 0xba45dc07d701f4f62ab9b85be466f918880db93e9bc5a6f168b015b8b299035640d46805b8435ae706b9c0dc1eb7b61ac3c6b0f0740bb73c1aa506a9409e136a9409e132784c6604
  | 52 => 0xbcb5eb870779b95e1ebc35a803c6a8e8740bbbb5696507713c9e137713c9e13610cc6604bb33eae6374184c21b74184c21b670e47209bab399c4e739349a12739349a12268482403
  | 53 => 0xbeb82c27d7c1ed702abe37e88466f111240dbdb7aa25a7b9614015bd3227435638d06805bcb5eb870779b95e1ebc35a803c6a8e8740bbbb5696507713c9e137713c9e13610cc6604
  | 54 => 0xc2446bc76859cd6222c1b6e84406b8f91a0dc13d29c54779493415c0b167035618d11005c041eb26980999501ebfb4a7c3c678e9180bbf3ae90507413d30137413d3013608cc6604
  | 55 => 0xc446ec6838aa01742ec3b928c4a70121260fc33faa85e7c1714417c2b327837648d91206c2446bc76859cd6222c1b6e84406b8f91a0dc13d29c54779493415c0b167035618d11005
  | 56 => 0xc7bbdde6ec0abd5e1ec7355aa3a6a8e8740bc6bb9dc4f7713c9e13c63098433610cc6604c5ba1d06174184c21bc53399c39670e47209c4b9dce4d739349a12739349a12268482403
  | 57 => 0xc9be1f07bc2ae1702ac9379bc44b8a49240dc8bddee58bd2814015c831d8e34638d06805c7bbdde6ec0abd5e1ec7355aa3a6a8e8740bc6bb9dc4f7713c9e13c63098433610cc6604
  | 58 => 0xccc3e1673c1ad16222cc369ae3eb7a3d1a0dcbbc9de52bc2713415c73118634618d11005cb4160266bfaad501ecab459e3a678e9180bca3a9d04f7413d3013c53098233608cc6604
  | 59 => 0xce4662a80c3af5742ecdb8dc048b9a55260fcd3f1f05cbe2914417c932d9236b52291206ccc3e1673c1ad16222cc369ae3eb7a3d1a0dcbbc9de52bc2713415c73118634618d11005
  | 60 => 0xd042eba73c12c66022cbb5e823eb72351a0dcfbbe9a52bba693415c6b0d8634b3a211005cf406b066bf2a1501eca33d9e3ab6231180bceba1d04fbaa613013c4b058233608cc6604
  | 61 => 0xd1456c480c32ea682ecd3828a48b924e460fd0be2a65cbda8a5417c8b267636b4a251206d042eba73c12c66022cbb5e823eb72351a0dcfbbe9a52bba693415c6b0d8634b3a211005
  | 62 => 0xd2452c07ac22de6426ccb768642b8246440fd03daa056bca7a5017c7b1a7236b42263e06d1c2ab66dc02ba5c22cb3527e3eb6a36420dcf3b69452bb26a4c15c5b0e6e34b32211005
  | 63 => 0xd2c7aca87c43026c32ce39a8e4cba25e4811d1402ac60bea9a5819c9b367a38b5a2e4007d2452c07ac22de6426ccb768642b8246440fd03daa056bca7a5017c7b1a7236b42263e06
  | _ => 0

def stateIndex (u : ℕ) : ℕ := (stateIndexPack (u / 64) >>> (9*(u % 64))) % 512

def packedClassPack : ℕ → ℕ
  | 0 => 0x4cc80000000000003cf00000000000002f7000000000000024180000000000001ab800000000000013200000000000000d200000000000000888000000000000052800000000000002d000000000000001500000000000000078000000000000001800000000000000000000000031000000000000002a4000000000000024000000000000001e400000000000001900000000000000144000000000000010000000000000000c40000000000000090000000000000006400000000000000400000000000000024000000000000001000000000000000040000000001c000000000000001a00000000000000180000000000000016000000000000001400000000000000120000000000000010000000000000000e000000000000000c000000000000000a0000000000000008000000000000000600000000000000040000000000000002000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1d6321280000000010c991d00000000009231bd00000000004b21c7800000000024072780000000000fddbe00000000000646fe000000000002296c8000000000009e2c80000000000022bf000000000000051f0000000000000061800000000000000180000000000000000000012a35e40000000000b8dfb800000000006dfc3800000000003e4edc000000000021465c00000000001086900000000000077d900000000000030414000000000001091400000000000048a80000000000000e28000000000000018c000000000000000c0000000000000000000000bd6ba000000000007f7940000000000052eb40000000000033cde000000000001ed3e00000000000114780000000000008fb800000000000043c20000000000001c02000000000000099c000000000000027c00000000000000660000000000000006000000000000000000000007881000000000000580e0000000000003ea60000000000002b2f0000000000001ca700000000000012240000000000000ad400000000000005fd00000000000002fd000000000000014a0000000000000072000000000000001b00000000000000030000000000000000
  | 2 => 0x2f99780000000000200b00000000000014d9c000000000000d0818000000000007c21800000000000459c00000000000024340000000000001113800000000000070f800000000000026c00000000000000a000000000000000198000000000000001800000000000000000000001c86c0000000000014be8000000000000eac8000000000000a0b400000000000069b4000000000000423000000000000026f0000000000000151c0000000000000a3c000000000000043800000000000001580000000000000044000000000000000400000000000000000000000f6b2000000000000b49400000000000080bc00000000000058f20000000000003b2e000000000000259800000000000016880000000000000c86000000000000064a00000000000002bc00000000000000f4000000000000003a0000000000000006000000000000000000000000ab8000000000000089500000000000006c0000000000000053300000000000003e800000000000002d90000000000000200000000000000015700000000000000d8000000000000007d0000000000000040000000000000001b00000000000000080000000000000001
  | 3 => 0x1ce6789800000000107b0d600000000008f38a2000000000049696f800000000023162580000000000f62880000000000060d30000000000002112b800000000000956d8000000000002036000000000000049a00000000000000538000000000000001800000000000000000000119d90c0000000000add508000000000066c7a8000000000039ca2400000000001e92f400000000000f00f0000000000006b1b0000000000002a32c000000000000e09c0000000000003a980000000000000a7800000000000000f4000000000000000400000000000000000000093fa4e00000000005ba900000000000036794000000000001ed1d60000000000106e660000000000082470000000000003adf0000000000001799e00000000000080ce00000000000022f000000000000006b000000000000000b60000000000000006000000000000000000000059b07000000000003c1160000000000026d9600000000000181a5000000000000e3850000000000007e2400000000000040a40000000000001de30000000000000c0300000000000003f200000000000000f2000000000000002100000000000000010000000000000000
  | 4 => 0x30aa78000000000020cfa0000000000015634000000000000d64e8000000000007fe180000000000047e8000000000000258400000000000011c2800000000000075f800000000000028a00000000000000a8000000000000001a800000000000000180000000000000000000000219780000000000018c180000000000011ca0000000000000c6840000000000008598000000000000561000000000000034800000000000001ddc0000000000000f78000000000000070800000000000002a000000000000000b4000000000000001800000000000000000005aa0c46e000000002f996ca00000000017a3b070000000000afc0d760000000004b5cbe60000000001d454f00000000000a0919000000000002ed20e00000000000af96e000000000001e31000000000000033c000000000000002760000000000000006000000000000000000003770e970000000001f7f51e0000000001107e4e00000000008ae995000000000041f14500000000001caa5400000000000b25b4000000000003bf9300000000000108d3000000000000370a000000000000075a000000000000007100000000000000010000000000000000
  | 5 => 0x1d51b6280000000010bce58000000000091a43300000000004ac38c800000000023cbcf80000000000fbacc0000000000063412000000000002203c8000000000009a54800000000000217400000000000004d10000000000000058800000000000000180000000000000000000011df8140000000000b092a000000000006889a000000000003ade8400000000001f340400000000000f58e0000000000006dde0000000000002b714000000000000e8540000000000003d000000000000000b000000000000000104000000000000000400000000000000000000096abea00000000005d7548000000000037a1bc00000000001f88e2000000000010d9be0000000000085f80000000000003cbe8000000000001874a000000000000863200000000000024a8000000000000071400000000000000c2000000000000000600000000000000000000005b27d000000000003d1d800000000000279300000000000018961000000000000e871000000000000811800000000000042480000000000001eb50000000000000c5d000000000000041000000000000000f8000000000000002100000000000000010000000000000000
  | 6 => 0x3188480000000000217080000000000015d4b000000000000db24000000000000830b80000000000049e000000000000026aa000000000000126000000000000007aa80000000000002a800000000000000b1000000000000001c00000000000000018000000000000000000000025840000000000001be440000000000014400000000000000e4c40000000000009c40000000000000668400000000000040000000000000002584000000000000144000000000000009c400000000000004000000000000000144000000000000004000000000000000040005bb7d3b20000000030371ad80000000017f86564000000000b26e5520000000004c9f00e0000000001dcfb200000000000a3e13800000000002fe94a00000000000b446a000000000001f21800000000000035ac0000000000000292000000000000000600000000000000000000381c3410000000001fe8204000000000114547c00000000008d0ba10000000000430e3900000000001d33d000000000000b61c0000000000003d699000000000001103900000000000038e400000000000007ac000000000000007900000000000000010000000000000000
  | 7 => 0x29915000000000001ba680000000000011bcf000000000000ae58800000000000659a00000000000037740000000000001bd60000000000000c8280000000000004d3000000000000017c00000000000000510000000000000008800000000000000000000000000000000000012c96740000000000ba68f800000000006eef9800000000003eddb000000000002194bc000000000010adf00000000000078f100000000000030a880000000000010ac400000000000048c80000000000000e080000000000000180000000000000000c0000000000000000000000b0b6600000000000762e4000000000004c4d4000000000002f3d2000000000001bcba000000000000f5b80000000000007d58000000000000399600000000000016ee000000000000076c00000000000001bc000000000000003a000000000000000200000000000000000000005c38d000000000003de2200000000000281c80000000000018f2e000000000000ec31000000000000836400000000000043980000000000001f640000000000000cad000000000000042e0000000000000100000000000000002200000000000000010000000000000000
  | 8 => 0x20ce4e0000000000141ae200000000000bcc1a000000000006927c0000000000036ffc000000000001a994000000000000ba44000000000000477a00000000000016e2000000000000059e00000000000000e600000000000000100000000000000000000000000000000000000e6fb9ac00000000083af150000000000477f3a000000000024a140c000000000117ecac00000000007aa0c00000000000302b600000000000106b9c0000000000049f4c000000000000fdd00000000000002400000000000000028c000000000000000c00000000000000000000089eed8000000000054e9ba000000000032183200000000001c175600000000000ed01e0000000000073d34000000000003366400000000000141ac00000000000069ec0000000000001b3600000000000004be000000000000006a000000000000000200000000000000000000047213e00000000002be6a7000000000019fa6700000000000e9ee1000000000007be73000000000003ce2e000000000001b35e000000000000abe200000000000039540000000000000f0100000000000002b1000000000000003f00000000000000010000000000000000
  | 9 => 0x2858db0000000000192bbc00000000000f15dc0000000000089f01000000000004a71b00000000000257400000000000011410000000000000718100000000000028130000000000000b6c000000000000025c0000000000000049000000000000000300000000000000000000b30eb42c000000005deae6d8000000002e90da40000000001597e69c00000000093c1dac0000000003930f9000000000013844a000000000005a7564000000000014ffcc0000000000038ec80000000000005f60000000000000046c000000000000000c000000000000000000006bc992a0000000003d1431c00000000020ec94000000000010b8aa400000000007e6a02000000000036a0f8000000000015149000000000000703b8000000000001e84a00000000000063440000000000000cd000000000000000bc000000000000000200000000000000000000372d1b30000000001f5407600000000010ed492000000000089ef81000000000041663d00000000001c622400000000000b035c000000000003b107000000000001039700000000000035920000000000000716000000000000006d00000000000000010000000000000000
  | 10 => 0x2383a5800000000015eb3a00000000000cf8690000000000074ccc000000000003dde6800000000001e684000000000000d97e00000000000055ea0000000000001caf8000000000000786000000000000015b00000000000000200000000000000000800000000000000000000f908e040000000008edfc780000000004e273fc00000000028665fc000000000138201000000000008a9c3000000000003767f8000000000013543c0000000000059e2c0000000000014348000000000000316400000000000003fc0000000000000018000000000000000000000951c5e00000000005c6b64000000000036f71000000000001f1ff40000000000109c860000000000083e08000000000003bb100000000000017fb0000000000000833e00000000000023bc00000000000006e000000000000000bc00000000000000060000000000000000000004c7bee00000000002f7fd300000000001c509d00000000001013d90000000000089bd100000000000449d6000000000001f35a000000000000c9da0000000000004598000000000000132500000000000003bb000000000000006700000000000000030000000000000000
  | 11 => 0x1bfcc5c8000000000fe907e000000000089be220000000000464696000000000021642480000000000e87dc000000000005a858000000000001e7b400000000000086d08000000000001c1200000000000003c2000000000000003a000000000000000080000000000000000000c15cebac00000000661470d00000000033007b240000000017de6ea4000000000a52c82000000000040d62e0000000000168734800000000006af22c000000000019aa840000000000049130000000000000847c000000000000071400000000000000180000000000000000000074a981c0000000004290816000000000242d122000000000128e3e600000000008e00c200000000003e514c00000000001888a400000000000863400000000000025ed000000000000082da00000000000012ae00000000000001520000000000000006000000000000000000003b91ad1000000000220b8420000000001289d6e0000000000987d950000000000492327000000000020343c00000000000cbb44000000000004603f0000000000013ecd00000000000045660000000000000a0a00000000000000b900000000000000030000000000000000
  | 12 => 0x34b870000000000023c5b00000000000177e4000000000000ed828000000000008f4300000000000051a20000000000002b5000000000000014f580000000000008f7000000000000033900000000000000e400000000000000288000000000000003000000000000000000096dba4cb400000004951d9fd00000000217ab773c00000000e32110c00000000058118430000000001e97c8c00000000009410ab800000000025707d80000000000770a3c000000000010d5100000000000016be40000000000000cf0000000000000001800000000000000000005b7a35020000000030104f0c0000000017e1087c000000000b198d4e0000000004c2ca0e0000000001d971680000000000a24bc800000000002f4a2a00000000000b103a000000000001e4e400000000000033740000000000000266000000000000000600000000000000000002e89811400000000187c2da1000000000c2f2e270000000005acac38000000000270815d0000000000f3458a000000000053af5e0000000000187e33000000000005c382000000000000fe9f0000000000001b51000000000000014a00000000000000030000000000000000
  | 13 => 0x1c56cb88000000001020c9100000000008bd01c000000000047723a80000000002203b480000000000ed6c6000000000005cbe4000000000001f5e18000000000008b9c8000000000001d5b000000000000040000000000000000408000000000000000800000000000000000000ee05a74000000000880a5080000000004a1544800000000026174640000000001245cfc000000000080c670000000000032efb000000000001185cc000000000004fe840000000000011718000000000000289800000000000002f4000000000000000c0000000000000000000009054220000000000592afc000000000034d32000000000001dc4da00000000000fca92000000000007c6080000000000037b3000000000000160ae00000000000075f20000000000001ef40000000000000590000000000000008200000000000000020000000000000000000004cabeb00000000002f9d6e00000000001c61d80000000000101d21000000000008a04b0000000000044ba4000000000001f3d8000000000000c9d30000000000004573000000000000130a00000000000003b0000000000000006500000000000000030000000000000000
  | 14 => 0x2b2ad000000000001ccd700000000000128b3000000000000b70c0000000000006b3a0000000000003ae60000000000001dce0000000000000d89000000000000054b00000000000001a9000000000000005d000000000000000a000000000000000000000000000000000000013394980000000000bf0b6c000000000071e564000000000040acb8000000000022a0c40000000000113ef8000000000007d7080000000000032a5c00000000000116c00000000000004c540000000000000ebc0000000000000190000000000000000c0000000000000000000000d7dbc0000000000092b8400000000000608d0000000000003d2660000000000024fcc0000000000015258000000000000b44000000000000057aa00000000000025bc0000000000000dac00000000000003d000000000000000ae000000000000000c00000000000000000002e68732500000000186b42da000000000c2737120000000005a9546900000000026f54af0000000000f2fb8c000000000053ae8c0000000000188a3b000000000005cb7900000000000101ae0000000000001c06000000000000015d00000000000000030000000000000000
  | 15 => 0x21b806800000000014b67380000000000c2ffb800000000006cfe880000000000393d5000000000001bd2f000000000000c4230000000000004bef000000000000189d8000000000000628800000000000010480000000000000138000000000000000000000000000000000000eb8546c000000000867962400000000049240a8000000000258cd4400000000011fac0c00000000007e6768000000000031d6d000000000001111f8000000000004d5ac0000000000010b9c000000000000265800000000000002bc000000000000000c0000000000000000000008e37d2000000000057c57c000000000033ef3800000000001d39e400000000000f7a520000000000079ab800000000000365c0000000000001573800000000000072620000000000001de40000000000000558000000000000007c00000000000000020000000000000000000004832f400000000002c9a8500000000001a6c1900000000000ee375000000000007e57f000000000003e2da000000000001bd52000000000000b0180000000000003ace0000000000000f6300000000000002bf000000000000003f00000000000000010000000000000000
  | 16 => 0x26148d800000000017a29600000000000e1422000000000007fc84800000000004455d8000000000021fc0000000000000f6c000000000000063688000000000002219800000000000094e00000000000001ca0000000000000030800000000000000180000000000000000000b5ede1d8000000005f8b33d4000000002f710fbc000000001609a604000000000971ca240000000003aa37480000000001412f1800000000005d6ad8000000000015cd20000000000003b86c00000000000064c400000000000004bc000000000000000c000000000000000000006e5014e0000000003ea137000000000021d61a4000000000113b226000000000082b1aa000000000038b530000000000015fed80000000000075e5600000000000205a60000000000006aa00000000000000e0c00000000000000d60000000000000002000000000000000000003801b2e0000000001fd675e0000000001139ec500000000008c9bbd000000000042ccdb00000000001d100c00000000000b4fc2000000000003ce810000000000010d1c00000000000037f2000000000000077b000000000000007500000000000000010000000000000000
  | 17 => 0x1dc79258000000001104e7180000000009445c700000000004c392f0000000000248e39800000000010183b0000000000065ca60000000000022fa88000000000009f3580000000000022a28000000000000501000000000000005c0000000000000001800000000000000000000f0cd09000000000089baf200000000004b10c6400000000026a1c8c000000000128d354000000000082e480000000000033d6e8000000000011db5400000000000518680000000000011ce0000000000000295c00000000000002fc000000000000000c000000000000000000000913d52000000000059cbdc0000000000353eb800000000001e0a3400000000000ff552000000000007def800000000000388c0000000000001676800000000000078e2000000000000200400000000000005d8000000000000008c0000000000000002000000000000000000003f36efe000000000244edeb00000000013e30a20000000000a4bc1100000000004fb07e000000000023773e00000000000e36cc000000000004f99000000000000173a600000000000053f50000000000000ce6000000000000010b00000000000000060000000000000000
  | 18 => 0x17436128800000000c3d3bd880000000061714160000000002d60b7900000000013818978000000000798ec1000000000029ce9400000000000c3b6f800000000002e0828000000000007efb8000000000000d9a00000000000000a4000000000000000180000000000000000000bc3a372800000000631e1bf400000000315f120c00000000170512f80000000009e8e8c40000000003dddfa800000000015536380000000000641ffc000000000017a450000000000004196c00000000000071740000000000000570000000000000000c00000000000000000000720c6d000000000040ee0ae00000000023318da00000000011fe0640000000000891e8e00000000003bd96c00000000001763f4000000000007ea1e00000000000233b400000000000076720000000000001016000000000000010000000000000000020000000000000000000310686280000000019e8aa0b000000000cf5ed1000000000061305930000000002a1b312000000000108fe8e00000000005c4e7800000000001b79320000000000069eac0000000000012f25000000000000229800000000000001dd00000000000000060000000000000000
  | 19 => 0x2716fa8000000000184ea200000000000e829b00000000000840738000000000046cff800000000002356800000000000101a2000000000000684d80000000000023fc80000000000009e200000000000001e90000000000000033800000000000000180000000000000000000001a551c000000000011dd2800000000000bbaa800000000000768a400000000000477840000000000028b300000000000015930000000000000a6cc000000000000472c000000000000197800000000000006f8000000000000013400000000000000140000000000000000000000eb24800000000000a0e9c000000000006abc000000000000443d60000000000029bf80000000000018348000000000000d20000000000000068820000000000002e6800000000000011940000000000000540000000000000010e0000000000000018000000000000000000262ec033b00000001293251d70000000087da6ffd0000000039ad1aaa000000001665ba180000000007cb5e5600000000025cea8a000000000099611300000000001e962100000000000458390000000000005e7b000000000000036000000000000000060000000000000000
  | 20 => 0x2173f4000000000014874000000000000c1040000000000006bb590000000000038718000000000001b5b8000000000000c01000000000000049e900000000000017bc00000000000005d800000000000000f000000000000000110000000000000000000000000000000000000ee1c94c0000000008811b740000000004a14ec80000000002613e400000000001241f4c00000000008093e8000000000032cd900000000000117254000000000004f54c00000000000113ac00000000000027b800000000000002d8000000000000000c0000000000000000000008d7ab60000000000573f6c00000000003392ec00000000001cfc8800000000000f533a0000000000078318000000000003586800000000000150540000000000006f3e0000000000001cb400000000000005040000000000000070000000000000000200000000000000000000048f7e200000000002d1c1d00000000001abe2b00000000000f151600000000000801db000000000003f1f2000000000001c4a6000000000000b33d0000000000003bf00000000000000fb300000000000002cd000000000000004000000000000000010000000000000000
  | 21 => 0x267f8c800000000017e98700000000000e4177000000000008183b800000000004556b8000000000022872000000000000fb12000000000000655280000000000022d2800000000000098500000000000001d50000000000000031800000000000000180000000000000000000b762c1cc00000000605df0d0000000002fe251d8000000001642f9bc00000000098cc64c0000000003b5d460000000000145a5b000000000005ee5e4000000000016344c000000000003cdb000000000000067a800000000000004ec000000000000000c000000000000000000006e51fe00000000003ea0a8000000000021d492600000000011397980000000000829b7e000000000038a570000000000015f51c0000000000075924000000000002035400000000000069d00000000000000dda00000000000000d0000000000000000200000000000000000000387c7db0000000002021bb200000000011661a600000000008e25ad0000000000439afd00000000001d73cc00000000000b7b74000000000003df4b000000000001127f000000000000394600000000000007b2000000000000007900000000000000010000000000000000
  | 22 => 0x1dcc2ba800000000110780f0000000000945bc700000000004c43d180000000002492bf80000000001019ca0000000000065cfa0000000000022f9a8000000000009f1c800000000000229500000000000004fd000000000000005b8000000000000001800000000000000000000f2e34e00000000008b04cb80000000004bd4064000000000270fb5800000000012c7734000000000084ae90000000000034a3a80000000000122c28000000000005335800000000000123e80000000000002a9c0000000000000318000000000000000c00000000000000000000090447e0000000000591fd0000000000034cb6400000000001dbfb200000000000fc74a000000000007c4100000000000037a18000000000001602200000000000075b60000000000001ee0000000000000058c00000000000000820000000000000002000000000000000000003fe789d00000000024bc2510000000001423e490000000000a70613000000000050e824000000000024112200000000000e7bfa00000000000515120000000000017ce700000000000056670000000000000d57000000000000011500000000000000060000000000000000
  | 23 => 0x174d7776000000000c42c4b8000000000619f3428000000002d77038800000000138b82a800000000079cf50000000000029e5a100000000000c427d800000000002e2510000000000007f600000000000000dad80000000000000a6800000000000000180000000000000000000bd8533540000000063d9d95c0000000031c466f8000000001738a16c000000000a01553c0000000003e878380000000001595390000000000065825000000000001806a40000000000042e44000000000000746800000000000005a4000000000000000c0000000000000000000071fc1e600000000040e3384000000000232aa1400000000011f9c96000000000088f73a00000000003bc4180000000000175958000000000007e56a00000000000231ee00000000000075ec0000000000000ffc00000000000000fe00000000000000020000000000000000000316a71fe000000001a2176cc000000000d14a928000000000622b49e0000000002a927c600000000010c3e1800000000005d930000000000001be706000000000006bd5e00000000000135b4000000000000238800000000000001ee00000000000000060000000000000000
  | 24 => 0x250ccb800000000016ee6a00000000000d9ce5000000000007b081800000000004170a8000000000020508000000000000e85e0000000000005c538000000000001f01800000000000082a000000000000017700000000000000218000000000000000800000000000000000000018f5e8000000000010dac800000000000b0160000000000006e7bc000000000004210800000000000253b0000000000001378000000000000093c40000000000003d680000000000001518000000000000056000000000000000cc00000000000000080000000000000000000009f1a520000000000630fc000000000003b38ec000000000021bcb800000000001221ae00000000000912000000000000042528000000000001af28000000000000956a0000000000002940000000000000080400000000000000d80000000000000006000000000000000000266db5bfa000000012b403b390000000088ddc9a0000000003a249ce3000000001698760e0000000007ded66a0000000002637ec000000000009b43dc00000000001f05320000000000046b070000000000006080000000000000037900000000000000060000000000000000
  | 25 => 0x21ae9b000000000014adcb00000000000c289d000000000006ca0b0000000000038f76000000000001ba26000000000000c2320000000000004ad0000000000000180d00000000000005ed00000000000000f300000000000000110000000000000000000000000000000000000ed4cfcc0000000008792a2c00000000049ca75800000000025ea7ac000000000122c58c00000000007fed3800000000003284f000000000001156a8000000000004ec8c0000000000011194000000000000276800000000000002d4000000000000000c0000000000000000000008b835e000000000055f4bc000000000032c1ec00000000001c7e7600000000000f0b6a0000000000075d08000000000003460800000000000148820000000000006c760000000000001bf400000000000004e4000000000000006e0000000000000002000000000000000000000476c3f00000000002c13e600000000001a13e200000000000eabe6000000000007c425000000000003cffc000000000001b36c000000000000ab6400000000000038db0000000000000eba0000000000000296000000000000003a00000000000000010000000000000000
  | 26 => 0x1b582b18000000000f833e9800000000085f8480000000000442592000000000020429280000000000df90b0000000000056840000000000001ce498000000000007e4f80000000000019da8000000000000360000000000000003300000000000000008000000000000000000000fe235000000000009b458800000000005ac630000000000032570400000000001a2da000000000000c90f000000000000571e00000000000020f4c000000000000a530000000000000271800000000000005d00000000000000054000000000000000000000000000000000000706f75c0000000003fef52e000000000229aefe00000000011a955400000000008651a600000000003a79ac000000000016c71c000000000007ac6e0000000000021f4800000000000071320000000000000f3200000000000000f0000000000000000200000000000000000000041e96400000000002866ec000000000017b64800000000000d365f000000000006e95800000000000357c000000000000176800000000000008fa30000000000002dec0000000000000b3c00000000000001c8000000000000001f00000000000000000000000000000000
  | 27 => 0x24525a000000000016733e80000000000d4e8a80000000000780e0000000000003fba7800000000001f659000000000000e12d00000000000059358000000000001ddf00000000000007d9800000000000016980000000000000210000000000000000800000000000000000000fecaea8000000000926ed8800000000050433a00000000002996d18000000000142393800000000008f9550000000000039a24000000000001435e0000000000005e98800000000000156f800000000000034e00000000000000448000000000000001800000000000000000005a28860e000000002f4eec000000000017777c88000000000ae3270c0000000004a8a1060000000001cde56000000000009db9a000000000002db8dc00000000000a9f6e000000000001cd600000000000003088000000000000024c00000000000000060000000000000000000035be81c0000000001e726d40000000001068407000000000085469b00000000003ef1b700000000001b2f5800000000000a7b760000000000037c09000000000000f23e000000000000312c0000000000000659000000000000005f00000000000000010000000000000000
  | 28 => 0x184fea7a800000000cd6c5c080000000066abb8f800000000301164000000000014cc3d6000000000082ad0900000000002d6c4f00000000000d7b648000000000033c8b800000000000937b80000000000010bc80000000000000e70000000000000003000000000000000000000e886b5400000000084a3bf0000000000481091800000000024f36e400000000011aa8fc00000000007bfb40000000000030c790000000000010a9f4000000000004b4640000000000010370000000000000250800000000000002a4000000000000000c00000000000000000000763d8aa000000000438902800000000024bf80c00000000012e03a6000000000090b2fe00000000003fa1a00000000000191d480000000000089d0e00000000000271b200000000000087a8000000000000138400000000000001660000000000000006000000000000000000003c73278000000000229677600000000012dbe6d00000000009b5eab00000000004aa83d000000000020f28c00000000000d0fc2000000000004814700000000000149a6000000000000482a0000000000000a8300000000000000c300000000000000030000000000000000
  | 29 => 0x1b102438000000000f577b700000000008461ab00000000004345eb00000000001fcf7280000000000dc27e0000000000055102000000000001c5b00000000000007bb1800000000000194100000000000003490000000000000031000000000000000080000000000000000000ba4f0dbc000000006204b33c0000000030c56c480000000016b5dbf40000000009c2ceec0000000003cd0e1800000000014e8dd0000000000061d740000000000016ff9c000000000003f6c40000000000006cf8000000000000053c000000000000000c000000000000000000006f1ab2e0000000003f1ef7e00000000022210200000000001165a000000000000841d3a00000000003969fc00000000001650e00000000000077f5e00000000000210f60000000000006db20000000000000ea000000000000000e40000000000000002000000000000000000003874d93000000000201d9c8000000000116415600000000008e180300000000004396ad00000000001d737800000000000b7c54000000000003e02b0000000000011307000000000000398000000000000007c2000000000000007b00000000000000010000000000000000
  | 30 => 0x19fac0af000000000dcb0dc50000000006eff8d2000000000345b9f480000000016dc571000000000091422600000000003336dc00000000000f7c39800000000003cfe3000000000000b40f000000000000159600000000000001468000000000000005000000000000000000095e7a4334000000048ccb764000000002135b5d1400000000e106b77800000000571dc010000000001e3310e000000000091c004800000000024b58200000000000740e5c00000000001046600000000000015bec0000000000000c48000000000000001800000000000000000005a31abfc000000002f544c6000000000177a836e000000000ae4c55a0000000004a970d20000000001ce456000000000009de14c00000000002dc6c600000000000aa320000000000001cde000000000000030720000000000000242000000000000000600000000000000000002daeb37b0000000017fefaa3000000000beaed4c0000000005898c3c00000000025fa5cb0000000000ebd98e000000000050c1a00000000000177df50000000000057ba3000000000000ef8d000000000000195c000000000000013200000000000000030000000000000000
  | 31 => 0x1840f5b3000000000cce125c000000000665e6d00000000002fe8c9000000000014b849b0000000000821c8800000000002d314800000000000d6640000000000003362b00000000000091f4000000000000107800000000000000e0000000000000000300000000000000000000c45e1a100000000067c468800000000033e6df40000000001851f6e4000000000a8888a80000000004242cc000000000017108e000000000006db72c00000000001a63c0000000000004b50000000000000088e000000000000007540000000000000018000000000000000000063a5a2840000000034b76990000000001a66f654000000000c6404280000000005605e0c00000000021e57700000000000bd4cf8000000000038794400000000000da4c400000000000272a000000000000047bc00000000000003e0000000000000000c000000000000000000003c6e44400000000022934a100000000012d9eb700000000009b4bd900000000004a9dbd000000000020ed2200000000000d0d3e0000000000048044000000000001495200000000000048170000000000000a8100000000000000c300000000000000030000000000000000
  | 32 => 0x1366e23dd8000000097263a5a800000004528cadf800000001d645e2a800000000b6d30780000000003fb290500000000013551b300000000004e812600000000000fa9848000000000023911800000000000302880000000000001b3800000000000000300000000000000000000bacd7f5400000000624ae6500000000030ea5ac80000000016c811b80000000009cb193c0000000003d0776000000000014fc83000000000006234e80000000000171424000000000003f8f00000000000006c980000000000000518000000000000000c00000000000000000005e7ecc3a0000000031c4655c0000000018cb0604000000000b8fbdaa0000000004fa443e0000000001f139880000000000ab61d800000000003246ae00000000000bdd020000000000020dd400000000000038ac00000000000002b200000000000000060000000000000000002839f5f76000000013a5e4bb90000000090614fc2000000003da35d32000000001818afaa00000000087462a2000000000296eeec0000000000aa57ff00000000002296b60000000000050b3f00000000000072860000000000000478000000000000000a0000000000000000
  | 33 => 0xfa3e67c0f0000000707f35c8d00000002f3454d1a000000012404e5a580000000664ca919000000001fbef58600000000087576840000000001d9bc5c80000000004f8a6b00000000000932a70000000000009b2600000000000004038000000000000005000000000000000000097855b2cc000000049a3c35180000000219f3990400000000e40c0570000000005863a220000000001eaeee500000000009454ac8000000000256ece00000000000769d24000000000010ab88000000000001645c0000000000000c7000000000000000180000000000000000004c83efabc00000002536ed3a60000000110185f6c000000007376a3a2000000002cce97dc000000000f93bb5c0000000004b709480000000001314e5000000000003ca52c0000000000088eda000000000000b8040000000000000676000000000000000c00000000000000000002dd419ad0000000018140528000000000bf62e0200000000058f366e0000000002624c1f0000000000ecfb200000000000512f8c000000000017a19600000000000584d1000000000000f1280000000000001976000000000000012e00000000000000030000000000000000
  | 34 => 0x17807ef6800000000c6103f200000000062b1ad10000000002e0ab9680000000013d61df80000000007bfcd800000000002ad17600000000000c9a1e800000000002fd9880000000000085f20000000000000ebb00000000000000ba8000000000000001800000000000000000000e40e74400000000081d53e0000000000465ec7000000000023f97040000000001122564000000000077a66000000000002ec20000000000000fd1d400000000000466a4000000000000ecc00000000000002030000000000000020400000000000000040000000000000000000078d87d6000000000452422800000000025b27580000000001368c5a0000000000953676000000000041d8a000000000001a1a6000000000000900ea000000000002930600000000000090680000000000001518000000000000018a000000000000000600000000000000000000052df16000000000033c94200000000001f1838000000000011cec5000000000009a236000000000004dc1c0000000000023ee0000000000000ed270000000000005406000000000000180600000000000004f8000000000000009900000000000000060000000000000000
  | 35 => 0x1c39b3c000000000100d5b580000000008b07c4800000000046f67a800000000021bb1b80000000000eaed3000000000005b7a1000000000001eca700000000000087fd0000000000001c3680000000000003bf8000000000000039800000000000000080000000000000000000011160b00000000000a81598000000000063016000000000003767d000000000001d232000000000000e2fb000000000000643000000000000026de8000000000000ca1000000000000032a8000000000000086000000000000000a000000000000000000000000000000000000077ce82a000000000447bdbc000000000254bfd4000000000132d230000000000093289e000000000040c99800000000001999f8000000000008ca640000000000027f120000000000008a8400000000000013dc00000000000001680000000000000006000000000000000000000534c9200000000003411e000000000001f46a0000000000011eb21000000000009b29e000000000004e4f80000000000024340000000000000ef1100000000000054ba00000000000018380000000000000500000000000000009900000000000000060000000000000000
  | 36 => 0x18c7f7c6000000000d1b6f05800000000690269b000000000314574d8000000001560231000000000086bffb00000000002f08e600000000000e092800000000000364c00000000000009c1e80000000000011ed00000000000000f88000000000000003000000000000000000000ee287d400000000088126a00000000004a10c18000000000260e824000000000123d2fc0000000000805c20000000000032aa900000000000115f84000000000004ece400000000000110c0000000000000270800000000000002c4000000000000000c00000000000000000005c53c85200000000308b5e9e0000000018233500000000000b3b0db20000000004d28d9e0000000001e037ec0000000000a4e480000000000030259000000000000b4b7a000000000001f102000000000000352000000000000002860000000000000006000000000000000000003834dd30000000001ff5bde000000000114c39a00000000008d3e4a000000000043217d00000000001d38bc00000000000b616c000000000003d5340000000000010f370000000000003872000000000000078e000000000000007600000000000000010000000000000000
  | 37 => 0x134c1781c80000000965342ff0000000044c842c5800000001d3c0d07800000000b5e3df20000000003f6776a0000000001342f7300000000004e59ce80000000000fae318000000000023d15000000000000310e80000000000001c5800000000000000300000000000000000000bcb1e2e000000000636224e8000000003183e24c000000001717daa80000000009f1d4540000000003e1c090000000000156b818000000000064a160000000000017c7b8000000000004209800000000000072540000000000000578000000000000000c00000000000000000005ea272060000000031dab7c60000000018d86438000000000b97550e0000000004fe4ef60000000001f3362c0000000000ac43c00000000000329e8000000000000bf97600000000000214ea00000000000039d800000000000002ca000000000000000600000000000000000000399671c00000000020cfa0d00000000011cceb5000000000091c294000000000045843f00000000001e63d200000000000be67a000000000004096700000000000120760000000000003ce30000000000000853000000000000008600000000000000010000000000000000
  | 38 => 0x2293b4800000000015469180000000000c8ae780000000000706a1000000000003b2e9000000000001cd97000000000000cc030000000000004f4180000000000019c78000000000000676800000000000011080000000000000140000000000000000000000000000000000000f369ac00000000008b4f1680000000004bf9f74000000000272103c00000000012ce034000000000084c8d0000000000034a10800000000001223bc0000000000052d38000000000001211800000000000029cc00000000000002fc000000000000000c00000000000000000000093555e00000000005b2630000000000036150c00000000001e88040000000000103a6a00000000000801c000000000000398480000000000016d340000000000007a76000000000000203000000000000005c400000000000000840000000000000002000000000000000000000552a52000000000035516400000000002014e00000000000126abf000000000009fd9e0000000000050e500000000000025840000000000000f8a3000000000000587a00000000000019640000000000000540000000000000009f00000000000000060000000000000000
  | 39 => 0x247e9b800000000016900300000000000d607b0000000000078b828000000000040192800000000001f962000000000000e29200000000000059c18000000000001e0980000000000007e100000000000001690000000000000020800000000000000080000000000000000000bac4f9c400000000624975a40000000030ebb3e80000000016ca06e80000000009ccbf1c0000000003d1902800000000015064f00000000000627ea400000000001730b4000000000004019c0000000000006e780000000000000550000000000000000c00000000000000000000717e1ae0000000004094aae00000000022fb97000000000011deed00000000000880f7a00000000003b4f9c00000000001723c0000000000007cf6e0000000000022a3600000000000073c20000000000000f9000000000000000f40000000000000002000000000000000000003936cd100000000020929a100000000011a76a600000000009061e4000000000044bfd100000000001dfd7200000000000bb56c000000000003f45900000000000118b10000000000003a9700000000000007da000000000000007a00000000000000010000000000000000
  | 40 => 0x1d09a3e800000000108e21500000000008fcfcc000000000049aa938000000000232bb880000000000f652e00000000000609cc0000000000020d6c800000000000930e8000000000001f2700000000000004480000000000000045800000000000000080000000000000000000c877f6b4000000006a1ea69c0000000035302d040000000018fc0e64000000000ada8c10000000000448813800000000017f7ea8000000000072b90800000000001bd35c0000000000050584000000000000947c000000000000081c0000000000000018000000000000000000007a0165200000000045dab9a000000000261e02800000000013a4f06000000000097303e000000000042ce6400000000001a86700000000000092a88000000000002a05a00000000000093a6000000000000159800000000000001920000000000000006000000000000000000003c584b50000000002283af000000000012cf44200000000009adcbb00000000004a592f000000000020c59800000000000cf84c0000000000047657000000000001454900000000000046c80000000000000a3600000000000000bb00000000000000030000000000000000
  | 41 => 0x25443f800000000017134800000000000db487000000000007bf020000000000041f7a80000000000209a0000000000000eaaa0000000000005d5a0000000000001f658000000000000848000000000000017d0000000000000022000000000000000080000000000000000009bb979ce400000004bddeabf8000000022bd3405400000000ec727498000000005c09e47000000000201f64b00000000009c5edc800000000027d42b000000000007fd7ac0000000000124f88000000000001932c0000000000000ea8000000000000001800000000000000000005eff643000000000320f20140000000018f47a5a000000000ba57ff6000000000504f2fa0000000001f60de80000000000ad5984000000000032f9d600000000000c120c00000000000219ec0000000000003a8600000000000002d6000000000000000600000000000000000002fcc479e0000000019332c18000000000c91e17f0000000005ded6a20000000002883ba90000000000fd8a68000000000057a836000000000019d1fc00000000000620b000000000000111f00000000000001df1000000000000017600000000000000030000000000000000
  | 42 => 0x1c7f92f000000000103828b80000000008c9965800000000047d6110000000000222ff180000000000ee743000000000005d04b000000000001f6198000000000008b020000000000001cf480000000000003de800000000000003c000000000000000080000000000000000000010bbd7c0000000000a449a400000000006088b4000000000035dc5400000000001c37b800000000000dabc8000000000005fe880000000000024dc0000000000000bce40000000000002e3c000000000000074c000000000000007c00000000000000000000000000000000000008b8f74000000000055ed6c000000000032b16c00000000001c6b7800000000000ef9e80000000000074ef80000000000033bf8000000000001421c00000000000068ec0000000000001a54000000000000045400000000000000500000000000000000000000000000000000003cb30cc00000000022bb5e500000000012eff9300000000009c007200000000004af1bd0000000000210f4200000000000d18660000000000048289000000000001491a00000000000047ab0000000000000a5500000000000000bc00000000000000030000000000000000
  | 43 => 0x1e0fdd780000000011305e4800000000095d47100000000004d10e8800000000024faed8000000000104a45000000000006711a00000000000236c1000000000000a12380000000000022fb8000000000000507000000000000005b800000000000000180000000000000000000b7dcfd340000000060a02b400000000030041b48000000001652fc70000000000993b07c0000000003b87a0000000000014681b000000000005f1df00000000000163dc4000000000003ce40000000000000679800000000000004f0000000000000000c000000000000000000006dd299e0000000003e534a800000000021a7acc0000000001120ce2000000000081d0aa00000000003845a0000000000015cc880000000000074a52000000000001fef600000000000068e80000000000000dc400000000000000d200000000000000020000000000000000000038689b60000000002015683000000000115ec6300000000008de34a000000000043779300000000001d623e00000000000b7386000000000003dc1f000000000001116c00000000000038fd00000000000007a5000000000000007800000000000000010000000000000000
  | 44 => 0x1c1d2a28000000000ffcafb00000000008a7468000000000046aa8d800000000021976080000000000e9ffa000000000005b284000000000001eb6880000000000087ea8000000000001c5100000000000003cc000000000000003b8000000000000000800000000000000000000e6ac3f000000000083717c00000000004751dcc0000000002481a0c000000000116a09c000000000079d58000000000002fb8f800000000001031a400000000000485b8000000000000f4800000000000002174000000000000021c0000000000000004000000000000000000062bb9dd8000000003432e3ee000000001a1f9284000000000c3fc78c00000000054f40a4000000000216f24c0000000000ba722800000000003785c600000000000d6260000000000002651200000000000045fc00000000000003c8000000000000000c000000000000000000003ca957500000000022b7c5c00000000012ef83a00000000009c0e3d00000000004b048f0000000000211f8000000000000d239c00000000000488fd0000000000014c2900000000000048cc0000000000000a9e00000000000000c500000000000000030000000000000000
  | 45 => 0x1301b98ab0000000093d938800000000043881b8e000000001ca4671b800000000b1bbec30000000003dbf3b400000000012acf1c00000000004b83fb80000000000efcdb0000000000021d440000000000002d92000000000000019f800000000000000300000000000000000000b75745f8000000006054e188000000002fdbd76c00000000163ebc5800000000098a3ce40000000003b47470000000000144fbf800000000005e9f280000000000161c00000000000003c758000000000000669400000000000004d8000000000000000c00000000000000000005d58de6600000000311e1aee0000000018718a58000000000b6261040000000004e4e0360000000001e8004c0000000000a7d500000000000031194e00000000000b8b96000000000001fd9200000000000036b800000000000002a0000000000000000600000000000000000002f099b680000000018c3ddab000000000c553f4b0000000005bfa7fc00000000027946650000000000f6f49e0000000000550e66000000000018edc1000000000005e02e00000000000104250000000000001c0d000000000000015a00000000000000030000000000000000
  | 46 => 0x17f45270800000000ca1182b00000000064ca7320000000002f11a2f800000000144cbbf80000000007f008600000000002be34400000000000ceaaf8000000000030f9280000000000088750000000000000ed600000000000000b780000000000000018000000000000000000a28f38dd400000004f75c36a40000000248690c5c00000000f9c0076c0000000061c132200000000022596348000000000a8a31b80000000002b6e21800000000008d82fc000000000014b7bc000000000001d90400000000000012940000000000000028000000000000000000063dbc3b40000000034d62054000000001a778b78000000000c6c745e0000000005645d3c00000000022012f80000000000bdf8d0000000000038b2c200000000000db48400000000000275dc000000000000482800000000000003e6000000000000000c000000000000000000031c64e89000000001a5484c6000000000d2f8bad00000000062ff92b0000000002af33cc00000000010ebc9400000000005e7a7200000000001c2d8d000000000006ce2b000000000001387200000000000023c300000000000001ef00000000000000060000000000000000
  | 47 => 0x132cce25a00000000953ee5300000000044373d31000000001cf46a60000000000b3d5a510000000003e8ab9800000000012f05ea00000000004cafd400000000000f3e1400000000000227080000000000002e4f00000000000001a0000000000000000300000000000000000009b6b19c0c00000004bae20914000000022a1a03bc00000000eb83a05c000000005b9215c0000000001fe89aa80000000009af9cd80000000002756f7800000000007d99c4000000000011d44c00000000000182440000000000000da400000000000000180000000000000000004e228b00a00000002610207ce0000000116d0bd62000000007692c94e000000002e222d28000000001016b53c0000000004e3855400000000013e1c4000000000003f97be0000000000090d62000000000000c51e000000000000070a000000000000000c00000000000000000002f1d91d40000000018cec22b000000000c5adbd30000000005c25a2600000000027a766d0000000000f76c6e0000000000553706000000000018f8cb000000000005e23200000000000104350000000000001bf5000000000000015400000000000000030000000000000000
  | 48 => 0x1ecbaf980000000011a3aed80000000009a116700000000004f6ee580000000002638e1800000000010e4a7000000000006b5060000000000025101000000000000a9a1800000000000251a80000000000005610000000000000062800000000000000180000000000000000000014ab5480000000000ce929400000000007bf7dc000000000046f20800000000002657dc0000000000135108000000000008e878000000000003a9e40000000000014aa00000000000005dac000000000000130400000000000002300000000000000014000000000000000000000b88588000000000074427c0000000000467ac0000000000028d26e000000000016627800000000000b7ac80000000000056a000000000000024ada000000000000d72800000000000040740000000000000e4000000000000001e60000000000000018000000000000000001f9d42f7fa0000000e393437b400000005f9463d90000000024fea908b00000000cf9f66ba0000000040876110000000001139e6300000000003c7009b0000000000a2d86a000000000012e79400000000000140800000000000000853000000000000000a0000000000000000
  | 49 => 0x1e5e2de800000000116063d00000000009797b300000000004e0ca98000000000257ee78000000000108a560000000000068d5200000000000241b4800000000000a4b880000000000023e70000000000000531000000000000005f800000000000000180000000000000000000bc32467c0000000063198fd800000000315c9858000000001703cf280000000009e8506c0000000003dd9fd00000000001551ff00000000000641aa8000000000017a45c0000000000041a4800000000000071e80000000000000588000000000000000c000000000000000000007023e0e0000000003fbb3c200000000022785d000000000011936300000000000857e7a00000000003a02e400000000001689c0000000000007901a00000000000214160000000000006dae0000000000000e7000000000000000dc00000000000000020000000000000000000039902de00000000020c89c600000000011c694d00000000009172240000000000454abb00000000001e3e9400000000000bd0d2000000000003fe540000000000011bac0000000000003b4200000000000007f3000000000000007c00000000000000010000000000000000
  | 50 => 0x180725d5800000000cac834a00000000065349680000000002f4c366000000000146b1c580000000007fe9e400000000002c48e400000000000d11a00000000000031c198000000000008b960000000000000f5c00000000000000c20000000000000001800000000000000000000e53b8940000000008287b6800000000046c3530000000000242ead4000000000113c6c40000000000785f7000000000002f09c000000000000fe8cc0000000000046c14000000000000ed7800000000000020300000000000000204000000000000000400000000000000000006500818e00000000357fecfa000000001ad59566000000000c9dc15200000000057c8e5000000000022b04740000000000c2709c00000000003a4b8000000000000e2e7a00000000000291f60000000000004c7a0000000000000436000000000000000c000000000000000000003c58f5f00000000022842c200000000012cf9d800000000009ae09900000000004a5bc3000000000020c73c00000000000cf94800000000000476e3000000000001458f00000000000046e60000000000000a4000000000000000bd00000000000000030000000000000000
  | 51 => 0x1ee16cd00000000011b0b4880000000009a883080000000004faea40000000000265894800000000010f2ed000000000006baa100000000000252cb800000000000aa06000000000000251f800000000000055b8000000000000061000000000000000180000000000000000000015281980000000000d3cf3400000000007f5d8c0000000000490f70000000000027987c00000000001403880000000000094458000000000003d48c0000000000015bd0000000000000634c0000000000001454000000000000025800000000000000140000000000000000004e4b2c238000000026292576a0000000117b9d5b80000000077120724000000002e6287b400000000103460640000000004efb4600000000001426b32000000000040d6700000000000095256000000000000ce980000000000000798000000000000000c00000000000000000002f52e6ac0000000018ee22bf000000000c6c82810000000005cbc44f00000000027f2bf50000000000f99996000000000056201a0000000000194e76000000000005fca20000000000010a910000000000001cff000000000000016900000000000000030000000000000000
  | 52 => 0x1c197458000000000ffa35200000000008a5ad70000000000469ac30000000000218e1e80000000000e9ae4000000000005aff2000000000001ea3f00000000000087778000000000001c2e00000000000003c5000000000000003b0000000000000000800000000000000000000e02ca700000000007f642d000000000044e4cac000000000231f4c000000000010ab59c000000000073ddc000000000002cfeb800000000000f16780000000000042438000000000000da100000000000001c9400000000000001b00000000000000004000000000000000000007356bec00000000041b18ce000000000239f69e0000000001237ef800000000008ae10600000000003c9e4c000000000017ae1c000000000008005200000000000237f800000000000076720000000000000fd200000000000000f400000000000000020000000000000000000004518d600000000002a82860000000000190e4a00000000000e081a000000000007626c000000000003990c00000000000196c40000000000009dd4000000000000333a0000000000000cca0000000000000216000000000000002600000000000000000000000000000000
  | 53 => 0x18fb277e800000000d38227c00000000069f6c7080000000031bf9540000000001598aba0000000000883c8000000000002f967d00000000000e35ec000000000003700b8000000000009e2c000000000000122780000000000000fc0000000000000003000000000000000000000f14518400000000089fbbe00000000004b30a5800000000026af6240000000001291a1c000000000082ec60000000000033cb50000000000011cf1400000000000510f400000000000119c0000000000000288800000000000002e4000000000000000c0000000000000000000079ad48400000000045a08fc00000000025f73c6000000000138c3060000000000964062000000000042463800000000001a3f3c000000000009091e00000000000292d80000000000008f44000000000000149a0000000000000176000000000000000600000000000000000002e88cf7200000000187a9788000000000c2d901b0000000005ab62fe00000000026fa1710000000000f2c0580000000000536a6e0000000000185ff4000000000005b8dc000000000000fbf00000000000001af5000000000000014a00000000000000030000000000000000
  | 54 => 0x175a714a800000000c49c61580000000061d80ac0000000002d91ad60000000001396d3b80000000007a1273000000000029fa1000000000000c46ed800000000002e2b08000000000007f3e8000000000000da400000000000000a7000000000000000180000000000000000000be0771b0000000006420f9480000000031e9032400000000174a27e0000000000a08fd140000000003eb6fb000000000015a4ce8000000000065c1f000000000001810c80000000000042e58000000000000741c00000000000005a0000000000000000c0000000000000000000072c75ba00000000041610b000000000023755200000000001223f4800000000008a5da200000000003c74a0000000000017a85000000000000804880000000000023c3a000000000000789000000000000010700000000000000108000000000000000200000000000000000000393655a000000000209264700000000011a75bf0000000000906247000000000044c0bb00000000001dfe6e00000000000bb63e000000000003f4ec00000000000119080000000000003ac100000000000007e9000000000000007d00000000000000010000000000000000
  | 55 => 0x18f5b81d000000000d34c75e00000000069d712c00000000031add69800000000158f5d7000000000087f48000000000002f771800000000000e29fb8000000000036c490000000000009d46000000000000120400000000000000f9800000000000000300000000000000000000c8d83d7c000000006a518014000000003549384c00000000190754dc000000000adf0a60000000000449ff2800000000017fd938000000000072be4800000000001bcb94000000000005014c0000000000009374000000000000080400000000000000180000000000000000004cba3e00c0000000255446f1400000001110903080000000073ea628a000000002d022c8c000000000fa8a9f80000000004be97d0000000000133a7f600000000003d3f4c000000000008ad5c000000000000bc3800000000000006c2000000000000000c00000000000000000002e913f5300000000187f9d6a000000000c306d740000000005acf0690000000002706beb0000000000f31fec00000000005393600000000000186f63000000000005bdbb000000000000fd1e0000000000001b24000000000000014d00000000000000030000000000000000
  | 56 => 0x13ae939f880000000997faecf800000004652e2a4800000001dee89c8800000000ba8416e000000000412043700000000013d1ef5000000000050c4b700000000001030d1800000000002505c80000000000032b380000000000001d3800000000000000300000000000000000000bf1ebf1c0000000064bdfdb000000000323ce1400000000017744c4c000000000a1ca6cc0000000003f3ce4000000000015d7860000000000066c98c000000000018561c0000000000043bb000000000000075a000000000000005ac000000000000000c00000000000000000005fb44c48000000003273f03a000000001929bebe000000000bbfe74a0000000005110dfa0000000001fb16d40000000000af329c0000000000338cf000000000000c366400000000000220560000000000003b3200000000000002de000000000000000600000000000000000028fc7caf50000000140c1631100000000938d87fd000000003f1cd9f50000000018ba93900000000008b345c20000000002ac7fc20000000000b0a2c800000000002410f70000000000054ca700000000000079a300000000000004cf000000000000000a0000000000000000
  | 57 => 0x2e0eb880000000001d02c200000000001194a200000000000a2d8480000000000593c8800000000002db8800000000000158880000000000009190800000000000352c8000000000000fd20000000000000372000000000000007080000000000000048000000000000000007f5f03c28c00000039560a6328000000181888b74400000009555727240000000346d50a700000000104fc78700000000045c35d28000000000f52c8e400000000029612e400000000004d18f800000000000520fc000000000000224400000000000000280000000000000000004d98880e4000000025c7d5c9c0000000114941ea8000000007589b572000000002db105dc000000000feafe280000000004d49ff0000000000139cb7e00000000003e9614000000000008e0f4000000000000c03800000000000006ca000000000000000c00000000000000000026ee3045b000000012f59c1ca000000008ad588db000000003b0517090000000016f3c9500000000007fffb2400000000026ddf5e00000000009dee0100000000001f89690000000000047ba60000000000006175000000000000037900000000000000060000000000000000
  | 58 => 0x1c40ec300000000010104e900000000008b1306800000000046f1b5800000000021b18580000000000ea5e2000000000005b149000000000001e8f980000000000086420000000000001b97000000000000039980000000000000358000000000000000800000000000000000000e9eeb58000000000855d2fc00000000048648fc00000000025114b400000000011af18c00000000007baff8000000000030663800000000001062180000000000048cf0000000000000f324000000000000206400000000000001ec00000000000000040000000000000000000009c7be8000000000061435e00000000003a0662000000000020f7ec000000000011a8be000000000008cb8c000000000003fec40000000000019bf60000000000008cdc0000000000002602000000000000070e00000000000000a80000000000000002000000000000000000003ec88ab000000000240196500000000013aedaa0000000000a29fb100000000004e6423000000000022b73200000000000dd034000000000004c8120000000000015edb0000000000004ccb0000000000000b1600000000000000c700000000000000030000000000000000
  | 59 => 0x1939a641000000000d5bc7648000000006b2c885000000000325e4f980000000015e479b00000000008a4f7d00000000003066b600000000000e7ca200000000000383c9000000000000a25380000000000012b700000000000001048000000000000003000000000000000000000f6d68640000000008d624f80000000004d2d4f800000000027c93cc000000000132405c0000000000874e90000000000035b0100000000000128584000000000005499400000000000126e80000000000002a6800000000000002fc000000000000000c00000000000000000005dfb8ed8000000003179e39e0000000018a2bea2000000000b7b31c60000000004f07eaa0000000001ecf60c0000000000a9b6b4000000000031b5ac00000000000bb4840000000000020562000000000000379e00000000000002aa00000000000000060000000000000000000037d7d1f0000000001fb99f80000000001126c9e00000000008bd95900000000004257d500000000001cce1800000000000b2d94000000000003bea500000000000106cb00000000000035f0000000000000070a000000000000006900000000000000010000000000000000
  | 60 => 0x1bc4c398000000000fc516b8000000000885a9c0000000000457457000000000020ee5280000000000e4a170000000000058a98000000000001dae480000000000082178000000000001ab0800000000000037c0000000000000034000000000000000080000000000000000000bfa7e03000000000650d878c000000003268e2cc00000000178b4fd4000000000a27e4740000000003f8d9d800000000015f81180000000000677ff80000000000188ae80000000000044754000000000000775400000000000005cc000000000000000c0000000000000000000071f6f6e00000000040dbe36000000000232366800000000011f3c6c000000000088b05a00000000003b952c0000000000173d90000000000007d6fa0000000000022b9600000000000073ba0000000000000f7800000000000000f0000000000000000200000000000000000000398b0c100000000020c539700000000011c46e20000000000915d420000000000453ec100000000001e382e00000000000bcdb4000000000003fcfd0000000000011b310000000000003b2100000000000007ee000000000000007c00000000000000010000000000000000
  | 61 => 0x19531845000000000d6a39900000000006ba9778000000000329e04d0000000001602c2700000000008b22d0000000000030b97000000000000e98cf0000000000038bc1000000000000a41000000000000012f80000000000000109000000000000000300000000000000000009a6fc896800000004b2c27ca800000002262424b800000000e9b70844000000005ad22118000000001fa0c9700000000009983dd000000000026f23fc00000000007c50e8000000000011aab800000000000181280000000000000df4000000000000001800000000000000000005cfe959e0000000030ea2ea200000000185511a4000000000b53a0940000000004ddbd360000000001e4d4240000000000a690a8000000000030a8b600000000000b6b4e000000000001f68e00000000000035bc0000000000000290000000000000000600000000000000000002ef77c2f0000000018b96dea000000000c4f84200000000005bcaeaa000000000277d5830000000000f65064000000000054ccb8000000000018d6ec000000000005d99f00000000000102b60000000000001bd8000000000000015600000000000000030000000000000000
  | 62 => 0x17d8ba83800000000c915dd30000000006441def0000000002ecbb58000000000142b5f580000000007e172200000000002b87e600000000000ccbbc00000000000306f780000000000086a90000000000000e9900000000000000b4000000000000000180000000000000000000c046d87c0000000065670498000000003298ca980000000017a378c0000000000a333b6c0000000003fdb99000000000016161700000000000682080000000000018b75c00000000000450c800000000000078a800000000000005e0000000000000000c0000000000000000000071b98ea00000000040b6f38000000000230e3d000000000011e85a200000000008854c200000000003b6b800000000000172cf0000000000007d1820000000000022a4a00000000000073980000000000000f8000000000000000f20000000000000002000000000000000000294026c9c0000000142fba1f50000000094a9ab2a000000003fa164460000000018f3abde0000000008c9930a0000000002b433940000000000b2e7970000000000249b3800000000000565130000000000007c6600000000000004f4000000000000000a0000000000000000
  | 63 => 0x13647c7c30000000097106ed700000000451d0d9e000000001d5e709e000000000b6a6cdb0000000003f9fed6000000000134e3c400000000004e5f8500000000000fa1cb0000000000023809000000000000302a00000000000001b8000000000000000300000000000000000009c5485a6400000004c286f900000000022de3898c00000000ed451698000000005c5274d000000000203347e00000000009c9481800000000027cfe5000000000007f6b4c00000000001229a00000000000018cd40000000000000e48000000000000001800000000000000000005dbe0f080000000031563b1400000000188f0a72000000000b70ea8a0000000004eb7f2a0000000001eabbe80000000000a8d374000000000031677200000000000b9e7400000000000200ac00000000000036ee000000000000029a000000000000000600000000000000000027977ddf50000000134e9a9a3000000008d994ad7000000003c4e3f1e0000000017810bec000000000836e42e000000000280b6ae0000000000a36daf000000000020d3d7000000000004b4ad00000000000067a100000000000003c400000000000000060000000000000000
  | 64 => 0x1d2ef4100000000010a33318000000000908173800000000049ffe98000000000234f8580000000000f71130000000000060be70000000000020c9e00000000000092100000000000001ea2800000000000042080000000000000408000000000000000800000000000000000000139e9880000000000c338780000000000748c20000000000042485c0000000000238cc8000000000011bd10000000000008148000000000000344d400000000000120480000000000004ee80000000000000f20000000000000018c0000000000000008000000000000000000064913acc00000000353eb024000000001ab0fc10000000000c8a435c000000000572cd6c0000000002267ec80000000000c088c000000000003995c800000000000df52c00000000000283bc0000000000004a100000000000000404000000000000000c000000000000000001ffeca722d0000000e6862a971000000060eb371230000000258f148c000000000d3186ed80000000041b954f200000000119569a60000000003ddd65d0000000000a7510700000000001387270000000000014dd500000000000008c6000000000000000a0000000000000000
  | 65 => 0x175d08ac000000000c4b671300000000061e7b5f8000000002d9a9cb000000000139b9b280000000007a383e00000000002a0af700000000000c4d90000000000002e4df0000000000007fcd0000000000000dbc80000000000000a90000000000000001800000000000000000000df7a0780000000007ef85e000000000044a6ae400000000022fd758000000000109a22c0000000000735d2000000000002cc8e800000000000f03000000000000041e70000000000000d8c00000000000001c5c00000000000001a8000000000000000400000000000000000005f72d31e00000000324ff1aa000000001917053c000000000bb6c99200000000050cf6160000000001f96d640000000000ae9ab80000000000335f2400000000000c2b6e0000000000021e760000000000003b0400000000000002de000000000000000600000000000000000000397573d00000000020b89f000000000011bd76c00000000009123a3000000000045236100000000001e2c8800000000000bc970000000000003fbbb0000000000011aed0000000000003b1800000000000007ec000000000000007b00000000000000010000000000000000
  | 66 => 0x144c26915000000009eb874aa0000000048f225c8000000001f2a8ebe800000000c31e8fd0000000004488648000000000150457800000000005688ee8000000000119aad00000000000292fa0000000000003ac000000000000002528000000000000005000000000000000000097e89def4000000049d7806a0000000021b8aa66c00000000e4c6c4a40000000058b273f0000000001eccfe4000000000094f6d58000000000259df4c00000000007756bc000000000010d2200000000000016af40000000000000d14000000000000001800000000000000000005ac7c336000000002fa9f0100000000017a90cb0000000000afca1f60000000004b4d9160000000001d3463000000000009fd97000000000002e736600000000000ad446000000000001d8c000000000000032200000000000000266000000000000000600000000000000000002e1920bd00000000183b7fcb000000000c0bae3800000000059a426000000000026796270000000000ef4d860000000000521980000000000017f19f0000000000059b99000000000000f63d0000000000001a48000000000000014200000000000000030000000000000000
  | 67 => 0x1377f7c400000000097b281c980000000456c8a96000000001d82cb85000000000b79b3610000000003ffc633000000000136cdd800000000004ee84280000000000fc03a0000000000023d1280000000000030be00000000000001c2000000000000000300000000000000000000bd0a9c84000000006390bc0000000000319aa7c8000000001721ffdc0000000009f5cfdc0000000003e30b2000000000015702f0000000000064a45c000000000017c1340000000000041da000000000000071d8000000000000057c000000000000000c00000000000000000005f974ee80000000032645884000000001921dbe6000000000bbc349a00000000050f7a7a0000000001fa7f180000000000af02ac000000000033815e00000000000c34c4000000000002206c0000000000003b4a00000000000002e20000000000000006000000000000000000003921c8b0000000002085a64000000000119fc720000000000901d920000000000449c0d00000000001dec3800000000000badfc000000000003f19600000000000117df0000000000003a6c00000000000007d6000000000000007a00000000000000010000000000000000
  | 68 => 0x12cd434f700000000921b8b2b0000000042a80c24000000001c3ad6c0000000000aedc3530000000003c9c4fe00000000012472400000000000499de100000000000e87f700000000000208a50000000000002b540000000000000186000000000000000300000000000000000009807d04a0000000049e608824000000021bed28c800000000e4eb58640000000058bd74a8000000001ecf0ee800000000094f2f500000000002596fa80000000000771d50000000000010bf9c00000000000167380000000000000cbc00000000000000180000000000000000004cccebdec0000000255c60dc8000000011139afcc0000000073f87d76000000002d03eafc000000000fa759200000000004bd5188000000000132fe2600000000003d023c0000000000089e88000000000000ba2400000000000006a6000000000000000c00000000000000000002e5d1701000000001861cb1d000000000c2030660000000005a498b100000000026c6d570000000000f15f2a000000000052e3040000000000183360000000000005aced000000000000f98b0000000000001aa2000000000000014300000000000000030000000000000000
  | 69 => 0x13c0fdfad800000009a1a9ca480000000469fecff800000001e126312000000000bb7a690000000000418014900000000013f2d3b0000000000515e3280000000001054ac800000000002566f800000000000335080000000000001d9000000000000000300000000000000000000beac0d98000000006481cfac00000000321f823c0000000017674014000000000a1790240000000003f22f3800000000015d2098000000000066cb9000000000001861e0000000000004411400000000000076c400000000000005bc000000000000000c0000000000000000042a79f50ae0000001e1d1a1e440000000cb59b8bd800000004f2a7528a00000001bf6a270e000000008c4211380000000025d9e7e000000000086b159e000000000171fb5e00000000002c2b4c0000000000030f180000000000001612000000000000001e000000000000000001f35b0fa0a0000000e0654fd9300000005e1c378ac0000000245cf1df900000000cba425b2000000003f1eddbe0000000010ca9ce00000000003aa3e7e00000000009d03b200000000001212cd0000000000012f3c00000000000007d7000000000000000a0000000000000000
  | 70 => 0xfef51bd9e800000072c1938440000000303818be2800000012ac4788e8000000068da66f800000000209b401c0000000008b58ec10000000001e92280800000000052651f8000000000099030000000000000a1e5800000000000042e800000000000000500000000000000000009a9924b1c00000004b4015fc80000000226b254ec00000000e9f073b4000000005ae66820000000001fa6a2700000000009995ff800000000026f213c00000000007c31740000000000119bd80000000000017d540000000000000d84000000000000001800000000000000000405f631f5c0000001cfee47e920000000c31b48dac00000004ba1cd1e800000001a933df5400000000846afa0400000000236e83080000000007ca5c92000000000150e7dc0000000000273fde0000000000029bc40000000000001154000000000000001400000000000000000027302acc6000000013184777e000000008be91b14000000003b8523c400000000172aa99600000000081542c400000000027524780000000000a008ac00000000002005b6000000000004904a000000000000637c000000000000038c00000000000000060000000000000000
  | 71 => 0x209de4f00000000012c6b8b0000000000a4fa54000000000055ac6e80000000002997f300000000001297620000000000077d90000000000002a391800000000000c6cf0000000000002d6900000000000007140000000000000094800000000000000300000000000000000678fb9b42c0000002b0f128f46800000109a08ae4c40000005da4ad12c80000001da2ccca8400000008371933b000000001ed9a31a8000000005d6d83a8000000000d412c98000000000140e3780000000000107afc0000000000004ea8000000000000003c000000000000000003ebbc942700000001c33e42ca40000000bd585656c000000049349df44000000019a46444c000000007f4972280000000021e694f8000000000769085800000000013e0818000000000024abdc00000000000267140000000000000fbc0000000000000014000000000000000001f9d797f8a0000000e38a6e0cb00000005f8ad4c5a000000024f7e0bb300000000cf615fea00000000406990e600000000112ddb540000000003c304d60000000000a1d25a000000000012b7fd0000000000013b66000000000000081d000000000000000a0000000000000000
  | 72 => 0x1753cf85800000000c45f44400000000061b68da0000000002d80644800000000138e88d800000000079d85c000000000029e37000000000000c3f5e800000000002e0a18000000000007ed00000000000000d9200000000000000a4800000000000000180000000000000000000bb68edb00000000062a26174000000003119201c0000000016df96280000000009d613340000000003d523880000000001518d78000000000062c8b40000000000173ba8000000000004010c0000000000006dc40000000000000530000000000000000c00000000000000000000817b0440000000004a7950000000000028daf0000000000015304320000000000a44ffc00000000004947f000000000001d6f8000000000000a535200000000000304d4000000000000aeb00000000000001ac00000000000000222000000000000000c00000000000000000002faac20b000000001921a696000000000c8965d00000000005db21c1000000000286d6eb0000000000fd23540000000000579aa8000000000019d983000000000006277300000000000114c20000000000001e98000000000000018500000000000000030000000000000000
  | 73 => 0x1cf35e3000000000107f4ae00000000008f373c8000000000494cab000000000022f4dd80000000000f4728000000000005faad000000000002069a000000000000906a0000000000001e56000000000000041b8000000000000041000000000000000080000000000000000000107acd9800000000097de95000000000053729a00000000002b5c36c00000000015102d8000000000096b70000000000003cbe80000000000015660c0000000000064a580000000000016e9000000000000038a0000000000000048c00000000000000180000000000000000000009f85ac0000000000634ff000000000003b5c80000000000021ce5600000000001228d400000000000913b00000000000042480000000000001ade6000000000000945c00000000000028a000000000000007c000000000000000c6000000000000000400000000000000000026eeefb6e000000012f7feb09000000008afb0b62000000003b20c0e3000000001704edde000000000809258a000000000272158c00000000009f8d7000000000002009360000000000049857000000000000656600000000000003b100000000000000060000000000000000
  | 74 => 0x1810ff6d800000000cb1edff80000000065619fe0000000002f620ed8000000001474d6580000000008027f700000000002c5e4000000000000d17900000000000031d418000000000008bac8000000000000f5600000000000000c0800000000000000180000000000000000000bce1d51c000000006377f6d800000000318c45e000000000171a167c0000000009f1bccc0000000003e11c500000000001562fa000000000006455d4000000000017a91c00000000000418080000000000007100000000000000056c000000000000000c000000000000000000007320c22000000000419398800000000023901180000000001230ed200000000008ab6b200000000003c9420000000000017afc000000000000804420000000000023ad200000000000077c800000000000010380000000000000102000000000000000200000000000000000002f79c88f000000001903050c000000000c7707240000000005d0a73700000000028136d30000000000fa5630000000000056561000000000001957ef000000000005fbef000000000001096c0000000000001ca4000000000000015f00000000000000030000000000000000
  | 75 => 0x1c9aa250000000001048d8d80000000008d37598000000000482f030000000000225f2580000000000efe8f000000000005dacb000000000001fa4f8000000000008c740000000000001d5a80000000000003f2800000000000003e000000000000000080000000000000000000bb070374000000006265ebf00000000030f558b80000000016cb76080000000009cb6ebc0000000003cfed6000000000014f3d50000000000061e208000000000016f0c4000000000003ee900000000000006ae80000000000000508000000000000000c000000000000000000007339a4200000000041a20ca0000000002397f6c0000000001234e8000000000008ad36200000000003c9ef4000000000017b29800000000000804420000000000023a420000000000007766000000000000101400000000000000fc0000000000000002000000000000000000275425fff0000000132cf3457000000008c9ddda1000000003be23b910000000017574720000000000828d2f600000000027cce920000000000a2a01c000000000020bd3d000000000004b649000000000000687700000000000003d300000000000000060000000000000000
  | 76 => 0x17e6f819800000000c997ce9000000000648875e0000000002eefe74800000000143cae580000000007e90ae00000000002bb7c800000000000cdc218000000000030b9d80000000000087ab0000000000000ebe00000000000000b68000000000000001800000000000000000099af5964800000004ac72b8380000000223029e2800000000e84326e0000000005a32fa18000000001f631cd00000000009832470000000000268fde000000000007addc8000000000011692800000000000179780000000000000d80000000000000001800000000000000000005eb2547c0000000031e21a0e0000000018db580a000000000b98355a0000000004fe5da20000000001f30bfc0000000000ac1c14000000000032877400000000000befd00000000000021222000000000000396600000000000002c6000000000000000600000000000000000002e79d88f000000001870c936000000000c2770a60000000005a7c5d500000000026da2db0000000000f1bccc000000000052f37c0000000000183059000000000005a907000000000000f7ea0000000000001a4a000000000000013d00000000000000030000000000000000
  | 77 => 0x218b36d0000000001357f4b0000000000aa4b10000000000058a03580000000002b21770000000000135462000000000007cf60000000000002c262800000000000d0590000000000002f990000000000000760000000000000009780000000000000030000000000000000007f53fbc7000000003950d45c5800000018163fa4b000000009546d354c00000003468205980000000104e372b00000000045bd7a60000000000f51ee94000000000296191000000000004d24e80000000000052390000000000000227c00000000000000280000000000000000004e79d6e900000000263e0540200000001183dd03800000000773ca1e6000000002e6b1a0400000000103311b40000000004ed4100000000000140f290000000000040413800000000000929fe000000000000c7f80000000000000722000000000000000c00000000000000000026d7bde1c000000012e9fd7ed000000008a7ad3ba000000003adbdd390000000016e29aa20000000007f98dda00000000026bc7f400000000009d5d6800000000001f6b70000000000004778b0000000000006136000000000000037b00000000000000060000000000000000
  | 78 => 0x17d9d6c9800000000c921dfb00000000064499fc0000000002ed0755800000000142e1bd80000000007e2e9200000000002b935c00000000000cd0ba80000000000308d580000000000087390000000000000eb800000000000000b78000000000000001800000000000000000000e76ca4c00000000083db9e00000000004787f88000000000249a5040000000001173774000000000079fce000000000002fb77000000000001027940000000000047e5c000000000000f1400000000000002098000000000000020400000000000000040000000000000000000602327620000000032b2df3000000000194bbc2c000000000bd1337a0000000005193e8e0000000001fea2900000000000b0916800000000003401ba00000000000c561a00000000000226c00000000000003c0400000000000002ea0000000000000006000000000000000000003a52055000000000213f73a000000000120c580000000000093e03e000000000046904100000000001edc1400000000000c15c800000000000418cc00000000000124250000000000003d560000000000000848000000000000008200000000000000010000000000000000
  | 79 => 0x17c7e47b000000000c8735d980000000063e3ea68000000002e980ed0000000001410a9080000000007d4a2f00000000002b2e9d00000000000ca973800000000002fbe800000000000083e68000000000000e2580000000000000ac0000000000000001800000000000000000000e95f1980000000008508fa80000000004835d5400000000024f917800000000011a3a2c00000000007b63300000000000304b880000000000105b880000000000048c90000000000000f3b800000000000020ac00000000000001f800000000000000040000000000000000004f58edbea000000026b6d1002000000011c1f6ac200000000791cf06a000000002f42ab8800000000108b612400000000050d80b400000000014b1770000000000042dcfe000000000009aace000000000000d7de00000000000007fe000000000000000c000000000000000000030614425000000001987fe4f000000000cbfdc7c0000000005f65a2b00000000029370870000000001026ff6000000000059931800000000001a78ae0000000000064f610000000000011be10000000000001f54000000000000018d00000000000000030000000000000000
  | 80 => 0x13734dc2a80000000979123c580000000455f5775800000001d7e817f000000000b78cd960000000003ffddaf00000000013704eb00000000004f091580000000000fccab8000000000024022800000000000312680000000000001c6000000000000000300000000000000000000bf36b9580000000064cc6d580000000032452d74000000001778cf4c000000000a1ef1c40000000003f4e09000000000015deba8000000000066f3c400000000001863000000000000043ec8000000000000762c00000000000005bc000000000000000c00000000000000000005e569ba40000000031ab1b420000000018bbc6a6000000000b8701660000000004f590420000000001eee1940000000000aa531c000000000031dba000000000000bb9d8000000000002051e000000000000375a00000000000002a200000000000000060000000000000000000039cfb8200000000020ef27600000000011dcea10000000000923614000000000045af2300000000001e6dd400000000000be4ba000000000004058c0000000000011dc80000000000003bb200000000000007ff000000000000007c00000000000000010000000000000000
  | 81 => 0x1010e4bcef800000073caf938d800000030b38fda0800000012e1c2bd7800000006a2e83ec000000002114e0e90000000008dba42f0000000001f32cbe0000000000547ec8800000000009e13c800000000000a9498000000000000474800000000000000500000000000000000009e083f15400000004d0cdda000000000234f645cc00000000f08bbbf4000000005db86fb00000000020bd6c400000000009f8311800000000028a784c000000000082805c000000000012ab8000000000000199940000000000000ec400000000000000180000000000000000004e86d6a8000000002645072ca0000000118773e1000000000775856d6000000002e778e4400000000103836b40000000004ef2c50000000000141946c0000000000406ee80000000000093486000000000000c9c0000000000000074a000000000000000c00000000000000000003028753500000000196670d0000000000cace7c40000000005ec319d00000000028e55170000000001001070000000000058939800000000001a1a5f000000000006324100000000000114f00000000000001e3c000000000000017900000000000000030000000000000000
  | 82 => 0x1d25fa5000000000109d36500000000009043ca800000000049d9e2800000000023394180000000000f64da00000000000605b900000000000209d080000000000090f80000000000001e4b000000000000040d800000000000003e800000000000000080000000000000000000c056e038000000006569ea6800000000329657c400000000179fbc44000000000a2ffec40000000003fb82f00000000001601c8800000000006783ec00000000001879e00000000000043e78000000000000751c0000000000000594000000000000000c00000000000000000000725b34e0000000004113660000000000233fd5c0000000001200d4000000000008900ca00000000003baa800000000000173ce8000000000007d190000000000002278600000000000071e00000000000000ef400000000000000e00000000000000002000000000000000000003afab6800000000021a56520000000001247237000000000095e10800000000004794ff00000000001f557c00000000000c48260000000000042aa000000000000129220000000000003e460000000000000859000000000000008000000000000000010000000000000000
  | 83 => 0x17a12dd5800000000c71dc028000000006331cd00000000002e414ed80000000013e9d5d80000000007c50a500000000002ad7cc00000000000c90cd000000000002f6d180000000000083598000000000000e2c00000000000000ae800000000000000180000000000000000000c0a8418800000000659ef4b40000000032b7605c0000000017b33d94000000000a3accc40000000004010bc8000000000162ae180000000000689038000000000018d5b000000000000456cc000000000000796400000000000005ec000000000000000c00000000000000000005f43eaac000000003231d86c00000000190490d2000000000bac10620000000005071f020000000001f67da80000000000ad4524000000000032d73e00000000000bfe600000000000021304000000000000391e00000000000002ba00000000000000060000000000000000000038a286b0000000002034956000000000116e10200000000008e4b51000000000043994d00000000001d660400000000000b6e1c000000000003d66f0000000000010dff00000000000037920000000000000746000000000000006d00000000000000010000000000000000
  | 84 => 0x13c37ba10000000009a2fc7008000000046aa976d000000001e17716b000000000bb9e1c5000000000418e90900000000013f826a0000000000517a178000000000105ca6000000000002585b80000000000033ab00000000000001e2000000000000000300000000000000000000bead0dbc00000000647c2118000000003218798000000000176144ac000000000a135b0c0000000003efa15000000000015bc8e000000000006632440000000000182a7c00000000000432480000000000007460000000000000059c000000000000000c000000000000000000060eff5ce000000003327b7e200000000198b3a64000000000bf1c28e000000000528cf9600000000020576340000000000b340a8000000000034ec3800000000000c981e00000000000234de0000000000003dfc000000000000030a0000000000000006000000000000000000272f9517900000001318634b1000000008bedcbab000000003b89690500000000172d9214000000000816e84a000000000275ef760000000000a05b3e0000000000202153000000000004977f00000000000064cd00000000000003ab00000000000000060000000000000000
  | 85 => 0x1d97f6080000000010e304d800000000092d28700000000004b461c000000000023f75880000000000fc07b0000000000062d9e00000000000218fd80000000000095c08000000000001f6e800000000000043900000000000000410000000000000000800000000000000000813d5faa940000003a3da1ec080000001881ce41b40000000981bd20080000000357f04710000000010ae23ea0000000004787f598000000000fc406a00000000002ac50ac0000000000503508000000000005639c000000000000248800000000000000280000000000000000004e729cab800000002639e505000000001181a1ae000000000772a8986000000002e62a4f400000000102f81300000000004ebf1f00000000001408d760000000000402af00000000000092780000000000000c8300000000000000736000000000000000c00000000000000000027b8930fb0000000135fea080000000008e223a4b000000003c8d88b300000000179c013000000000084146700000000002843c5e0000000000a470e50000000000210f69000000000004bea000000000000068a500000000000003cf00000000000000060000000000000000
  | 86 => 0x1347495ae00000000961bd0030000000044a3f767000000001d265fbe800000000b527ac10000000003f0bd36000000000131bcae00000000004d76d680000000000f6c980000000000022f7d0000000000002f7100000000000001b6800000000000000300000000000000000000bb86a34c0000000062b455900000000031237f100000000016e543b40000000009d8fd2c0000000003d68540000000000152258000000000006302740000000000174e6c00000000000406100000000000006ed00000000000000554000000000000000c00000000000000000005fe4398a000000003290249c00000000193996e8000000000bc8529a0000000005153c2e0000000001fcff380000000000affab0000000000033d40200000000000c4b2200000000000224e40000000000003bd800000000000002ea000000000000000600000000000000000002f775639000000001900c641000000000c75443a0000000005cf6ba70000000002806f770000000000f9e4d20000000000561cdc0000000000193f06000000000005f30500000000000107070000000000001c3e000000000000015900000000000000030000000000000000
  | 87 => 0x133b4801d0000000095b43b0200000000446f0352000000001d0cf84b800000000b4731af0000000003ec2de80000000001301a3c00000000004cf66580000000000f4c9100000000000229820000000000002eb600000000000001ab800000000000000300000000000000000009c38b8a5000000004c187ca94000000022d57e83000000000ecfce2fc000000005c2f9ba8000000002023d8c80000000009c3294000000000027ae65000000000007ed6800000000000120bac00000000000189700000000000000e3400000000000000180000000000000000004dc25ed4a000000025dd04c1800000001153527d20000000075d09962000000002dcd7688000000000ff52bc00000000004d7ca1400000000013aa09a00000000003ec55e000000000008ea78000000000000c20e0000000000000702000000000000000c00000000000000000003037d25e00000000196f8372000000000cb205ab0000000005eeeccd00000000028fb219000000000100b0b4000000000058d5be00000000001a32150000000000063940000000000001167e0000000000001e75000000000000017d00000000000000030000000000000000
  | 88 => 0x102036adac0000000743c2dad4000000030e4145e2000000012f4bbd7d000000006a9841d300000000213481680000000008e3453c0000000001f4791e000000000054963e000000000009dc44000000000000a7de000000000000045b000000000000000500000000000000000080a7e3ddb800000039f2b09c04000000185e6046d000000009721e208000000003519b8cc800000001089225a80000000046ca3820000000000f90c3fc0000000002a1549800000000004e84fc0000000000053c30000000000000232800000000000000280000000000000000004f79f9eb8000000026c46686a000000011c68316800000000792b59b6000000002f3ed3940000000010851f2400000000050952600000000001491e780000000000422c500000000000097f76000000000000d18800000000000007a2000000000000000c000000000000000001f87357bc00000000e2db7f72f00000005f39fae9c000000024d51b89800000000ce8623f600000000401c0df600000000111602e80000000003bcee6b0000000000a0a1d400000000001291410000000000013964000000000000082a000000000000000a0000000000000000
  | 89 => 0x207ef2400000000012b1c838000000000a41f148000000000552286000000000029454180000000001268a3000000000007650900000000000297e4800000000000c1f10000000000002bbc80000000000006a780000000000000850000000000000002800000000000000000001220ccd0000000000a84e1680000000005d48a8000000000030f89dc00000000018158700000000000aef3f0000000000047dc00000000000019f044000000000007e090000000000001e0780000000000004f80000000000000072c000000000000003000000000000000003428c9947120000015b2d04405c00000085f08713fc0000002f40c0f9f00000000ef7a71b46000000042743158800000000f9df2198000000002f5f4c180000000006bc2f0a0000000000a388740000000000086f040000000000002870000000000000001e000000000000000001fe58d01640000000e5b7d294200000006087ad24e000000025623ca7e00000000d1eed15e000000004149d134000000001170a76c0000000003d393740000000000a506c000000000001327de00000000000144520000000000000862000000000000000a0000000000000000
  | 90 => 0x13f3cd257800000009bd68f918000000047865357800000001e82f210800000000beac5bc00000000042d3b1b0000000001470c03000000000053e303000000000010fdba80000000000277ba80000000000037808000000000000213800000000000000300000000000000000000bed33e8c000000006493fde0000000003226cd500000000017697954000000000a17cbac0000000003f1dee000000000015cd2000000000000669fa4000000000018512c0000000000043d40000000000000769000000000000005d4000000000000000c00000000000000000005fcf5e9a0000000032830894000000001931c0f4000000000bc3e9e6000000000512ee7e0000000001fbe6b80000000000af84b8000000000033aa2a00000000000c3fa200000000000222dc0000000000003bbc00000000000002ee00000000000000060000000000000000000308afb0900000000199de2ae000000000cca8ca60000000005fb1a450000000002954b170000000001030734000000000059b2f400000000001a77b30000000000064ad500000000000119ba0000000000001ed2000000000000018100000000000000030000000000000000
  | 91 => 0x179bb2cc800000000c6e27cc000000000630bc760000000002e2a50780000000013dcdc780000000007be4f000000000002aa57c00000000000c7c4e800000000002efe680000000000081940000000000000de200000000000000a9800000000000000180000000000000000000bdd40cac0000000063fae2780000000031ceca38000000001739634c0000000009ff168c0000000003e619f0000000000157b9f0000000000064adac000000000017b0ec00000000000415080000000000006fc8000000000000054c000000000000000c0000000000000000000603dc7da0000000032bd82e400000000194e9d2c000000000bd0e874000000000518155e0000000001fd93880000000000afe188000000000033a77000000000000c31820000000000021bbc00000000000039e400000000000002bc000000000000000600000000000000000000415245a0000000002596f4700000000014a1cbf0000000000ab4cca0000000000531267000000000025119600000000000ee54e00000000000539af00000000000186c000000000000058090000000000000d59000000000000010800000000000000050000000000000000
  | 92 => 0x13a7e95de80000000994826520000000046379ebc000000001de2114a800000000ba307080000000004100d8a00000000013c7b7a000000000050992200000000001028358000000000024f6000000000000032b200000000000001d5800000000000000300000000000000000009dc06bf4400000004ce91b6400000000233ecc1e000000000f01adb4c000000005d8d9ae00000000020af87300000000009f4a750000000000289ebd8000000000082885c000000000012b7500000000000019c900000000000000f04000000000000001800000000000000000005ea7217a0000000031d94cb00000000018d51010000000000b941a820000000004fbe9ee0000000001f1b8c00000000000ab7960000000000032446600000000000bd9520000000000020c90000000000000389000000000000002ba0000000000000006000000000000000000273359bb90000000131a8c9d8000000008c00af8b000000003b9324640000000017323d34000000000818f4c0000000000276bcb60000000000a0a02800000000002033f30000000000049b18000000000000652d00000000000003ac00000000000000060000000000000000
  | 93 => 0x1813c129000000000cb20be20000000006553d278000000002f51fa18000000001467fa080000000007fa16c00000000002c13b300000000000cf4c8800000000003101600000000000087ee0000000000000ea880000000000000b3800000000000000180000000000000000000c382aaa000000000673343a800000000338b279400000000181b018c000000000a699df400000000041411d00000000001696a4800000000006a888c0000000000194458000000000004655800000000000079ac00000000000005cc000000000000000c0000000000000000000085912940000000004cfabfe0000000002a535ee0000000001601de80000000000ab274e00000000004c93ec00000000001ede3c00000000000ade020000000000032fe0000000000000b8820000000000001c020000000000000224000000000000000a00000000000000000204d8d9aa60000000e8eb5307a0000000620397156000000026062df5f00000000d5fd201e0000000042bb80180000000011e3e2380000000003f1d2530000000000ab54ca0000000000141ada0000000000015a860000000000000933000000000000000a0000000000000000
  | 94 => 0x13ea4485f800000009b77d00800000000474eb726800000001e645d23000000000bdb32b000000000042601440000000001441035000000000052d3f0000000000010af6e80000000000266f4000000000000354580000000000001f5000000000000000300000000000000000000bf6c571c0000000064e6db08000000003250f87000000000177d5a8c000000000a204b0c0000000003f50df000000000015dce00000000000066d7a400000000001855dc0000000000043b1800000000000075b000000000000005bc000000000000000c0000000000000000004f3a6add6000000026a4129c4000000011b70f49c0000000078bdace6000000002f126cb800000000107517600000000005045480000000000147d858000000000041edba00000000000977e4000000000000d13c00000000000007aa000000000000000c00000000000000000002fcbc6fd00000000193096b8000000000c8f064c0000000005dc7f590000000002869d670000000000fc912000000000005725a800000000001997b30000000000060b790000000000010c280000000000001cf4000000000000016500000000000000030000000000000000
  | 95 => 0x17cf17c3800000000c8b4afa80000000064072a30000000002ea9fef80000000014192ad80000000007d856900000000002b45c600000000000cb15e000000000002fe2f800000000000846d8000000000000e3d00000000000000ae800000000000000180000000000000000000c01b1cd80000000065452dec000000003280b6fc000000001793a474000000000a29a5240000000003f86d7800000000015ec198000000000066fe600000000000184f2000000000000434140000000000007384000000000000057c000000000000000c00000000000000000411aa2d32e0000001d5b1c1e980000000c5c764e4200000004cc91b49000000001b0834c30000000008706037800000000243ed15c000000000801372c00000000015c67d2000000000028ffb0000000000002c58600000000000012f0000000000000001400000000000000000027a5bcef2000000013561ec88000000008dd55e9a000000003c6a61c100000000178d3dc600000000083bb378000000000282669c0000000000a3f03d000000000020f452000000000004bae0000000000000686e00000000000003d100000000000000060000000000000000
  | 96 => 0x138214f300000000098067d39000000004595ab4e000000001d959765800000000b819a21000000000402c53a000000000137cd4800000000004f302d80000000000fd06a0000000000023fbf000000000000310600000000000001c5800000000000000300000000000000000009cdce3d4400000004c6f2678000000002300c8b8c00000000ee40e374000000005cbb9ed000000000205aba400000000009d62f5800000000028085ac0000000000802dac000000000012480000000000000190140000000000000e84000000000000001800000000000000000005f4a92ca00000000323610be0000000019072464000000000bad918e000000000507f43e0000000001f6ec3c0000000000ad79f8000000000032edf000000000000c06d2000000000002159200000000000039ac00000000000002ca00000000000000060000000000000000002704aacdb00000001301661fc000000008b32ecf8000000003b3041a70000000017062464000000000807060c0000000002703f5c00000000009e9c0800000000001fb1e50000000000048300000000000000627c000000000000039100000000000000060000000000000000
  | 97 => 0x1020f3b993000000074421d11b800000030e6ebb48000000012f605d9e000000006aa111fd00000000213805bf0000000008e4908c0000000001f4e70e800000000054b5c3000000000009e370800000000000a8f4000000000000046d0000000000000005000000000000000000816f95a98c0000003a53fb347c000000188aed7ab400000009851269780000000358fcca70000000010b25dcb80000000047932908000000000fc4118c0000000002abac6400000000005003e40000000000055d8c000000000000245000000000000000280000000000000000004f11b6b2c0000000268e2900a000000011abe3b6600000000786854d6000000002eeccb64000000001066122c0000000004ff0dc400000000014648160000000000419034000000000009688e000000000000cfd2000000000000079e000000000000000c000000000000000001fcc6b1c990000000e4f4232870000000602e2c3770000000253c3655200000000d1027c880000000040f7ae2e000000001157e7a60000000003cd6b770000000000a3dd73000000000013044100000000000142d90000000000000878000000000000000a0000000000000000
  | 98 => 0x18bb68fd800000000d10b86d8000000006880d3100000000030ec9b980000000015289b1800000000084c86700000000002e09c200000000000d98810000000000033b35800000000000903a8000000000000f9f00000000000000be800000000000000180000000000000000000109bb35c000000000991946000000000054257580000000002bbbb64000000000153f444000000000098052000000000003d3dd00000000000158be400000000000650ac0000000000016d80000000000000378800000000000004440000000000000014000000000000000000009091c3200000000053d75480000000002e6f8a8000000000185aa1a0000000000bf6382000000000056bc2000000000002387a000000000000cc59a000000000003da22000000000000e8080000000000002568000000000000032a000000000000001200000000000000001a3fd944d68000000aecde179c4000000437a555b6c00000017d2669ec2000000078d3d63910000000218fe6398000000007e5a01200000000017fe0ecb00000000036b14560000000000533e040000000000044f9400000000000014c0000000000000000f0000000000000000
  | 99 => 0x13efb87c5000000009ba874340000000047687544800000001e712a62800000000be119990000000004287b52000000000144fc430000000000531f09000000000010c2b70000000000026a9a00000000000035b580000000000001fb800000000000000300000000000000000000bffc6b900000000065358c280000000032797714000000001790b7c4000000000a28ba940000000003f84d5000000000015eda8800000000006718f40000000000185e2800000000000439d800000000000074ec00000000000005a4000000000000000c0000000000000000000613f8d1200000000334f838400000000199d4638000000000bf8d56e00000000052aef9e000000000205b7c80000000000b30570000000000034b30600000000000c7a7a0000000000022abc0000000000003be800000000000002de00000000000000060000000000000000000040e94c30000000002555a26000000000147ac5e0000000000a9e9650000000000525399000000000024b24400000000000eb9d4000000000005281300000000000180af00000000000056620000000000000d0a000000000000010100000000000000050000000000000000
  | 100 => 0x1057c32737000000075f28cc8d800000031afb1bf60000000134cd0b66000000006cc7ebfd0000000021fca69b0000000009220b3000000000020519cc8000000000581a2700000000000a66e6800000000000b50e00000000000004e1000000000000000500000000000000000009f03269f800000004d930a648000000023937102c00000000f2925e4c000000005e9d8c08000000002119b780000000000a1951c8000000000294b8a00000000000851ac80000000000132bc8000000000001a9c40000000000000fb4000000000000001800000000000000000050193ecec000000027198385c000000011f1a217c000000007a737548000000002fcf673c0000000010bf214800000000051e026800000000014f73d8000000000043c07c000000000009cab4000000000000da740000000000000818000000000000000c00000000000000000002ff3ca470000000019478d5c000000000c9b9a8c0000000005e30533000000000289c8630000000000fdfce0000000000057b980000000000019ccb70000000000061b97000000000001100c0000000000001d9c000000000000017300000000000000030000000000000000
  | 101 => 0x13cd1b049000000009a7e892a0000000046d06b66800000001e2845ea800000000bc0b0a100000000041b59120000000001404037000000000051a7d8000000000010644300000000000258f000000000000033a380000000000001e1800000000000000300000000000000000009dc73441000000004ceaac7600000000233e5bab000000000f00c4a4c000000005d8132280000000020a799e00000000009f085c0000000000288289c000000000081f0c000000000001292c000000000000197700000000000000ecc00000000000000180000000000000000000602540da0000000032afccb000000000194757c4000000000bcd4a220000000005166afe0000000001fce1b00000000000afa058000000000033937a00000000000c2ce20000000000021b2000000000000039ec00000000000002c20000000000000006000000000000000000030c0286c0000000019b9798a000000000cd7c5af000000000600cb2b00000000029760bd000000000103983c000000000059bf5e00000000001a68010000000000063eda00000000000114ee0000000000001db9000000000000016700000000000000030000000000000000
  | 102 => 0x10354f232c000000074e12de860000000312ff6ae90000000131533bbf000000006b6416e300000000217c76940000000008f98b2a0000000001fa4dbb000000000055cfb600000000000a0ce2000000000000aca7000000000000048f0000000000000005000000000000000000824ee45e6c0000003ac09e911000000018bc96646c000000099a273ed000000003612c3e70000000010dfef6800000000048702cb8000000000ffc20880000000002b6df040000000000519d10000000000005809400000000000025800000000000000028000000000000000004013f768920000001cda3d1b0e0000000c20f9626a00000004b306866000000001a6760eb80000000083787894000000002326010c0000000007b87fb200000000014d91ae000000000026d99a000000000002971e00000000000011840000000000000014000000000000000000274a1d57600000001325b33d2000000008c51cd86000000003bb4b73700000000173e84ce00000000081cba540000000002779c340000000000a0ba7f0000000000202eee00000000000497fe00000000000064a200000000000003a700000000000000060000000000000000
  | 103 => 0x13fb5c239000000009c039ae6000000004791ce36000000001e822fbd000000000be73f9700000000042a4ff40000000001455e7400000000005323c7000000000010bc4500000000000267b2000000000000352200000000000001f1000000000000000300000000000000000009f4ea84d800000004db82df00000000023a455fcc00000000f3016bcc000000005ec51c08000000002124f030000000000a1b3a480000000002947ab8000000000084c6280000000000130b10000000000001a3640000000000000f4400000000000000180000000000000000000631b100e00000000345a5f88000000001a2b67d0000000000c3fecee00000000054bdd2600000000021391800000000000b82a5000000000003650ae00000000000ce0ce0000000000023c280000000000003d6000000000000002de000000000000000600000000000000001a660d9594b000000afdfdf9aa400000043ece848e600000017fe851672000000079c9ef537000000021dbd5348000000007f9b8f6c000000001843de3a000000000376b493000000000054935c00000000000465ba0000000000001542000000000000000f0000000000000000
  | 104 => 0xfdb9f2701000000072263308800000002feff69740000000128d1a541800000006814b50d000000002054e40400000000089fbd080000000001e3819780000000005147390000000000096acc0000000000009fcc00000000000004398000000000000005000000000000000006a0b6a1a0dc000002c2b917d718000001110c981124000000607ece4e580000001ea0b7f71c000000088536ebb0000000020233f7e80000000061e154f4000000000dfde91c0000000001566088000000000011dd3c00000000000056e0000000000000003c0000000000000000041869636640000001d8e92ba480000000c736dce5800000004d60ad73c00000001b4107b94000000008834eb90000000002495c0d0000000000815c7d40000000001602a640000000000297b78000000000002cf48000000000000134c000000000000001400000000000000000203b506dc80000000e85096e0b000000061b604df2000000025e1cfc3600000000d501a8c20000000042594b220000000011c22fc00000000003e814f90000000000a91d48000000000013c08900000000000152aa0000000000000904000000000000000a0000000000000000
  | 105 => 0x2ab4f444e0020000106b8bfa72a8000005d0ef751040000001de83e301a800000088c901af2a00000021dd81bf500000000700112eb0000000012576ffc000000000232f57e20000000002b8fa1800000000001becf00000000000005ff8000000000000002a000000000000000019deb82ba51000000ac0f8f43600000004251d5d4bc000000175ef3547b000000076476b77b000000020c388c48000000007ae9a1a000000000173b6a8900000000034a261500000000004f745800000000000412fc0000000000001387000000000000000f0000000000000000
  | _ => 0

def packedClass (u : ℕ) : ℕ := (packedClassPack (u / 4) >>> (877*(u % 4))) % 1007641851683931820587806291420968258893675472328417820220872324040744595635843008946260940337480903424595632540239579541935629958157893251896932560850028184716008537290582817399466548302510149103210893455908181007667595468047259786297601506742546990374638711734272

def packedRow (u : ℕ) := packedClass (stateIndex u)

def tab (n u : ℕ) : ℕ := (packedRow u >>> (64 * n)) % 1125899906842624

def radixSum : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | d+1, f => f 0 + 18446744073709551616 * radixSum d (fun i => f (i+1))

theorem radix_inj (d : ℕ) (f g : ℕ → ℕ)
    (hf : ∀ i < d, f i < 18446744073709551616) (hg : ∀ i < d, g i < 18446744073709551616)
    (h : radixSum d f = radixSum d g) : ∀ i < d, f i = g i := by
  induction d generalizing f g with
  | zero => omega
  | succ d ih =>
    simp only [radixSum] at h
    have f0 := hf 0 (by omega)
    have g0 := hg 0 (by omega)
    have e0 : f 0 = g 0 := by omega
    intro i hi
    cases i with
    | zero => exact e0
    | succ i => exact ih (fun j => f (j+1)) (fun j => g (j+1))
                    (fun j hj => hf _ (by omega)) (fun j hj => hg _ (by omega)) (by omega) i (by omega)

theorem radix_sum {α : Type} (s : Finset α) (d : ℕ) (f : α → ℕ → ℕ) :
    radixSum d (fun i => ∑ w ∈ s, f w i) = ∑ w ∈ s, radixSum d (f w) := by
  induction d generalizing f with
  | zero => simp [radixSum]
  | succ d ih =>
    simp only [radixSum, sum_add_distrib, ← mul_sum]
    rw [ih (fun w i => f w (i+1))]

def subsetSum : ℕ → ℕ → ℕ → (ℕ → ℕ) → ℕ
  | 0, _, b, f => f b
  | k+1, u, b, f => subsetSum k u b f +
      if u.testBit k then subsetSum k u (b+2^k) f else 0

theorem subHigh {k i : ℕ} (hi : i < 2^k) (u : ℕ) :
    ((2^k+i) &&& u = 2^k+i) ↔ u.testBit k = true ∧ (i &&& u) = i := by
  have hlt : (i &&& u) < 2^k := Nat.and_le_left.trans_lt hi
  rw [Nat.add_comm (2^k) i, ← Nat.or_two_pow_eq_add_of_lt hi, Nat.and_or_distrib_right,
    Nat.land_comm (2^k) u, Nat.and_two_pow]
  cases h : u.testBit k <;>
    simp [Nat.or_two_pow_eq_add_of_lt hi, Nat.or_two_pow_eq_add_of_lt hlt] <;> omega

theorem subsetSum_eq (k u b : ℕ) (f : ℕ → ℕ) :
    (∑ i ∈ range (2^k), if i &&& u = i then f (b+i) else 0) = subsetSum k u b f := by
  induction k generalizing b with
  | zero => simp [subsetSum]
  | succ k ih =>
    rw [pow_succ, Nat.mul_two, sum_range_add, ih, subsetSum]
    congr 1
    by_cases h : u.testBit k = true
    · rw [if_pos h, ← ih]
      apply sum_congr rfl
      intro i hi
      simp only [subHigh (mem_range.mp hi), h, true_and, Nat.add_assoc]
    · rw [if_neg h]
      apply sum_eq_zero
      intro i hi
      rw [if_neg (fun q => h ((subHigh (mem_range.mp hi) u).mp q).1)]

theorem subsetSum_step (u : Fin 4096) (f : ℕ → ℕ) :
    (∑ w ∈ subs u, if compc w.val u.val = true then f w.val else 0) =
      subsetSum 12 u.val 0 (fun w => if compc w u.val = true then f w else 0) := by
  unfold subs
  rw [sum_filter]
  simp only [beq_iff_eq]
  rw [← subsetSum_eq]
  simp only [Nat.zero_add]
  exact Fin.sum_univ_eq_sum_range (fun w => if w &&& u.val = w then
    (if compc w u.val = true then f w else 0) else 0) 4096


def parents (u : Fin 4096) := (subs u).filter (fun w => compc w.val u.val = true)

def inputRow (u : ℕ) := packedRow u % (2 ^ 832)
def outputRow (u : ℕ) := packedRow u >>> 64

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 65536 in
theorem packInput : ∀ u : Fin 4096, radixSum 13 (fun i => tab i u.val) = inputRow u.val := by
  apply blocks
  intro j
  fin_cases j <;> decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 65536 in
theorem packOutput : ∀ u : Fin 4096, radixSum 13 (fun i => tab (i+1) u.val) = outputRow u.val := by
  apply blocks
  intro j
  fin_cases j <;> decide +kernel

set_option maxRecDepth 65536 in
theorem step0 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*0+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step1 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*1+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step2 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*2+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step3 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*3+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step4 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*4+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step5 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*5+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step6 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*6+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step7 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*7+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step8 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*8+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step9 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*9+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step10 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*10+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step11 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*11+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step12 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*12+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step13 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*13+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step14 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*14+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step15 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*15+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step16 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*16+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step17 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*17+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step18 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*18+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step19 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*19+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step20 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*20+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step21 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*21+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step22 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*22+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step23 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*23+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step24 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*24+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step25 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*25+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step26 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*26+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step27 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*27+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step28 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*28+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step29 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*29+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step30 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*30+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step31 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*31+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step32 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*32+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step33 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*33+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step34 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*34+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step35 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*35+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step36 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*36+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step37 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*37+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step38 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*38+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step39 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*39+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step40 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*40+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step41 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*41+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step42 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*42+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step43 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*43+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step44 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*44+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step45 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*45+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step46 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*46+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step47 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*47+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step48 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*48+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step49 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*49+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step50 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*50+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step51 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*51+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step52 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*52+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step53 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*53+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step54 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*54+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step55 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*55+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step56 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*56+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step57 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*57+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step58 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*58+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step59 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*59+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step60 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*60+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step61 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*61+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step62 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*62+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step63 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*63+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxHeartbeats 1600000 in
theorem packedStep (u : Fin 4096) : subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by
  let i : Fin 64 := ⟨u.val % 64, Nat.mod_lt _ (by decide)⟩
  have hu := u.isLt
  generalize h : u.val / 64 = j
  have hj : j < 64 := by omega
  interval_cases j

  · have e : u = ⟨64*0+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step0 i

  · have e : u = ⟨64*1+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step1 i

  · have e : u = ⟨64*2+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step2 i

  · have e : u = ⟨64*3+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step3 i

  · have e : u = ⟨64*4+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step4 i

  · have e : u = ⟨64*5+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step5 i

  · have e : u = ⟨64*6+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step6 i

  · have e : u = ⟨64*7+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step7 i

  · have e : u = ⟨64*8+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step8 i

  · have e : u = ⟨64*9+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step9 i

  · have e : u = ⟨64*10+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step10 i

  · have e : u = ⟨64*11+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step11 i

  · have e : u = ⟨64*12+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step12 i

  · have e : u = ⟨64*13+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step13 i

  · have e : u = ⟨64*14+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step14 i

  · have e : u = ⟨64*15+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step15 i

  · have e : u = ⟨64*16+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step16 i

  · have e : u = ⟨64*17+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step17 i

  · have e : u = ⟨64*18+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step18 i

  · have e : u = ⟨64*19+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step19 i

  · have e : u = ⟨64*20+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step20 i

  · have e : u = ⟨64*21+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step21 i

  · have e : u = ⟨64*22+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step22 i

  · have e : u = ⟨64*23+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step23 i

  · have e : u = ⟨64*24+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step24 i

  · have e : u = ⟨64*25+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step25 i

  · have e : u = ⟨64*26+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step26 i

  · have e : u = ⟨64*27+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step27 i

  · have e : u = ⟨64*28+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step28 i

  · have e : u = ⟨64*29+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step29 i

  · have e : u = ⟨64*30+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step30 i

  · have e : u = ⟨64*31+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step31 i

  · have e : u = ⟨64*32+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step32 i

  · have e : u = ⟨64*33+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step33 i

  · have e : u = ⟨64*34+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step34 i

  · have e : u = ⟨64*35+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step35 i

  · have e : u = ⟨64*36+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step36 i

  · have e : u = ⟨64*37+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step37 i

  · have e : u = ⟨64*38+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step38 i

  · have e : u = ⟨64*39+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step39 i

  · have e : u = ⟨64*40+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step40 i

  · have e : u = ⟨64*41+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step41 i

  · have e : u = ⟨64*42+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step42 i

  · have e : u = ⟨64*43+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step43 i

  · have e : u = ⟨64*44+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step44 i

  · have e : u = ⟨64*45+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step45 i

  · have e : u = ⟨64*46+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step46 i

  · have e : u = ⟨64*47+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step47 i

  · have e : u = ⟨64*48+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step48 i

  · have e : u = ⟨64*49+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step49 i

  · have e : u = ⟨64*50+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step50 i

  · have e : u = ⟨64*51+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step51 i

  · have e : u = ⟨64*52+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step52 i

  · have e : u = ⟨64*53+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step53 i

  · have e : u = ⟨64*54+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step54 i

  · have e : u = ⟨64*55+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step55 i

  · have e : u = ⟨64*56+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step56 i

  · have e : u = ⟨64*57+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step57 i

  · have e : u = ⟨64*58+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step58 i

  · have e : u = ⟨64*59+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step59 i

  · have e : u = ⟨64*60+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step60 i

  · have e : u = ⟨64*61+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step61 i

  · have e : u = ⟨64*62+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step62 i

  · have e : u = ⟨64*63+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step63 i

theorem transfer (u : Fin 4096) (n : ℕ) (hn : n < 13) : (∑ w ∈ subs u, if compc w.val u.val = true then tab n w.val else 0) = tab (n+1) u.val := by
  have pack : radixSum 13 (fun i => ∑ w ∈ parents u, tab i w.val) =
      radixSum 13 (fun i => tab (i+1) u.val) := by
    rw [radix_sum (parents u) 13 (fun w i => tab i w.val),packOutput]
    simp only [packInput,parents,sum_filter,subsetSum_step]
    exact packedStep u
  have bound (i w : ℕ) : tab i w ≤ 1125899906842624 := (Nat.mod_lt _ (by decide)).le
  have sumBound (i : ℕ) : (∑ w ∈ parents u, tab i w.val) < 18446744073709551616 := by
    have h := sum_le_sum (s:=parents u) (fun w _ => bound i w.val)
    have hc : (parents u).card ≤ 4096 := by simpa only [Fintype.card_fin] using (parents u).card_le_univ
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at h
    omega
  have h := radix_inj _ _ _ (fun i _ => sumBound i) (fun i _ => (bound (i+1) u.val).trans_lt (by decide)) pack n hn
  simpa only [parents,sum_filter] using h

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 65536 in
theorem start : ∀ u : Fin 4096, G 0 u = tab 0 u.val := by
  apply blocks
  intro j
  fin_cases j <;> decide +kernel

theorem table_ok (n : ℕ) (hn : n ≤ 13) : ∀ u : Fin 4096, G n u = tab n u.val := by
  induction n with
  | zero => exact start
  | succ n ih =>
    intro u
    rw [G_succ]
    simp only [ih (by omega)]
    exact transfer u n (by omega)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 65536 in
theorem baseCert : ∀ u : Fin 4096, tab 13 u.val + 78 * tab 11 u.val + 715 * tab 9 u.val + 1716 * tab 7 u.val + 1287 * tab 5 u.val + 286 * tab 3 u.val + 13 * tab 1 u.val = 13 * tab 12 u.val + 286 * tab 10 u.val + 1287 * tab 8 u.val + 1716 * tab 6 u.val + 715 * tab 4 u.val + 78 * tab 2 u.val + tab 0 u.val := by
  apply blocks
  intro j
  fin_cases j <;> decide +kernel

theorem recurrenceVec (m : ℕ) : ∀ u : Fin 4096, G (m + 13) u + 78 * G (m + 11) u + 715 * G (m + 9) u + 1716 * G (m + 7) u + 1287 * G (m + 5) u + 286 * G (m + 3) u + 13 * G (m + 1) u = 13 * G (m + 12) u + 286 * G (m + 10) u + 1287 * G (m + 8) u + 1716 * G (m + 6) u + 715 * G (m + 4) u + 78 * G (m + 2) u + G m u := by
  induction m with
  | zero =>
    intro u
    simp only [Nat.zero_add]
    simpa only [table_ok 0 (by decide) u, table_ok 1 (by decide) u, table_ok 2 (by decide) u, table_ok 3 (by decide) u, table_ok 4 (by decide) u, table_ok 5 (by decide) u, table_ok 6 (by decide) u, table_ok 7 (by decide) u, table_ok 8 (by decide) u, table_ok 9 (by decide) u, table_ok 10 (by decide) u, table_ok 11 (by decide) u, table_ok 12 (by decide) u, table_ok 13 (by decide) u] using (show G 13 u + 78 * G 11 u + 715 * G 9 u + 1716 * G 7 u + 1287 * G 5 u + 286 * G 3 u + 13 * G 1 u = 13 * G 12 u + 286 * G 10 u + 1287 * G 8 u + 1716 * G 6 u + 715 * G 4 u + 78 * G 2 u + G 0 u from by
      rw [table_ok 0 (by decide) u, table_ok 1 (by decide) u, table_ok 2 (by decide) u, table_ok 3 (by decide) u, table_ok 4 (by decide) u, table_ok 5 (by decide) u, table_ok 6 (by decide) u, table_ok 7 (by decide) u, table_ok 8 (by decide) u, table_ok 9 (by decide) u, table_ok 10 (by decide) u, table_ok 11 (by decide) u, table_ok 12 (by decide) u, table_ok 13 (by decide) u]
      exact baseCert u)
  | succ m ih =>
    intro u
    rw [show m + 1 + 1 = (m+1)+1 by omega, show m + 1 + 2 = (m+2)+1 by omega, show m + 1 + 3 = (m+3)+1 by omega, show m + 1 + 4 = (m+4)+1 by omega, show m + 1 + 5 = (m+5)+1 by omega, show m + 1 + 6 = (m+6)+1 by omega, show m + 1 + 7 = (m+7)+1 by omega, show m + 1 + 8 = (m+8)+1 by omega, show m + 1 + 9 = (m+9)+1 by omega, show m + 1 + 10 = (m+10)+1 by omega, show m + 1 + 11 = (m+11)+1 by omega, show m + 1 + 12 = (m+12)+1 by omega, show m + 1 + 13 = (m+13)+1 by omega]
    rw [G_succ (m + 13), G_succ (m + 12), G_succ (m + 11), G_succ (m + 10), G_succ (m + 9), G_succ (m + 8), G_succ (m + 7), G_succ (m + 6), G_succ (m + 5), G_succ (m + 4), G_succ (m + 3), G_succ (m + 2), G_succ (m + 1), G_succ m]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs
    · exact ih w
    · rfl

theorem recurrence (n : ℕ) (hn : 13 < n) : (a n : ℤ) = 13 * a (n - 1) - 78 * a (n - 2) + 286 * a (n - 3) - 715 * a (n - 4) + 1287 * a (n - 5) - 1716 * a (n - 6) + 1716 * a (n - 7) - 1287 * a (n - 8) + 715 * a (n - 9) - 286 * a (n - 10) + 78 * a (n - 11) - 13 * a (n - 12) + a (n - 13) := by
  obtain ⟨m,rfl⟩ : ∃ m, n = m + 13 := ⟨n-13,by omega⟩
  have h : (a (m + 13) : ℤ) + 78 * (a (m + 11) : ℤ) + 715 * (a (m + 9) : ℤ) + 1716 * (a (m + 7) : ℤ) + 1287 * (a (m + 5) : ℤ) + 286 * (a (m + 3) : ℤ) + 13 * (a (m + 1) : ℤ) = 13 * (a (m + 12) : ℤ) + 286 * (a (m + 10) : ℤ) + 1287 * (a (m + 8) : ℤ) + 1716 * (a (m + 6) : ℤ) + 715 * (a (m + 4) : ℤ) + 78 * (a (m + 2) : ℤ) + (a m : ℤ) := by
    simp only [a_eq_G]
    exact_mod_cast recurrenceVec m 4095
  simp only [show m+13-1 = (m + 12) by omega, show m+13-2 = (m + 11) by omega, show m+13-3 = (m + 10) by omega, show m+13-4 = (m + 9) by omega, show m+13-5 = (m + 8) by omega, show m+13-6 = (m + 7) by omega, show m+13-7 = (m + 6) by omega, show m+13-8 = (m + 5) by omega, show m+13-9 = (m + 4) by omega, show m+13-10 = (m + 3) by omega, show m+13-11 = (m + 2) by omega, show m+13-12 = (m + 1) by omega, show m+13-13 = m by omega]
  linarith

open PowerSeries in
set_option maxRecDepth 16000 in
set_option maxHeartbeats 1500000 in
theorem generating : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 13 =
      X * (21 + 12011 * X + 757010 * X ^ 2 + 11894854 * X ^ 3 + 66128388 * X ^ 4
        + 153231228 * X ^ 5 + 158628614 * X ^ 6 + 73421530 * X ^ 7 + 14037031 * X ^ 8
        + 882297 * X ^ 9 + 8616 * X ^ 10) := by
  let F : ℕ → ℚ := (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  change PowerSeries.mk F * _ = _

  have lhs : PowerSeries.mk F * (1-X)^13 = C 1 * (PowerSeries.mk F * X ^ 0) - C 13 * (PowerSeries.mk F * X ^ 1) + C 78 * (PowerSeries.mk F * X ^ 2) - C 286 * (PowerSeries.mk F * X ^ 3) + C 715 * (PowerSeries.mk F * X ^ 4) - C 1287 * (PowerSeries.mk F * X ^ 5) + C 1716 * (PowerSeries.mk F * X ^ 6) - C 1716 * (PowerSeries.mk F * X ^ 7) + C 1287 * (PowerSeries.mk F * X ^ 8) - C 715 * (PowerSeries.mk F * X ^ 9) + C 286 * (PowerSeries.mk F * X ^ 10) - C 78 * (PowerSeries.mk F * X ^ 11) + C 13 * (PowerSeries.mk F * X ^ 12) - C 1 * (PowerSeries.mk F * X ^ 13) := by simp only [map_one,map_ofNat]; ring
  have rhs : (X * (21 + 12011 * X + 757010 * X ^ 2 + 11894854 * X ^ 3 + 66128388 * X ^ 4
        + 153231228 * X ^ 5 + 158628614 * X ^ 6 + 73421530 * X ^ 7 + 14037031 * X ^ 8
        + 882297 * X ^ 9 + 8616 * X ^ 10) : ℚ⟦X⟧) = C 21 * X ^ 1 + C 12011 * X ^ 2 + C 757010 * X ^ 3 + C 11894854 * X ^ 4 + C 66128388 * X ^ 5 + C 153231228 * X ^ 6 + C 158628614 * X ^ 7 + C 73421530 * X ^ 8 + C 14037031 * X ^ 9 + C 882297 * X ^ 10 + C 8616 * X ^ 11 := by simp only [map_ofNat]; ring
  rw [lhs,rhs]
  ext k
  simp only [map_sub,map_add,coeff_C_mul_X_pow]
  simp only [coeff_C_mul,coeff_mul_X_pow',coeff_mk]

  by_cases hk : k < 14
  ·

    have v1 : a 1 = 21 := (a_eq_G 1).trans ((table_ok 1 (by decide) 4095).trans (by decide +kernel))

    have v2 : a 2 = 12284 := (a_eq_G 2).trans ((table_ok 2 (by decide) 4095).trans (by decide +kernel))

    have v3 : a 3 = 915064 := (a_eq_G 3).trans ((table_ok 3 (by decide) 4095).trans (by decide +kernel))

    have v4 : a 4 = 22838540 := (a_eq_G 4).trans ((table_ok 4 (by decide) 4095).trans (by decide +kernel))

    have v5 : a 5 = 295152625 := (a_eq_G 5).trans ((table_ok 5 (by decide) 4095).trans (by decide +kernel))

    have v6 : a 6 = 2461761504 := (a_eq_G 6).trans ((table_ok 6 (by decide) 4095).trans (by decide +kernel))

    have v7 : a 7 = 15032948568 := (a_eq_G 7).trans ((table_ok 7 (by decide) 4095).trans (by decide +kernel))

    have v8 : a 8 = 72725094312 := (a_eq_G 8).trans ((table_ok 8 (by decide) 4095).trans (by decide +kernel))

    have v9 : a 9 = 293743941525 := (a_eq_G 9).trans ((table_ok 9 (by decide) 4095).trans (by decide +kernel))

    have v10 : a 10 = 1027603529940 := (a_eq_G 10).trans ((table_ok 10 (by decide) 4095).trans (by decide +kernel))

    have v11 : a 11 = 3197464381472 := (a_eq_G 11).trans ((table_ok 11 (by decide) 4095).trans (by decide +kernel))

    have v12 : a 12 = 9027047995732 := (a_eq_G 12).trans ((table_ok 12 (by decide) 4095).trans (by decide +kernel))

    have v13 : a 13 = 23478340317185 := (a_eq_G 13).trans ((table_ok 13 (by decide) 4095).trans (by decide +kernel))

    interval_cases k

    · simp only [F, if_pos (show 0 ≤ 0 by decide), if_neg (show ¬ 1 ≤ 0 by decide), if_neg (show ¬ 2 ≤ 0 by decide), if_neg (show ¬ 3 ≤ 0 by decide), if_neg (show ¬ 4 ≤ 0 by decide), if_neg (show ¬ 5 ≤ 0 by decide), if_neg (show ¬ 6 ≤ 0 by decide), if_neg (show ¬ 7 ≤ 0 by decide), if_neg (show ¬ 8 ≤ 0 by decide), if_neg (show ¬ 9 ≤ 0 by decide), if_neg (show ¬ 10 ≤ 0 by decide), if_neg (show ¬ 11 ≤ 0 by decide), if_neg (show ¬ 12 ≤ 0 by decide), if_neg (show ¬ 13 ≤ 0 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 1 by decide), if_pos (show 1 ≤ 1 by decide), if_neg (show ¬ 2 ≤ 1 by decide), if_neg (show ¬ 3 ≤ 1 by decide), if_neg (show ¬ 4 ≤ 1 by decide), if_neg (show ¬ 5 ≤ 1 by decide), if_neg (show ¬ 6 ≤ 1 by decide), if_neg (show ¬ 7 ≤ 1 by decide), if_neg (show ¬ 8 ≤ 1 by decide), if_neg (show ¬ 9 ≤ 1 by decide), if_neg (show ¬ 10 ≤ 1 by decide), if_neg (show ¬ 11 ≤ 1 by decide), if_neg (show ¬ 12 ≤ 1 by decide), if_neg (show ¬ 13 ≤ 1 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 2 by decide), if_pos (show 1 ≤ 2 by decide), if_pos (show 2 ≤ 2 by decide), if_neg (show ¬ 3 ≤ 2 by decide), if_neg (show ¬ 4 ≤ 2 by decide), if_neg (show ¬ 5 ≤ 2 by decide), if_neg (show ¬ 6 ≤ 2 by decide), if_neg (show ¬ 7 ≤ 2 by decide), if_neg (show ¬ 8 ≤ 2 by decide), if_neg (show ¬ 9 ≤ 2 by decide), if_neg (show ¬ 10 ≤ 2 by decide), if_neg (show ¬ 11 ≤ 2 by decide), if_neg (show ¬ 12 ≤ 2 by decide), if_neg (show ¬ 13 ≤ 2 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 3 by decide), if_pos (show 1 ≤ 3 by decide), if_pos (show 2 ≤ 3 by decide), if_pos (show 3 ≤ 3 by decide), if_neg (show ¬ 4 ≤ 3 by decide), if_neg (show ¬ 5 ≤ 3 by decide), if_neg (show ¬ 6 ≤ 3 by decide), if_neg (show ¬ 7 ≤ 3 by decide), if_neg (show ¬ 8 ≤ 3 by decide), if_neg (show ¬ 9 ≤ 3 by decide), if_neg (show ¬ 10 ≤ 3 by decide), if_neg (show ¬ 11 ≤ 3 by decide), if_neg (show ¬ 12 ≤ 3 by decide), if_neg (show ¬ 13 ≤ 3 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2, v3]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 4 by decide), if_pos (show 1 ≤ 4 by decide), if_pos (show 2 ≤ 4 by decide), if_pos (show 3 ≤ 4 by decide), if_pos (show 4 ≤ 4 by decide), if_neg (show ¬ 5 ≤ 4 by decide), if_neg (show ¬ 6 ≤ 4 by decide), if_neg (show ¬ 7 ≤ 4 by decide), if_neg (show ¬ 8 ≤ 4 by decide), if_neg (show ¬ 9 ≤ 4 by decide), if_neg (show ¬ 10 ≤ 4 by decide), if_neg (show ¬ 11 ≤ 4 by decide), if_neg (show ¬ 12 ≤ 4 by decide), if_neg (show ¬ 13 ≤ 4 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2, v3, v4]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 5 by decide), if_pos (show 1 ≤ 5 by decide), if_pos (show 2 ≤ 5 by decide), if_pos (show 3 ≤ 5 by decide), if_pos (show 4 ≤ 5 by decide), if_pos (show 5 ≤ 5 by decide), if_neg (show ¬ 6 ≤ 5 by decide), if_neg (show ¬ 7 ≤ 5 by decide), if_neg (show ¬ 8 ≤ 5 by decide), if_neg (show ¬ 9 ≤ 5 by decide), if_neg (show ¬ 10 ≤ 5 by decide), if_neg (show ¬ 11 ≤ 5 by decide), if_neg (show ¬ 12 ≤ 5 by decide), if_neg (show ¬ 13 ≤ 5 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2, v3, v4, v5]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 6 by decide), if_pos (show 1 ≤ 6 by decide), if_pos (show 2 ≤ 6 by decide), if_pos (show 3 ≤ 6 by decide), if_pos (show 4 ≤ 6 by decide), if_pos (show 5 ≤ 6 by decide), if_pos (show 6 ≤ 6 by decide), if_neg (show ¬ 7 ≤ 6 by decide), if_neg (show ¬ 8 ≤ 6 by decide), if_neg (show ¬ 9 ≤ 6 by decide), if_neg (show ¬ 10 ≤ 6 by decide), if_neg (show ¬ 11 ≤ 6 by decide), if_neg (show ¬ 12 ≤ 6 by decide), if_neg (show ¬ 13 ≤ 6 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2, v3, v4, v5, v6]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 7 by decide), if_pos (show 1 ≤ 7 by decide), if_pos (show 2 ≤ 7 by decide), if_pos (show 3 ≤ 7 by decide), if_pos (show 4 ≤ 7 by decide), if_pos (show 5 ≤ 7 by decide), if_pos (show 6 ≤ 7 by decide), if_pos (show 7 ≤ 7 by decide), if_neg (show ¬ 8 ≤ 7 by decide), if_neg (show ¬ 9 ≤ 7 by decide), if_neg (show ¬ 10 ≤ 7 by decide), if_neg (show ¬ 11 ≤ 7 by decide), if_neg (show ¬ 12 ≤ 7 by decide), if_neg (show ¬ 13 ≤ 7 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2, v3, v4, v5, v6, v7]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 8 by decide), if_pos (show 1 ≤ 8 by decide), if_pos (show 2 ≤ 8 by decide), if_pos (show 3 ≤ 8 by decide), if_pos (show 4 ≤ 8 by decide), if_pos (show 5 ≤ 8 by decide), if_pos (show 6 ≤ 8 by decide), if_pos (show 7 ≤ 8 by decide), if_pos (show 8 ≤ 8 by decide), if_neg (show ¬ 9 ≤ 8 by decide), if_neg (show ¬ 10 ≤ 8 by decide), if_neg (show ¬ 11 ≤ 8 by decide), if_neg (show ¬ 12 ≤ 8 by decide), if_neg (show ¬ 13 ≤ 8 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2, v3, v4, v5, v6, v7, v8]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 9 by decide), if_pos (show 1 ≤ 9 by decide), if_pos (show 2 ≤ 9 by decide), if_pos (show 3 ≤ 9 by decide), if_pos (show 4 ≤ 9 by decide), if_pos (show 5 ≤ 9 by decide), if_pos (show 6 ≤ 9 by decide), if_pos (show 7 ≤ 9 by decide), if_pos (show 8 ≤ 9 by decide), if_pos (show 9 ≤ 9 by decide), if_neg (show ¬ 10 ≤ 9 by decide), if_neg (show ¬ 11 ≤ 9 by decide), if_neg (show ¬ 12 ≤ 9 by decide), if_neg (show ¬ 13 ≤ 9 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2, v3, v4, v5, v6, v7, v8, v9]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 10 by decide), if_pos (show 1 ≤ 10 by decide), if_pos (show 2 ≤ 10 by decide), if_pos (show 3 ≤ 10 by decide), if_pos (show 4 ≤ 10 by decide), if_pos (show 5 ≤ 10 by decide), if_pos (show 6 ≤ 10 by decide), if_pos (show 7 ≤ 10 by decide), if_pos (show 8 ≤ 10 by decide), if_pos (show 9 ≤ 10 by decide), if_pos (show 10 ≤ 10 by decide), if_neg (show ¬ 11 ≤ 10 by decide), if_neg (show ¬ 12 ≤ 10 by decide), if_neg (show ¬ 13 ≤ 10 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 11 by decide), if_pos (show 1 ≤ 11 by decide), if_pos (show 2 ≤ 11 by decide), if_pos (show 3 ≤ 11 by decide), if_pos (show 4 ≤ 11 by decide), if_pos (show 5 ≤ 11 by decide), if_pos (show 6 ≤ 11 by decide), if_pos (show 7 ≤ 11 by decide), if_pos (show 8 ≤ 11 by decide), if_pos (show 9 ≤ 11 by decide), if_pos (show 10 ≤ 11 by decide), if_pos (show 11 ≤ 11 by decide), if_neg (show ¬ 12 ≤ 11 by decide), if_neg (show ¬ 13 ≤ 11 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 12 by decide), if_pos (show 1 ≤ 12 by decide), if_pos (show 2 ≤ 12 by decide), if_pos (show 3 ≤ 12 by decide), if_pos (show 4 ≤ 12 by decide), if_pos (show 5 ≤ 12 by decide), if_pos (show 6 ≤ 12 by decide), if_pos (show 7 ≤ 12 by decide), if_pos (show 8 ≤ 12 by decide), if_pos (show 9 ≤ 12 by decide), if_pos (show 10 ≤ 12 by decide), if_pos (show 11 ≤ 12 by decide), if_pos (show 12 ≤ 12 by decide), if_neg (show ¬ 13 ≤ 12 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false]
      rw [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 13 by decide), if_pos (show 1 ≤ 13 by decide), if_pos (show 2 ≤ 13 by decide), if_pos (show 3 ≤ 13 by decide), if_pos (show 4 ≤ 13 by decide), if_pos (show 5 ≤ 13 by decide), if_pos (show 6 ≤ 13 by decide), if_pos (show 7 ≤ 13 by decide), if_pos (show 8 ≤ 13 by decide), if_pos (show 9 ≤ 13 by decide), if_pos (show 10 ≤ 13 by decide), if_pos (show 11 ≤ 13 by decide), if_pos (show 12 ≤ 13 by decide), if_pos (show 13 ≤ 13 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false]
      rw [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13]
      norm_num

  · have eqr := recurrence (k+0) (by omega)
    have hq : (a (k+0) : ℚ) = 13 * a (k+0-1) - 78 * a (k+0-2) + 286 * a (k+0-3) - 715 * a (k+0-4) + 1287 * a (k+0-5) - 1716 * a (k+0-6) + 1716 * a (k+0-7) - 1287 * a (k+0-8) + 715 * a (k+0-9) - 286 * a (k+0-10) + 78 * a (k+0-11) - 13 * a (k+0-12) + a (k+0-13) := by exact_mod_cast eqr
    simp only [F, if_pos (show 0 ≤ k by omega), if_pos (show 1 ≤ k by omega), if_pos (show 2 ≤ k by omega), if_pos (show 3 ≤ k by omega), if_pos (show 4 ≤ k by omega), if_pos (show 5 ≤ k by omega), if_pos (show 6 ≤ k by omega), if_pos (show 7 ≤ k by omega), if_pos (show 8 ≤ k by omega), if_pos (show 9 ≤ k by omega), if_pos (show 10 ≤ k by omega), if_pos (show 11 ≤ k by omega), if_pos (show 12 ≤ k by omega), if_pos (show 13 ≤ k by omega), if_neg (show k ≠ 1 by omega), if_neg (show k ≠ 2 by omega), if_neg (show k ≠ 3 by omega), if_neg (show k ≠ 4 by omega), if_neg (show k ≠ 5 by omega), if_neg (show k ≠ 6 by omega), if_neg (show k ≠ 7 by omega), if_neg (show k ≠ 8 by omega), if_neg (show k ≠ 9 by omega), if_neg (show k ≠ 10 by omega), if_neg (show k ≠ 11 by omega), Nat.sub_zero, if_neg (show k ≠ 0 by omega), if_neg (show k-1 ≠ 0 by omega), if_neg (show k-2 ≠ 0 by omega), if_neg (show k-3 ≠ 0 by omega), if_neg (show k-4 ≠ 0 by omega), if_neg (show k-5 ≠ 0 by omega), if_neg (show k-6 ≠ 0 by omega), if_neg (show k-7 ≠ 0 by omega), if_neg (show k-8 ≠ 0 by omega), if_neg (show k-9 ≠ 0 by omega), if_neg (show k-10 ≠ 0 by omega), if_neg (show k-11 ≠ 0 by omega), if_neg (show k-12 ≠ 0 by omega), if_neg (show k-13 ≠ 0 by omega)]
    simp only [Nat.add_zero] at hq
    linarith

end OMA.WindowCount

theorem OMA.solution : type_of% @OMA.S_oeis_a250065.main := ⟨OMA.WindowCount.generating, OMA.WindowCount.recurrence⟩

