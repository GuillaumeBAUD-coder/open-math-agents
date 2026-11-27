import FormalConjectures.ErdosProblems.«775»
open Finset SimpleGraph
namespace Spencer

/-- A control for each ordinary block, and a separate family of rows for the small cliques. -/
inductive Vertex (k h : ℕ) (w : Fin k → ℕ)
  | ctrl (i : Fin k)
  | base (i : Fin k) (j : Fin (w i + 1))
  | row (i : Fin h) (j : Fin (2 * i.val + 2))
  | star
  | z (b : Bool)
  deriving DecidableEq, Fintype

variable {k h : ℕ} {w : Fin k → ℕ}

def compatible (high : Fin h ↪ Fin k) (v t : Vertex k h w) : Prop :=
  match v, t with
  | .ctrl i, .base j _ | .base j _, .ctrl i => i ≠ j
  | .ctrl i, .row j _ | .row j _, .ctrl i => i ∉ Set.range high ∨ i = high j
  | .ctrl i, .z _ | .z _, .ctrl i => i ∈ Set.range high
  | .row _ j, .z b | .z b, .row _ j => b = false ∨ 0 < j.val
  | .star, .row .. | .row .., .star | .z _, .z _ | .z _, .star | .star, .z _
  | .z _, .base .. | .base .., .z _ => False
  | _, _ => True

def graph (high : Fin h ↪ Fin k) : SimpleGraph (Vertex k h w) where
  Adj v t := v ≠ t ∧ compatible high v t
  symm := by
    constructor
    rintro v t ⟨hne, ht⟩
    refine ⟨hne.symm, ?_⟩
    cases v <;> cases t <;> simp_all [compatible, eq_comm]
  loopless := ⟨fun v hv => hv.1 rfl⟩

lemma witness {V : Type} [Fintype V] (G : SimpleGraph V) (p : V → Prop) [DecidablePred p]
    (cl : ∀ x, p x → ∀ y, p y → x ≠ y → G.Adj x y)
    (ma : ∀ x, ¬ p x → ∃ y, p y ∧ ¬ G.Adj x y) :
    (univ.filter p).card ∈ G.cliqueSizes := by
  refine ⟨_, ⟨?_, ?_⟩, rfl⟩
  · intro x hx y hy hne
    exact cl x (mem_filter.mp hx).2 y (mem_filter.mp hy).2 hne
  · intro T hT hsub x hx
    simp only [mem_filter, mem_univ, true_and]
    by_contra hn
    obtain ⟨y, hy, hxy⟩ := ma x hn
    exact hxy (hT hx (hsub (mem_filter.mpr ⟨mem_univ _,hy⟩)) (fun he => hn (he ▸ hy)))

/-- Choose one control or its whole ordinary block at each index, together with the star. -/
def middle (S : Finset (Fin k)) : Vertex k h w → Prop
  | .ctrl i => i ∈ S
  | .base i _ => i ∉ S
  | .star => True
  | _ => False

/-- Keep all rows and choose controls only from the low indices. -/
def upper (S : Finset (Fin k)) : Vertex k h w → Prop
  | .ctrl i => i ∈ S
  | .base i _ => i ∉ S
  | .row .. => True
  | _ => False

/-- A single high control and its row, with one of the two special vertices. -/
def lower (high : Fin h ↪ Fin k) (r : Fin h) (b : Bool) : Vertex k h w → Prop
  | .ctrl i => i = high r
  | .row i j => i = r ∧ (b = false ∨ 0 < j.val)
  | .z a => a = b
  | _ => False

instance (S : Finset (Fin k)) : DecidablePred (middle (w := w) (h := h) S) :=
  fun v => by cases v <;> simp only [middle] <;> infer_instance

instance (S : Finset (Fin k)) : DecidablePred (upper (w := w) (h := h) S) :=
  fun v => by cases v <;> simp only [upper] <;> infer_instance

instance (high : Fin h ↪ Fin k) (r : Fin h) (b : Bool) : DecidablePred (lower (w := w) high r b) :=
  fun v => by cases v <;> simp only [lower] <;> infer_instance

lemma middle_mem (high : Fin h ↪ Fin k) (S : Finset (Fin k)) :
    (univ.filter (middle (h := h) (w := w) S)).card ∈ (graph (w := w) high).cliqueSizes := by
  classical
  apply witness
  · intro x hx y hy hne
    refine ⟨hne, ?_⟩
    cases x <;> cases y <;> simp_all [middle, compatible] <;> grind
  · intro x hx
    cases x with
    | ctrl i => exact ⟨.base i 0, hx, by simp [graph, compatible]⟩
    | base i j => exact ⟨.ctrl i, by simpa [middle] using hx, by simp [graph, compatible]⟩
    | row i j => exact ⟨.star, trivial, by simp [graph, compatible]⟩
    | z b => exact ⟨.star, trivial, by simp [graph, compatible]⟩
    | star => exact (hx trivial).elim

lemma upper_mem (high : Fin h ↪ Fin k) (S : Finset (Fin k)) (low : ∀ i ∈ S, i ∉ Set.range high)
    (r : Fin h) :
    (univ.filter (upper (h := h) (w := w) S)).card ∈ (graph (w := w) high).cliqueSizes := by
  classical
  apply witness
  · intro x hx y hy hne
    refine ⟨hne, ?_⟩
    cases x <;> cases y <;> simp_all [upper, compatible] <;> grind
  · intro x hx
    cases x with
    | ctrl i => exact ⟨.base i 0, hx, by simp [graph, compatible]⟩
    | base i j => exact ⟨.ctrl i, by simpa [upper] using hx, by simp [graph, compatible]⟩
    | star => exact ⟨.row r 0, trivial, by simp [graph, compatible]⟩
    | row i j => exact (hx trivial).elim
    | z b => exact ⟨.base (high r) 0, fun hi => low _ hi ⟨r,rfl⟩, by simp [graph, compatible]⟩

lemma lower_mem (high : Fin h ↪ Fin k) (r : Fin h) (b : Bool)
 :
    (univ.filter (lower (w := w) high r b)).card ∈ (graph (w := w) high).cliqueSizes := by
  classical
  apply witness
  · intro x hx y hy hne
    refine ⟨hne, ?_⟩
    cases x <;> cases y <;> simp_all [lower, compatible]
  · intro x hx
    cases x with
    | ctrl i =>
      by_cases hi : i ∈ Set.range high
      · exact ⟨.row r ⟨1, by omega⟩, ⟨rfl, Or.inr Nat.zero_lt_one⟩, fun hc => hc.2.elim (fun hn => hn hi) hx⟩
      · exact ⟨.z b, rfl, fun hc => hi hc.2⟩
    | base i j => exact ⟨.z b, rfl, by simp [graph, compatible]⟩
    | star => exact ⟨.z b, rfl, by simp [graph, compatible]⟩
    | z a => exact ⟨.z b, rfl, by simp [graph, compatible]⟩
    | row i j =>
      by_cases hi : i = r
      · exact ⟨.z b, rfl, by simpa [graph, compatible, lower, hi] using hx⟩
      · exact ⟨.ctrl (high r), rfl, by simp [graph, compatible, Ne.symm hi]⟩

lemma sumV (f : Vertex k h w → ℕ) :
    ∑ v, f v = (∑ i, f (.ctrl i)) + (∑ i, ∑ j, f (.base i j)) +
    (∑ i, ∑ j, f (.row i j)) + f .star + f (.z true) + f (.z false) := by
  rw [← (Vertex.proxyTypeEquiv k h w).sum_comp f]
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_unique, Fintype.sum_bool]
  ac_rfl

lemma vertex_card : Fintype.card (Vertex k h w) =
    2*k + (∑ i, w i) + (∑ i : Fin h, (2*i.val+2)) + 3 := by
  have := sumV (fun _ : Vertex k h w => 1)
  simp [Finset.sum_add_distrib] at this ⊢
  omega

lemma countV (p : Vertex k h w → Prop) [DecidablePred p] : (univ.filter p).card = ∑ x, if p x then 1 else 0 := by
  simpa using (Finset.sum_boole (R := ℕ) p univ).symm

lemma blocks (S : Finset (Fin k)) :
    ((∑ i, if i ∈ S then 1 else 0) + ∑ i, ∑ _j : Fin (w i + 1), if i ∉ S then 1 else 0) =
    k + ∑ i ∈ Sᶜ, w i := by
  have hh : Sᶜ = univ.filter (fun i => i ∉ S) := by ext; simp
  rw [hh, sum_filter, ← sum_add_distrib]
  calc
    _ = ∑ i, (1 + if i ∉ S then w i else 0) := by
      apply sum_congr rfl
      intro i _
      by_cases hi : i ∈ S <;> simp [hi, add_comm]
    _ = _ := by simp [sum_add_distrib]

lemma mid_card (S : Finset (Fin k)) :
    (univ.filter (middle (h := h) (w := w) S)).card = k + (∑ i ∈ Sᶜ, w i) + 1 := by
  classical
  rw [countV, sumV]
  simp [middle]
  simpa using blocks (w := w) S

lemma up_card (S : Finset (Fin k)) :
    (univ.filter (upper (h := h) (w := w) S)).card =
    k + (∑ i ∈ Sᶜ, w i) + ∑ i : Fin h, (2*i.val+2) := by
  classical
  rw [countV, sumV]
  simp [upper]
  simpa using blocks (w := w) S

lemma low_card (high : Fin h ↪ Fin k) (r : Fin h) (b : Bool) :
    (univ.filter (lower (w := w) high r b)).card = 2*r.val + (if b then 3 else 4) := by
  classical
  rw [countV, sumV]
  cases b <;> simp [lower]
  · omega
  have hz (x : Fin h) : (univ.filter (fun j : Fin (2 * x.val + 2) => x = r ∧ 0 < j)).card =
        if x = r then 2*x.val+1 else 0 := by
      split_ifs with hx
      · have he : (univ.filter (fun j : Fin (2*x.val+2) => x = r ∧ 0 < j)) = univ.erase 0 := by
          ext j
          simp [hx, Fin.lt_def, Nat.pos_iff_ne_zero]
        rw [he, card_erase_of_mem (mem_univ _)]
        simp
      · simp [hx]
  simp_rw [hz]
  simp
  omega

/-- Capacity of the first m binary weights, capped at the available total W. -/
def cap (W m : ℕ) := min W (2^m - 1)
def weight (W i : ℕ) := min (2^i) (W - (2^i-1))

lemma cap_step (W m : ℕ) : cap W (m+1) = cap W m + weight W m := by
  simp only [cap, weight, pow_succ]
  have : 0 < 2^m := pow_pos (by decide) _
  omega

lemma weight_bound (W m : ℕ) : weight W m ≤ cap W m + 1 := by
  unfold weight cap
  have : 0 < 2^m := pow_pos (by decide) _
  omega

lemma sum_weight (W k : ℕ) : (∑ i : Fin k, weight W i.val) = cap W k := by
  induction k with
  | zero => simp [cap]
  | succ k ih => rw [Fin.sum_univ_castSucc, cap_step]; simpa using congrArg (· + weight W k) ih

lemma represent {k : ℕ} (W m : ℕ) (hm : m ≤ k) (d : ℕ) (hd : d ≤ cap W m) :
    ∃ S : Finset (Fin k), (∀ i ∈ S, i.val < m) ∧ (∑ i ∈ S, weight W i.val) = d := by
  induction m generalizing d with
  | zero =>
    have : d = 0 := by simpa [cap] using hd
    exact ⟨∅, by simp, by simp [this]⟩
  | succ m ih =>
    by_cases hh : d ≤ cap W m
    · obtain ⟨S,hS,hs⟩ := ih (by omega) d hh
      exact ⟨S,fun i hi => Nat.lt_succ_of_lt (hS i hi),hs⟩
    · have hstep := cap_step W m
      have hb := weight_bound W m
      obtain ⟨S,hS,hs⟩ := ih (by omega) (d-weight W m) (by omega)
      let x : Fin k := ⟨m,by omega⟩
      have hnot : x ∉ S := fun hx => (Nat.lt_irrefl m) (hS x hx)
      refine ⟨insert x S, ?_, ?_⟩
      · intro i hi
        rcases mem_insert.mp hi with rfl | hi
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (hS i hi)
      · rw [sum_insert hnot, hs]
        change weight W m + _ = _
        omega

def lastHalf (h : ℕ) : Fin h ↪ Fin (2*h) where
  toFun i := ⟨h+i.val, by omega⟩
  inj' := by intro a b hab; apply Fin.ext; have := congrArg Fin.val hab; dsimp at this; omega

def rows (h : ℕ) := ∑ i : Fin h, (2*i.val+2)
def wt (h W : ℕ) (i : Fin (2*h)) := weight W i.val

lemma consecutive (h W : ℕ) (hh : 1 ≤ h) (hW : W < 2^(2*h))
    (hA : rows h ≤ cap W h) (d : ℕ) (hd : 3 ≤ d) (hu : d ≤ 2*h+W+rows h) :
    d ∈ (graph (w := wt h W) (lastHalf h)).cliqueSizes := by
  have full : cap W (2*h) = W := by unfold cap; omega
  by_cases small : d ≤ 2*h+2
  · let r : Fin h := ⟨(d-3)/2, by omega⟩
    let b : Bool := decide (d % 2 = 1)
    have H := lower_mem (w := wt h W) (lastHalf h) r b
    rw [low_card] at H
    convert H using 1
    dsimp [r,b]
    simp only [decide_eq_true_eq]
    split_ifs <;> omega
  by_cases mid : d ≤ 2*h+W+1
  · obtain ⟨S,_,hs⟩ := represent (k := 2*h) W (2*h) le_rfl (d-(2*h+1)) (by omega)
    have H := middle_mem (w := wt h W) (lastHalf h) Sᶜ
    rw [mid_card,compl_compl] at H
    change (∑ i ∈ S, wt h W i) = _ at hs
    rwa [hs, show 2*h + (d-(2*h+1)) + 1 = d by omega] at H
  · obtain ⟨S,hl,hs⟩ := represent (k := 2*h) W h (by omega) (2*h+W+rows h-d) (by omega)
    have low (i : Fin (2*h)) (hi : i ∈ S) : i ∉ Set.range (lastHalf h) := by
      rintro ⟨j,rfl⟩
      have ht := hl _ hi
      change h+j.val < h at ht
      omega
    have H := upper_mem (w := wt h W) (lastHalf h) S low ⟨0,by omega⟩
    rw [up_card] at H
    change (∑ i ∈ S, wt h W i) = _ at hs
    have total := sum_add_sum_compl S (wt h W)
    rw [show (∑ i, wt h W i) = W from (sum_weight W _).trans full] at total
    change 2*h + (∑ i ∈ Sᶜ, wt h W i) + rows h ∈ _ at H
    rwa [show 2*h + (∑ i ∈ Sᶜ, wt h W i) + rows h = d by omega] at H

lemma rows_eq (h : ℕ) : rows h = h*(h+1) := by
  induction h with
  | zero => simp [rows]
  | succ h ih =>
    unfold rows at *
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    ring

lemma plenty {h : ℕ} (hh : 10 ≤ h) : 2*rows h + 4*h + 4 ≤ 2^h := by
  rw [rows_eq]
  induction h, hh using Nat.le_induction with
  | base => decide
  | succ h hh ih => rw [pow_succ]; nlinarith

lemma transport {α β : Type} (G : SimpleGraph α) (e : α ≃ β) :
    G.cliqueSizes ⊆ (G.map e.toEmbedding).cliqueSizes := by
  classical
  rintro d ⟨S,hS,rfl⟩
  refine ⟨S.map e.toEmbedding, ⟨hS.1.finsetMap, ?_⟩, card_map _⟩
  intro T hT hsub
  let U := T.map e.symm.toEmbedding
  have hUT : U.map e.toEmbedding = T := by ext; simp [U]
  have hU : G.IsClique (U : Set α) := by
    rw [← hUT, coe_map] at hT
    exact isClique_map_image_iff.mp hT
  have hSU : S ⊆ U := by
    intro x hx
    have hy := hsub (mem_map.mpr ⟨x,hx,rfl⟩)
    simpa [U] using hy
  have heq := hS.2 hU hSU
  rw [← hUT]
  exact map_subset_map.mpr heq

lemma many {n h W : ℕ} (hh : 1 ≤ h) (hW : W < 2^(2*h)) (hA : rows h ≤ cap W h)
    (size : n = 4*h+W+rows h+3) :
    ∃ G : SimpleGraph (Fin n), n ≤ G.cliqueSizes.ncard + 2*h+5 := by
  classical
  let G := graph (w := wt h W) (lastHalf h)
  have full : cap W (2*h) = W := by unfold cap; omega
  have hc : Fintype.card (Vertex (2*h) h (wt h W)) = n := by
    rw [vertex_card]
    change 2*(2*h) + (∑ i : Fin (2*h), weight W i.val) + rows h + 3 = n
    rw [sum_weight, full]; omega
  let e := Fintype.equivFinOfCardEq hc
  refine ⟨G.map e.toEmbedding, ?_⟩
  have sub : Set.Icc 3 (2*h+W+rows h) ⊆ (G.map e.toEmbedding).cliqueSizes :=
    fun d hd => transport G e (consecutive h W hh hW hA d hd.1 hd.2)
  have fin : (G.map e.toEmbedding).cliqueSizes.Finite := by
    apply Set.Finite.subset (Set.finite_Iic n)
    rintro d ⟨S,_,rfl⟩
    simpa using S.card_le_univ
  have hb := Set.ncard_le_ncard sub fin
  rw [← Finset.coe_Icc, Set.ncard_coe_finset, Nat.card_Icc] at hb
  omega
end Spencer

open Spencer in
theorem OMA.solution : type_of% @Erdos775.erdos_775.variants.spencer := by
  refine ⟨2^40, ?_⟩
  intro n
  let l := Nat.log 2 n
  have logarithm := Real.natLog_le_logb n 2
  norm_num only [Nat.cast_ofNat] at logarithm
  change (l : ℝ) ≤ _ at logarithm
  have up := Nat.lt_pow_succ_log_self (b := 2) (by decide) n
  change n < 2^(l+1) at up
  by_cases small : l < 40
  · refine ⟨⊥, ?_⟩
    have hn : n ≤ 2^40 := up.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
    have hn' : (n : ℝ) ≤ 2^40 := by exact_mod_cast hn
    have := Nat.cast_nonneg (α := ℝ) l
    have := Nat.cast_nonneg (α := ℝ) (SimpleGraph.cliqueSizes (⊥ : SimpleGraph (Fin n))).ncard
    linarith
  let h := l/2+1
  let W := n-(4*h+rows h+3)
  have rangeh : l+1 ≤ 2*h ∧ 2*h ≤ l+2 ∧ 10 ≤ h ∧ h ≤ l := by dsimp [h]; omega
  have lower : 2^h ≤ n := by
    have hn : n ≠ 0 := by intro he; simp [he,l] at small
    exact (Nat.pow_le_pow_right (by decide) rangeh.2.2.2).trans (Nat.pow_log_le_self _ hn)
  have upper : n < 2^(2*h) := up.trans_le (Nat.pow_le_pow_right (by decide) rangeh.1)
  have budget := plenty rangeh.2.2.1
  have size : n = 4*h+W+rows h+3 := by dsimp [W]; omega
  have hw : W < 2^(2*h) := by omega
  have cover : rows h ≤ cap W h := by unfold cap; omega
  obtain ⟨G,hG⟩ := many (by omega) hw cover size
  refine ⟨G, ?_⟩
  have hG' : (n : ℝ) ≤ (G.cliqueSizes.ncard : ℝ) + 2*(h : ℝ)+5 := by exact_mod_cast hG
  have hh' : 2*(h : ℝ) ≤ (l : ℝ)+2 := by exact_mod_cast rangeh.2.1
  linarith
