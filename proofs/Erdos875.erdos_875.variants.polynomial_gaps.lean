import FormalConjectures.ErdosProblems.«875»

/-! Encode the number of selected elements from each block in its sum. -/
open Finset Filter Erdos875
namespace Blocks875
def block (K Q : ℕ) : Finset ℕ := (range K).image fun j => (K^2+j)*Q
lemma block_card (K Q : ℕ) (hq : 0<Q) : (block K Q).card=K := by
  unfold block
  rw [card_image_of_injective,card_range]
  intro a b h
  exact Nat.add_left_cancel (Nat.eq_of_mul_eq_mul_right hq h)

def digit (Q : ℕ) (S : Finset ℕ) := ∑ x ∈ S, x/Q
lemma block_digit {K Q : ℕ} (hk : 0<K) (hq : 0<Q) {S : Finset ℕ} (hs : S ⊆ block K Q) :
    (∑ x ∈ S, x) = digit Q S * Q ∧
    S.card*K^2 ≤ digit Q S ∧ digit Q S < (S.card+1)*K^2 ∧ digit Q S < 2*K^3 := by
  have hx {x} (h : x ∈ S) : ∃ j < K, (K^2+j)*Q=x := by
    simpa [block] using hs h
  have hc := card_le_card hs
  rw [block_card _ _ hq] at hc
  have hl : S.card*K^2 ≤ digit Q S := by
    calc
      _ = ∑ _x ∈ S, K^2 := by simp
      _ ≤ _ := by
        apply sum_le_sum; intro x hx'
        obtain ⟨j,hj,rfl⟩ := hx hx'
        simp [Nat.mul_div_cancel _ hq]
  have hu : digit Q S ≤ S.card*(K^2+(K-1)) := by
    calc
      _ ≤ ∑ _x ∈ S, (K^2+(K-1)) := by
        apply sum_le_sum; intro x hx'
        obtain ⟨j,hj,rfl⟩ := hx hx'
        simpa [Nat.mul_div_cancel _ hq] using (show K^2+j ≤ K^2+(K-1) by omega)
      _ = _ := by simp
  have ht : S.card*(K-1)<K^2 := calc
    _ ≤ K*(K-1) := Nat.mul_le_mul_right _ hc
    _ < K^2 := by have : K-1+1=K := by omega
                  nlinarith [congrArg (fun x : ℕ => K*x) this]
  refine ⟨?_,hl,by nlinarith,?_⟩
  · unfold digit
    rw [sum_mul]; apply sum_congr rfl; intro x hx'
    obtain ⟨j,hj,rfl⟩ := hx hx'
    rw [Nat.mul_div_cancel _ hq]
  · have := Nat.mul_le_mul_right (K^2) hc
    have : K^2 ≤ K*K^2 := Nat.le_mul_of_pos_left _ hk
    nlinarith

variable (K Q : ℕ → ℕ)
def blocksBelow : ℕ → Finset ℕ
  | 0 => ∅
  | i+1 => blocksBelow i ∪ block (K i) (Q i)
def points : Set ℕ := {x | ∃ i, x ∈ blocksBelow K Q i}

lemma prefix_mono : Monotone (blocksBelow K Q) := monotone_nat_of_le_succ fun i => subset_union_left
lemma bounded_prefix {S : Finset ℕ} (hs : ↑S ⊆ points K Q) : ∃ i, S ⊆ blocksBelow K Q i := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0,empty_subset _⟩
  | @insert x S _ ih =>
    obtain ⟨i,hi⟩ := ih (fun z hz => hs (mem_insert_of_mem hz))
    obtain ⟨j,hj⟩ := hs (mem_insert_self x S)
    refine ⟨max i j, insert_subset (prefix_mono K Q (le_max_right ..) hj) (hi.trans (prefix_mono K Q (le_max_left ..)))⟩

variable (hk : ∀ i, 0<K i) (hq : ∀ i, 0<Q i)
    (hstep : ∀ i, 2*(K i)^3 * Q i ≤ Q (i+1))
include hk hq hstep in
lemma prefix_code (i : ℕ) :
    (∀ S ⊆ blocksBelow K Q i, ∑ x ∈ S, x < Q i) ∧
    ∀ S ⊆ blocksBelow K Q i, ∀ T ⊆ blocksBelow K Q i,
      (∑ x ∈ S, x) = ∑ x ∈ T, x → S.card=T.card := by
  induction i with
  | zero =>
    simpa [blocksBelow] using hq 0
  | succ i ih =>
    let B := block (K i) (Q i)
    have splitS (S : Finset ℕ) (hs : S ⊆ blocksBelow K Q (i+1)) :
        S \ B ⊆ blocksBelow K Q i := by
      intro x hx
      exact (mem_union.mp (hs (mem_sdiff.mp hx).1)).resolve_right (mem_sdiff.mp hx).2
    have spec (S : Finset ℕ) (hs : S ⊆ blocksBelow K Q (i+1)) :
        (∑ x ∈ S, x) = (∑ x ∈ S \ B, x) + digit (Q i) (S ∩ B)*Q i ∧
        (∑ x ∈ S \ B, x) < Q i ∧
        (S ∩ B).card*(K i)^2 ≤ digit (Q i) (S ∩ B) ∧
        digit (Q i) (S ∩ B) < ((S ∩ B).card+1)*(K i)^2 ∧
        digit (Q i) (S ∩ B) < 2*(K i)^3 := by
      obtain ⟨h₁,h₂,h₃,h₄⟩ := block_digit (hk i) (hq i) (S := S ∩ B) inter_subset_right
      refine ⟨?_,ih.1 _ (splitS S hs),h₂,h₃,h₄⟩
      rw [← h₁, ← sum_union (disjoint_sdiff_inter S B), sdiff_union_inter]
    constructor
    · intro S hs
      obtain ⟨h,hl,_,_,hh⟩ := spec S hs
      have hb := Nat.mul_le_mul_right (Q i) (show digit (Q i) (S ∩ B)+1 ≤ 2*(K i)^3 from hh)
      nlinarith [hstep i]
    · intro S hs T ht he
      obtain ⟨hS,lS,sS,tS,_⟩ := spec S hs
      obtain ⟨hT,lT,sT,tT,_⟩ := spec T ht
      rw [hS,hT] at he
      have hmod := congrArg (fun x => x % Q i) he
      simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt lS, Nat.mod_eq_of_lt lT] at hmod
      have hdig : digit (Q i) (S ∩ B) = digit (Q i) (T ∩ B) := Nat.eq_of_mul_eq_mul_right (hq i) (by omega)
      have hcard : (S ∩ B).card = (T ∩ B).card := by
        apply le_antisymm <;> by_contra! hh
        · have := Nat.mul_le_mul_right ((K i)^2) (show (T ∩ B).card+1 ≤ (S ∩ B).card by omega)
          omega
        · have := Nat.mul_le_mul_right ((K i)^2) (show (S ∩ B).card+1 ≤ (T ∩ B).card by omega)
          omega
      have hlow := ih.2 _ (splitS S hs) _ (splitS T ht) hmod
      have := card_sdiff_add_card_inter S B
      have := card_sdiff_add_card_inter T B
      omega

include hk hq hstep in
lemma admissible : IsAdmissible (points K Q) := by
  intro r _ s _ hrs
  apply Set.disjoint_left.mpr
  rintro x ⟨S,hS,hSr,hSx⟩ ⟨T,hT,hTs,hTx⟩
  obtain ⟨i,hi⟩ := bounded_prefix K Q hS
  obtain ⟨j,hj⟩ := bounded_prefix K Q hT
  have he := (prefix_code K Q hk hq hstep (max i j)).2 S (hi.trans (prefix_mono K Q (le_max_left ..)))
    T (hj.trans (prefix_mono K Q (le_max_right ..))) (hSx.trans hTx.symm)
  exact hrs (hSr.symm.trans (he.trans hTs))
end Blocks875

namespace Blocks875
lemma block_mem (K Q : ℕ → ℕ) (i : ℕ) {x : ℕ} (hx : x ∈ block (K i) (Q i)) :
    x ∈ points K Q := ⟨i+1,mem_union_right _ hx⟩

lemma infinite_points (K Q : ℕ → ℕ) (hq : ∀ i, 0<Q i) (hun : ∀ n, ∃ i, n < K i) :
    (points K Q).Infinite := by
  intro hf
  obtain ⟨i,hi⟩ := hun hf.toFinset.card
  have hsub : block (K i) (Q i) ⊆ hf.toFinset := fun x hx => hf.mem_toFinset.mpr (block_mem K Q i hx)
  have := card_le_card hsub
  rw [block_card _ _ (hq i)] at this
  omega

lemma nth_block (K Q : ℕ → ℕ) (i n : ℕ) (hq : 0<Q i) (hn : n<K i) :
    Nat.nth (· ∈ points K Q) n ≤ 2*(K i)^2*Q i := by
  classical
  have sub : block (K i) (Q i) ⊆ (range (2*(K i)^2*Q i+1)).filter (· ∈ points K Q) := by
    intro x hx
    refine mem_filter.mpr ⟨mem_range.mpr ?_,block_mem K Q i hx⟩
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
    have hj' := mem_range.mp hj
    have : K i ≤ (K i)^2 := by nlinarith [Nat.one_le_pow 2 (K i) (by omega : 0 < K i)]
    exact Nat.lt_succ_of_le (Nat.mul_le_mul_right _ (by omega))
  have hc := card_le_card sub
  rw [block_card _ _ hq, ← Nat.count_eq_card_filter_range] at hc
  exact Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count (hn.trans_le hc))

lemma parameters (c : ℝ) (hc : 5+2*Real.sqrt 6<c) :
    ∃ u v : ℕ → ℕ, (∀ i, 1+3*v i+u i ≤ u (i+1)) ∧
    (∀ i, ((1+2*v (i+1)+u (i+1) : ℕ):ℝ) ≤ c*v i) ∧
    (∀ n, ∃ i, n < 2^(v i)) := by
  let s := Real.sqrt 6
  let r := 1+s/2
  have hs : s^2=6 := Real.sq_sqrt (by norm_num)
  have hsp : 0 ≤ s := Real.sqrt_nonneg _
  have hr : 2 ≤ r := by dsimp [r]; nlinarith
  have hc0 : 0<c := by dsimp [s] at *; linarith
  let B := s+(c-(5+2*s))/(2*r)
  have hr0 : 0<r := by linarith
  have hδ : 0 < (c-(5+2*s))/(2*r) := div_pos (sub_pos.mpr hc) (by positivity)
  have hB : 0<B := by dsimp [B]; linarith
  have hsep : 0<B*(r-1)-3 := by
    dsimp [B]
    have : s*(r-1)=3 := by dsimp [r]; nlinarith
    nlinarith [mul_pos hδ (show 0<r-1 by linarith)]
  have hg : 0<c-(B+2)*r := by
    have h1 : (s+2)*r=5+2*s := by dsimp [r]; nlinarith
    have h2 := div_mul_cancel₀ (c-(5+2*s)) (show 2*r≠0 by positivity)
    dsimp [B]; nlinarith
  let D := 1+2/(B*(r-1)-3)+(c+1)/(c-(B+2)*r)
  have hD : 1≤D := by dsimp [D]; linarith [div_pos (by norm_num : (0:ℝ)<2) hsep,div_pos (show 0<c+1 by linarith) hg]
  have hd1 : 2 ≤ D*(B*(r-1)-3) := by
    have hl : 2/(B*(r-1)-3) ≤ D := by dsimp [D]; linarith [div_pos (show 0<c+1 by linarith) hg]
    exact (div_le_iff₀ hsep).mp hl
  have hd2 : c+1 ≤ D*(c-(B+2)*r) := by
    have hl : (c+1)/(c-(B+2)*r) ≤ D := by dsimp [D]; linarith [div_pos (by norm_num : (0:ℝ)<2) hsep]
    exact (div_le_iff₀ hg).mp hl
  let x (i : ℕ) := D*r^i
  have hDx (i) : D ≤ x i := le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by linarith : (1:ℝ) ≤ r))
  have hx (i) : 0≤x i := by linarith [hDx i]
  have hx' (i) : x (i+1)=x i*r := by dsimp [x]; rw [pow_succ]; ring
  let u (i : ℕ) := ⌊B*x i⌋₊
  let v (i : ℕ) := ⌊x i⌋₊
  have hu (i) : (u i : ℝ) ≤ B*x i := Nat.floor_le (mul_nonneg hB.le (hx i))
  have hv (i) : (v i : ℝ) ≤ x i := Nat.floor_le (hx i)
  have hV (i) : x i < (v i : ℝ)+1 := Nat.lt_floor_add_one _
  refine ⟨u,v,?_,?_,?_⟩
  · intro i
    change _ ≤ ⌊B*x (i+1)⌋₊
    apply Nat.le_floor
    push_cast
    rw [hx']
    nlinarith only [hu i,hv i,hd1,mul_le_mul_of_nonneg_right (hDx i) hsep.le]
  · intro i
    push_cast
    have h₁ := hu (i+1)
    have h₂ := hv (i+1)
    rw [hx'] at h₁ h₂
    nlinarith only [h₁,h₂,mul_lt_mul_of_pos_left (hV i) hc0,hd2,mul_le_mul_of_nonneg_right (hDx i) hg.le]
  · intro n
    refine ⟨n,(Nat.lt_two_pow_self (n:=n)).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_floor ?_))⟩
    have ht : (n:ℝ) ≤ (2:ℝ)^n := by exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
    exact ht.trans ((pow_le_pow_left₀ (by norm_num) hr n).trans (le_mul_of_one_le_left (by positivity) hD))

end Blocks875

open Blocks875 in
theorem OMA.solution : type_of% @Erdos875.erdos_875.variants.polynomial_gaps := by
  intro c hc
  obtain ⟨u,v,hs,hg,hun⟩ := parameters c hc
  let K (i : ℕ) := 2^(v i)
  let Q (i : ℕ) := 2^(u i)
  have hk (i) : 0<K i := Nat.two_pow_pos _
  have hq (i) : 0<Q i := Nat.two_pow_pos _
  have step (i) : 2*(K i)^3*Q i ≤ Q (i+1) := by
    dsimp [K,Q]
    convert Nat.pow_le_pow_right (by decide : 0 < 2) (hs i) using 1
    rw [pow_add,pow_add,Nat.mul_comm 3 (v i),pow_mul]; ring
  let A := points K Q
  refine ⟨A,infinite_points K Q hq hun,admissible K Q hk hq step,?_⟩
  filter_upwards [eventually_ge_atTop (K 0)] with n hn
  obtain ⟨i,hi₁,hi₂⟩ : ∃ i, K i ≤ n ∧ n < K (i+1) := by
    let j := Nat.find (hun n)
    have hj : n < K j := Nat.find_spec (hun n)
    cases he : j with
    | zero => rw [he] at hj; omega
    | succ i =>
      refine ⟨i,le_of_not_gt ?_,he ▸ hj⟩
      exact Nat.find_min (hun n) (show i < j by omega)
  have hc0 : 0≤c := by linarith [Real.sqrt_nonneg 6]
  calc
    (gap A n : ℝ) ≤ Nat.nth (· ∈ A) n := by exact_mod_cast Nat.sub_le _ _
    _ ≤ (2*(K (i+1))^2*Q (i+1) : ℕ) := by exact_mod_cast nth_block K Q (i+1) n (hq _) hi₂
    _ = (2:ℝ)^((1+2*v (i+1)+u (i+1) : ℕ):ℝ) := by
      rw [Real.rpow_natCast]; push_cast; dsimp [K,Q]; push_cast; rw [pow_add,pow_add,Nat.mul_comm 2 (v (i+1)),pow_mul]; ring
    _ ≤ (2:ℝ)^(c*v i) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (hg i)
    _ = (K i : ℝ)^c := by dsimp [K]; push_cast; rw [mul_comm c, Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
    _ ≤ (n:ℝ)^c := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hi₁) hc0
