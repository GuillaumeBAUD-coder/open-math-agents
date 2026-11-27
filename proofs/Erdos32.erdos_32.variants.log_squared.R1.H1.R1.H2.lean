import OMAReductions.R_Erdos32_erdos_32_variants_log_squared_R1_H1_R1
import Mathlib

/-! A greedy cover chooses a shift of maximum degree in the remaining incidence graph. Double counting bounds the surviving fraction at each step. -/
open Finset Real
namespace Cover32
lemma pick (U T : Finset ℕ) (R : ℕ → ℕ → Prop) [DecidableRel R] (k : ℕ)
    (hu : U.Nonempty) (hk : 0<k)
    (h : ∀ n ∈ T, U.card ≤ k*(U.filter (R n)).card) :
    ∃ a ∈ U, (((T.filter fun n => ¬R n a).card):ℝ) ≤ exp (-(1/(k:ℝ))) * T.card := by
  classical
  let f (a : ℕ) := (T.filter fun n => R n a).card
  obtain ⟨a,ha,hmax⟩ := U.exists_max_image f hu
  have eq : (∑ n ∈ T, (U.filter (R n)).card) = ∑ b ∈ U, f b :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
  have hh : T.card * U.card ≤ (k*f a) * U.card := calc
    _ = ∑ _ ∈ T, U.card := by simp
    _ ≤ ∑ n ∈ T, k*(U.filter (R n)).card := sum_le_sum h
    _ = k*(∑ b ∈ U, f b) := by rw [←mul_sum,eq]
    _ ≤ k*(∑ _b ∈ U, f a) := Nat.mul_le_mul_left _ (sum_le_sum hmax)
    _ = _ := by simp; ring
  have key := Nat.le_of_mul_le_mul_right hh (card_pos.mpr hu)
  have hkr : 0<(k:ℝ) := by exact_mod_cast hk
  have key' : (T.card:ℝ) ≤ k*(f a:ℝ) := by exact_mod_cast key
  have part : (f a:ℝ) + ((T.filter fun n => ¬R n a).card:ℝ) = T.card := by
    exact_mod_cast card_filter_add_card_filter_not (s := T) (p := fun n => R n a)
  have hl : (T.card:ℝ)/k ≤ f a := (div_le_iff₀ hkr).mpr (by linarith)
  refine ⟨a,ha,?_⟩
  calc _ ≤ (1-1/(k:ℝ))*T.card := by rw [sub_mul,one_mul]; linarith only [hl,part,show (1/(k:ℝ))*T.card = T.card/k by ring]
       _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [add_one_le_exp (-(1/(k:ℝ)))]) (Nat.cast_nonneg _)

lemma greedy (U : Finset ℕ) (R : ℕ → ℕ → Prop) [DecidableRel R] (k : ℕ)
    (hu : U.Nonempty) (hk : 0<k) (m : ℕ) (T : Finset ℕ)
    (h : ∀ n ∈ T, U.card ≤ k*(U.filter (R n)).card) :
    ∃ B ⊆ U, B.card ≤ m ∧ ∃ S : Finset ℕ, (S.card:ℝ) ≤ exp (-(m:ℝ)/k)*T.card ∧
      ∀ n ∈ T, n ∉ S → ∃ a ∈ B, R n a := by
  classical
  induction m generalizing T with
  | zero => exact ⟨∅,empty_subset _,by simp,T,by simp,fun _ hn hx => (hx hn).elim⟩
  | succ m ih =>
    obtain ⟨a,ha,hs⟩ := pick U T R k hu hk h
    let T' := T.filter fun n => ¬R n a
    obtain ⟨B,hB,hc,S,hS,hit⟩ := ih T' (fun n hn => h n (mem_filter.mp hn).1)
    refine ⟨insert a B,insert_subset ha hB,(card_insert_le a B).trans (by omega), S,?_,?_⟩
    · calc _ ≤ exp (-(m:ℝ)/k) * T'.card := hS
           _ ≤ exp (-(m:ℝ)/k) * (exp (-(1/(k:ℝ))) * T.card) := mul_le_mul_of_nonneg_left hs (exp_pos _).le
           _ = _ := by rw [←mul_assoc,←exp_add]; push_cast; congr 2; ring
    · intro n hn hx
      by_cases e : R n a
      · exact ⟨a,mem_insert_self _ _,e⟩
      obtain ⟨b,hb,hr⟩ := hit n (mem_filter.mpr ⟨hn,e⟩) hx
      exact ⟨b,mem_insert_of_mem hb,hr⟩

lemma covering (C : ℕ) (hC : 1≤C) : ∃ D : ℕ, ∀ (L : ℕ) (U T : Finset ℕ) (R : ℕ → ℕ → Prop)
    [DecidableRel R], 1≤L → U.Nonempty → T.card ≤ 2^(8*L) →
    (∀ n ∈ T, U.card ≤ C*L*(U.filter (R n)).card) →
    ∃ B ⊆ U, B.card ≤ D*L^2 ∧ ∀ n ∈ T, ∃ a ∈ B, R n a := by
  classical
  refine ⟨9*C,fun L U T R _ hL hu hT h => ?_⟩
  let k := C*L
  have hk : 0<k := Nat.mul_pos (by omega) (by omega)
  obtain ⟨B,hB,hc,S,hS,hit⟩ := greedy U R k hu hk (9*L*k) T h
  have hkr : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hex : -((9*L*k:ℕ):ℝ)/k = -9*L := by push_cast; field_simp
  rw [hex] at hS
  have hpow : (T.card:ℝ) ≤ exp (8*L) := calc
    _ ≤ (2:ℝ)^(8*L) := by exact_mod_cast hT
    _ ≤ exp 1 ^ (8*L) := pow_le_pow_left₀ (by norm_num) (by linarith only [add_one_le_exp 1]) _
    _ = _ := by rw [← exp_nat_mul]; push_cast; ring_nf
  have lt1 : (S.card:ℝ) < 1 := calc
    _ ≤ exp (-9*L)*exp (8*L) := hS.trans (mul_le_mul_of_nonneg_left hpow (exp_pos _).le)
    _ < 1 := by
      rw [←exp_add,exp_lt_one_iff]
      have : (0:ℝ)<L := by exact_mod_cast (show 0<L by omega)
      linarith
  have hc0 : S.card < 1 := by exact_mod_cast lt1
  have empt : S = ∅ := card_eq_zero.mp (by omega)
  refine ⟨B,hB,hc.trans (by dsimp [k]; nlinarith),fun n hn => hit n hn (by simp [empt])⟩
end Cover32

theorem OMA.solution : OMA.R_Erdos32_erdos_32_variants_log_squared_R1_H1_R1.H2 := Cover32.covering
