import OMAReductions.R_Green92_green_92_variants_chase_lower_R1
import Mathlib

open Finset Filter Green92
open scoped Topology

theorem OMA.solution : OMA.R_Green92_green_92_variants_chase_lower_R1.H2 := by
  classical
  intro n
  let A := Finset (Fin n)
  let B : Finset A := univ.erase univ
  let K : ℕ := Fintype.card A
  have hK : 0 < K := Fintype.card_pos
  have hb : B.card < K := by
    dsimp [B,K]
    exact (card_erase_lt_of_mem (mem_univ _)).trans_le (by simp)
  have den : 0 < (K:ℝ) := by exact_mod_cast hK
  have lt1 : (B.card:ℝ)/K < 1 := (div_lt_one den).mpr (by exact_mod_cast hb)
  have lim := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ (B.card:ℝ)/K) lt1
  obtain ⟨m,hm⟩ := ((tendsto_order.1 lim).2 (1/10) (by norm_num)).exists
  let R (o : Fin m → List Bool) : Fin n → Bool :=
    if h : ∃ y : Fin n → Bool, ∃ j, o j = List.ofFn y then h.choose else fun _ => false
  refine ⟨m,R,?_⟩
  intro x
  have full (S : Fin m → A) (h : ∃ j, S j = univ) :
      R (fun j => Green92.trace x (S j)) = x := by
    obtain ⟨j,hj⟩ := h
    have witness : ∃ y : Fin n → Bool, ∃ i, Green92.trace x (S i) = List.ofFn y :=
      ⟨x,j,by simp [hj, Green92.trace, List.ofFn_eq_map]⟩
    simp only [R,dif_pos witness]
    obtain ⟨i,hi⟩ := witness.choose_spec
    apply List.ofFn_injective
    have sub : (Green92.trace x (S i)).Sublist (List.ofFn x) := by
      rw [List.ofFn_eq_map]
      exact List.filter_sublist.map _
    rw [hi] at sub
    exact sub.eq_of_length (by simp)
  let good := univ.filter (fun S : Fin m → A => R (fun j => Green92.trace x (S j)) = x)
  let bad := univ.filter (fun S : Fin m → A => R (fun j => Green92.trace x (S j)) ≠ x)
  have bsub : bad ⊆ Fintype.piFinset (fun _ : Fin m => B) := by
    intro S hs
    apply Fintype.mem_piFinset.mpr
    intro j
    exact mem_erase.mpr ⟨fun hj => (mem_filter.mp hs).2 (full S ⟨j,hj⟩),mem_univ _⟩
  have bcard : bad.card ≤ B.card^m := (card_le_card bsub).trans_eq (Fintype.card_piFinset_const _ _)
  have tot : good.card + bad.card = K^m := by
    simpa [K,Fintype.card_fun] using
      (card_filter_add_card_filter_not (s := (univ : Finset (Fin m → A)))
        (p := fun S => R (fun j => Green92.trace x (S j)) = x))
  change 9/10 ≤ (good.card:ℝ) / (Fintype.card (Fin m → A):ℝ)
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
  change 9/10 ≤ (good.card:ℝ) / (K:ℝ)^m
  apply (le_div_iff₀ (pow_pos den m)).mpr
  rw [div_pow,div_lt_iff₀ (pow_pos den m)] at hm
  have hB : (bad.card:ℝ) ≤ (B.card:ℝ)^m := by exact_mod_cast bcard
  have hT : (good.card:ℝ) + bad.card = (K:ℝ)^m := by exact_mod_cast tot
  linarith
