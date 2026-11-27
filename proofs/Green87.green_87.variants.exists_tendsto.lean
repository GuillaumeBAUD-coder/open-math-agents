import FormalConjectures.GreensOpenProblems.«87»
import Mathlib.GroupTheory.Perm.Centralizer

/-! Remove the cycle of a distinguished point of a permutation. Its complement
is uniformly permuted conditional on its size. -/

open Equiv Finset Filter
open scoped BigOperators Nat Topology
namespace OMA.PermutationLimit
variable {V : Type*} [Fintype V] [DecidableEq V]
private abbrev SingleCycle (V : Type*) := {f : Perm V // ∀ x y, f.SameCycle x y}
private def HasK (f : Perm V) (k : ℕ) := ∃ B : Finset V, B.card = k ∧ ∀ x, f x ∈ B ↔ x ∈ B

private theorem hasK_iff {n k : ℕ} {f : Perm (Fin n)} : HasK f k ↔ Green87.FixesSet f k := by
  classical
  constructor
  · rintro ⟨s,hs,h⟩
    refine ⟨s,hs,?_⟩
    ext x
    simp only [mem_image]
    exact ⟨fun ⟨a,ha,e⟩ => e ▸ (h a).mpr ha,
      fun hx => ⟨f.symm x, (h _).mp (by simpa using hx), f.apply_symm_apply _⟩⟩
  · rintro ⟨s,hs,he⟩
    refine ⟨s,hs,fun x => ?_⟩
    nth_rw 1 [← he]
    simp [f.injective.eq_iff]

private noncomputable def rest (x : V) (f : Perm V) : Finset V := by
  classical
  exact univ.filter (fun y => ¬ f.SameCycle x y)

@[simp] private theorem mem_rest (x y : V) (f : Perm V) : y ∈ rest x f ↔ ¬ f.SameCycle x y := by
  classical
  simp [rest]

private def join (S : Finset V) (g : Perm S) (c : Perm {y // y ∉ S}) : Perm V :=
  Perm.subtypeCongr (p := (· ∈ S)) g c

private theorem join_mem (S : Finset V) (g : Perm S) (c : Perm {y // y ∉ S}) (y : V) :
    join S g c y ∈ S ↔ y ∈ S := by
  by_cases h : y ∈ S
  · simpa [join,h] using (g ⟨y,h⟩).property
  · simpa [join,h] using (c ⟨y,h⟩).property

private theorem join_left (S : Finset V) (g : Perm S) (c : Perm {y // y ∉ S}) :
    (join S g c).subtypePerm (join_mem S g c) = g := by
  ext z
  simp [join]

private theorem join_right (S : Finset V) (g : Perm S) (c : Perm {y // y ∉ S}) :
    (join S g c).subtypePerm (fun y => not_congr (join_mem S g c y)) = c := by
  ext z
  simp [join]

private theorem invariant_cycle {f : Perm V} {S : Finset V} (h : ∀ y, f y ∈ S ↔ y ∈ S)
    {x y : V} (hc : f.SameCycle x y) (hx : x ∈ S) : y ∈ S := by
  obtain ⟨i,rfl⟩ := hc
  simpa only [Perm.subtypePerm_zpow, Perm.subtypePerm_apply] using ((f.subtypePerm h ^ i) (⟨x,hx⟩ : S)).property

private theorem rest_join (S : Finset V) (x : V) (hx : x ∉ S) (g : Perm S)
    (c : SingleCycle {y // y ∉ S}) : rest x (join S g c.1) = S := by
  ext y
  rw [mem_rest]
  by_cases hy : y ∈ S
  · exact iff_of_true (fun h => hx (invariant_cycle (join_mem S g c.1) h.symm hy)) hy
  · apply iff_of_false _ hy
    apply not_not_intro
    have h := c.2 ⟨x,hx⟩ ⟨y,hy⟩
    rw [← join_right S g c.1] at h
    exact Perm.sameCycle_subtypePerm.mp h

private noncomputable def fiberEquiv (x : V) (S : Finset V) (hx : x ∉ S) :
    (Perm S × SingleCycle {y // y ∉ S}) ≃ {f : Perm V // rest x f = S} := by
  classical
  let hmem (f : {f : Perm V // rest x f = S}) (y : V) : f.1 y ∈ S ↔ y ∈ S := by
    obtain ⟨f,rfl⟩ := f
    simp
  let g (f : {f : Perm V // rest x f = S}) : Perm S := f.1.subtypePerm (hmem f)
  let c (f : {f : Perm V // rest x f = S}) : SingleCycle {y // y ∉ S} :=
    ⟨f.1.subtypePerm (fun y => not_congr (hmem f y)), by
      intro y z
      apply Perm.sameCycle_subtypePerm.mpr
      have hr (w : {y // y ∉ S}) : f.1.SameCycle x w := by
        by_contra h
        exact w.2 (by simpa only [f.2] using (mem_rest _ _ _).mpr h)
      exact (hr y).symm.trans (hr z)⟩
  refine ⟨fun a => ⟨join S a.1 a.2.1, rest_join S x hx a.1 a.2⟩, fun f => (g f,c f), ?_, ?_⟩
  · rintro ⟨a,b⟩
    exact Prod.ext (join_left _ _ _) (Subtype.ext (join_right _ _ _))
  · intro f
    apply Subtype.ext
    ext y
    by_cases hy : y ∈ S <;> simp [join,g,c,hy]

private theorem cyclic_card (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W] :
    Nat.card (SingleCycle W) = (Fintype.card W - 1)! := by
  classical
  by_cases h : 2 ≤ Fintype.card W
  · have hnon : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp h
    have iffcy (f : Perm W) : (∀ x y, f.SameCycle x y) ↔ f.cycleType = {Fintype.card W} := by
      constructor
      · intro hf
        have hnf (x : W) : f x ≠ x := by
          obtain ⟨y,hy⟩ := exists_ne x
          exact fun he => hy (Perm.SameCycle.eq_of_left (hf x y) he).symm
        let x : W := Classical.choice inferInstance
        have hcy : f.IsCycle := ⟨x,hnf x,fun b _ => hf x b⟩
        have hs : f.support = univ := eq_univ_of_forall (fun y => Perm.mem_support.mpr (hnf y))
        simp [hcy.cycleType,hs]
      · intro hf
        have hcy : f.IsCycle := Perm.card_cycleType_eq_one.mp (by simp [hf])
        have hcard := f.sum_cycleType
        rw [hf, Multiset.sum_singleton] at hcard
        have hs : f.support = univ := eq_univ_of_card f.support hcard.symm
        intro x y
        exact hcy.isCycleOn.2 (Perm.mem_support.mp (hs ▸ mem_univ x)) (Perm.mem_support.mp (hs ▸ mem_univ y))
    rw [show Nat.card (SingleCycle W) = Fintype.card { f : Perm W // f.cycleType = {Fintype.card W}} from
      (Nat.card_congr (Equiv.subtypeEquivRight iffcy)).trans Nat.card_eq_fintype_card]
    simpa [Fintype.card_subtype] using
      (Perm.card_of_cycleType_singleton (α:=W) h le_rfl)
  · have hcard : Fintype.card W = 1 := by have := Fintype.card_pos (α:=W); omega
    obtain ⟨w,hw⟩ := Fintype.card_eq_one_iff.mp hcard
    letI : Unique W := ⟨⟨w⟩,hw⟩
    letI : Unique (SingleCycle W) := ⟨⟨⟨1,fun x y => (Subsingleton.elim x y).sameCycle _⟩⟩,
      fun a => Subtype.ext (Subsingleton.elim _ _)⟩
    simp [hcard]



private theorem hasK_join (S : Finset V) (g : Perm S) (c : SingleCycle {y // y ∉ S}) (k : ℕ) :
    (HasK g k → HasK (join S g c.1) k) ∧
    (k < Sᶜ.card → HasK (join S g c.1) k → HasK g k) := by
  classical
  constructor
  · rintro ⟨T,hcard,hT⟩
    refine ⟨T.map (Function.Embedding.subtype _), by simpa, fun y => ?_⟩
    by_cases hy : y ∈ S
    · rw [join,Perm.subtypeCongr.left_apply _ _ hy]
      change (Function.Embedding.subtype _) (g ⟨y,hy⟩) ∈ _ ↔ (Function.Embedding.subtype _) (⟨y,hy⟩ : S) ∈ _
      simpa only [Finset.mem_map'] using hT ⟨y,hy⟩
    · have hf := (join_mem S g c.1 y).not.mpr hy
      exact iff_of_false (fun h => hf (T.property_of_mem_map_subtype h))
        (fun h => hy (T.property_of_mem_map_subtype h))
  · rintro hk ⟨B,hB,hin⟩
    have hb : ∀ z ∈ B, z ∈ S := by
      intro z hz
      by_contra hzs
      have hsub : Sᶜ ⊆ B := by
        intro y hy
        have hcy := c.2 ⟨z,hzs⟩ ⟨y,mem_compl.mp hy⟩
        rw [← join_right S g c.1] at hcy
        exact invariant_cycle hin (Perm.sameCycle_subtypePerm.mp hcy) hz
      exact (not_le_of_gt hk) (hB ▸ card_le_card hsub)
    refine ⟨B.subtype (· ∈ S), ?_, ?_⟩
    · rw [← card_map (Function.Embedding.subtype _)]; exact congrArg card (subtype_map_of_mem hb) |>.trans hB
    · intro y
      simpa [join] using hin (y : V)

open scoped Classical in
private noncomputable def score (f : Perm V) (k : ℕ) : ℝ := if HasK f k then 1 else 0

private theorem score_congr {W : Type*} [Fintype W] [DecidableEq W] (e : V ≃ W) (f : Perm V) (k : ℕ) :
    score (e.permCongr f) k = score f k := by
  classical
  unfold score
  apply if_congr _ rfl rfl
  constructor
  · rintro ⟨B,hB,hin⟩
    refine ⟨B.map e.symm.toEmbedding, by simpa, fun y => ?_⟩
    simpa [Equiv.permCongr_apply, Finset.mem_map_equiv] using hin (e y)
  · rintro ⟨B,hB,hin⟩
    refine ⟨B.map e.toEmbedding, by simpa, fun y => ?_⟩
    simpa [Equiv.permCongr_apply, Finset.mem_map_equiv] using hin (e.symm y)

private theorem score_sum (k : ℕ) :
    ∑ f : Perm V, score f k = (Fintype.card V)! * Green87.i (Fintype.card V) k := by
  classical
  let e := Fintype.equivFin V
  calc
    _ = ∑ f : Perm (Fin (Fintype.card V)), score f k := by
      rw [← (Equiv.permCongr e).sum_comp (fun f => score f k)]
      exact sum_congr rfl fun f _ => (score_congr e f k).symm
    _ = _ := by
      unfold Green87.i score
      simp only [hasK_iff, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rw [mul_div_cancel₀ _ (by positivity)]
      simp [Fintype.card_subtype, Finset.sum_boole]

private theorem prob_bounds (n k : ℕ) : 0 ≤ Green87.i n k ∧ Green87.i n k ≤ 1 := by
  classical
  unfold Green87.i
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  constructor
  · positivity
  · apply (div_le_one (by positivity)).mpr
    exact_mod_cast Fintype.card_subtype_le _



private noncomputable def slice {n : ℕ} (x : Fin (n+1)) (S : Finset (Fin (n+1))) (k : ℕ) : ℝ := by
  classical
  exact ∑ f ∈ univ.filter (fun f => rest x f = S), score f k

private def err (n k m : ℕ) : ℝ := if n+1-m ≤ k then 1 else 0
private def weight (n m : ℕ) : ℝ := (m ! : ℝ)*(n-m)!

private theorem slice_bounds {n k : ℕ} (x : Fin (n+1)) (S : Finset (Fin (n+1))) (hx : x ∉ S) :
    weight n S.card * Green87.i S.card k ≤ slice x S k ∧
    slice x S k ≤ weight n S.card * (Green87.i S.card k + err n k S.card) := by
  classical
  let W := {y : Fin (n+1) // y ∉ S}
  letI : Nonempty W := ⟨⟨x,hx⟩⟩
  have hW : Fintype.card W = n+1-S.card := by
    rw [Fintype.card_subtype_compl]; simp
  have hC : (Fintype.card (SingleCycle W) : ℝ) = ((n-S.card)! : ℕ) := by
    rw [← Nat.card_eq_fintype_card, cyclic_card, hW, show n+1-S.card-1=n-S.card by omega]
  have hsum : slice x S k = ∑ g : Perm S, ∑ c : SingleCycle W, score (join S g c.1) k := by
    unfold slice
    rw [Finset.sum_subtype (p:=fun f => rest x f = S) _ (by simp) _]
    rw [← (fiberEquiv x S hx).sum_comp, Fintype.sum_prod_type]
    rfl
  have hb (g : Perm S) (c : SingleCycle W) :
      score g k ≤ score (join S g c.1) k ∧ score (join S g c.1) k ≤ score g k + err n k S.card := by
    have h := hasK_join S g c k
    by_cases h1 : HasK g k
    · simp [score,h1,h.1 h1,err]; split_ifs <;> norm_num
    · by_cases h2 : HasK (join S g c.1) k
      · have hh : Sᶜ.card ≤ k := le_of_not_gt fun hk => h1 (h.2 hk h2)
        have hh' : n+1-S.card ≤ k := by simpa [card_compl] using hh
        simp [score,h1,h2,err,hh']
      · simp [score,h1,h2,err]; split_ifs <;> norm_num
  have evalSum (d : ℝ) :
      (∑ g : Perm S, ∑ _c : SingleCycle W, (score g k + d)) =
        weight n S.card*(Green87.i S.card k+d) := by
    simp only [sum_const, card_univ, nsmul_eq_mul, hC, ← mul_sum, sum_add_distrib,
      score_sum, Fintype.card_coe, Fintype.card_perm]
    unfold weight
    ring
  rw [hsum]
  constructor
  · rw [← add_zero (Green87.i S.card k), ← evalSum]
    exact sum_le_sum fun g _ => sum_le_sum fun c _ => by simpa using (hb g c).1
  · rw [← evalSum]
    exact sum_le_sum fun g _ => sum_le_sum fun c _ => (hb g c).2

private theorem shell_sum {n : ℕ} (x : Fin (n+1)) (a : ℕ → ℝ) :
    ∑ S ∈ (univ.erase x).powerset, weight n S.card * a S.card =
      (n ! : ℝ)*∑ m ∈ range (n+1), a m := by
  classical
  have hcard : (univ.erase x).card = n := by simp
  rw [sum_powerset, hcard, mul_sum]
  apply sum_congr rfl
  intro m hm
  rw [Finset.sum_powersetCard m _ (fun l => weight n l*a l), hcard, nsmul_eq_mul]
  have h : (n.choose m : ℝ)*(m ! : ℝ)*((n-m)! : ℝ) = n ! := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by have := mem_range.mp hm; omega : m ≤ n)
  rw [← h, weight]; ring

private theorem recurrence (n k : ℕ) :
    (∑ m ∈ range (n+1), Green87.i m k) ≤ (n+1 : ℝ)*Green87.i (n+1) k ∧
    (n+1 : ℝ)*Green87.i (n+1) k ≤ (∑ m ∈ range (n+1), Green87.i m k)+k := by
  classical
  let x : Fin (n+1) := 0
  let P := (univ.erase x).powerset
  have hsub (f : Perm (Fin (n+1))) : rest x f ∈ P := by
    apply mem_powerset.mpr
    intro y hy
    simp only [mem_erase,mem_univ,and_true]
    rintro rfl
    exact (mem_rest _ _ _).mp hy (Perm.SameCycle.refl _ _)
  have hsum : ∑ S ∈ P, slice x S k = ((n+1)! : ℝ)*Green87.i (n+1) k := by
    unfold slice
    rw [sum_fiberwise_of_maps_to (fun f _ => hsub f), score_sum]
    simp
  have hfree (S) (hS : S ∈ P) : x ∉ S := by
    intro hx
    exact (mem_erase.mp (mem_powerset.mp hS hx)).1 rfl
  have hlow := sum_le_sum (s:=P) fun S hS => (slice_bounds (k:=k) x S (hfree S hS)).1
  have hupp := sum_le_sum (s:=P) fun S hS => (slice_bounds (k:=k) x S (hfree S hS)).2
  rw [hsum, shell_sum x (fun m => Green87.i m k)] at hlow
  rw [hsum, shell_sum x (fun m => Green87.i m k + err n k m), sum_add_distrib] at hupp
  have herr : (∑ m ∈ range (n+1), err n k m) ≤ k := by
    simp only [err, sum_boole]
    exact_mod_cast (show ((range (n+1)).filter (fun m => n+1-m ≤ k)).card ≤ k by
      calc
        _ ≤ (Ico (n+1-k) (n+1)).card := card_le_card (by intro m hm; simp_all [mem_filter,mem_range,mem_Ico]; omega)
        _ ≤ _ := by rw [Nat.card_Ico]; omega)
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hlow hupp
  have hn : (0:ℝ) < n ! := by positivity
  constructor
  · apply (le_of_mul_le_mul_left _ hn)
    nlinarith only [hlow]
  · apply (le_of_mul_le_mul_left _ hn)
    nlinarith only [hupp, mul_le_mul_of_nonneg_left herr hn.le]

private theorem limit_exists (k : ℕ) : ∃ L : ℝ, Tendsto (fun n => Green87.i n k) atTop (𝓝 L) := by
  let avg (n : ℕ) := (∑ m ∈ range (n+1), Green87.i m k) / (n+1 : ℝ)
  have hav (n : ℕ) : avg n ≤ Green87.i (n+1) k ∧
      Green87.i (n+1) k ≤ avg n + (k:ℝ)/(n+1) := by
    have hpos : 0 < (n:ℝ)+1 := by positivity
    obtain ⟨hl,hu⟩ := recurrence n k
    constructor
    · exact (div_le_iff₀ hpos).mpr (by linarith)
    · dsimp [avg]
      rw [← add_div]
      exact (le_div_iff₀ hpos).mpr (by linarith)
  have hm : Monotone avg := by
    apply monotone_nat_of_le_succ
    intro n
    have h := (hav n).1
    dsimp only [avg] at h ⊢
    rw [sum_range_succ _ (n+1), Nat.cast_add, Nat.cast_one]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mp h
    nlinarith only [hh]
  have hb : BddAbove (Set.range avg) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n,rfl⟩
    exact (hav n).1.trans (prob_bounds (n+1) k).2
  have hlim := tendsto_atTop_ciSup hm hb
  have ht : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun n : ℕ => (k:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ht
  refine ⟨⨆ n, avg n, ?_⟩
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim (by simpa using hlim.add herr)
    (fun n => (hav n).1) (fun n => (hav n).2)

end OMA.PermutationLimit

open OMA.PermutationLimit in
theorem OMA.solution : type_of% @Green87.green_87.variants.exists_tendsto := limit_exists
