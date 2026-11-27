import FormalConjectures.GreensOpenProblems.«19»
import Mathlib

/-! # Popular corners and triforce densities

The finite triforce lower bound follows by discarding low-codegree pairs. For the converse, locally linear graphs from the Ruzsa–Szemerédi construction yield densities close to the reciprocal of their number of vertices. The two transfer statements translate between finite templates and popular corners. See Mandache, A variant of the Corners theorem (2021), and Fox, Sah, Sawhney, Stoner and Zhao, Triforce and corners (2020). -/

namespace OMA.R_Green19_green_19_R1


open Finset Filter Real Topology
open scoped Classical
lemma small_fibers {E X : Type*} [DecidableEq X] [Fintype X]
    (H : Finset E) (proj : E → X) (s : ℝ) (hs : 0 ≤ s) :
    let deg (x : X) : ℝ := (H.filter (fun z => proj z = x)).card
    ((H.filter (fun e => deg (proj e) < s)).card : ℝ) ≤ Fintype.card X*s := by
  intro deg
  classical
  let B := H.filter (fun e => deg (proj e) < s)
  have eq := Finset.card_eq_sum_card_fiberwise (s:=B) (t:=(univ : Finset X)) (f:=proj) (fun _ _ => mem_univ _)
  have r (x : X) : ((B.filter (fun e => proj e=x)).card:ℝ) ≤ s := by
    by_cases sm : deg x < s
    · refine le_trans ?_ sm.le
      unfold deg
      exact_mod_cast Finset.card_le_card (filter_subset_filter _ (filter_subset _ _))
    · have empty : B.filter (fun e => proj e = x) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro e h
        obtain ⟨he,hx⟩ := mem_filter.mp h
        exact sm (hx ▸ (mem_filter.mp he).2)
      simp only [empty,card_empty,Nat.cast_zero]; exact hs
  change (B.card:ℝ) ≤ _
  calc
    _ = ∑ x : X, ((B.filter (fun e => proj e=x)).card:ℝ) := by exact_mod_cast eq
    _ ≤ ∑ _x : X,s := sum_le_sum (fun x _ => r x)
    _ = _ := by simp

lemma triforce_lower {q : ℕ} (hq : 0<q) (H : Finset (Fin q × Fin q × Fin q)) :
    let xy (e : Fin q × Fin q × Fin q) := (e.1,e.2.1)
    let xz (e : Fin q × Fin q × Fin q) := (e.1,e.2.2)
    let yz (e : Fin q × Fin q × Fin q) := (e.2.1,e.2.2)
    let deg (proj : (Fin q × Fin q × Fin q) → Fin q × Fin q) (x : Fin q × Fin q) : ℝ :=
      (H.filter (fun e => proj e = x)).card
    let density : ℝ := H.card / (q:ℝ)^3
    let triforce := (∑ e : Fin q × Fin q × Fin q,
      deg xy (xy e) * deg xz (xz e) * deg yz (yz e)) / (q:ℝ)^6
    (1/432:ℝ) * density ^ (4:ℕ) ≤ triforce := by
  intro xy xz yz deg density triforce
  classical
  let t : ℝ := H.card
  let s : ℝ := t/(6*q^2)
  have qp : 0 < (q:ℝ) := by exact_mod_cast hq
  have hn : 0 ≤ t := Nat.cast_nonneg _
  have sn : 0 ≤ s := by dsimp [s]; positivity
  let bad (proj : (Fin q × Fin q × Fin q) → Fin q × Fin q) := H.filter (fun e => deg proj (proj e) < s)
  let B := (bad xy ∪ bad xz) ∪ bad yz
  let G := H \ B
  have few (proj : (Fin q × Fin q × Fin q) → Fin q × Fin q) : ((bad proj).card:ℝ) ≤ t / 6 := by
    have h := small_fibers H proj s sn
    rw [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] at h
    have cancel : (q:ℝ)*q*s = t/6 := by dsimp [s]; field_simp
    exact h.trans_eq cancel
  have b : (B.card:ℝ) ≤ t/2 := by
    have h : B.card ≤ (bad xy).card + (bad xz).card + (bad yz).card :=
      (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
    have hr : (B.card:ℝ) ≤ (bad xy).card + ((bad xz).card:ℝ) + (bad yz).card := by exact_mod_cast h
    linarith [few xy,few xz,few yz]
  have cover : H ⊆ G ∪ B := by intro e he; by_cases h : e ∈ B <;> simp [G,h,he]
  have sz : (H.card:ℝ) ≤ (G.card:ℝ) + B.card := by exact_mod_cast (card_le_card cover).trans (card_union_le _ _)
  have lg : t/2 ≤ (G.card:ℝ) := by change t ≤ _ at sz; linarith
  let val (e : (Fin q × Fin q × Fin q)) := deg xy (xy e) * deg xz (xz e) * deg yz (yz e)
  have good (e : (Fin q × Fin q × Fin q)) (he : e ∈ G) : s^3 ≤ val e := by
    obtain ⟨hit,out⟩ := mem_sdiff.mp he
    have ok (proj : (Fin q × Fin q × Fin q) → Fin q × Fin q) (inc : bad proj ⊆ B) : s ≤ deg proj (proj e) :=
      le_of_not_gt (fun lt => out (inc (mem_filter.mpr ⟨hit,lt⟩)))
    have a := ok xy (fun _ h => mem_union_left _ (mem_union_left _ h))
    have b := ok xz (fun _ h => mem_union_left _ (mem_union_right _ h))
    have c := ok yz (fun _ h => mem_union_right _ h)
    dsimp [val]
    rw [pow_succ,sq]
    exact mul_le_mul (mul_le_mul a b sn (sn.trans a)) c sn (mul_nonneg (sn.trans a) (sn.trans b))
  have vnon (e : (Fin q × Fin q × Fin q)) : 0 ≤ val e := by dsimp [val,deg]; positivity
  have total : (t/2)*s^3 ≤ ∑ e : (Fin q × Fin q × Fin q), val e := calc
    _ ≤ (G.card:ℝ)*s^3 := mul_le_mul_of_nonneg_right lg (pow_nonneg sn _)
    _ = ∑ _e ∈ G,s^3 := by simp
    _ ≤ ∑ e ∈ G,val e := sum_le_sum good
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun e _ _ => vnon e)
  change (1/432:ℝ)*(t/q^3)^4 ≤ (∑ e : (Fin q × Fin q × Fin q),val e)/q^6
  rw [le_div_iff₀ (pow_pos qp 6)]
  apply le_trans (le_of_eq ?_) total
  dsimp [s]
  field_simp
  ring


-- Convex power-law lower bounds for finite triforce models transfer to popular corners.
def H1 : Prop := ∀ c : ℝ, 1 ≤ c → ∀ b > (0:ℝ),
    (∀ q : ℕ, 0 < q → ∀ H : Finset (Fin q × Fin q × Fin q),
    let xy (e : Fin q × Fin q × Fin q) := (e.1,e.2.1)
    let xz (e : Fin q × Fin q × Fin q) := (e.1,e.2.2)
    let yz (e : Fin q × Fin q × Fin q) := (e.2.1,e.2.2)
    let deg (proj : (Fin q × Fin q × Fin q) → Fin q × Fin q) (x : Fin q × Fin q) : ℝ :=
      (H.filter (fun e => proj e = x)).card
    let density : ℝ := H.card / (q:ℝ)^3
    let triforce := (∑ e : Fin q × Fin q × Fin q,
      deg xy (xy e) * deg xz (xz e) * deg yz (yz e)) / (q:ℝ)^6
    b * density^c ≤ triforce) →
    Green19.ValidExponent c

-- Sampling the triangle hypergraph of a locally linear graph yields sets with few
-- corners simultaneously in every nonzero direction, in arbitrarily high dimensions.
def H2 : Prop := ∀ q : ℕ, 1 < q → ∀ (G : SimpleGraph (Fin q)) [DecidableRel G.Adj], G.LocallyLinear →
    ∃ᶠ n : ℕ in atTop, ∃ A : Finset (𝔽₂ n × 𝔽₂ n),
      let N : ℝ := Fintype.card (𝔽₂ n)
      ((G.cliqueFinset 3).card:ℝ) / (q:ℝ)^3 * N^2 ≤ A.card ∧
        ∀ d : 𝔽₂ n, d ≠ 0 → ((Green19.S d A).card:ℝ) ≤ (2/(q:ℝ)^4) * N^2



open Finset Filter Real Asymptotics Topology
lemma many_triangles (η : ℝ) (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop, (q:ℝ)^((2:ℝ)-η) ≤ (ruzsaSzemerediNumberNat q : ℝ) := by
  obtain ⟨C,hC,bound⟩ := ruzsaSzemerediNumberNat_asymptotic_lower_bound.exists_pos
  have logs := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [bound.bound,logs.eventually_ge_atTop ((8/η)^2),
    logs.eventually_ge_atTop (2*log C/η),eventually_gt_atTop 1] with q b sq big hq
  have qp : 0<(q:ℝ) := by exact_mod_cast (by omega : 0<q)
  let l := log (q:ℝ)
  change (8/η)^2 ≤ l at sq
  change 2*log C/η ≤ l at big
  have nl : 0 ≤ l := (sq_nonneg _).trans sq
  have root : 8/η ≤ √l := (le_sqrt (by positivity) nl).mpr sq
  have re := (div_le_iff₀ hη).mp root
  have bb := (div_le_iff₀ hη).mp big
  have re' := mul_le_mul_of_nonneg_right re (sqrt_nonneg l)
  have sr : √l*η*√l = l*η := calc
    _ = (√l)^2*η := by ring
    _ = _ := by rw [Real.sq_sqrt nl]
  rw [sr] at re'
  have sm : log C + 4*√l ≤ l*η := by linarith
  have lhs : C*(q:ℝ)^((2:ℝ)-η) ≤ (q:ℝ)^2 * exp (-4*√l) := by
    rw [← Real.rpow_natCast (q:ℝ) 2]
    simp only [Real.rpow_def_of_pos qp]
    rw [← Real.exp_log hC,← Real.exp_add,← Real.exp_add,Real.exp_le_exp]
    change log C + l*(2-η) ≤ l*2 + -4*√l
    linarith
  have rhs : (q:ℝ)^2*exp (-4*√l) ≤ C*(ruzsaSzemerediNumberNat q:ℝ) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (exp_pos _).le),
      abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (ruzsaSzemerediNumberNat q))] using b
  exact (mul_le_mul_iff_right₀ hC).mp (lhs.trans rhs)


lemma graph_test (transfer : H2) {q : ℕ} (hq : 1<q) {α b K : ℝ}
    (dens : α ≤ (ruzsaSzemerediNumberNat q:ℝ)/(q:ℝ)^3)
    (popular : ∀ᶠ n : ℕ in atTop, ∀ A : Finset (𝔽₂ n × 𝔽₂ n),
      let N : ℝ := Fintype.card (𝔽₂ n)
      α*N^2 ≤ A.card → ∃ d : 𝔽₂ n, d ≠ 0 ∧ K*α^b*N^2 ≤ (Green19.S d A).card) :
    K*α^b ≤ 2/(q:ℝ)^4 := by
  obtain ⟨G,adj,card,linear⟩ := ruzsaSzemerediNumber_spec (α:=Fin q)
  let _ : DecidableRel G.Adj := adj
  have dup : (G.cliqueFinset 3).card = ruzsaSzemerediNumberNat q := card
  obtain ⟨n,found,every⟩ := ((transfer q hq G linear).and_eventually popular).exists
  obtain ⟨A,lo,hi⟩ := found
  let N : ℝ := Fintype.card (𝔽₂ n)
  have Np : 0 < N := by dsimp only [N]; exact_mod_cast (Fintype.card_pos (α:=𝔽₂ n))
  have val : α ≤ ((G.cliqueFinset 3).card:ℝ)/(q:ℝ)^3 := by rw [dup]; exact dens
  have lo' : ((G.cliqueFinset 3).card:ℝ)/(q:ℝ)^3*N^2 ≤ A.card := lo
  have inA : α*N^2 ≤ A.card := (mul_le_mul_of_nonneg_right val (sq_nonneg N)).trans lo'
  obtain ⟨d,ne,yes⟩ := every A inA
  exact (mul_le_mul_iff_left₀ (pow_pos Np 2)).mp (yes.trans (hi d ne))

lemma exponent_mono {c b : ℝ} (cb : c ≤ b) (hc : Green19.ValidExponent c) :
    Green19.ValidExponent b := by
  obtain ⟨K,hK,valid⟩ := hc
  refine ⟨K,hK,?_⟩
  intro α pos lt
  filter_upwards [valid α pos lt] with n hn
  intro A
  dsimp only
  intro dens
  obtain ⟨d,hd,low⟩ := hn A dens
  refine ⟨d,hd,le_trans ?_ low⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge pos lt.le cb) hK.le) (sq_nonneg _)

lemma exponent_obstruction (transfer : H2) {b : ℝ} (hb : 1 ≤ b)
    (valid : Green19.ValidExponent b) : 4 ≤ b := by
  by_contra! small
  obtain ⟨K,hK,v⟩ := valid
  let η := (4-b)/(2*b)
  have bp : 0 < b := by linarith
  have ηp : 0 < η := div_pos (by linarith) (by positivity)
  let a := 1+η
  have ap : 0 < a := by dsimp [a]; positivity
  have ab : a*b = (4+b)/2 := by dsimp [a,η]; field_simp; ring
  have gap : 0 < 4-a*b := by linarith
  have grows := (tendsto_rpow_atTop gap).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨q,many,large,hq⟩ := ((many_triangles η ηp).and
    ((grows.eventually_gt_atTop (2/K)).and (eventually_gt_atTop 1))).exists
  have qp : 0<(q:ℝ) := by exact_mod_cast (by omega : 0<q)
  have q1 : 1<(q:ℝ) := by exact_mod_cast hq
  let α := (q:ℝ)^(-a)
  have αp : 0 < α := Real.rpow_pos_of_pos qp _
  have α1 : α < 1 := Real.rpow_lt_one_of_one_lt_of_neg q1 (neg_lt_zero.mpr ap)
  have dens : α ≤ (ruzsaSzemerediNumberNat q:ℝ)/(q:ℝ)^3 := by
    rw [le_div_iff₀ (pow_pos qp 3)]
    apply le_trans (le_of_eq ?_) many
    dsimp [α]
    rw [← Real.rpow_natCast (q:ℝ) 3,← Real.rpow_add qp]
    congr 1
    dsimp [a]
    ring
  have limited : K*α^b ≤ 2/(q:ℝ)^4 := graph_test transfer hq dens (v α αp α1)
  have impossible := (le_div_iff₀ (pow_pos qp 4)).mp limited
  have scale : α^b*(q:ℝ)^4 = (q:ℝ)^(4-a*b) := by
    dsimp [α]
    rw [← Real.rpow_mul qp.le,← Real.rpow_natCast (q:ℝ) 4,← Real.rpow_add qp]
    congr 1
    ring
  rw [mul_assoc,scale] at impossible
  change 2/K < (q:ℝ)^(4-a*b) at large
  linarith [(div_lt_iff₀ hK).mp large]

theorem main : H1 → H2 → type_of% @Green19.green_19 := by
  intro transferUpper transferLower
  have v4 : Green19.ValidExponent 4 := by
    apply transferUpper 4 (by norm_num) (1/432) (by norm_num)
    intro q hq H
    simpa only [Real.rpow_ofNat] using triforce_lower hq H
  have lower {c : ℝ} (hc : Green19.ValidExponent c) : 4 ≤ c := by
    by_contra! lt
    let b := max 1 c
    have sm : b < 4 := max_lt (by norm_num) lt
    exact (not_le.mpr sm) (exponent_obstruction transferLower (le_max_left _ _) (exponent_mono (le_max_right _ _) hc))
  change sInf {c : ℝ | Green19.ValidExponent c} = 4
  exact le_antisymm (csInf_le ⟨4,fun _ h => lower h⟩ v4) (le_csInf ⟨4,v4⟩ (fun _ h => lower h))


end OMA.R_Green19_green_19_R1
