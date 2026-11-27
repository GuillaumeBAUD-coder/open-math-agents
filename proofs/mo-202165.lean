import OMAStatements.S_mo_202165
import Mathlib

open Finset OMA.S_mo_202165
namespace Propp

noncomputable def mix (t a b : ℝ) := t * a + (1-t)*b

lemma mix_zero {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) :
    ∃ t : ℝ, (0 ≤ t ∧ t ≤ 1) ∧ mix t a b = 0 := by
  by_cases h : b-a = 0
  · refine ⟨0, by norm_num, ?_⟩
    simp [mix, show b = 0 by linarith]
  · have hp : 0 < b-a := lt_of_le_of_ne (by linarith) (Ne.symm h)
    refine ⟨b/(b-a), ⟨div_nonneg hb hp.le, (div_le_one hp).2 (by linarith)⟩, ?_⟩
    unfold mix
    field_simp
    ring

lemma mix_nonneg {t a b : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ mix t a b := add_nonneg (mul_nonneg ht.1 ha) (mul_nonneg (by linarith [ht.2]) hb)

lemma mix_nonpos {t a b : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) (ha : a ≤ 0) (hb : b ≤ 0) :
    mix t a b ≤ 0 := add_nonpos (mul_nonpos_of_nonneg_of_nonpos ht.1 ha)
      (mul_nonpos_of_nonneg_of_nonpos (by linarith [ht.2]) hb)

lemma mix_unit {t a b : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) (ha : 0 ≤ a ∧ a ≤ 1)
    (hb : 0 ≤ b ∧ b ≤ 1) : 0 ≤ mix t a b ∧ mix t a b ≤ 1 := by
  refine ⟨mix_nonneg ht ha.1 hb.1, ?_⟩
  have h := mix_nonneg ht (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2)
  unfold mix at *
  linarith

noncomputable def part {r : ℤ} {p : Profile} (a : Rows r p) (w : ℤ → ℝ) (x : ℤ) :=
  ∑ i ∈ Icc (x-r) x, w i * a.val i x

lemma part_mix {r : ℤ} {p : Profile} (a : Rows r p) (t : ℝ) (u v : ℤ → ℝ) (x : ℤ) :
    part a (fun i => mix t (u i) (v i)) x = mix t (part a u x) (part a v x) := by
  simp only [part, mix, add_mul, mul_assoc, sum_add_distrib, mul_sum]

lemma part_sub {r : ℤ} {p : Profile} (a : Rows r p) (u v : ℤ → ℝ) (x : ℤ) :
    part a (fun i => u i - v i) x = part a u x - part a v x := by
  simp [part, sub_mul, sum_sub_distrib]

noncomputable def step (t i : ℤ) : ℝ := if i ≤ t then 1 else 0

lemma step_bounds (t i : ℤ) : 0 ≤ step t i ∧ step t i ≤ 1 := by
  unfold step
  split <;> norm_num

lemma early {r : ℤ} {p : Profile} (a : Rows r p) {w : ℤ → ℝ} {x : ℤ}
    (hw : ∀ i ≤ x, w i = 1) : part a w x = p x := by
  rw [← a.col x]
  apply sum_congr rfl
  intro i hi
  simp [hw i (mem_Icc.mp hi).2]

lemma late {r : ℤ} {p : Profile} (a : Rows r p) {w : ℤ → ℝ} {x : ℤ}
    (hw : ∀ i, x-r ≤ i → w i = 0) : part a w x = 0 := by
  apply sum_eq_zero
  intro i hi
  simp [hw i (mem_Icc.mp hi).1]

lemma part_bounds {r : ℤ} {p : Profile} (a : Rows r p) {w : ℤ → ℝ}
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (x : ℤ) : 0 ≤ part a w x ∧ part a w x ≤ p x := by
  constructor
  · exact sum_nonneg fun i _ => mul_nonneg (hw i).1 (a.pos i x)
  · rw [← a.col x]
    exact sum_le_sum fun i _ => mul_le_of_le_one_left (a.pos i x) (hw i).2

noncomputable def disc {r s : ℤ} {q : Profile} (b : Rows r q) (c : Rows s q) (u v : ℤ → ℝ) (x : ℤ) :=
  part b u x - part c v x

lemma disc_mix {r s : ℤ} {q : Profile} (b : Rows r q) (c : Rows s q)
    (t : ℝ) (u v U V : ℤ → ℝ) (x : ℤ) :
    disc b c (fun i => mix t (u i) (U i)) (fun i => mix t (v i) (V i)) x =
      mix t (disc b c u v x) (disc b c U V x) := by
  unfold disc
  rw [part_mix, part_mix]
  unfold mix
  ring

noncomputable def integral (I : Finset ℤ) (f D : ℤ → ℝ) := ∑ x ∈ I, f x * D x

lemma integral_mix (I : Finset ℤ) (f D E : ℤ → ℝ) (t : ℝ) :
    integral I f (fun x => mix t (D x) (E x)) = mix t (integral I f D) (integral I f E) := by
  simp only [integral, mix, mul_add, sum_add_distrib, mul_sum]
  congr 1 <;> apply sum_congr rfl <;> intros <;> ring

structure Weights (t h : ℤ) where
  w : ℤ → ℝ
  unit : ∀ i, 0 ≤ w i ∧ w i ≤ 1
  left : ∀ i, i ≤ t → w i = 1
  right : ∀ i, t+3*h < i → w i = 0

noncomputable def Weights.blend {t h : ℤ} (a b : Weights t h) (k : ℝ) (hk : 0 ≤ k ∧ k ≤ 1) :
    Weights t h where
  w i := mix k (a.w i) (b.w i)
  unit i := mix_unit hk (a.unit i) (b.unit i)
  left i hi := by simp [mix, a.left i hi, b.left i hi]
  right i hi := by simp [mix, a.right i hi, b.right i hi]

noncomputable def Weights.atStep {t h : ℤ} (u : ℤ) (ha : t ≤ u) (hb : u ≤ t+3*h) : Weights t h where
  w := step u
  unit := step_bounds u
  left i hi := by simp [step, le_trans hi ha]
  right i hi := by simp [step, show ¬i ≤ u by omega]


abbrev Plan (t h : ℤ) := Weights t h × Weights t h

noncomputable def stat {r s t h : ℤ} {q : Profile} (b : Rows r q) (c : Rows s q)
    (I : Finset ℤ) (f : ℤ → ℝ) (p : Plan t h) :=
  integral I f (disc b c p.1.w p.2.w)

noncomputable def combine {t h : ℤ} (a b : Plan t h) (k : ℝ) (hk : 0 ≤ k ∧ k ≤ 1) : Plan t h :=
  (a.1.blend b.1 k hk, a.2.blend b.2 k hk)

lemma stat_comb {r s t h : ℤ} {q : Profile} (b : Rows r q) (c : Rows s q)
    (I : Finset ℤ) (f : ℤ → ℝ) (p v : Plan t h) (k : ℝ) (hk : 0 ≤ k ∧ k ≤ 1) :
    stat b c I f (combine p v k hk) = mix k (stat b c I f p) (stat b c I f v) := by
  unfold stat
  change integral I f (disc b c (fun i => mix k (p.1.w i) (v.1.w i))
    (fun i => mix k (p.2.w i) (v.2.w i))) = _
  have he : disc b c (fun i => mix k (p.1.w i) (v.1.w i))
      (fun i => mix k (p.2.w i) (v.2.w i)) =
      fun x => mix k (disc b c p.1.w p.2.w x) (disc b c v.1.w v.2.w x) :=
    funext (disc_mix b c k p.1.w p.2.w v.1.w v.2.w)
  rw [he, integral_mix]

lemma stat_swap {r s t h : ℤ} {q : Profile} (b : Rows r q) (c : Rows s q)
    (I : Finset ℤ) (f : ℤ → ℝ) (p : Plan t h) :
    stat c b I f p.swap = -stat b c I f p := by
  simp only [stat, integral, disc, Prod.fst_swap, Prod.snd_swap, ← sum_neg_distrib]
  apply sum_congr rfl
  intros
  ring

lemma sharp_sign {r s : ℤ} {q : Profile} (b : Rows r q) (c : Rows s q)
    {h : ℤ} (hr : r ≤ h) (hs : s ≤ h) (hh : 0 ≤ h) (a x : ℤ) :
    let D := disc b c (step (a+h)) (step a) x
    0 ≤ D ∧ ((x ≤ a ∨ a+2*h < x) → D = 0) := by
  dsimp only
  unfold disc
  have one (z y : ℤ) (hy : y ≤ z) : step z y = 1 := by simp [step, hy]
  have zero (z y : ℤ) (hy : z < y) : step z y = 0 := by simp [step, not_le.mpr hy]
  constructor
  · by_cases hx : x ≤ a+h
    · rw [early b (fun i hi => one _ _ (by omega))]
      exact sub_nonneg.mpr (part_bounds c (step_bounds a) x).2
    · rw [late c (fun i hi => zero _ _ (by omega)), sub_zero]
      exact (part_bounds b (step_bounds (a+h)) x).1
  · rintro (hx | hx)
    · rw [early b (fun i hi => one _ _ (by omega)), early c (fun i hi => one _ _ (by omega))]
      ring
    · rw [late b (fun i hi => zero _ _ (by omega)), late c (fun i hi => zero _ _ (by omega))]
      ring

noncomputable def center (z x : ℤ) : ℝ := (x:ℝ) - (z:ℝ)

lemma tilt {r s : ℤ} {q : Profile} (b : Rows r q) (c : Rows s q) (t h : ℤ)
    (hr : r ≤ h) (hs : s ≤ h) (hh : 0 ≤ h) (I : Finset ℤ) :
    ∃ p : Plan t h, stat b c I (fun _ => 1) p = 0 ∧ stat b c I (center (t+2*h)) p ≤ 0 := by
  let pos : Plan t h := (Weights.atStep (t+h) (by omega) (by omega),
    Weights.atStep t (by omega) (by omega))
  let rev : Plan t h := (Weights.atStep (t+2*h+h) (by omega) (by omega),
    Weights.atStep (t+2*h) (by omega) (by omega))
  have pl (x : ℤ) := sharp_sign b c hr hs hh t x
  have pr (x : ℤ) := sharp_sign c b hs hr hh (t+2*h) x
  have ml : 0 ≤ stat b c I (fun _ => 1) pos := by
    exact sum_nonneg fun x _ => mul_nonneg zero_le_one (pl x).1
  have mr : 0 ≤ stat c b I (fun _ => 1) rev := by
    exact sum_nonneg fun x _ => mul_nonneg zero_le_one (pr x).1
  have cl : stat b c I (center (t+2*h)) pos ≤ 0 := by
    apply sum_nonpos
    intro x hx
    change center _ x * disc b c (step (t+h)) (step t) x ≤ 0
    by_cases hle : x ≤ t+2*h
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (by exact_mod_cast hle)) (pl x).1
    · simp [(pl x).2 (Or.inr (lt_of_not_ge hle))]
  have cr : 0 ≤ stat c b I (center (t+2*h)) rev := by
    apply sum_nonneg
    intro x hx
    change 0 ≤ center _ x * disc c b (step (t+2*h+h)) (step (t+2*h)) x
    by_cases hle : t+2*h ≤ x
    · exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hle)) (pr x).1
    · simp [(pr x).2 (Or.inl (le_of_lt (lt_of_not_ge hle)))]
  obtain ⟨k,hk,hk0⟩ := mix_zero (a := stat b c I (fun _ => 1) rev.swap)
    (by rw [stat_swap]; linarith) ml
  refine ⟨combine rev.swap pos k hk, ?_, ?_⟩
  · rwa [stat_comb]
  · rw [stat_comb, stat_swap]
    exact mix_nonpos hk (by linarith) cl

lemma cut {r s : ℤ} {q : Profile} (b : Rows r q) (c : Rows s q) (t h : ℤ)
    (hr : r ≤ h) (hs : s ≤ h) (hh : 0 ≤ h) :
    ∃ p : Plan t h, ∀ j, stat b c (Icc t (t+4*h)) (moment j) p = 0 := by
  let I := Icc t (t+4*h)
  obtain ⟨p,pm,pc⟩ := tilt b c t h hr hs hh I
  obtain ⟨v,vm,vc⟩ := tilt c b t h hs hr hh I
  obtain ⟨k,hk,hkc⟩ := mix_zero pc (b := stat b c I (center (t+2*h)) v.swap)
    (by rw [stat_swap]; linarith)
  let u := combine p v.swap k hk
  have hm : stat b c I (fun _ => 1) u = 0 := by
    simp [u, stat_comb, stat_swap, pm, vm, mix]
  have hc : stat b c I (center (t+2*h)) u = 0 := by
    simpa only [u, stat_comb] using hkc
  refine ⟨u, ?_⟩
  intro j
  cases j
  · exact hm
  · change stat b c I (fun x => (x:ℝ)) u = 0
    have he : stat b c I (center (t+2*h)) u = stat b c I (fun x => (x:ℝ)) u -
        ((t+2*h : ℤ) : ℝ) * stat b c I (fun _ => 1) u := by
      simp only [stat, integral, center, sub_mul, sum_sub_distrib, mul_sum, one_mul]
    rw [he, hm] at hc
    simpa using hc


lemma same_sum {I J : Finset ℤ} {f : ℤ → ℝ}
    (h : ∀ i, f i ≠ 0 → (i ∈ I ↔ i ∈ J)) : ∑ i ∈ I, f i = ∑ i ∈ J, f i := by
  classical
  have grow (A B : Finset ℤ) (hab : ∀ i, f i ≠ 0 → (i ∈ A ↔ i ∈ B)) :
      ∑ i ∈ A, f i = ∑ i ∈ A ∪ B, f i := by
    apply sum_subset subset_union_left
    intro i hi hn
    by_contra hv
    apply hn
    exact (hab i hv).2 ((mem_union.mp hi).resolve_left hn)
  rw [grow I J h, grow J I (fun i hi => (h i hi).symm), union_comm I J]

lemma tally_part {r : ℤ} {p : Profile} (a : Rows r p) (w : ℤ → ℝ) (l u : ℤ)
    (hw : ∀ i, w i ≠ 0 → l ≤ i ∧ i+r ≤ u) (k : Bool) (_hr : 0 ≤ r) :
    tally l u k (part a w) = ∑ i ∈ Icc l u, w i * tally i (i+r) k (a.val i) := by
  unfold tally part
  simp_rw [mul_sum]
  calc
    _ = ∑ x ∈ Icc l u, ∑ i ∈ Icc l u, moment k x * (w i * a.val i x) := by
      apply sum_congr rfl
      intro x hx
      apply same_sum
      intro i hi
      have h1 : w i ≠ 0 := by intro h; simp [h] at hi
      have h2 : a.val i x ≠ 0 := by intro h; simp [h] at hi
      have ha := a.loc i x h2
      have hb := hw i h1
      simp only [mem_Icc]
      omega
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      calc
        _ = ∑ x ∈ Icc i (i+r), moment k x * (w i * a.val i x) := by
          apply same_sum
          intro x hx
          have h1 : w i ≠ 0 := by intro h; simp [h] at hx
          have h2 : a.val i x ≠ 0 := by intro h; simp [h] at hx
          have ha := a.loc i x h2
          have hb := hw i h1
          simp only [mem_Icc]
          omega
        _ = _ := by apply sum_congr rfl; intros; ring

noncomputable def edge (h i : ℤ) := (4*h) * (i / (4*h)) + 4*h

lemma edge_bounds (i : ℤ) {h : ℤ} (hh : 0 < h) : i ≤ edge h i ∧ edge h i ≤ i+4*h := by
  have hp : 0 < 4*h := by omega
  have he := Int.emod_add_mul_ediv i (4*h)
  have hn := Int.emod_nonneg i hp.ne'
  have hl := Int.emod_lt_of_pos i hp
  unfold edge
  omega

lemma edge_jump (i : ℤ) {h : ℤ} (hh : 0 < h) :
    edge h i = edge h (i+1) ∨ edge h i + 4*h ≤ edge h (i+1) := by
  have hp : 0 < 4*h := by omega
  have he := Int.ediv_le_ediv (a := i) (b := i+1) hp (by omega)
  by_cases hq : i / (4*h) = (i+1)/(4*h)
  · left
    simp [edge, hq]
  · right
    have ht : i/(4*h) + 1 ≤ (i+1)/(4*h) := by omega
    have hm := mul_le_mul_of_nonneg_left ht hp.le
    unfold edge
    rw [mul_add, mul_one] at hm
    omega

noncomputable def increment {h : ℤ} (U : ∀ t, Weights t h) (j i : ℤ) :=
  (U (edge h (j+1))).w i - (U (edge h j)).w i

lemma incr_pos {h : ℤ} (hh : 0 < h) (U : ∀ t, Weights t h) (j i : ℤ) :
    0 ≤ increment U j i := by
  unfold increment
  rcases edge_jump j hh with he | he
  · have eqw := congrArg (fun t => (U t).w i) he
    exact sub_nonneg.mpr eqw.le
  · by_cases hx : i ≤ edge h (j+1)
    · rw [(U _).left i hx]
      linarith [(U (edge h j)).unit i]
    · rw [(U (edge h j)).right i (by omega), sub_zero]
      exact ((U _).unit i).1

lemma incr_support {r h : ℤ} (hh : 0 < h) (hr : r ≤ h) (U : ∀ t, Weights t h) (j i : ℤ)
    (hn : increment U j i ≠ 0) : j ≤ i ∧ i+r ≤ j+(8*h+1) := by
  have h0 := edge_bounds j hh
  have h1 := edge_bounds (j+1) hh
  unfold increment at hn
  constructor
  · by_contra! hx
    rw [(U _).left i (by omega), (U _).left i (by omega), sub_self] at hn
    contradiction
  · by_contra! hx
    rw [(U _).right i (by omega), (U _).right i (by omega), sub_self] at hn
    contradiction

lemma telescope (f : ℤ → ℝ) (a b : ℤ) (hab : a ≤ b) :
    ∑ i ∈ Icc a b, (f (i+1)-f i) = f (b+1)-f a := by
  rw [Int.Icc_eq_finset_map, sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
  have he := sum_range_sub (fun i : ℕ => f (a+(i:ℤ))) (b+1-a).toNat
  push_cast at he
  have hz : 0 ≤ b+1-a := by omega
  rw [Int.toNat_of_nonneg hz] at he
  simpa [← add_assoc] using he

noncomputable def makeRows {r h : ℤ} {p : Profile} (hh : 0 < h) (hr : r ≤ h) (a : Rows r p)
    (U : ∀ t, Weights t h) : Rows (8*h+1) p where
  val j := part a (increment U j)
  pos j x := sum_nonneg fun i _ => mul_nonneg (incr_pos hh U j i) (a.pos i x)
  loc j x hn := by
    by_contra hbad
    apply hn
    apply sum_eq_zero
    intro i hi
    by_contra hv
    have hw : increment U j i ≠ 0 := by intro h; simp [h] at hv
    have ha : a.val i x ≠ 0 := by intro h; simp [h] at hv
    have h1 := a.loc i x ha
    have h2 := incr_support hh hr U j i hw
    omega
  col x := by
    unfold part
    rw [sum_comm, ← a.col x]
    apply sum_congr rfl
    intro i hi
    rw [← sum_mul]
    suffices ∑ j ∈ Icc (x-(8*h+1)) x, increment U j i = 1 by rw [this, one_mul]
    unfold increment
    rw [telescope (fun j => (U (edge h j)).w i) _ _ (by omega)]
    have hxi := mem_Icc.mp hi
    have h1 := edge_bounds (x+1) hh
    have h2 := edge_bounds (x-(8*h+1)) hh
    rw [(U _).left i (by omega), (U _).right i (by omega)]
    norm_num


lemma enlarge {r s z h : ℤ} {q : Profile} (b : Rows r q) (c : Rows s q)
    (p : Plan z h) (hr : r ≤ h) (hs : s ≤ h) (l u : ℤ) (hl : l ≤ z) (hu : z+4*h ≤ u)
    (k : Bool) (hz : stat b c (Icc z (z+4*h)) (moment k) p = 0) :
    stat b c (Icc l u) (moment k) p = 0 := by
  rw [← hz]
  unfold stat integral
  apply same_sum
  intro x hx
  have hd : disc b c p.1.w p.2.w x ≠ 0 := by intro hd; simp [hd] at hx
  have hb : z ≤ x ∧ x ≤ z+4*h := by
    unfold disc at hd
    constructor
    · by_contra! hlt
      rw [early b (fun i hi => p.1.left i (by omega)),
        early c (fun i hi => p.2.left i (by omega)), sub_self] at hd
      contradiction
    · by_contra! hlt
      rw [late b (fun i hi => p.1.right i (by omega)),
        late c (fun i hi => p.2.right i (by omega)), sub_self] at hd
      contradiction
  simp only [mem_Icc]
  omega

lemma middle {r s h : ℤ} {q : Profile} (b : Rows r q) (c : Rows s q)
    (P : ∀ t, Plan t h) (hr : r ≤ h) (hs : s ≤ h) (hh : 0 < h)
    (hb : ∀ t k, stat b c (Icc t (t+4*h)) (moment k) (P t) = 0) (j : ℤ) (k : Bool) :
    tally j (j+(8*h+1)) k (part b (increment (fun t => (P t).1) j)) =
    tally j (j+(8*h+1)) k (part c (increment (fun t => (P t).2) j)) := by
  let I := Icc j (j+(8*h+1))
  have h0 := edge_bounds j hh
  have h1 := edge_bounds (j+1) hh
  have zero0 : stat b c I (moment k) (P (edge h j)) = 0 :=
    enlarge b c _ hr hs _ _ (by omega) (by omega) _ (hb _ _)
  have zero1 : stat b c I (moment k) (P (edge h (j+1))) = 0 :=
    enlarge b c _ hr hs _ _ (by omega) (by omega) _ (hb _ _)
  have he : tally j (j+(8*h+1)) k (part b (increment (fun t => (P t).1) j)) -
      tally j (j+(8*h+1)) k (part c (increment (fun t => (P t).2) j)) =
      stat b c I (moment k) (P (edge h (j+1))) - stat b c I (moment k) (P (edge h j)) := by
    unfold tally increment stat integral disc
    simp only [part_sub, ← sum_sub_distrib, I]
    apply sum_congr rfl
    intros
    ring
  linarith

lemma transport {r s h : ℤ} {p q v : Profile} (a : Rows r p) (b : Rows r q)
    (c : Rows s q) (e : Rows s v) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s) (hh : 0 < h)
    (hr : r ≤ h) (hs : s ≤ h)
    (hab : ∀ i k, tally i (i+r) k (a.val i) = tally i (i+r) k (b.val i))
    (hce : ∀ i k, tally i (i+s) k (c.val i) = tally i (i+s) k (e.val i)) :
    ∃ (A : Rows (8*h+1) p) (E : Rows (8*h+1) v), ∀ i k,
      tally i (i+(8*h+1)) k (A.val i) = tally i (i+(8*h+1)) k (E.val i) := by
  classical
  choose P hp using fun t => cut b c t h hr hs hh.le
  let U := fun t => (P t).1
  let V := fun t => (P t).2
  refine ⟨makeRows hh hr a U, makeRows hh hs e V, ?_⟩
  intro i k
  change tally _ _ _ (part a (increment U i)) = tally _ _ _ (part e (increment V i))
  calc
    _ = tally i (i+(8*h+1)) k (part b (increment U i)) := by
      rw [tally_part a _ _ _ (incr_support hh hr U i) k hr0,
        tally_part b _ _ _ (incr_support hh hr U i) k hr0]
      simp only [hab]
    _ = tally i (i+(8*h+1)) k (part c (increment V i)) := middle b c P hr hs hh hp i k
    _ = _ := by
      rw [tally_part c _ _ _ (incr_support hh hs V i) k hs0,
        tally_part e _ _ _ (incr_support hh hs V i) k hs0]
      simp only [hce]


end Propp

theorem OMA.solution : type_of% @OMA.S_mo_202165.main := by
  intro p q v hp hq
  obtain ⟨r,hr,a,b,hab⟩ := hp
  obtain ⟨s,hs,c,e,hce⟩ := hq
  let h := max r s + 1
  have hh : 0 < h := by dsimp [h]; omega
  exact ⟨8*h+1, by omega, Propp.transport a b c e hr hs hh
    (by dsimp [h]; omega) (by dsimp [h]; omega) hab hce⟩
