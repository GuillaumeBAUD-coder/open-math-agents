import FormalConjectures.ErdosProblems.«1147»

/-! Odd numerator approximations with prime denominators. The second moment
of the hit count is controlled by an injective map from intersecting pairs of
intervals to their integer separations. The resulting metric approximation
gives the additive-basis obstruction of Konieczny, arXiv:1504.02410. -/

open MeasureTheory Set Finset Filter
open scoped Topology ENNReal

noncomputable section

namespace RecurrencePrime

def unitMeasure : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unitMeasure := by
  constructor
  simp [unitMeasure,Real.volume_Icc]

def centre (q : ℕ) (i : Fin q) : ℝ := ((i : ℕ)+1/2)/(q:ℝ)
def radius (c : ℝ) (q : ℕ) : ℝ := c / (q:ℝ)^2
def cell (c : ℝ) (q : ℕ) (i : Fin q) : Set ℝ :=
  Ioo (centre q i - radius c q) (centre q i + radius c q)
def event (c : ℝ) (q : ℕ) : Set ℝ := ⋃ i : Fin q, cell c q i

lemma event_measurable (c : ℝ) (q : ℕ) : MeasurableSet (event c q) :=
  MeasurableSet.iUnion fun _ ↦ measurableSet_Ioo

lemma radius_le {c : ℝ} (hc : c ≤ 1/2) {q : ℕ} (hq : 0 < q) :
    radius c q ≤ (1/2)/(q:ℝ) := by
  have hqR : 0 < (q:ℝ) := by exact_mod_cast hq
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  unfold radius
  apply (div_le_iff₀ (sq_pos_of_pos hqR)).2
  rw [pow_two, ← mul_assoc, div_mul_cancel₀ _ hqR.ne']
  linarith

lemma cell_subset {c : ℝ} (hc : c ≤ 1/2) {q : ℕ} (hq : 0 < q) (i : Fin q) :
    cell c q i ⊆ Icc (0:ℝ) 1 := by
  have hqR : 0 < (q:ℝ) := by exact_mod_cast hq
  have hLo : (1/2)/(q:ℝ) ≤ centre q i := by
    apply div_le_div_of_nonneg_right _ hqR.le
    have hi : 0 ≤ ((i:ℕ):ℝ) := by positivity
    linarith
  have hHi : centre q i + (1/2)/(q:ℝ) ≤ 1 := by
    rw [centre, ← add_div]
    apply (div_le_iff₀ hqR).2
    have hi : (i:ℕ)+1 ≤ q := i.isLt
    have hu : ((i:ℕ):ℝ)+1 ≤ q := by exact_mod_cast hi
    linarith
  intro x hx
  change centre q i - radius c q < x ∧ x < centre q i + radius c q at hx
  exact ⟨by linarith [hx.1,radius_le hc hq],by linarith [hx.2,radius_le hc hq]⟩

lemma cell_measure {c : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1/2) {q : ℕ} (hq : 0 < q)
    (i : Fin q) : unitMeasure.real (cell c q i) = 2*radius c q := by
  rw [measureReal_def,unitMeasure,Measure.restrict_apply (show MeasurableSet (cell c q i) from measurableSet_Ioo),
    inter_eq_left.mpr (cell_subset hc' hq i),cell,Real.volume_Ioo,ENNReal.toReal_ofReal]
  · ring
  · have hr : 0 ≤ radius c q := by unfold radius; positivity
    linarith

lemma cell_disjoint {c : ℝ} (hc : c ≤ 1/2) {q : ℕ} (hq : 0 < q) :
    Pairwise (fun i j : Fin q ↦ Disjoint (cell c q i) (cell c q j)) := by
  intro i j hij
  have hNear (x : ℝ) (hi : x ∈ cell c q i) (hj : x ∈ cell c q j) :
      |centre q i - centre q j| < 2*radius c q := by
    apply abs_lt.mpr
    change centre q i - radius c q < x ∧ x < centre q i + radius c q at hi
    change centre q j - radius c q < x ∧ x < centre q j + radius c q at hj
    constructor <;> linarith [hi.1,hi.2,hj.1,hj.2]
  rw [Set.disjoint_left]
  intro x hi hj
  have h := hNear x hi hj
  have hqR : 0 < (q:ℝ) := by exact_mod_cast hq
  have hgap : (1:ℝ) ≤ |((i:ℕ):ℝ) - ((j:ℕ):ℝ)| := by
    have hne : (i:ℕ) ≠ (j:ℕ) := fun he ↦ hij (Fin.ext he)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hh : (i:ℕ)+1 ≤ (j:ℕ) := hlt
      have hu : ((i:ℕ):ℝ)+1 ≤ (j:ℕ) := by exact_mod_cast hh
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hh : (j:ℕ)+1 ≤ (i:ℕ) := hlt
      have hu : ((j:ℕ):ℝ)+1 ≤ (i:ℕ) := by exact_mod_cast hh
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hm : 1/(q:ℝ) ≤ |centre q i - centre q j| := by
    unfold centre
    rw [← sub_div,abs_div,abs_of_pos hqR]
    apply div_le_div_of_nonneg_right _ hqR.le
    have he : ((i:ℕ):ℝ) + 1/2 - (((j:ℕ):ℝ)+1/2) =
        ((i:ℕ):ℝ)-((j:ℕ):ℝ) := by ring
    rwa [he]
  have hcap : 2*radius c q ≤ 1/(q:ℝ) := by
    calc
      _ ≤ 2*((1/2)/(q:ℝ)) := mul_le_mul_of_nonneg_left (radius_le hc hq) (by norm_num)
      _ = _ := by ring
  exact (hcap.trans hm).not_gt h

lemma event_measure {c : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1/2) {q : ℕ} (hq : 0 < q) :
    unitMeasure.real (event c q) = 2*c/(q:ℝ) := by
  unfold event
  rw [measureReal_iUnion_fintype (μ := unitMeasure) (f := cell c q)
    (cell_disjoint hc' hq) (fun _ ↦ measurableSet_Ioo)]
  simp_rw [cell_measure hc hc' hq]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hqR : (q:ℝ) ≠ 0 := by positivity
  unfold radius
  field_simp [hqR]

def separation {p q : ℕ} (ij : Fin p × Fin q) : ℤ :=
  (q:ℤ)*(ij.1:ℕ) - (p:ℤ)*(ij.2:ℕ) + ((q:ℤ)-(p:ℤ))/2

lemma separation_injective {p q : ℕ} (hp : 0 < p) (_hq : 0 < q) (hcop : p.Coprime q) :
    Function.Injective (separation (p:=p) (q:=q)) := by
  intro i j hij
  have hGcd : Int.gcd (p:ℤ) (q:ℤ) = 1 := by simpa [Nat.Coprime] using hcop
  have hd : (p:ℤ) ∣ (q:ℤ)*(((i.1:ℕ):ℤ) - ((j.1:ℕ):ℤ)) := by
    refine ⟨((i.2:ℕ):ℤ)-((j.2:ℕ):ℤ),?_⟩
    unfold separation at hij
    linear_combination hij
  have hd' := Int.dvd_of_dvd_mul_right_of_gcd_one hd hGcd
  have hAbs : |((i.1:ℕ):ℤ)-((j.1:ℕ):ℤ)| < (p:ℤ) := by
    have hi := i.1.isLt
    have hj := j.1.isLt
    exact abs_lt.mpr ⟨by omega,by omega⟩
  have hzero : ((i.1:ℕ):ℤ)-((j.1:ℕ):ℤ) = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd'
    omega
  have hi : i.1 = j.1 := by apply Fin.ext; omega
  have hj : i.2 = j.2 := by
    unfold separation at hij
    rw [hi] at hij
    have hh : (p:ℤ)*((i.2:ℕ):ℤ) = (p:ℤ)*((j.2:ℕ):ℤ) := by omega
    have hh' := mul_left_cancel₀ (by positivity : (p:ℤ) ≠ 0) hh
    exact Fin.ext (by exact_mod_cast hh')
  exact Prod.ext hi hj

lemma separation_eq {p q : ℕ} (hp : Odd p) (hq : Odd q) (ij : Fin p × Fin q) :
    (separation ij : ℝ) = (p:ℝ)*(q:ℝ)*(centre p ij.1-centre q ij.2) := by
  have hpR : (p:ℝ) ≠ 0 := by have := hp.pos; positivity
  have hqR : (q:ℝ) ≠ 0 := by have := hq.pos; positivity
  have hdiv : (2:ℤ) ∣ (q:ℤ)-(p:ℤ) := by
    obtain ⟨u,hu⟩ := hp
    obtain ⟨v,hv⟩ := hq
    exact ⟨(v:ℤ)-(u:ℤ),by omega⟩
  have hhalf : (((((q:ℤ)-(p:ℤ))/2):ℤ):ℝ) = ((q:ℝ)-(p:ℝ))/2 := by
    apply (eq_div_iff (by norm_num : (2:ℝ) ≠ 0)).2
    exact_mod_cast Int.ediv_mul_cancel hdiv
  unfold separation centre
  push_cast
  rw [hhalf]
  field_simp [hpR,hqR]
  ring

lemma joint_measure {c : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1/2) {p q : ℕ}
    (hp : Odd p) (hq : Odd q) (hcop : p.Coprime q) :
    unitMeasure.real (event c p ∩ event c q) ≤
      (2*c/(p:ℝ))*(2*c/(q:ℝ)) + 4*c^2*(p:ℝ)/(q:ℝ)^3 + 2*c/(q:ℝ)^2 := by
  classical
  have hpR : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have hqR : 0 < (q:ℝ) := by exact_mod_cast hq.pos
  let S : Finset (Fin p × Fin q) :=
    univ.filter fun ij ↦ (cell c p ij.1 ∩ cell c q ij.2).Nonempty
  let X := c*((q:ℝ)/p+(p:ℝ)/q)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hs : Set.InjOn separation (↑S : Set (Fin p × Fin q)) :=
    (separation_injective hp.pos hq.pos hcop).injOn
  have hdist (ij : Fin p × Fin q) (hij : ij ∈ S) : |(separation ij : ℝ)| ≤ X := by
    obtain ⟨x,ha,hb⟩ := (Finset.mem_filter.mp hij).2
    change centre p ij.1 - radius c p < x ∧ x < centre p ij.1 + radius c p at ha
    change centre q ij.2 - radius c q < x ∧ x < centre q ij.2 + radius c q at hb
    have h : |centre p ij.1-centre q ij.2| ≤ radius c p + radius c q :=
      abs_le.mpr ⟨by linarith [ha.1,hb.2],by linarith [ha.2,hb.1]⟩
    rw [separation_eq hp hq,abs_mul,abs_of_pos (mul_pos hpR hqR)]
    calc
      _ ≤ (p:ℝ)*(q:ℝ)*(radius c p + radius c q) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = X := by dsimp [X,radius]; field_simp
  have hcount : (S.card : ℝ) ≤ 2*X+1 := by
    let T := Finset.Icc (-⌊X⌋) ⌊X⌋
    have hcard : S.card ≤ T.card := Finset.card_le_card_of_injOn separation (by
      intro ij hij
      have hh := abs_le.mp (hdist ij (Finset.mem_coe.mp hij))
      apply Finset.mem_Icc.mpr
      constructor
      · have hlow : -(separation ij) ≤ ⌊X⌋ := by
          apply Int.le_floor.mpr
          push_cast
          linarith [hh.1]
        omega
      · exact Int.le_floor.mpr hh.2) hs
    have hT : (T.card : ℝ) ≤ 2*X+1 := by
      have hfloor : 0 ≤ ⌊X⌋ := Int.floor_nonneg.mpr hX
      have he : (T.card : ℤ) = 2*⌊X⌋+1 := by
        unfold T
        rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]
        omega
      have heR : (T.card : ℝ) = 2*(⌊X⌋:ℝ)+1 := by exact_mod_cast he
      linarith [Int.floor_le X]
    exact (by exact_mod_cast hcard : (S.card : ℝ) ≤ T.card).trans hT
  have hsub : event c p ∩ event c q ⊆ ⋃ ij ∈ S, cell c p ij.1 ∩ cell c q ij.2 := by
    intro x hx
    obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := (show x ∈ event c p ∧ x ∈ event c q from hx)
      |> And.imp Set.mem_iUnion.mp Set.mem_iUnion.mp
    exact Set.mem_iUnion₂.mpr ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,hi,hj⟩,hi,hj⟩
  have hmass : unitMeasure.real (event c p ∩ event c q) ≤ (S.card : ℝ)*(2*radius c q) := by
    calc
      _ ≤ unitMeasure.real (⋃ ij ∈ S, cell c p ij.1 ∩ cell c q ij.2) := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ ij ∈ S, unitMeasure.real (cell c p ij.1 ∩ cell c q ij.2) :=
        measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _ij ∈ S, 2*radius c q := by
        apply Finset.sum_le_sum
        intro ij _
        rw [← cell_measure hc hc' hq.pos ij.2]
        exact measureReal_mono inter_subset_right
      _ = _ := by simp
  refine hmass.trans ((mul_le_mul_of_nonneg_right hcount (by unfold radius; positivity)).trans_eq ?_)
  dsimp [X,radius]
  field_simp
  ring

end RecurrencePrime

namespace RecurrencePrime

def hit (c : ℝ) (q : ℕ) : ℝ → ℝ := (event c q).indicator fun _ ↦ 1

lemma hit_measurable (c : ℝ) (q : ℕ) : Measurable (hit c q) :=
  measurable_const.indicator (event_measurable _ _)

lemma hit_mem (c : ℝ) (q : ℕ) (x : ℝ) : hit c q x ∈ Icc (0 : ℝ) 1 := by
  by_cases h : x ∈ event c q <;> simp [hit,h]

lemma hit_integrable (c : ℝ) (q : ℕ) : Integrable (hit c q) unitMeasure :=
  Integrable.of_mem_Icc 0 1 (hit_measurable c q).aemeasurable (Eventually.of_forall (hit_mem c q))

lemma integral_hit (c : ℝ) (q : ℕ) :
    (∫ x, hit c q x ∂unitMeasure) = unitMeasure.real (event c q) := by
  rw [hit,integral_indicator_const _ (event_measurable _ _),smul_eq_mul,mul_one]

lemma hit_pow (c : ℝ) (q : ℕ) (x : ℝ) : hit c q x ^ 2 = hit c q x := by
  by_cases h : x ∈ event c q <;> simp [hit,h]

lemma hit_mul (c : ℝ) (p q : ℕ) (x : ℝ) :
    hit c p x * hit c q x = (event c p ∩ event c q).indicator (fun _ ↦ (1:ℝ)) x := by
  by_cases hp : x ∈ event c p <;> by_cases hq : x ∈ event c q <;> simp [hit,hp,hq]

def totalHit (c : ℝ) (s : Finset ℕ) (x : ℝ) : ℝ := ∑ q ∈ s, hit c q x

def meanHit (c : ℝ) (s : Finset ℕ) : ℝ := ∑ q ∈ s, 2*c/(q:ℝ)

lemma total_measurable (c : ℝ) (s : Finset ℕ) : Measurable (totalHit c s) := by
  unfold totalHit
  exact Finset.measurable_sum _ fun q _ ↦ hit_measurable _ _

lemma total_mem (c : ℝ) (s : Finset ℕ) (x : ℝ) : totalHit c s x ∈ Icc (0:ℝ) (s.card : ℝ) := by
  constructor
  · exact Finset.sum_nonneg fun q _ ↦ (hit_mem c q x).1
  · calc
      _ ≤ ∑ _q ∈ s, (1:ℝ) := Finset.sum_le_sum fun q _ ↦ (hit_mem c q x).2
      _ = _ := by simp

lemma total_integrable (c : ℝ) (s : Finset ℕ) :
    Integrable (totalHit c s) unitMeasure :=
  Integrable.of_mem_Icc 0 s.card (total_measurable c s).aemeasurable
    (Eventually.of_forall (total_mem c s))

lemma total_sq_integrable (c : ℝ) (s : Finset ℕ) :
    Integrable (fun x ↦ totalHit c s x ^ 2) unitMeasure :=
  Integrable.of_mem_Icc 0 ((s.card:ℝ)^2) ((total_measurable c s).pow_const _).aemeasurable
    (Eventually.of_forall fun x ↦ ⟨sq_nonneg _,pow_le_pow_left₀ (total_mem c s x).1
      (total_mem c s x).2 _⟩)

lemma total_mul_integrable (c : ℝ) (s : Finset ℕ) (q : ℕ) :
    Integrable (fun x ↦ totalHit c s x * hit c q x) unitMeasure :=
  Integrable.of_mem_Icc 0 s.card ((total_measurable c s).mul (hit_measurable c q)).aemeasurable
    (Eventually.of_forall fun x ↦ ⟨mul_nonneg (total_mem c s x).1 (hit_mem c q x).1,
      (mul_le_mul (total_mem c s x).2 (hit_mem c q x).2 (hit_mem c q x).1
        (by positivity)).trans_eq (mul_one _)⟩)

lemma integral_total {c : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1/2) (s : Finset ℕ)
    (hs : ∀ q ∈ s, 0 < q) :
    (∫ x, totalHit c s x ∂unitMeasure) = meanHit c s := by
  unfold totalHit meanHit
  rw [integral_finsetSum _ (fun q _ ↦ hit_integrable _ _)]
  apply Finset.sum_congr rfl
  intro q hq
  rw [integral_hit,event_measure hc hc' (hs q hq)]

lemma integral_total_mul (c : ℝ) (s : Finset ℕ) (q : ℕ) :
    (∫ x, totalHit c s x * hit c q x ∂unitMeasure) =
      ∑ p ∈ s, unitMeasure.real (event c p ∩ event c q) := by
  simp_rw [totalHit,Finset.sum_mul,hit_mul]
  rw [integral_finsetSum _ (fun p _ ↦ (integrable_const _).indicator
    ((event_measurable _ _).inter (event_measurable _ _)))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_indicator_const _ ((event_measurable _ _).inter (event_measurable _ _)),smul_eq_mul,mul_one]

lemma total_pair_bound {c : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1/2) (s : Finset ℕ)
    {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q)
    (hs : ∀ p ∈ s, p.Prime ∧ 3 ≤ p ∧ p < q) :
    (∫ x, totalHit c s x * hit c q x ∂unitMeasure) ≤
      meanHit c s * (2*c/(q:ℝ)) + 2*(2*c/(q:ℝ)) := by
  rw [integral_total_mul]
  have hqR : 0 < (q:ℝ) := by exact_mod_cast hq.pos
  have hqOdd := hq.odd_of_ne_two (by omega)
  have hcard : (s.card : ℝ) ≤ (q : ℝ) := by
    have he : s ⊆ Finset.range q := fun p hp ↦ Finset.mem_range.mpr (hs p hp).2.2
    exact_mod_cast (Finset.card_le_card he).trans_eq (Finset.card_range q)
  let E := (4*c^2+2*c)/(q:ℝ)^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  calc
    _ ≤ ∑ p ∈ s, ((2*c/(p:ℝ))*(2*c/(q:ℝ)) + E) := by
      apply Finset.sum_le_sum
      intro p hp
      have ⟨hpp,hp3,hlt⟩ := hs p hp
      have hcop : p.Coprime q := hpp.coprime_iff_not_dvd.mpr fun h ↦
        (hpp.ne_one ((Nat.dvd_prime hq).mp h |>.resolve_right hlt.ne))
      apply (joint_measure hc hc' (hpp.odd_of_ne_two (by omega)) hqOdd hcop).trans
      rw [add_assoc]
      apply add_le_add le_rfl
      dsimp [E]
      have hppR : (p:ℝ) ≤ q := by exact_mod_cast hlt.le
      have h := (mul_le_mul_of_nonneg_left hppR (by positivity : 0 ≤ 4*c^2))
      have hm := div_le_div_of_nonneg_right h (by positivity : 0 ≤ (q:ℝ)^3)
      have he : 4*c^2*(q:ℝ)/(q:ℝ)^3 = 4*c^2/(q:ℝ)^2 := by
        field_simp
      rw [he] at hm
      rw [add_div]
      exact add_le_add hm le_rfl
    _ = meanHit c s * (2*c/(q:ℝ)) + (s.card:ℝ)*E := by
      simp [Finset.sum_add_distrib,← Finset.sum_mul,meanHit]
    _ ≤ _ := by
      apply add_le_add le_rfl
      refine (mul_le_mul_of_nonneg_right hcard hE).trans ?_
      dsimp [E]
      have he : (q:ℝ)*((4*c^2+2*c)/(q:ℝ)^2) = (4*c^2+2*c)/(q:ℝ) := by
        field_simp
      rw [he,← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hqR.le
      have h := mul_le_mul_of_nonneg_left hc' (show 0 ≤ 4*c by positivity)
      nlinarith

lemma total_second_moment {c : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1/2) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 3 ≤ p) :
    (∫ x, totalHit c s x ^ 2 ∂unitMeasure) ≤ (meanHit c s)^2 + 5*meanHit c s := by
  induction s using Finset.induction_on_max with
  | empty => simp [meanHit,totalHit]
  | insert q s hlt ih =>
    have hqnot : q ∉ s := fun h ↦ (hlt q h).false
    have hq := hs q (Finset.mem_insert_self _ _)
    have hs' p hp := hs p (Finset.mem_insert_of_mem hp)
    have h2 := ih hs'
    have h3 := total_pair_bound hc hc' s hq.1 hq.2 fun p hp ↦
      ⟨(hs' p hp).1,(hs' p hp).2,hlt p hp⟩
    have hmean : meanHit c (insert q s) = 2*c/(q:ℝ)+meanHit c s := by
      rw [meanHit,Finset.sum_insert hqnot]
      rfl
    have hExpand : (fun x ↦ totalHit c (insert q s) x ^ 2) =
        fun x ↦ (totalHit c s x ^ 2 + 2*(totalHit c s x * hit c q x)) + hit c q x := by
      funext x
      rw [totalHit,Finset.sum_insert hqnot,← totalHit,add_sq,hit_pow]
      ring
    have iA : Integrable (fun x ↦ totalHit c s x^2) unitMeasure := total_sq_integrable c s
    have iB : Integrable (fun x ↦ 2*(totalHit c s x * hit c q x)) unitMeasure :=
      (total_mul_integrable c s q).const_mul 2
    have iAB : Integrable (fun x ↦ totalHit c s x^2 + 2*(totalHit c s x * hit c q x))
        unitMeasure := iA.add iB
    rw [hmean,hExpand,integral_add iAB (hit_integrable c q),integral_add iA iB,
      integral_const_mul,integral_hit,event_measure hc hc' hq.1.pos]
    nlinarith only [h2,h3,sq_nonneg (2*c/(q:ℝ))]

end RecurrencePrime

namespace RecurrencePrime

lemma arbitrarily_large_mean {c : ℝ} (hc : 0 < c) (B : ℕ) (T : ℝ) :
    ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ B ≤ p) ∧ T < meanHit c s := by
  classical
  let f (p : ℕ) := if p.Prime ∧ B ≤ p then 1/(p:ℝ) else 0
  let g (p : ℕ) := if p.Prime ∧ p < B then 1/(p:ℝ) else 0
  have hg : Summable g := summable_of_ne_finset_zero (s := Finset.range B) fun p hp ↦ by
    simp only [Finset.mem_range,not_lt] at hp
    simp [g,not_lt.mpr hp]
  have hnot : ¬ Summable f := by
    intro hs
    apply not_summable_one_div_on_primes
    have he : (fun p ↦ f p+g p) =
        Set.indicator {p : ℕ | p.Prime} (fun p ↦ 1/(p:ℝ)) := by
      funext p
      by_cases hP : p.Prime <;> by_cases hB : B ≤ p <;>
        simp [f,g,hP,hB,not_lt.mpr,lt_of_not_ge]
    rw [← he]
    exact hs.add hg
  obtain ⟨s,hs⟩ : ∃ s : Finset ℕ, T/(2*c) < ∑ p ∈ s, f p := by
    by_contra h
    push Not at h
    exact hnot (summable_of_sum_le (by intro p; simp [f]; split_ifs <;> positivity) h)
  let t := s.filter (fun p ↦ p.Prime ∧ B ≤ p)
  have hmean : meanHit c t = (2*c)*∑ p ∈ s, f p := by
    unfold meanHit
    rw [Finset.mul_sum,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : p.Prime ∧ B ≤ p <;> simp [f,h,div_eq_mul_inv]
  refine ⟨t,fun p hp ↦ (Finset.mem_filter.mp hp).2,?_⟩
  rw [hmean,mul_comm]
  exact (div_lt_iff₀ (by positivity)).mp hs

lemma ae_event_tail {c : ℝ} (hc : 0 < c) (hc' : c ≤ 1/2) (B : ℕ) :
    ∀ᵐ x ∂unitMeasure, ∃ q : ℕ, q.Prime ∧ max B 3 ≤ q ∧ x ∈ event c q := by
  classical
  let P (q : ℕ) := q.Prime ∧ max B 3 ≤ q
  let W := (⋃ q : Subtype P, event c q)ᶜ
  have hW : MeasurableSet W := (MeasurableSet.iUnion (fun _ ↦ event_measurable _ _)).compl
  have hNo (x : ℝ) (hx : x ∈ W) (q : ℕ) (hq : P q) : x ∉ event c q := by
    intro hm
    exact hx (Set.mem_iUnion.mpr ⟨⟨q,hq⟩,hm⟩)
  have hμ : unitMeasure.real W = 0 := by
    by_contra h
    have hpos : 0 < unitMeasure.real W := lt_of_le_of_ne measureReal_nonneg (Ne.symm h)
    obtain ⟨s,hs,hmean⟩ := arbitrarily_large_mean hc (max B 3) (5 / unitMeasure.real W)
    let M := meanHit c s
    have hM : 0 < M := (div_pos (by norm_num) hpos).trans hmean
    have hZ : (∫ x, totalHit c s x ∂unitMeasure) = M :=
      integral_total hc.le hc' s (fun p hp ↦ (hs p hp).1.pos)
    have hZ₂ := total_second_moment hc.le hc' s
      (fun p hp ↦ ⟨(hs p hp).1,le_trans (le_max_right B 3) (hs p hp).2⟩)
    change (∫ x, totalHit c s x ^ 2 ∂unitMeasure) ≤ M^2 + 5*M at hZ₂
    have hi : Integrable (fun x ↦ (totalHit c s x - M)^2) unitMeasure := by
      have he : (fun x ↦ (totalHit c s x - M)^2) =
          fun x ↦ totalHit c s x ^ 2 - 2*M*totalHit c s x + M^2 := by funext x; ring
      rw [he]
      exact ((total_sq_integrable _ _).sub ((total_integrable _ _).const_mul _)).add
        (integrable_const _)
    have hL : M^2 * unitMeasure.real W ≤ ∫ x, (totalHit c s x - M)^2 ∂unitMeasure := by
      rw [mul_comm, ← smul_eq_mul, ← integral_indicator_const (μ := unitMeasure) (M^2) hW]
      apply integral_mono ((integrable_const _).indicator hW) hi
      intro x
      by_cases hx : x ∈ W
      · have hzero : totalHit c s x = 0 := by
          unfold totalHit
          exact Finset.sum_eq_zero fun q hq ↦ by simp [hit,hNo x hx q (hs q hq)]
        simp [hx,hzero]
      · simpa only [Set.indicator_of_notMem hx] using sq_nonneg (totalHit c s x-M)
    have hR : (∫ x, (totalHit c s x - M)^2 ∂unitMeasure) ≤ 5*M := by
      have he : (fun x ↦ (totalHit c s x - M)^2) =
          fun x ↦ totalHit c s x ^ 2 - 2*M*totalHit c s x + M^2 := by funext x; ring
      have iA : Integrable (fun x ↦ totalHit c s x^2) unitMeasure := total_sq_integrable c s
      have iB : Integrable (fun x ↦ 2*M*totalHit c s x) unitMeasure :=
        (total_integrable c s).const_mul _
      have iAB : Integrable (fun x ↦ totalHit c s x^2 - 2*M*totalHit c s x)
          unitMeasure := iA.sub iB
      rw [he,integral_add iAB (show Integrable (fun _ : ℝ ↦ M^2) unitMeasure from
        integrable_const _),integral_sub iA iB,integral_const_mul,hZ,integral_const]
      simp [measureReal_def]
      linarith only [hZ₂]
    have hm : 5 < M * unitMeasure.real W := (div_lt_iff₀ hpos).mp hmean
    have hContra := mul_lt_mul_of_pos_left hm hM
    have hBound := hL.trans hR
    nlinarith only [hContra,hBound]
  have hzero : unitMeasure W = 0 := (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hμ
  apply ae_iff.mpr
  have he : {x : ℝ | ¬ ∃ q : ℕ, q.Prime ∧ max B 3 ≤ q ∧ x ∈ event c q} = W := by
    ext x
    simp [W,P,and_assoc]
  rw [he]
  exact hzero

def Approximable (x : ℝ) : Prop :=
  ∀ B m : ℕ, ∃ q : ℕ, q.Prime ∧ max B 3 ≤ q ∧
    ∃ a : ℤ, Odd a ∧ |(q:ℝ)*x-(a:ℝ)/2| < (1 / ((m:ℝ)+2))/(q:ℝ)

lemma ae_approx_unit : ∀ᵐ x ∂unitMeasure, Approximable x := by
  unfold Approximable
  rw [ae_all_iff]
  intro B
  rw [ae_all_iff]
  intro m
  let c : ℝ := 1 / ((m:ℝ)+2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc' : c ≤ 1/2 := by
    dsimp [c]
    apply one_div_le_one_div_of_le (by norm_num)
    have hm : 0 ≤ (m:ℝ) := by positivity
    linarith
  filter_upwards [ae_event_tail hc hc' B] with x hx
  obtain ⟨q,hq,hqB,hx⟩ := hx
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
  let a : ℤ := 2*((i:ℕ):ℤ)+1
  refine ⟨q,hq,hqB,a,⟨(i:ℕ),by ring⟩,?_⟩
  have hqR : 0 < (q:ℝ) := by exact_mod_cast hq.pos
  have hEq : (a:ℝ)/2 = (q:ℝ)*centre q i := by
    unfold a centre
    push_cast
    field_simp
  have h : |x-centre q i| < radius c q :=
    abs_lt.mpr ⟨by linarith [hi.1],by linarith [hi.2]⟩
  rw [hEq,← mul_sub,abs_mul,abs_of_pos hqR]
  have h' := mul_lt_mul_of_pos_left h hqR
  change (q:ℝ)*|x-centre q i| < c/(q:ℝ)
  have he : (q:ℝ)*radius c q = c/(q:ℝ) := by
    unfold radius
    field_simp
  rwa [he] at h'

lemma approx_int_translate {x : ℝ} (h : Approximable x) (z : ℤ) :
    Approximable (x+z) := by
  intro B m
  obtain ⟨q,hq,hqB,p,hp,herr⟩ := h B m
  refine ⟨q,hq,hqB,p+2*z*(q:ℤ),?_,?_⟩
  · obtain ⟨u,hu⟩ := hp
    refine ⟨u+z*(q:ℤ),?_⟩
    rw [hu]
    ring
  · push_cast
    convert herr using 2; ring

lemma ae_approx : ∀ᵐ x : ℝ, Approximable x := by
  have h : ∀ᵐ x : ℝ, x ∈ Icc (0:ℝ) 1 → Approximable x :=
    (ae_restrict_iff' measurableSet_Icc).mp ae_approx_unit
  have hz (z : ℤ) : ∀ᵐ x : ℝ, x - z ∈ Icc (0:ℝ) 1 → Approximable (x-z) := by
    have hpres := measurePreserving_add_right (volume : Measure ℝ) (-(z:ℝ))
    have h' : ∀ᵐ x ∂(volume : Measure ℝ).map (fun x ↦ x+(-(z:ℝ))),
        x ∈ Icc (0:ℝ) 1 → Approximable x := by rw [hpres.map_eq]; exact h
    simpa [sub_eq_add_neg] using ae_of_ae_map hpres.measurable.aemeasurable h'
  have hAll : ∀ᵐ x : ℝ, ∀ z : ℤ, x-z ∈ Icc (0:ℝ) 1 → Approximable (x-z) :=
    ae_all_iff.mpr hz
  filter_upwards [hAll] with x hx
  have hIx : x-(⌊x⌋:ℝ) ∈ Icc (0:ℝ) 1 := ⟨sub_nonneg.mpr (Int.floor_le _),
    by have := Int.lt_floor_add_one x; linarith⟩
  have hApp := approx_int_translate (hx ⌊x⌋ hIx) ⌊x⌋
  simpa only [sub_add_cancel] using hApp

end RecurrencePrime

namespace RecurrencePrime

open scoped Pointwise

private lemma irrational_gap {x : ℝ} (hx : Irrational x) :
    ∃ d > (0:ℝ), ∀ z : ℤ, d ≤ |x-z| := by
  have hl : (⌊x⌋:ℝ) < x := lt_of_le_of_ne (Int.floor_le _) (hx.ne_int _).symm
  have hu : x < (⌊x⌋:ℝ)+1 := Int.lt_floor_add_one _
  refine ⟨min (x-(⌊x⌋:ℝ)) ((⌊x⌋:ℝ)+1-x),lt_min (sub_pos.mpr hl) (sub_pos.mpr hu),?_⟩
  intro z
  by_cases hz : z ≤ ⌊x⌋
  · have h : (z:ℝ) ≤ ⌊x⌋ := by exact_mod_cast hz
    rw [abs_of_nonneg (by linarith)]
    exact (min_le_left _ _).trans (by linarith)
  · have hz' : ⌊x⌋+1 ≤ z := by omega
    have h : (⌊x⌋:ℝ)+1 ≤ z := by exact_mod_cast hz'
    rw [abs_of_nonpos (by linarith)]
    exact (min_le_right _ _).trans (by linarith)

private lemma half_gap (z : ℤ) : (1/2:ℝ) ≤ |(z:ℝ)-1/2| := by
  by_cases hz : z ≤ 0
  · have h : (z:ℝ) ≤ 0 := by exact_mod_cast hz
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hz' : 1 ≤ z := by omega
    have h : (1:ℝ) ≤ z := by exact_mod_cast hz'
    rw [abs_of_nonneg (by linarith)]
    linarith

private lemma uniform_gap {α : ℝ} (hi : Irrational α) (N : ℕ) :
    ∃ d > (0:ℝ), ∀ n : ℕ, 1 ≤ n → n ≤ N → ∀ z : ℤ,
      d ≤ |α*(n:ℝ)^2+1/2-z| := by
  induction N with
  | zero => exact ⟨1,by norm_num,by intro n h₁ h₂; omega⟩
  | succ N ih =>
    obtain ⟨d,hd,h⟩ := ih
    have hin : Irrational (α*(N+1:ℕ)^2 + ((1 / 2 : ℚ) : ℝ)) := by
      apply irrational_add_ratCast_iff.mpr
      have he : α*(N+1:ℕ)^2 = α*(((N+1)^2 : ℕ):ℝ) := by push_cast; ring
      rw [he]
      exact irrational_mul_natCast_iff.mpr ⟨pow_ne_zero _ (by omega),hi⟩
    have hin' : Irrational (α*((N+1:ℕ):ℝ)^2 + 1/2) := by
      convert hin using 1
      norm_num
    obtain ⟨e,he,hnew⟩ := irrational_gap hin'
    refine ⟨min d e,lt_min hd he,?_⟩
    intro n hn hnN z
    by_cases hn' : n ≤ N
    · exact (min_le_left _ _).trans (h n hn hn' z)
    · have hnEq : n = N+1 := by omega
      subst n
      exact (min_le_right _ _).trans (hnew z)

lemma fails_basis {α : ℝ} (hi : Irrational α) (hApp : Approximable α)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    ¬ (Erdos1147.recurrenceSet α ε).IsAsymptoticAddBasisOfOrder 2 := by
  intro hBasis
  rw [Set.isAsymptoticAddBasisOfOrder_two_iff,cofinite_eq_atTop] at hBasis
  obtain ⟨K,hK⟩ := eventually_atTop.mp hBasis
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hε.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/8)))
  obtain ⟨d,hd,hSmall⟩ := uniform_gap hi N
  let T := min (1/8:ℝ) (d/4)
  have hT : 0 < T := lt_min (by norm_num) (by positivity)
  have hT₈ : T ≤ (1/8:ℝ) := min_le_left _ _
  have hTd : T ≤ d/4 := min_le_right _ _
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hε.eventually (gt_mem_nhds hT))
  obtain ⟨j,hj⟩ := exists_nat_one_div_lt hT
  let c := (1:ℝ)/((j:ℝ)+2)
  have hc : c < T := by
    apply lt_of_le_of_lt _ hj
    dsimp [c]
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  obtain ⟨q,hq,hqB,p,hp,hErr⟩ := hApp (max K (N+M)) j
  have hqK : K ≤ q := by omega
  have hqThree : 3 ≤ q := by omega
  have hqR : 0 < (q:ℝ) := by exact_mod_cast hq.pos
  have hqOdd := hq.odd_of_ne_two (by omega)
  obtain ⟨n,hn,m,hm,hnm⟩ := Set.mem_add.mp (hK q hqK)
  have noPair (n m : ℕ) (hn : n ∈ Erdos1147.recurrenceSet α ε)
      (hm : m ∈ Erdos1147.recurrenceSet α ε) (hle : n ≤ m) (hs : n+m=q) : False := by
    change 1 ≤ n ∧ |α*(n:ℝ)^2 - (round (α*(n:ℝ)^2):ℝ)| < ε n at hn
    change 1 ≤ m ∧ |α*(m:ℝ)^2 - (round (α*(m:ℝ)^2):ℝ)| < ε m at hm
    let z := round (α*(n:ℝ)^2)
    let w := round (α*(m:ℝ)^2)
    let e := ((q:ℝ)*α-(p:ℝ)/2)*((q:ℝ)-2*(n:ℝ))
    have he : |e| < T := by
      have ha : |(q:ℝ)-2*(n:ℝ)| ≤ (q:ℝ) := by
        have hqn : n ≤ q := by omega
        have hqnR : (n:ℝ) ≤ q := by exact_mod_cast hqn
        exact abs_le.mpr ⟨by linarith,by linarith [show 0 ≤ (n:ℝ) by positivity]⟩
      have heCast : |(q:ℝ)*α-(p:ℝ)/2| < c/(q:ℝ) := hErr
      calc
        _ ≤ |(q:ℝ)*α-(p:ℝ)/2| * (q:ℝ) := by
          unfold e
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left ha (abs_nonneg _)
        _ < (c/(q:ℝ))*(q:ℝ) := mul_lt_mul_of_pos_right heCast hqR
        _ = c := div_mul_cancel₀ _ hqR.ne'
        _ < T := hc
    have hOdd : Odd ((q:ℤ)-2*(n:ℤ)) := by
      obtain ⟨a,ha⟩ := hqOdd
      exact ⟨(a:ℤ)-(n:ℤ),by omega⟩
    obtain ⟨r,hr⟩ := hp.mul hOdd
    have hrR : (p:ℝ)*((q:ℝ)-2*(n:ℝ)) = 2*(r:ℝ)+1 := by exact_mod_cast hr
    have hqSum : (q:ℝ) = n+m := by exact_mod_cast hs.symm
    have hEq : α*(m:ℝ)^2 = α*(n:ℝ)^2 + (r:ℝ)+1/2+e := by
      dsimp [e]
      rw [hqSum] at hrR ⊢
      linear_combination (1 / 2 : ℝ)*hrR
    have he' := abs_lt.mp he
    by_cases hlarge : N ≤ n
    · have hz := abs_lt.mp (hn.2.trans (hN n hlarge))
      have hw := abs_lt.mp (hm.2.trans (hN m (hlarge.trans hle)))
      have hh := half_gap (w-z-r)
      rw [Int.cast_sub,Int.cast_sub] at hh
      change -(1/8:ℝ) < α*(n:ℝ)^2-z ∧ α*(n:ℝ)^2-z < 1/8 at hz
      change -(1/8:ℝ) < α*(m:ℝ)^2-w ∧ α*(m:ℝ)^2-w < 1/8 at hw
      have hcontra : |(w:ℝ)-(z:ℝ)-(r:ℝ)-1/2| < 1/2 :=
        abs_lt.mpr ⟨by linarith [he'.1,hz.1,hw.2],by linarith [he'.2,hz.2,hw.1]⟩
      exact hcontra.not_ge hh
    · have hnN : n ≤ N := by omega
      have hmM : M ≤ m := by omega
      have hw := abs_lt.mp (hm.2.trans (hM m hmM))
      change -T < α*(m:ℝ)^2-w ∧ α*(m:ℝ)^2-w < T at hw
      have hGap := hSmall n hn.1 hnN (w-r)
      rw [Int.cast_sub] at hGap
      have hcontra : |α*(n:ℝ)^2+1/2-((w:ℝ)-(r:ℝ))| < d :=
        abs_lt.mpr ⟨by linarith [he'.2,hw.1],by linarith [he'.1,hw.2]⟩
      exact hcontra.not_ge hGap
  rcases le_total n m with hnm' | hmn'
  · exact noPair n m hn hm hnm' hnm
  · exact noPair m n hm hn hmn' (by omega)

end RecurrencePrime

theorem OMA.solution : type_of% @Erdos1147.erdos_1147.variants.almost_every := by
  intro ε hε
  have hi : ∀ᵐ x : ℝ, Irrational x := by
    rw [ae_iff]
    change volume {x : ℝ | ¬ Irrational x} = 0
    have he : {x : ℝ | ¬ Irrational x} = Set.range (fun q : ℚ ↦ (q:ℝ)) := by ext x; simp [Irrational]
    rw [he]
    exact (Set.countable_range _).measure_zero volume
  filter_upwards [RecurrencePrime.ae_approx,hi] with x hApp hI
  intro _
  exact RecurrencePrime.fails_basis hI hApp ε hε