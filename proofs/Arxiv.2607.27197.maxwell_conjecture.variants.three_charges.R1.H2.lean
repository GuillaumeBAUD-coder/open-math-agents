import OMAReductions.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_charges_R1
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Three collinear Coulomb charges with arbitrary nonzero strengths

The projective coordinate sending the sites to infinity, zero and one reduces the
axial field equation to a level set for two signed inverse-square terms. Rolle's
theorem gives at most two roots on each interval. For like signs the terms decrease on each interval. For opposite signs at a
positive level the ranges force every root into one interval. Inversion handles
the remaining sign case. The resulting upper bound is two.

The differential and orthogonality arguments taking equilibria to the axis are
adapted from Brandon Yee (brandonyee-cs), Open Math Agents PR 4101. This proves
the collinear hypothesis in Steven Enamakel's reduction, Open Math Agents PR 4126.
-/

open InnerProductSpace
open scoped RealInnerProductSpace Gradient

namespace MaxwellLineCount
open Arxiv.«2607.27197»
open Set

noncomputable def K (x : ℝ) : ℝ := x / |x| ^ 3

lemma kpos {x : ℝ} (hx : 0 < x) : K x = 1 / x^2 := by
  rw [K, abs_of_pos hx]
  field_simp

lemma kneg {x : ℝ} (hx : x < 0) : K x = -(1 / x^2) := by
  rw [K, abs_of_neg hx]
  field_simp

lemma kmul (x y : ℝ) : K (x*y) = K x * K y := by
  simp only [K, abs_mul, mul_pow]
  ring

lemma kne {x : ℝ} (h : x ≠ 0) : K x ≠ 0 :=
  div_ne_zero h (pow_ne_zero _ (abs_ne_zero.mpr h))

/-- Two poles and a constant give at most two roots per interval between poles.
The derivative equation fixes the cube of (x-1)/x. -/
lemma cell_bound (I : Set ℝ) (hI : OrdConnected I)
    (h0 : ∀ x ∈ I, x ≠ 0) (h1 : ∀ x ∈ I, x ≠ 1)
    (A B C : ℝ) (hA : A ≠ 0) :
    {x : ℝ | x ∈ I ∧ A/x^2 + B/(x-1)^2 = C}.encard ≤ 2 := by
  let F := fun x : ℝ => A/x^2 + B/(x-1)^2
  let D := fun x : ℝ => -2*A/x^3 + -2*B/(x-1)^3
  have derivF (x : ℝ) (hx : x ∈ I) : HasDerivAt F (D x) x := by
    have hx0 := h0 x hx
    have hx1 := sub_ne_zero.mpr (h1 x hx)
    have h := ((hasDerivAt_const x A).div ((hasDerivAt_id x).pow 2) (pow_ne_zero _ hx0)).add
      ((hasDerivAt_const x B).div (((hasDerivAt_id x).sub_const 1).pow 2) (pow_ne_zero _ hx1))
    convert h using 1 <;> (try rfl)
    dsimp [D]
    field_simp
    ring
  have critical (x : ℝ) (hx : x ∈ I) (hd : D x = 0) : ((x-1)/x)^3 = -B/A := by
    dsimp [D] at hd
    have hx0 := h0 x hx
    have hx1 := sub_ne_zero.mpr (h1 x hx)
    field_simp at hd ⊢
    linarith
  have rolle {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) (hxy : x < y) (h : F x = F y) :
      ∃ t ∈ Ioo x y, t ∈ I ∧ D t = 0 := by
    have sub := hI.out hx hy
    obtain ⟨t,ht,hd⟩ := exists_hasDerivAt_eq_zero hxy
      (fun u hu => (derivF u (sub hu)).continuousAt.continuousWithinAt) h
      (fun u hu => derivF u (sub (Ioo_subset_Icc_self hu)))
    exact ⟨t,ht,sub (Ioo_subset_Icc_self ht),hd⟩
  let S := {x : ℝ | x ∈ I ∧ A/x^2 + B/(x-1)^2 = C}
  have noThree {x y z : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
      (hxy : x < y) (hyz : y < z) : False := by
    obtain ⟨u,hu,huI,du⟩ := rolle hx.1 hy.1 hxy (hx.2.trans hy.2.symm)
    obtain ⟨v,hv,hvI,dv⟩ := rolle hy.1 hz.1 hyz (hy.2.trans hz.2.symm)
    have cubes := (critical u huI du).trans (critical v hvI dv).symm
    have hr := (show Odd 3 by decide).strictMono_pow.injective cubes
    change (u-1)/u = (v-1)/v at hr
    field_simp [h0 u huI,h0 v hvI] at hr
    have := hu.2.trans hv.1
    linarith
  by_contra! big
  have three : (3 : ℕ∞) ≤ S.encard := Order.add_one_le_of_lt big
  obtain ⟨T,hT,ht⟩ := Set.exists_subset_encard_eq three
  obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := Set.encard_eq_three.mp ht
  have mx : x ∈ S := hT (by simp)
  have my : y ∈ S := hT (by simp)
  have mz : z ∈ S := hT (by simp)
  rcases lt_or_gt_of_ne hxy with a|a <;> rcases lt_or_gt_of_ne hxz with b|b <;>
    rcases lt_or_gt_of_ne hyz with c|c <;>
    first | exact noThree mx my mz a c | exact noThree mx mz my b c
          | exact noThree my mx mz a b | exact noThree my mz mx c b
          | exact noThree mz mx my b a | exact noThree mz my mx c a


/-- Per-interval root counts and separation of the ranges on the three intervals. -/
lemma level_bound (b c : ℝ) (signs : 0 ≤ b ∨ 0 < c) :
    {t : ℝ | t ≠ 0 ∧ t ≠ 1 ∧ K t + b*K (t-1) = c}.encard ≤ 2 := by
  let S := {t : ℝ | t ≠ 0 ∧ t ≠ 1 ∧ K t + b*K (t-1) = c}
  let L := S ∩ Iio 0
  let M := S ∩ Ioo 0 1
  let R := S ∩ Ioi 1
  have cover : S ⊆ L ∪ M ∪ R := by
    intro x hx
    rcases lt_or_gt_of_ne hx.1 with h|h
    · exact Or.inl (Or.inl ⟨hx,h⟩)
    · rcases lt_or_gt_of_ne hx.2.1 with k|k
      · exact Or.inl (Or.inr ⟨hx,h,k⟩)
      · exact Or.inr ⟨hx,k⟩
  have lbound : L.encard ≤ 2 := by
    apply le_trans (Set.encard_le_encard (t := {x : ℝ | x ∈ Iio 0 ∧ (-1)/x^2 + (-b)/(x-1)^2 = c}) ?_)
    · exact cell_bound (Iio 0) Set.ordConnected_Iio (fun _ hx => ne_of_lt hx)
        (fun _ hx => ne_of_lt (lt_trans hx zero_lt_one)) _ _ _ (by norm_num)
    · rintro x ⟨hx,hl⟩
      refine ⟨hl,?_⟩
      have h := hx.2.2
      change x < 0 at hl
      rw [kneg hl,kneg (by linarith : x-1<0)] at h
      convert h using 1
      ring
  have mbound : M.encard ≤ 2 := by
    apply le_trans (Set.encard_le_encard (t := {x : ℝ | x ∈ Ioo 0 1 ∧ 1/x^2 + (-b)/(x-1)^2 = c}) ?_)
    · exact cell_bound (Ioo 0 1) Set.ordConnected_Ioo (fun _ hx => ne_of_gt hx.1)
        (fun _ hx => ne_of_lt hx.2) _ _ _ (by norm_num)
    · rintro x ⟨hx,hm⟩
      refine ⟨hm,?_⟩
      have h := hx.2.2
      rw [kpos hm.1,kneg (sub_neg.mpr hm.2)] at h
      convert h using 1
      ring
  have rbound : R.encard ≤ 2 := by
    apply le_trans (Set.encard_le_encard (t := {x : ℝ | x ∈ Ioi 1 ∧ 1/x^2 + b/(x-1)^2 = c}) ?_)
    · exact cell_bound (Ioi 1) Set.ordConnected_Ioi (fun _ hx => ne_of_gt (lt_trans zero_lt_one hx))
        (fun _ hx => ne_of_gt hx) _ _ _ (by norm_num)
    · rintro x ⟨hx,hr⟩
      refine ⟨hr,?_⟩
      have h := hx.2.2
      rw [kpos (lt_trans zero_lt_one hr),kpos (sub_pos.mpr hr)] at h
      convert h using 1
      ring
  have pair {U V : Set ℝ} (sub : S ⊆ U ∪ V) (u : U.encard ≤ 1) (v : V.encard ≤ 1) :
      S.encard ≤ 2 := calc
    _ ≤ (U ∪ V).encard := encard_le_encard sub
    _ ≤ U.encard + V.encard := encard_union_le _ _
    _ ≤ (1:ℕ∞) + 1 := add_le_add u v
    _ = 2 := rfl
  by_cases hb : 0 ≤ b
  · have decK {x y : ℝ} (xy : x < y) (side : y < 0 ∨ 0 < x) : K y < K x := by
      rcases side with hn | hp
      · rw [kneg hn, kneg (xy.trans hn), neg_lt_neg_iff]
        apply one_div_lt_one_div_of_lt (sq_pos_of_neg hn)
        nlinarith [mul_pos (sub_pos.mpr xy) (show 0 < -x-y by linarith)]
      · rw [kpos hp,kpos (hp.trans xy)]
        apply one_div_lt_one_div_of_lt (sq_pos_of_pos hp)
        nlinarith [mul_pos (sub_pos.mpr xy) (show 0 < x+y by linarith)]
    have distinct {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) (xy : x<y)
        (h : y<0 ∨ 0<x) (h' : y<1 ∨ 1<x) : False := by
      have d := decK xy h
      have e := decK (sub_lt_sub_right xy 1) (h'.imp sub_neg.mpr sub_pos.mpr)
      have f := mul_le_mul_of_nonneg_left e.le hb
      linarith only [hx.2.2,hy.2.2,d,f]
    have one (I : Set ℝ) (s0 : (∀ x ∈ I, x<0) ∨ (∀ x ∈ I, 0<x))
        (s1 : (∀ x ∈ I, x<1) ∨ (∀ x ∈ I, 1<x)) : (S ∩ I).encard ≤ 1 := by
      rw [Set.encard_le_one_iff]
      intro x y hx hy
      by_contra ne
      rcases lt_or_gt_of_ne ne with h|h
      · exact distinct hx.1 hy.1 h (s0.imp (fun f => f y hy.2) (fun f => f x hx.2))
          (s1.imp (fun f => f y hy.2) (fun f => f x hx.2))
      · exact distinct hy.1 hx.1 h (s0.imp (fun f => f x hx.2) (fun f => f y hy.2))
          (s1.imp (fun f => f x hx.2) (fun f => f y hy.2))
    have lo : L.encard ≤ 1 := one _ (.inl (fun _ hx => hx)) (.inl (fun _ hx => lt_trans hx zero_lt_one))
    have mi : M.encard ≤ 1 := one _ (.inr (fun _ hx => hx.1)) (.inl (fun _ hx => hx.2))
    have hi : R.encard ≤ 1 := one _ (.inr (fun _ hx => lt_trans zero_lt_one hx)) (.inr (fun _ hx => hx))
    by_cases hc : 0 < c
    · have e : L = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx,hl⟩
        change x < 0 at hl
        have ex := hx.2.2
        rw [kneg hl,kneg (by linarith : x-1<0)] at ex
        have := mul_nonneg hb (show 0 ≤ 1/(x-1)^2 by positivity)
        have := one_div_pos.mpr (sq_pos_of_neg hl)
        linarith
      exact pair (by simpa only [e,empty_union] using cover) mi hi
    · have e : R = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx,hr⟩
        change 1 < x at hr
        have ex := hx.2.2
        rw [kpos (zero_lt_one.trans hr),kpos (sub_pos.mpr hr)] at ex
        have := mul_nonneg hb (show 0 ≤ 1/(x-1)^2 by positivity)
        have := one_div_pos.mpr (sq_pos_of_pos (zero_lt_one.trans hr))
        linarith
      exact pair (by simpa only [e,union_empty] using cover) lo mi
  · have hc := signs.resolve_left hb
    have B : 0 < -b := by linarith
    have leftInfo {x} (hx : x ∈ L) : c < -b ∧ b < -1 := by
      obtain ⟨hx,hl⟩ := hx
      change x < 0 at hl
      have ex := hx.2.2
      rw [kneg hl,kneg (by linarith : x-1<0)] at ex
      have px := one_div_pos.mpr (sq_pos_of_neg hl)
      have p : 0 ≤ 1/(x-1)^2 := by positivity
      have l : 1/(x-1)^2 < 1 := (div_lt_one (sq_pos_of_neg (by linarith : x-1<0))).mpr (by nlinarith [sq_nonneg x])
      have h := mul_lt_mul_of_pos_left l B
      refine ⟨by linarith,?_⟩
      by_contra! h'
      have t := mul_le_mul_of_nonneg_right h' p
      have order : 1/(x-1)^2 < 1/x^2 := by
        apply one_div_lt_one_div_of_lt (sq_pos_of_neg hl)
        nlinarith
      linarith
    have rightInfo {x} (hx : x ∈ R) : c < 1 ∧ -1 < b := by
      obtain ⟨hx,hr⟩ := hx
      change 1 < x at hr
      have ex := hx.2.2
      rw [kpos (zero_lt_one.trans hr),kpos (sub_pos.mpr hr)] at ex
      have p := one_div_pos.mpr (sq_pos_of_pos (sub_pos.mpr hr))
      have up : 1/x^2 < 1 := (div_lt_one (sq_pos_of_pos (zero_lt_one.trans hr))).mpr (by nlinarith [sq_nonneg (x-1)])
      have t := mul_neg_of_neg_of_pos (lt_of_not_ge hb) p
      refine ⟨by linarith,?_⟩
      by_contra! h'
      have h := mul_le_mul_of_nonneg_right h' p.le
      have order : 1/x^2 < 1/(x-1)^2 := by
        apply one_div_lt_one_div_of_lt (sq_pos_of_pos (sub_pos.mpr hr))
        nlinarith
      linarith
    by_cases mid : M.Nonempty
    · obtain ⟨y,hy,lo,hi⟩ := mid
      have eq := hy.2.2
      rw [kpos lo,kneg (sub_neg.mpr hi)] at eq
      have a : 1 < 1/y^2 := (one_lt_div (sq_pos_of_pos lo)).mpr (by nlinarith [mul_pos lo (sub_pos.mpr hi)])
      have a' : 1 < 1/(y-1)^2 := (one_lt_div (sq_pos_of_neg (sub_neg.mpr hi))).mpr (by nlinarith [mul_pos lo (sub_pos.mpr hi)])
      have := mul_lt_mul_of_pos_left a' B
      apply le_trans (Set.encard_le_encard (t := M) ?_) mbound
      intro x hx
      rcases cover hx with (hl|hm)|hr
      · have := (leftInfo hl).1
        exfalso; linarith
      · exact hm
      · have := (rightInfo hr).1
        exfalso; linarith
    · rcases le_total b (-1) with bsmall|blarge
      · apply le_trans (Set.encard_le_encard (t := L) ?_) lbound
        intro x hx
        rcases cover hx with (hl|hm)|hr
        · exact hl
        · exact (mid ⟨_,hm⟩).elim
        · exact ((not_lt.mpr bsmall) (rightInfo hr).2).elim
      · apply le_trans (Set.encard_le_encard (t := R) ?_) rbound
        intro x hx
        rcases cover hx with (hl|hm)|hr
        · exact ((not_lt.mpr blarge) (leftInfo hl).2).elim
        · exact (mid ⟨_,hm⟩).elim
        · exact hr
lemma kdiv (x y : ℝ) : K (x/y) = K x / K y := by
  simp only [K, abs_div, div_pow]
  ring

/-- Inverting the coordinate exchanges the constant and one pole. -/
lemma normalized_bound (b c : ℝ) (hc : c ≠ 0) :
    {t : ℝ | t ≠ 0 ∧ t ≠ 1 ∧ K t + b*K (t-1) = c}.encard ≤ 2 := by
  by_cases signs : 0 ≤ b ∨ 0 < c
  · exact level_bound b c signs
  push Not at signs
  have bc : 0 ≤ b/c := by simpa using div_nonneg (neg_nonneg.mpr signs.1.le) (neg_nonneg.mpr signs.2)
  let Z := {u : ℝ | u ≠ 0 ∧ u ≠ 1 ∧ K u + (b/c)*K (u-1) = 1/c}
  apply le_trans (Set.encard_le_encard_of_injOn (f := fun t : ℝ => 1/t) (t := Z) ?_ ?_) (level_bound _ _ (.inl bc))
  · rintro t ⟨ht,ht1,eq⟩
    have kt := kne ht
    have one : K 1 = 1 := by norm_num [K]
    have neg : K (-1) = -1 := by norm_num [K]
    have inv : K (1/t) = 1/K t := by rw [kdiv,one]
    have shift : 1/t-1 = (-1)*(t-1)/t := by field_simp; ring
    refine ⟨div_ne_zero one_ne_zero ht,?_,?_⟩
    · intro h
      exact ht1 (by field_simp at h; linarith)
    · rw [inv,shift,kdiv,kmul,neg]
      field_simp [kt,hc]
      linarith
  · intro x _ y _ h
    simpa only [one_div,inv_inj] using h

/-- The fractional linear parameter sends the sources to infinity, zero and one.
The signed inverse-square kernel is multiplicative, so the first source becomes a constant. -/
lemma axis_bound (r q : Fin 3 → ℝ) (hr : Function.Injective r) (hq : ∀ i, q i ≠ 0) :
    {s : ℝ | (∀ j, s ≠ r j) ∧ ∑ j, q j / |s - r j|^3 * (s - r j) = 0}.encard ≤ 2 := by
  let c := (r 2-r 0)/(r 2-r 1)
  have r20 : r 2-r 0 ≠ 0 := sub_ne_zero.mpr (hr.ne (by decide))
  have r21 : r 2-r 1 ≠ 0 := sub_ne_zero.mpr (hr.ne (by decide))
  have r10 : r 1-r 0 ≠ 0 := sub_ne_zero.mpr (hr.ne (by decide))
  have c0 : c ≠ 0 := div_ne_zero r20 r21
  have cdef : c*(r 2-r 1) = r 2-r 0 := div_mul_cancel₀ _ r21
  have c1 : c-1 ≠ 0 := by
    intro h
    have : c=1 := by linarith
    rw [this, one_mul] at cdef
    exact r10 (by linarith)
  let T := fun s : ℝ => c*(s-r 1)/(s-r 0)
  have shift (s : ℝ) (hs : s ≠ r 0) : T s - 1 = (c-1)*(s-r 2)/(s-r 0) := by
    dsimp [T]
    field_simp [sub_ne_zero.mpr hs]
    linarith
  let A := q 1 / K c
  let B := q 2 / K (c-1)
  have A0 : A ≠ 0 := div_ne_zero (hq 1) (kne c0)
  let S := {s : ℝ | (∀ j, s ≠ r j) ∧ ∑ j, q j / |s - r j|^3 * (s - r j) = 0}
  let Z := {t : ℝ | t ≠ 0 ∧ t ≠ 1 ∧ K t + (B/A)*K (t-1) = -q 0/A}
  have maps : MapsTo T S Z := by
    rintro s ⟨hs,eq⟩
    have d (j : Fin 3) := sub_ne_zero.mpr (hs j)
    have wt : K (T s) = K c * K (s-r 1) / K (s-r 0) := by
      dsimp only [T]
      rw [kdiv,kmul]
    have wt1 : K (T s-1) = K (c-1) * K (s-r 2) / K (s-r 0) := by
      rw [shift s (hs 0),kdiv,kmul]
    refine ⟨div_ne_zero (mul_ne_zero c0 (d 1)) (d 0),?_,?_⟩
    · apply sub_ne_zero.mp
      rw [shift s (hs 0)]
      exact div_ne_zero (mul_ne_zero c1 (d 2)) (d 0)
    · have force : q 0 * K (s-r 0) + q 1 * K (s-r 1) + q 2 * K (s-r 2) = 0 := by
        rw [Fin.sum_univ_three] at eq
        convert eq using 1
        simp only [K]
        ring
      rw [wt,wt1]
      dsimp only [A,B]
      field_simp [kne (d 0), kne c0, kne c1, hq 1]
      linear_combination force
  have inj : InjOn T S := by
    intro x hx y hy eq
    change c*(x-r 1)/(x-r 0) = c*(y-r 1)/(y-r 0) at eq
    field_simp [sub_ne_zero.mpr (hx.1 0),sub_ne_zero.mpr (hy.1 0)] at eq
    have eq' : (x-y)*(r 1-r 0) = 0 := by linear_combination eq
    exact sub_eq_zero.mp ((mul_eq_zero.mp eq').resolve_right r10)
  exact (encard_le_encard_of_injOn maps inj).trans (normalized_bound _ _ (div_ne_zero (neg_ne_zero.mpr (hq 0)) A0))

lemma charge_hasGradient (q : ℝ) (a x : (EuclideanSpace ℝ (Fin 3))) (hxa : x ≠ a) :
    HasGradientAt (fun y : (EuclideanSpace ℝ (Fin 3)) => q / dist y a) ((-q / ‖x-a‖^3) • (x-a)) x := by
  have hn : ‖x-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa)
  have hs : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => ‖y-a‖^2) (2 • innerSL ℝ (x-a)) x := by
    simpa using ((hasFDerivAt_id x).sub_const a).norm_sq
  have hd : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => ‖y-a‖) (‖x-a‖⁻¹ • innerSL ℝ (x-a)) x := by
    convert! hs.sqrt (pow_ne_zero 2 hn) using 1
    · funext y; exact (Real.sqrt_sq (norm_nonneg _)).symm
    · simp only [Real.sqrt_sq (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      congr 1
      field_simp
      <;> norm_num
  have hi := ((hasDerivAt_inv hn).comp_hasFDerivAt x hd).const_mul q
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert! hi using 1 <;> ext v <;>
    simp [dist_eq_norm, div_eq_mul_inv, toDual_apply_apply, inner_smul_left, smul_smul]
  <;> field_simp [hn]
  <;> simp
  <;> ring

lemma potential_hasGradient (q : Fin 3 → ℝ) (a : Fin 3 → (EuclideanSpace ℝ (Fin 3))) (x : (EuclideanSpace ℝ (Fin 3))) (hx : x ∉ Set.range a) :
    HasGradientAt (Arxiv.«2607.27197».potential q a) (-((∑ j, (q j / ‖x - a j‖^3) • (x - a j)))) x := by
  have hn (j : Fin 3) : x ≠ a j := fun h => hx ⟨j, h.symm⟩
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hf : Arxiv.«2607.27197».potential q a = fun y => ∑ j, q j / dist y (a j) := rfl
  rw [hf]
  have := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => (charge_hasGradient (q j) (a j) x (hn j)).hasFDerivAt)
  have key : (toDual ℝ (EuclideanSpace ℝ (Fin 3))) (-((∑ j, (q j / ‖x - a j‖^3) • (x - a j)))) =
      ∑ i, (toDual ℝ (EuclideanSpace ℝ (Fin 3))) ((-q i / ‖x - a i‖ ^ 3) • (x - a i)) := by
    rw [← Finset.sum_neg_distrib, map_sum]
    simp only [neg_div, neg_smul]
  rw [key]
  exact this

lemma mem_equilibria_iff (q : Fin 3 → ℝ) (a : Fin 3 → (EuclideanSpace ℝ (Fin 3))) (x : (EuclideanSpace ℝ (Fin 3))) :
    x ∈ Arxiv.«2607.27197».equilibria q a ↔ x ∉ Set.range a ∧ (∑ j, (q j / ‖x - a j‖^3) • (x - a j)) = 0 := by
  constructor
  · rintro ⟨hx, hg⟩
    refine ⟨hx, ?_⟩
    have := (potential_hasGradient q a x hx).gradient
    rw [hg] at this
    exact neg_eq_zero.mp this.symm
  · rintro ⟨hx, hg⟩
    refine ⟨hx, ?_⟩
    rw [(potential_hasGradient q a x hx).gradient, hg, neg_zero]


lemma norm_sub_hasFDerivAt (a x : (EuclideanSpace ℝ (Fin 3))) (hxa : x ≠ a) :
    HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => ‖y-a‖) (‖x-a‖⁻¹ • innerSL ℝ (x-a)) x := by
  have hn : ‖x-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa)
  have hs : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => ‖y-a‖^2) (2 • innerSL ℝ (x-a)) x := by
    simpa using ((hasFDerivAt_id x).sub_const a).norm_sq
  convert! hs.sqrt (pow_ne_zero 2 hn) using 1
  · funext y; exact (Real.sqrt_sq (norm_nonneg _)).symm
  · simp only [Real.sqrt_sq (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    field_simp
    norm_num

/-- the coefficient `q / ‖y - a‖^3` has a derivative that kills every vector orthogonal to `x - a`. -/
lemma coeff_hasFDerivAt (q : ℝ) (a x : (EuclideanSpace ℝ (Fin 3))) (hxa : x ≠ a) :
    ∃ C : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ, HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => q / ‖y-a‖^3) C x ∧
      ∀ u : (EuclideanSpace ℝ (Fin 3)), ⟪x - a, u⟫ = 0 → C u = 0 := by
  have hn : ‖x-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa)
  have hg : DifferentiableAt ℝ (fun r : ℝ => q / r^3) ‖x-a‖ :=
    (differentiableAt_const q).div (differentiableAt_pow 3) (pow_ne_zero 3 hn)
  refine ⟨deriv (fun r : ℝ => q / r^3) ‖x-a‖ • (‖x-a‖⁻¹ • innerSL ℝ (x-a)), ?_, ?_⟩
  · have h := hg.hasDerivAt.comp_hasFDerivAt (f := fun y : (EuclideanSpace ℝ (Fin 3)) => ‖y-a‖) x
      (norm_sub_hasFDerivAt a x hxa)
    exact h
  · intro u hu
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply, hu]
    simp

lemma field_hasFDerivAt (q : Fin 3 → ℝ) (a : Fin 3 → (EuclideanSpace ℝ (Fin 3))) (x : (EuclideanSpace ℝ (Fin 3))) (hx : x ∉ Set.range a) :
    ∃ D : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (EuclideanSpace ℝ (Fin 3)), HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => (∑ j, (q j / ‖y - a j‖^3) • (y - a j))) D x ∧
      ∀ u : (EuclideanSpace ℝ (Fin 3)), (∀ j, ⟪x - a j, u⟫ = 0) → D u = (∑ j, q j / ‖x - a j‖^3) • u := by
  have hn (j : Fin 3) : x ≠ a j := fun h => hx ⟨j, h.symm⟩
  choose C hC hCu using fun j => coeff_hasFDerivAt (q j) (a j) x (hn j)
  have hj (j : Fin 3) : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => (q j / ‖y - a j‖^3) • (y - a j))
      ((q j / ‖x - a j‖^3) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) + (C j).smulRight (x - a j)) x :=
    (hC j).fun_smul ((hasFDerivAt_id x).sub_const (a j))
  refine ⟨∑ j, ((q j / ‖x - a j‖^3) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) + (C j).smulRight (x - a j)),
    ?_, ?_⟩
  · have := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hj j)
    exact this
  · intro u hu
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq,
      ContinuousLinearMap.smulRight_apply, hCu _ u (hu _), zero_smul, add_zero, Finset.sum_smul]

/-- **Lemma D**: an equilibrium at which some nonzero `u` is orthogonal to all `x - a j` while
`∑ q j / r_j^3 = 0` is degenerate. -/
lemma not_nondegenerate (q : Fin 3 → ℝ) (a : Fin 3 → (EuclideanSpace ℝ (Fin 3))) (x : (EuclideanSpace ℝ (Fin 3))) (hx : x ∉ Set.range a)
    (u : (EuclideanSpace ℝ (Fin 3))) (hu : u ≠ 0) (horth : ∀ j, ⟪x - a j, u⟫ = 0)
    (hsum : ∑ j, q j / ‖x - a j‖^3 = 0) :
    ¬ Arxiv.«2607.27197».HasNondegenerateHessianAt (Arxiv.«2607.27197».potential q a) x := by
  intro hnd
  obtain ⟨D, hD, hDu⟩ := field_hasFDerivAt q a x hx
  have hopen : IsOpen (Set.range a)ᶜ := (Set.finite_range a).isClosed.isOpen_compl
  have hev : fderiv ℝ (Arxiv.«2607.27197».potential q a) =ᶠ[nhds x]
      fun y => -(innerSL ℝ ((∑ j, (q j / ‖y - a j‖^3) • (y - a j)))) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    rw [(potential_hasGradient q a y hy).hasFDerivAt.fderiv]
    ext w
    simp [toDual_apply_apply, innerSL_apply_apply, inner_neg_left]
  have hF : HasFDerivAt (fun y => -(innerSL ℝ ((∑ j, (q j / ‖y - a j‖^3) • (y - a j))))) (-((innerSL ℝ).comp D)) x :=
    (((innerSL ℝ : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ).hasFDerivAt).comp x hD).neg
  obtain ⟨w, hw⟩ := hnd u hu
  apply hw
  rw [iteratedFDeriv_two_apply, hev.fderiv_eq, hF.fderiv]
  simp [hDu u horth, hsum]

lemma exists_orth (d v : (EuclideanSpace ℝ (Fin 3))) : ∃ u : (EuclideanSpace ℝ (Fin 3)), u ≠ 0 ∧ ⟪d, u⟫ = 0 ∧ ⟪v, u⟫ = 0 := by
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := Submodule.span ℝ (Set.range ![d, v])
  have hK : Module.finrank ℝ K ≤ 2 := by
    have := finrank_range_le_card (R := ℝ) ![d, v]
    simpa [Set.finrank] using this
  have hsum := Submodule.finrank_add_finrank_orthogonal K
  rw [finrank_euclideanSpace_fin] at hsum
  have hne : Kᗮ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hsum
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨u, hu0, ?_, ?_⟩
  · exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (show d ∈ Set.range ![d, v] from ⟨0, rfl⟩)) hu
  · exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (show v ∈ Set.range ![d, v] from ⟨1, rfl⟩)) hu

/-- Arbitrary nonzero collinear charges with nondegenerate equilibria have at most two equilibria. -/
lemma collinear_case (q : Fin 3 → ℝ) (a : Fin 3 → (EuclideanSpace ℝ (Fin 3))) (ha : Function.Injective a)
    (hq : ∀ j, q j ≠ 0)
    (hnd : ∀ x ∈ equilibria q a, HasNondegenerateHessianAt (potential q a) x)
    (hcol : Collinear ℝ (Set.range a)) : (equilibria q a).encard ≤ 2 := by
  obtain ⟨p₀, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).mp hcol
  choose r hr using fun j => hv (a j) ⟨j, rfl⟩
  simp only [vadd_eq_add] at hr
  have hv0 : v ≠ 0 := by
    intro h0
    have : a 0 = a 1 := by rw [hr 0, hr 1, h0]; simp
    exact absurd (ha this) (by decide)
  have hvv : ⟪v, v⟫ ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]; exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv0)
  -- every equilibrium lies on the line
  have hline : ∀ x ∈ equilibria q a, x = (⟪x - p₀, v⟫ / ⟪v, v⟫) • v + p₀ := by
    intro x hx
    by_contra hoff
    have hx' := (mem_equilibria_iff q a x).mp hx
    obtain ⟨d, hd⟩ : ∃ d, d = x - p₀ := ⟨_, rfl⟩
    set c : Fin 3 → ℝ := fun j => q j / ‖x - a j‖^3
    have hxa (j : Fin 3) : x - a j = d - r j • v := by rw [hd, hr j]; abel
    have hF : (∑ j, c j) • d - (∑ j, c j * r j) • v = 0 := by
      have := hx'.2
      simp only [hxa] at this
      rw [← this, Finset.sum_smul, Finset.sum_smul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [c, smul_sub, smul_smul]
      rw [hxa j]
    have hS : ∑ j, c j = 0 := by
      by_contra hS
      apply hoff
      have : d = ((∑ j, c j * r j) / ∑ j, c j) • v := by
        rw [sub_eq_zero] at hF
        rw [div_eq_inv_mul, mul_smul, ← hF, smul_smul, inv_mul_cancel₀ hS, one_smul]
      have h2 : ⟪d, v⟫ / ⟪v, v⟫ = (∑ j, c j * r j) / ∑ j, c j := by
        rw [this, real_inner_smul_left, mul_div_assoc, div_self hvv, mul_one]
      rw [← hd, h2, ← this, hd, sub_add_cancel]
    obtain ⟨u, hu0, hdu, hvu⟩ := exists_orth d v
    apply not_nondegenerate q a x hx'.1 u hu0 _ hS (hnd x hx)
    intro j
    rw [hxa, inner_sub_left, real_inner_smul_left, hdu, hvu]; ring
  -- map to the line parameter
  let g : (EuclideanSpace ℝ (Fin 3)) → ℝ := fun x => ⟪x - p₀, v⟫ / ⟪v, v⟫
  have hmaps : Set.MapsTo g (equilibria q a)
      {s : ℝ | (∀ j, s ≠ r j) ∧ ∑ j, q j / |s - r j|^3 * (s - r j) = 0} := by
    intro x hx
    have hx' := (mem_equilibria_iff q a x).mp hx
    have hxl := hline x hx
    set s := g x
    have hxa (j : Fin 3) : x - a j = (s - r j) • v := by
      rw [hr j]; conv_lhs => rw [hxl]
      rw [sub_smul]; abel
    refine ⟨fun j hj => hx'.1 ⟨j, ?_⟩, ?_⟩
    · have := hxa j; rw [hj, sub_self, zero_smul] at this; exact (sub_eq_zero.mp this).symm
    · have h0 := hx'.2
      simp only [hxa, norm_smul, Real.norm_eq_abs, smul_smul, ← Finset.sum_smul] at h0
      have h1 := (smul_eq_zero.mp h0).resolve_right hv0
      have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
      have : ∑ j, q j / |s - r j|^3 * (s - r j) = ‖v‖^3 * ∑ j, q j / (|s - r j| * ‖v‖)^3 * (s - r j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_pow]
        field_simp
      rw [this, h1, mul_zero]
  have hinj : Set.InjOn g (equilibria q a) := by
    intro x hx y hy hxy
    rw [hline x hx, hline y hy]
    simp only [g] at hxy
    rw [hxy]
  calc (equilibria q a).encard
      ≤ {s : ℝ | (∀ j, s ≠ r j) ∧ ∑ j, q j / |s - r j|^3 * (s - r j) = 0}.encard :=
        Set.encard_le_encard_of_injOn hmaps hinj
    _ ≤ 2 := axis_bound r q (fun i j hij => ha (by rw [hr i, hr j, hij])) hq

end MaxwellLineCount

theorem OMA.solution : OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_charges_R1.H2 := by
  intro q a ha hind hq hnd
  exact (MaxwellLineCount.collinear_case q a ha hq hnd (collinear_iff_not_affineIndependent.mpr hind)).trans (by decide)
