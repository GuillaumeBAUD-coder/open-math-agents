import OMAReductions.R_InscribedSquare_exists_inscribed_rectangle_R1_H2_R1
import Mathlib

/-!
Parametrize the boundary of the prism max(|x|+|y|,|z|)=1 by its two
horizontal faces and its side. The upper half of the horizontal diamond
is the interval u ↦ (2u-1,1-|2u-1|). Identifying opposite vectors glues
these charts into the capped Möbius strip. The map v ↦ vvᵀ realizes the
antipodal quotient inside a Hausdorff space.
-/
noncomputable section
open scoped unitInterval
namespace OMA.DiamondCap

abbrev B := {p : I × I // p.2 = 0 ∨ p.2 = 1}
abbrev U := (I × I) ⊕ (B × I)
abbrev V := Fin 3 → ℝ
abbrev S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

def seam (p q : I × I) : Prop := p = q ∨
  (p.1 = 0 ∧ q.1 = 1 ∧ q.2 = unitInterval.symm p.2) ∨
  (p.1 = 1 ∧ q.1 = 0 ∧ p.2 = unitInterval.symm q.2)

def glue (x y : U) : Prop := match x,y with
  | .inl p,.inl q => seam p q
  | .inl p,.inr w => w.2 = 1 ∧ seam p w.1.val
  | .inr w,.inl p => w.2 = 1 ∧ seam p w.1.val
  | .inr v,.inr w => v.2 = w.2 ∧ (v.2 = 0 ∨ seam v.1.val w.1.val)

def base : U → I × I := Sum.elim id (fun w => w.1.val)
def rad : U → I := Sum.elim (fun _ => 1) Prod.snd
def lin (s : I) : ℝ := 2*(s:ℝ)-1
def width (s : I) : ℝ := 1-|lin s|
def vec (x : U) : V :=
  ![(rad x : ℝ)*lin (base x).1,(rad x : ℝ)*width (base x).1,lin (base x).2]
def horizontal (v : V) : ℝ := |v 0| + |v 1|
def gauge (v : V) : ℝ := max (horizontal v) |v 2|
def matrix (v : V) (i j : Fin 3) : ℝ := v i*v j

lemma seam_comm (p q : I × I) : seam p q ↔ seam q p := by
  simp only [seam,eq_comm]; tauto

lemma glue_iff (x y : U) : glue x y ↔ rad x = rad y ∧ (rad x = 0 ∨ seam (base x) (base y)) := by
  cases x with
  | inl p =>
    cases y with
    | inl q => simp [glue,rad,base]
    | inr w => simp [glue,rad,base,eq_comm]
  | inr v =>
    cases y with
    | inl q =>
      simp only [glue,rad,base,Sum.elim_inr,Sum.elim_inl,id_eq]
      rw [seam_comm]
      constructor
      · rintro ⟨h,h'⟩; exact ⟨h,Or.inr h'⟩
      · rintro ⟨h,h'|h'⟩
        · simp [h] at h'
        · exact ⟨h,h'⟩
    | inr w => rfl

lemma lin_inj : Function.Injective lin := by
  intro s t h
  apply Subtype.ext
  dsimp [lin] at h
  linarith

lemma lin_bounds (s : I) : -1 ≤ lin s ∧ lin s ≤ 1 := by
  dsimp [lin]
  constructor <;> linarith [s.2.1,s.2.2]

lemma abs_lin (s : I) : |lin s| ≤ 1 := abs_le.mpr (lin_bounds s)
lemma width_nonneg (s : I) : 0 ≤ width s := sub_nonneg.mpr (abs_lin s)
lemma width_zero (s : I) (hs : width s = 0) : s = 0 ∨ s = 1 := by
  have ha : |lin s| = 1 := by unfold width at hs; linarith
  rcases le_total 0 (lin s) with h|h
  · rw [abs_of_nonneg h] at ha
    right; apply Subtype.ext; change (s:ℝ)=1; unfold lin at ha; linarith
  · rw [abs_of_nonpos h] at ha
    left; apply Subtype.ext; change (s:ℝ)=0; unfold lin at ha; linarith

lemma lin_symm (s : I) : lin (unitInterval.symm s) = -lin s := by
  simp [lin]; ring

lemma end_height (x : U) (hr : rad x ≠ 1) : (base x).2 = 0 ∨ (base x).2 = 1 := by
  cases x with
  | inl p => exact (hr rfl).elim
  | inr w => exact w.1.property

lemma horizon_vec (x : U) : horizontal (vec x) = (rad x : ℝ) := by
  have hr := (rad x).property.1
  have hw := width_nonneg (base x).1
  change |(rad x:ℝ)*lin (base x).1| + |(rad x:ℝ)*width (base x).1| = _
  rw [abs_mul,abs_mul,abs_of_nonneg hr,abs_of_nonneg hw]
  unfold width
  ring

lemma gauge_vec (x : U) : gauge (vec x) = 1 := by
  rw [gauge,horizon_vec]
  change max (rad x : ℝ) |lin (base x).2| = 1
  by_cases hr : rad x = 1
  · rw [hr]; exact max_eq_left (abs_lin _)
  · have ht : |lin (base x).2| = 1 := by
      rcases end_height x hr with h|h <;> rw [h] <;> norm_num [lin]
    rw [ht,max_eq_right (rad x).property.2]

lemma matrix_iff (v w : V) : matrix v = matrix w ↔ v = w ∨ v = -w := by
  constructor
  · intro h
    have hprod (i j) : v i * v j = w i * w j := congrFun (congrFun h i) j
    by_cases hz : ∀ i, v i = 0
    · left; ext i
      have := hprod i i
      rw [hz i] at *
      nlinarith
    · push Not at hz
      obtain ⟨i,hi⟩ := hz
      have hsign : (v i - w i)*(v i+w i)=0 := by nlinarith [hprod i i]
      rcases mul_eq_zero.mp hsign with hm|hp
      · left
        have hh : w i = v i := by linarith
        ext j
        have hx := hprod i j
        rw [hh] at hx
        exact mul_left_cancel₀ hi hx
      · right
        have hh : w i = -v i := by linarith
        ext j
        change v j = -w j
        apply mul_left_cancel₀ hi
        rw [hprod,hh]; ring
  · rintro (rfl|h)
    · rfl
    · subst v
      ext i j
      simp [matrix]

lemma horizontal_neg (v : V) : horizontal (-v) = horizontal v := by simp [horizontal]
lemma vec_eq_iff (x y : U) : vec x = vec y ∨ vec x = -vec y ↔ glue x y := by
  rw [glue_iff]
  constructor
  · intro h
    have hr : rad x = rad y := by
      apply Subtype.ext
      rw [← horizon_vec,← horizon_vec]
      rcases h with h|h <;> rw [h]
      exact horizontal_neg _
    refine ⟨hr, ?_⟩
    by_cases hz : rad x = 0
    · exact Or.inl hz
    right
    have hpos : 0 < (rad x : ℝ) := lt_of_le_of_ne (rad x).property.1
      (fun e => hz (Subtype.ext e.symm))
    rcases h with h|h
    · left
      have hx : (rad x : ℝ)*lin (base x).1 = (rad y : ℝ)*lin (base y).1 := congrFun h 0
      rw [← hr] at hx
      exact Prod.ext (lin_inj (mul_left_cancel₀ hpos.ne' hx)) (lin_inj (congrFun h 2))
    · have hx : (rad x : ℝ)*lin (base x).1 = -((rad y : ℝ)*lin (base y).1) := congrFun h 0
      have hy : (rad x : ℝ)*width (base x).1 = -((rad y : ℝ)*width (base y).1) := congrFun h 1
      have ht : lin (base x).2 = -lin (base y).2 := congrFun h 2
      rw [← hr,← mul_neg] at hx hy
      have hxx := mul_left_cancel₀ hpos.ne' hx
      have hyy := mul_left_cancel₀ hpos.ne' hy
      have hw : width (base x).1 = 0 := by linarith [width_nonneg (base x).1,width_nonneg (base y).1]
      have e0 : lin 0 = -1 := by norm_num [lin]
      have e1 : lin 1 = 1 := by norm_num [lin]
      rcases width_zero _ hw with hs|hs
      · right; left; refine ⟨hs,lin_inj ?_,lin_inj ?_⟩
        · rw [hs,e0] at hxx; rw [e1]; linarith
        · rw [lin_symm]; linarith
      · right; right; refine ⟨hs,lin_inj ?_,lin_inj ?_⟩
        · rw [hs,e1] at hxx; rw [e0]; linarith
        · rw [lin_symm]; exact ht
  · rintro ⟨hr,hz|hs⟩
    · have hzy : rad y = 0 := hr ▸ hz
      have ex := end_height x (by rw [hz]; exact zero_ne_one)
      have ey := end_height y (by rw [hzy]; exact zero_ne_one)
      rcases ex with ex|ex <;> rcases ey with ey|ey
      · left; ext i; fin_cases i <;> norm_num [vec,hz,hzy,ex,ey,lin]
      · right; ext i; fin_cases i <;> norm_num [vec,hz,hzy,ex,ey,lin]
      · right; ext i; fin_cases i <;> norm_num [vec,hz,hzy,ex,ey,lin]
      · left; ext i; fin_cases i <;> norm_num [vec,hz,hzy,ex,ey,lin]
    · rcases hs with h|⟨hs,hs',ht⟩|⟨hs,hs',ht⟩
      · left; simp [vec,hr,h]
      · right; ext i; fin_cases i <;> (norm_num [vec,hr,hs,hs',ht,width,lin]; first | done | ring)
      · right; ext i; fin_cases i <;> (norm_num [vec,hr,hs,hs',ht,width,lin]; first | done | ring)

def fromLin (z : ℝ) (hz : |z| ≤ 1) : I :=
  ⟨(z+1)/2,by obtain ⟨h,h'⟩ := abs_le.mp hz; constructor <;> linarith⟩

lemma lin_from (z : ℝ) (hz : |z| ≤ 1) : lin (fromLin z hz) = z := by
  dsimp [fromLin,lin]; ring

lemma image_upper (v : V) (hg : gauge v = 1) (hy : 0 ≤ v 1) : ∃ x : U, vec x = v := by
  have hpair : max (|v 0| + v 1) |v 2| = 1 := by simpa [gauge,horizontal,abs_of_nonneg hy] using hg
  let r : ℝ := |v 0|+v 1
  have hr : 0 ≤ r := add_nonneg (abs_nonneg _) hy
  have hr1 : r ≤ 1 := by change |v 0|+v 1 ≤ 1; rw [← hpair]; exact le_max_left _ _
  have hz : |v 2| ≤ 1 := by rw [← hpair]; exact le_max_right _ _
  let t := fromLin (v 2) hz
  have ht : lin t = v 2 := lin_from _ _
  have hnorm : |v 0 / r| ≤ 1 := by
    rw [abs_div,abs_of_nonneg hr]
    rcases hr.eq_or_lt with h|h
    · simp [← h]
    · apply (div_le_iff₀ h).mpr
      dsimp [r]; linarith
  let s := fromLin (v 0 / r) hnorm
  have hs : lin s = v 0/r := lin_from _ _
  have hx : r*lin s=v 0 := by
    rw [hs]
    by_cases hr0 : r=0
    · have hv : |v 0|=0 := by dsimp [r] at hr0; linarith [abs_nonneg (v 0)]
      simp [hr0,abs_eq_zero.mp hv]
    · field_simp
  have hwidth : r*width s=v 1 := by
    have hx' := congrArg abs hx
    rw [abs_mul,abs_of_nonneg hr] at hx'
    unfold width
    have he : r=|v 0|+v 1 := rfl
    nlinarith
  have mk (x : U) (hb : base x=(s,t)) (hrr : (rad x : ℝ)=r) : vec x=v := by
    ext i
    fin_cases i <;> simp [vec,hb,hrr,hx,hwidth,ht]
  by_cases h1 : r=1
  · exact ⟨.inl (s,t),mk _ rfl (by simpa [rad] using h1.symm)⟩
  · have hvz : |v 2|=1 := by
      change max r |v 2| = 1 at hpair
      rcases le_total r |v 2| with h|h
      · simpa [max_eq_right h] using hpair
      · exact (h1 (by simpa [max_eq_left h] using hpair)).elim
    have he : t=0 ∨ t=1 := by
      apply width_zero
      simp [width,ht,hvz]
    let b : B := ⟨(s,t),he⟩
    exact ⟨.inr (b,⟨r,hr,hr1⟩), mk _ rfl rfl⟩

lemma gauge_neg (v : V) : gauge (-v)=gauge v := by simp [gauge,horizontal_neg]

lemma image_orbit (v : V) (hg : gauge v=1) : ∃ x : U, matrix (vec x)=matrix v := by
  by_cases h : 0≤v 1
  · obtain ⟨x,hx⟩ := image_upper v hg h
    exact ⟨x,(matrix_iff _ _).mpr (Or.inl hx)⟩
  · obtain ⟨x,hx⟩ := image_upper (-v) ((gauge_neg v).trans hg) (by simp; linarith)
    exact ⟨x,(matrix_iff _ _).mpr (Or.inr hx)⟩

def plain (x : S) : V := fun i => x.val i
def normalized (x : S) : V := fun i => plain x i / gauge (plain x)

lemma sphere_norm (x : S) : ‖x.val‖=1 := by simpa [Metric.mem_sphere,dist_zero_right] using x.property

lemma gauge_pos (x : S) : 0 < gauge (plain x) := by
  have h0 : 0 ≤ horizontal (plain x) := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have h1 : horizontal (plain x) ≤ gauge (plain x) := le_max_left _ _
  have h2 : |plain x 2| ≤ gauge (plain x) := le_max_right _ _
  by_contra! h
  have hxy : horizontal (plain x)=0 := le_antisymm (h1.trans h) h0
  have hx : plain x 0=0 := abs_eq_zero.mp (by unfold horizontal at hxy; linarith [abs_nonneg (plain x 0), abs_nonneg (plain x 1)])
  have hy : plain x 1=0 := abs_eq_zero.mp (by unfold horizontal at hxy; linarith [abs_nonneg (plain x 0), abs_nonneg (plain x 1)])
  have hz : plain x 2=0 := abs_eq_zero.mp (le_antisymm (h2.trans h) (abs_nonneg _))
  have hh : x.val=0 := by ext i; fin_cases i <;> assumption
  have hn := sphere_norm x
  simp [hh] at hn

lemma gauge_normalized (x : S) : gauge (normalized x)=1 := by
  let d := gauge (plain x)
  have hd : 0 < d := gauge_pos _
  have hxy : horizontal (normalized x) = horizontal (plain x)/d := by
    simp only [horizontal,normalized,abs_div,abs_of_pos (gauge_pos x),add_div,d]
  change max (horizontal (normalized x)) |plain x 2/d|=1
  rw [hxy,abs_div,abs_of_pos hd]
  rcases le_total (horizontal (plain x)) |plain x 2| with h|h
  · rw [max_eq_right (div_le_div_of_nonneg_right h hd.le)]
    have hh : d=|plain x 2| := max_eq_right h
    rw [← hh, div_self hd.ne']
  · rw [max_eq_left (div_le_div_of_nonneg_right h hd.le)]
    have hh : d=horizontal (plain x) := max_eq_left h
    rw [← hh,div_self hd.ne']

lemma normalized_inj {x y : S} (h : normalized x = normalized y) : x = y := by
  let d := gauge (plain x)/gauge (plain y)
  have hd : 0 ≤ d := div_nonneg (gauge_pos _).le (gauge_pos _).le
  have hv : x.val = d • y.val := by
    ext i
    change plain x i = d*plain y i
    have he := congrFun h i
    change plain x i/gauge (plain x) = plain y i/gauge (plain y) at he
    have hh := (div_eq_div_iff (gauge_pos x).ne' (gauge_pos y).ne').mp he
    calc
      plain x i = plain y i*gauge (plain x)/gauge (plain y) := (eq_div_iff (gauge_pos y).ne').mpr hh
      _ = _ := by dsimp [d]; ring
  have hnorm := congrArg norm hv
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd,sphere_norm,sphere_norm,mul_one] at hnorm
  apply Subtype.ext
  simpa [← hnorm] using hv

def antipode (y : S) : S := ⟨-y.val,by
  simpa [Metric.mem_sphere,dist_zero_right] using sphere_norm y⟩

lemma normalized_antipode (y : S) : normalized (antipode y) = -normalized y := by
  have hh : plain (antipode y) = -plain y := rfl
  ext i
  change plain (antipode y) i / gauge (plain (antipode y)) = -(plain y i / gauge (plain y))
  rw [hh,gauge_neg]
  change -(plain y i)/_ = -(_/_)
  ring

lemma normalized_orbit (x y : S) : matrix (normalized x)=matrix (normalized y) ↔ x=y ∨ x.val = -y.val := by
  rw [matrix_iff]
  constructor
  · rintro (h|h)
    · exact Or.inl (normalized_inj h)
    · rw [← normalized_antipode] at h
      exact Or.inr (congrArg Subtype.val (normalized_inj h))
  · rintro (rfl|h)
    · exact Or.inl rfl
    · have he : x=antipode y := Subtype.ext h
      exact Or.inr (he ▸ normalized_antipode y)

lemma continuous_vec : Continuous vec := by
  have hb : Continuous base := continuous_id.sumElim (continuous_subtype_val.comp continuous_fst)
  have hr : Continuous rad := continuous_const.sumElim continuous_snd
  have hl : Continuous lin := by unfold lin; fun_prop
  have hw : Continuous width := by unfold width; fun_prop
  apply continuous_pi
  intro i
  fin_cases i <;> simp [vec] <;> fun_prop

lemma continuous_matrix : Continuous matrix := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply i).mul (continuous_apply j)

lemma continuous_normalized : Continuous normalized := by
  have hc (i : Fin 3) : Continuous (fun x:S => plain x i) := by unfold plain; fun_prop
  have hg : Continuous (fun x:S => gauge (plain x)) := by unfold gauge horizontal; fun_prop
  apply continuous_pi
  intro i
  exact (hc i).div hg (fun x => (gauge_pos x).ne')

theorem chart : ∃ π : S → Quot glue,
    Continuous π ∧ ∀ x y, π x = π y ↔ x=y ∨ x.val = -y.val := by
  classical
  let _ : CompactSpace B := by
    apply isCompact_iff_compactSpace.mp
    exact ((isClosed_eq continuous_snd (continuous_const (y:= (0:I)))).union
      (isClosed_eq continuous_snd (continuous_const (y:= (1:I))))).isCompact
  let body (x : U) := matrix (vec x)
  have kernel (x y : U) : body x = body y ↔ glue x y :=
    (matrix_iff _ _).trans (vec_eq_iff _ _)
  let desc := Quot.lift body (fun x y h => (kernel x y).mpr h)
  have hd : Continuous desc := continuous_quot_lift _ (continuous_matrix.comp continuous_vec)
  have hinj : Function.Injective desc := by
    intro q r
    induction q using Quot.inductionOn with
    | h x =>
      induction r using Quot.inductionOn with
      | h y =>
        intro h
        exact Quot.sound ((kernel x y).mp h)
  have he := hd.isClosedEmbedding hinj
  have pre (x : S) : ∃ q, desc q = matrix (normalized x) := by
    obtain ⟨u,h⟩ := image_orbit _ (gauge_normalized x)
    exact ⟨Quot.mk glue u,h⟩
  let π (x : S) := (pre x).choose
  have hπ (x : S) : desc (π x)=matrix (normalized x) := (pre x).choose_spec
  refine ⟨π,he.isInducing.continuous_iff.mpr ?_,?_⟩
  · simpa only [Function.comp_def,hπ] using continuous_matrix.comp continuous_normalized
  · intro x y
    rw [← hinj.eq_iff,hπ,hπ,normalized_orbit]

end OMA.DiamondCap

theorem OMA.solution : OMA.R_InscribedSquare_exists_inscribed_rectangle_R1_H2_R1.H1 := by
  unfold OMA.R_InscribedSquare_exists_inscribed_rectangle_R1_H2_R1.H1
  intro B seam G
  have he : G = OMA.DiamondCap.glue := by
    funext x y
    cases x <;> cases y <;> rfl
  rw [he]
  exact OMA.DiamondCap.chart
