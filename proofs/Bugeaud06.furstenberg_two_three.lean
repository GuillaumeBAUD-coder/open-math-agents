import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_6

/-!
# Furstenberg's ×2, ×3 theorem

The multiplicative semigroup meets every sufficiently large interval of prescribed
relative width. Scaling small differences on the circle then shows that every
infinite closed invariant set has all possible differences. Successive intersections
with rational translates force a torsion point in the orbit closure. A suitable
forward image of that point is periodic under both maps, so scaling around the
periodic point gives the entire circle.

Classical theorem of H. Furstenberg (1967). For the rational-grid argument see
M. Hochman, Lectures on Topological Dynamics, §12 (2022),
https://math.huji.ac.il/~mhochman/courses/TD2022/notes-v3.pdf .
-/

-- Credit: @zarnab222-dev


section
open Real
namespace FurstScale

private def SumLog (x : ℝ) : Prop := ∃ m n : ℕ, x = m * log 2 + n * log 3

private theorem combine {u v : ℝ} (hu : SumLog u) (hv : SumLog v) (a b : ℕ) :
    SumLog (a*u+b*v) := by
  obtain ⟨i,j,rfl⟩ := hu
  obtain ⟨k,l,rfl⟩ := hv
  refine ⟨a*i+b*k,a*j+b*l,?_⟩
  push_cast
  ring

private theorem grid {u v h : ℝ} (up : 0 < u) (uv : u < v) (gap : v-u ≤ h)
    (su : SumLog u) (sv : SumLog v) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∃ y : ℝ, SumLog y ∧ x ≤ y ∧ y ≤ x+h := by
  let N : ℕ := ⌈u/(v-u)⌉₊
  refine ⟨N*u,?_⟩
  intro x hx
  have hp : 0 ≤ x := (mul_nonneg (Nat.cast_nonneg _) up.le).trans hx
  let k : ℕ := ⌊x/u⌋₊
  have hk : N ≤ k := (Nat.le_floor_iff (div_nonneg hp up.le)).mpr ((le_div_iff₀ up).mpr hx)
  have lo : (k:ℝ)*u ≤ x := (le_div_iff₀ up).mp (Nat.floor_le (div_nonneg hp up.le))
  have hi : x < ((k:ℝ)+1)*u := (div_lt_iff₀ up).mp (Nat.lt_floor_add_one _)
  let j : ℕ := ⌈(x-k*u)/(v-u)⌉₊
  have pos : 0 < v-u := sub_pos.mpr uv
  have jN : j ≤ N := Nat.ceil_mono ((div_le_div_iff_of_pos_right pos).mpr (by linarith))
  have jk := jN.trans hk
  have jl : x-(k:ℝ)*u ≤ (j:ℝ)*(v-u) := (div_le_iff₀ pos).mp (Nat.le_ceil _)
  have jt : (j:ℝ) < (x-k*u)/(v-u)+1 := Nat.ceil_lt_add_one (div_nonneg (sub_nonneg.mpr lo) pos.le)
  have jt' : ((j:ℝ)-1)*(v-u) < x-k*u := (lt_div_iff₀ pos).mp (by linarith)
  use (k-j:ℕ)*u+j*v, combine su sv _ _
  rw [Nat.cast_sub jk]
  constructor <;> nlinarith

private theorem close (h : ℝ) (hp : 0<h) :
    ∃ u v : ℝ, 0<u ∧ u<v ∧ v-u≤h ∧ SumLog u ∧ SumLog v := by
  have l2 : 0 < log 2 := log_pos (by norm_num)
  have l3 : 0 < log 3 := log_pos (by norm_num)
  have l23 : log 2 < log 3 := log_lt_log (by norm_num) (by norm_num)
  obtain ⟨N,hN⟩ := exists_nat_gt (log 2 / h + 1)
  have Npos : 0<N := by exact_mod_cast (show (0:ℝ)<N by linarith [div_pos l2 hp])
  obtain ⟨j,k,kpos,_,approx⟩ := Real.exists_int_int_abs_mul_sub_le (log 3/log 2) Npos
  have uc : (1:ℝ)/((N:ℝ)+1) < 1 := (div_lt_one (by positivity)).mpr (by exact_mod_cast (show 1<N+1 by omega))
  have kk : (1:ℝ) ≤ k := by exact_mod_cast (show (1:ℤ) ≤ k by omega)
  have ratio : 1 < log 3 / log 2 := (one_lt_div l2).mpr l23
  have jj : (0:ℝ) < j := by
    have z := (abs_le.mp approx).2
    nlinarith [mul_le_mul_of_nonneg_right kk (le_of_lt (lt_trans (by norm_num : (0:ℝ)<1) ratio))]
  let a := j.toNat
  let b := k.toNat
  have ja : (a:ℝ) = j := by exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ j by exact_mod_cast jj.le)
  have kb : (b:ℝ) = k := by exact_mod_cast Int.toNat_of_nonneg kpos.le
  have ap : 0<a := by exact_mod_cast (show 0<(a:ℝ) by linarith)
  have bp : 0<b := by exact_mod_cast (show 0<(b:ℝ) by rw [kb]; exact_mod_cast kpos)
  have est : |(b:ℝ)*log 3-(a:ℝ)*log 2| ≤ h := by
    have aux := mul_le_mul_of_nonneg_right approx l2.le
    rw [← abs_of_pos l2, ← abs_mul] at aux
    have eq : ((k:ℝ)*(log 3/log 2)-j)*|log 2| = k*log 3-j*log 2 := by rw [abs_of_pos l2]; field_simp
    have bound := (div_lt_iff₀ hp).mp (show log 2/h < (N:ℝ)+1 by linarith)
    rw [ja,kb]
    calc _ = |((k:ℝ)*(log 3/log 2)-j)*log 2| := by congr 1; field_simp
         _ ≤ (1/((N:ℝ)+1))*log 2 := by simpa [abs_of_pos l2] using aux
         _ ≤ h := by rw [one_div, inv_mul_eq_div]; exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  have ne : (a:ℝ)*log 2 ≠ (b:ℝ)*log 3 := by
    intro eq
    have e := congrArg exp eq
    rw [← Real.log_pow, ← Real.log_pow, Real.exp_log (by positivity), Real.exp_log (by positivity)] at e
    have natEq : (2:ℕ)^a = 3^b := by exact_mod_cast e
    have dvd : (2:ℕ) ∣ 3^b := natEq ▸ (dvd_pow_self 2 ap.ne')
    exact (by decide : ¬ (2:ℕ) ∣ 3) (Nat.prime_two.dvd_of_dvd_pow dvd)
  have sa : SumLog ((a:ℝ)*log 2) := ⟨a,0,by simp⟩
  have sb : SumLog ((b:ℝ)*log 3) := ⟨0,b,by simp⟩
  rcases lt_or_gt_of_ne ne with hab|hba
  · exact ⟨_,_,mul_pos (by exact_mod_cast ap) l2,hab,(abs_le.mp est).2,sa,sb⟩
  · exact ⟨_,_,mul_pos (by exact_mod_cast bp) l3,hba,by linarith [(abs_le.mp est).1],sb,sa⟩

theorem shell (d : ℕ) (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∃ m n : ℕ,
      x ≤ (2:ℝ)^(d*m) * 3^(d*n) ∧ (2:ℝ)^(d*m) * 3^(d*n) ≤ (1+ε)*x := by
  have dp : 0 < (d:ℝ) := by exact_mod_cast hd
  let h := log (1+ε)/(d:ℝ)
  obtain ⟨u,v,up,uv,small,su,sv⟩ := close h (div_pos (log_pos (by linarith)) dp)
  obtain ⟨T,net⟩ := grid up uv small su sv
  refine ⟨exp (d*T),?_⟩
  intro x hx
  have xp : 0<x := (exp_pos _).trans_le hx
  have tx : T ≤ log x/d := (le_div_iff₀ dp).mpr (by rw [mul_comm]; exact by simpa [Real.log_exp] using (Real.log_le_log (Real.exp_pos _) hx))
  obtain ⟨y,⟨m,n,rfl⟩,low,high⟩ := net (log x/d) tx
  have lo := (div_le_iff₀ dp).mp low
  have hi := mul_le_mul_of_nonneg_right high dp.le
  have h1 : log x ≤ (d*m:ℕ)*log 2 + (d*n:ℕ)*log 3 := by push_cast; linarith only [lo]
  have h2 : (d*m:ℕ)*log 2 + (d*n:ℕ)*log 3 ≤ log (1+ε)+log x := by
    dsimp [h] at hi
    field_simp at hi
    push_cast
    linarith only [hi]
  refine ⟨m,n,?_,?_⟩
  · have p := Real.exp_le_exp.mpr h1
    rw [Real.exp_log xp,Real.exp_add,← Real.log_pow,← Real.log_pow,Real.exp_log (by positivity),Real.exp_log (by positivity)] at p
    exact p
  · have p := Real.exp_le_exp.mpr h2
    rw [Real.exp_add,← Real.log_pow,← Real.log_pow,Real.exp_log (by positivity),Real.exp_log (by positivity),
      Real.exp_add,Real.exp_log (by linarith),Real.exp_log xp] at p
    exact p

end FurstScale
end

section
open Set Filter
open scoped Topology Pointwise
namespace FurstDifference
abbrev T := AddCircle (1:ℝ)

def Shell (d : ℕ) := ∀ {ε : ℝ}, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
  ∃ m n : ℕ, x ≤ (2:ℝ)^(d*m) * 3^(d*n) ∧ (2:ℝ)^(d*m) * 3^(d*n) ≤ (1+ε)*x

theorem int_zero (z : ℤ) : ((z:ℝ) : T) = 0 := by
  rw [show (z:ℝ) = z • (1:ℝ) by simp, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]

theorem centered (v : T) : ∃ t : ℝ, (t:T)=v ∧ |t|=‖v‖ ∧ |t| ≤ 1/2 := by
  obtain ⟨a,rfl⟩ := QuotientAddGroup.mk_surjective v
  refine ⟨a-round a,?_,?_,?_⟩
  · rw [AddCircle.coe_sub,int_zero,sub_zero]
  · exact (UnitAddCircle.norm_eq (x:=a)).symm
  · exact abs_sub_round a

theorem pow_mem {S : Set T} {b : ℕ} (hb : ∀ x ∈ S, b • x ∈ S)
    {x : T} (hx : x ∈ S) (m : ℕ) : b^m • x ∈ S := by
  induction m with
  | zero => simpa using hx
  | succ m ih => simpa [pow_succ',mul_smul] using hb _ ih

theorem expansion (S : Set T) (closed : IsClosed S) (d : ℕ) (shell : Shell d)
    (h2 : ∀ x ∈ S, (2^d:ℕ) • x ∈ S) (h3 : ∀ x ∈ S, (3^d:ℕ) • x ∈ S)
    (acc : (0:T) ∈ closure (S \ {0})) : S=univ := by
  apply Set.eq_univ_of_forall
  intro y
  rw [← closed.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨X,hs⟩ := shell (show 0 < ε/4 by linarith)
  have pos : 0 < |X|+1 := by positivity
  obtain ⟨v,hv,hclose⟩ := Metric.mem_closure_iff.mp acc (1/(|X|+1)) (by positivity)
  obtain ⟨t,ht,tn,tiny⟩ := centered v
  have near : |t| < 1/(|X|+1) := by simpa [tn,dist_comm] using hclose
  have nz : t ≠ 0 := by
    intro z
    apply hv.2
    simp [← ht,z]
  obtain ⟨u,hy,_,small⟩ := centered y
  let w := if 0<t then u+2 else u-2
  have two : ((2:ℝ):T)=0 := by simpa using int_zero 2
  have wy : (w:T)=y := by
    dsimp [w]
    split_ifs
    · simp [AddCircle.coe_add,two,hy]
    · simp [AddCircle.coe_sub,two,hy]
  have ww : 1 ≤ |w| ∧ |w| ≤ 3 := by
    have := abs_le.mp small
    dsimp [w]
    split_ifs
    · rw [abs_of_pos (show 0<u+2 by linarith)]
      constructor <;> linarith
    · rw [abs_of_neg (show u-2<0 by linarith)]
      constructor <;> linarith
  have ta := abs_pos.mpr nz
  have scale : X ≤ |w| / |t| := by
    apply (le_div_iff₀ ta).mpr
    have h := (lt_div_iff₀ pos).mp near
    nlinarith [abs_le.mp (le_refl |X|), mul_le_mul_of_nonneg_right (le_abs_self X) ta.le,ww.1]
  obtain ⟨m,n,lo,hi⟩ := hs _ scale
  let k := (2^d)^m*(3^d)^n
  have kc : (k:ℝ) = (2:ℝ)^(d*m)*3^(d*n) := by simp [k,pow_mul]
  have mv : k • v ∈ S := by simpa [k,mul_smul] using pow_mem h2 (pow_mem h3 hv.1 n) m
  refine ⟨k • v,mv,?_⟩
  have L := (div_le_iff₀ ta).mp lo
  have H : ((2:ℝ)^(d*m)*3^(d*n))*|t| ≤ (1+ε/4)*|w| := by
    rw [← le_div_iff₀ ta, mul_div_assoc]
    exact hi
  have err : |(k:ℝ)*t-w|<ε := by
    rw [kc,abs_lt]
    have E := mul_le_mul_of_nonneg_left ww.2 (show 0 ≤ ε/4 by linarith)
    have uz := abs_le.mp small
    dsimp [w] at H L E ⊢
    by_cases h : 0<t
    · simp only [if_pos h,abs_of_pos h,abs_of_pos (show 0<u+2 by linarith)] at *
      constructor <;> nlinarith
    · have neg : t<0 := lt_of_le_of_ne (le_of_not_gt h) nz
      simp only [if_neg h,abs_of_neg neg,abs_of_neg (show u-2<0 by linarith)] at *
      constructor <;> nlinarith
  rw [dist_comm,dist_eq_norm,← ht,← wy,← AddCircle.coe_nsmul,← AddCircle.coe_sub,nsmul_eq_mul]
  exact (QuotientAddGroup.norm_mk_le_norm (m:=(k:ℝ)*t-w)).trans_lt (by simpa only [Real.norm_eq_abs] using err)

end FurstDifference
end

section
open Set
open scoped Topology Pointwise
namespace FurstGap
abbrev T := AddCircle (1:ℝ)

theorem diff (d : ℕ)
    (expand : ∀ D : Set T, IsClosed D →
      (∀ v ∈ D, (2^d : ℕ) • v ∈ D) → (∀ v ∈ D, (3^d : ℕ) • v ∈ D) →
      (0 : T) ∈ closure (D \ {0}) → D = univ)
    (S : Set T) (closed : IsClosed S) (inf : S.Infinite)
    (h2 : MapsTo ((2^d : ℕ) • ·) S S) (h3 : MapsTo ((3^d : ℕ) • ·) S S)
    (h : T) : ∃ x ∈ S, x + h ∈ S := by
  let D : Set T := (fun p : T × T => p.2 - p.1) '' (S ×ˢ S)
  have hc : IsClosed D :=
    ((closed.isCompact.prod closed.isCompact).image (continuous_snd.sub continuous_fst)).isClosed
  have inv (q : ℕ) (hq : MapsTo (q • ·) S S) : ∀ v ∈ D, q • v ∈ D := by
    rintro v ⟨⟨a,b⟩, ⟨ha,hb⟩, rfl⟩
    exact ⟨(q • a, q • b), ⟨hq ha,hq hb⟩, by simp [nsmul_sub]⟩
  obtain ⟨a, ha, hacc⟩ := inf.exists_accPt_of_subset_isCompact closed.isCompact Subset.rfl
  have hz : (0 : T) ∈ closure (D \ {0}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨b, ⟨hd,hb⟩, hne⟩ := accPt_iff_nhds.mp hacc (Metric.ball a ε) (Metric.ball_mem_nhds a hε)
    refine ⟨b - a, ⟨⟨(a,b),⟨ha,hb⟩,rfl⟩, ?_⟩, ?_⟩
    · simpa using sub_ne_zero.mpr hne
    · simpa [dist_comm (0 : T), dist_eq_norm] using (Metric.mem_ball.mp hd)
  have full := expand D hc (inv _ h2) (inv _ h3) hz
  have hh : h ∈ D := full.symm ▸ mem_univ h
  obtain ⟨⟨a,b⟩, ⟨ha,hb⟩, rfl⟩ := hh
  exact ⟨a, ha, by simpa using hb⟩
end FurstGap
end

section
open Set
namespace FurstGrid

abbrev T := AddCircle (1 : ℝ)

def DiffProperty : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ (s : Set T), IsClosed s → s.Infinite →
    MapsTo ((2 ^ k : ℕ) • ·) s s → MapsTo ((3 ^ k : ℕ) • ·) s s →
    ∀ h : T, ∃ x ∈ s, x + h ∈ s

theorem pow_maps {s : Set T} {a : ℕ} (hs : MapsTo (a • ·) s s) (k : ℕ) :
    MapsTo ((a ^ k) • ·) s s := by
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
    intro x hx
    simpa [pow_succ', mul_smul] using hs (ih hx)

theorem infinite_of_aperiodic {s : Set T} {a : ℕ} (ha : 1 < a)
    (hs : MapsTo (a • ·) s s) {x : T} (hx : x ∈ s) (hord : ¬IsOfFinAddOrder x) :
    s.Infinite := by
  intro hf
  let := hf.to_subtype
  let f (n : ℕ) : s := ⟨(a ^ n) • x, pow_maps hs n hx⟩
  have hi : Function.Injective f := by
    intro n m he
    have he' : (a ^ n) • x = (a ^ m) • x := congrArg Subtype.val he
    have hp : a ^ n = a ^ m :=
      (AddRightCancelMonoid.injective_nsmul_iff_not_isOfFinAddOrder.mpr hord) he'
    exact (pow_right_strictMono₀ ha).injective hp
  exact not_injective_infinite_finite f hi

private def segment (Y : Set T) (h : T) (m : ℕ) : Set T :=
  {x | ∀ j ≤ m, x + j • h ∈ Y}

theorem has_grid (diff : DiffProperty) {Y : Set T} (hc : IsClosed Y) (hne : Y.Nonempty)
    (hord : ∀ x ∈ Y, ¬IsOfFinAddOrder x) {k : ℕ} (hk : 0 < k)
    (h2 : MapsTo ((2 ^ k : ℕ) • ·) Y Y) (h3 : MapsTo ((3 ^ k : ℕ) • ·) Y Y)
    {h : T} (f2 : (2 ^ k : ℕ) • h = h) (f3 : (3 ^ k : ℕ) • h = h) (m : ℕ) :
    ∃ x : T, ∀ j ≤ m, x + j • h ∈ Y := by
  change (segment Y h m).Nonempty
  induction m with
  | zero =>
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, by simpa [segment] using hx⟩
  | succ m ih =>
    have closed : IsClosed (segment Y h m) := by
      simp only [segment, Set.ofPred_forall]
      exact isClosed_iInter fun j => isClosed_iInter fun _ =>
        hc.preimage (continuous_id.add continuous_const)
    have inv (a : ℕ) (her : MapsTo (a • ·) Y Y) (fixh : a • h = h) :
        MapsTo (a • ·) (segment Y h m) (segment Y h m) := by
      intro x hx j hj
      have hj' := her (hx j hj)
      simpa [nsmul_add, smul_comm a j, fixh] using hj'
    have big : (segment Y h m).Infinite := by
      obtain ⟨x, hx⟩ := ih
      exact infinite_of_aperiodic (one_lt_pow₀ (by decide : 1 < (2 : ℕ)) hk.ne')
        (inv _ h2 f2) hx (hord x (by simpa using hx 0 (Nat.zero_le _)))
    obtain ⟨x, hx, hxh⟩ := diff k hk (segment Y h m) closed big (inv _ h2 f2) (inv _ h3 f3) h
    refine ⟨x, fun j hj => ?_⟩
    by_cases hj' : j ≤ m
    · exact hx j hj'
    · have he : j = m + 1 := by omega
      simpa [he, succ_nsmul, add_assoc, add_comm, add_left_comm] using hxh m le_rfl


private theorem grid_near_zero {q : ℕ} (hq : 0 < q) {Y : Set T}
    {x : T} (hgrid : ∀ j ≤ q, x + j • (↑(1 / (q : ℝ)) : T) ∈ Y) :
    ∃ y ∈ Y, dist 0 y < 1 / (q : ℝ) := by
  have hrep : x ∈ ((↑) : ℝ → T) '' Icc (-1) (-1 + 1) := by
    rw [AddCircle.coe_image_Icc_eq]
    exact mem_univ _
  obtain ⟨u, ⟨hu₁, hu₂⟩, rfl⟩ := hrep
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  let j : ℕ := ⌊-u * q⌋₊
  have hj : j ≤ q := Nat.floor_le_of_le (by nlinarith)
  have h₁ : (j : ℝ) ≤ -u * q := Nat.floor_le (by nlinarith)
  have h₂ : -u * q < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  let w : ℝ := u + j / (q : ℝ)
  have he : (↑w : T) = (↑u : T) + j • (↑(1 / (q : ℝ)) : T) := by
    rw [← AddCircle.coe_nsmul, ← AddCircle.coe_add, nsmul_eq_mul]
    congr 1
    dsimp [w]
    ring
  refine ⟨↑w, he ▸ hgrid j hj, ?_⟩
  rw [dist_zero_left]
  apply lt_of_le_of_lt (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1 : ℝ)) (m := w))
  rw [Real.norm_eq_abs, abs_lt]
  constructor
  · dsimp [w]
    rw [add_div', ← neg_div, div_lt_div_iff_of_pos_right hq'] <;> linarith
  · dsimp [w]
    rw [add_div', div_lt_div_iff_of_pos_right hq'] <;> linarith

theorem contains_torsion (diff : DiffProperty) {Y : Set T} (hc : IsClosed Y) (hne : Y.Nonempty)
    (h2 : MapsTo ((2 : ℕ) • ·) Y Y) (h3 : MapsTo ((3 : ℕ) • ·) Y Y) :
    ∃ x ∈ Y, IsOfFinAddOrder x := by
  by_contra! hord
  suffices hz : (0 : T) ∈ Y by exact hord 0 hz (by simp)
  rw [← hc.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  obtain ⟨q, hnq, hprime⟩ := Nat.exists_infinite_primes (n + 4)
  let h : T := ↑(1 / (q : ℝ))
  have hq : 0 < q := hprime.pos
  have fixed (a : ℕ) (apos : 0 < a) (aq : a < q) : (a ^ q.totient) • h = h := by
    have cop : a.Coprime q :=
      (hprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt apos aq)).symm
    nth_rewrite 2 [← one_nsmul h]
    apply AddRightCancelMonoid.nsmul_eq_nsmul_iff_modEq.mpr
    rw [show addOrderOf h = q from AddCircle.addOrderOf_period_div hq]
    exact Nat.ModEq.pow_totient cop
  obtain ⟨x, hx⟩ := has_grid diff hc hne hord (Nat.totient_pos.mpr hq) (pow_maps h2 _)
    (pow_maps h3 _) (fixed 2 (by decide) (by omega)) (fixed 3 (by decide) (by omega)) q
  obtain ⟨y, hy, hd⟩ := grid_near_zero hq hx
  refine ⟨y, hy, hd.trans ?_⟩
  have hnq' : (n : ℝ) ≤ q := by exact_mod_cast (show n ≤ q by omega)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_lt_iff₀ hq']
  have := (div_lt_iff₀ hε).mp (hn.trans_le hnq')
  linarith

end FurstGrid
end

section
open Set Filter
open scoped Topology
namespace FurstOrbit
abbrev T := AddCircle (1 : ℝ)
def orbit (ξ : ℝ) : Set T := {x | ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ x = ↑(ξ * (2 ^ m * 3 ^ n : ℕ))}
theorem noTorsion {ξ : ℝ} (irr : Irrational ξ) {x : T} (hx : x ∈ orbit ξ) : ¬ IsOfFinAddOrder x := by
  obtain ⟨m,n,_,_,rfl⟩ := hx
  intro ht
  obtain ⟨q,hq⟩ := AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div.mp ht
  have hi := (irrational_mul_natCast_iff (x:=ξ) (n:=2^m*3^n)).2 ⟨by positivity,irr⟩
  exact hi ⟨q,by simpa using hq⟩

theorem invTwo (ξ : ℝ) : MapsTo (fun x : T => 2 • x) (orbit ξ) (orbit ξ) := by
  rintro _ ⟨m,n,hm,hn,rfl⟩
  refine ⟨m+1,n,by omega,hn,?_⟩
  dsimp only
  rw [← AddCircle.coe_nsmul (p:= (1:ℝ))]
  apply congrArg (fun a : ℝ => (a : T))
  push_cast
  simp only [nsmul_eq_mul,pow_succ]
  ring
theorem invThree (ξ : ℝ) : MapsTo (fun x : T => 3 • x) (orbit ξ) (orbit ξ) := by
  rintro _ ⟨m,n,hm,hn,rfl⟩
  refine ⟨m,n+1,hm,by omega,?_⟩
  dsimp only
  rw [← AddCircle.coe_nsmul (p:= (1:ℝ))]
  apply congrArg (fun a : ℝ => (a : T))
  push_cast
  simp only [nsmul_eq_mul,pow_succ]
  ring

theorem forward_pow {S : Set T} {b : ℕ} (hb : MapsTo (fun x : T => b • x) S S) (n : ℕ) :
    MapsTo (fun x : T => (b^n) • x) S S := by
  intro x hx
  induction n with
  | zero => simpa using hx
  | succ n ih => simpa [pow_succ',mul_smul] using hb ih

theorem minPeriod {x : T} (ht : IsOfFinAddOrder x) (b : ℕ) :
    ∃ i k : ℕ, 0 < k ∧ (b^k) • ((b^i) • x) = (b^i) • x := by
  have hd := addOrderOf_pos_iff.mpr ht
  have H := (Set.finite_Iio (addOrderOf x)).exists_lt_map_eq_of_forall_mem
    (f := fun n : ℕ => b^n % addOrderOf x) (fun _ => Nat.mod_lt _ hd)
  obtain ⟨i,j,hij,h⟩ := H
  refine ⟨i,j-i,by omega,?_⟩
  rw [← mul_smul,← pow_add, Nat.sub_add_cancel hij.le]
  exact nsmul_eq_nsmul_iff_modEq.mpr h.symm

theorem fixed_from_torsion {Y : Set T}
    (two : MapsTo (fun x : T => 2 • x) Y Y) (three : MapsTo (fun x : T => 3 • x) Y Y)
    {x : T} (hx : x ∈ Y) (ht : IsOfFinAddOrder x) :
    ∃ r ∈ Y, IsOfFinAddOrder r ∧ ∃ d : ℕ, 0<d ∧ (2^d) • r = r ∧ (3^d) • r = r := by
  obtain ⟨i,a,ha,hA⟩ := minPeriod ht 2
  let y := (2^i) • x
  have hy : IsOfFinAddOrder y := ht.nsmul
  obtain ⟨j,b,hb,hB⟩ := minPeriod hy 3
  let r := (3^j) • y
  have fa : (2^a) • r = r := by
    dsimp [r,y]
    rw [smul_comm (2^a) (3^j),hA]
  have lift {q : ℕ} (h : q • r = r) (k : ℕ) : (q^k) • r = r := by
    induction k with
    | zero => simp
    | succ k ih => simpa [pow_succ',mul_smul,ih] using h
  refine ⟨r,forward_pow three j (forward_pow two i hx),hy.nsmul,a*b,Nat.mul_pos ha hb,?_,?_⟩
  · rw [pow_mul]; exact lift fa b
  · rw [Nat.mul_comm a b,pow_mul]; exact lift hB a

theorem accum {ξ : ℝ} (irr : Irrational ξ) {r : T} (ht : IsOfFinAddOrder r)
    (hr : r ∈ closure (orbit ξ)) : r ∈ closure (closure (orbit ξ) \ {r}) := by
  apply closure_mono _ hr
  intro x hx
  exact ⟨subset_closure hx, fun e => noTorsion irr hx ((Set.mem_singleton_iff.mp e).symm ▸ ht)⟩

theorem translate_expansion (Y : Set T) (cY : IsClosed Y) (d : ℕ)
    (expand : ∀ S : Set T, IsClosed S → MapsTo ((2^d : ℕ) • ·) S S →
      MapsTo ((3^d : ℕ) • ·) S S → (0 : T) ∈ closure (S \ {0}) → S = univ)
    (two : MapsTo ((2^d : ℕ) • ·) Y Y) (three : MapsTo ((3^d : ℕ) • ·) Y Y)
    (r : T) (fix2 : (2^d : ℕ) • r = r) (fix3 : (3^d : ℕ) • r = r)
    (accumR : r ∈ closure (Y \ {r})) : Y = univ := by
  let S : Set T := (fun x => x+r) ⁻¹' Y
  have closedS : IsClosed S := cY.preimage (continuous_id.add continuous_const)
  have inv (b : ℕ) (fix : b • r = r) (h : MapsTo (b • ·) Y Y) : MapsTo (b • ·) S S := by
    intro x hx
    change b • x + r ∈ Y
    simpa only [nsmul_add,fix] using h (show x+r ∈ Y from hx)
  have shift : MapsTo (fun x : T => x-r) (Y \ {r}) (S \ {0}) := by
    intro x hx
    refine ⟨?_,?_⟩
    · change x-r+r ∈ Y
      simpa only [sub_add_cancel] using hx.1
    · exact fun eq => hx.2 (Set.mem_singleton_iff.mpr (sub_eq_zero.mp (Set.mem_singleton_iff.mp eq)))
  have zero : (0 : T) ∈ closure (S \ {0}) := by
    simpa using shift.closure (continuous_id.sub continuous_const) accumR
  have all := expand S closedS (inv _ fix2 two) (inv _ fix3 three) zero
  apply Set.eq_univ_of_forall
  intro x
  have hx : x-r ∈ S := all.symm ▸ Set.mem_univ _
  simpa only [S,Set.mem_preimage,sub_add_cancel] using hx

theorem assemble
    (torsion : ∀ Y : Set T, IsClosed Y → Y.Nonempty → MapsTo ((2:ℕ) • ·) Y Y →
      MapsTo ((3:ℕ) • ·) Y Y → ∃ x ∈ Y, IsOfFinAddOrder x)
    (expand : ∀ d : ℕ, 0 < d → ∀ S : Set T, IsClosed S → MapsTo ((2^d:ℕ) • ·) S S →
      MapsTo ((3^d:ℕ) • ·) S S → (0:T) ∈ closure (S \ {0}) → S = univ)
    (ξ : ℝ) (irr : Irrational ξ) : Dense (orbit ξ) := by
  let Y := closure (orbit ξ)
  have two : MapsTo ((2:ℕ) • ·) Y Y := (invTwo ξ).closure (by fun_prop)
  have three : MapsTo ((3:ℕ) • ·) Y Y := (invThree ξ).closure (by fun_prop)
  have ne : Y.Nonempty := ⟨_,subset_closure ⟨1,1,by decide,by decide,rfl⟩⟩
  obtain ⟨x,hx,ht⟩ := torsion Y isClosed_closure ne two three
  obtain ⟨r,hr,tr,d,hd,f2,f3⟩ := fixed_from_torsion two three hx ht
  apply dense_iff_closure_eq.mpr
  exact translate_expansion Y isClosed_closure d (expand d hd)
    (forward_pow two d) (forward_pow three d) r f2 f3 (accum irr tr hr)

end FurstOrbit
end

theorem OMA.solution : type_of% @Bugeaud06.furstenberg_two_three := by
  have expansion (d : ℕ) (hd : 0 < d) (S : Set FurstOrbit.T) (hc : IsClosed S)
      (h2 : Set.MapsTo ((2^d : ℕ) • ·) S S) (h3 : Set.MapsTo ((3^d : ℕ) • ·) S S)
      (ha : (0 : FurstOrbit.T) ∈ closure (S \ {0})) : S = Set.univ :=
    FurstDifference.expansion S hc d (FurstScale.shell d hd) (fun _ hx => h2 hx) (fun _ hx => h3 hx) ha
  have diff : FurstGrid.DiffProperty := by
    intro d hd S hc hi h2 h3 h
    apply FurstGap.diff d _ S hc hi h2 h3 h
    intro D closed two three acc
    exact expansion d hd D closed (fun {x} hx => two x hx) (fun {x} hx => three x hx) acc
  exact FurstOrbit.assemble (fun _ => FurstGrid.contains_torsion diff) expansion
