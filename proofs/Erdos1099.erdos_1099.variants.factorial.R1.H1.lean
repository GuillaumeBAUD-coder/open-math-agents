import OMAReductions.R_Erdos1099_erdos_1099_variants_factorial_R1
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Upper approximation by factorial divisors

The finite-difference construction through `FactorialGaps.centre_bounds` is
Marcus Buffett's proof from open-math-agents PR 2287, commit
c07754576e5a13a93fb5ed44e03365ecaa6e0232.
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2287

For the upper approximation in dk8827's reduction (PR 1929), apply that
lower approximation to divisors of (k-1)! at a logarithmic point slightly
above log(x/k). Multiplication by k gives a divisor of k! strictly above x.
Stirling's bound makes the logarithmic error uniform on the required band.
-/

open Finset Filter Real Erdos1099
namespace FactorialGaps

-- The j-th forward difference of −log is a logarithm of a quotient of two
-- products of small integers. Its magnitude is comparable to x^(-j).
noncomputable def g : ℕ → ℝ → ℝ
  | 0, x => - Real.log x
  | j+1, x => j.factorial/x^(j+1)

lemma g_deriv (j : ℕ) {x : ℝ} (hx : 0 < x) : HasDerivAt (g j) (-g (j+1) x) x := by
  cases j with
  | zero =>
    change HasDerivAt (fun z => -Real.log z) _ x
    exact (Real.hasDerivAt_log hx.ne').neg.congr_deriv (by simp [g])
  | succ j =>
    change HasDerivAt (fun z : ℝ => (j.factorial:ℝ)/z^(j+1)) _ x
    apply ((hasDerivAt_const x (j.factorial:ℝ)).div ((hasDerivAt_id x).pow (j+1)) (pow_ne_zero _ hx.ne')).congr_deriv
    simp only [g,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,id_eq,Nat.add_sub_cancel,
      mul_one,zero_mul,zero_sub,Pi.pow_apply,id_eq]
    field_simp; ring

noncomputable def diff : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0,f => f
  | j+1,f => fun x => diff j f x - diff j f (x+1)

lemma diff_deriv (k j : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (diff k (g j)) (-diff k (g (j+1)) x) x := by
  induction k generalizing x with
  | zero => exact g_deriv j hx
  | succ k ih =>
    apply ((ih hx).sub ((ih (show 0 < x+1 by linarith)).comp_add_const x 1)).congr_deriv
    simp [diff]; ring

lemma diff_value (k j : ℕ) (x : ℝ) (hx : 0 < x) :
    ∃ y : ℝ, x ≤ y ∧ y ≤ x+k ∧ diff k (g j) x = g (j+k) y := by
  induction k generalizing j x with
  | zero => exact ⟨x,le_rfl,by simp,by simp [diff]⟩
  | succ k ih =>
    let f := diff k (g j)
    have deriv {z : ℝ} (hz : x ≤ z) : HasDerivAt f (-diff k (g (j+1)) z) z := diff_deriv k j (hx.trans_le hz)
    obtain ⟨z,hz,he⟩ := exists_hasDerivAt_eq_slope f (fun z => -diff k (g (j+1)) z) (a := x) (b := x+1) (by linarith)
      (fun z hz => (deriv hz.1).continuousAt.continuousWithinAt) (fun z hz => deriv hz.1.le)
    obtain ⟨y,hy,hy',hyv⟩ := ih (j+1) z (hx.trans hz.1)
    refine ⟨y,hz.1.le.trans hy,by push_cast; linarith [hz.2],?_⟩
    simp only [add_sub_cancel_left,div_one] at he
    change f x - f (x+1) = _
    rw [show j+(k+1)=j+1+k by omega,← hyv]; linarith

def pair : ℕ → ℕ → ℕ × ℕ
  | 0,x => (1,x)
  | j+1,x => ((pair j x).1*(pair j (x+1)).2,(pair j x).2*(pair j (x+1)).1)

lemma pair_prop (j x : ℕ) (hx : 0 < x) :
    0 < (pair j x).1 ∧ 0 < (pair j x).2 ∧
    (pair j x).1*(pair j x).2 ∣ (x+j).factorial ^ (2^j) ∧
    Real.log (pair j x).1 - Real.log (pair j x).2 = diff j (g 0) x := by
  induction j generalizing x with
  | zero => simp [pair,g,diff,hx,Nat.dvd_factorial hx le_rfl]
  | succ j ih =>
    obtain ⟨ha,hb,hd,he⟩ := ih x hx
    obtain ⟨ha',hb',hd',he'⟩ := ih (x+1) (by omega)
    have H := Nat.mul_dvd_mul (hd.trans (pow_dvd_pow_of_dvd
      (Nat.factorial_dvd_factorial (by omega : x+j ≤ x+(j+1))) _)) hd'
    dsimp only [pair]
    refine ⟨Nat.mul_pos ha hb',Nat.mul_pos hb ha',?_,?_⟩
    · convert H using 1
      · ring
      · rw [show x+1+j=x+(j+1) by omega,pow_succ,pow_mul,sq]
    · push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
      simp only [Nat.cast_add,Nat.cast_one] at he'
      dsimp only [diff]; linarith

noncomputable def gap (j x : ℕ) := Real.log (pair j x).1 - Real.log (pair j x).2

lemma gap_bounds {j x : ℕ} (hj : 1 ≤ j) (hx : j ≤ x) :
    1/(2*(x:ℝ))^j ≤ gap j x ∧ gap j x ≤ (j.factorial:ℝ)/(x:ℝ)^j := by
  have hxpos : 0 < x := by omega
  obtain ⟨y,hy,hy',he⟩ := diff_value j 0 (x:ℝ) (by positivity)
  have hp := (pair_prop j x (by omega)).2.2.2
  cases j with
  | zero => omega
  | succ j =>
    rw [Nat.zero_add] at he
    simp only [g] at he
    rw [gap,hp,he]
    constructor
    · apply div_le_div₀ (by positivity) (by exact_mod_cast (show 1 ≤ j.factorial from Nat.factorial_pos j))
        (pow_pos (lt_of_lt_of_le (by positivity : (0:ℝ) < x) hy) _) _
      apply pow_le_pow_left₀ (by linarith) _ _
      linarith [show ((j+1:ℕ):ℝ) ≤ x by exact_mod_cast hx]
    · apply div_le_div₀ (by positivity) (by exact_mod_cast Nat.factorial_le (Nat.le_succ j)) (by positivity) _
      gcongr

def copies (D x : ℕ) := 2^D * D.factorial * x^2

def box (D x : ℕ) : ℕ → ℕ
  | 0 => 1
  | j+1 => box D x j * ((pair (j+1) x).1*(pair (j+1) x).2)^(copies D x)

def base (D x : ℕ) : ℕ → ℕ
  | 0 => 1
  | j+1 => base D x j * (pair (j+1) x).2^(copies D x)

lemma box_pos (D j : ℕ) {x : ℕ} (hx : 0 < x) : 0 < box D x j := by
  induction j with
  | zero => simp [box]
  | succ j ih =>
    obtain ⟨ha,hb,-⟩ := pair_prop (j+1) x hx
    exact Nat.mul_pos ih (pow_pos (Nat.mul_pos ha hb) _)

lemma base_dvd (D j x : ℕ) : base D x j ∣ box D x j := by
  induction j with
  | zero => rfl
  | succ j ih => exact Nat.mul_dvd_mul ih (pow_dvd_pow_of_dvd (dvd_mul_left ..) _)

lemma box_dvd (D x j : ℕ) (hx : 0 < x) (hj : j ≤ D) :
    box D x j ∣ (x+D).factorial^(j*2^D*copies D x) := by
  induction j with
  | zero => simp [box]
  | succ j ih =>
    rw [Nat.succ_mul,Nat.add_mul,pow_add]
    apply Nat.mul_dvd_mul (ih (by omega))
    rw [pow_mul]
    apply pow_dvd_pow_of_dvd
    exact (pair_prop (j+1) x hx).2.2.1 |>.trans
      ((pow_dvd_pow_of_dvd (Nat.factorial_dvd_factorial (Nat.add_le_add_left hj x)) _).trans
        (pow_dvd_pow _ (Nat.pow_le_pow_right (by decide) hj)))

lemma net (D x j : ℕ) (hx : 0 < x) (hDx : D ≤ x) (hj : j ≤ D) {u : ℝ}
    (hu : 0 ≤ u) (hu' : u ≤ x) : ∃ v : ℕ, 0 < v ∧ v ∣ box D x j ∧
      0 ≤ u + Real.log (base D x j) - Real.log v ∧
      u + Real.log (base D x j) - Real.log v ≤ (D.factorial:ℝ)*x/(x:ℝ)^j := by
  induction j with
  | zero =>
    refine ⟨1,by decide,dvd_rfl,by simpa [base],?_⟩
    simp only [base,Nat.cast_one,Real.log_one,add_zero,sub_zero,pow_zero,div_one]
    exact hu'.trans (le_mul_of_one_le_left (by positivity) (by exact_mod_cast D.factorial_pos))
  | succ j ih =>
    obtain ⟨v,hv,hdiv,hlo,hhi⟩ := ih (by omega)
    let e := u+Real.log (base D x j)-Real.log v
    let g := gap (j+1) x
    obtain ⟨hg,hg'⟩ := gap_bounds (j := j+1) (by omega) (hj.trans hDx)
    have gpos : 0 < g := lt_of_lt_of_le (by positivity) hg
    let r := ⌊e/g⌋₊
    have rle : r ≤ copies D x := by
      apply Nat.floor_le_of_le
      apply (div_le_iff₀ gpos).mpr
      have hx' : (0:ℝ) < x := by positivity
      have hfactor : (2:ℝ)^(j+1) ≤ (2:ℝ)^D := pow_le_pow_right₀ (by norm_num) hj
      have h1 : (D.factorial:ℝ)*x/(x:ℝ)^j ≤ (copies D x:ℝ) * (1/(2*(x:ℝ))^(j+1)) := by
        dsimp [copies]; push_cast
        rw [mul_pow,pow_succ (x:ℝ)]
        field_simp
        rw [pow_succ (x:ℝ)]; nlinarith only [mul_le_mul_of_nonneg_right hfactor (show (0:ℝ) ≤ (x:ℝ)*(x:ℝ)^j by positivity)]
      exact hhi.trans (h1.trans (mul_le_mul_of_nonneg_left hg (by positivity)))
    let a := (pair (j+1) x).1
    let b := (pair (j+1) x).2
    obtain ⟨ha,hb,-⟩ := pair_prop (j+1) x hx
    change 0 < a at ha
    change 0 < b at hb
    refine ⟨v*(a^r*b^(copies D x-r)),by positivity,Nat.mul_dvd_mul hdiv ?_,?_⟩
    · rw [mul_pow]
      exact Nat.mul_dvd_mul (pow_dvd_pow a rle) (pow_dvd_pow b (Nat.sub_le ..))
    · have hpbase : 0 < base D x j := Nat.pos_of_dvd_of_pos (base_dvd ..) (box_pos D j hx)
      have eq : u+Real.log (base D x (j+1))-Real.log ((v*(a^r*b^(copies D x-r)):ℕ):ℝ) = e-r*g := by
        simp only [base,Nat.cast_mul,Nat.cast_pow]
        rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity)]
        simp only [Real.log_pow,Nat.cast_sub rle]
        dsimp only [e,g,gap,a,b]; ring
      rw [eq]
      have hr := (le_div_iff₀ gpos).mp (Nat.floor_le (div_nonneg hlo gpos.le) : (r:ℝ) ≤ e/g)
      have hr' := (div_lt_iff₀ gpos).mp (Nat.lt_floor_add_one (e/g))
      refine ⟨by linarith,(show e-r*g ≤ g by linarith).trans (hg'.trans ?_)⟩
      gcongr
      have hfac : ((j+1).factorial:ℝ) ≤ D.factorial := by exact_mod_cast Nat.factorial_le hj
      exact hfac.trans (le_mul_of_one_le_right (by positivity) (by exact_mod_cast hx))

lemma coarse (m : ℕ) (s : ℕ) (hs : s ∣ m.factorial) (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ Real.log s) :
    ∃ y : ℕ, 0 < y ∧ y ∣ s ∧ 0 ≤ u-Real.log y ∧ u-Real.log y ≤ Real.log m := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    have hs' := Nat.pos_of_dvd_of_pos hs m.factorial_pos
    by_cases h1 : s=1
    · subst s; simp at hu'
      exact ⟨1,by decide,dvd_rfl,by simpa,by simpa using hu'.trans (Real.log_natCast_nonneg m)⟩
    let p := s.minFac
    have pp := Nat.minFac_prime h1
    obtain ⟨r,hr⟩ := Nat.minFac_dvd s
    change s=p*r at hr
    have hp : 0 < p := pp.pos
    have hpp : 1 < p := pp.one_lt
    have hpr : 0 < r := Nat.pos_of_dvd_of_pos (hr ▸ dvd_mul_left .. : r ∣ s) hs'
    have hrd : r ∣ s := hr ▸ dvd_mul_left ..
    have he : Real.log s = Real.log p+Real.log r := by rw [hr,Nat.cast_mul,Real.log_mul (by positivity) (by positivity)]
    by_cases hle : u ≤ Real.log r
    · obtain ⟨y,hy,hd,hlo,hhi⟩ := ih r (by nlinarith only [hr,Nat.mul_le_mul_right r (by omega : 2 ≤ p),hpr])
        (hrd.trans hs) hle
      exact ⟨y,hy,hd.trans hrd,hlo,hhi⟩
    · have hpm := (pp.dvd_factorial.mp ((Nat.minFac_dvd s).trans hs))
      exact ⟨r,hpr,hrd,by linarith,by linarith [Real.log_le_log (by positivity : (0:ℝ) < p) (by exact_mod_cast hpm : (p:ℝ) ≤ m)]⟩

def size (D x : ℕ) := (x+D)*(D*2^D*copies D x)
lemma box_factorial {D x : ℕ} (hx : 0 < x) : box D x D ∣ (size D x).factorial := by
  apply (box_dvd D x D hx le_rfl).trans
  simpa [size,Nat.mul_comm] using
    (Nat.prod_factorial_dvd_factorial_sum (range (D*2^D*copies D x)) (fun _ => x+D))

lemma fac_sq_le {a b : ℕ} (h : 2*a ≤ b) : a.factorial^2 ≤ b.factorial := by
  apply Nat.le_of_dvd b.factorial_pos
  rw [sq]
  exact (Nat.factorial_mul_factorial_dvd_factorial_add a a).trans (Nat.factorial_dvd_factorial (by omega))

lemma local_net {m D x : ℕ} (hx : 0 < x) (hD : D ≤ x) (hs : 2*size D x < m)
    (hm : Real.log m ≤ x) (u : ℝ) (hu : Real.log (m-1:ℕ).factorial ≤ 2*u) (hu' : 2*u ≤ Real.log m.factorial) :
    ∃ v : ℕ, 0 < v ∧ v ∣ m.factorial ∧ 0 ≤ u-Real.log v ∧ u-Real.log v ≤ (D.factorial:ℝ)*x/(x:ℝ)^D := by
  let B := box D x D
  let b := base D x D
  have hB : B ∣ (size D x).factorial := box_factorial hx
  have hBp : 0 < B := box_pos D D hx
  have hb : b ∣ B := base_dvd ..
  have hbp : 0 < b := Nat.pos_of_dvd_of_pos hb hBp
  have bound (k : ℕ) (hk : 2*size D x ≤ k) : 2*Real.log B ≤ Real.log k.factorial := by
    have hh := (Nat.pow_le_pow_left (Nat.le_of_dvd (size D x).factorial_pos hB) 2).trans (fac_sq_le hk)
    have H := Real.log_le_log (by positivity : (0:ℝ) < (B:ℝ)^2) (by exact_mod_cast hh : (B:ℝ)^2 ≤ (k.factorial:ℝ))
    simpa [Real.log_pow] using H
  have hBlog := bound (m-1) (by omega)
  have hBlog' := bound m (by omega)
  obtain ⟨r,hr⟩ := hB.trans (Nat.factorial_dvd_factorial (by omega : size D x ≤ m))
  have hrp : 0 < r := Nat.pos_of_dvd_of_pos (hr ▸ dvd_mul_left .. : r ∣ m.factorial) m.factorial_pos
  have hl : Real.log m.factorial = Real.log B+Real.log r := by rw [hr,Nat.cast_mul,Real.log_mul (by positivity) (by positivity)]
  have hble := Real.log_le_log (by positivity : (0:ℝ) < b) (by exact_mod_cast Nat.le_of_dvd hBp hb : (b:ℝ) ≤ B)
  obtain ⟨y,hyp,hyd,hylo,hyhi⟩ := coarse m r (hr ▸ dvd_mul_left ..) (u-Real.log b) (by linarith)
    (by linarith [Real.log_natCast_nonneg b])
  obtain ⟨z,hzp,hzd,hzlo,hzhi⟩ := net D x D hx hD le_rfl hylo (hyhi.trans hm)
  refine ⟨z*y,Nat.mul_pos hzp hyp,hr ▸ Nat.mul_dvd_mul hzd hyd,?_⟩
  rw [Nat.cast_mul,Real.log_mul (by positivity) (by positivity)]
  change 0 ≤ u - Real.log b - Real.log y + Real.log b - Real.log z at hzlo
  change u - Real.log b - Real.log y + Real.log b - Real.log z ≤ _ at hzhi
  constructor <;> linarith

lemma sqrt_scale (m : ℕ) : (m.sqrt.sqrt)^4 ≤ m ∧ m < (m.sqrt.sqrt+1)^4 := by
  let t := m.sqrt.sqrt
  have h1 := Nat.sqrt_le m
  have h2 := Nat.sqrt_le m.sqrt
  have h3 := Nat.lt_succ_sqrt m
  have h4 := Nat.lt_succ_sqrt m.sqrt
  constructor
  · nlinarith only [h1,Nat.mul_le_mul h2 h2]
  · have hle : m.sqrt+1 ≤ (t+1)*(t+1) := by exact h4
    nlinarith only [h3,Nat.mul_le_mul hle hle]

lemma log_size (m : ℕ) (hm : 0 < m) : Real.log m.factorial ≤ (m:ℝ)^2 := by
  have hh := Real.log_le_log (by positivity : (0:ℝ) < m.factorial)
    (by exact_mod_cast m.factorial_le_pow : (m.factorial:ℝ) ≤ (m:ℝ)^m)
  rw [Real.log_pow] at hh
  nlinarith only [hh,mul_le_mul_of_nonneg_left (Real.log_le_self (x := m) (by positivity)) (show (0:ℝ) ≤ m by positivity)]

lemma centre_bounds (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ u : ℝ,
    0 ≤ u → 2*u ≤ Real.log n.factorial →
    ∃ v : ℕ, 0 < v ∧ v ∣ n.factorial ∧ 0 ≤ u-Real.log v ∧
      (u-Real.log v)*(1+u)^k ≤ C := by
  let D := 8*k+1
  let K := D*2^D*(2^D*D.factorial)
  have logE := Real.isLittleO_log_id_atTop.bound (c := (1:ℝ)/8) (by norm_num)
  obtain ⟨t₀,ht₀⟩ := eventually_atTop.mp
    (((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1:ℝ)))).eventually logE)
  let T := max t₀ (max (4*K+1) (max D 1))
  let U := ((T+1)^4 : ℕ)
  let C := max ((U:ℝ)^2 * (1+(U:ℝ)^2)^k) ((D.factorial:ℝ)*257^k)
  refine ⟨C,lt_of_lt_of_le (by positivity : (0:ℝ) < (D.factorial:ℝ)*257^k) (le_max_right ..),?_⟩
  intro n u hu hun
  classical
  let cond := fun m : ℕ => 2*u ≤ Real.log m.factorial
  have hex : ∃ m,cond m := ⟨n,hun⟩
  let m := Nat.find hex
  have hmn : m ≤ n := Nat.find_min' hex hun
  have hmu : 2*u ≤ Real.log m.factorial := Nat.find_spec hex
  let x := m.sqrt.sqrt
  obtain ⟨hlo,hhi⟩ := sqrt_scale m
  change x^4 ≤ m at hlo
  change m < (x+1)^4 at hhi
  by_cases small : x < T
  · have hmU : m ≤ U := hhi.le.trans (Nat.pow_le_pow_left (by omega : x+1 ≤ T+1) 4)
    have hUpos : 0 < U := by dsimp [U]; positivity
    have hlogU := Real.log_le_log (by positivity : (0:ℝ) < m.factorial)
      (by exact_mod_cast Nat.factorial_le hmU : (m.factorial:ℝ) ≤ U.factorial)
    have huU : u ≤ (U:ℝ)^2 := by linarith [log_size U hUpos]
    refine ⟨1,by decide,one_dvd _,by simpa,?_⟩
    simp only [Nat.cast_one,Real.log_one,sub_zero]
    exact (mul_le_mul huU (pow_le_pow_left₀ (by linarith) (by linarith) k) (by positivity) (by positivity)).trans (le_max_left ..)
  have hxT : T ≤ x := by omega
  have hx : 0 < x := by dsimp [T] at hxT; omega
  have hD : D ≤ x := by dsimp [T] at hxT; omega
  have hK : 4*K < x := by dsimp [T] at hxT; omega
  have hx' : (1:ℝ) ≤ x := by exact_mod_cast hx
  have hm : 0 < m := (pow_pos hx 4).trans_le hlo
  have hsize : 2*size D x < m := by
    have HE : size D x = (x+D)*K*x^2 := by dsimp [size,K,copies]; ring
    rw [HE]
    apply lt_of_lt_of_le _ hlo
    have h1 := Nat.mul_le_mul_right (K*x^2) (show x+D ≤ 2*x by omega)
    have h2 := Nat.mul_lt_mul_of_pos_right hK (pow_pos hx 3)
    nlinarith only [h1,h2]
  have hlogm : Real.log m ≤ x := by
    have hh := ht₀ x (by dsimp [T] at hxT; omega)
    change ‖Real.log ((x:ℝ)+1)‖ ≤ 1/8 * ‖(x:ℝ)+1‖ at hh
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (x:ℝ)+1)] at hh
    have h1 := Real.log_le_log (by positivity : (0:ℝ) < m)
      (by exact_mod_cast hhi.le : (m:ℝ) ≤ ((x:ℝ)+1)^4)
    rw [Real.log_pow] at h1; norm_num only [Nat.cast_ofNat] at h1
    linarith [(le_abs_self _).trans hh]
  have hprev : Real.log (m-1:ℕ).factorial ≤ 2*u := by
    exact le_of_lt (lt_of_not_ge (Nat.find_min hex (by omega : m-1 < m)))
  obtain ⟨v,hv,hd,h0,he⟩ := local_net hx hD hsize hlogm u hprev hmu
  refine ⟨v,hv,hd.trans (Nat.factorial_dvd_factorial hmn),h0,?_⟩
  have Hm : (m:ℝ) ≤ 16*(x:ℝ)^4 := by
    have H := Nat.pow_le_pow_left (by omega : x+1 ≤ 2*x) 4
    have H' : (m:ℝ) ≤ (2*(x:ℝ))^4 := by exact_mod_cast hhi.le.trans H
    nlinarith only [H']
  have hu' : 1+u ≤ 257*(x:ℝ)^8 := by
    have H := mul_self_le_mul_self (show (0:ℝ) ≤ m by positivity) Hm
    have Hx := one_le_pow₀ hx' (n := 8)
    nlinarith only [H,log_size m hm,hmu,Hx]
  apply le_trans _ (le_max_right ..)
  calc
    _ ≤ ((D.factorial:ℝ)*x/(x:ℝ)^D) * (257*(x:ℝ)^8)^k :=
      mul_le_mul he (pow_le_pow_left₀ (by linarith) hu' k) (by positivity) (by positivity)
    _ = _ := by dsimp [D]; rw [pow_succ,mul_pow,← pow_mul]; field_simp

end FactorialGaps

open Real

namespace FactorialApproximation

private lemma exp_le_linear {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/2) :
    exp t ≤ 1 + 2*t := by
  apply (Real.exp_bound_div_one_sub_of_interval ht (by linarith)).trans
  apply (div_le_iff₀ (by linarith : 0 < 1-t)).2
  nlinarith [mul_nonneg ht (show 0 ≤ 1-2*t by linarith)]

-- Approximate log(x/k) from just above, using divisors of (k-1)!.
-- The factor k both returns the divisor to k! and leaves room at the midpoint.
private lemma large_case (β : ℝ) (m : ℕ) (hm : β ≤ (m : ℝ)) (C : ℝ)
    (hnet : ∀ n : ℕ, ∀ u : ℝ, 0 ≤ u → 2*u ≤ Real.log n.factorial →
      ∃ v : ℕ, 0 < v ∧ v ∣ n.factorial ∧ 0 ≤ u-Real.log v ∧
        (u-Real.log v)*(1+u)^(m+1) ≤ C)
    (n : ℕ) (hn : 2 ≤ n) (hlog : 8 ≤ Real.log n) (hC : 2*C < (n : ℝ))
    (x : ℝ) (hx : √(n.factorial : ℝ) < x)
    (hx' : x ≤ √((n+1).factorial : ℝ)) :
    ∃ d : ℕ, d ∣ (n+1).factorial ∧ x < (d : ℝ) ∧
      (d : ℝ) ≤ (1 + ((n+1 : ℕ) : ℝ)^(-β)) * x := by
  let s : ℝ := n+1
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 1 ≤ s := by dsimp [s]; linarith
  have hs0 : 0 < s := by linarith
  have hslog : 8 ≤ log s := hlog.trans (Real.log_le_log (by positivity) (by dsimp [s]; linarith))
  have hnlog := Stirling.le_log_factorial_stirling (n := n) (by omega)
  have hpi : 0 ≤ log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hfac : 4*s ≤ log n.factorial := by
    dsimp [s]
    nlinarith [mul_nonneg (show 0 ≤ (n:ℝ) by positivity) (sub_nonneg.mpr hlog)]
  have x0 : 0 < x := (Real.sqrt_nonneg _).trans_lt hx
  have nf : (0:ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have lhs := Real.log_lt_log (Real.sqrt_pos.2 nf) hx
  rw [Real.log_sqrt nf.le] at lhs
  have rhs := Real.log_le_log x0 hx'
  rw [Real.log_sqrt (by positivity), Nat.factorial_succ, Nat.cast_mul,
    Real.log_mul (by positivity) nf.ne'] at rhs
  push_cast at rhs
  change log x ≤ (log s + log (n.factorial : ℝ)) / 2 at rhs
  let t : ℝ := 1 / (2*s^m)
  have hpow : 1 ≤ s^m := one_le_pow₀ hs
  have ht : 0 < t := by dsimp [t]; positivity
  have ht' : t ≤ 1/2 := by dsimp [t]; apply (div_le_iff₀ (by positivity)).2; linarith
  let u := log x - log s + t
  have hu : s ≤ u := by
    dsimp [u]
    linarith [Real.log_le_self hs0.le]
  have hu' : 2*u ≤ log n.factorial := by dsimp [u]; linarith
  obtain ⟨v,hv,hd,hlo,hbound⟩ := hnet n u (by linarith) hu'
  have hdif : u - log v < t := by
    by_contra! h
    have hmle := pow_le_pow_left₀ hs0.le (show s ≤ 1+u by linarith) (m+1)
    have pr := mul_le_mul h hmle (by positivity : 0 ≤ s^(m+1)) hlo
    have idt : t*s^(m+1) = s/2 := by dsimp [t]; rw [pow_succ]; field_simp
    rw [idt] at pr
    dsimp [s] at pr
    linarith
  have hdlog : log (((n+1)*v : ℕ) : ℝ) = log s + log v := by
    rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    push_cast
    rfl
  refine ⟨(n+1)*v, by rw [Nat.factorial_succ]; exact Nat.mul_dvd_mul_left _ hd, ?_, ?_⟩
  · apply (Real.log_lt_log_iff x0 (by positivity)).1
    rw [hdlog]
    dsimp [u] at hdif
    linarith
  · have hex : log s + log v ≤ log x + t := by dsimp [u] at hlo; linarith
    have he := Real.exp_le_exp.mpr (hdlog.trans_le hex)
    rw [Real.exp_log (by positivity), Real.exp_add, Real.exp_log x0] at he
    have small : 2*t ≤ s^(-β) := by
      have vpow := Real.rpow_le_rpow_of_exponent_le hs (show -(m:ℝ) ≤ -β by linarith)
      rw [Real.rpow_neg hs0.le, Real.rpow_natCast] at vpow
      exact le_trans (by dsimp [t]; field_simp; linarith : 2*t ≤ (s^m)⁻¹) vpow
    have hexsmall : exp t ≤ 1+s^(-β) := (exp_le_linear ht.le ht').trans (add_le_add_right small 1)
    change _ ≤ (1+((n+1 : ℕ):ℝ)^(-β))*x
    rw [Nat.cast_add_one]
    change _ ≤ (1+s^(-β))*x
    rw [mul_comm _ x]
    exact he.trans (mul_le_mul_of_nonneg_left hexsmall x0.le)

end FactorialApproximation

open FactorialApproximation

theorem OMA.solution : OMA.R_Erdos1099_erdos_1099_variants_factorial_R1.H1 := by
  intro β hβ
  obtain ⟨m,hm⟩ := exists_nat_gt β
  obtain ⟨C,hC,hnet⟩ := FactorialGaps.centre_bounds (m+1)
  obtain ⟨N,hN⟩ := exists_nat_gt (max (Real.exp 8) (2*C))
  let B : ℝ := (N+1 : ℕ)
  let M : ℝ := 1 + ((N+1).factorial : ℝ)*B^β
  have B0 : 0 < B := by dsimp [B]; positivity
  have hM : 1 ≤ M := by dsimp [M]; linarith [show (0:ℝ) ≤ ((N+1).factorial : ℝ)*B^β by positivity]
  refine ⟨M,by linarith,?_⟩
  intro k hk x hx hx'
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp only [Nat.succ_sub_one] at hx
  have x1 : 1 ≤ x := by
    have h1 := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (n.factorial : ℝ) by exact_mod_cast n.factorial_pos)
    simpa using h1.trans hx.le
  have x0 : 0 < x := by linarith
  have kp : (0 : ℝ) < (n+1 : ℕ) := by positivity
  by_cases hlarge : N ≤ n
  · have hNR : (N : ℝ) ≤ n := by exact_mod_cast hlarge
    have np : 0 < (n:ℝ) := (Real.exp_pos 8).trans_le (((le_max_left ..).trans hN.le).trans hNR)
    have hlog : 8 ≤ Real.log n :=
      (Real.le_log_iff_exp_le np).2
        (((le_max_left ..).trans hN.le).trans hNR)
    have hn : 2 ≤ n := by
      by_contra! h
      interval_cases n <;> norm_num at hlog
    obtain ⟨d,hd,hlo,hhi⟩ := FactorialApproximation.large_case β m hm.le C hnet n hn hlog
      (((le_max_right ..).trans_lt hN).trans_le hNR) x hx hx'
    refine ⟨d,hd,hlo,hhi.trans ?_⟩
    gcongr
    exact le_mul_of_one_le_left (by positivity) hM
  · have hnk : n+1 ≤ N+1 := by omega
    have hfact : (0:ℝ) < (n+1).factorial := by positivity
    have hbig : (1:ℝ) < (n+1).factorial := by exact_mod_cast Nat.one_lt_factorial.mpr hk
    have hlt : x < ((n+1).factorial : ℝ) := hx'.trans_lt (Real.sqrt_lt_self_iff.mpr hbig)
    refine ⟨(n+1).factorial,dvd_rfl,hlt,?_⟩
    have comp : ((n+1 : ℕ) : ℝ)^β ≤ B^β :=
      Real.rpow_le_rpow kp.le (by dsimp [B]; exact_mod_cast hnk) hβ.le
    have hmul : ((n+1).factorial : ℝ) * ((n+1 : ℕ) : ℝ)^β ≤ M := by
      dsimp only [M]
      apply le_trans _ (by linarith : ((N+1).factorial : ℝ)*B^β ≤ _)
      exact mul_le_mul (by exact_mod_cast Nat.factorial_le hnk) comp (by positivity) (by positivity)
    have hbound := (le_div_iff₀ (Real.rpow_pos_of_pos kp β)).2 hmul
    rw [Real.rpow_neg kp.le, ← div_eq_mul_inv]
    exact hbound.trans ((by linarith : M / ((n+1 : ℕ) : ℝ)^β ≤ 1 + M / ((n+1 : ℕ) : ℝ)^β).trans
      (le_mul_of_one_le_right (by positivity) x1))
