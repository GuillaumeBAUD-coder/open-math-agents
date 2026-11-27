import FormalConjectures.ErdosProblems.«1099»
/-! Uniform bounds for the divisor-gap sum on factorials. -/
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

lemma gap_control (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ {n a b : ℕ},
    a ∣ n.factorial → b ∣ n.factorial → a < b →
    (∀ v, v ∣ n.factorial → v ≤ a ∨ b ≤ v) →
    (Real.log b-Real.log a)*(1+Real.log a)^k ≤ C ∨
    (Real.log b-Real.log a)*(1+(Real.log n.factorial-Real.log b))^k ≤ C := by
  obtain ⟨C,hC,hnet⟩ := centre_bounds k
  refine ⟨2*C,by positivity,?_⟩
  intro n a b ha hb hab adj
  let A := Real.log a
  let B := Real.log b
  let L := Real.log n.factorial
  have hap := Nat.pos_of_dvd_of_pos ha n.factorial_pos
  have hbp := Nat.pos_of_dvd_of_pos hb n.factorial_pos
  have hAB : A < B := Real.log_lt_log (by positivity) (by exact_mod_cast hab)
  have hA : 0 ≤ A := Real.log_natCast_nonneg _
  have hBL : B ≤ L := Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_of_dvd n.factorial_pos hb)
  let mid := (A+B)/2
  have hmid : A < mid ∧ mid < B := by dsimp [mid]; constructor <;> linarith
  by_cases h : 2*mid ≤ L
  · left
    obtain ⟨v,hv,hd,hlo,he⟩ := hnet n mid (by linarith [hmid.1]) h
    have hVA : Real.log v ≤ A := by
      rcases adj v hd with hi|hi
      · exact Real.log_le_log (by positivity) (by exact_mod_cast hi)
      · have hBV : B ≤ Real.log v := Real.log_le_log (by positivity) (by exact_mod_cast hi)
        linarith [hmid.2]
    have hcmp := mul_le_mul (by linarith : mid-A ≤ mid-Real.log v)
      (pow_le_pow_left₀ (by linarith : 0 ≤ 1+A) (by linarith [hmid.1] : 1+A ≤ 1+mid) k) (by positivity) hlo
    change (B-A)*(1+A)^k ≤ _
    have heq : B-A = 2*(mid-A) := by dsimp [mid]; ring
    rw [heq,mul_assoc]; linarith
  · right
    obtain ⟨v,hv,hd,hlo,he⟩ := hnet n (L-mid) (by linarith [hmid.2]) (by change 2*(L-mid) ≤ L; linarith)
    obtain ⟨w,hw⟩ := hd
    have hw' : w ∣ n.factorial := hw ▸ dvd_mul_left ..
    have hwpos := Nat.pos_of_dvd_of_pos hw' n.factorial_pos
    have hlog : L = Real.log v+Real.log w := by
      dsimp [L]; rw [hw,Nat.cast_mul,Real.log_mul (by positivity) (by positivity)]
    have hV : Real.log v ≤ L-B := by
      rcases adj w hw' with hi|hi
      · have hWA : Real.log w ≤ A := Real.log_le_log (by positivity) (by exact_mod_cast hi)
        linarith [hmid.1]
      · have hBW : B ≤ Real.log w := Real.log_le_log (by positivity) (by exact_mod_cast hi)
        linarith
    have hcmp := mul_le_mul (by linarith : B-mid ≤ (L-mid)-Real.log v)
      (pow_le_pow_left₀ (by linarith : 0 ≤ 1+(L-B)) (by linarith [hmid.2] : 1+(L-B) ≤ 1+(L-mid)) k)
      (by positivity) hlo
    change (B-A)*(1+(L-B))^k ≤ _
    have heq : B-A = 2*(B-mid) := by dsimp [mid]; ring
    rw [heq,mul_assoc]; linarith

noncomputable def pot (t : ℝ) := 1/(1+t)

lemma cost {α C t h : ℝ} {k : ℕ} (hα : 1 < α) (hk : 2 ≤ (k:ℝ)*(α-1)) (hC : 0 < C)
    (ht : 0 ≤ t) (hh : 0 < h) (he : h*(1+t)^k ≤ C) :
    (Real.exp h-1)^α ≤ ((Real.exp C)^α*C^(α-1)*(1+C))*(pot t-pot (t+h)) := by
  have ht1 : 1 ≤ 1+t := by linarith
  have h1p : 0 < 1+t := by linarith
  have hC' : h ≤ C := (le_mul_of_one_le_right hh.le (one_le_pow₀ ht1)).trans he
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ h*(1+t)^k) he (by linarith : 0 ≤ α-1)
  rw [Real.mul_rpow hh.le (by positivity),← Real.rpow_natCast_mul h1p.le] at hpow
  have hpow' := Real.rpow_le_rpow_of_exponent_le ht1 hk
  rw [Real.rpow_two] at hpow'
  have h1 : h^(α-1)*(1+t)^2 ≤ C^(α-1) :=
    (mul_le_mul_of_nonneg_left hpow' (Real.rpow_nonneg hh.le _)).trans hpow
  have h2 : Real.exp h-1 ≤ Real.exp C*h := by
    have he' := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos (Real.exp_pos h)) (Real.exp_pos h).le
    rw [Real.log_exp,mul_sub,mul_one,mul_inv_cancel₀ (Real.exp_ne_zero h)] at he'
    exact he'.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hC') hh.le)
  have h3 := Real.rpow_le_rpow (by linarith [Real.add_one_le_exp h] : 0 ≤ Real.exp h-1) h2 (by linarith : 0 ≤ α)
  rw [Real.mul_rpow (Real.exp_pos _).le hh.le] at h3
  have hexp : h^α = h^(α-1)*h := by rw [← Real.rpow_add_one hh.ne']; congr 1; ring
  rw [hexp] at h3
  have hpot : pot t-pot (t+h) = h/((1+t)*(1+t+h)) := by
    dsimp [pot]; rw [←add_assoc]; field_simp; ring
  rw [hpot]
  apply h3.trans
  have ht2 : 0 < 1+t+h := by linarith
  rw [←mul_div_assoc,le_div_iff₀ (mul_pos h1p ht2)]
  have Hcmp : 1+t+h ≤ (1+t)*(1+C) := by nlinarith only [hC',mul_nonneg ht hC.le]
  have hcom := mul_le_mul_of_nonneg_left Hcmp (show 0 ≤ h^(α-1)*(1+t) by positivity)
  have hprod := mul_le_mul_of_nonneg_right h1 (show 0 ≤ 1+C by positivity)
  have hf := hcom.trans (by nlinarith only [hprod] : h^(α-1)*(1+t)*((1+t)*(1+C)) ≤ C^(α-1)*(1+C))
  nlinarith only [mul_le_mul_of_nonneg_left hf (show 0 ≤ (Real.exp C)^α*h by positivity)]

lemma pot_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : pot y ≤ pot x := by
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

end FactorialGaps
open FactorialGaps

theorem OMA.solution : type_of% @Erdos1099.erdos_1099.variants.factorial := by
  intro α hα
  obtain ⟨k,hk⟩ := exists_nat_gt (2/(α-1))
  have hk' : 2 ≤ (k:ℝ)*(α-1) := ((div_lt_iff₀ (by linarith)).mp hk).le
  obtain ⟨C,hC,hbound⟩ := gap_control k
  let W := (Real.exp C)^α*C^(α-1)*(1+C)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  refine ⟨2*W,fun n => ?_⟩
  let N := n.factorial
  let d := Nat.nth (· ∣ N)
  let l := fun i => Real.log (d i)
  let m := N.divisors.card-1
  let L := Real.log N
  have hN : 0 < N := n.factorial_pos
  have hfin : (Set.ofPred (· ∣ N)).Finite := by
    apply N.divisors.finite_toSet.subset
    intro x hx; exact Nat.mem_divisors.mpr ⟨hx,hN.ne'⟩
  have hset : hfin.toFinset = N.divisors := by ext v; simp [hN.ne']
  have hcard : m < N.divisors.card := by
    have hh := Finset.card_pos.mpr (show N.divisors.Nonempty from ⟨1,Nat.mem_divisors.mpr ⟨one_dvd _,hN.ne'⟩⟩)
    dsimp [m]; omega
  have dvd {i : ℕ} (hi : i ≤ m) : d i ∣ N := Nat.nth_mem_of_lt_card hfin (hset ▸ hi.trans_lt hcard)
  have logBound {i : ℕ} (hi : i ≤ m) : l i ≤ L := Real.log_le_log
    (by exact_mod_cast Nat.pos_of_dvd_of_pos (dvd hi) hN) (by exact_mod_cast Nat.le_of_dvd hN (dvd hi))
  let a := fun i => pot (l i)
  let b := fun i => pot (L-l i)
  have eq {i : ℕ} (hi : i < m) : ((d (i+1):ℝ)/d i-1)^α ≤ W*((a i-a (i+1))+(b (i+1)-b i)) := by
    have h₁ := dvd hi.le
    have h₂ := dvd hi
    have p₁ := Nat.pos_of_dvd_of_pos h₁ hN
    have p₂ := Nat.pos_of_dvd_of_pos h₂ hN
    have hlt : d i < d (i+1) := Nat.nth_lt_nth_of_lt_card hfin (Nat.lt_succ_self i)
      (hset ▸ (show i+1 ≤ m from hi).trans_lt hcard)
    have hloglt : l i < l (i+1) := Real.log_lt_log (by positivity) (by exact_mod_cast hlt)
    have hlog0 : 0 ≤ l i := Real.log_natCast_nonneg _
    have hupper := logBound (i := i+1) hi
    have ha : 0 ≤ a i-a (i+1) := sub_nonneg.mpr (pot_anti hlog0 hloglt.le)
    have hb : 0 ≤ b (i+1)-b i := sub_nonneg.mpr (pot_anti (sub_nonneg.mpr hupper) (by linarith))
    have hex : Real.exp (l (i+1)-l i) = (d (i+1):ℝ)/d i := by
      rw [Real.exp_sub]; dsimp [l]; rw [Real.exp_log (by positivity),Real.exp_log (by positivity)]
    rw [← hex]
    have hdif : 0 < l (i+1)-l i := by linarith
    rcases hbound h₁ h₂ hlt (fun v hv => or_iff_not_imp_right.mpr (fun hh =>
      Nat.le_nth_of_lt_nth_succ (lt_of_not_ge hh) hv)) with H|H
    · have h₃ := cost hα hk' hC hlog0 hdif H
      rw [add_sub_cancel] at h₃
      apply h₃.trans
      exact mul_le_mul_of_nonneg_left (by linarith) hW
    · have h₃ := cost hα hk' hC (sub_nonneg.mpr hupper) hdif H
      rw [show L-l (i+1)+(l (i+1)-l i)=L-l i by ring] at h₃
      apply h₃.trans
      exact mul_le_mul_of_nonneg_left (by linarith) hW
  change (∑ i : Fin m,((d (i.val+1):ℝ)/d i.val-1)^α) ≤ _
  rw [Fin.sum_univ_eq_sum_range (fun i => ((d (i+1):ℝ)/d i-1)^α)]
  apply (sum_le_sum (fun i hi => eq (mem_range.mp hi))).trans
  rw [← mul_sum,sum_add_distrib,sum_range_sub',sum_range_sub]
  have rangeA (i) : 0 ≤ a i ∧ a i ≤ 1 := by
    have hh := Real.log_natCast_nonneg (d i)
    dsimp [a,pot,l]; constructor
    · positivity
    · apply (div_le_iff₀ (by positivity)).mpr; linarith
  have rangeB (i) (hi : i ≤ m) : 0 ≤ b i ∧ b i ≤ 1 := by
    have hh := sub_nonneg.mpr (logBound hi)
    dsimp only [b,pot]; constructor
    · positivity
    · apply (div_le_iff₀ (by positivity)).mpr; linarith
  rw [mul_comm 2 W]
  apply mul_le_mul_of_nonneg_left _ hW
  linarith only [(rangeA 0).2,(rangeA m).1,(rangeB m le_rfl).2,(rangeB 0 (Nat.zero_le m)).1]
