import OMAStatements.S_mse_4190405

/-!
# Asymptotics of the running standard deviation

Vincent Granville posed the recurrence and conjectured its asymptotic behavior
in Math Stack Exchange question 4190405. The statement and its explicit
amplitude are from @Sai-yr's formalization in #7452. Proof and Lean
implementation by @anmolspace with OpenAI Codex.

For N = n+2, normalize the cumulative sum by N times the next standard
deviation. The resulting ratio has a contraction factor at most sqrt(N/(N+1))
and a fixed-point error at most 1/N². Multiplication by sqrt(N+1) shows the
ratio converges to r with error O(1/sqrt N). The logarithmic corrections are
therefore absolutely summable. Their partial sums telescope to the logarithm
of cumulative mass, giving the positive amplitude specified in the statement.
-/

noncomputable section

namespace OMA.RunningSD

open Filter Finset
open scoped Topology BigOperators

/- The normalized update preserves [1,2] and contracts by 1/sqrt(1+t). -/

def denom (t x : ℝ) := Real.sqrt (1+t*(1+(x-1)^2))
def step (t x : ℝ) := (x+t)/denom t x

lemma denom_pos {t : ℝ} (ht : 0 ≤ t) (x : ℝ) : 0 < denom t x := by
  exact Real.sqrt_pos.mpr (by positivity)

lemma denom_sq {t : ℝ} (ht : 0 ≤ t) (x : ℝ) : denom t x ^ 2 = 1+t*(1+(x-1)^2) := by
  exact Real.sq_sqrt (by positivity)

lemma step_mem {t x : ℝ} (ht : 0 ≤ t) (hu : t ≤ 1/2) (hl : 1 ≤ x) (hh : x ≤ 2) :
    1 ≤ step t x ∧ step t x ≤ 2 := by
  have hd := denom_pos ht x
  have hs := denom_sq ht x
  have hx : 0 ≤ x+t := by linarith
  constructor
  · apply (le_div_iff₀ hd).mpr
    rw [one_mul]
    apply (sq_le_sq₀ hd.le hx).mp
    rw [hs]
    have h₁ : 0 ≤ -(x^2)+4*x-2 := by nlinarith [mul_nonneg (show 0≤x-1 by linarith) (show 0≤2-x by linarith)]
    nlinarith [mul_nonneg ht h₁, sq_nonneg t, mul_self_le_mul_self (by norm_num : 0≤(1:ℝ)) hl]
  · apply (div_le_iff₀ hd).mpr
    apply (sq_le_sq₀ hx (by positivity)).mp
    rw [mul_pow, hs]
    have h₂ : 0 ≤ 4+4*(x-1)^2-2*x-t := by nlinarith [sq_nonneg (2*x-5/2)]
    nlinarith [mul_nonneg ht h₂, mul_self_le_mul_self (by linarith : 0≤x) hh]

lemma step_inc {t x y : ℝ} (ht : 0 ≤ t) (hu : t ≤ 1/2)
    (hx : 1 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2) : step t x ≤ step t y := by
  have hdx := denom_pos ht x
  have hdy := denom_pos ht y
  apply (div_le_div_iff₀ hdx hdy).mpr
  apply (sq_le_sq₀ (mul_nonneg (by linarith) hdy.le) (mul_nonneg (by linarith) hdx.le)).mp
  rw [mul_pow, mul_pow, denom_sq ht, denom_sq ht]
  have h : (y+t)*(x-1)+(x+t)*(y-1) ≤ y+x+2*t := by
    nlinarith [mul_nonneg (show 0≤y+t by linarith) (show 0≤2-x by linarith),
      mul_nonneg (show 0≤x+t by linarith) (show 0≤2-y by linarith)]
  have hh : 0 ≤ x+y+2*t-t*((y+t)*(x-1)+(x+t)*(y-1)) := by
    nlinarith [mul_le_mul_of_nonneg_left h ht,
      mul_nonneg (show 0≤1-t by linarith) (show 0≤x+y+2*t by linarith)]
  nlinarith only [mul_nonneg (mul_nonneg (sub_nonneg.mpr hxy) (by linarith : 0≤1+t)) hh]

lemma step_diff_one {t x y : ℝ} (ht : 0 ≤ t) (hu : t ≤ 1/2)
    (hx : 1 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2) :
    |step t y-step t x| ≤ |y-x| / Real.sqrt (1+t) := by
  rw [abs_of_nonneg (sub_nonneg.mpr (step_inc ht hu hx hxy hy)), abs_of_nonneg (sub_nonneg.mpr hxy)]
  have hmono : denom t x ≤ denom t y := by
    apply Real.sqrt_le_sqrt
    have := mul_self_le_mul_self (by linarith : 0≤x-1) (by linarith : x-1 ≤ y-1)
    nlinarith [mul_le_mul_of_nonneg_left this ht]
  have hbase : Real.sqrt (1+t) ≤ denom t y := by
    apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg ht (sq_nonneg (y-1))]
  calc
    _ ≤ (y+t)/denom t y - (x+t)/denom t y := by
      unfold step
      exact sub_le_sub_left (div_le_div_of_nonneg_left (by linarith) (denom_pos ht x) hmono) _
    _ = (y-x)/denom t y := by rw [← sub_div]; ring
    _ ≤ _ := div_le_div_of_nonneg_left (by linarith) (Real.sqrt_pos.mpr (by linarith)) hbase

lemma step_contract {t x y : ℝ} (ht : 0 ≤ t) (hu : t ≤ 1/2)
    (hx : x ∈ Set.Icc 1 2) (hy : y ∈ Set.Icc 1 2) :
    |step t x-step t y| ≤ |x-y| / Real.sqrt (1+t) := by
  rcases le_total x y with h | h
  · rw [abs_sub_comm (step t x), abs_sub_comm x]
    exact step_diff_one ht hu hx.1 h hy.2
  · exact step_diff_one ht hu hy.1 h hx.2

lemma root_error {t r : ℝ} (ht : 0 ≤ t) (hu : t ≤ 1/2) (hr : r ∈ Set.Icc 1 2)
    (hroot : r*(1+(r-1)^2)=2) : |step t r-r| ≤ t^2 := by
  have hd := denom_pos ht r
  have hs := denom_sq ht r
  have hrpos := hr.1
  have hstep := (step_mem ht hu hr.1 hr.2).1
  have hstep_eq : step t r * denom t r = r+t := div_mul_cancel₀ _ hd.ne'
  have hprod : ((step t r)^2-r^2) * (denom t r)^2 = t^2 := by
    calc
      _ = (step t r * denom t r)^2-r^2*(denom t r)^2 := by ring
      _ = _ := by
        rw [hstep_eq, hs]
        linear_combination -r*t*hroot
  have hge : r ≤ step t r := by
    by_contra! h
    have : (step t r)^2 < r^2 := (sq_lt_sq₀ (by linarith) (by linarith)).mpr h
    nlinarith [mul_neg_of_neg_of_pos (sub_neg.mpr this) (sq_pos_of_pos hd), sq_nonneg t]
  rw [abs_of_nonneg (sub_nonneg.mpr hge)]
  have hden : 1 ≤ (denom t r)^2 := by rw [hs]; nlinarith [mul_nonneg ht (sq_nonneg (r-1))]
  have hdiff : step t r-r ≤ (step t r)^2-r^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hge) (show 0≤step t r+r-1 by linarith)]
  have hprodnonneg := mul_nonneg (show 0 ≤ (step t r)^2-r^2 by linarith)
    (show 0 ≤ (denom t r)^2-1 by linarith)
  exact hdiff.trans (by nlinarith)

/- The error after subtracting the linear term of log(1+t) is quadratic. -/

lemma log_remainder {t : ℝ} (ht : 0 ≤ t) : |Real.log (1+t)-t| ≤ t^2 := by
  have ha := Real.log_le_sub_one_of_pos (by linarith : 0 < 1+t)
  have hb := Real.le_log_one_add_of_nonneg ht
  have hlow : t-t^2 ≤ 2*t/(t+2) := by
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg t, mul_nonneg ht (sq_nonneg t)]
  rw [abs_le]
  constructor <;> linarith [sq_nonneg t]

lemma correction_bound {t x r : ℝ} (ht : 0 ≤ t) (hx : 1 ≤ x) (hr : 1 ≤ r) :
    |Real.log (1+t/x) - r⁻¹*Real.log (1+t)| ≤ 2*t^2 + t*|x-r| := by
  have hxp : 0<x := by linarith
  have hrp : 0<r := by linarith
  have htx : t/x ≤ t := (div_le_iff₀ hxp).mpr (by nlinarith [mul_nonneg ht (sub_nonneg.mpr hx)])
  have htx' : 0 ≤ t/x := div_nonneg ht hxp.le
  have ht' := log_remainder htx'
  have ht₀ := log_remainder ht
  have hrinv : r⁻¹ ≤ 1 := (inv_le_one₀ hrp).mpr hr
  have hlead : |t/x - r⁻¹*t| ≤ t * |x-r| := by
    have heq : t/x - r⁻¹*t = (t*(r-x))/(x*r) := by field_simp
    rw [heq, abs_div, abs_mul, abs_of_nonneg ht, abs_of_pos (mul_pos hxp hrp), abs_sub_comm r]
    apply (div_le_iff₀ (mul_pos hxp hrp)).mpr
    have hxr : 1 ≤ x*r := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hr)]
    nlinarith [mul_nonneg (mul_nonneg ht (abs_nonneg (x-r))) (sub_nonneg.mpr hxr)]
  have tail : |r⁻¹*(Real.log (1+t)-t)| ≤ t^2 := by
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hrp.le)]
    calc
      _ ≤ r⁻¹*t^2 := mul_le_mul_of_nonneg_left ht₀ (inv_nonneg.mpr hrp.le)
      _ ≤ 1*t^2 := mul_le_mul_of_nonneg_right hrinv (sq_nonneg t)
      _ = _ := one_mul _
  calc
    _ = |((Real.log (1+t/x)-t/x)+(t/x-r⁻¹*t)) - r⁻¹*(Real.log (1+t)-t)| := by ring_nf
    _ ≤ |(Real.log (1+t/x)-t/x)+(t/x-r⁻¹*t)| + |r⁻¹*(Real.log (1+t)-t)| := abs_sub _ _
    _ ≤ (|Real.log (1+t/x)-t/x| + |t/x-r⁻¹*t|) + |r⁻¹*(Real.log (1+t)-t)| :=
      add_le_add (abs_add_le ..) le_rfl
    _ ≤ _ := by nlinarith [mul_self_le_mul_self htx' htx]

/- Recover the exponent in the question from the defining cubic. -/

def radical : ℝ :=
  let z := (((13+3*Real.sqrt 33)/4 : ℝ) ^ (1/3 : ℝ))
  (2+2/z-z)/3

lemma fixed_root : ∃ r ∈ Set.Ioo (1:ℝ) 2, r*(1+(r-1)^2) = 2 ∧
    let a := 1-r⁻¹
    a ∈ Set.Ioo (0:ℝ) (1/2) ∧ a^2=(1-2*a)*(1-a)^2 ∧ a=radical := by
  let w : ℝ := (13 + 3 * Real.sqrt 33) / 4
  let z : ℝ := w ^ (1/3 : ℝ)
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 33)
  have hs := Real.sqrt_nonneg 33
  have hw : 0 < w := by unfold w; positivity
  have hz : 0 < z := Real.rpow_pos_of_pos hw _
  have hz3 : z^3=w := by
    change (w ^ (1/3:ℝ))^3=w
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]
    norm_num
  have hl : (9/5 : ℝ) < z := by
    by_contra! h
    have := pow_le_pow_left₀ hz.le h 3
    dsimp [w] at hz3
    nlinarith
  have hu : z < 2 := by
    by_contra! h
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h 3
    dsimp [w] at hz3
    nlinarith
  have hwrel : 2*w^2 - 13*w - 16 = 0 := by
    dsimp [w]
    nlinarith
  let a := (2+2/z-z)/3
  have ha0 : 0<a := by dsimp [a]; have := div_pos (by norm_num : (0:ℝ)<2) hz; linarith
  have ha2 : a<1/2 := by
    have hbound : 2/z < 6/5 := (div_lt_iff₀ hz).mpr (by linarith)
    dsimp [a]
    linarith
  have hcubic : a^2=(1-2*a)*(1-a)^2 := by
    dsimp [a]
    field_simp
    rw [← hz3] at hwrel
    linear_combination -hwrel
  let r := 1/(1-a)
  have hden : 0<1-a := by linarith
  have hr1 : 1<r := (lt_div_iff₀ hden).mpr (by linarith)
  have hr2 : r<2 := (div_lt_iff₀ hden).mpr (by linarith)
  have ha : 1-r⁻¹=a := by simp [r]
  refine ⟨r,⟨hr1,hr2⟩,?_,?_⟩
  · dsimp [r]
    field_simp
    linear_combination hcubic
  · rw [ha]
    exact ⟨⟨ha0,ha2⟩,hcubic,rfl⟩

/- Multiplication of the contraction inequality by sqrt(n+2) makes it telescope. -/

def N (n : ℕ) : ℝ := n+2
lemma N_ge (n : ℕ) : 2 ≤ N n := by unfold N; linarith [Nat.cast_nonneg (α := ℝ) n]
lemma N_pos (n : ℕ) : 0 < N n := by linarith [N_ge n]
lemma N_succ (n : ℕ) : N (n+1) = N n+1 := by simp [N]; ring

def major (n : ℕ) : ℝ := 1/(N n * Real.sqrt (N n))

lemma major_summable : Summable major := by
  have hs := (Real.summable_one_div_nat_add_rpow 2 (3/2)).mpr (by norm_num)
  apply hs.congr
  intro n
  change 1/|N n|^(3/2:ℝ) = 1/(N n*Real.sqrt (N n))
  rw [abs_of_pos (N_pos n), show (3/2:ℝ)=1+(1/2) by norm_num, Real.rpow_add (N_pos n),
    Real.rpow_one, Real.sqrt_eq_rpow]

lemma rate {R : ℕ → ℝ} (hzero : R 0 = 1)
    (hstep : ∀ n, R (n+1) = step (N n)⁻¹ (R n)) (r : ℝ)
    (hr : r ∈ Set.Icc 1 2) (hroot : r*(1+(r-1)^2)=2) :
    (∀ n, R n ∈ Set.Icc 1 2) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n, Real.sqrt (N n) * |R n-r| ≤ C := by
  have ht (n : ℕ) : (N n)⁻¹ ∈ Set.Icc 0 (1/2) :=
    ⟨(inv_pos.mpr (N_pos n)).le, by rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) (N_ge n)⟩
  have hR (n : ℕ) : R n ∈ Set.Icc 1 2 := by
    induction n with
    | zero => rw [hzero]; exact ⟨le_rfl,by norm_num⟩
    | succ n ih => rw [hstep]; exact step_mem (ht n).1 (ht n).2 ih.1 ih.2
  refine ⟨hR,?_⟩
  have hsingle (n : ℕ) : Real.sqrt (N (n+1)) * |R (n+1)-r| ≤
      Real.sqrt (N n) * |R n-r| + 2*major n := by
    have hrec : |R (n+1)-r| ≤ |R n-r| / Real.sqrt (1+(N n)⁻¹) + ((N n)⁻¹)^2 := by
      rw [hstep]
      refine (abs_sub_le (step (N n)⁻¹ (R n)) (step (N n)⁻¹ r) r).trans ?_
      exact add_le_add (step_contract (ht n).1 (ht n).2 (hR n) hr) (root_error (ht n).1 (ht n).2 hr hroot)
    have hs := Real.sqrt_nonneg (N n)
    have hn := N_pos n
    have hsn : 0 < Real.sqrt (N n) := Real.sqrt_pos.mpr hn
    have hleft : Real.sqrt (N (n+1)) = Real.sqrt (N n) * Real.sqrt (1+(N n)⁻¹) := by
      rw [← Real.sqrt_mul hn.le, N_succ]; congr 1; field_simp
    have hsr : 0 < Real.sqrt (1+(N n)⁻¹) := Real.sqrt_pos.mpr (by positivity)
    have hdouble : Real.sqrt (N (n+1)) ≤ 2*Real.sqrt (N n) := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rw [Real.sq_sqrt (N_pos _).le, mul_pow, Real.sq_sqrt hn.le, N_succ]
      linarith [N_ge n]
    have hscale : Real.sqrt (N (n+1)) * (|R n-r| / Real.sqrt (1+(N n)⁻¹))
        = Real.sqrt (N n) * |R n-r| := by rw [hleft]; field_simp
    have herr : Real.sqrt (N (n+1)) * ((N n)⁻¹)^2 ≤ 2*major n := by
      calc
        _ ≤ 2*Real.sqrt (N n)*((N n)⁻¹)^2 := mul_le_mul_of_nonneg_right hdouble (sq_nonneg _)
        _ = _ := by unfold major; field_simp; nlinarith [Real.sq_sqrt hn.le]
    have h := mul_le_mul_of_nonneg_left hrec (Real.sqrt_nonneg (N (n+1)))
    rw [mul_add, hscale] at h
    linarith
  have hm n : 0 ≤ major n := by unfold major; exact (one_div_pos.mpr (mul_pos (N_pos n) (Real.sqrt_pos.mpr (N_pos n)))).le
  let c₀ := Real.sqrt (N 0) * |R 0-r|
  have hsum (n : ℕ) : Real.sqrt (N n)*|R n-r| ≤ c₀+2*∑ i ∈ range n, major i := by
    induction n with
    | zero => simp [c₀]
    | succ n ih => rw [sum_range_succ]; linarith [hsingle n]
  refine ⟨c₀+2*∑' i, major i, ?_,?_⟩
  · have hn : 0 ≤ ∑' n, major n := tsum_nonneg hm
    dsimp [c₀]; positivity
  · intro n
    have hh := major_summable.sum_le_tsum (range n) (fun i _ => hm i)
    linarith [hsum n]

/- Recover the ratio dynamics from the cumulative first and second moments. -/

def time (n : ℕ) : ℝ := (n:ℝ)+2
def mass (x : ℕ → ℝ) (n : ℕ) := ∑ j ∈ range (n+2), x j
def energy (x : ℕ → ℝ) (n : ℕ) := ∑ j ∈ range (n+2), (x j)^2

lemma update_square {p s v : ℝ} (hp : 0<p) :
    (p*s^2+(p*v*s)^2/p+s^2)/(p+1) - ((p*v*s+s)/(p+1))^2 =
    (p/(p+1)*s*denom p⁻¹ v)^2 := by
  rw [mul_pow (p/(p+1)*s) (denom p⁻¹ v), denom_sq (inv_pos.mpr hp).le]
  have hp1 : p+1 ≠ 0 := by linarith
  field_simp
  ring

lemma normalized {x R : ℕ → ℝ} (hx0 : 0<x 0) (hR0 : R 0=1)
    (hR : ∀ n, R (n+1) = step (time n)⁻¹ (R n))
    (hx : ∀ n, x (n+1) = Real.sqrt
      ((∑ j ∈ range (n+1), (x j)^2) / ((n:ℝ)+1) -
        ((∑ j ∈ range (n+1), x j) / ((n:ℝ)+1))^2)) :
    ∀ n, 0 < x (n+2) ∧ mass x n = time n*R n*x (n+2) ∧
      energy x n = time n*(x (n+2))^2+(mass x n)^2/time n := by
  have hx1 : x 1=0 := by simpa using hx 0
  have hx2 : x 2=x 0/2 := by
    have h := hx 1
    simp [sum_range_succ,hx1] at h
    convert h using 1
    rw [← Real.sqrt_sq (show 0≤x 0 / 2 by positivity)]
    congr 1
    ring
  intro n
  induction n with
  | zero =>
    simp [mass, energy, time, sum_range_succ, hR0, hx1, hx2]
    constructor
    · positivity
    · constructor <;> ring
  | succ n ih =>
    obtain ⟨hpos,hm,hq⟩ := ih
    let p := time n
    have hp : 0 < p := by dsimp [p,time]; positivity
    have hp1 : 0 < p+1 := by linarith
    have ht : time (n+1)=p+1 := by simp [time,p]; ring
    have hm' : mass x (n+1)=mass x n+x (n+2) := by unfold mass; rw [sum_range_succ]
    have hq' : energy x (n+1)=energy x n+(x (n+2))^2 := by unfold energy; rw [sum_range_succ]
    have hxx : x (n+1+2)=Real.sqrt (energy x (n+1)/(p+1) - (mass x (n+1)/(p+1))^2) := by
      simpa only [mass,energy,p,time,Nat.cast_add,Nat.cast_ofNat] using hx (n+2)
    have halg : energy x (n+1)/(p+1) - (mass x (n+1)/(p+1))^2 =
        (p/(p+1)*x (n+2)*denom p⁻¹ (R n))^2 := by
      rw [hq',hm',hq,hm]
      exact update_square hp
    have hd := denom_pos (inv_pos.mpr hp).le (R n)
    have hw : 0<p/(p+1)*x (n+2)*denom p⁻¹ (R n) := by positivity
    have hnew := hxx.trans (by rw [halg,Real.sqrt_sq hw.le])
    refine ⟨hnew.symm ▸ hw,?_,?_⟩
    · rw [hm',hm,ht,hR,hnew]
      change _ = (p+1)*((R n+p⁻¹)/denom p⁻¹ (R n)) *
        (p/(p+1)*x (n+2)*denom p⁻¹ (R n))
      change p*R n*x (n+2) + x (n+2) = _
      field_simp [hd.ne']
    · have heq : (x (n+1+2))^2=energy x (n+1)/(p+1) - (mass x (n+1)/(p+1))^2 :=
        (congrArg (·^2) hnew).trans halg.symm
      rw [ht,heq]
      field_simp
      ring

/- The ratio error decays as 1/sqrt(n+2), and the logarithmic corrections are summable. -/

theorem analytic {R : ℕ → ℝ} (hzero : R 0 = 1)
    (hstep : ∀ n, R (n+1) = step (N n)⁻¹ (R n)) (r : ℝ)
    (hr : r ∈ Set.Icc 1 2) (hroot : r*(1+(r-1)^2)=2) :
    (∀ n, R n ∈ Set.Icc 1 2) ∧ Tendsto R atTop (𝓝 r) ∧
    Summable (fun n => |Real.log (1+(N n)⁻¹/R n) - r⁻¹*Real.log (1+(N n)⁻¹)|) := by
  obtain ⟨hR,C,hC,hrate⟩ := rate hzero hstep r hr hroot
  refine ⟨hR,?_,?_⟩
  · have ht : Tendsto (fun n : ℕ => N n) atTop atTop := tendsto_natCast_atTop_atTop.atTop_add
      tendsto_const_nhds
    have hlim : Tendsto (fun n => C / Real.sqrt (N n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp ht)
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) ?_ hlim
    intro n
    rw [Real.dist_eq]
    apply (le_div_iff₀ (Real.sqrt_pos.mpr (N_pos n))).mpr
    simpa only [mul_comm] using hrate n
  · apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (f := fun n => (2+C)*major n) ?_
      (major_summable.mul_left (2+C))
    intro n
    have hp := N_pos n
    have hs := Real.sqrt_pos.mpr hp
    have hbound := correction_bound (inv_pos.mpr hp).le (hR n).1 hr.1
    have hss := Real.sq_sqrt hp.le
    have hsle : Real.sqrt (N n) ≤ N n := by
      apply (sq_le_sq₀ hs.le hp.le).mp
      rw [hss]
      nlinarith [mul_nonneg hp.le (show 0≤N n-1 by linarith [N_ge n])]
    have h₁ : (N n)⁻¹^2 ≤ major n := by
      unfold major
      rw [inv_pow, ← one_div]
      apply one_div_le_one_div_of_le (mul_pos hp hs)
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left hsle hp.le
    have h₂ : (N n)⁻¹*|R n-r| ≤ C*major n := by
      unfold major
      rw [mul_one_div]
      apply (le_div_iff₀ (mul_pos hp hs)).mpr
      calc
        _ = Real.sqrt (N n)*|R n-r| := by field_simp
        _ ≤ C := hrate n
    nlinarith

/- Telescoping cumulative mass gives the amplitude exactly. -/

def corr (r : ℝ) (R : ℕ → ℝ) (n : ℕ) :=
  Real.log (1+(N n)⁻¹/R n) - r⁻¹*Real.log (1+(N n)⁻¹)

lemma mass_product (R x : ℕ → ℝ) {r : ℝ} (hx0 : 0<x 0) (hR : ∀ n,0<R n)
    (hm0 : mass x 0=x 0) (hm : ∀ n, mass x n=N n*R n*x (n+2)) :
    ∀ n, mass x n /x 0 = Real.exp (∑ i ∈ range n, corr r R i) * (N n/2)^r⁻¹ := by
  intro n
  induction n with
  | zero => simp [hm0,N,hx0.ne']
  | succ n ih =>
    have hn := N_pos n
    have hs := hR n
    have hfac : mass x (n+1) = mass x n*(1+(N n)⁻¹/R n) := by
      rw [show mass x (n+1) = mass x n+x (n+2) by unfold mass; rw [sum_range_succ]]
      rw [hm n]
      field_simp
    have htime : N (n+1)/2=(N n/2)*(1+(N n)⁻¹) := by rw [N_succ]; field_simp
    have hA : 0<1+(N n)⁻¹/R n := by positivity
    have hB : 0<1+(N n)⁻¹ := by positivity
    have hnew : Real.exp (corr r R n) * (1+(N n)⁻¹)^r⁻¹ = 1+(N n)⁻¹/R n := by
      rw [corr,Real.exp_sub,Real.exp_log hA,Real.rpow_def_of_pos hB,mul_comm r⁻¹]
      exact div_mul_cancel₀ _ (Real.exp_ne_zero _)
    rw [hfac,show mass x n*(1+(N n)⁻¹/R n)/x 0 =
      (mass x n/x 0)*(1+(N n)⁻¹/R n) by ring,ih, sum_range_succ,Real.exp_add,htime,
      Real.mul_rpow (by positivity) hB.le]
    rw [← hnew]
    ring

private lemma cancel_scale {p q h k u v l : ℝ} (hh : h≠0) (hv : v≠0) (hl : l≠0) (pq : p*q=h) :
    (p*k) * (u * (q/l) / (h*v)) = u*k/(v*l) := by
  field_simp
  linear_combination u*k*pq

lemma final_limit (R x : ℕ → ℝ) (r : ℝ) (hr : 1 ≤ r) (hx0 : 0<x 0)
    (hR : ∀ n,0<R n) (hRlim : Tendsto R atTop (𝓝 r))
    (hsum : Summable (fun n => |corr r R n|))
    (hm0 : mass x 0=x 0) (hm : ∀ n, mass x n=N n*R n*x (n+2)) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^(1-r⁻¹)*x n/x 0) atTop
      (𝓝 (Real.exp (∑' n, corr r R n) / (r*(2:ℝ)^r⁻¹))) := by
  let a := 1-r⁻¹
  have hrpos : 0<r := by linarith
  have hsum' : Summable (corr r R) := by
    exact summable_norm_iff.mp (by simpa only [Real.norm_eq_abs] using hsum)
  have hs := hsum'.hasSum.tendsto_sum_nat
  have hN : Tendsto N atTop atTop := tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hinv : Tendsto (fun n => (N n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hN
  have hratio : Tendsto (fun n => (1+(N n)⁻¹)^a) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1:ℝ))).add hinv).rpow_const (Or.inl (by norm_num))
  have hlim := ((Real.continuous_exp.continuousAt.tendsto.comp hs).mul hratio).div
    (hRlim.mul (tendsto_const_nhds (x := (2:ℝ)^r⁻¹))) (mul_ne_zero hrpos.ne' (Real.rpow_pos_of_pos (by norm_num) _).ne')
  apply (tendsto_add_atTop_iff_nat 2).mp
  apply (tendsto_congr' ?_).mpr (by simpa using hlim)
  filter_upwards with n
  have hn := N_pos n
  have hm' := mass_product R x (r := r) hx0 hR hm0 hm n
  rw [hm n] at hm'
  simp only [Nat.cast_add,Nat.cast_ofNat] at *
  change (N n+1)^a*x (n+2)/x 0 = Real.exp (∑ i ∈ range n, corr r R i) * (1+(N n)⁻¹)^a / (R n * 2^r⁻¹)
  have hx : x (n+2)/x 0=Real.exp (∑ i ∈ range n, corr r R i)*(N n/2)^r⁻¹/(N n*R n) := by
    rw [← hm']; field_simp [(hR n).ne']
  rw [mul_div_assoc,hx, Real.div_rpow hn.le (by norm_num)]
  have ha : (N n)^a*(N n)^r⁻¹=N n := by rw [← Real.rpow_add hn]; simp [a]
  have hb : (N n+1)^a=(N n)^a * (1+(N n)⁻¹)^a := by
    rw [← Real.mul_rpow hn.le (by positivity)]
    congr 1; field_simp
  rw [hb]
  exact cancel_scale hn.ne' (hR n).ne' (Real.rpow_pos_of_pos (by norm_num) _).ne' ha

end OMA.RunningSD

open OMA.S_mse_4190405 OMA.RunningSD in
theorem OMA.solution : type_of% @OMA.S_mse_4190405.main := by
  obtain ⟨r,hr,heq,ha,hpoly,hrad⟩ := fixed_root
  have hR0 : ratio 0=1 := rfl
  have hR : ∀ n, ratio (n+1) = step (N n)⁻¹ (ratio n) := fun _ => rfl
  have hr' : r ∈ Set.Icc 1 2 := ⟨hr.1.le,hr.2.le⟩
  obtain ⟨hinterval,hlim,hs⟩ := analytic hR0 hR r hr' heq
  have hpos : 0<r := by linarith [hr.1]
  refine ⟨r,hr,heq,ha,hpoly,hrad,hs,?_,?_⟩
  · unfold amplitude
    positivity
  · intro x h0 hx
    have hsums := normalized h0 hR0 hR hx
    have hx1 : x 1=0 := by simpa using hx 0
    exact final_limit ratio x r hr.1.le h0 (fun n => by linarith [(hinterval n).1])
      hlim hs (by simp [mass, Finset.sum_range_succ, hx1]) (fun n => (hsums n).2.1)
