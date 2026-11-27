import FormalConjectures.Wikipedia.Mills
import Mathlib

/-!
# From primes in short intervals to the least Mills number

An Ingham-type prime number theorem in intervals of length x^(2/3), applied
at x = n^3, gives the first estimate. The second estimate follows from
Mathlib's Chebyshev.psi_sub_theta_le_mul_sqrt. We remove the higher prime
powers, iterate primes between successive cubes, and construct a Mills
number from nested intervals. To prove leastness, we show that the
infimum also satisfies each individual prime-floor condition.

References: W. H. Mills, A prime-representing function (1947).
A. E. Ingham, On the difference between consecutive primes (1937).
https://doi.org/10.1093/qmath/os-8.1.255
-/

namespace OMA.R_Mills_exists_least_R1

open Set Filter Real Topology Mills

-- A uniform lower bound for the von Mangoldt sum in cubic intervals.
def H1 : Prop := ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    c*(n:ℝ)^2 ≤ Chebyshev.psi ((n:ℝ)^3+(n:ℝ)^2)-Chebyshev.psi ((n:ℝ)^3)

-- A global bound on the contribution of prime powers with exponent at least two.
def H2 : Prop := ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
    Chebyshev.psi x-Chebyshev.theta x ≤ C*sqrt x

-- The floors at the infimum agree individually with floors just to its right.
lemma least_of_exists (existsM : ∃ x > (1:ℝ), IsMills x) : ∃ x, IsMinMills x := by
  let S : Set ℝ := {x | x > 1 ∧ IsMills x}
  have non : S.Nonempty := existsM
  have lower : ∀ x ∈ S, 5/4 ≤ x := by
    intro x hx
    have h := (Nat.prime_iff.mpr (hx.2 (1:ℕ+))).two_le
    have hfloor : 2 ≤ ⌊x^3⌋₊ := by simpa using h
    have hpow : (2:ℝ) ≤ x^3 := by
      simpa using (Nat.le_floor_iff (pow_nonneg (by linarith [hx.1] : 0≤x) 3)).mp hfloor
    by_contra! no
    have upper : x^3 ≤ (5/4:ℝ)^3 := pow_le_pow_left₀ (zero_le_one.trans hx.1.le) no.le 3
    linarith
  have bd : BddBelow S := ⟨5/4, lower⟩
  let b := sInf S
  have hb : 5/4 ≤ b := le_csInf non lower
  have bp : 0 < b := by linarith
  refine ⟨b,⟨⟨by linarith,?_⟩,fun x hx => csInf_le bd hx⟩⟩
  intro n
  let m := 3^(n:ℕ)
  let k := ⌊b^m⌋₊
  have below : b^m < (k:ℝ)+1 := Nat.lt_floor_add_one (b^m)
  have near : {x : ℝ | x^m < (k:ℝ)+1} ∈ 𝓝 b :=
    ((continuous_id.pow m).continuousAt.eventually_lt continuousAt_const below)
  obtain ⟨x,hx,hS⟩ := mem_closure_iff_nhds.mp (csInf_mem_closure non bd) _ near
  have lo : b^m ≤ x^m := pow_le_pow_left₀ bp.le (csInf_le bd hS) m
  have same : ⌊x^m⌋₊ = k := Nat.le_antisymm
    (Nat.lt_succ_iff.mp ((Nat.floor_lt (pow_nonneg (by linarith [hS.1] : (0:ℝ)≤x) m)).mpr (by simpa using hx)))
    (Nat.floor_mono lo)
  change Prime k
  rw [← same]
  exact hS.2 n

lemma exists_of_chain (q : ℕ → ℕ) (pr : ∀ n, (q n).Prime)
    (lo : ∀ n, q n ^ 3 ≤ q (n+1)) (hi : ∀ n, q (n+1)+1 < (q n + 1)^3) :
    ∃ A > (1:ℝ), IsMills A := by
  let d (n : ℕ) := 3^(n+1)
  let l (n : ℕ) := (q n:ℝ)^((d n:ℝ)⁻¹)
  let u (n : ℕ) := ((q n:ℝ)+1)^((d n:ℝ)⁻¹)
  have dpos (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have lpos (n : ℕ) : 0 ≤ l n := rpow_nonneg (by positivity) _
  have upos (n : ℕ) : 0 ≤ u n := rpow_nonneg (by positivity) _
  have lp (n : ℕ) : l n ^ d n = (q n:ℝ) := rpow_inv_natCast_pow (by positivity) (dpos n).ne'
  have up (n : ℕ) : u n ^ d n = (q n:ℝ)+1 := rpow_inv_natCast_pow (by positivity) (dpos n).ne'
  have deq (n : ℕ) : d (n+1) = d n * 3 := by dsimp [d]; rw [pow_succ 3 (n+1)]
  have increasing : Monotone l := monotone_nat_of_le_succ fun n => by
    apply (pow_le_pow_iff_left₀ (lpos n) (lpos (n+1)) (dpos (n+1)).ne').mp
    rw [lp (n+1), deq, pow_mul, lp]
    exact_mod_cast lo n
  have decreasing : StrictAnti u := strictAnti_nat_of_succ_lt fun n => by
    apply (pow_lt_pow_iff_left₀ (upos (n+1)) (upos n) (dpos (n+1)).ne').mp
    rw [up (n+1), deq, pow_mul, up]
    exact_mod_cast hi n
  have sep (n : ℕ) : l n < u n :=
    rpow_lt_rpow (by positivity) (lt_add_one _) (inv_pos.mpr (by exact_mod_cast dpos n))
  have all (m n : ℕ) : l m ≤ u n := by
    rcases le_total m n with h | h
    · exact (increasing h).trans (sep n).le
    · exact (sep m).le.trans (decreasing.antitone h)
  have bounded : BddAbove (Set.range l) := ⟨u 0, by rintro _ ⟨m,rfl⟩; exact all m 0⟩
  let A := sSup (Set.range l)
  have low (n : ℕ) : l n ≤ A := le_csSup bounded ⟨n,rfl⟩
  have high (n : ℕ) : A < u n := (csSup_le (Set.range_nonempty _) (by
    rintro _ ⟨m,rfl⟩
    exact all m (n+1))).trans_lt (decreasing (Nat.lt_succ_self n))
  have first : 1 < l 0 := one_lt_rpow (by exact_mod_cast (pr 0).one_lt) (by
    exact inv_pos.mpr (by exact_mod_cast dpos 0))
  have hA := first.trans_le (low 0)
  refine ⟨A,hA,?_⟩
  intro n
  obtain ⟨j,hj⟩ := n
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  change Prime ⌊A^(d k)⌋₊
  have lw := pow_le_pow_left₀ (lpos k) (low k) (d k)
  have hw := pow_lt_pow_left₀ (high k) (zero_le_one.trans hA.le) (dpos k).ne'
  rw [lp] at lw
  rw [up] at hw
  have val : ⌊A^(d k)⌋₊ = q k := Nat.le_antisymm
    (Nat.lt_succ_iff.mp ((Nat.floor_lt (by positivity)).mpr (by simpa using hw)))
    (Nat.le_floor lw)
  rw [val]
  exact (pr k).prime

open Finset Chebyshev

-- A prime in the first n² integers above n³ leaves room below (n+1)³.
lemma exists_of_prime_intervals
    (h : ∀ᶠ n : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ n^3 < p ∧ p ≤ n^3+n^2) :
    ∃ A > (1:ℝ), IsMills A := by
  classical
  obtain ⟨M,hm⟩ := eventually_atTop.mp h
  let S := {p : ℕ // p.Prime ∧ M ≤ p}
  let step (a : S) := (hm a.val a.prop.2).choose
  have hs (a : S) : (step a).Prime ∧ a.val^3 < step a ∧ step a ≤ a.val^3+a.val^2 :=
    (hm a.val a.prop.2).choose_spec
  let F (a : S) : S := ⟨step a,(hs a).1,a.prop.2.trans
    ((Nat.le_self_pow (by norm_num : 3 ≠ 0) _).trans (hs a).2.1.le)⟩
  obtain ⟨p,hle,hp⟩ := Nat.exists_infinite_primes M
  let start : S := ⟨p,hp,hle⟩
  let a (n : ℕ) := (F^[n]) start
  have nextTerm (n : ℕ) : a (n+1) = F (a n) := Function.iterate_succ_apply' ..
  apply exists_of_chain (fun n => (a n).val) (fun n => (a n).prop.1)
  · intro n
    rw [nextTerm]
    exact (hs _).2.1.le
  · intro n
    rw [nextTerm]
    change step (a n) + 1 < ((a n).val+1)^3
    have hp1 := (a n).prop.1.two_le
    nlinarith [(hs (a n)).2.2]

-- A positive cubic-interval contribution to theta forces a rational prime there.
lemma prime_between_of_theta (l u : ℕ) (lt : theta l < theta u) :
    ∃ p : ℕ, p.Prime ∧ l < p ∧ p ≤ u := by
  classical
  by_contra! bad
  have incl : Nat.primesLE u ⊆ Nat.primesLE l := by
    intro p hp
    obtain ⟨hu,hp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨le_of_not_gt (fun h => (bad p hp h).not_ge hu),hp⟩
  rw [theta_eq_sum_primesLE_log,theta_eq_sum_primesLE_log] at lt
  exact (not_le.mpr lt) (sum_le_sum_of_subset_of_nonneg incl (fun p _ _ => log_natCast_nonneg p))

lemma intervals_of_estimates
    (main : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c*(n:ℝ)^2 ≤ psi ((n:ℝ)^3+(n:ℝ)^2)-psi ((n:ℝ)^3))
    (powers : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, psi x-theta x ≤ C*sqrt x) :
    ∀ᶠ n : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ n^3 < p ∧ p ≤ n^3+n^2 := by
  obtain ⟨c,hc,hm⟩ := main
  obtain ⟨C,hC,hp⟩ := powers
  obtain ⟨M,hM⟩ := exists_nat_gt (2*C^2/c^2)
  filter_upwards [eventually_ge_atTop M,eventually_ge_atTop 1,hm] with n hn h1 hmain
  let x : ℝ := n
  have xp : 0 < x := by dsimp [x]; exact_mod_cast (by omega : 0<n)
  have x1 : 1 ≤ x := by dsimp [x]; exact_mod_cast h1
  have hc2 : 0 < c^2 := by positivity
  have big : 2*C^2 < c^2*x := by
    have lt : 2*C^2/c^2 < x := hM.trans_le (by dsimp [x]; exact_mod_cast hn)
    simpa only [mul_comm] using (div_lt_iff₀ hc2).mp lt
  have t : x^3+x^2 ≤ 2*x^3 := by nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr x1)]
  have sqb : C^2*(x^3+x^2) < (c*x^2)^2 := calc
    _ ≤ C^2*(2*x^3) := mul_le_mul_of_nonneg_left t (sq_nonneg _)
    _ = (2*C^2)*x^3 := by ring
    _ < (c^2*x)*x^3 := mul_lt_mul_of_pos_right big (by positivity)
    _ = _ := by ring
  have root : C*sqrt (x^3+x^2) < c*x^2 := by
    have hsq := Real.sq_sqrt (show 0 ≤ x^3+x^2 by positivity)
    have strict : (C*sqrt (x^3+x^2))^2 < (c*x^2)^2 := by rwa [mul_pow,hsq]
    exact (sq_lt_sq₀ (by positivity) (by positivity)).mp strict
  apply prime_between_of_theta
  push_cast
  linarith [hp (x^3+x^2),theta_le_psi (x^3)]

theorem main : H1 → H2 → type_of% @Mills.exists_least := by
  intro h1 h2
  exact least_of_exists (exists_of_prime_intervals (intervals_of_estimates h1 h2))

end OMA.R_Mills_exists_least_R1
