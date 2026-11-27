import FormalConjectures.ErdosProblems.«627»

/-! # The classical upper bound for the chromatic-to-clique ratio

Use the off-diagonal Ramsey recurrence and the entropy bound on binomial coefficients to
find an independent set in each large induced subgraph. Choosing a cutoff n^r with r just
below 1 makes the final uncolored remainder negligible and yields the constant 4. -/

open SimpleGraph Filter
open scoped Asymptotics

namespace OMA.E627

theorem choose_le_exp_sharp
    (entropy : ∀ a b : ℝ, 0 < a → 0 < b →
      a * Real.log (1 + b / a) + b * Real.log (1 + a / b) ≤
        2 * Real.log 2 * Real.sqrt (a * b)) (s t : ℕ) :
    ((s + t).choose s : ℝ) ≤ Real.exp (2 * Real.log 2 * Real.sqrt ((s : ℝ) * t)) := by
  obtain rfl | hs := Nat.eq_zero_or_pos s
  · simp
  obtain rfl | ht := Nat.eq_zero_or_pos t
  · simp
  let x := (s : ℝ)
  let y := (t : ℝ)
  have hx : 0 < x := Nat.cast_pos.mpr hs
  have hy : 0 < y := Nat.cast_pos.mpr ht
  have hterm : x^s * y^t * ((s+t).choose s : ℝ) ≤ (x+y)^(s+t) := by
    rw [add_pow]
    have h := Finset.single_le_sum
      (f := fun i : ℕ => x^i * y^(s+t-i) * ((s+t).choose i : ℝ))
      (fun i _ => by positivity) (Finset.mem_range.mpr (show s < s+t+1 by omega))
    simpa using h
  have expand (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
      u + v = u * Real.exp (Real.log (1 + v/u)) := by
    rw [Real.exp_log (by positivity)]
    field_simp
  refine le_of_mul_le_mul_left (a := x^s * y^t) ?_ (by positivity)
  calc x^s * y^t * ((s+t).choose s : ℝ) ≤ (x+y)^(s+t) := hterm
       _ = (x+y)^s * (y+x)^t := by rw [pow_add, add_comm y x]
       _ = (x * Real.exp (Real.log (1+y/x)))^s * (y * Real.exp (Real.log (1+x/y)))^t := by
         rw [expand x y hx hy, expand y x hy hx]
       _ = x^s * y^t * (Real.exp (Real.log (1+y/x))^s * Real.exp (Real.log (1+x/y))^t) := by
         rw [mul_pow, mul_pow]; ring
       _ = x^s * y^t * Real.exp (x * Real.log (1+y/x) + y * Real.log (1+x/y)) := by
         rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
       _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (entropy x y hx hy)) (by positivity)

end OMA.E627

namespace Erdos627Upper

open Combinatorics.Diagonal

private theorem ramsey_choose_succ (s t : ℕ) :
    HasRamseyProperty ((s + t).choose s) (s + 1) (t + 1) := by
  induction s generalizing t with
  | zero =>
    rw [Nat.choose_zero_right]
    exact hasRamseyProperty_one_left (t + 1)
  | succ s ihs =>
    induction t with
    | zero =>
      rw [Nat.add_zero, Nat.choose_self]
      exact hasRamseyProperty_one_right (s + 2)
    | succ t iht =>
      have hs : HasRamseyProperty ((s + (t + 1)).choose s) (s + 1) (t + 2) := ihs (t + 1)
      have hpos : 1 ≤ (s + (t + 1)).choose s := Nat.choose_pos (by omega)
      have hp : ((s + 1) + (t + 1)).choose (s + 1) =
          (s + (t + 1)).choose s + ((s + 1) + t).choose (s + 1) := by
        rw [show (s + 1) + (t + 1) = (s + (t + 1)) + 1 by omega, Nat.choose_succ_succ]
        rw [show s + (t + 1) = (s + 1) + t by omega]
      rw [hp]
      intro m c V hV
      exact HasRamseyProperty.step hs iht hpos c V hV

theorem indep_of_choose_le
    {n s t : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hclique : G.cliqueNum ≤ s)
    (hn : (s + t).choose s ≤ S.card) :
    ∃ T ⊆ S, T.card = t + 1 ∧ G.IsIndepSet (T : Set (Fin n)) := by
  classical
  let c (e : Finset (Fin n)) : Bool := decide (¬ G.IsClique (e : Set (Fin n)))
  obtain ⟨T, _, hT, hmono⟩ | ⟨T, hTS, hT, hmono⟩ := ramsey_choose_succ s t c S hn
  · have hTc : G.IsClique (T : Set (Fin n)) := by
      intro x hx y hy hxy
      have h := hmono {x, y} (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
        (by simp [hxy])
      simpa [c, SimpleGraph.isClique_pair, hxy] using h
    have hle := hTc.card_le_cliqueNum
    omega
  · refine ⟨T, hTS, hT, ?_⟩
    intro x hx y hy hxy
    have h := hmono {x, y} (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
      (by simp [hxy])
    simpa [c, SimpleGraph.isClique_pair, hxy] using h

end Erdos627Upper

open SimpleGraph

lemma greedyColor627 {n m t : ℕ} (G : SimpleGraph (Fin n)) (ht : 1 ≤ t)
    (hlarge : ∀ S : Finset (Fin n), m ≤ S.card →
      ∃ T : Finset (Fin n), T ⊆ S ∧ t ≤ T.card ∧ G.IsIndepSet (T : Set (Fin n))) :
    G.chromaticNumber.toNat ≤ n / t + m := by
  classical
  let rec color (S : Finset (Fin n)) :
      (G.induce (S : Set (Fin n))).Colorable (S.card / t + m) := by
    by_cases hS : m ≤ S.card
    · obtain ⟨T, hTS, htT, hI⟩ := hlarge S hS
      let R := S \ T
      have hRT : R.card + T.card = S.card := Finset.card_sdiff_add_card_eq_card hTS
      have hlt : R.card < S.card := by omega
      obtain ⟨c⟩ := color R
      let f (x : (S : Set (Fin n))) : Fin ((R.card / t + m) + 1) :=
        if hx : x.val ∈ T then Fin.last _ else
          (c ⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, hx⟩⟩).castSucc
      have hdiv : R.card / t + 1 ≤ S.card / t := by
        apply (Nat.le_div_iff_mul_le ht).mpr
        rw [Nat.add_mul, Nat.one_mul]
        have := Nat.div_mul_le_self R.card t
        omega
      apply Colorable.mono (show R.card / t + m + 1 ≤ S.card / t + m by omega)
      refine ⟨Coloring.mk f ?_⟩
      intro x y hxy
      have hxy' : G.Adj x.val y.val := hxy
      by_cases hx : x.val ∈ T <;> by_cases hy : y.val ∈ T
      · exact ((hI hx hy hxy'.ne) hxy').elim
      · simp only [f, dif_pos hx, dif_neg hy]
        exact (Fin.castSucc_ne_last _).symm
      · simp [f, hx, hy, Fin.castSucc_ne_last]
      · simp only [f, dif_neg hx, dif_neg hy]
        apply (Fin.castSucc_injective _).ne
        exact c.valid (show (G.induce (R : Set (Fin n))).Adj
          ⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, hx⟩⟩
          ⟨y.val, Finset.mem_sdiff.mpr ⟨y.property, hy⟩⟩ from hxy')
    · apply Colorable.mono _ (G.induce (S : Set (Fin n))).colorable_of_fintype
      simpa using (Nat.le_of_lt (Nat.lt_of_not_ge hS)).trans (Nat.le_add_left m (S.card / t))
  termination_by S.card
  let U : Finset (Fin n) := Finset.univ
  let inclusion : G →g G.induce (U : Set (Fin n)) :=
    { toFun := fun x => ⟨x, Finset.mem_univ x⟩, map_rel' := fun h => h }
  have h := (color U).of_hom inclusion
  apply ENat.toNat_le_of_le_natCast
  simpa [U] using h.chromaticNumber_le

open SimpleGraph Filter
open scoped Asymptotics

namespace Erdos627Sharp

lemma sharp_ratio {n w colors : ℕ} (hn : 2 ≤ n) (hw : 0 < w)
    {r η : ℝ} (hr : 0 < r)
    (htail : (⌈(n : ℝ) ^ r⌉₊ : ℝ) ≤ η * ((n : ℝ) / (Real.logb 2 n)^2))
    (hc : ∀ t m : ℕ, Real.exp (2 * Real.log 2 * Real.sqrt ((w : ℝ) * t)) ≤ m →
      colors ≤ n / (t + 1) + m) :
    (colors : ℝ) / w ≤ (4 / r^2 + η) * ((n : ℝ) / (Real.logb 2 n)^2) := by
  let L := Real.logb 2 n
  let u := (r * L)^2 / (4 * w)
  let t := ⌊u⌋₊
  let m := ⌈(n : ℝ) ^ r⌉₊
  have hn' : 1 < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hn0 : 0 < (n : ℝ) := by positivity
  have hb := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have hL : 0 < L := div_pos (Real.log_pos hn') hb
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hwt : (w : ℝ) * t ≤ (r * L)^2 / 4 := by
    have h := (le_div_iff₀ (show 0 < 4 * (w : ℝ) by positivity)).mp (Nat.floor_le hu)
    dsimp [t, u] at *
    linarith only [h]
  have hroot : Real.sqrt ((w : ℝ)*t) ≤ r*L/2 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith only [hwt]⟩
  have hscale : Real.log 2 * L = Real.log n := by
    dsimp [L, Real.logb]
    field_simp
  have hm : Real.exp (2 * Real.log 2 * Real.sqrt ((w : ℝ) * t)) ≤ m := calc
    _ ≤ Real.exp (2 * Real.log 2 * (r*L/2)) := by gcongr
    _ = (n : ℝ)^r := by
      rw [Real.rpow_def_of_pos hn0, ← hscale]
      congr 1
      ring
    _ ≤ _ := Nat.le_ceil _
  have hcap := hc t m hm
  have hcolor : (colors : ℝ) ≤ (n : ℝ) / (t + 1) + m := calc
    _ ≤ ((n / (t + 1) + m : ℕ) : ℝ) := by exact_mod_cast hcap
    _ ≤ _ := by push_cast; gcongr; exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := n) (n := t+1))
  have hunit : (r*L)^2 / 4 ≤ ((t : ℝ)+1)*w := by
    have h := (div_lt_iff₀ (show 0 < (4 : ℝ)*w by positivity)).mp (Nat.lt_floor_add_one u)
    dsimp [t,u] at *
    linarith only [h]
  have hmain : ((n : ℝ) / ((t : ℝ)+1)) / w ≤ (4/r^2)*((n : ℝ)/L^2) := calc
    _ = (n : ℝ) / (((t : ℝ)+1)*w) := div_div _ _ _
    _ ≤ (n : ℝ) / ((r*L)^2 / 4) := div_le_div_of_nonneg_left hn0.le (by positivity) hunit
    _ = _ := by field_simp
  have hmdiv : (m : ℝ) / w ≤ η * ((n : ℝ)/L^2) :=
    (div_le_self (Nat.cast_nonneg _) hw1).trans htail
  calc
    (colors : ℝ)/w ≤ ((n : ℝ) / ((t : ℝ)+1) + m)/w := by gcongr
    _ ≤ _ := by rw [add_div, add_mul]; exact add_le_add hmain hmdiv

end Erdos627Sharp

open Filter

lemma eventually_ceil_rpow_le_627 {η r : ℝ} (hη : 0 < η) (hr : 0 < r) (hr1 : r < 1) :
    ∀ᶠ n : ℕ in atTop, (⌈(n : ℝ) ^ r⌉₊ : ℝ) ≤ η * ((n : ℝ) / Real.logb 2 n ^ 2) := by
  have hb : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hO := (isLittleO_log_rpow_rpow_atTop 2 (sub_pos.mpr hr1)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := hO.bound (show 0 < η * Real.log 2 ^ 2 / 2 by positivity)
  filter_upwards [h, eventually_ge_atTop 2] with n hn hn2
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hnp := zero_lt_one.trans hn1
  have hlp := Real.log_pos hn1
  change ‖Real.log (n : ℝ) ^ (2 : ℝ)‖ ≤ η * Real.log 2 ^ 2 / 2 * ‖(n : ℝ) ^ (1 - r)‖ at hn
  rw [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnp.le _)] at hn
  have hc : (⌈(n : ℝ)^r⌉₊ : ℝ) ≤ 2 * (n : ℝ)^r := by
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hnp.le r)
    have := Real.one_le_rpow hn1.le hr.le
    linarith
  have hratio : Real.logb 2 n ^ 2 ≤ (η / 2) * (n : ℝ) ^ (1-r) := by
    rw [Real.logb, div_pow, div_le_iff₀ (sq_pos_of_pos hb)]
    linarith
  rw [← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos (Real.logb_pos (by norm_num) hn1))]
  calc
    _ ≤ (2 * (n : ℝ)^r) * ((η / 2) * (n : ℝ)^(1-r)) :=
      mul_le_mul hc hratio (sq_nonneg _) (by positivity)
    _ = η * ((n : ℝ)^r * (n : ℝ)^(1-r)) := by ring
    _ = η * n := by rw [← Real.rpow_add hnp, show r+(1-r) = 1 by ring, Real.rpow_one]

lemma cutoffExponent627 {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ 4 / r^2 + ε / 2 ≤ 4 + ε := by
  let q := 4 / (4 + ε/2)
  have hd : 0 < 4 + ε/2 := by positivity
  have hq : 0 < q := div_pos (by norm_num) hd
  have hq1 : q < 1 := (div_lt_one hd).mpr (by linarith)
  refine ⟨Real.sqrt q, Real.sqrt_pos.mpr hq, ?_, ?_⟩
  · nlinarith [Real.sq_sqrt hq.le, Real.sqrt_nonneg q]
  · rw [Real.sq_sqrt hq.le]
    dsimp [q]
    rw [div_div_eq_mul_div]
    linarith

namespace Erdos627Upper

open Real Set

private noncomputable def imbalance (x : ℝ) := log (1+x) - x * log (1+1/x)
private noncomputable def entropyRatio (x : ℝ) := (log (1+x) + x * log (1+1/x)) / sqrt x

private theorem logTerms {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => log (1+y)) (1/(1+x)) x ∧
    HasDerivAt (fun y : ℝ => y * log (1+1/y)) (log (1+1/x) - 1/(1+x)) x := by
  have hi := hasDerivAt_id x
  have hc := hasDerivAt_const x (1 : ℝ)
  have h1 := (hc.fun_add hi).log (show (1:ℝ) + x ≠ 0 by positivity)
  have h2 := (hc.fun_add (hc.fun_div hi hx.ne')).log (show (1:ℝ) + 1/x ≠ 0 by positivity)
  constructor
  · simpa using h1
  · apply (hi.fun_mul h2).congr_deriv
    simp only [id, zero_mul, one_mul, zero_sub, zero_add, mul_one]
    field_simp
    ring

private theorem imbalance_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ imbalance x := by
  have hd {y : ℝ} (hy : 0 < y) :
      HasDerivAt imbalance (2/(1+y) - log (1+1/y)) y := by
    obtain ⟨h1,h2⟩ := logTerms hy
    apply (h1.fun_sub h2).congr_deriv
    ring
  have hmono : MonotoneOn imbalance (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact fun y hy => (hd (lt_of_lt_of_le zero_lt_one hy)).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd (lt_of_lt_of_le zero_lt_one (interior_subset hy))).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy1 : 1 ≤ y := interior_subset hy
      have hy0 : 0 < y := by linarith
      rw [(hd hy0).deriv]
      have hlog := log_le_sub_one_of_pos (show 0 < (1:ℝ)+1/y by positivity)
      have hs : 1/y ≤ 2/(1+y) := (div_le_div_iff₀ hy0 (by positivity)).mpr (by linarith)
      linarith
  have h := hmono (show (1:ℝ) ∈ Ici 1 by simp) hx hx
  simpa [imbalance] using h

private theorem entropyRatio_le {x : ℝ} (hx : 1 ≤ x) : entropyRatio x ≤ 2 * log 2 := by
  have hd {y : ℝ} (hy : 0 < y) :
      HasDerivAt entropyRatio (-imbalance y / (2 * sqrt y * y)) y := by
    have hs := sqrt_pos.2 hy
    obtain ⟨h1,h2⟩ := logTerms hy
    have hnum : HasDerivAt (fun z : ℝ => log (1+z) + z * log (1+1/z)) (log (1+1/y)) y := by
      apply (h1.fun_add h2).congr_deriv
      ring
    apply (hnum.fun_div (hasDerivAt_sqrt hy.ne') hs.ne').congr_deriv
    unfold imbalance
    field_simp
    rw [sq_sqrt hy.le]
    ring
  have hanti : AntitoneOn entropyRatio (Ici 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact fun y hy => (hd (lt_of_lt_of_le zero_lt_one hy)).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd (lt_of_lt_of_le zero_lt_one (interior_subset hy))).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy1 : 1 ≤ y := interior_subset hy
      rw [(hd (lt_of_lt_of_le zero_lt_one hy1)).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (imbalance_nonneg hy1)) (by positivity)
  have h := hanti (show (1:ℝ) ∈ Ici 1 by simp) hx hx
  simpa [entropyRatio, two_mul, show (1:ℝ)+1=2 by norm_num] using h

private theorem entropy_le_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a * log (1+b/a) + b * log (1+a/b) ≤ 2 * log 2 * sqrt (a*b) := by
  have hb := ha.trans_le hab
  have h := entropyRatio_le (x := b/a) ((one_le_div ha).mpr hab)
  unfold entropyRatio at h
  rw [show 1/(b/a) = a/b by field_simp] at h
  have hm := mul_le_mul_of_nonneg_left ((div_le_iff₀ (sqrt_pos.mpr (div_pos hb ha))).mp h) ha.le
  have hs : a * sqrt (b/a) = sqrt (a*b) := by
    calc
      _ = sqrt (a^2) * sqrt (b/a) := by rw [sqrt_sq ha.le]
      _ = _ := by rw [← sqrt_mul (sq_nonneg a)]; congr 1; field_simp
  calc
    _ = a * (log (1+b/a) + (b/a) * log (1+a/b)) := by field_simp
    _ ≤ a * (2 * log 2 * sqrt (b/a)) := hm
    _ = _ := by rw [← hs]; ring

theorem binary_entropy_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * Real.log (1+b/a) + b * Real.log (1+a/b) ≤
      2 * Real.log 2 * Real.sqrt (a*b) := by
  rcases le_total a b with hab | hba
  · exact entropy_le_of_le ha hab
  · simpa only [mul_comm b a, add_comm (b * _) (a * _)] using entropy_le_of_le hb hba

end Erdos627Upper

private lemma upper_of_entropy
    (entropy : ∀ a b : ℝ, 0 < a → 0 < b →
      a * Real.log (1 + b/a) + b * Real.log (1 + a/b) ≤
        2 * Real.log 2 * Real.sqrt (a*b)) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Erdos627.maxChromaticCliqueRatio n ≤ (4 + ε) * ((n : ℝ) / Real.logb 2 n ^ 2) := by
  classical
  intro ε hε
  obtain ⟨r, hr, hr1, hcoeff⟩ := cutoffExponent627 hε
  have heta : 0 < ε/2 := half_pos hε
  filter_upwards [eventually_ge_atTop 2, eventually_ceil_rpow_le_627 heta hr hr1] with n hn hTail
  apply ciSup_le
  intro G
  have hw : 0 < G.cliqueNum := by
    let v : Fin n := ⟨0, by omega⟩
    have hv : G.IsClique (({v} : Finset (Fin n)) : Set (Fin n)) := by simp
    change 1 ≤ G.cliqueNum
    simpa using hv.card_le_cliqueNum
  apply le_trans (Erdos627Sharp.sharp_ratio hn hw hr hTail ?_)
    (mul_le_mul_of_nonneg_right hcoeff (by positivity))
  intro t m hm
  apply greedyColor627 G (by omega : 1 ≤ t + 1)
  intro S hs
  have hb := OMA.E627.choose_le_exp_sharp entropy G.cliqueNum t
  have hs' : (m : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hs
  have hsize : (G.cliqueNum + t).choose G.cliqueNum ≤ S.card := by
    exact_mod_cast hb.trans (hm.trans hs')
  obtain ⟨I, hI, hcard, hind⟩ := Erdos627Upper.indep_of_choose_le G S le_rfl hsize
  exact ⟨I, hI, hcard.ge, hind⟩

theorem OMA.solution : type_of% @Erdos627.erdos_627.variants.upper :=
  upper_of_entropy fun _ _ ha hb => Erdos627Upper.binary_entropy_le ha hb
