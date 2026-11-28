import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R2
import Mathlib

-- Credit: @camronh
/-!
# A scored-patch reduction of the five-term square-root-budget step

PianothShaveck's PR 36506 asks for a halving of the logarithmic density
parameter on one progression. Here the source only has to pay for a smaller
gain at each stage. A step costing one plus the log of the dimension earns
that charge times the square root of the current parameter in log density.
The proof composes the actual one-based progression sections, carries their
five-term freeness through every restriction, and telescopes the square-root
potential until the original parameter is halved.

H1 is the inverse or amplification problem with no log-log size cutoff.
Its log-resource allowance grows only as the cube root of the parameter. H2 is a set-independent positive approximation in total absolute error
for triangular polynomial patches. Selection permits overlapping pieces. The
entire weighted-degree-one, one-slot case of H2 is proved with constant six, for arbitrary real
slope and offset. The rational-polynomial case is exact if its denominator
permits sufficiently long residue classes. A further theorem constructs a
zero-slot witness for H1 throughout the cube-root small-scale regime.

The patch coordinates and score normalization follow OpenAI's arithmetic
progressions manuscript and ScoredPatchDensityStep.lean at openai/math,
3344da59991ed94f9ba711217b29c1d760badfa6, as unpacked in YevhenDiachenko0's
PR 36701. Its set-dependent scored-step theorem is distinct from H2's
uniform L1 approximation. Its source gives a smaller gain than H1 requires.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R2_H1_R1
open Finset Real
open scoped Classical

/-- A five-term-progression-free input has a signed score on a long slice.
The gain is proportional on the log scale to the square root of the current
log-density times the dimension charge. Its log-resource allowance grows only
as the cube root, and the source has no ambient log-log cutoff. -/
def H1 : Prop :=
  ∃ (s : ℕ) (B T : ℝ), 0 ≤ B ∧ ∀ (N : ℕ) (S : Finset ℕ),
    2 ≤ N → S ⊆ Icc 1 N → 0 < S.card →
    (¬ ∃ a e : ℕ, 0 < e ∧ ∀ i < 5, a+i*e ∈ S) →
    let p := max 2 (log (2*(N:ℝ)/S.card))
    T < p →
    ∃ (d M a q : ℕ) (U : ℝ) (w : Fin d → ℕ)
      (P : (i : Fin d) → MvPolynomial (Unit ⊕ Fin i.val) ℝ)
      (Φ : (Fin d → ℝ) → ℝ) (L' : NNReal),
      (∀ i, 1 ≤ w i ∧ w i ≤ s) ∧ Monotone w ∧
      (∀ i, P i ∈ MvPolynomial.restrictSupport ℝ
        {m | Finsupp.weight (Sum.elim (fun _ : Unit ↦ (1 : ℕ))
          (fun j : Fin i.val ↦ w ⟨j.val, lt_trans j.isLt i.isLt⟩)) m ≤ w i}) ∧
      (∀ x, 0 ≤ Φ x ∧ Φ x ≤ 1) ∧ (∀ x, Φ x ≠ 0 → ∀ i, |x i| ≤ 1/4) ∧
      LipschitzWith L' Φ ∧ 0 < q ∧ (∀ n < M, a+q*n ∈ Icc 1 N) ∧
      1 ≤ U ∧ log (N:ℝ)-U ≤ log M ∧ (L':ℝ)+1 ≤ exp U ∧
      let R := log ((d:ℝ)+1)
      let δ := (1+R)*sqrt p
      ((2*s*s+1 : ℕ):ℝ)*R + log U ≤ B*p^(1/3:ℝ) ∧ 2 ≤ p-δ ∧
      exp (-U) ≤ (∑ n ∈ range M,
        ((if a+q*n ∈ S then (1:ℝ) else 0)-exp δ*((S.card:ℝ)/N)) *
          ∑' z : Fin d → ℤ, Φ (fun i ↦ (z i:ℝ) - MvPolynomial.aeval
            (Sum.elim (fun _ : Unit ↦ (n:ℝ))
              (fun j : Fin i.val ↦ (z ⟨j.val, lt_trans j.isLt i.isLt⟩:ℝ))) (P i))) / (M:ℝ)

/-- Approximate the patch on the original parameter interval in total absolute
error by a positive combination of long progression indicators. -/
def H2 : Prop :=
  ∀ s : ℕ, ∃ L₀ : ℝ, ∀ (N M d : ℕ) (U R V : ℝ)
    (w : Fin d → ℕ) (P : (i : Fin d) → MvPolynomial (Unit ⊕ Fin i.val) ℝ)
    (Φ : (Fin d → ℝ) → ℝ) (L : NNReal),
    (∀ i, 1 ≤ w i ∧ w i ≤ s) → Monotone w →
    (∀ i, P i ∈ MvPolynomial.restrictSupport ℝ
      {m | Finsupp.weight (Sum.elim (fun _ : Unit ↦ (1 : ℕ))
        (fun j : Fin i.val ↦ w ⟨j.val, lt_trans j.isLt i.isLt⟩)) m ≤ w i}) →
    (∀ x, 0 ≤ Φ x ∧ Φ x ≤ 1) → (∀ x, Φ x ≠ 0 → ∀ i, |x i| ≤ 1 / 4) →
    LipschitzWith L Φ → 2 ≤ N → 0 < M → 1 ≤ U →
    log (N : ℝ) - U ≤ log (M : ℝ) → (L : ℝ) + 1 ≤ exp U →
    log ((d : ℝ) + 1) ≤ R → log U ≤ V →
    L₀ + ((2*s*s+1 : ℕ) : ℝ)*R + V ≤ log (log N) →
    let W := fun n : ℕ => ∑' z : Fin d → ℤ, Φ (fun i ↦ (z i : ℝ) - MvPolynomial.aeval
      (Sum.elim (fun _ : Unit ↦ (n : ℝ))
        (fun j : Fin i.val ↦ (z ⟨j.val, lt_trans j.isLt i.isLt⟩ : ℝ))) (P i))
    ∃ (J : ℕ) (T : Fin J → Finset ℕ) (v : Fin J → ℝ),
      (∀ i, 0 ≤ v i) ∧ (∀ i, ∃ t q m : ℕ, 0 < q ∧ 2 ≤ m ∧ T i ⊆ range M ∧
        T i = (Icc 1 m).image (fun n => t + (n-1)*q) ∧
        log (log N) - (L₀ + ((2*s*s : ℕ) : ℝ)*R) ≤ log (log m)) ∧
      ∑ n ∈ range M, |W n - ∑ i, if n ∈ T i then v i else 0| < (M : ℝ)*exp (-U)

/-- Find a dense piece from a nonnegative finite approximation to a test. -/
theorem select_piece {J : ℕ} (U : Finset ℕ) (f W : ℕ → ℝ)
    (pieces : Fin J → Finset ℕ) (w : Fin J → ℝ) (b τ : ℝ)
    (hf : ∀ x ∈ U, f x ∈ Set.Icc 0 1) (hW : ∀ x ∈ U, 0 ≤ W x)
    (hin : ∀ i, pieces i ⊆ U) (hw : ∀ i, 0 ≤ w i)
    (hb : 0 ≤ b) (hτ : 0 < τ)
    (hscore : τ ≤ ∑ x ∈ U, (f x - b) * W x)
    (herr : ∑ x ∈ U, |W x - ∑ i, if x ∈ pieces i then w i else 0| < τ) :
    ∃ i, b * (pieces i).card < ∑ x ∈ pieces i, f x := by
  classical
  let V (x : ℕ) := ∑ i, if x ∈ pieces i then w i else 0
  have hb1 : b < 1 := by
    by_contra! h
    have hneg : ∑ x ∈ U, (f x-b)*W x ≤ 0 := sum_nonpos fun x hx =>
      mul_nonpos_of_nonpos_of_nonneg (by linarith [(hf x hx).2]) (hW x hx)
    linarith
  have point (x : ℕ) (hx : x ∈ U) :
      (f x - b) * W x ≤ (f x - b) * V x + |W x - V x| := by
    have hfb : |f x-b| ≤ 1 := abs_le.mpr ⟨by linarith [(hf x hx).1], by linarith [(hf x hx).2]⟩
    have h := (le_abs_self ((f x-b)*(W x-V x))).trans
      ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right hfb (abs_nonneg _)))
    linarith
  have hcomp := sum_le_sum point
  rw [sum_add_distrib] at hcomp
  change (∑ x ∈ U, |W x - V x|) < τ at herr
  have hV : 0 < ∑ x ∈ U, (f x-b)*V x := by linarith
  have swap : (∑ x ∈ U, (f x-b)*V x) =
      ∑ i, w i * ((∑ x ∈ pieces i, f x) - b * (pieces i).card) := by
    dsimp only [V]
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl (fun i _ => ?_)
    calc
      _ = ∑ x ∈ U, if x ∈ pieces i then w i * (f x-b) else 0 := by
        refine sum_congr rfl (fun x _ => ?_)
        by_cases hx : x ∈ pieces i <;> simp [hx, mul_comm]
      _ = ∑ x ∈ pieces i, w i * (f x-b) := by
        rw [← sum_filter]
        congr 1
        ext x
        exact mem_filter.trans ⟨fun h => h.2, fun h => ⟨hin i h, h⟩⟩
      _ = _ := by rw [← mul_sum, sum_sub_distrib]; simp [mul_comm]
  rw [swap] at hV
  by_contra! h
  exact hV.not_ge (sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hw i) (sub_nonpos.mpr (h i)))

/-- The integer lift changes by an exact integer after a period. The equality
of the two sums follows by translation of the lift, also for a composite q. -/
theorem rational_patch_periodic (P : Polynomial ℤ) (q : ℕ) (hq : 0 < q) (Φ : ℝ → ℝ) :
    Function.Periodic (fun n : ℕ => ∑' z : ℤ, Φ ((z : ℝ) - ((P.eval (n : ℤ) : ℤ) : ℝ) / q)) q := by
  intro n
  have hd := Polynomial.sub_dvd_eval_sub ((n : ℤ) + q) (n : ℤ) P
  rw [add_sub_cancel_left] at hd
  obtain ⟨t, ht⟩ := hd
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have he : ((P.eval ((n : ℤ) + q) : ℤ) : ℝ) = ((P.eval (n : ℤ) : ℤ) : ℝ) + (q : ℝ)*t := by
    exact_mod_cast (show P.eval ((n : ℤ) + q) = P.eval (n : ℤ) + (q : ℤ)*t by linarith)
  push_cast
  rw [he]
  have shift := (Equiv.addRight (-t)).tsum_eq
    (fun z : ℤ => Φ ((z : ℝ) - ((P.eval (n : ℤ) : ℤ) : ℝ)/q))
  rw [← shift]
  refine tsum_congr (fun z => congrArg Φ ?_)
  change (z : ℝ) - _ = ((z + -t : ℤ) : ℝ) - _
  push_cast
  field_simp
  ring

/-- A periodic nonnegative test is exactly a positive combination of
progression indicators, each of length at least L, whenever L*q ≤ M.
This holds for nonmultiples of q and needs no averaging over the origin. -/
theorem periodic_progression_mixture (W : ℕ → ℝ) {M q L : ℕ}
    (hq : 0 < q) (hL : 0 < L) (hfit : L*q ≤ M)
    (hper : Function.Periodic W q) (hnonneg : ∀ n, 0 ≤ W n) :
    ∃ (pieces : Fin q → Finset ℕ) (v : Fin q → ℝ),
      (∀ i, 0 ≤ v i) ∧ (∀ i, ∃ m : ℕ, L ≤ m ∧ pieces i ⊆ range M ∧
        pieces i = (Icc 1 m).image (fun n => i.val + (n-1)*q)) ∧
      ∀ n ∈ range M, W n = ∑ i, if n ∈ pieces i then v i else 0 := by
  classical
  let pieces (i : Fin q) := (range M).filter (fun n => n % q = i.val)
  have hqM : q ≤ M := (Nat.le_mul_of_pos_left q hL).trans hfit
  refine ⟨pieces, fun i => W i.val, fun i => hnonneg _, ?_, ?_⟩
  · intro i
    have hi : i.val < M := i.isLt.trans_le hqM
    let m := (M-1-i.val)/q + 1
    have eqv (j : ℕ) : j < m ↔ i.val + j*q < M := by
      dsimp [m]
      rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hq]
      omega
    have hlen : L ≤ m := by
      have hmul : (L-1)*q + q = L*q := by
        rw [← Nat.succ_mul, show (L-1).succ = L by omega]
      have hlast : i.val + (L-1)*q < M := by have := i.isLt; omega
      have := (eqv (L-1)).mpr hlast
      omega
    refine ⟨m, hlen, filter_subset _ _, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨hxm, hr⟩ := mem_filter.mp hx
      have hrepr : i.val + (x/q)*q = x := by
        rw [← hr, Nat.mul_comm]; exact Nat.mod_add_div _ _
      have hxlen := (eqv (x/q)).mpr (by rw [hrepr]; exact mem_range.mp hxm)
      exact mem_image.mpr ⟨x/q+1, mem_Icc.mpr ⟨Nat.succ_le_succ (Nat.zero_le _), hxlen⟩, by simpa using hrepr⟩
    · intro hx
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
      obtain ⟨hj1,hjm⟩ := mem_Icc.mp hj
      exact mem_filter.mpr ⟨mem_range.mpr ((eqv (j-1)).mp (by omega)), by simp [Nat.mod_eq_of_lt i.isLt]⟩
  · intro n hn
    let r : Fin q := ⟨n % q, Nat.mod_lt _ hq⟩
    have periodic (t : ℕ) : W (r.val + t*q) = W r.val := by
      induction t with
      | zero => simp
      | succ t ih => rw [Nat.succ_mul, ← Nat.add_assoc, hper, ih]
    have hrepr : r.val + (n/q)*q = n := by rw [Nat.mul_comm]; exact Nat.mod_add_div _ _
    have hW : W n = W r.val := hrepr ▸ periodic (n/q)
    rw [sum_eq_single r]
    · simp [pieces, hn, r, hW]
    · intro i _ hir
      have hne : n % q ≠ i.val := fun h => hir (Fin.ext h.symm)
      simp [pieces, hne]
    · simp


/-- For a rational one-slot polynomial phase the geometric approximation is
exact as soon as the chosen period admits progressions of the required length.
The denominator can be composite and M need not be a multiple of it. -/
theorem rational_case (P : Polynomial ℤ) (q M m₀ : ℕ) (Φ : ℝ → ℝ)
    (hq : 0 < q) (hm : 2 ≤ m₀) (hfit : m₀*q ≤ M) (hΦ : ∀ z, 0 ≤ Φ z)
    (loss U : ℝ) (hloss : loss ≤ log (log m₀)) :
    let W := fun n : ℕ => ∑' z : ℤ, Φ ((z : ℝ) - ((P.eval (n : ℤ) : ℤ) : ℝ) / q)
    ∃ (J : ℕ) (T : Fin J → Finset ℕ) (v : Fin J → ℝ),
      (∀ i, 0 ≤ v i) ∧ (∀ i, ∃ t l m : ℕ, 0 < l ∧ 2 ≤ m ∧ T i ⊆ range M ∧
        T i = (Icc 1 m).image (fun n => t + (n-1)*l) ∧ loss ≤ log (log m)) ∧
      ∑ n ∈ range M, |W n - ∑ i, if n ∈ T i then v i else 0| < (M : ℝ)*exp (-U) := by
  intro W
  obtain ⟨T,v,hv,ht,he⟩ := periodic_progression_mixture W hq (by omega : 0 < m₀)
    hfit (rational_patch_periodic P q hq Φ) (fun _ => tsum_nonneg (fun _ => hΦ _))
  refine ⟨q,T,v,hv,?_,?_⟩
  · intro i
    obtain ⟨m, hlen, hin, himg⟩ := ht i
    have hm₀' : (1 : ℝ) < m₀ := by exact_mod_cast (show 1 < m₀ by omega)
    have hle : (m₀ : ℝ) ≤ m := by exact_mod_cast hlen
    exact ⟨i.val,q,m,hq,hm.trans hlen,hin,himg,
      hloss.trans (log_le_log (log_pos hm₀') (log_le_log (by linarith) hle))⟩
  · have hz : (∑ n ∈ range M, |W n - ∑ i, if n ∈ T i then v i else 0|) = 0 :=
      sum_eq_zero (fun n hn => by rw [he n hn, sub_self, abs_zero])
    rw [hz]
    have hM : 0 < M := (Nat.mul_pos (by omega : 0 < m₀) hq).trans_le hfit
    positivity

private theorem increment_along (W : ℕ → ℝ) (q : ℕ) (η : ℝ)
    (h : ∀ n, |W (n+q)-W n| ≤ η) (a t : ℕ) : |W (a+t*q) - W a| ≤ t*η := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc]
    calc
      _ ≤ |W (a+t*q+q)-W (a+t*q)| + |W (a+t*q)-W a| := abs_sub_le _ _ _
      _ ≤ η + (t : ℝ)*η := add_le_add (h _) ih
      _ = _ := by push_cast; ring

/-- An almost period gives an L¹ approximation on an arbitrary interval.
There is one piece for each residue in each complete block of length Hq.
The final partial block is the only boundary loss. -/
theorem tile_almost_period (W : ℕ → ℝ) (M H q : ℕ) (η : ℝ) (hH : 0 < H)
    (hq : 0 < q) (hη : 0 ≤ η) (hW : ∀ n, W n ∈ Set.Icc 0 1)
    (hstep : ∀ n, |W (n+q)-W n| ≤ η) :
    ∃ (J : ℕ) (base : Fin J → ℕ) (v : Fin J → ℝ),
      (∀ i, 0 ≤ v i) ∧ (∀ i, ∀ t < H, base i+t*q < M) ∧
      ∑ n ∈ range M, |W n - ∑ i, if n ∈ (range H).image (fun t => base i+t*q)
          then v i else 0| ≤ (M : ℝ)*H*η + (M % (H*q) : ℕ) := by
  classical
  let C := H*q
  let K := M/C
  let I := Fin K × Fin q
  let e := Fintype.equivFin I
  let base (i : I) := i.1.val*C + i.2.val
  let piece (i : I) := (range H).image (fun t => base i + t*q)
  let model (n : ℕ) := ∑ i : I, if n ∈ piece i then W (base i) else 0
  have hC : 0 < C := Nat.mul_pos hH hq
  have hprefix : K*C ≤ M := Nat.div_mul_le_self _ _
  have small (i : Fin q) {t : ℕ} (ht : t < H) : i.val+t*q < C := by
    have hh := Nat.mul_le_mul_right q (show t+1 ≤ H by omega)
    rw [Nat.succ_mul] at hh
    dsimp [C]
    have := i.isLt
    omega
  have chunk {i : I} {n : ℕ} (hn : n ∈ piece i) :
      n/C = i.1.val ∧ n%q = i.2.val ∧ n < K*C := by
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hn
    have hs := small i.2 (mem_range.mp ht)
    refine ⟨?_, ?_, ?_⟩
    · change (i.1.val*C+i.2.val+t*q)/C = _
      rw [Nat.add_assoc, Nat.mul_comm i.1.val C, Nat.mul_add_div hC, Nat.div_eq_of_lt hs, Nat.add_zero]
    · change (i.1.val*(H*q)+i.2.val+t*q)%q = i.2.val
      rw [← Nat.mul_assoc, Nat.add_mul_mod_self_right, Nat.add_comm (_ * q) i.2.val,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.2.isLt]
    · have hh := Nat.mul_le_mul_right C i.1.isLt
      rw [Nat.succ_mul] at hh
      dsimp only [base]
      omega
  have cover (n : ℕ) (hn : n < K*C) : ∃ i : I, n ∈ piece i := by
    have hd : n/C < K := (Nat.div_lt_iff_lt_mul hC).mpr hn
    let i : I := (⟨n/C,hd⟩, ⟨n%q, Nat.mod_lt _ hq⟩)
    let t := (n%C)/q
    have ht : t < H := (Nat.div_lt_iff_lt_mul hq).mpr (Nat.mod_lt _ hC)
    have hmd : n%C%q = n%q := Nat.mod_mod_of_dvd _ (by dsimp [C]; exact dvd_mul_left _ _)
    have hr := Nat.mod_add_div (n%C) q
    rw [hmd, Nat.mul_comm] at hr
    refine ⟨i, mem_image.mpr ⟨t, mem_range.mpr ht, ?_⟩⟩
    change (n/C)*C + n%q + t*q = n
    rw [Nat.add_assoc, show n%q+t*q = n%C from hr, Nat.mul_comm]
    exact Nat.div_add_mod _ _
  have hgood (n : ℕ) (hn : n < K*C) : |W n-model n| ≤ (H : ℝ)*η := by
    obtain ⟨i, hi⟩ := cover n hn
    have hval : model n = W (base i) := by
      dsimp only [model]
      rw [sum_eq_single i]
      · simp [hi]
      · intro j _ hji
        have no : n ∉ piece j := by
          intro hj
          apply hji
          exact Prod.ext (Fin.ext ((chunk hj).1.symm.trans (chunk hi).1))
            (Fin.ext ((chunk hj).2.1.symm.trans (chunk hi).2.1))
        simp [no]
      · simp
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hi
    rw [hval]
    exact (increment_along W q η hstep (base i) t).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_range.mp ht).le) hη)
  have htail (t : ℕ) : |W (K*C+t)-model (K*C+t)| ≤ 1 := by
    have hz (i : I) : K*C+t ∉ piece i := fun hi => (by omega : ¬ K*C+t < K*C) (chunk hi).2.2
    simpa [model, hz, abs_of_nonneg (hW _).1] using (hW (K*C+t)).2
  have herr : ∑ n ∈ range M, |W n-model n| ≤ (M : ℝ)*H*η + (M % C : ℕ) := by
    have hsplit : K*C + M%C = M := by dsimp [K]; rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    calc
      _ = (∑ n ∈ range (K*C), |W n-model n|) + ∑ t ∈ range (M%C), |W (K*C+t)-model (K*C+t)| := by
        rw [← sum_range_add, hsplit]
      _ ≤ (∑ _n ∈ range (K*C), (H : ℝ)*η) + ∑ _t ∈ range (M%C), (1 : ℝ) :=
        add_le_add (sum_le_sum fun n hn => hgood n (mem_range.mp hn)) (sum_le_sum fun t _ => htail t)
      _ ≤ _ := by
        simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
        rw [← mul_assoc]
        gcongr
  refine ⟨Fintype.card I, fun i => base (e.symm i), fun i => W (base (e.symm i)),
    fun i => (hW _).1, ?_, ?_⟩
  · intro i t ht
    exact ((chunk (i := e.symm i) (mem_image_of_mem _ (mem_range.mpr ht))).2.2).trans_le hprefix
  · convert herr using 1
    refine sum_congr rfl (fun n _ => ?_)
    have h := Equiv.sum_comp e.symm (fun i : I => if n ∈ piece i then W (base i) else 0)
    change |W n - _| = |W n - model n|
    exact congrArg (fun y : ℝ => |W n - y|) h

/-- Any Lipschitz test of a real linear phase admits an explicit positive
approximation. Dirichlet's theorem chooses a stride q ≤ Q. The first error
is the drift along the progressions, and H*Q bounds the discarded tail. -/
theorem linear_phase_mixture (F : ℝ → ℝ) (α β : ℝ) (L : NNReal) (M H Q : ℕ)
    (hH : 0 < H) (hQ : 0 < Q) (hper : Function.Periodic F 1)
    (hlip : LipschitzWith L F) (hb : ∀ x, F x ∈ Set.Icc 0 1) :
    let W := fun n : ℕ => F (α*n + β)
    ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ∃ (J : ℕ) (base : Fin J → ℕ) (v : Fin J → ℝ),
      (∀ i, 0 ≤ v i) ∧ (∀ i, ∀ t < H, base i+t*q < M) ∧
      ∑ n ∈ range M, |W n - ∑ i, if n ∈ (range H).image (fun t => base i+t*q)
          then v i else 0| ≤ (M : ℝ)*H*((L : ℝ)/(Q+1)) + (H : ℝ)*Q := by
  intro W
  obtain ⟨j,k,hk,hkQ,happrox⟩ := Real.exists_int_int_abs_mul_sub_le α hQ
  lift k to ℕ using hk.le
  have hk' : 0 < k := by exact_mod_cast hk
  have hkQ' : k ≤ Q := by exact_mod_cast hkQ
  have hstep (n : ℕ) : |W (n+k)-W n| ≤ (L : ℝ)/(Q+1) := by
    have hp : F (α*n + β + j) = F (α*n + β) := by simpa using (hper.zsmul j) (α*n + β)
    have he := hlip.dist_le_mul (α*((n:ℝ)+k)+β) (α*n+β+j)
    rw [Real.dist_eq, Real.dist_eq, hp] at he
    have hdiff : α*((n:ℝ)+k)+β-(α*n+β+j) = (k:ℝ)*α-j := by ring
    rw [hdiff] at he
    change |F (α*(↑(n+k):ℝ)+β)-F (α*n+β)| ≤ _
    rw [Nat.cast_add]
    calc
      _ ≤ _ := he
      _ ≤ (L : ℝ) * (1/(Q+1)) := mul_le_mul_of_nonneg_left (by simpa using happrox) L.coe_nonneg
      _ = _ := by ring
  obtain ⟨J,base,v,hv,hin,herr⟩ := tile_almost_period W M H k _ hH hk' (by positivity)
    (fun n => hb _) hstep
  refine ⟨k,hk',hkQ',J,base,v,hv,hin,herr.trans ?_⟩
  have htail := (Nat.mod_lt M (Nat.mul_pos hH hk')).le.trans (Nat.mul_le_mul_left H hkQ')
  have htail' : ((M % (H*k) : ℕ) : ℝ) ≤ (H : ℝ)*Q := by exact_mod_cast htail
  exact add_le_add le_rfl htail'

/-- A nonnegative Lipschitz kernel supported in [-1/4,1/4] has a one-periodic
integer-lift sum with the same Lipschitz constant. At every point at most one
lift is nonzero, and a maximizing lift exists even when all values vanish. -/
theorem periodize_kernel (Φ : ℝ → ℝ) (L : NNReal) (hlip : LipschitzWith L Φ)
    (hb : ∀ x, Φ x ∈ Set.Icc 0 1) (hsupp : ∀ x, Φ x ≠ 0 → |x| ≤ 1/4) :
    let F := fun x : ℝ => ∑' z : ℤ, Φ ((z : ℝ)-x)
    Function.Periodic F 1 ∧ LipschitzWith L F ∧ ∀ x, F x ∈ Set.Icc 0 1 := by
  intro F
  have unique_lift (x : ℝ) (z w : ℤ) (hz : Φ ((z : ℝ)-x) ≠ 0)
      (hw : Φ ((w : ℝ)-x) ≠ 0) : z = w := by
    obtain ⟨hz₁,hz₂⟩ := abs_le.mp (hsupp _ hz)
    obtain ⟨hw₁,hw₂⟩ := abs_le.mp (hsupp _ hw)
    have h₁ : (z : ℝ) < (w : ℝ)+1 := by linarith
    have h₂ : (w : ℝ) < (z : ℝ)+1 := by linarith
    have h₁' : z < w+1 := by exact_mod_cast h₁
    have h₂' : w < z+1 := by exact_mod_cast h₂
    omega
  have peak (x : ℝ) : ∃ z : ℤ, F x = Φ ((z : ℝ)-x) ∧ ∀ w : ℤ, Φ ((w : ℝ)-x) ≤ F x := by
    by_cases hx : ∃ z : ℤ, Φ ((z : ℝ)-x) ≠ 0
    · obtain ⟨z,hz⟩ := hx
      have he (w : ℤ) (hw : w ≠ z) : Φ ((w : ℝ)-x) = 0 := by
        by_contra hn
        exact hw (unique_lift x w z hn hz)
      have hf : F x = Φ ((z : ℝ)-x) := tsum_eq_single z he
      refine ⟨z,hf,fun w => ?_⟩
      by_cases hw : w = z
      · simp [hw, hf]
      · rw [he w hw, hf]
        exact (hb _).1
    · push Not at hx
      have hf : F x = 0 := by dsimp [F]; simp [hx]
      exact ⟨0, by rw [hf, hx], fun w => by rw [hf, hx]⟩
  have upper (x y : ℝ) : F x - F y ≤ (L : ℝ)*|x-y| := by
    obtain ⟨z,hz,_⟩ := peak x
    obtain ⟨_,_,hy⟩ := peak y
    have h := hlip.dist_le_mul ((z:ℝ)-x) ((z:ℝ)-y)
    rw [Real.dist_eq, Real.dist_eq, show (z:ℝ)-x-(z-y) = -(x-y) by ring, abs_neg] at h
    linarith [(le_abs_self _).trans h, hy z]
  refine ⟨?_, LipschitzWith.of_dist_le_mul ?_, ?_⟩
  · intro x
    have h := (Equiv.addRight (-1 : ℤ)).tsum_eq (fun z : ℤ => Φ ((z : ℝ)-x))
    calc
      F (x+1) = ∑' z : ℤ, Φ (((z + -1 : ℤ) : ℝ)-x) := by
        refine tsum_congr (fun z => congrArg Φ ?_)
        push_cast
        ring
      _ = F x := h
  · intro x y
    rw [Real.dist_eq, Real.dist_eq]
    exact abs_le.mpr ⟨by have hh := upper y x; rw [abs_sub_comm y x] at hh; linarith, upper x y⟩
  · intro x
    obtain ⟨z,hz,_⟩ := peak x
    rw [hz]
    exact hb _

/-- Choose integer lengths for the linear-phase approximation. The cutoff
pays both the Lipschitz error and the discarded endpoints with a strict margin. -/
theorem affine_scales {N M : ℕ} {U L : ℝ} (hM : 0 < M)
    (hU : 1 ≤ U) (hsize : 64*U ≤ log N) (hside : log N-U ≤ log M)
    (hL : 0 ≤ L) (hlip : L ≤ exp U) :
    ∃ H Q : ℕ, 2 ≤ H ∧ 0 < Q ∧ log (log N) - log 8 ≤ log (log H) ∧
      (M : ℝ)*H*(L/(Q+1)) + (H : ℝ)*Q < (M : ℝ)*exp (-U) := by
  let t := log N/8
  let B := exp t
  let E := exp U
  let H := ⌈B⌉₊
  let Q := ⌈B^4⌉₊
  have ht : 8 ≤ t := by dsimp [t]; linarith
  have hB : 8 < B := by dsimp [B]; linarith [add_one_le_exp t]
  have hBp : 0 < B := by linarith
  have hEp : 0 < E := exp_pos _
  have hEB : E ≤ B := exp_le_exp.mpr (by dsimp [t]; linarith)
  have hHlo : B ≤ (H : ℝ) := Nat.le_ceil _
  have hQlo : B^4 ≤ (Q : ℝ) := Nat.le_ceil _
  have h4 : 1 ≤ B^4 := one_le_pow₀ (by linarith)
  have hHhi : (H : ℝ) ≤ 2*B := by
    have h := Nat.ceil_lt_add_one hBp.le; change (H : ℝ) < B+1 at h; linarith
  have hQhi : (Q : ℝ) ≤ 2*B^4 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ B^4 by positivity)
    change (Q : ℝ) < B^4+1 at h
    linarith
  have hM' : 0 < (M : ℝ) := by exact_mod_cast hM
  have hMlo : B^7 ≤ (M : ℝ) := calc
    B^7 = exp (7*t) := by simpa using (exp_nat_mul t 7).symm
    _ ≤ exp (log M) := exp_le_exp.mpr (by dsimp [t]; linarith)
    _ = _ := exp_log hM'
  have hHQ : 0 < (Q : ℝ)+1 := by positivity
  have hfirst : (H : ℝ)*L*E < ((Q : ℝ)+1)/2 := calc
    _ ≤ (2*B)*B*B := by gcongr; exact hlip.trans hEB
    _ < (B^4+1)/2 := by nlinarith [mul_pos (show 0 < B-4 by linarith) (pow_pos hBp 3)]
    _ ≤ _ := by linarith
  have hsecond : (H : ℝ)*Q*E < (M : ℝ)/2 := calc
    _ ≤ (2*B)*(2*B^4)*B := by gcongr
    _ < B^7/2 := by nlinarith [mul_pos (show 0 < B-8 by linarith) (pow_pos hBp 6)]
    _ ≤ _ := by linarith
  have hfrac : (H : ℝ)*(L/(Q+1))*E < 1/2 := by
    rw [show (H : ℝ)*(L/(Q+1))*E = (H*L*E)/(Q+1) by ring]
    apply (div_lt_iff₀ hHQ).mpr
    linarith
  have he : E*exp (-U) = 1 := by simp [E, exp_neg]
  have hH2 : 2 ≤ H := by exact_mod_cast (show (2 : ℝ) ≤ H by linarith)
  refine ⟨H,Q,hH2,by exact_mod_cast (show (0 : ℝ) < Q by linarith),?_,?_⟩
  · have hlog : t ≤ log H := by
      rw [← log_exp t]
      exact log_le_log (exp_pos _) hHlo
    have ht' : 0 < t := by linarith
    have hn : 0 < log N := by linarith
    have h := log_le_log ht' hlog
    rwa [show log t = log (log N)-log 8 by dsimp [t]; rw [log_div hn.ne' (by norm_num)]] at h
  · apply (mul_lt_mul_iff_left₀ hEp).mp
    have h := mul_lt_mul_of_pos_left hfrac hM'
    nlinarith only [h,hsecond,congrArg (fun z : ℝ => (M:ℝ)*z) he]

/-- A fully proved case of the long-progression approximation. The supplied
one-slot real polynomial is affine with arbitrary coefficients. The logarithmic
loss and strict score allowance have the same form as the geometric hypothesis. -/
theorem affine_patch_case (α β : ℝ) (Φ : (Fin 1 → ℝ) → ℝ) (L : NNReal)
    {N M : ℕ} {U R V : ℝ} (hM : 0 < M) (hU : 1 ≤ U)
    (hside : log (N : ℝ)-U ≤ log M) (hLip : (L : ℝ)+1 ≤ exp U) (hR : 0 ≤ R)
    (hV : log U ≤ V) (hsize : 6+3*R+V ≤ log (log N))
    (hlip : LipschitzWith L Φ) (hb : ∀ x, Φ x ∈ Set.Icc 0 1)
    (hsupp : ∀ x, Φ x ≠ 0 → ∀ i, |x i| ≤ 1/4) :
    let W := fun n : ℕ => ∑' z : Fin 1 → ℤ, Φ (fun i => (z i : ℝ) - (α*n+β))
    ∃ (J : ℕ) (T : Fin J → Finset ℕ) (v : Fin J → ℝ),
      (∀ i, 0 ≤ v i) ∧ (∀ i, ∃ a q m : ℕ, 0 < q ∧ 2 ≤ m ∧ T i ⊆ range M ∧
        T i = (Icc 1 m).image (fun n => a+(n-1)*q) ∧
        log (log N)-(6+2*R) ≤ log (log m)) ∧
      ∑ n ∈ range M, |W n-∑ i, if n ∈ T i then v i else 0| < (M : ℝ)*exp (-U) := by
  classical
  intro W
  have hUp : 0 < U := by linarith
  have hnlog : 0 < log N := by
    by_contra! hn
    have hn' : (N : ℝ) ≤ 1 := by
      by_contra! h
      exact (log_pos h).not_ge hn
    have hn'' : N ≤ 1 := by exact_mod_cast hn'
    interval_cases N <;> simp at hsize <;> linarith [log_nonneg hU]
  have e1 : (2:ℝ) < exp 1 := Real.exp_one_gt_two
  have e6 : (64:ℝ) ≤ exp 6 := calc
    (64:ℝ) = 2^6 := by norm_num
    _ ≤ (exp 1)^6 := pow_le_pow_left₀ (by norm_num) e1.le _
    _ = exp 6 := by convert (exp_nat_mul 1 6).symm using 1; norm_num
  have h64 : 64*U ≤ log N := calc
    64*U ≤ exp 6 * U := mul_le_mul_of_nonneg_right e6 hUp.le
    _ = exp (6 + log U) := by rw [exp_add, exp_log hUp]
    _ ≤ exp (log (log N)) := exp_le_exp.mpr (by linarith)
    _ = _ := exp_log hnlog
  obtain ⟨H,Q,hH,hQ,hlength,hbudget⟩ := affine_scales hM hU h64 hside L.coe_nonneg (by linarith : (L:ℝ) ≤ exp U)
  let φ (x : ℝ) := Φ (fun _ => x)
  have hφ : LipschitzWith L φ := LipschitzWith.of_dist_le_mul (fun x y => by
    simpa [φ,dist_pi_const] using hlip.dist_le_mul (fun _ => x) (fun _ => y))
  let F (x : ℝ) := ∑' z : ℤ, φ ((z : ℝ)-x)
  obtain ⟨hpF,hLF,hbF⟩ := periodize_kernel φ L hφ (fun x => hb _) (fun x hx => hsupp _ hx 0)
  have heval (n : ℕ) : W n = F (α*n+β) := by
    have h := (Equiv.funUnique (Fin 1) ℤ).symm.tsum_eq
      (fun z : Fin 1 → ℤ => Φ (fun i => (z i : ℝ)-(α*n+β)))
    exact h.symm
  obtain ⟨q,hq,_,J,a,v,hv,hin,herr⟩ :=
    linear_phase_mixture F α β L M H Q (by omega) hQ hpF hLF hbF
  let T (i : Fin J) := (range H).image (fun t => a i+t*q)
  refine ⟨J,T,v,hv,?_,?_⟩
  · intro i
    refine ⟨a i,q,H,hq,hH,?_,?_,?_⟩
    · intro x hx
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hx
      exact mem_range.mpr (hin i _ (mem_range.mp ht))
    · ext x
      constructor
      · intro hx
        obtain ⟨t,ht,rfl⟩ := mem_image.mp hx
        exact mem_image.mpr ⟨t+1,mem_Icc.mpr ⟨by omega, mem_range.mp ht⟩,by simp⟩
      · intro hx
        obtain ⟨n,hn,rfl⟩ := mem_image.mp hx
        obtain ⟨hn₁,hn₂⟩ := mem_Icc.mp hn
        exact mem_image.mpr ⟨n-1,mem_range.mpr (by omega),rfl⟩
    · have hlog8 : log (8:ℝ) ≤ 6 := (log_le_iff_le_exp (by norm_num)).mpr (by linarith)
      linarith
  · simp_rw [heval]
    exact herr.trans_lt hbudget


/-- On a one-variable slot, weighted support at most one forces affine evaluation. -/
theorem affine_evaluation {σ : Type*} [Unique σ] (P : MvPolynomial σ ℝ)
    (w : σ → ℕ) (hw : w default = 1)
    (h : P ∈ MvPolynomial.restrictSupport ℝ {m | Finsupp.weight w m ≤ 1}) :
    ∃ α β : ℝ, ∀ t : σ → ℝ, MvPolynomial.aeval t P = α*t default+β := by
  classical
  let Q := MvPolynomial.uniqueAlgEquiv ℝ σ P
  have hdeg : Q.degree ≤ 1 := by
    apply (Polynomial.degree_le_iff_coeff_zero Q 1).mpr
    intro m hm
    change (MvPolynomial.uniqueAlgEquiv ℝ σ P).coeff m = 0
    rw [MvPolynomial.coeff_uniqueAlgEquiv]
    by_contra hn
    have hs := h (MvPolynomial.mem_support_iff.mpr hn)
    change Finsupp.weight w (Finsupp.single default m) ≤ 1 at hs
    rw [Finsupp.weight_single,hw] at hs
    simpa using (show False from (not_lt_of_ge (show m ≤ 1 by simpa using hs)) (by exact_mod_cast hm))
  refine ⟨Q.coeff 1,Q.coeff 0,?_⟩
  intro t
  have he := MvPolynomial.eval₂_uniqueAlgEquiv (f := P) (φ := RingHom.id ℝ) (a := t)
  change Q.eval₂ (RingHom.id ℝ) (t default) = _ at he
  change P.eval₂ (RingHom.id ℝ) t = _
  rw [← he]
  conv_lhs => rw [Polynomial.eq_X_add_C_of_degree_le_one hdeg]
  simp

/-- The weighted-degree condition in H2 implies the affine representation at s=d=1.
This proves the complete one-slot degree-one specialization of the geometric hypothesis. -/
theorem one_slot_degree_one (w : Fin 1 → ℕ)
    (P : (i : Fin 1) → MvPolynomial (Unit ⊕ Fin i.val) ℝ)
    (hw : ∀ i, 1 ≤ w i ∧ w i ≤ 1)
    (hP : ∀ i, P i ∈ MvPolynomial.restrictSupport ℝ
      {m | Finsupp.weight (Sum.elim (fun _ : Unit ↦ (1:ℕ))
        (fun j : Fin i.val ↦ w ⟨j.val,lt_trans j.isLt i.isLt⟩)) m ≤ w i})
    (Φ : (Fin 1 → ℝ) → ℝ) (L : NNReal) {N M : ℕ} {U R V : ℝ}
    (hM : 0 < M) (hU : 1 ≤ U) (hside : log (N:ℝ)-U ≤ log M)
    (hLip : (L:ℝ)+1 ≤ exp U) (hR : 0 ≤ R) (hV : log U ≤ V)
    (hsize : 6+3*R+V ≤ log (log N))
    (hlip : LipschitzWith L Φ) (hb : ∀ x, Φ x ∈ Set.Icc 0 1)
    (hsupp : ∀ x, Φ x ≠ 0 → ∀ i, |x i| ≤ 1/4) :
    let W := fun n : ℕ => ∑' z : Fin 1 → ℤ, Φ (fun i => (z i:ℝ) -
      MvPolynomial.aeval (Sum.elim (fun _ : Unit ↦ (n:ℝ))
        (fun j : Fin i.val ↦ (z ⟨j.val,lt_trans j.isLt i.isLt⟩:ℝ))) (P i))
    ∃ (J : ℕ) (T : Fin J → Finset ℕ) (v : Fin J → ℝ),
      (∀ i, 0 ≤ v i) ∧ (∀ i, ∃ a q m : ℕ, 0 < q ∧ 2 ≤ m ∧ T i ⊆ range M ∧
        T i = (Icc 1 m).image (fun n => a+(n-1)*q) ∧
        log (log N)-(6+2*R) ≤ log (log m)) ∧
      ∑ n ∈ range M, |W n-∑ i, if n ∈ T i then v i else 0| < (M:ℝ)*exp (-U) := by
  classical
  let o : Fin 1 := ⟨0,by decide⟩
  let : Unique (Unit ⊕ Fin o.val) := {
    default := Sum.inl ()
    uniq := by
      rintro (u|v)
      · cases u; rfl
      · exact Fin.elim0 v }
  let w' : Unit ⊕ Fin o.val → ℕ := Sum.elim (fun _ => 1) (fun j => Fin.elim0 j)
  have hdeg : P o ∈ MvPolynomial.restrictSupport ℝ {m | Finsupp.weight w' m ≤ 1} := by
    have he : w o = 1 := le_antisymm (hw o).2 (hw o).1
    have hf : (Sum.elim (fun _ : Unit ↦ (1:ℕ)) (fun j : Fin o.val ↦
        w ⟨j.val,lt_trans j.isLt o.isLt⟩)) = w' := by
      funext x
      rcases x with u|v
      · rfl
      · exact Fin.elim0 v
    simpa only [hf,he] using hP o
  obtain ⟨α,β,heval⟩ := affine_evaluation (P o) w' rfl hdeg
  have he (n : ℕ) (z : Fin 1 → ℤ) (i : Fin 1) :
      MvPolynomial.aeval (Sum.elim (fun _ : Unit ↦ (n:ℝ))
        (fun j : Fin i.val ↦ (z ⟨j.val,lt_trans j.isLt i.isLt⟩:ℝ))) (P i) = α*n+β := by
    have eqo : i = o := Subsingleton.elim _ _
    subst i
    exact heval _
  intro W
  simp only [W,he]
  exact affine_patch_case α β Φ L hM hU hside hLip hR hV hsize hlip hb hsupp


/-- At or below the cube-root resource cutoff the inverse claim already has an
unconditional witness. One occupied point and a zero-slot constant test suffice. -/
theorem small_scale_source (s N : ℕ) (S : Finset ℕ) (hN : 2 ≤ N) (hS : S ⊆ Icc 1 N)
    (hSc : 0 < S.card) : let p := max 2 (log (2*(N:ℝ)/S.card))
    16 < p → log (log N) ≤ p^(1/3:ℝ) →
    ∃ (d M a q : ℕ) (U : ℝ) (w : Fin d → ℕ)
      (P : (i : Fin d) → MvPolynomial (Unit ⊕ Fin i.val) ℝ)
      (Φ : (Fin d → ℝ) → ℝ) (L' : NNReal),
      (∀ i, 1 ≤ w i ∧ w i ≤ s) ∧ Monotone w ∧
      (∀ i, P i ∈ MvPolynomial.restrictSupport ℝ
        {m | Finsupp.weight (Sum.elim (fun _ : Unit ↦ (1 : ℕ))
          (fun j : Fin i.val ↦ w ⟨j.val, lt_trans j.isLt i.isLt⟩)) m ≤ w i}) ∧
      (∀ x, 0 ≤ Φ x ∧ Φ x ≤ 1) ∧ (∀ x, Φ x ≠ 0 → ∀ i, |x i| ≤ 1/4) ∧
      LipschitzWith L' Φ ∧ 0 < q ∧ (∀ n < M, a+q*n ∈ Icc 1 N) ∧
      1 ≤ U ∧ log (N:ℝ)-U ≤ log M ∧ (L':ℝ)+1 ≤ exp U ∧
      let R := log ((d:ℝ)+1)
      let δ := (1+R)*sqrt p
      ((2*s*s+1 : ℕ):ℝ)*R + log U ≤ 1*p^(1/3:ℝ) ∧ 2 ≤ p-δ ∧
      exp (-U) ≤ (∑ n ∈ range M,
        ((if a+q*n ∈ S then (1:ℝ) else 0)-exp δ*((S.card:ℝ)/N)) *
          ∑' z : Fin d → ℤ, Φ (fun i ↦ (z i:ℝ) - MvPolynomial.aeval
            (Sum.elim (fun _ : Unit ↦ (n:ℝ))
              (fun j : Fin i.val ↦ (z ⟨j.val, lt_trans j.isLt i.isLt⟩:ℝ))) (P i))) / (M:ℝ) := by
  intro p hp hscale
  classical
  obtain ⟨a,ha⟩ := card_pos.mp hSc
  let U := max 1 (log (N:ℝ))
  have hU : 1 ≤ U := le_max_left _ _
  have hN' : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hSc' : 0 < (S.card:ℝ) := by exact_mod_cast hSc
  have hpeq : p = log (2*(N:ℝ)/S.card) := by
    change max 2 _ = _
    apply max_eq_right
    by_contra! he
    change 16 < max 2 _ at hp
    rw [max_eq_left he.le] at hp
    norm_num at hp
  have hs : 0 ≤ sqrt p := sqrt_nonneg _
  have hs2 := sq_sqrt (by linarith : 0 ≤ p)
  have hsl : 2 ≤ sqrt p := by nlinarith
  have hroom : sqrt p+2 ≤ p := by nlinarith [mul_nonneg (by linarith : 0 ≤ sqrt p-2) (sqrt_nonneg p)]
  have hexp : 2 ≤ exp (1:ℝ) := by linarith [add_one_le_exp (1:ℝ)]
  have hexp2 : 4 ≤ exp (2:ℝ) := by
    rw [show (2:ℝ)=1+1 by norm_num,exp_add]
    nlinarith [sq_nonneg (exp 1-2)]
  have hratio : exp p*((S.card:ℝ)/N) = 2 := by
    rw [hpeq,exp_log (by positivity)]
    field_simp
  have hsmall : exp (sqrt p)*((S.card:ℝ)/N) ≤ 1/2 := by
    have he := exp_le_exp.mpr hroom
    rw [exp_add] at he
    have hh := (mul_le_mul_of_nonneg_left hexp2 (exp_pos (sqrt p)).le).trans he
    have hh' := mul_le_mul_of_nonneg_right hh (div_pos hSc' hN').le
    nlinarith only [hh',hratio]
  have hexpU : exp (-U) ≤ 1/2 := by
    rw [exp_neg,inv_eq_one_div]
    apply (div_le_div_iff₀ (exp_pos _) (by norm_num : (0:ℝ)<2)).mpr
    linarith [add_one_le_exp U]
  have hlogU : log U ≤ p^(1/3:ℝ) := by
    by_cases he : 1 ≤ log (N:ℝ)
    · simpa [U,max_eq_right he] using hscale
    · simp only [U,max_eq_left (le_of_not_ge he),log_one]
      exact rpow_nonneg (by linarith) _
  refine ⟨0,1,a,1,U,Fin.elim0,(fun i => Fin.elim0 i),(fun _ => 1),0,?_,?_,?_,?_,?_,?_,
    by decide,?_,hU,?_,?_,?_⟩
  · exact fun i => Fin.elim0 i
  · exact fun i => Fin.elim0 i
  · exact fun i => Fin.elim0 i
  · intro x
    norm_num
  · exact fun _ _ i => Fin.elim0 i
  · exact LipschitzWith.const _
  · intro n hn
    have : n = 0 := by omega
    simpa [this] using hS ha
  · simp only [Nat.cast_one,log_one]
    exact sub_nonpos.mpr (le_max_right _ _)
  · simp only [NNReal.coe_zero,zero_add]
    exact one_le_exp (by linarith)
  · simp only [Nat.cast_zero, zero_add,log_one,add_zero,one_mul,mul_zero]
    refine ⟨by simpa using hlogU,by linarith,?_⟩
    rw [sum_range_one]
    simpa [ha] using (show exp (-U) ≤ 1-exp (sqrt p)*((S.card:ℝ)/N) by linarith)

private theorem scored_of_approximation (geometry : H2) : ∀ s : ℕ, ∃ L₀ : ℝ, ∀ (N : ℕ) (S : Finset ℕ) (p : ℝ) (d M a q : ℕ) (U R V G δ : ℝ)
      (w : Fin d → ℕ) (P : (i : Fin d) → MvPolynomial (Unit ⊕ Fin i.val) ℝ)
      (Φ : (Fin d → ℝ) → ℝ) (L : NNReal),
    (∀ i, 1 ≤ w i ∧ w i ≤ s) → Monotone w →
    (∀ i, P i ∈ MvPolynomial.restrictSupport ℝ
      {m | Finsupp.weight (Sum.elim (fun _ : Unit ↦ (1 : ℕ))
        (fun j : Fin i.val ↦ w ⟨j.val, lt_trans j.isLt i.isLt⟩)) m ≤ w i}) →
    (∀ x, 0 ≤ Φ x ∧ Φ x ≤ 1) → (∀ x, Φ x ≠ 0 → ∀ i, |x i| ≤ 1 / 4) →
    LipschitzWith L Φ →
    2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
    p = max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ))) →
    0 < q → (∀ n < M, a + q * n ∈ Finset.Icc 1 N) → 1 ≤ U →
    Real.log (N : ℝ) - U ≤ Real.log (M : ℝ) → (L : ℝ) + 1 ≤ Real.exp U →
    Real.log ((d : ℝ) + 1) ≤ R → Real.log U ≤ V →
    L₀ + ((2 * s * s + 1 : ℕ) : ℝ) * R + V ≤ Real.log (Real.log (N : ℝ)) →
    0 < G → δ ≤ Real.log G → 2 ≤ p - δ →
    Real.exp (-U) ≤ (∑ n ∈ Finset.range M,
      ((if a + q * n ∈ S then (1 : ℝ) else 0) - G * ((S.card : ℝ) / (N : ℝ))) *
        ∑' b : Fin d → ℤ, Φ (fun i ↦ (b i : ℝ) - MvPolynomial.aeval
          (Sum.elim (fun _ : Unit ↦ (n : ℝ))
            (fun j : Fin i.val ↦ (b ⟨j.val, lt_trans j.isLt i.isLt⟩ : ℝ))) (P i))) /
      (M : ℝ) →
    ∃ a' q' M' : ℕ, 0 < q' ∧ 2 ≤ M' ∧
      (∀ i ∈ Finset.Icc 1 M', a' + (i - 1) * q' ∈ Finset.Icc 1 N) ∧
      Real.log (Real.log (N : ℝ)) - (L₀ + ((2 * s * s : ℕ) : ℝ) * R) ≤
        Real.log (Real.log (M' : ℝ)) ∧
      G * ((S.card : ℝ) / (N : ℝ)) <
        (((Finset.Icc 1 M').filter (fun i ↦ a' + (i - 1) * q' ∈ S)).card : ℝ) / (M' : ℝ) ∧
      max 2 (Real.log (2 * (M' : ℝ) /
        (((Finset.Icc 1 M').filter (fun i ↦ a' + (i - 1) * q' ∈ S)).card : ℝ))) ≤ p - δ := by
  classical
  intro s
  obtain ⟨L₀, hap⟩ := geometry s
  refine ⟨L₀, ?_⟩
  intro N S p d M a q U R V G δ w P Φ L hw hm hP hΦ hsupport hlip hN hS hSc hp hq hslice hU hM hL hR hV hsize hG hδ hroom hscore
  let α := (S.card : ℝ) / N
  let f (n : ℕ) : ℝ := if a + q*n ∈ S then 1 else 0
  let W (n : ℕ) := ∑' z : Fin d → ℤ, Φ (fun i ↦ (z i : ℝ) - MvPolynomial.aeval
    (Sum.elim (fun _ : Unit ↦ (n : ℝ))
      (fun j : Fin i.val ↦ (z ⟨j.val, lt_trans j.isLt i.isLt⟩ : ℝ))) (P i))
  change exp (-U) ≤ (∑ n ∈ range M, (f n-G*α)*W n) / (M : ℝ) at hscore
  have hMp : 0 < M := by
    by_contra! he
    have hz : M = 0 := by omega
    rw [hz] at hscore
    exact (exp_pos (-U)).not_ge (by simpa using hscore)
  have hM' : 0 < (M : ℝ) := by exact_mod_cast hMp
  obtain ⟨J, T, v, hv, ht, herr⟩ :=
    hap N M d U R V w P Φ L hw hm hP hΦ hsupport hlip hN hMp hU hM hL hR hV hsize
  have hf (n) (_ : n ∈ range M) : f n ∈ Set.Icc 0 1 := by
    dsimp [f]; split <;> norm_num
  have hW (n) (_ : n ∈ range M) : 0 ≤ W n := tsum_nonneg (fun z => (hΦ _).1)
  have hin (i) : T i ⊆ range M := by obtain ⟨_, _, _, _, _, hh, _⟩ := ht i; exact hh
  have hα : 0 < α := by dsimp [α]; positivity
  have hs' := (le_div_iff₀ hM').mp hscore
  obtain ⟨i, hi⟩ := select_piece (range M) f W T v (G*α) ((M : ℝ)*exp (-U)) hf hW hin hv
    (mul_pos hG hα).le (mul_pos hM' (exp_pos _)) (by linarith) herr
  obtain ⟨t, l, m, hl, hm2, hsubset, hT, hlength⟩ := ht i
  let j (n : ℕ) := t + (n-1)*l
  let a' := a + q*t
  let q' := q*l
  have hj (n) : a+q*(j n) = a'+(n-1)*q' := by dsimp [j,a',q']; ring
  have hjmem (n) (hn : n ∈ Icc 1 m) : j n < M := by
    exact mem_range.mp (hsubset (hT ▸ mem_image_of_mem _ hn))
  have hjinj : Set.InjOn j (Icc 1 m : Finset ℕ) := by
    intro x hx y hy hxy
    have hx' := (mem_Icc.mp hx).1
    have hy' := (mem_Icc.mp hy).1
    have hh := Nat.eq_of_mul_eq_mul_right hl (Nat.add_left_cancel hxy)
    omega
  let B := (Icc 1 m).filter (fun n => a'+(n-1)*q' ∈ S)
  change T i = (Icc 1 m).image j at hT
  rw [hT, card_image_of_injOn hjinj, sum_image (fun x hx y hy h => hjinj hx hy h)] at hi
  have hsum : ∑ n ∈ Icc 1 m, f (j n) = (B.card : ℝ) := by
    simp [f, hj, B]
  rw [hsum] at hi
  simp only [Nat.card_Icc, Nat.add_sub_cancel] at hi
  have hm' : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hdense : G*α < (B.card : ℝ)/m := (lt_div_iff₀ hm').mpr (by simpa using hi)
  have hB : 0 < (B.card : ℝ) := by by_contra! hb; exact (mul_pos hG hα).not_ge (hdense.le.trans (div_nonpos_of_nonpos_of_nonneg hb hm'.le))
  refine ⟨a', q', m, Nat.mul_pos hq hl, hm2, ?_, hlength, hdense, max_le hroom ?_⟩
  · intro n hn
    rw [← hj]
    exact hslice _ (hjmem n hn)
  · change log (2*(m:ℝ)/B.card) ≤ p-δ
    have hratio := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2) (mul_pos hG hα) hdense.le
    have hh := log_le_log (by positivity) hratio
    rw [show 2/((B.card : ℝ)/m) = 2*(m:ℝ)/B.card by field_simp] at hh
    rw [log_div (by norm_num) (mul_pos hG hα).ne', log_mul hG.ne' hα.ne'] at hh
    have hN' : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hSc' : 0 < (S.card : ℝ) := by exact_mod_cast hSc
    have hbase : log 2 - log α ≤ p := by
      rw [hp, show log 2 - log α = log (2*(N:ℝ)/S.card) by
        rw [← log_div (by norm_num) hα.ne']; dsimp [α]; congr 1; field_simp]
      exact le_max_right _ _
    linarith

/-- Composition in one-based progression coordinates, including the first point. -/
private theorem compose_index (a b q e i : ℕ) (hb : 1 ≤ b) :
    a+(b+(i-1)*e-1)*q = (a+(b-1)*q)+(i-1)*(e*q) := by
  rw [show b+(i-1)*e-1 = (b-1)+(i-1)*e by omega]
  ring

/-- Taking a progression section preserves absence of five-term progressions. -/
private theorem free_section (S : Finset ℕ) (m a q : ℕ) (hq : 0 < q)
    (hf : ¬ ∃ x e : ℕ, 0 < e ∧ ∀ i < 5, x+i*e ∈ S) :
    ¬ ∃ x e : ℕ, 0 < e ∧ ∀ i < 5, x+i*e ∈ (Icc 1 m).filter
      (fun n => a+(n-1)*q ∈ S) := by
  rintro ⟨b,e,he,h⟩
  have hfirst := h 0 (by decide)
  rw [Nat.zero_mul,Nat.add_zero] at hfirst
  have hb : 1 ≤ b := (mem_Icc.mp (mem_filter.mp hfirst).1).1
  apply hf
  refine ⟨a+(b-1)*q,e*q,Nat.mul_pos he hq,fun i hi => ?_⟩
  have hm := (mem_filter.mp (h i hi)).2
  rwa [show b+i*e-1 = (b-1)+i*e by omega, Nat.add_mul,
    Nat.mul_assoc, ← Nat.add_assoc] at hm

/-- A drop of (1+R) sqrt(p) pays for a log-log length loss linear in 1+R. -/
private theorem pay_sqrt {p t R : ℝ} (hp : 2 ≤ p) (ht : 0 ≤ t) (hR : 0 ≤ R)
    (hdrop : t ≤ p-(1+R)*sqrt p) : 1+R ≤ 2*(sqrt p-sqrt t) := by
  have hroot : 0 < sqrt p := sqrt_pos.mpr (by linarith)
  have htp : t ≤ p := by nlinarith [mul_nonneg (show 0 ≤ 1+R by linarith) hroot.le]
  have hs := sqrt_le_sqrt htp
  have hx : (1+R)*sqrt p ≤ (sqrt p-sqrt t)*(sqrt p+sqrt t) := by
    nlinarith only [hdrop,sq_sqrt (by linarith : 0 ≤ p),sq_sqrt ht]
  have hy := mul_le_mul_of_nonneg_left (show sqrt p+sqrt t ≤ 2*sqrt p by linarith)
    (sub_nonneg.mpr hs)
  exact le_of_mul_le_mul_right (by nlinarith only [hx,hy] :
    (1+R)*sqrt p ≤ (2*(sqrt p-sqrt t))*sqrt p) hroot

/-- Iterate strictly improving, indexed sections and telescope their actual length losses. -/
private theorem halve_sections {D K T : ℝ} (hD : 0 < D) (hKD : D ≤ K)
    (step : ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Icc 1 N → 0 < S.card →
      (¬ ∃ a e : ℕ, 0 < e ∧ ∀ i < 5, a+i*e ∈ S) →
      let p := max 2 (log (2*(N:ℝ)/S.card))
      T < p → K*sqrt p ≤ log (log N) →
      ∃ a q m : ℕ, 0 < q ∧ 2 ≤ m ∧ (∀ i ∈ Icc 1 m, a+(i-1)*q ∈ Icc 1 N) ∧
        let B := (Icc 1 m).filter (fun i => a+(i-1)*q ∈ S)
        let t := max 2 (log (2*(m:ℝ)/B.card))
        0 < B.card ∧ t+1 ≤ p ∧ log (log N)-log (log m) ≤ D*(sqrt p-sqrt t)) :
    OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R2.H1 := by
  classical
  refine ⟨D,K,2*max 4 T,hD,?_⟩
  intro N A hN hA hcard hf p hp hbudget
  let param (m : ℕ) (B : Finset ℕ) := max 2 (log (2*(m:ℝ)/B.card))
  let sectionSet (a q m : ℕ) := (Icc 1 m).filter (fun i => a+(i-1)*q ∈ A)
  let Goal := ∃ a q m : ℕ, 0 < q ∧ 2 ≤ m ∧
    (∀ i ∈ Icc 1 m, a+(i-1)*q ∈ Icc 1 N) ∧
    0 < (sectionSet a q m).card ∧ param m (sectionSet a q m) ≤ p/2 ∧
    log (log N) ≤ log (log m)+D*sqrt p
  change Goal
  have loop (j : ℕ) : ∀ a q m : ℕ, 0 < q → 2 ≤ m →
      (∀ i ∈ Icc 1 m, a+(i-1)*q ∈ Icc 1 N) →
      let B := sectionSet a q m
      let t := param m B
      0 < B.card → ⌊t⌋₊ = j → K*sqrt t ≤ log (log m) →
      log (log N)-log (log m) ≤ D*(sqrt p-sqrt t) → Goal := by
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro a q m hq hm hin B t hB hj hbud hloss
      by_cases hstop : t ≤ p/2
      · exact ⟨a,q,m,hq,hm,hin,hB,hstop,by nlinarith [mul_nonneg hD.le (sqrt_nonneg t)]⟩
      have hthreshold : T < t := by linarith [le_max_right (4:ℝ) T]
      obtain ⟨b,e,l,he,hl,hin',hc,hd,hcost⟩ := step m B hm (filter_subset _ _)
        hB (free_section A m a q hq hf) hthreshold hbud
      let C := (Icc 1 l).filter (fun i => b+(i-1)*e ∈ B)
      let t' := param l C
      change 0 < C.card at hc
      change t'+1 ≤ t at hd
      change log (log m)-log (log l) ≤ D*(sqrt t-sqrt t') at hcost
      have hb : 1 ≤ b := (mem_Icc.mp (by simpa using hin' 1 (mem_Icc.mpr ⟨le_rfl,by omega⟩))).1
      have heq : C = sectionSet (a+(b-1)*q) (e*q) l := by
        ext i
        simp only [C, B, sectionSet, mem_filter]
        constructor
        · rintro ⟨hi,_,hs⟩
          exact ⟨hi,compose_index a b q e i hb ▸ hs⟩
        · rintro ⟨hi,hs⟩
          exact ⟨hi,hin' i hi,(compose_index a b q e i hb).symm ▸ hs⟩
      have hfloor : ⌊t'⌋₊ < j := by
        rw [← hj]
        have hpos : 0 ≤ t' := le_trans (by norm_num) (le_max_left _ _)
        have h := Nat.floor_le_floor hd
        rwa [Nat.floor_add_one hpos] at h
      have hdec := sub_nonneg.mpr (sqrt_le_sqrt (by linarith : t' ≤ t))
      have hK := mul_le_mul_of_nonneg_right hKD hdec
      have hrec := ih ⌊t'⌋₊ hfloor (a+(b-1)*q) (e*q) l (Nat.mul_pos he hq) hl
        (fun i hi => compose_index a b q e i hb ▸ hin _ (hin' i hi))
      dsimp only at hrec
      rw [← heq] at hrec
      exact hrec hc rfl (by nlinarith only [hbud,hcost,hK])
        (by nlinarith only [hloss,hcost])
  have hinit : sectionSet 1 1 N = A := by
    ext i
    simp only [sectionSet, mem_filter]
    constructor
    · rintro ⟨hi,h⟩
      rwa [show 1+(i-1)*1=i by have := (mem_Icc.mp hi).1; omega] at h
    · intro hi
      have hin := hA hi
      exact ⟨hin,by simpa [show 1+(i-1)=i by have := (mem_Icc.mp hin).1; omega] using hi⟩
  have hstart := loop ⌊p⌋₊ 1 1 N (by decide) hN
    (fun i hi => by rwa [show 1+(i-1)*1=i by have := (mem_Icc.mp hi).1; omega])
  dsimp only at hstart
  rw [hinit] at hstart
  exact hstart hcard rfl hbudget (by change _ ≤ D*(sqrt p-sqrt p); simp)

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R2.H1 := by
  classical
  rintro ⟨s,B,T,hB,source⟩ geometry
  obtain ⟨L₀,score⟩ := scored_of_approximation geometry s
  let dcost : ℝ := |L₀| + ((2*s*s:ℕ):ℝ) + 1
  let D := 2*dcost
  let K := max D (|L₀|+B)
  have hdc : 0 < dcost := by dsimp [dcost]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hKD : D ≤ K := le_max_left _ _
  apply halve_sections hD hKD (T := max 4 T)
  intro N S hN hS hSc hf p hp hreserve
  have hp2 : 2 ≤ p := le_max_left _ _
  have hsqrt : 1 ≤ sqrt p := by
    exact (by simpa using sqrt_le_sqrt (show (1:ℝ) ≤ p by linarith))
  have hroot : 0 ≤ sqrt p := sqrt_nonneg _
  obtain ⟨d,M,a,q,U,w,P,Φ,L',hw,hmono,hP,hΦ,hsp,hlip,hq,hin,hU,hside,hlip',hresources,hroom,hscore⟩ :=
    source N S hN hS hSc hf ((le_max_right 4 T).trans_lt hp)
  let R := log ((d:ℝ)+1)
  let δ := (1+R)*sqrt p
  have hR : 0 ≤ R := log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) d] : (1:ℝ) ≤ (d:ℝ)+1)
  change ((2*s*s+1:ℕ):ℝ)*R + log U ≤ B*p^(1/3:ℝ) at hresources
  have hpow : p^(1/3:ℝ) ≤ sqrt p := by
    rw [sqrt_eq_rpow]
    exact rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hres := hresources.trans (mul_le_mul_of_nonneg_left hpow hB)
  change 2 ≤ p-δ at hroom
  have hbudget : L₀+((2*s*s+1:ℕ):ℝ)*R+log U ≤ log (log N) := by
    have ha := mul_le_mul_of_nonneg_right (le_max_right D (|L₀|+B)) hroot
    have hb := mul_le_mul_of_nonneg_left hsqrt (abs_nonneg L₀)
    nlinarith only [ha,hb,hres,hreserve,le_abs_self L₀]
  obtain ⟨a',q',m,hq',hm,hin',hlen,hdense,hnew⟩ := score N S p d M a q U R (log U)
    (exp δ) δ w P Φ L' hw hmono hP hΦ hsp hlip hN hS hSc rfl hq hin hU hside
    hlip' le_rfl le_rfl hbudget (exp_pos _) (by rw [log_exp]) hroom hscore
  let V := (Icc 1 m).filter (fun i => a'+(i-1)*q' ∈ S)
  let t := max 2 (log (2*(m:ℝ)/V.card))
  change t ≤ p-δ at hnew
  have hV : 0 < V.card := by
    by_contra! hz
    have he : V.card = 0 := by omega
    change exp δ*((S.card:ℝ)/N) < (V.card:ℝ)/m at hdense
    rw [he,Nat.cast_zero,zero_div] at hdense
    exact (not_lt_of_ge (by positivity) hdense)
  have ht : 0 ≤ t := le_trans (by norm_num) (le_max_left _ _)
  have pay := pay_sqrt hp2 ht hR hnew
  have hone : 1 ≤ δ := by dsimp [δ]; nlinarith [mul_nonneg hR hroot]
  refine ⟨a',q',m,hq',hm,hin',hV,by linarith,?_⟩
  change log (log N)-(L₀+((2*s*s:ℕ):ℝ)*R) ≤ log (log m) at hlen
  have hbase : L₀+((2*s*s:ℕ):ℝ)*R ≤ dcost*(1+R) := by
    dsimp [dcost]
    nlinarith [le_abs_self L₀,mul_nonneg (abs_nonneg L₀) hR,
      (show 0 ≤ ((2*s*s:ℕ):ℝ) by positivity)]
  have hh := mul_le_mul_of_nonneg_left pay hdc.le
  change log (log N)-log (log m) ≤ 2*dcost*(sqrt p-sqrt t)
  nlinarith only [hh,hbase,hlen]

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R2_H1_R1
