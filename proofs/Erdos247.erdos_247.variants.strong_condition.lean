import FormalConjectures.ErdosProblems.«247»
import Mathlib

/-! A finite dyadic carry proof for Erdős Problem 247. -/

open Filter Finset Polynomial
open scoped BigOperators

namespace OMA247

noncomputable section

private def q (m : ℕ) : ℝ := (1/2)^m

private lemma q_pos (m : ℕ) : 0 < q m := by unfold q; positivity

private lemma q_add (i j : ℕ) : q (i+j) = q i * q j := by unfold q; rw [pow_add]

private lemma q_anti : Antitone q := by
  intro i j h
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h

private lemma q_scale (i j : ℕ) (h : i ≤ j) : q i * q (j-i) = q j := by
  rw [← q_add, Nat.add_sub_of_le h]

private lemma q_twopow (i j : ℕ) (h : i ≤ j) :
    q j * (2 : ℝ)^(j-i) = q i := by
  rw [← q_scale i j h]
  unfold q
  rw [mul_assoc, ← mul_pow]
  norm_num

private lemma quarter (B : ℕ) : (B : ℝ) * q (B+2) ≤ 1/4 := by
  have h : (B : ℝ) ≤ 2^B := by exact_mod_cast B.lt_two_pow_self.le
  calc
    (B : ℝ) * q (B+2) ≤ (2:ℝ)^B * q (B+2) :=
      mul_le_mul_of_nonneg_right h (q_pos _).le
    _ = 1/4 := by
      have ht := q_twopow 2 (B+2) (by omega)
      rw [show (B+2-2) = B by omega] at ht
      convert ht using 1 <;> norm_num [mul_comm, q]

private lemma exists_avoiding {S : Finset ℕ} (a j K : ℕ)
    (h : S.card*K < j) :
    ∃ R ∈ Ico a (a+j), ∀ s ∈ S, ¬ (R < s ∧ s ≤ R+K) := by
  classical
  let bad := (S ×ˢ range K).image fun p => p.1-(p.2+1)
  have hb : bad.card ≤ S.card*K := by
    simpa [bad] using (card_image_le (s := S ×ˢ range K)
      (f := fun p : ℕ × ℕ => p.1-(p.2+1)))
  have hc : (Ico a (a+j)).card = j := by simp
  obtain ⟨R, hR, hn⟩ := exists_mem_notMem_of_card_lt_card
    (show bad.card < (Ico a (a+j)).card by omega)
  refine ⟨R, hR, fun s hs hh => hn ?_⟩
  exact mem_image.2 ⟨(s,s-R-1), mem_product.2 ⟨hs, mem_range.2 (by omega)⟩, by
    dsimp
    omega⟩

private lemma exists_scaled_integer {ι : Type*} [Fintype ι] (c : ι → ℤ)
    (w : ι → ℕ) (R : ℕ) (hR : ∀ i, w i ≤ R) :
    ∃ z : ℤ, (∑ i, (c i : ℝ) * q (w i)) = q R * z := by
  refine ⟨∑ i, c i * 2^(R-w i), ?_⟩
  push_cast
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [← q_twopow (w i) R (hR i)]
  ring

private lemma tail_bound {ι : Type*} [Fintype ι]
    (c : ι → ℤ) (w : ι → ℕ) (s : Finset ι) (m : ℕ)
    (h : ∀ i ∈ s, m ≤ w i) :
    |∑ i ∈ s, (c i : ℝ) * q (w i)| ≤ (∑ i, (c i).natAbs : ℕ) * q m := by
  calc
    _ ≤ ∑ i ∈ s, |(c i : ℝ) * q (w i)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, ((c i).natAbs : ℝ) * q m := by
      apply sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (q_pos _).le, Nat.cast_natAbs]
      have hc : (0:ℝ) ≤ |(c i : ℝ)| := abs_nonneg _
      exact_mod_cast mul_le_mul_of_nonneg_left (q_anti (h i hi)) hc
    _ ≤ _ := by
      push_cast
      rw [sum_mul]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (by
        intros
        exact mul_nonneg (Nat.cast_nonneg _) (q_pos _).le)

/-- A positive term in a gap for negative terms contradicts the small total
when an earlier cut is separated from every subsequent term. -/
private lemma finite_carry {ι : Type*} [Fintype ι]
    (c : ι → ℤ) (w : ι → ℕ) (B L N R : ℕ) (i₀ : ι)
    (hB : (∑ i, (c i).natAbs) ≤ B) (hL : L ≤ B)
    (hV : |∑ i, (c i : ℝ) * q (w i)| ≤ L * q N)
    (hzero : ∀ i, R < w i → R+B+2 < w i)
    (hRi : R < w i₀) (hNi : w i₀+B+2 ≤ N) (hi : 0 < c i₀)
    (hgap : ∀ i, R < w i → w i ≤ w i₀+B+2 → 0 ≤ c i) :
    False := by
  classical
  let v (i : ι) := (c i : ℝ) * q (w i)
  let low := univ.filter fun i => w i ≤ R
  let mid := univ.filter fun i => R < w i ∧ w i ≤ w i₀+B+2
  let high := univ.filter fun i => w i₀+B+2 < w i
  let tail := univ.filter fun i => R < w i
  let z : ℤ := ∑ i ∈ low, c i * 2^(R-w i)
  have hlow : ∑ i ∈ low, v i = q R * z := by
    dsimp [z]
    push_cast
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    have hw : w i ≤ R := (mem_filter.1 hi).2
    dsimp [v]
    rw [← q_twopow (w i) R hw]
    ring
  have htail : ∑ i ∈ tail, v i = (∑ i ∈ mid, v i) + ∑ i ∈ high, v i := by
    rw [← sum_filter_add_sum_filter_not tail (fun i => w i ≤ w i₀+B+2)]
    congr 1 <;> congr 1 <;> ext i <;> simp [tail, mid, high]
    omega
  have htot : ∑ i, v i = q R * z + ∑ i ∈ tail, v i := by
    rw [← sum_filter_add_sum_filter_not univ (fun i => w i ≤ R) v, hlow]
    simp [tail, not_le]
  have htail_small : |∑ i ∈ tail, v i| ≤ q R / 4 := by
    calc
      _ ≤ (∑ i, (c i).natAbs : ℕ) * q (R+(B+2)) :=
        tail_bound c w tail _ fun i hm => by
          have : R < w i := (mem_filter.1 hm).2
          have := hzero i this
          omega
      _ ≤ q R / 4 := by
        rw [q_add]
        have hh : ((∑ i, (c i).natAbs : ℕ) : ℝ) ≤ B := by exact_mod_cast hB
        calc
          _ ≤ (B:ℝ) * (q R * q (B+2)) :=
            mul_le_mul_of_nonneg_right hh (mul_nonneg (q_pos _).le (q_pos _).le)
          _ ≤ _ := by
            have H := mul_le_mul_of_nonneg_left (quarter B) (q_pos R).le
            linarith only [H]
  have hhigh : |∑ i ∈ high, v i| ≤ q (w i₀) / 4 := by
    calc
      _ ≤ (∑ i, (c i).natAbs : ℕ) * q (w i₀+(B+2)) :=
        tail_bound c w high _ fun i hm => by
          have : w i₀+B+2 < w i := (mem_filter.1 hm).2
          omega
      _ ≤ q (w i₀) / 4 := by
        rw [q_add]
        have hh : ((∑ i, (c i).natAbs : ℕ) : ℝ) ≤ B := by exact_mod_cast hB
        calc
          _ ≤ (B:ℝ) * (q (w i₀) * q (B+2)) :=
            mul_le_mul_of_nonneg_right hh (mul_nonneg (q_pos _).le (q_pos _).le)
          _ ≤ _ := by
            have H := mul_le_mul_of_nonneg_left (quarter B) (q_pos (w i₀)).le
            linarith only [H]
  have hmid : q (w i₀) ≤ ∑ i ∈ mid, v i := by
    have hmem : i₀ ∈ mid := mem_filter.2 ⟨mem_univ _, hRi, by omega⟩
    have hc : (1 : ℝ) ≤ c i₀ := by exact_mod_cast (show (1:ℤ) ≤ c i₀ by omega)
    calc
      q (w i₀) ≤ v i₀ := by dsimp [v]; nlinarith [q_pos (w i₀)]
      _ ≤ _ := single_le_sum (f := v) (fun i hm => by
        have hh : R < w i ∧ w i ≤ w i₀+B+2 := (mem_filter.1 hm).2
        have hc' : (0 : ℝ) ≤ c i := by exact_mod_cast hgap i hh.1 hh.2
        dsimp [v]
        exact mul_nonneg hc' (q_pos _).le) hmem
  have herr : |∑ i, v i| ≤ q (w i₀) / 4 := by
    calc
      _ ≤ (L:ℝ) * q N := hV
      _ ≤ (B:ℝ) * q (w i₀+(B+2)) := mul_le_mul
        (by exact_mod_cast hL) (q_anti (by omega)) (q_pos _).le (by positivity)
      _ ≤ _ := by rw [q_add]; nlinarith [quarter B, q_pos (w i₀)]
  have hz : z = 0 := by
    have hbound := (abs_add_le (∑ i, v i) (-(∑ i ∈ tail, v i))).trans
      (add_le_add herr (show |-(∑ i ∈ tail, v i)| ≤ q R/4 by rwa [abs_neg]))
    have hq := q_anti (show R ≤ w i₀ by omega)
    rw [htot, add_neg_cancel_right, abs_mul, abs_of_pos (q_pos R)] at hbound
    have hh : |(z : ℝ)| < 1 := by
      by_contra! hh
      nlinarith [q_pos R]
    have hh' : |z| < 1 := by exact_mod_cast hh
    have hh'' := abs_lt.mp hh'
    omega
  rw [hz, Int.cast_zero, mul_zero, zero_add, htail] at htot
  linarith [(abs_le.1 hhigh).1, (abs_le.1 herr).2, q_pos (w i₀)]


private def wgt (n : ℕ → ℕ) (k : ℕ) : Option (Fin k) → ℕ :=
  fun u => u.elim 0 (fun i => n i)

private def xk (n : ℕ → ℕ) (k : ℕ) : ℝ :=
  1 + ∑ i ∈ range k, q (n i)

private lemma xk_sum (n : ℕ → ℕ) (k : ℕ) :
    xk n k = ∑ i, q (wgt n k i) := by
  simp [xk, wgt, Fintype.sum_option, q]
  exact (Fin.sum_univ_eq_sum_range (fun i => ((2:ℝ)^n i)⁻¹) k).symm

private lemma xk_strict (n : ℕ → ℕ) : StrictMono (xk n) := by
  apply strictMono_nat_of_lt_succ
  intro k
  simp only [xk, sum_range_succ]
  linarith [q_pos (n k)]

private lemma q_summable : Summable q := by
  unfold q
  exact summable_geometric_of_norm_lt_one (by norm_num)

private lemma q_tsum : ∑' i, q i = 2 := by
  unfold q
  rw [tsum_geometric_of_norm_lt_one (by norm_num)]
  norm_num

private lemma xk_approx (n : ℕ → ℕ) (hn : StrictMono n) (k : ℕ) :
    let x := 1 + ∑' i, q (n i)
    xk n k ∈ Set.Icc (0 : ℝ) 3 ∧ x ∈ Set.Icc (0 : ℝ) 3 ∧
      |xk n k - x| ≤ 2*q (n k) := by
  dsimp
  have hs : Summable (q ∘ n) := q_summable.comp_injective hn.injective
  have htail : Summable (fun i => q (n (i+k))) :=
    hs.comp_injective (fun i j hij => Nat.add_right_cancel hij)
  have hnstep : ∀ i, n k + i ≤ n (i+k) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hk := hn (show i+k < (i+1)+k by omega)
      omega
  have htail_ge : 0 ≤ ∑' i, q (n (i+k)) := tsum_nonneg fun _ => (q_pos _).le
  have htail_le : ∑' i, q (n (i+k)) ≤ 2*q (n k) := by
    calc
      _ ≤ ∑' i, q (n k) * q i := htail.tsum_le_tsum
        (fun i => (q_anti (hnstep i)).trans_eq (q_add _ _))
        (q_summable.mul_left _)
      _ = _ := by rw [tsum_mul_left, q_tsum, mul_comm]
  have heq : ∑ i ∈ range k, q (n i) + ∑' i, q (n (i+k)) = ∑' i, q (n i) :=
    hs.sum_add_tsum_nat_add k
  have hsum_ge : 0 ≤ ∑ i ∈ range k, q (n i) := sum_nonneg fun i _ => (q_pos _).le
  have hsum_le : ∑' i, q (n i) ≤ 2 := by
    rw [← q_tsum]
    exact hs.tsum_le_tsum (fun i => q_anti (hn.id_le i)) q_summable
  have habs : xk n k - (1 + ∑' i, q (n i)) ≤ 0 := by unfold xk; linarith
  refine ⟨⟨by unfold xk; linarith, by unfold xk; linarith⟩,
    ⟨by linarith, by linarith⟩, ?_⟩
  rw [abs_of_nonpos habs]
  unfold xk
  linarith

private lemma poly_error (P : ℤ[X]) (n : ℕ → ℕ) (hn : StrictMono n)
    (hP : aeval (1 + ∑' i, q (n i)) P = (0:ℝ)) :
    ∃ L : ℕ, ∀ k, |aeval (xk n k) P| ≤ L * q (n k) := by
  obtain ⟨K, hK⟩ := (Polynomial.contDiff_aeval (𝕜 := ℝ) P 1).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_Icc (0:ℝ) 3) isCompact_Icc
  obtain ⟨L, hL⟩ := exists_nat_gt (2 * (K:ℝ))
  refine ⟨L, fun k => ?_⟩
  obtain ⟨h₁,h₂,h₃⟩ := xk_approx n hn k
  have hh := hK.dist_le_mul _ h₁ _ h₂
  rw [Real.dist_eq, Real.dist_eq, hP, sub_zero] at hh
  exact hh.trans <| (mul_le_mul_of_nonneg_left h₃ K.coe_nonneg).trans <| by
    rw [← mul_assoc, mul_comm (K:ℝ) 2]
    exact mul_le_mul_of_nonneg_right hL.le (q_pos _).le

private def coeffIndex (D k : ℕ) := Σ d : Fin (D+1), Fin d.val → Option (Fin k)

private instance (D k : ℕ) : Fintype (coeffIndex D k) :=
  inferInstanceAs (Fintype (Σ d : Fin (D+1), Fin d.val → Option (Fin k)))

private def wt {D k : ℕ} (n : ℕ → ℕ) (u : coeffIndex D k) :=
  ∑ i, wgt n k (u.2 i)

private def cf {D k : ℕ} (P : ℤ[X]) (u : coeffIndex D k) :=
  P.coeff u.1.val

private lemma sum_q_prod {m : ℕ} (f : Fin m → ℕ) : q (∑ i, f i) = ∏ i, q (f i) := by
  unfold q
  exact (prod_pow_eq_pow_sum univ f _).symm

private lemma eval_terms (P : ℤ[X]) (n : ℕ → ℕ) (k : ℕ) :
    aeval (xk n k) P =
      ∑ u : coeffIndex P.natDegree k, (cf P u : ℝ) * q (wt n u) := by
  rw [Polynomial.aeval_eq_sum_range]
  rw [← Fin.sum_univ_eq_sum_range]
  change _ = ∑ u : (Σ d : Fin (P.natDegree+1), Fin d.val → Option (Fin k)),
    (P.coeff u.1.val : ℝ) * q (∑ i, wgt n k (u.2 i))
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro d hd
  rw [xk_sum, Fintype.sum_pow, zsmul_eq_mul, mul_sum]
  apply sum_congr rfl
  intro t ht
  rw [sum_q_prod]

private lemma poly_eventually_nonzero (n : ℕ → ℕ) (P : ℤ[X]) (hP : P ≠ 0) :
    ∀ᶠ k in atTop, aeval (xk n k) P ≠ (0:ℝ) := by
  let Q := P.map (algebraMap ℤ ℝ)
  have hQ : Q ≠ 0 := (Polynomial.map_ne_zero_iff (Int.cast_injective (α := ℝ))).2 hP
  have hf : Set.Finite {k | aeval (xk n k) P = (0:ℝ)} := by
    have hh := (Polynomial.finite_setOfPred_isRoot hQ).preimage (xk_strict n).injective.injOn
    convert hh using 1
    ext k
    simp [Q, Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval_map]
  exact atTop_le_cofinite hf.eventually_cofinite_notMem

private lemma exponent_bound (n : ℕ → ℕ) (hn : StrictMono n) (P : ℤ[X])
    (hP : P ≠ 0) (L : ℕ) (hL : ∀ k, |aeval (xk n k) P| ≤ L * q (n k)) :
    ∃ k₀, ∀ k ≥ k₀, n (k+1) ≤ P.natDegree * n k + L := by
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (poly_eventually_nonzero n P hP)
  refine ⟨k₀, fun k hk => ?_⟩
  let D := P.natDegree
  have hw (u : coeffIndex D (k+1)) : wt n u ≤ D * n k := by
    have hh (i : Fin u.1.val) : wgt n (k+1) (u.2 i) ≤ n k := by
      cases h : u.2 i with
      | none => simp [wgt]
      | some j =>
        have hj : j.val ≤ k := by have := j.isLt; omega
        simpa [wgt,h] using hn.monotone hj
    calc
      wt n u ≤ ∑ _ : Fin u.1.val, n k := sum_le_sum fun i _ => hh i
      _ = u.1.val * n k := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (by have := u.1.isLt; omega)
  obtain ⟨z,hz⟩ := exists_scaled_integer (cf P) (wt n) (D*n k) hw
  rw [← eval_terms] at hz
  have hne : z ≠ 0 := by
    intro h
    exact hk₀ (k+1) (by omega) (by simpa [h] using hz)
  have habs : (1:ℝ) ≤ |(z:ℝ)| := by
    have hz' := abs_pos.mpr hne
    exact_mod_cast (show (1:ℤ) ≤ |z| by omega)
  have hu := hL (k+1)
  rw [hz, abs_mul, abs_of_pos (q_pos _)] at hu
  have hq : q (D*n k) ≤ (L:ℝ)*q (n (k+1)) :=
    (le_mul_of_one_le_right (q_pos _).le habs).trans hu
  by_contra! h
  have hpow : q (D*n k)*q L ≥ q (n (k+1)) := by
    rw [← q_add]
    exact q_anti h.le
  have htwo : (L:ℝ)*q L < 1 := by
    have hh : (L:ℝ) < 2^L := by exact_mod_cast L.lt_two_pow_self
    have h' := mul_lt_mul_of_pos_right hh (q_pos L)
    have hq₀ := q_twopow 0 L (Nat.zero_le _)
    rw [Nat.sub_zero, show q 0 = 1 by simp [q]] at hq₀
    rwa [mul_comm (2^L) (q L), hq₀] at h'
  have h' := mul_le_mul_of_nonneg_left hpow (show (0:ℝ) ≤ L by positivity)
  exact (calc
    q (D*n k) ≤ (L:ℝ)*q (n (k+1)) := hq
    _ ≤ q (D*n k) * ((L:ℝ)*q L) := by nlinarith only [h']
    _ < q (D*n k) := mul_lt_of_lt_one_right (q_pos _) htwo
  ).false

private lemma nearby_digit (n : ℕ → ℕ) (hn : StrictMono n) {D L k₀ : ℕ}
    (hb : ∀ k ≥ k₀, n (k+1) ≤ D*n k+L) (x : ℕ) (hx : n k₀ ≤ x) :
    ∃ i, x < n i ∧ n i ≤ D*x+L := by
  let hE : ∃ i, x < n i := ⟨x+1, (Nat.lt_succ_self _).trans_le (hn.id_le _)⟩
  let i := Nat.find hE
  have hi : x < n i := Nat.find_spec hE
  have hk : k₀ < i := by
    by_contra! hh
    exact (hi.trans_le ((hn.monotone hh).trans hx)).false
  have hp : n (i-1) ≤ x := Nat.le_of_not_gt (Nat.find_min hE (show i-1 < i by omega))
  have hh := hb (i-1) (by omega)
  rw [show i-1+1=i by omega] at hh
  exact ⟨i, hi, hh.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hp) _)⟩


private lemma card_coeffIndex (D k : ℕ) :
    Fintype.card (coeffIndex D k) ≤ (D+1)*(k+1)^D := by
  change Fintype.card (Σ d : Fin (D+1), Fin d.val → Option (Fin k)) ≤ _
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : Fin (D+1), (k+1)^D := by
      apply sum_le_sum
      intro d hd
      simp only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin]
      exact Nat.pow_le_pow_right (by omega) (by have := d.isLt; omega)
    _ = _ := by simp

private lemma pad_digits {α : Type*} (f : α → ℕ) (z : α) (hz : f z = 0) {d e : ℕ}
    (h : d ≤ e) (u : Fin d → α) :
    ∃ v : Fin e → α, ∑ i, f (v i) = ∑ i, f (u i) := by
  induction e with
  | zero =>
    have : d = 0 := by omega
    subst d
    exact ⟨u, rfl⟩
  | succ e ih =>
    by_cases he : d = e+1
    · subst d
      exact ⟨u, rfl⟩
    obtain ⟨v,hv⟩ := ih (by omega)
    refine ⟨Fin.snoc v z, ?_⟩
    simpa [Fin.sum_univ_castSucc, hz] using hv

private lemma cutoff_bound (C D L Q S : ℕ) (hS : 1 ≤ S) :
    let B := C*S
    let H := (B+2)^2 + Q + 1
    let J := D*H+L
    let M := J+B+2
    B*M+1+M ≤ ((C+1)*(D*((C+2)^2+Q+1)+L+C+2)+1)*S^3 := by
  dsimp
  let U := (C+2)^2+Q+1
  let V := D*U+L+C+2
  have hB : C*S+2 ≤ (C+2)*S := by nlinarith
  have hS2 : 1 ≤ S^2 := Nat.one_le_pow _ _ hS
  have hS12 : S ≤ S^2 := by nlinarith
  have hH : (C*S+2)^2+Q+1 ≤ U*S^2 := by
    have hh := Nat.pow_le_pow_left hB 2
    rw [mul_pow] at hh
    dsimp [U]
    nlinarith
  have hM : D*((C*S+2)^2+Q+1)+L+C*S+2 ≤ V*S^2 := by
    have hh := Nat.mul_le_mul_left D hH
    have hh' := Nat.mul_le_mul_left C hS12
    dsimp [V]
    nlinarith
  have hcs : C*S+1 ≤ (C+1)*S := by nlinarith
  have hfinal := Nat.mul_le_mul hcs hM
  have hS3 : 1 ≤ S^3 := Nat.one_le_pow _ _ hS
  dsimp [V,U] at hfinal
  nlinarith

private lemma large_exponent {n : ℕ → ℕ}
    (h : ∀ t ≥ (1 : ℝ),
      atTop.limsup (fun k => (n k / (k.succ : ℝ)^t).toEReal) = ⊤)
    (A t : ℕ) (ht : 1 ≤ t) : ∃ k, A*(k+1)^t ≤ n k := by
  have ht' : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  have hf : ∃ᶠ k in atTop, ((A:ℝ):EReal) <
      (n k / (k.succ:ℝ)^(t:ℝ)).toEReal := by
    apply frequently_lt_of_lt_limsup (by isBoundedDefault)
    rw [h t ht']
    exact EReal.coe_lt_top _
  obtain ⟨k,hk⟩ := hf.exists
  have hh : (A:ℝ) < n k / (k.succ:ℝ)^(t:ℝ) := EReal.coe_lt_coe_iff.1 hk
  rw [Real.rpow_natCast, lt_div_iff₀ (by positivity)] at hh
  exact ⟨k, (by exact_mod_cast hh : A*(k+1)^t < n k).le⟩

private lemma stage (n : ℕ → ℕ) (hn : StrictMono n) (P : ℤ[X])
    (hD : 0 < P.natDegree) (hlead : 0 < P.leadingCoeff)
    (L k₀ : ℕ) (hL : ∀ k, |aeval (xk n k) P| ≤ L*q (n k))
    (hb : ∀ k ≥ k₀, n (k+1) ≤ P.natDegree*n k+L)
    (growth : ∀ A t : ℕ, 1 ≤ t → ∃ k, A*(k+1)^t ≤ n k) : False := by
  classical
  let D := P.natDegree
  let U := ∑ d : Fin (D+1), (P.coeff d.val).natAbs
  let C := (D+1)*(U+1)+L
  let Q := n k₀
  let A := (C+1)*(D*((C+2)^2+Q+1)+L+C+2)+1
  obtain ⟨k,hk⟩ := growth A (D*3) (by dsimp [D]; omega)
  let S := (k+1)^D
  let B := C*S
  let H := (B+2)^2+Q+1
  let J := D*H+L
  let M := J+B+2
  let W := B*M+1
  have hS : 1 ≤ S := by dsimp [S]; exact Nat.one_le_pow _ _ (by omega)
  have hN : W+M ≤ n k := by
    apply (cutoff_bound C D L Q S hS).trans
    simpa only [A,S,pow_mul] using hk
  have hcard : Fintype.card (coeffIndex D k) ≤ B := by
    apply (card_coeffIndex D k).trans
    change (D+1)*S ≤ C*S
    apply Nat.mul_le_mul_right
    dsimp [C]
    nlinarith
  have hLC : L ≤ B := by
    apply (show L ≤ C by dsimp [C]; omega).trans
    simpa [B] using Nat.mul_le_mul_left C hS
  have hBBC : (∑ i : coeffIndex D k, (cf P i).natAbs) ≤ B := by
    calc
      _ ≤ ∑ _ : coeffIndex D k, U := by
        apply sum_le_sum
        intro i hi
        exact single_le_sum (f := fun d : Fin (D+1) => (P.coeff d.val).natAbs)
          (fun _ _ => Nat.zero_le _) (mem_univ i.1)
      _ = Fintype.card (coeffIndex D k)*U := by simp
      _ ≤ ((D+1)*S)*U := Nat.mul_le_mul_right _ (card_coeffIndex D k)
      _ ≤ B := by dsimp [B,C]; nlinarith
  let low : Finset ℕ := univ.image fun t : Fin (D-1) → Option (Fin k) =>
    ∑ i, wgt n k (t i)
  have hlcard : low.card ≤ B := by
    change (univ.image _).card ≤ _
    calc
      _ ≤ (univ : Finset (Fin (D-1) → Option (Fin k))).card := card_image_le
      _ = (k+1)^(D-1) := by simp
      _ ≤ S := Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
      _ ≤ B := by
        have : 1 ≤ C := by dsimp [C]; nlinarith
        dsimp [B]
        simpa using Nat.mul_le_mul_right S this
  have hlzero : 0 ∈ low := mem_image.2 ⟨fun _ => none, mem_univ _, by simp [wgt]⟩
  obtain ⟨r₀,hr₀,havo⟩ := exists_avoiding 0 W M
    (show low.card*M < W by
      have hh := Nat.mul_le_mul_right M hlcard
      dsimp [W]
      omega)
  have hr : r₀ < W := by simpa using (mem_Ico.1 hr₀).2
  let pref := low.filter (fun a => a ≤ r₀)
  have hne : pref.Nonempty := ⟨0,mem_filter.2 ⟨hlzero,Nat.zero_le _⟩⟩
  let a := pref.max' hne
  have ha : a ∈ low ∧ a ≤ r₀ := mem_filter.1 (max'_mem _ _)
  obtain ⟨j,hj,hj'⟩ := nearby_digit n hn hb H (show Q ≤ H by dsimp [H]; omega)
  have hnk : n j < n k := by
    change n j ≤ J at hj'
    dsimp [M] at hN
    omega
  have hjk : j < k := hn.lt_iff_lt.1 hnk
  let all : Finset ℕ := univ.image (wt n : coeffIndex D k → ℕ)
  have hacard : all.card ≤ B := (card_image_le.trans_eq card_univ).trans hcard
  obtain ⟨R,hRm,havoid⟩ := exists_avoiding a (n j) (B+2)
    (show all.card*(B+2) < n j by
      have hh := Nat.mul_le_mul_right (B+2) hacard
      dsimp [H] at hj
      nlinarith)
  have hR := mem_Ico.1 hRm
  have hnlow (x : ℕ) (hx : x ∈ low) (hx' : a < x) : r₀+M < x := by
    by_cases hxr : x ≤ r₀
    · have hh : x ≤ a := le_max' _ _ (mem_filter.2 ⟨hx,hxr⟩)
      omega
    exact (havo x hx |> not_and.1) (by omega) |> Nat.lt_of_not_ge
  obtain ⟨t,_,ht⟩ := mem_image.1 ha.1
  have hD' : D-1+1 = D := by dsimp [D]; omega
  let t' : Fin (D-1+1) → Option (Fin k) :=
    Fin.snoc t (some ⟨j,hjk⟩)
  let i₀ : coeffIndex D k :=
    ⟨Fin.last D, fun i => t' (i.cast hD'.symm)⟩
  have hiw : wt n i₀ = a+n j := by
    change (∑ i : Fin D, wgt n k (t' (i.cast hD'.symm))) = _
    calc
      _ = ∑ i : Fin (D-1+1), wgt n k (t' i) :=
        (Fin.castOrderIso hD'.symm).toEquiv.sum_comp _
      _ = _ := by
        simpa [t', Fin.sum_univ_castSucc,wgt] using congrArg (·+n j) ht
  have hci : 0 < cf P i₀ := hlead
  refine finite_carry (cf P) (wt n) B L (n k) R i₀ hBBC hLC ?_ ?_ ?_ ?_ hci ?_
  · rw [← eval_terms]
    exact hL k
  · intro i hi
    have hh := havoid (wt n i) (mem_image.2 ⟨i,mem_univ _,rfl⟩)
    omega
  · omega
  · have : n j ≤ J := hj'
    rw [hiw]
    dsimp [M] at hN
    omega
  · intro i hi hwi
    by_cases hd : i.1.val = D
    · change 0 ≤ P.coeff i.1.val
      rw [hd]
      exact hlead.le
    have hd' : i.1.val ≤ D-1 := by have := i.1.isLt; omega
    obtain ⟨v,hv⟩ := pad_digits (wgt n k) none rfl hd' i.2
    have hh : wt n i ∈ low := mem_image.2 ⟨v,mem_univ _,hv⟩
    have hlarge := hnlow (wt n i) hh (by omega)
    have : n j ≤ J := hj'
    rw [hiw] at hwi
    dsimp [M] at hlarge
    omega

private lemma positive_polynomial (x : ℝ) (hx : IsAlgebraic ℤ x) :
    ∃ P : ℤ[X], P ≠ 0 ∧ 0 < P.natDegree ∧ 0 < P.leadingCoeff ∧ aeval x P = 0 := by
  obtain ⟨P,hP,he⟩ := hx
  have hd : 0 < P.natDegree := by
    by_contra! h
    have heq := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero h)
    rw [heq] at he
    have hcoeff : P.coeff 0 = 0 := by simpa using he
    exact hP (heq.trans (by rw [hcoeff,C_0]))
  have hlead := leadingCoeff_ne_zero.mpr hP
  by_cases h : 0 < P.leadingCoeff
  · exact ⟨P,hP,hd,h,he⟩
  exact ⟨-P, neg_ne_zero.mpr hP, by simpa using hd, by simpa using (show P.leadingCoeff < 0 by omega),
    by simp [he]⟩

end

/-- The sparse-digit argument uses finite dyadic approximations and the sign
of the leading term, following the carry method of Bailey, Borwein, Crandall
and Pomerance in [On the binary expansions of algebraic numbers](https://doi.org/10.5802/jtnb.457). -/
theorem solution (n : ℕ → ℕ) (hn : StrictMono n)
    (h : ∀ t ≥ (1 : ℝ), atTop.limsup
      (fun k => (n k / (k.succ : ℝ)^t).toEReal) = ⊤) :
    Transcendental ℚ (∑' k, (1 : ℝ) / 2 ^ n k) := by
  intro hcon
  have hq : (∑' k, q (n k)) = ∑' k, (1:ℝ)/2^n k := by
    simp [q]
  rw [← hq] at hcon
  have hx : IsAlgebraic ℚ (1 + ∑' k, q (n k)) :=
    (isAlgebraic_one (R := ℚ) (A := ℝ)).add hcon
  obtain ⟨P,hP,hD,hlead,he⟩ :=
    positive_polynomial _ ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).2 hx)
  obtain ⟨L,hL⟩ := poly_error P n hn he
  obtain ⟨k₀,hk₀⟩ := exponent_bound n hn P hP L hL
  exact stage n hn P hD hlead L k₀ hL hk₀ (fun A t ht => large_exponent h A t ht)

end OMA247

theorem OMA.solution : type_of% @Erdos247.erdos_247.variants.strong_condition := by
  exact OMA247.solution