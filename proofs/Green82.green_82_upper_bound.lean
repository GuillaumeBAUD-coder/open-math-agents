import FormalConjectures.GreensOpenProblems.«82»
/-! Juškevičius and Sahasrabudhe, Cosine polynomials with few zeros,
Bull. Lond. Math. Soc. 52 (2020), Theorem 1.1, arXiv:2005.01695.

This proof uses the same low-frequency deletion construction.
It bounds zeros on a discrete grid by Rolle and counts occupied cells
using Chebyshev polynomials and the finite Sperner inequality. -/

open Finset Filter Real Set
open scoped BigOperators ContDiff

namespace Green82Proof

noncomputable def cosineSum (s : Finset ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ s, Real.cos ((k : ℝ) * x)

noncomputable def wave (r : ℝ) (x : ℝ) : ℝ := Real.sin (r * x)

noncomputable def correction (s : Finset ℕ) (x : ℝ) : ℝ :=
  (∑ k ∈ s, (wave ((k : ℝ) + 1 / 2) x - wave ((k : ℝ) - 1 / 2) x)) -
    wave (1 / 2) x

theorem wave_diff (r x : ℝ) :
    wave (r + 1 / 2) x - wave (r - 1 / 2) x = 2 * Real.sin (x / 2) * Real.cos (r * x) := by
  unfold wave
  rw [Real.sin_sub_sin]
  congr 1
  · congr 1
    ring
  · congr 1
    ring

theorem correction_eq (s : Finset ℕ) (x : ℝ) :
    correction s x = Real.sin (x / 2) * (2 * cosineSum s x - 1) := by
  unfold correction cosineSum
  simp_rw [wave_diff, ← Finset.mul_sum]
  unfold wave
  rw [show (1 / 2 : ℝ) * x = x / 2 by ring]
  ring

theorem full_sum (n : ℕ) (x : ℝ) :
    2 * Real.sin (x / 2) * cosineSum (Finset.range n) x =
      wave ((n : ℝ) - 1 / 2) x + wave (1 / 2) x := by
  unfold cosineSum
  simp_rw [Finset.mul_sum, ← wave_diff]
  have h := Finset.sum_range_sub
    (fun k : ℕ => wave ((k : ℝ) - 1 / 2) x) n
  simp only [Nat.cast_succ, show ∀ r : ℝ, r + 1 - 1 / 2 = r + 1 / 2 by intro; ring] at h
  rw [h]
  simp [wave, Real.sin_neg]

theorem deleted_sum {s : Finset ℕ} {q : ℕ} (hs : s ⊆ Finset.range q) (x : ℝ) :
    2 * Real.sin (x / 2) * cosineSum (Finset.range q \ s) x =
      wave ((q : ℝ) - 1 / 2) x - correction s x := by
  have hsplit := Finset.sum_sdiff (f := fun k : ℕ => Real.cos ((k : ℝ) * x)) hs
  change cosineSum (Finset.range q \ s) x + cosineSum s x = cosineSum (Finset.range q) x at hsplit
  rw [correction_eq]
  have hfull := full_sum q x
  rw [← hsplit, mul_add] at hfull
  have hw : wave (1 / 2) x = Real.sin (x / 2) := by unfold wave; congr 1; ring
  rw [hw] at hfull
  linarith

theorem smooth_wave (r : ℝ) : ContDiff ℝ ∞ (wave r) := by
  unfold wave
  fun_prop

theorem smooth_correction (s : Finset ℕ) : ContDiff ℝ ∞ (correction s) := by
  unfold correction
  apply ContDiff.sub _ (smooth_wave _)
  exact ContDiff.sum (fun i _ => (smooth_wave _).sub (smooth_wave _))

theorem smooth_finite {f : ℝ → ℝ} (h : ContDiff ℝ ∞ f) (l : ℕ) (x : ℝ) :
    ContDiffAt ℝ l f x :=
  h.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl l)

theorem iterated_wave (r : ℝ) (l : ℕ) (x : ℝ) :
    iteratedDeriv l (wave r) x = r ^ l * iteratedDeriv l Real.sin (r * x) := by
  unfold wave
  exact congrFun (iteratedDeriv_comp_const_mul (n := l) Real.contDiff_sin r) x

theorem iterated_wave_abs {r B : ℝ} (hr : |r| ≤ B) (l : ℕ) (x : ℝ) :
    |iteratedDeriv l (wave r) x| ≤ B ^ l := by
  rw [iterated_wave, abs_mul, abs_pow]
  calc
    |r| ^ l * |iteratedDeriv l Real.sin (r * x)| ≤ |r| ^ l * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_iteratedDeriv_sin_le_one _ _) (by positivity)
    _ ≤ B ^ l := by simpa using pow_le_pow_left₀ (abs_nonneg r) hr l

theorem iterated_correction_abs {s : Finset ℕ} {B : ℝ}
    (hB : (1 / 2 : ℝ) ≤ B) (hs : ∀ k ∈ s, (k : ℝ) + 1 / 2 ≤ B) (l : ℕ) (x : ℝ) :
    |iteratedDeriv l (correction s) x| ≤ (2 * s.card + 1) * B ^ l := by
  unfold correction
  rw [iteratedDeriv_fun_sub, iteratedDeriv_fun_sum]
  · calc
      _ ≤ |∑ i ∈ s, iteratedDeriv l (fun z => wave ((i : ℝ) + 1 / 2) z -
            wave ((i : ℝ) - 1 / 2) z) x| + |iteratedDeriv l (wave (1 / 2)) x| := abs_sub _ _
      _ ≤ (∑ _i ∈ s, (B ^ l + B ^ l)) + B ^ l := by
        apply add_le_add _ (iterated_wave_abs (by simpa using hB) l x)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
        rw [iteratedDeriv_fun_sub]
        · refine (abs_sub _ _).trans (add_le_add (iterated_wave_abs ?_ _ _)
                (iterated_wave_abs ?_ _ _))
          · rw [abs_of_nonneg (by positivity)]
            exact hs i hi
          · apply abs_le.mpr
            constructor <;> linarith [hs i hi, show (0 : ℝ) ≤ i by positivity]
        · exact smooth_finite (smooth_wave _) _ _
        · exact smooth_finite (smooth_wave _) _ _
      _ = _ := by simp; ring
  · intro i _
    exact smooth_finite ((smooth_wave _).sub (smooth_wave _)) _ _
  · exact smooth_finite (ContDiff.sum (fun _ _ => (smooth_wave _).sub (smooth_wave _))) _ _
  · exact smooth_finite (smooth_wave _) _ _

theorem rolle_iterate {a b : ℝ} {l : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (xs : Fin (l + 1) → ℝ) (hm : StrictMono xs)
    (hx : ∀ i, xs i ∈ Icc a b) (hz : ∀ i, f (xs i) = 0) :
    ∃ y ∈ Icc a b, iteratedDeriv l f y = 0 := by
  induction l generalizing f with
  | zero => exact ⟨xs 0, hx 0, by simpa using hz 0⟩
  | succ l ih =>
    have hbetween (i : Fin (l + 1)) : ∃ z ∈ Ioo (xs i.castSucc) (xs i.succ), deriv f z = 0 :=
      exists_deriv_eq_zero (hm (Fin.castSucc_lt_succ (i := i)))
        hf.continuous.continuousOn ((hz _).trans (hz _).symm)
    choose ys hys hyd using hbetween
    have hmono : StrictMono ys := by
      intro i j hij
      exact ((hys i).2.trans_le (hm.monotone
        (show i.succ ≤ j.castSucc from Nat.succ_le_of_lt hij))).trans (hys j).1
    have hmem (i : Fin (l + 1)) : ys i ∈ Icc a b :=
      ⟨(hx i.castSucc).1.trans (hys i).1.le, (hys i).2.le.trans (hx i.succ).2⟩
    obtain ⟨y, hy, hyzero⟩ := ih (f := deriv f) ((contDiff_infty_iff_deriv.mp hf).2) ys hmono hmem hyd
    exact ⟨y, hy, by simpa only [iteratedDeriv_succ'] using hyzero⟩

theorem encard_zeros_le {a b : ℝ} {l : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hnz : ∀ y ∈ Icc a b, iteratedDeriv l f y ≠ 0) :
    ({x ∈ Icc a b | f x = 0} : Set ℝ).encard ≤ l := by
  classical
  by_contra! h
  have hl : ((l + 1 : ℕ) : ℕ∞) ≤ ({x ∈ Icc a b | f x = 0} : Set ℝ).encard := by
    by_contra! nh
    exact (not_le_of_gt h) (ENat.lt_natCast_add_one_iff.mp (by push_cast at nh; exact nh))
  obtain ⟨u, hus, hu⟩ := Set.exists_subset_encard_eq hl
  have huf : u.Finite := Set.encard_lt_top_iff.mp (hu ▸ ENat.natCast_lt_top _)
  have huc : huf.toFinset.card = l + 1 := by
    apply ENat.natCast_inj.mp
    rw [← Set.encard_coe_eq_coe_finsetCard, Set.Finite.coe_toFinset]
    exact hu
  let xs := huf.toFinset.orderEmbOfFin huc
  have hm (i) : xs i ∈ u := huf.mem_toFinset.mp (huf.toFinset.orderEmbOfFin_mem huc i)
  obtain ⟨y, hy, he⟩ := rolle_iterate hf xs xs.strictMono
    (fun i => (hus (hm i)).1) (fun i => (hus (hm i)).2)
  exact hnz y hy he

theorem abs_sin_or_cos (x : ℝ) :
    1 / 2 ≤ |Real.sin x| ∨ 1 / 2 ≤ |Real.cos x| := by
  by_contra! h
  have ha : (Real.sin x) ^ 2 < (1 / 2 : ℝ) ^ 2 :=
    sq_lt_sq.mpr (by simpa using h.1)
  have hb : (Real.cos x) ^ 2 < (1 / 2 : ℝ) ^ 2 :=
    sq_lt_sq.mpr (by simpa using h.2)
  nlinarith only [ha, hb, Real.sin_sq_add_cos_sq x]

theorem short_interval_bound {s : Finset ℕ} {B r a b : ℝ} (hB : 1 / 2 ≤ B)
    (hs : ∀ k ∈ s, (k : ℝ) + 1 / 2 ≤ B) (hBr : B ≤ r)
    (hsmall : (2 * s.card + 1) * B ^ 4 ≤ r ^ 4 / 4)
    (hlen : r * (b - a) ≤ 1 / 8) :
    ({x ∈ Icc a b | wave r x - correction s x = 0} : Set ℝ).encard ≤ 5 := by
  have hr : 0 < r := by linarith
  have hf : ContDiff ℝ ∞ (fun x => wave r x - correction s x) :=
    (smooth_wave r).sub (smooth_correction s)
  have hdist (x) (hx : x ∈ Icc a b) : |r * x - r * a| ≤ 1 / 8 := by
    rw [← mul_sub, abs_of_nonneg (mul_nonneg hr.le (sub_nonneg.mpr hx.1))]
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 _) hr.le).trans hlen
  have h5 : (2 * s.card + 1) * B ^ 5 ≤ r ^ 5 / 4 := by
    calc
      _ = ((2 * s.card + 1) * B ^ 4) * B := by ring
      _ ≤ (r ^ 4 / 4) * r :=
        mul_le_mul hsmall hBr (by linarith) (by positivity)
      _ = _ := by ring
  rcases abs_sin_or_cos (r * a) with ha | ha
  · have hh := encard_zeros_le (l := 4) hf (a := a) (b := b) (show ∀ x ∈ Icc a b,
        iteratedDeriv 4 (fun x => wave r x - correction s x) x ≠ 0 from by
      intro x hx hz
      have hl := (Real.abs_sin_sub_sin_le (r * x) (r * a)).trans (hdist x hx)
      have hsin : 3 / 8 ≤ |Real.sin (r * x)| := by
        have htri := abs_sub_abs_le_abs_sub (Real.sin (r * a)) (Real.sin (r * x))
        rw [abs_sub_comm] at htri
        linarith only [hl, htri, ha]
      rw [iteratedDeriv_fun_sub (smooth_finite (smooth_wave r) _ _)
        (smooth_finite (smooth_correction s) _ _), iterated_wave] at hz
      have hid : iteratedDeriv 4 Real.sin (r * x) = Real.sin (r * x) := by
        simpa only [show 4 = 2 * 2 by rfl, Real.iteratedDeriv_even_sin] using
          (show ((-1 : ℝ → ℝ) ^ 2 * Real.sin) (r * x) = Real.sin (r * x) by norm_num)
      rw [hid, sub_eq_zero] at hz
      have hpow : 0 < r ^ (4 : ℕ) := by positivity
      have hb := (iterated_correction_abs hB hs 4 x).trans hsmall
      rw [← hz, abs_mul, abs_of_nonneg hpow.le] at hb
      have hc := mul_le_mul_of_nonneg_left hsin hpow.le
      linarith only [hb, hc, hpow])
    exact hh.trans (by norm_num)
  · apply encard_zeros_le hf
    intro x hx hz
    have hl := (Real.abs_cos_sub_cos_le (r * x) (r * a)).trans (hdist x hx)
    have hcos : 3 / 8 ≤ |Real.cos (r * x)| := by
      have htri := abs_sub_abs_le_abs_sub (Real.cos (r * a)) (Real.cos (r * x))
      rw [abs_sub_comm] at htri
      linarith only [hl, htri, ha]
    rw [iteratedDeriv_fun_sub (smooth_finite (smooth_wave r) _ _)
      (smooth_finite (smooth_correction s) _ _), iterated_wave] at hz
    have hid : iteratedDeriv 5 Real.sin (r * x) = Real.cos (r * x) := by
      rw [show 5 = 2 * 2 + 1 by rfl, Real.iteratedDeriv_odd_sin]
      norm_num
    rw [hid, sub_eq_zero] at hz
    have hpow : 0 < r ^ (5 : ℕ) := by positivity
    have hb := (iterated_correction_abs hB hs 5 x).trans h5
    rw [← hz, abs_mul, abs_of_nonneg hpow.le] at hb
    have hc := mul_le_mul_of_nonneg_left hcos hpow.le
    linarith only [hb, hc, hpow]

end Green82Proof

open Finset Filter Real Set
open scoped BigOperators

namespace Green82Proof

theorem central_binom_square_bound (k : ℕ) :
    ((Nat.centralBinom k : ℝ) / 4 ^ k) ^ 2 * (k + 1) ≤ 1 := by
  induction k with
  | zero => norm_num [Nat.centralBinom]
  | succ k ih =>
    have hr : ((Nat.centralBinom (k + 1) : ℝ) / 4 ^ (k + 1)) =
        ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) *
          ((Nat.centralBinom k : ℝ) / 4 ^ k) := by
      have h := Nat.succ_mul_centralBinom_succ k
      have h' : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) =
          2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) := by exact_mod_cast h
      rw [pow_succ]
      have hk : (k : ℝ) + 1 ≠ 0 := by positivity
      have h4 : (4 : ℝ) ^ k ≠ 0 := by positivity
      field_simp
      nlinarith only [h']
    have hm : ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) ^ 2 *
        ((k : ℝ) + 1 + 1) ≤ (k : ℝ) + 1 := by
      have hp : 0 < (2 : ℝ) * ((k : ℝ) + 1) := by positivity
      rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (pow_pos hp 2)]
      nlinarith only [show (0 : ℝ) ≤ k by positivity]
    push_cast
    rw [hr, mul_pow, mul_comm (_ ^ 2) (_ ^ 2), mul_assoc]
    exact (mul_le_mul_of_nonneg_left hm (sq_nonneg _)).trans ih

theorem central_binom_bound (k : ℕ) :
    (Nat.centralBinom k : ℝ) ≤ (4 : ℝ) ^ k / Real.sqrt (k + 1) := by
  have hs : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hp : 0 < (4 : ℝ) ^ k := by positivity
  have h := central_binom_square_bound k
  rw [le_div_iff₀ hs]
  have hq : (Nat.centralBinom k : ℝ) * Real.sqrt ((k : ℝ) + 1) / 4 ^ k ≤ 1 := by
    have he : ((Nat.centralBinom k : ℝ) * Real.sqrt ((k : ℝ) + 1) / 4 ^ k) ^ 2 ≤ 1 := by
      rw [mul_div_right_comm, mul_pow, Real.sq_sqrt (by positivity)]
      exact h
    nlinarith only [he, sq_nonneg
      ((Nat.centralBinom k : ℝ) * Real.sqrt ((k : ℝ) + 1) / 4 ^ k - 1)]
  simpa using (div_le_iff₀ hp).mp hq

noncomputable def slot (w : ℕ → ℝ) (L : ℝ) (u : Finset ℕ) : ℕ :=
  ⌊2 * ((∑ i ∈ u, w i) - L)⌋₊

theorem slot_mem {w : ℕ → ℝ} {L U : ℝ} {u : Finset ℕ}
    (h : (∑ i ∈ u, w i) ∈ Icc L U) :
    slot w L u ∈ Finset.range (⌊2 * (U - L)⌋₊ + 1) := by
  apply Finset.mem_range.mpr
  exact Nat.lt_succ_of_le (Nat.floor_mono (by linarith [h.2]))

theorem slot_gap {w : ℕ → ℝ} {L : ℝ} {u v : Finset ℕ}
    (hu : L ≤ ∑ i ∈ u, w i) (_hv : L ≤ ∑ i ∈ v, w i)
    (h : slot w L u = slot w L v) :
    (∑ i ∈ v, w i) - (∑ i ∈ u, w i) < 1 / 2 := by
  have h₁ := Nat.floor_le (show 0 ≤ 2 * ((∑ i ∈ u, w i) - L) by linarith)
  have h₂ := Nat.lt_floor_add_one (2 * ((∑ i ∈ v, w i) - L))
  unfold slot at h
  rw [← h] at h₂
  linarith only [h₁, h₂]

theorem card_interval_subsets {A B : Finset ℕ} (hBA : B ⊆ A) {k : ℕ}
    (hBcard : B.card = 2 * k) (w : ℕ → ℝ) (hpos : ∀ i ∈ B, (1 / 2 : ℝ) ≤ w i)
    (L U : ℝ) :
    (A.powerset.filter (fun s => (∑ i ∈ s, w i) ∈ Icc L U)).card ≤
      Nat.centralBinom k * (2 ^ (A.card - B.card) * (⌊2 * (U - L)⌋₊ + 1)) := by
  classical
  let F := A.powerset.filter (fun s => (∑ i ∈ s, w i) ∈ Icc L U)
  let label (s : Finset ℕ) := (s \ B, slot w L s)
  let P := (A \ B).powerset ×ˢ Finset.range (⌊2 * (U - L)⌋₊ + 1)
  have hmap : ∀ s ∈ F, label s ∈ P := by
    intro s hs
    have hsm := Finset.mem_filter.mp hs
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_powerset.mpr
      (Finset.sdiff_subset_sdiff_left B (Finset.mem_powerset.mp hsm.1)), slot_mem hsm.2⟩
  have hfib (p : Finset ℕ × ℕ) (_hp : p ∈ P) :
      (F.filter fun s => label s = p).card ≤ Nat.centralBinom k := by
    let S := F.filter fun s => label s = p
    let bits (s : Finset ℕ) : Finset {i : ℕ // i ∈ B} := s.subtype (· ∈ B)
    have hbits (s) (i : {i : ℕ // i ∈ B}) : i ∈ bits s ↔ i.val ∈ s := by
      simp [bits]
    have hp' (s) (hs : s ∈ S) : s \ B = p.1 ∧ slot w L s = p.2 := by
      have he := (Finset.mem_filter.mp hs).2
      exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
    have hsub {s t : Finset ℕ} (hs : s ∈ S) (ht : t ∈ S) (h : bits s ⊆ bits t) : s ⊆ t := by
      intro i hi
      by_cases hib : i ∈ B
      · exact (hbits t ⟨i, hib⟩).mp (h ((hbits s ⟨i, hib⟩).mpr hi))
      · have he := (hp' s hs).1.trans (hp' t ht).1.symm
        exact Finset.mem_sdiff.mp (he ▸ Finset.mem_sdiff.mpr ⟨hi, hib⟩) |>.1
    have hbij : Set.InjOn bits (S : Set (Finset ℕ)) := by
      intro s hs t ht h
      exact le_antisymm (hsub hs ht h.le) (hsub ht hs h.ge)
    have hanti : IsAntichain (fun u v : Finset {i : ℕ // i ∈ B} => u ⊆ v)
        (↑(S.image bits) : Set (Finset {i : ℕ // i ∈ B})) := by
      intro u hu v hv hne huv
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
      have hst := hsub hs ht huv
      have hst' : s ≠ t := fun hh => hne (congrArg bits hh)
      have hts : ¬ t ⊆ s := fun h => hst' (le_antisymm hst h)
      simp only [Finset.subset_iff] at hts
      push Not at hts
      obtain ⟨j, hjt, hjs⟩ := hts
      have hdvd : t \ s ⊆ B := by
        intro i hi
        have hi' := Finset.mem_sdiff.mp hi
        by_contra hnot
        have he := (hp' t ht).1.trans (hp' s hs).1.symm
        exact hi'.2 (Finset.mem_sdiff.mp (he ▸ Finset.mem_sdiff.mpr ⟨hi'.1, hnot⟩)).1
      have hle : (1 / 2 : ℝ) ≤ ∑ i ∈ t \ s, w i :=
        (hpos j (hdvd (Finset.mem_sdiff.mpr ⟨hjt, hjs⟩))).trans
          (Finset.single_le_sum (fun i hi => (by norm_num : (0 : ℝ) ≤ 1 / 2).trans
            (hpos i (hdvd hi))) (Finset.mem_sdiff.mpr ⟨hjt, hjs⟩))
      have he := Finset.sum_sdiff (f := w) hst
      have hlo (v) (hv : v ∈ S) : L ≤ ∑ i ∈ v, w i := by
        exact ((Finset.mem_filter.mp ((Finset.mem_filter.mp hv).1)).2).1
      have hg := slot_gap (hlo s hs) (hlo t ht) ((hp' s hs).2.trans (hp' t ht).2.symm)
      linarith only [he, hle, hg]
    have hsper := hanti.sperner
    rw [Finset.card_image_of_injOn hbij, Fintype.card_coe, hBcard,
      show (2 * k) / 2 = k by omega, ← Nat.centralBinom_eq_two_mul_choose] at hsper
    exact hsper
  have h := Finset.card_le_mul_card_image_of_maps_to hmap (Nat.centralBinom k) hfib
  simpa [F, P, Finset.card_product, Finset.card_powerset, Finset.card_sdiff_of_subset hBA] using h

end Green82Proof

open Finset Filter Real Set Polynomial
open scoped BigOperators

namespace Green82Proof

theorem polynomial_zero_encard {s : Set ℝ} (c : ℝ → ℝ) (hc : Set.InjOn c s)
    (P : ℝ[X]) (hP : P ≠ 0) (hz : ∀ x ∈ s, P.eval (c x) = 0) :
    s.encard ≤ P.natDegree := by
  classical
  rw [← hc.encard_image]
  calc
    _ ≤ ((P.roots.toFinset : Finset ℝ) : Set ℝ).encard := by
      apply Set.encard_mono
      rintro _ ⟨x, hx, rfl⟩
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).2 (hz x hx))
    _ ≤ (P.natDegree : ℕ∞) := by
      rw [Set.encard_coe_eq_coe_finsetCard]
      exact_mod_cast (Multiset.toFinset_card_le P.roots).trans (Polynomial.card_roots' P)

theorem cheb_eval (s : Finset ℕ) (x : ℝ) :
    (∑ k ∈ s, Chebyshev.T ℝ (2 * (k : ℤ))).eval (Real.cos (x / 2)) =
      cosineSum s x := by
  rw [Polynomial.eval_finsetSum]
  unfold cosineSum
  apply Finset.sum_congr rfl
  intro k _
  rw [Chebyshev.T_real_cos]
  push_cast
  congr 1
  ring

theorem correction_boundary_encard {s : Finset ℕ} {m : ℕ} (hs : ∀ k ∈ s, k ≤ m) :
    ({x ∈ Icc 0 π | |correction s x| = 1} : Set ℝ).encard ≤ (4 * m + 2 : ℕ) := by
  let T : ℝ[X] := ∑ k ∈ s, Chebyshev.T ℝ (2 * (k : ℤ))
  let U : ℝ[X] := Polynomial.C 2 * T - 1
  let P : ℝ[X] := (1 - X ^ 2) * U ^ 2 - 1
  have hT : T.natDegree ≤ 2 * m := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    rw [Chebyshev.natDegree_T, Int.natAbs_mul]
    simpa using Nat.mul_le_mul_left 2 (hs i hi)
  have hU : U.natDegree ≤ 2 * m := by
    change (Polynomial.C 2 * T - 1).natDegree ≤ 2 * m
    simpa only [max_self] using
      Polynomial.natDegree_sub_le_of_le ((Polynomial.natDegree_C_mul_le 2 T).trans hT)
      (show (1 : ℝ[X]).natDegree ≤ 2 * m by rw [Polynomial.natDegree_one]; exact Nat.zero_le _)
  have hPdeg : P.natDegree ≤ 4 * m + 2 := by
    change ((1 - X ^ 2) * U ^ 2 - 1).natDegree ≤ 4 * m + 2
    have hL : ((1 : ℝ[X]) - X ^ 2).natDegree ≤ 2 :=
      (Polynomial.natDegree_sub_le _ _).trans (by simp)
    have hR := Polynomial.natDegree_pow_le_of_le 2 hU
    have hprod : ((1 - X ^ 2) * U ^ 2).natDegree ≤ 4 * m + 2 :=
      Polynomial.natDegree_mul_le.trans (by omega)
    simpa only [max_self] using Polynomial.natDegree_sub_le_of_le hprod
      (show (1 : ℝ[X]).natDegree ≤ 4 * m + 2 by rw [Polynomial.natDegree_one]; omega)
  have hPne : P ≠ 0 := by
    intro h
    have hEval : P.eval 1 = (-1 : ℝ) := by simp [P]
    rw [h] at hEval
    norm_num at hEval
  have hi : Set.InjOn (fun x : ℝ => Real.cos (x / 2))
      {x ∈ Icc 0 π | |correction s x| = 1} := by
    intro x hx y hy he
    have h1 (z : ℝ) (hz : z ∈ Icc 0 π) : z / 2 ∈ Icc 0 π :=
      ⟨by linarith [hz.1], by linarith [hz.2, pi_pos]⟩
    have he' := Real.strictAntiOn_cos.injOn (h1 x hx.1) (h1 y hy.1) he
    linarith only [he']
  refine (polynomial_zero_encard _ hi P hPne ?_).trans (by exact_mod_cast hPdeg)
  intro x hx
  have hEval : T.eval (Real.cos (x / 2)) = cosineSum s x := cheb_eval s x
  have hSquare := congrArg (fun t : ℝ => t ^ 2) hx.2
  rw [sq_abs, correction_eq, mul_pow, Real.sin_sq] at hSquare
  simpa [P, U, hEval, sub_eq_zero] using hSquare

theorem cosine_zeros_encard {s : Finset ℕ} (hne : s.Nonempty) {m : ℕ}
    (hs : ∀ k ∈ s, k ≤ m) :
    ({x ∈ Icc 0 π | cosineSum s x = 0} : Set ℝ).encard ≤ m := by
  let P : ℝ[X] := ∑ k ∈ s, Chebyshev.T ℝ (k : ℤ)
  have heval (x) : P.eval (Real.cos x) = cosineSum s x := by
    simp [P, cosineSum, Polynomial.eval_finsetSum, Chebyshev.T_real_cos]
  have hpne : P ≠ 0 := by
    intro h
    have he := heval 0
    rw [h] at he
    have hpos := Finset.card_pos.mpr hne
    simp [cosineSum] at he
    have hcard : (0 : ℕ) = s.card := by exact_mod_cast he
    omega
  have hdeg : P.natDegree ≤ m := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    rw [Chebyshev.natDegree_T, Int.natAbs_natCast]
    exact hs k hk
  exact (polynomial_zero_encard _ (Real.strictAntiOn_cos.injOn.mono fun _ h => h.1)
    P hpne (fun x hx => (heval x).trans hx.2)).trans (by exact_mod_cast hdeg)

theorem cosineSum_reflect (s : Finset ℕ) (x : ℝ) :
    cosineSum s (2 * π - x) = cosineSum s x := by
  unfold cosineSum
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_sub, Real.cos_nat_mul_two_pi_sub]

theorem full_period_encard {s : Finset ℕ} {k : ℕ}
    (h : ({x ∈ Icc 0 π | cosineSum s x = 0} : Set ℝ).encard ≤ k) :
    ({x ∈ Set.Ico 0 1 | ∑ i ∈ s, Real.cos (2 * π * (i : ℝ) * x) = 0} : Set ℝ).encard ≤
      (2 * k : ℕ) := by
  let H := {x ∈ Icc 0 π | cosineSum s x = 0}
  let A := {x ∈ Set.Ico (0 : ℝ) 1 | ∑ i ∈ s, Real.cos (2 * π * (i : ℝ) * x) = 0}
  let f (x : ℝ) := 2 * π * x
  let g (x : ℝ) := 2 * π - x
  have hf : Function.Injective f := by
    intro x y he
    have he' : (2 * π) * x = (2 * π) * y := he
    exact mul_left_cancel₀ (by positivity) he'
  have hg : Function.Injective g := by intro x y he; dsimp [g] at he; linarith only [he]
  have hsub : f '' A ⊆ H ∪ g '' H := by
    rintro _ ⟨x, hx, rfl⟩
    have hc : cosineSum s (f x) = 0 := by
      unfold cosineSum f
      simpa only [mul_left_comm, mul_assoc, mul_comm] using hx.2
    have hx' : x ∈ Set.Ico (0 : ℝ) 1 := hx.1
    have h0 : 0 ≤ f x := mul_nonneg (by positivity) hx'.1
    have h1 : f x ≤ 2 * π :=
      calc f x ≤ (2 * π) * 1 := mul_le_mul_of_nonneg_left hx'.2.le (by positivity)
           _ = 2 * π := mul_one _
    by_cases hhalf : f x ≤ π
    · exact Or.inl ⟨⟨h0, hhalf⟩, hc⟩
    · apply Or.inr
      refine ⟨g (f x), ⟨⟨?_, ?_⟩, ?_⟩, by simp [g]⟩
      · dsimp [g]
        linarith only [h1]
      · dsimp [g]
        linarith only [hhalf]
      · simpa only [g, cosineSum_reflect] using hc
  calc
    A.encard = (f '' A).encard := (hf.encard_image _).symm
    _ ≤ (H ∪ g '' H).encard := Set.encard_mono hsub
    _ ≤ H.encard + (g '' H).encard := Set.encard_union_le _ _
    _ ≤ (2 * k : ℕ) := by
      rw [hg.encard_image]
      rw [two_mul, Nat.cast_add]
      exact add_le_add (show H.encard ≤ (k : ℕ∞) from h) h

end Green82Proof

open Finset Filter Real Set
open scoped BigOperators

namespace Green82Proof

def samplePool (k : ℕ) : Finset ℕ := Finset.Icc 1 (16 * k)

theorem sample_count (k : ℕ) : (samplePool k).card = 16 * k := by
  simp [samplePool, Nat.card_Icc]

theorem separated_cosine_coefficients (k : ℕ) (x : ℝ) :
    ∃ s ⊆ samplePool k, s.card = 2 * k ∧
      ((∀ i ∈ s, (1 / 2 : ℝ) ≤ Real.cos ((i : ℝ) * x)) ∨
        (∀ i ∈ s, (1 / 2 : ℝ) ≤ -Real.cos ((i : ℝ) * x))) := by
  classical
  let w (j : ℕ) := Real.cos ((j : ℝ) * x)
  let J := Finset.Icc (4 * k + 1) (8 * k)
  let G := (samplePool k).filter fun j => (1 / 2 : ℝ) ≤ |w j|
  let f (j : ℕ) := if (1 / 2 : ℝ) ≤ |w j| then j else 2 * j
  have hJ : J.card = 4 * k := by simp [J, Nat.card_Icc]; omega
  have hf : Set.InjOn f (J : Set ℕ) := by
    intro i hi j hj h
    have hi' := Finset.mem_Icc.mp hi
    have hj' := Finset.mem_Icc.mp hj
    dsimp [f] at h
    split at h <;> split at h <;> omega
  have hg : J.image f ⊆ G := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    have hj' := Finset.mem_Icc.mp hj
    by_cases hgood : (1 / 2 : ℝ) ≤ |w j|
    · rw [show f j = j from if_pos hgood]
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hgood⟩
    · rw [show f j = 2 * j from if_neg hgood]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      have hsq : w j ^ 2 < (1 / 2 : ℝ) ^ 2 :=
        sq_lt_sq.mpr (by simpa using lt_of_not_ge hgood)
      have hw : w (2 * j) = 2 * (w j) ^ 2 - 1 := by
        unfold w
        rw [show (((2 * j : ℕ) : ℝ) * x) = 2 * ((j : ℝ) * x) by push_cast; ring,
          Real.cos_two_mul]
      have hneg : w (2 * j) < -(1 / 2 : ℝ) := by linarith only [hsq, hw]
      exact (by linarith only [hneg] : (1 / 2 : ℝ) ≤ -w (2 * j)).trans (neg_le_abs _)
  have hsize : 4 * k ≤ G.card := by
    simpa only [Finset.card_image_of_injOn hf, hJ] using Finset.card_le_card hg
  let p (j : ℕ) : Prop := (1 / 2 : ℝ) ≤ w j
  have hpart := Finset.card_filter_add_card_filter_not (s := G) p
  have hchoice : 2 * k ≤ (G.filter p).card ∨ 2 * k ≤ (G.filter (fun j => ¬ p j)).card := by omega
  rcases hchoice with hp | hn
  · obtain ⟨B, hB, hc⟩ := Finset.exists_subset_card_eq hp
    refine ⟨B, hB.trans ((Finset.filter_subset ..).trans (Finset.filter_subset ..)), hc, Or.inl ?_⟩
    intro j hj
    exact (Finset.mem_filter.mp (hB hj)).2
  · obtain ⟨B, hB, hc⟩ := Finset.exists_subset_card_eq hn
    refine ⟨B, hB.trans ((Finset.filter_subset ..).trans (Finset.filter_subset ..)), hc, Or.inr ?_⟩
    intro j hj
    have hSub := Finset.mem_filter.mp (hB hj)
    have habs := (Finset.mem_filter.mp hSub.1).2
    have hnp : ¬ (1 / 2 : ℝ) ≤ w j := hSub.2
    by_cases h0 : 0 ≤ w j
    · rw [abs_of_nonneg h0] at habs
      exact (hnp habs).elim
    · simpa [abs_of_neg (lt_of_not_ge h0)] using habs

theorem correction_band_card {k : ℕ} {x : ℝ} (hx : x ∈ Ioc 0 π) :
    (((samplePool k).powerset.filter (fun s => |correction s x| ≤ 1)).card : ℝ) ≤
      ((2 : ℝ) ^ (16 * k)) * ((2 * π / x + 1) / Real.sqrt (k + 1)) := by
  classical
  obtain ⟨B, hB, hcard, hweights⟩ := separated_cosine_coefficients k x
  let D : ℝ := π / (2 * x)
  have hx0 : 0 < x := hx.1
  have hpos : 0 < D := by dsimp [D]; positivity
  have hsin : x / π ≤ Real.sin (x / 2) := by
    have h := Real.mul_le_sin (show 0 ≤ x / 2 by linarith [hx.1])
      (show x / 2 ≤ π / 2 by linarith [hx.2])
    convert h using 1
    ring
  have hsin0 : 0 ≤ Real.sin (x / 2) := (by positivity : 0 ≤ x / π).trans hsin
  have hband (s : Finset ℕ) (hs : |correction s x| ≤ 1) :
      cosineSum s x ∈ Icc (1 / 2 - D) (1 / 2 + D) := by
    rw [correction_eq, abs_mul, abs_of_nonneg hsin0] at hs
    have hm := (mul_le_mul_of_nonneg_right hsin (abs_nonneg (2 * cosineSum s x - 1))).trans hs
    have hw : |2 * cosineSum s x - 1| ≤ π / x := by
      apply (le_div_iff₀ hx.1).2
      have hm' : x * |2 * cosineSum s x - 1| / π ≤ 1 := by
        simpa only [div_mul_eq_mul_div] using hm
      have hw' := (div_le_iff₀ pi_pos).1 hm'
      simpa [mul_comm] using hw'
    have hw' := abs_le.mp hw
    have he : π / x = 2 * D := by dsimp [D]; ring
    rw [he] at hw'
    exact ⟨by linarith only [hw'.1], by linarith only [hw'.2]⟩
  have hcount : ((samplePool k).powerset.filter (fun s => |correction s x| ≤ 1)).card ≤
      Nat.centralBinom k * (2 ^ (16 * k - 2 * k) * (⌊4 * D⌋₊ + 1)) := by
    rcases hweights with hp | hn
    · have h := card_interval_subsets hB hcard (fun i => Real.cos ((i : ℝ) * x)) hp
        (1 / 2 - D) (1 / 2 + D)
      rw [sample_count, hcard, show 2 * ((1 / 2 + D) - (1 / 2 - D)) = 4 * D by ring] at h
      refine (Finset.card_le_card ?_).trans h
      intro s hs
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1, hband s (Finset.mem_filter.mp hs).2⟩
    · have h := card_interval_subsets hB hcard (fun i => -Real.cos ((i : ℝ) * x)) hn
        (-(1 / 2 + D)) (-(1 / 2 - D))
      rw [sample_count, hcard, show 2 * (-(1 / 2 - D) - -(1 / 2 + D)) = 4 * D by ring] at h
      refine (Finset.card_le_card ?_).trans h
      intro s hs
      have hb := hband s (Finset.mem_filter.mp hs).2
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1, ?_⟩
      rw [Finset.sum_neg_distrib]
      exact ⟨neg_le_neg hb.2, neg_le_neg hb.1⟩
  have hcast : ((((samplePool k).powerset.filter (fun s => |correction s x| ≤ 1)).card : ℕ) : ℝ) ≤
      (Nat.centralBinom k : ℝ) * (2 ^ (16 * k - 2 * k) * ((⌊4 * D⌋₊ : ℕ) + 1)) := by
    exact_mod_cast hcount
  have h4 : 4 * D = 2 * π / x := by unfold D; ring
  have hpow : (4 : ℝ) ^ k * 2 ^ (16 * k - 2 * k) = 2 ^ (16 * k) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  calc
    _ ≤ (Nat.centralBinom k : ℝ) * (2 ^ (16 * k - 2 * k) * ((⌊4 * D⌋₊ : ℕ) + 1)) := hcast
    _ ≤ ((4 : ℝ) ^ k / Real.sqrt (k + 1)) *
          (2 ^ (16 * k - 2 * k) * (4 * D + 1)) := by
      apply mul_le_mul (central_binom_bound k) _ (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (Nat.floor_le (show 0 ≤ 4 * D by positivity)) le_rfl
    _ = _ := by rw [← h4, ← hpow]; ring

end Green82Proof

open Finset Filter Real Set
open scoped BigOperators

namespace Green82Proof

noncomputable def grid (M j : ℕ) : ℝ := π * (j : ℝ) / M

noncomputable def gridGood (s : Finset ℕ) (M : ℕ) : Finset ℕ :=
  open Classical in (Finset.range M).filter (fun j => |correction s (grid M j)| ≤ 1)

noncomputable def gridCrossing (s : Finset ℕ) (M : ℕ) : Finset ℕ :=
  open Classical in (Finset.range M).filter (fun j =>
    ∃ x ∈ Ioc (grid M j) (grid M (j + 1)), |correction s x| = 1)

theorem grid_strictMono {M : ℕ} (hM : 0 < M) : StrictMono (grid M) := by
  intro i j hij
  unfold grid
  gcongr

theorem grid_zero (M : ℕ) : grid M 0 = 0 := by simp [grid]

theorem grid_end {M : ℕ} (hM : 0 < M) : grid M M = π := by
  unfold grid
  exact mul_div_cancel_right₀ _ (by positivity)

theorem grid_length (M j : ℕ) : grid M (j + 1) - grid M j = π / M := by
  unfold grid
  push_cast
  ring

theorem grid_crossing_card {s : Finset ℕ} {m M : ℕ} (hM : 0 < M)
    (hs : ∀ u ∈ s, u ≤ m) :
    (gridCrossing s M).card ≤ 4 * m + 2 := by
  classical
  let C := gridCrossing s M
  have hw (j) (hj : j ∈ C) :
      ∃ x ∈ Ioc (grid M j) (grid M (j + 1)), |correction s x| = 1 :=
    (Finset.mem_filter.mp hj).2
  let wit (j : ℕ) : ℝ := if h : j ∈ C then Classical.choose (hw j h) else 0
  have hv (j) (hj : j ∈ C) :
      wit j ∈ Ioc (grid M j) (grid M (j + 1)) ∧ |correction s (wit j)| = 1 := by
    simpa only [wit, dif_pos hj] using Classical.choose_spec (hw j hj)
  have hmap : Set.MapsTo wit (C : Set ℕ) {x ∈ Icc 0 π | |correction s x| = 1} := by
    intro j hj
    have hval := hv j hj
    have hM' := Nat.succ_le_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
    have h0 : 0 ≤ grid M j := by unfold grid; positivity
    have h1 : grid M (j + 1) ≤ π := by
      rw [← grid_end hM]
      exact (grid_strictMono hM).monotone hM'
    exact ⟨⟨h0.trans hval.1.1.le, hval.1.2.trans h1⟩, hval.2⟩
  have hinj : Set.InjOn wit (C : Set ℕ) := by
    intro i hi j hj he
    rcases lt_trichotomy i j with h | h | h
    · have hle := (grid_strictMono hM).monotone (Nat.succ_le_of_lt h)
      have hh := ((hv i hi).1.2.trans hle).trans_lt (hv j hj).1.1
      exact False.elim (hh.ne he)
    · exact h
    · have hle := (grid_strictMono hM).monotone (Nat.succ_le_of_lt h)
      have hh := ((hv j hj).1.2.trans hle).trans_lt (hv i hi).1.1
      exact False.elim (hh.ne he.symm)
  have h := (Set.encard_le_encard_of_injOn hmap hinj).trans (correction_boundary_encard hs)
  rw [Set.encard_coe_eq_coe_finsetCard] at h
  exact_mod_cast h

theorem cell_flag {s : Finset ℕ} {M j : ℕ} {x : ℝ} (hj : j ∈ Finset.range M)
    (hx : x ∈ Ioc (grid M j) (grid M (j + 1))) (hc : |correction s x| ≤ 1) :
    j ∈ gridGood s M ∪ gridCrossing s M := by
  classical
  by_cases h : |correction s (grid M j)| ≤ 1
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hj, h⟩)
  · apply Finset.mem_union_right _
    apply Finset.mem_filter.mpr
    refine ⟨hj, ?_⟩
    have hcont : Continuous (fun y => |correction s y|) :=
      (smooth_correction s).continuous.abs
    have hrange := intermediate_value_Icc' hx.1.le hcont.continuousOn
      (show (1 : ℝ) ∈ Icc |correction s x| |correction s (grid M j)| from
        ⟨hc, (lt_of_not_ge h).le⟩)
    obtain ⟨y, hy, hval⟩ := hrange
    have hne : grid M j ≠ y := by
      intro he
      apply h
      simpa [← he, hval] using hval.le
    exact ⟨y, ⟨hy.1.lt_of_ne hne, hy.2.trans hx.2⟩, hval⟩

theorem half_period_grid_encard {s : Finset ℕ} {q m M : ℕ}
    (hM : 0 < M) (hs : s ⊆ Finset.range q) (hN : 0 < (Finset.range q \ s).card)
    (hm : ∀ i ∈ s, i ≤ m)
    (hBr : (m : ℝ) + 1 ≤ (q : ℝ) - 1 / 2)
    (hsmall : (2 * s.card + 1) * ((m : ℝ) + 1) ^ 4 ≤ ((q : ℝ) - 1 / 2) ^ 4 / 4)
    (hlen : ((q : ℝ) - 1 / 2) * (π / (M : ℝ)) ≤ 1 / 8) :
    ({x ∈ Icc 0 π | cosineSum (Finset.range q \ s) x = 0} : Set ℝ).encard ≤
      (5 * ((gridGood s M).card + (4 * m + 2)) : ℕ) := by
  classical
  let r : ℝ := (q : ℝ) - 1 / 2
  let C := gridGood s M ∪ gridCrossing s M
  let R (j : ℕ) := {x ∈ Ioc (grid M j) (grid M (j + 1)) | wave r x - correction s x = 0}
  have hcover : {x ∈ Icc 0 π | cosineSum (Finset.range q \ s) x = 0} ⊆ ⋃ j ∈ C, R j := by
    intro x hx
    have hx0 : 0 < x := by
      by_contra! h
      have he : x = 0 := le_antisymm h hx.1.1
      have hz := hx.2
      simp only [he, cosineSum, mul_zero, Real.cos_zero, Finset.sum_const, nsmul_eq_mul,
        mul_one] at hz
      have hcard : (Finset.range q \ s).card = 0 := by exact_mod_cast hz
      omega
    have hx' : x ∈ Ioc (grid M 0) (grid M M) := by
      rw [grid_zero, grid_end hM]
      exact ⟨hx0, hx.1.2⟩
    obtain ⟨j, hj, hjx⟩ := Set.mem_iUnion₂.mp (Ioc_subset_biUnion_Ioc M (grid M) hx')
    have hz := deleted_sum hs x
    rw [hx.2, mul_zero] at hz
    have hp : |correction s x| ≤ 1 := by
      rw [← sub_eq_zero.mp hz.symm]
      exact Real.abs_sin_le_one _
    exact Set.mem_iUnion₂.mpr ⟨j, cell_flag hj hjx hp, hjx, hz.symm⟩
  have hcell (j : ℕ) :
      (R j).encard ≤ 5 := by
    apply (Set.encard_mono (show R j ⊆
      {x ∈ Icc (grid M j) (grid M (j + 1)) | wave r x - correction s x = 0} from
      fun _ hx => ⟨Ioc_subset_Icc_self hx.1, hx.2⟩)).trans
    refine short_interval_bound (B := (m : ℝ) + 1) (by linarith [show (0 : ℝ) ≤ m by positivity])
      ?_ hBr hsmall ?_
    · intro i hi
      have h : (i : ℝ) ≤ m := by exact_mod_cast hm i hi
      linarith only [h]
    · rw [grid_length]
      exact hlen
  have hC : C.card ≤ (gridGood s M).card + (4 * m + 2) :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left (grid_crossing_card hM hm) _)
  calc
    _ ≤ (⋃ j ∈ C, R j).encard := Set.encard_mono hcover
    _ ≤ ∑ j ∈ C, (R j).encard := C.set_encard_biUnion_le R
    _ ≤ ∑ _j ∈ C, (5 : ℕ∞) := Finset.sum_le_sum (fun j _ => hcell j)
    _ ≤ (5 * ((gridGood s M).card + (4 * m + 2)) : ℕ) := by
      simpa [mul_comm] using (show ((C.card * 5 : ℕ) : ℕ∞) ≤
        ((5 * ((gridGood s M).card + (4 * m + 2)) : ℕ) : ℕ∞) from by
        exact_mod_cast (show C.card * 5 ≤ 5 * ((gridGood s M).card + (4 * m + 2)) by omega))

end Green82Proof

open Finset Filter Real Set
open scoped BigOperators

namespace Green82Proof

theorem count_grid_swap (P : Finset (Finset ℕ)) (M : ℕ) :
    (∑ s ∈ P, (gridGood s M).card) =
      ∑ j ∈ Finset.range M, (P.filter (fun s => |correction s (grid M j)| ≤ 1)).card := by
  classical
  change ∑ s ∈ P, ((Finset.range M).filter (fun j => |correction s (grid M j)| ≤ 1)).card = _
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem harmonic_real_sum (n : ℕ) :
    (∑ j ∈ Finset.range n, ((j : ℝ) + 1)⁻¹) = (harmonic n : ℝ) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_one,
    Rat.cast_natCast, Nat.cast_add, Nat.cast_one]

theorem sample_grid_good (k M : ℕ) (hM : 0 < M) :
    ∃ s ⊆ samplePool k, ((gridGood s M).card : ℝ) ≤
      1 + (M : ℝ) * (3 + 2 * Real.log M) / Real.sqrt (k + 1) := by
  classical
  let P := (samplePool k).powerset
  let hits (j : ℕ) : ℝ := (P.filter (fun s => |correction s (grid M j)| ≤ 1)).card
  let r := Real.sqrt (k + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hcard : (P.card : ℝ) = (2 : ℝ) ^ (16 * k) := by
    simp [P, Finset.card_powerset, sample_count]
  have hzero : hits 0 ≤ P.card := by
    unfold hits
    exact_mod_cast Finset.card_filter_le P (fun s => |correction s (grid M 0)| ≤ 1)
  have hhit (j : ℕ) (hj : j < M) (hj0 : 0 < j) :
      hits j ≤ (P.card : ℝ) * ((2 * (M : ℝ) / (j : ℝ) + 1) / r) := by
    have hmem : grid M j ∈ Ioc 0 π := by
      rw [← grid_zero M, ← grid_end hM]
      exact ⟨(grid_strictMono hM) hj0, (grid_strictMono hM).monotone hj.le⟩
    have he : 2 * π / grid M j = 2 * (M : ℝ) / (j : ℝ) := by
      unfold grid
      have hj' : (j : ℝ) ≠ 0 := by positivity
      have hM' : (M : ℝ) ≠ 0 := by positivity
      field_simp [Real.pi_ne_zero]
    simpa only [hits, P, he, hcard, r] using correction_band_card (k := k) hmem
  obtain ⟨m, hm⟩ : ∃ m : ℕ, M = m + 1 := ⟨M - 1, by omega⟩
  have hharmonic : (harmonic m : ℝ) ≤ 1 + Real.log M := by
    by_cases hm0 : m = 0
    · have he : M = 1 := by omega
      simp [hm0, he]
    · refine (harmonic_le_one_add_log _).trans ?_
      have hm' : (m : ℝ) ≤ M := by exact_mod_cast (show m ≤ M by omega)
      exact add_le_add le_rfl (Real.log_le_log (by positivity) hm')
  let T : ℝ := 1 + (M : ℝ) * (3 + 2 * Real.log M) / r
  have htotal : ∑ j ∈ Finset.range M, hits j ≤ (P.card : ℝ) * T := by
    rw [show Finset.range M = Finset.range (m + 1) by rw [hm], Finset.sum_range_succ']
    calc
      _ ≤ (∑ j ∈ Finset.range m, (P.card : ℝ) * ((2 * (M : ℝ) / ((j : ℝ) + 1) + 1) / r)) +
          (P.card : ℝ) := by
            apply add_le_add _ hzero
            apply Finset.sum_le_sum
            intro j hj
            have hj' := Finset.mem_range.mp hj
            simpa only [Nat.cast_succ] using hhit (j + 1) (by omega) (by omega)
      _ = (P.card : ℝ) * (1 + ((2 * (M : ℝ) * (harmonic m : ℝ)) + m) / r) := by
        have heach (j : ℕ) : (P.card : ℝ) * ((2 * (M : ℝ) / ((j : ℝ) + 1) + 1) / r) =
            ((P.card : ℝ) / r * (2 * (M : ℝ))) * ((j : ℝ) + 1)⁻¹ + (P.card : ℝ) / r := by ring
        simp_rw [heach, Finset.sum_add_distrib, ← Finset.mul_sum, harmonic_real_sum,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      _ ≤ (P.card : ℝ) * T := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine add_le_add le_rfl ((div_le_div_iff_of_pos_right hr).2 ?_)
        have hc : (m : ℝ) ≤ M := by exact_mod_cast (show m ≤ M by omega)
        have he := mul_le_mul_of_nonneg_left hharmonic (show (0 : ℝ) ≤ 2 * M by positivity)
        nlinarith only [he, hc]
  have hswap : (∑ s ∈ P, ((gridGood s M).card : ℝ)) = ∑ j ∈ Finset.range M, hits j := by
    unfold hits
    exact_mod_cast count_grid_swap P M
  have hex : ∃ s ∈ P, ((gridGood s M).card : ℝ) ≤ T := by
    by_contra! h
    have hP : P.Nonempty := ⟨∅, Finset.mem_powerset.2 (Finset.empty_subset _)⟩
    have hLt := Finset.sum_lt_sum_of_nonempty hP (fun s hs => h s hs)
    rw [hswap, Finset.sum_const, nsmul_eq_mul] at hLt
    exact (not_lt_of_ge htotal) hLt
  obtain ⟨s, hs, hsg⟩ := hex
  exact ⟨s, Finset.mem_powerset.mp hs, hsg⟩

end Green82Proof

open Finset Filter Real Set
open scoped BigOperators

namespace Green82Proof

noncomputable def rate (n : ℕ) : ℝ := ((n : ℝ) * Real.log n) ^ (2 / 3 : ℝ)

theorem rate_nonneg (n : ℕ) : 0 ≤ rate n := by
  unfold rate
  by_cases h : n = 0
  · simp [h]
  · have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    exact Real.rpow_nonneg (mul_nonneg (by positivity) (Real.log_nonneg hn)) _

theorem rate_mono {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : rate a ≤ rate b := by
  unfold rate
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (a : ℝ) ≤ b := by exact_mod_cast hab
  apply Real.rpow_le_rpow (mul_nonneg (by positivity) (Real.log_nonneg ha')) _ (by norm_num)
  exact mul_le_mul hb' (Real.log_le_log (by linarith) hb') (Real.log_nonneg ha') (by positivity)

theorem eventually_rate_control :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 ≤ Real.log n ∧
      17 * rate n ≤ (n : ℝ) ^ (3 / 4 : ℝ) ∧ 128 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hL : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1
  have hquarter : ∀ᶠ n : ℕ in atTop, 128 ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp ht).eventually_ge_atTop 128
  have h24 : ∀ᶠ n : ℕ in atTop, 17 ≤ (n : ℝ) ^ (1 / 24 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 24)).comp ht).eventually_ge_atTop 17
  have hlittle := isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16)
  have hlog := ht.eventually (hlittle.bound (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [eventually_ge_atTop (2 : ℕ), hL, hquarter, h24, hlog] with n hn hL hquarter h24 hlog
  have hn0 : (0 : ℝ) < n := by positivity
  have hlog0 : 0 ≤ Real.log n := by linarith
  have hlog' : Real.log n ≤ (n : ℝ) ^ (1 / 16 : ℝ) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_pos (Real.rpow_pos_of_pos hn0 _)] using hlog
  refine ⟨hn, hL, ?_, hquarter⟩
  have hpow : rate n ≤ (n : ℝ) ^ (17 / 24 : ℝ) := by
    unfold rate
    calc
      _ ≤ ((n : ℝ) * (n : ℝ) ^ (1 / 16 : ℝ)) ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow (mul_nonneg hn0.le hlog0)
          (mul_le_mul_of_nonneg_left hlog' hn0.le) (by norm_num)
      _ = _ := by
        rw [mul_comm (a := (n : ℝ)) (b := (n : ℝ) ^ _), ← Real.rpow_add_one hn0.ne']
        rw [← Real.rpow_mul hn0.le]
        norm_num
  calc
    17 * rate n ≤ 17 * (n : ℝ) ^ (17 / 24 : ℝ) := mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ (n : ℝ) ^ (1 / 24 : ℝ) * (n : ℝ) ^ (17 / 24 : ℝ) :=
      mul_le_mul_of_nonneg_right h24 (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; norm_num

theorem rate_balance {n : ℕ} (hn : 0 < n) (hL : 1 ≤ Real.log n) :
    (n : ℝ) * Real.log n / Real.sqrt ((⌊rate n⌋₊ : ℕ) + 1) ≤ rate n := by
  have hp : 0 < (n : ℝ) * Real.log n := by positivity
  have hRate : 0 ≤ rate n := rate_nonneg n
  have hfloor := (Nat.lt_floor_add_one (rate n)).le
  have hSqrt := Real.sqrt_le_sqrt hfloor
  have hbe : rate n * Real.sqrt (rate n) = (n : ℝ) * Real.log n := by
    unfold rate
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hp.le, ← Real.rpow_add hp]
    norm_num
  apply (div_le_iff₀ (Real.sqrt_pos.2 (by positivity))).2
  rw [← hbe]
  exact mul_le_mul_of_nonneg_left hSqrt hRate

theorem eventual_construction :
    ∀ᶠ n : ℕ in atTop, ∃ A : Finset ℕ, A.card = n ∧
      ({x ∈ Set.Ico 0 1 | ∑ i ∈ A, Real.cos (2 * π * (i : ℝ) * x) = 0} : Set ℝ).encard ≤
        (⌊25000 * rate n⌋₊ : ℕ∞) := by
  classical
  filter_upwards [eventually_rate_control] with n hn
  obtain ⟨hn2, hlog, hrate, hquarter⟩ := hn
  let k := ⌊rate n⌋₊
  let m := 16 * k
  let M := 64 * (n + m + 1)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hup : 1 ≤ rate n := by
    unfold rate
    simpa using Real.rpow_le_rpow (show (0 : ℝ) ≤ 1 by norm_num)
      (show (1 : ℝ) ≤ n * Real.log n from one_le_mul_of_one_le_of_one_le hn1 hlog)
      (show (0 : ℝ) ≤ 2 / 3 by norm_num)
  have hfloor : (k : ℝ) ≤ rate n := Nat.floor_le (rate_nonneg _)
  have hb : (m : ℝ) + 1 ≤ (n : ℝ) ^ (3 / 4 : ℝ) := by
    have hs : (m : ℝ) + 1 ≤ 17 * rate n := by
      dsimp [m]
      push_cast
      linarith only [hfloor, hup]
    exact hs.trans hrate
  have hpow : (n : ℝ) ^ (3 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) = n := by
    rw [← Real.rpow_add hn0]
    norm_num
  have hbhalf : (m : ℝ) + 1 ≤ (n : ℝ) / 2 := by
    have hp := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ n ^ (1 / 4 : ℝ) by linarith only [hquarter])
      (Real.rpow_nonneg hn0.le (3 / 4))
    rw [hpow] at hp
    linarith only [hb, hp]
  have hM : 0 < M := by dsimp [M]; positivity
  have hM128 : (M : ℝ) ≤ 128 * n := by
    dsimp [M]
    push_cast
    linarith only [hbhalf, hn0]
  obtain ⟨s, hs, hsg⟩ := sample_grid_good k M hM
  let q := n + s.card
  let A := Finset.range q \ s
  let r : ℝ := (q : ℝ) - 1 / 2
  have hsCard : s.card ≤ m := (Finset.card_le_card hs).trans (sample_count k).le
  have hsm (i) (hi : i ∈ s) : i ≤ m := (Finset.mem_Icc.mp (hs hi)).2
  have hsub : s ⊆ Finset.range q := by
    intro i hi
    have h := hsm i hi
    have hm : m < n := by
      exact_mod_cast (show (m : ℝ) < n by linarith only [hbhalf, hn0])
    exact Finset.mem_range.mpr (by dsimp [q]; omega)
  have hA : A.card = n := by
    simp [A, q, Finset.card_sdiff_of_subset hsub]
  have hr : (n : ℝ) / 2 ≤ r := by
    dsimp [r, q]
    push_cast
    have := (show (0 : ℝ) ≤ s.card by positivity)
    linarith
  have hsSmall : (2 * s.card + 1) * ((m : ℝ) + 1) ^ 4 ≤ r ^ 4 / 4 := by
    have hcast : (s.card : ℝ) ≤ m := by exact_mod_cast hsCard
    have hprod : (n : ℝ) ^ (15 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) = (n : ℝ) ^ (4 : ℕ) := by
      rw [← Real.rpow_add hn0, show (15 / 4 + 1 / 4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
    have hmult := mul_le_mul_of_nonneg_left hquarter (Real.rpow_nonneg hn0.le (15 / 4))
    rw [hprod] at hmult
    calc
      _ ≤ (2 * ((m : ℝ) + 1)) * ((m : ℝ) + 1) ^ 4 :=
        mul_le_mul_of_nonneg_right (by linarith only [hcast]) (by positivity)
      _ = 2 * ((m : ℝ) + 1) ^ 5 := by ring
      _ ≤ 2 * ((n : ℝ) ^ (3 / 4 : ℝ)) ^ (5 : ℕ) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb 5) (by norm_num)
      _ = 2 * (n : ℝ) ^ (15 / 4 : ℝ) := by
        rw [← Real.rpow_natCast _ 5, ← Real.rpow_mul hn0.le]; norm_num
      _ ≤ ((n : ℝ) / 2) ^ 4 / 4 := by nlinarith only [hmult]
      _ ≤ r ^ 4 / 4 := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hr 4) (by norm_num)
  have hlen : r * (π / (M : ℝ)) ≤ 1 / 8 := by
    have hr0 : 0 ≤ r := (by positivity : 0 ≤ (n : ℝ) / 2).trans hr
    have hrl : r ≤ (n : ℝ) + m + 1 := by
      dsimp [r, q]
      push_cast
      have hcast : (s.card : ℝ) ≤ m := by exact_mod_cast hsCard
      linarith only [hcast]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < M)).2
    have hpre := mul_le_mul hrl Real.pi_lt_four.le pi_pos.le (by positivity)
    dsimp [M]
    push_cast
    linarith only [hpre, hn0, show (0 : ℝ) ≤ m by positivity]
  have hlogM : Real.log M ≤ 8 * Real.log n := by
    have hln := Real.log_le_log (by positivity : 0 < (M : ℝ)) hM128
    rw [Real.log_mul (by norm_num) (by positivity)] at hln
    have hpow : Real.log (128 : ℝ) = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.log_pow]; norm_num
    rw [hpow] at hln
    have hncast : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hncast
    linarith only [hln, h2]
  have hsg' : ((gridGood s M).card : ℝ) ≤ 1 + 2432 * rate n := by
    have hSqrt : 0 < Real.sqrt ((k : ℝ) + 1) := by positivity
    have hbound := mul_le_mul hM128 (show 3 + 2 * Real.log M ≤ 19 * Real.log n by
      linarith only [hlog, hlogM]) (by
        have hl := Real.log_nonneg (show (1 : ℝ) ≤ M by exact_mod_cast hM)
        linarith) (by positivity)
    have hb' : (M : ℝ) * (3 + 2 * Real.log M) ≤ 2432 * (n * Real.log n) := by
      nlinarith only [hbound]
    have hb'' := (div_le_div_iff_of_pos_right hSqrt).2 hb'
    simpa using hsg.trans (add_le_add le_rfl (hb''.trans (by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (rate_balance (by omega) hlog) (by norm_num))))
  have hZ := half_period_grid_encard hM hsub (show 0 < A.card by rw [hA]; omega) hsm
    (hbhalf.trans hr) hsSmall hlen
  have hbound : (2 * (5 * ((gridGood s M).card + (4 * m + 2))) : ℕ) ≤ ⌊25000 * rate n⌋₊ := by
    apply Nat.le_floor
    push_cast
    have hmrate : (m : ℝ) ≤ 16 * rate n := by
      dsimp [m]
      push_cast
      linarith only [hfloor]
    linarith only [hsg', hmrate, hup]
  refine ⟨A, hA, (full_period_encard hZ).trans ?_⟩
  exact_mod_cast hbound

end Green82Proof

open Finset Filter Real Set
open scoped BigOperators

namespace Green82Proof

theorem all_construction :
    ∃ C > (0 : ℝ), ∀ n ≥ 1, ∃ A : Finset ℕ, A.card = n ∧
      ({x ∈ Set.Ico 0 1 | ∑ i ∈ A, Real.cos (2 * π * (i : ℝ) * x) = 0} : Set ℝ).encard ≤
        (⌊C * rate n⌋₊ : ℕ∞) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 eventual_construction
  let C : ℝ := max 25000 (2 * (N : ℝ) / rate 2)
  refine ⟨C, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro n hn
  by_cases h : N ≤ n
  · obtain ⟨A, hA, hZ⟩ := hN n h
    refine ⟨A, hA, hZ.trans ?_⟩
    exact_mod_cast Nat.floor_mono (mul_le_mul_of_nonneg_right (le_max_left _ _) (rate_nonneg n))
  · have hA : (Finset.range n).Nonempty := Finset.card_pos.mp (by simpa using (show 0 < n by omega))
    have hZ := full_period_encard (cosine_zeros_encard hA (m := n - 1)
        (fun i hi => by have := Finset.mem_range.mp hi; omega))
    refine ⟨Finset.range n, Finset.card_range n, hZ.trans ?_⟩
    have hsmall : (2 * (n - 1) : ℕ) ≤ ⌊C * rate n⌋₊ := by
      apply Nat.le_floor
      by_cases hn' : 2 ≤ n
      · have hpos : 0 < rate 2 := by
          unfold rate
          exact Real.rpow_pos_of_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num))) _
        have hM := rate_mono (show 1 ≤ 2 by norm_num) hn'
        have hc0 : 0 ≤ 2 * (N : ℝ) / rate 2 := by positivity
        have hc : (2 * (N : ℝ) / rate 2) * rate 2 = 2 * (N : ℝ) :=
          div_mul_cancel₀ _ hpos.ne'
        calc
          _ ≤ 2 * (N : ℝ) := by
            push_cast
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show n - 1 ≤ N by omega)) (by norm_num)
          _ = (2 * (N : ℝ) / rate 2) * rate 2 := hc.symm
          _ ≤ C * rate n := mul_le_mul (le_max_right _ _) hM hpos.le (le_trans hc0 (le_max_right _ _))
      · have he : n = 1 := by omega
        rw [he]
        norm_num
        exact mul_nonneg ((le_max_left _ _).trans' (by norm_num)) (rate_nonneg _)
    exact_mod_cast hsmall

end Green82Proof

open Green82Proof

theorem OMA.solution : type_of% @Green82.green_82_upper_bound := by
  obtain ⟨C, hC, h⟩ := all_construction
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨s, hsc, hZ⟩ := h n hn
  let e : ℕ ↪ ℤ := ⟨Int.ofNat, Int.ofNat_injective⟩
  let A := s.map e
  refine ⟨A, by simpa [A] using hsc, ?_⟩
  let R : Set ℝ := {x ∈ Set.Ico 0 1 | ∑ i ∈ s, Real.cos (2 * π * (i : ℝ) * x) = 0}
  have hR : {x ∈ Set.Ico 0 1 | ∑ i ∈ A, Real.cos (2 * π * (i : ℝ) * x) = 0} = R := by
    ext x
    simp [A, R, e, Finset.sum_map]
  rw [hR]
  have hf : R.Finite := (Set.encard_le_coe_iff_finite_ncard_le.mp hZ).1
  rw [hf.cast_ncard_eq]
  exact hZ
