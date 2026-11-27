import OMAStatements.S_opg_distribution_and_upper_bound_of_mimic_numbers

/-!
# Distribution and upper bound of mimic numbers

Source: https://www.openproblemgarden.org/op/distribution_and_upper_bound_of_mimic_numbers
Definitions 1 and 2 of Bhattacharyya, Bandyopadhyay and Maulik,
“Non-primes are recursively divisible,” Acta Universitatis Apulensis 19 (2009).
Credit: @rleshner

M is a radix of at least two. The source theorem assumes positive D ≤ M.
Evaluating the base-M digit polynomial at M-D is the mimic step. The mimic
number is the first hitting time of D, when it exists. The two requested
quantities are the exact histogram on any initial window and the support
of possible hitting times for positive multiples of D.
-/

namespace OMA.S_opg_distribution_and_upper_bound_of_mimic_numbers

open scoped Polynomial

private theorem small {M D n : ℕ} (hn : n < M) : step M D n = n := by
  rcases eq_or_ne n 0 with rfl|h
  · simp [step]
  · simp [step, Nat.digits_of_lt M n h hn]

private theorem digit_step {M D : ℕ} (hM : 1 < M) (r q : ℕ) (hr : r < M) :
    step M D (r+M*q) = r+(M-D)*step M D q := by
  by_cases h : r ≠ 0 ∨ q ≠ 0
  · simp only [step, Nat.digits_add M hM r q hr h, Nat.ofDigits_cons]
  · push Not at h
    simp [h.1,h.2,step]

private theorem step_mod {M D n : ℕ} (hd : D ≤ M) : Nat.ModEq D n (step M D n) := by
  have h : Nat.ModEq D M (M-D) := by
    apply Nat.ModEq.symm
    apply (Nat.modEq_iff_dvd' (Nat.sub_le ..)).2
    simp [Nat.sub_sub_self hd]
  simpa only [step, Nat.ofDigits_digits] using Nat.ofDigits_modEq' M (M-D) D h (M.digits n)

private theorem positive {M D n : ℕ} (hM : 1 < M) (hB : 0 < M-D) (hn : 0 < n) :
    0 < step M D n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n < M
    · rwa [small h]
    · have hq : 0 < n / M := Nat.div_pos (by omega) (by omega)
      have hlt := Nat.div_lt_self hn hM
      have pos := ih _ hlt hq
      calc 0 < n%M + (M-D)*step M D (n/M) := by positivity
           _ = step M D n := by
              rw [← digit_step hM _ _ (Nat.mod_lt n (by omega)), Nat.mod_add_div]

private theorem decrease {M D n : ℕ} (hM : 1 < M) (hD : 0 < D) (hn : M ≤ n) :
    step M D n < n := by
  have hq := Nat.div_pos hn (show 0 < M by omega)
  have hm : step M D (n/M) ≤ n/M := by
    simpa only [step, Nat.ofDigits_digits] using Nat.ofDigits_monotone (M.digits (n/M)) (Nat.sub_le M D)
  calc
    step M D n = n%M + (M-D)*step M D (n/M) := by
      rw [← digit_step hM _ _ (Nat.mod_lt n (by omega)), Nat.mod_add_div]
    _ ≤ n%M + (M-D)*(n/M) := by gcongr
    _ < n%M + M*(n/M) := by gcongr; omega
    _ = n := Nat.mod_add_div n M

private theorem step_recode {M D : ℕ} (hM : 1 < M) (ds : List ℕ)
    (hds : ∀ a ∈ ds, a < M) : step M D (Nat.ofDigits M ds) = Nat.ofDigits (M-D) ds := by
  induction ds with
  | nil => simp [step]
  | cons a ds ih =>
    simp only [Nat.ofDigits_cons, digit_step hM a _ (hds a (by simp)), ih (by aesop)]

private theorem lift {M D t : ℕ} (hM : 1 < M) (hD : 0 < D) (hd : D < M)
    (ht : M-D ≤ t) : ∃ u, t < u ∧ step M D u = t := by
  let B := M-D
  have hb : 0 < B := by dsimp [B]; omega
  have hBM : B < M := by dsimp [B]; omega
  let q := t/B
  have hq : 0 < q := Nat.div_pos ht hb
  let z := Nat.ofDigits M (B.digits q)
  have hz : q ≤ z := by simpa only [z, Nat.ofDigits_digits] using Nat.ofDigits_monotone (B.digits q) hBM.le
  have hz' : step M D z = q := by
    rw [show z = Nat.ofDigits M (B.digits q) by rfl, step_recode hM]
    · exact Nat.ofDigits_digits B q
    · intro a ha
      by_cases h1 : B = 1
      · simp only [h1, Nat.digits_one, List.mem_replicate] at ha
        omega
      · exact (Nat.digits_lt_base (by omega : 1 < B) ha).trans hBM
  refine ⟨t % B + M*z, ?_, ?_⟩
  · calc t = t % B + B*q := (Nat.mod_add_div ..).symm
         _ < t % B + M*q := by gcongr
         _ ≤ t % B + M*z := by gcongr
  · rw [digit_step hM _ _ ((Nat.mod_lt _ hb).trans hBM), hz']
    exact Nat.mod_add_div t B

private theorem upFirst {M D n u h : ℕ} (hu : step M D u = n) (hne : u ≠ D)
    (hn : First M D h n) : First M D (h+1) u := by
  constructor
  · rw [Function.iterate_succ_apply, hu]; exact hn.1
  · intro j hj
    cases j with
    | zero => exact hne
    | succ j => rw [Function.iterate_succ_apply, hu]; exact hn.2 j (by omega)

private theorem allHeights {M D : ℕ} (hM : 1 < M) (hD : 0 < D) (hd : D < M)
    (hB : M-D ≤ D) (h : ℕ) : ∃ n, D ≤ n ∧ D ∣ n ∧ First M D h n := by
  induction h with
  | zero => exact ⟨D, le_rfl, dvd_refl _, rfl, by omega⟩
  | succ h ih =>
    obtain ⟨n,hn,hdiv,hfirst⟩ := ih
    obtain ⟨u,hu,hs⟩ := lift hM hD hd (hB.trans hn)
    have hcong := step_mod (n:=u) hd.le
    rw [hs] at hcong
    exact ⟨u, by omega, Nat.modEq_zero_iff_dvd.mp (hcong.trans hdiv.modEq_zero_nat),
      upFirst hs (by omega) hfirst⟩

private theorem allHit {M D : ℕ} (hM : 1 < M) (hD : 0 < D) (hd : D < M)
    (hB : M-D ≤ D) (n : ℕ) (hn : 0 < n) (hdiv : D ∣ n) : ∃ h, First M D h n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases eq : n = D
    · exact ⟨0, eq, by omega⟩
    have hlt : M ≤ n := by
      obtain ⟨v,rfl⟩ := hdiv
      by_contra! h
      have hv : 2 ≤ v := by by_contra! e; interval_cases v <;> simp_all
      nlinarith [Nat.mul_le_mul_left D hv, Nat.sub_add_cancel hd.le]
    have d := decrease hM hD hlt
    have h' := (step_mod (n:=n) hd.le).symm.trans hdiv.modEq_zero_nat
    obtain ⟨h,hh⟩ := ih _ d (positive hM (by omega) hn) (Nat.modEq_zero_iff_dvd.mp h')
    exact ⟨h+1, upFirst rfl eq hh⟩

private theorem below {M D : ℕ} (hM : 1 < M) (hd : D < M-D) (n : ℕ) :
    step M D n = D → n = D := by
  intro e
  by_cases h : n < M
  · rwa [small h] at e
  · have hn : 0 < n/M := Nat.div_pos (by omega) (by omega)
    have hpos := positive (D:=D) hM (by omega) hn
    have hsplit := digit_step (D:=D) hM (n%M) (n/M) (Nat.mod_lt _ (by omega))
    rw [Nat.mod_add_div, e] at hsplit
    have hm := Nat.mul_le_mul_left (M-D) hpos
    simp only [Nat.mul_one] at hm
    omega

private theorem onlyZero {M D : ℕ} (hM : 1 < M) (hD : 0 < D) (hd : D ≤ M)
    (exc : D = M ∨ D < M-D) {n h : ℕ} (hdiv : D ∣ n) :
    First M D h n ↔ n = D ∧ h = 0 := by
  constructor
  · rintro ⟨reach,first⟩
    cases h with
    | zero => exact ⟨reach, rfl⟩
    | succ h =>
      exfalso
      rcases exc with eq|hB
      · subst D
        have hz : step M M n = 0 := by
          rcases eq_or_ne n 0 with rfl|hne
          · simp [step]
          · simp [step, Nat.digits_def' hM (Nat.pos_of_ne_zero hne), Nat.ofDigits_cons,
              Nat.mod_eq_zero_of_dvd hdiv]
        rw [Function.iterate_succ_apply, hz] at reach
        have h0 : Function.IsFixedPt (step M M) 0 := by simp [Function.IsFixedPt,step]
        have hz' := h0.iterate h
        change (step M M)^[h] 0 = 0 at hz'
        omega
      · have back (j a : ℕ) (e : (step M D)^[j] a = D) : a = D := by
          induction j generalizing a with
          | zero => exact e
          | succ j ih =>
            rw [Function.iterate_succ_apply] at e
            exact below hM hB _ (ih _ e)
        apply first 0 (by omega)
        exact back _ _ reach
  · rintro ⟨rfl,rfl⟩; exact ⟨rfl, by omega⟩

private theorem preimage_bound {M D : ℕ} (hM : 1 < M) (hB : 2 ≤ M-D)
    (t n : ℕ) (hle : step M D n ≤ t) : n < (M+1)^(t+1) := by
  induction t using Nat.strong_induction_on generalizing n with
  | h t ih =>
    by_cases hn : n < M
    · have hl := Nat.one_le_pow t (M+1) (by omega)
      rw [pow_succ]
      nlinarith
    · have hq : 0 < n/M := Nat.div_pos (by omega) (by omega)
      have hp := positive (D:=D) hM (by omega) hq
      have eq := digit_step (D:=D) hM (n%M) (n/M) (Nat.mod_lt _ (by omega))
      rw [Nat.mod_add_div] at eq
      have hstep : step M D (n/M) < t := by
        have H := Nat.mul_le_mul_right (step M D (n/M)) hB
        omega
      have bound := ih (step M D (n/M)) hstep (n/M) le_rfl
      have hpow : (M+1)^(step M D (n/M)+1) ≤ (M+1)^t :=
        Nat.pow_le_pow_right (by omega) hstep
      have hrem := Nat.mod_lt n (by omega : 0 < M)
      have hv := Nat.mod_add_div n M
      have hb := Nat.succ_le_of_lt (bound.trans_le hpow)
      rw [pow_succ]
      nlinarith [Nat.mul_le_mul_left M hb, Nat.one_le_pow t (M+1) (by omega)]

private theorem bounded_height {M D : ℕ} (hM : 1 < M) (hB : 2 ≤ M-D)
    (h : ℕ) : ∃ N, ∀ n, (step M D)^[h] n = D → n < N := by
  induction h with
  | zero => exact ⟨D+1, fun n hn => by change n = D at hn; omega⟩
  | succ h ih =>
    obtain ⟨N,hN⟩ := ih
    refine ⟨(M+1)^(N+1), fun n hn => ?_⟩
    rw [Function.iterate_succ_apply] at hn
    exact preimage_bound hM hB N n (hN _ hn).le

private theorem unbounded_height {M D : ℕ} (hM : 1 < M) (hD : 0 < D) (hB : M-D = 1)
    (h K : ℕ) : ∃ n, K < n ∧ D ∣ n ∧ First M D (h+1) n := by
  have hd : D < M := by omega
  obtain ⟨v,hv,hdiv,hf⟩ := allHeights hM hD hd (by omega) (h+1)
  have hvD : v ≠ D := hf.2 0 (by omega)
  have hstep (k : ℕ) : step M D (M^k*v) = step M D v := by
    induction k with
    | zero => simp
    | succ k ih =>
      have dig := digit_step (D:=D) hM 0 (M^k*v) (by omega)
      simpa [pow_succ', hB, Nat.mul_assoc, ih] using dig
  let n := M^(K+1)*v
  have hgrowth : K < M^(K+1) := by
    have := Nat.lt_pow_self (n:=K+1) (a:=M) (by omega)
    omega
  have hn : K < n := by
    dsimp [n]
    nlinarith [Nat.mul_le_mul_left (M^(K+1)) (show 1 ≤ v by omega)]
  have hnD : n ≠ D := by
    dsimp [n]
    have := Nat.mul_le_mul_right v (Nat.one_le_pow (K+1) M (by omega))
    simp only [Nat.one_mul] at this
    omega
  have hh : First M D h (step M D v) := by
    refine ⟨?_,fun j hj e => ?_⟩
    · rw [← Function.iterate_succ_apply]; exact hf.1
    · exact hf.2 (j+1) (by omega) (by rwa [Function.iterate_succ_apply])
  exact ⟨n,hn,dvd_mul_of_dvd_right hdiv _,upFirst (hstep _) hnD hh⟩
private theorem digitStep {M D q d : ℕ} (hM : 1 < M) (hd : d < M) :
    step M D (M*q+d) = d + (M-D)*step M D q := by
  rw [Nat.add_comm (M*q) d, digit_step hM d q hd]

private theorem eligible {M D n h : ℕ} (hD : 0 < D) (hd : D ≤ M) (hf : First M D h n) :
    0 < n ∧ D ∣ n := by
  have con (j a : ℕ) : Nat.ModEq D a ((step M D)^[j] a) := by
    induction j generalizing a with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply]
      exact (step_mod hd).trans (ih _)
  have H := con h n
  rw [hf.1] at H
  have hdvd := Nat.modEq_zero_iff_dvd.mp (H.trans (dvd_refl D).modEq_zero_nat)
  refine ⟨?_, hdvd⟩
  by_contra! hz
  have h0 : Function.IsFixedPt (step M D) 0 := by simp [Function.IsFixedPt,step]
  have e : (step M D)^[h] 0 = 0 := h0.iterate h
  have he := hf.1
  obtain rfl : n = 0 := by omega
  omega

private theorem radixHistogram {M D : ℕ} (hM : 1 < M) : HistogramLaw M D := by
  classical
  have chunk (q r : ℕ) (hr : r ≤ M) :
      windowPoly M D (M*q+r) = windowPoly M D (M*q) +
        Polynomial.X ^ ((M-D)*step M D q) * digitPoly r := by
    simp only [windowPoly, digitPoly, Finset.sum_range_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    rw [digitStep hM ((Finset.mem_range.mp hd).trans_le hr), ← pow_add, Nat.add_comm]
  have full (q : ℕ) : windowPoly M D (M*q) =
      (windowPoly M D q).comp (Polynomial.X ^ (M-D)) * digitPoly M := by
    induction q with
    | zero => simp [windowPoly]
    | succ q ih =>
      rw [Nat.mul_succ, chunk q M le_rfl, ih]
      simp [windowPoly, Finset.sum_range_succ, Polynomial.add_comp,
        add_mul, ← pow_mul]
  refine ⟨fun q r hr => (chunk q r hr).trans (by rw [full q]), ?_⟩
  have first_succ (h n : ℕ) : First M D (h+1) n ↔
      n ≠ D ∧ First M D h (step M D n) := by
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨hb 0 (by omega), ha, fun j hj => hb (j+1) (by omega)⟩
    · rintro ⟨hd, ha, hb⟩
      refine ⟨ha, ?_⟩
      intro j hj
      cases j with
      | zero => exact hd
      | succ j => exact hb j (by omega)
  intro N h
  let S := (Finset.range N).filter fun n => First M D h (step M D n)
  have hfilter : (Finset.range N).filter (First M D (h+1)) = S.erase D := by
    ext n
    simp [S, first_succ, and_left_comm]
  have hcoeff (t : ℕ) : (windowPoly M D N).coeff t =
      ((Finset.range N).filter (fun n => step M D n = t)).card := by
    simp [windowPoly, Polynomial.coeff_X_pow, eq_comm]
  have hsum : (∑ t ∈ (Finset.range N).filter (First M D h), (windowPoly M D N).coeff t) = S.card := by
    simp_rw [hcoeff]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    apply Finset.filter_congr
    intro n hn
    have hle : step M D n ≤ n := (Nat.ofDigits_monotone (M.digits n) (Nat.sub_le M D)).trans_eq (Nat.ofDigits_digits M n)
    have hs : step M D n < N := hle.trans_lt (Finset.mem_range.mp hn)
    simp [hs]
  rw [hfilter, hsum]
  by_cases hd : D ∈ S
  · have h := hd
    simp only [S, Finset.mem_filter, Finset.mem_range] at h
    simp [h, Finset.card_erase_of_mem hd]
  · have h := hd
    simp only [S, Finset.mem_filter, Finset.mem_range] at h
    simp [h, Finset.erase_eq_of_notMem hd]

end OMA.S_opg_distribution_and_upper_bound_of_mimic_numbers

open OMA.S_opg_distribution_and_upper_bound_of_mimic_numbers

theorem OMA.solution : type_of% @OMA.S_opg_distribution_and_upper_bound_of_mimic_numbers.main := by
  intro M D hM hD hd
  refine ⟨radixHistogram hM, fun _ _ hf => eligible hD hd hf,
    fun exc _ _ hdiv => onlyZero hM hD hd exc hdiv,
    fun ⟨hlt,hu⟩ => ⟨allHit hM hD hlt hu, allHeights hM hD hlt hu⟩, ?_,
    fun hu => unbounded_height hM hD hu⟩
  intro hB h
  obtain ⟨N,hN⟩ := bounded_height hM hB h
  exact ⟨N,fun n hf => hN n hf.1⟩
