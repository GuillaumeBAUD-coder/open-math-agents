import FormalConjectures.Mathoverflow.«10799»

/-!
# Weak Kahn–Kalai: an optimal `p` in `[n^(-ε) t, t]`

Following the informal argument of Kahn and Kalai (2006). Write `g p = μ_p(F)` and
`L p = log (1 / g p)`. Russo's formula `g' (p) = I^p(F)` is proved by pairing every set `S`
with `S Δ {i}`. If no `p ∈ [a, t]` (with `a = n^(-ε) t`) were `(C log (1/p), p)`-optimal, then
`I^p(F) > C g L / p` on the whole interval, so `p ↦ L p * p ^ C` is antitone there. Then
`log 2 · t^C ≤ L a · a^C`, i.e. `L a ≥ log 2 · n^(ε C)`, while `g a ≥ (a / t)^n g t` gives
`L a ≤ log 2 + ε n log n`. Taking `ε C = ⌈4(ε+1)⌉ + 2` makes these incompatible for `n ≥ 2`.
-/

open Finset Real Mathoverflow10799

namespace OMAv6
variable {n : ℕ}

lemma card_lt_of_notMem' {S : Finset (Fin n)} {i : Fin n} (hi : i ∉ S) : #S < n := by
  have h : S ⊂ univ := Finset.ssubset_iff_subset_ne.mpr ⟨S.subset_univ, fun h => hi (h ▸ mem_univ i)⟩
  simpa using Finset.card_lt_card h

lemma symmDiff_single_of_notMem' {S : Finset (Fin n)} {i : Fin n} (hi : i ∉ S) :
    symmDiff S {i} = insert i S := by
  ext x
  simp only [mem_symmDiff, mem_singleton, mem_insert]
  by_cases hx : x = i
  · subst hx; simp [hi]
  · simp [hx]

lemma symmDiff_single_invol (S : Finset (Fin n)) (i : Fin n) :
    symmDiff (symmDiff S {i}) {i} = S := symmDiff_symmDiff_cancel_right _ _

lemma mu_insert' (p : ℝ) {S : Finset (Fin n)} {i : Fin n} (hi : i ∉ S) :
    μ p S * p = μ p (insert i S) * (1 - p) := by
  have hlt := card_lt_of_notMem' hi
  unfold μ
  rw [card_insert_of_notMem hi]
  obtain ⟨k, hk⟩ : ∃ k, n - #S = k + 1 := ⟨n - #S - 1, by omega⟩
  rw [hk, show n - (#S + 1) = k by omega]
  ring


lemma pair_identity (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (F : Finset (Finset (Fin n)))
    (hF : IsMonotoneIncreasing F) (i : Fin n) :
    ∑ S : Finset (Fin n), (if S ∈ F then μ p S * (if i ∈ S then 1 / p else -(1 / (1 - p))) else 0)
      = ∑ S : Finset (Fin n), (if Xor (S ∈ F) (symmDiff S {i} ∈ F) then μ p S else 0) := by
  set d : Finset (Fin n) → ℝ := fun S =>
    if S ∈ F then μ p S * (if i ∈ S then 1 / p else -(1 / (1 - p))) else 0 with hd
  set g : Finset (Fin n) → ℝ := fun S =>
    if Xor (S ∈ F) (symmDiff S {i} ∈ F) then μ p S else 0 with hg
  have hq : (1 : ℝ) - p ≠ 0 := by linarith
  have hp : p ≠ 0 := hp0.ne'
  -- the pointwise identity for a set without `i`
  have key : ∀ S : Finset (Fin n), i ∉ S →
      d S + d (symmDiff S {i}) = g S + g (symmDiff S {i}) := by
    intro S hi
    have hU : symmDiff S {i} = insert i S := symmDiff_single_of_notMem' hi
    have hUU : symmDiff (insert i S) {i} = S := by
      rw [← hU]; exact symmDiff_single_invol S i
    have hiU : i ∈ insert i S := mem_insert_self i S
    have hmu := mu_insert' p hi
    have hup : S ∈ F → insert i S ∈ F := fun h =>
      hF (Finset.subset_insert i S) h
    rw [hU]
    simp only [hd, hg, hUU, hU, hiU, hi, if_true, if_false]
    by_cases hS : S ∈ F
    · have hS' := hup hS
      simp only [hS, hS', if_true, xor_self, if_false]
      field_simp
      linarith
    · by_cases hS' : insert i S ∈ F
      · simp only [hS, hS', if_true, if_false]
        simp only [Xor, true_and, false_and, or_false, and_true, false_or, not_false_eq_true,
          if_true, zero_add, add_zero]
        field_simp
        linarith
      · simp [hS, hS']
  have key' : ∀ S : Finset (Fin n), d S + d (symmDiff S {i}) = g S + g (symmDiff S {i}) := by
    intro S
    by_cases hi : i ∈ S
    · have hi' : i ∉ symmDiff S {i} := by simp [mem_symmDiff, hi]
      have := key _ hi'
      rw [symmDiff_single_invol] at this
      linarith
    · exact key S hi
  let e : Finset (Fin n) ≃ Finset (Fin n) :=
    (Function.Involutive.toPerm (fun S => symmDiff S {i}) (fun S => symmDiff_single_invol S i))
  have hde : ∑ S, d (symmDiff S {i}) = ∑ S, d S := Equiv.sum_comp e d
  have hge : ∑ S, g (symmDiff S {i}) = ∑ S, g S := Equiv.sum_comp e g
  have hsum : ∑ S, (d S + d (symmDiff S {i})) = ∑ S, (g S + g (symmDiff S {i})) :=
    Finset.sum_congr rfl fun S _ => key' S
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hde, hge] at hsum
  linarith


lemma hasDerivAt_mu' (S : Finset (Fin n)) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun q => μ q S)
      (μ p S * ((S.card : ℝ) / p - ((n - S.card : ℕ) : ℝ) / (1 - p))) p := by
  have h1 : HasDerivAt (fun q : ℝ => q ^ S.card) (S.card * p ^ (S.card - 1)) p := hasDerivAt_pow _ p
  have h2 : HasDerivAt (fun q : ℝ => (1 - q) ^ (n - S.card))
      (((n - S.card : ℕ) : ℝ) * (1 - p) ^ (n - S.card - 1) * (-1)) p :=
    ((hasDerivAt_id p).const_sub 1).fun_pow (n - S.card)
  have h := h1.fun_mul h2
  show HasDerivAt (fun q : ℝ => q ^ S.card * (1 - q) ^ (n - S.card)) _ p
  refine h.congr_deriv ?_
  unfold μ
  have hq : (1 : ℝ) - p ≠ 0 := by linarith
  have hp : p ≠ 0 := hp0.ne'
  generalize S.card = k
  generalize n - k = m
  rcases k with _ | k <;> rcases m with _ | m <;> simp only [pow_succ, pow_zero, Nat.cast_zero, Nat.cast_succ, Nat.add_sub_cancel, Nat.zero_sub] <;> field_simp <;> ring

lemma weight_sum (S : Finset (Fin n)) (p : ℝ) :
    ∑ i : Fin n, (if i ∈ S then 1 / p else -(1 / (1 - p)))
      = (S.card : ℝ) / p - ((n - S.card : ℕ) : ℝ) / (1 - p) := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have h1 : (univ.filter fun i : Fin n => i ∈ S) = S := by ext; simp
  have h2 : (univ.filter fun i : Fin n => i ∉ S) = Sᶜ := by ext; simp
  rw [h1, h2, card_compl, Fintype.card_fin]
  ring

lemma russo (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun q => μFamily q F) (edgeBoundary n p F) p := by
  have hd : HasDerivAt (fun q => μFamily q F)
      (∑ S ∈ F, μ p S * ((S.card : ℝ) / p - ((n - S.card : ℕ) : ℝ) / (1 - p))) p := by
    unfold μFamily
    exact HasDerivAt.fun_sum fun S _ => hasDerivAt_mu' S hp0 hp1
  convert hd using 1
  symm
  calc ∑ S ∈ F, μ p S * ((S.card : ℝ) / p - ((n - S.card : ℕ) : ℝ) / (1 - p))
      = ∑ S : Finset (Fin n), ∑ i : Fin n,
          (if S ∈ F then μ p S * (if i ∈ S then 1 / p else -(1 / (1 - p))) else 0) := by
        rw [← Finset.sum_filter_add_sum_filter_not univ (fun S => S ∈ F)]
        have hf : (univ.filter fun S : Finset (Fin n) => S ∈ F) = F := by ext; simp
        rw [hf]
        have h0 : ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S ∉ F), ∑ i : Fin n,
            (if S ∈ F then μ p S * (if i ∈ S then 1 / p else -(1 / (1 - p))) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro S hS
          simp only [mem_filter] at hS
          simp [hS.2]
        rw [h0, add_zero]
        apply Finset.sum_congr rfl
        intro S hS
        simp only [hS, if_true]
        rw [← Finset.mul_sum, weight_sum]
    _ = ∑ i : Fin n, ∑ S : Finset (Fin n),
          (if S ∈ F then μ p S * (if i ∈ S then 1 / p else -(1 / (1 - p))) else 0) :=
        Finset.sum_comm
    _ = ∑ i : Fin n, ∑ S : Finset (Fin n),
          (if Xor (S ∈ F) (symmDiff S {i} ∈ F) then μ p S else 0) :=
        Finset.sum_congr rfl fun i _ => pair_identity p hp0 hp1 F hF i
    _ = ∑ S : Finset (Fin n), ∑ i : Fin n,
          (if Xor (S ∈ F) (symmDiff S {i} ∈ F) then μ p S else 0) := Finset.sum_comm
    _ = edgeBoundary n p F := by
        unfold edgeBoundary boundaryCount
        apply Finset.sum_congr rfl
        intro S _
        rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp


lemma mu_nonneg' (S : Finset (Fin n)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ μ p S := by
  unfold μ
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

lemma mu_total (p : ℝ) : ∑ S : Finset (Fin n), μ p S = 1 := by
  have h := Finset.sum_pow_mul_eq_add_pow p (1 - p) (univ : Finset (Fin n))
  rw [Finset.powerset_univ, card_univ, Fintype.card_fin, add_sub_cancel, one_pow] at h
  exact h

lemma univ_mem_of (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F) {t : ℝ}
    (h : μFamily t F = 1 / 2) : (univ : Finset (Fin n)) ∈ F := by
  obtain ⟨S, hS⟩ : F.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp [μFamily] at h
  exact hF (Finset.subset_univ S) hS

lemma empty_not_mem_of (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F) {t : ℝ}
    (h : μFamily t F = 1 / 2) : (∅ : Finset (Fin n)) ∉ F := by
  intro he
  have hall : F = univ := by
    ext S
    simp only [mem_univ, iff_true]
    exact hF (Finset.empty_subset S) he
  rw [μFamily, hall, mu_total] at h
  norm_num at h

lemma muFamily_pos (F : Finset (Finset (Fin n))) (hU : (univ : Finset (Fin n)) ∈ F) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) : 0 < μFamily p F := by
  have h1 : μ p (univ : Finset (Fin n)) ≤ μFamily p F :=
    Finset.single_le_sum (fun S _ => mu_nonneg' S hp0.le hp1.le) hU
  have h2 : 0 < μ p (univ : Finset (Fin n)) := by
    unfold μ
    rw [card_univ, Fintype.card_fin, Nat.sub_self, pow_zero, mul_one]
    exact pow_pos hp0 _
  linarith

lemma muFamily_lt_one (F : Finset (Finset (Fin n))) (hE : (∅ : Finset (Fin n)) ∉ F) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) : μFamily p F < 1 := by
  have hsub : F ⊆ univ.erase ∅ := fun S hS => mem_erase.mpr ⟨fun h => hE (h ▸ hS), mem_univ S⟩
  have h1 : μFamily p F ≤ ∑ S ∈ univ.erase (∅ : Finset (Fin n)), μ p S :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun S _ _ => mu_nonneg' S hp0.le hp1.le
  have h2 := Finset.sum_erase_add (univ : Finset (Finset (Fin n))) (fun S => μ p S) (mem_univ ∅)
  rw [mu_total] at h2
  have h3 : 0 < μ p (∅ : Finset (Fin n)) := by
    unfold μ
    rw [card_empty, pow_zero, one_mul, Nat.sub_zero]
    exact pow_pos (by linarith) _
  linarith

lemma muFamily_lower (F : Finset (Finset (Fin n))) {a t : ℝ} (ha : 0 < a) (hat : a ≤ t)
    (ht1 : t < 1) : (a / t) ^ n * μFamily t F ≤ μFamily a F := by
  unfold μFamily
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S _
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have hk : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hr0 : 0 ≤ a / t := (div_pos ha ht).le
  have hr1 : a / t ≤ 1 := (div_le_one ht).mpr hat
  unfold μ
  have e1 : a ^ S.card = (a / t) ^ S.card * t ^ S.card := by
    rw [← mul_pow, div_mul_cancel₀ a ht.ne']
  have h1 : (a / t) ^ n ≤ (a / t) ^ S.card := pow_le_pow_of_le_one hr0 hr1 hk
  have h2 : (1 - t) ^ (n - S.card) ≤ (1 - a) ^ (n - S.card) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  rw [e1]
  have h3 : 0 ≤ t ^ S.card := pow_nonneg ht.le _
  have h4 : 0 ≤ (1 - t) ^ (n - S.card) := pow_nonneg (by linarith) _
  calc (a / t) ^ n * (t ^ S.card * (1 - t) ^ (n - S.card))
      ≤ (a / t) ^ S.card * (t ^ S.card * (1 - t) ^ (n - S.card)) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg h3 h4)
    _ ≤ (a / t) ^ S.card * (t ^ S.card * (1 - a) ^ (n - S.card)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr0 _)
        exact mul_le_mul_of_nonneg_left h2 h3
    _ = (a / t) ^ S.card * t ^ S.card * (1 - a) ^ (n - S.card) := by ring

lemma rhs_eq (C p m : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    C * Real.log (1 / p) * (m * Real.logb p m / p) = C * m * (-Real.log m) / p := by
  have hl : Real.log p ≠ 0 := (Real.log_neg hp0 hp1).ne
  rw [Real.logb, one_div, Real.log_inv]
  field_simp


lemma main_target :
    ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (_ : 2 ≤ n)
    (F : Finset (Finset (Fin n))) (_ : IsMonotoneIncreasing F)
    (t : ℝ) (_ : 0 < t) (_ : t < 1) (_ : μFamily t F = 1 / 2),
    ∃ p, (n : ℝ) ^ (-ε) * t ≤ p ∧ p ≤ t ∧ IsOptimalWith C p F := by
  intro ε hε
  set M : ℕ := ⌈4 * (ε + 1)⌉₊ with hM
  set K : ℕ := M + 2 with hK
  refine ⟨(K : ℝ) / ε, by positivity, ?_⟩
  intro n hn F hF t ht0 ht1 hμ
  set C : ℝ := (K : ℝ) / ε with hC
  have hCpos : 0 < C := by positivity
  clear_value C
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set s : ℝ := (n : ℝ) ^ (-ε) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hn0 _
  have hs1 : s < 1 := Real.rpow_lt_one_of_one_lt_of_neg hn1 (by linarith)
  set a : ℝ := s * t with ha
  have ha0 : 0 < a := mul_pos hs0 ht0
  have hat : a < t := mul_lt_of_lt_one_left ht0 hs1
  by_contra hcon
  push_neg at hcon
  have hU := univ_mem_of F hF hμ
  have hE := empty_not_mem_of F hF hμ
  set g : ℝ → ℝ := fun q => μFamily q F with hg
  set L : ℝ → ℝ := fun q => -Real.log (g q) with hL
  set ψ : ℝ → ℝ := fun q => L q * q ^ C with hψ
  -- derivative of ψ on the closed interval
  have hderiv : ∀ q ∈ Set.Icc a t, HasDerivAt ψ
      (-(edgeBoundary n q F / g q) * q ^ C + L q * (C * q ^ (C - 1))) q := by
    intro q hq
    have hq0 : 0 < q := lt_of_lt_of_le ha0 hq.1
    have hq1 : q < 1 := lt_of_le_of_lt hq.2 ht1
    have hgq : g q ≠ 0 := (muFamily_pos F hU hq0 hq1).ne'
    have h1 : HasDerivAt g (edgeBoundary n q F) q := russo F hF hq0 hq1
    have h2 : HasDerivAt L (-(edgeBoundary n q F / g q)) q := (h1.log hgq).neg
    have h3 : HasDerivAt (fun x : ℝ => x ^ C) (C * q ^ (C - 1)) q :=
      Real.hasDerivAt_rpow_const (Or.inl hq0.ne')
    exact h2.mul h3
  have hneg : ∀ q ∈ Set.Icc a t,
      -(edgeBoundary n q F / g q) * q ^ C + L q * (C * q ^ (C - 1)) ≤ 0 := by
    intro q hq
    have hq0 : 0 < q := lt_of_lt_of_le ha0 hq.1
    have hq1 : q < 1 := lt_of_le_of_lt hq.2 ht1
    have hgq : 0 < g q := muFamily_pos F hU hq0 hq1
    have hno := hcon q hq.1 hq.2
    unfold IsOptimalWith at hno
    simp only at hno
    rw [rhs_eq C q _ hq0 hq1, not_le] at hno
    -- hno : C * g q * L q / q < edgeBoundary n q F
    have hqC : q ^ C = q * q ^ (C - 1) := by
      rw [← Real.rpow_one_add' hq0.le (by linarith)]
      ring_nf
    have hpow : 0 < q ^ (C - 1) := Real.rpow_pos_of_pos hq0 _
    have key : C * L q < edgeBoundary n q F / g q * q := by
      rw [div_lt_iff₀ hq0] at hno
      rw [div_mul_eq_mul_div, lt_div_iff₀ hgq]
      change C * g q * (-Real.log (g q)) < edgeBoundary n q F * q at hno
      change C * (-Real.log (g q)) * g q < edgeBoundary n q F * q
      linarith
    rw [hqC]
    have : -(edgeBoundary n q F / g q) * (q * q ^ (C - 1)) + L q * (C * q ^ (C - 1))
        = q ^ (C - 1) * (C * L q - edgeBoundary n q F / g q * q) := by ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos hpow.le (by linarith)
  have hanti : AntitoneOn ψ (Set.Icc a t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a t)
    · intro q hq
      exact (hderiv q hq).continuousAt.continuousWithinAt
    · intro q hq
      rw [interior_Icc] at hq
      exact (hderiv q (Set.Ioo_subset_Icc_self hq)).differentiableAt.differentiableWithinAt
    · intro q hq
      rw [interior_Icc] at hq
      rw [(hderiv q (Set.Ioo_subset_Icc_self hq)).deriv]
      exact hneg q (Set.Ioo_subset_Icc_self hq)
  have hmono := hanti ⟨le_refl a, hat.le⟩ ⟨hat.le, le_refl t⟩ hat.le
  -- hmono : ψ t ≤ ψ a
  have hLt : L t = Real.log 2 := by
    change -Real.log (μFamily t F) = Real.log 2
    rw [hμ, one_div, Real.log_inv, neg_neg]
  have hga : s ^ n / 2 ≤ g a := by
    have := muFamily_lower F ha0 hat.le ht1
    rw [hμ, show a / t = s by rw [ha]; field_simp] at this
    change s ^ n / 2 ≤ μFamily a F
    linarith
  have hlogs : Real.log s = -ε * Real.log n := by
    rw [hs, Real.log_rpow hn0]
  have hLa : L a ≤ Real.log 2 + n * ε * Real.log n := by
    change -Real.log (g a) ≤ _
    have hpos : 0 < s ^ n / 2 := by positivity
    have := Real.log_le_log hpos hga
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow, hlogs] at this
    linarith
  have hψa : ψ a = L a * s ^ C * t ^ C := by
    change L a * (s * t) ^ C = _
    rw [Real.mul_rpow hs0.le ht0.le]; ring
  have hψt : ψ t = Real.log 2 * t ^ C := by
    change L t * t ^ C = _
    rw [hLt]
  have htC : 0 < t ^ C := Real.rpow_pos_of_pos ht0 _
  have h1 : Real.log 2 ≤ L a * s ^ C := by
    rw [hψa, hψt] at hmono
    exact le_of_mul_le_mul_right hmono htC
  have hsC : s ^ C * (n : ℝ) ^ K = 1 := by
    rw [hs, ← Real.rpow_mul hn0.le, ← Real.rpow_natCast, ← Real.rpow_add hn0]
    rw [show -ε * C + (K : ℝ) = 0 by rw [hC]; field_simp; ring]
    exact Real.rpow_zero _
  have hnK : (0 : ℝ) < (n : ℝ) ^ K := by positivity
  have h2 : Real.log 2 * (n : ℝ) ^ K ≤ Real.log 2 + n * ε * Real.log n := by
    have hsCpos : 0 < s ^ C := Real.rpow_pos_of_pos hs0 _
    have : Real.log 2 * (n : ℝ) ^ K ≤ L a * s ^ C * (n : ℝ) ^ K :=
      mul_le_mul_of_nonneg_right h1 hnK.le
    rw [mul_assoc, hsC, mul_one] at this
    linarith
  -- numerical contradiction
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hlogn : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos hn0; linarith
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1.le
  have hM4 : 4 * (ε + 1) ≤ (M : ℝ) := Nat.le_ceil _
  have h2M : ((M : ℝ) + 1) ≤ (2 : ℝ) ^ M := by
    have := Nat.lt_two_pow_self (n := M)
    exact_mod_cast this
  have hnM : (2 : ℝ) ^ M ≤ (n : ℝ) ^ M := by
    apply pow_le_pow_left₀ (by norm_num)
    exact_mod_cast hn
  have hnK' : (n : ℝ) ^ K = (n : ℝ) ^ M * (n : ℝ) ^ 2 := by rw [hK, pow_add]
  have hn2 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hbig : (4 * ε + 5) * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ K := by
    rw [hnK']
    have : 4 * ε + 5 ≤ (n : ℝ) ^ M := by linarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hεn : n * ε * Real.log n ≤ ε * (n : ℝ) ^ 2 := by
    have : (n : ℝ) * Real.log n ≤ (n : ℝ) ^ 2 := by
      rw [sq]; exact mul_le_mul_of_nonneg_left hlogn hn0.le
    have := mul_le_mul_of_nonneg_left this hε.le
    linarith
  have hA := mul_le_mul_of_nonneg_left hbig (by linarith : (0 : ℝ) ≤ Real.log 2)
  have hB : (1 / 2 : ℝ) * ((4 * ε + 5) * (n : ℝ) ^ 2) < Real.log 2 * ((4 * ε + 5) * (n : ℝ) ^ 2) :=
    mul_lt_mul_of_pos_right hlog2 (by positivity)
  nlinarith [h2, hA, hB, hεn, hlog2', hn2]

end OMAv6

theorem OMA.solution : type_of% @Mathoverflow10799.mathoverflow_10799.variants.weak_kahn_kalai :=
  OMAv6.main_target
