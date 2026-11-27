import FormalConjectures.ErdosProblems.«888»

-- Problem: Erdős Problem 888 — sarkozy
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/888.lean:70 (declaration Erdos888.erdos_888.variants.sarkozy)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

open Finset Erdos888

lemma cs_bound {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β))
    (U : Finset α) (V : Finset β) (hE : E ⊆ U ×ˢ V) (t : ℕ)
    (hcod : ∀ u ∈ U, ∀ u' ∈ U, u ≠ u' →
      (V.filter (fun v => (u, v) ∈ E ∧ (u', v) ∈ E)).card ≤ t) :
    E.card ^ 2 ≤ V.card * (E.card + t * U.card ^ 2) := by
  have hcard : E.card = ∑ v ∈ V, ∑ u ∈ U, (if (u, v) ∈ E then 1 else 0) := by
    have h1 : E = (U ×ˢ V).filter (fun x => x ∈ E) := by
      ext x
      simp only [mem_filter, iff_and_self]
      exact fun hx => hE hx
    conv_lhs => rw [h1]
    rw [card_filter, sum_product_right]
  have hcard' : E.card = ∑ u ∈ U, ∑ v ∈ V, (if (u, v) ∈ E then 1 else 0) := by
    rw [hcard, sum_comm]
  have hsq : ∑ v ∈ V, (∑ u ∈ U, (if (u, v) ∈ E then 1 else 0)) ^ 2
      ≤ E.card + t * U.card ^ 2 := by
    have e1 : ∑ v ∈ V, (∑ u ∈ U, (if (u, v) ∈ E then 1 else 0)) ^ 2
        = ∑ u ∈ U, ∑ u' ∈ U, ∑ v ∈ V,
          ((if (u, v) ∈ E then 1 else 0) * (if (u', v) ∈ E then 1 else 0) : ℕ) := by
      simp only [sq, sum_mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun u _ => ?_
      rw [sum_comm]
    rw [e1]
    have e2 : ∀ u ∈ U, ∀ u' ∈ U, ∑ v ∈ V,
          ((if (u, v) ∈ E then 1 else 0) * (if (u', v) ∈ E then 1 else 0) : ℕ)
        ≤ (if u = u' then ∑ v ∈ V, (if (u, v) ∈ E then 1 else 0) else 0) + t := by
      intro u hu u' hu'
      by_cases h : u = u'
      · subst h
        rw [if_pos rfl]
        refine le_trans (sum_le_sum fun v _ => ?_) (Nat.le_add_right _ _)
        split_ifs <;> simp
      · rw [if_neg h, zero_add]
        refine le_trans (le_of_eq ?_) (hcod u hu u' hu' h)
        rw [card_filter]
        refine sum_congr rfl fun v _ => ?_
        split_ifs <;> simp_all
    have e3 : ∀ u ∈ U, ∑ u' ∈ U,
        ((if u = u' then ∑ v ∈ V, (if (u, v) ∈ E then 1 else 0) else 0) + t)
        = (∑ v ∈ V, (if (u, v) ∈ E then 1 else 0)) + U.card * t := by
      intro u hu
      rw [sum_add_distrib, sum_ite_eq, if_pos hu, sum_const, smul_eq_mul]
    calc _ ≤ ∑ u ∈ U, ∑ u' ∈ U,
            ((if u = u' then ∑ v ∈ V, (if (u, v) ∈ E then 1 else 0) else 0) + t) :=
          sum_le_sum fun u hu => sum_le_sum fun u' hu' => e2 u hu u' hu'
      _ = E.card + t * U.card ^ 2 := by
          rw [sum_congr rfl e3, sum_add_distrib, ← hcard', sum_const, smul_eq_mul]
          ring
  calc E.card ^ 2 = (∑ v ∈ V, ∑ u ∈ U, (if (u, v) ∈ E then 1 else 0)) ^ 2 := by rw [← hcard]
    _ ≤ V.card * ∑ v ∈ V, (∑ u ∈ U, (if (u, v) ∈ E then 1 else 0)) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ _ := Nat.mul_le_mul_left _ hsq

lemma k222 (X Y Z : Finset ℕ) (H : Finset (ℕ × ℕ × ℕ)) (hH : H ⊆ X ×ˢ (Y ×ˢ Z))
    (hfree : ∀ x x' y y' z z', (x, y, z) ∈ H → (x, y', z') ∈ H → (x', y, z') ∈ H →
      (x', y', z) ∈ H → x = x' ∨ y = y' ∨ z = z')
    (M : ℕ) (hX : M ≤ X.card) (hY : M ≤ Y.card) (hZ : M ≤ Z.card) :
    M * H.card ^ 4 ≤ 6 * (X.card * Y.card * Z.card) ^ 4 := by
  have hcod : ∀ u ∈ X, ∀ u' ∈ X, u ≠ u' →
      ((Y ×ˢ Z).filter (fun v => (u, v) ∈ H ∧ (u', v) ∈ H)).card
        ≤ Nat.sqrt (Z.card * (Y.card * Z.card + Y.card ^ 2)) := by
    intro u _ u' _ huu
    have hGs : (Y ×ˢ Z).filter (fun v => (u, v) ∈ H ∧ (u', v) ∈ H) ⊆ Y ×ˢ Z :=
      filter_subset _ _
    have h1 := cs_bound _ Y Z hGs 1 (by
      intro v hv v' hv' hvv
      rw [card_le_one]
      intro a ha b hb
      have ha' := (mem_filter.mp ha).2
      have hb' := (mem_filter.mp hb).2
      have ha1 := (mem_filter.mp ha'.1).2
      have ha2 := (mem_filter.mp ha'.2).2
      have hb1 := (mem_filter.mp hb'.1).2
      have hb2 := (mem_filter.mp hb'.2).2
      rcases hfree u u' v v' a b ha1.1 hb2.1 hb1.2 ha2.2 with h | h | h
      · exact absurd h huu
      · exact absurd h hvv
      · exact h)
    have hGc := (card_le_card hGs).trans (card_product Y Z).le
    rw [Nat.le_sqrt']
    refine h1.trans (Nat.mul_le_mul_left _ ?_)
    linarith
  have h2 := cs_bound H X (Y ×ˢ Z) hH _ hcod
  rw [card_product] at h2
  have ht2 := Nat.sqrt_le' (Z.card * (Y.card * Z.card + Y.card ^ 2))
  have hexyz : H.card ≤ X.card * Y.card * Z.card := by
    calc H.card ≤ (X ×ˢ (Y ×ˢ Z)).card := card_le_card hH
      _ = X.card * Y.card * Z.card := by rw [card_product, card_product, mul_assoc]
  generalize Nat.sqrt (Z.card * (Y.card * Z.card + Y.card ^ 2)) = t at h2 ht2
  generalize X.card = x at *
  generalize Y.card = y at *
  generalize Z.card = z at *
  generalize H.card = e at *
  have h1 : e ^ 4 ≤ (y * z * (e + t * x ^ 2)) ^ 2 := by
    calc e ^ 4 = (e ^ 2) ^ 2 := by ring
      _ ≤ _ := Nat.pow_le_pow_left h2 2
  have h3 : (e + t * x ^ 2) ^ 2 ≤ 2 * (e ^ 2 + t ^ 2 * x ^ 4) := by
    zify
    nlinarith [sq_nonneg ((e : ℤ) - t * x ^ 2)]
  have h4 : e ^ 2 ≤ (x * y * z) ^ 2 := Nat.pow_le_pow_left hexyz 2
  have h5 : M * (z * (y * z + y ^ 2)) ≤ 2 * (y ^ 2 * z ^ 2) := by
    nlinarith [Nat.mul_le_mul_right (y * z * z) hY, Nat.mul_le_mul_right (y * y * z) hZ]
  have h6 : M * (x * y * z) ^ 2 ≤ x ^ 4 * (y ^ 2 * z ^ 2) := by
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · simp [h0]
    · have h7 : x ^ 3 ≤ x ^ 4 := Nat.pow_le_pow_right h0 (by norm_num)
      calc M * (x * y * z) ^ 2 ≤ x * (x * y * z) ^ 2 := Nat.mul_le_mul_right _ hX
        _ = x ^ 3 * (y ^ 2 * z ^ 2) := by ring
        _ ≤ x ^ 4 * (y ^ 2 * z ^ 2) := Nat.mul_le_mul_right _ h7
  calc M * e ^ 4
      ≤ M * ((y * z) ^ 2 * (2 * ((x * y * z) ^ 2 + z * (y * z + y ^ 2) * x ^ 4))) := by
        refine Nat.mul_le_mul_left _ (h1.trans ?_)
        rw [mul_pow]
        refine Nat.mul_le_mul_left _ (h3.trans ?_)
        exact Nat.mul_le_mul_left _ (Nat.add_le_add h4 (Nat.mul_le_mul_right _ ht2))
    _ = 2 * (y * z) ^ 2 * (M * (x * y * z) ^ 2)
          + 2 * (y * z) ^ 2 * x ^ 4 * (M * (z * (y * z + y ^ 2))) := by ring
    _ ≤ 2 * (y * z) ^ 2 * (x ^ 4 * (y ^ 2 * z ^ 2))
          + 2 * (y * z) ^ 2 * x ^ 4 * (2 * (y ^ 2 * z ^ 2)) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ h6) (Nat.mul_le_mul_left _ h5)
    _ = 6 * (x * y * z) ^ 4 := by ring

lemma minmax {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n) {a b c d : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (h1 : a ≤ b) (h2 : a ≤ c) (h3 : b ≤ d) (h4 : c ≤ d) (hs : ∃ r, a * b * c * d = r * r) :
    a * d = b * c := by
  obtain ⟨r, hr⟩ := hs
  rcases le_total b c with h | h
  · exact hA.2 a ha b hb c hc d hd h1 h h4 ⟨r, hr⟩
  · have := hA.2 a ha c hc b hb d hd h2 h h3 ⟨r, by rw [← hr]; ring⟩
    rw [this]; ring

lemma four_sym {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n) {a b c d : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A) (hs : ∃ r, a * b * c * d = r * r) :
    a * b = c * d ∨ a * c = b * d ∨ a * d = b * c := by
  obtain ⟨r, hr⟩ := hs
  rcases le_total a b with h1 | h1 <;> rcases le_total a c with h2 | h2 <;>
  rcases le_total a d with h3 | h3 <;> rcases le_total b c with h4 | h4 <;>
  rcases le_total b d with h5 | h5 <;> rcases le_total c d with h6 | h6 <;>
  first
  | (have h := minmax hA ha hb hc hd (by omega) (by omega) (by omega) (by omega)
      ⟨r, by rw [← hr]⟩
     right; right; linarith)
  | (have h := minmax hA ha hb hd hc (by omega) (by omega) (by omega) (by omega)
      ⟨r, by rw [← hr]; ring⟩
     right; left; linarith)
  | (have h := minmax hA ha hc hd hb (by omega) (by omega) (by omega) (by omega)
      ⟨r, by rw [← hr]; ring⟩
     left; linarith)
  | (have h := minmax hA hb hc hd ha (by omega) (by omega) (by omega) (by omega)
      ⟨r, by rw [← hr]; ring⟩
     left; linarith)
  | (have h := minmax hA hb ha hd hc (by omega) (by omega) (by omega) (by omega)
      ⟨r, by rw [← hr]; ring⟩
     right; right; linarith)
  | (have h := minmax hA hb ha hc hd (by omega) (by omega) (by omega) (by omega)
      ⟨r, by rw [← hr]; ring⟩
     right; left; linarith)
  | (have h := minmax hA hc hb hd ha (by omega) (by omega) (by omega) (by omega)
      ⟨r, by rw [← hr]; ring⟩
     right; left; linarith)
  | (have h := minmax hA hc ha hd hb (by omega) (by omega) (by omega) (by omega)
      ⟨r, by rw [← hr]; ring⟩
     right; right; linarith)
  | (have h := minmax hA hc ha hb hd (by omega) (by omega) (by omega) (by omega)
      ⟨r, by rw [← hr]; ring⟩
     left; linarith)
  | (have h := minmax hA hd hb hc ha (by omega) (by omega) (by omega) (by omega)
      ⟨r, by rw [← hr]; ring⟩
     right; right; linarith)
  | (have h := minmax hA hd ha hc hb (by omega) (by omega) (by omega) (by omega)
      ⟨r, by rw [← hr]; ring⟩
     right; left; linarith)
  | (have h := minmax hA hd ha hb hc (by omega) (by omega) (by omega) (by omega)
      ⟨r, by rw [← hr]; ring⟩
     left; linarith)

lemma pattern {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n) {k x x' y y' z z' : ℕ}
    (h1 : k * x * y * z ∈ A) (h2 : k * x * y' * z' ∈ A) (h3 : k * x' * y * z' ∈ A)
    (h4 : k * x' * y' * z ∈ A) : x = x' ∨ y = y' ∨ z = z' := by
  have hp1 : 0 < k * x * y * z := (mem_Ioc.mp (hA.1 h1)).1
  have hp2 : 0 < k * x * y' * z' := (mem_Ioc.mp (hA.1 h2)).1
  have hp3 : 0 < k * x' * y * z' := (mem_Ioc.mp (hA.1 h3)).1
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h] at hp1
    · exact h
  have hx : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · simp [h] at hp1
    · exact h
  have hy : 0 < y := by
    rcases Nat.eq_zero_or_pos y with h | h
    · simp [h] at hp1
    · exact h
  have hz : 0 < z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · simp [h] at hp1
    · exact h
  have hy' : 0 < y' := by
    rcases Nat.eq_zero_or_pos y' with h | h
    · simp [h] at hp2
    · exact h
  have hz' : 0 < z' := by
    rcases Nat.eq_zero_or_pos z' with h | h
    · simp [h] at hp2
    · exact h
  have hx' : 0 < x' := by
    rcases Nat.eq_zero_or_pos x' with h | h
    · simp [h] at hp3
    · exact h
  rcases four_sym hA h1 h2 h3 h4 ⟨k * k * x * x' * y * y' * z * z', by ring⟩ with h | h | h
  · left
    have hK : 0 < k * k * y * y' * z * z' := by positivity
    have : x * x * (k * k * y * y' * z * z') = x' * x' * (k * k * y * y' * z * z') := by
      linarith
    exact Nat.mul_self_inj.mp (Nat.eq_of_mul_eq_mul_right hK this)
  · right; left
    have hK : 0 < k * k * x * x' * z * z' := by positivity
    have : y * y * (k * k * x * x' * z * z') = y' * y' * (k * k * x * x' * z * z') := by
      linarith
    exact Nat.mul_self_inj.mp (Nat.eq_of_mul_eq_mul_right hK this)
  · right; right
    have hK : 0 < k * k * x * x' * y * y' := by positivity
    have : z * z * (k * k * x * x' * y * y') = z' * z' * (k * k * x * x' * y * y') := by
      linarith
    exact Nat.mul_self_inj.mp (Nat.eq_of_mul_eq_mul_right hK this)


def cls (j : ℕ) : Finset ℕ := (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime

noncomputable def w (j : ℕ) : ℝ := ((cls j).card : ℝ) / 2 ^ j

lemma cls_mem {j p : ℕ} (hp : p ∈ cls j) : 2 ^ j ≤ p ∧ p < 2 ^ (j + 1) ∧ p.Prime := by
  have := mem_filter.mp hp
  exact ⟨(mem_Ico.mp this.1).1, (mem_Ico.mp this.1).2, this.2⟩

lemma cls_card_le (j : ℕ) : (cls j).card ≤ 2 ^ j := by
  refine (card_filter_le _ _).trans ?_
  rw [Nat.card_Ico, pow_succ]
  omega

lemma w_nonneg (j : ℕ) : 0 ≤ w j := by
  unfold w
  positivity

lemma w_le_one (j : ℕ) : w j ≤ 1 := by
  unfold w
  rw [div_le_one (by positivity)]
  exact_mod_cast cls_card_le j

lemma recip_le (j : ℕ) : ∑ p ∈ cls j, (1 : ℝ) / p ≤ w j := by
  unfold w
  have h1 : ∑ p ∈ cls j, (1 : ℝ) / p ≤ (cls j).card • ((1 : ℝ) / 2 ^ j) := by
    refine sum_le_card_nsmul _ _ _ fun p hp => ?_
    have h := (cls_mem hp).1
    have h' : (2 : ℝ) ^ j ≤ p := by exact_mod_cast h
    exact one_div_le_one_div_of_le (by positivity) h'
  rw [nsmul_eq_mul] at h1
  have e : ((cls j).card : ℝ) * (1 / 2 ^ j) = (cls j).card / 2 ^ j := by ring
  linarith

lemma recip_ge (j : ℕ) : w j / 2 ≤ ∑ p ∈ cls j, (1 : ℝ) / p := by
  unfold w
  have h1 : (cls j).card • ((1 : ℝ) / 2 ^ (j + 1)) ≤ ∑ p ∈ cls j, (1 : ℝ) / p := by
    refine card_nsmul_le_sum _ _ _ fun p hp => ?_
    have h := (cls_mem hp).2.1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (cls_mem hp).2.2.pos
    have h' : (p : ℝ) ≤ 2 ^ (j + 1) := by exact_mod_cast h.le
    exact one_div_le_one_div_of_le hp0 h'
  rw [nsmul_eq_mul] at h1
  have e : ((cls j).card : ℝ) * (1 / 2 ^ (j + 1)) = (cls j).card / 2 ^ j / 2 := by
    rw [pow_succ]
    field_simp
  linarith

lemma primes_below (J : ℕ) :
    ∑ p ∈ (range (2 ^ J)).filter Nat.Prime, (1 : ℝ) / p ≤ ∑ j ∈ range J, w j := by
  induction J with
  | zero =>
    have h0 : (range (2 ^ 0)).filter Nat.Prime = ∅ := by decide
    rw [h0]
    simp
  | succ J ih =>
    have hsplit : (range (2 ^ (J + 1))).filter Nat.Prime
        = (range (2 ^ J)).filter Nat.Prime ∪ cls J := by
      unfold cls
      rw [← filter_union, range_eq_Ico, range_eq_Ico,
        Ico_union_Ico_eq_Ico (Nat.zero_le _)
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J))]
    have hdisj : Disjoint ((range (2 ^ J)).filter Nat.Prime) (cls J) := by
      refine disjoint_left.mpr fun p h1 h2 => ?_
      have h3 := mem_range.mp (mem_filter.mp h1).1
      have h4 := (cls_mem h2).1
      omega
    rw [hsplit, sum_union hdisj, sum_range_succ]
    linarith [recip_le J]

lemma w_unbounded (B : ℝ) : ∃ J, B ≤ ∑ j ∈ range J, w j := by
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (f := Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n))
    (fun n => Set.indicator_nonneg (fun _ _ => by positivity) _)).mp
    not_summable_one_div_on_primes
  obtain ⟨N, hN⟩ := (Filter.tendsto_atTop.mp hdiv B).exists
  refine ⟨N, hN.trans ?_⟩
  have h1 : ∑ i ∈ range N, Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i
      = ∑ p ∈ (range N).filter Nat.Prime, (1 : ℝ) / p := by
    rw [sum_filter]
    refine sum_congr rfl fun i _ => ?_
    simp [Set.indicator_apply]
  rw [h1]
  refine le_trans ?_ (primes_below N)
  refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
  intro p hp
  rw [mem_filter, mem_range] at hp ⊢
  exact ⟨hp.1.trans Nat.lt_two_pow_self, hp.2⟩

noncomputable def hsum (M J : ℕ) : ℝ :=
  ∑ j ∈ range J, (if M ≤ (cls j).card then w j else 0)

lemma hsum_unbounded (M : ℕ) (B : ℝ) : ∃ J, B ≤ hsum M J := by
  obtain ⟨J, hJ⟩ := w_unbounded (B + 2 * M)
  refine ⟨J, ?_⟩
  have h1 : ∑ j ∈ range J, w j
      ≤ ∑ j ∈ range J, ((if M ≤ (cls j).card then w j else 0) + M * (1 / 2 : ℝ) ^ j) := by
    refine sum_le_sum fun j _ => ?_
    split_ifs with hc
    · have h0 : (0 : ℝ) ≤ M * (1 / 2 : ℝ) ^ j := by positivity
      linarith
    · unfold w
      push Not at hc
      have h0 : ((cls j).card : ℝ) ≤ M := by exact_mod_cast hc.le
      rw [zero_add, one_div, inv_pow, ← div_eq_mul_inv]
      gcongr
  rw [sum_add_distrib, ← mul_sum] at h1
  have h2 := sum_geometric_two_le J
  have h3 : (M : ℝ) * ∑ i ∈ range J, (1 / (2 : ℝ)) ^ i ≤ M * 2 :=
    mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg M)
  unfold hsum
  linarith

lemma hsum_mono (M : ℕ) {a b : ℕ} (hab : a ≤ b) : hsum M a ≤ hsum M b := by
  unfold hsum
  refine sum_le_sum_of_subset_of_nonneg (range_mono hab) fun j _ _ => ?_
  split_ifs
  · exact w_nonneg j
  · exact le_rfl

lemma hsum_succ (M J : ℕ) : hsum M (J + 1) ≤ hsum M J + 1 := by
  unfold hsum
  rw [sum_range_succ]
  split_ifs
  · linarith [w_le_one J]
  · linarith

lemma select (M J0 : ℕ) (S : ℝ) (hS : 0 ≤ S) : ∃ G : Finset ℕ, ∃ J1 : ℕ,
    (∀ j ∈ G, J0 ≤ j ∧ j < J1 ∧ M ≤ (cls j).card) ∧
      S ≤ ∑ j ∈ G, w j ∧ ∑ j ∈ G, w j ≤ S + 1 := by
  classical
  have hex : ∃ J, J0 ≤ J ∧ hsum M J0 + S ≤ hsum M J := by
    obtain ⟨J, hJ⟩ := hsum_unbounded M (hsum M J0 + S)
    exact ⟨max J J0, le_max_right _ _, hJ.trans (hsum_mono M (le_max_left _ _))⟩
  obtain ⟨J1, ⟨h1, h2⟩, hmin⟩ : ∃ J1, (J0 ≤ J1 ∧ hsum M J0 + S ≤ hsum M J1) ∧
      ∀ m < J1, ¬ (J0 ≤ m ∧ hsum M J0 + S ≤ hsum M m) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  refine ⟨(Ico J0 J1).filter (fun j => M ≤ (cls j).card), J1, ?_, ?_⟩
  · intro j hj
    rw [mem_filter, mem_Ico] at hj
    exact ⟨hj.1.1, hj.1.2, hj.2⟩
  have hW : ∑ j ∈ (Ico J0 J1).filter (fun j => M ≤ (cls j).card), w j
      = hsum M J1 - hsum M J0 := by
    rw [sum_filter, sum_Ico_eq_sub _ h1]
    rfl
  rw [hW]
  refine ⟨by linarith, ?_⟩
  rcases Nat.eq_or_lt_of_le h1 with heq | hlt
  · rw [← heq]
    linarith
  · have h3 : hsum M (J1 - 1) < hsum M J0 + S := by
      by_contra hcon
      exact hmin (J1 - 1) (by omega) ⟨by omega, not_lt.mp hcon⟩
    have h4 := hsum_succ M (J1 - 1)
    rw [show J1 - 1 + 1 = J1 by omega] at h4
    linarith

lemma totient_prod_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ((Nat.totient (∏ p ∈ P, p) : ℕ) : ℝ)
      ≤ ((∏ p ∈ P, p : ℕ) : ℝ) * Real.exp (-∑ p ∈ P, (1 : ℝ) / p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | insert q P hq ih =>
    have hqp : q.Prime := hP q (mem_insert_self _ _)
    have hP' : ∀ p ∈ P, p.Prime := fun p hp => hP p (mem_insert_of_mem hp)
    have hcop : Nat.Coprime q (∏ p ∈ P, p) := by
      rw [Nat.coprime_prod_right_iff]
      intro p hp
      refine (Nat.coprime_primes hqp (hP' p hp)).mpr (fun h => hq ?_)
      rw [h]
      exact hp
    rw [prod_insert hq, sum_insert hq, Nat.totient_mul hcop, Nat.totient_prime hqp, neg_add,
      Real.exp_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_pred hqp.pos]
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqp.one_le
    have hq0 : (0 : ℝ) < q := by linarith
    have hb : (q : ℝ) - 1 ≤ q * Real.exp (-(1 / (q : ℝ))) := by
      have h0 := Real.add_one_le_exp (-(1 / (q : ℝ)))
      calc (q : ℝ) - 1 = q * (-(1 / (q : ℝ)) + 1) := by
            field_simp
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h0 hq0.le
    have ih' := ih hP'
    calc ((q : ℝ) - 1) * (Nat.totient (∏ p ∈ P, p) : ℝ)
        ≤ (q * Real.exp (-(1 / (q : ℝ))))
          * (((∏ p ∈ P, p : ℕ) : ℝ) * Real.exp (-∑ p ∈ P, (1 : ℝ) / p)) :=
          mul_le_mul hb ih' (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring

def exc (G : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (Ioc 0 n).filter (fun a => ∀ j ∈ G, ∀ p ∈ cls j, ¬ p ∣ a)

lemma exc_bound (G : Finset ℕ) (n : ℕ) :
    ((exc G n).card : ℝ)
      ≤ n * Real.exp (-(∑ j ∈ G, w j) / 2) + ((∏ p ∈ G.biUnion cls, p : ℕ) : ℝ) := by
  classical
  have hP : ∀ p ∈ G.biUnion cls, p.Prime := by
    intro p hp
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp hp
    exact (cls_mem hj).2.2
  have hm0 : (∏ p ∈ G.biUnion cls, p) ≠ 0 :=
    prod_ne_zero_iff.mpr fun p hp => (hP p hp).ne_zero
  have hsub : exc G n ⊆ (Ico 1 (1 + n)).filter (Nat.Coprime (∏ p ∈ G.biUnion cls, p)) := by
    intro a ha
    unfold exc at ha
    rw [mem_filter, mem_Ioc] at ha
    rw [mem_filter, mem_Ico]
    refine ⟨by omega, ?_⟩
    rw [Nat.coprime_prod_left_iff]
    intro p hp
    obtain ⟨j, hj, hpj⟩ := mem_biUnion.mp hp
    exact ((cls_mem hpj).2.2.coprime_iff_not_dvd).mpr (ha.2 j hj p hpj)
  have hc := (card_le_card hsub).trans (Nat.Ico_filter_coprime_le 1 n hm0)
  have ht := totient_prod_le _ hP
  have hsumP : ∑ j ∈ G, w j / 2 ≤ ∑ p ∈ G.biUnion cls, (1 : ℝ) / p := by
    rw [sum_biUnion]
    · exact sum_le_sum fun j _ => recip_ge j
    · intro i _ j _ hij
      change Disjoint (cls i) (cls j)
      refine disjoint_left.mpr fun p hpi hpj => hij ?_
      have h1 := cls_mem hpi
      have h2 := cls_mem hpj
      exact (Nat.log_eq_of_pow_le_of_lt_pow h1.1 h1.2.1).symm.trans
        (Nat.log_eq_of_pow_le_of_lt_pow h2.1 h2.2.1)
  generalize (∏ p ∈ G.biUnion cls, p) = m at hm0 hc ht
  have hc' : ((exc G n).card : ℝ) ≤ (Nat.totient m : ℝ) * (((n / m : ℕ) : ℝ) + 1) := by
    exact_mod_cast hc
  have hexp : Real.exp (-∑ p ∈ G.biUnion cls, (1 : ℝ) / p)
      ≤ Real.exp (-(∑ j ∈ G, w j) / 2) := by
    apply Real.exp_le_exp.mpr
    rw [← sum_div] at hsumP
    linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  have hdiv : ((n / m : ℕ) : ℝ) ≤ n / m := Nat.cast_div_le
  have hφm : (Nat.totient m : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hφ0 : (0 : ℝ) ≤ Nat.totient m := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hratio : (Nat.totient m : ℝ) / m ≤ Real.exp (-(∑ j ∈ G, w j) / 2) := by
    rw [div_le_iff₀ hmpos]
    calc (Nat.totient m : ℝ) ≤ m * Real.exp (-∑ p ∈ G.biUnion cls, (1 : ℝ) / p) := ht
      _ ≤ m * Real.exp (-(∑ j ∈ G, w j) / 2) := mul_le_mul_of_nonneg_left hexp hmpos.le
      _ = _ := mul_comm _ _
  calc ((exc G n).card : ℝ) ≤ (Nat.totient m : ℝ) * (((n / m : ℕ) : ℝ) + 1) := hc'
    _ ≤ (Nat.totient m : ℝ) * (n / m + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hφ0
    _ = n * ((Nat.totient m : ℝ) / m) + Nat.totient m := by
        field_simp
    _ ≤ n * Real.exp (-(∑ j ∈ G, w j) / 2) + m :=
        add_le_add (mul_le_mul_of_nonneg_left hratio hn0) hφm

abbrev Hset (A : Finset ℕ) (k j1 j2 j3 : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (cls j1 ×ˢ (cls j2 ×ˢ cls j3)).filter (fun q => k * q.1 * q.2.1 * q.2.2 ∈ A)

lemma Hset_bound {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n) (M : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hM : 6 ≤ M * δ ^ 4) (k j1 j2 j3 : ℕ) (h1 : M ≤ (cls j1).card)
    (h2 : M ≤ (cls j2).card) (h3 : M ≤ (cls j3).card) :
    ((Hset A k j1 j2 j3).card : ℝ)
      ≤ δ * (((cls j1).card : ℝ) * (cls j2).card * (cls j3).card) := by
  have key := k222 (cls j1) (cls j2) (cls j3) (Hset A k j1 j2 j3) (filter_subset _ _)
    (fun x x' y y' z z' a b c d => pattern hA (mem_filter.mp a).2 (mem_filter.mp b).2
      (mem_filter.mp c).2 (mem_filter.mp d).2) M h1 h2 h3
  have keyR : (M : ℝ) * ((Hset A k j1 j2 j3).card : ℝ) ^ 4
      ≤ 6 * (((cls j1).card : ℝ) * (cls j2).card * (cls j3).card) ^ 4 := by
    exact_mod_cast key
  generalize ((Hset A k j1 j2 j3).card : ℝ) = e at keyR ⊢
  have hc0 : (0 : ℝ) ≤ ((cls j1).card : ℝ) * (cls j2).card * (cls j3).card := by positivity
  generalize ((cls j1).card : ℝ) * (cls j2).card * (cls j3).card = c at keyR hc0 ⊢
  by_contra hcon
  push Not at hcon
  have h4 : (δ * c) ^ 4 < e ^ 4 := pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
  have hMpos : (0 : ℝ) < M := by
    by_contra h
    have h0 : (M : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg M)
    rw [h0] at hM
    linarith
  have h5 := mul_lt_mul_of_pos_left h4 hMpos
  have h6 := mul_le_mul_of_nonneg_right hM (by positivity : (0 : ℝ) ≤ c ^ 4)
  have h7 : (M : ℝ) * (δ * c) ^ 4 = M * δ ^ 4 * c ^ 4 := by ring
  linarith

abbrev Bset (A : Finset ℕ) (n : ℕ) (G1 G2 G3 : Finset ℕ) : Finset ℕ :=
  (G1 ×ˢ (G2 ×ˢ G3)).biUnion (fun J =>
    (Ioc 0 (n / 2 ^ (J.1 + J.2.1 + J.2.2))).biUnion (fun k =>
      (Hset A k J.1 J.2.1 J.2.2).image (fun q => k * q.1 * q.2.1 * q.2.2)))

lemma cover {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n) (M : ℕ)
    (G1 G2 G3 : Finset ℕ) (J1 J2 : ℕ)
    (h1 : ∀ j ∈ G1, j < J1 ∧ M ≤ (cls j).card)
    (h2 : ∀ j ∈ G2, J1 ≤ j ∧ j < J2 ∧ M ≤ (cls j).card)
    (h3 : ∀ j ∈ G3, J2 ≤ j ∧ M ≤ (cls j).card) :
    A ⊆ exc G1 n ∪ exc G2 n ∪ exc G3 n ∪ Bset A n G1 G2 G3 := by
  intro a ha
  have han := mem_Ioc.mp (hA.1 ha)
  by_cases e1 : a ∈ exc G1 n
  · simp [e1]
  by_cases e2 : a ∈ exc G2 n
  · simp [e2]
  by_cases e3 : a ∈ exc G3 n
  · simp [e3]
  have f : ∀ G, a ∉ exc G n → ∃ j ∈ G, ∃ p ∈ cls j, p ∣ a := by
    intro G hG
    by_contra hcon
    push Not at hcon
    exact hG (mem_filter.mpr ⟨hA.1 ha, hcon⟩)
  obtain ⟨j1, hj1, p1, hp1, hd1⟩ := f G1 e1
  obtain ⟨j2, hj2, p2, hp2, hd2⟩ := f G2 e2
  obtain ⟨j3, hj3, p3, hp3, hd3⟩ := f G3 e3
  have c1 := cls_mem hp1
  have c2 := cls_mem hp2
  have c3 := cls_mem hp3
  have lt12 : p1 < p2 := by
    calc p1 < 2 ^ (j1 + 1) := c1.2.1
      _ ≤ 2 ^ j2 := Nat.pow_le_pow_right (by norm_num) (by
          have := (h1 j1 hj1).1
          have := (h2 j2 hj2).1
          omega)
      _ ≤ p2 := c2.1
  have lt23 : p2 < p3 := by
    calc p2 < 2 ^ (j2 + 1) := c2.2.1
      _ ≤ 2 ^ j3 := Nat.pow_le_pow_right (by norm_num) (by
          have := (h2 j2 hj2).2.1
          have := (h3 j3 hj3).1
          omega)
      _ ≤ p3 := c3.1
  have cop12 : Nat.Coprime p1 p2 := (Nat.coprime_primes c1.2.2 c2.2.2).mpr (by omega)
  have cop13 : Nat.Coprime p1 p3 := (Nat.coprime_primes c1.2.2 c3.2.2).mpr (by omega)
  have cop23 : Nat.Coprime p2 p3 := (Nat.coprime_primes c2.2.2 c3.2.2).mpr (by omega)
  have d12 : p1 * p2 ∣ a := cop12.mul_dvd_of_dvd_of_dvd hd1 hd2
  have d123 : p1 * p2 * p3 ∣ a :=
    (Nat.Coprime.mul_left cop13 cop23).mul_dvd_of_dvd_of_dvd d12 hd3
  obtain ⟨k, hk⟩ := d123
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk
      omega
    · exact h
  have hkle : k ≤ n / 2 ^ (j1 + j2 + j3) := by
    rw [Nat.le_div_iff_mul_le (by positivity)]
    calc k * 2 ^ (j1 + j2 + j3) = 2 ^ j1 * 2 ^ j2 * 2 ^ j3 * k := by ring
      _ ≤ p1 * p2 * p3 * k :=
          Nat.mul_le_mul_right k (Nat.mul_le_mul (Nat.mul_le_mul c1.1 c2.1) c3.1)
      _ = a := hk.symm
      _ ≤ n := han.2
  have hkeq : k * p1 * p2 * p3 = a := by
    rw [hk]
    ring
  refine mem_union_right _ ?_
  refine mem_biUnion.mpr ⟨(j1, j2, j3), ?_, mem_biUnion.mpr ⟨k, mem_Ioc.mpr ⟨hk0, hkle⟩,
    mem_image.mpr ⟨(p1, p2, p3), mem_filter.mpr ⟨?_, ?_⟩, hkeq⟩⟩⟩
  · exact mem_product.mpr ⟨hj1, mem_product.mpr ⟨hj2, hj3⟩⟩
  · exact mem_product.mpr ⟨hp1, mem_product.mpr ⟨hp2, hp3⟩⟩
  · change k * p1 * p2 * p3 ∈ A
    rw [hkeq]
    exact ha

lemma Bset_card {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n) (M : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hM : 6 ≤ M * δ ^ 4) (G1 G2 G3 : Finset ℕ)
    (h1 : ∀ j ∈ G1, M ≤ (cls j).card) (h2 : ∀ j ∈ G2, M ≤ (cls j).card)
    (h3 : ∀ j ∈ G3, M ≤ (cls j).card) :
    ((Bset A n G1 G2 G3).card : ℝ)
      ≤ n * δ * ((∑ j ∈ G1, w j) * (∑ j ∈ G2, w j) * (∑ j ∈ G3, w j)) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  calc ((Bset A n G1 G2 G3).card : ℝ)
      ≤ ∑ J ∈ G1 ×ˢ (G2 ×ˢ G3), ∑ k ∈ Ioc 0 (n / 2 ^ (J.1 + J.2.1 + J.2.2)),
          ((Hset A k J.1 J.2.1 J.2.2).card : ℝ) := by
        have h0 : (Bset A n G1 G2 G3).card
            ≤ ∑ J ∈ G1 ×ˢ (G2 ×ˢ G3), ∑ k ∈ Ioc 0 (n / 2 ^ (J.1 + J.2.1 + J.2.2)),
              (Hset A k J.1 J.2.1 J.2.2).card :=
          card_biUnion_le.trans (sum_le_sum fun J _ =>
            card_biUnion_le.trans (sum_le_sum fun k _ => card_image_le))
        exact_mod_cast h0
    _ ≤ ∑ J ∈ G1 ×ˢ (G2 ×ˢ G3), n * δ * (w J.1 * w J.2.1 * w J.2.2) := by
        refine sum_le_sum fun J hJ => ?_
        have hJ1 := (mem_product.mp hJ).1
        have hJ2 := (mem_product.mp (mem_product.mp hJ).2).1
        have hJ3 := (mem_product.mp (mem_product.mp hJ).2).2
        have b : ∀ k ∈ Ioc 0 (n / 2 ^ (J.1 + J.2.1 + J.2.2)),
            ((Hset A k J.1 J.2.1 J.2.2).card : ℝ)
              ≤ δ * (((cls J.1).card : ℝ) * (cls J.2.1).card * (cls J.2.2).card) :=
          fun k _ => Hset_bound hA M δ hδ hM k _ _ _ (h1 _ hJ1) (h2 _ hJ2) (h3 _ hJ3)
        refine (sum_le_sum b).trans ?_
        rw [sum_const, nsmul_eq_mul, Nat.card_Ioc, Nat.sub_zero]
        have hdiv : ((n / 2 ^ (J.1 + J.2.1 + J.2.2) : ℕ) : ℝ)
            ≤ (n : ℝ) / (2 : ℝ) ^ (J.1 + J.2.1 + J.2.2) := by
          have h0 : ((n / 2 ^ (J.1 + J.2.1 + J.2.2) : ℕ) : ℝ)
              ≤ ((n : ℕ) : ℝ) / ((2 ^ (J.1 + J.2.1 + J.2.2) : ℕ) : ℝ) := Nat.cast_div_le
          push_cast at h0
          exact h0
        have hnn : (0 : ℝ)
            ≤ δ * (((cls J.1).card : ℝ) * (cls J.2.1).card * (cls J.2.2).card) := by
          positivity
        refine (mul_le_mul_of_nonneg_right hdiv hnn).trans (le_of_eq ?_)
        unfold w
        rw [pow_add, pow_add]
        field_simp
    _ = n * δ * ((∑ j ∈ G1, w j) * (∑ j ∈ G2, w j) * (∑ j ∈ G3, w j)) := by
        rw [← mul_sum]
        congr 1
        have h0 : (∑ j ∈ G1, w j) * (∑ j ∈ G2, w j) * (∑ j ∈ G3, w j)
            = ∑ x ∈ G1, ∑ y ∈ G2, ∑ z ∈ G3, w x * w y * w z := by
          rw [sum_mul_sum, sum_mul]
          refine sum_congr rfl fun x _ => ?_
          rw [sum_mul]
          refine sum_congr rfl fun y _ => ?_
          rw [mul_sum]
        rw [sum_product]
        simp only [sum_product]
        exact h0.symm

lemma main (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset ℕ,
    RequiredCondition A n → (A.card : ℝ) ≤ ε * n := by
  obtain ⟨S, hS, hS0⟩ : ∃ S : ℝ, S = 2 * |Real.log (ε / 8)| ∧ 0 ≤ S :=
    ⟨_, rfl, by positivity⟩
  have hexpS : Real.exp (-S / 2) ≤ ε / 8 := by
    have h0 : -S / 2 = -|Real.log (ε / 8)| := by
      rw [hS]
      ring
    rw [h0]
    calc Real.exp (-|Real.log (ε / 8)|) ≤ Real.exp (Real.log (ε / 8)) :=
          Real.exp_le_exp.mpr (neg_abs_le _)
      _ = ε / 8 := Real.exp_log (by positivity)
  obtain ⟨δ, hδdef, hδ⟩ : ∃ δ : ℝ, δ = ε / (4 * (S + 1) ^ 3) ∧ 0 < δ :=
    ⟨_, rfl, by positivity⟩
  obtain ⟨M, hM⟩ := exists_nat_ge (6 / δ ^ 4)
  have hM' : 6 ≤ M * δ ^ 4 := by rwa [div_le_iff₀ (by positivity)] at hM
  obtain ⟨G1, J1, hG1, hl1, hu1⟩ := select M 0 S hS0
  obtain ⟨G2, J2, hG2, hl2, hu2⟩ := select M J1 S hS0
  obtain ⟨G3, J3, hG3, hl3, hu3⟩ := select M J2 S hS0
  obtain ⟨N, hN⟩ := exists_nat_ge (8 * (((∏ p ∈ G1.biUnion cls, p : ℕ) : ℝ)
    + ((∏ p ∈ G2.biUnion cls, p : ℕ) : ℝ) + ((∏ p ∈ G3.biUnion cls, p : ℕ) : ℝ)) / ε)
  refine ⟨N, fun n hn A hA => ?_⟩
  have hsub := cover hA M G1 G2 G3 J1 J2 (fun j hj => ⟨(hG1 j hj).2.1, (hG1 j hj).2.2⟩)
    (fun j hj => hG2 j hj) (fun j hj => ⟨(hG3 j hj).1, (hG3 j hj).2.2⟩)
  have hB := Bset_card (n := n) hA M δ hδ hM' G1 G2 G3 (fun j hj => (hG1 j hj).2.2)
    (fun j hj => (hG2 j hj).2.2) (fun j hj => (hG3 j hj).2.2)
  have x1 := exc_bound G1 n
  have x2 := exc_bound G2 n
  have x3 := exc_bound G3 n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hexp : ∀ W : ℝ, S ≤ W → (n : ℝ) * Real.exp (-W / 2) ≤ n * (ε / 8) := fun W hW =>
    mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr (by linarith)).trans hexpS) hn0
  have y1 := hexp _ hl1
  have y2 := hexp _ hl2
  have y3 := hexp _ hl3
  have hn' := hN.trans (by exact_mod_cast hn : (N : ℝ) ≤ n)
  rw [div_le_iff₀ hε] at hn'
  have hprod : (∑ j ∈ G1, w j) * (∑ j ∈ G2, w j) * (∑ j ∈ G3, w j) ≤ (S + 1) ^ 3 := by
    calc (∑ j ∈ G1, w j) * (∑ j ∈ G2, w j) * (∑ j ∈ G3, w j)
        ≤ (S + 1) * (S + 1) * (S + 1) :=
          mul_le_mul (mul_le_mul hu1 hu2 (by linarith) (by linarith)) hu3 (by linarith)
            (by positivity)
      _ = (S + 1) ^ 3 := by ring
  have hδS : δ * (S + 1) ^ 3 = ε / 4 := by
    rw [hδdef]
    field_simp
  have hB' : (n : ℝ) * δ * ((∑ j ∈ G1, w j) * (∑ j ∈ G2, w j) * (∑ j ∈ G3, w j))
      ≤ n * (ε / 4) := by
    calc (n : ℝ) * δ * ((∑ j ∈ G1, w j) * (∑ j ∈ G2, w j) * (∑ j ∈ G3, w j))
        ≤ n * δ * (S + 1) ^ 3 := mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = n * (ε / 4) := by rw [mul_assoc, hδS]
  have hcard : (A.card : ℝ) ≤ ((exc G1 n).card : ℝ) + (exc G2 n).card + (exc G3 n).card
      + (Bset A n G1 G2 G3).card := by
    have h0 : A.card ≤ (exc G1 n).card + (exc G2 n).card + (exc G3 n).card
        + (Bset A n G1 G2 G3).card :=
      (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_right
        ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)) _))
    exact_mod_cast h0
  linarith

end OMA

open Erdos888 in
open scoped Classical in
theorem OMA.solution : type_of% @Erdos888.erdos_888.variants.sarkozy := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨N, hN⟩ := OMA.main c hc
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hp0 : p n 0 := ⟨∅, ⟨Finset.empty_subset _, by simp⟩, Finset.card_empty⟩
  obtain ⟨A, hA, hcard⟩ := Nat.findGreatest_spec (P := p n) (Nat.zero_le n) hp0
  rw [Real.norm_natCast, Real.norm_natCast, ← hcard]
  exact hN n hn A hA
