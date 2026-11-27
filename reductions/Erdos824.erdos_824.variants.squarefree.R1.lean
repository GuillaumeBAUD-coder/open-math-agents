import FormalConjectures.ErdosProblems.«824»

-- Reduction Erdos824.erdos_824.variants.squarefree.R1 of Erdős Problem 824 — squarefree
-- Credit: @marcusbuffett
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/- Adapted from Shisheng Li and Zhong Zhuang, daizisheng/erdos-824,
commit b4b7099bb8ab9c1c7fc61dae18a73cdbe503fe5a, MIT license.
Their checked conditional bound counts coprime pairs. Here the two products of
distinct primes left after removing the common factors are proved squarefree.

Copyright (c) 2026 Shisheng Li and Zhong Zhuang

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR
OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE
OR OTHER DEALINGS IN THE SOFTWARE.
-/

namespace OMA.R_Erdos824_erdos_824_variants_squarefree_R1

open Finset ArithmeticFunction Filter

def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1/4 → ∀ η : ℝ, 0 < η → ∃ y0 : ℝ, ∀ y : ℝ, y0 ≤ y →
    (y ^ (1 - η) : ℝ) ≤ (((Finset.Iic ⌊5*y⌋₊).filter
        (fun p => p.Prime ∧ ∀ q ∈ (p+1).primeFactors, ((q:ℕ):ℝ) ≤ y ^ δ)).card : ℝ)

def H2 : Prop := ∀ (P : Finset ℕ) (Y s k x : ℕ),
    (∀ p ∈ P, p ≤ Y) → (∀ p ∈ P, ∀ q ∈ (p+1).primeFactors, q ≤ s) →
    (Y+1)^k ≤ x →
    ((P.powersetCard k).image (fun T => ∏ p ∈ T, (p + 1))).card ≤ (Nat.log 2 x + 1)^(s+1)

lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  have := sigma_one_apply_prime_pow (i := 1) hp
  simpa [Finset.sum_range_succ, add_comm] using this

lemma sigma_prod {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) : sigma 1 (∏ p ∈ T, p) = (∏ p ∈ T, (p + 1)) := by
  rw [isMultiplicative_sigma.map_prod_of_prime T hT]
  exact Finset.prod_congr rfl (fun p hp => sigma_one_prime (hT p hp))

lemma tau_pos (T : Finset ℕ) : 0 < (∏ p ∈ T, (p + 1)) := prod_pos (fun p _ => Nat.succ_pos p)

/-- Cauchy–Schwarz / pigeonhole: `#F^2 ≤ #f(F) * #{(a,b) ∈ F² : f a = f b}`. -/
lemma cs_pairs {α β : Type*} [DecidableEq α] [DecidableEq β] (F : Finset α) (f : α → β) :
    F.card ^ 2 ≤ (F.image f).card * ((F ×ˢ F).filter (fun e => f e.1 = f e.2)).card := by
  have h1 : F.card = ∑ s ∈ F.image f, (F.filter (fun a => f a = s)).card :=
    card_eq_sum_card_image f F
  have h2 : ((F ×ˢ F).filter (fun e => f e.1 = f e.2)).card
      = ∑ s ∈ F.image f, (F.filter (fun a => f a = s)).card ^ 2 := by
    rw [card_eq_sum_card_fiberwise (f := fun e => f e.1) (t := F.image f)]
    · apply sum_congr rfl
      intro s _
      rw [sq, ← card_product]
      congr 1
      ext ⟨a, b⟩
      simp only [mem_filter, mem_product]
      constructor
      · rintro ⟨⟨⟨ha, hb⟩, hab⟩, hs⟩
        exact ⟨⟨ha, hs⟩, hb, hab ▸ hs⟩
      · rintro ⟨⟨ha, hs⟩, hb, hs'⟩
        exact ⟨⟨⟨ha, hb⟩, hs.trans hs'.symm⟩, hs⟩
    · intro e he
      simp only [coe_filter, Set.mem_ofPred_eq, mem_product] at he
      exact mem_coe.2 (mem_image_of_mem f he.1.1)
  rw [h1, h2]
  exact sq_sum_le_card_mul_sum_sq

/-- Pairs of `k`-subsets sharing at least `t` elements. -/
lemma card_bad (P : Finset ℕ) (k t : ℕ) :
    (((P.powersetCard k) ×ˢ (P.powersetCard k)).filter (fun e => t ≤ (e.1 ∩ e.2).card)).card
      ≤ (P.powersetCard k).card * (k.choose t * P.card.choose (k - t)) := by
  set F := P.powersetCard k
  have hsub : ((F ×ˢ F).filter (fun e => t ≤ (e.1 ∩ e.2).card)) ⊆
      F.biUnion (fun T => (T.powersetCard t).biUnion
        (fun W => ({T} : Finset (Finset ℕ)) ×ˢ (F.filter (fun T' => W ⊆ T')))) := by
    rintro ⟨T, T'⟩ he
    simp only [mem_filter, mem_product] at he
    obtain ⟨W, hW, hWc⟩ := exists_subset_card_eq he.2
    simp only [mem_biUnion, mem_product, mem_singleton, mem_filter, mem_powersetCard]
    exact ⟨T, he.1.1, W, ⟨hW.trans inter_subset_left, hWc⟩, rfl, he.1.2,
      hW.trans inter_subset_right⟩
  refine (card_le_card hsub).trans ?_
  refine card_biUnion_le.trans ?_
  rw [← smul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro T hT
  refine card_biUnion_le.trans ?_
  have hTc : T.card = k := (mem_powersetCard.1 hT).2
  have hc : (T.powersetCard t).card = k.choose t := by rw [card_powersetCard, hTc]
  rw [← hc, ← smul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro W hW
  rw [card_product, card_singleton, one_mul]
  have hWt : W.card = t := (mem_powersetCard.1 hW).2
  rw [← card_powersetCard]
  apply card_le_card_of_injOn (fun T' => T' \ W)
  · intro T' hT'
    simp only [coe_filter, Set.mem_ofPred_eq, mem_powersetCard, F] at hT'
    simp only [mem_coe, mem_powersetCard]
    obtain ⟨⟨hT'P, hT'c⟩, hWT'⟩ := hT'
    exact ⟨sdiff_subset.trans hT'P, by rw [card_sdiff_of_subset hWT', hT'c, hWt]⟩
  · intro A hA B hB hAB
    simp only [coe_filter, Set.mem_ofPred_eq] at hA hB
    simp only at hAB
    rw [← sdiff_union_of_subset hA.2, ← sdiff_union_of_subset hB.2, hAB]

section primes

variable {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
include hP

lemma pf_prod {S : Finset ℕ} (hS : S ⊆ P) : (∏ p ∈ S, p).primeFactors = S :=
  Nat.primeFactors_prod (fun p hp => hP p (hS hp))

lemma prod_pos' {S : Finset ℕ} (hS : S ⊆ P) : 0 < ∏ p ∈ S, p :=
  prod_pos (fun p hp => (hP p (hS hp)).pos)

lemma sigma_prod' {S : Finset ℕ} (hS : S ⊆ P) : sigma 1 (∏ p ∈ S, p) = (∏ p ∈ S, (p + 1)) :=
  sigma_prod (fun p hp => hP p (hS hp))

end primes

private lemma squarefree_prime_product (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    Squarefree (∏ p ∈ S, p) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have hprime := hS p (mem_insert_self p S)
    have hrest : ∀ q ∈ S, Nat.Prime q := fun q hq => hS q (mem_insert_of_mem hq)
    rw [prod_insert hp, Nat.squarefree_mul]
    · exact ⟨hprime.prime.squarefree, ih hrest⟩
    · apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hprime (hrest q hq)).mpr fun he => hp (he ▸ hq)


/-- Pairs of `k`-subsets with equal `τ` sharing fewer than `t` elements inject into
`(pairs counted by Erdos824.hSquarefree x) × [1, Y^t] × Bool`. -/
lemma card_good (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Y k t x : ℕ)
    (hY : ∀ p ∈ P, p ≤ Y) (hx : (Y+1)^k ≤ x) (htk : t ≤ k) :
    (((P.powersetCard k) ×ˢ (P.powersetCard k)).filter
        (fun e => (∏ p ∈ e.1, (p + 1)) = (∏ p ∈ e.2, (p + 1)) ∧ (e.1 ∩ e.2).card < t)).card ≤ Erdos824.hSquarefree x * (Y^t * 2) := by
  classical
  set F := P.powersetCard k
  let u : Finset ℕ × Finset ℕ → ℕ := fun e => ∏ p ∈ e.1 \ e.2, p
  let v : Finset ℕ × Finset ℕ → ℕ := fun e => ∏ p ∈ e.2 \ e.1, p
  let g : Finset ℕ × Finset ℕ → ℕ := fun e => ∏ p ∈ e.1 ∩ e.2, p
  let φ : Finset ℕ × Finset ℕ → (ℕ × ℕ) × (ℕ × Bool) := fun e =>
    ((min (u e) (v e), max (u e) (v e)), (g e, decide (u e < v e)))
  let H := (Finset.Ico 1 x ×ˢ Finset.Ico 1 x).filter
    (fun p => p.1 < p.2 ∧ Squarefree p.1 ∧ Squarefree p.2 ∧ sigma 1 p.1 = sigma 1 p.2)
  have hH : Erdos824.hSquarefree x = H.card := rfl
  have hcard : (H ×ˢ (Icc 1 (Y^t) ×ˢ (univ : Finset Bool))).card = Erdos824.hSquarefree x * (Y^t * 2) := by
    simp [card_product, hH]
  rw [← hcard]
  apply card_le_card_of_injOn φ
  · rintro ⟨T, T'⟩ he
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_powersetCard, F] at he
    obtain ⟨⟨⟨hTP, hTk⟩, hT'P, hT'k⟩, hτ, hlt⟩ := he
    have hsd : ((T \ T').card) + (T ∩ T').card = k := by rw [card_sdiff_add_card_inter, hTk]
    have hsd' : ((T' \ T).card) + (T ∩ T').card = k := by
      rw [inter_comm, card_sdiff_add_card_inter, hT'k]
    have hne : (T \ T').Nonempty := by
      rw [← card_pos]; omega
    have hne' : (T' \ T).Nonempty := by
      rw [← card_pos]; omega
    have hk0 : k ≠ 0 := by omega
    have hA : T \ T' ⊆ P := sdiff_subset.trans hTP
    have hB : T' \ T ⊆ P := sdiff_subset.trans hT'P
    have hC : T ∩ T' ⊆ P := inter_subset_left.trans hTP
    obtain ⟨p0, hp0⟩ := hne
    have hY1 : 1 ≤ Y := le_trans (hP p0 (hA hp0)).one_lt.le (hY p0 (hA hp0))
    -- bounds on the products
    have hbound : ∀ S ⊆ P, (∏ p ∈ S, p) ≤ Y ^ S.card := fun S hS =>
      prod_le_pow_card _ _ _ (fun p hp => hY p (hS hp))
    have hlt_x : ∀ S ⊆ P, S.card ≤ k → (∏ p ∈ S, p) < x := by
      intro S hS hSk
      calc (∏ p ∈ S, p) ≤ Y ^ S.card := hbound S hS
        _ ≤ Y ^ k := Nat.pow_le_pow_right hY1 hSk
        _ < (Y+1)^k := Nat.pow_lt_pow_left (Nat.lt_succ_self Y) hk0
        _ ≤ x := hx
    have hu_x : u (T, T') < x := show (∏ p ∈ T \ T', p) < x from hlt_x _ hA (by omega)
    have hv_x : v (T, T') < x := show (∏ p ∈ T' \ T, p) < x from hlt_x _ hB (by omega)
    have hu1 : 1 ≤ u (T, T') := prod_pos' hP hA
    have hv1 : 1 ≤ v (T, T') := prod_pos' hP hB
    have huv : u (T, T') ≠ v (T, T') := by
      intro heq
      have h1 := pf_prod hP hA
      have h2 := pf_prod hP hB
      have : T \ T' = T' \ T := by
        rw [← h1, ← h2]; exact congrArg Nat.primeFactors heq
      have hp0' : p0 ∈ T' \ T := this ▸ hp0
      exact (mem_sdiff.1 hp0).2 (mem_sdiff.1 hp0').1
    have hsu : Squarefree (u (T, T')) := squarefree_prime_product _ (fun p hp => hP p (hA hp))
    have hsv : Squarefree (v (T, T')) := squarefree_prime_product _ (fun p hp => hP p (hB hp))
    have hsig : sigma 1 (u (T, T')) = sigma 1 (v (T, T')) := by
      show sigma 1 (∏ p ∈ T \ T', p) = sigma 1 (∏ p ∈ T' \ T, p)
      rw [sigma_prod' hP hA, sigma_prod' hP hB]
      have e1 : (∏ p ∈ (T ∩ T'), (p + 1)) * (∏ p ∈ (T \ T'), (p + 1)) = (∏ p ∈ T, (p + 1)) := prod_inter_mul_prod_sdiff T T' _
      have e2 : (∏ p ∈ (T ∩ T'), (p + 1)) * (∏ p ∈ (T' \ T), (p + 1)) = (∏ p ∈ T', (p + 1)) := by
        rw [inter_comm]; exact prod_inter_mul_prod_sdiff T' T _
      exact Nat.eq_of_mul_eq_mul_left (tau_pos _) (by rw [e1, e2]; exact hτ)
    have hg : g (T, T') ∈ Icc 1 (Y^t) := by
      rw [mem_Icc]
      exact ⟨prod_pos' hP hC, (hbound _ hC).trans (Nat.pow_le_pow_right hY1 hlt.le)⟩
    simp only [φ, coe_product, Set.mem_prod, mem_coe, mem_univ, and_true, H,
      mem_filter, mem_product, mem_Ico]
    refine ⟨?_, hg⟩
    rcases lt_or_gt_of_ne huv with hl | hl
    · rw [min_eq_left hl.le, max_eq_right hl.le]
      exact ⟨⟨⟨hu1, hu_x⟩, hv1, hv_x⟩, hl, hsu, hsv, hsig⟩
    · rw [min_eq_right hl.le, max_eq_left hl.le]
      exact ⟨⟨⟨hv1, hv_x⟩, hu1, hu_x⟩, hl, hsv, hsu, hsig.symm⟩
  · rintro ⟨T1, T1'⟩ he1 ⟨T2, T2'⟩ he2 hφ
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_powersetCard, F] at he1 he2
    simp only [φ, Prod.mk.injEq] at hφ
    obtain ⟨⟨hmin, hmax⟩, hg, hdec⟩ := hφ
    have huv : u (T1, T1') = u (T2, T2') ∧ v (T1, T1') = v (T2, T2') := by
      by_cases h1 : u (T1, T1') < v (T1, T1')
      · have h2 : u (T2, T2') < v (T2, T2') := by simpa [h1] using hdec
        rw [min_eq_left h1.le, min_eq_left h2.le] at hmin
        rw [max_eq_right h1.le, max_eq_right h2.le] at hmax
        exact ⟨hmin, hmax⟩
      · have h2 : ¬ u (T2, T2') < v (T2, T2') := by simpa [h1] using hdec
        push Not at h1 h2
        rw [min_eq_right h1, min_eq_right h2] at hmin
        rw [max_eq_left h1, max_eq_left h2] at hmax
        exact ⟨hmax, hmin⟩
    have hA : T1 \ T1' = T2 \ T2' := by
      rw [← pf_prod hP (sdiff_subset.trans he1.1.1.1),
        ← pf_prod hP (sdiff_subset.trans he2.1.1.1)]
      exact congrArg Nat.primeFactors huv.1
    have hB : T1' \ T1 = T2' \ T2 := by
      rw [← pf_prod hP (sdiff_subset.trans he1.1.2.1),
        ← pf_prod hP (sdiff_subset.trans he2.1.2.1)]
      exact congrArg Nat.primeFactors huv.2
    have hC : T1 ∩ T1' = T2 ∩ T2' := by
      rw [← pf_prod hP (inter_subset_left.trans he1.1.1.1),
        ← pf_prod hP (inter_subset_left.trans he2.1.1.1)]
      exact congrArg Nat.primeFactors hg
    have e1 : T1 = T2 := by
      rw [← sdiff_union_inter T1 T1', ← sdiff_union_inter T2 T2', hA, hC]
    have e2 : T1' = T2' := by
      rw [← sdiff_union_inter T1' T1, ← sdiff_union_inter T2' T2, hB, inter_comm, hC,
        inter_comm]
    rw [e1, e2]

/-- **Combinatorial core.** -/
theorem core (hImages : H2) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Y s k t x : ℕ)
    (hY : ∀ p ∈ P, p ≤ Y) (hs : ∀ p ∈ P, ∀ q ∈ (p+1).primeFactors, q ≤ s)
    (hx : (Y+1)^k ≤ x) (htk : t ≤ k) :
    (P.card.choose k)^2 ≤ (Nat.log 2 x + 1)^(s+1) *
      (Erdos824.hSquarefree x * (Y^t * 2) + P.card.choose k * (k.choose t * P.card.choose (k-t))) := by
  classical
  set F := P.powersetCard k
  have hF : F.card = P.card.choose k := card_powersetCard k P
  rw [← hF]
  refine (cs_pairs F (fun T : Finset ℕ => ∏ p ∈ T, (p + 1))).trans (Nat.mul_le_mul (hImages P Y s k x hY hs hx) ?_)
  have hsub : ((F ×ˢ F).filter (fun e => (∏ p ∈ e.1, (p + 1)) = (∏ p ∈ e.2, (p + 1)))) ⊆ ((F ×ˢ F).filter
      (fun e => (∏ p ∈ e.1, (p + 1)) = (∏ p ∈ e.2, (p + 1)) ∧ (e.1 ∩ e.2).card < t)) ∪
      ((F ×ˢ F).filter (fun e => t ≤ (e.1 ∩ e.2).card)) := by
    intro e he
    simp only [mem_filter, mem_union] at he ⊢
    by_cases hlt : (e.1 ∩ e.2).card < t
    · exact Or.inl ⟨he.1, he.2, hlt⟩
    · exact Or.inr ⟨he.1, not_lt.1 hlt⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add ?_ ?_))
  · exact card_good P hP Y k t x hY hx htk
  · exact card_bad P k t

/-- `C(M,k-t) * (M-k)^t ≤ C(M,k) * k^t` for `t ≤ k`. -/
lemma choose_ratio (M k : ℕ) : ∀ t, t ≤ k →
    M.choose (k - t) * (M - k)^t ≤ M.choose k * k^t := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have ih := ih (by omega)
    set j := k - (t+1) with hj
    have hjk : j + 1 = k - t := by omega
    have hrec := Nat.choose_succ_right_eq M j
    rw [hjk] at hrec
    -- C(M,j) * (M-k) ≤ C(M,j) * (M-j) = C(M,k-t) * (k-t) ≤ C(M,k-t) * k
    have step : M.choose j * (M - k) ≤ M.choose (k - t) * k := by
      calc M.choose j * (M - k) ≤ M.choose j * (M - j) := Nat.mul_le_mul_left _ (by omega)
        _ = M.choose (k - t) * (k - t) := by rw [hrec]
        _ ≤ M.choose (k - t) * k := Nat.mul_le_mul_left _ (by omega)
    calc M.choose j * (M - k) ^ (t+1) = (M.choose j * (M - k)) * (M - k)^t := by ring
      _ ≤ (M.choose (k - t) * k) * (M - k)^t := Nat.mul_le_mul_right _ step
      _ = k * (M.choose (k - t) * (M - k)^t) := by ring
      _ ≤ k * (M.choose k * k^t) := Nat.mul_le_mul_left _ ih
      _ = M.choose k * k^(t+1) := by ring

/-- `(M-k)^k ≤ C(M,k) * k^k`. -/
lemma choose_lower (M k : ℕ) : (M - k)^k ≤ M.choose k * k^k := by
  calc (M - k)^k ≤ (M + 1 - k)^k := Nat.pow_le_pow_left (by omega) _
    _ ≤ M.descFactorial k := Nat.pow_sub_le_descFactorial M k
    _ = k.factorial * M.choose k := Nat.descFactorial_eq_factorial_mul_choose M k
    _ ≤ k^k * M.choose k := Nat.mul_le_mul_right _ (Nat.factorial_le_pow k)
    _ = M.choose k * k^k := by ring

/-- Pure arithmetic: removing the bad pairs. -/
lemma arith (N U H G c b D K E : ℕ) (h1 : N^2 ≤ U * (H * (G * 2) + N * (c * b)))
    (h2 : c ≤ E) (h3 : b * D ≤ N * K) (h4 : 2 * U * E * K ≤ D) (hD : 0 < D) :
    N^2 ≤ 4 * U * H * G := by
  have s1 : N^2 * D ≤ 2 * U * H * G * D + N^2 * (U * E * K) := by
    calc N^2 * D ≤ U * (H * (G * 2) + N * (c * b)) * D := Nat.mul_le_mul_right _ h1
      _ = 2 * U * H * G * D + U * N * c * (b * D) := by ring
      _ ≤ 2 * U * H * G * D + U * N * E * (N * K) := by
          apply Nat.add_le_add_left
          exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) h3
      _ = 2 * U * H * G * D + N^2 * (U * E * K) := by ring
  have s2 : 2 * (N^2 * (U * E * K)) ≤ N^2 * D := by
    calc 2 * (N^2 * (U * E * K)) = N^2 * (2 * U * E * K) := by ring
      _ ≤ N^2 * D := Nat.mul_le_mul_left _ h4
  have s3 : N^2 * D ≤ (4 * U * H * G) * D := by nlinarith
  exact Nat.le_of_mul_le_mul_right s3 hD

/-- **Core, final form**: if the bad-pair condition `2 U 2^k k^t ≤ (M-k)^t` holds, then
`C(M,k)^2 ≤ 4 U h(x) Y^t`, with `U = (log₂ x + 1)^(s+1)`. -/
theorem core_final (hImages : H2) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Y s k t x : ℕ)
    (hY : ∀ p ∈ P, p ≤ Y) (hs : ∀ p ∈ P, ∀ q ∈ (p+1).primeFactors, q ≤ s)
    (hx : (Y+1)^k ≤ x) (htk : t ≤ k) (hkM : k < P.card)
    (hbad : 2 * (Nat.log 2 x + 1)^(s+1) * 2^k * k^t ≤ (P.card - k)^t) :
    (P.card.choose k)^2 ≤ 4 * (Nat.log 2 x + 1)^(s+1) * Erdos824.hSquarefree x * Y^t :=
  arith _ _ _ _ _ _ _ _ _ (core hImages P hP Y s k t x hY hs hx htk) (Nat.choose_le_two_pow k t)
    (choose_ratio P.card k t htk) hbad (pow_pos (by omega) _)


open Real Asymptotics

lemma log_consts : Real.log 6 < 2 ∧ Real.log 5 < 2 ∧ Real.log 4 < 2 ∧
    0 < Real.log 5 ∧ 0 < Real.log 6 := by
  have h6 : Real.log 6 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [e]; nlinarith
  have h5 := Real.log_lt_log (by norm_num : (0:ℝ) < 5) (by norm_num : (5:ℝ) < 6)
  have h4 := Real.log_lt_log (by norm_num : (0:ℝ) < 4) (by norm_num : (4:ℝ) < 6)
  exact ⟨h6, by linarith, by linarith, Real.log_pos (by norm_num), Real.log_pos (by norm_num)⟩

/-- Bad-pair condition in log form: `log 2 + log U + k log 2 ≤ t (log D - log k)`. -/
lemma bad_ineq (k t ℓ L B η a dk G lU l2 r logScale : ℝ)
    (hk0 : 0 ≤ k) (ht : η * k ≤ t) (hda : a ≤ dk) (ha0 : 0 ≤ a) (ha : a = (B - 2) * ℓ - l2)
    (hBη : B * η = 1) (hη16 : η ≤ 1/16) (hη0 : 0 < η) (hl2 : l2 < 0.7) (hl2p : 0 < l2)
    (hℓ8 : 8 ≤ ℓ) (hB : 16 ≤ B) (hr : r * logScale = L) (hlogScale : logScale ≤ 2 * B * ℓ) (hrk : r - 1 ≤ k)
    (hr0 : 0 ≤ r) (hG2 : 12 * B * G ≤ L) (hℓG : ℓ + 1 ≤ G) (hlU : lU ≤ G) :
    l2 + lU + k * l2 ≤ t * dk := by
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have p1 : η * k * a ≤ t * dk := mul_le_mul ht hda ha0 ht0
  have p2 : η * k * a = (B * η) * (k * ℓ) - 2 * η * (k * ℓ) - η * k * l2 := by rw [ha]; ring
  rw [hBη] at p2
  have hkℓ0 : 0 ≤ k * ℓ := mul_nonneg hk0 (by linarith)
  have p3 : η * (k * ℓ) ≤ (1/16) * (k * ℓ) := mul_le_mul_of_nonneg_right hη16 hkℓ0
  have p4' : η * l2 ≤ 1/16 := by nlinarith
  have p4 : η * k * l2 ≤ k / 16 := by
    have := mul_le_mul_of_nonneg_left p4' hk0; linarith
  have p5 : 8 * k ≤ k * ℓ := by nlinarith
  have p6 : k * l2 ≤ 0.7 * k := by nlinarith
  have p7 : (r - 1) * ℓ ≤ k * ℓ := mul_le_mul_of_nonneg_right hrk (by linarith)
  have p8 : r * logScale ≤ r * (2 * B * ℓ) := mul_le_mul_of_nonneg_left hlogScale hr0
  have p9 : 2 * B * ((r - 1) * ℓ) ≤ 2 * B * (k * ℓ) :=
    mul_le_mul_of_nonneg_left p7 (by positivity)
  have p10 : 2 * B * (6 * G - ℓ) ≤ 2 * B * (k * ℓ) := by nlinarith
  have p11 : 6 * G - ℓ ≤ k * ℓ := le_of_mul_le_mul_left p10 (by positivity)
  linarith

/-- Main inequality in log form: `(2-ε)L + log 4 + log U + t log Y < 2k (log D - log k)`. -/
lemma main_ineq (k t ℓ L B η ε a dk G lU l2 l4 l5 l6 lY r logScale : ℝ)
    (hk0 : 0 ≤ k) (ha : a = (B - 2) * ℓ - l2) (hda : a ≤ dk) (ht1 : t ≤ η * k + 1)
    (ht0 : 0 ≤ t) (hlY : lY ≤ l5 + B * ℓ) (hlY0 : 0 ≤ lY) (hBη : B * η = 1)
    (hεB : ε * B = 16) (hε : 0 < ε) (hη0 : 0 < η) (hη16 : η ≤ 1/16)
    (hl2 : l2 < 0.7) (_hl2p : 0 < l2) (hl4 : l4 < 2) (hl5 : l5 < 2) (hl5p : 0 < l5)
    (hl6 : l6 < 2) (hl6p : 0 < l6) (hlogScaledef : logScale = l6 + B * ℓ) (hr : r * logScale = L)
    (hrk : r - 1 ≤ k) (hr0 : 0 ≤ r) (hklogScale : k * logScale ≤ L) (hℓ8 : 8 ≤ ℓ) (hB : 16 ≤ B)
    (hG1 : 8 * (3 * B + 4) * G ≤ 3 * ε * L) (hℓG : ℓ + 1 ≤ G) (hlU : lU ≤ G)
    (hL0 : 0 < L) :
    (2 - ε) * L + (l4 + lU + t * lY) < 2 * k * dk := by
  have q1 : 2 * k * ((B - 2) * ℓ - l2) ≤ 2 * k * dk := by
    rw [← ha]; exact mul_le_mul_of_nonneg_left hda (by positivity)
  have q2 : t * lY ≤ (η * k + 1) * (l5 + B * ℓ) := mul_le_mul ht1 hlY hlY0 (by linarith)
  have q2' : (η * k + 1) * (l5 + B * ℓ) = η * k * l5 + (B * η) * (k * ℓ) + l5 + B * ℓ := by
    ring
  rw [hBη] at q2'
  have q3a : ε * logScale = ε * l6 + 16 * ℓ := by rw [hlogScaledef]; linear_combination ℓ * hεB
  have q3b : 0 < ε * l6 := mul_pos hε hl6p
  have q3 : (2 - ε / 2) * logScale ≤ (2 * B - 5) * ℓ := by
    have e : (2 - ε / 2) * logScale = 2 * logScale - (ε * logScale) / 2 := by ring
    rw [e, q3a, hlogScaledef]; linarith
  have q4a : r * ((2 - ε / 2) * logScale) ≤ r * ((2 * B - 5) * ℓ) := mul_le_mul_of_nonneg_left q3 hr0
  have q4b : r * ((2 - ε / 2) * logScale) = (2 - ε / 2) * L := by rw [← hr]; ring
  have hc0 : 0 ≤ (2 * B - 5) * ℓ := mul_nonneg (by linarith) (by linarith)
  have q5 : (r - 1) * ((2 * B - 5) * ℓ) ≤ k * ((2 * B - 5) * ℓ) :=
    mul_le_mul_of_nonneg_right hrk hc0
  have q6a : k * (B * ℓ) ≤ k * logScale := mul_le_mul_of_nonneg_left (by linarith) hk0
  have q6b : ε * (k * (B * ℓ)) ≤ ε * L := mul_le_mul_of_nonneg_left (by linarith) hε.le
  have q6c : ε * (k * (B * ℓ)) = 16 * (k * ℓ) := by linear_combination (k * ℓ) * hεB
  have q7 : k * 8 ≤ k * ℓ := mul_le_mul_of_nonneg_left hℓ8 hk0
  have q8a : η * l5 ≤ 1/16 * 2 := mul_le_mul hη16 hl5.le hl5p.le (by norm_num)
  have q8 : η * k * l5 ≤ k / 8 := by
    have := mul_le_mul_of_nonneg_left q8a hk0; linarith
  have q9 : k * l2 ≤ k * 0.7 := mul_le_mul_of_nonneg_left hl2.le hk0
  have q10 : B * (ℓ + 1) ≤ B * G := mul_le_mul_of_nonneg_left hℓG (by linarith)
  have hεL : 0 < ε * L := mul_pos hε hL0
  linarith


/-- `(√L+1)(log(2L)+1) = o(L)`. -/
lemma master (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, (√L + 1) * (Real.log (2*L) + 1) ≤ c * L := by
  have h1 : (fun L : ℝ => √L + 1) =O[atTop] (fun L => L ^ (1/2:ℝ)) := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL
    rw [Real.norm_eq_abs, Real.norm_eq_abs, ← Real.sqrt_eq_rpow,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have : 1 ≤ √L := Real.one_le_sqrt.2 hL
    linarith
  have h2 : (fun L : ℝ => Real.log (2*L) + 1) =o[atTop] (fun L => L ^ (1/2:ℝ)) := by
    have hlog := isLittleO_log_rpow_atTop (r := 1/2) (by norm_num)
    have hc : (fun _ : ℝ => Real.log 2 + 1) =o[atTop] (fun L : ℝ => L ^ (1/2:ℝ)) := by
      rw [isLittleO_const_left]
      right
      exact tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop (by norm_num))
    refine (hlog.add hc).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    rw [Real.log_mul (by norm_num) hL.ne']; ring
  have h3 := h1.mul_isLittleO h2
  have h4 : (fun L : ℝ => L ^ (1/2:ℝ) * L ^ (1/2:ℝ)) =ᶠ[atTop] (fun L => L) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    rw [← Real.rpow_add' hL (by norm_num)]; norm_num
  have h5 := (h3.congr' EventuallyEq.rfl h4).bound hc
  filter_upwards [h5, eventually_ge_atTop (1:ℝ)] with L h hL
  have hlog : 0 ≤ Real.log (2*L) := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by linarith)] at h
  exact h

set_option maxHeartbeats 4000000 in
/-- The main estimate at one (large) `x`, with all largeness conditions explicit. -/
lemma main_at (hImages : H2) (ε B η δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hB : B = 16 / ε) (hη : η = ε / 16)
    (hδ : δ = 1 / (2 * B)) (x : ℕ) (hx : 0 < x) (L : ℝ) (hL : L = Real.log x)
    (hL8 : Real.exp 8 ≤ L)
    (hG1 : 8 * (3*B+4) * ((√L + 1) * (Real.log (2*L) + 1)) ≤ 3 * ε * L)
    (hG2 : 12 * B * ((√L + 1) * (Real.log (2*L) + 1)) ≤ L)
    (P : Finset ℕ)
    (hPdef : P = (Finset.Iic ⌊5*(L^B)⌋₊).filter
        (fun p => p.Prime ∧ ∀ q ∈ (p+1).primeFactors, ((q:ℕ):ℝ) ≤ (L^B) ^ δ))
    (hM : (L^B) ^ (1 - η) ≤ (P.card : ℝ)) :
    (x:ℝ) ^ (2 - ε) < (Erdos824.hSquarefree x : ℝ) := by
  obtain ⟨hlog6, hlog5, hlog4, hlog5p, hlog6p⟩ := log_consts
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  -- basic parameter facts
  have hBpos : 0 < B := by rw [hB]; positivity
  have hBη : B * η = 1 := by rw [hB, hη]; field_simp
  have hεB : ε * B = 16 := by rw [hB]; field_simp
  have hB16 : 16 ≤ B := by rw [hB, le_div_iff₀ hε]; linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  have hη16 : η ≤ 1/16 := by rw [hη]; linarith
  have he8 : (2:ℝ) ≤ Real.exp 8 := by have := Real.add_one_le_exp (8:ℝ); linarith
  have hL2 : 2 ≤ L := le_trans he8 hL8
  have hL0 : 0 < L := by linarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = Real.log L := ⟨_, rfl⟩
  have hℓ8 : 8 ≤ ℓ := by
    rw [hℓ, ← Real.log_exp 8]; exact Real.log_le_log (Real.exp_pos 8) hL8
  obtain ⟨y, hy⟩ : ∃ y, y = L ^ B := ⟨_, rfl⟩
  rw [← hy] at hPdef hM
  have hy1 : 1 ≤ y := by rw [hy]; exact Real.one_le_rpow (by linarith) hBpos.le
  have hy0 : 0 < y := by linarith
  have hlogy : Real.log y = B * ℓ := by rw [hy, hℓ]; exact Real.log_rpow hL0 B
  have hyδ : y ^ δ = √L := by
    rw [hy, ← Real.rpow_mul hL0.le, Real.sqrt_eq_rpow, hδ]
    congr 1; field_simp
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℕ, Y = ⌊5*y⌋₊ := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ, s = ⌊y ^ δ⌋₊ := ⟨_, rfl⟩
  obtain ⟨logScale, hlogScale⟩ : ∃ logScale : ℝ, logScale = Real.log 6 + B * ℓ := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = L / logScale := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = ⌊r⌋₊ := ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t : ℕ, t = ⌈η * k⌉₊ := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = P.card := ⟨_, rfl⟩
  rw [← hMdef] at hM
  have hBℓ8 : 16 * 8 ≤ B * ℓ := mul_le_mul hB16 hℓ8 (by norm_num) hBpos.le
  have hlogScalepos : 0 < logScale := by rw [hlogScale]; linarith
  have hlogScalele : logScale ≤ 2 * B * ℓ := by rw [hlogScale]; linarith
  have hr : r * logScale = L := by rw [hrdef]; field_simp
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hPprop : ∀ p ∈ P, p.Prime ∧ p ≤ Y ∧ ∀ q ∈ (p+1).primeFactors, q ≤ s := by
    intro p hp
    rw [hPdef, Finset.mem_filter, Finset.mem_Iic] at hp
    refine ⟨hp.2.1, hYdef ▸ hp.1, fun q hq => hsdef ▸ Nat.le_floor (hp.2.2 q hq)⟩
  have hsL : (s:ℝ) ≤ √L := by rw [← hyδ, hsdef]; exact Nat.floor_le (by positivity)
  have hY1 : 1 ≤ Y := by rw [hYdef]; exact Nat.le_floor (by push_cast; linarith)
  have hYle : (Y:ℝ) ≤ 5 * y := by rw [hYdef]; exact Nat.floor_le (by positivity)
  have hYpos : (0:ℝ) < Y := by exact_mod_cast hY1
  have hlogY : Real.log Y ≤ Real.log 5 + B * ℓ := by
    rw [← hlogy, ← Real.log_mul (by norm_num) hy0.ne']
    exact Real.log_le_log hYpos hYle
  have hlogY0 : 0 ≤ Real.log Y := Real.log_nonneg (by exact_mod_cast hY1)
  have hk_le : (k:ℝ) ≤ r := by rw [hkdef]; exact Nat.floor_le hr0
  have hrk : r - 1 ≤ (k:ℝ) := by rw [hkdef]; have := Nat.lt_floor_add_one r; linarith
  have hklogScale : (k:ℝ) * logScale ≤ L := by rw [← hr]; exact mul_le_mul_of_nonneg_right hk_le hlogScalepos.le
  have hk0' : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hkL : (k:ℝ) ≤ L := by
    have : (k:ℝ) * 1 ≤ k * logScale := mul_le_mul_of_nonneg_left (by linarith) hk0'
    linarith
  -- G
  obtain ⟨G, hGdef⟩ : ∃ G, G = (√L + 1) * (Real.log (2*L) + 1) := ⟨_, rfl⟩
  rw [← hGdef] at hG1 hG2
  have hsqrt0 : 0 ≤ √L := Real.sqrt_nonneg L
  have hlog2L : ℓ ≤ Real.log (2*L) := by rw [hℓ]; exact Real.log_le_log hL0 (by linarith)
  have hGe : G = √L * (Real.log (2*L) + 1) + (Real.log (2*L) + 1) := by rw [hGdef]; ring
  have hℓG : ℓ + 1 ≤ G := by
    have : 0 ≤ √L * (Real.log (2*L) + 1) := mul_nonneg hsqrt0 (by linarith)
    linarith
  have hk1 : 1 ≤ k := by
    have p8 : L ≤ 2 * B * (r * ℓ) := by
      have := mul_le_mul_of_nonneg_left hlogScalele hr0; rw [hr] at this; linarith
    have p9 : 12 * B * (ℓ + 1) ≤ 12 * B * G := mul_le_mul_of_nonneg_left hℓG (by positivity)
    have p10 : 2 * B * (6 * ℓ) ≤ 2 * B * (r * ℓ) := by linarith
    have p11 : 6 * ℓ ≤ r * ℓ := le_of_mul_le_mul_left p10 (by positivity)
    have p12 : 6 ≤ r := le_of_mul_le_mul_right p11 (by linarith)
    have : (1:ℝ) ≤ k := by linarith
    exact_mod_cast this
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk1
  have ht_ge : η * k ≤ (t:ℝ) := by rw [htdef]; exact Nat.le_ceil _
  have ht_lt : (t:ℝ) < η * k + 1 := by rw [htdef]; exact Nat.ceil_lt_add_one (by positivity)
  have htk : t ≤ k := by
    rw [htdef]; apply Nat.ceil_le.2
    have := mul_le_mul_of_nonneg_right (show η ≤ 1 by linarith) hk0'; linarith
  -- M bounds
  have hMge : L ^ (B - 1) ≤ (M:ℝ) := by
    have e : y ^ (1 - η) = L ^ (B - 1) := by
      rw [hy, ← Real.rpow_mul hL0.le]; congr 1; linear_combination (-1:ℝ) * hBη
    rw [← e]; exact hM
  have hLLB : L * L ≤ L ^ (B - 1) := by
    have h2 : L ^ (2:ℝ) ≤ L ^ (B - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rwa [Real.rpow_two, sq] at h2
  have hLL : 2 * L ≤ L * L := by nlinarith
  have hkM : k < M := by
    have : (k:ℝ) < M := by linarith
    exact_mod_cast this
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ, D = M - k := ⟨_, rfl⟩
  have hDcast : (D:ℝ) = M - k := by rw [hDdef, Nat.cast_sub hkM.le]
  have hDge : L ^ (B - 1) / 2 ≤ (D:ℝ) := by rw [hDcast]; linarith
  have hLB0 : 0 < L ^ (B - 1) := Real.rpow_pos_of_pos hL0 _
  have hD0 : (0:ℝ) < D := by linarith
  have hlogD : (B - 1) * ℓ - Real.log 2 ≤ Real.log D := by
    have hpos : 0 < L ^ (B - 1) / 2 := by positivity
    have := Real.log_le_log hpos hDge
    rw [Real.log_div hLB0.ne' (by norm_num), Real.log_rpow hL0, ← hℓ] at this
    linarith
  have hlogk : Real.log k ≤ ℓ := by rw [hℓ]; exact Real.log_le_log hk0 hkL
  have hDk : (B - 2) * ℓ - Real.log 2 ≤ Real.log D - Real.log k := by linarith
  have ha0 : 0 ≤ (B - 2) * ℓ - Real.log 2 := by
    have : 14 * 8 ≤ (B - 2) * ℓ := mul_le_mul (by linarith) hℓ8 (by norm_num) (by linarith)
    linarith
  -- U
  obtain ⟨E, hEdef⟩ : ∃ E : ℕ, E = Nat.log 2 x := ⟨_, rfl⟩
  obtain ⟨U, hUdef⟩ : ∃ U : ℕ, U = (E + 1) ^ (s + 1) := ⟨_, rfl⟩
  have hE : (E:ℝ) * Real.log 2 ≤ L := by
    have h2E : ((2 ^ E : ℕ) : ℝ) ≤ x := by
      rw [hEdef]; exact_mod_cast Nat.pow_log_le_self 2 hx.ne'
    have := Real.log_le_log (by positivity) h2E
    rw [Nat.cast_pow, Real.log_pow] at this
    rw [hL]; push_cast at this; linarith
  have hE1 : (E:ℝ) + 1 ≤ 2 * L := by
    have := mul_le_mul_of_nonneg_left hlog2.le (Nat.cast_nonneg (α := ℝ) E)
    linarith
  have hU0 : (0:ℝ) < U := by rw [hUdef]; positivity
  have hlogU : Real.log U ≤ G := by
    rw [hUdef, Nat.cast_pow, Real.log_pow]
    push_cast
    have h1 : Real.log ((E:ℝ) + 1) ≤ Real.log (2*L) :=
      Real.log_le_log (by positivity) hE1
    have h2 : 0 ≤ Real.log ((E:ℝ) + 1) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg E : (0:ℝ) ≤ E)])
    have h3 : ((s:ℝ) + 1) * Real.log ((E:ℝ) + 1) ≤ (√L + 1) * Real.log (2*L) :=
      mul_le_mul (by linarith) h1 h2 (by positivity)
    have h4 : (√L + 1) * Real.log (2*L) ≤ G := by
      have e : (√L + 1) * (Real.log (2*L) + 1) = (√L + 1) * Real.log (2*L) + (√L + 1) := by
        ring
      rw [hGdef, e]; linarith
    linarith
  -- the bad-pair condition
  have hbad_log := bad_ineq k t ℓ L B η ((B - 2) * ℓ - Real.log 2)
    (Real.log D - Real.log k) G (Real.log U) (Real.log 2) r logScale hk0' ht_ge hDk ha0 rfl hBη
    hη16 hη0 (by linarith) (by linarith) hℓ8 hB16 hr hlogScalele hrk hr0 hG2 hℓG hlogU
  have hbad : 2 * U * 2^k * k^t ≤ D^t := by
    have key : Real.log 2 + Real.log U + k * Real.log 2 + t * Real.log k
        ≤ t * Real.log D := by linarith
    have lhs : Real.exp (Real.log 2 + Real.log U + k * Real.log 2 + t * Real.log k)
        = ((2 * U * 2^k * k^t : ℕ) : ℝ) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log (by norm_num), Real.exp_log hU0, Real.exp_log hk0]
      push_cast; ring
    have rhs : Real.exp (t * Real.log D) = ((D^t : ℕ) : ℝ) := by
      rw [Real.exp_nat_mul, Real.exp_log hD0]; push_cast; ring
    have := Real.exp_le_exp.2 key
    rw [lhs, rhs] at this
    exact_mod_cast this
  -- (Y+1)^k ≤ x
  have hYk : (Y + 1)^k ≤ x := by
    have h6y : Real.log (6 * y) = logScale := by rw [Real.log_mul (by norm_num) hy0.ne', hlogy, hlogScale]
    have hY6 : ((Y:ℝ) + 1) ≤ 6 * y := by linarith
    have : (((Y + 1)^k : ℕ) : ℝ) ≤ x := by
      push_cast
      calc ((Y:ℝ) + 1)^k ≤ (6 * y)^k := pow_le_pow_left₀ (by positivity) hY6 k
        _ = Real.exp (k * logScale) := by
            rw [Real.exp_nat_mul, ← h6y, Real.exp_log (by positivity)]
        _ ≤ Real.exp L := Real.exp_le_exp.2 hklogScale
        _ = x := by rw [hL, Real.exp_log (by exact_mod_cast hx)]
    exact_mod_cast this
  -- the combinatorial core
  have hbad' : 2 * (Nat.log 2 x + 1)^(s+1) * 2^k * k^t ≤ (P.card - k)^t := by
    rw [hUdef, hEdef, hDdef, hMdef] at hbad; exact hbad
  have hcore := core_final hImages P (fun p hp => (hPprop p hp).1) Y s k t x
    (fun p hp => (hPprop p hp).2.1) (fun p hp => (hPprop p hp).2.2) hYk htk
    (by rw [← hMdef]; exact hkM) hbad'
  rw [← hMdef, ← hEdef, ← hUdef] at hcore
  have hlow := choose_lower M k
  rw [← hDdef] at hlow
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = M.choose k := ⟨_, rfl⟩
  rw [← hNdef] at hcore hlow
  -- main log inequality
  have hmain := main_ineq k t ℓ L B η ε ((B - 2) * ℓ - Real.log 2) (Real.log D - Real.log k)
    G (Real.log U) (Real.log 2) (Real.log 4) (Real.log 5) (Real.log 6) (Real.log Y) r logScale
    hk0' rfl hDk ht_lt.le (Nat.cast_nonneg t) hlogY hlogY0 hBη hεB hε hη0 hη16
    (by linarith) (by linarith) hlog4 hlog5 hlog5p hlog6 hlog6p hlogScale hr hrk hr0 hklogScale hℓ8 hB16
    hG1 hℓG hlogU hL0
  have hmain_log : (2 - ε) * L + (Real.log 4 + Real.log U + t * Real.log Y
      + ((2*k : ℕ) : ℝ) * Real.log k) < ((2*k : ℕ) : ℝ) * Real.log D := by
    push_cast; linarith
  -- conclude
  have hC : Real.exp (Real.log 4 + Real.log U + t * Real.log Y
      + ((2*k : ℕ) : ℝ) * Real.log k) = 4 * U * (Y:ℝ)^t * (k:ℝ)^(2*k) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log (by norm_num), Real.exp_log hU0, Real.exp_log hYpos, Real.exp_log hk0]
  have hDpow : Real.exp (((2*k : ℕ) : ℝ) * Real.log D) = (D:ℝ)^(2*k) := by
    rw [Real.exp_nat_mul, Real.exp_log hD0]
  have hlt := Real.exp_lt_exp.2 hmain_log
  rw [Real.exp_add, hC, hDpow] at hlt
  have hlowR : (D:ℝ)^k ≤ N * (k:ℝ)^k := by exact_mod_cast hlow
  have hcoreR : (N:ℝ)^2 ≤ 4 * U * Erdos824.hSquarefree x * (Y:ℝ)^t := by exact_mod_cast hcore
  have hD2 : (D:ℝ)^(2*k) ≤ (Erdos824.hSquarefree x : ℝ) * (4 * U * (Y:ℝ)^t * (k:ℝ)^(2*k)) := by
    have e1 : (D:ℝ)^(2*k) = ((D:ℝ)^k)^2 := by ring
    have e2 : (k:ℝ)^(2*k) = ((k:ℝ)^k)^2 := by ring
    rw [e1, e2]
    calc ((D:ℝ)^k)^2 ≤ (N * (k:ℝ)^k)^2 := pow_le_pow_left₀ (by positivity) hlowR 2
      _ = (N:ℝ)^2 * ((k:ℝ)^k)^2 := by ring
      _ ≤ (4 * U * Erdos824.hSquarefree x * (Y:ℝ)^t) * ((k:ℝ)^k)^2 :=
          mul_le_mul_of_nonneg_right hcoreR (by positivity)
      _ = (Erdos824.hSquarefree x : ℝ) * (4 * U * (Y:ℝ)^t * ((k:ℝ)^k)^2) := by ring
  have hCpos : 0 < 4 * (U:ℝ) * (Y:ℝ)^t * (k:ℝ)^(2*k) := by positivity
  have hfinal := lt_of_lt_of_le hlt hD2
  have := lt_of_mul_lt_mul_right hfinal hCpos.le
  have e : Real.log x * (2 - ε) = (2 - ε) * L := by rw [hL]; ring
  rw [Real.rpow_def_of_pos (by exact_mod_cast hx), e]
  exact this

/-- The theorem for `0 < ε ≤ 1`, from the weakened hypothesis. -/
lemma main_small (hImages : H2) (H : H1) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ X : ℝ, ∀ x : ℕ, X ≤ x → (x:ℝ) ^ (2 - ε) < (Erdos824.hSquarefree x : ℝ) := by
  set B : ℝ := 16 / ε with hB
  set η : ℝ := ε / 16 with hη
  set δ : ℝ := 1 / (2 * B) with hδ
  have hBpos : 0 < B := by positivity
  have hB16 : 16 ≤ B := by rw [hB, le_div_iff₀ hε]; linarith
  have hδpos : 0 < δ := by positivity
  have hδ14 : δ < 1/4 := by
    rw [hδ, div_lt_iff₀ (by positivity)]; linarith
  obtain ⟨y0, hy0⟩ := H δ hδpos hδ14 η (by positivity)
  obtain ⟨c1, hc1def⟩ : ∃ c : ℝ, c = (3*ε/8) / (3*B+4) := ⟨_, rfl⟩
  obtain ⟨c2, hc2def⟩ : ∃ c : ℝ, c = 1 / (12 * B) := ⟨_, rfl⟩
  have hc1 : 0 < c1 := by rw [hc1def]; positivity
  have hc2 : 0 < c2 := by rw [hc2def]; positivity
  have hev : ∀ᶠ L : ℝ in atTop,
      (√L + 1) * (Real.log (2*L) + 1) ≤ min c1 c2 * L ∧ Real.exp 8 ≤ L ∧ y0 ≤ L ^ B ∧ 0 ≤ L :=
    (master _ (lt_min hc1 hc2)).and ((eventually_ge_atTop _).and
      (((tendsto_rpow_atTop hBpos).eventually_ge_atTop y0).and (eventually_ge_atTop 0)))
  obtain ⟨L0, hL0⟩ := eventually_atTop.1 hev
  refine ⟨Real.exp L0, fun x hx => ?_⟩
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hx0 : 0 < x := by exact_mod_cast hxpos
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log x := ⟨_, rfl⟩
  have hL0L : L0 ≤ L := by
    rw [hL, ← Real.exp_le_exp, Real.exp_log hxpos]; exact hx
  obtain ⟨hG, hL8, hyL, hLnn⟩ := hL0 L hL0L
  have hG1 : 8 * (3*B+4) * ((√L + 1) * (Real.log (2*L) + 1)) ≤ 3 * ε * L := by
    have h1 := hG.trans (mul_le_mul_of_nonneg_right (min_le_left c1 c2) hLnn)
    have e : 8 * (3*B+4) * (c1 * L) = 3 * ε * L := by
      rw [hc1def]; field_simp
    calc _ ≤ 8 * (3*B+4) * (c1 * L) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := e
  have hG2 : 12 * B * ((√L + 1) * (Real.log (2*L) + 1)) ≤ L := by
    have h1 := hG.trans (mul_le_mul_of_nonneg_right (min_le_right c1 c2) hLnn)
    have e : 12 * B * (c2 * L) = L := by
      rw [hc2def]; field_simp
    calc _ ≤ 12 * B * (c2 * L) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := e
  exact main_at hImages ε B η δ hε hε1 hB hη hδ x hx0 L hL hL8 hG1 hG2 _ rfl (hy0 _ hyL)

/-- **Main theorem (weak hypothesis).** -/
theorem erdos824_of_smoothSuccessorWeak (hImages : H2) (H : H1) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℕ, X ≤ x → (x:ℝ) ^ (2 - ε) < (Erdos824.hSquarefree x : ℝ) := by
  intro ε hε
  obtain ⟨X, hX⟩ := main_small hImages H (min ε 1) (lt_min hε one_pos) (min_le_right _ _)
  refine ⟨max X 1, fun x hx => ?_⟩
  have hx1 : (1:ℝ) ≤ x := le_trans (le_max_right _ _) hx
  calc (x:ℝ) ^ (2 - ε) ≤ (x:ℝ) ^ (2 - min ε 1) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [min_le_left ε 1])
    _ < Erdos824.hSquarefree x := hX x (le_trans (le_max_left _ _) hx)


theorem main : H1 → H2 → type_of% @Erdos824.erdos_824.variants.squarefree := by
  intro supply images ε hε
  obtain ⟨X, hX⟩ := erdos824_of_smoothSuccessorWeak images supply ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt X
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hX n (hN.le.trans (by exact_mod_cast hn))

end OMA.R_Erdos824_erdos_824_variants_squarefree_R1
