import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1

/-!
Proof of Erdos470.erdos_470.variants.odd_weird_prime_div.R2.H2.R1.H1.

Every odd abundant number n with five prime factors, valuations 2, 1, 1 at 3, 5, 7,
a prime divisor p in [107, 210), and all prime factors below 5565 is pseudoperfect.

If the fifth prime q is below 107, the parent reduction's small_multiple certifies 315 * q.
Otherwise 107 <= q < 5565 and n = 315 * p^a * q^b with a, b >= 1. Taking the minimal
abundant divisor m = 315 * p^a * q^(j+1) of n (with 315 * p^a * q^j deficient; if perfect
it is already pseudoperfect), its excess E = sigma(m) - 2m is a positive multiple of 6
satisfying E <= 624 * sigma(p^a) - q. Using the subset sums of the divisors of 315
(which cover [0, 624] outside {2, 622} and [307, 317]) in base p across layers d * p^k,
with at most one shift d0 * p^(a-1) * q (d0 in {1, 3, 7, 35}) to bypass the middle gap
[307 * p^a, 319 * p^a], we represent E as a sum of distinct proper divisors of m.
Complementation gives m.Pseudoperfect, and pseudoperfect_multiple lifts it to n.
-/

namespace OMA.Erdos470R2H2R1H1

open Finset
open OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1

private def divs315List : List ℕ := [315, 105, 63, 45, 35, 21, 15, 9, 7, 5, 3, 1]

private def greedy315 : List ℕ → ℕ → List ℕ
  | [], _ => []
  | d :: ds, rem =>
      if d ≤ rem ∧ rem - d ≠ 2 then d :: greedy315 ds (rem - d)
      else greedy315 ds rem

private lemma greedy315_sublist : ∀ (ds : List ℕ) (rem : ℕ), (greedy315 ds rem).Sublist ds
  | [], _ => List.Sublist.slnil
  | d :: ds, rem => by
      unfold greedy315
      split_ifs
      · exact List.Sublist.cons_cons d (greedy315_sublist ds (rem - d))
      · exact List.Sublist.cons d (greedy315_sublist ds rem)

private def checkGood (c : ℕ) : Bool :=
  decide (624 < c ∨ c = 2 ∨ c = 622 ∨ (307 ≤ c ∧ c ≤ 317) ∨ (greedy315 divs315List c).sum = c)

private def checkTree : ℕ → ℕ → Bool
  | 0, lo => checkGood lo
  | d + 1, lo => checkTree d lo && checkTree d (lo + 2 ^ d)

private lemma checkTree_spec (d : ℕ) :
    ∀ lo c, lo ≤ c → c < lo + 2 ^ d → checkTree d lo = true → checkGood c = true := by
  induction d with
  | zero =>
      intro lo c hlo hhi hct
      have : c = lo := by omega
      subst this
      simpa [checkTree] using hct
  | succ d ih =>
      intro lo c hlo hhi hct
      simp only [checkTree, Bool.and_eq_true] at hct
      by_cases hc : c < lo + 2 ^ d
      · exact ih lo c hlo hc hct.1
      · have h2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [pow_succ]; ring
        exact ih (lo + 2 ^ d) c (by omega) (by omega) hct.2

private lemma checkTree_10 : checkTree 10 0 = true := by decide

private lemma greedy315_sum_ok {c : ℕ} (hle : c ≤ 624) (h2 : c ≠ 2) (h622 : c ≠ 622)
    (hmid : c < 307 ∨ 317 < c) :
    (greedy315 divs315List c).sum = c := by
  have hcg := checkTree_spec 10 0 c (Nat.zero_le c) (by omega) checkTree_10
  have hprop := of_decide_eq_true hcg
  rcases hprop with h | h | h | ⟨h1, h2'⟩ | h
  · omega
  · omega
  · omega
  · omega
  · exact h

private lemma divs315List_nodup : divs315List.Nodup := by decide

private lemma divs315List_mem_divisors :
    ∀ d ∈ divs315List, d ∈ (315 : ℕ).divisors := by
  intro d hd
  have hd' : d ∣ 315 := by
    have htest : divs315List.all (fun x => decide (x ∣ 315)) = true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp htest d hd)
  exact Nat.mem_divisors.mpr ⟨hd', by decide⟩

private def GoodDigit (c : ℕ) : Prop :=
  c ≤ 624 ∧ c ≠ 2 ∧ c ≠ 622 ∧ (c < 307 ∨ 317 < c)

private lemma subset_sum_315 {c : ℕ} (hc : GoodDigit c) :
    ∃ s ⊆ (315 : ℕ).divisors, ∑ d ∈ s, d = c := by
  rcases hc with ⟨hle, h2, h622, hmid⟩
  let l := greedy315 divs315List c
  have hsub : l.Sublist divs315List := greedy315_sublist divs315List c
  have hnd : l.Nodup := hsub.nodup divs315List_nodup
  have hsum : l.sum = c := greedy315_sum_ok hle h2 h622 hmid
  refine ⟨l.toFinset, ?_, ?_⟩
  · intro d hd
    exact divs315List_mem_divisors d (hsub.subset (List.mem_toFinset.mp hd))
  · calc
      ∑ d ∈ l.toFinset, d = (l.map id).sum := List.sum_toFinset id hnd
      _ = l.sum := by simp
      _ = c := hsum

private def geomSum (p a : ℕ) : ℕ :=
  ∑ k ∈ range (a + 1), p ^ k

private def Mval (p a : ℕ) : ℕ :=
  624 * geomSum p a

private lemma geomSum_zero (p : ℕ) : geomSum p 0 = 1 := by
  simp [geomSum]

private lemma geomSum_succ (p a : ℕ) : geomSum p (a + 1) = geomSum p a + p ^ (a + 1) := by
  simp [geomSum, Finset.sum_range_succ]

private lemma geomSum_mul_pred (p a : ℕ) (hp : 1 ≤ p) :
    (p - 1) * geomSum p a + 1 = p ^ (a + 1) := by
  induction a with
  | zero =>
      rw [geomSum_zero, mul_one, pow_one]
      omega
  | succ a ih =>
      rw [geomSum_succ, mul_add, add_assoc]
      have h1 : (p - 1) * p ^ (a + 1) + p ^ (a + 1) = p ^ (a + 1 + 1) := by
        rw [show (p - 1) * p ^ (a + 1) + p ^ (a + 1) = ((p - 1) + 1) * p ^ (a + 1) by ring]
        rw [Nat.sub_add_cancel hp, ← pow_succ']
      omega

private lemma geomSum_ge_pow (p a : ℕ) : p ^ a ≤ geomSum p a := by
  unfold geomSum
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_self a))

private lemma Mval_zero (p : ℕ) : Mval p 0 = 624 := by
  simp [Mval, geomSum_zero]

private lemma Mval_succ (p a : ℕ) : Mval p (a + 1) = 624 * p ^ (a + 1) + Mval p a := by
  simp [Mval, geomSum_succ]
  ring

private lemma Mval_ge_three_mul (p a : ℕ) (hp1 : 1 ≤ p) (hp2 : p ≤ 209) :
    3 * p ^ (a + 1) ≤ Mval p a + 3 := by
  have h1 := geomSum_mul_pred p a hp1
  have h2 : 3 * (p - 1) ≤ 624 := by omega
  have h3 : 3 * ((p - 1) * geomSum p a) ≤ 624 * geomSum p a := by
    calc
      3 * ((p - 1) * geomSum p a) = (3 * (p - 1)) * geomSum p a := by ring
      _ ≤ 624 * geomSum p a := Nat.mul_le_mul_right _ h2
  unfold Mval
  omega

private lemma Mval_ge_624_mul (p a : ℕ) : 624 * p ^ a ≤ Mval p a := by
  unfold Mval
  exact Nat.mul_le_mul_left 624 (geomSum_ge_pow p a)

private def Good (p a x : ℕ) : Prop :=
  x ≤ Mval p a ∧ x ≠ 2 ∧ x ≠ Mval p a - 2 ∧ (x < 307 * p ^ a ∨ 319 * p ^ a < x)

private lemma not_both_bad {p a y : ℕ} (hlo : 107 ≤ p) (hhi : p ≤ 209)
    (hle : y + p ^ (a + 1) ≤ Mval p a) :
    Good p a y ∨ Good p a (y + p ^ (a + 1)) := by
  by_cases hy : Good p a y
  · exact Or.inl hy
  · right
    set Q := p ^ a
    set P := p ^ (a + 1)
    have hQpos : 1 ≤ Q := Nat.one_le_pow a p (by omega)
    have hPeq : P = p * Q := by simp [P, Q, pow_succ']
    have hPlo : 107 * Q ≤ P := by rw [hPeq]; exact Nat.mul_le_mul_right Q hlo
    have hPhi : P ≤ 209 * Q := by rw [hPeq]; exact Nat.mul_le_mul_right Q hhi
    have hMge : 624 * Q ≤ Mval p a := Mval_ge_624_mul p a
    have hyle : y ≤ Mval p a := by omega
    have hybad : y = 2 ∨ y = Mval p a - 2 ∨ (307 * Q ≤ y ∧ y ≤ 319 * Q) := by
      unfold Good at hy
      push Not at hy
      by_cases h2 : y = 2
      · exact Or.inl h2
      · by_cases hM : y = Mval p a - 2
        · exact Or.inr (Or.inl hM)
        · exact Or.inr (Or.inr (hy hyle h2 hM))
    refine ⟨hle, ?_, ?_, ?_⟩
    · omega
    · rcases hybad with rfl | hM | ⟨h1, h2⟩
      · omega
      · omega
      · omega
    · rcases hybad with rfl | hM | ⟨h1, h2⟩
      · left; omega
      · omega
      · right; omega

private lemma good_step {p a x : ℕ} (hlo : 107 ≤ p) (hhi : p ≤ 209)
    (hx : Good p (a + 1) x) :
    ∃ c y : ℕ, GoodDigit c ∧ Good p a y ∧ c * p ^ (a + 1) + y = x := by
  set Q := p ^ a
  set P := p ^ (a + 1)
  set M := Mval p a
  have hQpos : 1 ≤ Q := Nat.one_le_pow a p (by omega)
  have hPeq : P = p * Q := by simp [P, Q, pow_succ']
  have hPlo : 107 * Q ≤ P := by rw [hPeq]; exact Nat.mul_le_mul_right Q hlo
  have hPhi : P ≤ 209 * Q := by rw [hPeq]; exact Nat.mul_le_mul_right Q hhi
  have hM3 : 3 * P ≤ M + 3 := Mval_ge_three_mul p a (by omega) hhi
  have hM624 : 624 * Q ≤ M := Mval_ge_624_mul p a
  have hMsucc : Mval p (a + 1) = 624 * P + M := Mval_succ p a
  rcases hx with ⟨hxle, hx2, hxM2, hxmid⟩
  rw [hMsucc] at hxle hxM2
  change x < 307 * P ∨ 319 * P < x at hxmid
  by_cases h1 : x < P
  · refine ⟨0, x, ⟨by omega, by omega, by omega, Or.inl (by omega)⟩,
      ⟨by omega, hx2, by omega, Or.inl (by omega)⟩, by simp⟩
  · by_cases h2 : x < 3 * P
    · by_cases hleM : x ≤ M
      · rcases not_both_bad (a := a) hlo hhi (y := x - P) (by omega) with hg | hg
        · exact ⟨1, x - P, ⟨by omega, by omega, by omega, Or.inl (by omega)⟩, hg, by omega⟩
        · have heq : x - P + P = x := by omega
          rw [heq] at hg
          exact ⟨0, x, ⟨by omega, by omega, by omega, Or.inl (by omega)⟩, hg, by simp⟩
      · refine ⟨1, x - P, ⟨by omega, by omega, by omega, Or.inl (by omega)⟩,
          ⟨by omega, by omega, by omega, Or.inr (by omega)⟩, by omega⟩
    · by_cases h3 : x < 307 * P
      · let c0 := x / P
        let r := x % P
        have hr : r < P := Nat.mod_lt x (by omega)
        have hdiv : c0 * P + r = x := by
          dsimp only [c0, r]
          rw [Nat.mul_comm]
          exact Nat.div_add_mod x P
        have hc0_lo : 3 ≤ c0 := by
          by_contra hc
          have : c0 ≤ 2 := by omega
          have : c0 * P ≤ 2 * P := Nat.mul_le_mul_right P this
          omega
        have hc0_hi : c0 ≤ 306 := by
          by_contra hc
          have : 307 ≤ c0 := by omega
          have : 307 * P ≤ c0 * P := Nat.mul_le_mul_right P this
          omega
        by_cases hc3 : c0 = 3
        · rw [hc3] at hdiv
          by_cases hr2 : r = 2
          · by_cases hbig : 319 * Q < 2 * P + 2
            · refine ⟨1, 2 * P + 2, ⟨by omega, by omega, by omega, Or.inl (by omega)⟩,
                ⟨by omega, by omega, by omega, Or.inr hbig⟩, by omega⟩
            · refine ⟨0, 3 * P + 2, ⟨by omega, by omega, by omega, Or.inl (by omega)⟩,
                ⟨by omega, by omega, by omega, Or.inr (by omega)⟩, by omega⟩
          · refine ⟨3, r, ⟨by omega, by omega, by omega, Or.inl (by omega)⟩,
              ⟨by omega, hr2, by omega, Or.inl (by omega)⟩, by omega⟩
        · rcases not_both_bad (a := a) hlo hhi (y := r) (by omega) with hg | hg
          · refine ⟨c0, r, ⟨by omega, by omega, by omega, Or.inl (by omega)⟩, hg, hdiv⟩
          · refine ⟨c0 - 1, r + P, ⟨by omega, by omega, by omega, Or.inl (by omega)⟩, hg, ?_⟩
            have hsub : (c0 - 1) * P + P = c0 * P := by
              rw [show (c0 - 1) * P + P = (c0 - 1 + 1) * P by ring, Nat.sub_add_cancel (by omega)]
            omega
      · have hxgt : 319 * P < x := by omega
        by_cases h4 : x < 623 * P
        · let c0 := x / P
          let r := x % P
          have hr : r < P := Nat.mod_lt x (by omega)
          have hdiv : c0 * P + r = x := by
            dsimp only [c0, r]
            rw [Nat.mul_comm]
            exact Nat.div_add_mod x P
          have hc0_lo : 319 ≤ c0 := by
            by_contra hc
            have : c0 ≤ 318 := by omega
            have : c0 * P ≤ 318 * P := Nat.mul_le_mul_right P this
            omega
          have hc0_hi : c0 ≤ 622 := by
            by_contra hc
            have : 623 ≤ c0 := by omega
            have : 623 * P ≤ c0 * P := Nat.mul_le_mul_right P this
            omega
          by_cases hc622 : c0 = 622
          · rw [hc622] at hdiv
            by_cases hfit : r + 2 * P ≤ M
            · rcases not_both_bad (a := a) hlo hhi (y := r + P) (by omega) with hg | hg
              · refine ⟨621, r + P, ⟨by omega, by omega, by omega, Or.inr (by omega)⟩, hg, by omega⟩
              · refine ⟨620, r + P + P, ⟨by omega, by omega, by omega, Or.inr (by omega)⟩, hg, by omega⟩
            · refine ⟨621, r + P, ⟨by omega, by omega, by omega, Or.inr (by omega)⟩,
                ⟨by omega, by omega, by omega, Or.inr (by omega)⟩, by omega⟩
          · rcases not_both_bad (a := a) hlo hhi (y := r) (by omega) with hg | hg
            · refine ⟨c0, r, ⟨by omega, by omega, by omega, Or.inr (by omega)⟩, hg, hdiv⟩
            · refine ⟨c0 - 1, r + P, ⟨by omega, by omega, by omega, Or.inr (by omega)⟩, hg, ?_⟩
              have hsub : (c0 - 1) * P + P = c0 * P := by
                rw [show (c0 - 1) * P + P = (c0 - 1 + 1) * P by ring, Nat.sub_add_cancel (by omega)]
              omega
        · by_cases h5 : 624 * P ≤ x
          · let y := x - 624 * P
            have hy_le : y ≤ M := by omega
            have hy_M2 : y ≠ M - 2 := by omega
            by_cases hyg : Good p a y
            · exact ⟨624, y, ⟨by omega, by omega, by omega, Or.inr (by omega)⟩, hyg, by omega⟩
            · have hy_small : y + P ≤ M := by
                unfold Good at hyg
                push Not at hyg
                by_cases h2' : y = 2
                · omega
                · have ⟨hlo', hhi'⟩ := hyg hy_le h2' hy_M2
                  omega
              rcases not_both_bad (a := a) hlo hhi (y := y) hy_small with hg | hg
              · exact absurd hg hyg
              · exact ⟨623, y + P, ⟨by omega, by omega, by omega, Or.inr (by omega)⟩, hg, by omega⟩
          · let r := x - 623 * P
            have hr : r < P := by omega
            by_cases hr2 : r = 2
            · by_cases hbig : 319 * Q < 2 * P + 2
              · refine ⟨621, 2 * P + 2, ⟨by omega, by omega, by omega, Or.inr (by omega)⟩,
                  ⟨by omega, by omega, by omega, Or.inr hbig⟩, by omega⟩
              · refine ⟨620, 3 * P + 2, ⟨by omega, by omega, by omega, Or.inr (by omega)⟩,
                  ⟨by omega, by omega, by omega, Or.inr (by omega)⟩, by omega⟩
            · refine ⟨623, r, ⟨by omega, by omega, by omega, Or.inr (by omega)⟩,
                ⟨by omega, hr2, by omega, Or.inl (by omega)⟩, by omega⟩

private lemma rep_base_p {p : ℕ} (hlo : 107 ≤ p) (hhi : p ≤ 209) :
    ∀ (a x : ℕ), Good p a x →
      ∃ c : ℕ → ℕ, (∀ k ≤ a, GoodDigit (c k)) ∧ ∑ k ∈ range (a + 1), c k * p ^ k = x := by
  intro a
  induction a with
  | zero =>
      intro x hx
      refine ⟨fun _ => x, ?_, ?_⟩
      · intro k hk
        dsimp only
        rcases hx with ⟨hle, h2, h622, hmid⟩
        rw [Mval_zero] at hle h622
        simp only [pow_zero, mul_one] at hmid
        refine ⟨hle, h2, h622, ?_⟩
        rcases hmid with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      · simp
  | succ a ih =>
      intro x hx
      obtain ⟨c_top, y, hctop, hy, hsum⟩ := good_step hlo hhi hx
      obtain ⟨c, hc, hcsum⟩ := ih y hy
      refine ⟨fun k => if k = a + 1 then c_top else c k, ?_, ?_⟩
      · intro k hk
        by_cases hka : k = a + 1
        · simpa [hka] using hctop
        · simpa [hka] using hc k (by omega)
      · rw [Finset.sum_range_succ]
        simp only [ite_true]
        have hcongr :
            ∑ k ∈ range (a + 1), (if k = a + 1 then c_top else c k) * p ^ k =
              ∑ k ∈ range (a + 1), c k * p ^ k := by
          apply Finset.sum_congr rfl
          intro k hk
          have hne : k ≠ a + 1 := ne_of_lt (Finset.mem_range.mp hk)
          simp [hne]
        rw [hcongr, hcsum]
        omega

private lemma rep_layer_divisors {p a x : ℕ} (hp : p.Prime) (hlo : 107 ≤ p) (hhi : p ≤ 209)
    (hx : Good p a x) :
    ∃ S : Finset ℕ, S ⊆ (315 * p ^ a).divisors ∧ ∑ d ∈ S, d = x := by
  classical
  obtain ⟨c, hc, hcsum⟩ := rep_base_p hlo hhi a x hx
  have hsub315 : ∀ k, k ≤ a → ∃ s ⊆ (315 : ℕ).divisors, ∑ d ∈ s, d = c k :=
    fun k hk => subset_sum_315 (hc k hk)
  let s : ℕ → Finset ℕ := fun k =>
    if h : k ≤ a then (hsub315 k h).choose else ∅
  have hs_sub : ∀ k, k ≤ a → s k ⊆ (315 : ℕ).divisors := by
    intro k hk
    simp only [s, dif_pos hk]
    exact (hsub315 k hk).choose_spec.1
  have hs_sum : ∀ k, k ≤ a → ∑ d ∈ s k, d = c k := by
    intro k hk
    simp only [s, dif_pos hk]
    exact (hsub315 k hk).choose_spec.2
  let layer : ℕ → Finset ℕ := fun k => (s k).image (fun d => d * p ^ k)
  let S : Finset ℕ := (range (a + 1)).biUnion layer
  have hcop315 : (315 : ℕ).Coprime p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hdvd
    have : p ≤ 315 := Nat.le_of_dvd (by decide) hdvd
    have hcases : p ∣ 3 ∨ p ∣ 3 ∨ p ∣ 5 ∨ p ∣ 7 := by
      change p ∣ 3 * (3 * (5 * 7)) at hdvd
      simpa only [hp.dvd_mul] using hdvd
    rcases hcases with h | h | h | h <;> have := Nat.le_of_dvd (by decide) h <;> omega
  have hdisj : Set.PairwiseDisjoint (range (a + 1) : Set ℕ) layer := by
    intro k1 hk1 k2 hk2 hne
    change Disjoint (layer k1) (layer k2)
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [layer, Finset.mem_image] at hz1 hz2
    obtain ⟨d1, hd1, rfl⟩ := hz1
    obtain ⟨d2, hd2, heq⟩ := hz2
    have hd1_315 : d1 ∣ 315 := Nat.dvd_of_mem_divisors (hs_sub k1 (by simp at hk1; omega) hd1)
    have hd2_315 : d2 ∣ 315 := Nat.dvd_of_mem_divisors (hs_sub k2 (by simp at hk2; omega) hd2)
    have hpdvd : ∀ d, d ∣ 315 → ¬ p ∣ d := fun d hd hpd =>
      (hp.coprime_iff_not_dvd.mp hcop315.symm) (hpd.trans hd)
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hpow : p ^ k1 * p ^ (k2 - k1) = p ^ k2 := by
        rw [← pow_add, Nat.add_sub_of_le hlt.le]
      have h1 : d2 * p ^ (k2 - k1) = d1 := by
        have hpos : 0 < p ^ k1 := pow_pos hp.pos k1
        apply Nat.eq_of_mul_eq_mul_right hpos
        calc
          d2 * p ^ (k2 - k1) * p ^ k1 = d2 * (p ^ k1 * p ^ (k2 - k1)) := by ring
          _ = d2 * p ^ k2 := by rw [hpow]
          _ = d1 * p ^ k1 := heq
      have hpd : p ∣ d1 := by
        rw [← h1]
        exact dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) d2
      exact hpdvd d1 hd1_315 hpd
    · have hpow : p ^ k2 * p ^ (k1 - k2) = p ^ k1 := by
        rw [← pow_add, Nat.add_sub_of_le hgt.le]
      have h1 : d1 * p ^ (k1 - k2) = d2 := by
        have hpos : 0 < p ^ k2 := pow_pos hp.pos k2
        apply Nat.eq_of_mul_eq_mul_right hpos
        calc
          d1 * p ^ (k1 - k2) * p ^ k2 = d1 * (p ^ k2 * p ^ (k1 - k2)) := by ring
          _ = d1 * p ^ k1 := by rw [hpow]
          _ = d2 * p ^ k2 := heq.symm
      have hpd : p ∣ d2 := by
        rw [← h1]
        exact dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) d1
      exact hpdvd d2 hd2_315 hpd
  refine ⟨S, ?_, ?_⟩
  · intro z hz
    simp only [S, layer, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image] at hz
    obtain ⟨k, hk, d, hd, rfl⟩ := hz
    have hd315 : d ∣ 315 := Nat.dvd_of_mem_divisors (hs_sub k (by omega) hd)
    have hpk : p ^ k ∣ p ^ a := pow_dvd_pow p (by omega)
    exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul hd315 hpk,
      Nat.mul_ne_zero (by decide) (pow_ne_zero a hp.ne_zero)⟩
  · rw [Finset.sum_biUnion hdisj]
    have hlayer_sum : ∀ k ∈ range (a + 1), ∑ z ∈ layer k, z = c k * p ^ k := by
      intro k hk
      have hk' : k ≤ a := by simp at hk; omega
      have hinj : Set.InjOn (fun d => d * p ^ k) (s k : Set ℕ) := by
        intro d1 _ d2 _ h
        exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos k) h
      rw [Finset.sum_image hinj, ← Finset.sum_mul, hs_sum k hk']
    rw [Finset.sum_congr rfl hlayer_sum, hcsum]

private lemma coprime_315_of_prime_gt_seven {r : ℕ} (hr : r.Prime) (hgt : 7 < r) :
    (315 : ℕ).Coprime r := by
  rw [Nat.coprime_comm, hr.coprime_iff_not_dvd]
  intro hdvd
  have hcases : r ∣ 3 ∨ r ∣ 3 ∨ r ∣ 5 ∨ r ∣ 7 := by
    change r ∣ 3 * (3 * (5 * 7)) at hdvd
    simpa only [hr.dvd_mul] using hdvd
  rcases hcases with h | h | h | h <;> have := Nat.le_of_dvd (by decide) h <;> omega

private lemma sum_divisors_315 : ∑ d ∈ (315 : ℕ).divisors, d = 624 := by
  have h9 : ∑ d ∈ (3 ^ 2 : ℕ).divisors, d = 13 :=
    factored_power 3 2 13 (by decide) (by decide)
  have h5 : ∑ d ∈ (5 ^ 1 : ℕ).divisors, d = 6 :=
    factored_power 5 1 6 (by decide) (by decide)
  have h7 : ∑ d ∈ (7 ^ 1 : ℕ).divisors, d = 8 :=
    factored_power 7 1 8 (by decide) (by decide)
  have h35 : ∑ d ∈ (5 * 7 : ℕ).divisors, d = 48 :=
    factored_pair 5 7 6 8 (by decide) (by simpa using h5) (by simpa using h7)
  exact factored_pair 9 35 13 48 (by decide) (by simpa using h9) h35

private lemma pseudoperfect_of_excess_subset {m : ℕ} (hm : 0 < m) {T : Finset ℕ}
    (hTsub : T ⊆ m.properDivisors)
    (hTsum : ∑ d ∈ T, d + 2 * m = ∑ d ∈ m.divisors, d) :
    m.Pseudoperfect := by
  have htot : ∑ d ∈ m.divisors, d = ∑ d ∈ m.properDivisors, d + m :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  have hsplit := Finset.sum_sdiff hTsub (f := id)
  change (∑ d ∈ m.properDivisors \ T, d) + (∑ d ∈ T, d) = ∑ d ∈ m.properDivisors, d at hsplit
  refine ⟨hm, m.properDivisors \ T, Finset.sdiff_subset, ?_⟩
  omega

private lemma choose_shift_div {q : ℕ} (hq_lo : 107 ≤ q) (hq_hi : q < 5565) :
    ∃ d0 : ℕ, d0 ∣ 315 ∧ d0 ≤ 35 ∧ 2600 ≤ d0 * q ∧ d0 * q ≤ 13020 := by
  by_cases h1 : 2600 ≤ q
  · exact ⟨1, by decide, by omega, by omega, by omega⟩
  · by_cases h2 : 867 ≤ q
    · exact ⟨3, by decide, by omega, by omega, by omega⟩
    · by_cases h3 : 372 ≤ q
      · exact ⟨7, by decide, by omega, by omega, by omega⟩
      · exact ⟨35, by decide, by omega, by omega, by omega⟩

end OMA.Erdos470R2H2R1H1

open Finset
open OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1
open OMA.Erdos470R2H2R1H1

theorem OMA.solution : OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1.H1 := by
  classical
  intro n hodd hab hcard he3 he5 he7 ⟨p, hp, hp_lo, hp_hi, hp_dvd⟩ hbound
  have hn : 0 < n := hodd.pos
  have hn0 : n ≠ 0 := hn.ne'
  have m3 : 3 ∈ n.primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨by decide, ?_, hn0⟩
    have h1 : 3 ^ 2 ∣ n := (Nat.Prime.pow_dvd_iff_le_factorization (by decide) hn0).mpr (by omega)
    exact dvd_trans (by decide : 3 ∣ 3 ^ 2) h1
  have m5 : 5 ∈ n.primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨by decide, ?_, hn0⟩
    simpa using (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 5) hn0 (k := 1)).mpr (by omega)
  have m7 : 7 ∈ n.primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨by decide, ?_, hn0⟩
    simpa using (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 7) hn0 (k := 1)).mpr (by omega)
  have mp : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hp_dvd, hn0⟩
  have h315_dvd : 315 ∣ n := by
    have d9 : 9 ∣ n := (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 3) hn0 (k := 2)).mpr (by omega)
    have d5 : 5 ∣ n := Nat.dvd_of_mem_primeFactors m5
    have d7 : 7 ∣ n := Nat.dvd_of_mem_primeFactors m7
    exact combine_dvd (combine_dvd d9 d5 (by decide)) d7 (by decide)
  let base4 : Finset ℕ := {3, 5, 7, p}
  have hbase4_sub : base4 ⊆ n.primeFactors := by
    intro r hr
    simp only [base4, mem_insert, mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  have hbase4_card : base4.card = 4 := by
    change ({3, 5, 7, p} : Finset ℕ).card = 4
    rw [card_insert_of_notMem (by simp; omega),
        card_insert_of_notMem (by simp; omega),
        card_insert_of_notMem (by simp; omega),
        card_singleton]
  have hdiff_card : (n.primeFactors \ base4).card = 1 := by
    rw [Finset.card_sdiff_of_subset hbase4_sub, hcard, hbase4_card]
  obtain ⟨q, hq_eq⟩ := Finset.card_eq_one.mp hdiff_card
  have hq_mem_diff : q ∈ n.primeFactors \ base4 := by rw [hq_eq]; exact mem_singleton_self q
  obtain ⟨mq, hq_not_base4⟩ := mem_sdiff.mp hq_mem_diff
  have hq : q.Prime := Nat.prime_of_mem_primeFactors mq
  have hq_dvd : q ∣ n := Nat.dvd_of_mem_primeFactors mq
  have hq_lt5565 : q < 5565 := hbound q mq
  have hq_ne : q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ p := by
    simpa [base4, mem_insert, mem_singleton, not_or] using hq_not_base4
  have hq_ne2 : q ≠ 2 := fun h => hodd.not_two_dvd_nat (h ▸ hq_dvd)
  have hq_gt7 : 7 < q := by
    by_contra! hle
    have cert : ∀ j : Fin 8, j.val.Prime → j.val ∈ ([2, 3, 5, 7] : List ℕ) := by decide
    have hv := cert ⟨q, by omega⟩ hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    omega
  by_cases hq_small : q < 107
  · have hcop : (315 : ℕ).Coprime q := coprime_315_of_prime_gt_seven hq hq_gt7
    exact pseudoperfect_multiple (combine_dvd h315_dvd hq_dvd hcop) hn
      (small_multiple q hq hq_gt7 hq_small)
  · have hq_lo : 107 ≤ q := by omega
    have hpf_eq : n.primeFactors = {3, 5, 7, p, q} := by
      have hu : base4 ∪ (n.primeFactors \ base4) = n.primeFactors := Finset.union_sdiff_of_subset hbase4_sub
      rw [hq_eq] at hu
      rw [← hu]
      ext r
      simp only [base4, mem_union, mem_insert, mem_singleton]
      tauto
    let a := n.factorization p
    let b := n.factorization q
    have ha_pos : 1 ≤ a := at_least_one mp
    have hb_pos : 1 ≤ b := at_least_one mq
    have hn_eq : n = 315 * p ^ a * q ^ b := by
      have hprod := Nat.prod_primeFactors_pow_factorization hn0
      rw [hpf_eq] at hprod
      have h3_ni : (3 : ℕ) ∉ ({5, 7, p, q} : Finset ℕ) := by simp; omega
      have h5_ni : (5 : ℕ) ∉ ({7, p, q} : Finset ℕ) := by simp; omega
      have h7_ni : (7 : ℕ) ∉ ({p, q} : Finset ℕ) := by simp; omega
      have hp_ni : p ∉ ({q} : Finset ℕ) := by simp; omega
      rw [prod_insert h3_ni, prod_insert h5_ni, prod_insert h7_ni, prod_insert hp_ni, prod_singleton] at hprod
      rw [he3, he5, he7] at hprod
      change n = 3 ^ 2 * (5 ^ 1 * (7 ^ 1 * (p ^ a * q ^ b))) at hprod
      linarith
    have hcop_315_p : (315 : ℕ).Coprime p := coprime_315_of_prime_gt_seven hp (by omega)
    have hcop_315_q : (315 : ℕ).Coprime q := coprime_315_of_prime_gt_seven hq hq_gt7
    have hcop_pq : p.Coprime q := (Nat.coprime_primes hp hq).mpr hq_ne.2.2.2.symm
    have hcop_315pa_q : (315 * p ^ a).Coprime q :=
      (hcop_315_q).mul_left (hcop_pq.pow_left a)
    let f : ℕ → ℕ := fun k => 315 * p ^ a * q ^ k
    have hf_pos : ∀ k, 0 < f k := fun k => by
      dsimp [f]
      exact Nat.mul_pos (Nat.mul_pos (by decide) (pow_pos hp.pos a)) (pow_pos hq.pos k)
    have hsigma_315pa : ∑ d ∈ (315 * p ^ a).divisors, d = 624 * geomSum p a := by
      rw [factored_pair 315 (p ^ a) 624 (geomSum p a) (hcop_315_p.pow_right a)
        sum_divisors_315 (power_sum p a hp)]
    have hsigma_f : ∀ k, ∑ d ∈ (f k).divisors, d = 624 * geomSum p a * geomSum q k := by
      intro k
      exact factored_pair (315 * p ^ a) (q ^ k) (624 * geomSum p a) (geomSum q k)
        (hcop_315pa_q.pow_right k) hsigma_315pa (power_sum q k hq)
    have hf0_not_ab : ¬ 2 * f 0 < ∑ d ∈ (f 0).divisors, d := by
      rw [hsigma_f 0, geomSum_zero, mul_one]
      have hg := geomSum_mul_pred p a (by omega)
      have hpa : f 0 = 315 * p ^ a := by simp [f]
      rw [hpa]
      have hkey : (p - 1) * (624 * geomSum p a) < (p - 1) * (2 * (315 * p ^ a)) := by
        have h1 : (p - 1) * (624 * geomSum p a) + 624 = 624 * p ^ (a + 1) := by
          calc
            (p - 1) * (624 * geomSum p a) + 624 = 624 * ((p - 1) * geomSum p a + 1) := by ring
            _ = 624 * p ^ (a + 1) := by rw [hg]
        have h2 : 624 * p ≤ 630 * (p - 1) := by omega
        have h3 : 624 * p ^ (a + 1) ≤ (p - 1) * (2 * (315 * p ^ a)) := by
          calc
            624 * p ^ (a + 1) = (624 * p) * p ^ a := by rw [pow_succ']; ring
            _ ≤ (630 * (p - 1)) * p ^ a := Nat.mul_le_mul_right _ h2
            _ = (p - 1) * (2 * (315 * p ^ a)) := by ring
        omega
      intro hlt
      have hpm := Nat.mul_lt_mul_of_pos_left hlt (show 0 < p - 1 by omega)
      omega
    have hfb_ab : 2 * f b < ∑ d ∈ (f b).divisors, d := by
      have hfb_eq : f b = n := hn_eq.symm
      rw [hfb_eq]
      have h := Nat.abundant_iff_two_lt_abundancyIndex.mp hab
      rw [Nat.abundancyIndex, lt_div_iff₀ (show (0 : ℚ) < n by exact_mod_cast hn)] at h
      have h' : ((2 * n : ℕ) : ℚ) < ((∑ d ∈ n.divisors, d : ℕ) : ℚ) := by
        simpa [Nat.cast_mul, Nat.cast_sum] using h
      exact_mod_cast h'
    have hex : ∃ k, 2 * f k < ∑ d ∈ (f k).divisors, d := ⟨b, hfb_ab⟩
    let k0 := Nat.find hex
    have hk0_spec : 2 * f k0 < ∑ d ∈ (f k0).divisors, d := Nat.find_spec hex
    have hk0_le : k0 ≤ b := Nat.find_min' hex hfb_ab
    have hk0_ne0 : k0 ≠ 0 := by
      intro h0
      rw [h0] at hk0_spec
      exact hf0_not_ab hk0_spec
    obtain ⟨j, hj_eq⟩ := Nat.exists_eq_succ_of_ne_zero hk0_ne0
    have hj_not_ab : ∑ d ∈ (f j).divisors, d ≤ 2 * f j := by
      have hlt : j < k0 := by omega
      have hnot := Nat.find_min hex hlt
      omega
    have hfj_dvd : f j ∣ n := by
      rw [hn_eq]
      exact Nat.mul_dvd_mul_left (315 * p ^ a) (pow_dvd_pow q (by omega))
    by_cases hperf : ∑ d ∈ (f j).divisors, d = 2 * f j
    · have hfj_pp : (f j).Pseudoperfect := by
        refine ⟨hf_pos j, (f j).properDivisors, Subset.rfl, ?_⟩
        have htot : ∑ d ∈ (f j).divisors, d = ∑ d ∈ (f j).properDivisors, d + f j :=
          Nat.sum_divisors_eq_sum_properDivisors_add_self
        omega
      exact pseudoperfect_multiple hfj_dvd hn hfj_pp
    · have hj_def : ∑ d ∈ (f j).divisors, d + 1 ≤ 2 * f j := by omega
      let m := f (j + 1)
      have hm_pos : 0 < m := hf_pos (j + 1)
      have hm_dvd : m ∣ n := by
        rw [hn_eq]
        exact Nat.mul_dvd_mul_left (315 * p ^ a) (pow_dvd_pow q (by omega))
      have hm_ab : 2 * m < ∑ d ∈ m.divisors, d := by
        dsimp [m]
        rw [show j + 1 = k0 from hj_eq.symm]
        exact hk0_spec
      have hgeom_q : geomSum q (j + 1) = q * geomSum q j + 1 := by
        have h1 := geomSum_mul_pred q j (by omega)
        have h2 := geomSum_succ q j
        have h3 : q * geomSum q j = (q - 1) * geomSum q j + geomSum q j := by
          rw [show (q - 1) * geomSum q j + geomSum q j = ((q - 1) + 1) * geomSum q j by ring,
            Nat.sub_add_cancel (by omega)]
        omega
      have hsigma_step : ∑ d ∈ m.divisors, d = q * (∑ d ∈ (f j).divisors, d) + Mval p a := by
        dsimp [m, Mval]
        rw [hsigma_f (j + 1), hsigma_f j, hgeom_q]
        ring
      have h2m_step : 2 * m = q * (2 * f j) := by
        dsimp [m, f]
        rw [pow_succ]
        ring
      let E := (∑ d ∈ m.divisors, d) - 2 * m
      have hE_sum : E + 2 * m = ∑ d ∈ m.divisors, d := Nat.sub_add_cancel hm_ab.le
      have hE_pos : 1 ≤ E := by omega
      have h6_dvd_E : 6 ∣ E := by
        have h6_sig : 6 ∣ ∑ d ∈ m.divisors, d := by
          dsimp [m]
          rw [hsigma_f (j + 1)]
          exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by decide : 6 ∣ 624) _) _
        have h6_2m : 6 ∣ 2 * m := by
          dsimp [m, f]
          have : 2 * (315 * p ^ a * q ^ (j + 1)) = 6 * (105 * p ^ a * q ^ (j + 1)) := by ring
          rw [this]
          exact dvd_mul_right 6 _
        exact (Nat.dvd_add_left h6_2m).mp (hE_sum.symm ▸ h6_sig)
      have hE_ne2 : E ≠ 2 := by
        intro h2
        rw [h2] at h6_dvd_E
        exact absurd h6_dvd_E (by decide)
      have hE_hi : E + q ≤ Mval p a := by
        have hmul : q * (∑ d ∈ (f j).divisors, d) + q ≤ q * (2 * f j) := by
          calc
            q * (∑ d ∈ (f j).divisors, d) + q = q * ((∑ d ∈ (f j).divisors, d) + 1) := by ring
            _ ≤ q * (2 * f j) := Nat.mul_le_mul_left q hj_def
        omega
      have hE_le : E ≤ Mval p a := by omega
      have hE_neM2 : E ≠ Mval p a - 2 := by omega
      have hsub_prop : (315 * p ^ a).divisors ⊆ m.properDivisors := by
        intro d hd
        have hd_dvd : d ∣ 315 * p ^ a := Nat.dvd_of_mem_divisors hd
        have h315pa_pos : 0 < 315 * p ^ a := Nat.mul_pos (by decide) (pow_pos hp.pos a)
        have hqpow_gt1 : 1 < q ^ (j + 1) := one_lt_pow₀ hq.one_lt (Nat.succ_ne_zero j)
        refine Nat.mem_properDivisors.mpr ⟨hd_dvd.trans (dvd_mul_right _ _), ?_⟩
        calc
          d ≤ 315 * p ^ a := Nat.le_of_dvd h315pa_pos hd_dvd
          _ = 315 * p ^ a * 1 := (mul_one _).symm
          _ < 315 * p ^ a * q ^ (j + 1) := Nat.mul_lt_mul_of_pos_left hqpow_gt1 h315pa_pos
      have hm_pp : m.Pseudoperfect := by
        by_cases hmid : E < 307 * p ^ a ∨ 319 * p ^ a < E
        · obtain ⟨S, hSsub, hSsum⟩ :=
            rep_layer_divisors hp hp_lo (by omega) ⟨hE_le, hE_ne2, hE_neM2, hmid⟩
          exact pseudoperfect_of_excess_subset hm_pos (hSsub.trans hsub_prop) (by omega)
        · have hE_lo_mid : 307 * p ^ a ≤ E := by omega
          have hE_hi_mid : E ≤ 319 * p ^ a := by omega
          obtain ⟨d0, hd0_dvd, hd0_le, hd0_lo, hd0_hi⟩ := choose_shift_div hq_lo hq_lt5565
          let Q := p ^ (a - 1)
          have hQ_pos : 1 ≤ Q := Nat.one_le_pow (a - 1) p hp.pos
          have hpa_eq : p ^ a = p * Q := by
            have : a = (a - 1) + 1 := by omega
            conv_lhs => rw [this, pow_succ']
          let Δ := d0 * Q * q
          have hΔ_lo : 12 * p ^ a < Δ := by
            have h1 : 12 * p < 2600 := by omega
            calc
              12 * p ^ a = (12 * p) * Q := by rw [hpa_eq]; ring
              _ < 2600 * Q := Nat.mul_lt_mul_of_pos_right h1 hQ_pos
              _ ≤ (d0 * q) * Q := Nat.mul_le_mul_right Q hd0_lo
              _ = Δ := by dsimp [Δ]; ring
          have hΔ_hi : Δ ≤ 122 * p ^ a := by
            have h1 : 13020 ≤ 122 * p := by omega
            calc
              Δ = (d0 * q) * Q := by dsimp [Δ]; ring
              _ ≤ 13020 * Q := Nat.mul_le_mul_right Q hd0_hi
              _ ≤ (122 * p) * Q := Nat.mul_le_mul_right Q h1
              _ = 122 * p ^ a := by rw [hpa_eq]; ring
          let E' := E - Δ
          have hE'_good : Good p a E' := by
            have hM624 : 624 * p ^ a ≤ Mval p a := Mval_ge_624_mul p a
            have hpa_pos : 1 ≤ p ^ a := Nat.one_le_pow a p hp.pos
            refine ⟨by omega, by omega, by omega, Or.inl (by omega)⟩
          obtain ⟨S, hSsub, hSsum⟩ := rep_layer_divisors hp hp_lo (by omega) hE'_good
          have hΔ_notMem : Δ ∉ S := by
            intro hmem
            have hdvd : Δ ∣ 315 * p ^ a := Nat.dvd_of_mem_divisors (hSsub hmem)
            have hqdvd : q ∣ 315 * p ^ a := (dvd_mul_left q (d0 * Q)).trans hdvd
            exact (hq.coprime_iff_not_dvd.mp hcop_315pa_q.symm) hqdvd
          have hΔ_prop : Δ ∈ m.properDivisors := by
            have hdvd : Δ ∣ m := by
              dsimp [Δ, m, f, Q]
              have h1 : d0 * p ^ (a - 1) ∣ 315 * p ^ a :=
                Nat.mul_dvd_mul hd0_dvd (pow_dvd_pow p (Nat.sub_le a 1))
              have h2 : q ∣ q ^ (j + 1) := dvd_pow_self q (Nat.succ_ne_zero j)
              exact Nat.mul_dvd_mul h1 h2
            have hlt : Δ < m := by
              dsimp [Δ, m, f, Q]
              have h1 : d0 * p ^ (a - 1) < 315 * p ^ a := by
                have hle1 : p ^ (a - 1) ≤ p ^ a := Nat.pow_le_pow_right hp.pos (Nat.sub_le a 1)
                have hpos : 0 < p ^ a := pow_pos hp.pos a
                calc
                  d0 * p ^ (a - 1) ≤ 35 * p ^ a := Nat.mul_le_mul hd0_le hle1
                  _ < 315 * p ^ a := Nat.mul_lt_mul_of_pos_right (by omega) hpos
              have h2 : q ≤ q ^ (j + 1) := by
                simpa using Nat.pow_le_pow_right hq.pos (show 1 ≤ j + 1 by omega)
              exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h1 hq.pos)
                (Nat.mul_le_mul_left _ h2)
            exact Nat.mem_properDivisors.mpr ⟨hdvd, hlt⟩
          refine pseudoperfect_of_excess_subset hm_pos (T := insert Δ S)
            (Finset.insert_subset hΔ_prop (hSsub.trans hsub_prop)) ?_
          rw [Finset.sum_insert hΔ_notMem, hSsum]
          omega
      exact pseudoperfect_multiple hm_dvd hn hm_pp
