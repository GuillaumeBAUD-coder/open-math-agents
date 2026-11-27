import FormalConjectures.Wikipedia.Grimm

/-!
Reduction of weak Grimm conjecture to a smooth-number count bound in the logarithmic-power
(Baker / Ramachandra-Shorey-Tijdeman) regime and a sub-Cramer prime-gap bound.

Unconditionally proved inside this reduction:
1. Bertrand bound (`k < n` and `4 ≤ n`) for every consecutive composite run;
2. Erdos-Grimm LCM maximizer deletion: if fewer than `k` distinct primes divide the product,
   then some element divides `lcm(1, ..., k - 1)`, forcing `n ≤ lcm(1, ..., k - 1)`;
3. Small-`k` elimination (`k ≤ 7`) via explicit prime hits on `[4, 60]`;
4. Prime-splitting smooth-count inequality: `π(k) + (k - |S_smooth|) ≤ ω(∏ (n + j))`.
-/

namespace OMA.R_Grimm_grimm_conjecture_weak_R1

open Finset Nat

def H1 : Prop :=
  ∀ n k : ℕ, 8 ≤ k → k < n → n ≤ (Finset.Ico 1 k).lcm id →
    (∃ j : Fin k, (n + j) ∣ (Finset.Ico 1 k).lcm id) →
    k ^ 2 ≤ (Nat.log 2 n) ^ 5 →
    (∀ i : Fin k, (n + i).Composite) →
    (Finset.univ.filter (fun j : Fin k => (n + j) ∈ Nat.smoothNumbers (k + 1))).card ≤
      Nat.primeCounting k

def H2 : Prop :=
  ∀ n k : ℕ, 8 ≤ k → (∀ i : Fin k, (n + i).Composite) →
    k ^ 2 ≤ (Nat.log 2 n) ^ 5

lemma bertrand_lt_of_composite (n k : ℕ) (hk : 1 ≤ k)
    (h : ∀ i : Fin k, (n + i).Composite) : k < n ∧ 4 ≤ n := by
  have hncomp : n.Composite := by simpa using h ⟨0, hk⟩
  have hn4 : 4 ≤ n := by
    rcases hncomp with ⟨h1, hnp⟩
    have : n ≠ 2 := by rintro rfl; exact hnp Nat.prime_two
    have : n ≠ 3 := by rintro rfl; exact hnp Nat.prime_three
    omega
  obtain ⟨p, hp, hnp, hp2n⟩ := Nat.bertrand n (by omega)
  have hp_lt : p < 2 * n := by
    rcases lt_or_eq_of_le hp2n with hlt | heq
    · exact hlt
    · exfalso
      have hd : 2 ∣ p := ⟨n, heq⟩
      rcases hp.eq_one_or_self_of_dvd 2 hd with h2 | h2 <;> omega
  have hnk : p ∉ Finset.Ico n (n + k) := by
    intro hmem
    rw [Finset.mem_Ico] at hmem
    have hi : p - n < k := by omega
    have := (h ⟨p - n, hi⟩).2
    rw [show n + (p - n) = p by omega] at this
    exact this hp
  rw [Finset.mem_Ico, not_and] at hnk
  have : n + k ≤ p := by
    by_contra hlt
    exact hnk hnp.le (by omega)
  omega

lemma exists_emb_of_card_primeFactors_le (n k : ℕ)
    (hcard : k ≤ (∏ j : Fin k, (n + j)).primeFactors.card) :
    ∃ ps : Fin k ↪ ℕ, ∀ i : Fin k, (ps i).Prime ∧ ∃ j : Fin k, ps i ∣ (n + j) := by
  let P := (∏ j : Fin k, (n + j)).primeFactors
  obtain ⟨S, hSP, hScard⟩ := Finset.exists_subset_card_eq hcard
  let e : Fin k ↪o ℕ := S.orderEmbOfFin hScard
  refine ⟨e.toEmbedding, fun i => ?_⟩
  have hmem : e i ∈ P := hSP (Finset.orderEmbOfFin_mem S hScard i)
  have hp : (e i).Prime := Nat.prime_of_mem_primeFactors hmem
  have hdvd : e i ∣ ∏ j : Fin k, (n + j) := Nat.dvd_of_mem_primeFactors hmem
  obtain ⟨j, _, hj⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd
  exact ⟨hp, j, hj⟩

lemma exists_dvd_lcm_of_card_lt (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hlt : (∏ j : Fin k, (n + j)).primeFactors.card < k) :
    ∃ j : Fin k, (n + j) ∣ (Finset.Ico 1 k).lcm id := by
  classical
  let P := (∏ j : Fin k, (n + j)).primeFactors
  have hprod_ne : (∏ j : Fin k, (n + j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => by omega
  have hmax : ∀ p ∈ P, ∃ j₀ : Fin k, ∀ j : Fin k,
      (n + j).factorization p ≤ (n + j₀).factorization p := fun p _ =>
    (Finset.exists_max_image Finset.univ (fun j : Fin k => (n + j).factorization p)
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩).imp fun j₀ hj₀ => fun j => hj₀.2 j (Finset.mem_univ j)
  choose jmax hjmax using fun p (hp : p ∈ P) => hmax p hp
  let M : Finset (Fin k) := P.attach.image fun p => jmax p.1 p.2
  have hMcard : M.card ≤ P.card := by
    calc M.card ≤ P.attach.card := Finset.card_image_le
      _ = P.card := Finset.card_attach
  have hdiff : (Finset.univ \ M).Nonempty := by
    rw [← Finset.card_pos]
    have hle : M.card < (Finset.univ : Finset (Fin k)).card := by
      simpa [Finset.card_univ, Fintype.card_fin] using hMcard.trans_lt hlt
    have := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin k)) M
    have hinter : (Finset.univ ∩ M).card = M.card := by simp
    omega
  obtain ⟨j, hj⟩ := hdiff
  rw [Finset.mem_sdiff] at hj
  refine ⟨j, ?_⟩
  let L := (Finset.Ico 1 k).lcm id
  have hL_ne : L ≠ 0 := by
    rw [Finset.lcm_ne_zero_iff]
    intro x hx
    rw [Finset.mem_Ico] at hx
    simp; omega
  rw [← Nat.factorization_prime_le_iff_dvd (by omega : n + j ≠ 0) hL_ne]
  intro p hp
  by_cases hpd : p ∣ n + j
  · have hpP : p ∈ P := by
      rw [Nat.mem_primeFactors]
      refine ⟨hp, hpd.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)), hprod_ne⟩
    let j₀ := jmax p hpP
    have hj₀_mem : j₀ ∈ M := Finset.mem_image.mpr ⟨⟨p, hpP⟩, Finset.mem_attach _ _, rfl⟩
    have hne : j ≠ j₀ := fun heq => hj.2 (heq ▸ hj₀_mem)
    have hle_fac : (n + j).factorization p ≤ (n + j₀).factorization p := hjmax p hpP j
    have hpow_dvd_j : p ^ (n + j).factorization p ∣ n + j :=
      (hp.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl
    have hpow_dvd_j₀ : p ^ (n + j).factorization p ∣ n + j₀ :=
      (hp.pow_dvd_iff_le_factorization (by omega)).mpr hle_fac
    have hpow_dvd_diff : p ^ (n + j).factorization p ∣
        (max (j : ℕ) (j₀ : ℕ) - min (j : ℕ) (j₀ : ℕ)) := by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt' | hlt'
      · rw [max_eq_right hlt'.le, min_eq_left hlt'.le]
        have heq : n + (j₀ : ℕ) - (n + (j : ℕ)) = (j₀ : ℕ) - (j : ℕ) := by omega
        rw [← heq]
        exact Nat.dvd_sub hpow_dvd_j₀ hpow_dvd_j
      · rw [max_eq_left hlt'.le, min_eq_right hlt'.le]
        have heq : n + (j : ℕ) - (n + (j₀ : ℕ)) = (j : ℕ) - (j₀ : ℕ) := by omega
        rw [← heq]
        exact Nat.dvd_sub hpow_dvd_j hpow_dvd_j₀
    have hdiff_mem : max (j : ℕ) (j₀ : ℕ) - min (j : ℕ) (j₀ : ℕ) ∈ Finset.Ico 1 k := by
      rw [Finset.mem_Ico]
      have hne' : (j : ℕ) ≠ (j₀ : ℕ) := Fin.val_ne_of_ne hne
      omega
    have hpow_dvd_L : p ^ (n + j).factorization p ∣ L :=
      hpow_dvd_diff.trans (Finset.dvd_lcm hdiff_mem)
    exact (hp.pow_dvd_iff_le_factorization hL_ne).mp hpow_dvd_L
  · rw [Nat.factorization_eq_zero_of_not_dvd hpd]
    exact zero_le _

lemma small_k_composite_gt_lcm :
    ∀ k : ℕ, 1 ≤ k → k ≤ 7 → ∀ n : ℕ,
      (∀ i : Fin k, (n + i).Composite) → (Finset.Ico 1 k).lcm id < n := by
  intro k hk1 hk7 n h
  have hn4 : 4 ≤ n := (bertrand_lt_of_composite n k hk1 h).2
  by_contra hle
  push Not at hle
  have hL60 : (Finset.Ico 1 k).lcm id ≤ 60 := by
    interval_cases k <;> decide
  have hn60 : n ≤ 60 := hle.trans hL60
  have hsmallPrimes :
      ∀ p ∈ ([5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61] : List ℕ),
        p.Prime := by
    decide
  have hhit4 : ∀ m ∈ Finset.Icc 4 6,
      ∃ p ∈ ([5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61] : List ℕ),
        m ≤ p ∧ p < m + 4 := by decide
  have hhit5 : ∀ m ∈ Finset.Icc 4 12,
      ∃ p ∈ ([5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61] : List ℕ),
        m ≤ p ∧ p < m + 5 := by decide
  have hhit6 : ∀ m ∈ Finset.Icc 4 60,
      ∃ p ∈ ([5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61] : List ℕ),
        m ≤ p ∧ p < m + 6 := by decide
  have aux : ∀ p, p.Prime → n ≤ p → p < n + k → False := fun p hp hnp hpk =>
    (h ⟨p - n, by omega⟩).2 (by rwa [show n + (p - n) = p by omega])
  interval_cases k
  · have hL : (Finset.Ico 1 1).lcm id = 1 := by decide
    omega
  · have hL : (Finset.Ico 1 2).lcm id = 1 := by decide
    omega
  · have hL : (Finset.Ico 1 3).lcm id = 2 := by decide
    omega
  · have hL : (Finset.Ico 1 4).lcm id = 6 := by decide
    obtain ⟨p, hp, hnp, hpk⟩ := hhit4 n (Finset.mem_Icc.mpr ⟨hn4, by omega⟩)
    exact aux p (hsmallPrimes p hp) hnp hpk
  · have hL : (Finset.Ico 1 5).lcm id = 12 := by decide
    obtain ⟨p, hp, hnp, hpk⟩ := hhit5 n (Finset.mem_Icc.mpr ⟨hn4, by omega⟩)
    exact aux p (hsmallPrimes p hp) hnp hpk
  · obtain ⟨p, hp, hnp, hpk⟩ := hhit6 n (Finset.mem_Icc.mpr ⟨hn4, hn60⟩)
    exact aux p (hsmallPrimes p hp) hnp hpk
  · obtain ⟨p, hp, hnp, hpk⟩ := hhit6 n (Finset.mem_Icc.mpr ⟨hn4, hn60⟩)
    exact aux p (hsmallPrimes p hp) hnp (by omega)

lemma primeCounting_add_smooth_le (n k : ℕ) (hn : 1 ≤ n) :
    Nat.primeCounting k +
      (k - (Finset.univ.filter (fun j : Fin k => (n + j) ∈ Nat.smoothNumbers (k + 1))).card) ≤
      (∏ j : Fin k, (n + j)).primeFactors.card := by
  classical
  let P := (∏ j : Fin k, (n + j)).primeFactors
  let P_le := P.filter (· ≤ k)
  let P_gt := P.filter (k < ·)
  let S_sm := Finset.univ.filter (fun j : Fin k => (n + j) ∈ Nat.smoothNumbers (k + 1))
  let S_lg := Finset.univ.filter (fun j : Fin k => (n + j) ∉ Nat.smoothNumbers (k + 1))
  have hprod_ne : (∏ j : Fin k, (n + j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => by omega
  have hP_part : P_le.card + P_gt.card = P.card := by
    have hdisj : Disjoint P_le P_gt :=
      Finset.disjoint_filter.mpr fun p _ h1 h2 => by omega
    have hunion : P_le ∪ P_gt = P := by
      ext p
      simp only [P_le, P_gt, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
      · intro hp
        rcases le_or_gt p k with h | h
        · exact Or.inl ⟨hp, h⟩
        · exact Or.inr ⟨hp, h⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hPle_eq : P_le = Nat.primesLE k := by
    ext p
    simp only [P_le, P, Finset.mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, _, _⟩, hpk⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hpk', hp⟩
      have hpk : p ≤ k := by omega
      refine ⟨⟨hp, ?_, hprod_ne⟩, hpk⟩
      let r := n % p
      have hr : r < p := Nat.mod_lt n hp.pos
      let jv := if r = 0 then 0 else p - r
      have hjv : jv < p := by
        dsimp [jv]
        split_ifs <;> omega
      have hdvd : p ∣ n + jv := by
        apply Nat.dvd_of_mod_eq_zero
        dsimp [jv, r]
        split_ifs with h0
        · rw [Nat.add_zero, h0]
        · have hmod : (n + (p - n % p)) % p = (n % p + (p - n % p)) % p := by
            rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : p - n % p < p)]
          rw [hmod, Nat.add_sub_cancel' hr.le, Nat.mod_self]
      exact hdvd.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨jv, hjv.trans_le hpk⟩ : Fin k)))
  have hPle_card : P_le.card = Nat.primeCounting k := by
    rw [hPle_eq, Nat.primesLE_card_eq_primeCounting]
  have hS_part : S_sm.card + S_lg.card = k := by
    have hdisj : Disjoint S_sm S_lg :=
      Finset.disjoint_filter.mpr fun j _ h1 h2 => h2 h1
    have hunion : S_sm ∪ S_lg = Finset.univ := by
      ext j
      simp [S_sm, S_lg, em]
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  have hS_lg_le : S_lg.card ≤ P_gt.card := by
    have hex : ∀ j ∈ S_lg, ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ n + j := by
      intro j hj
      rw [Finset.mem_filter] at hj
      have hnot := hj.2
      rw [Nat.mem_smoothNumbers'] at hnot
      push Not at hnot
      obtain ⟨p, hp, hpd, hkp⟩ := hnot
      exact ⟨p, hp, by omega, hpd⟩
    choose f hf using fun j (hj : j ∈ S_lg) => hex j hj
    let g : Fin k → ℕ := fun j => if hj : j ∈ S_lg then f j hj else 0
    have hinj : Set.InjOn g S_lg := by
      intro j₁ hj₁ j₂ hj₂ heq
      rw [Finset.mem_coe] at hj₁ hj₂
      dsimp [g] at heq
      rw [dif_pos hj₁, dif_pos hj₂] at heq
      have hf₁ := hf j₁ hj₁
      have hf₂ := hf j₂ hj₂
      let p := f j₁ hj₁
      have hp : p.Prime := hf₁.1
      have hkp : k < p := hf₁.2.1
      have hpd₁ : p ∣ n + j₁ := hf₁.2.2
      have hpd₂ : p ∣ n + j₂ := by simpa [p, heq] using hf₂.2.2
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
      · have hd : p ∣ (j₂ : ℕ) - (j₁ : ℕ) := by
          have heq' : n + (j₂ : ℕ) - (n + (j₁ : ℕ)) = (j₂ : ℕ) - (j₁ : ℕ) := by omega
          rw [← heq']
          exact Nat.dvd_sub hpd₂ hpd₁
        have hpos : 0 < (j₂ : ℕ) - (j₁ : ℕ) := by omega
        have hle := Nat.le_of_dvd hpos hd
        omega
      · have hd : p ∣ (j₁ : ℕ) - (j₂ : ℕ) := by
          have heq' : n + (j₁ : ℕ) - (n + (j₂ : ℕ)) = (j₁ : ℕ) - (j₂ : ℕ) := by omega
          rw [← heq']
          exact Nat.dvd_sub hpd₁ hpd₂
        have hpos : 0 < (j₁ : ℕ) - (j₂ : ℕ) := by omega
        have hle := Nat.le_of_dvd hpos hd
        omega
    have himg : S_lg.image g ⊆ P_gt := by
      intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨j, hj, rfl⟩ := hp
      dsimp [g]
      rw [dif_pos hj]
      have hfj := hf j hj
      rw [Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hfj.1, hfj.2.2.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)), hprod_ne⟩, hfj.2.1⟩
    calc S_lg.card = (S_lg.image g).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ P_gt.card := Finset.card_le_card himg
  change Nat.primeCounting k + (k - S_sm.card) ≤ P.card
  omega

theorem main : H1 → H2 → type_of% @Grimm.grimm_conjecture_weak := by
  intro h1 h2 n k hn hk h
  apply exists_emb_of_card_primeFactors_le n k
  by_contra! hlt
  obtain ⟨j, hj_dvd⟩ := exists_dvd_lcm_of_card_lt n k hn hk hlt
  have hL_pos : 0 < (Finset.Ico 1 k).lcm id := by
    rw [Nat.pos_iff_ne_zero, Finset.lcm_ne_zero_iff]
    intro x hx
    rw [Finset.mem_Ico] at hx
    simp; omega
  have hle_lcm : n ≤ (Finset.Ico 1 k).lcm id :=
    (by omega : n ≤ n + j).trans (Nat.le_of_dvd hL_pos hj_dvd)
  have hk8 : 8 ≤ k := by
    by_contra hk7
    have hgt := small_k_composite_gt_lcm k hk (by omega) n h
    omega
  have hkn : k < n := (bertrand_lt_of_composite n k hk h).1
  have hgap : k ^ 2 ≤ (Nat.log 2 n) ^ 5 := h2 n k hk8 h
  have hsm := h1 n k hk8 hkn hle_lcm ⟨j, hj_dvd⟩ hgap h
  have hsplit := primeCounting_add_smooth_le n k hn
  omega

end OMA.R_Grimm_grimm_conjecture_weak_R1

