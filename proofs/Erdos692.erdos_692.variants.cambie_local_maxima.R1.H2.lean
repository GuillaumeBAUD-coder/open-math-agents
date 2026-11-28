import OMAReductions.R_Erdos692_erdos_692_variants_cambie_local_maxima_R1

-- Step Erdos692.erdos_692.variants.cambie_local_maxima.R1.H2: hypothesis H2 of reduction Erdos692.erdos_692.variants.cambie_local_maxima.R1
-- Credit: @luciusacarr
-- Moving the right end from 2q to 2q+1 adds only the divisor 2q, and every multiple of 2q
-- already has the divisor q in (n, 2q). So the new set sits inside the old one, and the old one
-- also contains the residue class 2q modulo 2q·(2q)!, which has positive density.
-- The two density lemmas are adapted from reductions/Erdos470...R1 (hasDensity_sdiff)
-- and proofs/Erdos786...selfridge (hasDensity_of_periodic).

namespace OMA.E692H2

open Filter Topology Erdos692

lemma hasDensity_sdiff {S T : Set ℕ} {α β : ℝ} (hST : T ⊆ S)
    (hS : S.HasDensity α) (hT : T.HasDensity β) : (S \ T).HasDensity (α - β) := by
  rw [Set.HasDensity] at hS hT ⊢
  have heq : ∀ b : ℕ, (S \ T).partialDensity Set.univ b =
      S.partialDensity Set.univ b - T.partialDensity Set.univ b := by
    intro b
    simp only [Set.partialDensity, Set.inter_univ]
    have hfinS : (S ∩ Set.Iio b).Finite := (Set.finite_Iio b).inter_of_right S
    have hfinT : (T ∩ Set.Iio b).Finite := (Set.finite_Iio b).inter_of_right T
    have hsub : T ∩ Set.Iio b ⊆ S ∩ Set.Iio b := Set.inter_subset_inter_left _ hST
    have hdiff : (S \ T) ∩ Set.Iio b = (S ∩ Set.Iio b) \ (T ∩ Set.Iio b) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_sdiff]
      tauto
    rw [hdiff, Set.ncard_sdiff hsub hfinT]
    have hle : (T ∩ Set.Iio b).ncard ≤ (S ∩ Set.Iio b).ncard := Set.ncard_le_ncard hsub hfinS
    rw [Nat.cast_sub hle, sub_div]
  simp_rw [heq]
  exact hS.sub hT

lemma hasDensity_of_periodic {A : Set ℕ} [DecidablePred (· ∈ A)] {M : ℕ} (hM : 0 < M)
    (hper : ∀ n : ℕ, n % M ∈ A ↔ n ∈ A) :
    A.HasDensity ((((Finset.range M).filter (· ∈ A)).card : ℝ) / (M : ℝ)) := by
  let c : ℕ := ((Finset.range M).filter (· ∈ A)).card
  have hmul : ∀ q : ℕ, ((Finset.range (q * M)).filter (· ∈ A)).card = q * c := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      have hsplit : (Finset.range ((q + 1) * M)).filter (· ∈ A) =
          (Finset.range (q * M)).filter (· ∈ A) ∪
            (Finset.Ico (q * M) ((q + 1) * M)).filter (· ∈ A) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
        constructor
        · rintro ⟨hn, hA⟩
          by_cases hlt : n < q * M
          · exact Or.inl ⟨hlt, hA⟩
          · exact Or.inr ⟨⟨Nat.le_of_not_lt hlt, hn⟩, hA⟩
        · rintro (⟨hlt, hA⟩ | ⟨⟨_, hlt⟩, hA⟩)
          · exact ⟨lt_of_lt_of_le hlt (by nlinarith), hA⟩
          · exact ⟨hlt, hA⟩
      have hdisj : Disjoint ((Finset.range (q * M)).filter (· ∈ A))
          ((Finset.Ico (q * M) ((q + 1) * M)).filter (· ∈ A)) :=
        Finset.disjoint_left.mpr fun n h1 h2 => by
          have h1' := Finset.mem_range.mp (Finset.mem_filter.mp h1).1
          have h2' := (Finset.mem_Ico.mp (Finset.mem_filter.mp h2).1).1
          omega
      have hblock : ((Finset.Ico (q * M) ((q + 1) * M)).filter (· ∈ A)).card = c := by
        refine Finset.card_bij (fun n _ => n - q * M) ?_ ?_ ?_
        · intro n hn
          rcases Finset.mem_filter.mp hn with ⟨hIco, hA⟩
          rcases Finset.mem_Ico.mp hIco with ⟨hle, hlt⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
            have : (q + 1) * M = q * M + M := by ring
            omega), ?_⟩
          have hmod : (n - q * M) % M = n % M := by
            have hadd : q * M + (n - q * M) = n := by omega
            rw [← Nat.mul_add_mod_self_right q M (n - q * M), hadd]
          exact (hper (n - q * M)).mp (hmod.symm ▸ (hper n).mpr hA)
        · intro n₁ hn₁ n₂ hn₂ heq
          have h1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn₁).1).1
          have h2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn₂).1).1
          omega
        · intro r hr
          rcases Finset.mem_filter.mp hr with ⟨hr_lt, hAr⟩
          rw [Finset.mem_range] at hr_lt
          have : (q + 1) * M = q * M + M := by ring
          refine ⟨q * M + r, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩,
            by omega⟩
          have hmod : (q * M + r) % M = r % M := by rw [Nat.mul_add_mod_self_right]
          exact (hper (q * M + r)).mp (hmod.symm ▸ (hper r).mpr hAr)
      rw [hsplit, Finset.card_union_of_disjoint hdisj, ih, hblock]
      ring
  have hcard : ∀ n : ℕ, (A ∩ Set.Iio n).ncard = ((Finset.range n).filter (· ∈ A)).card := by
    intro n
    have hset : A ∩ Set.Iio n = ↑((Finset.range n).filter (· ∈ A)) := by
      ext m
      simp [Set.mem_Iio, and_comm]
    rw [hset, Set.ncard_coe_finset]
  rw [Set.HasDensity]
  have hpd : ∀ n : ℕ, A.partialDensity Set.univ n =
      (((Finset.range n).filter (· ∈ A)).card : ℝ) / (n : ℝ) := by
    intro n
    rw [Set.partialDensity, Set.inter_univ, Set.univ_inter, hcard, Nat.ncard_Iio]
  simp only [hpd]
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hbdd : ∀ n : ℕ, 1 ≤ n →
      (c : ℝ) / (M : ℝ) - (c : ℝ) * (1 / (n : ℝ)) ≤
        (((Finset.range n).filter (· ∈ A)).card : ℝ) / (n : ℝ) ∧
      (((Finset.range n).filter (· ∈ A)).card : ℝ) / (n : ℝ) ≤
        (c : ℝ) / (M : ℝ) + (c : ℝ) * (1 / (n : ℝ)) := by
    intro n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    let q := n / M
    have hq_le : q * M ≤ n := Nat.div_mul_le_self n M
    have hq_lt : n < (q + 1) * M := by
      have h1 : q * M + n % M = n := by
        dsimp only [q]
        rw [mul_comm]
        exact Nat.div_add_mod n M
      have h2 := Nat.mod_lt n hM
      nlinarith
    have hlo_nat : q * c ≤ ((Finset.range n).filter (· ∈ A)).card := by
      rw [← hmul q]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hq_le))
    have hhi_nat : ((Finset.range n).filter (· ∈ A)).card ≤ (q + 1) * c := by
      rw [← hmul (q + 1)]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hq_lt.le))
    have hlo : (q : ℝ) * (c : ℝ) ≤ (((Finset.range n).filter (· ∈ A)).card : ℝ) := by
      exact_mod_cast hlo_nat
    have hhi : (((Finset.range n).filter (· ∈ A)).card : ℝ) ≤ ((q : ℝ) + 1) * (c : ℝ) := by
      exact_mod_cast hhi_nat
    have hqM_le : (q : ℝ) * (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hq_le
    have hqM_gt : (n : ℝ) < ((q : ℝ) + 1) * (M : ℝ) := by exact_mod_cast hq_lt
    have hc_nonneg : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
    constructor
    · rw [le_div_iff₀ hn_pos]
      have h1 : ((c : ℝ) / (M : ℝ) - (c : ℝ) * (1 / (n : ℝ))) * (n : ℝ) * (M : ℝ) =
          (c : ℝ) * ((n : ℝ) - (M : ℝ)) := by
        field_simp [hM_pos.ne', hn_pos.ne']
      have h2 : (c : ℝ) * ((n : ℝ) - (M : ℝ)) ≤ (q : ℝ) * (c : ℝ) * (M : ℝ) := by nlinarith
      nlinarith
    · rw [div_le_iff₀ hn_pos]
      have h1 : ((c : ℝ) / (M : ℝ) + (c : ℝ) * (1 / (n : ℝ))) * (n : ℝ) * (M : ℝ) =
          (c : ℝ) * ((n : ℝ) + (M : ℝ)) := by
        field_simp [hM_pos.ne', hn_pos.ne']
      have h2 : ((q : ℝ) + 1) * (c : ℝ) * (M : ℝ) ≤ (c : ℝ) * ((n : ℝ) + (M : ℝ)) := by
        nlinarith
      nlinarith
  have hlim : ∀ s : ℝ, Tendsto (fun n : ℕ => (c : ℝ) / (M : ℝ) + s * (1 / (n : ℝ)))
      atTop (𝓝 ((c : ℝ) / (M : ℝ))) := fun s => by
    simpa using Tendsto.const_add ((c : ℝ) / (M : ℝ))
      (Tendsto.const_mul s tendsto_one_div_atTop_nhds_zero_nat)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa [sub_eq_add_neg, neg_mul] using hlim (-(c : ℝ)))
    (hlim (c : ℝ))
    (eventually_atTop.mpr ⟨1, fun n hn => by simpa [sub_eq_add_neg, neg_mul] using (hbdd n hn).1⟩)
    (eventually_atTop.mpr ⟨1, fun n hn => (hbdd n hn).2⟩)

/-- A multiple of `2q` has the two divisors `q` and `2q` in `(n, 2q+1)`. -/
lemma not_mem_of_dvd {n q x : ℕ} (hnq : n < q) (hx : 2 * q ∣ x) :
    x ∉ exactlyOneDivisorIn n (2 * q + 1) := by
  intro hmem
  have hfin : {d ∈ Set.Ioo n (2 * q + 1) | d ∣ x}.Finite :=
    (Set.finite_Ioo n (2 * q + 1)).subset (fun d hd => hd.1)
  have hsub : ({q, 2 * q} : Set ℕ) ⊆ {d ∈ Set.Ioo n (2 * q + 1) | d ∣ x} := by
    intro d hd
    rcases hd with rfl | rfl
    · exact ⟨⟨hnq, by omega⟩, (Dvd.intro_left 2 rfl).trans hx⟩
    · exact ⟨⟨by omega, by omega⟩, hx⟩
  have h2 := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_pair (by omega)] at h2
  have h1 : {d ∈ Set.Ioo n (2 * q + 1) | d ∣ x}.ncard = 1 := hmem
  omega

lemma subset_old {n q : ℕ} (hnq : n < q) :
    exactlyOneDivisorIn n (2 * q + 1) ⊆ exactlyOneDivisorIn n (2 * q) := by
  intro x hx
  by_cases hdx : 2 * q ∣ x
  · exact absurd hx (not_mem_of_dvd hnq hdx)
  · have hset : {d ∈ Set.Ioo n (2 * q) | d ∣ x} = {d ∈ Set.Ioo n (2 * q + 1) | d ∣ x} := by
      ext d
      simp only [Set.mem_setOf_eq, Set.mem_Ioo]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, by omega⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, ?_⟩, h3⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h | h
        · exact h
        · exact absurd (h ▸ h3) hdx
    show {d ∈ Set.Ioo n (2 * q) | d ∣ x}.ncard = 1
    rw [hset]
    exact hx

lemma class_mem {n q x : ℕ} (hn : 2 ≤ n) (hnq : n < q) (hq : q.Prime)
    (hx : x % (2 * q * (2 * q).factorial) = 2 * q) :
    x ∈ exactlyOneDivisorIn n (2 * q) \ exactlyOneDivisorIn n (2 * q + 1) := by
  set F := (2 * q).factorial with hF
  set u := 1 + x / (2 * q * F) * F with hu
  have hxu : x = 2 * q * u := by
    have := Nat.div_add_mod x (2 * q * F)
    rw [hx] at this
    rw [hu]
    nlinarith
  have hdx : 2 * q ∣ x := ⟨u, hxu⟩
  refine ⟨?_, not_mem_of_dvd hnq hdx⟩
  have hset : {d ∈ Set.Ioo n (2 * q) | d ∣ x} = {q} := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_Ioo, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hdF : d ∣ F := Nat.dvd_factorial (by omega) h2.le
      have hcopF : Nat.Coprime F u := by
        rw [hu, Nat.coprime_add_mul_right_right]
        exact Nat.coprime_one_right F
      have hcop : Nat.Coprime d u := Nat.Coprime.coprime_dvd_left hdF hcopF
      have hd2q : d ∣ 2 * q := hcop.dvd_of_dvd_mul_right (hxu ▸ h3)
      by_cases hqd : q ∣ d
      · obtain ⟨e, rfl⟩ := hqd
        have he : e ∣ 2 := by
          have hq0 : 0 < q := hq.pos
          rw [mul_comm 2 q] at hd2q
          exact (Nat.mul_dvd_mul_iff_left hq0).1 hd2q
        have he2 : e ≤ 2 := Nat.le_of_dvd (by norm_num) he
        interval_cases e
        · omega
        · omega
        · omega
      · have hcq : Nat.Coprime q d := (Nat.Prime.coprime_iff_not_dvd hq).2 hqd
        have : d ∣ 2 := hcq.symm.dvd_of_dvd_mul_right hd2q
        have := Nat.le_of_dvd (by norm_num) this
        omega
    · rintro rfl
      exact ⟨⟨hnq, by have := hq.pos; omega⟩, (Dvd.intro_left 2 rfl).trans hdx⟩
  show {d ∈ Set.Ioo n (2 * q) | d ∣ x}.ncard = 1
  rw [hset, Set.ncard_singleton]

end OMA.E692H2

open Erdos692 in
theorem OMA.solution :
    OMA.R_Erdos692_erdos_692_variants_cambie_local_maxima_R1.H2 := by
  classical
  intro δ hδ n q hn hnq hq
  set M := 2 * q * (2 * q).factorial with hM
  have hF : 0 < (2 * q).factorial := Nat.factorial_pos _
  have hMpos : 0 < M := by have := hq.pos; positivity
  have h2qM : 2 * q < M := by
    have h2 : 2 ≤ (2 * q).factorial := by
      calc 2 = (2 : ℕ).factorial := rfl
        _ ≤ (2 * q).factorial := Nat.factorial_le (by have := hq.two_le; omega)
    have := hq.pos
    rw [hM]
    nlinarith
  set S : Set ℕ := {x | x % M = 2 * q} with hS
  have hSd := OMA.E692H2.hasDensity_of_periodic (A := S) hMpos (by
    intro x
    simp only [hS, Set.mem_setOf_eq, Nat.mod_mod])
  have hdiff := OMA.E692H2.hasDensity_sdiff (OMA.E692H2.subset_old hnq) (hδ n (2 * q))
    (hδ n (2 * q + 1))
  have hsub : S ⊆ exactlyOneDivisorIn n (2 * q) \ exactlyOneDivisorIn n (2 * q + 1) :=
    fun x hx => OMA.E692H2.class_mem hn hnq hq hx
  have hle := Set.HasDensity.mono hsub hSd hdiff
  have hc : 1 ≤ ((Finset.range M).filter (· ∈ S)).card := by
    apply Finset.card_pos.2
    refine ⟨2 * q, Finset.mem_filter.2 ⟨Finset.mem_range.2 h2qM, ?_⟩⟩
    show 2 * q % M = 2 * q
    exact Nat.mod_eq_of_lt h2qM
  have hpos : (0 : ℝ) < (((Finset.range M).filter (· ∈ S)).card : ℝ) / (M : ℝ) := by
    apply div_pos
    · exact_mod_cast hc
    · exact_mod_cast hMpos
  linarith
