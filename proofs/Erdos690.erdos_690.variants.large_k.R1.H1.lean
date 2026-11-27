import OMAReductions.R_Erdos690_erdos_690_variants_large_k_R1

/-!
# Exact CRT density formula for `kthPrimeFactorSet (k + 1) p`

For any prime `p`, let `P = Nat.primesBelow p`. A positive integer `n` has `p` as its
`(k + 1)`-st smallest prime factor if and only if `p ∣ n` and the set `T` of primes in `P`
dividing `n` has cardinality `k`. Each choice of `T ∈ P.powersetCard k` defines a periodic set
whose density is `(1 / p) * (∏ q ∈ T, 1 / q) * (∏ q ∈ P \ T, (1 - 1 / q))` by the Chinese
Remainder Theorem, which rewrites as `B p * (∏ q ∈ T, 1 / (q - 1)) / p`. Summing over the
pairwise disjoint cells `T ∈ P.powersetCard k` and removing `{0}` yields `B p * E p k / p`.
-/

namespace OMA.E690H1

open Filter Set Topology
open scoped Classical

noncomputable def cnt (S : Set ℕ) (b : ℕ) : ℕ := ((Finset.range b).filter (· ∈ S)).card

lemma pd_eq (S : Set ℕ) (b : ℕ) : S.partialDensity Set.univ b = (cnt S b : ℝ) / b := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
  have h1 : S ∩ Iio b = ↑((Finset.range b).filter (· ∈ S)) := by
    ext n; simp [and_comm]
  rw [h1, Set.ncard_coe_finset, Nat.ncard_Iio]
  simp [cnt]

lemma hasDensity_iff (S : Set ℕ) (d : ℝ) :
    S.HasDensity d ↔ Tendsto (fun b => (cnt S b : ℝ) / b) atTop (𝓝 d) := by
  simp only [Set.HasDensity, pd_eq]

lemma cnt_succ (S : Set ℕ) (n : ℕ) :
    cnt S (n + 1) = cnt S n + (if n ∈ S then 1 else 0) := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma cnt_le (S : Set ℕ) (n : ℕ) : cnt S n ≤ n := by
  unfold cnt
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma cnt_split (S X : Set ℕ) (n : ℕ) : cnt S n = cnt (S ∩ X) n + cnt (S \ X) n := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_union, Set.mem_inter_iff,
      Set.mem_sdiff]; tauto
  · rw [Finset.disjoint_left]; intro x h1 h2
    simp only [Finset.mem_filter, Set.mem_inter_iff, Set.mem_sdiff] at h1 h2; tauto

def Per (Y : Set ℕ) (N : ℕ) : Prop := ∀ n, n ∈ Y ↔ n + N ∈ Y

lemma Per.mem_add_mul {Y : Set ℕ} {N : ℕ} (h : Per Y N) (n k : ℕ) :
    n ∈ Y ↔ n + N * k ∈ Y := by
  induction k with
  | zero => simp
  | succ k ih => rw [ih, h (n + N * k)]; ring_nf

lemma Per.mem_mod {Y : Set ℕ} {N : ℕ} (h : Per Y N) (n : ℕ) : n ∈ Y ↔ n % N ∈ Y := by
  rw [h.mem_add_mul (n % N) (n / N), Nat.mod_add_div]

lemma Per.cnt_add {Y : Set ℕ} {N : ℕ} (h : Per Y N) (n : ℕ) :
    cnt Y (n + N) = cnt Y n + cnt Y N := by
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    rw [show n + 1 + N = (n + N) + 1 by ring, cnt_succ, ih, cnt_succ]
    have := h n
    by_cases hn : n ∈ Y
    · rw [if_pos hn, if_pos (this.1 hn)]; omega
    · rw [if_neg hn, if_neg (fun h' => hn (this.2 h'))]; omega

lemma Per.cnt_approx {Y : Set ℕ} {N : ℕ} (h : Per Y N) (hN : 0 < N) (n : ℕ) :
    |(cnt Y n : ℝ) - n * (cnt Y N) / N| ≤ N := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < N
    · have h1 : (cnt Y n : ℝ) ≤ n := by exact_mod_cast cnt_le Y n
      have h2 : (cnt Y N : ℝ) ≤ N := by exact_mod_cast cnt_le Y N
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have h3 : (n : ℝ) * cnt Y N / N ≤ n := by
        rw [div_le_iff₀ hN']; exact mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 : (0 : ℝ) ≤ n * cnt Y N / N := by positivity
      have h5 : (n : ℝ) ≤ N := by exact_mod_cast hn.le
      rw [abs_le]; constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (cnt Y n)]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + N := ⟨n - N, by omega⟩
      have := ih m (by omega)
      rw [h.cnt_add]
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have e : ((cnt Y m + cnt Y N : ℕ) : ℝ) - ((m + N : ℕ) : ℝ) * cnt Y N / N
          = (cnt Y m : ℝ) - m * cnt Y N / N := by
        push_cast; field_simp; ring
      rw [e]; exact this

lemma Per.hasDensity {Y : Set ℕ} {N : ℕ} (h : Per Y N) (hN : 0 < N) :
    Y.HasDensity ((cnt Y N : ℝ) / N) := by
  rw [hasDensity_iff, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n0, hn0⟩ := exists_nat_gt ((N : ℝ) / ε)
  refine ⟨n0 + 1, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn' : (N : ℝ) / ε < n := lt_of_lt_of_le hn0 (by exact_mod_cast (show n0 ≤ n by omega))
  rw [Real.dist_eq]
  have e : (cnt Y n : ℝ) / n - cnt Y N / N = ((cnt Y n : ℝ) - n * cnt Y N / N) / n := by
    field_simp
  rw [e, abs_div, abs_of_pos hnpos, div_lt_iff₀ hnpos]
  refine lt_of_le_of_lt (h.cnt_approx hN n) ?_
  rwa [div_lt_iff₀ hε, mul_comm] at hn'

lemma HasDensity.unique {S : Set ℕ} {a b : ℝ} (ha : S.HasDensity a) (hb : S.HasDensity b) :
    a = b := tendsto_nhds_unique ha hb

lemma HasDensity.diff {S X : Set ℕ} {a b : ℝ} (ha : S.HasDensity a)
    (hb : (S ∩ X).HasDensity b) : (S \ X).HasDensity (a - b) := by
  rw [hasDensity_iff] at *
  refine (ha.sub hb).congr (fun n => ?_)
  rw [cnt_split S X n]; push_cast; ring

lemma Per.cnt_dvd {Y : Set ℕ} {N p : ℕ} (h : Per Y N) (hN : 0 < N) (hp : 0 < p)
    (hc : Nat.Coprime p N) : cnt (Y ∩ {n | p ∣ n}) (p * N) = cnt Y N := by
  unfold cnt
  have e1 : (Finset.range (p * N)).filter (· ∈ Y ∩ {n | p ∣ n}) =
      ((Finset.range N).filter (fun k => p * k ∈ Y)).image (p * ·) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_inter_iff, Set.mem_setOf_eq,
      Finset.mem_image]
    constructor
    · rintro ⟨h1, h2, k, rfl⟩
      exact ⟨k, ⟨by nlinarith, h2⟩, rfl⟩
    · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
      exact ⟨by nlinarith, h2, dvd_mul_right _ _⟩
  refine Eq.trans (b := (((Finset.range N).filter (fun k => p * k ∈ Y)).image (p * ·)).card)
    (by convert congrArg Finset.card e1) ?_
  rw [Finset.card_image_of_injective _ (fun a b hab => by
    simpa [hp.ne'] using hab)]
  have hinj : ∀ a ∈ Finset.range N, ∀ b ∈ Finset.range N, p * a % N = p * b % N → a = b := by
    intro a ha b hb hab
    simp only [Finset.mem_range] at ha hb
    have h1 : p * a ≡ p * b [MOD N] := hab
    have h2 := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hc) h1
    unfold Nat.ModEq at h2
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
  have himg : (Finset.range N).image (fun k => p * k % N) = Finset.range N := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx; simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨k, -, rfl⟩ := hx; exact Nat.mod_lt _ hN
    · rw [Finset.card_image_of_injOn (fun a ha b hb hab => hinj a ha b hb hab)]
  apply Finset.card_nbij (fun k => p * k % N)
  · intro k hk
    have hk' := Finset.mem_filter.1 hk
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ hN), (h.mem_mod _).1 hk'.2⟩
  · intro a ha b hb hab
    have ha' := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
    have hb' := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
    exact hinj a ha'.1 b hb'.1 hab
  · intro m hm
    have hm' := Finset.mem_filter.1 (Finset.mem_coe.1 hm)
    have : m ∈ (Finset.range N).image (fun k => p * k % N) := by
      rw [himg]; exact hm'.1
    obtain ⟨k, hk, hkm⟩ := Finset.mem_image.1 this
    refine ⟨k, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hk, ?_⟩), hkm⟩
    rw [h.mem_mod, hkm]; exact hm'.2

lemma Per.inter_dvd {Y : Set ℕ} {N p : ℕ} (h : Per Y N) :
    Per (Y ∩ {n | p ∣ n}) (p * N) := by
  intro n
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [h.mem_add_mul n p, mul_comm N p, Nat.dvd_add_left (dvd_mul_right p N)]

lemma Per.sdiff_dvd {Y : Set ℕ} {N q : ℕ} (h : Per Y N) :
    Per (Y \ {n | q ∣ n}) (q * N) := by
  intro n
  simp only [Set.mem_diff, Set.mem_setOf_eq]
  rw [h.mem_add_mul n q, mul_comm N q, Nat.dvd_add_left (dvd_mul_right q N)]

lemma Per.hasDensity_dvd {Y : Set ℕ} {N p : ℕ} (h : Per Y N) (hN : 0 < N) (hp : 0 < p)
    (hc : Nat.Coprime p N) {d : ℝ} (hd : Y.HasDensity d) :
    (Y ∩ {n | p ∣ n}).HasDensity (d / p) := by
  have e := HasDensity.unique hd (h.hasDensity hN)
  have := (h.inter_dvd (p := p)).hasDensity (Nat.mul_pos hp hN)
  rw [h.cnt_dvd hN hp hc] at this
  convert this using 1
  rw [e]; push_cast; field_simp

lemma Per.hasDensity_not_dvd {Y : Set ℕ} {N q : ℕ} (h : Per Y N) (hN : 0 < N) (hq : 0 < q)
    (hc : Nat.Coprime q N) {d : ℝ} (hd : Y.HasDensity d) :
    (Y \ {n | q ∣ n}).HasDensity (d * (1 - 1 / (q : ℝ))) := by
  have hdiff := HasDensity.diff hd (h.hasDensity_dvd hN hq hc hd)
  convert hdiff using 1
  ring

lemma HasDensity.union_disjoint {S T : Set ℕ} {a b : ℝ} (hd : Disjoint S T)
    (ha : S.HasDensity a) (hb : T.HasDensity b) : (S ∪ T).HasDensity (a + b) := by
  rw [hasDensity_iff] at *
  refine (ha.add hb).congr (fun n => ?_)
  have hcnt : cnt (S ∪ T) n = cnt S n + cnt T n := by
    unfold cnt
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext x
      simp only [Finset.mem_filter, Finset.mem_union, Set.mem_union]
      tauto
    · rw [Finset.disjoint_left]; intro x h1 h2
      exact Set.disjoint_left.mp hd (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
  rw [hcnt]; push_cast; ring

lemma HasDensity.biUnion_disjoint {ι : Type*} (s : Finset ι) (f : ι → Set ℕ) (d : ι → ℝ)
    (hdisj : (s : Set ι).PairwiseDisjoint f)
    (hd : ∀ i ∈ s, (f i).HasDensity (d i)) :
    (⋃ i ∈ s, f i).HasDensity (∑ i ∈ s, d i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Finset.sum_empty]
    exact Set.HasDensity.empty
  | @insert a s ha ih =>
    have hunion : (⋃ i ∈ insert a s, f i) = f a ∪ ⋃ i ∈ s, f i := by
      ext x; simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union, exists_prop]
      constructor
      · rintro ⟨i, rfl | hi, hxi⟩
        · exact Or.inl hxi
        · exact Or.inr ⟨i, hi, hxi⟩
      · rintro (hxa | ⟨i, hi, hxi⟩)
        · exact ⟨a, Or.inl rfl, hxa⟩
        · exact ⟨i, Or.inr hi, hxi⟩
    rw [hunion, Finset.sum_insert ha]
    have hdisj' : Disjoint (f a) (⋃ i ∈ s, f i) := by
      rw [Set.disjoint_left]
      intro x hxa hx
      simp only [Set.mem_iUnion, exists_prop] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      exact Set.disjoint_left.mp
        (hdisj (Finset.mem_coe.mpr (Finset.mem_insert_self a s))
          (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hi)) (fun h => ha (h ▸ hi)))
        hxa hxi
    have hpair : (s : Set ι).PairwiseDisjoint f :=
      hdisj.subset (Finset.coe_subset.mpr (Finset.subset_insert a s))
    exact HasDensity.union_disjoint hdisj'
      (hd a (Finset.mem_insert_self a s))
      (ih hpair (fun i hi => hd i (Finset.mem_insert_of_mem hi)))

lemma HasDensity.sdiff_zero {S : Set ℕ} {d : ℝ} (hS : S.HasDensity d) :
    (S \ {0}).HasDensity d := by
  have h0 : (S ∩ {0}).HasDensity 0 :=
    Nat.hasDensity_zero_of_finite ((Set.finite_singleton 0).subset Set.inter_subset_right)
  simpa using HasDensity.diff hS h0

def cell (P T : Finset ℕ) (p : ℕ) : Set ℕ :=
  {n | p ∣ n ∧ (∀ q ∈ T, q ∣ n) ∧ (∀ q ∈ P \ T, ¬ q ∣ n)}

lemma cell_per_and_density {p : ℕ} (hp : p.Prime) (P : Finset ℕ) :
    (∀ q ∈ P, q.Prime) → p ∉ P →
    ∀ T : Finset ℕ, T ⊆ P →
      Per (cell P T p) (p * ∏ q ∈ P, q) ∧
      (cell P T p).HasDensity
        ((1 / (p : ℝ)) * (∏ q ∈ T, (1 / (q : ℝ))) * (∏ q ∈ P \ T, (1 - 1 / (q : ℝ)))) := by
  induction P using Finset.induction_on with
  | empty =>
    intro _ _ T hT
    have hTe : T = ∅ := Finset.subset_empty.mp hT
    subst hTe
    have hcell : cell ∅ ∅ p = Set.univ ∩ {n | p ∣ n} := by
      ext n; simp [cell]
    have hper1 : Per (Set.univ : Set ℕ) 1 := fun _ => Iff.rfl
    rw [hcell, Finset.prod_empty, Finset.sdiff_empty, Finset.prod_empty]
    refine ⟨hper1.inter_dvd, ?_⟩
    simpa using hper1.hasDensity_dvd Nat.one_pos hp.pos (Nat.coprime_one_right p)
      Set.HasDensity.univ_nat_hasDensity_one
  | @insert a S ha ih =>
    intro hP hpP T hT
    have haP : a.Prime := hP a (Finset.mem_insert_self a S)
    have hS : ∀ q ∈ S, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hpS : p ∉ S := fun h => hpP (Finset.mem_insert_of_mem h)
    have hap : a ≠ p := fun h => hpP (h ▸ Finset.mem_insert_self a S)
    have hNpos : 0 < p * ∏ q ∈ S, q :=
      Nat.mul_pos hp.pos (Finset.prod_pos fun q hq => (hS q hq).pos)
    have hcop : Nat.Coprime a (p * ∏ q ∈ S, q) := by
      refine Nat.Coprime.mul_right ((Nat.coprime_primes haP hp).mpr hap) ?_
      refine Nat.Coprime.prod_right fun q hq => ?_
      exact (Nat.coprime_primes haP (hS q hq)).mpr (fun h => ha (h ▸ hq))
    have hprod_eq : a * (p * ∏ q ∈ S, q) = p * ∏ q ∈ insert a S, q := by
      rw [Finset.prod_insert ha]; ring
    by_cases haT : a ∈ T
    · let T' := T.erase a
      have hT'S : T' ⊆ S := by
        intro q hq
        have hq' := Finset.mem_erase.mp hq
        exact (Finset.mem_insert.mp (hT hq'.2)).resolve_left hq'.1
      have hsdiff : (insert a S) \ T = S \ T' := by
        ext q
        simp only [T', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨rfl | hqS, hqT⟩
          · exact (hqT haT).elim
          · exact ⟨hqS, fun h => hqT h.2⟩
        · rintro ⟨hqS, hqT'⟩
          refine ⟨Or.inr hqS, fun hqT => ?_⟩
          by_cases hqa : q = a
          · exact ha (hqa ▸ hqS)
          · exact hqT' ⟨hqa, hqT⟩
      have hcell : cell (insert a S) T p = cell S T' p ∩ {n | a ∣ n} := by
        ext n
        simp only [cell, Set.mem_inter_iff, Set.mem_setOf_eq, hsdiff]
        constructor
        · rintro ⟨hpn, h1, h2⟩
          exact ⟨⟨hpn, fun q hq => h1 q (Finset.mem_erase.mp hq).2, h2⟩, h1 a haT⟩
        · rintro ⟨⟨hpn, h1, h2⟩, han⟩
          refine ⟨hpn, fun q hq => ?_, h2⟩
          by_cases hqa : q = a
          · exact hqa ▸ han
          · exact h1 q (Finset.mem_erase.mpr ⟨hqa, hq⟩)
      obtain ⟨hper, hdens⟩ := ih hS hpS T' hT'S
      rw [hcell, ← hprod_eq]
      refine ⟨hper.inter_dvd, ?_⟩
      have hd := hper.hasDensity_dvd hNpos haP.pos hcop hdens
      convert hd using 1
      rw [hsdiff, ← Finset.insert_erase haT, Finset.prod_insert (Finset.notMem_erase a T)]
      ring
    · have hTS : T ⊆ S := by
        intro q hq
        exact (Finset.mem_insert.mp (hT hq)).resolve_left (fun h => haT (h ▸ hq))
      have hsdiff : (insert a S) \ T = insert a (S \ T) := by
        ext q
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hqS, hqT⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hqS, hqT⟩
        · rintro (rfl | ⟨hqS, hqT⟩)
          · exact ⟨Or.inl rfl, haT⟩
          · exact ⟨Or.inr hqS, hqT⟩
      have haST : a ∉ S \ T := fun h => ha (Finset.mem_sdiff.mp h).1
      have hcell : cell (insert a S) T p = cell S T p \ {n | a ∣ n} := by
        ext n
        simp only [cell, Set.mem_diff, Set.mem_setOf_eq, hsdiff]
        constructor
        · rintro ⟨hpn, h1, h2⟩
          exact ⟨⟨hpn, h1, fun q hq => h2 q (Finset.mem_insert_of_mem hq)⟩,
            h2 a (Finset.mem_insert_self a _)⟩
        · rintro ⟨⟨hpn, h1, h2⟩, hna⟩
          refine ⟨hpn, h1, fun q hq => ?_⟩
          rcases Finset.mem_insert.mp hq with rfl | hq'
          · exact hna
          · exact h2 q hq'
      obtain ⟨hper, hdens⟩ := ih hS hpS T hTS
      rw [hcell, ← hprod_eq]
      refine ⟨hper.sdiff_dvd, ?_⟩
      have hd := hper.hasDensity_not_dvd hNpos haP.pos hcop hdens
      convert hd using 1
      rw [hsdiff, Finset.prod_insert haST]
      ring

lemma term_eq {P T : Finset ℕ} (hP : ∀ q ∈ P, q.Prime) (hTP : T ⊆ P) (p : ℕ) :
    (1 / (p : ℝ)) * (∏ q ∈ T, (1 / (q : ℝ))) * (∏ q ∈ P \ T, (1 - 1 / (q : ℝ))) =
      (∏ x ∈ P, (1 - 1 / (x : ℝ))) * (∏ x ∈ T, (1 / ((x : ℝ) - 1))) / (p : ℝ) := by
  have hpoint : ∀ x ∈ T, (1 - 1 / (x : ℝ)) * (1 / ((x : ℝ) - 1)) = 1 / (x : ℝ) := by
    intro x hx
    have hx2 : 2 ≤ x := (hP x (hTP hx)).two_le
    have hx0 : (x : ℝ) ≠ 0 := by exact_mod_cast (by omega : x ≠ 0)
    have hx1 : (x : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ x := by exact_mod_cast hx2
      linarith
    calc (1 - 1 / (x : ℝ)) * (1 / ((x : ℝ) - 1))
        = (((x : ℝ) - 1) / (x : ℝ)) * (1 / ((x : ℝ) - 1)) := by
            rw [sub_div, div_self hx0]
      _ = 1 / (x : ℝ) := by
            rw [mul_one_div, div_div, mul_comm (x : ℝ), ← div_div, div_self hx1]
  have hsplit : (∏ x ∈ P, (1 - 1 / (x : ℝ))) * (∏ x ∈ T, (1 / ((x : ℝ) - 1))) =
      (∏ x ∈ P \ T, (1 - 1 / (x : ℝ))) * (∏ x ∈ T, (1 / (x : ℝ))) := by
    rw [← Finset.prod_sdiff hTP, mul_assoc, ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl hpoint]
  rw [hsplit]
  ring

lemma kthPrimeFactorSet_eq (k p : ℕ) (hp : p.Prime) :
    Erdos690.kthPrimeFactorSet (k + 1) p =
      (⋃ T ∈ (Nat.primesBelow p).powersetCard k, cell (Nat.primesBelow p) T p) \ {0} := by
  ext n
  simp only [Erdos690.kthPrimeFactorSet, Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff,
    Set.mem_iUnion, Finset.mem_powersetCard, cell, exists_prop]
  constructor
  · rintro ⟨hnpos, hp_mem, hcard⟩
    have hn0 : n ≠ 0 := hnpos.ne'
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp_mem
    refine ⟨⟨n.primeFactors.filter (· < p), ⟨?_, by simpa using hcard⟩, hpn, ?_, ?_⟩, hn0⟩
    · intro q hq
      obtain ⟨hqm, hql⟩ := Finset.mem_filter.mp hq
      exact Nat.mem_primesBelow.mpr ⟨hql, Nat.prime_of_mem_primeFactors hqm⟩
    · intro q hq
      exact Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hq).1
    · intro q hq hqn
      obtain ⟨hqP, hqnot⟩ := Finset.mem_sdiff.mp hq
      obtain ⟨hql, hqprime⟩ := Nat.mem_primesBelow.mp hqP
      exact hqnot (Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hqprime, hqn, hn0⟩, hql⟩)
  · rintro ⟨⟨T, ⟨hTP, hTcard⟩, hpn, hTdvd, hTndvd⟩, hn0⟩
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hfilt : n.primeFactors.filter (· < p) = T := by
      ext q
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hqm, hql⟩
        have hqP : q ∈ Nat.primesBelow p :=
          Nat.mem_primesBelow.mpr ⟨hql, Nat.prime_of_mem_primeFactors hqm⟩
        by_contra hqT
        exact hTndvd q (Finset.mem_sdiff.mpr ⟨hqP, hqT⟩) (Nat.dvd_of_mem_primeFactors hqm)
      · intro hqT
        obtain ⟨hql, hqprime⟩ := Nat.mem_primesBelow.mp (hTP hqT)
        exact ⟨Nat.mem_primeFactors.mpr ⟨hqprime, hTdvd q hqT, hn0⟩, hql⟩
    refine ⟨hnpos, Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩, ?_⟩
    rw [hfilt, hTcard]
    simp

end OMA.E690H1

theorem OMA.solution : OMA.R_Erdos690_erdos_690_variants_large_k_R1.H1 := by
  intro k p hp
  dsimp only
  let P := Nat.primesBelow p
  have hP : ∀ q ∈ P, q.Prime := fun q hq => (Nat.mem_primesBelow.mp hq).2
  have hpP : p ∉ P := fun h => lt_irrefl p (Nat.mem_primesBelow.mp h).1
  have hdisj : ((P.powersetCard k : Finset (Finset ℕ)) : Set (Finset ℕ)).PairwiseDisjoint
      (fun T => OMA.E690H1.cell P T p) := by
    intro T₁ hT₁ T₂ hT₂ hne
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hT₁ hT₂
    rw [Set.disjoint_left]
    intro n hn₁ hn₂
    have hns : ¬ T₁ ⊆ T₂ := fun hsub =>
      hne (Finset.eq_of_subset_of_card_le hsub (by rw [hT₁.2, hT₂.2]))
    obtain ⟨q, hq₁, hq₂⟩ := Finset.not_subset.mp hns
    exact hn₂.2.2 q (Finset.mem_sdiff.mpr ⟨hT₁.1 hq₁, hq₂⟩) (hn₁.2.1 q hq₁)
  have hcell_d : ∀ T ∈ P.powersetCard k,
      (OMA.E690H1.cell P T p).HasDensity
        ((∏ x ∈ P, (1 - 1 / (x : ℝ))) * (∏ x ∈ T, (1 / ((x : ℝ) - 1))) / (p : ℝ)) := by
    intro T hT
    have hTP : T ⊆ P := (Finset.mem_powersetCard.mp hT).1
    have hd := (OMA.E690H1.cell_per_and_density hp P hP hpP T hTP).2
    rwa [OMA.E690H1.term_eq hP hTP p] at hd
  have hunion := OMA.E690H1.HasDensity.biUnion_disjoint (P.powersetCard k)
    (fun T => OMA.E690H1.cell P T p)
    (fun T => (∏ x ∈ P, (1 - 1 / (x : ℝ))) * (∏ x ∈ T, (1 / ((x : ℝ) - 1))) / (p : ℝ))
    hdisj hcell_d
  have hsdiff := OMA.E690H1.HasDensity.sdiff_zero hunion
  rw [← OMA.E690H1.kthPrimeFactorSet_eq k p hp] at hsdiff
  convert hsdiff using 1
  rw [Finset.mul_sum, Finset.sum_div]
