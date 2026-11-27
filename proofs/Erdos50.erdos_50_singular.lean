import FormalConjectures.ErdosProblems.«50»

-- Problem: Erdős Problem 50 — erdos 50 singular
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/50.lean:69 (declaration Erdos50.erdos_50_singular)
-- Credit: @tamoghnokandar (the owner of the agent is credited as the solver)
-- The counting lemmas, the finite model, the anti-concentration bound `anti` and the tail bound
-- `cnt_bad` are reused from proofs/Erdos50.erdos_50_schoenberg.lean (credit: @Genbox).
--
-- Three parts.
-- 1. Continuity (`OMA50.cont`): the finite model puts little mass in narrow multiplicative
--    windows (`anti`), so the distribution function has no jumps.
-- 2. Covering (`OMA50.covering`): for every eps, finitely many half-open intervals of total
--    length at most eps contain phi(n)/n for all but eps*N of the n < N. Scales l_j = 2^(k_j),
--    m_j = l_j^10, l_(j+1) = 4^(m_j); scale j succeeds at n when n has no prime factor in
--    (l_j, m_j] and the product of its prime factors in (m_(j-1), l_j] is at most l_j^8. Each
--    scale succeeds with density at least (1/50)^4/2, scales are independent by the Chinese
--    remainder theorem, and a successful scale pins phi(n)/n to one of few short intervals.
-- 3. Analysis (`OMA50s.analysis`): the covering makes the Stieltjes measure of the distribution
--    function singular to Lebesgue measure, hence its derivative vanishes almost everywhere.

open Filter Set Topology

namespace OMA50

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

lemma cnt_mono {S T : Set ℕ} (h : S ⊆ T) (n : ℕ) : cnt S n ≤ cnt T n := by
  unfold cnt
  exact Finset.card_le_card (fun x hx => by
    simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, h hx.2⟩)

lemma cnt_union_le (S T : Set ℕ) (n : ℕ) : cnt (S ∪ T) n ≤ cnt S n + cnt T n := by
  unfold cnt
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_union, Set.mem_union] at hx ⊢
  tauto

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

/-- Key CRT counting: multiples of a coprime `p` in a periodic set. -/
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
  -- bijection k ↦ p*k % N
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

lemma Per.hasDensity_dvd {Y : Set ℕ} {N p : ℕ} (h : Per Y N) (hN : 0 < N) (hp : 0 < p)
    (hc : Nat.Coprime p N) {d : ℝ} (hd : Y.HasDensity d) :
    (Y ∩ {n | p ∣ n}).HasDensity (d / p) := by
  have e := HasDensity.unique hd (h.hasDensity hN)
  have := (h.inter_dvd (p := p)).hasDensity (Nat.mul_pos hp hN)
  rw [h.cnt_dvd hN hp hc] at this
  convert this using 1
  rw [e]; push_cast; field_simp

/-- Cauchy criterion for densities. -/
lemma exists_hasDensity (S : Set ℕ)
    (h : ∀ ε > 0, ∃ d : ℝ, ∀ᶠ n in atTop, |(cnt S n : ℝ) / n - d| ≤ ε) :
    ∃ L, S.HasDensity L := by
  have hc : CauchySeq (fun n => (cnt S n : ℝ) / n) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨d, hd⟩ := h (ε / 3) (by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hd
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm
    have h2 := hN n hn
    rw [Real.dist_eq]
    calc |(cnt S m : ℝ) / m - cnt S n / n|
        = |((cnt S m : ℝ) / m - d) - ((cnt S n : ℝ) / n - d)| := by ring_nf
      _ ≤ |(cnt S m : ℝ) / m - d| + |(cnt S n : ℝ) / n - d| := abs_sub _ _
      _ < ε := by linarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨L, (hasDensity_iff S L).2 hL⟩


/-! ## The finite model -/

def status (Q : Finset ℕ) (n : ℕ) : Finset ℕ := Q.filter (· ∣ n)

noncomputable def g (D : Finset ℕ) : ℝ := ∏ p ∈ D, (1 - 1 / (p : ℝ))

noncomputable def w (Q D : Finset ℕ) : ℝ :=
  (∏ p ∈ D, 1 / (p : ℝ)) * ∏ p ∈ Q \ D, (1 - 1 / (p : ℝ))

lemma one_sub_nonneg' (p : ℕ) : 0 ≤ 1 - 1 / (p : ℝ) := by
  rcases Nat.eq_zero_or_pos p with h | h
  · simp [h]
  · have : (1 : ℝ) / p ≤ 1 := by
      rw [div_le_one (by exact_mod_cast h)]; exact_mod_cast h
    linarith

lemma g_nonneg (D : Finset ℕ) : 0 ≤ g D := Finset.prod_nonneg fun p _ => one_sub_nonneg' p

lemma g_insert {p : ℕ} {E : Finset ℕ} (h : p ∉ E) : g (insert p E) = (1 - 1 / (p : ℝ)) * g E := by
  unfold g; rw [Finset.prod_insert h]

lemma status_per (Q : Finset ℕ) (R : Finset ℕ → Prop) :
    Per {n | R (status Q n)} (∏ p ∈ Q, p) := by
  intro n
  simp only [Set.mem_setOf_eq]
  have : status Q (n + ∏ p ∈ Q, p) = status Q n := by
    unfold status
    refine Finset.filter_congr fun p hp => ?_
    exact Nat.dvd_add_left (Finset.dvd_prod_of_mem _ hp)
  rw [this]

lemma prod_pos_of_primes (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) : 0 < ∏ p ∈ Q, p :=
  Finset.prod_pos fun p hp => (hQ p hp).pos

lemma status_insert {p : ℕ} {Q : Finset ℕ} (n : ℕ) :
    status (insert p Q) n = if p ∣ n then insert p (status Q n) else status Q n := by
  unfold status; rw [Finset.filter_insert]

lemma density_status (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    ∀ D ⊆ Q, {n | status Q n = D}.HasDensity (w Q D) := by
  induction Q using Finset.induction_on with
  | empty =>
    intro D hD
    rw [Finset.subset_empty] at hD
    subst hD
    have : {n | status ∅ n = (∅ : Finset ℕ)} = Set.univ := by
      ext n; simp [status]
    rw [this]
    simp [w]
  | insert p Q hpQ ih =>
    intro D hD
    have hp : p.Prime := hQ p (Finset.mem_insert_self p Q)
    have hQ' : ∀ q ∈ Q, q.Prime := fun q hq => hQ q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ Q, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      exact (Nat.coprime_primes hp (hQ' q hq)).2 (fun h => hpQ (h ▸ hq))
    have hN := prod_pos_of_primes Q hQ'
    have hpS : ∀ n, p ∉ status Q n := fun n h => hpQ (Finset.mem_filter.1 h).1
    by_cases hpD : p ∈ D
    · have hE : D.erase p ⊆ Q := by
        intro x hx
        have := Finset.mem_erase.1 hx
        rcases Finset.mem_insert.1 (hD this.2) with h | h
        · exact absurd h this.1
        · exact h
      have hset : {n | status (insert p Q) n = D} =
          {n | status Q n = D.erase p} ∩ {n | p ∣ n} := by
        ext n
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, status_insert]
        by_cases hn : p ∣ n
        · rw [if_pos hn]
          constructor
          · intro h; refine ⟨?_, hn⟩; rw [← h, Finset.erase_insert (hpS n)]
          · intro h; rw [h.1, Finset.insert_erase hpD]
        · rw [if_neg hn]
          constructor
          · intro h; exact absurd (h ▸ hpD) (hpS n)
          · intro h; exact absurd h.2 hn
      rw [hset]
      have := (status_per Q (· = D.erase p)).hasDensity_dvd hN hp.pos hcop (ih hQ' _ hE)
      convert this using 1
      unfold w
      rw [← Finset.mul_prod_erase D _ hpD]
      have : insert p Q \ D = Q \ D.erase p := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact absurd (h1 ▸ hpD) h2
          · exact ⟨h1, fun h => h2 h.2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨Or.inr h1, fun h => h2 ⟨?_, h⟩⟩
          rintro rfl; exact hpQ h1
      rw [this]; ring
    · have hD' : D ⊆ Q := by
        intro x hx
        rcases Finset.mem_insert.1 (hD hx) with h | h
        · exact absurd (h ▸ hx) hpD
        · exact h
      have hset : {n | status (insert p Q) n = D} =
          {n | status Q n = D} \ {n | p ∣ n} := by
        ext n
        simp only [Set.mem_setOf_eq, Set.mem_sdiff, status_insert]
        by_cases hn : p ∣ n
        · rw [if_pos hn]
          constructor
          · intro h; exact absurd (h ▸ Finset.mem_insert_self p _) hpD
          · intro h; exact absurd hn h.2
        · rw [if_neg hn]; tauto
      rw [hset]
      have h1 := ih hQ' D hD'
      have h2 := (status_per Q (· = D)).hasDensity_dvd hN hp.pos hcop h1
      have := HasDensity.diff h1 h2
      convert this using 1
      unfold w
      have : insert p Q \ D = insert p (Q \ D) := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact Or.inl h1
          · exact Or.inr ⟨h1, h2⟩
        · rintro (h1 | ⟨h1, h2⟩)
          · exact ⟨Or.inl h1, h1 ▸ hpD⟩
          · exact ⟨Or.inr h1, h2⟩
      rw [this, Finset.prod_insert (fun h => hpQ (Finset.mem_sdiff.1 h).1)]
      ring

lemma density_pred (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (R : Finset ℕ → Prop) :
    {n | R (status Q n)}.HasDensity (∑ D ∈ Q.powerset.filter R, w Q D) := by
  have hc : ∀ b, cnt {n | R (status Q n)} b =
      ∑ D ∈ Q.powerset.filter R, cnt {n | status Q n = D} b := by
    intro b
    unfold cnt
    rw [Finset.card_eq_sum_card_fiberwise (f := status Q) (t := Q.powerset.filter R)]
    · refine Finset.sum_congr rfl fun D hD => ?_
      congr 1
      ext n
      simp only [Finset.mem_filter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ (Finset.mem_filter.1 hD).2⟩, h3⟩
    · intro n hn
      have hn' := (Finset.mem_filter.1 hn).2
      exact Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.filter_subset _ _), hn'⟩
  rw [hasDensity_iff]
  have := tendsto_finset_sum (Q.powerset.filter R) (fun D hD =>
    (hasDensity_iff _ _).1 (density_status Q hQ D (Finset.mem_powerset.1 (Finset.mem_filter.1 hD).1)))
  refine this.congr fun b => ?_
  rw [hc b]; push_cast; rw [Finset.sum_div]

lemma sum_w (Q : Finset ℕ) : ∑ D ∈ Q.powerset, w Q D = 1 := by
  unfold w
  rw [← Finset.prod_add]
  simp

/-! ## Anti-concentration via toggling -/

def tog (p : ℕ) (D : Finset ℕ) : Finset ℕ := if p ∈ D then D.erase p else insert p D

lemma tog_tog (p : ℕ) (D : Finset ℕ) : tog p (tog p D) = D := by
  unfold tog
  by_cases h : p ∈ D
  · rw [if_pos h, if_neg (Finset.notMem_erase p D), Finset.insert_erase h]
  · rw [if_neg h, if_pos (Finset.mem_insert_self p D), Finset.erase_insert h]

lemma tog_subset {p : ℕ} {Q D : Finset ℕ} (hp : p ∈ Q) (hD : D ⊆ Q) : tog p D ⊆ Q := by
  unfold tog
  split_ifs
  · exact (Finset.erase_subset p D).trans hD
  · exact Finset.insert_subset hp hD

lemma w_insert {p : ℕ} {Q E : Finset ℕ} (hp : p ∈ Q) (hE : E ⊆ Q) (hpE : p ∉ E) :
    ∃ C ≥ (0 : ℝ), w Q (insert p E) = (1 / p) * C ∧ w Q E = (1 - 1 / (p : ℝ)) * C := by
  refine ⟨(∏ q ∈ E, 1 / (q : ℝ)) * ∏ q ∈ Q \ insert p E, (1 - 1 / (q : ℝ)), ?_, ?_, ?_⟩
  · exact mul_nonneg (Finset.prod_nonneg fun q _ => by positivity)
      (Finset.prod_nonneg fun q _ => one_sub_nonneg' q)
  · unfold w; rw [Finset.prod_insert hpE]; ring
  · unfold w
    have : Q \ E = insert p (Q \ insert p E) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hx : x = p
        · exact Or.inl hx
        · exact Or.inr ⟨h1, fun h => h.elim hx h2⟩
      · rintro (h1 | ⟨h1, h2⟩)
        · exact ⟨h1 ▸ hp, h1 ▸ hpE⟩
        · exact ⟨h1, fun h => h2 (Or.inr h)⟩
    rw [this, Finset.prod_insert (by simp)]; ring

lemma w_tog {p : ℕ} {Q D : Finset ℕ} (hpr : p.Prime) (hp : p ∈ Q) (hD : D ⊆ Q) :
    w Q D / p ≤ w Q (tog p D) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  unfold tog
  by_cases hpD : p ∈ D
  · rw [if_pos hpD]
    obtain ⟨C, hC, h1, h3⟩ := w_insert hp ((Finset.erase_subset p D).trans hD)
      (Finset.notMem_erase p D)
    rw [Finset.insert_erase hpD] at h1
    rw [h1, h3]
    have : 1 / (p : ℝ) / p ≤ 1 - 1 / p := by
      rw [div_div, div_le_iff₀ (by positivity)]
      have e : (1 - 1 / (p : ℝ)) * (p * p) = p * p - p := by field_simp
      nlinarith
    calc 1 / (p : ℝ) * C / p = (1 / p / p) * C := by ring
      _ ≤ (1 - 1 / p) * C := mul_le_mul_of_nonneg_right this hC
  · rw [if_neg hpD]
    obtain ⟨C, hC, h1, h3⟩ := w_insert hp hD hpD
    rw [h1, h3]
    have : 0 ≤ 1 / (p : ℝ) := by positivity
    have h4 : (1 - 1 / (p : ℝ)) / p ≤ 1 / p := by
      rw [div_le_div_iff_of_pos_right hp0]; linarith
    calc (1 - 1 / (p : ℝ)) * C / p = ((1 - 1 / p) / p) * C := by ring
      _ ≤ 1 / p * C := mul_le_mul_of_nonneg_right h4 hC

lemma sep_out {p q : ℕ} {F : Finset ℕ} {x η : ℝ} (hη : 0 ≤ η)
    (hsep : (1 + η) * (1 - 1 / (p : ℝ)) ≤ 1 - 1 / (q : ℝ))
    (hp1 : x ≤ (1 - 1 / (p : ℝ)) * g F) (hq2 : (1 - 1 / (q : ℝ)) * g F < x * (1 + η)) : False := by
  have hg := g_nonneg F
  have h1 : (1 + η) * x ≤ (1 + η) * ((1 - 1 / (p : ℝ)) * g F) :=
    mul_le_mul_of_nonneg_left hp1 (by linarith)
  have h2 : (1 + η) * (1 - 1 / (p : ℝ)) * g F ≤ (1 - 1 / (q : ℝ)) * g F :=
    mul_le_mul_of_nonneg_right hsep hg
  nlinarith

lemma sep_in {p q : ℕ} {u v x η : ℝ} (hp2 : 2 ≤ p)
    (hsep : (1 + η) * (1 - 1 / (p : ℝ)) ≤ 1 - 1 / (q : ℝ))
    (huv : (1 - 1 / (p : ℝ)) * u = (1 - 1 / (q : ℝ)) * v)
    (hu : u < x * (1 + η)) (hv : x ≤ v) (hv0 : 0 ≤ v) (hη : 0 ≤ η) : False := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hpos : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have h3 : (1 + η) * (1 - 1 / (p : ℝ)) * v ≤ (1 - 1 / (q : ℝ)) * v :=
    mul_le_mul_of_nonneg_right hsep hv0
  have h4 : (1 - 1 / (p : ℝ)) * ((1 + η) * v) ≤ (1 - 1 / (p : ℝ)) * u := by nlinarith
  have h5 : (1 + η) * v ≤ u := le_of_mul_le_mul_left h4 hpos
  nlinarith

lemma card_tog_le (Q P F : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (hPQ : P ⊆ Q) (x η : ℝ)
    (hη : 0 ≤ η)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p < q → (1 + η) * (1 - 1 / (p : ℝ)) ≤ 1 - 1 / (q : ℝ)) :
    (P.filter (fun p => x ≤ g (tog p F) ∧ g (tog p F) < x * (1 + η))).card ≤ 2 := by
  set s := P.filter (fun p => x ≤ g (tog p F) ∧ g (tog p F) < x * (1 + η))
  have hsub : s ⊆ s.filter (· ∈ F) ∪ s.filter (· ∉ F) := by
    intro p hp; by_cases h : p ∈ F
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hp, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hp, h⟩)
  have hA : (s.filter (· ∈ F)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [s, Finset.mem_filter] at ha hb
    have key : ∀ p q, p ∈ P → q ∈ P → p ∈ F → q ∈ F → p < q →
        (x ≤ g (tog p F) ∧ g (tog p F) < x * (1 + η)) →
        (x ≤ g (tog q F) ∧ g (tog q F) < x * (1 + η)) → False := by
      intro p q hp hq hpF hqF hpq h1 h2
      unfold tog at h1 h2
      rw [if_pos hpF] at h1
      rw [if_pos hqF] at h2
      have ep := g_insert (Finset.notMem_erase p F)
      have eq := g_insert (Finset.notMem_erase q F)
      rw [Finset.insert_erase hpF] at ep
      rw [Finset.insert_erase hqF] at eq
      exact sep_in (hQ p (hPQ hp)).two_le (hsep p hp q hq hpq) (ep.symm.trans eq) h1.2 h2.1
        (g_nonneg _) hη
    rcases lt_trichotomy a b with h | h | h
    · exact (key a b ha.1.1 hb.1.1 ha.2 hb.2 h ha.1.2 hb.1.2).elim
    · exact h
    · exact (key b a hb.1.1 ha.1.1 hb.2 ha.2 h hb.1.2 ha.1.2).elim
  have hB : (s.filter (· ∉ F)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [s, Finset.mem_filter] at ha hb
    have key : ∀ p q, p ∈ P → q ∈ P → p ∉ F → q ∉ F → p < q →
        (x ≤ g (tog p F) ∧ g (tog p F) < x * (1 + η)) →
        (x ≤ g (tog q F) ∧ g (tog q F) < x * (1 + η)) → False := by
      intro p q hp hq hpF hqF hpq h1 h2
      unfold tog at h1 h2
      rw [if_neg hpF, g_insert hpF] at h1
      rw [if_neg hqF, g_insert hqF] at h2
      exact sep_out hη (hsep p hp q hq hpq) h1.1 h2.2
    rcases lt_trichotomy a b with h | h | h
    · exact (key a b ha.1.1 hb.1.1 ha.2 hb.2 h ha.1.2 hb.1.2).elim
    · exact h
    · exact (key b a hb.1.1 ha.1.1 hb.2 ha.2 h hb.1.2 ha.1.2).elim
  calc s.card ≤ (s.filter (· ∈ F) ∪ s.filter (· ∉ F)).card := Finset.card_le_card hsub
    _ ≤ (s.filter (· ∈ F)).card + (s.filter (· ∉ F)).card := Finset.card_union_le _ _
    _ ≤ 2 := by omega

theorem anti (Q P : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (hPQ : P ⊆ Q) (x η : ℝ) (hη : 0 ≤ η)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p < q → (1 + η) * (1 - 1 / (p : ℝ)) ≤ 1 - 1 / (q : ℝ)) :
    (∑ D ∈ Q.powerset.filter (fun D => x ≤ g D ∧ g D < x * (1 + η)), w Q D) *
      (∑ p ∈ P, 1 / (p : ℝ)) ≤ 2 := by
  set W := Q.powerset.filter (fun D => x ≤ g D ∧ g D < x * (1 + η))
  have hW : ∀ D ∈ W, D ⊆ Q := fun D hD => Finset.mem_powerset.1 (Finset.mem_filter.1 hD).1
  have step1 : (∑ D ∈ W, w Q D) * (∑ p ∈ P, 1 / (p : ℝ)) = ∑ p ∈ P, ∑ D ∈ W, w Q D / p := by
    rw [Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun D _ => by ring
  have step2 : ∀ p ∈ P, ∑ D ∈ W, w Q D / p ≤ ∑ D ∈ W, w Q (tog p D) := fun p hp =>
    Finset.sum_le_sum fun D hD => w_tog (hQ p (hPQ hp)) (hPQ hp) (hW D hD)
  have step3 : ∀ p ∈ P, ∑ D ∈ W, w Q (tog p D) =
      ∑ F ∈ Q.powerset, if tog p F ∈ W then w Q F else 0 := by
    intro p hp
    rw [← Finset.sum_filter]
    refine Finset.sum_nbij' (tog p) (tog p) ?_ ?_ ?_ ?_ ?_
    · intro D hD
      exact Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (tog_subset (hPQ hp) (hW D hD)),
        by rw [tog_tog]; exact hD⟩
    · intro F hF
      exact (Finset.mem_filter.1 hF).2
    · intro D _; exact tog_tog p D
    · intro F _; exact tog_tog p F
    · intro D _; rfl
  have step4 : ∀ F ∈ Q.powerset, (∑ p ∈ P, if tog p F ∈ W then w Q F else 0) ≤ 2 * w Q F := by
    intro F hF
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hw : 0 ≤ w Q F := by
      unfold w
      exact mul_nonneg (Finset.prod_nonneg fun q _ => by positivity)
        (Finset.prod_nonneg fun q _ => one_sub_nonneg' q)
    have hcard : (P.filter (fun p => tog p F ∈ W)).card ≤ 2 := by
      have := card_tog_le Q P F hQ hPQ x η hη hsep
      refine le_trans (Finset.card_le_card fun p hp => ?_) this
      simp only [Finset.mem_filter, W] at hp ⊢
      exact ⟨hp.1, hp.2.2⟩
    have : ((P.filter (fun p => tog p F ∈ W)).card : ℝ) ≤ 2 := by exact_mod_cast hcard
    exact mul_le_mul_of_nonneg_right this hw
  rw [step1]
  calc ∑ p ∈ P, ∑ D ∈ W, w Q D / p ≤ ∑ p ∈ P, ∑ D ∈ W, w Q (tog p D) :=
        Finset.sum_le_sum step2
    _ = ∑ p ∈ P, ∑ F ∈ Q.powerset, if tog p F ∈ W then w Q F else 0 :=
        Finset.sum_congr rfl step3
    _ = ∑ F ∈ Q.powerset, ∑ p ∈ P, if tog p F ∈ W then w Q F else 0 := Finset.sum_comm
    _ ≤ ∑ F ∈ Q.powerset, 2 * w Q F := Finset.sum_le_sum step4
    _ = 2 := by rw [← Finset.mul_sum, sum_w]; ring


/-! ## Number theory bridge -/

lemma phi_eq {n : ℕ} (hn : n ≠ 0) :
    (Nat.totient n : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
  have h := congrArg (Rat.cast : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors n)
  push_cast at h
  simpa [one_div] using h

noncomputable def hK (K n : ℕ) : ℝ := ∑ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), 1 / (p : ℝ)

noncomputable def QK (K : ℕ) : Finset ℕ := (Finset.range (K + 1)).filter Nat.Prime

lemma QK_prime (K : ℕ) : ∀ p ∈ QK K, p.Prime := fun p hp => (Finset.mem_filter.1 hp).2

lemma prod_ge (s : Finset ℕ) : 1 - ∑ p ∈ s, 1 / (p : ℝ) ≤ ∏ p ∈ s, (1 - 1 / (p : ℝ)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h0 := one_sub_nonneg' a
    have hy : 0 ≤ ∑ p ∈ s, 1 / (p : ℝ) := Finset.sum_nonneg fun p _ => by positivity
    have hx : 0 ≤ 1 / (a : ℝ) := by positivity
    have : (1 - 1 / (a : ℝ)) * (1 - ∑ p ∈ s, 1 / (p : ℝ)) ≤
        (1 - 1 / (a : ℝ)) * ∏ p ∈ s, (1 - 1 / (p : ℝ)) := mul_le_mul_of_nonneg_left ih h0
    nlinarith

lemma phi_split {n : ℕ} (hn : n ≠ 0) (K : ℕ) :
    (Nat.totient n : ℝ) = n * (g (status (QK K) n) *
      ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), (1 - 1 / (p : ℝ))) := by
  rw [phi_eq hn, ← Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => p ≤ K)]
  congr 2
  unfold g status QK
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2, _⟩, h4⟩; exact ⟨⟨by omega, h1⟩, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h2, h3, hn⟩, by omega⟩

lemma lower_incl {n : ℕ} (hn : n ≠ 0) (K : ℕ) {c : ℝ} (h : g (status (QK K) n) < c) :
    (Nat.totient n : ℝ) < c * n := by
  rw [phi_split hn K]
  have hR : ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), (1 - 1 / (p : ℝ)) ≤ 1 :=
    Finset.prod_le_one (fun p _ => one_sub_nonneg' p) (fun p _ => by
      have : 0 ≤ 1 / (p : ℝ) := by positivity
      linarith)
  have hR0 : 0 ≤ ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), (1 - 1 / (p : ℝ)) :=
    Finset.prod_nonneg fun p _ => one_sub_nonneg' p
  have hg := g_nonneg (status (QK K) n)
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have : g (status (QK K) n) * ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K),
      (1 - 1 / (p : ℝ)) < c := by nlinarith
  nlinarith

lemma upper_incl {n : ℕ} (K : ℕ) {c δ : ℝ} (hδ : δ < 1) (h : (Nat.totient n : ℝ) < c * n)
    (hb : hK K n ≤ δ) : g (status (QK K) n) < c / (1 - δ) := by
  have hn : n ≠ 0 := by rintro rfl; simp at h
  rw [phi_split hn K] at h
  have hR := prod_ge (n.primeFactors.filter (fun p => ¬ p ≤ K))
  unfold hK at hb
  have hg := g_nonneg (status (QK K) n)
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [lt_div_iff₀ (by linarith)]
  have h1 : g (status (QK K) n) * ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K),
      (1 - 1 / (p : ℝ)) < c := by
    by_contra hc
    have hc' := le_of_not_gt hc
    nlinarith [mul_le_mul_of_nonneg_left hc' hn'.le]
  have h2 : g (status (QK K) n) * (1 - δ) ≤ g (status (QK K) n) *
      ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), (1 - 1 / (p : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hg
  linarith

/-! ## The bad set -/

lemma tail_sq (K : ℕ) (hK : 1 ≤ K) (N : ℕ) :
    ∑ m ∈ (Finset.range N).filter (fun m => ¬ m ≤ K), 1 / (m : ℝ) ^ 2 ≤ 1 / (K : ℝ) := by
  have key : ∀ j : ℕ, ∑ m ∈ (Finset.range (j + K + 1)).filter (fun m => ¬ m ≤ K),
      1 / (m : ℝ) ^ 2 ≤ 1 / (K : ℝ) - 1 / ((j + K : ℕ) : ℝ) := by
    intro j
    induction j with
    | zero =>
      have : (Finset.range (0 + K + 1)).filter (fun m => ¬ m ≤ K) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro m hm; simp only [Finset.mem_range] at hm; omega
      rw [this]; simp
    | succ j ih =>
      rw [show j + 1 + K + 1 = (j + K + 1) + 1 by ring, Finset.range_add_one,
        Finset.filter_insert, if_pos (by omega),
        Finset.sum_insert (by simp)]
      have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
      have hjK : (0 : ℝ) < (j + K : ℕ) := by push_cast; positivity
      have e : 1 / (((j + K + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / ((j + K : ℕ) : ℝ) - 1 / ((j + 1 + K : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith
  have hsub : (Finset.range N).filter (fun m => ¬ m ≤ K) ⊆
      (Finset.range (N + K + 1)).filter (fun m => ¬ m ≤ K) :=
    Finset.filter_subset_filter _ (Finset.range_subset_range.2 (by omega))
  calc _ ≤ ∑ m ∈ (Finset.range (N + K + 1)).filter (fun m => ¬ m ≤ K), 1 / (m : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 1 / (K : ℝ) - 1 / ((N + K : ℕ) : ℝ) := key N
    _ ≤ 1 / (K : ℝ) := by
        have : (0 : ℝ) ≤ 1 / ((N + K : ℕ) : ℝ) := by positivity
        linarith

lemma card_mult_le (p N : ℕ) (hp : 0 < p) :
    (((Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0)).card : ℝ) ≤ N / p := by
  have h : (Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0) ⊆
      (Finset.Icc 1 (N / p)).image (p * ·) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, ⟨k, rfl⟩, hn0⟩ := hn
    simp only [Finset.mem_image, Finset.mem_Icc]
    refine ⟨k, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos k with h | h
      · simp [h] at hn0
      · exact h
    · rw [Nat.le_div_iff_mul_le hp]; linarith
  have h1 := Finset.card_le_card h
  have h2 := Finset.card_image_le (s := Finset.Icc 1 (N / p)) (f := (p * ·))
  simp only [Nat.card_Icc, add_tsub_cancel_right] at h2
  have h3 : ((Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0)).card ≤ N / p := h1.trans h2
  calc (((Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0)).card : ℝ) ≤ ((N / p : ℕ) : ℝ) := by
        exact_mod_cast h3
    _ ≤ N / p := Nat.cast_div_le

lemma sum_hK (K N : ℕ) (hK1 : 1 ≤ K) : ∑ n ∈ Finset.range N, hK K n ≤ N / K := by
  have e1 : ∀ n ∈ Finset.range N, hK K n = ∑ p ∈ Finset.range N,
      if (p.Prime ∧ ¬ p ≤ K) ∧ (p ∣ n ∧ n ≠ 0) then 1 / (p : ℝ) else 0 := by
    intro n hn
    rw [← Finset.sum_filter]
    unfold hK
    congr 1
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_range] at hn ⊢
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero h3) h2) hn, ⟨h1, h4⟩, h2, h3⟩
    · rintro ⟨_, ⟨h1, h4⟩, h2, h3⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  have e2 : ∀ p ∈ Finset.range N, (∑ n ∈ Finset.range N,
      if (p.Prime ∧ ¬ p ≤ K) ∧ (p ∣ n ∧ n ≠ 0) then 1 / (p : ℝ) else 0) ≤
      if ¬ p ≤ K then N * (1 / (p : ℝ) ^ 2) else 0 := by
    intro p _
    by_cases hp : p.Prime ∧ ¬ p ≤ K
    · have hiff : ∀ n, ((p.Prime ∧ ¬ p ≤ K) ∧ (p ∣ n ∧ n ≠ 0)) ↔ (p ∣ n ∧ n ≠ 0) :=
        fun n => ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩
      rw [if_pos hp.2, Finset.sum_congr rfl (fun n _ => if_congr (hiff n) rfl rfl),
        ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have := card_mult_le p N hp.1.pos
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1.pos
      calc (((Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0)).card : ℝ) * (1 / p)
          ≤ (N / p) * (1 / p) := mul_le_mul_of_nonneg_right this (by positivity)
        _ = N * (1 / (p : ℝ) ^ 2) := by field_simp
    · have : ∀ n, ¬ ((p.Prime ∧ ¬ p ≤ K) ∧ (p ∣ n ∧ n ≠ 0)) := fun n h => hp h.1
      simp only [this, if_false, Finset.sum_const_zero]
      split_ifs <;> positivity
  calc _ ≤ ∑ p ∈ Finset.range N, (if ¬ p ≤ K then N * (1 / (p : ℝ) ^ 2) else 0) :=
        Finset.sum_le_sum e2
    _ = N * ∑ m ∈ (Finset.range N).filter (fun m => ¬ m ≤ K), 1 / (m : ℝ) ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_filter]
    _ ≤ N * (1 / K) := mul_le_mul_of_nonneg_left (tail_sq K hK1 N) (by positivity)
    _ = N / K := by ring

lemma cnt_bad (K N : ℕ) (hK1 : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) :
    (cnt {n | δ < hK K n} N : ℝ) ≤ N / (K * δ) := by
  have hnn : ∀ n, 0 ≤ hK K n := fun n => Finset.sum_nonneg fun p _ => by positivity
  have h1 : (cnt {n | δ < hK K n} N : ℝ) * δ ≤ ∑ n ∈ Finset.range N, hK K n := by
    unfold cnt
    calc (((Finset.range N).filter (· ∈ {n | δ < hK K n})).card : ℝ) * δ
        = ∑ n ∈ (Finset.range N).filter (· ∈ {n | δ < hK K n}), δ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ (Finset.range N).filter (· ∈ {n | δ < hK K n}), hK K n :=
          Finset.sum_le_sum fun n hn => (Finset.mem_filter.1 hn).2.le
      _ ≤ ∑ n ∈ Finset.range N, hK K n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n _ _ => hnn n)
  have h2 := sum_hK K N hK1
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK1
  have h3 : (cnt {n | δ < hK K n} N : ℝ) * δ ≤ N / K := h1.trans h2
  rw [le_div_iff₀ hK'] at h3
  rw [le_div_iff₀ (by positivity)]
  calc (cnt {n | δ < hK K n} N : ℝ) * (K * δ) = cnt {n | δ < hK K n} N * δ * K := by ring
    _ ≤ N := h3

/-! ## Divergence of the prime harmonic series -/

lemma diverge (R : ℝ) : ∃ L, R ≤ ∑ p ∈ (Finset.range L).filter Nat.Prime, 1 / (p : ℝ) := by
  by_contra h
  push Not at h
  apply not_summable_one_div_on_primes
  refine summable_of_sum_range_le (c := R) (fun n => ?_) (fun n => ?_)
  · exact Set.indicator_nonneg (fun p _ => by positivity) _
  · rw [show ∑ i ∈ Finset.range n, Set.indicator {p | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i =
        ∑ p ∈ (Finset.range n).filter Nat.Prime, 1 / (p : ℝ) by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Set.indicator_apply]]
    exact (h n).le


/-! ## Assembly -/

lemma cnt_zero_le (N : ℕ) : cnt {0} N ≤ 1 := by
  unfold cnt
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Set.mem_singleton_iff] at ha hb
  rw [ha.2, hb.2]

lemma w_nonneg (Q D : Finset ℕ) : 0 ≤ w Q D := mul_nonneg
  (Finset.prod_nonneg fun q _ => by positivity) (Finset.prod_nonneg fun q _ => one_sub_nonneg' q)

lemma sep_of_le (L : ℕ) (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpL : p ≤ L) (hqL : q ≤ L)
    (hpq : p < q) :
    (1 + 1 / (L : ℝ) ^ 2) * (1 - 1 / (p : ℝ)) ≤ 1 - 1 / (q : ℝ) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_lt.le
  have hpL' : (p : ℝ) ≤ L := by exact_mod_cast hpL
  have hqL' : (q : ℝ) ≤ L := by exact_mod_cast hqL
  have hpq' : (p : ℝ) + 1 ≤ q := by exact_mod_cast hpq
  have hη0 : 0 ≤ 1 / (L : ℝ) ^ 2 := by positivity
  have h1 : 1 / (L : ℝ) ^ 2 * (1 - 1 / (p : ℝ)) ≤ 1 / (L : ℝ) ^ 2 := by
    have : 0 ≤ 1 / (p : ℝ) := by positivity
    nlinarith
  have h2 : 1 / (L : ℝ) ^ 2 ≤ 1 / ((p : ℝ) * q) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h3 : 1 / ((p : ℝ) * q) ≤ 1 / (p : ℝ) - 1 / q := by
    rw [div_sub_div _ _ (by positivity) (by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  nlinarith

/-! ## Continuity of the distribution function -/

/-- Mass of the finite model below `x`. -/
noncomputable def Sm (Q : Finset ℕ) (x : ℝ) : ℝ :=
  ∑ D ∈ Q.powerset.filter (fun D => g D < x), w Q D

lemma Sm_nonneg (Q : Finset ℕ) (x : ℝ) : 0 ≤ Sm Q x :=
  Finset.sum_nonneg fun D _ => w_nonneg Q D

lemma lower_bd (K : ℕ) {c d : ℝ} (hd : {n : ℕ | (Nat.totient n : ℝ) < c * n}.HasDensity d) :
    Sm (QK K) c ≤ d := by
  unfold Sm
  have h1 := (hasDensity_iff _ _).1 (density_pred (QK K) (QK_prime K) (fun D => g D < c))
  have h2 := ((hasDensity_iff _ _).1 hd).add tendsto_one_div_atTop_nhds_zero_nat
  rw [add_zero] at h2
  refine le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun N => ?_)
  have hsub : {n | g (status (QK K) n) < c} ⊆ {n : ℕ | (Nat.totient n : ℝ) < c * n} ∪ {0} := by
    intro n hn
    by_cases h0 : n = 0
    · exact Or.inr h0
    · exact Or.inl (lower_incl h0 K hn)
  have c1 : cnt {n | g (status (QK K) n) < c} N ≤
      cnt {n : ℕ | (Nat.totient n : ℝ) < c * n} N + 1 := by
    have := (cnt_mono hsub N).trans (cnt_union_le _ {0} N)
    have := cnt_zero_le N
    omega
  show (cnt {n | g (status (QK K) n) < c} N : ℝ) / N ≤
    (cnt {n : ℕ | (Nat.totient n : ℝ) < c * n} N : ℝ) / N + 1 / N
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast c1

lemma upper_bd (K : ℕ) (hK1 : 1 ≤ K) {c d δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hd : {n : ℕ | (Nat.totient n : ℝ) < c * n}.HasDensity d) :
    d ≤ Sm (QK K) (c / (1 - δ)) + 1 / (K * δ) := by
  unfold Sm
  have h2 := (hasDensity_iff _ _).1
    (density_pred (QK K) (QK_prime K) (fun D => g D < c / (1 - δ)))
  have h2' := h2.add (tendsto_const_nhds (x := 1 / ((K : ℝ) * δ)))
  refine le_of_tendsto_of_tendsto ((hasDensity_iff _ _).1 hd) h2'
    (Eventually.of_forall fun N => ?_)
  have hsub : {n : ℕ | (Nat.totient n : ℝ) < c * n} ⊆
      {n | g (status (QK K) n) < c / (1 - δ)} ∪ {n | δ < hK K n} := by
    intro n hn
    by_cases hb : δ < hK K n
    · exact Or.inr hb
    · exact Or.inl (upper_incl K hδ1 hn (le_of_not_gt hb))
  have c2 := (cnt_mono hsub N).trans (cnt_union_le _ _ N)
  have c3 := cnt_bad K N hK1 hδ0
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hKδ : (0 : ℝ) < K * δ := by positivity
  show (cnt {n : ℕ | (Nat.totient n : ℝ) < c * n} N : ℝ) / N ≤
    (cnt {n | g (status (QK K) n) < c / (1 - δ)} N : ℝ) / N + 1 / (K * δ)
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    simp only [Nat.cast_zero, div_zero, zero_add]
    positivity
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have c2' : (cnt {n : ℕ | (Nat.totient n : ℝ) < c * n} N : ℝ) ≤
      cnt {n | g (status (QK K) n) < c / (1 - δ)} N + cnt {n | δ < hK K n} N := by
    exact_mod_cast c2
  have c3' : (cnt {n | δ < hK K n} N : ℝ) / N ≤ 1 / (K * δ) := by
    rw [div_le_iff₀ hN']
    calc (cnt {n | δ < hK K n} N : ℝ) ≤ N / (K * δ) := c3
      _ = 1 / (K * δ) * N := by ring
  calc (cnt {n : ℕ | (Nat.totient n : ℝ) < c * n} N : ℝ) / N
      ≤ ((cnt {n | g (status (QK K) n) < c / (1 - δ)} N : ℝ) + cnt {n | δ < hK K n} N) / N :=
        div_le_div_of_nonneg_right c2' hN'.le
    _ = (cnt {n | g (status (QK K) n) < c / (1 - δ)} N : ℝ) / N +
        (cnt {n | δ < hK K n} N : ℝ) / N := add_div _ _ _
    _ ≤ _ := by linarith

lemma mono_bd {c1 c2 d1 d2 : ℝ} (h12 : c1 ≤ c2)
    (h1 : {n : ℕ | (Nat.totient n : ℝ) < c1 * n}.HasDensity d1)
    (h2 : {n : ℕ | (Nat.totient n : ℝ) < c2 * n}.HasDensity d2) : d1 ≤ d2 := by
  refine le_of_tendsto_of_tendsto ((hasDensity_iff _ _).1 h1) ((hasDensity_iff _ _).1 h2)
    (Eventually.of_forall fun N => ?_)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hsub : {n : ℕ | (Nat.totient n : ℝ) < c1 * n} ⊆
      {n : ℕ | (Nat.totient n : ℝ) < c2 * n} := by
    intro n hn
    simp only [Set.mem_setOf_eq] at hn ⊢
    exact lt_of_lt_of_le hn (mul_le_mul_of_nonneg_right h12 (Nat.cast_nonneg n))
  exact_mod_cast cnt_mono hsub N

lemma window (Q P : Finset ℕ) (hQp : ∀ p ∈ Q, p.Prime) (hPQ : P ⊆ Q) (x y η ε : ℝ)
    (hη0 : 0 ≤ η) (hε : 0 < ε) (hxy : x ≤ y) (hy : y ≤ x * (1 + η))
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p < q → (1 + η) * (1 - 1 / (p : ℝ)) ≤ 1 - 1 / (q : ℝ))
    (hL : 6 / ε ≤ ∑ p ∈ P, 1 / (p : ℝ)) :
    Sm Q y - Sm Q x ≤ ε / 3 := by
  unfold Sm
  have e : (∑ D ∈ Q.powerset.filter (fun D => g D < y), w Q D) =
      (∑ D ∈ Q.powerset.filter (fun D => g D < x), w Q D) +
      ∑ D ∈ (Q.powerset.filter (fun D => g D < y)).filter
        (fun D => ¬ g D < x), w Q D := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun D => g D < x), Finset.filter_filter]
    congr 2
    ext D
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, lt_of_lt_of_le h3 hxy, h3⟩
  have hsub : (Q.powerset.filter (fun D => g D < y)).filter (fun D => ¬ g D < x) ⊆
      Q.powerset.filter (fun D => x ≤ g D ∧ g D < x * (1 + η)) := by
    intro D hD
    simp only [Finset.mem_filter] at hD ⊢
    exact ⟨hD.1.1, le_of_not_gt hD.2, lt_of_lt_of_le hD.1.2 hy⟩
  have ha := anti Q P hQp hPQ x η hη0 hsep
  have hW := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun D _ _ => w_nonneg Q D)
  have hWnn : 0 ≤ ∑ D ∈ Q.powerset.filter (fun D => x ≤ g D ∧ g D < x * (1 + η)), w Q D :=
    Finset.sum_nonneg fun D _ => w_nonneg Q D
  have : (∑ D ∈ Q.powerset.filter (fun D => x ≤ g D ∧ g D < x * (1 + η)), w Q D) ≤ ε / 3 := by
    have h7 : (∑ D ∈ Q.powerset.filter (fun D => x ≤ g D ∧ g D < x * (1 + η)), w Q D) *
        (6 / ε) ≤ 2 := le_trans (mul_le_mul_of_nonneg_left hL hWnn) ha
    rw [mul_div_assoc', div_le_iff₀ hε] at h7
    linarith
  linarith

lemma params (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∃ δ η : ℝ, 1 ≤ K ∧ 0 < δ ∧ δ < 1 ∧ 0 ≤ η ∧ 1 / (K * δ) ≤ ε / 3 ∧
      1 < (1 + η) * (1 - δ) ∧
      ∀ x y : ℝ, x ≤ y → y ≤ x * (1 + η) → Sm (QK K) y - Sm (QK K) x ≤ ε / 3 := by
  obtain ⟨L, hL⟩ := diverge (6 / ε)
  have h6 : 0 < 6 / ε := by positivity
  have hL1 : 1 ≤ L := by
    by_contra h
    have : L = 0 := by omega
    subst this
    simp at hL
    linarith
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = 1 / (L : ℝ) ^ 2 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one (by positivity)]; nlinarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = η / 4 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ < 1 := by rw [hδ]; linarith
  obtain ⟨K0, hK0⟩ := exists_nat_gt (3 / (δ * ε))
  obtain ⟨K, hK⟩ : ∃ K, K = max (max K0 L) 1 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := hK ▸ le_max_right _ _
  have hLK : L ≤ K := hK ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hK0K : (K0 : ℝ) ≤ K := by
    exact_mod_cast (hK ▸ le_trans (le_max_left _ _) (le_max_left _ _) : K0 ≤ K)
  have hPQ : (Finset.range L).filter Nat.Prime ⊆ QK K := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    simp only [QK, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp.2⟩
  have hsep : ∀ p ∈ (Finset.range L).filter Nat.Prime, ∀ q ∈ (Finset.range L).filter Nat.Prime,
      p < q → (1 + η) * (1 - 1 / (p : ℝ)) ≤ 1 - 1 / (q : ℝ) := by
    intro p hp q hq hpq
    simp only [Finset.mem_filter, Finset.mem_range] at hp hq
    rw [hη]
    exact sep_of_le L p q hp.2 hq.2 hp.1.le hq.1.le hpq
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  have hKδ : 1 / (K * δ) ≤ ε / 3 := by
    have : 3 / (δ * ε) < K := lt_of_lt_of_le hK0 hK0K
    rw [div_lt_iff₀ (by positivity)] at this
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨K, δ, η, hK1, hδ0, hδ1, hη0.le, hKδ, ?_, ?_⟩
  · rw [hδ]; nlinarith
  · intro x y hxy hy
    exact window (QK K) _ (QK_prime K) hPQ x y η ε hη0.le hε hxy hy hsep hL

lemma g_anti {Q D : Finset ℕ} (hD : D ⊆ Q) : g Q ≤ g D := by
  unfold g
  rw [← Finset.prod_sdiff hD]
  have h1 : ∏ p ∈ Q \ D, (1 - 1 / (p : ℝ)) ≤ 1 :=
    Finset.prod_le_one (fun p _ => one_sub_nonneg' p) (fun p _ => by
      have : 0 ≤ 1 / (p : ℝ) := by positivity
      linarith)
  have h2 : 0 ≤ ∏ p ∈ D, (1 - 1 / (p : ℝ)) := Finset.prod_nonneg fun p _ => one_sub_nonneg' p
  nlinarith

lemma Sm_zero (Q : Finset ℕ) {x : ℝ} (hx : x ≤ g Q) : Sm Q x = 0 := by
  unfold Sm
  apply Finset.sum_eq_zero
  intro D hD
  simp only [Finset.mem_filter, Finset.mem_powerset] at hD
  exact absurd hD.2 (not_lt.2 (hx.trans (g_anti hD.1)))

lemma g_pos (K : ℕ) : 0 < g (QK K) := Finset.prod_pos fun p hp => by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (QK_prime K p hp).two_le
  have : 1 / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith

lemma core (f : ℝ → ℝ) (hf : Erdos50.IsDistributionOfPhiRatio f) (ε : ℝ) (hε : 0 < ε) :
    ∃ r ρ0 : ℝ, 1 < r ∧ 0 < ρ0 ∧
      (∀ c1 ∈ Icc (0 : ℝ) 1, ∀ c2 ∈ Icc (0 : ℝ) 1, c1 ≤ c2 → c2 ≤ c1 * r →
        f c2 - f c1 ≤ 2 * ε / 3) ∧
      (∀ c ∈ Icc (0 : ℝ) 1, c ≤ ρ0 → f c ≤ ε / 3) := by
  obtain ⟨K, δ, η, hK1, hδ0, hδ1, hη0, hKδ, hr, hwin⟩ := params ε hε
  refine ⟨(1 + η) * (1 - δ), (1 - δ) * g (QK K), hr, mul_pos (by linarith) (g_pos K), ?_, ?_⟩
  · intro c1 hc1 c2 hc2 h12 h2r
    have hu := upper_bd K hK1 hδ0 hδ1 (hf c2 hc2)
    have hl := lower_bd K (hf c1 hc1)
    have hxy : c1 ≤ c2 / (1 - δ) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith [hc1.1]
    have hy : c2 / (1 - δ) ≤ c1 * (1 + η) := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hw := hwin c1 (c2 / (1 - δ)) hxy hy
    linarith
  · intro c hc hcρ
    have hu := upper_bd K hK1 hδ0 hδ1 (hf c hc)
    have hz : Sm (QK K) (c / (1 - δ)) = 0 :=
      Sm_zero _ (by rw [div_le_iff₀ (by linarith)]; linarith)
    linarith

theorem cont (f : ℝ → ℝ) (hf : Erdos50.IsDistributionOfPhiRatio f) :
    ContinuousOn f (Icc 0 1) := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  obtain ⟨r, ρ0, hr, hρ0, hwin, hzero⟩ := core f hf ε hε
  have hnn : ∀ c ∈ Icc (0 : ℝ) 1, 0 ≤ f c := fun c hc =>
    (Sm_nonneg _ _).trans (lower_bd 0 (hf c hc))
  have hmono : ∀ c1 ∈ Icc (0 : ℝ) 1, ∀ c2 ∈ Icc (0 : ℝ) 1, c1 ≤ c2 → f c1 ≤ f c2 :=
    fun c1 hc1 c2 hc2 h => mono_bd h (hf c1 hc1) (hf c2 hc2)
  have hr0 : 0 < r := by linarith
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = 1 / r := ⟨_, rfl⟩
  have hu : u * r = 1 := by rw [hu_def]; field_simp
  have hu1 : u < 1 := by rw [hu_def, div_lt_one hr0]; exact hr
  rcases hb.1.eq_or_lt with hb0 | hb0
  · subst hb0
    refine ⟨ρ0, hρ0, fun a ha hab => ?_⟩
    rw [Real.dist_eq] at hab ⊢
    have ha' : a ≤ ρ0 := by
      rw [sub_zero, abs_of_nonneg ha.1] at hab; exact hab.le
    have h1 := hzero a ha ha'
    have h2 := hzero 0 hb hρ0.le
    have h3 := hnn a ha
    have h4 := hnn 0 hb
    rw [abs_lt]; constructor <;> linarith
  · refine ⟨b * (1 - u), mul_pos hb0 (by linarith), fun a ha hab => ?_⟩
    rw [Real.dist_eq, abs_lt] at hab
    rw [Real.dist_eq, abs_lt]
    rcases le_total a b with hab' | hab'
    · have h1 : b * u < a := by linarith [hab.1]
      have h2 : b * u * r < a * r := mul_lt_mul_of_pos_right h1 hr0
      have h3 : b * u * r = b := by rw [mul_assoc, hu, mul_one]
      have hbr : b ≤ a * r := by linarith
      have := hwin a ha b hb hab' hbr
      have := hmono a ha b hb hab'
      constructor <;> linarith
    · have h2 : 2 - u ≤ r := by nlinarith [sq_nonneg (r - 1)]
      have h3 : b * (2 - u) ≤ b * r := mul_le_mul_of_nonneg_left h2 hb0.le
      have har : a ≤ b * r := by linarith [hab.2]
      have := hwin b hb a ha hab' har
      have := hmono b hb a ha hab'
      constructor <;> linarith


/-! ## Primes in dyadic blocks -/

/-- Primes in `(a, b]`. -/
def PB (a b : ℕ) : Finset ℕ := (Finset.Ioc a b).filter Nat.Prime

lemma mem_PB {a b p : ℕ} : p ∈ PB a b ↔ (a < p ∧ p ≤ b) ∧ p.Prime := by
  simp [PB]

lemma PB_union {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) : PB a c = PB a b ∪ PB b c := by
  ext p; simp only [mem_PB, Finset.mem_union]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    by_cases h : p ≤ b
    · exact Or.inl ⟨⟨h1, h⟩, h3⟩
    · exact Or.inr ⟨⟨by omega, h2⟩, h3⟩
  · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
    · exact ⟨⟨h1, by omega⟩, h3⟩
    · exact ⟨⟨by omega, h2⟩, h3⟩

lemma PB_disjoint (a b c : ℕ) : Disjoint (PB a b) (PB b c) := by
  rw [Finset.disjoint_left]; intro p h1 h2
  rw [mem_PB] at h1 h2; omega

lemma prod_PB_le (a b : ℕ) : ∏ p ∈ PB a b, p ≤ 4 ^ b := by
  refine le_trans ?_ (primorial_le_four_pow b)
  unfold primorial
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · intro p hp
    rw [mem_PB] at hp
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp.2⟩
  · intro p hp _
    exact (Finset.mem_filter.1 hp).2.one_lt.le

lemma blk_count (i : ℕ) : i * (PB (2 ^ i) (2 ^ (i + 1))).card ≤ 2 ^ (i + 2) := by
  have h1 : (2 ^ i) ^ (PB (2 ^ i) (2 ^ (i + 1))).card ≤ ∏ p ∈ PB (2 ^ i) (2 ^ (i + 1)), p :=
    Finset.pow_card_le_prod _ _ _ fun p hp => (mem_PB.1 hp).1.1.le
  have h2 := h1.trans (prod_PB_le _ _)
  rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ'] at h2
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
  calc i * (PB (2 ^ i) (2 ^ (i + 1))).card ≤ 2 ^ (i + 1 + 1) := this
    _ = 2 ^ (i + 2) := by ring_nf

lemma blk_sum_inv (i : ℕ) (hi : 1 ≤ i) :
    ∑ p ∈ PB (2 ^ i) (2 ^ (i + 1)), 1 / (p : ℝ) ≤ 4 / i := by
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have h2 : (0 : ℝ) < 2 ^ i := by positivity
  have h1 : ∑ p ∈ PB (2 ^ i) (2 ^ (i + 1)), 1 / (p : ℝ) ≤
      ∑ _p ∈ PB (2 ^ i) (2 ^ (i + 1)), 1 / (2 : ℝ) ^ i := by
    apply Finset.sum_le_sum
    intro p hp
    have : (2 : ℝ) ^ i ≤ p := by exact_mod_cast (mem_PB.1 hp).1.1.le
    exact one_div_le_one_div_of_le h2 this
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  refine h1.trans ?_
  have hc : (i : ℝ) * (PB (2 ^ i) (2 ^ (i + 1))).card ≤ 2 ^ (i + 2) := by
    exact_mod_cast blk_count i
  rw [mul_one_div, div_le_div_iff₀ h2 hi']
  calc ((PB (2 ^ i) (2 ^ (i + 1))).card : ℝ) * i = i * (PB (2 ^ i) (2 ^ (i + 1))).card := by ring
    _ ≤ 2 ^ (i + 2) := hc
    _ = 4 * 2 ^ i := by ring

lemma blk_sum_log (i : ℕ) :
    ∑ p ∈ PB (2 ^ i) (2 ^ (i + 1)), Real.log p / (p : ℝ) ≤ 4 * Real.log 2 := by
  have h2 : (0 : ℝ) < 2 ^ i := by positivity
  have h1 : ∑ p ∈ PB (2 ^ i) (2 ^ (i + 1)), Real.log p / (p : ℝ) ≤
      ∑ p ∈ PB (2 ^ i) (2 ^ (i + 1)), Real.log p / (2 : ℝ) ^ i := by
    apply Finset.sum_le_sum
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_PB.1 hp).2.one_lt.le
    have : (2 : ℝ) ^ i ≤ p := by exact_mod_cast (mem_PB.1 hp).1.1.le
    exact div_le_div_of_nonneg_left (Real.log_nonneg hp1) h2 this
  refine h1.trans ?_
  rw [← Finset.sum_div, div_le_iff₀ h2]
  have hlog : ∑ p ∈ PB (2 ^ i) (2 ^ (i + 1)), Real.log p =
      Real.log ((∏ p ∈ PB (2 ^ i) (2 ^ (i + 1)), p : ℕ) : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (mem_PB.1 hp).2.ne_zero
  rw [hlog]
  have hpos : (0 : ℝ) < ((∏ p ∈ PB (2 ^ i) (2 ^ (i + 1)), p : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun p hp => (mem_PB.1 hp).2.pos
  have hle : ((∏ p ∈ PB (2 ^ i) (2 ^ (i + 1)), p : ℕ) : ℝ) ≤ (4 : ℝ) ^ (2 ^ (i + 1)) := by
    exact_mod_cast prod_PB_le (2 ^ i) (2 ^ (i + 1))
  refine (Real.log_le_log hpos hle).trans ?_
  rw [Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  ring_nf
  nlinarith [this]

lemma sum_log_le (k : ℕ) :
    ∑ p ∈ PB 0 (2 ^ k), Real.log p / (p : ℝ) ≤ 4 * k * Real.log 2 := by
  induction k with
  | zero =>
    have : PB 0 (2 ^ 0) = ∅ := by
      ext p; simp only [mem_PB, pow_zero, Finset.notMem_empty, iff_false]
      rintro ⟨⟨h1, h2⟩, h3⟩
      exact absurd h3 (by interval_cases p; decide)
    rw [this]; simp
  | succ k ih =>
    rw [PB_union (Nat.zero_le _) (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k)),
      Finset.sum_union (PB_disjoint _ _ _)]
    have := blk_sum_log k
    push_cast
    linarith

lemma prod_blk (i : ℕ) (hi : 1 ≤ i) :
    1 - 4 / (i : ℝ) ≤ ∏ p ∈ PB (2 ^ i) (2 ^ (i + 1)), (1 - 1 / (p : ℝ)) :=
  le_trans (by linarith [blk_sum_inv i hi]) (prod_ge _)

lemma prod_range (k : ℕ) (hk : 5 ≤ k) (m : ℕ) (hm : k ≤ m) :
    (((k : ℝ) - 4) / ((m : ℝ) - 4)) ^ 4 ≤ ∏ p ∈ PB (2 ^ k) (2 ^ m), (1 - 1 / (p : ℝ)) := by
  induction m, hm using Nat.le_induction with
  | base =>
    have : PB (2 ^ k) (2 ^ k) = ∅ := by
      ext p; simp only [mem_PB, Finset.notMem_empty, iff_false]; omega
    have hk' : (k : ℝ) - 4 ≠ 0 := by
      have : (5 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    rw [this, Finset.prod_empty, div_self hk', one_pow]
  | succ m hm ih =>
    rw [PB_union (Nat.pow_le_pow_right (by norm_num) hm)
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m)),
      Finset.prod_union (PB_disjoint _ _ _)]
    have hb := prod_blk m (by omega)
    have hk5 : (5 : ℝ) ≤ k := by exact_mod_cast hk
    have hmk : (k : ℝ) ≤ m := by exact_mod_cast hm
    have ha : (0 : ℝ) < (k : ℝ) - 4 := by linarith
    have ht : (0 : ℝ) < (m : ℝ) - 4 := by linarith
    have hm0 : (0 : ℝ) < m := by linarith
    have h1 : (0 : ℝ) ≤ 1 - 4 / (m : ℝ) := by
      rw [sub_nonneg, div_le_one hm0]; linarith
    have key : (((k : ℝ) - 4) / (((m + 1 : ℕ) : ℝ) - 4)) ^ 4 ≤
        (((k : ℝ) - 4) / ((m : ℝ) - 4)) ^ 4 * (1 - 4 / (m : ℝ)) := by
      push_cast
      have e1 : 1 - 4 / (m : ℝ) = ((m : ℝ) - 4) / m := by field_simp
      rw [e1, div_pow, div_pow, div_mul_div_comm, div_le_div_iff₀ (pow_pos (by linarith) 4) (mul_pos (pow_pos ht 4) hm0)]
      have e2 : ((m : ℝ) + 1 - 4) ^ 4 * ((m : ℝ) - 4) - ((m : ℝ) - 4) ^ 4 * m =
          ((m : ℝ) - 4) * (6 * ((m : ℝ) - 4) ^ 2 + 4 * ((m : ℝ) - 4) + 1) := by ring
      have e3 : 0 ≤ ((m : ℝ) - 4) * (6 * ((m : ℝ) - 4) ^ 2 + 4 * ((m : ℝ) - 4) + 1) := by
        positivity
      have e4 : ((m : ℝ) - 4) ^ 4 * m ≤ ((m : ℝ) + 1 - 4) ^ 4 * ((m : ℝ) - 4) := by linarith
      calc ((k : ℝ) - 4) ^ 4 * (((m : ℝ) - 4) ^ 4 * m)
          ≤ ((k : ℝ) - 4) ^ 4 * (((m : ℝ) + 1 - 4) ^ 4 * ((m : ℝ) - 4)) :=
            mul_le_mul_of_nonneg_left e4 (by positivity)
        _ = ((k : ℝ) - 4) ^ 4 * ((m : ℝ) - 4) * ((m : ℝ) + 1 - 4) ^ 4 := by ring
    refine key.trans ?_
    exact mul_le_mul ih hb h1 (Finset.prod_nonneg fun p _ => one_sub_nonneg' p)

lemma prod_scale (k : ℕ) (hk : 5 ≤ k) :
    (1 / 50 : ℝ) ^ 4 ≤ ∏ p ∈ PB (2 ^ k) (2 ^ (10 * k)), (1 - 1 / (p : ℝ)) := by
  refine le_trans ?_ (prod_range k hk (10 * k) (by omega))
  have hk5 : (5 : ℝ) ≤ k := by exact_mod_cast hk
  apply pow_le_pow_left₀ (by norm_num)
  push_cast
  rw [div_le_div_iff₀ (by norm_num) (by linarith)]
  linarith

/-! ## Periodic sets: complements, intersections, independence -/

lemma Per.compl {Y : Set ℕ} {N : ℕ} (h : Per Y N) : Per Yᶜ N := fun n => by
  simp only [Set.mem_compl_iff]; rw [h n]

lemma Per.mul_right {Y : Set ℕ} {N : ℕ} (h : Per Y N) (k : ℕ) : Per Y (N * k) :=
  fun n => h.mem_add_mul n k

lemma Per.inter {Y Z : Set ℕ} {N N' : ℕ} (hY : Per Y N) (hZ : Per Z N') :
    Per (Y ∩ Z) (N * N') := by
  intro n
  simp only [Set.mem_inter_iff]
  rw [hY.mem_add_mul n N', hZ.mem_add_mul n N, mul_comm N' N]

lemma Per.cnt_inter {Y Z : Set ℕ} {N N' : ℕ} (hY : Per Y N) (hZ : Per Z N') (hN : 0 < N)
    (hN' : 0 < N') (hc : Nat.Coprime N N') :
    cnt (Y ∩ Z) (N * N') = cnt Y N * cnt Z N' := by
  unfold cnt
  rw [← Finset.card_product]
  refine Finset.card_bij (fun n _ => (n % N, n % N')) ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_inter_iff] at hn
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨Nat.mod_lt _ hN, (hY.mem_mod n).1 hn.2.1⟩, ⟨Nat.mod_lt _ hN', (hZ.mem_mod n).1 hn.2.2⟩⟩
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    simp only [Prod.mk.injEq] at hab
    have h1 : a ≡ b [MOD N * N'] := (Nat.modEq_and_modEq_iff_modEq_mul hc).1 ⟨hab.1, hab.2⟩
    rwa [Nat.ModEq, Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at h1
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hab
    obtain ⟨⟨ha, haY⟩, hb, hbZ⟩ := hab
    have hk := (Nat.chineseRemainder hc a b).2
    have hk1 : (Nat.chineseRemainder hc a b : ℕ) % N = a := by
      have := hk.1; rwa [Nat.ModEq, Nat.mod_eq_of_lt ha] at this
    have hk2 : (Nat.chineseRemainder hc a b : ℕ) % N' = b := by
      have := hk.2; rwa [Nat.ModEq, Nat.mod_eq_of_lt hb] at this
    refine ⟨Nat.chineseRemainder hc a b, ?_, by rw [hk1, hk2]⟩
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_inter_iff]
    refine ⟨Nat.chineseRemainder_lt_mul hc a b hN.ne' hN'.ne', ?_, ?_⟩
    · rw [hY.mem_mod, hk1]; exact haY
    · rw [hZ.mem_mod, hk2]; exact hbZ

/-- The density of a periodic set, as a number. -/
noncomputable def pd (Y : Set ℕ) (N : ℕ) : ℝ := (cnt Y N : ℝ) / N

lemma Per.pd_inter {Y Z : Set ℕ} {N N' : ℕ} (hY : Per Y N) (hZ : Per Z N') (hN : 0 < N)
    (hN' : 0 < N') (hc : Nat.Coprime N N') :
    pd (Y ∩ Z) (N * N') = pd Y N * pd Z N' := by
  unfold pd
  rw [hY.cnt_inter hZ hN hN' hc]
  have h1 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2 : (N' : ℝ) ≠ 0 := by exact_mod_cast hN'.ne'
  push_cast; field_simp

lemma Per.pd_eq_of_hasDensity {Y : Set ℕ} {N : ℕ} (h : Per Y N) (hN : 0 < N) {d : ℝ}
    (hd : Y.HasDensity d) : pd Y N = d :=
  HasDensity.unique (h.hasDensity hN) hd

lemma pd_nonneg (Y : Set ℕ) (N : ℕ) : 0 ≤ pd Y N := by unfold pd; positivity

lemma pd_compl {Y : Set ℕ} {N : ℕ} (hN : 0 < N) : pd Yᶜ N = 1 - pd Y N := by
  unfold pd
  have h := cnt_split Set.univ Y N
  rw [Set.univ_inter, ← Set.compl_eq_univ_diff] at h
  have hu : cnt Set.univ N = N := by simp [cnt]
  rw [hu] at h
  have h1 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h' : (N : ℝ) = (cnt Y N : ℝ) + cnt Yᶜ N := by exact_mod_cast h
  field_simp; linarith

/-! ## One scale: no prime of a block divides `n` -/

lemma pd_noprime (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) :
    pd {n | status R n = ∅} (∏ p ∈ R, p) = ∏ p ∈ R, (1 - 1 / (p : ℝ)) := by
  have h := density_status R hR ∅ (Finset.empty_subset R)
  rw [(status_per R (· = ∅)).pd_eq_of_hasDensity (prod_pos_of_primes R hR) h]
  simp [w]

/-! ## One scale: the product of the primes of a block dividing `n` is small -/

lemma cnt_mul_le_sum (S : Set ℕ) (N : ℕ) (c : ℝ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    (h : ∀ n ∈ S, c ≤ F n) : (cnt S N : ℝ) * c ≤ ∑ n ∈ Finset.range N, F n := by
  unfold cnt
  calc (((Finset.range N).filter (· ∈ S)).card : ℝ) * c
      = ∑ _n ∈ (Finset.range N).filter (· ∈ S), c := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ (Finset.range N).filter (· ∈ S), F n :=
        Finset.sum_le_sum fun n hn => h n (Finset.mem_filter.1 hn).2
    _ ≤ ∑ n ∈ Finset.range N, F n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n _ _ => hF n)

lemma markov_B (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) (T : ℕ) (hT : 1 < T) (N : ℕ) :
    (cnt {n | ¬ (∏ p ∈ status R n, p ≤ T)} N : ℝ) * Real.log T ≤
      Real.log T + N * ∑ p ∈ R, Real.log p / (p : ℝ) := by
  have hlT : 0 ≤ Real.log T := Real.log_nonneg (by exact_mod_cast hT.le)
  have hlp : ∀ p ∈ R, 0 ≤ Real.log (p : ℝ) := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (hR p hp).one_lt.le)
  have hcard : (cnt {n | ¬ (∏ p ∈ status R n, p ≤ T)} N : ℝ) ≤
      (cnt {n | ¬ (∏ p ∈ status R n, p ≤ T) ∧ n ≠ 0} N : ℝ) + 1 := by
    have hsub : {n | ¬ (∏ p ∈ status R n, p ≤ T)} ⊆
        {n | ¬ (∏ p ∈ status R n, p ≤ T) ∧ n ≠ 0} ∪ {0} := by
      intro n hn
      by_cases h0 : n = 0
      · exact Or.inr h0
      · exact Or.inl ⟨hn, h0⟩
    have h1 := (cnt_mono hsub N).trans (cnt_union_le _ _ N)
    have h2 := cnt_zero_le N
    exact_mod_cast (by omega : cnt {n | ¬ (∏ p ∈ status R n, p ≤ T)} N ≤
      cnt {n | ¬ (∏ p ∈ status R n, p ≤ T) ∧ n ≠ 0} N + 1)
  have hpt : ∀ n ∈ {n | ¬ (∏ p ∈ status R n, p ≤ T) ∧ n ≠ 0},
      Real.log T ≤ ∑ p ∈ R, if p ∣ n ∧ n ≠ 0 then Real.log (p : ℝ) else 0 := by
    intro n hn
    have hn : ¬ (∏ p ∈ status R n, p ≤ T) ∧ n ≠ 0 := hn
    have e : (∑ p ∈ R, if p ∣ n ∧ n ≠ 0 then Real.log (p : ℝ) else 0) =
        ∑ p ∈ status R n, Real.log (p : ℝ) := by
      unfold status
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp [hn.2]
    rw [e]
    have e2 : ∑ p ∈ status R n, Real.log (p : ℝ) =
        Real.log ((∏ p ∈ status R n, p : ℕ) : ℝ) := by
      rw [Nat.cast_prod, Real.log_prod]
      intro p hp
      exact_mod_cast (hR p (Finset.mem_filter.1 hp).1).ne_zero
    rw [e2]
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < T))
    exact_mod_cast (not_le.1 hn.1).le
  have h1 := cnt_mul_le_sum {n | ¬ (∏ p ∈ status R n, p ≤ T) ∧ n ≠ 0} N (Real.log T)
    (fun n => ∑ p ∈ R, if p ∣ n ∧ n ≠ 0 then Real.log (p : ℝ) else 0)
    (fun n => Finset.sum_nonneg fun p hp => by split_ifs; exacts [hlp p hp, le_rfl]) hpt
  have h2 : (∑ n ∈ Finset.range N, ∑ p ∈ R, if p ∣ n ∧ n ≠ 0 then Real.log (p : ℝ) else 0) ≤
      N * ∑ p ∈ R, Real.log p / (p : ℝ) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have := card_mult_le p N (hR p hp).pos
    calc (((Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0)).card : ℝ) * Real.log p
        ≤ (N / p) * Real.log p := mul_le_mul_of_nonneg_right this (hlp p hp)
      _ = N * (Real.log p / p) := by ring
  nlinarith [mul_le_mul_of_nonneg_right hcard hlT]

lemma pd_B_compl_le (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) (T : ℕ) (hT : 1 < T) :
    pd {n | ¬ (∏ p ∈ status R n, p ≤ T)} (∏ p ∈ R, p) ≤
      (∑ p ∈ R, Real.log p / (p : ℝ)) / Real.log T := by
  have hlT : 0 < Real.log T := Real.log_pos (by exact_mod_cast hT)
  have hper := status_per R (fun D => ¬ (∏ p ∈ D, p ≤ T))
  have hd := (hasDensity_iff _ _).1 (hper.hasDensity (prod_pos_of_primes R hR))
  have hr : Tendsto (fun N : ℕ => 1 / (N : ℝ) + (∑ p ∈ R, Real.log p / (p : ℝ)) / Real.log T)
      atTop (𝓝 (0 + (∑ p ∈ R, Real.log p / (p : ℝ)) / Real.log T)) :=
    tendsto_one_div_atTop_nhds_zero_nat.add tendsto_const_nhds
  rw [zero_add] at hr
  refine le_of_tendsto_of_tendsto hd hr ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hm := markov_B R hR T hT N
  rw [div_add_div _ _ hN'.ne' hlT.ne', div_le_div_iff₀ hN' (mul_pos hN' hlT)]
  nlinarith [hm, hN']
/-! ## The scales -/

/-- Exponents of the scales: `k_{j+1} = 2 * 2 ^ (10 * k_j)`. -/
def kk (k0 : ℕ) : ℕ → ℕ
  | 0 => k0
  | j + 1 => 2 * 2 ^ (10 * kk k0 j)

/-- Lower threshold `l_j = 2 ^ k_j`. -/
def ll (k0 j : ℕ) : ℕ := 2 ^ kk k0 j

/-- Upper threshold `m_j = l_j ^ 10`. -/
def mm (k0 j : ℕ) : ℕ := 2 ^ (10 * kk k0 j)

/-- Upper threshold of the previous scale. -/
def mprev (k0 : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => mm k0 j

lemma kk_succ (k0 j : ℕ) : kk k0 (j + 1) = 2 * 2 ^ (10 * kk k0 j) := rfl

lemma mprev_succ (k0 j : ℕ) : mprev k0 (j + 1) = mm k0 j := rfl

lemma kk_ge (k0 j : ℕ) : k0 ≤ kk k0 j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    rw [kk_succ]
    have : 10 * kk k0 j < 2 ^ (10 * kk k0 j) := Nat.lt_two_pow_self
    omega

lemma ll_le_mm (k0 j : ℕ) : ll k0 j ≤ mm k0 j :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

lemma four_pow_mprev_le (k0 j : ℕ) : 4 ^ mprev k0 j ≤ ll k0 j := by
  cases j with
  | zero => simp only [mprev, pow_zero, ll]; exact Nat.one_le_two_pow
  | succ j =>
    rw [mprev_succ]
    unfold ll mm
    rw [kk_succ, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]

lemma mprev_le_ll (k0 j : ℕ) : mprev k0 j ≤ ll k0 j :=
  (Nat.lt_pow_self (by norm_num : 1 < 4)).le.trans (four_pow_mprev_le k0 j)

lemma ll_ge (k0 j : ℕ) : 2 ^ k0 ≤ ll k0 j :=
  Nat.pow_le_pow_right (by norm_num) (kk_ge k0 j)

lemma mm_eq (k0 j : ℕ) : mm k0 j = ll k0 j ^ 10 := by
  unfold mm ll; rw [← pow_mul, mul_comm]

/-! ## Blocks of primes and the success set of a scale -/

lemma PB_prime {a b p : ℕ} (h : p ∈ PB a b) : p.Prime := (mem_PB.1 h).2

lemma PB_disjoint' {a b c d : ℕ} (h : b ≤ c) : Disjoint (PB a b) (PB c d) := by
  rw [Finset.disjoint_left]; intro p h1 h2
  rw [mem_PB] at h1 h2; omega

/-- Primes between the previous scale and `l_j`. -/
def Rp (k0 j : ℕ) : Finset ℕ := PB (mprev k0 j) (ll k0 j)

/-- Primes in `(l_j, m_j]`. -/
def Rb (k0 j : ℕ) : Finset ℕ := PB (ll k0 j) (mm k0 j)

/-- Scale `j` succeeds at `n`. -/
def succS (k0 j : ℕ) : Set ℕ :=
  {n | status (Rb k0 j) n = ∅} ∩ {n | ∏ p ∈ status (Rp k0 j) n, p ≤ ll k0 j ^ 8}

lemma coprime_prod {S T : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime)
    (h : Disjoint S T) : Nat.Coprime (∏ p ∈ S, p) (∏ p ∈ T, p) := by
  refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq => ?_
  exact (Nat.coprime_primes (hS p hp) (hT q hq)).2
    (fun e => Finset.disjoint_left.1 h hp (e ▸ hq))

lemma per_succ (k0 j : ℕ) :
    Per (succS k0 j) ((∏ p ∈ Rb k0 j, p) * ∏ p ∈ Rp k0 j, p) :=
  (status_per (Rb k0 j) (· = ∅)).inter
    (status_per (Rp k0 j) (fun D => ∏ p ∈ D, p ≤ ll k0 j ^ 8))

lemma pd_succ (k0 j : ℕ) (hk : 5 ≤ k0) :
    (1 / 50 : ℝ) ^ 4 / 2 ≤ pd (succS k0 j) ((∏ p ∈ Rb k0 j, p) * ∏ p ∈ Rp k0 j, p) := by
  have hRb : ∀ p ∈ Rb k0 j, p.Prime := fun p hp => PB_prime hp
  have hRp : ∀ p ∈ Rp k0 j, p.Prime := fun p hp => PB_prime hp
  have hk5 : 5 ≤ kk k0 j := hk.trans (kk_ge k0 j)
  have hkpos : (0 : ℝ) < kk k0 j := by exact_mod_cast (by omega : 0 < kk k0 j)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : (1 / 50 : ℝ) ^ 4 ≤ pd {n | status (Rb k0 j) n = ∅} (∏ p ∈ Rb k0 j, p) := by
    rw [pd_noprime (Rb k0 j) hRb]
    exact prod_scale (kk k0 j) hk5
  have hT : 1 < ll k0 j ^ 8 :=
    Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
  have hBc := pd_B_compl_le (Rp k0 j) hRp (ll k0 j ^ 8) hT
  have hsum : ∑ p ∈ Rp k0 j, Real.log p / (p : ℝ) ≤ 4 * (kk k0 j) * Real.log 2 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (sum_log_le (kk k0 j))
    · intro p hp
      unfold Rp ll at hp
      rw [mem_PB] at hp ⊢
      exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
    · intro p hp _
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast (PB_prime hp).one_lt.le))
        (by positivity)
  have hlog : Real.log ((ll k0 j ^ 8 : ℕ) : ℝ) = 8 * (kk k0 j) * Real.log 2 := by
    unfold ll; push_cast; rw [← pow_mul, Real.log_pow]; push_cast; ring
  have hpos : 0 < 8 * (kk k0 j : ℝ) * Real.log 2 := by positivity
  have hBc' : pd {n | ¬ (∏ p ∈ status (Rp k0 j) n, p ≤ ll k0 j ^ 8)} (∏ p ∈ Rp k0 j, p) ≤
      1 / 2 := by
    refine hBc.trans ?_
    rw [hlog, div_le_iff₀ hpos]
    linarith
  have hc : pd {n | ¬ (∏ p ∈ status (Rp k0 j) n, p ≤ ll k0 j ^ 8)} (∏ p ∈ Rp k0 j, p) =
      1 - pd {n | ∏ p ∈ status (Rp k0 j) n, p ≤ ll k0 j ^ 8} (∏ p ∈ Rp k0 j, p) :=
    pd_compl (Y := {n | ∏ p ∈ status (Rp k0 j) n, p ≤ ll k0 j ^ 8})
      (prod_pos_of_primes _ hRp)
  have hB : (1 / 2 : ℝ) ≤
      pd {n | ∏ p ∈ status (Rp k0 j) n, p ≤ ll k0 j ^ 8} (∏ p ∈ Rp k0 j, p) := by linarith
  have hI := (status_per (Rb k0 j) (· = ∅)).pd_inter
    (status_per (Rp k0 j) (fun D => ∏ p ∈ D, p ≤ ll k0 j ^ 8))
    (prod_pos_of_primes _ hRb) (prod_pos_of_primes _ hRp)
    (coprime_prod hRb hRp (PB_disjoint _ _ _).symm)
  unfold succS
  rw [hI]
  calc (1 / 50 : ℝ) ^ 4 / 2 = (1 / 50 : ℝ) ^ 4 * (1 / 2) := by ring
    _ ≤ _ := mul_le_mul hA hB (by norm_num) (pd_nonneg _ _)

/-! ## Failing at every scale is rare -/

/-- `n` fails at each of the first `J` scales. -/
def FF (k0 J : ℕ) : Set ℕ := {n | ∀ j < J, n ∉ succS k0 j}

lemma FF_succ (k0 J : ℕ) : FF k0 (J + 1) = FF k0 J ∩ (succS k0 J)ᶜ := by
  ext n
  simp only [FF, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
  constructor
  · intro h; exact ⟨fun j hj => h j (by omega), h J (by omega)⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    exacts [h1 j h, h2]

lemma FF_main (k0 : ℕ) (hk : 5 ≤ k0) : ∀ J : ℕ,
    Per (FF k0 J) (∏ p ∈ PB 0 (mprev k0 J), p) ∧
    pd (FF k0 J) (∏ p ∈ PB 0 (mprev k0 J), p) ≤ (1 - (1 / 50 : ℝ) ^ 4 / 2) ^ J := by
  intro J
  induction J with
  | zero =>
    have hU : FF k0 0 = Set.univ := by ext n; simp [FF]
    have hP : PB 0 (mprev k0 0) = ∅ := by
      ext p; simp only [mem_PB, mprev, Finset.notMem_empty, iff_false]; omega
    rw [hU, hP, Finset.prod_empty]
    exact ⟨fun n => by simp, by simp [pd, cnt]⟩
  | succ J ih =>
    have hRb : ∀ p ∈ Rb k0 J, p.Prime := fun p hp => PB_prime hp
    have hRp : ∀ p ∈ Rp k0 J, p.Prime := fun p hp => PB_prime hp
    have h0 : ∀ p ∈ PB 0 (mprev k0 J), p.Prime := fun p hp => PB_prime hp
    have hPeq : ∏ p ∈ PB 0 (mprev k0 (J + 1)), p =
        (∏ p ∈ PB 0 (mprev k0 J), p) * ((∏ p ∈ Rb k0 J, p) * ∏ p ∈ Rp k0 J, p) := by
      rw [mprev_succ, PB_union (Nat.zero_le _) (ll_le_mm k0 J),
        Finset.prod_union (PB_disjoint _ _ _),
        PB_union (Nat.zero_le _) (mprev_le_ll k0 J), Finset.prod_union (PB_disjoint _ _ _)]
      unfold Rb Rp; ring
    have hcop : Nat.Coprime (∏ p ∈ PB 0 (mprev k0 J), p)
        ((∏ p ∈ Rb k0 J, p) * ∏ p ∈ Rp k0 J, p) :=
      Nat.Coprime.mul_right (coprime_prod h0 hRb (PB_disjoint' (mprev_le_ll k0 J)))
        (coprime_prod h0 hRp (PB_disjoint _ _ _))
    have hQpos : 0 < (∏ p ∈ Rb k0 J, p) * ∏ p ∈ Rp k0 J, p :=
      Nat.mul_pos (prod_pos_of_primes _ hRb) (prod_pos_of_primes _ hRp)
    rw [FF_succ, hPeq]
    refine ⟨ih.1.inter (per_succ k0 J).compl, ?_⟩
    rw [ih.1.pd_inter (per_succ k0 J).compl (prod_pos_of_primes _ h0) hQpos hcop,
      pd_compl hQpos, pow_succ]
    have hs := pd_succ k0 J hk
    have hc0 : (0 : ℝ) ≤ 1 - (1 / 50 : ℝ) ^ 4 / 2 := by norm_num
    exact mul_le_mul ih.2 (by linarith) (by
      have := pd_compl (Y := succS k0 J) hQpos
      linarith [pd_nonneg (succS k0 J)ᶜ ((∏ p ∈ Rb k0 J, p) * ∏ p ∈ Rp k0 J, p)])
      (pow_nonneg hc0 J)
/-! ## A successful scale places `φ(n)/n` in a short interval -/

lemma QK_eq_PB (K : ℕ) : QK K = PB 0 K := by
  ext p; simp only [QK, mem_PB, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, by omega⟩, h2⟩
  · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨by omega, h3⟩

lemma status_union (S T : Finset ℕ) (n : ℕ) :
    status (S ∪ T) n = status S n ∪ status T n := by
  unfold status; exact Finset.filter_union _ _ _

lemma g_le_one (D : Finset ℕ) : g D ≤ 1 :=
  Finset.prod_le_one (fun p _ => one_sub_nonneg' p) (fun p _ => by
    have : 0 ≤ 1 / (p : ℝ) := by positivity
    linarith)

/-- The statuses with a small product at scale `j`. -/
def DD (k0 j : ℕ) : Finset (Finset ℕ) :=
  (PB 0 (ll k0 j)).powerset.filter (fun D => ∏ p ∈ D, p ≤ 4 ^ mprev k0 j * ll k0 j ^ 8)

lemma mem_DD {k0 j : ℕ} {D : Finset ℕ} :
    D ∈ DD k0 j ↔ D ⊆ PB 0 (ll k0 j) ∧ ∏ p ∈ D, p ≤ 4 ^ mprev k0 j * ll k0 j ^ 8 := by
  unfold DD; rw [Finset.mem_filter, Finset.mem_powerset]

lemma card_DD (k0 j : ℕ) : (DD k0 j).card ≤ 4 ^ mprev k0 j * ll k0 j ^ 8 + 1 := by
  rw [← Finset.card_range (4 ^ mprev k0 j * ll k0 j ^ 8 + 1)]
  apply Finset.card_le_card_of_injOn (fun D => ∏ p ∈ D, p)
  · intro D hD
    have := (mem_DD.1 (Finset.mem_coe.1 hD)).2
    exact Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le this))
  · intro D1 h1 D2 h2 h
    have p1 : ∀ p ∈ D1, p.Prime := fun p hp => PB_prime ((mem_DD.1 (Finset.mem_coe.1 h1)).1 hp)
    have p2 : ∀ p ∈ D2, p.Prime := fun p hp => PB_prime ((mem_DD.1 (Finset.mem_coe.1 h2)).1 hp)
    have h' : ∏ p ∈ D1, p = ∏ p ∈ D2, p := h
    rw [← Nat.primeFactors_prod p1, ← Nat.primeFactors_prod p2, h']

lemma succ_covers (k0 j n : ℕ) (hn : 2 ≤ n) (hs : n ∈ succS k0 j) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : hK (mm k0 j) n ≤ δ) :
    ∃ D ∈ DD k0 j, max 0 (g D - δ) ≤ (Nat.totient n : ℝ) / n ∧
      (Nat.totient n : ℝ) / n < min 1 (g D + δ) := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hA : status (PB (ll k0 j) (mm k0 j)) n = ∅ := hs.1
  have hB : ∏ p ∈ status (Rp k0 j) n, p ≤ ll k0 j ^ 8 := hs.2
  have hst : status (QK (mm k0 j)) n = status (PB 0 (ll k0 j)) n := by
    rw [QK_eq_PB, PB_union (Nat.zero_le _) (ll_le_mm k0 j), status_union, hA,
      Finset.union_empty]
  have hphi := phi_split hn0 (mm k0 j)
  rw [hst] at hphi
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ mm k0 j),
      (1 - 1 / (p : ℝ)) := ⟨_, rfl⟩
  rw [← ht] at hphi
  have ht1 : t ≤ 1 := by
    rw [ht]
    exact Finset.prod_le_one (fun p _ => one_sub_nonneg' p) (fun p _ => by
      have : 0 ≤ 1 / (p : ℝ) := by positivity
      linarith)
  have ht0 : 1 - δ ≤ t := by
    have := prod_ge (n.primeFactors.filter (fun p => ¬ p ≤ mm k0 j))
    unfold hK at hδ
    rw [ht]; linarith
  have ht0' : 0 ≤ t := by
    rw [ht]; exact Finset.prod_nonneg fun p _ => one_sub_nonneg' p
  have hr : (Nat.totient n : ℝ) / n = g (status (PB 0 (ll k0 j)) n) * t := by
    rw [hphi]; field_simp
  have hg0 := g_nonneg (status (PB 0 (ll k0 j)) n)
  have hg1 := g_le_one (status (PB 0 (ll k0 j)) n)
  have hlt1 : (Nat.totient n : ℝ) / n < 1 := by
    rw [div_lt_one hnpos]; exact_mod_cast Nat.totient_lt n (by omega)
  refine ⟨status (PB 0 (ll k0 j)) n, ?_, ?_, ?_⟩
  · rw [mem_DD]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    have hsplit : status (PB 0 (ll k0 j)) n =
        status (PB 0 (mprev k0 j)) n ∪ status (Rp k0 j) n := by
      rw [PB_union (Nat.zero_le _) (mprev_le_ll k0 j), status_union]; rfl
    have hdisj : Disjoint (status (PB 0 (mprev k0 j)) n) (status (Rp k0 j) n) :=
      Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
        (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (PB_disjoint _ _ _))
    rw [hsplit, Finset.prod_union hdisj]
    refine Nat.mul_le_mul ?_ hB
    refine le_trans ?_ (prod_PB_le 0 (mprev k0 j))
    exact Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
      (fun p hp _ => (PB_prime hp).one_lt.le)
  · rw [hr]
    apply max_le
    · exact mul_nonneg hg0 ht0'
    · nlinarith [mul_le_mul_of_nonneg_left ht0 hg0, mul_le_mul_of_nonneg_right hg1 hδ0.le]
  · rw [lt_min_iff]
    refine ⟨hlt1, ?_⟩
    rw [hr]
    have := mul_le_of_le_one_right hg0 ht1
    linarith

/-! ## Final count -/

lemma cnt_iUnion_le (S : ℕ → Set ℕ) (J N : ℕ) :
    cnt (⋃ j ∈ Finset.range J, S j) N ≤ ∑ j ∈ Finset.range J, cnt (S j) N := by
  induction J with
  | zero => simp [cnt]
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have : (⋃ j ∈ Finset.range (J + 1), S j) = (⋃ j ∈ Finset.range J, S j) ∪ S J := by
      ext n
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_union, exists_prop]
      constructor
      · rintro ⟨j, hj, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h' | rfl
        exacts [Or.inl ⟨j, h', h⟩, Or.inr h]
      · rintro (⟨j, hj, h⟩ | h)
        exacts [⟨j, by omega, h⟩, ⟨J, by omega, h⟩]
    rw [this]
    exact (cnt_union_le _ _ N).trans (by omega)

lemma ncard_eq_cnt (S : Set ℕ) (N : ℕ) : ({n | n < N ∧ n ∈ S}).ncard = cnt S N := by
  unfold cnt
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n; simp

lemma sum_image_le' {α β : Type*} [DecidableEq β] (s : Finset α) (h : α → β) (f : β → ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f (h x)) : ∑ y ∈ s.image h, f y ≤ ∑ x ∈ s, f (h x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ih' := ih fun x hx => hf x (Finset.mem_insert_of_mem hx)
    have hfa := hf a (Finset.mem_insert_self a s)
    rw [Finset.image_insert, Finset.sum_insert ha]
    by_cases hmem : h a ∈ s.image h
    · rw [Finset.insert_eq_of_mem hmem]; linarith
    · rw [Finset.sum_insert hmem]; linarith
lemma cnt_single_le (a N : ℕ) : cnt {a} N ≤ 1 := by
  unfold cnt
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_filter, Set.mem_singleton_iff] at hx hy
  rw [hx.2, hy.2]

/-- The arithmetic covering statement: for every `ε`, finitely many half-open intervals of total
length at most `ε` contain `φ(n)/n` for all but `ε N` of the `n < N`. -/
theorem covering : ∀ ε : ℝ, 0 < ε → ∃ I : Finset (ℝ × ℝ),
    (∀ p ∈ I, 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1) ∧ ∑ p ∈ I, (p.2 - p.1) ≤ ε ∧
    ∃ N0 : ℕ, ∀ N ≥ N0,
      (({n : ℕ | n < N ∧ ¬ ∃ p ∈ I, p.1 ≤ (Nat.totient n : ℝ) / n ∧
        (Nat.totient n : ℝ) / n < p.2}).ncard : ℝ) ≤ ε * N := by
  intro ε hε
  have hc0 : (0 : ℝ) ≤ 1 - (1 / 50 : ℝ) ^ 4 / 2 := by norm_num
  have hc1 : 1 - (1 / 50 : ℝ) ^ 4 / 2 < 1 := by norm_num
  obtain ⟨J0, hJ0⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 3 by positivity) hc1
  obtain ⟨J, hJ, hJpos⟩ : ∃ J : ℕ, (1 - (1 / 50 : ℝ) ^ 4 / 2) ^ J < ε / 3 ∧ 0 < J := by
    refine ⟨J0 + 1, ?_, Nat.succ_pos _⟩
    rw [pow_succ]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (pow_nonneg hc0 _) hc1.le) hJ0
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJpos
  have hJne : (J : ℝ) ≠ 0 := hJr.ne'
  obtain ⟨k1, hk1⟩ := pow_unbounded_of_one_lt (24 * (J : ℝ) ^ 2 / ε ^ 2)
    (by norm_num : (1 : ℝ) < 2)
  obtain ⟨k0, hk0⟩ : ∃ k0, k0 = max 5 k1 := ⟨_, rfl⟩
  have hk5 : 5 ≤ k0 := hk0 ▸ le_max_left _ _
  have hk0' : 24 * (J : ℝ) ^ 2 / ε ^ 2 < 2 ^ k0 :=
    hk1.trans_le (pow_le_pow_right₀ (by norm_num) (hk0 ▸ le_max_right _ _))
  -- the sizes `X j` of the families and the widths `δ j`
  obtain ⟨X, hX⟩ : ∃ X : ℕ → ℝ, ∀ j, X j = ((4 ^ mprev k0 j * ll k0 j ^ 8 : ℕ) : ℝ) + 1 :=
    ⟨_, fun _ => rfl⟩
  have hXpos : ∀ j, 0 < X j := fun j => by rw [hX]; positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℝ, ∀ j, δ j = ε / (4 * J * X j) := ⟨_, fun _ => rfl⟩
  have hδpos : ∀ j, 0 < δ j := fun j => by
    rw [hδ]; have := hXpos j; positivity
  have hl1 : ∀ j, 1 ≤ ll k0 j := fun j => by unfold ll; exact Nat.one_le_two_pow
  have hLpos : ∀ j, (0 : ℝ) < (ll k0 j : ℝ) := fun j => by exact_mod_cast hl1 j
  have hL : ∀ j, 24 * (J : ℝ) ^ 2 < ε ^ 2 * (ll k0 j : ℝ) := by
    intro j
    have h1 : (2 : ℝ) ^ k0 ≤ (ll k0 j : ℝ) := by exact_mod_cast ll_ge k0 j
    have h2 := (div_lt_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)).1 hk0'
    nlinarith [mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ ε ^ 2)]
  have hXle : ∀ j, X j ≤ 2 * (ll k0 j : ℝ) ^ 9 := by
    intro j
    have h1 : 4 ^ mprev k0 j * ll k0 j ^ 8 ≤ ll k0 j ^ 9 :=
      calc 4 ^ mprev k0 j * ll k0 j ^ 8 ≤ ll k0 j * ll k0 j ^ 8 :=
            Nat.mul_le_mul_right _ (four_pow_mprev_le k0 j)
        _ = ll k0 j ^ 9 := by ring
    have h2 : 1 ≤ ll k0 j ^ 9 := Nat.one_le_pow _ _ (hl1 j)
    have h3 : 4 ^ mprev k0 j * ll k0 j ^ 8 + 1 ≤ 2 * ll k0 j ^ 9 := by omega
    rw [hX]
    exact_mod_cast h3
  -- the intervals
  obtain ⟨I, hI⟩ : ∃ I : Finset (ℝ × ℝ), I = ((Finset.range J).sigma (fun j => DD k0 j)).image
      (fun x => (max 0 (g x.2 - δ x.1), min 1 (g x.2 + δ x.1))) := ⟨_, rfl⟩
  have hImem : ∀ p ∈ I, ∃ j D, j < J ∧ D ∈ DD k0 j ∧
      p = (max 0 (g D - δ j), min 1 (g D + δ j)) := by
    intro p hp
    rw [hI, Finset.mem_image] at hp
    obtain ⟨⟨j, D⟩, hx, rfl⟩ := hp
    rw [Finset.mem_sigma] at hx
    exact ⟨j, D, Finset.mem_range.1 hx.1, hx.2, rfl⟩
  have hord : ∀ j D, max 0 (g D - δ j) ≤ min 1 (g D + δ j) := by
    intro j D
    have := hδpos j; have := g_nonneg D; have := g_le_one D
    exact le_min (max_le zero_le_one (by linarith)) (max_le (by linarith) (by linarith))
  refine ⟨I, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨j, D, -, -, rfl⟩ := hImem p hp
    exact ⟨le_max_left _ _, hord j D, min_le_left _ _⟩
  · rw [hI]
    refine (sum_image_le' _ _ (fun p : ℝ × ℝ => p.2 - p.1) ?_).trans ?_
    · intro x _
      exact sub_nonneg.2 (hord x.1 x.2)
    · rw [Finset.sum_sigma]
      have hterm : ∀ j ∈ Finset.range J,
          ∑ D ∈ DD k0 j, (min 1 (g D + δ j) - max 0 (g D - δ j)) ≤ ε / (2 * J) := by
        intro j _
        have h1 : ∀ D ∈ DD k0 j, min 1 (g D + δ j) - max 0 (g D - δ j) ≤ 2 * δ j := by
          intro D _
          have := min_le_right 1 (g D + δ j)
          have := le_max_right 0 (g D - δ j)
          linarith
        refine (Finset.sum_le_sum h1).trans ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        have hc : ((DD k0 j).card : ℝ) ≤ X j := by
          rw [hX]; exact_mod_cast card_DD k0 j
        have hXj := hXpos j
        calc ((DD k0 j).card : ℝ) * (2 * δ j) ≤ X j * (2 * δ j) :=
              mul_le_mul_of_nonneg_right hc (by have := hδpos j; linarith)
          _ = ε / (2 * J) := by rw [hδ]; field_simp; ring
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have : (J : ℝ) * (ε / (2 * J)) = ε / 2 := by field_simp
      linarith
  · obtain ⟨Bad, hBad⟩ : ∃ Bad : Set ℕ, Bad = {n : ℕ | ¬ ∃ p ∈ I,
        p.1 ≤ (Nat.totient n : ℝ) / n ∧ (Nat.totient n : ℝ) / n < p.2} := ⟨_, rfl⟩
    have hsub : Bad ⊆ ((({0} : Set ℕ) ∪ {1}) ∪ FF k0 J) ∪
        ⋃ j ∈ Finset.range J, {n | δ j < hK (mm k0 j) n} := by
      intro n hn
      rw [hBad] at hn
      by_cases h2 : n < 2
      · left; left
        rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      by_cases hF : n ∈ FF k0 J
      · exact Or.inl (Or.inr hF)
      right
      have hF' : ∃ j, j < J ∧ n ∈ succS k0 j := by
        by_contra hcon
        exact hF fun j hj hs => hcon ⟨j, hj, hs⟩
      obtain ⟨j, hj, hs⟩ := hF'
      simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
      refine ⟨j, hj, ?_⟩
      by_contra hb
      obtain ⟨D, hD, h1, h2'⟩ :=
        succ_covers k0 j n (by omega) hs (hδpos j) (le_of_not_gt hb)
      apply hn
      refine ⟨(max 0 (g D - δ j), min 1 (g D + δ j)), ?_, h1, h2'⟩
      rw [hI, Finset.mem_image]
      exact ⟨⟨j, D⟩, Finset.mem_sigma.2 ⟨Finset.mem_range.2 hj, hD⟩, rfl⟩
    have hcnt : ∀ N, cnt Bad N ≤ 2 + cnt (FF k0 J) N +
        ∑ j ∈ Finset.range J, cnt {n | δ j < hK (mm k0 j) n} N := by
      intro N
      have h1 := cnt_mono hsub N
      have h2 := cnt_union_le ((({0} : Set ℕ) ∪ {1}) ∪ FF k0 J)
        (⋃ j ∈ Finset.range J, {n | δ j < hK (mm k0 j) n}) N
      have h3 := cnt_union_le (({0} : Set ℕ) ∪ {1}) (FF k0 J) N
      have h4 := cnt_union_le ({0} : Set ℕ) {1} N
      have h5 := cnt_single_le 0 N
      have h6 := cnt_single_le 1 N
      have h7 := cnt_iUnion_le (fun j => {n | δ j < hK (mm k0 j) n}) J N
      omega
    have htail : ∀ j, ∀ N : ℕ,
        (cnt {n | δ j < hK (mm k0 j) n} N : ℝ) ≤ N * (ε / (3 * J)) := by
      intro j N
      have hm1 : 1 ≤ mm k0 j := by unfold mm; exact Nat.one_le_two_pow
      refine (cnt_bad (mm k0 j) N hm1 (hδpos j)).trans ?_
      have hmm : ((mm k0 j : ℕ) : ℝ) = (ll k0 j : ℝ) ^ 10 := by rw [mm_eq]; push_cast; ring
      have hLj := hLpos j
      have hXj := hXpos j
      have key : 1 / ((mm k0 j : ℝ) * δ j) ≤ ε / (3 * J) := by
        have e : ((mm k0 j : ℕ) : ℝ) * δ j = ((ll k0 j : ℝ) ^ 10 * ε) / (4 * J * X j) := by
          rw [hmm, hδ]; ring
        rw [e, one_div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 : 12 * (J : ℝ) ^ 2 * X j ≤ 12 * (J : ℝ) ^ 2 * (2 * (ll k0 j : ℝ) ^ 9) :=
          mul_le_mul_of_nonneg_left (hXle j) (by positivity)
        have h2 : 24 * (J : ℝ) ^ 2 * (ll k0 j : ℝ) ^ 9 ≤
            ε ^ 2 * (ll k0 j : ℝ) * (ll k0 j : ℝ) ^ 9 :=
          mul_le_mul_of_nonneg_right (hL j).le (by positivity)
        nlinarith [h1, h2]
      calc (N : ℝ) / ((mm k0 j : ℝ) * δ j) = N * (1 / ((mm k0 j : ℝ) * δ j)) := by ring
        _ ≤ N * (ε / (3 * J)) := mul_le_mul_of_nonneg_left key (Nat.cast_nonneg N)
    obtain ⟨hper, hpd⟩ := FF_main k0 hk5 J
    have hP : 0 < ∏ p ∈ PB 0 (mprev k0 J), p :=
      prod_pos_of_primes _ fun p hp => PB_prime hp
    have hdens := (hasDensity_iff _ _).1 (hper.hasDensity hP)
    have hev := (tendsto_order.1 hdens).2 (ε / 2) (by unfold pd at hpd; linarith)
    obtain ⟨N1, hN1⟩ := exists_nat_gt (12 / ε)
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hev.and (eventually_ge_atTop (N1 + 1)))
    refine ⟨N0, fun N hN => ?_⟩
    obtain ⟨hF, hNge⟩ := hN0 N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hN12 : 12 / ε < N := hN1.trans (by exact_mod_cast (by omega : N1 < N))
    have e : ({n : ℕ | n < N ∧ ¬ ∃ p ∈ I, p.1 ≤ (Nat.totient n : ℝ) / n ∧
        (Nat.totient n : ℝ) / n < p.2}).ncard = cnt Bad N := by
      rw [hBad]; exact ncard_eq_cnt _ N
    rw [e]
    have h1 : (cnt Bad N : ℝ) ≤ 2 + cnt (FF k0 J) N +
        ∑ j ∈ Finset.range J, (cnt {n | δ j < hK (mm k0 j) n} N : ℝ) := by
      exact_mod_cast hcnt N
    have h2 : (cnt (FF k0 J) N : ℝ) ≤ ε / 2 * N := by
      rw [div_lt_iff₀ hNpos] at hF; exact hF.le
    have h3 : ∑ j ∈ Finset.range J, (cnt {n | δ j < hK (mm k0 j) n} N : ℝ) ≤ ε / 3 * N := by
      refine (Finset.sum_le_sum fun j _ => htail j N).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have : (J : ℝ) * (N * (ε / (3 * J))) = ε / 3 * N := by field_simp
      linarith
    have h4 : (2 : ℝ) ≤ ε / 6 * N := by
      rw [div_lt_iff₀ hε] at hN12; linarith
    linarith

end OMA50

open Filter Set Topology MeasureTheory

namespace OMA50s

open scoped Classical

/-- Number of `n < N` with `r n ∈ A`. -/
noncomputable def cN (r : ℕ → ℝ) (A : Set ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => r n ∈ A)).card

/-- The frequency of `r n ∈ A` converges to `μ A`. -/
def Conv (μ : Measure ℝ) (r : ℕ → ℝ) (A : Set ℝ) : Prop :=
  MeasurableSet A ∧ Tendsto (fun N : ℕ => (cN r A N : ℝ) / N) atTop (𝓝 (μ A).toReal)

lemma cN_union {r : ℕ → ℝ} {A B : Set ℝ} (h : Disjoint A B) (N : ℕ) :
    cN r (A ∪ B) N = cN r A N + cN r B N := by
  unfold cN
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext n
    simp only [Finset.mem_filter, Finset.mem_union, Set.mem_union]; tauto
  · rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact Set.disjoint_left.1 h h1.2 h2.2

lemma Conv.empty {μ : Measure ℝ} {r : ℕ → ℝ} : Conv μ r ∅ :=
  ⟨MeasurableSet.empty, by simp [cN]⟩

lemma Conv.union {μ : Measure ℝ} [IsFiniteMeasure μ] {r : ℕ → ℝ} {A B : Set ℝ}
    (hA : Conv μ r A) (hB : Conv μ r B) (h : Disjoint A B) : Conv μ r (A ∪ B) := by
  refine ⟨hA.1.union hB.1, ?_⟩
  rw [measure_union h hB.1, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  refine (hA.2.add hB.2).congr fun N => ?_
  rw [cN_union h]; push_cast; ring

lemma Conv.diff {μ : Measure ℝ} [IsFiniteMeasure μ] {r : ℕ → ℝ} {A B : Set ℝ}
    (hA : Conv μ r A) (hB : Conv μ r B) (h : A ⊆ B) : Conv μ r (B \ A) := by
  refine ⟨hB.1.diff hA.1, ?_⟩
  have e : ∀ N, (cN r (B \ A) N : ℝ) = cN r B N - cN r A N := by
    intro N
    have := cN_union (r := r) (disjoint_sdiff_self_right : Disjoint A (B \ A)) N
    rw [Set.union_sdiff_cancel h] at this
    rw [this]; push_cast; ring
  have hm : (μ (B \ A)).toReal = (μ B).toReal - (μ A).toReal := by
    rw [measure_sdiff h hA.1.nullMeasurableSet (measure_ne_top _ _),
      ENNReal.toReal_sub_of_le (measure_mono h) (measure_ne_top _ _)]
  rw [hm]
  refine (hB.2.sub hA.2).congr fun N => ?_
  rw [e]; ring

/-- Union of the half-open intervals of a finite family. -/
def U (I : Finset (ℝ × ℝ)) : Set ℝ := ⋃ p ∈ I, Ico p.1 p.2

lemma mem_U {I : Finset (ℝ × ℝ)} {x : ℝ} : x ∈ U I ↔ ∃ p ∈ I, p.1 ≤ x ∧ x < p.2 := by
  simp only [U, Set.mem_iUnion, Set.mem_Ico, exists_prop]

lemma conv_U {μ : Measure ℝ} [IsFiniteMeasure μ] {r : ℕ → ℝ}
    (hbase : ∀ a b : ℝ, 0 ≤ a → b ≤ 1 → Conv μ r (Ico a b)) :
    ∀ n : ℕ, ∀ I : Finset (ℝ × ℝ), I.card ≤ n → (∀ p ∈ I, 0 ≤ p.1 ∧ p.2 ≤ 1) →
      Conv μ r (U I) := by
  intro n
  induction n with
  | zero =>
    intro I hI _
    have : I = ∅ := Finset.card_eq_zero.1 (by omega)
    subst this
    have : U (∅ : Finset (ℝ × ℝ)) = ∅ := by ext x; simp [mem_U]
    rw [this]; exact Conv.empty
  | succ n ih =>
    intro I hI hb
    rcases I.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
    · have : U (∅ : Finset (ℝ × ℝ)) = ∅ := by ext x; simp [mem_U]
      rw [this]; exact Conv.empty
    have hI' : (I.erase q).card ≤ n := by rw [Finset.card_erase_of_mem hq]; omega
    have hb' : ∀ p ∈ I.erase q, 0 ≤ p.1 ∧ p.2 ≤ 1 :=
      fun p hp => hb p (Finset.mem_of_mem_erase hp)
    have hE := ih (I.erase q) hI' hb'
    have hI'' : ((I.erase q).image (fun p => (max p.1 q.1, min p.2 q.2))).card ≤ n :=
      Finset.card_image_le.trans hI'
    have hb'' : ∀ p ∈ (I.erase q).image (fun p => (max p.1 q.1, min p.2 q.2)),
        0 ≤ p.1 ∧ p.2 ≤ 1 := by
      intro p hp
      obtain ⟨p0, hp0, rfl⟩ := Finset.mem_image.1 hp
      exact ⟨le_max_of_le_left (hb' p0 hp0).1, min_le_of_left_le (hb' p0 hp0).2⟩
    have hint : U ((I.erase q).image (fun p => (max p.1 q.1, min p.2 q.2))) =
        U (I.erase q) ∩ Ico q.1 q.2 := by
      ext x
      simp only [mem_U, Finset.mem_image, Set.mem_inter_iff, Set.mem_Ico]
      constructor
      · rintro ⟨p, ⟨p0, hp0, rfl⟩, h1, h2⟩
        exact ⟨⟨p0, hp0, (le_max_left _ _).trans h1, h2.trans_le (min_le_left _ _)⟩,
          (le_max_right _ _).trans h1, h2.trans_le (min_le_right _ _)⟩
      · rintro ⟨⟨p0, hp0, h1, h2⟩, h3, h4⟩
        exact ⟨_, ⟨p0, hp0, rfl⟩, max_le h1 h3, lt_min h2 h4⟩
    have hEJ := ih _ hI'' hb''
    have hJ := hbase q.1 q.2 (hb q hq).1 (hb q hq).2
    have hD : Conv μ r (Ico q.1 q.2 \ U ((I.erase q).image (fun p => (max p.1 q.1, min p.2 q.2)))) :=
      Conv.diff hEJ hJ (by rw [hint]; exact Set.inter_subset_right)
    have hU : U I = U (I.erase q) ∪
        (Ico q.1 q.2 \ U ((I.erase q).image (fun p => (max p.1 q.1, min p.2 q.2)))) := by
      rw [hint]; ext x
      simp only [mem_U, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_Ico]
      constructor
      · rintro ⟨p, hp, hx⟩
        by_cases hpq : p = q
        · subst hpq
          by_cases hx' : ∃ p' ∈ I.erase p, p'.1 ≤ x ∧ x < p'.2
          · exact Or.inl hx'
          · exact Or.inr ⟨hx, fun h => hx' h.1⟩
        · exact Or.inl ⟨p, Finset.mem_erase.2 ⟨hpq, hp⟩, hx⟩
      · rintro (⟨p, hp, hx⟩ | ⟨hx, _⟩)
        · exact ⟨p, Finset.mem_of_mem_erase hp, hx⟩
        · exact ⟨q, hq, hx⟩
    rw [hU]
    refine hE.union hD ?_
    rw [hint]
    exact Set.disjoint_left.2 fun x hx h => h.2 ⟨hx, h.1⟩

/-- A measure that is, for every `k`, carried up to `2^-k` by a set of Lebesgue measure at most
`2^-k`, is singular with respect to Lebesgue measure. -/
lemma singular_of_cover (ν : Measure ℝ)
    (h : ∀ k : ℕ, ∃ E : Set ℝ, volume E ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) ∧
      ν Eᶜ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) :
    ν ⟂ₘ (volume : Measure ℝ) := by
  choose E hEv hEν using h
  have hsum : ∑' k, volume (E k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hEv)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) summable_geometric_two]
    exact ENNReal.ofReal_ne_top
  have h0 : volume (limsup E atTop) = 0 := measure_limsup_atTop_eq_zero hsum
  have h1 : ν (limsup E atTop)ᶜ = 0 := by
    rw [limsup_eq_iInf_iSup_of_nat]
    simp only [Set.iInf_eq_iInter, Set.iSup_eq_iUnion, Set.compl_iInter, Set.compl_iUnion]
    refine measure_iUnion_null fun n => ?_
    have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
      simpa using this
    refine le_antisymm (ge_of_tendsto hlim ?_) zero_le
    filter_upwards [eventually_ge_atTop n] with k hk
    refine (measure_mono ?_).trans (hEν k)
    intro x hx
    simp only [Set.mem_iInter] at hx
    exact hx k hk
  exact Measure.MutuallySingular.mk h1 h0 (by simp)

/-- If the Stieltjes measure of `sF`, restricted to `[0, 1)`, is singular, then any function
agreeing with `sF` on `[0, 1]` has derivative zero almost everywhere there. -/
lemma deriv_zero_of_singular (sF : StieltjesFunction ℝ) (f : ℝ → ℝ)
    (hfF : ∀ x ∈ Icc (0 : ℝ) 1, f x = sF x)
    (hs : (sF.measure.restrict (Ico 0 1)) ⟂ₘ (volume : Measure ℝ)) :
    ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), derivWithin f (Icc 0 1) x = 0 := by
  have h1 := (Measure.rnDeriv_eq_zero _ _).2 hs
  have h2 := Measure.rnDeriv_restrict sF.measure (volume : Measure ℝ)
    (measurableSet_Ico (a := (0 : ℝ)) (b := 1))
  have h3 := sF.ae_hasDerivAt
  rw [ae_restrict_iff' measurableSet_Icc]
  have n0 : ∀ᵐ x : ℝ, x ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.2 (Real.volume_singleton (a := (0 : ℝ)))] with x hx
    simpa using hx
  have n1 : ∀ᵐ x : ℝ, x ≠ 1 := by
    filter_upwards [compl_mem_ae_iff.2 (Real.volume_singleton (a := (1 : ℝ)))] with x hx
    simpa using hx
  filter_upwards [h1, h2, h3, n0, n1] with x hx1 hx2 hx3 hx0 hx1' hxI
  have hxo : x ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hxI.1 (Ne.symm hx0), lt_of_le_of_ne hxI.2 hx1'⟩
  have hr : sF.measure.rnDeriv volume x = 0 := by
    have := hx2.symm.trans hx1
    rw [Set.indicator_of_mem (Ioo_subset_Ico_self hxo)] at this
    simpa using this
  rw [hr, ENNReal.toReal_zero] at hx3
  have heq : f =ᶠ[𝓝 x] sF := by
    filter_upwards [Icc_mem_nhds hxo.1 hxo.2] with y hy using hfF y hy
  have hd : HasDerivAt f 0 x := hx3.congr_of_eventuallyEq heq
  exact hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc_zero_one x hxI)

/-! ## Densities of sets of naturals -/

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

lemma cnt_mono {S T : Set ℕ} (h : S ⊆ T) (n : ℕ) : cnt S n ≤ cnt T n := by
  unfold cnt
  exact Finset.card_le_card (fun x hx => by
    simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, h hx.2⟩)

lemma cnt_split (S X : Set ℕ) (n : ℕ) : cnt S n = cnt (S ∩ X) n + cnt (S \ X) n := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_union, Set.mem_inter_iff,
      Set.mem_sdiff]; tauto
  · rw [Finset.disjoint_left]; intro x h1 h2
    simp only [Finset.mem_filter, Set.mem_inter_iff, Set.mem_sdiff] at h1 h2; tauto

lemma HasDensity.diff {S X : Set ℕ} {a b : ℝ} (ha : S.HasDensity a)
    (hb : (S ∩ X).HasDensity b) : (S \ X).HasDensity (a - b) := by
  rw [hasDensity_iff] at *
  refine (ha.sub hb).congr (fun n => ?_)
  rw [cnt_split S X n]; push_cast; ring

lemma mono_bd {c1 c2 d1 d2 : ℝ} (h12 : c1 ≤ c2)
    (h1 : {n : ℕ | (Nat.totient n : ℝ) < c1 * n}.HasDensity d1)
    (h2 : {n : ℕ | (Nat.totient n : ℝ) < c2 * n}.HasDensity d2) : d1 ≤ d2 := by
  refine le_of_tendsto_of_tendsto ((hasDensity_iff _ _).1 h1) ((hasDensity_iff _ _).1 h2)
    (Eventually.of_forall fun N => ?_)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hsub : {n : ℕ | (Nat.totient n : ℝ) < c1 * n} ⊆
      {n : ℕ | (Nat.totient n : ℝ) < c2 * n} := by
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn ⊢
    exact lt_of_lt_of_le hn (mul_le_mul_of_nonneg_right h12 (Nat.cast_nonneg n))
  exact_mod_cast cnt_mono hsub N

/-! ## From densities to frequencies of `φ(n)/n` -/

/-- The ratio `φ(n)/n`. -/
noncomputable def rr (n : ℕ) : ℝ := (Nat.totient n : ℝ) / n

lemma freq_of_density {A : Set ℝ} {D : Set ℕ} {d : ℝ} (hD : D.HasDensity d)
    (key : ∀ n : ℕ, n ≠ 0 → (rr n ∈ A ↔ n ∈ D)) (h0 : 0 ∉ D) :
    Tendsto (fun N : ℕ => (cN rr A N : ℝ) / N) atTop (𝓝 d) := by
  rw [hasDensity_iff] at hD
  have hD' := hD.add tendsto_one_div_atTop_nhds_zero_nat
  rw [add_zero] at hD'
  have h1 : ∀ N, cnt D N ≤ cN rr A N := by
    intro N
    unfold cnt cN
    apply Finset.card_le_card
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    have hn0 : n ≠ 0 := by rintro rfl; exact h0 hn.2
    exact ⟨hn.1, (key n hn0).2 hn.2⟩
  have h2 : ∀ N, cN rr A N ≤ cnt D N + 1 := by
    intro N
    unfold cnt cN
    refine (Finset.card_le_card (t := insert 0 ((Finset.range N).filter (· ∈ D))) ?_).trans
      (Finset.card_insert_le _ _)
    intro n hn
    simp only [Finset.mem_filter] at hn
    by_cases hn0 : n = 0
    · simp [hn0]
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hn.1, (key n hn0).1 hn.2⟩)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hD hD' (fun N => ?_) (fun N => ?_)
  · have h : (cnt D N : ℝ) ≤ (cN rr A N : ℝ) := by exact_mod_cast h1 N
    exact div_le_div_of_nonneg_right h (Nat.cast_nonneg _)
  · have h : (cN rr A N : ℝ) ≤ (cnt D N : ℝ) + 1 := by exact_mod_cast h2 N
    show (cN rr A N : ℝ) / N ≤ (cnt D N : ℝ) / N + 1 / N
    rw [← add_div]
    exact div_le_div_of_nonneg_right h (Nat.cast_nonneg _)

lemma freq_Ico {a b fa fb : ℝ} (hab : a ≤ b)
    (ha : {n : ℕ | (Nat.totient n : ℝ) < a * n}.HasDensity fa)
    (hb : {n : ℕ | (Nat.totient n : ℝ) < b * n}.HasDensity fb) :
    Tendsto (fun N : ℕ => (cN rr (Ico a b) N : ℝ) / N) atTop (𝓝 (fb - fa)) := by
  have hsub : {n : ℕ | (Nat.totient n : ℝ) < a * n} ⊆
      {n : ℕ | (Nat.totient n : ℝ) < b * n} := by
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn ⊢
    exact lt_of_lt_of_le hn (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg n))
  have hd := HasDensity.diff hb (by rw [Set.inter_eq_right.2 hsub]; exact ha)
  refine freq_of_density hd (fun n hn => ?_) (by simp)
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  simp only [rr, Set.mem_Ico, Set.mem_sdiff, Set.mem_ofPred_eq, not_lt]
  rw [le_div_iff₀ hn', div_lt_iff₀ hn']
  tauto

/-! ## Assembly -/

/-- Clamp to `[0, 1]`. -/
noncomputable def clamp (x : ℝ) : ℝ := max 0 (min x 1)

lemma clamp_mem (x : ℝ) : clamp x ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

lemma clamp_of_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : clamp x = x := by
  unfold clamp; rw [min_eq_left hx.2, max_eq_right hx.1]

lemma clamp_mono : Monotone clamp := fun _ _ h => max_le_max le_rfl (min_le_min h le_rfl)

lemma clamp_cont : Continuous clamp := by unfold clamp; fun_prop

theorem analysis
    (hcov : ∀ ε : ℝ, 0 < ε → ∃ I : Finset (ℝ × ℝ),
      (∀ p ∈ I, 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1) ∧ ∑ p ∈ I, (p.2 - p.1) ≤ ε ∧
      ∃ N0 : ℕ, ∀ N ≥ N0,
        (({n : ℕ | n < N ∧ ¬ ∃ p ∈ I, p.1 ≤ (Nat.totient n : ℝ) / n ∧
          (Nat.totient n : ℝ) / n < p.2}).ncard : ℝ) ≤ ε * N)
    (f : ℝ → ℝ) (hf : Erdos50.IsDistributionOfPhiRatio f)
    (hcont : ContinuousOn f (Icc 0 1)) :
    ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), derivWithin f (Icc 0 1) x = 0 := by
  have hmono : ∀ c1 ∈ Icc (0 : ℝ) 1, ∀ c2 ∈ Icc (0 : ℝ) 1, c1 ≤ c2 → f c1 ≤ f c2 :=
    fun c1 hc1 c2 hc2 h => mono_bd h (hf c1 hc1) (hf c2 hc2)
  have hFc : Continuous (fun x => f (clamp x)) :=
    hcont.comp_continuous clamp_cont clamp_mem
  obtain ⟨sF, hsF⟩ : ∃ sF : StieltjesFunction ℝ, ∀ x, sF x = f (clamp x) :=
    ⟨{ toFun := fun x => f (clamp x)
       mono' := fun x y h => hmono _ (clamp_mem x) _ (clamp_mem y) (clamp_mono h)
       right_continuous' := fun x => hFc.continuousWithinAt }, fun x => rfl⟩
  have hsFc : Continuous (sF : ℝ → ℝ) := by
    have e : (sF : ℝ → ℝ) = fun x => f (clamp x) := funext hsF
    rw [e]; exact hFc
  have hfF : ∀ x ∈ Icc (0 : ℝ) 1, f x = sF x := fun x hx => by rw [hsF, clamp_of_mem hx]
  have hIco : ∀ a b : ℝ, sF.measure (Ico a b) = ENNReal.ofReal (sF b - sF a) := by
    intro a b
    rw [sF.measure_Ico]
    have e : ∀ x, Function.leftLim sF x = sF x := fun x =>
      (hsFc.continuousWithinAt (s := Iic x) (x := x)).leftLim_eq
    rw [e, e]
  have : IsFiniteMeasure (sF.measure.restrict (Ico 0 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, hIco]; exact ENNReal.ofReal_lt_top⟩
  have hbase : ∀ a b : ℝ, 0 ≤ a → b ≤ 1 →
      Conv (sF.measure.restrict (Ico 0 1)) rr (Ico a b) := by
    intro a b ha hb
    by_cases hab : a < b
    · have ha' : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.le.trans hb⟩
      have hb' : b ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hab.le, hb⟩
      refine ⟨measurableSet_Ico, ?_⟩
      rw [Measure.restrict_eq_self _ (Ico_subset_Ico ha hb), hIco, ← hfF a ha', ← hfF b hb',
        ENNReal.toReal_ofReal (sub_nonneg.2 (hmono a ha' b hb' hab.le))]
      exact freq_Ico hab.le (hf a ha') (hf b hb')
    · rw [Set.Ico_eq_empty hab]; exact Conv.empty
  apply deriv_zero_of_singular sF f hfF
  apply singular_of_cover
  intro k
  obtain ⟨I, hI, hsum, N0, hN⟩ := hcov ((1 / 2 : ℝ) ^ k) (by positivity)
  refine ⟨U I, ?_, ?_⟩
  · calc volume (U I) ≤ ∑ p ∈ I, volume (Ico p.1 p.2) := measure_biUnion_finset_le I _
      _ = ∑ p ∈ I, ENNReal.ofReal (p.2 - p.1) := by simp only [Real.volume_Ico]
      _ = ENNReal.ofReal (∑ p ∈ I, (p.2 - p.1)) :=
          (ENNReal.ofReal_sum_of_nonneg fun p hp => sub_nonneg.2 (hI p hp).2.1).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hsum
  · have hU : Conv (sF.measure.restrict (Ico 0 1)) rr (U I) :=
      conv_U hbase I.card I le_rfl fun p hp => ⟨(hI p hp).1, (hI p hp).2.2⟩
    have hsub : U I ⊆ Ico (0 : ℝ) 1 := by
      intro x hx
      obtain ⟨p, hp, h1, h2⟩ := mem_U.1 hx
      exact ⟨(hI p hp).1.trans h1, h2.trans_le (hI p hp).2.2⟩
    have hD := Conv.diff hU (hbase 0 1 le_rfl le_rfl) hsub
    have hle : ((sF.measure.restrict (Ico 0 1)) (Ico 0 1 \ U I)).toReal ≤ (1 / 2 : ℝ) ^ k := by
      refine le_of_tendsto hD.2 ?_
      filter_upwards [eventually_ge_atTop (max N0 1)] with N hN'
      have hN1 : 1 ≤ N := (le_max_right N0 1).trans hN'
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
      rw [div_le_iff₀ hNpos]
      refine le_trans ?_ (hN N ((le_max_left _ _).trans hN'))
      have : cN rr (Ico 0 1 \ U I) N ≤ ({n : ℕ | n < N ∧ ¬ ∃ p ∈ I,
          p.1 ≤ (Nat.totient n : ℝ) / n ∧ (Nat.totient n : ℝ) / n < p.2}).ncard := by
        unfold cN
        rw [← Set.ncard_coe_finset]
        apply Set.ncard_le_ncard
        · intro n hn
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, Set.mem_sdiff] at hn
          exact ⟨hn.1, fun h => hn.2.2 (mem_U.2 h)⟩
        · exact (Set.finite_Iio N).subset fun n hn => hn.1
      exact_mod_cast this
    calc (sF.measure.restrict (Ico 0 1)) (U I)ᶜ
        ≤ (sF.measure.restrict (Ico 0 1)) ((Ico 0 1 \ U I) ∪ (Ico 0 1)ᶜ) := measure_mono (by
          intro x hx
          by_cases h : x ∈ Ico (0 : ℝ) 1
          · exact Or.inl ⟨h, hx⟩
          · exact Or.inr h)
      _ ≤ (sF.measure.restrict (Ico 0 1)) (Ico 0 1 \ U I) +
          (sF.measure.restrict (Ico 0 1)) (Ico 0 1)ᶜ := measure_union_le _ _
      _ = (sF.measure.restrict (Ico 0 1)) (Ico 0 1 \ U I) := by
          rw [Measure.restrict_apply measurableSet_Ico.compl, Set.compl_inter_self,
            measure_empty, add_zero]
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
          rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
          exact ENNReal.ofReal_le_ofReal hle

end OMA50s

theorem OMA.solution : type_of% @Erdos50.erdos_50_singular := by
  intro f hf
  exact ⟨OMA50.cont f hf, OMA50s.analysis OMA50.covering f hf (OMA50.cont f hf)⟩
