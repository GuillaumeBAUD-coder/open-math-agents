import FormalConjectures.ErdosProblems.«470»

-- Problem: Erdős Problem 470 — weird pos density
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/470.lean:66 (declaration Erdos470.erdos_470.variants.weird_pos_density)
-- Credit: @mucoucah (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Topology

namespace OMA470

/-- The nondeficient numbers: positive `n` with `n ≤ s(n)` (abundant or perfect). -/
def ND : Set ℕ := {n : ℕ | 0 < n ∧ n ≤ ∑ d ∈ n.properDivisors, d}

/-- The pseudoperfect numbers. -/
def PP : Set ℕ := {n : ℕ | n.Pseudoperfect}

/-- Every pseudoperfect number is nondeficient. -/
lemma PP_subset_ND : PP ⊆ ND := by
  rintro n ⟨hpos, s, hs, hsum⟩
  refine ⟨hpos, ?_⟩
  calc n = ∑ i ∈ s, i := hsum.symm
    _ ≤ ∑ i ∈ n.properDivisors, i := Finset.sum_le_sum_of_subset hs

/-- Weird = nondeficient and not pseudoperfect (perfect numbers are pseudoperfect, so no
separate density-zero statement about perfect numbers is needed). -/
lemma weird_eq_diff : {n : ℕ | n.Weird} = ND \ PP := by
  ext n
  constructor
  · rintro ⟨ha, hp⟩
    exact ⟨⟨ha.pos, le_of_lt ha⟩, hp⟩
  · rintro ⟨⟨hpos, hle⟩, hp⟩
    refine ⟨?_, hp⟩
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd ⟨hpos, n.properDivisors, subset_rfl, h.symm⟩ hp

/-- Partial densities subtract along an inclusion. -/
lemma pd_diff (N P : Set ℕ) (hPN : P ⊆ N) (b : ℕ) :
    (N \ P).partialDensity Set.univ b
      = N.partialDensity Set.univ b - P.partialDensity Set.univ b := by
  have hfin : ∀ S : Set ℕ, ((S ∩ Set.univ) ∩ Set.Iio b).Finite := fun S =>
    (Set.finite_Iio b).subset Set.inter_subset_right
  have hsub : (P ∩ Set.univ) ∩ Set.Iio b ⊆ (N ∩ Set.univ) ∩ Set.Iio b := by
    intro x hx
    exact ⟨⟨hPN hx.1.1, trivial⟩, hx.2⟩
  have heq : ((N \ P) ∩ Set.univ) ∩ Set.Iio b
      = ((N ∩ Set.univ) ∩ Set.Iio b) \ ((P ∩ Set.univ) ∩ Set.Iio b) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_univ, and_true, Set.mem_Iio]
    tauto
  have hcard := Set.ncard_sdiff hsub (hfin P)
  have hle := Set.ncard_le_ncard hsub (hfin N)
  show ((((N \ P) ∩ Set.univ) ∩ Set.Iio b).ncard : ℝ) / ((Set.univ ∩ Set.Iio b).ncard : ℝ)
      = (((N ∩ Set.univ) ∩ Set.Iio b).ncard : ℝ) / ((Set.univ ∩ Set.Iio b).ncard : ℝ)
        - (((P ∩ Set.univ) ∩ Set.Iio b).ncard : ℝ) / ((Set.univ ∩ Set.Iio b).ncard : ℝ)
  rw [heq, hcard, Nat.cast_sub hle, sub_div]

/-- Densities subtract along an inclusion. -/
lemma hasDensity_diff {N P : Set ℕ} (hPN : P ⊆ N) {α β : ℝ}
    (hN : N.HasDensity α) (hP : P.HasDensity β) : (N \ P).HasDensity (α - β) := by
  have h := Filter.Tendsto.sub hN hP
  exact h.congr (fun b => (pd_diff N P hPN b).symm)

/-- A set with a density and an eventual positive lower bound on its partial densities has
positive density. -/
lemma pos_of_lower {W : Set ℕ} {γ c : ℝ} (hc : 0 < c) (hW : W.HasDensity γ)
    (hlow : ∀ᶠ b : ℕ in atTop, c ≤ W.partialDensity Set.univ b) : W.HasPosDensity :=
  ⟨γ, lt_of_lt_of_le hc (ge_of_tendsto hW hlow), hW⟩

/-- The reduction: the target follows from the existence of the densities of the nondeficient
and of the pseudoperfect numbers, plus a positive lower bound for the weird numbers. -/
theorem glue
    (h1 : ∃ α : ℝ, ND.HasDensity α)
    (h2 : ∃ β : ℝ, PP.HasDensity β)
    (h3 : ∃ c : ℝ, 0 < c ∧
      ∀ᶠ b : ℕ in atTop, c ≤ {n : ℕ | n.Weird}.partialDensity Set.univ b) :
    {n : ℕ | n.Weird}.HasPosDensity := by
  obtain ⟨α, hα⟩ := h1
  obtain ⟨β, hβ⟩ := h2
  obtain ⟨c, hc, hlow⟩ := h3
  have hW : {n : ℕ | n.Weird}.HasDensity (α - β) := by
    rw [weird_eq_diff]
    exact hasDensity_diff PP_subset_ND hα hβ
  exact pos_of_lower hc hW hlow

/-- The nondeficient numbers are closed under positive multiples. -/
lemma ND_mul {n : ℕ} (hn : n ∈ ND) {k : ℕ} (hk : 0 < k) : k * n ∈ ND := by
  obtain ⟨hpos, hle⟩ := hn
  refine ⟨Nat.mul_pos hk hpos, ?_⟩
  have himg : (n.properDivisors.image (fun d => k * d)) ⊆ (k * n).properDivisors := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    have hd' := Nat.mem_properDivisors.mp hd
    exact Nat.mem_properDivisors.mpr
      ⟨Nat.mul_dvd_mul_left k hd'.1, (Nat.mul_lt_mul_left hk).mpr hd'.2⟩
  calc k * n ≤ k * ∑ d ∈ n.properDivisors, d := Nat.mul_le_mul_left k hle
    _ = ∑ d ∈ n.properDivisors, k * d := Finset.mul_sum _ _ _
    _ = ∑ e ∈ n.properDivisors.image (fun d => k * d), e := by
        rw [Finset.sum_image]
        intro a _ b _ hab
        exact Nat.eq_of_mul_eq_mul_left hk hab
    _ ≤ ∑ e ∈ (k * n).properDivisors, e := Finset.sum_le_sum_of_subset himg

/-- The pseudoperfect numbers are closed under positive multiples. -/
lemma PP_mul {n : ℕ} (hn : n ∈ PP) {k : ℕ} (hk : 0 < k) : k * n ∈ PP := by
  obtain ⟨hpos, s, hs, hsum⟩ := hn
  refine ⟨Nat.mul_pos hk hpos, s.image (fun d => k * d), ?_, ?_⟩
  · intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    have hd' := Nat.mem_properDivisors.mp (hs hd)
    exact Nat.mem_properDivisors.mpr
      ⟨Nat.mul_dvd_mul_left k hd'.1, (Nat.mul_lt_mul_left hk).mpr hd'.2⟩
  · rw [Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hk hab),
      ← Finset.mul_sum, hsum]

/-- A pseudoperfect multiple descends when the unscaled divisors have small total. -/
lemma PP_of_mul_small {n t : ℕ} (hn : 0 < n) (ht : 0 < t)
    (hsmall : ∑ e ∈ (t * n).properDivisors.filter (fun e => ¬ t ∣ e), e < t)
    (hPP : t * n ∈ PP) : n ∈ PP := by
  obtain ⟨_, E, hE, hsum⟩ := hPP
  refine ⟨hn, (E.filter (fun e => t ∣ e)).image (fun e => e / t), ?_, ?_⟩
  · intro d hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨heE, hte⟩ := Finset.mem_filter.mp he
    obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp (hE heE)
    obtain ⟨d, rfl⟩ := hte
    rw [Nat.mul_div_cancel_left d ht]
    exact Nat.mem_properDivisors.mpr
      ⟨(Nat.mul_dvd_mul_iff_left ht).mp hdvd, (Nat.mul_lt_mul_left ht).mp hlt⟩
  · have hinj : ∀ a ∈ E.filter (fun e => t ∣ e), ∀ b ∈ E.filter (fun e => t ∣ e),
        a / t = b / t → a = b := by
      intro a ha b hb hab
      obtain ⟨a', rfl⟩ := (Finset.mem_filter.mp ha).2
      obtain ⟨b', rfl⟩ := (Finset.mem_filter.mp hb).2
      rw [Nat.mul_div_cancel_left a' ht, Nat.mul_div_cancel_left b' ht] at hab
      rw [hab]
    rw [Finset.sum_image hinj]
    have h1 : ∑ e ∈ E.filter (fun e => t ∣ e), e
        = t * ∑ e ∈ E.filter (fun e => t ∣ e), e / t := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun e he => ?_)
      exact (Nat.mul_div_cancel' (Finset.mem_filter.mp he).2).symm
    have h0 : ∑ e ∈ E.filter (fun e => ¬ t ∣ e), e < t := by
      refine lt_of_le_of_lt (Finset.sum_le_sum_of_subset ?_) hsmall
      intro e he
      obtain ⟨heE, hte⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨hE heE, hte⟩
    have hsplit := Finset.sum_filter_add_sum_filter_not E (fun e => t ∣ e) (fun e => e)
    have hkey : t * (∑ e ∈ E.filter (fun e => t ∣ e), e / t)
        + ∑ e ∈ E.filter (fun e => ¬ t ∣ e), e = t * n := by
      rw [← h1, hsplit, hsum]
    generalize (∑ e ∈ E.filter (fun e => t ∣ e), e / t) = A at hkey ⊢
    generalize (∑ e ∈ E.filter (fun e => ¬ t ∣ e), e) = r at hkey h0
    have hle : A ≤ n := by
      by_contra hcon
      have h2 : t * n < t * A := (Nat.mul_lt_mul_left ht).mpr (not_le.mp hcon)
      omega
    have hge : n ≤ A := by
      by_contra hcon
      have h2 : t * (A + 1) ≤ t * n := Nat.mul_le_mul_left t (not_le.mp hcon)
      rw [Nat.mul_add, Nat.mul_one] at h2
      omega
    omega

/-- Key step of Benkoski–Erdős Theorem 5, in integer form: if `n` is weird and the proper
divisors of `t * n` that are not multiples of `t` sum to less than `t`, then `t * n` is weird. -/
lemma weird_mul {n t : ℕ} (hn : n.Weird) (ht : 0 < t)
    (hsmall : ∑ e ∈ (t * n).properDivisors.filter (fun e => ¬ t ∣ e), e < t) :
    (t * n).Weird := by
  exact ⟨hn.1.mul_left ht.ne', fun h => hn.2 (PP_of_mul_small hn.pos ht hsmall h)⟩

/-- Explicit weird multiples of `70`: if `t` is coprime to `70` and `144 * s(t) < t`
(where `s(t)` is the sum of the proper divisors of `t` and `144 = σ(70)`), then `t * 70`
is weird. -/
lemma weird_seventy_mul {t : ℕ} (ht : 0 < t) (hco : Nat.Coprime t 70)
    (hsmall : 144 * ∑ s ∈ t.properDivisors, s < t) : (t * 70).Weird := by
  refine weird_mul Nat.weird_seventy ht (lt_of_le_of_lt ?_ hsmall)
  have h144 : ∑ d ∈ (70 : ℕ).divisors, d = 144 := by decide
  have hsub : (t * 70).properDivisors.filter (fun e => ¬ t ∣ e)
      ⊆ ((70 : ℕ).divisors ×ˢ t.properDivisors).image (fun x => x.1 * x.2) := by
    intro e he
    obtain ⟨hpd, hte⟩ := Finset.mem_filter.mp he
    obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hpd
    refine Finset.mem_image.mpr ⟨(Nat.gcd e 70, Nat.gcd e t), ?_, ?_⟩
    · refine Finset.mem_product.mpr
        ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right e 70, by norm_num⟩,
          Nat.mem_properDivisors.mpr ⟨Nat.gcd_dvd_right e t, ?_⟩⟩
      refine lt_of_le_of_ne (Nat.le_of_dvd ht (Nat.gcd_dvd_right e t)) ?_
      intro h
      exact hte (h ▸ Nat.gcd_dvd_left e t)
    · show Nat.gcd e 70 * Nat.gcd e t = e
      rw [← Nat.Coprime.gcd_mul e hco.symm]
      exact Nat.gcd_eq_left (by rwa [Nat.mul_comm] at hdvd)
  calc ∑ e ∈ (t * 70).properDivisors.filter (fun e => ¬ t ∣ e), e
      ≤ ∑ e ∈ ((70 : ℕ).divisors ×ˢ t.properDivisors).image (fun x => x.1 * x.2), e :=
        Finset.sum_le_sum_of_subset hsub
    _ ≤ ∑ x ∈ (70 : ℕ).divisors ×ˢ t.properDivisors, x.1 * x.2 :=
        Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
    _ = (∑ d ∈ (70 : ℕ).divisors, d) * ∑ s ∈ t.properDivisors, s := by
        rw [Finset.sum_mul_sum, Finset.sum_product]
    _ = 144 * ∑ s ∈ t.properDivisors, s := by rw [h144]

/-- The good multipliers of `70`. -/
def T : Set ℕ := {t : ℕ | 0 < t ∧ Nat.Coprime t 70 ∧ 144 * ∑ s ∈ t.properDivisors, s < t}

/-- Transfer: a linear lower bound for the counting function of `T` gives the positive lower
bound for the partial densities of the weird numbers. -/
lemma h3_of_T
    (hT : ∃ c : ℝ, 0 < c ∧ ∀ᶠ b : ℕ in atTop, c * b ≤ ((T ∩ Set.Iio b).ncard : ℝ)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ b : ℕ in atTop, c ≤ {n : ℕ | n.Weird}.partialDensity Set.univ b := by
  obtain ⟨c, hc, hev⟩ := hT
  refine ⟨c / 140, by positivity, ?_⟩
  have htend : Tendsto (fun b : ℕ => b / 70) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr (fun m => ⟨70 * m, fun a ha => by omega⟩)
  filter_upwards [htend.eventually hev, eventually_ge_atTop 140] with b hb hb140
  have hinj : (T ∩ Set.Iio (b / 70)).ncard
      ≤ (({n : ℕ | n.Weird} ∩ Set.univ) ∩ Set.Iio b).ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun t => t * 70) ?_ ?_
      ((Set.finite_Iio b).subset Set.inter_subset_right)
    · rintro t ⟨⟨ht0, hco, hs⟩, htb⟩
      refine ⟨⟨weird_seventy_mul ht0 hco hs, trivial⟩, ?_⟩
      have h1 : t < b / 70 := htb
      show t * 70 < b
      omega
    · intro t1 _ t2 _ h
      have h1 : t1 * 70 = t2 * 70 := h
      omega
  have hden : (Set.univ ∩ Set.Iio b).ncard = b := by
    rw [Set.univ_inter, ← Finset.coe_Iio, Set.ncard_coe_finset, Nat.card_Iio]
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    have : 0 < b := by omega
    exact_mod_cast this
  show c / 140 ≤ ((({n : ℕ | n.Weird} ∩ Set.univ) ∩ Set.Iio b).ncard : ℝ)
      / ((Set.univ ∩ Set.Iio b).ncard : ℝ)
  rw [hden, le_div_iff₀ hbpos]
  have h1 : c * ((b / 70 : ℕ) : ℝ)
      ≤ ((({n : ℕ | n.Weird} ∩ Set.univ) ∩ Set.Iio b).ncard : ℝ) :=
    le_trans hb (by exact_mod_cast hinj)
  have h2 : (b : ℝ) / 140 ≤ ((b / 70 : ℕ) : ℝ) := by
    have h3 : b ≤ 140 * (b / 70) := by omega
    have h4 : (b : ℝ) ≤ 140 * ((b / 70 : ℕ) : ℝ) := by exact_mod_cast h3
    linarith
  calc c / 140 * b = c * (b / 140) := by ring
    _ ≤ c * ((b / 70 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left h2 hc.le
    _ ≤ _ := h1

/-- Lower bound for the number of `x < b` coprime to `K`. -/
lemma count_lower (K b : ℕ) (hK : 0 < K) :
    (K.totient : ℝ) * ((b : ℝ) / K - 1)
      ≤ (((Finset.range b).filter (fun x => K.Coprime x)).card : ℝ) := by
  have hq : ∀ q : ℕ, ((Finset.range (K * q)).filter (fun x => K.Coprime x)).card
      = K.totient * q := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      have hsplit : Finset.range (K * (q + 1))
          = Finset.range (K * q) ∪ Finset.Ico (K * q) (K * q + K) := by
        ext x
        simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
        constructor
        · intro hx
          by_cases h : x < K * q
          · exact Or.inl h
          · right; constructor <;> [omega; (rw [Nat.mul_succ] at hx; exact hx)]
        · rintro (h | ⟨_, h⟩)
          · exact lt_of_lt_of_le h (Nat.mul_le_mul_left K (Nat.le_succ q))
          · rw [Nat.mul_succ]; exact h
      have hdisj : Disjoint (Finset.range (K * q)) (Finset.Ico (K * q) (K * q + K)) := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        simp only [Finset.mem_range] at hx
        simp only [Finset.mem_Ico] at hx'
        omega
      rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter hdisj), ih, Nat.filter_coprime_Ico_eq_totient,
        Nat.mul_succ]
  have hsub : (Finset.range (K * (b / K))).filter (fun x => K.Coprime x)
      ⊆ (Finset.range b).filter (fun x => K.Coprime x) := by
    apply Finset.filter_subset_filter
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    exact lt_of_lt_of_le hx (Nat.mul_div_le b K)
  have h1 := Finset.card_le_card hsub
  rw [hq] at h1
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have h2 : (b : ℝ) / K - 1 ≤ ((b / K : ℕ) : ℝ) := by
    have h3 : b < K * (b / K + 1) := by
      have := Nat.lt_mul_div_succ b hK
      linarith
    have h4 : (b : ℝ) < K * (((b / K : ℕ) : ℝ) + 1) := by exact_mod_cast h3
    rw [div_sub_one hKr.ne', div_le_iff₀ hKr]
    linarith
  calc (K.totient : ℝ) * ((b : ℝ) / K - 1) ≤ (K.totient : ℝ) * ((b / K : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    _ = ((K.totient * (b / K) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ _ := by exact_mod_cast h1

/-- `s(t)/t + 1` is the sum of the reciprocals of the divisors of `t`. -/
lemma s_div_add_one (t : ℕ) (ht : 0 < t) :
    ((∑ d ∈ t.properDivisors, d : ℕ) : ℝ) / t + 1 = ∑ e ∈ t.divisors, (1 : ℝ) / e := by
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  rw [← Nat.sum_div_divisors t (fun e => (1 : ℝ) / e)]
  have h1 : ∀ d ∈ t.divisors, (1 : ℝ) / ((t / d : ℕ) : ℝ) = (d : ℝ) / t := by
    intro d hd
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hd0 : (d : ℝ) ≠ 0 := by
      have := Nat.pos_of_mem_divisors hd
      exact_mod_cast this.ne'
    rw [Nat.cast_div hdvd hd0]
    field_simp
  rw [Finset.sum_congr rfl h1, ← Finset.sum_div]
  have h2 : ((∑ d ∈ t.divisors, d : ℕ) : ℝ) = ((∑ d ∈ t.properDivisors, d : ℕ) : ℝ) + t := by
    rw [Nat.sum_divisors_eq_sum_properDivisors_add_self]
    push_cast
    ring
  push_cast at h2 ⊢
  rw [h2]
  field_simp

/-- Multiples of `e` below `b` that are coprime to `K`. -/
lemma mult_count (K b e : ℕ) (hK : 0 < K) (he : 0 < e) :
    ((((Finset.range b).filter (fun x => K.Coprime x)).filter (fun t => e ∣ t)).card : ℝ)
      ≤ (K.totient : ℝ) * ((b : ℝ) / (e * K) + 2) := by
  have hinj : ((((Finset.range b).filter (fun x => K.Coprime x)).filter (fun t => e ∣ t)).card)
      ≤ ((Finset.Ico 0 (0 + (b / e + 1))).filter (fun x => K.Coprime x)).card := by
    refine Finset.card_le_card_of_injOn (fun t => t / e) ?_ ?_
    · intro t ht
      have ht' := Finset.mem_coe.mp ht
      obtain ⟨htA, hdvd⟩ := Finset.mem_filter.mp ht'
      obtain ⟨htb, hco⟩ := Finset.mem_filter.mp htA
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, ?_⟩)
      · simp only [Finset.mem_Ico, zero_add, Nat.zero_le, true_and]
        have := Nat.div_le_div_right (c := e) (le_of_lt (Finset.mem_range.mp htb))
        omega
      · exact Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hdvd) hco
    · intro t1 ht1 t2 ht2 h
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp ht1)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp ht2)).2
      have h' : t1 / e = t2 / e := h
      rw [← Nat.div_mul_cancel h1, ← Nat.div_mul_cancel h2, h']
  have hle := Nat.Ico_filter_coprime_le (a := K) 0 (b / e + 1) hK.ne'
  have h3 := le_trans hinj hle
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have her : (0 : ℝ) < e := by exact_mod_cast he
  have h4 : (((b / e + 1) / K : ℕ) : ℝ) ≤ (b : ℝ) / (e * K) + 1 := by
    have a1 : (((b / e + 1) / K : ℕ) : ℝ) ≤ ((b / e + 1 : ℕ) : ℝ) / K := Nat.cast_div_le
    have a2 : ((b / e : ℕ) : ℝ) ≤ (b : ℝ) / e := Nat.cast_div_le
    have a3 : ((b / e + 1 : ℕ) : ℝ) / K ≤ ((b : ℝ) / e + 1) / K := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      push_cast
      linarith
    have a4 : ((b : ℝ) / e + 1) / K ≤ (b : ℝ) / (e * K) + 1 := by
      rw [add_div, div_div]
      have : (1 : ℝ) / K ≤ 1 := by rw [div_le_one (by linarith)]; exact hKr
      linarith
    linarith
  calc ((((Finset.range b).filter (fun x => K.Coprime x)).filter (fun t => e ∣ t)).card : ℝ)
      ≤ ((K.totient * ((b / e + 1) / K + 1) : ℕ) : ℝ) := by exact_mod_cast h3
    _ = (K.totient : ℝ) * ((((b / e + 1) / K : ℕ) : ℝ) + 1) := by push_cast; ring
    _ ≤ (K.totient : ℝ) * ((b : ℝ) / (e * K) + 2) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        linarith

/-- Telescoping tail bound for `∑ 1/e^2`. -/
lemma inv_sq_tail (n : ℕ) :
    ∑ e ∈ Finset.Ico 289 (289 + n), (1 : ℝ) / (e : ℝ) ^ 2 ≤ 1 / 288 - 1 / (288 + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Nat.add_assoc, Finset.sum_Ico_succ_top (by omega)]
    have h1 : (1 : ℝ) / ((289 + n : ℕ) : ℝ) ^ 2 ≤ 1 / (288 + n) - 1 / (288 + (n + 1 : ℕ)) := by
      push_cast
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

/-- Harmonic bound. -/
lemma harm_le (b : ℕ) :
    ∑ e ∈ (Finset.range b).filter (fun e => 0 < e), (1 : ℝ) / e ≤ 1 + Real.log b := by
  have hsub : (Finset.range b).filter (fun e => 0 < e)
      ⊆ (Finset.range b).image (fun i : ℕ => i + 1) := by
    intro e he
    obtain ⟨heb, he0⟩ := Finset.mem_filter.mp he
    refine Finset.mem_image.mpr ⟨e - 1, ?_, by omega⟩
    have := Finset.mem_range.mp heb
    exact Finset.mem_range.mpr (by omega)
  calc ∑ e ∈ (Finset.range b).filter (fun e => 0 < e), (1 : ℝ) / e
      ≤ ∑ e ∈ (Finset.range b).image (fun i : ℕ => i + 1), (1 : ℝ) / (e : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ i ∈ Finset.range b, (1 : ℝ) / ((i + 1 : ℕ) : ℝ) := by
        rw [Finset.sum_image (fun a _ c _ (h : a + 1 = c + 1) => by omega)]
    _ = ((harmonic b : ℚ) : ℝ) := by
        rw [harmonic]
        push_cast
        simp [one_div]
    _ ≤ 1 + Real.log b := harmonic_le_one_add_log b

/-- The divisor-sum bound (first moment of `s(t)/t` over `t` coprime to `K`). -/
lemma sum_bound (K b : ℕ) (hK : 0 < K) (hK288 : ∀ e : ℕ, 1 < e → K.Coprime e → 288 < e) :
    ∑ t ∈ (Finset.range b).filter (fun x => K.Coprime x),
        ((∑ d ∈ t.properDivisors, d : ℕ) : ℝ) / t
      ≤ (K.totient : ℝ) / K * b / 288 + 2 * (K.totient : ℝ) * (2 + Real.log b) := by
  have hK1 : K ≠ 1 := by
    rintro rfl
    have := hK288 2 (by norm_num) (Nat.coprime_one_left 2)
    omega
  set A := (Finset.range b).filter (fun x => K.Coprime x) with hA
  set φK : ℝ := (K.totient : ℝ) with hφK
  have hφ0 : (0 : ℝ) ≤ φK := Nat.cast_nonneg _
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  -- pointwise rewriting
  have hpt : ∀ t ∈ A, ((∑ d ∈ t.properDivisors, d : ℕ) : ℝ) / t
      = ∑ e ∈ Finset.range b, (if 1 < e ∧ e ∣ t then (1 : ℝ) / e else 0) := by
    intro t ht
    obtain ⟨htb, hco⟩ := Finset.mem_filter.mp ht
    have htb' := Finset.mem_range.mp htb
    have ht0 : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · rw [h, Nat.coprime_zero_right] at hco; exact absurd hco hK1
      · exact h
    have hdiv : t.divisors = insert 1 ((Finset.range b).filter (fun e => 1 < e ∧ e ∣ t)) := by
      ext e
      simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hd, _⟩
        have hle := Nat.le_of_dvd ht0 hd
        have hne : e ≠ 0 := by rintro rfl; rw [zero_dvd_iff] at hd; omega
        by_cases h1 : e = 1
        · exact Or.inl h1
        · exact Or.inr ⟨by omega, by omega, hd⟩
      · rintro (rfl | ⟨_, _, hd⟩)
        · exact ⟨one_dvd t, ht0.ne'⟩
        · exact ⟨hd, ht0.ne'⟩
    have h1 := s_div_add_one t ht0
    rw [hdiv, Finset.sum_insert (by simp)] at h1
    rw [← Finset.sum_filter]
    simp only [Nat.cast_one, div_one] at h1
    linarith
  rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
  -- bound each e
  set g : ℕ → ℝ := fun e => if 288 < e then φK / K * b * ((1 : ℝ) / (e : ℝ) ^ 2)
      + 2 * φK * ((1 : ℝ) / e) else 0 with hg
  have hge : ∀ e ∈ Finset.range b,
      ∑ t ∈ A, (if 1 < e ∧ e ∣ t then (1 : ℝ) / e else 0) ≤ g e := by
    intro e _
    rw [← Finset.sum_filter]
    by_cases h1 : 1 < e
    · simp only [h1, true_and, Finset.sum_const, nsmul_eq_mul]
      by_cases h288 : 288 < e
      · have her : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
        have hm := mult_count K b e hK (by omega)
        simp only [hg, h288, if_true]
        calc ((A.filter (fun t => e ∣ t)).card : ℝ) * (1 / e)
            ≤ φK * ((b : ℝ) / (e * K) + 2) * (1 / e) :=
              mul_le_mul_of_nonneg_right hm (by positivity)
          _ = φK / K * b * (1 / (e : ℝ) ^ 2) + 2 * φK * (1 / e) := by
              field_simp
      · have hemp : A.filter (fun t => e ∣ t) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro t ht hd
          have hco := (Finset.mem_filter.mp ht).2
          exact h288 (hK288 e h1 (Nat.Coprime.coprime_dvd_right hd hco))
        simp [hemp, hg, h288]
    · have : A.filter (fun t => 1 < e ∧ e ∣ t) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro t _ h
        exact h1 h.1
      rw [this, Finset.sum_empty]
      simp only [hg]
      split_ifs
      · positivity
      · exact le_refl 0
  refine le_trans (Finset.sum_le_sum hge) ?_
  have hsplit : ∑ e ∈ Finset.range b, g e
      = φK / K * b * ∑ e ∈ (Finset.range b).filter (fun e => 288 < e), (1 : ℝ) / (e : ℝ) ^ 2
        + 2 * φK * ∑ e ∈ (Finset.range b).filter (fun e => 288 < e), (1 : ℝ) / e := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_filter]
  rw [hsplit]
  have hs1 : ∑ e ∈ (Finset.range b).filter (fun e => 288 < e), (1 : ℝ) / (e : ℝ) ^ 2
      ≤ 1 / 288 := by
    have hsub : (Finset.range b).filter (fun e => 288 < e) ⊆ Finset.Ico 289 (289 + b) := by
      intro e he
      obtain ⟨heb, he2⟩ := Finset.mem_filter.mp he
      have := Finset.mem_range.mp heb
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun e : ℕ => (1 : ℝ) / (e : ℝ) ^ 2) (fun _ _ _ => by positivity)
    have h2 := inv_sq_tail b
    have h3 : (0 : ℝ) ≤ 1 / (288 + (b : ℝ)) := by
      have : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
      exact div_nonneg zero_le_one (by linarith)
    linarith
  have hs2 : ∑ e ∈ (Finset.range b).filter (fun e => 288 < e), (1 : ℝ) / e
      ≤ 1 + Real.log b := by
    have hsub : (Finset.range b).filter (fun e => 288 < e)
        ⊆ (Finset.range b).filter (fun e => 0 < e) := by
      intro e he
      obtain ⟨heb, he2⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨heb, by omega⟩
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
      (harm_le b)
  have hc1 : (0 : ℝ) ≤ φK / K * b := by positivity
  have e1 := mul_le_mul_of_nonneg_left hs1 hc1
  have e2 := mul_le_mul_of_nonneg_left hs2 (by positivity : (0 : ℝ) ≤ 2 * φK)
  have e3 : φK / K * b * (1 / 288) = φK / K * b / 288 := by ring
  nlinarith

/-- `log b = o(b)` in the explicit form needed below. -/
lemma log_eventually (a : ℝ) (ha : 0 < a) (C : ℝ) :
    ∀ᶠ b : ℕ in atTop, C * (2 + Real.log b) + C ≤ a * b := by
  have h := Real.isLittleO_log_id_atTop
  have h2 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := h.tendsto_div_nhds_zero
  have h3 : Tendsto (fun x : ℝ => (C * (2 + Real.log x) + C) / x) atTop (𝓝 0) := by
    have e1 : Tendsto (fun x : ℝ => 3 * C / x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have := e1.add (h2.const_mul C)
    simp only [mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    field_simp
    ring
  have h4 := (h3.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds ha)
  filter_upwards [h4, eventually_gt_atTop 0] with b hb hb0
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb0
  simp only [Function.comp] at hb
  rw [div_lt_iff₀ hbr] at hb
  linarith

/-- Markov step plus asymptotics. -/
lemma hT_of_K (K : ℕ) (hK : 0 < K) (h70 : 70 ∣ K)
    (hK288 : ∀ e : ℕ, 1 < e → K.Coprime e → 288 < e) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ b : ℕ in atTop, c * b ≤ ((T ∩ Set.Iio b).ncard : ℝ) := by
  have hK1 : K ≠ 1 := by
    rintro rfl
    have := hK288 2 (by norm_num) (Nat.coprime_one_left 2)
    omega
  have hphi : (0 : ℝ) < K.totient := by exact_mod_cast Nat.totient_pos.mpr hK
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  refine ⟨(K.totient : ℝ) / (4 * K), by positivity, ?_⟩
  filter_upwards [log_eventually (1 / (4 * K)) (by positivity) 288] with b hb
  set A := (Finset.range b).filter (fun x => K.Coprime x) with hA
  set s : ℕ → ℕ := fun t => ∑ d ∈ t.properDivisors, d with hs
  have hpos : ∀ t ∈ A, 0 < t := by
    intro t ht
    rcases Nat.eq_zero_or_pos t with h | h
    · exfalso
      have hc := (Finset.mem_filter.mp ht).2
      rw [h, Nat.coprime_zero_right] at hc
      exact hK1 hc
    · exact h
  set G := A.filter (fun t => 144 * s t < t) with hG
  set B := A.filter (fun t => ¬ 144 * s t < t) with hB
  have hGB : (G.card : ℝ) + B.card = A.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not _
  have hBle : (B.card : ℝ) ≤ 144 * ∑ t ∈ A, ((s t : ℕ) : ℝ) / t := by
    calc (B.card : ℝ) = ∑ t ∈ B, (1 : ℝ) := by simp
      _ ≤ ∑ t ∈ B, 144 * (((s t : ℕ) : ℝ) / t) := by
          refine Finset.sum_le_sum (fun t ht => ?_)
          obtain ⟨htA, hnt⟩ := Finset.mem_filter.mp ht
          have htr : (0 : ℝ) < t := by exact_mod_cast hpos t htA
          have h1 : (t : ℝ) ≤ 144 * (s t : ℝ) := by exact_mod_cast not_lt.mp hnt
          rw [← mul_div_assoc, le_div_iff₀ htr]
          linarith
      _ ≤ ∑ t ∈ A, 144 * (((s t : ℕ) : ℝ) / t) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro t _ _
          positivity
      _ = _ := by rw [Finset.mul_sum]
  have hsum := sum_bound K b hK hK288
  have hcount := count_lower K b hK
  have hGT : (G.card : ℝ) ≤ ((T ∩ Set.Iio b).ncard : ℝ) := by
    have : (G : Set ℕ) ⊆ T ∩ Set.Iio b := by
      intro t ht
      have ht' := Finset.mem_coe.mp ht
      obtain ⟨htA, hlt⟩ := Finset.mem_filter.mp ht'
      obtain ⟨htb, hco⟩ := Finset.mem_filter.mp htA
      refine ⟨⟨hpos t htA, (Nat.Coprime.coprime_dvd_left h70 hco).symm, hlt⟩, ?_⟩
      exact Finset.mem_range.mp htb
    have h := Set.ncard_le_ncard this ((Set.finite_Iio b).subset Set.inter_subset_right)
    rw [Set.ncard_coe_finset] at h
    exact_mod_cast h
  refine le_trans ?_ hGT
  have e1 : (K.totient : ℝ) * ((b : ℝ) / K - 1)
      = (K.totient : ℝ) / K * b - K.totient := by field_simp
  have e2 : (K.totient : ℝ) / K * b / 288 * 144 = (K.totient : ℝ) / K * b / 2 := by ring
  have hb' : (K.totient : ℝ) * (288 * (2 + Real.log b) + 288)
      ≤ (K.totient : ℝ) * (1 / (4 * K) * b) := mul_le_mul_of_nonneg_left hb hphi.le
  have e3 : (K.totient : ℝ) * (1 / (4 * K) * b) = (K.totient : ℝ) / (4 * K) * b := by
    field_simp
  have e4 : (K.totient : ℝ) / K * b = 4 * ((K.totient : ℝ) / (4 * K) * b) := by
    field_simp
  nlinarith

lemma hT_main : ∃ c : ℝ, 0 < c ∧ ∀ᶠ b : ℕ in atTop, c * b ≤ ((T ∩ Set.Iio b).ncard : ℝ) := by
  refine hT_of_K (Nat.factorial 288) (Nat.factorial_pos _) ?_ ?_
  · exact Nat.dvd_factorial (by norm_num : 0 < 70) (by norm_num : 70 ≤ 288)
  · intro e he hco
    by_contra hle
    rw [not_lt] at hle
    have hd : e ∣ Nat.factorial 288 := Nat.dvd_factorial (by omega) hle
    have : Nat.gcd (Nat.factorial 288) e = e := Nat.gcd_eq_right hd
    rw [hco] at this
    omega

lemma pd_nat (S : Set ℕ) (b : ℕ) :
    S.partialDensity Set.univ b = ((S ∩ Set.Iio b).ncard : ℝ) / b := by
  simp [Set.partialDensity]

lemma pd_mono_nat {A B : Set ℕ} (h : A ⊆ B) (b : ℕ) :
    A.partialDensity Set.univ b ≤ B.partialDensity Set.univ b := by
  rw [pd_nat, pd_nat]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_left _ h)
    ((Set.finite_Iio b).inter_of_right B)

/-- A periodic set has natural density equal to its proportion in one period. -/
lemma density_periodic (S : Set ℕ) {k : ℕ} (hk : 0 < k)
    (hper : ∀ n : ℕ, n + k ∈ S ↔ n ∈ S) :
    S.HasDensity (((S ∩ Set.Iio k).ncard : ℝ) / k) := by
  classical
  let f : ℕ → ℕ := fun n => if n ∈ S then 1 else 0
  have hf (n : ℕ) : f (n + k) = f n := by simp only [f, hper]
  have hf' (n : ℕ) : f (k + n) = f n := by rw [Nat.add_comm, hf]
  let C : ℕ → ℕ := fun b => ∑ i ∈ Finset.range b, f i
  have hC (b : ℕ) : C b = (S ∩ Set.Iio b).ncard := by
    have heq : (((Finset.range b).filter (fun n => n ∈ S)) : Set ℕ) = S ∩ Set.Iio b := by
      ext n
      simp [and_comm]
    rw [← heq, Set.ncard_coe_finset]
    simp [C, f]
  have hblock (q : ℕ) : C (q * k) = q * C k := by
    induction q with
    | zero => simp [C]
    | succ q ih =>
      rw [Nat.succ_mul]
      calc C (q * k + k) = C (k + q * k) := by rw [add_comm]
        _ = C k + C (q * k) := by
          simp only [C, Finset.sum_range_add, hf']
        _ = (q + 1) * C k := by rw [ih, Nat.add_mul, Nat.one_mul, add_comm]
  have hmono : Monotone C := by
    intro a b hab
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hab)
  have hl (b : ℕ) : b / k * C k ≤ C b := by
    rw [← hblock]
    exact hmono (Nat.div_mul_le_self b k)
  have hu (b : ℕ) : C b ≤ (b / k + 1) * C k := by
    rw [← hblock]
    apply hmono
    simpa [Nat.mul_comm] using (Nat.lt_mul_div_succ b hk).le
  let d : ℝ := (C k : ℝ) / k
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hd : 0 ≤ d := by positivity
  have hb (b : ℕ) : |(C b : ℝ) - d * b| ≤ C k := by
    have h₁ : (b : ℝ) ≤ ((b / k : ℕ) : ℝ) * k + k := by
      exact_mod_cast (show b ≤ b / k * k + k by
        simpa only [Nat.mul_add, Nat.mul_one, Nat.mul_comm k (b / k)] using
          (Nat.lt_mul_div_succ b hk).le)
    have h₂ : ((b / k : ℕ) : ℝ) * k ≤ b := by exact_mod_cast Nat.div_mul_le_self b k
    have h₃ : d * k = C k := div_mul_cancel₀ _ hkR.ne'
    have h₄ := mul_le_mul_of_nonneg_left h₁ hd
    have h₅ := mul_le_mul_of_nonneg_left h₂ hd
    have h₆ : ((b / k : ℕ) : ℝ) * C k ≤ C b := by exact_mod_cast hl b
    have h₇ : (C b : ℝ) ≤ (((b / k : ℕ) : ℝ) + 1) * C k := by exact_mod_cast hu b
    rw [abs_le]
    constructor <;> nlinarith
  rw [← hC k]
  change Tendsto (S.partialDensity Set.univ) atTop (𝓝 d)
  refine tendsto_iff_dist_tendsto_zero.mpr ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat (C k : ℝ)) ?_ ?_
  · exact Filter.Eventually.of_forall fun b => dist_nonneg
  · filter_upwards [eventually_ge_atTop 1] with b hbpos
    have hbR : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
    have heq : (C b : ℝ) / b - d = ((C b : ℝ) - d * b) / b := by
      field_simp
    rw [Real.dist_eq, pd_nat, ← hC, heq, abs_div, abs_of_pos hbR]
    exact div_le_div_of_nonneg_right (hb b) hbR.le

/-- Positive multiples of positive elements of S at most y. -/
def smallMultiples (S : Set ℕ) (y : ℕ) : Set ℕ :=
  {n | 0 < n ∧ ∃ d ∈ S, 0 < d ∧ d ≤ y ∧ d ∣ n}

lemma smallMultiples_density (S : Set ℕ) (y : ℕ) :
    ∃ α : ℝ, (smallMultiples S y).HasDensity α := by
  let A : Set ℕ := {n | ∃ d ∈ S, 0 < d ∧ d ≤ y ∧ d ∣ n}
  have hA := density_periodic A (Nat.factorial_pos y) (fun n => by
    change (∃ d ∈ S, 0 < d ∧ d ≤ y ∧ d ∣ n + y.factorial) ↔
      ∃ d ∈ S, 0 < d ∧ d ≤ y ∧ d ∣ n
    constructor
    · rintro ⟨d, hd, hdpos, hdy, hdn⟩
      exact ⟨d, hd, hdpos, hdy, (Nat.dvd_add_iff_left (Nat.dvd_factorial hdpos hdy)).mpr hdn⟩
    · rintro ⟨d, hd, hdpos, hdy, hdn⟩
      exact ⟨d, hd, hdpos, hdy, (Nat.dvd_add_iff_left (Nat.dvd_factorial hdpos hdy)).mp hdn⟩)
  have hZ : (A ∩ {0}).HasDensity 0 :=
    Nat.hasDensity_zero_of_finite ((Set.finite_singleton 0).inter_of_right A)
  have hEq : smallMultiples S y = A \ (A ∩ {0}) := by
    ext n
    change (0 < n ∧ n ∈ A) ↔ n ∈ A \ (A ∩ {0})
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_singleton_iff, Nat.pos_iff_ne_zero]
    tauto
  rw [hEq]
  exact ⟨_, hasDensity_diff Set.inter_subset_left hA hZ⟩

/-- Arbitrarily small eventual density errors from subsets with density suffice for convergence. -/
lemma exists_density_of_approx {S : Set ℕ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ A : Set ℕ, A ⊆ S ∧ (∃ α : ℝ, A.HasDensity α) ∧
      ∀ᶠ b : ℕ in atTop, (S \ A).partialDensity Set.univ b < ε) :
    ∃ α : ℝ, S.HasDensity α := by
  apply cauchySeq_tendsto_of_complete
  refine Metric.cauchySeq_iff.mpr (fun ε hε => ?_)
  obtain ⟨A, hAS, ⟨α, hα⟩, herr⟩ := h (ε / 4) (by positivity)
  have hNear : ∀ᶠ b : ℕ in atTop, dist (A.partialDensity Set.univ b) α < ε / 4 :=
    (Metric.tendsto_nhds.mp hα) _ (by positivity)
  have hBoth : ∀ᶠ b : ℕ in atTop, dist (S.partialDensity Set.univ b) α < ε / 2 := by
    filter_upwards [herr, hNear] with b hb hba
    have hSA : dist (S.partialDensity Set.univ b) (A.partialDensity Set.univ b) < ε / 4 := by
      rwa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (pd_mono_nat hAS b)), ← pd_diff S A hAS b]
    linarith [dist_triangle (S.partialDensity Set.univ b) (A.partialDensity Set.univ b) α]
  obtain ⟨N, hN⟩ := eventually_atTop.mp hBoth
  refine ⟨N, fun m hm n hn => ?_⟩
  have hn' := hN n hn
  rw [dist_comm] at hn'
  linarith [dist_triangle (S.partialDensity Set.univ m) α (S.partialDensity Set.univ n), hN m hm]

lemma density_of_smallMultiples {S : Set ℕ}
    (hMul : ∀ n ∈ S, ∀ k : ℕ, 0 < k → k * n ∈ S)
    (hRem : ∀ ε : ℝ, 0 < ε → ∃ y : ℕ,
      ∀ᶠ b : ℕ in atTop, (S \ smallMultiples S y).partialDensity Set.univ b < ε) :
    ∃ α : ℝ, S.HasDensity α := by
  apply exists_density_of_approx
  intro ε hε
  obtain ⟨y, hy⟩ := hRem ε hε
  refine ⟨smallMultiples S y, ?_, smallMultiples_density S y, hy⟩
  rintro n ⟨hn, d, hd, _, _, k, rfl⟩
  rw [Nat.mul_comm]
  exact hMul d hd k (Nat.pos_of_ne_zero (by intro hk; simp [hk] at hn))

/-- Positive elements of S with no smaller positive divisor in S. -/
def primitive (S : Set ℕ) : Set ℕ :=
  {d | d ∈ S ∧ 0 < d ∧ ∀ e ∈ S, 0 < e → e ∣ d → d = e}

lemma exists_primitive_dvd {S : Set ℕ} {n : ℕ} (hn : n ∈ S) (hpos : 0 < n) :
    ∃ d ∈ primitive S, d ∣ n := by
  classical
  have hex : ∃ d, d ∈ S ∧ 0 < d ∧ d ∣ n := ⟨n, hn, hpos, dvd_refl n⟩
  obtain ⟨hdS, hdpos, hdvd⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, ⟨hdS, hdpos, ?_⟩, hdvd⟩
  intro e heS hepos hed
  exact le_antisymm (Nat.find_min' hex ⟨heS, hepos, hed.trans hdvd⟩) (Nat.le_of_dvd hdpos hed)

/-- The number of positive multiples of d below b is at most b / d. -/
lemma card_positive_multiples (b d : ℕ) (hd : 0 < d) :
    ((Finset.range b).filter (fun n => 0 < n ∧ d ∣ n)).card ≤ b / d := by
  have hcard : (Finset.Icc 1 (b / d)).card = b / d := by simp [Nat.card_Icc]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun n => n / d) ?_ ?_
  · intro n hn
    obtain ⟨hnb, hnpos, hdn⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hn)
    have hnle := (Finset.mem_range.mp hnb).le
    apply Finset.mem_coe.mpr
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos_iff.mpr ⟨hd, Nat.le_of_dvd hnpos hdn⟩,
      Nat.div_le_div_right hnle⟩
  · intro n hn m hm heq
    have hn' := (Finset.mem_filter.mp (Finset.mem_coe.mp hn)).2.2
    have hm' := (Finset.mem_filter.mp (Finset.mem_coe.mp hm)).2.2
    have h := congrArg (fun x => x * d) heq
    rwa [Nat.div_mul_cancel hn', Nat.div_mul_cancel hm'] at h

/-- The union bound for positive multiples of finitely many positive integers. -/
lemma pd_le_of_dvd_cover {A : Set ℕ} {b : ℕ} {F : Finset ℕ}
    (hF : ∀ d ∈ F, 0 < d)
    (hCover : ∀ n ∈ A ∩ Set.Iio b, 0 < n ∧ ∃ d ∈ F, d ∣ n) :
    A.partialDensity Set.univ b ≤ ∑ d ∈ F, (d : ℝ)⁻¹ := by
  let G : ℕ → Finset ℕ := fun d => (Finset.range b).filter (fun n => 0 < n ∧ d ∣ n)
  have hSub : A ∩ Set.Iio b ⊆ ↑(F.biUnion G) := by
    intro n hn
    obtain ⟨hnpos, d, hd, hdn⟩ := hCover n hn
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨d, hd,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn.2, hnpos, hdn⟩⟩)
  have hN := Set.ncard_le_ncard hSub (F.biUnion G).finite_toSet
  rw [Set.ncard_coe_finset] at hN
  calc A.partialDensity Set.univ b ≤ (∑ d ∈ F, ((G d).card : ℝ)) / b := by
        rw [pd_nat]
        refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
        exact_mod_cast hN.trans Finset.card_biUnion_le
    _ = ∑ d ∈ F, ((G d).card : ℝ) / b := Finset.sum_div _ _ _
    _ ≤ ∑ d ∈ F, (d : ℝ)⁻¹ := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        have hdR : 0 < (d : ℝ) := by exact_mod_cast hF d hd
        by_cases hb : b = 0
        · simp [hb, inv_nonneg.mpr hdR.le]
        have hbR : 0 < (b : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hb)
        rw [div_le_iff₀ hbR, inv_mul_eq_div]
        exact (Nat.cast_le.mpr (card_positive_multiples b d (hF d hd))).trans Nat.cast_div_le

/-- Summability of reciprocals of primitive elements implies natural density. -/
lemma density_of_primitive_summable {S : Set ℕ}
    (hPos : ∀ n ∈ S, 0 < n)
    (hMul : ∀ n ∈ S, ∀ k : ℕ, 0 < k → k * n ∈ S)
    (hSum : Summable (fun d : ℕ =>
      open scoped Classical in if d ∈ primitive S then (d : ℝ)⁻¹ else 0)) :
    ∃ α : ℝ, S.HasDensity α := by
  classical
  let f : ℕ → ℝ := fun d => if d ∈ primitive S then (d : ℝ)⁻¹ else 0
  have hf : ∀ d, 0 ≤ f d := fun d => by
    dsimp [f]
    split <;> positivity
  have hlim : Tendsto (fun y : ℕ => ∑ i ∈ Finset.range y, f i) atTop (𝓝 (∑' i, f i)) :=
    hSum.hasSum.tendsto_sum_nat
  apply density_of_smallMultiples hMul
  intro ε hε
  have hNear : ∀ᶠ y : ℕ in atTop, (∑' i, f i) - ε < ∑ i ∈ Finset.range y, f i :=
    hlim.eventually (lt_mem_nhds (sub_lt_self _ hε))
  obtain ⟨y, hy⟩ := hNear.exists
  refine ⟨y, Filter.Eventually.of_forall (fun b => ?_)⟩
  let F := (Finset.range b).filter (fun d => y < d ∧ d ∈ primitive S)
  have hF (d : ℕ) (hd : d ∈ F) : 0 < d := (Finset.mem_filter.mp hd).2.2.2.1
  have hCover (n : ℕ) (hn : n ∈ (S \ smallMultiples S y) ∩ Set.Iio b) :
      0 < n ∧ ∃ d ∈ F, d ∣ n := by
    have hnpos := hPos n hn.1.1
    obtain ⟨d, hd, hdn⟩ := exists_primitive_dvd hn.1.1 hnpos
    have hdy : y < d := by
      by_contra! hnle
      exact hn.1.2 ⟨hnpos, d, hd.1, hd.2.1, hnle, hdn⟩
    have hdb : d < b := lt_of_le_of_lt (Nat.le_of_dvd hnpos hdn) hn.2
    exact ⟨hnpos, d, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hdb, hdy, hd⟩, hdn⟩
  have hdisj : Disjoint (Finset.range y) F := by
    rw [Finset.disjoint_left]
    exact fun d hdr hdf => (not_lt_of_ge (Finset.mem_range.mp hdr).le) (Finset.mem_filter.mp hdf).2.1
  have hle : (∑ i ∈ Finset.range y, f i) + ∑ d ∈ F, f d ≤ ∑' i, f i := by
    rw [← Finset.sum_union hdisj]
    exact hSum.sum_le_tsum _ (fun i _ => hf i)
  have heq : ∑ d ∈ F, f d = ∑ d ∈ F, (d : ℝ)⁻¹ := by
    refine Finset.sum_congr rfl (fun d hd => ?_)
    exact if_pos (Finset.mem_filter.mp hd).2.2
  rw [heq] at hle
  exact (pd_le_of_dvd_cover hF hCover).trans_lt (by linarith)

/-- The abundancy ratio, expressed as a sum over reciprocal divisors. -/
noncomputable def abundancy (n : ℕ) : ℝ := ∑ d ∈ n.divisors, (1 : ℝ) / d

lemma ND_iff_abundancy {n : ℕ} (hn : 0 < n) : n ∈ ND ↔ 2 ≤ abundancy n := by
  rw [abundancy, ← s_div_add_one n hn]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (1 : ℝ) ≤ (∑ d ∈ n.properDivisors, (d : ℝ)) / n ↔
      n ≤ ∑ d ∈ n.properDivisors, d := by
    rw [le_div_iff₀ hnR, one_mul, ← Nat.cast_sum, Nat.cast_le]
  constructor
  · rintro ⟨_, h⟩
    have h' := hs.mpr h
    push_cast
    linarith
  · intro h
    refine ⟨hn, hs.mp ?_⟩
    push_cast at h
    linarith

lemma abundancy_le_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : 0 < n) :
    abundancy m ≤ abundancy n := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    exact Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors hd).trans hmn, hn.ne'⟩
  · intro d _ _
    positivity

lemma abundancy_gcd_periodic (K n : ℕ) :
    abundancy ((n + K).gcd K) = abundancy (n.gcd K) := by
  rw [Nat.gcd_add_self_left]

noncomputable def abundancyTail (K n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => K < d), (1 : ℝ) / d

lemma abundancy_le_gcd_add_tail (K n : ℕ) (hn : 0 < n) :
    abundancy n ≤ abundancy (n.gcd K.factorial) + abundancyTail K n := by
  rw [abundancy, ← Finset.sum_filter_add_sum_filter_not n.divisors (fun d => d ≤ K)]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨hdn, hdK⟩ := Finset.mem_filter.mp hd
      exact Nat.mem_divisors.mpr
        ⟨Nat.dvd_gcd (Nat.dvd_of_mem_divisors hdn) (Nat.dvd_factorial
          (Nat.pos_of_mem_divisors hdn) hdK), (Nat.gcd_pos_of_pos_left _ hn).ne'⟩
    · intro d _ _
      positivity
  · simp [abundancyTail]

lemma pd_union_le (A B : Set ℕ) (b : ℕ) :
    (A ∪ B).partialDensity Set.univ b ≤
      A.partialDensity Set.univ b + B.partialDensity Set.univ b := by
  rw [pd_nat, pd_nat, pd_nat, ← add_div, Set.union_inter_distrib_right]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast Set.ncard_union_le (A ∩ Set.Iio b) (B ∩ Set.Iio b)

lemma sum_abundancyTail_le (K b : ℕ) :
    ∑ n ∈ Finset.range b, abundancyTail K n
      ≤ (b : ℝ) * ∑ d ∈ (Finset.range b).filter (fun d => K < d), 1 / (d : ℝ)^2 := by
  classical
  let F := (Finset.range b).filter (fun d => K < d)
  have hswap : ∀ n ∈ Finset.range b,
      n.divisors.filter (fun d => K < d) = F.filter (fun d => 0 < n ∧ d ∣ n) := by
    intro n hn
    ext d
    simp only [F, Finset.mem_filter, Nat.mem_divisors, Finset.mem_range]
    constructor
    · rintro ⟨⟨hdn, hn0⟩, hdK⟩
      have hnpos := Nat.pos_of_ne_zero hn0
      exact ⟨⟨lt_of_le_of_lt (Nat.le_of_dvd hnpos hdn) (Finset.mem_range.mp hn), hdK⟩,
        hnpos, hdn⟩
    · rintro ⟨⟨_, hdK⟩, hnpos, hdn⟩
      exact ⟨⟨hdn, hnpos.ne'⟩, hdK⟩
  calc ∑ n ∈ Finset.range b, abundancyTail K n
      = ∑ n ∈ Finset.range b, ∑ d ∈ F, if 0 < n ∧ d ∣ n then (1 : ℝ) / d else 0 := by
        refine Finset.sum_congr rfl (fun n hn => ?_)
        rw [abundancyTail, hswap n hn, Finset.sum_filter]
    _ = ∑ d ∈ F, (((Finset.range b).filter (fun n => 0 < n ∧ d ∣ n)).card : ℝ) * (1 / d) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [← Finset.sum_filter]
        simp
    _ ≤ (b : ℝ) * ∑ d ∈ F, 1 / (d : ℝ)^2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun d hd => ?_)
      have hd' : 0 < d := by have := (Finset.mem_filter.mp hd).2; omega
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd'
      have he := mul_le_mul_of_nonneg_right
        ((Nat.cast_le.mpr (card_positive_multiples b d hd')).trans (Nat.cast_div_le (α := ℝ)))
        (show 0 ≤ (1 : ℝ) / d by positivity)
      convert he using 1
      field_simp

-- The telescoping bound is adapted from the local Schoenberg proof.
lemma tail_sq(K : ℕ) (hK : 1 ≤ K) (N : ℕ) :
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

lemma pd_abundancyTail_le (K b : ℕ) (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) :
    {n | δ < abundancyTail K n}.partialDensity Set.univ b ≤ 1 / (K * δ) := by
  classical
  let F := (Finset.range b).filter (fun n => δ < abundancyTail K n)
  have hF : (F : Set ℕ) = {n | δ < abundancyTail K n} ∩ Set.Iio b := by
    ext n
    simp [F, and_comm]
  have hsum : (F.card : ℝ) * δ ≤ (b : ℝ) / K := by
    calc (F.card : ℝ) * δ = ∑ _ ∈ F, δ := by simp
      _ ≤ ∑ n ∈ F, abundancyTail K n :=
        Finset.sum_le_sum (fun n hn => (Finset.mem_filter.mp hn).2.le)
      _ ≤ ∑ n ∈ Finset.range b, abundancyTail K n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro n _ _
        exact Finset.sum_nonneg (fun d _ => by positivity)
      _ ≤ (b : ℝ) * ∑ d ∈ (Finset.range b).filter (fun d => K < d), 1 / (d : ℝ)^2 :=
        sum_abundancyTail_le K b
      _ ≤ (b : ℝ) / K := by
        rw [div_eq_mul_one_div]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        simpa [not_le] using tail_sq K hK b
  rw [pd_nat, ← hF, Set.ncard_coe_finset]
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr (by omega)
  by_cases hb : b = 0
  · rw [hb, Nat.cast_zero, div_zero]
    positivity
  have hbR : 0 < (b : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hb)
  have hbound : (F.card : ℝ) ≤ (b : ℝ) / (K * δ) := by
    rw [le_div_iff₀ (mul_pos hKr hδ)]
    calc (F.card : ℝ) * (K * δ) = ((F.card : ℝ) * δ) * K := by ring
      _ ≤ ((b : ℝ) / K) * K := mul_le_mul_of_nonneg_right hsum hKr.le
      _ = b := div_mul_cancel₀ _ hKr.ne'
  rw [div_le_iff₀ hbR]
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hbound

/-- A periodic approximation to the nondeficient numbers, with zero removed. -/
def ndApprox (K : ℕ) : Set ℕ :=
  {n | 0 < n ∧ 2 ≤ abundancy (n.gcd K.factorial)}

lemma ndApprox_subset (K : ℕ) : ndApprox K ⊆ ND := by
  rintro n ⟨hn, h⟩
  exact (ND_iff_abundancy hn).mpr (h.trans (abundancy_le_of_dvd (Nat.gcd_dvd_left _ _) hn))

lemma ndApprox_density (K : ℕ) : ∃ α : ℝ, (ndApprox K).HasDensity α := by
  let A : Set ℕ := {n | 2 ≤ abundancy (n.gcd K.factorial)}
  have hA : ∀ n, n + K.factorial ∈ A ↔ n ∈ A := by
    intro n
    change (2 ≤ abundancy ((n + K.factorial).gcd K.factorial)) ↔ 2 ≤ abundancy (n.gcd K.factorial)
    rw [abundancy_gcd_periodic]
  have hEq : ndApprox K = A \ (A ∩ {0}) := by
    ext n
    change (0 < n ∧ n ∈ A) ↔ n ∈ A \ (A ∩ {0})
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_singleton_iff, Nat.pos_iff_ne_zero]
    tauto
  rw [hEq]
  exact ⟨_, hasDensity_diff Set.inter_subset_left (density_periodic A (Nat.factorial_pos K) hA)
    (Nat.hasDensity_zero_of_finite ((Set.finite_singleton 0).inter_of_right A))⟩

def abundancyWindow (K : ℕ) (δ : ℝ) : Set ℕ :=
  {n | 2 - δ ≤ abundancy (n.gcd K.factorial) ∧ abundancy (n.gcd K.factorial) < 2}

lemma nd_density_of_window
    (hwin : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ K : ℕ in atTop,
      ∀ᶠ b : ℕ in atTop, (abundancyWindow K δ).partialDensity Set.univ b < ε) :
    ∃ α : ℝ, ND.HasDensity α := by
  apply exists_density_of_approx
  intro ε hε
  obtain ⟨δ, hδ, hwinδ⟩ := hwin (ε / 2) (by positivity)
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (2 / (ε * δ))
  obtain ⟨K, hwinK, hK⟩ := (hwinδ.and (eventually_ge_atTop (max K₀ 1))).exists
  have h1 : 1 ≤ K := le_trans (le_max_right _ _) hK
  have h2 : (2 : ℝ) / (ε * δ) < K := hK₀.trans_le
    (Nat.cast_le.mpr (le_trans (le_max_left _ _) hK))
  have h3 : 1 / ((K : ℝ) * δ) ≤ ε / 2 := by
    rw [div_lt_iff₀ (mul_pos hε hδ)] at h2
    rw [div_le_iff₀ (mul_pos (Nat.cast_pos.mpr (by omega)) hδ)]
    nlinarith
  refine ⟨ndApprox K, ndApprox_subset K, ndApprox_density K, ?_⟩
  filter_upwards [hwinK] with b hb
  have hsub : ND \ ndApprox K ⊆ abundancyWindow K δ ∪ {n | δ < abundancyTail K n} := by
    rintro n ⟨hn, hnA⟩
    by_cases htail : δ < abundancyTail K n
    · exact Or.inr htail
    · left
      refine ⟨?_, lt_of_not_ge (fun h => hnA ⟨hn.1, h⟩)⟩
      have hle := abundancy_le_gcd_add_tail K n hn.1
      have h2 := (ND_iff_abundancy hn.1).mp hn
      linarith
  have hle := (pd_mono_nat hsub b).trans (pd_union_le _ _ b)
  linarith [pd_abundancyTail_le K b h1 hδ]

/-- Multiplication by p divides the density of a periodic set by p. -/
lemma density_periodic_mul_image (A : Set ℕ) {k p : ℕ} (hk : 0 < k) (hp : 0 < p)
    (hper : ∀ n : ℕ, n + k ∈ A ↔ n ∈ A) :
    ((fun n => p * n) '' A).HasDensity ((((A ∩ Set.Iio k).ncard : ℝ) / k) / p) := by
  let B := (fun n => p * n) '' A
  have hmem (n : ℕ) : n ∈ B ↔ p ∣ n ∧ n / p ∈ A := by
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨dvd_mul_right _ _, by rwa [Nat.mul_div_cancel_left _ hp]⟩
    · rintro ⟨hn, ha⟩
      exact ⟨n / p, ha, Nat.mul_div_cancel' hn⟩
  have hB (n : ℕ) : n + p * k ∈ B ↔ n ∈ B := by
    rw [hmem, hmem, ← Nat.dvd_add_iff_left (dvd_mul_right p k), Nat.add_mul_div_left _ _ hp, hper]
  have hcard : (B ∩ Set.Iio (p * k)).ncard = (A ∩ Set.Iio k).ncard := by
    have heq : B ∩ Set.Iio (p * k) = (fun n => p * n) '' (A ∩ Set.Iio k) := by
      ext n
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, hlt⟩
        exact ⟨a, ⟨ha, (Nat.mul_lt_mul_left hp).mp hlt⟩, rfl⟩
      · rintro ⟨a, ⟨ha, hlt⟩, rfl⟩
        exact ⟨⟨a, ha, rfl⟩, (Nat.mul_lt_mul_left hp).mpr hlt⟩
    rw [heq, Set.ncard_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left hp h)]
  have ht := density_periodic B (Nat.mul_pos hp hk) hB
  rw [hcard, Nat.cast_mul] at ht
  simpa only [div_div, mul_comm (p : ℝ)] using ht

lemma density_dvd {p : ℕ} (hp : 0 < p) : {n | p ∣ n}.HasDensity (1 / (p : ℝ)) := by
  have heq : (fun n => p * n) '' (Set.univ : Set ℕ) = {n | p ∣ n} := by
    ext n
    exact ⟨fun ⟨a, _, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, trivial, ha.symm⟩⟩
  have h := density_periodic_mul_image Set.univ (k := 1) (by omega) hp (fun _ => by simp)
  simpa [heq] using h

lemma sum_densities_le_one {P : Finset ℕ} {A : ℕ → Set ℕ} {α : ℕ → ℝ}
    (hA : ∀ p ∈ P, (A p).HasDensity (α p))
    (hDisj : (P : Set ℕ).PairwiseDisjoint A) : ∑ p ∈ P, α p ≤ 1 := by
  classical
  have ht := tendsto_finsetSum P hA
  apply le_of_tendsto_of_tendsto' ht tendsto_const_nhds
  intro b
  let F : ℕ → Finset ℕ := fun p => (Finset.range b).filter (fun n => n ∈ A p)
  have hF (p : ℕ) : (F p : Set ℕ) = A p ∩ Set.Iio b := by
    ext n
    simp [F, and_comm]
  have hFin : (P : Set ℕ).PairwiseDisjoint F := by
    intro p hp q hq hpq
    change Disjoint (F p) (F q)
    rw [Finset.disjoint_left]
    intro n hn h'n
    exact Set.disjoint_left.mp (hDisj hp hq hpq)
      (Finset.mem_filter.mp hn).2 (Finset.mem_filter.mp h'n).2
  have hcard : ∑ p ∈ P, (F p).card ≤ b := by
    rw [← Finset.card_biUnion hFin, ← Finset.card_range b]
    apply Finset.card_le_card
    intro n hn
    obtain ⟨p, _, hnp⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hnp).1
  calc (∑ p ∈ P, (A p).partialDensity Set.univ b)
      = (∑ p ∈ P, ((F p).card : ℝ)) / b := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun p _ => by rw [pd_nat, ← hF, Set.ncard_coe_finset])
    _ ≤ 1 := by
      apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
      exact_mod_cast hcard

/-- Disjoint images formed by inserting absent primes bound the density of the original set. -/
lemma periodic_sparse_of_prime_images {W : Set ℕ} {k : ℕ} (hk : 0 < k)
    (hper : ∀ n : ℕ, n + k ∈ W ↔ n ∈ W)
    (P : Finset ℕ) (hP : ∀ p ∈ P, 1 < p ∧ p ∣ k)
    (hDisj : (P : Set ℕ).PairwiseDisjoint
      (fun p => (fun n => p * n) '' (W \ {n | p ∣ n}))) :
    (((W ∩ Set.Iio k).ncard : ℝ) / k) * (∑ p ∈ P, (1 : ℝ) / p) ≤ 2 := by
  classical
  let α : ℝ := ((W ∩ Set.Iio k).ncard : ℝ) / k
  let β : ℕ → ℝ := fun p =>
    ((((W \ {n | p ∣ n}) ∩ Set.Iio k).ncard : ℝ) / k) / p
  let γ : ℕ → ℝ := fun p => (((W ∩ {n | p ∣ n}) ∩ Set.Iio k).ncard : ℝ) / k
  have hβ p (hp : p ∈ P) :
      ((fun n => p * n) '' (W \ {n | p ∣ n})).HasDensity (β p) := by
    refine density_periodic_mul_image _ hk (by have := (hP p hp).1; omega) (fun n => ?_)
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, hper, ← Nat.dvd_add_iff_left (hP p hp).2]
  have hγ p (hp : p ∈ P) : (W ∩ {n | p ∣ n}).HasDensity (γ p) := by
    refine density_periodic _ hk (fun n => ?_)
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hper, ← Nat.dvd_add_iff_left (hP p hp).2]
  have hbound p (hp : p ∈ P) : α / p ≤ β p + 1 / (p : ℝ)^2 := by
    have hp' : 0 < p := by have := (hP p hp).1; omega
    have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp'
    have hγle : γ p ≤ 1 / (p : ℝ) :=
      Set.HasDensity.mono Set.inter_subset_right (hγ p hp) (density_dvd hp')
    have heq : W \ (W ∩ {n | p ∣ n}) = W \ {n | p ∣ n} := by
      ext n
      simp only [Set.mem_sdiff, Set.mem_inter_iff]
      tauto
    have hden := hasDensity_diff Set.inter_subset_left (density_periodic W hk hper) (hγ p hp)
    rw [heq] at hden
    have hW' : ∀ n : ℕ, n + k ∈ W \ {n | p ∣ n} ↔ n ∈ W \ {n | p ∣ n} := by
      intro n
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq, hper, ← Nat.dvd_add_iff_left (hP p hp).2]
    have he := tendsto_nhds_unique hden (density_periodic _ hk hW')
    change α - γ p = _ at he
    dsimp [β]
    rw [← he, sub_div]
    have hg := div_le_div_of_nonneg_right hγle hpR.le
    rw [show (1 : ℝ) / p / p = 1 / (p : ℝ)^2 by rw [div_div, pow_two]] at hg
    linarith
  have hb := sum_densities_le_one hβ hDisj
  obtain ⟨L, hL⟩ := Finset.exists_nat_subset_range P
  have hsq : ∑ p ∈ P, 1 / (p : ℝ)^2 ≤ 1 := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg
      (t := (Finset.range L).filter (fun p => 1 < p)) ?_ (fun p _ _ => by positivity)).trans ?_
    · intro p hp
      exact Finset.mem_filter.mpr ⟨hL hp, (hP p hp).1⟩
    · simpa only [not_le, Nat.cast_one, div_one] using tail_sq 1 (by omega) L
  rw [Finset.mul_sum]
  calc (∑ p ∈ P, α * (1 / (p : ℝ))) = ∑ p ∈ P, α / p := by simp only [mul_one_div]
    _ ≤ ∑ p ∈ P, (β p + 1 / (p : ℝ)^2) := Finset.sum_le_sum hbound
    _ ≤ 2 := by rw [Finset.sum_add_distrib]; linarith


lemma abundancy_eq_sigma {n : ℕ} (hn : 0 < n) :
    abundancy n = (ArithmeticFunction.sigma 1 n : ℝ) / n := by
  rw [abundancy, ← s_div_add_one n hn, ArithmeticFunction.sigma_one_apply,
    Nat.sum_divisors_eq_sum_properDivisors_add_self, Nat.cast_add, add_div,
    div_self (Nat.cast_ne_zero.mpr hn.ne')]

lemma abundancy_mul_prime {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (hco : p.Coprime n) :
    abundancy (p * n) = (1 + 1 / (p : ℝ)) * abundancy n := by
  have hs : ArithmeticFunction.sigma 1 p = p + 1 := by
    have h := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp
    rw [pow_one] at h
    simpa [Finset.sum_range_succ, Nat.add_comm] using h
  rw [abundancy_eq_sigma (Nat.mul_pos hp.pos hn), abundancy_eq_sigma hn,
    (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hco,
    hs, Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  <;> ring

lemma abundancy_gcd_mul_prime {p n k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hpk : p ∣ k) (hpn : ¬ p ∣ n) :
    abundancy ((p * n).gcd k) = (1 + 1 / (p : ℝ)) * abundancy (n.gcd k) := by
  have hco := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn
  rw [Nat.gcd_comm (p * n) k, hco.gcd_mul k, Nat.gcd_eq_right hpk, Nat.gcd_comm k n]
  exact abundancy_mul_prime hp (Nat.gcd_pos_of_pos_right _ hk) (hco.coprime_dvd_right (Nat.gcd_dvd_left _ _))

lemma abundancy_one_le {n : ℕ} (hn : 0 < n) : 1 ≤ abundancy n := by
  simpa [show abundancy 1 = 1 by simp [abundancy]] using
    abundancy_le_of_dvd (one_dvd n) hn

lemma window_separation {p q L : ℕ} {a b : ℝ} (hp : p.Prime) (hpq : p < q) (hqL : q ≤ L)
    (ha : 1 ≤ a) (hab : (1 + 1 / (p : ℝ)) * a = (1 + 1 / (q : ℝ)) * b) :
    1 / (4 * (L : ℝ)^2) ≤ b - a := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr (hp.pos.trans hpq)
  have hLR : (0 : ℝ) < L := Nat.cast_pos.mpr ((hp.pos.trans hpq).trans_le hqL)
  have hpL : (p : ℝ) ≤ L := Nat.cast_le.mpr (hpq.le.trans hqL)
  have hqL' : (q : ℝ) ≤ L := Nat.cast_le.mpr hqL
  have hdist : (p : ℝ) + 1 ≤ q := by exact_mod_cast hpq
  have hprod : (p : ℝ) * q ≤ (L : ℝ)^2 := by
    rw [pow_two]
    exact mul_le_mul hpL hqL' hqR.le hLR.le
  have hdiff : 1 / (L : ℝ)^2 ≤ 1 / (p : ℝ) - 1 / (q : ℝ) := by
    rw [div_sub_div _ _ hpR.ne' hqR.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    have h := mul_le_mul_of_nonneg_right (show 1 ≤ (q : ℝ) - p by linarith) (sq_nonneg (L : ℝ))
    nlinarith
  have hdiff0 : 0 ≤ 1 / (p : ℝ) - 1 / (q : ℝ) := (by positivity : 0 ≤ 1 / (L : ℝ)^2).trans hdiff
  have hbig := mul_le_mul_of_nonneg_right ha hdiff0
  simp only [one_mul] at hbig
  have hiden : (b - a) * (1 + 1 / (q : ℝ)) = a * (1 / (p : ℝ) - 1 / (q : ℝ)) := by
    linarith only [hab]
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hqtwo : (1 : ℝ) + 1 / q ≤ 2 := by
    have := (div_le_one hqR).mpr hqone
    linarith
  have hmul := mul_le_mul_of_nonneg_left hqtwo (show 0 ≤ 1 / (4 * (L : ℝ)^2) by positivity)
  have he : (1 / (4 * (L : ℝ)^2)) * 2 ≤ 1 / (L : ℝ)^2 := by
    have hh : (1 : ℝ) / (4 * (L : ℝ)^2) * 2 = (1 / (L : ℝ)^2) / 2 := by
      field_simp
      <;> ring
    rw [hh]
    have : (0 : ℝ) ≤ 1 / (L : ℝ)^2 := by positivity
    linarith
  apply (le_of_mul_le_mul_right · (by positivity : 0 < (1 : ℝ) + 1 / q))
  rw [hiden]
  simpa only [one_mul] using hmul.trans (he.trans (hdiff.trans hbig))

lemma window_prime_images_disjoint {K L : ℕ} (hLK : L ≤ K)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ L) :
    (P : Set ℕ).PairwiseDisjoint (fun p => (fun n => p * n) ''
      (abundancyWindow K (1 / (4 * (L : ℝ)^2)) \ {n | p ∣ n})) := by
  have hSep : ∀ p ∈ P, ∀ q ∈ P, p < q →
      Disjoint ((fun n => p * n) '' (abundancyWindow K (1 / (4 * (L : ℝ)^2)) \ {n | p ∣ n}))
        ((fun n => q * n) '' (abundancyWindow K (1 / (4 * (L : ℝ)^2)) \ {n | q ∣ n})) := by
    intro p hp q hq hpq
    rw [Set.disjoint_left]
    rintro n ⟨x, ⟨hx, hpx⟩, hxn⟩ ⟨y, ⟨hy, hqy⟩, hyn⟩
    have hpK := Nat.dvd_factorial (hP p hp).1.pos ((hP p hp).2.trans hLK)
    have hqK := Nat.dvd_factorial (hP q hq).1.pos ((hP q hq).2.trans hLK)
    have hx' := abundancy_gcd_mul_prime (hP p hp).1 (Nat.factorial_pos K) hpK hpx
    have hy' := abundancy_gcd_mul_prime (hP q hq).1 (Nat.factorial_pos K) hqK hqy
    change p * x = n at hxn
    change q * y = n at hyn
    rw [hxn] at hx'
    rw [hyn] at hy'
    have hxge := abundancy_one_le (Nat.gcd_pos_of_pos_right x (Nat.factorial_pos K))
    have h := window_separation (hP p hp).1 hpq (hP q hq).2 hxge (hx'.symm.trans hy')
    have h1 := hx.1
    have h2 := hy.2
    linarith
  intro p hp q hq hpq
  rcases lt_or_gt_of_ne hpq with hpq' | hqp
  · exact hSep p hp q hq hpq'
  · exact (hSep q hq p hp hqp).symm

lemma prime_harmonic_diverge (R : ℝ) : ∃ L, R ≤ ∑ p ∈ (Finset.range L).filter Nat.Prime, 1 / (p : ℝ) := by
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

lemma abundancyWindow_small :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ K : ℕ in atTop,
      ∀ᶠ b : ℕ in atTop, (abundancyWindow K δ).partialDensity Set.univ b < ε := by
  intro ε hε
  obtain ⟨L, hL⟩ := prime_harmonic_diverge (4 / ε)
  let P := (Finset.range L).filter Nat.Prime
  let δ : ℝ := 1 / (4 * ((L + 2 : ℕ) : ℝ)^2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [eventually_ge_atTop (L + 2)] with K hK
  let W := abundancyWindow K δ
  have hper : ∀ n : ℕ, n + K.factorial ∈ W ↔ n ∈ W := by
    intro n
    change (2 - δ ≤ abundancy ((n + K.factorial).gcd K.factorial) ∧
      abundancy ((n + K.factorial).gcd K.factorial) < 2) ↔
      (2 - δ ≤ abundancy (n.gcd K.factorial) ∧ abundancy (n.gcd K.factorial) < 2)
    rw [abundancy_gcd_periodic]
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ p ≤ L + 2 := by
    obtain ⟨hpL, hpr⟩ := Finset.mem_filter.mp hp
    have := Finset.mem_range.mp hpL
    exact ⟨hpr, by omega⟩
  have hs := periodic_sparse_of_prime_images (Nat.factorial_pos K) hper P
    (fun p hp => ⟨(hP p hp).1.one_lt, Nat.dvd_factorial (hP p hp).1.pos ((hP p hp).2.trans hK)⟩)
    (window_prime_images_disjoint hK P hP)
  let α : ℝ := ((W ∩ Set.Iio K.factorial).ncard : ℝ) / K.factorial
  have hα0 : 0 ≤ α := by positivity
  have hα : α * (4 / ε) ≤ 2 :=
    (mul_le_mul_of_nonneg_left (show 4 / ε ≤ ∑ p ∈ P, (1 : ℝ) / p from hL) hα0).trans hs
  have hεα : α < ε := by
    have hm : (4 / ε : ℝ) * ε = 4 := by field_simp
    have hα' := mul_le_mul_of_nonneg_right hα hε.le
    rw [mul_assoc, hm] at hα'
    linarith
  exact (density_periodic W (Nat.factorial_pos K) hper).eventually (gt_mem_nhds hεα)

lemma ND_density : ∃ α : ℝ, ND.HasDensity α :=
  nd_density_of_window abundancyWindow_small


/-- If a reciprocal-divisor tail is shorter than a single unit of the cutoff
denominator, the cutoff determines pseudoperfectness. -/
lemma PP_gcd_factorial_iff_of_tail {K n : ℕ} (hn : 0 < n)
    (htail : ((n.gcd K.factorial : ℕ) : ℝ) * abundancyTail K n < 1) :
    n ∈ PP ↔ n.gcd K.factorial ∈ PP := by
  let m := n.gcd K.factorial
  let t := n / m
  have hm : 0 < m := Nat.gcd_pos_of_pos_left K.factorial hn
  have hmn : m ∣ n := Nat.gcd_dvd_left _ _
  have ht : 0 < t := Nat.div_pos_iff.mpr ⟨hm, Nat.le_of_dvd hn hmn⟩
  have htm : t * m = n := Nat.div_mul_cancel hmn
  constructor
  · intro hnPP
    have hsplit : ∑ e ∈ n.properDivisors.filter (fun e => ¬ t ∣ e), e < t := by
      let F := n.properDivisors.filter (fun e => ¬ t ∣ e)
      let f := fun e : ℕ => n / e
      have hD (e : ℕ) (he : e ∈ F) : e ∈ n.divisors :=
        Nat.properDivisors_subset_divisors (Finset.mem_filter.mp he).1
      have hmem (e : ℕ) (he : e ∈ F) : f e ∈ n.divisors := by
        rw [← Nat.image_div_divisors_eq_divisors n]
        exact Finset.mem_image.mpr ⟨e, hD e he, rfl⟩
      have hinj : ∀ a ∈ F, ∀ b ∈ F, f a = f b → a = b := by
        intro a ha b hb hab
        have heq := congrArg (fun d => n / d) hab
        dsimp [f] at heq
        rwa [Nat.div_div_self (Nat.dvd_of_mem_divisors (hD a ha)) hn.ne',
          Nat.div_div_self (Nat.dvd_of_mem_divisors (hD b hb)) hn.ne'] at heq
      have hsub : F.image f ⊆ n.divisors.filter (fun d => K < d) := by
        intro d hd
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
        have hfe := hmem e he
        refine Finset.mem_filter.mpr ⟨hfe, ?_⟩
        by_contra! hle
        have hdm : f e ∣ m := Nat.dvd_gcd (Nat.dvd_of_mem_divisors hfe)
          (Nat.dvd_factorial (Nat.pos_of_mem_divisors hfe) hle)
        obtain ⟨q, hq⟩ := hdm
        have heq : n = f e * (t * q) := by
          rw [← htm, hq]
          ac_rfl
        have hdiv : n / (f e) = t * q :=
          Nat.div_eq_of_eq_mul_right (Nat.pos_of_mem_divisors hfe) heq
        change n / (n / e) = t * q at hdiv
        rw [Nat.div_div_self (Nat.dvd_of_mem_divisors (hD e he)) hn.ne'] at hdiv
        exact (Finset.mem_filter.mp he).2 ⟨q, hdiv⟩
      have hsum : (∑ e ∈ F, (e : ℝ)) ≤ (n : ℝ) * abundancyTail K n := by
        rw [abundancyTail, Finset.mul_sum]
        calc
          (∑ e ∈ F, (e : ℝ)) = (∑ e ∈ F, (n : ℝ) * (1 / (f e : ℝ))) := by
            refine Finset.sum_congr rfl (fun e he => ?_)
            have hfe : (f e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors (hmem e he)).ne'
            have heq : (e : ℝ) * (f e : ℝ) = n := by
              exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors (hD e he))
            field_simp
            exact heq
          _ = (∑ d ∈ F.image f, (n : ℝ) * (1 / (d : ℝ))) := by rw [Finset.sum_image hinj]
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      have htmR : (t : ℝ) * (m : ℝ) = n := by exact_mod_cast htm
      have htR : (0 : ℝ) < t := Nat.cast_pos.mpr ht
      have htail' : (m : ℝ) * abundancyTail K n < 1 := htail
      have hlt := mul_lt_mul_of_pos_left htail' htR
      rw [← mul_assoc, htmR, mul_one] at hlt
      have h := hsum.trans_lt hlt
      rw [← Nat.cast_sum] at h
      exact_mod_cast h
    rw [← htm] at hsplit hnPP
    exact PP_of_mul_small hm ht hsplit hnPP
  · intro hmPP
    rw [← htm]
    exact PP_mul hmPP ht

def badCutoffs (F : Finset ℕ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ ∀ K ∈ F, 1 ≤ ((n.gcd K.factorial : ℕ) : ℝ) * abundancyTail K n}

lemma pp_density_of_good_cutoffs
    (hcut : ∀ ε : ℝ, 0 < ε → ∃ F : Finset ℕ, ∀ᶠ b : ℕ in atTop,
      (badCutoffs F).partialDensity Set.univ b < ε) :
    ∃ α : ℝ, PP.HasDensity α := by
  apply density_of_smallMultiples (fun _ hn _ hk => PP_mul hn hk)
  intro ε hε
  obtain ⟨F, hF⟩ := hcut ε hε
  refine ⟨F.sup Nat.factorial, ?_⟩
  filter_upwards [hF] with b hb
  apply lt_of_le_of_lt (pd_mono_nat ?_ b) hb
  intro n hn
  have hnpos : 0 < n := hn.1.1
  refine ⟨hnpos, fun K hK => ?_⟩
  by_contra! h
  have hpp := (PP_gcd_factorial_iff_of_tail hnpos h).mp hn.1
  exact hn.2 ⟨hnpos, n.gcd K.factorial, hpp, Nat.gcd_pos_of_pos_left _ hnpos,
    (Nat.le_of_dvd (Nat.factorial_pos _) (Nat.gcd_dvd_right _ _)).trans (Finset.le_sup hK),
    Nat.gcd_dvd_left _ _⟩


/-- An elementary logarithmically weighted estimate for prime reciprocals. -/
lemma sum_prime_log_div_le (y : ℕ) (hy : 0 < y) :
    ∑ p ∈ (Finset.range (y + 1)).filter Nat.Prime, Real.log p / (p : ℝ) ≤ 2 * Real.log y := by
  let P := (Finset.range (y + 1)).filter Nat.Prime
  have hp (p : ℕ) (h : p ∈ P) : p.Prime ∧ p ≤ y := by
    obtain ⟨hpy, hp⟩ := Finset.mem_filter.mp h
    exact ⟨hp, Nat.le_of_lt_succ (Finset.mem_range.mp hpy)⟩
  have hδ (p : ℕ) (hpr : p.Prime) (hpy : p ≤ y) : y / p ≤ y.factorial.factorization p := by
    have hlog : Nat.log p y < Nat.log p y + 2 := by omega
    rw [Nat.factorization_factorial hpr hlog]
    have hi : (1 : ℕ) ∈ Finset.Ico 1 (Nat.log p y + 2) := by simp
    simpa only [pow_one] using Finset.single_le_sum (fun i _ => Nat.zero_le (y / p ^ i)) hi
  have hcase (p : ℕ) (h : p ∈ P) :
      (y : ℝ) / (2 * p) ≤ (y.factorial.factorization p : ℝ) := by
    obtain ⟨hpr, hpy⟩ := hp p h
    have hpp : 0 < p := hpr.pos
    have hdiv : (1 : ℕ) ≤ y / p := Nat.div_pos_iff.mpr ⟨hpp, hpy⟩
    have hlt := Nat.lt_mul_div_succ y hpp
    have hle : y ≤ 2 * p * (y / p) := by
      calc y ≤ p * (y / p + 1) := hlt.le
        _ ≤ p * (y / p + y / p) := Nat.mul_le_mul_left p (Nat.add_le_add_left hdiv _)
        _ = 2 * p * (y / p) := by ring
    have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hpp
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * p)]
    exact le_trans (by simpa only [mul_comm] using (show (y : ℝ) ≤ 2 * p * ((y / p : ℕ) : ℝ) by exact_mod_cast hle))
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hδ p hpr hpy)) (by positivity))
  have hsub : P ⊆ y.factorial.factorization.support := by
    intro p h
    obtain ⟨hpr, hpy⟩ := hp p h
    have hd : 0 < y / p := Nat.div_pos_iff.mpr ⟨hpr.pos, hpy⟩
    exact Finsupp.mem_support_iff.mpr (hd.trans_le (hδ p hpr hpy)).ne'
  have hsum : (y : ℝ) / 2 * (∑ p ∈ P, Real.log p / (p : ℝ)) ≤ Real.log y.factorial := by
    rw [Finset.mul_sum, Real.log_nat_eq_sum_factorization, Finsupp.sum]
    calc ∑ p ∈ P, (y : ℝ) / 2 * (Real.log p / (p : ℝ))
        ≤ ∑ p ∈ P, (y.factorial.factorization p : ℝ) * Real.log p := by
          refine Finset.sum_le_sum (fun p h => ?_)
          have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
          calc (y : ℝ) / 2 * (Real.log p / (p : ℝ)) = ((y : ℝ) / (2 * p)) * Real.log p := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (hcase p h) hlog
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ =>
        mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
  have hlogle : Real.log (y.factorial : ℝ) ≤ (y : ℝ) * Real.log y := by
    have h := Real.log_le_log (Nat.cast_pos.mpr (Nat.factorial_pos y))
      (show (y.factorial : ℝ) ≤ (y : ℝ)^y by exact_mod_cast Nat.factorial_le_pow y)
    simpa only [Real.log_pow] using h
  have hyR : (0 : ℝ) < y := Nat.cast_pos.mpr hy
  have h := hsum.trans hlogle
  apply (le_of_mul_le_mul_left · (by positivity : (0 : ℝ) < (y : ℝ) / 2))
  linarith only [h]


lemma coprime_period (k n : ℕ) : k.Coprime (n + k) ↔ k.Coprime n := by
  change k.gcd (n + k) = 1 ↔ k.gcd n = 1
  rw [Nat.gcd_add_self_right]

lemma density_coprime {k : ℕ} (hk : 0 < k) :
    {n | k.Coprime n}.HasDensity ((k.totient : ℝ) / k) := by
  have h := density_periodic {n | k.Coprime n} hk (coprime_period k)
  have he : {n | k.Coprime n} ∩ Set.Iio k =
      (↑((Finset.Ico 0 k).filter (fun n => k.Coprime n)) : Set ℕ) := by
    ext n
    simp [and_comm]
  rw [he, Set.ncard_coe_finset] at h
  have hcard := Nat.filter_coprime_Ico_eq_totient k 0
  rw [Nat.zero_add] at hcard
  rwa [hcard] at h

lemma density_coprime_inter_dvd {d k : ℕ} (hd : 0 < d) (hk : 0 < k) (hkd : k.Coprime d) :
    {n | k.Coprime n ∧ d ∣ n}.HasDensity ((k.totient : ℝ) / k / d) := by
  let A : Set ℕ := {n | k.Coprime n}
  have heq : (fun n => d * n) '' A = {n | k.Coprime n ∧ d ∣ n} := by
    ext n
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨Nat.coprime_mul_iff_right.mpr ⟨hkd, hm⟩, dvd_mul_right d m⟩
    · rintro ⟨hn, m, rfl⟩
      exact ⟨m, (Nat.coprime_mul_iff_right.mp hn).2, rfl⟩
  have h := density_periodic_mul_image A hk hd (coprime_period k)
  rw [heq] at h
  rw [tendsto_nhds_unique (density_periodic A hk (coprime_period k)) (density_coprime hk)] at h
  exact h

def blockPrimes (y K : ℕ) : Finset ℕ :=
  ((Finset.range (K + 1)).filter Nat.Prime).filter (fun p => y < p)

def blockModulus (y K : ℕ) : ℕ := ∏ p ∈ blockPrimes y K, p

lemma mem_blockPrimes {p y K : ℕ} :
    p ∈ blockPrimes y K ↔ p.Prime ∧ y < p ∧ p ≤ K := by
  simp only [blockPrimes, Finset.mem_filter, Finset.mem_range_succ_iff]
  tauto

lemma blockModulus_pos (y K : ℕ) : 0 < blockModulus y K :=
  Finset.prod_pos (fun _ h => (mem_blockPrimes.mp h).1.pos)

lemma blockModulus_primeFactors (y K : ℕ) :
    (blockModulus y K).primeFactors = blockPrimes y K :=
  Nat.primeFactors_prod (fun _ h => (mem_blockPrimes.mp h).1)

lemma sum_block_prime_reciprocals {y D : ℕ} (hy : 2 ≤ y) :
    ∑ p ∈ blockPrimes y (y^D), (1 : ℝ) / p ≤ 2 * (D : ℝ) := by
  have hylog : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hK : 0 < y^D := Nat.pow_pos (by omega)
  apply (le_of_mul_le_mul_left · hylog)
  rw [Finset.mul_sum]
  calc (∑ p ∈ blockPrimes y (y^D), Real.log (y : ℝ) * (1 / (p : ℝ)))
      ≤ ∑ p ∈ blockPrimes y (y^D), Real.log (p : ℝ) / p := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hyp := (mem_blockPrimes.mp hp).2.1
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right
          (Real.log_le_log (by positivity : (0 : ℝ) < y) (Nat.cast_le.mpr hyp.le)) (Nat.cast_nonneg _)
    _ ≤ ∑ p ∈ (Finset.range (y^D + 1)).filter Nat.Prime, Real.log (p : ℝ) / p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ =>
        div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _))
    _ ≤ 2 * Real.log ((y^D : ℕ) : ℝ) := sum_prime_log_div_le _ hK
    _ = Real.log (y : ℝ) * (2 * (D : ℝ)) := by rw [Nat.cast_pow, Real.log_pow]; ring

lemma block_ratio_eq_product (y K : ℕ) :
    ((blockModulus y K).totient : ℝ) / blockModulus y K =
      ∏ p ∈ blockPrimes y K, (1 - 1 / (p : ℝ)) := by
  have h := congrArg (Rat.cast : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors (blockModulus y K))
  push_cast at h
  rw [blockModulus_primeFactors] at h
  rw [h, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (blockModulus_pos y K).ne')]
  simp only [one_div]

lemma exp_neg_two_mul_le_sub {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hp := Real.exp_pos (2 * x)
  rw [show -2 * x = -(2 * x) by ring, Real.exp_neg, inv_eq_one_div, div_le_iff₀ hp]
  have h₁ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (2 * x)) (by linarith : 0 ≤ 1 - x)
  have h₂ : 1 ≤ (1 - x) * (2 * x + 1) := by
    nlinarith [mul_nonneg hx (show 0 ≤ 1 - 2 * x by linarith)]
  exact h₂.trans h₁

/-- A prime-free block between y and y^D occurs with probability bounded below
uniformly in y in the periodic model. -/
lemma block_ratio_lower {y D : ℕ} (hy : 2 ≤ y) :
    Real.exp (-4 * (D : ℝ)) ≤
      ((blockModulus y (y^D)).totient : ℝ) / blockModulus y (y^D) := by
  rw [block_ratio_eq_product]
  let P := blockPrimes y (y^D)
  calc Real.exp (-4 * (D : ℝ))
      ≤ Real.exp (∑ p ∈ P, -2 * (1 / (p : ℝ))) := by
        apply Real.exp_le_exp.mpr
        rw [← Finset.mul_sum]
        linarith [sum_block_prime_reciprocals (D := D) hy]
    _ = ∏ p ∈ P, Real.exp (-2 * (1 / (p : ℝ))) := Real.exp_sum _ _
    _ ≤ ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
      apply Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_blockPrimes.mp hp).1.two_le
      have hp0 : (0 : ℝ) < p := by linarith
      exact exp_neg_two_mul_le_sub (by positivity) (by
        rw [div_le_div_iff₀ hp0 (by norm_num)]
        linarith)


lemma mem_add_period_mul {A : Set ℕ} {k : ℕ}
    (hA : ∀ n, n + k ∈ A ↔ n ∈ A) (n q : ℕ) :
    n + k * q ∈ A ↔ n ∈ A := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← Nat.add_assoc, hA, ih]

lemma mem_mod_of_period {A : Set ℕ} {k : ℕ}
    (hA : ∀ n, n + k ∈ A ↔ n ∈ A) (n : ℕ) :
    n ∈ A ↔ n % k ∈ A := by
  have h := mem_add_period_mul hA (n % k) (n / k)
  rwa [Nat.mod_add_div] at h

/-- Periodic sets with coprime periods have multiplicative intersection density. -/
lemma density_periodic_inter {A B : Set ℕ} {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (hkl : k.Coprime l) (hA : ∀ n, n + k ∈ A ↔ n ∈ A) (hB : ∀ n, n + l ∈ B ↔ n ∈ B)
    {α β : ℝ} (ha : A.HasDensity α) (hb : B.HasDensity β) :
    (A ∩ B).HasDensity (α * β) := by
  classical
  let C := A ∩ B
  let F (S : Set ℕ) (m : ℕ) := (Finset.range m).filter (fun n => n ∈ S)
  have hF (S : Set ℕ) (m : ℕ) : (F S m : Set ℕ) = S ∩ Set.Iio m := by
    ext n
    simp [F, and_comm]
  have hC (n : ℕ) : n + k * l ∈ C ↔ n ∈ C := by
    change (n + k * l ∈ A ∧ n + k * l ∈ B) ↔ n ∈ A ∧ n ∈ B
    exact and_congr (mem_add_period_mul hA n l) (by
      rw [Nat.mul_comm]
      exact mem_add_period_mul hB n k)
  have hcard : (F C (k * l)).card = (F A k).card * (F B l).card := by
    rw [← Finset.card_product]
    refine Finset.card_bij (fun n _ => (n % k, n % l)) ?_ ?_ ?_
    · intro n hn
      simp only [F, Finset.mem_filter] at hn
      obtain ⟨_, hna, hnb⟩ := hn
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hk), (mem_mod_of_period hA _).mp hna⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hl), (mem_mod_of_period hB _).mp hnb⟩⟩
    · intro n hn m hm he
      simp only [F, Finset.mem_filter] at hn hm
      have hn' := Finset.mem_range.mp hn.1
      have hm' := Finset.mem_range.mp hm.1
      have he' := (Nat.modEq_and_modEq_iff_modEq_mul hkl).mp
        ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
      change n % (k * l) = m % (k * l) at he'
      rwa [Nat.mod_eq_of_lt hn', Nat.mod_eq_of_lt hm'] at he'
    · rintro ⟨a, b⟩ hab
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      obtain ⟨hak, haA⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbl, hbB⟩ := Finset.mem_filter.mp hb
      let z := Nat.chineseRemainder hkl a b
      have hzk : (z : ℕ) % k = a := by
        have hr : (z : ℕ) % k = a % k := z.2.1
        rwa [Nat.mod_eq_of_lt (Finset.mem_range.mp hak)] at hr
      have hzl : (z : ℕ) % l = b := by
        have hr : (z : ℕ) % l = b % l := z.2.2
        rwa [Nat.mod_eq_of_lt (Finset.mem_range.mp hbl)] at hr
      have hzC : (z : ℕ) ∈ C := by
        constructor
        · apply (mem_mod_of_period hA (z : ℕ)).mpr
          rwa [hzk]
        · apply (mem_mod_of_period hB (z : ℕ)).mpr
          rwa [hzl]
      refine ⟨z, ?_, Prod.ext hzk hzl⟩
      simp only [F, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (Nat.chineseRemainder_lt_mul hkl a b hk.ne' hl.ne'), hzC⟩
  have ha' := tendsto_nhds_unique ha (density_periodic A hk hA)
  have hb' := tendsto_nhds_unique hb (density_periodic B hl hB)
  rw [ha', hb']
  have ht := density_periodic C (Nat.mul_pos hk hl) hC
  rw [← hF C, Set.ncard_coe_finset, hcard, Nat.cast_mul, Nat.cast_mul] at ht
  rw [← hF A, ← hF B, Set.ncard_coe_finset, Set.ncard_coe_finset, div_mul_div_comm]
  exact ht


lemma pd_eq_indicator (A : Set ℕ) (b : ℕ) :
    A.partialDensity Set.univ b =
      (∑ n ∈ Finset.range b, (open scoped Classical in if n ∈ A then (1 : ℝ) else 0)) / b := by
  classical
  have hF : (↑((Finset.range b).filter (fun n => n ∈ A)) : Set ℕ) = A ∩ Set.Iio b := by
    ext n
    simp [and_comm]
  rw [pd_nat, ← hF, Set.ncard_coe_finset, ← Finset.sum_filter]
  simp

lemma weighted_density_bound {ι : Type*} {I : Finset ι} {A : ι → Set ℕ} {B : Set ℕ}
    {a w : ι → ℝ} {β : ℝ} (ha : ∀ i ∈ I, (A i).HasDensity (a i)) (hβ : B.HasDensity β)
    (hw : ∀ i ∈ I, 0 ≤ w i)
    (hCover : ∀ n ∈ B, 1 ≤ ∑ i ∈ I, (open scoped Classical in if n ∈ A i then w i else 0)) :
    β ≤ ∑ i ∈ I, w i * a i := by
  classical
  have ht := tendsto_finsetSum I (fun i hi => (ha i hi).const_mul (w i))
  apply le_of_tendsto_of_tendsto' hβ ht
  intro b
  simp only [pd_eq_indicator, ← mul_div_assoc]
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have he (i : ι) : w i * (∑ n ∈ Finset.range b, if n ∈ A i then (1 : ℝ) else 0) =
      ∑ n ∈ Finset.range b, if n ∈ A i then w i else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    split <;> simp
  have hsum : ∑ i ∈ I, w i * (∑ n ∈ Finset.range b, if n ∈ A i then (1 : ℝ) else 0) =
      ∑ n ∈ Finset.range b, ∑ i ∈ I, if n ∈ A i then w i else 0 := by
    simp only [he]
    exact Finset.sum_comm
  rw [hsum]
  refine Finset.sum_le_sum (fun n _ => ?_)
  by_cases hn : n ∈ B
  · simpa only [if_pos hn] using hCover n hn
  · rw [if_neg hn]
    exact Finset.sum_nonneg (fun i hi => by split <;> simp [hw i hi])


lemma block_coprime_small_prime {p y K : ℕ} (hp : p.Prime) (hpy : p ≤ y) :
    (blockModulus y K).Coprime p := by
  refine Nat.coprime_prod_left_iff.mpr (fun q hq => ?_)
  have hq' := mem_blockPrimes.mp hq
  exact (Nat.coprime_primes hq'.1 hp).mpr (by omega)

lemma block_core_log_le {n y K : ℕ} (hg : (blockModulus y K).Coprime n) :
    Real.log ((n.gcd K.factorial : ℕ) : ℝ) ≤
      ∑ p ∈ (Finset.range (y + 1)).filter Nat.Prime,
        ∑ i ∈ Finset.Ico 1 (K.factorial + 1), if p ^ i ∣ n then Real.log p else 0 := by
  let m := n.gcd K.factorial
  let J := Finset.Ico 1 (K.factorial + 1)
  let P := (Finset.range (y + 1)).filter Nat.Prime
  have hm : 0 < m := Nat.gcd_pos_of_pos_right n (Nat.factorial_pos _)
  have hmd : m ∣ K.factorial := Nat.gcd_dvd_right _ _
  have hmn : m ∣ n := Nat.gcd_dvd_left _ _
  have hsub : m.factorization.support ⊆ P := by
    intro p hp
    have hpf : p ∈ m.primeFactors := hp
    obtain ⟨hp', hpm, _⟩ := Nat.mem_primeFactors.mp hpf
    have hpK := hp'.dvd_factorial.mp (hpm.trans hmd)
    have hpy : p ≤ y := by
      by_contra! hlt
      have hpd : p ∣ blockModulus y K :=
        Finset.dvd_prod_of_mem _ (mem_blockPrimes.mpr ⟨hp', hlt, hpK⟩)
      exact (hp'.coprime_iff_not_dvd.mp (hg.coprime_dvd_left hpd)) (hpm.trans hmn)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpy), hp'⟩
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc (∑ p ∈ m.factorization.support, (m.factorization p : ℝ) * Real.log p)
      ≤ ∑ p ∈ P, (m.factorization p : ℝ) * Real.log p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
        mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p))
    _ ≤ _ := by
      refine Finset.sum_le_sum (fun p hp => ?_)
      have hp' : p.Prime := (Finset.mem_filter.mp hp).2
      have hbound : m < p ^ (K.factorial + 1) :=
        (Nat.le_of_dvd (Nat.factorial_pos _) hmd).trans_lt
          ((Nat.lt_succ_self _).trans (Nat.lt_pow_self hp'.one_lt))
      rw [Nat.factorization_eq_card_pow_dvd_of_lt hp' hm hbound]
      change (((J.filter (fun i => p ^ i ∣ m)).card : ℕ) : ℝ) * Real.log p ≤
        ∑ i ∈ J, if p ^ i ∣ n then Real.log p else 0
      rw [← Finset.sum_filter]
      have hsum : (((J.filter (fun i => p ^ i ∣ m)).card : ℕ) : ℝ) * Real.log p =
          ∑ _ ∈ J.filter (fun i => p ^ i ∣ m), Real.log p := by simp
      rw [hsum]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Real.log_natCast_nonneg p)
      intro i hi
      obtain ⟨hiJ, hid⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨hiJ, hid.trans hmn⟩

lemma sum_inv_prime_powers_le {p J : ℕ} (hp : p.Prime) (hJ : 1 ≤ J) :
    ∑ i ∈ Finset.Ico 1 J, (1 : ℝ) / (p : ℝ)^i ≤ 2 / (p : ℝ) := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hx : (1 : ℝ) / p ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hp0 (by norm_num)]
    linarith
  have hpos : 0 < 1 - (1 : ℝ) / p := by linarith
  have he : (∑ i ∈ Finset.Ico 1 J, (1 : ℝ) / (p : ℝ)^i) =
      ∑ i ∈ Finset.Ico 1 J, ((1 : ℝ) / p)^i :=
    Finset.sum_congr rfl (fun i _ => by rw [div_pow, one_pow])
  rw [he, geom_sum_Ico' (by linarith : (1 : ℝ) / p ≠ 1) hJ, pow_one, div_le_iff₀ hpos]
  have hmul := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ 1 - 1 / p by linarith)
    (show (0 : ℝ) ≤ 2 / p by positivity)
  have hz : 0 ≤ ((1 : ℝ) / p) ^ J := by positivity
  rw [show (2 : ℝ) / p * (1 / 2) = 1 / p by ring] at hmul
  linarith

/-- Even conditional on a prime-free block, an excessively large small-prime
part has proportion at most 4 / C. -/
lemma block_large_core_density {y K C : ℕ} (hy : 2 ≤ y) (hC : 0 < C) :
    ∃ β : ℝ, {n | (blockModulus y K).Coprime n ∧ y ^ C < n.gcd K.factorial}.HasDensity β ∧
      β ≤ (((blockModulus y K).totient : ℝ) / blockModulus y K) * (4 / C) := by
  classical
  let k := blockModulus y K
  let P := (Finset.range (y + 1)).filter Nat.Prime
  let J := Finset.Ico 1 (K.factorial + 1)
  let A : ℕ × ℕ → Set ℕ := fun v => {n | k.Coprime n ∧ v.1 ^ v.2 ∣ n}
  let B : Set ℕ := {n | k.Coprime n ∧ y ^ C < n.gcd K.factorial}
  let α : ℝ := (k.totient : ℝ) / k
  let R : ℝ := (C : ℝ) * Real.log y
  let w : ℕ × ℕ → ℝ := fun v => Real.log v.1 / R
  have hk : 0 < k := blockModulus_pos _ _
  have hlog : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hR : 0 < R := mul_pos (Nat.cast_pos.mpr hC) hlog
  have hB (n : ℕ) : n + k * K.factorial ∈ B ↔ n ∈ B := by
    change (k.Coprime (n + k * K.factorial) ∧ y ^ C < (n + k * K.factorial).gcd K.factorial) ↔
      k.Coprime n ∧ y ^ C < n.gcd K.factorial
    have hp := mem_add_period_mul (A := {n | k.Coprime n}) (coprime_period k) n K.factorial
    have hq := mem_add_period_mul (A := {n | y ^ C < n.gcd K.factorial})
      (k := K.factorial) (fun n => by simp) n k
    rw [Nat.mul_comm K.factorial k] at hq
    exact and_congr hp hq
  let β : ℝ := ((B ∩ Set.Iio (k * K.factorial)).ncard : ℝ) / (k * K.factorial : ℕ)
  have hβ : B.HasDensity β := density_periodic B (Nat.mul_pos hk (Nat.factorial_pos _)) hB
  refine ⟨β, hβ, ?_⟩
  have hAd (v : ℕ × ℕ) (hv : v ∈ P ×ˢ J) : (A v).HasDensity (α / (v.1 : ℝ)^v.2) := by
    obtain ⟨hvP, _⟩ := Finset.mem_product.mp hv
    obtain ⟨hvy, hpr⟩ := Finset.mem_filter.mp hvP
    have hvy' := Nat.le_of_lt_succ (Finset.mem_range.mp hvy)
    have hco := block_coprime_small_prime (K := K) hpr hvy'
    simpa only [Nat.cast_pow] using density_coprime_inter_dvd (pow_pos hpr.pos _) hk (hco.pow_right v.2)
  have hs : β ≤ ∑ v ∈ P ×ˢ J, w v * (α / (v.1 : ℝ)^v.2) := by
    apply weighted_density_bound hAd hβ (fun v _ => div_nonneg (Real.log_natCast_nonneg _) hR.le)
    intro n hn
    obtain ⟨hnk, hnsize⟩ := hn
    change k.Coprime n at hnk
    have h := block_core_log_le (y := y) (K := K) hnk
    have hlt : R < Real.log ((n.gcd K.factorial : ℕ) : ℝ) := by
      have hcast : ((y ^ C : ℕ) : ℝ) < (n.gcd K.factorial : ℕ) := by exact_mod_cast hnsize
      have hh := Real.log_lt_log (by positivity : 0 < ((y ^ C : ℕ) : ℝ)) hcast
      simpa only [Nat.cast_pow, Real.log_pow, R] using hh
    rw [Finset.sum_product]
    have he : ((∑ p ∈ P, ∑ i ∈ J, if p ^ i ∣ n then Real.log (p : ℝ) else 0) / R) =
        ∑ p ∈ P, ∑ i ∈ J, @ite ℝ (n ∈ A (p, i)) (Classical.propDecidable _) (w (p, i)) 0 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hi : p ^ i ∣ n
      · have ha : n ∈ A (p, i) := ⟨hnk, hi⟩
        simp [hi, ha, w]
      · have ha : n ∉ A (p, i) := fun h => hi h.2
        simp [hi, ha]
    have hratio : 1 ≤ (∑ p ∈ P, ∑ i ∈ J, if p ^ i ∣ n then Real.log (p : ℝ) else 0) / R := by
      rw [le_div_iff₀ hR, one_mul]
      exact (hlt.trans_le h).le
    exact hratio.trans_eq he
  have hα : 0 ≤ α := by positivity
  have hscale : 0 ≤ α / R := div_nonneg hα hR.le
  refine hs.trans ?_
  rw [Finset.sum_product]
  calc (∑ p ∈ P, ∑ i ∈ J, w (p, i) * (α / (p : ℝ)^i))
      = (α / R) * ∑ p ∈ P, Real.log p * ∑ i ∈ J, (1 : ℝ) / (p : ℝ)^i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [← mul_assoc, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by dsimp [w]; ring)
    _ ≤ (α / R) * ∑ p ∈ P, Real.log p * (2 / (p : ℝ)) := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p hp => ?_)) hscale
      exact mul_le_mul_of_nonneg_left
        (sum_inv_prime_powers_le (Finset.mem_filter.mp hp).2 (by omega)) (Real.log_natCast_nonneg p)
    _ = (α / R) * (2 * ∑ p ∈ P, Real.log p / (p : ℝ)) := by
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    _ ≤ (α / R) * (2 * (2 * Real.log y)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sum_prime_log_div_le y (by omega)) (by norm_num)) hscale
    _ = α * (4 / C) := by
      dsimp [R]
      field_simp
      <;> ring


lemma pd_biUnion_le_sum {ι : Type*} (F : Finset ι) (A : ι → Set ℕ) (b : ℕ) :
    (⋃ i ∈ F, A i).partialDensity Set.univ b ≤ ∑ i ∈ F, (A i).partialDensity Set.univ b := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [Set.partialDensity]
  | insert i F hi ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hi]
    exact (pd_union_le _ _ b).trans (add_le_add le_rfl ih)

lemma density_compl {A : Set ℕ} {α : ℝ} (h : A.HasDensity α) : Aᶜ.HasDensity (1 - α) := by
  simpa only [Set.compl_eq_univ_sdiff] using
    hasDensity_diff (Set.subset_univ A) Set.HasDensity.univ_nat_hasDensity_one h

/-- Avoiding finitely many periodic sets with pairwise coprime periods
has density given by the product of the individual avoidance densities. -/
lemma density_periodic_avoid {ι : Type*} (F : Finset ι) {A : ι → Set ℕ} {k : ι → ℕ} {α : ι → ℝ}
    (hk : ∀ i ∈ F, 0 < k i)
    (hco : (F : Set ι).Pairwise (fun i j => (k i).Coprime (k j)))
    (hp : ∀ i ∈ F, ∀ n, n + k i ∈ A i ↔ n ∈ A i)
    (ha : ∀ i ∈ F, (A i).HasDensity (α i)) :
    {n | ∀ i ∈ F, n ∉ A i}.HasDensity (∏ i ∈ F, (1 - α i)) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simpa using Set.HasDensity.univ_nat_hasDensity_one
  | insert i F hi ih =>
    let B : Set ℕ := {n | ∀ j ∈ F, n ∉ A j}
    let l := ∏ j ∈ F, k j
    have hmem (j : ι) (hj : j ∈ F) : j ∈ insert i F := Finset.mem_insert_of_mem hj
    have hki := hk i (Finset.mem_insert_self i F)
    have hl : 0 < l := Finset.prod_pos (fun j hj => hk j (hmem j hj))
    have hB (n : ℕ) : n + l ∈ B ↔ n ∈ B := by
      change (∀ j ∈ F, n + l ∉ A j) ↔ ∀ j ∈ F, n ∉ A j
      refine forall_congr' (fun j => ?_)
      by_cases hj : j ∈ F
      · simp only [hj, true_implies]
        obtain ⟨v, hv⟩ := Finset.dvd_prod_of_mem k hj
        have hv' : l = k j * v := hv
        rw [hv']
        exact not_congr (mem_add_period_mul (hp j (hmem j hj)) n v)
      · simp [hj]
    have hF : B.HasDensity (∏ j ∈ F, (1 - α j)) :=
      ih (fun j hj => hk j (hmem j hj))
        (fun j hj t ht hne => hco (hmem j hj) (hmem t ht) hne)
        (fun j hj => hp j (hmem j hj)) (fun j hj => ha j (hmem j hj))
    have hcol : (k i).Coprime l := Nat.coprime_prod_right_iff.mpr (fun j hj =>
      hco (Finset.mem_insert_self i F) (hmem j hj) (fun he => hi (he ▸ hj)))
    have heq : {n | ∀ j ∈ insert i F, n ∉ A j} = (A i)ᶜ ∩ B := by
      ext n
      simp only [Set.mem_ofPred_eq, Finset.forall_mem_insert, Set.mem_inter_iff, Set.mem_compl_iff, B]
    rw [heq, Finset.prod_insert hi]
    exact density_periodic_inter hki hl hcol (fun n => not_congr (hp i (Finset.mem_insert_self i F) n))
      hB (density_compl (ha i (Finset.mem_insert_self i F))) hF


lemma pp_good_cutoffs : ∀ ε : ℝ, 0 < ε → ∃ F : Finset ℕ, ∀ᶠ b : ℕ in atTop,
      (badCutoffs F).partialDensity Set.univ b < ε := by
  classical
  intro ε hε
  have hev : ∀ᶠ R : ℝ in atTop, Real.exp (-R) < ε / 4 :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (by positivity))
  obtain ⟨R, hR, hRone⟩ := (hev.and (eventually_ge_atTop (1 : ℝ))).exists
  obtain ⟨C, hC⟩ := exists_nat_gt (16 * (R + 1) / ε)
  have hCpos : 0 < C := Nat.cast_pos.mp (lt_of_le_of_lt (by positivity) hC)
  have hCore : (4 / (C : ℝ)) * (R + 1) < ε / 4 := by
    rw [div_lt_iff₀ hε] at hC
    rw [div_mul_eq_mul_div, div_lt_iff₀ (Nat.cast_pos.mpr hCpos)]
    nlinarith
  let a : ℝ := Real.exp (-4 * ((C + 1 : ℕ) : ℝ))
  have ha : 0 < a := Real.exp_pos _
  obtain ⟨M, hM⟩ := exists_nat_gt (R / a)
  obtain ⟨Y₀, hY₀⟩ := exists_nat_gt (8 * (M : ℝ) / ε)
  let Y := max 2 Y₀
  let y : ℕ → ℕ := Nat.rec Y (fun _ z => z ^ (C + 1))
  let K (i : ℕ) := y (i + 1)
  have hK (i : ℕ) : K i = y i ^ (C + 1) := rfl
  have hy (i : ℕ) : Y ≤ y i := by
    induction i with
    | zero => exact le_rfl
    | succ i ih => exact ih.trans (Nat.le_self_pow (by omega) (y i))
  have hy2 (i : ℕ) : 2 ≤ y i := (le_max_left 2 Y₀).trans (hy i)
  have hstrict : StrictMono y := strictMono_nat_of_lt_succ (fun i => by
    change y i < K i
    rw [hK]
    have hh : y i < y i ^ 2 := by
      rw [pow_two]
      simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left
        (show 1 < y i from hy2 i) (show 0 < y i by have := hy2 i; omega)
    exact hh.trans_le (Nat.pow_le_pow_right (by have := hy2 i; omega) (by omega)))
  let k (i : ℕ) := blockModulus (y i) (K i)
  let A (i : ℕ) : Set ℕ := {n | (k i).Coprime n}
  let α (i : ℕ) : ℝ := ((k i).totient : ℝ) / k i
  have hk (i : ℕ) : 0 < k i := blockModulus_pos _ _
  have hα (i : ℕ) : (A i).HasDensity (α i) := density_coprime (hk i)
  have hlo (i : ℕ) : a ≤ α i := by
    dsimp [a, α, k]
    rw [hK]
    exact block_ratio_lower (D := C + 1) (hy2 i)
  have hhi (i : ℕ) : α i ≤ 1 :=
    Set.HasDensity.mono (Set.subset_univ _) (hα i) Set.HasDensity.univ_nat_hasDensity_one
  have hcop : ∀ i j : ℕ, i < j → (k i).Coprime (k j) := by
    intro i j hij
    apply Nat.coprime_prod_left_iff.mpr
    intro p hp
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    obtain ⟨hpp, _, hpi⟩ := mem_blockPrimes.mp hp
    obtain ⟨hqp, hqj, _⟩ := mem_blockPrimes.mp hq
    exact (Nat.coprime_primes hpp hqp).mpr
      ((hpi.trans ((hstrict.monotone (Nat.succ_le_of_lt hij)) : K i ≤ y j)).trans_lt hqj).ne
  have hsumM : R ≤ ∑ i ∈ Finset.range M, α i := by
    have ht := (div_lt_iff₀ ha).mp hM
    exact ht.le.trans (by
      simpa using Finset.sum_le_sum (s := Finset.range M) (fun i _ => hlo i))
  have hex : ∃ N : ℕ, R ≤ ∑ i ∈ Finset.range N, α i := ⟨M, hsumM⟩
  let N := Nat.find hex
  let I := Finset.range N
  have hN : R ≤ ∑ i ∈ I, α i := Nat.find_spec hex
  have hNM : N ≤ M := Nat.find_min' hex hsumM
  have hNup : ∑ i ∈ I, α i ≤ R + 1 := by
    have hNp : N ≠ 0 := by
      intro h
      have hh := hN
      simp [I, h] at hh
      linarith
    obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero hNp
    have hbefore : ¬ R ≤ ∑ i ∈ Finset.range u, α i := Nat.find_min hex (by omega)
    simp only [I, hu, Nat.succ_eq_add_one, Finset.sum_range_succ]
    linarith [lt_of_not_ge hbefore, hhi u]
  let Miss : Set ℕ := {n | ∀ i ∈ I, n ∉ A i}
  have hMiss : Miss.HasDensity (∏ i ∈ I, (1 - α i)) :=
    density_periodic_avoid I (fun i _ => hk i)
      (fun i _ j _ hij => (lt_or_gt_of_ne hij).elim (hcop i j) (fun h => (hcop j i h).symm))
      (fun i _ => coprime_period (k i)) (fun i _ => hα i)
  have hMissBound : ∏ i ∈ I, (1 - α i) < ε / 4 := by
    calc (∏ i ∈ I, (1 - α i)) ≤ ∏ i ∈ I, Real.exp (-α i) := by
          apply Finset.prod_le_prod (fun i _ => sub_nonneg.mpr (hhi i))
          intro i _
          linarith [Real.add_one_le_exp (-α i)]
      _ = Real.exp (-(∑ i ∈ I, α i)) := by rw [← Real.exp_sum, Finset.sum_neg_distrib]
      _ ≤ Real.exp (-R) := Real.exp_le_exp.mpr (neg_le_neg hN)
      _ < ε / 4 := hR
  let Large (i : ℕ) : Set ℕ := {n | (k i).Coprime n ∧ y i ^ C < n.gcd (K i).factorial}
  choose β hβ hβle using fun i : ℕ => block_large_core_density (K := K i) (hy2 i) hCpos
  have hsumβ : ∑ i ∈ I, β i < ε / 4 := by
    calc (∑ i ∈ I, β i) ≤ ∑ i ∈ I, α i * (4 / (C : ℝ)) :=
          Finset.sum_le_sum (fun i _ => hβle i)
      _ ≤ (R + 1) * (4 / (C : ℝ)) := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right hNup (by positivity)
      _ < ε / 4 := by rwa [mul_comm]
  let δ (i : ℕ) : ℝ := 1 / (2 * ((y i ^ C : ℕ) : ℝ))
  let Tail (i : ℕ) : Set ℕ := {n | δ i < abundancyTail (K i) n}
  have hyR (i : ℕ) : 0 < (Nat.cast (y i) : ℝ) := by
    exact_mod_cast (show 0 < y i by have := hy2 i; omega)
  have hpowR (i : ℕ) : 0 < ((y i ^ C : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
    exact pow_pos (hyR i) C
  have hδ (i : ℕ) : 0 < δ i := one_div_pos.mpr (mul_pos (by norm_num) (hpowR i))
  have hTail (i b : ℕ) : (Tail i).partialDensity Set.univ b ≤ 2 / (Y : ℝ) := by
    refine (pd_abundancyTail_le (K i) b (by have := hy2 (i + 1); exact (by omega : 1 ≤ y (i + 1)))
      (hδ i)).trans ?_
    have he : 1 / ((Nat.cast (K i) : ℝ) * δ i) = 2 / (Nat.cast (y i) : ℝ) := by
      dsimp [δ]
      rw [hK, pow_succ, Nat.cast_mul]
      have hne := (hpowR i).ne'
      have hny := (hyR i).ne'
      field_simp
      <;> ring
    rw [he]
    exact div_le_div_of_nonneg_left (by norm_num)
      (Nat.cast_pos.mpr (by dsimp [Y]; omega)) (Nat.cast_le.mpr (hy i))
  have hTailSum (b : ℕ) : ∑ i ∈ I, (Tail i).partialDensity Set.univ b < ε / 4 := by
    calc (∑ i ∈ I, (Tail i).partialDensity Set.univ b) ≤ ∑ i ∈ I, 2 / (Y : ℝ) :=
          Finset.sum_le_sum (fun i _ => hTail i b)
      _ ≤ (M : ℝ) * (2 / (Y : ℝ)) := by
        simp only [I, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hNM) (by positivity)
      _ < ε / 4 := by
        have hY : (8 : ℝ) * M / ε < Y := hY₀.trans_le (Nat.cast_le.mpr (le_max_right 2 Y₀))
        rw [div_lt_iff₀ hε] at hY
        rw [← mul_div_assoc, div_lt_iff₀ (Nat.cast_pos.mpr (by dsimp [Y]; omega))]
        nlinarith
  refine ⟨I.image K, ?_⟩
  have hcov : badCutoffs (I.image K) ⊆ Miss ∪ ((⋃ i ∈ I, Large i) ∪ (⋃ i ∈ I, Tail i)) := by
    intro n hn
    by_cases hmiss : n ∈ Miss
    · exact Or.inl hmiss
    · right
      have hhit : ∃ i ∈ I, n ∈ A i := by
        by_contra! hf
        exact hmiss hf
      obtain ⟨i, hi, hAi⟩ := hhit
      by_cases hL : y i ^ C < n.gcd (K i).factorial
      · exact Or.inl (Set.mem_iUnion₂.mpr ⟨i, hi, hAi, hL⟩)
      · right
        apply Set.mem_iUnion₂.mpr
        refine ⟨i, hi, ?_⟩
        by_contra! hT
        have hbad := hn.2 (K i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
        have hsize : ((n.gcd (K i).factorial : ℕ) : ℝ) ≤ ((y i ^ C : ℕ) : ℝ) :=
          Nat.cast_le.mpr (le_of_not_gt hL)
        have hu : ((n.gcd (K i).factorial : ℕ) : ℝ) * abundancyTail (K i) n
            ≤ ((y i ^ C : ℕ) : ℝ) * δ i :=
          mul_le_mul hsize (le_of_not_gt hT) (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
        have hhalf : ((y i ^ C : ℕ) : ℝ) * δ i = 1 / 2 := by
          dsimp [δ]
          have hne := (hpowR i).ne'
          field_simp
        linarith
  have hsumLim : Tendsto (fun b : ℕ => ∑ i ∈ I, (Large i).partialDensity Set.univ b) atTop
      (𝓝 (∑ i ∈ I, β i)) := tendsto_finsetSum I (fun i _ => hβ i)
  filter_upwards [hMiss.eventually (gt_mem_nhds hMissBound),
    hsumLim.eventually (gt_mem_nhds hsumβ)] with b hb hbl
  have hu := (pd_mono_nat hcov b).trans (pd_union_le _ _ b)
  have hv := pd_union_le (⋃ i ∈ I, Large i) (⋃ i ∈ I, Tail i) b
  linarith [pd_biUnion_le_sum I Large b, pd_biUnion_le_sum I Tail b, hTailSum b]

end OMA470

theorem OMA.solution : type_of% @Erdos470.erdos_470.variants.weird_pos_density := by
  have h1 : ∃ α : ℝ, OMA470.ND.HasDensity α := OMA470.ND_density
  have h2 : ∃ β : ℝ, OMA470.PP.HasDensity β := by
    exact OMA470.pp_density_of_good_cutoffs OMA470.pp_good_cutoffs
  have h3 : ∃ c : ℝ, 0 < c ∧
      ∀ᶠ b : ℕ in Filter.atTop, c ≤ {n : ℕ | n.Weird}.partialDensity Set.univ b := by
    exact OMA470.h3_of_T OMA470.hT_main
  exact OMA470.glue h1 h2 h3
