import FormalConjectures.ErdosProblems.«329»

-- Problem: Erdős Problem 329: Maximum Density of Sidon Sets (warm-up: a Sidon set with positive upper density)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/329.lean:111 (declaration Erdos329.exists_sidon_pos_density)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- This formalises a classical fact (Erdős; the Erdős–Turán / Bose quadratic-residue construction glued over
-- sparse scales). No new mathematical result is claimed.
-- Proof idea: for an odd prime p the set {2pa + (a^2 mod p) + t : a < p} is Sidon (Erdős–Turán), has p
-- elements, consecutive gaps larger than p, and lies in [t, t + 2p^2). Starting from the empty set, append
-- at stage n such a block with t = 4p^2 + 1 and p larger than everything built so far. A short case split
-- shows each union stays Sidon, so the union A of all stages is Sidon. At N = 6p^2 the block alone gives
-- |A ∩ [1, N]| >= p >= sqrt(N) / 3. A trivial difference count (a - b distinct over ordered pairs) bounds the
-- normalised count by 2, so the limsup is a genuine limsup and is at least 1/3.

open Filter

namespace OMAProof329

-- Adapted from the accepted open-math-agents proof proofs/Erdos44.sidon_set_lower_bound.lean
-- (lemma bosePrefix_sidon), generalised from the shift 1 to an arbitrary shift t.
lemma bose_sidon {p k t : ℕ} (hp : Nat.Prime p) (hk : k < p) (hp2 : p ≠ 2) :
    IsSidon
      (((Finset.range (k + 1)).image (fun a => 2 * p * a + (a * a) % p + t) : Finset ℕ) :
        Set ℕ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  rw [Finset.mem_coe, Finset.mem_image] at hi₁ hj₁ hi₂ hj₂
  obtain ⟨a, ha, rfl⟩ := hi₁
  obtain ⟨c, hc, rfl⟩ := hj₁
  obtain ⟨b, hb, rfl⟩ := hi₂
  obtain ⟨d, hd, rfl⟩ := hj₂
  have ha_lt : a < p := by rw [Finset.mem_range] at ha; omega
  have hb_lt : b < p := by rw [Finset.mem_range] at hb; omega
  have hc_lt : c < p := by rw [Finset.mem_range] at hc; omega
  have hd_lt : d < p := by rw [Finset.mem_range] at hd; omega
  have hpos : 0 < p := hp.pos
  have hsum' :
      2 * p * (a + b) + ((a * a) % p + (b * b) % p) =
        2 * p * (c + d) + ((c * c) % p + (d * d) % p) := by
    have hcancel :
        2 * p * a + (a * a) % p + (2 * p * b + (b * b) % p) =
          2 * p * c + (c * c) % p + (2 * p * d + (d * d) % p) := by
      omega
    calc
      2 * p * (a + b) + ((a * a) % p + (b * b) % p)
          = 2 * p * a + (a * a) % p + (2 * p * b + (b * b) % p) := by ring
      _ = 2 * p * c + (c * c) % p + (2 * p * d + (d * d) % p) := hcancel
      _ = 2 * p * (c + d) + ((c * c) % p + (d * d) % p) := by ring
  have hσ : (a * a) % p + (b * b) % p < 2 * p := by
    have haσ : (a * a) % p < p := Nat.mod_lt _ hpos
    have hbσ : (b * b) % p < p := Nat.mod_lt _ hpos
    omega
  have hτ : (c * c) % p + (d * d) % p < 2 * p := by
    have hcτ : (c * c) % p < p := Nat.mod_lt _ hpos
    have hdτ : (d * d) % p < p := Nat.mod_lt _ hpos
    omega
  have htwo : 0 < 2 * p := by omega
  have hquot (q r : ℕ) (hr : r < 2 * p) :
      (r + (2 * p) * q) / (2 * p) = q := by
    rw [Nat.add_mul_div_left _ _ htwo, Nat.div_eq_of_lt hr, zero_add]
  have hidx : a + b = c + d := by
    have hleft := hquot (a + b) ((a * a) % p + (b * b) % p) hσ
    have hright := hquot (c + d) ((c * c) % p + (d * d) % p) hτ
    have hcomm :
        (a * a) % p + (b * b) % p + (2 * p) * (a + b) =
          (c * c) % p + (d * d) % p + (2 * p) * (c + d) := by
      calc
        (a * a) % p + (b * b) % p + (2 * p) * (a + b)
            = (2 * p) * (a + b) + ((a * a) % p + (b * b) % p) := by ac_rfl
        _ = (2 * p) * (c + d) + ((c * c) % p + (d * d) % p) := hsum'
        _ = (c * c) % p + (d * d) % p + (2 * p) * (c + d) := by ac_rfl
    rw [← hleft, ← hright, hcomm]
  have hres :
      (a * a) % p + (b * b) % p = (c * c) % p + (d * d) % p :=
    Nat.add_left_cancel (n := 2 * p * (a + b)) (by simpa [hidx] using hsum')
  have hsq :
      (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = (c : ZMod p) ^ 2 + (d : ZMod p) ^ 2 := by
    calc
      (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2
          = (((a * a) % p : ℕ) : ZMod p) + (((b * b) % p : ℕ) : ZMod p) := by
            simp [pow_two, ZMod.natCast_mod]
      _ = ((((a * a) % p + (b * b) % p : ℕ) : ZMod p)) := by
            push_cast
            rfl
      _ = ((((c * c) % p + (d * d) % p : ℕ) : ZMod p)) := by
            exact congr_arg (Nat.cast : ℕ → ZMod p) hres
      _ = (c : ZMod p) ^ 2 + (d : ZMod p) ^ 2 := by
            simp [pow_two, ZMod.natCast_mod]
  have hsumZ : (a : ZMod p) + b = (c : ZMod p) + d := by
    have : ((a + b : ℕ) : ZMod p) = (c + d : ℕ) := congr_arg (Nat.cast : ℕ → ZMod p) hidx
    simpa [Nat.cast_add] using this
  have htwo_mul :
      (2 : ZMod p) * (a : ZMod p) * b = (2 : ZMod p) * (c : ZMod p) * d := by
    have hleft : (2 : ZMod p) * a * b = ((a : ZMod p) + b) ^ 2 - ((a : ZMod p) ^ 2 + b ^ 2) := by
      ring
    have hright : (2 : ZMod p) * c * d = ((c : ZMod p) + d) ^ 2 - ((c : ZMod p) ^ 2 + d ^ 2) := by
      ring
    rw [hleft, hright, hsumZ, hsq]
  have htwo_ne : (2 : ZMod p) ≠ 0 := by
    rw [ne_eq, ← Nat.cast_two, ZMod.natCast_eq_zero_iff]
    intro hdiv
    have : p ≤ 2 := Nat.le_of_dvd (by decide) hdiv
    have : 2 ≤ p := hp.two_le
    omega
  have hprod : (a : ZMod p) * b = (c : ZMod p) * d := by
    apply mul_left_cancel₀ htwo_ne
    simpa [mul_assoc, mul_left_comm, mul_comm] using htwo_mul
  have hfactor : ((c : ZMod p) - a) * ((c : ZMod p) - b) = 0 := by
    calc
      ((c : ZMod p) - a) * (c - b)
          = (c : ZMod p) ^ 2 - ((a : ZMod p) + b) * c + a * b := by ring
      _ = (c : ZMod p) ^ 2 - ((c : ZMod p) + d) * c + c * d := by rw [hsumZ, hprod]
      _ = 0 := by ring
  have hc_eq : (c : ZMod p) = a ∨ (c : ZMod p) = b := by
    rcases mul_eq_zero.mp hfactor with hca | hcb
    · left
      exact sub_eq_zero.mp hca
    · right
      exact sub_eq_zero.mp hcb
  have lift {x y : ℕ} (hx : x < p) (hy : y < p) (hxy : (x : ZMod p) = y) : x = y := by
    have hmod : x % p = y % p := (ZMod.natCast_eq_natCast_iff' x y p).mp hxy
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hmod
  rcases hc_eq with hca | hcb
  · have hac : a = c := lift ha_lt hc_lt hca.symm
    have hbd : b = d := by omega
    left
    subst hac
    subst hbd
    exact ⟨rfl, rfl⟩
  · have hab : b = c := lift hb_lt hc_lt hcb.symm
    have had : a = d := by omega
    right
    subst hab
    subst had
    exact ⟨rfl, rfl⟩

/-- Gluing a Sidon block `C`, sitting high above a Sidon set `B` and with gaps at least `s`,
keeps the Sidon property. -/
lemma union_sidon (B C : Set ℕ) (s M W : ℕ) (hB : IsSidon B) (hC : IsSidon C)
    (hBs : ∀ b ∈ B, b < s) (hCM : ∀ c ∈ C, M ≤ c ∧ c < M + W)
    (h1 : W + s ≤ M) (h2 : 2 * s ≤ M)
    (hgap : ∀ c ∈ C, ∀ c' ∈ C, c = c' ∨ c + s ≤ c' ∨ c' + s ≤ c) :
    IsSidon (B ∪ C) := by
  have key : ∀ x ∈ B ∪ C, (x ∈ B ∧ x < s) ∨ (x ∈ C ∧ M ≤ x ∧ x < M + W) := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl ⟨hx, hBs x hx⟩
    · exact Or.inr ⟨hx, hCM x hx⟩
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hs
  rcases key _ hi₁ with ⟨m1, b1⟩ | ⟨m1, b1, b1'⟩ <;>
  rcases key _ hj₁ with ⟨m2, b2⟩ | ⟨m2, b2, b2'⟩ <;>
  rcases key _ hi₂ with ⟨m3, b3⟩ | ⟨m3, b3, b3'⟩ <;>
  rcases key _ hj₂ with ⟨m4, b4⟩ | ⟨m4, b4, b4'⟩ <;>
  first
  | exact hB _ m1 _ m2 _ m3 _ m4 hs
  | exact hC _ m1 _ m2 _ m3 _ m4 hs
  | omega
  | (have g := hgap _ m1 _ m2; omega)
  | (have g := hgap _ m1 _ m4; omega)
  | (have g := hgap _ m3 _ m2; omega)
  | (have g := hgap _ m3 _ m4; omega)

/-- The block used for the prime `p`. -/
def blk (p : ℕ) : Finset ℕ :=
  (Finset.range (p - 1 + 1)).image (fun a => 2 * p * a + (a * a) % p + (4 * p * p + 1))

lemma blk_gap (p a b : ℕ) (hp : 0 < p) (hab : a < b) :
    2 * p * a + (a * a) % p + (4 * p * p + 1) + p ≤ 2 * p * b + (b * b) % p + (4 * p * p + 1) := by
  have h1 : 2 * p * (a + 1) ≤ 2 * p * b := Nat.mul_le_mul_left _ hab
  have h2 : (a * a) % p < p := Nat.mod_lt _ hp
  have h3 : 2 * p * (a + 1) = 2 * p * a + 2 * p := by ring
  omega

lemma blk_mem (p x : ℕ) (hp : 0 < p) (hx : x ∈ blk p) :
    4 * p * p + 1 ≤ x ∧ x < 4 * p * p + 1 + 2 * p * p := by
  unfold blk at hx
  rw [Finset.mem_image] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  rw [Finset.mem_range] at ha
  have h1 : 2 * p * (a + 1) ≤ 2 * p * p := Nat.mul_le_mul_left _ (by omega)
  have h2 : (a * a) % p < p := Nat.mod_lt _ hp
  have h3 : 2 * p * (a + 1) = 2 * p * a + 2 * p := by ring
  omega

lemma blk_sidon (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : IsSidon (blk p : Set ℕ) :=
  bose_sidon hp (by have := hp.pos; omega) hp2

lemma blk_card (p : ℕ) (hp : 0 < p) : (blk p).card = p := by
  unfold blk
  rw [Finset.card_image_of_injOn, Finset.card_range]
  · omega
  · intro a _ b _ hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := blk_gap p a b hp h
      simp only at hab
      omega
    · have := blk_gap p b a hp h
      simp only at hab
      omega

lemma blk_gaps (p : ℕ) (hp : 0 < p) :
    ∀ c ∈ (blk p : Set ℕ), ∀ c' ∈ (blk p : Set ℕ), c = c' ∨ c + p ≤ c' ∨ c' + p ≤ c := by
  intro c hc c' hc'
  rw [Finset.mem_coe] at hc hc'
  unfold blk at hc hc'
  rw [Finset.mem_image] at hc hc'
  obtain ⟨a, _, rfl⟩ := hc
  obtain ⟨b, _, rfl⟩ := hc'
  rcases lt_trichotomy a b with h | h | h
  · exact Or.inr (Or.inl (blk_gap p a b hp h))
  · exact Or.inl (by rw [h])
  · exact Or.inr (Or.inr (blk_gap p b a hp h))

/-- A prime at least `s + 3`. -/
noncomputable def prm (s : ℕ) : ℕ := Classical.choose (Nat.exists_infinite_primes (s + 3))

lemma prm_spec (s : ℕ) : s + 3 ≤ prm s ∧ (prm s).Prime :=
  Classical.choose_spec (Nat.exists_infinite_primes (s + 3))

/-- The stages of the construction. -/
noncomputable def F : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => F n ∪ blk (prm ((F n).sup id + n + 1))

/-- The prime used at stage `n`. -/
noncomputable def P (n : ℕ) : ℕ := prm ((F n).sup id + n + 1)

lemma F_succ (n : ℕ) : F (n + 1) = F n ∪ blk (P n) := rfl

lemma P_ge (n : ℕ) : (F n).sup id + n + 4 ≤ P n := (prm_spec _).1

lemma P_prime (n : ℕ) : (P n).Prime := (prm_spec _).2

lemma F_sidon (n : ℕ) : IsSidon (F n : Set ℕ) := by
  induction n with
  | zero =>
    intro i₁ hi₁
    simp [F] at hi₁
  | succ n ih =>
    rw [F_succ, Finset.coe_union]
    have hp := P_prime n
    have hge := P_ge n
    have hp0 : 0 < P n := hp.pos
    have hpp : P n ≤ P n * P n := Nat.le_mul_self _
    refine union_sidon _ _ (P n) (4 * P n * P n + 1) (2 * P n * P n) ih
      (blk_sidon _ hp (by omega)) ?_ (fun c hc => blk_mem _ c hp0 hc) (by nlinarith)
      (by nlinarith) (blk_gaps _ hp0)
    intro b hb
    have := Finset.le_sup (f := id) (Finset.mem_coe.mp hb)
    simp only [id] at this
    omega

lemma F_mono : Monotone F := by
  apply monotone_nat_of_le_succ
  intro n
  rw [F_succ]
  exact Finset.subset_union_left

/-- The Sidon set. -/
def A : Set ℕ := ⋃ n, (F n : Set ℕ)

lemma A_sidon : IsSidon A := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hs
  simp only [A, Set.mem_iUnion] at hi₁ hj₁ hi₂ hj₂
  obtain ⟨n1, h1⟩ := hi₁
  obtain ⟨n2, h2⟩ := hj₁
  obtain ⟨n3, h3⟩ := hi₂
  obtain ⟨n4, h4⟩ := hj₂
  have sub : ∀ m, m ≤ max (max n1 n2) (max n3 n4) →
      (F m : Set ℕ) ⊆ (F (max (max n1 n2) (max n3 n4)) : Set ℕ) :=
    fun m hm => Finset.coe_subset.mpr (F_mono hm)
  exact F_sidon _ _ (sub n1 (by omega) h1) _ (sub n2 (by omega) h2) _ (sub n3 (by omega) h3) _
    (sub n4 (by omega) h4) hs

/-- Trivial upper bound: a Sidon set has at most `2 √N` elements in `[1, N]`. -/
lemma card_le (S : Finset ℕ) (N : ℕ) (hS : S ⊆ Finset.Icc 1 N) (hs : IsSidon (S : Set ℕ)) :
    S.card * S.card ≤ 4 * N := by
  have hk : S.card ≤ N := by
    have := Finset.card_le_card hS
    rw [Nat.card_Icc] at this
    omega
  have hinj : S.offDiag.card ≤ (Finset.Icc (-(N : ℤ)) N).card := by
    refine Finset.card_le_card_of_injOn (fun q => (q.1 : ℤ) - q.2) ?_ ?_
    · intro q hq
      rw [Finset.mem_coe, Finset.mem_offDiag] at hq
      obtain ⟨h1, h2, _⟩ := hq
      have a1 := Finset.mem_Icc.mp (hS h1)
      have a2 := Finset.mem_Icc.mp (hS h2)
      rw [Finset.mem_coe, Finset.mem_Icc]
      show -(N : ℤ) ≤ (q.1 : ℤ) - q.2 ∧ (q.1 : ℤ) - q.2 ≤ N
      constructor <;> omega
    · intro q hq r hr hqr
      rw [Finset.mem_coe, Finset.mem_offDiag] at hq hr
      simp only at hqr
      have hsum : q.1 + r.2 = r.1 + q.2 := by omega
      rcases hs _ hq.1 _ hr.1 _ hr.2.1 _ hq.2.1 hsum with h | h
      · exact Prod.ext h.1 h.2.symm
      · exact absurd h.1 (by rw [h.2] at hqr; omega)
  rw [Finset.offDiag_card, Int.card_Icc] at hinj
  have : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
  rw [this] at hinj
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    have : S.card = 0 := by omega
    rw [this]
  · have : S.card ≤ S.card * S.card := Nat.le_mul_self _
    omega

open Erdos329

lemma density_le (N : ℕ) : sqrtPartialDensity A N ≤ 2 := by
  classical
  unfold sqrtPartialDensity
  set S : Finset ℕ := (Finset.Icc 1 N).filter (· ∈ A) with hSdef
  have hset : A ∩ Set.Icc 1 N = (S : Set ℕ) := by
    ext x
    rw [Set.mem_inter_iff, Set.mem_Icc, Finset.mem_coe, hSdef, Finset.mem_filter, Finset.mem_Icc]
    tauto
  rw [hset, Set.ncard_coe_finset]
  have hsub : S ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
  have hsid : IsSidon (S : Set ℕ) :=
    Set.IsSidon.subset A_sidon (fun x hx => (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2)
  have hc := card_le S N hsub hsid
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  · have hNr : (0 : ℝ) < N := by exact_mod_cast hpos
    have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
    rw [div_le_iff₀ hsq]
    have hcR : ((S.card : ℝ)) ^ 2 ≤ 4 * N := by
      have : ((S.card * S.card : ℕ) : ℝ) ≤ ((4 * N : ℕ) : ℝ) := by exact_mod_cast hc
      push_cast at this
      nlinarith
    have hs2 : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt (le_of_lt hNr)
    have h0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    nlinarith

lemma density_freq (n : ℕ) : ∃ N ≥ n, (1 : ℝ) / 3 ≤ sqrtPartialDensity A N := by
  have hp := P_prime n
  have hge := P_ge n
  have hp0 : 0 < P n := hp.pos
  refine ⟨6 * P n * P n, ?_, ?_⟩
  · have : P n ≤ P n * P n := Nat.le_mul_self _
    nlinarith
  unfold sqrtPartialDensity
  have hsub : (blk (P n) : Set ℕ) ⊆ A ∩ Set.Icc 1 (6 * P n * P n) := by
    intro x hx
    refine ⟨Set.mem_iUnion.mpr ⟨n + 1, ?_⟩, ?_⟩
    · rw [F_succ, Finset.coe_union]
      exact Or.inr hx
    · have := blk_mem _ x hp0 (Finset.mem_coe.mp hx)
      constructor <;> nlinarith
  have hfin : (A ∩ Set.Icc 1 (6 * P n * P n)).Finite :=
    (Set.finite_Icc _ _).subset Set.inter_subset_right
  have hcard := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, blk_card _ hp0] at hcard
  have hcR : (P n : ℝ) ≤ ((A ∩ Set.Icc 1 (6 * P n * P n)).ncard : ℝ) := by exact_mod_cast hcard
  have hpR : (0 : ℝ) < P n := by exact_mod_cast hp0
  have hNr : (0 : ℝ) < ((6 * P n * P n : ℕ) : ℝ) := by push_cast; positivity
  have hsq : 0 < Real.sqrt ((6 * P n * P n : ℕ) : ℝ) := Real.sqrt_pos.mpr hNr
  have hle : Real.sqrt ((6 * P n * P n : ℕ) : ℝ) ≤ 3 * P n := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    push_cast
    nlinarith
  rw [le_div_iff₀ hsq]
  linarith

end OMAProof329

theorem OMA.solution : type_of% @Erdos329.exists_sidon_pos_density := by
  refine ⟨OMAProof329.A, OMAProof329.A_sidon, ?_⟩
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun N => Erdos329.sqrtPartialDensity OMAProof329.A N) :=
    isBoundedUnder_of ⟨2, OMAProof329.density_le⟩
  have hf : ∃ᶠ N in atTop, (1 : ℝ) / 3 ≤ Erdos329.sqrtPartialDensity OMAProof329.A N := by
    rw [frequently_atTop]
    exact OMAProof329.density_freq
  have := le_limsup_of_frequently_le hf hb
  unfold Erdos329.sidonUpperDensity
  linarith
