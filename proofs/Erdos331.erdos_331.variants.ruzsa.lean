import FormalConjectures.ErdosProblems.«331»
import Mathlib.Analysis.PSeries

/-!
# The Ruzsa variant of Erdős Problem 331

The disjoint-block argument is adapted from Theorem 4 of Erdős and Freud,
*On disjoint sets of differences* (1984), pp. 108–109.
-/

-- Credit: @ysanatomic

open Filter
open scoped Asymptotics Topology BigOperators Classical


private theorem counting_ratio_tendsto (A : Set ℕ) {c : ℝ}
    (h : (fun n : ℕ ↦ (Nat.count (· ∈ A) n : ℝ)) ~[atTop]
      (fun n : ℕ ↦ c * (n : ℝ) ^ (1 / 2 : ℝ))) :
    Tendsto (fun n : ℕ ↦ (Nat.count (· ∈ A) n : ℝ) / Real.sqrt n) atTop (𝓝 c) := by
  obtain ⟨φ, hφ, heq⟩ := h.exists_eq_mul
  have ht : Tendsto (fun n : ℕ ↦ φ n * c) atTop (𝓝 c) := by
    simpa only [one_mul] using hφ.mul_const c
  refine ht.congr' ?_
  filter_upwards [heq, eventually_ge_atTop (1 : ℕ)] with n hn hnpos
  have hs : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  change (Nat.count (· ∈ A) n : ℝ) = φ n * (c * (n : ℝ) ^ (1 / 2 : ℝ)) at hn
  rw [hn, ← Real.sqrt_eq_rpow, ← mul_assoc, mul_div_cancel_right₀ _ hs]

private theorem card_interval_cast (A : Set ℕ) {l u : ℕ} (hlu : l ≤ u) :
    ((Finset.Ico l u).filter (· ∈ A)).card =
      (Nat.count (· ∈ A) u : ℝ) - (Nat.count (· ∈ A) l : ℝ) := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  have hsub : ((Finset.range l).filter (· ∈ A)) ⊆ ((Finset.range u).filter (· ∈ A)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨hx.1.trans_le hlu, hx.2⟩
  have hfilter :
      ((Finset.range u).filter (· ∈ A)) \ ((Finset.range l).filter (· ∈ A)) =
        (Finset.Ico l u).filter (· ∈ A) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    by_cases hx : x ∈ A <;> simp [hx]
    omega
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [hfilter] at hcard
  apply eq_sub_of_add_eq
  exact_mod_cast hcard

private theorem scaled_count_limit (A : Set ℕ) {c : ℝ} (k : ℕ) (hk : 0 < k)
    (h : Tendsto (fun n : ℕ ↦ (Nat.count (· ∈ A) n : ℝ) / Real.sqrt n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ ↦ (Nat.count (· ∈ A) (k * n) : ℝ) / Real.sqrt n)
      atTop (𝓝 (c * Real.sqrt k)) := by
  have hk₁ : 1 ≤ k := hk
  have ht : Tendsto (fun n : ℕ ↦ k * n) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by simpa using Nat.mul_le_mul_right n hk₁) tendsto_id
  apply ((h.comp ht).mul_const (Real.sqrt k)).congr
  intro n
  change (Nat.count (· ∈ A) (k * n) : ℝ) / Real.sqrt (↑(k * n) : ℝ) * Real.sqrt k =
    (Nat.count (· ∈ A) (k * n) : ℝ) / Real.sqrt n
  rw [Nat.cast_mul, Real.sqrt_mul (by positivity : 0 ≤ (k : ℝ))]
  have hk' : Real.sqrt k ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hk))
  rw [div_mul_eq_mul_div₀, mul_comm _ (Real.sqrt k), mul_div_mul_left _ _ hk']

private theorem block_limit (A : Set ℕ) {c : ℝ}
    (h : Tendsto (fun n : ℕ ↦ (Nat.count (· ∈ A) n : ℝ) / Real.sqrt n) atTop (𝓝 c))
    (i : ℕ) :
    Tendsto
      (fun n : ℕ ↦ (((Finset.Ico ((i + 1) * n) ((i + 2) * n)).filter (· ∈ A)).card : ℝ) /
        Real.sqrt n)
      atTop (𝓝 (c * (Real.sqrt ((i : ℝ) + 2) - Real.sqrt ((i : ℝ) + 1)))) := by
  have hdiff := (scaled_count_limit A (i + 2) (by omega) h).sub
    (scaled_count_limit A (i + 1) (by omega) h)
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, ← mul_sub] at hdiff
  apply hdiff.congr
  intro n
  rw [card_interval_cast A (Nat.mul_le_mul_right _ (by omega)), sub_div]

/-- Distinct signed differences bound the sum of the products of the block counts. -/
private theorem block_count (A B : Set ℕ) (M N K : ℕ) (hMN : M ≤ N)
    (hinj : ∀ a b a' b' : ℕ, a ∈ A → b ∈ B → a' ∈ A → b' ∈ B →
      M ≤ a → (a : ℤ) - (b : ℤ) = (a' : ℤ) - (b' : ℤ) → a = a' ∧ b = b') :
    (∑ i ∈ Finset.range K,
      ((Finset.Ico ((i + 1) * N) ((i + 2) * N)).filter (· ∈ A)).card *
      ((Finset.Ico ((i + 1) * N) ((i + 2) * N)).filter (· ∈ B)).card) ≤ 2 * N + 1 := by
  let block (D : Set ℕ) (i : ℕ) :=
    (Finset.Ico ((i + 1) * N) ((i + 2) * N)).filter (· ∈ D)
  let pairs (i : ℕ) := (block A i) ×ˢ (block B i)
  let allPairs := (Finset.range K).biUnion pairs
  let diff (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - (p.2 : ℤ)
  have hmem {i : ℕ} {p : ℕ × ℕ} (hp : p ∈ pairs i) :
      ((i + 1) * N ≤ p.1 ∧ p.1 < (i + 2) * N) ∧ p.1 ∈ A ∧
      ((i + 1) * N ≤ p.2 ∧ p.2 < (i + 2) * N) ∧ p.2 ∈ B := by
    simpa [pairs, block, and_assoc] using hp
  have hdisj : (↑(Finset.range K) : Set ℕ).PairwiseDisjoint pairs := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    have hi := (hmem hpi).1
    have hj := (hmem hpj).1
    rcases lt_or_gt_of_ne hij with h | h
    · have hle := Nat.mul_le_mul_right N (by omega : i + 2 ≤ j + 1)
      omega
    · have hle := Nat.mul_le_mul_right N (by omega : j + 2 ≤ i + 1)
      omega
  have hall : allPairs.card = ∑ i ∈ Finset.range K, (block A i).card * (block B i).card := by
    rw [Finset.card_biUnion hdisj]
    simp only [pairs, Finset.card_product]
  have hdiff : Set.InjOn diff (↑allPairs : Set (ℕ × ℕ)) := by
    intro p hp q hq hpq
    obtain ⟨i, _, hpi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨j, _, hqj⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hpl, hpA, _, hpB⟩ := hmem hpi
    obtain ⟨_, hqA, _, hqB⟩ := hmem hqj
    have hle : M ≤ p.1 := by
      calc
        M ≤ N := hMN
        _ = 1 * N := (one_mul N).symm
        _ ≤ (i + 1) * N := Nat.mul_le_mul_right N (by omega)
        _ ≤ p.1 := hpl.1
    obtain ⟨h₁, h₂⟩ := hinj p.1 p.2 q.1 q.2 hpA hpB hqA hqB hle hpq
    exact Prod.ext h₁ h₂
  have hbound : allPairs.image diff ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨i, _, hpi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hpa, _, hpb, _⟩ := hmem hpi
    have hend : (i + 2) * N = (i + 1) * N + N := by ring
    rw [hend] at hpa hpb
    rw [Finset.mem_Icc]
    dsimp [diff]
    omega
  change (∑ i ∈ Finset.range K, (block A i).card * (block B i).card) ≤ 2 * N + 1
  rw [← hall, ← Finset.card_image_of_injOn hdiff]
  calc
    _ ≤ (Finset.Icc (-(N : ℤ)) (N : ℤ)).card := Finset.card_le_card hbound
    _ = 2 * N + 1 := by rw [Int.card_Icc]; omega

private theorem harmonic_contradiction (d : ℝ) (hd : 0 < d)
    (h : ∀ K : ℕ,
      d * (∑ i ∈ Finset.range K,
        (Real.sqrt ((i : ℝ) + 2) - Real.sqrt ((i : ℝ) + 1)) ^ 2) ≤ 2) : False := by
  let f (i : ℕ) := (Real.sqrt ((i : ℝ) + 2) - Real.sqrt ((i : ℝ) + 1)) ^ 2
  have hf : Summable f :=
    summable_of_sum_range_le (c := 2 / d) (fun i => sq_nonneg _)
      (fun K => (le_div_iff₀ hd).mpr (by simpa only [mul_comm _ d] using h K))
  have hLower (i : ℕ) : 1 / (4 * ((i : ℝ) + 2)) ≤ f i := by
    let a := Real.sqrt ((i : ℝ) + 2)
    let b := Real.sqrt ((i : ℝ) + 1)
    have ha : a ^ 2 = (i : ℝ) + 2 := Real.sq_sqrt (by positivity)
    have hb : b ^ 2 = (i : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hba : b ≤ a := Real.sqrt_le_sqrt (by linarith)
    have hIdentity : (a - b) * (a + b) = 1 := by nlinarith
    have hProduct : 1 ≤ (a - b) * (2 * a) := by
      rw [← hIdentity]
      exact mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hba)
    apply (div_le_iff₀ (by positivity : 0 < 4 * ((i : ℝ) + 2))).mpr
    change 1 ≤ (a - b) ^ 2 * (4 * ((i : ℝ) + 2))
    calc
      1 = (1 : ℝ) ^ 2 := by norm_num
      _ ≤ ((a - b) * (2 * a)) ^ 2 := pow_le_pow_left₀ zero_le_one hProduct 2
      _ = (a - b) ^ 2 * (4 * ((i : ℝ) + 2)) := by
        rw [mul_pow, mul_pow, ha]
        norm_num
  have hSmall : Summable (fun i : ℕ => 1 / (4 * ((i : ℝ) + 2))) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hLower hf
  have hShift : Summable (fun i : ℕ => 1 / ((i + 2 : ℕ) : ℝ)) := by
    refine (hSmall.mul_left (4 : ℝ)).congr (fun i => ?_)
    push_cast
    field_simp
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 2).mp hShift)

theorem OMA.solution : type_of% @Erdos331.erdos_331.variants.ruzsa := by
  intro A B hA hB
  obtain ⟨cA, hcA, hA⟩ := hA
  obtain ⟨cB, hcB, hB⟩ := hB
  let collisions : Set (ℕ × ℕ × ℕ × ℕ) :=
    {s | let ⟨a₁, a₂, b₁, b₂⟩ := s
      a₁ ∈ A ∧ a₂ ∈ A ∧ b₁ ∈ B ∧ b₂ ∈ B ∧ a₁ ≠ a₂ ∧ a₁ + b₂ = a₂ + b₁}
  change collisions.Infinite
  by_contra h
  have hf := Set.not_infinite.mp h
  obtain ⟨C, hC⟩ : BddAbove (Prod.fst '' collisions) := (hf.image Prod.fst).bddAbove
  have hinj (a b a' b' : ℕ) (ha : a ∈ A) (hb : b ∈ B) (ha' : a' ∈ A) (hb' : b' ∈ B)
      (hCa : C + 1 ≤ a) (he : (a : ℤ) - b = (a' : ℤ) - b') :
      a = a' ∧ b = b' := by
    have he' : a + b' = a' + b := by omega
    by_cases haa : a = a'
    · exact ⟨haa, by omega⟩
    · have hs : (a, a', b, b') ∈ collisions := ⟨ha, ha', hb, hb', haa, he'⟩
      have hle : a ≤ C := hC ⟨(a, a', b, b'), hs, rfl⟩
      omega
  have htA := counting_ratio_tendsto A hA
  have htB := counting_ratio_tendsto B hB
  apply harmonic_contradiction (cA * cB) (mul_pos hcA hcB)
  intro K
  let Q (i N : ℕ) : Finset ℕ := Finset.Ico ((i+1)*N) ((i+2)*N)
  let a (i N : ℕ) : ℕ := ((Q i N).filter (· ∈ A)).card
  let b (i N : ℕ) : ℕ := ((Q i N).filter (· ∈ B)).card
  let s (i : ℕ) := Real.sqrt ((i : ℝ) + 2) - Real.sqrt ((i : ℝ) + 1)
  have hterms (i : ℕ) :
      Tendsto (fun N : ℕ ↦ (a i N : ℝ) * b i N / N)
        atTop (𝓝 ((cA * cB) * (s i)^2)) := by
    convert (block_limit A htA i).mul (block_limit B htB i) using 1
    · funext N
      simp only [a, b, Q]
      rw [div_mul_div_comm, Real.mul_self_sqrt (by positivity : 0 ≤ (N : ℝ))]
    · unfold s
      congr 1
      ring
  have hsum :
      Tendsto (fun N : ℕ ↦ ∑ i ∈ Finset.range K, (a i N : ℝ) * b i N / N)
        atTop (𝓝 ((cA * cB) * ∑ i ∈ Finset.range K, (s i)^2)) := by
    rw [Finset.mul_sum]
    exact tendsto_finsetSum _ (fun i _ ↦ hterms i)
  have hnat : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp hnat
  have htop : Tendsto (fun N : ℕ ↦ 2 + (N : ℝ)⁻¹) atTop (𝓝 (2 : ℝ)) := by
    simpa only [add_zero] using hinv.const_add (2 : ℝ)
  refine le_of_tendsto_of_tendsto hsum htop ?_
  filter_upwards [eventually_ge_atTop (C + 1)] with N hN
  have hcount : ∑ i ∈ Finset.range K, a i N * b i N ≤ 2 * N + 1 :=
    block_count A B (C+1) N K hN hinj
  have hcast : ∑ i ∈ Finset.range K, (a i N : ℝ) * b i N ≤ 2 * (N : ℝ) + 1 := by
    exact_mod_cast hcount
  have hp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  rw [← Finset.sum_div]
  calc
    _ ≤ (2 * (N : ℝ) + 1) / N := div_le_div_of_nonneg_right hcast hp.le
    _ = _ := by field_simp

