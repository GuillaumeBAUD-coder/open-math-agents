import FormalConjectures.ErdosProblems.«817»

-- Problem: Erdős Problem 817 — bdd_power
-- Declaration Erdos817.erdos_817.variants.bdd_power
-- Proof: the subset sums of A are 3-AP-free, so the 3^n sums with coefficients in {0,1,2}
-- are pairwise distinct (Erdős–Sárközy), giving 3^n ≤ 2 n N + 1; powers of 4 are a witness.

open Filter

lemma oma_ap3 {x y z : ℕ} (h : x + z = 2 * y) (hxy : x < y) :
    ({x, y, z} : Set ℕ).IsAPOfLength 3 := by
  refine ⟨x, y - x, ?_, ?_⟩
  · have hyz : y < z := by omega
    change ({x, y, z} : Set ℕ).encard = 3
    rw [Set.encard_insert_of_notMem (by simp; omega), Set.encard_pair (by omega)]
    rfl
  · ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, smul_eq_mul]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by ring⟩
      · exact ⟨1, by norm_num, by omega⟩
      · exact ⟨2, by norm_num, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      have hk' : k < 3 := by exact_mod_cast hk
      interval_cases k
      · left; ring
      · right; left; omega
      · right; right; omega

lemma oma_pow4_bound (δ : ℕ → ℤ) (hδ : ∀ i, -2 ≤ δ i ∧ δ i ≤ 2) (n : ℕ) :
    3 * |∑ i ∈ Finset.range n, δ i * 4 ^ i| ≤ 2 * 4 ^ n - 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 := abs_add_le (∑ i ∈ Finset.range n, δ i * 4 ^ i) (δ n * 4 ^ n)
    have h2 : |δ n * 4 ^ n| ≤ 2 * 4 ^ n := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℤ) < 4 ^ n)]
      have := hδ n
      exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) (by positivity)
    rw [pow_succ]
    linarith

lemma oma_pow4 (δ : ℕ → ℤ) (hδ : ∀ i, -2 ≤ δ i ∧ δ i ≤ 2) (n : ℕ)
    (h0 : ∑ i ∈ Finset.range n, δ i * 4 ^ i = 0) : ∀ i < n, δ i = 0 := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    rw [Finset.sum_range_succ] at h0
    have hb := oma_pow4_bound δ hδ n
    have hn : δ n = 0 := by
      by_contra hne
      have hpos : (0:ℤ) < 4 ^ n := by positivity
      have : 4 ^ n ≤ |δ n * 4 ^ n| := by
        rw [abs_mul, abs_of_pos hpos]
        have : (1:ℤ) ≤ |δ n| := Int.one_le_abs hne
        nlinarith
      have he : |∑ i ∈ Finset.range n, δ i * 4 ^ i| = |δ n * 4 ^ n| := by
        rw [show ∑ i ∈ Finset.range n, δ i * 4 ^ i = -(δ n * 4 ^ n) by linarith, abs_neg]
      linarith
    rw [hn, zero_mul, add_zero] at h0
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ih h0 i hi
    · exact hn

lemma oma_key (A : Finset ℕ) (hpos : ∀ a ∈ A, 1 ≤ a)
    (hfree : ∀ X Y Z : Finset A,
      (∑ a ∈ X, ((a : ℕ) : ℤ)) + (∑ a ∈ Z, ((a : ℕ) : ℤ)) = 2 * ∑ a ∈ Y, ((a : ℕ) : ℤ) →
      (∑ a ∈ X, ((a : ℕ) : ℤ)) = ∑ a ∈ Y, ((a : ℕ) : ℤ))
    (δ : A → ℤ) (hδ : ∀ a, -2 ≤ δ a ∧ δ a ≤ 2) (h0 : ∑ a : A, δ a * ((a : ℕ) : ℤ) = 0) :
    ∀ a, δ a = 0 := by
  classical
  have hfilt : ∀ P : A → Prop, ∀ [DecidablePred P],
      ∑ a ∈ Finset.univ.filter P, ((a : ℕ) : ℤ) = ∑ a : A, if P a then ((a : ℕ) : ℤ) else 0 :=
    fun P _ => Finset.sum_filter _ _
  have hzero : ∀ c : ℤ, (∑ a : A, if δ a = c then ((a : ℕ) : ℤ) else 0) = 0 → ∀ a, δ a ≠ c := by
    intro c hc a ha
    have hnn : ∀ b ∈ (Finset.univ : Finset A), 0 ≤ (if δ b = c then ((b : ℕ) : ℤ) else 0) := by
      intro b _; split_ifs <;> positivity
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hc a (Finset.mem_univ _)
    rw [if_pos ha] at this
    have h1 := hpos a a.2
    omega
  set p2 := ∑ a : A, if δ a = 2 then ((a : ℕ) : ℤ) else 0 with hp2
  set p1 := ∑ a : A, if δ a = 1 then ((a : ℕ) : ℤ) else 0 with hp1
  set n1 := ∑ a : A, if δ a = -1 then ((a : ℕ) : ℤ) else 0 with hn1
  set n2 := ∑ a : A, if δ a = -2 then ((a : ℕ) : ℤ) else 0 with hn2
  have hrel : 2 * p2 + p1 - n1 - 2 * n2 = 0 := by
    rw [← h0, hp2, hp1, hn1, hn2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    have := hδ a
    have : δ a = -2 ∨ δ a = -1 ∨ δ a = 0 ∨ δ a = 1 ∨ δ a = 2 := by omega
    rcases this with h | h | h | h | h <;> simp [h]
  -- choice (a): X = P2 ∪ P1, Y = N1 ∪ N2, Z = P2 ∪ N1
  have ha := hfree (Finset.univ.filter fun a => δ a = 2 ∨ δ a = 1)
    (Finset.univ.filter fun a => δ a = -1 ∨ δ a = -2)
    (Finset.univ.filter fun a => δ a = 2 ∨ δ a = -1)
  have hb := hfree (Finset.univ.filter fun a => δ a = 2)
    (Finset.univ.filter fun a => δ a = -1 ∨ δ a = -2)
    (Finset.univ.filter fun a => δ a = 2 ∨ δ a = 1 ∨ δ a = -1)
  simp only [hfilt] at ha hb
  have hor2 : ∀ c d : ℤ, c ≠ d → (∑ a : A, if δ a = c ∨ δ a = d then ((a : ℕ) : ℤ) else 0) =
      (∑ a : A, if δ a = c then ((a : ℕ) : ℤ) else 0) +
        ∑ a : A, if δ a = d then ((a : ℕ) : ℤ) else 0 := by
    intro c d hcd
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h1 : δ a = c
    · have : δ a ≠ d := fun h => hcd (h1 ▸ h)
      simp [h1, hcd]
    · by_cases h2 : δ a = d <;> simp [h1, h2, hcd.symm]
  have hor3 : (∑ a : A, if δ a = 2 ∨ δ a = 1 ∨ δ a = -1 then ((a : ℕ) : ℤ) else 0) =
      p2 + p1 + n1 := by
    rw [hp2, hp1, hn1, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h1 : δ a = 2
    · simp [h1]
    · by_cases h2 : δ a = 1
      · simp [h2]
      · by_cases h3 : δ a = -1 <;> simp [h1, h2, h3]
  rw [hor2 2 1 (by norm_num), hor2 (-1) (-2) (by norm_num), hor2 2 (-1) (by norm_num)] at ha
  rw [hor2 (-1) (-2) (by norm_num), hor3] at hb
  simp only [← hp2, ← hp1, ← hn1, ← hn2] at ha hb
  have ea := ha (by linarith)
  have eb := hb (by linarith)
  have hp1z : p1 = 0 := by linarith
  have hn1z : n1 = 0 := by linarith
  -- choice (e): X = ∅, Y = P2, Z = P2 ∪ N2
  have he := hfree ∅ (Finset.univ.filter fun a => δ a = 2)
    (Finset.univ.filter fun a => δ a = 2 ∨ δ a = -2)
  simp only [hfilt, Finset.sum_empty] at he
  rw [hor2 2 (-2) (by norm_num)] at he
  simp only [← hp2, ← hn2] at he
  have ee := he (by linarith)
  have hp2z : p2 = 0 := by linarith
  have hn2z : n2 = 0 := by linarith
  intro a
  have := hδ a
  have h2 := hzero 2 hp2z a
  have h1 := hzero 1 hp1z a
  have h3 := hzero (-1) hn1z a
  have h4 := hzero (-2) hn2z a
  omega

lemma oma_hfree (A : Finset ℕ)
    (hA : ∀ s, s ⊆ { ∑ a ∈ B, a | B ∈ A.powerset } → s.IsAPOfLengthFree 3) :
    ∀ X Y Z : Finset A,
      (∑ a ∈ X, ((a : ℕ) : ℤ)) + (∑ a ∈ Z, ((a : ℕ) : ℤ)) = 2 * ∑ a ∈ Y, ((a : ℕ) : ℤ) →
      (∑ a ∈ X, ((a : ℕ) : ℤ)) = ∑ a ∈ Y, ((a : ℕ) : ℤ) := by
  intro X Y Z h
  have hmem : ∀ W : Finset A, ∑ a ∈ W, (a : ℕ) ∈ { ∑ a ∈ B, a | B ∈ A.powerset } := by
    intro W
    refine ⟨W.map (Function.Embedding.subtype _), ?_, ?_⟩
    · rw [Finset.mem_powerset]
      intro b hb
      rw [Finset.mem_map] at hb
      obtain ⟨a, _, rfl⟩ := hb
      exact a.2
    · rw [Finset.sum_map]
      rfl
  push_cast [← Nat.cast_sum] at h ⊢
  norm_cast at h ⊢
  set x := ∑ a ∈ X, (a : ℕ)
  set y := ∑ a ∈ Y, (a : ℕ)
  set z := ∑ a ∈ Z, (a : ℕ)
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hs : ({x, y, z} : Set ℕ) ⊆ { ∑ a ∈ B, a | B ∈ A.powerset } := by
      intro w hw
      rcases hw with rfl | rfl | rfl
      · exact hmem X
      · exact hmem Y
      · exact hmem Z
    have := hA _ hs _ subset_rfl (oma_ap3 h hlt)
    exact absurd this (by decide)
  · have hs : ({z, y, x} : Set ℕ) ⊆ { ∑ a ∈ B, a | B ∈ A.powerset } := by
      intro w hw
      rcases hw with rfl | rfl | rfl
      · exact hmem Z
      · exact hmem Y
      · exact hmem X
    have := hA _ hs _ subset_rfl (oma_ap3 (by omega) (by omega))
    exact absurd this (by decide)

lemma oma_count (A : Finset ℕ) (N : ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (hfree : ∀ X Y Z : Finset A,
      (∑ a ∈ X, ((a : ℕ) : ℤ)) + (∑ a ∈ Z, ((a : ℕ) : ℤ)) = 2 * ∑ a ∈ Y, ((a : ℕ) : ℤ) →
      (∑ a ∈ X, ((a : ℕ) : ℤ)) = ∑ a ∈ Y, ((a : ℕ) : ℤ)) :
    3 ^ A.card ≤ 2 * A.card * N + 1 := by
  have hpos : ∀ a ∈ A, 1 ≤ a := fun a ha => (Finset.mem_Icc.mp (hA ha)).1
  have hle : ∀ a ∈ A, a ≤ N := fun a ha => (Finset.mem_Icc.mp (hA ha)).2
  let Φ : (A → Fin 3) → ℕ := fun ε => ∑ a : A, (ε a : ℕ) * (a : ℕ)
  have hΦle : ∀ ε, Φ ε < 2 * A.card * N + 1 := by
    intro ε
    have : Φ ε ≤ ∑ _a : A, 2 * N := by
      apply Finset.sum_le_sum
      intro a _
      have h1 : (ε a : ℕ) ≤ 2 := by omega
      exact Nat.mul_le_mul h1 (hle a a.2)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul] at this
    nlinarith
  have hinj : Function.Injective Φ := by
    intro ε ε' he
    have h0 : ∑ a : A, (((ε a : ℕ) : ℤ) - ((ε' a : ℕ) : ℤ)) * ((a : ℕ) : ℤ) = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      have : ((Φ ε : ℕ) : ℤ) = ((Φ ε' : ℕ) : ℤ) := by rw [he]
      simp only [Φ] at this
      push_cast at this
      linarith
    have hz := oma_key A hpos hfree _ (fun a => by constructor <;> omega) h0
    funext a
    have := hz a
    apply Fin.ext
    omega
  have := Fintype.card_le_of_injective (fun ε => (⟨Φ ε, hΦle ε⟩ : Fin (2 * A.card * N + 1)))
    (fun ε ε' h => hinj (by simpa using h))
  simpa [Fintype.card_fun, Fintype.card_coe] using this

lemma oma_pow_free (n : ℕ) (X Y Z : Finset ℕ)
    (hX : X ⊆ (Finset.range n).image (fun i => 4 ^ i))
    (hY : Y ⊆ (Finset.range n).image (fun i => 4 ^ i))
    (hZ : Z ⊆ (Finset.range n).image (fun i => 4 ^ i))
    (h : ∑ b ∈ X, b + ∑ b ∈ Z, b = 2 * ∑ b ∈ Y, b) : ∑ b ∈ X, b = ∑ b ∈ Y, b := by
  classical
  have hinj : Function.Injective (fun i : ℕ => 4 ^ i) := Nat.pow_right_injective (by norm_num)
  have hrep : ∀ B ⊆ (Finset.range n).image (fun i => 4 ^ i),
      ∑ b ∈ B, b = ∑ i ∈ Finset.range n, if 4 ^ i ∈ B then 4 ^ i else 0 := by
    intro B hB
    rw [← Finset.sum_filter]
    have hBeq : B = ((Finset.range n).filter (fun i => 4 ^ i ∈ B)).image (fun i => 4 ^ i) := by
      ext b
      constructor
      · intro hb
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hB hb)
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hb⟩, rfl⟩
      · intro hb
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
        exact (Finset.mem_filter.mp hi).2
    conv_lhs => rw [hBeq]
    rw [Finset.sum_image (fun i _ j _ hij => hinj hij)]
  rw [hrep X hX, hrep Y hY, hrep Z hZ] at h
  rw [hrep X hX, hrep Y hY]
  let δ : ℕ → ℤ := fun i => (if 4 ^ i ∈ X then 1 else 0) + (if 4 ^ i ∈ Z then 1 else 0) -
    2 * (if 4 ^ i ∈ Y then 1 else 0)
  have hδ : ∀ i, -2 ≤ δ i ∧ δ i ≤ 2 := by
    intro i
    simp only [δ]
    split_ifs <;> norm_num
  have h0 : ∑ i ∈ Finset.range n, δ i * 4 ^ i = 0 := by
    have hz : ((∑ i ∈ Finset.range n, if 4 ^ i ∈ X then 4 ^ i else 0 : ℕ) : ℤ) +
        ((∑ i ∈ Finset.range n, if 4 ^ i ∈ Z then 4 ^ i else 0 : ℕ) : ℤ) -
        2 * ((∑ i ∈ Finset.range n, if 4 ^ i ∈ Y then 4 ^ i else 0 : ℕ) : ℤ) = 0 := by
      rw [← Nat.cast_add, h]; push_cast; ring
    rw [← hz]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [δ]
    split_ifs <;> ring
  have hall := oma_pow4 δ hδ n h0
  apply Finset.sum_congr rfl
  intro i hi
  have := hall i (Finset.mem_range.mp hi)
  simp only [δ] at this
  by_cases h1 : 4 ^ i ∈ X <;> by_cases h2 : 4 ^ i ∈ Y <;> by_cases h3 : 4 ^ i ∈ Z <;>
    simp [h1, h2, h3] at this ⊢

lemma oma_witness (n : ℕ) : ∀ s, s ⊆ { ∑ a ∈ B, a | B ∈ ((Finset.range n).image
    (fun i => 4 ^ i)).powerset } → s.IsAPOfLengthFree 3 := by
  intro s hs t ht hAP
  exfalso
  obtain ⟨a, d, hcard, heq⟩ := hAP
  have hcard' : t.encard = 3 := hcard
  have m0 : a ∈ t := by rw [heq]; exact ⟨0, by norm_num, by simp⟩
  have m1 : a + d ∈ t := by rw [heq]; exact ⟨1, by norm_num, by simp⟩
  have m2 : a + 2 * d ∈ t := by rw [heq]; exact ⟨2, by norm_num, by simp⟩
  have hd : d ≠ 0 := by
    rintro rfl
    have hsub : t ⊆ {a} := by
      intro w hw
      rw [heq] at hw
      obtain ⟨k, _, rfl⟩ := hw
      simp
    have := Set.encard_le_encard hsub
    rw [Set.encard_singleton, hcard'] at this
    exact absurd this (by decide)
  obtain ⟨X, hX, hXs⟩ := hs (ht m0)
  obtain ⟨Y, hY, hYs⟩ := hs (ht m1)
  obtain ⟨Z, hZ, hZs⟩ := hs (ht m2)
  rw [Finset.mem_powerset] at hX hY hZ
  have := oma_pow_free n X Y Z hX hY hZ (by rw [hXs, hYs, hZs]; ring)
  omega

theorem OMA.solution : type_of% @Erdos817.erdos_817.variants.bdd_power := by
  refine ⟨1, one_pos, ?_⟩
  have hmain : ∀ n : ℕ, 3 ^ n ≤ 2 * n * Erdos817.g 3 n + 1 := by
    intro n
    have hne : { N | ∃ A ⊆ Finset.Icc 1 N, A.card = n ∧
        ∀ s, s ⊆ { ∑ a ∈ B, a | B ∈ A.powerset } → s.IsAPOfLengthFree 3}.Nonempty := by
      refine ⟨4 ^ n, (Finset.range n).image (fun i => 4 ^ i), ?_, ?_, oma_witness n⟩
      · intro b hb
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
        have := Finset.mem_range.mp hi
        exact Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ (by norm_num),
          Nat.pow_le_pow_right (by norm_num) this.le⟩
      · rw [Finset.card_image_of_injective _ (Nat.pow_right_injective (by norm_num)),
          Finset.card_range]
    obtain ⟨A, hA, hcard, hfree⟩ := Nat.sInf_mem hne
    have := oma_count A _ hA (oma_hfree A hfree)
    rw [hcard] at this
    exact this
  apply Asymptotics.IsBigO.of_bound 4
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h := hmain n
  have h3 : (2 : ℕ) ≤ 3 ^ n := by
    calc 2 ≤ 3 ^ 1 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hR : (3 : ℝ) ^ n ≤ 4 * n * (Erdos817.g 3 n : ℝ) := by
    have : (3 ^ n : ℕ) ≤ 4 * n * Erdos817.g 3 n := by
      have e1 : 2 * n * Erdos817.g 3 n = 2 * (n * Erdos817.g 3 n) := by ring
      have e2 : 4 * n * Erdos817.g 3 n = 4 * (n * Erdos817.g 3 n) := by ring
      rw [e1] at h
      rw [e2]
      omega
    exact_mod_cast this
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity), div_le_iff₀ hnpos]
  linarith
