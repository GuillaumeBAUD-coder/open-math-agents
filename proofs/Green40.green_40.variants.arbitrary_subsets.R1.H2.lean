import OMAReductions.R_Green40_green_40_variants_arbitrary_subsets_R1

/-!
Proves `Green40.green_40.variants.arbitrary_subsets.R1.H2`:
`∀ r : ℕ, 0 < r → Green40.f_tilde (r + 1) ≤ 6 * Green40.f_tilde r`.

Proof outline:
1. For any `m ≥ 1`, construct the binary Hamming code `hammingCode m : Finset (𝔽₂ (2 ^ m - 1))`
   as the kernel of the parity-check map whose columns are the nonzero vectors of `𝔽₂ m`.
   Show `IsCoveringFinset (2 ^ m - 1) 1 (hammingCode m)` and `(hammingCode m).card * 2 ^ m = 2 ^ (2 ^ m - 1)`.
2. Take the direct product `V × hammingCode m ⊆ 𝔽₂ (n + (2 ^ m - 1))` of any radius-`r` covering
   finset `V ⊆ 𝔽₂ n` with `hammingCode m`, yielding a radius-`(r + 1)` covering finset of density
   at most `density(V) * |B(n + 2^m - 1, r + 1)| / (2^m * |B(n, r)|)`.
3. Choose `m(n) = Nat.clog 2 (n / (2 * (r + 1)))` so `n / (2 * (r + 1)) ≤ 2 ^ m(n) ≤ n / (r + 1)`
   for large `n`. Using `|B(N, k)| = ∑_{j ≤ k} N.choose j` and `(1 + 1 / (r + 1)) ^ (r + 1) ≤ exp 1`,
   the density ratio is eventually at most `(41 * 40 / 39 ^ 2) * 2 * exp 1 < 6`.
4. Conclude `f_tilde (r + 1) ≤ 6 * f_tilde r` by passing to `liminf` along `φ n = n + 2 ^ m(n) - 1`.
-/

namespace OMA.Proof_Green40_R1_H2

open Green40 Filter Topology
open scoped ENNReal Pointwise

private def col (m : ℕ) (i : Fin (2 ^ m - 1)) (j : Fin m) : ZMod 2 :=
  if (i.val + 1).testBit j.val then 1 else 0

private def syn (m : ℕ) : 𝔽₂ (2 ^ m - 1) →+ 𝔽₂ m where
  toFun x j := ∑ i : Fin (2 ^ m - 1), x i * col m i j
  map_zero' := by ext j; simp
  map_add' x y := by
    ext j
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private def vecToNat (m : ℕ) (s : 𝔽₂ m) : ℕ :=
  ∑ j : Fin m, (s j).val * 2 ^ j.val

private lemma zmod2_val_le_one (a : ZMod 2) : a.val ≤ 1 := by
  have := a.val_lt
  omega

private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma vecToNat_lt (m : ℕ) (s : 𝔽₂ m) : vecToNat m s < 2 ^ m := by
  unfold vecToNat
  have hle : ∑ j : Fin m, (s j).val * 2 ^ j.val ≤ ∑ j : Fin m, 2 ^ j.val := by
    apply Finset.sum_le_sum
    intro j _
    calc
      (s j).val * 2 ^ j.val ≤ 1 * 2 ^ j.val := Nat.mul_le_mul_right _ (zmod2_val_le_one (s j))
      _ = 2 ^ j.val := one_mul _
  have hsum : ∑ j : Fin m, 2 ^ j.val = 2 ^ m - 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => 2 ^ j) m]
    clear s hle
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by decide)
      omega
  have hpos : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by decide)
  omega

private lemma vecToNat_pos {m : ℕ} {s : 𝔽₂ m} (hs : s ≠ 0) : 0 < vecToNat m s := by
  have hex : ∃ j : Fin m, s j ≠ 0 := by
    by_contra h
    push Not at h
    exact hs (funext h)
  obtain ⟨j₀, hj₀⟩ := hex
  have hval : (s j₀).val = 1 := by
    rcases zmod2_eq_zero_or_one (s j₀) with h0 | h1
    · exact absurd h0 hj₀
    · rw [h1]; decide
  have hterm : 0 < (s j₀).val * 2 ^ j₀.val := by
    rw [hval, one_mul]
    exact Nat.two_pow_pos _
  exact lt_of_lt_of_le hterm
    (Finset.single_le_sum (f := fun j : Fin m => (s j).val * 2 ^ j.val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j₀))

private lemma vecToNat_testBit (m : ℕ) (s : 𝔽₂ m) (j : Fin m) :
    (vecToNat m s).testBit j.val = decide (s j = 1) := by
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
    have hsplit : vecToNat (m + 1) s = (s 0).val + 2 * vecToNat m (fun i => s i.succ) := by
      unfold vecToNat
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, ← mul_assoc,
        Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsplit]
    refine Fin.cases ?_ (fun j' => ?_) j
    · simp only [Fin.val_zero, Nat.testBit_zero]
      rcases zmod2_eq_zero_or_one (s 0) with h0 | h1
      · rw [h0]
        have hv : (0 : ZMod 2).val = 0 := rfl
        rw [hv]
        simp
      · rw [h1]
        have hv : (1 : ZMod 2).val = 1 := rfl
        rw [hv]
        have hm : (1 + 2 * vecToNat m (fun i => s i.succ)) % 2 = 1 := by omega
        simp [hm]
    · simp only [Fin.val_succ, Nat.testBit_succ]
      have hdiv : ((s 0).val + 2 * vecToNat m (fun i => s i.succ)) / 2 =
          vecToNat m (fun i => s i.succ) := by
        have := zmod2_val_le_one (s 0)
        omega
      rw [hdiv]
      exact ih (fun i => s i.succ) j'

private lemma syn_single (m : ℕ) (i : Fin (2 ^ m - 1)) :
    syn m (Pi.single i (1 : ZMod 2)) = col m i := by
  ext j
  simp only [syn, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ i) h

private lemma syn_surjective (m : ℕ) : Function.Surjective (syn m) := by
  intro s
  by_cases hs : s = 0
  · exact ⟨0, by simp [hs]⟩
  · have hpos := vecToNat_pos hs
    have hlt := vecToNat_lt m s
    let i₀ : Fin (2 ^ m - 1) := ⟨vecToNat m s - 1, by omega⟩
    refine ⟨Pi.single i₀ (1 : ZMod 2), ?_⟩
    rw [syn_single]
    ext j
    simp only [col, i₀, Nat.sub_add_cancel hpos, vecToNat_testBit]
    rcases zmod2_eq_zero_or_one (s j) with h0 | h1
    · rw [h0]; decide
    · rw [h1]; decide

private def hammingCode (m : ℕ) : Finset (𝔽₂ (2 ^ m - 1)) :=
  Finset.univ.filter fun x => syn m x = 0

private lemma hammingCode_covering (m : ℕ) :
    IsCoveringFinset (2 ^ m - 1) 1 (hammingCode m) := by
  unfold IsCoveringFinset
  ext x
  simp only [Finset.mem_univ, iff_true, Finset.mem_add]
  by_cases hs : syn m x = 0
  · refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, 0, ?_, by simp⟩
    simp [hammingBallFinset, hammingNorm_zero]
  · have hpos := vecToNat_pos hs
    have hlt := vecToNat_lt m (syn m x)
    let i₀ : Fin (2 ^ m - 1) := ⟨vecToNat m (syn m x) - 1, by omega⟩
    let e : 𝔽₂ (2 ^ m - 1) := Pi.single i₀ (1 : ZMod 2)
    have hsyne : syn m e = syn m x := by
      rw [show e = Pi.single i₀ (1 : ZMod 2) from rfl, syn_single]
      ext j
      simp only [col, i₀, Nat.sub_add_cancel hpos, vecToNat_testBit]
      rcases zmod2_eq_zero_or_one (syn m x j) with h0 | h1
      · rw [h0]; decide
      · rw [h1]; decide
    have hv_mem : x + e ∈ hammingCode m := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [map_add, hsyne]
      ext j
      exact zmod2_add_self _
    have he_mem : e ∈ hammingBallFinset (2 ^ m - 1) 1 := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hsub : Finset.univ.filter (fun i => e i ≠ 0) ⊆ {i₀} := by
        intro i hi
        have hne : e i ≠ 0 := (Finset.mem_filter.mp hi).2
        by_contra h
        have hneq : i ≠ i₀ := by simpa using h
        exact hne (by simp [e, Pi.single_eq_of_ne hneq])
      calc
        hammingNorm e = (Finset.univ.filter fun i => e i ≠ 0).card := rfl
        _ ≤ ({i₀} : Finset _).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton _
    refine ⟨x + e, hv_mem, e, he_mem, ?_⟩
    ext i
    simp only [Pi.add_apply]
    rw [add_assoc, zmod2_add_self, add_zero]

private lemma hammingCode_card (m : ℕ) :
    (hammingCode m).card * 2 ^ m = 2 ^ (2 ^ m - 1) := by
  have hsum : Fintype.card (𝔽₂ (2 ^ m - 1)) =
      ∑ s : 𝔽₂ m, (Finset.univ.filter fun x : 𝔽₂ (2 ^ m - 1) => syn m x = s).card := by
    simpa using Finset.card_eq_sum_card_fiberwise (f := syn m)
      (s := (Finset.univ : Finset (𝔽₂ (2 ^ m - 1)))) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
  have hfiber : ∀ s : 𝔽₂ m,
      (Finset.univ.filter fun x : 𝔽₂ (2 ^ m - 1) => syn m x = s).card = (hammingCode m).card := by
    intro s
    obtain ⟨x₀, hx₀⟩ := syn_surjective m s
    apply Finset.card_bij (fun x _ => x + x₀)
    · intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hxs : syn m x = s := (Finset.mem_filter.mp hx).2
      rw [map_add, hxs, hx₀]
      ext j
      exact zmod2_add_self _
    · intro x₁ _ x₂ _ h
      have := congrArg (· + x₀) h
      simpa only [add_assoc, show x₀ + x₀ = 0 from funext (fun _ => zmod2_add_self _), add_zero] using this
    · intro v hv
      refine ⟨v + x₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [map_add, (Finset.mem_filter.mp hv).2, zero_add, hx₀]
      · ext i; simp only [Pi.add_apply]; rw [add_assoc, zmod2_add_self, add_zero]
  have hcard1 : Fintype.card (𝔽₂ (2 ^ m - 1)) = 2 ^ (2 ^ m - 1) := by
    simp [ZMod.card]
  have hcard2 : Fintype.card (𝔽₂ m) = 2 ^ m := by
    simp [ZMod.card]
  rw [hcard1] at hsum
  rw [Finset.sum_congr rfl (fun s _ => hfiber s), Finset.sum_const, Finset.card_univ, hcard2,
    smul_eq_mul, mul_comm] at hsum
  exact hsum.symm

private def joinVec {n k : ℕ} (x : 𝔽₂ n) (y : 𝔽₂ k) : 𝔽₂ (n + k) :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else y ⟨i.val - n, by omega⟩

private lemma joinVec_injective {n k : ℕ} :
    Function.Injective (fun p : 𝔽₂ n × 𝔽₂ k => joinVec p.1 p.2) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  ext i
  · have hi := congrFun h ⟨i.val, by omega⟩
    simpa [joinVec, i.isLt] using hi
  · have hi := congrFun h ⟨n + i.val, by omega⟩
    have hnot : ¬ (n + i.val < n) := by omega
    have hsub : n + i.val - n = i.val := by omega
    simpa [joinVec, hnot, hsub] using hi

private lemma joinVec_add {n k : ℕ} (x₁ x₂ : 𝔽₂ n) (y₁ y₂ : 𝔽₂ k) :
    joinVec (x₁ + x₂) (y₁ + y₂) = joinVec x₁ y₁ + joinVec x₂ y₂ := by
  ext i
  by_cases h : i.val < n <;> simp [joinVec, h]

private lemma hammingNorm_joinVec {n k : ℕ} (x : 𝔽₂ n) (y : 𝔽₂ k) :
    hammingNorm (joinVec x y) = hammingNorm x + hammingNorm y := by
  unfold hammingNorm
  let emb1 : Fin n ↪ Fin (n + k) :=
    ⟨fun i => ⟨i.val, by omega⟩, fun a b h => Fin.ext (congrArg (fun x : Fin (n + k) => x.val) h)⟩
  let emb2 : Fin k ↪ Fin (n + k) :=
    ⟨fun j => ⟨n + j.val, by omega⟩, fun a b h => Fin.ext (Nat.add_left_cancel (congrArg (fun x : Fin (n + k) => x.val) h))⟩
  let A : Finset (Fin (n + k)) := (Finset.univ.filter fun i : Fin n => x i ≠ 0).map emb1
  let B : Finset (Fin (n + k)) := (Finset.univ.filter fun j : Fin k => y j ≠ 0).map emb2
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hzA
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hzB
    have hv : n + j.val = i.val := congrArg Fin.val hj
    omega
  have heq : Finset.univ.filter (fun i : Fin (n + k) => joinVec x y i ≠ 0) = A ∪ B := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, A, B, Finset.mem_map]
    by_cases hz : z.val < n
    · simp only [joinVec, hz, ↓reduceDIte]
      constructor
      · intro h; left; exact ⟨⟨z.val, hz⟩, h, Fin.ext rfl⟩
      · rintro (⟨i, hi, hiz⟩ | ⟨j, _, hjz⟩)
        · have hv : i.val = z.val := congrArg Fin.val hiz
          have : i = ⟨z.val, hz⟩ := Fin.ext (show i.val = z.val from hv)
          rwa [← this]
        · have hv : n + j.val = z.val := congrArg Fin.val hjz
          omega
    · simp only [joinVec, hz, ↓reduceDIte]
      constructor
      · intro h; right; exact ⟨⟨z.val - n, by omega⟩, h, Fin.ext (show n + (z.val - n) = z.val by omega)⟩
      · rintro (⟨i, _, hiz⟩ | ⟨j, hj, hjz⟩)
        · have hv : i.val = z.val := congrArg Fin.val hiz
          omega
        · have hv : n + j.val = z.val := congrArg Fin.val hjz
          have : j = ⟨z.val - n, by omega⟩ := Fin.ext (show j.val = z.val - n by omega)
          rwa [← this]
  rw [heq, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map]

private lemma product_covering {n k r : ℕ} {V : Finset (𝔽₂ n)} {H : Finset (𝔽₂ k)}
    (hV : IsCoveringFinset n r V) (hH : IsCoveringFinset k 1 H) :
    IsCoveringFinset (n + k) (r + 1) ((V ×ˢ H).image fun p => joinVec p.1 p.2) := by
  unfold IsCoveringFinset at hV hH ⊢
  ext z
  simp only [Finset.mem_univ, iff_true, Finset.mem_add]
  let x : 𝔽₂ n := fun i => z ⟨i.val, by omega⟩
  let y : 𝔽₂ k := fun j => z ⟨n + j.val, by omega⟩
  have hz_eq : joinVec x y = z := by
    ext i
    by_cases h : i.val < n
    · simp [joinVec, x, h]
    · simp only [joinVec, y, h, ↓reduceDIte]
      congr 1; apply Fin.ext; dsimp; omega
  have hx : x ∈ V + hammingBallFinset n r := hV ▸ Finset.mem_univ x
  have hy : y ∈ H + hammingBallFinset k 1 := hH ▸ Finset.mem_univ y
  obtain ⟨v, hv, e₁, he₁, hve₁⟩ := Finset.mem_add.mp hx
  obtain ⟨h, hh, e₂, he₂, hhe₂⟩ := Finset.mem_add.mp hy
  refine ⟨joinVec v h, Finset.mem_image.mpr ⟨(v, h), Finset.mem_product.mpr ⟨hv, hh⟩, rfl⟩,
    joinVec e₁ e₂, ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [hammingNorm_joinVec]
    have h1 := (Finset.mem_filter.mp he₁).2
    have h2 := (Finset.mem_filter.mp he₂).2
    omega
  · rw [← joinVec_add, hve₁, hhe₂, hz_eq]

private lemma card_hammingBall (n r : ℕ) :
    Nat.card (hammingBall n r) = ∑ j ∈ Finset.range (r + 1), n.choose j := by
  classical
  have hcard : Nat.card (hammingBall n r) = (hammingBallFinset n r).card := by
    rw [Nat.card_coe_set_eq]
    have heq : (hammingBall n r) = (hammingBallFinset n r : Set (𝔽₂ n)) := by
      ext x; simp [hammingBall, hammingBallFinset]
    rw [heq, Set.ncard_coe_finset]
  rw [hcard]
  let supp : 𝔽₂ n → Finset (Fin n) := fun x => Finset.univ.filter fun i => x i ≠ 0
  have hsupp_bij : (hammingBallFinset n r).card =
      ((Finset.univ : Finset (Finset (Fin n))).filter fun S => S.card ≤ r).card := by
    apply Finset.card_bij (fun x _ => supp x)
    · intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact (Finset.mem_filter.mp hx).2
    · intro x₁ _ x₂ _ h
      ext i
      have hi : i ∈ supp x₁ ↔ i ∈ supp x₂ := by rw [h]
      simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases zmod2_eq_zero_or_one (x₁ i) with h1 | h1 <;>
        rcases zmod2_eq_zero_or_one (x₂ i) with h2 | h2
      · rw [h1, h2]
      · exfalso; rw [h1, h2] at hi; exact (hi.mpr one_ne_zero) rfl
      · exfalso; rw [h1, h2] at hi; exact (hi.mp one_ne_zero) rfl
      · rw [h1, h2]
    · intro S hS
      let x : 𝔽₂ n := fun i => if i ∈ S then 1 else 0
      have hsx : supp x = S := by
        ext i
        simp only [supp, x, Finset.mem_filter, Finset.mem_univ, true_and]
        split_ifs with hi
        · exact ⟨fun _ => hi, fun _ => one_ne_zero⟩
        · exact ⟨fun h => absurd rfl h, fun h => absurd h hi⟩
      refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hsx⟩
      change (supp x).card ≤ r
      rw [hsx]
      exact (Finset.mem_filter.mp hS).2
  rw [hsupp_bij]
  have hpart : ((Finset.univ : Finset (Finset (Fin n))).filter fun S => S.card ≤ r).card =
      ∑ j ∈ Finset.range (r + 1),
        (((Finset.univ : Finset (Finset (Fin n))).filter fun S => S.card ≤ r).filter
          fun S => S.card = j).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro S hS
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hS).2)
  rw [hpart]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hfeq : (((Finset.univ : Finset (Finset (Fin n))).filter fun S => S.card ≤ r).filter
      fun S => S.card = j) = Finset.powersetCard j (Finset.univ : Finset (Fin n)) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
      Finset.subset_univ]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨h ▸ hjr, h⟩
  rw [hfeq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private lemma card_hammingBall_pos (n r : ℕ) : 0 < Nat.card (hammingBall n r) := by
  rw [card_hammingBall]
  have h0 : 0 ∈ Finset.range (r + 1) := Finset.mem_range.mpr (Nat.succ_pos r)
  exact lt_of_lt_of_le (by simp : 0 < n.choose 0)
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) h0)

private lemma minDensityFinset_step (n r m : ℕ) :
    minDensityFinset (n + (2 ^ m - 1)) (r + 1) ≤
      minDensityFinset n r *
        ((Nat.card (hammingBall (n + (2 ^ m - 1)) (r + 1)) : ℝ≥0∞) /
          ((2 ^ m : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞))) := by
  let k := 2 ^ m - 1
  have hHcov : IsCoveringFinset k 1 (hammingCode m) := hammingCode_covering m
  have hHcard : (hammingCode m).card * 2 ^ m = 2 ^ k := hammingCode_card m
  have h2m_ne : (2 ^ m : ℝ≥0∞) ≠ 0 := by positivity
  have h2m_top : (2 ^ m : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  have h2n_ne : (2 ^ n : ℝ≥0∞) ≠ 0 := by positivity
  have h2n_top : (2 ^ n : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  have h2k_ne : (2 ^ k : ℝ≥0∞) ≠ 0 := by positivity
  have h2k_top : (2 ^ k : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  have hBn_ne : (Nat.card (hammingBall n r) : ℝ≥0∞) ≠ 0 :=
    by exact_mod_cast (card_hammingBall_pos n r).ne'
  have hBn_top : (Nat.card (hammingBall n r) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hBN_ne : (Nat.card (hammingBall (n + k) (r + 1)) : ℝ≥0∞) ≠ 0 :=
    by exact_mod_cast (card_hammingBall_pos (n + k) (r + 1)).ne'
  have hBN_top : (Nat.card (hammingBall (n + k) (r + 1)) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  let C : ℝ≥0∞ := (Nat.card (hammingBall (n + k) (r + 1)) : ℝ≥0∞) /
    ((2 ^ m : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞))
  have hC_ne : C ≠ 0 := by
    dsimp [C]
    exact ENNReal.div_ne_zero.mpr ⟨hBN_ne, ENNReal.mul_ne_top h2m_top hBn_top⟩
  have hC_top : C ≠ ⊤ := by
    dsimp [C]
    exact ENNReal.div_ne_top hBN_top (mul_ne_zero h2m_ne hBn_ne)
  have hHinv : ((hammingCode m).card : ℝ≥0∞) * (2 ^ k : ℝ≥0∞)⁻¹ = (2 ^ m : ℝ≥0∞)⁻¹ := by
    have hcast : ((hammingCode m).card : ℝ≥0∞) * (2 ^ m : ℝ≥0∞) = (2 ^ k : ℝ≥0∞) := by
      exact_mod_cast hHcard
    apply (ENNReal.mul_left_inj h2k_ne h2k_top).mp
    calc
      ((hammingCode m).card : ℝ≥0∞) * (2 ^ k : ℝ≥0∞)⁻¹ * (2 ^ k : ℝ≥0∞)
        = ((hammingCode m).card : ℝ≥0∞) * ((2 ^ k : ℝ≥0∞)⁻¹ * (2 ^ k : ℝ≥0∞)) := by ring
      _ = ((hammingCode m).card : ℝ≥0∞) := by rw [ENNReal.inv_mul_cancel h2k_ne h2k_top, mul_one]
      _ = ((hammingCode m).card : ℝ≥0∞) * ((2 ^ m : ℝ≥0∞) * (2 ^ m : ℝ≥0∞)⁻¹) := by
        rw [ENNReal.mul_inv_cancel h2m_ne h2m_top, mul_one]
      _ = (2 ^ m : ℝ≥0∞)⁻¹ * (((hammingCode m).card : ℝ≥0∞) * (2 ^ m : ℝ≥0∞)) := by ring
      _ = (2 ^ m : ℝ≥0∞)⁻¹ * (2 ^ k : ℝ≥0∞) := by rw [hcast]
  change minDensityFinset (n + k) (r + 1) ≤ minDensityFinset n r * C
  rw [← ENNReal.div_le_iff_le_mul (Or.inl hC_ne) (Or.inl hC_top)]
  unfold minDensityFinset
  refine le_iInf₂ fun V hV => ?_
  rw [ENNReal.div_le_iff_le_mul (Or.inl hC_ne) (Or.inl hC_top)]
  let W : Finset (𝔽₂ (n + k)) := (V ×ˢ hammingCode m).image fun p => joinVec p.1 p.2
  have hWcov : IsCoveringFinset (n + k) (r + 1) W := product_covering hV hHcov
  have hWcard : W.card = V.card * (hammingCode m).card := by
    rw [Finset.card_image_of_injective _ joinVec_injective, Finset.card_product]
  calc
    ⨅ (U : Finset (𝔽₂ (n + k))) (_ : IsCoveringFinset (n + k) (r + 1) U),
        (U.card : ℝ≥0∞) * (Nat.card (hammingBall (n + k) (r + 1)) : ℝ≥0∞) / (2 ^ (n + k) : ℝ≥0∞)
      ≤ (W.card : ℝ≥0∞) * (Nat.card (hammingBall (n + k) (r + 1)) : ℝ≥0∞) / (2 ^ (n + k) : ℝ≥0∞) :=
        iInf₂_le W hWcov
    _ = ((V.card : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞)) * C := by
        dsimp [C]
        rw [hWcard, Nat.cast_mul, pow_add]
        simp only [div_eq_mul_inv, ENNReal.mul_inv (Or.inl h2n_ne) (Or.inl h2n_top),
          ENNReal.mul_inv (Or.inl h2m_ne) (Or.inl h2m_top)]
        calc
          (V.card : ℝ≥0∞) * ((hammingCode m).card : ℝ≥0∞) *
              (Nat.card (hammingBall (n + k) (r + 1)) : ℝ≥0∞) * ((2 ^ n : ℝ≥0∞)⁻¹ * (2 ^ k : ℝ≥0∞)⁻¹)
            = (V.card : ℝ≥0∞) * (((hammingCode m).card : ℝ≥0∞) * (2 ^ k : ℝ≥0∞)⁻¹) *
                (Nat.card (hammingBall (n + k) (r + 1)) : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)⁻¹ := by ring
          _ = (V.card : ℝ≥0∞) * (2 ^ m : ℝ≥0∞)⁻¹ *
                (Nat.card (hammingBall (n + k) (r + 1)) : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)⁻¹ := by rw [hHinv]
          _ = (V.card : ℝ≥0∞) * ((Nat.card (hammingBall n r) : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞)⁻¹) *
                (2 ^ m : ℝ≥0∞)⁻¹ * (Nat.card (hammingBall (n + k) (r + 1)) : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)⁻¹ := by
                rw [ENNReal.mul_inv_cancel hBn_ne hBn_top, mul_one]
          _ = _ := by
                simp only [Nat.card_coe_set_eq]
                ring

private lemma choose_le_pow_div_factorial (N k : ℕ) :
    (N.choose k : ℝ) ≤ (N : ℝ) ^ k / (k.factorial : ℝ) := by
  have h1 : k.factorial * N.choose k = N.descFactorial k :=
    (Nat.descFactorial_eq_factorial_mul_choose N k).symm
  have h2 : N.descFactorial k ≤ N ^ k := Nat.descFactorial_le_pow N k
  have h3 : (N.choose k : ℝ) * (k.factorial : ℝ) ≤ (N : ℝ) ^ k := by
    have : N.choose k * k.factorial ≤ N ^ k := by rw [mul_comm]; exact h1.le.trans h2
    exact_mod_cast this
  exact (le_div_iff₀ (by exact_mod_cast Nat.factorial_pos k)).mpr h3

private lemma pow_sub_div_factorial_le_choose {n r : ℕ} (hr : r ≤ n) :
    ((n - r : ℕ) : ℝ) ^ r / (r.factorial : ℝ) ≤ (n.choose r : ℝ) := by
  have h1 : (n - r) ^ r ≤ n.descFactorial r := by
    suffices h2 : ∀ j : ℕ, j ≤ r → (n - r) ^ j ≤ n.descFactorial j from h2 r (le_refl r)
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ihj =>
      intro hjr
      rw [pow_succ', Nat.descFactorial_succ]
      exact Nat.mul_le_mul (by omega) (ihj (by omega))
  have h2 : n.descFactorial r = r.factorial * n.choose r :=
    Nat.descFactorial_eq_factorial_mul_choose n r
  have h3 : ((n - r : ℕ) : ℝ) ^ r ≤ (n.choose r : ℝ) * (r.factorial : ℝ) := by
    have : (n - r) ^ r ≤ n.choose r * r.factorial := by rw [mul_comm]; exact h1.trans h2.le
    exact_mod_cast this
  exact (div_le_iff₀ (by exact_mod_cast Nat.factorial_pos r)).mpr h3

private lemma ratio_eventually_le_six (r : ℕ) (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop,
      let m := Nat.clog 2 (n / (2 * (r + 1)))
      let k := 2 ^ m - 1
      (Nat.card (hammingBall (n + k) (r + 1)) : ℝ≥0∞) /
        ((2 ^ m : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞)) ≤ 6 := by
  let N₀ : ℕ := max (80 * (r + 1) * (r + 1).factorial) (80 * (r + 1) ^ 2)
  filter_upwards [eventually_ge_atTop N₀] with n hn
  have hn_fac : 80 * (r + 1) * (r + 1).factorial ≤ n := le_trans (le_max_left _ _) hn
  have hn_sq : 80 * (r + 1) ^ 2 ≤ n := le_trans (le_max_right _ _) hn
  have hfac_pos : 1 ≤ (r + 1).factorial := Nat.factorial_pos _
  have hr1_pos : (0 : ℝ) < (r + 1 : ℕ) := by positivity
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by nlinarith
    exact_mod_cast this
  let q : ℕ := n / (2 * (r + 1))
  have hq_ge : 40 ≤ q := by
    dsimp [q]
    rw [Nat.le_div_iff_mul_le (by omega)]
    nlinarith
  let m : ℕ := Nat.clog 2 q
  let k : ℕ := 2 ^ m - 1
  have hm_ge : q ≤ 2 ^ m := Nat.le_pow_clog (by decide) q
  have hm_pos : 1 ≤ m := by
    by_contra hm0
    have h0 : m = 0 := by omega
    rw [h0, pow_zero] at hm_ge
    omega
  have hm_lt : 2 ^ (m - 1) < q := Nat.pow_pred_clog_lt_self (by decide) (by omega : 1 < q)
  have h2m_le_2q : 2 ^ m ≤ 2 * q := by
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hm_pos, pow_succ']
    omega
  have h2m_le_div : 2 ^ m * (r + 1) ≤ n := by
    have hq2 : 2 * (r + 1) * q ≤ n := Nat.mul_div_le n (2 * (r + 1))
    nlinarith
  have h2m_ge_real : (39 / 40 : ℝ) * ((n : ℝ) / (2 * ((r + 1 : ℕ) : ℝ))) ≤ (2 ^ m : ℝ) := by
    have hdiv : n < 2 * (r + 1) * (q + 1) := by
      dsimp [q]
      have := Nat.lt_mul_div_succ n (show 0 < 2 * (r + 1) by omega)
      linarith
    have hdiv_r : (n : ℝ) < 2 * ((r + 1 : ℕ) : ℝ) * ((q : ℝ) + 1) := by exact_mod_cast hdiv
    have hq_r : (40 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_ge
    have h2m_r : (q : ℝ) ≤ (2 ^ m : ℝ) := by exact_mod_cast hm_ge
    have hstep : (39 / 40 : ℝ) * ((q : ℝ) + 1) ≤ (q : ℝ) := by linarith
    have hstep2 : (n : ℝ) / (2 * ((r + 1 : ℕ) : ℝ)) ≤ (q : ℝ) + 1 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    nlinarith
  let N : ℕ := n + k
  have hN_ge_n : n ≤ N := Nat.le_add_right n k
  have hN_le : (N : ℝ) ≤ (n : ℝ) * (1 + 1 / ((r + 1 : ℕ) : ℝ)) := by
    have hk_le : k ≤ 2 ^ m := Nat.sub_le _ _
    have h2m_r : (2 ^ m : ℝ) * ((r + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2m_le_div
    have hk_r : (k : ℝ) ≤ (n : ℝ) / ((r + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hr1_pos]
      have : (k : ℝ) ≤ (2 ^ m : ℝ) := by exact_mod_cast hk_le
      nlinarith
    have hNr : (N : ℝ) = (n : ℝ) + (k : ℝ) := by exact_mod_cast rfl
    rw [hNr, mul_add, mul_one, mul_one_div]
    linarith
  have hBN_ub : (Nat.card (hammingBall N (r + 1)) : ℝ) ≤
      (41 / 40 : ℝ) * (N : ℝ) ^ (r + 1) / (((r + 1).factorial : ℕ) : ℝ) := by
    rw [card_hammingBall]
    push_cast
    rw [Finset.sum_range_succ]
    have htop : (N.choose (r + 1) : ℝ) ≤ (N : ℝ) ^ (r + 1) / (((r + 1).factorial : ℕ) : ℝ) :=
      choose_le_pow_div_factorial N (r + 1)
    have hlow : (∑ j ∈ Finset.range (r + 1), (N.choose j : ℝ)) ≤
        ((r + 1 : ℕ) : ℝ) * (N : ℝ) ^ r := by
      have hterm : ∀ j ∈ Finset.range (r + 1), (N.choose j : ℝ) ≤ (N : ℝ) ^ r := by
        intro j hj
        have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have h1 : (N.choose j : ℝ) ≤ (N : ℝ) ^ j := by
          exact_mod_cast (Nat.choose_le_descFactorial N j).trans (Nat.descFactorial_le_pow N j)
        have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
          have : 1 ≤ N := by nlinarith
          exact_mod_cast this
        exact h1.trans (pow_le_pow_right₀ hN1 hjr)
      simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul (Finset.range (r + 1)) _ _ hterm
    have hsmall : ((r + 1 : ℕ) : ℝ) * (N : ℝ) ^ r ≤
        (1 / 40 : ℝ) * ((N : ℝ) ^ (r + 1) / (((r + 1).factorial : ℕ) : ℝ)) := by
      have hNfac : (40 : ℝ) * ((r + 1 : ℕ) : ℝ) * (((r + 1).factorial : ℕ) : ℝ) ≤ (N : ℝ) := by
        have : 40 * (r + 1) * (r + 1).factorial ≤ N := by nlinarith
        exact_mod_cast this
      have hfacp : (0 : ℝ) < (((r + 1).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos (r + 1)
      rw [mul_div_assoc', le_div_iff₀ hfacp, pow_succ]
      have hNr0 : (0 : ℝ) ≤ (N : ℝ) ^ r := by positivity
      nlinarith
    have hsplit : (41 / 40 : ℝ) * (N : ℝ) ^ (r + 1) / (((r + 1).factorial : ℕ) : ℝ) =
        (N : ℝ) ^ (r + 1) / (((r + 1).factorial : ℕ) : ℝ) +
          (1 / 40 : ℝ) * ((N : ℝ) ^ (r + 1) / (((r + 1).factorial : ℕ) : ℝ)) := by ring
    linarith
  have hBn_lb : (39 / 40 : ℝ) * (n : ℝ) ^ r / ((r.factorial : ℕ) : ℝ) ≤
      (Nat.card (hammingBall n r) : ℝ) := by
    rw [card_hammingBall]
    push_cast
    have hmem : r ∈ Finset.range (r + 1) := Finset.mem_range.mpr (Nat.lt_succ_self r)
    have hge_choose : (n.choose r : ℝ) ≤ ∑ j ∈ Finset.range (r + 1), (n.choose j : ℝ) :=
      Finset.single_le_sum (fun j _ => Nat.cast_nonneg _) hmem
    have hlb : ((n - r : ℕ) : ℝ) ^ r / ((r.factorial : ℕ) : ℝ) ≤ (n.choose r : ℝ) :=
      pow_sub_div_factorial_le_choose (by nlinarith)
    have hbern : (39 / 40 : ℝ) * (n : ℝ) ^ r ≤ ((n - r : ℕ) : ℝ) ^ r := by
      have hsub_cast : ((n - r : ℕ) : ℝ) = (n : ℝ) * (1 - (r : ℝ) / (n : ℝ)) := by
        have hrn : r ≤ n := by nlinarith
        rw [Nat.cast_sub hrn, mul_sub, mul_one, mul_div_cancel₀ _ hn_pos.ne']
      rw [hsub_cast, mul_pow]
      have hneg1 : (-1 : ℝ) ≤ -((r : ℝ) / (n : ℝ)) := by
        have : (r : ℝ) ≤ (n : ℝ) := by
          have : r ≤ n := by nlinarith
          exact_mod_cast this
        rw [neg_le_neg_iff, div_le_one hn_pos]
        exact this
      have hneg2 : (-2 : ℝ) ≤ -((r : ℝ) / (n : ℝ)) := by linarith
      have h1 := one_add_mul_le_pow hneg2 r
      have hr2_le : (r : ℝ) * (r : ℝ) ≤ (1 / 40 : ℝ) * (n : ℝ) := by
        have : 40 * (r * r) ≤ n := by nlinarith
        have hcast : (40 : ℝ) * ((r : ℝ) * (r : ℝ)) ≤ (n : ℝ) := by exact_mod_cast this
        linarith
      have hdiv_le : (r : ℝ) * ((r : ℝ) / (n : ℝ)) ≤ 1 / 40 := by
        rw [← mul_div_assoc, div_le_iff₀ hn_pos]
        linarith
      have hpow_ge : (39 / 40 : ℝ) ≤ (1 - (r : ℝ) / (n : ℝ)) ^ r := by
        rw [show (1 : ℝ) - (r : ℝ) / (n : ℝ) = 1 + -((r : ℝ) / (n : ℝ)) by ring]
        linarith
      calc
        (39 / 40 : ℝ) * (n : ℝ) ^ r = (n : ℝ) ^ r * (39 / 40 : ℝ) := by ring
        _ ≤ (n : ℝ) ^ r * (1 - (r : ℝ) / (n : ℝ)) ^ r :=
          mul_le_mul_of_nonneg_left hpow_ge (by positivity)
    have hfacp : (0 : ℝ) < ((r.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos r
    exact (div_le_div_of_nonneg_right hbern hfacp.le).trans (hlb.trans hge_choose)
  have hexp_bound : (1 + 1 / ((r + 1 : ℕ) : ℝ)) ^ (r + 1) ≤ Real.exp 1 := by
    have h1 : 1 + 1 / ((r + 1 : ℕ) : ℝ) ≤ Real.exp (1 / ((r + 1 : ℕ) : ℝ)) := by
      linarith [Real.add_one_le_exp (1 / ((r + 1 : ℕ) : ℝ))]
    calc
      (1 + 1 / ((r + 1 : ℕ) : ℝ)) ^ (r + 1)
        ≤ (Real.exp (1 / ((r + 1 : ℕ) : ℝ))) ^ (r + 1) :=
          pow_le_pow_left₀ (by positivity) h1 (r + 1)
      _ = Real.exp (((r + 1 : ℕ) : ℝ) * (1 / ((r + 1 : ℕ) : ℝ))) := by
          rw [← Real.exp_nat_mul]
      _ = Real.exp 1 := by
          rw [mul_one_div_cancel hr1_pos.ne']
  have hreal_ineq : (Nat.card (hammingBall N (r + 1)) : ℝ) ≤
      6 * ((2 ^ m : ℝ) * (Nat.card (hammingBall n r) : ℝ)) := by
    have hfac_eq : (((r + 1).factorial : ℕ) : ℝ) = ((r + 1 : ℕ) : ℝ) * ((r.factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_succ r
    have hNpow : (N : ℝ) ^ (r + 1) ≤ (n : ℝ) ^ (r + 1) * Real.exp 1 := by
      calc
        (N : ℝ) ^ (r + 1) ≤ ((n : ℝ) * (1 + 1 / ((r + 1 : ℕ) : ℝ))) ^ (r + 1) :=
          pow_le_pow_left₀ (Nat.cast_nonneg N) hN_le (r + 1)
        _ = (n : ℝ) ^ (r + 1) * (1 + 1 / ((r + 1 : ℕ) : ℝ)) ^ (r + 1) := mul_pow _ _ _
        _ ≤ (n : ℝ) ^ (r + 1) * Real.exp 1 :=
          mul_le_mul_of_nonneg_left hexp_bound (by positivity)
    have hexp_lt : Real.exp 1 < 27183 / 10000 := by
      have := Real.exp_one_lt_d9
      linarith
    have hfacp : (0 : ℝ) < ((r.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos r
    have hprod_lb : (39 / 40 : ℝ) * (39 / 40 : ℝ) * ((n : ℝ) ^ (r + 1) / (2 * ((r + 1 : ℕ) : ℝ) * ((r.factorial : ℕ) : ℝ))) ≤
        (2 ^ m : ℝ) * (Nat.card (hammingBall n r) : ℝ) := by
      have hmul := mul_le_mul h2m_ge_real hBn_lb (by positivity) (by positivity)
      have halg : (39 / 40 : ℝ) * ((n : ℝ) / (2 * ((r + 1 : ℕ) : ℝ))) *
          ((39 / 40 : ℝ) * (n : ℝ) ^ r / ((r.factorial : ℕ) : ℝ)) =
          (39 / 40 : ℝ) * (39 / 40 : ℝ) * ((n : ℝ) ^ (r + 1) / (2 * ((r + 1 : ℕ) : ℝ) * ((r.factorial : ℕ) : ℝ))) := by
        rw [pow_succ']
        ring
      linarith
    have htop_ub : (Nat.card (hammingBall N (r + 1)) : ℝ) ≤
        (41 / 40 : ℝ) * Real.exp 1 * ((n : ℝ) ^ (r + 1) / (((r + 1 : ℕ) : ℝ) * ((r.factorial : ℕ) : ℝ))) := by
      rw [hfac_eq] at hBN_ub
      have hstep : (41 / 40 : ℝ) * (N : ℝ) ^ (r + 1) / (((r + 1 : ℕ) : ℝ) * ((r.factorial : ℕ) : ℝ)) ≤
          (41 / 40 : ℝ) * ((n : ℝ) ^ (r + 1) * Real.exp 1) / (((r + 1 : ℕ) : ℝ) * ((r.factorial : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNpow (by norm_num)) (by positivity)
      calc
        (Nat.card (hammingBall N (r + 1)) : ℝ)
          ≤ (41 / 40 : ℝ) * ((n : ℝ) ^ (r + 1) * Real.exp 1) / (((r + 1 : ℕ) : ℝ) * ((r.factorial : ℕ) : ℝ)) :=
            hBN_ub.trans hstep
        _ = (41 / 40 : ℝ) * Real.exp 1 * ((n : ℝ) ^ (r + 1) / (((r + 1 : ℕ) : ℝ) * ((r.factorial : ℕ) : ℝ))) := by
            ring
    have hcoeff : (41 / 40 : ℝ) * Real.exp 1 ≤ 6 * ((39 / 40 : ℝ) * (39 / 40 : ℝ) / 2) := by
      linarith
    have hbase_pos : 0 ≤ (n : ℝ) ^ (r + 1) / (((r + 1 : ℕ) : ℝ) * ((r.factorial : ℕ) : ℝ)) := by positivity
    have hhalve : (n : ℝ) ^ (r + 1) / (2 * ((r + 1 : ℕ) : ℝ) * ((r.factorial : ℕ) : ℝ)) =
        (1 / 2 : ℝ) * ((n : ℝ) ^ (r + 1) / (((r + 1 : ℕ) : ℝ) * ((r.factorial : ℕ) : ℝ))) := by ring
    rw [hhalve] at hprod_lb
    nlinarith
  have hnat_ineq : Nat.card (hammingBall N (r + 1)) ≤ 6 * (2 ^ m * Nat.card (hammingBall n r)) := by
    exact_mod_cast hreal_ineq
  have hden_ne : ((2 ^ m : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞)) ≠ 0 :=
    mul_ne_zero (by positivity) (by exact_mod_cast (card_hammingBall_pos n r).ne')
  have hden_top : ((2 ^ m : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) (ENNReal.natCast_ne_top _)
  rw [ENNReal.div_le_iff_le_mul (Or.inl hden_ne) (Or.inl hden_top)]
  exact_mod_cast hnat_ineq

private lemma liminf_le_liminf_comp_atTop (u : ℕ → ℝ≥0∞) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) :
    liminf u atTop ≤ liminf (u ∘ φ) atTop := by
  rw [Filter.liminf_eq, Filter.liminf_eq]
  apply sSup_le
  intro a ha
  exact le_sSup (hφ.eventually ha)

private lemma liminf_const_mul_le (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ⊤) (v : ℕ → ℝ≥0∞) :
    liminf (fun n => c * v n) atTop ≤ c * liminf v atTop := by
  rw [Filter.liminf_eq]
  apply sSup_le
  intro a ha
  have hdiv : a / c ≤ liminf v atTop := by
    rw [Filter.liminf_eq]
    apply le_sSup
    filter_upwards [ha] with n hn
    exact (ENNReal.div_le_iff_le_mul (Or.inl hc0) (Or.inl hctop)).mpr (by simpa [mul_comm] using hn)
  calc
    a = c * (a / c) := by rw [ENNReal.mul_div_cancel hc0 hctop]
    _ ≤ c * liminf v atTop := by gcongr

end OMA.Proof_Green40_R1_H2

theorem OMA.solution : OMA.R_Green40_green_40_variants_arbitrary_subsets_R1.H2 := by
  intro r hr
  unfold Green40.f_tilde
  let φ : ℕ → ℕ := fun n => n + (2 ^ Nat.clog 2 (n / (2 * (r + 1))) - 1)
  have hφ : Filter.Tendsto φ Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono (f := id)
    · intro n; exact Nat.le_add_right n _
    · exact Filter.tendsto_id
  have hstep : ∀ᶠ n : ℕ in Filter.atTop,
      Green40.minDensityFinset (φ n) (r + 1) ≤ 6 * Green40.minDensityFinset n r := by
    filter_upwards [OMA.Proof_Green40_R1_H2.ratio_eventually_le_six r hr] with n hrat
    have h1 := OMA.Proof_Green40_R1_H2.minDensityFinset_step n r (Nat.clog 2 (n / (2 * (r + 1))))
    calc
      Green40.minDensityFinset (φ n) (r + 1)
        ≤ Green40.minDensityFinset n r *
            ((Nat.card (Green40.hammingBall (φ n) (r + 1)) : ENNReal) /
              ((2 ^ Nat.clog 2 (n / (2 * (r + 1))) : ENNReal) * (Nat.card (Green40.hammingBall n r) : ENNReal))) := h1
      _ ≤ Green40.minDensityFinset n r * 6 := by gcongr
      _ = 6 * Green40.minDensityFinset n r := mul_comm _ _
  calc
    Filter.liminf (fun n => Green40.minDensityFinset n (r + 1)) Filter.atTop
      ≤ Filter.liminf (fun n => Green40.minDensityFinset (φ n) (r + 1)) Filter.atTop :=
        OMA.Proof_Green40_R1_H2.liminf_le_liminf_comp_atTop _ φ hφ
    _ ≤ Filter.liminf (fun n => 6 * Green40.minDensityFinset n r) Filter.atTop :=
        Filter.liminf_le_liminf hstep
    _ ≤ 6 * Filter.liminf (fun n => Green40.minDensityFinset n r) Filter.atTop :=
        OMA.Proof_Green40_R1_H2.liminf_const_mul_le 6 (by simp) (by simp) _
