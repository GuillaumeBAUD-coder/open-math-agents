import OMAStatements.S_oeis_a396102
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a396102

open OMA.S_oeis_a396102

/-- The geometric series `x / (1 - c * x) = ∑_{n ≥ 1} c^(n - 1) * x^n`. -/
private def geom {R : Type*} [CommRing R] (c : R) (n : ℕ) : R :=
  if n = 0 then 0 else c ^ (n - 1)

private lemma powSeq_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (g : ℕ → R) :
    ∀ k n : ℕ, φ (powSeq g k n) = powSeq (fun i => φ (g i)) k n := by
  intro k
  induction k with
  | zero => intro n; dsimp [powSeq]; split_ifs <;> simp
  | succ k ih => intro n; simp only [powSeq, map_sum, map_mul, ih]

private lemma comp_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f g : ℕ → R) (n : ℕ) :
    φ (comp f g n) = comp (fun i => φ (f i)) (fun i => φ (g i)) n := by
  simp only [comp, map_sum, map_mul, powSeq_map]

private lemma iterComp_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : ℕ → R) :
    ∀ r n : ℕ, φ (iterComp f r n) = iterComp (fun i => φ (f i)) r n := by
  intro r
  induction r with
  | zero => intro n; dsimp [iterComp]; split_ifs <;> simp
  | succ r ih =>
    intro n
    simp only [iterComp, comp_map]
    have hfun : (fun i => φ (iterComp f r i)) = iterComp (fun i => φ (f i)) r := by
      ext i; exact ih i
    rw [hfun]

private lemma powSeq_congr {R : Type*} [CommRing R] {g1 g2 : ℕ → R} {N : ℕ}
    (hg : ∀ i ≤ N, g1 i = g2 i) : ∀ k n : ℕ, n ≤ N → powSeq g1 k n = powSeq g2 k n := by
  intro k
  induction k with
  | zero => intro n _; rfl
  | succ k ih =>
    intro n hn
    simp only [powSeq]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hg i (le_trans hin hn), ih (n - i) (by omega)]

private lemma comp_congr {R : Type*} [CommRing R] {f1 f2 g1 g2 : ℕ → R} {N : ℕ}
    (hf : ∀ i ≤ N, f1 i = f2 i) (hg : ∀ i ≤ N, g1 i = g2 i) :
    ∀ n ≤ N, comp f1 g1 n = comp f2 g2 n := by
  intro n hn
  simp only [comp]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [hf k (le_trans hkn hn), powSeq_congr hg k n hn]

private lemma iterComp_congr {R : Type*} [CommRing R] {f1 f2 : ℕ → R} {N : ℕ}
    (hf : ∀ i ≤ N, f1 i = f2 i) : ∀ r n : ℕ, n ≤ N → iterComp f1 r n = iterComp f2 r n := by
  intro r
  induction r with
  | zero => intro n _; rfl
  | succ r ih =>
    intro n hn
    exact comp_congr hf (fun i hi => ih i hi) n hn

private lemma powSeq_zero_of_lt {R : Type*} [CommRing R] {g : ℕ → R} (hg0 : g 0 = 0) :
    ∀ k m : ℕ, m < k → powSeq g k m = 0 := by
  intro k
  induction k with
  | zero => intro m hm; omega
  | succ k ih =>
    intro m hm
    simp only [powSeq]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hi0 : i = 0
    · rw [hi0, hg0, zero_mul]
    · rw [ih (m - i) (by omega), mul_zero]

private lemma powSeq_diag {R : Type*} [CommRing R] {g : ℕ → R} (hg0 : g 0 = 0) :
    ∀ k : ℕ, powSeq g k k = (g 1) ^ k := by
  intro k
  induction k with
  | zero => simp [powSeq]
  | succ k ih =>
    simp only [powSeq]
    have hterm : ∀ i ∈ Finset.range (k + 2),
        g i * powSeq g k (k + 1 - i) = if i = 1 then g 1 ^ (k + 1) else 0 := by
      intro i hi
      have hik : i ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      by_cases hi1 : i = 1
      · rw [hi1, if_pos rfl, Nat.add_sub_cancel, ih, pow_succ']
      · rw [if_neg hi1]
        by_cases hi0 : i = 0
        · rw [hi0, hg0, zero_mul]
        · rw [powSeq_zero_of_lt hg0 k (k + 1 - i) (by omega), mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ 1,
      if_pos (Finset.mem_range.mpr (by omega))]

private lemma powSeq_one {R : Type*} [CommRing R] (g : ℕ → R) (n : ℕ) :
    powSeq g 1 n = g n := by
  simp only [powSeq]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      g i * (if n - i = 0 then (1 : R) else 0) = if i = n then g n else 0 := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases h : i = n
    · rw [h]; simp
    · simp [h, show n - i ≠ 0 by omega]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ n,
    if_pos (Finset.mem_range.mpr (Nat.lt_succ_self n))]

private lemma powSeq_congr_lt {R : Type*} [CommRing R] {g1 g2 : ℕ → R} {n : ℕ}
    (hg10 : g1 0 = 0) (hg20 : g2 0 = 0) (hg : ∀ i < n, g1 i = g2 i) :
    ∀ k : ℕ, 2 ≤ k → powSeq g1 k n = powSeq g2 k n := by
  intro k hk
  cases k with
  | zero => omega
  | succ k =>
    simp only [powSeq]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hi0 : i = 0
    · rw [hi0, hg10, hg20, zero_mul, zero_mul]
    · by_cases hin_eq : i = n
      · rw [hin_eq, Nat.sub_self, powSeq_zero_of_lt hg10 k 0 (by omega),
          powSeq_zero_of_lt hg20 k 0 (by omega), mul_zero, mul_zero]
      · rw [hg i (by omega)]
        congr 1
        exact powSeq_congr (N := n - 1) (fun j hj => hg j (by omega)) k (n - i) (by omega)

private lemma comp_split {R : Type*} [CommRing R] {f g : ℕ → R}
    (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hg0 : g 0 = 0) (hg1 : g 1 = 1) {n : ℕ} (hn : 2 ≤ n) :
    comp f g n = f n + g n + ∑ k ∈ Finset.Icc 2 (n - 1), f k * powSeq g k n := by
  simp only [comp]
  rw [Finset.sum_range_succ]
  have hlow : ∑ k ∈ Finset.range n, f k * powSeq g k n =
      g n + ∑ k ∈ Finset.Icc 2 (n - 1), f k * powSeq g k n := by
    have hsplit : Finset.range n = insert 0 (insert 1 (Finset.Icc 2 (n - 1))) := by
      ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    simp only [hf0, zero_mul, zero_add, hf1, one_mul, powSeq_one]
  rw [hlow, powSeq_diag hg0, hg1, one_pow, mul_one]
  ring

private lemma comp_sub_diag {R : Type*} [CommRing R] {f1 f2 g1 g2 : ℕ → R} {n : ℕ} (hn : 2 ≤ n)
    (hf10 : f1 0 = 0) (hf20 : f2 0 = 0) (hf11 : f1 1 = 1) (hf21 : f2 1 = 1)
    (hg10 : g1 0 = 0) (hg20 : g2 0 = 0) (hg11 : g1 1 = 1) (hg21 : g2 1 = 1)
    (hf : ∀ i < n, f1 i = f2 i) (hg : ∀ i < n, g1 i = g2 i) :
    comp f1 g1 n - (f1 n + g1 n) = comp f2 g2 n - (f2 n + g2 n) := by
  rw [comp_split hf10 hf11 hg10 hg11 hn, comp_split hf20 hf21 hg20 hg21 hn]
  simp only [add_sub_cancel_left]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkn : k < n := by have := (Finset.mem_Icc.mp hk).2; omega
  rw [hf k hkn, powSeq_congr_lt hg10 hg20 hg k hk2]

/-- Hockey-stick identity: `∑_{j=0}^{m} C(j + k, k) = C(m + k + 1, k + 1)`. -/
private lemma hockey_stick (k : ℕ) :
    ∀ m : ℕ, ∑ j ∈ Finset.range (m + 1), Nat.choose (j + k) k = Nat.choose (m + k + 1) (k + 1) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : m + 1 + k = (m + k) + 1 := by omega
    rw [h1, add_comm, ← Nat.choose_succ_succ]

/-- Powers of `geom b`: `[x^n] (x / (1 - b*x))^k = C(n - 1, k - 1) * b^(n - k)` for `1 ≤ k ≤ n`. -/
private lemma powSeq_geom {R : Type*} [CommRing R] (b : R) :
    ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ,
      powSeq (geom b) k n = if k ≤ n then (Nat.choose (n - 1) (k - 1) : R) * b ^ (n - k) else 0 := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · intro n
      simp only [powSeq, geom]
      by_cases hn : 1 ≤ n
      · rw [if_pos hn]
        have hterm : ∀ i ∈ Finset.range (n + 1),
            (if i = 0 then (0 : R) else b ^ (i - 1)) * (if n - i = 0 then 1 else 0) =
            if i = n then b ^ (n - 1) else 0 := by
          intro i hi
          have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          by_cases h : i = n
          · rw [h]; simp [show n ≠ 0 by omega]
          · simp [h, show n - i ≠ 0 by omega]
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ n,
          if_pos (Finset.mem_range.mpr (Nat.lt_succ_self n))]
        simp
      · have hn0 : n = 0 := by omega
        subst hn0; simp
    · intro n
      simp only [powSeq]
      have hih := ih hkpos
      by_cases hkn : k + 1 ≤ n
      · rw [if_pos hkn]
        have hterm : ∀ i ∈ Finset.range (n + 1),
            geom b i * powSeq (geom b) k (n - i) =
            if 1 ≤ i ∧ i ≤ n - k then
              (Nat.choose (n - i - 1) (k - 1) : R) * b ^ (n - (k + 1))
            else 0 := by
          intro i hi
          have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          rw [hih (n - i)]
          dsimp [geom]
          by_cases hi0 : i = 0
          · subst hi0; simp
          · rw [if_neg hi0]
            by_cases hle : k ≤ n - i
            · rw [if_pos hle, if_pos ⟨by omega, by omega⟩]
              have hexp : (i - 1) + (n - i - k) = n - (k + 1) := by omega
              rw [← mul_assoc, mul_comm (b ^ (i - 1)), mul_assoc, ← pow_add, hexp]
            · rw [if_neg hle, if_neg (by omega), mul_zero]
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← Finset.sum_mul]
        congr 1
        have hbij : ∑ i ∈ (Finset.range (n + 1)).filter (fun i => 1 ≤ i ∧ i ≤ n - k),
            (Nat.choose (n - i - 1) (k - 1) : R) =
            ∑ j ∈ Finset.range (n - k), (Nat.choose (j + (k - 1)) (k - 1) : R) := by
          refine Finset.sum_bij (fun i _ => n - i - k) ?_ ?_ ?_ ?_
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢; omega
          · intro i1 h1 i2 h2 heq
            simp only [Finset.mem_filter, Finset.mem_range] at h1 h2; omega
          · intro j hj
            have hjlt : j < n - k := Finset.mem_range.mp hj
            refine ⟨n - k - j, ?_, by omega⟩
            simp only [Finset.mem_filter, Finset.mem_range]; omega
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_range] at hi
            congr 2; omega
        rw [hbij, ← Nat.cast_sum]
        have hnk : n - k = (n - k - 1) + 1 := by omega
        rw [hnk, hockey_stick (k - 1) (n - k - 1)]
        congr 2 <;> omega
      · rw [if_neg hkn]
        refine Finset.sum_eq_zero (fun i hi => ?_)
        have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [hih (n - i)]
        dsimp [geom]
        by_cases hi0 : i = 0
        · subst hi0; simp
        · rw [if_neg hi0, if_neg (by omega), mul_zero]

/-- Composition of geometric series: `(geom a) ∘ (geom b) = geom (a + b)`. -/
private lemma comp_geom {R : Type*} [CommRing R] (a b : R) :
    comp (geom a) (geom b) = geom (a + b) := by
  ext n
  cases n with
  | zero => simp [comp, geom]
  | succ n =>
    simp only [comp, geom, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [Finset.sum_range_succ']
    simp only [if_true, zero_mul, add_zero]
    have hterm : ∀ k ∈ Finset.range (n + 1),
        (if k + 1 = 0 then (0 : R) else a ^ (k + 1 - 1)) * powSeq (geom b) (k + 1) (n + 1) =
        a ^ k * b ^ (n - k) * (Nat.choose n k : R) := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel, powSeq_geom b (k + 1) (by omega) (n + 1),
        if_pos (by omega), Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.succ_sub_succ]
      ring
    rw [Finset.sum_congr rfl hterm, ← add_pow]

/-- `r`-fold composition of `geom 1` is `geom (r : R)`. -/
private lemma iterComp_geom_one {R : Type*} [CommRing R] :
    ∀ r : ℕ, iterComp (geom (1 : R)) r = geom (r : R) := by
  intro r
  induction r with
  | zero =>
    ext n
    simp only [iterComp, geom, Nat.cast_zero]
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simp
      | succ n => simp [zero_pow (Nat.succ_ne_zero n)]
  | succ r ih =>
    have hfun : iterComp (geom (1 : R)) (r + 1) = comp (geom (1 : R)) (iterComp (geom (1 : R)) r) := rfl
    rw [hfun, ih, comp_geom, Nat.cast_succ, add_comm]

private lemma prove_a396102 (a : ℕ → ℤ) (ha0 : a 0 = 0) (ha1 : a 1 = 1)
    (harec : ∀ n : ℕ, iterComp a 3 (n + 1) = iterComp a 2 (n + 1) + iterComp a 2 n)
    (n : ℕ) (hn : 1 ≤ n) : a n ≡ 1 [ZMOD 3] := by
  let φ : ℤ →+* ZMod 3 := Int.castRingHom (ZMod 3)
  let b : ℕ → ZMod 3 := fun i => φ (a i)
  let g : ℕ → ZMod 3 := geom (1 : ZMod 3)
  have hb0 : b 0 = 0 := by simp [b, ha0]
  have hb1 : b 1 = 1 := by simp [b, ha1]
  have hg0 : g 0 = 0 := by simp [g, geom]
  have hg1 : g 1 = 1 := by simp [g, geom]
  have hbrec : ∀ m : ℕ, iterComp b 3 (m + 1) = iterComp b 2 (m + 1) + iterComp b 2 m := by
    intro m
    have h := congr_arg φ (harec m)
    rw [map_add, iterComp_map, iterComp_map, iterComp_map] at h
    exact h
  have hgrec : ∀ m : ℕ, 1 ≤ m → iterComp g 3 (m + 1) = iterComp g 2 (m + 1) + iterComp g 2 m := by
    intro m hm
    rw [iterComp_geom_one, iterComp_geom_one]
    have h3 : ((3 : ℕ) : ZMod 3) = 0 := by decide
    have h2 : ((2 : ℕ) : ZMod 3) = -1 := by decide
    rw [h3, h2]
    simp only [geom, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, show m ≠ 0 by omega]
    rw [zero_pow (by omega)]
    have hpow : (-1 : ZMod 3) ^ m = (-1 : ZMod 3) * (-1 : ZMod 3) ^ (m - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hm, pow_succ']
    rw [hpow]
    ring
  have hmod : ∀ k : ℕ, b k = g k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      rcases k with _ | _ | m
      · exact hb0.trans hg0.symm
      · exact hb1.trans hg1.symm
      · have h2_congr : ∀ i < m + 2, iterComp b 2 i = iterComp g 2 i :=
          fun i hi => iterComp_congr (N := m + 1) (fun j hj => ih j (by omega)) 2 i (by omega)
        have hgb20 : iterComp g 2 0 = 0 := by rw [iterComp_geom_one]; simp [geom]
        have hgb21 : iterComp g 2 1 = 1 := by rw [iterComp_geom_one]; simp [geom]
        have hb20 : iterComp b 2 0 = 0 := (h2_congr 0 (by omega)).trans hgb20
        have hb21 : iterComp b 2 1 = 1 := (h2_congr 1 (by omega)).trans hgb21
        have hdiag := comp_sub_diag (n := m + 2) (by omega)
          hb0 hg0 hb1 hg1 hb20 hgb20 hb21 hgb21
          (fun i hi => ih i hi) h2_congr
        have hb3 : comp b (iterComp b 2) (m + 2) = iterComp b 2 (m + 2) + iterComp b 2 (m + 1) :=
          hbrec (m + 1)
        have hg3 : comp g (iterComp g 2) (m + 2) = iterComp g 2 (m + 2) + iterComp g 2 (m + 1) :=
          hgrec (m + 1) (by omega)
        have hprev : iterComp b 2 (m + 1) = iterComp g 2 (m + 1) := h2_congr (m + 1) (by omega)
        rw [hb3, hg3, hprev] at hdiag
        have hneg : -(b (m + 2)) = -(g (m + 2)) := by
          linear_combination hdiag
        exact neg_inj.mp hneg
  have h1 : (a n : ZMod 3) = ((1 : ℤ) : ZMod 3) := by
    have := hmod n
    simpa [b, φ, g, geom, show n ≠ 0 by omega] using this
  exact (ZMod.intCast_eq_intCast_iff (a n) 1 3).mp h1

end OMA.P_oeis_a396102

theorem OMA.solution : type_of% @OMA.S_oeis_a396102.main :=
  OMA.P_oeis_a396102.prove_a396102
