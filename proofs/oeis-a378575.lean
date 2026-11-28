import OMAStatements.S_oeis_a378575
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a378575

open OMA.S_oeis_a378575

/-- The geometric series `x / (1 - c * x) = ∑_{n ≥ 1} c^(n - 1) * x^n`. -/
private def geom {R : Type*} [CommRing R] (c : R) (n : ℕ) : R :=
  if n = 0 then 0 else c ^ (n - 1)

private lemma powSeq_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (g : ℕ → R) :
    ∀ k n : ℕ, φ (powSeq g k n) = powSeq (fun i => φ (g i)) k n := by
  intro k
  induction k with
  | zero =>
    intro n; dsimp [powSeq]; split_ifs <;> simp
  | succ k ih =>
    intro n
    simp only [powSeq, map_sum, map_mul, ih]

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

private lemma prove_a378575 (a : ℕ → ℤ) (ha0 : a 0 = 0)
    (harec : ∀ n : ℕ, a (n + 1) = (if n = 0 then 1 else 0) + iterComp a 5 n)
    (n : ℕ) (hn : 1 ≤ n) : a n ≡ 1 [ZMOD 4] := by
  let φ : ℤ →+* ZMod 4 := Int.castRingHom (ZMod 4)
  have hmod : ∀ k : ℕ, φ (a k) = geom (1 : ZMod 4) k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero => simp [ha0, geom]
      | succ k =>
        rw [harec k, map_add, iterComp_map]
        have hcongr : iterComp (fun i => φ (a i)) 5 k = iterComp (geom (1 : ZMod 4)) 5 k :=
          iterComp_congr (fun i hi => ih i (by omega)) 5 k le_rfl
        rw [hcongr, iterComp_geom_one]
        have h5 : ((5 : ℕ) : ZMod 4) = 1 := by decide
        rw [h5]
        cases k with
        | zero => simp [geom]
        | succ k => simp [geom]
  have h1 : (a n : ZMod 4) = ((1 : ℤ) : ZMod 4) := by
    have := hmod n
    simpa [φ, geom, show n ≠ 0 by omega] using this
  exact (ZMod.intCast_eq_intCast_iff (a n) 1 4).mp h1

end OMA.P_oeis_a378575

theorem OMA.solution : type_of% @OMA.S_oeis_a378575.main :=
  OMA.P_oeis_a378575.prove_a378575
