import OMAReductions.R_Erdos604_erdos_604_variants_grid_upper_bound_R1
import Mathlib

/-! A divisor decomposition of the logarithm on integers with even inert-prime
valuations, followed by the Chebyshev bound for the von Mangoldt sum. -/

open Finset Filter ArithmeticFunction
namespace Grid604
def Good (m : ℕ) : Prop := ∀ q ∈ m.primeFactors, q % 4 = 3 → Even (padicValNat q m)

lemma good_mul {x y : ℕ} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : Good x) (hy : Good y) :
    Good (x * y) := by
  intro q hq h3
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have := Fact.mk hqp
  rw [padicValNat.mul hx0 hy0]
  have ex : Even (padicValNat q x) := by
    by_cases hqx : q ∣ x
    · exact hx q (Nat.mem_primeFactors.2 ⟨hqp, hqx, hx0⟩) h3
    · rw [padicValNat.eq_zero_of_not_dvd hqx]; exact ⟨0, rfl⟩
  have ey : Even (padicValNat q y) := by
    by_cases hqy : q ∣ y
    · exact hy q (Nat.mem_primeFactors.2 ⟨hqp, hqy, hy0⟩) h3
    · rw [padicValNat.eq_zero_of_not_dvd hqy]; exact ⟨0, rfl⟩
  exact ex.add ey

lemma good_of_coprime_mul {a b : ℕ} (hab : a.Coprime b) (h : Good (a * b)) (hb0 : b ≠ 0) :
    Good a := by
  intro q hq h3
  have hqp := Nat.prime_of_mem_primeFactors hq
  have := Fact.mk hqp
  have hqa := Nat.dvd_of_mem_primeFactors hq
  have ha0 : a ≠ 0 := (Nat.mem_primeFactors.1 hq).2.2
  have hqb : ¬ q ∣ b := (Nat.Prime.coprime_iff_not_dvd hqp).1 (Nat.Coprime.coprime_dvd_left hqa hab)
  have := h q (Nat.mem_primeFactors.2 ⟨hqp, dvd_mul_of_dvd_left hqa b, mul_ne_zero ha0 hb0⟩) h3
  rwa [padicValNat.mul ha0 hb0, padicValNat.eq_zero_of_not_dvd hqb, add_zero] at this

lemma good_prime_pow {p i : ℕ} (hp : p.Prime) (h : p % 4 = 3 → Even i) : Good (p ^ i) := by
  have := Fact.mk hp
  intro q hq h3
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp at hq
  rw [Nat.primeFactors_prime_pow hi.ne' hp, Finset.mem_singleton] at hq
  subst hq
  rw [padicValNat.prime_pow]; exact h h3

open scoped Classical in
lemma log_le_split_div (m : ℕ) (hm : Good m) :
    Real.log m ≤ 2 * ∑ d ∈ m.divisors, if Good (m / d) then Λ d else 0 := by
  revert hm
  refine Nat.recOnPrimeCoprime ?_ ?_ ?_ m
  · intro _; simp
  · intro p k hp hgood
    have := Fact.mk hp
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    by_cases h3 : p % 4 = 3
    · -- k is even
      have hk : Even k := by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · exact ⟨0, rfl⟩
        have := hgood p (by rw [Nat.primeFactors_prime_pow hk.ne' hp]; simp) h3
        rwa [padicValNat.prime_pow] at this
      obtain ⟨r, rfl⟩ := hk
      rw [Nat.sum_divisors_prime_pow hp]
      have hsub : (range r).image (fun i => 2 * i + 2) ⊆ range (r + r + 1) := by
        intro x hx
        simp only [Finset.mem_image, mem_range] at hx ⊢
        obtain ⟨i, hi, rfl⟩ := hx
        omega
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (f := fun x => if Good (p ^ (r + r) / p ^ x) then Λ (p ^ x) else 0)
        (fun x _ _ => by
          split_ifs
          · exact vonMangoldt_nonneg
          · exact le_refl _)
      rw [Finset.sum_image (fun a _ b _ h => by omega)] at hle
      have hterm : ∀ i ∈ range r,
          (if Good (p ^ (r + r) / p ^ (2 * i + 2)) then Λ (p ^ (2 * i + 2)) else 0)
            = Real.log p := by
        intro i hi
        simp only [mem_range] at hi
        rw [Nat.pow_div (by omega) hp.pos, if_pos, vonMangoldt_apply_pow (by omega),
          vonMangoldt_apply_prime hp]
        apply good_prime_pow hp
        intro _
        exact ⟨r - i - 1, by omega⟩
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_range, nsmul_eq_mul] at hle
      rw [Nat.cast_pow, Real.log_pow]
      push_cast
      nlinarith
    · -- every divisor is eligible
      have hall : ∀ d ∈ (p ^ k).divisors,
          (if Good (p ^ k / d) then Λ d else 0) = Λ d := by
        intro d hd
        obtain ⟨x, hx, rfl⟩ := (Nat.dvd_prime_pow hp).1 (Nat.dvd_of_mem_divisors hd)
        rw [Nat.pow_div hx hp.pos, if_pos]
        exact good_prime_pow hp (fun h => absurd h h3)
      rw [Finset.sum_congr rfl hall, vonMangoldt_sum]
      have : 0 ≤ Real.log ((p ^ k : ℕ) : ℝ) := Real.log_natCast_nonneg _
      linarith
  · intro a b ha hb hab iha ihb hgood
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hga : Good a := good_of_coprime_mul hab hgood hb0
    have hgb : Good b := good_of_coprime_mul hab.symm (by rwa [mul_comm]) ha0
    have h1 := iha hga
    have h2 := ihb hgb
    set f : ℕ → ℕ → ℝ := fun n d => if Good (n / d) then Λ d else 0 with hf
    have hnn : ∀ n d, 0 ≤ f n d := fun n d => by
      simp only [hf]; split_ifs
      · exact vonMangoldt_nonneg
      · exact le_refl _
    have hfilt : ∀ n, ∑ d ∈ n.divisors with IsPrimePow d, f n d = ∑ d ∈ n.divisors, f n d := by
      intro n
      apply Finset.sum_filter_of_ne
      intro d _ hd
      by_contra hpp
      apply hd
      simp only [hf]
      split_ifs
      · exact vonMangoldt_eq_zero_iff.2 hpp
      · rfl
    have hsplit : ∑ d ∈ (a * b).divisors, f (a * b) d =
        ∑ d ∈ a.divisors with IsPrimePow d, f (a * b) d +
        ∑ d ∈ b.divisors with IsPrimePow d, f (a * b) d := by
      rw [← hfilt, Nat.mul_divisors_filter_prime_pow hab, filter_union,
        sum_union (Nat.disjoint_divisors_filter_isPrimePow hab)]
    have hA : ∑ d ∈ a.divisors with IsPrimePow d, f a d ≤
        ∑ d ∈ a.divisors with IsPrimePow d, f (a * b) d := by
      apply Finset.sum_le_sum
      intro d hd
      have hda : d ∣ a := Nat.dvd_of_mem_divisors (Finset.mem_filter.1 hd).1
      simp only [hf]
      by_cases hg : Good (a / d)
      · have had0 : a / d ≠ 0 :=
          (Nat.div_pos (Nat.le_of_dvd (by omega) hda) (Nat.pos_of_dvd_of_pos hda (by omega))).ne'
        rw [if_pos hg, if_pos]
        rw [Nat.mul_div_right_comm hda]
        exact good_mul had0 hb0 hg hgb
      · rw [if_neg hg]; exact hnn _ _
    have hB : ∑ d ∈ b.divisors with IsPrimePow d, f b d ≤
        ∑ d ∈ b.divisors with IsPrimePow d, f (a * b) d := by
      apply Finset.sum_le_sum
      intro d hd
      have hdb : d ∣ b := Nat.dvd_of_mem_divisors (Finset.mem_filter.1 hd).1
      simp only [hf]
      by_cases hg : Good (b / d)
      · have hbd0 : b / d ≠ 0 :=
          (Nat.div_pos (Nat.le_of_dvd (by omega) hdb) (Nat.pos_of_dvd_of_pos hdb (by omega))).ne'
        rw [if_pos hg, if_pos]
        rw [Nat.mul_div_assoc a hdb]
        exact good_mul ha0 hbd0 hga hg
      · rw [if_neg hg]; exact hnn _ _
    have h1' : Real.log a ≤ 2 * ∑ d ∈ a.divisors, f a d := h1
    have h2' : Real.log b ≤ 2 * ∑ d ∈ b.divisors, f b d := h2
    rw [← hfilt] at h1' h2'
    show Real.log ((a * b : ℕ) : ℝ) ≤ 2 * ∑ d ∈ (a * b).divisors, f (a * b) d
    rw [hsplit, Nat.cast_mul, Real.log_mul (by exact_mod_cast ha0) (by exact_mod_cast hb0)]
    linarith

open scoped Classical in
theorem log_le_split (m : ℕ) (hm : Good m) :
  Real.log m ≤ 2 * ∑ z ∈ m.divisorsAntidiagonal, if Good z.2 then ArithmeticFunction.vonMangoldt z.1 else 0 := by
  rw [Nat.sum_divisorsAntidiagonal (fun x y => if Good y then ArithmeticFunction.vonMangoldt x else 0)]
  exact log_le_split_div m hm


open Classical in
/-- Summing the local estimate `hl` over good `m ≤ N`, reindexing by `(d, k)` with `d * k ≤ N`,
and bounding the inner von Mangoldt sums by Chebyshev's bound `ψ x ≤ (log 4 + 4) x`. -/
theorem global_bound
    (hl : ∀ m : ℕ, Good m → Real.log m ≤
      2 * ∑ z ∈ m.divisorsAntidiagonal,
        if Good z.2 then ArithmeticFunction.vonMangoldt z.1 else 0)
    (N : ℕ) :
    let S := (Finset.range (N+1)).filter Good
    (∑ m ∈ S, Real.log m) ≤ (2 * (Real.log 4 + 4)) * N * ∑ m ∈ S, (m : ℝ)⁻¹ := by
  intro S
  set f : ℕ × ℕ → ℝ := fun z => if Good z.2 then ArithmeticFunction.vonMangoldt z.1 else 0
    with hf
  have hf0 : ∀ z, 0 ≤ f z := fun z => by
    simp only [hf]; split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
  -- Step 1: sum hl and drop the condition `Good m`.
  have h1 : (∑ m ∈ S, Real.log m) ≤
      2 * ∑ m ∈ Finset.range (N+1), ∑ z ∈ m.divisorsAntidiagonal, f z := by
    calc (∑ m ∈ S, Real.log m)
        ≤ ∑ m ∈ S, 2 * ∑ z ∈ m.divisorsAntidiagonal, f z :=
          Finset.sum_le_sum fun m hm => hl m (Finset.mem_filter.1 hm).2
      _ = 2 * ∑ m ∈ S, ∑ z ∈ m.divisorsAntidiagonal, f z := by rw [Finset.mul_sum]
      _ ≤ 2 * ∑ m ∈ Finset.range (N+1), ∑ z ∈ m.divisorsAntidiagonal, f z := by
          gcongr 2 * ?_
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun m _ _ => Finset.sum_nonneg fun z _ => hf0 z
  -- Step 2: reindex over pairs `(d, k)` with `d * k ≤ N`.
  set P : Finset (ℕ × ℕ) := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun z => z.1 * z.2 ≤ N)
    with hP
  have h2 : ∑ m ∈ Finset.range (N+1), ∑ z ∈ m.divisorsAntidiagonal, f z = ∑ z ∈ P, f z := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := P) (t := Finset.range (N+1))
      (g := fun z => z.1 * z.2)]
    · refine Finset.sum_congr rfl fun m hm => ?_
      have hmN : m ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
      congr 1
      ext ⟨d, k⟩
      simp only [Nat.mem_divisorsAntidiagonal, hP, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc]
      constructor
      · rintro ⟨rfl, h0⟩
        have hd : d ≠ 0 := fun h => h0 (by simp [h])
        have hk : k ≠ 0 := fun h => h0 (by simp [h])
        have h1d : d ≤ N := le_trans (Nat.le_mul_of_pos_right d (Nat.pos_of_ne_zero hk)) hmN
        have h1k : k ≤ N := le_trans (Nat.le_mul_of_pos_left k (Nat.pos_of_ne_zero hd)) hmN
        exact ⟨⟨⟨⟨Nat.one_le_iff_ne_zero.2 hd, h1d⟩, Nat.one_le_iff_ne_zero.2 hk, h1k⟩, hmN⟩, rfl⟩
      · rintro ⟨⟨⟨⟨hd, -⟩, hk, -⟩, -⟩, rfl⟩
        exact ⟨rfl, Nat.mul_ne_zero (by omega) (by omega)⟩
    · intro z hz
      rw [hP, Finset.mem_filter] at hz
      exact Finset.mem_range.2 (Nat.lt_succ_of_le hz.2)
  -- Step 3: regroup by `k`; the inner sum is `ψ (N / k)`.
  have h3 : ∑ z ∈ P, f z =
      ∑ k ∈ Finset.Icc 1 N, if Good k then Chebyshev.psi ((N : ℝ) / k) else 0 := by
    rw [hP, Finset.sum_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    have hkpos : 0 < k := hk1
    simp only [hf]
    split_ifs with hg
    · rw [Chebyshev.psi, Nat.floor_div_eq_div, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
      rw [Nat.le_div_iff_mul_le hkpos]
      constructor
      · rintro ⟨⟨hd, -⟩, h⟩; exact ⟨hd, h⟩
      · rintro ⟨hd, h⟩
        exact ⟨⟨hd, le_trans (Nat.le_mul_of_pos_right d hkpos) h⟩, h⟩
    · simp
  -- Step 4: Chebyshev's bound.
  have h4 : ∑ k ∈ Finset.Icc 1 N, (if Good k then Chebyshev.psi ((N : ℝ) / k) else 0) ≤
      (Real.log 4 + 4) * N * ∑ m ∈ S, (m : ℝ)⁻¹ := by
    have hS : ∑ m ∈ S, (m : ℝ)⁻¹ =
        ∑ k ∈ Finset.range (N+1), if Good k then (k : ℝ)⁻¹ else 0 := by
      simp only [S]; rw [Finset.sum_filter]
    rw [hS, Finset.mul_sum]
    calc ∑ k ∈ Finset.Icc 1 N, (if Good k then Chebyshev.psi ((N : ℝ) / k) else 0)
        ≤ ∑ k ∈ Finset.Icc 1 N, (Real.log 4 + 4) * N * (if Good k then (k : ℝ)⁻¹ else 0) := by
          refine Finset.sum_le_sum fun k _ => ?_
          split_ifs
          · have := Chebyshev.psi_le_const_mul_self (x := (N : ℝ) / k) (by positivity)
            rw [div_eq_mul_inv, ← mul_assoc] at this
            exact this
          · simp
      _ ≤ ∑ k ∈ Finset.range (N+1), (Real.log 4 + 4) * N * (if Good k then (k : ℝ)⁻¹ else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => ?_
          · intro k hk
            exact Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hk).2)
          · have : (0 : ℝ) ≤ Real.log 4 + 4 := by
              have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
            split_ifs <;> positivity
  calc (∑ m ∈ S, Real.log m)
      ≤ 2 * ∑ m ∈ Finset.range (N+1), ∑ z ∈ m.divisorsAntidiagonal, f z := h1
    _ = 2 * ∑ k ∈ Finset.Icc 1 N, (if Good k then Chebyshev.psi ((N : ℝ) / k) else 0) := by
        rw [h2, h3]
    _ ≤ 2 * ((Real.log 4 + 4) * N * ∑ m ∈ S, (m : ℝ)⁻¹) := by gcongr
    _ = (2 * (Real.log 4 + 4)) * N * ∑ m ∈ S, (m : ℝ)⁻¹ := by ring

end Grid604

theorem OMA.solution : OMA.R_Erdos604_erdos_604_variants_grid_upper_bound_R1.H2 := by
  refine ⟨2 * (Real.log 4 + 4), by positivity, Filter.Eventually.of_forall ?_⟩
  intro N
  classical
  have h := Grid604.global_bound Grid604.log_le_split N
  dsimp only at h ⊢
  convert h using 1 <;> congr! 3 <;> ext m <;> simp [Grid604.Good]
