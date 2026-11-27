import OMAReductions.R_Erdos535_erdos_535_variants_first_open_case_R1
import Mathlib

-- Step Erdos535.erdos_535.variants.first_open_case.R1.H2: hypothesis H2 of reduction Erdos535.erdos_535.variants.first_open_case.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! g n records the exponents of the primes up to t, which are at most log₂ N. enc n contains one
even token 2 * pair(p, j) for each prime p > t and each j < v_p(n), padded with odd tokens up to
size K. The even part of enc a ∩ enc b recovers min(v_p a, v_p b) for p > t, and the equal g-values
fix the small primes, so the factorizations of gcd a b and gcd c d agree. -/

namespace Erdos535StepH2

open Finset

def R (t n : ℕ) : Finset ℕ :=
  (n.primeFactors.filter (t < ·)).biUnion (fun p => (range (n.factorization p)).image
    (fun j => 2 * Nat.pair p j))

def enc (t K n : ℕ) : Finset ℕ :=
  R t n ∪ (range (K - (R t n).card)).image (fun i => 2 * i + 1)

lemma mem_R {t n p j : ℕ} : 2 * Nat.pair p j ∈ R t n ↔
    p ∈ n.primeFactors ∧ t < p ∧ j < n.factorization p := by
  constructor
  · intro h
    simp only [R, mem_biUnion, mem_filter, mem_image, mem_range] at h
    obtain ⟨q, ⟨hq, htq⟩, i, hi, he⟩ := h
    have he' : Nat.pair q i = Nat.pair p j := by omega
    rw [Nat.pair_eq_pair] at he'
    obtain ⟨rfl, rfl⟩ := he'
    exact ⟨hq, htq, hi⟩
  · rintro ⟨hp, htp, hj⟩
    simp only [R, mem_biUnion, mem_filter, mem_image, mem_range]
    exact ⟨p, ⟨hp, htp⟩, j, hj, rfl⟩

lemma R_even {t n x : ℕ} (h : x ∈ R t n) : Even x := by
  simp only [R, mem_biUnion, mem_image] at h
  obtain ⟨_, _, _, _, rfl⟩ := h
  exact even_two_mul _

lemma card_R_le (t n : ℕ) : (R t n).card ≤ ∑ p ∈ n.primeFactors.filter (t < ·), n.factorization p := by
  unfold R
  refine (card_biUnion_le).trans (sum_le_sum fun p _ => ?_)
  exact card_image_le.trans (by simp)

lemma card_enc (t K n : ℕ) (h : (R t n).card ≤ K) : (enc t K n).card = K := by
  unfold enc
  rw [card_union_of_disjoint]
  · rw [card_image_of_injective _ (fun a b hab => by simpa using hab), card_range]
    omega
  · rw [disjoint_left]
    intro x hx hx2
    have he := R_even hx
    simp only [mem_image] at hx2
    obtain ⟨i, -, rfl⟩ := hx2
    exact (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one i)) he

lemma even_inter {t K a b x : ℕ} : x ∈ enc t K a ∩ enc t K b ∧ Even x ↔ x ∈ R t a ∩ R t b := by
  constructor
  · rintro ⟨hx, he⟩
    rw [mem_inter] at hx ⊢
    have odd_not : ∀ n, x ∈ (range (K - (R t n).card)).image (fun i => 2 * i + 1) → False := by
      intro n h
      simp only [mem_image] at h
      obtain ⟨i, -, rfl⟩ := h
      exact (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one i)) he
    unfold enc at hx
    rcases mem_union.mp hx.1 with h1 | h1
    · rcases mem_union.mp hx.2 with h2 | h2
      · exact ⟨h1, h2⟩
      · exact (odd_not b h2).elim
    · exact (odd_not a h1).elim
  · intro hx
    rw [mem_inter] at hx
    exact ⟨mem_inter.mpr ⟨mem_union_left _ hx.1, mem_union_left _ hx.2⟩, R_even hx.1⟩

lemma fact_le_log {n p N : ℕ} (hn : n ≠ 0) (hN : n ≤ N) (hp : p.Prime) :
    n.factorization p ≤ Nat.log 2 N := by
  apply Nat.le_log_of_pow_le (by norm_num)
  calc 2 ^ n.factorization p ≤ p ^ n.factorization p := Nat.pow_le_pow_left hp.two_le _
    _ ≤ n := Nat.ordProj_le p hn
    _ ≤ N := hN

theorem main : ∀ t K N : ℕ, (∀ n ∈ Finset.Icc 1 N, ∑ p ∈ n.primeFactors.filter (t < ·), n.factorization p ≤ K) → ∃ (g : ℕ → Fin (t + 1) → Fin (Nat.log 2 N + 1)) (enc : ℕ → Finset ℕ), (∀ n ∈ Finset.Icc 1 N, (enc n).card = K) ∧ ∀ a ∈ Finset.Icc 1 N, ∀ b ∈ Finset.Icc 1 N, ∀ c ∈ Finset.Icc 1 N, ∀ d ∈ Finset.Icc 1 N, g a = g b → g a = g c → g a = g d → enc a ∩ enc b = enc c ∩ enc d → Nat.gcd a b = Nat.gcd c d := by
  intro t K N hK
  refine ⟨fun n i => ⟨min (n.factorization i) (Nat.log 2 N), by omega⟩, enc t K, ?_, ?_⟩
  · intro n hn
    exact card_enc t K n ((card_R_le t n).trans (hK n hn))
  · intro a ha b hb c hc d hd hab hac had he
    have ha0 : a ≠ 0 := by have := (mem_Icc.mp ha).1; omega
    have hb0 : b ≠ 0 := by have := (mem_Icc.mp hb).1; omega
    have hc0 : c ≠ 0 := by have := (mem_Icc.mp hc).1; omega
    have hd0 : d ≠ 0 := by have := (mem_Icc.mp hd).1; omega
    apply Nat.eq_of_factorization_eq (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero ha0)).ne'
      (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hc0)).ne'
    intro p
    rw [Nat.factorization_gcd ha0 hb0, Nat.factorization_gcd hc0 hd0]
    simp only [Finsupp.inf_apply]
    by_cases hp : p.Prime
    · by_cases hpt : p ≤ t
      · have small : ∀ x y : ℕ, x ∈ Finset.Icc 1 N → y ∈ Finset.Icc 1 N →
            (fun i : Fin (t + 1) => (⟨min (x.factorization i) (Nat.log 2 N), by omega⟩ :
              Fin (Nat.log 2 N + 1))) = (fun i => ⟨min (y.factorization i) (Nat.log 2 N), by omega⟩) →
            x.factorization p = y.factorization p := by
          intro x y hx hy hxy
          have h1 := congrArg Fin.val (congrFun hxy ⟨p, by omega⟩)
          simp only at h1
          have hx0 : x ≠ 0 := by have := (mem_Icc.mp hx).1; omega
          have hy0 : y ≠ 0 := by have := (mem_Icc.mp hy).1; omega
          have := fact_le_log hx0 (mem_Icc.mp hx).2 hp
          have := fact_le_log hy0 (mem_Icc.mp hy).2 hp
          omega
        have e1 := small a b ha hb hab
        have e2 := small a c ha hc hac
        have e3 := small a d ha hd had
        rw [← e1, ← e2, ← e3]
      · push Not at hpt
        have key : ∀ j, (j < a.factorization p ∧ j < b.factorization p) ↔
            (j < c.factorization p ∧ j < d.factorization p) := by
          intro j
          have h1 : 2 * Nat.pair p j ∈ enc t K a ∩ enc t K b ∧ Even (2 * Nat.pair p j) ↔
              2 * Nat.pair p j ∈ enc t K c ∩ enc t K d ∧ Even (2 * Nat.pair p j) := by rw [he]
          rw [even_inter, even_inter, mem_inter, mem_inter, mem_R, mem_R, mem_R, mem_R] at h1
          have pa : p ∈ a.primeFactors ↔ 0 < a.factorization p := by
            rw [← Nat.support_factorization, Finsupp.mem_support_iff]; omega
          have pb : p ∈ b.primeFactors ↔ 0 < b.factorization p := by
            rw [← Nat.support_factorization, Finsupp.mem_support_iff]; omega
          have pc : p ∈ c.primeFactors ↔ 0 < c.factorization p := by
            rw [← Nat.support_factorization, Finsupp.mem_support_iff]; omega
          have pd : p ∈ d.primeFactors ↔ 0 < d.factorization p := by
            rw [← Nat.support_factorization, Finsupp.mem_support_iff]; omega
          rw [pa, pb, pc, pd] at h1
          constructor
          · intro h; have := h1.mp ⟨⟨by omega, hpt, h.1⟩, ⟨by omega, hpt, h.2⟩⟩; exact ⟨this.1.2.2, this.2.2.2⟩
          · intro h; have := h1.mpr ⟨⟨by omega, hpt, h.1⟩, ⟨by omega, hpt, h.2⟩⟩; exact ⟨this.1.2.2, this.2.2.2⟩
        have k1 := key (min (a.factorization p) (b.factorization p))
        have k2 := key (min (c.factorization p) (d.factorization p))
        apply le_antisymm
        · by_contra hlt
          push Not at hlt
          have := k2.mpr (by constructor <;> omega)
          omega
        · by_contra hlt
          push Not at hlt
          have := k1.mp (by constructor <;> omega)
          omega
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

end Erdos535StepH2

theorem OMA.solution : OMA.R_Erdos535_erdos_535_variants_first_open_case_R1.H2 := Erdos535StepH2.main
