import OMAReductions.R_Erdos700_erdos_700_parts_ii_R1

-- Step Erdos700.erdos_700.parts.ii.R1.H2: hypothesis H2 of reduction Erdos700.erdos_700.parts.ii.R1
-- Credit: @implicitall
-- Proof: Chebyshev's lower bound from 4^n ≤ (2n+1) C(2n,n) ≤ (2n+1) (2n)^π(2n) gives many primes in
-- (2Y^2, Y^3] for Y = 2^m; by pigeonhole some block [iY, (i+1)Y) holds m + 2 of them, and m + 2
-- points of diameter < 2^m always contain p < q < r with q - p < r - q (otherwise the distance to
-- the maximum halves at each step). Then 2 (r - p)^2 < 2 Y^2 < p.

namespace OMA_E700H2

open Finset

lemma cheb (n : ℕ) (hn : 0 < n) :
    4 ^ n ≤ (2 * n + 1) * (2 * n) ^ (Nat.count Nat.Prime (2 * n + 1)) := by
  refine le_trans (Nat.four_pow_le_two_mul_add_one_mul_central_binom n) ?_
  apply Nat.mul_le_mul_left
  have hC0 : (2 * n).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  calc (2 * n).choose n
      = ∏ p ∈ ((2 * n).choose n).primeFactors, p ^ ((2 * n).choose n).factorization p :=
        Nat.prod_primeFactors_pow_factorization hC0
    _ ≤ (2 * n) ^ ((2 * n).choose n).primeFactors.card :=
        Finset.prod_le_pow_card _ _ _ (fun p _ => Nat.pow_factorization_choose_le (by omega))
    _ ≤ (2 * n) ^ (Nat.count Nat.Prime (2 * n + 1)) := by
        apply Nat.pow_le_pow_right (by omega)
        rw [Nat.count_eq_card_filter_range]
        apply Finset.card_le_card
        intro p hp
        have hp' := Nat.mem_primeFactors.mp hp
        have hv : 0 < ((2 * n).choose n).factorization p :=
          hp'.1.factorization_pos_of_dvd hC0 hp'.2.1
        have h1 : p ≤ p ^ ((2 * n).choose n).factorization p := Nat.le_self_pow hv.ne' p
        have h2 : p ^ ((2 * n).choose n).factorization p ≤ 2 * n :=
          Nat.pow_factorization_choose_le (by omega)
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hp'.1⟩

lemma chebPow (s : ℕ) :
    2 ^ (s + 1) ≤ s + 2 + (s + 1) * Nat.count Nat.Prime (2 ^ (s + 1) + 1) := by
  have h := cheb (2 ^ s) (by positivity)
  have e1 : 2 * 2 ^ s = 2 ^ (s + 1) := by ring
  rw [e1] at h
  have e2 : (4 : ℕ) ^ (2 ^ s) = 2 ^ (2 ^ (s + 1)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
  have e3 : 2 ^ (s + 1) + 1 ≤ 2 ^ (s + 2) := by
    have : 1 ≤ 2 ^ (s + 1) := Nat.one_le_two_pow
    rw [pow_succ 2 (s + 1)]; omega
  have e4 : ((2 : ℕ) ^ (s + 1)) ^ Nat.count Nat.Prime (2 ^ (s + 1) + 1) =
      2 ^ ((s + 1) * Nat.count Nat.Prime (2 ^ (s + 1) + 1)) := by rw [← pow_mul]
  rw [e2, e4] at h
  set c := Nat.count Nat.Prime (2 ^ (s + 1) + 1) with hc
  have h2 : 2 ^ (2 ^ (s + 1)) ≤ 2 ^ (s + 2 + (s + 1) * c) :=
    calc 2 ^ (2 ^ (s + 1)) ≤ (2 ^ (s + 1) + 1) * 2 ^ ((s + 1) * c) := h
      _ ≤ 2 ^ (s + 2) * 2 ^ ((s + 1) * c) := Nat.mul_le_mul_right _ e3
      _ = 2 ^ (s + 2 + (s + 1) * c) := (pow_add 2 (s + 2) ((s + 1) * c)).symm
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

lemma triple (K : ℕ) : ∀ S : Finset ℕ, K + 2 ≤ S.card → (∀ a ∈ S, ∀ b ∈ S, b - a < 2 ^ K) →
    ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p < q ∧ q < r ∧ q - p < r - q := by
  induction K with
  | zero =>
    intro S hS hd
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
    have h1 := hd a ha b hb
    have h2 := hd b hb a ha
    simp at h1 h2
    omega
  | succ K ih =>
    intro S hS hd
    have hne : S.Nonempty := Finset.card_pos.mp (show 0 < S.card by omega)
    set x1 := S.min' hne with hx1
    set z := S.max' hne with hz
    have hx1S : x1 ∈ S := Finset.min'_mem S hne
    set S' := S.erase x1 with hS'
    have hS'c : K + 2 ≤ S'.card := by
      rw [hS', Finset.card_erase_of_mem hx1S]; omega
    have hne' : S'.Nonempty := Finset.card_pos.mp (show 0 < S'.card by omega)
    set x2 := S'.min' hne' with hx2
    have hx2S' : x2 ∈ S' := Finset.min'_mem S' hne'
    have hx2S : x2 ∈ S := Finset.mem_of_mem_erase hx2S'
    have hx12 : x1 < x2 := by
      have hne2 : x2 ≠ x1 := Finset.ne_of_mem_erase hx2S'
      have : x1 ≤ x2 := Finset.min'_le S x2 hx2S
      omega
    obtain ⟨w, hw⟩ : (S'.erase x2).Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem hx2S']; omega)
    have hwS' : w ∈ S' := Finset.mem_of_mem_erase hw
    have hwS : w ∈ S := Finset.mem_of_mem_erase hwS'
    have hw2 : x2 < w := by
      have hne2 : w ≠ x2 := Finset.ne_of_mem_erase hw
      have : x2 ≤ w := Finset.min'_le S' w hwS'
      omega
    have hzS : z ∈ S := Finset.max'_mem S hne
    have hwz : w ≤ z := Finset.le_max' S w hwS
    by_cases h : x2 - x1 < z - x2
    · exact ⟨x1, hx1S, x2, hx2S, z, hzS, hx12, by omega, h⟩
    · have hzx := hd x1 hx1S z hzS
      rw [pow_succ] at hzx
      obtain ⟨p, hp, q, hq, r, hr, h1, h2, h3⟩ := ih S' hS'c (by
        intro a ha b hb
        have : x2 ≤ a := Finset.min'_le S' a ha
        have : b ≤ z := Finset.le_max' S b (Finset.mem_of_mem_erase hb)
        omega)
      exact ⟨p, Finset.mem_of_mem_erase hp, q, Finset.mem_of_mem_erase hq, r,
        Finset.mem_of_mem_erase hr, h1, h2, h3⟩

lemma big (m : ℕ) (hm : 10 ≤ m) : 4 * m ^ 2 + 20 * m ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have e : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [e]
    nlinarith

end OMA_E700H2

open OMA_E700H2 in
theorem OMA.solution : OMA.R_Erdos700_erdos_700_parts_ii_R1.H2 := by
  intro N
  set m := N + 10 with hm
  set Y := 2 ^ m with hY
  have hYbig : 4 * m ^ 2 + 20 * m ≤ Y := big m (by omega)
  have hY1 : m < Y := Nat.lt_two_pow_self
  have hX : 2 ^ (3 * m) = Y * Y * Y := by rw [hY, ← pow_add, ← pow_add]; ring_nf
  have hch := chebPow (3 * m - 1)
  rw [show 3 * m - 1 + 1 = 3 * m by omega, hX] at hch
  set M := Nat.count Nat.Prime (Y * Y * Y + 1) with hM
  set S := (Finset.Ioc (2 * Y * Y) (Y * Y * Y)).filter Nat.Prime with hS
  have hSc : M ≤ (2 * Y * Y + 1) + S.card := by
    rw [hM, Nat.count_eq_card_filter_range]
    calc ((Finset.range (Y * Y * Y + 1)).filter Nat.Prime).card
        ≤ (Finset.range (2 * Y * Y + 1) ∪ S).card := by
          apply Finset.card_le_card
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_range] at hp
          simp only [Finset.mem_union, Finset.mem_range, hS, Finset.mem_filter, Finset.mem_Ioc]
          by_cases h : p ≤ 2 * Y * Y
          · left; omega
          · right; exact ⟨⟨by omega, by omega⟩, hp.2⟩
      _ ≤ _ := by
          refine (Finset.card_union_le _ _).trans ?_
          rw [Finset.card_range]
  -- counting inequality
  have hcount : (Finset.range (Y * Y + 1)).card * (m + 1) < S.card := by
    rw [Finset.card_range]
    have h3m : 3 * m - 1 + 2 = 3 * m + 1 := by omega
    rw [h3m] at hch
    have hY2 : Y * Y * (4 * m ^ 2 + 20 * m) ≤ Y * Y * Y := Nat.mul_le_mul_left _ hYbig
    have hpos : 0 < m := by omega
    have key : 3 * m * ((Y * Y + 1) * (m + 1) + 2 * Y * Y + 1) < 3 * m * M := by nlinarith
    have key2 : (Y * Y + 1) * (m + 1) + 2 * Y * Y + 1 < M := Nat.lt_of_mul_lt_mul_left key
    omega
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := S) (t := Finset.range (Y * Y + 1)) (f := fun p => p / Y) (n := m + 1)
    (by
      intro p hp
      simp only [hS, Finset.mem_filter, Finset.mem_Ioc] at hp
      simp only [Finset.mem_range]
      have : p / Y ≤ Y * Y := Nat.div_le_of_le_mul (by nlinarith)
      omega) hcount
  set F := S.filter (fun p => p / Y = i) with hF
  obtain ⟨p, hp, q, hq, r, hr, h1, h2, h3⟩ := triple m F (by omega) (by
    intro a ha b hb
    simp only [hF, Finset.mem_filter] at ha hb
    have hYpos : 0 < Y := by positivity
    have ea := Nat.div_add_mod a Y
    have eb := Nat.div_add_mod b Y
    have ma := Nat.mod_lt a hYpos
    have mb := Nat.mod_lt b hYpos
    rw [ha.2] at ea
    rw [hb.2] at eb
    rw [← hY]
    omega)
  simp only [hF, hS, Finset.mem_filter, Finset.mem_Ioc] at hp hq hr
  have hYpos : 0 < Y := by positivity
  have hrp : r - p < Y := by
    have ea := Nat.div_add_mod p Y
    have eb := Nat.div_add_mod r Y
    have ma := Nat.mod_lt p hYpos
    have mb := Nat.mod_lt r hYpos
    rw [hp.2] at ea
    rw [hr.2] at eb
    omega
  have hsq : (r - p) ^ 2 < Y * Y := by rw [sq]; exact Nat.mul_self_lt_mul_self hrp
  have e2 : 2 * Y * Y = 2 * (Y * Y) := by ring
  refine ⟨p, q, r, ?_, hp.1.2, hq.1.2, hr.1.2, h1, h2, h3, ?_⟩
  · have : Y ≤ 2 * Y * Y := by nlinarith
    omega
  · omega
