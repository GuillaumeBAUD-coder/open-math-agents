import OMAStatements.S_oeis_a183003
import Mathlib

namespace A183003Aux

open OMA.S_oeis_a183003

lemma flip_lt (N d : ℕ) (hN : 0 < N) (hd : d ∣ N) (h : d * d < N) :
    N < (N / d) * (N / d) := by
  obtain ⟨e, rfl⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_mul_pos_right hN
  rw [Nat.mul_div_cancel_left e hd0]
  have hlt : d < e := Nat.lt_of_mul_lt_mul_left h
  nlinarith

lemma flip_gt (N d : ℕ) (hN : 0 < N) (hd : d ∣ N) (h : N < d * d) :
    (N / d) * (N / d) < N := by
  obtain ⟨e, rfl⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_mul_pos_right hN
  rw [Nat.mul_div_cancel_left e hd0]
  have hlt : e < d := Nat.lt_of_mul_lt_mul_left h
  nlinarith

lemma card_lt_eq_card_gt (N : ℕ) (hN : 0 < N) :
    (N.divisors.filter (fun d => d * d < N)).card
      = (N.divisors.filter (fun d => N < d * d)).card := by
  apply Finset.card_nbij' (fun d => N / d) (fun d => N / d)
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd ⊢
    exact ⟨⟨Nat.div_dvd_of_dvd hd.1.1, hd.1.2⟩, flip_lt N d hN hd.1.1 hd.2⟩
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd ⊢
    exact ⟨⟨Nat.div_dvd_of_dvd hd.1.1, hd.1.2⟩, flip_gt N d hN hd.1.1 hd.2⟩
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd
    exact Nat.div_div_self hd.1.1 hd.1.2
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd
    exact Nat.div_div_self hd.1.1 hd.1.2

lemma card_eq_le_one (N : ℕ) :
    (N.divisors.filter (fun d => d * d = N)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  exact Nat.mul_self_inj.mp (ha.2.trans hb.2.symm)

lemma card_split (N : ℕ) (hN : 0 < N) :
    N.divisors.card + N.divisors.card % 2
      = 2 * (N.divisors.filter (fun d => d * d ≤ N)).card := by
  have h1 : N.divisors.card = (N.divisors.filter (fun d => d * d < N)).card
      + (N.divisors.filter (fun d => d * d = N)).card
      + (N.divisors.filter (fun d => N < d * d)).card := by
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> omega
  have h2 : (N.divisors.filter (fun d => d * d ≤ N)).card
      = (N.divisors.filter (fun d => d * d < N)).card
      + (N.divisors.filter (fun d => d * d = N)).card := by
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> omega
  have h3 := card_lt_eq_card_gt N hN
  have h4 := card_eq_le_one N
  omega

lemma card_small (m : ℕ) :
    ((m + 1).divisors.filter (fun d => d * d ≤ m + 1)).card = A072670 m + 1 := by
  have h1mem : 1 ∈ (m + 1).divisors.filter (fun d => d * d ≤ m + 1) := by
    simp only [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd _, by omega⟩, by omega⟩
  rw [← Finset.card_erase_add_one h1mem]
  congr 1
  symm
  unfold A072670
  apply Finset.card_bij (fun p _ => p.1 + 1)
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hi1, hi2⟩, hj1, hj2⟩, hij, heq⟩ := hp
    have hprod : (i + 1) * (j + 1) = m + 1 := by rw [← heq]; ring
    simp only [Finset.mem_erase, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨by omega, ⟨Dvd.intro _ hprod, by omega⟩, ?_⟩
    calc (i + 1) * (i + 1) ≤ (i + 1) * (j + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = m + 1 := hprod
  · rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp hp'
    obtain ⟨_, _, heq⟩ := hp
    obtain ⟨_, _, heq'⟩ := hp'
    have hi : i = i' := by simpa using h
    subst hi
    have hprod : (i + 1) * (j + 1) = (i + 1) * (j' + 1) := by
      have e1 : (i + 1) * (j + 1) = i * j + i + j + 1 := by ring
      have e2 : (i + 1) * (j' + 1) = i * j' + i + j' + 1 := by ring
      rw [e1, e2, heq, heq']
    have hj : j + 1 = j' + 1 := Nat.eq_of_mul_eq_mul_left (by omega) hprod
    have hj' : j = j' := by omega
    rw [hj']
  · intro d hd
    simp only [Finset.mem_erase, Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨hd1, ⟨⟨e, he⟩, _⟩, hsq⟩ := hd
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · rw [h, zero_mul] at he
        omega
      · exact h
    have hde : d ≤ e := by
      rw [he] at hsq
      exact Nat.le_of_mul_le_mul_left hsq hd0
    obtain ⟨i, rfl⟩ : ∃ i, d = i + 1 := ⟨d - 1, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j, e = j + 1 := ⟨e - 1, by omega⟩
    have hm : m = i * j + i + j := by
      have e1 : (i + 1) * (j + 1) = i * j + i + j + 1 := by ring
      omega
    have hi1 : 1 ≤ i := by omega
    have hij : i ≤ j := by omega
    have h1 : i ≤ i * j := Nat.le_mul_of_pos_right i (by omega)
    have h2 : j ≤ i * j := Nat.le_mul_of_pos_left j (by omega)
    refine ⟨(i, j), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨hi1, by omega⟩, by omega, by omega⟩, hij, hm.symm⟩

lemma key (m : ℕ) : A161840 (m + 1) = 2 * A072670 m := by
  unfold A161840
  have h1 := card_split (m + 1) (by omega)
  have h2 := card_small m
  omega

lemma sum_eq (n : ℕ) : A183002 n = 2 * ∑ m ∈ Finset.range n, A072670 m := by
  induction n with
  | zero => simp [A183002]
  | succ n ih =>
    unfold A183002 at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih, key n]
    ring

end A183003Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a183003.main := by
  intro n _
  unfold OMA.S_oeis_a183003.a
  rw [A183003Aux.sum_eq n]
  exact Nat.mul_div_cancel_left _ (by norm_num)
