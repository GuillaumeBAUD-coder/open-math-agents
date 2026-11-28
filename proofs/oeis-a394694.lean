import OMAStatements.S_oeis_a394694

namespace A394694
open OMA.S_oeis_a394694

lemma T_iff (i j N : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) : T i j = N + 1 ↔ (i - 1) * j = N := by
  unfold T
  obtain ⟨d, rfl⟩ : ∃ d, i = d + 1 := ⟨i - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, j = c + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Nat.mul_succ]; omega

lemma a_eq (N : ℕ) (hN : 1 ≤ N) :
    a (N + 1) = ((Nat.divisors N).filter fun j => j ≤ N / j + 1).card := by
  unfold a
  apply Finset.card_bij (fun p _ => p.2)
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hi1, hi2⟩, hj1, hj2⟩, hji, hT⟩ := hp
    rw [T_iff i j N hi1 hj1] at hT
    have hq : N / j = i - 1 := Nat.div_eq_of_eq_mul_left (by omega) hT.symm
    simp only [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨Dvd.intro_left _ hT, by omega⟩, by omega⟩
  · rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' hjj
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp hp'
    obtain ⟨⟨⟨hi1, hi2⟩, hj1, hj2⟩, hji, hT⟩ := hp
    obtain ⟨⟨⟨hi1', hi2'⟩, hj1', hj2'⟩, hji', hT'⟩ := hp'
    simp only at hjj
    subst hjj
    rw [T_iff i j N hi1 hj1] at hT
    rw [T_iff i' j N hi1' hj1] at hT'
    have : i - 1 = i' - 1 := Nat.eq_of_mul_eq_mul_right (by omega : 0 < j) (hT.trans hT'.symm)
    have : i = i' := by omega
    rw [this]
  · intro j hj
    simp only [Finset.mem_filter, Nat.mem_divisors] at hj
    obtain ⟨⟨hd, hN0⟩, hle⟩ := hj
    have hjpos : 0 < j := Nat.pos_of_dvd_of_pos hd (by omega)
    have hjle : j ≤ N := Nat.le_of_dvd (by omega) hd
    have hql : N / j ≤ N := Nat.div_le_self _ _
    refine ⟨(N / j + 1, j), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, hle, ?_⟩
    rw [T_iff _ _ N (by omega) (by omega), Nat.add_sub_cancel, Nat.div_mul_cancel hd]

lemma cardAC (N : ℕ) (hN : 1 ≤ N) :
    ((Nat.divisors N).filter fun j => j < N / j).card =
      ((Nat.divisors N).filter fun j => N / j < j).card := by
  apply Finset.card_bij (fun j _ => N / j)
  · intro j hj
    simp only [Finset.mem_filter, Nat.mem_divisors] at hj ⊢
    obtain ⟨⟨hd, hN0⟩, hlt⟩ := hj
    refine ⟨⟨Nat.div_dvd_of_dvd hd, hN0⟩, ?_⟩
    rw [Nat.div_div_self hd hN0]; exact hlt
  · intro j hj j' hj' h
    simp only [Finset.mem_filter, Nat.mem_divisors] at hj hj'
    have e1 := Nat.div_div_self hj.1.1 hj.1.2
    have e2 := Nat.div_div_self hj'.1.1 hj'.1.2
    rw [show N / j = N / j' from h] at e1
    omega
  · intro c hc
    simp only [Finset.mem_filter, Nat.mem_divisors] at hc
    obtain ⟨⟨hd, hN0⟩, hlt⟩ := hc
    refine ⟨N / c, ?_, Nat.div_div_self hd hN0⟩
    simp only [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨Nat.div_dvd_of_dvd hd, hN0⟩, ?_⟩
    rw [Nat.div_div_self hd hN0]; exact hlt

lemma cardB (N : ℕ) (hN : 1 ≤ N) :
    ((Nat.divisors N).filter fun j => j = N / j).card = if IsSquare N then 1 else 0 := by
  split_ifs with h
  · obtain ⟨r, rfl⟩ := h
    have hr : 0 < r := by rcases Nat.eq_zero_or_pos r with h | h; · subst h; omega
                          · exact h
    rw [Finset.card_eq_one]
    refine ⟨r, ?_⟩
    ext j
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hd, _⟩, hj⟩
      have := Nat.div_mul_cancel hd
      rw [← hj] at this
      exact Nat.mul_self_inj.1 this
    · rintro rfl
      exact ⟨⟨Dvd.intro _ rfl, by omega⟩, (Nat.mul_div_cancel _ hr).symm⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro j hj hjq
    have hd := (Nat.mem_divisors.1 hj).1
    have := Nat.div_mul_cancel hd
    rw [← hjq] at this
    exact h ⟨j, this.symm⟩

open Classical in
lemma cardP (N : ℕ) (hN : 1 ≤ N) :
    ((Nat.divisors N).filter fun j => j = N / j + 1).card = if IsPronic N then 1 else 0 := by
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rw [Finset.card_eq_one]
    refine ⟨k + 1, ?_⟩
    ext j
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hd, _⟩, hj⟩
      have h1 := Nat.div_mul_cancel hd
      generalize k * (k + 1) / j = q at hj h1
      subst hj
      have : q = k := by
        rcases Nat.lt_trichotomy q k with h | h | h
        · nlinarith
        · exact h
        · nlinarith
      omega
    · rintro rfl
      exact ⟨⟨Dvd.intro_left _ rfl, by omega⟩, by rw [Nat.mul_div_cancel _ (Nat.succ_pos k)]⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro j hj hjq
    have hd := (Nat.mem_divisors.1 hj).1
    have h1 := Nat.div_mul_cancel hd
    refine h ⟨N / j, ?_⟩
    generalize N / j = q at hjq h1 ⊢
    subst hjq
    exact h1.symm

lemma not_both (N : ℕ) (hN : 1 ≤ N) (h1 : IsSquare N) (h2 : IsPronic N) : False := by
  obtain ⟨r, hr⟩ := h1
  obtain ⟨k, hk⟩ := h2
  rw [hk] at hr
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · simp at hk; omega
    · omega
  rcases Nat.lt_or_ge k r with h | h
  · nlinarith
  · have h3 := Nat.mul_le_mul h h
    nlinarith

end A394694

open A394694 OMA.S_oeis_a394694 in
theorem OMA.solution : type_of% @OMA.S_oeis_a394694.main := by
  intro n hn
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hN : 1 ≤ N := by omega
  rw [Nat.add_sub_cancel, a_eq N hN]
  have hAC := cardAC N hN
  have hB := cardB N hN
  have hP := cardP N hN
  have s1 : ((Nat.divisors N).filter fun j => j ≤ N / j + 1).card =
      ((Nat.divisors N).filter fun j => j < N / j).card +
      ((Nat.divisors N).filter fun j => j = N / j).card +
      ((Nat.divisors N).filter fun j => j = N / j + 1).card := by
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> omega
  have s2 : (Nat.divisors N).card =
      ((Nat.divisors N).filter fun j => j < N / j).card +
      ((Nat.divisors N).filter fun j => j = N / j).card +
      ((Nat.divisors N).filter fun j => N / j < j).card := by
    simp only [Finset.card_filter]
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> omega
  rw [s1, s2, ← hAC, hB, hP]
  unfold e
  rw [Nat.add_sub_cancel]
  by_cases hs : IsSquare N
  · have hp : ¬ IsPronic N := fun hp => not_both N hN hs hp
    simp only [hs, hp, if_true, if_false]
    push_cast; ring
  · by_cases hp : IsPronic N
    · simp only [hs, hp, if_true, if_false]
      push_cast; ring
    · simp only [hs, hp, if_true, if_false]
      push_cast; ring
