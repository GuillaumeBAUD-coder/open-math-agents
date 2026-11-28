import OMAReductions.R_Erdos162_erdos_162_R1

namespace OMA.Erdos162H1Aux

open Erdos162

def Mono {n : ℕ} (c : Sym2 (Fin n) → Bool) (b : Bool) (H : Finset (Fin n)) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, x ≠ y → c s(x, y) = b

lemma ramsey {n : ℕ} (c : Sym2 (Fin n) → Bool) : ∀ k : ℕ, ∀ V : Finset (Fin n), 2 ^ k ≤ V.card →
    ∀ s t : ℕ, s + t ≤ k →
      (∃ H ⊆ V, s ≤ H.card ∧ Mono c true H) ∨ (∃ H ⊆ V, t ≤ H.card ∧ Mono c false H) := by
  intro k
  induction k with
  | zero =>
    intro V _ s t hst
    left
    refine ⟨∅, Finset.empty_subset _, by omega, ?_⟩
    intro x hx
    simp at hx
  | succ k ih =>
    intro V hV s t hst
    rcases Nat.eq_zero_or_pos s with hs | hs
    · left
      refine ⟨∅, Finset.empty_subset _, by omega, ?_⟩
      intro x hx
      simp at hx
    rcases Nat.eq_zero_or_pos t with ht | ht
    · right
      refine ⟨∅, Finset.empty_subset _, by omega, ?_⟩
      intro x hx
      simp at hx
    have hVpos : 0 < V.card := lt_of_lt_of_le (by positivity) hV
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hVpos
    set W := V.erase v with hW
    set R := W.filter (fun w => c s(v, w) = true) with hR
    set B := W.filter (fun w => ¬ c s(v, w) = true) with hB
    have hRB : R.card + B.card = W.card := Finset.card_filter_add_card_filter_not _
    have hWc : W.card + 1 = V.card := Finset.card_erase_add_one hv
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    have hRB2 : 2 ^ k ≤ R.card ∨ 2 ^ k ≤ B.card := by omega
    rcases hRB2 with hRk | hBk
    · rcases ih R hRk (s - 1) t (by omega) with ⟨H, hHR, hHc, hHm⟩ | ⟨H, hHR, hHc, hHm⟩
      · left
        have hvH : v ∉ H := by
          intro h
          have := hHR h
          simp [hR, hW] at this
        refine ⟨insert v H, ?_, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hv
          · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_filter _ (hHR hx))
        · rw [Finset.card_insert_of_notMem hvH]; omega
        · intro x hx y hy hxy
          rcases Finset.mem_insert.mp hx with rfl | hx' <;>
            rcases Finset.mem_insert.mp hy with rfl | hy'
          · exact absurd rfl hxy
          · exact (Finset.mem_filter.mp (hHR hy')).2
          · rw [Sym2.eq_swap]; exact (Finset.mem_filter.mp (hHR hx')).2
          · exact hHm x hx' y hy' hxy
      · right
        refine ⟨H, fun x hx => Finset.mem_of_mem_erase (Finset.mem_of_mem_filter _ (hHR hx)),
          hHc, hHm⟩
    · rcases ih B hBk s (t - 1) (by omega) with ⟨H, hHR, hHc, hHm⟩ | ⟨H, hHR, hHc, hHm⟩
      · left
        refine ⟨H, fun x hx => Finset.mem_of_mem_erase (Finset.mem_of_mem_filter _ (hHR hx)),
          hHc, hHm⟩
      · right
        have hvH : v ∉ H := by
          intro h
          have := hHR h
          simp [hB, hW] at this
        refine ⟨insert v H, ?_, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hv
          · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_filter _ (hHR hx))
        · rw [Finset.card_insert_of_notMem hvH]; omega
        · intro x hx y hy hxy
          rcases Finset.mem_insert.mp hx with rfl | hx' <;>
            rcases Finset.mem_insert.mp hy with rfl | hy'
          · exact absurd rfl hxy
          · simpa using (Finset.mem_filter.mp (hHR hy')).2
          · rw [Sym2.eq_swap]; simpa using (Finset.mem_filter.mp (hHR hx')).2
          · exact hHm x hx' y hy' hxy

lemma count_zero {n : ℕ} (c : Sym2 (Fin n) → Bool) (b : Bool) (H : Finset (Fin n))
    (hH : Mono c b H) : colourEdgeCount c H (!b) = 0 := by
  unfold colourEdgeCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    rw [Finset.mk_mem_sym2_iff] at he
    rintro ⟨hd, hc⟩
    rw [Sym2.mk_isDiag_iff] at hd
    rw [hH x he.1 y he.2 hd] at hc
    cases b <;> simp at hc

lemma F_gt {n : ℕ} (α : ℝ) (h0 : 0 ≤ α) (m : ℕ) (hm : 2 ^ (m + m) ≤ n) : m < F n α := by
  have hne : {k : ℕ | ∃ c : Sym2 (Fin n) → Bool, IsBalancedAbove n α c k}.Nonempty :=
    ⟨n + 1, fun _ => true, isBalancedAbove_succ n α _⟩
  obtain ⟨c, hc⟩ := Nat.sInf_mem hne
  have hV : 2 ^ (m + m) ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hm
  have key : ∀ b : Bool, ∀ H : Finset (Fin n), m ≤ H.card → Mono c b H → m < F n α := by
    intro b H hHc hHm
    by_contra hlt
    push Not at hlt
    have h := hc H (le_trans hlt hHc) (!b)
    rw [count_zero c b H hHm] at h
    have : 0 ≤ α * (H.card.choose 2 : ℝ) := mul_nonneg h0 (Nat.cast_nonneg _)
    push_cast at h
    linarith
  rcases ramsey c (m + m) Finset.univ hV m m le_rfl with ⟨H, _, hHc, hHm⟩ | ⟨H, _, hHc, hHm⟩
  · exact key true H hHc hHm
  · exact key false H hHc hHm

end OMA.Erdos162H1Aux

theorem OMA.solution : OMA.R_Erdos162_erdos_162_R1.H1 := by
  intro α h0 _
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨1 / Real.log 4, by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  set m := Nat.log 4 n with hm
  have h4m : 4 ^ m ≤ n := Nat.pow_log_le_self 4 (by omega)
  have h2m : 2 ^ (m + m) ≤ n := by
    have : 2 ^ (m + m) = 4 ^ m := by rw [← two_mul, pow_mul]; norm_num
    omega
  have hF := OMA.Erdos162H1Aux.F_gt α h0 m h2m
  have hlt : n < 4 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : Real.log n < (m + 1 : ℝ) * Real.log 4 := by
    have e : Real.log ((4 : ℝ) ^ (m + 1)) = (m + 1 : ℝ) * Real.log 4 := by
      rw [Real.log_pow]; push_cast; ring
    rw [← e]
    apply Real.log_lt_log hnpos
    exact_mod_cast hlt
  have hF' : ((m : ℝ) + 1) ≤ (Erdos162.F n α : ℝ) := by exact_mod_cast hF
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hl4]
  nlinarith
