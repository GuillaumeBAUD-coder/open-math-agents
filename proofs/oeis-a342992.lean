import OMAStatements.S_oeis_a342992
import Mathlib

namespace OMA.A342992Proof

open OMA.S_oeis_a342992

theorem lemX (b : ℕ) : ∃ L : List ℕ, L.length = b ∧ (∀ d ∈ L, d = 2 ∨ d = 3) ∧
    2 ^ b ∣ Nat.ofDigits 10 L := by
  induction b with
  | zero => exact ⟨[], rfl, by simp, by simp⟩
  | succ b ih =>
    obtain ⟨L, hlen, hd, q, hq⟩ := ih
    have h5 : Odd (5 ^ b) := Odd.pow (by decide)
    obtain ⟨r, hr⟩ := h5
    rcases Nat.even_or_odd q with ⟨s, hs⟩ | ⟨s, hs⟩
    · refine ⟨L ++ [2], by simp [hlen], ?_, ?_⟩
      · intro d hdm
        rcases List.mem_append.1 hdm with h | h
        · exact hd d h
        · simp at h; omega
      · rw [Nat.ofDigits_append, hq, hlen]
        refine ⟨s + 2 * r + 1, ?_⟩
        have : (10:ℕ) ^ b = 2 ^ b * 5 ^ b := by rw [← mul_pow]; norm_num
        rw [this, hr, hs]
        simp [Nat.ofDigits]
        ring
    · refine ⟨L ++ [3], by simp [hlen], ?_, ?_⟩
      · intro d hdm
        rcases List.mem_append.1 hdm with h | h
        · exact hd d h
        · simp at h; omega
      · rw [Nat.ofDigits_append, hq, hlen]
        refine ⟨s + 3 * r + 2, ?_⟩
        have : (10:ℕ) ^ b = 2 ^ b * 5 ^ b := by rw [← mul_pow]; norm_num
        rw [this, hr, hs]
        simp [Nat.ofDigits]
        ring

theorem rep_mem (L : List ℕ) (P : ℕ → Prop) (h : ∀ d ∈ L, P d) (c : ℕ) :
    ∀ d ∈ (List.replicate c L).flatten, P d := by
  intro d hd
  rw [List.mem_flatten] at hd
  obtain ⟨l, hl, hdl⟩ := hd
  rw [List.eq_of_mem_replicate hl] at hdl
  exact h d hdl

theorem rep_ne_nil (L : List ℕ) (h : L ≠ []) (c : ℕ) (hc : c ≠ 0) :
    (List.replicate c L).flatten ≠ [] := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc
  rw [List.replicate_succ, List.flatten_cons]
  simp [h]

theorem rep_dvd (L : List ℕ) (t : ℕ) (h : t ∣ Nat.ofDigits 10 L) (c : ℕ) :
    t ∣ Nat.ofDigits 10 (List.replicate c L).flatten := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append]
    exact dvd_add h (dvd_mul_of_dvd_right ih _)

theorem rep_mod (L : List ℕ) (m : ℕ) (h : 10 ^ L.length ≡ 1 [MOD m]) (c : ℕ) :
    Nat.ofDigits 10 (List.replicate c L).flatten ≡ c * Nat.ofDigits 10 L [MOD m] := by
  induction c with
  | zero => simp; rfl
  | succ c ih =>
    rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append]
    have := Nat.ModEq.add_left (Nat.ofDigits 10 L) (Nat.ModEq.mul h ih)
    rw [show (c + 1) * Nat.ofDigits 10 L = Nat.ofDigits 10 L + 1 * (c * Nat.ofDigits 10 L) by ring]
    exact this

end OMA.A342992Proof

open OMA.A342992Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a342992.main := by
  intro n hn h5
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := n) (by omega)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hn
  have h5m : ¬ 5 ∣ m := fun h => h5 (dvd_mul_of_dvd_right h _)
  have c2 : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by
    rw [Nat.two_dvd_ne_zero]; exact Nat.odd_iff.1 hm)
  have c5 : Nat.Coprime 5 m := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5m
  have c10 : Nat.Coprime 10 m := by
    have := Nat.Coprime.mul_left c2 c5
    simpa using this
  obtain ⟨L, hlen, hd, hdiv⟩ := lemX (a + 1)
  have hL : L ≠ [] := by rintro rfl; simp at hlen
  have hdivA : 2 ^ a ∣ Nat.ofDigits 10 L :=
    dvd_trans (pow_dvd_pow 2 (Nat.le_succ a)) hdiv
  set L' := (List.replicate (Nat.totient m) L).flatten with hL'
  have htot : Nat.totient m ≠ 0 := (Nat.totient_pos.2 (Nat.pos_of_ne_zero hm0)).ne'
  have hd' : ∀ d ∈ L', d = 2 ∨ d = 3 := rep_mem L _ hd _
  have hL'ne : L' ≠ [] := rep_ne_nil L hL _ htot
  have hdiv' : 2 ^ a ∣ Nat.ofDigits 10 L' := rep_dvd L _ hdivA _
  have hlen' : 10 ^ L'.length ≡ 1 [MOD m] := by
    have hl : L'.length = L.length * Nat.totient m := by
      rw [hL', List.length_flatten]
      simp [mul_comm]
    rw [hl, pow_mul]
    exact Nat.ModEq.pow_totient (Nat.Coprime.pow_left _ c10)
  set R := (List.replicate m L').flatten with hR
  have hdR : ∀ d ∈ R, d = 2 ∨ d = 3 := rep_mem L' _ hd' _
  have hRne : R ≠ [] := rep_ne_nil L' hL'ne _ hm0
  have hdivR : 2 ^ a ∣ Nat.ofDigits 10 R := rep_dvd L' _ hdiv' _
  have hmodR := rep_mod L' m hlen' m
  have hmR : m ∣ Nat.ofDigits 10 R := by
    apply (Nat.modEq_zero_iff_dvd).1
    refine hmodR.trans ?_
    exact (Nat.modEq_zero_iff_dvd).2 (dvd_mul_right _ _)
  have hnR : 2 ^ a * m ∣ Nat.ofDigits 10 R :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow_left _ c2) hdivR hmR
  have hdig : Nat.digits 10 (Nat.ofDigits 10 R) = R := by
    apply Nat.digits_ofDigits 10 (by norm_num)
    · intro l hl
      rcases hdR l hl with h | h <;> omega
    · intro h
      rcases hdR _ (List.getLast_mem h) with h' | h' <;> omega
  obtain ⟨k, hk⟩ := hnR
  have hY : Nat.ofDigits 10 R ≠ 0 := by
    intro h0
    rw [h0] at hdig
    simp at hdig
    exact hRne hdig
  refine ⟨k, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk; exact absurd hk hY
    · exact h
  · intro d hdm
    rw [mul_comm, ← hk, hdig] at hdm
    rcases hdR d hdm with h | h <;> simp [h]
