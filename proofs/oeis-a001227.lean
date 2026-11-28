import OMAStatements.S_oeis_a001227
import Mathlib

namespace A001227Proof

def Qc (s N k : ℕ) : ℕ :=
  ((Nat.divisors k).filter (fun d => N ≤ 2 * (s * d ^ 2) ∧ s * d ^ 2 < 2 * N)).card

def H (m s N : ℕ) : ℕ := ((Nat.divisors m).filter (fun e => s * e ^ 2 < 2 * N)).card

lemma Qc_def (s N k : ℕ) : Qc s N k =
    ((Nat.divisors k).filter (fun d => N ≤ 2 * (s * d ^ 2) ∧ s * d ^ 2 < 2 * N)).card := rfl

lemma H_def (m s N : ℕ) :
    H m s N = ((Nat.divisors m).filter (fun e => s * e ^ 2 < 2 * N)).card := rfl

lemma base (m s N : ℕ) : Qc s N m + H m (4 * s) N = H m s N := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Nat.divisors m).filter (fun e => s * e ^ 2 < 2 * N)) (fun e => 4 * s * e ^ 2 < 2 * N)
  rw [Finset.filter_filter, Finset.filter_filter] at h
  have h1 : (Nat.divisors m).filter (fun e => s * e ^ 2 < 2 * N ∧ 4 * s * e ^ 2 < 2 * N)
      = (Nat.divisors m).filter (fun e => 4 * s * e ^ 2 < 2 * N) := by
    apply Finset.filter_congr
    intro e _
    have e4 : 4 * s * e ^ 2 = 4 * (s * e ^ 2) := by ring
    rw [e4]
    omega
  have h2 : (Nat.divisors m).filter (fun e => s * e ^ 2 < 2 * N ∧ ¬ 4 * s * e ^ 2 < 2 * N)
      = (Nat.divisors m).filter (fun d => N ≤ 2 * (s * d ^ 2) ∧ s * d ^ 2 < 2 * N) := by
    apply Finset.filter_congr
    intro e _
    have e4 : 4 * s * e ^ 2 = 4 * (s * e ^ 2) := by ring
    rw [e4]
    omega
  rw [h1, h2] at h
  rw [Qc_def, H_def, H_def]
  omega

lemma split (k : ℕ) (hk : k ≠ 0) (P : ℕ → Prop) [DecidablePred P] :
    ((Nat.divisors (2 * k)).filter P).card
      = ((Nat.divisors (2 * k)).filter (fun d => Odd d ∧ P d)).card
        + ((Nat.divisors k).filter (fun d => P (2 * d))).card := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Nat.divisors (2 * k)).filter P) (fun d => Odd d)
  rw [Finset.filter_filter, Finset.filter_filter] at h
  have h1 : (Nat.divisors (2 * k)).filter (fun d => P d ∧ Odd d)
      = (Nat.divisors (2 * k)).filter (fun d => Odd d ∧ P d) := by
    apply Finset.filter_congr
    intro d _
    exact and_comm
  have h2 : ((Nat.divisors k).filter (fun d => P (2 * d))).card
      = ((Nat.divisors (2 * k)).filter (fun d => P d ∧ ¬ Odd d)).card := by
    apply Finset.card_bij (fun d _ => 2 * d)
    · intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      refine ⟨⟨Nat.mul_dvd_mul_left 2 hd.1.1, by omega⟩, hd.2, ?_⟩
      rw [Nat.not_odd_iff_even]
      exact even_two_mul d
    · intro a _ b _ hab
      have hab' : 2 * a = 2 * b := hab
      omega
    · intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hdvd, _⟩, hP, hodd⟩ := hd
      have heven : Even d := Nat.not_odd_iff_even.mp hodd
      obtain ⟨d', rfl⟩ := heven.two_dvd
      refine ⟨d', ?_, rfl⟩
      rw [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨(Nat.mul_dvd_mul_iff_left (by norm_num)).mp hdvd, hk⟩, hP⟩
  rw [h1] at h
  omega

lemma odd_div (a m d : ℕ) (hd : Odd d) : d ∣ 2 ^ a * m ↔ d ∣ m := by
  constructor
  · intro h
    have hc : Nat.Coprime d (2 ^ a) := Nat.Coprime.pow_right a hd.coprime_two_right
    exact hc.dvd_of_dvd_mul_left h
  · intro h
    exact Dvd.dvd.mul_left h _

lemma odd_filter (a m : ℕ) (hm : Odd m) (P : ℕ → Prop) [DecidablePred P] :
    (Nat.divisors (2 ^ a * m)).filter (fun d => Odd d ∧ P d) = (Nat.divisors m).filter P := by
  have hm0 : 0 < m := hm.pos
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdvd, _⟩, hod, hc⟩
    exact ⟨⟨(odd_div a m d hod).mp hdvd, hm0.ne'⟩, hc⟩
  · rintro ⟨⟨hdvd, _⟩, hc⟩
    have hod : Odd d := hm.of_dvd_nat hdvd
    exact ⟨⟨(odd_div a m d hod).mpr hdvd, by positivity⟩, hod, hc⟩

lemma main_ind (m : ℕ) (hm : Odd m) :
    ∀ a s N : ℕ, Qc s N (2 ^ a * m) + H m (s * 4 ^ (a + 1)) N = H m s N := by
  have hm0 : 0 < m := hm.pos
  intro a
  induction a with
  | zero =>
    intro s N
    rw [pow_zero, one_mul, zero_add, pow_one, mul_comm s 4]
    exact base m s N
  | succ a ih =>
    intro s N
    have hk : 2 ^ a * m ≠ 0 := by positivity
    have e : 2 ^ (a + 1) * m = 2 * (2 ^ a * m) := by ring
    have hs : ((Nat.divisors (2 * (2 ^ a * m))).filter
          (fun d => N ≤ 2 * (s * d ^ 2) ∧ s * d ^ 2 < 2 * N)).card
        = ((Nat.divisors (2 * (2 ^ a * m))).filter
            (fun d => Odd d ∧ (N ≤ 2 * (s * d ^ 2) ∧ s * d ^ 2 < 2 * N))).card
          + ((Nat.divisors (2 ^ a * m)).filter
            (fun d => N ≤ 2 * (s * (2 * d) ^ 2) ∧ s * (2 * d) ^ 2 < 2 * N)).card :=
      split (2 ^ a * m) hk _
    have hodd : ((Nat.divisors (2 * (2 ^ a * m))).filter
          (fun d => Odd d ∧ (N ≤ 2 * (s * d ^ 2) ∧ s * d ^ 2 < 2 * N))).card = Qc s N m := by
      rw [Qc_def, ← e, odd_filter (a + 1) m hm]
    have heven : ((Nat.divisors (2 ^ a * m)).filter
          (fun d => N ≤ 2 * (s * (2 * d) ^ 2) ∧ s * (2 * d) ^ 2 < 2 * N)).card
        = Qc (4 * s) N (2 ^ a * m) := by
      rw [Qc_def]
      congr 1
      apply Finset.filter_congr
      intro d _
      have e4 : s * (2 * d) ^ 2 = 4 * s * d ^ 2 := by ring
      rw [e4]
    have hQ : Qc s N (2 ^ (a + 1) * m) = Qc s N m + Qc (4 * s) N (2 ^ a * m) := by
      rw [Qc_def s N (2 ^ (a + 1) * m), e, hs, hodd, heven]
    have h1 := base m s N
    have h2 := ih (4 * s) N
    have e2 : s * 4 ^ (a + 1 + 1) = 4 * s * 4 ^ (a + 1) := by ring
    rw [hQ, e2]
    omega

lemma inv_count (a m : ℕ) (hm : 0 < m) :
    ((Nat.divisors m).filter (fun e => 2 * (2 ^ a * m) < e ^ 2)).card
      = H m (1 * 4 ^ (a + 1)) (2 ^ a * m) := by
  rw [H_def, Finset.card_filter, Finset.card_filter, ← Nat.sum_div_divisors]
  apply Finset.sum_congr rfl
  intro e he
  rw [Nat.mem_divisors] at he
  obtain ⟨c, hc⟩ := he.1
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, zero_mul] at hc; omega
    · exact h
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, mul_zero] at hc; omega
    · exact h
  have hdiv : m / e = c := by rw [hc]; exact Nat.mul_div_cancel_left c he0
  have h4 : (4 : ℕ) ^ (a + 1) = 2 ^ (a + 1) * 2 ^ (a + 1) := by
    rw [← mul_pow]; norm_num
  have hu0 : 0 < 2 ^ (a + 1) * e := by positivity
  have l1 : 2 * (2 ^ a * m) = 2 ^ (a + 1) * e * c := by rw [hc]; ring
  have l2 : 1 * 4 ^ (a + 1) * e ^ 2 = 2 ^ (a + 1) * e * (2 ^ (a + 1) * e) := by rw [h4]; ring
  have l3 : c ^ 2 = c * c := by ring
  have iff1 : (2 * (2 ^ a * m) < (m / e) ^ 2) ↔ (1 * 4 ^ (a + 1) * e ^ 2 < 2 * (2 ^ a * m)) := by
    rw [hdiv, l2, l3, l1, Nat.mul_lt_mul_right hc0, Nat.mul_lt_mul_left hu0]
  by_cases hP : 2 * (2 ^ a * m) < (m / e) ^ 2
  · rw [if_pos hP, if_pos (iff1.mp hP)]
  · rw [if_neg hP, if_neg (fun h => hP (iff1.mpr h))]

end A001227Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a001227.main := by
  intro n hn
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := n) (by omega)
  have hm0 : 0 < m := hm.pos
  -- second identity: split the odd divisors at sqrt(2n)
  have hsecond : OMA.S_oeis_a001227.A001227 (2 ^ a * m)
      = OMA.S_oeis_a001227.A082647 (2 ^ a * m) + OMA.S_oeis_a001227.A131576 (2 ^ a * m) := by
    unfold OMA.S_oeis_a001227.A001227 OMA.S_oeis_a001227.A082647 OMA.S_oeis_a001227.A131576
    have h := Finset.card_filter_add_card_filter_not
      (s := (Nat.divisors (2 ^ a * m)).filter (fun d => Odd d))
      (fun d => d ^ 2 < 2 * (2 ^ a * m))
    rw [Finset.filter_filter, Finset.filter_filter] at h
    have h1 : (Nat.divisors (2 ^ a * m)).filter
          (fun d => Odd d ∧ ¬ d ^ 2 < 2 * (2 ^ a * m))
        = (Nat.divisors (2 ^ a * m)).filter (fun d => Odd d ∧ 2 * (2 ^ a * m) < d ^ 2) := by
      apply Finset.filter_congr
      intro d _
      constructor
      · rintro ⟨hd, hlt⟩
        obtain ⟨t, ht⟩ := hd.pow (n := 2)
        exact ⟨hd, by omega⟩
      · rintro ⟨hd, hlt⟩
        exact ⟨hd, by omega⟩
    rw [h1] at h
    omega
  -- the three counts in terms of the odd part m
  have hM : OMA.S_oeis_a001227.A067742 (2 ^ a * m) = A001227Proof.Qc 1 (2 ^ a * m) (2 ^ a * m) := by
    unfold OMA.S_oeis_a001227.A067742
    rw [A001227Proof.Qc_def]
    congr 1
    apply Finset.filter_congr
    intro d _
    rw [one_mul]
  have hL : OMA.S_oeis_a001227.A082647 (2 ^ a * m) = A001227Proof.H m 1 (2 ^ a * m) := by
    unfold OMA.S_oeis_a001227.A082647
    rw [A001227Proof.H_def, A001227Proof.odd_filter a m hm]
    congr 1
    apply Finset.filter_congr
    intro d _
    rw [one_mul]
  have hG : OMA.S_oeis_a001227.A131576 (2 ^ a * m)
      = A001227Proof.H m (1 * 4 ^ (a + 1)) (2 ^ a * m) := by
    unfold OMA.S_oeis_a001227.A131576
    rw [A001227Proof.odd_filter a m hm]
    exact A001227Proof.inv_count a m hm0
  have hmain := A001227Proof.main_ind m hm a 1 (2 ^ a * m)
  refine ⟨?_, hsecond⟩
  rw [hsecond, hM, hL, hG]
  omega
