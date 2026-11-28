import OMAStatements.S_oeis_a349890
import Mathlib

open OMA.S_oeis_a349890

def Eq6 (x : ℤ) (E : ℕ) (n j : ℤ) : Prop :=
  6 * n * 2 ^ E - 2 * ((2 ^ E) ^ 2 - 1) - 3 * j * (j + 1) = 6 * x

lemma six_T (n k : ℕ) : Eq6 (T n k) (e n) n ((k : ℤ) - 1) := by
  have h3 : ((4 : ℤ) ^ e n - 1) / 3 * 3 = 4 ^ e n - 1 := by
    apply Int.ediv_mul_cancel
    have := (Int.ModEq.pow (e n) (show (4 : ℤ) ≡ 1 [ZMOD 3] by decide)).symm.dvd
    simpa using this
  have h2 : ((k : ℤ) * ((k : ℤ) - 1)) / 2 * 2 = (k : ℤ) * ((k : ℤ) - 1) :=
    Int.ediv_mul_cancel (Int.even_mul_pred_self (k : ℤ)).two_dvd
  have h4 : (4 : ℤ) ^ e n = (2 ^ e n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  unfold Eq6 T
  rw [← h4]
  linear_combination 2 * h3 + 3 * h2

lemma e_spec (n : ℕ) (hn : 1 ≤ n) : n < 2 ^ e n ∧ 2 ^ e n ≤ 2 * n := by
  unfold e
  constructor
  · rw [add_comm]; exact Nat.lt_pow_succ_log_self (by norm_num) n
  · rw [pow_add, pow_one]; exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))

lemma e_eq (n E : ℕ) (h1 : 2 ^ E ≤ n) (h2 : n < 2 ^ (E + 1)) : e n = E + 1 := by
  unfold e
  rw [add_comm]; congr 1
  have hp : 0 < 2 ^ E := by positivity
  exact (Nat.log_eq_iff (Or.inr ⟨by norm_num, by omega⟩)).2 ⟨h1, h2⟩

lemma step_even {x : ℤ} {E : ℕ} {n j u : ℤ} (h : Eq6 x E n j) (hu : n + 2 ^ E = 2 * u) :
    Eq6 x (E + 1) u j := by
  unfold Eq6 at *
  have hn : n = 2 * u - 2 ^ E := by linarith
  subst hn
  rw [pow_succ]; linear_combination h

lemma step_odd {x : ℤ} {E : ℕ} {n j u : ℤ} (h : Eq6 x E n j) (hu : n + 2 ^ E = 2 * u + 1) :
    Eq6 x (E + 1) (u + 2 ^ E - j) (2 * 2 ^ E - 1 - j) := by
  unfold Eq6 at *
  have hn : n = 2 * u + 1 - 2 ^ E := by linarith
  subst hn
  rw [pow_succ]; linear_combination h

lemma stepNo {x : ℤ} {E : ℕ} {n j : ℤ} (h : Eq6 x E n j) (hj0 : 0 ≤ j) (hj : j < 2 ^ E)
    (hn0 : 0 ≤ n) (hn : n < 2 ^ E) :
    ∃ n' j' : ℤ, Eq6 x (E + 1) n' j' ∧ 0 ≤ j' ∧ j' < 2 ^ (E + 1) ∧ 0 ≤ n' ∧ n' < 2 ^ (E + 1) ∧
      ¬ (2 ^ E ≤ n' ∧ j' < n') := by
  have hP : (0 : ℤ) < 2 ^ E := by positivity
  rcases Int.even_or_odd' (n + 2 ^ E) with ⟨u, hu | hu⟩
  · refine ⟨u, j, step_even h hu, hj0, ?_, ?_, ?_, ?_⟩
    · rw [pow_succ]; linarith
    · linarith
    · rw [pow_succ]; linarith
    · rintro ⟨a, -⟩; linarith
  · refine ⟨_, _, step_odd h hu, ?_, ?_, ?_, ?_, ?_⟩
    · linarith
    · rw [pow_succ]; linarith
    · linarith
    · rw [pow_succ]; linarith
    · rintro ⟨-, a⟩; linarith

lemma odd_cop (E : ℕ) (a b : ℤ) (ha : Odd a) (h : (2 : ℤ) ^ E ∣ a * b) : (2 : ℤ) ^ E ∣ b := by
  obtain ⟨c, rfl⟩ := ha
  have hc : IsCoprime (2 : ℤ) (2 * c + 1) := ⟨-c, 1, by ring⟩
  exact (hc.pow_left).dvd_of_dvd_mul_left h

lemma uniq {x : ℤ} {E : ℕ} {n j n' j' : ℤ} (h : Eq6 x E n j) (h' : Eq6 x E n' j')
    (hj0 : 0 ≤ j) (hj : j < 2 ^ E) (hj0' : 0 ≤ j') (hj' : j' < 2 ^ E) : n = n' ∧ j = j' := by
  have hP : (0 : ℤ) < 2 ^ E := by positivity
  unfold Eq6 at h h'
  have key3 : 3 * ((j - j') * (j + j' + 1)) = 3 * (2 ^ (E + 1) * (n - n')) := by
    rw [pow_succ]; linear_combination h' - h
  have key : (j - j') * (j + j' + 1) = 2 ^ (E + 1) * (n - n') :=
    mul_left_cancel₀ (by norm_num) key3
  have hjj : j = j' := by
    by_contra hne
    have hd : (2 : ℤ) ^ (E + 1) ∣ (j - j') * (j + j' + 1) := ⟨n - n', key⟩
    rcases Int.even_or_odd (j - j') with he | ho
    · have ho : Odd (j + j' + 1) := by
        have e1 : j + j' + 1 = (j - j') + (2 * j' + 1) := by ring
        rw [e1]; exact he.add_odd ⟨j', rfl⟩
      have hd' : (2 : ℤ) ^ (E + 1) ∣ (j - j') := by
        rw [mul_comm] at hd; exact odd_cop _ _ _ ho hd
      have h0 : j - j' = 0 :=
        Int.eq_zero_of_abs_lt_dvd hd' (by rw [abs_lt, pow_succ]; constructor <;> linarith)
      exact hne (by linarith)
    · have hd' := odd_cop _ _ _ ho hd
      have h1 := Int.le_of_dvd (by linarith) hd'
      rw [pow_succ] at h1; linarith
  subst hjj
  refine ⟨?_, rfl⟩
  have h0 : (2 : ℤ) ^ (E + 1) * (n - n') = 0 := by rw [← key]; ring
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact absurd h1 (by positivity)
  · linarith

lemma propg {x : ℤ} : ∀ (d E : ℕ) (n j : ℤ), Eq6 x E n j → 0 ≤ j → j < 2 ^ E → 0 ≤ n →
    n < 2 ^ E → ∃ n' j' : ℤ, Eq6 x (E + d + 1) n' j' ∧ 0 ≤ j' ∧ j' < 2 ^ (E + d + 1) ∧ 0 ≤ n' ∧
      n' < 2 ^ (E + d + 1) ∧ ¬ (2 ^ (E + d) ≤ n' ∧ j' < n') := by
  intro d
  induction d with
  | zero => intro E n j h a b c d'; exact stepNo h a b c d'
  | succ d ih =>
    intro E n j h a b c d'
    obtain ⟨n1, j1, h1, a1, b1, c1, d1, -⟩ := ih E n j h a b c d'
    exact stepNo h1 a1 b1 c1 d1

lemma hitFin {x : ℤ} {E : ℕ} {n j : ℤ} (h : Eq6 x (E + 1) n j) (hj0 : 0 ≤ j) (hjn : j < n)
    (h1 : 2 ^ E ≤ n) (h2 : n < 2 ^ (E + 1)) :
    ∃ p ∈ {p : ℕ × ℕ | 1 ≤ p.2 ∧ p.2 ≤ p.1}, T p.1 p.2 = x := by
  lift j to ℕ using hj0
  lift n to ℕ using (by linarith [Int.natCast_nonneg j])
  have hjn' : j < n := by exact_mod_cast hjn
  refine ⟨(n, j + 1), ⟨by simp, by simpa using hjn'⟩, ?_⟩
  have he : e n = E + 1 := e_eq n E (by exact_mod_cast h1) (by exact_mod_cast h2)
  have h6 := six_T n (j + 1)
  rw [he] at h6
  unfold Eq6 at h h6
  push_cast at h6
  have e1 : ((j : ℤ) + 1 - 1) = j := by ring
  rw [e1] at h6
  show T n (j + 1) = x
  linarith

lemma hitEx {x : ℤ} : ∀ (m E : ℕ) (n j : ℤ), Eq6 x E n j → 0 ≤ j → j < 2 ^ E → n = 2 ^ E + m →
    ∃ p ∈ {p : ℕ × ℕ | 1 ≤ p.2 ∧ p.2 ≤ p.1}, T p.1 p.2 = x := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro E n j h hj0 hj hn
    have hP : (0 : ℤ) < 2 ^ E := by positivity
    rcases Nat.even_or_odd' m with ⟨t, rfl | rfl⟩
    · have hu : n + 2 ^ E = 2 * (2 ^ E + (t : ℤ)) := by push_cast at hn; linarith
      have h1 := step_even h hu
      have ht0 : (0 : ℤ) ≤ t := Int.natCast_nonneg t
      by_cases ht : (t : ℤ) < 2 ^ E
      · exact hitFin h1 hj0 (by linarith) (by linarith) (by rw [pow_succ]; linarith)
      · obtain ⟨m', hm'⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ (t : ℤ) - 2 ^ E by linarith)
        refine ih m' ?_ (E + 1) _ j h1 hj0 (by rw [pow_succ]; linarith)
          (by rw [pow_succ, ← hm']; ring)
        have : (m' : ℤ) < 2 * t := by linarith
        exact_mod_cast this
    · have hu : n + 2 ^ E = 2 * (2 ^ E + (t : ℤ)) + 1 := by push_cast at hn; linarith
      have h1 := step_odd h hu
      have ht0 : (0 : ℤ) ≤ t := Int.natCast_nonneg t
      by_cases ht : (t : ℤ) < j
      · exact hitFin h1 (by linarith) (by linarith) (by linarith) (by rw [pow_succ]; linarith)
      · obtain ⟨m', hm'⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ (t : ℤ) - j by linarith)
        refine ih m' ?_ (E + 1) _ _ h1 (by linarith) (by rw [pow_succ]; linarith)
          (by rw [pow_succ, ← hm']; ring)
        have : (m' : ℤ) < 2 * t + 1 := by linarith
        exact_mod_cast this

lemma inj_aux {n k n' k' : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hk1' : 1 ≤ k') (hkn' : k' ≤ n')
    (heq : T n k = T n' k') (hle : e n ≤ e n') : n = n' ∧ k = k' := by
  have h := six_T n k
  have h' := six_T n' k'
  rw [← heq] at h'
  obtain ⟨ha, hb⟩ := e_spec n (by omega)
  obtain ⟨ha', hb'⟩ := e_spec n' (by omega)
  have ha1 : (n : ℤ) < 2 ^ e n := by exact_mod_cast ha
  have ha1' : (n' : ℤ) < 2 ^ e n' := by exact_mod_cast ha'
  have hb1' : (2 : ℤ) ^ e n' ≤ 2 * n' := by exact_mod_cast hb'
  have c1 : (1 : ℤ) ≤ k := by exact_mod_cast hk1
  have c2 : (k : ℤ) ≤ n := by exact_mod_cast hkn
  have c1' : (1 : ℤ) ≤ k' := by exact_mod_cast hk1'
  have c2' : (k' : ℤ) ≤ n' := by exact_mod_cast hkn'
  rcases Nat.eq_or_lt_of_le hle with he | hlt
  · rw [← he] at h' ha1'
    obtain ⟨u1, u2⟩ := uniq h h' (by linarith) (by linarith) (by linarith) (by linarith)
    have u3 : (k : ℤ) = k' := by linarith
    exact ⟨by exact_mod_cast u1, by exact_mod_cast u3⟩
  · exfalso
    obtain ⟨d, hd⟩ : ∃ d, e n' = e n + d + 1 := ⟨e n' - e n - 1, by omega⟩
    obtain ⟨n1, j1, g, g1, g2, g3, g4, g5⟩ :=
      propg d (e n) n ((k : ℤ) - 1) h (by linarith) (by linarith) (Int.natCast_nonneg n) ha1
    rw [← hd] at g g2 g4
    obtain ⟨u1, u2⟩ := uniq g h' g1 g2 (by linarith) (by linarith)
    apply g5
    constructor
    · rw [hd, pow_succ] at hb1'; linarith
    · linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a349890.main := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨n, k⟩ ⟨hk1, hkn⟩
    show (1 : ℤ) ≤ T n k
    have hk1 : 1 ≤ k := hk1
    have hkn : k ≤ n := hkn
    have h6 := six_T n k
    obtain ⟨ha, hb⟩ := e_spec n (by omega)
    unfold Eq6 at h6
    have ha' : (n : ℤ) + 1 ≤ 2 ^ e n := by exact_mod_cast ha
    have hb' : (2 : ℤ) ^ e n ≤ 2 * n := by exact_mod_cast hb
    have hk1' : (1 : ℤ) ≤ k := by exact_mod_cast hk1
    have hkn' : (k : ℤ) ≤ n := by exact_mod_cast hkn
    nlinarith [mul_nonneg (sub_nonneg.2 ha') (sub_nonneg.2 hb'),
      mul_nonneg (sub_nonneg.2 hkn') (show (0 : ℤ) ≤ n + k - 1 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n - 1 by linarith) (show (0 : ℤ) ≤ n + 4 by linarith)]
  · rintro ⟨n, k⟩ ⟨hk1, hkn⟩ ⟨n', k'⟩ ⟨hk1', hkn'⟩ heq
    rcases le_total (e n) (e n') with hle | hle
    · obtain ⟨a, b⟩ := inj_aux hk1 hkn hk1' hkn' heq hle
      exact Prod.ext a b
    · obtain ⟨a, b⟩ := inj_aux hk1' hkn' hk1 hkn heq.symm hle
      exact Prod.ext a.symm b.symm
  · intro x hx
    have hx1 : (1 : ℤ) ≤ x := hx
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ x - 1 by linarith)
    exact hitEx m 0 x 0 (by unfold Eq6; ring) le_rfl (by norm_num)
      (by rw [pow_zero, ← hm]; ring)
