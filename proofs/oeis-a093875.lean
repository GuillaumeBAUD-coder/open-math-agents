import OMAStatements.S_oeis_a093875
import Mathlib

namespace OMA.P_oeis_a093875

open OMA.S_oeis_a093875

theorem kepler_even (m : ℕ) (hm : 0 < m) :
    kepler (2 * m) = ((kepler m).1, (kepler m).1 + (kepler m).2) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h2 : 2 * (k + 1) = (2 * k) + 2 := by ring
  have e2 : (2 * k + 2) / 2 = k + 1 := by omega
  have p2 : (2 * k + 2) % 2 = 0 := by omega
  rw [h2, kepler, if_pos p2, e2]

theorem kepler_odd (m : ℕ) (hm : 0 < m) :
    kepler (2 * m + 1) = ((kepler m).2, (kepler m).1 + (kepler m).2) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
  have e1 : (2 * k + 1 + 2) / 2 = k + 1 := by omega
  have p1 : ¬ (2 * k + 1 + 2) % 2 = 0 := by omega
  rw [h1, kepler, if_neg p1, e1]

theorem kepler_one : kepler 1 = (1, 1) := by rw [kepler]

/-- Exponents of n shifted by s, descending. -/
def E (n s : ℕ) : List ℕ := ((Nat.bitIndices n).map (· + s)).reverse

theorem E_one (s : ℕ) : E 1 s = [s] := by simp [E]

theorem E_even (n s : ℕ) : E (2 * n) s = E n (s + 1) := by
  unfold E
  rw [Nat.bitIndices_two_mul, List.map_map]
  congr 2
  funext x
  simp only [Function.comp]
  omega

theorem E_odd (n s : ℕ) : E (2 * n + 1) s = E n (s + 1) ++ [s] := by
  unfold E
  rw [Nat.bitIndices_two_mul_add_one, List.map_cons, List.reverse_cons, List.map_map]
  congr 2
  · congr 1
    funext x
    simp only [Function.comp]
    omega
  · simp

theorem expo_eq (n : ℕ) : expo n = E n 2 := by
  have h : expo n = E (2 * (2 * n)) 0 := by
    unfold expo E
    have : 4 * n = 2 * (2 * n) := by ring
    rw [this]
    simp
  rw [h, E_even, E_even]

/-- Differences with a final base value t. -/
def dif : List ℕ → ℕ → List ℕ
  | [], _ => []
  | [b], t => [b - t]
  | b :: c :: r, t => (b - c) :: dif (c :: r) t

theorem diffs_eq : ∀ l : List ℕ, diffs l = dif l 0
  | [] => by simp [diffs, dif]
  | [b] => by simp [diffs, dif]
  | b :: c :: r => by
    have := diffs_eq (c :: r)
    simp [diffs, dif, this]

theorem dif_append (s t : ℕ) : ∀ l : List ℕ, l ≠ [] → dif (l ++ [s]) t = dif l s ++ [s - t]
  | [], h => absurd rfl h
  | [b], _ => by simp [dif]
  | b :: c :: r, _ => by
    have := dif_append s t (c :: r) (by simp)
    simp only [List.cons_append] at this ⊢
    simp [dif, this]

def T (d : ℕ) (v : ℕ × ℕ) : ℕ × ℕ := (d * v.1 + v.2, v.1)

def cfV : List ℕ → ℕ × ℕ → ℕ × ℕ
  | [], v => v
  | d :: r, v => T d (cfV r v)

theorem cfV_append (v : ℕ × ℕ) : ∀ l m : List ℕ, cfV (l ++ m) v = cfV l (cfV m v)
  | [], m => by simp [cfV]
  | d :: r, m => by simp [cfV, cfV_append v r m]

theorem key : ∀ n : ℕ, 0 < n → ∀ (t g : ℕ) (v : ℕ × ℕ), 0 < g →
    E n (t + g) ≠ [] ∧ (∀ d ∈ dif (E n (t + g)) t, 0 < d) ∧
    ((cfV (dif (E n (t + g)) t) v).1 : ℤ) =
      ((g : ℤ) * v.1 + v.2 - v.1) * (kepler n).1 + v.1 * (kepler n).2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn t g v hg
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have : n = 1 := by omega
      subst this
      rw [E_one, kepler_one]
      refine ⟨by simp, ?_, ?_⟩
      · intro d hd
        simp [dif] at hd
        omega
      · simp [dif, cfV, T]
    · rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
      · have hm : 0 < m := by omega
        have := ih m (by omega) hm t (g + 1) v (by omega)
        rw [E_even, kepler_even m hm]
        rw [show t + g + 1 = t + (g + 1) by ring]
        obtain ⟨a1, a2, a3⟩ := this
        refine ⟨a1, a2, ?_⟩
        rw [a3]
        push_cast
        ring
      · have hm : 0 < m := by omega
        have := ih m (by omega) hm (t + g) 1 (T g v) (by omega)
        obtain ⟨a1, a2, a3⟩ := this
        rw [E_odd, kepler_odd m hm]
        refine ⟨by simp, ?_, ?_⟩
        · rw [dif_append _ _ _ a1]
          intro d hd
          rcases List.mem_append.1 hd with h | h
          · exact a2 d h
          · simp at h
            omega
        · rw [dif_append _ _ _ a1, cfV_append, show t + g - t = g by omega]
          have e : cfV [g] v = T g v := by simp [cfV]
          rw [e, a3]
          simp only [T]
          push_cast
          ring

theorem cf_pair : ∀ l : List ℕ, l ≠ [] → (∀ d ∈ l, 0 < d) →
    0 < (cfV l (1, 0)).1 ∧ 0 < (cfV l (1, 0)).2 ∧
    Nat.Coprime (cfV l (1, 0)).1 (cfV l (1, 0)).2 ∧
    cf l = ((cfV l (1, 0)).1 : ℚ) / ((cfV l (1, 0)).2 : ℚ)
  | [], h, _ => absurd rfl h
  | [d], _, hp => by
    have hd : 0 < d := hp d (by simp)
    simp [cfV, T, cf, hd]
  | d :: e :: r, _, hp => by
    obtain ⟨p1, p2, p3, p4⟩ := cf_pair (e :: r) (by simp)
      (fun x hx => hp x (List.mem_cons_of_mem _ hx))
    have hc : cfV (d :: e :: r) (1, 0) = T d (cfV (e :: r) (1, 0)) := rfl
    rw [hc]
    generalize cfV (e :: r) (1, 0) = w at p1 p2 p3 p4
    obtain ⟨p, q⟩ := w
    simp only at p1 p2 p3 p4
    simp only [T]
    refine ⟨by positivity, p1, ?_, ?_⟩
    · have : Nat.Coprime (q + d * p) p := by
        rw [Nat.coprime_add_mul_right_left]
        exact p3.symm
      rwa [Nat.add_comm] at this
    · have hp0 : (p : ℚ) ≠ 0 := by positivity
      have hq0 : (q : ℚ) ≠ 0 := by positivity
      rw [cf, p4]
      push_cast
      field_simp

theorem A_eq (n : ℕ) (hn : 0 < n) : A071585 n = a (2 * n) := by
  obtain ⟨k1, k2, k3⟩ := key n hn 0 2 (1, 0) (by norm_num)
  rw [Nat.zero_add] at k1 k2 k3
  obtain ⟨c1, c2, c3, c4⟩ := cf_pair (dif (E n 2) 0)
    (by
      intro h
      rcases hE : E n 2 with _ | ⟨b, _ | ⟨c, r⟩⟩
      · exact k1 hE
      · rw [hE] at h; simp [dif] at h
      · rw [hE] at h; simp [dif] at h) k2
  have hnum : (cf (dif (E n 2) 0)).num = ((cfV (dif (E n 2) 0) (1, 0)).1 : ℤ) := by
    rw [c4]
    have := Rat.num_div_eq_of_coprime (a := ((cfV (dif (E n 2) 0) (1, 0)).1 : ℤ))
      (b := ((cfV (dif (E n 2) 0) (1, 0)).2 : ℤ)) (by exact_mod_cast c2) (by simpa using c3)
    rw [Int.cast_natCast, Int.cast_natCast] at this
    exact this
  have hA : A071585 n = (cf (diffs (expo n))).num.toNat := by
    unfold A071585
    rw [if_neg (by omega)]
  rw [hA, expo_eq, diffs_eq, hnum, Int.toNat_natCast]
  have : ((cfV (dif (E n 2) 0) (1, 0)).1 : ℤ) = ((a (2 * n) : ℕ) : ℤ) := by
    rw [k3]
    unfold a
    rw [kepler_even n hn]
    push_cast
    ring
  exact_mod_cast this

theorem first (n : ℕ) (hn : 0 < n) : a (2 * n + 1) = a (2 * n) := by
  unfold a
  rw [kepler_odd n hn, kepler_even n hn]

theorem all : (∀ n : ℕ, 0 < n → a (2 * n + 1) = a (2 * n)) ∧
    (∀ n : ℕ, a (2 * n + 1) = A071585 n) ∧
    (∀ n : ℕ, 0 < n → a (2 * n) = A071585 n) := by
  refine ⟨first, ?_, fun n hn => (A_eq n hn).symm⟩
  intro n
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp [a, kepler_one, A071585]
  · rw [first n h, A_eq n h]

end OMA.P_oeis_a093875

theorem OMA.solution : type_of% @OMA.S_oeis_a093875.main := OMA.P_oeis_a093875.all
