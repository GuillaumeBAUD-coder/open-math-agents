import FormalConjectures.ErdosProblems.«376»

namespace OMA.E376

def G (p n : ℕ) : Prop := ∀ k : ℕ, 2 * (n % p ^ k) < p ^ k

theorem G_not_dvd {p n : ℕ} (hp : p.Prime) (h : G p n) : ¬ p ∣ n.centralBinom := by
  have key := Nat.Prime.emultiplicity_choose' (p := p) (n := n) (k := n)
    (b := Nat.log p (n + n) + 1) hp (Nat.lt_succ_self _)
  have hempty : (Finset.filter (fun i => p ^ i ≤ n % p ^ i + n % p ^ i)
      (Finset.Ico 1 (Nat.log p (n + n) + 1))) = ∅ := by
    apply Finset.filter_eq_empty_iff.2
    intro i _ hi
    have := h i
    omega
  rw [hempty, Finset.card_empty] at key
  have h0 : ¬ p ∣ (n + n).choose n := by
    rw [← emultiplicity_eq_zero]
    exact key.trans Nat.cast_zero
  rw [Nat.centralBinom_eq_two_mul_choose, two_mul]
  exact h0

theorem G_small {p c : ℕ} (h : 2 * c < p) : G p c := by
  intro k
  cases k with
  | zero =>
    rw [pow_zero, Nat.mod_one]
    omega
  | succ k =>
    have h1 : p ≤ p ^ (k + 1) := Nat.le_self_pow (Nat.succ_ne_zero k) p
    have h2 : c % p ^ (k + 1) = c := Nat.mod_eq_of_lt (by omega)
    rw [h2]
    omega

theorem G_append {p a d : ℕ} (hd : 2 * d < p) (h : G p a) : G p (p * a + d) := by
  intro k
  cases k with
  | zero =>
    rw [pow_zero, Nat.mod_one]
    omega
  | succ k =>
    have hp : 0 < p := by omega
    have hdp : d < p := by omega
    have h1 : (p * a + d) % p ^ (k + 1) = d + p * (a % p ^ k) := by
      rw [pow_succ', Nat.mod_mul, Nat.mul_add_mod, Nat.mod_eq_of_lt hdp, Nat.mul_add_div hp,
        Nat.div_eq_of_lt hdp, add_zero]
    have h2 := h k
    have h3 : p * (2 * (a % p ^ k) + 1) ≤ p * p ^ k := Nat.mul_le_mul_left p h2
    have h4 : p * (2 * (a % p ^ k) + 1) = 2 * (p * (a % p ^ k)) + p := by ring
    rw [h1, pow_succ']
    omega

theorem step {p h X Y u V : ℕ} (hp : p = 2 * h + 1) (hX : 0 < X) (h1 : 2 * u ≤ 2 * V + Y)
    (h2 : 2 * V ≤ 2 * u + p * X) (hXY : X ≤ Y) :
    ∃ d, 2 * d < p ∧ 2 * (u + d * X) ≤ 2 * V + Y ∧ 2 * V ≤ 2 * (u + d * X) + X := by
  subst hp
  by_cases hc : h ≤ (2 * V + Y - 2 * u) / (2 * X)
  · refine ⟨h, by omega, ?_, ?_⟩
    · have h3 : h * (2 * X) ≤ 2 * V + Y - 2 * u := (Nat.le_div_iff_mul_le (by omega)).1 hc
      have h4 : h * (2 * X) = 2 * (h * X) := by ring
      omega
    · have h4 : (2 * h + 1) * X = 2 * (h * X) + X := by ring
      omega
  · have hc' : (2 * V + Y - 2 * u) / (2 * X) < h := by omega
    refine ⟨(2 * V + Y - 2 * u) / (2 * X), by omega, ?_, ?_⟩
    · have h3 := Nat.div_mul_le_self (2 * V + Y - 2 * u) (2 * X)
      have h4 : (2 * V + Y - 2 * u) / (2 * X) * (2 * X)
          = 2 * ((2 * V + Y - 2 * u) / (2 * X) * X) := by ring
      omega
    · have h3 := Nat.lt_div_mul_add (a := 2 * V + Y - 2 * u) (b := 2 * X) (by omega)
      have h4 : (2 * V + Y - 2 * u) / (2 * X) * (2 * X)
          = 2 * ((2 * V + Y - 2 * u) / (2 * X) * X) := by ring
      omega

theorem descent {p q : ℕ} (hp : Odd p) (hq : Odd q) :
    ∀ m i j a b : ℕ, i + j = m → G p a → G q b →
      2 * (a * p ^ i) ≤ 2 * (b * q ^ j) + q ^ j →
      2 * (b * q ^ j) ≤ 2 * (a * p ^ i) + p ^ i →
      q ^ j ≤ q * p ^ i → p ^ i ≤ p * q ^ j →
      ∃ n, G p n ∧ G q n ∧ a * p ^ i ≤ n ∧ b * q ^ j ≤ n := by
  obtain ⟨hh, hph⟩ := hp
  obtain ⟨kk, hqk⟩ := hq
  have ppos : 0 < p := by omega
  have qpos : 0 < q := by omega
  intro m
  induction m with
  | zero =>
    intro i j a b hij ha hb h1 h2 _ _
    obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := by omega
    simp only [pow_zero, mul_one] at h1 h2
    have hab : a = b := by omega
    subst hab
    exact ⟨a, ha, hb, by rw [pow_zero, mul_one], by rw [pow_zero, mul_one]⟩
  | succ m ih =>
    intro i j a b hij ha hb h1 h2 h3 h4
    by_cases hc : ∃ i', i = i' + 1 ∧ q ^ j ≤ q * p ^ i'
    · obtain ⟨i', rfl, hc⟩ := hc
      have hX : 0 < p ^ i' := Nat.pow_pos ppos
      have e1 : p ^ (i' + 1) = p * p ^ i' := pow_succ' p i'
      have hXY : p ^ i' ≤ q ^ j := by
        rw [e1] at h4
        exact Nat.le_of_mul_le_mul_left h4 ppos
      have h2' : 2 * (b * q ^ j) ≤ 2 * (a * p ^ (i' + 1)) + p * p ^ i' := by
        rw [← e1]; exact h2
      obtain ⟨d, hd, s1, s2⟩ := step hph hX h1 h2' hXY
      have e2 : (p * a + d) * p ^ i' = a * p ^ (i' + 1) + d * p ^ i' := by
        rw [e1]; ring
      have h4' : p ^ i' ≤ p * q ^ j := le_trans hXY (Nat.le_mul_of_pos_left _ ppos)
      obtain ⟨n, hn1, hn2, hn3, hn4⟩ := ih i' j (p * a + d) b (by omega) (G_append hd ha) hb
        (by rw [e2]; exact s1) (by rw [e2]; exact s2) hc h4'
      refine ⟨n, hn1, hn2, ?_, hn4⟩
      rw [e2] at hn3
      omega
    · have hj : ∃ j', j = j' + 1 ∧ p ^ i ≤ p * q ^ j' := by
        cases j with
        | zero =>
          exfalso
          apply hc
          refine ⟨m, by omega, ?_⟩
          rw [pow_zero]
          exact Nat.mul_pos qpos (Nat.pow_pos ppos)
        | succ j' =>
          refine ⟨j', rfl, ?_⟩
          cases i with
          | zero =>
            rw [pow_zero]
            exact Nat.mul_pos ppos (Nat.pow_pos qpos)
          | succ i' =>
            have hlt : q * p ^ i' < q ^ (j' + 1) := by
              by_contra hcon
              exact hc ⟨i', rfl, by omega⟩
            rw [pow_succ' q j'] at hlt
            have hlt' : p ^ i' < q ^ j' := Nat.lt_of_mul_lt_mul_left hlt
            rw [pow_succ' p i']
            exact Nat.mul_le_mul_left p (le_of_lt hlt')
      obtain ⟨j', rfl, hc'⟩ := hj
      have hX : 0 < q ^ j' := Nat.pow_pos qpos
      have e1 : q ^ (j' + 1) = q * q ^ j' := pow_succ' q j'
      have hXY : q ^ j' ≤ p ^ i := by
        rw [e1] at h3
        exact Nat.le_of_mul_le_mul_left h3 qpos
      have h1' : 2 * (a * p ^ i) ≤ 2 * (b * q ^ (j' + 1)) + q * q ^ j' := by
        rw [← e1]; exact h1
      obtain ⟨d, hd, s1, s2⟩ := step hqk hX h2 h1' hXY
      have e2 : (q * b + d) * q ^ j' = b * q ^ (j' + 1) + d * q ^ j' := by
        rw [e1]; ring
      have h3' : q ^ j' ≤ q * p ^ i := le_trans hXY (Nat.le_mul_of_pos_left _ qpos)
      obtain ⟨n, hn1, hn2, hn3, hn4⟩ := ih i j' a (q * b + d) (by omega) ha (G_append hd hb)
        (by rw [e2]; exact s2) (by rw [e2]; exact s1) h3' hc'
      refine ⟨n, hn1, hn2, hn3, ?_⟩
      rw [e2] at hn4
      omega

theorem core {p q : ℕ} (hp : Odd p) (hq : Odd q) (hp3 : 3 ≤ p) (hq5 : 5 ≤ q) (N : ℕ) :
    ∃ n, N ≤ n ∧ G p n ∧ G q n := by
  have hyN : N < q ^ N := Nat.lt_pow_self (by omega)
  have hex : ∃ i, q ^ N ≤ p ^ i := ⟨q ^ N, le_of_lt (Nat.lt_pow_self (by omega))⟩
  classical
  have hi : q ^ N ≤ p ^ (Nat.find hex) := Nat.find_spec hex
  have hmin : ∀ i', i' < Nat.find hex → ¬ q ^ N ≤ p ^ i' := fun i' h => Nat.find_min hex h
  generalize Nat.find hex = i at hi hmin
  have ppos : 0 < p := by omega
  have qpos : 0 < q := by omega
  have h4 : p ^ i ≤ p * q ^ N := by
    cases i with
    | zero =>
      rw [pow_zero]
      exact Nat.mul_pos ppos (Nat.pow_pos qpos)
    | succ i' =>
      have := hmin i' (Nat.lt_succ_self i')
      rw [pow_succ' p i']
      exact Nat.mul_le_mul_left p (by omega)
  have h3 : q ^ N ≤ q * p ^ i := le_trans hi (Nat.le_mul_of_pos_left _ qpos)
  by_cases hA : 2 * q ^ N ≤ p ^ i
  · obtain ⟨n, hn1, hn2, _, hn4⟩ := descent hp hq (i + N) i N 0 1 rfl
      (G_small (by omega)) (G_small (by omega)) (by omega) (by omega) h3 h4
    exact ⟨n, by omega, hn1, hn2⟩
  · by_cases hB : 2 * p ^ i ≤ 3 * q ^ N
    · obtain ⟨n, hn1, hn2, hn3, _⟩ := descent hp hq (i + N) i N 1 1 rfl
        (G_small (by omega)) (G_small (by omega)) (by omega) (by omega) h3 h4
      exact ⟨n, by omega, hn1, hn2⟩
    · obtain ⟨n, hn1, hn2, hn3, _⟩ := descent hp hq (i + N) i N 1 2 rfl
        (G_small (by omega)) (G_small (by omega)) (by omega) (by omega) h3 h4
      exact ⟨n, by omega, hn1, hn2⟩

theorem same {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) (N : ℕ) :
    ∃ n, N ≤ n ∧ G p n ∧ G p n := by
  have hyN : N < p ^ N := Nat.lt_pow_self (by omega)
  have ppos : 0 < p := by omega
  have h3 : p ^ N ≤ p * p ^ N := Nat.le_mul_of_pos_left _ ppos
  obtain ⟨n, hn1, hn2, hn3, _⟩ := descent hp hp (N + N) N N 1 1 rfl
    (G_small (by omega)) (G_small (by omega)) (by omega) (by omega) h3 h3
  exact ⟨n, by omega, hn1, hn2⟩

theorem final {p q : ℕ} (h₁ : p.Prime) (h₂ : Odd p) (h₃ : q.Prime) (h₄ : Odd q) :
    { (n : ℕ) | n.centralBinom.Coprime (p * q) }.Infinite := by
  have hp3 : 3 ≤ p := by
    obtain ⟨k, hk⟩ := h₂
    have := h₁.two_le
    omega
  have hq3 : 3 ≤ q := by
    obtain ⟨k, hk⟩ := h₄
    have := h₃.two_le
    omega
  have hsub : ∀ N, ∃ n, N ≤ n ∧ G p n ∧ G q n := by
    intro N
    by_cases hq5 : 5 ≤ q
    · exact core h₂ h₄ hp3 hq5 N
    · by_cases hp5 : 5 ≤ p
      · obtain ⟨n, hn, h1, h2⟩ := core h₄ h₂ hq3 hp5 N
        exact ⟨n, hn, h2, h1⟩
      · have hpq : p = q := by
          obtain ⟨k, hk⟩ := h₂
          obtain ⟨l, hl⟩ := h₄
          omega
        subst hpq
        exact same h₂ hp3 N
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨n, hn, h1, h2⟩ := hsub (B + 1)
  have hmem : n ∈ { (n : ℕ) | n.centralBinom.Coprime (p * q) } := by
    show n.centralBinom.Coprime (p * q)
    exact Nat.Coprime.mul_right
      ((Nat.Prime.coprime_iff_not_dvd h₁).2 (G_not_dvd h₁ h1)).symm
      ((Nat.Prime.coprime_iff_not_dvd h₃).2 (G_not_dvd h₃ h2)).symm
  have := hB hmem
  omega

end OMA.E376

theorem OMA.solution : type_of% @Erdos376.erdos_376.variants.prime := by
  intro p q h₁ h₂ h₃ h₄
  exact OMA.E376.final h₁ h₂ h₃ h₄
