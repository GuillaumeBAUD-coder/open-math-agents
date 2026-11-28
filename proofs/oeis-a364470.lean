import OMAStatements.S_oeis_a364470

namespace OMA.S_oeis_a364470



/-! ### Omega -/

lemma Omega_mul {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) : Omega (x * y) = Omega x + Omega y := by
  unfold Omega
  rw [(Nat.perm_primeFactorsList_mul hx hy).length_eq, List.length_append]

lemma Omega_two : Omega 2 = 1 := by decide +kernel

lemma Omega_four : Omega 4 = 2 := by decide +kernel

lemma Omega_four_mul {x : ℕ} (hx : x ≠ 0) : Omega (4 * x) = Omega x + 2 := by
  rw [Omega_mul (by norm_num) hx, Omega_four]
  ring

lemma Omega_two_mul {x : ℕ} (hx : x ≠ 0) : Omega (2 * x) = Omega x + 1 := by
  rw [Omega_mul (by norm_num) hx, Omega_two]
  ring

/-- An odd number has at least 3^Omega(w) as its size. -/
lemma pow_Omega_le_of_odd {w : ℕ} (hw : w % 2 = 1) : 3 ^ Omega w ≤ w := by
  have hw0 : w ≠ 0 := by omega
  unfold Omega
  have hprod := Nat.prod_primeFactorsList hw0
  conv_rhs => rw [← hprod]
  apply List.pow_card_le_prod
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactorsList hp
  have hpd := Nat.dvd_of_mem_primeFactorsList hp
  rcases hpp.eq_two_or_odd with h2 | hodd
  · subst h2
    omega
  · have := hpp.two_le
    omega

/-! ### Good values and the recursion -/

/-- V is the least k > N with Omega(k (N + k)) = n. -/
def Good (n N V : ℕ) : Prop :=
  N < V ∧ Omega (V * (N + V)) = n ∧ ∀ k, k < V → N < k → Omega (k * (N + k)) ≠ n

instance (n N V : ℕ) : Decidable (Good n N V) := by
  unfold Good
  infer_instance

lemma a_of_good {n N V : ℕ} (hn : 1 ≤ n) (hN : a n = N) (hg : Good (n + 1) N V) :
    a (n + 1) = V := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show sInf {k | a (m + 1) < k ∧ Omega (k * (a (m + 1) + k)) = m + 2} = V
  rw [hN]
  obtain ⟨h1, h2, h3⟩ := hg
  have hmem : V ∈ {k | N < k ∧ Omega (k * (N + k)) = m + 2} := ⟨h1, h2⟩
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · apply le_csInf ⟨V, hmem⟩
    rintro k ⟨hk1, hk2⟩
    by_contra hlt
    push_neg at hlt
    exact h3 k hlt hk1 hk2

/-- The scaling step. -/
lemma scale {n N V : ℕ} (hg : Good n N V) (hb : 72 * V ^ 2 < 3 ^ (n + 4)) :
    Good (n + 4) (4 * N) (4 * V) := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hV0 : V ≠ 0 := by omega
  refine ⟨by omega, ?_, ?_⟩
  · rw [show 4 * N + 4 * V = 4 * (N + V) by ring, Omega_mul (by omega) (by omega),
      Omega_four_mul hV0, Omega_four_mul (by omega), ← h2, Omega_mul hV0 (by omega)]
    ring
  · intro k hk1 hk2 hk3
    have hk0 : k ≠ 0 := by omega
    rw [Omega_mul hk0 (by omega)] at hk3
    rcases Nat.lt_or_ge (k % 4) 1 with hm | hm
    · -- k = 4 k0
      obtain ⟨k0, rfl⟩ : ∃ k0, k = 4 * k0 := ⟨k / 4, by omega⟩
      have hk00 : k0 ≠ 0 := by omega
      rw [show 4 * N + 4 * k0 = 4 * (N + k0) by ring, Omega_four_mul hk00,
        Omega_four_mul (by omega)] at hk3
      apply h3 k0 (by omega) (by omega)
      rw [Omega_mul hk00 (by omega)]
      omega
    · rcases Nat.lt_or_ge (k % 2) 1 with hm2 | hm2
      · -- k = 2 u with u odd
        obtain ⟨u, rfl⟩ : ∃ u, k = 2 * u := ⟨k / 2, by omega⟩
        have hu : u % 2 = 1 := by omega
        have hu0 : u ≠ 0 := by omega
        rw [show 4 * N + 2 * u = 2 * (2 * N + u) by ring, Omega_two_mul hu0,
          Omega_two_mul (by omega)] at hk3
        have b1 := pow_Omega_le_of_odd hu
        have b2 := pow_Omega_le_of_odd (show (2 * N + u) % 2 = 1 by omega)
        have hprod : 3 ^ (n + 4) ≤ 9 * (u * (2 * N + u)) := by
          rw [← hk3, show Omega u + 1 + (Omega (2 * N + u) + 1) =
            (Omega u + Omega (2 * N + u)) + 2 by ring, pow_add, pow_add]
          have := Nat.mul_le_mul b1 b2
          nlinarith
        have hu2 : u < 2 * V := by omega
        have hw2 : 2 * N + u < 4 * V := by omega
        have : u * (2 * N + u) < 2 * V * (4 * V) := Nat.mul_lt_mul'' hu2 hw2
        nlinarith
      · -- k odd
        have hko : k % 2 = 1 := by omega
        have b1 := pow_Omega_le_of_odd hko
        have b2 := pow_Omega_le_of_odd (show (4 * N + k) % 2 = 1 by omega)
        have hprod : 3 ^ (n + 4) ≤ k * (4 * N + k) := by
          rw [← hk3, pow_add]
          exact Nat.mul_le_mul b1 b2
        have hw2 : 4 * N + k < 8 * V := by omega
        have : k * (4 * N + k) < 4 * V * (8 * V) := Nat.mul_lt_mul'' hk1 hw2
        nlinarith

/-! ### The first terms -/

lemma a1 : a 1 = 1 := rfl
lemma a2 : a 2 = 2 := a_of_good (n := 1) le_rfl a1 (by decide +kernel)
lemma a3 : a 3 = 7 := a_of_good (n := 2) (by norm_num) a2 (by decide +kernel)
lemma a4 : a 4 = 11 := a_of_good (n := 3) (by norm_num) a3 (by decide +kernel)
lemma a5 : a 5 = 13 := a_of_good (n := 4) (by norm_num) a4 (by decide +kernel)
lemma a6 : a 6 = 19 := a_of_good (n := 5) (by norm_num) a5 (by decide +kernel)
lemma a7 : a 7 = 32 := a_of_good (n := 6) (by norm_num) a6 (by decide +kernel)

lemma g8 : Good 8 32 56 := by decide +kernel
lemma g9 : Good 9 56 80 := by decide +kernel
lemma g10 : Good 10 80 120 := by decide +kernel
lemma g11 : Good 11 120 128 := by decide +kernel

lemma a8 : a 8 = 56 := a_of_good (n := 7) (by norm_num) a7 g8
lemma a9 : a 9 = 80 := a_of_good (n := 8) (by norm_num) a8 g9
lemma a10 : a 10 = 120 := a_of_good (n := 9) (by norm_num) a9 g10
lemma a11 : a 11 = 128 := a_of_good (n := 10) (by norm_num) a10 g11

/-! ### The induction -/

/-- For n >= 8: a(n) is good at level n over a(n-1), 72 a(n)^2 < 3^(n+4), and a(n) = 4 a(n-4)
once n >= 12. -/
lemma chain : ∀ n, 8 ≤ n → Good n (a (n - 1)) (a n) ∧ 72 * a n ^ 2 < 3 ^ (n + 4) ∧
    (12 ≤ n → a n = 4 * a (n - 4)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 12 with hlt | hge
    · interval_cases n
      · refine ⟨by show Good 8 (a 7) (a 8); rw [a7, a8]; exact g8, by rw [a8]; norm_num,
          by omega⟩
      · refine ⟨by show Good 9 (a 8) (a 9); rw [a8, a9]; exact g9, by rw [a9]; norm_num,
          by omega⟩
      · refine ⟨by show Good 10 (a 9) (a 10); rw [a9, a10]; exact g10, by rw [a10]; norm_num,
          by omega⟩
      · refine ⟨by show Good 11 (a 10) (a 11); rw [a10, a11]; exact g11, by rw [a11]; norm_num,
          by omega⟩
    · obtain ⟨g4, b4, -⟩ := ih (n - 4) (by omega) (by omega)
      -- a(n-1) = 4 a(n-5)
      have hprev : a (n - 1) = 4 * a (n - 4 - 1) := by
        rcases Nat.lt_or_ge (n - 1) 12 with h | h
        · have hn12 : n = 12 := by omega
          subst hn12
          show a 11 = 4 * a 7
          rw [a11, a7]
        · have := (ih (n - 1) (by omega) (by omega)).2.2 h
          rw [this, show n - 1 - 4 = n - 4 - 1 by omega]
      have hs := scale g4 b4
      rw [show n - 4 + 4 = n by omega] at hs
      rw [← hprev] at hs
      have hs' : Good (n - 1 + 1) (a (n - 1)) (4 * a (n - 4)) := by
        rwa [show n - 1 + 1 = n by omega]
      have ha : a n = 4 * a (n - 4) := by
        have := a_of_good (n := n - 1) (by omega) rfl hs'
        rwa [show n - 1 + 1 = n by omega] at this
      refine ⟨?_, ?_, fun _ => ha⟩
      · rw [ha]
        exact hs
      · rw [ha]
        have : 3 ^ (n + 4) = 81 * 3 ^ (n - 4 + 4) := by
          rw [show n + 4 = (n - 4 + 4) + 4 by omega, pow_add]
          ring
        rw [this]
        nlinarith

/-- Israel's conjecture: a(n+4) = 4 a(n) for n >= 7. -/
theorem conjecture : ∀ n : ℕ, 7 ≤ n → a (n + 4) = 4 * a n := by
  intro n hn
  rcases Nat.lt_or_ge n 8 with h | h
  · have : n = 7 := by omega
    subst this
    rw [a11, a7]
  · have := (chain (n + 4) (by omega)).2.2 (by omega)
    rwa [show n + 4 - 4 = n by omega] at this

/-! ### Controls from the entry -/

/-- The entry's data a(1..11) = 1, 2, 7, 11, 13, 19, 32, 56, 80, 120, 128. -/
lemma controls : a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 7 ∧ a 4 = 11 ∧ a 5 = 13 ∧ a 6 = 19 ∧ a 7 = 32 ∧
    a 8 = 56 ∧ a 9 = 80 ∧ a 10 = 120 ∧ a 11 = 128 :=
  ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩

end OMA.S_oeis_a364470

theorem OMA.solution : type_of% @OMA.S_oeis_a364470.main :=
  OMA.S_oeis_a364470.conjecture
