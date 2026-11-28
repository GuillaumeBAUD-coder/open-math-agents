import OMAReductions.R_oeis_a400795_R1

-- Step oeis-a400795.R1.H1: hypothesis H1 of reduction oeis-a400795.R1
-- Credit: @Raimo33

open OMA.S_oeis_a400795

theorem OMAStep.S_even (g u v : ℕ) (hc : Nat.Coprime u v) (hu : 0 < u) (hv : 0 < v) :
    Even (g*g*(u*v) + g*(u+v-1)) := by
  have key : ¬ (u % 2 = 0 ∧ v % 2 = 0) := by
    rintro ⟨hi, hj⟩
    have h2 : 2 ∣ Nat.gcd u v := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hi) (Nat.dvd_of_mod_eq_zero hj)
    rw [hc] at h2; omega
  obtain ⟨w, hw⟩ : ∃ w, u + v - 1 = w := ⟨_, rfl⟩
  have hw' : Even w ↔ ¬ (Even u ↔ Even v) := by
    have : u + v = w + 1 := by omega
    have h := congrArg Even this
    rw [Nat.even_add, Nat.even_add_one] at h
    tauto
  have key' : ¬ (Even u ∧ Even v) := by
    rw [Nat.even_iff, Nat.even_iff]; exact key
  rw [hw, Nat.even_add, Nat.even_mul, Nat.even_mul, Nat.even_mul, Nat.even_mul, hw']
  tauto

theorem OMA.solution : OMA.R_oeis_a400795_R1.H1 := by
  intro p a b y hp h3 hm hs hr ha hb ht
  set g := a.gcd b with hg
  have g0 : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  obtain ⟨u, v, huv, hau, hbv⟩ := Nat.exists_coprime a b
  rw [← hg] at hau hbv
  have hu : 0 < u := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_mul] at hau; omega)
  have hv : 0 < v := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_mul] at hbv; omega)
  have hX : a*b + a + b - g = g*g*(u*v) + g*(u+v-1) := by
    have h1 : g ≤ a := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left a b)
    have h2 : g*(u+v-1) + g = g*u + g*v := by
      rw [← Nat.mul_succ, ← Nat.mul_add]; congr 1; omega
    rw [hau, hbv]
    have : u * g * (v * g) + u * g + v * g = g*g*(u*v) + g*(u+v-1) + g := by
      rw [add_assoc (g*g*(u*v)), h2]; ring
    omega
  have hev := OMAStep.S_even g u v huv hu hv
  have hS : g*g*(u*v) + g*(u+v-1) = 2*(2*p-1) := by
    unfold triangleCount at ht; rw [hX] at ht
    obtain ⟨k, hk⟩ := hev; rw [hk] at ht ⊢; omega
  refine ⟨?_, u, v, hu, hv, by rw [← hS]; ring⟩
  by_contra hy
  push Not at hy
  have hgd : g ∣ 2*(2*p-1) := ⟨g*(u*v) + (u+v-1), by rw [← hS]; ring⟩
  rcases Nat.lt_or_ge g 2 with g1 | g2
  · have g1 : g = 1 := by omega
    rw [g1] at hS hau hbv
    simp only [mul_one] at hau hbv
    have e4 : (u+1)*(v+1) = 4*p := by
      have : 2*(2*p-1) + 2 = 4*p := by omega
      rw [← this, ← hS]
      have : u + v - 1 + 1 = u + v := by omega
      nlinarith
    have hpd : p ∣ (u+1)*(v+1) := ⟨4, by rw [e4]; ring⟩
    have hg3 : ∀ x, x + 1 = p → 3 ∣ x := fun x hx => by omega
    rcases (Nat.Prime.dvd_mul hp).1 hpd with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [hk] at e4
      have : k*(v+1) = 4 := Nat.eq_of_mul_eq_mul_left hp.pos (by linarith)
      have hv2 : 2 ≤ v := by omega
      have hk1 : k = 1 := by
        rcases k with _ | _ | k
        · simp at this
        · rfl
        · have := Nat.mul_le_mul (show 2 ≤ k + 1 + 1 by omega) (show 3 ≤ v + 1 by omega)
          omega
      subst hk1
      have hv3 : v = 3 := by omega
      have := Nat.dvd_gcd (show 3 ∣ a by rw [hau]; exact hg3 u (by omega)) (show 3 ∣ b by rw [hbv]; omega)
      rw [← hg, g1] at this; omega
    · rw [hk] at e4
      have : k*(u+1) = 4 := Nat.eq_of_mul_eq_mul_left hp.pos (by linarith)
      have hu2 : 2 ≤ u := by omega
      have hk1 : k = 1 := by
        rcases k with _ | _ | k
        · simp at this
        · rfl
        · have := Nat.mul_le_mul (show 2 ≤ k + 1 + 1 by omega) (show 3 ≤ u + 1 by omega)
          omega
      subst hk1
      have := Nat.dvd_gcd (show 3 ∣ a by rw [hau]; omega) (show 3 ∣ b by rw [hbv]; exact hg3 v (by omega))
      rw [← hg, g1] at this; omega
  · rcases Nat.even_or_odd g with ⟨h, hh⟩ | hodd
    · have hd : h ∣ 2*p-1 := by
        obtain ⟨c, hc⟩ := hgd
        rw [hh, add_mul] at hc
        exact ⟨c, by omega⟩
      have h1 : h = 1 := by
        by_contra hne
        exact hr h (by omega) (by omega) hd
      have g2' : g = 2 := by omega
      rw [g2'] at hS
      have e : (2*u+1)*(2*v+1) = 4*p+1 := by
        have : u + v - 1 + 1 = u + v := by omega
        have : 2*(2*p-1) + 3 = 4*p+1 := by omega
        nlinarith
      have h1 := hs (2*u+1) ⟨2*v+1, e.symm⟩
      have h2 := hs (2*v+1) ⟨2*u+1, by rw [← e]; ring⟩
      have hmod : (2*u+1)*(2*v+1) % 4 = 1 := by
        rw [e]; omega
      have hu2 : u % 2 = 0 := by
        rw [Nat.mul_mod] at hmod
        have : (2*u+1) % 4 = 1 ∨ (2*u+1) % 4 = 3 := by omega
        have : (2*v+1) % 4 = 1 ∨ (2*v+1) % 4 = 3 := by omega
        omega
      have hv2 : v % 2 = 0 := by
        rw [Nat.mul_mod] at hmod
        have : (2*u+1) % 4 = 1 ∨ (2*u+1) % 4 = 3 := by omega
        have : (2*v+1) % 4 = 1 ∨ (2*v+1) % 4 = 3 := by omega
        omega
      have := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hu2) (Nat.dvd_of_mod_eq_zero hv2)
      rw [huv] at this; omega
    · have hc : Nat.Coprime g 2 := Nat.coprime_two_right.2 hodd
      have := hc.dvd_of_dvd_mul_left hgd
      exact hr g (by omega) hy this
