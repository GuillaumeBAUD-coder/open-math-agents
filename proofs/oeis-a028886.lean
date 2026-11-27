import OMAStatements.S_oeis_a028886
import Mathlib.Tactic

-- Problem: Kurkov's primality criterion for OEIS A028886
-- Upstream: statements/oeis-a028886.lean (declaration OMA.S_oeis_a028886.main)
-- Credit: @jared-jasinski (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a028886

lemma choose_two_eq (q : ℕ) : 2 * q.choose 2 = q * (q - 1) := by
  rw [Nat.choose_two_right]
  have h : Even (q * (q - 1)) := Nat.even_mul_pred_self q
  obtain ⟨k, hk⟩ := h
  omega

lemma square_iff_pell (m q s : ℕ) (hm : 2 < m) (hq : 1 ≤ q) :
    q * (m + 1) + q.choose 2 + 1 = s ^ 2 ↔
    ((2 * q + 2 * m + 1 : ℤ) ^ 2 - 8 * (s : ℤ) ^ 2 = ((2 * m + 1) ^ 2 - 8 : ℤ)) := by
  have hc := choose_two_eq q
  have hcz : 2 * (q.choose 2 : ℤ) = (q : ℤ) * ((q : ℤ) - 1) := by
    have : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := Nat.cast_sub hq
    have h2 : (2 * q.choose 2 : ℤ) = (q : ℤ) * ((q - 1 : ℕ) : ℤ) := by exact_mod_cast hc
    rw [this] at h2
    exact h2
  constructor
  · intro h
    have hz : (q : ℤ) * ((m : ℤ) + 1) + (q.choose 2 : ℤ) + 1 = (s : ℤ) ^ 2 := by exact_mod_cast h
    linarith [hcz]
  · intro h
    have hz : (q : ℤ) * ((m : ℤ) + 1) + (q.choose 2 : ℤ) + 1 = (s : ℤ) ^ 2 := by linarith [hcz]
    exact_mod_cast hz

lemma forward_dir (m : ℕ) (hm : 2 < m) (hprime : Nat.Prime ((2 * m + 1) ^ 2 - 8)) :
    ∀ q : ℕ, 1 ≤ q → q ≤ 2 * (m - 2) → ¬ IsSquare (q * (m + 1) + q.choose 2 + 1) := by
  intro q hq1 hq2 ⟨s, hs⟩
  have hsq : q * (m + 1) + q.choose 2 + 1 = s ^ 2 := by rw [sq]; exact hs
  have hpell := (square_iff_pell m q s hm hq1).mp hsq
  set N : ℤ := ((2 * m + 1) ^ 2 - 8 : ℤ)
  set X : ℤ := (2 * q + 2 * m + 1 : ℤ)
  have hN_cast : ((((2 * m + 1) ^ 2 - 8 : ℕ) : ℤ)) = N := by
    have h8 : 8 ≤ (2 * m + 1) ^ 2 := by nlinarith
    rw [Nat.cast_sub h8]; push_cast; rfl
  have hN_prime : Prime N := by
    rw [← hN_cast]
    exact Nat.prime_iff_prime_int.mp hprime
  have hN_pos : 0 < N := by dsimp [N]; nlinarith
  have hX_lo : 2 * (m : ℤ) + 3 ≤ X := by dsimp [X]; omega
  have hX_hi : X ≤ 6 * (m : ℤ) - 7 := by dsimp [X]; omega
  have hs_ge2 : (2 : ℤ) ≤ (s : ℤ) := by
    have h1 : 8 * (s : ℤ) ^ 2 = X ^ 2 - (2 * (m : ℤ) + 1) ^ 2 + 8 := by dsimp [N] at hpell; linarith
    have h2 : (2 * (m : ℤ) + 3) ^ 2 ≤ X ^ 2 := by nlinarith only [hm, hX_lo]
    have hs0 : (0 : ℤ) ≤ (s : ℤ) := Nat.cast_nonneg s
    nlinarith only [hm, h1, h2, hs0]
  have hs_le : (s : ℤ) ≤ 2 * (m : ℤ) - 3 := by
    have h1 : 8 * (s : ℤ) ^ 2 = X ^ 2 - (2 * (m : ℤ) + 1) ^ 2 + 8 := by dsimp [N] at hpell; linarith
    have h2 : X ^ 2 ≤ (6 * (m : ℤ) - 7) ^ 2 := by nlinarith only [hm, hX_lo, hX_hi]
    have hs0 : (0 : ℤ) ≤ (s : ℤ) := Nat.cast_nonneg s
    have hlt : (s : ℤ) < 2 * (m : ℤ) - 2 := by nlinarith only [hm, h1, h2, hs0]
    omega
  have hprod : ((2 * (m : ℤ) + 1) * (s : ℤ) - X) * ((2 * (m : ℤ) + 1) * (s : ℤ) + X) =
      N * ((s : ℤ) ^ 2 - 1) := by
    dsimp [N] at hpell ⊢
    linear_combination -hpell
  have hdvd : N ∣ ((2 * (m : ℤ) + 1) * (s : ℤ) - X) * ((2 * (m : ℤ) + 1) * (s : ℤ) + X) :=
    ⟨(s : ℤ) ^ 2 - 1, hprod⟩
  have hpos_sub : 0 < (2 * (m : ℤ) + 1) * (s : ℤ) - X := by
    have hpos_prod : 0 < ((2 * (m : ℤ) + 1) * (s : ℤ) - X) * ((2 * (m : ℤ) + 1) * (s : ℤ) + X) := by
      rw [hprod]; exact mul_pos hN_pos (by nlinarith only [hs_ge2])
    have hpos_add : 0 < (2 * (m : ℤ) + 1) * (s : ℤ) + X := by nlinarith only [hm, hs_ge2, hX_lo]
    nlinarith only [hpos_prod, hpos_add]
  have hlt_add : (2 * (m : ℤ) + 1) * (s : ℤ) + X < N := by
    dsimp [N]; nlinarith only [hm, hs_le, hX_hi]
  rcases hN_prime.dvd_or_dvd hdvd with h1 | h2
  · have hle := Int.le_of_dvd hpos_sub h1
    linarith
  · have hle := Int.le_of_dvd (by linarith) h2
    linarith

lemma sq_ne_two_mul_sq (u v : ℤ) (huv : u ≠ 0 ∨ v ≠ 0) : u ^ 2 - 2 * v ^ 2 ≠ 0 := by
  intro heq
  have hnat : u.natAbs ^ 2 = 2 * v.natAbs ^ 2 := by
    have : ((u.natAbs ^ 2 : ℕ) : ℤ) = ((2 * v.natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast; rw [sq_abs, sq_abs]; linarith
    exact_mod_cast this
  have hpos : 0 < v.natAbs := by
    rcases huv with hu | hv
    · by_contra h0
      have hv0 : v.natAbs = 0 := by omega
      rw [hv0] at hnat
      have hu0 : u.natAbs = 0 := by nlinarith
      exact hu (Int.natAbs_eq_zero.mp hu0)
    · exact Int.natAbs_pos.mpr hv
  have hirr := irrational_sqrt_two
  have hrat : Real.sqrt 2 = ((u.natAbs : ℚ) / (v.natAbs : ℚ) : ℚ) := by
    push_cast
    have hvR : (0 : ℝ) < (v.natAbs : ℝ) := by exact_mod_cast hpos
    rw [eq_div_iff (ne_of_gt hvR)]
    have hsqR : (Real.sqrt 2 * (v.natAbs : ℝ)) ^ 2 = (u.natAbs : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
      exact_mod_cast hnat.symm
    have h1 : 0 ≤ Real.sqrt 2 * (v.natAbs : ℝ) := by positivity
    have h2 : 0 ≤ (u.natAbs : ℝ) := by positivity
    nlinarith
  exact hirr ⟨(u.natAbs : ℚ) / (v.natAbs : ℚ), hrat.symm⟩

lemma exists_norm_eq_prime (p : ℕ) (hp : p.Prime) (_hp2 : p ≠ 2) (a : ℤ)
    (ha : (p : ℤ) ∣ a ^ 2 - 2) :
    ∃ u v : ℤ, u ^ 2 - 2 * v ^ 2 = (p : ℤ) := by
  let k : ℕ := Nat.sqrt p
  have hk_gt : p < (k + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt p
    nlinarith
  have hk_le : k ^ 2 ≤ p := by rw [sq]; exact Nat.sqrt_le p
  let S : Finset (Fin (k + 1) × Fin (k + 1)) := Finset.univ
  let f : Fin (k + 1) × Fin (k + 1) → Fin p := fun xy =>
    ⟨(((xy.1.val : ℤ) - a * (xy.2.val : ℤ)) % (p : ℤ)).toNat, by
      have hp_pos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
      have hlt := Int.emod_lt_of_pos ((xy.1.val : ℤ) - a * (xy.2.val : ℤ)) hp_pos
      have hnn := Int.emod_nonneg ((xy.1.val : ℤ) - a * (xy.2.val : ℤ)) (ne_of_gt hp_pos)
      omega⟩
  have hcard : Fintype.card (Fin p) < S.card := by
    simp only [S, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, ← sq]
    exact hk_gt
  obtain ⟨xy1, _, xy2, _, hne, hfeq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := S) (t := (Finset.univ : Finset (Fin p))) (f := f) (by simpa using hcard) (fun _ _ => Finset.mem_univ _)
  let u : ℤ := (xy1.1.val : ℤ) - (xy2.1.val : ℤ)
  let v : ℤ := (xy1.2.val : ℤ) - (xy2.2.val : ℤ)
  have huv_ne : u ≠ 0 ∨ v ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    ext <;> dsimp [u, v] at h <;> omega
  have hmod_eq : ((xy1.1.val : ℤ) - a * (xy1.2.val : ℤ)) % (p : ℤ) =
      ((xy2.1.val : ℤ) - a * (xy2.2.val : ℤ)) % (p : ℤ) := by
    have hv := congrArg Fin.val hfeq
    dsimp [f] at hv
    have hp_pos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
    have hnn1 := Int.emod_nonneg ((xy1.1.val : ℤ) - a * (xy1.2.val : ℤ)) (ne_of_gt hp_pos)
    have hnn2 := Int.emod_nonneg ((xy2.1.val : ℤ) - a * (xy2.2.val : ℤ)) (ne_of_gt hp_pos)
    omega
  have hdvd_lin : (p : ℤ) ∣ u - a * v := by
    have h1 : u - a * v = ((xy1.1.val : ℤ) - a * (xy1.2.val : ℤ)) -
        ((xy2.1.val : ℤ) - a * (xy2.2.val : ℤ)) := by dsimp [u, v]; ring
    rw [h1]
    exact Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, hmod_eq, sub_self, Int.zero_emod])
  have hdvd_norm : (p : ℤ) ∣ u ^ 2 - 2 * v ^ 2 := by
    have hid : u ^ 2 - 2 * v ^ 2 = (u - a * v) * (u + a * v) + v ^ 2 * (a ^ 2 - 2) := by ring
    rw [hid]
    exact dvd_add (dvd_mul_of_dvd_left hdvd_lin _) (dvd_mul_of_dvd_right ha _)
  have hu_le : u ^ 2 < (p : ℤ) := by
    have h1 : |u| ≤ (k : ℤ) := by
      dsimp [u]; rw [abs_le]; constructor <;> omega
    have h2 : u ^ 2 ≤ (k : ℤ) ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
    have h3 : (k : ℤ) ^ 2 ≤ (p : ℤ) := by exact_mod_cast hk_le
    have hne_sq : (k : ℤ) ^ 2 ≠ (p : ℤ) := by
      intro heq
      have heqN : k ^ 2 = p := by exact_mod_cast heq
      have hkdvd : k ∣ p := ⟨k, by linarith [sq k]⟩
      rcases hp.eq_one_or_self_of_dvd k hkdvd with hk1 | hkp
      · rw [hk1] at heqN; exact hp.ne_one heqN.symm
      · rw [hkp] at heqN; nlinarith [hp.two_le]
    omega
  have hv_le : v ^ 2 < (p : ℤ) := by
    have h1 : |v| ≤ (k : ℤ) := by
      dsimp [v]; rw [abs_le]; constructor <;> omega
    have h2 : v ^ 2 ≤ (k : ℤ) ^ 2 := by nlinarith [sq_abs v, abs_nonneg v]
    have h3 : (k : ℤ) ^ 2 ≤ (p : ℤ) := by exact_mod_cast hk_le
    have hne_sq : (k : ℤ) ^ 2 ≠ (p : ℤ) := by
      intro heq
      have heqN : k ^ 2 = p := by exact_mod_cast heq
      have hkdvd : k ∣ p := ⟨k, by linarith [sq k]⟩
      rcases hp.eq_one_or_self_of_dvd k hkdvd with hk1 | hkp
      · rw [hk1] at heqN; exact hp.ne_one heqN.symm
      · rw [hkp] at heqN; nlinarith [hp.two_le]
    omega
  have hnz : u ^ 2 - 2 * v ^ 2 ≠ 0 := sq_ne_two_mul_sq u v huv_ne
  obtain ⟨t, ht⟩ := hdvd_norm
  have ht_eq : t = -1 := by
    have hp_pos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
    have h1 : -2 < t := by nlinarith [sq_nonneg u]
    have h2 : t < 1 := by nlinarith [sq_nonneg v]
    have h3 : t ≠ 0 := by intro h0; rw [h0, mul_zero] at ht; exact hnz ht
    omega
  exact ⟨u + 2 * v, u + v, by rw [ht_eq] at ht; linarith⟩

/-- Invariant asserting `(X, Y)` is not an associate of `(2m+1, ±2)` modulo `(3 ± 2√2)`. -/
def nonAssoc (m : ℕ) (X Y : ℤ) : Prop :=
  let N : ℤ := (2 * (m : ℤ) + 1) ^ 2 - 8
  (¬ (N ∣ X * (2 * (m : ℤ) + 1) - 4 * Y ∧ N ∣ 2 * X - (2 * (m : ℤ) + 1) * Y)) ∧
  (¬ (N ∣ X * (2 * (m : ℤ) + 1) + 4 * Y ∧ N ∣ 2 * X + (2 * (m : ℤ) + 1) * Y))

lemma nonAssoc_neg {m : ℕ} {X Y : ℤ} (h : nonAssoc m X Y) : nonAssoc m (-X) (-Y) := by
  dsimp [nonAssoc] at h ⊢
  constructor
  · rintro ⟨h1, h2⟩
    apply h.1
    rw [show -X * (2 * (m : ℤ) + 1) - 4 * -Y = -(X * (2 * (m : ℤ) + 1) - 4 * Y) by ring] at h1
    rw [show 2 * -X - (2 * (m : ℤ) + 1) * -Y = -(2 * X - (2 * (m : ℤ) + 1) * Y) by ring] at h2
    exact ⟨dvd_neg.mp h1, dvd_neg.mp h2⟩
  · rintro ⟨h1, h2⟩
    apply h.2
    rw [show -X * (2 * (m : ℤ) + 1) + 4 * -Y = -(X * (2 * (m : ℤ) + 1) + 4 * Y) by ring] at h1
    rw [show 2 * -X + (2 * (m : ℤ) + 1) * -Y = -(2 * X + (2 * (m : ℤ) + 1) * Y) by ring] at h2
    exact ⟨dvd_neg.mp h1, dvd_neg.mp h2⟩

lemma nonAssoc_conj {m : ℕ} {X Y : ℤ} (h : nonAssoc m X Y) : nonAssoc m X (-Y) := by
  dsimp [nonAssoc] at h ⊢
  constructor
  · rintro ⟨h1, h2⟩
    apply h.2
    rw [show X * (2 * (m : ℤ) + 1) - 4 * -Y = X * (2 * (m : ℤ) + 1) + 4 * Y by ring] at h1
    rw [show 2 * X - (2 * (m : ℤ) + 1) * -Y = 2 * X + (2 * (m : ℤ) + 1) * Y by ring] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    apply h.1
    rw [show X * (2 * (m : ℤ) + 1) + 4 * -Y = X * (2 * (m : ℤ) + 1) - 4 * Y by ring] at h1
    rw [show 2 * X + (2 * (m : ℤ) + 1) * -Y = 2 * X - (2 * (m : ℤ) + 1) * Y by ring] at h2
    exact ⟨h1, h2⟩

lemma nonAssoc_descent {m : ℕ} {X Y : ℤ} (h : nonAssoc m X Y) :
    nonAssoc m (3 * X - 4 * Y) (-2 * X + 3 * Y) := by
  dsimp [nonAssoc] at h ⊢
  set N : ℤ := (2 * (m : ℤ) + 1) ^ 2 - 8
  constructor
  · rintro ⟨h1, h2⟩
    apply h.1
    have e1 : X * (2 * (m : ℤ) + 1) - 4 * Y =
        3 * ((3 * X - 4 * Y) * (2 * (m : ℤ) + 1) - 4 * (-2 * X + 3 * Y)) -
        4 * (2 * (3 * X - 4 * Y) - (2 * (m : ℤ) + 1) * (-2 * X + 3 * Y)) := by ring
    have e2 : 2 * X - (2 * (m : ℤ) + 1) * Y =
        -2 * ((3 * X - 4 * Y) * (2 * (m : ℤ) + 1) - 4 * (-2 * X + 3 * Y)) +
        3 * (2 * (3 * X - 4 * Y) - (2 * (m : ℤ) + 1) * (-2 * X + 3 * Y)) := by ring
    exact ⟨e1 ▸ dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _),
           e2 ▸ dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _)⟩
  · rintro ⟨h1, h2⟩
    apply h.2
    have e1 : X * (2 * (m : ℤ) + 1) + 4 * Y =
        3 * ((3 * X - 4 * Y) * (2 * (m : ℤ) + 1) + 4 * (-2 * X + 3 * Y)) +
        4 * (2 * (3 * X - 4 * Y) + (2 * (m : ℤ) + 1) * (-2 * X + 3 * Y)) := by ring
    have e2 : 2 * X + (2 * (m : ℤ) + 1) * Y =
        2 * ((3 * X - 4 * Y) * (2 * (m : ℤ) + 1) + 4 * (-2 * X + 3 * Y)) +
        3 * (2 * (3 * X - 4 * Y) + (2 * (m : ℤ) + 1) * (-2 * X + 3 * Y)) := by ring
    exact ⟨e1 ▸ dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _),
           e2 ▸ dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _)⟩

lemma exists_nonAssoc_of_not_prime (m : ℕ) (hm : 2 < m)
    (hnot : ¬ Nat.Prime ((2 * m + 1) ^ 2 - 8)) :
    ∃ X Y : ℤ, X ^ 2 - 2 * Y ^ 2 = (2 * (m : ℤ) + 1) ^ 2 - 8 ∧ nonAssoc m X Y := by
  set Nnat : ℕ := (2 * m + 1) ^ 2 - 8
  have hNnat_ge : 41 ≤ Nnat := by
    dsimp [Nnat]
    have : 49 ≤ (2 * m + 1) ^ 2 := by nlinarith
    omega
  have hN_cast : (Nnat : ℤ) = (2 * (m : ℤ) + 1) ^ 2 - 8 := by
    dsimp [Nnat]
    have h8 : 8 ≤ (2 * m + 1) ^ 2 := by nlinarith
    rw [Nat.cast_sub h8]; push_cast; rfl
  let p : ℕ := Nnat.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpdvd : p ∣ Nnat := Nat.minFac_dvd Nnat
  have hp2 : p ≠ 2 := by
    intro h2
    rw [h2] at hpdvd
    have hNodd : Nnat % 2 = 1 := by
      dsimp [Nnat]
      have : (2 * m + 1) ^ 2 = 4 * m ^ 2 + 4 * m + 1 := by ring
      omega
    omega
  set c : ℕ := Nnat / p
  have hpc : p * c = Nnat := Nat.mul_div_cancel' hpdvd
  have hc_gt1 : 1 < c := by
    by_contra hle
    have hc1 : c = 1 := by
      have hpos : 0 < c := by
        by_contra h0
        have hc0 : c = 0 := Nat.eq_zero_of_not_pos h0
        rw [hc0, mul_zero] at hpc
        linarith
      linarith
    rw [hc1, mul_one] at hpc
    exact hnot (hpc ▸ hp)
  have hNodd : Nnat % 2 = 1 := by
    dsimp [Nnat]
    have : (2 * m + 1) ^ 2 = 4 * m ^ 2 + 4 * m + 1 := by ring
    omega
  have hcodd : c % 2 = 1 := by
    by_contra h
    have hc0 : c % 2 = 0 := by omega
    have hpc0 : (p * c) % 2 = 0 := by rw [Nat.mul_mod, hc0]; simp
    rw [hpc] at hpc0
    omega
  -- Find a with p ∣ a^2 - 2 (since (2m+1)^2 ≡ 8 = 4*2 mod p, take a = (2m+1) * (p+1)/2)
  have hp_odd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · exact absurd h2 hp2
    · exact hodd
  let inv2 : ℤ := ((p + 1) / 2 : ℕ)
  have h2inv : (p : ℤ) ∣ 2 * inv2 - 1 := by
    refine ⟨1, ?_⟩
    dsimp [inv2]; omega
  let a : ℤ := (2 * (m : ℤ) + 1) * inv2
  have ha : (p : ℤ) ∣ a ^ 2 - 2 := by
    have hpdvdZ : (p : ℤ) ∣ (2 * (m : ℤ) + 1) ^ 2 - 8 := by
      rw [← hN_cast]; exact_mod_cast hpdvd
    have hid : 4 * (a ^ 2 - 2) =
        ((2 * (m : ℤ) + 1) ^ 2 - 8) * (2 * inv2) ^ 2 +
        8 * (2 * inv2 - 1) * (2 * inv2 + 1) := by dsimp [a]; ring
    have h4 : (p : ℤ) ∣ 4 * (a ^ 2 - 2) := by
      rw [hid]
      exact dvd_add (dvd_mul_of_dvd_left hpdvdZ _)
        (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h2inv _) _)
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpZ.dvd_or_dvd h4 with h4p | hap
    · have hp4 : p ∣ 4 := by exact_mod_cast h4p
      have hle4 := Nat.le_of_dvd (by decide) hp4
      have h2le := hp.two_le
      interval_cases p <;> omega
    · exact hap
  obtain ⟨u, v0, huv0⟩ := exists_norm_eq_prime p hp hp2 a ha
  -- Choose sign of v so that p ∣ 2*u - (2m+1)*v
  have hprod_p : (p : ℤ) ∣ (2 * u - (2 * (m : ℤ) + 1) * v0) * (2 * u + (2 * (m : ℤ) + 1) * v0) := by
    have hid : (2 * u - (2 * (m : ℤ) + 1) * v0) * (2 * u + (2 * (m : ℤ) + 1) * v0) =
        4 * (u ^ 2 - 2 * v0 ^ 2) - ((2 * (m : ℤ) + 1) ^ 2 - 8) * v0 ^ 2 := by ring
    rw [hid, huv0, ← hN_cast]
    have hpdvdZ : (p : ℤ) ∣ (Nnat : ℤ) := by exact_mod_cast hpdvd
    exact dvd_sub (dvd_mul_of_dvd_right (dvd_refl _) _) (dvd_mul_of_dvd_left hpdvdZ _)
  have hv_exists : ∃ v : ℤ, u ^ 2 - 2 * v ^ 2 = (p : ℤ) ∧ (p : ℤ) ∣ 2 * u - (2 * (m : ℤ) + 1) * v := by
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpZ.dvd_or_dvd hprod_p with h1 | h2
    · exact ⟨v0, huv0, h1⟩
    · exact ⟨-v0, by linarith, by simpa [show 2 * u - (2 * (m : ℤ) + 1) * -v0 = 2 * u + (2 * (m : ℤ) + 1) * v0 by ring] using h2⟩
  obtain ⟨v, huv, hB_dvd⟩ := hv_exists
  obtain ⟨B0, hB0⟩ := hB_dvd
  have hA_sq_dvd : (p : ℤ) ^ 2 ∣ ((2 * (m : ℤ) + 1) * u - 4 * v) ^ 2 := by
    have hid : ((2 * (m : ℤ) + 1) * u - 4 * v) ^ 2 - 2 * (2 * u - (2 * (m : ℤ) + 1) * v) ^ 2 =
        ((2 * (m : ℤ) + 1) ^ 2 - 8) * (u ^ 2 - 2 * v ^ 2) := by ring
    rw [huv, ← hN_cast, ← hpc] at hid
    have h1 : ((2 * (m : ℤ) + 1) * u - 4 * v) ^ 2 =
        (p : ℤ) ^ 2 * ((c : ℤ) + 2 * B0 ^ 2) := by
      push_cast at hid
      rw [hB0] at hid
      linarith
    exact ⟨(c : ℤ) + 2 * B0 ^ 2, h1⟩
  have hA_dvd : (p : ℤ) ∣ (2 * (m : ℤ) + 1) * u - 4 * v := by
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have h1 : (p : ℤ) ∣ ((2 * (m : ℤ) + 1) * u - 4 * v) * ((2 * (m : ℤ) + 1) * u - 4 * v) := by
      rw [← sq]; exact dvd_trans (dvd_pow_self _ (by decide)) hA_sq_dvd
    rcases hpZ.dvd_or_dvd h1 with h | h <;> exact h
  obtain ⟨A0, hA0⟩ := hA_dvd
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hAB_norm : A0 ^ 2 - 2 * B0 ^ 2 = (c : ℤ) := by
    have hid : ((2 * (m : ℤ) + 1) * u - 4 * v) ^ 2 - 2 * (2 * u - (2 * (m : ℤ) + 1) * v) ^ 2 =
        ((2 * (m : ℤ) + 1) ^ 2 - 8) * (u ^ 2 - 2 * v ^ 2) := by ring
    rw [hA0, hB0, huv, ← hN_cast, ← hpc] at hid
    push_cast at hid
    have : (p : ℤ) ^ 2 * (A0 ^ 2 - 2 * B0 ^ 2) = (p : ℤ) ^ 2 * (c : ℤ) := by linarith
    exact mul_left_cancel₀ (pow_ne_zero 2 hp_ne) this
  have halpha1 : A0 * u + 2 * B0 * v = 2 * (m : ℤ) + 1 := by
    have : (p : ℤ) * (A0 * u + 2 * B0 * v) = (p : ℤ) * (2 * (m : ℤ) + 1) := by
      calc (p : ℤ) * (A0 * u + 2 * B0 * v)
          = ((p : ℤ) * A0) * u + 2 * ((p : ℤ) * B0) * v := by ring
        _ = ((2 * (m : ℤ) + 1) * u - 4 * v) * u + 2 * (2 * u - (2 * (m : ℤ) + 1) * v) * v := by rw [← hA0, ← hB0]
        _ = (u ^ 2 - 2 * v ^ 2) * (2 * (m : ℤ) + 1) := by ring
        _ = (p : ℤ) * (2 * (m : ℤ) + 1) := by rw [huv]
    exact mul_left_cancel₀ hp_ne this
  have halpha2 : B0 * u + A0 * v = 2 := by
    have : (p : ℤ) * (B0 * u + A0 * v) = (p : ℤ) * 2 := by
      calc (p : ℤ) * (B0 * u + A0 * v)
          = ((p : ℤ) * B0) * u + ((p : ℤ) * A0) * v := by ring
        _ = (2 * u - (2 * (m : ℤ) + 1) * v) * u + ((2 * (m : ℤ) + 1) * u - 4 * v) * v := by rw [← hA0, ← hB0]
        _ = (u ^ 2 - 2 * v ^ 2) * 2 := by ring
        _ = (p : ℤ) * 2 := by rw [huv]
    exact mul_left_cancel₀ hp_ne this
  -- Define β = (A0 + B0 √2)(u - v √2)
  let X0 : ℤ := A0 * u - 2 * B0 * v
  let Y0 : ℤ := B0 * u - A0 * v
  refine ⟨X0, Y0, ?_, ?_⟩
  · calc X0 ^ 2 - 2 * Y0 ^ 2 = (A0 ^ 2 - 2 * B0 ^ 2) * (u ^ 2 - 2 * v ^ 2) := by dsimp [X0, Y0]; ring
      _ = (c : ℤ) * (p : ℤ) := by rw [hAB_norm, huv]
      _ = (Nnat : ℤ) := by rw [← hpc]; push_cast; ring
      _ = (2 * (m : ℤ) + 1) ^ 2 - 8 := hN_cast
  · dsimp [nonAssoc]
    have hN_eq : (2 * (m : ℤ) + 1) ^ 2 - 8 = (p : ℤ) * (c : ℤ) := by
      rw [← hN_cast, ← hpc]; push_cast; rfl
    rw [hN_eq]
    have hc_ne : (c : ℤ) ≠ 0 := by omega
    constructor
    · -- Rule out (p * c) dividing both X0*(2m+1) - 4*Y0 and 2*X0 - (2m+1)*Y0
      rintro ⟨h1, _⟩
      have hid1 : X0 * (2 * (m : ℤ) + 1) - 4 * Y0 = (c : ℤ) * (u ^ 2 + 2 * v ^ 2) := by
        rw [← halpha1, ← hAB_norm]
        have : 2 = B0 * u + A0 * v := halpha2.symm
        dsimp [X0, Y0]
        calc (A0 * u - 2 * B0 * v) * (A0 * u + 2 * B0 * v) - 2 * 2 * (B0 * u - A0 * v)
            = (A0 * u - 2 * B0 * v) * (A0 * u + 2 * B0 * v) - 2 * (B0 * u + A0 * v) * (B0 * u - A0 * v) := by
              rw [← halpha2]
          _ = (A0 ^ 2 - 2 * B0 ^ 2) * (u ^ 2 + 2 * v ^ 2) := by ring
      rw [hid1] at h1
      have hp_dvd_sum : (p : ℤ) ∣ u ^ 2 + 2 * v ^ 2 := by
        obtain ⟨k, hk⟩ := h1
        exact ⟨k, mul_left_cancel₀ hc_ne (by linarith)⟩
      have hp_dvd_2u2 : (p : ℤ) ∣ 2 * u ^ 2 := by
        have : 2 * u ^ 2 = (u ^ 2 + 2 * v ^ 2) + (u ^ 2 - 2 * v ^ 2) := by ring
        rw [this, huv]; exact dvd_add hp_dvd_sum (dvd_refl _)
      have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      have hp_dvd_u : (p : ℤ) ∣ u := by
        rcases hpZ.dvd_or_dvd hp_dvd_2u2 with h2p | hu2
        · have : p ∣ 2 := by exact_mod_cast h2p
          have := Nat.le_of_dvd (by decide) this; have := hp.two_le; omega
        · rw [sq] at hu2; rcases hpZ.dvd_or_dvd hu2 with h | h <;> exact h
      have hp_dvd_2v2 : (p : ℤ) ∣ 2 * v ^ 2 := by
        have : 2 * v ^ 2 = u ^ 2 - (u ^ 2 - 2 * v ^ 2) := by ring
        rw [this, huv]; exact dvd_sub (dvd_pow hp_dvd_u (by decide)) (dvd_refl _)
      have hp_dvd_v : (p : ℤ) ∣ v := by
        rcases hpZ.dvd_or_dvd hp_dvd_2v2 with h2p | hv2
        · have : p ∣ 2 := by exact_mod_cast h2p
          have := Nat.le_of_dvd (by decide) this; have := hp.two_le; omega
        · rw [sq] at hv2; rcases hpZ.dvd_or_dvd hv2 with h | h <;> exact h
      obtain ⟨u1, hu1⟩ := hp_dvd_u
      obtain ⟨v1, hv1⟩ := hp_dvd_v
      have hp2_dvd : (p : ℤ) ^ 2 ∣ (p : ℤ) := by
        refine ⟨u1 ^ 2 - 2 * v1 ^ 2, ?_⟩
        calc (p : ℤ) = u ^ 2 - 2 * v ^ 2 := huv.symm
          _ = (p : ℤ) ^ 2 * (u1 ^ 2 - 2 * v1 ^ 2) := by rw [hu1, hv1]; ring
      have : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos (by exact_mod_cast hp2_dvd)
      nlinarith [hp.two_le]
    · -- Rule out (p * c) dividing both X0*(2m+1) + 4*Y0 and 2*X0 + (2m+1)*Y0
      rintro ⟨h1, _⟩
      have hid2 : X0 * (2 * (m : ℤ) + 1) + 4 * Y0 = (p : ℤ) * (A0 ^ 2 + 2 * B0 ^ 2) := by
        rw [← halpha1, ← huv]
        dsimp [X0, Y0]
        calc (A0 * u - 2 * B0 * v) * (A0 * u + 2 * B0 * v) + 2 * 2 * (B0 * u - A0 * v)
            = (A0 * u - 2 * B0 * v) * (A0 * u + 2 * B0 * v) + 2 * (B0 * u + A0 * v) * (B0 * u - A0 * v) := by
              rw [← halpha2]
          _ = (u ^ 2 - 2 * v ^ 2) * (A0 ^ 2 + 2 * B0 ^ 2) := by ring
      rw [hid2] at h1
      have hc_dvd_sum : (c : ℤ) ∣ A0 ^ 2 + 2 * B0 ^ 2 := by
        obtain ⟨k, hk⟩ := h1
        exact ⟨k, mul_left_cancel₀ hp_ne (by linarith)⟩
      let q : ℕ := c.minFac
      have hq : q.Prime := Nat.minFac_prime (by omega)
      have hqc : q ∣ c := Nat.minFac_dvd c
      have hq2 : q ≠ 2 := by
        intro h2; rw [h2] at hqc; omega
      have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
      have hqcZ : (q : ℤ) ∣ (c : ℤ) := by exact_mod_cast hqc
      have hq_sum : (q : ℤ) ∣ A0 ^ 2 + 2 * B0 ^ 2 := dvd_trans hqcZ hc_dvd_sum
      have hq_2A2 : (q : ℤ) ∣ 2 * A0 ^ 2 := by
        have : 2 * A0 ^ 2 = (A0 ^ 2 + 2 * B0 ^ 2) + (A0 ^ 2 - 2 * B0 ^ 2) := by ring
        rw [this, hAB_norm]; exact dvd_add hq_sum hqcZ
      have hq_A0 : (q : ℤ) ∣ A0 := by
        rcases hqZ.dvd_or_dvd hq_2A2 with h2q | hA2
        · have : q ∣ 2 := by exact_mod_cast h2q
          have := Nat.le_of_dvd (by decide) this; have := hq.two_le; omega
        · rw [sq] at hA2; rcases hqZ.dvd_or_dvd hA2 with h | h <;> exact h
      have hq_2B2 : (q : ℤ) ∣ 2 * B0 ^ 2 := by
        have : 2 * B0 ^ 2 = A0 ^ 2 - (A0 ^ 2 - 2 * B0 ^ 2) := by ring
        rw [this, hAB_norm]; exact dvd_sub (dvd_pow hq_A0 (by decide)) hqcZ
      have hq_B0 : (q : ℤ) ∣ B0 := by
        rcases hqZ.dvd_or_dvd hq_2B2 with h2q | hB2
        · have : q ∣ 2 := by exact_mod_cast h2q
          have := Nat.le_of_dvd (by decide) this; have := hq.two_le; omega
        · rw [sq] at hB2; rcases hqZ.dvd_or_dvd hB2 with h | h <;> exact h
      have hq_dvd_2 : (q : ℤ) ∣ 2 := by
        rw [← halpha2]
        exact dvd_add (dvd_mul_of_dvd_left hq_B0 _) (dvd_mul_of_dvd_left hq_A0 _)
      have : q ∣ 2 := by exact_mod_cast hq_dvd_2
      have := Nat.le_of_dvd (by decide) this
      have := hq.two_le
      omega

lemma backward_dir (m : ℕ) (hm : 2 < m)
    (hno : ∀ q : ℕ, 1 ≤ q → q ≤ 2 * (m - 2) → ¬ IsSquare (q * (m + 1) + q.choose 2 + 1)) :
    Nat.Prime ((2 * m + 1) ^ 2 - 8) := by
  by_contra hnot
  set N : ℤ := (2 * (m : ℤ) + 1) ^ 2 - 8
  have hN_pos : 0 < N := by dsimp [N]; nlinarith
  have hex : ∃ k : ℕ, ∃ X Y : ℤ, X.natAbs = k ∧ X ^ 2 - 2 * Y ^ 2 = N ∧ nonAssoc m X Y := by
    obtain ⟨X0, Y0, h1, h2⟩ := exists_nonAssoc_of_not_prime m hm hnot
    exact ⟨X0.natAbs, X0, Y0, rfl, h1, h2⟩
  classical
  let k0 := Nat.find hex
  obtain ⟨X1, Y1, hX1_abs, hX1_pell, hX1_na⟩ := Nat.find_spec hex
  have hmin : ∀ X' Y' : ℤ, X' ^ 2 - 2 * Y' ^ 2 = N → nonAssoc m X' Y' → X1.natAbs ≤ X'.natAbs := by
    intro X' Y' hp hna
    rw [hX1_abs]
    exact Nat.find_min' hex ⟨X', Y', rfl, hp, hna⟩
  -- Normalize to X > 0 and Y ≥ 0
  have hnorm : ∃ X Y : ℤ, 0 < X ∧ 0 ≤ Y ∧ X.natAbs = X1.natAbs ∧ X ^ 2 - 2 * Y ^ 2 = N ∧ nonAssoc m X Y := by
    have hX1_ne : X1 ≠ 0 := by intro h0; rw [h0] at hX1_pell; nlinarith
    have h1 : ∃ X Y : ℤ, 0 < X ∧ X.natAbs = X1.natAbs ∧ X ^ 2 - 2 * Y ^ 2 = N ∧ nonAssoc m X Y := by
      rcases lt_or_gt_of_ne hX1_ne with hlt | hgt
      · exact ⟨-X1, -Y1, by omega, by simp, by linarith, nonAssoc_neg hX1_na⟩
      · exact ⟨X1, Y1, hgt, rfl, hX1_pell, hX1_na⟩
    obtain ⟨Xa, Ya, hXa, hXa_abs, hXa_pell, hXa_na⟩ := h1
    rcases le_or_gt 0 Ya with hge | hlt
    · exact ⟨Xa, Ya, hXa, hge, hXa_abs, hXa_pell, hXa_na⟩
    · exact ⟨Xa, -Ya, hXa, by omega, hXa_abs, by linarith, nonAssoc_conj hXa_na⟩
  obtain ⟨X, Y, hXpos, hYnn, hXabs, hXpell, hXna⟩ := hnorm
  -- Prove X^2 ≤ 2 * N by minimality
  have hX2_le : X ^ 2 ≤ 2 * N := by
    by_contra hgt
    push Not at hgt
    let X' := 3 * X - 4 * Y
    let Y' := -2 * X + 3 * Y
    have hX'_pell : X' ^ 2 - 2 * Y' ^ 2 = N := by dsimp [X', Y']; linarith
    have hX'_na : nonAssoc m X' Y' := nonAssoc_descent hXna
    have hX'_lt : |X'| < X := by
      dsimp [X']
      rw [abs_lt]
      constructor <;> nlinarith
    have hle := hmin X' Y' hX'_pell hX'_na
    rw [← hXabs] at hle
    have : (X.natAbs : ℤ) ≤ (X'.natAbs : ℤ) := by exact_mod_cast hle
    have h1 : (X.natAbs : ℤ) = X := Int.natAbs_of_nonneg (le_of_lt hXpos)
    have h2 : (X'.natAbs : ℤ) = |X'| := by simp
    linarith
  -- Parity: X is odd and Y is even
  have hXodd : X % 2 = 1 := by
    have hNmod : N % 2 = 1 := by
      dsimp [N]
      have : (2 * (m : ℤ) + 1) ^ 2 = 4 * (m : ℤ) ^ 2 + 4 * (m : ℤ) + 1 := by ring
      omega
    have hX2mod : X ^ 2 % 2 = 1 := by omega
    have : X % 2 = 0 ∨ X % 2 = 1 := by omega
    rcases this with h0 | h1
    · have : X = 2 * (X / 2) := by omega
      rw [this] at hX2mod; ring_nf at hX2mod; omega
    · exact h1
  have hYeven : Y % 2 = 0 := by
    have hX2mod8 : X ^ 2 % 8 = 1 := by
      set qx := X / 2
      have hx : X = 2 * qx + 1 := by omega
      have hsq : X ^ 2 = 4 * (qx * (qx + 1)) + 1 := by rw [hx]; ring
      have hev : (qx * (qx + 1)) % 2 = 0 := by
        set r := qx / 2
        have : qx = 2 * r ∨ qx = 2 * r + 1 := by omega
        rcases this with h | h <;> rw [h] <;> ring_nf <;> omega
      omega
    have hNmod8 : N % 8 = 1 := by
      dsimp [N]
      have : (2 * (m : ℤ) + 1) ^ 2 - 8 = 4 * ((m : ℤ) * ((m : ℤ) + 1)) - 7 := by ring
      have hev : ((m : ℤ) * ((m : ℤ) + 1)) % 2 = 0 := by
        set r := (m : ℤ) / 2
        have : (m : ℤ) = 2 * r ∨ (m : ℤ) = 2 * r + 1 := by omega
        rcases this with h | h <;> rw [h] <;> ring_nf <;> omega
      omega
    have h2Y2 : (2 * Y ^ 2) % 8 = 0 := by omega
    have : Y % 2 = 0 ∨ Y % 2 = 1 := by omega
    rcases this with h0 | h1
    · exact h0
    · set qy := Y / 2
      have hy : Y = 2 * qy + 1 := by omega
      rw [hy] at h2Y2; ring_nf at h2Y2; omega
  let s : ℕ := (Y / 2).toNat
  have hYs : Y = 2 * (s : ℤ) := by dsimp [s]; omega
  -- Rule out s = 0 and s = 1
  have hs_ne0 : s ≠ 0 := by
    intro h0; rw [h0] at hYs; simp at hYs; rw [hYs] at hXpell
    dsimp [N] at hXpell
    have h1 : (2 * (m : ℤ)) ^ 2 < X ^ 2 := by nlinarith
    have h2 : X ^ 2 < (2 * (m : ℤ) + 1) ^ 2 := by nlinarith
    have h3 : 2 * (m : ℤ) < X := by nlinarith
    have h4 : X < 2 * (m : ℤ) + 1 := by nlinarith
    omega
  have hs_ne1 : s ≠ 1 := by
    intro h1; rw [h1] at hYs; norm_num at hYs; rw [hYs] at hXpell
    have hXeq : X = 2 * (m : ℤ) + 1 := by dsimp [N] at hXpell; nlinarith
    apply hXna.1
    rw [hXeq, hYs]
    exact ⟨⟨1, by ring⟩, ⟨0, by ring⟩⟩
  have hs_ge2 : 2 ≤ s := by omega
  have hX_lo : 2 * (m : ℤ) + 3 ≤ X := by
    have h1 : (2 * (m : ℤ) + 1) ^ 2 < X ^ 2 := by
      rw [hYs] at hXpell; dsimp [N] at hXpell
      have hsZ : (2 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs_ge2
      nlinarith
    have h2 : 2 * (m : ℤ) + 1 < X := by nlinarith
    omega
  have hX_hi : X ≤ 6 * (m : ℤ) - 7 := by
    have h1 : 2 * N < (6 * (m : ℤ) - 7) ^ 2 := by dsimp [N]; nlinarith
    have h2 : X ^ 2 < (6 * (m : ℤ) - 7) ^ 2 := by linarith
    nlinarith
  let q : ℕ := ((X - (2 * (m : ℤ) + 1)) / 2).toNat
  have hq_eq : X = (2 * q + 2 * m + 1 : ℤ) := by dsimp [q]; omega
  have hq1 : 1 ≤ q := by dsimp [q]; omega
  have hq2 : q ≤ 2 * (m - 2) := by dsimp [q]; omega
  have hsq : q * (m + 1) + q.choose 2 + 1 = s ^ 2 := by
    rw [square_iff_pell m q s hm hq1, ← hq_eq]
    rw [hYs] at hXpell
    dsimp [N] at hXpell
    linarith
  exact hno q hq1 hq2 ⟨s, by rw [← sq]; exact hsq⟩

end OMA.P_oeis_a028886

theorem OMA.solution : type_of% @OMA.S_oeis_a028886.main := by
  intro m hm
  exact ⟨OMA.P_oeis_a028886.forward_dir m hm, OMA.P_oeis_a028886.backward_dir m hm⟩
