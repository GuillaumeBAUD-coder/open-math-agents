import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1

-- Reduction of the remaining a = 2 mod 4 branch of Erdos1052.
-- Credit: @jerryttuyan.
-- Certifies z = 199 using a new weight at prime 823; the other fifteen primes remain open.
-- Builds on the merged factor-graph reductions by @adammcarter and @aroth01.
-- The parent already reports a computational search eliminating 199; this is a Lean certificate.
-- Developed with ChatGPT GPT-6 Astra Pro; compiled with Codex gpt-6.1-sol assistance.

namespace OMA.Extra823

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1
  (facts master_gen mersenne_bound two_pow_of_no_odd_prime one_add_le_B B_nonneg kernel_balance_one)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 (simple_of_unique_repeated)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1

/-- Every prime whose successor is divisible by 823 is at least 3291.
The only smaller candidates are 822, 1645 and 2468, all composite. -/
theorem nx823 {p : ℕ} (hp : p.Prime) (hd : 823 ∣ p + 1) : 3291 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk4 : k < 4 := by omega
  obtain rfl : p = 823 * k - 1 := by omega
  interval_cases k <;> first | omega | (norm_num at hp)

/-- A kept parent of 103 is either 823 or at least 1647.
Below 1647 the only other prime candidate is 617, but 3 divides 618,
so 103 cannot be its least non-core odd factor when z is at least 17. -/
theorem nx103_extra {z p : ℕ} (hz : 17 ≤ z) (hp : p.Prime)
    (hd : 103 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) →
      c' ∣ p + 1 → 103 ≤ c') :
    p = 823 ∨ 1647 ≤ p := by
  have h3z : (3 : ℕ) ∉ ({z} : Finset ℕ) := by
    rw [Finset.mem_singleton]
    omega
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk16 : k < 16 := by omega
  obtain rfl : p = 103 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) h3z (by decide); omega)



theorem table_master_q823 {m e z q0 Nq : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (hz17 : 17 ≤ z)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hzP : z ∉ P) (h5P : 5 ∈ P) (h5c : ∀ p ∈ P, ¬ 5 ∣ p + 1) (b7 b13 b31 b61 b103 b127 b823 : ℚ)
    (h7 : 1 ≤ b7 ∧ (7 ∈ P → 8 / 7 ≤ b7 ∧ b7 ≤ 4 / 3 ∧ (b7 = 4 / 3 ∨ (∀ p ∈ P, ¬ 7 ∣ p + 1) ∨
      (13 ∈ P ∧ 8 / 7 * b13 ≤ b7) ∨ (13 ∉ P ∧ 8 / 7 * (182 / 180) ≤ b7))))
    (h13 : 1 ≤ b13 ∧ (13 ∈ P → 14 / 13 ≤ b13 ∧ b13 ≤ 7 / 6 ∧ (b13 = 7 / 6 ∨
      (∀ p ∈ P, ¬ 13 ∣ p + 1) ∨ (103 ∈ P ∧ 14 / 13 * b103 ≤ b13) ∨
      (103 ∉ P ∧ 14 / 13 * (884 / 882) ≤ b13))))
    (h31 : 1 ≤ b31 ∧ (31 ∈ P → 32 / 31 ≤ b31 ∧ b31 ≤ 16 / 15 ∧ (b31 = 16 / 15 ∨
      (∀ p ∈ P, ¬ 31 ∣ p + 1) ∨ (61 ∈ P ∧ 32 / 31 * b61 ≤ b31) ∨
      (61 ∉ P ∧ 32 / 31 * (992 / 990) ≤ b31))))
    (h61 : 1 ≤ b61 ∧ (61 ∈ P → 62 / 61 ≤ b61 ∧ b61 ≤ 31 / 30 ∧ (b61 = 31 / 30 ∨
      (∀ p ∈ P, ¬ 61 ∣ p + 1) ∨ 62 / 61 * (488 / 486) ≤ b61)))
    (h103 : 1 ≤ b103 ∧ (103 ∈ P → 104 / 103 ≤ b103 ∧ b103 ≤ 52 / 51 ∧ (b103 = 52 / 51 ∨
      (∀ p ∈ P, ¬ 103 ∣ p + 1) ∨ 104 / 103 * b823 ≤ b103)))
    (h127 : 1 ≤ b127 ∧ (127 ∈ P → 128 / 127 ≤ b127 ∧ b127 ≤ 64 / 63 ∧ (b127 = 64 / 63 ∨
      (∀ p ∈ P, ¬ 127 ∣ p + 1) ∨ 128 / 127 * (4064 / 4062) ≤ b127)))
    (hb823lo : (824 / 823 : ℚ) ≤ b823)
    (hb823B : b823 ≤ (824 / 822 : ℚ))
    (hb823step : (824 / 823 : ℚ) * (3292 / 3290) ≤ b823)
    (hq823 : q0 ≠ 823)
    (hq0 : 128 ≤ q0) (hq0p : q0.Prime) (bq : ℚ) (hbqlo : 1 + 1 / (q0 : ℚ) ≤ bq)
    (hbqB : bq ≤ ((q0 : ℚ) + 1) / ((q0 : ℚ) - 1)) (hNq2 : 2 ≤ Nq)
    (hNq : Nq + 1 ≤ 2 * q0 * (q0 + 1))
    (hfar : ∀ i j : ℕ, (q0 * (2 ^ i * z ^ j) - 1).Prime → Nq ≤ q0 * (2 ^ i * z ^ j) - 1)
    (hbq : (1 + 1 / (q0 : ℚ)) * (((Nq : ℚ) + 1) / ((Nq : ℚ) - 1)) ≤ bq) :
    ∃ L : Finset ℕ, L ⊆ P ∧ (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) ∧
      (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * (((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ)) *
        ((8 / 5 * b7 * b31 * b127 * (2048 / 2047)) *
          (bq * ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ x = q0),
            (((x : ℚ) + 1) / ((x : ℚ) - 1)))) := by
  classical
  have hne : ∀ c : ℕ, c < 128 → c ≠ q0 := fun c hc => by omega
  have hbq1 : (1 : ℚ) ≤ bq := le_trans (by
    have : (0 : ℚ) ≤ 1 / (q0 : ℚ) := by positivity
    linarith) hbqlo
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨-, -, F3, -, -, F6, -, -⟩ := facts hP hK E
  have hcz : ∀ c ∈ P, c ∉ ({z} : Finset ℕ) := fun c hc => by
    rw [Finset.mem_singleton]
    rintro rfl
    exact hzP hc
  obtain ⟨β, hβq, hβ3, hβ5, hβ7, hβ13, hβ31, hβ61, hβ103, hβ127, hβ823, hβ⟩ : ∃ β : ℕ → ℚ, β q0 = bq ∧ β 3 = 8 / 5 ∧
      β 5 = 6 / 5 ∧ β 7 = b7 ∧ β 13 = b13 ∧ β 31 = b31 ∧ β 61 = b61 ∧ β 103 = b103 ∧ β 127 = b127 ∧ β 823 = b823 ∧
      ∀ x : ℕ, x ≠ q0 → x ≠ 3 → x ≠ 5 → x ≠ 7 → x ≠ 13 → x ≠ 31 → x ≠ 61 → x ≠ 103 → x ≠ 127 → x ≠ 823 →
        β x = ((x : ℚ) + 1) / ((x : ℚ) - 1) :=
    ⟨fun x => if x = q0 then bq else if x = 3 then 8 / 5 else if x = 5 then 6 / 5 else if x = 7 then b7
      else if x = 13 then b13 else if x = 31 then b31 else if x = 61 then b61
      else if x = 103 then b103 else if x = 127 then b127 else if x = 823 then b823 else ((x : ℚ) + 1) / ((x : ℚ) - 1),
      by simp, by simp [hne 3 (by norm_num)], by simp [hne 5 (by norm_num)],
      by simp [hne 7 (by norm_num)], by simp [hne 13 (by norm_num)], by simp [hne 31 (by norm_num)],
      by simp [hne 61 (by norm_num)], by simp [hne 103 (by norm_num)], by simp [hne 127 (by norm_num)],
      by simp [Ne.symm hq823],
      fun x h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => by simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]⟩
  have hBd : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases eq0 : p = q0
    · rw [eq0, hβq]
      exact ⟨hbqlo, hbqB⟩
    by_cases e3 : p = 3
    · subst e3
      rw [hβ3]
      norm_num
    by_cases e5 : p = 5
    · subst e5
      rw [hβ5]
      norm_num
    by_cases e7 : p = 7
    · subst e7
      obtain ⟨hlo, hhi, -⟩ := h7.2 hp
      rw [hβ7]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    by_cases e13 : p = 13
    · subst e13
      obtain ⟨hlo, hhi, -⟩ := h13.2 hp
      rw [hβ13]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    by_cases e31 : p = 31
    · subst e31
      obtain ⟨hlo, hhi, -⟩ := h31.2 hp
      rw [hβ31]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    by_cases e61 : p = 61
    · subst e61
      obtain ⟨hlo, hhi, -⟩ := h61.2 hp
      rw [hβ61]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    by_cases e103 : p = 103
    · subst e103
      obtain ⟨hlo, hhi, -⟩ := h103.2 hp
      rw [hβ103]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    by_cases e127 : p = 127
    · subst e127
      obtain ⟨hlo, hhi, -⟩ := h127.2 hp
      rw [hβ127]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    by_cases e823 : p = 823
    · subst e823
      rw [hβ823]
      exact ⟨le_trans (by norm_num) hb823lo, le_trans hb823B (by norm_num)⟩
    rw [hβ p eq0 e3 e5 e7 e13 e31 e61 e103 e127 e823]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have hsp : ∀ c : ℕ, β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) →
      c = q0 ∨ c = 3 ∨ c = 5 ∨ c = 7 ∨ c = 13 ∨ c = 31 ∨ c = 61 ∨ c = 103 ∨ c = 127 ∨ c = 823 := by
    intro c hc
    by_contra hcon
    push Not at hcon
    rcases hcon with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact hc (hβ c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9)
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hl hne'
    have hpp := (hP p hp).1
    have hwp := (hBd p hp).2
    rcases hsp c hne' with hcq | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hd' : q0 ∣ p + 1 := hcq ▸ hd
      have hcP' : q0 ∈ P := hcq ▸ hc
      have hodd : p % 2 = 1 := (hP p hp).1.eq_two_or_odd.resolve_left (hP p hp).2
      rw [hcq, hβq]
      rcases kept_parent_form (z := z) hq0p (by omega) hd'
        (F6 q0 hq0p (by omega) (hcz q0 hcP') p hp) hodd
        (fun c' h1 h2 h3 h4 => hcq ▸ hl c' h1 h2 h3 h4) with ⟨i, j, hij⟩ | hbig
      · have hpe : p = q0 * (2 ^ i * z ^ j) - 1 := by omega
        have hN : Nq ≤ p := by
          rw [hpe]
          exact hfar i j (hpe ▸ hpp)
        exact far_step (c := q0) (N := Nq) hNq2 hN hwp hbq
      · exact far_step (c := q0) (N := Nq) hNq2 (by omega) hwp hbq
    · have hp5 : p = 5 :=
        F3 3 Nat.prime_three (by norm_num) (hcz 3 hc) p hp 5 h5P hd (by norm_num)
      rw [hp5, hβ5, hβ3]
      norm_num
    · exact absurd hd (h5c p hp)
    · obtain ⟨-, -, hmenu⟩ := h7.2 hc
      rw [hβ7]
      rcases hmenu with heq | hcl | ⟨hnP, hw⟩ | ⟨hnn, hw⟩
      · exact absurd (by rw [hβ7, heq]; norm_num) hne'
      · exact absurd hd (hcl p hp)
      · have hpn : p = 13 :=
          F3 7 (by norm_num) (by norm_num) (hcz 7 hc) p hp 13 hnP hd (by norm_num)
        rw [hpn, hβ13]
        refine le_trans (le_of_eq ?_) hw
        norm_num
      · rcases nx7 hz17 hpp hd (F6 7 (by norm_num) (by norm_num) (hcz 7 hc) p hp) hl with rfl | hfar
        · exact absurd hp hnn
        · exact far_step (c := 7) (N := 181) (by norm_num) hfar hwp
            (le_trans (le_of_eq (by norm_num)) hw)
    · obtain ⟨-, -, hmenu⟩ := h13.2 hc
      rw [hβ13]
      rcases hmenu with heq | hcl | ⟨hnP, hw⟩ | ⟨hnn, hw⟩
      · exact absurd (by rw [hβ13, heq]; norm_num) hne'
      · exact absurd hd (hcl p hp)
      · have hpn : p = 103 :=
          F3 13 (by norm_num) (by norm_num) (hcz 13 hc) p hp 103 hnP hd (by norm_num)
        rw [hpn, hβ103]
        refine le_trans (le_of_eq ?_) hw
        norm_num
      · rcases nx13 hz17 hpp hd (F6 13 (by norm_num) (by norm_num) (hcz 13 hc) p hp) hl with rfl | hfar
        · exact absurd hp hnn
        · exact far_step (c := 13) (N := 883) (by norm_num) hfar hwp
            (le_trans (le_of_eq (by norm_num)) hw)
    · obtain ⟨-, -, hmenu⟩ := h31.2 hc
      rw [hβ31]
      rcases hmenu with heq | hcl | ⟨hnP, hw⟩ | ⟨hnn, hw⟩
      · exact absurd (by rw [hβ31, heq]; norm_num) hne'
      · exact absurd hd (hcl p hp)
      · have hpn : p = 61 :=
          F3 31 (by norm_num) (by norm_num) (hcz 31 hc) p hp 61 hnP hd (by norm_num)
        rw [hpn, hβ61]
        refine le_trans (le_of_eq ?_) hw
        norm_num
      · rcases nx31 hz17 hpp hd hl with rfl | hfar
        · exact absurd hp hnn
        · exact far_step (c := 31) (N := 991) (by norm_num) hfar hwp
            (le_trans (le_of_eq (by norm_num)) hw)
    · obtain ⟨-, -, hmenu⟩ := h61.2 hc
      rw [hβ61]
      rcases hmenu with heq | hcl | hw
      · exact absurd (by rw [hβ61, heq]; norm_num) hne'
      · exact absurd hd (hcl p hp)
      · exact far_step (c := 61) (N := 487) (by norm_num) (nx61 hpp hd) hwp
          (le_trans (le_of_eq (by norm_num)) hw)
    · obtain ⟨-, -, hmenu⟩ := h103.2 hc
      rw [hβ103]
      rcases hmenu with heq | hcl | hw
      · exact absurd (by rw [hβ103, heq]; norm_num) hne'
      · exact absurd hd (hcl p hp)
      · rcases nx103_extra hz17 hpp hd hl with hpe | hfar103
        · rw [hpe, hβ823]
          exact le_trans (le_of_eq (by norm_num)) hw
        · apply far_step (c := 103) (N := 1647) (by norm_num) hfar103 hwp
          calc (1 + 1 / (103 : ℚ)) * (((1647 : ℚ) + 1) / ((1647 : ℚ) - 1))
              = (104 / 103) * (824 / 823) := by norm_num
            _ ≤ (104 / 103) * b823 := mul_le_mul_of_nonneg_left hb823lo (by norm_num)
            _ ≤ b103 := hw
    · obtain ⟨-, -, hmenu⟩ := h127.2 hc
      rw [hβ127]
      rcases hmenu with heq | hcl | hw
      · exact absurd (by rw [hβ127, heq]; norm_num) hne'
      · exact absurd hd (hcl p hp)
      · exact far_step (c := 127) (N := 4063) (by norm_num) (nx127 hz17 hpp hd hl) hwp
          (le_trans (le_of_eq (by norm_num)) hw)
    · rw [hβ823]
      apply far_step (c := 823) (N := 3291) (by norm_num) (nx823 hpp hd) hwp
      exact le_trans (le_of_eq (by norm_num)) hb823step
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen hP hK (by positivity) E β hBd h4
  have hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z := fun x hx c hc h2 hd =>
    Finset.mem_singleton.mp (hLleaf x hx c hc h2 hd)
  refine ⟨L, hLP, hleaf, ?_⟩
  have hpos : ∀ x ∈ L, 0 < β x := fun x hx =>
    lt_of_lt_of_le (by positivity) (hBd x (hLP hx)).1
  have hBq : ∀ x ∈ L, β x ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx => (hBd x (hLP hx)).2
  have hM : ∏ x ∈ L.filter (fun x => ¬ z ∣ x + 1), β x ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    apply mersenne_bound
    · intro x hx
      exact (hP x (hLP (Finset.mem_filter.mp hx).1)).1
    · intro x hx
      obtain ⟨hxL, hxz⟩ := Finset.mem_filter.mp hx
      exact two_pow_of_no_odd_prime (fun c hc h2 hd => hxz (hleaf x hxL c hc h2 hd ▸ hd))
    · intro x hx
      have hxL := (Finset.mem_filter.mp hx).1
      exact ⟨hpos x hxL, hBq x hxL⟩
    · rw [hβ3, hβ7, hβ31, hβ127]
      exact ⟨by norm_num, h7.1, h31.1, h127.1⟩
  rw [hβ3, hβ7, hβ31, hβ127] at hM
  have hq0leaf : ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => x = q0), β x ≤ bq := by
    have hsub : (L.filter (fun x => z ∣ x + 1)).filter (fun x => x = q0) ⊆ ({q0} : Finset ℕ) :=
      fun x hx => by
        rw [Finset.mem_singleton]
        exact (Finset.mem_filter.mp hx).2
    have h := Finset.prod_le_prod_of_subset_of_one_le (f := β) hsub
      (fun x hx => (hpos x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).le)
      (fun x hx _ => by
        rw [Finset.mem_singleton.mp hx, hβq]
        exact hbq1)
    rwa [Finset.prod_singleton, hβq] at h
  have hrest : ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ x = q0), β x ≤
      ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ x = q0),
        (((x : ℚ) + 1) / ((x : ℚ) - 1)) :=
    Finset.prod_le_prod
      (fun x hx => (hpos x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).le)
      (fun x hx => hBq x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)
  have hZ : ∏ x ∈ L.filter (fun x => z ∣ x + 1), β x ≤ bq *
      ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ x = q0),
        (((x : ℚ) + 1) / ((x : ℚ) - 1)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (L.filter (fun x => z ∣ x + 1))
      (fun x => x = q0) β]
    exact mul_le_mul hq0leaf hrest (Finset.prod_nonneg fun x hx =>
      (hpos x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).le) (by linarith)
  have hX : ∏ x ∈ L, β x ≤ (8 / 5 * b7 * b31 * b127 * (2048 / 2047)) *
      (bq * ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ x = q0),
        (((x : ℚ) + 1) / ((x : ℚ) - 1))) := by
    rw [← Finset.prod_filter_mul_prod_filter_not L (fun x => z ∣ x + 1) β, mul_comm]
    exact mul_le_mul hM hZ (Finset.prod_nonneg fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le)
      (by
        have := h7.1
        have := h31.1
        have := h127.1
        positivity)
  exact hmain.trans (mul_le_mul_of_nonneg_left hX (by positivity))


-- The formerly unresolved z = 199 branch closes with this single extra weight.
-- All constants are rational and are discharged by norm_num.
set_option maxHeartbeats 2000000 in
theorem amod4_z199 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 199 ^ e) * ∏ p ∈ P, (p + 1) =
      2 ^ (m + 1) * 199 ^ e * ∏ p ∈ P, p)
    (hzP : 199 ∉ P) (hm4 : m % 4 = 2) (hm : 22 ≤ m) (he : 3 ≤ e) : False := by
  classical
  have hz : Nat.Prime 199 := by norm_num
  obtain ⟨h3P, h5P, h5c, -⟩ := setup5 hP hz (by norm_num) E hm4
  have hK : ∀ c : ℕ, c.Prime → c ∣ 199 ^ e → c ∈ ({199} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨F1, -, -, -, -, -, -, -⟩ := facts hP hK E
  have hfar397 : ∀ i j : ℕ, (397 * (2 ^ i * 199 ^ j) - 1).Prime →
      12703 ≤ 397 * (2 ^ i * 199 ^ j) - 1 :=
    far_of_small (i0 := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (fun i hi => by interval_cases i <;> norm_num)
  have hfin : ∀ C : ℚ, 0 ≤ C → C ≤ (33554432 / 16836575 : ℚ) →
      (∃ L : Finset ℕ, L ⊆ P ∧ (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = 199) ∧
        (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * (((1 + 199 ^ e : ℕ) : ℚ) / ((199 ^ e : ℕ) : ℚ)) *
          (C * ((6368 / 6351) * ∏ x ∈ (L.filter (fun x => 199 ∣ x + 1)).filter (fun x => ¬ x = 397),
            (((x : ℚ) + 1) / ((x : ℚ) - 1))))) → False := by
    rintro C hC0 hC ⟨L, hLP, hleaf, hmain⟩
    have hZ := zleaves_except (s := 4) (q0 := 397) hz (by norm_num)
      (fun k hk1 hk4 hp => by interval_cases k <;> first | (norm_num at hp; done) | norm_num)
      (fun x hx => hP x (hLP hx)) hleaf
    apply table_close hm hmain (by positivity) (kk_le (by norm_num) (le_refl 199) he) hC0
      (mul_nonneg (by norm_num : (0 : ℚ) ≤ 6368 / 6351)
        (Finset.prod_nonneg fun x hx =>
          B_nonneg (hP x (hLP (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)).1.one_lt.le))
      (mul_le_mul_of_nonneg_left hZ (by norm_num : (0 : ℚ) ≤ 6368 / 6351))
    have hn : (1 + 1 / (2 : ℚ) ^ 22) * (((1 + 199 ^ 3 : ℕ) : ℚ) / ((199 ^ 3 : ℕ) : ℚ)) *
        ((33554432 / 16836575) * ((6368 / 6351) *
          (((199 : ℚ) ^ 2 / ((199 : ℚ) ^ 2 - 3)) *
            (((2 ^ 4 * 199 : ℕ) : ℚ) / (((2 ^ 4 * 199 : ℕ) : ℚ) - 2))))) < 2 := by norm_num
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC (by norm_num)) (by norm_num)) hn
  by_cases h13 : 13 ∈ P
  · have h7 : 7 ∈ P := F1 7 (by norm_num) (by norm_num) (by decide) 13 h13 (by norm_num)
    by_cases h31 : 31 ∈ P
    · exact kill_7_13_31 hP hz E h3P h5P h7 h13 h31
    · by_cases h103 : 103 ∈ P
      · by_cases h127 : 127 ∈ P
        · exact kill_7_13_103_127 hP hz E h3P h5P h7 h13 h103 h127
        · exact hfin _ (by norm_num) (by norm_num)
            (table_master_q823 hP hz (by norm_num) E hzP h5P h5c
              (8 / 7 * (14 / 13 * (1664 / 1645))) (14 / 13 * (1664 / 1645)) 1
              (31 / 30) (1664 / 1645) 1 (1648 / 1645)
              ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inl ⟨h13, by norm_num⟩))⟩⟩
              ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inl ⟨h103, by norm_num⟩))⟩⟩
              ⟨le_refl _, fun h => absurd h h31⟩
              ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
              ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (by norm_num))⟩⟩
              ⟨le_refl _, fun h => absurd h h127⟩
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (q0 := 397) (Nq := 12703) (by norm_num) (by norm_num) (6368 / 6351)
              (by norm_num) (by norm_num) (by norm_num) (by norm_num) hfar397 (by norm_num))
      · exact hfin _ (by norm_num) (by norm_num)
          (table_master_q hP hz (by norm_num) E hzP h5P h5c
            (8 / 7 * (14 / 13 * (884 / 882))) (14 / 13 * (884 / 882)) 1
            (31 / 30) (52 / 51) (128 / 127 * (4064 / 4062))
            ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inl ⟨h13, le_refl _⟩))⟩⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inr ⟨h103, le_refl _⟩))⟩⟩
            ⟨le_refl _, fun h => absurd h h31⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (le_refl _))⟩⟩
            (q0 := 397) (Nq := 12703) (by norm_num) (by norm_num) (6368 / 6351)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) hfar397 (by norm_num))
  · exact hfin _ (by norm_num) (by norm_num)
      (table_master_q hP hz (by norm_num) E hzP h5P h5c
        (8 / 7 * (182 / 180)) 1 (16 / 15)
        (31 / 30) (52 / 51) (128 / 127 * (4064 / 4062))
        ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inr ⟨h13, le_refl _⟩))⟩⟩
        ⟨le_refl _, fun h => absurd h h13⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (le_refl _))⟩⟩
        (q0 := 397) (Nq := 12703) (by norm_num) (by norm_num) (6368 / 6351)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) hfar397 (by norm_num))

-- The exact unitary-perfect-number special case needed by the held step.
theorem z199_bound {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 199)
    (he : n.factorization 199 % 32 = 0) (hm4 : padicValNat 2 n % 4 = 2) :
    padicValNat 2 n ≤ 21 := by
  by_contra hgt
  have hz : Nat.Prime 199 := by norm_num
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hzpf : 199 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf (by norm_num) hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  have he2 : 2 ≤ n.factorization 199 :=
    (hz.pow_dvd_iff_le_factorization h.2.ne').mp ((hS 199).mpr rfl).2.2
  have hzP : 199 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({199} : Finset ℕ)) :=
    fun hmem => (Finset.mem_filter.mp hmem).2 (Finset.mem_singleton_self 199)
  exact amod4_z199 hP E hzP hm4 (by omega) (by omega)

end OMA.Extra823



namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1_H2_R2

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem residual_cases {z : ℕ} (hz : z.Prime)
    (hc : z ∈ ({23, 37, 41, 53} : Finset ℕ) ∨ (61 ≤ z ∧ z < 823 ∧
      z ∉ ({67, 73, 89, 101, 103, 107, 109, 113, 127, 131, 149, 151, 163, 167, 179, 181, 191, 193, 197,
      211, 223, 227, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313,
      317, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433,
      439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
      563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
      661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
      797, 809, 811, 821} : Finset ℕ))) :
    z ∈ ({23, 37, 41, 53, 61, 71, 79, 83} : Finset ℕ) ∨
    z ∈ ({97, 137, 139, 157, 173, 229, 331} : Finset ℕ) ∨ z = 199 := by
  have hfinite : (Finset.range 823).filter (fun z : ℕ => z.Prime ∧ (z ∈ ({23, 37, 41, 53} : Finset ℕ) ∨ (61 ≤ z ∧ z < 823 ∧
      z ∉ ({67, 73, 89, 101, 103, 107, 109, 113, 127, 131, 149, 151, 163, 167, 179, 181, 191, 193, 197,
      211, 223, 227, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313,
      317, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433,
      439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
      563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
      661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
      797, 809, 811, 821} : Finset ℕ)))) =
      ({23, 37, 41, 53, 61, 71, 79, 83, 97, 137, 139, 157, 173, 199, 229, 331} : Finset ℕ) := by decide
  have hb : z < 823 := by
    rcases hc with hs | hs
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> omega
    · exact hs.2.1
  have hm : z ∈ ({23, 37, 41, 53, 61, 71, 79, 83, 97, 137, 139, 157, 173, 199, 229, 331} : Finset ℕ) := by
    rw [← hfinite]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb, ⟨hz, hc⟩⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
  omega

-- The new certificate settles z = 199. These two hypotheses retain the other cases.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime →
    z ∈ ({23, 37, 41, 53, 61, 71, 79, 83} : Finset ℕ) →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    n.factorization z % 32 = 0 →
    padicValNat 2 n % 20 ≠ 10 → padicValNat 2 n % 28 ≠ 14 →
    padicValNat 2 n % 4 = 2 → padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime →
    z ∈ ({97, 137, 139, 157, 173, 229, 331} : Finset ℕ) →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    n.factorization z % 32 = 0 →
    padicValNat 2 n % 20 ≠ 10 → padicValNat 2 n % 28 ≠ 14 →
    padicValNat 2 n % 4 = 2 → padicValNat 2 n ≤ A

theorem main : H1 → H2 →
    OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1.H2 := by
  rintro ⟨A, hA⟩ ⟨B, hB⟩
  refine ⟨max (max A B) 21, ?_⟩
  intro n hn z hz hc hS he h20 h28 h4
  rcases residual_cases hz hc with hlow | hhigh | rfl
  · exact (hA n hn z hz hlow hS he h20 h28 h4).trans
      ((le_max_left A B).trans (le_max_left (max A B) 21))
  · exact (hB n hn z hz hhigh hS he h20 h28 h4).trans
      ((le_max_right A B).trans (le_max_left (max A B) 21))
  · exact (OMA.Extra823.z199_bound hn hS he h4).trans (le_max_right (max A B) 21)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1_H2_R2
