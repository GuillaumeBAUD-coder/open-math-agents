import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1

/-! For the unique repeated prime 257, reduce the possible supplier of 3 to
5. The weighting uses the least odd child outside the kernel.
Split the remaining case by whether 19 supplies 5. -/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1_H3_R1

open scoped BigOperators
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1
  (facts kernel_balance_one master_gen mersenne_bound two_pow_of_no_odd_prime
   one_add_le_B B_anti)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 (simple_of_unique_repeated)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1 (table_finish)

private theorem only_core_prime {e : ℕ} (c : ℕ) (hc : c.Prime) (hdiv : c ∣ 257 ^ e) :
    c ∈ ({257} : Finset ℕ) :=
  Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc (by norm_num)).mp
    (hc.dvd_of_dvd_pow hdiv))

private theorem weighted_contradiction {a e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (ha : 11 ≤ a) (he : 2 ≤ e)
    (E : (2 ^ a + 1) * (1 + 257 ^ e) * ∏ p ∈ P, (p + 1) =
      2 ^ (a + 1) * 257 ^ e * ∏ p ∈ P, p)
    (β : ℕ → ℚ)
    (hβ : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1))
    (hstep : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ r : ℕ, r.Prime → r ≠ 2 → r ∉ ({257} : Finset ℕ) → r ∣ p + 1 → c ≤ r) →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c)
    (hbase : 1 ≤ β 3 ∧ 1 ≤ β 7 ∧ 1 ≤ β 31 ∧ 1 ≤ β 127)
    (hnum : (1 + 1 / (2 : ℚ) ^ 11) * (((1 + (257 : ℕ) ^ 2 : ℕ) : ℚ) / ((257 ^ 2 : ℕ) : ℚ)) *
      ((β 3 * β 7 * β 31 * β 127 * (2048 / 2047)) *
        (((257 : ℚ) ^ 2 / ((257 : ℚ) ^ 2 - 3)) * ((257 : ℚ) / (257 - 2)))) < 2) : False := by
  classical
  obtain ⟨L, hLP, hleaf, hprod⟩ :=
    master_gen hP (only_core_prime (e := e)) (by positivity) E β hβ hstep
  have hpos (x : ℕ) (hx : x ∈ L) : 0 < β x :=
    lt_of_lt_of_le (by positivity) (hβ x (hLP hx)).1
  have hmersenne := mersenne_bound β (L.filter fun x => ¬ 257 ∣ x + 1)
    (fun x hx => (hP x (hLP (Finset.mem_filter.mp hx).1)).1)
    (fun x hx => by
      obtain ⟨hxL, hdiv⟩ := Finset.mem_filter.mp hx
      apply two_pow_of_no_odd_prime
      intro r hr hr2 hrdiv
      have hrz := Finset.mem_singleton.mp (hleaf x hxL r hr hr2 hrdiv)
      exact hdiv (hrz ▸ hrdiv))
    (fun x hx => ⟨hpos x (Finset.mem_filter.mp hx).1,
      (hβ x (hLP (Finset.mem_filter.mp hx).1)).2⟩) hbase
  have hother :
      (∏ x ∈ L.filter (fun x => 257 ∣ x + 1), β x) ≤
        ∏ x ∈ L.filter (fun x => 257 ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) :=
    Finset.prod_le_prod (fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le)
      (fun x hx => (hβ x (hLP (Finset.mem_filter.mp hx).1)).2)
  have hother0 : 0 ≤ ∏ x ∈ L.filter (fun x => 257 ∣ x + 1), β x :=
    Finset.prod_nonneg fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le
  have hC0 : 0 ≤ β 3 * β 7 * β 31 * β 127 * (2048 / 2047) := by
    obtain ⟨h3,h7,h31,h127⟩ := hbase
    have h3' : 0 ≤ β 3 := by linarith
    have h7' : 0 ≤ β 7 := by linarith
    have h31' : 0 ≤ β 31 := by linarith
    have h127' : 0 ≤ β 127 := by linarith
    positivity
  refine table_finish (a0 := 11) (Z0 := 257) (e0 := 2)
    hP (by norm_num : Nat.Prime 257) (by decide) (le_refl _) ha he hC0 ?_ hnum
  refine ⟨L, hLP, fun x hx c hc hn hd => Finset.mem_singleton.mp (hleaf x hx c hc hn hd), ?_⟩
  refine hprod.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [← Finset.prod_filter_mul_prod_filter_not L (fun x => 257 ∣ x + 1) β, mul_comm]
  exact mul_le_mul hmersenne hother hother0 hC0

/-- Install overrides only at vertices 3, 7 and 47. A supplier of 7 that also
supplies 3 does not use 7 as its least odd child. -/
private theorem reject_table {a e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (ha : 11 ≤ a) (he : 2 ≤ e)
    (E : (2 ^ a + 1) * (1 + 257 ^ e) * ∏ p ∈ P, (p + 1) =
      2 ^ (a + 1) * 257 ^ e * ∏ p ∈ P, p)
    (b3 b7 b47 : ℚ)
    (h3 : 4 / 3 ≤ b3 ∧ b3 ≤ 2) (h7 : 8 / 7 ≤ b7 ∧ b7 ≤ 4 / 3)
    (h47 : 48 / 47 ≤ b47 ∧ b47 ≤ 48 / 46)
    (hnum : (1 + 1 / (2 : ℚ) ^ 11) * (((1 + (257 : ℕ) ^ 2 : ℕ) : ℚ) / ((257 ^ 2 : ℕ) : ℚ)) *
      ((b3 * b7 * (16 / 15) * (64 / 63) * (2048 / 2047)) *
        (((257 : ℚ) ^ 2 / ((257 : ℚ) ^ 2 - 3)) * ((257 : ℚ) / (257 - 2)))) < 2)
    (cert : let β := fun p : ℕ => if p = 3 then b3 else if p = 7 then b7 else
        if p = 47 then b47 else ((p : ℚ) + 1) / ((p : ℚ) - 1)
      (∀ p ∈ P, β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1)) →
      (∀ p ∈ P, 3 ∣ p + 1 → b3 ≠ 2 → (4 / 3) * β p ≤ b3) ∧
      (∀ p ∈ P, 7 ∣ p + 1 → ¬ 3 ∣ p + 1 → b7 ≠ 4 / 3 → (8 / 7) * β p ≤ b7) ∧
      (∀ p ∈ P, 47 ∣ p + 1 → b47 ≠ 48 / 46 → (48 / 47) * β p ≤ b47)) : False := by
  let β := fun p : ℕ => if p = 3 then b3 else if p = 7 then b7 else
    if p = 47 then b47 else ((p : ℚ) + 1) / ((p : ℚ) - 1)
  have hβ : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst p
      norm_num [β] at h3 ⊢
      exact h3
    by_cases e7 : p = 7
    · subst p
      norm_num [β] at h7 ⊢
      exact h7
    by_cases e47 : p = 47
    · subst p
      norm_num [β] at h47 ⊢
      exact h47
    simpa [β, e3, e7, e47] using one_add_le_B (hP p hp).1.two_le
  obtain ⟨s3,s7,s47⟩ := cert (fun p hp => (hβ p hp).2)
  refine weighted_contradiction hP ha he E β hβ ?_ ?_ ?_
  · intro p hp c _ div least special
    by_cases e3 : c = 3
    · subst c
      have hne : b3 ≠ 2 := by
        intro eq
        apply special
        norm_num [β, eq]
      have hs := s3 p hp div hne
      norm_num [β] at hs ⊢
      exact hs
    by_cases e7 : c = 7
    · subst c
      have hne : b7 ≠ 4 / 3 := by
        intro eq
        apply special
        norm_num [β, eq]
      have hn3 : ¬ 3 ∣ p + 1 := by
        intro h
        have bad := least 3 (by norm_num) (by decide) (by decide) h
        norm_num at bad
      have hs := s7 p hp div hn3 hne
      norm_num [β] at hs ⊢
      exact hs
    by_cases e47 : c = 47
    · subst c
      have hne : b47 ≠ 48 / 46 := by
        intro eq
        apply special
        norm_num [β, eq]
      have hs := s47 p hp div hne
      norm_num [β] at hs ⊢
      exact hs
    exact (special (by simp [β, e3, e7, e47])).elim
  · norm_num [β]
    exact ⟨(by norm_num : (1 : ℚ) ≤ 4 / 3).trans h3.1,
      (by norm_num : (1 : ℚ) ≤ 8 / 7).trans h7.1⟩
  · norm_num [β] at hnum ⊢
    exact hnum

/-- A permissible supplier of 47 is at least 751. The two smaller candidates
in the required progression are composite. -/
private theorem supplier_47_lower {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h47 : 47 ∣ p + 1) (hn3 : ¬ 3 ∣ p + 1) : 751 ≤ p := by
  have h2 : 2 ∣ p + 1 := even_iff_two_dvd.mp (hp.odd_of_ne_two hp2).add_one
  have h94 : 94 ∣ p + 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2 47) h2 h47
  have hp3 : p ≠ 3 := by
    intro h
    rw [h] at h47
    norm_num at h47
  have hn : ¬ 3 ∣ p := fun h =>
    hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
  have hmod : p % 3 = 1 := by omega
  obtain ⟨k,hk⟩ := h94
  by_contra notlarge
  have hcases : k = 2 ∨ k = 5 := by omega
  rcases hcases with rfl | rfl
  · have eq : p = 187 := by omega
    rw [eq] at hp
    norm_num at hp
  · have eq : p = 469 := by omega
    rw [eq] at hp
    norm_num at hp

set_option maxHeartbeats 2000000 in
private theorem small_source_cases {q : ℕ} (h : q < 71) (hp : q.Prime)
    (h2 : q ≠ 2) (h3 : 3 ∣ q + 1) :
    q = 5 ∨ q = 11 ∨ q = 17 ∨ q = 23 ∨ q = 29 ∨ q = 41 ∨ q = 47 ∨
      q = 53 ∨ q = 59 := by
  exact (by decide : ∀ t : Fin 71, t.val.Prime → t.val ≠ 2 → 3 ∣ t.val + 1 →
    t.val = 5 ∨ t.val = 11 ∨ t.val = 17 ∨ t.val = 23 ∨ t.val = 29 ∨
      t.val = 41 ∨ t.val = 47 ∨ t.val = 53 ∨ t.val = 59) ⟨q,h⟩ hp h2 h3

/-- For a fixed supplier of 3, verify the modified weights by checking only
the small arithmetic progressions that can supply each modified prime. -/
private theorem reject_certified_weights {a e q : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (ha : 11 ≤ a) (he : 2 ≤ e)
    (E : (2 ^ a + 1) * (1 + 257 ^ e) * ∏ p ∈ P, (p + 1) =
      2 ^ (a + 1) * 257 ^ e * ∏ p ∈ P, p)
    (hq : q ∈ P) (hq3 : 3 ∣ q + 1) (adjusted : Finset ℕ) (β : ℕ → ℚ)
    (hdefault : ∀ c, c ∉ adjusted → β c = ((c : ℚ) + 1) / ((c : ℚ) - 1))
    (hvals : ∀ c : ↑adjusted,
      1 + 1 / (c.val : ℚ) ≤ β c.val ∧ β c.val ≤ ((c.val : ℚ) + 1) / ((c.val : ℚ) - 1))
    (h3 : β 3 = (1 + 1 / (3 : ℚ)) * β q)
    (hsource : ∀ c : ↑adjusted, c.val ≠ 3 → (¬ c.val ∣ q + 1) ∧ (¬ c.val ∣ 4))
    (hlarge : ∀ c : ↑adjusted, c.val ≠ 3 →
      (1 + 1 / (c.val : ℚ)) * (1025 / 1023) ≤ β c.val)
    (hsmall : ∀ c : ↑adjusted, c.val ≠ 3 → ∀ k : Fin (1024 / c.val + 1),
      let p := c.val * k.val - 1
      p.Prime → p % 3 = 1 → (1 + 1 / (c.val : ℚ)) * β p ≤ β c.val)
    (hbase : 1 ≤ β 3 ∧ 1 ≤ β 7 ∧ 1 ≤ β 31 ∧ 1 ≤ β 127)
    (hnum : (1 + 1 / (2 : ℚ) ^ 11) * (((1 + (257 : ℕ) ^ 2 : ℕ) : ℚ) / ((257 ^ 2 : ℕ) : ℚ)) *
      ((β 3 * β 7 * β 31 * β 127 * (2048 / 2047)) *
        (((257 : ℚ) ^ 2 / ((257 : ℚ) ^ 2 - 3)) * ((257 : ℚ) / (257 - 2)))) < 2) : False := by
  obtain ⟨-, -, unique, -, -, -, -, -⟩ := facts hP (only_core_prime (e := e)) E
  have hβ p (hp : p ∈ P) :
      1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    by_cases h : p ∈ adjusted
    · exact hvals ⟨p,h⟩
    · rw [hdefault p h]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
  refine weighted_contradiction hP ha he E β hβ ?_ hbase hnum
  intro p hp c hc hd _ hmodified
  have hmem : c ∈ adjusted := by
    by_contra h
    exact hmodified (hdefault c h)
  have unique3 (hd3 : 3 ∣ p + 1) : p = q :=
    unique 3 (by norm_num) (by decide) (by decide) p hp q hq hd3 hq3
  by_cases hc3 : c = 3
  · subst c
    simp [unique3 hd, h3]
  have hnot : (¬ c ∣ q + 1) ∧ (¬ c ∣ 4) := hsource ⟨c,hmem⟩ hc3
  have hp3 : p ≠ 3 := by
    intro h
    exact hnot.2 (by simpa [h] using hd)
  have hpq : p ≠ q := by
    intro h
    exact hnot.1 (by simpa [h] using hd)
  have hpmod : p % 3 = 1 := by
    have hn1 : ¬ 3 ∣ p + 1 := fun h => hpq (unique3 h)
    have hn0 : ¬ 3 ∣ p := fun h =>
      hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (hP p hp).1).mp h).symm
    omega
  by_cases hsmallp : p < 1024
  · obtain ⟨k,hk⟩ := hd
    have hk' : k ≤ 1024 / c := (Nat.le_div_iff_mul_le (hP c hc).1.pos).mpr
      (by rw [Nat.mul_comm, ← hk]; omega)
    have eq : c * k - 1 = p := by omega
    let k' : Fin (1024 / c + 1) := ⟨k, by omega⟩
    have h := hsmall ⟨c,hmem⟩ hc3 k'
    dsimp only [k'] at h
    rw [eq] at h
    exact h (hP p hp).1 hpmod
  · have h := (hβ p hp).2.trans (B_anti (by decide : 2 ≤ 1024) (by omega : 1024 ≤ p))
    have h' : β p ≤ (1025 / 1023 : ℚ) := by norm_num at h ⊢; exact h
    exact (mul_le_mul_of_nonneg_left h' (by positivity)).trans (hlarge ⟨c,hmem⟩ hc3)


set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem no_source_23 {a e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (ha : 11 ≤ a) (he : 2 ≤ e)
    (E : (2 ^ a + 1) * (1 + 257 ^ e) * ∏ p ∈ P, (p + 1) =
      2 ^ (a + 1) * 257 ^ e * ∏ p ∈ P, p) (hq : 23 ∈ P) : False := by
  let adjusted : Finset ℕ := {3, 7, 13}
  let β (p : ℕ) : ℚ :=
    if p = 3 then 16 / 11 else
    if p = 7 then 64 / 51 else
    if p = 13 then 56 / 51 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1)
  refine reject_certified_weights hP ha he E hq (by decide) adjusted β
    ?_ ?_ (by norm_num [β]) ?_ ?_ ?_ (by norm_num [β]) (by norm_num [β])
  · intro c h
    simp only [adjusted, Finset.mem_insert, Finset.mem_singleton, not_or] at h
    simp [β, h.1, h.2.1, h.2.2]
  · dsimp only [adjusted, β]
    decide +kernel
  · dsimp only [adjusted]
    decide +kernel
  · dsimp only [adjusted, β]
    decide +kernel
  · dsimp only [adjusted, β]
    decide +kernel


set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem no_source_11 {a e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (ha : 11 ≤ a) (he : 2 ≤ e)
    (E : (2 ^ a + 1) * (1 + 257 ^ e) * ∏ p ∈ P, (p + 1) =
      2 ^ (a + 1) * 257 ^ e * ∏ p ∈ P, p) (hq : 11 ∈ P) : False := by
  let adjusted : Finset ℕ := {3, 7, 11, 13, 31, 43, 61, 103, 127}
  let β (p : ℕ) : ℚ :=
    if p = 3 then 112 / 75 else
    if p = 7 then 512 / 411 else
    if p = 11 then 28 / 25 else
    if p = 13 then 448 / 411 else
    if p = 31 then 256 / 243 else
    if p = 43 then 77 / 75 else
    if p = 61 then 248 / 243 else
    if p = 103 then 416 / 411 else
    if p = 127 then 512 / 507 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1)
  refine reject_certified_weights hP ha he E hq (by decide) adjusted β
    ?_ ?_ (by norm_num [β]) ?_ ?_ ?_ (by norm_num [β]) (by norm_num [β])
  · intro c h
    simp only [adjusted, Finset.mem_insert, Finset.mem_singleton, not_or] at h
    simp [β, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2]
  · dsimp only [adjusted, β]
    decide +kernel
  · dsimp only [adjusted]
    decide +kernel
  · dsimp only [adjusted, β]
    decide +kernel
  · dsimp only [adjusted, β]
    decide +kernel

/-- For large enough a, 5 is the only possible simple supplier of 3. -/
private theorem remaining_source {a e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (ha : 11 ≤ a) (he : 2 ≤ e)
    (E : (2 ^ a + 1) * (1 + 257 ^ e) * ∏ p ∈ P, (p + 1) =
      2 ^ (a + 1) * 257 ^ e * ∏ p ∈ P, p) :
    5 ∈ P := by
  classical
  obtain ⟨source, -, unique, -, -, noSquare, -, -⟩ := facts hP (only_core_prime (e := e)) E
  have unique3 {p q} (hp : p ∈ P) (hq : q ∈ P) (hp3 : 3 ∣ p + 1) (hq3 : 3 ∣ q + 1) :
      p = q := unique 3 (by norm_num) (by decide) (by decide) p hp q hq hp3 hq3
  have no9 {p} (hp : p ∈ P) (h9 : 9 ∣ p + 1) : False :=
    noSquare 3 (by norm_num) (by decide) (by decide) p hp h9
  have no5 {p} (hp : p ∈ P) (hne : p ≠ 5) (h5 : 5 ∣ p + 1) (h3 : 3 ∣ p + 1) : False := by
    have h5P := source 5 (by norm_num) (by decide) (by decide) p hp h5
    exact hne (unique3 hp h5P h3 (by decide))
  by_cases existsQ : ∃ q ∈ P, 3 ∣ q + 1
  · obtain ⟨q,hq,hq3⟩ := existsQ
    by_cases hlarge : 71 ≤ q
    · exfalso
      refine reject_table hP ha he E ((4/3)*(72/70)) (4/3) (48/46)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
      dsimp only
      intro upper
      refine ⟨?_, fun _ _ _ _ h => (h rfl).elim, fun _ _ _ h => (h rfl).elim⟩
      intro p hp hp3 _
      have eq := unique3 hp hq hp3 hq3
      subst p
      have h := (upper q hq).trans (B_anti (by norm_num : 2 ≤ 71) hlarge)
      have hm := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℚ) ≤ 4 / 3)
      norm_num at hm ⊢
      exact hm
    have cases := small_source_cases (by omega : q < 71) (hP q hq).1 (hP q hq).2 hq3
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hq
    · exact (no_source_11 hP ha he E hq).elim
    · exact (no9 hq (by decide)).elim
    · exact (no_source_23 hP ha he E hq).elim
    · exact (no5 hq (by decide) (by decide) hq3).elim
    · exfalso
      refine reject_table hP ha he E ((4/3)*(42/40)) (8/7) (48/46)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
      dsimp only
      intro _
      refine ⟨?_, ?_, fun _ _ _ h => (h rfl).elim⟩
      · intro p hp hp3 _
        have eq := unique3 hp hq hp3 hq3
        subst p
        norm_num
      · intro p hp hp7 hn3 _
        have eq := unique 7 (by norm_num) (by decide) (by decide) p hp 41 hq hp7 (by decide)
        exact (hn3 (eq ▸ hq3)).elim
    · exfalso
      refine reject_table hP ha he E ((4/3)*((48/47)*(752/750))) (4/3) ((48/47)*(752/750))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
      dsimp only
      intro upper
      refine ⟨?_, fun _ _ _ _ h => (h rfl).elim, ?_⟩
      · intro p hp hp3 _
        have eq := unique3 hp hq hp3 hq3
        subst p
        norm_num
      · intro p hp hp47 _
        have hpne : p ≠ 47 := by
          intro eq
          rw [eq] at hp47
          norm_num at hp47
        have hn3 : ¬ 3 ∣ p + 1 := fun h => hpne (unique3 hp hq h hq3)
        have hmin := supplier_47_lower (hP p hp).1 (hP p hp).2 hp47 hn3
        have h := (upper p hp).trans (B_anti (by norm_num : 2 ≤ 751) hmin)
        have hm := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℚ) ≤ 48 / 47)
        norm_num at hm ⊢
        exact hm
    · exact (no9 hq (by decide)).elim
    · exact (no5 hq (by decide) (by decide) hq3).elim
  · exfalso
    refine reject_table hP ha he E (4/3) (4/3) (48/46)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    dsimp only
    intro _
    exact ⟨fun p hp hp3 _ => (existsQ ⟨p,hp,hp3⟩).elim,
      fun _ _ _ _ h => (h rfl).elim, fun _ _ _ h => (h rfl).elim⟩

/-- The case in which 19 supplies the factor 5. -/
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 257) →
    n.factorization 257 % 32 = 0 → padicValNat 2 n % 16 = 8 →
    5 ∣ n → 19 ∣ n → padicValNat 2 n ≤ A

/-- The case in which 5 has no supplier 19. -/
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 257) →
    n.factorization 257 % 32 = 0 → padicValNat 2 n % 16 = 8 →
    5 ∣ n → ¬ 19 ∣ n → padicValNat 2 n ≤ A

theorem main : H1 → H2 →
    OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1.H3 := by
  rintro ⟨A1,h1⟩ ⟨A2,h2⟩
  refine ⟨max 10 (max A1 A2), ?_⟩
  intro n h hS he32 ha16
  by_cases ha : 11 ≤ padicValNat 2 n
  · have hz : Nat.Prime 257 := by norm_num
    obtain ⟨hzn,hs⟩ := simple_of_unique_repeated h.2.ne' hS
    have hzpf : 257 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz,hzn,h.2.ne'⟩
    have he : 2 ≤ n.factorization 257 :=
      (hz.pow_dvd_iff_le_factorization h.2.ne').mp ((hS 257).mpr rfl).2.2
    obtain ⟨hP,E⟩ := kernel_balance_one h hzpf (by decide) hs
    rw [Nat.factorization_def n Nat.prime_two] at E
    have h5 := remaining_source hP ha he E
    have dvd5 : 5 ∣ n :=
      Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase (Finset.mem_filter.mp h5).1)
    by_cases h19 : 19 ∣ n
    · exact (h1 n h hS he32 ha16 dvd5 h19).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (h2 n h hS he32 ha16 dvd5 h19).trans ((le_max_right _ _).trans (le_max_right _ _))
  · exact (by omega : padicValNat 2 n ≤ 10).trans (le_max_left _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1_H3_R1
