import OMAReductions.R_Erdos647_erdos_647_variants_infinite_R1
import Mathlib

/-! Divisor counts in six fixed positions determine the admissible residue class. -/

open Finset
open scoped BigOperators

namespace OMA.DivisorWindows

private def offsets : Finset ℕ := {1, 2, 3, 4, 6, 12}

private def Good (n : ℕ) : Prop :=
  ∀ j ∈ offsets, (n - j).divisors.card ≤ j + 2

private instance (n : ℕ) : Decidable (Good n) :=
  inferInstanceAs (Decidable (∀ j ∈ offsets, (n - j).divisors.card ≤ j + 2))

private theorem doubled_divisors {m d : ℕ} (h : d ∣ m) (hm : d ^ 2 < m) :
    2 * d.divisors.card ≤ m.divisors.card := by
  have hm0 : m ≠ 0 := by omega
  have hd : 0 < d := by
    by_contra! h0
    have he : d = 0 := by omega
    exact hm0 (by simpa [he] using h)
  let a := m / d
  have he : a * d = m := Nat.div_mul_cancel h
  have had : d < a := by
    by_contra! hn
    have hmul := Nat.mul_le_mul_right d hn
    rw [he, ← pow_two] at hmul
    omega
  have ha0 : 0 < a := hd.trans had
  let V := d.divisors
  let W := V.image (fun q => a*q)
  have hw : W ⊆ m.divisors := by
    intro v hv
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hv
    have hvd := Nat.mul_dvd_mul_left a (Nat.dvd_of_mem_divisors hq)
    exact Nat.mem_divisors.mpr ⟨he ▸ hvd, hm0⟩
  have hv : V ⊆ m.divisors := Nat.divisors_subset_of_dvd hm0 h
  have hdisj : Disjoint V W := by
    apply Finset.disjoint_left.mpr
    intro q hq hqw
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hqw
    exact (not_lt_of_ge (Nat.divisor_le hq))
      (had.trans_le (Nat.le_mul_of_pos_right a (Nat.pos_of_mem_divisors hr)))
  have hcard : W.card = V.card := by
    apply Finset.card_image_iff.mpr
    intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left ha0 hxy
  have hc := card_le_card (union_subset hv hw)
  rw [card_union_of_disjoint hdisj, hcard] at hc
  simpa only [two_mul] using hc

private theorem offset_le {j : ℕ} (hj : j ∈ offsets) : j ≤ 12 := by
  simp [offsets] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private theorem offset_pos {j : ℕ} (hj : j ∈ offsets) : 0 < j := by
  simp [offsets] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private theorem bound_of_dvd {n j d : ℕ} (_hn : 24 < n) (hg : Good n) (hj : j ∈ offsets)
    (hdiv : d ∣ n-j) (hlim : j+2 < 2*d.divisors.card) : n ≤ j+d^2 := by
  have hjn := offset_le hj
  by_contra! hb
  have hd := doubled_divisors hdiv (by omega : d^2 < n-j)
  exact (not_lt_of_ge ((hg j hj).trans' hd)) hlim

private theorem certify {n m L p : ℕ} (check : ∀ t : Fin L, 24 < m*t.val → Good (m*t.val) → p ∣ m*t.val)
    (hn : 24 < n) (hg : Good n) (hm : m ∣ n) (hbound : n < m*L) : p ∣ n := by
  obtain ⟨t, rfl⟩ := hm
  have ht : t < L := by
    by_contra! h
    exact (not_le_of_gt hbound) (Nat.mul_le_mul_left m h)
  exact check ⟨t, ht⟩ hn hg

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem small3 : ∀ t : Fin 10, 24 < 4*t.val → Good (4*t.val) → 3 ∣ 4*t.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem small5 : ∀ t : Fin 34, 24 < 12*t.val → Good (12*t.val) → 5 ∣ 12*t.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem small8 : ∀ t : Fin 2, 24 < 60*t.val → Good (60*t.val) → 8 ∣ 60*t.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem small9 : ∀ t : Fin 3, 24 < 120*t.val → Good (120*t.val) → 9 ∣ 120*t.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem small7 : ∀ t : Fin 20, 24 < 360*t.val → Good (360*t.val) → 7 ∣ 360*t.val := by decide +kernel

private theorem force_of_cover {n m p L : ℕ} (hn : 24 < n) (hg : Good n) (hm : m ∣ n)
    (hp : 0 < p) (hnot : ¬ p ∣ n)
    (cover : ∀ r : Fin p, 0 < r.val → ∃ j ∈ offsets,
      r.val = j%p ∧ j∣m ∧ j.Coprime p ∧ j+2 < 2*(j*p).divisors.card ∧ j+(j*p)^2 ≤ L) :
    n ≤ L := by
  have hr : 0 < n%p := Nat.pos_of_ne_zero (fun h => hnot (Nat.dvd_of_mod_eq_zero h))
  obtain ⟨j, hj, he, hjm, hcop, hlim, hL⟩ := cover ⟨n%p, Nat.mod_lt _ hp⟩ hr
  have hjn : j ≤ n := by have := offset_le hj; omega
  have hjdiff : j ∣ n-j := Nat.dvd_sub (hjm.trans hm) (dvd_refl j)
  have hpdiff : p ∣ n-j := (show j ≡ n [MOD p] from he.symm).dvd'
  exact (bound_of_dvd hn hg hj (hcop.mul_dvd_of_dvd_of_dvd hjdiff hpdiff) hlim).trans hL

private theorem cover5 : ∀ r : Fin 5, 0 < r.val → ∃ j ∈ offsets,
    r.val = j%5 ∧ j∣12 ∧ j.Coprime 5 ∧ j+2 < 2*(j*5).divisors.card ∧ j+(j*5)^2 ≤ 404 := by
  decide +kernel

private theorem cover7 : ∀ r : Fin 7, 0 < r.val → ∃ j ∈ offsets,
    r.val = j%7 ∧ j∣360 ∧ j.Coprime 7 ∧ j+2 < 2*(j*7).divisors.card ∧ j+(j*7)^2 ≤ 7068 := by
  decide +kernel

private theorem nine_remainders {r : ℕ} (hr : r < 9) (h0 : r ≠ 0) (h3 : r%3 = 0) :
    r = 3 ∨ r = 6 := by omega

private theorem four_remainder {r : ℕ} (hr : r < 4) (h0 : r ≠ 0) (h2 : r%2 = 0) :
    r = 2 := by omega

private theorem eight_remainder {r : ℕ} (hr : r < 8) (h0 : r ≠ 0) (h4 : r%4 = 0) :
    r = 4 := by omega

set_option maxHeartbeats 400000 in
private theorem large_multiple {n : ℕ} (hn : 24 < n) (hg : Good n) : 2520 ∣ n := by
  have h2 : 2 ∣ n := by
    by_contra h2
    have hd : 2 ∣ n-1 := by simp only [Nat.dvd_iff_mod_eq_zero] at *; omega
    have hb := bound_of_dvd hn hg (show 1 ∈ offsets by decide) hd (by decide)
    omega
  have h4 : 4 ∣ n := by
    by_contra h4
    have hm := (Nat.mod_mod_of_dvd n (by decide : 2∣4)).trans (Nat.mod_eq_zero_of_dvd h2)
    have hv := four_remainder (Nat.mod_lt n (by decide)) (fun h => h4 (Nat.dvd_of_mod_eq_zero h)) hm
    have hd : 4 ∣ n-2 := (show 2 ≡ n [MOD 4] from hv.symm).dvd'
    have hb := bound_of_dvd hn hg (show 2 ∈ offsets by decide) hd (by decide)
    omega
  have h3 : 3 ∣ n := by
    by_contra h3
    have hcases : n%3=1 ∨ n%3=2 := by
      simp only [Nat.dvd_iff_mod_eq_zero] at h3
      have := Nat.mod_lt n (by decide : 0<3)
      omega
    rcases hcases with h1 | h2'
    · have hd : 3 ∣ n-1 := (show 1 ≡ n [MOD 3] from h1.symm).dvd'
      have hb := bound_of_dvd hn hg (show 1 ∈ offsets by decide) hd (by decide)
      omega
    · have hd₂ : 2 ∣ n-2 := Nat.dvd_sub h2 (dvd_refl 2)
      have hd₃ : 3 ∣ n-2 := (show 2 ≡ n [MOD 3] from h2'.symm).dvd'
      have hd : 6 ∣ n-2 := (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd hd₂ hd₃
      have hb := bound_of_dvd hn hg (show 2 ∈ offsets by decide) hd (by decide)
      exact h3 (certify small3 hn hg h4 (hb.trans_lt (by decide)))
  have h12 : 12 ∣ n := (by decide : Nat.Coprime 4 3).mul_dvd_of_dvd_of_dvd h4 h3
  have h5 : 5 ∣ n := by
    by_contra h5
    have hb := force_of_cover hn hg h12 (by decide) h5 cover5
    exact h5 (certify small5 hn hg h12 (hb.trans_lt (by decide)))
  have h60 : 60 ∣ n := (by decide : Nat.Coprime 12 5).mul_dvd_of_dvd_of_dvd h12 h5
  have h8 : 8 ∣ n := by
    by_contra h8
    have hm := (Nat.mod_mod_of_dvd n (by decide : 4∣8)).trans (Nat.mod_eq_zero_of_dvd h4)
    have hv := eight_remainder (Nat.mod_lt n (by decide)) (fun h => h8 (Nat.dvd_of_mod_eq_zero h)) hm
    have hd : 8 ∣ n-4 := (show 4 ≡ n [MOD 8] from hv.symm).dvd'
    have hb := bound_of_dvd hn hg (show 4 ∈ offsets by decide) hd (by decide)
    exact h8 (certify small8 hn hg h60 (hb.trans_lt (by decide)))
  have h15 : 15 ∣ n := (by decide : 15 ∣ 60).trans h60
  have h120 : 120 ∣ n := (by decide : Nat.Coprime 15 8).mul_dvd_of_dvd_of_dvd h15 h8
  have h9 : 9 ∣ n := by
    by_contra h9
    have hcases : n%9=3 ∨ n%9=6 := by
      simp only [Nat.dvd_iff_mod_eq_zero] at h9 h3
      have hm := Nat.mod_mod_of_dvd n (by decide : 3∣9)
      exact nine_remainders (Nat.mod_lt _ (by decide)) h9 (hm.trans h3)
    rcases hcases with h3' | h6
    · have hd : 9 ∣ n-3 := (show 3 ≡ n [MOD 9] from h3'.symm).dvd'
      have hb := bound_of_dvd hn hg (show 3 ∈ offsets by decide) hd (by decide)
      exact h9 (certify small9 hn hg h120 (hb.trans_lt (by decide)))
    · have hd₂ : 2 ∣ n-6 := Nat.dvd_sub h2 (by decide)
      have hd₉ : 9 ∣ n-6 := (show 6 ≡ n [MOD 9] from h6.symm).dvd'
      have hd : 18 ∣ n-6 := (by decide : Nat.Coprime 2 9).mul_dvd_of_dvd_of_dvd hd₂ hd₉
      have hb := bound_of_dvd hn hg (show 6 ∈ offsets by decide) hd (by decide)
      exact h9 (certify small9 hn hg h120 (hb.trans_lt (by decide)))
  have h40 : 40 ∣ n := (by decide : 40∣120).trans h120
  have h360 : 360 ∣ n := (by decide : Nat.Coprime 40 9).mul_dvd_of_dvd_of_dvd h40 h9
  have h7 : 7 ∣ n := by
    by_contra h7
    have hb := force_of_cover hn hg h360 (by decide) h7 cover7
    exact h7 (certify small7 hn hg h360 (hb.trans_lt (by decide)))
  exact (by decide : Nat.Coprime 360 7).mul_dvd_of_dvd_of_dvd h360 h7


private theorem prime_of_two_divisors {m : ℕ} (hm : 1 < m) (hc : m.divisors.card ≤ 2) :
    m.Prime := by
  refine Nat.prime_def_lt'.2 ⟨hm, ?_⟩
  intro a ha ham hd
  let T : Finset ℕ := {1, a, m}
  have hsub : T ⊆ m.divisors := by
    intro q hq
    simp only [T, mem_insert, mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨one_dvd _, by omega⟩
    · exact Nat.mem_divisors.mpr ⟨hd, by omega⟩
    · exact Nat.mem_divisors.mpr ⟨dvd_refl _, by omega⟩
  have hcard : T.card = 3 := by
    simp [T, show (1 : ℕ) ≠ a by omega, show (1 : ℕ) ≠ m by omega, ham.ne]
  have := card_le_card hsub
  omega

private theorem prime_of_three_divisors {m : ℕ} (hm : 1 < m) (hr : m%4 = 3)
    (hc : m.divisors.card ≤ 3) : m.Prime := by
  refine Nat.prime_iff_not_exists_mul_eq.mpr ⟨hm, ?_⟩
  rintro ⟨a, b, ham, hbm, hmul⟩
  have ha : 2 ≤ a := by
    by_contra! h
    have h' : a = 0 ∨ a = 1 := by omega
    rcases h' with rfl | rfl <;> simp_all
  have hb : 2 ≤ b := by
    by_contra! h
    have h' : b = 0 ∨ b = 1 := by omega
    rcases h' with rfl | rfl <;> simp_all
  have hab : a ≠ b := by
    intro he
    rw [← hmul, ← he, Nat.mul_mod] at hr
    have hh : ∀ k : Fin 4, (k.val*k.val)%4 ≠ 3 := by decide +kernel
    exact hh ⟨a%4, Nat.mod_lt _ (by decide)⟩ hr
  let T : Finset ℕ := {1, a, b, m}
  have hsub : T ⊆ m.divisors := by
    intro q hq
    simp only [T, mem_insert, mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨one_dvd _, by omega⟩
    · exact Nat.mem_divisors.mpr ⟨⟨b, hmul.symm⟩, by omega⟩
    · exact Nat.mem_divisors.mpr ⟨⟨a, by rw [mul_comm, hmul]⟩, by omega⟩
    · exact Nat.mem_divisors.mpr ⟨dvd_refl _, by omega⟩
  have hcard : T.card = 4 := by
    simp [T, show (1 : ℕ) ≠ a by omega, show (1 : ℕ) ≠ b by omega,
      show (1 : ℕ) ≠ m by omega, hab, ham.ne, hbm.ne]
  have := card_le_card hsub
  omega

private theorem factor_guard : ∀ j : Fin 13, j.val ∈ offsets →
    j.val ∣ 2520 ∧ 210 ≤ 2520 / j.val ∧ 2*j.val.divisors.card ≤ j.val+2 ∧
      (j.val ≠ 1 → j.val+2 < 3*j.val.divisors.card) := by decide +kernel

private theorem prime_guard : ∀ j p : Fin 13, j.val ∈ offsets → p.val.Prime → p.val∣j.val →
    p.val ∣ 2520/j.val := by decide +kernel

private theorem quotient_data {t j : ℕ} (ht : 0 < t) (hj : j ∈ offsets) :
    let q := (2520/j)*t - 1
    2520*t-j = j*q ∧ j.Coprime q ∧ 1 < q := by
  let q := (2520/j)*t - 1
  have hj' := factor_guard ⟨j, by have := offset_le hj; omega⟩ hj
  have hbig : 210 ≤ (2520/j)*t := hj'.2.1.trans (Nat.le_mul_of_pos_right _ ht)
  refine ⟨?_, ?_, by omega⟩
  · have hjmul : j*(2520/j) = 2520 := Nat.mul_div_cancel' hj'.1
    change 2520*t-j = j*((2520/j)*t-1)
    rw [Nat.mul_sub, ← Nat.mul_assoc, hjmul, Nat.mul_one]
  · by_contra h
    obtain ⟨p, hp, hpj, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have hpj' : p ≤ j := Nat.le_of_dvd (offset_pos hj) hpj
    have hpB := prime_guard ⟨j, by have := offset_le hj; omega⟩
      ⟨p, by have := offset_le hj; omega⟩ hj hp hpj
    have hd := Nat.dvd_sub (dvd_mul_of_dvd_left hpB t) hpq
    have hd1 : (2520/j)*t-q = 1 := by dsimp only [q]; omega
    rw [hd1] at hd
    exact hp.ne_one (Nat.dvd_one.mp hd)

theorem classify (n : ℕ) (hn : 24 < n) :
    ((∀ j ∈ ({1, 2, 3, 4, 6, 12} : Finset ℕ), (n - j).divisors.card ≤ j + 2) ↔
      ∃ t : ℕ, 0 < t ∧ n = 2520 * t ∧
        ∀ j ∈ ({1, 2, 3, 4, 6, 12} : Finset ℕ), ((2520 / j) * t - 1).Prime) := by
  constructor
  · intro h
    have hg : Good n := h
    obtain ⟨t, rfl⟩ := large_multiple hn hg
    have ht : 0 < t := by omega
    refine ⟨t, ht, rfl, ?_⟩
    intro j hj
    let q := (2520/j)*t - 1
    have hdata : 2520*t-j = j*q ∧ j.Coprime q ∧ 1 < q := quotient_data ht hj
    have hcard := hg j hj
    rw [hdata.1, Nat.Coprime.card_divisors_mul hdata.2.1] at hcard
    by_cases h1 : j = 1
    · subst j
      apply prime_of_three_divisors hdata.2.2
      · change ((2520 / 1) * t - 1)%4 = 3
        norm_num
        omega
      · simpa using hcard
    · apply prime_of_two_divisors hdata.2.2
      by_contra! hb
      have hj' : j + 2 < 3 * j.divisors.card :=
        (factor_guard ⟨j, by have := offset_le hj; omega⟩ hj).2.2.2 h1
      have hc : 3 * j.divisors.card ≤ j.divisors.card * q.divisors.card := by
        rw [Nat.mul_comm 3]
        exact Nat.mul_le_mul_left j.divisors.card (by omega)
      exact (not_lt_of_ge (hc.trans hcard)) hj'
  · rintro ⟨t, ht, rfl, h⟩ j hj
    let q := (2520/j)*t - 1
    have hdata : 2520*t-j = j*q ∧ j.Coprime q ∧ 1 < q := quotient_data ht hj
    have hp : q.Prime := h j hj
    have hq : q.divisors.card = 2 := by rw [hp.divisors]; simp [hp.ne_one.symm]
    rw [hdata.1, Nat.Coprime.card_divisors_mul hdata.2.1, hq, Nat.mul_comm]
    exact (factor_guard ⟨j, by have := offset_le hj; omega⟩ hj).2.2.1

end OMA.DivisorWindows

theorem OMA.solution : OMA.R_Erdos647_erdos_647_variants_infinite_R1.H2 :=
  OMA.DivisorWindows.classify