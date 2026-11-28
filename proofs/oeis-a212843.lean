import OMAStatements.S_oeis_a212843
import Mathlib

namespace OMA.S_oeis_a212843

lemma binom_aux (u : ℕ) : ∀ k : ℕ, ∃ w : ℕ, (1 + u) ^ k = 1 + k * u + u ^ 2 * w := by
  intro k
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨k + w + u * w, by rw [pow_succ, hw]; ring⟩

lemma cop_aux (u d : ℕ) (hd : d ∣ u) : Nat.Coprime (1 + u) d := by
  have h : Nat.Coprime (1 + u) u := by
    first
      | exact Nat.coprime_add_self_left.2 (Nat.coprime_one_left u)
      | simp
  exact Nat.Coprime.coprime_dvd_right hd h

lemma sqfree_aux (C p : ℕ) (hp : p.Prime)
    (H : ∀ a : ℕ, Nat.Coprime a C → a ^ (C - 1) ≡ 1 [MOD C]) (hC : 1 < C) :
    ¬ p * p ∣ C := by
  rintro ⟨t, ht⟩
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h; omega
    · exact h
  have hcop : Nat.Coprime (1 + p * t) C := by
    have hC' : C = p * (p * t) := by rw [ht]; ring
    rw [hC']
    exact Nat.Coprime.mul_right (cop_aux _ _ (dvd_mul_right _ _)) (cop_aux _ _ dvd_rfl)
  have h1 := H _ hcop
  obtain ⟨w, hw⟩ := binom_aux (p * t) (C - 1)
  rw [hw] at h1
  have h2 : C ∣ (C - 1) * (p * t) + (p * t) ^ 2 * w := by
    have h3 : 1 + ((C - 1) * (p * t) + (p * t) ^ 2 * w) ≡ 1 + 0 [MOD C] := by
      simpa [add_assoc] using h1
    exact (Nat.modEq_zero_iff_dvd).1 (Nat.ModEq.add_left_cancel' 1 h3)
  have h4 : C ∣ (p * t) ^ 2 * w := ⟨t * w, by rw [ht]; ring⟩
  have h5 : C ∣ (C - 1) * (p * t) := (Nat.dvd_add_left h4).1 h2
  have hC' : C = p * (p * t) := by rw [ht]; ring
  have h5' : p * (p * t) ∣ (C - 1) * (p * t) := by rwa [← hC']
  have h6 : p ∣ (C - 1) := Nat.dvd_of_mul_dvd_mul_right (Nat.mul_pos hp.pos htpos) h5'
  have h7 : p ∣ C := ⟨p * t, hC'⟩
  have h8 : p ∣ C - (C - 1) := Nat.dvd_sub h7 h6
  have : C - (C - 1) = 1 := by omega
  rw [this] at h8
  exact hp.one_lt.ne' (Nat.dvd_one.1 h8)

lemma korselt_aux (C p : ℕ) (hp : p.Prime)
    (H : ∀ a : ℕ, Nat.Coprime a C → a ^ (C - 1) ≡ 1 [MOD C]) (hC : 1 < C) (hpC : p ∣ C) :
    (p - 1) ∣ (C - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := hpC
  have hsq := sqfree_aux C p hp H hC
  have hpm : Nat.Coprime p m := by
    rcases (Nat.coprime_or_dvd_of_prime hp m) with h | h
    · exact h
    · exfalso; apply hsq; rw [hm]; exact Nat.mul_dvd_mul_left p h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  obtain ⟨a, ha1, ha2⟩ := Nat.chineseRemainder hpm (g : ZMod p).val 1
  have hap : ((a : ℕ) : ZMod p) = (g : ZMod p) := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 ha1
    rw [this, ZMod.natCast_zmod_val]
  have hacop : Nat.Coprime a C := by
    rw [hm]
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro hd
      have h0 : ((a : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
      rw [hap] at h0
      exact g.ne_zero h0
    · have := ha2.gcd_eq
      rw [Nat.Coprime, this]
      simp
  have h1 := H a hacop
  have h2 : a ^ (C - 1) ≡ 1 [MOD p] := Nat.ModEq.of_dvd ⟨m, hm⟩ h1
  have h3 : ((a : ZMod p)) ^ (C - 1) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h2
    simpa using this
  rw [hap] at h3
  have h4 : g ^ (C - 1) = 1 := Units.ext (by simpa using h3)
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one h4

lemma prodmod10 (s : Finset ℕ) (h : ∀ q ∈ s, q % 10 = 1) : (∏ q ∈ s, q) % 10 = 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Nat.mul_mod, ih (fun q hq => h q (Finset.mem_insert_of_mem hq)),
      h x (Finset.mem_insert_self _ _)]

lemma prodmod30 (s : Finset ℕ) (h : ∀ q ∈ s, q % 30 = 1 ∨ q % 30 = 11) :
    (∏ q ∈ s, q) % 30 = 1 ∨ (∏ q ∈ s, q) % 30 = 11 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Nat.mul_mod]
    have h1 := ih (fun q hq => h q (Finset.mem_insert_of_mem hq))
    have h2 := h x (Finset.mem_insert_self _ _)
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> norm_num

lemma mulmod3 (A B D : ℕ) : (A * B * D) % 30 = ((A % 30) * (B % 30) % 30 * (D % 30)) % 30 := by
  rw [Nat.mul_mod, Nat.mul_mod A B]

lemma combo (C A B D : ℕ) (hC : C = A * B * D) (hA : 1 < A) (hB : 1 < B) (hD : 1 < D)
    (hA' : A % 30 = 1 ∨ A % 30 = 11) (hB' : B % 30 = 1 ∨ B % 30 = 11)
    (hD' : D % 30 = 1 ∨ D % 30 = 11)
    (h1 : ¬ (A % 30 = 11 ∧ B % 30 = 1 ∧ D % 30 = 1))
    (h2 : ¬ (A % 30 = 1 ∧ B % 30 = 11 ∧ D % 30 = 1))
    (h3 : ¬ (A % 30 = 1 ∧ B % 30 = 1 ∧ D % 30 = 11)) :
    (∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ C = (30 * a + 1) * (30 * b + 1) * (30 * c + 1)) ∨
      (∃ a b c : ℕ, C = (30 * a + 11) * (30 * b + 11) * (30 * c + 11)) ∨
      (∃ a b c : ℕ, 0 < a ∧ C = (30 * a + 1) * (30 * b + 11) * (30 * c + 11)) := by
  rcases hA' with hA' | hA' <;> rcases hB' with hB' | hB' <;> rcases hD' with hD' | hD'
  · left
    refine ⟨(A - 1) / 30, (B - 1) / 30, (D - 1) / 30, by omega, by omega, by omega, ?_⟩
    have e1 : 30 * ((A - 1) / 30) + 1 = A := by omega
    have e2 : 30 * ((B - 1) / 30) + 1 = B := by omega
    have e3 : 30 * ((D - 1) / 30) + 1 = D := by omega
    rw [e1, e2, e3, hC]
  · exact absurd ⟨hA', hB', hD'⟩ h3
  · exact absurd ⟨hA', hB', hD'⟩ h2
  · right; right
    refine ⟨(A - 1) / 30, (B - 11) / 30, (D - 11) / 30, by omega, ?_⟩
    have e1 : 30 * ((A - 1) / 30) + 1 = A := by omega
    have e2 : 30 * ((B - 11) / 30) + 11 = B := by omega
    have e3 : 30 * ((D - 11) / 30) + 11 = D := by omega
    rw [e1, e2, e3, hC]
  · exact absurd ⟨hA', hB', hD'⟩ h1
  · right; right
    refine ⟨(B - 1) / 30, (A - 11) / 30, (D - 11) / 30, by omega, ?_⟩
    have e1 : 30 * ((B - 1) / 30) + 1 = B := by omega
    have e2 : 30 * ((A - 11) / 30) + 11 = A := by omega
    have e3 : 30 * ((D - 11) / 30) + 11 = D := by omega
    rw [e1, e2, e3, hC]; ring
  · right; right
    refine ⟨(D - 1) / 30, (A - 11) / 30, (B - 11) / 30, by omega, ?_⟩
    have e1 : 30 * ((D - 1) / 30) + 1 = D := by omega
    have e2 : 30 * ((A - 11) / 30) + 11 = A := by omega
    have e3 : 30 * ((B - 11) / 30) + 11 = B := by omega
    rw [e1, e2, e3, hC]; ring
  · right; left
    refine ⟨(A - 11) / 30, (B - 11) / 30, (D - 11) / 30, ?_⟩
    have e1 : 30 * ((A - 11) / 30) + 11 = A := by omega
    have e2 : 30 * ((B - 11) / 30) + 11 = B := by omega
    have e3 : 30 * ((D - 11) / 30) + 11 = D := by omega
    rw [e1, e2, e3, hC]

lemma carm_cop (C : ℕ) (hC : 1 < C) (hn : ¬ C.Prime)
    (H : ∀ a : ℕ, Nat.Coprime a C → a ^ (C - 1) ≡ 1 [MOD C]) :
    Squarefree C ∧ 2 < C.primeFactors.card := by
  have hsf : Squarefree C := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro x hx
    exact sqfree_aux C x hx H hC
  refine ⟨hsf, ?_⟩
  have hprod := Nat.prod_primeFactors_of_squarefree hsf
  by_contra hle
  push_neg at hle
  have hc : C.primeFactors.card = 0 ∨ C.primeFactors.card = 1 ∨ C.primeFactors.card = 2 := by omega
  rcases hc with h | h | h
  · rw [Finset.card_eq_zero] at h
    rw [h] at hprod; simp at hprod; omega
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.1 h
    rw [hp] at hprod; simp at hprod
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hp]; simp)
    exact hn (by rw [← hprod]; exact hpp)
  · obtain ⟨p, q, hpq, hS⟩ := Finset.card_eq_two.1 h
    rw [hS] at hprod
    rw [Finset.prod_pair hpq] at hprod
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hS]; simp)
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hS]; simp)
    have h1 := korselt_aux C p hpp H hC (by rw [← hprod]; exact dvd_mul_right _ _)
    have h2 := korselt_aux C q hqp H hC (by rw [← hprod]; exact dvd_mul_left _ _)
    have hp2 := hpp.two_le
    have hq2 := hqp.two_le
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have e1 : C - 1 = p' * (q' + 1) + q' := by
      rw [← hprod]; have : (p' + 1) * (q' + 1) = p' * (q' + 1) + q' + 1 := by ring
      omega
    have e2 : C - 1 = q' * (p' + 1) + p' := by
      rw [← hprod]; have : (p' + 1) * (q' + 1) = q' * (p' + 1) + p' + 1 := by ring
      omega
    simp only [Nat.add_sub_cancel] at h1 h2
    rw [e1] at h1; rw [e2] at h2
    have h3 : p' ∣ q' := (Nat.dvd_add_right (dvd_mul_right _ _)).1 h1
    have h4 : q' ∣ p' := (Nat.dvd_add_right (dvd_mul_right _ _)).1 h2
    have : p' = q' := Nat.dvd_antisymm h3 h4
    exact hpq (by rw [this])

end OMA.S_oeis_a212843

theorem OMA.solution : type_of% @OMA.S_oeis_a212843.main := by
  open OMA.S_oeis_a212843 in
  refine ⟨?_, ?_, ?_⟩
  · rintro C ⟨hC, hn, H⟩ hall
    obtain ⟨hsf, _⟩ := carm_cop C hC hn H
    rw [← Nat.prod_primeFactors_of_squarefree hsf]
    apply prodmod10
    intro q hq
    exact hall q (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)
  · refine ⟨561, ⟨by norm_num, by norm_num, ?_⟩, by norm_num, 3, by norm_num, by norm_num, by norm_num⟩
    intro a ha
    have key : ∀ r < 561, Nat.Coprime r 561 → r ^ 560 % 561 = 1 := by decide +kernel
    have hr : Nat.Coprime (a % 561) 561 := by
      rw [Nat.Coprime, ← Nat.gcd_rec]; exact Nat.coprime_comm.1 ha
    show a ^ 560 % 561 = 1 % 561
    rw [Nat.pow_mod]
    exact key _ (Nat.mod_lt _ (by norm_num)) hr
  · rintro C ⟨hC, hn, H⟩ hall
    obtain ⟨hsf, hcard⟩ := carm_cop C hC hn H
    have hprod := Nat.prod_primeFactors_of_squarefree hsf
    have hcls : ∀ q ∈ C.primeFactors, q % 30 = 1 ∨ q % 30 = 11 := by
      intro q hq
      have hqp := Nat.prime_of_mem_primeFactors hq
      have h10 := hall q hqp (Nat.dvd_of_mem_primeFactors hq)
      have h3 : q % 3 ≠ 0 := by
        intro h
        have : 3 ∣ q := Nat.dvd_of_mod_eq_zero h
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hqp).1 this
        omega
      omega
    have hc1 : ∀ q ∈ C.primeFactors, q % 30 = 1 → C % 30 = 1 := by
      intro q hq hq1
      have := korselt_aux C q (Nat.prime_of_mem_primeFactors hq) H hC (Nat.dvd_of_mem_primeFactors hq)
      have h30 : 30 ∣ q - 1 := by omega
      have := dvd_trans h30 this
      omega
    obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.1 hcard
    have hsub : ({x, y, z} : Finset ℕ) ⊆ C.primeFactors := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> assumption
    have hsplit := Finset.prod_sdiff hsub (f := fun q => q)
    rw [hprod] at hsplit
    have h3 : ∏ q ∈ ({x, y, z} : Finset ℕ), q = x * (y * z) := by
      rw [Finset.prod_insert (by simp [hxy, hxz]), Finset.prod_pair hyz]
    rw [h3] at hsplit
    obtain ⟨R, hR⟩ : ∃ R, R = ∏ q ∈ C.primeFactors \ {x, y, z}, q := ⟨_, rfl⟩
    rw [← hR] at hsplit
    have hRcls := prodmod30 (C.primeFactors \ {x, y, z}) (fun q hq => hcls q (Finset.mem_sdiff.1 hq).1)
    rw [← hR] at hRcls
    have hRpos : 0 < R := by
      rw [hR]; apply Finset.prod_pos
      intro q hq
      exact (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.1 hq).1).pos
    have hxp := Nat.prime_of_mem_primeFactors hx
    have hyp := Nat.prime_of_mem_primeFactors hy
    have hzp := Nat.prime_of_mem_primeFactors hz
    have hGx : 1 < x * R := by
      have := hxp.two_le
      nlinarith
    have hGcls : (x * R) % 30 = 1 ∨ (x * R) % 30 = 11 := by
      rw [Nat.mul_mod]
      rcases hcls x hx with h | h <;> rcases hRcls with h' | h' <;> rw [h, h'] <;> norm_num
    have hCeq : C = (x * R) * y * z := by rw [← hsplit]; ring
    have hmod := mulmod3 (x * R) y z
    rw [← hCeq] at hmod
    refine combo C (x * R) y z hCeq hGx hyp.one_lt hzp.one_lt hGcls (hcls y hy) (hcls z hz) ?_ ?_ ?_
    · rintro ⟨h1, h2, h3⟩
      have := hc1 y hy h2
      rw [h1, h2, h3] at hmod; omega
    · rintro ⟨h1, h2, h3⟩
      have := hc1 z hz h3
      rw [h1, h2, h3] at hmod; omega
    · rintro ⟨h1, h2, h3⟩
      have := hc1 y hy h2
      rw [h1, h2, h3] at hmod; omega
