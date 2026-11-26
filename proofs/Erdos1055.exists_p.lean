import FormalConjectures.ErdosProblems.«1055»

-- Problem: Erdős Problem 1055 — exists p
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1055.lean:54 (declaration Erdos1055.exists_p)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
--
-- Strategy. Unfold `IsOfClass` into its base and successor cases. Classes are unique, every prime
-- has a class (strong induction: take one more than the largest class of a prime factor of p+1),
-- and a prime of class n+1 yields a prime of class n. By Dirichlet, for a prime q ∉ {2,3} of
-- class c there is a prime p ≡ -1 (mod q), whose class exceeds c. So classes are unbounded, and
-- stepping down gives every class.

open Erdos1055

namespace OMA.Erdos1055

lemma sio {P : ℕ+ → Sort*} (n : ℕ+) (IH : ∀ k, (∀ m, m < k → P m) → P k) :
    PNat.strongInductionOn n IH = IH n (fun a _ => PNat.strongInductionOn a IH) := by
  rw [PNat.strongInductionOn]

lemma cls_one (p : ℕ) : IsOfClass 1 p ↔ (p + 1).primeFactors ⊆ {2, 3} := by
  unfold IsOfClass PNat.caseStrongInductionOn
  rw [PNat.strongInductionOn]
  rfl

lemma cls_succ (n : ℕ+) (p : ℕ) : IsOfClass (n + 1) p ↔
    ((∀ m ≤ n, ¬ IsOfClass m p) ∧
      (∀ q ∈ (p + 1).primeFactors, ∃ m, ∃ _ : m ≤ n, IsOfClass m q) ∧
      (∃ q ∈ (p + 1).primeFactors, ∀ m ≤ n, IsOfClass m q → m = n)) := by
  obtain ⟨_ | k, hk⟩ := n
  · omega
  show IsOfClass ⟨k + 2, by omega⟩ p ↔ _
  unfold IsOfClass PNat.caseStrongInductionOn
  refine (iff_of_eq (congrFun (sio (P := fun _ : ℕ+ => ℕ → Prop) ⟨k + 2, by omega⟩ _) p)).trans ?_
  rfl

lemma cls_uniq_aux {a b : ℕ+} {p : ℕ} (hab : a < b) (ha : IsOfClass a p) (hb : IsOfClass b p) :
    False := by
  have hb1 : b ≠ 1 := by
    rintro rfl; exact absurd hab (not_lt.2 (by simp))
  obtain ⟨n, rfl⟩ := PNat.exists_eq_succ_of_ne_one hb1
  rw [cls_succ] at hb
  exact hb.1 a (PNat.lt_add_one_iff.1 hab) ha

lemma cls_uniq {a b : ℕ+} {p : ℕ} (ha : IsOfClass a p) (hb : IsOfClass b p) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact (cls_uniq_aux h ha hb).elim
  · exact h
  · exact (cls_uniq_aux h hb ha).elim

lemma exists_cls : ∀ p : ℕ, p.Prime → ∃ r, IsOfClass r p := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  intro hp
  by_cases h23 : (p + 1).primeFactors ⊆ {2, 3}
  · exact ⟨1, (cls_one p).2 h23⟩
  have hlt : ∀ q ∈ (p + 1).primeFactors, q < p := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    have hle := Nat.le_of_dvd (by omega) hqd
    have hne : q ≠ p := by
      rintro rfl
      have : q ∣ 1 := (Nat.dvd_add_right (dvd_refl q)).1 hqd
      exact hqp.one_lt.ne' (Nat.dvd_one.1 this)
    have hne' : q ≠ p + 1 := by
      rintro rfl
      apply h23
      rcases hp.eq_two_or_odd' with rfl | ho
      · intro x hx
        rw [Nat.Prime.primeFactors hqp] at hx
        simp at hx; simp [hx]
      · rcases hqp.eq_two_or_odd' with h2 | ho2
        · exfalso; have := hp.two_le; omega
        · exfalso
          obtain ⟨a, ha⟩ := ho; obtain ⟨b, hb⟩ := ho2; omega
    omega
  have hcl : ∀ q ∈ (p + 1).primeFactors, ∃ r, IsOfClass r q := fun q hq =>
    ih q (hlt q hq) (Nat.prime_of_mem_primeFactors hq)
  choose! c hc using hcl
  have hne : ((p + 1).primeFactors).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; rintro h; rw [h] at h23; exact h23 (Finset.empty_subset _)
  set M := ((p + 1).primeFactors).sup' hne c with hM
  by_cases hex : ∃ m ≤ M, IsOfClass m p
  · obtain ⟨m, -, hm⟩ := hex; exact ⟨m, hm⟩
  push Not at hex
  refine ⟨M + 1, (cls_succ M p).2 ⟨fun m hm h => hex m hm h, ?_, ?_⟩⟩
  · intro q hq
    exact ⟨c q, Finset.le_sup' c hq, hc q hq⟩
  · obtain ⟨q₀, hq₀, hq₀M⟩ := Finset.exists_mem_eq_sup' hne c
    refine ⟨q₀, hq₀, fun m _ hm => ?_⟩
    rw [hM, hq₀M]
    exact cls_uniq hm (hc q₀ hq₀)

lemma cls_lower {p q : ℕ} {c r : ℕ+} (hq : q ∈ (p + 1).primeFactors) (h23 : q ∉ ({2, 3} : Finset ℕ))
    (hc : IsOfClass c q) (hr : IsOfClass r p) : c < r := by
  by_cases hr1 : r = 1
  · subst hr1
    exact absurd ((cls_one p).1 hr hq) h23
  obtain ⟨n, rfl⟩ := PNat.exists_eq_succ_of_ne_one hr1
  obtain ⟨m, hmn, hm⟩ := ((cls_succ n p).1 hr).2.1 q hq
  rw [cls_uniq hc hm]
  exact PNat.lt_add_one_iff.2 hmn

lemma cls_down {n : ℕ+} {p : ℕ} (h : IsOfClass (n + 1) p) : ∃ q, q.Prime ∧ IsOfClass n q := by
  obtain ⟨-, h2, q, hq, h3⟩ := (cls_succ n p).1 h
  obtain ⟨m, hmn, hm⟩ := h2 q hq
  exact ⟨q, Nat.prime_of_mem_primeFactors hq, h3 m hmn hm ▸ hm⟩

lemma cls_unbounded (r : ℕ+) : ∃ p, p.Prime ∧ ∃ s, r ≤ s ∧ IsOfClass s p := by
  induction r using PNat.recOn with
  | one =>
    refine ⟨2, Nat.prime_two, 1, le_rfl, (cls_one 2).2 ?_⟩
    rw [show (2 + 1 : ℕ) = 3 by rfl, Nat.Prime.primeFactors Nat.prime_three]
    simp
  | succ r ih =>
    obtain ⟨p, hp, s, hrs, hs⟩ := ih
    -- find a prime q ∉ {2,3} with class c ≥ r
    obtain ⟨q, hq, h23, c, hrc, hc⟩ : ∃ q, q.Prime ∧ q ∉ ({2, 3} : Finset ℕ) ∧
        ∃ c, r ≤ c ∧ IsOfClass c q := by
      by_cases hs1 : s = 1
      · subst hs1
        refine ⟨5, by norm_num, by decide, 1, hrs, (cls_one 5).2 ?_⟩
        rw [show (5 + 1 : ℕ) = 2 * 3 by rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
          Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
        intro x; simp
      · refine ⟨p, hp, ?_, s, hrs, hs⟩
        intro hp23
        apply hs1
        refine cls_uniq hs ((cls_one p).2 ?_)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp23
        rcases hp23 with rfl | rfl
        · rw [show (2 + 1 : ℕ) = 3 by rfl, Nat.Prime.primeFactors Nat.prime_three]; simp
        · rw [show (3 + 1 : ℕ) = 2 ^ 2 by rfl, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
          simp
    have : NeZero q := ⟨hq.ne_zero⟩
    obtain ⟨p', -, hp', hmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod
      (q := q) (a := -1) isUnit_one.neg 0
    have hdvd : q ∣ p' + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast; rw [hmod]; ring
    have hmem : q ∈ (p' + 1).primeFactors :=
      Nat.mem_primeFactors.2 ⟨hq, hdvd, by omega⟩
    obtain ⟨r', hr'⟩ := exists_cls p' hp'
    refine ⟨p', hp', r', ?_, hr'⟩
    have := cls_lower hmem h23 hc hr'
    exact PNat.add_one_le_iff.2 (lt_of_le_of_lt hrc this)

theorem exists_p_main (r : ℕ+) : ∃ p, p.Prime ∧ IsOfClass r p := by
  obtain ⟨p, hp, s, hrs, hs⟩ := cls_unbounded r
  have key : ∀ d : ℕ, ∀ s : ℕ+, (s : ℕ) = r + d → (∃ p, p.Prime ∧ IsOfClass s p) →
      ∃ p, p.Prime ∧ IsOfClass r p := by
    intro d
    induction d with
    | zero =>
      intro s hs h
      have : s = r := PNat.eq (by simpa using hs)
      exact this ▸ h
    | succ d ih =>
      intro s hs ⟨p, hp, h⟩
      obtain ⟨n, hn⟩ : ∃ n : ℕ+, (n : ℕ) = r + d := ⟨⟨r + d, by positivity⟩, rfl⟩
      have hsn : s = n + 1 := PNat.eq (by rw [PNat.add_coe, hn, hs]; simp; ring)
      rw [hsn] at h
      exact ih n hn (cls_down h)
  exact key ((s : ℕ) - r) s (by have := PNat.coe_le_coe r s |>.2 hrs; omega) ⟨p, hp, hs⟩

end OMA.Erdos1055

theorem OMA.solution : type_of% @Erdos1055.exists_p := OMA.Erdos1055.exists_p_main
