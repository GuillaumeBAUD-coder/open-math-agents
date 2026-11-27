import FormalConjectures.ErdosProblems.«703»
import Mathlib

-- Problem: Erdős Problem 703 — frankl furedi
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/703.lean:113 (declaration Erdos703.erdos_703.variants.frankl_furedi)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: formalization of P. Frankl and Z. Füredi, On hypergraphs without two edges intersecting
-- in a given number of vertices, J. Combin. Theory Ser. A 36 (1984) 230-236, including the
-- Frankl–Singhi rank theorem (Theorem 1.4) and the shadow bound (Theorem 1.5) it relies on.

/-!
# Frankl–Füredi: families avoiding one intersection size

Fix `t`. For `n` large, a family of subsets of an `n`-set with no two members (equal or not)
meeting in exactly `t` points has at most as many members as the family of all sets of size
`< t` together with the Katona family of sets meeting pairwise in more than `t` points.

* `fs_card_le`: Frankl–Singhi. For `h`-sets avoiding intersection `t`, where `h - t` has a prime
  power divisor `q > t`, the rows of the inclusion matrix against `(h-t-1)`-sets are independent
  over `ℤ` (a mod `p` argument with the test polynomial `choose (x - t - 1) (h - t - 1)`), so the
  family is no larger than its `(h-t-1)`-shadow.
* `shadow_good`: applying this to every link gives `h |F| ≤ (h - t) |∂_{h-t} F|`.
* `pair_disj`: the `(i-t)`-shadow of the `i`-sets and the complements of the `(n+t-i)`-sets are
  disjoint; with the shadow bound this pairs level `i` with level `n + t - i`.
* `upper`: summing over the pairs; a member of small size forces exponentially many excluded
  sets at the top pair, which beats the polynomially many small sets.
-/

open Finset

namespace OMA.FF

theorem p_dvd_choose {p s t M u : ℕ} (hp : p.Prime) (hq : t < p ^ s) (hdvd : p ^ s ∣ M)
    (hu1 : 1 ≤ u) (hut : u ≤ t) : p ∣ Nat.choose (M + u - 1) u := by
  have key : Nat.choose (M + u - 1) u * u = Nat.choose (M + u - 1) (u - 1) * M := by
    have := Nat.choose_succ_right_eq (M + u - 1) (u - 1)
    have e1 : u - 1 + 1 = u := by omega
    have e2 : M + u - 1 - (u - 1) = M := by omega
    rw [e1, e2] at this
    exact this
  by_contra hnd
  have hcop : Nat.Coprime (p ^ s) (Nat.choose (M + u - 1) u) :=
    Nat.Coprime.pow_left s ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
  have h1 : p ^ s ∣ Nat.choose (M + u - 1) u * u := by
    rw [key]; exact Dvd.dvd.mul_left hdvd _
  have h2 : p ^ s ∣ u := hcop.dvd_of_dvd_mul_left h1
  have := Nat.le_of_dvd (by omega) h2
  omega

/-- The test polynomial, evaluated at a natural number. -/
noncomputable def V (t m x : ℕ) : ℤ := Ring.choose ((x : ℤ) - (t + 1 : ℤ)) m

theorem V_top (t m : ℕ) : V t m (t + 1 + m) = 1 := by
  unfold V
  have : ((t + 1 + m : ℕ) : ℤ) - (t + 1 : ℤ) = ((m : ℕ) : ℤ) := by push_cast; ring
  rw [this, Ring.choose_natCast, Nat.choose_self]
  simp

theorem V_mid (t m x : ℕ) (h1 : t + 1 ≤ x) (h2 : x < t + 1 + m) : V t m x = 0 := by
  unfold V
  have : (x : ℤ) - (t + 1 : ℤ) = ((x - (t + 1) : ℕ) : ℤ) := by push_cast [h1]; ring
  rw [this, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
  simp

theorem V_low (t m x : ℕ) (h1 : x ≤ t) :
    V t m x = (Int.negOnePow m : ℤ) * (Nat.choose (t - x + m) m : ℤ) := by
  unfold V
  have : (x : ℤ) - (t + 1 : ℤ) = -((t + 1 - x : ℕ) : ℤ) := by push_cast [show x ≤ t + 1 by omega]; ring
  rw [this, Ring.choose_neg]
  have e : ((t + 1 - x : ℕ) : ℤ) + (m : ℤ) - 1 = ((t - x + m : ℕ) : ℤ) := by
    push_cast [show x ≤ t + 1 by omega, h1]; ring
  rw [e, Ring.choose_natCast, Units.smul_def]
  simp

theorem V_expand (t m x : ℕ) :
    V t m x = ∑ ij ∈ antidiagonal m,
      (Nat.choose x ij.1 : ℤ) * Ring.choose (-(t + 1 : ℤ)) ij.2 := by
  unfold V
  rw [sub_eq_add_neg, Ring.add_choose_eq m (Commute.all _ _)]
  refine sum_congr rfl ?_
  intro ij _
  rw [Ring.choose_natCast]

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The integer vector `c` is orthogonal to every row of the `m`-th inclusion matrix. -/
def Rel (F : Finset (Finset α)) (c : Finset α → ℤ) (m : ℕ) : Prop :=
  ∀ T : Finset α, T.card = m → ∑ A ∈ F, (if T ⊆ A then c A else 0) = 0

theorem rel_step (F : Finset (Finset α)) (c : Finset α → ℤ) (h : ℕ)
    (hcard : ∀ A ∈ F, A.card = h) (S : Finset α) :
    ∑ x ∈ univ \ S, ∑ A ∈ F, (if insert x S ⊆ A then c A else 0) =
      ((h - S.card : ℕ) : ℤ) * ∑ A ∈ F, (if S ⊆ A then c A else 0) := by
  rw [sum_comm, mul_sum]
  refine sum_congr rfl ?_
  intro A hA
  by_cases hS : S ⊆ A
  · have e : ∀ x, (insert x S ⊆ A ↔ x ∈ A) := fun x => by
      rw [insert_subset_iff]; exact ⟨fun h => h.1, fun h => ⟨h, hS⟩⟩
    simp only [e, hS, if_true]
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
    congr 1
    have : (univ \ S).filter (· ∈ A) = A \ S := by
      ext x; simp [and_comm]
    rw [this, card_sdiff_of_subset hS, hcard A hA]
  · have e : ∀ x, ¬ (insert x S ⊆ A) := fun x h => hS ((subset_insert x S).trans h)
    simp [e, hS]

theorem rel_down (F : Finset (Finset α)) (c : Finset α → ℤ) (h m : ℕ)
    (hcard : ∀ A ∈ F, A.card = h) (hmh : m < h) (hR : Rel F c m) :
    ∀ S : Finset α, S.card ≤ m → ∑ A ∈ F, (if S ⊆ A then c A else 0) = 0 := by
  suffices H : ∀ d, ∀ S : Finset α, S.card + d = m → ∑ A ∈ F, (if S ⊆ A then c A else 0) = 0 by
    intro S hS
    exact H (m - S.card) S (by omega)
  intro d
  induction d with
  | zero => intro S hS; exact hR S (by omega)
  | succ d ih =>
    intro S hS
    have h0 : ∑ x ∈ univ \ S, ∑ A ∈ F, (if insert x S ⊆ A then c A else 0) = 0 := by
      refine sum_eq_zero ?_
      intro x hx
      have hxS : x ∉ S := by simpa using hx
      exact ih (insert x S) (by rw [card_insert_of_notMem hxS]; omega)
    rw [rel_step F c h hcard S] at h0
    have hne : ((h - S.card : ℕ) : ℤ) ≠ 0 := by
      have : 0 < h - S.card := by omega
      exact_mod_cast this.ne'
    exact (mul_eq_zero.mp h0).resolve_left hne

theorem rel_inter (F : Finset (Finset α)) (c : Finset α → ℤ) (h m : ℕ)
    (hcard : ∀ A ∈ F, A.card = h) (hmh : m < h) (hR : Rel F c m) (A0 : Finset α)
    (s : ℕ) (hs : s ≤ m) :
    ∑ A ∈ F, c A * (Nat.choose (A ∩ A0).card s : ℤ) = 0 := by
  have H : ∀ S ∈ powersetCard s A0, ∑ A ∈ F, (if S ⊆ A then c A else 0) = 0 := by
    intro S hS
    rw [mem_powersetCard] at hS
    exact rel_down F c h m hcard hmh hR S (by omega)
  have H2 := sum_eq_zero H
  rw [sum_comm] at H2
  rw [← H2]
  refine sum_congr rfl ?_
  intro A _
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  have : (powersetCard s A0).filter (· ⊆ A) = powersetCard s (A ∩ A0) := by
    ext S; simp only [mem_filter, mem_powersetCard, subset_inter_iff]; tauto
  rw [this, card_powersetCard]

theorem rel_core {p s t m : ℕ} (hp : p.Prime) (hq : t < p ^ s) (hdvd : p ^ s ∣ m + 1)
    (F : Finset (Finset α)) (c : Finset α → ℤ)
    (hcard : ∀ A ∈ F, A.card = t + 1 + m)
    (hint : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card ≠ t)
    (hR : Rel F c m) (A0 : Finset α) (hA0 : A0 ∈ F) : (p : ℤ) ∣ c A0 := by
  have hsum : ∑ A ∈ F, c A * V t m (A ∩ A0).card = 0 := by
    simp_rw [V_expand, mul_sum]
    rw [sum_comm]
    refine sum_eq_zero ?_
    intro ij hij
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have := rel_inter F c (t + 1 + m) m hcard (by omega) hR A0 ij.1 (by omega)
    calc ∑ A ∈ F, c A * ((Nat.choose (A ∩ A0).card ij.1 : ℤ) * Ring.choose (-(t + 1 : ℤ)) ij.2)
        = (∑ A ∈ F, c A * (Nat.choose (A ∩ A0).card ij.1 : ℤ)) * Ring.choose (-(t + 1 : ℤ)) ij.2 := by
          rw [sum_mul]; refine sum_congr rfl ?_; intro A _; ring
      _ = 0 := by rw [this, zero_mul]
  rw [← add_sum_erase F _ hA0] at hsum
  have htop : V t m (A0 ∩ A0).card = 1 := by
    rw [inter_self, hcard A0 hA0, V_top]
  rw [htop, mul_one] at hsum
  have hrest : (p : ℤ) ∣ ∑ A ∈ F.erase A0, c A * V t m (A ∩ A0).card := by
    refine dvd_sum ?_
    intro A hA
    obtain ⟨hne, hAF⟩ := mem_erase.mp hA
    set x := (A ∩ A0).card with hx
    have hxle : x ≤ t + 1 + m := by
      rw [← hcard A0 hA0]; exact card_le_card inter_subset_right
    have hxne : x ≠ t + 1 + m := by
      intro heq
      have h1 : A ∩ A0 = A0 :=
        eq_of_subset_of_card_le inter_subset_right (by rw [hcard A0 hA0]; omega)
      have h2 : A ∩ A0 = A :=
        eq_of_subset_of_card_le inter_subset_left (by rw [hcard A hAF]; omega)
      exact hne (h2.symm.trans h1)
    have hxt : x ≠ t := hint A hAF A0 hA0 hne
    rcases lt_or_gt_of_ne hxt with hlt | hgt
    · rw [V_low t m x hlt.le]
      refine dvd_mul_of_dvd_right (dvd_mul_of_dvd_right ?_ _) _
      have hpd := p_dvd_choose (M := m + 1) (u := t - x) hp hq hdvd (by omega) (by omega)
      have e : m + 1 + (t - x) - 1 = t - x + m := by omega
      rw [e, Nat.choose_symm_add] at hpd
      exact_mod_cast hpd
    · rw [V_mid t m x (by omega) (by omega), mul_zero]
      exact dvd_zero _
  have : c A0 = -(∑ A ∈ F.erase A0, c A * V t m (A ∩ A0).card) := by linarith
  rw [this]
  exact dvd_neg.mpr hrest

theorem rel_zero {p s t m : ℕ} (hp : p.Prime) (hq : t < p ^ s) (hdvd : p ^ s ∣ m + 1)
    (F : Finset (Finset α))
    (hcard : ∀ A ∈ F, A.card = t + 1 + m)
    (hint : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card ≠ t)
    (c : Finset α → ℤ) (hR : Rel F c m) : ∀ A ∈ F, c A = 0 := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have key : ∀ k : ℕ, ∀ c : Finset α → ℤ, Rel F c m → ∀ A ∈ F, (p : ℤ) ^ k ∣ c A := by
    intro k
    induction k with
    | zero => intro c _ A _; simp
    | succ k ih =>
      intro c hR A hA
      have hdiv : ∀ B ∈ F, (p : ℤ) ∣ c B := fun B hB =>
        rel_core hp hq hdvd F c hcard hint hR B hB
      let c' : Finset α → ℤ := fun B => c B / p
      have hc : ∀ B ∈ F, c B = p * c' B := fun B hB => (Int.mul_ediv_cancel' (hdiv B hB)).symm
      have hR' : Rel F c' m := by
        intro T hT
        have h0 := hR T hT
        have : ∑ A ∈ F, (if T ⊆ A then c A else 0) = p * ∑ A ∈ F, (if T ⊆ A then c' A else 0) := by
          rw [mul_sum]; refine sum_congr rfl ?_; intro B hB
          split_ifs
          · exact hc B hB
          · simp
        rw [this] at h0
        exact (mul_eq_zero.mp h0).resolve_left hp0
      have := ih c' hR' A hA
      rw [hc A hA, pow_succ']
      exact mul_dvd_mul_left _ this
  intro A hA
  refine Int.eq_zero_of_abs_lt_dvd (key (c A).natAbs c hR A hA) ?_
  rw [Int.abs_eq_natAbs]
  have : (c A).natAbs < p ^ (c A).natAbs := Nat.lt_pow_self hp.one_lt
  exact_mod_cast this

/-- Frankl–Singhi: the inclusion matrix has full row rank, hence the family is no larger
than its shadow. -/
theorem fs_card_le {p s t m : ℕ} (hp : p.Prime) (hq : t < p ^ s) (hdvd : p ^ s ∣ m + 1)
    (F : Finset (Finset α))
    (hcard : ∀ A ∈ F, A.card = t + 1 + m)
    (hint : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card ≠ t) :
    F.card ≤ (F.biUnion (fun A => powersetCard m A)).card := by
  set D := F.biUnion (fun A => powersetCard m A) with hD
  let v : F → (D → ℤ) := fun A T => if (T : Finset α) ⊆ (A : Finset α) then 1 else 0
  have hli : LinearIndependent ℤ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg A
    let c : Finset α → ℤ := fun B => if hB : B ∈ F then g ⟨B, hB⟩ else 0
    have hR : Rel F c m := by
      intro T hT
      rw [← sum_coe_sort F]
      by_cases hTD : T ∈ D
      · have := congrFun hg ⟨T, hTD⟩
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v] at this
        refine Eq.trans ?_ this
        refine sum_congr rfl ?_
        intro B _
        have hcB : c B = g B := by
          simp only [c, dif_pos B.2]
        by_cases hTB : T ⊆ (B : Finset α)
        · rw [if_pos hTB, if_pos hTB, hcB, mul_one]
        · rw [if_neg hTB, if_neg hTB, mul_zero]
      · refine sum_eq_zero ?_
        intro B _
        rw [if_neg]
        intro hTB
        apply hTD
        rw [hD, mem_biUnion]
        exact ⟨B, B.2, mem_powersetCard.mpr ⟨hTB, hT⟩⟩
    have := rel_zero hp hq hdvd F hcard hint c hR A A.2
    simpa [c] using this
  have := hli.fintype_card_le_finrank
  simpa using this

/-- The `g`-shadow of a family. -/
abbrev sh (F : Finset (Finset α)) (g : ℕ) : Finset (Finset α) :=
  F.biUnion (fun A => powersetCard g A)

theorem sum_card_filter_mem (D : Finset (Finset α)) :
    ∑ x : α, (D.filter (x ∈ ·)).card = ∑ A ∈ D, A.card := by
  simp_rw [card_filter]
  rw [sum_comm]
  refine sum_congr rfl ?_
  intro A _
  rw [← card_filter, filter_mem_eq_inter, univ_inter]

theorem shadow_main {p s t m : ℕ} (hp : p.Prime) (hq : t < p ^ s) (hdvd : p ^ s ∣ m + 1)
    (ht : 1 ≤ t) (F : Finset (Finset α)) (hcard : ∀ A ∈ F, A.card = t + 1 + m)
    (hint : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card ≠ t) :
    (t + 1 + m) * F.card ≤ (m + 1) * (sh F (m + 1)).card := by
  have hloc : ∀ x : α, (F.filter (x ∈ ·)).card ≤ ((sh F (m + 1)).filter (x ∈ ·)).card := by
    intro x
    set Fx := (F.filter (x ∈ ·)).image (·.erase x) with hFx
    have hinj : Set.InjOn (·.erase x) (F.filter (x ∈ ·) : Set (Finset α)) := by
      intro A hA B hB hAB
      exact erase_injOn' x (mem_filter.1 hA).2 (mem_filter.1 hB).2 hAB
    have hcardFx : Fx.card = (F.filter (x ∈ ·)).card := card_image_of_injOn hinj
    have hc' : ∀ B ∈ Fx, B.card = (t - 1) + 1 + m := by
      intro B hB
      obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
      obtain ⟨hAF, hxA⟩ := mem_filter.1 hA
      rw [card_erase_of_mem hxA, hcard A hAF]; omega
    have hi' : ∀ B1 ∈ Fx, ∀ B2 ∈ Fx, B1 ≠ B2 → (B1 ∩ B2).card ≠ t - 1 := by
      intro B1 hB1 B2 hB2 hne
      obtain ⟨A1, hA1, rfl⟩ := mem_image.1 hB1
      obtain ⟨A2, hA2, rfl⟩ := mem_image.1 hB2
      obtain ⟨hA1F, hxA1⟩ := mem_filter.1 hA1
      obtain ⟨hA2F, hxA2⟩ := mem_filter.1 hA2
      have hA : A1 ≠ A2 := fun h => hne (by rw [h])
      have e : A1.erase x ∩ A2.erase x = (A1 ∩ A2).erase x := by
        ext y; simp only [mem_inter, mem_erase]; tauto
      have hxI : x ∈ A1 ∩ A2 := mem_inter.2 ⟨hxA1, hxA2⟩
      rw [e, card_erase_of_mem hxI]
      have h1 := hint A1 hA1F A2 hA2F hA
      have h2 : 1 ≤ (A1 ∩ A2).card := card_pos.2 ⟨x, hxI⟩
      omega
    have hfs := fs_card_le (t := t - 1) hp (by omega) hdvd Fx hc' hi'
    rw [hcardFx] at hfs
    refine hfs.trans ?_
    refine card_le_card_of_injOn (insert x) ?_ ?_
    · intro B hB
      rw [mem_coe, mem_biUnion] at hB
      obtain ⟨A', hA', hBA'⟩ := hB
      obtain ⟨A, hA, rfl⟩ := mem_image.1 hA'
      obtain ⟨hAF, hxA⟩ := mem_filter.1 hA
      obtain ⟨hBsub, hBc⟩ := mem_powersetCard.1 hBA'
      have hxB : x ∉ B := fun h => by simpa using hBsub h
      rw [mem_coe, mem_filter]
      refine ⟨?_, mem_insert_self x B⟩
      rw [mem_biUnion]
      refine ⟨A, hAF, mem_powersetCard.2 ⟨?_, ?_⟩⟩
      · exact insert_subset hxA (hBsub.trans (erase_subset x A))
      · rw [card_insert_of_notMem hxB, hBc]
    · intro B1 hB1 B2 hB2 h
      have hx : ∀ B ∈ (sh Fx m : Set (Finset α)), x ∉ B := by
        intro B hB
        rw [mem_coe, mem_biUnion] at hB
        obtain ⟨A', hA', hBA'⟩ := hB
        obtain ⟨A, hA, rfl⟩ := mem_image.1 hA'
        intro hxB
        have := (mem_powersetCard.1 hBA').1 hxB
        simp at this
      have := congrArg (·.erase x) h
      simp only [erase_insert (hx B1 hB1), erase_insert (hx B2 hB2)] at this
      exact this
  have hsum := sum_le_sum (fun x (_ : x ∈ (univ : Finset α)) => hloc x)
  rw [sum_card_filter_mem, sum_card_filter_mem] at hsum
  rw [sum_congr rfl hcard, sum_const, smul_eq_mul] at hsum
  have hsh : ∀ G ∈ sh F (m + 1), G.card = m + 1 := by
    intro G hG
    rw [mem_biUnion] at hG
    obtain ⟨A, _, hGA⟩ := hG
    exact (mem_powersetCard.1 hGA).2
  rw [sum_congr rfl hsh, sum_const, smul_eq_mul] at hsum
  linarith

theorem exists_big_prime_pow (t M : ℕ) (hM : t ^ t < M) :
    ∃ p s, p.Prime ∧ t < p ^ s ∧ p ^ s ∣ M := by
  by_contra H
  push Not at H
  have hM0 : M ≠ 0 := by
    have : 0 < t ^ t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h; simp
      · exact Nat.pow_pos h
    omega
  have hle : ∀ p ∈ M.primeFactors, p ^ M.factorization p ≤ t := by
    intro p hp
    by_contra h
    exact H p _ (Nat.prime_of_mem_primeFactors hp) (by omega) (Nat.ordProj_dvd M p)
  have hsub : M.primeFactors ⊆ Icc 1 t := by
    intro p hp
    have hk : M.factorization p ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hp
    have h1 := hle p hp
    have h2 : p ≤ p ^ M.factorization p := Nat.le_self_pow hk p
    have h3 := (Nat.prime_of_mem_primeFactors hp).one_lt
    rw [mem_Icc]; omega
  have hcardle : M.primeFactors.card ≤ t := by
    have := card_le_card hsub; simpa using this
  have hprod := prod_le_pow_card M.primeFactors (fun p => p ^ M.factorization p) t hle
  rw [← Nat.prod_primeFactors_pow_factorization hM0] at hprod
  have : t ^ M.primeFactors.card ≤ t ^ t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h
      have : M.primeFactors.card = 0 := by omega
      rw [this]
    · exact Nat.pow_le_pow_right h hcardle
  omega

/-- The shadow inequality for uniform families avoiding one intersection size. -/
theorem shadow_good (t h : ℕ) (hth : t < h) (hgood : t = 0 ∨ t ^ t < h - t)
    (F : Finset (Finset α)) (hcard : ∀ A ∈ F, A.card = h)
    (hint : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card ≠ t) :
    h * F.card ≤ (h - t) * (sh F (h - t)).card := by
  by_cases h0 : t = 0
  · subst h0
    simp only [Nat.sub_zero]
    refine Nat.mul_le_mul_left _ (card_le_card ?_)
    intro A hA
    rw [mem_biUnion]
    exact ⟨A, hA, mem_powersetCard.2 ⟨subset_refl A, hcard A hA⟩⟩
  · have hbig := hgood.resolve_left h0
    obtain ⟨p, s, hp, hq, hdvd⟩ := exists_big_prime_pow t (h - t) hbig
    have ht : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr h0
    have e : h = t + 1 + (h - t - 1) := by omega
    have e2 : h - t = (h - t - 1) + 1 := by omega
    rw [e2] at hdvd
    have hc : ∀ A ∈ F, A.card = t + 1 + (h - t - 1) := fun A hA => by rw [hcard A hA]; omega
    have := shadow_main hp hq hdvd ht F hc hint
    rw [← e, ← e2] at this
    exact this

/-- No two members (equal or not) meet in exactly `t` points. -/
def Valid (F : Finset (Finset α)) (t : ℕ) : Prop := ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ t

/-- The members of size `k`. -/
abbrev lev (F : Finset (Finset α)) (k : ℕ) : Finset (Finset α) := F.filter (·.card = k)

theorem lev_le {β : Type*} [Fintype β] (F : Finset (Finset β)) (k : ℕ) :
    (lev F k).card ≤ (Fintype.card β).choose k := by
  calc (lev F k).card ≤ (powersetCard k (univ : Finset β)).card := by
        refine card_le_card ?_
        intro A hA
        rw [mem_filter] at hA
        rw [mem_powersetCard]
        exact ⟨subset_univ _, hA.2⟩
    _ = _ := by rw [card_powersetCard, card_univ]

theorem lev_t {β : Type*} [DecidableEq β] (F : Finset (Finset β)) (t : ℕ) (hF : Valid F t) : (lev F t).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro A hA hc
  exact hF A hA A hA (by rw [inter_self]; exact hc)

theorem pair_disj (F : Finset (Finset α)) (t i : ℕ) (hF : Valid F t) (hti : t ≤ i)
    (hin : i ≤ Fintype.card α) :
    (sh (lev F i) (i - t)).card + (lev F (Fintype.card α + t - i)).card ≤
      (Fintype.card α).choose (i - t) := by
  set Cm := (lev F (Fintype.card α + t - i)).image compl with hCmdef
  have hCm : Cm.card = (lev F (Fintype.card α + t - i)).card :=
    card_image_of_injective _ compl_injective
  have hdisj : Disjoint (sh (lev F i) (i - t)) Cm := by
    rw [disjoint_left]
    intro G hG hGC
    rw [mem_biUnion] at hG
    obtain ⟨A, hA, hGA⟩ := hG
    obtain ⟨hAF, hAc⟩ := mem_filter.1 hA
    obtain ⟨hGsub, hGc⟩ := mem_powersetCard.1 hGA
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hGC
    obtain ⟨hBF, _⟩ := mem_filter.1 hB
    apply hF A hAF B hBF
    have : A ∩ B = A \ Bᶜ := by rw [sdiff_eq_inter_compl, compl_compl]
    rw [this, card_sdiff_of_subset hGsub, hAc, hGc]; omega
  have hsub : sh (lev F i) (i - t) ∪ Cm ⊆ powersetCard (i - t) univ := by
    intro G hG
    rw [mem_union] at hG
    rw [mem_powersetCard]
    refine ⟨subset_univ _, ?_⟩
    rcases hG with hG | hG
    · rw [mem_biUnion] at hG
      obtain ⟨A, _, hGA⟩ := hG
      exact (mem_powersetCard.1 hGA).2
    · obtain ⟨B, hB, rfl⟩ := mem_image.1 hG
      rw [card_compl, (mem_filter.1 hB).2]; omega
  have := card_le_card hsub
  rw [card_union_of_disjoint hdisj, hCm, card_powersetCard, card_univ] at this
  exact this

theorem key_ineq (F : Finset (Finset α)) (t i : ℕ) (hF : Valid F t) (hti : t < i)
    (hin : i ≤ Fintype.card α) (hgood : t = 0 ∨ t ^ t < i - t) :
    i * (lev F i).card + (i - t) * (lev F (Fintype.card α + t - i)).card ≤
      (i - t) * (Fintype.card α).choose (i - t) := by
  have h1 := shadow_good t i hti hgood (lev F i) (fun A hA => (mem_filter.1 hA).2)
    (fun A hA B hB _ => hF A (mem_filter.1 hA).1 B (mem_filter.1 hB).1)
  have h2 := pair_disj F t i hF hti.le hin
  calc i * (lev F i).card + (i - t) * (lev F (Fintype.card α + t - i)).card
      ≤ (i - t) * (sh (lev F i) (i - t)).card + (i - t) * (lev F (Fintype.card α + t - i)).card :=
        Nat.add_le_add_right h1 _
    _ = (i - t) * ((sh (lev F i) (i - t)).card + (lev F (Fintype.card α + t - i)).card) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ h2

end OMA.FF

namespace OMA.FF

theorem decomp (φ : ℕ → ℕ) (n t : ℕ) (htn : t ≤ n) :
    ∑ k ∈ range (n + 1), φ k = ∑ k ∈ range t, φ k
      + ∑ i ∈ Ico t ((n + t + 1) / 2), (φ i + φ (n + t - i))
      + ∑ k ∈ Ico ((n + t + 1) / 2) (n + t + 1 - (n + t + 1) / 2), φ k := by
  set P := (n + t + 1) / 2 with hP
  have h1 : t ≤ P := by omega
  have h2 : P ≤ n + t + 1 - P := by omega
  have h3 : n + t + 1 - P ≤ n + 1 := by omega
  rw [sum_add_distrib]
  have hrefl : ∑ i ∈ Ico t P, φ (n + t - i) = ∑ k ∈ Ico (n + t + 1 - P) (n + 1), φ k := by
    have := sum_Ico_reflect φ t (n := n + t) (show P ≤ n + t + 1 by omega)
    rw [this, show n + t + 1 - t = n + 1 by omega]
  rw [hrefl, range_eq_Ico, range_eq_Ico]
  have e1 := sum_Ico_consecutive φ (Nat.zero_le t) (h1.trans (h2.trans h3))
  have e2 := sum_Ico_consecutive φ h1 (h2.trans h3)
  have e3 := sum_Ico_consecutive φ h2 h3
  rw [← e1, ← e2, ← e3]
  ring

theorem eventually_pow_lt (c k : ℕ) : ∀ᶠ n : ℕ in Filter.atTop, c * n ^ k < 2 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt k (show (1 : ℝ) < 2 by norm_num)
  have hpos : (0 : ℝ) < 1 / (c + 1) := by positivity
  filter_upwards [h.eventually (gt_mem_nhds hpos)] with n hn
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_lt_div_iff₀ h2 (by positivity)] at hn
  have h3 : (0 : ℝ) ≤ (n : ℝ) ^ k := by positivity
  have : (c : ℝ) * (n : ℝ) ^ k < 2 ^ n := by nlinarith
  exact_mod_cast this

theorem choose_lower (N k : ℕ) (hk : k ≤ N) (h2 : 2 * (N - k) ≤ N) :
    4 ^ (N - k) ≤ (2 * (N - k) + 1) * N.choose k := by
  rw [← Nat.choose_symm hk]
  calc 4 ^ (N - k) ≤ (2 * (N - k) + 1) * (2 * (N - k)).choose (N - k) :=
        Nat.four_pow_le_two_mul_add_one_mul_central_binom _
    _ ≤ (2 * (N - k) + 1) * N.choose (N - k) :=
        Nat.mul_le_mul_left _ (Nat.choose_le_choose _ h2)

theorem sum_choose_le (n Q : ℕ) (hn : 1 ≤ n) : ∑ i ∈ range Q, n.choose i ≤ Q * n ^ Q := by
  calc ∑ i ∈ range Q, n.choose i ≤ ∑ i ∈ range Q, n ^ Q := by
        refine sum_le_sum ?_
        intro i hi
        rw [mem_range] at hi
        exact (Nat.choose_le_pow n i).trans (Nat.pow_le_pow_right hn hi.le)
    _ = Q * n ^ Q := by rw [sum_const, card_range, smul_eq_mul]

section Gain
variable {α : Type*} [DecidableEq α] [Fintype α]

theorem excluded (F : Finset (Finset α)) (t b : ℕ) (hF : Valid F t) (F0 : Finset α)
    (hF0 : F0 ∈ F) (ht : t ≤ F0.card) (hb : t ≤ b) :
    (lev F b).card + (Fintype.card α - F0.card).choose (b - t) ≤ (Fintype.card α).choose b := by
  obtain ⟨S0, hS0, hS0c⟩ := exists_subset_card_eq ht
  set E := (powersetCard (b - t) F0ᶜ).image (S0 ∪ ·) with hE
  have hinj : Set.InjOn (S0 ∪ ·) (powersetCard (b - t) F0ᶜ : Set (Finset α)) := by
    intro R1 hR1 R2 hR2 h
    have k1 := (mem_powersetCard.1 hR1).1
    have k2 := (mem_powersetCard.1 hR2).1
    have e : ∀ R : Finset α, R ⊆ F0ᶜ → (S0 ∪ R) ∩ F0ᶜ = R := by
      intro R hR
      ext x
      simp only [mem_inter, mem_union, mem_compl]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd (hS0 h1) h2
        · exact h1
      · intro hx
        exact ⟨Or.inr hx, by simpa using hR hx⟩
    have := congrArg (· ∩ F0ᶜ) h
    simp only at this
    rw [e R1 k1, e R2 k2] at this
    exact this
  have hEc : E.card = (Fintype.card α - F0.card).choose (b - t) := by
    rw [card_image_of_injOn hinj, card_powersetCard, card_compl]
  have hmem : ∀ B ∈ E, B.card = b ∧ (B ∩ F0).card = t := by
    intro B hB
    obtain ⟨R, hR, rfl⟩ := mem_image.1 hB
    obtain ⟨hRs, hRc⟩ := mem_powersetCard.1 hR
    have hd : Disjoint S0 R := by
      rw [disjoint_left]
      intro x hx hxR
      have := hRs hxR
      rw [mem_compl] at this
      exact this (hS0 hx)
    refine ⟨?_, ?_⟩
    · rw [card_union_of_disjoint hd, hS0c, hRc]; omega
    · have : (S0 ∪ R) ∩ F0 = S0 := by
        ext x
        simp only [mem_inter, mem_union]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact h1
          · exact absurd h2 (by simpa using hRs h1)
        · intro hx; exact ⟨Or.inl hx, hS0 hx⟩
      rw [this, hS0c]
  have hdisj : Disjoint (lev F b) E := by
    rw [disjoint_left]
    intro B hB hBE
    exact hF B (mem_filter.1 hB).1 F0 hF0 (hmem B hBE).2
  have hsub : lev F b ∪ E ⊆ powersetCard b univ := by
    intro B hB
    rw [mem_powersetCard]
    refine ⟨subset_univ _, ?_⟩
    rcases mem_union.1 hB with h | h
    · exact (mem_filter.1 h).2
    · exact (hmem B h).1
  have := card_le_card hsub
  rw [card_union_of_disjoint hdisj, hEc, card_powersetCard, card_univ] at this
  exact this

theorem pair_le (F : Finset (Finset α)) (t n i : ℕ) (hα : Fintype.card α = n) (hF : Valid F t)
    (hti : t ≤ i) (hin : i ≤ n) :
    (lev F i).card + (lev F (n + t - i)).card ≤ n.choose (i - t) +
      (if t < i ∧ ¬ (t = 0 ∨ t ^ t < i - t) then (lev F i).card else 0) := by
  have hj : (lev F (n + t - i)).card ≤ n.choose (i - t) := by
    have := lev_le F (n + t - i)
    rw [hα] at this
    rw [show n + t - i = n - (i - t) by omega, Nat.choose_symm (by omega)] at this
    rwa [show n + t - i = n - (i - t) by omega]
  rcases Nat.eq_or_lt_of_le hti with h | h
  · subst h
    rw [lev_t F t hF]
    simp only [lt_irrefl, false_and, if_false]
    omega
  · by_cases hg : t = 0 ∨ t ^ t < i - t
    · simp only [hg, not_true_eq_false, and_false, if_false, add_zero]
      have k := key_ineq F t i hF h (by rw [hα]; exact hin) hg
      rw [hα] at k
      have hpos : 0 < i - t := by omega
      have : (i - t) * ((lev F i).card + (lev F (n + t - i)).card) ≤ (i - t) * n.choose (i - t) := by
        have : (i - t) * (lev F i).card ≤ i * (lev F i).card := Nat.mul_le_mul_right _ (by omega)
        nlinarith
      exact Nat.le_of_mul_le_mul_left this hpos
    · simp only [h, hg, not_false_eq_true, and_self, if_true]
      omega

end Gain
section Upper
variable {α : Type*} [DecidableEq α] [Fintype α]

theorem upper (t n : ℕ) (hα : Fintype.card α = n) (htn : t + 1 ≤ n)
    (hP : t + t ^ t + 2 ≤ (n + t + 1) / 2)
    (hexp : ∀ a, a < t + t ^ t + 1 →
      n * ∑ i ∈ range (t + t ^ t + 1), n.choose i ≤ (n - a).choose (n - (n + t + 1) / 2 + 1))
    (F : Finset (Finset α)) (hF : Valid F t) :
    F.card ≤ ∑ k ∈ range t, n.choose k + ∑ i ∈ Ico t ((n + t + 1) / 2), n.choose (i - t)
      + ∑ k ∈ Ico ((n + t + 1) / 2) (n + t + 1 - (n + t + 1) / 2), (n - 1).choose k := by
  set P := (n + t + 1) / 2 with hPdef
  set Q := t + t ^ t + 1 with hQ
  have hcard : F.card = ∑ k ∈ range (n + 1), (lev F k).card := by
    refine card_eq_sum_card_fiberwise ?_
    intro A _
    rw [mem_coe, mem_range]
    have := card_le_univ A
    omega
  rw [hcard, decomp (fun k => (lev F k).card) n t (by omega)]
  refine add_le_add (add_le_add ?_ ?_) ?_
  · refine sum_le_sum ?_
    intro k _
    have := lev_le F k
    rwa [hα] at this
  · by_cases hsmall : ∃ A ∈ F, t < A.card ∧ ¬ (t = 0 ∨ t ^ t < A.card - t)
    · obtain ⟨F0, hF0, hF0t, hF0g⟩ := hsmall
      have ht0 : t ≠ 0 := fun h => hF0g (Or.inl h)
      have hag : F0.card - t ≤ t ^ t := by
        by_contra hc
        exact hF0g (Or.inr (by omega))
      have ha : F0.card < Q := by omega
      have e : Ico t P = Ico t (P - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
      rw [e, sum_Ico_succ_top (by omega), sum_Ico_succ_top (by omega)]
      set i0 := P - 1 with hi0
      set L := ∑ i ∈ range Q, n.choose i with hL
      have hrest : ∑ i ∈ Ico t i0, ((lev F i).card + (lev F (n + t - i)).card) ≤
          ∑ i ∈ Ico t i0, n.choose (i - t) + L := by
        calc ∑ i ∈ Ico t i0, ((lev F i).card + (lev F (n + t - i)).card)
            ≤ ∑ i ∈ Ico t i0, (n.choose (i - t) +
                (if t < i ∧ ¬ (t = 0 ∨ t ^ t < i - t) then (lev F i).card else 0)) := by
              refine sum_le_sum ?_
              intro i hi
              rw [mem_Ico] at hi
              exact pair_le F t n i hα hF hi.1 (by omega)
          _ = ∑ i ∈ Ico t i0, n.choose (i - t) + ∑ i ∈ Ico t i0,
                (if t < i ∧ ¬ (t = 0 ∨ t ^ t < i - t) then (lev F i).card else 0) :=
              sum_add_distrib
          _ ≤ ∑ i ∈ Ico t i0, n.choose (i - t) + L := by
              refine Nat.add_le_add_left ?_ _
              calc ∑ i ∈ Ico t i0,
                    (if t < i ∧ ¬ (t = 0 ∨ t ^ t < i - t) then (lev F i).card else 0)
                  ≤ ∑ i ∈ Ico t i0, (if i < Q then n.choose i else 0) := by
                    refine sum_le_sum ?_
                    intro i _
                    split_ifs with h1 h2
                    · have := lev_le F i; rwa [hα] at this
                    · exfalso
                      apply h2
                      have : i - t ≤ t ^ t := by
                        by_contra hc; exact h1.2 (Or.inr (by omega))
                      omega
                    · exact Nat.zero_le _
                    · exact le_refl _
                _ = ∑ i ∈ (Ico t i0).filter (· < Q), n.choose i := by rw [sum_filter]
                _ ≤ L := by
                    refine sum_le_sum_of_subset ?_
                    intro i hi
                    rw [mem_filter] at hi
                    rw [mem_range]; exact hi.2
      have hlast : (lev F i0).card + (lev F (n + t - i0)).card + L ≤ n.choose (i0 - t) := by
        have hgood : t = 0 ∨ t ^ t < i0 - t := Or.inr (by omega)
        have key := key_ineq F t i0 hF (by omega) (by rw [hα]; omega) hgood
        rw [hα] at key
        have exc := excluded F t (n + t - i0) hF F0 hF0 hF0t.le (by omega)
        rw [hα, show n + t - i0 - t = n - P + 1 by omega,
          show n + t - i0 = n - (i0 - t) by omega, Nat.choose_symm (by omega)] at exc
        rw [show n + t - i0 = n - (i0 - t) by omega]
        rw [show n + t - i0 = n - (i0 - t) by omega] at key
        have he := hexp F0.card ha
        set fi := (lev F i0).card
        set fj := (lev F (n - (i0 - t))).card
        set C := n.choose (i0 - t)
        set E := (n - F0.card).choose (n - P + 1)
        set d := i0 - t with hd
        have hi0d : i0 = d + t := by omega
        have h1 : t * fj + t * E ≤ t * C := by
          rw [← mul_add]; exact Nat.mul_le_mul_left _ exc
        have h2 : i0 * L ≤ n * L := Nat.mul_le_mul_right _ (by omega)
        have h3 : E ≤ t * E := Nat.le_mul_of_pos_left _ (by omega)
        have h4 : i0 * (fi + fj + L) ≤ i0 * C := by
          rw [hi0d] at key h2 ⊢
          nlinarith
        exact Nat.le_of_mul_le_mul_left h4 (by omega)
      omega
    · push Not at hsmall
      refine sum_le_sum ?_
      intro i hi
      rw [mem_Ico] at hi
      have := pair_le F t n i hα hF hi.1 (by omega)
      have h0 : (if t < i ∧ ¬ (t = 0 ∨ t ^ t < i - t) then (lev F i).card else 0) = 0 := by
        split_ifs with h
        · rw [card_eq_zero, filter_eq_empty_iff]
          intro A hA hAc
          have := hsmall A hA (by rw [hAc]; exact h.1)
          rw [hAc] at this
          exact h.2 this
        · rfl
      omega
  · refine sum_le_sum ?_
    intro k hk
    rw [mem_Ico] at hk
    have hk' : k = P := by omega
    have h2 : n + t = 2 * P := by omega
    subst hk'
    have hgood : t = 0 ∨ t ^ t < P - t := Or.inr (by omega)
    have k := key_ineq F t P hF (by omega) (by rw [hα]; omega) hgood
    rw [hα, show n + t - P = P by omega] at k
    have e1 : n.choose (P - t) = n.choose P := by
      rw [show P - t = n - P by omega, Nat.choose_symm (by omega)]
    have e2 : (n - 1).choose P * n = n.choose P * (n - P) := by
      have := Nat.choose_mul_succ_eq (n - 1) P
      rwa [show n - 1 + 1 = n by omega] at this
    rw [e1, show P - t = n - P by omega] at k
    have : n * (lev F P).card ≤ n * (n - 1).choose P := by
      have h3 : P + (n - P) = n := by omega
      calc n * (lev F P).card = P * (lev F P).card + (n - P) * (lev F P).card := by
            rw [← add_mul, h3]
        _ ≤ (n - P) * n.choose P := k
        _ = n * (n - 1).choose P := by rw [mul_comm, ← e2, mul_comm]
    exact Nat.le_of_mul_le_mul_left this (by omega)

end Upper
theorem cond (t : ℕ) : ∀ᶠ n : ℕ in Filter.atTop, t + 1 ≤ n ∧ t + t ^ t + 2 ≤ (n + t + 1) / 2 ∧
    ∀ a, a < t + t ^ t + 1 →
      n * ∑ i ∈ range (t + t ^ t + 1), n.choose i ≤ (n - a).choose (n - (n + t + 1) / 2 + 1) := by
  set Q := t + t ^ t + 1 with hQ
  filter_upwards [Filter.eventually_ge_atTop (2 * Q + 4 + t),
    eventually_pow_lt (2 * Q * 2 ^ (2 * Q + 2)) (Q + 2)] with n hn1 hn2
  set P := (n + t + 1) / 2 with hP
  refine ⟨by omega, by omega, ?_⟩
  intro a ha
  set j := P - Q - 1 with hj
  have hL : ∑ i ∈ range Q, n.choose i ≤ Q * n ^ Q := sum_choose_le n Q (by omega)
  have hlow := choose_lower (n - Q) (n - P + 1) (by omega) (by omega)
  rw [show n - Q - (n - P + 1) = j by omega] at hlow
  have hmono : (n - Q).choose (n - P + 1) ≤ (n - a).choose (n - P + 1) :=
    Nat.choose_le_choose _ (by omega)
  have h2j : 2 ^ n ≤ 4 ^ j * 2 ^ (2 * Q + 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkey : 2 * Q * n ^ (Q + 2) < 4 ^ j := by
    have : 2 * Q * n ^ (Q + 2) * 2 ^ (2 * Q + 2) < 4 ^ j * 2 ^ (2 * Q + 2) := by
      calc 2 * Q * n ^ (Q + 2) * 2 ^ (2 * Q + 2) = 2 * Q * 2 ^ (2 * Q + 2) * n ^ (Q + 2) := by ring
        _ < 2 ^ n := hn2
        _ ≤ _ := h2j
    exact Nat.lt_of_mul_lt_mul_right this
  have hj2 : 2 * j + 1 ≤ 2 * n := by omega
  have hprod : n * (∑ i ∈ range Q, n.choose i) * (2 * j + 1) ≤ 2 * Q * n ^ (Q + 2) := by
    calc n * (∑ i ∈ range Q, n.choose i) * (2 * j + 1) ≤ n * (Q * n ^ Q) * (2 * n) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hL) hj2
      _ = 2 * Q * n ^ (Q + 2) := by ring
  have : n * (∑ i ∈ range Q, n.choose i) * (2 * j + 1) < (n - Q).choose (n - P + 1) * (2 * j + 1) := by
    calc n * (∑ i ∈ range Q, n.choose i) * (2 * j + 1) < 4 ^ j := lt_of_le_of_lt hprod hkey
      _ ≤ (2 * j + 1) * (n - Q).choose (n - P + 1) := hlow
      _ = _ := by ring
  have := Nat.lt_of_mul_lt_mul_right this
  omega

theorem real_lt (a b k : ℕ) : ((a + b : ℝ) / 2 < (k : ℝ)) ↔ a + b < 2 * k := by
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
  constructor
  · intro h; have : ((a + b : ℕ) : ℝ) < ((2 * k : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · intro h; have : ((a + b : ℕ) : ℝ) < ((2 * k : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith

theorem real_le (a b k : ℕ) : ((a + b : ℝ) / 2 ≤ (k : ℝ)) ↔ a + b ≤ 2 * k := by
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  constructor
  · intro h; have : ((a + b : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · intro h; have : ((a + b : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith

section Levels

theorem lev_all {α : Type*} [Fintype α] (G : Finset (Finset α)) (k : ℕ)
    (h : ∀ A : Finset α, A.card = k → A ∈ G) :
    (lev G k).card = (Fintype.card α).choose k := by
  have : lev G k = powersetCard k univ := by
    ext A
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
    exact ⟨fun h' => h'.2, fun h' => ⟨h A h', h'⟩⟩
  rw [this, card_powersetCard, card_univ]

theorem lev_none {α : Type*} (G : Finset (Finset α)) (k : ℕ) (h : ∀ A : Finset α, A.card = k → A ∉ G) :
    (lev G k).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro A hA hc
  exact h A hc hA

/-- The count of a family whose levels are those of the extremal family. -/
theorem card_of_levels {α : Type*} [Fintype α] (G : Finset (Finset α)) (t n : ℕ) (hα : Fintype.card α = n) (htn : t ≤ n)
    (hlow : ∀ k < t, (lev G k).card = n.choose k)
    (hpair : ∀ i, t ≤ i → 2 * i < n + t → (lev G i).card = 0 ∧
      (lev G (n + t - i)).card = n.choose (i - t))
    (hmid : ∀ k, 2 * k = n + t → (lev G k).card = (n - 1).choose k) :
    G.card = ∑ k ∈ range t, n.choose k + ∑ i ∈ Ico t ((n + t + 1) / 2), n.choose (i - t)
      + ∑ k ∈ Ico ((n + t + 1) / 2) (n + t + 1 - (n + t + 1) / 2), (n - 1).choose k := by
  have hcard : G.card = ∑ k ∈ range (n + 1), (lev G k).card := by
    refine card_eq_sum_card_fiberwise ?_
    intro A _
    rw [mem_coe, mem_range]
    have := card_le_univ A
    omega
  rw [hcard, decomp (fun k => (lev G k).card) n t htn]
  congr 1
  congr 1
  · exact sum_congr rfl (fun k hk => hlow k (mem_range.1 hk))
  · refine sum_congr rfl ?_
    intro i hi
    rw [mem_Ico] at hi
    obtain ⟨h1, h2⟩ := hpair i hi.1 (by omega)
    rw [h1, h2, zero_add]
  · refine sum_congr rfl ?_
    intro k hk
    rw [mem_Ico] at hk
    exact hmid k (by omega)

end Levels
section Extremal

theorem G1_valid (n r : ℕ) :
    Valid ((univ : Finset (Finset (Fin n))).filter fun A ↦
      (n + r : ℝ) / 2 < A.card ∨ A.card < r) r := by
  intro A hA B hB
  simp only [mem_filter, mem_univ, true_and, real_lt] at hA hB
  have hu := card_union_add_card_inter A B
  have hle := card_le_univ (A ∪ B)
  rw [Fintype.card_fin] at hle
  have h1 := card_le_card (inter_subset_left : A ∩ B ⊆ A)
  have h2 := card_le_card (inter_subset_right : A ∩ B ⊆ B)
  omega

theorem G1_card (n r : ℕ) (hrn : r ≤ n) (hodd : (n + r) % 2 = 1) :
    ((univ : Finset (Finset (Fin n))).filter fun A ↦
      (n + r : ℝ) / 2 < A.card ∨ A.card < r).card =
    ∑ k ∈ range r, n.choose k + ∑ i ∈ Ico r ((n + r + 1) / 2), n.choose (i - r)
      + ∑ k ∈ Ico ((n + r + 1) / 2) (n + r + 1 - (n + r + 1) / 2), (n - 1).choose k := by
  refine card_of_levels _ r n (Fintype.card_fin n) hrn ?_ ?_ ?_
  · intro k hk
    rw [lev_all _ k, Fintype.card_fin]
    intro A hA
    simp only [mem_filter, mem_univ, true_and, real_lt]
    omega
  · intro i hi1 hi2
    constructor
    · refine lev_none _ i ?_
      intro A hA
      simp only [mem_filter, mem_univ, true_and, real_lt]
      omega
    · rw [lev_all _ _, Fintype.card_fin]
      · rw [show n + r - i = n - (i - r) by omega, Nat.choose_symm (by omega)]
      · intro A hA
        simp only [mem_filter, mem_univ, true_and, real_lt]
        omega
  · intro k hk
    omega

theorem Z_zero_le {n : ℕ} (A : Finset (Fin n)) :
    (A.filter fun i : Fin n ↦ ¬ (i : ℕ) ≠ 0).card ≤ 1 := by
  rw [card_le_one]
  intro a ha b hb
  simp only [mem_filter, not_not] at ha hb
  exact Fin.ext (by omega)

theorem Z_bounds {n : ℕ} (A : Finset (Fin n)) : (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0).card ≤ A.card ∧ A.card ≤ (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0).card + 1 := by
  have h := card_filter_add_card_filter_not (s := A) (fun i : Fin n ↦ (i : ℕ) ≠ 0)
  have := Z_zero_le A
  omega

theorem Z_univ (n : ℕ) (hn : 1 ≤ n) : ((univ : Finset (Fin n)).filter fun i : Fin n ↦ (i : ℕ) ≠ 0).card = n - 1 := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i : Fin n ↦ (i : ℕ) ≠ 0)
  have h1 : ((univ : Finset (Fin n)).filter fun i : Fin n ↦ ¬ (i : ℕ) ≠ 0).card = 1 := by
    rw [card_eq_one]
    refine ⟨⟨0, by omega⟩, ?_⟩
    ext i
    simp only [mem_filter, mem_univ, true_and, not_not, mem_singleton]
    constructor
    · intro h; exact Fin.ext h
    · intro h; rw [h]
  rw [card_univ, Fintype.card_fin] at h
  omega

theorem G2_valid (n r : ℕ) (hn : 1 ≤ n) :
    Valid ((univ : Finset (Finset (Fin n))).filter fun A ↦
      (n + r : ℝ) / 2 ≤ (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0).card ∨ A.card < r) r := by
  intro A hA B hB
  simp only [mem_filter, mem_univ, true_and, real_le] at hA hB
  have h1 := card_le_card (inter_subset_left : A ∩ B ⊆ A)
  have h2 := card_le_card (inter_subset_right : A ∩ B ⊆ B)
  rcases hA with hA | hA
  · rcases hB with hB | hB
    · have hu := card_union_add_card_inter (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0) (B.filter fun i : Fin n ↦ (i : ℕ) ≠ 0)
      have hsub : (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0) ∪ (B.filter fun i : Fin n ↦ (i : ℕ) ≠ 0) ⊆ ((univ : Finset (Fin n)).filter fun i : Fin n ↦ (i : ℕ) ≠ 0) := by
        intro x hx
        simp only [mem_union, mem_filter, mem_univ, true_and] at hx ⊢
        rcases hx with h | h
        · exact h.2
        · exact h.2
      have hle := card_le_card hsub
      rw [Z_univ n hn] at hle
      have hsub2 : (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0) ∩ (B.filter fun i : Fin n ↦ (i : ℕ) ≠ 0) ⊆ A ∩ B := by
        intro x hx
        simp only [mem_inter, mem_filter] at hx ⊢
        exact ⟨hx.1.1, hx.2.1⟩
      have := card_le_card hsub2
      omega
    · omega
  · omega

theorem G2_card (n r : ℕ) (hrn : r + 1 ≤ n) (heven : (n + r) % 2 = 0) :
    ((univ : Finset (Finset (Fin n))).filter fun A ↦
      (n + r : ℝ) / 2 ≤ (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0).card ∨ A.card < r).card =
    ∑ k ∈ range r, n.choose k + ∑ i ∈ Ico r ((n + r + 1) / 2), n.choose (i - r)
      + ∑ k ∈ Ico ((n + r + 1) / 2) (n + r + 1 - (n + r + 1) / 2), (n - 1).choose k := by
  refine card_of_levels _ r n (Fintype.card_fin n) (by omega) ?_ ?_ ?_
  · intro k hk
    rw [lev_all _ k, Fintype.card_fin]
    intro A hA
    simp only [mem_filter, mem_univ, true_and, real_le]
    omega
  · intro i hi1 hi2
    constructor
    · refine lev_none _ i ?_
      intro A hA
      simp only [mem_filter, mem_univ, true_and, real_le]
      have := Z_bounds A
      omega
    · rw [lev_all _ _, Fintype.card_fin]
      · rw [show n + r - i = n - (i - r) by omega, Nat.choose_symm (by omega)]
      · intro A hA
        simp only [mem_filter, mem_univ, true_and, real_le]
        have := Z_bounds A
        omega
  · intro k hk
    have : lev ((univ : Finset (Finset (Fin n))).filter fun A ↦
        (n + r : ℝ) / 2 ≤ (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0).card ∨ A.card < r) k =
        powersetCard k ((univ : Finset (Fin n)).filter fun i : Fin n ↦ (i : ℕ) ≠ 0) := by
      ext A
      simp only [mem_filter, mem_univ, true_and, real_le, mem_powersetCard]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · refine ⟨?_, h2⟩
          have hZ := Z_bounds A
          have heq : (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0).card = A.card := by omega
          have hall := card_filter_eq_iff.1 heq
          intro x hx
          simp only [mem_filter, mem_univ, true_and]
          exact hall x hx
        · omega
      · rintro ⟨h1, h2⟩
        refine ⟨Or.inl ?_, h2⟩
        have : (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0) = A := by
          refine filter_true_of_mem ?_
          intro x hx
          have := h1 hx
          simp only [mem_filter, mem_univ, true_and] at this
          exact this
        rw [this, h2]; omega
    rw [this, card_powersetCard, Z_univ n (by omega)]

end Extremal
end OMA.FF

open OMA.FF

theorem OMA.solution : type_of% @Erdos703.erdos_703.variants.frankl_furedi := by
  intro r
  filter_upwards [cond r] with n hn
  obtain ⟨h1, h2, h3⟩ := hn
  have hupper : ∀ F : Finset (Finset (Fin n)), Valid F r →
      F.card ≤ ∑ k ∈ range r, n.choose k + ∑ i ∈ Ico r ((n + r + 1) / 2), n.choose (i - r)
        + ∑ k ∈ Ico ((n + r + 1) / 2) (n + r + 1 - (n + r + 1) / 2), (n - 1).choose k :=
    fun F hF => upper r n (Fintype.card_fin n) h1 h2 h3 F hF
  have hT : ∀ G : Finset (Finset (Fin n)), Valid G r →
      G.card = ∑ k ∈ range r, n.choose k + ∑ i ∈ Ico r ((n + r + 1) / 2), n.choose (i - r)
        + ∑ k ∈ Ico ((n + r + 1) / 2) (n + r + 1 - (n + r + 1) / 2), (n - 1).choose k →
      Erdos703.T n r = G.card := by
    intro G hG hGc
    unfold Erdos703.T
    refine le_antisymm ?_ ?_
    · refine csSup_le ⟨G.card, G, hG, rfl⟩ ?_
      rintro k ⟨F, hF, rfl⟩
      rw [hGc]
      exact hupper F hF
    · refine le_csSup ⟨G.card, ?_⟩ ⟨G, hG, rfl⟩
      rintro k ⟨F, hF, rfl⟩
      rw [hGc]
      exact hupper F hF
  split_ifs with hpar
  · exact hT _ (G1_valid n r) (G1_card n r (by omega) hpar)
  · exact hT _ (G2_valid n r (by omega)) (G2_card n r (by omega) (by omega))
