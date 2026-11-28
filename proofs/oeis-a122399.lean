import OMAStatements.S_oeis_a122399
import Mathlib

/-
A122399: a(n) = sum over j of j^n j! S(n,j) satisfies a(n + p - 1) = a(n) modulo every prime p,
for all n >= 1.

Method, for any S with the Stirling recurrence S(n+1, j+1) = (j+1) S(n, j+1) + S(n, j):
- surj: S(n,j) j! = sum over i <= j of (-1)^(j+i) C(j,i) i^n, by induction on n.
- S_zero: S(n,j) = 0 for j > n, so the sum can be extended to any longer range.
- fermat: i^(n + p - 1) = i^n modulo p for n >= 1.
- genperP: the terms with j >= p vanish modulo p because p divides j!; for j < p both j^n and
  S(n,j) j! are unchanged modulo p when n grows by p - 1.
-/

namespace OMA.P122399

lemma chooseK (j i : ℕ) : (i : ℤ) * ((j + 1).choose i : ℤ) =
    (j + 1) * (((j + 1).choose i : ℤ) - (j.choose i : ℤ)) := by
  rcases i with _ | m
  · simp
  · have h1 := Nat.add_one_mul_choose_eq j m
    have h2 := Nat.choose_succ_succ j m
    zify at h1 h2
    push_cast
    linear_combination (-1 : ℤ) * h1 - ((j : ℤ) + 1) * h2

lemma surj (S : ℕ → ℕ → ℕ) (h00 : S 0 0 = 1) (hn0 : ∀ n, S (n + 1) 0 = 0)
    (h0j : ∀ j, S 0 (j + 1) = 0)
    (hrec : ∀ n j, S (n + 1) (j + 1) = (j + 1) * S n (j + 1) + S n j) :
    ∀ n j : ℕ, (S n j : ℤ) * (j.factorial : ℤ) =
      ∑ i ∈ Finset.range (j + 1), (-1 : ℤ) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ n := by
  intro n
  induction n with
  | zero =>
    intro j
    have e : ∀ i : ℕ, (-1 : ℤ) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ 0 =
        (-1) ^ j * ((-1) ^ i * (j.choose i : ℤ)) := fun i => by rw [pow_add]; ring
    simp only [e, ← Finset.mul_sum, Int.alternating_sum_range_choose]
    rcases j with _ | j
    · simp [h00]
    · simp [h0j]
  | succ n ih =>
    intro j
    rcases j with _ | j
    · simp [hn0]
    · have ih1 := ih (j + 1)
      have ih0 := ih j
      have ext : ∑ i ∈ Finset.range (j + 1), (-1 : ℤ) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ n =
          ∑ i ∈ Finset.range (j + 1 + 1), (-1 : ℤ) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ n := by
        rw [Finset.sum_range_succ _ (j + 1)]
        simp [Nat.choose_succ_self]
      rw [ext] at ih0
      have lhs : (S (n + 1) (j + 1) : ℤ) * ((j + 1).factorial : ℤ) =
          (j + 1) * ((S n (j + 1) : ℤ) * ((j + 1).factorial : ℤ)) +
            (j + 1) * ((S n j : ℤ) * (j.factorial : ℤ)) := by
        rw [hrec, Nat.factorial_succ]
        push_cast
        ring
      rw [lhs, ih1, ih0, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have K := chooseK j i
      have s : (-1 : ℤ) ^ (j + i) = -(-1) ^ (j + 1 + i) := by
        rw [show j + 1 + i = j + i + 1 by ring, pow_succ]
        ring
      rw [s, pow_succ]
      linear_combination (-((-1 : ℤ) ^ (j + 1 + i)) * (i : ℤ) ^ n) * K

lemma sum_modEq {ι : Type*} (s : Finset ι) (f g : ι → ℤ) (m : ℤ)
    (h : ∀ i ∈ s, f i ≡ g i [ZMOD m]) : ∑ i ∈ s, f i ≡ ∑ i ∈ s, g i [ZMOD m] := by
  rw [Int.modEq_iff_dvd, ← Finset.sum_sub_distrib]
  exact Finset.dvd_sum fun i hi => Int.modEq_iff_dvd.1 (h i hi)

lemma S_zero (S : ℕ → ℕ → ℕ) (h0j : ∀ j, S 0 (j + 1) = 0)
    (hrec : ∀ n j, S (n + 1) (j + 1) = (j + 1) * S n (j + 1) + S n j) :
    ∀ n j : ℕ, n < j → S n j = 0 := by
  intro n
  induction n with
  | zero =>
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact h0j i
  | succ n ih =>
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [hrec, ih (i + 1) (by omega), ih i (by omega)]
    simp

lemma fermat (p : ℕ) (hp : p.Prime) (i n : ℕ) (hn : 1 ≤ n) :
    i ^ (n + (p - 1)) ≡ i ^ n [MOD p] := by
  have := Fact.mk hp
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e : m + 1 + (p - 1) = m + p := by have := hp.pos; omega
  rw [e, pow_add, ZMod.pow_card, pow_succ]

lemma genperP (S : ℕ → ℕ → ℕ) (h00 : S 0 0 = 1) (hn0 : ∀ n, S (n + 1) 0 = 0)
    (h0j : ∀ j, S 0 (j + 1) = 0)
    (hrec : ∀ n j, S (n + 1) (j + 1) = (j + 1) * S n (j + 1) + S n j)
    (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) (w w' : ℕ → ℤ)
    (hw : ∀ j < p, w' j ≡ w j [ZMOD (p : ℤ)]) :
    (∑ j ∈ Finset.range (n + (p - 1) + 1),
        w' j * ((S (n + (p - 1)) j : ℤ) * (j.factorial : ℤ))) ≡
      ∑ j ∈ Finset.range (n + 1), w j * ((S n j : ℤ) * (j.factorial : ℤ)) [ZMOD (p : ℤ)] := by
  have trunc : ∀ (m : ℕ) (v : ℕ → ℤ),
      (∑ j ∈ Finset.range (m + 1), v j * ((S m j : ℤ) * (j.factorial : ℤ))) ≡
        ∑ j ∈ Finset.range p, v j * ((S m j : ℤ) * (j.factorial : ℤ)) [ZMOD (p : ℤ)] := by
    intro m v
    have e1 : ∑ j ∈ Finset.range (m + 1), v j * ((S m j : ℤ) * (j.factorial : ℤ)) =
        ∑ j ∈ Finset.range (m + 1 + p), v j * ((S m j : ℤ) * (j.factorial : ℤ)) := by
      refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j _ hj => ?_
      rw [S_zero S h0j hrec m j (by simpa using hj)]
      simp
    rw [e1, Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le p) (by omega : p ≤ m + 1 + p),
      Int.modEq_iff_dvd, sub_add_cancel_left]
    refine dvd_neg.2 (Finset.dvd_sum fun j hj => ?_)
    have hj' : p ≤ j := (Finset.mem_Ico.1 hj).1
    exact Dvd.dvd.mul_left
      (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 (Nat.dvd_factorial hp.pos hj')) _) _
  refine (trunc _ w').trans (Int.ModEq.trans ?_ (trunc n w).symm)
  refine sum_modEq _ _ _ _ fun j hj => Int.ModEq.mul (hw j (Finset.mem_range.1 hj)) ?_
  rw [surj S h00 hn0 h0j hrec, surj S h00 hn0 h0j hrec]
  refine sum_modEq _ _ _ _ fun i _ => Int.ModEq.mul_left _ ?_
  have := fermat p hp i n hn
  exact_mod_cast (Int.natCast_modEq_iff.2 this)

lemma main' (S : ℕ → ℕ → ℕ) (h00 : S 0 0 = 1) (hn0 : ∀ n, S (n + 1) 0 = 0)
    (h0j : ∀ j, S 0 (j + 1) = 0)
    (hrec : ∀ n j, S (n + 1) (j + 1) = (j + 1) * S n (j + 1) + S n j) :
    ∀ p n : ℕ, p.Prime → 1 ≤ n →
      (∑ j ∈ Finset.range (n + (p - 1) + 1), j ^ (n + (p - 1)) * j.factorial * S (n + (p - 1)) j) ≡
        ∑ j ∈ Finset.range (n + 1), j ^ n * j.factorial * S n j [MOD p] := by
  intro p n hp hn
  have e : ∀ m, ∑ j ∈ Finset.range (m + 1), j ^ m * j.factorial * S m j =
      ∑ j ∈ Finset.range (m + 1), j ^ m * (S m j * j.factorial) :=
    fun m => Finset.sum_congr rfl fun j _ => by ring
  rw [e, e]
  have := genperP S h00 hn0 h0j hrec p hp n hn (fun j => (j : ℤ) ^ n)
    (fun j => (j : ℤ) ^ (n + (p - 1))) fun j _ => by
      have := fermat p hp j n hn
      exact_mod_cast (Int.natCast_modEq_iff.2 this)
  exact_mod_cast this

end OMA.P122399

theorem OMA.solution : type_of% @OMA.S_oeis_a122399.main :=
  OMA.P122399.main' OMA.S_oeis_a122399.stirling2 rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
