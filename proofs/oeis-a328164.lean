import OMAStatements.S_oeis_a328164
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Data.Multiset.Replicate
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open OMA.S_oeis_a328164
open Filter Finset

namespace OMA.S_oeis_a328164.Proof

private theorem gcd_diff (x y d : ℕ) (hy : 0 < y) (hxy : y ≤ x) :
    Nat.gcd (x - y) (Nat.gcd (y - 1) d) = Nat.gcd (x - 1) (Nat.gcd (y - 1) d) := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd _ (Nat.gcd_dvd_right _ _)
    rw [show x - 1 = (x - y) + (y - 1) by omega]
    exact Nat.dvd_add (Nat.gcd_dvd_left _ _)
      (dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _))
  · apply Nat.dvd_gcd _ (Nat.gcd_dvd_right _ _)
    rw [show x - y = (x - 1) - (y - 1) by omega]
    exact Nat.dvd_sub (Nat.gcd_dvd_left _ _)
      (dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _))

private theorem list_qualifies (l : List ℕ) (hl : l.Pairwise (· ≥ ·))
    (hpos : ∀ x ∈ l, 0 < x) (h1 : 1 ∈ l) :
    ((l.zipWith (· - ·) l.tail).foldr Nat.gcd 0) = ((l.map (· - 1)).foldr Nat.gcd 0) := by
  induction l with
  | nil => simp at h1
  | cons x l ih =>
    have hx := List.pairwise_cons.mp hl
    cases l with
    | nil =>
      have he : x = 1 := by simpa [eq_comm] using h1
      subst x
      decide
    | cons y ys =>
      have h1tail : 1 ∈ y :: ys := by
        rcases List.mem_cons.mp h1 with he | ht
        · have hy' := hx.1 y (by simp)
          have hy0 := hpos y (by simp)
          have hy1 : y = 1 := by omega
          simp [hy1]
        · exact ht
      have htail := ih hx.2 (fun z hz => hpos z (List.mem_cons_of_mem _ hz)) h1tail
      change Nat.gcd (x - y) (((y :: ys).zipWith (· - ·) ys).foldr Nat.gcd 0) =
        Nat.gcd (x - 1) (((y :: ys).map (· - 1)).foldr Nat.gcd 0)
      simp only [List.tail_cons] at htail
      rw [htail]
      exact gcd_diff x y _ (hpos y (by simp)) (hx.1 y (by simp))

private theorem part_one_qualifies (n : ℕ) (p : n.Partition) (hp : 1 ∈ p.parts) :
    qualifies p := by
  let l := p.parts.sort (· ≥ ·)
  exact list_qualifies l (Multiset.pairwise_sort p.parts (· ≥ ·))
    (fun _ hx => p.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp hx)) ((Multiset.mem_sort (· ≥ ·)).mpr hp)

private abbrev NoOnes (n : ℕ) := { p : n.Partition // 1 ∉ p.parts }

private abbrev Pairs (n : ℕ) :=
  Σ p : NoOnes n, {k : ℕ // k ∈ p.val.parts.toFinset}

private theorem erase_mem_of_mem (s : Multiset ℕ) (k x : ℕ) (hx : x ∈ s.erase k) : x ∈ s :=
  Multiset.mem_of_le (Multiset.erase_le _ _) hx

private def split {n : ℕ} (a : Pairs n) : n.Partition where
  parts := a.1.val.parts.erase a.2.val + Multiset.replicate a.2.val 1
  parts_pos := by
    intro x hx
    rcases Multiset.mem_add.mp hx with h | h
    · exact a.1.val.parts_pos (erase_mem_of_mem _ _ _ h)
    · exact (Multiset.mem_replicate.mp h).2.symm ▸ Nat.one_pos
  parts_sum := by
    have ha : a.2.val ∈ a.1.val.parts := Multiset.mem_toFinset.mp a.2.prop
    have hs := congrArg Multiset.sum (Multiset.cons_erase ha)
    simp only [Multiset.sum_cons, a.1.val.parts_sum] at hs
    simpa [Multiset.sum_add, Multiset.sum_replicate, Nat.add_comm] using hs

private theorem split_count {n : ℕ} (a : Pairs n) : (split a).parts.count 1 = a.2.val := by
  have h : 1 ∉ a.1.val.parts.erase a.2.val :=
    fun he => a.1.prop (erase_mem_of_mem _ _ _ he)
  simp [split, Multiset.count_eq_zero.mpr h]

private theorem split_injective (n : ℕ) : Function.Injective (split (n := n)) := by
  rintro ⟨p, k⟩ ⟨q, l⟩ h
  have hkl : k.val = l.val := by
    have h' := congrArg (fun pp : n.Partition => pp.parts.count 1) h
    rw [split_count, split_count] at h'
    exact h'
  have he := congrArg Nat.Partition.parts h
  change p.val.parts.erase k.val + Multiset.replicate k.val 1 =
    q.val.parts.erase l.val + Multiset.replicate l.val 1 at he
  rw [← hkl] at he
  have hp := Multiset.cons_erase (Multiset.mem_toFinset.mp k.prop)
  have hq := Multiset.cons_erase (Multiset.mem_toFinset.mp l.prop)
  have hEq : p = q := by
    apply Subtype.ext
    apply Nat.Partition.ext
    rw [← hp, ← hq, ← hkl, add_right_cancel he]
  subst q
  exact congrArg (Sigma.mk p) (Subtype.ext hkl)

private theorem pairs_bound (n : ℕ) : (∑ a : NoOnes n, a.val.parts.toFinset.card) ≤ p n := by
  classical
  have h := Fintype.card_le_of_injective (split (n := n)) (split_injective n)
  rwa [Fintype.card_sigma, show (fun a : NoOnes n => Fintype.card {k : ℕ // k ∈ a.val.parts.toFinset}) =
    (fun a : NoOnes n => a.val.parts.toFinset.card) by
      funext a; exact Fintype.card_coe _] at h

private abbrev Thin (n k : ℕ) := { p : NoOnes n // p.val.parts.toFinset.card ≤ k }

private theorem card_parts_le (n : ℕ) (p : n.Partition) : p.parts.card ≤ n := by
  have h (s : Multiset ℕ) (hs : ∀ x ∈ s, 0 < x) : s.card ≤ s.sum := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons x s ih =>
      have hpos := hs x (by simp)
      have hle := ih (fun y hy => hs y (by simp [hy]))
      simp only [Multiset.card_cons, Multiset.sum_cons]
      omega
  exact (h _ (fun _ hmem => p.parts_pos hmem)).trans_eq p.parts_sum

private def encode {n k : ℕ} (p : Thin n k) (i : Fin k) : Fin (n + 1) × Fin (n + 1) :=
  if hi : i.val < p.val.val.parts.toFinset.card then
    let a := p.val.val.parts.toFinset.orderEmbOfFin rfl ⟨i.val, hi⟩
    have ha : a ∈ p.val.val.parts := Multiset.mem_toFinset.mp (orderEmbOfFin_mem _ rfl _)
    (⟨a, Nat.lt_succ_of_le (p.val.val.le_of_mem_parts ha)⟩,
     ⟨p.val.val.parts.count a, Nat.lt_succ_of_le
       ((Multiset.count_le_card _ _).trans (card_parts_le n p.val.val))⟩)
  else (0, 0)

private theorem encode_compare {n k : ℕ} (p q : Thin n k) (h : encode p = encode q)
    (x : ℕ) (hx : x ∈ p.val.val.parts) :
    x ∈ q.val.val.parts ∧ p.val.val.parts.count x = q.val.val.parts.count x := by
  let j := (p.val.val.parts.toFinset.orderIsoOfFin rfl).symm ⟨x, Multiset.mem_toFinset.mpr hx⟩
  let i : Fin k := ⟨j.val, j.isLt.trans_le p.prop⟩
  have hp : i.val < p.val.val.parts.toFinset.card := j.isLt
  have hpX : p.val.val.parts.toFinset.orderEmbOfFin rfl ⟨i.val, hp⟩ = x := by
    change (p.val.val.parts.toFinset.orderIsoOfFin rfl j).val = x
    simp [j]
  have he := congrFun h i
  unfold encode at he
  rw [dif_pos hp] at he
  have he1 := congrArg (fun v : Fin (n + 1) × Fin (n + 1) => v.1.val) he
  by_cases hq : i.val < q.val.val.parts.toFinset.card
  · rw [dif_pos hq] at he
    let y := q.val.val.parts.toFinset.orderEmbOfFin rfl ⟨i.val, hq⟩
    have hxy : x = y := by
      have h1 := congrArg (fun v : Fin (n + 1) × Fin (n + 1) => v.1.val) he
      simpa only [hpX] using h1
    have hcount := congrArg (fun v : Fin (n + 1) × Fin (n + 1) => v.2.val) he
    change p.val.val.parts.count _ = q.val.val.parts.count y at hcount
    rw [hpX, ← hxy] at hcount
    exact ⟨hxy ▸ (Multiset.mem_toFinset.mp (orderEmbOfFin_mem _ rfl _) :
      y ∈ q.val.val.parts), hcount⟩
  · simp only [dif_neg hq] at he1
    change p.val.val.parts.toFinset.orderEmbOfFin rfl ⟨i.val, hp⟩ = 0 at he1
    rw [hpX] at he1
    exact (p.val.val.parts_pos hx).ne' he1 |>.elim

private theorem thin_bound (n k : ℕ) : Fintype.card (Thin n k) ≤ (n + 1) ^ (2 * k) := by
  classical
  have hinj : Function.Injective (encode (n := n) (k := k)) := by
    intro p q h
    apply Subtype.ext
    apply Subtype.ext
    apply Nat.Partition.ext
    apply Multiset.ext.mpr
    intro x
    by_cases hp : x ∈ p.val.val.parts
    · exact (encode_compare p q h x hp).2
    by_cases hq : x ∈ q.val.val.parts
    · exact (encode_compare q p h.symm x hq).2.symm
    simp [Multiset.count_eq_zero.mpr hp, Multiset.count_eq_zero.mpr hq]
  have h := Fintype.card_le_of_injective _ hinj
  simpa [Fintype.card_fun, Fintype.card_prod, pow_mul, pow_two] using h

private theorem count_multisets {α : Type*} (s : Finset α) (f : α → Multiset ℕ) (a : ℕ) :
    (∑ i ∈ s, f i).count a = ∑ i ∈ s, (f i).count a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, Multiset.count_add, ih]

private theorem sum_multisets {α : Type*} (s : Finset α) (f : α → Multiset ℕ) :
    (∑ i ∈ s, f i).sum = ∑ i ∈ s, (f i).sum := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, Multiset.sum_add, ih]

private theorem pos_multisets {α : Type*} (s : Finset α) (f : α → Multiset ℕ)
    (hf : ∀ i ∈ s, ∀ a ∈ f i, 0 < a) :
    ∀ a ∈ ∑ i ∈ s, f i, 0 < a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    intro a ha
    rw [Finset.sum_insert hi] at ha
    rcases Multiset.mem_add.mp ha with h | h
    · exact hf i (mem_insert_self i s) a h
    · exact ih (fun j hj => hf j (mem_insert_of_mem hj)) a h

private def budget (m : ℕ) := m * (m + 2)

private def core {n m : ℕ} (f : Fin m → Fin (n / budget m + 1)) : Multiset ℕ :=
  ∑ i : Fin m, Multiset.replicate (f i).val (i.val + 2)

private theorem sum_core_le {n m : ℕ} (f : Fin m → Fin (n / budget m + 1)) :
    (core f).sum ≤ n := by
  unfold core
  rw [sum_multisets]
  simp only [Multiset.sum_replicate, nsmul_eq_mul]
  calc
    _ ≤ ∑ _ : Fin m, n / budget m * (m + 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.mul_le_mul (Nat.le_of_lt_succ (f i).isLt)
        (by have := i.isLt; omega)
    _ = n / budget m * budget m := by simp [budget]; ring
    _ ≤ n := Nat.div_mul_le_self _ _

private def pack {n m : ℕ} (f : Fin m → Fin (n / budget m + 1)) : n.Partition where
  parts := core f + Multiset.replicate (n - (core f).sum) 1
  parts_pos := by
    intro a ha
    rcases Multiset.mem_add.mp ha with h | h
    · apply pos_multisets Finset.univ _ _ _ h
      intro i _ t ht
      have he := (Multiset.mem_replicate.mp ht).2
      omega
    · have he := (Multiset.mem_replicate.mp h).2
      omega
  parts_sum := by
    simp only [Multiset.sum_add, Multiset.sum_replicate, nsmul_eq_mul, mul_one]
    exact (Nat.add_comm _ _).trans (Nat.sub_add_cancel (sum_core_le f))

private theorem pack_count {n m : ℕ} (f : Fin m → Fin (n / budget m + 1)) (i : Fin m) :
    (pack f).parts.count (i.val + 2) = (f i).val := by
  unfold pack core
  simp only [Multiset.count_add, count_multisets, Multiset.count_replicate]
  have h1 : 1 ≠ i.val + 2 := by omega
  rw [if_neg h1, add_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : j.val + 2 ≠ i.val + 2 := by
      intro he
      exact hji (Fin.ext (by omega))
    rw [if_neg hne]
  · simp

private theorem pack_bound (n m : ℕ) : (n / budget m + 1) ^ m ≤ p n := by
  classical
  have hi : Function.Injective (pack (n := n) (m := m)) := by
    intro f g h
    funext i
    apply Fin.ext
    simpa only [pack_count] using congrArg (fun P : n.Partition => P.parts.count (i.val + 2)) h
  simpa [Fintype.card_fun, p] using Fintype.card_le_of_injective _ hi

private theorem few_bound (n k : ℕ) :
    k * Fintype.card (NoOnes n) ≤ p n + k * Fintype.card (Thin n k) := by
  classical
  have hs : (∑ a : NoOnes n, k) ≤
      ∑ a : NoOnes n, (a.val.parts.toFinset.card + if a.val.parts.toFinset.card ≤ k then k else 0) := by
    apply Finset.sum_le_sum
    intro a _
    split <;> omega
  simp only [Finset.sum_add_distrib, Finset.sum_const, card_univ, nsmul_eq_mul] at hs
  rw [show (∑ a : NoOnes n, if a.val.parts.toFinset.card ≤ k then k else 0) =
      k * Fintype.card (Thin n k) by
    rw [show Fintype.card (Thin n k) = ((Finset.univ : Finset (NoOnes n)).filter
      (fun a => a.val.parts.toFinset.card ≤ k)).card from Fintype.card_subtype _]
    have hCard : (Finset.univ.filter (fun a : NoOnes n => a.val.parts.toFinset.card ≤ k)).card =
        ∑ a : NoOnes n, if a.val.parts.toFinset.card ≤ k then 1 else 0 :=
      (Finset.sum_boole (R := ℕ) _ _).symm
    rw [hCard, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    split <;> simp_all] at hs
  have hp := pairs_bound n
  rw [Nat.mul_comm k]
  exact hs.trans (Nat.add_le_add_right hp _)

private theorem pow_bound (n m : ℕ) (hm : 0 < m) : (n + 1) ^ m ≤ budget m ^ m * p n := by
  have hD : 0 < budget m := Nat.mul_pos hm (by omega)
  have hn : n + 1 ≤ budget m * (n / budget m + 1) := by
    have hmod := Nat.mod_lt n hD
    have hDiv := Nat.mod_add_div n (budget m)
    rw [Nat.mul_add, mul_one]
    omega
  calc
    (n + 1) ^ m ≤ (budget m * (n / budget m + 1)) ^ m := Nat.pow_le_pow_left hn _
    _ = budget m ^ m * (n / budget m + 1) ^ m := by rw [mul_pow]
    _ ≤ budget m ^ m * p n := Nat.mul_le_mul_left _ (pack_bound n m)

private theorem count_bounds (n : ℕ) : a n ≤ p n ∧ p n - a n ≤ Fintype.card (NoOnes n) := by
  classical
  have hCard : Fintype.card {x : n.Partition // qualifies x} = a n := Fintype.card_subtype _
  refine ⟨?_, ?_⟩
  · rw [← hCard]
    exact Fintype.card_subtype_le _
  · rw [← hCard]
    change Fintype.card n.Partition - Fintype.card {x : n.Partition // qualifies x} ≤ _
    rw [← Fintype.card_subtype_compl]
    exact Fintype.card_subtype_mono _ _ (fun x h hn => h (part_one_qualifies n x hn))

private theorem count_pos (n : ℕ) : 0 < p n :=
  Fintype.card_pos_iff.mpr ⟨Nat.Partition.indiscrete n⟩

private theorem error_bound (n k : ℕ) (hk : 0 < k) :
    1 - (a n : ℝ) / p n ≤ 1 / (k : ℝ) + (budget (2 * k + 1) : ℝ) ^ (2 * k + 1) / (n + 1 : ℝ) := by
  classical
  have hp : 0 < (p n : ℝ) := by exact_mod_cast count_pos n
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have h := count_bounds n
  have he : (p n : ℝ) - a n ≤ Fintype.card (NoOnes n) := by
    rw [← Nat.cast_sub h.1]
    exact_mod_cast h.2
  have hF : (k : ℝ) * Fintype.card (NoOnes n) ≤ (p n : ℝ) + k * Fintype.card (Thin n k) := by
    exact_mod_cast few_bound n k
  have hQ : (Fintype.card (NoOnes n) : ℝ) ≤ p n / (k : ℝ) + Fintype.card (Thin n k) := by
    have hAux : ((Fintype.card (NoOnes n) : ℝ) - Fintype.card (Thin n k)) ≤ p n / (k : ℝ) := by
      apply (le_div_iff₀ hk').mpr
      nlinarith
    linarith
  have hT : (Fintype.card (Thin n k) : ℝ) / p n ≤
      (budget (2 * k + 1) : ℝ) ^ (2 * k + 1) / (n + 1 : ℝ) := by
    apply (div_le_div_iff₀ hp (by positivity : 0 < (n + 1 : ℝ))).mpr
    have hh : Fintype.card (Thin n k) * (n + 1) ≤ budget (2 * k + 1) ^ (2 * k + 1) * p n := by
      calc
        _ ≤ (n + 1) ^ (2 * k) * (n + 1) := Nat.mul_le_mul_right _ (thin_bound n k)
        _ = (n + 1) ^ (2 * k + 1) := (pow_succ _ _).symm
        _ ≤ _ := pow_bound _ _ (by omega)
    exact_mod_cast hh
  have hR : ((p n : ℝ) - a n) / p n ≤ 1 / (k : ℝ) + (Fintype.card (Thin n k) : ℝ) / p n := by
    apply (div_le_iff₀ hp).mpr
    have hMul : (1 / (k : ℝ) + (Fintype.card (Thin n k) : ℝ) / p n) * p n =
        p n / (k : ℝ) + Fintype.card (Thin n k) := by
      field_simp [hp.ne', hk'.ne']
    rw [hMul]
    exact he.trans hQ
  rw [sub_div, div_self hp.ne'] at hR
  linarith

end OMA.S_oeis_a328164.Proof

open OMA.S_oeis_a328164.Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a328164.main := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / ε)
  have hpos : 0 < (k : ℝ) := lt_trans (by positivity) hk
  have hk' : 0 < k := by exact_mod_cast hpos
  have hSmallK : 1 / (k : ℝ) < ε / 2 := by
    apply (div_lt_iff₀ hpos).mpr
    have ht := (div_lt_iff₀ hε).mp hk
    linarith
  let C : ℝ := (budget (2 * k + 1) : ℝ) ^ (2 * k + 1)
  obtain ⟨N, hN⟩ := exists_nat_gt (C / (ε / 2))
  refine ⟨N, ?_⟩
  intro n hn
  have hposN : 0 < (n + 1 : ℝ) := by positivity
  have hSmallN : C / (n + 1 : ℝ) < ε / 2 := by
    apply (div_lt_iff₀ hposN).mpr
    have hN' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have ht : C / (ε / 2) < (n : ℝ) + 1 := hN.trans_le (by linarith)
    have hm := (div_lt_iff₀ (by positivity : 0 < ε / 2)).mp ht
    simpa only [mul_comm] using hm
  have hp : 0 < (p n : ℝ) := by exact_mod_cast count_pos n
  have ha : (a n : ℝ) ≤ p n := by exact_mod_cast (count_bounds n).1
  have he := error_bound n k hk'
  change 1 - (a n : ℝ) / p n ≤ 1 / (k : ℝ) + C / (n + 1 : ℝ) at he
  change dist ((a n : ℝ) / p n) 1 < ε
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ((div_le_iff₀ hp).mpr (by simpa using ha)))]
  linarith
