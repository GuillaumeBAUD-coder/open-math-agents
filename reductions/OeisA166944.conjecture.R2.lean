import FormalConjectures.OEIS.«166944»

/-!
For a canonical record r, fewer than one nonunit increment per complete block
on average in (r + 2, 2r] suffices to determine the next record from a(2r).
The length of a block is twice the integer square root of 4r + 1.

The affine-run induction follows the approach of the RowlandSequence sibling
proof. The small-divisor test for the two parities builds on Shevelev's
Three theorems on twin primes and @desenyon's reduction R1.
-/

open OeisA166944
namespace OMA.R_OeisA166944_conjecture_R2

private theorem step {n : ℕ} (hn : 2 ≤ n) :
    a n = a (n - 1) + (if n % 2 = 0 then n else n - 2).gcd (a (n - 1)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp only [a, Nat.add_sub_cancel]
  split <;> rfl

private theorem diff {n : ℕ} (hn : 2 ≤ n) : d n = (if n % 2 = 0 then n else n - 2).gcd (a (n - 1)) := by
  unfold d
  rw [step hn, Nat.add_sub_cancel_left]

private theorem growth {n : ℕ} (hn : 2 ≤ n) : a (n - 1) + 1 ≤ a n := by
  by_cases h : n = 2
  · subst n; decide
  have hi : 0 < (if n % 2 = 0 then n else n - 2) := by split <;> omega
  rw [step hn]
  have := Nat.gcd_pos_of_pos_left (a (n - 1)) hi
  omega

private theorem offset_mono {n b : ℕ} (hb : 2 ≤ b) (h : b ≤ n) :
    a b + n ≤ a n + b := by
  induction n, h using Nat.le_induction with
  | base => omega
  | succ n hn ih =>
    have := growth (n := n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at this
    omega

private theorem parity {n : ℕ} (hn : 2 ≤ n) : a n % 2 = n % 2 := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have hstep := step (n := n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hstep
    have ho : (if (n + 1) % 2 = 0 then n + 1 else n + 1 - 2).gcd (a n) % 2 = 1 := by
      by_contra h
      have he : 2 ∣ (if (n + 1) % 2 = 0 then n + 1 else n + 1 - 2).gcd (a n) := Nat.dvd_of_mod_eq_zero (by omega)
      have h₁ := Nat.mod_eq_zero_of_dvd (he.trans (Nat.gcd_dvd_left ..))
      have h₂ := Nat.mod_eq_zero_of_dvd (he.trans (Nat.gcd_dvd_right ..))
      split at h₁ <;> omega
    omega

/-- The gcd divides the distance of the preceding value from three times
the gcd index. This bounds every term by the line of slope three. -/
private theorem upper (n : ℕ) : a n ≤ 3 * n := by
  induction n with
  | zero => decide
  | succ n ih =>
    by_cases hs : n < 3
    · interval_cases n <;> decide
    let i := if (n + 1) % 2 = 0 then n + 1 else n + 1 - 2
    let g := i.gcd (a n)
    have hstep : a (n + 1) = a n + g := by simpa [g, i] using step (n := n + 1) (by omega)
    have hx : g ∣ 3 * i := dvd_mul_of_dvd_right (Nat.gcd_dvd_left ..) 3
    have ha : g ∣ a n := Nat.gcd_dvd_right ..
    by_cases h : a n < 3 * i
    · have := Nat.le_of_dvd (by omega : 0 < 3 * i - a n) (Nat.dvd_sub hx ha)
      have hi : i ≤ n + 1 := by dsimp [i]; split <;> omega
      omega
    · have par := parity (n := n) (by omega)
      dsimp only [i] at hx h
      split at h <;> rename_i e
      · omega
      · rw [if_neg e] at hx
        have odd : 3 * (n + 1 - 2) < a n := by omega
        have := Nat.le_of_dvd (by omega : 0 < a n - 3 * (n + 1 - 2)) (Nat.dvd_sub ha hx)
        omega

private theorem affine_diff {n c : ℕ} (hn : 2 ≤ n) (hc : 1 ≤ c)
    (h : a (n - 1) = (n - 1) + c) :
    d n = if n % 2 = 0 then n.gcd (c - 1) else (n - 2).gcd (c + 1) := by
  rw [diff hn, h]
  split <;> rename_i he
  · rw [show n - 1 + c = (c - 1) + n by omega, Nat.gcd_add_self_right]
  · rw [show n - 1 + c = (c + 1) + (n - 2) by omega, Nat.gcd_add_self_right]

private theorem add_diff {n : ℕ} (hn : 2 ≤ n) : a n = a (n - 1) + d n := by
  have := growth hn
  unfold d
  omega

private theorem affine_run {b e c : ℕ} (hb : 2 ≤ b) (start : a b = b + c)
    (unit : ∀ j, b < j → j ≤ e → d j = 1) :
    ∀ j, b ≤ j → j ≤ e → a j = j + c := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact fun _ => start
  | succ j hj ih =>
    intro he
    have h := add_diff (n := j + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h
    rw [unit _ (by omega) he, ih (by omega)] at h
    omega

private theorem progression {b s l : ℕ} (hs : s ≤ b) (hl : 0 < l) :
    ∃ t, b < l * t + s ∧ l * t + s ≤ b + l := by
  refine ⟨(b - s) / l + 1, ?_⟩
  have := Nat.mod_add_div (b - s) l
  have := Nat.mod_lt (b - s) hl
  rw [Nat.mul_add, Nat.mul_one]
  omega

private theorem sieve {r b c : ℕ} (hr : 7 ≤ r) (hb : r + 2 ≤ b)
    (hc : 2 * r - 2 ≤ c) (hmax : c ≤ 4 * r) (even : c % 2 = 0) (start : a b = b + c)
    (unit : ∀ j, b < j → j ≤ b + (2 * (4 * r + 1).sqrt) → d j = 1) :
    (c - 1).Prime ∧ (c + 1).Prime := by
  have affine := affine_run (by omega : 2 ≤ b) start unit
  have small : (4 * r + 1).sqrt < r := by
    apply Nat.sqrt_lt.mpr
    nlinarith
  have bound : ∀ x, 1 < x → x ≤ 4 * r + 1 → ¬ x.Prime → x.minFac ≤ (4 * r + 1).sqrt := by
    intro x hx hm hn
    apply Nat.le_sqrt.mpr
    have := Nat.minFac_sq_le_self (by omega : 0 < x) hn
    nlinarith
  have forbid : ∀ j, b < j → j ≤ b + (2 * (4 * r + 1).sqrt) →
      (if j % 2 = 0 then j.gcd (c - 1) else (j - 2).gcd (c + 1)) = 1 := by
    intro j hj he
    rw [← affine_diff (by omega) (by omega) (affine _ (by omega) (by omega))]
    exact unit j hj he
  constructor <;> by_contra hn
  · let p := (c - 1).minFac
    have hp : 2 ≤ p := (Nat.minFac_prime (by omega : c - 1 ≠ 1)).two_le
    have hp' : p ≤ (4 * r + 1).sqrt := bound _ (by omega) (by omega) hn
    obtain ⟨t, lo, hi⟩ := progression (b := b) (s := 0) (l := 2 * p) (by omega) (by omega)
    simp only [Nat.add_zero] at lo hi
    have e := forbid (2 * p * t) lo (by omega)
    rw [if_pos (by simp [Nat.mul_assoc])] at e
    have div : p ∣ (2 * p * t).gcd (c - 1) :=
      Nat.dvd_gcd (dvd_mul_of_dvd_left (dvd_mul_left p 2) t) (Nat.minFac_dvd _)
    rw [e] at div
    have := Nat.le_of_dvd (by decide : 0 < 1) div
    omega
  · let p := (c + 1).minFac
    have hp : 2 ≤ p := (Nat.minFac_prime (by omega : c + 1 ≠ 1)).two_le
    have pd : p ∣ c + 1 := Nat.minFac_dvd _
    have odd : p % 2 = 1 := by
      by_contra h
      have he : 2 ∣ p := Nat.dvd_of_mod_eq_zero (by omega)
      have := Nat.mod_eq_zero_of_dvd (he.trans pd)
      omega
    have hp' : p ≤ (4 * r + 1).sqrt := bound _ (by omega) (by omega) hn
    obtain ⟨t, lo, hi⟩ := progression (b := b) (s := p + 2) (l := 2 * p) (by omega) (by omega)
    have e := forbid _ lo (by omega)
    have he : (2 * p * t) % 2 = 0 := by simp [Nat.mul_assoc]
    rw [if_neg (by omega), show 2 * p * t + (p + 2) - 2 = 2 * p * t + p by omega] at e
    have div : p ∣ (2 * p * t + p).gcd (c + 1) :=
      Nat.dvd_gcd (dvd_add (dvd_mul_of_dvd_left (dvd_mul_left p 2) t) dvd_rfl) pd
    rw [e] at div
    have := Nat.le_of_dvd (by decide : 0 < 1) div
    omega

/-- In the doubling interval a gcd exceeding r would equal its index.
Parity excludes the even case. In the odd case the only possible quotient
of the preceding term by that index is three, again excluded by parity. -/
private theorem early_bound {r n : ℕ} (hr : 7 ≤ r) (hs : a (r + 2) = 3 * r)
    (hlo : r + 2 < n) (hhi : n ≤ 2 * r) : d n ≤ r := by
  by_contra h
  have hd := diff (n := n) (by omega)
  have dv : d n ∣ (if n % 2 = 0 then n else n - 2) := hd ▸ Nat.gcd_dvd_left ..
  have da : d n ∣ a (n - 1) := hd ▸ Nat.gcd_dvd_right ..
  have par := parity (n := n - 1) (by omega)
  split at dv <;> rename_i e
  · have eq := Nat.eq_of_dvd_of_lt_two_mul (by omega : n ≠ 0) dv (by omega)
    have two : 2 ∣ d n := Nat.dvd_of_mod_eq_zero (by omega)
    have := Nat.mod_eq_zero_of_dvd (two.trans da)
    omega
  · have eq := Nat.eq_of_dvd_of_lt_two_mul (by omega : n - 2 ≠ 0) dv (by omega)
    rw [← eq] at da
    obtain ⟨t, ht⟩ := da
    have lower := offset_mono (b := r + 2) (n := n - 1) (by omega) (by omega)
    rw [hs] at lower
    have up := upper (n - 1)
    have t₁ : 2 < t := by
      by_contra! ht'
      have := Nat.mul_le_mul_left (n - 2) ht'
      omega
    have t₂ : t < 4 := by
      by_contra! ht'
      have := Nat.mul_le_mul_left (n - 2) ht'
      omega
    rw [show t = 3 by omega] at ht
    omega

/-- Once the offset is flanked by primes, the first possible nonunit
increment occurs at c + 3, where the odd gcd equals c + 1. -/
private theorem locked {b c : ℕ} (hb : 2 ≤ b) (hc : 6 ≤ c) (even : c % 2 = 0)
    (start : a b = b + c) (room : b ≤ c + 2) (pr : (c - 1).Prime ∧ (c + 1).Prime) :
    d (c + 3) = c + 1 ∧ a (c + 3) = 3 * (c + 1) ∧ ∀ n, b < n → n ≤ c + 2 → d n = 1 := by
  have next : ∀ n, b < n → n ≤ c + 2 → a (n - 1) = n - 1 + c → d n = 1 := by
    intro n hn he h
    rw [affine_diff (by omega) (by omega) h]
    split <;> rename_i e
    · apply Nat.Coprime.gcd_eq_one
      apply Nat.Coprime.symm
      apply pr.1.coprime_iff_not_dvd.mpr
      intro dv
      have := Nat.eq_of_dvd_of_lt_two_mul (by omega : n ≠ 0) dv (by omega)
      omega
    · apply Nat.Coprime.gcd_eq_one
      apply Nat.Coprime.symm
      apply pr.2.coprime_iff_not_dvd.mpr
      intro dv
      have := Nat.le_of_dvd (by omega : 0 < n - 2) dv
      omega
  have run : ∀ n, b ≤ n → n ≤ c + 2 → a n = n + c := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact fun _ => start
    | succ n hn ih =>
      intro he
      have prev := ih (by omega)
      have hg := next (n + 1) (by omega) he (by simpa using prev)
      have ha := add_diff (n := n + 1) (by omega)
      simp only [Nat.add_sub_cancel] at ha
      omega
  have last := run (c + 2) room (by omega)
  have hj := affine_diff (n := c + 3) (c := c) (by omega) (by omega) (by simpa using last)
  rw [if_neg (by omega)] at hj
  simp at hj
  have ha := add_diff (n := c + 3) (by omega)
  simp at ha
  exact ⟨hj, by omega, fun n hn he => next n hn he (run _ (by omega) (by omega))⟩

/-- There is an empty block of length w when the number of marked indices is
smaller than the number of disjoint complete blocks in the interval. -/
private theorem empty_block (s : Finset ℕ) {l u w : ℕ} (hlu : l ≤ u)
    (few : s.card < (u - l) / w) :
    ∃ b, l ≤ b ∧ b + w ≤ u ∧ ∀ j, b < j → j ≤ b + w → j ∉ s := by
  classical
  by_contra! fail
  let m := (u - l) / w
  have bad (i : ℕ) (hi : i < m) :
      ∃ j, l + w * i < j ∧ j ≤ l + w * i + w ∧ j ∈ s := by
    apply fail _ (by omega)
    have h₁ := Nat.mul_le_mul_left w (show i + 1 ≤ m by omega)
    have h₂ := Nat.div_mul_le_self (u - l) w
    dsimp [m] at h₁
    rw [Nat.mul_comm ((u - l) / w) w] at h₂
    rw [Nat.mul_add, Nat.mul_one] at h₁
    omega
  let f (i : ℕ) := if hi : i < m then (bad i hi).choose else 0
  have spec (i : ℕ) (hi : i < m) : l + w * i < f i ∧ f i ≤ l + w * i + w ∧ f i ∈ s := by
    simpa [f, hi] using (bad i hi).choose_spec
  have ord {i j : ℕ} (hij : i < j) (hj : j < m) : f i < f j := by
    have hi := spec i (by omega)
    have hj' := spec j hj
    have h := Nat.mul_le_mul_left w (show i + 1 ≤ j by omega)
    rw [Nat.mul_add, Nat.mul_one] at h
    omega
  have bound := Finset.card_le_card_of_injOn (s := Finset.range m) (t := s) f
    (fun i hi => (spec i (Finset.mem_range.mp hi)).2.2)
    (by
      intro i hi j hj he
      rcases lt_trichotomy i j with h | h | h
      · exact False.elim ((ord h (Finset.mem_range.mp hj)).ne he)
      · exact h
      · exact False.elim ((ord h (Finset.mem_range.mp hi)).ne he.symm))
  rw [Finset.card_range] at bound
  omega

/-- A single count in the interval following the old record suffices to
produce the next record, its index, and its twin-prime certificate. -/
theorem next_of_sparse {r : ℕ} (hr : 7 ≤ r) (hs : a (r + 2) = 3 * r)
    (few : ((Finset.Ioc (r + 2) (2 * r)).filter (fun n => 1 < d n)).card <
      (r - 2) / (2 * (4 * r + 1).sqrt)) :
    ∃ q, r < q ∧ q = a (2 * r) - 2 * r + 1 ∧ d (q + 2) = q ∧
      a (q + 2) = 3 * q ∧ IsGreaterTwinPrime q ∧
      ∀ j, r + 2 < j → j < q + 2 → d j ≤ r := by
  obtain ⟨b, hb, he, clear⟩ := empty_block
    ((Finset.Ioc (r + 2) (2 * r)).filter (fun n => 1 < d n))
    (l := r + 2) (u := 2 * r) (w := 2 * (4 * r + 1).sqrt) (by omega)
    (by rwa [show 2 * r - (r + 2) = r - 2 by omega])
  have unit (j : ℕ) (hj : b < j) (hw : j ≤ b + 2 * (4 * r + 1).sqrt) : d j = 1 := by
    have h := clear j hj hw
    simp only [Finset.mem_filter, Finset.mem_Ioc, not_and] at h
    have h' := h ⟨by omega, by omega⟩
    have hpos := growth (n := j) (by omega)
    unfold d at *
    omega
  let c := a b - b
  have off := offset_mono (b := r + 2) (n := b) (by omega) hb
  rw [hs] at off
  have sta : a b = b + c := by dsimp [c]; omega
  have up := upper b
  have par := parity (n := b) (by omega)
  have even : c % 2 = 0 := by omega
  have twin := sieve hr hb (c := c) (by omega) (by omega) even sta unit
  have lock := locked (by omega : 2 ≤ b) (by omega : 6 ≤ c) even sta (by omega) twin
  have atDouble := affine_run (by omega : 2 ≤ b) sta (e := 2 * r)
    (fun j hj he => lock.2.2 j hj (by omega)) (2 * r) (by omega) le_rfl
  refine ⟨c + 1, by omega, by omega, lock.1, lock.2.1, ⟨twin.2, ?_⟩, ?_⟩
  · simpa using twin.1
  · intro j hlo hhi
    by_cases hj : j ≤ b
    · exact early_bound hr hs hlo (by omega)
    · have := lock.2.2 j (by omega) (by omega)
      omega

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem prefix_data : ∀ i : Fin 664,
    let j : ℕ := if 315 < i.val then 315 else if 141 < i.val then 141
      else if 45 < i.val then 45 else if 15 < i.val then 15 else 9
    d i.val ≤ 5 ∨ ((d i.val).Prime ∧ (d i.val - 2).Prime) ∨
      (2 ≤ j ∧ j < i.val ∧ d i.val ≤ d j) := by
  decide +kernel

set_option maxRecDepth 12000 in
private theorem seed : d 663 = 661 ∧ a 663 = 1983 := by decide +kernel

/-- Bound the number of nonunit even-indexed increments in the first
doubling interval of each canonical increment. -/
def H1 : Prop := ∀ r : ℕ, 661 ≤ r → d (r + 2) = r →
  let blocks := (r - 2) / (2 * (4 * r + 1).sqrt)
  (((Finset.Ioc (r + 2) (2 * r)).filter (fun n => 1 < d n)).filter
    (fun n => n % 2 = 0)).card < 2 * blocks / 3

/-- Bound the nonunit odd-indexed increments in the same interval. -/
def H2 : Prop := ∀ r : ℕ, 661 ≤ r → d (r + 2) = r →
  let blocks := (r - 2) / (2 * (4 * r + 1).sqrt)
  (((Finset.Ioc (r + 2) (2 * r)).filter (fun n => 1 < d n)).filter
    (fun n => n % 2 ≠ 0)).card ≤ blocks - 2 * blocks / 3

theorem main : H1 → H2 → type_of% @OeisA166944.conjecture := by
  intro even odd R hR hrec
  obtain ⟨n, hn, eqR, record⟩ := hrec
  by_cases small : n ≤ 663
  · rcases prefix_data ⟨n, by omega⟩ with h | h | ⟨hj, hjn, hd⟩
    · change d n ≤ 5 at h
      omega
    · exact eqR ▸ h
    · have := record _ hj hjn
      change d n ≤ _ at hd
      omega
  have cover : ∀ t r : ℕ, 661 ≤ r → d (r + 2) = r → a (r + 2) = 3 * r →
      r + 2 < n → n = r + 2 + t → IsGreaterTwinPrime R := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro r hr hd ha hlo ht
      let jumps := (Finset.Ioc (r + 2) (2 * r)).filter (fun j => 1 < d j)
      let blocks := (r - 2) / (2 * (4 * r + 1).sqrt)
      have e : (jumps.filter (fun j => j % 2 = 0)).card < 2 * blocks / 3 := even r hr hd
      have o : (jumps.filter (fun j => ¬ j % 2 = 0)).card ≤ blocks - 2 * blocks / 3 :=
        odd r hr hd
      have splitCount := Finset.card_filter_add_card_filter_not
        (s := jumps) (fun j => j % 2 = 0)
      have total : jumps.card < blocks := by omega
      obtain ⟨q, hq, _, hqd, hqa, pr, between⟩ := next_of_sparse (by omega : 7 ≤ r) ha total
      rcases lt_trichotomy n (q + 2) with before | atq | afterq
      · have hle := between n hlo before
        have hlt := record (r + 2) (by omega) hlo
        omega
      · have : R = q := by rw [← eqR, atq, hqd]
        exact this ▸ pr
      · exact ih (n - (q + 2)) (by omega) q (by omega) hqd hqa afterq (by omega)
  exact cover (n - 663) 661 (by decide) seed.1 seed.2 (by omega) (by omega)

end OMA.R_OeisA166944_conjecture_R2
