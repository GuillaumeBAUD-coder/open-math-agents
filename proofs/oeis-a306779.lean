import OMAStatements.S_oeis_a306779
import Mathlib

namespace A306779Disproof

open OMA.S_oeis_a306779

lemma eastCount_zero (w : ℕ → Bool) : eastCount w 0 = 0 := by
  simp [eastCount]

lemma eastCount_succ (w : ℕ → Bool) (t : ℕ) :
    eastCount w (t + 1) = eastCount w t + if w t = true then 1 else 0 := by
  unfold eastCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp
  · simp

lemma eastCount_le (w : ℕ → Bool) (t : ℕ) : eastCount w t ≤ t := by
  unfold eastCount
  calc _ ≤ (Finset.range t).card := Finset.card_filter_le _ _
    _ = t := Finset.card_range t

lemma pos_zero (n k : ℕ) (w : ℕ → Bool) : pos n k w 0 = (0, 0) := by
  simp [pos, eastCount_zero]

lemma step_true {n k : ℕ} {w : ℕ → Bool} {t : ℕ} (h : w t = true) :
    pos n k w (t + 1) = (((pos n k w t).1 + 1) % n, (pos n k w t).2) := by
  have hle := eastCount_le w t
  simp only [pos, eastCount_succ, h, if_true, Nat.mod_add_mod]
  congr 2
  omega

lemma step_false {n k : ℕ} {w : ℕ → Bool} {t : ℕ} (h : w t = false) :
    pos n k w (t + 1) = ((pos n k w t).1, ((pos n k w t).2 + 1) % k) := by
  have hle := eastCount_le w t
  simp only [pos, eastCount_succ, h, Bool.false_eq_true, if_false, add_zero, Nat.mod_add_mod]
  congr 2
  omega

lemma surj {n k : ℕ} {w : ℕ → Bool} (hinj : Set.InjOn (pos n k w) (Set.Iio (n * k)))
    (hn : 0 < n) (hk : 0 < k) (x y : ℕ) (hx : x < n) (hy : y < k) :
    ∃ s, s < n * k ∧ pos n k w s = (x, y) := by
  have hsub : (Finset.range (n * k)).image (pos n k w) ⊆ Finset.range n ×ˢ Finset.range k := by
    intro p hp
    simp only [Finset.mem_image, Finset.mem_range] at hp
    obtain ⟨i, -, rfl⟩ := hp
    simp only [Finset.mem_product, Finset.mem_range, pos]
    exact ⟨Nat.mod_lt _ hn, Nat.mod_lt _ hk⟩
  have hcard : ((Finset.range (n * k)).image (pos n k w)).card =
      (Finset.range n ×ˢ Finset.range k).card := by
    rw [Finset.card_image_of_injOn, Finset.card_range, Finset.card_product, Finset.card_range,
      Finset.card_range]
    intro a ha b hb hab
    exact hinj (Set.mem_Iio.mpr (by simpa using ha)) (Set.mem_Iio.mpr (by simpa using hb)) hab
  have heq := Finset.eq_of_subset_of_card_le hsub hcard.ge
  have hmem : (x, y) ∈ (Finset.range (n * k)).image (pos n k w) := by
    rw [heq]
    simp [hx, hy]
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨s, hs, h⟩ := hmem
  exact ⟨s, hs, h⟩

lemma anti {n k : ℕ} {w : ℕ → Bool} (hN : pos n k w (n * k) = (0, 0))
    (hinj : Set.InjOn (pos n k w) (Set.Iio (n * k))) {t s : ℕ} (ht : t < n * k)
    (hs : s < n * k) (hwt : w t = true)
    (h1 : (pos n k w s).1 = ((pos n k w t).1 + 1) % n)
    (h2 : ((pos n k w s).2 + 1) % k = (pos n k w t).2) : w s = true := by
  by_contra hws
  have hws' : w s = false := by simpa using hws
  have hst : s ≠ t := by
    rintro rfl
    rw [hwt] at hws'
    exact absurd hws' (by decide)
  have heq : pos n k w (s + 1) = pos n k w (t + 1) := by
    rw [step_false hws', step_true hwt, h1, h2]
  have h0 := pos_zero n k w
  rcases Nat.lt_or_ge (s + 1) (n * k) with hs1 | hs1 <;>
    rcases Nat.lt_or_ge (t + 1) (n * k) with ht1 | ht1
  · have := hinj (Set.mem_Iio.mpr hs1) (Set.mem_Iio.mpr ht1) heq
    omega
  · have e : t + 1 = n * k := by omega
    rw [e, hN, ← h0] at heq
    have := hinj (Set.mem_Iio.mpr hs1) (Set.mem_Iio.mpr (show 0 < n * k by omega)) heq
    omega
  · have e : s + 1 = n * k := by omega
    rw [e, hN, ← h0] at heq
    have := hinj (Set.mem_Iio.mpr (show 0 < n * k by omega)) (Set.mem_Iio.mpr ht1) heq
    omega
  · omega

lemma shift {n k : ℕ} {w : ℕ → Bool} (hN : pos n k w (n * k) = (0, 0))
    (hinj : Set.InjOn (pos n k w) (Set.Iio (n * k))) (hn : 0 < n) (hk : 0 < k) :
    ∀ j t s : ℕ, t < n * k → s < n * k → w t = true →
      (pos n k w s).1 = ((pos n k w t).1 + j) % n →
      ((pos n k w s).2 + j) % k = (pos n k w t).2 → w s = true
  | 0, t, s, ht, hs, hwt, h1, h2 => by
    have hp : pos n k w s = pos n k w t := by
      rw [Prod.ext_iff]
      constructor
      · rw [h1, add_zero]
        simp [pos]
      · rw [← h2, add_zero]
        simp [pos]
    have := hinj (Set.mem_Iio.mpr hs) (Set.mem_Iio.mpr ht) hp
    subst this
    exact hwt
  | j + 1, t, s, ht, hs, hwt, h1, h2 => by
    obtain ⟨u, hu, hpu⟩ := surj hinj hn hk (((pos n k w t).1 + j) % n)
      (((pos n k w s).2 + 1) % k) (Nat.mod_lt _ hn) (Nat.mod_lt _ hk)
    have hwu : w u = true := by
      refine shift hN hinj hn hk j t u ht hu hwt (by rw [hpu]) ?_
      rw [hpu, ← h2]
      simp only [Nat.mod_add_mod]
      congr 1
      ring
    refine anti hN hinj hu hs hwu ?_ (by rw [hpu])
    rw [h1, hpu]
    simp only [Nat.mod_add_mod]
    congr 1

lemma cls {n k : ℕ} {w : ℕ → Bool} (hN : pos n k w (n * k) = (0, 0))
    (hinj : Set.InjOn (pos n k w) (Set.Iio (n * k))) (hn : 0 < n) (hk : 0 < k) {t s : ℕ}
    (ht : t < n * k) (hs : s < n * k) (hts : t % Nat.gcd n k = s % Nat.gcd n k)
    (hwt : w t = true) : w s = true := by
  have hEt := eastCount_le w t
  have hEs := eastCount_le w s
  have hab : eastCount w s + (n - 1) * eastCount w t ≡
      (t - eastCount w t) + (k - 1) * (s - eastCount w s) [MOD Nat.gcd n k] := by
    rw [Nat.modEq_iff_dvd]
    have hts' : (Nat.gcd n k : ℤ) ∣ (s : ℤ) - t := Nat.modEq_iff_dvd.mp hts
    obtain ⟨p, hp⟩ := Nat.gcd_dvd_left n k
    obtain ⟨q, hq⟩ := Nat.gcd_dvd_right n k
    obtain ⟨r, hr⟩ := hts'
    have hp' : (n : ℤ) = (Nat.gcd n k : ℤ) * p := by exact_mod_cast hp
    have hq' : (k : ℤ) = (Nat.gcd n k : ℤ) * q := by exact_mod_cast hq
    refine ⟨-r + q * ((s : ℤ) - eastCount w s) - p * eastCount w t, ?_⟩
    push_cast [Nat.cast_sub hEt, Nat.cast_sub hEs, Nat.cast_sub (show 1 ≤ n by omega),
      Nat.cast_sub (show 1 ≤ k by omega)]
    linear_combination ((s : ℤ) - eastCount w s) * hq' - (eastCount w t : ℤ) * hp' - hr
  obtain ⟨j, hj1, hj2⟩ := Nat.chineseRemainder' hab
  refine shift hN hinj hn hk j t s ht hs hwt ?_ ?_
  · show eastCount w s % n = (eastCount w t % n + j) % n
    rw [Nat.mod_add_mod]
    have e1 : eastCount w t + j ≡ eastCount w t + (eastCount w s + (n - 1) * eastCount w t)
        [MOD n] := Nat.ModEq.add_left _ hj1
    have e2 : eastCount w t + (eastCount w s + (n - 1) * eastCount w t) =
        eastCount w s + n * eastCount w t := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [e2] at e1
    rw [e1, Nat.add_mul_mod_self_left]
  · show ((s - eastCount w s) % k + j) % k = (t - eastCount w t) % k
    rw [Nat.mod_add_mod]
    have e1 : (s - eastCount w s) + j ≡ (s - eastCount w s) +
        ((t - eastCount w t) + (k - 1) * (s - eastCount w s)) [MOD k] := Nat.ModEq.add_left _ hj2
    have e2 : (s - eastCount w s) + ((t - eastCount w t) + (k - 1) * (s - eastCount w s)) =
        (t - eastCount w t) + k * (s - eastCount w s) := by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [e2] at e1
    rw [e1, Nat.add_mul_mod_self_left]

lemma per {n k : ℕ} {w : ℕ → Bool} (hN : pos n k w (n * k) = (0, 0))
    (hinj : Set.InjOn (pos n k w) (Set.Iio (n * k))) (hn : 0 < n) (hk : 0 < k) {u i : ℕ}
    (hu : Nat.gcd n k ∣ u) (hui : u + i < n * k) : w (u + i) = w i := by
  have hmod : (u + i) % Nat.gcd n k = i % Nat.gcd n k := by
    obtain ⟨c, rfl⟩ := hu
    simp [Nat.add_mod]
  cases h : w i
  · by_contra hc
    have hc' : w (u + i) = true := by simpa using hc
    have := cls hN hinj hn hk hui (by omega) hmod hc'
    rw [h] at this
    exact absurd this (by decide)
  · exact cls hN hinj hn hk (by omega) hui hmod.symm h

lemma east_add {n k : ℕ} {w : ℕ → Bool} (hN : pos n k w (n * k) = (0, 0))
    (hinj : Set.InjOn (pos n k w) (Set.Iio (n * k))) (hn : 0 < n) (hk : 0 < k) {u : ℕ}
    (hu : Nat.gcd n k ∣ u) : ∀ i, u + i ≤ n * k → eastCount w (u + i) = eastCount w u + eastCount w i
  | 0, _ => by simp [eastCount_zero]
  | i + 1, hi => by
    rw [← add_assoc, eastCount_succ, eastCount_succ, east_add hN hinj hn hk hu i (by omega),
      per hN hinj hn hk hu (by omega)]
    ring

lemma east_mul {n k : ℕ} {w : ℕ → Bool} (hN : pos n k w (n * k) = (0, 0))
    (hinj : Set.InjOn (pos n k w) (Set.Iio (n * k))) (hn : 0 < n) (hk : 0 < k) :
    ∀ m, Nat.gcd n k * m ≤ n * k →
      eastCount w (Nat.gcd n k * m) = m * eastCount w (Nat.gcd n k)
  | 0, _ => by simp [eastCount_zero]
  | m + 1, hm => by
    rw [Nat.mul_succ, east_add hN hinj hn hk (Dvd.intro m rfl) _ (by rw [← Nat.mul_succ]; exact hm),
      east_mul hN hinj hn hk m (by nlinarith)]
    ring

theorem noLoop : ¬ HasFullLoop 4368 880 := by
  rintro ⟨w, hN, hinj⟩
  have hg : Nat.gcd 4368 880 = 16 := by norm_num
  have he := eastCount_le w 16
  have key : ∀ m, 16 * m ≤ 4368 * 880 → eastCount w (16 * m) = m * eastCount w 16 := by
    have := east_mul hN hinj (by norm_num) (by norm_num)
    rwa [hg] at this
  have contra : ∀ m, 0 < m → 16 * m < 4368 * 880 → (m * eastCount w 16) % 4368 = 0 →
      (m * (16 - eastCount w 16)) % 880 = 0 → False := by
    intro m hm hlt h1 h2
    have hp : pos 4368 880 w (16 * m) = pos 4368 880 w 0 := by
      rw [pos_zero]
      simp only [pos, key m hlt.le]
      rw [h1, show 16 * m - m * eastCount w 16 = m * (16 - eastCount w 16) by
        rw [Nat.mul_sub]; ring_nf, h2]
    have := hinj (Set.mem_Iio.mpr hlt) (Set.mem_Iio.mpr (by norm_num)) hp
    omega
  clear key
  generalize eastCount w 16 = e at he contra
  interval_cases e
  · exact contra 55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact contra 48048 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact contra 120120 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact contra 80080 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact contra 60060 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact contra 21840 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact contra 8008 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact contra 34320 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact contra 30030 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact contra 80080 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact contra 120120 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact contra 48048 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact contra 20020 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact contra 18480 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact contra 17160 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact contra 80080 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact contra 273 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end A306779Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a306779.main) := by
  intro h
  exact A306779Disproof.noLoop ((h 4368 880 (by norm_num) (by norm_num)).mpr (Or.inr (by norm_num)))
