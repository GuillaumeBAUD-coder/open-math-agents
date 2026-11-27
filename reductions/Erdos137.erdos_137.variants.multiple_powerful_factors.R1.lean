import FormalConjectures.ErdosProblems.«137»

/-! Credit: @FelixDou.
Use the last b terms, where b is the smaller of the interval length and half
its upper endpoint, rounded down. A prime above b has at most one multiple
anywhere in the original interval. Disjoint short blocks therefore give
distinct primes of the required multiplicity. -/

namespace OMA.R_Erdos137_erdos_137_variants_multiple_powerful_factors_R1

/-- Below the square threshold only a large prime divisor is needed.
Theorem 1 of P. Erdős, On consecutive integers (1955), guarantees such a divisor
in a block of length at most C b / log b starting above b. For each fixed a,
this length is eventually at most the requested floor of b/a. -/
def H1 : Prop :=
  ∀ a : ℕ, 0 < a → ∀ᶠ b in Filter.atTop, ∀ t : ℕ, b ≤ t → t + b / a ≤ b ^ 2 →
    ∃ x p : ℕ, t < x ∧ x ≤ t + b / a ∧ b < p ∧ p.Prime ∧ p ∣ x

/-- Above the square threshold, find a single term with a large prime factor
of multiplicity one in an interval of length a fixed fraction of b.
Under abc, Theorem 1' of A. Granville, On the scarcity of powerful binomial
coefficients (1999), gives this for the binomial coefficient with top t + b/a
and bottom b/a. The logarithm of the product of primes at most b is O(b),
whereas Granville's lower bound has logarithm at least a constant times
(b/a) log b for each fixed positive a and all sufficiently large b. -/
def H2 : Prop :=
  ∀ a : ℕ, 0 < a → ∀ᶠ b in Filter.atTop, ∀ t : ℕ, b ≤ t → b ^ 2 < t + b / a →
    ∃ x p : ℕ, t < x ∧ x ≤ t + b / a ∧ b < p ∧ p.Prime ∧ p ∣ x ∧ ¬ p ^ 2 ∣ x

lemma unique_multiple {m n p x y : ℕ} (hsize : n ≤ p ∨ m + n < 2 * p)
    (hx : x ∈ Finset.Ioc m (m + n)) (hy : y ∈ Finset.Ioc m (m + n))
    (hpx : p ∣ x) (hpy : p ∣ y) : x = y := by
  have impossible (u v : ℕ) (hu : m < u) (hv : v ≤ m + n) (huv : u < v)
      (hpu : p ∣ u) (hpv : p ∣ v) : False := by
    have hgap := Nat.le_of_dvd (Nat.sub_pos_of_lt huv) (Nat.dvd_sub hpv hpu)
    have hlo := Nat.le_of_dvd (by omega : 0 < u) hpu
    omega
  obtain ⟨hxl, hxr⟩ := Finset.mem_Ioc.mp hx
  obtain ⟨hyl, hyr⟩ := Finset.mem_Ioc.mp hy
  rcases lt_trichotomy x y with h | h | h
  · exact (impossible x y hxl hyr h hpx hpy).elim
  · exact h
  · exact (impossible y x hyl hxr h hpy hpx).elim

lemma transfer_factor {m n p x : ℕ} (hsize : n ≤ p ∨ m + n < 2 * p)
    (hx : x ∈ Finset.Ioc m (m + n)) (hp : p.Prime) (hd : p ∣ x) (hsq : ¬ p ^ 2 ∣ x) :
    p ∣ (∏ y ∈ Finset.Ioc m (m + n), y) ∧ ¬ p ^ 2 ∣ (∏ y ∈ Finset.Ioc m (m + n), y) := by
  let s := Finset.Ioc m (m + n)
  have hrest : ¬ p ∣ ∏ y ∈ s.erase x, y := by
    intro h
    obtain ⟨y, hy, hpy⟩ := (hp.prime.dvd_finsetProd_iff (fun z : ℕ => z)).mp h
    obtain ⟨hne, hym⟩ := Finset.mem_erase.mp hy
    exact hne (unique_multiple hsize hym hx hpy hd)
  have hcop := (hp.coprime_iff_not_dvd.mpr hrest).pow_left 2
  change p ∣ (∏ y ∈ s, y) ∧ ¬ p ^ 2 ∣ (∏ y ∈ s, y)
  rw [← Finset.mul_prod_erase s (fun y : ℕ => y) hx]
  exact ⟨dvd_mul_of_dvd_left hd _, fun h => hsq (hcop.dvd_of_dvd_mul_right h)⟩

theorem main : H1 → H2 → type_of% @Erdos137.erdos_137.variants.multiple_powerful_factors := by
  classical
  intro hsmall hlarge k
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1
    ((hsmall (k + 1) (by omega)).and (hlarge (k + 1) (by omega)))
  apply Filter.eventually_atTop.2
  refine ⟨2 * B, ?_⟩
  intro n hn m hm
  let b := min n ((m + n) / 2)
  let s := m + n - b
  let w := b / (k + 1)
  have hbn : b ≤ n := min_le_left _ _
  have hbh : b ≤ (m + n) / 2 := min_le_right _ _
  have hBb : B ≤ b := le_min (by omega) (by omega)
  have hsb : b ≤ s := by dsimp [s]; omega
  have hsm : m ≤ s := by dsimp [s]; omega
  have htop : s + b = m + n := by dsimp [s]; omega
  obtain ⟨hs, hl⟩ := hB b hBb
  have hblock (t : ℕ) (ht : b ≤ t) :
      ∃ x p : ℕ, t < x ∧ x ≤ t + w ∧ b < p ∧ p.Prime ∧ p ∣ x ∧ ¬ p ^ 2 ∣ x := by
    by_cases h : t + w ≤ b ^ 2
    · obtain ⟨x, p, hx, hx', hbp, hp, hd⟩ := hs t ht h
      refine ⟨x, p, hx, hx', hbp, hp, hd, ?_⟩
      intro hsq
      have hle := Nat.le_of_dvd (by omega : 0 < x) hsq
      have hlt : b ^ 2 < p ^ 2 := Nat.pow_lt_pow_left hbp (by decide)
      omega
    · exact hl t ht (by omega)
  have hpack : k * w ≤ b := calc
    k * w ≤ (k + 1) * w := Nat.mul_le_mul_right w (by omega)
    _ ≤ b := by simpa [w, Nat.mul_comm] using Nat.div_mul_le_self b (k + 1)
  have hblocks (i : Fin k) := hblock (s + i.val * w) (by omega)
  choose x p hleft hright hbig hprime hd hsq using hblocks
  have hmem (i : Fin k) : x i ∈ Finset.Ioc m (m + n) := by
    have hstop := Nat.mul_le_mul_right w (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at hstop
    exact Finset.mem_Ioc.mpr ⟨by have := hleft i; omega, by have := hright i; omega⟩
  have hsize (i : Fin k) : n ≤ p i ∨ m + n < 2 * p i := by
    have hi := hbig i
    by_cases h : n ≤ (m + n) / 2
    · rw [show b = n from min_eq_left h] at hi
      exact Or.inl (by omega)
    · rw [show b = (m + n) / 2 from min_eq_right (by omega)] at hi
      exact Or.inr (by omega)
  have hmono : StrictMono x := by
    intro i j hij
    have hstep := Nat.mul_le_mul_right w (Nat.succ_le_of_lt (show i.val < j.val from hij))
    rw [Nat.succ_mul] at hstep
    have hi := hright i
    have hj := hleft j
    omega
  have hinj : Function.Injective p := by
    intro i j heq
    exact hmono.injective (unique_multiple (hsize i) (hmem i) (hmem j) (hd i) (heq ▸ hd j))
  refine ⟨Finset.univ.image p, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨hprime i, transfer_factor (hsize i) (hmem i) (hprime i) (hd i) (hsq i)⟩

end OMA.R_Erdos137_erdos_137_variants_multiple_powerful_factors_R1
