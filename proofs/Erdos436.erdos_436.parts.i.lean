import FormalConjectures.ErdosProblems.«436»
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
A formalization of Dietzel's combinatorial proof of Hildebrand's theorem
(arXiv:1309.7506). The Ramsey argument uses a sequence whose successive
differences are factorials, so the common divisor supplied by the
monochromatic triangle can be divided out in the natural numbers.
-/

open Filter

private def ramseyBound (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => k * ramseyBound k m + 1

private theorem pickRows {k : ℕ} (hk : 0 < k) (edge : ℕ → ℕ → Fin k)
    (m : ℕ) (s : Finset ℕ) (hs : ramseyBound k m ≤ s.card) :
    ∃ (f : Fin m → ℕ) (color : Fin m → Fin k), StrictMono f ∧
      (∀ i, f i ∈ s) ∧ ∀ i j, i < j → edge (f i) (f j) = color i := by
  classical
  induction m generalizing s with
  | zero =>
    refine ⟨Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
    all_goals intro i; exact Fin.elim0 i
  | succ m ih =>
    have hs' : k * ramseyBound k m + 1 ≤ s.card := hs
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    let a := s.min' hne
    have ha : a ∈ s := Finset.min'_mem s hne
    obtain ⟨c, _, hc⟩ :=
      Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
        (s := s.erase a) (t := (Finset.univ : Finset (Fin k)))
        (f := edge a) (fun _ _ => Finset.mem_univ _) ⟨⟨0, hk⟩, Finset.mem_univ _⟩
        (by rw [Finset.card_univ, Fintype.card_fin, Finset.card_erase_of_mem ha]; omega :
          (Finset.univ : Finset (Fin k)).card * ramseyBound k m ≤ (s.erase a).card)
    obtain ⟨f, color, hf, hfs, hcolor⟩ := ih _ hc
    have hm (i : Fin m) : f i ∈ s.erase a ∧ edge a (f i) = c :=
      Finset.mem_filter.mp (hfs i)
    have hlt (i : Fin m) : a < f i :=
      lt_of_le_of_ne (Finset.min'_le s _ (Finset.mem_erase.mp (hm i).1).2)
        (Finset.mem_erase.mp (hm i).1).1.symm
    refine ⟨Fin.cons a f, Fin.cons c color, ?_, ?_, ?_⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij
      · exact (lt_irrefl _ hij).elim
      · simpa using hlt j
      · exact (not_lt_of_ge (Fin.zero_le _) hij).elim
      · simpa using hf (Fin.succ_lt_succ_iff.mp hij)
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using ha
      · simpa using (Finset.mem_erase.mp (hm i).1).2
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij
      · exact (lt_irrefl _ hij).elim
      · simpa using (hm j).2
      · exact (not_lt_of_ge (Fin.zero_le _) hij).elim
      · simpa using hcolor i j (Fin.succ_lt_succ_iff.mp hij)

private theorem monoTriangle {k : ℕ} (hk : 0 < k) (edge : ℕ → ℕ → Fin k) :
    ∃ i j l, i < j ∧ j < l ∧ l < ramseyBound k (k + 2) ∧
      edge i j = edge i l ∧ edge i j = edge j l := by
  obtain ⟨f, color, hf, hs, hc⟩ :=
    pickRows hk edge (k + 2) (Finset.range (ramseyBound k (k + 2))) (by simp)
  obtain ⟨a, b, hne, hab⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (k + 1) => color i.castSucc) (by simp)
  suffices ∀ a b : Fin (k + 1), a < b → color a.castSucc = color b.castSucc →
      ∃ i j l, i < j ∧ j < l ∧ l < ramseyBound k (k + 2) ∧
        edge i j = edge i l ∧ edge i j = edge j l by
    rcases lt_or_gt_of_ne hne with h | h
    · exact this a b h hab
    · exact this b a h hab.symm
  intro a b hab hcolor
  have hab' : a.castSucc < b.castSucc := hab
  have hlast : b.castSucc < Fin.last (k + 1) := Fin.castSucc_lt_last _
  refine ⟨f a.castSucc, f b.castSucc, f (Fin.last (k + 1)), hf hab', hf hlast,
    Finset.mem_range.mp (hs _), ?_, ?_⟩
  · rw [hc _ _ hab', hc _ _ (hab'.trans hlast)]
  · rw [hc _ _ hab', hc _ _ hlast, hcolor]

private def factorialPositions : ℕ → ℕ
  | 0 => 0
  | n + 1 => factorialPositions n + (factorialPositions n).factorial

private theorem factorialPositions_strictMono : StrictMono factorialPositions := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact Nat.lt_add_of_pos_right (Nat.factorial_pos _)

private theorem factorialPositions_dvd {i j l : ℕ} (hij : i < j) (hjl : j ≤ l) :
    factorialPositions j - factorialPositions i ∣ factorialPositions l - factorialPositions j := by
  induction l, hjl using Nat.le_induction with
  | base => simp
  | succ l hjl ih =>
    have hs := factorialPositions_strictMono.monotone hjl
    have hpos := Nat.sub_pos_of_lt (factorialPositions_strictMono hij)
    have hle : factorialPositions j - factorialPositions i ≤ factorialPositions l := by omega
    rw [factorialPositions]
    have heq : factorialPositions l + (factorialPositions l).factorial - factorialPositions j =
        (factorialPositions l - factorialPositions j) + (factorialPositions l).factorial := by omega
    rw [heq]
    exact Nat.dvd_add ih (Nat.dvd_factorial hpos hle)

private theorem divisibleSchur {k : ℕ} (hk : 0 < k) :
    ∃ N : ℕ, ∀ color : ℕ → Fin k, ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y ≤ N ∧
      x ∣ y ∧ color x = color y ∧ color x = color (x + y) := by
  refine ⟨factorialPositions (ramseyBound k (k + 2)), ?_⟩
  intro color
  obtain ⟨i, j, l, hij, hjl, hN, h₁, h₂⟩ :=
    monoTriangle hk (fun i j => color (factorialPositions j - factorialPositions i))
  have hi := factorialPositions_strictMono hij
  have hj := factorialPositions_strictMono hjl
  have hl := factorialPositions_strictMono hN
  have hsum : factorialPositions j - factorialPositions i +
      (factorialPositions l - factorialPositions j) = factorialPositions l - factorialPositions i := by
    omega
  refine ⟨factorialPositions j - factorialPositions i, factorialPositions l - factorialPositions j,
    by omega, by omega, by omega, factorialPositions_dvd hij hjl.le, h₂, ?_⟩
  rw [hsum]
  exact h₁

private theorem findResidues {k : ℕ} (hk : 0 < k) :
    ∃ N : ℕ, ∀ p > N, p.Prime → ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧
      Erdos436.IsPowerResidue k p n ∧ Erdos436.IsPowerResidue k p (n + 1) := by
  classical
  obtain ⟨N, hN⟩ := divisibleSchur hk
  refine ⟨N, ?_⟩
  intro p hp hprime
  let : Fact p.Prime := ⟨hprime⟩
  have hnonzero (a : ℕ) (ha₀ : 0 < a) (ha : a < p) : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => (not_le_of_gt ha) (Nat.le_of_dvd ha₀ h)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  let unit (a : ℕ) : (ZMod p)ˣ :=
    if ha : (a : ZMod p) ≠ 0 then Units.mk0 _ ha else 1
  have hu (a : ℕ) (ha : (a : ZMod p) ≠ 0) : (unit a : ZMod p) = a := by simp [unit, ha]
  have hexp (a : ℕ) : ∃ e : ℤ, g ^ e = unit a := hg (unit a)
  choose e he using hexp
  let color (a : ℕ) : Fin k :=
    ⟨(e a % k).toNat, by
      have hk' : (0 : ℤ) < k := by exact_mod_cast hk
      have hmod := Int.emod_lt_of_pos (e a) hk'
      omega⟩
  have hdvd {a b : ℕ} (h : color a = color b) : (k : ℤ) ∣ e b - e a := by
    have hm : (e a % k).toNat = (e b % k).toNat := congrArg Fin.val h
    have ha := Int.emod_nonneg (e a) (by exact_mod_cast hk.ne' : (k : ℤ) ≠ 0)
    have hb := Int.emod_nonneg (e b) (by exact_mod_cast hk.ne' : (k : ℤ) ≠ 0)
    have heq : Int.ModEq (k : ℤ) (e a) (e b) := by unfold Int.ModEq; omega
    exact heq.dvd
  have hpower {a b d : ℕ} (ha : (a : ZMod p) ≠ 0) (hb : (b : ZMod p) ≠ 0)
      (hd : b = a * d) (hc : color a = color b) :
      Erdos436.IsPowerResidue k p d := by
    have hmul : (b : ZMod p) = (a : ZMod p) * (d : ZMod p) := by simpa using congrArg (fun n : ℕ => (n : ZMod p)) hd
    have hnz : (d : ZMod p) ≠ 0 := by
      intro hz
      exact hb (by rw [hmul, hz, mul_zero])
    obtain ⟨q, hq⟩ := hdvd hc
    have hpow : g ^ e b = g ^ e a * (g ^ q) ^ k := by
      have h : e b = e a + q * (k : ℤ) := by rw [mul_comm]; omega
      rw [h, zpow_add, zpow_mul, zpow_natCast]
    rw [he, he] at hpow
    have hv := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hpow
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, hu a ha, hu b hb] at hv
    have hd' := mul_left_cancel₀ ha (hmul.symm.trans hv)
    exact ⟨hnz, (g ^ q : (ZMod p)ˣ), hd'.symm⟩
  obtain ⟨x, y, hx, hy, hxy, ⟨n, hn⟩, hcolor₁, hcolor₂⟩ := hN color
  have hn₀ : 0 < n := by
    by_contra! he
    simp [Nat.eq_zero_of_le_zero he] at hn
    omega
  have hxn : n ≤ y := by
    rw [hn]
    exact Nat.le_mul_of_pos_left _ hx
  have hstep : x + y = x * (n + 1) := by rw [hn, Nat.mul_succ]; omega
  have hxp := hnonzero x hx (by omega)
  refine ⟨n, hn₀, by omega, hpower hxp (hnonzero y hy (by omega)) hn hcolor₁,
    hpower hxp (hnonzero (x + y) (by omega) (by omega)) hstep hcolor₂⟩

theorem OMA.solution : type_of% @Erdos436.erdos_436.parts.i := by
  intro k hk
  obtain ⟨N, hN⟩ := findResidues (by omega : 0 < k)
  have hevent : ∀ᶠ p in atTop ⊓ 𝓟 {p : ℕ | p.Prime}, Erdos436.r k 2 p ≤ (N : ℕ∞) := by
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_gt_atTop N] with p hp hprime
    obtain ⟨n, hn, hnN, hr₀, hr₁⟩ := hN p hp hprime
    have hrun : 1 ≤ n ∧ ∀ i < 2, Erdos436.IsPowerResidue k p (n + i) := by
      refine ⟨hn, fun i hi => ?_⟩
      have h : i = 0 ∨ i = 1 := by omega
      rcases h with rfl | rfl
      · simpa using hr₀
      · exact hr₁
    exact (iInf₂_le n hrun).trans (by exact_mod_cast hnN)
  exact lt_of_le_of_lt (Filter.limsup_le_of_le (by isBoundedDefault) hevent) (by simp)
