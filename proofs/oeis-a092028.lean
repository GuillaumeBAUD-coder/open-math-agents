import OMAStatements.S_oeis_a092028
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.Finite.Basic

/-! OEIS A092028: for `n ≥ 3`, the least `m > 1` with `m ∣ n ^ m - 1` is the least prime factor
`p` of `n - 1`.

`p` works: `p ∣ n - 1 ∣ n ^ p - 1`. Conversely, let `m > 1` with `m ∣ n ^ m - 1` and let `q` be
the least prime factor of `m`. Then `q ∤ n`, so `q ∣ n ^ (q - 1) - 1` (Fermat), and `m` is coprime
to `q - 1` (every prime factor of `m` is at least `q`). Hence
`q ∣ gcd (n ^ m - 1) (n ^ (q - 1) - 1) = n ^ gcd m (q - 1) - 1 = n - 1`, so `p ≤ q ≤ m`. -/

namespace OpenMath.A092028

open OMA.S_oeis_a092028

/-- If a prime `q` divides `n ^ m - 1` with `m ≥ 1` coprime to `q - 1`, then `q ∣ n - 1`. -/
private theorem key (n m q : ℕ) (hq : q.Prime) (hn : 0 < n) (hm : 1 ≤ m)
    (hdvd : q ∣ n ^ m - 1) (hcop : Nat.Coprime m (q - 1)) : q ∣ n - 1 := by
  have hpow : 1 ≤ n ^ m := Nat.one_le_pow _ _ hn
  have hqn : ¬q ∣ n := by
    intro h
    have h1 : q ∣ n ^ m := h.trans (dvd_pow_self n (by omega))
    have h2 : q ∣ n ^ m - (n ^ m - 1) := Nat.dvd_sub h1 hdvd
    rw [show n ^ m - (n ^ m - 1) = 1 by omega] at h2
    exact hq.one_lt.ne' (Nat.dvd_one.1 h2)
  have hcopn : Nat.Coprime n q :=
    Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hq).2 hqn)
  have hferm : n ^ (q - 1) ≡ 1 [MOD q] := by
    have h := Nat.ModEq.pow_totient hcopn
    rwa [Nat.totient_prime hq] at h
  have hferm' : q ∣ n ^ (q - 1) - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hn)).1 hferm.symm
  have h := Nat.dvd_gcd hdvd hferm'
  rwa [Nat.pow_sub_one_gcd_pow_sub_one, Nat.Coprime.gcd_eq_one hcop, pow_one] at h

/-- `m` is coprime to `minFac m - 1`. -/
private theorem coprime_minFac_sub_one (m : ℕ) (hm : 1 < m) :
    Nat.Coprime m (m.minFac - 1) := by
  have hq := Nat.minFac_prime (show m ≠ 1 by omega)
  have hq2 := hq.two_le
  by_contra h
  have hg1 : Nat.gcd m (m.minFac - 1) ≠ 1 := h
  have hr := Nat.minFac_prime hg1
  have hrm : (Nat.gcd m (m.minFac - 1)).minFac ∣ m :=
    (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
  have hrq : (Nat.gcd m (m.minFac - 1)).minFac ∣ m.minFac - 1 :=
    (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
  have h1 := Nat.minFac_le_of_dvd hr.two_le hrm
  have h2 := Nat.le_of_dvd (by omega) hrq
  omega

theorem main : ∀ n : ℕ, 3 ≤ n → (a n).Prime ∧ a n = (n - 1).minFac := by
  intro n hn
  have hp : (n - 1).minFac.Prime := Nat.minFac_prime (by omega)
  have hmem : (n - 1).minFac ∈ {m : ℕ | 1 < m ∧ m ∣ n ^ m - 1} :=
    ⟨hp.one_lt, (Nat.minFac_dvd _).trans (Nat.sub_one_dvd_pow_sub_one n _)⟩
  have hlow : ∀ m ∈ {m : ℕ | 1 < m ∧ m ∣ n ^ m - 1}, (n - 1).minFac ≤ m := by
    rintro m ⟨hm1, hmd⟩
    have hq := Nat.minFac_prime (show m ≠ 1 by omega)
    have hqd : m.minFac ∣ n - 1 :=
      key n m m.minFac hq (by omega) (by omega) ((Nat.minFac_dvd m).trans hmd)
        (coprime_minFac_sub_one m hm1)
    exact (Nat.minFac_le_of_dvd hq.two_le hqd).trans (Nat.minFac_le (by omega))
  have ha : a n = (n - 1).minFac :=
    le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ hlow)
  exact ⟨by rw [ha]; exact hp, ha⟩

end OpenMath.A092028

theorem OMA.solution : type_of% @OMA.S_oeis_a092028.main := OpenMath.A092028.main
