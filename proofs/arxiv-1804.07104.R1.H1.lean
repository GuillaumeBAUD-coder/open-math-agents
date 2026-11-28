import OMAReductions.R_arxiv_1804_07104_R1
import Mathlib

namespace PrimeCircle

def offset (n s j : ℕ) := (j * s) % n

theorem offset_inj {n s j k : ℕ} (cop : n.Coprime s)
    (hj : j < n) (hk : k < n) (eqn : offset n s j = offset n s k) : j = k :=
  (Nat.ModEq.cancel_right_of_coprime cop eqn).eq_of_lt_of_lt hj hk

def entry {n : ℕ} (hn : 2 ≤ n) (s : ℕ) (i : Fin (2 * n)) : Fin (2 * n) :=
  let t := offset n s (i.val / 2)
  if i.val % 2 = 0 then ⟨2 * t, by
    have := Nat.mod_lt ((i.val / 2) * s) (by omega : 0 < n)
    dsimp [t, offset]
    omega⟩
  else ⟨2 * n - 1 - 2 * t, by omega⟩

theorem entry_val {n : ℕ} (hn : 2 ≤ n) (s : ℕ) (i : Fin (2 * n)) :
    (entry hn s i).val = if i.val % 2 = 0 then 2 * offset n s (i.val / 2)
      else 2 * n - 1 - 2 * offset n s (i.val / 2) := by
  by_cases h : i.val % 2 = 0 <;> simp [entry, h]

theorem entry_injective {n s : ℕ} (hn : 2 ≤ n) (cop : n.Coprime s) :
    Function.Injective (entry hn s) := by
  intro i j same
  have eqn := congrArg Fin.val same
  rw [entry_val, entry_val] at eqn
  have hi := i.isLt
  have hj := j.isLt
  have bound (k : ℕ) : offset n s k < n := Nat.mod_lt _ (by omega)
  have bi := bound (i.val / 2)
  have bj := bound (j.val / 2)
  apply Fin.ext
  have sameOffset : offset n s (i.val / 2) = offset n s (j.val / 2) := by
    split at eqn <;> split at eqn <;> omega
  have halves := offset_inj cop (by omega) (by omega) sameOffset
  split at eqn <;> split at eqn <;> omega

theorem next_val {n : ℕ} (hn : 2 ≤ n) (i : Fin (2 * n)) :
    (finRotate (2*n) i).val = if i.val + 1 < 2*n then i.val + 1 else 0 := by
  let : NeZero (2*n) := ⟨by omega⟩
  rw [finRotate_apply, Fin.val_add]
  have one : ((1 : Fin (2*n)) : ℕ) = 1 := Nat.mod_eq_of_lt (by omega : 1 < 2*n)
  rw [one]
  split
  · exact Nat.mod_eq_of_lt (by omega)
  · rw [show i.val + 1 = 2*n by have := i.isLt; omega, Nat.mod_self]

theorem adjacent {n s : ℕ} (hn : 2 ≤ n) (hs : s < n)
    (center : (2*n+1).Prime) (low : (2*s+1).Prime)
    (high : (2*n+2*s+1).Prime) (i : Fin (2*n)) :
    ((entry hn s i).val + 1 + ((entry hn s (finRotate (2*n) i)).val + 1)).Prime := by
  let j := finRotate (2*n) i
  change ((entry hn s i).val + 1 + ((entry hn s j).val + 1)).Prime
  rw [entry_val, entry_val]
  have hj : j.val = if i.val + 1 < 2*n then i.val+1 else 0 := next_val hn i
  have hi := i.isLt
  have bound : offset n s (i.val/2) < n := Nat.mod_lt _ (by omega)
  by_cases even : i.val % 2 = 0
  · have next : j.val = i.val + 1 := by rw [hj, if_pos (by omega)]
    rw [if_pos even, if_neg (by omega), show j.val/2 = i.val/2 by omega]
    convert center using 1
    omega
  · have evenNext : j.val % 2 = 0 := by split at hj <;> omega
    rw [if_neg even, if_pos evenNext]
    have step : offset n s (j.val/2) = (offset n s (i.val/2) + s) % n := by
      unfold offset
      rw [Nat.mod_add_mod, ← Nat.succ_mul]
      by_cases interior : i.val + 1 < 2*n
      · rw [if_pos interior] at hj
        rw [show j.val/2 = (i.val/2).succ by omega]
      · rw [if_neg interior] at hj
        rw [hj, show (i.val/2).succ = n by omega]
        simp
    rw [step]
    by_cases wrap : offset n s (i.val/2) + s < n
    · rw [Nat.mod_eq_of_lt wrap]
      convert high using 1
      omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      convert low using 1
      omega

end PrimeCircle

theorem OMA.solution : OMA.R_arxiv_1804_07104_R1.H1 := by
  intro n s hn hs cop center low high
  let a := Equiv.ofBijective (PrimeCircle.entry hn s)
    (Finite.injective_iff_bijective.mp (PrimeCircle.entry_injective hn cop))
  exact ⟨a, PrimeCircle.adjacent hn hs center low high⟩
