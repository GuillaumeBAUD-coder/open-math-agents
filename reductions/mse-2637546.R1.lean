import OMAStatements.S_mse_2637546
import Mathlib

/-! Initial lengths and the induction for paired square-sum paths. -/

namespace OMA.R_mse_2637546_R1

private theorem path_from {n : Nat} (xs : List Nat)
    (perm : xs.Perm ((List.range n).map Nat.succ))
    (chain : xs.IsChain fun a b => IsSquare (a + b)) :
    ∃ p : Equiv.Perm (Fin n), ∀ i j : Fin n, j.val = i.val + 1 →
      IsSquare ((p i).val + 1 + ((p j).val + 1)) := by
  have len : xs.length = n := by simpa using perm.length_eq
  have dist : xs.Nodup := perm.nodup_iff.mpr (List.nodup_range.map Nat.succ_injective)
  have bounds (x : Nat) (hx : x ∈ xs) : 0 < x ∧ x ≤ n := by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (perm.mem_iff.mp hx)
    have hj' := List.mem_range.mp hj
    omega
  let ix (i : Fin n) : Fin xs.length := ⟨i.val, len.symm ▸ i.isLt⟩
  have in_list (i : Fin n) : xs.get (ix i) ∈ xs := List.get_mem xs (ix i)
  let f (i : Fin n) : Fin n :=
    ⟨xs.get (ix i) - 1, by have h := bounds _ (in_list i); omega⟩
  have get (i : Fin n) : (f i).val + 1 = xs.get (ix i) := by
    have := (bounds _ (in_list i)).1
    change xs.get (ix i) - 1 + 1 = xs.get (ix i)
    omega
  have inj : Function.Injective f := by
    intro i j h
    have h' : xs.get (ix i) = xs.get (ix j) := by
      rw [← get i, ← get j, h]
    exact Fin.ext (congrArg (fun k : Fin xs.length => k.val) (dist.injective_get h'))
  let p := Equiv.ofBijective f ⟨inj, Finite.surjective_of_injective inj⟩
  refine ⟨p, ?_⟩
  intro i j next
  change IsSquare ((f i).val + 1 + ((f j).val + 1))
  rw [get i, get j]
  have hj : i.val + 1 < xs.length := by rw [len, ← next]; exact j.isLt
  have adjacent := List.isChain_iff_getElem.mp chain i.val hj
  simpa only [ix, List.get_eq_getElem, next] using adjacent

def H1 : Prop :=
  ∀ n : Nat, 25 ≤ n → n < 99 →
    ∃ p : Equiv.Perm (Fin n), ∀ i j : Fin n, j.val = i.val + 1 →
      IsSquare ((p i).val + 1 + ((p j).val + 1))

def H2 : Prop :=
  let paired := fun n : Nat => ∃ s t : List Nat,
    s.Perm ((List.range n).map Nat.succ) ∧
    t.Perm ((List.range (n + 1)).map Nat.succ) ∧
    s.IsChain (fun a b => IsSquare (a + b)) ∧
    t.IsChain (fun a b => IsSquare (a + b)) ∧
    s.head? = some 1 ∧ t.head? = some 1 ∧
    s.getLast? = some (if n % 2 = 0 then 8 else 3) ∧
    t.getLast? = some (if n % 2 = 0 then 3 else 8) ∧
    ∀ x ∈ s, s.idxOf x % 2 = t.idxOf x % 2
  ∀ n : Nat, 99 ≤ n → n < 4875 → paired n

def H3 : Prop :=
  let paired := fun n : Nat => ∃ s t : List Nat,
    s.Perm ((List.range n).map Nat.succ) ∧
    t.Perm ((List.range (n + 1)).map Nat.succ) ∧
    s.IsChain (fun a b => IsSquare (a + b)) ∧
    t.IsChain (fun a b => IsSquare (a + b)) ∧
    s.head? = some 1 ∧ t.head? = some 1 ∧
    s.getLast? = some (if n % 2 = 0 then 8 else 3) ∧
    t.getLast? = some (if n % 2 = 0 then 3 else 8) ∧
    ∀ x ∈ s, s.idxOf x % 2 = t.idxOf x % 2
  ∀ n : Nat, 99 ≤ n → paired n →
    ∀ k : Nat, 24 ≤ k → k ≤ 72 → paired (49 * n + k)

theorem main : H1 → H2 → H3 → type_of% @OMA.S_mse_2637546.main := by
  intro small basis step n hn
  by_cases hs : n < 99
  · exact small n hn hs
  · let paired := fun n : Nat => ∃ s t : List Nat,
      s.Perm ((List.range n).map Nat.succ) ∧
      t.Perm ((List.range (n + 1)).map Nat.succ) ∧
      s.IsChain (fun a b => IsSquare (a + b)) ∧
      t.IsChain (fun a b => IsSquare (a + b)) ∧
      s.head? = some 1 ∧ t.head? = some 1 ∧
      s.getLast? = some (if n % 2 = 0 then 8 else 3) ∧
      t.getLast? = some (if n % 2 = 0 then 3 else 8) ∧
      ∀ x ∈ s, s.idxOf x % 2 = t.idxOf x % 2
    have all_pairs : ∀ m : Nat, 99 ≤ m → paired m := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro hm
        by_cases hbase : m < 4875
        · exact basis m hm hbase
        · let j := (m - 24) / 49
          let k := (m - 24) % 49 + 24
          have gj : 99 ≤ j := by dsimp [j]; omega
          have lj : j < m := by dsimp [j]; omega
          have lo : 24 ≤ k := by dsimp [k]; omega
          have hi : k ≤ 72 := by dsimp [k]; omega
          have decomp : 49 * j + k = m := by dsimp [j, k]; omega
          have next : paired (49 * j + k) := step j gj (ih j lj gj) k lo hi
          rwa [decomp] at next
    obtain ⟨s, t, hs, ht, hchain, _⟩ := all_pairs n (by omega)
    exact path_from s hs hchain

end OMA.R_mse_2637546_R1