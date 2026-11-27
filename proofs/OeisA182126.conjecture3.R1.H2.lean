import OMAReductions.R_OeisA182126_conjecture3_R1

-- Step OeisA182126.conjecture3.R1.H2: hypothesis H2 of reduction OeisA182126.conjecture3.R1
-- Credit: @iskan-ai

/-! The finite part: the first 63 primes are tabulated through `Nat.nth_count`, after which each
of the 61 residues `prime n * prime (n+1) % prime (n+2)` is computed and its primality decided. -/

namespace OMA.A182126H2

theorem nth_of_count {q k : ℕ} (hq : q.Prime) (hc : Nat.count Nat.Prime q = k) :
    Nat.nth Nat.Prime k = q := hc ▸ Nat.nth_count hq

set_option maxHeartbeats 4000000 in
theorem t0 : Nat.nth Nat.Prime 0 = 2 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t1 : Nat.nth Nat.Prime 1 = 3 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t2 : Nat.nth Nat.Prime 2 = 5 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t3 : Nat.nth Nat.Prime 3 = 7 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t4 : Nat.nth Nat.Prime 4 = 11 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t5 : Nat.nth Nat.Prime 5 = 13 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t6 : Nat.nth Nat.Prime 6 = 17 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t7 : Nat.nth Nat.Prime 7 = 19 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t8 : Nat.nth Nat.Prime 8 = 23 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t9 : Nat.nth Nat.Prime 9 = 29 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t10 : Nat.nth Nat.Prime 10 = 31 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t11 : Nat.nth Nat.Prime 11 = 37 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t12 : Nat.nth Nat.Prime 12 = 41 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t13 : Nat.nth Nat.Prime 13 = 43 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t14 : Nat.nth Nat.Prime 14 = 47 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t15 : Nat.nth Nat.Prime 15 = 53 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t16 : Nat.nth Nat.Prime 16 = 59 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t17 : Nat.nth Nat.Prime 17 = 61 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t18 : Nat.nth Nat.Prime 18 = 67 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t19 : Nat.nth Nat.Prime 19 = 71 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t20 : Nat.nth Nat.Prime 20 = 73 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t21 : Nat.nth Nat.Prime 21 = 79 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t22 : Nat.nth Nat.Prime 22 = 83 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t23 : Nat.nth Nat.Prime 23 = 89 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t24 : Nat.nth Nat.Prime 24 = 97 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t25 : Nat.nth Nat.Prime 25 = 101 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t26 : Nat.nth Nat.Prime 26 = 103 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t27 : Nat.nth Nat.Prime 27 = 107 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t28 : Nat.nth Nat.Prime 28 = 109 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t29 : Nat.nth Nat.Prime 29 = 113 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t30 : Nat.nth Nat.Prime 30 = 127 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t31 : Nat.nth Nat.Prime 31 = 131 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t32 : Nat.nth Nat.Prime 32 = 137 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t33 : Nat.nth Nat.Prime 33 = 139 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t34 : Nat.nth Nat.Prime 34 = 149 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t35 : Nat.nth Nat.Prime 35 = 151 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t36 : Nat.nth Nat.Prime 36 = 157 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t37 : Nat.nth Nat.Prime 37 = 163 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t38 : Nat.nth Nat.Prime 38 = 167 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t39 : Nat.nth Nat.Prime 39 = 173 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t40 : Nat.nth Nat.Prime 40 = 179 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t41 : Nat.nth Nat.Prime 41 = 181 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t42 : Nat.nth Nat.Prime 42 = 191 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t43 : Nat.nth Nat.Prime 43 = 193 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t44 : Nat.nth Nat.Prime 44 = 197 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t45 : Nat.nth Nat.Prime 45 = 199 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t46 : Nat.nth Nat.Prime 46 = 211 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t47 : Nat.nth Nat.Prime 47 = 223 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t48 : Nat.nth Nat.Prime 48 = 227 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t49 : Nat.nth Nat.Prime 49 = 229 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t50 : Nat.nth Nat.Prime 50 = 233 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t51 : Nat.nth Nat.Prime 51 = 239 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t52 : Nat.nth Nat.Prime 52 = 241 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t53 : Nat.nth Nat.Prime 53 = 251 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t54 : Nat.nth Nat.Prime 54 = 257 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t55 : Nat.nth Nat.Prime 55 = 263 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t56 : Nat.nth Nat.Prime 56 = 269 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t57 : Nat.nth Nat.Prime 57 = 271 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t58 : Nat.nth Nat.Prime 58 = 277 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t59 : Nat.nth Nat.Prime 59 = 281 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t60 : Nat.nth Nat.Prime 60 = 283 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t61 : Nat.nth Nat.Prime 61 = 293 := nth_of_count (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
theorem t62 : Nat.nth Nat.Prime 62 = 307 := nth_of_count (by norm_num) (by decide +kernel)

theorem a1 : OeisA182126.a 1 = 1 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t0, t1, t2]

theorem a2 : OeisA182126.a 2 = 1 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t1, t2, t3]

theorem a3 : OeisA182126.a 3 = 2 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t2, t3, t4]

theorem a4 : OeisA182126.a 4 = 12 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t3, t4, t5]

theorem a5 : OeisA182126.a 5 = 7 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t4, t5, t6]

theorem a6 : OeisA182126.a 6 = 12 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t5, t6, t7]

theorem a7 : OeisA182126.a 7 = 1 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t6, t7, t8]

theorem a8 : OeisA182126.a 8 = 2 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t7, t8, t9]

theorem a9 : OeisA182126.a 9 = 16 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t8, t9, t10]

theorem a10 : OeisA182126.a 10 = 11 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t9, t10, t11]

theorem a11 : OeisA182126.a 11 = 40 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t10, t11, t12]

theorem a12 : OeisA182126.a 12 = 12 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t11, t12, t13]

theorem a13 : OeisA182126.a 13 = 24 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t12, t13, t14]

theorem a14 : OeisA182126.a 14 = 7 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t13, t14, t15]

theorem a15 : OeisA182126.a 15 = 13 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t14, t15, t16]

theorem a16 : OeisA182126.a 16 = 16 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t15, t16, t17]

theorem a17 : OeisA182126.a 17 = 48 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t16, t17, t18]

theorem a18 : OeisA182126.a 18 = 40 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t17, t18, t19]

theorem a19 : OeisA182126.a 19 = 12 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t18, t19, t20]

theorem a20 : OeisA182126.a 20 = 48 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t19, t20, t21]

theorem a21 : OeisA182126.a 21 = 40 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t20, t21, t22]

theorem a22 : OeisA182126.a 22 = 60 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t21, t22, t23]

theorem a23 : OeisA182126.a 23 = 15 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t22, t23, t24]

theorem a24 : OeisA182126.a 24 = 48 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t23, t24, t25]

theorem a25 : OeisA182126.a 25 = 12 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t24, t25, t26]

theorem a26 : OeisA182126.a 26 = 24 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t25, t26, t27]

theorem a27 : OeisA182126.a 27 = 12 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t26, t27, t28]

theorem a28 : OeisA182126.a 28 = 24 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t27, t28, t29]

theorem a29 : OeisA182126.a 29 = 125 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t28, t29, t30]

theorem a30 : OeisA182126.a 30 = 72 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t29, t30, t31]

theorem a31 : OeisA182126.a 31 = 60 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t30, t31, t32]

theorem a32 : OeisA182126.a 32 = 16 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t31, t32, t33]

theorem a33 : OeisA182126.a 33 = 120 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t32, t33, t34]

theorem a34 : OeisA182126.a 34 = 24 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t33, t34, t35]

theorem a35 : OeisA182126.a 35 = 48 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t34, t35, t36]

theorem a36 : OeisA182126.a 36 = 72 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t35, t36, t37]

theorem a37 : OeisA182126.a 37 = 40 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t36, t37, t38]

theorem a38 : OeisA182126.a 38 = 60 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t37, t38, t39]

theorem a39 : OeisA182126.a 39 = 72 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t38, t39, t40]

theorem a40 : OeisA182126.a 40 = 16 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t39, t40, t41]

theorem a41 : OeisA182126.a 41 = 120 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t40, t41, t42]

theorem a42 : OeisA182126.a 42 = 24 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t41, t42, t43]

theorem a43 : OeisA182126.a 43 = 24 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t42, t43, t44]

theorem a44 : OeisA182126.a 44 = 12 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t43, t44, t45]

theorem a45 : OeisA182126.a 45 = 168 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t44, t45, t46]

theorem a46 : OeisA182126.a 46 = 65 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t45, t46, t47]

theorem a47 : OeisA182126.a 47 = 64 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t46, t47, t48]

theorem a48 : OeisA182126.a 48 = 12 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t47, t48, t49]

theorem a49 : OeisA182126.a 49 = 24 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t48, t49, t50]

theorem a50 : OeisA182126.a 50 = 60 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t49, t50, t51]

theorem a51 : OeisA182126.a 51 = 16 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t50, t51, t52]

theorem a52 : OeisA182126.a 52 = 120 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t51, t52, t53]

theorem a53 : OeisA182126.a 53 = 96 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t52, t53, t54]

theorem a54 : OeisA182126.a 54 = 72 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t53, t54, t55]

theorem a55 : OeisA182126.a 55 = 72 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t54, t55, t56]

theorem a56 : OeisA182126.a 56 = 16 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t55, t56, t57]

theorem a57 : OeisA182126.a 57 = 48 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t56, t57, t58]

theorem a58 : OeisA182126.a 58 = 40 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t57, t58, t59]

theorem a59 : OeisA182126.a 59 = 12 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t58, t59, t60]

theorem a60 : OeisA182126.a 60 = 120 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t59, t60, t61]

theorem a61 : OeisA182126.a 61 = 29 := by
  unfold OeisA182126.a OeisA182126.prime
  rw [if_neg (by norm_num)]
  simp only [Nat.reduceSub, Nat.reduceAdd, t60, t61, t62]

end OMA.A182126H2

open OMA.A182126H2 in
theorem OMA.solution : OMA.R_OeisA182126_conjecture3_R1.H2 := by
  intro n hn hle hp
  interval_cases n
  · rw [a1] at hp; exact absurd hp (by norm_num)
  · rw [a2] at hp; exact absurd hp (by norm_num)
  · rw [a3]; decide
  · rw [a4] at hp; exact absurd hp (by norm_num)
  · rw [a5]; decide
  · rw [a6] at hp; exact absurd hp (by norm_num)
  · rw [a7] at hp; exact absurd hp (by norm_num)
  · rw [a8]; decide
  · rw [a9] at hp; exact absurd hp (by norm_num)
  · rw [a10]; decide
  · rw [a11] at hp; exact absurd hp (by norm_num)
  · rw [a12] at hp; exact absurd hp (by norm_num)
  · rw [a13] at hp; exact absurd hp (by norm_num)
  · rw [a14]; decide
  · rw [a15]; decide
  · rw [a16] at hp; exact absurd hp (by norm_num)
  · rw [a17] at hp; exact absurd hp (by norm_num)
  · rw [a18] at hp; exact absurd hp (by norm_num)
  · rw [a19] at hp; exact absurd hp (by norm_num)
  · rw [a20] at hp; exact absurd hp (by norm_num)
  · rw [a21] at hp; exact absurd hp (by norm_num)
  · rw [a22] at hp; exact absurd hp (by norm_num)
  · rw [a23] at hp; exact absurd hp (by norm_num)
  · rw [a24] at hp; exact absurd hp (by norm_num)
  · rw [a25] at hp; exact absurd hp (by norm_num)
  · rw [a26] at hp; exact absurd hp (by norm_num)
  · rw [a27] at hp; exact absurd hp (by norm_num)
  · rw [a28] at hp; exact absurd hp (by norm_num)
  · rw [a29] at hp; exact absurd hp (by norm_num)
  · rw [a30] at hp; exact absurd hp (by norm_num)
  · rw [a31] at hp; exact absurd hp (by norm_num)
  · rw [a32] at hp; exact absurd hp (by norm_num)
  · rw [a33] at hp; exact absurd hp (by norm_num)
  · rw [a34] at hp; exact absurd hp (by norm_num)
  · rw [a35] at hp; exact absurd hp (by norm_num)
  · rw [a36] at hp; exact absurd hp (by norm_num)
  · rw [a37] at hp; exact absurd hp (by norm_num)
  · rw [a38] at hp; exact absurd hp (by norm_num)
  · rw [a39] at hp; exact absurd hp (by norm_num)
  · rw [a40] at hp; exact absurd hp (by norm_num)
  · rw [a41] at hp; exact absurd hp (by norm_num)
  · rw [a42] at hp; exact absurd hp (by norm_num)
  · rw [a43] at hp; exact absurd hp (by norm_num)
  · rw [a44] at hp; exact absurd hp (by norm_num)
  · rw [a45] at hp; exact absurd hp (by norm_num)
  · rw [a46] at hp; exact absurd hp (by norm_num)
  · rw [a47] at hp; exact absurd hp (by norm_num)
  · rw [a48] at hp; exact absurd hp (by norm_num)
  · rw [a49] at hp; exact absurd hp (by norm_num)
  · rw [a50] at hp; exact absurd hp (by norm_num)
  · rw [a51] at hp; exact absurd hp (by norm_num)
  · rw [a52] at hp; exact absurd hp (by norm_num)
  · rw [a53] at hp; exact absurd hp (by norm_num)
  · rw [a54] at hp; exact absurd hp (by norm_num)
  · rw [a55] at hp; exact absurd hp (by norm_num)
  · rw [a56] at hp; exact absurd hp (by norm_num)
  · rw [a57] at hp; exact absurd hp (by norm_num)
  · rw [a58] at hp; exact absurd hp (by norm_num)
  · rw [a59] at hp; exact absurd hp (by norm_num)
  · rw [a60] at hp; exact absurd hp (by norm_num)
  · rw [a61]; decide
