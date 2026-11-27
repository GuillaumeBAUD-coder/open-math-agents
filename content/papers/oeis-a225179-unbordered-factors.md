---
title: A length-150 counterexample to the unbordered-factor conjecture in OEIS A225179
date: 2026-11-27
summary: An explicit binary word has 22 distinct unbordered factors where the conjecture predicts a minimum of 24.
author: Dhruvik Patel with OpenAI Codex (GPT-6)
---

An unbordered word has no nonempty proper prefix that is also a suffix. Let $B(w)$ count the distinct nonempty contiguous factors of $w$ that are themselves unbordered. Kalle Saari's OEIS entry asks whether its continued-fraction sequence gives the smallest possible $B(w)$ among unbordered words of each length. One binary word of length 150 disproves this equality. [OEIS A225179](https://oeis.org/A225179) · [Formal statement](https://github.com/DhruRules/oeis-a225179/blob/69b7a368f958900e9f06261ab8181c03c24f00a3/Challenge.lean)

## Constructing the word

Begin with `0011`. The substitution L sends 0 to 0 and 1 to 01. The substitution R sends 0 to 01 and 1 to 1. Apply the following eight substitutions from left to right to the entire current word.

```
L R L R R L L R
```

The resulting word is unbordered. Its distinct unbordered factors, including the whole word, total **22**. The theorem `A225179.length150_certificate` checks its length, that it is an admissible binary word, the absence of a border, and the count. To count factors, the proof enumerates every starting position at each length, removes duplicates, then tests every proper border length. [Lean certificate](https://github.com/DhruRules/oeis-a225179/blob/69b7a368f958900e9f06261ab8181c03c24f00a3/Counterexample.lean#L82-L93)

## Comparing with the conjecture

For each coprime pair $p<q$ with $p+q=150$, take the continued fraction of $p/q$. Its score counts the last quotient once, all preceding positive quotients twice, and adds two. The minimum of these scores is **24**, as verified by `A225179.predicted_value`. The proposed equality would force every unbordered length-150 word to have at least 24 distinct unbordered factors. The word above has 22, giving the contradiction proved by `A225179.counterexample`. [Lean proof](https://github.com/DhruRules/oeis-a225179/blob/69b7a368f958900e9f06261ab8181c03c24f00a3/Counterexample.lean#L104-L110)

## The shorter witness

At the Fields Institute in 2013, Saari also asked whether every minimizing word was Sturmian. Applying L R L R L to the same seed gives a length-42 unbordered word with **16** distinct unbordered factors. Its halves of length 21 have **7** and **9** ones. This violates the balance condition for a finite Sturmian word. The theorem `A225179.length42_certificate` checks exactly these word statistics. The accompanying research note gives the separate argument and exhaustive computation for minimality. [Workshop problem 1](https://www.fields.utoronto.ca/programs/scientific/12-13/words/OpenProblemList.pdf) · [Length-42 certificate](https://github.com/DhruRules/oeis-a225179/blob/69b7a368f958900e9f06261ab8181c03c24f00a3/Counterexample.lean#L95-L102) · [Research note](https://github.com/DhruRules/oeis-a225179/blob/69b7a368f958900e9f06261ab8181c03c24f00a3/output/pdf/A225179-counterexample.pdf)

Both words belong to Xavier Provençal's previously classified family of minimal almost balanced words. The result here concerns their counts of unbordered factors and their application to Saari's questions. Dhruvik Patel selected the problem and directed the investigation. OpenAI Codex (GPT-6) found the witnesses, developed the proof, and wrote the Lean code, independent checks and manuscript. [Provençal, §5.1](https://www.xprov.org/articles/Provencal--MinimalNonConvexWords.pdf) · [Independent literal-string verifier](https://github.com/DhruRules/oeis-a225179/blob/69b7a368f958900e9f06261ab8181c03c24f00a3/verify.py)
