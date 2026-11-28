---
title: A machine-checked counterexample to Jaeger's modular orientation conjecture for k = 3
date: 2026-11-27
summary: We give a proof, checked by the Lean 4 kernel, that an explicit 13-regular multigraph on 170 vertices is 12-edge-connected and has no modulo-7 orientation, so Jaeger's modular orientation conjecture fails for k = 3. The counterexample is due to Han, Li, Wu and Zhang (2018) and Mattiolo and Steffen (2022); the contribution is the formal proof, including the edge-connectivity of the graph, which the literature does not check.
author: Lionel Arce (github.com/lzvxck), with the agent Claude Code (model claude-opus-5-5)
latex_author: Lionel Arce
latex_urladdr: https://github.com/lzvxck
latex_title: A machine-checked counterexample to Jaeger's modular orientation conjecture for $k = 3$
latex_short_title: A machine-checked counterexample to Jaeger's conjecture
---

**Abstract.** Jaeger's modular orientation conjecture asserts that for every positive integer $k$, every $4k$-edge-connected graph has an orientation in which the indegree and the outdegree of every vertex are congruent modulo $2k+1$. Han, Li, Wu and Zhang disproved it for every $k \ge 3$ in 2018. We give a complete formal proof, checked by the kernel of the Lean 4 proof assistant, that the conjecture fails for $k = 3$. The counterexample is an explicit 13-regular multigraph on 170 vertices, the case $p = 3$ of a construction of Mattiolo and Steffen for one choice of a splitting. We verify formally that it has no modulo-7 orientation, by an argument that follows Han et al., and that it is 12-edge-connected, by a certificate of edge-disjoint walks that the kernel evaluates, combined with the cyclic symmetry of the graph. The edge-connectivity of this particular graph is not checked in the literature. As far as we know, this is the first formal proof that Jaeger's conjecture is false. The mathematical result is not new; the contribution is a machine-checked proof of it.

**Keywords.** Modulo orientation, circular flow, nowhere-zero flow, edge-connectivity, formal proof, Lean 4.

**MSC 2020.** 05C21, 05C40, 68V20.

## 1. Introduction

All graphs in this paper are finite and may have parallel edges and loops. An orientation of a graph is a *modulo $m$-orientation* if $d^+(v) \equiv d^-(v) \pmod m$ at every vertex $v$, where $d^+(v)$ and $d^-(v)$ denote the outdegree and the indegree of $v$. Jaeger [3] observed that a graph has a modulo $(2k+1)$-orientation if and only if it has a nowhere-zero circular $(2 + 1/k)$-flow. In particular, a graph has a modulo 3-orientation if and only if it has a nowhere-zero 3-flow.

**Conjecture 1.1** (Jaeger [2]). *For every positive integer $k$, every $4k$-edge-connected graph has a modulo $(2k+1)$-orientation.*

Conjecture 1.1 is also known as the circular flow conjecture. For $k = 1$ it is equivalent to Tutte's 3-flow conjecture, by a result of Kochol [5], and for $k = 2$ it would imply Tutte's 5-flow conjecture [3, 5]. Thomassen [13] proved that edge-connectivity 8 suffices for $k = 1$, and $2(2k+1)^2 + 2k + 1$ for $k \ge 2$. Lovász, Thomassen, Wu and Zhang [6] improved this to $6k$. In the other direction, Han, Li, Wu and Zhang [1] constructed, for every $k \ge 3$, a $4k$-edge-connected graph with no modulo $(2k+1)$-orientation, and for every $k \ge 5$ a $(4k+1)$-edge-connected one. Recently Jafari [4] proved that $(4k+2)$-edge-connectivity suffices for every $k$; together with [1], this makes $4k+2$ the exact threshold for $k \ge 5$. Naserasr [11] gives another proof. Conjecture 1.1 remains open for $k = 1$ and $k = 2$.

Mattiolo and Steffen [9] modified the construction of [1] to produce regular class 1 graphs with large circular flow number. For $p = 3$ their graph $\tilde M_3$ is 13-regular, and it has no modulo-7 orientation.

**Contribution.** We formalize the case $k = 3$ of the disproof in Lean 4 [10] with the Mathlib library [8]. The formal statement of Conjecture 1.1 (Section 6.1) quantifies over all finite multigraphs, and our main theorem is its negation.

**Theorem 1.2.** *There is a finite loopless multigraph that is 12-edge-connected and has no modulo-7 orientation. Consequently, Conjecture 1.1 fails for $k = 3$.* Lean: `loopless`, `edge_connected` and `nonmodular`; the consequence is `OMA.disproof`.

The witness is the graph $G$ of Section 3, which is the graph $\tilde M_3$ of [9] for one choice of the splitting (Remark 3.4). That $G$ has no modulo-7 orientation is due to [1, 9]. Our formal proof of this part (Section 4) was written for the Left to Solve platform by AkiRA-COM-FP, who used the same graph to refute a conjecture on class 1 graphs [14]. That $G$ is 12-edge-connected is not checked in [1] or [9]: [1] proves that its graph $M$ is 12-edge-connected, and remarks without details that a splitting argument gives 12-edge-connected 13-regular counterexamples. Our formal proof that $G$ is 12-edge-connected (Section 5), and of the reduction of the formal statement to these two facts (Section 6), is new. As far as we know, this is the first formal proof that Jaeger's conjecture is false.

Section 2 fixes notation and proves elementary lemmas. Section 3 defines $G$. Sections 4 and 5 prove that $G$ has no modulo-7 orientation and that it is 12-edge-connected. Section 6 describes the formal statement and the formal proof, and Section 7 discusses the cases that remain open. Each result is followed by the names of the corresponding declarations in the Lean file [14].

## 2. Preliminaries

In this section, $G$ denotes an arbitrary finite multigraph with vertex set $V$ and edge set $E$, in which every edge $e$ has two ends $\mathrm{src}(e)$ and $\mathrm{tgt}(e)$. For $S \subseteq V$, let $\delta(S)$ denote the set of edges with exactly one end in $S$. The graph $G$ is *$n$-edge-connected* if $G - F$ is connected for every set $F$ of fewer than $n$ edges.

We fix the reference direction $\mathrm{src}(e) \to \mathrm{tgt}(e)$ of every edge. A *signing* of $G$ is a map $f : E \to \{1, -1\}$, and its *balance* at a vertex $v$ is

$$\beta_f(v) = \sum_{\mathrm{src}(e) = v} f(e) \;-\; \sum_{\mathrm{tgt}(e) = v} f(e).$$

Lean: `vertexBalance`. An orientation $D$ of $G$ determines the signing $f_D$ with $f_D(e) = 1$ if $D$ orients $e$ from $\mathrm{src}(e)$ to $\mathrm{tgt}(e)$, and $f_D(e) = -1$ otherwise.

**Lemma 2.1.** *For every orientation $D$ and every vertex $v$, $\beta_{f_D}(v) = d^+_D(v) - d^-_D(v)$. Hence $D$ is a modulo $m$-orientation if and only if $\beta_{f_D}(v) \equiv 0 \pmod m$ for every vertex $v$.* Lean: the step `key` of `OMA.disproof`, which proves the identity for the graph $G$ of Section 3 only.

*Proof.* An edge $e$ with $\mathrm{src}(e) = v \ne \mathrm{tgt}(e)$ contributes $f_D(e)$, which is $1$ if $e$ leaves $v$ and $-1$ if it enters $v$. An edge with $\mathrm{tgt}(e) = v \ne \mathrm{src}(e)$ contributes $-f_D(e)$, which is again $1$ if $e$ leaves $v$ and $-1$ if it enters $v$. A loop at $v$ contributes $f_D(e) - f_D(e) = 0$, and it counts once in $d^+_D(v)$ and once in $d^-_D(v)$. ∎

**Lemma 2.2.** *For every signing $f$, (a) $\sum_{v \in V} \beta_f(v) = 0$, and (b) $\sum_{v \in S} \beta_f(v) \le |\delta(S)|$ for every $S \subseteq V$.* Lean: `balance_total`, `balance_cut`.

*Proof.* (a) Every edge contributes $f(e)$ at its end $\mathrm{src}(e)$ and $-f(e)$ at its end $\mathrm{tgt}(e)$. (b) In $\sum_{v \in S} \beta_f(v)$, an edge with both ends in $S$ or both ends outside $S$ contributes 0, and an edge of $\delta(S)$ contributes $\pm 1$. ∎

**Lemma 2.3.** *Let $G$ be loopless, let $f$ be a signing of $G$ and let $v$ be a vertex of degree 11 or 13. If $\beta_f(v) \equiv 0 \pmod 7$, then $\beta_f(v) = \pm 7$.* Lean: `balance_seven_of_odd`, `balance_as_count`.

*Proof.* If $n$ of the $\deg(v)$ edges at $v$ contribute $+1$ to $\beta_f(v)$, then $\beta_f(v) = 2n - \deg(v)$. So $\beta_f(v)$ is odd and lies between $-13$ and $13$, and the only odd multiples of 7 in that range are $\pm 7$. ∎

**Lemma 2.4.** *If seven signs $a, p_1, \dots, p_6 \in \{1, -1\}$ satisfy $a + p_1 + \dots + p_6 \equiv 0 \pmod 7$, then $p_1 = \dots = p_6 = a$.* Lean: `port_uniform`, `sum_signs`.

*Proof.* A sum of seven signs is odd and lies between $-7$ and $7$. If it is divisible by 7, it is $\pm 7$, and then all seven signs are equal. ∎

**Lemma 2.5.** *Every nonzero residue modulo 7 is congruent to one of the integers $\pm 1, \pm 3, \pm 5$, that is, to a sum of five signs.* Lean: `nonzero_as_five_signs`.

*Proof.* The six integers $\pm 1, \pm 3, \pm 5$ are pairwise incongruent modulo 7, and none of them is divisible by 7. ∎

## 3. The graph

**Definition 3.1** (the block). Let $B$ be the multigraph with vertex set $\{0, 1, \dots, 11\}$ whose edges are the 66 edges of the complete graph $K_{12}$ together with the six edges of the triangles $\{3,4,5\}$ and $\{6,7,8\}$, added a second time. The vertices $0, 1, 2, 9, 10, 11$ are called *outer*. Lean: `BaseVertex`, `InnerEdge`, `innerSrc`, `innerTgt`, `outerVertex`.

The block $B$ is loopless, every outer vertex has degree 11 in $B$, and every other vertex has degree 13. Lean: `inner_loopless`; `inner_degree` states that every degree is 11 or 13, which is all that the proof uses.

**Definition 3.2** (the graph $G$). Take thirteen disjoint copies $B_i$ of $B$, for $i \in \mathbb{Z}_{13}$, thirteen *rim* vertices $r_i$, for $i \in \mathbb{Z}_{13}$, and a *centre* $c$. The edges of $G$, with their reference directions, are:

- the edges of each block $B_i$, directed as in $B$;
- for every $i$ and every outer vertex $x$ of $B_i$, a *left port* $r_i \to x$ and a *right port* $r_{i+1} \to x$;
- for every $i$, a *spoke* $r_i \to c$.

Lean: `Vertex`, `Edge`, `src`, `tgt`.

**Proposition 3.3.** *The graph $G$ is loopless, has 170 vertices and 1105 edges, and every vertex has degree 13. Its edge-connectivity is exactly 12.*

*Proof.* There are $13 \cdot 12 + 13 + 1 = 170$ vertices and $13 \cdot (66 + 6 + 12) + 13 = 1105$ edges. An outer vertex has degree $11 + 2$, the other vertices of a block have degree 13, a rim vertex has $6 + 6 + 1$ edges, and the centre has 13. The twelve ports of a block form an edge cut, so the edge-connectivity is at most 12, and it is at least 12 by Theorem 5.4. ∎

Only looplessness (Lean: `loopless`) and the lower bound on the edge-connectivity (Theorem 5.4) are formalized, and the proof of Theorem 1.2 uses nothing else from Proposition 3.3. We also confirmed the counts, the degrees and the edge-connectivity by a computer calculation.

**Remark 3.4** (provenance of the graph). For $p = 3$, the graph $M$ of [1, Construction 3] consists of the blocks $B_i$ with their ports, the centre with its spokes, and one more edge $r_i r_{i+1}$ for each $i$, which is the edge $z_1 z_2$ of the gadget $G_2$ of [1]. So $G$ is $M$ with these thirteen edges deleted. Mattiolo and Steffen [9, Section 3] obtain their 13-regular graph $\tilde M_3$ from $M$ (for $p = 3$ their intermediate graph $M'_3$ equals $M$) by splitting each rim vertex $r_i$ into a vertex of degree 13 and a vertex of degree 2, and then suppressing the vertices of degree 2. In the 13-edge-colouring of [9, Lemma 3.3], the spoke $r_i c$ and the edge $r_{i-1} r_i$ both have colour $i + 11$ (in the indexing of [9], with $t = 1$). If these two edges are the ones split off at every $r_i$, the result is exactly $G$. By [9, Theorem 3.4] the circular flow number of $\tilde M_3$ exceeds $7/3$, which by Jaeger's observation means that $\tilde M_3$ has no modulo-7 orientation. The edge-connectivity of $\tilde M_3$ is not discussed in [9]. In [1, Section 5] the authors remark, leaving the details to the reader, that Mader's splitting theorem [7] yields $4p$-edge-connected $(4p+1)$-regular counterexamples.

## 4. The graph has no modulo-7 orientation

By Lemma 2.1, it suffices to show that no signing $f$ of $G$ has $\beta_f(v) \equiv 0 \pmod 7$ at every vertex $v$. For a signing $f$ of $G$ and $i \in \mathbb{Z}_{13}$, we write $s_i = f(r_i c)$ for the sign of the spoke at $r_i$, $L_i$ for the sum of $f$ over the six left ports of $B_i$, and $R_i$ for the sum of $f$ over the six right ports of $B_i$.

**Lemma 4.1** ([1, Lemma 3.1(i)] for $p = 3$). *No signing of $B$ has $\beta(v) \equiv 0 \pmod 7$ at every vertex $v$ of $B$.* Lean: `inner_not_modulo_seven`.

*Proof.* Suppose that such a signing exists. By Lemma 2.3 every balance is $\pm 7$, and by Lemma 2.2(a) the balances sum to 0, so the set $S$ of vertices with balance 7 has six elements. By Lemma 2.2(b), $42 = \sum_{v \in S} \beta(v) \le |\delta_B(S)|$. But $\delta_B(S)$ contains at most $|S| \cdot |V(B) \setminus S| = 36$ edges of $K_{12}$ and at most two edges of each of the two triangles, so $|\delta_B(S)| \le 40$ (Lean: `inner_cut_card`, which bounds every edge cut of $B$ by 40). This is a contradiction. ∎

**Lemma 4.2.** *Let $f$ be a signing of $G$ with $\beta_f(v) \equiv 0 \pmod 7$ for every vertex $v$. Then for every $i \in \mathbb{Z}_{13}$:*

- *(a) $L_i + R_i \equiv 0 \pmod 7$;*
- *(b) $s_i + L_i + R_{i-1} \equiv 0 \pmod 7$;*
- *(c) $d_i := s_i + L_i \not\equiv 0 \pmod 7$.*

Lean: the steps `hsum`, `hr` and `hd` of `nonmodular`, using `balance_inside`, `balance_total`, `balance_rim` and `block_port_nonzero`.

*Proof.* For a vertex $x$ of $B_i$, the ports at $x$ point into $B_i$, so $\beta_f(x)$ is the balance at $x$ of the restriction of $f$ to $B_i$, minus the sum of $f$ over the ports at $x$ (Lean: `balance_inside`). Summing over all vertices $x$ of $B_i$ and applying Lemma 2.2(a) to $B_i$ gives $\sum_x \beta_f(x) = -(L_i + R_i)$, which proves (a). The edges at $r_i$ are the six left ports of $B_i$, the six right ports of $B_{i-1}$ and the spoke, and all of them leave $r_i$, so $\beta_f(r_i) = L_i + R_{i-1} + s_i$ (Lean: `balance_rim`). This proves (b).

For (c), suppose that $s_i + L_i \equiv 0$. By Lemma 2.4, applied to $s_i$ and the six left ports of $B_i$, every left port of $B_i$ has sign $s_i$, so $L_i = 6 s_i$. By (a), $-s_i + R_i \equiv -s_i - 6 s_i = -7 s_i \equiv 0$, and Lemma 2.4, applied to $-s_i$ and the six right ports of $B_i$, shows that every right port of $B_i$ has sign $-s_i$. So the two ports at each outer vertex of $B_i$ contribute $s_i - s_i = 0$, and the restriction of $f$ to $B_i$ has every balance divisible by 7. This contradicts Lemma 4.1. ∎

**Lemma 4.3** (cf. [1, Lemma 3.2]). *There are no maps $d : \mathbb{Z}_{13} \to \mathbb{Z}_7 \setminus \{0\}$ and $a : \mathbb{Z}_{13} \to \{1, -1\}$ such that $d_i - d_{i-1} + a_i \equiv 0 \pmod 7$ for every $i \in \mathbb{Z}_{13}$.* Lean: `odd_wheel_obstruction`.

*Proof.* By Lemma 2.5 we may choose integers $u_i \in \{\pm 1, \pm 3, \pm 5\}$ with $u_i \equiv d_i \pmod 7$. Put $b_i = u_i - u_{i-1} + a_i$. Then $b_i \equiv 0 \pmod 7$, $b_i$ is odd and $|b_i| \le 11$, so $b_i = \pm 7$. Moreover, $b_i + b_{i+1} = u_{i+1} - u_{i-1} + a_i + a_{i+1}$ has absolute value at most 12 and is a sum of two elements of $\{7, -7\}$, so $b_i + b_{i+1} = 0$. Summing over $i \in \mathbb{Z}_{13}$ gives $2 \sum_i b_i = 0$. But $\sum_i b_i$ is 7 times a sum of thirteen signs, which is odd, so $\sum_i b_i \ne 0$. ∎

**Theorem 4.4.** *The graph $G$ has no modulo-7 orientation.* Lean: `nonmodular`.

*Proof.* Let $f$ be a signing of $G$ with every balance divisible by 7, and let $d_i = s_i + L_i$. By Lemma 4.2(a) and (b),

$$d_i - d_{i-1} + s_{i-1} = s_i + L_i - L_{i-1} \equiv s_i + L_i + R_{i-1} \equiv 0 \pmod 7,$$

and $d_i \not\equiv 0$ by Lemma 4.2(c). This contradicts Lemma 4.3 with $a_i = s_{i-1}$. By Lemma 2.1, $G$ has no modulo-7 orientation. ∎

**Remark 4.5** (comparison with [1]). Lemma 4.1 is [1, Lemma 3.1(i)] for $p = 3$. Lemma 4.2(c) is [1, Lemma 3.1(ii)] adapted to a graph without the edges $z_1 z_2$: the spoke $r_i c$ plays the part of the edge $z_1 z_2$ of the gadget $G_2$. Lemma 4.3 is the parity argument of [1, Lemma 3.2] for the wheel $W$, the dual of an example of DeVos (see [1]), with $d_i$ playing the part of the net flow on a bundle of $2p - 1 = 5$ parallel edges of $W$, and Lemma 2.5 is the counterpart of [1, Observation 2.1]. Together, Lemma 4.2(c) and Lemma 4.3 replace the 2-sum lemma [1, Lemma 2.3]. The balance at the centre $c$ is never used.

## 5. The graph is 12-edge-connected

**Lemma 5.1** (certificate). *For $x = r_0$ and for every vertex $x$ of $B_0$, there are twelve walks in $G$ from $c$ to $x$ in which no edge occurs twice in total; in particular, they are pairwise edge-disjoint.* Lean: `cert`, `cert_ok`, `covers_ok`, `cert_covers`.

*Proof.* The thirteen families of twelve walks are listed explicitly in `cert`. The statement `cert_ok` is proved by `decide +kernel`: the Lean kernel itself evaluates the check that each family has twelve walks, that each walk is a walk of $G$ from $c$ to its target (Lean: `walkOK`), and that no edge occurs twice in the concatenation of a family. The statements `covers_ok` and `cert_covers` check that the targets are $r_0$ and the twelve vertices of $B_0$. ∎

**Lemma 5.2.** *If there are twelve walks from $c$ to a vertex $x$ in which no edge occurs twice in total, then $c$ and $x$ are connected in $G - F$ for every set $F$ of fewer than 12 edges.* Lean: `pigeon`, `walk_reach`.

*Proof.* Each edge of $F$ lies on at most one of the walks, so one of the walks avoids $F$. ∎

**Lemma 5.3.** *For $j \in \mathbb{Z}_{13}$, let $\sigma_j$ map each vertex of $B_i$ to the corresponding vertex of $B_{i+j}$, map $r_i$ to $r_{i+j}$ and fix $c$, and map edges accordingly. Then $\sigma_j$ is an automorphism of $G$ that preserves the reference directions.* Lean: `shV`, `shE`, `src_shE`, `tgt_shE`, `shV_injective`, `shE_injective`.

*Proof.* This is immediate from Definition 3.2: the ports of $B_i$ go to $r_i$ and $r_{i+1}$, and the spoke at $r_i$ goes to $c$. Lean proves that $\sigma_j$ commutes with $\mathrm{src}$ and $\mathrm{tgt}$ and is injective on vertices and on edges, hence bijective, since $G$ is finite. ∎

**Theorem 5.4.** *The graph $G$ is 12-edge-connected.* Lean: `edge_connected`.

*Proof.* Let $F$ be a set of fewer than 12 edges. Every vertex $y \ne c$ has the form $\sigma_j(x)$ with $x = r_0$ or $x$ a vertex of $B_0$. The set $\sigma_j^{-1}(F)$ also has fewer than 12 edges, so by Lemmas 5.1 and 5.2 some walk from $c$ to $x$ avoids it, and the image of that walk under $\sigma_j$ is a walk from $c$ to $y$ that avoids $F$ (Lean: `reach_shift`, `reach_centre`). So every vertex is connected to $c$ in $G - F$, and $G - F$ is connected. ∎

## 6. The formal proof

### 6.1 The formal statement

The formal statement [14] was written for the Left to Solve platform from the Open Problem Garden [12]. Flow theory allows parallel edges and loops, and edge-connectivity depends on parallel edges, so the statement is about finite multigraphs: a vertex type `V`, an edge type `E`, and two ends `src e` and `tgt e` for each edge `e`.

- An orientation is a map `o : E → Bool`: `o e = true` orients `e` from `src e` to `tgt e`, and `false` orients it the other way. So `head e` is `tgt e` when `o e` holds and `src e` otherwise, and `tail e` is the other end.
- `IsEdgeConnected src tgt n` states that for every finite set `S` of fewer than `n` edges, the simple graph `underlying src tgt S` is connected. That graph joins two distinct vertices when some edge outside `S` joins them, so it is connected exactly when the multigraph minus `S` is connected.
- The theorem `main` states that for every $k \ge 1$ and every finite multigraph that is $4k$-edge-connected, some orientation satisfies $\#\{e : \mathrm{head}(e) = v\} - \#\{e : \mathrm{tail}(e) = v\} \equiv 0 \pmod{2k+1}$ at every vertex $v$.

This is Conjecture 1.1 for finite multigraphs, with loops and parallel edges allowed; a loop counts once in the indegree and once in the outdegree.

### 6.2 Proof of Theorem 1.2

The final theorem `OMA.disproof` has type `¬ (type_of% @OMA.S_opg_jaegers_modular_orientation_conjecture.main)`, where `type_of%` refers to the statement exactly as it was merged on the platform. Its proof assumes `main` and applies it with $k = 3$ to the graph $G$ and to Theorem 5.4, using $12 = 4 \cdot 3$, which yields an orientation `o`. For the signing $f$ with $f(e) = 1$ if `o e` holds and $f(e) = -1$ otherwise, the step `key` (Lemma 2.1) gives $\beta_f(v) = -(\#\{e : \mathrm{head}(e) = v\} - \#\{e : \mathrm{tail}(e) = v\})$. So every balance is divisible by 7, which contradicts Theorem 4.4.

### 6.3 Checking the proof

The proof is a single Lean file of about 1000 lines [14], of which about 170 lines are the data of `cert`. It is compiled with Lean 4 v4.33.1 and Mathlib at commit 0df444a360ea, as pinned through the platform's checkout of formal-conjectures (commit 9097e2f90e66). The platform's checker accepted it (pull request #9662), and a local recheck on 27 November 2026, including the build of the statement, took about eight minutes on a desktop computer. The command `#print axioms OMA.disproof` lists only Lean's three standard axioms, `propext`, `Classical.choice` and `Quot.sound`. The proof contains no `sorry` and no `native_decide`, so the certificate of Lemma 5.1 is evaluated by the kernel and not by compiled code.

The declarations of the file up to `nonmodular` (lines 28 to 611) are those of pull request #7972, unchanged. The file also carries declarations from #7972 that the proof does not use: `round_unit_circulation`, its helpers `integral_assignment`, `divergence`, `divergence_add` and `divergence_cast`, and `balance_centre`.

## 7. The cases that remain open

By [1] and [4], the least edge-connectivity that guarantees a modulo $(2k+1)$-orientation is $4k+2$ for every $k \ge 5$. For smaller $k$ the following is known.

- $k = 1$: 6-edge-connectivity suffices [6]. Whether 4-edge-connectivity suffices is Tutte's 3-flow conjecture, which is equivalent, by Kochol [5], to the same question for 5-edge-connectivity.
- $k = 2$: 10-edge-connectivity suffices [4]. Whether 8 or 9 suffices is open.
- $k = 3$: 12-edge-connectivity does not suffice ([1] and Theorem 1.2), and 14 suffices [4]. Whether 13 suffices is open (see also [11]). The graph $G$ has edge-connectivity exactly 12 (Proposition 3.3), so it says nothing about this question.
- $k = 4$: 16-edge-connectivity does not suffice [1], and 18 suffices [4]. Whether 17 suffices is open.

Natural next steps for formalization are the $(4k+1)$-edge-connected counterexamples of [1, Theorem 1.4] for $k \ge 5$, and the positive results of [6] and [4].

## Acknowledgements

The formal proof of Section 4 is due to AkiRA-COM-FP (Left to Solve pull request #7972). The formal statement (pull request #6526), the formal proof of Section 5 and of Theorem 1.2 (pull request #9662), and this paper were written by the AI agent Claude Code (model claude-opus-5-5, Anthropic) under the direction of the author. An independent AI reviewer (Claude Opus) checked the paper against the Lean file and the literature. The author is responsible for the content. The mathematics is due to Han, Li, Wu and Zhang [1] and to Mattiolo and Steffen [9], and the conjecture is due to Jaeger [2]. The proofs were checked on the Left to Solve platform.

## References

- [1] M. Han, J. Li, Y. Wu, C.-Q. Zhang, Counterexamples to Jaeger's circular flow conjecture, J. Combin. Theory Ser. B 131 (2018) 1–11. [doi:10.1016/j.jctb.2018.01.002](https://doi.org/10.1016/j.jctb.2018.01.002)
- [2] F. Jaeger, On circular flows in graphs, in: Finite and Infinite Sets (Eger, 1981), Colloq. Math. Soc. János Bolyai 37, North-Holland, Amsterdam, 1984, 391–402.
- [3] F. Jaeger, Nowhere-zero flow problems, in: L. W. Beineke, R. J. Wilson (eds.), Selected Topics in Graph Theory 3, Academic Press, London, 1988, 71–95.
- [4] A. Jafari, The modular Nash–Williams theorem, preprint, 2026. [arXiv:2610.07034](https://arxiv.org/abs/2610.07034)
- [5] M. Kochol, An equivalent version of the 3-flow conjecture, J. Combin. Theory Ser. B 83 (2001) 258–261.
- [6] L. M. Lovász, C. Thomassen, Y. Wu, C.-Q. Zhang, Nowhere-zero 3-flows and modulo k-orientations, J. Combin. Theory Ser. B 103 (2013) 587–598.
- [7] W. Mader, A reduction method for edge-connectivity in graphs, Ann. Discrete Math. 3 (1978) 145–164.
- [8] The mathlib Community, The Lean mathematical library, in: Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020), ACM, 2020, 367–381.
- [9] D. Mattiolo, E. Steffen, Edge colorings and circular flows on regular graphs, J. Graph Theory 99(3) (2022) 399–413. [arXiv:2001.02484](https://arxiv.org/abs/2001.02484)
- [10] L. de Moura, S. Ullrich, The Lean 4 theorem prover and programming language, in: Automated Deduction – CADE 28, Lecture Notes in Comput. Sci. 12699, Springer, 2021, 625–635.
- [11] R. Naserasr, Jaeger conjecture and Jaeger–Zhang conjecture, preprint, 2026. [arXiv:2611.08862](https://arxiv.org/abs/2611.08862)
- [12] Open Problem Garden, Jaeger's modular orientation conjecture. [openproblemgarden.org](https://www.openproblemgarden.org/op/jaegers_modular_orientation_conjecture)
- [13] C. Thomassen, The weak 3-flow conjecture and the weak circular flow conjecture, J. Combin. Theory Ser. B 102 (2012) 521–529.
- [14] Left to Solve, the Lean files statements/opg-jaegers-modular-orientation-conjecture.lean (pull request #6526) and proofs/opg-jaegers-modular-orientation-conjecture.lean (pull requests #7972 and #9662). [github.com/GuillaumeBAUD-coder/open-math-agents](https://github.com/GuillaumeBAUD-coder/open-math-agents)
