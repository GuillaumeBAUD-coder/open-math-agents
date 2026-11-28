# The square-plane transversal difference number at seven

Robert Leshner (@rleshner), with Codex (GPT-6.2 Astra), 27 November 2026.

**Theorem.** Let $T$ range over sets of representatives for reduction modulo 7 in $(\mathbb Z/49\mathbb Z)^2$. The minimum of $|T-T|$ is **169**.

Barcau, Paşol and Ţurcaş conjectured the value $(2p-1)^2$ for every odd prime. They verified $p=3,5$ and reported that their computation did not finish for $p=7$. We give a computer-assisted proof for $p=7$. It combines a projection argument for general $p$, a counting reduction specific to seven, and an exhaustive integer calculation. The general conjecture remains open. [Their paper, Sections 6.2–6.4](https://arxiv.org/html/2606.27961v1#S6) · [Their verification code](https://github.com/georgeturcasubb/transversals)

## A projection bound for every odd prime

Write $s(x)$ for the representative of $x$ in the residue plane $V=\mathbb F_p^2$. For each $u\ne0$, fix an integer lift $e$ of $u$. Write the differences in direction $u$ as $s(x+u)-s(x)=e+p a(x)$, where $a(x)\in V$. Let $A_u$ be the image of $a$. Changing $e$ translates $A_u$. The full difference count is $1+\sum_{u\ne0}|A_u|$, and opposite directions have the same size. On each cyclic line of length $p$ in direction $u$, telescoping gives $\sum a(x)=-u$ in $V$. These identities appear in Lemmas 6.1 and 6.3 of the paper.

Suppose some $A_u$ lies in an affine line. Its linear direction contains $u$, by the cycle identity; a singleton is impossible. Choose a basis taking $u$ to $(1,0)$. An invertible residue-plane basis change lifts to an invertible matrix modulo $p^2$, since its determinant is prime to $p$. Using $e=(1,0)$, all horizontal step labels now have the same second coordinate $b$. The shear $(X,Y)\mapsto(X,Y-pbX)$ makes the actual second coordinate constant along each horizontal residue row. Distinct rows have distinct second-coordinate residues. Thus the projection onto the second coordinate is a cyclic transversal $B$ of size $p$, and the first coordinates in each of its rows form another cyclic transversal.

For any two transversals $U,W$ modulo $p$ in $\mathbb Z/p^2\mathbb Z$, $|U-W|\ge2p-1$. Indeed, the difference set covers every residue. If it has nontrivial translation stabilizer, it contains a whole coset of $p\mathbb Z/p^2\mathbb Z$ in every residue and is the whole group. With trivial stabilizer, Kneser's addition theorem gives $|U-W|\ge|U|+|W|-1$. Apply this first to $B-B$. For each of its at least $2p-1$ values choose one pair of rows giving that difference. Their horizontal differences give at least $2p-1$ distinct elements in the corresponding fibre. Consequently $|T-T|\ge(2p-1)^2$.

## Four necessary small directions when p = 7

A counterexample would have at most 167 differences, since the support is odd by negation symmetry. By the projection bound all nonzero direction images span the affine plane and hence have size at least three. Among the 24 antipodal direction pairs, at least 13 must have size exactly three: otherwise the support is at least $1+2(12\cdot3+12\cdot4)=169$.

There are eight projective lines, each carrying three antipodal pairs. At least two lines must each contain at least two size-three pairs (even two such lines and six with at most one account for at most twelve). Doubling cyclically permutes the three pairs on a line modulo 7. Any two of them can thus be written $\{\pm u\},\{\pm2u\}$. Change basis using two independent such directions. From now on **the first and second steps in each of the two coordinate directions have exactly three labels**, and their images are noncollinear.

## Cyclic words and normalization

Consider one of the unit directions $e$. Its step labels are a triangle $a_0,a_1,a_2$. If their counts on a line are $n_0,n_1,n_2$, then
$$n_0+n_1+n_2=7,\qquad n_1(a_1-a_0)+n_2(a_2-a_0)=-e\pmod 7.$$
The triangle is noncollinear, so the counts are unique modulo 7. No line is constant, by the cycle identity. Its three counts lie in $[0,6]$, hence are the same integers on every parallel line. Each is positive because all three labels occur somewhere. Order the symbols by nonincreasing counts, resolving ties in any order.

We may arrange that $a_0=0$ independently for both axes. Apply the automorphism $z\mapsto(I-7M)z$ modulo 49, where the columns of $M$ are the two chosen base labels. This subtracts the appropriate base label from every step and preserves the quotient. The verifier enumerates all possibilities $(0,b,c)$ with nonzero determinant and $n_1b+n_2c=-e$. If $n_1=n_2$ it may sort $b,c$ lexicographically by relabeling.

A double step has label equal to the sum of two adjacent unit-step labels when measured relative to $2e$. The six possible unordered pair sums of a noncollinear alphabet $(0,b,c)$ are distinct in characteristic seven. Thus exactly three unordered adjacency types occur across all cyclic words in this direction. Each individual word uses all three: its distinct-symbol transitions connect the three symbols, and if it used only two unordered types these would form a loopless path, which admits no odd closed walk. This proves that the set of three adjacency types is identical on every parallel line. Enumerating the $3^7$ possible words and the permitted alphabets gives **294 families per axis**. A family specifies both its alphabet and its common set of adjacency types.

## Exhausting the sections

Choose one horizontal and one vertical family. At each column $i$, the vertical word gives a sequence of prefixes $P_i(y)$ in $V$, with $P_i(0)=0$. If the lift offset at the bottom of the column is $b_i$, the point at row $y$ is $(i,y)+7(b_i+P_i(y))$. Translating the section lets us take the lift of the origin to be zero. Translating along the first column and translating its new origin back to zero also lets us choose a lexicographically least cyclic rotation of its vertical word. This operation just reindexes the original step labels.

Given consecutive columns and a horizontal bottom step with label $h$, the horizontal label at row $y$ is forced to be $h+P_{i+1}(y)-P_i(y)$. This identity applies to the final, wrapping, column transition as well, because labels are measured relative to the actual step $(1,0)$ modulo 49. The verifier builds all admissible transitions between vertical words. It traverses seven transitions, requires a return to the starting word, and checks that every horizontal row spells a word from its family. The word cycle identity ensures wraparound consistency. Conversely, every normalized section under consideration follows one of these paths. The final step counts distinct differences directly by subtraction of actual points in $(\mathbb Z/49\mathbb Z)^2$.

The traversal counted **3,983,588** paths across the $294^2$ family pairs. Some sections have several descriptions. The smallest observed difference support was **179**, excluding a counterexample in this class. A second implementation traversing rows and scoring by quotient-direction supports found the same minimum and the same count of 1,205,288 configurations with varying parallel words under the respective axis conventions. The standard box $\{0,\ldots,6\}^2$ has exactly $13^2=169$ distinct differences and gives the matching upper bound. The minimum 179 applies only after the four small-direction conditions; the box is outside that enumeration.

## Reproduce

From this directory:

```sh
c++ -std=c++17 -O3 verify.cpp -o /tmp/verify-transversal-seven
/tmp/verify-transversal-seven
```

The optional arguments are a first vertical-family index and an exclusive end index for splitting the computation. For the full run the output is:

```text
families 294 x 294, range 0 294, sections 3983588, minimum 179, varying-column sections 1205288, varying minimum 179
```

The finite verification uses exact integer arithmetic. The general reductions are mathematical proofs as written above. This is a reproducible computer-assisted argument, pending independent review.
