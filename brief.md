# The best two large gaps before a final insertion pass

On a uniform permutation of distinct keys run $(h,g,1)$ with $n>h>g\ge\lceil n/2\rceil$. Every nontrivial chain in the first two passes is a pair. The final pass costs $I+n-R$, where $I$ counts remaining inversions and $R$ counts strict prefix minima including the first key. For [2,0,1] this gives three comparisons for two inversions. To compute the mean, classify slot pairs by their shared original keys and count prefix minima separately.

Write $a=n-h$, $b=n-g$. For $n\ge237$ fix $b=\lfloor n/2\rfloor$. The unique best first gap corresponds to
$$a=\left\lfloor(14n+34b-50)/92\right\rfloor.$$
The proof compares adjacent values of $a$ and controls the change in the record-minimum term. For $2a<b$, put $q=\lfloor b/2\rfloor$. Every such candidate has cost greater than $C(q,b)-1$, whereas $C(q+2,b)<C(q,b)-1$ in the overlap region. This excludes an entire range in one comparison. For $n=237$, $g=119$, the winning first gap is 158.

For an interior lattice point below $b=\lfloor n/2\rfloor$, the finite formula gives a legal step increasing either $a$ or $b$ by one and strictly decreasing cost. The sum $a+b$ increases on a finite set, so improvement reaches the boundary. This extends uniqueness to the entire two-large-gap class. At $n=236$ the formula gives $(158,118,1)$ and $(157,118,1)$ costs strictly less on average, establishing the exact onset. Smaller second gaps can produce longer chains and require another analysis.

[ThreePassClosedMean.lean](https://github.com/EternalYMZ/Two-large-gaps-in-Shellsort/blob/ab5b5b784e5487ceca89e2b17abcd7fa4d418f67/Shellsort/ThreePassClosedMean.lean) · [TwoGapOverlapWinner.lean](https://github.com/EternalYMZ/Two-large-gaps-in-Shellsort/blob/ab5b5b784e5487ceca89e2b17abcd7fa4d418f67/Shellsort/TwoGapOverlapWinner.lean) · [TwoGapHalfWinner.lean](https://github.com/EternalYMZ/Two-large-gaps-in-Shellsort/blob/ab5b5b784e5487ceca89e2b17abcd7fa4d418f67/Shellsort/TwoGapHalfWinner.lean)
