# 两个大间隔怎样配合，才能让平均键比较次数最少？

在均匀随机的互异键上，运行无哨兵线性插入的三遍 Shellsort，依次采用 $(h,g,1)$。若 $n>h>g\ge\lceil n/2\rceil$，前两趟每条非平凡链都只有两个键。决定平均比较次数时，前两趟有多少次比较是已知的；难点是它们给末遍留下了什么数组。

例如末遍要依次插入的键为 $[2,0,1]$。它有两个逆序，实际做了三次键比较。插入 $0$ 时一直抵达链首，插入 $1$ 时还要同 $0$ 比一下才停。一般地，若末遍开始时有 $I$ 个逆序、从左往右有 $R$ 个新最小值（首项也计入），实际末遍键比较数就是 $I+n-R$。前两趟若动过同一个来源的键，末遍各槽会相关。证明按共享原始键的方式给槽对分类，逐类计算期望逆序；对前缀中新最小值的出现另行计数。这得到每对合法大间隔的有限平均比较公式。[实际程序的比较均值](https://github.com/EternalYMZ/Two-large-gaps-in-Shellsort/blob/ab5b5b784e5487ceca89e2b17abcd7fa4d418f67/Shellsort/ThreePassClosedMean.lean)

写 $a=n-h,\ b=n-g$。公开 Lean 定理证明，对每个 $n\ge237$，固定 $b=\lfloor n/2\rfloor$，在全部整数 $0<a<b$ 中，唯一使平均比较数最小的是
$$
a=\left\lfloor\frac{14n+34b-50}{92}\right\rfloor .
$$
证明比较相邻 $a$ 的费用差，控制纪录项波动对差值符号的影响。针对 $2a<b$ 的另一段，取 $q=\lfloor b/2\rfloor$，先证这段中每个候选的均值都大于 $C(q,b)-1$，再证重叠区中的 $C(q+2,b)<C(q,b)-1$。这一次跨边界比较就排除了整段。例如 $n=237$、$g=119$ 时，唯一最优首间隔是 $158$。[重叠范围的整数最优性](https://github.com/EternalYMZ/Two-large-gaps-in-Shellsort/blob/ab5b5b784e5487ceca89e2b17abcd7fa4d418f67/Shellsort/TwoGapOverlapWinner.lean) · [固定第二间隔的全部竞争者](https://github.com/EternalYMZ/Two-large-gaps-in-Shellsort/blob/ab5b5b784e5487ceca89e2b17abcd7fa4d418f67/Shellsort/TwoGapHalfWinner.lean)

**怎样把固定第二间隔的结论推广到整类？** 把候选画成整数格点 $(a,b)$，边界是 $b=\lfloor n/2\rfloor$。本地待审的 Lean 证明从有限均值公式推出，对每个内部点，总能把 $a$ 或 $b$ 之一增加 $1$，同时保持合法，并使平均键比较数严格下降。每走一步，$a+b$ 增加，而可走的点只有有限个，所以一定抵达边界。此时只需用上面已经公开的边界最优定理。于是对每个 $n\ge237$，公式在整个 $n>h>g\ge\lceil n/2\rceil$ 内给出唯一赢家。

起点也可检验。$n=236$ 时公式给 $(158,118,1)$，而 $(157,118,1)$ 的实际平均比较数严格更低。这个反例验证了 $237$ 是使公式从此一直成立的最小起点。内部点的改进定理和这个反例均已有本地 Lean 版本，以上链接对应此前公开的证明。若允许第二间隔小于 $\lceil n/2\rceil$，前两趟可能出现三键以上的链，要重新分析这些比较的相互影响。
