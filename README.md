# Project S · P10 · Two large gaps in Shellsort

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

Let a uniform permutation of n distinct keys be processed by ordinary Shellsort with gaps (n-a, n-b, 1). For every n ≥ 237, over the entire class 0 < a < b ≤ floor(n/2), the unique minimizer of the executed mean key comparison count is b = floor(n/2), a = floor((14n + 34b − 50)/92). The counterexample at n = 236 establishes the threshold for this all-larger-sizes statement. In gap coordinates the class is n > h > g ≥ ceil(n/2).

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.

## Proof guide

[Read the proof guide](brief.md). For n ≥ 237 and n > h > g ≥ ceil(n/2), the unique minimizing table is (n−w,n−B,1), with B=floor(n/2) and w=floor((14n+34B−50)/92). See Shellsort/TwoGapInterior.lean.
