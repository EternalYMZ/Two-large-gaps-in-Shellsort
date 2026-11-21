# Project S · P10 · Two large gaps in Shellsort

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

For a uniform permutation of distinct keys, consider ordinary Shellsort with gaps (n-a, n-b, 1). Lean connects its executed mean key comparisons to a finite formula when both initial gaps are at least n/2. For every n ≥ 237, set b = floor(n/2). Among all integers a satisfying b ≤ 2a and a < b, the unique minimizer is floor((14n + 34b - 50)/92). Comparing against smaller b or against 2a < b at this fixed b remains open in this formalization.

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.
