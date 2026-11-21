# Project S · P10 · Two large gaps in Shellsort

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

Let a uniform permutation of n distinct keys be processed by ordinary Shellsort with gaps (n-a, n-b, 1). For every n ≥ 237, fix b = floor(n/2). Among all integers 0 < a < b, the unique minimizer of the executed mean key comparison count is floor((14n + 34b - 50)/92). Equivalently, the second gap is ceil(n/2) and every legal larger first gap competes. The finite comparison formula also applies when both gaps are at least half the input length. Full optimization over the second gap remains open in this formalization.

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.
