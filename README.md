# Project S · P10 · Two large gaps in Shellsort

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

For two initial gaps at least half the input length, Lean connects the executed mean comparison count to the closed finite formula. A second root proves an exact optimizer in the specified corner for n ≥ 1000. The proposed full-domain threshold n ≥ 237 is outside the checked winner statement.

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.
