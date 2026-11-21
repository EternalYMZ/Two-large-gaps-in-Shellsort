import Shellsort.TagThreshold

namespace Shellsort

/-- If a physical slot has no predecessor or successor in its gap chain,
then its original key stays there throughout the pass. -/
theorem gapSort_fixed_between_gap_ends {n h : ℕ} (p : RankPlacement n) (x : Fin n)
    (hleft : (p x).val < h) (hright : n ≤ (p x).val + h) :
    gapSort p h x = p x := by
  apply Fin.ext
  let j := (gapSort p h x).val
  have hj : j < n := (gapSort p h x).isLt
  have he : j % h = (p x).val := by
    simpa only [Nat.mod_eq_of_lt hleft] using gapSort_preserves_residue p h x
  change j = (p x).val
  by_cases hsmall : j < h
  · simpa only [Nat.mod_eq_of_lt hsmall] using he
  · have hle : h ≤ j := by omega
    have hrem : j - h < h := by omega
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hrem] at he
    omega

/-- Every pass in the prefix fixes the same slot, so its initial key stays
there at the end of the actual sequence of gap sorts. -/
theorem sortWord_fixed_between_gap_ends {n H : ℕ} (p : RankPlacement n)
    (x : Fin n) (hs : List ℕ) (hgaps : ∀ h ∈ hs, H ≤ h)
    (hleft : (p x).val < H) (hright : n ≤ (p x).val + H) :
    sortWord p hs x = p x := by
  induction hs generalizing p with
  | nil => rfl
  | cons h hs ih =>
    have hH : H ≤ h := hgaps h (by simp)
    have hfix := gapSort_fixed_between_gap_ends p x (h := h) (by omega) (by omega)
    change sortWord (gapSort p h) hs x = p x
    calc
      _ = gapSort p h x := ih (gapSort p h) (fun k hk => hgaps k (by simp [hk]))
        (by simpa only [hfix] using hleft) (by simpa only [hfix] using hright)
      _ = p x := hfix

/-- With gaps strictly greater than H, the rigorous zero-based central range
is `n - (H+1) ≤ i < H+1`, intersected with valid array indices. -/
theorem sortWord_original_key_at_core_slot {n H : ℕ} (p : RankPlacement n)
    (i : Fin n) (hs : List ℕ) (hgaps : ∀ h ∈ hs, H < h)
    (hlo : n - (H + 1) ≤ i.val) (hhi : i.val < H + 1) :
    (sortWord p hs).symm i = p.symm i := by
  apply (sortWord p hs).injective
  rw [Equiv.apply_symm_apply]
  symm
  calc
    sortWord p hs (p.symm i) = p (p.symm i) :=
      sortWord_fixed_between_gap_ends p (p.symm i) hs
        (H := H + 1) (fun h hh => hgaps h hh)
        (by simpa using hhi) (by simpa using (show n ≤ i.val + (H + 1) by omega))
    _ = i := p.apply_symm_apply i

end Shellsort
