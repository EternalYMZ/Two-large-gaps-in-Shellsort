import Shellsort.SourceDecomposition
import Shellsort.TaggedLaw
import Shellsort.PrefixMean

noncomputable section
namespace Shellsort
open scoped BigOperators

def taggedSubsetTarget {n : ℕ} (h g : ℕ) (i : Fin n) (B : Finset (Fin n)) : ℕ :=
  (i.val % h + h * chainLowerCount B h (i.val % h)) % g

def taggedSubsetDisplacement {n : ℕ} (h g : ℕ) (i : Fin n) (B : Finset (Fin n)) : ℝ :=
  (taggedSubsetTarget h g i B : ℝ) + ∑ s ∈ Finset.range h,
    sourceResidualReal h g (taggedSubsetTarget h g i B) s (chainLowerCount B h s)

/-- The actual tagged key has the subset observable as its exact signed displacement. -/
theorem actual_tagged_displacement_eq {n : ℕ} (p : RankPlacement n)
    (h g : ℕ) (hh : 0 < h) (hg : 0 < g) (i : Fin n) :
    ((gapSort (gapSort p h) g (p.symm i)).val : ℝ) - ((p.symm i).val : ℝ) =
      taggedSubsetDisplacement h g i (tagLowerState p i).val := by
  have hp := gapSort_tag_position p h hh (p.symm i)
  rw [Equiv.apply_symm_apply] at hp
  rw [two_pass_tag_displacement_real p h g hh hg (p.symm i), hp]
  rfl

/-- Summing by original positions is exactly the same footrule as summing by ranks. -/
theorem twoPass_footrule_by_original_positions {n : ℕ} (p : RankPlacement n) (h g : ℕ) :
    footrule (gapSort (gapSort p h) g) =
      ∑ i : Fin n, |((gapSort (gapSort p h) g (p.symm i)).val : ℝ) - ((p.symm i).val : ℝ)| := by
  unfold footrule transport
  simp only [Equiv.refl_apply]
  exact (p.symm.sum_comp
    (fun x => |((gapSort (gapSort p h) g x).val : ℝ) - (x.val : ℝ)|)).symm

theorem uniform_twoPass_footrule_by_original_positions (n h g : ℕ) :
    uniformAverage (n := n) (fun p => footrule (gapSort (gapSort p h) g)) =
      ∑ i : Fin n, uniformAverage (fun p : RankPlacement n =>
        |((gapSort (gapSort p h) g (p.symm i)).val : ℝ) - ((p.symm i).val : ℝ)|) := by
  simp_rw [twoPass_footrule_by_original_positions]
  unfold uniformAverage
  rw [Finset.sum_comm, Finset.sum_div]

end Shellsort
end
