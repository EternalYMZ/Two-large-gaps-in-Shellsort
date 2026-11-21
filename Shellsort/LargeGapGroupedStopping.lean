import Shellsort.LargeGapCornerStopping
import Shellsort.LargeGapRecordChanges

namespace Shellsort.LargeGapGroupedStopping
open Finset LargeGapRecordWeights LargeGapCornerRecords LargeGapRecordChanges
open LargeGapCornerStopping HarvestOperationalAudit
noncomputable section

/-- Exact record contribution, allowing either of the two widths to be larger. -/
theorem all_stopping_means {n : ℕ} (w : HarvestBlockIteration.PositiveWord)
    (asc : (w.map Subtype.val).reverse.Pairwise (· < ·))
    (large : ∀ z ∈ w, z.val < n ∧ n ≤ 2*z.val)
    (g h : ℕ) (gaps : (w.map Subtype.val).reverse = [g,h])
    (hg : h ≤ n) (gh : g ≤ h) (size : n ≤ 2*g) :
    uniformAverage (fun p : RankPlacement n =>
      (((runPass (runWord (slots p) w).1 ⟨1,by decide⟩).2 : ℕ) : ℝ) -
        (gapInsertionCost (sortWord p (w.map Subtype.val)) 1 (by decide) : ℝ)) =
      (n:ℝ)-harmonic n-grouped (n-h) (h-g) := by
  let x := n-h
  let y := h-g
  let d := min x y
  let t := max x y - d
  let s := g-(d+t)
  have ge : d+t+s=g := by dsimp [s,t,d,x,y]; omega
  have ne : g+(2*d+t)=n := by dsimp [t,d,x,y]; omega
  let pool := fun j : ℕ => min j g + min j (d+t) + min j d
  have pool_eq (j : ℕ) : cappedWeight n j [g,h] = pool j := by
    simp [cappedWeight, weight,pool, t,d,x,y]; omega
  have re : grouped (n-h) (h-g) = reduced d t := by
    unfold grouped; split <;> congr 1 <;> dsimp [t,d,x,y] <;> omega
  have H := sum_terms d t s
  dsimp only at H
  change (∑ j ∈ range (d+t+s+(2*d+t)),
    (((min (j+1) (d+t+s)+min (j+1) (d+t)+min (j+1) d) -
      (min j (d+t+s)+min j (d+t)+min j d):ℕ):ℝ) /
      (min (j+1) (d+t+s)+min (j+1) (d+t)+min (j+1) d:ℕ)) = _ at H
  rw [ge,ne] at H
  rw [LargeGapStoppingCost.final_stopping_mean w asc large, gaps]
  simp_rw [pool_eq]
  rw [Fin.sum_univ_eq_sum_range (fun j => ((pool (j+1)-pool j:ℕ):ℝ)/(pool (j+1):ℝ))]
  rw [re]
  change (n:ℝ) - (∑ j ∈ range n, _) = _
  dsimp only [pool]
  rw [H]; ring

#print axioms all_stopping_means
end
end Shellsort.LargeGapGroupedStopping
