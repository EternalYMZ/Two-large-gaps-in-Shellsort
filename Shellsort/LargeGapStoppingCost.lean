import Shellsort.LargeGapRecordWeights
import Shellsort.AdjacentCutLedger

/-! End-to-end mean of the ordinary unit-gap pass's stopping comparisons. -/
namespace Shellsort.LargeGapStoppingCost
open Finset HarvestOperationalAudit LargeGapRecordWeights LargeGapRecordMean

private theorem prefix_record_sum {n} (p : RankPlacement n) :
    (gapPrefixMinima p 1 (by decide) : ℝ) = ∑ j : Fin n, indicator (record (slots p) j) := by
  classical
  rw [gapPrefixMinima,Nat.cast_sum,sum_positions_by_chains n 1 (by decide)]
  apply sum_congr rfl
  intro s _
  rw [AdjacentCutLedger.prefixMinima_ofFn,Nat.cast_sum]
  apply sum_congr rfl
  intro v _
  simp only [Nat.cast_ite,Nat.cast_one,Nat.cast_zero, indicator, record, slots,Vector.getElem_ofFn]
  apply if_congr _ rfl rfl
  constructor
  · intro h i hi
    obtain ⟨⟨s',z⟩,rfl⟩ := (positionChainEquiv n 1 (by decide)).symm.surjective i
    obtain rfl : s' = s := Subsingleton.elim _ _
    exact h z ((chainPosition_lt_iff ..).mp hi)
  · intro h i hi
    exact h _ ((chainPosition_lt_iff ..).mpr hi)

/-- The mean comparisons in the final unit pass, minus its successful right shifts.
The schedule is fixed before the uniform rank permutation is drawn. -/
theorem final_stopping_mean {n : ℕ} (w : HarvestBlockIteration.PositiveWord)
    (asc : (w.map Subtype.val).reverse.Pairwise (· < ·))
    (large : ∀ h ∈ w, h.val < n ∧ n ≤ 2*h.val) :
    let gs := (w.map Subtype.val).reverse
    uniformAverage (fun p : RankPlacement n =>
      (((runPass (runWord (slots p) w).1 ⟨1,by decide⟩).2 : ℕ) : ℝ)
      - (gapInsertionCost (sortWord p (w.map Subtype.val)) 1 (by decide) : ℝ)) =
      n - ∑ j : Fin n, ((cappedWeight n (j.val+1) gs - cappedWeight n j.val gs : ℕ) : ℝ)
        / (cappedWeight n (j.val+1) gs : ℝ) := by
  classical
  let gs := (w.map Subtype.val).reverse
  let final := fun (p : RankPlacement n) => sortWord p (w.map Subtype.val)
  let F := fun (j : Fin n) (p : RankPlacement n) => indicator (record (runWord (slots p) w).1 j)
  have localCost (p : RankPlacement n) :
    (((runPass (runWord (slots p) w).1 ⟨1,by decide⟩).2 : ℕ) : ℝ) -
        (gapInsertionCost (final p) 1 (by decide) : ℝ) =
      (n : ℝ) - ∑ j : Fin n, F j p := by
    have h := gapComparisonCost_records (final p) 1 (by decide)
    have e := congrArg (fun z : ℕ => (z : ℝ)) h
    simp only [Nat.cast_add,prefix_record_sum] at e
    simp only [F,runWord_slots,runPass_slots,final] at *
    linarith
  have avg := congrArg (uniformAverage (n := n)) (funext localCost)
  have se : uniformAverage (fun p : RankPlacement n => (n:ℝ)-∑ j : Fin n, F j p) =
      (n:ℝ)-∑ j : Fin n, uniformAverage (F j) := by
    unfold uniformAverage
    rw [Finset.sum_sub_distrib, sub_div, Finset.sum_comm (f := fun p j => F j p)]
    have c := uniformAverage_const n (n:ℝ)
    unfold uniformAverage at c
    rw [c, Finset.sum_div]
  rw [se] at avg
  change _ = (n:ℝ)-_ 
  rw [avg]
  congr 1
  exact sum_congr rfl (fun j _ => executed_weighted_record w asc large j)

#print axioms final_stopping_mean
end Shellsort.LargeGapStoppingCost
