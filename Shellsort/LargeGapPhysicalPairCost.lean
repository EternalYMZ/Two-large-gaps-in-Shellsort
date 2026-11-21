import Shellsort.LargeGapGroupedStopping

/-! Slot-level comparator gates and a real two-large-gap prefix's exact cost. -/
namespace Shellsort.LargeGapPhysicalPairCost
open Finset HarvestOperationalAudit
noncomputable section

def gate {n : ℕ} (g : ℕ) (a : Fin n → Fin n) (i : Fin n) : Fin n :=
  if hi : i.val + g < n then min (a i) (a ⟨i.val+g,hi⟩)
  else if g ≤ i.val then max (a ⟨i.val-g,lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩) (a i)
  else a i

private theorem same_residue {n g : ℕ} (half : n ≤ 2*g) (i j : Fin n) (hi : i.val < g)
    (eq : j.val % g = i.val) : j.val = i.val ∨ j.val = i.val+g := by
  by_cases hj : j.val < g
  · exact Or.inl ((Nat.mod_eq_of_lt hj).symm.trans eq)
  · have ge : g ≤ j.val := by omega
    have t : j.val-g < g := by have := j.isLt; omega
    rw [Nat.mod_eq_sub_mod ge,Nat.mod_eq_of_lt t] at eq
    omega

private theorem both {n g : ℕ} (p : RankPlacement n) (hg : 0 < g) (half : n ≤ 2*g)
    (i j : Fin n) (pair : j.val = i.val+g) :
    (gapSort p g).symm i = min (p.symm i) (p.symm j) ∧
      (gapSort p g).symm j = max (p.symm i) (p.symm j) := by
  have low : i.val < g := by have := j.isLt; omega
  have res (z : Fin n) (eq : z.val % g = i.val) :
      (gapSort p g).symm z = p.symm i ∨ (gapSort p g).symm z = p.symm j := by
    let key := (gapSort p g).symm z
    have rel := gapSort_preserves_residue p g key
    simp only [key,Equiv.apply_symm_apply,eq] at rel
    rcases same_residue half i (p key) low rel.symm with e | e
    · exact Or.inl ((p.symm_apply_eq).2 (Fin.ext e).symm).symm
    · exact Or.inr ((p.symm_apply_eq).2 (Fin.ext (e.trans pair.symm)).symm).symm
  have order := slotStepOrdered_after_gapSort p hg i j pair
  have left := res i (Nat.mod_eq_of_lt low)
  have right := res j (by simp [pair,Nat.mod_eq_of_lt low])
  rcases left with l | l <;> rcases right with r | r <;> rw [l,r] at order ⊢
  · exact (lt_irrefl _ order).elim
  · simp [min_eq_left order.le,max_eq_right order.le]
  · simp [min_eq_right order.le,max_eq_left order.le]
  · exact (lt_irrefl _ order).elim

/-- The same raw-slot min/max gate applies to every input, including singletons. -/
theorem gate_eq {n g : ℕ} (p : RankPlacement n) (hg : 0 < g) (half : n ≤ 2*g)
    (i : Fin n) : (gapSort p g).symm i = gate g p.symm i := by
  unfold gate
  split
  · next hi => exact (both p hg half i ⟨i.val+g,hi⟩ rfl).1
  · next hi =>
    split
    · next ge => exact (both p hg half ⟨i.val-g,lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ i
          (by dsimp; omega)).2
    · next ge =>
      let key := (gapSort p g).symm i
      have rel := gapSort_preserves_residue p g key
      have low : i.val < g := by omega
      simp only [key,Equiv.apply_symm_apply,Nat.mod_eq_of_lt low] at rel
      rcases same_residue half i (p key) low rel.symm with e | e
      · exact ((p.symm_apply_eq).2 (Fin.ext e).symm).symm
      · have := (p key).isLt; omega

private theorem short_chain {α : Type*} [LinearOrder α] (l : List α) (hl : l.length ≤ 2) :
    (insertionComparedExecution l).comparisons = l.length - 1 := by
  cases l with
  | nil => simp [insertionComparedExecution,insertionComparedBack_nil]
  | cons a l =>
    have one : insertionComparedBack [a] = ⟨[a],0,0⟩ := by
      rw [show [a] = [] ++ [a] from rfl,insertionComparedBack_append,insertionComparedBack_nil]
      rfl
    cases l with
    | nil => simp [insertionComparedExecution,one]
    | cons b l =>
      cases l with
      | nil =>
        rw [show [a,b] = [a] ++ [b] from rfl]
        simp only [insertionComparedExecution,insertionComparedBack_append,one]
        change (0 + (insertCompared b [a]).comparisons) = 1
        by_cases lt : b < a <;> simp [insertCompared,lt]
      | cons c l => simp at hl

theorem half_comparisons {n g : ℕ} (p : RankPlacement n) (hg : 0 < g) (half : n ≤ 2*g) :
    gapComparisonCost p g hg = n-g := by
  rw [gapComparisonCost,← chainScanVisits_eq n g hg]
  apply sum_congr rfl
  intro s _
  have small : sourceTrialLength (n/g) (n%g) s.val ≤ 2 := by
    by_contra! h
    have := actual_chain_prefix_lt n g hg s ⟨2,h⟩
    simp only at this
    omega
  simpa only [List.length_ofFn] using short_chain (List.ofFn (chainKeys p g hg s))
    (by simpa only [List.length_ofFn] using small)

/-- How much must still be summed: the only unevaluated terms are the inversion
probabilities of two explicit depth-two gates on the original physical slots. -/
theorem whole_mean {n h g : ℕ} (hg : 0 < g) (gh : g < h) (hn : h < n) (half : n ≤ 2*g) :
    let w : HarvestBlockIteration.PositiveWord := [⟨h,by omega⟩,⟨g,hg⟩,⟨1,by decide⟩]
    uniformAverage (fun p : RankPlacement n => ((runWord (slots p) w).2 : ℝ)) =
      ((n-h:ℕ):ℝ) + (n-g:ℕ) + n - LargeGapCornerRecords.harmonic n -
        LargeGapRecordChanges.grouped (n-h) (h-g) +
      ∑ ij ∈ gapPositionPairs n 1, uniformAverage (fun p : RankPlacement n =>
        if gate g (gate h p.symm) ij.2 < gate g (gate h p.symm) ij.1 then (1 : ℝ) else 0) := by
  classical
  dsimp only
  let H : {a : ℕ // 0 < a} := ⟨h,by omega⟩
  let G : {a : ℕ // 0 < a} := ⟨g,hg⟩
  let U : {a : ℕ // 0 < a} := ⟨1,by decide⟩
  let q := fun p : RankPlacement n => gapSort (gapSort p h) g
  have firstTwo (p : RankPlacement n) : (runWord (slots p) [H,G]).1 = slots (q p) := by
    simp [runWord,runPass_slots,H,G,q]
  have cost (p : RankPlacement n) :
      ((runWord (slots p) [H,G,U]).2 : ℝ) =
       ((n-h:ℕ):ℝ)+(n-g:ℕ)+((runPass (slots (q p)) U).2:ℝ) := by
    simp only [runWord,runPass_slots,add_zero,H,G,U,q,
      half_comparisons (n := n) (g := h) _ _ (by omega),half_comparisons (g := g) _ _ half,
      Nat.cast_add,add_assoc]
  have stop := LargeGapGroupedStopping.all_stopping_means (n := n) [H,G]
    (by simp [H,G,gh]) (by intro z hz; simp [H,G] at hz; rcases hz with rfl | rfl <;> dsimp <;> omega)
    g h rfl hn.le gh.le half
  simp only [firstTwo,List.map_cons,List.map_nil,H,G,sortWord] at stop
  have avgsub (f v : RankPlacement n → ℝ) :
      uniformAverage (fun p => f p - v p) = uniformAverage f - uniformAverage v := by
    simp only [uniformAverage,Finset.sum_sub_distrib,sub_div]
  rw [avgsub] at stop
  have inv (p : RankPlacement n) :
      (gapInsertionCost (q p) 1 (by decide) : ℝ) =
        ∑ ij ∈ gapPositionPairs n 1, (if gate g (gate h p.symm) ij.2 <
          gate g (gate h p.symm) ij.1 then (1:ℝ) else 0) := by
    rw [gapInsertionCost_eq_gapInversions,gapInversions_eq_indicator_sum]
    have bothSlots : (q p).symm = gate g (gate h p.symm) := by
      have inner := funext (gate_eq p (g := h) (by omega) (by omega))
      exact (funext (gate_eq (gapSort p h) hg half)).trans (congrArg (gate g) inner)
    simp only [pairInversionIndicator,bothSlots]
  have st : uniformAverage (fun p => ((runPass (slots (q p)) U).2 : ℝ)) -
      uniformAverage (fun p => (gapInsertionCost (q p) 1 (by decide):ℝ)) = _ := stop
  simp_rw [inv] at st
  have swap (f : (Fin n × Fin n) → RankPlacement n → ℝ) :
      uniformAverage (fun p => ∑ ij ∈ gapPositionPairs n 1, f ij p) =
        ∑ ij ∈ gapPositionPairs n 1, uniformAverage (f ij) := by
    unfold uniformAverage
    rw [sum_comm,Finset.sum_div]
  rw [swap] at st
  change uniformAverage (fun p => ((runWord (slots p) [H,G,U]).2:ℝ)) = _
  simp_rw [cost]
  rw [uniformAverage_add,uniformAverage_const]
  linarith

#print axioms whole_mean

end
end Shellsort.LargeGapPhysicalPairCost
