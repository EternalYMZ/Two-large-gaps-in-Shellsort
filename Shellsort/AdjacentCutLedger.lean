import Shellsort.OrdinaryWordComparisons

noncomputable section
namespace Shellsort.AdjacentCutLedger
open Finset

/-- Every chain's record-minimum indicator, expressed in original positions. -/
theorem prefixMinima_ofFn {α : Type*} [LinearOrder α] {L : ℕ} (f : Fin L → α) :
    prefixMinima (List.ofFn f) =
      ∑ j : Fin L, if (∀ i : Fin L, i < j → f j < f i) then 1 else 0 := by
  classical
  induction L with
  | zero => simp [prefixMinima]
  | succ L ih =>
    rw [List.ofFn_succ', List.concat_eq_append]
    simp only [prefixMinima, List.reverseRec_concat]
    change prefixMinima _ + _ = _
    rw [ih, Fin.sum_univ_castSucc]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      apply if_congr _ rfl rfl
      constructor
      · intro h i
        refine Fin.lastCases ?_ (fun a => ?_) i
        · intro bad; exact False.elim (not_lt_of_ge (Fin.le_last _) bad)
        · simpa using h a
      · intro h i hi
        exact h i.castSucc (by simpa using hi)
    · apply if_congr _ rfl rfl
      simp only [List.all_eq_true, List.mem_ofFn, decide_eq_true_eq]
      constructor
      · intro h i
        refine Fin.lastCases ?_ (fun a => ?_) i
        · simp
        · exact fun _ => h _ ⟨a,rfl⟩
      · rintro h b ⟨a,rfl⟩
        exact h a.castSucc (Fin.castSucc_lt_last a)




/-- Positions of keys of rank strictly below the indicated cut, along any chain. -/
def lowMask {n L} (f : Fin L → Fin n) (T : ℕ) : Finset (Fin L) :=
  univ.filter fun i => (f i).val < T

/-- Movement reward from a pair of adjacent threshold masks alone. -/
def shiftReward {L : ℕ} (lo hi : Finset (Fin L)) : ℕ :=
  ∑ j : Fin L, if j ∈ hi \ lo then
    ∑ i : Fin L, if i < j ∧ i ∉ hi then 1 else 0 else 0

/-- Once all strictly larger predecessors move, a final comparison occurs
iff an earlier predecessor is at most the pivot. -/
def stopReward {L : ℕ} (lo hi : Finset (Fin L)) : ℕ :=
  ∑ j : Fin L, if j ∈ hi \ lo then
    (if ∃ i : Fin L, i < j ∧ i ∈ hi then 1 else 0) else 0

private theorem mem_delta {n L} (f : Fin L → Fin n) (i : Fin L) (a : Fin n) :
    i ∈ (lowMask f (a.val+1) \ lowMask f a.val) ↔ a = f i := by
  simp [lowMask, Fin.ext_iff]; omega

theorem chain_shifts {n L} (f : Fin L → Fin n) :
    (insertionExecution (List.ofFn f)).2 =
      ∑ a : Fin n, shiftReward (lowMask f a.val) (lowMask f (a.val+1)) := by
  classical
  rw [insertionExecution_ofFn_count]
  simp only [shiftReward, mem_delta]
  rw [Finset.sum_comm (s := (univ : Finset (Fin n))) (t := (univ : Finset (Fin L)))]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro i _
  simp only [lowMask, mem_filter, mem_univ, true_and, Nat.lt_succ_iff, not_le, Fin.lt_def]

theorem chain_comparisons {n L} (f : Fin L → Fin n) :
    (insertionComparedExecution (List.ofFn f)).comparisons =
      ∑ a : Fin n, (shiftReward (lowMask f a.val) (lowMask f (a.val+1)) +
                    stopReward (lowMask f a.val) (lowMask f (a.val+1))) := by
  classical
  rw [Finset.sum_add_distrib, ←chain_shifts]
  have hr := insertionComparedBack_records (List.ofFn f)
  have hs := insertionComparedExecution_shifts (List.ofFn f)
  change (insertionComparedBack _).shifts = _ at hs
  change (insertionComparedBack _).comparisons = _
  rw [hs, prefixMinima_ofFn, List.length_ofFn] at hr
  simp only [stopReward, mem_delta]
  rw [Finset.sum_comm (s := (univ : Finset (Fin n))) (t := (univ : Finset (Fin L)))]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have complements :
      (∑ j : Fin L, if ∀ i : Fin L, i < j → f j < f i then (1:ℕ) else 0) +
        (∑ j : Fin L, if ∃ i : Fin L, i < j ∧ i ∈ lowMask f ((f j).val+1) then (1:ℕ) else 0) = L := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _j : Fin L, (1:ℕ) := by
        apply Finset.sum_congr rfl
        intro j _
        have h : (∃ i : Fin L, i < j ∧ i ∈ lowMask f ((f j).val+1)) ↔ ¬ (∀ i : Fin L, i < j → f j < f i) := by
          simp only [lowMask, mem_filter, mem_univ, true_and, Nat.lt_succ_iff, Fin.lt_def, not_forall, not_lt]
          grind
        simp only [h]
        split <;> simp_all
      _ = L := by simp
  omega




/-- Global colored slots, taken before the actual gap pass. -/
def globalLow {n : ℕ} (p : RankPlacement n) (T : ℕ) : Finset (Fin n) :=
  lowMask p.symm T

def chainMask {n k : ℕ} (hk : 0 < k) (s : Fin k) (A : Finset (Fin n)) :
    Finset (Fin (sourceTrialLength (n/k) (n%k) s.val)) :=
  univ.filter fun i => (positionChainEquiv n k hk).symm ⟨s,i⟩ ∈ A

private theorem chainMask_globalLow {n k : ℕ} (p : RankPlacement n)
    (hk : 0 < k) (s : Fin k) (T : ℕ) :
    chainMask hk s (globalLow p T) = lowMask (chainKeys p k hk s) T := by
  apply Finset.ext
  intro i
  unfold chainMask globalLow lowMask chainKeys
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
  simp

def shiftPair {n k : ℕ} (hk : 0 < k) (lo hi : Finset (Fin n)) : ℕ :=
  ∑ s : Fin k, shiftReward (chainMask hk s lo) (chainMask hk s hi)

def comparisonPair {n k : ℕ} (hk : 0 < k) (lo hi : Finset (Fin n)) : ℕ :=
  ∑ s : Fin k, (shiftReward (chainMask hk s lo) (chainMask hk s hi) +
               stopReward (chainMask hk s lo) (chainMask hk s hi))

/-- The two masks at rank a determine that pivot's contribution.
The sum equals the actual ordinary shift counter. -/
theorem gap_shifts {n k : ℕ} (p : RankPlacement n) (hk : 0 < k) :
    gapInsertionCost p k hk =
      ∑ a : Fin n, shiftPair hk (globalLow p a.val) (globalLow p (a.val+1)) := by
  unfold gapInsertionCost shiftPair
  simp_rw [chainMask_globalLow, chain_shifts]
  rw [Finset.sum_comm]

/-- Likewise for the actual unsentinelled comparison counter (including stops). -/
theorem gap_comparisons {n k : ℕ} (p : RankPlacement n) (hk : 0 < k) :
    gapComparisonCost p k hk =
      ∑ a : Fin n, comparisonPair hk (globalLow p a.val) (globalLow p (a.val+1)) := by
  unfold gapComparisonCost comparisonPair
  simp_rw [chainMask_globalLow, chain_comparisons]
  rw [Finset.sum_comm]

end Shellsort.AdjacentCutLedger



