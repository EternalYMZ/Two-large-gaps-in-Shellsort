import Shellsort.GapInsertionBridge
import Shellsort.GapSort

/-! A deterministic shift budget for a pass following order at two multiples. -/
namespace Shellsort

/-- Ranks increase between physical slots exactly one specified step apart. -/
def SlotStepOrdered {n : ℕ} (p : RankPlacement n) (a : ℕ) : Prop :=
  ∀ i j : Fin n, j.val = i.val + a → p.symm i < p.symm j

theorem slotStepOrdered_after_gapSort {n a : ℕ} (p : RankPlacement n) (ha : 0 < a) :
    SlotStepOrdered (gapSort p a) a := by
  intro i j hj
  have hm : i.val % a = j.val % a := by simp [hj]
  have hs := gapSort_sorted p a ((gapSort p a).symm i) ((gapSort p a).symm j)
  simp only [Equiv.apply_symm_apply] at hs
  apply (hs hm).mp
  change i.val < j.val
  omega

/-- Every distance of at least two chain steps is a sum of twos and threes. -/
theorem binaryGap_ordered_long {n h : ℕ} (p : RankPlacement n)
    (h₂ : SlotStepOrdered p (2*h)) (h₃ : SlotStepOrdered p (3*h))
    (m : ℕ) (hm : 2 ≤ m) (i j : Fin n) (dist : j.val = i.val + m*h) :
    p.symm i < p.symm j := by
  induction m using Nat.strong_induction_on generalizing i j with
  | ind m ih =>
    by_cases m₂ : m = 2
    · exact h₂ i j (by simpa [m₂] using dist)
    by_cases m₃ : m = 3
    · exact h₃ i j (by simpa [m₃] using dist)
    have parts : m = (m-2)+2 := by omega
    have split : m*h = (m-2)*h + 2*h := by
      calc
        m*h = ((m-2)+2)*h := congrArg (· * h) parts
        _ = _ := Nat.add_mul _ _ _
    let t : Fin n := ⟨i.val+(m-2)*h, by have := j.isLt; omega⟩
    exact lt_trans (ih (m-2) (by omega) (by omega) i t rfl)
      (h₂ t j (by change j.val = (i.val + (m-2)*h) + 2*h; omega))

theorem binaryGap_inverted_pair_adjacent {n h : ℕ} (p : RankPlacement n)
    (h₂ : SlotStepOrdered p (2*h)) (h₃ : SlotStepOrdered p (3*h))
    {i j : Fin n} (hij : i < j) (res : i.val % h = j.val % h)
    (inv : p.symm j < p.symm i) : j.val = i.val+h := by
  have hlt : i.val < j.val := hij
  obtain ⟨m, hm⟩ := (Nat.modEq_iff_dvd' hlt.le).mp res
  have dist : j.val = i.val + m*h := by rw [Nat.mul_comm m h]; omega
  by_cases hm₂ : 2 ≤ m
  · exact ((binaryGap_ordered_long p h₂ h₃ m hm₂ i j dist).asymm inv).elim
  have one : m = 1 := by
    by_contra hne
    have zero : m = 0 := by omega
    simp [zero] at dist
    omega
  simpa [one] using dist

/-- Actual insertion shifts are bounded by the number of possible left slots. -/
theorem binaryGap_insertionCost_le {n h : ℕ} (p : RankPlacement n) (hh : 0 < h)
    (h₂ : SlotStepOrdered p (2*h)) (h₃ : SlotStepOrdered p (3*h)) :
    gapInsertionCost p h hh ≤ n-h := by
  rw [gapInsertionCost_eq_gapInversions]
  unfold gapInversions
  let S := (gapPositionPairs n h).filter (fun ij => p.symm ij.2 < p.symm ij.1)
  have adjacent : ∀ ij ∈ S, ij.2.val = ij.1.val + h := by
    intro ij hij
    obtain ⟨hp, hi⟩ := Finset.mem_filter.mp hij
    exact binaryGap_inverted_pair_adjacent p h₂ h₃
      (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hp).2.2 hi
  change S.card ≤ n-h
  rw [← Finset.card_range (n-h)]
  apply Finset.card_le_card_of_injOn (fun ij : Fin n × Fin n => ij.1.val)
  · intro ij hij
    apply Finset.mem_range.mpr
    change ij.1.val < n-h
    have hp := adjacent ij hij
    have ht := ij.2.isLt
    omega
  · intro x hx y hy hxy
    change x.1.val = y.1.val at hxy
    apply Prod.ext (Fin.ext hxy)
    apply Fin.ext
    rw [adjacent x hx, adjacent y hy, hxy]

end Shellsort
