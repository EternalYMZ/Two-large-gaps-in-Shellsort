import Shellsort.ThreePassClosedMean
import Shellsort.LargeGapCornerWinner

namespace Shellsort.ExecutionCornerWinner
open LargeGapCornerRecords LargeGapRecordChanges LargeGapCornerWinner ThreePassClosedMean
noncomputable section

def actual (n a b : ℕ) (ha : a<n) (hb : b<n) : ℝ :=
  let w : HarvestBlockIteration.PositiveWord := [⟨n-a,by omega⟩,⟨n-b,by omega⟩,⟨1,by decide⟩]
  uniformAverage (fun p : RankPlacement n => ((HarvestOperationalAudit.runWord
    (HarvestOperationalAudit.slots p) w).2:ℝ))

private def common (n b : ℕ) : ℝ :=
  105*(n:ℝ)^2/4-28*(b:ℝ)*n+30*(b:ℝ)^2+315*(n:ℝ)/4+86*b-105*harmonic n

theorem comparison_score {n a b : ℕ} (ap : 0<a) (ab : a<b) (half : 2*b≤n)
    (corner : 2*b≤3*a) :
    105 * actual n a b (by omega) (by omega) = score n b a + common n b := by
  unfold actual
  rw [executed_closed (show 0<n-b by omega) (show n-b<n-a by omega) (show n-a<n by omega)
    (show n≤2*(n-b) by omega)]
  rw [show n-(n-a)=a by omega,show n-(n-b)=b by omega,show n-a-(n-b)=b-a by omega]
  have region : b-a<a := by omega
  have rem : ¬a≤b-a := by omega
  unfold baseline score numerator common
  simp only [region,ite_true,grouped,rem,ite_false]
  by_cases edge : a ≤ 2*(b-a)
  · simp only [edge,ite_true]
    have eq : 3*(a:ℝ) = 2*b := by exact_mod_cast (show 3*a = 2*b by omega)
    push_cast
    nlinarith
  · simp only [edge,ite_false]
    push_cast
    ring

/-- At fixed b=floor(n/2), against all legal contenders with 2b≤3a,
the formula is the unique actual-comparison minimizer for n≥1000. -/
theorem actual_winner (n : ℕ) (hn : 1000 ≤ n) :
    let b := n/2
    let w := winner n b
    ∃ hw : w<n, ∃ hb : b<n, w<b ∧ 2*b ≤ 3*w ∧
      ∀ a (ha : a<n), 2*b≤3*a → a<b → a≠w → actual n w b hw hb < actual n a b ha hb := by
  dsimp only
  obtain ⟨cw,wb,rest⟩ := strict_winner n hn
  have hb : n/2<n := by omega
  refine ⟨by omega,hb,wb,cw,?_⟩
  intro a ha ca a_lt neq
  have ws := comparison_score (n:=n) (by omega : 0<winner n (n/2)) wb (by omega) cw
  have ascore := comparison_score (n:=n) (by omega : 0<a) a_lt (by omega) ca
  linarith [rest a ca a_lt neq]

#print axioms actual_winner
end
end Shellsort.ExecutionCornerWinner
