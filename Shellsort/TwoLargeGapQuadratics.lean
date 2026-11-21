import Mathlib.Tactic

/-! The real quadratics arise by independent marginal integration for two large
gaps. This module checks their minimization and the integer schedule recurrence. -/
namespace Shellsort.TwoLargeGapQuadratics

noncomputable def disjoint (u v : ℝ) : ℝ :=
  1/4 - v/3 + 2*u^2/5 - 2*u*v/5 + v^2/3

noncomputable def overlap (u v : ℝ) : ℝ :=
  1/4 - 2*u/15 - 4*v/15 + (46*u^2 - 34*u*v + 30*v^2)/105

def leftCount (n : ℤ) : ℤ := (14*n + 34*(n/2) - 50)/92

theorem disjoint_bound (u v : ℝ) (hv : v ≤ 1/2) : 17/120 ≤ disjoint u v := by
  have h₁ : 0 ≤ 1/2 - v := by linarith
  have h₂ : 0 ≤ 1/3 - 7*(v+1/2)/30 := by linarith
  unfold disjoint
  nlinarith [mul_nonneg h₁ h₂, sq_nonneg (u-v/2)]

theorem overlap_bound (u v : ℝ) (hv : v ≤ 1/2) :
    891/6440 + 13/105*((u-31/92)^2 + (v-1/2)^2) ≤ overlap u v := by
  unfold overlap
  nlinarith [sq_nonneg (u-31/92), sq_nonneg ((u-31/92)-(v-1/2))]

theorem finite_algebra_certificate :
    (∀ u v : ℝ, v ≤ 1/2 → 17/120 ≤ disjoint u v) ∧
    (∀ u v : ℝ, v ≤ 1/2 →
      891/6440 + 13/105*((u-31/92)^2 + (v-1/2)^2) ≤ overlap u v) ∧
    (overlap (31/92) (1/2) = 891/6440) ∧
    (∀ n : ℤ, leftCount (n+92) = leftCount n + 31 ∧ (n+92)/2 = n/2+46) := by
  refine ⟨disjoint_bound, overlap_bound, ?_, ?_⟩
  · norm_num [overlap]
  · intro n
    unfold leftCount
    constructor <;> omega

#print axioms finite_algebra_certificate
end Shellsort.TwoLargeGapQuadratics
