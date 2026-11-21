import Shellsort.GapInversions

namespace Shellsort.OrderedRegionSum
open Finset
noncomputable section

private def halfDiagonal {m : ℕ} (p : Fin m → Fin m → ℝ) (t u : Fin m) : ℝ :=
  if t<u then p t u else if t=u then p t t/2 else 0

/-- Compress any ordered pair statistic once the physical labels are
nondecreasing and their single-slot marginal weights are known. -/
theorem regroup {n m : ℕ} (r : Fin n → Fin m) (w : Fin m → ℝ) (p : Fin m → Fin m → ℝ)
    (mono : Monotone r) (reduce : ∀ f : Fin m → ℝ, ∑ i, f (r i) = ∑ t, w t*f t) :
    (∑ ij ∈ gapPositionPairs n 1, p (r ij.1) (r ij.2)) =
      ∑ t, ∑ u, if t<u then w t*w u*p t u else
        if t=u then w t*(w t-1)/2*p t u else 0 := by
  let B (i j : Fin n) : ℝ := if i<j then p (r i) (r j) else 0
  let Q (i j : Fin n) : ℝ := halfDiagonal p (r i) (r j)
  have point (i j : Fin n) : B i j+B j i =
      Q i j+Q j i-(if i=j then p (r i) (r i) else 0) := by
    rcases lt_trichotomy i j with h|h|h
    · rcases (mono h.le).lt_or_eq with t|t
      · simp [B,Q,halfDiagonal,h,h.ne,not_lt.mpr h.le,t,t.ne,not_lt.mpr t.le,t.ne']
      · simp [B,Q,halfDiagonal,h,h.ne,not_lt.mpr h.le,t]
    · subst j; simp [B,Q,halfDiagonal]
    · rcases (mono h.le).lt_or_eq with t|t
      · simp [B,Q,halfDiagonal,h,h.ne',not_lt.mpr h.le,t,t.ne,not_lt.mpr t.le,t.ne']
      · simp [B,Q,halfDiagonal,h,h.ne',not_lt.mpr h.le,t]
  have identity := congrArg (fun f : Fin n → Fin n → ℝ => ∑ i, ∑ j, f i j)
    (funext fun i => funext (point i))
  simp only [sum_add_distrib,sum_sub_distrib,sum_ite_eq,mem_univ,ite_true] at identity
  have bs : (∑ i, ∑ j, B j i) = ∑ i, ∑ j, B i j := sum_comm
  have qs : (∑ i, ∑ j, Q j i) = ∑ i, ∑ j, Q i j := sum_comm
  rw [bs,qs] at identity
  have qsum : (∑ i, ∑ j, Q i j) = ∑ t, ∑ u, w t*w u*halfDiagonal p t u := by
    calc
      _ = ∑ i, ∑ u, w u*halfDiagonal p (r i) u := by
        apply sum_congr rfl; intro i _; exact reduce (fun u => halfDiagonal p (r i) u)
      _ = ∑ t, w t * (∑ u, w u*halfDiagonal p t u) := reduce (fun t => ∑ u, w u*halfDiagonal p t u)
      _ = _ := by simp [mul_sum,mul_assoc]
  have diag := reduce (fun t => p t t)
  have ledger : (∑ ij ∈ gapPositionPairs n 1, p (r ij.1) (r ij.2)) = ∑ i, ∑ j, B i j := by
    simp [gapPositionPairs,sum_filter,Fintype.sum_prod_type,B,Nat.mod_one]
  rw [ledger]
  calc
    _ = (∑ t, ∑ u, w t*w u*halfDiagonal p t u) - (∑ t, w t*p t t)/2 := by
      rw [←qsum,←diag]; linarith
    _ = ∑ t, ∑ u, (w t*w u*halfDiagonal p t u -
        (if t=u then w t*p t t/2 else 0)) := by
      simp [sum_sub_distrib,sum_div]
    _ = _ := by
      apply sum_congr rfl; intro t _; apply sum_congr rfl; intro u _
      rcases lt_trichotomy t u with h|h|h
      · simp [halfDiagonal,h,h.ne]
      · subst u; simp [halfDiagonal]; ring
      · simp [halfDiagonal,not_lt.mpr h.le,h.ne']

end
end Shellsort.OrderedRegionSum
