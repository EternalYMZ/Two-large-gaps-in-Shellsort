import Shellsort.LargeGapCornerRecords
import Shellsort.TwoLargeGapQuadratics

/-! Integer optimum of the overlap-corner score. Here a=n-h, b=n-g=floor(n/2).
The common factors 105 and input-only additive constants have been removed. -/
namespace Shellsort.LargeGapCornerWinner
open LargeGapCornerRecords
noncomputable section

def numerator (n b a : ℕ) : ℤ :=
  46*(a:ℤ)^2-(14*(n:ℤ)+34*(b:ℤ)-96)*(a:ℤ)

def score (n b a : ℕ) : ℝ :=
  (numerator n b a : ℝ)-105*reduced (b-a) (a-(b-a))

def winner (n b : ℕ) : ℕ := (14*n+34*b-50)/92

private theorem step (n a b : ℕ) (hn : 1000 ≤ n) (hb : b = n/2)
    (ha : 2*b ≤ 3*a) (hab : a+1 < b) :
    (a < winner n b → score n b (a+1) < score n b a) ∧
    (winner n b ≤ a → score n b a < score n b (a+1)) := by
  let d := b-a-1
  let t := a-(b-a)
  have hd : b-a = d+1 := by dsimp [d]; omega
  have hd' : b-(a+1) = d := by dsimp [d]; omega
  have ht' : a+1-(b-(a+1)) = t+2 := by dsimp [t]; omega
  have recs := record_increment d t
  let gap : ℤ := 92*(a:ℤ)-14*(n:ℤ)-34*(b:ℤ)+142
  have hq : numerator n b (a+1) - numerator n b a = gap := by
    unfold numerator gap
    push_cast
    ring
  have hstep : score n b (a+1) - score n b a =
      (gap:ℝ)-105*(reduced d (t+2)-reduced (d+1) t) := by
    unfold score
    rw [ht', hd']
    change (_:ℝ) - 105*_ - (_ - 105*reduced (b-a) t) = _
    rw [hd, ← hq, Int.cast_sub]; ring
  constructor
  · intro h
    have hg : gap ≤ 0 := by dsimp [gap]; unfold winner at h; omega
    have hg' : (gap:ℝ) ≤ 0 := by exact_mod_cast hg
    linarith [recs.1]
  · intro h
    by_cases hlarge : 5 ≤ d
    · have hg : 1 ≤ gap := by dsimp [gap]; unfold winner at h; omega
      have hg' : (1:ℝ) ≤ gap := by exact_mod_cast hg
      have hd5 : (5:ℝ) ≤ d := by exact_mod_cast hlarge
      have hsmall : 2/(3*((d:ℝ)+1)*(3*((d:ℝ)+1)-1)) < 1/105 := by
        have hn0 : 0 < 3*((d:ℝ)+1)-1 := by linarith
        apply (div_lt_div_iff₀ (by positivity) (by norm_num)).2
        nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 5) hd5]
      linarith [recs.2]
    · have hg : 106 ≤ gap := by dsimp [gap]; dsimp [d] at hlarge; omega
      have hg' : (106:ℝ) ≤ gap := by exact_mod_cast hg
      have small : 2/(3*((d:ℝ)+1)*(3*((d:ℝ)+1)-1)) ≤ 1 := by
        have hn0 : 0 < 3*((d:ℝ)+1)-1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [sq_nonneg (d:ℝ)]
      linarith [recs.2]

/-- Unique minimum over 2*b ≤ 3*a, a < b. The predecessor/successor
comparison at an exact quadratic tie is strict thanks to the record correction. -/
theorem strict_winner (n : ℕ) (hn : 1000 ≤ n) :
    let b := n/2
    let w := winner n b
    2*b ≤ 3*w ∧ w < b ∧
      ∀ a, 2*b ≤ 3*a → a < b → a ≠ w → score n b w < score n b a := by
  dsimp only
  let b := n/2
  let w := winner n b
  have hb : b = n/2 := rfl
  have hw : 2*b ≤ 3*w ∧ w < b := by dsimp [w,winner,b]; omega
  refine ⟨hw.1, hw.2, ?_⟩
  intro a ha hab hne
  change score n b w < score n b a
  by_cases hlt : a < w
  · obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hlt)
    have descend : ∀ (j:ℕ), a+1+j ≤ w → score n b (a+1+j) < score n b a := by
      intro j
      induction j with
      | zero =>
        intro h
        exact (step n a b hn hb ha (by omega)).1 (by omega)
      | succ j ih =>
        intro h
        have last := (step n (a+1+j) b hn hb (by omega) (by omega)).1 (by omega : a+1+j < w)
        exact last.trans (ih (by omega))
    have e : a+1+k = w := by omega
    simpa only [e] using descend k (by omega)
  · have hu : w < a := by change a ≠ w at hne; omega
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hu)
    have ascend : ∀ (j:ℕ), w+1+j < b → score n b w < score n b (w+1+j) := by
      intro j
      induction j with
      | zero =>
        intro h
        exact (step n w b hn hb hw.1 (by omega)).2 (by rfl)
      | succ j ih =>
        intro h
        exact (ih (by omega)).trans
          ((step n (w+1+j) b hn hb (by omega) (by omega)).2 (by change w ≤ _; omega))
    have e : w+1+k = a := by omega
    simpa only [e] using ascend k (by omega)

#print axioms strict_winner
end
end Shellsort.LargeGapCornerWinner
