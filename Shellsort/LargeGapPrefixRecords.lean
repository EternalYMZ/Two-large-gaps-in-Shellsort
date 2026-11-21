import Shellsort.GrowingGapCore
import Shellsort.BinaryGapLocalOrder
import Shellsort.HarvestOperationalAudit

/-! Exact raw slots seen by a prefix minimum after decreasing half-array gaps. -/
namespace Shellsort.LargeGapPrefixRecords
open HarvestOperationalAudit

def hits {n : ℕ} (p : RankPlacement n) (l t : ℕ) : Prop :=
  ∃ i : Fin n, i.val < l ∧ (p.symm i).val < t

private theorem firstInChain {n g : ℕ} (p : RankPlacement n) (hg : 0 < g)
    (i : Fin n) :
    ((gapSort p g).symm ⟨i.val % g, lt_of_le_of_lt (Nat.mod_le _ _) i.isLt⟩) ≤ p.symm i := by
  let q := gapSort p g
  let j : Fin n := ⟨i.val % g, lt_of_le_of_lt (Nat.mod_le _ _) i.isLt⟩
  let y := p.symm i
  have er : (q y).val % g = j.val := by simp [q,y,j,gapSort_preserves_residue]
  have ej : j.val % g = j.val := Nat.mod_eq_of_lt (Nat.mod_lt _ hg)
  by_contra! h
  have below : y < q.symm j := h
  have ch : (q y).val % g = (q (q.symm j)).val % g := by simp [er,ej]
  have bad := (gapSort_sorted p g y (q.symm j) ch).mpr below
  change q y < q (q.symm j) at bad
  rw [Equiv.apply_symm_apply] at bad
  have small : j.val ≤ (q y).val := er ▸ Nat.mod_le _ _
  exact (not_lt_of_ge small) bad

private theorem hits_pass {n g l t : ℕ} (p : RankPlacement n)
    (hg : 0 < g) (hl : l ≤ g) :
    hits (gapSort p g) l t ↔ ∃ i : Fin n, i.val % g < l ∧ (p.symm i).val < t := by
  constructor
  · rintro ⟨i,hi,ht⟩
    let y := (gapSort p g).symm i
    refine ⟨p y, ?_, by simpa [y]⟩
    have h := gapSort_preserves_residue p g y
    change (p y).val % g < l
    rw [← h]
    simpa [y,Nat.mod_eq_of_lt (lt_of_lt_of_le hi hl)]
  · rintro ⟨i,hi,ht⟩
    exact ⟨_,hi,lt_of_le_of_lt (firstInChain p hg i) ht⟩

def fresh (g H l i : ℕ) : Prop := g ≤ i ∧ i < H ∧ i < g+l

private theorem next_step {n g H l t : ℕ} (p : RankPlacement n)
    (hg : 0 < g) (half : n ≤ 2*g) (hH : g < H) (hl : l ≤ g)
    (sorted : SlotStepOrdered p H) :
    hits (gapSort p g) l t ↔ hits p l t ∨ ∃ i : Fin n, fresh g H l i.val ∧ (p.symm i).val < t := by
  rw [hits_pass p hg hl]
  constructor
  · rintro ⟨i,hi,ht⟩
    by_cases low : i.val < g
    · rw [Nat.mod_eq_of_lt low] at hi
      exact Or.inl ⟨i,hi,ht⟩
    have ge : g ≤ i.val := by omega
    have rem : i.val - g < g := by have := i.isLt; omega
    rw [Nat.mod_eq_sub_mod ge, Nat.mod_eq_of_lt rem] at hi
    by_cases new : i.val < H
    · exact Or.inr ⟨i,⟨ge,new,by omega⟩,ht⟩
    · let j : Fin n := ⟨i.val-H,lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
      have sj : p.symm j < p.symm i := sorted j i (by dsimp [j]; omega)
      exact Or.inl ⟨j,by dsimp [j]; omega, lt_trans sj ht⟩
  · rintro (⟨i,hi,ht⟩ | ⟨i,⟨hlo,hhi,hend⟩,ht⟩)
    · exact ⟨i,lt_of_le_of_lt (Nat.mod_le _ _) hi,ht⟩
    · refine ⟨i,?_,ht⟩
      have rem : i.val-g < g := by have := i.isLt; omega
      rw [Nat.mod_eq_sub_mod hlo,Nat.mod_eq_of_lt rem]
      omega

/-- Reversed gaps enumerate newly met right-hand slots, plus the initial prefix. -/
def seen (n l i : ℕ) : List ℕ → Prop
  | [] => i < l
  | g :: gs => seen n l i gs ∨ fresh g (gs.headD n) l i

private theorem snoc {n : ℕ} (p : RankPlacement n) (gs : List ℕ) (g : ℕ) :
    sortWord p (gs ++ [g]) = gapSort (sortWord p gs) g := by
  induction gs generalizing p with
  | nil => rfl
  | cons a gs ih => exact ih (gapSort p a)

private theorem lastOrdered {n : ℕ} (p : RankPlacement n) (gs : List ℕ)
    (pos : ∀ h ∈ gs, 0 < h) :
    SlotStepOrdered (sortWord p gs.reverse) (gs.headD n) := by
  cases gs with
  | nil =>
    intro i j he
    simp at he
    have := j.isLt
    omega
  | cons h gs =>
    simp only [List.reverse_cons, List.headD_cons, snoc]
    exact slotStepOrdered_after_gapSort _ (pos h (by simp))

private theorem head_le {n : ℕ} {gs : List ℕ} (asc : gs.Pairwise (· < ·)) :
    ∀ h ∈ gs.reverse, gs.headD n ≤ h := by
  intro h hh
  rw [List.mem_reverse] at hh
  cases gs with
  | nil => simp at hh
  | cons j gs =>
    simp only [List.headD_cons]
    rcases List.mem_cons.mp hh with he | he
    · omega
    · exact (List.pairwise_cons.mp asc).1 _ he |>.le

theorem actual_prefix {n : ℕ} (p : RankPlacement n) (gs : List ℕ)
    (asc : gs.Pairwise (· < ·)) (legal : ∀ h ∈ gs, 0 < h ∧ h < n ∧ n ≤ 2*h)
    (l t : ℕ) (hl : l ≤ gs.headD n) :
    hits (sortWord p gs.reverse) l t ↔
    ∃ i : Fin n, seen n l i.val gs ∧ (p.symm i).val < t := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨hp,hgn,half⟩ := legal g (by simp)
    have facts := List.pairwise_cons.mp asc
    have gH : g < gs.headD n := by
      cases gs with
      | nil => exact hgn
      | cons h tail => exact facts.1 h (by simp)
    change l ≤ g at hl
    have sub := fun h hh => legal h (List.mem_cons_of_mem g hh)
    have old := ih facts.2 sub (le_trans hl gH.le)
    simp only [List.reverse_cons, snoc]
    rw [next_step _ hp half gH hl (lastOrdered p gs (fun h hh => (sub h hh).1)),old]
    have same (i : Fin n) (hi : fresh g (gs.headD n) l i.val) :
        (sortWord p gs.reverse).symm i = p.symm i := by
      apply (sortWord p gs.reverse).injective
      rw [Equiv.apply_symm_apply]
      symm
      calc
        _ = p (p.symm i) := sortWord_fixed_between_gap_ends p (p.symm i) gs.reverse
          (H := gs.headD n) (head_le facts.2) (by simpa using hi.2.1)
          (by simp only [Equiv.apply_symm_apply]; have := hi.1; omega)
        _ = i := p.apply_symm_apply i
    constructor
    · rintro (⟨i,hi,ht⟩ | ⟨i,hi,ht⟩)
      · exact ⟨i,Or.inl hi,ht⟩
      · exact ⟨i,Or.inr hi,by rwa [same i hi] at ht⟩
    · rintro ⟨i, hi|hi, ht⟩
      · exact Or.inl ⟨i,hi,ht⟩
      · exact Or.inr ⟨i,hi,by rwa [same i hi]⟩

private theorem cap_hits {n H l t : ℕ} (p : RankPlacement n) (half : n ≤ 2*H)
    (ord : SlotStepOrdered p H) : hits p l t ↔ hits p (min l H) t := by
  constructor
  · rintro ⟨i,hi,ht⟩
    by_cases small : i.val < H
    · exact ⟨i,lt_min hi small,ht⟩
    · let j : Fin n := ⟨i.val-H,lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
      have sj : p.symm j < p.symm i := ord j i (by dsimp [j]; omega)
      refine ⟨j,?_,lt_trans sj ht⟩
      dsimp [j]
      have := i.isLt
      omega
  · rintro ⟨i,hi,ht⟩
    exact ⟨i,lt_of_lt_of_le hi (min_le_left ..),ht⟩

/-- The executed array's prefix has a small key exactly when one of the indicated
original slots holds a small key. All thresholds and all cut positions are allowed. -/
theorem executed_prefix {n : ℕ} (p : RankPlacement n) (w : HarvestBlockIteration.PositiveWord)
    (asc : (w.map Subtype.val).reverse.Pairwise (· < ·))
    (large : ∀ h ∈ w, h.val < n ∧ n ≤ 2*h.val) (l t : ℕ) :
    (∃ i : Fin n, i.val < l ∧ ((runWord (slots p) w).1[i.val]).val < t) ↔
    ∃ i : Fin n, seen n (min l ((w.map Subtype.val).reverse.headD n)) i.val
      (w.map Subtype.val).reverse ∧ (p.symm i).val < t := by
  let gs := (w.map Subtype.val).reverse
  have legal (h : ℕ) (hh : h ∈ gs) : 0 < h ∧ h < n ∧ n ≤ 2*h := by
    have hh' : h ∈ w.map Subtype.val := List.mem_reverse.mp hh
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hh'
    exact ⟨a.property,large a ha⟩
  have half : n ≤ 2*gs.headD n := by
    generalize he : gs = ws at *
    cases ws with
    | nil => simp; omega
    | cons g ws => exact (legal g (by simp)).2.2
  have r : gs.reverse = w.map Subtype.val := by simp [gs]
  rw [runWord_slots]
  simp only [slots, Vector.getElem_ofFn]
  change hits (sortWord p (w.map Subtype.val)) l t ↔ _
  rw [← r,cap_hits _ half (lastOrdered p gs (fun h hh => (legal h hh).1))]
  simpa only [List.reverse_reverse] using
    (actual_prefix p gs asc legal (min l (gs.headD n)) t (min_le_right ..))

#print axioms executed_prefix
end Shellsort.LargeGapPrefixRecords
