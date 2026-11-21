import Shellsort.LocalRelativeOrderMean

namespace Shellsort.TwoLargeGapSourceOverlap
open LocalRelativeOrderMean

def reads (g : ℕ) {n : ℕ} (i j : Fin n) : Prop :=
  j = i ∨ j.val = i.val+g ∨ i.val = j.val+g

private theorem parse {n g : ℕ} (hg : 0 < g) (half : n ≤ 2*g)
    (prev : Fin n → GateTree n) (i z : Fin n) :
    z ∈ sources (passTree g prev i) ↔ ∃ j, reads g i j ∧ z ∈ sources (prev j) := by
  have expand : (∃ j, reads g i j ∧ z ∈ sources (prev j)) ↔
      z ∈ sources (prev i) ∨
      (∃ j : Fin n, j.val = i.val+g ∧ z ∈ sources (prev j)) ∨
      (∃ j : Fin n, i.val = j.val+g ∧ z ∈ sources (prev j)) := by
    simp only [reads,or_and_right,exists_or,exists_eq_left]
  rw [expand]; unfold passTree
  split
  · next hi =>
    simp only [sources,Finset.mem_union]
    have low : i.val < g := by omega
    constructor
    · rintro (h|h); exact Or.inl h; exact .inr (.inl ⟨_,rfl,h⟩)
    · rintro (h|⟨j,e,h⟩|⟨j,e,h⟩)
      · exact Or.inl h
      · have eq : j = ⟨i.val+g,hi⟩ := Fin.ext e
        exact Or.inr (eq ▸ h)
      · omega
  · next hi =>
    split
    · next high =>
      simp only [sources,Finset.mem_union]
      constructor
      · rintro (h|h)
        · exact .inr (.inr ⟨_,by dsimp; omega,h⟩)
        · exact Or.inl h
      · rintro (h|⟨j,e,h⟩|⟨j,e,h⟩)
        · exact Or.inr h
        · have := j.isLt; omega
        · have eq : j = ⟨i.val-g,lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ := Fin.ext (by dsimp; omega)
          exact Or.inl (eq ▸ h)
    · next high =>
      constructor
      · exact Or.inl
      · rintro (h|⟨j,e,h⟩|⟨j,e,h⟩)
        · exact h
        · have := j.isLt; omega
        · omega

private theorem leaf_members {n h g : ℕ} (hg : 0 < g) (gh : g < h) (half : n ≤ 2*g) (i z : Fin n) :
    z ∈ sources (depthTwo h g i) ↔ ∃ j : Fin n, reads g i j ∧ reads h j z := by
  unfold depthTwo
  rw [parse hg half]
  simp only [parse (g := h) (n := n) (by omega) (by omega),sources,Finset.mem_singleton,exists_eq_right']

private theorem column_mem {n h g : ℕ} (hg : 0 < g) (gh : g < h) (half : n ≤ 2*g)
    (i z : Fin n) (ip : i.val+g < n) :
    z ∈ sources (depthTwo h g i) ↔
      z.val = i.val ∨ z.val = i.val+g ∨ z.val = i.val+h ∨ z.val+h = i.val+g := by
  rw [leaf_members hg gh half]
  constructor
  · rintro ⟨j,hj,hz⟩
    have zj := j.isLt
    have zz := z.isLt
    simp only [reads,Fin.ext_iff] at hj hz
    omega
  · rintro (e|e|e|e)
    · exact ⟨i,.inl rfl,.inl (Fin.ext e)⟩
    · exact ⟨z,.inr (.inl e),.inl rfl⟩
    · exact ⟨i,.inl rfl,.inr (.inl e)⟩
    · exact ⟨⟨i.val+g,ip⟩,.inr (.inl rfl),.inr (.inr e.symm)⟩

private theorem equal_columns {n h g : ℕ} (hg : 0 < g) (half : n ≤ 2*g)
    (i : Fin n) (ip : i.val+g < n) :
    sources (depthTwo h g i) = sources (depthTwo h g ⟨i.val+g,ip⟩) := by
  unfold depthTwo passTree; simp [ip,show ¬ i.val+g+g<n by omega,sources,Nat.add_sub_cancel]

/-- For two distinct full columns with left endpoints i<j, every output in
each reads the same physical leaf set. A common leaf exists exactly when
j=i+h-g. This includes the boundary n=2g. -/
theorem physical_overlap {n h g : ℕ} (hg : 0 < g) (gh : g < h) (half : n ≤ 2*g)
    (i j : Fin n) (ip : i.val+g < n) (jp : j.val+g < n) (order : i < j) :
    sources (depthTwo h g i) = sources (depthTwo h g ⟨i.val+g,ip⟩) ∧
    sources (depthTwo h g j) = sources (depthTwo h g ⟨j.val+g,jp⟩) ∧
    ((∃ z, z ∈ sources (depthTwo h g i) ∧ z ∈ sources (depthTwo h g j)) ↔
      j.val+g = i.val+h) := by
  refine ⟨equal_columns hg half i ip,equal_columns hg half j jp,?_⟩
  simp_rw [column_mem hg gh half i _ ip,column_mem hg gh half j _ jp]
  change i.val < j.val at order
  constructor
  · rintro ⟨z,li,lj⟩
    rcases li with a|a|a|a <;> rcases lj with b|b|b|b <;> omega
  · intro e; exact ⟨⟨j.val+g,jp⟩,.inr (.inr (.inl e)),.inr (.inl rfl)⟩

#print axioms physical_overlap
end Shellsort.TwoLargeGapSourceOverlap
