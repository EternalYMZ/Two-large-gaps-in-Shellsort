import Shellsort.DisjointGateBaseline

namespace Shellsort.PhysicalOverlapClassification
open LocalRelativeOrderMean TwoLargeGapSourceOverlap DisjointGateBaseline Finset
noncomputable section

/-- Every slot is either an unchanged middle singleton or one of the named
outputs in exactly one second-pass pair. -/
def base {n g : ℕ} (i : Fin n) : Fin n :=
  if g ≤ i.val then ⟨i.val-g,lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ else i

private theorem identify {n h g : ℕ} (gh : g<h) (half : n ≤ 2*g)
    (i : Fin n) (full : i.val+g<n ∨ g ≤ i.val) :
    (base (g:=g) i).val+g<n ∧
      sources (depthTwo h g i) = sources (depthTwo h g (base (g:=g) i)) := by
  by_cases high : g ≤ i.val
  · let u : Fin n := ⟨i.val-g,lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
    have up : u.val+g<n := by dsimp [u]; have := i.isLt; omega
    have e : (⟨u.val+g,up⟩ : Fin n) = i := Fin.ext (by dsimp [u]; omega)
    have s : sources (depthTwo h g u) = sources (depthTwo h g i) := by
      obtain ⟨left,right⟩ := TwoLargeGapPhysicalShapes.column_shape gh half u up
      have a : sources (depthTwo h g u) = sources (depthTwo h g ⟨u.val+g,up⟩) := by
        rw [left,right]; rfl
      exact a.trans (congrArg (fun z => sources (depthTwo h g z)) e)
    simpa [base,high,u] using And.intro up s.symm
  · simp only [base,high,ite_false,and_true]
    exact full.resolve_right high

private theorem has_source {n} (t : GateTree n) : (sources t).Nonempty := by
  induction t with
  | leaf _ => simp [sources]
  | low l r h _ | high l r h _ => exact h.mono subset_union_left

def exceptional {n g h : ℕ} (i j : Fin n) : Prop :=
  (i.val+g<n ∨ g ≤ i.val) ∧ (j.val+g<n ∨ g ≤ j.val) ∧
    ((base (g:=g) i) = (base (g:=g) j) ∨
     (base (g:=g) j).val+g = (base (g:=g) i).val+h ∨
     (base (g:=g) i).val+g = (base (g:=g) j).val+h)

theorem all_slot_pairs {n h g : ℕ} (hg : 0<g) (gh : g<h) (half : n ≤ 2*g)
    (i j : Fin n) (different : i ≠ j) :
    (¬ Disjoint (sources (depthTwo h g i)) (sources (depthTwo h g j))) ↔
      exceptional (h:=h) (g:=g) i j := by
  by_cases fa : i.val+g<n ∨ g ≤ i.val
  · by_cases fb : j.val+g<n ∨ g ≤ j.val
    · obtain ⟨ip,li⟩ := identify (h:=h) gh half i fa
      obtain ⟨jp,lj⟩ := identify (h:=h) gh half j fb
      simp only [exceptional,fa,fb,true_and,li,lj]
      let a := base (g:=g) i
      let b := base (g:=g) j
      rcases lt_trichotomy a b with ab|ab|ba
      · have e := (physical_overlap hg gh half a b ip jp ab).2.2
        rw [not_disjoint_iff]
        change (∃ z, z ∈ sources (depthTwo h g a) ∧ z ∈ sources (depthTwo h g b)) ↔ _
        rw [e]
        have v : a.val < b.val := ab
        change (_ : Prop) ↔ a=b ∨ b.val+g=a.val+h ∨ a.val+g=b.val+h
        simp [ne_of_lt ab,show a.val+g≠b.val+h by omega]
      · change ¬ Disjoint (sources (depthTwo h g a)) (sources (depthTwo h g b)) ↔ a=b ∨ _ ∨ _
        rw [ab,not_disjoint_iff]
        obtain ⟨z,hz⟩ := has_source (depthTwo h g b)
        simp [hz,show ∃ z, z ∈ sources (depthTwo h g b) by exact ⟨z,hz⟩]
      · have e := (physical_overlap hg gh half b a jp ip ba).2.2
        rw [disjoint_comm,not_disjoint_iff]
        change (∃ z, z ∈ sources (depthTwo h g b) ∧ z ∈ sources (depthTwo h g a)) ↔ _
        rw [e]
        have v : b.val < a.val := ba
        change (_ : Prop) ↔ a=b ∨ b.val+g=a.val+h ∨ a.val+g=b.val+h
        simp [ne_of_gt ba,show b.val+g≠a.val+h by omega]
    · have s := isolated_source hg gh half j i (by omega) (by omega) (Ne.symm different)
      simp [exceptional,fb,s.symm]
  · have s := isolated_source hg gh half i j (by omega) (by omega) different
    simp [exceptional,fa,s]

theorem all_ordinary_pairs_uncharged {n h g : ℕ} (hg : 0<g) (gh : g<h)
    (half : n ≤ 2*g) (i j : Fin n) (different : i ≠ j)
    (outside : ¬exceptional (h:=h) (g:=g) i j) :
    localInversion (depthTwo h g i) (depthTwo h g j) =
      separate (depthTwo h g i) (depthTwo h g j) := by
  apply disjoint_zero
  by_contra h
  exact outside ((all_slot_pairs hg gh half i j different).mp h)

#print axioms all_ordinary_pairs_uncharged
end
end Shellsort.PhysicalOverlapClassification
