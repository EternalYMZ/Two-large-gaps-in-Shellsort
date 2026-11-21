import Shellsort.TwoLargeGapSourceOverlap

namespace Shellsort.TwoLargeGapPhysicalShapes
open LocalRelativeOrderMean

def leftInput {n} (h : ℕ) (i : Fin n) : GateTree n :=
  if e : i.val+h<n then .low (.leaf i) (.leaf ⟨i.val+h,e⟩) else .leaf i

def rightInput {n} (h : ℕ) (j : Fin n) : GateTree n :=
  if h ≤ j.val then .high (.leaf ⟨j.val-h,lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩) (.leaf j)
  else .leaf j

/-- The two actual gate trees in a column, including their exact source labels. -/
theorem column_shape {n h g : ℕ} (gh : g < h) (half : n ≤ 2*g)
    (i : Fin n) (ip : i.val+g<n) :
    let j : Fin n := ⟨i.val+g,ip⟩
    depthTwo h g i = .low (leftInput h i) (rightInput h j) ∧
    depthTwo h g j = .high (leftInput h i) (rightInput h j) := by
  have ia : ¬ (h  ≤  i.val) := by omega
  have next : ¬ (i.val+g+h<n) := by omega
  have outside : ¬ (i.val+g+g<n) := by omega
  simp [depthTwo,passTree,leftInput,rightInput,ip,ia,next,outside]

/-- For columns i and i+h-g the common first comparator contributes the
minimum at the first left input and the maximum at the second right input. -/
theorem neighboring_shapes {n h g : ℕ} (i j : Fin n) (ip : i.val+g<n) (jp : j.val+g<n)
    (shared : j.val+g=i.val+h) :
    let r : Fin n := ⟨j.val+g,jp⟩
    leftInput h i = .low (.leaf i) (.leaf r) ∧
    rightInput h r = .high (.leaf i) (.leaf r) ∧
    (h ≤ i.val+g ↔ h-g ≤ i.val) ∧ (j.val+h<n ↔ j.val<n-h) := by
  have hi : i.val+h<n := by omega
  have hj : h ≤ j.val+g := by omega
  have p : (⟨i.val+h,hi⟩ : Fin n) = ⟨j.val+g,jp⟩ := Fin.ext shared.symm
  have q : (⟨j.val+g-h,lt_of_le_of_lt (Nat.sub_le _ _) jp⟩ : Fin n) = i := Fin.ext (by change j.val+g-h=i.val; omega)
  dsimp only; simp [rightInput,leftInput,hi,hj,p,q]
  omega

#print axioms neighboring_shapes
end Shellsort.TwoLargeGapPhysicalShapes
