import Shellsort.LargeGapPhysicalPairCost
import Mathlib.Data.Finset.Sort

namespace Shellsort.LocalRelativeOrderMean
open Finset
noncomputable section

private theorem relative_order {n : ℕ} (s : Finset (Fin n)) (p : Equiv.Perm (Fin n)) :
    ∃ d : Equiv.Perm s, ∀ x y : s, p x < p y ↔ d x < d y := by
  let r := s.map p.toEmbedding
  let e : s ≃ r := s.equivMap p.toEmbedding
  let a : r ≃o s := (r.orderIsoOfFin (by simp [r])).symm.trans (s.orderIsoOfFin rfl)
  refine ⟨e.trans a.toEquiv, fun x y => ?_⟩
  change e x < e y ↔ a (e x) < a (e y)
  exact a.lt_iff_lt.symm

private def permuteSlots {n : ℕ} (e : Equiv.Perm (Fin n)) :
    RankPlacement n ≃ RankPlacement n where
  toFun p := p.trans e.symm
  invFun p := p.trans e
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- Every observable depending only on the relative order of a fixed set of raw
slots has its exact mean on the permutation group of those slots alone. -/
theorem local_mean {n : ℕ} (s : Finset (Fin n)) (f : (Fin n → Fin n) → ℝ)
    (localOrder : ∀ a b : Fin n → Fin n,
      (∀ x y : s, a x < a y ↔ b x < b y) → f a = f b) :
    uniformAverage (fun p : RankPlacement n => f p.symm) =
      (∑ d : Equiv.Perm s, f (Equiv.Perm.ofSubtype d)) / (s.card.factorial : ℝ) := by
  classical
  let L := ∑ d : Equiv.Perm s, f (Equiv.Perm.ofSubtype d)
  let obs := fun (p : RankPlacement n) (d : Equiv.Perm s) =>
    f (fun x => p.symm (Equiv.Perm.ofSubtype d x))
  have row (p : RankPlacement n) : (∑ d, obs p d) = L := by
    obtain ⟨d,hd⟩ := relative_order s p.symm
    let e : Equiv.Perm s ≃ Equiv.Perm s :=
      {toFun := fun u => u.trans d, invFun := fun u => u.trans d.symm,
       left_inv := by intro u; ext; simp, right_inv := by intro u; ext; simp}
    calc ∑ u, obs p u = ∑ u, f (Equiv.Perm.ofSubtype (e u)) := by
           apply sum_congr rfl
           intro u _
           apply localOrder; intro x y
           simp only [Equiv.Perm.ofSubtype_apply_coe]
           exact hd (u x) (u y)
         _ = L := e.sum_comp (fun u => f (Equiv.Perm.ofSubtype u))
  have col (d : Equiv.Perm s) : uniformAverage (fun p => obs p d) =
      uniformAverage (fun p => f p.symm) :=
    uniformAverage_reindex (permuteSlots (Equiv.Perm.ofSubtype d)) (fun p => f p.symm)
  have comp : uniformAverage (fun p => ∑ d, obs p d) =
      ∑ d, uniformAverage (fun p => obs p d) := by
    unfold uniformAverage; rw [Finset.sum_comm,Finset.sum_div]
  simp_rw [row] at comp
  simp only [uniformAverage_const, col,Finset.sum_const,Finset.card_univ,Fintype.card_perm,
    Fintype.card_coe,nsmul_eq_mul] at comp
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero s.card)).2
  simpa only [mul_comm] using comp.symm

inductive GateTree (n : ℕ)
  | leaf (i : Fin n)
  | low (l r : GateTree n)
  | high (l r : GateTree n)

def evaluate {n} (a : Fin n → Fin n) : GateTree n → Fin n
  | .leaf i => a i
  | .low l r => min (evaluate a l) (evaluate a r)
  | .high l r => max (evaluate a l) (evaluate a r)

def sources {n} : GateTree n → Finset (Fin n)
  | .leaf i => {i}
  | .low l r | .high l r => sources l ∪ sources r

/-- Two rank assignments with the same local order give the same winning leaf.
Overlapping branches may read the same physical key. -/
private theorem shared_leaf {n} (s : Finset (Fin n)) (a b : Fin n → Fin n)
    (o : ∀ x y : s, a x < a y ↔ b x < b y) (t : GateTree n) (sub : sources t ⊆ s) :
    ∃ i ∈ sources t, evaluate a t = a i ∧ evaluate b t = b i := by
  induction t with
  | leaf i => exact ⟨i,by simp [sources],rfl,rfl⟩
  | low l r il ir | high l r il ir =>
    obtain ⟨i,hi,ai,bi⟩ := il (Finset.subset_union_left.trans sub)
    obtain ⟨j,hj,aj,bj⟩ := ir (Finset.subset_union_right.trans sub)
    have ii : i ∈ s := sub (Finset.mem_union_left _ hi)
    have jj : j ∈ s := sub (Finset.mem_union_right _ hj)
    have ord := o ⟨i,ii⟩ ⟨j,jj⟩
    change a i < a j ↔ b i < b j at ord
    have li : i ∈ sources l ∪ sources r := mem_union_left _ hi
    have rj : j ∈ sources l ∪ sources r := mem_union_right _ hj
    simp only [evaluate,ai,bi,aj,bj,sources]
    by_cases lt : a i < a j
    · have lt' := ord.mp lt
      first | exact ⟨i,li,min_eq_left lt.le,min_eq_left lt'.le⟩
            | exact ⟨j,rj,max_eq_right lt.le,max_eq_right lt'.le⟩
    · have le := le_of_not_gt lt
      have le' := le_of_not_gt (mt ord.mpr lt)
      first | exact ⟨j,rj,min_eq_right le,min_eq_right le'⟩
            | exact ⟨i,li,max_eq_left le,max_eq_left le'⟩

def localInversion {n} (l r : GateTree n) : ℝ :=
  let s := sources l ∪ sources r
  (∑ d : Equiv.Perm s, if evaluate (Equiv.Perm.ofSubtype d) r <
      evaluate (Equiv.Perm.ofSubtype d) l then (1:ℝ) else 0) / (s.card.factorial : ℝ)

theorem pair_probability {n} (l r : GateTree n) :
    uniformAverage (fun p : RankPlacement n =>
      if evaluate p.symm r < evaluate p.symm l then (1:ℝ) else 0) = localInversion l r := by
  apply local_mean (sources l ∪ sources r)
    (fun a => if evaluate a r < evaluate a l then (1:ℝ) else 0)
  intro a b o
  obtain ⟨i,hi,ai,bi⟩ := shared_leaf _ a b o l subset_union_left
  obtain ⟨j,hj,aj,bj⟩ := shared_leaf _ a b o r subset_union_right
  simp only [ai,bi,aj,bj]
  exact if_congr (o ⟨j,mem_union_right _ hj⟩ ⟨i,mem_union_left _ hi⟩) rfl rfl

def passTree {n} (g : ℕ) (prev : Fin n → GateTree n) (i : Fin n) : GateTree n :=
  if hi : i.val + g < n then .low (prev i) (prev ⟨i.val+g,hi⟩)
  else if g ≤ i.val then .high (prev ⟨i.val-g,lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩) (prev i)
  else prev i

private theorem eval_pass {n} (g : ℕ) (prev : Fin n → GateTree n) (a : Fin n → Fin n)
    (i : Fin n) : evaluate a (passTree g prev i) =
      LargeGapPhysicalPairCost.gate g (fun j => evaluate a (prev j)) i := by
  simp only [passTree,LargeGapPhysicalPairCost.gate]
  split <;> first | rfl | split <;> rfl

private theorem double_bound {n c} (g : ℕ) (prev : Fin n → GateTree n)
    (bound : ∀ i, (sources (prev i)).card ≤ c) (i : Fin n) :
    (sources (passTree g prev i)).card ≤ c+c := by
  unfold passTree
  split
  · exact (card_union_le _ _).trans (Nat.add_le_add (bound _) (bound _))
  · split
    · exact (card_union_le _ _).trans (Nat.add_le_add (bound _) (bound _))
    · exact (bound i).trans (by omega)

def depthTwo {n} (h g : ℕ) (i : Fin n) := passTree g (passTree h .leaf) i

theorem at_most_eight {n} (h g : ℕ) (i j : Fin n) :
    (sources (depthTwo h g i) ∪ sources (depthTwo h g j)).card ≤ 8 := by
  have one (u : Fin n) : (sources (GateTree.leaf u)).card ≤ 1 := by simp [sources]
  exact (card_union_le _ _).trans (Nat.add_le_add
    (double_bound g _ (double_bound h _ one) i) (double_bound g _ (double_bound h _ one) j))

theorem mean_from_local_enumeration {n h g : ℕ} (hg : 0 < g) (gh : g < h)
    (hn : h < n) (half : n ≤ 2*g) :
    let w : HarvestBlockIteration.PositiveWord := [⟨h,by omega⟩,⟨g,hg⟩,⟨1,by decide⟩]
    uniformAverage (fun p : RankPlacement n => ((HarvestOperationalAudit.runWord
      (HarvestOperationalAudit.slots p) w).2 : ℝ)) =
      ((n-h:ℕ):ℝ)+(n-g:ℕ)+n-LargeGapCornerRecords.harmonic n-
        LargeGapRecordChanges.grouped (n-h) (h-g)+
          ∑ ij ∈ gapPositionPairs n 1, localInversion (depthTwo h g ij.1) (depthTwo h g ij.2) := by
  dsimp only
  apply (LargeGapPhysicalPairCost.whole_mean hg gh hn half).trans
  apply congrArg (fun z : ℝ => ((n-h:ℕ):ℝ)+(n-g:ℕ)+n-LargeGapCornerRecords.harmonic n-
    LargeGapRecordChanges.grouped (n-h) (h-g)+z)
  apply sum_congr rfl
  intro ij _
  simpa only [depthTwo,eval_pass,evaluate] using pair_probability
    (depthTwo h g ij.1) (depthTwo h g ij.2)

#print axioms mean_from_local_enumeration

theorem eight_slot_certificate {n h g : ℕ} (hg : 0 < g) (gh : g < h)
    (hn : h < n) (half : n ≤ 2*g) :
    (∀ i j : Fin n, (sources (depthTwo h g i) ∪ sources (depthTwo h g j)).card ≤ 8) ∧
    let w : HarvestBlockIteration.PositiveWord := [⟨h,by omega⟩,⟨g,hg⟩,⟨1,by decide⟩]
    uniformAverage (fun p : RankPlacement n => ((HarvestOperationalAudit.runWord
      (HarvestOperationalAudit.slots p) w).2 : ℝ)) =
      ((n-h:ℕ):ℝ)+(n-g:ℕ)+n-LargeGapCornerRecords.harmonic n-
        LargeGapRecordChanges.grouped (n-h) (h-g)+
          ∑ ij ∈ gapPositionPairs n 1, localInversion (depthTwo h g ij.1) (depthTwo h g ij.2) :=
  ⟨at_most_eight h g,mean_from_local_enumeration hg gh hn half⟩

end
end Shellsort.LocalRelativeOrderMean
