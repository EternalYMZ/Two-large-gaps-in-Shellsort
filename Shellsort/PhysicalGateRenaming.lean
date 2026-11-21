import Shellsort.LocalGatePivotCounts

namespace Shellsort.PhysicalGateRenaming
open Finset LocalRelativeOrderMean
noncomputable section

def rename {m n} (f : Fin m → Fin n) : GateTree m → GateTree n
  | .leaf i => .leaf (f i)
  | .low l r => .low (rename f l) (rename f r)
  | .high l r => .high (rename f l) (rename f r)

theorem sources_rename {m n} (f : Fin m → Fin n) (t : GateTree m) :
    sources (rename f t) = (sources t).image f := by
  induction t <;> simp_all [rename,sources,Finset.image_union]

private theorem common_leaf {m n} (s : Finset (Fin m)) (f : Fin m → Fin n)
    (a : Fin m → Fin m) (b : Fin n → Fin n)
    (order : ∀ i ∈ s, ∀ j ∈ s, a i < a j ↔ b (f i) < b (f j))
    (t : GateTree m) (sub : sources t ⊆ s) :
    ∃ i ∈ sources t, evaluate a t = a i ∧ evaluate b (rename f t) = b (f i) := by
  induction t with
  | leaf i => exact ⟨i,by simp [sources],rfl,rfl⟩
  | low l r il ir | high l r il ir =>
    obtain ⟨i,hi,ai,bi⟩ := il (subset_union_left.trans sub)
    obtain ⟨j,hj,aj,bj⟩ := ir (subset_union_right.trans sub)
    have li : i ∈ sources l ∪ sources r := mem_union_left _ hi
    have rj : j ∈ sources l ∪ sources r := mem_union_right _ hj
    have ord := order i (sub li) j (sub rj)
    simp only [rename,evaluate,ai,bi,aj,bj,sources]
    by_cases lt : a i < a j
    · have lt' := ord.mp lt
      first | exact ⟨i,li,min_eq_left lt.le,min_eq_left lt'.le⟩
            | exact ⟨j,rj,max_eq_right lt.le,max_eq_right lt'.le⟩
    · have le := le_of_not_gt lt
      have le' := le_of_not_gt (mt ord.mpr lt)
      first | exact ⟨j,rj,min_eq_right le,min_eq_right le'⟩
            | exact ⟨i,li,max_eq_left le,max_eq_left le'⟩

/-- Only leaves actually used need distinct names. Unused labels may collide,
and the physical and prototype arrays may have different sizes. -/
theorem rename_inversion {m n} (f : Fin m → Fin n) (l r : GateTree m)
    (inj : Set.InjOn f (↑(sources l ∪ sources r) : Set (Fin m))) :
    localInversion (rename f l) (rename f r) = localInversion l r := by
  classical
  let s := sources l ∪ sources r
  let u := sources (rename f l) ∪ sources (rename f r)
  have ue : u = s.image f := by simp [s,u,sources_rename,image_union]
  let sf : s → u := fun i => ⟨f i, by rw [ue]; exact mem_image_of_mem _ i.property⟩
  have bij : Function.Bijective sf := by
    constructor
    · intro x y e
      exact Subtype.ext (inj x.property y.property (congrArg Subtype.val e))
    · intro y
      obtain ⟨x,hx,eq⟩ := mem_image.mp (ue ▸ y.property : y.val ∈ s.image f)
      exact ⟨⟨x,hx⟩,Subtype.ext eq⟩
  let e : s ≃ u := Equiv.ofBijective sf bij
  have card : s.card = u.card := by simpa using Fintype.card_congr e
  let o : s ≃o u := (s.orderIsoOfFin rfl).symm.trans (u.orderIsoOfFin card.symm)
  let reindex : Equiv.Perm s ≃ Equiv.Perm u :=
    {toFun := fun d => (e.symm.trans d).trans o.toEquiv,
     invFun := fun d => (e.trans d).trans o.symm.toEquiv,
     left_inv := by intro d; ext; simp,
     right_inv := by intro d; ext; simp}
  let event {N : ℕ} (v w : GateTree N) (p : Fin N → Fin N) :=
    if evaluate p w < evaluate p v then (1:ℝ) else 0
  let F := fun d : Equiv.Perm u =>
    event (rename f l) (rename f r) (Equiv.Perm.ofSubtype d)
  have same (d : Equiv.Perm s) : F (reindex d) =
      event l r (Equiv.Perm.ofSubtype d) := by
    let a := Equiv.Perm.ofSubtype d
    let b := Equiv.Perm.ofSubtype (reindex d)
    have order (i) (hi : i ∈ s) (j) (hj : j ∈ s) : a i < a j ↔ b (f i) < b (f j) := by
      let x : s := ⟨i,hi⟩
      let y : s := ⟨j,hj⟩
      change (Equiv.Perm.ofSubtype d) x < (Equiv.Perm.ofSubtype d) y ↔
        (Equiv.Perm.ofSubtype (reindex d)) (e x) < (Equiv.Perm.ofSubtype (reindex d)) (e y)
      simp only [Equiv.Perm.ofSubtype_apply_coe]
      change d x < d y ↔ o (d (e.symm (e x))) < o (d (e.symm (e y)))
      simp
    obtain ⟨x,hx,ax,bx⟩ := common_leaf s f a b order l subset_union_left
    obtain ⟨y,hy,ay,by'⟩ := common_leaf s f a b order r subset_union_right
    change (if evaluate b (rename f r) < evaluate b (rename f l) then (1:ℝ) else 0) =
      (if evaluate a r < evaluate a l then (1:ℝ) else 0)
    rw [ax,ay,bx,by']
    exact if_congr (order y (mem_union_right _ hy) x (mem_union_left _ hx)).symm rfl rfl
  change (∑ d : Equiv.Perm u, F d) / (u.card.factorial:ℝ) =
    (∑ d : Equiv.Perm s, event l r (Equiv.Perm.ofSubtype d)) / (s.card.factorial:ℝ)
  rw [← reindex.sum_comp F,← card]
  simp_rw [same]

#print axioms rename_inversion
end
end Shellsort.PhysicalGateRenaming
