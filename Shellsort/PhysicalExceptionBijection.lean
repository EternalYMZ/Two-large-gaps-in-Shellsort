import Shellsort.PhysicalSeparatedEdges

namespace Shellsort.PhysicalExceptionBijection
open PhysicalOverlapClassification ThreePassSeparatedLedger Finset
noncomputable section
set_option maxHeartbeats 1000000

abbrev Domain (n h g : ℕ) := Fin (n-g) ⊕ (Fin (n-h) × Fin 4)

def pairNat (n h g : ℕ) : Domain n h g → ℕ × ℕ
  | .inl i => (i.val,i.val+g)
  | .inr (i,t) =>
    let j := i.val+(h-g)
    if t.val=0 then (i.val,j) else if t.val=1 then (i.val,j+g)
    else if t.val=2 then (j,i.val+g) else (i.val+g,j+g)

private theorem bounds {n h g : ℕ} (hg : 0<g) (gh : g<h) (hn : h<n) (half : n ≤ 2*g)
    (u : Domain n h g) : (pairNat n h g u).1 < (pairNat n h g u).2 ∧ (pairNat n h g u).2<n := by
  rcases u with i | ⟨i,t⟩ <;> have hi := i.isLt
  · simp only [pairNat]; omega
  · fin_cases t <;> norm_num [pairNat] <;> omega

def pair {n h g : ℕ} (hg : 0<g) (gh : g<h) (hn : h<n) (half : n ≤ 2*g)
    (u : Domain n h g) : Fin n × Fin n :=
  let a := pairNat n h g u
  let e := bounds hg gh hn half u
  (⟨a.1,e.1.trans e.2⟩,⟨a.2,e.2⟩)

private theorem injective {n h g : ℕ} (hg : 0<g) (gh : g<h) (hn : h<n) (half : n ≤ 2*g) :
    Function.Injective (pair hg gh hn half) := by
  intro u v same
  have first := congrArg (fun z : Fin n × Fin n => z.1.val) same
  have second := congrArg (fun z : Fin n × Fin n => z.2.val) same
  rcases u with i|⟨i,t⟩ <;> rcases v with j|⟨j,k⟩ <;> have hi := i.isLt <;> have hj := j.isLt
  all_goals try fin_cases t
  all_goals try fin_cases k
  all_goals norm_num [pair,pairNat,Fin.ext_iff] at first second ⊢ <;> omega

private theorem mem_iff {n h g : ℕ} (hg : 0<g) (gh : g<h) (hn : h<n) (half : n ≤ 2*g)
    (u v : Fin n) :
    (u,v) ∈ overlapping n h g ↔
    u.val < v.val ∧ (u.val+g<n ∨ g ≤ u.val) ∧ (v.val+g<n ∨ g ≤ v.val) ∧
    (let x := if g ≤ u.val then u.val-g else u.val
     let y := if g ≤ v.val then v.val-g else v.val
     x=y ∨ y+g=x+h ∨ x+g=y+h) := by
  simp only [overlapping,gapPositionPairs,mem_filter,mem_univ,true_and,Nat.mod_one,and_true,
    exceptional,base,Fin.ext_iff,Fin.lt_def]
  by_cases a : g ≤ u.val <;> by_cases b : g ≤ v.val <;> simp [a,b]

private theorem belongs {n h g : ℕ} (hg : 0<g) (gh : g<h) (hn : h<n) (half : n ≤ 2*g)
    (u : Domain n h g) : pair hg gh hn half u ∈ overlapping n h g := by
  rw [← Prod.eta (pair hg gh hn half u),mem_iff hg gh hn half]
  rcases u with i|⟨i,t⟩ <;> have hi := i.isLt
  · have low : ¬ (g ≤ i.val) := by omega
    norm_num [pair,pairNat,low]; omega
  · have low : ¬ (g ≤ i.val) := by omega
    have low' : ¬(g ≤ i.val+(h-g)) := by omega
    fin_cases t <;> norm_num [pair,pairNat,low,low'] <;> omega

/-- Decode an ordered exceptional pair according to which half of the array
its two slots occupy. The shared-column case is the diagonal across halves. -/
private theorem onto {n h g : ℕ} (hg : 0<g) (gh : g<h) (hn : h<n) (half : n ≤ 2*g)
    (u v : Fin n) (inside : (u,v) ∈ overlapping n h g) :
    ∃ z : Domain n h g, pair hg gh hn half z = (u,v) := by
  have m := (mem_iff hg gh hn half u v).mp inside
  try dsimp only at m
  have hu := u.isLt
  have hv := v.isLt
  have make (z : Domain n h g) (l : (pairNat n h g z).1=u.val)
      (r : (pairNat n h g z).2=v.val) : ∃ z, pair hg gh hn half z = (u,v) :=
    ⟨z,Prod.ext (Fin.ext l) (Fin.ext r)⟩
  by_cases uh : g ≤ u.val <;> by_cases vh : g ≤ v.val <;> simp only [uh,vh,ite_true,ite_false,
    or_false,or_true,true_and,and_true] at m
  · apply make (.inr (⟨u.val-g,by omega⟩,3)) <;> norm_num [pairNat] <;> omega
  · omega
  · by_cases eq : u.val+g=v.val
    · exact make (.inl ⟨u.val,by omega⟩) rfl eq
    · by_cases dir : u.val+h=v.val
      · apply make (.inr (⟨u.val,by omega⟩,1)) <;> norm_num [pairNat] <;> omega
      · apply make (.inr (⟨v.val-g,by omega⟩,2)) <;> norm_num [pairNat] <;> omega
  ·
    apply make (.inr (⟨u.val,by omega⟩,0)) <;> norm_num [pairNat] <;> omega

private def bij {n h g : ℕ} (hg : 0<g) (gh : g<h) (hn : h<n) (half : n ≤ 2*g) :
    Domain n h g ≃ overlapping n h g :=
  Equiv.ofBijective (fun z => ⟨pair hg gh hn half z,belongs hg gh hn half z⟩)
    ⟨fun _ _ e => injective hg gh hn half (congrArg Subtype.val e),
     fun ⟨⟨a,b⟩,mem⟩ => by
       obtain ⟨z,e⟩ := onto hg gh hn half a b mem
       exact ⟨z,Subtype.ext e⟩⟩

theorem sum_columns {n h g : ℕ} (hg : 0<g) (gh : g<h) (hn : h<n) (half : n ≤ 2*g)
    (cost : Fin n × Fin n → ℝ) :
    ∑ ij ∈ overlapping n h g, cost ij =
      (∑ i : Fin (n-g), cost (pair hg gh hn half (.inl i))) +
      ∑ i : Fin (n-h), ∑ t : Fin 4, cost (pair hg gh hn half (.inr (i,t))) := by
  rw [← Finset.sum_attach]
  change (∑ z : overlapping n h g, cost (z:Fin n × Fin n)) = _
  rw [← (bij hg gh hn half).sum_comp (fun z => cost (z:Fin n × Fin n))]
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  rfl

#print axioms sum_columns
end
end Shellsort.PhysicalExceptionBijection
