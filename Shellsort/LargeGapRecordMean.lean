import Shellsort.LargeGapPrefixRecords
import Shellsort.GapInversions

/-! Exact probability of a new prefix minimum at a slot of an executed large-gap word. -/
noncomputable section
namespace Shellsort.LargeGapRecordMean
open Finset HarvestOperationalAudit LargeGapPrefixRecords

def lowest {n : ℕ} (S : Finset (Fin n)) (p : RankPlacement n) (i : Fin n) : Prop :=
  ∀ j ∈ S, p.symm i ≤ p.symm j

def indicator (P : Prop) : ℝ := by classical exact if P then 1 else 0

private theorem swap_mem {n : ℕ} {S : Finset (Fin n)} {i j x : Fin n}
    (hi : i ∈ S) (hj : j ∈ S) (hx : x ∈ S) : Equiv.swap i j x ∈ S := by
  by_cases a : x = i
  · simpa [a] using hj
  by_cases b : x = j
  · simpa [b] using hi
  rwa [Equiv.swap_apply_of_ne_of_ne a b]

private theorem symmetry {n : ℕ} (S : Finset (Fin n)) (i j : Fin n)
    (hi : i ∈ S) (hj : j ∈ S) :
    uniformAverage (fun p => indicator (lowest S p i)) =
    uniformAverage (fun p => indicator (lowest S p j)) := by
  rw [← uniformAverage_reindex (swapPositionsEquiv i j) (fun p => indicator (lowest S p i))]
  congr 1; funext p
  congr 1; apply propext
  constructor
  · intro h x hx
    have e := h (Equiv.swap i j x) (swap_mem hi hj hx)
    simpa [swapPositionsEquiv] using e
  · intro h x hx
    have e := h (Equiv.swap i j x) (swap_mem hi hj hx)
    simpa [swapPositionsEquiv] using e

private theorem unique_lowest {n : ℕ} {S : Finset (Fin n)} {p : RankPlacement n}
    {i j : Fin n} (hi : i ∈ S) (hj : j ∈ S) (mi : lowest S p i) (mj : lowest S p j) :
    i = j := p.symm.injective (le_antisymm (mi j hj) (mj i hi))

private theorem sum_sub {n : ℕ} (p : RankPlacement n) (A B : Finset (Fin n))
    (ab : A ⊆ B) (i : Fin n) (hi : i ∈ B) (mi : lowest B p i) :
    (∑ j ∈ A, indicator (lowest B p j)) = indicator (i ∈ A) := by
  classical
  by_cases ha : i ∈ A
  · rw [Finset.sum_eq_single_of_mem i ha]
    · simp [indicator,ha,mi]
    · intro j hj ne
      exact if_neg (fun m : lowest B p j => ne (unique_lowest (ab hj) hi m mi))
  · rw [Finset.sum_eq_zero]
    · simp [indicator,ha]
    · intro j hj
      have no (m : lowest B p j) := ha (unique_lowest (ab hj) hi m mi ▸ hj)
      exact if_neg no

private theorem avg_sum {n : ℕ} (S : Finset (Fin n)) (f : Fin n → RankPlacement n → ℝ) :
    uniformAverage (fun p => ∑ i ∈ S, f i p) = ∑ i ∈ S, uniformAverage (f i) := by
  unfold uniformAverage
  rw [Finset.sum_comm, Finset.sum_div]

private theorem single_mean {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    uniformAverage (fun p => indicator (lowest S p i)) = 1/(S.card : ℝ) := by
  classical
  have one (p : RankPlacement n) : (∑ j ∈ S, indicator (lowest S p j)) = 1 := by
    obtain ⟨m,hm,hs⟩ := S.exists_min_image p.symm ⟨i,hi⟩
    rw [sum_sub p S S (Subset.rfl) m hm hs]
    simp [indicator,hm]
  have e := congrArg (uniformAverage (n := n)) (funext one)
  rw [avg_sum,uniformAverage_const] at e
  rw [Finset.sum_congr rfl (fun j hj => symmetry S j i hj hi)] at e
  simp only [Finset.sum_const, nsmul_eq_mul] at e
  apply (eq_div_iff (by exact_mod_cast Finset.card_ne_zero.mpr ⟨i,hi⟩)).mpr
  linarith

def hitSet {n : ℕ} (S : Finset (Fin n)) (p : RankPlacement n) (t : ℕ) : Prop :=
  ∃ i ∈ S, (p.symm i).val < t

private theorem average_new {n : ℕ} (A B : Finset (Fin n)) (hab : A ⊆ B) :
    uniformAverage (fun p => indicator (∃ t, hitSet B p t ∧ ¬hitSet A p t)) =
      ((B \ A).card : ℝ)/(B.card : ℝ) := by
  classical
  by_cases hB : B.Nonempty
  · have e (p : RankPlacement n) : indicator (∃ t, hitSet B p t ∧ ¬hitSet A p t) =
          ∑ j ∈ B \ A, indicator (lowest B p j) := by
      obtain ⟨m,hm,hs⟩ := B.exists_min_image p.symm hB
      rw [sum_sub p _ B Finset.sdiff_subset _ hm hs]
      congr 1; apply propext
      constructor
      · rintro ⟨t,⟨j,hj,ht⟩,none⟩
        exact Finset.mem_sdiff.mpr ⟨hm,fun ma => none ⟨m,ma,lt_of_le_of_lt (hs j hj) ht⟩⟩
      · intro mm
        refine ⟨(p.symm m).val+1,⟨m,hm,by omega⟩,?_⟩
        rintro ⟨j,hj,ht⟩
        have lo := hs j (hab hj)
        have eq : p.symm m = p.symm j := Fin.ext (by change (p.symm m).val ≤ (p.symm j).val at lo; omega)
        exact (Finset.mem_sdiff.mp mm).2 (p.symm.injective eq ▸ hj)
    rw [funext e,avg_sum,Finset.sum_congr rfl (fun j hj => single_mean B j (Finset.sdiff_subset hj))]
    simp [div_eq_mul_inv]
  · have e := Finset.not_nonempty_iff_eq_empty.mp hB
    simp [e,hitSet,indicator,uniformAverage_const]

def rawSet (n : ℕ) (gs : List ℕ) (l : ℕ) : Finset (Fin n) := by
  classical exact Finset.univ.filter fun i => seen n (min l (gs.headD n)) i.val gs

private theorem seen_mono {n l k i : ℕ} (lk : l ≤ k) (gs : List ℕ) :
    seen n l i gs → seen n k i gs := by
  induction gs with
  | nil => exact fun h => lt_of_lt_of_le h lk
  | cons h gs ih =>
    rintro (old | ⟨b,c,d⟩)
    · exact Or.inl (ih old)
    · exact Or.inr ⟨b,c,by omega⟩

def record {n : ℕ} (a : Vector (Fin n) n) (j : Fin n) : Prop :=
  ∀ i : Fin n, i < j → a[j.val] < a[i.val]

private def arrayHit {n : ℕ} (a : Vector (Fin n) n) (l t : ℕ) : Prop :=
  ∃ i : Fin n, i.val < l ∧ (a[i.val]).val < t

private theorem record_hit {n : ℕ} (a : Vector (Fin n) n) (j : Fin n) :
    record a j ↔ ∃ t, arrayHit a (j.val+1) t ∧ ¬arrayHit a j.val t := by
  constructor
  · intro h
    refine ⟨a[j.val].val+1, ⟨j,by omega,by omega⟩, ?_⟩
    rintro ⟨i,hi,ht⟩
    have e := h i hi
    change a[j.val].val < a[i.val].val at e
    change Nat.lt (a[i.val]).val ((a[j.val]).val+1) at ht
    exact (not_lt_of_ge (show (a[j.val]).val+1 ≤ (a[i.val]).val from e)) ht
  · rintro ⟨t,⟨i,hi,ht⟩,no⟩ k hk
    have hji : i=j := by
      apply Fin.ext; by_contra! bad
      exact no ⟨i,by omega,ht⟩
    subst i
    have lower : ¬a[k.val].val < t := fun h => no ⟨k,hk,h⟩
    change a[j.val].val < a[k.val].val
    omega

theorem executed_record_probability {n : ℕ} (w : HarvestBlockIteration.PositiveWord)
    (asc : (w.map Subtype.val).reverse.Pairwise (· < ·))
    (large : ∀ h ∈ w, h.val < n ∧ n ≤ 2*h.val) (j : Fin n) :
    let gs := (w.map Subtype.val).reverse
    uniformAverage (fun p : RankPlacement n =>
      indicator (record (runWord (slots p) w).1 j)) =
      ((rawSet n gs (j.val+1) \ rawSet n gs j.val).card : ℝ) /
        ((rawSet n gs (j.val+1)).card : ℝ) := by
  classical
  let gs := (w.map Subtype.val).reverse
  have transfer (p : RankPlacement n) (l t : ℕ) :
    arrayHit (runWord (slots p) w).1 l t ↔ hitSet (rawSet n gs l) p t := by
    simpa [arrayHit,hitSet,rawSet,gs] using executed_prefix p w asc large l t
  have sub : rawSet n gs j.val ⊆ rawSet n gs (j.val+1) := by
    intro i hi
    simpa only [rawSet,Finset.mem_filter,Finset.mem_univ,true_and] using
      (seen_mono (n := n) (i := i.val) (min_le_min_right (gs.headD n) (Nat.le_succ j.val)) gs
        (by simpa [rawSet] using hi))
  simpa only [record_hit, transfer] using
    (average_new (rawSet n gs j.val) (rawSet n gs (j.val+1)) sub)

#print axioms executed_record_probability
end Shellsort.LargeGapRecordMean
