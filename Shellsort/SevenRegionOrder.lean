import Shellsort.PhysicalSevenSegments

namespace Shellsort.SevenRegionOrder
open Finset PhysicalSevenSegments SevenSegmentBaseline
noncomputable section
set_option maxHeartbeats 2000000

def start (n h g : ℕ) : Fin 7 → ℕ :=
  let x := min (n-h) (h-g)
  let y := max (n-h) (h-g)
  ![0,x,y,n-g,g,g+x,g+y]

def stop (n h g : ℕ) : Fin 7 → ℕ :=
  let x := min (n-h) (h-g)
  let y := max (n-h) (h-g)
  ![x,y,n-g,g,g+x,g+y,n]

private theorem bounds {n h g : ℕ} (gh : g<h) (hn : h<n) (half : n ≤ 2*g) (t : Fin 7) :
    start n h g t ≤ stop n h g t ∧ stop n h g t ≤ n := by
  fin_cases t <;> norm_num [start,stop] <;> omega

private theorem member {n h g i : ℕ} (gh : g<h) (hn : h<n) (half : n ≤ 2*g)
    (hi : i<n) (t : Fin 7) : region n h g i=t ↔ start n h g t ≤ i ∧ i<stop n h g t := by
  fin_cases t <;> by_cases l : i<n-g <;> by_cases m : i<g <;>
    by_cases a : i<n-h <;> by_cases b : h-g ≤ i <;>
    by_cases c : i-g<n-h <;> by_cases d : h-g ≤ i-g <;>
    norm_num [region,tag,start,stop,l,m,a,b,c,d] <;> omega

theorem region_monotone {n h g : ℕ} (gh : g<h) (hn : h<n) (half : n ≤ 2*g) :
    Monotone (fun i : Fin n => region n h g i.val) := by
  intro i j ij
  generalize eq1 : region n h g i.val = t
  generalize eq2 : region n h g j.val = u
  obtain ⟨il,ir⟩ := (member gh hn half i.isLt t).mp eq1
  obtain ⟨jl,jr⟩ := (member gh hn half j.isLt u).mp eq2
  have le : i.val ≤ j.val := ij
  fin_cases t <;> fin_cases u <;> norm_num [start,stop] at * <;> omega

def span (n h g : ℕ) (t : Fin 7) : ℝ := ((stop n h g t - start n h g t : ℕ):ℝ)

theorem one_sum {n h g : ℕ} (gh : g<h) (hn : h<n) (half : n ≤ 2*g) (f : Fin 7 → ℝ) :
    ∑ i : Fin n, f (region n h g i.val) = ∑ t : Fin 7, span n h g t * f t := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f (region n h g i))]
  rw [← Finset.sum_fiberwise' (range n) (region n h g) f]
  apply sum_congr rfl
  intro t _
  have inter : (range n).filter (fun i => region n h g i=t) =
      Ico (start n h g t) (stop n h g t) := by
    ext i
    have sb := bounds gh hn half t
    simp only [mem_filter,mem_range,mem_Ico]
    by_cases hi : i<n
    · simp [hi,member gh hn half hi]
    · constructor <;> intro hu <;> omega
  rw [inter]; simp [span]

theorem lengths {n h g : ℕ} (gh : g<h) (hn : h<n) (half : n ≤ 2*g) :
    let a : ℝ := (n-h:ℕ)
    let b : ℝ := (n-g:ℕ)
    span n h g = if h-g<n-h then widths (b-a) (2*a-b) (n-2*b)
      else widths a (b-2*a) (n-2*b) := by
  dsimp only
  funext t
  have hg : g ≤ h := by omega
  have hn' : h ≤ n := by omega
  have gn : g ≤ n := by omega
  by_cases case1 : h-g<n-h
  · have le : h-g ≤ n-h := by omega
    fin_cases t <;> norm_num [span,start,stop,widths,case1,min_eq_right le,max_eq_left le]
      <;> first | omega | (simp (disch := omega) only [Nat.cast_sub,Nat.cast_add] <;> ring)
  · have le : n-h ≤ h-g := by omega
    fin_cases t <;> norm_num [span,start,stop,widths,case1,min_eq_left le,max_eq_right le]
      <;> first | omega | (simp (disch := omega) only [Nat.cast_sub,Nat.cast_add] <;> ring)

#print axioms one_sum
end
end Shellsort.SevenRegionOrder
