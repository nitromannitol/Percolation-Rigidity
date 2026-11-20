import Rigidity.Percolation.SlabTriadicPartition

/-!
# Nearest-neighbor connectivity in lattice rectangles

Every two vertices of an integer-coordinate rectangle are connected by a
nearest-neighbor path inside the rectangle.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

/-- The integer points in a half-open coordinate rectangle. -/
def latticeRectangle {d : ℕ} (lo hi : Vertex d) : Set (Vertex d) :=
  {x | ∀ i, lo i ≤ x i ∧ x i < hi i}

/-- Any two vertices of a lattice rectangle are connected there when all
bonds are open. -/
theorem reachable_allOpen_latticeRectangle {d : ℕ} (lo hi : Vertex d)
    {x y : Vertex d} (hx : x ∈ latticeRectangle lo hi) (hy : y ∈ latticeRectangle lo hi) :
    (openIn (allOpen d) (latticeRectangle lo hi)).Reachable x y := by
  classical
  have hlo : lo ∈ latticeRectangle lo hi := fun i => ⟨le_rfl, (hx i).1.trans_lt (hx i).2⟩
  have hcorner : ∀ z ∈ latticeRectangle lo hi,
      (openIn (allOpen d) (latticeRectangle lo hi)).Reachable z lo := by
    suffices H : ∀ m : ℕ, ∀ z ∈ latticeRectangle lo hi,
        (∑ i, (z i - lo i).toNat) = m →
        (openIn (allOpen d) (latticeRectangle lo hi)).Reachable z lo from fun z hz => H _ z hz rfl
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro z hz hm
      by_cases hzero : z = lo
      · subst z
        exact SimpleGraph.Reachable.refl lo
      · obtain ⟨i, hcoord⟩ : ∃ i, lo i < z i := by
          by_contra h
          push Not at h
          apply hzero
          funext i
          exact le_antisymm (h i) (hz i).1
        let w : Vertex d := Function.update z i (z i - 1)
        have hwi : w i = z i - 1 := by simp only [w, Function.update_self]
        have hwj : ∀ j, j ≠ i → w j = z j := by
          intro j hj
          exact Function.update_of_ne hj _ _
        have hw : w ∈ latticeRectangle lo hi := by
          intro j
          by_cases hj : j = i
          · subst j
            rw [hwi]
            have hzj := hz i
            omega
          · rw [hwj j hj]
            exact hz j
        have hstep : (nearestNeighborGraph d).Adj z w := by
          refine ⟨i, Or.inr ?_⟩
          funext j
          by_cases hj : j = i
          · subst j
            simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same, hwi]
            omega
          · simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_of_ne hj, add_zero, hwj j hj]
        have hadj : (openIn (allOpen d) (latticeRectangle lo hi)).Adj z w :=
          ⟨by simpa only [openGraph_allOpen] using hstep, hz, hw⟩
        have hlt : ∑ j, (w j - lo j).toNat < m := by
          rw [← hm]
          apply Finset.sum_lt_sum
          · intro j _
            by_cases hj : j = i
            · subst j
              rw [hwi]
              apply Int.toNat_le_toNat
              omega
            · rw [hwj j hj]
          · refine ⟨i, Finset.mem_univ _, ?_⟩
            rw [hwi]
            omega
        exact hadj.reachable.trans (ih _ hlt w hw rfl)
  exact (hcorner x hx).trans (hcorner y hy).symm

/-- Every complete cube slab is a half-open coordinate rectangle. -/
theorem IntegerCube.slab_eq_latticeRectangle {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) (width k : ℕ) (hfull : (k + 1) * width ≤ Q.size) :
    Q.slab j width k = latticeRectangle
      (Function.update Q.corner j (Q.corner j + ((k * width : ℕ) : ℤ)))
      (Function.update (fun i => Q.corner i + (Q.size : ℤ)) j
        (Q.corner j + (((k + 1) * width : ℕ) : ℤ))) := by
  classical
  have hfull' : (((k + 1) * width : ℕ) : ℤ) ≤ (Q.size : ℤ) := by exact_mod_cast hfull
  have hk : (0 : ℤ) ≤ ((k * width : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le _
  ext x
  constructor
  · intro hx i
    by_cases hij : i = j
    · subst i
      simpa only [Function.update_self] using hx.2
    · simpa only [Function.update_of_ne hij] using (Q.mem_vertices x).mp hx.1 i
  · intro hx
    have hxj := hx j
    simp only [Function.update_self] at hxj
    refine ⟨?_, hxj⟩
    rw [Q.mem_vertices]
    intro i
    by_cases hij : i = j
    · subst i
      constructor <;> omega
    · simpa only [Function.update_of_ne hij] using hx i

/-- Vertices in a complete cube slab are connected when all bonds are open. -/
theorem IntegerCube.reachable_allOpen_slab {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) (width k : ℕ) (hfull : (k + 1) * width ≤ Q.size)
    {x y : Vertex d} (hx : x ∈ Q.slab j width k) (hy : y ∈ Q.slab j width k) :
    (openIn (allOpen d) (Q.slab j width k)).Reachable x y := by
  rw [Q.slab_eq_latticeRectangle j width k hfull] at hx hy ⊢
  exact reachable_allOpen_latticeRectangle _ _ hx hy

/-- The fully open bond model satisfies uniform cube-slab connectivity. -/
theorem uniformCubeSlabConnectivity_one (d : ℕ) : UniformCubeSlabConnectivity d 1 := by
  refine ⟨1, by omega, 1, by norm_num, ?_⟩
  intro Q j k hfull x hx y hy
  have hreach := Q.reachable_allOpen_slab j 1 k hfull hx hy
  rw [latticeBondLaw_one, measureReal_def,
    Measure.dirac_apply' _ (measurableSet_openIn_reachable (Q.slab j 1 k) x y)]
  have hm : allOpen d ∈ {ω | (openIn ω (Q.slab j 1 k)).Reachable x y} := hreach
  rw [Set.indicator_of_mem hm]
  norm_num

end Rigidity.Percolation
