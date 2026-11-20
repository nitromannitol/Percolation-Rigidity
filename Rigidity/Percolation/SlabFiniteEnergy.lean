import Rigidity.Percolation.SlabRectangularConnectivity
import Rigidity.Percolation.TargetConnectionHarris

/-!
# Positive probability of finite open paths

Every deterministic nearest-neighbor path has positive probability to be open
when the bond density is positive. This applies to any fixed complete slab.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- Reachability in a fixed region is increasing as bonds are opened. -/
theorem isUpperSet_reachable_openIn {d : ℕ} (B : Set (Vertex d)) (x y : Vertex d) :
    IsUpperSet {ω : Configuration d | (openIn ω B).Reachable x y} := by
  intro ω η hωη hω
  exact hω.mono (openIn_mono_configuration hωη B)

/-- Adding a prescribed nearest-neighbor bond to an open connection costs at
most one factor of the bond density. -/
theorem mul_measureReal_reachable_le_of_adj {d : ℕ} (p : unitInterval)
    (B : Set (Vertex d)) {u v w : Vertex d} (hu : u ∈ B) (hv : v ∈ B)
    (hnn : (nearestNeighborGraph d).Adj u v) :
    (p : ℝ) * (latticeBondLaw d p).real {ω | (openIn ω B).Reachable v w} ≤
      (latticeBondLaw d p).real {ω | (openIn ω B).Reachable u w} := by
  let e := bondOfAdjacent hnn
  let A : Set (Configuration d) := {ω | ω e = true}
  let C : Set (Configuration d) := {ω | (openIn ω B).Reachable v w}
  have hA : MeasurableSet A := (measurableSet_singleton true).preimage (measurable_pi_apply e)
  have hAupper : IsUpperSet A := by
    intro ω η hωη hω
    have h := hωη e
    change ω e = true at hω
    rw [hω] at h
    cases he : η e with
    | false => exact ((by decide : ¬ true ≤ false) (he ▸ h)).elim
    | true => exact he
  have hAprob : (latticeBondLaw d p).real A = p := by
    rw [measureReal_def, latticeBondLaw_open, ENNReal.toReal_ofReal p.property.1]
  have hinter : (latticeBondLaw d p).real A * (latticeBondLaw d p).real C ≤
      (latticeBondLaw d p).real (A ∩ C) :=
    LatticeProb.infinitePi_harris_bool (fun _ : Bond d => bernoulliMeasure true false p)
      hAupper (isUpperSet_reachable_openIn B v w) hA (measurableSet_openIn_reachable B v w)
  have hsubset : A ∩ C ⊆ {ω | (openIn ω B).Reachable u w} := by
    rintro ω ⟨hopen, hrest⟩
    have hstep : (openIn ω B).Adj u v :=
      ⟨(openGraph_adj_iff ω u v).mpr ⟨hnn, hopen⟩, hu, hv⟩
    exact hstep.reachable.trans hrest
  rw [← hAprob]
  exact hinter.trans (measureReal_mono hsubset (measure_ne_top _ _))

/-- A deterministic path of `n` edges is open with probability at least
`p ^ n`, allowing for repeated bonds. -/
theorem pow_length_le_measureReal_reachable_openIn {d : ℕ} (p : unitInterval)
    (B : Set (Vertex d)) {x y : Vertex d} (walk : (openIn (allOpen d) B).Walk x y) :
    (p : ℝ) ^ walk.length ≤ (latticeBondLaw d p).real {ω | (openIn ω B).Reachable x y} := by
  induction walk with
  | @nil u =>
    have heq : {ω : Configuration d | (openIn ω B).Reachable u u} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact SimpleGraph.Reachable.refl u
    simp only [SimpleGraph.Walk.length_nil, pow_zero, heq, probReal_univ, le_refl]
  | @cons u v w huv walk ih =>
    have hnn : (nearestNeighborGraph d).Adj u v := by
      simpa only [openGraph_allOpen] using huv.1
    calc
      (p : ℝ) ^ (SimpleGraph.Walk.cons huv walk).length = (p : ℝ) * (p : ℝ) ^ walk.length := by
        simp only [SimpleGraph.Walk.length_cons, pow_succ, mul_comm]
      _ ≤ (p : ℝ) * (latticeBondLaw d p).real {ω | (openIn ω B).Reachable v w} :=
        mul_le_mul_of_nonneg_left ih p.property.1
      _ ≤ _ := mul_measureReal_reachable_le_of_adj p B huv.2.1 huv.2.2 hnn

/-- A connection available when all bonds are open has positive probability
at every positive bond density. -/
theorem measureReal_reachable_openIn_pos_of_allOpen {d : ℕ} (p : unitInterval)
    (hp : 0 < (p : ℝ)) (B : Set (Vertex d)) {x y : Vertex d}
    (hpath : (openIn (allOpen d) B).Reachable x y) :
    0 < (latticeBondLaw d p).real {ω | (openIn ω B).Reachable x y} := by
  obtain ⟨walk⟩ := hpath
  exact (pow_pos hp walk.length).trans_le (pow_length_le_measureReal_reachable_openIn p B walk)

/-- Every pair of vertices in a fixed complete cube slab has positive
connection probability at positive bond density. -/
theorem IntegerCube.measureReal_reachable_slab_pos {d : ℕ} (p : unitInterval)
    (hp : 0 < (p : ℝ)) (Q : IntegerCube d) (j : Fin d) (width k : ℕ)
    (hfull : (k + 1) * width ≤ Q.size) {x y : Vertex d}
    (hx : x ∈ Q.slab j width k) (hy : y ∈ Q.slab j width k) :
    0 < (latticeBondLaw d p).real {ω | (openIn ω (Q.slab j width k)).Reachable x y} :=
  measureReal_reachable_openIn_pos_of_allOpen p hp (Q.slab j width k)
    (Q.reachable_allOpen_slab j width k hfull hx hy)

/-- The support of a path in a region stays in that region when its first
vertex lies there. -/
theorem walk_support_subset_openIn {d : ℕ} {ω : Configuration d} {B : Set (Vertex d)}
    {x y : Vertex d} (walk : (openIn ω B).Walk x y) (hx : x ∈ B) :
    ∀ z ∈ walk.support, z ∈ B := by
  induction walk with
  | @nil u =>
    intro z hz
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    subst z
    exact hx
  | @cons u v w huv walk ih =>
    intro z hz
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hx
    · exact ih huv.2.2 z hz

/-- A connection inside a finite region has probability at least the bond
density raised to the number of vertices. -/
theorem pow_card_le_measureReal_reachable_openIn {d : ℕ} (p : unitInterval)
    (B : Finset (Vertex d)) {x y : Vertex d} (hx : x ∈ B)
    (hpath : (openIn (allOpen d) B).Reachable x y) :
    (p : ℝ) ^ B.card ≤ (latticeBondLaw d p).real
      {ω | (openIn ω B).Reachable x y} := by
  classical
  obtain ⟨walk, hsimple⟩ := hpath.exists_isPath
  have hs : walk.support.toFinset ⊆ B := by
    intro z hz
    apply walk_support_subset_openIn walk hx z
    exact List.mem_toFinset.mp hz
  have hcard := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup hsimple.support_nodup, SimpleGraph.Walk.length_support] at hcard
  have hlength : walk.length ≤ B.card := by omega
  exact (pow_le_pow_of_le_one p.property.1 p.property.2 hlength).trans
    (pow_length_le_measureReal_reachable_openIn p (↑B : Set (Vertex d)) walk)

/-- In a complete slab, the two-point probability is bounded below by the
bond density raised to the ambient cube's vertex count. -/
theorem IntegerCube.pow_card_le_measureReal_reachable_slab {d : ℕ} (p : unitInterval)
    (Q : IntegerCube d) (j : Fin d) (width k : ℕ) (hfull : (k + 1) * width ≤ Q.size)
    {x y : Vertex d} (hx : x ∈ Q.slab j width k) (hy : y ∈ Q.slab j width k) :
    (p : ℝ) ^ Q.vertices.card ≤
      (latticeBondLaw d p).real {ω | (openIn ω (Q.slab j width k)).Reachable x y} := by
  classical
  let B : Finset (Vertex d) := Q.vertices.filter fun z => z ∈ Q.slab j width k
  have hB : (↑B : Set (Vertex d)) = Q.slab j width k := by
    ext z
    simp only [B, Finset.mem_coe, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  have hxB : x ∈ B := Finset.mem_filter.mpr ⟨hx.1, hx⟩
  have hpath : (openIn (allOpen d) B).Reachable x y := by
    rw [hB]
    exact Q.reachable_allOpen_slab j width k hfull hx hy
  have hcard : B.card ≤ Q.vertices.card := Finset.card_filter_le _ _
  calc
    (p : ℝ) ^ Q.vertices.card ≤ (p : ℝ) ^ B.card :=
      pow_le_pow_of_le_one p.property.1 p.property.2 hcard
    _ ≤ (latticeBondLaw d p).real {ω | (openIn ω B).Reachable x y} :=
      pow_card_le_measureReal_reachable_openIn p B hxB hpath
    _ = _ := by rw [hB]

/-- A uniform two-point lower bound for sufficiently large complete slabs
extends to every cube by finite-energy bounds on the remaining sizes. -/
theorem UniformCubeSlabConnectivity.of_large_cubes {d : ℕ} (p : unitInterval)
    (hp : 0 < (p : ℝ)) (width N : ℕ) (hwidth : 0 < width) (ρ : ℝ) (hρ : 0 < ρ)
    (hlarge : ∀ Q : IntegerCube d, N ≤ Q.size → ∀ j : Fin d, ∀ k : ℕ,
      (k + 1) * width ≤ Q.size → ∀ x ∈ Q.slab j width k, ∀ y ∈ Q.slab j width k,
        ρ ≤ (latticeBondLaw d p).real {ω | (openIn ω (Q.slab j width k)).Reachable x y}) :
    UniformCubeSlabConnectivity d p := by
  let δ : ℝ := min ρ ((p : ℝ) ^ (N ^ d))
  refine ⟨width, hwidth, δ, lt_min hρ (pow_pos hp _), ?_⟩
  intro Q j k hfull x hx y hy
  by_cases hsize : N ≤ Q.size
  · exact (min_le_left _ _).trans (hlarge Q hsize j k hfull x hx y hy)
  · have hcard : Q.vertices.card ≤ N ^ d := by
      rw [Q.card_vertices]
      gcongr
      omega
    calc
      δ ≤ (p : ℝ) ^ (N ^ d) := min_le_right _ _
      _ ≤ (p : ℝ) ^ Q.vertices.card := pow_le_pow_of_le_one p.property.1 p.property.2 hcard
      _ ≤ _ := Q.pow_card_le_measureReal_reachable_slab p j width k hfull hx hy

end Rigidity.Percolation
