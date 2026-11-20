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

/-- A connection available when all bonds are open has positive probability
at every positive bond density. -/
theorem measureReal_reachable_openIn_pos_of_allOpen {d : ℕ} (p : unitInterval)
    (hp : 0 < (p : ℝ)) (B : Set (Vertex d)) {x y : Vertex d}
    (hpath : (openIn (allOpen d) B).Reachable x y) :
    0 < (latticeBondLaw d p).real {ω | (openIn ω B).Reachable x y} := by
  obtain ⟨walk⟩ := hpath
  induction walk with
  | @nil u =>
    have heq : {ω : Configuration d | (openIn ω B).Reachable u u} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact SimpleGraph.Reachable.refl u
    rw [heq, probReal_univ]
    norm_num
  | @cons u v w huv walk ih =>
    have hnn : (nearestNeighborGraph d).Adj u v := by
      simpa only [openGraph_allOpen] using huv.1
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
    have hCupper : IsUpperSet C := isUpperSet_reachable_openIn B v w
    have hC : MeasurableSet C := measurableSet_openIn_reachable B v w
    have hAprob : (latticeBondLaw d p).real A = p := by
      rw [measureReal_def, latticeBondLaw_open, ENNReal.toReal_ofReal p.property.1]
    have hinter : (latticeBondLaw d p).real A * (latticeBondLaw d p).real C ≤
        (latticeBondLaw d p).real (A ∩ C) :=
      LatticeProb.infinitePi_harris_bool (fun _ : Bond d => bernoulliMeasure true false p)
        hAupper hCupper hA hC
    have hsubset : A ∩ C ⊆ {ω | (openIn ω B).Reachable u w} := by
      rintro ω ⟨hopen, hrest⟩
      have hstep : (openIn ω B).Adj u v :=
        ⟨(openGraph_adj_iff ω u v).mpr ⟨hnn, hopen⟩, huv.2.1, huv.2.2⟩
      exact hstep.reachable.trans hrest
    have hpos : 0 < (latticeBondLaw d p).real A * (latticeBondLaw d p).real C := by
      rw [hAprob]
      exact mul_pos hp ih
    exact hpos.trans_le (hinter.trans (measureReal_mono hsubset (measure_ne_top _ _)))

/-- Every pair of vertices in a fixed complete cube slab has positive
connection probability at positive bond density. -/
theorem IntegerCube.measureReal_reachable_slab_pos {d : ℕ} (p : unitInterval)
    (hp : 0 < (p : ℝ)) (Q : IntegerCube d) (j : Fin d) (width k : ℕ)
    (hfull : (k + 1) * width ≤ Q.size) {x y : Vertex d}
    (hx : x ∈ Q.slab j width k) (hy : y ∈ Q.slab j width k) :
    0 < (latticeBondLaw d p).real {ω | (openIn ω (Q.slab j width k)).Reachable x y} :=
  measureReal_reachable_openIn_pos_of_allOpen p hp (Q.slab j width k)
    (Q.reachable_allOpen_slab j width k hfull hx hy)

end Rigidity.Percolation
