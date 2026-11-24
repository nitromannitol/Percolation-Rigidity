import Rigidity.Proofs.Corrector.DarioResamplePartition
import PercolationClusterHomogenization.Proofs.Percolation.PlanarMeshFlip
import PercolationClusterHomogenization.Proofs.Percolation.PlanarAnchorInterior

/-!
# Lemma 3.5 of Dario for the planar partition of meshed cubes

`ResamplePartitionBound 4747 14244` holds (`resamplePartitionBound_holds`), hence
`DarioResamplePartitionTwo` (`darioResamplePartitionTwo_holds`).

This is Lemma 3.5 of Dario (*Optimal corrector estimates on percolation clusters*) for the planar
partition of the repository, whose goodness is the strip-mesh condition `planarMeshed` instead of
Dario's crossing conditions, in the form `ResamplePartitionBound` (which adds the agreement of the
anchors outside the ball). Dario's printed proof uses crossings by clusters avoiding a cube, which the
strip meshes do not provide; the proof here is the following. Let `ω, ω'` be equal off a bond
`e = {x, y}` and let `s` be the side of `□_{𝒫(ω)}(x)`.

* The square of side `s` around `x` is tested in the strip mesh of `□_{𝒫(ω)}(x)`; its outer strip
  crossings do not use `e`, and by planar duality a change of a crossing of a strip of width at
  least `s + 2` would give a closed dual path from `e` leaving that square, which these crossings
  block (`Rigidity.Percolation.crossing_iff_of_flip`). Hence the meshed cubes of `ω` and `ω'` agree
  except for cubes of side below `101 s` near `x` (`Rigidity.Percolation.meshedFlipBound_of_flip`).
* The good, stable and stopping cubes then agree except for cubes of side below `909 s` within
  `4242 s` of `x`, so the partition cubes at `z` with `|z - x|_∞ ≥ 4747 s` agree
  (`Rigidity.Percolation.planarPartCube_eq_of_meshedFlipBound`), and the partition cubes at the
  other `z` have side at most `14244 s` (`Rigidity.Percolation.side_planarPartCube_le_of_meshedFlipBound`,
  with the comparison of the scales of neighbouring partition cubes).
* For a common partition cube away from `x` the bond `e` is not inside the cube, and the anchor of a
  meshed cube depends only on the open edges inside it
  (`Rigidity.Percolation.TriadicCube.planarAnchor_eq_of_adj_iff_vertices`).

The constants `C₀ = 4747`, `C = 14244` are explicit; Dario's statement has unspecified constants.
-/

namespace Rigidity.Corrector

open LatticeProb.Percolation Rigidity.Percolation

/-- **Lemma 3.5 of Dario for the planar partition**, with `C₀ = 4747` and `C = 14244`. -/
theorem resamplePartitionBound_holds : ResamplePartitionBound 4747 14244 := by
  intro e ω ω' hagree hP hP' x hx z
  obtain ⟨y, hexy⟩ : ∃ y, e.1 = s(x, y) := Sym2.mem_iff_exists.1 hx
  have hb := meshedFlipBound_of_flip hP hagree hexy
  have hsdef : (planarPartCube ω x).side = 3 ^ (planarPartCube ω x).scale := rfl
  have hs1 : (1 : ℤ) ≤ (planarPartCube ω x).side := one_le_pow₀ (by norm_num)
  constructor
  · intro hball
    have hz : ∀ i, |z i - x i| ≤ 4747 * (planarPartCube ω x).side := fun i => by
      have := hball i
      push_cast at this
      rw [hsdef]
      exact this.le
    have h := side_planarPartCube_le_of_meshedFlipBound hP hP' hb hz
    have hle : (planarPartCube ω' z).side ≤ 14244 * (planarPartCube ω x).side := by
      refine h.trans (max_le (by linarith) ?_)
      have : max (planarPartCube ω x).side (4747 * (planarPartCube ω x).side + 1) ≤
          4748 * (planarPartCube ω x).side := max_le (by linarith) (by linarith)
      linarith
    have h' : ((3 ^ (planarPartCube ω' z).scale : ℕ) : ℤ) ≤
        ((14244 * 3 ^ (planarPartCube ω x).scale : ℕ) : ℤ) := by
      push_cast
      exact hle
    exact_mod_cast h'
  · intro hnot
    have hfar : ∃ i, 47 * (101 * (planarPartCube ω x).side) ≤ |z i - x i| := by
      unfold InResampleBall at hnot
      push Not at hnot
      obtain ⟨i, hi⟩ := hnot
      refine ⟨i, ?_⟩
      push_cast at hi
      rw [hsdef]
      linarith
    have hcell := planarPartCube_eq_of_meshedFlipBound hP hP' hb hfar
    refine ⟨hcell, ?_⟩
    unfold planarCoarseAnchor
    rw [hcell]
    have hzD := (planarPartCube_spec hP z).1
    have hxD : x ∉ (planarPartCube ω z).vertices := by
      intro hxD
      have h1 : planarPartCube ω x = planarPartCube ω z := planarPartCube_eq_of_mem hP hxD
      obtain ⟨i, hi⟩ := hfar
      have h2 := TriadicCube.abs_coord_sub_lt_side hzD hxD i
      rw [← h1] at h2
      linarith
    have hm := (planarPartCube_meshed hP z).1
    have hm' : (planarPartCube ω z).planarMeshed ω' := by
      rw [← hcell]
      exact (planarPartCube_meshed hP' z).1
    exact TriadicCube.planarAnchor_eq_of_adj_iff_vertices hm hm'
      (adj_iff_of_agree_off_of_notMem hagree hexy hxD)

/-- **Lemma 3.5 of Dario for the planar partition.** -/
theorem darioResamplePartitionTwo_holds : DarioResamplePartitionTwo :=
  ⟨4747, 14244, by norm_num, resamplePartitionBound_holds⟩

end Rigidity.Corrector
