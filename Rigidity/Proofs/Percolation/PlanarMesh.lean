import Rigidity.Proofs.Percolation.PlanarBarrier
import Rigidity.Proofs.Percolation.PlanarBoxCluster
import Rigidity.Proofs.Percolation.PlanarPathGeometry

/-!
# Crossing meshes in a planar cube

Transverse strip crossings connect long open paths to the crossing cluster.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5

namespace Rigidity.Percolation

/-- Every strip of the given width in either direction has a transverse crossing. -/
def HasStripCrossings (ω : Configuration 2) (x : Vertex 2) (N w : ℕ) : Prop :=
  (∀ L : ℤ, x 1 - N ≤ L → L + w ≤ x 1 + N →
    ∃ a b, ReachIn ω (cubeAt x N ∩ {v | L ≤ v 1 ∧ v 1 ≤ L + w}) a b ∧
      a 0 = x 0 - N ∧ b 0 = x 0 + N) ∧
  (∀ L : ℤ, x 0 - N ≤ L → L + w ≤ x 0 + N →
    ∃ a b, ReachIn ω (cubeAt x N ∩ {v | L ≤ v 0 ∧ v 0 ≤ L + w}) a b ∧
      a 1 = x 1 - N ∧ b 1 = x 1 + N)

/-- A crossing cluster is closed under open connections inside its cube. -/
theorem IsCrossingCluster.mem_of_reachable {ω : Configuration 2} {x : Vertex 2} {N : ℕ}
    {V : Set (Vertex 2)} (hV : IsCrossingCluster ω x N V) {a b : Vertex 2}
    (ha : a ∈ V) (hab : (openIn ω (cubeAt x N)).Reachable a b) : b ∈ V := by
  obtain ⟨⟨u, _, hVeq⟩, _⟩ := hV
  rw [hVeq] at ha ⊢
  exact ha.trans hab

/-- A horizontal strip crossing lies in the crossing cluster of the cube. -/
theorem horizontal_barrier_mem_cluster {ω : Configuration 2} {x : Vertex 2} {N : ℕ}
    {L U : ℤ} {a b : Vertex 2} {V : Set (Vertex 2)}
    (hV : IsCrossingCluster ω x N V) (hL : x 1 - N ≤ L) (hU : U ≤ x 1 + N)
    (hbar : ReachIn ω (cubeAt x N ∩ {v | L ≤ v 1 ∧ v 1 ≤ U}) a b)
    (ha : a 0 = x 0 - N) (hb : b 0 = x 0 + N) : a ∈ V := by
  obtain ⟨⟨u, hu, hVeq⟩, hcross⟩ := hV
  rw [hVeq] at hcross ⊢
  obtain ⟨⟨c, hc, hcface⟩, ⟨d, hd, hdface⟩⟩ := hcross 1
  have hcmem := (reachIn_of_reachable_openIn hu hc).end_mem
  have hp := reachIn_of_reachable_openIn hcmem (hc.symm.trans hd)
  have hjoin := horizontal_barrier_connects hbar ha hb hp (by rw [hcface]; exact hL)
    (by rw [hdface]; exact hU)
  exact hc.trans (reachIn_reachable_openIn hjoin).symm

/-- A vertical strip crossing lies in the crossing cluster of the cube. -/
theorem vertical_barrier_mem_cluster {ω : Configuration 2} {x : Vertex 2} {N : ℕ}
    {L U : ℤ} {a b : Vertex 2} {V : Set (Vertex 2)}
    (hV : IsCrossingCluster ω x N V) (hL : x 0 - N ≤ L) (hU : U ≤ x 0 + N)
    (hbar : ReachIn ω (cubeAt x N ∩ {v | L ≤ v 0 ∧ v 0 ≤ U}) a b)
    (ha : a 1 = x 1 - N) (hb : b 1 = x 1 + N) : a ∈ V := by
  obtain ⟨⟨u, hu, hVeq⟩, hcross⟩ := hV
  rw [hVeq] at hcross ⊢
  obtain ⟨⟨c, hc, hcface⟩, ⟨d, hd, hdface⟩⟩ := hcross 0
  have hcmem := (reachIn_of_reachable_openIn hu hc).end_mem
  have hp := reachIn_of_reachable_openIn hcmem (hc.symm.trans hd)
  have hjoin := vertical_barrier_connects hbar ha hb hp (by rw [hcface]; exact hL)
    (by rw [hdface]; exact hU)
  exact hc.trans (reachIn_reachable_openIn hjoin).symm

/-- An open path with displacement greater than the strip width joins the crossing cluster. -/
theorem mem_crossingCluster_of_displacement {ω : Configuration 2} {x : Vertex 2} {N w : ℕ}
    {V : Set (Vertex 2)} (hmesh : HasStripCrossings ω x N w)
    (hV : IsCrossingCluster ω x N V) {c d : Vertex 2}
    (hpath : ReachIn ω (cubeAt x N) c d) {j : Fin 2}
    (hdisp : (w : ℤ) < |d j - c j|) : c ∈ V := by
  have hc0 := abs_le.mp (hpath.start_mem 0)
  have hc1 := abs_le.mp (hpath.start_mem 1)
  have hd0 := abs_le.mp (hpath.end_mem 0)
  have hd1 := abs_le.mp (hpath.end_mem 1)
  fin_cases j
  · change (w : ℤ) < |d 0 - c 0| at hdisp
    by_cases hcd : c 0 ≤ d 0
    · rw [abs_of_nonneg (sub_nonneg.mpr hcd)] at hdisp
      have hL : x 0 - N ≤ c 0 := by omega
      have hU : c 0 + w ≤ x 0 + N := by omega
      obtain ⟨a, b, hbar, ha, hb⟩ := hmesh.2 (c 0) hL hU
      have haV := vertical_barrier_mem_cluster hV hL hU hbar ha hb
      have hjoin := vertical_barrier_connects hbar ha hb hpath le_rfl (by omega)
      exact hV.mem_of_reachable haV (reachIn_reachable_openIn hjoin)
    · have hdc : d 0 ≤ c 0 := by omega
      rw [abs_of_nonpos (sub_nonpos.mpr hdc)] at hdisp
      have hL : x 0 - N ≤ d 0 := by omega
      have hU : d 0 + w ≤ x 0 + N := by omega
      obtain ⟨a, b, hbar, ha, hb⟩ := hmesh.2 (d 0) hL hU
      have haV := vertical_barrier_mem_cluster hV hL hU hbar ha hb
      have hjoin := vertical_barrier_connects hbar ha hb hpath.symm le_rfl (by omega)
      exact hV.mem_of_reachable haV (reachIn_reachable_openIn (hjoin.trans hpath.symm))
  · change (w : ℤ) < |d 1 - c 1| at hdisp
    by_cases hcd : c 1 ≤ d 1
    · rw [abs_of_nonneg (sub_nonneg.mpr hcd)] at hdisp
      have hL : x 1 - N ≤ c 1 := by omega
      have hU : c 1 + w ≤ x 1 + N := by omega
      obtain ⟨a, b, hbar, ha, hb⟩ := hmesh.1 (c 1) hL hU
      have haV := horizontal_barrier_mem_cluster hV hL hU hbar ha hb
      have hjoin := horizontal_barrier_connects hbar ha hb hpath le_rfl (by omega)
      exact hV.mem_of_reachable haV (reachIn_reachable_openIn hjoin)
    · have hdc : d 1 ≤ c 1 := by omega
      rw [abs_of_nonpos (sub_nonpos.mpr hdc)] at hdisp
      have hL : x 1 - N ≤ d 1 := by omega
      have hU : d 1 + w ≤ x 1 + N := by omega
      obtain ⟨a, b, hbar, ha, hb⟩ := hmesh.1 (d 1) hL hU
      have haV := horizontal_barrier_mem_cluster hV hL hU hbar ha hb
      have hjoin := horizontal_barrier_connects hbar ha hb hpath.symm le_rfl (by omega)
      exact hV.mem_of_reachable haV (reachIn_reachable_openIn (hjoin.trans hpath.symm))

/-- Every sufficiently long injective open path joins the crossing cluster in a crossing mesh. -/
theorem long_path_mem_crossingCluster {ω : Configuration 2} {x : Vertex 2} {N w n : ℕ}
    {V : Set (Vertex 2)} (hmesh : HasStripCrossings ω x N w)
    (hV : IsCrossingCluster ω x N V) (γ : Fin (n + 1) → Vertex 2)
    (hinj : Function.Injective γ)
    (hγ : ∀ i : Fin n, (openIn ω (cubeAt x N)).Adj (γ i.castSucc) (γ i.succ))
    (hn : (2 * w + 1) ^ 2 < n + 1) : γ 0 ∈ V := by
  obtain ⟨b, j, hpath, hdisp⟩ := exists_open_subpath_with_displacement γ hinj hγ hn
  exact mem_crossingCluster_of_displacement hmesh hV hpath hdisp

end Rigidity.Percolation
